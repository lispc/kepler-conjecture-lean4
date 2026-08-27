#!/usr/bin/env python3
"""socert.py — untrusted converter: SoPlex exact-rational solution -> Lean certificate.

Pipeline (all steps here are UNTRUSTED; trust is established by the Lean side
re-checking with kernel `decide` via `Kepler.LP.Cert`):

  1. parse a CPLEX .lp file (subset, see below) into (c, A, b), max c^T x
     s.t. A x <= b, x >= 0, with INTEGRAL data;
  2. run SoPlex in exact rational mode (`--loadset=exact.set -X -Y -c`);
  3. parse the rational primal/dual solution;
  4. validate (exact Fraction arithmetic): x >= 0, A x <= b, y >= 0,
     A^T y >= c, strong duality c^T x = b^T y;
  5. integerize the dual certificate: D = lcm(denominators of y),
     Y = D*y, G = b^T Y (so y = Y/D, gamma = G/D);
  6. emit `lean/Kepler/LP/<Module>.lean` with `checkDual ... = true := by decide`
     and a `bound` theorem via `checkDual_sound`.

Supported .lp subset: `Maximize`/`Minimize`, one `obj:`-style optional
label, `Subject To` with one labelled linear constraint per line,
comparators `<=` `>=` (`<`/`>` treated the same), integer/fraction/decimal
coefficients, default bounds x >= 0. NOT supported (loud error): `=`
constraints (split them beforehand, e.g. with flatten_lp.py),
Bounds/General/Binary sections.

Rational (non-integral) data are accepted: rows and objective are scaled
row-wise by their denominator lcms at emission time so the emitted Lean
certificate is integral.  The dual multipliers are scaled accordingly:
with row scale s_i and objective scale s_c, y'_i = s_c·y_i/s_i, then
Y = D·y' with D = lcm(denominators of y') — the integerized certificate
(Y, D, G) with G = b_intᵀY certifies c_intᵀx ≤ G/D = s_c·(original γ).
For `>=` rows the parser negates the row to `<=` form; the corresponding
SoPlex dual multiplier is sign-flipped (SoPlex reports <= 0 for `>=` rows
of a maximization).

Usage:
  socert.py INPUT.lp [-o OUT.lean] [--module NAME] [--soplex PATH] [--settings PATH]

Defaults: soplex = <repo>/pipeline/tools/soplex-8.0.3/bin/soplex,
settings = <repo>/pipeline/lp/exact.set,
OUT = <repo>/lean/Kepler/LP/Cert<Name>.lean (name from the .lp file stem).
"""

import argparse
import re
import subprocess
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DEFAULT_SOPLEX = REPO / "pipeline/tools/soplex-8.0.3/bin/soplex"
DEFAULT_SETTINGS = REPO / "pipeline/lp/exact.set"


# ---------------------------------------------------------------- .lp parsing

_NUMBER_RE = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)(/\d+)?$")


def _is_number(tok: str) -> bool:
    return bool(_NUMBER_RE.match(tok))


def parse_linear(s: str):
    """Parse a linear expression into ({var: Fraction coeff}, const Fraction)."""
    s = s.replace("+", " + ").replace("-", " - ").replace("*", " * ")
    toks = s.split()
    coeffs: dict[str, Fraction] = {}
    const = Fraction(0)
    i, sign = 0, 1
    while i < len(toks):
        t = toks[i]
        if t == "+":
            sign = 1
            i += 1
            continue
        if t == "-":
            sign = -1
            i += 1
            continue
        if _is_number(t):
            if i + 1 < len(toks) and toks[i + 1] == "*":
                coef, var = Fraction(t), toks[i + 2]
                i += 3
            elif i + 1 < len(toks) and toks[i + 1] not in "+-" and not _is_number(toks[i + 1]):
                coef, var = Fraction(t), toks[i + 1]
                i += 2
            else:
                const += sign * Fraction(t)
                i += 1
                sign = 1
                continue
        else:
            coef, var = Fraction(1), t
            i += 1
        coeffs[var] = coeffs.get(var, Fraction(0)) + sign * coef
        sign = 1
    return coeffs, const


_CMP_RE = re.compile(r"(<=|>=|<|>|=)")


class LPData:
    """max c^T x s.t. A x <= b, x >= 0; rational (Fraction) data."""

    def __init__(self):
        self.vars: list[str] = []
        self.c: list[Fraction] = []
        self.rows: list[tuple[str, list[Fraction], Fraction]] = []  # (name, coeffs, rhs)
        self.flipped: list[bool] = []  # row i was negated from an original `>=`


def parse_lp(path: Path) -> LPData:
    section = None
    sense = 1  # +1 maximize, -1 minimize
    obj_text: list[str] = []
    con_lines: list[str] = []
    for raw in path.read_text().splitlines():
        line = raw.split("\\", 1)[0].strip()
        if not line:
            continue
        low = line.lower()
        if low.startswith(("maximize", "max", "minimize", "min")):
            if section is not None:
                raise ValueError(f"section keyword inside section: {line}")
            sense = -1 if low.startswith("min") else 1
            section = "obj"
            line = line.split(None, 1)[1] if len(line.split(None, 1)) > 1 else ""
            if not line:
                continue
        elif low.startswith(("subject to", "such that", "st")):
            section = "con"
            continue
        elif low.startswith(("bounds", "general", "binary", "binaries", "end")):
            if not low.startswith("end"):
                raise ValueError(f"unsupported section (pilot): {line}")
            section = None
            continue
        if section == "obj":
            obj_text.append(line)
        elif section == "con":
            con_lines.append(line)
        else:
            raise ValueError(f"content outside any section: {line}")

    data = LPData()

    def register(var: str):
        if var not in data.vars:
            data.vars.append(var)

    # objective: optional leading `label:`
    obj = " ".join(obj_text)
    if ":" in obj:
        obj = obj.split(":", 1)[1]
    obj_coeffs, obj_const = parse_linear(obj)
    if obj_const != 0:
        raise ValueError("constant term in objective not supported")
    for v in obj_coeffs:
        register(v)

    raw_rows: list[tuple[str, dict[str, Fraction], Fraction, bool]] = []
    for line in con_lines:
        if ":" not in line:
            raise ValueError(f"constraint without label (pilot requires labels): {line}")
        name, rest = line.split(":", 1)
        name = name.strip()
        m = _CMP_RE.search(rest)
        if not m:
            raise ValueError(f"no comparator in constraint: {line}")
        cmp_ = m.group(1)
        lhs, rhs = rest[: m.start()], rest[m.end():]
        lc, lconst = parse_linear(lhs)
        rc, rconst = parse_linear(rhs)
        coeffs: dict[str, Fraction] = dict(lc)
        for v, k in rc.items():
            coeffs[v] = coeffs.get(v, Fraction(0)) - k
        rhs_val = rconst - lconst
        flipped = cmp_ in (">=", ">")
        if flipped:
            coeffs = {v: -k for v, k in coeffs.items()}
            rhs_val = -rhs_val
        elif cmp_ == "=":
            raise ValueError(f"equality constraints not supported "
                             f"(split them with flatten_lp.py first): {line}")
        for v in coeffs:
            register(v)
        raw_rows.append((name, coeffs, rhs_val, flipped))

    n = len(data.vars)
    vidx = {v: j for j, v in enumerate(data.vars)}
    data.c = [sense * obj_coeffs.get(v, Fraction(0)) for v in data.vars]
    for name, coeffs, rhs_val, flipped in raw_rows:
        row = [coeffs.get(v, Fraction(0)) for v in data.vars]
        data.rows.append((name, row, rhs_val))
        data.flipped.append(flipped)
    _ = n, vidx
    return data


# ------------------------------------------------------- SoPlex output parsing


def run_soplex(soplex: Path, settings: Path, lp: Path) -> str:
    cmd = [str(soplex), f"--loadset={settings}", "-X", "-Y", "-c", str(lp)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0 or "Solved to optimality" not in out:
        raise RuntimeError(f"SoPlex did not solve to optimality:\n{out}")
    for needle in ("Primal solution feasible in original problem",
                   "Dual solution feasible in original problem"):
        if needle not in out:
            raise RuntimeError(f"SoPlex exact check missing ({needle!r}):\n{out}")
    return out


def _parse_solution_section(out: str, header: str, stop_prefix: str) -> dict[str, Fraction]:
    res: dict[str, Fraction] = {}
    lines = out.splitlines()
    try:
        i = next(i for i, l in enumerate(lines) if l.startswith(header))
    except StopIteration:
        raise RuntimeError(f"section {header!r} not found in SoPlex output")
    for line in lines[i + 1:]:
        if line.startswith(stop_prefix) or not line.strip():
            break
        parts = line.split()
        if len(parts) != 2:
            raise RuntimeError(f"cannot parse solution line: {line!r}")
        res[parts[0]] = Fraction(parts[1])
    return res


# ------------------------------------------------------------------ emission


def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def _int(z: int) -> str:
    return f"({z})" if z < 0 else str(z)


def _sparse(pairs) -> str:
    return "[" + ", ".join(f"({j}, {_int(k)})" for j, k in pairs if k != 0) + "]"


def module_name_for(stem: str) -> str:
    parts = [p for p in re.split(r"[^A-Za-z0-9]+", stem) if p]
    return "Cert" + "".join(p[:1].upper() + p[1:] for p in parts)


def emit_lean(mod: str, data: LPData, y: list[Fraction], x: list[Fraction],
              D: int, Y: list[int], G: int, lp_path: Path) -> str:
    gamma = Fraction(G, D)
    if gamma.denominator == 1:
        gamma_lit = str(gamma.numerator)
    else:
        gamma_lit = f"({gamma.numerator}/{gamma.denominator} : Rat)"
    c_sparse = _sparse([(j, int(k)) for j, k in enumerate(data.c)])
    rows_lean = ",\n    ".join(
        "⟨" + _sparse([(j, int(k)) for j, k in enumerate(row)]) + f", {_int(int(rhs))}⟩"
        for _, row, rhs in data.rows)
    Y_lean = "[" + ", ".join(_int(v) for v in Y) + "]"
    primal_integral = all(v.denominator == 1 for v in x)
    lines = f"""/-
AUTO-GENERATED certificate — do not edit

Generated by `pipeline/lp/socert.py` from `{lp_path.name}`
(SoPlex exact rational mode, see `pipeline/lp/README.md`).

LP: max cᵀx s.t. A·x ≤ b, x ≥ 0 — {len(data.vars)} vars, {len(data.rows)} rows.
Dual certificate: y = Y/D with D = {D}, claimed bound γ = G/D = {gamma}.
Untrusted validation (exact Fraction arithmetic in the converter):
x ≥ 0, A·x ≤ b, y ≥ 0, Aᵀy ≥ c, cᵀx = bᵀy (strong duality).
-/
import Kepler.LP.Cert

-- deep list literals and the kernel `decide` re-check need headroom
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

/-- The LP, sparse integer data (`{lp_path.name}`). -/
def lp : LPI where
  numVars := {len(data.vars)}
  c := {c_sparse}
  A := [
    {rows_lean}]

/-- Kernel re-check of the integerized dual certificate. -/
theorem dual_check : checkDual lp {Y_lean} {D} {_int(G)} = true := by decide

/-- End-to-end: every rational-feasible point of `lp` has objective ≤ {gamma}. -/
theorem bound (x : List Rat) (hxlen : x.length = lp.numVars)
    (hx0 : ∀ j < lp.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ lp.A, r.evalRat x ≤ (r.rhs : Rat)) :
    lp.c.dotRat x ≤ {gamma_lit} := by
  have h := checkDual_sound lp {Y_lean} {D} {_int(G)} dual_check x hxlen hx0 hxA
  rwa [show (({_int(G)} : Int) : Rat) / (({D} : ℕ) : Rat) = {gamma_lit} by norm_num] at h
"""
    if primal_integral:
        X_lean = "[" + ", ".join(_int(int(v)) for v in x) + "]"
        lines += f"""
/-- The SoPlex primal solution is integral; the kernel checks feasibility. -/
theorem primal_check : checkPrimal lp {X_lean} = true := by decide
"""
    else:
        lines += f"""
-- The SoPlex primal solution is fractional (x = {", ".join(str(v) for v in x)});
-- the Int-valued `checkPrimal` does not apply, the dual certificate suffices.
"""
    lines += f"\nend Kepler.LP.{mod}\n"
    return lines


def emit_lean_sharded(mod: str, data: LPData, D: int, Y: list[int], G: int,
                      lp_path: Path, k: int, terminal_bound: int | None) -> Path:
    """Sharded emission (see README "分片原型"): a directory
    `lean/Kepler/LP/<mod>/` with

    - `Data.lean`     — `lp`, `certY`, `certD`, `certG` literals + `base_check`
                        (all non-column checks of `checkDual`), elaborated once;
    - `Cols<i>.lean`  — `shard_<i> : checkDualCols lp certY certD s len = true`
                        closed by its own kernel `decide` (independent module,
                        parallel builds);
    - `Assembly.lean` — shard chain (term-mode `Bool.and_eq_true_iff.mpr`
                        links, no kernel re-evaluation), `dual_check` via
                        `checkDual_of_shards`, and the `bound` theorem via
                        `checkDual_sound`.
    """
    n = len(data.vars)
    count = (n + k - 1) // k
    dirpath = REPO / "lean/Kepler/LP" / mod
    dirpath.mkdir(parents=True, exist_ok=True)
    c_sparse = _sparse([(j, int(kk)) for j, kk in enumerate(data.c)])
    rows_lean = ",\n    ".join(
        "⟨" + _sparse([(j, int(kk)) for j, kk in enumerate(row)]) + f", {_int(int(rhs))}⟩"
        for _, row, rhs in data.rows)
    Y_lean = "[" + ", ".join(_int(v) for v in Y) + "]"
    header = f"""/-
AUTO-GENERATED certificate (sharded mode) — do not edit

Generated by `pipeline/lp/socert.py --shard-cols {k}` from `{lp_path.name}`
(SoPlex exact rational mode, see `pipeline/lp/README.md`).

LP: max cᵀx s.t. A·x ≤ b, x ≥ 0 — {n} vars, {len(data.rows)} rows.
Dual certificate: y = Y/D with D = certD, claimed bound γ = certG/certD.
Untrusted validation (exact Fraction arithmetic in the converter):
x ≥ 0, A·x ≤ b, y ≥ 0, Aᵀy ≥ c, cᵀx = bᵀy (strong duality).
-/
"""
    data_lean = header + f"""import Kepler.LP.Cert

-- deep list literals and the kernel `decide` re-check need headroom
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

/-- The LP, sparse integer data (`{lp_path.name}`). -/
def lp : LPI where
  numVars := {n}
  c := {c_sparse}
  A := [
    {rows_lean}]

/-- The integerized dual solution `Y` (the rational dual is `Y/certD`). -/
def certY : List Int := {Y_lean}

/-- The certificate denominator `D > 0`. -/
def certD : ℕ := {D}

/-- The integerized bound numerator: `γ = certG / certD`. -/
def certG : Int := {_int(G)}

/-- Everything except the column loop: `D > 0`, sizes, well-formedness,
`Y ≥ 0`, and `bᵀY ≤ G`. -/
theorem base_check : checkDualBase lp certY certD certG = true := by
  decide

end Kepler.LP.{mod}
"""
    (dirpath / "Data.lean").write_text(data_lean)

    for i in range(count):
        s = i * k
        length = min(k, n - s)
        cols = header + f"""import Kepler.LP.{mod}.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

/-- Column shard {i}: `AᵀY ≥ D·c` restricted to columns [{s}, {s + length}). -/
theorem shard_{i} : checkDualCols lp certY certD {s} {length} = true := by
  decide

end Kepler.LP.{mod}
"""
        (dirpath / f"Cols{i:03d}.lean").write_text(cols)

    imports = "\n".join(
        f"import Kepler.LP.{mod}.Cols{i:03d}" for i in range(count))
    links = ["theorem cols_0 : checkDualColShards lp certY certD "
             f"{n} {k} 0 = true := rfl"]
    for i in range(count):
        links.append(
            f"theorem cols_{i + 1} : checkDualColShards lp certY certD "
            f"{n} {k} ({i} + 1) = true :=\n"
            f"  Bool.and_eq_true_iff.mpr ⟨cols_{i}, shard_{i}⟩")
    links_lean = "\n\n".join(links)
    asm = header + imports + f"""

namespace Kepler.LP.{mod}

/-- Shard chain: `cols_<i>` covers columns `[0, i·{k})`. Term-mode links:
no kernel re-evaluation of the shards. -/
{links_lean}

/-- Reassembly: the sharded checks give the full dual certificate. -/
theorem dual_check : checkDual lp certY certD certG = true :=
  checkDual_of_shards lp certY certD certG {k} {count} (by decide)
    base_check cols_{count}

/-- End-to-end: every rational-feasible point of `lp` has objective
≤ `certG / certD`. -/
theorem bound (x : List Rat) (hxlen : x.length = lp.numVars)
    (hx0 : ∀ j < lp.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ lp.A, r.evalRat x ≤ (r.rhs : Rat)) :
    lp.c.dotRat x ≤ ((certG : Int) : Rat) / ((certD : ℕ) : Rat) :=
  checkDual_sound lp certY certD certG dual_check x hxlen hx0 hxA
"""
    if terminal_bound is not None:
        B = terminal_bound
        asm += f"""
/-- The Flyspeck terminal condition `γ < {B}`, as an integer inequality
(`G < {B}·D` ⟺ `G/D < {B}` since `D > 0`). -/
theorem gamma_lt : certG < {B} * (certD : Int) := by
  decide

/-- The terminal condition transported to the objective: every
rational-feasible point has objective `< {B}`. -/
theorem bound_lt (x : List Rat) (hxlen : x.length = lp.numVars)
    (hx0 : ∀ j < lp.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ lp.A, r.evalRat x ≤ (r.rhs : Rat)) :
    lp.c.dotRat x < {B} := by
  refine lt_of_le_of_lt (bound x hxlen hx0 hxA) ?_
  have hD : (0 : Rat) < ((certD : ℕ) : Rat) := Nat.cast_pos.mpr (by decide)
  rw [div_lt_iff₀ hD]
  calc ((certG : Int) : Rat) < (({B} * (certD : Int) : Int) : Rat) :=
        Int.cast_lt.mpr gamma_lt
    _ = {B} * ((certD : ℕ) : Rat) := by push_cast; ring
"""
    asm += f"\nend Kepler.LP.{mod}\n"
    (dirpath / "Assembly.lean").write_text(asm)
    return dirpath


def _tree_depth(m: int) -> int:
    """Smallest `d` with `2^d ≥ m` (the tree depth for the dual vector)."""
    d = 0
    while (1 << d) < m:
        d += 1
    return d


def _chunk_indices(n: int, size: int) -> list[tuple[int, int]]:
    """Nonempty index ranges `[s, e)` partitioning `[0, n)`, each ≤ `size`."""
    return [(s, min(s + size, n)) for s in range(0, n, size)]


def emit_col_major_sharded(mod: str, data: LPData, D: int, Y: list[int], G: int,
                           lp_path: Path, k: int | None,
                           terminal_bound: int | None) -> Path:
    """Column-major (transposed) emission: a directory
    `lean/Kepler/LP/<mod>/` with

    - `Data.lean`     — `lp : LPCM` (`cs`: per-variable `(cⱼ, column)` pairs,
                        `b`: dense rhs), `certY`/`certD`/`certG` literals,
                        tree depth `d`, + `base_check`
                        (`checkDualCMTBase`), elaborated once;
    - `Assembly.lean` — the single O(nnz) `cols_check` kernel `decide`
                        (`checkDualCMTCols`), reassembly via
                        `checkDualCMT_split`, `bound` via
                        `checkDualCMT_sound`, and the Flyspeck terminal
                        condition `gamma_lt`/`bound_lt`;
    - `Bench.lean`    — self-contained single-file variant (imports only
                        `Kepler.LP.ColMajor`; everything inline) for
                        `lake env lean` wall-clock benchmarking.

    With the transposed layout the kernel work of the dual check is O(nnz):
    each column inequality scans only that column's support.  The dual
    vector `Y` is kept as a plain list; the emitted theorems build the
    transient tree `ITree.ofList certY d` inside the `decide`.
    """
    n = len(data.vars)
    m = len(data.rows)
    d = _tree_depth(m)
    dirpath = REPO / "lean/Kepler/LP" / mod
    dirpath.mkdir(parents=True, exist_ok=True)

    # per-variable (objective coefficient, sparse column) pairs
    cs_items = [(int(data.c[j]),
                 [(i, int(row[j])) for i, (_, row, _) in enumerate(data.rows)
                  if row[j] != 0]) for j in range(n)]
    b_vals = [int(rhs) for _, _, rhs in data.rows]
    assert len(cs_items) == n and len(b_vals) == m and len(Y) == m

    header = f"""/-
AUTO-GENERATED certificate (column-major mode) — do not edit

Generated by `pipeline/lp/socert.py --col-major` from `{lp_path.name}`
(SoPlex exact rational mode, see `pipeline/lp/README.md`).

LP: max cᵀx s.t. A·x ≤ b, x ≥ 0 — {n} vars, {m} rows.
Constraint matrix stored BY COLUMN (`LPCM.cs`); the dual check is O(nnz).
Dual certificate: y = Y/D with D = certD, claimed bound γ = certG/certD.
The dual vector Y is a plain `List Int`; the tree `ITree.ofList certY {d}`
(2^{d} = {2 ** d} leaves ≥ {m} rows) is built transiently inside the decide.
Untrusted validation (exact Fraction arithmetic in the converter):
x ≥ 0, A·x ≤ b, y ≥ 0, Aᵀy ≥ c, cᵀx = bᵀy (strong duality).
-/
"""

    # chunked `def`s: ≤100 columns per cs chunk, ≤250 items per b/certY chunk
    CS_CHUNK = 100
    VEC_CHUNK = 250

    def fmt_col(col: list) -> str:
        return "[" + ", ".join(f"({i}, {_int(a)})" for i, a in col) + "]"

    def fmt_cs_item(item) -> str:
        c, col = item
        # the inner `: ColI` ascription anchors the list-literal element type at
        # elaboration time (avoiding superlinear pending-MVar synthesis on the
        # nested `List (Nat × Int)` literal; measured on the real pilot).
        return f"({_int(c)}, ({fmt_col(col)} : ColI))"

    cs_defs: list[str] = []
    for idx, (s, e) in enumerate(_chunk_indices(n, CS_CHUNK)):
        items = ", ".join(fmt_cs_item(it) for it in cs_items[s:e])
        if n > CS_CHUNK:
            cs_defs.append(f"def cs_{idx} : List (Int × ColI) := [\n  {items}\n]")
        else:
            cs_defs.append(f"def cs : List (Int × ColI) := [\n  {items}\n]")
    if n > CS_CHUNK:
        cs_defs.append("def cs : List (Int × ColI) := " +
                       " ++ ".join(f"cs_{i}" for i in range(len(cs_defs))))

    b_defs: list[str] = []
    for idx, (s, e) in enumerate(_chunk_indices(m, VEC_CHUNK)):
        items = ", ".join(_int(v) for v in b_vals[s:e])
        if m > VEC_CHUNK:
            b_defs.append(f"def b_{idx} : List Int := [\n  {items}\n]")
        else:
            b_defs.append(f"def b : List Int := [\n  {items}\n]")
    if m > VEC_CHUNK:
        b_defs.append("def b : List Int := " +
                      " ++ ".join(f"b_{i}" for i in range(len(b_defs))))

    y_defs: list[str] = []
    for idx, (s, e) in enumerate(_chunk_indices(m, VEC_CHUNK)):
        items = ", ".join(_int(v) for v in Y[s:e])
        if m > VEC_CHUNK:
            y_defs.append(f"def certY_{idx} : List Int := [\n  {items}\n]")
        else:
            y_defs.append("def certY : List Int := [\n  " + items + "\n]")
    if m > VEC_CHUNK:
        y_defs.append("def certY : List Int := " +
                      " ++ ".join(f"certY_{i}" for i in range(len(y_defs))))

    # ----------------------------------------------------------- Data.lean
    data_lean = header + f"""import Kepler.LP.ColMajor

-- deep list literals and the kernel `decide` re-check need headroom
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

{chr(10).join(cs_defs)}

{chr(10).join(b_defs)}

/-- The LP in column-major form: `cs[j] = (cⱼ, column j)` (column `j` lists
the `(row index, coefficient)` pairs of variable `j`), dense right-hand side
`b` (`{lp_path.name}`). -/
def lp : LPCM where
  cs := cs
  b := b

{chr(10).join(y_defs)}

/-- The certificate denominator `D > 0`. -/
def certD : ℕ := {D}

/-- The integerized bound numerator: `γ = certG / certD`. -/
def certG : Int := {_int(G)}

/-- Tree depth: `2^d ≥ b.length` (the transient tree holding `certY`). -/
def d : ℕ := {d}

/-- Everything except the column loop: `D > 0`, sizes, well-formedness,
`Y ≥ 0`, and the lockstep bound `bᵀY ≤ G` (flat `dotLI`, O(n)). -/
theorem base_check : checkDualCMTBaseFlat lp d certY certD certG = true := by
  decide

end Kepler.LP.{mod}
"""
    (dirpath / "Data.lean").write_text(data_lean)

    # ------------------------------------------------------- Assembly.lean
    asm_head = header + f"""import Kepler.LP.{mod}.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

/-- The whole column loop `AᵀY ≥ D·c` over all {n} columns: with the
column-major layout this is a single O(nnz) kernel `decide`. -/
theorem cols_check : checkDualCMTCols lp d (ITree.ofList certY d) certD = true := by
  decide

/-- Reassembly: flat base checks + column loop give the full dual certificate. -/
theorem dual_check : checkDualCMTF lp d (ITree.ofList certY d) certY certD certG = true :=
  checkDualCMTF_split base_check cols_check
"""

    asm_tail = f"""
/-- End-to-end: every rational-feasible point of `lp` has objective
≤ `certG / certD`.  Feasibility is stated over the column-major data
(`cmRowEval`). -/
theorem bound (x : List Rat) (hxlen : x.length = lp.cs.length)
    (hx0 : ∀ j < lp.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < lp.b.length, cmRowEval lp i x ≤ (lp.b.getD i 0 : Rat)) :
    cmObj lp x ≤ ((certG : Int) : Rat) / ((certD : ℕ) : Rat) :=
  checkDualCMTF_sound lp d certY certD certG dual_check x hxlen hx0 hxrows
"""
    if terminal_bound is not None:
        B = terminal_bound
        asm_tail += f"""
/-- The Flyspeck terminal condition `γ < {B}`, as an integer inequality
(`G < {B}·D` ⟺ `G/D < {B}` since `D > 0`). -/
theorem gamma_lt : certG < {B} * (certD : Int) := by
  decide

/-- The terminal condition transported to the objective: every
rational-feasible point has objective `< {B}`. -/
theorem bound_lt (x : List Rat) (hxlen : x.length = lp.cs.length)
    (hx0 : ∀ j < lp.cs.length, 0 ≤ x.getD j 0)
    (hxrows : ∀ i < lp.b.length, cmRowEval lp i x ≤ (lp.b.getD i 0 : Rat)) :
    cmObj lp x < {B} := by
  refine lt_of_le_of_lt (bound x hxlen hx0 hxrows) ?_
  have hD : (0 : Rat) < ((certD : ℕ) : Rat) := Nat.cast_pos.mpr (by decide)
  rw [div_lt_iff₀ hD]
  calc ((certG : Int) : Rat) < (({B} * (certD : Int) : Int) : Rat) :=
        Int.cast_lt.mpr gamma_lt
    _ = {B} * ((certD : ℕ) : Rat) := by push_cast; ring
"""
    asm = asm_head + asm_tail + f"\nend Kepler.LP.{mod}\n"
    (dirpath / "Assembly.lean").write_text(asm)

    # ---------------------------------------------------------- Bench.lean
    # Self-contained single-file variant for wall-clock benchmarking with
    # `lake env lean` (imports only the framework module): identical data
    # literals and identical kernel `decide`s as the modular layout above.
    bench_body = f"""import Kepler.LP.ColMajor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.LP.{mod}

{chr(10).join(cs_defs)}

{chr(10).join(b_defs)}

/-- The LP in column-major form (`{lp_path.name}`). -/
def lp : LPCM where
  cs := cs
  b := b

{chr(10).join(y_defs)}

def certD : ℕ := {D}

def certG : Int := {_int(G)}

def d : ℕ := {d}

theorem base_check : checkDualCMTBaseFlat lp d certY certD certG = true := by
  decide

theorem cols_check : checkDualCMTCols lp d (ITree.ofList certY d) certD = true := by
  decide

theorem dual_check : checkDualCMTF lp d (ITree.ofList certY d) certY certD certG = true :=
  checkDualCMTF_split base_check cols_check
"""
    bench = header + bench_body + asm_tail + f"\nend Kepler.LP.{mod}\n"
    (dirpath / "Bench.lean").write_text(bench)
    return dirpath


# ---------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description="SoPlex exact -> Lean certificate converter")
    ap.add_argument("lp", type=Path, help="input .lp file")
    ap.add_argument("-o", "--out", type=Path, default=None, help="output .lean file")
    ap.add_argument("--module", default=None, help="Lean module name (default: from file stem)")
    ap.add_argument("--soplex", type=Path, default=DEFAULT_SOPLEX)
    ap.add_argument("--settings", type=Path, default=DEFAULT_SETTINGS)
    ap.add_argument("--shard-cols", type=int, default=None, metavar="K",
                    help="sharded mode: emit a module directory with one kernel-"
                         "`decide` theorem per K columns (see README 分片原型); "
                         "row-major only, ignored with --col-major")
    ap.add_argument("--col-major", action="store_true",
                    help="column-major (transposed) certificate: emit LPCM data "
                         "and use Kepler.LP.ColMajor's O(nnz) checker (see "
                         "README 列主序); base/cols split into two kernel "
                         "`decide`s, no per-column sharding")
    ap.add_argument("--terminal-bound", type=int, default=None, metavar="B",
                    help="also emit `gamma_lt`/`bound_lt`: the certificate bound "
                         "γ < B (Flyspeck terminal condition; B=12)")
    args = ap.parse_args()

    data = parse_lp(args.lp)
    out = run_soplex(args.soplex, args.settings, args.lp)
    prim = _parse_solution_section(out, "Primal solution", "All other variables")
    dual = _parse_solution_section(out, "Dual solution", "All other dual values")

    x = [prim.get(v, Fraction(0)) for v in data.vars]
    # SoPlex reports duals <= 0 for `>=` rows of a maximization; those rows
    # were negated into `<=` form at parse time, so flip the sign back.
    y = [(-1 if f else 1) * dual.get(name, Fraction(0))
         for f, (name, _, _) in zip(data.flipped, data.rows)]

    # exact untrusted validation
    for j, v in enumerate(x):
        assert v >= 0, f"primal variable {data.vars[j]} negative: {v}"
    for name, row, rhs in data.rows:
        lhs = sum(k * v for k, v in zip(row, x))
        assert lhs <= rhs, f"row {name} violated: {lhs} <= {rhs} false"
    for i, v in enumerate(y):
        assert v >= 0, f"dual multiplier {data.rows[i][0]} negative: {v} (sign convention?)"
    for j, v in enumerate(data.vars):
        lhs = sum(row[j] * y[i] for i, (_, row, _) in enumerate(data.rows))
        assert lhs >= data.c[j], f"dual constraint {v} violated: {lhs} >= {data.c[j]} false"
    obj_x = sum(k * v for k, v in zip(data.c, x))
    obj_y = sum(rhs * y[i] for i, (_, _, rhs) in enumerate(data.rows))
    assert obj_x == obj_y, f"duality gap: cᵀx={obj_x} ≠ bᵀy={obj_y}"

    # ---- integerize the data and the dual certificate (see module docstring)
    def denom_lcm(vals) -> int:
        d = 1
        for v in vals:
            d = _lcm(d, v.denominator)
        return d

    s_c = denom_lcm(data.c)
    c_int = [int(k * s_c) for k in data.c]
    row_scales = [denom_lcm(list(row) + [rhs]) for _, row, rhs in data.rows]
    rows_int = [([int(k * s) for k in row], int(rhs * s))
                for s, (_, row, rhs) in zip(row_scales, data.rows)]
    y_scaled = [s_c * v / s for v, s in zip(y, row_scales)]
    D = denom_lcm(y_scaled)
    Y = [int(v * D) for v in y_scaled]
    G = sum(rhs * Y[i] for i, (_, rhs) in enumerate(rows_int))
    # integer-level double check of what the kernel will verify
    for j in range(len(data.vars)):
        lhs = sum(row[j] * Y[i] for i, (row, _) in enumerate(rows_int))
        assert lhs >= D * c_int[j], f"integerized dual column {j} violated"
    assert G == D * s_c * obj_y, "integerized bound mismatch"

    data.c = c_int
    data.rows = [(name, row, rhs)
                 for (name, _, _), (row, rhs) in zip(data.rows, rows_int)]

    mod = args.module or module_name_for(args.lp.stem)
    nnz = sum(1 for _, row, _ in data.rows for k in row if k != 0)
    print(f"[socert] {args.lp.name}: {len(data.vars)} vars, {len(data.rows)} rows, "
          f"{nnz} nonzeros; D={D}, G={G}, γ={Fraction(G, D)}; "
          f"validation OK (x≥0, Ax≤b, y≥0, Aᵀy≥c, cᵀx=bᵀy)")
    if args.col_major:
        dirpath = emit_col_major_sharded(mod, data, D, Y, G, args.lp,
                                         args.shard_cols, args.terminal_bound)
        print(f"[socert] column-major: wrote {dirpath}/ "
              f"(Data + Assembly + Bench); base_check in Data.lean, "
              f"cols_check in Assembly.lean")
        print(f"[socert] build: lake env lean {dirpath}/Bench.lean   "
              f"(single-file benchmark)")
    elif args.shard_cols is not None:
        dirpath = emit_lean_sharded(mod, data, D, Y, G, args.lp, args.shard_cols,
                                    args.terminal_bound)
        count = (len(data.vars) + args.shard_cols - 1) // args.shard_cols
        print(f"[socert] sharded (k={args.shard_cols}): wrote {dirpath}/ "
              f"(Data + {count} Cols shards + Assembly)")
        print(f"[socert] build: lake build Kepler.LP.{mod}.Assembly")
    else:
        out_path = args.out or (REPO / "lean/Kepler/LP" / f"{mod}.lean")
        text = emit_lean(mod, data, y, x, D, Y, G, args.lp)
        out_path.write_text(text)
        print(f"[socert] wrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
