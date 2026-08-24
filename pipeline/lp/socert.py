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

Supported .lp subset (pilot): `Maximize`/`Minimize`, one `obj:`-style
optional label, `Subject To` with one labelled linear constraint per line,
comparators `<=` `>=` (`<`/`>` treated the same), integer/fraction/decimal
coefficients, default bounds x >= 0. NOT supported (loud error): `=`
constraints, Bounds/General/Binary sections, non-integral data after parsing
(data must be integral; the *certificate* is what gets 通分/scaled).

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
    """max c^T x s.t. A x <= b, x >= 0; integral data."""

    def __init__(self):
        self.vars: list[str] = []
        self.c: list[Fraction] = []
        self.rows: list[tuple[str, list[Fraction], Fraction]] = []  # (name, coeffs, rhs)


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

    raw_rows: list[tuple[str, dict[str, Fraction], Fraction]] = []
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
        if cmp_ in (">=", ">"):
            coeffs = {v: -k for v, k in coeffs.items()}
            rhs_val = -rhs_val
        elif cmp_ == "=":
            raise ValueError(f"equality constraints not supported (pilot): {line}")
        for v in coeffs:
            register(v)
        raw_rows.append((name, coeffs, rhs_val))

    n = len(data.vars)
    vidx = {v: j for j, v in enumerate(data.vars)}
    data.c = [sense * obj_coeffs.get(v, Fraction(0)) for v in data.vars]
    for name, coeffs, rhs_val in raw_rows:
        row = [coeffs.get(v, Fraction(0)) for v in data.vars]
        data.rows.append((name, row, rhs_val))

    # pilot: integral data only
    all_coeffs = list(data.c) + [k for _, row, _ in data.rows for k in row]
    all_coeffs += [rhs for _, _, rhs in data.rows]
    bad = [k for k in all_coeffs if k.denominator != 1]
    if bad:
        raise ValueError(f"non-integral LP data not supported (pilot): {bad[:3]}")
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


# ---------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description="SoPlex exact -> Lean certificate converter")
    ap.add_argument("lp", type=Path, help="input .lp file")
    ap.add_argument("-o", "--out", type=Path, default=None, help="output .lean file")
    ap.add_argument("--module", default=None, help="Lean module name (default: from file stem)")
    ap.add_argument("--soplex", type=Path, default=DEFAULT_SOPLEX)
    ap.add_argument("--settings", type=Path, default=DEFAULT_SETTINGS)
    args = ap.parse_args()

    data = parse_lp(args.lp)
    out = run_soplex(args.soplex, args.settings, args.lp)
    prim = _parse_solution_section(out, "Primal solution", "All other variables")
    dual = _parse_solution_section(out, "Dual solution", "All other dual values")

    x = [prim.get(v, Fraction(0)) for v in data.vars]
    y = [dual.get(name, Fraction(0)) for name, _, _ in data.rows]

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

    D = 1
    for v in y:
        D = _lcm(D, v.denominator)
    Y = [int(v * D) for v in y]
    G = sum(int(rhs) * Y[i] for i, (_, _, rhs) in enumerate(data.rows))

    mod = args.module or module_name_for(args.lp.stem)
    out_path = args.out or (REPO / "lean/Kepler/LP" / f"{mod}.lean")
    text = emit_lean(mod, data, y, x, D, Y, G, args.lp)
    out_path.write_text(text)
    nnz = sum(1 for _, row, _ in data.rows for k in row if k != 0)
    print(f"[socert] {args.lp.name}: {len(data.vars)} vars, {len(data.rows)} rows, "
          f"{nnz} nonzeros; D={D}, G={G}, γ={Fraction(G, D)}; "
          f"validation OK (x≥0, Ax≤b, y≥0, Aᵀy≥c, cᵀx=bᵀy)")
    print(f"[socert] wrote {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
