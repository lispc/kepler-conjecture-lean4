#!/usr/bin/env python3
"""flatten_lp.py — normalize a glpsol --wcpxlp CPLEX-LP file for socert.py.

socert.py (and the Lean checker `Kepler.LP.Cert`) accepts only the pure form
  max cᵀx s.t. A x <= b, x >= 0, with INTEGRAL data.
glpsol's --wcpxlp output deviates in three ways; this script rewrites it into
an EQUIVALENT pure-form LP (untrusted step — trust is re-established by the
Lean kernel re-check, and by the exact-arithmetic validation inside socert):

  1. equality rows `r: lhs = rhs`  ->  two rows `r__le: lhs <= rhs`,
     `r__ge: lhs >= rhs` (an equality is the conjunction of both);
  2. Bounds section -> explicit rows: finite upper bound `x <= u`, finite
     nonzero lower bound `x >= l` (default LP lower bound 0 stays implicit);
  3. free variables (only `ynsum`, `sqdeficit` in the Flyspeck model —
     report-only variables) are split `v = v_pos - v_neg`, v_pos,v_neg >= 0.
     Soundness of the bound transfer: any feasible point of the original LP
     maps to a feasible point of the split LP with the same objective value
     (take v_pos = max(v,0)), so  sup_orig <= sup_split <= gamma.

Additionally every emitted number is kept EXACT (finite decimals stay decimal;
anything else is printed as num/den) — SoPlex reads them exactly with
`int:readmode = 1`.  Integerization (row-wise denominator clearing, with the
matching rescaling of the dual multipliers) happens at certificate-emission
time inside socert.py, NOT here: emitting integer-scaled rows (×10^14 for
the pi digits) breaks floating-point presolve tolerance checks downstream.

Usage: flatten_lp.py IN.lp OUT.lp
"""

import re
import sys
from fractions import Fraction

from socert import parse_linear, _is_number  # reuse the .lp expression parser

_CMP_RE = re.compile(r"(<=|>=|<|>|=)")


def parse_cpxlp(path: str):
    """Parse a CPLEX-LP file into (sense, obj_const-free coeffs, rows, bounds).

    rows: list of (name, {var: Fraction}, cmp in {'<=','>=','='}, Fraction rhs)
    bounds: {var: (lo or None, hi or None)}  (None = unbounded on that side)
    """
    section = None
    sense = 1
    obj_text: list[str] = []
    con_lines: list[str] = []
    bnd_lines: list[str] = []
    for raw in open(path):
        line = raw.split("\\", 1)[0].rstrip("\n")
        if not line.strip():
            continue
        low = line.strip().lower()
        if low.startswith(("maximize", "max", "minimize", "min")):
            section, sense = "obj", (-1 if low.startswith("min") else 1)
            continue
        if low.startswith(("subject to", "such that", "st")):
            section = "con"
            continue
        if low == "bounds":
            section = "bnd"
            continue
        if low == "end":
            section = None
            continue
        if section == "obj":
            obj_text.append(line.strip())
        elif section == "con":
            # rows may wrap; a continuation line starts with +/-, a digit,
            # or '.', a new row starts with a `<name>:` label
            s = line.strip()
            if con_lines and s[0] in "+-0123456789.=<>":
                con_lines[-1] += " " + s
            else:
                con_lines.append(s)
        elif section == "bnd":
            bnd_lines.append(line.strip())
        else:
            raise ValueError(f"content outside any section: {line!r}")

    obj = " ".join(obj_text)
    if ":" in obj:
        obj = obj.split(":", 1)[1]
    obj_coeffs, obj_const = parse_linear(obj)
    if obj_const != 0:
        raise ValueError("constant term in objective not supported")

    rows = []
    for line in con_lines:
        name, rest = line.split(":", 1)
        m = _CMP_RE.search(rest)
        if not m:
            raise ValueError(f"no comparator in constraint: {line}")
        cmp_ = m.group(1)
        cmp_ = {"<": "<=", ">": ">="}.get(cmp_, cmp_)
        lc, lconst = parse_linear(rest[: m.start()])
        rc, rconst = parse_linear(rest[m.end():])
        coeffs = dict(lc)
        for v, k in rc.items():
            coeffs[v] = coeffs.get(v, Fraction(0)) - k
        coeffs = {v: k for v, k in coeffs.items() if k != 0}
        rows.append((name.strip(), coeffs, cmp_, rconst - lconst))

    bounds: dict[str, tuple] = {}
    for line in bnd_lines:
        toks = line.split()
        if toks[-1] == "free":
            bounds[toks[0]] = (None, None)
            continue
        nums = [t for t in toks if _is_number(t)]
        var = [t for t in toks if not _is_number(t) and t not in ("<=", ">=", "<", ">")]
        if len(var) != 1:
            raise ValueError(f"cannot parse bounds line: {line!r}")
        v = var[0]
        if line.index(v) < (line.index(nums[0]) if nums else len(line)):
            # 'var <= hi' or 'var >= lo'
            hi = Fraction(nums[0]) if "<" in line else None
            lo = Fraction(nums[0]) if ">" in line else None
            bounds[v] = (lo, hi)
        else:
            # 'lo <= var <= hi' or 'lo <= var'
            lo = Fraction(nums[0])
            hi = Fraction(nums[1]) if len(nums) > 1 else None
            bounds[v] = (lo, hi)
    return sense, obj_coeffs, rows, bounds


def flatten(sense, obj_coeffs, rows, bounds):
    """Apply the three equivalences; return (obj, rows) with only <=/>= rows
    over nonnegative variables."""
    # free-variable split: substitute v -> v_pos - v_neg everywhere
    free_vars = {v for v, (lo, hi) in bounds.items() if lo is None}

    def subst(coeffs):
        out = {}
        for v, k in coeffs.items():
            if v in free_vars:
                out[v + "__pos"] = out.get(v + "__pos", Fraction(0)) + k
                out[v + "__neg"] = out.get(v + "__neg", Fraction(0)) - k
            else:
                out[v] = out.get(v, Fraction(0)) + k
        return {v: k for v, k in out.items() if k != 0}

    obj = subst(obj_coeffs)
    out_rows = []
    for name, coeffs, cmp_, rhs in rows:
        coeffs = subst(coeffs)
        if cmp_ == "=":
            out_rows.append((name + "__le", coeffs, "<=", rhs))
            out_rows.append((name + "__ge", coeffs, ">=", rhs))
        else:
            out_rows.append((name, coeffs, cmp_, rhs))
    # bounds -> rows (skip lower bound 0: default in pure form)
    for v, (lo, hi) in bounds.items():
        if v in free_vars:
            if lo is not None or hi is not None:
                raise ValueError(f"one-sided unbounded variable {v} not supported")
            continue
        if lo is not None and lo != 0:
            out_rows.append((f"bdlo__{v}", {v: Fraction(1)}, ">=", lo))
        if hi is not None:
            out_rows.append((f"bdhi__{v}", {v: Fraction(1)}, "<=", hi))
    return obj, out_rows


def _num(z: Fraction) -> str:
    """Exact literal: finite decimal whenever the denominator has only
    factors 2 and 5 (always the case for glpsol-printed decimals), else
    num/den (accepted by SoPlex with int:readmode = 1)."""
    if z.denominator == 1:
        return str(z.numerator)
    d, a, b = z.denominator, 0, 0
    while d % 2 == 0:
        d //= 2
        a += 1
    while d % 5 == 0:
        d //= 5
        b += 1
    if d != 1:
        return f"{z.numerator}/{z.denominator}"
    k = max(a, b)
    n = z.numerator * (2 ** (k - a)) * (5 ** (k - b))
    s = str(abs(n)).rjust(k + 1, "0")
    out = (s[:-k] or "0") + "." + s[-k:]
    return ("-" if n < 0 else "") + out


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit("usage: flatten_lp.py IN.lp OUT.lp")
    sense, obj_coeffs, rows, bounds = parse_cpxlp(sys.argv[1])
    obj, out_rows = flatten(sense, obj_coeffs, rows, bounds)

    all_vars: list[str] = []
    for v in obj:
        if v not in all_vars:
            all_vars.append(v)
    for _, c, _, _ in out_rows:
        for v in c:
            if v not in all_vars:
                all_vars.append(v)

    def fmt(coeffs) -> str:
        parts = []
        for v in all_vars:
            k = coeffs.get(v)
            if not k:
                continue
            if k == 1:
                parts.append(f"+ {v}")
            elif k == -1:
                parts.append(f"- {v}")
            elif k > 0:
                parts.append(f"+ {_num(k)} {v}")
            else:
                parts.append(f"- {_num(-k)} {v}")
        return " ".join(parts) if parts else "+ 0"

    with open(sys.argv[2], "w") as f:
        f.write("\\* flattened by flatten_lp.py from " + sys.argv[1] + " *\\\n\n")
        f.write(("Maximize\n" if sense > 0 else "Minimize\n"))
        f.write(" objective: " + fmt(obj) + "\n\n")
        f.write("Subject To\n")
        for name, coeffs, cmp_, rhs in out_rows:
            f.write(f" {name}: {fmt(coeffs)} {cmp_} {_num(rhs)}\n")
        f.write("\nEnd\n")

    nnz = sum(len(c) for _, c, _, _ in out_rows)
    print(f"[flatten_lp] {len(all_vars)} vars, {len(out_rows)} rows, {nnz} nonzeros; "
          f"exact decimal data; wrote {sys.argv[2]}")
    if sense < 0:
        print("[flatten_lp] note: Minimize kept as-is; socert negates c internally")
    return 0


if __name__ == "__main__":
    sys.exit(main())
