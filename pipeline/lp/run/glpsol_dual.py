#!/usr/bin/env python3
"""glpsol --exact -> exact rational dual certificate channel.

For the terminal LPs where SoPlex exact gives up ("did not solve to
optimality"), glpsol --exact (GLPK exact-arithmetic simplex) still finds
an optimal basis, but its `-o` report prints only floating-point
marginals.  This tool recovers an EXACT rational dual from the reported
basis statuses:

  - rows with St != B are nonbasic (constraint active)  -> y_i unknown
  - rows with St == B are basic (slack > 0)             -> y_i = 0
  - columns with St == B are basic (reduced cost 0)     -> (A^T y)_j = c_j
  - columns with St != B sit at their lower bound 0     -> no equation

The resulting square system B^T y = c_B is solved with sparse Fraction
Gaussian elimination (Markowitz pivoting), then checked exactly:
y >= 0, A^T y >= c (all columns), and b^T y against glpsol's printed
objective.  Integerization + emission reuse the exact same semantics as
gen_one.generate() (denom_lcm / row_scales / y_scaled / D / G + the
sparse integer pre-check of A^T Y >= D*c), via socert.emit_col_major_sharded.

Everything here is UNTRUSTED codegen; trust comes from the Lean kernel
re-check (`decide`) on the emitted Bench.lean.

Usage:
  glpsol_dual.py --id 206218905887_t0 [--terminal-bound 12]
  glpsol_dual.py --id 62586200165_t0007 --lp slack_flat.lp --terminal-bound 0

Defaults: workdir /dev/shm/retry/<id>, lp <workdir>/root_flat.lp,
solution <workdir>/glpk_exact_sol.txt, module "T"+id (sanitized).
"""
import argparse, os, re, subprocess, sys, time
from fractions import Fraction
from pathlib import Path

REPO_LP = "/home/scroll/repos/kepler-conjecture-lean4/pipeline/lp"
sys.path.insert(0, REPO_LP)
sys.path.insert(0, REPO_LP + "/run")
import socert
import gen_one

GLPSOL = REPO_LP + "/../tools/glpk-5.0/bin/glpsol"
ROOT = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun"))
GEN = ROOT / "gen"

_STAT = {"B", "NL", "NU", "NF", "NS"}
_NUMLINE_RE = re.compile(r"^ {0,5}\d+ ")


def parse_sol(path: Path):
    """Parse glpsol `-o` basic-solution report (fixed-width format).

    An entry starts on a line whose cols 0-5 hold the number; the status
    code sits at cols 20-21 of the entry's LAST line.  Names of <= 12
    chars keep everything on the numbered line (col 19 is a pad space);
    longer names put the name on the numbered line (wrapped if need be)
    and the status on a continuation line.  Returns
    (row_st, col_st, obj_text)."""
    lines = path.read_text().splitlines()
    status = next((l.split(":", 1)[1].strip() for l in lines[:10]
                   if l.startswith("Status:")), "")
    if status != "OPTIMAL":
        raise RuntimeError(f"glpsol status is {status!r}, not OPTIMAL")
    obj_text = None
    for l in lines[:10]:
        m = re.match(r"Objective:\s+\S+ = ([-+\d.eE]+) \((MAX|MIN)", l)
        if m:
            obj_text = m.group(1)
    if obj_text is None:
        raise RuntimeError("objective line not found")
    i_rows = next(i for i, l in enumerate(lines) if "Row name" in l)
    i_cols = next(i for i, l in enumerate(lines) if "Column name" in l)
    i_end = next((i for i, l in enumerate(lines)
                  if "Karush-Kuhn-Tucker" in l or "End of output" in l),
                 len(lines))

    def section(lo, hi):
        st = {}
        cur = None  # name of pending multi-line entry
        for l in lines[lo:hi]:
            if _NUMLINE_RE.match(l):
                if len(l) > 19 and l[19] == " ":
                    code = l[20:22].strip()
                    if code not in _STAT:
                        raise RuntimeError(f"bad status line: {l!r}")
                    st[l[7:19].strip()] = code
                    cur = None
                else:
                    cur = l[7:].strip()
            elif cur is not None:
                code = l[20:22].strip() if len(l) >= 22 else ""
                if code in _STAT:
                    st[cur] = code
                    cur = None
                else:  # wrapped name chunk (not seen in practice)
                    cur += l.strip()
        return st

    row_st = section(i_rows + 2, i_cols)
    col_st = section(i_cols + 2, i_end)
    return row_st, col_st, obj_text


def sparse_solve(rows: list[dict], rhs: list[Fraction]) -> dict[int, Fraction]:
    """Solve M y = rhs exactly; M = list of row dicts {col: Fraction}.
    Markowitz-pivoted sparse Gaussian elimination over Fraction.
    Returns {col: value} for all columns."""
    rows = [dict(r) for r in rows]
    rhs = list(rhs)
    active = set(range(len(rows)))
    cols: dict[int, set[int]] = {}
    for i, r in enumerate(rows):
        for j in r:
            cols.setdefault(j, set()).add(i)
    steps = []  # (row, pivot_col, pivot, row_dict, rhs) for back-subst
    while active:
        best = None
        for j, rset in cols.items():
            rset &= active
            cols[j] = rset
            if not rset:
                continue
            clen = len(rset)
            for i in rset:
                if j not in rows[i]:
                    continue
                cost = (clen - 1) * (len(rows[i]) - 1)
                if best is None or cost < best[0]:
                    best = (cost, i, j)
                    if cost == 0:
                        break
            if best is not None and best[0] == 0:
                break
        if best is None:
            raise RuntimeError("basis system structurally singular")
        _, i, j = best
        prow, piv = rows[i], rows[i][j]
        for k in list(cols[j]):
            if k == i or k not in active or j not in rows[k]:
                continue
            r = rows[k]
            f = r[j] / piv
            del r[j]
            for jj, vv in prow.items():
                if jj == j:
                    continue
                nv = r.get(jj, Fraction(0)) - f * vv
                if nv:
                    r[jj] = nv
                    cols.setdefault(jj, set()).add(k)
                else:
                    r.pop(jj, None)
            rhs[k] -= f * rhs[i]
        steps.append((i, j, piv, prow, rhs[i]))
        active.discard(i)
        for jj in prow:
            cs = cols.get(jj)
            if cs:
                cs.discard(i)
        rows[i] = {}
    y: dict[int, Fraction] = {}
    for i, j, piv, prow, rrhs in reversed(steps):
        s = rrhs
        for jj, vv in prow.items():
            if jj != j and jj in y:
                s -= vv * y[jj]
        y[j] = s / piv
    return y


def exact_dual(lpdata, row_st, col_st):
    """Exact rational dual y (list[Fraction] over lpdata.rows) from the
    glpsol basis; exact-checks y >= 0 and A^T y >= c."""
    names = [name for name, _, _ in lpdata.rows]
    if set(row_st) != set(names) or len(row_st) != len(names):
        raise RuntimeError("row name/status mismatch with flat LP")
    if set(col_st) != set(lpdata.vars) or len(col_st) != len(lpdata.vars):
        raise RuntimeError("column name/status mismatch with flat LP")
    nb_rows = [i for i, name in enumerate(names) if row_st[name] != "B"]
    b_cols = [j for j, v in enumerate(lpdata.vars) if col_st[v] == "B"]
    if len(nb_rows) != len(b_cols):
        raise RuntimeError(f"basis size mismatch: {len(nb_rows)} nonbasic "
                           f"rows vs {len(b_cols)} basic cols")
    M, rhs = [], []
    for j in b_cols:
        M.append({i: lpdata.rows[i][1][j] for i in nb_rows
                  if lpdata.rows[i][1][j]})
        rhs.append(lpdata.c[j])
    t0 = time.time()
    y_loc = sparse_solve(M, rhs)
    y = [Fraction(0)] * len(names)
    for i, v in y_loc.items():
        y[i] = v
    # ---- exact untrusted verification (loud on any failure)
    bad = [i for i, v in enumerate(y) if v < 0]
    if bad:
        raise RuntimeError(f"{len(bad)} negative duals, first: {names[bad[0]]}")
    acc = [Fraction(0)] * len(lpdata.vars)
    for i in nb_rows:
        if y[i]:
            for j, a in enumerate(lpdata.rows[i][1]):
                if a:
                    acc[j] += a * y[i]
    for j in range(len(lpdata.vars)):
        if acc[j] < lpdata.c[j]:
            raise RuntimeError(f"dual infeasible at col {j} "
                               f"({lpdata.vars[j]}): {acc[j]} < {lpdata.c[j]}")
        if col_st[lpdata.vars[j]] == "B" and acc[j] != lpdata.c[j]:
            raise RuntimeError(f"basic col {j} reduced cost nonzero")
    print(f"[dual] {len(nb_rows)}x{len(b_cols)} basis system solved "
          f"({time.time()-t0:.1f}s); y>=0 and A^Ty>=c exact-verified")
    return y


def integerize_emit(lpdata, y, mod, lp_path, terminal_bound, verbose=True):
    """Same semantics as the second half of gen_one.generate()."""
    def denom_lcm(vals):
        d = 1
        for v in vals:
            d = socert._lcm(d, v.denominator)
        return d

    s_c = denom_lcm(v for v in lpdata.c if v)
    c_int = [int(k * s_c) if k else 0 for k in lpdata.c]
    row_scales = [denom_lcm([v for v in row if v] + [rhs])
                  for _, row, rhs in lpdata.rows]
    rows_int = [([int(k * s) if k else 0 for k in row], int(rhs * s))
                for s, (_, row, rhs) in zip(row_scales, lpdata.rows)]
    y_scaled = [s_c * v / s for v, s in zip(y, row_scales)]
    D = denom_lcm(y_scaled)
    Y = [int(v * D) for v in y_scaled]
    G = sum(rhs * Y[i] for i, (_, rhs) in enumerate(rows_int))
    # sparse integer check of A^T Y >= D c  (O(nnz)); full trust stays with Lean
    acc = [0] * len(lpdata.vars)
    for i, (row, _) in enumerate(rows_int):
        yi = Y[i]
        if yi:
            for j, a in enumerate(row):
                if a:
                    acc[j] += a * yi
    for j in range(len(lpdata.vars)):
        assert acc[j] >= D * c_int[j], f"integerized dual col {j} violated"
    lpdata.c = c_int
    lpdata.rows = [(name, row, rhs)
                   for (name, _, _), (row, rhs) in zip(lpdata.rows, rows_int)]

    socert.REPO = GEN  # emit under $LPRUN_ROOT/gen/lean/Kepler/LP/<mod>
    dirpath = socert.emit_col_major_sharded(
        mod, lpdata, D, Y, G, lp_path, None, terminal_bound)
    if verbose:
        print(f"[emit] {mod}: D={D.bit_length()} bits, "
              f"gamma=G/D={float(Fraction(G, D)):.10f} -> {dirpath}")
    return dirpath, D, Y, G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", required=True, help="terminal id, e.g. 206218905887_t0")
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--lp", default=None,
                    help="flat LP file (default <workdir>/root_flat.lp); "
                         "use slack_flat.lp for infeasible terminals")
    ap.add_argument("--sol", default=None,
                    help="glpsol -o report (default <workdir>/glpk_exact_sol.txt)")
    ap.add_argument("--module", default=None)
    ap.add_argument("--terminal-bound", type=int, default=12)
    ap.add_argument("--run-glpsol", action="store_true",
                    help="run glpsol --exact first if the solution is missing")
    a = ap.parse_args()
    wd = Path(a.workdir or f"/dev/shm/retry/{a.id}")
    lp = Path(a.lp) if a.lp and os.path.isabs(a.lp) else wd / (a.lp or "root_flat.lp")
    sol = Path(a.sol) if a.sol else wd / "glpk_exact_sol.txt"
    mod = a.module or "T" + a.id.replace(".", "_").replace("-", "_")

    if not sol.exists():
        if not a.run_glpsol:
            raise SystemExit(f"missing {sol} (pass --run-glpsol to solve)")
        log = open(wd / "glpk_exact.log", "w")
        r = subprocess.run([GLPSOL, "--lp", str(lp), "--exact",
                            "-o", str(sol)], stdout=log,
                           stderr=subprocess.STDOUT)
        log.close()
        if r.returncode != 0:
            raise SystemExit(f"glpsol --exact failed, see {wd}/glpk_exact.log")

    t0 = time.time()
    lpdata = gen_one.parse_lp_fast(lp)
    row_st, col_st, obj_text = parse_sol(sol)
    print(f"[parse] {len(lpdata.rows)} rows x {len(lpdata.vars)} vars; "
          f"glpsol objective {obj_text}")
    y = exact_dual(lpdata, row_st, col_st)
    obj = sum(rhs * y[i] for i, (_, _, rhs) in enumerate(lpdata.rows))
    # numeric self-consistency: glpsol prints the exact objective rounded
    printed = Fraction(obj_text)
    tol = Fraction(1, 10**9) * max(1, abs(printed))
    ok = abs(obj - printed) <= max(tol, Fraction(1, 10**8) * max(1, abs(printed)))
    print(f"[check] b^Ty = {float(obj):.10f} vs glpsol {obj_text} "
          f"(|diff|={float(abs(obj - printed)):.3e}) -> {'OK' if ok else 'MISMATCH'}")
    if not ok:
        raise RuntimeError("b^Ty inconsistent with glpsol objective")
    if not obj < a.terminal_bound:
        raise RuntimeError(f"terminal condition fails: b^Ty={obj} !< {a.terminal_bound}")
    integerize_emit(lpdata, y, mod, lp, a.terminal_bound)
    print(f"[done] {a.id} in {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
