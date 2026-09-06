#!/usr/bin/env python3
"""Generate one terminal's Lean col-major certificate module.

Usage: gen_one.py --hypermap-string S --module Run123 [--terminal-bound 12]
Chain: gen_data (root data section) -> glpsol --wcpxlp -> flatten_lp ->
socert.emit_col_major_sharded with REPO patched to OUTROOT/gen.

Everything here is UNTRUSTED codegen; trust comes from the Lean kernel
re-check (`decide`) on the emitted Bench.lean.

（2026-09-06 重启后重建版：从 /dev/shm 迁入 git 持久化；OUTROOT 仍指
/dev/shm/lprun，可用环境变量 LPRUN_ROOT 覆盖。）
"""
import argparse, shutil, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, "/home/scroll/repos/kepler-conjecture-lean4/pipeline/lp")
import socert
import gen_data

GLPSOL = "/home/scroll/repos/kepler-conjecture-lean4/pipeline/tools/glpk-5.0/bin/glpsol"
REF = Path("/dev/shm/kepler-ref/flyspeck/formal_lp/glpk")
import os
ROOT = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun"))
WORK = ROOT / "work"       # scratch per job
GEN = ROOT / "gen"         # socert output root (REPO stand-in)

from fractions import Fraction


def parse_lp_fast(path: Path):
    """Sparse-but-compatible re-implementation of socert.parse_lp: same var
    registration order (objective vars, then constraint vars in row order),
    same row order, `>=` rows negated to `<=`; returns a socert.LPData with
    DENSE rows (densified once)."""
    import re
    from socert import LPData, parse_linear, _CMP_RE
    section, sense, obj_text, con_lines = None, 1, [], []
    for raw in path.read_text().splitlines():
        line = raw.split("\\", 1)[0].strip()
        if not line:
            continue
        low = line.lower()
        if low.startswith(("maximize", "max", "minimize", "min")):
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
                raise ValueError(f"unsupported section: {line}")
            section = None
            continue
        if section == "obj":
            obj_text.append(line)
        elif section == "con":
            con_lines.append(line)
        else:
            raise ValueError(f"content outside section: {line}")

    data = LPData()
    vidx: dict[str, int] = {}

    def register(var):
        if var not in vidx:
            vidx[var] = len(data.vars)
            data.vars.append(var)

    obj = " ".join(obj_text)
    if ":" in obj:
        obj = obj.split(":", 1)[1]
    obj_coeffs, obj_const = parse_linear(obj)
    if obj_const != 0:
        raise ValueError("objective constant")
    for v in obj_coeffs:
        register(v)

    dense_rows = []
    for line in con_lines:
        name, rest = line.split(":", 1)
        name = name.strip()
        m = _CMP_RE.search(rest)
        cmp_ = m.group(1)
        lc, lconst = parse_linear(rest[: m.start()])
        rc, rconst = parse_linear(rest[m.end():])
        coeffs = dict(lc)
        for v, k in rc.items():
            coeffs[v] = coeffs.get(v, Fraction(0)) - k
        rhs_val = rconst - lconst
        flipped = cmp_ in (">=", ">")
        if flipped:
            coeffs = {v: -k for v, k in coeffs.items()}
            rhs_val = -rhs_val
        elif cmp_ == "=":
            raise ValueError("equality row in flat lp")
        for v in coeffs:
            register(v)
        row = [0] * len(data.vars)
        for v, k in coeffs.items():
            row[vidx[v]] = k
        dense_rows.append(row)
        data.rows.append((name, row, rhs_val))
        data.flipped.append(flipped)
    # pad all rows to final width; rebuild objective in final variable order
    n = len(data.vars)
    for r in dense_rows:
        if len(r) < n:
            r.extend([0] * (n - len(r)))
    data.c = [sense * obj_coeffs.get(v, Fraction(0)) for v in data.vars]
    return data


def build_model2() -> str:
    model = (REF / "head.mod").read_text() + (REF / "body.mod").read_text()
    import re
    model = re.sub(r"main:.*", "", model)
    model = re.sub(r"maximize objective:.*", "maximize objective: sum{i in node} ln[i];", model)
    model = re.sub(r"lnsum_def:.*", "", model)
    return model


def add_slacks_flat(flat_path: Path, out_path: Path) -> tuple[Path, list[str]]:
    """Every flattened row gets its own slack column:
      `r: lhs <= rhs` -> `r: lhs - s<k> <= rhs`;  `>=` -> `+ s<k> >=`.
    Objective becomes `max obj - sum(s_k)` (existing terms preserved).
    Any feasible point of the original LP maps to all-slacks-zero here, so
    an exact optimal value < 0 certifies infeasibility of the original."""
    import re
    lines = flat_path.read_text().splitlines()
    out, slacks = [], []
    k = 0
    for line in lines:
        m = re.match(r"^ (\S+):\s*(.*)(<=|>=)\s*(\S+)\s*$", line)
        if m:
            name, lhs, cmp_, rhs = m.groups()
            s = f"s{k}"
            k += 1
            slacks.append(s)
            sign = "-" if cmp_ == "<=" else "+"
            out.append(f" {name}: {lhs} {sign} {s} {cmp_} {rhs}")
        elif line.strip().lower().startswith("maximize"):
            out.append(line)
        else:
            out.append(line)
    txt = "\n".join(out) + "\n"
    if slacks:
        obj_line = " objective: " + " ".join(f"- {s}" for s in slacks)
        # replace the whole (possibly multi-line) objective with -sum(slacks)
        import re as _re
        txt = _re.sub(r" objective:.*?(?=\nSubject To)", obj_line,
                      txt, count=1, flags=_re.S)
    out_path.write_text(txt)
    return out_path, slacks


def generate(hypermap_string: str, mod: str, terminal_bound: int | None,
             workdir: Path, verbose=False, data_text: str | None = None,
             slack_infeasible: bool = False) -> Path:
    workdir.mkdir(parents=True, exist_ok=True)
    (workdir / "model2.mod").write_text(build_model2())
    data = data_text if data_text is not None else \
        gen_data.ampl_of_bb(gen_data.root_bb(hypermap_string))
    (workdir / "data.txt").write_text(data)
    lp = workdir / "root.lp"
    r = subprocess.run([GLPSOL, "-m", "model2.mod", "-d", "data.txt",
                        "--wcpxlp", "root.lp", "--check"],
                       cwd=workdir, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"glpsol failed: {r.stdout[-2000:]} {r.stderr[-2000:]}")
    flat = workdir / "root_flat.lp"
    r = subprocess.run([sys.executable,
                        "/home/scroll/repos/kepler-conjecture-lean4/pipeline/lp/flatten_lp.py",
                        str(lp), str(flat)], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"flatten failed: {r.stdout[-2000:]} {r.stderr[-2000:]}")
    if slack_infeasible:
        flat2 = workdir / "slack_flat.lp"
        flat, _slacks = add_slacks_flat(flat, flat2)

    # socert: parse LP, solve exact with SoPlex, integerize, emit col-major.
    lpdata = parse_lp_fast(flat)
    out = socert.run_soplex(socert.DEFAULT_SOPLEX, socert.DEFAULT_SETTINGS, flat)
    prim = socert._parse_solution_section(out, "Primal solution", "All other variables")
    dual = socert._parse_solution_section(out, "Dual solution", "All other dual values")
    x = [prim.get(v, socert.Fraction(0)) for v in lpdata.vars]
    y = [(-1 if f else 1) * dual.get(name, socert.Fraction(0))
         for f, (name, _, _) in zip(lpdata.flipped, lpdata.rows)]
    for j, v in enumerate(x):
        assert v >= 0, f"primal var {j} negative"
    for i, v in enumerate(y):
        assert v >= 0, f"dual {i} negative"
    obj_y = sum(rhs * y[i] for i, (_, _, rhs) in enumerate(lpdata.rows))

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
        mod, lpdata, D, Y, G, flat, None, terminal_bound)
    gamma = socert.Fraction(G, D)
    if verbose:
        print(f"[gen] {mod}: gamma={float(gamma):.8f}")
    return dirpath


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--hypermap-string", default="")
    ap.add_argument("--data-text-file", default=None,
                    help="AMPL data section file (batch2a schema)")
    ap.add_argument("--module", required=True)
    ap.add_argument("--terminal-bound", type=int, default=12)
    ap.add_argument("--infeasible", action="store_true",
                    help="slack-column infeasibility certificate (bound 0)")
    ap.add_argument("--workdir", default=None)
    a = ap.parse_args()
    wd = Path(a.workdir or str(WORK / a.module))
    t0 = time.time()
    dt = Path(a.data_text_file).read_text() if a.data_text_file else None
    d = generate(a.hypermap_string, a.module,
                 0 if a.infeasible else a.terminal_bound, wd,
                 data_text=dt, slack_infeasible=a.infeasible)
    print(f"wrote {d} in {time.time()-t0:.1f}s")
