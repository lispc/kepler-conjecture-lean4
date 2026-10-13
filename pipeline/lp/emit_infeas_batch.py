#!/usr/bin/env python3
"""emit_infeas_batch.py — C1.7 批量发射器：189 条 infeasible Farkas 证书
→ LpInfeasCert 探针（LpFarkasCore + coreShape/farkasCheck 双 decide）批量
发射 + `lake env lean` 串行机器验证。

发射形状 = gen_farkas.py --lean 内置 pin 模板（与 /tmp/p4g5/ProbePilotB.lean
逐字同形）：import Kepler.Text.LP.LPSchemaFarkas + maxHeartbeats 0 +
maxRecDepth 100000 + core_shape/core_farkasCheck 双 `by decide` +
`#print axioms`。本发射器只做编排：排序、发射、串行编译、记账。

数据源：/tmp/p4g5/batch_results.json（G5 波 Python 精确预检 189/189 OK 的
清单，每条含 hs/gi/ti/hid/prec/rows/nvars）。排序键 = (rows×cols, rows,
cols, hs, gi, ti) 升序——最小 p3 记录先行。

用法（一切命令在仓库根跑；探针/日志全落 /tmp，零 git 足迹）：
  emit_infeas_batch.py --plan                      # 只打印排序队列（不发射）
  emit_infeas_batch.py --limit 15                  # 发射+编译前 15 条（默认预算 30 分/条）
  emit_infeas_batch.py --limit 0 --emit-only       # 全队列只发射 .lean 不编译
  emit_infeas_batch.py --limit 15 --resume         # 按 manifest 跳过已记账条目续跑
  emit_infeas_batch.py --report                    # 汇总 manifest + CPU 时外推

纪律对齐（docs/fill-worker-playbook.md）：
  - 单 lake 进程串行（playbook §6 单 lean 进程配额）；退出码由 subprocess
    returncode 直取，不经管道；
  - macOS 无 timeout 命令 → 每条编译用 subprocess 死线（默认 30 分钟），
    超时 killpg 整组（防孤儿进程，playbook §5.4'' ㉗）后记 SKIP 跳下一条；
  - 长命令日志落文件（行级 flush + fsync），"0 字节"≠卡死；
  - native_decide 是项目禁词，本发射器不生成；证书正确性以 G5 Python 精确
    预检为准，decide 只是对拍确认。
"""

import argparse
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
GEN = REPO / "pipeline" / "lp" / "gen_farkas.py"
LEAN_DIR = REPO / "lean"
DEF_RESULTS = Path("/tmp/p4g5/batch_results.json")
DEF_OUTDIR = Path("/tmp/p4g5/batch1")


def load_queue(results_path):
    recs = json.loads(Path(results_path).read_text())
    recs = [r for r in recs if r.get("ok")]
    recs.sort(key=lambda r: (r["rows"] * r["nvars"], r["rows"], r["nvars"],
                             r["hs"], r["gi"], r["ti"]))
    for i, r in enumerate(recs):
        r["bid"] = i + 1
        r["id"] = f"{r['hs']}#{r['gi']}#{r['ti']}"
    return recs


def log(msg, runlog=None):
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, file=sys.stderr, flush=True)
    if runlog:
        with open(runlog, "a") as f:
            f.write(line + "\n")


def emit_one(rec, out_dir):
    """gen_farkas.py --lean 单条发射；返回 (exit, path, ns, msg)。"""
    ns = f"C17B{rec['bid']:03d}"
    path = out_dir / f"B{rec['bid']:03d}.lean"
    cmd = [sys.executable, str(GEN), "--lean", rec["hs"], str(rec["gi"]),
           str(rec["ti"]), str(path), ns]
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, path, ns, (p.stdout + p.stderr).strip()


def compile_one(path, timeout_s):
    """`lake env lean` 单条串行编译。返回 dict(exit, elapsed, log_path,
    axioms, err_lines, timed_out)。"""
    tlog = out_dir_log(path)
    env = dict(os.environ)
    elan = Path.home() / ".elan" / "bin"
    env["PATH"] = str(elan) + os.pathsep + env.get("PATH", "")
    t0 = time.monotonic()
    with open(tlog, "wb") as f:
        p = subprocess.Popen(["lake", "env", "lean", str(path)],
                             cwd=str(LEAN_DIR), stdout=f, stderr=f,
                             env=env, start_new_session=True)
        timed_out = False
        try:
            rc = p.wait(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            rc = p.wait()
    elapsed = time.monotonic() - t0
    text = Path(tlog).read_text(errors="replace")
    axioms = ""
    for ln in text.splitlines():
        if "depends on axioms" in ln:
            axioms = ln.strip()
    err_lines = [ln for ln in text.splitlines()
                 if "error" in ln.lower() and "axioms" not in ln]
    return dict(exit=rc, elapsed_s=round(elapsed, 1), log=str(tlog),
                axioms=axioms, err_lines=err_lines[:5], timed_out=timed_out)


def out_dir_log(path):
    return path.with_suffix(".log")


def manifest_append(manifest_path, obj):
    with open(manifest_path, "a") as f:
        f.write(json.dumps(obj, ensure_ascii=False) + "\n")
        f.flush()
        os.fsync(f.fileno())


def run(queue, limit, out_dir, timeout_min, emit_only, resume):
    out_dir.mkdir(parents=True, exist_ok=True)
    runlog = out_dir / "run.log"
    manifest = out_dir / "manifest.jsonl"
    done = set()
    if resume and manifest.exists():
        for ln in manifest.read_text().splitlines():
            if ln.strip():
                done.add(json.loads(ln)["id"])
        log(f"resume: {len(done)} 条已有账", runlog)
    sel = queue[:limit] if limit > 0 else queue
    log(f"queue={len(queue)} selected={len(sel)} out={out_dir} "
        f"timeout={timeout_min}min emit_only={emit_only}", runlog)
    for rec in sel:
        if rec["id"] in done:
            log(f"B{rec['bid']:03d} {rec['id']} 已记账，跳", runlog)
            continue
        cells = rec["rows"] * rec["nvars"]
        log(f"B{rec['bid']:03d} emit {rec['id']} "
            f"p{rec['prec']} {rec['rows']}x{rec['nvars']} cells={cells}",
            runlog)
        rc, path, ns, msg = emit_one(rec, out_dir)
        if rc != 0:
            log(f"  EMIT FAIL exit={rc}: {msg[:200]}", runlog)
            manifest_append(manifest, dict(
                id=rec["id"], bid=rec["bid"], hid=rec["hid"], prec=rec["prec"],
                rows=rec["rows"], nvars=rec["nvars"], ns=ns,
                status="emit_fail", emit_exit=rc, emit_msg=msg[:300]))
            continue
        if emit_only:
            log(f"  emitted {path}", runlog)
            continue
        res = compile_one(path, timeout_min * 60)
        if res["timed_out"]:
            status = "skip_timeout"
        elif res["exit"] == 0:
            status = "ok"
        else:
            status = "lean_error"
        log(f"  {status} exit={res['exit']} {res['elapsed_s']}s "
            f"axioms={res['axioms'] or '-'}", runlog)
        if res["err_lines"]:
            log(f"  err0: {res['err_lines'][0][:200]}", runlog)
        manifest_append(manifest, dict(
            id=rec["id"], bid=rec["bid"], hid=rec["hid"], prec=rec["prec"],
            rows=rec["rows"], nvars=rec["nvars"], ns=ns, status=status,
            lean_exit=res["exit"], elapsed_s=res["elapsed_s"],
            axioms=res["axioms"], errs=res["err_lines"],
            probe=str(path), log=res["log"]))
    log("done", runlog)


def report(queue, out_dir):
    manifest = out_dir / "manifest.jsonl"
    if not manifest.exists():
        print("no manifest at", manifest)
        return 1
    rows = [json.loads(x) for x in manifest.read_text().splitlines() if x.strip()]
    qmap = {r["id"]: r for r in queue}
    ok = [r for r in rows if r["status"] == "ok"]
    bad = [r for r in rows if r["status"] != "ok"]
    print(f"records={len(rows)} ok={len(ok)} not_ok={len(bad)}")
    for r in rows:
        print(f"  B{r['bid']:03d} {r['id']:26s} p{r['prec']} "
              f"{r['rows']:3d}x{r['nvars']:3d} cells={r['rows']*r['nvars']:6d} "
              f"{r['status']:12s} {r.get('elapsed_s','-'):>8} "
              f"{r.get('axioms','')[:60]}")
    if len(ok) >= 2:
        cells = [r["rows"] * r["nvars"] for r in ok]
        secs = [r["elapsed_s"] for r in ok]
        # 幂律拟合 log t = a·log cells + b（decide 代价对规模常超线性）
        n = len(ok)
        lx = [__import__("math").log(c) for c in cells]
        ly = [__import__("math").log(s) for s in secs]
        mx, my = sum(lx) / n, sum(ly) / n
        a = sum((x - mx) * (y - my) for x, y in zip(lx, ly)) / \
            sum((x - mx) ** 2 for x in lx)
        b = my - a * mx
        total = 0.0
        for r in queue:
            c = r["rows"] * r["nvars"]
            est = __import__("math").exp(a * __import__("math").log(c) + b)
            total += est
        print(f"power-law fit: t = {__import__('math').exp(b):.2f} * "
              f"cells^{a:.3f}  (n={n})")
        print(f"189 条全量 CPU 时外推 ≈ {total/3600:.1f} h"
              f"（幂律按已测规模段；最大 327×230 在测段外，另有 >40min 实证下界）")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--results", default=str(DEF_RESULTS))
    ap.add_argument("--out-dir", default=str(DEF_OUTDIR))
    ap.add_argument("--limit", type=int, default=0,
                    help="只取排序队列前 N 条（0=全队列）")
    ap.add_argument("--timeout-min", type=int, default=30)
    ap.add_argument("--plan", action="store_true")
    ap.add_argument("--emit-only", action="store_true")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args(argv)
    queue = load_queue(args.results)
    if args.plan:
        for r in queue:
            print(f"B{r['bid']:03d} {r['id']:26s} hid={r['hid']} "
                  f"p{r['prec']} {r['rows']:3d}x{r['nvars']:3d} "
                  f"cells={r['rows']*r['nvars']:6d}")
        return 0
    if args.report:
        return report(queue, Path(args.out_dir))
    run(queue, args.limit, Path(args.out_dir), args.timeout_min,
        args.emit_only, args.resume)
    return 0


if __name__ == "__main__":
    sys.exit(main())
