#!/usr/bin/env python3
"""Driver: full-scale Lean verification of precomputed LP terminals.

Input:  a task list (JSON) of terminals to verify; each with
        {id, graph, ti, hypermap_string} (batch1 root-LP schema) or
        {id, graph, ti, data_text, infeasible} (batch2a schema).
Work:   per terminal — generate col-major module under $LPRUN_ROOT/gen
        (gen_data -> glpsol -> flatten -> SoPlex exact -> socert emit),
        then `lean Bench.lean` with a standalone LEAN_PATH (never touches
        the repo .lake), record one JSON line, delete artifacts.
Resume: skips ids already recorded PASS (exit 0) in results.jsonl.

（2026-09-06 重启后重建版：迁入 git 持久化。根目录用 LPRUN_ROOT 环境
变量，默认 /dev/shm/lprun；results.jsonl 同时镜像到
/home/scroll/lprun-logs/（backup_logs 线程，5 分钟周期）。）
"""
import argparse, hashlib, json, os, resource, shutil, subprocess, sys, time
import threading
from pathlib import Path

REPO_LP = "/home/scroll/repos/kepler-conjecture-lean4/pipeline/lp"
ROOT = Path(os.environ.get("LPRUN_ROOT", "/dev/shm/lprun"))
sys.path.insert(0, str(ROOT))
sys.path.insert(0, REPO_LP)
sys.path.insert(0, REPO_LP + "/run")

GEN = ROOT / "gen"
RESULTS = ROOT / "results.jsonl"
PROGRESS = ROOT / "progress.json"
LEAN_BIN = str(Path.home() / ".elan/bin/lean")
LOG_BACKUP = Path("/home/scroll/lprun-logs")


def lean_env() -> dict:
    env = dict(os.environ)
    lp = (ROOT / "leanpath.txt").read_text().strip()
    env["LEAN_PATH"] = lp
    return env


def record(line: dict):
    with RESULTS_LOCK:
        with open(RESULTS, "a") as f:
            f.write(json.dumps(line) + "\n")
            f.flush()
            os.fsync(f.fileno())


RESULTS_LOCK = threading.Lock()


def already_done(done: dict, tid: str) -> bool:
    return done.get(tid) == 0


def load_done() -> dict:
    done = {}
    if RESULTS.exists():
        for line in RESULTS.read_text().splitlines():
            try:
                r = json.loads(line)
                done[r["id"]] = r["exit"]
            except Exception:
                pass
    return done


def mem_available_gb() -> float:
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1e6
    return 0.0


def wait_for_memory(threshold_gb: float = 25.0, timeout: float = 7200.0):
    t0 = time.time()
    while mem_available_gb() < threshold_gb:
        if time.time() - t0 > timeout:
            return
        time.sleep(20)


def work_one(task: dict, env: dict, timeout: int) -> dict:
    import gen_one
    tid = task["id"]
    mod = "T" + tid.replace(".", "_").replace("-", "_")
    wdir = ROOT / "work" / tid
    gdir = GEN / "lean/Kepler/LP" / mod
    t0 = time.time()
    sha = ""
    exitcode = out = secs = rss_kb = None
    try:
        shutil.rmtree(wdir, ignore_errors=True)
        shutil.rmtree(gdir, ignore_errors=True)
        gen_one.generate(task.get("hypermap_string") or "", mod,
                         0 if task.get("infeasible") else 12, wdir,
                         data_text=task.get("data_text"),
                         slack_infeasible=task.get("infeasible", False))
        bench = gdir / "Bench.lean"
        sha = hashlib.sha256((gdir / "Data.lean").read_bytes()).hexdigest()
        wait_for_memory()
        pre = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        r = subprocess.run([LEAN_BIN, str(bench)], env=env,
                           capture_output=True, text=True, timeout=timeout)
        exitcode, out = r.returncode, (r.stdout + r.stderr)[-4000:]
        rss_kb = max(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, pre)
        secs = round(time.time() - t0, 1)
    except subprocess.TimeoutExpired:
        exitcode, out = 124, "lean timeout"
        secs = round(time.time() - t0, 1)
    except Exception as e:  # generation failure
        exitcode, out = 130, f"gen error: {e!r}"[:4000]
        secs = round(time.time() - t0, 1)
    finally:
        shutil.rmtree(wdir, ignore_errors=True)
        shutil.rmtree(gdir, ignore_errors=True)
    return {"id": tid, "graph": task["graph"], "ti": task.get("ti", 0),
            "exit": exitcode, "seconds": secs, "sha256_Data": sha,
            "rss_kb": rss_kb,
            "msg": out if exitcode != 0 else ""}


def backup_logs():
    import shutil as sh
    dest = LOG_BACKUP
    dest.mkdir(exist_ok=True)
    while True:
        time.sleep(300)
        try:
            if RESULTS.exists():
                sh.copy(RESULTS, dest / "results.jsonl")
        except Exception:
            pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tasks", required=True, help="JSON list of tasks")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--lean-timeout", type=int, default=5400)
    ap.add_argument("--limit", type=int, default=None)
    a = ap.parse_args()

    tasks = json.load(open(a.tasks))
    if a.limit:
        tasks = tasks[: a.limit]
    done = load_done()
    todo = [t for t in tasks if not already_done(done, t["id"])]
    print(f"[driver] {len(tasks)} tasks, {len(todo)} todo, "
          f"{len(tasks)-len(todo)} already done", flush=True)
    if not todo:
        return

    env = lean_env()
    from concurrent.futures import ProcessPoolExecutor, as_completed
    import multiprocessing as mp
    threading.Thread(target=backup_logs, daemon=True).start()
    n_pass = n_fail = 0
    t_start = time.time()

    with ProcessPoolExecutor(max_workers=a.workers, mp_context=mp.get_context("fork")) as ex:
        futs = [ex.submit(work_one, t, env, a.lean_timeout) for t in todo]
        for i, fut in enumerate(as_completed(futs)):
            r = fut.result()
            record(r)
            if r["exit"] == 0:
                n_pass += 1
            else:
                n_fail += 1
                print(f"[driver] FAIL {r['id']} exit={r['exit']} {r['msg'][:300]}", flush=True)
            if (i + 1) % 5 == 0 or i + 1 == len(todo):
                el = time.time() - t_start
                prog = {"done": i + 1, "todo": len(todo), "pass": n_pass,
                        "fail": n_fail, "elapsed_s": round(el),
                        "rate_per_hour": round((i + 1) / el * 3600, 2)}
                PROGRESS.write_text(json.dumps(prog))
                print(f"[driver] progress {prog}", flush=True)
    print(f"[driver] ALL DONE pass={n_pass} fail={n_fail}", flush=True)


if __name__ == "__main__":
    main()
