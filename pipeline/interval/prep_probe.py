#!/usr/bin/env python3
"""Bounded bb_arb probe over queue entries.

Runs at most `--jobs` bb_arb processes (nice 19), each with a wall timeout and
a node cap, and appends one JSON line per run to `--out`.  Used to fill the
`probe` field of prep_queue.jsonl without committing to a full solve.

Usage
    python3 pipeline/interval/prep_probe.py --queue out/prep_queue.jsonl \
        --route R1 [--max-nodes 400000] [--timeout 20] [--jobs 2] \
        [--mode plain|tm] [--out out/prep_probe.jsonl] [--cert-dir DIR]

Exit status: 0 if every probe run produced a parseable status, else 1.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
DEFAULT_BB = os.path.join(HERE, "tools", "bb_arb")

CLOSED_RE = re.compile(r"CLOSED:\s+leaves=(\d+)\s+nodes=(\d+)")
LIMIT_RE = re.compile(r"节点超限（(\d+)），未闭合叶\s*(\d+)\s*个")

_lock = threading.Lock()


def run_one(bb, row, max_nodes, timeout, mode, cert_dir):
    case = os.path.join(ROOT, row["case_json"])
    cmd = ["nice", "-n", "19", bb, case, "--max-nodes", str(max_nodes)]
    if mode == "tm":
        cmd.append("--tm")
    cert = None
    if cert_dir:
        os.makedirs(cert_dir, exist_ok=True)
        base = os.path.basename(case)[:-5]
        cert = os.path.join(cert_dir, "%s_%s.cert.json" % (base, mode))
        cmd += ["--cert", cert]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout)
        rc = p.returncode
        out, err = p.stdout, p.stderr
        status = "error"
        leaves = nodes = pending = None
        m = CLOSED_RE.search(out)
        if m:
            status = "closed"
            leaves, nodes = int(m.group(1)), int(m.group(2))
        elif rc == 2:
            status = "limit"
            nodes = max_nodes
            m2 = LIMIT_RE.search(err)
            if m2:
                pending = int(m2.group(2))
        elif rc == 1:
            status = "counterexample"
    except subprocess.TimeoutExpired:
        rc = None
        out = err = ""
        status = "timeout"
        leaves = nodes = pending = None
        # best effort: kill happened inside subprocess.run
        if cert and os.path.exists(cert):
            try:
                os.unlink(cert)      # partial cert is not usable
            except OSError:
                pass
    wall = time.time() - t0
    return {
        "idv": row["idv"],
        "mode": mode,
        "route": row.get("route"),
        "status": status,
        "rc": rc,
        "leaves": leaves,
        "nodes": nodes,
        "pending_leaves": pending,
        "wall_s": round(wall, 3),
        "max_nodes": max_nodes,
        "timeout_s": timeout,
        "cert": os.path.relpath(cert, ROOT) if cert and status == "closed"
        else None,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--queue", default=os.path.join(
        HERE, "out", "prep_queue.jsonl"))
    ap.add_argument("--bb", default=DEFAULT_BB)
    ap.add_argument("--route", default="R1",
                    help="route filter (R1/R2/R3/R4) or 'all'")
    ap.add_argument("--ids", default="", help="comma-separated idv filter")
    ap.add_argument("--max-nodes", type=int, default=400000)
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--mode", default="plain", choices=("plain", "tm"))
    ap.add_argument("--out", default=os.path.join(
        HERE, "out", "prep_probe.jsonl"))
    ap.add_argument("--cert-dir", default="")
    ap.add_argument("--skip-existing", action="store_true",
                    help="skip (mode,idv) already present in --out")
    args = ap.parse_args()

    rows = []
    with open(args.queue) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if args.route != "all" and r.get("route") != args.route:
                continue
            if args.ids:
                wanted = {s.strip() for s in args.ids.split(",") if s.strip()}
                if r["idv"] not in wanted:
                    continue
            if not r.get("case_json"):
                continue
            rows.append(r)

    done = set()
    if args.skip_existing and os.path.exists(args.out):
        with open(args.out, errors="replace") as f:
            for line in f:
                try:
                    r = json.loads(line)
                    done.add((r.get("mode"), r["idv"]))
                except (ValueError, KeyError):
                    pass
    rows = [r for r in rows if (args.mode, r["idv"]) not in done]

    print("probing %d records (route=%s, mode=%s, max_nodes=%d, timeout=%ss,"
          " jobs=%d)" % (len(rows), args.route, args.mode, args.max_nodes,
                         args.timeout, args.jobs))
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    out = open(args.out, "a")
    bad = 0

    def work(r):
        nonlocal bad
        res = run_one(args.bb, r, args.max_nodes, args.timeout, args.mode,
                      args.cert_dir)
        with _lock:
            out.write(json.dumps(res, ensure_ascii=False) + "\n")
            out.flush()
            print("PROBE %-26s %-9s leaves=%-7s nodes=%-7s %6.2fs"
                  % (res["idv"], res["status"], res["leaves"], res["nodes"],
                     res["wall_s"]))
            if res["status"] in ("error", "counterexample"):
                bad += 1
        return res

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(work, rows))
    out.close()
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
