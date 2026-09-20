#!/usr/bin/env python3
"""Phase 4, G4: leaf repair loop for bb_arb certs.

Some cert leaves pass in FLINT ball arithmetic but fail Lean's (looser)
dyadic interval evaluation.  A failing leaf is not a dead end: bisection
refinement is always legal (`splitOK` holds for exact midpoint halves), so
we re-check the leaf in Lean (compiled `FillParams.runLadder` driver —
bit-faithful by construction), split failures on their widest dimension,
and iterate.  The output is a *repaired cert JSON* whose leaf list has the
failures replaced by their passing descendants; feed it to emit_lean.py
exactly like an original cert.

Usage:
  repair_leaves.py <case.json> <cert.json> <out_cert.json>
                   [--max-depth=3] [--chunk=40000] [--keep-going]
"""
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import emit_lean as E

LEAN_DIR = os.environ.get("G4E_LEAN_DIR", "/home/scroll/repos/kepler-g4e/lean")
REPAIR_DIR = os.path.join(LEAN_DIR, "Kepler/Interval/Cases/Repair")


def die(msg):
    sys.exit(f"repair_leaves: {msg}")


def split_box(box):
    """Widest-dim exact midpoint split (dyadic pairs; mid in midRadius form)."""
    widths = [(E.dval(hi) - E.dval(lo), d) for d, (lo, hi) in enumerate(box)]
    _, d = max(widths)
    lo, hi = box[d]
    mid = E.dmid(lo, hi)
    return (box[:d] + ((lo, mid),) + box[d + 1:],
            box[:d] + ((mid, hi),) + box[d + 1:])


def box_json(box):
    def dy(p):
        m, e = p
        if e < 0:
            return {"num": m, "den": 1 << (-e)}
        return {"num": m * (1 << e), "den": 1}
    return [[dy(lo), dy(hi)] for lo, hi in box]


def run_round(mod, n, driver, items, round_no, chunk_size, params_out=None):
    """items: list of (box, hit, depth).  Returns (failing indices, verdicts)
    where verdicts maps item index -> recomputed hit string (disj drivers
    only; None for single-goal drivers).
    driver: ("single", expr) or ("disj", mkexprs, terms, hit_of_goal).
    When params_out is a dict, records {box: (mantissa ints, rung, hit)} for
    every PASS/PASSV leaf (rung from the chunk's RUNG / BESTFAIL header)."""
    kind = driver[0]
    hit_of_goal = driver[3] if kind == "disj" else None
    failures = []
    verdicts = {}
    for c0 in range(0, len(items), chunk_size):
        chunk = items[c0:c0 + chunk_size]
        cname = f"Dr{round_no}C{c0 // chunk_size}"
        boxes_lean = [E.box_lit(b) for b, _, _ in chunk]
        if kind == "disj":
            src = E.stage_a_file_disj(mod + cname, n, driver[1], driver[2],
                                      boxes_lean, len(chunk))
        else:
            src = E.stage_a_file(mod + cname, n, driver[1], boxes_lean,
                                 len(chunk))
        src = src.format(caseid="repair", origop="", vars="", nleaves=len(chunk),
                         prec=None, extra="")
        os.makedirs(REPAIR_DIR, exist_ok=True)
        rel = f"Kepler/Interval/Cases/Repair/{cname}.lean"
        open(os.path.join(LEAN_DIR, rel), "w").write(src)
        print(f"[round {round_no}] chunk {c0 // chunk_size}: "
              f"{len(chunk)} boxes, building+running ...", flush=True)
        p = subprocess.run(["lake", "env", "lean", "--run", rel],
                           cwd=LEAN_DIR, capture_output=True, text=True,
                           timeout=86400)
        lines = (p.stdout + p.stderr).splitlines()
        chunk_fails = 0
        leaf_lines = 0
        driver_errors = []
        rung = None
        for ln in lines:
            parts = ln.split()
            if parts[:1] == ["RUNG"]:
                rung = [int(parts[1]), int(parts[2])]
            elif parts[:1] == ["BESTFAIL"]:
                m = re.search(r"N=(\d+) out=(-?\d+)", ln)
                if m:
                    rung = [int(m.group(1)), int(m.group(2))]
            if len(parts) >= 2 and parts[0].isdigit():
                idx = c0 + int(parts[0])
                if parts[1] in ("PASS", "PASSV", "FAIL"):
                    leaf_lines += 1
                if parts[1] == "FAIL":
                    failures.append(idx)
                    chunk_fails += 1
                    continue
                # PASS / PASSV: schema v1 (i PASS s1 t1 ...) or v2
                # (i PASS k s1 t1 ... / i PASSV k); k re-computes the hit.
                if kind == "disj":
                    k = int(parts[2])
                    hit = hit_of_goal[k]
                    nums = [int(x) for x in parts[3:]]
                else:
                    hit = chunk[int(parts[0])][1]
                    nums = [int(x) for x in parts[2:]]
                verdicts[idx] = hit
                if params_out is not None:
                    params_out[chunk[int(parts[0])][0]] = (nums, rung, hit)
            if "error" in ln.lower() and "BESTFAIL" not in ln:
                driver_errors.append(ln)
        if driver_errors or leaf_lines != len(chunk):
            die(f"driver chunk {c0 // chunk_size} broken: "
                f"{len(driver_errors)} errors, {leaf_lines}/{len(chunk)} "
                f"leaf lines — aborting (no silent clean)\n"
                + "\n".join(driver_errors[:5]))
        print(f"[round {round_no}] chunk {c0 // chunk_size}: "
              f"{chunk_fails} FAIL / {len(chunk)}", flush=True)
    return failures, verdicts


def main():
    max_depth, chunk_size = 3, 5000
    fails_file = None
    args = []
    for a in sys.argv[1:]:
        if a.startswith("--max-depth="):
            max_depth = int(a.split("=", 1)[1])
        elif a.startswith("--chunk="):
            chunk_size = int(a.split("=", 1)[1])
        elif a.startswith("--fails="):
            fails_file = a.split("=", 1)[1]
        elif a == "--keep-going":
            pass
        elif not a.startswith("--"):
            args.append(a)
    if len(args) != 3:
        die(__doc__)
    case = json.load(open(args[0]))
    cert = json.load(open(args[1]))
    if cert["root_box"] != case["box"]:
        die("cert root_box != case box")
    n = len(case["vars"])
    if case.get("disj"):
        # Disj repair (wave-2 D2): the driver carries ALL goals and
        # recomputes the hit per (sub-)leaf — no hit inheritance; the cert
        # hit is only a first-hit-wins hint at FLINT precision.
        mkexprs, terms, goals_manifest = E.fill_goals(case)
        hit_of_goal = {g["index"]: g["label"] for g in goals_manifest}
        driver = ("disj", mkexprs, terms, hit_of_goal)
    else:
        rpn = E.RPN(sqrt_slot=lambda i: ("0", "0"),
                    trans=lambda op, closed: ("2048", "(-64)") if closed else ("N", "out"))
        driver = ("single", rpn.emit(case["prog"]))
    mod = "CRepair" + "".join(ch if ch.isalnum() else "x"
                              for ch in os.path.basename(args[1]).split(".")[0])

    # (box, hit, depth) triples; survivors = verified PASS (possibly split)
    items = [(tuple(E.box_frac(iv) for iv in l["box"]), l["hit"], 0)
             for l in cert["leaves"]]
    params_by_box = {}
    if fails_file is not None:
        # Seeded mode: a prior scan (e.g. sharded stage-A) already verified
        # most leaves; only the seeded failures enter the split loop.
        seed = {int(x) for x in open(fails_file) if x.strip()}
        survivors = [it for i, it in enumerate(items) if i not in seed]
        items = [it for i, it in enumerate(items) if i in seed]
        print(f"repair: seeded {len(items)} failing leaves "
              f"({len(survivors)} pre-verified survivors)", flush=True)
        start_round = 1
    else:
        print(f"repair: {len(items)} leaves, round 0 full scan", flush=True)
        survivors = []
        start_round = 0
    for round_no in range(start_round, max_depth + 1):
        fails, verdicts = run_round(mod, n, driver, items, round_no,
                                    chunk_size if round_no == 0 else 100000,
                                    params_by_box)
        if not fails:
            # hits recomputed by the driver this round (disj); cert hit kept
            # only where there is no verdict (single-goal driver).
            survivors.extend((b, verdicts.get(i, hit), d)
                             for i, (b, hit, d) in enumerate(items))
            print(f"repair: round {round_no} clean — {len(survivors)} "
                  f"surviving leaves total", flush=True)
            break
        failset = set(fails)
        nxt = []
        for i, (b, hit, depth) in enumerate(items):
            if i in failset:
                if depth >= max_depth:
                    die(f"leaf still failing at depth {depth}: {b} hit={hit}")
                l, r = split_box(b)
                # child hits are NOT inherited — next round's driver
                # recomputes them (the parent hit is kept for debug only)
                nxt.append((l, hit, depth + 1))
                nxt.append((r, hit, depth + 1))
            else:
                survivors.append((b, verdicts.get(i, hit), depth))
        print(f"repair: round {round_no}: {len(fails)} failing -> "
              f"{len(nxt)} children to re-check", flush=True)
        items = nxt
    else:
        die(f"still failing after {max_depth} splits")

    out = {"id": cert.get("id"), "root_box": cert["root_box"],
           "prec": cert.get("prec"), "nodes": cert.get("nodes"),
           "repaired": f"{len(cert['leaves'])} original leaves -> "
                       f"{len(survivors)} after repair",
           "leaves": [{"box": box_json(b), "hit": hit}
                      for b, hit, _ in survivors]}
    json.dump(out, open(args[2], "w"))
    print(f"repair: wrote {args[2]} ({len(survivors)} leaves)", flush=True)
    # Params for every leaf that passed through a repair round (descendants
    # of failing leaves); the pre-verified survivors keep their stage-A
    # params — params_merge.py joins the two by box value.
    pfile = args[2] + ".params.json"
    pleaves = [{"box": box_json(b), "params": params_by_box[b][0],
                "rung": params_by_box[b][1], "hit": params_by_box[b][2]}
               for b, _, _ in survivors if b in params_by_box]
    json.dump({"leaves": pleaves}, open(pfile, "w"))
    print(f"repair: wrote {pfile} ({len(pleaves)} param leaves)", flush=True)


if __name__ == "__main__":
    main()
