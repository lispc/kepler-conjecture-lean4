#!/usr/bin/env python3
"""Merge sharded stage-A params with repair-loop params into one FillParams
params file covering a repaired certificate.

Box-value keyed: stage B (emit_lean.py --bbg) looks params up by cert box,
so the merge only needs to map every repaired-cert leaf box to its mantissa
list.  Sources, in priority order:
  1. <repair.params.json> — leaves that went through the repair loop
     (descendants of failing leaves), each with its own rung;
  2. <stagea_dir>/chunk*.out — pre-verified leaves from sharded stage A
     (global index i*sz+local ↔ original cert leaf order).
The global rung is the max (ladder order) over all contributing rungs;
sqrt mantissas are rung-independent, so mixing sources is sound.

usage: params_merge.py <orig_cert.json> <stagea_dir> <sz>
                       <repaired_cert.json> <repair.params.json> <out.txt>
"""
import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import emit_lean as E

LADDER = [(12, -64), (16, -64), (20, -64), (24, -64), (32, -64), (48, -64),
          (64, -64), (96, -64), (128, -64), (128, -80), (128, -100)]
RANK = {r: i for i, r in enumerate(LADDER)}


def die(msg):
    sys.exit(f"params_merge: {msg}")


def load_manifest(d):
    """Manifest single source of truth (wave-2 design D3):
    `<dir>/manifest.json` (schema v2) when present; otherwise None and the
    hardcoded ladder, with a deprecation warning."""
    p = os.path.join(d, "manifest.json")
    if os.path.exists(p):
        m = json.load(open(p))
        if m.get("schema") != 2 or not m.get("ladder"):
            die(f"{p}: not a schema-v2 manifest with a ladder")
        return m
    print(f"params_merge: warning: no {p} — falling back to the hardcoded "
          "ladder (deprecated; re-emit stage A with schema v2)",
          file=sys.stderr)
    return None


def box_key(box_json):
    return tuple(E.box_frac(iv) for iv in box_json)


def main():
    if len(sys.argv) != 7:
        die(__doc__)
    orig_cert = json.load(open(sys.argv[1]))
    stagea_dir, sz = sys.argv[2], int(sys.argv[3])
    repaired = json.load(open(sys.argv[4]))
    rparams = json.load(open(sys.argv[5]))
    outpath = sys.argv[6]
    manifest = load_manifest(stagea_dir)
    ladder = [tuple(r) for r in manifest["ladder"]] if manifest else LADDER
    rank = {r: i for i, r in enumerate(ladder)}
    # schema v2: goal label -> descriptor (repair params carry recomputed
    # hit labels; the merged file needs the goal index k).
    goal_of_label = ({g["label"]: g for g in manifest.get("goals", [])}
                     if manifest else None)

    rungs = []
    old = {}
    orig_boxes = [box_key(l["box"]) for l in orig_cert["leaves"]]
    for f in sorted(glob.glob(os.path.join(stagea_dir, "chunk*.out"))):
        idx = int(re.search(r"chunk(\d+)", os.path.basename(f)).group(1))
        for ln in open(f):
            parts = ln.split()
            if not parts:
                continue
            if parts[0] == "RUNG":
                rungs.append((int(parts[1]), int(parts[2])))
            elif parts[0] == "BESTFAIL":
                # Failing leaves in this shard get no params here; they must
                # be covered by the repair params (final lookup will verify).
                print(f"params_merge: note BESTFAIL shard {f} ({ln.strip()})",
                      file=sys.stderr)
            elif parts[0].isdigit() and parts[1] in ("PASS", "PASSV"):
                # schema v2: `i PASS k s1 t1 ...` / `i PASSV k` — keep the
                # status word and everything after the local index verbatim
                # (stage B re-validates against the manifest goals).
                g = idx * sz + int(parts[0])
                old[orig_boxes[g]] = (parts[1], parts[2:])

    new = {}
    for l in rparams["leaves"]:
        rungs.append(tuple(l["rung"]))
        hit = l.get("hit")
        if goal_of_label is not None and hit is not None:
            # schema v2 (wave-2 W4): repair recomputed the hit; map the goal
            # label back to its index and keep the PASS/PASSV shape.
            g = goal_of_label.get(hit)
            if g is None:
                die(f"repair hit label {hit!r} not in manifest goals")
            if g["kind"] == "varLt":
                if l["params"]:
                    die(f"varLt repair leaf with params: {hit}")
                new[box_key(l["box"])] = ("PASSV", [str(g["index"])])
            else:
                new[box_key(l["box"])] = ("PASS", [str(g["index"])]
                                          + [str(x) for x in l["params"]])
        else:
            # v1-shaped (main-goal pos fills, single-goal pipeline)
            new[box_key(l["box"])] = ("PASS", [str(x) for x in l["params"]])
    if not rungs:
        die("no rungs found in any source")
    for r in rungs:
        if r not in rank:
            die(f"rung {r} not on the ladder")
    global_rung = max(rungs, key=lambda r: rank[r])

    missing = 0
    with open(outpath, "w") as out:
        out.write(f"RUNG {global_rung[0]} {global_rung[1]}\n")
        for i, l in enumerate(repaired["leaves"]):
            key = box_key(l["box"])
            entry = new.get(key) or old.get(key)
            if entry is None:
                print(f"missing params for leaf {i}: {key}", file=sys.stderr)
                missing += 1
                continue
            status, params = entry
            tail = f" {' '.join(params)}" if params else ""
            out.write(f"{i} {status}{tail}\n")
    if missing:
        die(f"{missing} repaired-cert leaves have no params")
    if manifest is not None:
        # Repaired-certificate manifest for stage B (`--manifest`): goals and
        # ladder unchanged (the real invariants), nleaves tracks the repaired
        # cert (bisection may have added leaves).  The stage-A manifest in
        # <stagea_dir> stays untouched.
        rm = dict(manifest)
        rm["nleaves"] = len(repaired["leaves"])
        rm["repaired_from"] = manifest.get("nleaves")
        mp = outpath + ".manifest.json"
        with open(mp, "w") as f:
            json.dump(rm, f, indent=1)
            f.write("\n")
        print(f"params_merge: wrote {mp} (repaired manifest, "
              f"nleaves {manifest.get('nleaves')} -> {len(repaired['leaves'])})")
    print(f"params_merge: wrote {outpath} — {len(repaired['leaves'])} leaves, "
          f"global rung {global_rung} ({len(old)} stage-A + {len(new)} repair)")


if __name__ == "__main__":
    main()
