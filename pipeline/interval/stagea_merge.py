#!/usr/bin/env python3
"""Merge sharded stage-A outputs into one FillParams params file.

Each shard driver (emit_lean.py --stage-a --stage-a-shards=K) covers a
contiguous chunk of `sz` leaves and reports LOCAL leaf indices.  This script:

  scan mode (default): read <dir>/chunk*.out, find every shard's rung,
    print `GLOBAL N out` (max rung in ladder order) and one
    `STALE <chunkfile> <N> <out>` line per shard below the global rung
    (re-run those with the pinned args, then re-scan).
  emit mode (`--emit OUT`): all shards must be at the global rung; write the
    merged params file (RUNG header + globally-indexed PASS lines).

usage: stagea_merge.py <dir> <sz> [--emit OUT]
"""
import glob
import json
import os
import re
import sys

LADDER = [(12, -64), (16, -64), (20, -64), (24, -64), (32, -64), (48, -64),
          (64, -64), (96, -64), (128, -64), (128, -80), (128, -100)]
RANK = {r: i for i, r in enumerate(LADDER)}


def die(msg):
    sys.exit(f"stagea_merge: {msg}")


def load_ladder(d):
    """Ladder single source of truth (wave-2 design D3): `<dir>/manifest.json`
    (schema v2) when present; otherwise the hardcoded copy, with a
    deprecation warning."""
    p = os.path.join(d, "manifest.json")
    if os.path.exists(p):
        m = json.load(open(p))
        if m.get("schema") != 2 or not m.get("ladder"):
            die(f"{p}: not a schema-v2 manifest with a ladder")
        return [tuple(r) for r in m["ladder"]]
    print(f"stagea_merge: warning: no {p} — falling back to the hardcoded "
          "ladder (deprecated; re-emit stage A with schema v2)",
          file=sys.stderr)
    return LADDER


def main():
    emit_out = None
    args = []
    for a in sys.argv[1:]:
        if a == "--emit":
            pass
        elif a.startswith("--emit="):
            emit_out = a.split("=", 1)[1]
        else:
            args.append(a)
    if len(args) != 2:
        die(__doc__)
    d, sz = args[0], int(args[1])
    ladder = load_ladder(d)
    rank = {r: i for i, r in enumerate(ladder)}

    shards = {}
    for f in sorted(glob.glob(os.path.join(d, "chunk*.out"))):
        rung = None
        lines = []
        for ln in open(f):
            parts = ln.split()
            if not parts:
                continue
            if parts[0] == "RUNG":
                rung = (int(parts[1]), int(parts[2]))
            elif parts[0] == "BESTFAIL":
                die(f"{f}: shard ladder exhausted ({ln.strip()}) — "
                    "extend FillParams.ladder or repair leaves")
            elif parts[0].isdigit():
                lines.append(ln.rstrip("\n"))
        if rung is None:
            die(f"{f}: no RUNG line (shard still running or failed?)")
        idx = int(re.search(r"chunk(\d+)", os.path.basename(f)).group(1))
        shards[idx] = (rung, lines, f)

    if not shards:
        die(f"no chunk*.out in {d}")
    for i, s in shards.items():
        if s[0] not in rank:
            die(f"{s[2]}: rung {s[0]} not on the ladder")

    global_rung = max((s[0] for s in shards.values()), key=lambda r: rank[r])
    print(f"GLOBAL {global_rung[0]} {global_rung[1]} "
          f"({len(shards)} shards)")

    stale = [i for i, s in shards.items() if s[0] != global_rung]
    if stale and emit_out is None:
        for i in sorted(stale):
            print(f"STALE {shards[i][2][:-4]} "
                  f"{global_rung[0]} {global_rung[1]}")
        return
    if stale:
        die(f"{len(stale)} shards still below global rung — re-run them first")

    if emit_out is None:
        print("all shards at global rung — ready to emit")
        return

    nlines = 0
    with open(emit_out, "w") as out:
        out.write(f"RUNG {global_rung[0]} {global_rung[1]}\n")
        for i in sorted(shards):
            rung, lines, f = shards[i]
            for ln in lines:
                parts = ln.split(None, 1)
                out.write(f"{i * sz + int(parts[0])} {parts[1]}\n")
                nlines += 1
    print(f"wrote {emit_out}: {nlines} leaves at rung {global_rung}")


if __name__ == "__main__":
    main()
