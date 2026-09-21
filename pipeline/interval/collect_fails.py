#!/usr/bin/env python3
"""Collect FAIL leaf global indices from stage-A chunk outs (BESTFAIL
shards) into a repair --fails seed file.  Also prints a per-chunk rung
summary so STALE chunks (below the global rung) can be spotted.

usage: collect_fails.py <stagea_dir> <sz> <out_fails_file>
"""
import glob
import os
import re
import sys

d, sz, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
fails = []
nchunks = nbest = 0
for f in sorted(glob.glob(os.path.join(d, "chunk*.txt.out"))):
    idx = int(re.search(r"chunk(\d+)", os.path.basename(f)).group(1))
    hdr = None
    nf = 0
    for ln in open(f):
        p = ln.split()
        if not p:
            continue
        if p[0] in ("RUNG", "BESTFAIL"):
            hdr = ln.strip()
        elif p[0].isdigit() and p[1] == "FAIL":
            fails.append(idx * sz + int(p[0]))
            nf += 1
    nchunks += 1
    if hdr and hdr.startswith("BESTFAIL"):
        nbest += 1
    print(f"chunk{idx:05d}: {hdr}  fails={nf}")
open(out, "w").write("".join(f"{i}\n" for i in fails))
print(f"wrote {out}: {len(fails)} failing leaves "
      f"({nbest}/{nchunks} BESTFAIL chunks)", file=sys.stderr)
