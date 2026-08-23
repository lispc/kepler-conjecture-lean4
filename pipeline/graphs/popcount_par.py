#!/usr/bin/env python3
"""Parallel pops counter for a single Pent frontier root's subtree.

Replicates Lean Worklist.loop semantics: no dedup, one unit per pop.
Splits the first `split_depth` levels under the root into pieces and counts
them with a process pool. Duplicates across pieces are ~0 in this
enumerator (verified in the original run), matching the no-dedup loop.

Usage: popcount_par.py <root-index> [split_depth=3] [procs=120]
"""
import sys
import time
import multiprocessing as mp

sys.path.insert(0, '/home/scroll/repos/kepler-conjecture-lean4/pipeline/graphs')
from enumerate import frontier, next_tame, finalGraph

P = 2

def count_subtree(g):
    cnt = 0
    stack = [g]
    while stack:
        x = stack.pop()
        cnt += 1
        if not finalGraph(x):
            stack.extend(next_tame(P, x))
    return cnt

if __name__ == '__main__':
    j = int(sys.argv[1])
    split_depth = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    procs = int(sys.argv[3]) if len(sys.argv) > 3 else 120
    t0 = time.time()

    roots = frontier(P, 3)
    root = roots[j]
    print(f"frontier(2,3) size={len(roots)}, root j={j}, split_depth={split_depth}", flush=True)

    # expand split levels, counting internal (non-piece) nodes
    internal = 1  # the root itself
    level = [root]
    for d in range(split_depth):
        nxt = []
        for g in level:
            if finalGraph(g):
                internal += 0  # final node: counted, no children
                continue
            ch = next_tame(P, g)
            nxt.extend(ch)
        # every node in `level` was counted as internal except the root's
        # children generation above; count nodes at this level:
        # (root already counted; level nodes beyond root counted below)
        level = nxt
        # nodes in nxt will be counted either as internal (next iteration)
        # or as piece roots (final iteration)
        if d < split_depth - 1:
            internal += len(level)
    pieces = level
    print(f"split: {len(pieces)} pieces, internal nodes={internal}, "
          f"setup {time.time()-t0:.0f}s", flush=True)

    done = 0
    total = internal
    with mp.Pool(procs) as pool:
        for c in pool.imap_unordered(count_subtree, pieces, chunksize=1):
            total += c
            done += 1
            if done % 10 == 0 or done == len(pieces):
                el = time.time() - t0
                print(f"pieces {done}/{len(pieces)} pops_so_far={total} "
                      f"elapsed={el:.0f}s", flush=True)
    print(f"DONE j={j} pops={total} total_time={time.time()-t0:.0f}s", flush=True)
