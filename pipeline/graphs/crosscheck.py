#!/usr/bin/env python3
"""Untrusted cross-check: dedup enumerated fgraphs up to isomorphism and
compare against the Flyspeck/AFP Archive (Tri/Quad/Pent/Hex .ML files).

Isomorphism (PlaneGraphIso.thy): vertex bijection φ with map(map φ) Fs1 = Fs2
up to rotation of each face and permutation of the face list (no reversal).

Canonical form: for a connected plane graph, BFS over darts from a chosen
start dart using face-step and inverse-step generators yields a deterministic
relabeling; the normalized relabeled face list, minimized over all start
darts, is a complete invariant.
"""

import re
import sys
from collections import deque

def faces_to_darts(faces):
    """Map dart (u,v) -> (face index, position) for each directed edge."""
    darts = {}
    for fi, f in enumerate(faces):
        n = len(f)
        for i in range(n):
            darts[(f[i], f[(i + 1) % n])] = (fi, i)
    return darts

def canonical(faces, allow_mirror=True):
    """Canonical code of a connected plane graph given as face list.

    PlaneGraphIso.thy iso_test: g1 ≃ g2 iff pr_iso_test g1 g2 or
    pr_iso_test g1 (map rev g2) — reversal IS allowed, so we minimize
    over the mirror image as well."""
    faces = [tuple(f) for f in faces]
    darts = faces_to_darts(faces)
    best = None
    for d0 in darts:
        code = code_from(faces, darts, d0)
        if code is not None and (best is None or code < best):
            best = code
    if allow_mirror:
        m = canonical([tuple(reversed(f)) for f in faces], allow_mirror=False)
        if m is not None and (best is None or m < best):
            best = m
    return best

def code_from(faces, darts, d0):
    """BFS relabeling from start dart d0; returns normalized face list."""
    label = {}
    nxt = 0

    def lab(v):
        nonlocal nxt
        if v not in label:
            label[v] = nxt
            nxt += 1
        return label[v]

    seen = set()
    q = deque([d0])
    seen.add(d0)
    lab(d0[0]); lab(d0[1])
    while q:
        (a, b) = q.popleft()
        for d in (face_step(faces, darts, a, b), (b, a)):
            if d is None:
                return None  # not a proper closed map
            lab(d[0]); lab(d[1])
            if d not in seen:
                seen.add(d)
                q.append(d)
    if len(seen) != len(darts):
        return None  # not connected through {face-step, inverse}
    out = []
    for f in faces:
        rf = [label[v] for v in f]
        # rotate_min
        k = rf.index(min(rf))
        out.append(tuple(rf[k:] + rf[:k]))
    return tuple(sorted(out))

def face_step(faces, darts, a, b):
    fi, i = darts[(a, b)]
    f = faces[fi]
    c = f[(i + 1) % len(f)]
    d = f[(i + 2) % len(f)]
    return (c, d)

def parse_ml_archive(path):
    """Parse an AFP/flyspeck archive .ML file into a list of fgraphs."""
    txt = open(path).read()
    body = txt[txt.index("["):]
    graphs = []
    depth = 0
    cur = None
    face = None
    for tok in re.findall(r"\[|\]|\d+", body):
        if tok == "[":
            depth += 1
            if depth == 2:
                cur = []
            elif depth == 3:
                face = []
        elif tok == "]":
            if depth == 3:
                cur.append(face)
            elif depth == 2:
                graphs.append(cur)
            depth -= 1
            if depth == 0:
                break
        else:
            if face is not None and depth == 3:
                face.append(int(tok))
    return graphs

if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    import enumerate as E

    p = int(sys.argv[1])
    ml = sys.argv[2]
    depth = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    procs = int(sys.argv[4]) if len(sys.argv) > 4 else 96
    raw = E.enumerate_seed_parallel(p, depth=depth, procs=procs)
    codes = {}
    for g in raw:
        c = canonical(E.fgraph(g))
        if c is not None:
            codes[c] = E.fgraph(g)
    arch = parse_ml_archive(ml)
    arch_codes = {}
    for fg in arch:
        c = canonical(fg)
        if c is not None:
            arch_codes[c] = fg
    mine = set(codes)
    theirs = set(arch_codes)
    print(f"seed p={p}: enumerated {len(raw)} raw -> {len(mine)} iso classes")
    print(f"archive {ml}: {len(arch)} graphs -> {len(theirs)} iso classes")
    print(f"only in enumeration: {len(mine - theirs)}")
    print(f"only in archive:     {len(theirs - mine)}")
