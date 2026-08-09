#!/usr/bin/env python3
"""Untrusted enumeration generator for tame plane graphs.

Direct Python port of the AFP Flyspeck-Tame executable theories
(reference/afp-flyspeck-tame/{Graph,Enumerator,FaceDivision,Plane,Plane1,
Tame,Generator,TameEnum}.thy), mirroring the Lean port in
lean/Kepler/Graphs/. Everything produced here is UNTRUSTED: output is only
ever used after re-checking by the Lean kernel checkers.

Graph representation (as in Graph.thy):
  face  = (vertices: tuple[int,...], final: bool)
  graph = (faces: list[face], n: int, faceListAt: list[list[face]], heights: list[int])
"""

from itertools import count
from functools import lru_cache

# ---------------------------------------------------------------- ListAux

def splitAt(c, vs):
    """ListAux.thy splitAt: split at first occurrence of c."""
    for i, x in enumerate(vs):
        if x == c:
            return (list(vs[:i]), list(vs[i + 1:]))
    return ([], list(vs))

def between(vs, ram1, ram2):
    """ListAux.thy between: vertices strictly between ram1 and ram2 (cyclic)."""
    pre1, post1 = splitAt(ram1, vs)
    if ram2 in post1:
        pre2, _ = splitAt(ram2, post1)
        return pre2
    else:
        pre2, _ = splitAt(ram2, pre1)
        return post1 + pre2

def minimal(f, xs):
    """ListAux.thy minimal: first element minimizing f."""
    best = None
    for x in xs:
        if best is None or f(x) < f(best):
            best = x
    return best

def replace(x, ys, zs):
    """ListAux.thy replace: replace first occurrence of x by list ys."""
    out = []
    done = False
    for z in zs:
        if not done and z == x:
            out.extend(ys)
            done = True
        else:
            out.append(z)
    return out

def mapAt(ns, f, F):
    """ListAux.thy mapAt: apply f at positions ns of list F."""
    return [f(x) if i in ns else x for i, x in enumerate(F)]

def removeKeyList(ws, ps):
    return [p for p in ps if p[0] not in set(ws)]

# ---------------------------------------------------------------- Graph

FINAL, NONFINAL = True, False

def Face(vs, ftype):
    return (tuple(vs), ftype)

def nextElem(xs, b, x):
    """Graph.thy nextElem: successor of x in cyclic list xs with base b."""
    for i, a in enumerate(xs):
        if a == x:
            return xs[i + 1] if i + 1 < len(xs) else b
    return b

def nextVertex(f, v):
    """Graph.thy: f • v"""
    vs = f[0]
    return nextElem(vs, vs[0], v)

def nextVertices(f, n, v):
    for _ in range(n):
        v = nextVertex(f, v)
    return v

def vertices_face(f):
    return f[0]

def final(f):
    return f[1] == FINAL

def faces(g): return g[0]
def countVertices(g): return g[1]
def faceListAt(g): return g[2]
def heights(g): return g[3]

def vertices_graph(g):
    return list(range(countVertices(g)))

def facesAt(g, v):
    return faceListAt(g)[v] if 0 <= v < len(faceListAt(g)) else []

def height(g, v):
    h = heights(g)
    return h[v] if 0 <= v < len(h) else 0

def graph(n):
    """Graph.thy graph: the 'wheel' seed graph with one n-gon."""
    vs = list(range(n))
    fs = [Face(vs, FINAL), Face(list(reversed(vs)), NONFINAL)]
    return (fs, n, [list(fs) for _ in range(n)], [0] * n)

def finals(g):
    return [f for f in faces(g) if final(f)]

def nonFinals(g):
    return [f for f in faces(g) if not final(f)]

def finalGraph(g):
    return nonFinals(g) == []

def finalVertex(g, v):
    return all(final(f) for f in facesAt(g, v))

def degree(g, v):
    return len(facesAt(g, v))

def tri(g, v):
    return len([f for f in facesAt(g, v) if final(f) and len(f[0]) == 3])

def quad(g, v):
    return len([f for f in facesAt(g, v) if final(f) and len(f[0]) == 4])

def except_(g, v):
    return len([f for f in facesAt(g, v) if final(f) and len(f[0]) >= 5])

def vertextype(g, v):
    return (tri(g, v), quad(g, v), except_(g, v))

def neighbors(g, v):
    return [nextVertex(f, v) for f in facesAt(g, v)]

def directedLength(f, a, b):
    """Graph.thy directedLength (precondition: a, b in f)."""
    if a == b:
        return 0
    return len(between(f[0], a, b)) + 1

def setFinal(f):
    return Face(f[0], FINAL)

# ---------------------------------------------------------------- Enumerator

def enumBase(nmax):
    return [[i] for i in range(nmax + 1)]

def enumAppend(nmax, iss):
    return [is_ + [n] for is_ in iss for n in range(is_[-1], nmax + 1)]

def enumerator(inner, outer):
    """Enumerator.thy enumerator (precondition inner >= 3)."""
    nmax = outer - 2
    k = inner - 3
    iss = enumBase(nmax)
    for _ in range(k):
        iss = enumAppend(nmax, iss)
    return [[0] + is_ + [outer - 1] for is_ in iss]

def hideDupsRec(a, bs):
    out = []
    for b in bs:
        out.append(None if a == b else b)
        a = b
    return out

def hideDups(xs):
    if not xs:
        return []
    return [xs[0]] + hideDupsRec(xs[0], xs[1:])

def indexToVertexList(f, v, is_):
    """Enumerator.thy indexToVertexList (precondition hd is = 0)."""
    return hideDups([nextVertices(f, k, v) for k in is_])

# ---------------------------------------------------------------- FaceDivision

def split_face(f, ram1, ram2, newVs):
    vs = f[0]
    f1 = [ram1] + between(vs, ram1, ram2) + [ram2]
    f2 = [ram2] + between(vs, ram2, ram1) + [ram1]
    return (Face(list(reversed(newVs)) + f1, NONFINAL),
            Face(f2 + list(newVs), NONFINAL))

def replacefacesAt(ns, f, fs, F):
    return mapAt(ns, lambda fl: replace(f, fs, fl), F)

def makeFaceFinalFaceList(f, fs):
    return replace(f, [setFinal(f)], fs)

def makeFaceFinal(f, g):
    return (makeFaceFinalFaceList(f, faces(g)),
            countVertices(g),
            [makeFaceFinalFaceList(f, fs) for fs in faceListAt(g)],
            heights(g))

def heightsNewVertices(h1, h2, n):
    return [min(h1 + i + 1, h2 + n - i) for i in range(n)]

def splitFace(g, ram1, ram2, oldF, newVs):
    fs = faces(g); n = countVertices(g); Fs = faceListAt(g); h = heights(g)
    vs1 = between(oldF[0], ram1, ram2)
    vs2 = between(oldF[0], ram2, ram1)
    f1, f2 = split_face(oldF, ram1, ram2, newVs)
    Fs = replacefacesAt(vs1, oldF, [f1], Fs)
    Fs = replacefacesAt(vs2, oldF, [f2], Fs)
    Fs = replacefacesAt([ram1], oldF, [f2, f1], Fs)
    Fs = replacefacesAt([ram2], oldF, [f1, f2], Fs)
    Fs = Fs + [[f1, f2] for _ in newVs]
    return (f1, f2,
            (replace(oldF, [f2], fs) + [f1],
             n + len(newVs),
             Fs,
             h + heightsNewVertices(h[ram1], h[ram2], len(newVs))))

def subdivFaceRec(g, f, u, n, vos):
    if not vos:
        return makeFaceFinal(f, g)
    vo, rest = vos[0], vos[1:]
    if vo is None:
        return subdivFaceRec(g, f, u, n + 1, rest)
    v = vo
    if nextVertex(f, u) == v and n == 0:
        return subdivFaceRec(g, f, v, 0, rest)
    ws = list(range(countVertices(g), countVertices(g) + n))
    f1, f2, g2 = splitFace(g, u, v, f, ws)
    return subdivFaceRec(g2, f2, v, 0, rest)

def subdivFace(g, f, vos):
    return subdivFaceRec(g, f, vos[0], 0, vos[1:])

# ---------------------------------------------------------------- Plane

def maxGon(p):
    return p + 3

def duplicateEdge(g, f, a, b):
    return (2 <= directedLength(f, a, b) and 2 <= directedLength(f, b, a)
            and b in neighbors(g, a))

def containsUnacceptableEdgeSnd(N, v, ws):
    for i in range(len(ws) - 1):
        w, w2 = ws[i], ws[i + 1]
        if v < w and w < w2 and N(w, w2):
            return True
        # Isabelle recurses with (w, ws tail): v becomes w
        # containsUnacceptableEdgeSnd N v (w#ws) checks v<w<w' then recurses on (w, ws)
        # handled by loop with v updated below
        v = w
    return False

def containsUnacceptableEdge(N, vs):
    """Plane.thy containsUnacceptableEdge: single head check, then Snd.
    (No outer recursion — the Snd helper walks the tail.)"""
    if len(vs) < 2:
        return False
    v, w = vs[0], vs[1]
    if v < w and N(v, w):
        return True
    return containsUnacceptableEdgeSnd(N, v, vs[1:])

def containsDuplicateEdge(g, f, v, is_):
    return containsUnacceptableEdge(
        lambda i, j: duplicateEdge(g, f, nextVertices(f, i, v), nextVertices(f, j, v)),
        is_)

def generatePolygon(n, v, f, g):
    enumeration = enumerator(n, len(f[0]))
    enumeration = [is_ for is_ in enumeration
                   if not containsDuplicateEdge(g, f, v, is_)]
    vertexLists = [indexToVertexList(f, v, is_) for is_ in enumeration]
    return [subdivFace(g, f, vs) for vs in vertexLists]

def next_plane0(p, g):
    if finalGraph(g):
        return []
    return [g2 for f in nonFinals(g) for v in f[0]
            for i in range(3, maxGon(p) + 1)
            for g2 in generatePolygon(i, v, f, g)]

def Seed(p):
    return graph(maxGon(p))

# ---------------------------------------------------------------- Plane1

def minimalFace(fs):
    return minimal(lambda f: len(f[0]), fs)

def minimalVertex(g, f):
    return minimal(lambda v: height(g, v), f[0])

def next_plane(p, g):
    fs = nonFinals(g)
    if not fs:
        return []
    f = minimalFace(fs)
    v = minimalVertex(g, f)
    return [g2 for i in range(3, maxGon(p) + 1)
            for g2 in generatePolygon(i, v, f, g)]

# ---------------------------------------------------------------- Tame

squanderTarget = 15410
excessTCount = 6295

def squanderVertex(p, q):
    table = {(0, 3): 6177, (0, 4): 9696, (1, 2): 6557, (1, 3): 6176,
             (2, 1): 7967, (2, 2): 4116, (2, 3): 12846, (3, 1): 3106,
             (3, 2): 8165, (4, 0): 3466, (4, 1): 3655, (5, 0): 395,
             (5, 1): 11354, (6, 0): 6854, (7, 0): 14493}
    return table.get((p, q), squanderTarget)

def squanderFace(n):
    table = {3: 0, 4: 2058, 5: 4819, 6: 7120}
    return table.get(n, squanderTarget)

def tame9a(g):
    return all(3 <= len(f[0]) <= 6 for f in faces(g))

def tame10(g):
    n = countVertices(g)
    return 13 <= n <= 15

def tame10ub(g):
    return countVertices(g) <= 15

def tame11a(g):
    return all(3 <= degree(g, v) for v in vertices_graph(g))

def tame11b(g):
    return all(degree(g, v) <= (7 if except_(g, v) == 0 else 6)
               for v in vertices_graph(g))

def tame12o(g):
    return all(not (except_(g, v) != 0 and degree(g, v) == 6)
               or vertextype(g, v) == (5, 0, 1)
               for v in vertices_graph(g))

# ---------------------------------------------------------------- Generator

def faceSquanderLowerBound(g):
    return sum(squanderFace(len(f[0])) for f in finals(g))

def excessAtType(t, q, e):
    if e == 0:
        if 7 < t + q:
            return squanderTarget
        return squanderVertex(t, q) - t * squanderFace(3) - q * squanderFace(4)
    if t + q + e != 6:
        return 0
    if t == 5:
        return excessTCount
    return squanderTarget

def ExcessAt(g, v):
    if not finalVertex(g, v):
        return 0
    return excessAtType(tri(g, v), quad(g, v), except_(g, v))

def ExcessTable(g, vs):
    out = []
    for v in vs:
        e = ExcessAt(g, v)
        if 0 < e:
            out.append((v, e))
    return out

def deleteAround(g, v, ps):
    ws = []
    for f in facesAt(g, v):
        nxt = nextVertex(f, v)
        if len(f[0]) == 4:
            ws.extend([nxt, nextVertex(f, nxt)])
        else:
            ws.append(nxt)
    return removeKeyList(ws, ps)

def ExcessNotAtRec(ps, g):
    if not ps:
        return 0
    (x, y), rest = ps[0], ps[1:]
    return max(ExcessNotAtRec(rest, g),
               y + ExcessNotAtRec(deleteAround(g, x, rest), g))

def ExcessNotAt(g, v_opt):
    ps = ExcessTable(g, vertices_graph(g))
    if v_opt is not None:
        ps = deleteAround(g, v_opt, ps)
    ps = tuple(tuple(p) for p in ps)
    cache = {}

    def rec(ps):
        if not ps:
            return 0
        if ps in cache:
            return cache[ps]
        (x, y), rest = ps[0], ps[1:]
        r = max(rec(rest),
                y + rec(tuple(tuple(p) for p in deleteAround(g, x, rest))))
        cache[ps] = r
        return r

    return rec(ps)

def squanderLowerBound(g):
    return faceSquanderLowerBound(g) + ExcessNotAt(g, None)

def is_tame13a(g):
    return squanderLowerBound(g) < squanderTarget

def notame(g):
    return not (tame10ub(g) and tame11b(g))

def notame7(g):
    return not (tame10ub(g) and tame11b(g) and is_tame13a(g))

def generatePolygonTame(n, v, f, g):
    enumeration = enumerator(n, len(f[0]))
    enumeration = [is_ for is_ in enumeration
                   if not containsDuplicateEdge(g, f, v, is_)]
    vertexLists = [indexToVertexList(f, v, is_) for is_ in enumeration]
    return [g2 for g2 in (subdivFace(g, f, vs) for vs in vertexLists)
            if not notame(g2)]

def polysizes(p, g):
    lb = squanderLowerBound(g)
    return [n for n in range(3, maxGon(p) + 1)
            if lb + squanderFace(n) < squanderTarget]

def next_tame0(p, g):
    fs = nonFinals(g)
    if not fs:
        return []
    f = minimalFace(fs)
    v = minimalVertex(g, f)
    return [g2 for i in polysizes(p, g)
            for g2 in generatePolygonTame(i, v, f, g)]

# ---------------------------------------------------------------- TameEnum

def is_tame(g):
    return tame10(g) and tame11a(g) and tame12o(g) and is_tame13a(g)

def next_tame(p, g):
    return [g2 for g2 in next_tame0(p, g) if not finalGraph(g2) or is_tame(g2)]

def tame(g):
    return (tame9a(g) and tame10(g) and tame11a(g) and tame11b(g)
            and tame12o(g) and is_tame13a(g))

# ---------------------------------------------------------------- enumeration

def fgraph(g):
    """ArchCompAux.thy fgraph."""
    return [list(f[0]) for f in faces(g)]

def enumerate_seed(p, limit=None):
    """BFS from Seed p over next_tame; returns final graphs found."""
    seen = set()
    finals_found = []
    queue = [Seed(p)]
    while queue:
        g = queue.pop()
        key = repr(g)
        if key in seen:
            continue
        seen.add(key)
        if finalGraph(g):
            finals_found.append(g)
            continue
        for g2 in next_tame(p, g):
            queue.append(g2)
        if limit and len(seen) > limit:
            break
    return finals_found

if __name__ == "__main__":
    import sys
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    found = enumerate_seed(p)
    print(f"seed p={p}: {len(found)} final tame graphs (raw, pre-iso-dedup)")
