"""engine.py — deterministic best-first branch & bound for CertTM2 leaves.

Verbatim port of the g4port prototype `engine_lipsch.py` (ESTIMATE mode:
exact float jet at the box centre + sampled Lipschitz bound on the
Hessian — the third-derivative proxy), plus the box/node helpers from
`engine.py`.  Productionised; the algorithm, the float operation order
and every tie-break are kept bit-compatible so the leaf counts reproduce
the g4port s-curve (PILOT_RESULTS.md: 81/60/47 at safety 10).

Four levers (ENGINE.md):
  L1  second-order Taylor node (exact 1-D minimisation per free dim)
  L2  per-subbox local derivative-sign pruning (FIX)
  L3  concavity glue (CONC leaves: enumerate vertices of mono|conc dims)
  L4  adaptive search (priority queue on the lower bound; split rule
      = most-dangerous |g_i|/R_i dimension, tie-broken deterministically)

Determinism: the L3 diagonal probes use a fixed-seed PRNG
(random.Random(12345), Mersenne Twister — stream stable across CPython
releases); the priority queue ties break on an insertion counter; every
reduction runs over explicitly ordered lists.  No wall-clock, no
unordered-set iteration feeds any decision.

**The L3 estimate is NOT a certificate.**  This module only NAVIGATES;
the emitted certificate comes from the C1 supplier (`emit_tm2.py` on
`dyad.py`), which re-derives every field in exact dyadic interval
arithmetic.
"""

import heapq
import itertools
import random
import time
from fractions import Fraction as F

import exprs as EX
import jetlib as J
import nav

KINK = F(252, 100)
N_AXIS = 2                    # samples per dimension (one on each side)
DIAG_SEED = 12345             # fixed PRNG seed for the 8 diagonal probes
N_DIAG = 8


class Node:
    __slots__ = ('box', 'sides', 'depth')

    def __init__(self, box, sides, depth=0):
        self.box = box
        self.sides = sides
        self.depth = depth


def default_sides(root_box):
    return ['left' if hi <= KINK else
            ('right' if lo >= KINK else 'left')
            for lo, hi in root_box]


def box_hw(box):
    return [(hi - lo) / 2 for lo, hi in box]


def split_box(node, i):
    lo, hi = node.box[i]
    mid = (lo + hi) / 2
    b1 = list(node.box); b1[i] = (lo, mid)
    b2 = list(node.box); b2[i] = (mid, hi)
    return (Node(b1, node.sides, node.depth + 1),
            Node(b2, node.sides, node.depth + 1))


def fix_box(node, fixes):
    b = list(node.box)
    for i, v in fixes.items():
        b[i] = (v, v)
    return Node(b, node.sides, node.depth)


def kink_split(box, sides):
    """Split every slot that straddles the lmfun kink y = 2*h0 = 2.52."""
    sides = list(sides)
    for i in range(6):
        lo, hi = box[i]
        if hi <= KINK:
            sides[i] = 'left'
        elif lo >= KINK:
            sides[i] = 'right'
    out = [Node(list(box), list(sides), 0)]
    for i in range(6):
        nxt = []
        for nd in out:
            lo, hi = nd.box[i]
            if lo < KINK < hi:
                b1 = list(nd.box); b1[i] = (lo, KINK)
                b2 = list(nd.box); b2[i] = (KINK, hi)
                s1 = list(nd.sides); s1[i] = 'left'
                s2 = list(nd.sides); s2[i] = 'right'
                nxt.append(Node(b1, s1, 1))
                nxt.append(Node(b2, s2, 1))
            else:
                nxt.append(nd)
        out = nxt
    return out


# ---------------------------------------------------------------- analysis

def point_jet(y, mkexpr, sides):
    ys = [EX.point_jet(nav.BackendF, i, y[i]) for i in range(6)]
    return mkexpr(ys, sides, None)


def analyse(node, mkexpr, stats):
    t0 = time.time()
    box = node.box
    hw = box_hw(box)
    centre = [(lo + hi) / 2 for lo, hi in box]
    stats['point_evals'] += 1
    pj = point_jet(centre, mkexpr, node.sides)
    f_c = pj.v
    g = [pj.g[i] for i in range(6)]
    H = [[pj.H[i][j] for j in range(6)] for i in range(6)]

    free = [i for i in range(6) if hw[i] > 0]
    if not free:
        info = dict(bound=f_c, hw=hw, mono={}, t2=f_c)
        return ('IA' if f_c > stats['SAFE'] else None), info

    # ---- sampled Lipschitz bound on the Hessian (ESTIMATE)
    # L3d[i][j][k] estimates |d_k H_ij|; the enclosure row for H_ij is
    #   sum_k L3d[i][j][k] * hw_k .
    L3d = [[[0.0] * 6 for _ in range(6)] for _ in range(6)]
    for j in free:
        hj = float(hw[j])
        if hj <= 0:
            continue
        probes = [(box[j][0], hj),
                  (centre[j] - F(int(0.5 * hj * 1e12), 10 ** 12), 0.5 * hj),
                  (centre[j] + F(int(0.5 * hj * 1e12), 10 ** 12), 0.5 * hj),
                  (box[j][1], hj)]
        for pj, d in probes:
            if d <= 0:
                continue
            y = list(centre)
            y[j] = pj
            stats['point_evals'] += 1
            qj = point_jet(y, mkexpr, node.sides)
            for i in range(6):
                for k in range(6):
                    v = abs(qj.H[i][k] - H[i][k]) / d
                    if v > L3d[i][k][j]:
                        L3d[i][k][j] = v
    # diagonal probes: attribute |dH| / sum|t| to every direction k
    _rng = random.Random(DIAG_SEED)
    for _ in range(N_DIAG):
        bits = [1.0 if _rng.random() < 0.5 else -1.0 for _ in free]
        y = list(centre)
        tot = 0.0
        for k, i in enumerate(free):
            y[i] = centre[i] + F(int(bits[k] * float(hw[i]) * 0.999 * 1e12),
                                 10 ** 12)
            y[i] = min(max(y[i], box[i][0]), box[i][1])
            tot += float(hw[i])
        if tot <= 0:
            continue
        stats['point_evals'] += 1
        qj = point_jet(y, mkexpr, node.sides)
        for i in range(6):
            for k in range(6):
                v = abs(qj.H[i][k] - H[i][k]) / tot
                for j in free:
                    if v > L3d[i][k][j]:
                        L3d[i][k][j] = v
    for i in range(6):
        for k in range(6):
            for j in range(6):
                L3d[i][k][j] *= stats['L3_SAFETY']
    # Hessian enclosure row for H_ij: sum_k L3d[i][j][k] hw_k
    RH = [[sum(L3d[i][j][k] * float(hw[k]) for k in free) for j in range(6)]
          for i in range(6)]
    Hlo = [[H[i][j] - RH[i][j] for j in range(6)] for i in range(6)]
    Hhi = [[H[i][j] + RH[i][j] for j in range(6)] for i in range(6)]
    S = [[max(abs(Hlo[i][j]), abs(Hhi[i][j])) for j in range(6)]
         for i in range(6)]
    # gradient enclosure: |g_i(y)-g_i(c)| <= sum_j |H_ij| hw_j + 1/2 sum_j L3 hw_j^2
    Rg = [0.0] * 6
    for i in range(6):
        Rg[i] = sum(abs(H[i][j]) * float(hw[j]) for j in free) \
            + 0.5 * sum(L3d[i][j][j] * float(hw[j]) ** 2 for j in free)
    G = [(g[i] - Rg[i], g[i] + Rg[i]) for i in range(6)]
    # flattened L3 (max over directions) for reporting
    L3 = [[max(L3d[i][j][k] for k in range(6)) for j in range(6)]
          for i in range(6)]

    mono = {}
    for i in free:
        lo, hi = G[i]
        if lo > 0:
            mono[i] = 'lo'
        elif hi < 0:
            mono[i] = 'hi'
    conc = set(i for i in free if Hhi[i][i] <= 0)
    conv = set(i for i in free if Hlo[i][i] >= 0)

    # ---- L1/L3: per-dim exact 1-D minimisation of the quadratic
    sep = 0.0
    for i in free:
        gi = g[i]
        mi = Hlo[i][i]
        hwi = float(hw[i])
        if mi > 0:
            ts = -gi / mi
            ts = max(-hwi, min(hwi, ts))
            qi = gi * ts + 0.5 * mi * ts * ts
        else:
            qi = -abs(gi) * hwi + 0.5 * mi * hwi * hwi
        sep += qi
    cross = sum(S[i][j] * float(hw[i]) * float(hw[j])
                for i in free for j in free if i < j)
    t2 = f_c + sep - cross

    info = dict(f_c=f_c, g=g, G=G, H=H, Hlo=Hlo, Hhi=Hhi, S=S, L3=L3,
                mono=mono, conc=conc, conv=conv, t2=t2, hw=hw,
                dt=time.time() - t0)

    if 0 < len(mono) < len(free):
        fixes = {i: (box[i][0] if s == 'lo' else box[i][1])
                 for i, s in mono.items()}
        return 'FIX', info, fixes

    if t2 > stats['SAFE']:
        info['bound'] = t2
        return 'T2', info

    if len(mono) == len(free):
        vtx = []
        for i in range(6):
            lo, hi = box[i]
            vtx.append(lo if (hw[i] == 0 or mono[i] == 'lo') else hi)
        cj = point_jet(vtx, mkexpr, node.sides).v
        stats['corner_evals'] += 1
        stats['corner_min'] = min(stats.get('corner_min', 1e9), cj)
        if cj > stats['SAFE']:
            info['corner'] = cj
            info['bound'] = cj
            return 'MONO', info
        info['bound'] = t2
        return None, info

    if all((i in mono) or (i in conc) for i in free):
        freevars = [i for i in free if i not in mono]
        ok, vmin = True, 1e9
        for bits in itertools.product((0, 1), repeat=len(freevars)):
            vtx = []
            for i in range(6):
                lo, hi = box[i]
                if hw[i] == 0:
                    vtx.append(lo)
                elif i in mono:
                    vtx.append(lo if mono[i] == 'lo' else hi)
                else:
                    k = freevars.index(i)
                    vtx.append(hi if bits[k] else lo)
            cj = point_jet(vtx, mkexpr, node.sides).v
            stats['corner_evals'] += 1
            vmin = min(vmin, cj)
            if cj <= stats['SAFE']:
                ok = False
                break
        if ok:
            info['nvertices'] = 2 ** len(freevars)
            info['bound'] = vmin
            return 'CONC', info
        info['bound'] = t2
        return None, info

    info['bound'] = t2
    return None, info


def choose_split(node, info):
    """L4: split the dimension contributing most to the radius of the most
    dangerous (smallest |g_i|/R_i) coordinate; deterministic tie-breaks."""
    hw, mono = info['hw'], info['mono']
    free = [i for i in range(6) if hw[i] > 0]
    gvec = info.get('g')
    cand = []
    for i in free:
        if i in mono:
            continue
        R = sum(float(info['S'][i][j]) * float(hw[j]) for j in free)
        gi = abs(float(gvec[i]))
        ratio = gi / R if R > 0 else 0.0
        contrib = [(float(info['S'][i][j]) * float(hw[j]), j) for j in free]
        jbest = max(contrib)[1] if contrib else free[0]
        straddle = 1 if (info['G'][i][0] <= 0 <= info['G'][i][1]) else 0
        cand.append((straddle, -ratio, float(hw[jbest]), jbest))
    if not cand:
        return None
    cand.sort(reverse=True)
    return cand[0][3]


# ---------------------------------------------------------------- solve

def solve(root_box, mkexpr, sides=None, max_nodes=200000,
          L3_SAFETY=10.0, SAFE=1e-7):
    """Best-first B&B.  Returns the stats dict; leaves live in
    `stats['leaves_detail']` as (kind, Node, info) in completion order
    (deterministic).  No file logging here — the caller owns logging."""
    if sides is None:
        sides = default_sides(root_box)
    roots = kink_split(root_box, sides)
    pq = []
    counter = itertools.count()
    stats = dict(point_evals=0, corner_evals=0, nodes=0, fixes=0, leaves={},
                 splits=0, max_depth=0, L3_SAFETY=float(L3_SAFETY),
                 SAFE=float(SAFE))
    leaves = []
    closed_lb_min = 1e300

    def dispatch(nd):
        nonlocal closed_lb_min
        while True:
            res = analyse(nd, mkexpr, stats)
            stats['nodes'] += 1
            if res[0] == 'FIX':
                _, info, fixes = res
                nd = fix_box(nd, fixes)
                stats['fixes'] += 1
                continue
            kind, info = res
            if kind in ('T2', 'MONO', 'CONC', 'IA'):
                stats['leaves'][kind] = stats['leaves'].get(kind, 0) + 1
                leaves.append((kind, nd, info))
                closed_lb_min = min(closed_lb_min, info.get('bound', info['t2']))
            else:
                heapq.heappush(pq, (info['bound'], next(counter), nd, info))
                closed_lb_min = min(closed_lb_min, info['bound'])
            return

    for nd in roots:
        dispatch(nd)
    while pq:
        if stats['nodes'] >= max_nodes:
            stats['timeout'] = True
            break
        bound, _, nd, info = heapq.heappop(pq)
        stats['splits'] += 1
        i = choose_split(nd, info)
        if i is None:
            stats['stuck'] = stats.get('stuck', 0) + 1
            continue
        for ch in split_box(nd, i):
            stats['max_depth'] = max(stats['max_depth'], ch.depth)
            dispatch(ch)
    stats['nleaves'] = len(leaves) + len(pq)
    stats['open'] = len(pq)
    stats['leaves_detail'] = leaves
    stats['closed_lb'] = closed_lb_min
    return stats
