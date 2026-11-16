"""engine_cert.py — certified-envelope B&B (Gate-0 P1).

Structure-identical to `engine.py` (same dispatch loop, same FIX /
MONO-vertex / CONC-vertex / T2 / IA levers, same SAFE, same PQ + split
rule), with ONE substitution: every value/gradient/Hessian enclosure the
decisions consume is CERTIFIED (exact dyadic):

  * thin jet  fC/gC/HC — dyadic AD at the exact dyadic centre
    (the landed `exprs`/`jetlib` point-jet path over `dyad.Dy`);
  * box jet   GB_i / HB_ij — the TM-hull C1 supplier
    (`tmcarry.envelopes`: point-coefficient mean-value TM, adaptive
    sub-box refinement on sound failure);
  * per-dim 1-D minimisation — `emit_tm2.min_quad` (exact joint min over
    the gradient interval) = the certified L1;
  * MONO/CONC vertex bounds — certified thin evals at the nav vertices.

Decision order follows engine.analyse (FIX -> T2 -> MONO -> CONC), with
one cost-driven difference: the certified T2 bound needs the full
Hessian, so the cheap vertex levers (MONO/CONC, diag-only) are tried
BEFORE the off-diagonal evaluation.  A leaf that closes closes either
way; only the reported `kind` label can differ (documented in the P1
report).  Every closure decision compares exact Fractions against the
exact SAFE; floats only feed the priority-queue key.
"""

import heapq
import itertools
import time
from fractions import Fraction as F

import dyad                     # noqa: E402
import exprs as EX              # noqa: E402
import engine                   # noqa: E402  (Node/box helpers, verbatim)
import emit_tm2 as EM           # noqa: E402  (dy_box, min_quad)
import symtree as ST            # noqa: E402
import tmcarry as TC            # noqa: E402


def dy_f(d):
    return F(d[0]) * (F(2) ** d[1])


class CertEnv:
    """Per-solve certified state (one BackendDy: pi/mm12 caches)."""

    def __init__(self, grid=-20, s0=None, max_split=3, max_cells=512,
                 refine_hw=F(1, 50)):
        self.N = dyad.BackendDy()
        self.grid = grid
        self.max_split = max_split
        self.s0 = s0            # None = adaptive by max half-width
        self.max_cells = max_cells
        self.refine_hw = refine_hw
        self.cert_time = 0.0

    def sched(self, boxD):
        if self.s0 is not None:
            return self.s0
        hw = max((dy_f(hi) - dy_f(lo)) / 2 for lo, hi in boxD)
        if hw >= F(1, 10):
            return 2
        if hw >= F(3, 100):
            return 1
        return 0


def analyse_cert(node, env, kit, expr, stats):
    """Certified analysis of one node; engine.analyse dispatch shapes."""
    t0 = time.time()
    boxF = node.box
    boxD = EM.dy_box(boxF, env.grid)
    ivs = [(lo, hi) for lo, hi in boxD]
    c, w = EM.dyadic_center_w(ivs)
    wF = [dy_f(x) for x in w]
    free = [i for i in range(6) if boxD[i][0] != boxD[i][1]]
    yboxF = [(dy_f(lo), dy_f(hi)) for lo, hi in boxD]
    Nd = env.N
    safeF = stats['SAFE']
    info = dict(hw=[float(x) for x in wF], t2=None, mono={}, conc=set(),
                conv=set(), G={}, g=[0.0] * 6, S={}, Hlo={}, Hhi={})

    # ---- thin jet at the dyadic centre (fC/gC/HC) — certified
    ys = [EX.point_jet(Nd, i, dyad.Dy(c[i])) for i in range(6)]
    Nd.sqrt_trace = []
    thin = expr(ys, node.sides, yboxF)
    fClo = dy_f(thin.v.lo)

    if not free:
        info['bound'] = float(fClo)
        info['t2'] = float(fClo)
        env.cert_time += time.time() - t0
        return ('IA' if fClo > safeF else None), info

    def envs(comps, s0):
        res, _ = TC.envelopes(kit, comps, boxD, Nd, yboxF,
                              s0=s0, max_split=env.max_split,
                              max_cells=env.max_cells,
                              refine_hw=env.refine_hw)
        return res

    # ---- stage G: gradient enclosures (cheap; FIX lever)
    resg = envs([("g", i) for i in free], env.sched(boxD))
    gbDef = {}
    for i in free:
        g = resg[("g", i)][0]
        gbDef[i] = "+" if g[0][0] > 0 else ("-" if g[1][0] < 0 else None)
    mono = {i for i in free if gbDef[i] is not None}
    info['mono'] = {i: ("lo" if gbDef[i] == "+" else "hi") for i in mono}
    for i in free:
        info['G'][i] = (float(dy_f(resg[('g', i)][0][0])),
                        float(dy_f(resg[('g', i)][0][1])))
        glo, ghi = info['G'][i]
        info['g'][i] = glo if abs(glo) <= abs(ghi) else ghi

    if 0 < len(mono) < len(free):
        fixes = {i: (boxF[i][0] if gbDef[i] == "+" else boxF[i][1])
                 for i in mono}
        env.cert_time += time.time() - t0
        return 'FIX', info, fixes

    # ---- stage Hd: Hessian diagonal (conc/conv + vertex levers)
    resd = envs([("h", i, i) for i in free], env.sched(boxD))
    hbDiag = {i: resd[('h', i, i)][0] for i in free}
    for i in free:
        info['Hlo'][i] = float(dy_f(hbDiag[i][0]))
        info['Hhi'][i] = float(dy_f(hbDiag[i][1]))
    conc = {i for i in free if hbDiag[i][1][0] <= 0}
    conv = {i for i in free if hbDiag[i][0][0] >= 0}
    info['conc'] = conc
    info['conv'] = conv

    def vertex_min(freevars):
        """Certified thin evals at the enumerated vertices (nav box)."""
        vmin = None
        for bits in itertools.product((0, 1), repeat=len(freevars)):
            vtx = []
            for i in range(6):
                lo, hi = boxF[i]
                if i not in free:
                    vtx.append(lo)
                elif i in mono:
                    vtx.append(lo if gbDef[i] == "+" else hi)
                else:
                    k = freevars.index(i)
                    vtx.append(hi if bits[k] else lo)
            ys = [EX.point_jet(Nd, i, dyad.Dy.from_frac(vtx[i],
                                                         Nd.point_grid))
                  for i in range(6)]
            Nd.sqrt_trace = []
            cj = dy_f(expr(ys, node.sides, yboxF).v.lo)
            stats['corner_evals'] = stats.get('corner_evals', 0) + 1
            vmin = cj if vmin is None else min(vmin, cj)
        return vmin

    if len(mono) == len(free):
        # ---- MONO vertex lever (engine: all free dims mono)
        vmin = vertex_min([])
        if vmin is not None and vmin > safeF:
            info['bound'] = float(vmin)
            info['corner'] = float(vmin)
            env.cert_time += time.time() - t0
            return 'MONO', info

    if all((i in mono) or (i in conc) for i in free) \
            and len(mono) < len(free):
        # ---- CONC vertex lever (engine: mono|conc dims, vertices)
        freevars = [i for i in free if i not in mono]
        vmin = vertex_min(freevars)
        if vmin is not None and vmin > safeF:
            info['nvertices'] = 2 ** len(freevars)
            info['bound'] = float(vmin)
            env.cert_time += time.time() - t0
            return 'CONC', info

    # ---- T2: certified quadratic bound (needs the off-diagonal Hessian)
    comps_ho = [("h", i, j) for i in free for j in free if i < j]
    reso = envs(comps_ho, env.sched(boxD)) if comps_ho else {}

    sep = F(0)
    for i in free:
        glo, ghi = thin.g[i].lo_frac(), thin.g[i].hi_frac()
        mi = dy_f(hbDiag[i][0])
        sep += EM.min_quad(glo, ghi, mi, wF[i])
    cross = F(0)
    for i in free:
        for j in free:
            if i < j:
                iv = reso[('h', i, j)][0]
                sij = max(abs(dy_f(iv[0])), abs(dy_f(iv[1])))
                info['S'][(i, j)] = float(sij)
                cross += sij * wF[i] * wF[j]
    boundA = fClo + sep - cross
    info['t2'] = float(boundA)
    info['boundA'] = boundA
    info['f_c'] = float(fClo)
    if boundA > safeF:
        info['bound'] = float(boundA)
        env.cert_time += time.time() - t0
        return 'T2', info
    info['bound'] = float(boundA)
    env.cert_time += time.time() - t0
    return None, info


def choose_split_cert(info):
    """engine.choose_split verbatim over certified S/G (float view)."""
    hw, mono = info['hw'], info.get('mono', {})
    free = [i for i in range(6) if hw[i] > 0]
    gvec = info.get('g') or [0.0] * 6
    S = info.get('S') or {}
    if not free:
        return None
    if not S:
        # conservative-open nodes (certificates unaffordable): split the
        # WIDEST free dim — deterministic, and the only choice that
        # shrinks the wrap that blocked the analysis
        j = max(free, key=lambda i: (float(hw[i]), -i))
        return j
    cand = []
    for i in free:
        if i in mono:
            continue
        R = sum(S.get((min(i, j), max(i, j)), 0.0) * float(hw[j])
                for j in free if j != i)
        gi = abs(float(gvec[i]))
        ratio = gi / R if R > 0 else 0.0
        contrib = [(S.get((min(i, j), max(i, j)), 0.0) * float(hw[j]), j)
                   for j in free if j != i]
        jbest = max(contrib)[1] if contrib else free[0]
        G = info.get('G', {}).get(i, (0.0, 0.0))
        straddle = 1 if (G[0] <= 0 <= G[1]) else 0
        cand.append((straddle, -ratio, float(hw[jbest]), jbest))
    if not cand:
        # all free dims mono but the leaf stayed open (MONO vertex failed
        # and T2 bound negative): split the widest mono dim
        j = max(free, key=lambda i: (float(hw[i]), -i))
        return j
    cand.sort(reverse=True)
    return cand[0][3]


def solve_cert(root_box, base_tree_of, expr, sides=None, max_nodes=4000,
               SAFE=1e-7, grid=-20, s0=None, max_split=3, max_cells=512):
    """Certified best-first B&B.  Same dispatch/PQ structure as
    engine.solve; N(P) counts certified-closable leaves only.
    `base_tree_of(sides)` -> symtree base tree; `expr` = certified
    thin-jet closure (ys, sides, ybox) -> Jet over BackendDy."""
    t_start = time.time()
    if sides is None:
        sides = engine.default_sides(root_box)
    env = CertEnv(grid=grid, s0=s0, max_split=max_split,
                  max_cells=max_cells)
    kits = {}

    def kit_for(sides_):
        key = tuple(sides_)
        if key not in kits:
            kits[key] = ST.TreeKit(base_tree_of(sides_))
        return kits[key]

    roots = engine.kink_split(root_box, sides)
    pq = []
    counter = itertools.count()
    stats = dict(nodes=0, fixes=0, leaves={}, splits=0, max_depth=0,
                 open=0, SAFE=F(SAFE), corner_evals=0, thin_evals=0,
                 point_evals=0, L3_SAFETY=0.0, timeout=False)
    leaves = []
    closed_lb_min = 1e300

    def dispatch(nd):
        nonlocal closed_lb_min
        while True:
            try:
                res = analyse_cert(nd, env, kit_for(nd.sides), expr, stats)
            except TC.CertFailTM as exc:
                # enclosures unaffordable at every level: keep the node
                # OPEN with a conservative bound so L4 splits it first
                # (splitting shrinks width; eventually computable)
                stats['certfail_nodes'] = stats.get('certfail_nodes', 0) + 1
                if stats['nodes'] >= max_nodes:
                    stats['timeout'] = True
                    return
                info = dict(hw=[float(dy_f(hi) - dy_f(lo)) / 2
                                for lo, hi in EM.dy_box(nd.box, env.grid)],
                            t2=-1e9, bound=-1e9, mono={}, conc=set(),
                            conv=set(), G={}, g=[0.0] * 6, S={}, Hlo={},
                            Hhi={})
                heapq.heappush(pq, (-1e9, next(counter), nd, info))
                stats['nodes'] += 1
                closed_lb_min = min(closed_lb_min, -1e9)
                return
            stats['nodes'] += 1
            if res[0] == 'FIX':
                _, info, fixes = res
                nd = engine.fix_box(nd, fixes)
                stats['fixes'] += 1
                continue
            kind, info = res
            if kind in ('T2', 'MONO', 'CONC', 'IA'):
                stats['leaves'][kind] = stats['leaves'].get(kind, 0) + 1
                leaves.append((kind, nd, info))
                closed_lb_min = min(closed_lb_min, info.get('bound') or 0.0)
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
        i = choose_split_cert(info)
        if i is None:
            stats['stuck'] = stats.get('stuck', 0) + 1
            continue
        for ch in engine.split_box(nd, i):
            stats['max_depth'] = max(stats['max_depth'], ch.depth)
            dispatch(ch)
    stats['nleaves'] = len(leaves) + len(pq)
    stats['open'] = len(pq)
    stats['leaves_detail'] = leaves
    stats['closed_lb'] = closed_lb_min
    stats['wall'] = time.time() - t_start
    stats['cert_time'] = env.cert_time
    stats['SAFE_float'] = float(SAFE)
    return stats
