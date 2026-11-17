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

Every closure decision compares exact Fractions against the exact SAFE;
floats only feed the priority-queue key.

---------------------------------------------------------------------
gate0-measure-w1 (2026-11-17) — measured-s* re-run optimisations.
Profile evidence (lane PROFILE.md): per-node cost = thin jet 0.24 s +
stage G (d1 trees) + stage Hd (d2 diag) + stage Ho (d2 off-diag; 25.7 s
of the 42.1 s analysable-band node); d2 tree union 107k PM nodes;
conservative (unaffordable) nodes cost only the thin jet.

Engine changes, all SOUND (closure is only ever claimed from a
certified boundA / vertex value computed by unchanged `tmcarry` /
`emit_tm2` / `symtree` arithmetic):

1. T2-dead precut (certified, from the thin jet alone, before any
   box-TM work):
   boundA = fClo + sep - cross; the endpoint candidates of min_quad give
   sep <= -sum_i max(|g_i(c)|) w_i, and cross >= 0 (S entries are
   max(|lo|,|hi|) >= 0 and w >= 0).  Hence
     dead := fClo - sum_i max(|g_i(c)|) w_i <= SAFE
   certifies the T2 lever dead.  On such nodes only stage G runs (FIX
   lever and all-mono MONO vertex kept); Hd/Ho and the CONC lever are
   skipped and the open node is split on its widest free dim (the same
   rule as conservative-open nodes).  PQ key = the certified dead bound
   (an UPPER bound of the true boundA — exploration order changes vs
   the old engine; convergence and every closure rule unchanged).
2. sep_early early-out (after Hd): fClo + sep <= SAFE certifies T2 dead
   (cross >= 0) -> skip Ho.  Fires where 1 misses (positive diagonals).
3. P0-parity level escalation: a node still open at its level re-runs
   the full comp set at s+1 .. max_split while (2^s)^nfree <= max_cells
   (the p0_rho1 leaf protocol that produced the 132/188 anchors).  The
   old engine escalated only on CertFailTM (soundness recovery), which
   under-closed vs the P0 protocol.
4. Stage Hd+Ho comps are evaluated in ONE `envelopes` call (one sub-box
   pass, shared node memo) — per-component values are identical either
   way (evaluation is a pure function of (comp tree, sub-box, level)).
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

    def affordable(self, s, nfree):
        """P0 parity: level s affordable iff (2^s)^nfree <= max_cells."""
        return (2 ** s) ** max(nfree, 1) <= self.max_cells


def _open_hw(node, env):
    return [float(dy_f(hi) - dy_f(lo)) / 2
            for lo, hi in EM.dy_box(node.box, env.grid)]


def _open_info(node, env, bound):
    """Open-node info without H data (conservative or precut)."""
    return dict(hw=_open_hw(node, env), t2=bound, bound=bound, mono={},
                conc=set(), conv=set(), G={}, g=[0.0] * 6, S={}, Hlo={},
                Hhi={})


def _verdict_from_hulls(thin, fClo, boxF, free, wF, resg, resh,
                        safeF, stats, env, expr, node, yboxF):
    """FIX / MONO / CONC / T2 decision from the current hulls.

    Returns (kind, info, fixes), kind in
      'FIX' | 'MONO' | 'CONC' | 'T2' | None   (None = open).
    `resh` may be None on dead nodes (no H comps evaluated): only the
    FIX / all-mono MONO levers are then consulted.  Open returns carry
    a certified PQ key in info['bound'] (boundA, sep_early bound, or
    the thin-jet dead bound).
    """
    gbDef = {}
    for i in free:
        g = resg[("g", i)][0]
        gbDef[i] = "+" if g[0][0] > 0 else ("-" if g[1][0] < 0 else None)
    mono = {i for i in free if gbDef[i] is not None}
    monoI = {i: ("lo" if gbDef[i] == "+" else "hi") for i in mono}

    def vertex_min(freevars):
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
            ys = [EX.point_jet(env.N, i, dyad.Dy.from_frac(vtx[i],
                                                           env.N.point_grid))
                  for i in range(6)]
            env.N.sqrt_trace = []
            cj = dy_f(expr(ys, node.sides, yboxF).v.lo)
            stats['corner_evals'] = stats.get('corner_evals', 0) + 1
            vmin = cj if vmin is None else min(vmin, cj)
        return vmin

    if 0 < len(mono) < len(free):
        fixes = {i: (boxF[i][0] if gbDef[i] == "+" else boxF[i][1])
                 for i in mono}
        return 'FIX', None, fixes

    if len(mono) == len(free):
        vmin = vertex_min([])
        if vmin is not None and vmin > safeF:
            return 'MONO', dict(bound=float(vmin), corner=float(vmin),
                                mono=monoI, hw=_open_hw(node, env)), None

    if resh is None:
        return None, None, None

    hbDiag = {i: resh[('h', i, i)][0] for i in free}
    conc = {i for i in free if hbDiag[i][1][0] <= 0}
    conv = {i for i in free if hbDiag[i][0][0] >= 0}

    if all((i in mono) or (i in conc) for i in free) \
            and len(mono) < len(free):
        freevars = [i for i in free if i not in mono]
        vmin = vertex_min(freevars)
        if vmin is not None and vmin > safeF:
            return 'CONC', dict(
                nvertices=2 ** len(freevars), bound=float(vmin),
                mono=monoI, conc=conc, conv=conv, hw=_open_hw(node, env),
                Hlo={i: float(dy_f(hbDiag[i][0])) for i in free},
                Hhi={i: float(dy_f(hbDiag[i][1])) for i in free}), None

    # ---- T2: certified quadratic bound
    sep = F(0)
    for i in free:
        glo, ghi = thin.g[i].lo_frac(), thin.g[i].hi_frac()
        mi = dy_f(hbDiag[i][0])
        sep += EM.min_quad(glo, ghi, mi, wF[i])
    sep_early = fClo + sep
    if sep_early <= safeF:
        # cross >= 0 -> boundA <= sep_early <= SAFE: T2 provably dead
        # (second precut; fires where the thin-jet test missed)
        info = _open_info(node, env, float(sep_early))
        info['mono'] = monoI
        return None, info, None
    cross = F(0)
    Sf = {}
    Gf = {}
    for i in free:
        for j in free:
            if i < j:
                iv = resh[('h', i, j)][0]
                sij = max(abs(dy_f(iv[0])), abs(dy_f(iv[1])))
                Sf[(i, j)] = float(sij)
                cross += sij * wF[i] * wF[j]
    boundA = fClo + sep - cross
    for i in free:
        Gf[i] = (float(dy_f(resg[('g', i)][0][0])),
                 float(dy_f(resg[('g', i)][0][1])))
    info = dict(hw=[float(x) for x in wF], t2=float(boundA),
                bound=float(boundA), boundA=boundA, bound_frac=boundA,
                mono=monoI, conc=conc, conv=conv,
                G=Gf, g=[0.0] * 6, S=Sf,
                Hlo={i: float(dy_f(hbDiag[i][0])) for i in free},
                Hhi={i: float(dy_f(hbDiag[i][1])) for i in free},
                f_c=float(fClo))
    for i in free:
        glo, ghi = Gf[i]
        info['g'][i] = glo if abs(glo) <= abs(ghi) else ghi
    if boundA > safeF:
        return 'T2', info, None
    return None, info, None


def analyse_cert(node, env, kit, expr, stats):
    """Certified analysis of one node; engine.analyse dispatch shapes.

    Returns exactly one of
      ('IA'|'T2'|'MONO'|'CONC', info)
      (None, info)                      open node
      ('FIX', None, fixes)              collapse dims and re-analyse
    """
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

    # ---- thin jet at the dyadic centre (fC/gC/HC) — certified
    ys = [EX.point_jet(Nd, i, dyad.Dy(c[i])) for i in range(6)]
    Nd.sqrt_trace = []
    thin = expr(ys, node.sides, yboxF)
    fClo = dy_f(thin.v.lo)
    stats['thin_evals'] = stats.get('thin_evals', 0) + 1

    def done(rv):
        env.cert_time += time.time() - t0
        return rv

    if not free:
        info = dict(hw=[0.0] * 6, t2=float(fClo), bound=float(fClo),
                    mono={}, conc=set(), conv=set(), G={}, g=[0.0] * 6,
                    S={}, Hlo={}, Hhi={})
        return done(('IA' if fClo > safeF else None, info))

    # ---- T2-dead precut from the thin jet alone (soundness argument in
    # the module docstring; uses only certified point-jet values)
    dead = fClo
    for i in free:
        glo, ghi = thin.g[i].lo_frac(), thin.g[i].hi_frac()
        dead -= max(abs(glo), abs(ghi)) * wF[i]
    dead_node = dead <= safeF

    def envs(comps, s0_):
        res_, _ = TC.envelopes(kit, comps, boxD, Nd, yboxF,
                               s0=s0_, max_split=env.max_split,
                               max_cells=env.max_cells,
                               refine_hw=env.refine_hw)
        return res_

    s0 = env.sched(boxD)
    nfree = len(free)
    comps_g = [("g", i) for i in free]
    comps_h = ([("h", i, i) for i in free]
               + [("h", i, j) for i in free for j in free if i < j])

    # ---- certificates affordable at the start level at all?
    if not env.affordable(s0, nfree):
        # no affordable level exists (P0 cap): conservative-open.  The
        # precut bound is still certified — report it when known.
        stats['certfail_nodes'] = stats.get('certfail_nodes', 0) + 1
        return done((None, _open_info(node, env,
                                      float(dead) if dead_node else -1e9)))

    # ---- stage G (cheap; FIX lever) — keep the CertFailTM contract
    try:
        resg = envs(comps_g, s0)
    except TC.CertFailTM:
        stats['certfail_nodes'] = stats.get('certfail_nodes', 0) + 1
        raise
    resh = None
    if not dead_node:
        try:
            resh = envs(comps_h, s0)      # one pass, shared memo
        except TC.CertFailTM:
            stats['certfail_nodes'] = stats.get('certfail_nodes', 0) + 1
            raise

    kind, info, fixes = _verdict_from_hulls(
        thin, fClo, boxF, free, wF, resg, resh, safeF, stats, env,
        expr, node, yboxF)
    if kind == 'FIX':
        return done(('FIX', None, fixes))
    if kind in ('MONO', 'CONC', 'T2'):
        return done((kind, info))
    if resh is None:
        # T2-dead precut node, no closure lever fired: open (widest-dim
        # split via choose_split_cert's empty-S rule), PQ key = dead
        stats['precut_nodes'] = stats.get('precut_nodes', 0) + 1
        oinfo = _open_info(node, env, float(dead))
        oinfo['mono'] = info['mono'] if info else {}
        return done((None, oinfo))

    # ---- P0-parity escalation: still open at s0 — retry the full comp
    # set at s+1 .. max_split while affordable (tighter hulls -> tighter
    # boundA / possible FIX / vertex closures).
    for s in range(s0 + 1, env.max_split + 1):
        if not env.affordable(s, nfree):
            break
        stats['escalations'] = stats.get('escalations', 0) + 1
        try:
            resall = envs(comps_g + comps_h, s)
        except TC.CertFailTM:
            break                     # keep the shallower result
        kind, info, fixes = _verdict_from_hulls(
            thin, fClo, boxF, free, wF,
            {k: resall[k] for k in comps_g}, resall, safeF, stats, env,
            expr, node, yboxF)
        if kind == 'FIX':
            return done(('FIX', None, fixes))
        if kind in ('MONO', 'CONC', 'T2'):
            return done((kind, info))
        # open: fall through to the next level (info carries the deepest
        # certified boundA)
    return done((None, info))


def choose_split_cert(info):
    """engine.choose_split verbatim over certified S/G (float view)."""
    hw, mono = info['hw'], info.get('mono', {})
    free = [i for i in range(6) if hw[i] > 0]
    gvec = info.get('g') or [0.0] * 6
    S = info.get('S') or {}
    if not free:
        return None
    if not S:
        # conservative-open / precut nodes: split the WIDEST free dim —
        # deterministic, and the only choice that shrinks the wrap that
        # blocked the analysis
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
               SAFE=1e-7, grid=-20, s0=None, max_split=3, max_cells=512,
               tick=None, tick_nodes=25):
    """Certified best-first B&B.  Same dispatch/PQ structure as
    engine.solve; N(P) counts certified-closable leaves only.
    `base_tree_of(sides)` -> symtree base tree; `expr` = certified
    thin-jet closure (ys, sides, ybox) -> Jet over BackendDy.
    `tick(stats, pq, leaves)`, when given, is called every `tick_nodes`
    dispatches (and once after the roots) — the driver owns checkpoint
    serialisation."""
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
                 point_evals=0, L3_SAFETY=0.0, timeout=False,
                 escalations=0, certfail_nodes=0, precut_nodes=0,
                 root_box=[str(v) for pair in root_box for v in pair],
                 t_start=t_start)
    leaves = []
    closed_lb_min = 1e300

    def dispatch(nd):
        nonlocal closed_lb_min
        while True:
            try:
                res = analyse_cert(nd, env, kit_for(nd.sides), expr, stats)
            except TC.CertFailTM:
                # enclosures unaffordable at every level: keep the node
                # OPEN with a conservative bound so L4 splits it first
                # (splitting shrinks width; eventually computable)
                if stats['nodes'] >= max_nodes:
                    stats['timeout'] = True
                    return
                heapq.heappush(pq, (-1e9, next(counter), nd,
                                    _open_info(nd, env, -1e9)))
                stats['nodes'] += 1
                closed_lb_min = min(closed_lb_min, -1e9)
                return
            stats['nodes'] += 1
            if res[0] == 'FIX':
                nd = engine.fix_box(nd, res[2])
                stats['fixes'] += 1
                continue
            kind, info = res
            if kind in ('T2', 'MONO', 'CONC', 'IA'):
                stats['leaves'][kind] = stats['leaves'].get(kind, 0) + 1
                leaves.append((kind, nd, info))
                closed_lb_min = min(closed_lb_min, info.get('bound') or 0.0)
            else:
                if not info.get('S') and info.get('bound', -1e9) > -1e8:
                    stats['precut_nodes'] = \
                        stats.get('precut_nodes', 0) + 1
                heapq.heappush(pq, (info['bound'], next(counter), nd, info))
                closed_lb_min = min(closed_lb_min, info['bound'])
            return

    def maybe_tick(force=False):
        if tick is not None and (force or
                                 stats['nodes'] % tick_nodes == 0):
            tick(stats, pq, leaves)

    for nd in roots:
        dispatch(nd)
    maybe_tick(force=True)
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
        maybe_tick()
    stats['nleaves'] = len(leaves) + len(pq)
    stats['open'] = len(pq)
    stats['leaves_detail'] = leaves
    stats['closed_lb'] = closed_lb_min
    stats['wall'] = time.time() - t_start
    stats['cert_time'] = env.cert_time
    stats['SAFE_float'] = float(SAFE)
    return stats
