"""tmcarry.py — TM-hull carrier for the C1 supplier trees (Gate-0 P0/P1).

Primary carrier: `PM`, a POINT-coefficient mean-value first-order Taylor
model over the leaf box.  Every linear coefficient is an EXACT dyadic
point; the constant part is a thin dyadic interval (sqrt/recip/atan of
points are irrational); every op's higher-order deviation is an exact
dyadic bound folded into `err`.  All arithmetic is exact dyadic (the
only rounding is +1 ulp on sqrt/recip/atan of points), so the
numerator/denominator correlation of the rad chain and the 19-dihY
summation survive at the first order — the JET3_PLAN §2.3 C1 design
intent ("Δ-族精确值域 / 一阶 TM 携带相关性").

Invariant (per box, |t_i| <= w_i, w0 = Σ_i |a_i| w_i):

    f(y) ∈ v0 + Σ_i a_i·t_i + [-err, +err]

with the EXPANSION POINT convention p := v0[0] and, writing
E := (v0[1] - v0[0]) + err  (constant-part width folded in):

    |f(y) - p - Σ_i a_i t_i| <= E    for every y in the box.

Soundness per op (exact identities + worst-case bounds; pf = |p|):
  mul : fg = pq + (p·Lg + q·Lf)t + R,
        |R| <= pf·E_g + qg·E_f + w0f·E_g + w0g·E_f + E_f·E_g + w0f·w0g
  sq  : u² = p² + 2p·L·t + R,  |R| <= 2·pf·E + w0² + 2·w0·E + E²
  div : 1/g = 1/p - (g-p)/(p·g)   [exact for any p ≠ 0];
        Q := 1/(p·g) ∈ [1/(p·hi_r), 1/(p·lo_r)] from the g range;
        linear coeff -b_i·q_lo (a point of the Q interval), deviation
        w0g·(q_hi - q_lo) + E_g·q_hi into err.
        c_floor (sound external lower bound of the true g, from the
        deltaX corner-min fact) re-anchors p and lifts lo_r BEFORE
        the recip; p ≤ 0 re-anchors at the lifted lo_r.
  sqrt: √g = √p + (g-p)/(√g+√p)   [exact rationalization];
        denominator range ⊆ [2√lo_r, 2√hi_r]; same Q structure.
  atan: atan(g) - atan(p) = (g-p)/(1+ξ²), ξ between g and p [MVT];
        same Q structure with 1+range².

Only nodes reachable after <= 2 symbolic differentiations occur in the
d1/d2 trees (const/var/neg/add/sub/mul/div/sq/sqrt); atan/pi/mm12 are
implemented for completeness (value-tree consumers).

The landed Lean `TaylorM` (tmexact.M: INTERVAL fB and interval dfB) was
measured as a comparison arm (probe_oneleaf.py, 2026-11-16): interval
COEFFICIENTS re-wrap at every product (dfB = interval x interval); a
(1+u²)-type denominator straddles zero and minv fails on the p1 wide
MONO leaf — the M1 interval-coefficient carrier is documented as
insufficient for C1 on wide leaves; PM is the minimal sound fix.
"""

import tmexact as X          # noqa: E402
from fractions import Fraction as F   # noqa: E402
import dyad                  # noqa: E402
import exprs as EX           # noqa: E402
import symtree as ST         # noqa: E402  (tree shapes / tags only)


class CertFailTM(ArithmeticError):
    """A TM evaluation could not proceed (sound abort; caller records it)."""


def _pabs_d(d):
    """|dyadic point|."""
    return (d[0], d[1]) if d[0] >= 0 else (-d[0], d[1])


# =================================================================
# PM — point-coefficient mean-value TM
# =================================================================

class PM:
    """(v0, a, err, w0): see module docstring.  w0 cached."""
    __slots__ = ("v0", "a", "err", "w0")

    def __init__(self, v0, a, err, w0):
        self.v0 = v0          # (lo, hi) dyadic interval
        self.a = a            # tuple of 6 exact dyadic points (m, e)
        self.err = err        # (m, e) dyadic width >= 0
        self.w0 = w0          # cached Σ |a_i| w_i (dyadic point)

    def __repr__(self):
        return "PM(v0=%r, err=%r)" % (self.v0, self.err)


def pm_w0(a, w):
    acc = X.ZERO
    for i in range(6):
        ai = a[i]
        m = -ai[0] if ai[0] < 0 else ai[0]
        acc = X.add(acc, X.mul((m, ai[1]), w[i]))
    return acc


def pm_range(Mm):
    """Certified enclosure (lo, hi) as dyadic interval pairs."""
    we = X.add(Mm.w0, Mm.err)
    return (X.sub(Mm.v0[0], we), X.add(Mm.v0[1], we))


def pm_const(ctx, fr, grid):
    v0 = (dyad.floor_grid(fr, grid), dyad.ceil_grid(fr, grid))
    return PM(v0, (X.ZERO,) * 6, X.ZERO, X.ZERO)


def pm_var(ctx, k):
    y, w = ctx[0], ctx[1]
    a = [X.ZERO] * 6
    a[k] = (1, 0)
    a = tuple(a)
    return PM((y[k], y[k]), a, X.ZERO, pm_w0(a, w))


def pm_neg(Mm):
    lo, hi = Mm.v0
    return PM((X.neg(hi), X.neg(lo)), tuple(X.neg(x) for x in Mm.a),
              Mm.err, Mm.w0)


def pm_add(Mf, Mg):
    v0 = X.iadd(Mf.v0, Mg.v0)
    a = tuple(X.add(p, q) for p, q in zip(Mf.a, Mg.a))
    return PM(v0, a, X.add(Mf.err, Mg.err), X.add(Mf.w0, Mg.w0))


def pm_sub(Mf, Mg):
    return pm_add(Mf, pm_neg(Mg))


def _E(Mm):
    """Total deviation bound E = dx + err (dx = constant-part width)."""
    return X.add(X.sub(Mm.v0[1], Mm.v0[0]), Mm.err)


def pmmul(Mf, Mg, ctx):
    """f*g; soundness derivation in the module docstring."""
    pf, qg = _pabs_d(Mf.v0[0]), _pabs_d(Mg.v0[0])
    a = tuple(X.add(X.mul(Mf.v0[0], Mg.a[i]), X.mul(Mg.v0[0], Mf.a[i]))
              for i in range(6))
    v0 = X.imul(Mf.v0, Mg.v0)
    ef, eg = _E(Mf), _E(Mg)
    err = X.mul(Mf.w0, Mg.w0)
    err = X.add(err, X.add(X.mul(pf, eg), X.mul(qg, ef)))
    err = X.add(err, X.add(X.mul(Mf.w0, eg), X.mul(Mg.w0, ef)))
    err = X.add(err, X.mul(ef, eg))
    return PM(v0, a, err, pm_w0(a, ctx[1]))


def pmsq(Mm, ctx):
    """Square via the expansion-point form (F1 semantics: never the
    interval product x*x)."""
    p = Mm.v0[0]
    ll = X.mul(p, p)
    e = _E(Mm)
    a = tuple(X.mul(X.add(p, p), x) for x in Mm.a)
    err = X.mul(X.add(_pabs_d(p), _pabs_d(p)), e)   # 2|p| E
    err = X.add(err, X.mul(Mm.w0, Mm.w0))           # (L t)^2
    err = X.add(err, X.mul(X.add(Mm.w0, Mm.w0), e)) # 2 w0 E
    err = X.add(err, X.mul(e, e))
    return PM((ll, ll), a, err, pm_w0(a, ctx[1]))


def _reanchor(Mm, p_new):
    """Re-anchor the expansion point to the dyadic point p_new, folding
    the constant-interval shift into err (sound for ANY p_new)."""
    d1 = X.sub(Mm.v0[1], p_new)
    d2 = X.sub(p_new, Mm.v0[0])
    d = d1 if X.ble(d2, d1) else d2
    return PM((p_new, p_new), Mm.a, X.add(Mm.err, d), Mm.w0)


def _range_of(Mm):
    lo = X.sub(Mm.v0[0], X.add(Mm.w0, Mm.err))
    hi = X.add(Mm.v0[1], X.add(Mm.w0, Mm.err))
    return lo, hi


def pmrecip_point(c, grid):
    """Thin enclosure of 1/c for a positive dyadic point c."""
    r = X.recipFloor(c, grid)
    if r is None:
        raise CertFailTM("recipFloor failed on positive point")
    return (r, (r[0] + 1, grid))


def pmrecip_ceil(d, grid):
    """Ceiling of 1/d as a dyadic point (d a positive dyadic point)."""
    r = X.recipFloor(d, grid)
    if r is None:
        raise CertFailTM("recipFloor failed")
    return (r[0] + 1, grid)


def pmdiv(Mf, Mg, ctx, grid, c_floor=None):
    """f/g; soundness derivation in the module docstring."""
    p = Mg.v0[0]
    lo_r, hi_r = _range_of(Mg)
    if c_floor is not None and X.ble(lo_r, c_floor):
        lo_r = c_floor
    if not X.isPos(lo_r):
        lo, hi = pm_range(Mg)
        raise CertFailTM("pmdiv: denominator range not positive "
                         "(v0=%r w0=%r err=%r range=[%r, %r])"
                         % (Mg.v0, Mg.w0, Mg.err, lo, hi))
    if not X.isPos(p):
        p = lo_r                       # re-anchor at the lifted lower end
        Mg = _reanchor(Mg, p)
    D_lo = X.mul(p, lo_r)
    D_hi = X.mul(p, hi_r)
    if not X.isPos(D_lo):
        raise CertFailTM("pmdiv: p*lo_r not positive")
    q_hi = pmrecip_ceil(D_lo, grid)
    q_lo = X.recipFloor(D_hi, grid)
    if q_lo is None:
        raise CertFailTM("pmdiv: recip failed")
    v0 = pmrecip_point(p, grid)
    a = tuple(X.neg(X.mul(b, q_lo)) for b in Mg.a)
    err = X.mul(Mg.w0, X.sub(q_hi, q_lo))
    err = X.add(err, X.mul(_E(Mg), q_hi))
    inv = PM(v0, a, err, pm_w0(a, ctx[1]))
    return pmmul(Mf, inv, ctx)


def pmsqrt(Mm, ctx, grid, c_floor=None):
    """sqrt(g); soundness derivation in the module docstring.
    ctx[2] is the sqrt-triple trace list (bookkeeping for a future Lean
    replay queue)."""
    p = Mm.v0[0]
    lo_r, hi_r = _range_of(Mm)
    if c_floor is not None and X.ble(lo_r, c_floor):
        lo_r = c_floor
    if not X.isPos(lo_r):
        raise CertFailTM("pmsqrt: radicand range not positive")
    if not X.isPos(p):
        p = lo_r
        Mm = _reanchor(Mm, p)
    slo = X.sqrtMantissaRel(p)
    J = X.sqrtRel(p, slo)
    if J is None:
        raise CertFailTM("pmsqrt: sqrtRel failed")
    v0 = (J[0], (J[1][0] + 1, J[1][1]))
    slo_hi = X.sqrtMantissaRel(hi_r)
    J_hi = X.sqrtRel(hi_r, slo_hi)
    slo_lo = X.sqrtMantissaRel(lo_r)
    J_lo = X.sqrtRel(lo_r, slo_lo)
    if J_hi is None or J_lo is None:
        raise CertFailTM("pmsqrt: sqrtRel range failed")
    ctx[2].append((slo, slo_hi, slo_lo))
    den_lo = X.mul((2, 0), J_lo[0])    # <= 2 sqrt(lo_r)
    den_hi = X.mul((2, 0), J_hi[1])    # >= 2 sqrt(hi_r)
    q_hi = pmrecip_ceil(den_lo, grid)
    q_lo = X.recipFloor(den_hi, grid)
    if q_lo is None:
        raise CertFailTM("pmsqrt: recip failed")
    a = tuple(X.mul(x, q_lo) for x in Mm.a)
    err = X.mul(Mm.w0, X.sub(q_hi, q_lo))
    err = X.add(err, X.mul(_E(Mm), q_hi))
    return PM(v0, a, err, pm_w0(a, ctx[1]))


def pmatan(Mm, ctx, N):
    """atan(g) = atan(p) + (g-p)/(1+xi^2), xi between g and p (MVT)."""
    p = Mm.v0[0]
    lo_r, hi_r = _range_of(Mm)
    l2 = X.add(X.mul(lo_r, lo_r), (1, 0))
    h2 = X.add(X.mul(hi_r, hi_r), (1, 0))
    if not X.isPos(l2):
        raise CertFailTM("pmatan: 1+range^2 not positive")
    ap = N.atan(dyad.Dy(p))             # thin atan of the expansion point
    v0 = (ap.lo, (ap.hi[0] + 1, ap.hi[1]))
    q_hi = pmrecip_ceil(l2, N.out)
    q_lo = X.recipFloor(h2, N.out)
    if q_lo is None:
        raise CertFailTM("pmatan: recip failed")
    a = tuple(X.mul(x, q_lo) for x in Mm.a)
    err = X.mul(Mm.w0, X.sub(q_hi, q_lo))
    err = X.add(err, X.mul(_E(Mm), q_hi))
    return PM(v0, a, err, pm_w0(a, ctx[1]))


# ----------------------------------------------------------------- eval

def _floor_for(tag, yboxF, N):
    """deltaX corner-min radicand floor for a sqrt tag (exact rational
    floored to N.floor_grid), or None."""
    if tag is None:
        return None
    xbox = tuple((lo * lo, hi * hi) for lo, hi in yboxF)
    cmin = EX.delta_corner_min(xbox)
    if tag == 'delta':
        return dyad.floor_grid(cmin, N.floor_grid)
    k = int(tag.split(':')[1])
    return dyad.floor_grid(4 * yboxF[k][0] * cmin, N.floor_grid)


def eval_pm(t, ctx, N, yboxF, _memo=None):
    """PM value of a symtree tree over the box (ctx = (y, w, trace))."""
    if _memo is None:
        _memo = {}
    got = _memo.get(id(t))
    if got is not None:
        return got
    op = t[0]
    if op == 'const':
        out = pm_const(ctx, t[1], N.coef_grid)
    elif op == 'var':
        out = pm_var(ctx, t[1])
    elif op == 'neg':
        out = pm_neg(eval_pm(t[1], ctx, N, yboxF, _memo))
    elif op == 'add':
        out = pm_add(eval_pm(t[1], ctx, N, yboxF, _memo),
                     eval_pm(t[2], ctx, N, yboxF, _memo))
    elif op == 'sub':
        out = pm_sub(eval_pm(t[1], ctx, N, yboxF, _memo),
                     eval_pm(t[2], ctx, N, yboxF, _memo))
    elif op == 'mul':
        out = pmmul(eval_pm(t[1], ctx, N, yboxF, _memo),
                    eval_pm(t[2], ctx, N, yboxF, _memo), ctx)
    elif op == 'sq':
        out = pmsq(eval_pm(t[1], ctx, N, yboxF, _memo), ctx)
    elif op == 'div':
        out = pmdiv(eval_pm(t[1], ctx, N, yboxF, _memo),
                    eval_pm(t[2], ctx, N, yboxF, _memo), ctx, N.out)
    elif op == 'sqrt':
        u = eval_pm(t[1], ctx, N, yboxF, _memo)
        fl = _floor_for(t[2], yboxF, N)
        out = pmsqrt(u, ctx, N.out, c_floor=fl)
    elif op == 'atan':
        out = pmatan(eval_pm(t[1], ctx, N, yboxF, _memo), ctx, N)
    elif op == 'pi':
        p = N.pi()
        out = PM((p.lo, p.hi), (X.ZERO,) * 6, X.ZERO, X.ZERO)
    elif op == 'pidiv2':
        p = N.pi() / 2
        out = PM((p.lo, p.hi), (X.ZERO,) * 6, X.ZERO, X.ZERO)
    elif op in ('mm1', 'mm2'):
        EX.mm12(N)
        d = N._mm12[0 if op == 'mm1' else 1]
        out = PM((d.lo, d.hi), (X.ZERO,) * 6, X.ZERO, X.ZERO)
    else:
        raise CertFailTM("eval_pm: node %r" % (op,))
    _memo[id(t)] = out
    return out


# =================================================================
# envelope plumbing
# =================================================================

class TMBox:
    """Dyadic box -> TM context (exact dyadic centre + half-widths)."""

    def __init__(self, boxD):
        ivs = [(lo, hi) for lo, hi in boxD]
        self.y = X.boxCenter(ivs)
        self.w = X.boxW(ivs)
        self.trace = []
        self.ctx = (self.y, self.w, self.trace)


def envelopes(kit, comps, boxD, N, yboxF, s0=0, max_split=3,
              max_cells=128, refine_hw=None):
    """Batch C1-TM enclosures of `comps` over one dyadic box.

    Level schedule (JET3_PLAN §3.4-2 bypass b): all components start at
    sub-box refinement level s0 (2^s equal dyadic cells per free dim);
    a component whose evaluation aborts soundly (CertFailTM, e.g. a d2
    denominator model straddling 0) is retried at level s+1 .. max_split.
    Every component's enclosure is the HULL of its sub-box ranges —
    sound at whatever level it closed.  Returns
      (res, s_used) : res[comp] = ((lo, hi), w0, err, s).
    Raises CertFailTM (with the last error) if some component never
    closes.

    One TMBox + node memo per sub-box is SHARED across components (the
    component trees are sub-DAGs of one another, so this is also the
    main cost lever)."""
    nfree = sum(1 for lo, hi in boxD if (lo[0] != hi[0]) or (lo[1] != hi[1]))
    pending = list(comps)
    res = {}
    last = None
    s = s0
    while pending and s <= max_split:
        if s > 0 and (2 ** s) ** max(nfree, 1) > max_cells:
            break            # level not affordable; keep best-so-far
        subs = _sub_boxes(boxD, s, refine_hw) if s else [list(boxD)]
        failed = {}
        for sub in subs:
            tb = TMBox(sub)
            memo = {}
            subF = [(dfy(lo), dfy(hi)) for lo, hi in sub]
            for comp in pending:
                if comp == 'v':
                    tree = kit.base
                elif comp[0] == 'g':
                    tree = kit.first(comp[1])
                else:
                    tree = kit.second(comp[1], comp[2])
                del tb.trace[:]
                try:
                    Mm = eval_pm(tree, tb.ctx, N, subF, memo)
                except CertFailTM as e:
                    failed[comp] = e
                    continue
                lo, hi = pm_range(Mm)
                got = res.get(comp)
                if got is None:
                    res[comp] = [(lo, hi), Mm.w0, Mm.err, s]
                else:
                    w0 = got[1] if X.ble(Mm.w0, got[1]) else Mm.w0
                    er = got[2] if X.ble(Mm.err, got[2]) else Mm.err
                    res[comp] = [(X.dmin(got[0][0], lo), X.dmax(got[0][1], hi)),
                                 w0, er, got[3]]
        pending = list(failed)
        last = next(iter(failed.values()), None)
        s += 1
    if pending:
        if last is None:
            raise CertFailTM("no affordable refinement level for %d free "
                             "dim(s) (max_cells=%d)"
                             % (nfree, max_cells))
        raise last
    return res, max(g[3] for g in res.values())


def envelope(kit, comp, tb, N, yboxF, memo):
    """C1-TM enclosure of one symbolic component on ONE box (no
    refinement) -> ((lo, hi), w0, err)."""
    if comp == 'v':
        tree = kit.base
    elif comp[0] == 'g':
        tree = kit.first(comp[1])
    else:
        tree = kit.second(comp[1], comp[2])
    del tb.trace[:]
    Mm = eval_pm(tree, tb.ctx, N, yboxF, memo)
    lo, hi = pm_range(Mm)
    return (lo, hi), Mm.w0, Mm.err


def _sub_boxes(boxD, s, refine_hw=None):
    """Refine every free dim into 2^s CONSECUTIVE dyadic cells that cover
    the dim (endpoints outward-rounded to the parent grid; cells overlap
    by <= 1 ulp, which only makes the union cover more).  `refine_hw`:
    only dims whose half-width is >= this Fraction are refined (narrow
    dims contribute nothing to the wrap and are kept whole — the union
    still covers the box).  Returns a list of dyadic boxes."""
    grids = []
    for lo, hi in boxD:
        free = (lo[0] != hi[0]) or (lo[1] != hi[1])
        if free and refine_hw is not None:
            hw = dfy(X.dmax(X.sub(hi, lo), X.ZERO)) / 2
            free = hw >= refine_hw
        if free:
            lof, hif = dfy(lo), dfy(hi)
            pts = [lof + (hif - lof) * F(k, 2 ** s) for k in range(2 ** s + 1)]
            cells = [(dyad.floor_grid(pts[k], lo[1]),
                      dyad.ceil_grid(pts[k + 1], lo[1]))
                     for k in range(2 ** s)]
            grids.append(cells)
        else:
            grids.append([(lo, hi)])
    out = [[]]
    for grid in grids:
        out = [b + [cell] for b in out for cell in grid]
    return out


def _envelope_refined(kit, comp, boxD, N, yboxF, max_split):
    if comp == 'v':
        tree = kit.base
    elif comp[0] == 'g':
        tree = kit.first(comp[1])
    else:
        tree = kit.second(comp[1], comp[2])
    best = None
    prev_w = None
    last = None
    for s in range(max_split + 1):
        subs = _sub_boxes(boxD, s, refine_hw) if s else [list(boxD)]
        acc = None
        w0m = errm = None
        try:
            for sub in subs:
                tb = TMBox(sub)
                subF = [(dfy(lo), dfy(hi)) for lo, hi in sub]
                memo = {}
                del tb.trace[:]
                Mm = eval_pm(tree, tb.ctx, N, subF, memo)
                lo, hi = pm_range(Mm)
                if acc is None:
                    acc = (lo, hi)
                    w0m, errm = Mm.w0, Mm.err
                else:
                    acc = (X.dmin(acc[0], lo), X.dmax(acc[1], hi))
                    if X.ble(w0m, Mm.w0):
                        w0m = Mm.w0
                    if X.ble(errm, Mm.err):
                        errm = Mm.err
        except CertFailTM as e:
            last = e
            continue
        w = dfy(acc[1]) - dfy(acc[0])
        if best is None or w < best[0]:
            best = (w, acc, w0m, errm, s)
        if prev_w is not None and w * 10 > prev_w * 7:
            break            # improvement < 30%: stalled, keep best
        prev_w = w
    if best is None:
        raise last
    return best[1], best[2], best[3], best[4]


def dfy(d):
    return F(d[0]) * (F(2) ** d[1])
