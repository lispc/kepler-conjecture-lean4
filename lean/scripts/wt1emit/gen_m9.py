#!/usr/bin/env python3
"""gen_m9.py — emit the DC-only wt1 tree certificate for one of the **221
D1 certificate boxes** (`boxes221.json`, round M9).

Derived from `gen_m8.py` (which is unchanged).  **Only the `matan` channel
changes**; everything else (fCN2 real bodies, the one-tree fan, the wide-corner
`Dlt`, `dSqrt` literals, one op per `rfl`, literal V/G, KZ = 1024, the
`fTop_eq_w1F3Z/O` bridge, the 7 `#print axioms`) is inherited op for op.

**The M8 matan channel and why it failed.**  M8 measured `matan` on the whole
box interval (`dMatan9` / `dMatanWp` / `dMatanU9` / `dMatanMir`) and took the
derivative from the interval formula `dMatanD A Mv`.  On the D1 cover the value
bracket is 1.1–248× wider than the cover's own endpoint-monotone design
(`layout9`'s `PB`), 196/221 boxes had `slackZ ≤ 0`, and 8 boxes have a
genuinely negative `matan` argument (`dLoBig` false).  The v3 Python prediction
(`wt1-m8-preflight-w1`, `M8B-V2-PREDICT.md`) measured the fix: endpoint value
brackets + `matan` monotonicity, and endpoint derivative brackets + `matanD`
monotonicity, are 221/221 with positive slack (min +1.06e-5).

**The M9 matan channel** (landed kit `DCMatanMono` + `M8Kit`):

  * value  = `dMatanMono A MvLo MvHi` — the monotone hull of the two endpoint
    point brackets `[matan(aHi).lo, matan(aLo).hi]` (K1).  Each endpoint
    bracket is the landed four-arm point evaluation (`dMatan9` / `dMatanWp` /
    `dMatanU9` / `dMatanTightW`+`dMatanMir`, branch table = `layout9`'s
    `point_bracket`), a **negative** endpoint uses `lkB_matan_neg_pt`'s exact
    rational artanh bracket through `dc_mem_of_qinterval` (K2), and a zero
    endpoint uses `matan 0 = 1`;
  * gradient = `dMatanDHullPos` / `dMatanDHullNeg` / `dMatanDHullCross` — the
    monotone hull of the two endpoint derivative brackets, `dMatanD` on a
    positive endpoint and `dMatanDNeg` on a negative one (K3/K4).  The
    interval formula `dMatanD A Mv` is **never** used across a zero crossing;
  * no `matan` domain gate remains: the new gates are exactly the endpoint-arm
    tests plus the hull's `-1 < lo` / sign facts.

The generic `matanHull` jet is emitted locally per box; the `C¹` fact for
`matan` on `(-1, ∞)` (`contDiffAt_matan_gt`, which the landed
`contDiffAt_matan_of_pos` does not cover for `t ≤ 0`) comes from the landed
`Kepler.Text.TaylorSecond.MatanC1` (`f60a76f7`) — nothing is re-proved here.

**Gate registry (unchanged discipline).**  Every `by decide` site is appended
to `GATES` at emission time with (a) an anchor that must occur next to the
token in the *emitted text* and (b) a pure-Python predicate over the replica
literals.  `anchored_gates()` locates every `decide` token in the final text
(block comments stripped), pairs them in order with the registry, and refuses
to return on a count mismatch — the preflight really enumerates the gates of
the emitted file, and it uses the very same `render()` plan object the
emitter used (`M8a`'s ERRATA: a replica that is not the emission is a fake
PASS).

Usage:
    gen_m9.py --id W1DC_15869_LLLLLLL_zero_0 [--occ 0] --out /tmp/x.lean
    gen_m9.py --index 17 --out /tmp/x.lean          # 0-based manifest index
    gen_m9.py --id ... --print-gates                # preflight-side use

No `axiom` / `sorry` / `admit` / `native_decide` is ever emitted.
"""
import json
import math
import os
import re
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(500000)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import dcrep as R
import node_table as T

VERSION = 'gen_m9.py v1 (2026-11-25, lane wt1-m9-emission-w1)'
K = 200
K2 = 201
BOXES_DEFAULT = os.path.join(HERE, 'boxes221.json')

# ------------------------------------------------------------------ manifest
def load_boxes(path=None):
    path = path or os.environ.get('BOXES221', BOXES_DEFAULT)
    with open(path) as fh:
        boxes = json.load(fh)
    for i, r in enumerate(boxes):
        r['_idx'] = i
    return boxes


def node_arg(rec, name):
    """The argument child of a tree node (set by `render` via `T.by_name`)."""
    return T.by_name[name][2]


def box_key(r):
    """Stable human key; ids are NOT unique in the manifest (7 repeats)."""
    return '%s#%d' % (r['id'], r['_idx'])


def find_box(boxes, ident=None, occ=0, index=None):
    if index is not None:
        return boxes[index]
    hits = [r for r in boxes if r['id'] == ident]
    if not hits:
        raise SystemExit('no box with id %r' % ident)
    if occ >= len(hits):
        raise SystemExit('id %r has only %d record(s)' % (ident, len(hits)))
    return hits[occ]


# ------------------------------------------------------------------ grid
def fl(q):
    x = F(q) * (1 << K)
    return x.numerator // x.denominator


def ce(q):
    x = F(q) * (1 << K)
    return -((-x.numerator) // x.denominator)


def ri(n):
    return '(%d : \u2124)' % n


def dcl(t):
    return '\u27e8(%d : \u2124), (%d : \u2124), (%d : \u2124)\u27e9' % t


def dedupe(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


def box_data(rec):
    lo = [fl(rec['ylo'][i]) for i in range(3)]
    hi = [ce(rec['yhi'][i]) for i in range(3)]
    for i in range(3):
        assert lo[i] <= hi[i], (rec['id'], i, lo[i], hi[i])
    return [(lo[i], hi[i]) for i in range(3)]


# ------------------------------------------------------------------ node tables
def nodes_for(mode):
    """The node list of the tree; `zero` is M7's, `one` adds the Lf4·DihC fan."""
    if mode == 'zero':
        return list(T.ALL)
    if mode != 'one':
        raise SystemExit('unknown mode %r' % mode)
    top = []
    for n in T.TOP:
        if n[0] == 'PosA':
            # replaced by the three-term fan below
            top.append(('Lf4DihC', 'mul', 'Lf4', 'DihC'))
            top.append(('Lf5DihA', 'mul', 'Lf5', 'DihA'))
            top.append(('Lf6DihB', 'mul', 'Lf6', 'DihB'))
            top.append(('POSa', 'add', 'Lf4DihC', 'Lf5DihA'))
            top.append(('POS', 'add', 'POSa', 'Lf6DihB'))
            continue
        if n[0] == 'Lf5DihA' or n[0] == 'Lf6DihB':
            continue
        if n[0] == 'Pos':
            top.append(('Pos', 'mul', 'K2', 'POS'))
            continue
        top.append(n)
    return list(T.LEAVES) + list(T.DLT) + list(T.BR_A) + list(T.BR_B) + \
        list(T.BR_C) + list(T.MID) + list(T.MATAN) + top


def dlt_corner(box):
    (lo4, hi4), (lo5, hi5), (lo6, hi6) = box

    def dlt_int(m4, m5, m6):
        X4, X5, X6 = m4 * m4, m5 * m5, m6 * m6
        quad = (-2 * (X4 * X4 + X5 * X5 + X6 * X6)
                + 4 * (X4 * X5 + X4 * X6 + X5 * X6))
        return (quad << 400) - X4 * X5 * X6

    nlo = dlt_int(lo4, lo5, lo6)
    nhi = dlt_int(hi4, hi5, hi6)
    _lof = F(nhi, 2 ** 1200) * 2 ** 200
    lo200 = _lof.numerator // _lof.denominator
    _hif = F(nlo, 2 ** 1200) * 2 ** 200
    hi200 = -((-_hif.numerator) // _hif.denominator)
    return (nlo, nhi, lo200, hi200)


# ------------------------------------------------------------------ f bodies
def fbody(n):
    name, kind, a, b = n
    if kind == 'coord':
        return 'fun x => x %d' % a
    if kind == 'constI':
        if a < 0:
            # `((n : ℤ) : ℝ)` with `n < 0` is not `rfl`-equal to `(n : ℝ)`
            # (`Int.cast` on a negative literal does not reduce), and the
            # `fTop = w1F3Z` bridge would fail on this one leaf.
            return 'fun _ => (%d : \u211d)' % a
        return 'fun x => ((%d : \u2124) : \u211d)' % a
    if kind == 'constDC':
        return 'fun _ => %s' % a
    if kind == 'constQ':
        return 'fun _ => (%d / %d : \u211d)' % a
    if kind == 'mul':
        return 'fun x => f%s x * f%s x' % (a, b)
    if kind == 'add':
        return 'fun x => f%s x + f%s x' % (a, b)
    if kind == 'sub':
        return 'fun x => f%s x - f%s x' % (a, b)
    if kind == 'inv':
        return 'fun x => (f%s x)\u207b\u00b9' % a
    if kind == 'matan':
        return 'fun x => matan (f%s x)' % a
    raise ValueError(n)


# ------------------------------------------------------------------ literals
def leaf_lits(box, pfx):
    v = {}
    if pfx == 'I':
        v['Y4'] = (200, box[0][0], box[0][1])
        v['Y5'] = (200, box[1][0], box[1][1])
        v['Y6'] = (200, box[2][0], box[2][1])
    else:
        v['Y4'] = (201, box[0][0] + box[0][1], box[0][0] + box[0][1])
        v['Y5'] = (201, box[1][0] + box[1][1], box[1][0] + box[1][1])
        v['Y6'] = (201, box[2][0] + box[2][1], box[2][0] + box[2][1])
    v['SI'] = (60, 1630477228166597776, 1630477228166597777)
    v['PI'] = R.PIbr
    v['MM1'] = (200, fl(F(10120808, 10 ** 7)), ce(F(10120809, 10 ** 7)))
    v['MM2'] = (200, fl(F(2541450, 10 ** 8)), ce(F(2541451, 10 ** 8)))
    for nm, q in (('C2', 2), ('C4', 4), ('C8', 8), ('CN2', -2)):
        v[nm] = R.dInt(q)
    for nm, (num, den) in (('CH', (1, 2)), ('CH0', (63, 50)), ('CH0i', (50, 13)),
                           ('C008', (1, 125)), ('C112', (1, 12))):
        v[nm] = R.dDiv(R.dInt(num), R.dInt(den))
    return v


CONST_NAMES = ['SI', 'PI', 'MM1', 'MM2', 'C2', 'C4', 'C8', 'CN2', 'CH', 'CH0', 'CH0i',
               'C008', 'C112']


def dc_width(A):
    """Interval width as an exact rational (`hi/2^k - lo/2^k`)."""
    d = F(A[2] - A[1])
    return d / (1 << A[0]) if A[0] >= 0 else d * (1 << (-A[0]))


# ------------------------------------------------- M9: the K1-K4 matan channel
CUT = F(1019, 10000)      # layout9's direct-9 threshold (CUT = 0.1019)
NEG_DIGITS = 40           # DCMatanMono §2 ql/qh rule: D decimal digits


def fl_q(q, k):
    x = F(q) * (1 << k)
    return x.numerator // x.denominator


def ce_q(q, k):
    x = F(q) * (1 << k)
    return -((-x.numerator) // x.denominator)


def rat_of(A):
    """Exact rational value of a `DC` literal (`lo · 2^-k`)."""
    k, lo, hi = A
    return F(lo, 1 << k) if k >= 0 else F(lo << (-k))


def pt_lo(A):
    return (A[0], A[1], A[1])


def pt_hi(A):
    return (A[0], A[2], A[2])


def dRescale(k, B):
    """`DCMatanMono.dRescale`: exact left shift, outward floor/ceil otherwise."""
    if B[0] <= k:
        d = k - B[0]
        return (k, B[1] << d, B[2] << d)
    d = B[0] - k
    return (k, B[1] >> d, -((-B[2]) >> d))


def dMatanMono(A, Mlo, Mhi):
    """K1 value hull `⟨A.k, (rescale Mhi).lo, (rescale Mlo).hi⟩` (reverse pairing)."""
    return (A[0], dRescale(A[0], Mhi)[1], dRescale(A[0], Mlo)[2])


def dMatanDNeg(A, Mv):
    """K3 negative-branch derivative `dNeg (dDiv (dSub (dInv (1+A)) Mv) (-2·A))`."""
    return R.dNeg(R.dDiv(R.dSub(R.dInv(R.dAdd(R.ONE, A)), Mv), R.dMul(R.dInt(-2), A)))


def dMatanDHull(A, Glo, Ghi):
    """K4 gradient hull `⟨A.k, (rescale Glo).lo, (rescale Ghi).hi⟩` (forward)."""
    return (A[0], dRescale(A[0], Glo)[1], dRescale(A[0], Ghi)[2])


def lkB5r(q):
    return q + q ** 3 / 3 + q ** 5 / 5 + q ** 7 / 7 + q ** 9 / 9


def sqrt_br_ql_qh(s, D=NEG_DIGITS):
    """`DCMatanMono` §2 rule: `ql = isqrt(floor(s·10^2D))/10^D`,
    `qh = (isqrt(ceil(s·10^2D))+1)/10^D` (exact `ℚ`, no floats)."""
    sc = 10 ** (2 * D)
    num, den = s.numerator, s.denominator
    Nf = (num * sc) // den
    ql = F(math.isqrt(Nf), 10 ** D)
    Nc = -((-num * sc) // den)
    qh = F(math.isqrt(Nc) + 1, 10 ** D)
    return ql, qh


def neg_value_bracket(t):
    """`lkB_matan_neg_pt`'s exact-rational bracket at `-1 < t < 0`."""
    s = -t
    ql, qh = sqrt_br_ql_qh(s)
    assert 0 < ql <= qh < 1, ('qh range', t, ql, qh)
    assert ql * ql <= s <= qh * qh, ('isqrt bracket', t, ql, qh, s)
    vlo = lkB5r(ql) / ql
    vhi = (lkB5r(qh) + qh * (qh ** 10 / (1 - qh ** 2))) / qh
    return ql, qh, vlo, vhi


def dc_of_qrange(vlo, vhi, k=200):
    """Outward `DC` literal at scale `k`, padded one grid unit on each side."""
    return (k, ce_q(vlo, k) - 1, fl_q(vhi, k) + 1)


def endpoint_plan(t):
    """Endpoint bracket plan for the exact rational `t > -1`.

    Positive: the landed four-arm point evaluation, branch table = `layout9`'s
    `point_bracket` (`direct9` / `mirror` / `wplus` / `u9`; the mirror inner is
    `dMatanTightW`).  Negative: `lkB_matan_neg_pt` (exact `ℚ`, `isqrt` ql/qh).
    Zero: `matan 0 = 1`.
    """
    if t > 0:
        if t <= CUT:
            arm = 'd9'
        elif t < 1:
            arm = 'mir'
        elif t <= 4:
            arm = 'wp'
        else:
            arm = 'u9'
        return dict(kind='pos', arm=arm, t=t)
    if t == 0:
        return dict(kind='zero', arm='one', t=t)
    assert t > -1, ('matan pole, no finite bracket', t)
    ql, qh, vlo, vhi = neg_value_bracket(t)
    return dict(kind='neg', arm='lkB', ql=ql, qh=qh, vlo=vlo, vhi=vhi, t=t)


def endpoint_lit(pl, pt):
    """The `DC` literal of an endpoint value bracket (`pt` = `ptLo`/`ptHi` literal)."""
    if pl['kind'] == 'neg':
        return dc_of_qrange(pl['vlo'], pl['vhi'])
    if pl['kind'] == 'zero':
        return (0, 1, 1)
    arm = pl['arm']
    if arm == 'd9':
        return R.dMatan9(pt)
    if arm == 'wp':
        return R.dMatanWp(pt)
    if arm == 'u9':
        return R.dMatanU9(pt)
    if arm == 'mir':
        return R.dMatanMir(pt, R.dMatanTightW(pt))
    raise ValueError(arm)


def matan_plan9(A):
    """The M9 per-node plan: endpoint brackets (K1/K2) + monotone hulls (K1/K4)."""
    aLo, aHi = rat_of(pt_lo(A)), rat_of(pt_hi(A))
    plo, phi = endpoint_plan(aLo), endpoint_plan(aHi)
    MvLo = endpoint_lit(plo, pt_lo(A))
    MvHi = endpoint_lit(phi, pt_hi(A))
    if aLo > 0:
        arm = 'pos'
    elif aHi < 0:
        arm = 'neg'
    else:
        assert A[1] < 0 < A[2], ('zero endpoint (absent from the 221 set)', A)
        arm = 'cross'
    Glo = dMatanDNeg(pt_lo(A), MvLo) if arm in ('neg', 'cross') else R.dMatanD(pt_lo(A), MvLo)
    Ghi = R.dMatanD(pt_hi(A), MvHi) if arm in ('pos', 'cross') else dMatanDNeg(pt_hi(A), MvHi)
    H = dMatanDHull(A, Glo, Ghi)
    V = dMatanMono(A, MvLo, MvHi)
    return dict(alo=aLo, ahi=aHi, lo=plo, hi=phi, MvLo=MvLo, MvHi=MvHi,
                V=V, arm=arm, Glo=Glo, Ghi=Ghi, H=H, A=A)


def compute(nodes, base, dlt_lit=None):
    v = dict(base)
    p = {nm: [R.dInt(0)] * 3 for nm in base}
    plans = {}
    for n in nodes:
        name, kind, a, b = n
        if kind == 'coord':
            p[name] = [R.dInt(1 if j == a else 0) for j in range(3)]
            continue
        if kind in ('constI', 'constDC', 'constQ'):
            p[name] = [R.dInt(0)] * 3
            continue
        if name == 'Dlt' and dlt_lit is not None:
            v[name] = dlt_lit
            p[name] = [R.dAdd(p[a][i], R.dNeg(p[b][i])) for i in range(3)]
            continue
        if kind == 'mul':
            v[name] = R.dMul(v[a], v[b])
            p[name] = [R.dAdd(R.dMul(v[a], p[b][i]), R.dMul(v[b], p[a][i])) for i in range(3)]
            continue
        if kind == 'add':
            v[name] = R.dAdd(v[a], v[b])
            p[name] = [R.dAdd(p[a][i], p[b][i]) for i in range(3)]
            continue
        if kind == 'sub':
            v[name] = R.dSub(v[a], v[b])
            p[name] = [R.dAdd(p[a][i], R.dNeg(p[b][i])) for i in range(3)]
            continue
        if kind == 'inv':
            v[name] = R.dInv(v[a])
            p[name] = [R.dNeg(R.dMul(R.dMul(v[name], v[name]), p[a][i])) for i in range(3)]
            continue
        if kind == 'matan':
            pl = matan_plan9(v[a])
            plans[name] = pl
            v[name] = pl['V']
            p[name] = [R.dMul(pl['H'], p[a][i]) for i in range(3)]
            continue
        raise ValueError(n)
    if dlt_lit is not None:
        v['Dlt'] = dlt_lit
    return v, p, plans


# ------------------------------------------------------------------ gates
GATES = []


def g_add(kind, anchor, prop, fn, desc=''):
    GATES.append(dict(kind=kind, anchor=anchor, prop=prop, fn=fn, desc=desc,
                      line=None, anchor_ok=None, ok=None, msg=''))


def strip_block_comments(text):
    """Blank out /- ... -/ spans, preserving line structure."""
    def repl(m):
        return re.sub(r'[^\n]', ' ', m.group(0))
    return re.sub(r'/-.*?-/', repl, text, flags=re.S)


def anchored_gates(text):
    """Pair every `decide` token of the emitted text with a registry entry."""
    clean = strip_block_comments(text)
    lines = clean.split('\n')
    pos = []
    for ln, line in enumerate(lines, 1):
        for m in re.finditer(r'\bdecide\b', line):
            pos.append((ln, m.start()))
    if len(pos) != len(GATES):
        raise SystemExit('decide tokens %d != gate registry %d\n%s'
                         % (len(pos), len(GATES),
                            '\n'.join('%d: %s' % (l + 1, lines[l][:120])
                                      for l in sorted({p[0] for p in pos}))))
    for gate, (ln, _) in zip(GATES, pos):
        gate['line'] = ln
        win = '\n'.join(lines[max(0, ln - 18):ln])
        gate['anchor_ok'] = (gate['anchor'] in win) or (gate['prop'] in win)
    return GATES


def run_gates():
    """Evaluate every gate; returns (n_ok, failures)."""
    bad = []
    for gate in GATES:
        try:
            ok, msg = gate['fn']()
        except Exception as exc:                      # replica blow-up = failure
            ok, msg = False, 'exception: %r' % (exc,)
        gate['ok'] = ok
        gate['msg'] = msg
        if not ok:
            bad.append(gate)
    return len(GATES) - len(bad), bad


# ------------------------------------------------------------------ header
def emit_header(out, rec):
    box = box_data(rec)
    nodes = nodes_for(rec['mode'])
    out.append(f'''/-
Kepler.Text.TaylorSecond.{rec['id']} — lane `wt1-m9-emission-w1` (2026-11-25).

**DC-only tree certificate** of the D1 certificate box `{box_key(rec)}`
(case {rec['case']}, path {rec['path']}, mode `{rec['mode']}`, nleaves {rec['nleaves']}):
the full {len(nodes)}-node tree of `w1F3Z` emitted as `DCJet` chains via
`Kepler.Text.TaylorSecond.DCJet`, in two passes

  * box pass  `Box.J…`  : `JetMem J… f… D`   on `D = {{x | I4.mem (x 0) ∧ …}}`,
  * point pass `Pt.J…`  : `JetMem J… f… Dpt` on the degenerate `Dpt = {{x | x = c}}`,

and the T2 terminal `dcT2_pos` with `V := Pt.JTop.value`, `G i := Box.JTop.part i`.

The box coordinates are the manifest `ylo/yhi` of `boxes221.json`, floored/ceiled
once onto the `2^-200` grid — no term table is consulted here.

**`mode = one`** carries the extra fan term `Lf4 · DihC`:
`fPos = fK2 * (fLf4DihC + fLf5DihA + fLf6DihB)`, i.e. definitionally
`fK2 x * ((fLf4 x * fDihC x + fLf5 x * fDihA x) + fLf6 x * fDihB x)`.
`mode = zero` is the M7 tree (`fPos = fK2 * (fLf5DihA + fLf6DihB)`).

**`dSqrt` repair (M7).**  `Nat.sqrt` does not reduce in the kernel, so no
`decide`/`rfl` may ever see a `dSqrt` node.  Every square root is emitted as a
literal proved through `DCSqrtLit.dSqrt_val` (two `Nat` bracketing facts), and
every node gets a literal equality proved one op at a time
(`dMul ⟨…⟩ ⟨…⟩ = ⟨…⟩` by `rfl`), so the kernel evaluates at most one `DC` op
per node.  The gates are `by rw [ev_…]; decide` on literals.

**M9 `matan` channel.**  The M8 whole-box arm evaluation is replaced by the
landed `DCMatanMono` + `M8Kit` kit: the value is the endpoint-monotone hull
`dMatanMono` (K1) of the two endpoint point brackets — the landed four-arm
evaluation on a positive endpoint (`dMatan9`/`dMatanWp`/`dMatanU9`/
`dMatanTightW`+`dMatanMir`, branch table = `layout9`'s `point_bracket`), the
exact-rational `lkB_matan_neg_pt` artanh bracket (K2) on a negative endpoint,
`matan 0 = 1` on a zero endpoint — and the partial is the monotone endpoint
hull `dMatanDHullPos/Neg/Cross` (K3/K4) of `dMatanD` / `dMatanDNeg`.  No
`matan` domain gate (`dLoBig` on the argument) remains: the emitted gates are
exactly the endpoint-arm tests and the hull's `-1 < lo` / sign facts.

**Corner rule (M8).**  The `Dlt` value channel uses the corner bracket at base
`y4 ≥ 2.4618` (`DltCornerWide.delta_mono_y4_wide`, `96ddb1d0`), with the y5/y6
directions re-proved in-module on the same base; the naive DC interval of the
`Dlt` subtree straddles zero and makes every `matan` gate false.

The slack is decided on ℤ and cast to ℝ (`dcSlack`).

Generated by `{VERSION}`.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.TaylorSecond.LeafKit
import Kepler.Text.TaylorSecond.DCSqrtLit
import Kepler.Text.TaylorSecond.DltCornerWide
import Kepler.Text.TaylorSecond.DCMatanMono
import Kepler.Text.TaylorSecond.MatanC1
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks21

set_option maxHeartbeats 32000000
set_option maxRecDepth 2000000
set_option exponentiation.threshold 2048
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace {rec['id']}

open DCKit
open DCJetKit
open DCMatan
open DCMatanMono
open M8Kit
open MatanC1
open DCSqrtLit
open Kepler.Text
open Filter
open scoped Topology ContDiff

noncomputable section

/-! ## 0. The box, centre, half-width, and the two domains -/

def I4 : DC := \u27e8(200 : \u2124), {ri(box[0][0])}, {ri(box[0][1])}\u27e9
def I5 : DC := \u27e8(200 : \u2124), {ri(box[1][0])}, {ri(box[1][1])}\u27e9
def I6 : DC := \u27e8(200 : \u2124), {ri(box[2][0])}, {ri(box[2][1])}\u27e9

/-- The box. -/
def D : Set (Fin 3 \u2192 \u211d) :=
  {{x | I4.mem (x 0) \u2227 I5.mem (x 1) \u2227 I6.mem (x 2)}}

def s : \u211d := (2 : \u211d) ^ (-(200 : \u2124))
def s2 : \u211d := (2 : \u211d) ^ (-(201 : \u2124))

def c0 : \u211d := ((({ri(box[0][0])}) : \u211d) + (({ri(box[0][1])}) : \u211d)) * s2
def c1 : \u211d := ((({ri(box[1][0])}) : \u211d) + (({ri(box[1][1])}) : \u211d)) * s2
def c2 : \u211d := ((({ri(box[2][0])}) : \u211d) + (({ri(box[2][1])}) : \u211d)) * s2

def w0 : \u211d := ((({ri(box[0][1])}) : \u211d) - (({ri(box[0][0])}) : \u211d)) * s2
def w1 : \u211d := ((({ri(box[1][1])}) : \u211d) - (({ri(box[1][0])}) : \u211d)) * s2
def w2 : \u211d := ((({ri(box[2][1])}) : \u211d) - (({ri(box[2][0])}) : \u211d)) * s2

/-- The box widths, in grid units of `2^-200`. -/
def wz0 : \u2124 := ({ri(box[0][1])}) - ({ri(box[0][0])})
def wz1 : \u2124 := ({ri(box[1][1])}) - ({ri(box[1][0])})
def wz2 : \u2124 := ({ri(box[2][1])}) - ({ri(box[2][0])})

def c : Fin 3 \u2192 \u211d
  | 0 => c0
  | 1 => c1
  | 2 => c2

def w : Fin 3 \u2192 \u211d
  | 0 => w0
  | 1 => w1
  | 2 => w2

/-- The degenerate centre box. -/
def Dpt : Set (Fin 3 \u2192 \u211d) := {{x | x = c}}
''')
    # c_mem's three literal `by decide` gates
    for i in range(3):
        lo, hi = box[i]
        anchor = 'by decide : %s \u2264 %s' % (ri(lo), ri(hi))

        def mk(lo=lo, hi=hi):
            return lambda: (lo <= hi, 'lo=%d hi=%d' % (lo, hi))
        g_add('c_mem', anchor, anchor, mk(), 'axis %d endpoint order' % i)
    out.append(f'''
theorem s_pos : 0 < s := zpow_pos (by norm_num) _
theorem s2_pos : 0 < s2 := zpow_pos (by norm_num) _
theorem s_eq : s = 2 * s2 := by norm_num [s, s2]

theorem c_mem : c \u2208 D := by
  have h4 : ({ri(box[0][0])} : \u211d) \u2264 ({ri(box[0][1])} : \u211d) := by
    exact_mod_cast (by decide : {ri(box[0][0])} \u2264 {ri(box[0][1])})
  have h5 : ({ri(box[1][0])} : \u211d) \u2264 ({ri(box[1][1])} : \u211d) := by
    exact_mod_cast (by decide : {ri(box[1][0])} \u2264 {ri(box[1][1])})
  have h6 : ({ri(box[2][0])} : \u211d) \u2264 ({ri(box[2][1])} : \u211d) := by
    exact_mod_cast (by decide : {ri(box[2][0])} \u2264 {ri(box[2][1])})
  have h4s : ({ri(box[0][0])} : \u211d) * s \u2264 ({ri(box[0][1])} : \u211d) * s :=
    mul_le_mul_of_nonneg_right h4 s_pos.le
  have h5s : ({ri(box[1][0])} : \u211d) * s \u2264 ({ri(box[1][1])} : \u211d) * s :=
    mul_le_mul_of_nonneg_right h5 s_pos.le
  have h6s : ({ri(box[2][0])} : \u211d) * s \u2264 ({ri(box[2][1])} : \u211d) * s :=
    mul_le_mul_of_nonneg_right h6 s_pos.le
  refine \u27e8?_, ?_, ?_\u27e9
  \u00b7 change ({ri(box[0][0])} : \u211d) * s \u2264 c0 \u2227 c0 \u2264 ({ri(box[0][1])} : \u211d) * s
    simp only [c0]; rw [s_eq] at *; constructor <;> linarith
  \u00b7 change ({ri(box[1][0])} : \u211d) * s \u2264 c1 \u2227 c1 \u2264 ({ri(box[1][1])} : \u211d) * s
    simp only [c1]; rw [s_eq] at *; constructor <;> linarith
  \u00b7 change ({ri(box[2][0])} : \u211d) * s \u2264 c2 \u2227 c2 \u2264 ({ri(box[2][1])} : \u211d) * s
    simp only [c2]; rw [s_eq] at *; constructor <;> linarith

theorem seg_mem : \u2200 x \u2208 D, \u2200 t \u2208 Set.Icc (0 : \u211d) 1,
    (fun i => c i + t * (x i - c i)) \u2208 D := by
  intro x hx t ht
  obtain \u27e8ht0, ht1\u27e9 := ht
  have hc := c_mem
  have hx1 : ({ri(box[0][0])} : \u211d) * s \u2264 x 0 := hx.1.1
  have hx2 : x 0 \u2264 ({ri(box[0][1])} : \u211d) * s := hx.1.2
  have hx3 : ({ri(box[1][0])} : \u211d) * s \u2264 x 1 := hx.2.1.1
  have hx4 : x 1 \u2264 ({ri(box[1][1])} : \u211d) * s := hx.2.1.2
  have hx5 : ({ri(box[2][0])} : \u211d) * s \u2264 x 2 := hx.2.2.1
  have hx6 : x 2 \u2264 ({ri(box[2][1])} : \u211d) * s := hx.2.2.2
  have hc1 : ({ri(box[0][0])} : \u211d) * s \u2264 c0 := hc.1.1
  have hc2 : c0 \u2264 ({ri(box[0][1])} : \u211d) * s := hc.1.2
  have hc3 : ({ri(box[1][0])} : \u211d) * s \u2264 c1 := hc.2.1.1
  have hc4 : c1 \u2264 ({ri(box[1][1])} : \u211d) * s := hc.2.1.2
  have hc5 : ({ri(box[2][0])} : \u211d) * s \u2264 c2 := hc.2.2.1
  have hc6 : c2 \u2264 ({ri(box[2][1])} : \u211d) * s := hc.2.2.2
  rw [s_eq] at hx1 hx2 hx3 hx4 hx5 hx6 hc1 hc2 hc3 hc4 hc5 hc6
  have ht0' : 0 \u2264 1 - t := by linarith
  refine \u27e8?_, ?_, ?_\u27e9
  \u00b7 change ({ri(box[0][0])} : \u211d) * s \u2264 c0 + t * (x 0 - c0) \u2227
      c0 + t * (x 0 - c0) \u2264 ({ri(box[0][1])} : \u211d) * s
    rw [s_eq]
    constructor
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc1 ht0', mul_le_mul_of_nonneg_left hx1 ht0]
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc2 ht0', mul_le_mul_of_nonneg_left hx2 ht0]
  \u00b7 change ({ri(box[1][0])} : \u211d) * s \u2264 c1 + t * (x 1 - c1) \u2227
      c1 + t * (x 1 - c1) \u2264 ({ri(box[1][1])} : \u211d) * s
    rw [s_eq]
    constructor
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc3 ht0', mul_le_mul_of_nonneg_left hx3 ht0]
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc4 ht0', mul_le_mul_of_nonneg_left hx4 ht0]
  \u00b7 change ({ri(box[2][0])} : \u211d) * s \u2264 c2 + t * (x 2 - c2) \u2227
      c2 + t * (x 2 - c2) \u2264 ({ri(box[2][1])} : \u211d) * s
    rw [s_eq]
    constructor
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc5 ht0', mul_le_mul_of_nonneg_left hx5 ht0]
    \u00b7 nlinarith [mul_le_mul_of_nonneg_left hc6 ht0', mul_le_mul_of_nonneg_left hx6 ht0]

theorem w_abs : \u2200 x \u2208 D, \u2200 i, |x i - c i| \u2264 w i := by
  intro x hx i
  have hx1 : ({ri(box[0][0])} : \u211d) * s \u2264 x 0 := hx.1.1
  have hx2 : x 0 \u2264 ({ri(box[0][1])} : \u211d) * s := hx.1.2
  have hx3 : ({ri(box[1][0])} : \u211d) * s \u2264 x 1 := hx.2.1.1
  have hx4 : x 1 \u2264 ({ri(box[1][1])} : \u211d) * s := hx.2.1.2
  have hx5 : ({ri(box[2][0])} : \u211d) * s \u2264 x 2 := hx.2.2.1
  have hx6 : x 2 \u2264 ({ri(box[2][1])} : \u211d) * s := hx.2.2.2
  rw [s_eq] at hx1 hx2 hx3 hx4 hx5 hx6
  fin_cases i
  \u00b7 change |x 0 - c0| \u2264 w0
    rw [abs_le]; constructor
    \u00b7 simp only [c0, w0]; linarith
    \u00b7 simp only [c0, w0]; linarith
  \u00b7 change |x 1 - c1| \u2264 w1
    rw [abs_le]; constructor
    \u00b7 simp only [c1, w1]; linarith
    \u00b7 simp only [c1, w1]; linarith
  \u00b7 change |x 2 - c2| \u2264 w2
    rw [abs_le]; constructor
    \u00b7 simp only [c2, w2]; linarith
    \u00b7 simp only [c2, w2]; linarith
''')
    out.append('''/-- `constDC` — a constant jet with a prescribed `DC` bracket (the `DC`
analogue of `constJet`; `DCJetKit.const` only covers integer constants). -/
def constDC (V : DC) (v : ℝ) : DCJet := ⟨V, fun _ => dInt 0⟩

theorem constDC_mem (V : DC) (v : ℝ) (h : V.mem v) (E : Set (Fin 3 → ℝ)) :
    JetMem (constDC V v) (fun _ : Fin 3 → ℝ => v) E := by
  refine ⟨fun _ _ => contDiffAt_const, fun _ _ => h, fun x _ i => ?_⟩
  have h0 : partial1 i (fun _ : Fin 3 → ℝ => v) x = 0 := by simp [partial1]
  rw [h0]
  simpa [constDC] using dInt_mem 0

/-- `√2` bracket, outward on `2^-60` (from the landed pilot). -/
def SIbr : DC := ⟨(60 : ℤ), (1630477228166597776 : ℤ), (1630477228166597777 : ℤ)⟩

theorem SIbr_mem : SIbr.mem (Real.sqrt 2) := by
  refine ⟨?_, ?_⟩
  · show (((1630477228166597776 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(60 : ℤ)) ≤ Real.sqrt 2
    rw [Real.le_sqrt (by norm_num)] <;> norm_num
  · show Real.sqrt 2 ≤ (((1630477228166597777 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(60 : ℤ))
    rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
''')


def emit_m9_kit(out):
    """Emit the M9 hull jet once per box.  The `C¹` of `matan` on `(-1, ∞)`
    is **not** emitted any more: it is the landed `MatanC1` module."""
    out.append("/-! ## 2b. The M9 matan plumbing\n\n`matan` is `C¹` on `(-1, ∞)`: the landed `MatanC1` (`f60a76f7`, 5 theorems, all\nstandard three) supplies `contDiffAt_matan_gt`, which the `JetMem` chain rule\nneeds at the hull endpoints (they may be negative — the Dlt-crossing boxes).  It\ngeneralises the landed `contDiffAt_matan_of_pos` (`t > 0` only) to the whole\ndomain, including the removable singularity at `0` (`matanD 0 = -1/3`).\nNothing about `matan` is re-proved here. -/\n\n/-! ### 2c. The hull jet (`dMatanMono` value, `dMatanDHull·∂f` partial) -/\n\n/-- The M9 `matan` jet: value from the endpoint-monotone hull `dMatanMono`\n(K1), partial from the monotone derivative hull `dMatanDHull` (K4) — the DC\ncounterpart of `DCJetKit.matanWith`, with no `1/(2r)` interval formula. -/\ndef matanHull (J : DCJet) (MvLo MvHi GHull : DC) : DCJet :=\n  ⟨dMatanMono J.value MvLo MvHi, fun i => dMul GHull (J.part i)⟩\n\ntheorem matanHull_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}\n    {MvLo MvHi GHull : DC} (hJ : JetMem J f D)\n    (hlo1 : dLoGt J.value (dInt (-1)) = true)\n    (hMvLo : MvLo.mem (matan ((J.value.lo : ℝ) * (2:ℝ)^(-(J.value.k:ℤ)))))\n    (hMvHi : MvHi.mem (matan ((J.value.hi : ℝ) * (2:ℝ)^(-(J.value.k:ℤ)))))\n    (hG : ∀ r, J.value.mem r → GHull.mem (deriv matan r)) :\n    JetMem (matanHull J MvLo MvHi GHull) (fun x => matan (f x)) D := by\n  obtain ⟨h1, h2, h3⟩ := hJ\n  have hlo1R : -1 < (J.value.lo : ℝ) * (2:ℝ)^(-(J.value.k:ℤ)) := by\n    simpa [dInt] using dLoGt_sound hlo1\n  have hmat : ∀ x ∈ D, ContDiffAt ℝ 1 matan (f x) := fun x hx =>\n    contDiffAt_matan_gt (lt_of_lt_of_le hlo1R (h2 x hx).1)\n  refine ⟨fun x hx => (hmat x hx).comp x (h1 x hx), fun x hx => ?_, fun x hx i => ?_⟩\n  · exact dMatanMono_mem (h2 x hx) hlo1R hMvLo hMvHi\n  · have hcomp : partial1 i (matan ∘ f) x = deriv matan (f x) * partial1 i f x :=\n      partial1_comp (hmat x hx) (h1 x hx) i\n    have htarget : partial1 i (fun y => matan (f y)) x\n        = deriv matan (f x) * partial1 i f x := by\n      have hfun : (fun y => matan (f y)) = matan ∘ f := rfl\n      rw [hfun, hcomp]\n    rw [htarget]\n    exact dMul_mem (hG (f x) (h2 x hx)) (h3 x hx i)\n\n#print axioms matanHull_mem\n")


def emit_mm_brackets(out):
    for nm, lo_q, hi_q, lem in (
            ('MM1', F(10120808, 10 ** 7), F(10120809, 10 ** 7), 'lk_mm1_mem'),
            ('MM2', F(2541450, 10 ** 8), F(2541451, 10 ** 8), 'lk_mm2_mem')):
        mlo = fl(lo_q)
        mhi = ce(hi_q)
        real = nm.lower()
        declo, dechi = ({'MM1': ('1.0120808', '1.0120809'), 'MM2': ('0.02541450', '0.02541451')})[nm]
        out.append(f'''
/-- `{nm}` bracket, outward on `2^-200` from `{lem}`. -/
def {nm}br : DC := ⟨(200 : \u2124), {ri(mlo)}, {ri(mhi)}⟩

theorem {nm}br_mem : {nm}br.mem {real} := by
  have h := {lem}
  have h1 : (({ri(mlo)}) : \u211d) * (2 : \u211d) ^ (-(200 : \u2124)) \u2264 (({declo} : \u211a) : \u211d) := by
    norm_num
  have h2 : (({dechi} : \u211a) : \u211d) \u2264 (({ri(mhi)}) : \u211d) * (2 : \u211d) ^ (-(200 : \u2124)) := by
    norm_num
  exact \u27e8le_trans h1 h.1, le_trans h.2 h2\u27e9
''')


def emit_fdefs(out, nodes):
    out.append('\n/-! ## 1. The slot functions (mirror of `W1aFJet` §3, op-for-op) -/\n')
    for n in nodes:
        out.append('def f%s : (Fin 3 \u2192 \u211d) \u2192 \u211d := %s' % (n[0], fbody(n)))
    out.append('')


BRIDGE = {}


def emit_bridge(out, mode):
    """The per-box assembly bridge (M8, orchestrator 2026-11-25): the emitted
    `fTop` is *definitionally* the landed tree function — `w1F3Z` for the zero
    mode, `w1F3O` (the `h0cut = 1` branch, `fPos1` keeps `fLf4 * fDihC`) for the
    one mode.  No `simp` set is needed: 24 of the 25 slot bodies are `rfl`-equal
    to `W1aFJet`'s, and the 25th (`fCN2`) is emitted as `fun _ => (-2 : ℝ)`."""
    target = 'w1F3Z' if mode == 'zero' else 'w1F3O'
    name = 'fTop_eq_' + target
    out.append(f'''
/-- **Assembly bridge**: `fTop` is the landed tree function `{target}` by `rfl`. -/
theorem {name} : fTop = {target} := by
  funext x
  rfl
''')
    BRIDGE['name'] = name


def emit_shared_jets(out, litconst, want_part):
    out.append('\n/-! ## 2. The shared constant jets (box- and point-independent) -/\n')
    for n in T.LEAVES:
        name, kind, a, b = n
        if kind == 'coord':
            continue
        if kind == 'constDC':
            out.append('def J%s : DCJet := constDC %sbr (%s)' % (name, name, a))
            out.append('theorem J%s_mem (E : Set (Fin 3 \u2192 \u211d)) : JetMem J%s f%s E :='
                       % (name, name, name))
            out.append('  constDC_mem %sbr _ %sbr_mem E\n' % (name, name))
        elif kind == 'constI':
            if a < 0:
                # `DCJetKit.const` carries `fun x => ((n : ℤ) : ℝ)`, which is not
                # `rfl`-equal to the `fun _ => (n : ℝ)` body the `w1F3Z` bridge
                # needs; the same jet is spelled through the local `constDC`.
                out.append('def J%s : DCJet := constDC (dInt (%d : \u2124)) (%d : \u211d)'
                           % (name, a, a))
                out.append('theorem J%s_mem (E : Set (Fin 3 \u2192 \u211d)) : JetMem J%s f%s E :='
                           % (name, name, name))
                out.append('  constDC_mem (dInt (%d : \u2124)) (%d : \u211d) (by simpa using dInt_mem (%d)) E\n'
                           % (a, a, a))
            else:
                out.append('def J%s : DCJet := DCJetKit.const (%d : \u2124)' % (name, a))
                out.append('theorem J%s_mem (E : Set (Fin 3 \u2192 \u211d)) : JetMem J%s f%s E :='
                           % (name, name, name))
                out.append('  DCJetKit.const_mem (%d : \u2124) E\n' % a)
        elif kind == 'constQ':
            num, den = a
            out.append('def J%s : DCJet := constDC (dDiv (dInt %d) (dInt %d)) (%d / %d : \u211d)'
                       % (name, num, den, num, den))
            out.append('theorem J%s_mem (E : Set (Fin 3 \u2192 \u211d)) : JetMem J%s f%s E :='
                       % (name, name, name))
            out.append('  constDC_mem _ _ (by simpa using dDiv_mem (by decide) '
                       '(dInt_mem %d) (dInt_mem %d)) E\n' % (num, den))
            anchor = ('dDiv_mem (by decide) (dInt_mem %d) (dInt_mem %d)' % (num, den))

            def mkq(den=den):
                return lambda: (den > 0, 'den=%d' % den)
            g_add('constQ_den', anchor, '0 < (%d : \u2124)' % den, mkq(),
                  'constQ %s denominator positivity' % name)
        out.append('theorem ev_%s : (J%s).value = %s := by rfl\n'
                   % (name, name, dcl(litconst[name])))
        if want_part:
            for i in range(3):
                out.append('theorem p%d_%s : (J%s).part %d = \u27e8(0 : \u2124), (0 : \u2124), (0 : \u2124)\u27e9 := by rfl\n'
                           % (i, name, name, i))


def emit_sqrt_lemma(out, nm, litA, kind, tag):
    A = dcl(litA)
    if kind == 'plain':
        S = R.dSqrt(litA)
        tgt = 'dSqrt %s' % A
        name = 'sq_%s' % nm
        arg = A
        clamped = R.dClamp0(litA)
        pfx = 'sq'
    else:
        D = R.dInv(litA)
        S = R.dSqrt(D)
        tgt = 'dSqrt (dInv %s)' % A
        name = 'sqi_%s' % nm
        arg = '(dInv %s)' % A
        clamped = R.dClamp0(D)
        pfx = 'sqi'
    Kk = (clamped[0] + 201) // 2
    d = 2 * Kk - clamped[0]
    nlo = max(clamped[1], 0) << d
    nhi = max(clamped[2], 0) << d
    rlo, rhin = S[1], S[2]
    rhi = rhin - 1
    out.append(f'''/-- literal square root `{tgt}` — `Nat.sqrt` never reaches the kernel. -/
theorem {name} : {tgt} = {dcl(S)} := by
  refine dSqrt_val (A := {arg}) (K := {ri(Kk)})
    (rlo := {ri(rlo)}) (rhi := {ri(rhi)})
    (nlo := {nlo}) (nhi := {nhi}) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  \u00b7 decide
  \u00b7 decide
  \u00b7 decide
  \u00b7 exact nat_sqrt_eq_of_sq (by decide) (by decide)
  \u00b7 exact nat_sqrt_eq_of_sq (by decide) (by decide)
  \u00b7 decide
  \u00b7 decide
''')
    # --- the 9 `decide`s of this theorem, as 9 registry entries -------------
    an = 'theorem %s' % name

    def mkhK(clamped=clamped, Kk=Kk):
        return lambda: ((clamped[0] + 201) // 2 == Kk, 'k=%d K=%d' % (clamped[0], Kk))

    def mkhnlo(clamped=clamped, d=d, nlo=nlo):
        def f():
            v = max(clamped[1] << d, 0)
            return (v == nlo, 'lo<<%d=%d nlo=%d' % (d, v, nlo))
        return f

    def mkhnhi(clamped=clamped, d=d, nhi=nhi):
        def f():
            v = max(clamped[2] << d, 0)
            return (v == nhi, 'hi<<%d=%d nhi=%d' % (d, v, nhi))
        return f

    def mksq(nlo=nlo, r=rlo):
        return lambda: (r * r <= nlo, 'r^2=%d <= nlo=%d' % (r * r, nlo))

    def mksqhi(nlo=nlo, r=rlo):
        return lambda: (nlo < (r + 1) * (r + 1), 'nlo=%d < (r+1)^2=%d' % (nlo, (r + 1) ** 2))

    def mksq2(nhi=nhi, r=rhi):
        return lambda: (r * r <= nhi, 'r^2=%d <= nhi=%d' % (r * r, nhi))

    def mksq2hi(nhi=nhi, r=rhi):
        return lambda: (nhi < (r + 1) * (r + 1), 'nhi=%d < (r+1)^2=%d' % (nhi, (r + 1) ** 2))

    def mklo0(r=rlo):
        return lambda: (r >= 0, 'rlo=%d' % r)

    def mkhi0(r=rhi):
        return lambda: (r >= 0, 'rhi=%d' % r)

    g_add('%s_hK' % pfx, an, '((dClamp0 A).k + 201) / 2 = (%d : \u2124)' % Kk, mkhK(),
          '%s %s output scale' % (tag, name))
    g_add('%s_hnlo' % pfx, an, '(dClamp0 A).lo <<< (2*K - k).toNat = %d' % nlo, mkhnlo(),
          '%s %s shifted lo' % (tag, name))
    g_add('%s_hnhi' % pfx, an, '(dClamp0 A).hi <<< (2*K - k).toNat = %d' % nhi, mkhnhi(),
          '%s %s shifted hi' % (tag, name))
    g_add('%s_hslo1' % pfx, an, 'rlo*rlo <= nlo', mksq(),
          '%s %s sqrt lo square' % (tag, name))
    g_add('%s_hslo2' % pfx, an, 'nlo < (rlo+1)*(rlo+1)', mksqhi(),
          '%s %s sqrt lo strict' % (tag, name))
    g_add('%s_hshi1' % pfx, an, 'rhi*rhi <= nhi', mksq2(),
          '%s %s sqrt hi square' % (tag, name))
    g_add('%s_hshi2' % pfx, an, 'nhi < (rhi+1)*(rhi+1)', mksq2hi(),
          '%s %s sqrt hi strict' % (tag, name))
    g_add('%s_hlo0' % pfx, an, '0 <= rlo', mklo0(),
          '%s %s rlo nonneg' % (tag, name))
    g_add('%s_hhi0' % pfx, an, '0 <= rhi', mkhi0(),
          '%s %s rhi nonneg' % (tag, name))


def qstr(q):
    """Lean `ℚ` literal for the exact rational `q`."""
    if q.denominator == 1:
        return '(%d : \u211a)' % q.numerator
    return '((%d : \u211a) / (%d : \u211a))' % (q.numerator, q.denominator)


def emit_endpoint_mem(out, name, aidx, ep, sfx, p_, pt, Lit, A, memname):
    """The `MvLo`/`MvHi` `mem` fact, stated at `(J.a).value` and proved after
    rewriting the goal to the literal box (the arm theorems are all literal)."""
    side = 'lo' if ep == 'lo' else 'hi'
    memst = ('(%s : DC).mem (matan (((J%s).value.%s : \u211d) * (2:\u211d)^(-((J%s).value.k:\u2124))))'
             % (dcl(Lit), aidx, side, aidx))
    out.append('''theorem %s : %s := by
  rw [show (J%s).value = %s from ev_%s]
''' % (memname, memst, aidx, dcl(A), aidx))
    Alit = dcl(A)
    if p_['kind'] == 'zero':
        out.append('''  have harg : (((%s : DC).%s : \u2124) : \u211d) *
      (2:\u211d)^(-((%s : DC).k : \u2124)) = 0 := by norm_num
  rw [harg, lkB_matan_zero]
  exact dInt_mem 1
''' % (Alit, side, Alit))
        return
    if p_['kind'] == 'neg':
        tstr = qstr(p_['t'])
        ql, qh = qstr(p_['ql']), qstr(p_['qh'])
        out.append('''  have harg : (((%s : DC).%s : \u2124) : \u211d) *
      (2:\u211d)^(-((%s : DC).k : \u2124)) = ((%s : \u211a) : \u211d) := by norm_num
  rw [harg]
  have hV := lkB_matan_neg_pt %s %s %s
    (QInterval.mk (lkB5r %s / %s)
      ((lkB5r %s + %s * ((%s) ^ 10 / (1 - (%s) ^ 2))) / %s))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) rfl
  exact dc_mem_of_qinterval (k := %d) (lo := (%d : \u2124)) (hi := (%d : \u2124))
    (by norm_num [lkB5r]) (by norm_num [lkB5r]) hV
''' % (Alit, side, Alit, tstr, tstr, ql, qh, ql, ql, qh, qh, qh, qh, qh,
       Lit[0], Lit[1], Lit[2]))
        return
    # positive endpoint: the arm gates are literal facts, `exact` bridges them
    g = 'g%s_%s' % (sfx, name)
    arm = p_['arm']
    blk = '''  have hpt : (pt%s %s).mem (((%s : DC).%s : \u211d) *
      (2:\u211d)^(-((%s : DC).k : \u2124))) :=
    pt%s_mem %s
  have hbig : dLoBig (pt%s %s) = true := %s_hbig
''' % (sfx, Alit, Alit, side, Alit, sfx, Alit, sfx, Alit, g)
    tail = '\n  have h := '
    if arm == 'd9':
        blk += tail + 'dMatan9_mem hpt hbig\n'
    elif arm == 'u9':
        blk += tail + 'dMatanU9_mem hpt hbig\n'
    elif arm == 'wp':
        blk += '''  have h1 : dLoGt (pt%s %s) ONE = true := %s_h1
  have hden : dLoBig (dAdd (dSqrt (pt%s %s)) ONE) = true := %s_hden
''' % (sfx, Alit, g, sfx, Alit, g)
        blk += tail + 'dMatanWp_mem hpt hbig h1 hden\n'
    else:
        blk += '''  have hRden : dLoBig (dAdd (dSqrt (dInv (pt%s %s))) ONE) = true := %s_hRden
  have hRbig : dLoBig (dInv (pt%s %s)) = true := %s_hRbig
  have hinner : (dMatanTightW (pt%s %s)).mem (matan (1 / (((%s : DC).%s : \u211d) *
      (2:\u211d)^(-((%s : DC).k : \u2124))))) :=
    dMatanTightW_mem hpt hbig hRden hRbig
''' % (sfx, Alit, g, sfx, Alit, g, sfx, Alit, Alit, side, Alit)
        blk += tail + 'dMatanMir_mem hpt hinner hbig\n'
    out.append(blk + '  rwa [mv%s_%s] at h\n' % (sfx, name))


def emit_endpoint_arm(out, tag, name, aidx, ep, sfx, p_, pt, Lit, A):
    """The arm literal theorem (at `pt{Lo,Hi} {box literal}`) + gates."""
    ptl = dcl(pt)
    Alit = dcl(A)
    nm = '%s_%s' % (sfx, name)
    arm = p_['arm']
    g = 'g%s_%s' % (sfx, name)
    anchor = 'theorem %s_gates' % g
    if arm == 'd9':
        out.append('''theorem mv%s_%s : dMatan9 (pt%s %s) = %s := by
  unfold dMatan9 pt%s
  rfl

theorem %s_gates : dLoBig %s = true := by decide
theorem %s_hbig : dLoBig %s = true := %s_gates
''' % (sfx, name, sfx, Alit, dcl(Lit), sfx, g, ptl, g, ptl, g))

        def mkg(pt=pt):
            b = R.dLoBig(pt)
            return lambda: (b, 'dLoBig=%r' % b)
        g_add('arm_d9', anchor, 'dLoBig %s = true' % ptl, mkg(),
              '%s %s endpoint arm (d9)' % (tag, nm))
        return
    if arm in ('wp', 'u9'):
        emit_sqrt_lemma(out, nm, pt, 'plain', tag)
        fn = 'dMatanWp' if arm == 'wp' else 'dMatanU9'
        out.append('''theorem mv%s_%s : %s (pt%s %s) = %s := by
  unfold %s pt%s dDiv
  rw [sq_%s]
  rfl
''' % (sfx, name, fn, sfx, Alit, dcl(Lit), fn, sfx, nm))
        if arm == 'wp':
            out.append('''theorem %s_gates : (dLoBig %s = true \u2227 dLoGt %s ONE = true \u2227
    dLoBig (dAdd (dSqrt %s) ONE) = true) := by
  rw [sq_%s]
  decide
theorem %s_hbig : dLoBig %s = true := %s_gates.1
theorem %s_h1 : dLoGt %s ONE = true := %s_gates.2.1
theorem %s_hden : dLoBig (dAdd (dSqrt %s) ONE) = true := %s_gates.2.2
''' % (g, ptl, ptl, ptl, nm, g, ptl, g, g, ptl, g, g, ptl, g))
            preds = [R.dLoBig(pt), R.dLoGt(pt, R.ONE), R.dLoBig(R.dAdd(R.dSqrt(pt), R.ONE))]

            def mkg(preds=preds):
                return lambda: (all(preds), 'LoBig=%r LoGt=%r den=%r' % tuple(preds))
            g_add('arm_wp', anchor,
                  '(dLoBig %s = true \u2227 dLoGt %s ONE = true \u2227 '
                  'dLoBig (dAdd (dSqrt %s) ONE) = true)' % ((ptl,) * 3), mkg(),
                  '%s %s endpoint arm (wp)' % (tag, nm))
        else:
            out.append('''theorem %s_gates : dLoBig %s = true := by decide
theorem %s_hbig : dLoBig %s = true := %s_gates
''' % (g, ptl, g, ptl, g))

            def mkg(pt=pt):
                b = R.dLoBig(pt)
                return lambda: (b, 'dLoBig=%r' % b)
            g_add('arm_u9', anchor, 'dLoBig %s = true' % ptl, mkg(),
                  '%s %s endpoint arm (u9)' % (tag, nm))
        return
    # ---- mirror (`dMatanMir` + `dMatanTightW`)
    D = R.dInv(pt)
    emit_sqrt_lemma(out, nm, pt, 'plain', tag)
    emit_sqrt_lemma(out, nm, pt, 'inv', tag)
    outer = R.dLoGt(D, R.ONE)
    inner = R.dHiLt(D, R.dInt(4))
    branches = []
    if outer:
        branches.append('if_pos (by decide)')
        if inner:
            fn, Lit_in, an = 'dMatanWp', R.dMatanWp(D), 'wp'
            branches.append('if_pos (by decide)')
        else:
            fn, Lit_in, an = 'dMatanU9', R.dMatanU9(D), 'u9'
            branches.append('if_neg (by decide)')
    else:
        fn, Lit_in, an = 'dMatanU9', R.dMatanU9(D), 'u9'
        branches.append('if_neg (by decide)')
    MV = R.dMatanMir(pt, Lit_in)
    assert MV == Lit, ('mir literal mismatch', MV, Lit)
    HP = R.dMul(R.HALF, R.PIbr)
    IS = R.dInv(R.dSqrt(pt))
    DS = R.dMul(HP, IS)
    IA = R.dInv(pt)
    DT = R.dMul(Lit_in, IA)
    out.append('''theorem {an}_{nm} : {fn} (dInv {ptl}) = {Lit_in} := by
  unfold {fn} dDiv
  rw [sqi_{nm}]
  rfl

theorem mt{sfx}_{name} : dMatanTightW {ptl} = {Lit_in} := by
  unfold dMatanTightW
  rw [{branches}]
  exact {an}_{nm}

theorem m{sfx}_{name}a : dMul HALF PIbr = {HP} := by rfl
theorem m{sfx}_{name}b : dInv {SQ} = {IS} := by rfl
theorem m{sfx}_{name}c : dMul {HP} {IS} = {DS} := by rfl
theorem m{sfx}_{name}d : dInv {ptl} = {IA} := by rfl
theorem m{sfx}_{name}e : dMul {Lit_in} {IA} = {DT} := by rfl
theorem m{sfx}_{name}f : dSub {DS} {DT} = {MV} := by rfl

theorem mv{sfx}_{name} : dMatanMir (pt{sfx} {Alit}) (dMatanTightW (pt{sfx} {Alit})) = {MV} := by
  unfold dMatanMir pt{sfx} dDiv
  rw [sq_{nm}, mt{sfx}_{name}, m{sfx}_{name}a, m{sfx}_{name}b, m{sfx}_{name}c,
    m{sfx}_{name}d, m{sfx}_{name}e]
  exact m{sfx}_{name}f
'''.format(an=an, nm=nm, fn=fn, ptl=ptl, Lit_in=dcl(Lit_in), sfx=sfx, name=name,
           branches=', '.join(branches), HP=dcl(HP), SQ=dcl(R.dSqrt(pt)), IS=dcl(IS),
           DS=dcl(DS), IA=dcl(IA), DT=dcl(DT), MV=dcl(MV), Alit=Alit))
    an_full = 'theorem %s_%s' % (an, nm)

    def mkarm(truth=outer):
        return lambda: (truth == outer, 'dLoGt (dInv pt) ONE = %r' % (outer,))
    g_add('arm_mir', an_full, 'dLoGt (dInv %s) ONE = %r' % (ptl, outer), mkarm(),
          '%s %s tight-mirror outer test' % (tag, nm))
    if outer:
        def mkarm2(truth=inner):
            return lambda: (truth == inner, 'dHiLt (dInv pt) 4 = %r' % (inner,))
        g_add('arm_mir', an_full, 'dHiLt (dInv %s) (dInt 4) = %r' % (ptl, inner),
              mkarm2(), '%s %s tight-mirror inner test' % (tag, nm))
    out.append('''theorem %s_gates : (dLoBig %s = true \u2227
    dLoBig (dAdd (dSqrt (dInv %s)) ONE) = true \u2227
    dLoBig (dInv %s) = true \u2227 dLoBig (dAdd ONE %s) = true \u2227
    dLoBig (dMul (dInt 2) %s) = true) := by
  rw [sqi_%s]
  decide
theorem %s_hbig : dLoBig %s = true := %s_gates.1
theorem %s_hRden : dLoBig (dAdd (dSqrt (dInv %s)) ONE) = true := %s_gates.2.1
theorem %s_hRbig : dLoBig (dInv %s) = true := %s_gates.2.2.1
theorem %s_hden1 : dLoBig (dAdd ONE %s) = true := %s_gates.2.2.2.1
theorem %s_hden2 : dLoBig (dMul (dInt 2) %s) = true := %s_gates.2.2.2.2
''' % (g, ptl, ptl, ptl, ptl, ptl, nm, g, ptl, g, g, ptl, g, g, ptl, g,
       g, ptl, g, g, ptl, g))
    preds = [R.dLoBig(pt), R.dLoBig(R.dAdd(R.dSqrt(D), R.ONE)), R.dLoBig(D),
             R.dLoBig(R.dAdd(R.ONE, pt)), R.dLoBig(R.dMul(R.dInt(2), pt))]

    def mkg(preds=preds):
        return lambda: (all(preds),
                        'LoBig=%r Rden=%r Rbig=%r den1=%r den2=%r' % tuple(preds))
    g_add('arm_mir', anchor,
          '(dLoBig %s = true \u2227 dLoBig (dAdd (dSqrt (dInv %s)) ONE) = true \u2227 '
          'dLoBig (dInv %s) = true \u2227 dLoBig (dAdd ONE %s) = true '
          '\u2227 dLoBig (dMul (dInt 2) %s) = true)' % ((ptl,) * 5), mkg(),
          '%s %s endpoint arm (mir)' % (tag, nm))


HULL_ARMS = dict(pos='Pos', neg='Neg', cross='Cross')


def emit_matan_node(out, tag, name, aidx, pl, lit, part, want_part, Dexpr):
    """Emit one M9 `matan` node: endpoint brackets (K1/K2), value hull (K1),
    gradient hull (K3/K4), the `matanHull` jet and its part literals."""
    A = lit[aidx]
    fname = 'f%s' % name
    for ep, sfx in (('lo', 'Lo'), ('hi', 'Hi')):
        p_ = pl[ep]
        pt = pt_lo(A) if ep == 'lo' else pt_hi(A)
        Lit = pl['MvLo'] if ep == 'lo' else pl['MvHi']
        if p_['kind'] == 'pos':
            emit_endpoint_arm(out, tag, name, aidx, ep, sfx, p_, pt, Lit, A)
        emit_endpoint_mem(out, name, aidx, ep, sfx, p_, pt, Lit, A,
                          'mv%s_%s_mem' % (sfx, name))
    # ---- value hull (K1)
    out.append('''theorem vh_%s : dMatanMono (J%s).value %s %s = %s := by
  rw [ev_%s]
  unfold dMatanMono dRescale
  rfl
''' % (name, aidx, dcl(pl['MvLo']), dcl(pl['MvHi']), dcl(pl['V']), aidx))

    # ---- gradient hull (K3/K4)
    arm = pl['arm']
    As = HULL_ARMS[arm]
    unfold_list = {'pos': 'dMatanDHullPos dMatanDHull dMatanD',
                   'neg': 'dMatanDHullNeg dMatanDHull dMatanDNeg',
                   'cross': 'dMatanDHullCross dMatanDHull dMatanDNeg dMatanD'}[arm]
    out.append('''theorem gh_%s : dMatanDHull%s (J%s).value %s %s = %s := by
  rw [ev_%s]
  unfold %s dDiv dRescale ptLo ptHi
  rfl
''' % (name, As, aidx, dcl(pl['MvLo']), dcl(pl['MvHi']), dcl(pl['H']), aidx, unfold_list))

    # ---- hull gates
    pLo, pHi = dcl(pt_lo(A)), dcl(pt_hi(A))
    Jv = '(J%s).value' % aidx
    if arm == 'pos':
        fields = [
            ('hlo', '(0 : \u2124) < %s.lo' % Jv, A[1] > 0),
            ('hlo1', 'dLoGt %s (dInt (-1)) = true' % Jv, R.dLoGt(A, R.dInt(-1))),
            ('hbigLo', 'dLoBig %s = true' % pLo, R.dLoBig(pt_lo(A))),
            ('hden1Lo', 'dLoBig (dAdd ONE %s) = true' % pLo,
             R.dLoBig(R.dAdd(R.ONE, pt_lo(A)))),
            ('hden2Lo', 'dLoBig (dMul (dInt 2) %s) = true' % pLo,
             R.dLoBig(R.dMul(R.dInt(2), pt_lo(A)))),
            ('hbigHi', 'dLoBig %s = true' % pHi, R.dLoBig(pt_hi(A))),
            ('hden1Hi', 'dLoBig (dAdd ONE %s) = true' % pHi,
             R.dLoBig(R.dAdd(R.ONE, pt_hi(A)))),
            ('hden2Hi', 'dLoBig (dMul (dInt 2) %s) = true' % pHi,
             R.dLoBig(R.dMul(R.dInt(2), pt_hi(A)))),
        ]
    elif arm == 'neg':
        fields = [
            ('hhi', '%s.hi < 0' % Jv, A[2] < 0),
            ('hlo1', 'dLoGt %s (dInt (-1)) = true' % Jv, R.dLoGt(A, R.dInt(-1))),
            ('hden1Lo', 'dLoBig (dAdd ONE %s) = true' % pLo,
             R.dLoBig(R.dAdd(R.ONE, pt_lo(A)))),
            ('hden2Lo', 'dLoBig (dMul (dInt (-2)) %s) = true' % pLo,
             R.dLoBig(R.dMul(R.dInt(-2), pt_lo(A)))),
            ('hden1Hi', 'dLoBig (dAdd ONE %s) = true' % pHi,
             R.dLoBig(R.dAdd(R.ONE, pt_hi(A)))),
            ('hden2Hi', 'dLoBig (dMul (dInt (-2)) %s) = true' % pHi,
             R.dLoBig(R.dMul(R.dInt(-2), pt_hi(A)))),
        ]
    else:
        fields = [
            ('hlo', '%s.lo < 0' % Jv, A[1] < 0),
            ('hhi', '(0 : \u2124) < %s.hi' % Jv, A[2] > 0),
            ('hlo1', 'dLoGt %s (dInt (-1)) = true' % Jv, R.dLoGt(A, R.dInt(-1))),
            ('hden1Lo', 'dLoBig (dAdd ONE %s) = true' % pLo,
             R.dLoBig(R.dAdd(R.ONE, pt_lo(A)))),
            ('hden2Lo', 'dLoBig (dMul (dInt (-2)) %s) = true' % pLo,
             R.dLoBig(R.dMul(R.dInt(-2), pt_lo(A)))),
            ('hbigHi', 'dLoBig %s = true' % pHi, R.dLoBig(pt_hi(A))),
            ('hden1Hi', 'dLoBig (dAdd ONE %s) = true' % pHi,
             R.dLoBig(R.dAdd(R.ONE, pt_hi(A)))),
            ('hden2Hi', 'dLoBig (dMul (dInt 2) %s) = true' % pHi,
             R.dLoBig(R.dMul(R.dInt(2), pt_hi(A)))),
        ]
    conj = ' \u2227\n     '.join(f[1] for f in fields)
    out.append('''theorem gg_%s_gates :
    (%s) := by
  rw [ev_%s]
  decide
''' % (name, conj, aidx))
    proj = 'gg_%s_gates' % name
    nf = len(fields)
    for i, f in enumerate(fields):
        if i == nf - 1:
            out.append('theorem gg_%s_%s : %s := %s%s\n'
                       % (name, f[0], f[1], proj, '.2' * i))
        else:
            out.append('theorem gg_%s_%s : %s := %s%s.1\n'
                       % (name, f[0], f[1], proj, '.2' * i))

    def mkg(fields=fields):
        return lambda: (all(f[2] for f in fields),
                        '; '.join('%s=%r' % (f[0], f[2]) for f in fields))
    g_add('hull_gates', 'theorem gg_%s_gates' % name, conj, mkg(),
          '%s gg_%s hull gates (%s)' % (tag, name, arm))
    # ---- the jet
    MvLo, MvHi, H, V = pl['MvLo'], pl['MvHi'], pl['H'], pl['V']
    out.append('def J%s : DCJet := matanHull J%s %s %s %s\n'
               % (name, aidx, dcl(MvLo), dcl(MvHi), dcl(H)))
    if arm == 'pos':
        hull_before = 'gg_%s_hlo' % name
        hull_after = ('gg_%s_hbigLo gg_%s_hden1Lo gg_%s_hden2Lo '
                      'gg_%s_hbigHi gg_%s_hden1Hi gg_%s_hden2Hi' % ((name,) * 6))
    elif arm == 'neg':
        hull_before = ('gg_%s_hhi (by simpa [dInt] using dLoGt_sound gg_%s_hlo1)'
                       % (name, name))
        hull_after = ('gg_%s_hden1Lo gg_%s_hden2Lo gg_%s_hden1Hi gg_%s_hden2Hi'
                      % ((name,) * 4))
    else:
        hull_before = ('gg_%s_hlo gg_%s_hhi (by simpa [dInt] using dLoGt_sound gg_%s_hlo1)'
                       % (name, name, name))
        hull_after = ('gg_%s_hden1Lo gg_%s_hden2Lo gg_%s_hbigHi gg_%s_hden1Hi '
                      'gg_%s_hden2Hi' % ((name,) * 5))
    out.append('''theorem J%s_mem : JetMem J%s %s %s :=
  matanHull_mem (J%s_mem) gg_%s_hlo1
    (mvLo_%s_mem) (mvHi_%s_mem)
    (fun r hr => by
      rw [show %s = dMatanDHull%s (J%s).value %s %s from (gh_%s).symm]
      exact dMatanDHull%s_mem hr %s (mvLo_%s_mem) (mvHi_%s_mem) %s)

theorem ev_%s : (J%s).value = %s := by
  show dMatanMono (J%s).value %s %s = %s
  exact vh_%s
''' % (name, name, fname, Dexpr, aidx, name, name, name,
       dcl(H), As, aidx, dcl(MvLo), dcl(MvHi), name, As, hull_before, name, name,
       hull_after, name, name, dcl(V), aidx, dcl(MvLo), dcl(MvHi), dcl(V), name))
    if want_part:
        for i in range(3):
            out.append('''theorem p%d_%s : (J%s).part %d = %s := by
  show dMul %s ((J%s).part %d) = %s
  rw [p%d_%s]
  rfl
''' % (i, name, name, i, dcl(part[name][i]), dcl(H), aidx, i,
       dcl(part[name][i]), i, aidx))


def emit_value_lemma(out, name, kind, a, b, lit, arm=None):
    """Value literal of an op node.  `matan` nodes are emitted wholesale by
    `emit_matan_node` (the M9 hull channel), so this only sees the four ops."""
    if kind in ('mul', 'add', 'sub', 'inv'):
        opname = 'op_%s' % name
        if kind == 'mul':
            out.append(f'theorem {opname} : dMul {dcl(lit[a])} {dcl(lit[b])} = {dcl(lit[name])} := by\n  rfl\n')
            evdef = 'dMul (J%s).value (J%s).value' % (a, b)
            rws = ['ev_%s' % a, 'ev_%s' % b]
        elif kind == 'add':
            out.append(f'theorem {opname} : dAdd {dcl(lit[a])} {dcl(lit[b])} = {dcl(lit[name])} := by\n  rfl\n')
            evdef = 'dAdd (J%s).value (J%s).value' % (a, b)
            rws = ['ev_%s' % a, 'ev_%s' % b]
        elif kind == 'sub':
            out.append(f'theorem {opname} : dAdd {dcl(lit[a])} (dNeg {dcl(lit[b])}) = {dcl(lit[name])} := by\n  rfl\n')
            evdef = 'dAdd (J%s).value (dNeg (J%s).value)' % (a, b)
            rws = ['ev_%s' % a, 'ev_%s' % b]
        else:
            out.append(f'theorem {opname} : dInv {dcl(lit[a])} = {dcl(lit[name])} := by\n  rfl\n')
            evdef = 'dInv (J%s).value' % a
            rws = ['ev_%s' % a]
        tail = 'exact %s' % opname
    else:
        raise ValueError(kind)
    rws = dedupe(rws)
    out.append(f'''theorem ev_{name} : (J{name}).value = {dcl(lit[name])} := by
  rw [show (J{name}).value = {evdef} from rfl, {', '.join(rws)}]
  {tail}
''')


def emit_part_lemmas(out, name, kind, a, b, lit, part, arm=None):
    """Part literals of an op node (`matan` nodes are emitted by `emit_matan_node`)."""
    for i in range(3):
        tgt = dcl(part[name][i])
        if kind == 'mul':
            dfx = ('dAdd (dMul (J%s).value ((J%s).part %d)) (dMul (J%s).value ((J%s).part %d))'
                   % (a, b, i, b, a, i))
            rws = dedupe(['ev_%s' % a, 'ev_%s' % b, 'p%d_%s' % (i, a), 'p%d_%s' % (i, b)])
        elif kind == 'add':
            dfx = 'dAdd ((J%s).part %d) ((J%s).part %d)' % (a, i, b, i)
            rws = dedupe(['p%d_%s' % (i, a), 'p%d_%s' % (i, b)])
        elif kind == 'sub':
            dfx = 'dAdd ((J%s).part %d) (dNeg ((J%s).part %d))' % (a, i, b, i)
            rws = dedupe(['p%d_%s' % (i, a), 'p%d_%s' % (i, b)])
        elif kind == 'inv':
            dfx = ('dNeg (dMul (dMul (dInv (J%s).value) (dInv (J%s).value)) ((J%s).part %d))'
                   % (a, a, a, i))
            rws = dedupe(['ev_%s' % a, 'op_%s' % name, 'p%d_%s' % (i, a)])
        else:
            raise ValueError(kind)
        out.append(f'''theorem p{i}_{name} : (J{name}).part {i} = {tgt} := by
  rw [show (J{name}).part {i} = {dfx} from rfl, {', '.join(rws)}]
  rfl
''')


def emit_pass(out, nodes, tag, Dexpr, coord_dc, coord_mem, top, lit, part, want_part, box,
              plans):
    out.append('\n/-! ## %s -/\n' % ('3. Box pass' if tag == 'B' else '4. Point pass'))
    ns = 'Box' if tag == 'B' else 'Pt'
    out.append('namespace %s\n' % ns)
    for n in nodes:
        name, kind, a, b = n
        plan = plans.get(name)
        if kind == 'coord':
            out.append('def J%s : DCJet := DCJetKit.coord %d %s' % (name, a, coord_dc[a]))
            out.append('theorem J%s_mem : JetMem J%s f%s %s :=' % (name, name, name, Dexpr))
            out.append('  DCJetKit.coord_mem %d %s %s (%s)\n' % (a, coord_dc[a], Dexpr, coord_mem[a]))
            out.append('theorem ev_%s : (J%s).value = %s := by rfl\n' % (name, name, dcl(lit[name])))
            if want_part:
                for i in range(3):
                    c = 'if (%d : Fin 3) = %d then (1 : \u2124) else 0' % (i, a)
                    tac = 'if_pos (by decide)' if i == a else 'if_neg (by decide)'
                    out.append(f'''theorem p{i}_{name} : (J{name}).part {i} = dInt {1 if i == a else 0} := by
  show dInt ({c}) = dInt {1 if i == a else 0}
  rw [{tac}]
''')
                    truth = (i == a)

                    def mki(pos=(i == a), posb=(tac == 'if_pos (by decide)'), i=i, a=a):
                        return lambda: (pos == posb,
                                        'slot %d coord %d (%s)' % (i, a, 'pos' if pos else 'neg'))
                    g_add('idx', 'rw [%s]' % tac, '(%d : Fin 3) = %d' % (i, a), mki(),
                          '%s p%d_%s index' % (tag, i, name))
            continue
        if kind in ('constI', 'constDC', 'constQ'):
            continue
        if tag == 'B' and name == 'Dlt':
            emit_corner_block(out, box)
            emit_corner_jets(out, lit, want_part, part)
            continue

        def mem(ch):
            nm = T.by_name[ch]
            if nm[1] in ('constI', 'constDC', 'constQ'):
                return 'J%s_mem %s' % (ch, Dexpr)
            return 'J%s_mem' % ch

        if kind == 'matan':
            emit_matan_node(out, tag, name, a, plans[name], lit, part, want_part, Dexpr)
            continue
        if kind == 'mul':
            expr = 'DCJetKit.mul J%s J%s' % (a, b)
            proof = 'DCJetKit.mul_mem (%s) (%s)' % (mem(a), mem(b))
        elif kind == 'add':
            expr = 'DCJetKit.add J%s J%s' % (a, b)
            proof = 'DCJetKit.add_mem (%s) (%s)' % (mem(a), mem(b))
        elif kind == 'sub':
            expr = 'DCJetKit.sub J%s J%s' % (a, b)
            proof = 'DCJetKit.sub_mem (%s) (%s)' % (mem(a), mem(b))
        elif kind == 'inv':
            expr = 'DCJetKit.inv J%s' % a
            proof = 'DCJetKit.inv_mem (%s) (by rw [ev_%s]; decide)' % (mem(a), a)
            anchor = '(by rw [ev_%s]; decide)' % a
            va = lit[a]

            def mk(v=va):
                return lambda: (v[1] > 0, 'lo=%d' % v[1])
            g_add('inv_pos', anchor, '0 < (J%s).value.lo' % a, mk(),
                  '%s J%s inverse denominator positivity' % (tag, name))
        else:
            raise ValueError(n)
        out.append('def J%s : DCJet := %s' % (name, expr))
        out.append('theorem J%s_mem : JetMem J%s f%s %s :=' % (name, name, name, Dexpr))
        out.append('  %s\n' % proof)
        emit_value_lemma(out, name, kind, a, b, lit)
        if want_part:
            emit_part_lemmas(out, name, kind, a, b, lit, part)
    out.append('end %s\n' % ns)


def emit_corner_block(out, box):
    (lo4, hi4), (lo5, hi5), (lo6, hi6) = box
    nlo, nhi, lo200, hi200 = dlt_corner(box)

    l4 = '((%s : \u211d) * s)' % ri(box[0][0])
    l5 = '((%s : \u211d) * s)' % ri(box[1][0])
    l6 = '((%s : \u211d) * s)' % ri(box[2][0])
    h4 = '((%s : \u211d) * s)' % ri(box[0][1])
    h5 = '((%s : \u211d) * s)' % ri(box[1][1])
    h6 = '((%s : \u211d) * s)' % ri(box[2][1])

    def dl(a, b, c):
        return 'deltaX (%s * %s) 2 (%s * %s) 2 (%s * %s) 2' % (a, a, b, b, c, c)

    out.append(f"""
/-! ## 3b. The `Dlt` corner rule (box pass) — wide base `y4 ≥ 2.4618`

`fDlt` is nonincreasing in each coordinate on the wt1 box, so its range on `D`
is bracketed by the two opposite corner values.  The 45 bottom certificate
boxes have `l4 = 2.46350884418000923`, **below** the true
`2 * hminus = 2.46350884418060878`, so the landed `nb21_delta_mono_y4/y5/y6`
chain (`2 * hminus ≤ y4`) is unprovable there.  The y4 direction is the landed
`Kepler.Text.TaylorSecond.DltCornerWide.delta_mono_y4_wide` (`96ddb1d0`, base
`2.4618`); the y5/y6 directions are re-proved below on the same base — the
landed proofs only use `y4 ≥ 2.4635` for `x4 ≥ 6.06`, so the factorisation is
verbatim.  The naive DC interval of the `Dlt` subtree straddles zero, which
makes every `matan` gate false; the corner bracket replaces only the *value*
channel, the AD partial channel is unchanged. -/
def xlo : Fin 3 \u2192 \u211d
  | 0 => {l4}
  | 1 => {l5}
  | 2 => {l6}

def xhi : Fin 3 \u2192 \u211d
  | 0 => {h4}
  | 1 => {h5}
  | 2 => {h6}

theorem fDlt_eq_delta (y : Fin 3 \u2192 \u211d) :
    fDlt y = deltaX (y 0 * y 0) 2 (y 1 * y 1) 2 (y 2 * y 2) 2 := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4]
  unfold deltaX
  ring

theorem fDlt_xlo : fDlt xlo = ({nlo} : \u211d) * (2 : \u211d) ^ (-(1200 : \u2124)) := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4, xlo, s]
  norm_num

theorem fDlt_xhi : fDlt xhi = ({nhi} : \u211d) * (2 : \u211d) ^ (-(1200 : \u2124)) := by
  simp only [fDlt, fDltA, fCN2S2, fC4S1, fS2, fS2a, fX4sq, fX5sq, fX6sq,
    fS1, fS1a, fX4X5, fX4X6, fX5X6, fX4X5X6, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4, xhi, s]
  norm_num

/-- `Delta` is nonincreasing in `y5` on the wide base `y4 ≥ 2.4618`
(local copy of `nb21_delta_mono_y5` with the `2 * hminus` hypothesis dropped). -/
theorem delta_mono_y5_wide {{y4 y5 y5' y6 : \u211d}}
    (hy4 : 2.4618 ≤ y4) (hy5 : 2 ≤ y5) (hy5' : 2 ≤ y5') (hy5le : y5' ≤ y5)
    (hy6 : 2 ≤ y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2 := by
  have hx4 : (4 : \u211d) ≤ y4 * y4 := by nlinarith
  have hx5 : (4 : \u211d) ≤ y5 * y5 := by nlinarith
  have hx5' : (4 : \u211d) ≤ y5' * y5' := by nlinarith
  have hx6 : (4 : \u211d) ≤ y6 * y6 := by nlinarith
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2
      = ((y5 * y5) - (y5' * y5')) *
          (16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
            - 2 * ((y5 * y5) + (y5' * y5'))) := by
    rw [Kepler.NliBanks21.nb21_dlt_eq, Kepler.NliBanks21.nb21_dlt_eq]
    ring
  have hd : (0 : \u211d) ≤ (y5 * y5) - (y5' * y5') := by nlinarith
  have hs : 16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
      - 2 * ((y5 * y5) + (y5' * y5')) ≤ 0 := by
    have h1 : (0 : \u211d) ≤ ((y4 * y4) - 4) * ((y6 * y6) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-- `Delta` is nonincreasing in `y6` on the wide base `y4 ≥ 2.4618`. -/
theorem delta_mono_y6_wide {{y4 y5 y6 y6' : \u211d}}
    (hy4 : 2.4618 ≤ y4) (hy6 : 2 ≤ y6) (hy6' : 2 ≤ y6') (hy6le : y6' ≤ y6)
    (hy5 : 2 ≤ y5) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2 := by
  have hx4 : (4 : \u211d) ≤ y4 * y4 := by nlinarith
  have hx5 : (4 : \u211d) ≤ y5 * y5 := by nlinarith
  have hx6 : (4 : \u211d) ≤ y6 * y6 := by nlinarith
  have hx6' : (4 : \u211d) ≤ y6' * y6' := by nlinarith
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2
      = ((y6 * y6) - (y6' * y6')) *
          (16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
            - 2 * ((y6 * y6) + (y6' * y6'))) := by
    rw [Kepler.NliBanks21.nb21_dlt_eq, Kepler.NliBanks21.nb21_dlt_eq]
    ring
  have hd : (0 : \u211d) ≤ (y6 * y6) - (y6' * y6') := by nlinarith
  have hs : 16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
      - 2 * ((y6 * y6) + (y6' * y6')) ≤ 0 := by
    have h1 : (0 : \u211d) ≤ ((y4 * y4) - 4) * ((y5 * y5) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-- The corner bracket of `fDlt` on `D`, on the same `2^-200` grid as the box. -/
def DltCorner : DC := \u27e8(200 : \u2124), ({lo200} : \u2124), ({hi200} : \u2124)\u27e9

theorem fDlt_le_xlo : \u2200 x \u2208 D, fDlt x ≤ fDlt xlo := by
  intro x hx
  obtain \u27e8hx4, hx5, hx6\u27e9 := hx
  have hx4lo : {l4} ≤ x 0 := hx4.1
  have hx5lo : {l5} ≤ x 1 := hx5.1
  have hx6lo : {l6} ≤ x 2 := hx6.1
  have hc4 : (2.4618 : \u211d) ≤ {l4} := by norm_num [s]
  have hc5 : (2 : \u211d) ≤ {l5} := by norm_num [s]
  have hc6 : (2 : \u211d) ≤ {l6} := by norm_num [s]
  have h4x : (2.4618 : \u211d) ≤ x 0 := hc4.trans hx4lo
  have h5x : (2 : \u211d) ≤ x 1 := hc5.trans hx5lo
  have h6x : (2 : \u211d) ≤ x 2 := hc6.trans hx6lo
  calc fDlt x = {dl('x 0', 'x 1', 'x 2')} := fDlt_eq_delta x
    _ ≤ {dl(l4, 'x 1', 'x 2')} :=
        Kepler.Text.TaylorSecond.DltCornerWide.delta_mono_y4_wide
          (y4 := {l4}) (y4' := x 0) hc4 h4x hx4lo h5x h6x
    _ ≤ {dl(l4, l5, 'x 2')} :=
        delta_mono_y5_wide (y4 := {l4}) (y5 := x 1) (y5' := {l5}) hc4 h5x hc5 hx5lo h6x
    _ ≤ {dl(l4, l5, l6)} :=
        delta_mono_y6_wide (y4 := {l4}) (y6 := x 2) (y6' := {l6}) hc4 h6x hc6 hx6lo hc5
    _ = fDlt xlo := (fDlt_eq_delta xlo).symm

theorem fDlt_xhi_le : \u2200 x \u2208 D, fDlt xhi ≤ fDlt x := by
  intro x hx
  obtain \u27e8hx4, hx5, hx6\u27e9 := hx
  have hx4hi : x 0 ≤ {h4} := hx4.2
  have hx5hi : x 1 ≤ {h5} := hx5.2
  have hx6hi : x 2 ≤ {h6} := hx6.2
  have hc4 : (2.4618 : \u211d) ≤ {l4} := by norm_num [s]
  have hc4h : (2.4618 : \u211d) ≤ {h4} := by norm_num [s]
  have hc5 : (2 : \u211d) ≤ {l5} := by norm_num [s]
  have hc5h : (2 : \u211d) ≤ {h5} := by norm_num [s]
  have hc6 : (2 : \u211d) ≤ {l6} := by norm_num [s]
  have hc6h : (2 : \u211d) ≤ {h6} := by norm_num [s]
  have h4x : (2.4618 : \u211d) ≤ x 0 := hc4.trans hx4.1
  have h5x : (2 : \u211d) ≤ x 1 := hc5.trans hx5.1
  have h6x : (2 : \u211d) ≤ x 2 := hc6.trans hx6.1
  calc fDlt xhi = {dl(h4, h5, h6)} := fDlt_eq_delta xhi
    _ ≤ {dl('x 0', h5, h6)} :=
        Kepler.Text.TaylorSecond.DltCornerWide.delta_mono_y4_wide
          (y4 := x 0) (y4' := {h4}) h4x hc4h hx4hi hc5h hc6h
    _ ≤ {dl('x 0', 'x 1', h6)} :=
        delta_mono_y5_wide (y4 := x 0) (y5 := {h5}) (y5' := x 1) h4x hc5h h5x hx5hi hc6h
    _ ≤ {dl('x 0', 'x 1', 'x 2')} :=
        delta_mono_y6_wide (y4 := x 0) (y6 := {h6}) (y6' := x 2) h4x hc6h h6x hx6hi h5x
    _ = fDlt x := (fDlt_eq_delta x).symm

theorem DltCorner_mem : \u2200 x \u2208 D, DltCorner.mem (fDlt x) := by
  intro x hx
  have h1 := fDlt_xhi_le x hx
  have h2 := fDlt_le_xlo x hx
  rw [fDlt_xhi] at h1
  rw [fDlt_xlo] at h2
  have c1 : (({lo200} : \u2124) : \u211d) * (2 : \u211d) ^ (-(200 : \u2124)) ≤
      ({nhi} : \u211d) * (2 : \u211d) ^ (-(1200 : \u2124)) := by norm_num
  have c2 : ({nlo} : \u211d) * (2 : \u211d) ^ (-(1200 : \u2124)) ≤
      (({hi200} : \u2124) : \u211d) * (2 : \u211d) ^ (-(200 : \u2124)) := by norm_num
  exact \u27e8c1.trans h1, h2.trans c2\u27e9
""")


def emit_corner_jets(out, lit, want_part, part):
    out.append('def JDltN : DCJet := DCJetKit.sub JDltA JX4X5X6')
    out.append('theorem JDltN_mem : JetMem JDltN fDlt D :=')
    out.append('  DCJetKit.sub_mem (JDltA_mem) (JX4X5X6_mem)')
    out.append('')
    out.append('def JDlt : DCJet := \u27e8DltCorner, JDltN.part\u27e9')
    out.append('theorem JDlt_mem : JetMem JDlt fDlt D := by')
    out.append('  refine \u27e8JDltN_mem.1, ?_, ?_\u27e9')
    out.append('  \u00b7 simpa [JDlt] using DltCorner_mem')
    out.append('  \u00b7 intro x hx i')
    out.append('    simpa [JDlt] using JDltN_mem.2.2 x hx i')
    out.append('')
    out.append('theorem ev_Dlt : (JDlt).value = %s := by rfl\n' % dcl(lit['Dlt']))
    for i in range(3 if want_part else 0):
        out.append(f'''theorem p{i}_DltN : (JDltN).part {i} =
    dAdd ((JDltA).part {i}) (dNeg ((JX4X5X6).part {i})) := by rfl

theorem p{i}_Dlt : (JDlt).part {i} = {dcl(part['Dlt'][i])} := by
  rw [show (JDlt).part {i} = (JDltN).part {i} from rfl, p{i}_DltN, p{i}_DltA, p{i}_X4X5X6]
  rfl
''')
    out.append('')


def slack_model(box, litV, litG):
    """Python mirror of the emitted `slackZ` (and the real-valued slack)."""
    Vk, Vlo = litV[0], litV[1]
    KZ = 1024
    G = [R.dAbs(g) for g in litG]
    wz = [box[i][1] - box[i][0] for i in range(3)]
    terms = [wz[i] * (G[i][2] << (KZ - 201 - litG[i][0])) for i in range(3)]
    slackZ = (Vlo << (KZ - Vk)) - (terms[0] + terms[1] + terms[2])
    real = F(Vlo) / (2 ** Vk) - sum(F(wz[i] * G[i][2], 2 ** 201 * 2 ** litG[i][0])
                                   for i in range(3))
    return dict(slackZ=slackZ, real=real, KZ=KZ, k_ok=(Vk <= KZ and
                all(litG[i][0] <= KZ - 201 for i in range(3))),
                shifted=[(KZ - Vk)] + [KZ - 201 - litG[i][0] for i in range(3)],
                wz=wz, absGhi=[G[i][2] for i in range(3)])


def emit_terminal(out, top, rec, litV, litG, box):
    sm = slack_model(box, litV, litG)
    bridge_name = 'fTop_eq_' + ('w1F3Z' if rec['mode'] == 'zero' else 'w1F3O')
    out.append(f"""
/-! ## 5. The T2 terminal

`V` and `G` are the **literal** brackets of `Pt.J{top}.value` / `Box.J{top}.part i`
(proved equal to the tree slots in `V_mem`/`G_mem`), so the slack below is one
pure-integer kernel computation: `Nat.sqrt` inside the tree never reaches it. -/

def V : DC := {dcl(litV)}

def G : Fin 3 \u2192 DC
  | 0 => {dcl(litG[0])}
  | 1 => {dcl(litG[1])}
  | 2 => {dcl(litG[2])}

theorem V_mem : V.mem (f{top} c) := by
  have h := Pt.J{top}_mem.2.1 c (show c \u2208 Dpt from rfl)
  rwa [Pt.ev_{top}] at h

theorem G0_eq : G 0 = Box.J{top}.part 0 := by
  rw [show G 0 = {dcl(litG[0])} from rfl]
  exact Box.p0_{top}.symm

theorem G1_eq : G 1 = Box.J{top}.part 1 := by
  rw [show G 1 = {dcl(litG[1])} from rfl]
  exact Box.p1_{top}.symm

theorem G2_eq : G 2 = Box.J{top}.part 2 := by
  rw [show G 2 = {dcl(litG[2])} from rfl]
  exact Box.p2_{top}.symm

theorem G_mem : \u2200 x \u2208 D, \u2200 i, (G i).mem (partial1 i f{top} x) := by
  intro x hx i
  rw [show G i = Box.J{top}.part i from by
    fin_cases i
    \u00b7 exact G0_eq
    \u00b7 exact G1_eq
    \u00b7 exact G2_eq]
  exact Box.J{top}_mem.2.2 x hx i

/-- Scale of the integer slack: far above every `DC.k` in the tree. -/
def KZ : \u2124 := 1024

/-- **The T2 slack, scaled by `2^KZ` and evaluated in `\u2124`.**  A `\u211a`
version is unusable for `decide`: `Rat.blt` does not reduce in the kernel
(measured: even `0 < (1/3 : \u211a)` is stuck), so the sign is decided on the
integer scale `2^KZ` and transported to `\u211d` by `dcSlack` below. -/
def slackZ : \u2124 :=
  V.lo * (2 : \u2124) ^ (KZ - V.k).toNat -
    (wz0 * ((dAbs (G 0)).hi * (2 : \u2124) ^ (KZ - 201 - (G 0).k).toNat) +
     wz1 * ((dAbs (G 1)).hi * (2 : \u2124) ^ (KZ - 201 - (G 1).k).toNat) +
     wz2 * ((dAbs (G 2)).hi * (2 : \u2124) ^ (KZ - 201 - (G 2).k).toNat))

/-- The `k` bounds (needed by the cast bridge) and the slack sign, in **one**
kernel computation on literals. -/
theorem val_facts :
    ((V.k \u2264 KZ \u2227 (G 0).k \u2264 KZ - 201 \u2227 (G 1).k \u2264 KZ - 201 \u2227
        (G 2).k \u2264 KZ - 201) \u2227 0 < slackZ) := by
  decide

theorem dcSlack : 0 < (V.lo : \u211d) * (2 : \u211d) ^ (-(V.k : \u2124)) -
    (w 0 * (((dAbs (G 0)).hi : \u211d) * (2 : \u211d) ^ (-((G 0).k : \u2124))) +
     w 1 * (((dAbs (G 1)).hi : \u211d) * (2 : \u211d) ^ (-((G 1).k : \u2124))) +
     w 2 * (((dAbs (G 2)).hi : \u211d) * (2 : \u211d) ^ (-((G 2).k : \u2124)))) := by
  have hZ : (0 : \u2124) < slackZ := val_facts.2
  have hL : (0 : \u211d) < (slackZ : \u211d) := by exact_mod_cast hZ
  have hk0 : 0 \u2264 KZ - V.k := by linarith [val_facts.1.1]
  have hk1 : 0 \u2264 KZ - 201 - (G 0).k := by linarith [val_facts.1.2.1]
  have hk2 : 0 \u2264 KZ - 201 - (G 1).k := by linarith [val_facts.1.2.2.1]
  have hk3 : 0 \u2264 KZ - 201 - (G 2).k := by linarith [val_facts.1.2.2.2]
  have e0 : (2 : \u211d) ^ (KZ - V.k) = (2 : \u211d) ^ KZ * (2 : \u211d) ^ (-(V.k)) := by
    rw [show KZ - V.k = KZ + (-(V.k)) by ring, zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0)]
  have f0 : (2 : \u211d) ^ (KZ - 201 - (G 0).k) =
      (2 : \u211d) ^ KZ * ((2 : \u211d) ^ (-(201 : \u2124)) * (2 : \u211d) ^ (-((G 0).k))) := by
    rw [show KZ - 201 - (G 0).k = KZ + (-(201 : \u2124) + -((G 0).k)) by ring,
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0),
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0)]
  have f1 : (2 : \u211d) ^ (KZ - 201 - (G 1).k) =
      (2 : \u211d) ^ KZ * ((2 : \u211d) ^ (-(201 : \u2124)) * (2 : \u211d) ^ (-((G 1).k))) := by
    rw [show KZ - 201 - (G 1).k = KZ + (-(201 : \u2124) + -((G 1).k)) by ring,
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0),
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0)]
  have f2 : (2 : \u211d) ^ (KZ - 201 - (G 2).k) =
      (2 : \u211d) ^ KZ * ((2 : \u211d) ^ (-(201 : \u2124)) * (2 : \u211d) ^ (-((G 2).k))) := by
    rw [show KZ - 201 - (G 2).k = KZ + (-(201 : \u2124) + -((G 2).k)) by ring,
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0),
      zpow_add\u2080 (by norm_num : (2 : \u211d) \u2260 0)]
  have he : (slackZ : \u211d) = (2 : \u211d) ^ KZ *
      ((V.lo : \u211d) * (2 : \u211d) ^ (-(V.k : \u2124)) -
        (w 0 * (((dAbs (G 0)).hi : \u211d) * (2 : \u211d) ^ (-((G 0).k : \u2124))) +
         w 1 * (((dAbs (G 1)).hi : \u211d) * (2 : \u211d) ^ (-((G 1).k : \u2124))) +
         w 2 * (((dAbs (G 2)).hi : \u211d) * (2 : \u211d) ^ (-((G 2).k : \u2124))))) := by
    simp only [slackZ, wz0, wz1, wz2, w, w0, w1, w2, s2]
    push_cast
    rw [\u2190 zpow_natCast, \u2190 zpow_natCast, \u2190 zpow_natCast, \u2190 zpow_natCast,
      Int.toNat_of_nonneg hk0, Int.toNat_of_nonneg hk1, Int.toNat_of_nonneg hk2,
      Int.toNat_of_nonneg hk3, e0, f0, f1, f2]
    ring
  rw [he] at hL
  exact pos_of_mul_pos_right hL (zpow_pos (by norm_num) _).le

/-- **The box is positive**: `f{top} > 0` on the box, closed by the DC T2
terminal alone (value bracket at the centre + box-wide gradient brackets). -/
theorem {top}_pos : \u2200 x \u2208 D, 0 < f{top} x :=
  dcT2_pos (f := f{top}) (D := D) (c := c) (w := w)
    c_mem seg_mem Box.J{top}_mem.1 w_abs V G V_mem G_mem dcSlack

#print axioms c_mem
#print axioms seg_mem
#print axioms w_abs
#print axioms val_facts
#print axioms dcSlack
#print axioms {top}_pos
#print axioms {bridge_name}

end

end {rec['id']}
end Kepler.Text.TaylorSecond
""")
    # the single `decide` of val_facts
    def mkfacts(sm=sm):
        def f():
            ok = sm['k_ok'] and sm['slackZ'] > 0
            return (ok, 'k_ok=%r slackZ=%s (%d digits) real=%.6e'
                    % (sm['k_ok'], str(sm['slackZ'])[:20] + '…',
                       len(str(abs(sm['slackZ']))), float(sm['real'])))
        return f
    g_add('val_facts', 'theorem val_facts', 'V.k \u2264 KZ \u2227 \u2026 \u2227 0 < slackZ',
          mkfacts(), 'T2 slack sign and k bounds')


# ------------------------------------------------------------------ render
def render(rec, want_gates=False):
    """Emit the module text (and, with want_gates, the anchored gate list)."""
    global GATES
    GATES = []
    T.by_name = {n[0]: n for n in T.ALL}
    for n in nodes_for(rec['mode']):
        T.by_name[n[0]] = n
    box = box_data(rec)
    nodes = nodes_for(rec['mode'])
    top = 'Top'
    litconst = leaf_lits(box, 'I')
    _, _, lo200, hi200 = dlt_corner(box)
    dlt_lit = (200, lo200, hi200)
    litB, partB, plansB = compute(nodes, leaf_lits(box, 'I'), dlt_lit)
    litP, partP, plansP = compute(nodes, leaf_lits(box, 'P'))
    # NB: the two passes may pick different arms for the same `matan` node —
    # they are independent `JetMem` proofs on different domains, so this is
    # sound (and tighter: the point pass often lands in the `mir`/`wp` band
    # while the box pass needs the universal arm).
    litB['_pDlt'] = partB['Dlt']

    out = []
    emit_header(out, rec)
    emit_mm_brackets(out)
    emit_fdefs(out, nodes)
    emit_bridge(out, rec['mode'])
    emit_shared_jets(out, litconst, True)
    emit_m9_kit(out)
    box_dc = ['I4', 'I5', 'I6']
    box_mem = ['fun x hx => hx.1', 'fun x hx => hx.2.1', 'fun x hx => hx.2.2']
    emit_pass(out, nodes, 'B', 'D', box_dc, box_mem, top, litB, partB, True, box, plansB)
    pt_dc = ['P4', 'P5', 'P6']
    out.append('\n/-! ## 3c. The point coordinate brackets -/\n')
    for i in range(3):
        out.append('def P%d : DC := \u27e8(201 : \u2124), ((%s) + (%s)), ((%s) + (%s))\u27e9'
                   % (i + 4, ri(box[i][0]), ri(box[i][1]), ri(box[i][0]), ri(box[i][1])))
        out.append('theorem P%d_mem : P%d.mem (c %d) := by' % (i + 4, i + 4, i))
        out.append('  have h : c%d = (((%s) : \u211d) + ((%s) : \u211d)) * (2 : \u211d) ^ (-(201 : \u2124)) := by'
                   % (i, ri(box[i][0]), ri(box[i][1])))
        out.append('    simp only [c%d, s2]' % i)
        out.append('  change (((%s) + (%s) : \u2124) : \u211d) * (2 : \u211d) ^ (-(201 : \u2124)) \u2264 c%d \u2227'
                   % (ri(box[i][0]), ri(box[i][1]), i))
        out.append('    c%d \u2264 (((%s) + (%s) : \u2124) : \u211d) * (2 : \u211d) ^ (-(201 : \u2124))'
                   % (i, ri(box[i][0]), ri(box[i][1])))
        out.append('  rw [h]; constructor <;> norm_num\n')
    pt_mem = ['fun x hx => by rw [show x = c from hx]; exact P4_mem',
              'fun x hx => by rw [show x = c from hx]; exact P5_mem',
              'fun x hx => by rw [show x = c from hx]; exact P6_mem']
    emit_pass(out, nodes, 'P', 'Dpt', pt_dc, pt_mem, top, litP, partP, False, box, plansP)
    emit_terminal(out, top, rec, litP[top], partB[top], box)
    text = '\n'.join(out) + '\n'
    anchored_gates(text)
    info = dict(rec=rec, box=box, nodes=nodes, litB=litB, litP=litP,
                partB=partB, partP=partP, plans=plansB,
                slack=slack_model(box, litP[top], partB[top]),
                text=text, gates=list(GATES))
    return info


def main(argv):
    args = argv[1:]
    ident = None
    index = None
    occ = 0
    outp = None
    print_gates = False
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--id':
            ident = args[i + 1]; i += 2
        elif a == '--index':
            index = int(args[i + 1]); i += 2
        elif a == '--occ':
            occ = int(args[i + 1]); i += 2
        elif a == '--out':
            outp = args[i + 1]; i += 2
        elif a == '--print-gates':
            print_gates = True; i += 1
        elif a == '--boxes':
            os.environ['BOXES221'] = args[i + 1]; i += 2
        else:
            raise SystemExit('unknown arg %r' % a)
    boxes = load_boxes()
    rec = find_box(boxes, ident=ident, occ=occ, index=index)
    info = render(rec)
    if print_gates:
        nok, bad = run_gates()
        print('%s: %d gates, %d ok, %d bad' % (box_key(rec), len(GATES), nok, len(bad)))
        for g in bad:
            print('FAIL %-14s L%-5s %s | %s' % (g['kind'], g['line'], g['desc'], g['msg']))
    if outp:
        with open(outp, 'w') as fh:
            fh.write(info['text'])
        print('wrote %s  %d lines  %d nodes  %d gates  mode=%s  box=%s'
              % (outp, info['text'].count('\n'), len(info['nodes']), len(GATES),
                 rec['mode'], box_key(rec)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
