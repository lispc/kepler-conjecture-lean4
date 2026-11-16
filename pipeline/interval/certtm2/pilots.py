"""pilots.py — the three g4port pilot problems (exact Fraction registry).

Port of the prototype `pilot_run.PILOTS`.  Every endpoint is an exact
rational; `2*hminus` uses the in-tree outer box [2.4635, 2.46352]
(`nb17_two_hminus_bounds`), sqrt(8) uses the outer upper endpoint
2.8284272 (its square = 8.0000004... > 8) — outer boxes only make the
claim stronger (positivity on the outer box implies positivity on the
original box).  `affine` is an ordered (index, Fraction) list: the
accumulation order is part of the float-parity contract.
"""

import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import exprs as EX   # noqa: E402  (exact endpoint constants)


def _frac_box(box):
    return [(F(lo), F(hi)) for lo, hi in box]


PILOTS = {
    'p1': dict(
        name='bank_ZTGIJCF4_0_0_0_0',
        box=[(EX.HM_LO, EX.HP)] + [(EX.TWO, EX.HM_HI)] * 5,
        w=1, m=0, sides=['left'] * 6,
        margin_target='+7.7991e-4',
    ),
    'p2': dict(
        name='bank_ZTGIJCF4_0_1_0_0',
        box=[(EX.HM_LO, EX.HP), (EX.TWO, EX.HM_HI), (EX.TWO, EX.HM_HI),
             (EX.HM_LO, EX.S8_HI), (EX.TWO, EX.HM_HI), (EX.TWO, EX.HM_HI)],
        w=2, m=1, sides=['left'] * 6,
        margin_target='+2.6771e-2',
    ),
    'p3': dict(
        name='nliOx3q1h #147',
        box=[(F(253635, 100000), F(25527, 10000)), (EX.TWO, EX.HM_HI),
             (EX.TWO, EX.HM_HI), (EX.TWO, F(205794, 100000)),
             (EX.TWO, EX.HM_HI), (EX.TWO, EX.HM_HI)],
        B=F('-0.090009'),
        affine=[(0, F('-0.013837')), (1, F('-0.073665')), (2, F('-0.073665')),
                (4, F('-0.073665')), (5, F('-0.073665'))],
        const=F('0.755879'), sides=['right'] + ['left'] * 5,
        margin_target='+3.0205e-4',
    ),
}


def normalize(key, box=None, sides=None):
    """Return a pilot dict; overrides for single-leaf mode (exact decimal
    strings are accepted for `box`)."""
    p = PILOTS[key]
    q = dict(p)
    if box is not None:
        q['box'] = _frac_box(box)
    if sides is not None:
        q['sides'] = list(sides)
    return q


def mkexpr(pilot, N):
    """Backend-bound expression closure (ys, sides, ybox) -> Jet."""
    if 'w' in pilot:
        w, m = pilot['w'], pilot['m']
        return lambda ys, sides, yb: EX.main_jet(N, ys, w, m, sides, yb)
    B, aff, cst = pilot['B'], pilot['affine'], pilot['const']
    return lambda ys, sides, yb: EX.margin_jet(N, ys, B, aff, cst, sides, yb)
