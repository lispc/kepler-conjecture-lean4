"""exprs.py — pilot expression builders, generic over the jetlib backends.

Port of the g4port prototype `tmcore.py` (the gamma4/main/margin atom
layer), productionised.  Two consumers share this module verbatim:

  * float navigation (`N.name == "float"`): point jets, fast, ~1e-15,
    operation order kept bit-compatible with the prototype (the B&B must
    reproduce the g4port s-curve leaf counts);
  * certified dyadic intervals (`N.name == "dy"`): box jets over `Dy`
    scalars; every emitted enclosure is machine-checkable.

Certified-only soundness hooks (both strictly tighter, both sound):

  * deltaX corner lift — `deltaX(x)` is separately concave in each x_i
    (leading coefficient -x_pair), hence its minimum over an x-box is
    attained at a vertex; the 64 vertices are exact rationals (squares of
    y-endpoints; the sqrt(8) outer box endpoint has x = 8 exactly), so
    the value lower bound is `max(IA_low, exact_vertex_min)`, memoized
    per x-box (prototype `tmcore.delta_corner_min`).  Without this the
    naive IA lower bound on the wide pilot boxes is far below 0 and every
    sqrt-derivative interval would be unusable;
  * sqrt radicand floor — for R(x) = 4 x1 deltaX(x) with both factors
    positive, R(x) >= 4 x1.lo * deltaX_min pointwise, so the radicand's
    lower end may be raised to that exact floor before `sqrt`
    (prototype `tm_sqrt` floor, dyadic form).

The pilot coefficients (0.0560305, 0.0445813, -0.005, -0.090009, ...) are
carried as exact Fractions and converted per backend: float (correctly
rounded — bit-identical to the prototype's `float("...")`) or minimal
straddling dyadic interval on `coef_grid` (sound enclosure).
"""

import itertools
import math
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import tmexact as X          # noqa: E402
import dyad                  # noqa: E402
import jetlib as J          # noqa: E402

# Exact pilot constants (decimal-exact; the float conversion is correctly
# rounded, hence bit-identical to the prototype's float("...")).
A5 = F("0.0560305")          # aSpine5
NEG_B5 = F("0.0445813")      # -bSpine5 (main uses -bSpine5*dihY; b5 = -0.0445813)
BETA = F("-0.005")           # betaBumpLb
HM_LO = F(246350, 100000)    # 2.4635  <= 2*hminus
HM_HI = F(246352, 100000)    # 2.46352 >= 2*hminus
HP = F(26508, 10000)         # 2.6508
S8_HI = F(28284272, 10000000)  # 2.8284272 > sqrt(8) (its square = 8.0000004...)
TWO = F(2)
KINK = F(252, 100)           # 2.52 = 2*h0


def C(N, fr):
    """Backend-generic exact constant -> float or Dy straddle interval."""
    if N.name == "dy":
        return dyad.Dy.from_frac(fr, N.coef_grid)
    return float(fr)


# ---------------------------------------------------------------- mm12

def mm12(N):
    """sol0/tau0 constants (cached on the backend for the dy branch).
    float branch verbatim (g4core.mm12 / jet2.mm12);
    dyadic branch = the iv branch with exact dyadic integer radicands:
    acos(1/3) = atan2(sqrt(8)/3, 1/3) = atan(sqrt(8))."""
    if N.name == "dy":
        got = getattr(N, "_mm12", None)
        if got is None:
            got = _mm12_dy(N)
            N._mm12 = got
        return got
    acos13 = math.acos(1.0 / 3.0)
    pi = math.pi
    sol0 = 3 * acos13 - pi
    tau0 = 4 * pi - 20 * sol0
    return (sol0 * math.sqrt(8) / tau0,
            (6 * sol0 - pi) * math.sqrt(2) / (6 * tau0))


def _mm12_dy(N):
    """atan(sqrt(8)) must NOT go through tmexact's `arctanIPos` branch
    (its `halfPiI(max(N,512))` bound is ~0.004 wide, and sol0/tau0
    amplify it through 1/tau0).  Reduction at pi/4 (the landed
    `arctanINearP` trick): atan(x) = pi/4 + atan((x-1)/(x+1)); for
    x = sqrt(8) the reduced argument is ~0.4775 and the base series at
    N=48 has remainder ~1e-32."""
    sqrt8 = N.sqrt(dyad.Dy.from_int(8))
    sqrt2 = N.sqrt(dyad.Dy.from_int(2))
    red = (sqrt8 - 1) / (sqrt8 + 1)
    a_red = N.atan(red)                       # base-branch series, N = 48
    pi4 = N.pi() / 4
    acos13 = pi4 + a_red
    pi = N.pi()
    sol0 = 3 * acos13 - pi
    tau0 = 4 * pi - 20 * sol0
    mm1 = sol0 * sqrt8 / tau0
    mm2 = (6 * sol0 - pi) * sqrt2 / (6 * tau0)
    return mm1, mm2


# ---------------------------------------------------------------- exact deltaX

def deltaX_rat(x):
    """Exact rational deltaX at a point (vertex evaluation)."""
    x1, x2, x3, x4, x5, x6 = x
    return (x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6)
            + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
            + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6)
            - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6)


_DCACHE = {}


def delta_corner_min(xbox):
    """Exact min of deltaX over the x-box (separate concavity => vertex).
    Memoised per x-box: one gamma4 evaluation runs 19 dihY atoms on the
    same box."""
    key = tuple(xbox)
    v = _DCACHE.get(key)
    if v is None:
        v = min(deltaX_rat(list(c)) for c in itertools.product(*xbox))
        if len(_DCACHE) > 200000:
            _DCACHE.clear()
        _DCACHE[key] = v
    return v


# ---------------------------------------------------------------- atoms

def deltaX_jet(N, x, xbox=None):
    """deltaX jet with the certified corner lift on the value lower end."""
    A = J.deltaX(N, x)
    if xbox is not None and N.name == "dy":
        cmin_lo = dyad.floor_grid(delta_corner_min(xbox), N.floor_grid)
        if X.ble(A.v.lo, cmin_lo):
            A.v = dyad.Dy(cmin_lo, A.v.hi)
    return A


def deltaX4_jet(N, x):
    x1, x2, x3, x4, x5, x6 = x
    return J.add(J.add(J.add(J.add(J.mul(J.mul(J.neg(x2), x3), J.const(N, x1.v * 0 + 1)),
                                  J.neg(J.mul(x1, x4))),
                            J.mul(x2, x5)),
                      J.mul(x3, x6)),
                J.add(J.neg(J.mul(x5, x6)),
                      J.mul(x1, J.add(J.add(J.add(J.add(J.neg(x1), x2), x3), J.neg(x4)),
                                      J.add(x5, x6)))))


def _lift_radicand(A, floor_lo):
    """Raise the value interval's lower end to the sound floor (Dy only;
    `floor_lo` is a degenerate Dy or None; keeps max(lo, floor))."""
    if floor_lo is not None and isinstance(A.v, dyad.Dy) \
            and X.ble(A.v.lo, floor_lo.lo):
        A = J.Jet(dyad.Dy(floor_lo.lo, A.v.hi), A.g, A.H)
    return A


def dihXf_t(N, x, xbox=None):
    dx = deltaX_jet(N, x, xbox)
    floor = None
    if N.name == "dy" and xbox is not None:
        floor = dyad.Dy.from_frac(4 * xbox[0][0] * delta_corner_min(xbox),
                                  N.floor_grid)
    rad = _lift_radicand(J.mul(J.mul(J.const(N, C(N, F(4))), x[0]), dx), floor)
    a = J.sqrt(rad, N)
    b = J.neg(deltaX4_jet(N, x))
    return J.add(J.const(N, N.pi() / 2), J.atan2(b, a, N))


def dihY_t(N, y, ybox=None):
    xbox = None
    if ybox is not None:
        xbox = tuple((lo * lo, hi * hi) for lo, hi in ybox)
    return dihXf_t(N, [J.mul(v, v) for v in y], xbox)


def _pbox(ybox, pm):
    """Permute a box alongside the permuted y list (the dihY radicand
    floor must be anchored at the ATOM's own first coordinate; delta is
    invariant under the lane perms, so the corner-min is unchanged, but
    the x1-box lo is not)."""
    if ybox is None:
        return None
    return tuple(ybox[k] for k in pm)


def solY_t(N, y, ybox=None):
    y1, y2, y3, y4, y5, y6 = y
    return J.sub(J.add(J.add(dihY_t(N, [y1, y2, y3, y4, y5, y6], ybox),
                             dihY_t(N, [y2, y3, y1, y5, y6, y4],
                                    _pbox(ybox, (1, 2, 0, 4, 5, 3)))),
                       dihY_t(N, [y3, y1, y2, y6, y4, y5],
                              _pbox(ybox, (2, 0, 1, 5, 3, 4)))),
                 J.const(N, N.pi()))


def _jet_hull(A, B):
    """Coordinate-wise interval hull of two jets (prototype `jet2.jet_hull`)."""
    lo = lambda x, y: dyad.Dy(X.dmin(x.lo, y.lo), X.dmax(x.hi, y.hi))
    return J.Jet(lo(A.v, B.v),
                 [lo(a, b) for a, b in zip(A.g, B.g)],
                 [[lo(A.H[i][j], B.H[i][j]) for j in range(6)]
                  for i in range(6)])


KINK_H = F(63, 50)   # h0 = 2.52 / 2: the lmfun kink in the h = y/2 coordinate


def lmfun_side(N, y_jet, side):
    """lmfun on a box known to lie on one side of the kink y = 2*h0 = 2.52.
    side: 'left' (y <= 2h0) => affine branch; 'right' => 0.

    Certified (dy) boxes that *round across* the kink (a nav leaf endpoint
    may be exactly y = 2.52 = 63/50, which is not dyadic, so the outward
    dyadic box crosses it, by <= 2^-23): lmfun is continuous, piecewise
    affine/zero, with one-sided slopes -1/(2(h0-1)) and 0 and second
    derivative 0 at every smooth point — the sound enclosure on the
    crossing box is the hull of the two branch jets (prototype
    `jet_hull` mode).  The future Lean consumption of crossing boxes
    needs the piecewise-C1 chain rule (the M1 `iteHullTM2` composite
    situation); see SCHEMA.md.  Float navigation points never cross.
    """
    if N.name != "dy":
        if side == 'right':
            return J.const(N, C(N, F(0)))
        h = J.scale(y_jet, C(N, F(1, 2)))
        return J.div(J.sub(J.const(N, N.h0), h), J.const(N, N.h0 - N.one))
    h = J.scale(y_jet, C(N, F(1, 2)))
    if h.v.hi_frac() <= KINK_H:
        return J.div(J.sub(J.const(N, N.h0), h), J.const(N, N.h0 - N.one))
    if h.v.lo_frac() >= KINK_H:
        return J.const(N, C(N, F(0)))
    left = J.div(J.sub(J.const(N, N.h0), h), J.const(N, N.h0 - N.one))
    return _jet_hull(left, J.const(N, C(N, F(0))))


def gamma4_t(N, y, sides, ybox=None):
    y1, y2, y3, y4, y5, y6 = y
    def dyf(idx):
        yy = [y[k] for k in idx]
        return dihY_t(N, yy, _pbox(ybox, idx))
    S = J.add(J.add(J.add(solY_t(N, [y1, y2, y3, y4, y5, y6], ybox),
                          solY_t(N, [y1, y5, y6, y4, y2, y3],
                                 _pbox(ybox, (0, 4, 5, 3, 1, 2)))),
                    solY_t(N, [y4, y5, y3, y1, y2, y6],
                           _pbox(ybox, (3, 4, 2, 0, 1, 5)))),
              solY_t(N, [y4, y2, y6, y1, y5, y3],
                     _pbox(ybox, (3, 1, 5, 0, 4, 2))))
    D_PERMS = ((0, 1, 2, 3, 4, 5), (1, 2, 0, 4, 5, 3), (2, 0, 1, 5, 3, 4),
               (3, 2, 4, 0, 5, 1), (4, 0, 5, 1, 3, 2), (5, 0, 4, 2, 3, 1))
    dterms = [dyf(pm) for pm in D_PERMS]
    D = J.add(J.add(J.add(J.add(J.add(
        J.mul(lmfun_side(N, y1, sides[0]), dterms[0]),
        J.mul(lmfun_side(N, y2, sides[1]), dterms[1])),
        J.mul(lmfun_side(N, y3, sides[2]), dterms[2])),
        J.mul(lmfun_side(N, y4, sides[3]), dterms[3])),
        J.mul(lmfun_side(N, y5, sides[4]), dterms[4])),
        J.mul(lmfun_side(N, y6, sides[5]), dterms[5]))
    mm1, mm2 = mm12(N)
    xbox = None if ybox is None else tuple((lo * lo, hi * hi) for lo, hi in ybox)
    dxj = deltaX_jet(N, [J.mul(v, v) for v in y], xbox)
    floor = None
    if N.name == "dy" and xbox is not None:
        floor = dyad.Dy.from_frac(delta_corner_min(xbox), N.floor_grid)
    volY = J.div(J.sqrt(_lift_radicand(dxj, floor), N), J.const(N, C(N, F(12))))
    vol4 = J.sub(J.mul(J.const(N, 2 * mm1 / N.pi()), S),
                 J.mul(J.const(N, 8 * mm2 / N.pi()), D))
    return J.sub(volY, vol4)


# ---------------------------------------------------------------- pilots

def main_jet(N, y, w, m, sides, ybox=None):
    """main = gamma4/w + m*betaBumpLb - (aSpine5 + bSpine5*dihY)."""
    g = gamma4_t(N, y, sides, ybox)
    d = dihY_t(N, y, ybox)
    return J.add(J.add(J.scale(g, C(N, F(1, w))),
                       J.const(N, C(N, m * BETA))),
                 J.add(J.const(N, C(N, -A5)),
                       J.scale(d, C(N, NEG_B5))))


def margin_jet(N, y, Bcoef, affine, const, sides, ybox=None):
    """margin = gamma4 + Bcoef*dihY + sum c_i y_i + const.
    `affine` is a list of (index, Fraction) in fixed accumulation order."""
    g = gamma4_t(N, y, sides, ybox)
    d = dihY_t(N, y, ybox)
    out = J.add(g, J.scale(d, C(N, Bcoef)))
    out = J.add(out, J.const(N, C(N, const)))
    for k, c in affine:
        out = J.add(out, J.scale(y[k], C(N, c)))
    return out


# ---------------------------------------------------------------- box entries

def var_jet(N, i, box):
    """Variable jet over a box; `box` entries are backend scalars
    (float midpoints for navigation, Dy intervals for certification)."""
    if N.name == "dy":
        v = box[i]
    else:
        v = (float(box[i][0]) + float(box[i][1])) / 2
    z = [v * 0 for _ in range(6)]
    H = [[v * 0 for _ in range(6)] for _ in range(6)]
    g = list(z)
    g[i] = v * 0 + 1
    return J.Jet(v, g, H)


def point_jet(N, i, y):
    """Variable jet at an exact point y (Fraction, or a degenerate Dy)."""
    if N.name == "dy":
        v = y if isinstance(y, dyad.Dy) else dyad.Dy.from_frac(y, N.point_grid)
    else:
        v = float(y)
    z = [v * 0 for _ in range(6)]
    H = [[v * 0 for _ in range(6)] for _ in range(6)]
    g = list(z)
    g[i] = v * 0 + 1
    return J.Jet(v, g, H)


def box_widths(box):
    return [hi - lo for lo, hi in box]


def box_mid(box):
    return [(lo + hi) / 2 for lo, hi in box]
