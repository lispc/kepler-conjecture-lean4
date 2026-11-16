"""dyad.py — certified dyadic-interval backend (the C1 supplier's arithmetic).

Every scalar is a `Dy`, an outward-rounded dyadic interval `(lo, hi)` with
`lo`/`hi` dyadic integer pairs `(m, e)` in the sense of `tmexact.py` (the
bit-exact Python replica of the Lean interval kernel: Dyadic/DInterval
ops, `sqrtI`/`sqrtRel`, `arctanI`, `halfPiI`).  A box evaluation over
`Dy` scalars is therefore a machine-checkable enclosure by construction:

  * + - * and the tight square: exact dyadic interval arithmetic
    (`tmexact.iadd/isub/imul`); the square `{t*t : t in x}` is computed
    directly (never the wider interval product `x*x`);
  * division / reciprocal: `tmexact.irecip` at fixed granularity
    `out = 2^-80` (M1-calibrated), hard-fails on a sign-straddling
    denominator;
  * sqrt: `tmexact.sqrtRel` on both ends (mantissas via `sqrtMantissaRel`,
    the 2^-160-shifted integer isqrt — outward by construction); the
    radicand must be strictly positive;
  * arctan: `tmexact.arctanI` (branch structure verbatim, alternating
    series with per-term outward `divFloorQ` and the term-shaped
    remainder bound), series order = `rung` (default 64: every atan
    argument of this lane satisfies |u| <= 0.71, so the alternating
    remainder <= 0.71^129/129 < 2^-80; the |u| >= 1 branches of
    `arctanI` fall back to `halfPiI(max(rung, 512))` inside tmexact);
  * pi: `2 * halfPiI(512, out)` (tmexact), computed once per backend.

Decimal-string constants become the minimal straddling dyadic interval
on a fixed grid (`coef_grid`, default 2^-60) — a sound enclosure of the
exact rational (e.g. the pilot coefficients 0.0560305, -0.090009).

Every `sqrt` call appends its `(slo, shi)` mantissas to `sqrt_trace`
(evaluation order): the replay queue a future Lean bit-exact mirror
consumes (M1 `TMParams.sqrtCerts` discipline).

Failures raise `CertFail` (an ArithmeticError, deliberately NOT a
ValueError, so `jetlib.sqrt`'s F2 fallback hook cannot swallow it): the
emitter turns these into per-leaf `certFail` reasons, never into wrong
certificates.

NOTE: one `BackendDy` per process (the `out` granularity is shared
module state; the emitter never mixes granularities in one run).
"""

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import tmexact as X          # noqa: E402  (bit-exact Lean interval replica)

ZERO = X.ZERO
_OUT = [-80]                 # reciprocal granularity, set by BackendDy


class CertFail(ArithmeticError):
    """A certified evaluation could not produce an enclosure (sound abort)."""


def floor_grid(fr, g):
    """Exact Fraction -> dyadic (m, g) rounded DOWN (divmod floors)."""
    k = -g
    q, _ = divmod(fr.numerator * (1 << k), fr.denominator)
    return (q, g)


def ceil_grid(fr, g):
    """Exact Fraction -> dyadic (m, g) rounded UP."""
    q, r = divmod(fr.numerator * (1 << -g), fr.denominator)
    if r != 0:
        q += 1
    return (q, g)


def _d(o):
    """Coerce int/float literal operands to exact Dy (floats via Fraction,
    which is the exact binary value; jetlib only ever uses small ints)."""
    if isinstance(o, Dy):
        return o
    if isinstance(o, bool):
        raise CertFail("bool scalar operand")
    if isinstance(o, int):
        return Dy.from_int(o)
    if isinstance(o, float):
        return Dy.from_frac(Fraction(o), _GRID[0])
    raise CertFail("unsupported scalar operand %r" % (o,))


_GRID = [-60]                # float-literal coercion grid, set by BackendDy


class Dy:
    """Outward-rounded dyadic interval with float-like operator syntax."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        self.lo = lo
        self.hi = hi

    # ---- constructors -------------------------------------------------
    @classmethod
    def from_int(cls, k):
        return cls((k, 0))

    @classmethod
    def from_frac(cls, fr, g):
        """Exact rational -> minimal straddling dyadic interval on grid 2^g."""
        return cls(floor_grid(fr, g), ceil_grid(fr, g))

    @classmethod
    def from_decimal(cls, s, g):
        return cls.from_frac(Fraction(str(s)), g)

    # ---- exact rational views (for bound arithmetic) -------------------
    def lo_frac(self):
        return Fraction(self.lo[0], 1) * (Fraction(1, 2) ** (-self.lo[1])
                                          if self.lo[1] < 0
                                          else Fraction(1 << self.lo[1]))

    def hi_frac(self):
        return Fraction(self.hi[0], 1) * (Fraction(1, 2) ** (-self.hi[1])
                                          if self.hi[1] < 0
                                          else Fraction(1 << self.hi[1]))

    def __repr__(self):
        return "Dy[%s, %s]" % (self.lo, self.hi)

    # ---- arithmetic ----------------------------------------------------
    @staticmethod
    def _iv(d):
        return (d.lo, d.hi)

    def __add__(self, o):
        return Dy(*X.iadd(self._iv(self), self._iv(_d(o))))

    def __radd__(self, o):
        return _d(o).__add__(self)

    def __sub__(self, o):
        return Dy(*X.isub(self._iv(self), self._iv(_d(o))))

    def __rsub__(self, o):
        return _d(o).__sub__(self)

    def __neg__(self):
        return Dy(*X.ineg(self._iv(self)))

    def __mul__(self, o):
        return Dy(*X.imul(self._iv(self), self._iv(_d(o))))

    def __rmul__(self, o):
        return _d(o).__mul__(self)

    def __pow__(self, k):
        if k != 2:
            raise CertFail("Dy ** %r unsupported" % (k,))
        ll = X.mul(self.lo, self.lo)
        hh = X.mul(self.hi, self.hi)
        if X.ble(self.lo, ZERO) and X.ble(ZERO, self.hi):
            return Dy(ZERO, X.dmax(ll, hh))
        if X.ble(ZERO, self.lo):
            return Dy(ll, hh)
        return Dy(hh, ll)

    def __truediv__(self, o):
        return self * _d(o).recip()

    def __rtruediv__(self, o):
        return _d(o) / self

    def recip(self):
        r = X.irecip((self.lo, self.hi), _OUT[0])
        if r is None:
            raise CertFail("reciprocal of sign-straddling interval")
        return Dy(*r)


class BackendDy:
    """Certified backend handle (knobs + caches + the sqrt trace)."""

    name = "dy"

    def __init__(self, out=-80, rung=64, coef_grid=-60,
                 pi_rung=24, pi_rung_239=8, half_pi_terms=512,
                 point_grid=-60, floor_grid=-40):
        _OUT[0] = out
        _GRID[0] = coef_grid
        self.out = out
        self.rung = rung
        self.coef_grid = coef_grid
        self.pi_rung = pi_rung          # Machin atan(1/5) order
        self.pi_rung_239 = pi_rung_239  # Machin atan(1/239) order
        self.point_grid = point_grid    # Fraction points -> thin Dy
        self.floor_grid = floor_grid    # deltaX corner / radicand floors
        self.half_pi_terms = half_pi_terms  # arctanIPos fallback inside tmexact
        self.sqrt_trace = []
        self._pi = None
        self._h0 = None

    # -- numbers --------------------------------------------------------
    def num(self, s):
        if isinstance(s, bool):
            raise CertFail("bool constant")
        if isinstance(s, int):
            return Dy.from_int(s)
        return Dy.from_decimal(s, self.coef_grid)

    @property
    def one(self):
        return Dy.from_int(1)

    @property
    def h0(self):
        if self._h0 is None:
            self._h0 = Dy.from_decimal("1.26", self.coef_grid)
        return self._h0

    # -- atoms ----------------------------------------------------------
    def sqrt(self, v):
        if not isinstance(v, Dy):
            raise CertFail("sqrt expects a Dy interval")
        if not (v.lo[0] > 0):
            raise CertFail("sqrt radicand lower bound <= 0")
        slo = X.sqrtMantissaRel(v.lo)
        shi = X.sqrtMantissaRel(v.hi)
        Jl = X.sqrtRel(v.lo, slo)
        Jh = X.sqrtRel(v.hi, shi)
        if Jl is None or Jh is None:
            raise CertFail("sqrtRel failed on a positive radicand")
        self.sqrt_trace.append((slo, shi))
        return Dy(Jl[0], Jh[1])

    def atan(self, u):
        I = X.arctanI((u.lo, u.hi), self.rung, self.out)
        if I is None:
            raise CertFail("arctanI failed")
        return Dy(*I)

    def atan2(self, y, x):
        """atan2(y, x) = atan(y/x) for x > 0 (scalar-interval form)."""
        if not isinstance(x, Dy) or not (x.lo[0] > 0):
            raise CertFail("atan2 denominator not sign-definite positive")
        J = X.idiv((y.lo, y.hi), (x.lo, x.hi), self.out)
        if J is None:
            raise CertFail("atan2 reciprocal failed")
        I = X.arctanI(J, self.rung, self.out)
        if I is None:
            raise CertFail("arctanI failed in atan2")
        return Dy(*I)

    def pi(self):
        """Certified pi enclosure via Machin's formula
            pi = 16 atan(1/5) - 4 atan(1/239),
        all tmexact interval ops on degenerate dyadic intervals.
        (The landed `halfPiI(N)` bound carries the alternating Taylor
        remainder ~2/(2N+1) — 0.004 wide at N=512, useless here; Machin's
        remainders at rung 24 / 8 are ~1e-36 / 1e-41.)"""
        if self._pi is None:
            a5 = X.arctanI(X.idiv(((1, 0), (1, 0)), ((5, 0), (5, 0)),
                                  self.out), self.pi_rung, self.out)
            a239 = X.arctanI(X.idiv(((1, 0), (1, 0)), ((239, 0), (239, 0)),
                                    self.out), self.pi_rung_239, self.out)
            if a5 is None or a239 is None:
                raise CertFail("Machin arctan failed")
            lo = X.sub(X.mul((16, 0), a5[0]), X.mul((4, 0), a239[1]))
            hi = X.sub(X.mul((16, 0), a5[1]), X.mul((4, 0), a239[0]))
            self._pi = (lo, hi)
        return Dy(*self._pi)

    @staticmethod
    def abs(x):
        if X.ble(x.hi, ZERO):
            return Dy(X.ineg(x.hi), X.ineg(x.lo))
        if X.ble(ZERO, x.lo):
            return Dy(x.lo, x.hi)
        return Dy(ZERO, X.dmax(X.neg(x.lo), x.hi))

    @staticmethod
    def safe_cube_inv(v):
        raise CertFail("sqrt value range crosses 0 (impossible on pilot boxes)")
