"""jetlib.py — backend-generic second-order forward AD (value/gradient/Hessian).

Verbatim port of the g4port prototype `jet2.py` AD core, productionised:
  * the scalar operations (+ - * / ** and unary -) are supplied by the
    backend scalar type itself (float, or the certified dyadic interval
    `Dy` from `dyad.py`), so this module is shared by navigation and
    certification;
  * both documented prototype fixes are baked in and kept:
      (F1) interval squaring uses the tight square semantics (`x ** 2` is
           dispatched to the backend square, i.e. `{t*t : t in x}`, never
           the wider interval product `x*x`);
      (F2) the `sqrt` curvature coefficient has a backend hook
           (`N.safe_cube_inv`) for the case where the sqrt *value* range
           crosses 0 — unreachable on every pilot box (radicand
           >= 4*4*54) and a hard failure in the certified backend.
  * the derivative formulas are the pointwise AD identities
        mul : (AB)_i = A_i B + A B_i ;  (AB)_ij = A_ij B + A B_ij
              + A_i B_j + B_i A_j
        inv : (1/s)_i = -s_i/s^2 ;  (1/s)_ij = -s_ij/s^2 + 2 s_i s_j/s^3
        sqrt: (sqrt s)_i = s_i/(2 sqrt s) ;
              (sqrt s)_ij = s_ij/(2 sqrt s) - s_i s_j/(4 s^(3/2))
        atan: (atan s)_i = s_i/(1+s^2) ;
              (atan s)_ij = s_ij/(1+s^2) - 2 s s_i s_j/(1+s^2)^2
        atan2(b,a) = atan(b/a) for a > 0 (all four Lean `atn2` branches
              coincide there; `a` = sqrt(4 x1 deltaX) >= sqrt(4*4*54) on
              every box of this lane).
    A box evaluation is sound because every identity holds pointwise and
    every scalar occurring in it is contained in the corresponding
    interval; interval arithmetic then encloses the pointwise results.

The `deltaX` / `deltaX4` polynomial builders are kept here verbatim from
jet2 (operation order matters for float navigation parity); the pilot
atoms with sides / corner-lift hooks live in `exprs.py`.

Backend contract (see `nav.py` / `dyad.py`): scalars support + - * /
`** 2`, unary -, int coercion on the right (`2 * x`, `1 / x`), and the
module-level helpers `N.sqrt`, `N.atan`, `N.atan2(y, x)`, `N.pi()`,
`N.num(str)`, `N.h0`, `N.one`, `N.name`, plus (dyadic only)
`N.safe_cube_inv`.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# ------------------------------------------------------------------ Jet


class Jet:
    __slots__ = ("v", "g", "H")

    def __init__(self, v, g, H):
        self.v = v
        self.g = g
        self.H = H

    def __repr__(self):
        return "Jet(%r)" % (self.v,)


def const(N, v):
    z = [v * 0 for _ in range(6)]
    return Jet(v, z, [[0 * v for _ in range(6)] for _ in range(6)])


def var(N, i, v):
    z = [v * 0 for _ in range(6)]
    H = [[0 * v for _ in range(6)] for _ in range(6)]
    g = list(z)
    g[i] = v * 0 + 1
    return Jet(v, g, H)


def add(A, B):
    return Jet(A.v + B.v, [a + b for a, b in zip(A.g, B.g)],
               [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A.H, B.H)])


def neg(A):
    return Jet(-A.v, [-a for a in A.g], [[-a for a in ra] for ra in A.H])


def sub(A, B):
    return add(A, neg(B))


def scale(A, s):
    return Jet(A.v * s, [a * s for a in A.g], [[a * s for a in ra] for ra in A.H])


def _gg(g, i, j):
    """g_i*g_j, with the diagonal as a *square* (F1; intervals straddling 0)."""
    return g[i] ** 2 if i == j else g[i] * g[j]


def mul(A, B):
    av, bv = A.v, B.v
    g = [av * b + bv * a for a, b in zip(A.g, B.g)]
    H = [[av * B.H[i][j] + bv * A.H[i][j] + A.g[i] * B.g[j] + B.g[i] * A.g[j]
          for j in range(6)] for i in range(6)]
    return Jet(av * bv, g, H)


def inv(A):
    av = A.v
    d = av ** 2  # square via pow (F1: interval squaring must not straddle 0)
    g = [-a / d for a in A.g]
    H = [[-A.H[i][j] / d + 2 * _gg(A.g, i, j) / (d * av)
          for j in range(6)] for i in range(6)]
    return Jet(1 / av, g, H)


def div(A, B):
    return mul(A, inv(B))


def sqrt(A, N):
    v = N.sqrt(A.v)
    d = 1 / (2 * v)
    try:
        c = 1 / (4 * v * v * v)
    except (ZeroDivisionError, ValueError):
        # interval/TM range of sqrt crosses 0: conservative curvature
        # coefficient (F2; hard-fails in the certified backend).
        c = N.safe_cube_inv(v)
    g = [d * a for a in A.g]
    H = [[d * A.H[i][j] - c * _gg(A.g, i, j) for j in range(6)]
         for i in range(6)]
    return Jet(v, g, H)


def atan(A, N):
    u = A.v
    d = 1 / (1 + u * u)
    e = 2 * u * d * d
    g = [d * a for a in A.g]
    H = [[d * A.H[i][j] - e * _gg(A.g, i, j) for j in range(6)]
         for i in range(6)]
    return Jet(N.atan(u), g, H)


def atan2(B, A, N):
    """atan2(b, a) for a > 0 (all four Lean atn2 branches coincide there)."""
    a, b = A.v, B.v
    D = a ** 2 + b ** 2  # pow: interval squaring must not straddle 0
    fa = -b / D
    fb = a / D
    D2 = D ** 2
    fab = (b ** 2 - a ** 2) / D2
    faa = 2 * a * b / D2
    fbb = -2 * a * b / D2
    g = [fb * B.g[i] + fa * A.g[i] for i in range(6)]
    H = [[(fb * B.H[i][j] + fa * A.H[i][j]
           + fbb * _gg(B.g, i, j) + faa * _gg(A.g, i, j)
           + fab * (A.g[i] * B.g[j] + B.g[i] * A.g[j]))
          for j in range(6)] for i in range(6)]
    return Jet(N.atan2(b, a), g, H)


# ------------------------------------------------------------------ polynomials
# Verbatim from jet2.py (operation order matters for float parity).

def deltaX(N, x):
    x1, x2, x3, x4, x5, x6 = x
    return add(add(add(mul(mul(x1, x4), add(add(add(add(neg(x1), x2), x3),
                                               neg(x4)), add(x5, x6))),
                       mul(mul(x2, x5), add(add(add(add(x1, neg(x2)), x3), x4),
                                            add(neg(x5), x6)))),
                   mul(mul(x3, x6), add(add(add(add(x1, x2), neg(x3)), x4),
                                        add(x5, neg(x6))))),
               neg(add(add(add(mul(mul(x2, x3), x4), mul(mul(x1, x3), x5)),
                           mul(mul(x1, x2), x6)), mul(mul(x4, x5), x6))))


def deltaX4(N, x):
    x1, x2, x3, x4, x5, x6 = x
    return add(add(add(add(mul(mul(neg(x2), x3), const(N, x1.v * 0 + 1)),
                           neg(mul(x1, x4))),
                       mul(x2, x5)),
                   mul(x3, x6)),
               add(neg(mul(x5, x6)),
                   mul(x1, add(add(add(add(neg(x1), x2), x3), neg(x4)),
                               add(x5, x6)))))
