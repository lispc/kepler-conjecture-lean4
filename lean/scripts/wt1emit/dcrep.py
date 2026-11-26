#!/usr/bin/env python3
"""dcrep.py — bit-exact Python replica of the Lean DC kit of
`Kepler/Text/TaylorSecond/{DCKit,DCMatan,DCJet}.lean`.

The replica is *not* trusted: every literal it produces is turned into a Lean
`rfl`/`decide` obligation by the emitter, so a replica bug shows up as a
compile error.  Its only job is to supply candidate literals.

Semantics notes (all verified against the Lean sources):
  * `dnorm` bit length: `bl = max (Int.natAbs lo).log2 (Int.natAbs hi).log2 + 1`
    with `Nat.log2 0 = 0`, i.e. `log2 x = x.bit_length() - 1` for x > 0 and 0
    for x = 0.  (The older `dc_widths.py` used `bitlen + 1`, which is off by
    one — that is the `k` mismatch of M5 finding #2.)
  * `Int.shiftRight x d` is the *arithmetic* (floor) shift for x < 0.
  * `Int` `/` in `dInv`: all `dInv` arguments in the tree have `lo > 0`, where
    truncated and Euclidean division agree; we assert `lo > 0`.
"""
import math
import sys

sys.set_int_max_str_digits(500000)


# ---------------------------------------------------------------- core
def log2(n):
    return n.bit_length() - 1 if n > 0 else 0


def bitlen_leanish(x):
    return log2(abs(x))


def dnorm(k, lo, hi):
    bl = max(log2(abs(lo)), log2(abs(hi))) + 1
    if bl <= 200:
        return (k, lo, hi)
    drop = min(bl - 200, abs(k))
    return (k - drop, lo >> drop, -((-hi) >> drop))


def dInt(n):
    return (0, n, n)


def dAdd(A, B):
    k = max(A[0], B[0])
    return dnorm(k,
                 (A[1] << (k - A[0])) + (B[1] << (k - B[0])),
                 (A[2] << (k - A[0])) + (B[2] << (k - B[0])))


def dNeg(A):
    return (A[0], -A[2], -A[1])


def dSub(A, B):
    return dAdd(A, dNeg(B))


def dMul(A, B):
    c1 = A[1] * B[1]
    c2 = A[1] * B[2]
    c3 = A[2] * B[1]
    c4 = A[2] * B[2]
    return dnorm(A[0] + B[0], min(c1, c2, c3, c4), max(c1, c2, c3, c4))


def ediv(a, b):
    """Lean `Int./` (Euclidean): remainder `a - b*q` is in `[0, |b|)`.

    The M7 replica asserted `lo > 0`; the M8 preflight must evaluate *every*
    manifest box, including ones whose `matan` argument bracket straddles the
    pole (those are exactly the boxes whose `hbig`/`dLoBig` gate is false, and
    the attribution must come from the gate, not from a Python crash), so the
    definition is now evaluated faithfully for both signs.
    """
    if b == 0:
        return 0
    if b > 0:
        return a // b
    r = a % (-b)
    return (a - r) // b


def dInv(B):
    if B[1] <= 0:
        NONPOS_INV.append(B)
    bl = log2(abs(B[1])) + 1
    S = 208 + bl
    M = 1 << S
    return dnorm(S - B[0], ediv(M, B[2]), -ediv(-M, B[1]))


def dDiv(A, B):
    return dMul(A, dInv(B))


def dJoin(L, H):
    kk = max(L[0], H[0])
    return (kk, L[1] << (kk - L[0]), H[2] << (kk - H[0]))


def dClamp0(A):
    return (A[0], max(A[1], 0), A[2])


def dSqrtCore(A):
    K = (A[0] + 201) // 2
    d = 2 * K - A[0]
    lo = A[1] << d
    hi = A[2] << d
    rlo = math.isqrt(lo) if lo > 0 else 0
    rhi = math.isqrt(hi) if hi > 0 else 0
    return (K, rlo, rhi + 1)


def dSqrt(A):
    return dSqrtCore(dClamp0(A))


# ---------------------------------------------------------------- constants
def _consts():
    g = {}
    g['ONE'] = dInt(1)
    g['PIbr'] = (40, 3454217652357, 3454217652358)
    g['SQ2'] = (40, 1554944255987, 1554944255988)
    g['HALF'] = dInv(dInt(2))
    g['QUARTER'] = dInv(dInt(4))
    g['THIRD'] = dInv(dInt(3))
    g['FIFTH'] = dInv(dInt(5))
    g['SEVENTH'] = dInv(dInt(7))
    g['NINTH'] = dInv(dInt(9))
    g['ELEVENTH'] = dInv(dInt(11))
    return g


NONPOS_INV = []

C = _consts()
ONE = C['ONE']
PIbr = C['PIbr']
HALF = C['HALF']
QUARTER = C['QUARTER']
THIRD = C['THIRD']
FIFTH = C['FIFTH']
SEVENTH = C['SEVENTH']
NINTH = C['NINTH']
ELEVENTH = C['ELEVENTH']


# ---------------------------------------------------------------- polynomials
def evalP9(A):
    return dAdd(ONE, dMul(A, dAdd(dNeg(THIRD), dMul(A, dAdd(FIFTH, dMul(A, dAdd(
        dNeg(SEVENTH), dMul(A, dAdd(NINTH, dMul(A, dNeg(ELEVENTH)))))))))))


def evalA9(A):
    return dAdd(ONE, dMul(A, dAdd(dNeg(THIRD), dMul(A, dAdd(FIFTH, dMul(A, dAdd(
        dNeg(SEVENTH), dMul(A, NINTH))))))))


def evalA7(A):
    return dAdd(ONE, dMul(A, dAdd(dNeg(THIRD), dMul(A, dAdd(FIFTH, dMul(A, dNeg(SEVENTH)))))))


def evalA5(A):
    return dAdd(ONE, dMul(A, dAdd(dNeg(THIRD), dMul(A, FIFTH))))


# ---------------------------------------------------------------- matan arms
def dMatan9(A):
    return dJoin(evalP9(A), evalA9(A))


def dMatanWp(A):
    SQ = dSqrt(A)
    W = dDiv(dSub(SQ, ONE), dAdd(SQ, ONE))
    W2 = dMul(W, W)
    X = dAdd(dMul(QUARTER, PIbr), dMul(W, evalA7(W2)))
    Y = dAdd(dMul(QUARTER, PIbr), dMul(W, evalA5(W2)))
    return dJoin(dDiv(X, SQ), dDiv(Y, SQ))


def dMatanU9(A):
    SQ = dSqrt(A)
    R = dInv(SQ)
    R2 = dMul(R, R)
    X = dSub(dMul(HALF, PIbr), dMul(R, evalA9(R2)))
    Y = dSub(dMul(HALF, PIbr), dMul(R, evalP9(R2)))
    return dJoin(dDiv(X, SQ), dDiv(Y, SQ))


def dMatanMir(A, Minner):
    SQ = dSqrt(A)
    return dSub(dDiv(dMul(HALF, PIbr), SQ), dDiv(Minner, A))


def dHiLt(X, Y):
    kk = max(X[0], Y[0])
    return (X[2] << (kk - X[0])) < (Y[2] << (kk - Y[0]))


def dMatanTight(A):
    if dHiLt(dInv(A), dInt(4)):
        return dMatanWp(dInv(A))
    return dMatanU9(dInv(A))


def dMatanTightW(A):
    """M8 local inner: `dMatanWp` only inside its designed band `1 < r < 4`
    (both tests must be *provable* `decide` facts), `dMatanU9` otherwise."""
    D = dInv(A)
    if dLoGt(D, ONE) and dHiLt(D, dInt(4)):
        return dMatanWp(D)
    return dMatanU9(D)


def dMatanD(A, Mv):
    return dDiv(dSub(dInv(dAdd(ONE, A)), Mv), dMul(dInt(2), A))


# ---------------------------------------------------------------- gates
def dLoBig(A):
    if A[0] >= 100:
        return (1 << (A[0] - 100)) <= A[1]
    return A[1] > 0


def dLoGt(X, Y):
    kk = max(X[0], Y[0])
    return (X[1] << (kk - X[0])) > (Y[1] << (kk - Y[0]))


def dAbs(A):
    return (A[0], max(A[1] if A[1] > 0 else -A[2], 0), max(-A[1], A[2]))


# ---------------------------------------------------------------- printing
def dc(t):
    return '\u27e8(%d : \u2124), (%d : \u2124), (%d : \u2124)\u27e9' % t
