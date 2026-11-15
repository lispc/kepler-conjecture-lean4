"""Bit-exact Python replica of the Lean TM-hull certificate generator
`evalTMHullFill2D` (CertTMDiv2) and its kernel consumer `evalTMHullD2C`
(CertTM), using Python integers only (no floats anywhere).

Everything here is defined to match the Lean definitions *bit for bit*:

  Dyadic.add/mul/neg/ble/dmin/dmax/chopCeilTo      (Basic.lean, CertTM.lean)
  Dyadic.divFloorQ/recipFloor, DInterval.recip/div (Div.lean)
  Dyadic.sqrtI/sqrtRel                             (Sqrt.lean, CertTM.lean)
  taylorIter/arctanInterval/arctanPoint/arctanI    (Trans.lean)
  TaylorM.constTM/varTM/fallbackTM/closedTM/mul/
    sqrt/invCore/inv/trans/valueRange/loBound      (CertTM.lean)
  DInterval.jumpBound/iteHullTM2, loaLower         (CertTM.lean, CertTMDiv2.lean)
  evalIParams / evalIParamsFill                    (CertTM.lean)
  evalTMHullFill2D (the probe that reports the sqrt triples) (CertTMDiv2.lean)
  evalTMHullD2C (the kernel C checker)              (CertTM.lean)

Lean `Int` division is Euclidean (remainder in `[0, |b|)`), i.e. floor for a
positive divisor and ceiling for a negative one; `divFloorQ` compensates the
negative-divisor case with `- 1`.  `ediv` below reproduces that exactly.
"""

from math import isqrt

SX = ["slo", "shi", "sc"]          # triple field order (SqrtTMP)
ZERO = (0, 0)
ZIV = (ZERO, ZERO)
PI4D = ((14488038916154245684, -64), (14488038916154245685, -64))
BAND = (5, -3)                     # atanCurvBand = 5/8
OUT = -80                          # uniform granularity used by the probe


# ------------------------------------------------------------------ dyadics
def add(a, b):
    e = a[1] if a[1] < b[1] else b[1]
    return ((a[0] << (a[1] - e)) + (b[0] << (b[1] - e)), e)


def sub(a, b):
    return add(a, (-b[0], b[1]))


def mul(a, b):
    return (a[0] * b[0], a[1] + b[1])


def neg(a):
    return (-a[0], a[1])


def _al(a, b):
    e = a[1] if a[1] < b[1] else b[1]
    return a[0] << (a[1] - e), b[0] << (b[1] - e)


def ble(a, b):
    x, y = _al(a, b)
    return x <= y


def blt(a, b):
    x, y = _al(a, b)
    return x < y


def dmin(a, b):
    return a if ble(a, b) else b


def dmax(a, b):
    return b if ble(a, b) else a


def isPos(d):
    return d[0] > 0


def isNN(d):
    return d[0] >= 0


def isNeg(d):
    return d[0] < 0


def chopCeilTo(d, e0):
    """Lean `chopCeilTo`: round the mantissa UP at exponent e0 (Euclidean /
    floor division by a positive power of two)."""
    if e0 <= d[1]:
        return d
    k = e0 - d[1]
    return ((d[0] + (1 << k) - 1) // (1 << k), e0)


# -------------------------------------------------------- integer division
def ediv(a, b):
    """Lean `Int./` (Euclidean): floor for b > 0, ceiling for b < 0."""
    if b > 0:
        return a // b
    return -((-a) // b)


def divFloorQ(a, b, out):
    """`Dyadic.divFloorQ a b out` (Div.lean), bit for bit."""
    if b[0] == 0:
        return None
    k = a[1] - b[1] - out
    if k >= 0:
        n = a[0] << k
        if b[0] > 0:
            return (n // b[0], out)
        return (ediv(n, b[0]) - 1, out)
    m = b[1] + out - a[1]
    den = b[0] << m
    if b[0] > 0:
        return (a[0] // den, out)
    return (ediv(a[0], den) - 1, out)


def recipFloor(b, out):
    return divFloorQ((1, 0), b, out)


# --------------------------------------------------------------- intervals
def iadd(I, J):
    return (add(I[0], J[0]), add(I[1], J[1]))


def ineg(I):
    return (neg(I[1]), neg(I[0]))


def isub(I, J):
    return iadd(I, ineg(J))


def imul(I, J):
    c00, c01 = mul(I[0], J[0]), mul(I[0], J[1])
    c10, c11 = mul(I[1], J[0]), mul(I[1], J[1])
    return (dmin(dmin(c00, c01), dmin(c10, c11)),
            dmax(dmax(c00, c01), dmax(c10, c11)))


def iabs(I):
    if ble(I[1], ZERO):
        lo = neg(I[1])
    elif ble(ZERO, I[0]):
        lo = I[0]
    else:
        lo = ZERO
    hi = dmax(dmax(I[0], neg(I[0])), dmax(I[1], neg(I[1])))
    return (lo, hi)


def ihull(I, J):
    return (dmin(I[0], J[0]), dmax(I[1], J[1]))


def irecip(I, out):
    if isPos(I[0]) or isNeg(I[1]):
        fl = recipFloor(I[1], out)
        fu = recipFloor(I[0], out)
        if fl is None or fu is None:
            return None
        return (fl, (fu[0] + 1, out))
    return None


def idiv(I, J, out):
    r = irecip(J, out)
    return None if r is None else imul(I, r)


def loaLower(I):
    if isNN(I[0]):
        return I[0]
    if isNeg(I[1]):
        return neg(I[1])
    return ZERO


# --------------------------------------------------------------- sqrt certs
def sqrtI(d, s):
    """`Dyadic.sqrtI d s` (Sqrt.lean)."""
    n = d[0] << (d[1] % 2)
    if 0 <= s and 0 <= d[0] and s * s <= n < (s + 1) * (s + 1):
        return ((s, d[1] // 2), (s + 1, d[1] // 2))
    return None


def sqrtRel(d, s):
    """`Dyadic.sqrtRel d s`: sqrtI on the 2^160-value-shifted radicand,
    descaled by 2^-80."""
    if d[0] < 0:
        return None
    J = sqrtI((d[0] << 160, d[1]), s)
    if J is None:
        return None
    return ((J[0][0], J[0][1] - 80), (J[1][0], J[1][1] - 80))


def sqrtMantissa(d):
    """`sqrtMantissa` (guard arm): representation-bound exact floor root."""
    if d[0] >= 0:
        return isqrt(d[0] << (d[1] % 2))
    return 0


def sqrtMantissaRel(d):
    """`sqrtMantissaRel` (TM arm): fixed 2^-80 relative exact floor root."""
    if d[0] >= 0:
        return isqrt(d[0] << 160 << (d[1] % 2))
    return 0


# ------------------------------------------------------------------ arctan
def npow(x, n):
    """`Dyadic.npow x n` (exact repeated multiplication)."""
    return (x[0] ** n, x[1] * n)


def arctanInterval(x, N, out):
    """`arctanInterval x N out`: alternating Taylor with per-term
    `divFloorQ` outward rounding and the term-shaped remainder."""
    lw = hg = ZERO
    x2 = mul(x, x)
    xp = (1, 0)
    for i in range(N):
        xp = mul(xp, x) if i == 0 else mul(xp, x2)
        q = divFloorQ(xp, ((2 * i + 1), 0), out)
        if q is None:
            return None
        if i % 2 == 0:
            lw = add(lw, q)
            hg = add(hg, (q[0] + 1, out))
        else:
            lw = add(lw, neg((q[0] + 1, out)))
            hg = add(hg, neg(q))
    u = divFloorQ(npow(x, 2 * N + 1), ((2 * N + 1), 0), out)
    if u is None:
        return None
    ulp = (u[0] + 1, out)
    return (sub(lw, ulp), add(hg, ulp))


def arctanPoint(z, N, out):
    if isNeg(z):
        L = arctanInterval(neg(z), N, out)
        return None if L is None else ineg(L)
    return arctanInterval(z, N, out)


def arctanIBase(J, N, out):
    if ble((-1, 0), J[0]) and ble(J[1], (1, 0)):
        L = arctanPoint(J[0], N, out)
        H = arctanPoint(J[1], N, out)
        if L is None or H is None:
            return None
        return (L[0], H[1])
    return None


def halfPiI(Npi, out):
    A = arctanPoint((1, 0), Npi, out)
    if A is None:
        return None
    return (mul((2, 0), A[0]), mul((2, 0), A[1]))


def arctanIPosAux(R, N, out):
    L = arctanPoint(dmax(R[0], ZERO), N, out)
    if L is None:
        return None
    H = arctanPoint(dmin(R[1], (1, 0)), N, out)
    if H is None:
        return None
    P = halfPiI(max(N, 512), out)
    if P is None:
        return None
    return isub(P, (L[0], H[1]))


def arctanIPos(J, N, out):
    if ble((1, 0), J[0]):
        R = irecip(J, out)
        return None if R is None else arctanIPosAux(R, N, out)
    return None


def arctanINeg(J, N, out):
    if ble(J[1], (-1, 0)):
        L = arctanIPos(ineg(J), N, out)
        return None if L is None else ineg(L)
    return None


def arctanI(J, N, out):
    """`arctanI` (Trans.lean), branch structure verbatim."""
    if ble((-1, 0), J[0]) and ble(J[1], (1, 0)):
        return arctanIBase(J, N, out)
    if ble((1, 0), J[0]):
        return arctanIPos(J, N, out)
    if ble(J[1], (-1, 0)):
        return arctanINeg(J, N, out)
    if ble((-1, 0), J[0]):
        a = arctanIBase((J[0], (1, 0)), N, out)
        b = arctanIPos(((1, 0), J[1]), N, out)
        return None if a is None or b is None else ihull(a, b)
    if ble(J[1], (1, 0)):
        a = arctanINeg((J[0], (-1, 0)), N, out)
        b = arctanIBase(((-1, 0), J[1]), N, out)
        return None if a is None or b is None else ihull(a, b)
    a = arctanINeg((J[0], (-1, 0)), N, out)
    b = arctanIBase(((-1, 0), (1, 0)), N, out)
    c = arctanIPos(((1, 0), J[1]), N, out)
    if a is None or b is None or c is None:
        return None
    return ihull(a, ihull(b, c))


def transOn(kind, I, N, out):
    """`Expr.transOn`, restricted to the kinds used by the TSKAJXY AST."""
    if kind == ".atan1K":
        if I[0] == (1, 0) and I[1] == (1, 0):
            return PI4D
        return arctanI(I, N, out)
    if kind == ".arctanK":
        return arctanI(I, N, out)
    raise ValueError("trans kind not needed by this AST: %r" % (kind,))


# ------------------------------------------------------------- Taylor model
class M(object):
    __slots__ = ("y", "w", "fB", "dfB", "err")

    def __init__(self, y, w, fB, dfB, err):
        self.y, self.w, self.fB, self.dfB, self.err = y, w, fB, dfB, err


def boxCenter(box):
    out = []
    for lo, hi in box:
        e = lo[1] if lo[1] < hi[1] else hi[1]
        out.append(((lo[0] << (lo[1] - e)) + (hi[0] << (hi[1] - e)), e - 1))
    return out


def boxW(box):
    c = boxCenter(box)
    return [dmax(sub(c[i], box[i][0]), sub(box[i][1], c[i]))
            for i in range(len(box))]


def W0(Mm):
    acc = ZERO
    for i in range(len(Mm.y)):
        acc = add(acc, mul(iabs(Mm.dfB[i])[1], Mm.w[i]))
    return acc


def W(Mm):
    return dmax(add(W0(Mm), Mm.err), ZERO)


def errScale(Mm):
    return 2 * min(w[1] for w in Mm.w) - 24


def constTM(ctx, d):
    return M(ctx[0], ctx[1], (d, d), [ZIV] * len(ctx[0]), ZERO)


def varTM(ctx, k):
    dfB = [(ZIV if i != k else ((1, 0), (1, 0))) for i in range(len(ctx[0]))]
    return M(ctx[0], ctx[1], (ctx[0][k], ctx[0][k]), dfB, ZERO)


def closedTM(ctx, I):
    return M(ctx[0], ctx[1], I, [ZIV] * len(ctx[0]), ZERO)


def fallbackTM(ctx, I):
    return M(ctx[0], ctx[1], I, [ZIV] * len(ctx[0]), add(I[1], neg(I[0])))


def mneg(Mm):
    return M(Mm.y, Mm.w, ineg(Mm.fB), [ineg(d) for d in Mm.dfB], Mm.err)


def madd(Mf, Mg):
    return M(Mf.y, Mf.w, iadd(Mf.fB, Mg.fB),
             [iadd(a, b) for a, b in zip(Mf.dfB, Mg.dfB)], add(Mf.err, Mg.err))


def msub(Mf, Mg):
    return madd(Mf, mneg(Mg))


def mmul(Mf, Mg):
    W0f, W0g = W0(Mf), W0(Mg)
    fB = imul(Mf.fB, Mg.fB)
    dfB = [iadd(imul(Mf.dfB[i], Mg.fB), imul(Mf.fB, Mg.dfB[i]))
           for i in range(len(Mf.y))]
    err = add(mul(W0f, W0g),
              add(mul(Mf.err, add(add(iabs(Mg.fB)[1], W0g), Mg.err)),
                  mul(Mg.err, add(iabs(Mf.fB)[1], W0f))))
    return M(Mf.y, Mf.w, fB, dfB, chopCeilTo(err, errScale(Mf)))


def msqrt(Mm, slo, shi, sc, o1, o2):
    """`TaylorM.sqrt` with the three mantissas supplied explicitly (the
    kernel consumes them from `TMParams`; the fill computes them)."""
    c = sub(Mm.fB[0], W(Mm))
    if not isPos(c):
        return None
    Jl = sqrtRel(Mm.fB[0], slo)
    if Jl is None:
        return None
    Jh = sqrtRel(Mm.fB[1], shi)
    if Jh is None:
        return None
    Jc = sqrtRel(c, sc)
    if Jc is None:
        return None
    J = irecip((mul((2, 0), Jl[0]), mul((2, 0), Jh[1])), o1)
    if J is None:
        return None
    KK = irecip((mul((8, 0), mul(c, Jc[0])), mul((8, 0), mul(c, Jc[0]))), o2)
    if KK is None:
        return None
    err = add(mul(Mm.err, J[1]), mul(mul(W(Mm), W(Mm)), KK[1]))
    return M(Mm.y, Mm.w, (Jl[0], Jh[1]),
             [imul(Mm.dfB[i], J) for i in range(len(Mm.y))],
             chopCeilTo(err, errScale(Mm))), Jc


def invCore(Mm, c, o0, o1, o2):
    V = irecip(Mm.fB, o0)
    if V is None:
        return None
    Jp = irecip((mul(c, c), mul(iabs(Mm.fB)[1], iabs(Mm.fB)[1])), o1)
    if Jp is None:
        return None
    cc = mul(c, mul(c, c))
    KK = irecip((cc, cc), o2)
    if KK is None:
        return None
    err = add(mul(Mm.err, iabs(Jp)[1]), mul(mul(W(Mm), W(Mm)), KK[1]))
    return M(Mm.y, Mm.w, V, [imul(Mm.dfB[i], ineg(Jp)) for i in range(len(Mm.y))],
             chopCeilTo(err, errScale(Mm)))


def minv(Mm, o0, o1, o2):
    cpos = sub(Mm.fB[0], W(Mm))
    cneg = neg(add(Mm.fB[1], W(Mm)))
    if isPos(cpos):
        return invCore(Mm, cpos, o0, o1, o2)
    if isPos(cneg):
        return invCore(Mm, cneg, o0, o1, o2)
    return None


def atanCurv(rLo, rHi, o2):
    if ble(rHi, neg(BAND)):
        Jc = irecip((add((1, 0), mul(neg(rHi), neg(rHi))),
                     add((1, 0), mul(neg(rHi), neg(rHi)))), o2)
        if Jc is None:
            return (7, -3)
        return mul(mul((2, 0), neg(rHi)), mul(Jc[1], Jc[1]))
    if ble(BAND, rLo):
        Jc = irecip((add((1, 0), mul(rLo, rLo)),
                     add((1, 0), mul(rLo, rLo))), o2)
        if Jc is None:
            return (7, -3)
        return mul(mul((2, 0), rLo), mul(Jc[1], Jc[1]))
    return (7, -3)


def mtrans(kind, Mm, N, out, o1, o2):
    """`TaylorM.trans` for the `atan`/`atan1K` branches."""
    if kind in (".arctanK", ".atan1K"):
        V = transOn(".arctanK", (Mm.fB[0], Mm.fB[1]), N, out)
        if V is None:
            return None
        aI = iabs(Mm.fB)
        J = irecip((add((1, 0), mul(aI[0], aI[0])),
                    add((1, 0), mul(aI[1], aI[1]))), o1)
        if J is None:
            return None
        C = dmin(atanCurv(sub(Mm.fB[0], W(Mm)), add(Mm.fB[1], W(Mm)), o2),
                 mul((2, 0), add(aI[1], W(Mm))))
        err = add(mul(Mm.err, iabs(J)[1]), mul(mul(W(Mm), W(Mm)), C))
        return M(Mm.y, Mm.w, V, [imul(Mm.dfB[i], J) for i in range(len(Mm.y))],
                 chopCeilTo(err, errScale(Mm)))
    raise ValueError("trans kind not needed: %r" % (kind,))


def valueRange(Mm):
    return (sub(Mm.fB[0], W(Mm)), add(Mm.fB[1], W(Mm)))


def jumpBound(I, J):
    return dmax(dmax(sub(I[0], J[1]), sub(J[1], I[0])),
                dmax(sub(I[1], J[0]), sub(J[0], I[1])))


def iteHullTM2(Mt, Me):
    return M(Mt.y, Mt.w, ihull(valueRange(Mt), valueRange(Me)),
             [ihull(Mt.dfB[i], Me.dfB[i]) for i in range(len(Mt.y))],
             dmax(add(dmax(Mt.err, Me.err), jumpBound(Mt.fB, Me.fB)), ZERO))


def loBound(Mm, box):
    acc = Mm.fB[0]
    for i in range(len(Mm.y)):
        u = (sub(box[i][0], Mm.y[i]), sub(box[i][1], Mm.y[i]))
        acc = add(acc, imul(Mm.dfB[i], u)[0])
    return sub(acc, Mm.err)


# ------------------------------------------------------- plain interval eval
def _i(s):
    return int(str(s).strip("()"))


def _const(args):
    t = " ".join(args).replace("⟨", "").replace("⟩", "").replace(",", " ")
    m, e = t.split()
    return (int(m), int(e))


def ieval(ast, box):
    """`IExpr.eval` (Expr.lean), verbatim."""
    op, args = ast
    if op == ".const":
        d = _const(args)
        return (d, d)
    if op == ".var":
        return box[_i(args[0])]
    if op == ".neg":
        v = ieval(args[0], box)
        return None if v is None else ineg(v)
    if op == ".abs":
        v = ieval(args[0], box)
        return None if v is None else iabs(v)
    if op == ".add":
        a, b = ieval(args[0], box), ieval(args[1], box)
        return None if a is None or b is None else iadd(a, b)
    if op == ".sub":
        a, b = ieval(args[0], box), ieval(args[1], box)
        return None if a is None or b is None else isub(a, b)
    if op == ".mul":
        a, b = ieval(args[0], box), ieval(args[1], box)
        return None if a is None or b is None else imul(a, b)
    if op == ".div":
        a, b = ieval(args[0], box), ieval(args[1], box)
        if a is None or b is None:
            return None
        return idiv(a, b, _i(args[2]))
    if op == ".sqrt":
        v = ieval(args[0], box)
        if v is None:
            return None
        Jl = sqrtI(v[0], _i(args[1]))
        if Jl is None:
            return None
        Jh = sqrtI(v[1], _i(args[2]))
        if Jh is None:
            return None
        return (Jl[0], Jh[1])
    if op == ".trans":
        v = ieval(args[1], box)
        return None if v is None else transOn(args[0], v, _i(args[2]), _i(args[3]))
    if op == ".ite":
        C = ieval(args[0], box)
        if C is None:
            return None
        if isNeg(C[1]):
            return ieval(args[1], box)
        if isNN(C[0]):
            return ieval(args[2], box)
        t, e = ieval(args[1], box), ieval(args[2], box)
        return None if t is None or e is None else ihull(t, e)
    raise ValueError(op)


def is_closed(ast):
    op, args = ast
    if op == ".var":
        return False
    return all(is_closed(a) if isinstance(a, tuple) else True for a in args)


# --------------------------------------------- guard evaluator (evalIParams)
# `ps` is (n_sqrt, n_inv, n_trans): remaining certificate counts of the
# template.  The guard consumes one sqrt cert per sqrt node (head?/tail).
def evalIParams(ast, box, ps):
    """`evalIParams` (CertTM) / `evalIParamsFill` (leak-free, same flow):
    returns (I, ps', triples) where triples are (slo, shi, 0) per sqrt node."""
    op, args = ast
    n_sq, n_iv, n_tr = ps
    if op == ".const":
        d = _const(args)
        return ((d, d), ps, [])
    if op == ".var":
        return (box[_i(args[0])], ps, [])
    if op == ".neg":
        r = evalIParams(args[0], box, ps)
        return None if r is None else (ineg(r[0]), r[1], r[2])
    if op == ".abs":
        r = evalIParams(args[0], box, ps)
        return None if r is None else (iabs(r[0]), r[1], r[2])
    if op in (".add", ".sub", ".mul"):
        a = evalIParams(args[0], box, ps)
        if a is None:
            return None
        b = evalIParams(args[1], box, a[1])
        if b is None:
            return None
        if op == ".add":
            I = iadd(a[0], b[0])
        elif op == ".sub":
            I = isub(a[0], b[0])
        else:
            I = imul(a[0], b[0])
        return (I, b[1], a[2] + b[2])
    if op == ".div":
        a = evalIParams(args[0], box, ps)
        if a is None:
            return None
        b = evalIParams(args[1], box, a[1])
        if b is None:
            return None
        I = idiv(a[0], b[0], _i(args[2]))
        return None if I is None else (I, b[1], a[2] + b[2])
    if op == ".sqrt":
        if n_sq <= 0:
            return None
        ps1 = (n_sq - 1, n_iv, n_tr)
        a = evalIParams(args[0], box, ps)
        if a is None:
            return None
        I = a[0]
        if isNeg(I[1]):
            return None
        slo = sqrtMantissa(I[0])
        shi = sqrtMantissa(I[1])
        Jh = sqrtI(I[1], shi)
        if Jh is None:
            return None
        if isNN(I[0]):
            Jl = sqrtI(I[0], slo)
            if Jl is None:
                return None
            L = Jl[0]
        else:
            L = ZERO
        return ((L, Jh[1]), ps1, a[2] + [(slo, shi, 0)])
    if op == ".trans":
        v = evalIParams(args[1], box, ps)
        if v is None:
            return None
        I = transOn(args[0], v[0], _i(args[2]), _i(args[3]))
        return None if I is None else (I, v[1], v[2])
    if op == ".ite":
        C = evalIParams(args[0], box, ps)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = evalIParams(args[1], box, C[1])
            return None if r is None else (r[0], r[1], C[2] + r[2])
        if isNN(C[0][0]):
            r = evalIParams(args[2], box, C[1])
            return None if r is None else (r[0], r[1], C[2] + r[2])
        t = evalIParams(args[1], box, C[1])
        if t is None:
            return None
        e = evalIParams(args[2], box, t[1])
        if e is None:
            return None
        return (ihull(t[0], e[0]), e[1], C[2] + t[2] + e[2])
    raise ValueError(op)


# ------------------------------------------- certificate-producing evaluator
# Mirror of `evalTMHullFill2D` (CertTMDiv2), returning
#   (M, loa, ps', reported, entries, salv)
# `reported` = the probe's triple list (successes only, in traversal order);
# `entries`  = one triple per consumed sqrt cert, in queue order (fallback
#              positions carry the placeholder (0,0,0)), i.e. exactly the list
#              to bake into `TMParams.sqrtCerts`.
PLACEHOLDER = (0, 0, 0)


def evalFill2D(ast, box, ps, ctx=None):
    if ctx is None:
        ctx = (boxCenter(box), boxW(box))
    y, w = ctx
    op, args = ast
    n_sq, n_iv, n_tr = ps
    if op == ".const":
        d = _const(args)
        return (constTM(ctx, d), loaLower((d, d)), ps, [], [], 0)
    if op == ".var":
        k = _i(args[0])
        return (varTM(ctx, k), loaLower(box[k]), ps, [], [], 0)
    if op == ".neg":
        r = evalFill2D(args[0], box, ps, ctx)
        if r is None:
            return None
        return (mneg(r[0]), r[1], r[2], r[3], r[4], r[5])
    if op in (".add", ".sub", ".mul"):
        a = evalFill2D(args[0], box, ps, ctx)
        if a is None:
            return None
        b = evalFill2D(args[1], box, a[2], ctx)
        if b is None:
            return None
        if op == ".add":
            Mres, loa = madd(a[0], b[0]), ZERO
        elif op == ".sub":
            Mres, loa = msub(a[0], b[0]), ZERO
        else:
            Mres, loa = mmul(a[0], b[0]), ZERO
        return (Mres, loa, b[2], a[3] + b[3], a[4] + b[4], a[5] + b[5])
    if op == ".div":
        a = evalFill2D(args[0], box, ps, ctx)
        if a is None:
            return None
        b = evalFill2D(args[1], box, a[2], ctx)
        if b is None:
            return None
        if b[2][1] <= 0:
            return None
        ps2 = (b[2][0], b[2][1] - 1, b[2][2])
        Mi = minv(b[0], -80, -80, -80)
        if Mi is not None:
            return (mmul(a[0], Mi), ZERO, ps2,
                    a[3] + b[3], a[4] + b[4], a[5] + b[5])
        if isPos(b[1]):
            Mi = invCore(b[0], b[1], -80, -80, -80)
            if Mi is not None:
                return (mmul(a[0], Mi), ZERO, ps2,
                        a[3] + b[3], a[4] + b[4], a[5] + b[5] + 1)
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps2,
                a[3] + b[3], a[4] + b[4], a[5] + b[5])
    if op == ".sqrt":
        a = evalFill2D(args[0], box, ps, ctx)
        if a is None:
            return None
        if a[2][0] <= 0:
            return None
        ps1 = (a[2][0] - 1, a[2][1], a[2][2])
        M0 = a[0]
        c = sub(M0.fB[0], W(M0))
        res = None
        if isPos(c):
            sl = sqrtMantissaRel(M0.fB[0])
            sh = sqrtMantissaRel(M0.fB[1])
            sc = sqrtMantissaRel(c)
            res = msqrt(M0, sl, sh, sc, -80, -80)
            if res is None:
                raise AssertionError("sqrt TM must succeed when c > 0")
        if res is not None:
            Mres, Jc = res
            return (Mres, Jc[0], ps1, a[3] + [(sl, sh, sc)],
                    a[4] + [(sl, sh, sc)], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps1,
                a[3], a[4] + [PLACEHOLDER], a[5])
    if op == ".trans":
        if is_closed(args[1]):
            I = ieval(ast, box)
            if I is None:
                return None
            return (closedTM(ctx, I), loaLower(I), ps, [], [], 0)
        a = evalFill2D(args[1], box, ps, ctx)
        if a is None:
            return None
        if a[2][2] <= 0:
            return None
        ps1 = (a[2][0], a[2][1], a[2][2] - 1)
        Mt = mtrans(args[0], a[0], _i(args[2]), _i(args[3]), -80, -80)
        if Mt is not None:
            return (Mt, ZERO, ps1, a[3], a[4], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps1, a[3], a[4], a[5])
    if op == ".abs":
        a = evalFill2D(args[0], box, ps, ctx)
        if a is not None:
            vr = valueRange(a[0])
            if isNN(vr[0]):
                return (a[0], loaLower(vr), a[2], a[3], a[4], a[5])
            if isNeg(vr[1]):
                return (mneg(a[0]), loaLower(vr), a[2], a[3], a[4], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        # the failed sub-evaluation is discarded: original ps and no triples
        return (fallbackTM(ctx, I), loaLower(I), ps, [], [], 0)
    if op == ".ite":
        C = evalIParams(args[0], box, ps)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = evalFill2D(args[1], box, C[1], ctx)
            if r is None:
                return None
            return (r[0], r[1], r[2], C[2] + r[3], C[2] + r[4], r[5])
        if isNN(C[0][0]):
            r = evalFill2D(args[2], box, C[1], ctx)
            if r is None:
                return None
            return (r[0], r[1], r[2], C[2] + r[3], C[2] + r[4], r[5])
        t = evalFill2D(args[1], box, C[1], ctx)
        if t is None:
            return None
        e = evalFill2D(args[2], box, t[2], ctx)
        if e is None:
            return None
        return (iteHullTM2(t[0], e[0]), dmin(t[1], e[1]), e[2],
                C[2] + t[3] + e[3], C[2] + t[4] + e[4], t[5] + e[5])
    raise ValueError(op)


# ------------------------------------------ kernel consumer (evalTMHullD2C)
# The kernel eats `sqrtCerts` positionally; `_evalCq`/`_guard` below carry the
# queue explicitly so a generated list can be replayed exactly.  `checkPosTMHullC`
# is `checkPosTMHullC e box ps` from CertTM (box wf && eval succeeds && lb > 0).
def checkPosTMHullC(ast, box, params):
    """Kernel replay oracle for `checkPosTMHullC` with a generated params
    dict {"sqrt": [(slo,shi,sc), ...], "inv": n, "trans": n}."""
    if not all(ble(lo, hi) for lo, hi in box):
        return False
    r = _evalCq(ast, box, list(params["sqrt"]), 0,
                params["inv"], params["trans"], (boxCenter(box), boxW(box)))
    if r is None:
        return False
    return isPos(loBound(r[0], box))


def _evalCq(ast, box, q, i, n_iv, n_tr, ctx):
    """evalTMHullD2C with a positional sqrt-triple queue `q`/`i`."""
    op, args = ast
    if op == ".const":
        return (constTM(ctx, _const(args)), i, n_iv, n_tr)
    if op == ".var":
        return (varTM(ctx, _i(args[0])), i, n_iv, n_tr)
    if op == ".neg":
        r = _evalCq(args[0], box, q, i, n_iv, n_tr, ctx)
        return None if r is None else (mneg(r[0]), r[1], r[2], r[3])
    if op in (".add", ".sub", ".mul"):
        a = _evalCq(args[0], box, q, i, n_iv, n_tr, ctx)
        if a is None:
            return None
        b = _evalCq(args[1], box, q, a[1], a[2], a[3], ctx)
        if b is None:
            return None
        if op == ".add":
            return (madd(a[0], b[0]), b[1], b[2], b[3])
        if op == ".sub":
            return (msub(a[0], b[0]), b[1], b[2], b[3])
        return (mmul(a[0], b[0]), b[1], b[2], b[3])
    if op == ".div":
        a = _evalCq(args[0], box, q, i, n_iv, n_tr, ctx)
        if a is None:
            return None
        b = _evalCq(args[1], box, q, a[1], a[2], a[3], ctx)
        if b is None:
            return None
        if b[3] <= 0:
            return None
        Mi = minv(b[0], -80, -80, -80)
        if Mi is not None:
            return (mmul(a[0], Mi), b[1], b[2], b[3] - 1)
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), b[1], b[2], b[3] - 1)
    if op == ".sqrt":
        a = _evalCq(args[0], box, q, i, n_iv, n_tr, ctx)
        if a is None:
            return None
        if a[1] >= len(q):
            return None
        t = q[a[1]]
        res = msqrt(a[0], t[0], t[1], t[2], -80, -80)
        if res is not None:
            return (res[0], a[1] + 1, a[2], a[3])
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), a[1] + 1, a[2], a[3])
    if op == ".trans":
        if is_closed(args[1]):
            I = ieval(ast, box)
            return None if I is None else (closedTM(ctx, I), i, n_iv, n_tr)
        a = _evalCq(args[1], box, q, i, n_iv, n_tr, ctx)
        if a is None:
            return None
        if a[3] <= 0:
            return None
        Mt = mtrans(args[0], a[0], _i(args[2]), _i(args[3]), -80, -80)
        if Mt is not None:
            return (Mt, a[1], a[2], a[3] - 1)
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), a[1], a[2], a[3] - 1)
    if op == ".abs":
        a = _evalCq(args[0], box, q, i, n_iv, n_tr, ctx)
        if a is not None:
            vr = valueRange(a[0])
            if isNN(vr[0]):
                return (a[0], a[1], a[2], a[3])
            if isNeg(vr[1]):
                return (mneg(a[0]), a[1], a[2], a[3])
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), i, n_iv, n_tr)
    if op == ".ite":
        # guard: same positional sqrt queue
        C = _guard(ast_guard=args[0], box=box, q=q, st=(i, n_iv, n_tr))
        if C is None:
            return None
        (I, i1, iv1, tr1) = C
        if isNeg(I[1]):
            return _evalCq(args[1], box, q, i1, iv1, tr1, ctx)
        if isNN(I[0]):
            return _evalCq(args[2], box, q, i1, iv1, tr1, ctx)
        t = _evalCq(args[1], box, q, i1, iv1, tr1, ctx)
        if t is None:
            return None
        e = _evalCq(args[2], box, q, t[1], t[2], t[3], ctx)
        if e is None:
            return None
        return (iteHullTM2(t[0], e[0]), e[1], e[2], e[3])
    raise ValueError(op)


def _guard(ast_guard, box, q, st):
    """evalIParams with the positional sqrt queue (kernel consumer)."""
    i, n_iv, n_tr = st
    op, args = ast_guard
    if op == ".const":
        d = _const(args)
        return ((d, d), i, n_iv, n_tr)
    if op == ".var":
        return (box[_i(args[0])], i, n_iv, n_tr)
    if op == ".neg":
        r = _guard(args[0], box, q, st)
        return None if r is None else (ineg(r[0]), r[1], r[2], r[3])
    if op == ".abs":
        r = _guard(args[0], box, q, st)
        return None if r is None else (iabs(r[0]), r[1], r[2], r[3])
    if op in (".add", ".sub", ".mul"):
        a = _guard(args[0], box, q, st)
        if a is None:
            return None
        b = _guard(args[1], box, q, (a[1], a[2], a[3]))
        if b is None:
            return None
        if op == ".add":
            I = iadd(a[0], b[0])
        elif op == ".sub":
            I = isub(a[0], b[0])
        else:
            I = imul(a[0], b[0])
        return (I, b[1], b[2], b[3])
    if op == ".div":
        a = _guard(args[0], box, q, st)
        if a is None:
            return None
        b = _guard(args[1], box, q, (a[1], a[2], a[3]))
        if b is None:
            return None
        I = idiv(a[0], b[0], _i(args[2]))
        return None if I is None else (I, b[1], b[2], b[3])
    if op == ".sqrt":
        if i >= len(q):
            return None
        t = q[i]
        a = _guard(args[0], box, q, st)
        if a is None:
            return None
        I = a[0]
        if isNeg(I[1]):
            return None
        Jh = sqrtI(I[1], t[1])
        if Jh is None:
            return None
        if isNN(I[0]):
            Jl = sqrtI(I[0], t[0])
            if Jl is None:
                return None
            L = Jl[0]
        else:
            L = ZERO
        return ((L, Jh[1]), i + 1, n_iv, n_tr)
    if op == ".trans":
        v = _guard(args[1], box, q, st)
        if v is None:
            return None
        I = transOn(args[0], v[0], _i(args[2]), _i(args[3]))
        return None if I is None else (I, v[1], v[2], v[3])
    if op == ".ite":
        C = _guard(args[0], box, q, st)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = _guard(args[1], box, q, (C[1], C[2], C[3]))
            return None if r is None else (r[0], r[1], r[2], r[3])
        if isNN(C[0][0]):
            r = _guard(args[2], box, q, (C[1], C[2], C[3]))
            return None if r is None else (r[0], r[1], r[2], r[3])
        t = _guard(args[1], box, q, (C[1], C[2], C[3]))
        if t is None:
            return None
        e = _guard(args[2], box, q, (t[1], t[2], t[3]))
        if e is None:
            return None
        return (ihull(t[0], e[0]), e[1], e[2], e[3])
    raise ValueError(op)


# ------------------------------------------------------- failure attribution
def blame_path(ast, box, caps):
    """Heuristic blame for a failed `evalFill2D`: the deepest subtree that
    already fails when evaluated in isolation (same box, full template), in
    the evaluator's own visit order (guard before branches).  When all
    subtrees evaluate, the failure is node-local (TM rule gate / interval
    fallback) and the node's own path is returned with tag "node-level".

    Returns (path, reason) with `path` a list of `op[index]` steps.
    """
    ctx = (boxCenter(box), boxW(box))

    def ok(node):
        return evalFill2D(node, box, caps, ctx) is not None

    def walk(node, path):
        op, args = node
        if op in (".const", ".var"):
            return (path + [op], "leaf interval failed")
        if op in (".neg", ".abs", ".sqrt"):
            kids = [0]
        elif op in (".trans",):
            if is_closed(args[1]):
                return (path + ["%s(closed)" % op], "closed-node eval failed")
            kids = [1]
        elif op == ".ite":
            g = args[0]
            if not ok(g):
                return walk(g, path + ["ite[0:guard]"])
            C = evalIParams(g, box, caps)
            if C is None:
                return (path + ["ite[0:guard]"], "guard failed (context)")
            if isNeg(C[0][1]):
                return walk(args[1], path + ["ite[1:then]"])
            if isNN(C[0][0]):
                return walk(args[2], path + ["ite[2:else]"])
            if not ok(args[1]):
                return walk(args[1], path + ["ite[1:then]"])
            if not ok(args[2]):
                return walk(args[2], path + ["ite[2:else]"])
            return (path + ["ite"], "ite-hull node failed")
        else:
            kids = [0, 1]
        for k in kids:
            if isinstance(args[k], tuple) and not ok(args[k]):
                return walk(args[k], path + ["%s[%d]" % (op, k)])
        return (path + [op], "node-level rule/fallback failure")

    if ok(ast):
        return ([], "no failure")
    return walk(ast, [])

# ------------------------------------------------ Rule P (point-anchored)
# Mirrors `iteHullTM2P` / `evalPointTM` / `evalTMHullD2P` / `checkPosTMHullP`
# (CertTM, opt-in 2026-11-15).  All arithmetic is the same integer replica;
# the point rung `R` replaces the AST rung at every `trans` node in the point
# path only.
def iteHullTM2P(Pt, Pe, Mt, Me):
    """`iteHullTM2P Pt Pe Mt Me`: `fB = Pt.hull Pe`, point jump."""
    return M(Mt.y, Mt.w, ihull(Pt, Pe),
             [ihull(Mt.dfB[i], Me.dfB[i]) for i in range(len(Mt.y))],
             dmax(add(dmax(Mt.err, Me.err), jumpBound(Pt, Pe)), ZERO))


def pbox_of(box):
    """The degenerate center box `i ↦ [mid_i, mid_i]`."""
    return [(c, c) for c in boxCenter(box)]


# ---------------------------------------------------------------------------
# Rule P point-path cost levers (mirror of `CertTM`: `twoPi4D` / `rungOf` /
# `arctanIP*` / `transOnP`).  Point path only: `evalPointFill` below dispatches
# `trans` through `transOnP`; the landed main-box `transOn` is untouched, so
# `evalFill2D`/`checkPosTMHullC` stay bit-identical.
# ---------------------------------------------------------------------------

TWO_PI4D = (mul((2, 0), PI4D[0]), mul((2, 0), PI4D[1]))

# (threshold t, series order N): `|x| ≤ t ⇒ N`; the alternating remainder
# `t^(2N+1)/(2N+1)` is ≤ 1e-13 on every row (see CertTM `rungOf`).
RUNG_TABLE = (
    ((1, -1), 32),      # 1/2
    ((3, -2), 64),      # 3/4
    ((7, -3), 128),     # 7/8
    ((15, -4), 256),    # 15/16
    ((31, -5), 512),    # 31/32
    ((63, -6), 1024),   # 63/64
    ((127, -7), 2048),  # 127/128
)


def withinRung(I, t):
    """`withinRung I t`: `-t ≤ I.lo ∧ I.hi ≤ t`."""
    return ble(neg(t), I[0]) and ble(I[1], t)


def rungOf(I, R):
    """`rungOf I R`: adaptive series order from the certified interval."""
    for t, n in RUNG_TABLE:
        if withinRung(I, t):
            return min(R, n)
    return R


def clampR(Rr):
    """`clampR Rr = ⟨dmax Rr.lo 0, dmin Rr.hi 1⟩`."""
    return (dmax(Rr[0], ZERO), dmin(Rr[1], (1, 0)))


def arctanIBaseP(J, R, out):
    """`arctanIBaseP J R out` (adaptive rung)."""
    if ble((-1, 0), J[0]) and ble(J[1], (1, 0)):
        N = rungOf(J, R)
        L = arctanPoint(J[0], N, out)
        if L is None:
            return None
        H = arctanPoint(J[1], N, out)
        if H is None:
            return None
        return (L[0], H[1])
    return None


def arctanIPosAuxP(Rr, R, out):
    """`arctanIPosAuxP Rr R out`: `twoPi4D - [arctan R.lo, arctan R.hi]`."""
    N = rungOf(clampR(Rr), R)
    L = arctanPoint(dmax(Rr[0], ZERO), N, out)
    if L is None:
        return None
    H = arctanPoint(dmin(Rr[1], (1, 0)), N, out)
    if H is None:
        return None
    return isub(TWO_PI4D, (L[0], H[1]))


def arctanIPosP(J, R, out):
    """`arctanIPosP J R out`."""
    if ble((1, 0), J[0]):
        Rr = irecip(J, out)
        return None if Rr is None else arctanIPosAuxP(Rr, R, out)
    return None


def arctanINegP(J, R, out):
    """`arctanINegP J R out`."""
    if ble(J[1], (-1, 0)):
        L = arctanIPosP(ineg(J), R, out)
        return None if L is None else ineg(L)
    return None


ONE_D = ((1, 0), (1, 0))


def arctanINearP(J, R, out):
    """`arctanINearP`: on `J ⊆ [1/2, 2]`, `arctan y = pi4D + arctan ((y-1)/(y+1))`."""
    if ble((1, -1), J[0]) and ble(J[1], (2, 0)):
        T = idiv(isub(J, ONE_D), iadd(J, ONE_D), out)
        if T is None:
            return None
        K0 = arctanIBaseP(T, R, out)
        if K0 is None:
            return None
        return (add(PI4D[0], K0[0]), add(PI4D[1], K0[1]))
    return None


def arctanINearNegP(J, R, out):
    """`arctanINearNegP`: odd symmetry of `arctanINearP` on `J ⊆ [-2, -1/2]`."""
    if ble((-2, 0), J[0]) and ble(J[1], (-1, -1)):
        L = arctanINearP(ineg(J), R, out)
        return None if L is None else ineg(L)
    return None


def arctanIP(J, R, out):
    """`arctanIP J R out`: near-1 (pi/4 reduction) / point branches with
    adaptive rung; crossing intervals fall back to the landed `arctanI`."""
    if ble((1, -1), J[0]) and ble(J[1], (2, 0)):
        return arctanINearP(J, R, out)
    if ble((-2, 0), J[0]) and ble(J[1], (-1, -1)):
        return arctanINearNegP(J, R, out)
    if ble((-1, 0), J[0]) and ble(J[1], (1, 0)):
        return arctanIBaseP(J, R, out)
    if ble((1, 0), J[0]):
        return arctanIPosP(J, R, out)
    if ble(J[1], (-1, 0)):
        return arctanINegP(J, R, out)
    return arctanI(J, R, out)


def transOnP(kind, I, N, out):
    """`transOnP`: `transOn` with `arctan` routed through `arctanIP`."""
    if kind == ".atan1K":
        if I[0] == (1, 0) and I[1] == (1, 0):
            return PI4D
        return arctanIP(I, N, out)
    if kind == ".arctanK":
        return arctanIP(I, N, out)
    return transOn(kind, I, N, out)


def evalPointFill(ast, pbox, R):
    """Mirror of `evalPointTM R pbox`: returns `(I, triples)` where the
    triples are `(slo, shi, 0)` in consumption order (computed mantissas)."""
    op, args = ast
    if op == ".const":
        d = _const(args)
        return ((d, d), [])
    if op == ".var":
        return (pbox[_i(args[0])], [])
    if op == ".neg":
        r = evalPointFill(args[0], pbox, R)
        return None if r is None else (ineg(r[0]), r[1])
    if op == ".abs":
        r = evalPointFill(args[0], pbox, R)
        return None if r is None else (iabs(r[0]), r[1])
    if op in (".add", ".sub", ".mul"):
        a = evalPointFill(args[0], pbox, R)
        if a is None:
            return None
        b = evalPointFill(args[1], pbox, R)
        if b is None:
            return None
        if op == ".add":
            I = iadd(a[0], b[0])
        elif op == ".sub":
            I = isub(a[0], b[0])
        else:
            I = imul(a[0], b[0])
        return (I, a[1] + b[1])
    if op == ".div":
        a = evalPointFill(args[0], pbox, R)
        if a is None:
            return None
        b = evalPointFill(args[1], pbox, R)
        if b is None:
            return None
        I = idiv(a[0], b[0], _i(args[2]))
        return None if I is None else (I, a[1] + b[1])
    if op == ".sqrt":
        a = evalPointFill(args[0], pbox, R)
        if a is None:
            return None
        I = a[0]
        if isNeg(I[1]):
            return None
        slo = sqrtMantissa(I[0])
        shi = sqrtMantissa(I[1])
        Jh = sqrtI(I[1], shi)
        if Jh is None:
            return None
        if isNN(I[0]):
            Jl = sqrtI(I[0], slo)
            if Jl is None:
                return None
            L = Jl[0]
        else:
            L = ZERO
        return ((L, Jh[1]), a[1] + [(slo, shi, 0)])
    if op == ".trans":
        v = evalPointFill(args[1], pbox, R)
        if v is None:
            return None
        I = transOnP(args[0], v[0], R, _i(args[3]))
        return None if I is None else (I, v[1])
    if op == ".ite":
        C = evalPointFill(args[0], pbox, R)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = evalPointFill(args[1], pbox, R)
            return None if r is None else (r[0], C[1] + r[1])
        if isNN(C[0][0]):
            r = evalPointFill(args[2], pbox, R)
            return None if r is None else (r[0], C[1] + r[1])
        t = evalPointFill(args[1], pbox, R)
        if t is None:
            return None
        e = evalPointFill(args[2], pbox, R)
        if e is None:
            return None
        return (ihull(t[0], e[0]), C[1] + t[1] + e[1])
    raise ValueError(op)


def evalFill2DP(ast, box, ps, R, ctx=None):
    """Mirror of `evalTMHullD2P R box`.

    Returns `(M, loa, ps', main_entries, point_entries, salv)`:
    `main_entries` = one `(slo, shi, sc)` per consumed base sqrt cert (the
    `TMParams.sqrtCerts` to bake in); `point_entries` = one `(slo, shi, 0)`
    per consumed point cert (the `TMParamsP.pointCerts` to bake in)."""
    if ctx is None:
        ctx = (boxCenter(box), boxW(box))
    y, w = ctx
    op, args = ast
    n_sq, n_iv, n_tr = ps
    if op == ".const":
        d = _const(args)
        return (constTM(ctx, d), loaLower((d, d)), ps, [], [], 0)
    if op == ".var":
        k = _i(args[0])
        return (varTM(ctx, k), loaLower(box[k]), ps, [], [], 0)
    if op == ".neg":
        r = evalFill2DP(args[0], box, ps, R, ctx)
        if r is None:
            return None
        return (mneg(r[0]), r[1], r[2], r[3], r[4], r[5])
    if op in (".add", ".sub", ".mul"):
        a = evalFill2DP(args[0], box, ps, R, ctx)
        if a is None:
            return None
        b = evalFill2DP(args[1], box, a[2], R, ctx)
        if b is None:
            return None
        if op == ".add":
            Mres, loa = madd(a[0], b[0]), ZERO
        elif op == ".sub":
            Mres, loa = msub(a[0], b[0]), ZERO
        else:
            Mres, loa = mmul(a[0], b[0]), ZERO
        return (Mres, loa, b[2], a[3] + b[3], a[4] + b[4], a[5] + b[5])
    if op == ".div":
        a = evalFill2DP(args[0], box, ps, R, ctx)
        if a is None:
            return None
        b = evalFill2DP(args[1], box, a[2], R, ctx)
        if b is None:
            return None
        if b[2][1] <= 0:
            return None
        ps2 = (b[2][0], b[2][1] - 1, b[2][2])
        Mi = minv(b[0], -80, -80, -80)
        if Mi is not None:
            return (mmul(a[0], Mi), ZERO, ps2,
                    a[3] + b[3], a[4] + b[4], a[5] + b[5])
        if isPos(b[1]):
            Mi = invCore(b[0], b[1], -80, -80, -80)
            if Mi is not None:
                return (mmul(a[0], Mi), ZERO, ps2,
                        a[3] + b[3], a[4] + b[4], a[5] + b[5] + 1)
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps2,
                a[3] + b[3], a[4] + b[4], a[5] + b[5])
    if op == ".sqrt":
        a = evalFill2DP(args[0], box, ps, R, ctx)
        if a is None:
            return None
        if a[2][0] <= 0:
            return None
        ps1 = (a[2][0] - 1, a[2][1], a[2][2])
        M0 = a[0]
        c = sub(M0.fB[0], W(M0))
        res = None
        if isPos(c):
            sl = sqrtMantissaRel(M0.fB[0])
            sh = sqrtMantissaRel(M0.fB[1])
            sc = sqrtMantissaRel(c)
            res = msqrt(M0, sl, sh, sc, -80, -80)
            if res is None:
                raise AssertionError("sqrt TM must succeed when c > 0")
        if res is not None:
            Mres, Jc = res
            return (Mres, Jc[0], ps1, a[3] + [(sl, sh, sc)], a[4], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps1,
                a[3] + [PLACEHOLDER], a[4], a[5])
    if op == ".trans":
        if is_closed(args[1]):
            I = ieval(ast, box)
            if I is None:
                return None
            return (closedTM(ctx, I), loaLower(I), ps, [], [], 0)
        a = evalFill2DP(args[1], box, ps, R, ctx)
        if a is None:
            return None
        if a[2][2] <= 0:
            return None
        ps1 = (a[2][0], a[2][1], a[2][2] - 1)
        Mt = mtrans(args[0], a[0], _i(args[2]), _i(args[3]), -80, -80)
        if Mt is not None:
            return (Mt, ZERO, ps1, a[3], a[4], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps1, a[3], a[4], a[5])
    if op == ".abs":
        a = evalFill2DP(args[0], box, ps, R, ctx)
        if a is not None:
            vr = valueRange(a[0])
            if isNN(vr[0]):
                return (a[0], loaLower(vr), a[2], a[3], a[4], a[5])
            if isNeg(vr[1]):
                return (mneg(a[0]), loaLower(vr), a[2], a[3], a[4], a[5])
        I = ieval(ast, box)
        if I is None:
            return None
        return (fallbackTM(ctx, I), loaLower(I), ps, [], [], 0)
    if op == ".ite":
        C = evalIParams(args[0], box, ps)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = evalFill2DP(args[1], box, C[1], R, ctx)
            if r is None:
                return None
            return (r[0], r[1], r[2], C[2] + r[3], r[4], r[5])
        if isNN(C[0][0]):
            r = evalFill2DP(args[2], box, C[1], R, ctx)
            if r is None:
                return None
            return (r[0], r[1], r[2], C[2] + r[3], r[4], r[5])
        t = evalFill2DP(args[1], box, C[1], R, ctx)
        if t is None:
            return None
        e = evalFill2DP(args[2], box, t[2], R, ctx)
        if e is None:
            return None
        pb = pbox_of(box)
        pt = evalPointFill(args[1], pb, R)
        if pt is None:
            return None
        pe = evalPointFill(args[2], pb, R)
        if pe is None:
            return None
        return (iteHullTM2P(pt[0], pe[0], t[0], e[0]), dmin(t[1], e[1]), e[2],
                C[2] + t[3] + e[3],
                t[4] + e[4] + pt[1] + pe[1],
                t[5] + e[5])
    raise ValueError(op)


# --------------------------------------- kernel consumer replay (Rule P)
def _evalPointCq(ast, pbox, pq, pi, R):
    """Positional replay of `evalPointTM` (kernel consumer order)."""
    op, args = ast
    if op == ".const":
        d = _const(args)
        return ((d, d), pi)
    if op == ".var":
        return (pbox[_i(args[0])], pi)
    if op == ".neg":
        r = _evalPointCq(args[0], pbox, pq, pi, R)
        return None if r is None else (ineg(r[0]), r[1])
    if op == ".abs":
        r = _evalPointCq(args[0], pbox, pq, pi, R)
        return None if r is None else (iabs(r[0]), r[1])
    if op in (".add", ".sub", ".mul"):
        a = _evalPointCq(args[0], pbox, pq, pi, R)
        if a is None:
            return None
        b = _evalPointCq(args[1], pbox, pq, a[1], R)
        if b is None:
            return None
        if op == ".add":
            return (iadd(a[0], b[0]), b[1])
        if op == ".sub":
            return (isub(a[0], b[0]), b[1])
        return (imul(a[0], b[0]), b[1])
    if op == ".div":
        a = _evalPointCq(args[0], pbox, pq, pi, R)
        if a is None:
            return None
        b = _evalPointCq(args[1], pbox, pq, a[1], R)
        if b is None:
            return None
        I = idiv(a[0], b[0], _i(args[2]))
        return None if I is None else (I, b[1])
    if op == ".sqrt":
        a = _evalPointCq(args[0], pbox, pq, pi, R)
        if a is None:
            return None
        if a[1] >= len(pq):
            return None
        t = pq[a[1]]
        I = a[0]
        if isNeg(I[1]):
            return None
        Jh = sqrtI(I[1], t[1])
        if Jh is None:
            return None
        if isNN(I[0]):
            Jl = sqrtI(I[0], t[0])
            if Jl is None:
                return None
            L = Jl[0]
        else:
            L = ZERO
        return ((L, Jh[1]), a[1] + 1)
    if op == ".trans":
        v = _evalPointCq(args[1], pbox, pq, pi, R)
        if v is None:
            return None
        I = transOnP(args[0], v[0], R, _i(args[3]))
        return None if I is None else (I, v[1])
    if op == ".ite":
        C = _evalPointCq(args[0], pbox, pq, pi, R)
        if C is None:
            return None
        if isNeg(C[0][1]):
            r = _evalPointCq(args[1], pbox, pq, C[1], R)
            return None if r is None else (r[0], r[1])
        if isNN(C[0][0]):
            r = _evalPointCq(args[2], pbox, pq, C[1], R)
            return None if r is None else (r[0], r[1])
        t = _evalPointCq(args[1], pbox, pq, C[1], R)
        if t is None:
            return None
        e = _evalPointCq(args[2], pbox, pq, t[1], R)
        if e is None:
            return None
        return (ihull(t[0], e[0]), e[1])
    raise ValueError(op)


def _evalCqP(ast, box, bq, bi, pq, pi, n_iv, n_tr, R, ctx):
    """Positional replay of `evalTMHullD2P` (base sqrt queue + point queue)."""
    op, args = ast
    if op == ".const":
        return (constTM(ctx, _const(args)), bi, pi, n_iv, n_tr)
    if op == ".var":
        return (varTM(ctx, _i(args[0])), bi, pi, n_iv, n_tr)
    if op == ".neg":
        r = _evalCqP(args[0], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        return None if r is None else (mneg(r[0]), r[1], r[2], r[3], r[4])
    if op in (".add", ".sub", ".mul"):
        a = _evalCqP(args[0], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        if a is None:
            return None
        b = _evalCqP(args[1], box, bq, a[1], pq, a[2], a[3], a[4], R, ctx)
        if b is None:
            return None
        if op == ".add":
            return (madd(a[0], b[0]), b[1], b[2], b[3], b[4])
        if op == ".sub":
            return (msub(a[0], b[0]), b[1], b[2], b[3], b[4])
        return (mmul(a[0], b[0]), b[1], b[2], b[3], b[4])
    if op == ".div":
        a = _evalCqP(args[0], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        if a is None:
            return None
        b = _evalCqP(args[1], box, bq, a[1], pq, a[2], a[3], a[4], R, ctx)
        if b is None:
            return None
        if b[4] <= 0:
            return None
        Mi = minv(b[0], -80, -80, -80)
        if Mi is not None:
            return (mmul(a[0], Mi), b[1], b[2], b[3], b[4] - 1)
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), b[1], b[2], b[3],
                                       b[4] - 1)
    if op == ".sqrt":
        a = _evalCqP(args[0], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        if a is None:
            return None
        if a[1] >= len(bq):
            return None
        t = bq[a[1]]
        res = msqrt(a[0], t[0], t[1], t[2], -80, -80)
        if res is not None:
            return (res[0], a[1] + 1, a[2], a[3], a[4])
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), a[1] + 1, a[2],
                                       a[3], a[4])
    if op == ".trans":
        if is_closed(args[1]):
            I = ieval(ast, box)
            return None if I is None else (closedTM(ctx, I), bi, pi, n_iv, n_tr)
        a = _evalCqP(args[1], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        if a is None:
            return None
        if a[4] <= 0:
            return None
        Mt = mtrans(args[0], a[0], _i(args[2]), _i(args[3]), -80, -80)
        if Mt is not None:
            return (Mt, a[1], a[2], a[3], a[4] - 1)
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), a[1], a[2], a[3],
                                       a[4] - 1)
    if op == ".abs":
        a = _evalCqP(args[0], box, bq, bi, pq, pi, n_iv, n_tr, R, ctx)
        if a is not None:
            vr = valueRange(a[0])
            if isNN(vr[0]):
                return (a[0], a[1], a[2], a[3], a[4])
            if isNeg(vr[1]):
                return (mneg(a[0]), a[1], a[2], a[3], a[4])
        I = ieval(ast, box)
        return None if I is None else (fallbackTM(ctx, I), bi, pi, n_iv, n_tr)
    if op == ".ite":
        C = _guard(ast_guard=args[0], box=box, q=bq, st=(bi, n_iv, n_tr))
        if C is None:
            return None
        (I, bi1, iv1, tr1) = C
        if isNeg(I[1]):
            return _evalCqP(args[1], box, bq, bi1, pq, pi, iv1, tr1, R, ctx)
        if isNN(I[0]):
            return _evalCqP(args[2], box, bq, bi1, pq, pi, iv1, tr1, R, ctx)
        t = _evalCqP(args[1], box, bq, bi1, pq, pi, iv1, tr1, R, ctx)
        if t is None:
            return None
        e = _evalCqP(args[2], box, bq, t[1], pq, t[2], t[3], t[4], R, ctx)
        if e is None:
            return None
        pb = pbox_of(box)
        pt = _evalPointCq(args[1], pb, pq, e[2], R)
        if pt is None:
            return None
        pe = _evalPointCq(args[2], pb, pq, pt[1], R)
        if pe is None:
            return None
        return (iteHullTM2P(pt[0], pe[0], t[0], e[0]), e[1], pe[1], e[3], e[4])
    raise ValueError(op)


def checkPosTMHullP(ast, box, params, R):
    """Kernel replay oracle for `checkPosTMHullP R e box ps` with a generated
    params dict {"sqrt": [...], "inv": n, "trans": n, "point": [...]}."""
    if not all(ble(lo, hi) for lo, hi in box):
        return False
    r = _evalCqP(ast, box, list(params["sqrt"]), 0, list(params["point"]), 0,
                 params["inv"], params["trans"], R,
                 (boxCenter(box), boxW(box)))
    if r is None:
        return False
    return isPos(loBound(r[0], box))
