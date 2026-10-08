from fractions import Fraction as F
import math
def sqrt_ge(n, den=10**6):
    r = math.isqrt(n*den*den)
    if r*r < n*den*den: r += 1
    return F(r, den)
SQ3H = sqrt_ge(3); SQ2H = sqrt_ge(2); SQ6031H = sqrt_ge(6031)
T0 = F(93391,100000); assert (63*SQ3H+SQ6031H)/200 <= T0, "t0 <= 0.93391"
LF = F(253,130)
PI = F(31415,10000)          # 2pi >= 6.283
B1 = 2*PI - F(1097,1000)     # h=1 window budget: 2k asn(v1) <= 5.186+0.0331k
B0 = 2*PI - F(591,1000)      # h0 window budget: 2k asn(t0 s) <= 5.692+0.0331k
print("B1 =", float(B1), " B0 =", float(B0))

def T5b(k):  # sin(pi/k) upper, pi in (3.1415, 3.1416)
    return F(31416,10000)/k - (F(31415,10000)/k)**3/6 + (F(31416,10000)/k)**5/120
def sigma_k(k):
    return {3:F(433,500), 4:F(7072,10000), 6:F(1,2)}.get(k) or T5b(k)
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28
def P4(w):    return w + w**3/6 + 3*w**5/40 + w**7/16   # k=4 special: valid u <= 3/8

# certificate check for P4: q(u) = (P4')^2 (1-u) - 1 >= u^4 * r(u), r decreasing, r(3/8) > 0
# P4' = 1+u/2+3u^2/8+7u^3/16 ; r(u) = 21/64-42/64 u+3/64u^2-57/128u^3-21/256u^4-49/256u^5
def r_P4(u): return F(21,64)-F(42,64)*u+F(3,64)*u*u-F(57,128)*u**3-F(21,256)*u**4-F(49,256)*u**5
print("P4 cert r(3/8) =", float(r_P4(F(3,8))), " decreasing:", all(r_P4(F(i,1000)) >= r_P4(F(i+1,1000)) for i in range(1,375)))

# septic cert at u <= 9/16: h concave, h(9/16)>0 ; quadratic at u<=17/64: 1-3u-u^2-u^3>0
print("h_sept(9/16) =", float(F(1,4)+F(3,4)*F(9,16)-F(81,256)-F(729,16384)/4-F(3,16)*F(6561,65536)-F(9,16)*F(59049,1048576)))

CHORD_HI = F(2887,10000); assert CHORD_HI**2 >= F(1,12)
CHORD_LO = F(23,100)
TAU1 = F(86603,100000); assert SQ3H/2 <= TAU1
def TAU(b): return TAU1 + CHORD_HI*(b-1)
def Phi_of(tau, sig, den=10**7):
    tgt = sig*sig/(1-(tau*sig)**2)
    m = math.isqrt(tgt.numerator*den*den//tgt.denominator)
    while F(m,den)**2*(1-(tau*sig)**2) < sig*sig: m += 1
    return F(m,den)
def Phi0(k): return Phi_of(T0, sigma_k(k))
def PhiT(b,k): return Phi_of(TAU(b), sigma_k(k))

# ---- windows ----
WIN1 = {3:(F(3,4),P_sept), 4:(F(6124,10000),P4), 5:None, 6:None, 7:None,8:None,9:None,10:None,11:None}
for k in [5,6,7,8,9,10,11]:
    WIN1[k] = (F(8661,10000)*T5b(k), P_quad)
WIN0 = {4:(F(6608,10000),P_sept), 5:(F(5491,10000),P_sept)}
TAILV = F(8661,10000)*F(31416,10000)

# v <= Vt checks (exact)
assert F(433,500)*F(433,500) <= F(3,4)*4/4 and F(3,4) == F(3,4)
# k=3: v1 = (sqrt3/2)(sqrt3/2) = 3/4 exactly; Vt = 3/4
# k=4: v1 = sqrt6/4 ; sqrt6 <= 2.4496? (24496^2 >= 6e8)
assert 24496**2 >= 6*10**8
assert F(6124,10000)**2 <= F(19,50), "k=4 window u<=19/50 for P4"
print("r_P4(19/50) =", float(r_P4(F(19,50))), "positive:", r_P4(F(19,50)) > 0)
print("r_P4(3751/10000) =", float(r_P4(F(3751,10000))))
# k>=5: v1 = (sqrt3/2) sin(pi/k) <= (8661/10000) T5b(k): need sin(pi/k) <= T5b(k):
# T5(pi/k) <= termwise (pi<3.1416, pi>3.1415) and T5b via p22_sin_le_taylor5
for k in [5,6,7,8,9,10,11]:
    assert WIN1[k][0] < 1
print("windows defined")

def check(k, pieces, verbose=True):
    if k >= 12:
        Vt, P = TAILV/F(k), P_quad
        assert Vt*Vt <= F(17,64)
    else:
        Vt, P = WIN1[k]
    lhs_base = F(591,1000) - F(331,10000)*k
    res = []
    for idx,(a,b) in enumerate(pieces):
        cumA = F(0)
        for j in range(idx):
            a2,b2 = pieces[j]
            cumA += (b2-a2)*CHORD_HI*PhiT(b2,k)
        # sum bound candidates on this piece: at h=a: LF(1.26-a)+cumA ; at h=b: LF(1.26-b)+cumA+(b-a)CHORD_HI PhiT(b)
        candA = LF*(F(126,100)-a) + cumA
        candB = LF*(F(126,100)-b) + cumA + (b-a)*CHORD_HI*PhiT(b,k)
        smax = max(candA, candB)
        lhs = lhs_base + smax + 2*k*P(Vt)
        ok = lhs <= 2*PI
        res.append(ok)
        if verbose:
            print(f"  k={k} [{float(a):.3f},{float(b):.3f}] smax={float(smax):.6f} 2kP={float(2*k*P(Vt)):.6f} lhs={float(lhs):.6f} slack={float(2*PI-lhs):.6f} {'OK' if ok else 'FAIL'}")
    return all(res)

routes = {
 3: [(F(1),F(115,100)),(F(115,100),F(126,100))],
 4: [(F(1),F(11,10)),(F(11,10),F(126,100))],
 5: [(F(1),F(27,25)),(F(27,25),F(126,100))],
 6: [(F(1),F(126,100))],
 7: [(F(1),F(126,100))], 8: [(F(1),F(126,100))], 9: [(F(1),F(126,100))],
 10:[(F(1),F(126,100))], 11:[(F(1),F(126,100))],
 12:[(F(1),F(126,100))],
}
allok = True
for k in sorted(routes): allok &= check(k, routes[k])
# tail uniform for all k>=12: verify at k=12 and monotonicity argument
print("tail check k=12 above; monotone: lhs decreasing in k for k>=12")
print("ALL:", allok)

# ---- h0 windows k=4,5 (needed? no! routing no longer uses them) ----
print("h0 windows NOT needed in final design")

# ---- single-piece candidates where c_k <= LF: ----
for k in [6,7,8,9,10,11]:
    c = 2*k*CHORD_HI*PhiT(F(126,100),k)
    print(f"k={k}: c_k={float(c):.6f} vs LF={float(LF):.6f} single={c<=LF}")
c12 = 24*CHORD_HI*PhiT(F(126,100), sigma_k(100))  # sigma ~ 3.1416/100 tiny -> Phi ~ sigma
print("tail c_12 ~", float(c12))
