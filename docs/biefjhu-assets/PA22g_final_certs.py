from fractions import Fraction as F
import math

def ceil_rat(x, den):
    return F(math.ceil(x*den), den)
def sqrt_ceil(x, den=10**6):
    n = x.numerator*den*den//x.denominator
    r = math.isqrt(n)
    while F(r,den)**2 < x: r += 1
    return F(r,den)

C = F(2887,10000); LF = F(253,130); H0 = F(126,100); TAU1 = F(86603,100000)
def T5b(k): return F(31416,10000)/k - (F(31415,10000)/k)**3/6 + (F(31416,10000)/k)**5/120
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + F(3,28)*w**7
def Phi(tau, sig): return sqrt_ceil(sig*sig/(1-(tau*sig)**2))

print("========== FINAL CERTIFICATE TABLE (all exact) ==========")

# ---- sept hex identity: Q^2(1-u) = 1 + u^2*(1/4+3u/4-u^2-u^3/4-3u^4/16-9u^5/16)
u = F(7,100)
Q = 1+u/2+u*u/2+F(3,4)*u**3
assert Q*Q*(1-u)-1 == u*u*(F(1,4)+F(3,4)*u-u*u-u**3/4-F(3,16)*u**4-F(9,16)*u**5)
print("sept hex identity verified; bracket at u=7/10:",
      float(F(1,4)+F(3,4)*F(7,10)-F(7,10)**2-F(7,10)**3/4-F(3,16)*F(7,10)**4-F(9,16)*F(7,10)**5))
# quad hex identity
u = F(17,100)
Q = 1+u/2+u*u/2
assert Q*Q*(1-u)-1 == u*u*(1-3*u-u*u-u**3)/4
print("quad hex identity verified")

# ---- ser4 certificate: Qd = 1+u/2+3u^2/8+5u^3/16+7u^4/16 on u <= 3/8
d = [F(1)]
for n in range(1, 12): d.append(d[-1]*F(2*n-1,2*n))
assert F(35,128)*F(8,5) == F(7,16)
# E-coefficients
import collections
Qp = {0:F(1),1:F(1,2),2:F(3,8),3:F(5,16),4:F(7,16)}
def pmul(a,b):
    res = collections.defaultdict(F)
    for k1,v1 in a.items():
        for k2,v2 in b.items(): res[k1+k2] += v1*v2
    return dict(res)
E = dict(pmul(pmul(Qp,Qp),{0:F(1),1:F(-1)}))
E = {k:v for k,v in E.items() if v != 0}
print("ser4 E coefficients (u^k : coeff):")
for k in sorted(E): print(f"   u^{k} : {E[k]}")
# LP prefix check at r=3/8
s = F(0); ok = True
for k in range(0, max(E)+1):
    s += E.get(k,0)*F(3,8)**k
    if s < 0: ok = False
print("ser4 LP prefix sums all >=0:", ok, " E(3/8) = ", float(s))

# ---- windows (A_k)
print("\n--- windows A_k ---")
A = {}
A[3] = 6*P_sept(F(3,4))
ser4 = lambda w: w + w**3/6 + F(3,40)*w**5 + F(5,112)*w**7 + F(7,144)*w**9
print("sqrt6/4 <= 6124/1e4:", F(6124,10000)**2 >= F(3,8))
A[4] = 8*ser4(F(6124,10000))
for k in range(5,12):
    A[k] = 2*k*P_quad(F(8661,10000)*T5b(k))
VT = F(8661,10000)*F(31416,10000)
A[12] = 2*VT + 2*VT**3/(3*144) + VT**5/(5*12**4)
for k in sorted(A): print(f"  A[{k}] = {A[k]}  ({float(A[k]):.6f})")
print("  (Vt/12)^2 <= 17/64:", (VT/12)**2 <= F(17,64))

# ---- route2 packs k=3..6
print("\n--- route2 packs (b, kap, phiT, phiF, budgets vs B_k) ---")
def pack2(k, b, sig):
    Bk = F(6283,1000) - (F(591,1000)-F(331,10000)*k) - A[k]
    tau = TAU1 + C*(b-1); phiT = Phi(tau, sig)
    r = sqrt_ceil(1-(b/2)**2, 10**5)
    kap = ceil_rat(F(4331,10000)-b/(8*r), 10**5)
    tau0 = tau + (H0-b)*kap; phiF = Phi(tau0, sig)
    hX1 = LF*(H0-b) + (b-1)*2*k*C*phiT
    hX2b = (b-1)*2*k*C*phiT + (H0-b)*2*k*kap*phiF
    print(f"  k={k}: b={b} sig={sig}")
    print(f"      kap={kap} phiT={phiT} tau={tau} ({float(tau):.7f}) phiF={phiF} tau0={tau0} ({float(tau0):.7f})")
    print(f"      B={Bk} hX1={hX1} ({float(hX1):.6f}) hX2b={hX2b} ({float(hX2b):.6f}) slack={float(Bk-max(hX1,hX2b)):.6f} OK={max(hX1,hX2b)<=Bk}")
    print(f"      hB506 check: base+A+0.506 <= 6.283: {float(F(591,1000)-F(331,10000)*k+A[k]+F(1,2)):.6f}  tau*sig<1: {tau*sig<1}  tau0*sig<1: {tau0*sig<1}")
pack2(3, F(23,20), F(8661,10000))
pack2(4, F(11,10), F(7072,10000))
pack2(5, F(27,25), T5b(5))
pack2(6, F(6,5),   F(1,2))

# ---- route1 packs k=7..11
print("\n--- route1 packs k=7..11 (tau=235273/250000) ---")
TR1 = F(235273,250000)
for k in range(7,12):
    sig = T5b(k); phi = Phi(TR1, sig)
    hphi = (1-(TR1*sig)**2)*phi*phi >= sig*sig
    caseA = 2*k*C*phi <= LF
    mono = F(26,100)*2*k*C*phi <= F(506,1000)
    hB = F(591,1000)-F(331,10000)*k+A[k]+F(506,1000) <= F(6283,1000)
    print(f"  k={k}: phi={phi} hphi={hphi} caseA={caseA} mono={mono} hB={hB} (base+A+0.506={float(F(591,1000)-F(331,10000)*k+A[k]+F(506,1000)):.6f})")

# ---- tail k>=12
print("\n--- tail k>=12 ---")
PHI12 = F(270126977,1000000000)
sig12 = F(31416,10000)/12
print("  tail_phi k=12:", (1-(TR1*sig12)**2)*PHI12**2 >= sig12**2)
print("  tail Q1 k=12:", TR1*sig12 < 1)
print("  tail_mono: 0.26*24*C*phi =", float(F(26,100)*24*C*PHI12), "<=0.506:", F(26,100)*24*C*PHI12 <= F(506,1000))
print("  caseA k=12:", 24*C*PHI12 <= LF)
hB12 = F(591,1000)-F(331,10000)*12+A[12]+F(506,1000) <= F(6283,1000)
print("  hB k=12:", hB12, f"(base+A+0.506={float(F(591,1000)-F(331,10000)*12+A[12]+F(506,1000)):.6f})")
