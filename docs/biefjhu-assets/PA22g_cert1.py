from fractions import Fraction as F
import math

def sqrt_ceil(x, den=10**6):
    # smallest r with r >= sqrt(x), as Fraction r/den
    n = x.numerator * den * den // x.denominator
    r = math.isqrt(n)
    while F(r, den)**2 < x:
        r += 1
    return F(r, den)

def sqrt_floor(x, den=10**5):
    n = x.numerator * den * den // x.denominator
    r = math.isqrt(n)
    while F(r, den)**2 > x:
        r -= 1
    return F(r, den)

PI2 = 2*F(31416,10000)   # upper 2pi = 6.2832
PI2L = 2*F(31415,10000)  # lower 2pi = 6.283

def T5b(k):
    return F(31416,10000)/k - (F(31415,10000)/k)**3/6 + (F(31416,10000)/k)**5/120

def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28

def Phi(tau, sig, den=10**6):
    tgt = sig*sig/(1-(tau*sig)**2)
    return sqrt_ceil(tgt, den)

TAU1 = F(86603,100000)
C = F(2887,10000)
LF = F(253,130)
H0 = F(126,100)

def TAU(b): return TAU1 + C*(b-1)

print("=== basic constants ===")
print("sqrt3/2 <= 86603/1e5:", F(86603,100000)**2 >= F(3,4))
print("sqrt3/4 <= 4331/1e4:", F(4331,10000)**2 >= F(3,16))
print("T1 = sqrt3/2 ~", math.sqrt(3)/2, " tau1 = 0.86603")

print("\n=== sept majorant window check ===")
# Q = 1 + u/2 + u^2/2 + 3u^3/4 ; Q^2 (1-u) - 1 = u^2*(1/4 + 3u/4 - u^2 - u^3/4 - 3u^4/16 - 9u^5/16)
def sept_bracket(u):
    return F(1,4)+F(3,4)*u - u*u - u**3/4 - F(3,16)*u**4 - F(9,16)*u**5
for w2 in [F(9,16), F(7,10), F(19,25)]:
    print(f"  bracket at u={w2} = {float(sept_bracket(w2)):.6f}")
# identity check
import random
for _ in range(5):
    u = F(random.randint(1,60), 100)
    Q = 1+u/2+u*u/2+F(3,4)*u**3
    lhs = Q*Q*(1-u)-1
    rhs = u*u*sept_bracket(u)
    assert lhs == rhs, (u, lhs, rhs)
print("  sept hex identity OK")

print("\n=== quad majorant identity (window 17/64) ===")
def quad_bracket(u):
    return F(1,4) - F(3,4)*u - u*u/4 - u**3/4  # 1 + u^2*(1-3u-u^2-u^3)/4 - 1 = u^2*(...)/4
for _ in range(3):
    u = F(random.randint(1,60), 200)
    Q = 1+u/2+u*u/2
    assert Q*Q*(1-u)-1 == u*u*(1-3*u-u*u-u**3)/4
print("  quad hex identity OK; 3u+u^2+u^3 at 17/64:", float(3*F(17,64)+F(17,64)**2+F(17,64)**3))

print("\n=== w-windows (hwin): 2k*P(Vt) <= 5.186+0.0331k ===")
ok = True
# k=3: 6*P_sept(3/4)
v = 6*P_sept(F(3,4)); bud = F(5186,1000)+F(331,10000)*3
print(f"  k=3 : 6*P_sept(3/4) = {float(v):.6f} <= {float(bud):.6f} slack {float(bud-v):.6f} {v<=bud}"); ok &= v<=bud
# k=4: 8*P_sept(6124/1e4); check sqrt6/4 <= 6124/1e4
print("  sqrt6/4 <= 6124/1e4:", F(6124,10000)**2 >= F(6,16))
v = 8*P_sept(F(6124,10000)); bud = F(5186,1000)+F(331,10000)*4
print(f"  k=4 : 8*P_sept(6124/1e4) = {float(v):.6f} <= {float(bud):.6f} slack {float(bud-v):.6f} {v<=bud}"); ok &= v<=bud
for k in range(5,12):
    vt = F(8661,10000)*T5b(k)
    v = 2*k*P_quad(vt); bud = F(5186,1000)+F(331,10000)*k
    print(f"  k={k:2d}: 2k*P_quad(Vt) = {float(v):.6f} <= {float(bud):.6f} slack {float(bud-v):.6f} {v<=bud}"); ok &= v<=bud
print("  all hwin OK:", ok)

print("\n=== wtail (k>=12): 2k*asn(w0) <= 2Vt+2Vt^3/(3k^2)+Vt^5/(5k^4), Vt=TAILV ===")
VT = F(8661,10000)*F(31416,10000)
print("  Vt =", float(VT), " (Vt/12)^2 <= 17/64:", (VT/12)**2 <= F(17,64))
v = 2*VT + 2*VT**3/(3*144) + VT**5/(5*144**4)
print(f"  bound at k=12: {float(v):.6f} <= 5.186: {v <= F(5186,1000)}")

print("\n=== route1 packs k=7..11 (tau = 235273/250000) ===")
TAU_R1 = F(235273,250000)
for k in range(7,12):
    sig = T5b(k)
    phi = Phi(TAU_R1, sig)
    hphi = (1-(TAU_R1*sig)**2)*phi*phi >= sig*sig
    hq1 = TAU_R1*sig < 1
    mono = F(26,100)*(2*k*C*phi) <= F(506,1000)
    caseA = 2*k*C*phi <= LF
    print(f"  k={k:2d}: sig={float(sig):.6f} phi={float(phi):.6f} hphi={hphi} Q1={hq1} mono={mono} (0.26*2kCphi={float(F(26,100)*2*k*C*phi):.6f} vs 0.506) caseA={caseA}")

print("\n=== tail k>=12 (phi = 270126977/1e9) ===")
PHI12 = F(270126977,1000000000)
SIG12 = F(31416,10000)/12
print("  tail_phi at k=12:", (1-(TAU_R1*SIG12)**2)*PHI12**2 >= SIG12**2)
print("  tail Q1 (k=12):", TAU_R1*SIG12 < 1)
print("  tail_mono at k=12: 0.26*2*12*C*phi =", float(F(26,100)*24*C*PHI12), "<= 0.506:", F(26,100)*24*C*PHI12 <= F(506,1000))
print("  caseA at k=12: 2*12*C*phi <= 253/130:", 24*C*PHI12 <= LF)

print("\n=== route2 packs ===")
def sqrt3_4_floor(den=10**5):
    return sqrt_floor(F(3,16), den)  # r for chord: needs r >= sqrt(1-(b/2)^2) -> upper
def route2_pack(k, b, sig, label):
    bud = F(5186,1000)+F(331,10000)*k
    bud = PI2L - F(5186,1000) - F(331,10000)*k  # 2pi_lower - (5.186+0.0331k)
    tau = TAU(b)
    phiT = Phi(tau, sig)
    # chord r: upper bound of sqrt(1-(b/2)^2)
    r = sqrt_ceil(1-(b/2)**2, 10**5)
    # kappa >= sqrt3/4 - b/(8r)  (with sqrt3/4 <= 4331/1e4)
    kap_raw = F(4331,10000) - b/(8*r)
    kap = F(math.ceil(kap_raw*10**5), 10**5)
    tau0 = tau + (H0-b)*kap
    phiF = Phi(tau0, sig)
    hX1 = LF*(H0-b) + (b-1)*2*k*C*phiT
    hX2a = (b-1)*2*k*C*phiT + LF*(H0-b)
    hX2b = (b-1)*2*k*C*phiT + (H0-b)*2*k*kap*phiF
    ok = hX1<=bud and hX2a<=bud and hX2b<=bud
    print(f"  {label}: b={b} sig={float(sig):.6f} r={r} kap={kap} tau={float(tau):.7f} phiT={phiT} tau0={float(tau0):.7f} phiF={phiF}")
    print(f"      budget={float(bud):.6f} hX1={float(hX1):.6f} hX2a={float(hX2a):.6f} hX2b={float(hX2b):.6f} slack={float(bud-max(hX1,hX2a,hX2b)):.6f} ALL_OK={ok}")
    print(f"      Q1: tau*sig<1 = {tau*sig<1}, tau0*sig<1 = {tau0*sig<1}")
    return ok

allok = True
allok &= route2_pack(3, F(23,20), F(8661,10000), "k=3")
allok &= route2_pack(4, F(27,25), F(7072,10000), "k=4")
allok &= route2_pack(5, F(27,25), T5b(5), "k=5")
allok &= route2_pack(6, F(6,5),  F(1,2),    "k=6")
print("  route2 all OK:", allok)
