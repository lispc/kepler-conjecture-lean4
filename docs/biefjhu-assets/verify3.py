from fractions import Fraction as F
import math, decimal
decimal.getcontext().prec = 60
D = decimal.Decimal
pi_true = D("3.14159265358979323846264338327950288419716939937510")
def isqrt_ge(n):
    r = math.isqrt(n)
    if r*r < n: r += 1
    return r
def sqrt_iv(n, denom=10**6):
    return F(math.isqrt(n*denom*denom), denom), F(isqrt_ge(n*denom*denom), denom)
sq2 = sqrt_iv(2); sq3 = sqrt_iv(3)
sq2_hi, sq3_hi = sq2[1], sq3[1]
t0_hi = (63*sq3[1] + F(isqrt_ge(6031*10**12), 10**6))/200
def T5bar(k): return F(31416,10000)/k - (F(314,100)/k)**3/6 + (F(31416,10000)/k)**5/120
def sigma_k(k):
    if k == 3: return sq3_hi/2
    if k == 4: return sq2_hi/2
    if k == 6: return F(1,2)
    return T5bar(k)
def asn_ref(w):
    w = D(w); s = D(0)
    for n in range(0, 200):
        c = D(math.comb(2*n, n)) / (D(4)**n * D(2*n+1))
        t = c * w**(2*n+1)
        s += t
        if abs(t) < D("1e-28"): break
    return s
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28
c32 = F(8661,10000)
t0 = F(93391,100000)   # t0 <= 0.93391 (verified t0_hi = 0.9338936)
print("t0 <= 93391/1e5:", t0_hi <= t0)

# ---------- k >= 12 tail: v <= c32*(31416/10000)/k = 272097276/(1e8 k) ----------
num32 = F(272097276, 10**8)   # c32 * 3.1416
print("c32*3.1416 =", float(num32))
k = 12
Vt = num32/k
win = F(17,64)
print("tail: Vt(12)^2 =", float(Vt*Vt), "<= 17/64:", Vt*Vt <= win)
# s window: s <= sqrt(1 - v^2), v^2 <= Vt^2 ; pick s rational
s = F(9739,10000)
print("s^2 <= 1 - Vt(12)^2:", s*s <= 1 - Vt*Vt, float(1-Vt*Vt))
c = (1/s)/(1+s)   # coefficient s^{-1}/(1+s)
# hnum: 2k(Vt + c*Vt^3/3) <= 5.183 + 0.0331 k  for all k>=12; LHS = 2*num32 + 2*c*num32^3/(3 k^2) decreasing in k
lhs12 = 2*k*(Vt + c*Vt**3/3)
print("tail hnum at k=12:", float(lhs12), "budget", float(B12 := F(5183,1000)+F(331,10000)*12), "ok:", lhs12 <= B12)
# verify formula: 2k(Vt + c Vt^3/3) = 2 num32 + 2 c num32^3 /(3 k^2)
for k in [12, 13, 20, 100, 1000]:
    Vt = num32/F(k)
    lhs = 2*k*(Vt + c*Vt**3/3)
    print(f"  k={k}: {float(lhs):.6f} <= {float(F(5183,1000)+F(331,10000)*k):.6f}:", lhs <= F(5183,1000)+F(331,10000)*k)

# ---------- h0 windows k=4,5 ----------
# target: 0.591 - 0.0331k <= 2pi - 2k asn(t0 * sin(pi/k)); hnum: 2k P(Vt) <= 5.689 + 0.0331k
B0 = F(5689,1000)
print("\nB0 =", float(B0))
for k, Vt, major, win in [(4, F(6608,10000), P_sept, F(7,16)), (5, F(5491,10000), P_sept, F(7,16))]:
    sig = sigma_k(k)
    v = t0*sig
    assert v <= Vt, (k, float(v), float(Vt))
    assert Vt*Vt <= win, (k, float(Vt*Vt))
    P = major(Vt)
    lhs = 2*k*P
    budget = B0 + F(331,10000)*k
    # true margin
    w0 = D(str(float(pi_true)*math.sin(math.pi/k)))*D(str(float(t0_hi)))
    tm = float(2*pi_true - 2*k*asn_ref(w0) - D('0.591') + D('0.0331')*k)
    print(f"k={k} h0win: Vt={float(Vt)} v<={float(v):.6f} 2kP={float(lhs):.6f} budget={float(budget):.6f} ok={lhs<=budget} trueD0={tm:.5f}")
