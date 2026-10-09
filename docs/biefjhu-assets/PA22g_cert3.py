from fractions import Fraction as F
import math

# --- series majorant candidate: Qd(u) = sum_{n=0}^{7} d_n u^n + K u^8, K = d8*144/93
d = [F(1)]
for n in range(1, 30):
    d.append(d[-1]*F(2*n-1, 2*n))
K = d[8]*F(144,93)
print("d8 =", d[8], " K =", K, "=", float(K))

def Qd(u):
    s = F(0)
    for n in range(8):
        s += d[n]*u**n
    return s + K*u**8

# E(u) = Qd^2 (1-u) - 1 ; check >= 0 on [0, 3/8]
for u in [F(0), F(1,8), F(1,4), F(3,8)]:
    E = Qd(u)*Qd(u)*(1-u)-1
    print(f"E({u}) = {E}  ({float(E):.3e})")

# polyrith-style: expand E as polynomial in u
import collections
def padd(a, b):
    r = collections.defaultdict(F)
    for k, v in list(a.items())+list(b.items()): r[k] += v
    return {k: v for k, v in r.items() if v != 0}
def pmul(a, b):
    r = collections.defaultdict(F)
    for k1, v1 in a.items():
        for k2, v2 in b.items(): r[k1+k2] += v1*v2
    return {k: v for k, v in r.items() if v != 0}
Qd_poly = {n: d[n] for n in range(8)}
Qd_poly[8] = K
E_poly = pmul(pmul(Qd_poly, Qd_poly), {1: F(1), 0: F(-1)})
E_poly = padd(E_poly, {0: F(-1)})
print("E poly deg:", max(E_poly), " terms:", len(E_poly))

# LP feasibility of E >= 0 with atoms u^i, bounds u^i <= (3/8) u^{i-1} chain + u <= 3/8
# scipy linprog if available
try:
    from scipy.optimize import linprog
    n = 18  # atoms u^0..u^17
    c = [0.0]*n
    for k, v in E_poly.items(): c[k] = -float(v)   # minimize -E
    A = []; b = []
    for i in range(1, n):
        row = [0.0]*n; row[i] = 1.0; row[i-1] = -F(3,8)
        A.append([float(x) for x in row]); b.append(0.0)   # u^i <= 3/8 u^{i-1}
    row = [0.0]*n; row[0] = 1.0
    A.append([float(x) for x in row]); b.append(3/8)       # u <= 3/8
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)]*n, method="highs")
    print("LP min of -E:", res.fun, "=> E >= ", -res.fun)
except ImportError:
    print("no scipy")

# --- w4 final number: 8 * poly(6124/1e4) where poly(w) = sum c_n w^{2n+1} (c_n = d_n/(2n+1)), plus R
w = F(6124,10000)
poly = F(0)
for n in range(8):
    poly += (d[n]/(2*n+1))*w**(2*n+1)
R = (w/17)*d[8]*w**16*F(144,93)
A4 = 8*(poly+R)
print("8*asn-series-bound(6124/1e4) =", float(A4), "=", A4)
B4 = F(6283,1000) - F(591,1000) + F(331,10000)*4 - A4
print("B4 =", float(B4))
# 2-piece k=4 worst from before:
worst2pc = F(0)
# recompute quickly
C = F(2887,10000); LF = F(253,130); H0 = F(126,100); TAU1 = F(86603,100000)
def sqrt_ceil(x, den=10**6):
    n2 = x.numerator*den*den//x.denominator
    r = math.isqrt(n2)
    while F(r,den)**2 < x: r += 1
    return F(r,den)
sig4 = F(7072,10000)
tau = TAU1+C*F(1,10); phiT = sqrt_ceil(sig*0 if False else sig4*sig4/(1-(tau*sig4)**2))
r = sqrt_ceil(1-(F(11,10)/2)**2, 10**5)
kap = F(math.ceil(float(F(4331,10000)-F(11,10)/(8*r))*10**5), 10**5)
tau0 = tau+(H0-F(11,10))*kap; phiF = sqrt_ceil(sig4*sig4/(1-(tau0*sig4)**2))
hX1 = LF*(H0-F(11,10)) + F(1,10)*8*C*phiT
hX2b = F(1,10)*8*C*phiT + (H0-F(11,10))*8*kap*phiF
print(f"k4 2pc: hX1={float(hX1):.6f} hX2b={float(hX2b):.6f} vs B4={float(B4):.6f} slack={float(B4-max(hX1,hX2b)):.6f}")
