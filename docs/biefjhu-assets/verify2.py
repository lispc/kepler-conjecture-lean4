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
t1 = sq3_hi/2   # sqrt3/2 upper bound

def T5bar(k):  # sin(pi/k) upper bound, pi in (3.14, 3.1416)
    return F(31416,10000)/k - (F(314,100)/k)**3/6 + (F(31416,10000)/k)**5/120

def sigma_k(k):
    if k == 3: return sq3_hi/2
    if k == 4: return sq2_hi/2
    if k == 6: return F(1,2)
    return T5bar(k)

def sin_ref(k):
    return pi_true/k - (pi_true/k)**3/6 + (pi_true/k)**5/120 - (pi_true/k)**7/5040

# asn via series (reference, high precision)
def asn_ref(w):
    w = D(w); s = D(0); term = w
    n = 0
    while True:
        if n > 0:
            # term_n = C(2n,n)/(4^n (2n+1)) w^{2n+1}
            c = D(math.comb(2*n, n)) / (D(4)**n * D(2*n+1))
            term = c * w**(2*n+1)
        s += term
        if abs(term) < D("1e-30"): break
        n += 1
        if n > 200: break
    return s

# ---------- Septic majorant: asn w <= w + w^3/6 + w^5/10 + 3w^7/28, valid w^2 <= 9/16 (and up to 49/64?) ----------
# certificate g(u) = u^2*(1/4 + 3u/4 - u^2 - u^3/4 - 3u^4/16 - 9u^5/16), h(u) concave; check h >= 0 at endpoints
def h_septic(u):
    return F(1,4) + F(3,4)*u - u*u - F(1,4)*u**3 - F(3,16)*u**4 - F(9,16)*u**5
for u in [F(9,16), F(7,16)]:
    print("h_septic at", u, "=", float(h_septic(u)), ">=0:", h_septic(u) >= 0)

# ---------- quadratic majorant: asn w <= w + w^3/6 + w^5/10, valid 3u+u^2+u^3 <= 1 (u <= 17/64 OK) ----------
def cert_quad(u):
    return 1 - 3*u - u*u - u**3
print("cert_quad at 17/64:", float(cert_quad(F(17,64))))

def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28

# ---------- windows at h=1: v = (sqrt3/2) sin(pi/k), budget 2k*P(Vt) <= 5.183 + 0.0331*k ----------
# 5.183 = 6.28 - 1.097 ; also more precisely 2*pi >= 6.28 (p22_pi_lb presumably 3.14)
B1 = F(5183,1000)
c32 = F(8661,10000)
print("B1 =", float(B1))
print()
for k in range(3,12):
    sig = sigma_k(k)
    v_true = float(pi_true)*math.sin(math.pi/k)
    if k == 3: Vt = F(3,4); major = P_sept; win = F(9,16)
    elif k == 4: Vt = F(6124,10000); major = P_sept; win = F(7,16)  # sqrt6/4 <= 0.6124 (need 6e8 <= 24496^2)
    else:
        Vt = c32*T5bar(k); major = P_quad; win = F(17,64)
    assert Vt*Vt <= win, (k, float(Vt*Vt), float(win))
    assert Vt < 1
    # v_true <= Vt exact check: use rigorous sin upper = sigma, v <= c32*sig
    assert c32*sig <= Vt or k in (3,4), (k, float(c32*sig), float(Vt))
    # exact-sin checks: k=3 v=(sqrt3/2)^2=3/4; k=4 v=sqrt6/4 <= 6608/10000 iff 6 <= (2.6432)^2
    if k == 3: assert Vt == F(3,4)
    if k == 4: assert 6*10**8 <= 24496**2, "sqrt6/4 <= 0.6124" 
    P = major(Vt)
    budget = B1 + F(331,10000)*k
    lhs = 2*k*P
    print(f"k={k:2d} Vt={float(Vt):.6f} 2kP={float(lhs):.6f} budget={float(budget):.6f} margin={float(budget-lhs):.6f} ok={lhs<=budget}")
