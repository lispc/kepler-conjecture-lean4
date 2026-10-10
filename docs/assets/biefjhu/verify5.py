from fractions import Fraction as F
import math
def sqrt_ge(n, den=10**6):
    r = math.isqrt(n*den*den)
    if r*r < n*den*den: r += 1
    return F(r, den)
SQ3H = sqrt_ge(3); SQ6031H = sqrt_ge(6031)
T0 = F(93391,100000); assert (63*SQ3H+SQ6031H)/200 <= T0
C32 = F(8661,10000); assert SQ3H/2 <= C32
CHORD_HI = F(2887,10000); assert CHORD_HI*CHORD_HI >= F(1,12)
CHORD_LO = F(23,100)
TAU1 = F(86603,100000); assert SQ3H/2 <= TAU1
def TAU(b): return TAU1 + CHORD_HI*(b-1)
def T5bar(k): return F(31416,10000)/k - (F(314,100)/k)**3/6 + (F(31416,10000)/k)**5/120
def sigma_k(k):
    return {3:F(433,500), 4:F(7072,10000), 6:F(1,2)}.get(k) or T5bar(k)
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28
WIN1 = {3:(F(3,4),P_sept),4:(F(6124,10000),P_sept),5:(C32*T5bar(5),P_quad),6:(C32*T5bar(6),P_quad),
        7:(C32*T5bar(7),P_quad),8:(C32*T5bar(8),P_quad),9:(C32*T5bar(9),P_quad),
        10:(C32*T5bar(10),P_quad),11:(C32*T5bar(11),P_quad)}
TAILV = C32*F(31416,10000)
def Phi_of(tau, sig, den=10**6):
    tgt = sig*sig/(1-(tau*sig)**2)
    m = math.isqrt(tgt.numerator*den*den//tgt.denominator)
    while F(m,den)**2*(1-(tau*sig)**2) < sig*sig: m += 1
    return F(m,den)
def incr_hi(a,b,k): return (b-a)*CHORD_HI*Phi_of(TAU(b), sigma_k(k))
def incr_lo(a,b,k): return (b-a)*CHORD_LO*Phi_of(T0, sigma_k(k))
LF = F(253,130)

def check_route(k, pieces):
    if k >= 12: Vt, P = TAILV/F(k), P_quad
    else: Vt, P = WIN1[k]
    print(f"--- k={k}")
    okall = True
    for idx,(a,b) in enumerate(pieces):
        cumA = sum(incr_hi(a2,b2,k) for (a2,b2) in pieces[:idx])
        if b == F(126,100):
            # h0-slide piece: cum(h) <= cumA + (h0-h)*CHORD_LO*Phi0 ; sum slop negative -> max at h=a
            cummax = incr_lo(a,b,k)
            smax = LF*(F(126,100)-a) + cumA + cummax
        else:
            # h1-slide piece: cum(h) <= cumA + (h-a)*CHORD_HI*Phi(TAU(b))
            m = CHORD_HI*Phi_of(TAU(b), sigma_k(k)) - LF
            if m <= 0: smax = LF*(F(126,100)-a) + cumA
            else:      smax = LF*(F(126,100)-b) + cumA + (b-a)*CHORD_HI*Phi_of(TAU(b), sigma_k(k))
        lhs = F(591,1000) - F(331,10000)*k + smax + 2*k*P(Vt)
        ok = lhs <= F(628,100)
        okall &= ok
        print(f"   [{float(a):.2f},{float(b):.2f}] smax={float(smax):.6f} lhs={float(lhs):.6f} ok={ok} slack={float(F(628,100)-lhs):.6f}")
    return okall

routes = [(3,[(F(1),F(115,100)),(F(115,100),F(126,100))]),
          (4,[(F(1),F(126,100))]),
          (5,[(F(1),F(113,100)),(F(113,100),F(126,100))]),
          (6,[(F(1),F(12,10)),(F(12,10),F(126,100))]),
          (7,[(F(1),F(126,100))]),(8,[(F(1),F(126,100))]),(9,[(F(1),F(126,100))]),
          (10,[(F(1),F(126,100))]),(11,[(F(1),F(126,100))])]
for k,pieces in routes: check_route(k,pieces)
print("--- tail")
for k in [12,13,20,1000]:
    Vt = TAILV/F(k); P = P_quad(Vt)
    cumA = F(0); a,b = F(1),F(126,100)
    smax = LF*(F(126,100)-a) + incr_lo(a,b,k)
    lhs = F(591,1000)-F(331,10000)*k+smax+2*k*P(Vt)
    print(f"   k={k}: lhs={float(lhs):.6f} ok={lhs<=F(628,100)} Vt^2ok={Vt*Vt<=F(17,64)} sok={F(9739,10000)**2 <= 1-(TAILV/12)**2 if k==12 else True}")
