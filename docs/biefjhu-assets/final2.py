from fractions import Fraction as F
import math
def sqrt_ge(n, den=10**6):
    r = math.isqrt(n*den*den)
    if r*r < n*den*den: r += 1
    return F(r, den)
SQ3H = sqrt_ge(3); SQ6031H = sqrt_ge(6031)
T0 = F(93391,100000); assert (63*SQ3H+SQ6031H)/200 <= T0
LF = F(253,130)
PI2 = 2*F(31415,10000)               # 2*pi >= 6.283
def T5b(k): return F(31416,10000)/k - (F(31415,10000)/k)**3/6 + (F(31416,10000)/k)**5/120
def sigma_k(k): return {3:F(433,500),4:F(7072,10000),6:F(1,2)}.get(k) or T5b(k)
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28
def P4(w):    return w + w**3/6 + 3*w**5/40 + w**7/16
CHORD_HI = F(2887,10000); CHORD_LO = F(23,100)
TAU1 = F(86603,100000)
def TAU(b): return TAU1 + CHORD_HI*(b-1)
def Phi_of(tau, sig, den=10**7):
    tgt = sig*sig/(1-(tau*sig)**2)
    m = math.isqrt(tgt.numerator*den*den//tgt.denominator)
    while F(m,den)**2*(1-(tau*sig)**2) < sig*sig: m += 1
    return F(m,den)
def PhiT(b,k): return Phi_of(TAU(b), sigma_k(k))
def Phi0(k):  return Phi_of(T0, sigma_k(k))
WIN1 = {3:(F(3,4),P_sept),4:(F(6124,10000),P4),5:(F(8661,10000)*T5b(5),P_quad),
        6:(F(8661,10000)*T5b(6),P_quad),7:(F(8661,10000)*T5b(7),P_quad),8:(F(8661,10000)*T5b(8),P_quad),
        9:(F(8661,10000)*T5b(9),P_quad),10:(F(8661,10000)*T5b(10),P_quad),11:(F(8661,10000)*T5b(11),P_quad)}
TAILV = F(8661,10000)*F(31416,10000)

def check(k, pieces):
    if k >= 12: Vt, P = TAILV/F(k), P_quad
    else: Vt, P = WIN1[k]
    base = F(591,1000) - F(331,10000)*k
    okall = True
    for idx,(a,b) in enumerate(pieces):
        cumA = F(0)
        for j in range(idx):
            a2,b2 = pieces[j]
            cumA += 2*k*(b2-a2)*CHORD_HI*PhiT(b2,k)
        isfinal = (idx == len(pieces)-1)
        if isfinal:
            # h0-slide: cum(h) <= cumA + 2k*(h0-h)*CHORD_LO*Phi0 ; decreasing in h -> max at h=a
            smax = LF*(F(126,100)-a) + cumA + 2*k*(F(126,100)-a)*CHORD_LO*Phi0(k)
        else:
            candA = LF*(F(126,100)-a) + cumA
            candB = LF*(F(126,100)-b) + cumA + 2*k*(b-a)*CHORD_HI*PhiT(b,k)
            smax = max(candA, candB)
        lhs = base + smax + 2*k*P(Vt)
        ok = lhs <= PI2
        okall &= ok
        print(f"  k={k:2d} [{float(a):.3f},{float(b):.3f}] smax={float(smax):.6f} 2kP={float(2*k*P(Vt)):.6f} slack={float(PI2-lhs):.6f} {'OK' if ok else 'FAIL'}")
    return okall

routes = {3:[(F(1),F(115,100)),(F(115,100),F(126,100))],
          4:[(F(1),F(11,10)),(F(11,10),F(126,100))],
          5:[(F(1),F(27,25)),(F(27,25),F(126,100))],
          6:[(F(1),F(6,5)),(F(6,5),F(126,100))],
          7:[(F(1),F(126,100))],8:[(F(1),F(126,100))],9:[(F(1),F(126,100))],
          10:[(F(1),F(126,100))],11:[(F(1),F(126,100))]}
allok = True
for k in sorted(routes): allok &= check(k, routes[k])
# tail: single piece, candA=0.506 vs candB = 2k*0.26*CHORD_HI*sigma/√(1-(TAU(1.26) sigma/12)^2), sigma=31416/(1e4 k)
sig = F(31416,10000)
tau = TAU(F(126,100))
r12 = math.sqrt(float(1-(tau*sig/12)**2))
candB12 = 2*12*(F(26,100))*CHORD_HI*F(math.floor(sig/12*10**9),10**9)/F(math.floor(r12*10**9),10**9)
print(f"tail k=12: candA=0.506 candB={float(candB12):.6f} -> smax=0.506")
lhs12 = F(591,1000)-F(331,10000)*12+F(1,2)+24*P_quad(TAILV/12)
print(f"tail lhs(12) = {float(lhs12):.6f} <= {float(PI2)}: {lhs12 <= PI2}")
print("ALL:", allok)
