from fractions import Fraction as F
import math

# ---- exact rational toolkit ----
def sqrt_le(n, den=10**6):  # floor(sqrt(n))/den <= sqrt(n)
    return F(math.isqrt(n*den*den), den)
def sqrt_ge(n, den=10**6):
    r = math.isqrt(n*den*den)
    if r*r < n*den*den: r += 1
    return F(r, den)

SQ3L, SQ3H = sqrt_le(3), sqrt_ge(3)
SQ2H = sqrt_ge(2)
SQ6031H = sqrt_ge(6031)
T0 = F(93391,100000)          # t0 <= T0 ; check
assert (63*SQ3H + SQ6031H)/200 <= T0
T0L = F(93389,100000)
assert (63*SQ3L + sqrt_le(6031))/200 >= T0L
print("t0 in [", float(T0L), ",", float(T0H := T0), "]")

C32 = F(8661,10000)           # sqrt3/2 <= C32
assert SQ3H/2 <= C32
CHORD_HI = F(2887,10000)      # 1/(2*sqrt3) <= CHORD_HI  (2887^2 >= 12e6/1.44... check)
assert CHORD_HI*CHORD_HI >= F(1,12), "2887/1e4 >= 1/(2 sqrt3)"
CHORD_LO = F(23,100)
TAU1 = F(86603,100000); assert SQ3H/2 <= TAU1
TAU = lambda b: TAU1 + CHORD_HI*(b-1)   # T(b) <= TAU1 + CHORD_HI*(b-1) for b in [1,1.26]

def T5bar(k): return F(31416,10000)/k - (F(314,100)/k)**3/6 + (F(31416,10000)/k)**5/120
def sigma_k(k):
    if k == 3: return F(433,500)          # sqrt3/2 <= 433/500
    if k == 4: return F(7072,10000)       # sqrt2/2 <= 7072/10000
    if k == 6: return F(1,2)
    return T5bar(k)
def P_quad(w): return w + w**3/6 + w**5/10
def P_sept(w): return w + w**3/6 + w**5/10 + 3*w**7/28

# window table: (k, Vt, majorant)
WIN1 = {3:(F(3,4),P_sept), 4:(F(6124,10000),P_sept), 5:(C32*T5bar(5),P_quad),
        6:(C32*T5bar(6),P_quad), 7:(C32*T5bar(7),P_quad), 8:(C32*T5bar(8),P_quad),
        9:(C32*T5bar(9),P_quad), 10:(C32*T5bar(10),P_quad), 11:(C32*T5bar(11),P_quad)}
WIN0 = {4:(F(6608,10000),P_sept), 5:(F(5491,10000),P_sept)}
TAILV = C32*F(31416,10000)    # v <= TAILV/k for k >= 12

# Phi windows: Phi = sigma/sqrt(1-(tau*sigma)^2) >= actually we need rational Phi_k_tau with
#   Phi^2 * (1-(tau*sigma)^2) >= sigma^2  i.e. Phi is an UPPER rational for sigma/sqrt(1-(tau sigma)^2)
def Phi_of(tau, sig, den=10**6):
    # search rational q = m/den with q^2 (1-(tau sig)^2) >= sig^2, minimal
    target = sig*sig/(1-(tau*sig)**2)
    m = math.isqrt((target*den*den).numerator // (target*den*den).denominator)
    while True:
        m += 1
        if F(m,den)**2*(1-(tau*sig)**2) >= sig*sig:
            return F(m,den)

# --- T-bound at a breakpoint
def tau_at(b): return TAU(b)

# ---- slide increment for piece [a,b], k: incr <= (b-a)*CHORD_HI*Phi(tau(b),sigma_k) ----
def incr_hi(a,b,k):
    return (b-a)*CHORD_HI*Phi_of(tau_at(b), sigma_k(k))
def incr_lo(a,b,k):  # h0-slide: (b-a)*CHORD_LO*Phi(T0, sigma_k)
    return (b-a)*CHORD_LO*Phi_of(T0, sigma_k(k))

# ---- final per-piece feasibility: for each piece [a,b] of the cover of [1,h0]:
#   0.591-0.0331k + (253/130)*(1.26-a) + 2k*(P(Vt)+cumincr(b)) <= 6.28
# where cumincr(b) = sum of piece increments fully below/at b, with last piece partial-bounded by full (b-a) at b=h0.
def check_route(k, pieces, win):
    Vt, major = win[k] if k in win else (None,None)
    if k >= 12:
        Vt, P = TAILV/F(k), P_quad
    else:
        Vt, P = Vt, major
    s = 0.0
    print(f"--- k={k} pieces={pieces}")
    okall = True
    for (a,b) in pieces:
        # cumulative increment bounded at right end b: sum over earlier full pieces + this piece (a..b)
        cum = F(0)
        for (a2,b2) in pieces:
            if b2 <= b:  # earlier piece fully counted
                lo, hi = incr_lo(a2,b2,k), incr_hi(a2,b2,k)
                # earlier pieces use hi-bound; if piece is the final one ending at h0 use lo-style? Use hi for all pre-final, lo for final
                cum += hi if b2 != pieces[-1][1] else min(hi, incr_lo(a2,b2,k)+ (F(0)))
        # for the piece containing b itself: increment from its left end a to b
        this = incr_hi(a,b,k) if b != F(126,100) else incr_hi(a,b,k)
        cum = F(0)
        for (a2,b2) in pieces[:-1]:
            if b2 <= a: cum += incr_hi(a2,b2,k)
        # increment from 1 to a (previous pieces) plus a to b (this piece)
        cumA = F(0)
        for (a2,b2) in pieces[:-1]:
            cumA += incr_hi(a2,b2,k)
        total_at_b = cumA + (incr_hi(a,b,k) if b != F(126,100) else incr_hi(a,b,k))
        # NOTE for final piece ending at h0, better: previous full pieces (hi) + chord_lo from a to h0
        if b == F(126,100):
            total_at_b = sum(incr_hi(a2,b2,k) for (a2,b2) in pieces[:-1]) + incr_lo(a,b,k)
        lhs = F(591,1000) - F(331,10000)*k + F(253,130)*(F(126,100)-a) + 2*k*(P(Vt)+total_at_b)
        ok = lhs <= F(628,100)
        okall = okall and ok
        print(f"   [{float(a):.2f},{float(b):.2f}] cum={float(total_at_b):.6f} lhs={float(lhs):.6f} <= 6.28: {ok}  (slack {float(F(628,100)-lhs):.6f})")
    return okall

routes = [
    (3, [(F(1),F(115,100)), (F(115,100),F(126,100))], WIN1),
    (4, [(F(1),F(126,100))], WIN1),
    (5, [(F(1),F(113,100)), (F(113,100),F(126,100))], WIN1),
    (6, [(F(1),F(12,10)), (F(12,10),F(126,100))], WIN1),
    (7, [(F(1),F(126,100))], WIN1),
    (8, [(F(1),F(126,100))], WIN1),
    (9, [(F(1),F(126,100))], WIN1),
    (10,[(F(1),F(126,100))], WIN1),
    (11,[(F(1),F(126,100))], WIN1),
]
for (k,pieces,win) in routes:
    check_route(k,pieces,win)

# tail k>=12: pieces [(1,h0)], Vt = TAILV/k
print("--- tail k>=12")
for k in [12, 13, 50, 1000]:
    Vt = TAILV/F(k)
    P = P_quad(Vt)
    cum = incr_hi(F(1),F(126,100),k)   # chord-hi version, tau = 433/500+2887/10000*0.26
    lhs = F(591,1000)-F(331,10000)*k+F(506,1000)+2*k*(P+cum)
    print(f"   k={k}: lhs={float(lhs):.6f} <= 6.28: {lhs <= F(628,100)}  (Vt^2={float(Vt*Vt):.5f}<=17/64:{Vt*Vt<=F(17,64)})")
