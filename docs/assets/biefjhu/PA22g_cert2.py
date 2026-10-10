from fractions import Fraction as F
import math

def sqrt_ceil(x, den=10**6):
    n = x.numerator * den * den // x.denominator
    r = math.isqrt(n)
    while F(r, den)**2 < x:
        r += 1
    return F(r, den)

def Phi(tau, sig, den=10**6):
    return sqrt_ceil(sig*sig/(1-(tau*sig)**2), den)

C = F(2887,10000); LF = F(253,130); H0 = F(126,100); TAU1 = F(86603,100000)
def P_sept(w): return w + w**3/6 + w**5/10 + F(3,28)*w**7
def T5b(k): return F(31416,10000)/k - (F(31415,10000)/k)**3/6 + (F(31416,10000)/k)**5/120

def Tval(h):  # true T(h) in float for reference
    return float(h)*math.sqrt(3)/4 + math.sqrt(1-(float(h)/2)**2)/2

def base(k): return F(591,1000) - F(331,10000)*k

def Bk(k, sig, Vt):
    return F(6283,1000) - base(k) - 2*k*P_sept(Vt) if k==3 or k==4 else F(6283,1000)-base(k)-2*k*(Vt+Vt**3/6+Vt**5/10)

SIG = {3:F(8661,10000), 4:F(7072,10000), 5:T5b(5), 6:F(1,2)}
VT  = {3:F(3,4), 4:F(6124,10000)}
for k in (5,6): VT[k] = F(8661,10000)*T5b(k)

print("=== budgets B_k = 6.283 - base - 2k*P(Vt) ===")
for k in (3,4,5,6):
    print(f"  k={k}: B = {float(Bk(k,SIG[k],VT[k])):.6f}")

# generic multi-piece certificate check: pieces = list of (a,b); chord C1 = 0.2887 on piece0 (from 1),
# per-piece kappa_i = ceil(T'(a_i)) via r_i = ceil(sqrt(1-(a_i/2)^2)) upper, window tau_i = TAU1+C*(b_i-1) for piece0
# else tau_i = ceil(T(a_i)+(b_i-a_i)*kappa_i) (rational), phi_i = Phi(tau_i, sig)
def certify(k, pieces, sig, label):
    B = Bk(k, sig, VT[k])
    two_k = 2*k
    cumA = F(0)
    worst = F(0)
    ok = True
    details = []
    for idx,(a,b) in enumerate(pieces):
        if idx == 0:
            kap = C
            tau = TAU1 + C*(b-1)
        else:
            r = sqrt_ceil(1-(a/2)**2, 10**5)
            kap_raw = F(4331,10000) - a/(8*r)
            kap = F(math.ceil(kap_raw*10**5), 10**5)
            tau = TAU1 + C*(a-1) + (b-a)*kap  # T(a) upper + chord
        phi = Phi(tau, sig)
        endB = (b-a)*two_k*kap*phi
        endA = LF*(H0-a)
        piece_max = cumA + max(endA, endB)
        worst = max(worst, piece_max)
        details.append((a,b,float(kap),float(phi),float(cumA),float(endA),float(endB)))
        cumA = cumA + endB
    ok = worst <= B
    print(f"  {label}: worst={float(worst):.6f} B={float(B):.6f} slack={float(B-worst):.6f} OK={ok}")
    for d in details:
        print(f"      [{float(d[0]):.4f},{float(d[1]):.4f}] kap={d[2]:.5f} phi={d[3]:.6f} cumA={d[4]:.6f} endA={d[5]:.6f} endB={d[6]:.6f}")
    return ok

print("\n=== k=4 piece-split search ===")
certify(4, [(F(1),F(11,10)),(F(11,10),H0)], SIG[4], "k=4 2pc b=1.1")
certify(4, [(F(1),F(11,10)),(F(11,10),F(6,5)),(F(6,5),H0)], SIG[4], "k=4 3pc 1.1/1.2")
certify(4, [(F(1),F(27,25)),(F(27,25),F(6,5)),(F(6,5),H0)], SIG[4], "k=4 3pc 1.08/1.2")
certify(4, [(F(1),F(27,25)),(F(27,25),F(23,20)),(F(23,20),H0)], SIG[4], "k=4 3pc 1.08/1.15")
certify(4, [(F(1),F(21,20)),(F(21,20),F(11,10)),(F(11,10),F(6,5)),(F(6,5),H0)], SIG[4], "k=4 4pc")

print("\n=== final route2 checks (budget vs B_k) for k=3,5,6 ===")
def certify2(k, b, sig, label):
    tau = TAU1 + C*(b-1)
    phiT = Phi(tau, sig)
    r = sqrt_ceil(1-(b/2)**2, 10**5)
    kap_raw = F(4331,10000) - b/(8*r)
    kap = F(math.ceil(kap_raw*10**5), 10**5)
    tau0 = tau + (H0-b)*kap
    phiF = Phi(tau0, sig)
    B = Bk(k, sig, VT[k])
    hX1 = LF*(H0-b) + (b-1)*2*k*C*phiT
    hX2a = hX1
    hX2b = (b-1)*2*k*C*phiT + (H0-b)*2*k*kap*phiF
    slack = B - max(hX1,hX2b)
    print(f"  {label}: B={float(B):.6f} hX1={float(hX1):.6f} hX2b={float(hX2b):.6f} slack={float(slack):.6f} OK={slack>=0} kap={kap} phiT={phiT} phiF={phiF} r={r}")
    return slack >= 0

c3 = certify2(3, F(23,20), SIG[3], "k=3 b=23/20")
c5 = certify2(5, F(27,25), SIG[5], "k=5 b=27/25")
c6 = certify2(6, F(6,5),  SIG[6], "k=6 b=6/5")
print("route2 k=3,5,6 all OK:", c3 and c5 and c6)

print("\n=== k=4 finer piece-split search (budget B4 = 0.522377) ===")
configs = {
 "B 1.1/1.16": [(F(1),F(11,10)),(F(11,10),F(29,25)),(F(29,25),H0)],
 "C 1.1/1.18": [(F(1),F(11,10)),(F(11,10),F(59,50)),(F(59,50),H0)],
 "D 1.08/1.16/1.22": [(F(1),F(27,25)),(F(27,25),F(29,25)),(F(29,25),F(61,50)),(F(61,50),H0)],
 "E 1.1/1.16/1.21": [(F(1),F(11,10)),(F(11,10),F(29,25)),(F(29,25),F(121,100)),(F(121,100),H0)],
 "F 1.12/1.18/1.22": [(F(1),F(28,25)),(F(28,25),F(59,50)),(F(59,50),F(61,50)),(F(61,50),H0)],
 "G 1.1/1.17/1.22": [(F(1),F(11,10)),(F(11,10),F(117,100)),(F(117,100),F(61,50)),(F(61,50),H0)],
 "H 1.1/1.16/1.20/1.24": [(F(1),F(11,10)),(F(11,10),F(29,25)),(F(29,25),F(6,5)),(F(6,5),F(31,25)),(F(31,25),H0)],
}
for name, pcs in configs.items():
    certify(4, pcs, SIG[4], "k=4 "+name)
