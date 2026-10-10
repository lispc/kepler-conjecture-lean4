from fractions import Fraction as F
import collections

d = [F(1)]
for n in range(1, 40):
    d.append(d[-1]*F(2*n-1, 2*n))

r = F(3,8)

def try_N(N, Kform="8/5"):
    # Qd = sum_{n<=N-1} d_n u^n + K u^N, K = d_N * 8/5 (valid: tail <= d_N u^N/(1-u) <= d_N*8/5 for u <= 3/8)
    if Kform == "8/5":
        K = d[N]*F(8,5)
    else:
        K = Kform
    Q = {n: d[n] for n in range(N)}
    Q[N] = K
    # E = Q^2*(1-u) - 1
    def pmul(a,b):
        res = collections.defaultdict(F)
        for k1,v1 in a.items():
            for k2,v2 in b.items(): res[k1+k2] += v1*v2
        return dict(res)
    def padd(a,b):
        res = collections.defaultdict(F)
        for k,v in list(a.items())+list(b.items()): res[k] += v
        return {k:v for k,v in res.items() if v != 0}
    E = pmul(pmul(Q,Q), {0:F(1),1:F(-1)})
    E = padd(E, {0:F(-1)})
    # LP check: prefix sums of a_k r^k must be >= 0 for all prefixes
    deg = max(E)
    bad = []
    s = F(0)
    for k in range(0, deg+1):
        s += E.get(k, 0)*r**k
        if s < 0: bad.append((k, s))
    return E, bad

for N in range(4, 15):
    E, bad = try_N(N)
    print(f"N={N}: deg={max(E)} coefficients={len(E)} LP-prefix-failures={len(bad)}", ("FIRST BAD "+str(bad[0])) if bad else "LP-OK")
