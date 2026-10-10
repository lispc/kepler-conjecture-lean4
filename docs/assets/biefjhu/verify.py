from fractions import Fraction as F
import math

def isqrt_ge(n):
    # smallest integer r with r*r >= n
    r = math.isqrt(n)
    if r*r < n: r += 1
    return r
def isqrt_le(n):
    return math.isqrt(n)

# sqrt bounds as Fractions with denominator 10^6
def sqrt_iv(n, denom=10**6):
    lo = F(isqrt_le(n*denom*denom), denom)
    hi = F(isqrt_ge(n*denom*denom), denom)
    return lo, hi

sq3 = sqrt_iv(3)
sq5 = sqrt_iv(5)
sq7 = sqrt_iv(7)
sq6031 = sqrt_iv(6031)
print("sqrt3:", float(sq3[0]), float(sq3[1]))
print("sqrt6031:", float(sq6031[0]), float(sq6031[1]))

# t0 = (63*sqrt3 + sqrt6031)/200
t0_lo = (63*sq3[0] + sq6031[0])/200
t0_hi = (63*sq3[1] + sq6031[1])/200
print("t0 true-ish:", float(t0_lo), float(t0_hi))
print("t0 <= 467/500 ?", t0_hi <= F(467,500), float(t0_hi))
print("t0 <= 93391/100000 ?", t0_hi <= F(93391,100000))

# pi bounds
PI_LO = F(314159265358979, 10**14)  # conservative true pi lower
PI_UP = F(31416, 10000)             # pi < 3.1416 (Real.pi_lt_d4)
import decimal
decimal.getcontext().prec = 50
pi_true = decimal.Decimal("3.14159265358979323846264338327950288419716939937510")
print("pi check:", float(pi_true))

# sin(pi/k) via mpmath for reference
try:
    import mpmath as mp
    mp.mp.dps = 40
    def sin_ref(k): return mp.sin(mp.pi/k)
except ImportError:
    sin_ref = None

# T5 upper bound with pi in (3.14, 3.1416): sin(pi/k) <= 3.1416/k - (3.14/k)^3/6 + (3.1416/k)^5/120
def T5bar(k):
    return F(31416,10000*1)/k - (F(314,100)/k)**3/6 + (F(31416,10000)/k)**5/120

# sin(pi/3)=sqrt3/2 exact, sin(pi/4)=sqrt2/2, sin(pi/6)=1/2 exact.
def sigma_k(k):
    if k == 3:
        return sq3[1]/2
    if k == 4:
        return sq2_hi/2
    if k == 6:
        return F(1,2)
    return T5bar(k)

sq2 = sqrt_iv(2)
sq2_hi = sq2[1]

# coefficient for sqrt3/2: use exact sqrt3/2 or rational 8661/10000
c32 = F(8661,10000)
print("sqrt3/2 <=", float(c32), sq3[1]/2 <= c32)

