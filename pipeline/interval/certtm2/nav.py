"""nav.py — float navigation backend for the CertTM2 emitter.

Port of the g4port prototype `g4core.BackendF` (name/num/pi/sqrt/atan/
atan2/abs/h0/hplus), productionised.  Floats are NAVIGATION ONLY
(~1e-15 relative): every certificate field is re-derived by `dyad.py`.
Operation parity with the prototype is load-bearing: the B&B leaf counts
must reproduce the g4port s-curve (81/60/47 at safety 10), so `num`,
`pi`, `sqrt`, `atan`, `atan2` and the `mm12` constants keep the exact
prototype expressions (`math.acos(1/3)` etc.).
"""

import math


class BackendF:
    name = "float"
    h0 = 1.26
    hplus = 1.3254
    one = 1.0

    @staticmethod
    def num(s):
        if isinstance(s, str) and "/" in s:
            a, b = s.split("/")
            return float(a) / float(b)
        return float(s)

    @staticmethod
    def pi():
        return math.pi

    @staticmethod
    def sqrt(x):
        return math.sqrt(x) if x > 0 else 0.0

    @staticmethod
    def atan(x):
        return math.atan(x)

    @staticmethod
    def atan2(y, x):
        return math.atan2(y, x)

    @staticmethod
    def abs(x):
        return abs(x)

    @staticmethod
    def safe_cube_inv(v):
        raise ValueError("float sqrt crossed 0 (impossible on pilot boxes)")


def mm12(N):
    """Point mm12 constants (float branch of g4core.mm12 — verbatim)."""
    acos13 = math.acos(1.0 / 3.0)
    pi = math.pi
    sol0 = 3 * acos13 - pi
    tau0 = 4 * pi - 20 * sol0
    return (sol0 * math.sqrt(8) / tau0,
            (6 * sol0 - pi) * math.sqrt(2) / (6 * tau0))
