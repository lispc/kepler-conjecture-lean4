#!/usr/bin/env python3
"""audit.py — per-leaf sampling audit for CertTM2 leaf certificates.

Two auditors over the emitted certificate JSON:

  * float  — the PROTOTYPE口径 (g4port `leaf_valid.py`): 300 deterministic
    pseudo-random samples per leaf (seed 99, Fraction construction,
    clamped), evaluated with the float navigation backend; checks
      (a) positivity: every sample value > 0;
      (b) claim: per-leaf sample minimum >= estBound - 1e-9, where
          `estBound` is the navigation estimate — the same quantity the
          prototype audited.
  * mpmath — high-precision re-check (mp.dps=60): the same samples are
    re-evaluated with mpmath and compared against (i) positivity with a
    -1e-40 guard, (ii) the CERTIFIED bounds `boundA` / `boundB` /
    `vertexBound` exactly (Fraction arithmetic on the converted samples).
    The certificate fields themselves are exact dyadic enclosures, so a
    violation here would mean an emitter bug, not round-off.

Usage:
  python3 audit.py --json out/p1_s10.json [--points 300] \
      [--modes float,mpmath] [--mp-leaves 25] [--seed 99]

Exit code 0 iff no violations (in the audited modes).
"""

import argparse
import json
import os
import random
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)

import exprs as EX            # noqa: E402
import nav                    # noqa: E402
import pilots                 # noqa: E402

_MP = {"fn": None, "key": None}


def sample_points(leaf, n, seed):
    """Prototype `leaf_valid` sample construction (verbatim formula,
    seedable); samples the NAV box (the certificate's dyadic box is an
    outward superset of it)."""
    rng = random.Random(seed)
    boxF = [(F(lo), F(hi)) for lo, hi in leaf["boxNav"]]
    pts = []
    for _ in range(n):
        y = []
        for lo, hi in boxF:
            if hi == lo:
                y.append(lo)
            else:
                u = rng.random()
                v = lo + (hi - lo) * F(int(u * 10 ** 12), 10 ** 12)
                y.append(min(max(v, lo), hi))
        pts.append(y)
    return pts


def eval_float(pkey, y, sides):
    expr = pilots.mkexpr(pilots.PILOTS[pkey], nav.BackendF())
    ys = [EX.point_jet(nav.BackendF, i, y[i]) for i in range(6)]
    return expr(ys, sides, None).v


def mp_fn(pkey):
    """mpmath point evaluator for a pilot (60 dps callers)."""
    import mpmath as mp
    got = _MP.get(pkey)
    if got is not None:
        return got

    def deltaX(x):
        x1, x2, x3, x4, x5, x6 = x
        return (x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6)
                + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
                + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6)
                - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6)

    def deltaX4(x):
        x1, x2, x3, x4, x5, x6 = x
        return (-x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6
                + x1 * (-x1 + x2 + x3 - x4 + x5 + x6))

    def dihY(yy):
        x = [v * v for v in yy]
        return mp.pi / 2 + mp.atan2(-deltaX4(x), mp.sqrt(4 * x[0] * deltaX(x)))

    def solY(yy):
        a, b, c, d, e, f = yy
        return (dihY([a, b, c, d, e, f]) + dihY([b, c, a, e, f, d])
                + dihY([c, a, b, f, d, e]) - mp.pi)

    def lmfun(h, side):
        if side == 'right':
            return mp.mpf(0)
        h0 = mp.mpf("1.26")
        return (h0 - h / 2) / (h0 - 1)

    D_PERMS = ((0, 1, 2, 3, 4, 5), (1, 2, 0, 4, 5, 3), (2, 0, 1, 5, 3, 4),
               (3, 2, 4, 0, 5, 1), (4, 0, 5, 1, 3, 2), (5, 0, 4, 2, 3, 1))
    S_PERMS = ((0, 1, 2, 3, 4, 5), (0, 4, 5, 3, 1, 2), (3, 4, 2, 0, 1, 5),
               (3, 1, 5, 0, 4, 2))

    def gamma4(yy, sides):
        y = list(yy)
        S = solY([y[k] for k in S_PERMS[0]])
        for pm in S_PERMS[1:]:
            S = S + solY([y[k] for k in pm])
        D = mp.mpf(0)
        for k, pm in enumerate(D_PERMS):
            D = D + lmfun(y[k], sides[k]) * dihY([y[j] for j in pm])
        acos13 = mp.acos(mp.mpf(1) / 3)
        sol0 = 3 * acos13 - mp.pi
        tau0 = 4 * mp.pi - 20 * sol0
        mm1 = sol0 * mp.sqrt(8) / tau0
        mm2 = (6 * sol0 - mp.pi) * mp.sqrt(2) / (6 * tau0)
        vol4 = (2 * mm1 / mp.pi) * S - (8 * mm2 / mp.pi) * D
        volY = mp.sqrt(deltaX([v * v for v in y])) / 12
        return volY - vol4

    p = pilots.PILOTS[pkey]

    def fn(yv, sides):
        if 'w' in p:
            w, m = p['w'], p['m']
            return (gamma4(yv, sides) / w + m * mp.mpf("-0.005")
                    - mp.mpf("0.0560305")
                    + mp.mpf("0.0445813") * dihY(list(yv)))
        B = mp.mpf(str(p['B']))
        out = gamma4(yv, sides) + B * dihY(list(yv)) \
            + mp.mpf(str(p['const']))
        for k, cf in p['affine']:
            out = out + mp.mpf(str(cf)) * yv[k]
        return out

    _MP[pkey] = fn
    return fn


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", required=True)
    ap.add_argument("--points", type=int, default=300)
    ap.add_argument("--modes", default="float,mpmath")
    ap.add_argument("--mp-leaves", type=int, default=0,
                    help="if >0: mpmath re-check only the first N leaves "
                         "plus every MONO/CONC leaf (budget knob; 0 = all)")
    ap.add_argument("--seed", type=int, default=99)
    args = ap.parse_args()

    doc = json.load(open(args.json))
    pkey = doc["pilot"]["key"]
    sides0 = doc["pilot"]["sides"]
    leaves = doc["leaves"]
    modes = args.modes.split(",")

    n_pos_bad = 0
    n_claim_bad = 0
    n_cert_bad = 0
    worst_gap = 0.0
    audited = 0

    def _q(s):
        a, b = s.split("/")
        return F(int(a), int(b))

    for leaf in leaves:
        pts = sample_points(leaf, args.points, args.seed)
        sides = leaf.get("sides", sides0)

        if "float" in modes:
            audited += 1
            mn = None
            for y in pts:
                v = eval_float(pkey, y, sides)
                if v <= 0:
                    n_pos_bad += 1
                mn = v if mn is None else min(mn, v)
            claim = leaf.get("estBound")
            if claim is not None and mn < claim - 1e-9:
                n_claim_bad += 1
                worst_gap = max(worst_gap, claim - mn)

        if "mpmath" in modes and (args.mp_leaves <= 0
                                  or leaf["index"] < args.mp_leaves
                                  or leaf["kind"] in ("MONO", "CONC")):
            audited += 1
            import mpmath as mp
            mp.mp.dps = 60
            fn = mp_fn(pkey)
            claims = []
            for key in ("boundA", "boundB", "vertexBound"):
                q = (leaf.get(key) or {}).get("q")
                if q:
                    claims.append(_q(q))
            mn = None
            for y in pts:
                v = fn([mp.mpf(a.numerator) / mp.mpf(a.denominator)
                        for a in y], sides)
                if v <= -mp.mpf("1e-40"):
                    n_pos_bad += 1
                mn = v if mn is None else min(mn, v)
            # mpf -> exact Fraction via the 60-digit decimal string (error
            # ~1e-59 relative, far below the 1e-30 comparison guard)
            mnF = F(str(mn))
            for qf in claims:
                if mnF < qf - F(1, 10 ** 30):
                    n_cert_bad += 1

    print("audited %d leaf-blocks (modes=%s): positivity violations=%d "
          "float-claim violations=%d (worst gap %.3g) certified-claim "
          "violations=%d" % (audited, ",".join(modes), n_pos_bad,
                             n_claim_bad, worst_gap, n_cert_bad))
    if n_pos_bad or n_claim_bad or n_cert_bad:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
