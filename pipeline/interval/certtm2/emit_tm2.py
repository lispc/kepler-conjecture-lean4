#!/usr/bin/env python3
"""emit_tm2.py — CertTM2/d2B production leaf-certificate emitter.

Pipeline (per run):
  1. NAVIGATE: deterministic best-first B&B in float mode (engine.solve,
     g4port `engine_lipsch` port) — reproduces the s-curve leaf counts.
  2. CERTIFY every closed leaf with the C1 supplier: certified
     dyadic-interval evaluations of the pilot expression on `dyad.py`
     (the tmexact.py kernel replica):
       * thin box at the exact dyadic centre  -> fC (f(c)), gC (grad c),
         HC (Hess c)                          — point-jet enclosures;
       * full leaf box                        -> GB (grad over box),
         HB (Hessian over box)                — the C1 d2B envelopes
         (symbolic second derivatives, box-interval evaluated; zero D3,
         zero atan residue: after two differentiations the atan nodes
         are gone, only sqrt / rational operations remain).
  3. BOUNDS in exact rational arithmetic (Fractions over dyadic values):
       boundA = fC.lo + sum_i minQuad(gC_i, HB_ii.lo, w_i)
                - sum_{i<j} |HB_ij|.hi * w_i * w_j
         (the engine's t2 formula with every sampled quantity replaced by
         its certified C1 counterpart; sound by axial telescoping + 1-D
         Lagrange — the future `loBound2A`-shaped Lean lemma);
       boundB = fC.lo + sum_i (GB_i . [-w_i, w_i]).lo
                + 1/2 sum_i min(0, HB_ii.lo) * w_i^2
         (the HOL-shaped B form — the future `loBound2B`; no D3 at all);
       vertexBound (MONO/CONC): certified thin evaluations at the
         enumerated vertices.
  4. EMIT one schema'd JSON document (`certtm2-leaf-cert/1.0`,
     byte-deterministic — see SCHEMA.md).

The emitted box is the nav box rounded OUTWARD to a dyadic grid
(default 2^-24; nav endpoints like 27897/12500 are not dyadic); all
certified quantities are valid for the emitted box, hence for the nav
box it contains.  Boxes that kiss the lmfun kink y = 2.52 (not dyadic)
are certified with the hull of the two lmfun branches (piecewise-C1;
the affected slots are flagged per leaf under "kinkCross").

Usage:
  python3 emit_tm2.py --pilot p1 --safety 10 --out out/p1_s10.json
  python3 emit_tm2.py --pilot p3 --safety 10 --out out/p3.json \
      --compare-tsv leaves_p3.tsv
  python3 emit_tm2.py --pilot p1 --box '63/25,63/25,2,2,...' \
      --sides left,left,... --out out/oneleaf.json      # single leaf

Exit codes: 0 emitted (per-leaf cert failures are data, not errors),
2 nothing emitted / hard failure, 3 bad input.

Trust discipline (AGENTS §2): this tool produces DATA only.  A leaf
counts as *kernel-closed* only after the future Lean CertTM2 checker
replays its fields with `decide`; `certOk` here means "the certified
bound exceeds the navigation safety margin", nothing more.
"""

import argparse
import itertools
import json
import math
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))          # pipeline/interval
sys.path.insert(0, HERE)                           # the package itself

import tmexact as X            # noqa: E402
import certtm2                 # noqa: E402  (package doc / schema constants)
# NOTE: sibling modules are imported FLAT (sys.path carries certtm2/), not
# as `certtm2.x` — mixing the two styles would create duplicate module
# objects and break isinstance checks on the Dy class.
import dyad                    # noqa: E402
import exprs as EX             # noqa: E402
import engine                  # noqa: E402
import nav                     # noqa: E402
import pilots                  # noqa: E402
import symtree as ST           # noqa: E402


# ------------------------------------------------------------------ helpers

def dy_box(boxF, g):
    """Fraction box -> list of (loDy, hiDy) outward dyadic pairs."""
    return [(dyad.floor_grid(lo, g), dyad.ceil_grid(hi, g))
            for lo, hi in boxF]


def dy_f(d):
    """Dyadic pair -> exact Fraction."""
    return F(d[0]) * (F(2) ** d[1])


def jdy(d):
    """Dyadic pair -> JSON [m, e]."""
    return [d[0], d[1]]


def jinterval(I):
    """Dy interval -> JSON [[m,e],[m,e]]."""
    return [jdy(I.lo), jdy(I.hi)]


def jfrac(fr):
    """Fraction -> JSON "num/den" (exact); bare integer string when den=1
    (matches the g4port TSV rendering of integral endpoints)."""
    if fr.denominator == 1:
        return str(fr.numerator)
    return "%d/%d" % (fr.numerator, fr.denominator)


def dyadic_fbox(boxD):
    """Dyadic box -> exact Fraction box (the corner-min data view)."""
    return [(dy_f(lo), dy_f(hi)) for lo, hi in boxD]


def dyadic_center_w(boxD):
    """Exact dyadic centre and half-width list (tmexact semantics)."""
    ivs = [(lo, hi) for lo, hi in boxD]
    return X.boxCenter(ivs), X.boxW(ivs)


def min_quad(glo, ghi, m, w):
    """Exact joint minimum of g*t + (m/2)*t^2 over t in [-w, w],
    g in [glo, ghi] (all Fractions; m may be negative).
    Candidates: the four endpoint pairs plus the two stationary points
    t = -g/m (m > 0) when inside the interval — the exact joint min."""
    cands = []
    for t in (w, -w):
        for g in (glo, ghi):
            cands.append(g * t + m * t * t / 2)
    if m > 0:
        for g in (glo, ghi):
            t = -g / m
            if -w <= t <= w:
                cands.append(g * t + m * t * t / 2)
    return min(cands)


def _safe_frac(safe):
    """Float SAFE -> exact Fraction (binary-exact conversion)."""
    return F(safe)


# ------------------------------------------------------------------ certify

def pilot_base_tree(pkey, sides):
    """Base expression tree for a pilot (kink sides fixed)."""
    p = pilots.PILOTS[pkey]
    if 'w' in p:
        return ST.t_main(sides, p['w'], p['m'])
    return ST.t_margin(sides, p['B'], p['affine'], p['const'])


def certify_leaf(kind, boxF, sides, info, args, pkey):
    """C1 certification of one leaf.  Returns the certificate dict (JSON
    fields already encoded; floats only where documented).

    Certified quantities:
      * fC/gC/HC  — thin-box (dyadic centre) jet enclosures (AD);
      * fB/GB/HB  — full-box enclosures from the C1 tree supplier
        (symbolic partials of the pilot expression evaluated over the
        box; `--cert-mode ad` keeps the legacy interval-AD comparison);
    Verdict (certOk) is KIND-AWARE, mirroring the future Lean leaf
    arguments:
      T2   : boundA > SAFE                       (quadratic t2 argument)
      MONO : GB sign-definite on all free dims
             and vertexBound > SAFE               (mono-fix vertex argument)
      CONC : GB definite or HB_ii.hi <= 0 per free dim
             and vertexBound > SAFE               (mono|conc vertex argument)
      IA/LEAF: max(boundA, fB.lo) > SAFE          (plain interval argument)
    """
    boxD = dy_box(boxF, args.grid_exp)                    # (loDy, hiDy)
    ivs = [(lo, hi) for lo, hi in boxD]
    c, w = dyadic_center_w(ivs)
    boxFdy = dyadic_fbox(boxD)                            # Fraction view
    wF = [dy_f(x) for x in w]

    N = dyad.BackendDy(out=args.out_exp, rung=args.rung,
                       coef_grid=args.coef_grid, point_grid=args.coef_grid,
                       floor_grid=args.floor_grid)
    expr = pilots.mkexpr(pilots.PILOTS[pkey], N)
    rec = {
        "kind": kind,
        "box": [x for lo, hi in boxD for x in (jdy(lo), jdy(hi))],
        "boxNav": [[jfrac(lo), jfrac(hi)] for lo, hi in boxF],
        "center": [jdy(x) for x in c],
        "w": [jdy(x) for x in w],
        "sides": list(sides),
        "fB": None, "fC": None, "gC": None, "HC": None,
        "GB": None, "HB": None,
        "sqrtQueueThin": [], "sqrtQueueFull": [],
        "boundA": None, "boundB": None, "vertexBound": None,
        "estBound": (float(info["bound"]) if info and "bound" in info
                     else (float(info["t2"]) if info and "t2" in info
                           else None)),
        "certOk": False, "certArg": None, "certFail": None,
        "gbDefinite": [None] * 6,
        "hbDiagHi": None,
        "kinkCross": [],
    }

    # which slots kiss / cross the kink after outward rounding (hull mode)
    for i in range(6):
        loF, hiF = boxFdy[i]
        if loF <= EX.KINK <= hiF and boxFdy[i] != (EX.KINK, EX.KINK):
            rec["kinkCross"].append(i)

    try:
        # ---- thin evaluation at the exact dyadic centre (AD jet)
        ys = [EX.point_jet(N, i, dyad.Dy(c[i])) for i in range(6)]
        N.sqrt_trace = []
        thin = expr(ys, sides, boxFdy)
        rec["fC"] = jinterval(thin.v)
        rec["gC"] = [jinterval(thin.g[i]) for i in range(6)]
        rec["HC"] = [jinterval(thin.H[i][j]) for i in range(6)
                     for j in range(6)]
        rec["sqrtQueueThin"] = [list(t) for t in N.sqrt_trace]

        # ---- full-box C1 supplier: symbolic partials over the box
        # (--cert-splits s: each Fraction-free dim is refined into 2^s
        # equal Fraction pieces and the enclosures are hulled over the
        # sub-boxes — JET3_PLAN §3.4-2 bypass b; deterministic.)
        split = max(0, int(getattr(args, "cert_splits", 0)))
        freeF = [i for i in range(6) if boxFdy[i][0] != boxFdy[i][1]]
        grids = []
        for i in range(6):
            if i in freeF and split > 0:
                lo, hi = boxFdy[i]
                pts = [lo + (hi - lo) * F(k, 2 ** split)
                       for k in range(2 ** split + 1)]
                grids.append([(pts[k], pts[k + 1]) for k in range(2 ** split)])
            else:
                grids.append([boxFdy[i]])
        sub_boxes = []          # (Dy box, Fraction box) covering pairs
        for combo in itertools.product(*grids):
            tb = [dyad.Dy(dyad.floor_grid(lo, args.grid_exp),
                          dyad.ceil_grid(hi, args.grid_exp))
                  for lo, hi in combo]
            sub_boxes.append((tb, combo))
        traces = []
        if getattr(args, "cert_mode", "tree") == "ad":
            # legacy comparison mode: interval-AD jet over the box
            # (documented in VALIDATION.md: wrapping-explode measurement)
            tree_box = [dyad.Dy(lo, hi) for lo, hi in boxD]
            ys = [EX.var_jet(N, i, tree_box) for i in range(6)]
            N.sqrt_trace = []
            full = expr(ys, sides, boxFdy)
            fB, GBd, HBd = full.v, full.g, full.H
            traces = list(N.sqrt_trace)
            GB, HB = list(GBd), [HBd[i][j] for i in range(6)
                                 for j in range(6)]
        else:
            kit = ST.kit_for((pkey, tuple(sides)),
                             pilot_base_tree(pkey, sides))
            fB = None
            GB = [None] * 6
            HB = [None] * 36

            def hull(acc, v):
                if acc is None:
                    return v
                return dyad.Dy(X.dmin(acc.lo, v.lo), X.dmax(acc.hi, v.hi))

            for tb, yb in sub_boxes:
                N.sqrt_trace = []
                v, tr_f = ST.eval_main(kit, tb, N, yb)
                traces += tr_f
                fB = hull(fB, v)
                for i in range(6):
                    N.sqrt_trace = []
                    g = ST.eval_tree(kit.first(i), tb, N, yb)
                    traces += list(N.sqrt_trace)
                    GB[i] = hull(GB[i], g)
                for ij in range(36):
                    N.sqrt_trace = []
                    h = ST.eval_tree(kit.second(ij // 6, ij % 6), tb, N, yb)
                    traces += list(N.sqrt_trace)
                    HB[ij] = hull(HB[ij], h)
        rec["fB"] = jinterval(fB)
        rec["GB"] = [jinterval(g) for g in GB]
        rec["HB"] = [jinterval(h) for h in HB]
        rec["sqrtQueueFull"] = [list(t) for t in traces]

        # ---- exact bound arithmetic (Fractions over dyadic values)
        fClo = dy_f(thin.v.lo)
        sep = F(0)
        for i in range(6):
            glo, ghi = thin.g[i].lo_frac(), thin.g[i].hi_frac()
            mi = HB[i * 6 + i].lo_frac()
            sep += min_quad(glo, ghi, mi, wF[i])
        cross = F(0)
        for i in range(6):
            for j in range(6):
                if i < j:
                    Hij = HB[i * 6 + j]
                    sij = max(Hij.hi_frac(), -Hij.lo_frac())
                    cross += sij * wF[i] * wF[j]
        boundA = fClo + sep - cross
        rec["boundA"] = {"q": jfrac(boundA),
                         "dy": jdy(dyad.floor_grid(boundA, args.out_exp))}

        boundB = fClo
        for i in range(6):
            a, b = GB[i].lo_frac(), GB[i].hi_frac()
            wi = wF[i]
            linlo = min(a * wi, a * (-wi), b * wi, b * (-wi))
            mii = min(F(0), HB[i * 6 + i].lo_frac())
            boundB += linlo + mii * wi * wi / 2
        rec["boundB"] = {"q": jfrac(boundB),
                         "dy": jdy(dyad.floor_grid(boundB, args.out_exp))}

        # ---- certified structural flags
        free = [i for i in range(6) if boxD[i][0] != boxD[i][1]]
        for i in range(6):
            if GB[i].lo[0] > 0:
                rec["gbDefinite"][i] = "+"
            elif GB[i].hi[0] < 0:
                rec["gbDefinite"][i] = "-"
        rec["hbDiagHi"] = [jinterval(HB[i * 6 + i]) for i in range(6)]

        # ---- vertex bound (MONO/CONC): certified thin evals at vertices
        vmin = None
        if kind in ("MONO", "CONC") and info:
            for vtx in enumerate_vertices(kind, boxD, info):
                ys = [EX.point_jet(N, i, dyad.Dy(vtx[i])) for i in range(6)]
                v = expr(ys, sides, boxFdy)
                lo = dy_f(v.v.lo)
                vmin = lo if vmin is None else min(vmin, lo)
            if vmin is not None:
                rec["vertexBound"] = {
                    "q": jfrac(vmin),
                    "dy": jdy(dyad.floor_grid(vmin, args.out_exp))}

        # ---- kind-aware verdict (against the navigation safety margin)
        safeF = _safe_frac(args.safe)
        if kind == "T2":
            ok, arg = boundA > safeF, "boundA"
        elif kind == "MONO":
            ok = all(rec["gbDefinite"][i] is not None for i in free) \
                and vmin is not None and vmin > safeF
            arg = "monoVertex"
        elif kind == "CONC":
            ok = True
            for i in free:
                hii = HB[i * 6 + i]
                if rec["gbDefinite"][i] is None and not (hii.hi[0] <= 0):
                    ok = False
            ok = ok and vmin is not None and vmin > safeF
            arg = "concVertex"
        else:  # IA / LEAF
            fblo = fB.lo_frac()
            ok, arg = max(boundA, fblo) > safeF, "boundA|fB"
        rec["certOk"] = bool(ok)
        rec["certArg"] = arg if ok else None
        if not ok:
            rec["certFail"] = ("certified %s argument <= SAFE %r "
                               "(C1 tightness)" % (arg, args.safe))
    except dyad.CertFail as e:
        rec["certFail"] = "CertFail: %s" % (e,)
    except ArithmeticError as e:
        rec["certFail"] = "%s: %s" % (type(e).__name__, e)
    except (ValueError, KeyError) as e:
        rec["certFail"] = "%s: %s" % (type(e).__name__, e)
    return rec


def enumerate_vertices(kind, boxD, info):
    """Vertex list (dyadic endpoints) mirroring the engine's MONO/CONC
    enumeration on the certificate box."""
    out = []
    free = [i for i in range(6) if boxD[i][0] != boxD[i][1]]
    mono = {int(k): v for k, v in (info.get("mono") or {}).items()}
    if kind == "MONO":
        vtx = []
        for i in range(6):
            lo, hi = boxD[i]
            if i not in mono:
                vtx.append(lo)          # degenerate slot (lo == hi)
            elif mono[i] == "lo":
                vtx.append(lo)
            else:
                vtx.append(hi)
        return [vtx]
    freevars = [i for i in free if i not in mono]
    for bits in itertools.product((0, 1), repeat=len(freevars)):
        vtx = []
        for i in range(6):
            lo, hi = boxD[i]
            if i not in free:
                vtx.append(lo)
            elif i in mono:
                vtx.append(lo if mono[i] == "lo" else hi)
            else:
                k = freevars.index(i)
                vtx.append(hi if bits[k] else lo)
        out.append(vtx)
    return out


# ------------------------------------------------------------------- main

def emit(pilot_key, args, box_override=None, sides_override=None):
    p = pilots.normalize(pilot_key, box_override, sides_override)
    expr_nav = pilots.mkexpr(p, nav.BackendF)

    t0 = time.time()
    if box_override is not None:
        nd = engine.Node(list(p["box"]), list(p["sides"]), 0)
        leaves = [("LEAF", nd, {})]
        stats = dict(nodes=0, splits=0, fixes=0, max_depth=0, open=0,
                     leaves={"LEAF": 1}, point_evals=0, corner_evals=0,
                     closed_lb=None, timeout=False)
    else:
        st = engine.solve(p["box"], expr_nav, p["sides"],
                          max_nodes=args.max_nodes,
                          L3_SAFETY=args.safety, SAFE=args.safe)
        stats = st
        leaves = st["leaves_detail"]
    nav_time = time.time() - t0

    t1 = time.time()
    recs = []
    for idx, (kind, nd, info) in enumerate(leaves):
        rec = certify_leaf(kind, nd.box, nd.sides, info, args, pilot_key)
        rec_full = {"index": idx, "depth": nd.depth}
        rec_full.update(rec)
        recs.append(rec_full)
    cert_time = time.time() - t1

    n_ok = sum(1 for r in recs if r["certOk"])
    fail_reasons = {}
    for r in recs:
        if not r["certOk"]:
            k = (r["certFail"] or "?").split(":")[0].split(" ")[0]
            fail_reasons[k] = fail_reasons.get(k, 0) + 1

    argv = sys.argv[1:]
    # `--out <path>` is bookkeeping, not computation input: exclude the pair
    # so that identical computations emit byte-identical documents.
    clean = []
    skip = False
    for a in argv:
        if skip:
            skip = False
            continue
        if a == "--out":
            skip = True
            continue
        clean.append(a)

    doc = {
        "schema": certtm2.SCHEMA,
        "generator": {
            "name": "pipeline/interval/certtm2/emit_tm2.py",
            "version": certtm2.VERSION,
            "args": clean,
        },
        "pilot": {
            "key": pilot_key,
            "name": p["name"],
            "marginTarget": p.get("margin_target"),
            "boxNav": [[jfrac(lo), jfrac(hi)] for lo, hi in p["box"]],
            "sides": list(p["sides"]),
            "w": p.get("w"), "m": p.get("m"),
            "B": jfrac(p["B"]) if "B" in p else None,
            "affine": [[k, jfrac(c)] for k, c in p.get("affine", [])],
            "const": jfrac(p["const"]) if "const" in p else None,
        },
        "params": {
            "L3Safety": args.safety,
            "SAFE": args.safe,
            "maxNodes": args.max_nodes,
            "gridExp": args.grid_exp,
            "coefGridExp": args.coef_grid,
            "floorGridExp": args.floor_grid,
            "outExp": args.out_exp,
            "rung": args.rung,
            "certMode": args.cert_mode,
            "certSplits": args.cert_splits,
        },
        "stats": {
            "nodes": stats["nodes"], "splits": stats["splits"],
            "fixes": stats["fixes"], "maxDepth": stats["max_depth"],
            "open": stats["open"], "timeout": bool(stats.get("timeout")),
            "leaves": stats["leaves"],
            "pointEvals": stats["point_evals"],
            "cornerEvals": stats["corner_evals"],
            "closedLb": stats.get("closed_lb"),
            "cert": {"ok": n_ok, "failed": len(recs) - n_ok,
                     "failReasons": fail_reasons},
        },
        "leaves": recs,
    }
    return doc, nav_time, cert_time


def check_finite(doc, path="$"):
    """Assert every float in the document is finite (no NaN/Inf leakage;
    JSON determinism then rests on repr round-trip stability)."""
    if isinstance(doc, float):
        if not math.isfinite(doc):
            raise ValueError("non-finite float at %s" % path)
    elif isinstance(doc, dict):
        for k, v in doc.items():
            check_finite(v, "%s.%s" % (path, k))
    elif isinstance(doc, list):
        for i, v in enumerate(doc):
            check_finite(v, "%s[%d]" % (path, i))


def compare_tsv(doc, path):
    """Index-wise compare against a g4port `dump_leaves` TSV (prototype
    口径): kind, depth, the 12 exact box endpoints, and the bound at
    %.10g precision.  Returns the number of mismatches."""
    rows = []
    with open(path) as f:
        header = f.readline().rstrip("\n").split("\t")
        for line in f:
            cols = line.rstrip("\n").split("\t")
            rows.append(dict(zip(header, cols)))
    bad = 0
    if len(rows) != len(doc["leaves"]):
        print("TSV compare: tsv %d leaves != json %d"
              % (len(rows), len(doc["leaves"])), file=sys.stderr)
        bad += 1
    for r, leaf in zip(rows, doc["leaves"]):
        if r["kind"] != leaf["kind"] or int(r["depth"]) != leaf["depth"]:
            print("TSV compare leaf %d: kind/depth %s/%s vs %s/%s"
                  % (leaf["index"], r["kind"], r["depth"],
                     leaf["kind"], leaf["depth"]), file=sys.stderr)
            bad += 1
            continue
        for k in range(6):
            got = leaf["boxNav"][k]
            want = [r["y%dlo" % (k + 1)], r["y%dhi" % (k + 1)]]
            if want != got:
                print("TSV compare leaf %d dim %d: box %s vs %s"
                      % (leaf["index"], k, want, got), file=sys.stderr)
                bad += 1
        if leaf.get("estBound") is None \
                or "%.10g" % leaf["estBound"] != r["bound"]:
            print("TSV compare leaf %d: bound %s vs %.10g"
                  % (leaf["index"], r["bound"], leaf.get("estBound")),
                  file=sys.stderr)
            bad += 1
    return bad


def main():
    ap = argparse.ArgumentParser(
        description="CertTM2/d2B leaf-certificate emitter (C1 supplier)")
    ap.add_argument("--pilot", required=True, choices=sorted(pilots.PILOTS))
    ap.add_argument("--safety", type=float, default=10.0,
                    help="L3 safety multiplier of the NAVIGATION engine "
                         "(the s of the s-curve; certificates do not use it)")
    ap.add_argument("--safe", type=float, default=1e-7,
                    help="closure safety margin SAFE of the navigation")
    ap.add_argument("--max-nodes", type=int, default=200000)
    ap.add_argument("--out", help="output JSON path (default stdout)")
    ap.add_argument("--box",
                    help="single-leaf mode: 12 exact endpoints, "
                         "comma separated (lo1,hi1,...,lo6,hi6)")
    ap.add_argument("--sides", help="single-leaf mode: 6 kink sides, "
                                    "comma separated")
    ap.add_argument("--grid-exp", type=int, default=-24,
                    help="outward dyadic grid for certificate box endpoints")
    ap.add_argument("--coef-grid", type=int, default=-60,
                    help="straddle grid for decimal constants / thin points")
    ap.add_argument("--floor-grid", type=int, default=-40,
                    help="grid for the deltaX corner / radicand floors")
    ap.add_argument("--out-exp", type=int, default=-80,
                    help="reciprocal / arctan granularity (tmexact out)")
    ap.add_argument("--rung", type=int, default=64,
                    help="arctan series order (|args| <= 0.71 on this lane)")
    ap.add_argument("--cert-mode", choices=["tree", "ad"], default="tree",
                    help="full-box supplier: tree = symbolic partials "
                         "evaluated over the box (C1, HOL parity); "
                         "ad = legacy interval-AD jet (wrapping comparison)")
    ap.add_argument("--cert-splits", type=int, default=0,
                    help="refine each Fraction-free dim into 2^s equal "
                         "pieces and hull the C1 enclosures (cost x4^s on "
                         "wide leaves; see VALIDATION.md)")
    ap.add_argument("--compare-tsv",
                    help="g4port leaves TSV to diff against (exact 口径)")
    args = ap.parse_args()

    box_override = sides_override = None
    if args.box is not None:
        try:
            vals = [F(s) for s in args.box.split(",")]
        except (ValueError, ZeroDivisionError):
            print("bad --box: endpoints must be exact decimals/ratials",
                  file=sys.stderr)
            return 3
        if len(vals) != 12:
            print("bad --box: need 12 endpoints", file=sys.stderr)
            return 3
        box_override = [(vals[2 * i], vals[2 * i + 1]) for i in range(6)]
        sides_override = (args.sides.split(",") if args.sides
                          else engine.default_sides(box_override))
        if len(sides_override) != 6:
            print("bad --sides: need 6 entries", file=sys.stderr)
            return 3

    doc, nav_time, cert_time = emit(args.pilot, args,
                                    box_override, sides_override)
    check_finite(doc)
    text = json.dumps(doc, indent=1, ensure_ascii=True,
                      allow_nan=False) + "\n"
    if args.out:
        outdir = os.path.dirname(os.path.abspath(args.out))
        os.makedirs(outdir, exist_ok=True)
        with open(args.out, "w") as f:
            f.write(text)
        print("wrote %s (%d leaves, nav %.1f s, cert %.1f s)"
              % (args.out, len(doc["leaves"]), nav_time, cert_time),
              file=sys.stderr)
    else:
        sys.stdout.write(text)

    s = doc["stats"]
    print("pilot %s (%s): leaves=%s nodes=%d fixes=%d depth=%d open=%d"
          % (args.pilot, doc["pilot"]["name"], s["leaves"], s["nodes"],
             s["fixes"], s["maxDepth"], s["open"]), file=sys.stderr)
    print("cert: ok=%d failed=%d reasons=%s"
          % (s["cert"]["ok"], s["cert"]["failed"], s["cert"]["failReasons"]),
          file=sys.stderr)
    if args.compare_tsv:
        bad = compare_tsv(doc, args.compare_tsv)
        print("tsv compare: %d mismatches" % bad, file=sys.stderr)
        if bad:
            return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
