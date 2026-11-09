#!/usr/bin/env python3
"""Round-2 sub-box planner/emitter for the schema-v3 hull route.

Why this exists (measured; see `~/c17_backup/lane_snapshots/biefjhu-tm/P5_DELIVERY.md`):
a stage-A leaf whose `evalTMHullFill2` output carries fewer mantissa triples
than the expression has `sqrt` nodes (`IExpr.nSqrt`) is **not kernel-closable**:
some `sqrt` node went through the mirror-only dummy-`(0,0)` fallback, which the
kernel evaluator cannot reproduce.  `Kepler.Interval.hullProbeSound` therefore
rejects such a leaf (`none`), and the fix is to bisect it: a half-width box
shrinks the Taylor remainder ~4x, which makes the `sqrt` mantissa condition
`(fB.lo - W).isPos` pass, so the sub-box reports a full triple list.

Split rule: widest dimension, exact dyadic midpoint (the `bb_arb` convention),
repeated `--levels` times (so 2^levels sub-boxes per bad leaf).  The emitted
sub-boxes are re-probed with the standard stage-A driver and then re-emitted as
a binary sub-tree of the parent leaf (the emitter's `--r2` surgery).

Usage:
  emit_round2.py <case.json> <cert.json> <outdir> --bad=8,70,127
                 [--levels=2] [--chunks=3] [--rung=128 --rung-out=-80 --gran=-80]
  emit_round2.py <case.json> <cert.json> <outdir> --from-logs=<dir>
                 [--levels=2] [--chunks=3]          # derive --bad from the logs

Writes into <outdir>:
  R2.map.json          global order: [cert leaf, path, [[lo],[hi]] per dim]
  R2c{0..c-1}.lean     probe drivers (one per chunk, run them concurrently)
  R2c{0..c-1}.idx.json chunk-local index -> global sub-box index
  R2.plan.json         the plan (bad leaves, level, split dims, counts)

Deterministic: same inputs -> byte-identical outputs; no state is read from
previous runs except the `--from-logs` bad-leaf derivation.
"""
import json
import os
import sys
from fractions import Fraction as F


def die(msg):
    sys.exit("emit_round2: " + msg)


def frac_dyadic(q):
    """Fraction -> (mantissa, exponent) with den = 2^-e (normalised: the
    Fraction is auto-reduced, so the mantissa is odd)."""
    if q.denominator <= 0 or q.denominator & (q.denominator - 1):
        die(f"non-dyadic {q}")
    e = 0
    den = q.denominator
    while den > 1:
        den >>= 1
        e -= 1
    return (q.numerator, e)


def box_frac(b):
    """JSON cert box -> tuple of exact (lo, hi) Fractions (split arithmetic)."""
    return tuple((F(d[0]["num"], d[0]["den"]),
                  F(d[1]["num"], d[1]["den"])) for d in b)


def encode_box(box):
    """Canonical JSON encoding: [[lo_num, lo_den], [hi_num, hi_den]] per dim."""
    return [[[lo.numerator, lo.denominator], [hi.numerator, hi.denominator]]
            for lo, hi in box]


def to_dyadic_box(box):
    """Fraction box -> the `(mantissa, exponent)` box shape `emit_lean` wants."""
    return tuple((frac_dyadic(lo), frac_dyadic(hi)) for lo, hi in box)


def split_once(box, n):
    """Widest dim, exact dyadic midpoint -> (dim, left, right)."""
    widths = [box[d][1] - box[d][0] for d in range(n)]
    d = max(range(n), key=lambda i: (widths[i], -i))
    lo, hi = box[d]
    mid = (lo + hi) / 2
    lb = list(box); lb[d] = (lo, mid)
    rb = list(box); rb[d] = (mid, hi)
    return d, tuple(lb), tuple(rb)


def bad_from_logs(logdir):
    """Bad leaves of a chunked round-1 run: verdict != PASS or a short triple
    list.  `logdir` holds `A{0,1,2}.idx.json` plus the driver logs next to it."""
    bad = []
    for ci in range(3):
        idxp = os.path.join(logdir, f"A{ci}.idx.json")
        if not os.path.exists(idxp):
            continue
        idxs = json.load(open(idxp))
        # logs live in the lane's logs/ dir, one level up in practice; accept both
        for cand in (os.path.join(logdir, f"A{ci}.txt"),
                     os.path.join(logdir, "..", "logs", f"stageA_chunk{ci}.log")):
            if os.path.exists(cand):
                for ln in open(cand):
                    ln = ln.strip()
                    if not ln or ln.startswith("RUNG"):
                        continue
                    tk = ln.split()
                    if tk[1] != "PASS" or len(tk[4:]) % 3:
                        bad.append(idxs[int(tk[0])])
                break
    return sorted(set(bad))


def main(argv):
    args = [a for a in argv[1:] if not a.startswith("--")]
    opts = {}
    for a in argv[1:]:
        if a.startswith("--"):
            k, _, v = a[2:].partition("=")
            opts[k] = v
    if len(args) != 3:
        die("usage: emit_round2.py <case.json> <cert.json> <outdir> "
            "--bad=…|--from-logs=… [--levels=2] [--chunks=3]")
    case_p, cert_p, outdir = args
    levels = int(opts.get("levels", "2"))
    nchunk = int(opts.get("chunks", "3"))
    rung_n = int(opts.get("rung", "128"))
    rung_out = int(opts.get("rung-out", "-80"))
    gran = int(opts.get("gran", "-80"))
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import emit_lean as EL

    if "bad" in opts:
        bad = sorted({int(x) for x in opts["bad"].split(",") if x.strip()})
    elif "from-logs" in opts:
        bad = bad_from_logs(opts["from-logs"])
    else:
        die("need --bad=… or --from-logs=…")
    if not bad:
        json.dump({"bad": [], "subboxes": []}, open(os.path.join(outdir, "R2.plan.json"), "w"))
        print("emit_round2: no bad leaves, nothing to do")
        return

    case = json.load(open(case_p))
    cert = json.load(open(cert_p))
    boxes = [box_frac(l["box"]) for l in cert["leaves"]]
    n = len(case["vars"])
    for k in bad:
        if not (0 <= k < len(boxes)):
            die(f"bad leaf index {k} out of range")
    expr, nsqrt, ndiv, ntrans = EL.hull_expr(case, rung_n, rung_out)

    subs, dims = [], {}
    def rec(leaf, box, path, depth):
        if depth == levels:
            subs.append((leaf, path, box))
            return
        d, lb, rb = split_once(box, n)
        dims.setdefault(leaf, []).append(d)
        rec(leaf, lb, path + "L", depth + 1)
        rec(leaf, rb, path + "R", depth + 1)
    for k in bad:
        rec(k, boxes[k], "", 0)
    seen, uniq = set(), []
    for leaf, path, box in subs:
        if box in seen:
            continue
        seen.add(box)
        uniq.append((leaf, path, box))
    print(f"emit_round2: {len(bad)} bad leaves -> {len(uniq)} sub-boxes "
          f"(levels={levels}, split dims {dims})")

    meta = dict(caseid="hullR2", origop=case.get("orig_op"), vars=case["vars"], prec="-")
    per = (len(uniq) + nchunk - 1) // nchunk
    os.makedirs(outdir, exist_ok=True)
    for ci in range(nchunk):
        part = list(range(ci * per, min((ci + 1) * per, len(uniq))))
        if not part:
            break
        sub = [to_dyadic_box(uniq[i][2]) for i in part]
        src = EL.hull_stage_a_file(
            f"HullR2c{ci}", n, expr, sub, gran, rung_n, rung_out,
            nsqrt, ndiv, ntrans, len(sub), meta,
            f" - round 2 chunk {ci}: {len(sub)} sub-boxes "
            f"(bad leaves {bad})")
        open(os.path.join(outdir, f"R2c{ci}.lean"), "w").write(src)
        json.dump(part, open(os.path.join(outdir, f"R2c{ci}.idx.json"), "w"))
        print(f"  R2c{ci}.lean: {len(sub)} sub-boxes (global {part[0]}..{part[-1]})")
    json.dump([[leaf, path, encode_box(box)] for leaf, path, box in uniq],
              open(os.path.join(outdir, "R2.map.json"), "w"))
    json.dump({"bad": bad, "levels": levels, "split_dims": dims,
               "subboxes": len(uniq), "rung": [rung_n, rung_out], "gran": gran,
               "nSqrt": nsqrt, "nDiv": ndiv, "nTrans": ntrans},
              open(os.path.join(outdir, "R2.plan.json"), "w"))
    print("emit_round2: wrote R2.map.json / R2.plan.json / R2c*.lean in", outdir)


if __name__ == "__main__":
    main(sys.argv)
