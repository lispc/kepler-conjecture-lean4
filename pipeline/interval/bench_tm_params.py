#!/usr/bin/env python3
"""Generation-time benchmark for `emit_tm_params.py` (generate only, no
kernel compile).  Loads the AST once, then for each leaf box of the
certificate runs the bit-exact `evalFill2D` and prints CSV:

  leaf,gen_s,lb,pass,ntriples,salv

Usage: python3 pipeline/interval/bench_tm_params.py --cert <full.cert.json> \
    --leaves 0-19
"""
import argparse
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import tmexact as T          # noqa: E402
from parse_expr import load_expr  # noqa: E402


def dy(fr):
    den = fr.denominator
    e = 0
    while den > 1:
        den //= 2
        e -= 1
    return (fr.numerator, e)


def fval(d):
    return float(F(d[0]) * F(2) ** d[1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expr", required=True)
    ap.add_argument("--cert", required=True)
    ap.add_argument("--leaves", default="0-19")
    args = ap.parse_args()

    if "-" in args.leaves and "," not in args.leaves:
        lo, hi = args.leaves.split("-")
        leaves = list(range(int(lo), int(hi) + 1))
    else:
        leaves = [int(x) for x in args.leaves.split(",")]
    import json
    cert = json.load(open(args.cert))
    t0 = time.time()
    ast = load_expr(args.expr, name=None)
    load_s = time.time() - t0
    # AST node counts = template sizes (79 / 165 / 143 for this expression)
    caps = [0, 0, 0]
    stack = [ast]
    while stack:
        op, a = stack.pop()
        if op == ".sqrt":
            caps[0] += 1
        elif op == ".div":
            caps[1] += 1
        elif op == ".trans":
            caps[2] += 1
        for x in a:
            if isinstance(x, tuple):
                stack.append(x)
    caps = tuple(caps)
    print("# ast_load_s=%.3f caps=%s" % (load_s, caps))
    print("leaf,gen_s,verify_s,lb,pass,ntriples,salv")
    for idx in leaves:
        box = [(dy(F(s[0]["num"], s[0]["den"])), dy(F(s[1]["num"], s[1]["den"])))
               for s in cert["leaves"][idx]["box"]]
        t = time.time()
        r = T.evalFill2D(ast, box, caps)
        dt = time.time() - t
        if r is None:
            print("%d,%.3f,,FAIL,,," % (idx, dt))
            continue
        M, loa, ps, rep, entries, salv = r
        lb = T.loBound(M, box)
        tv = time.time()
        ok = T.checkPosTMHullC(ast, box, {"sqrt": entries, "inv": caps[1],
                                          "trans": caps[2]})
        dv = time.time() - tv
        print("%d,%.3f,%.3f,%.12g,%s,%d,%d" %
              (idx, dt, dv, fval(lb), ok, len(entries), salv))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
