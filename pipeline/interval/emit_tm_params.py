#!/usr/bin/env python3
"""Emit a kernel-checkable `TMParams` (and optionally the full leaf module)
for one TSKAJXY / `atan1_box` leaf box, using the bit-exact Python replica
`tmexact.py` of `evalTMHullFill2D`.

Semantics produced (see VALIDATION.md):
  * `sqrtCerts` = one `SqrtTMP` per *visited* `sqrt` node in the evaluator's
    traversal order (guard first at `ite`, argument before node, left before
    right).  A TM-route node carries `(sqrtMantissaRel fB.lo,
    sqrtMantissaRel fB.hi, sqrtMantissaRel (fB.lo - W))`; a fallback node
    (certified lower bound `<= 0`, so the kernel ignores the triple) carries
    the placeholder `(0, 0, 0)`.  Guard-arm `sqrt` nodes carry
    `(sqrtMantissa I.lo, sqrtMantissa I.hi, 0)` and are consumed by
    `evalIParams`.
  * `invCerts` / `transCerts` = `List.replicate` of the fixed `(-80)` bundles
    (same shape as the landed `kParams0` / `kParams657`), sized by the AST's
    div / trans node counts (the template size of the probe).

Usage:
  python3 pipeline/interval/emit_tm_params.py --expr <Base.lean> \
      --cert <full.cert.json> --leaf 0 [--tag 0] [--out params.lean] \
      [--module Leaf.lean]
  python3 pipeline/interval/emit_tm_params.py --expr <Base.lean> \
      --box '[⟨⟨m, e⟩, ⟨m, e⟩⟩, ...]'

Exit codes: 0 emitted, 2 generation failed (node path printed), 3 bad input.
The tool is untrusted: correctness is decided by the kernel `decide` replay.
"""
import argparse
import json
import os
import re
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import tmexact as T          # noqa: E402
from parse_expr import load_expr  # noqa: E402

INV_TMP = "⟨(-80), (-80), (-80)⟩"
TRANS_TMP = "⟨(-80), (-80)⟩"


def dy(fr):
    den = fr.denominator
    e = 0
    while den > 1:
        if den % 2:
            raise SystemExit("non-dyadic box endpoint: %s" % (fr,))
        den //= 2
        e -= 1
    return (fr.numerator, e)


def box_from_cert(path, idx):
    cert = json.load(open(path))
    leaf = cert["leaves"][idx]
    return [(dy(F(s[0]["num"], s[0]["den"])), dy(F(s[1]["num"], s[1]["den"])))
            for s in leaf["box"]]


def box_from_literal(s):
    ivs = re.findall(r"⟨⟨(-?\d+), (-?\d+)⟩, ⟨(-?\d+), (-?\d+)⟩⟩", s)
    if not ivs:
        raise SystemExit("could not parse --box literal")
    return [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in ivs]


def ast_counts(ast):
    c = {"sqrt": 0, "div": 0, "trans": 0}
    stack = [ast]
    while stack:
        op, args = stack.pop()
        if op == ".sqrt":
            c["sqrt"] += 1
        elif op == ".div":
            c["div"] += 1
        elif op == ".trans":
            c["trans"] += 1
        for a in args:
            if isinstance(a, tuple):
                stack.append(a)
    return c


def fmt_triple(t):
    return "⟨%d, %d, %d, (-80), (-80)⟩" % t


def params_text(tag, entries, n_inv, n_tr):
    if entries:
        certs = ",\n    ".join(fmt_triple(t) for t in entries)
        body = "[" + certs + "]"
    else:
        body = "[]"
    return ("def kParams%s : TMParams :=\n"
            "  ⟨%s,\n"
            "   List.replicate %d %s,\n"
            "   List.replicate %d %s⟩\n"
            % (tag, body, n_inv, INV_TMP, n_tr, TRANS_TMP))


def box_text(tag, box):
    ivs = ", ".join("⟨⟨%d, %d⟩, ⟨%d, %d⟩⟩" % (lo[0], lo[1], hi[0], hi[1])
                    for lo, hi in box)
    return "def kBox%s : Fin %d → DInterval :=\n  ![%s]\n" % (tag, len(box), ivs)


def module_text(tag, expr_name, leaf_label, entries, n_inv, n_tr, box,
                base_mod):
    head = '''import Kepler.Interval.Cases.%s
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! TSKAJXY-XLLIPLS `atan1_box` leaf %s — kernel-checked leaf.

`TMParams.sqrtCerts` were produced off-kernel by the bit-exact Python
replica of `evalTMHullFill2D` (`emit_tm_params.py` + `tmexact.py`);
the kernel `decide` below is the acceptance criterion. -/

open Kepler.Interval
namespace Kepler.Interval.Cases

-- `private` mangles the name per module, so generated leaf modules do not
-- clash on import.
private instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

''' % (base_mod, leaf_label)
    tail = '''
end Kepler.Interval.Cases

open Kepler.Interval Kepler.Interval.Cases

/-- **Leaf %s passes** under the C hull checker. -/
theorem tskaJXY_xllipls_leaf%s_check :
    checkPosTMHullC %s kBox%s kParams%s = true := by
  decide +kernel

/-- Positivity of the expression everywhere in the box
(`checkPosTMHullC_sound`, `CertTM:4530`). -/
theorem tskaJXY_xllipls_leaf%s_pos (ρ : Fin %d → ℝ) (hρ : boxMem kBox%s ρ) :
    0 < %s.evalReal ρ :=
  checkPosTMHullC_sound tskaJXY_xllipls_leaf%s_check ρ hρ

#print axioms tskaJXY_xllipls_leaf%s_check
#print axioms tskaJXY_xllipls_leaf%s_pos
''' % (leaf_label, tag, expr_name, tag, tag, tag, len(box), tag,
       expr_name, tag, tag, tag)
    return head + params_text(tag, entries, n_inv, n_tr) + "\n" + \
        box_text(tag, box) + tail


def params_text_p(tag, entries, n_inv, n_tr, point_entries):
    """The landed 3-field literal + the Rule P wrapper with point certs."""
    base = params_text(tag, entries, n_inv, n_tr)
    if point_entries:
        certs = ",\n    ".join(fmt_triple(t) for t in point_entries)
        pbody = "[" + certs + "]"
    else:
        pbody = "[]"
    return (base +
            "\n/-- Rule P wrapper: point-evaluation sqrt certs. -/\n"
            "def kParams%sP : TMParamsP := ⟨kParams%s, %s⟩\n"
            % (tag, tag, pbody))


def module_text_p(tag, expr_name, leaf_label, entries, n_inv, n_tr,
                  point_entries, box, base_mod, rung):
    head = '''import Kepler.Interval.Cases.%s
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! TSKAJXY-XLLIPLS `atan1_box` leaf %s — kernel-checked leaf, **Rule P**.

`TMParams.sqrtCerts` (main box) and `TMParamsP.pointCerts` (degenerate
center box) were produced off-kernel by the bit-exact Python replica of
`evalTMHullD2P` (`emit_tm_params.py` + `tmexact.py`, point rung %d);
the kernel `decide` below is the acceptance criterion. -/

open Kepler.Interval
namespace Kepler.Interval.Cases

-- `private` mangles the name per module, so generated leaf modules do not
-- clash on import.
private instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩

''' % (base_mod, leaf_label, rung)
    tail = '''
end Kepler.Interval.Cases

open Kepler.Interval Kepler.Interval.Cases

/-- **Leaf %s passes** under the Rule P hull checker. -/
theorem tskaJXY_xllipls_p_leaf%s_check :
    checkPosTMHullP %d %s kBox%s kParams%sP = true := by
  decide +kernel

/-- Positivity of the expression everywhere in the box
(`checkPosTMHullP_sound`, opt-in Rule P checker). -/
theorem tskaJXY_xllipls_p_leaf%s_pos (ρ : Fin %d → ℝ) (hρ : boxMem kBox%s ρ) :
    0 < %s.evalReal ρ :=
  checkPosTMHullP_sound tskaJXY_xllipls_p_leaf%s_check ρ hρ

#print axioms tskaJXY_xllipls_p_leaf%s_check
#print axioms tskaJXY_xllipls_p_leaf%s_pos
''' % (leaf_label, tag, rung, expr_name, tag, tag, tag, len(box), tag,
       expr_name, tag, tag, tag)
    return head + params_text_p(tag, entries, n_inv, n_tr, point_entries) + \
        "\n" + box_text(tag, box) + tail


def fval(d):
    return float(F(d[0]) * F(2) ** d[1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expr", required=True)
    ap.add_argument("--expr-name", default=None)
    ap.add_argument("--cert")
    ap.add_argument("--leaf", type=int)
    ap.add_argument("--box")
    ap.add_argument("--tag", default=None)
    ap.add_argument("--out")
    ap.add_argument("--module")
    ap.add_argument("--base-mod", default="TskXLLIPLSAtan1Base")
    ap.add_argument("--label", default=None)
    ap.add_argument("--rule", choices=["C", "P"], default="C",
                    help="C = landed df-hull checker; P = opt-in point-anchored "
                         "Rule P (point certs + point rung)")
    ap.add_argument("--rung", type=int, default=8192,
                    help="point-evaluation trans rung R (Rule P only; the "
                         "landed AST rung is ignored on the point path)")
    ap.add_argument("--no-verify", action="store_true",
                    help="skip the in-process kernel replay oracle")
    args = ap.parse_args()

    if args.box is not None:
        box = box_from_literal(args.box)
    elif args.cert is not None and args.leaf is not None:
        box = box_from_cert(args.cert, args.leaf)
    else:
        ap.error("need --box or --cert + --leaf")

    ast = load_expr(args.expr, name=args.expr_name)
    counts = ast_counts(ast)
    caps = (counts["sqrt"], counts["div"], counts["trans"])
    tag = args.tag if args.tag is not None else (
        str(args.leaf) if args.leaf is not None else "X")
    label = args.label if args.label is not None else tag
    expr_name = args.expr_name
    if expr_name is None:
        m = re.search(r"def (\w+Expr)", open(args.expr).read())
        expr_name = m.group(1)

    t0 = time.time()
    if args.rule == "P":
        r = T.evalFill2DP(ast, box, caps, args.rung)
        dt = time.time() - t0
        if r is None:
            path, reason = T.blame_path(ast, box, caps)
            print("GENERATION FAILED (Rule P): %s" % reason)
            print("  node path: %s" % ("/".join(path) if path else "<root>"))
            return 2
        M, loa, ps, entries, pentries, salv = r
        lb = T.loBound(M, box)
        tv = time.time()
        ok = True if args.no_verify else T.checkPosTMHullP(
            ast, box, {"sqrt": entries, "inv": counts["div"],
                       "trans": counts["trans"], "point": pentries},
            args.rung)
        dv = time.time() - tv
        print("box %s (Rule P, R=%d): lb=%s (%.10g) salv=%d sqrtCerts=%d "
              "pointCerts=%d invSlots=%d transSlots=%d" %
              (tag, args.rung, lb, fval(lb), salv, len(entries),
               len(pentries), counts["div"], counts["trans"]))
        print("kernel replay oracle checkPosTMHullP = %s   gen %.3f s + "
              "verify %.3f s" % (ok, dt, dv))
        if not ok:
            print("WARNING: replica replay rejects the generated params "
                  "(do not ship this leaf)")
            return 2
        params = params_text_p(tag, entries, counts["div"], counts["trans"],
                               pentries)
        boxdef = box_text(tag, box)
        if args.out:
            open(args.out, "w").write(params + "\n" + boxdef)
            print("wrote", args.out)
        if args.module:
            open(args.module, "w").write(
                module_text_p(tag, expr_name, label, entries, counts["div"],
                              counts["trans"], pentries, box, args.base_mod,
                              args.rung))
            print("wrote", args.module)
        if not args.out and not args.module:
            sys.stdout.write(params + "\n" + boxdef)
        return 0

    r = T.evalFill2D(ast, box, caps)
    dt = time.time() - t0
    if r is None:
        path, reason = T.blame_path(ast, box, caps)
        print("GENERATION FAILED: %s" % reason)
        print("  node path: %s" % ("/".join(path) if path else "<root>"))
        return 2
    M, loa, ps, reported, entries, salv = r
    lb = T.loBound(M, box)
    tv = time.time()
    ok = True if args.no_verify else T.checkPosTMHullC(
        ast, box, {"sqrt": entries, "inv": counts["div"],
                   "trans": counts["trans"]})
    dv = time.time() - tv
    print("box %s: lb=%s (%.10g) salv=%d sqrtCerts=%d (reported %d) "
          "invSlots=%d transSlots=%d" %
          (tag, lb, fval(lb), salv, len(entries), len(reported),
           counts["div"], counts["trans"]))
    print("kernel replay oracle checkPosTMHullC = %s   gen %.3f s + verify "
          "%.3f s" % (ok, dt, dv))
    if not ok:
        print("WARNING: replica replay rejects the generated params "
              "(do not ship this leaf)")
        return 2

    params = params_text(tag, entries, counts["div"], counts["trans"])
    boxdef = box_text(tag, box)
    if args.out:
        open(args.out, "w").write(params + "\n" + boxdef)
        print("wrote", args.out)
    if args.module:
        open(args.module, "w").write(
            module_text(tag, expr_name, label, entries, counts["div"],
                        counts["trans"], box, args.base_mod))
        print("wrote", args.module)
    if not args.out and not args.module:
        sys.stdout.write(params + "\n" + boxdef)
    return 0


if __name__ == "__main__":
    sys.exit(main())
