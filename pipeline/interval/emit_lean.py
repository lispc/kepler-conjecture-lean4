#!/usr/bin/env python3
"""Phase 4, G4: bb_arb cert JSON -> Lean certificate shards (arb-layer.md §4).

v1 scope (pilot): single-goal ("main") cases, ops
{push_var, push_const, add, sub, mul, neg, abs, div, ite};
dyadic consts inline, non-dyadic consts as exact `div` of int consts.
sqrt / trans (atan/sin/cos/ln) / disj goals are rejected for now:
- sqrt needs *per-leaf* mantissa certs (IExpr.sqrt bakes s₁ s₂ into the
  expression, but the radicand interval varies per leaf) — cert-layer
  extension pending;
- trans works in principle (fixed N/out across leaves) but is untested.

Usage: emit_lean.py <case.json> <cert.json> <out.lean> [--name NAME]
"""
import json
import sys
from fractions import Fraction


def die(msg):
    sys.exit(f"emit_lean: {msg}")


def dyadic(num, den):
    """num/den -> (m, e) with den = 2^-e, or None if not dyadic."""
    if den <= 0 or den & (den - 1):
        return None
    e = 0
    while den > 1:
        den >>= 1
        e -= 1
    return (num, e)


class Leaf:
    def __init__(self, box):
        self.box = box  # tuple of (lo, hi) Fractions
        self.nleaves = 1


class Node:
    def __init__(self, box, d, l, r):
        self.box, self.d, self.l, self.r = box, d, l, r
        self.nleaves = l.nleaves + r.nleaves


def cut_shards(t, max_leaves):
    """Top-down shard cut: subtrees with <= max_leaves leaves become shards.
    Returns list of shard subtrees in left-to-right order; the skeleton is
    the tree with shard subtrees conceptually replaced by opaque leaves."""
    shards = []

    def walk(u):
        if isinstance(u, Leaf) or u.nleaves <= max_leaves:
            if not isinstance(u, Leaf):
                shards.append(u)
            return
        walk(u.l)
        walk(u.r)

    walk(t)
    if not shards:  # root itself fits — caller should use single-file mode
        shards.append(t)
    return shards


def reconstruct(box, leaves):
    """Rebuild the bb_arb bisection tree from the flat leaf list.

    `box`: tuple of (lo, hi) Fractions (the node box).
    `leaves`: set of leaf boxes (same repr) contained in `box`.
    Splits are exact dyadic midpoints; any dimension that separates all
    leaves without straddle yields a valid `splitOK` node (we prefer the
    widest, mimicking bb_arb).
    """
    if len(leaves) == 1:
        (only,) = leaves
        if only != box:
            die(f"reconstruct: singleton leaf != node box\n  leaf={only}\n  node={box}")
        return Leaf(box)
    n = len(box)
    cands = []
    for d in range(n):
        lo, hi = box[d]
        mid = (lo + hi) / 2
        left, right, straddle = set(), set(), False
        for leaf in leaves:
            llo, lhi = leaf[d]
            if lhi <= mid:
                left.add(leaf)
            elif llo >= mid:
                right.add(leaf)
            else:
                straddle = True
                break
        if not straddle and left and right and len(left) + len(right) == len(leaves):
            cands.append((hi - lo, d, left, right))
    if not cands:
        die(f"reconstruct: no clean split dim for box {box} with {len(leaves)} leaves")
    cands.sort(key=lambda c: -c[0])
    _, d, left, right = cands[0]
    lo, hi = box[d]
    mid = (lo + hi) / 2
    lbox = box[:d] + ((lo, mid),) + box[d + 1:]
    rbox = box[:d] + ((mid, hi),) + box[d + 1:]
    return Node(box, d, reconstruct(lbox, left), reconstruct(rbox, right))


def frac_dyadic(fr):
    """Fraction -> (m, e) dyadic mantissa/exponent (denominator must be 2^k)."""
    den = fr.denominator
    if den & (den - 1):
        die(f"non-dyadic fraction {fr} in cert box")
    e = 0
    while den > 1:
        den >>= 1
        e -= 1
    return (fr.numerator, e)


def box_frac(b):
    """JSON box interval [{num,den},{num,den}] -> (Fraction, Fraction)."""
    return (Fraction(b[0]["num"], b[0]["den"]), Fraction(b[1]["num"], b[1]["den"]))


def box_lit(box):
    """Fraction box tuple -> Lean `(Fin n -> DInterval)` literal."""
    ivs = []
    for lo, hi in box:
        dm, de = frac_dyadic(lo)
        em, ee = frac_dyadic(hi)
        ivs.append(f"⟨⟨{dm}, {de}⟩, ⟨{em}, {ee}⟩⟩")
    return "![" + ", ".join(ivs) + "]"


def emit_tree(t, depth=0):
    """Nested `BBTree` constructor text with inline per-leaf `by decide`."""
    if isinstance(t, Leaf):
        return f"(.leaf {box_lit(t.box)} (by decide))"
    pad = "  " * min(depth + 1, 20)
    return (f"(.node {box_lit(t.box)} {t.d}\n{pad}{emit_tree(t.l, depth + 1)}\n"
            f"{pad}{emit_tree(t.r, depth + 1)})")


class RPN:
    """RPN prog -> IExpr text. Stack machine; each entry is a Lean term str."""

    def __init__(self, div_out=-64):
        self.div_out = div_out

    def const(self, c):
        num, den = c["num"], c["den"]
        d = dyadic(num, den)
        if d is not None:
            return f"(.const ⟨{d[0]}, {d[1]}⟩)"
        # non-dyadic rational: exact interval division of int consts
        return (f"(.div (.const ⟨{num}, 0⟩) (.const ⟨{den}, 0⟩) "
                f"({self.div_out}))")

    def emit(self, prog):
        st = []
        for ins in prog:
            if isinstance(ins, dict):
                if "ite" not in ins:
                    die(f"unknown dict instr {list(ins)}")
                c = self.emit(ins["ite"]["cond"])
                t = self.emit(ins["ite"]["then"])
                e = self.emit(ins["ite"]["else"])
                st.append(f"(.ite {c} {t} {e})")
                continue
            op = ins[0]
            if op == "push_var":
                st.append(f"(.var {ins[1]})")
            elif op == "push_const":
                st.append(self.const(ins[1]))
            elif op in ("add", "sub", "mul"):
                b, a = st.pop(), st.pop()
                st.append(f"(.{op} {a} {b})")
            elif op == "neg":
                st.append(f"(.neg {st.pop()})")
            elif op == "abs":
                st.append(f"(.abs {st.pop()})")
            elif op == "div":
                b, a = st.pop(), st.pop()
                st.append(f"(.div {a} {b} ({self.div_out}))")
            elif op in ("sqrt", "atan", "sin", "cos", "ln"):
                die(f"op {op}: not supported in v1 (see module docstring)")
            else:
                die(f"unknown op {op}")
        if len(st) != 1:
            die(f"RPN stack imbalance: {len(st)}")
        return st[0]


def box_lean(box):
    """JSON box [[{num,den},{num,den}],..] -> (Fin n -> DInterval) literal."""
    ivs = []
    for lo, hi in box:
        dlo, dhi = dyadic(lo["num"], lo["den"]), dyadic(hi["num"], hi["den"])
        if dlo is None or dhi is None:
            die("box endpoint not dyadic (expected q-expanded dyadic box)")
        ivs.append(f"⟨⟨{dlo[0]}, {dlo[1]}⟩, ⟨{dhi[0]}, {dhi[1]}⟩⟩")
    return "![" + ", ".join(ivs) + "]"


HDR = """/-
  Phase 4, G4 certificate (auto-generated by pipeline/interval/emit_lean.py).
  case: {caseid}  (orig_op: {origop}, vars: {vars})
  cert: {nleaves} leaf/leaves, prec {prec} (bb_arb){extra}
  Do not edit by hand.
-/
"""


def base_file(mod, n, expr, box):
    return (HDR + "import Kepler.Interval.CertBool\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- The case expression (RPN prog mirrored as `IExpr`). -/\n"
            f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
            f"/-- The target box (dyadic q-expansion of the original decimal box). -/\n"
            f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
            "end Kepler.Interval.Cases\n")


def shard_file(mod, k, sub):
    return (HDR + f"import Kepler.Interval.Cases.{mod}.Base\n\n"
            "set_option maxHeartbeats 0\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- Shard {k} subtree (leaf certs are inline kernel `decide`s). -/\n"
            f"def {mod}Shard{k}Tree : BBTree _ {mod}Expr :=\n  {emit_tree(sub)}\n\n"
            f"/-- Covering of shard {k}: one kernel `decide` via `CertBool.coversB`. -/\n"
            f"theorem {mod}Shard{k}Covers : {mod}Shard{k}Tree.covers :=\n"
            "  BBTree.coversB_sound _ (by decide)\n\n"
            "end Kepler.Interval.Cases\n")


def main():
    shard_leaves = 128
    args = []
    for a in sys.argv[1:]:
        if a.startswith("--shard-leaves="):
            shard_leaves = int(a.split("=", 1)[1])
        elif not a.startswith("--"):
            args.append(a)
    if len(args) != 3:
        die("usage: emit_lean.py <case.json> <cert.json> <out.lean> [--shard-leaves=N]")
    case = json.load(open(args[0]))
    cert = json.load(open(args[1]))
    cid = args[0].split("/")[-1].replace(".json", "")
    mod = "C" + "".join(ch if ch.isalnum() else "x" for ch in cid)

    if case.get("disj"):
        die("disj case: v1 handles main-only certs (BBTreeD path pending)")
    hits = {l["hit"] for l in cert["leaves"]}
    if hits != {"main"}:
        die(f"cert hits {hits}: v1 main-only")
    if cert["root_box"] != case["box"]:
        die("cert root_box != case box")
    n = len(case["vars"])

    rpn = RPN()
    expr = rpn.emit(case["prog"])
    box = box_lean(case["box"])
    hdr = dict(caseid=case["id"], origop=case.get("orig_op"), vars=case["vars"],
               nleaves=len(cert["leaves"]), prec=cert.get("prec"), extra="")

    leaves = cert["leaves"]
    rootfrac = tuple(box_frac(iv) for iv in cert["root_box"])
    leafset = {tuple(box_frac(iv) for iv in l["box"]) for l in leaves}
    if len(leafset) != len(leaves):
        die(f"duplicate leaf boxes: {len(leaves) - len(leafset)}")
    t = reconstruct(rootfrac, leafset)

    outpath = args[2]
    if t.nleaves > shard_leaves:
        emit_sharded(t, mod, n, expr, box, hdr, outpath, shard_leaves)
        return

    if t.nleaves == 1:
        tree, cert_thm, covers_thm = pilot_single_leaf(mod, box)
    else:
        tree = emit_tree(t)
        cert_thm = ""
        covers_thm = (f"/-- Covering of the whole tree, one kernel `decide`\n"
                      f"through the Bool checker (`CertBool.coversB`). -/\n"
                      f"theorem {mod}_covers : {mod}Tree.covers :=\n"
                      f"  BBTree.coversB_sound _ (by decide)")

    out = (HDR + "import Kepler.Interval.CertBool\n\nset_option maxHeartbeats 0\n\n"
           "namespace Kepler.Interval.Cases\n\n"
           f"/-- The case expression (RPN prog mirrored as `IExpr`). -/\n"
           f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
           f"/-- The target box (dyadic q-expansion of the original decimal box). -/\n"
           f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
           f"{cert_thm}\n\n"
           f"/-- The certificate tree (leaf certs are inline kernel `decide`s). -/\n"
           f"def {mod}Tree : BBTree {n} {mod}Expr :=\n  {tree}\n\n"
           f"{covers_thm}\n\n"
           f"/-- Box containment is reflexive here (tree root = target box). -/\n"
           f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
           "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
           f"/-- End-to-end: the case expression is strictly positive on the whole box. -/\n"
           f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
           f"    0 < ({mod}Expr).evalReal ρ :=\n"
           f"  bb_sound {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ\n\n"
           f"#print axioms {mod}_pos\n\nend Kepler.Interval.Cases\n")
    open(outpath, "w").write(out.format(**hdr) if "{caseid}" in out else out)
    print(f"emit_lean: wrote {outpath} (module Kepler.Interval.Cases.{mod})")


def emit_sharded(t, mod, n, expr, box, hdr, outpath, shard_leaves):
    import os
    shards = cut_shards(t, shard_leaves)
    shard_idx = {id(u): i + 1 for i, u in enumerate(shards)}
    base = os.path.splitext(outpath)[0]  # .../Cases/<mod>
    os.makedirs(base, exist_ok=True)

    open(os.path.join(base, "Base.lean"), "w").write(
        base_file(mod, n, expr, box).format(**hdr))

    for i, u in enumerate(shards, 1):
        open(os.path.join(base, f"Shard{i}.lean"), "w").write(
            shard_file(mod, i, u).format(**hdr))

    def skel_tree(u):
        if id(u) in shard_idx:
            return f"{mod}Shard{shard_idx[id(u)]}Tree"
        if isinstance(u, Leaf):
            return f"(.leaf {box_lit(u.box)} (by decide))"
        return f"(.node {box_lit(u.box)} {u.d} {skel_tree(u.l)} {skel_tree(u.r)})"

    def skel_proof(u):
        if id(u) in shard_idx:
            return f"{mod}Shard{shard_idx[id(u)]}Covers"
        if isinstance(u, Leaf):
            return "trivial"
        return (f"⟨splitOKB_sound (by decide), {skel_proof(u.l)}, "
                f"{skel_proof(u.r)}⟩")

    imports = "\n".join(f"import Kepler.Interval.Cases.{mod}.Shard{i}"
                        for i in range(1, len(shards) + 1))
    root = (HDR + imports + "\n\nset_option maxHeartbeats 0\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- The certificate tree, assembled from {len(shards)} shard subtrees. -/\n"
            f"def {mod}Tree : BBTree {n} {mod}Expr :=\n  {skel_tree(t)}\n\n"
            f"/-- Covering: per-shard `coversB` certificates glued by `splitOKB`\n"
            f"on the {len(shards)}-way skeleton. -/\n"
            f"theorem {mod}_covers : {mod}Tree.covers :=\n  {skel_proof(t)}\n\n"
            f"/-- Box containment is reflexive here (tree root = target box). -/\n"
            f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
            "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
            f"/-- End-to-end: the case expression is strictly positive on the whole box. -/\n"
            f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
            f"    0 < ({mod}Expr).evalReal ρ :=\n"
            f"  bb_sound {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ\n\n"
            f"#print axioms {mod}_pos\n\nend Kepler.Interval.Cases\n")
    open(outpath, "w").write(root.format(**hdr))
    print(f"emit_lean: wrote {outpath} + Base/Shard1..{len(shards)} "
          f"({t.nleaves} leaves, {len(shards)} shards)")


def pilot_single_leaf(mod, box):
    tree = f".leaf {mod}Box {mod}_cert"
    cert_thm = (f"/-- Whole-box positivity certificate (kernel `decide`). -/\n"
                f"theorem {mod}_cert : checkPos {mod}Expr {mod}Box = true := by\n"
                f"  decide")
    covers_thm = (f"/-- A single leaf trivially covers itself. -/\n"
                  f"theorem {mod}_covers : {mod}Tree.covers :=\n"
                  f"  trivial")
    return tree, cert_thm, covers_thm


if __name__ == "__main__":
    main()
