#!/usr/bin/env python3
"""Phase 4, G4: bb_arb cert JSON -> Lean certificate shards (arb-layer.md §4).

v1 scope (pilot): single-goal ("main") cases, ops
{push_var, push_const, add, sub, mul, neg, abs, div, ite};
dyadic consts inline, non-dyadic consts as exact `div` of int consts.

v2 (FillParams pipeline, `--fill`): ops sqrt/atan/sin/cos/ln accepted.
- `sqrt` slots become *parameters*: Stage A (`--stage-a`) emits a Lean
  driver whose `fillMkExpr N out` has dummy `(0, 0)` mantissas; running it
  (`lake env lean --run`) recomputes the exact per-leaf mantissas with the
  tracing evaluator of `Kepler.Interval.Tools.FillParams` and walks an
  `(N, out)` rung ladder for the `trans` nodes.
- Stage B (`--bbg --params FILE`) reads that output and emits `BBTreeG`
  shards: `Base` carries `{mod}MkExpr (ms : Vector (Int × Int) k)` with the
  sqrt slots fed from `ms` (RPN/post order), a dummy-parameter global
  `{mod}Expr`, and a one-shot `rfl` lemma `{mod}_sem` closing every leaf's
  `hsame`; leaves are `.leaf box ({mod}MkExpr #v[..]) ({mod}_sem _)
  (by decide)`.
- `--leaves N` samples: take the first N cert leaves, shrink the root box
  to the smallest bisection-grid box containing them, then extend the
  sample to ALL cert leaves inside that box (a complete partition, so tree
  reconstruction still works); the target box of the emitted theorem is the
  shrunk box.

Usage: emit_lean.py <case.json> <cert.json> <out.lean> [--name NAME]
       [--shard-leaves=N] [--leaves=N] [--fill] [--stage-a]
       [--bbg --params=FILE]
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
    def __init__(self, box, hit="main", cert_box=None):
        self.box = box  # tuple of (lo, hi) dyadic (m, e) pairs (tree-construction form)
        self.cert_box = cert_box if cert_box is not None else box  # cert-origin key
        self.hit = hit  # 'main' | 'disj:K' | 'var_lt:I,J'
        self.nleaves = 1


def box_eq(a, b):
    """Value equality of dyadic-pair boxes (forms may differ)."""
    return all(dcmp(a[d][0], b[d][0]) == 0 and dcmp(a[d][1], b[d][1]) == 0
               for d in range(len(a)))


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
    `leaves`: dict leaf box -> hit string, all contained in `box`.
    Splits are exact dyadic midpoints; any dimension that separates all
    leaves without straddle yields a valid `splitOK` node (we prefer the
    widest, mimicking bb_arb).
    """
    if len(leaves) == 1:
        (only, hit), = leaves.items()
        if not box_eq(only, box):
            die(f"reconstruct: singleton leaf != node box\n  leaf={only}\n  node={box}")
        return Leaf(box, hit, cert_box=only)
    n = len(box)
    cands = []
    for d in range(n):
        lo, hi = box[d]
        mid = dmid(lo, hi)
        left, right, straddle = {}, {}, False
        for leaf, hit in leaves.items():
            llo, lhi = leaf[d]
            if dcmp(lhi, mid) <= 0:
                left[leaf] = hit
            elif dcmp(llo, mid) >= 0:
                right[leaf] = hit
            else:
                straddle = True
                break
        if not straddle and left and right and len(left) + len(right) == len(leaves):
            cands.append((dval(hi) - dval(lo), d, left, right, mid))
    if not cands:
        die(f"reconstruct: no clean split dim for box {box} with {len(leaves)} leaves")
    cands.sort(key=lambda c: -c[0])
    _, d, left, right, mid = cands[0]
    lo, hi = box[d]
    lbox = box[:d] + ((lo, mid),) + box[d + 1:]
    rbox = box[:d] + ((mid, hi),) + box[d + 1:]
    return Node(box, d, reconstruct(lbox, left), reconstruct(rbox, right))


def frac_dyadic(fr):
    """Fraction -> (m, e) dyadic mantissa/exponent (denominator must be 2^k).
    The Fraction is auto-reduced, so the result is the *normalised* form
    (odd mantissa or zero) — matching `frac_dyadic` canonical endpoints."""
    den = fr.denominator
    if den & (den - 1):
        die(f"non-dyadic fraction {fr} in cert box")
    e = 0
    while den > 1:
        den >>= 1
        e -= 1
    return (fr.numerator, e)


def dval(d):
    """Dyadic (m, e) -> Fraction value."""
    m, e = d
    return Fraction(m * (1 << e), 1) if e >= 0 else Fraction(m, 1 << (-e))


def dcmp(a, b):
    """Compare dyadics a b: -1/0/1 (exact, exponent-aligned)."""
    me = min(a[1], b[1])
    x = (a[0] << (a[1] - me)) - (b[0] << (b[1] - me))
    return (x > 0) - (x < 0)


def dmid(lo, hi):
    """Exact midpoint in `DInterval.midRadius.c` form: mantissa aligned to
    `min e` and exponent decremented — **not** normalised.  Emitted child
    endpoints MUST use this form, because the kernel compares them
    structurally against `midRadius.c` of the (equally emitted) parent."""
    me = min(lo[1], hi[1])
    return (lo[0] * (1 << (lo[1] - me)) + hi[0] * (1 << (hi[1] - me)), me - 1)


def box_frac(b):
    """JSON box interval [{num,den},{num,den}] -> normalised dyadic pair
    ((lm, le), (hm, he))."""
    return (frac_dyadic(Fraction(b[0]["num"], b[0]["den"])),
            frac_dyadic(Fraction(b[1]["num"], b[1]["den"])))


def box_lit(box):
    """Dyadic-pair box tuple -> Lean `(Fin n -> DInterval)` literal."""
    ivs = []
    for lo, hi in box:
        ivs.append(f"⟨⟨{lo[0]}, {lo[1]}⟩, ⟨{hi[0]}, {hi[1]}⟩⟩")
    return "![" + ", ".join(ivs) + "]"


def emit_tree(t, goal_k=None, depth=0):
    """Nested `BBTree`/`BBTreeD` constructor text with inline per-leaf
    `by decide` certs.  In disj mode `goal_k` maps hit strings to goal
    indices and leaves carry the `Fin goals.length` selector."""
    if isinstance(t, Leaf):
        if goal_k is None:
            return f"(.leaf {box_lit(t.box)} (by decide))"
        k = goal_k[t.hit]
        return f"(.leaf {box_lit(t.box)} ⟨{k}, by decide⟩ (by decide))"
    pad = "  " * min(depth + 1, 20)
    return (f"(.node {box_lit(t.box)} {t.d}\n{pad}{emit_tree(t.l, goal_k, depth + 1)}\n"
            f"{pad}{emit_tree(t.r, goal_k, depth + 1)})")


def build_goals(case, rpn):
    """Disj mode: the goal list [pos main] + disj entries, as
    (Lean text of the list, hit -> goal index) pair.  Validates var_lt
    hit indices against the case disj array."""
    goals = [f"(.pos {rpn.emit(case['prog'])})"]
    kinds = ["main"]
    for dj in case["disj"]:
        if "prog" in dj:
            goals.append(f"(.pos {rpn.emit(dj['prog'])})")
            kinds.append("prog")
        elif "var_lt" in dj:
            i, j = dj["var_lt"]
            goals.append(f"(.varLt {i} {j})")
            kinds.append(f"var_lt:{i},{j}")
        else:
            die(f"disj entry without prog/var_lt: {list(dj)}")
    goal_k = {"main": 0}
    for idx, dj in enumerate(case["disj"]):
        if "prog" in dj:
            goal_k[f"disj:{idx}"] = idx + 1
        else:
            i, j = dj["var_lt"]
            goal_k[f"var_lt:{i},{j}"] = idx + 1
    return "[" + ", ".join(goals) + "]", goal_k


TRANS_KIND = {"atan": "arctanK", "sin": "sinK", "cos": "cosK", "ln": "lnK"}


class RPN:
    """RPN prog -> IExpr text. Stack machine; each entry is a Lean term str.

    `sqrt_slot`: None rejects sqrt (v1 behavior); otherwise a callable
    i -> (s1_text, s2_text) fed with the sqrt node's index in RPN/post
    order (the same order FillParams.evalFill collects mantissas).
    `trans`: None rejects trans ops; otherwise a callable
    (op, closed) -> (N_text, out_text) supplying the certificate parameters.
    `closed` marks var-free arguments (constant across leaves): callers
    typically give them a fixed high N — the alternating arctan series
    converges only like `1/(2N+1)` at boundary points such as `arctan 1`,
    so a constant `atan(1)` node wants `N` in the hundreds while
    var-containing nodes stay on the rung ladder."""

    def __init__(self, div_out=-64, sqrt_slot=None, trans=None):
        self.div_out = div_out
        self.sqrt_slot = sqrt_slot
        self.trans = trans
        self.sqrt_count = 0

    def const(self, c):
        num, den = c["num"], c["den"]
        d = dyadic(num, den)
        if d is not None:
            return f"(.const ⟨{d[0]}, {d[1]}⟩)"
        # non-dyadic rational: exact interval division of int consts
        return (f"(.div (.const ⟨{num}, 0⟩) (.const ⟨{den}, 0⟩) "
                f"({self.div_out}))")

    def emit(self, prog):
        """RPN prog -> IExpr term text."""
        return self.emit_pair(prog)[0]

    def emit_pair(self, prog):
        """RPN prog -> (IExpr term text, closed): `closed` marks var-free
        subterms (leaf-constant), used by the `trans` callback."""
        # stack entries: (Lean term text, closed=var-free)
        st = []
        for ins in prog:
            if isinstance(ins, dict):
                if "ite" not in ins:
                    die(f"unknown dict instr {list(ins)}")
                c = self.emit_pair(ins["ite"]["cond"])
                t = self.emit_pair(ins["ite"]["then"])
                e = self.emit_pair(ins["ite"]["else"])
                st.append((f"(.ite {c[0]} {t[0]} {e[0]})",
                           c[1] and t[1] and e[1]))
                continue
            op = ins[0]
            if op == "push_var":
                st.append((f"(.var {ins[1]})", False))
            elif op == "push_const":
                st.append((self.const(ins[1]), True))
            elif op in ("add", "sub", "mul"):
                b, a = st.pop(), st.pop()
                st.append((f"(.{op} {a[0]} {b[0]})", a[1] and b[1]))
            elif op == "neg":
                a = st.pop()
                st.append((f"(.neg {a[0]})", a[1]))
            elif op == "abs":
                a = st.pop()
                st.append((f"(.abs {a[0]})", a[1]))
            elif op == "div":
                b, a = st.pop(), st.pop()
                st.append((f"(.div {a[0]} {b[0]} ({self.div_out}))", a[1] and b[1]))
            elif op == "sqrt":
                if self.sqrt_slot is None:
                    die("op sqrt: not supported without --fill (see module docstring)")
                a = st.pop()
                s1, s2 = self.sqrt_slot(self.sqrt_count)
                self.sqrt_count += 1
                st.append((f"(.sqrt {a[0]} {s1} {s2})", a[1]))
            elif op in TRANS_KIND:
                if self.trans is None:
                    die(f"op {op}: not supported without --fill (see module docstring)")
                a = st.pop()
                N, out = self.trans(op, a[1])
                st.append((f"(.trans .{TRANS_KIND[op]} {a[0]} {N} {out})", a[1]))
            else:
                die(f"unknown op {op}")
        if len(st) != 1:
            die(f"RPN stack imbalance: {len(st)}")
        return st[0]


def count_op(prog, target):
    """Count occurrences of op `target` in an RPN prog (ite subprogs included)."""
    k = 0
    for ins in prog:
        if isinstance(ins, dict):
            for key in ("cond", "then", "else"):
                k += count_op(ins["ite"][key], target)
        elif ins[0] == target:
            k += 1
    return k


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


class Mode:
    """Emission mode: 'main' (BBTree, single pos goal) or 'disj' (BBTreeD)."""

    def __init__(self, disj, goals_lean=None, goal_k=None):
        self.disj = disj
        self.goals_lean = goals_lean
        self.goal_k = goal_k

    def tree_type(self, mod, n):
        return f"BBTreeD {n} {mod}Goals" if self.disj else f"BBTree {n} {mod}Expr"

    def covers_sound(self):
        return "BBTreeD.coversB_sound" if self.disj else "BBTree.coversB_sound"

    def goals_def(self, mod, n):
        if not self.disj:
            return ""
        return (f"/-- The disjunctive goal list (main prog first). -/\n"
                f"def {mod}Goals : List (DisjGoal {n}) :=\n  {self.goals_lean}\n\n")

    def final_thm(self, mod, n):
        if self.disj:
            return (f"/-- End-to-end: some disjunct holds at every point of the box. -/\n"
                    f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
                    f"    ∃ g ∈ {mod}Goals, g.eval ρ :=\n"
                    f"  bb_sound_disj {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ")
        return (f"/-- End-to-end: the case expression is strictly positive on the whole box. -/\n"
                f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
                f"    0 < ({mod}Expr).evalReal ρ :=\n"
                f"  bb_sound {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ")


def base_file(mod, n, expr, box, mode):
    return (HDR + "import Kepler.Interval.CertBool\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- The case expression (RPN prog mirrored as `IExpr`). -/\n"
            f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
            f"/-- The target box (dyadic q-expansion of the original decimal box). -/\n"
            f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
            + mode.goals_def(mod, n) +
            "end Kepler.Interval.Cases\n")


def shard_file(mod, k, sub, n, mode):
    return (HDR + f"import Kepler.Interval.Cases.{mod}.Base\n\n"
            "set_option maxHeartbeats 0\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- Shard {k} subtree (leaf certs are inline kernel `decide`s). -/\n"
            f"def {mod}Shard{k}Tree : {mode.tree_type(mod, n)} :=\n  {emit_tree(sub, mode.goal_k)}\n\n"
            f"/-- Covering of shard {k}: one kernel `decide` via `CertBool.coversB`. -/\n"
            f"theorem {mod}Shard{k}Covers : {mod}Shard{k}Tree.covers :=\n"
            f"  {mode.covers_sound()} _ (by decide)\n\n"
            "end Kepler.Interval.Cases\n")


# ---------------------------------------------------------------------------
# FillParams pipeline (v2): streaming cert reader, leaf sampling, Stage A
# (per-leaf sqrt parameter computation in Lean) and Stage B (BBTreeG shards).
# ---------------------------------------------------------------------------

import itertools
import os


def stream_cert(path):
    """Stream a bb_arb cert JSON without materializing ~1GB of Python
    objects.  Returns (root_box JSON, prec, leaf generator)."""
    import re
    text = open(path).read()
    dec = json.JSONDecoder()
    i = text.index('"root_box"')
    i = text.index(":", i) + 1
    while text[i] in " \t\r\n":
        i += 1
    root_box, _ = dec.raw_decode(text, i)
    m = re.search(r'"prec"\s*:\s*(\d+)', text[:4096])
    prec = int(m.group(1)) if m else None
    p = text.index("[", text.index('"leaves"')) + 1

    def gen():
        nonlocal p
        while True:
            while text[p] in " \t\r\n,":
                p += 1
            if text[p] == "]":
                return
            leaf, p = dec.raw_decode(text, p)
            yield leaf

    return root_box, gen()


def sample_leaves(leaf_iter, rootfrac, limit):
    """Prefix sample: the first `limit` cert leaves, the root box shrunk to
    the smallest bisection-grid box containing them, then the sample
    extended to ALL cert leaves inside that grid box.  The contained leaves
    of a grid box partition it completely (every actual leaf is a grid box,
    hence either inside or interior-disjoint), so tree reconstruction still
    succeeds.  Returns (grid box, leaves in cert order)."""
    n = len(rootfrac)
    sample = []
    for leaf in leaf_iter:
        sample.append(leaf)
        if len(sample) >= limit:
            break
    if not sample:
        die("sample: empty cert leaf stream")
    boxes = [tuple(box_frac(iv) for iv in l["box"]) for l in sample]
    bbox = tuple((min((b[d][0] for b in boxes), key=lambda x: dval(x)),
                  max((b[d][1] for b in boxes), key=lambda x: dval(x)))
                 for d in range(n))
    cur = rootfrac
    improved = True
    while improved:
        improved = False
        for d in range(n):
            lo, hi = cur[d]
            mid = dmid(lo, hi)
            if dcmp(bbox[d][1], mid) <= 0:
                cur = cur[:d] + ((lo, mid),) + cur[d + 1:]
                improved = True
                break
            if dcmp(bbox[d][0], mid) >= 0:
                cur = cur[:d] + ((mid, hi),) + cur[d + 1:]
                improved = True
                break

    def inside(l):
        b = tuple(box_frac(iv) for iv in l["box"])
        return all(dcmp(b[d][0], cur[d][0]) >= 0 and dcmp(b[d][1], cur[d][1]) <= 0
                   for d in range(n))

    leaves = [l for l in itertools.chain(sample, leaf_iter) if inside(l)]
    return cur, leaves


def stage_a_file(mod, n, expr, boxes_lean, nleaves, leaf0=0):
    """Stage A driver: `fillMkExpr N out` (dummy sqrt slots, rung-parameter
    trans nodes) + the sampled leaf boxes + a `runMain` main (argv dispatch:
    no args = ladder, `N out` = pinned rung).  `leaf0` is the global index
    of the first box (sharded drivers report global leaf indices)."""
    return (HDR + "import Kepler.Interval.Tools.FillParams\n\n"
            "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "open Kepler.Interval Kepler.Interval.Tools\n\n"
            "/-- The case expression with dummy sqrt slots `(0, 0)`; the `trans`\n"
            "certificate parameters are the rung arguments `N out`. -/\n"
            f"def fillMkExpr (N : ℕ) (out : Int) : IExpr {n} :=\n  {expr}\n\n"
            f"/-- The {nleaves} sampled leaf boxes (cert order from {leaf0}). -/\n"
            f"def fillBoxes : Array (Fin {n} → DInterval) :=\n  #["
            + ",\n    ".join(f"({b} : Fin {n} → DInterval)" for b in boxes_lean)
            + "]\n\n"
            f"def main : List String → IO UInt32 := runMain fillMkExpr fillBoxes\n")


def parse_params(path, nleaves, k):
    """Parse FillParams output: `RUNG N out` header + `i PASS s1 t1 ...`
    lines.  Returns ((N, out), {leaf index: [(s1, t1), ...]})."""
    rung = None
    params = {}
    for ln in open(path):
        parts = ln.split()
        if not parts:
            continue
        if parts[0] == "RUNG":
            rung = (int(parts[1]), int(parts[2]))
        elif parts[0] == "BESTFAIL":
            die(f"FillParams reported failures ({ln.strip()}) — refusing stage B")
        elif parts[0].isdigit():
            i = int(parts[0])
            if parts[1] != "PASS":
                die(f"leaf {i} not PASS: {ln.strip()}")
            nums = [int(x) for x in parts[2:]]
            if len(nums) != 2 * k:
                die(f"leaf {i}: expected {2 * k} mantissas, got {len(nums)}")
            params[i] = [(nums[j], nums[j + 1]) for j in range(0, len(nums), 2)]
    if rung is None:
        die("params file has no RUNG line")
    if len(params) != nleaves:
        die(f"params cover {len(params)} leaves, expected {nleaves}")
    return rung, params


def ms_vec(pairs):
    return "#v[" + ", ".join(f"({s}, {t})" for s, t in pairs) + "]"


def emit_tree_bbg(u, mod, params_by_box, depth=0):
    """BBTreeG constructor text; leaves carry the per-leaf filled
    `{mod}MkExpr` instance, the one-shot `{mod}_sem` semantics lemma and an
    inline kernel `decide` cert."""
    if isinstance(u, Leaf):
        return (f"(.leaf {box_lit(u.box)} ({mod}MkExpr {ms_vec(params_by_box[u.cert_box])}) "
                f"({mod}_sem _) (by decide))")
    pad = "  " * min(depth + 1, 20)
    return (f"(.node {box_lit(u.box)} {u.d}\n{pad}{emit_tree_bbg(u.l, mod, params_by_box, depth + 1)}\n"
            f"{pad}{emit_tree_bbg(u.r, mod, params_by_box, depth + 1)})")


def base_file_bbg(mod, n, k, expr, box):
    return (HDR + "import Kepler.Interval.CertG\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            "/-- Expression factory: slot `i` of `ms` carries the per-leaf certificate\n"
            "mantissas `(s₁, s₂)` of the `i`-th `.sqrt` node (RPN/post order — the\n"
            "order `Kepler.Interval.Tools.FillParams.evalFill` collects them). -/\n"
            f"def {mod}MkExpr (ms : Vector (Int × Int) {k}) : IExpr {n} :=\n  {expr}\n\n"
            "/-- The global expression (dummy parameters; `evalReal` ignores them). -/\n"
            f"def {mod}Expr : IExpr {n} := {mod}MkExpr (Vector.replicate {k} (0, 0))\n\n"
            "/-- Every parameter instance coincides with the global expression over ℝ\n"
            "(`IExpr.evalReal` discards the certificate slots definitionally). -/\n"
            f"theorem {mod}_sem (ms : Vector (Int × Int) {k}) :\n"
            f"    ({mod}MkExpr ms).evalReal = ({mod}Expr).evalReal := rfl\n\n"
            "/-- The target box (tree root). -/\n"
            f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
            "end Kepler.Interval.Cases\n")


def shard_file_bbg(mod, i, sub, n, params_by_box):
    return (HDR + f"import Kepler.Interval.Cases.{mod}.Base\n\n"
            "set_option maxHeartbeats 0\n"
            "-- closed-arg atan nodes run N=128 Taylor terms; the elaborator's\n"
            "-- whnf recursion budget must cover the `taylorIter` fuel\n"
            "set_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- Shard {i} subtree (per-leaf filled expressions; certs are inline\n"
            f"kernel `decide`s). -/\n"
            f"def {mod}Shard{i}Tree : BBTreeG {n} {mod}Expr :=\n"
            f"  {emit_tree_bbg(sub, mod, params_by_box)}\n\n"
            f"/-- Covering of shard {i}: one kernel `decide` via `BBTreeG.coversB`. -/\n"
            f"theorem {mod}Shard{i}Covers : {mod}Shard{i}Tree.covers :=\n"
            f"  BBTreeG.coversB_sound _ (by decide)\n\n"
            "end Kepler.Interval.Cases\n")


def emit_sharded_bbg(t, mod, n, k, expr, box, hdr, outpath, shard_leaves, params_by_box):
    """Stage B: Base (MkExpr/Expr/sem/Box) + BBTreeG shards + root, for the
    per-leaf filled expressions."""
    shards = cut_shards(t, shard_leaves)
    shard_idx = {id(u): i + 1 for i, u in enumerate(shards)}
    base = os.path.splitext(outpath)[0]
    os.makedirs(base, exist_ok=True)

    open(os.path.join(base, "Base.lean"), "w").write(
        base_file_bbg(mod, n, k, expr, box).format(**hdr))

    for i, u in enumerate(shards, 1):
        open(os.path.join(base, f"Shard{i}.lean"), "w").write(
            shard_file_bbg(mod, i, u, n, params_by_box).format(**hdr))

    def skel_tree(u):
        if id(u) in shard_idx:
            return f"{mod}Shard{shard_idx[id(u)]}Tree"
        if isinstance(u, Leaf):
            return (f"(.leaf {box_lit(u.box)} ({mod}MkExpr {ms_vec(params_by_box[u.cert_box])}) "
                    f"({mod}_sem _) (by decide))")
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
    root = (HDR + imports + "\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- The certificate tree, assembled from {len(shards)} shard subtrees. -/\n"
            f"def {mod}Tree : BBTreeG {n} {mod}Expr :=\n  {skel_tree(t)}\n\n"
            f"/-- Covering: per-shard `coversB` certificates glued by `splitOKB`\n"
            f"on the {len(shards)}-way skeleton. -/\n"
            f"theorem {mod}_covers : {mod}Tree.covers :=\n  {skel_proof(t)}\n\n"
            f"/-- Box containment is reflexive here (tree root = target box). -/\n"
            f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
            "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
            "/-- End-to-end: the case expression is strictly positive on the whole box. -/\n"
            f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
            f"    0 < ({mod}Expr).evalReal ρ :=\n"
            f"  bb_soundG {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ\n\n"
            f"#print axioms {mod}_pos\n\nend Kepler.Interval.Cases\n")
    open(outpath, "w").write(root.format(**hdr))
    print(f"emit_lean: wrote {outpath} + Base/Shard1..{len(shards)} "
          f"({t.nleaves} leaves, {len(shards)} shards, BBTreeG)")


def main():
    shard_leaves = 128
    sample_n = None
    fill = False
    stage_a = False
    stage_a_shards = 1
    stage_a_data = False
    bbg = False
    params_file = None
    args = []
    for a in sys.argv[1:]:
        if a.startswith("--shard-leaves="):
            shard_leaves = int(a.split("=", 1)[1])
        elif a.startswith("--stage-a-shards="):
            stage_a_shards = int(a.split("=", 1)[1])
        elif a.startswith("--leaves="):
            sample_n = int(a.split("=", 1)[1])
        elif a == "--fill":
            fill = True
        elif a == "--stage-a":
            stage_a = True
        elif a == "--stage-a-data":
            stage_a_data = True
        elif a == "--bbg":
            bbg = True
        elif a.startswith("--params="):
            params_file = a.split("=", 1)[1]
        elif not a.startswith("--"):
            args.append(a)
    if len(args) != 3:
        die("usage: emit_lean.py <case.json> <cert.json> <out.lean> [--shard-leaves=N]\n"
            "                [--leaves=N] [--fill] [--stage-a] [--bbg --params=FILE]")
    fill = fill or stage_a or bbg
    case = json.load(open(args[0]))
    cid = args[0].split("/")[-1].replace(".json", "")
    outbase = os.path.splitext(os.path.basename(args[2]))[0]
    if outbase.startswith("C"):
        mod = outbase
    else:
        mod = "C" + "".join(ch if ch.isalnum() else "x" for ch in cid)
    n = len(case["vars"])
    extra = ""

    if sample_n is None:
        cert = json.load(open(args[1]))
        if cert["root_box"] != case["box"]:
            die("cert root_box != case box")
        leaves = cert["leaves"]
        rootfrac = tuple(box_frac(iv) for iv in cert["root_box"])
        prec = cert.get("prec")
    else:
        root_box_json, leaf_iter = stream_cert(args[1])
        if root_box_json != case["box"]:
            die("cert root_box != case box")
        rootfrac, leaves = sample_leaves(
            leaf_iter, tuple(box_frac(iv) for iv in root_box_json), sample_n)
        prec = None
        extra = (f" — SAMPLE: smallest grid box over first {sample_n} cert leaves"
                 f" ({len(leaves)} leaves inside)")

    hdr = dict(caseid=case["id"], origop=case.get("orig_op"), vars=case["vars"],
               nleaves=len(leaves), prec=prec, extra=extra)

    leafmap = {}
    for l in leaves:
        b = tuple(box_frac(iv) for iv in l["box"])
        if b in leafmap:
            die(f"duplicate leaf box: {b}")
        leafmap[b] = l["hit"]

    if fill:
        # ---- FillParams pipeline (stage A driver / stage B BBTreeG shards) ----
        if case.get("disj"):
            die("fill pipeline: disj cases unsupported (use the v1 path)")
        hits = {l["hit"] for l in leaves}
        if hits != {"main"}:
            die(f"fill pipeline needs main-only hits, got {hits}")
        t = reconstruct(rootfrac, leafmap)
        box = box_lit(rootfrac)
        k = count_op(case["prog"], "sqrt")
        # var-free (leaf-constant) trans arguments get a fixed Taylor order:
        # the alternating arctan series at a boundary point (atan 1)
        # converges only like 1/(2N+1), so the rung ladder's N (tuned for
        # interior args, where big mantissas make high N expensive) can
        # never reach the needed precision.  N=128 verified: all 3762 leaves
        # of 5490182221 chunk00000 PASS at N=64/128/256/1024 with the same
        # rung (12,-64); kernel cost scales ~linearly in N.
        closed_params = ("128", "(-64)")
        if stage_a:
            rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
                      trans=lambda op, closed: closed_params if closed else ("N", "out"))
            expr = rpn.emit(case["prog"])
            if stage_a_data:
                # Data-file mode: one tiny shared driver (compiles in
                # seconds) + plain-text box chunks read at runtime —
                # elaborating box literals is the scaling bottleneck.
                # Chunk layout identical to the .lean shard mode.
                sz = (len(leaves) + stage_a_shards - 1) // stage_a_shards
                d = os.path.splitext(args[2])[0] + ".d"
                os.makedirs(d, exist_ok=True)
                drv = (HDR + "import Kepler.Interval.Tools.FillParams\n\n"
                       "open Kepler.Interval Kepler.Interval.Tools\n\n"
                       f"def fillMkExpr (N : ℕ) (out : Int) : IExpr {n} :=\n"
                       f"  {expr}\n\n"
                       "def main : List String → IO UInt32 :=\n"
                       "  runMainFile fillMkExpr\n")
                open(os.path.join(d, "driver.lean"), "w").write(
                    drv.format(**hdr))
                nw = 0
                for i in range(0, len(leaves), sz):
                    p = os.path.join(d, f"chunk{i // sz:05d}.txt")
                    with open(p, "w") as f:
                        for l in leaves[i:i + sz]:
                            b = tuple(box_frac(iv) for iv in l["box"])
                            f.write(" ".join(
                                f"{lo[0]} {lo[1]} {hi[0]} {hi[1]}"
                                for lo, hi in b) + "\n")
                    nw += 1
                print(f"emit_lean: wrote data-mode stage-A to {d}/ "
                      f"(driver.lean + {nw} chunk txts, {len(leaves)} leaves, "
                      f"chunk size {sz}, {k} sqrt slots)")
                return
            boxes_lean = [box_lit(tuple(box_frac(iv) for iv in l["box"])) for l in leaves]
            if stage_a_shards > 1:
                # Sharded stage A: contiguous chunks, driver i covers global
                # leaf indices [i*sz, (i+1)*sz).  Each driver still reports
                # LOCAL indices; the merge step remaps via this layout.
                sz = (len(leaves) + stage_a_shards - 1) // stage_a_shards
                d = os.path.splitext(args[2])[0] + ".d"
                os.makedirs(d, exist_ok=True)
                nw = 0
                for i in range(0, len(leaves), sz):
                    chunk = boxes_lean[i:i + sz]
                    out = stage_a_file(mod, n, expr, chunk, len(chunk), leaf0=i)
                    p = os.path.join(d, f"chunk{i // sz:05d}.lean")
                    open(p, "w").write(out.format(**hdr))
                    nw += 1
                print(f"emit_lean: wrote {nw} stage-A shards to {d}/ "
                      f"({len(leaves)} leaves, chunk size {sz}, {k} sqrt slots)")
                return
            out = stage_a_file(mod, n, expr, boxes_lean, len(leaves))
            open(args[2], "w").write(out.format(**hdr))
            print(f"emit_lean: wrote {args[2]} (stage A: {len(leaves)} leaves, "
                  f"{k} sqrt slots)")
            return
        if params_file is None:
            die("--bbg needs --params=FILE (FillParams stage-A output)")
        (N, out_g), params = parse_params(params_file, len(leaves), k)
        rpn = RPN(sqrt_slot=lambda i: (f"((ms[{i}]'(by decide)).1)",
                                       f"((ms[{i}]'(by decide)).2)"),
                  trans=lambda op, closed: closed_params if closed else (str(N), f"({out_g})"))
        expr = rpn.emit(case["prog"])
        if rpn.sqrt_count != k:
            die(f"internal: sqrt count {rpn.sqrt_count} != prog count {k}")
        params_by_box = {}
        for i, l in enumerate(leaves):
            params_by_box[tuple(box_frac(iv) for iv in l["box"])] = params[i]
        emit_sharded_bbg(t, mod, n, k, expr, box, hdr, args[2], shard_leaves,
                         params_by_box)
        return

    # ---- original v1 path (BBTree / BBTreeD) ----
    rpn = RPN()
    expr = rpn.emit(case["prog"])
    box = box_lean(case["box"])

    if case.get("disj"):
        goals_lean, goal_k = build_goals(case, rpn)
        mode = Mode(True, goals_lean, goal_k)
    else:
        mode = Mode(False)
    hits = {l["hit"] for l in leaves}
    if mode.disj:
        unknown = hits - set(mode.goal_k)
        if unknown:
            die(f"cert hits not in goal map: {unknown}")
    elif hits != {"main"}:
        die(f"cert hits {hits}: case is not disj but cert uses disjuncts")

    t = reconstruct(rootfrac, leafmap)

    if mode.disj:
        # validate var_lt leaf closures against the Fraction boxes
        # (guards against 0/1-based index confusion upstream)
        def check_varlt(u):
            if isinstance(u, Leaf):
                if u.hit.startswith("var_lt:"):
                    i, j = (int(x) for x in u.hit[7:].split(","))
                    if not (dcmp(u.box[i][1], u.box[j][0]) < 0):
                        die(f"var_lt leaf fails box check: {u.hit} box={u.box}")
            else:
                check_varlt(u.l)
                check_varlt(u.r)
        check_varlt(t)

    outpath = args[2]
    if t.nleaves > shard_leaves:
        emit_sharded(t, mod, n, expr, box, hdr, outpath, shard_leaves, mode)
        return

    if t.nleaves == 1 and not mode.disj:
        tree, cert_thm, covers_thm = pilot_single_leaf(mod, box)
    else:
        tree = emit_tree(t, mode.goal_k)
        cert_thm = ""
        covers_thm = (f"/-- Covering of the whole tree, one kernel `decide`\n"
                      f"through the Bool checker (`CertBool.coversB`). -/\n"
                      f"theorem {mod}_covers : {mod}Tree.covers :=\n"
                      f"  {mode.covers_sound()} _ (by decide)")

    out = (HDR + "import Kepler.Interval.CertBool\n\nset_option maxHeartbeats 0\n\n"
           "namespace Kepler.Interval.Cases\n\n"
           f"/-- The case expression (RPN prog mirrored as `IExpr`). -/\n"
           f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
           f"/-- The target box (dyadic q-expansion of the original decimal box). -/\n"
           f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
           + mode.goals_def(mod, n) +
           f"{cert_thm}\n\n"
           f"/-- The certificate tree (leaf certs are inline kernel `decide`s). -/\n"
           f"def {mod}Tree : {mode.tree_type(mod, n)} :=\n  {tree}\n\n"
           f"{covers_thm}\n\n"
           f"/-- Box containment is reflexive here (tree root = target box). -/\n"
           f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
           "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
           + mode.final_thm(mod, n) + "\n\n"
           f"#print axioms {mod}_pos\n\nend Kepler.Interval.Cases\n")
    open(outpath, "w").write(out.format(**hdr) if "{caseid}" in out else out)
    print(f"emit_lean: wrote {outpath} (module Kepler.Interval.Cases.{mod})")


def emit_sharded(t, mod, n, expr, box, hdr, outpath, shard_leaves, mode):
    import os
    shards = cut_shards(t, shard_leaves)
    shard_idx = {id(u): i + 1 for i, u in enumerate(shards)}
    base = os.path.splitext(outpath)[0]  # .../Cases/<mod>
    os.makedirs(base, exist_ok=True)

    open(os.path.join(base, "Base.lean"), "w").write(
        base_file(mod, n, expr, box, mode).format(**hdr))

    for i, u in enumerate(shards, 1):
        open(os.path.join(base, f"Shard{i}.lean"), "w").write(
            shard_file(mod, i, u, n, mode).format(**hdr))

    def skel_tree(u):
        if id(u) in shard_idx:
            return f"{mod}Shard{shard_idx[id(u)]}Tree"
        if isinstance(u, Leaf):
            if mode.disj:
                k = mode.goal_k[u.hit]
                return f"(.leaf {box_lit(u.box)} ⟨{k}, by decide⟩ (by decide))"
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
    root = (HDR + imports + "\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- The certificate tree, assembled from {len(shards)} shard subtrees. -/\n"
            f"def {mod}Tree : {mode.tree_type(mod, n)} :=\n  {skel_tree(t)}\n\n"
            f"/-- Covering: per-shard `coversB` certificates glued by `splitOKB`\n"
            f"on the {len(shards)}-way skeleton. -/\n"
            f"theorem {mod}_covers : {mod}Tree.covers :=\n  {skel_proof(t)}\n\n"
            f"/-- Box containment is reflexive here (tree root = target box). -/\n"
            f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
            "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
            + mode.final_thm(mod, n) + "\n\n"
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
