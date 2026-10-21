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

v2 disj (wave-2, design D5/D6):
- `--bbg --disj-gd --params=FILE [--manifest=FILE]` reads the schema-v2
  FillParams output (`i PASS k s1 t1 ...` / `i PASSV k`) and the stage-A
  manifest (single source of truth for goals/ladder; auto-detected as
  `manifest.json` next to the params file when `--manifest` is absent),
  and emits `BBTreeGD` shards (CertGD): one `{mod}MkExprK` factory +
  `{mod}ExprK` dummy global + rfl bridge `{mod}SemK` per *pos* goal K,
  the full goals list (un-hit branches carry dummy parameters — only
  expression construction must be legal), leaves `.posLeaf box k e el rfl
  ({mod}SemK _) (by decide)` / `.varLtLeaf box k (by decide)`, root
  theorem `∃ g ∈ goals, g.eval ρ` via `bb_sound_disjG`.
- `--disj-dummy` (v1 repair path, design D6): for disj cases whose *hit*
  branches are all parameter-free, emit plain BBTreeD with dummy `(0, 0)`
  sqrt slots / fixed trans params on the un-hit branches instead of
  dying; a hit branch with sqrt/trans nodes is rejected (route it to
  `--bbg --disj-gd`).

Usage: emit_lean.py <case.json> <cert.json> <out.lean> [--name NAME]
       [--shard-leaves=N] [--leaves=N] [--fill] [--stage-a]
       [--bbg --params=FILE] [--bbg --disj-gd --params=FILE [--manifest=FILE]]
       [--disj-dummy]
"""
import json
import math
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


def tree_box_map(t):
    """cert-form box -> tree (node-form) box over all leaves of a
    reconstructed tree.  Stage-A drivers must evaluate the *node* forms:
    the emitted tree carries them (`splitOKB` compares child boxes
    structurally against `midRadius.c` of the parent), and the `.sqrt`
    mantissa certificate is form-sensitive (`Dyadic.sqrtI` aligns the
    mantissa to `e % 2`), so filling parameters on the normalised cert
    forms can produce mantissas the kernel rejects on the node forms."""
    m = {}

    def walk(u):
        if isinstance(u, Leaf):
            m[u.cert_box] = u.box
        else:
            walk(u.l)
            walk(u.r)

    walk(t)
    return m


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
    var-containing nodes stay on the rung ladder.

    `trans_unclose_sqrt`: W2 fix for the hull/TM route.  A var-free
    `trans` argument takes `evalTMHullFill2`'s closed fast path
    (`(IExpr.trans k e N out).eval box`), which evaluates the argument
    with the PLAIN `IExpr.eval` — and a plain `.sqrt` node reads its
    mantissa certificates from the AST slots.  The hull route emits
    dummy `(0, 0)` slots there, and `Dyadic.sqrtI d 0 = none` for EVERY
    nonzero radicand (the certificate check is `m·2^(e%2) < 1` on the
    mantissa, impossible for `m ≥ 1`), so any closed trans over a
    sqrt-containing constant argument (e.g. `atan(√(2/3)·3/4)` closed
    forms) killed the whole leaf — the BIX stage-A replay 0/20 root
    cause (all 66 such nodes in `prep-BIXPCGW 7274157868 a split(0/2)`).
    Fix: wrap exactly those arguments as
    `(.add arg (.mul (.var 0) (.const ⟨0, 0⟩)))` — extensionally equal
    (`e + x₀·0 = e`, exact dyadic arithmetic), but no longer `closed`,
    so the sound atan TM rule runs instead (its model over the constant
    submodel has `W = 0`, i.e. the same exact quality; the rule cannot
    fail — `1/(1+f²)` reciprocals are always away from 0).  Plain-atan
    closed args keep the fast path.

    `sqrt_const_pad_bits`: W6b plan A (W8 phase 0).  When set, every
    `push_const` whose (num, den) value directly feeds a `sqrt` node
    somewhere in the program (RPN order, per program list; `ite`
    subprograms are their own lists) is emitted with its mantissa scaled UP
    by factors of 4 (exponent down by 2 — value unchanged, parity of `e`
    preserved) until it reaches `2^sqrt_const_pad_bits`.  Padding is by
    VALUE, not by occurrence position (simpler; other occurrences of the
    same rational are inert — the value is identical, only the mantissa
    scale grows, which costs nothing but slightly larger `Int`s).  `Dyadic.sqrtI` certifies `√d` as
    `[s, s+1] · 2^(e/2)` with `s = ⌊√(m·2^(e%2))⌋`, so a small-mantissa
    radicand (`√8 = ⟨8,0⟩ → [2,3]`) certifies at whole-number granularity;
    a ≥2^120 mantissa (`8 = ⟨2^123, -120⟩`) certifies at 2^-60 — a ~10^9x
    tighter plain-eval enclosure for sqrt-of-const subtrees.  The injection
    happens AFTER `dyadic()` normalization, in the text layer (scaling the
    num/den fraction before `dyadic()` would be normalized away — W6b
    minefield).  Default None = v1/v2 byte-identical behavior."""

    def __init__(self, div_out=-64, sqrt_slot=None, trans=None,
                 trans_unclose_sqrt=False, sqrt_const_pad_bits=None):
        self.div_out = div_out
        self.sqrt_slot = sqrt_slot
        self.trans = trans
        self.trans_unclose_sqrt = trans_unclose_sqrt
        self.sqrt_const_pad_bits = sqrt_const_pad_bits
        self._pad_vals = None
        self.sqrt_count = 0

    @staticmethod
    def _sqrt_fed_consts(prog, acc):
        """collect the (num, den) of push_consts immediately followed by a
        `sqrt` in RPN order (ite subprograms scanned recursively)."""
        prev = None
        for ins in prog:
            if isinstance(ins, dict):
                it = ins["ite"]
                for sub in (it["cond"], it["then"], it["else"]):
                    RPN._sqrt_fed_consts(sub, acc)
                prev = None
                continue
            if (prev is not None and ins[0] == "sqrt"
                    and prev[0] == "push_const"):
                acc.add((prev[1]["num"], prev[1]["den"]))
            prev = ins

    def const(self, c):
        num, den = c["num"], c["den"]
        d = dyadic(num, den)
        if d is not None:
            m, e = d
            if (self.sqrt_const_pad_bits is not None
                    and self._pad_vals is not None
                    and (num, den) in self._pad_vals):
                # W6b plan A: scale mantissa to >= 2^bits, value-preserving,
                # e-parity preserved (factors of 4).  Post-normalization text
                # layer only (see class docstring).
                while abs(m) < (1 << self.sqrt_const_pad_bits):
                    m *= 4
                    e -= 2
                return f"(.const ⟨{m}, {e}⟩)"
            return f"(.const ⟨{m}, {e}⟩)"
        # non-dyadic rational: exact interval division of int consts
        return (f"(.div (.const ⟨{num}, 0⟩) (.const ⟨{den}, 0⟩) "
                f"({self.div_out}))")

    @staticmethod
    def _pad_closed_text(text, bits):
        """W8.1: rescale EVERY dyadic literal ⟨m, e⟩ in a closed (var-free)
        sqrt radicand to |m| >= 2^bits (value and e-parity preserved).
        Rationale: `Dyadic.sqrtI` certifies at granularity `2^(e/2)` of the
        radicand representation, so small-mantissa const composites
        (e.g. sqrt(1024*2) = sqrt 2048 -> [45,46]) inject huge sqrt junk
        that survives the whole TM chain (the W8.1 root cause: the W6a
        mirror's 2^-80 isqrt is tight while the kernel's is coarse).
        Literals inside `.trans ...` subterms are NOT scaled: their value
        already sits at the rung's output granularity (~2^-64), and padded
        atan args would inflate the closed Taylor BigInt cost.  Value- and
        parity-preserving (factors of 4), so certificates baked elsewhere
        stay sound; only mantissa representations grow."""
        out = []
        i = 0
        n = len(text)
        while i < n:
            j = text.find("⟨", i)
            if j < 0:
                out.append(text[i:])
                break
            k = text.find("⟩", j)
            if k < 0:
                out.append(text[i:])
                break
            body = text[j + 1:k]
            parts = body.split(",")
            if len(parts) == 2:
                try:
                    m = int(parts[0].strip())
                    e = int(parts[1].strip())
                    while m != 0 and abs(m) < (1 << bits):
                        m *= 4
                        e -= 2
                    out.append(text[i:j])
                    out.append(f"⟨{m}, {e}⟩")
                    i = k + 1
                    continue
                except ValueError:
                    pass
            out.append(text[i:k + 1])
            i = k + 1
        return "".join(out)

    def emit(self, prog):
        """RPN prog -> IExpr term text."""
        return self.emit_pair(prog)[0]

    @staticmethod
    def _pad_const_text(num, den, bits):
        """(num, den) dyadic -> padded literal text: mantissa scaled by
        factors of 4 to >= 2^bits (value and e-parity preserved)."""
        m, e = dyadic(num, den)
        while abs(m) < (1 << bits):
            m *= 4
            e -= 2
        return f"(.const \u27e8{m}, {e}\u27e9)"

    def emit_pair(self, prog):
        """RPN prog -> (IExpr term text, closed): `closed` marks var-free
        subterms (leaf-constant), used by the `trans` callback."""
        # stack entries: (Lean term text, closed=var-free, const tag or None)
        st = []
        for ins in prog:
            if isinstance(ins, dict):
                if "ite" not in ins:
                    die(f"unknown dict instr {list(ins)}")
                c = self.emit_pair(ins["ite"]["cond"])
                t = self.emit_pair(ins["ite"]["then"])
                e = self.emit_pair(ins["ite"]["else"])
                st.append((f"(.ite {c[0]} {t[0]} {e[0]})",
                           c[1] and t[1] and e[1], None))
                continue
            op = ins[0]
            if op == "push_var":
                st.append((f"(.var {ins[1]})", False, None))
            elif op == "push_const":
                c = ins[1]
                st.append((self.const(c), True,
                           (c["num"], c["den"])
                           if self.sqrt_const_pad_bits is not None else None))
            elif op in ("add", "sub", "mul"):
                b, a = st.pop(), st.pop()
                st.append((f"(.{op} {a[0]} {b[0]})", a[1] and b[1], None))
            elif op == "neg":
                a = st.pop()
                st.append((f"(.neg {a[0]})", a[1], None))
            elif op == "abs":
                a = st.pop()
                st.append((f"(.abs {a[0]})", a[1], None))
            elif op == "div":
                b, a = st.pop(), st.pop()
                st.append((f"(.div {a[0]} {b[0]} ({self.div_out}))",
                           a[1] and b[1], None))
            elif op == "sqrt":
                if self.sqrt_slot is None:
                    die("op sqrt: not supported without --fill (see module docstring)")
                a = st.pop()
                if (self.sqrt_const_pad_bits is not None
                        and a[2] is not None):
                    # W6b plan A, surgical: only the DIRECT const radicand is
                    # scaled (atan-arg consts keep small mantissas, so the
                    # N=2048 closed Taylor terms stay cheap).
                    num, den = a[2]
                    a = (self._pad_const_text(num, den,
                                              self.sqrt_const_pad_bits),
                         a[1], None)
                elif (self.sqrt_const_pad_bits is not None and a[1]
                      and ".trans" not in a[0]):
                    # W8.1: closed COMPOSITE radicands without trans (pure
                    # const +,-,*,/ trees) certify sqrtI at the smallest
                    # literal's granularity -- pad every literal in the
                    # radicand (value-preserving; trans-free so no Taylor
                    # BigInt blowup).  Closes the W8.1 kernel-vs-mirror df
                    # divergence root cause (sqrt(2048) = [45,46] junk).
                    a = (self._pad_closed_text(a[0],
                                               self.sqrt_const_pad_bits),
                         a[1], None)
                s1, s2 = self.sqrt_slot(self.sqrt_count)
                self.sqrt_count += 1
                # W8.1 NEGATIVE RESULT (recorded): a value-exact scale-up/
                # scale-down rewrite sqrt(x) -> sqrt(x*2^120)*2^-60 was tried
                # here and REVERTED: it fixes sqrtI granularity but the
                # resulting TM model carries a 2^60 ABSOLUTE width factor
                # (sqrt of the scaled radicand: W ~ 2^60 * w^2/(8v^1.5)),
                # which destroys every additive context downstream (observed
                # sqrt-gate junk c = -1.2e222 on R1).  The var-at-point sqrt
                # granularity blocker (sqrt(var @ [4,4]) = [2,3]) needs a
                # CertTM sqrt-rule granularity fix (orchestrator gate) or a
                # tree-aware emitter substitution -- NOT a value rewrite.
                st.append((f"(.sqrt {a[0]} {s1} {s2})", a[1], None))
            elif op in TRANS_KIND:
                if self.trans is None:
                    die(f"op {op}: not supported without --fill (see module docstring)")
                a = st.pop()
                N, out = self.trans(op, a[1])
                text, closed = a[0], a[1]
                if (self.trans_unclose_sqrt and closed
                        and "(.sqrt " in text):
                    # See `trans_unclose_sqrt` in the class docstring: keep
                    # sqrt-carrying constant args off the plain-eval closed
                    # fast path (dead dummy sqrt certificates there).
                    text = (f"(.add {text} (.mul (.var 0) (.const ⟨0, 0⟩)))")
                    closed = False
                st.append((f"(.trans .{TRANS_KIND[op]} {text} {N} {out})",
                           closed, None))
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


LADDER = [(12, -64), (16, -64), (20, -64), (24, -64), (32, -64), (48, -64),
          (64, -64), (96, -64), (128, -64), (128, -80), (128, -100)]


def fill_goals(case):
    """Disjunctive stage-A goals (schema v2, wave-2 design D2/D3): the main
    prog plus each `disj` entry, in goal order (goal 0 = main, disj entry j =
    goal j+1).  Returns (mkexprs, terms, manifest):
      mkexprs  — one `fillMkExpr<slot>` body per pos goal (dummy sqrt slots
                 `(0, 0)`, closed trans fixed (2048,-64), open trans on the
                 rung arguments `N out`);
      terms    — per-goal `FillGoal` term text, in goal order;
      manifest — per-goal JSON descriptors (kind/label/sqrt count or i,j).
    """
    rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
              trans=lambda op, closed: ("2048", "(-64)") if closed else ("N", "out"))
    mkexprs, terms, manifest = [], [], []

    def add_pos(prog, label):
        terms.append(f".pos fillMkExpr{len(mkexprs)}")
        mkexprs.append(rpn.emit(prog))
        manifest.append({"index": len(manifest), "label": label, "kind": "pos",
                         "sqrt": count_op(prog, "sqrt")})

    add_pos(case["prog"], "main")
    for idx, dj in enumerate(case["disj"]):
        if "prog" in dj:
            add_pos(dj["prog"], f"disj:{idx}")
        elif "var_lt" in dj:
            i, j = dj["var_lt"]
            terms.append(f".varLt {i} {j}")
            manifest.append({"index": len(manifest), "label": f"var_lt:{i},{j}",
                             "kind": "varLt", "i": i, "j": j})
        else:
            die(f"disj entry without prog/var_lt: {list(dj)}")
    return mkexprs, terms, manifest


def stage_a_disj_prelude(n, mkexprs, terms):
    """Shared disj driver prelude: fillMkExprK factories + fillGoals list."""
    out = []
    for i, e in enumerate(mkexprs):
        out.append(f"/-- Pos-goal factory {i} (dummy sqrt slots `(0, 0)`; the\n"
                   "`trans` certificate parameters are the rung arguments\n"
                   "`N out`, closed trans nodes fixed at (2048, -64)). -/\n"
                   f"def fillMkExpr{i} (N : ℕ) (out : Int) : IExpr {n} :=\n  {e}\n")
    out.append("/-- The full goal list (main prog first, disj entries in case\n"
               "order): pos factories plus exact-box varLt checks. -/\n"
               f"def fillGoals : List (FillGoal {n}) :=\n  ["
               + ", ".join(terms) + "]\n")
    return "\n".join(out)


def stage_a_file_disj(mod, n, mkexprs, terms, boxes_lean, nleaves, leaf0=0):
    """Disjunctive stage-A driver with inline box literals: `runMainDisj`
    walks the ladder and prints schema-v2 per-leaf lines (`i PASS k ...` /
    `i PASSV k` / `i FAIL`).  `leaf0` is the global index of the first box
    (sharded drivers report global leaf indices)."""
    return (HDR + "import Kepler.Interval.Tools.FillParams\n\n"
            "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "open Kepler.Interval Kepler.Interval.Tools\n\n"
            + stage_a_disj_prelude(n, mkexprs, terms) + "\n"
            f"/-- The {nleaves} sampled leaf boxes (cert order from {leaf0}). -/\n"
            f"def fillBoxes : Array (Fin {n} → DInterval) :=\n  #["
            + ",\n    ".join(f"({b} : Fin {n} → DInterval)" for b in boxes_lean)
            + "]\n\n"
            "def main : List String → IO UInt32 := runMainDisj fillGoals fillBoxes\n")


def stage_a_driver_disj(n, mkexprs, terms):
    """Data-file mode disj driver: one tiny source (compiles in seconds),
    box chunks read at runtime by `runMainFileDisj`."""
    return (HDR + "import Kepler.Interval.Tools.FillParams\n\n"
            "open Kepler.Interval Kepler.Interval.Tools\n\n"
            + stage_a_disj_prelude(n, mkexprs, terms) + "\n"
            "def main : List String → IO UInt32 :=\n  runMainFileDisj fillGoals\n")


def write_manifest(path, cid, n, goals, nleaves, mode, chunk_size=None):
    """Stage-A manifest (schema v2, design D3): single source of truth for
    the ladder and the per-goal sqrt slot counts; stagea_merge/params_merge
    read it (W3) instead of replicating the ladder."""
    m = {"schema": 2, "case": cid, "n": n,
         "ladder": [list(r) for r in LADDER],
         "goals": goals, "nleaves": nleaves, "mode": mode,
         "chunk_size": chunk_size}
    with open(path, "w") as f:
        json.dump(m, f, indent=1)
        f.write("\n")
    print(f"emit_lean: wrote {path} (schema v2 manifest, {len(goals)} goals)")


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


# ---------------------------------------------------------------------------
# Wave-2 stage B (design D5): BBTreeGD shards for disj cases with
# parameterised hit branches, driven by the schema-v2 manifest + params.
# ---------------------------------------------------------------------------

def case_goals(case):
    """Schema-v2 goal descriptors derived from the case JSON (the emitted
    goal list's source of truth; cross-checked against the manifest).
    `prog` is kept on pos goals for factory emission."""
    goals = [{"index": 0, "label": "main", "kind": "pos",
              "sqrt": count_op(case["prog"], "sqrt"), "prog": case["prog"]}]
    for idx, dj in enumerate(case.get("disj", [])):
        if "prog" in dj:
            goals.append({"index": idx + 1, "label": f"disj:{idx}", "kind": "pos",
                          "sqrt": count_op(dj["prog"], "sqrt"), "prog": dj["prog"]})
        elif "var_lt" in dj:
            i, j = dj["var_lt"]
            goals.append({"index": idx + 1, "label": f"var_lt:{i},{j}",
                          "kind": "varLt", "i": i, "j": j})
        else:
            die(f"disj entry without prog/var_lt: {list(dj)}")
    return goals


def find_manifest(manifest_file, params_file):
    """Locate the schema-v2 stage-A manifest: explicit --manifest, else
    `manifest.json` next to the params file."""
    if manifest_file:
        return manifest_file
    cand = os.path.join(os.path.dirname(os.path.abspath(params_file)),
                        "manifest.json")
    if os.path.exists(cand):
        return cand
    die("--disj-gd needs the stage-A manifest (design D3): pass "
        "--manifest=FILE or place manifest.json next to the params file")


def check_manifest(mf, goals, n, nleaves):
    """Cross-check the schema-v2 manifest against the case-derived goals
    (both describe the same goal list; disagreement = wrong input pair)."""
    if mf.get("schema") != 2:
        die(f"manifest schema {mf.get('schema')} != 2")
    if mf.get("n") != n:
        die(f"manifest n={mf.get('n')} != case vars {n}")
    if mf.get("nleaves") != nleaves:
        die(f"manifest nleaves={mf.get('nleaves')} != cert leaves {nleaves}")
    mg = mf.get("goals") or []
    if len(mg) != len(goals):
        die(f"manifest has {len(mg)} goals, case has {len(goals)}")
    for g, m in zip(goals, mg):
        for key in ("index", "label", "kind"):
            if m.get(key) != g[key]:
                die(f"goal {g['index']} {key}: manifest {m.get(key)} != case {g[key]}")
        if g["kind"] == "pos":
            if m.get("sqrt") != g["sqrt"]:
                die(f"goal {g['index']} sqrt: manifest {m.get('sqrt')} != "
                    f"case {g['sqrt']}")
        elif m.get("i") != g["i"] or m.get("j") != g["j"]:
            die(f"goal {g['index']} var_lt: manifest {m.get('i')},{m.get('j')} "
                f"!= case {g['i']},{g['j']}")
    return mf


def parse_params_disj(path, nleaves, goals):
    """Parse schema-v2 FillParams output: `RUNG N out` header plus per-leaf
    `i PASS k s1 t1 ...` (pos hit, 2*sqrt(goals[k]) ints) / `i PASSV k`
    (varLt hit, no params) lines.  BESTFAIL/FAIL lines are fatal.  Returns
    ((N, out), {leaf index: ("pos", k, [(s1, t1), ...]) | ("varLt", k, None)})."""
    rung = None
    hits = {}
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
            if i in hits:
                die(f"duplicate params line for leaf {i}")
            if parts[1] == "FAIL":
                die(f"leaf {i} FAIL ({ln.strip()}) — refusing stage B")
            elif parts[1] == "PASSV":
                if len(parts) != 3:
                    die(f"leaf {i}: PASSV takes exactly the goal index: {ln.strip()}")
                k = int(parts[2])
                if not (0 <= k < len(goals)) or goals[k]["kind"] != "varLt":
                    die(f"leaf {i}: PASSV {k} but goal {k} is not a varLt goal")
                hits[i] = ("varLt", k, None)
            elif parts[1] == "PASS":
                k = int(parts[2])
                if not (0 <= k < len(goals)) or goals[k]["kind"] != "pos":
                    die(f"leaf {i}: PASS {k} but goal {k} is not a pos goal")
                nums = [int(x) for x in parts[3:]]
                if len(nums) != 2 * goals[k]["sqrt"]:
                    die(f"leaf {i}: goal {k} expects {2 * goals[k]['sqrt']} "
                        f"mantissas, got {len(nums)}")
                hits[i] = ("pos", k,
                           [(nums[j], nums[j + 1]) for j in range(0, len(nums), 2)])
            else:
                die(f"leaf {i}: unknown status {parts[1]}: {ln.strip()}")
    if rung is None:
        die("params file has no RUNG line")
    if len(hits) != nleaves or (hits and (min(hits) < 0 or max(hits) >= nleaves)):
        die(f"params cover {len(hits)} leaves, expected indices 0..{nleaves - 1}")
    return rung, hits


def mkexpr_bbgd(prog, sj, rung):
    """BBTreeGD pos-goal factory body: sqrt slots read from `ms` (RPN/post
    order), open trans nodes on the global rung, closed trans fixed at
    (2048, -64) — the same policy as the BBTreeG factory."""
    N, out = rung
    rpn = RPN(sqrt_slot=lambda i: (f"((ms[{i}]'(by decide)).1)",
                                   f"((ms[{i}]'(by decide)).2)"),
              trans=lambda op, closed: ("2048", "(-64)") if closed
              else (str(N), f"({out})"))
    expr = rpn.emit(prog)
    if rpn.sqrt_count != sj:
        die(f"internal: sqrt count {rpn.sqrt_count} != manifest count {sj}")
    return expr


def base_file_bbgd(mod, n, goals, exprs, box):
    out = [HDR + "import Kepler.Interval.CertGD\n\n"
           # the dummy ExprK globals elaborate the full goal ASTs (the main
           # prog alone is 1.5k ops) — the default 200k-heartbeat budget
           # times out inside `synthesize pending MVars` (7-leaf BIXPCGW
           # pilot, W3); shards/top already carry the same options
           "set_option maxHeartbeats 0\n"
           "set_option maxRecDepth 1000000\n\n"
           "namespace Kepler.Interval.Cases\n\n"]
    for g in goals:
        if g["kind"] != "pos":
            continue
        j, sj = g["index"], g["sqrt"]
        out.append(
            f"/-- Pos-goal {j} (`{g['label']}`) expression factory: slot `i` of\n"
            "`ms` carries the per-leaf certificate mantissas `(s₁, s₂)` of the\n"
            "`i`-th `.sqrt` node (RPN/post order — the order\n"
            "`Kepler.Interval.Tools.FillParams.evalFill` collects them). -/\n"
            f"def {mod}MkExpr{j} (ms : Vector (Int × Int) {sj}) : IExpr {n} :=\n"
            f"  {exprs[j]}\n\n"
            f"/-- The global goal-{j} expression (dummy parameters; `evalReal`\n"
            "ignores them).  Un-hit branches appear in the goals list only via\n"
            "this dummy instance — soundness never checks them. -/\n"
            f"def {mod}Expr{j} : IExpr {n} := {mod}MkExpr{j} (Vector.replicate {sj} (0, 0))\n\n"
            "/-- Every parameter instance coincides with the global expression over ℝ\n"
            "(`IExpr.evalReal` discards the certificate slots definitionally). -/\n"
            f"theorem {mod}Sem{j} (ms : Vector (Int × Int) {sj}) :\n"
            f"    ({mod}MkExpr{j} ms).evalReal = ({mod}Expr{j}).evalReal := rfl\n\n")
    gl = ", ".join(f".pos {mod}Expr{g['index']}" if g["kind"] == "pos"
                   else f".varLt {g['i']} {g['j']}" for g in goals)
    out.append("/-- The disjunctive goal list (main prog first, disj entries in\n"
               "case order). -/\n"
               f"def {mod}Goals : List (DisjGoal {n}) :=\n  [{gl}]\n\n"
               "/-- The target box (tree root). -/\n"
               f"def {mod}Box : Fin {n} → DInterval :=\n  {box}\n\n"
               "end Kepler.Interval.Cases\n")
    return "".join(out)


def emit_leaf_bbgd(mod, box, hit):
    """One BBTreeGD leaf: pos hits carry the per-leaf filled factory
    instance + `rfl` (`goals.get k` reduces on the literal list) + the
    one-shot semantics bridge; varLt hits are plain box checks."""
    kl = f"⟨{hit[1]}, by decide⟩"
    if hit[0] == "varLt":
        return f"(.varLtLeaf {box_lit(box)} {kl} (by decide))"
    k, pairs = hit[1], hit[2]
    return (f"(.posLeaf {box_lit(box)} {kl} {mod}Expr{k} "
            f"({mod}MkExpr{k} {ms_vec(pairs)}) rfl ({mod}Sem{k} _) (by decide))")


def emit_tree_bbgd(u, mod, hits_by_box, depth=0):
    """BBTreeGD constructor text with inline per-leaf `by decide` certs."""
    if isinstance(u, Leaf):
        return emit_leaf_bbgd(mod, u.box, hits_by_box[u.cert_box])
    pad = "  " * min(depth + 1, 20)
    return (f"(.node {box_lit(u.box)} {u.d}\n{pad}{emit_tree_bbgd(u.l, mod, hits_by_box, depth + 1)}\n"
            f"{pad}{emit_tree_bbgd(u.r, mod, hits_by_box, depth + 1)})")


def shard_file_bbgd(mod, i, sub, n, hits_by_box):
    return (HDR + f"import Kepler.Interval.Cases.{mod}.Base\n\n"
            "set_option maxHeartbeats 0\n"
            "-- closed-arg atan nodes run N=2048 Taylor terms; the elaborator's\n"
            "-- whnf recursion budget must cover the `taylorIter` fuel\n"
            "set_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            f"/-- Shard {i} subtree (per-leaf filled expressions; certs are inline\n"
            f"kernel `decide`s). -/\n"
            f"def {mod}Shard{i}Tree : BBTreeGD {n} {mod}Goals :=\n"
            f"  {emit_tree_bbgd(sub, mod, hits_by_box)}\n\n"
            f"/-- Covering of shard {i}: one kernel `decide` via `BBTreeGD.coversB`. -/\n"
            f"theorem {mod}Shard{i}Covers : {mod}Shard{i}Tree.covers :=\n"
            f"  BBTreeGD.coversB_sound _ (by decide)\n\n"
            "end Kepler.Interval.Cases\n")


def emit_sharded_bbgd(t, mod, n, goals, exprs, box, hdr, outpath, shard_leaves,
                      hits_by_box):
    """Stage B (disj, schema v2): Base (per-goal MkExprK/ExprK/SemK + Goals +
    Box) + BBTreeGD shards + root, closing via `bb_sound_disjG`."""
    shards = cut_shards(t, shard_leaves)
    shard_idx = {id(u): i + 1 for i, u in enumerate(shards)}
    base = os.path.splitext(outpath)[0]
    os.makedirs(base, exist_ok=True)

    open(os.path.join(base, "Base.lean"), "w").write(
        base_file_bbgd(mod, n, goals, exprs, box).format(**hdr))

    for i, u in enumerate(shards, 1):
        open(os.path.join(base, f"Shard{i}.lean"), "w").write(
            shard_file_bbgd(mod, i, u, n, hits_by_box).format(**hdr))

    def skel_tree(u):
        if id(u) in shard_idx:
            return f"{mod}Shard{shard_idx[id(u)]}Tree"
        if isinstance(u, Leaf):
            return emit_leaf_bbgd(mod, u.box, hits_by_box[u.cert_box])
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
            f"def {mod}Tree : BBTreeGD {n} {mod}Goals :=\n  {skel_tree(t)}\n\n"
            f"/-- Covering: per-shard `coversB` certificates glued by `splitOKB`\n"
            f"on the {len(shards)}-way skeleton. -/\n"
            f"theorem {mod}_covers : {mod}Tree.covers :=\n  {skel_proof(t)}\n\n"
            f"/-- Box containment is reflexive here (tree root = target box). -/\n"
            f"theorem {mod}_sub : boxSub {mod}Box {mod}Tree.box := by\n"
            "  intro i\n  fin_cases i <;> exact ⟨by decide, by decide⟩\n\n"
            "/-- End-to-end: some disjunct holds at every point of the box. -/\n"
            f"theorem {mod}_pos (ρ : Fin {n} → ℝ) (hρ : boxMem {mod}Box ρ) :\n"
            f"    ∃ g ∈ {mod}Goals, g.eval ρ :=\n"
            f"  bb_sound_disjG {mod}Tree {mod}Box {mod}_covers {mod}_sub ρ hρ\n\n"
            f"#print axioms {mod}_pos\n\nend Kepler.Interval.Cases\n")
    open(outpath, "w").write(root.format(**hdr))
    print(f"emit_lean: wrote {outpath} + Base/Shard1..{len(shards)} "
          f"({t.nleaves} leaves, {len(shards)} shards, BBTreeGD)")


# ---------------------------------------------------------------------------
# M2b/schema-v3 hull pilot (`--hull`): TM-closed leaf certificates through the
# Lean kernel hull checker `checkPosTMHull` (CertTM.lean M2b/schema-v3
# section; since schema v3 the checker runs `evalTMHullD` — guard-decided
# single-branch, straddle → double-branch hull — and the stage-A probe runs
# the node-for-node mirror `evalTMHullFill`, guard sqrt mantissas included in
# the reported triples, guard-first in the queue).
#
#   stage A:  emit_lean.py <case.json> <cert.json> <outA.lean> --hull \
#                     [--leaves=20 --gran=-80 --rung=128 --rung-out=-80]
#     emits a compiled-run driver (`lake env lean --run outA.lean`) that
#     probes each sampled tm-hit leaf with `tmHullLeafProbe` and prints
#       RUNG <N> <out> <oinv0> <oinv1> <oinv2> <osq1> <osq2> <otr1> <otr2>
#       <k> PASS|NEG <lo_m> <lo_e> <slo shi sc>...   /   <k> FAIL
#   stage B:  emit_lean.py <case.json> <cert.json> <outB.lean> --hull \
#                     --params=<stage-A output>
#     emits the kernel certificate: per-PASS-leaf
#       theorem <mod>LeafK : checkPosTMHull <mod>Expr <mod>BoxK <mod>P<K>
#         = true := by decide
#     glued into a single `<mod>_pilot` conjunction for `#print axioms`.
# ---------------------------------------------------------------------------

def hull_sel_boxes(cert_path, want, stride=None):
    """Stride-select up to `want` tm-hit leaves from a bb_arb cert (two
    streaming passes: count, then pick every stride-th tm leaf).  With an
    explicit `stride` (stage B reproducing stage A's sample), `want` counts
    picks, not tm leaves."""
    _, gen = stream_cert(cert_path)
    ntm = sum(1 for l in gen if l["hit"] == "tm")
    if ntm == 0:
        die("no tm-hit leaves in cert")
    if stride is None:
        stride = max(1, ntm // max(1, want))
    picks, i = [], 0
    _, gen = stream_cert(cert_path)
    for l in gen:
        if l["hit"] == "tm":
            if i % stride == 0:
                picks.append(tuple(box_frac(iv) for iv in l["box"]))
                if len(picks) >= want:
                    break
            i += 1
    return picks, ntm, stride


def hull_expr(case, rung_n, rung_out):
    """The case expression for the hull route: dummy `(0, 0)` sqrt slots
    (mantissas live in `TMParams.sqrtCerts`, not in the AST), closed trans
    args pinned at (2048, -64), open trans args at the pilot rung.
    Identical text in stage A and stage B.  Node counts are taken from the
    EMITTED text, not the RPN op list: non-dyadic `push_const` entries
    expand to an extra `.div` node (const numerator / denominator), and the
    hull route consumes one invCert per emitted div.  Closed trans args
    carrying sqrt nodes are unclosed (`trans_unclose_sqrt`) — the closed
    fast path would evaluate them with the dead dummy certificates."""
    rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
              trans=lambda op, closed: ("2048", "(-64)") if closed
              else (str(rung_n), f"({rung_out})"),
              trans_unclose_sqrt=True)
    expr = rpn.emit(case["prog"])
    return (expr, expr.count("(.sqrt "), expr.count("(.div "),
            expr.count("(.trans "))


def hull_stage_a_file(mod, n, expr, boxes, gran, rung_n, rung_out,
                      nsqrt, ndiv, ntrans, nleaves, meta, extra):
    """Stage-A probe driver: compiled run (`lake env lean --run`) prints the
    RUNG header then one probe line per leaf.  Only HDR is .format-ed (the
    Lean interpolation braces of the probe loop stay literal)."""
    g = f"({gran})"
    boxes_lean = ",\n    ".join(
        f"({box_lit(b)} : Fin {n} → DInterval)" for b in boxes)
    hdr_text = (HDR.format(nleaves=nleaves, extra=extra, **meta) +
                "import Kepler.Interval.CertTM\n\n"
                "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
                "open Kepler.Interval\n\n"
                "/-- Local default (for `Array.get!` in the probe loop only). -/\n"
                "instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩\n\n"
                "/-- The case expression for the hull route: dummy `(0, 0)`\n"
                "sqrt slots (mantissas are carried in `TMParams.sqrtCerts`,\n"
                "not in the AST); closed atan args pinned at (2048, -64),\n"
                f"open atan args at the pilot rung ({rung_n}, {rung_out}). -/\n"
                f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
                "/-- Template TMParams: dummy mantissas, pilot recip\n"
                f"granularity {gran} everywhere. -/\n"
                f"def {mod}Ps : TMParams :=\n"
                f"  ⟨List.replicate {nsqrt} ⟨0, 0, 0, {g}, {g}⟩,\n"
                f"   List.replicate {ndiv} ⟨{g}, {g}, {g}⟩,\n"
                f"   List.replicate {ntrans} ⟨{g}, {g}⟩⟩\n\n"
                f"/-- The {nleaves} stride-sampled tm-hit leaf boxes. -/\n"
                f"def {mod}Boxes : Array (Fin {n} → DInterval) :=\n  #["
                + boxes_lean + "]\n\n"
                f"def main : List String → IO UInt32 := fun _ => do\n"
                f"  IO.println \"RUNG {rung_n} {rung_out} {g} {g} {g} {g} {g} {g} {g}\"\n"
                f"  for i in [0:{mod}Boxes.size] do\n"
                f"    match tmHullLeafProbe {mod}Expr {mod}Boxes[i]! {mod}Ps with\n"
                "    | some (p, m, e, l) =>\n"
                "        let v := if p then \"PASS\" else \"NEG\"\n"
                "        let trip := String.intercalate \" \"\n"
                "          (l.map fun t => s!\"{t.1} {t.2.1} {t.2.2}\")\n"
                "        IO.println s!\"{i} {v} {m} {e} {trip}\"\n"
                "    | none => IO.println s!\"{i} FAIL\"\n"
                "  return 0\n")
    return hdr_text


def parse_hull_params(path, nsqrt):
    """Parse stage-A probe output: the RUNG header + per-leaf lines.
    Returns (rung tuple (N, out, g0..g6), {k: (verdict, lo_m, lo_e,
    triples)} for all evaluated leaves; verdict is 'PASS' or 'NEG')."""
    rung = None
    verdicts = {}
    for ln in open(path):
        ln = ln.strip()
        if not ln:
            continue
        if ln.startswith("RUNG"):
            tk = ln.split()
            if len(tk) != 10:
                die(f"bad RUNG header: {ln}")
            rung = tuple(int(x.strip("()")) for x in tk[1:])
            continue
        tk = ln.split()
        k = int(tk[0])
        if tk[1] == "FAIL":
            continue
        if tk[1] not in ("PASS", "NEG"):
            die(f"bad probe line: {ln}")
        lo_m, lo_e = int(tk[2]), int(tk[3])
        trip = [int(x) for x in tk[4:]]
        if len(trip) % 3 != 0 or len(trip) // 3 > nsqrt:
            die(f"leaf {k}: {len(trip)} mantissas, expected at most "
                f"{3 * nsqrt} (reached sqrt nodes only)")
        verdicts[k] = (tk[1], lo_m, lo_e,
                       [tuple(trip[j:j + 3]) for j in range(0, len(trip), 3)])
    if rung is None:
        die("no RUNG header in params file")
    return rung, verdicts


def hull_stage_b_file(mod, n, expr, rows, rung, nsqrt, ndiv, ntrans,
                      meta, extra):
    """Stage-B kernel pilot: per-leaf box, filled TMParams and a kernel
    `decide` theorem stating that `checkPosTMHull` reproduces the stage-A
    verdict (`= true` on PASS leaves, `= false` on NEG leaves — the lemma
    proven is the compiled-run/kernel AGREEMENT, not positivity).  All leaf
    theorems are glued into one conjunction for `#print axioms`;
    components reference the leaf theorems, no recomputation."""
    npar, out, g0, g1, g2, g3, g4, g5, g6 = rung
    out_parts, pf = [], []
    for j, (k, box, verdict, lo_m, lo_e, triples) in enumerate(rows, 1):
        sq = ", ".join(f"⟨{a}, {b}, {c}, ({g3}), ({g4})⟩"
                       for a, b, c in triples)
        iv = ", ".join(f"⟨({g0}), ({g1}), ({g2})⟩" for _ in range(ndiv))
        tv = ", ".join(f"⟨({g5}), ({g6})⟩" for _ in range(ntrans))
        out_parts.append(
            f"/-- Leaf {k} of the stage-A sample: box, filled TMParams,\n"
            f"kernel verdict check.  Stage-A margin: loBound {lo_m} * 2^({lo_e}),\n"
            f"verdict {verdict}. -/\n"
            f"def {mod}Box{j} : Fin {n} → DInterval :=\n  {box_lit(box)}\n\n"
            f"def {mod}P{j} : TMParams := ⟨[{sq}], [{iv}], [{tv}]⟩\n\n"
            f"theorem {mod}Leaf{j} :\n"
            f"    checkPosTMHull {mod}Expr {mod}Box{j} {mod}P{j} = "
            f"{'true' if verdict == 'PASS' else 'false'} := by\n  decide\n")
        pf.append((f"{mod}Leaf{j}",
                   f"checkPosTMHull {mod}Expr {mod}Box{j} {mod}P{j} = "
                   f"{'true' if verdict == 'PASS' else 'false'}"))
    goal = " ∧\n    ".join(v for _, v in pf)
    conj = (f"⟨{', '.join(t for t, _ in pf)}⟩" if len(pf) > 1
            else pf[0][0])
    body = "\n".join(out_parts)
    return (HDR.format(nleaves=len(rows), extra=extra, **meta) +
            "import Kepler.Interval.CertTM\n\n"
            "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "namespace Kepler.Interval.Cases\n\n"
            "/-- The case expression for the hull route (dummy sqrt slots;\n"
            f"atan rungs baked: open ({npar}, ({out})), closed (2048, -64)). -/\n"
            f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
            + body +
            "\n/-- Kernel/compiled-run agreement on all pilot leaves; the\n"
            "conjunction references the leaf theorems, so no positivity\n"
            "computation is repeated. -/\n"
            f"theorem {mod}_pilot :\n    {goal} :=\n  {conj}\n\n"
            f"#print axioms {mod}_pilot\n\n"
            "end Kepler.Interval.Cases\n")


def hull_main(case, cid, mod, n, args, params_file, gran, rung_n, rung_out,
              nleaves, max_leaves=None, manifest_file=None):
    """The `--hull` driver: stage A (probe driver emission) or stage B
    (kernel certificate emission from the probe output)."""
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    meta = dict(caseid=cid, origop=case.get("orig_op"), vars=case["vars"],
                prec="-")
    if params_file is None:
        boxes, ntm, stride = hull_sel_boxes(args[1], nleaves)
        open(os.path.splitext(args[2])[0] + ".manifest.json", "w").write(
            json.dumps({"case": cid, "ntm": ntm, "stride": stride,
                        "want": len(boxes), "gran": gran,
                        "rung": [rung_n, rung_out], "nsqrt": nsqrt,
                        "ndiv": ndiv, "ntrans": ntrans}, indent=1))
        open(args[2], "w").write(hull_stage_a_file(
            mod, n, expr, boxes, gran, rung_n, rung_out,
            nsqrt, ndiv, ntrans, len(boxes), meta,
            f" — SCHEMA-V3 HULLD PILOT stage A: {ntm} tm leaves, stride {stride}"))
        print(f"emit_lean: wrote {args[2]} (M2b hull stage A: {len(boxes)} "
              f"tm leaves of {ntm}, stride {stride}, sqrt {nsqrt}, div "
              f"{ndiv}, trans {ntrans}; run `lake env lean --run {args[2]} "
              f"> params.txt`)")
        return
    mfpath = (manifest_file or
              os.path.splitext(params_file)[0] + ".manifest.json")
    if not os.path.exists(mfpath):
        # params.txt often sits next to the stage-A driver under a
        # `.params.txt` name — try the driver-side manifest too
        alt = os.path.splitext(
            os.path.splitext(params_file)[0])[0] + ".manifest.json"
        if os.path.exists(alt):
            mfpath = alt
    mf = json.load(open(mfpath))
    if mf["nsqrt"] != nsqrt or mf["ndiv"] != ndiv or mf["ntrans"] != ntrans:
        die("manifest node counts mismatch the case prog — wrong inputs?")
    rung, verdicts = parse_hull_params(params_file, nsqrt)
    if not verdicts:
        die("no evaluated leaves in stage-A output — nothing to pilot")
    boxes, ntm, stride = hull_sel_boxes(
        args[1], mf["want"], stride=mf["stride"])
    if len(boxes) < max(verdicts) + 1:
        die(f"manifest sample reproduced only {len(boxes)} boxes, need "
            f"{max(verdicts) + 1}")
    rows = []
    for j, k in enumerate(sorted(verdicts)):
        if max_leaves is not None and len(rows) >= max_leaves:
            break
        verdict, lo_m, lo_e, trip = verdicts[k]
        rows.append((k, boxes[k], verdict, lo_m, lo_e, trip))
    n_pos = sum(1 for r in rows if r[2] == "PASS")
    open(args[2], "w").write(hull_stage_b_file(
        mod, n, expr, rows, rung, nsqrt, ndiv, ntrans, meta,
        f" — SCHEMA-V3 HULLD PILOT stage B: kernel verdicts on {len(rows)} of "
        f"{ntm} tm leaves ({n_pos} PASS, {len(rows) - n_pos} NEG); NEG\n"
        "  leaves are NOT certificates — the lemma proven per leaf is the\n"
        "  kernel/compiled-run agreement (see CertTM.lean M2b section)"))
    print(f"emit_lean: wrote {args[2]} (M2b hull stage B: {len(rows)} "
          f"leaves of {ntm} tm leaves — {n_pos} PASS, "
          f"{len(rows) - n_pos} NEG)")






# ---------------------------------------------------------------------------
# W4 route (a): mirror gsplit (`--gsplit=a` / `--gsplit=b`, W3 fix route for
# guard-straddle NEG leaves).  The C side closes straddle leaves with
# `--gsplit2` (bb_arb_mono.c: gsplit2_dim guard-sensitivity bisection), but
# the gsplit sub-boxes never enter the certificate — mirroring the split on
# the Lean side keeps the solver certificates untouched.  The split itself is
# done here in exact rational interval arithmetic (no solver rerun): per NEG
# tm leaf, the guards straddling on the leaf box are bisected away (each step
# halves the dim with the smallest post-split straddle sum = largest
# straddle-width decrease; exact midpoints; depth cap 12), leaving
# guard-signed single-branch sub-boxes + at most one residual.
#
#   stage A round 2:  emit_lean.py <case.json> <cert.json> <outA2.lean> --hull \
#                     --gsplit=a --params=<round-1 params> \
#                     [--manifest=<round-1 manifest>] [--gsplit-depth=12]
#     reads the round-1 stage-A probe output, finds the NEG leaves, runs the
#     mirror bisection on each, and writes
#       <outA2 base>.manifest.json   sub-box manifest (schema gsplit-subboxes)
#       <outA2.lean>                 round-2 probe driver over all sub-boxes
#     (line-flushed: every result line to stdout *and* stderr with explicit
#     flushes — W3 minefield: redirected stdout is block-buffered, and a
#     killed run must keep its partial params).
#   stage B:  emit_lean.py <case.json> <cert.json> <outB.lean> --hull \
#             --gsplit=b --params=<round-2 params> [--max-leaves=N]
#     emits the kernel certificate over the sub-boxes from the round-2
#     manifest (auto-detected next to the round-2 params): per sub-box
#       theorem <mod>LeafK : checkPosTMHull ... = true|false := by decide
#     (NEG sub-boxes keep `= false`: the proven lemma is the compiled-run /
#     kernel agreement).  Residual sub-boxes stay NEG by construction.
#
#   Mirror validity anchor (W3/W4): on split_0_2 leaf 0 at rung (128, -80),
#   gran -80, this reproduces the W3 13-sub-box partition
#   (/tmp/p4w3/subboxes.json: 12 guard-signed + 1 residual sb0) exactly.
# ---------------------------------------------------------------------------

class GSplitError(Exception):
    pass


def gsplit_guards(case):
    """All ite guard progs of the case, traversal order."""
    guards = []

    def walk(prog):
        for op in prog:
            if isinstance(op, dict):
                it = op["ite"]
                guards.append(it["cond"])
                walk(it["cond"])
                walk(it["then"])
                walk(it["else"])

    walk(case["prog"])
    return guards


def gsplit_eval(prog, bx):
    """Exact-rational interval evaluation of a guard prog on a Fraction box
    (mirror of the C bare-interval guard probe; ite polarity per the kernel:
    guard interval negative -> then, nonnegative -> else, straddle -> hull of
    both branches; sqrt floors/ceilings via isqrt).  Raises GSplitError on
    ops the mirror cannot soundly evaluate (atan/trans guards)."""
    def isqrt_hi(x):
        n, d = x.numerator, x.denominator
        return Fraction(0) if n <= 0 else Fraction(math.isqrt(n * d - 1) + 1, d)

    def isqrt_lo(x):
        n, d = x.numerator, x.denominator
        return Fraction(0) if n <= 0 else Fraction(math.isqrt(n * d), d)

    st = []
    for op in prog:
        if isinstance(op, dict):
            it = op["ite"]
            cc = gsplit_eval(it["cond"], bx)
            if cc[1] < 0:
                st.append(gsplit_eval(it["then"], bx))
            elif cc[0] >= 0:
                st.append(gsplit_eval(it["else"], bx))
            else:
                t = gsplit_eval(it["then"], bx)
                e = gsplit_eval(it["else"], bx)
                st.append((min(t[0], e[0]), max(t[1], e[1])))
            continue
        o = op[0]
        if o == "push_const":
            q = Fraction(op[1]["num"], op[1]["den"])
            st.append((q, q))
        elif o == "push_var":
            st.append(bx[op[1]])
        elif o == "mul":
            b = st.pop()
            a = st.pop()
            st.append((min(a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]),
                       max(a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])))
        elif o == "add":
            b = st.pop()
            a = st.pop()
            st.append((a[0] + b[0], a[1] + b[1]))
        elif o == "sub":
            b = st.pop()
            a = st.pop()
            st.append((a[0] - b[1], a[1] - b[0]))
        elif o == "neg":
            a = st.pop()
            st.append((-a[1], -a[0]))
        elif o == "abs":
            a = st.pop()
            if a[1] <= 0:
                st.append((-a[1], -a[0]))
            elif a[0] >= 0:
                st.append(a)
            else:
                st.append((Fraction(0), max(-a[0], a[1])))
        elif o == "sqrt":
            a = st.pop()
            st.append((isqrt_lo(max(Fraction(0), a[0])),
                       isqrt_hi(max(Fraction(0), a[1]))))
        elif o == "div":
            b = st.pop()
            a = st.pop()
            if b[0] <= 0 <= b[1]:
                raise GSplitError("guard divides by a 0-straddling interval")
            qs = [a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1]]
            st.append((min(qs), max(qs)))
        else:
            raise GSplitError(f"guard op {o!r} unsupported in the gsplit "
                              "mirror (no trans/atan guards)")
    return st[-1]


def gsplit_subboxes(guards, frbox, depth):
    """Guard-guided bisection (mirror of gsplit2_dim's intent, W3 make_subboxes
    semantics): priority queue by guard-straddle width; each step bisects the
    dim whose post-split straddle sum is smallest (= straddle-width decrease
    largest) at the exact midpoint; a box is terminal when the guard set is
    signed on it, or at the depth cap (residual).  Returns
    [(residual, Fraction box), ...] in completion order."""
    def strad(bx):
        w = Fraction(0)
        for g in guards:
            r = gsplit_eval(g, bx)
            if r[0] <= 0 <= r[1]:
                w += r[1] - r[0]
        return w

    def split(bx):
        best, bw = None, None
        for d in range(len(bx)):
            lo, hi = bx[d]
            if lo == hi:
                continue
            mid = (lo + hi) / 2
            w = Fraction(0)
            for half in ((lo, mid), (mid, hi)):
                nb = list(bx)
                nb[d] = half
                w += strad(nb)
            if bw is None or w < bw:
                best, bw = d, w
        return best

    work = [(strad(frbox), 0, frbox)]
    done = []
    while work:
        work.sort(key=lambda t: -t[0])
        w, dep, bx = work.pop(0)
        if w == 0 or dep >= depth:
            done.append((w > 0, bx))
            continue
        d = split(bx)
        lo, hi = bx[d]
        mid = (lo + hi) / 2
        for half in ((lo, mid), (mid, hi)):
            nb = list(bx)
            nb[d] = half
            work.append((strad(nb), dep + 1, nb))
    return done


def frac_dyadic_at(fr, e, upper):
    """Fraction -> ((m, e), rounded?) with value m*2^e: exact when fr*2^-e is
    integral, otherwise floor/ceil (sound outer rounding — lower bounds round
    down, upper bounds round up)."""
    if e <= 0:
        m, r = divmod(fr.numerator * (1 << -e), fr.denominator)
    else:
        m, r = divmod(fr.numerator, fr.denominator * (1 << e))
    if r and upper:
        m += 1
    return (m, e), bool(r)


def gsplit_stage_a_file(mod, n, expr, boxes, gran, rung_n, rung_out,
                        nsqrt, ndiv, ntrans, meta, extra):
    """Stage-A round-2 probe driver over the gsplit sub-boxes.  Same
    probe-loop shape as the plain hull stage A, but every output line goes
    through `probeOut` (stdout + stderr, both explicitly flushed): redirected
    stdout is block-buffered, and a killed run must keep its partial params
    (W3 diagSB post-mortem).  stderr additionally carries per-box progress."""
    g = f"({gran})"
    boxes_lean = ",\n    ".join(
        f"({box_lit(b)} : Fin {n} → DInterval)" for b in boxes)
    return (HDR.format(nleaves=len(boxes), extra=extra, **meta) +
            "import Kepler.Interval.CertTM\n\n"
            "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n"
            "open Kepler.Interval\n\n"
            "/-- Local default (for `Array.get!` in the probe loop only). -/\n"
            "instance : Inhabited DInterval := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩\n\n"
            "/-- Line-flushed output: each line to stdout *and* stderr with\n"
            "explicit flushes.  Redirected stdout is block-buffered (W3\n"
            "minefield: a 3 h run looked dead at 0 bytes), and a killed run\n"
            "must keep its partial params — stderr is the live mirror. -/\n"
            "def probeOut (s : String) : IO Unit := do\n"
            "  let out ← IO.getStdout\n"
            "  out.putStr s\n"
            "  out.flush\n"
            "  let err ← IO.getStderr\n"
            "  err.putStr s\n"
            "  err.flush\n\n"
            "/-- The case expression for the hull route: dummy `(0, 0)`\n"
            "sqrt slots (mantissas are carried in `TMParams.sqrtCerts`,\n"
            "not in the AST); closed atan args pinned at (2048, -64),\n"
            f"open atan args at the pilot rung ({rung_n}, {rung_out}). -/\n"
            f"def {mod}Expr : IExpr {n} :=\n  {expr}\n\n"
            "/-- Template TMParams: dummy mantissas, pilot recip\n"
            f"granularity {gran} everywhere. -/\n"
            f"def {mod}Ps : TMParams :=\n"
            f"  ⟨List.replicate {nsqrt} ⟨0, 0, 0, {g}, {g}⟩,\n"
            f"   List.replicate {ndiv} ⟨{g}, {g}, {g}⟩,\n"
            f"   List.replicate {ntrans} ⟨{g}, {g}⟩⟩\n\n"
            f"/-- The {len(boxes)} gsplit sub-boxes (guard-guided bisection\n"
            "of the round-1 NEG leaves; see the emitted manifest). -/\n"
            f"def {mod}Boxes : Array (Fin {n} → DInterval) :=\n  #["
            + boxes_lean + "]\n\n"
            f"def main : List String → IO UInt32 := fun _ => do\n"
            f"  probeOut \"RUNG {rung_n} {rung_out} {g} {g} {g} {g} {g} {g} {g}\\n\"\n"
            "  let err ← IO.getStderr\n"
            f"  for i in [0:{mod}Boxes.size] do\n"
            "    let tms ← IO.monoMsNow\n"
            f"    err.putStr s!\"[gsplit] sub-box {{i}}/{{{mod}Boxes.size}} ms={{tms}}\\n\"\n"
            "    err.flush\n"
            f"    match tmHullLeafProbe {mod}Expr {mod}Boxes[i]! {mod}Ps with\n"
            "    | some (p, m, e, l) =>\n"
            "        let v := if p then \"PASS\" else \"NEG\"\n"
            "        let trip := String.intercalate \" \"\n"
            "          (l.map fun t => s!\"{t.1} {t.2.1} {t.2.2}\")\n"
            "        probeOut s!\"{i} {v} {m} {e} {trip}\\n\"\n"
            "    | none => probeOut s!\"{i} FAIL\\n\"\n"
            "  return 0\n")


def gsplit_main(case, cid, mod, n, args, params_file, manifest_file, gran,
                rung_n, rung_out, depth, stage_b, max_leaves=None):
    """`--gsplit` driver: stage A round 2 (NEG leaves -> sub-boxes + probe
    driver) or stage B (kernel decide theorems over the sub-boxes)."""
    if params_file is None:
        die("--gsplit needs --params=FILE (round-1 stage-A output for "
            "stage A round 2, round-2 stage-A output for stage B)")
    expr, nsqrt, ndiv, ntrans = hull_expr(case, rung_n, rung_out)
    meta = dict(caseid=cid, origop=case.get("orig_op"), vars=case["vars"],
                prec="-")
    if not stage_b:
        # ---- stage A round 2 ------------------------------------------------
        mfpath = (manifest_file or
                  os.path.splitext(params_file)[0] + ".manifest.json")
        if not os.path.exists(mfpath):
            die(f"round-1 manifest not found: {mfpath} (pass --manifest=)")
        r1mf = json.load(open(mfpath))
        if r1mf.get("schema") == "gsplit-subboxes":
            die(f"{mfpath} is a gsplit-subboxes manifest; --gsplit=a needs "
                "the ROUND-1 stage-A params/manifest")
        for key in ("want", "stride"):
            if key not in r1mf:
                die(f"round-1 manifest missing {key}")
        rung1, verdicts = parse_hull_params(params_file, nsqrt)
        if rung1 != (rung_n, rung_out) + tuple([gran] * 7):
            die(f"round-1 params rung {rung1} != CLI rung/gran "
                f"{(rung_n, rung_out, gran)} — pass the discovering rung")
        neg = [k for k in sorted(verdicts) if verdicts[k][0] == "NEG"]
        if not neg:
            die("no NEG leaves in the round-1 output — nothing to gsplit")
        boxes, ntm, stride = hull_sel_boxes(
            args[1], r1mf["want"], stride=r1mf["stride"])
        if len(boxes) < max(neg) + 1:
            die(f"sample reproduced only {len(boxes)} boxes, need "
                f"{max(neg) + 1} (round-1 manifest want/stride mismatch?)")
        subs, nrounded = [], 0
        for k in neg:
            frbox = [(dval(lo), dval(hi)) for lo, hi in boxes[k]]
            strad = []
            for g in gsplit_guards(case):
                try:
                    r = gsplit_eval(g, frbox)
                except GSplitError as ex:
                    die(f"leaf {k}: {ex}")
                if r[0] <= 0 <= r[1]:
                    strad.append(g)
            if not strad:
                die(f"leaf {k}: no guard straddles on the leaf box — not a "
                    "gsplit target (re-run stage A?)")
            for residual, fb in gsplit_subboxes(strad, frbox, depth):
                pairs, bad = [], False
                for lo, hi in fb:
                    dlo, r1 = frac_dyadic_at(lo, gran, False)
                    dhi, r2 = frac_dyadic_at(hi, gran, True)
                    bad = bad or r1 or r2
                    pairs.append([list(dlo), list(dhi)])
                nrounded += bad
                subs.append({"src": k, "residual": residual, "box": pairs})
        gs_mf = {"schema": "gsplit-subboxes", "case": cid,
                 "src_leaves": neg, "depth": depth, "gran": gran,
                 "rung": [rung_n, rung_out], "nsqrt": nsqrt, "ndiv": ndiv,
                 "ntrans": ntrans, "n": len(subs),
                 "nresidual": sum(1 for s in subs if s["residual"]),
                 "rounded_endpoints": nrounded,
                 "subboxes": subs}
        mf_out = os.path.splitext(args[2])[0] + ".manifest.json"
        open(mf_out, "w").write(json.dumps(gs_mf, indent=1))
        open(args[2], "w").write(gsplit_stage_a_file(
            mod, n, expr, [tuple(tuple(p) for p in s["box"]) for s in subs],
            gran, rung_n, rung_out, nsqrt, ndiv, ntrans, meta,
            f" — GSPLIT stage A round 2: {len(subs)} sub-boxes of NEG leaves "
            f"{neg} (depth {depth}, {gs_mf['nresidual']} residual)"))
        print(f"emit_lean: wrote {args[2]} + {mf_out} (gsplit stage A round 2: "
              f"{len(subs)} sub-boxes from NEG leaves {neg}, depth {depth}, "
              f"{gs_mf['nresidual']} residual; run `lake env lean --run "
              f"{args[2]} > params.txt 2> progress.txt`)")
        return
    # ---- stage B over the sub-boxes -----------------------------------------
    mfpath = (manifest_file or
              os.path.splitext(params_file)[0] + ".manifest.json")
    if not os.path.exists(mfpath):
        die(f"gsplit manifest not found: {mfpath} (run --gsplit=a first, or "
            "pass --manifest=)")
    mf = json.load(open(mfpath))
    if mf.get("schema") != "gsplit-subboxes":
        die(f"{mfpath} is not a gsplit-subboxes manifest — --gsplit=b "
            "consumes the round-2 params written next to it")
    if mf["nsqrt"] != nsqrt or mf["ndiv"] != ndiv or mf["ntrans"] != ntrans:
        die("manifest node counts mismatch the case prog — wrong inputs?")
    subs = mf["subboxes"]
    boxes = [tuple((tuple(s["box"][d][0]), tuple(s["box"][d][1]))
                   for d in range(n)) for s in subs]
    rung, verdicts = parse_hull_params(params_file, nsqrt)
    if not verdicts:
        die("no evaluated sub-boxes in stage-A round-2 output")
    rows = []
    for j, s in enumerate(subs):
        if max_leaves is not None and len(rows) >= max_leaves:
            break
        if j not in verdicts:
            continue
        verdict, lo_m, lo_e, trip = verdicts[j]
        rows.append((j, boxes[j], verdict, lo_m, lo_e, trip, s))
    n_pos = sum(1 for r in rows if r[2] == "PASS")
    n_res = sum(1 for r in rows if r[6]["residual"])
    rows6 = [r[:6] for r in rows]
    open(args[2], "w").write(hull_stage_b_file(
        mod, n, expr, rows6, rung, nsqrt, ndiv, ntrans, meta,
        f" — GSPLIT stage B: kernel verdicts on {len(rows)} of {len(subs)} "
        f"sub-boxes ({n_pos} PASS, {len(rows) - n_pos} NEG, {n_res}\n"
        "  residual); NEG rows are NOT certificates — the lemma proven per\n"
        "  row is the kernel/compiled-run agreement (CertTM M2b section)"))
    print(f"emit_lean: wrote {args[2]} (gsplit stage B: {len(rows)} of "
          f"{len(subs)} sub-boxes — {n_pos} PASS, {len(rows) - n_pos} NEG, "
          f"{n_res} residual)")


# ---------------------------------------------------------------------------
# W6 route A prototype: mono dimension reduction over guard-split sub-boxes
# (Python-side SEARCH only; the emitted artifacts are a certificate plan.
# The kernel side — evalReal chain rule + the mono-corner lemma — is W7
# scope; see docs/scouts/mono-corner-scout.md §5 for the route design).
#
#   emit_lean.py <case.json> <subboxes.json> <out> --mono
#                [--mono-budget=N] [--mono-max-depth=N] [--mono-subbox=K]
#
# Per sub-box, recursively:
#   (1) whole-expr TM hull on an exact-rational mirror of the kernel
#       evalTMHullD2 (W5 tm_probe3 semantics: Fractions instead of Dyadic,
#       isqrt at 2^-150, atan exact endpoints; looser than the kernel only
#       by the kernel's own extra slack, never tighter); POS (loBound > 0)
#       -> certificate leaf.
#   (2) ite guard straddle -> bisect a straddling guard's variable (mono
#       needs the branch resolved; sub-boxes of a decided box stay decided).
#   (3) symbolic d/dx_j (branch-resolved; div rule d(l/r) = (r*dl - l*dr)/r^2
#       — the W5 probe version had the numerator sign flipped, W6 finite-
#       difference-verified) + TM hull on the same box -> verdict:
#       flat [0,0] -> free restrict, incr -> restrict to the lo face,
#       decr -> restrict to the hi face (f >= f(face) on the box).
#   (4) no new sign -> single-dim bisection of the dim with the largest
#       promise |mid|/hw of its df enclosure.
#   (5) point box -> TM degenerates to the exact value (err = 0, W5 §5.1
#       fact 2) -> corner certificate.
#
# Every sign/enclosure verdict is replayable kernel-side by checkPosTMHull
# on the same box (subject to the W5 §2.3 kernel-looser fidelity gap), so
# the emitted manifest is directly the W7 stage-A/B work list.
# ---------------------------------------------------------------------------

_MonoSQK = 150  # sqrt precision bits (kernel sqrtI certs are gran -80-ish)
_MONO_REFRESH_AGE = 4  # v5 df refresh policy (see _mono_certify)
_MONO_REFRESH_NEAR = Fraction(1, 2)


def _mono_isqrt_hi(x):
    n, d = x.numerator, x.denominator
    if n <= 0:
        return Fraction(0)
    s = math.isqrt(n * (1 << (2 * _MonoSQK)) * d)
    if s * s < n * (1 << (2 * _MonoSQK)) * d:
        s += 1
    return Fraction(s, (1 << _MonoSQK) * d)


def _mono_isqrt_lo(x):
    n, d = x.numerator, x.denominator
    if n <= 0:
        return Fraction(0)
    return Fraction(math.isqrt(n * (1 << (2 * _MonoSQK)) * d),
                    (1 << _MonoSQK) * d)


def _mono_atan(x):
    """atan endpoints with 2^-300 mpmath slack (atan is not exact-rational
    computable; the kernel instead replays the trans rung ladder — the
    search-side verdict is re-certified kernel-side regardless)."""
    import mpmath
    v = mpmath.mpf(x.numerator) / x.denominator
    a = mpmath.atan(v)
    s, man, exp, bc = a._mpf_
    val = Fraction(man) * (Fraction(2) ** exp)
    val = -val if s else val
    slack = Fraction(1) / (Fraction(2) ** 300)
    return val - slack, val + slack


class _MonoNotes:
    def __init__(self):
        self.div_fallback = 0
        self.div_fail = 0
        self.sqrt_fail = 0
        self.ite_straddle = 0
        self.atan_n = 0
        self.guard_fail = 0


def _mono_iv_mul(I, J):
    a = [I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1]]
    return (min(a), max(a))


def _mono_iv_add(I, J):
    return (I[0] + J[0], I[1] + J[1])


def _mono_hull(I, J):
    return (min(I[0], J[0]), max(I[1], J[1]))


def _mono_abs_hi(I):
    return max(abs(I[0]), abs(I[1]))


def _mono_jump(I, J):
    return max(abs(I[0] - J[1]), abs(I[1] - J[0]), Fraction(0))


class _MonoTM:
    """kernel TaylorM mirror node: fB interval, dfB slope intervals, err."""
    __slots__ = ("fB", "dfB", "err", "n")

    def __init__(self, fB, dfB, err):
        self.fB = fB
        self.dfB = dfB
        self.err = err
        self.n = len(dfB)

    def W0(self, ws):
        s = Fraction(0)
        for d, w in zip(self.dfB, ws):
            s += _mono_abs_hi(d) * w
        return s

    def Wr(self, ws):
        return max(self.W0(ws) + self.err, Fraction(0))

    def valueRange(self, ws):
        w = self.Wr(ws)
        return (self.fB[0] - w, self.fB[1] + w)

    def loBound(self, box, y):
        s = self.fB[0]
        for d, (lo, hi), yi in zip(self.dfB, box, y):
            if lo == hi:
                continue
            a, b = lo - yi, hi - yi
            s += min(d[0] * a, d[0] * b, d[1] * a, d[1] * b)
        return s - self.err


def _mono_const(d, n):
    return _MonoTM((d, d), [(Fraction(0), Fraction(0))] * n, Fraction(0))


def _mono_var(k, box):
    dfB = [(Fraction(0), Fraction(0))] * len(box)
    dfB[k] = (Fraction(1), Fraction(1))
    return _MonoTM(box[k], dfB, Fraction(0))


def _mono_neg(M):
    return _MonoTM((-M.fB[1], -M.fB[0]),
                   [(-d[1], -d[0]) for d in M.dfB], M.err)


def _mono_add(Mf, Mg):
    return _MonoTM(_mono_iv_add(Mf.fB, Mg.fB),
                   [_mono_iv_add(a, b) for a, b in zip(Mf.dfB, Mg.dfB)],
                   Mf.err + Mg.err)


def _mono_mul(Mf, Mg, ws):
    fB = _mono_iv_mul(Mf.fB, Mg.fB)
    dfB = [_mono_iv_add(_mono_iv_mul(a, Mg.fB), _mono_iv_mul(Mf.fB, b))
           for a, b in zip(Mf.dfB, Mg.dfB)]
    W0f, W0g = Mf.W0(ws), Mg.W0(ws)
    ef, eg = Mf.err, Mg.err
    err = (W0f * W0g + ef * (_mono_abs_hi(Mg.fB) + W0g + eg)
           + eg * (_mono_abs_hi(Mf.fB) + W0f))
    return _MonoTM(fB, dfB, err)


def _mono_sqrt(M, ws, nt):
    W = M.Wr(ws)
    c = M.fB[0] - W
    if c <= 0:
        nt.sqrt_fail += 1
        return None
    Jl, Jh = _mono_isqrt_lo(M.fB[0]), _mono_isqrt_hi(M.fB[1])
    if Jl > Jh:
        Jl = Fraction(0)
    twoJl, twoJh = 2 * Jl, 2 * Jh
    if twoJl <= 0 <= twoJh:
        nt.sqrt_fail += 1
        return None
    J = (Fraction(1) / twoJh, Fraction(1) / twoJl)
    dfB = [_mono_iv_mul(d, J) for d in M.dfB]
    K = Fraction(1) / (8 * c * _mono_isqrt_hi(c))
    return _MonoTM((Jl, Jh), dfB, M.err * J[1] + W * W * K)


def _mono_inv(M, ws, nt):
    W = M.Wr(ws)
    cpos = M.fB[0] - W
    cneg = -(M.fB[1] + W)
    if cpos > 0:
        c = cpos
    elif cneg > 0:
        c = cneg
    else:
        nt.div_fail += 1
        return None
    a = _mono_abs_hi(M.fB)
    V = (Fraction(1) / M.fB[1], Fraction(1) / M.fB[0])
    Jp = (Fraction(1) / (a * a), Fraction(1) / (c * c))
    dfB = [_mono_iv_mul(d, (-Jp[1], -Jp[0])) for d in M.dfB]
    K = Fraction(1) / (c * c * c)
    return _MonoTM(V, dfB, M.err * Jp[1] + W * W * K)


def _mono_div(Mf, Mg, ws, nt):
    Mi = _mono_inv(Mg, ws, nt)
    if Mi is not None:
        return _mono_mul(Mf, Mi, ws)
    J = Mg.fB
    if J[0] <= 0 <= J[1]:
        nt.div_fail += 1
        return None
    qs = [Mf.fB[0] / J[0], Mf.fB[0] / J[1], Mf.fB[1] / J[0], Mf.fB[1] / J[1]]
    nt.div_fallback += 1
    return _MonoTM((min(qs), max(qs)), [(Fraction(0), Fraction(0))] * Mf.n,
                   Fraction(0))


def _mono_atan_tm(M, ws, nt, closed):
    nt.atan_n += 1
    if closed:
        lo = _mono_atan(M.fB[0])[0]
        hi = _mono_atan(M.fB[1])[1]
        return _MonoTM((lo, hi), [(Fraction(0), Fraction(0))] * M.n,
                       Fraction(0))
    W = M.Wr(ws)
    alo, ahi = _mono_atan(M.fB[0])[0], _mono_atan(M.fB[1])[1]
    al2 = _mono_abs_hi(M.fB)
    J = (Fraction(1) / (1 + al2 * al2), Fraction(1))
    dfB = [_mono_iv_mul(d, J) for d in M.dfB]
    C = min(Fraction(7, 8), 2 * (_mono_abs_hi(M.fB) + W))
    return _MonoTM((alo, ahi), dfB, M.err * J[1] + W * W * C)


def _mono_closed_map(prog):
    """per op-index: is the subtree ending at this op var-free?"""
    out = {}
    st = []
    for i, op in enumerate(prog):
        if isinstance(op, dict):
            it = op["ite"]
            cl = all(
                not any(isinstance(o, dict) or o[0] == "push_var" for o in sub)
                for sub in (it["cond"], it["then"], it["else"]))
            st.append(cl)
            out[i] = cl
            continue
        o = op[0]
        if o in ("push_const", "push_var"):
            cl = (o == "push_const")
        elif o in ("neg", "abs", "sqrt", "atan"):
            cl = st.pop()
        else:
            b = st.pop()
            a = st.pop()
            cl = a and b
        st.append(cl)
        out[i] = cl
    return out


def _mono_teval(prog, box, y, ws, nt, cmap):
    st = []
    for i, op in enumerate(prog):
        if isinstance(op, dict):
            it = op["ite"]
            cc = gsplit_eval(it["cond"], box)
            if cc is None:
                nt.guard_fail += 1
                st.append(None)
            elif cc[1] < 0:
                st.append(_mono_teval(it["then"], box, y, ws, nt,
                                      _mono_closed_map(it["then"])))
            elif cc[0] >= 0:
                st.append(_mono_teval(it["else"], box, y, ws, nt,
                                      _mono_closed_map(it["else"])))
            else:
                nt.ite_straddle += 1
                Mt = _mono_teval(it["then"], box, y, ws, nt,
                                 _mono_closed_map(it["then"]))
                Me = _mono_teval(it["else"], box, y, ws, nt,
                                 _mono_closed_map(it["else"]))
                if Mt is None or Me is None:
                    st.append(None)
                else:
                    vrT, vrE = Mt.valueRange(ws), Me.valueRange(ws)
                    fB = _mono_hull(vrT, vrE)
                    dfB = [_mono_hull(a, b)
                           for a, b in zip(Mt.dfB, Me.dfB)]
                    nt_err = max(Mt.err, Me.err) + _mono_jump(vrT, vrE)
                    st.append(_MonoTM(fB, dfB, nt_err))
            continue
        o = op[0]
        if o == "push_const":
            st.append(_mono_const(Fraction(op[1]["num"], op[1]["den"]),
                                  len(box)))
        elif o == "push_var":
            st.append(_mono_var(op[1], box))
        elif o == "add":
            b = st.pop()
            a = st.pop()
            st.append(None if (a is None or b is None) else _mono_add(a, b))
        elif o == "sub":
            b = st.pop()
            a = st.pop()
            st.append(None if (a is None or b is None)
                      else _mono_add(a, _mono_neg(b)))
        elif o == "mul":
            b = st.pop()
            a = st.pop()
            st.append(None if (a is None or b is None)
                      else _mono_mul(a, b, ws))
        elif o == "neg":
            a = st.pop()
            st.append(None if a is None else _mono_neg(a))
        elif o == "abs":
            a = st.pop()
            st.append(None if a is None else
                      _MonoTM(_mono_hull((-a.fB[1], -a.fB[0])
                                         if a.fB[1] <= 0 else
                                         ((Fraction(0), _mono_abs_hi(a.fB))
                                          if a.fB[0] < 0 else a.fB)),
                              [(Fraction(0), Fraction(0))] * a.n,
                              Fraction(0)))
        elif o == "sqrt":
            a = st.pop()
            st.append(None if a is None else _mono_sqrt(a, ws, nt))
        elif o == "div":
            b = st.pop()
            a = st.pop()
            st.append(None if (a is None or b is None)
                      else _mono_div(a, b, ws, nt))
        elif o == "atan":
            a = st.pop()
            st.append(None if a is None
                      else _mono_atan_tm(a, ws, nt, cmap[i]))
        else:
            raise ValueError(o)
    return st[-1]


class _MonoT2:
    __slots__ = ("kind", "op", "l", "r", "start", "end", "prog")

    def __init__(self, kind, op=None, l=None, r=None, start=0, end=0,
                 prog=None):
        self.kind, self.op, self.l, self.r = kind, op, l, r
        self.start, self.end, self.prog = start, end, prog


def _mono_parse2(prog):
    """expression tree with RPN slices (mul/div/sqrt/atan diff rules splice
    the ORIGINAL slices back together around the derivative progs)."""
    st = []
    for i, op in enumerate(prog):
        if isinstance(op, dict):
            st.append(_MonoT2("ite", op, start=i, end=i, prog=[op]))
        elif op[0] in ("push_const", "push_var"):
            st.append(_MonoT2("leaf", op, start=i, end=i, prog=[op]))
        elif op[0] in ("neg", "abs", "sqrt", "atan"):
            a = st.pop()
            st.append(_MonoT2(op[0], op, l=a, start=a.start, end=i,
                              prog=prog[a.start:i + 1]))
        else:
            b = st.pop()
            a = st.pop()
            st.append(_MonoT2(op[0], op, l=a, r=b, start=a.start, end=i,
                              prog=prog[a.start:i + 1]))
    assert len(st) == 1
    return st[0]


def _mono_diff(t, j, box):
    """branch-resolved symbolic d/dx_j as an RPN prog; 'ok' | 'nondiff'.
    (Finite-difference-verified W6: all rules exact on split_0_2 leaf 0,
    including div — the W5 probe numerator l*dr - r*dl was sign-flipped.)"""
    if t.kind == "leaf":
        op = t.op
        if op[0] == "push_var":
            return ([["push_const", {"num": 1, "den": 1}]] if op[1] == j
                    else [["push_const", {"num": 0, "den": 1}]]), "ok"
        return [["push_const", {"num": 0, "den": 1}]], "ok"
    if t.kind == "neg":
        dp, s = _mono_diff(t.l, j, box)
        return dp + [["neg"]], s
    if t.kind in ("add", "sub"):
        dp1, s1 = _mono_diff(t.l, j, box)
        dp2, s2 = _mono_diff(t.r, j, box)
        return (dp1 + dp2 + [[t.kind]],
                "nondiff" if "nondiff" in (s1, s2) else "ok")
    if t.kind == "mul":
        dp1, s1 = _mono_diff(t.l, j, box)
        dp2, s2 = _mono_diff(t.r, j, box)
        return (t.l.prog + dp2 + [["mul"]] + t.r.prog + dp1 + [["mul"]]
                + [["add"]],
                "nondiff" if "nondiff" in (s1, s2) else "ok")
    if t.kind == "div":
        dp1, s1 = _mono_diff(t.l, j, box)
        dp2, s2 = _mono_diff(t.r, j, box)
        num = (t.l.prog + dp2 + [["mul"]] + t.r.prog + dp1 + [["mul"]]
               + [["sub"], ["neg"]])
        return (num + t.r.prog + t.r.prog + [["mul"]] + [["div"]],
                "nondiff" if "nondiff" in (s1, s2) else "ok")
    if t.kind == "sqrt":
        dp, s = _mono_diff(t.l, j, box)
        return (dp + [["push_const", {"num": 2, "den": 1}]] + t.l.prog
                + [["sqrt"], ["mul"], ["div"]], s)
    if t.kind == "atan":
        dp, s = _mono_diff(t.l, j, box)
        den = ([["push_const", {"num": 1, "den": 1}]] + t.l.prog + t.l.prog
               + [["mul"], ["add"]])
        return dp + den + [["div"]], s
    if t.kind == "abs":
        dp, s = _mono_diff(t.l, j, box)
        return dp + [["abs"]], "nondiff"
    if t.kind == "ite":
        it = t.op["ite"]
        cc = gsplit_eval(it["cond"], box)
        if cc[1] < 0:
            return _mono_diff(_mono_parse2(it["then"]), j, box)
        if cc[0] >= 0:
            return _mono_diff(_mono_parse2(it["else"]), j, box)
        return None, "straddle"
    raise ValueError(t.kind)


class _MonoBudget(Exception):
    pass


def _mono_eval_prog(prog, box, budget):
    """TM-eval prog on box -> (M, nt, y, ws); raises _MonoBudget."""
    if budget[0] <= 0:
        raise _MonoBudget()
    budget[0] -= 1
    y = [(lo + hi) / 2 for lo, hi in box]
    ws = [(hi - lo) / 2 for lo, hi in box]
    nt = _MonoNotes()
    M = _mono_teval(prog, box, y, ws, nt, _mono_closed_map(prog))
    return M, nt, y, ws


def _mono_collect_vars(prog, acc):
    for op in prog:
        if isinstance(op, dict):
            it = op["ite"]
            for sub in (it["cond"], it["then"], it["else"]):
                _mono_collect_vars(sub, acc)
        elif op[0] == "push_var":
            acc.add(op[1])


def _mono_guard_split_dim(guards, box):
    """a max-width dim of some straddling guard (None if all fixed)."""
    best, bw = None, Fraction(0)
    for g in guards:
        try:
            r = gsplit_eval(g, box)
        except GSplitError:
            continue
        if r[0] <= 0 <= r[1]:
            vs = set()
            _mono_collect_vars(g, vs)
            for j in vs:
                w = box[j][1] - box[j][0]
                if w > bw:
                    best, bw = j, w
    return best


def _mono_df_enclosure(root, box, j, budget, st):
    """sound df_j enclosure + its loBound folded in, or None on any failure."""
    try:
        dp, status = _mono_diff(root, j, box)
    except (GSplitError, ValueError):
        return None
    if dp is None or status != "ok":
        return None
    try:
        Md, ntd, yd, wsd = _mono_eval_prog(dp, box, budget)
    except _MonoBudget:
        raise
    except (GSplitError, ZeroDivisionError, ValueError):
        return None
    if Md is None:
        return None
    st["df_evals"] += 1
    vr = Md.valueRange(wsd)
    dlb = Md.loBound(box, yd)
    return (min(vr[0], dlb), vr[1])


def _mono_verdict_of(enc):
    """'incr' | 'decr' | 'flat' | None from a df enclosure."""
    if enc is None:
        return None
    elo, ehi = enc
    if elo == 0 and ehi == 0:
        return "flat"
    if elo > 0:
        return "incr"
    if ehi < 0:
        return "decr"
    return None


def _mono_promise_of(enc):
    elo, ehi = enc
    mid, hw = (elo + ehi) / 2, (ehi - elo) / 2
    return abs(mid) / hw if hw > 0 else Fraction(10) ** 30


def _mono_certify(prog, root, box, guards, budget, st, depth, max_depth,
                  log, df_cache=None, age=None):
    """recursive mono reduction, v5.  st: mutable stats/cert accumulator.
    Returns 'POS' | 'NEG' | 'FAIL' | 'CAP'.

    df enclosures INHERITED via df_cache remain sound on subboxes (an
    interval over a superset box is a valid enclosure over the subset), so
    sign checks at every node are FREE cache reads; a dim's df is actually
    re-evaluated only (a) at the root, (b) after a restrict event, (c) when
    its cached promise is near-signing and the cache is stale
    (_MONO_REFRESH_AGE cuts, one dim per node max).  Signed/flat dims
    restrict to their min face for free; otherwise bisect the free dim
    picked by a STRICT round-robin cycle over the promise-ordered dims
    (promise fixes only the cycle start): the W6-measured df enclosures
    are cross-share dominated (own-dim share ~6% per halving), and a
    max-promise rule with near-equal promises degenerates into 2-dim
    alternation — a balanced kd-tree spread needs every dim cut (leaf
    count C(d+5,5), polynomial in depth)."""
    if depth > max_depth:
        st["cap"] += 1
        return "CAP"
    if df_cache is None:
        df_cache = {}
        age = {}
    try:
        M, nt, y, ws = _mono_eval_prog(prog, box, budget)
    except _MonoBudget:
        raise
    except (GSplitError, ZeroDivisionError, ValueError) as ex:
        st["fails"] += 1
        log(f"      teval error d{depth}: {type(ex).__name__}")
        return "FAIL"
    if M is None:
        st["fails"] += 1
        return "FAIL"
    lb = M.loBound(box, y)
    if lb > 0:
        st["corners"] += 1
        st["certs"].append({"kind": "enclosure", "depth": depth,
                            "box": _mono_box_str(box),
                            "loBound": _mono_fmt(lb)})
        log(f"      d{depth} POS lb={_mono_fmt(lb)} corners={st['corners']}")
        return "POS"
    if nt.ite_straddle > 0:
        d = _mono_guard_split_dim(guards, box)
        if d is None:
            d = max(range(len(box)), key=lambda j: box[j][1] - box[j][0])
        st["guard_splits"] += 1
        log(f"      d{depth} guard-bisect dim={d}")
        return _mono_split_two(prog, root, box, guards, budget, st, depth,
                               max_depth, d, log, df_cache, age)
    free = [j for j in range(len(box)) if box[j][0] != box[j][1]]
    if not free:
        st["neg_points"] += 1
        st["certs"].append({"kind": "point-NEG", "depth": depth,
                            "box": _mono_box_str(box),
                            "loBound": _mono_fmt(lb)})
        log(f"      d{depth} POINT NEG lb={_mono_fmt(lb)}")
        return "NEG"
    if not df_cache:
        # root: measure every free dim once
        for j in free:
            fresh = _mono_df_enclosure(root, box, j, budget, st)
            if fresh is not None:
                df_cache[j] = fresh
                age[j] = 0
    # near-signing refresh: at most one dim per node, aged caches only
    # (df tevals dominate the mirror cost: ~54k-op derivative programs,
    # W6-measured 163 s each at 2^-150 endpoints vs 4 s for the whole expr)
    cand = None
    for j in free:
        enc = df_cache.get(j)
        if (enc is not None and age.get(j, 0) > _MONO_REFRESH_AGE
                and _mono_promise_of(enc) > _MONO_REFRESH_NEAR):
            cand = j
            break
    if cand is not None:
        fresh = _mono_df_enclosure(root, box, cand, budget, st)
        if fresh is not None:
            df_cache[cand] = fresh
            age[cand] = 0
    signs = {}
    promise = {}
    for j in free:
        enc = df_cache.get(j)
        v = _mono_verdict_of(enc)
        if v is not None:
            signs[j] = v
        elif enc is not None:
            promise[j] = _mono_promise_of(enc)
    if signs:
        nb = list(box)
        ncache, nage = dict(df_cache), dict(age)
        for j, s in signs.items():
            nb[j] = ((box[j][0], box[j][0]) if s in ("incr", "flat")
                     else (box[j][1], box[j][1]))
            ncache.pop(j, None)
            nage.pop(j, None)
        st["mono_restricts"] += len(signs)
        st["certs"].append({"kind": "mono", "depth": depth,
                            "box": _mono_box_str(box),
                            "signs": {str(j): s for j, s in signs.items()}})
        log(f"      d{depth} mono restrict {signs}")
        return _mono_certify(prog, root, nb, guards, budget, st, depth + 1,
                             max_depth, log, ncache, nage)
    if not promise:
        log(f"      d{depth} no df verdicts on free dims {free} -> FAIL")
        st["fails"] += 1
        return "FAIL"
    order = sorted(free, key=lambda j: -promise[j])
    d = order[depth % len(order)]
    st["sign_splits"] += 1
    log(f"      d{depth} bisect dim={d} promise={float(promise[d]):.4g}")
    nage = {j: a + 1 for j, a in age.items()}
    return _mono_split_two(prog, root, box, guards, budget, st, depth,
                           max_depth, d, log, df_cache, nage)


def _mono_split_two(prog, root, box, guards, budget, st, depth, max_depth, d,
                    log, df_cache, age):
    lo, hi = box[d]
    mid = (lo + hi) / 2
    r1 = _mono_certify(prog, root, box[:d] + [(lo, mid)] + box[d + 1:],
                       guards, budget, st, depth + 1, max_depth, log,
                       df_cache, age)
    if r1 == "CAP":
        return "CAP"
    r2 = _mono_certify(prog, root, box[:d] + [(mid, hi)] + box[d + 1:],
                       guards, budget, st, depth + 1, max_depth, log,
                       df_cache, age)
    if r1 == "POS" and r2 == "POS":
        return "POS"
    if "CAP" in (r1, r2):
        return "CAP"
    if "FAIL" in (r1, r2):
        return "FAIL"
    return "NEG"


def _mono_box_str(box):
    return [[str(lo), str(hi)] for lo, hi in box]


def _mono_fmt(f):
    import mpmath
    x = mpmath.mpf(f.numerator) / f.denominator
    return mpmath.nstr(x, 6, strip_zeros=True)


def mono_main(case, cid, mod, n, args, budget_n, max_depth, subbox_filter):
    """`--mono` driver: run the route-A reduction over the sub-box manifest
    and write the certificate-plan report (text) + .mono.json (machine)."""
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(200000)  # huge Fractions in certs
    try:
        import mpmath
        mpmath.mp.dps = 120  # covers the 2^-300 atan endpoint slack
    except ImportError:
        die("--mono needs mpmath (pip3 install mpmath)")
    mf = json.load(open(args[1]))
    if mf.get("schema") == "gsplit-subboxes":
        raw = [s["box"] for s in mf["subboxes"]]
    elif "subboxes" in mf:
        raw = mf["subboxes"]
    else:
        die(f"{args[1]}: no subboxes (expected gsplit-subboxes manifest or "
            "the raw W3 make_subboxes dump)")
    boxes = []
    for bx in raw:
        pairs = []
        for dim in bx:
            (m1, e1), (m2, e2) = dim
            pairs.append((Fraction(m1) * (Fraction(2) ** e1),
                          Fraction(m2) * (Fraction(2) ** e2)))
        boxes.append(pairs)
    if subbox_filter is not None:
        boxes = [(k, b) for k, b in enumerate(boxes) if k == subbox_filter]
    else:
        boxes = list(enumerate(boxes))
    prog = case["prog"]
    guards = gsplit_guards(case)
    root = _mono_parse2(prog)
    rows, totals = [], {"corners": 0, "sign_splits": 0, "guard_splits": 0,
                        "mono_restricts": 0, "fails": 0, "cap": 0,
                        "neg_points": 0, "tevals": 0}
    import time
    for k, bx in boxes:
        budget = [budget_n]
        st = {"corners": 0, "sign_splits": 0, "guard_splits": 0,
              "mono_restricts": 0, "fails": 0, "cap": 0, "neg_points": 0,
              "df_evals": 0, "certs": []}
        w = [hi - lo for lo, hi in bx]
        print(f"emit_lean: [mono] sub-box {k}/{len(boxes)} "
              f"w=[{', '.join(_mono_fmt(x) for x in w)}]", flush=True)
        t0 = time.time()
        try:
            status = _mono_certify(prog, root, bx, guards, budget, st, 0,
                                   max_depth,
                                   lambda m: print(f"emit_lean: [mono {k}]"
                                                   f" {m}", flush=True))
        except _MonoBudget:
            status = "CAP"
            st["cap"] += 1
            print(f"emit_lean: [mono {k}] budget exhausted", flush=True)
        rows.append({"sb": k, "status": status, "box": _mono_box_str(bx),
                     "counts": {kk: st[kk] for kk in
                                ("corners", "sign_splits", "guard_splits",
                                 "mono_restricts", "fails", "cap",
                                 "neg_points", "df_evals")},
                     "tevals": budget_n - budget[0],
                     "events": st["certs"]})
        for kk in ("corners", "sign_splits", "guard_splits", "mono_restricts",
                   "fails", "cap", "neg_points"):
            totals[kk] += st[kk]
        totals["tevals"] += budget_n - budget[0]
        print(f"emit_lean: [mono {k}] -> {status} "
              f"(corners={st['corners']} bisect={st['sign_splits']} "
              f"guards={st['guard_splits']} "
              f"tevals={budget_n - budget[0]}, {time.time() - t0:.0f}s)",
              flush=True)
    npos = sum(1 for r in rows if r["status"] == "POS")
    out_json = os.path.splitext(args[2])[0] + ".mono.json"
    manifest = {"schema": "mono-corner-certs", "case": cid,
                "source_manifest": args[1], "n": len(boxes),
                "budget": budget_n, "max_depth": max_depth,
                "totals": totals,
                "n_pos": npos,
                "subboxes": rows}
    open(out_json, "w").write(json.dumps(manifest, indent=1))
    with open(args[2], "w") as f:
        f.write(f"/- mono route-A prototype report for {cid}\n")
        f.write(f"    sub-boxes: {len(rows)} ({npos} POS, "
                f"{len(rows) - npos} not-POS)\n")
        f.write(f"    totals: {totals}\n")
        f.write("    kernel replay (W7): per-event checkPosTMHull on the\n")
        f.write("    recorded box; per-corner point-box TM = exact value;\n")
        f.write("    assembly via the mono-corner lemma (scout §5.3). -/\n")
        for r in rows:
            f.write(f"\n== sb{r['sb']}: {r['status']}"
                    f"  corners={r['counts']['corners']}"
                    f" sign_bisects={r['counts']['sign_splits']}"
                    f" guard_splits={r['counts']['guard_splits']}"
                    f" tevals={r['tevals']}\n")
            for ev in r["events"]:
                if ev["kind"] == "mono":
                    f.write(f"   d{ev['depth']} MONO {ev['signs']}\n")
                elif ev["kind"] == "enclosure":
                    f.write(f"   d{ev['depth']} CORNER lb=+{ev['loBound']}"
                            f" box={ev['box']}\n")
                else:
                    f.write(f"   d{ev['depth']} {ev['kind']}\n")
    print(f"emit_lean: wrote {args[2]} + {out_json} (mono route A: {npos}/{len(rows)} "
          f"sub-boxes POS, {totals['corners']} corner certs, "
          f"{totals['sign_splits']} sign bisects, {totals['guard_splits']} "
          f"guard splits, {totals['tevals']} mirror tevals)")


# ---------------------------------------------------------------------------
# W7: kernel-side replay emission for the mono route (Lean MonoCorner.lean).
# Appended after the W6a mono block; consumes the in-memory cert plan and
# emits <out>.monolean.lean.  Per sub-box with an ALL-MONO path (only
# restrict events, no bisections, no flat dims) it emits:
#   - dfⱼ sign certificates as `checkPosTMHull (IExpr.derivExpr F j) box
#     TMParams.empty = true` — the kernel computes the symbolic derivative
#     ITSELF (MonoCorner.derivExpr); the Python `_mono_diff` df is
#     search-side only and is never trusted by the kernel;
#   - the corner point-box certificate `checkPosTMHull F (pointBox corner)`;
#   - the assembly through `MonoCorner.checkMonoCorner` (chain rule +
#     monotone slices + corner telescope ⇒ ∀ρ∈box, 0 < F.evalReal ρ).
# Restricted to polynomials (no sqrt/div/atan/abs/ite in the prog): a
# df/derivative carrying sqrt/div/atan nodes needs re-baked stage-A
# mantissa certificates for the kernel replay (W8 scope), and abs/ite need
# the derivSafe/DomOK guard-discharge emission (W8 scope).
# ---------------------------------------------------------------------------

_MONOLEAN_MIN_DIMS = 1


def _mono_lean_scan(prog, acc):
    """collect the op names of a prog (recursive over ite dicts)."""
    for op in prog:
        if isinstance(op, dict):
            it = op["ite"]
            for sub in (it["cond"], it["then"], it["else"]):
                _mono_lean_scan(sub, acc)
        else:
            acc.add(op[0])


def _mono_lean_dyadic(fr):
    """Fraction -> '⟨m, e⟩' dyadic literal text; None if not dyadic."""
    fr = Fraction(fr)
    num, den = fr.numerator, fr.denominator
    e = 0
    while den % 2 == 0:
        den //= 2
        e -= 1
    if den != 1:
        return None
    while num != 0 and num % 2 == 0:
        num //= 2
        e += 1
    return f"⟨{num}, {e}⟩"


def _mono_lean_fin_lit(j, n):
    """0-based index j -> Fin n literal text."""
    return f"({j} : Fin {n})"


def mono_lean_main(case, cid, n, args, mono_json, pad_bits=None):
    """emit <out>.monolean.lean from the mono-corner-certs manifest that the
    --mono run just wrote (mono_json = parsed manifest)."""
    import re
    nsp = "MonoReplay_" + re.sub(r"\W", "_", cid)
    expr = RPN(sqrt_const_pad_bits=pad_bits).emit(case["prog"])
    ops = set()
    _mono_lean_scan(case["prog"], ops)
    hard = {"sqrt", "div", "atan", "abs", "ite"}
    bad = sorted(ops & hard)
    if bad:
        print(f"emit_lean: [mono-lean] prog carries {bad}: kernel replay of "
              f"dfⱼ needs W8 stage-A re-bake (sqrt/div/atan certs) and/or "
              f"derivSafe/DomOK guard discharge (abs/ite) — nothing emitted")
        return
    rows = [r for r in mono_json["subboxes"] if r["status"] == "POS"]
    emitted, skipped = 0, 0
    chunks = []
    for r in rows:
        events = [ev for ev in r["events"] if ev["kind"] == "mono"
                  or ev["kind"] == "enclosure"]
        if (len(events) < _MONOLEAN_MIN_DIMS + 1
                or events[-1]["kind"] != "enclosure"
                or any(ev["kind"] != "mono" for ev in events[:-1])):
            skipped += 1
            continue
        signs = []
        ok = True
        for ev in events[:-1]:
            for j, s in ev["signs"].items():
                if s not in ("incr", "decr"):
                    ok = False  # flat dims need a df≡0 certificate (W8)
                    break
                signs.append((int(j), s))
            if not ok:
                break
        if not ok or not signs:
            skipped += 1
            continue
        k = r["sb"]
        box = [[Fraction(v) for v in side] for side in r["box"]]
        corner = list(box)
        for j, s in signs:
            corner[j] = [box[j][0], box[j][0]] if s == "incr" \
                else [box[j][1], box[j][1]]
        enc = events[-1]["box"]
        if any(Fraction(enc[j][0]) != corner[j][0]
               or Fraction(enc[j][1]) != corner[j][1] for j in range(n)):
            skipped += 1  # enclosure fired on a non-corner box
            continue
        dy_box = [[_mono_lean_dyadic(v) for v in side] for side in box]
        dy_cor = [_mono_lean_dyadic(c[0]) for c in corner]
        if any(d is None for side in dy_box for d in side) \
                or any(d is None for d in dy_cor):
            skipped += 1  # non-dyadic box endpoints
            continue
        sgn_vec = ["true"] * n
        for j, s in signs:
            sgn_vec[j] = "false" if s == "decr" else "true"
        dims = [j for j, _ in signs]
        body = [f"namespace {nsp}_sb{k}", "",
                f"/-- mono route-A sub-box {k} (mirror depth {events[-1]['depth']}), "
                f"lb=+{events[-1]['loBound']} at the corner. -/",
                f"def sb{k}Box : Fin {n} → DInterval := "
                f"![" + ", ".join(f"⟨{lo}, {hi}⟩" for lo, hi in dy_box) + "]",
                f"def sb{k}Corner : Fin {n} → Kepler.Interval.Dyadic := "
                f"![" + ", ".join(dy_cor) + "]",
                f"def sb{k}F : IExpr {n} := {expr}",
                f"def sb{k}Sgn : Fin {n} → Bool := "
                f"![" + ", ".join(sgn_vec) + "]", "",
                f"theorem sb{k}_safe : sb{k}F.derivSafe = true := by decide",
                f"theorem sb{k}_dom : DomOK sb{k}Box sb{k}F :=",
                f"  domOK_of_domTrivial _ _ (by decide)"]
        for j in dims:
            body.append(
                f"theorem sb{k}_df{j} : checkPosTMHull "
                f"(IExpr.derivExpr sb{k}F {_mono_lean_fin_lit(j, n)}) "
                f"sb{k}Box TMParams.empty = true := by decide")
        body.append(
            f"theorem sb{k}_corner : checkPosTMHull sb{k}F "
            f"(pointBox sb{k}Corner) TMParams.empty = true := by decide")
        incr_body, decr_body = [], []
        for j in range(n):
            if j in dims:
                incr_body.append(f"· exact ⟨sb{k}_df{j}, rfl⟩")
                decr_body.append("· exact Bool.noConfusion hj")
            else:
                incr_body.append("· exact Bool.noConfusion hj")
                decr_body.append("· exact Bool.noConfusion hj")
        # dims without a recorded sign cannot appear in an all-mono chain
        # (every free dim was signed or restricted before the enclosure);
        # guard the emission anyway:
        missing = [j for j in range(n) if j not in dims]
        if missing:
            skipped += 1
            continue
        body.append(
            f"theorem sb{k}_incr : ∀ j, sb{k}Sgn j = true →")
        body.append(
            f"    checkPosTMHull (IExpr.derivExpr sb{k}F j) sb{k}Box "
            f"TMParams.empty = true ∧ sb{k}Corner j = (sb{k}Box j).lo := by")
        body.append("  intro j hj")
        body.append("  fin_cases j")
        body.extend(["  " + b for b in incr_body])
        body.append(
            f"theorem sb{k}_decr : ∀ j, sb{k}Sgn j = false →")
        body.append(
            f"    checkPosTMHull (IExpr.neg (IExpr.derivExpr sb{k}F j)) "
            f"sb{k}Box TMParams.empty = true ∧ sb{k}Corner j = "
            f"(sb{k}Box j).hi := by")
        body.append("  intro j hj")
        body.append("  fin_cases j")
        body.extend(["  " + b for b in decr_body])
        cmem = []
        for j in range(n):
            cmem.append(
                "· simp only [sb%dBox, sb%dCorner, DInterval.mem, "
                "Kepler.Interval.Dyadic.toReal_def]\n    norm_num" % (k, k))
        body.append(
            f"theorem sb{k}_cmem : ∀ i, (sb{k}Box i).mem (sb{k}Corner i)"
            f".toReal := by")
        body.append("  intro i")
        body.append("  fin_cases i")
        body.extend(["  " + b for b in cmem])
        body.append("")
        body.append(
            f"/-- End to end: dfⱼ sign + corner POS ⇒ the whole sub-box is "
            f"positive (kernel-checked chain rule + mono-corner assembly). -/")
        body.append(
            f"theorem sb{k}_end_to_end (ρ : Fin {n} → ℝ) "
            f"(hρ : boxMem sb{k}Box ρ) : 0 < sb{k}F.evalReal ρ :=")
        body.append(
            f"  checkMonoCorner sb{k}F sb{k}Box sb{k}Sgn sb{k}Corner")
        body.append(
            f"    (fun _ => TMParams.empty) TMParams.empty sb{k}_safe "
            f"sb{k}_dom sb{k}_incr sb{k}_decr sb{k}_corner sb{k}_cmem ρ hρ")
        body.append("")
        body.append(f"end {nsp}_sb{k}")
        body.append("")
        chunks.append("\n".join(body))
        emitted += 1
    if not chunks:
        print(f"emit_lean: [mono-lean] no all-mono sub-box qualified "
              f"({skipped} skipped) — nothing emitted")
        return
    outpath = os.path.splitext(args[2])[0] + ".monolean.lean"
    hdr = (f"/- W7 kernel replay for the mono route-A plan ({cid}).\n"
           f"    Generated by emit_lean.py --mono --mono-lean from the\n"
           f"    mono-corner-certs manifest ({len(mono_json['subboxes'])} "
           f"sub-boxes, {emitted} all-mono emitted, {skipped} skipped).\n"
           f"    dfⱼ is computed by the kernel itself (IExpr.derivExpr,\n"
           f"    Kepler.Interval.MonoCorner); the Python-side df is\n"
           f"    search-only.  Assembly: checkMonoCorner. -/\n"
           f"import Kepler.Interval.MonoCorner\n\n"
           f"open Kepler.Interval\n\n")
    open(outpath, "w").write(hdr + "\n".join(chunks))
    print(f"emit_lean: wrote {outpath} (mono-lean kernel replay: {emitted} "
          f"all-mono sub-boxes, {skipped} skipped)")


# ---------------------------------------------------------------------------
# W8: mixed restrict×bisect tree emission for real leaves (route A, phase 2).
#
#   emit_lean.py <case.json> <spec.json> <out.lean> --mono-tree
#                [--pad-sqrt-const=N]
#   emit_lean.py <case.json> <spec.json> <out.lean> --mono-tree \
#                --params=<stage-A output>
#
# <spec.json> (schema "mono-tree-spec") describes ONE closed subtree of the
# W6a search over a guard-resolved, abs-eliminated program e* (the "expr"
# field; guards decided and abs signed on the ROOT box — premises the
# certificate is stated for):
#
#   {"schema": "mono-tree-spec", "n": 7,
#    "expr": <RPN prog of e*>,
#    "pad_sqrt_const": 120,
#    "gran": -80, "rung_n": 2048, "rung_out": -64,
#    "root": [[m,e],[m,e],...],
#    "tree": {"kind": "leaf", "box": [[m,e],...], "id": "L1"}
#           | {"kind": "restrict", "box": [...], "sgn": ["+",null,"-",...],
#              "id": "R1", "sub": {...}}
#           | {"kind": "split", "box": [...], "dim": d, "id": "S1",
#              "l": {...}, "r": {...}}}
#
# Stage A emits a compiled driver that (a) computes the REAL sqrt mantissa
# slots of e* over the root box (`Tools.FillParams.evalFill` — kernel-native,
# nested sqrts bottom-up; valid on every subtree by monotone narrowing) and
# (b) probes every certificate the tree needs — `tmHullLeafProbe` on
# `IExpr.derivExpr E j` (restrict dims, on the node box) and on `E` (leaves).
# It also prints one `DOM <nid> <entries>` line per restrict node: the node's
# DomOK v2 witness table, computed compiled-side by `Kepler.Interval.MonoTree`'s
# single-pass `domTable` (entries `(lo_m,lo_e,hi_m,hi_e)` or `N` for `none`).
# Stage B bakes the reported mantissa triples + template granularities into
# `TMParams`, the DOM tables as `List (Option DInterval)` literals, states the
# tree over `Kepler.Interval.MonoTree` and closes with `monoTree_sound`.  The
# per-restrict `DomOK` discharge is `domOK_of_domByIntervalTable`: the baked
# table must equal the kernel-recomputed `(domTable box E).2` AND be accepted
# by the pure consumer `domByTable` — both one O(n) kernel `decide` (the old
# `domOK_of_domByInterval` decide re-evaluated a full subtree interval at
# every div/sqrt/ite node, O(n·depth), the sb12-heavy leaf's >67 min blowup).
# All decides are kernel checks of exactly the emitted data; wrong Python-side
# verdicts/tables can only fail a decide, never pass.
#
# W8 witness-position rung lowering (`--mono-dom-rung=N[,OUT]` uniform /
# `--mono-witness-rung=N[,OUT]` marked, both off by default = v2 identical):
# the per-restrict DomOK decide pays `transOn` at EVERY trans node of E
# (rung-2048 closed-atan kernel Taylor: ~40-80s/node, the sb12-heavy leaf's
# dominant cost).  `transOn_sound` holds at every N, so a lowered rung only
# WIDENS a node's enclosure — sound everywhere, tighter nowhere.  The flags
# mark which trans nodes carry the lowered rung:
#   - uniform: every trans node (the DomOK decide pays all of them);
#   - witness-position (`_monotree_trans_marks`): only the trans nodes whose
#     values feed the witness table rows (divisor/guard/radicand subtrees).
# Every consumer (domTable, probes, stage-B decides) re-derives everything
# from the SAME emitted E, so a wrong stage-A verdict/table at any rung mix
# still can only fail a decide, never pass.
# ---------------------------------------------------------------------------

def _monotree_nodes(node, acc, path="T"):
    acc.append((path, node))
    if node["kind"] == "restrict":
        _monotree_nodes(node["sub"], acc, path + "s")
    elif node["kind"] == "split":
        _monotree_nodes(node["l"], acc, path + "l")
        _monotree_nodes(node["r"], acc, path + "r")


def _monotree_dyadic_pair(me):
    m, e = int(me[0]), int(me[1])
    return f"\u27e8{m}, ({e})\u27e9"


def _monotree_box_lit(box):
    return ("![" + ", ".join(
        f"\u27e8{_monotree_dyadic_pair(lo)}, {_monotree_dyadic_pair(hi)}\u27e9"
        for lo, hi in box) + "]")


def _monotree_sgn_lit(sgn):
    return ("![" + ", ".join(
        {"+": "some true", "-": "some false", None: "none"}[sg]
        for sg in sgn) + "]")


def _monotree_collect_doms(node, acc):
    """The restrict nodes in RPN order: (id, box) pairs needing a DomOK
    v2 witness table (one stage-A `DOM` line each)."""
    if node["kind"] == "restrict":
        acc.append((node["id"], node["box"]))
        _monotree_collect_doms(node["sub"], acc)
    elif node["kind"] == "split":
        _monotree_collect_doms(node["l"], acc)
        _monotree_collect_doms(node["r"], acc)


def _monotree_dom_entry_lit(entry):
    """DOM entry -> `Option DInterval` literal text (`None` = `none`)."""
    if entry is None:
        return "none"
    lm, le, hm, he = entry
    return f"some \u27e8\u27e8{lm}, ({le})\u27e9, \u27e8{hm}, ({he})\u27e9\u27e9"


def _monotree_collect_probes(node, acc):
    if node["kind"] == "leaf":
        acc.append(("leaf", node["id"], None, node["box"]))
    elif node["kind"] == "restrict":
        for j, sg in enumerate(node["sgn"]):
            if sg in ("+", "-"):
                acc.append(("df", node["id"], j, node["box"]))
        _monotree_collect_probes(node["sub"], acc)
    elif node["kind"] == "split":
        _monotree_collect_probes(node["l"], acc)
        _monotree_collect_probes(node["r"], acc)


def _monotree_count_ops(expr_text):
    return (expr_text.count("(.sqrt "), expr_text.count("(.div "),
            expr_text.count("(.trans "))


def _monotree_trans_marks(prog):
    """W8 witness-position marking: the RPN-order indices of the trans
    nodes whose interval values feed a DomOK v2 witness row, the total
    trans count, and the set of trans indices sitting under a `sqrt`
    radicand (must be empty for a witness-rung emission).

    The witness table rows are exactly the `div` divisor / `sqrt`
    radicand / `ite` guard intervals (the `domEvals` spec, and `domTable`
    collects the same list), so a trans node is a *witness position* iff
    it lies in one of those subtrees — for those nodes the DomOK discharge
    only consumes the SIGN of the value (divisor off 0, radicand positive,
    guard polarity), never a tight margin, which is what a lowered rung
    still certifies (`transOn_sound` holds at every N).  On the
    guard-resolved, abs-eliminated programs e* the tree carries no ite and
    the search-side precondition forbids trans under sqrt radicands, so in
    practice the marks are the divisor-subtree trans nodes.

    Traversal mirrors `RPN.emit_pair` exactly (dict = cond/then/else in
    order, binary ops pop right-then-left), so the trans counter here
    matches the emitter's per-node callback order."""
    marks = set()
    bad = set()
    cnt = [0]

    def walk(p):
        # stack entries: the set of trans indices each value contains
        st = []
        for ins in p:
            if isinstance(ins, dict):
                it = ins["ite"]
                c = walk(it["cond"])
                t = walk(it["then"])
                e = walk(it["else"])
                marks.update(c)  # guard: polarity check only
                st.append(c | t | e)
                continue
            op = ins[0]
            if op in ("push_var", "push_const"):
                st.append(set())
            elif op in ("add", "sub", "mul"):
                b = st.pop()
                a = st.pop()
                st.append(a | b)
            elif op in ("neg", "abs"):
                st.append(st.pop())
            elif op == "div":
                b = st.pop()  # e2 = the divisor (witness row)
                a = st.pop()
                marks.update(b)
                st.append(a | b)
            elif op == "sqrt":
                a = st.pop()
                bad.update(a)
                st.append(a)
            elif op in TRANS_KIND:
                k = cnt[0]
                cnt[0] += 1
                a = st.pop()
                st.append(a | {k})
            else:
                die(f"unknown op {op}")
        if len(st) != 1:
            die("RPN stack imbalance in witness marking")
        return st[0]

    walk(prog)
    return marks, cnt[0], bad


def _monotree_const_trans(prog):
    """W8 gen-4: the RPN-order indices of trans nodes whose ENTIRE feeding
    subtree is var-free (constant subterms).  Their interval values are
    box-independent, so lowering their rung buys no adaptivity while the
    coarse Taylor at a lowered rung can push a constant divisor row
    (atan-fed constants like 20*(1-4*atan(1)/3...) carried in the guard-free
    top level) across zero — BIXPCGW_7274157868_a carries two such rows that
    straddle at rung 16 on EVERY box and vanish at the spec rung.  The
    `--mono-dom-rung-keepconst` policy lowers every trans EXCEPT these.
    Traversal mirrors `RPN.emit_pair` exactly (dict = cond/then/else in
    order, binary ops pop right-then-left)."""
    const = set()
    cnt = [0]

    def walk(p):
        st = []
        for ins in p:
            if isinstance(ins, dict):
                it = ins["ite"]
                c = walk(it["cond"])
                t = walk(it["then"])
                e = walk(it["else"])
                st.append((True, c[1] | t[1] | e[1]))
                continue
            op = ins[0]
            if op == "push_var":
                st.append((True, set()))
            elif op == "push_const":
                st.append((False, set()))
            elif op in ("add", "sub", "mul"):
                b = st.pop()
                a = st.pop()
                st.append((a[0] or b[0], a[1] | b[1]))
            elif op in ("neg", "abs"):
                st.append(st.pop())
            elif op == "div":
                b = st.pop()
                a = st.pop()
                st.append((a[0] or b[0], a[1] | b[1]))
            elif op == "sqrt":
                st.append(st.pop())
            elif op in TRANS_KIND:
                k = cnt[0]
                cnt[0] += 1
                a = st.pop()
                if not a[0]:
                    const.add(k)
                st.append((a[0], a[1] | {k}))
            else:
                die(f"unknown op {op}")
        if len(st) != 1:
            die("RPN stack imbalance in const-trans marking")
        return st[0]

    walk(prog)
    return const, cnt[0]


def em_RPN(pad_bits, slots=None, rung=(2048, -64), unclose=False,
           dom_rung=None, witness_marks=None):
    """The W8 mono-tree RPN policy: sqrt slots from `slots` when given
    (`slots(ms)(i)` returns the (s1, s2) TEXT of the i-th sqrt node in RPN
    order — real mantissas computed kernel-side by `slotsDeep`, so closed
    trans args KEEP the fast path, no `trans_unclose_sqrt`), dummy `(0, 0)`
    otherwise; trans rung (N, out) for closed and open args alike; W6b
    plan-A const padding behind `pad_bits`.

    `dom_rung` (W8 witness-position rung lowering, off by default): when
    set to (N, out), trans nodes at DomOK witness positions are emitted at
    that lowered rung instead of `rung` — the domain discharge only needs
    the sign of those values (coarse interval suffices), while `rung`
    keeps serving the tight-margin TM certificates.  `witness_marks` = the
    `_monotree_trans_marks` index set to lower; `None` (with `dom_rung`
    set) lowers EVERY trans node (uniform mode — the DomOK decide pays
    `transOn` at all of them).  Default `dom_rung=None` keeps the v2
    behavior byte-identical."""
    if slots is None:
        sq = lambda i: ("0", "0")
    else:
        sq = slots
    if dom_rung is None:
        trans_cb = lambda op, closed: (str(rung[0]), "(" + str(rung[1]) + ")")
    else:
        dn = str(dom_rung[0])
        dout = "(" + str(dom_rung[1]) + ")"
        dr = (str(rung[0]), "(" + str(rung[1]) + ")")
        cnt = [0]
        if witness_marks is None:
            def trans_cb(op, closed):
                cnt[0] += 1
                return (dn, dout)
        else:
            def trans_cb(op, closed):
                k = cnt[0]
                cnt[0] += 1
                if k in witness_marks:
                    return (dn, dout)
                return dr
    return RPN(sqrt_slot=sq,
               trans=trans_cb,
               trans_unclose_sqrt=unclose,
               sqrt_const_pad_bits=pad_bits)


def monotree_main(case, cid, n, args, spec, params_file,
                  dom_rung=None, witness_rung=None, keepconst_rung=None,
                  split_fix=False, decide_mode="kernel"):
    import re
    nsp = "MonoTree_" + re.sub(r"\W", "_", cid)
    pad_bits = spec.get("pad_sqrt_const")
    rung = (int(spec.get("rung_n", 2048)), int(spec.get("rung_out", -64)))
    # W8 gen-8 `--decide-mode`: "kernel" (default; byte-identical output) or
    # "native" (DEV SPEED ONLY: every emitted decision tactic becomes
    # `native_decide`, which introduces the Lean.ofReduceBool axiom — never
    # a gate artifact; the gate lane stays kernel + axiom whitelist).
    dt = "native_decide" if decide_mode == "native" else "decide"
    # W8 witness-position rung lowering (flag-gated; absent = v2 identical).
    # A `None` out component resolves to the spec's rung_out.
    marks = None
    dom_rung_eff = None
    if dom_rung is not None or witness_rung is not None \
            or keepconst_rung is not None:
        if sum(x is not None for x in
               (dom_rung, witness_rung, keepconst_rung)) > 1:
            die("--mono-dom-rung / --mono-witness-rung /"
                " --mono-dom-rung-keepconst are mutually exclusive")
        if witness_rung is not None:
            mset, _nt, bad = _monotree_trans_marks(spec["expr"])
            if bad:
                die(f"witness rung: {len(bad)} trans node(s) under a sqrt "
                    "radicand — slotsDeep bakes the mantissa certificates "
                    "trans-free, so the radicand interval (and hence the "
                    "certificates) would become rung-dependent")
            wr = witness_rung
            out = rung[1] if wr[1] is None else wr[1]
            dom_rung_eff = (wr[0], out)
            marks = mset
        else:
            if keepconst_rung is not None:
                kr = keepconst_rung
                out = rung[1] if kr[1] is None else kr[1]
                dom_rung_eff = (kr[0], out)
                const, nt_total = _monotree_const_trans(spec["expr"])
                # only const trans that feed a DomOK row (divisor/guard/
                # radicand subtree) must keep the spec rung — a lowered
                # rung can push an atan-fed constant ROW across zero;
                # const trans outside row subtrees feed no row and lower
                # like everything else.
                mset, _nt, bad = _monotree_trans_marks(spec["expr"])
                protect = mset & const
                marks = set(range(nt_total)) - protect
                if not marks:
                    marks = None  # all-constant: falls back to spec rung
            else:
                dr = dom_rung
                out = rung[1] if dr[1] is None else dr[1]
                dom_rung_eff = (dr[0], out)
    rpn = em_RPN(pad_bits, rung=rung,
                 dom_rung=dom_rung_eff, witness_marks=marks)
    expr0 = rpn.emit(spec["expr"])
    nsq0, ndiv0, ntrans0 = _monotree_count_ops(expr0)
    gran = int(spec.get("gran", -80))
    root = spec["root"]
    tree = spec["tree"]
    probes = []
    _monotree_collect_probes(tree, probes)
    doms = []
    _monotree_collect_doms(tree, doms)
    root_lit = _monotree_box_lit(root)
    g = f"({gran})"
    iv_rep = f"List.replicate 8000 \u27e8{gran}, {gran}, {gran}\u27e9"
    tv_rep = f"List.replicate 8000 \u27e8{gran}, {gran}\u27e9"
    # Default-off byte-identity: with no rung flags the prelude must end
    # exactly as the pre-W8 emitter wrote it ("...kernel checks. -/" on one
    # line); the witness-rung note (if any) is spliced before the closure.
    all_note = "  All decides are kernel checks. -/\n"
    wr_all_note = "  All decides are kernel checks.\n"
    if decide_mode == "native":
        dev = ("  All decides are native_decide checks (DEV MODE: uses\n"
               "  Lean.ofReduceBool; never a gate artifact).")
        all_note = dev + " -/\n"
        wr_all_note = dev + "\n"
    wr_note = ""
    if dom_rung_eff is not None:
        if marks is None:
            wr_note = ("    W8 witness-rung policy: lowered rung "
                       f"{dom_rung_eff} on EVERY trans node (uniform —\n"
                       "    the DomOK decide pays transOn at all of them;\n"
                       "    sign accuracy is all it consumes there).\n")
        elif keepconst_rung is not None:
            wr_note = ("    W8 gen-4 keepconst policy: lowered rung "
                       f"{dom_rung_eff} on every trans node EXCEPT\n"
                       "    constant-subtree trans INSIDE DomOK row "
                       "subtrees (var-free feeding\n    subtrees — their "
                       "values are box-independent, and a lowered rung can "
                       "push\n    an atan-fed constant divisor row across "
                       "zero, so those keep the spec\n    rung; the DomOK "
                       "discharge pays transOn at all the lowered "
                       "ones).\n")
        else:
            wr_note = ("    W8 witness-rung policy: lowered rung "
                       f"{dom_rung_eff} on the {len(marks)}/{ntrans0}\n"
                       "    witness-position trans nodes (the divisor/guard/"
                       "radicand subtrees\n    the witness table rows read); "
                       "sign accuracy is all the DomOK\n    discharge "
                       "consumes there, and transOn_sound holds at every\n"
                       "    rung.  Tight-margin TM nodes keep the spec "
                       "rung.\n")
        wr_note = (wr_all_note + wr_note + "-/\n")
    prelude = (
        "/- W8 mono-tree certificate: a closed restrict\u00d7bisect subtree "
        "of the\n    W6a search over " + cid + " (route A; assembly via "
        "Kepler.Interval.MonoTree).\n    Generated by emit_lean.py "
        "--mono-tree" +
        (" --params (stage-B bake)." if params_file else
         " (stage-A driver).") + "\n"
        "    e* = the leaf program with all ite guards resolved and all abs\n"
        "    nodes eliminated on the tree-root box (kernel-side the certifi-\n"
        "    cate is stated for e*; the guard/abs sign facts are search-side\n"
        "    premises re-verified by the mirror).  Plan-A padded consts;\n"
        "    real sqrt slots computed kernel-side by evalFill (stage A) and\n"
        "    baked as `sbMs`."
        + (wr_note if wr_note else all_note) +
        "import Kepler.Interval.CertTM\n"
        "import Kepler.Interval.MonoTree\n\n"
        "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
        "set_option exponentiation.threshold 4096\n\n"
        "open Kepler.Interval\n\n"
        "/-- Local default (structural only). -/\n"
        "instance : Inhabited DInterval := \u27e8\u27e8\u27e80, 0\u27e9, "
        "\u27e80, 0\u27e9\u27e9\u27e9\n\n"
        "instance : Inhabited (Int \u00d7 Int) := \u27e8(0, 0)\u27e9\n\n"
        f"instance : Inhabited (IExpr {n}) := \u27e8.const \u27e80, 0\u27e9"
        "\u27e9\n\n"
        "/-- e* with dummy sqrt slots. -/\n"
        f"def E0 : IExpr {n} :=\n  {expr0}\n\n"
        "/-- The tree-root box. -/\n"
        f"def B0 : Fin {n} \u2192 DInterval := {root_lit}\n")

    if params_file is None:
        boxes_lean = ",\n    ".join(
            f"({_monotree_box_lit(b)} : Fin {n} \u2192 DInterval)"
            for _, _, _, b in probes)
        tags_lean = ", ".join(
            (f'"df_{pid}_{j}"' if kind == "df" else f'"leaf_{pid}"')
            for kind, pid, j, _ in probes)
        open(args[2], "w").write(prelude +
            "/-- Template TMParams: dummy sqrt mantissas, recip granularity\n"
            f"    {gran}; lengths over-provision the visited node counts\n"
            f"    (E0 static counts: sqrt {nsq0}, div {ndiv0}, trans "
            f"{ntrans0};\n    the df's duplicate E0's const forest). -/\n"
            "def Ps : TMParams :=\n"
            f"  \u27e8List.replicate 40000 \u27e80, 0, 0, {g}, {g}\u27e9,\n"
            f"   {iv_rep},\n"
            f"   {tv_rep}\u27e9\n\n"
            "/-- Real sqrt slots of E0 over the root box (kernel-native\n"
            "slotsDeep: plain-interval walk, all sqrt nodes, no Taylor;\n"
            "valid on every subtree by monotone narrowing). -/\n"
            "def sbMs : List (Int \u00d7 Int) := (slotsDeep B0 E0).2.1\n"
            +            "/-- E0 with slots read from the computed list (RPN order). -/\n"
            f"def MkE (ms : List (Int \u00d7 Int)) : IExpr {n} :=\n  "
            + em_RPN(pad_bits, rung=rung, slots=lambda i:
                     (f"(ms[{i}]!).1", f"(ms[{i}]!).2"),
                     dom_rung=dom_rung_eff,
                     witness_marks=marks).emit(spec["expr"])
            + "\n\n"
            "/-- The certified expression: E0 with real slots baked. -/\n"
            f"def E : IExpr {n} := MkE sbMs\n\n"
            "/-- One probe per tree certificate: \u2202\u2c7cE on restrict "
            "boxes, E on\nleaf boxes. -/\n"
            f"def probeExprs : Array (IExpr {n}) := #[" +
            ", ".join((f"(IExpr.derivExpr E {j})" if kind == "df" else "E")
                      for kind, _, j, _ in probes) + "]\n\n"
            f"def probeBoxes : Array (Fin {n} \u2192 DInterval) := #["
            + boxes_lean + "]\n\n"
            f"def probeTags : Array String := #[{tags_lean}]\n\n"
            "/-- DomOK v2: one witness-table box per restrict node.  Stage A\n"
            "prints `domTable box E`'s list per box; stage B bakes it as a\n"
            "literal and the kernel re-derives it (mismatch = decide fail). -/\n"
            + ((f"def domBoxes : Array (Fin {n} \u2192 DInterval) := #["
                + ", ".join((f"({_monotree_box_lit(b)} : Fin {n} \u2192 DInterval)")
                            for _, b in doms) + "]\n\n"
                f"def domIds : Array String := #["
                + ", ".join(f'"{nid}"' for nid, _ in doms) + "]\n\n")
              if doms else "")
            + "def main : List String \u2192 IO UInt32 := fun _ => do\n"
            "  let stdout \u2190 IO.getStdout\n"
            "  IO.println \"START\"\n"
            "  stdout.flush\n"
            "  IO.println s!\"FILL nsqrt={sbMs.length}\"\n"
            "  stdout.flush\n"
            + (("  for i in [0:domBoxes.size] do\n"
                "    let tbl := (domTable domBoxes[i]! E).2\n"
                "    IO.println (s!\"DOM {domIds[i]!} \" ++\n"
                "      String.intercalate \",\" (tbl.map fun o =>\n"
                "        match o with\n"
                "        | some I => s!\"({I.lo.m},{I.lo.e},{I.hi.m},{I.hi.e})\"\n"
                "        | none => \"N\"))\n"
                "    stdout.flush\n")
              if doms else "")
            + "  IO.println (\"MS \" ++ String.intercalate \",\"\n"
            "    (sbMs.map fun p => s!\"({p.1},{p.2})\"))\n"
            "  for i in [0:probeExprs.size] do\n"
            "    match tmHullLeafProbe probeExprs[i]! probeBoxes[i]! Ps with\n"
            "    | some (p, m, e, l) =>\n"
            "        let v := if p then \"PASS\" else \"NEG\"\n"
            "        let trip := String.intercalate \" \"\n"
            "          (l.map fun t => s!\"{t.1} {t.2.1} {t.2.2}\")\n"
            "        IO.println s!\"PROBE {probeTags[i]!} {v} {m} {e} "
            "{trip}\"\n"
            "        stdout.flush\n"
            "    | none =>\n"
            "        IO.println s!\"PROBE {probeTags[i]!} FAIL\"\n"
            "        stdout.flush\n"
            "  return 0\n")
        pol = ""
        if dom_rung_eff is not None:
            if marks is None:
                pol = (f"; witness-rung POLICY: uniform {dom_rung_eff} on "
                       f"all {ntrans0} trans")
            elif keepconst_rung is not None:
                pol = (f"; keepconst POLICY: {dom_rung_eff} on "
                       f"{len(marks)}/{ntrans0} trans (constant-subtree "
                       "trans keep the spec rung)")
            else:
                pol = (f"; witness-rung POLICY: {dom_rung_eff} on "
                       f"{len(marks)}/{ntrans0} witness-position trans")
        print(f"emit_lean: wrote {args[2]} (W8 mono-tree stage A: "
              f"{len(probes)} probes + {len(doms)} DOM tables; E0 static "
              f"sqrt {nsq0}, div {ndiv0}, trans {ntrans0}{pol}; run "
              f"`lake env lean --run {args[2]} > params.txt`)")
        return

    # ---- stage B: parse the stage-A output ----
    ms, verdicts, doms = None, {}, {}
    for ln in open(params_file):
        ln = ln.strip()
        if ln.startswith("DOM"):
            tk = ln.split()
            if len(tk) < 2:
                die(f"malformed DOM line: {ln[:80]}")
            body = tk[2] if len(tk) > 2 else ""
            entries = []
            for tok in re.findall(r"\([^)]*\)|N", body):
                if tok == "N":
                    entries.append(None)
                    continue
                parts = tok[1:-1].split(",")
                if len(parts) != 4:
                    die(f"malformed DOM entry {tok!r} for {tk[1]}")
                entries.append(tuple(int(v) for v in parts))
            doms[tk[1]] = entries
        elif ln.startswith("MS"):
            body = ln[2:].strip()
            if body.startswith("(") and body.endswith(")"):
                body = body[1:-1]
            ms = [tuple(int(x) for x in tok.split(","))
                  for tok in body.split("),(") if tok]
        elif ln.startswith("PROBE"):
            tk = ln.split()
            if tk[2] == "FAIL":
                die(f"probe {tk[1]} FAILED (queue exhausted or domain fail) "
                    "— raise the template counts or adjust gran/rung")
            triples = [tuple(int(v) for v in tk[5:][j:j + 3])
                       for j in range(0, len(tk) - 5, 3)]
            verdicts[tk[1]] = (tk[2], int(tk[3]), int(tk[4]), triples)
    if ms is None:
        die("no MS line in params file")
    nsq = len(ms)

    if nsq != nsq0:
        die(f"stage-A reported {nsq} sqrt slots but E0 has {nsq0} sqrt "
            "nodes (guard-resolved programs must traverse every node)")
    slots_txt = [None] * nsq

    def _slot(i):
        return (str(ms[i][0]), str(ms[i][1]))
    expr_conc = em_RPN(pad_bits, rung=rung, slots=_slot,
                       dom_rung=dom_rung_eff,
                       witness_marks=marks).emit(spec["expr"])
    out = [prelude +
        "/-- The certified expression (real sqrt slots baked concretely;\n"
        f"    stage-A ms, {nsq} sqrt nodes, RPN order). -/\n"
        f"def E : IExpr {n} :=\n  {expr_conc}\n"]
    def ps_lit(triples):
        trip = ", ".join(f"\u27e8{a}, {b}, {c}, {g}, {g}\u27e9"
                         for a, b, c in triples)
        return (f"\u27e8[{trip}], {iv_rep}, {tv_rep}\u27e9")

    def emit_node(node, box_expr=None):
        kind = node["kind"]
        nid = node["id"]
        bl = box_expr or _monotree_box_lit(node["box"])
        if kind == "leaf":
            tag = f"leaf_{nid}"
            v = verdicts[tag]
            out.append(
                f"/-- Leaf {nid}: kernel TM-hull positivity on its box\n"
                f"    (stage-A margin {v[1]}*2^({v[2]}); {len(v[3])} visited\n"
                f"    sqrt certs baked). -/\n"
                f"def {nid}Box : Fin {n} \u2192 DInterval := {bl}\n\n"
                f"def {nid}Ps : TMParams := {ps_lit(v[3])}\n\n"
                f"theorem {nid}_cert : checkPosTMHull E {nid}Box {nid}Ps"
                f" = true := by {dt}\n")
            return f"(MonoTree.leaf {nid}Box {nid}Ps {nid}_cert)"
        if kind == "restrict":
            sgn = node["sgn"]
            out.append(f"/-- Restrict node {nid}, sgn {sgn} (+ = \u2191 to "
                       f"the lo face). -/\n"
                       f"def {nid}Box : Fin {n} \u2192 DInterval := {bl}\n\n"
                       f"def {nid}Sgn : Fin {n} \u2192 Option Bool := "
                       f"{_monotree_sgn_lit(sgn)}\n")
            sub_term = emit_node(node["sub"],
                                 f"restrictBox {nid}Box {nid}Sgn")
            incr, decr = [], []
            for j, sg in enumerate(sgn):
                if sg not in ("+", "-"):
                    continue
                tag = f"df_{nid}_{j}"
                v = verdicts[tag]
                side = "IExpr.derivExpr E" if sg == "+" else \
                    "(IExpr.neg (IExpr.derivExpr E))"
                out.append(
                    f"/-- \u2202\u2c7cE at {nid} (stage-A margin {v[1]}"
                    f"*2^({v[2]}); {len(v[3])} sqrt certs). -/\n"
                    f"theorem {nid}_df{j} : checkPosTMHull ({side} {j}) "
                    f"{nid}Box {ps_lit(v[3])} = true := by {dt}\n")
                (incr if sg == "+" else decr).append(j)
            psd_parts = []
            for j in range(n):
                if j in incr or j in decr:
                    psd_parts.append(ps_lit(verdicts[f"df_{nid}_{j}"][3]))
                else:
                    psd_parts.append("TMParams.empty")
            out.append(f"def {nid}Psd : Fin {n} \u2192 TMParams := !["
                       + ", ".join(psd_parts) + "]\n")
            incr_body, decr_body = [], []
            for j in range(n):
                if j in incr:
                    incr_body.append(f"\u00b7 exact {nid}_df{j}")
                    decr_body.append(f"\u00b7 simp [{nid}Sgn] at hj")
                elif j in decr:
                    incr_body.append(f"\u00b7 simp [{nid}Sgn] at hj")
                    decr_body.append(f"\u00b7 exact {nid}_df{j}")
                else:
                    incr_body.append(f"\u00b7 simp [{nid}Sgn] at hj")
                    decr_body.append(f"\u00b7 simp [{nid}Sgn] at hj")
            out.append(
                f"theorem {nid}_incr : \u2200 j, {nid}Sgn j = some true "
                f"\u2192\n    checkPosTMHull (IExpr.derivExpr E j) {nid}Box "
                f"({nid}Psd j) = true := by\n"
                f"  intro j hj\n  fin_cases j\n"
                + "\n".join("  " + b for b in incr_body) + "\n\n"
                f"theorem {nid}_decr : \u2200 j, {nid}Sgn j = some false "
                f"\u2192\n    checkPosTMHull (IExpr.neg (IExpr.derivExpr E"
                f" j)) {nid}Box ({nid}Psd j) = true := by\n"
                f"  intro j hj\n  fin_cases j\n"
                + "\n".join("  " + b for b in decr_body) + "\n\n"
                f"theorem {nid}_hwf : \u2200 j, {nid}Sgn j \u2260 none "
                f"\u2192 ({nid}Box j).wf = true := by\n"
                f"  intro j hj\n  fin_cases j <;> {dt}\n\n"
                f"theorem {nid}_safe : E.derivSafe = true := by {dt}\n\n")
            # DomOK v2 (witness-table batch discharge): stage A computed the
            # table compiled-side by `domTable`; stage B bakes it as a literal
            # and the two kernel decides re-derive + consume it (O(n) each).
            if nid not in doms:
                die(f"no DOM line for restrict node {nid} — stale stage-A "
                    "params (pre-DOM run); rerun emit_lean --mono-tree "
                    "stage A")
            entries = ", ".join(_monotree_dom_entry_lit(e) for e in doms[nid])
            out.append(
                f"/-- DomOK v2 witness table for restrict node {nid}: the\n"
                f"    stage-A `domTable {nid}Box E` list ({len(doms[nid])}\n"
                "    entries).  Honesty: the kernel re-derives the table from\n"
                f"    `{nid}Box E` (`hT` decide) and the pure consumer accepts\n"
                "    it (`hok` decide) — a baked-table bug can only fail a\n"
                "    decide, never pass. -/\n"
                f"def {nid}DomTable : List (Option DInterval) := [{entries}]\n\n"
                f"theorem {nid}_dom : DomOK {nid}Box E :=\n"
                f"  domOK_of_domByIntervalTable {nid}Box E {nid}DomTable\n"
                f"    (by {dt}) (by {dt})\n")
            return (f"(MonoTree.restrict {nid}Box {nid}Sgn {nid}Psd {nid}_hwf"
                    f" {nid}_incr {nid}_decr {nid}_safe {nid}_dom {sub_term})")
        if kind == "split":
            lterm = emit_node(node["l"])
            rterm = emit_node(node["r"])
            d = int(node["dim"])
            lid, rid = node["l"]["id"], node["r"]["id"]
            out.append(
                f"/-- Split node {nid} along dim {d} (exact dyadic midpoint)."
                f" -/\n"
                f"def {nid}Box : Fin {n} \u2192 DInterval := {bl}\n\n"
                f"theorem {nid}_splitOK : splitOK {nid}Box {d} {lid}Box "
                f"{rid}Box := by\n"
                f"  refine \u27e8?_, ?_, ?_, ?_, ?_\u27e9\n"
                f"  \u00b7 intro i hi\n    fin_cases i\n"
                + "".join("    \u00b7 exact absurd rfl hi\n" if j == d else
                          "    \u00b7 exact \u27e8rfl, rfl\u27e9\n"
                          for j in range(n))
                + f"  \u00b7 {dt}\n  \u00b7 {dt}\n  \u00b7 {dt}\n"
                f"  \u00b7 {dt}\n")
            if split_fix:
                return (f"(MonoTree.split {nid}Box {d} {lterm} {rterm})")
            return (f"(MonoTree.split {nid}Box {d} {lterm} {rterm} "
                    f"{nid}_splitOK)")
        die(f"unknown tree node kind {kind}")

    def covers_term(node):
        if node["kind"] == "leaf":
            return "trivial"
        if node["kind"] == "restrict":
            return f"\u27e8{covers_term(node['sub'])}, rfl\u27e9"
        if split_fix:
            # covers of a split = splitOK ∧ l.covers ∧ r.covers (right-nested
            # And): three flat fields.  The v2 wrapper `⟨ct, rfl⟩` around each
            # child assumes the child's covers is an And with an equality
            # second field (restrict shape); a leaf child's covers is `True`
            # and a split child's is a plain And — both break under the
            # wrapper ("Constructor True.intro does not have explicit
            # fields").  Flat fields are correct for every child kind.
            return (f"\u27e8{node['id']}_splitOK, "
                    f"{covers_term(node['l'])}, "
                    f"{covers_term(node['r'])}\u27e9")
        return (f"\u27e8{node['id']}_splitOK, "
                f"\u27e8{covers_term(node['l'])}, rfl\u27e9, "
                f"\u27e8{covers_term(node['r'])}, rfl\u27e9\u27e9")
    tree_term = emit_node(tree)
    nleaf = sum(1 for k, _, _, _ in probes if k == "leaf")
    ndf = sum(1 for k, _, _, _ in probes if k == "df")
    out.append(
        "/-- The certificate tree. -/\n"
        f"def sbTree : MonoTree {n} E := {tree_term}\n\n"
        "/-- The covering structure (kernel-checked structural equalities)."
        "\n-/\n"
        "theorem sbTree_covers : sbTree.covers := by\n"
        "  unfold sbTree\n"
        f"  exact {covers_term(tree)}\n\n"
        "/-- End to end: every real point of the root box sees a strictly\n"
        "positive value (the W8 assembly). -/\n"
        f"theorem sb_end_to_end (\u03c1 : Fin {n} \u2192 \u211d)\n"
        f"    (h\u03c1 : boxMem B0 \u03c1) : 0 < E.evalReal \u03c1 :=\n"
        "  monoTree_sound sbTree sbTree_covers \u03c1 h\u03c1\n\n"
        "/-- Plain interval arithmetic fails on the root box (the reason the\n"
        "tree is needed). -/\n"
        "theorem B0_interval_neg : checkPos E B0 = false := by " + dt + "\n")
    if split_fix:
        # The v2 diagnostic `B0_interval_neg` presumes plain interval FAILS on
        # the root; on merged (split-root) boxes it may as well SUCCEED (the
        # decide then refutes the stated `= false`, killing the file).  It is
        # diagnostic, not load-bearing (monoTree_sound never consumes it) —
        # omit it under the fix flag.
        out[-1] = out[-1].replace(
            "/-- Plain interval arithmetic fails on the root box (the reason"
            " the\ntree is needed). -/\n"
            "theorem B0_interval_neg : checkPos E B0 = false := by " + dt + "\n",
            "")
    open(args[2], "w").write("\n".join(out))
    pol = ""
    if dom_rung_eff is not None:
        if marks is None:
            pol = (f"; witness rung {dom_rung_eff} uniform on {ntrans0} "
                   "trans")
        elif keepconst_rung is not None:
            pol = (f"; keepconst rung {dom_rung_eff} on {len(marks)}/"
                   f"{ntrans0} trans (constant-subtree trans keep the "
                   "spec rung)")
        else:
            pol = (f"; witness rung {dom_rung_eff} on {len(marks)}/"
                   f"{ntrans0} witness-position trans")
    print(f"emit_lean: wrote {args[2]} (W8 mono-tree stage B: {nleaf} leaf "
          f"certs + {ndf} df certs; {nsq} sqrt slots baked{pol})")


# W8 gen-7 rung curve (BIXPCGW_7274157868_a sb12-heavy, POS1 and L1 boxes
# agree row-for-row): of the 99 DOM witness rows, 97 are admissible at
# rung 8; rows 3 and 52 (both `div`) need rung 64; none need >64 and the
# nesting is monotone with zero counterexamples.  The stable recipe for the
# witness line is therefore `--mono-tree --mono-witness-rung=64` (8/53
# witness-position trans lowered, the 45 tight-margin trans keep the spec
# 2048 rung).  The leaf final-value line (checkPosTMHull) is separate: it
# still needs the constant bits at 2048 (keepconst policy).  This constant
# is documentation for drivers; the flag is the policy.
W8_WITNESS_RUNG_SB12HEAVY = 64


def _parse_rung_arg(s, flag):
    """`N` or `N,OUT` -> (N, OUT-or-None); None out resolves to the spec's
    rung_out inside monotree_main."""
    parts = s.split(",")
    if len(parts) == 1:
        return (int(parts[0]), None)
    if len(parts) == 2:
        return (int(parts[0]), int(parts[1]))
    die(f"{flag}: bad rung {s!r} (expected N or N,OUT)")


def main():
    shard_leaves = 128
    sample_n = None
    fill = False
    stage_a = False
    stage_a_shards = 1
    stage_a_data = False
    bbg = False
    disj_gd = False
    disj_dummy = False
    hull = False
    gsplit = None
    gsplit_depth = 12
    gran = -80
    rung_n = 128
    rung_out = -80
    max_leaves = None
    params_file = None
    manifest_file = None
    mono = False
    mono_budget = 20000
    mono_max_depth = 48
    mono_subbox = None
    monolean = False
    monotree = False
    pad_sqrt_const = None
    dom_rung = None
    witness_rung = None
    keepconst_rung = None
    # W8 gen-7: fixed split-node skeleton (the constructor takes box/d/l/r;
    # the splitOK proof is consumed by `covers`, not by the constructor).
    # OFF by default = byte-identical emission (the v2 5-arg skeleton is kept
    # for provenance; it never elaborates -- the split path was never exercised
    # before gen-7).
    split_fix = False
    # W8 gen-8: kernel (default, byte-identical) or native (DEV ONLY:
    # native_decide, introduces Lean.ofReduceBool; never a gate artifact).
    decide_mode = "kernel"
    args = []
    for a in sys.argv[1:]:
        if a.startswith("--shard-leaves="):
            shard_leaves = int(a.split("=", 1)[1])
        elif a.startswith("--stage-a-shards="):
            stage_a_shards = int(a.split("=", 1)[1])
        elif a.startswith("--leaves="):
            sample_n = int(a.split("=", 1)[1])
        elif a == "--mono":
            mono = True
        elif a == "--mono-lean":
            monolean = True
        elif a == "--mono-tree":
            monotree = True
        elif a.startswith("--mono-budget="):
            mono_budget = int(a.split("=", 1)[1])
        elif a.startswith("--mono-max-depth="):
            mono_max_depth = int(a.split("=", 1)[1])
        elif a.startswith("--mono-subbox="):
            mono_subbox = int(a.split("=", 1)[1])
        elif a.startswith("--pad-sqrt-const="):
            pad_sqrt_const = int(a.split("=", 1)[1])
        elif a.startswith("--mono-dom-rung="):
            dom_rung = _parse_rung_arg(a.split("=", 1)[1], "--mono-dom-rung")
        elif a.startswith("--mono-witness-rung="):
            witness_rung = _parse_rung_arg(a.split("=", 1)[1],
                                           "--mono-witness-rung")
        elif a.startswith("--mono-dom-rung-keepconst="):
            keepconst_rung = _parse_rung_arg(a.split("=", 1)[1],
                                             "--mono-dom-rung-keepconst")
        elif a == "--mono-split-fix":
            split_fix = True
        elif a.startswith("--decide-mode="):
            decide_mode = a.split("=", 1)[1]
            if decide_mode not in ("kernel", "native"):
                die("--decide-mode: expected `kernel` or `native`")
        elif a == "--fill":
            fill = True
        elif a == "--stage-a":
            stage_a = True
        elif a == "--stage-a-data":
            stage_a_data = True
        elif a == "--bbg":
            bbg = True
        elif a == "--disj-gd":
            disj_gd = True
        elif a == "--disj-dummy":
            disj_dummy = True
        elif a == "--hull":
            hull = True
        elif a == "--gsplit=a":
            hull = True
            gsplit = "a"
        elif a == "--gsplit=b":
            hull = True
            gsplit = "b"
        elif a.startswith("--gsplit-depth="):
            gsplit_depth = int(a.split("=", 1)[1])
        elif a.startswith("--gran="):
            gran = int(a.split("=", 1)[1])
        elif a.startswith("--rung="):
            rung_n = int(a.split("=", 1)[1])
        elif a.startswith("--rung-out="):
            rung_out = int(a.split("=", 1)[1])
        elif a.startswith("--max-leaves="):
            max_leaves = int(a.split("=", 1)[1])
        elif a.startswith("--params="):
            params_file = a.split("=", 1)[1]
        elif a.startswith("--manifest="):
            manifest_file = a.split("=", 1)[1]
        elif not a.startswith("--"):
            args.append(a)
    if len(args) != 3:
        die("usage: emit_lean.py <case.json> <cert.json> <out.lean> [--shard-leaves=N]\n"
            "                [--leaves=N] [--fill] [--stage-a] [--bbg --params=FILE]\n"
            "                [--bbg --disj-gd --params=FILE [--manifest=FILE]] [--disj-dummy]\n"
            "                [--hull --params=FILE --gran=G --rung=N --rung-out=O]\n"
            "                [--hull --gsplit=a --params=ROUND1 [--manifest=ROUND1MF]\n"
            "                      [--gsplit-depth=12]]\n"
            "                [--hull --gsplit=b --params=ROUND2 [--manifest=MF] [--max-leaves=N]]\n"
            "                [--mono --mono-budget=N --mono-max-depth=N [--mono-subbox=K]]\n"
            "                [--mono-lean] (with --mono: also emit the W7 kernel\n"
            "                replay <out>.monolean.lean from the cert plan)\n"
            "                [--pad-sqrt-const=N] (W6b plan A: scale sqrt-fed\n"
            "                const mantissas to >= 2^N in mono-lean replays)\n"
            "                [--mono-tree --mono-dom-rung=N[,OUT]] (W8: emit\n"
            "                EVERY trans node at the lowered rung — the DomOK\n"
            "                decide pays transOn at all of them; OUT defaults\n"
            "                to the spec rung_out)\n"
            "                [--mono-tree --mono-witness-rung=N[,OUT]] (W8:\n"
            "                lower the rung only at DomOK witness-position\n"
            "                trans nodes — divisor/guard/radicand subtrees the\n"
            "                witness table reads; tight-margin nodes keep the\n"
            "                spec rung; the two flags are exclusive)\n"
            "                [--decide-mode=kernel|native] (gen-8: default\n"
            "                kernel = byte-identical; native = DEV ONLY,\n"
            "                emits native_decide and uses Lean.ofReduceBool)\n"
            "                (mono: <arg2> = sub-box manifest, <out> = report)")
    if disj_gd and not bbg:
        die("--disj-gd is a stage-B mode: pass --bbg --disj-gd --params=FILE")
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

    if monotree:
        # ---- W8: mixed restrict×bisect tree for a real leaf (two-stage:
        # stage A = compiled slot/probe driver, stage B = kernel bake) ----
        spec = json.load(open(args[1]))
        nsp_n = int(spec.get("n", n))
        monotree_main(case, cid, nsp_n, args, spec, params_file,
                      dom_rung=dom_rung, witness_rung=witness_rung,
                      keepconst_rung=keepconst_rung, split_fix=split_fix,
                      decide_mode=decide_mode)
        return

    if mono:
        # ---- W6 route-A prototype: mono dimension reduction over the
        # sub-boxes (Python-side TM mirror search; emits a certificate
        # plan report + .mono.json manifest, kernel replay is W7) ----
        mono_main(case, cid, mod, n, args, mono_budget, mono_max_depth,
                  mono_subbox)
        if monolean:
            # ---- W7: kernel replay emission (consumes the .mono.json the
            # run just wrote; zero effect without --mono-lean) ----
            out_json = os.path.splitext(args[2])[0] + ".mono.json"
            mono_lean_main(case, cid, n, args, json.load(open(out_json)),
                           pad_bits=pad_sqrt_const)
        return

    if hull:
        # ---- M2b/schema-v3 hull pilot (stage A driver / stage B kernel
        # certificate, route `checkPosTMHull` = evalTMHullD; see the
        # M2b/schema-v3 section of CertTM.lean) ----
        if gsplit:
            gsplit_main(case, cid, mod, n, args, params_file, manifest_file,
                        gran, rung_n, rung_out, gsplit_depth, gsplit == "b",
                        max_leaves)
            return
        hull_main(case, cid, mod, n, args, params_file, gran, rung_n,
                  rung_out, sample_n or 20, max_leaves, manifest_file)
        return

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
        disj = bool(case.get("disj"))
        if disj and not stage_a and not disj_gd:
            die("fill pipeline: disj stage B needs --bbg --disj-gd (wave-2 W3); "
                "--stage-a emits the schema-v2 disj driver")
        if disj_gd and not disj:
            die("--disj-gd on a non-disj case: use plain --bbg (BBTreeG)")
        hits = {l["hit"] for l in leaves}
        if not disj and hits != {"main"}:
            die(f"fill pipeline needs main-only hits, got {hits}")
        t = reconstruct(rootfrac, leafmap)
        box = box_lit(rootfrac)
        k = count_op(case["prog"], "sqrt")
        # var-free (leaf-constant) trans arguments get a fixed Taylor order:
        # the alternating arctan series at a boundary point (atan 1)
        # converges only like 1/(2N+1), so the rung ladder's N (tuned for
        # interior args, where big mantissas make high N expensive) can
        # never reach the needed precision.  N=2048: 5490182221's tight-margin
        # region (chunks 85-88, leaf true margins down to ~3e-4) fails at
        # N=128 (remainder ~1/257 ≈ 0.0039 eats the margin) and marginally
        # at N=1024; N=2048 (remainder ~2.4e-4) passes all 3762 leaves of
        # chunk00085.  Kernel cost scales ~linearly in N.
        closed_params = ("2048", "(-64)")
        if stage_a and disj:
            # Disjunctive stage A (schema v2): one fillMkExprK per pos goal,
            # exact-box varLt goals; hit recomputed per leaf (design D2).
            # Boxes are fed in the *tree node* form (the form the kernel
            # will check), not the normalised cert form — the `.sqrt`
            # mantissa certificate is form-sensitive (see tree_box_map).
            mkexprs, terms, goals_manifest = fill_goals(case)
            nslots = sum(g["sqrt"] for g in goals_manifest if g["kind"] == "pos")
            tbm = tree_box_map(t)
            if stage_a_data:
                # Data-file mode: tiny shared driver + plain-text box chunks.
                sz = (len(leaves) + stage_a_shards - 1) // stage_a_shards
                d = os.path.splitext(args[2])[0] + ".d"
                os.makedirs(d, exist_ok=True)
                open(os.path.join(d, "driver.lean"), "w").write(
                    stage_a_driver_disj(n, mkexprs, terms).format(**hdr))
                nw = 0
                for i in range(0, len(leaves), sz):
                    p = os.path.join(d, f"chunk{i // sz:05d}.txt")
                    with open(p, "w") as f:
                        for l in leaves[i:i + sz]:
                            b = tbm[tuple(box_frac(iv) for iv in l["box"])]
                            f.write(" ".join(
                                f"{lo[0]} {lo[1]} {hi[0]} {hi[1]}"
                                for lo, hi in b) + "\n")
                    nw += 1
                write_manifest(os.path.join(d, "manifest.json"), cid, n,
                               goals_manifest, len(leaves), "data", sz)
                print(f"emit_lean: wrote data-mode disj stage-A to {d}/ "
                      f"(driver.lean + {nw} chunk txts, {len(leaves)} leaves, "
                      f"chunk size {sz}, {len(mkexprs)} pos goals, "
                      f"{nslots} sqrt slots total)")
                return
            boxes_lean = [box_lit(tbm[tuple(box_frac(iv) for iv in l["box"])])
                          for l in leaves]
            if stage_a_shards > 1:
                sz = (len(leaves) + stage_a_shards - 1) // stage_a_shards
                d = os.path.splitext(args[2])[0] + ".d"
                os.makedirs(d, exist_ok=True)
                nw = 0
                for i in range(0, len(leaves), sz):
                    chunk = boxes_lean[i:i + sz]
                    out = stage_a_file_disj(mod, n, mkexprs, terms, chunk,
                                            len(chunk), leaf0=i)
                    p = os.path.join(d, f"chunk{i // sz:05d}.lean")
                    open(p, "w").write(out.format(**hdr))
                    nw += 1
                write_manifest(os.path.join(d, "manifest.json"), cid, n,
                               goals_manifest, len(leaves), "lean-shards", sz)
                print(f"emit_lean: wrote {nw} disj stage-A shards to {d}/ "
                      f"({len(leaves)} leaves, chunk size {sz}, "
                      f"{len(mkexprs)} pos goals, {nslots} sqrt slots total)")
                return
            out = stage_a_file_disj(mod, n, mkexprs, terms, boxes_lean,
                                    len(leaves))
            open(args[2], "w").write(out.format(**hdr))
            write_manifest(os.path.splitext(args[2])[0] + ".manifest.json",
                           cid, n, goals_manifest, len(leaves), "lean")
            print(f"emit_lean: wrote {args[2]} (disj stage A: {len(leaves)} "
                  f"leaves, {len(mkexprs)} pos goals, {nslots} sqrt slots total)")
            return
        if disj_gd:
            # ---- Wave-2 stage B (design D5): BBTreeGD shards from the
            # schema-v2 manifest + params (hit recomputed by stage A). ----
            if params_file is None:
                die("--bbg --disj-gd needs --params=FILE (schema-v2 FillParams "
                    "stage-A output)")
            goals = case_goals(case)
            mfpath = find_manifest(manifest_file, params_file)
            mf = check_manifest(json.load(open(mfpath)), goals, n, len(leaves))
            rung, hits = parse_params_disj(params_file, len(leaves), goals)
            if list(rung) not in mf["ladder"]:
                die(f"params rung {rung} not on the manifest ladder "
                    f"({mfpath}) — mismatched inputs?")
            exprs = {g["index"]: mkexpr_bbgd(g["prog"], g["sqrt"], rung)
                     for g in goals if g["kind"] == "pos"}
            hits_by_box = {}
            for i, l in enumerate(leaves):
                hits_by_box[tuple(box_frac(iv) for iv in l["box"])] = hits[i]
            emit_sharded_bbgd(t, mod, n, goals, exprs, box, hdr, args[2],
                              shard_leaves, hits_by_box)
            return
        if stage_a:
            rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
                      trans=lambda op, closed: closed_params if closed else ("N", "out"))
            expr = rpn.emit(case["prog"])
            goals_manifest = [{"index": 0, "label": "main", "kind": "pos",
                               "sqrt": k}]
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
                write_manifest(os.path.join(d, "manifest.json"), cid, n,
                               goals_manifest, len(leaves), "data", sz)
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
                write_manifest(os.path.join(d, "manifest.json"), cid, n,
                               goals_manifest, len(leaves), "lean-shards", sz)
                print(f"emit_lean: wrote {nw} stage-A shards to {d}/ "
                      f"({len(leaves)} leaves, chunk size {sz}, {k} sqrt slots)")
                return
            out = stage_a_file(mod, n, expr, boxes_lean, len(leaves))
            open(args[2], "w").write(out.format(**hdr))
            write_manifest(os.path.splitext(args[2])[0] + ".manifest.json",
                           cid, n, goals_manifest, len(leaves), "lean")
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
    if disj_dummy:
        if not case.get("disj"):
            die("--disj-dummy is only meaningful on disj cases")
        # v1 repair path (wave-2 design D6): un-hit branches may carry
        # sqrt/trans nodes; emit them with dummy parameters (legal
        # expressions, never kernel-checked).  Hit branches are verified
        # parameter-free below.
        rpn = RPN(sqrt_slot=lambda i: ("0", "0"),
                  trans=lambda op, closed: ("2048", "(-64)"))
    else:
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
        if disj_dummy:
            # A hit pos branch with sqrt/trans nodes would be kernel-checked
            # against dummy `(0, 0)` slots — route those to --bbg --disj-gd.
            progs = {"main": case["prog"]}
            for idx, dj in enumerate(case["disj"]):
                if "prog" in dj:
                    progs[f"disj:{idx}"] = dj["prog"]
            for h in hits:
                prog = progs.get(h)
                if prog is None:
                    continue  # var_lt hit: exact box check, no expression
                npar = (count_op(prog, "sqrt")
                        + sum(count_op(prog, t0) for t0 in TRANS_KIND))
                if npar:
                    die(f"hit branch {h} has {npar} parameterised node(s) "
                        f"(sqrt/trans): use --bbg --disj-gd, not --disj-dummy")
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
