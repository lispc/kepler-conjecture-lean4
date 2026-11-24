/-
Kepler.NliKit.BoxTree — unified binary subdivision tree (P-A package, SPEC-v2).

Implements `strategy/nli-next-phase-20261123b.md` §4.2 P-A, per the frozen
spec `lane_snapshots/nlikit-boxtree-spec-w2/SPEC-v2.md` (2026-11-24):

* `DC`            — normalised dyadic interval ⟨k, lo, hi⟩, shared scale `k ≥ 0`
  (invariant maintained by emitters; the kernel only ever sees literal DCs).
  `DC.value = lo · 2^-k`, written as `lo / 2^k.toNat` so `norm_num` reduces
  every comparison against decimal literals to exact rational arithmetic.
  NOTE (DIFFERS registration): the full dyadic arithmetic kernel (`dnorm`,
  four operations, common-scale compares — v6 `Wt1LeafKit` productisation)
  is a SEPARATE future module `DC.lean` (CONSUMERS §3 step 1); this file
  fixes only the type + `value` projection the tree layer needs.
* `LeafRow n Aux` — uniform leaf row: dyadic box endpoints per axis + a
  debt-private `aux` slot (Aux-polymorphic; every debt instantiates its own).
  Leaf tables are emitted as explicit `match` functions over `Fin m` (the
  island's prebuilt Mathlib lacks `Data.Matrix.Notation`, so `![...]` array
  literals are unavailable; `match (j : ℕ) with | 0 => row0 | …` is
  kernel-`decide`-reducible all the same).
* `rowBox`        — leaf box semantics, closed box on both sides (w1 T-5).
* `Cover`         — shape-free binary subdivision tree: dimension `n`, leaf
  count `m`, `Aux`, target predicate `P` all parameters (P-A hard req ②).
  `node` split point `c : DC` is the EXACT shared endpoint of the two child
  boxes (closed boxes overlap on the cut face; harmless, w1 T-5).
* `cover_sound`   — the glue theorem: leaves all passing ⇒ the whole box
  satisfies `P`.  `hsound` is kept explicitly open, so leaf witnesses are
  source-agnostic (kernel-decide leaves, symbolic cell theorems, vac/absurd
  leaves all plug in); this is what makes the axiom-profile regression
  (wt2A 61 cells + sqrt8 26 cells replayed through this machinery, same
  axiom profile as the closed originals) possible.

Zero `axiom` / `sorry` / `admit` / `native_decide`.  Domain conditions (e.g.
wt2A's `hd : 0 ≤ deltaX …`) are NOT tree nodes: they are folded into `P`
(w1 T-4, `P = fun x => D x → target x`).

Lane `nlikit-boxtree-impl-w1`, 2026-11-24.  Emitter determinism discipline
(PR-54: `PYTHONHASHSEED=0`, content-derived EQNAMEs, cross-run byte diff)
applies to every generator consuming this module.
-/
import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace Kepler.NliKit.BoxTree

/-! ## Dyadic interval type (deterministic encoding, v6-compatible shape) -/

/-- Normalised dyadic interval with SHARED scale exponent: both endpoints
live on the grid `m · 2^-k`, mantissas `lo ≤ hi`, invariant `k ≥ 0` (emitter
discipline; kept by construction for every literal emitted).  The full
arithmetic kernel is future `DC.lean` (SPEC-v2 §2.0, §5). -/
structure DC where
  k  : ℤ   -- shared scale exponent, k ≥ 0
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

/-- Point value of a dyadic endpoint (`k ≥ 0` regime): `lo · 2^-k`, i.e.
`lo / 2^k.toNat`.  For point endpoints emitters emit `lo = hi`. -/
noncomputable def DC.value (d : DC) : ℝ := (d.lo : ℝ) / (2 : ℝ) ^ (d.k.toNat)

/-- norm_num glue: peel one `Function.update` layer off the `DC` field
projections.  `DC.value` unfolds to `.lo / 2 ^ .k.toNat` BEFORE these fire,
so the lemmas are stated on the projections; after each peel the `ite`
reduces by `reduceIte` on the `Fin` `DecidableEq` literals and the next
layer peels, all the way to the stored literal. -/
@[simp] theorem DC.lo_update {n : ℕ} (f : Fin n → DC) (i j : Fin n) (v : DC) :
    (Function.update f i v j).lo = (if i = j then v else f j).lo := by
  by_cases h : i = j
  · subst h
    simp [Function.update]
  · simp [Function.update, h, Ne.symm h]

@[simp] theorem DC.k_update {n : ℕ} (f : Fin n → DC) (i j : Fin n) (v : DC) :
    (Function.update f i v j).k = (if i = j then v else f j).k := by
  by_cases h : i = j
  · subst h
    simp [Function.update]
  · simp [Function.update, h, Ne.symm h]

@[simp] theorem DC.hi_update {n : ℕ} (f : Fin n → DC) (i j : Fin n) (v : DC) :
    (Function.update f i v j).hi = (if i = j then v else f j).hi := by
  by_cases h : i = j
  · subst h
    simp [Function.update]
  · simp [Function.update, h, Ne.symm h]

/-- norm_num glue: `Int.toNat` on a raw integer numeral does not reduce
automatically, so consumer modules emit one `rfl` lemma per scale exponent
in use — e.g. `theorem kNat40 : ((40 : ℤ).toNat) = 40 := rfl` — and run
`norm_num [DC.value, kNat40]` to evaluate every endpoint/cut comparison
into exact rational arithmetic (emitters always pass `k ≥ 0`). -/
example : ((40 : ℤ).toNat) = 40 := rfl

/-! ## Leaf rows -/

/-- Uniform leaf row (SPEC-v2 §2.1): endpoints in the shared-grid dyadic
encoding, plus a debt-private companion slot (`Aux` type parameter — each
debt instantiates its own; `Cover`/`cover_sound` are polymorphic in `Aux`). -/
structure LeafRow (n : ℕ) (Aux : Type) where
  boxLo : Fin n → DC
  boxHi : Fin n → DC
  aux   : Aux

/-- Leaf box semantics: closed box on every axis (w1 T-5). -/
def rowBox {n : ℕ} {Aux : Type} (r : LeafRow n Aux) : Set (Fin n → ℝ) :=
  fun x => ∀ i, (r.boxLo i).value ≤ x i ∧ x i ≤ (r.boxHi i).value

/-! ## The tree and the glue theorem -/

/-- Unified binary subdivision tree (SPEC-v2 §2.4, w1 §2.3 shape with dyadic
endpoints).  Parameters: target predicate `P`, leaf table `rows`, leaf pass
flags `leafPass`; node boxes carried as `Fin n → DC` endpoints.  `node`'s cut
`c : DC` is the exact shared endpoint of the two children
(`update hi i c` / `update lo i c`); closed-box overlap on the cut face is
harmless (w1 T-5, same convention as the `by_cases ≤` dispatch trees). -/
inductive Cover (P : (Fin n → ℝ) → Prop)
    (rows : Fin m → LeafRow n Aux) (leafPass : Fin m → Bool) :
    (Fin n → DC) → (Fin n → DC) → Prop where
  | leaf {lo hi} (j : Fin m) :
      (rows j).boxLo = lo → (rows j).boxHi = hi → leafPass j = true →
      Cover P rows leafPass lo hi
  | node {lo hi} (i : Fin n) (c : DC)
      (hcut : (lo i).value ≤ c.value ∧ c.value ≤ (hi i).value)
      (L : Cover P rows leafPass lo (Function.update hi i c))
      (R : Cover P rows leafPass (Function.update lo i c) hi) :
      Cover P rows leafPass lo hi

/-- **Glue theorem (the soul piece).**  All leaves passing ⇒ `P` holds on the
whole box.  `hsound` stays explicitly open: leaf witnesses are provided by
the consumer, so the tree layer is source-agnostic (kernel-decide leaves,
symbolic cell theorems, vac/absurd leaves all plug in without changing this
theorem's axiom profile contribution — it is pure `Prop` induction). -/
theorem cover_sound {n m : ℕ} {Aux : Type} {P : (Fin n → ℝ) → Prop}
    {rows : Fin m → LeafRow n Aux} {leafPass : Fin m → Bool}
    {lo hi : Fin n → DC}
    (hsound : ∀ j : Fin m, leafPass j = true → ∀ x ∈ rowBox (rows j), P x)
    (h : Cover P rows leafPass lo hi)
    (x : Fin n → ℝ) (hx : ∀ i, (lo i).value ≤ x i ∧ x i ≤ (hi i).value) :
    P x := by
  induction h with
  | leaf j hlo hhi hp =>
      refine hsound j hp x ?_
      subst hlo
      subst hhi
      exact hx
  | @node lo hi i c hcut L R ihL ihR =>
      by_cases hle : x i ≤ c.value
      · refine ihL (fun j => ?_)
        have hj := hx j
        by_cases hij : j = i
        · subst hij
          rw [Function.update_self]
          exact ⟨hj.1, hle⟩
        · rw [Function.update_of_ne hij]
          exact ⟨hj.1, hj.2⟩
      · refine ihR (fun j => ?_)
        have hj := hx j
        have hc : c.value < x i := not_le.mp hle
        by_cases hij : j = i
        · subst hij
          rw [Function.update_self]
          exact ⟨hc.le, hj.2⟩
        · rw [Function.update_of_ne hij]
          exact ⟨hj.1, hj.2⟩

end Kepler.NliKit.BoxTree
