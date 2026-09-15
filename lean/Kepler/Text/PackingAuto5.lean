/-
Packing chapter, part 3: the `omega_list` / truncation calculus over Marchal
cells and the Voronoi-cell polytopality toolkit.

HOL source: Flyspeck `scripts/packing/pack3.hl` (module `Packing3`,
2529 lines; 1 `new_definition` (`discrete`) + 144 `prove` items, of which the
two leading ones (`packing_lt`, `BIS_SYM`) are the pack1/sphere bridges).
Ported as `Kepler/Text/PackingAuto5.lean`, skeleton batch: statements are
verbatim-faithful; short/mechanical proofs are discharged, the remaining
geometric arguments carry `sorry`.

Encoding notes.
- HOL `real^3` / `real^N` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler.Geom);
  generic (`A`-polymorphic) list/set lemmas are kept polymorphic where the
  dependencies allow, otherwise instantiated at `V3` (the only instance used
  downstream), matching the `V3`-specialized defs of PackingAuto2.
- HOL `packing` ↔ `Packing` (Kepler.Statement); `dist(x,y)` ↔ `dist x y`;
  `ball(x,r)` ↔ `Metric.ball x r`; `dot` ↔ `⬝ᵥ` (`Matrix.dotProduct`,
  bridged to the inner product by `Kepler.Geom.inner_eq_dot`).
- HOL `INTERS f` ↔ `⋂₀ f`; `UNIONS f` ↔ `⋃₀ f`; `IMAGE f s` ↔ `f '' s`;
  `PSUBSET` ↔ `⊂`; `HAS_SIZE n` ↔ `Set.Finite ∧ Nat.card = n`.
- HOL `bounded` ↔ `Bornology.IsBounded`; `closed`/`open` ↔ `IsClosed`/
  `IsOpen`; `compact` ↔ `IsCompact`; `measurable` ↔ `MeasurableSet`.
- HOL `BUTLAST`/`LAST` ↔ `List.dropLast`/`List.getLast` (junk-value cases
  are never used: all occurrences are guarded by length hypotheses).
- HOL `p permutes s` (pointwise biconditional `!x. x IN s <=> p x IN s`)
  ↔ `PackingAuto2.permutes`. NOTE: HOL Light's `permutes` additionally
  fixes the complement pointwise; `PERMUTES_TRIVIAL` is only true for the
  HOL-strong relation, hence `sorry`ed here (kept for statement fidelity).
- `bis`, `voronoi_open` are public re-copies of the private
  `PackingAuto2.bis` / `PackingAuto2.voronoiOpen` (sphere.hl:360/304);
  delete the private copies in a later merge lane.
- Imports: `Kepler.Text.PackingAuto2` only (it transitively supplies
  Polytope/Fan/Statement/Mathlib and all needed pack_defs encodings;
  `PackingAuto1` is a parallel lane whose `saturated`/`KIUMVTC`/`DRUQUFE`
  clash, so it is deliberately not imported here).
-/

import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Definitions -/

/-- HOL `discrete` (pack3.hl:49):
```
discrete S <=> ?e. &0 < e /\ (!x y. x IN S /\ y IN S /\ dist(x, y) < e ==> x = y)
```
-/
def discrete (S : Set V3) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∀ x y : V3, x ∈ S → y ∈ S → dist x y < e → x = y

/-- HOL `voronoi_open` (sphere.hl:304; also pack1.hl:153). Public copy of the
private `PackingAuto2.voronoiOpen` — delete that copy on merge. -/
def voronoiOpen (V : Set V3) (v : V3) : Set V3 :=
  {x | ∀ w ∈ V, w ≠ v → dist x v < dist x w}

/-- HOL `bis` (sphere.hl:360). Public copy of the private `PackingAuto2.bis`
— delete that copy on merge. -/
def bis (u v : V3) : Set V3 := {x | dist x u = dist x v}

/-! ## Bridges (pack3.hl:23-35) -/

/-- pack3.hl:27 `PACKING_LT`. -/
theorem packing_lt (V : Set V3) :
    Packing V ↔ ∀ u v : V3, u ∈ V → v ∈ V → dist u v < 2 → u = v :=
  ⟨fun h u v hu hv hd => h u hu v hv hd, fun h u hu v hv hd => h u v hu hv hd⟩

/-- pack3.hl:34 `BIS_SYM`. -/
theorem BIS_SYM (p q : V3) : bis p q = bis q p :=
  Set.ext fun _ => eq_comm

/-! ## Auxiliary general lemmas (pack3.hl:45-381) -/

/-- pack3.hl:56 `IMAGE_LEMMA`. -/
theorem IMAGE_LEMMA {α β : Type*} (f : α → β) (s : Set α) : f '' s = {f x | x ∈ s} :=
  rfl

/-- pack3.hl:62 `SING_GSPEC_APP` (`{f x | x = a} = {f a}`). -/
theorem SING_GSPEC_APP {α β : Type*} (f : α → β) (a : α) : f '' {a} = {f a} :=
  Set.image_singleton

/-- pack3.hl:69 `SING_UNION_EQ_INSERT`. -/
theorem SING_UNION_EQ_INSERT {α : Type*} (s : Set α) (x : α) : {x} ∪ s = insert x s :=
  Set.singleton_union.symm

/-- pack3.hl:72 `IN_TRANS`. -/
theorem IN_TRANS {α : Type*} {x : α} {s t : Set α} (h : x ∈ t ∧ t ⊆ s) : x ∈ s :=
  h.2 h.1

/-- HOL `projection` (vectors.ml): `v - ((v dot d) / (d dot d)) % d`. -/
noncomputable def projection (v d : V3) : V3 := v - ((v ⬝ᵥ d) / (d ⬝ᵥ d)) • d

/-- pack3.hl:75 `PROJECTION_ORTHOGONAL`. The orthogonality argument needs the
`VECTOR_SUB_PROJECT_ORTHOGONAL` kit, not ported in this batch. -/
theorem PROJECTION_ORTHOGONAL (d v : V3) : (projection d v) ⬝ᵥ d = 0 := sorry

/-- pack3.hl:80 `LENGTH_IMP_CONS`. -/
theorem LENGTH_IMP_CONS (l : List V3) (h : 1 ≤ l.length) :
    ∃ (hd : V3) (tl : List V3), l = hd :: tl := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl⟩

/-- pack3.hl:90 `LENGTH_1_LEMMA`. -/
theorem LENGTH_1_LEMMA (ul : List V3) (h : ul.length = 1) : ul = [hdV ul] := by
  cases ul with
  | nil => simp at h
  | cons a t =>
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons b s => simp at h
    subst ht
    simp [hdV]

/-- pack3.hl:103 `PERMUTES_TRIVIAL`. Unprovable as encoded: `PackingAuto2.permutes`
is the weak membership biconditional (see header), under which e.g. the
transposition `1 ↔ 2` permutes `{0}` without being the identity. The HOL
statement needs HOL Light's complement-fixing `permutes`. -/
theorem PERMUTES_TRIVIAL (p : Equiv.Perm ℕ) : permutes p {0} ↔ p = Equiv.refl ℕ := sorry

/-- pack3.hl:131 `CONTAINS_BALL_AFFINE_HULL`. -/
theorem CONTAINS_BALL_AFFINE_HULL (s : Set V3) (x : V3) (r : ℝ) (hr : 0 < r)
    (h : Metric.ball x r ⊆ s) : affineSpan ℝ s = ⊤ := sorry

/-- pack3.hl:144 `CONV_UNION_lemma`. -/
theorem CONV_UNION_lemma (A B : Set V3) :
    convexHull ℝ (A ∪ B) = convexHull ℝ (A ∪ convexHull ℝ B) :=
  (convexHull_convexHull_union_right A B).symm

/-- pack3.hl:177 `CONVEX_HULL_EQ_EQ_SET_EQ`. -/
theorem CONVEX_HULL_EQ_EQ_SET_EQ (s t : Set V3) (hs : ¬ affineDependent s)
    (ht : ¬ affineDependent t) : (convexHull ℝ s = convexHull ℝ t ↔ s = t) := sorry

/-- pack3.hl:208 `HULL_INTER_SUBSET_INTER_HULL` (instantiated at the convex
hull operator; HOL is generic in `P`). -/
theorem HULL_INTER_SUBSET_INTER_HULL (s t : Set V3) :
    convexHull ℝ (s ∩ t) ⊆ convexHull ℝ s ∩ convexHull ℝ t :=
  Set.subset_inter (convexHull_mono Set.inter_subset_left)
    (convexHull_mono Set.inter_subset_right)

/-- pack3.hl:213 `HULL_INTER_EQ_INTER` (convex-hull instance). -/
theorem HULL_INTER_EQ_INTER (s t : Set V3) (hs : Convex ℝ s) (ht : Convex ℝ t) :
    convexHull ℝ (s ∩ t) = s ∩ t :=
  Set.eq_of_subset_of_subset
    (Set.subset_inter (convexHull_min Set.inter_subset_left hs)
      (convexHull_min Set.inter_subset_right ht))
    (subset_convexHull ℝ _)

/-- pack3.hl:221 `SUBSET_INTERS`. -/
theorem SUBSET_INTERS {α : Type*} (s : Set α) (f : Set (Set α)) :
    s ⊆ ⋂₀ f ↔ ∀ t ∈ f, s ⊆ t :=
  Set.subset_sInter_iff

/-- pack3.hl:224 `HULL_INTERS_SUBSET_INTERS_HULL` (convex-hull instance). -/
theorem HULL_INTERS_SUBSET_INTERS_HULL (s : Set (Set V3)) :
    convexHull ℝ (⋂₀ s) ⊆ ⋂₀ (convexHull ℝ '' s) := by
  refine Set.subset_sInter_iff.2 fun u hu => ?_
  obtain ⟨t, ht, rfl⟩ := hu
  exact convexHull_mono (Set.sInter_subset_of_mem ht)

/-- pack3.hl:235 `HULL_INTERS_EQ_INTERS` (convex-hull instance). -/
theorem HULL_INTERS_EQ_INTERS (s : Set (Set V3)) (h : ∀ t ∈ s, Convex ℝ t) :
    convexHull ℝ (⋂₀ s) = ⋂₀ s :=
  Set.eq_of_subset_of_subset (convexHull_min (le_refl _) (convex_sInter h))
    (subset_convexHull ℝ _)

/-- pack3.hl:260 `INTERS_2_LEMMA`. -/
theorem INTERS_2_LEMMA {α β : Type*} (a b : α) (f : α → Set β) :
    ⋂₀ (f '' {a, b}) = f a ∩ f b := by
  simp [Set.sInter_image]

/-- pack3.hl:263 `INTER_INTERS`. -/
theorem INTER_INTERS {α β : Type*} (s : Set α) (f : Set β) (Q : β → Set α)
    (hne : f ≠ ∅) : s ∩ ⋂₀ (Q '' f) = ⋂₀ ((fun t => s ∩ Q t) '' f) := by
  ext x
  constructor
  · rintro ⟨hs, h⟩ t ⟨y, hy, rfl⟩
    exact ⟨hs, h (Q y) ⟨y, hy, rfl⟩⟩
  · rintro h
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine ⟨(h _ ⟨y, hy, rfl⟩).1, ?_⟩
    rintro u ⟨z, hz, rfl⟩
    exact (h _ ⟨z, hz, rfl⟩).2

/-- pack3.hl:306 `INTERS_UNIV`. -/
theorem INTERS_UNIV {α : Type*} (f : Set (Set α)) : ⋂₀ f = ⋂₀ (f \ {Set.univ}) := by
  ext x
  constructor
  · exact fun h t ⟨ht, _⟩ => h t ht
  · intro h t ht
    by_cases htU : t = Set.univ
    · simp [htU]
    · exact h t ⟨ht, htU⟩

/-- pack3.hl:312 `INTERS_INTER_INTERS`. -/
theorem INTERS_INTER_INTERS {α : Type*} (f g : Set (Set α)) :
    ⋂₀ f ∩ ⋂₀ g = ⋂₀ (f ∪ g) :=
  Set.sInter_union f g |>.symm

/-- pack3.hl:316 `INTERS_INTER_INTERS_ALT`. -/
theorem INTERS_INTER_INTERS_ALT {α β : Type*} (f g : Set β) (Q : β → Set α) :
    ⋂₀ (Q '' f) ∩ ⋂₀ (Q '' g) = ⋂₀ (Q '' (f ∪ g)) := by
  rw [Set.image_union, Set.sInter_union]

/-- pack3.hl:321 `REAL_DIV_LE_1`. -/
theorem REAL_DIV_LE_1 (a b : ℝ) (hb : 0 < b) : (a / b ≤ 1 ↔ a ≤ b) :=
  div_le_one hb

/-- pack3.hl:327 `UNIONS_FINITE_LEMMA`. -/
theorem UNIONS_FINITE_LEMMA {α β : Type*} (g : Set β) (Q : β → Set α)
    (hg : g.Finite) (hQ : ∀ t ∈ g, (Q t).Finite) : (⋃₀ (Q '' g)).Finite := by
  refine (hg.biUnion fun t ht => hQ t ht).subset ?_
  rintro x ⟨s, hsmem, hx⟩
  obtain ⟨t, ht, rfl⟩ := hsmem
  have : x ∈ Q t := hx
  exact Set.subset_biUnion_of_mem ht this

/-- pack3.hl:344 `REAL_FINITE_MIN_EXISTS`. -/
theorem REAL_FINITE_MIN_EXISTS (S : Set ℝ) (hS : S.Finite) (hne : S ≠ ∅) :
    ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
  obtain ⟨a, ha, hb⟩ :=
    Set.exists_min_image S id hS (Set.nonempty_iff_ne_empty.2 hne)
  exact ⟨a, ha, fun x hx => hb x hx⟩

/-- pack3.hl:348 `REAL_FINITE_MAX_EXISTS`. -/
theorem REAL_FINITE_MAX_EXISTS (S : Set ℝ) (hS : S.Finite) (hne : S ≠ ∅) :
    ∃ m ∈ S, ∀ x ∈ S, x ≤ m := by
  obtain ⟨a, ha, hb⟩ :=
    Set.exists_max_image S id hS (Set.nonempty_iff_ne_empty.2 hne)
  exact ⟨a, ha, fun x hx => hb x hx⟩

/-- pack3.hl:352 `REAL_FINITE_ARGMIN`. -/
theorem REAL_FINITE_ARGMIN {α : Type*} (f : α → ℝ) (S : Set α) (hS : S.Finite)
    (hne : S ≠ ∅) : ∃ a ∈ S, ∀ x ∈ S, f a ≤ f x :=
  Set.exists_min_image S f hS (Set.nonempty_iff_ne_empty.2 hne)

/-- pack3.hl:366 `REAL_FINITE_ARGMAX`. -/
theorem REAL_FINITE_ARGMAX {α : Type*} (f : α → ℝ) (S : Set α) (hS : S.Finite)
    (hne : S ≠ ∅) : ∃ a ∈ S, ∀ x ∈ S, f x ≤ f a :=
  Set.exists_max_image S f hS (Set.nonempty_iff_ne_empty.2 hne)

/-! ## Bisector halfspaces (pack3.hl:385-431) -/

/-- Bridge helper: dotProduct linearity in the left argument. -/
private theorem dsub_dot (a b z : V3) : (a - b) ⬝ᵥ z = a ⬝ᵥ z - b ⬝ᵥ z := by
  rw [← inner_eq_dot (a - b) z, inner_sub_left, inner_eq_dot a z, inner_eq_dot b z]

/-- Bridge helper: the bisector membership in dot form. -/
private theorem bis_mem_eq (u v x : V3) :
    x ∈ bis u v ↔ 2 * ((v - u) ⬝ᵥ x) = v ⬝ᵥ v - u ⬝ᵥ u := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = w ⬝ᵥ w := by
    intro w
    rw [← inner_eq_dot w w, real_inner_self_eq_norm_sq]
  have key : ∀ w : V3, ‖x - w‖ ^ 2 = ‖x‖ ^ 2 - 2 * (w ⬝ᵥ x) + w ⬝ᵥ w := by
    intro w
    have h1 := norm_sub_sq_real (x := x) (y := w)
    rw [← real_inner_comm x w, inner_eq_dot w x, hnorm w] at h1
    linarith
  simp only [bis, Set.mem_setOf_eq, dist_eq_norm]
  constructor
  · intro h
    have h2 : ‖x - u‖ ^ 2 = ‖x - v‖ ^ 2 := by rw [h]
    have h3 := key u
    have h4 := key v
    rw [dsub_dot]
    linarith
  · intro h
    rw [dsub_dot] at h
    have h2 : ‖x - u‖ ^ 2 = ‖x - v‖ ^ 2 := by
      have h3 := key u
      have h4 := key v
      linarith
    have e1 : Real.sqrt (‖x - u‖ ^ 2) = ‖x - u‖ := Real.sqrt_sq (norm_nonneg _)
    have e2 : Real.sqrt (‖x - v‖ ^ 2) = ‖x - v‖ := Real.sqrt_sq (norm_nonneg _)
    have h4 : Real.sqrt (‖x - u‖ ^ 2) = Real.sqrt (‖x - v‖ ^ 2) := by rw [h2]
    rw [e1, e2] at h4
    exact h4

/-- Bridge helper: the bisector `bis_le` membership in dot form. -/
private theorem bis_mem_le (u v x : V3) :
    x ∈ bisLe u v ↔ 2 * ((v - u) ⬝ᵥ x) ≤ v ⬝ᵥ v - u ⬝ᵥ u := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = w ⬝ᵥ w := by
    intro w
    rw [← inner_eq_dot w w, real_inner_self_eq_norm_sq]
  have key : ∀ w : V3, ‖x - w‖ ^ 2 = ‖x‖ ^ 2 - 2 * (w ⬝ᵥ x) + w ⬝ᵥ w := by
    intro w
    have h1 := norm_sub_sq_real (x := x) (y := w)
    rw [← real_inner_comm x w, inner_eq_dot w x, hnorm w] at h1
    linarith
  simp only [bisLe, Set.mem_setOf_eq, dist_eq_norm]
  constructor
  · intro h
    have h2 : ‖x - u‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
      have hnu : 0 ≤ ‖x - u‖ := norm_nonneg _
      have hnv : 0 ≤ ‖x - v‖ := norm_nonneg _
      calc ‖x - u‖ ^ 2 = ‖x - u‖ * ‖x - u‖ := sq _
        _ ≤ ‖x - v‖ * ‖x - u‖ := by nlinarith
        _ ≤ ‖x - v‖ * ‖x - v‖ := by nlinarith
        _ = ‖x - v‖ ^ 2 := (sq _).symm
    have h3 := key u
    have h4 := key v
    rw [dsub_dot]
    linarith
  · intro h
    rw [dsub_dot] at h
    have h2 : ‖x - u‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
      have h3 := key u
      have h4 := key v
      linarith
    calc ‖x - u‖ = Real.sqrt (‖x - u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖x - v‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖x - v‖ := Real.sqrt_sq (norm_nonneg _)

/-- pack3.hl:385 `BIS_EQ_HYPERPLANE`. -/
theorem BIS_EQ_HYPERPLANE (u v : V3) :
    bis u v = {x : V3 | 2 * ((v - u) ⬝ᵥ x) = v ⬝ᵥ v - u ⬝ᵥ u} :=
  Set.ext (bis_mem_eq u v)

/-- pack3.hl:391 `BIS_LE_EQ_HALFSPACE`. -/
theorem BIS_LE_EQ_HALFSPACE (u v : V3) :
    bisLe u v = {x : V3 | 2 * ((v - u) ⬝ᵥ x) ≤ v ⬝ᵥ v - u ⬝ᵥ u} :=
  Set.ext (bis_mem_le u v)

/-- pack3.hl:397 `CONVEX_BIS_LE`. -/
theorem CONVEX_BIS_LE (u v : V3) : Convex ℝ (bisLe u v) := by
  intro x hx y hy a b ha hb hab
  rw [BIS_LE_EQ_HALFSPACE] at hx hy ⊢
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [← inner_eq_dot (v - u) (a • x + b • y), inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_eq_dot (v - u) x, inner_eq_dot (v - u) y]
  have h1 : 2 * (a * ((v - u) ⬝ᵥ x)) ≤ a * (v ⬝ᵥ v - u ⬝ᵥ u) := by
    rw [show 2 * (a * ((v - u) ⬝ᵥ x)) = a * (2 * ((v - u) ⬝ᵥ x)) from by ring]
    exact mul_le_mul_of_nonneg_left hx ha
  have h2 : 2 * (b * ((v - u) ⬝ᵥ y)) ≤ b * (v ⬝ᵥ v - u ⬝ᵥ u) := by
    rw [show 2 * (b * ((v - u) ⬝ᵥ y)) = b * (2 * ((v - u) ⬝ᵥ y)) from by ring]
    exact mul_le_mul_of_nonneg_left hy hb
  have h5 : a * (v ⬝ᵥ v - u ⬝ᵥ u) + b * (v ⬝ᵥ v - u ⬝ᵥ u) = v ⬝ᵥ v - u ⬝ᵥ u := by
    rw [← add_mul, hab, one_mul]
  rw [mul_add]
  linarith

/-- pack3.hl:402 `CLOSED_BIS_LE`. -/
theorem CLOSED_BIS_LE (u v : V3) : IsClosed (bisLe u v) := by
  have hc : Continuous fun x : V3 => (v - u) ⬝ᵥ x := by
    have h2 : Continuous fun t : V3 => inner ℝ (v - u) t :=
      continuous_const.inner continuous_id
    simpa [inner_eq_dot] using h2
  rw [BIS_LE_EQ_HALFSPACE]
  exact isClosed_le (continuous_const.mul hc) continuous_const

/-- pack3.hl:406 `CONVEX_BIS`. -/
theorem CONVEX_BIS (u v : V3) : Convex ℝ (bis u v) := by
  have h : bis u v = bisLe u v ∩ bisLe v u := by
    ext x
    simp only [bis, bisLe, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h1
      exact ⟨le_of_eq h1, le_of_eq h1.symm⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
  rw [h]
  exact (CONVEX_BIS_LE u v).inter (CONVEX_BIS_LE v u)

/-- pack3.hl:410 `POLYHEDRON_BIS`. -/
theorem POLYHEDRON_BIS (u v : V3) : polyhedron (bis u v) := by
  by_cases huv : u = v
  · subst huv
    refine ⟨∅, Set.finite_empty, ?_, ?_⟩
    · ext x
      simp only [Set.sInter_empty, Set.mem_univ, bis, Set.mem_setOf_eq]
    · intro h hF
      exact absurd hF (by simp)
  · have hne1 : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
    have hne2 : u - v ≠ 0 := sub_ne_zero.2 huv
    set hA : Set V3 := {x : V3 | (v - u) ⬝ᵥ x ≤ (v ⬝ᵥ v - u ⬝ᵥ u) / 2} with hAdef
    set hB : Set V3 := {x : V3 | (u - v) ⬝ᵥ x ≤ (u ⬝ᵥ u - v ⬝ᵥ v) / 2} with hBdef
    refine ⟨{hA, hB}, Set.Finite.insert hA (Set.finite_singleton hB), ?_, ?_⟩
    · rw [Set.sInter_pair, BIS_EQ_HYPERPLANE u v]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      have hduv := dsub_dot v u x
      have hdvu := dsub_dot u v x
      constructor
      · intro h1
        have hA1 : (v - u) ⬝ᵥ x ≤ (v ⬝ᵥ v - u ⬝ᵥ u) / 2 := by linarith
        have hB1 : (u - v) ⬝ᵥ x ≤ (u ⬝ᵥ u - v ⬝ᵥ v) / 2 := by
          rw [hdvu]
          linarith
        rw [hAdef, hBdef]
        simp only [Set.mem_setOf_eq]
        exact ⟨hA1, hB1⟩
      · rintro ⟨h1, h2⟩
        rw [hAdef] at h1
        rw [hBdef] at h2
        simp only [Set.mem_setOf_eq] at h1 h2
        rw [hdvu] at h2
        linarith
    · intro h hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hE | hE
      · rw [hE, hAdef]
        exact ⟨v - u, (v ⬝ᵥ v - u ⬝ᵥ u) / 2, hne1, rfl⟩
      · rw [hE, hBdef]
        exact ⟨u - v, (u ⬝ᵥ u - v ⬝ᵥ v) / 2, hne2, rfl⟩

/-- pack3.hl:415 `AFFINE_BIS`. Affine sets are encoded via `AffineSubspace`. -/
theorem AFFINE_BIS (a b : V3) : ∃ K : AffineSubspace ℝ V3, (K : Set V3) = bis a b := sorry

/-- pack3.hl:419 `AFFINE_HULL_INTERS_BIS`. -/
theorem AFFINE_HULL_INTERS_BIS (p : V3) (s : Set V3) :
    affineSpan ℝ (⋂₀ {bis p u | u ∈ s}) = ⋂₀ {bis p u | u ∈ s} := sorry

/-- pack3.hl:428 `MID_POINT_EXISTS` (`between x (v,w)` encoded as
`dist v x + dist x w = dist v w`). -/
theorem MID_POINT_EXISTS (v w : V3) (d : ℝ) (hd1 : 0 ≤ d) (hd2 : d ≤ dist v w) :
    ∃ x : V3, dist v x + dist x w = dist v w ∧ dist v x = d := by
  by_cases hvw : v = w
  · subst hvw
    have hd0 : d = 0 := by have h := dist_self v; linarith
    refine ⟨v, ?_, ?_⟩ <;> simp [dist_self, hd0]
  · have hD : 0 < dist v w := dist_pos.2 hvw
    have hpos : 0 ≤ d / dist v w := div_nonneg hd1 hD.le
    have hle1 : d / dist v w ≤ 1 := (div_le_one hD).2 hd2
    have hnorm : ‖w - v‖ = dist v w := by rw [← dist_eq_norm, dist_comm]
    have xeq : dist (v + (d / dist v w) • (w - v)) v = d := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpos, hnorm]
      field_simp
    have xeq2 : dist (v + (d / dist v w) • (w - v)) w = dist v w - d := by
      rw [dist_eq_norm]
      have hex : (v + (d / dist v w) • (w - v)) - w =
          ((d / dist v w) - 1) • (w - v) := by
        rw [sub_smul, smul_sub, one_smul]
        abel
      rw [hex, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : (d / dist v w) - 1 ≤ 0), hnorm]
      field_simp
      ring
    have xe1 : dist v (v + (d / dist v w) • (w - v)) = d := by
      rw [dist_comm]
      exact xeq
    exact ⟨v + (d / dist v w) • (w - v), by rw [xe1, xeq2]; ring, xe1⟩

/-! ## Discreteness (pack3.hl:464-541) -/

/-- pack3.hl:464 `CLOSED_DISCRETE`. -/
theorem CLOSED_DISCRETE (A : Set V3) (hA : discrete A) : IsClosed A := by
  obtain ⟨e, he, hsep⟩ := hA
  have hsub : closure A ⊆ A := by
    intro x hxc
    by_contra hxA
    obtain ⟨y0, hy0A, hy0d⟩ := Metric.mem_closure_iff.1 hxc (e / 2) (by linarith)
    have hball : ∀ z ∈ A, dist x z < e / 2 → z = y0 := by
      intro z hz hzd
      exact (hsep y0 z hy0A hz (by
        have ht := dist_triangle y0 x z
        rw [dist_comm y0 x] at ht
        linarith)).symm
    have hpos : 0 < dist x y0 := dist_pos.2 fun h => hxA (h ▸ hy0A)
    obtain ⟨z, hzA, hzd⟩ := Metric.mem_closure_iff.1 hxc (dist x y0 / 2) (by positivity)
    have hzlt : dist x z < e / 2 := by linarith
    have hzy := hball z hzA hzlt
    rw [hzy] at hzd
    linarith
  exact closure_subset_iff_isClosed.1 hsub

/-- pack3.hl:472 `DISCRETE_SUBSET`. -/
theorem DISCRETE_SUBSET (A B : Set V3) (hA : discrete A) (hB : B ⊆ A) : discrete B := by
  obtain ⟨e, he, hsep⟩ := hA
  exact ⟨e, he, fun x y hx hy hlt => hsep x y (hB hx) (hB hy) hlt⟩

/-- pack3.hl:485 `DISCRETE_OPEN_COVER` (`(b INTER S) HAS_SIZE 1` encoded as
`∃ p : V3, b ∩ S = {p}`). -/
theorem DISCRETE_OPEN_COVER (S : Set V3) (hS : discrete S) :
    ∃ f : Set (Set V3), (∀ b ∈ f, IsOpen b ∧ ∃ p : V3, b ∩ S = {p}) ∧
      S ⊆ ⋃₀ f := by
  obtain ⟨e, he, hsep⟩ := hS
  refine ⟨(fun x : V3 => Metric.ball x (e / 2)) '' S, ?_, ?_⟩
  · rintro b ⟨x, hxS, rfl⟩
    have hsub : (Metric.ball x (e / 2) ∩ S).Subsingleton := by
      rintro a ⟨ha1, ha2⟩ c ⟨hc1, hc2⟩
      have ha := Metric.mem_ball.1 ha1
      have hc := Metric.mem_ball.1 hc1
      rw [dist_comm c x] at hc
      have ht := dist_triangle a x c
      exact hsep a c ha2 hc2 (by linarith)
    have hxmem : x ∈ Metric.ball x (e / 2) ∩ S :=
      ⟨Metric.mem_ball_self (by linarith), hxS⟩
    refine ⟨Metric.isOpen_ball, x, hsub.eq_singleton_of_mem hxmem⟩
  · intro x hx
    exact Set.subset_sUnion_of_mem (Set.mem_image_of_mem _ hx)
      (Metric.mem_ball_self (by linarith))

/-- pack3.hl:503 `DISCRETE_BOUNDED_IMP_FINITE`. -/
theorem DISCRETE_BOUNDED_IMP_FINITE (S : Set V3) (hS : discrete S)
    (hb : Bornology.IsBounded S) : S.Finite := by
  obtain ⟨e, he, hsep⟩ := hS
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.1 hb
  rcases Set.eq_empty_or_nonempty S with hE | ⟨c0, hc0⟩
  · exact hE.symm ▸ Set.finite_empty
  have hsubCB : S ⊆ Metric.closedBall c0 R := fun x hx =>
    Metric.mem_closedBall.2 (by rw [dist_comm]; exact hR (x := c0) hc0 (y := x) hx)
  obtain ⟨t, htcov⟩ :=
    (isCompact_closedBall c0 R).elim_finite_subcover (fun i : V3 => Metric.ball i (e / 2))
      (fun _ => Metric.isOpen_ball)
      (fun p _ => Set.mem_iUnion.2 ⟨p, Metric.mem_ball_self (ε := e / 2) (by linarith)⟩)
  have htF : (t : Set V3).Finite := t.finite_toSet
  have hfin : ∀ y ∈ t, (Metric.ball y (e / 2) ∩ S).Finite := by
    intro y _
    have hsub1 : (Metric.ball y (e / 2) ∩ S).Subsingleton := by
      rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩
      have hta := dist_triangle a y b
      have ha := Metric.mem_ball.1 ha1
      have hb' := Metric.mem_ball.1 hb1
      rw [dist_comm b y] at hb'
      exact hsep a b ha2 hb2 (by linarith)
    rcases Set.eq_empty_or_nonempty (Metric.ball y (e / 2) ∩ S) with hE | ⟨p, hp⟩
    · rw [hE]
      exact Set.finite_empty
    · have heq : Metric.ball y (e / 2) ∩ S = {p} := hsub1.eq_singleton_of_mem hp
      exact heq ▸ Set.finite_singleton p
  refine (UNIONS_FINITE_LEMMA (t : Set V3) (fun y => Metric.ball y (e / 2) ∩ S) htF
    hfin).subset ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (htcov (hsubCB hx))
  have hxy' : x ∈ (Metric.ball y (e / 2) ∩ S : Set V3) := ⟨hxy, hx⟩
  exact Set.subset_sUnion_of_mem (Set.mem_image_of_mem _ hy) hxy'

/-- pack3.hl:479 `DISCRETE_IMP_BOUNDED_EQ_COMPACT`. -/
theorem DISCRETE_IMP_BOUNDED_EQ_COMPACT (S : Set V3) (hS : discrete S) :
    (Bornology.IsBounded S ↔ IsCompact S) := by
  constructor
  · intro hb
    exact (DISCRETE_BOUNDED_IMP_FINITE S hS hb).isCompact
  · intro hc
    exact hc.isBounded

/-- pack3.hl:536 `PACKING_IMP_DISCRETE`. -/
theorem PACKING_IMP_DISCRETE (V : Set V3) (hV : Packing V) : discrete V :=
  ⟨2, two_pos, fun x y hx hy hlt => hV x hx y hy hlt⟩

/-! ## KIUMVTC, TIWWFYQ (pack3.hl:541-613) -/

/-- pack3.hl:541 `KIUMVTC`. -/
theorem KIUMVTC (p : V3) (r : ℝ) (V : Set V3) (hV : Packing V) :
    (V ∩ Metric.ball p r).Finite := by
  by_cases hr : r ≤ 0
  · rw [Metric.ball_eq_empty.2 hr]
    simp
  · have hV' : Packing ((fun x : V3 => x - p) '' V) := by
      intro u hu v hv hlt
      obtain ⟨u, huV, rfl⟩ := hu
      obtain ⟨v, hvV, rfl⟩ := hv
      have hab : (u - p) - (v - p) = u - v := by abel
      have h1 : dist u v < 2 := by
        rw [dist_eq_norm, ← hab, ← dist_eq_norm]
        exact hlt
      exact congrArg (fun x => x - p) (hV u huV v hvV h1)
    have hfin : (((fun x : V3 => x - p) '' V) ∩ Metric.ball 0 r).Finite :=
      hV'.finite_inter_ball r
    have hsub : V ∩ Metric.ball p r ⊆
        (fun x : V3 => x + p) '' ((fun x : V3 => x - p) '' V ∩ Metric.ball 0 r) := by
      rintro x ⟨hxV, hxb⟩
      refine ⟨x - p, ⟨⟨x, hxV, rfl⟩, ?_⟩, by simp⟩
      have h0 : dist 0 (x - p) = dist x p := by
        rw [dist_eq_norm, dist_eq_norm, zero_sub, norm_neg]
      exact Metric.mem_ball.2 (by rw [dist_comm, h0]; exact hxb)
    have himg : ((fun x : V3 => x + p) ''
        ((fun x : V3 => x - p) '' V ∩ Metric.ball 0 r)).Finite :=
      Set.Finite.image (fun x : V3 => x + p) hfin
    exact himg.subset hsub

/-- pack3.hl:564 `TIWWFYQ`. -/
theorem TIWWFYQ (V : Set V3) (p : V3) (hV : Packing V) (hs : saturated V) :
    ∃ v ∈ V, p ∈ voronoiClosed V v := sorry

/-! ## Center and ball containment (pack3.hl:613-789) -/

/-- pack3.hl:613 `CENTER_IN_VORONOI_CELL`. -/
theorem CENTER_IN_VORONOI_CELL (V : Set V3) (v : V3) :
    v ∈ voronoiClosed V v ∧ v ∈ voronoiOpen V v := by
  refine ⟨fun w _ => by rw [dist_self]; exact dist_nonneg, fun w _ hwne => by
    rw [dist_self v]
    exact dist_pos.2 (Ne.symm hwne)⟩

/-- pack3.hl:629 `VORONOI_CLOSED_CONTAINS_BALL`. -/
theorem VORONOI_CLOSED_CONTAINS_BALL (V : Set V3) (v : V3) (hV : Packing V) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball v r ⊆ voronoiClosed V v := by
  by_cases hvV : v ∈ V
  · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
    by_cases hvw : w = v
    · subst hvw; exact le_refl _
    · have h2 : 2 ≤ dist v w := by
        have h3 := hV.dist_ge_two hw hvV hvw
        rwa [dist_comm w v] at h3
      have h1 : dist x v < 1 := Metric.mem_ball.1 hx
      have ht := dist_triangle v x w
      rw [dist_comm v x] at ht
      linarith
  · have hVcl : IsClosed V := CLOSED_DISCRETE V (PACKING_IMP_DISCRETE V hV)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVcl.isOpen_compl v (by simpa using hvV)
    refine ⟨ε / 4, by linarith, fun x hx u hu => ?_⟩
    have hge : ∀ u ∈ V, ε ≤ dist v u := by
      intro u hu
      refine le_of_not_gt fun hcon => ?_
      have hmem : u ∈ Metric.ball v ε := Metric.mem_ball.2 (by rw [dist_comm]; exact hcon)
      have hc : u ∈ Vᶜ := hball hmem
      rw [Set.mem_compl_iff] at hc
      exact hc hu
    have hxv := Metric.mem_ball.1 hx
    have ht := dist_triangle v x u
    rw [dist_comm v x] at ht
    have hge' := hge u hu
    linarith

/-- pack3.hl:753 `AFF_DIM_VORONOI_CLOSED`. -/
theorem AFF_DIM_VORONOI_CLOSED (V : Set V3) (v : V3) (hV : Packing V) :
    affDim (voronoiClosed V v) = 3 := sorry

/-- pack3.hl:767 `VORONOI_BALL2`. -/
theorem VORONOI_BALL2 (V : Set V3) (v : V3) (hs : saturated V) :
    voronoiClosed V v ⊆ Metric.ball v 2 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hs x
  exact Metric.mem_ball.2 (lt_of_le_of_lt (hx y hy) hxy)

/-- pack3.hl:782 `BOUNDED_VORONOI_CLOSED`. -/
theorem BOUNDED_VORONOI_CLOSED (V : Set V3) (v : V3) (hs : saturated V) :
    Bornology.IsBounded (voronoiClosed V v) :=
  (Metric.isBounded_ball).subset (VORONOI_BALL2 V v hs)

/-! ## voronoi_closed as intersection of bisectors (pack3.hl:789-970) -/

/-- pack3.hl:789 `VORONOI_CLOSED_EQ_INTERS_BIS_LE`. -/
theorem VORONOI_CLOSED_EQ_INTERS_BIS_LE (S : Set V3) (v : V3) :
    voronoiClosed S v = ⋂₀ ((fun w : V3 => bisLe v w) '' S) := by
  rw [voronoiClosed]
  ext x
  refine ⟨fun h t ht => ?_, fun h w hw => h (bisLe v w) ⟨w, hw, rfl⟩⟩
  obtain ⟨w, hw, heq⟩ := ht
  rw [← heq]
  exact h w hw

/-- pack3.hl:803 `VORONOI_CLOSED_EQ_INTERS_BIS_LE_ALT`. -/
theorem VORONOI_CLOSED_EQ_INTERS_BIS_LE_ALT (S : Set V3) (v : V3) :
    voronoiClosed S v =
      ⋂₀ ((fun w : V3 => bisLe v w) '' {w : V3 | w ∈ S ∧ w ≠ v}) := by
  rw [voronoiClosed]
  ext x
  refine ⟨fun h t ht => ?_, fun h w hw => ?_⟩
  · obtain ⟨w, ⟨hw, hwne⟩, heq⟩ := ht
    rw [← heq]
    exact h w hw
  · by_cases hwe : w = v
    · subst hwe; exact le_refl _
    · exact h (bisLe v w) ⟨w, ⟨hw, hwe⟩, rfl⟩

/-- pack3.hl:823 `VORONOI_INTER_BIS_LE`. -/
theorem VORONOI_INTER_BIS_LE (V : Set V3) (v : V3) (hV : Packing V) (hs : saturated V)
    (hv : v ∈ V) :
    voronoiClosed V v =
      ⋂₀ ((fun u : V3 => bisLe v u) '' {u : V3 | u ∈ V ∧ u ∈ Metric.ball v 4 ∧ u ≠ v}) := sorry

/-- pack3.hl:886 `VORONOI_CLOSED_EQ_FINITE_INTERS_BIS_LE`. -/
theorem VORONOI_CLOSED_EQ_FINITE_INTERS_BIS_LE (V : Set V3) (v : V3) (hV : Packing V)
    (hs : saturated V) (hv : v ∈ V) :
    ∃ W : Set V3, W ⊆ V ∧ v ∉ W ∧ W.Finite ∧
      voronoiClosed V v = ⋂₀ ((fun u : V3 => bisLe v u) '' W) := sorry

/-- pack3.hl:916 `VORONOI_POLYHEDRON`. -/
theorem VORONOI_POLYHEDRON (V : Set V3) (v : V3) (hV : Packing V) (hs : saturated V)
    (hv : v ∈ V) : polyhedron (voronoiClosed V v) := sorry

/-- pack3.hl:940 `CONVEX_VORONOI_CLOSED`. -/
theorem CONVEX_VORONOI_CLOSED (S : Set V3) (v : V3) : Convex ℝ (voronoiClosed S v) := by
  rw [VORONOI_CLOSED_EQ_INTERS_BIS_LE]
  refine convex_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact CONVEX_BIS_LE v w

/-- pack3.hl:949 `CLOSED_VORONOI_CLOSED`. -/
theorem CLOSED_VORONOI_CLOSED (S : Set V3) (v : V3) : IsClosed (voronoiClosed S v) := by
  rw [VORONOI_CLOSED_EQ_INTERS_BIS_LE]
  refine isClosed_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact CLOSED_BIS_LE v w

/-- pack3.hl:957 `COMPACT_VORONOI_CLOSED`. -/
theorem COMPACT_VORONOI_CLOSED (S : Set V3) (v : V3) (hs : saturated S) :
    IsCompact (voronoiClosed S v) :=
  (isCompact_closedBall v 2).of_isClosed_subset (CLOSED_VORONOI_CLOSED S v)
    (fun x hx => Metric.ball_subset_closedBall (VORONOI_BALL2 S v hs hx))

/-- pack3.hl:970 `DRUQUFE`. -/
theorem DRUQUFE (V : Set V3) (v : V3) (hV : Packing V) (hs : saturated V) :
    IsCompact (voronoiClosed V v) ∧ Convex ℝ (voronoiClosed V v) ∧
      MeasurableSet (voronoiClosed V v) :=
  ⟨COMPACT_VORONOI_CLOSED V v hs, CONVEX_VORONOI_CLOSED V v,
    (CLOSED_VORONOI_CLOSED V v).measurableSet⟩

/-! ## initial_sublist and list utilities (pack3.hl:992-1672) -/

private theorem getD_map'' {α : Type*} [Inhabited α] (g : ℕ → α) (l : List ℕ) (i : ℕ)
    (d : α) (h : i < l.length) : (l.map g).getD i d = g (l.getD i (0 : ℕ)) := by
  have hlen : i < (l.map g).length := by
    simp only [List.length_map]
    exact h
  have h1 : (l.map g).getD i d = (l.map g)[i] :=
    List.getD_eq_getElem (l := l.map g) (n := i) (d := d) (by simpa using h)
  have h2 : (l.map g)[i] = g (l[i]) := by rw [List.getElem_map]
  have h3 : l[i] = l.getD i (0 : ℕ) :=
    (List.getD_eq_getElem l (0 : ℕ) h).symm
  rw [h1, h2, h3]

/-- pack3.hl:992 `INITIAL_SUBLIST_APPEND`. -/
theorem INITIAL_SUBLIST_APPEND (ul vl : List V3) : initialSublist ul (ul ++ vl) :=
  ⟨vl, rfl⟩

/-- pack3.hl:997 `INITIAL_SUBLIST_HEAD_EQ`. -/
theorem INITIAL_SUBLIST_HEAD_EQ {xl zl : List V3} {hx hz : V3} {tx tz : List V3}
    (hxl : xl = hx :: tx) (hzl : zl = hz :: tz) (h : initialSublist xl zl) : hx = hz := by
  obtain ⟨yl, hyl⟩ := h
  rw [hyl, hxl, List.cons_append] at hzl
  injection hzl with _ _

/-- pack3.hl:1006 `INITIAL_SUBLIST_HEAD_EQ_2`. -/
theorem INITIAL_SUBLIST_HEAD_EQ_2 {xl yl zl : List V3} {hx hy : V3} {tx ty : List V3}
    (hxl : xl = hx :: tx) (hyl : yl = hy :: ty)
    (h1 : initialSublist xl zl) (h2 : initialSublist yl zl) : hx = hy := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  have e1 : zl = hx :: (tx ++ t) := by rw [ht, hxl, List.cons_append]
  have e2 : zl = hy :: (ty ++ t') := by rw [ht', hyl, List.cons_append]
  injection e1.symm.trans e2

/-- pack3.hl:1011 `INITIAL_SUBLIST_TAIL`. -/
theorem INITIAL_SUBLIST_TAIL {xl zl : List V3} {hx : V3} {tx : List V3}
    (hxl : xl = hx :: tx) (h : initialSublist xl zl) : initialSublist tx zl.tail := by
  obtain ⟨yl, hyl⟩ := h
  exact ⟨yl, by rw [hyl, hxl, List.cons_append, List.tail_cons]⟩

/-- pack3.hl:1022 `INITIAL_SUBLIST_UNIQUE`. -/
theorem INITIAL_SUBLIST_UNIQUE {xl yl zl : List V3} {n : ℕ} (h1 : initialSublist xl zl)
    (h2 : initialSublist yl zl) (hl1 : xl.length = n) (hl2 : yl.length = n) : xl = yl := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  have heq : xl ++ t1 = yl ++ t2 := by rw [← ht1, ht2]
  rcases List.append_eq_append_iff.1 heq with ⟨t, rfl, -⟩ | ⟨t, rfl, -⟩
  · rw [List.length_append, hl1] at hl2
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
  · rw [List.length_append, hl2] at hl1
    have ht0 : t.length = 0 := by omega
    rw [List.length_eq_zero_iff.1 ht0, List.append_nil]

/-- pack3.hl:1044 `INITIAL_SUBLIST_TRANS`. -/
theorem INITIAL_SUBLIST_TRANS {xl yl zl : List V3} (h1 : initialSublist xl yl)
    (h2 : initialSublist yl zl) : initialSublist xl zl := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  exact ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

/-- pack3.hl:1051 `INITIAL_SUBLIST_REFL`. -/
theorem INITIAL_SUBLIST_REFL (ul : List V3) : initialSublist ul ul := ⟨[], by simp⟩

/-- pack3.hl:1055 `INITIAL_SUBLIST_NIL`. -/
theorem INITIAL_SUBLIST_NIL (zl : List V3) : initialSublist [] zl := ⟨zl, rfl⟩

/-- pack3.hl:1060 `INITIAL_SUBLIST_EXISTS_ALT`. -/
theorem INITIAL_SUBLIST_EXISTS_ALT (zl : List V3) (n : ℕ) (k : ℕ) (hn : zl.length = n)
    (hk : k ≤ n) : ∃ xl, initialSublist xl zl ∧ xl.length = k :=
  ⟨zl.take k, ⟨zl.drop k, (List.take_append_drop k zl).symm⟩, by
    rw [List.length_take_of_le (by omega)]⟩

/-- pack3.hl:1103 `INITIAL_SUBLIST_EXISTS`. -/
theorem INITIAL_SUBLIST_EXISTS (zl : List V3) (k : ℕ) (hk : k ≤ zl.length) :
    ∃ xl, initialSublist xl zl ∧ xl.length = k :=
  INITIAL_SUBLIST_EXISTS_ALT zl zl.length k rfl hk

/-- pack3.hl:1108 `INITIAL_SUBLIST_LENGTH_LE`. -/
theorem INITIAL_SUBLIST_LENGTH_LE {xl zl : List V3} (h : initialSublist xl zl) :
    xl.length ≤ zl.length := by
  obtain ⟨yl, hyl⟩ := h
  rw [hyl, List.length_append]
  omega

/-- pack3.hl:1115 `INITIAL_SUBLIST_APPEND_2`. -/
theorem INITIAL_SUBLIST_APPEND_2 (xl ul vl : List V3) :
    initialSublist xl (ul ++ vl) ↔
      initialSublist xl ul ∨ ∃ yl, initialSublist yl vl ∧ xl = ul ++ yl := by
  sorry
/-- pack3.hl:1185 `INITIAL_SUBLIST_SING`. -/
theorem INITIAL_SUBLIST_SING (v : V3) (xl : List V3) :
    initialSublist xl [v] ↔ xl = [] ∨ xl = [v] := by
  constructor
  · rintro ⟨yl, hyl⟩
    cases xl with
    | nil => exact Or.inl rfl
    | cons a t =>
      right
      injection hyl with he htail
      have h2 := List.append_eq_nil_iff.1 htail.symm
      rw [he, h2.1]
  · rintro (rfl | rfl)
    · exact ⟨[v], by simp⟩
    · exact ⟨[], by simp⟩
/-- pack3.hl:1218 `INITIAL_SUBLIST_APPEND_SING`. -/
theorem INITIAL_SUBLIST_APPEND_SING (xl ul : List V3) (v : V3) :
    initialSublist xl (ul ++ [v]) ↔ initialSublist xl ul ∨ xl = ul ++ [v] := by
  sorry
/-- pack3.hl:1235 `INITIAL_SUBLIST_HD`. -/
theorem INITIAL_SUBLIST_HD (ul : List V3) (h : 1 ≤ ul.length) :
    initialSublist [hdV ul] ul := by
  cases ul with
  | nil => simp at h
  | cons a t => exact ⟨t, rfl⟩

/-- pack3.hl:1245 `BUTLAST_INITIAL_SUBLIST`. -/
theorem BUTLAST_INITIAL_SUBLIST (ul : List V3) (h : 1 ≤ ul.length) :
    initialSublist ul.dropLast ul := by
  sorry
/-- pack3.hl:1262 `LENGTH_BUTLAST`. -/
theorem LENGTH_BUTLAST (ul : List V3) (h : 1 ≤ ul.length) :
    ul.dropLast.length = ul.length - 1 := by
  sorry
/-- pack3.hl:1274 `HD_IN_SET_OF_LIST`. -/
theorem HD_IN_SET_OF_LIST (ul : List V3) (h : 1 ≤ ul.length) : hdV ul ∈ setOfList ul := by
  cases ul with
  | nil => simp at h
  | cons a t => simp [setOfList, hdV]

/-- pack3.hl:1283 `HD_INITIAL_SUBLIST`. -/
theorem HD_INITIAL_SUBLIST {xl yl : List V3} (h : 1 ≤ yl.length)
    (hsub : initialSublist yl xl) : hdV yl = hdV xl := by
  sorry
/-- pack3.hl:1303 `SET_OF_LIST_INITIAL_SUBLIST_SUBSET`. -/
theorem SET_OF_LIST_INITIAL_SUBLIST_SUBSET {vl ul : List V3} (h : initialSublist vl ul) :
    setOfList vl ⊆ setOfList ul := by
  sorry
/-- pack3.hl:1309 `LENGTH_REVERSE`. -/
theorem LENGTH_REVERSE (ul : List V3) : ul.reverse.length = ul.length :=
  List.length_reverse

/-- pack3.hl:1315 `EL_REVERSE`. -/
theorem EL_REVERSE (ul : List V3) (i : ℕ) (h : i < ul.length) :
    elV ul.reverse i = elV ul (ul.length - 1 - i) := by
  sorry
/-- pack3.hl:1350 `LENGTH_TABLE`. -/
theorem LENGTH_TABLE (f : ℕ → V3) (n : ℕ) : (table f n).length = n := by
  sorry
/-- pack3.hl:1360 `EL_TABLE`. -/
theorem EL_TABLE (f : ℕ → V3) (n : ℕ) (i : ℕ) (h : i < n) :
    elV (table f n) i = f i := by
  sorry
/-- pack3.hl:1380 `LENGTH_LEFT_ACTION_LIST`. -/
theorem LENGTH_LEFT_ACTION_LIST (ul : List V3) (p : Equiv.Perm ℕ) :
    (leftActionList p ul).length = ul.length := by
  simp [leftActionList]

/-- pack3.hl:1385 `EL_LEFT_ACTION_LIST`. -/
theorem EL_LEFT_ACTION_LIST (ul : List V3) (p : Equiv.Perm ℕ)
    (hp : permutes p {i : ℕ | i < ul.length}) (i : ℕ) (hi : i < ul.length) :
    elV ul i = elV (leftActionList p ul) (p i) := by
  sorry
/-- pack3.hl:1408 `MEM_LEFT_ACTION_LIST`. -/
theorem MEM_LEFT_ACTION_LIST (ul : List V3) (p : Equiv.Perm ℕ)
    (hp : permutes p {i : ℕ | i < ul.length}) (x : V3) :
    x ∈ leftActionList p ul ↔ x ∈ ul := by
  sorry
/-- pack3.hl:1440 `SET_OF_LIST_LEFT_ACTION_LIST`. -/
theorem SET_OF_LIST_LEFT_ACTION_LIST (ul : List V3) (p : Equiv.Perm ℕ)
    (hp : permutes p {i : ℕ | i < ul.length}) :
    setOfList (leftActionList p ul) = setOfList ul := by
  sorry
/-- pack3.hl:1448 `CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT`. -/
theorem CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT (ul : List V3)
    (h : Nat.card (setOfList ul) = ul.length) (i j : ℕ) (hi : i < ul.length)
    (hj : j < ul.length) (hij : i ≠ j) : elV ul i ≠ elV ul j := by
  sorry
/-- pack3.hl:1499 `LENGTH_DROP`. -/
theorem LENGTH_DROP (i : ℕ) (ul : List V3) (h : i < ul.length) :
    (dropIth ul i).length = ul.length - 1 := by
  sorry
/-- pack3.hl:1532 `EL_DROP`. -/
theorem EL_DROP (i : ℕ) (ul : List V3) (j : ℕ) (h : i < ul.length)
    (hj : j < ul.length - 1) :
    elV (dropIth ul i) j = if j < i then elV ul j else elV ul (j + 1) := by
  sorry
/-! ## barV and the truncation calculus (pack3.hl:1686-1960) -/

private theorem trunc_init_len (k : ℕ) (zl : List V3) (h : k + 1 ≤ zl.length) :
    initialSublist (truncateSimplex k zl) zl ∧ (truncateSimplex k zl).length = k + 1 := by
  have heps := @Classical.epsilon_spec _
    (fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
    ⟨zl.take (k + 1), List.length_take_of_le (by omega),
      ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
  exact ⟨heps.2, heps.1⟩

/-- pack3.hl:1686 `BARV_SUBSET`. -/
theorem BARV_SUBSET (V : Set V3) (k : ℕ) (ul : List V3) (hbar : barV V k ul) :
    setOfList ul ⊆ V :=
      (hbar.2 ul ⟨INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩).2.1

/-- pack3.hl:1702 `BARV_CONS`. -/
theorem BARV_CONS (V : Set V3) (k : ℕ) (ul : List V3) (hbar : barV V k ul) :
    ∃ hd : V3, ∃ tl : List V3, ul = hd :: tl ∧ hd = hdV ul := by
  cases ul with
  | nil => exact absurd hbar.1 (by simp)
  | cons a t => exact ⟨a, t, rfl, rfl⟩

/-- pack3.hl:1712 `BARV_INITIAL_SUBLIST`. -/
theorem BARV_INITIAL_SUBLIST (V : Set V3) (k : ℕ) (ul : List V3) (vl : List V3)
    (hbar : barV V k ul) (hsub : initialSublist vl ul) (hpos : 0 < vl.length) :
    barV V (vl.length - 1) vl := by
  refine ⟨by omega, fun wl hwl => hbar.2 wl ⟨INITIAL_SUBLIST_TRANS hwl.1 hsub, hwl.2⟩⟩

/-- pack3.hl:1727 `BARV_0`. -/
theorem BARV_0 (V : Set V3) (v : V3) (hV : Packing V) (hv : v ∈ V) : barV V 0 [v] := sorry

/-- pack3.hl:1740 `BARV_IMP_K_LE_3`. -/
theorem BARV_IMP_K_LE_3 (V : Set V3) (ul : List V3) (k : ℕ) (hbar : barV V k ul) :
    k ≤ 3 := by
  have h1 := hbar.2 ul ⟨INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩
  have h2 := h1.1
  have h3 := hbar.1
  omega

/-- pack3.hl:1749 `BARV_IMP_HD_IN_SET_OF_LIST`. -/
theorem BARV_IMP_HD_IN_SET_OF_LIST (V : Set V3) (k : ℕ) (ul : List V3) (hbar : barV V k ul) :
    hdV ul ∈ setOfList ul := by
  have h1 := hbar.1
  exact HD_IN_SET_OF_LIST ul (by omega)

/-- pack3.hl:1760 `TRUNCATE_SIMPLEX_INITIAL_SUBLIST`. -/
theorem TRUNCATE_SIMPLEX_INITIAL_SUBLIST (k : ℕ) (xl zl : List V3) :
    (truncateSimplex k zl = xl ∧ k + 1 ≤ zl.length) ↔
      initialSublist xl zl ∧ xl.length = k + 1 := by
  constructor
  · rintro ⟨heps, hle⟩
    have hw : (truncateSimplex k zl).length = k + 1 ∧
        initialSublist (truncateSimplex k zl) zl :=
      Classical.epsilon_spec
        (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
        ⟨zl.take (k + 1), List.length_take_of_le (by omega),
          ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
    rw [heps] at hw
    exact ⟨hw.2, hw.1⟩
  · rintro ⟨hinit, hlen⟩
    have hle2 := INITIAL_SUBLIST_LENGTH_LE hinit
    have hw : (truncateSimplex k zl).length = k + 1 ∧
        initialSublist (truncateSimplex k zl) zl :=
      Classical.epsilon_spec
        (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
        ⟨zl.take (k + 1), List.length_take_of_le (by omega),
          ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
    refine ⟨(INITIAL_SUBLIST_UNIQUE hinit hw.2 hlen hw.1).symm, by omega⟩

/-- pack3.hl:1777 `TRUNCATE_SIMPLEX_BARV`. -/
theorem TRUNCATE_SIMPLEX_BARV (V : Set V3) (r k : ℕ) (zl : List V3) (hbar : barV V k zl)
    (hr : r ≤ k) : barV V r (truncateSimplex r zl) := by
  have hbl := hbar.1
  have h1 := trunc_init_len r zl (by omega)
  have hb := BARV_INITIAL_SUBLIST V k zl (truncateSimplex r zl) hbar h1.1 (by omega)
  rw [h1.2] at hb
  simpa using hb

/-- pack3.hl:1792 `TRUNCATE_SIMPLEX_REFL`. -/
theorem TRUNCATE_SIMPLEX_REFL (k : ℕ) (ul : List V3) (h : ul.length = k + 1) :
    truncateSimplex k ul = ul := by
  have heps : (truncateSimplex k ul).length = k + 1 ∧ initialSublist (truncateSimplex k ul) ul :=
    Classical.epsilon_spec (p := fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl ul)
      ⟨ul, h, INITIAL_SUBLIST_REFL ul⟩
  exact INITIAL_SUBLIST_UNIQUE heps.2 (INITIAL_SUBLIST_REFL ul) heps.1 h

/-- pack3.hl:1799 `TRUNCATE_0_EQ_HEAD`. -/
theorem TRUNCATE_0_EQ_HEAD (ul : List V3) (h : 1 ≤ ul.length) :
    truncateSimplex 0 ul = [hdV ul] := by
  have hw : (truncateSimplex 0 ul).length = 0 + 1 ∧
      initialSublist (truncateSimplex 0 ul) ul :=
    Classical.epsilon_spec (p := fun vl : List V3 => vl.length = 0 + 1 ∧ initialSublist vl ul)
      ⟨[hdV ul], rfl, INITIAL_SUBLIST_HD ul h⟩
  have h1 := trunc_init_len 0 ul h
  exact INITIAL_SUBLIST_UNIQUE h1.1 (INITIAL_SUBLIST_HD ul h) hw.1 rfl

/-- pack3.hl:1807 `LENGTH_TRUNCATE_SIMPLEX`. -/
theorem LENGTH_TRUNCATE_SIMPLEX (k : ℕ) (ul : List V3) (h : k + 1 ≤ ul.length) :
    (truncateSimplex k ul).length = k + 1 := (trunc_init_len k ul h).2

/-- pack3.hl:1814 `TRUNCATE_SIMPLEX_EQ_BUTLAST`. -/
theorem TRUNCATE_SIMPLEX_EQ_BUTLAST (ul : List V3) (h : 2 ≤ ul.length) :
    truncateSimplex (ul.length - 2) ul = ul.dropLast := by
  have h1 := trunc_init_len (ul.length - 2) ul (by omega)
  have h2 : initialSublist ul.dropLast ul := BUTLAST_INITIAL_SUBLIST ul (by omega)
  have h3 := LENGTH_BUTLAST ul (by omega)
  have h3' : ul.dropLast.length = (ul.length - 2) + 1 := by omega
  exact INITIAL_SUBLIST_UNIQUE h1.1 h2 h1.2 h3'

/-- pack3.hl:1822 `HD_TRUNCATE_SIMPLEX`. -/
theorem HD_TRUNCATE_SIMPLEX (ul : List V3) (j : ℕ) (h : j + 1 ≤ ul.length) :
    hdV (truncateSimplex j ul) = hdV ul := by
  have h1 := trunc_init_len j ul h
  obtain ⟨yl, hyl⟩ := h1.1
  cases ul with
  | nil => exact absurd h (by simp [List.length_nil])
  | cons a t =>
    cases hs : truncateSimplex j (a :: t) with
    | nil =>
      rw [hs] at h1
      rw [List.length_nil] at h1
      exact absurd h1.2 (by omega)
    | cons b s =>
      rw [hs] at hyl
      injection hyl with e1 _
      simp only [hdV]
      exact e1.symm

/-- pack3.hl:1831 `TRUNCATE_TRUNCATE_SIMPLEX`. -/
theorem TRUNCATE_TRUNCATE_SIMPLEX (ul : List V3) (i j : ℕ) (hij : i ≤ j)
    (h : j + 1 ≤ ul.length) :
    truncateSimplex i (truncateSimplex j ul) = truncateSimplex i ul := by
  have hB := trunc_init_len j ul h
  have hlen : i + 1 ≤ (truncateSimplex j ul).length := by omega
  have hA := trunc_init_len i (truncateSimplex j ul) hlen
  have hC := trunc_init_len i ul (by omega)
  exact INITIAL_SUBLIST_UNIQUE (INITIAL_SUBLIST_TRANS hA.1 hB.1) hC.1 hA.2 hC.2

/-- pack3.hl:1856 `INITIAL_SUBLIST_IMP_TRUNCATE_SIMPLEX`. -/
theorem INITIAL_SUBLIST_IMP_TRUNCATE_SIMPLEX {xl yl : List V3} (h : initialSublist yl xl)
    (hpos : 1 ≤ yl.length) : yl = truncateSimplex (yl.length - 1) xl ∧ yl.length ≤ xl.length := by
  have hle := INITIAL_SUBLIST_LENGTH_LE h
  have h1 := trunc_init_len (yl.length - 1) xl (by omega)
  refine ⟨INITIAL_SUBLIST_UNIQUE h h1.1 (by omega) h1.2, INITIAL_SUBLIST_LENGTH_LE h⟩

/-- pack3.hl:1874 `LIST_EQ_TRUNCATE_SIMPLEX_APPEND_LAST`. -/
theorem LIST_EQ_TRUNCATE_SIMPLEX_APPEND_LAST (ul : List V3) (h : 2 ≤ ul.length) :
    ul = truncateSimplex (ul.length - 2) ul ++ [elV ul (ul.length - 1)] := sorry

/-- pack3.hl:1883 `TRUNCATE_SIMPLEX_ADD1`. -/
theorem TRUNCATE_SIMPLEX_ADD1 (ul : List V3) (k : ℕ) (h : k + 2 ≤ ul.length) :
    truncateSimplex (k + 1) ul =
      truncateSimplex k ul ++ [elV (truncateSimplex (k + 1) ul) (k + 1)] := sorry

/-- pack3.hl:1913 `EL_TRUNCATE_SIMPLEX`. -/
theorem EL_TRUNCATE_SIMPLEX (ul : List V3) (k j : ℕ) (h : k + 1 ≤ ul.length)
    (hj : j ≤ k) : elV (truncateSimplex k ul) j = elV ul j := by
  have h1 := trunc_init_len k ul h
  obtain ⟨yl, hyl⟩ := h1.1
  have hlen : j < (truncateSimplex k ul).length := by omega
  have hlen2 : j < (truncateSimplex k ul ++ yl).length := by
    rw [List.length_append]
    omega
  have hget : elV (truncateSimplex k ul ++ yl) j = elV (truncateSimplex k ul) j := by
    simp only [elV, List.getD_eq_getElem _ (0 : V3) hlen2,
      List.getD_eq_getElem _ (0 : V3) hlen]
    rw [List.getElem_append (l₁ := truncateSimplex k ul) (l₂ := yl) (by omega),
      dif_pos hlen]
  have h2 : elV ul j = elV (truncateSimplex k ul ++ yl) j :=
    congrArg (fun w => elV w j) hyl
  rw [h2, hget]

/-- pack3.hl:1928 `TRUNCATE_SIMPLEX_ADD1_ALT`. -/
theorem TRUNCATE_SIMPLEX_ADD1_ALT (ul : List V3) (k : ℕ) (h : k + 2 ≤ ul.length) :
    truncateSimplex (k + 1) ul = truncateSimplex k ul ++ [elV ul (k + 1)] := by
  have h1 := TRUNCATE_SIMPLEX_ADD1 ul k h
  rw [EL_TRUNCATE_SIMPLEX ul (k + 1) (k + 1) h (by omega)] at h1
  exact h1

/-! ## voronoi_set / voronoi_list (pack3.hl:1956-2158) -/

/-- pack3.hl:1956 `VORONOI_SET_SING`. -/
theorem VORONOI_SET_SING (V : Set V3) (u : V3) :
    voronoiSet V {u} = voronoiClosed V u := by
  ext x
  constructor
  · intro h t ht
    exact h (voronoiClosed V u) ⟨u, rfl, rfl⟩ t ht
  · intro h t ht
    obtain ⟨v, hv, hvt⟩ := ht
    rw [Set.mem_singleton_iff.1 hv] at hvt
    rw [← hvt]
    exact h

/-- pack3.hl:1961 `VORONOI_LIST_SING`. -/
theorem VORONOI_LIST_SING (V : Set V3) (u : V3) :
    voronoiList V [u] = voronoiClosed V u := by
  have hs : setOfList [u] = {u} := by simp [setOfList]
  rw [voronoiList, hs, VORONOI_SET_SING]

/-- pack3.hl:1966 `VORONOI_SET_2`. -/
theorem VORONOI_SET_2 (V : Set V3) (u v : V3) :
    voronoiSet V {u, v} = voronoiClosed V v ∩ voronoiClosed V u := by
  ext x
  constructor
  · intro h
    exact ⟨fun w hw => h _ ⟨v, Or.inr rfl, rfl⟩ w hw,
      fun w hw => h _ ⟨u, Or.inl rfl, rfl⟩ w hw⟩
  · rintro ⟨hv, hu⟩ t ht
    obtain ⟨w, hw, hwe⟩ := ht
    have hw2 : w = u ∨ w = v := by simpa using hw
    rcases hw2 with rfl | rfl
    · rw [← hwe]
      exact hu
    · rw [← hwe]
      exact hv

/-- pack3.hl:1971 `VORONOI_SET_2_BIS`. -/
theorem VORONOI_SET_2_BIS (V : Set V3) (u v : V3) (hu : u ∈ V) (hv : v ∈ V) :
    voronoiSet V {u, v} = voronoiClosed V v ∩ bis u v := by
  rw [VORONOI_SET_2]
  ext x
  simp only [voronoiClosed, bis, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm (h2 v hv) (h1 u hu)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw => le_trans h2.le (h1 w hw)⟩

/-- pack3.hl:1979 `VORONOI_SET_2_BIS_LE`. -/
theorem VORONOI_SET_2_BIS_LE (V : Set V3) (u v : V3) (hu : u ∈ V) (hv : v ∈ V) :
    voronoiSet V {u, v} = voronoiClosed V v ∩ bisLe u v := by
  rw [VORONOI_SET_2]
  ext x
  simp only [voronoiClosed, bisLe, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 v hv⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw => le_trans h2 (h1 w hw)⟩

/-- pack3.hl:1987 `VORONOI_LIST_BIS`. -/
theorem VORONOI_LIST_BIS (V : Set V3) (ul : List V3) (h : V3) (t : List V3)
    (hsub : setOfList ul ⊆ V) (hcons : ul = h :: t) :
    voronoiList V ul = voronoiClosed V h ∩ ⋂₀ ((fun u : V3 => bis h u) '' setOfList t) := sorry

/-- pack3.hl:2068 `LIST_SUBSET`. -/
theorem LIST_SUBSET (V : Set V3) (ul : List V3) (h : V3) (t : List V3)
    (hsub : setOfList ul ⊆ V) (hcons : ul = h :: t) : h ∈ V ∧ setOfList t ⊆ V := by
  refine ⟨hsub ?_, fun u hu => hsub ?_⟩
  · rw [hcons]
    simp only [setOfList, List.mem_cons]
    exact Or.inl rfl
  · rw [hcons]
    simp only [setOfList, List.mem_cons]
    exact Or.inr hu

/-- pack3.hl:2080 `VORONOI_LIST_BIS_LE`. -/
theorem VORONOI_LIST_BIS_LE (V : Set V3) (ul : List V3) (h : V3) (t : List V3)
    (hsub : setOfList ul ⊆ V) (hcons : ul = h :: t) :
    voronoiList V ul = voronoiClosed V h ∩ ⋂₀ ((fun u : V3 => bisLe u h) '' setOfList t) := sorry

/-- pack3.hl:2099 `BOUNDED_VORONOI_LIST`. -/
theorem BOUNDED_VORONOI_LIST (V : Set V3) (k : ℕ) (ul : List V3) (hs : saturated V)
    (hbar : barV V k ul) : Bornology.IsBounded (voronoiList V ul) := by
  have hbl := hbar.1
  refine (Metric.isBounded_ball (x := hdV ul) (r := (2 : ℕ))).subset fun x hx => ?_
  have hmem := hx (voronoiClosed V (hdV ul)) ⟨hdV ul, HD_IN_SET_OF_LIST ul (by omega), rfl⟩
  exact Metric.mem_ball.2 (VORONOI_BALL2 V (hdV ul) hs hmem)

/-- pack3.hl:2115 `VORONOI_LIST_INTER_BIS`. -/
theorem VORONOI_LIST_INTER_BIS (V : Set V3) (ul : List V3) (v : V3) (h : V3) (t : List V3)
    (hsub : setOfList ul ⊆ V) (hv : v ∈ V) (hcons : ul = h :: t) :
    voronoiList V ul ∩ bis h v = voronoiList V (ul ++ [v]) := by
  sorry

/-- pack3.hl:2145 `SUPSET_INTER`. -/
theorem SUPSET_INTER (s t u : Set V3) (h1 : s ⊆ t) (h2 : s = u) : u = t ∩ u := by
  subst h2
  rw [Set.inter_comm]
  exact (Set.inter_eq_self_of_subset_left h1).symm

/-- pack3.hl:2148 `INTER_AFFINE_HULL`. -/
theorem INTER_AFFINE_HULL (s : Set V3) :
    s = ((affineSpan ℝ s : Set V3) ∩ s) := by
  exact (Set.inter_eq_self_of_subset_right (subset_affineSpan ℝ s)).symm

/-! ## Canonical forms, polytope results (pack3.hl:2156-2420) -/

/-- pack3.hl:2207 `lemma1` (`HAS_SIZE n` encoded as `Finite ∧ Nat.card = n`). -/
theorem lemma1 {α : Type*} {f : Set α} (P : Set α → Prop) (hf : f.Finite) (hP : P f) :
    ∃ (n : ℕ) (g : Set α), g ⊆ f ∧ g.Finite ∧ Nat.card ↥g = n ∧ P g :=
  ⟨Nat.card ↥f, f, le_refl _, hf, rfl, hP⟩

/-- pack3.hl:2211 `MINIMAL_INTERS_EXISTS`. -/
theorem MINIMAL_INTERS_EXISTS {α : Type*} (s : Set α) (f : Set (Set α)) (hf : f.Finite)
    (hs : s = ⋂₀ f) : ∃ g ⊆ f, s = ⋂₀ g ∧ ∀ g' ⊂ g, s ⊂ ⋂₀ g' := sorry

/-- pack3.hl:2235 `MINIMAL_INTER_INTERS_EXISTS`. -/
theorem MINIMAL_INTER_INTERS_EXISTS {α : Type*} (s t : Set α) (f : Set (Set α))
    (hf : f.Finite) (hs : s = t ∩ ⋂₀ f) :
    ∃ g ⊆ f, s = t ∩ ⋂₀ g ∧ ∀ g' ⊂ g, s ⊂ t ∩ ⋂₀ g' := sorry

/-- pack3.hl:2260 `VORONOI_LIST_CANONICAL`. -/
theorem VORONOI_LIST_CANONICAL (V : Set V3) (ul : List V3) (h : V3) (t : List V3)
    (hV : Packing V) (hs : saturated V) (hsub : setOfList ul ⊆ V) (hcons : ul = h :: t) :
    ∃ K : Set (Set V3), K.Finite ∧
      voronoiList V ul = ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K) ∧
      (∀ a ∈ K, ∃ v ∈ V, v ≠ h ∧ (a = bisLe v h ∨ a = bisLe h v)) ∧
      (∀ K' ⊂ K, voronoiList V ul ⊂ ((affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K')) := sorry

/-- pack3.hl:2297 `POLYHEDRON_VORONOI_LIST`. -/
theorem POLYHEDRON_VORONOI_LIST (V : Set V3) (ul : List V3) (hV : Packing V)
    (hs : saturated V) (hsub : setOfList ul ⊆ V) : polyhedron (voronoiList V ul) := sorry

/-- pack3.hl:2341 `POLYTOPE_VORONOI_LIST`. -/
theorem POLYTOPE_VORONOI_LIST (V : Set V3) (ul : List V3) (hV : Packing V)
    (hs : saturated V) (hsub : setOfList ul ⊆ V) (hne : ul ≠ []) :
    polytope (voronoiList V ul) := sorry

/-- pack3.hl:2355 `POLYTOPE_VORONOI_LIST_BARV`. -/
theorem POLYTOPE_VORONOI_LIST_BARV (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hs : saturated V) (hbar : barV V k ul) : polytope (voronoiList V ul) := by
  have hbl := hbar.1
  exact POLYTOPE_VORONOI_LIST V ul hV hs (BARV_SUBSET V k ul hbar) (by
    intro h0
    simp [h0] at hbl)

/-- pack3.hl:2370 `CLOSED_VORONOI_LIST`. -/
theorem CLOSED_VORONOI_LIST (V : Set V3) (ul : List V3) : IsClosed (voronoiList V ul) := by
  rw [voronoiList, voronoiSet]
  refine isClosed_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact CLOSED_VORONOI_CLOSED V w

/-- pack3.hl:2380 `CONVEX_VORONOI_LIST`. -/
theorem CONVEX_VORONOI_LIST (V : Set V3) (ul : List V3) : Convex ℝ (voronoiList V ul) := by
  rw [voronoiList, voronoiSet]
  refine convex_sInter ?_
  rintro t ⟨w, -, rfl⟩
  exact CONVEX_VORONOI_CLOSED V w

/-- pack3.hl:2391 `AFF_DIM_VORONOI_LIST`. -/
theorem AFF_DIM_VORONOI_LIST (V : Set V3) (ul : List V3) (k : ℕ) (hbar : barV V k ul) :
    affDim (voronoiList V ul) = 3 - k := by
  have h1 := hbar.1
  have h3 := (hbar.2 ul ⟨INITIAL_SUBLIST_REFL ul, by simp [hbar.1]⟩).2.2
  omega

/-- pack3.hl:2399 `VORONOI_LIST_SUBSET_VORONOI_CLOSED`. -/
theorem VORONOI_LIST_SUBSET_VORONOI_CLOSED (V : Set V3) (vl : List V3) (h : 1 ≤ vl.length) :
    voronoiList V vl ⊆ voronoiClosed V (hdV vl) := by
  intro x hx
  exact hx _ ⟨hdV vl, HD_IN_SET_OF_LIST vl h, rfl⟩

/-! ## omega_list (pack3.hl:2423-2529) -/

/-- pack3.hl:2423 `OMEGA_LIST_N_LEMMA`. -/
theorem OMEGA_LIST_N_LEMMA (V : Set V3) (ul : List V3) (k i : ℕ)
    (h : k + i + 1 ≤ ul.length) :
    omegaListN V ul k = omegaListN V (truncateSimplex (k + i) ul) k := sorry

/-- pack3.hl:2441 `OMEGA_LIST_LEMMA`. -/
theorem OMEGA_LIST_LEMMA (V : Set V3) (ul : List V3) (k : ℕ) (h : k + 1 ≤ ul.length) :
    omegaList V (truncateSimplex k ul) = omegaListN V ul k := by
  have hlen := trunc_init_len k ul h
  rw [omegaList, hlen.2, Nat.add_sub_cancel, OMEGA_LIST_N_LEMMA V ul k 0 h, Nat.add_zero]

/-- pack3.hl:2451 `BARV_IMP_VORONOI_LIST_NOT_EMPTY`. -/
theorem BARV_IMP_VORONOI_LIST_NOT_EMPTY (V : Set V3) (ul : List V3) (k : ℕ)
    (hbar : barV V k ul) : voronoiList V ul ≠ ∅ := sorry

/-- pack3.hl:2472 `OMEGA_LIST_N_IN_VORONOI_LIST`. -/
theorem OMEGA_LIST_N_IN_VORONOI_LIST (V : Set V3) (ul : List V3) (k i : ℕ)
    (hbar : barV V k ul) (hi : i ≤ k) :
    omegaListN V ul i ∈ voronoiList V (truncateSimplex i ul) := sorry

/-- pack3.hl:2507 `OMEGA_LIST_IN_VORONOI_LIST`. -/
theorem OMEGA_LIST_IN_VORONOI_LIST (V : Set V3) (ul : List V3) (k : ℕ)
    (hbar : barV V k ul) : omegaList V ul ∈ voronoiList V ul := sorry

end Kepler.Text
