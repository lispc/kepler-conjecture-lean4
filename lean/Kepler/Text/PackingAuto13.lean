/-
Packing chapter, URRPHBZ2 lane: the Marchal cells are eventually radial at
packing points, plus the SLTSTLO covering theorems and the DDZUPHJ cell
rigidity theorem.

HOL sources (Flyspeck `scripts/packing/`, module authors VU KHAC KY):
- `URRPHBZ2.hl` (972 lines, 6 `prove` items, needs `marchal_cells_2.hl`):
  the eventually-radial kit `EVENTUALLY_RADIAL_RCONE_GE_ABC_A/B`,
  `OPEN_RCONE_GT` (multivariate/flyspeck.hl), `EVENTUALLY_RADIAL_AFF_GE`,
  `FUN_AFFINE_KLEMMA`, and the capstone `URRPHBZ2`.
- `SLTSTLO.hl` (3692 lines, 3 `prove` items): `NULLSET_SPHERE` and the
  covering capstones `SLTSTLO1` / `SLTSTLO2` (heavy internal NEW_GOAL
  chains, not named lemmas).
- `DDZUPHJ.hl` (611 lines, 2 `prove` items): `RCONE_GT_EQ_EMPTY_LEMMA` and
  the cell-rigidity capstone `DDZUPHJ`.

## Eventually-radial / limit machinery (encoding notes)

- HOL `eventually_radial x C` (sphere.hl:452) ↔ `EventuallyRadial x C`
  (Kepler/Geom/Volume.lean:32): `∃ r > 0, C ∩ ball x r is radial from x`,
  where `radial_norm r x C` keeps `x + t • u` in `C` for every `t ∈ (0,1)`
  scaling with `t ‖u‖ < r`. The cell measure work (URRPHBZ1-3) needs each
  cell to be `EventuallyRadial` at its `V`-points; near `v ∈ V` the cell is
  a cone over finitely many tangent directions, so the limit `vol / r³`
  exists — the limit machinery of Kepler.Geom.Volume (`sol`) consumes
  exactly this.
- HOL `rcone_ge`/`rcone_gt` ↔ `rconeGe`/`rconeGt` (PackingAuto2, the
  `rconesgn`-style inequalities); `aff_ge` ↔ `affGe` (Kepler/Geom/Aff.lean:
  `Affsign (0 ≤ ·)` — coefficients on the SECOND set are `≥ 0`, sum 1);
  `NULLSET` ↔ `nullSet` (`volume X = 0`); `aff_dim` ↔ `affDim`
  (Polytope.lean); `norm` ↔ `‖·‖`; `dist` ↔ `dist`.
- Marchal2 lemmas are NOT importable (parallel-owned Auto12): the Auto11
  private copies (`mcellExplicit`, `mxiExplicit`, `simplexFurthestLt2`,
  `rogersInterVLemma`) are private and hence NOT visible here — any
  consumer of URRPHBZ2's proof needs its own copies. NEEDS markers below
  list every marchal2 lemma per sorried capstone.
- IMPORT SCOPE: only Auto2/Auto5-8/Polytope (oleans present at write time;
  the Auto9/Auto10/Auto11 oleans are produced by parallel lanes and were
  not yet on disk). Their contents (`TEZFFSK`, `NJIUTIU`, `URRPHBZ1`,
  `RVFXZBU`, `LEPJBDJ`) are referenced by NAME in docstrings only; add
  `import Kepler.Text.PackingAuto9/10/11` when the oleans land.
- DISCHARGES convention: `URRPHBZ2` / `SLTSTLO1` / `SLTSTLO2` match the
  `sorry`-bodied interfaces `Kepler.Text.PackingAuto2.URRPHBZ2_concl` /
  `SLTSTLO1_concl` / `SLTSTLO2_concl` verbatim; at merge time the interface
  bodies become `exact URRPHBZ2` etc. `DDZUPHJ` has NO pack_concl interface
  (its statement is fresh; it consumes Auto9's `TEZFFSK`/`NJIUTIU` in HL).
- Proved honestly here: `EVENTUALLY_RADIAL_RCONE_GE_ABC_A/B`,
  `OPEN_RCONE_GT`, `EVENTUALLY_RADIAL_AFF_GE`, `NULLSET_SPHERE` (via
  Mathlib `MeasureTheory.addHaar_sphere`), `RCONE_GT_EQ_EMPTY_LEMMA`.
  Sorried (faithful statements + HL line references): `FUN_AFFINE_KLEMMA`,
  `URRPHBZ2`, `SLTSTLO1`, `SLTSTLO2`, `DDZUPHJ`.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## URRPHBZ2.hl: the eventually-radial kit -/

/-- HOL `EVENTUALLY_RADIAL_RCONE_GE_ABC_A` (URRPHBZ2.hl:30): a closed
radial cone at its apex `u0` is eventually radial (radius `1`; the cone
inequality is homogeneous: `t * (u ⬝ d) ≥ t * (‖u‖ * dist u1 u0 * a)`). -/
theorem EVENTUALLY_RADIAL_RCONE_GE_ABC_A (a : ℝ) (u0 u1 : V3) :
    EventuallyRadial u0 (rconeGe u0 u1 a) := by
  refine ⟨1, by norm_num, Set.inter_subset_right, fun u hu t ht htn => ?_⟩
  have hd : u ⬝ᵥ (u1 - u0) ≥ ‖u‖ * dist u1 u0 * a := by
    have h1 := hu.1
    simp only [rconeGe, Set.mem_setOf_eq, add_sub_cancel_left, dist_eq_norm,
      add_sub_cancel_left] at h1
    exact h1
  refine ⟨?_, ?_⟩
  · simp only [rconeGe, Set.mem_setOf_eq]
    rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, ← inner_eq_dot, real_inner_smul_left,
      inner_eq_dot]
    rw [ge_iff_le]
    calc t * ‖u‖ * dist u1 u0 * a = t * (‖u‖ * dist u1 u0 * a) := by ring
      _ ≤ t * (u ⬝ᵥ (u1 - u0)) := mul_le_mul_of_nonneg_left hd ht.le
  · simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htn

/-- Continuity of the `rcone` defining functional (copy of the Auto10
private pattern; `inner`-form continuity from `continuous_id.sub`
+ `Continuous.inner`). -/
private theorem continuousDotP13 (v w : V3) :
    Continuous fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
  have h : Continuous fun x : V3 => inner ℝ (x - v) (w - v) :=
    (continuous_id.sub continuous_const).inner continuous_const
  have heq : (fun x : V3 => inner ℝ (x - v) (w - v)) =
      fun x : V3 => (x - v) ⬝ᵥ (w - v) := by
    funext x
    exact inner_eq_dot (x - v) (w - v)
  rw [← heq]
  exact h

/-- HOL `OPEN_RCONE_GT` (URRPHBZ2.hl:54, John Harrison): the strict radial
cone is open — the preimage of `(0, ∞)` under the continuous functional
`x ↦ (x - v0) ⬝ (v1 - v0) - dist x v0 * dist v1 v0 * a`. -/
theorem OPEN_RCONE_GT (v0 v1 : V3) (a : ℝ) : IsOpen (rconeGt v0 v1 a) := by
  have hcont : Continuous fun x : V3 =>
      (x - v0) ⬝ᵥ (v1 - v0) - (dist x v0 * dist v1 v0 * a) :=
    (continuousDotP13 v0 v1).sub (by fun_prop)
  have hset : rconeGt v0 v1 a =
      (fun x : V3 => (x - v0) ⬝ᵥ (v1 - v0) - (dist x v0 * dist v1 v0 * a)) ⁻¹'
        (Set.Ioi 0) := by
    ext x
    simp only [rconeGt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, sub_pos]
  rw [hset]
  exact isOpen_Ioi.preimage hcont

/-- HOL `EVENTUALLY_RADIAL_RCONE_GE_ABC_B` (URRPHBZ2.hl:71): for `u0 ≠ u1`
and `0 < a < 1`, the tip `u1` lies strictly inside the cone
(`(1 - a) ‖u1 - u0‖² > 0`), so a small ball around `u1` sits in `rcone_gt`
(openness) and hence in `rcone_ge`; the ball is radial. -/
theorem EVENTUALLY_RADIAL_RCONE_GE_ABC_B (a : ℝ) (u0 u1 : V3) (hu01 : u0 ≠ u1)
    (_ha1 : 0 < a) (ha2 : a < 1) : EventuallyRadial u1 (rconeGe u0 u1 a) := by
  have hnpos : 0 < ‖u1 - u0‖ := norm_sub_pos_iff.mpr hu01.symm
  have hsqpos : 0 < ‖u1 - u0‖ ^ 2 := pow_pos hnpos 2
  have hmem : u1 ∈ rconeGt u0 u1 a := by
    simp only [rconeGt, Set.mem_setOf_eq]
    have h1 : inner ℝ (u1 - u0) (u1 - u0) = (u1 - u0) ⬝ᵥ (u1 - u0) :=
      inner_eq_dot (u1 - u0) (u1 - u0)
    rw [← h1, real_inner_self_eq_norm_sq, dist_eq_norm]
    have hring : ‖u1 - u0‖ ^ 2 - a * ‖u1 - u0‖ ^ 2 = (1 - a) * ‖u1 - u0‖ ^ 2 := by ring
    have hp : 0 < (1 - a) * ‖u1 - u0‖ ^ 2 :=
      mul_pos (by linarith) hsqpos
    linarith
  obtain ⟨e, he0, hball⟩ := Metric.isOpen_iff.mp (OPEN_RCONE_GT u0 u1 a) u1 hmem
  refine ⟨e, he0, Set.inter_subset_right, fun u hu t ht htn => ?_⟩
  have hsmul : dist (u1 + t • u) u1 = t * ‖u‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hinball : u1 + t • u ∈ Metric.ball u1 e := by
    rw [Metric.mem_ball, hsmul]
    exact htn
  refine ⟨?_, by rw [Metric.mem_ball, hsmul]; exact htn⟩
  show (u1 + t • u - u0) ⬝ᵥ (u1 - u0) ≥ dist (u1 + t • u) u0 * dist u1 u0 * a
  have hmem' : u1 + t • u ∈ rconeGt u0 u1 a := hball hinball
  have hgt : (u1 + t • u - u0) ⬝ᵥ (u1 - u0) >
      dist (u1 + t • u) u0 * dist u1 u0 * a := hmem'
  exact le_of_lt hgt

/-- HOL `EVENTUALLY_RADIAL_AFF_GE` (URRPHBZ2.hl:114): the affine cone
`aff_ge {a,b} {c,d}` (disjoint pairs) is eventually radial at its apex-side
point `a`. HL uses `AFF_GE_2_2`; here we manipulate the `Affsign` witness
directly: if `a + u = ∑ f w • w` (`∑ f = 1`, `f ≥ 0` on `{c,d}`) then scaling
every coefficient of the non-`a` part by `t` rescales `a + u` radially from
`a` while preserving the `aff_ge` certificate. -/
theorem EVENTUALLY_RADIAL_AFF_GE (a b c d : V3)
    (hdis : Disjoint ({a, b} : Set V3) ({c, d} : Set V3)) :
    EventuallyRadial a (affGe {a, b} {c, d}) := by
  refine ⟨1, by norm_num, Set.inter_subset_right, fun u hu t ht htn => ?_⟩
  obtain ⟨f, hfin, hsum, hge, hone⟩ := hu.1
  have hSa : a ∈ hfin.toFinset := by simp
  have hna : ¬a ∈ ({c, d} : Set V3) :=
    fun ha' => Set.disjoint_left.mp hdis (by simp) ha'
  have hne : ∀ w ∈ ({c, d} : Set V3), w ≠ a := by
    intro w hw hweq
    exact hna (by rw [← hweq]; exact hw)
  have hball : dist (a + t • u) a < 1 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    linarith
  refine ⟨⟨fun w => (if w = a then (1 - t : ℝ) else 0) + t * f w, hfin, ?_, ?_, ?_⟩,
    hball⟩
  · have expand : (∑ w ∈ hfin.toFinset,
        ((if w = a then (1 - t : ℝ) else 0) + t * f w) • w : V3) =
        (1 - t) • a + t • (a + u) := by
      rw [Finset.sum_congr rfl fun w _ =>
        show ((if w = a then (1 - t : ℝ) else 0) + t * f w) • w
            = (if w = a then (1 - t : ℝ) else 0) • w + (t * f w) • w from
          add_smul _ _ _, Finset.sum_add_distrib]
      congr 1
      · simp [ite_smul, zero_smul]
      · have h1 : ∀ w ∈ hfin.toFinset, ((t * f w) • w : V3) = t • (f w • w) :=
          fun w _ => (smul_smul t (f w) w).symm
        rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, hsum]
    rw [expand]
    module
  · intro w hw
    show 0 ≤ (if w = a then (1 - t : ℝ) else 0) + t * f w
    rw [if_neg (hne w hw)]
    simpa using mul_nonneg ht.le (hge w hw)
  · show ∑ w ∈ hfin.toFinset,
      ((if w = a then (1 - t : ℝ) else 0) + t * f w) = 1
    rw [Finset.sum_add_distrib]
    have h2 : (∑ w ∈ hfin.toFinset, t * f w : ℝ) =
        t * ∑ w ∈ hfin.toFinset, f w := by
      rw [Finset.mul_sum]
    rw [h2, hone,
      Finset.sum_ite_eq' hfin.toFinset a (fun _ => (1 - t : ℝ))]
    rw [if_pos hSa]
    ring

/-! ## URRPHBZ2.hl: the two giant statements -/

/-- GIANT (URRPHBZ2.hl:146-206, `FUN_AFFINE_KLEMMA`): with `{a,b,c}` a
2-dimensional simplex and `d` off its affine hull, `a` is not in the hull of
`{b,c,d}`. Proof sketch (HL expands `CONVEX_HULL_3`/`AFFINE_HULL_3` and
solves the coefficient algebra): if `a ∈ convex hull {b,c,d}` then
`a ∈ affineSpan {b,c,d}`, so `affineSpan {a,b,c} ≤ affineSpan {b,c,d}`;
both directions have dimension `2` (Cauchy bounds via `AFF_DIM_LE_CARD`),
so the two affine hulls coincide and `d` lies in `affineSpan {a,b,c}` —
contradiction.

NEEDS: port of the Mathlib affine-exchange argument
(`vectorSpan` monotonicity + `finrank` equality of nested subspaces). -/
theorem FUN_AFFINE_KLEMMA (a b c d : V3) (h1 : affDim {a, b, c} = 2)
    (h2 : d ∉ (affineSpan ℝ {a, b, c} : Set V3)) :
    a ∉ convexHull ℝ {b, c, d} := by
  sorry

/-- GIANT — HOL `URRPHBZ2` (URRPHBZ2.hl:215-972; concl
`pack_concl.hl:176-178`): Marchal cells are eventually radial at packing
points.

DISCHARGES: PackingAuto2.URRPHBZ2_concl (PackingAuto2.lean:788; the `sorry`
body is to be replaced by `exact URRPHBZ2` at merge time).

Proof architecture (HL). After `BARV_3_EXPLICIT` splits `ul` into
`[u0;u1;u2;u3]`: points outside the (closed, NEEDS `CLOSED_MCELL`) cell are
handled by NEEDS `EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET`; then per index:
`k = 0` — `v = u0` by NEEDS `ROGERS_INTER_V_LEMMA` (Auto11 private sorry)
and `v ∉ mcell0` anyway; `k = 1` — the cell is a triple intersection
(rogers — NEEDS `EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1` with
NEEDS `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS`; cball — radial with radius 1;
cone complement — homogeneity, exactly `EVENTUALLY_RADIAL_RCONE_GE_ABC_A`
with apex-side scaling), combined by NEEDS `EVENTUALLY_RADIAL_INTER`;
`k = 2` — mutual `rcone_ge`s at `v` on the edge (cone homogeneity again) +
`aff_ge` wedge (`EVENTUALLY_RADIAL_AFF_GE` above); `k = 3`/`k ≥ 4` —
`v ∈ {u0,u1,u2}` resp. `v ∈ {u0,u1,u2,u3}` via LEPJBDJ (Auto11) +
NEEDS `SIMPLEX_FURTHEST_LT_2` (Auto11 private sorry) and Voronoi-list
membership `OMEGA_LIST_IN_VORONOI_LIST`; each vertex case applies
NEEDS `EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1` with full-dimensionality
`MHFTTZN1` (Rogers) and NEEDS `MXI_EXPLICIT` (Auto11 private sorry);
empty cells by NEEDS `EVENTUALLY_RADIAL_EMPTY`. -/
theorem URRPHBZ2 (V : Set V3) (ul : List V3) (k : ℕ) (v : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hv : v ∈ V) :
    EventuallyRadial v (mcell k V ul) := by
  sorry

/-! ## SLTSTLO.hl -/

/-- HOL `NULLSET_SPHERE` (SLTSTLO.hl:31-38): a Euclidean sphere `{w | norm
(w - v) = r}` is a null set. HL cites `NEGLIGIBLE_SPHERE`; here Mathlib's
`MeasureTheory.addHaar_sphere` (`spheres have zero Haar measure`,
EqHaar.lean) does the work. -/
theorem NULLSET_SPHERE (P : Set V3)
    (h : ∃ v : V3, ∃ r : ℝ, 0 < r ∧ P = {w : V3 | ‖w - v‖ = r}) :
    nullSet P := by
  obtain ⟨v, r, hr, hP⟩ := h
  subst hP
  have hset : {w : V3 | ‖w - v‖ = r} = Metric.sphere v r := by
    ext w
    simp
  rw [hset]
  exact MeasureTheory.Measure.addHaar_sphere (μ := volume) v r

/-! ## DDZUPHJ.hl -/

/-- HOL `RCONE_GT_EQ_EMPTY_LEMMA` (DDZUPHJ.hl:38-52): for `r ≥ 1` the strict
cone `rcone_gt a b r` is empty — Cauchy–Schwarz caps the defining dot
product at `‖x - a‖ * ‖b - a‖ ≤ ‖x - a‖ * ‖b - a‖ * r`. -/
theorem RCONE_GT_EQ_EMPTY_LEMMA (a b : V3) (r : ℝ) (hr : 1 ≤ r) :
    rconeGt a b r = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  simp only [rconeGt, Set.mem_setOf_eq] at hx
  have hcs : |(x - a) ⬝ᵥ (b - a)| ≤ ‖x - a‖ * ‖b - a‖ := by
    rw [← inner_eq_dot]
    exact abs_real_inner_le_norm (x - a) (b - a)
  have hAle : 0 ≤ ‖x - a‖ * ‖b - a‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hchain : (x - a) ⬝ᵥ (b - a) ≤ ‖x - a‖ * ‖b - a‖ * r := by
    calc (x - a) ⬝ᵥ (b - a) ≤ |(x - a) ⬝ᵥ (b - a)| := le_abs_self _
      _ ≤ ‖x - a‖ * ‖b - a‖ := hcs
      _ ≤ ‖x - a‖ * ‖b - a‖ * r := by
          simpa using mul_le_mul_of_nonneg_left hr hAle
  exact absurd hx (not_lt.mpr hchain)

/-! ## SLTSTLO.hl: the two covering giants -/

/-- GIANT — HOL `SLTSTLO1` (SLTSTLO.hl:43-580; concl `pack_concl.hl:135`):
the Rogers simplex is covered by the Marchal cells `mcell 0..4`.

DISCHARGES: PackingAuto2.SLTSTLO1_concl (PackingAuto2.lean:729).

Proof architecture (HL, a single refinement script with NEW_GOAL chains,
no named sub-lemmas). Case `hl ul < sqrt 2`: `mcell 4 = convex hull
(set_of_list ul)`, expanded via NEEDS `WQPRRDY` (the hull is the union of
the six `rogers V (left_action_list p ul)` over `p permutes 0..3`), so
`p ∈ rogers V ul` lands in `mcell 4`. Case `sqrt 2 <= hl ul`: split
`dist (u0, p)` against `sqrt 2` — far points land in `mcell 0` (the
annular sliver); near points are graded by NEEDS `XNHPWAB1/3/4` and
NEEDS `IN_AFFINE_KY_LEMMA1` (the `aff_ge`/`rcone` membership algebra),
NEEDS `MHFTTZN4`/`ROGERS_EXPLICIT` (face structure), NEEDS
`SIMPLEX_FURTHEST_LE` + NEEDS `MXI_EXPLICIT_OLD` (the `mxi` exclusions)
into `mcell 1` / `mcell 2` / `mcell 3`, with `PYTHAGORAS` /
`PARALLEL_PROJECTION` / `BETWEEN_TRANS` for the edge-geometry steps and
`MCELL_EXPLICIT` (Auto11 private) dispatch. -/
theorem SLTSTLO1 (V : Set V3) (ul : List V3) (p : V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hpr : p ∈ rogers V ul) :
    ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul := by
  sorry

/-- GIANT — HOL `SLTSTLO2` (SLTSTLO.hl:582-3692; concl
`pack_concl.hl:138`): away from an explicit null set `Z` the covering of
the Rogers simplex by `mcell 0..4` is unique.

DISCHARGES: PackingAuto2.SLTSTLO2_concl (PackingAuto2.lean:736).

Proof architecture (HL). The witness is the union `Z = B1 ∪ … ∪ B7` of
seven boundary surfaces of `ul`'s data: `B1 = frontier (rogers V ul)`
(NEEDS `NULLSET_SPHERE`-style frontier/null arguments, `NEGLIGIBLE_UNION`
for the finite union — the sphere piece is `NULLSET_SPHERE` above),
`B2 = {w | norm (w - HD ul) = sqrt 2}` (the `mcell0`/`mcell1` interface,
null by `NULLSET_SPHERE`), `B3 = rcone_eq (HD ul) (HD (TL ul))
(hl (truncate_simplex 1 ul) / sqrt 2)` (the `mcell1`/`mcell2` cone
interface; null as a surface via NEEDS `TRANSLATE_AFFINE_KY_LEMMA1`),
`B4/B6` = affine hulls through `HD ul`-based triples (null: images of
lower-dimensional flats, NEEDS `IN_AFFINE_KY_LEMMA1`),
`B5 = convex hull {omega_list_n V ul 2, omega_list_n V ul 3}` and
`B7 = affine hull {omega_list_n V ul 1, 2, 3}` (the `mcell3`/`mcell4`
interfaces). Off `Z`, double membership `p ∈ mcell i V ul ∩ mcell j V vl`
(`i ≠ j`, `i,j ≤ 4`) is killed by RVFXZBU1 (Auto10; its proof consumes
NEEDS `XNHPWAB3/4` case algebra per index pair), giving the `∃!`. -/
theorem SLTSTLO2 (V : Set V3) (ul : List V3) :
    ∃ Z : Set V3, ∀ p : V3, saturated V → Packing V → barV V 3 ul →
      nullSet Z ∧ (p ∈ rogers V ul \ Z → ∃! i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul) := by
  sorry

/-! ## DDZUPHJ.hl: the capstone -/

/-- GIANT — HOL `DDZUPHJ` (DDZUPHJ.hl:59-608; concl DDZUPHJ.hl:29-34): two
`barV V 3` lists with the same full-dimensional Rogers simplex carry the
same Marchal cell of every index `k ∈ {0..4}` with nonempty `mcell k V ul`.
(HOL `k IN {0,1,2,3,4}` rendered as `k ≤ 4`.) No pack_concl interface
exists for this statement; it consumes Auto9's `TEZFFSK`/`NJIUTIU`.

Proof architecture (HL, case `k = 4,3,2,1,0`). `k = 4`: nonemptiness gives
`hl ul < sqrt 2`, so `truncate_simplex 3 ul = ul = vl` by `TEZFFSK`
(Auto9). `k = 3,2,1`: nonemptiness gives the circumradius regime
(`hl (truncate_simplex (k-1) ul) < sqrt 2`, `sqrt 2 <= hl ul`); the omega
chains agree by `NJIUTIU` (Auto9), `truncate_simplex (k-1) ul` =
`truncate_simplex (k-1) vl` by `TEZFFSK`, `mxi V ul = mxi V vl` via
`WAUFCHE1/2` (`hl ≤ dist (omega_list, HD)`), `HD_TRUNCATE_SIMPLEX` and
`OMEGA_LIST_LEMMA`; `mcell1` additionally needs
`HD ul = HD vl` (via NEEDS `ROGERS_INTER_V_LEMMA`, Auto11 private sorry,
on the shared Rogers simplex) and the `k = 1` tail case discharges the
`rcone_gt` factor by `RCONE_GT_EQ_EMPTY_LEMMA` above once
`1 ≤ hl (truncate_simplex 1 ·) / sqrt 2`; `k = 2` identifies
`{u0,u1} = {v0,v1}` from the shared truncation (NEEDS
`BARV_IMP_LENGTH_EQ_CARD` + `TRUNCATE_SIMPLEX_BARV`). `k = 0`: the cells
are the shared Rogers simplex minus the same ball. Cell definitions
dispatch via `MCELL_EXPLICIT` (Auto11 private `mcellExplicit`). -/
theorem DDZUPHJ (V : Set V3) (ul vl : List V3) (k : ℕ)
    (hs : saturated V) (hp : Packing V) (hk : k ≤ 4)
    (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
    (hne : mcell k V ul ≠ ∅) :
    mcell k V ul = mcell k V vl := by
  sorry

end Kepler.Text
