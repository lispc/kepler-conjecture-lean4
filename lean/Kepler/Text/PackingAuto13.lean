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
- UPDATE 2026-09-30 (SLTSTLO1 lane): `import Kepler.Text.PackingAuto12`
  added — Auto12's proved public marchal2 kit (`MCELL_EXPLICIT`,
  `ROGERS_EXPLICIT`, `MXI_EXPLICIT_OLD`, `OMEGA_LIST_1_EXPLICIT_NEW`,
  `CONVEX_HULL_4`/`CONVEX_HULL_4_IMP_2_2`/`CONVEX_HULL_4_SUBSET_AFF_GE_2_2`,
  `RCONE_GT_SUBSET_RCONE_GE`, `BARV_IMP_HL_1_POS_LT`,
  `RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE`) is importable, acyclic
  (Auto12 imports Auto2/5-8/10/11, not Auto13; no name collisions with any
  declaration in this repo). Auto7's sorry-backed `XNHPWAB2` /
  `OMEGA_LIST_N_IN_CONVEX_HULL` are consumed with NEEDS markers at the
  `SLTSTLO1` use sites.
- DISCHARGES convention: `URRPHBZ2` / `SLTSTLO1` / `SLTSTLO2` match the
  `sorry`-bodied interfaces `Kepler.Text.PackingAuto2.URRPHBZ2_concl` /
  `SLTSTLO1_concl` / `SLTSTLO2_concl` verbatim; at merge time the interface
  bodies become `exact URRPHBZ2` etc. `DDZUPHJ` has NO pack_concl interface
  (its statement is fresh; it consumes Auto9's `TEZFFSK`/`NJIUTIU` in HL).
- Proved honestly here: `EVENTUALLY_RADIAL_RCONE_GE_ABC_A/B`,
  `OPEN_RCONE_GT`, `EVENTUALLY_RADIAL_AFF_GE`, `NULLSET_SPHERE` (via
  Mathlib `MeasureTheory.addHaar_sphere`), `RCONE_GT_EQ_EMPTY_LEMMA`,
  and the two private `SLTSTLO1` helpers (`p13_barV_hd_ne`,
  `p13_hull_break4`).
- CLOSED 2026-09-30: `SLTSTLO1` (real proof body; NEEDS five sorry-backed
  upstream lemmas, all named in its docstring: Auto7 `XNHPWAB2` /
  `OMEGA_LIST_N_IN_CONVEX_HULL`, Auto12 `OMEGA_LIST_1_EXPLICIT_NEW` →
  `XNHPWAB1_concl`, Auto12 `MXI_EXPLICIT_OLD` → `MXI_EXISTS_concl`,
  Auto12 `RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE`).
  Sorried (faithful statements + HL line references): `FUN_AFFINE_KLEMMA`,
  `URRPHBZ2`, `SLTSTLO2`, `DDZUPHJ`.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto12
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
  intro ha
  have hac : a ∈ (affineSpan ℝ {b, c, d} : Set V3) :=
    convexHull_subset_affineSpan ({b, c, d} : Set V3) ha
  have hbc : (b : V3) ∈ (affineSpan ℝ {b, c, d} : Set V3) :=
    subset_affineSpan ℝ _ (Set.mem_insert b {c, d})
  have hcc : (c : V3) ∈ (affineSpan ℝ {b, c, d} : Set V3) :=
    subset_affineSpan ℝ _
      (Set.mem_insert_of_mem b (Set.mem_insert c {d}))
  have hsub : ({a, b, c} : Set V3) ⊆ (affineSpan ℝ {b, c, d} : Set V3) := by
    intros x hx
    rcases hx with rfl | rfl | rfl
    · exact hac
    · exact hbc
    · exact hcc
  have hle : affineSpan ℝ {a, b, c} ≤ affineSpan ℝ {b, c, d} :=
    affineSpan_le.2 hsub
  have hdirle : (affineSpan ℝ {a, b, c}).direction ≤
      (affineSpan ℝ {b, c, d}).direction := AffineSubspace.direction_le hle
  rw [direction_affineSpan, direction_affineSpan] at hdirle
  have hvs : vectorSpan ℝ {a, b, c} = vectorSpan ℝ {b, c, d} := by
    refine Submodule.eq_of_le_of_finrank_le hdirle ?_
    have h2le : (Module.finrank ℝ (vectorSpan ℝ {b, c, d}) : ℤ) ≤ 2 := by
      have hgen : vectorSpan ℝ {b, c, d} ≤
          Submodule.span ℝ ({c - b, d - b} : Set V3) := by
        rw [vectorSpan_def]
        refine Submodule.span_le.2 ?_
        intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.1 hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with hxe | hxe | hxe <;> rcases hy with hye | hye | hye
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨0, 0,
            show (0:ℝ) • (c - b) + (0:ℝ) • (d - b) = (b - b : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨-1, 0,
            show (-1:ℝ) • (c - b) + (0:ℝ) • (d - b) = (b - c : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨0, -1,
            show (0:ℝ) • (c - b) + (-1:ℝ) • (d - b) = (b - d : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨1, 0,
            show (1:ℝ) • (c - b) + (0:ℝ) • (d - b) = (c - b : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨0, 0,
            show (0:ℝ) • (c - b) + (0:ℝ) • (d - b) = (c - c : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨1, -1,
            show (1:ℝ) • (c - b) + (-1:ℝ) • (d - b) = (c - d : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨0, 1,
            show (0:ℝ) • (c - b) + (1:ℝ) • (d - b) = (d - b : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨-1, 1,
            show (-1:ℝ) • (c - b) + (1:ℝ) • (d - b) = (d - c : V3) by module⟩
        · rw [hxe, hye]
          exact Submodule.mem_span_pair.2 ⟨0, 0,
            show (0:ℝ) • (c - b) + (0:ℝ) • (d - b) = (d - d : V3) by module⟩
      have hf : ({c - b, d - b} : Set V3).Finite := by
        refine Set.Finite.insert (c - b) ?_
        exact Set.finite_singleton (d - b)
      haveI := hf.to_subtype
      haveI := Fintype.ofFinite (↥({c - b, d - b} : Set V3))
      have hgenrk := Submodule.finrank_mono hgen
      have hcard' : (Module.finrank ℝ (Submodule.span ℝ
          ({c - b, d - b} : Set V3)) : ℤ) ≤ 2 := by
        have hset : (({c - b, d - b} : Finset V3) : Set V3)
            = ({c - b, d - b} : Set V3) := by
          simp [Finset.coe_insert, Finset.coe_singleton]
        have h1 : (Module.finrank ℝ (Submodule.span ℝ
            (({c - b, d - b} : Finset V3) : Set V3)) : ℕ) ≤
            ({c - b, d - b} : Finset V3).card :=
          finrank_span_finset_le_card _
        rw [hset] at h1
        have h2 : ({c - b, d - b} : Finset V3).card ≤ 2 := by
          have hI := Finset.card_insert_le (c - b) ({d - b} : Finset V3)
          simp only [Finset.card_singleton] at hI
          omega
        omega
      omega
    rw [affDim, if_neg (Nonempty.ne_empty
      (⟨a, Set.mem_insert a ({b, c} : Set V3)⟩ :
        ({a, b, c} : Set V3).Nonempty))] at h1
    omega
  have hdir : (affineSpan ℝ {a, b, c}).direction =
      (affineSpan ℝ {b, c, d}).direction := by
    rw [direction_affineSpan, direction_affineSpan]
    exact hvs
  have hd : d ∈ (affineSpan ℝ {b, c, d} : Set V3) :=
    subset_affineSpan ℝ _
      (Set.mem_insert_of_mem b (Set.mem_insert_of_mem c (rfl : d ∈ ({d} : Set V3))))
  have hb : b ∈ (affineSpan ℝ {a, b, c} : Set V3) :=
    subset_affineSpan ℝ _
      (Set.mem_insert_of_mem a (Set.mem_insert b {c}))
  have heq : affineSpan ℝ {a, b, c} = affineSpan ℝ {b, c, d} :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨b, hb⟩ hle
  exact h2 (heq ▸ hd)

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

/-- `u0 ≠ u1` for a `barV V 3` list `[u0; u1; u2; u3]`: the pair sublist
forces `affDim (voronoiList V [u0, u0]) = 2` while the singleton sublist
forces `affDim (voronoiList V [u0]) = 3` if `u0 = u1` (same point set).
Replicates the inline argument of PackingAuto12's `BARV_IMP_HL_1_POS_LT`. -/
private theorem p13_barV_hd_ne (V : Set V3) (u0 u1 u2 u3 : V3)
    (hb : barV V 3 [u0, u1, u2, u3]) : u0 ≠ u1 := by
  intro he
  subst he
  have hv1 : voronoiNondg V [u0, u0] := hb.2 [u0, u0] ⟨⟨[u2, u3], rfl⟩, by simp⟩
  have hv0 : voronoiNondg V [u0] := hb.2 [u0] ⟨⟨[u0, u2, u3], rfl⟩, by simp⟩
  have hset : setOfList [u0, u0] = setOfList [u0] := by simp [setOfList]
  have h1 : affDim (voronoiList V [u0, u0]) + 2 = 4 := hv1.2.2
  have h0 : affDim (voronoiList V [u0]) + 1 = 4 := hv0.2.2
  simp only [voronoiList] at h1 h0
  rw [hset] at h1
  omega

/-- Honest re-derivation of marchal2.hl:1737 `CONVEX_HULL_BREAK_KY_LEMMA`
(sorry'd in PackingAuto12:1195): a segment point `x` of `[a, b]` splits the
4-point hull, `convexHull {a, b, c, d} = convexHull {a, x, c, d} ∪
convexHull {x, b, c, d}`. Coefficient algebra on Auto12's proved
`CONVEX_HULL_4`; the split parameters `(q, k)` of `x = q • a + k • b` come
from `mem_segment_iff_div`. -/
private theorem p13_hull_break4 (a b c d x : V3) (hx : x ∈ segment ℝ a b) :
    convexHull ℝ {a, b, c, d} =
      convexHull ℝ {a, x, c, d} ∪ convexHull ℝ {x, b, c, d} := by
  classical
  have hxco : ∃ q k : ℝ, 0 ≤ q ∧ 0 ≤ k ∧ q + k = 1 ∧ x = q • a + k • b := by
    rw [mem_segment_iff_div] at hx
    obtain ⟨α, β, hα, hβ, hsum, hse⟩ := hx
    refine ⟨α / (α + β), β / (α + β), div_nonneg hα (le_of_lt hsum),
      div_nonneg hβ (le_of_lt hsum), ?_, hse.symm⟩
    rw [← add_div, div_self hsum.ne']
  obtain ⟨q, k, hq, hk, hqk, hxL⟩ := hxco
  have hxh : x ∈ convexHull ℝ ({a, b} : Set V3) := by
    rw [hxL]
    have hset4 : convexHull ℝ ({a, b} : Set V3) = convexHull ℝ {a, b, b, b} := by
      congr 1
      ext y
      simp
    rw [hset4, CONVEX_HULL_4]
    refine ⟨q, k, 0, 0, hq, hk, by norm_num, by norm_num, by linarith, ?_⟩
    simp
  have hmono1 : convexHull ℝ {a, x, c, d} ⊆ convexHull ℝ {a, b, c, d} := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
    · rw [hz]; exact convexHull_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto) hxh
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
  have hmono2 : convexHull ℝ {x, b, c, d} ⊆ convexHull ℝ {a, b, c, d} := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz
    · rw [hz]; exact convexHull_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto) hxh
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
    · rw [hz]; exact subset_convexHull ℝ _ (by simp)
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [CONVEX_HULL_4] at hz
    obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, htsum, hzvec⟩ := hz
    by_cases hk0 : k = 0
    · -- x = a
      have hxa : x = a := by
        rw [hxL, hk0, zero_smul, add_zero]
        have hq1 : q = 1 := by linarith
        rw [hq1, one_smul]
      refine Set.mem_union_right _ ?_
      rw [CONVEX_HULL_4]
      refine ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, htsum, ?_⟩
      rw [hzvec, hxa]
    by_cases hq0 : q = 0
    · -- x = b
      have hxb : x = b := by
        rw [hxL, hq0, zero_smul, zero_add]
        have hk1 : k = 1 := by linarith
        rw [hk1, one_smul]
      refine Set.mem_union_left _ ?_
      rw [CONVEX_HULL_4]
      refine ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, htsum, ?_⟩
      rw [hzvec, hxb]
    have hqnz : q ≠ 0 := hq0
    have hknz : k ≠ 0 := hk0
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqnz)
    have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hknz)
    by_cases h2 : t2 = 0
    · -- t2 = 0: zero weight on b
      refine Set.mem_union_left _ ?_
      rw [CONVEX_HULL_4]
      refine ⟨t1, 0, t3, t4, ht1, by norm_num, ht3, ht4, ?_, ?_⟩
      · linarith
      · rw [hzvec, h2]
        module
    have ht2p : 0 < t2 := by
      refine lt_of_le_of_ne ht2 ?_
      intro hcon
      exact h2 hcon.symm
    set S := t1 + t2 with hSdef
    have hSp : 0 < S := by rw [hSdef]; linarith
    rcases le_or_gt (t2 / S) k with htle | hgt
    · -- p ∈ hull {a, x, c, d}: split at k
      refine Set.mem_union_left _ ?_
      rw [CONVEX_HULL_4]
      have hkey1 : t2 ≤ S * k := by
        have h1 := (div_le_iff₀ hSp).mp htle
        rw [mul_comm] at h1
        exact h1
      have hac2 : (t2 / k) * k = t2 := by field_simp
      have hac1 : S - t2 / k + (t2 / k) * q = t1 := by
        have h1 : (t2 / k) * (q + k) = (t2 / k) * q + (t2 / k) * k := mul_add _ _ _
        rw [hqk, mul_one, hac2] at h1
        linarith
      have hvec : t1 • a + t2 • b + t3 • c + t4 • d
          = (S - t2 / k) • a + (t2 / k) • x + t3 • c + t4 • d := by
        rw [hxL, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hac1, hac2]
      refine ⟨S - t2 / k, t2 / k, t3, t4, sub_nonneg.mpr ((div_le_iff₀ hkpos).mpr hkey1),
        div_nonneg ht2 hkpos.le, ht3, ht4, ?_, ?_⟩
      · linarith
      · rw [hzvec, hvec]
    · -- p ∈ hull {x, b, c, d}: split at q
      refine Set.mem_union_right _ ?_
      rw [CONVEX_HULL_4]
      have hkey2 : S * k ≤ t2 := by
        have h1 : k * S < t2 := (lt_div_iff₀ hSp).mp hgt
        rw [mul_comm]
        exact le_of_lt h1
      have hac1' : (t1 / q) * q = t1 := by field_simp
      have key2 : (t1 / q) * k + (S - t1 / q) = t2 := by
        have h1 : (t1 / q) * (k + q) = (t1 / q) * k + (t1 / q) * q := mul_add _ _ _
        rw [add_comm k q, hqk, mul_one, hac1'] at h1
        linarith
      have hν2 : 0 ≤ S - t1 / q := by
        rw [sub_nonneg, div_le_iff₀ hqpos]
        have h4 : t1 = t1 * q + t1 * k := by rw [← mul_add, hqk, mul_one]
        have h5 : S * q = t1 * q + t2 * q := by rw [hSdef, add_mul]
        have hA : t1 * k + t2 * k = S * k := by rw [← add_mul, ← hSdef]
        have hB : t2 * q + t2 * k = t2 := by rw [← mul_add, hqk, mul_one]
        linarith
      have hvec2 : t1 • a + t2 • b + t3 • c + t4 • d
          = (t1 / q) • x + (S - t1 / q) • b + t3 • c + t4 • d := by
        rw [hxL, smul_add, smul_smul, smul_smul, hac1']
        rw [add_assoc (t1 • a) ((t1 / q * k) • b) ((S - t1 / q) • b), ← add_smul, key2]
      refine ⟨t1 / q, S - t1 / q, t3, t4, div_nonneg ht1 hqpos.le, hν2, ht3, ht4, ?_, ?_⟩
      · linarith
      · rw [hzvec, hvec2]
  · intro z hz
    rcases hz with h | h
    · exact hmono1 h
    · exact hmono2 h

/-- GIANT — HOL `SLTSTLO1` (SLTSTLO.hl:43-580; concl `pack_concl.hl:135`):
the Rogers simplex is covered by the Marchal cells `mcell 0..4`.

DISCHARGES: PackingAuto2.SLTSTLO1_concl (PackingAuto2.lean:729).

CLOSED 2026-09-30 (SLTSTLO1 lane, PA13:402): the full HL case tree is
rebuilt on Auto12's proved marchal2 kit. Case `hl ul < sqrt 2`: witness 4,
all four omega points lie in `hull (setOfList ul)`. Case `sqrt 2 <= hl ul`:
far points → witness 0 (`mcell0`); near points off the head cone → witness 1
(`mcell1`); points in `rconeGt u0 u1 (hl [u0;u1]/sqrt 2)` (the cone
parameter is forced `< 1` by `RCONE_GT_EQ_EMPTY_LEMMA` above) split on the
`affGe {u0,u1} {mxi, w3}` wedge: inside → witness 2 (`mcell2`; second
mutual cone via `RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE` with
`p ∈ voronoiClosed V u0` from the CLOSED `GLTVHUM_concl`); outside → either
`hl [u0;u1;u2] >= sqrt 2` (then `mxi = w2` by the `mxi` if-branch and the
wedge membership holds after all via `CONVEX_HULL_4_SUBSET_AFF_GE_2_2` —
contradiction) or witness 3 (`mcell3`, hull break at `mxi` via the private
`p13_hull_break4` above, which honestly replaces the sorry'd Auto12
`CONVEX_HULL_BREAK_KY_LEMMA` for this argument).

NEEDS (upstream, sorry-backed; each named at its use site):
- `OMEGA_LIST_N_IN_CONVEX_HULL` (Auto7:556; XNHPWAB-family) — Case 1.
- `XNHPWAB2` (Auto7:542) — `w2 ∈ hull {u0,u1,u2}` in the `mcell3` branch.
- `OMEGA_LIST_1_EXPLICIT_NEW` (Auto12:1166, via `XNHPWAB1_concl`
  Auto2:3097) — `w1 = midpoint u0 u1` in both `4b` branches.
- `RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE` (Auto12:1152, sorry) — the
  second mutual cone in the `mcell2` branch.
- `MXI_EXPLICIT_OLD` (Auto12:1508, via `MXI_EXISTS_concl` Auto2) — the
  `mcell3` branch. Proved-honest inputs consumed: `BARV_3_EXPLICIT`
  (Auto8), `TRUNCATE_SIMPLEX_EXPLICIT_0/1/2`, `OMEGA_LIST_TRUNCATE_2`
  (Auto8), `BARV_SUBSET`, `HD_IN_SET_OF_LIST`, `TRUNCATE_SIMPLEX_BARV`
  (Auto5), `CIRCUMCENTER_2` (Auto6), `GLTVHUM_concl` (Auto2, CLOSED),
  `RCONE_GT_EQ_EMPTY_LEMMA` (this file, above). -/
theorem SLTSTLO1 (V : Set V3) (ul : List V3) (p : V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hpr : p ∈ rogers V ul) :
    ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  -- basic data
  have hVsub : setOfList [u0, u1, u2, u3] ⊆ V := BARV_SUBSET V 3 _ hb
  have hu0V : u0 ∈ V := hVsub (by simp [setOfList])
  have hu1V : u1 ∈ V := hVsub (by simp [setOfList])
  have hu01 : u0 ≠ u1 := p13_barV_hd_ne V u0 u1 u2 u3 hb
  have hTR1 : truncateSimplex 1 [u0, u1, u2, u3] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  have hTR2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hTS0 : truncateSimplex 0 [u0, u1, u2, u3] = [u0] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
  have e0 : hdV [u0, u1, u2, u3] = u0 := rfl
  have e1 : hdV [u0, u1, u2, u3].tail = u1 := rfl
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hRog2 : p ∈ convexHull ℝ {hdV [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 1,
      omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} := by
    have h2c := hpr
    rw [ROGERS_EXPLICIT V [u0, u1, u2, u3] hs hp hb] at h2c
    exact h2c
  rcases lt_or_ge (hl [u0, u1, u2, u3]) (Real.sqrt 2) with hH | hH
  · -- =================== Case 1: witness 4 ===================
    refine ⟨4, by omega, ?_⟩
    rw [(MCELL_EXPLICIT 4 V [u0, u1, u2, u3]).2.2.2.2 (le_refl 4), mcell4, if_pos hH]
    have m0 : hdV [u0, u1, u2, u3] ∈ convexHull ℝ (setOfList [u0, u1, u2, u3]) :=
      subset_convexHull ℝ _ (HD_IN_SET_OF_LIST _ (by simp))
    have m1 : omegaListN V [u0, u1, u2, u3] 1 ∈
        convexHull ℝ (setOfList [u0, u1, u2, u3]) :=
      OMEGA_LIST_N_IN_CONVEX_HULL V [u0, u1, u2, u3] 3 1 hp hb (by omega) hH
    have m2 : omegaListN V [u0, u1, u2, u3] 2 ∈
        convexHull ℝ (setOfList [u0, u1, u2, u3]) :=
      OMEGA_LIST_N_IN_CONVEX_HULL V [u0, u1, u2, u3] 3 2 hp hb (by omega) hH
    have m3 : omegaListN V [u0, u1, u2, u3] 3 ∈
        convexHull ℝ (setOfList [u0, u1, u2, u3]) :=
      OMEGA_LIST_N_IN_CONVEX_HULL V [u0, u1, u2, u3] 3 3 hp hb (by omega) hH
    refine convexHull_min ?_ (convex_convexHull ℝ _) hRog2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz
    · rw [hz]; exact m0
    · rw [hz]; exact m1
    · rw [hz]; exact m2
    · rw [hz]; exact m3
  · -- √2 ≤ hl ul for the rest
    rcases le_or_gt (Real.sqrt 2) (dist p u0) with hfar | hnear
    · -- =================== Case 2: witness 0 ===================
      refine ⟨0, by omega, ?_⟩
      rw [(MCELL_EXPLICIT 0 V [u0, u1, u2, u3]).1, mcell0]
      refine ⟨hpr, ?_⟩
      simp only [Metric.mem_ball, e0]
      exact not_lt.mpr hfar
    · -- =================== Case 3 / 4 ===================
      by_cases hpcone : p ∈ rconeGt (hdV [u0, u1, u2, u3]) (hdV [u0, u1, u2, u3].tail)
          (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2)
      · -- =================== Case 4: in the strict cone ===================
        have hpc : p ∈ rconeGt u0 u1
            (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) := by
          simpa only [e0, e1] using hpcone
        -- Step A: the cone parameter is < 1 (else the cone is empty)
        have hA1 : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 := by
          by_contra hcon
          have hcon' : Real.sqrt 2 ≤ hl (truncateSimplex 1 [u0, u1, u2, u3]) :=
            not_lt.mp hcon
          have hempty : rconeGt u0 u1
              (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) = ∅ := by
            refine RCONE_GT_EQ_EMPTY_LEMMA u0 u1 _ ?_
            exact (le_div_iff₀ h2pos).mpr (by linarith)
          rw [hempty] at hpc
          exact absurd hpc (Set.notMem_empty p)
        have hA2 : 0 < hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 :=
          div_pos (BARV_IMP_HL_1_POS_LT V [u0, u1, u2, u3] hs hp hb) h2pos
        have hA3 : hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 ≤ 1 :=
          (div_le_iff₀ h2pos).mpr (by rw [one_mul]; linarith)
        by_cases hpaff : p ∈ affGe {hdV [u0, u1, u2, u3], hdV [u0, u1, u2, u3].tail}
            {mxi V [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 3}
        · -- =================== Case 4a: witness 2 ===================
          simp only [e0, e1] at hpaff
          refine ⟨2, by omega, ?_⟩
          rw [(MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1, mcell2, if_pos ⟨hA1, hH⟩]
          simp only []
          simp only [e0, e1]
          refine ⟨⟨RCONE_GT_SUBSET_RCONE_GE u0 u1 _ hpc, ?_⟩, hpaff⟩
          have hvoro : p ∈ voronoiClosed V u0 := by
            rw [GLTVHUM_concl V u0 p ⟨hp, hs⟩ hu0V]
            exact ⟨[u0, u1, u2, u3], hb, hpr, hTS0⟩
          exact RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE V u0 u1 _ p hp hs hu0V hu1V
            hu01 hA2 hA3 (RCONE_GT_SUBSET_RCONE_GE u0 u1 _ hpc) hvoro
        · -- =================== Case 4b ===================
          simp only [e0, e1] at hpaff
          have hw1 : omegaListN V [u0, u1, u2, u3] 1 = midpoint ℝ u0 u1 := by
            have hh : hl [u0, u1] < Real.sqrt 2 := by rw [← hTR1]; exact hA1
            rw [OMEGA_LIST_1_EXPLICIT_NEW u0 u1 u2 u3 V [u0, u1, u2, u3] hs hp hb rfl hh,
              CIRCUMCENTER_2]
          have hpR : p ∈ convexHull ℝ {u0, midpoint ℝ u0 u1,
              omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} := by
            have h5 : p ∈ convexHull ℝ {u0, omegaListN V [u0, u1, u2, u3] 1,
                omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} := by
              simpa only [e0] using hRog2
            rwa [hw1] at h5
          rcases le_or_gt (Real.sqrt 2) (hl (truncateSimplex 2 [u0, u1, u2, u3])) with
            hGE2 | hLT2
          · -- -------- Case 4b-i: the affGe membership holds after all --------
            have hmxi : mxi V [u0, u1, u2, u3] = omegaListN V [u0, u1, u2, u3] 2 := by
              rw [mxi, if_pos hGE2]
            exfalso
            apply hpaff
            refine (CONVEX_HULL_4_SUBSET_AFF_GE_2_2 u0 u1 (mxi V [u0, u1, u2, u3])
              (omegaListN V [u0, u1, u2, u3] 3)) ?_
            refine convexHull_min ?_ (convex_convexHull ℝ
              ({u0, u1, mxi V [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 3} : Set V3)) hpR
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rw [← hmxi] at hz
            rcases hz with hz | hz | hz | hz
            · rw [hz]; exact subset_convexHull ℝ _ (by simp)
            · rw [hz]; exact convexHull_mono (by
                intro y hy
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
                tauto) (Convex.midpoint_mem
                (convex_convexHull ℝ ({u0, u1} : Set V3))
                (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)))
            · rw [hz]; exact subset_convexHull ℝ _ (by simp)
            · rw [hz]; exact subset_convexHull ℝ _ (by simp)
          · -- -------- Case 4b-ii: witness 3 --------
            refine ⟨3, by omega, ?_⟩
            rw [(MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1, mcell3, if_pos ⟨hLT2, hH⟩,
              hTR2]
            obtain ⟨s, hsSeg, hsDist, hsEq⟩ :=
              MXI_EXPLICIT_OLD V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl hLT2 hH
            rw [← hsEq]
            have hbar2 : barV V 2 [u0, u1, u2] := by
              rw [← hTR2]
              exact TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
            have hw2 : omegaListN V [u0, u1, u2, u3] 2 ∈
                convexHull ℝ (setOfList [u0, u1, u2]) := by
              have hwx := XNHPWAB2 V [u0, u1, u2] 2 hp hbar2 (by rw [← hTR2]; exact hLT2)
              rw [← OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3] at hwx
              exact hwx
            have hR3 : p ∈ convexHull ℝ {u0, u1, omegaListN V [u0, u1, u2, u3] 2,
                omegaListN V [u0, u1, u2, u3] 3} := by
              refine convexHull_min ?_ (convex_convexHull ℝ _) hpR
              intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with hz | hz | hz | hz
              · rw [hz]; exact subset_convexHull ℝ _ (by simp)
              · rw [hz]; exact convexHull_mono (by
                  intro y hy
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
                  tauto) (Convex.midpoint_mem
                  (convex_convexHull ℝ ({u0, u1} : Set V3))
                  (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)))
              · rw [hz]; exact subset_convexHull ℝ _ (by simp)
              · rw [hz]; exact subset_convexHull ℝ _ (by simp)
            have hEqSet : convexHull ℝ {u0, u1, omegaListN V [u0, u1, u2, u3] 2,
                omegaListN V [u0, u1, u2, u3] 3}
                = convexHull ℝ {omegaListN V [u0, u1, u2, u3] 2,
                  omegaListN V [u0, u1, u2, u3] 3, u0, u1} := by
              congr 1
              ext z
              simp
              tauto
            rw [hEqSet] at hR3
            rw [p13_hull_break4 (omegaListN V [u0, u1, u2, u3] 2)
              (omegaListN V [u0, u1, u2, u3] 3) u0 u1 s hsSeg] at hR3
            rcases hR3 with hR3 | hR3
            · refine convexHull_min ?_ (convex_convexHull ℝ
                (setOfList [u0, u1, u2] ∪ {s})) hR3
              intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with hz | hz | hz | hz
              · rw [hz]
                exact convexHull_mono Set.subset_union_left hw2
              · rw [hz]; exact subset_convexHull ℝ _ (by simp [setOfList])
              · rw [hz]; exact subset_convexHull ℝ _ (by simp [setOfList])
              · rw [hz]; exact subset_convexHull ℝ _ (by simp [setOfList])
            · exfalso
              apply hpaff
              have hre : convexHull ℝ {s, omegaListN V [u0, u1, u2, u3] 3, u0, u1} ⊆
                  affGe {u0, u1} {mxi V [u0, u1, u2, u3],
                    omegaListN V [u0, u1, u2, u3] 3} := by
                have h1 : convexHull ℝ {s, omegaListN V [u0, u1, u2, u3] 3, u0, u1}
                    = convexHull ℝ {u0, u1, mxi V [u0, u1, u2, u3],
                      omegaListN V [u0, u1, u2, u3] 3} := by
                  rw [← hsEq]
                  congr 1
                  ext z
                  simp
                  tauto
                rw [h1]
                exact CONVEX_HULL_4_SUBSET_AFF_GE_2_2 u0 u1 _ _
              exact hre hR3
      · -- =================== Case 3: witness 1 ===================
        refine ⟨1, by omega, ?_⟩
        rw [(MCELL_EXPLICIT 1 V [u0, u1, u2, u3]).2.1, mcell1, if_pos hH]
        refine ⟨⟨hpr, ?_⟩, hpcone⟩
        simp only [Metric.mem_closedBall, e0]
        exact le_of_lt hnear

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
