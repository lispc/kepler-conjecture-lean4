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
- DISCHARGES convention: `URRPHBZ2` / `SLTSTLO2` match the `sorry`-bodied
  interfaces `Kepler.Text.PackingAuto2.URRPHBZ2_concl` / `SLTSTLO2_concl`
  verbatim; at merge time the interface bodies become `exact URRPHBZ2` etc.
  (`SLTSTLO1_concl` was harvested from PA2 in the 2026-10-08 A-wave —
  `SLTSTLO1` here discharges `PackingConcl.SLTSTLO1_concl_discharged`
  directly.) `DDZUPHJ` has NO pack_concl interface
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
import Kepler.Text.PackingAuto9
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

/-- HOL `rcone_eq z w h` (flyspeck_multivariate.ml:4580): the equality
version of the radial cone, in inner-product form (`inner` = `dot`). -/
private def rconeEq (v w : V3) (h : ℝ) : Set V3 :=
  {x | inner ℝ (x - v) (w - v) = dist x v * dist w v * h}

/-- Copy of PA17's `p17_coplanar_null`: subsets of a coplanar set are null. -/
private theorem p13_coplanar_null {s t : Set V3} (hcop : Coplanar s) (hsub : t ⊆ s) :
    volume t = 0 := by
  obtain ⟨u, v, w, hsp⟩ := hcop
  have hvs : vectorSpan ℝ ({u, v, w} : Set V3)
      = Submodule.span ℝ ({v - u, w - u} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show u ∈ ({u, v, w} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨w, by simp, rfl⟩
  have hne : (affineSpan ℝ ({u, v, w} : Set V3) : AffineSubspace ℝ V3) ≠ ⊤ := by
    intro htop
    have hdir : (affineSpan ℝ ({u, v, w} : Set V3)).direction = ⊤ := by
      rw [htop]; exact AffineSubspace.direction_top ℝ V3 V3
    have hfr : Module.finrank ℝ
        (Submodule.span ℝ ({v - u, w - u} : Set V3)) ≤ 2 := by
      have h2 := finrank_span_finset_le_card (R := ℝ) ({v - u, w - u} : Finset V3)
      unfold Set.finrank at h2
      rw [show (({v - u, w - u} : Finset V3) : Set V3)
        = ({v - u, w - u} : Set V3) from by simp] at h2
      refine h2.trans ?_
      calc ({v - u, w - u} : Finset V3).card
          ≤ ({w - u} : Finset V3).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    have hle : Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction ≤ 2 := by
      rw [direction_affineSpan, hvs]
      exact hfr
    rw [hdir, finrank_top] at hle
    exact absurd hle (by norm_num)
  exact measure_mono_null (hsub.trans hsp)
    (Measure.addHaar_affineSubspace volume _ hne)

/-- Convexity of the radial cone for nonnegative parameter (copy of
PA24's `p24_rconeGe_convex`). -/
private theorem p13_rconeGe_convex (v w : V3) (c : ℝ) (hc0 : 0 ≤ c) :
    Convex ℝ (rconeGe v w c) := by
  intro x hx y hy α β hα hβ hαβ
  have hv : ((α • x + β • y : V3) - v) = α • (x - v) + β • (y - v) := by
    have hvs : ((α • x + β • y : V3) - v)
        = α • (x - v) + β • (y - v) + ((α + β - 1 : ℝ)) • v := by
      module
    rw [hvs]
    have hz : ((α + β - 1 : ℝ)) • v = 0 := by
      rw [← hαβ]
      simp
    rw [hz, add_zero]
  have hdot : ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      = α * ((x - v : V3) ⬝ᵥ (w - v)) + β * ((y - v : V3) ⬝ᵥ (w - v)) := by
    rw [hv]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct,
      smul_eq_mul]
  have hdist : dist (α • x + β • y) v ≤ α * dist x v + β * dist y v := by
    have h1 : dist (α • x + β • y) v = ‖((α • x + β • y : V3) - v)‖ :=
      dist_eq_norm _ _
    have h3 : ‖α • (x - v) + β • (y - v)‖
        ≤ ‖(α : ℝ) • (x - v)‖ + ‖(β : ℝ) • (y - v)‖ := norm_add_le _ _
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hα, abs_of_nonneg hβ] at h3
    rw [h1, hv]
    calc ‖α • (x - v) + β • (y - v)‖
        ≤ α * ‖(x - v : V3)‖ + β * ‖(y - v : V3)‖ := h3
      _ = α * dist x v + β * dist y v := by
          rw [← dist_eq_norm, ← dist_eq_norm]
  have hD : 0 ≤ dist w v := dist_nonneg
  show ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      ≥ dist (α • x + β • y) v * dist w v * c
  calc ((α • x + β • y : V3) - v) ⬝ᵥ (w - v)
      = α * ((x - v : V3) ⬝ᵥ (w - v)) + β * ((y - v : V3) ⬝ᵥ (w - v)) := hdot
    _ ≥ α * (dist x v * dist w v * c) + β * (dist y v * dist w v * c) := by
        have e1 := mul_le_mul_of_nonneg_left hx hα
        have e2 := mul_le_mul_of_nonneg_left hy hβ
        linarith
    _ = (α * dist x v + β * dist y v) * dist w v * c := by ring
    _ ≥ dist (α • x + β • y) v * dist w v * c :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdist hD) hc0

/-- For `0 ≤ h < 1` the equality cone is contained in the frontier of the
convex solid cone. -/
private theorem p13_rconeEq_subset_frontier {v w : V3} {h : ℝ}
    (hw : w ≠ v) (h0 : 0 ≤ h) (h1 : h < 1) :
    rconeEq v w h ⊆ frontier (rconeGe v w h) := by
  intro x hx
  have hcpos : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  have hx' : inner ℝ (x - v) (w - v) = dist x v * dist w v * h := hx
  have hxdot : (x - v) ⬝ᵥ (w - v) = dist x v * dist w v * h := by
    rw [← inner_eq_dot]; exact hx'
  have hxge : x ∈ rconeGe v w h := by
    rw [rconeGe, Set.mem_setOf_eq]
    exact le_of_eq hxdot.symm
  rw [frontier, Set.mem_sdiff]
  refine ⟨subset_closure hxge, ?_⟩
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
  set t := ε / (2 * ‖w - v‖) with ht
  have htpos : 0 < t := by
    rw [ht]; positivity
  set y := x - t • (w - v) with hy
  have hyball : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball]
    have hsub : y - x = -(t • (w - v)) := by rw [hy]; module
    rw [dist_eq_norm, hsub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    have htv : t * ‖w - v‖ = ε / 2 := by
      rw [ht]; field_simp
    rw [htv]; linarith
  have hyge : y ∈ rconeGe v w h := interior_subset (hball hyball)
  have hyge_inner : inner ℝ (y - v) (w - v) ≥ dist y v * dist w v * h := by
    have hh := hyge
    rw [rconeGe, Set.mem_setOf_eq] at hh
    have h2 : inner ℝ (y - v) (w - v) = (y - v) ⬝ᵥ (w - v) := inner_eq_dot ..
    rw [h2]
    exact hh
  set s := x - v with hs
  set c := w - v with hc
  have hCpos : 0 < ‖c‖ := by rw [hc]; exact hcpos
  have hsineq : inner ℝ s c = dist x v * dist w v * h := by
    have h := hx'
    rw [hs, hc] at h
    exact h
  have hsi : inner ℝ s c = ‖s‖ * ‖c‖ * h := by
    rw [hsineq, hs, hc, dist_eq_norm, dist_eq_norm]
  have hydot : inner ℝ (y - v) c = inner ℝ s c - t * inner ℝ c c := by
    have hsub : (y - v : V3) = s - t • c := by rw [hy, hs, hc]; module
    rw [hsub, inner_sub_left, real_inner_smul_left]
  have hcc : inner ℝ c c = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
  have hydist : dist y v ≥ ‖s‖ - t * ‖c‖ := by
    have hsub : (y - v : V3) = s - t • c := by rw [hy, hs, hc]; module
    rw [dist_eq_norm, hsub, hs]
    have htri := norm_sub_norm_le (x - v) (t • c)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at htri
    exact htri
  have hyout : inner ℝ (y - v) c < dist y v * ‖c‖ * h := by
    have hC2pos : 0 < t * ‖c‖ ^ 2 := by positivity
    rw [hydot, hsi, hcc]
    by_cases hh0 : h = 0
    · subst hh0
      have : dist y v * ‖c‖ * (0:ℝ) = 0 := by ring
      rw [this]
      linarith [hC2pos]
    · have hhpos : 0 < h := lt_of_le_of_ne h0 (Ne.symm hh0)
      have hkey : ‖s‖ * ‖c‖ * h - t * ‖c‖ ^ 2
          < (‖s‖ - t * ‖c‖) * ‖c‖ * h := by
        nlinarith [htpos, hCpos, hhpos, h1]
      refine lt_of_lt_of_le hkey ?_
      have hnonneg : 0 ≤ ‖c‖ * h := mul_nonneg hCpos.le hhpos.le
      have hmono : (‖s‖ - t * ‖c‖) * (‖c‖ * h) ≤ dist y v * (‖c‖ * h) :=
        mul_le_mul_of_nonneg_right hydist hnonneg
      nlinarith [hmono]
  have hyge'' : dist y v * ‖c‖ * h ≤ inner ℝ (y - v) c := by
    have h := hyge_inner
    rw [hc] at h
    have hd : dist w v = ‖c‖ := by rw [hc, dist_eq_norm]
    rwa [hd] at h
  linarith

/-- For `|h| = 1` the equality cone lies in the line through `v` and `w`. -/
private theorem p13_rconeEq_subset_line {v w : V3} (hw : w ≠ v) {h : ℝ}
    (hh : h = 1 ∨ h = -1) :
    rconeEq v w h ⊆ (affineSpan ℝ {v, w} : Set V3) := by
  intro x hx
  have hcpos : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  have hxeq : inner ℝ (x - v) (w - v) = dist x v * dist w v * h := hx
  rcases hh with rfl | rfl
  · have hx1 : inner ℝ (x - v) (w - v) = dist x v * dist w v := by
      simpa using hxeq
    by_cases hxv : x = v
    · rw [hxv]
      exact subset_affineSpan ℝ _ (Set.mem_insert v {w})
    · have hinner : inner ℝ (x - v) (w - v) = ‖x - v‖ * ‖w - v‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hx1
      have hpar : ‖w - v‖ • (x - v) = ‖x - v‖ • (w - v) :=
        (inner_eq_norm_mul_iff_real).mp hinner
      have hC : (‖w - v‖ : ℝ) ≠ 0 := ne_of_gt hcpos
      have hxexpr : x - v = (‖w - v‖⁻¹ * ‖x - v‖) • (w - v) := by
        have h1 : (‖w - v‖)⁻¹ • (‖w - v‖ • (x - v))
            = (‖w - v‖)⁻¹ • (‖x - v‖ • (w - v)) := by rw [hpar]
        rw [inv_smul_smul₀ hC, smul_smul] at h1
        exact h1
      have hthis : x = (x - v) +ᵥ v := by simp
      rw [hthis, hxexpr]
      exact smul_vsub_vadd_mem_affineSpan_pair _ v w
  · have hx1 : inner ℝ (x - v) (w - v) = -(dist x v * dist w v) := by
      have h := hxeq
      rw [h, mul_neg, mul_one]
    have hinner : inner ℝ (x - v) (v - w) = ‖x - v‖ * ‖v - w‖ := by
      have hneg : inner ℝ (x - v) (v - w) = -inner ℝ (x - v) (w - v) := by
        rw [show (v - w : V3) = -(w - v) from by module, inner_neg_right]
      rw [hneg, hx1]
      have h1 : ‖v - w‖ = ‖w - v‖ := by
        rw [show (v - w : V3) = -(w - v) from by module, norm_neg]
      rw [dist_eq_norm, dist_eq_norm, h1]
      ring
    have hpar : ‖v - w‖ • (x - v) = ‖x - v‖ • (v - w) :=
      (inner_eq_norm_mul_iff_real).mp hinner
    have hvw : (v - w : V3) = -(w - v) := by module
    have hnorm : ‖v - w‖ = ‖w - v‖ := by rw [hvw, norm_neg]
    rw [hnorm] at hpar
    have hneg2 : ‖x - v‖ • (v - w) = -(‖x - v‖ • (w - v)) := by
      rw [hvw, smul_neg]
    rw [hneg2] at hpar
    have hC : (‖w - v‖ : ℝ) ≠ 0 := ne_of_gt hcpos
    have hxexpr : x - v = (-(‖w - v‖⁻¹ * ‖x - v‖)) • (w - v) := by
      have h1 : (‖w - v‖)⁻¹ • (‖w - v‖ • (x - v))
          = (‖w - v‖)⁻¹ • (-(‖x - v‖ • (w - v))) := by rw [hpar]
      rw [inv_smul_smul₀ hC, smul_neg, smul_smul, ← neg_smul] at h1
      exact h1
    have hthis : x = (x - v) +ᵥ v := by simp
    rw [hthis, hxexpr]
    exact smul_vsub_vadd_mem_affineSpan_pair _ v w

private theorem p13_rconeEq_null_of_nonneg {v w : V3} (hw : w ≠ v) {h : ℝ}
    (h0 : 0 ≤ h) (h1 : h < 1) : nullSet (rconeEq v w h) :=
  measure_mono_null (p13_rconeEq_subset_frontier hw h0 h1)
    (Convex.addHaar_frontier volume (p13_rconeGe_convex v w h h0))

private theorem p13_rconeEq_null_of_abs_one {v w : V3} (hw : w ≠ v) {h : ℝ}
    (hh : h = 1 ∨ h = -1) : nullSet (rconeEq v w h) := by
  have hline : rconeEq v w h ⊆ (affineSpan ℝ {v, w} : Set V3) :=
    p13_rconeEq_subset_line hw hh
  have hcop : Coplanar (affineSpan ℝ {v, w} : Set V3) := by
    refine ⟨v, v, w, ?_⟩
    intro z hz
    simpa [show ({v, v, w} : Set V3) = {v, w} from by ext q; simp] using hz
  exact p13_coplanar_null hcop hline

private theorem p13_rconeEq_null_of_abs_gt_one {v w : V3} (hw : w ≠ v) {h : ℝ}
    (hh : h < -1 ∨ 1 < h) : nullSet (rconeEq v w h) := by
  have hsub : rconeEq v w h ⊆ {v} := by
    intro x hx
    have hxeq : inner ℝ (x - v) (w - v) = dist x v * dist w v * h := hx
    by_contra hxv
    have hdist : 0 < dist x v := dist_pos.mpr hxv
    have hcpos : 0 < dist w v := dist_pos.mpr hw
    have hcs : |inner ℝ (x - v) (w - v)| ≤ ‖x - v‖ * ‖w - v‖ :=
      abs_real_inner_le_norm (x - v) (w - v)
    have h1 : ‖x - v‖ * ‖w - v‖ = dist x v * dist w v := by
      rw [dist_eq_norm, dist_eq_norm]
    have hp : 0 < dist x v * dist w v := mul_pos hdist hcpos
    rw [abs_le] at hcs
    rw [hxeq, h1] at hcs
    rcases hh with hlt | hgt
    · nlinarith [hcs.1, hp]
    · nlinarith [hcs.2, hp]
  exact measure_mono_null hsub (by simp)

/-- HOL `NEGLIGIBLE_RCONE_EQ` (flyspeck_multivariate.ml:5196): for `w ≠ v`
the equality radial cone is null. -/
theorem nullset_rcone_eq (v w : V3) (h : ℝ) (hw : w ≠ v) :
    nullSet (rconeEq v w h) := by
  rcases lt_trichotomy h (-1) with hlt | heq | hgt
  · exact p13_rconeEq_null_of_abs_gt_one hw (Or.inl hlt)
  · subst heq
    exact p13_rconeEq_null_of_abs_one hw (Or.inr rfl)
  · rcases lt_trichotomy h 0 with hneg | hzero | hpos
    · have hd : dist (2 • v - w) v = dist w v := by
        rw [dist_comm]
        have h : (v - (2 • v - w) : V3) = w - v := by module
        rw [dist_eq_norm, dist_eq_norm, h]
      have hdotneg : ∀ x : V3, inner ℝ (x - v) ((2 • v - w) - v)
          = -inner ℝ (x - v) (w - v) := by
        intro x
        rw [show ((2 • v - w) - v : V3) = -(w - v) from by module, inner_neg_right]
      have hsub : rconeEq v w h = rconeEq v (2 • v - w) (-h) := by
        ext x
        constructor
        · intro hx
          have hxi : inner ℝ (x - v) (w - v) = dist x v * dist w v * h := hx
          have hnew : inner ℝ (x - v) ((2 • v - w) - v)
              = dist x v * dist (2 • v - w) v * (-h) := by
            rw [hdotneg x, hxi, hd, mul_neg]
          exact hnew
        · intro hx
          have hxi : inner ℝ (x - v) ((2 • v - w) - v)
              = dist x v * dist (2 • v - w) v * (-h) := hx
          have h1 : -inner ℝ (x - v) (w - v) = -(dist x v * dist w v * h) := by
            rw [← hdotneg x, hxi, hd, mul_neg]
          show inner ℝ (x - v) (w - v) = dist x v * dist w v * h
          linarith
      rw [hsub]
      have hw' : (2 • v - w) ≠ v := by
        intro he
        apply hw
        have h3 : v - w = 0 := by
          have h2 := congrArg (fun z : V3 => z - v) he
          simpa [two_smul, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2
        exact (sub_eq_zero.mp h3).symm
      exact p13_rconeEq_null_of_nonneg hw' (by linarith) (by linarith)
    · subst hzero
      exact p13_rconeEq_null_of_nonneg hw le_rfl (by norm_num)
    · rcases lt_trichotomy h 1 with hlt1 | heq1 | hgt1
      · exact p13_rconeEq_null_of_nonneg hw hpos.le hlt1
      · subst heq1
        exact p13_rconeEq_null_of_abs_one hw (Or.inl rfl)
      · exact p13_rconeEq_null_of_abs_gt_one hw (Or.inr hgt1)

/-! ## SLTSTLO.hl: the `SLTSTLO2` null set `Z` (B8a) -/

/-- The seven boundary surfaces of `ul`'s data (HOL `SLTSTLO2`'s
`B1 .. B7`).  `Z` is their nested union, exactly as in the HOL
`NEGLIGIBLE_UNION` chain. -/
private def sltZ (V : Set V3) (ul : List V3) : Set V3 :=
  ((((((frontier (rogers V ul)
        ∪ {w : V3 | ‖w - hdV ul‖ = Real.sqrt 2})
       ∪ rconeEq (hdV ul) (hdV (ul.tail))
           (hl (truncateSimplex 1 ul) / Real.sqrt 2))
      ∪ (affineSpan ℝ ({hdV ul, (hdV (ul.tail)), mxi V ul} : Set V3) : Set V3))
     ∪ convexHull ℝ ({omegaListN V ul 2, omegaListN V ul 3} : Set V3))
    ∪ (affineSpan ℝ ({hdV ul, (hdV (ul.tail)), (hdV (ul.tail.tail))} : Set V3) : Set V3))
   ∪ (affineSpan ℝ ({omegaListN V ul 1, omegaListN V ul 2,
        omegaListN V ul 3} : Set V3) : Set V3))

/-- `hdV ul ≠ hdV ul.tail` for a `barV V 3` list. -/
private theorem p13_barV_hd_ne_tail (V : Set V3) (ul : List V3)
    (hb : barV V 3 ul) : hdV ul ≠ (hdV (ul.tail)) := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  simpa [hdV] using p13_barV_hd_ne V u0 u1 u2 u3 hb

/-- An affine span of three points is null. -/
private theorem p13_nullset_affineSpan_triple (a b c : V3) :
    nullSet (affineSpan ℝ ({a, b, c} : Set V3)) :=
  p13_coplanar_null ⟨a, b, c, subset_rfl⟩ subset_rfl

/-- A segment (convex hull of two points) is null. -/
private theorem p13_nullset_convexHull_pair (a b : V3) :
    nullSet (convexHull ℝ ({a, b} : Set V3)) := by
  have h1 : convexHull ℝ ({a, b} : Set V3) ⊆
      (affineSpan ℝ ({a, b} : Set V3) : Set V3) :=
    convexHull_subset_affineSpan ({a, b} : Set V3)
  have h2 : (affineSpan ℝ ({a, b} : Set V3) : Set V3) ⊆
      (affineSpan ℝ ({a, b, b} : Set V3) : Set V3) := by
    rw [show ({a, b, b} : Set V3) = {a, b} from by ext q; simp]
  exact p13_coplanar_null ⟨a, b, b, subset_rfl⟩ (h1.trans h2)

/-- `frontier (rogers V ul)` is null on the `barV V 3` regime. -/
private theorem p13_nullset_frontier_rogers (V : Set V3) (ul : List V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) :
    nullSet (frontier (rogers V ul)) := by
  rw [ROGERS_EXPLICIT V ul hs hp hb]
  exact Convex.addHaar_frontier volume (convex_convexHull ℝ _)

/-- B8a: the `SLTSTLO2` null set is null. -/
private theorem p13_sltZ_null (V : Set V3) (ul : List V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) :
    nullSet (sltZ V ul) := by
  unfold sltZ
  refine measure_union_null (measure_union_null (measure_union_null
    (measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_)
    ?_) ?_) ?_
  · exact p13_nullset_frontier_rogers V ul hs hp hb
  · exact NULLSET_SPHERE _ ⟨hdV ul, Real.sqrt 2, Real.sqrt_pos.2 (by norm_num), rfl⟩
  · exact nullset_rcone_eq (hdV ul) (hdV (ul.tail))
      (hl (truncateSimplex 1 ul) / Real.sqrt 2) (Ne.symm (p13_barV_hd_ne_tail V ul hb))
  · exact p13_nullset_affineSpan_triple _ _ _
  · exact p13_nullset_convexHull_pair _ _
  · exact p13_nullset_affineSpan_triple _ _ _
  · exact p13_nullset_affineSpan_triple _ _ _

/-- B8a: existence of a covering cell index off `Z` (HOL's `SLTSTLO1`
call, including the `p ∈ rogers \ Z` projection). -/
private theorem p13_sltstlo2_exists (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hpZ : p ∈ rogers V ul \ sltZ V ul) :
    ∃ i : ℕ, i ≤ 4 ∧ p ∈ mcell i V ul :=
  SLTSTLO1 V ul p hs hp hb hpZ.1


/-! ## SLTSTLO2 case-tree fragments (B8a/B8b partial, green) -/

/-- In the `hl ul < √2` regime every covering index is `4` (`EMNWUUS2`
kills `mcell0..3`). -/
private theorem p13_lowhl_index (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hlt : hl ul < Real.sqrt 2) {i : ℕ} (hi : i ≤ 4)
    (hpi : p ∈ mcell i V ul) : i = 4 := by
  obtain ⟨e0, e1, e2, e3⟩ := (EMNWUUS2 V ul hs hp hb).1 hlt
  interval_cases i
  · rw [(MCELL_EXPLICIT 0 V ul).1, e0] at hpi
    exact absurd hpi (Set.notMem_empty p)
  · rw [(MCELL_EXPLICIT 1 V ul).2.1, e1] at hpi
    exact absurd hpi (Set.notMem_empty p)
  · rw [(MCELL_EXPLICIT 2 V ul).2.2.1, e2] at hpi
    exact absurd hpi (Set.notMem_empty p)
  · rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1, e3] at hpi
    exact absurd hpi (Set.notMem_empty p)
  · rfl

/-- In the `sqrt 2 ≤ hl ul` regime `mcell4` is empty, so every covering
index is `≤ 3`. -/
private theorem p13_highhl_index (V : Set V3) (ul : List V3) (p : V3)
    (hb : barV V 3 ul) (hge : Real.sqrt 2 ≤ hl ul) {i : ℕ} (hi : i ≤ 4)
    (hpi : p ∈ mcell i V ul) : i ≤ 3 := by
  rcases Nat.lt_or_ge i 4 with h | h
  · omega
  · have h4 : mcell i V ul = mcell4 V ul := (MCELL_EXPLICIT i V ul).2.2.2.2 h
    have hempty : mcell4 V ul = ∅ := by
      rw [mcell4, if_neg (not_lt.mpr hge)]
    rw [h4, hempty] at hpi
    exact absurd hpi (Set.notMem_empty p)

/-- Off `Z`, `mcell0` and `mcell1` are disjoint: the only interface is the
sphere `B2`. -/
private theorem p13_disjoint_mcell0_mcell1 (V : Set V3) (ul : List V3) (p : V3)
    (hpZ : p ∈ rogers V ul \ sltZ V ul)
    (h0 : p ∈ mcell 0 V ul) (h1 : p ∈ mcell 1 V ul) : False := by
  rw [(MCELL_EXPLICIT 0 V ul).1, mcell0] at h0
  rw [(MCELL_EXPLICIT 1 V ul).2.1] at h1
  by_cases hc : Real.sqrt 2 ≤ hl ul
  · rw [mcell1, if_pos hc] at h1
    have hfar : ¬ p ∈ Metric.ball (hdV ul) (Real.sqrt 2) := fun hb => h0.2 hb
    have hnear : p ∈ Metric.closedBall (hdV ul) (Real.sqrt 2) := h1.1.2
    have hd : dist p (hdV ul) = Real.sqrt 2 := by
      refine le_antisymm ?_ ?_
      · simpa [Metric.mem_closedBall] using hnear
      · simpa [Metric.mem_ball, not_lt] using hfar
    have hB2 : p ∈ {w : V3 | ‖w - hdV ul‖ = Real.sqrt 2} := by
      simpa [dist_eq_norm] using hd
    have hmem : p ∈ sltZ V ul := by
      simp only [sltZ, Set.mem_union]
      tauto
    exact hpZ.2 hmem
  · rw [mcell1, if_neg hc] at h1
    exact absurd h1 (Set.notMem_empty p)

/-- Off `Z`, `mcell1` and `mcell2` are disjoint: the only interface is the
equality cone `B3`. -/
private theorem p13_disjoint_mcell1_mcell2 (V : Set V3) (ul : List V3) (p : V3)
    (hpZ : p ∈ rogers V ul \ sltZ V ul)
    (h1 : p ∈ mcell 1 V ul) (h2 : p ∈ mcell 2 V ul) : False := by
  rw [(MCELL_EXPLICIT 1 V ul).2.1] at h1
  rw [(MCELL_EXPLICIT 2 V ul).2.2.1] at h2
  by_cases hc : Real.sqrt 2 ≤ hl ul
  · rw [mcell1, if_pos hc] at h1
    have hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 := by
      by_contra h
      rw [mcell2, if_neg (by tauto)] at h2
      exact absurd h2 (Set.notMem_empty p)
    rw [mcell2, if_pos ⟨hcond, hc⟩] at h2
    dsimp only at h2
    have hnotgt : ¬ ((p - hdV ul) ⬝ᵥ (hdV (ul.tail) - hdV ul) >
        dist p (hdV ul) * dist (hdV (ul.tail)) (hdV ul)
          * (hl (truncateSimplex 1 ul) / Real.sqrt 2)) := h1.2
    have hge : (p - hdV ul) ⬝ᵥ (hdV (ul.tail) - hdV ul) ≥
        dist p (hdV ul) * dist (hdV (ul.tail)) (hdV ul)
          * (hl (truncateSimplex 1 ul) / Real.sqrt 2) := h2.1.1
    have heqdot : (p - hdV ul) ⬝ᵥ (hdV (ul.tail) - hdV ul) =
        dist p (hdV ul) * dist (hdV (ul.tail)) (hdV ul)
          * (hl (truncateSimplex 1 ul) / Real.sqrt 2) :=
      le_antisymm (le_of_not_gt hnotgt) hge
    have hinner : inner ℝ (p - hdV ul) (hdV (ul.tail) - hdV ul) =
        dist p (hdV ul) * dist (hdV (ul.tail)) (hdV ul)
          * (hl (truncateSimplex 1 ul) / Real.sqrt 2) := by
      rw [inner_eq_dot]; exact heqdot
    have hmem : p ∈ sltZ V ul := by
      simp only [sltZ, Set.mem_union]
      tauto
    exact hpZ.2 hmem
  · rw [mcell1, if_neg hc] at h1
    exact absurd h1 (Set.notMem_empty p)

private theorem p13_hl_pair (u v : V3) : hl [u, v] = dist u v / 2 := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have hcc : circumcenter ({u, v} : Set V3) = midpoint ℝ u v := CIRCUMCENTER_2 u v
  have hexi : ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w := by
    refine ⟨dist (midpoint ℝ u v) u, ?_⟩
    rw [hcc]
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw'
    · rfl
    · rcases Set.mem_singleton_iff.mp hw' with rfl
      simp
  have key : radV ({u, v} : Set V3) = dist (circumcenter ({u, v} : Set V3)) u :=
    (Classical.epsilon_spec (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w) hexi) u (Set.mem_insert u {v})
  have hhl : hl [u, v] = dist (circumcenter ({u, v} : Set V3)) u := by
    show radV (setOfList [u, v]) = _
    rw [hset, key]
  rw [hhl, hcc]
  simp
  ring

/-- `rogers V ul` sits in the closed Voronoi cell of its head vertex. -/
private theorem p13_rogers_subset_voronoiClosed (V : Set V3) (ul : List V3)
    (hb : barV V 3 ul) :
    rogers V ul ⊆ voronoiClosed V (hdV ul) := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  have hbar' : barV V 3 [u0, u1, u2, u3] := hb
  have hmem : ∀ (j : ℕ), j < 4 →
      omegaListN V [u0, u1, u2, u3] j ∈ voronoiClosed V u0 := by
    intro j hj
    interval_cases j
    · show hdV [u0, u1, u2, u3] ∈ voronoiClosed V u0
      rw [show hdV [u0, u1, u2, u3] = u0 from rfl]
      intro w hw
      show dist u0 u0 ≤ dist u0 w
      rw [dist_self]
      exact dist_nonneg
    · have h1 := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 1 hbar' (by norm_num)
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at h1
      have hsub : voronoiList V [u0, u1] ⊆ voronoiClosed V u0 := by
        intro z hz
        have hzv : z ∈ voronoiSet V (setOfList [u0, u1]) := hz
        rw [voronoiSet] at hzv
        rw [Set.mem_sInter] at hzv
        exact hzv (voronoiClosed V u0) ⟨u0, by simp [setOfList], rfl⟩
      exact hsub h1
    · have h1 := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 2 hbar' (by norm_num)
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2] at h1
      have hsub : voronoiList V [u0, u1, u2] ⊆ voronoiClosed V u0 := by
        intro z hz
        have hzv : z ∈ voronoiSet V (setOfList [u0, u1, u2]) := hz
        rw [voronoiSet] at hzv
        rw [Set.mem_sInter] at hzv
        exact hzv (voronoiClosed V u0) ⟨u0, by simp [setOfList], rfl⟩
      exact hsub h1
    · have h1 := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 3 hbar' le_rfl
      rw [TRUNCATE_SIMPLEX_REFL 3 [u0, u1, u2, u3] hbar'.1] at h1
      have hsub : voronoiList V [u0, u1, u2, u3] ⊆ voronoiClosed V u0 := by
        intro z hz
        have hzv : z ∈ voronoiSet V (setOfList [u0, u1, u2, u3]) := hz
        rw [voronoiSet] at hzv
        rw [Set.mem_sInter] at hzv
        exact hzv (voronoiClosed V u0) ⟨u0, by simp [setOfList], rfl⟩
      exact hsub h1
  intro p hp
  rw [rogers] at hp
  refine convexHull_min ?_ (CONVEX_VORONOI_CLOSED V u0) hp
  rintro z ⟨j, hj, rfl⟩
  exact hmem j (by simpa using hj)

/-- Off `Z`, `mcell0` and `mcell2` are disjoint (the `mcell2` far branch
lands on the sphere `B2`). -/
private theorem p13_disjoint_mcell0_mcell2 (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hpZ : p ∈ rogers V ul \ sltZ V ul)
    (h0 : p ∈ mcell 0 V ul) (h2 : p ∈ mcell 2 V ul) : False := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  -- unfold cells before specializing the list
  rw [(MCELL_EXPLICIT 0 V ul).1] at h0
  rw [(MCELL_EXPLICIT 2 V ul).2.2.1] at h2
  have hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := by
    by_contra h
    rw [mcell2, if_neg h] at h2
    exact absurd h2 (Set.notMem_empty p)
  rw [mcell2, if_pos hcond] at h2
  dsimp only at h2
  rw [mcell0] at h0
  -- specialize the list everywhere
  rw [hul] at hb hpZ h0 h2 hcond
  -- mcell0: outside the ball
  have hfar : Real.sqrt 2 ≤ dist p (hdV [u0, u1, u2, u3]) := by
    have := h0.2
    simpa [Metric.mem_ball, not_lt] using this
  set a := hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 with ha
  have hcone1 : p ∈ rconeGe (hdV [u0, u1, u2, u3]) (hdV ([u0, u1, u2, u3].tail)) a := h2.1.1
  have hcone2 : p ∈ rconeGe (hdV ([u0, u1, u2, u3].tail)) (hdV [u0, u1, u2, u3]) a := h2.1.2
  have hhd : hdV [u0, u1, u2, u3] = u0 := rfl
  have htl : hdV ([u0, u1, u2, u3].tail) = u1 := rfl
  rw [hhd, htl] at hcone1 hcone2
  have hrog : p ∈ voronoiClosed V u0 :=
    p13_rogers_subset_voronoiClosed V [u0, u1, u2, u3] hb hpZ.1
  have hu1V : u1 ∈ V := by
    have hsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
    exact hsub (by simp [setOfList])
  have hle : dist p u0 ≤ dist p u1 := hrog u1 hu1V
  have hc1 : (p - u0) ⬝ᵥ (u1 - u0) ≥ dist p u0 * dist u1 u0 * a := hcone1
  have hc2 : (p - u1) ⬝ᵥ (u0 - u1) ≥ dist p u1 * dist u0 u1 * a := hcone2
  have hc1i : inner ℝ (p - u0) (u1 - u0) ≥ dist p u0 * dist u1 u0 * a := by
    rw [inner_eq_dot]; exact hc1
  have hc2i : inner ℝ (p - u1) (u0 - u1) ≥ dist p u1 * dist u0 u1 * a := by
    rw [inner_eq_dot]; exact hc2
  set e := dist u0 u1 with he
  set x := dist p u0 with hx
  set y := dist p u1 with hy
  have hes : dist u1 u0 = e := by rw [he, dist_comm]
  have hsum : e ^ 2 ≥ a * e * (x + y) := by
    have hdot : inner ℝ (p - u0) (u1 - u0) + inner ℝ (p - u1) (u0 - u1)
        = inner ℝ (u1 - u0) (u1 - u0) := by
      have h1 : (p - u1 : V3) = (p - u0) - (u1 - u0) := by module
      have h2 : (u0 - u1 : V3) = -(u1 - u0) := by module
      rw [h1, h2]
      simp only [inner_sub_left, inner_neg_right]
      ring
    have hab : dist p u0 * dist u1 u0 * a + dist p u1 * dist u0 u1 * a
        = a * e * (x + y) := by
      rw [hes, he, hx, hy]; ring
    have hcc : inner ℝ (u1 - u0) (u1 - u0) = e ^ 2 := by
      rw [real_inner_self_eq_norm_sq, he, dist_eq_norm, norm_sub_rev]
    have hadd := add_le_add hc1i hc2i
    rw [hab, hdot, hcc] at hadd
    exact hadd
  have hepos : 0 < e := by
    rw [he]
    exact dist_pos.mpr (p13_barV_hd_ne V u0 u1 u2 u3 hb)
  have hapos : 0 < a := by
    rw [ha]
    exact div_pos (BARV_IMP_HL_1_POS_LT V [u0, u1, u2, u3] hs hp hb)
      (Real.sqrt_pos.2 (by norm_num))
  have hhea : e / a = 2 * Real.sqrt 2 := by
    have h1 : hl (truncateSimplex 1 [u0, u1, u2, u3]) = e / 2 := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2, he, p13_hl_pair u0 u1]
    rw [ha, h1]
    field_simp
  have hxy : x + y ≤ 2 * Real.sqrt 2 := by
    have h1 : e * e ≥ a * e * (x + y) := by simpa [pow_two] using hsum
    have h2 : e ≥ a * (x + y) := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hepos))
      field_simp at h3
      linarith
    have h3 : x + y ≤ e / a := by
      rw [le_div_iff₀ hapos]
      simpa [mul_comm] using h2
    rwa [hhea] at h3
  have hxle : x ≤ y := hle
  have hx2 : x ≤ Real.sqrt 2 := by nlinarith [hxy, hxle]
  have hxeq : x = Real.sqrt 2 := le_antisymm hx2 hfar
  have hdpx : dist p (hdV [u0, u1, u2, u3]) = Real.sqrt 2 := by
    rw [hhd, ← hx]
    exact hxeq
  have hB2 : p ∈ {w : V3 | ‖w - hdV [u0, u1, u2, u3]‖ = Real.sqrt 2} := by
    simpa [dist_eq_norm] using hdpx
  have hmem : p ∈ sltZ V [u0, u1, u2, u3] := by
    simp only [sltZ, Set.mem_union]
    tauto
  exact hpZ.2 hmem



/-! ## shared affine/linear framework for B8c-e -/

/-- Uniqueness of affine coordinates in a 4-point basis, phrased through
linear independence of the three differences from the fourth point. -/
private theorem p13t_aff_coords_unique {a b c d p : V3}
    (hli : LinearIndependent ℝ ![a - d, b - d, c - d])
    {k1 k2 k3 k4 m1 m2 m3 m4 : ℝ}
    (hsum : k1 + k2 + k3 + k4 = 1)
    (hsum' : m1 + m2 + m3 + m4 = 1)
    (hp : p = k1 • a + k2 • b + k3 • c + k4 • d)
    (hp' : p = m1 • a + m2 • b + m3 • c + m4 • d) :
    k1 = m1 ∧ k2 = m2 ∧ k3 = m3 ∧ k4 = m4 := by
  have h0 : (k1 - m1) • a + (k2 - m2) • b + (k3 - m3) • c + (k4 - m4) • d = 0 := by
    have hsub : (k1 • a + k2 • b + k3 • c + k4 • d) -
        (m1 • a + m2 • b + m3 • c + m4 • d) = 0 := by
      rw [← hp, ← hp', sub_self]
    calc (k1 - m1) • a + (k2 - m2) • b + (k3 - m3) • c + (k4 - m4) • d
        = (k1 • a + k2 • b + k3 • c + k4 • d) -
          (m1 • a + m2 • b + m3 • c + m4 • d) := by module
      _ = 0 := hsub
  have hsumdiff : (k1 - m1) + (k2 - m2) + (k3 - m3) + (k4 - m4) = 0 := by linarith
  have hrel : (k1 - m1) • (a - d) + (k2 - m2) • (b - d) + (k3 - m3) • (c - d) = 0 := by
    calc (k1 - m1) • (a - d) + (k2 - m2) • (b - d) + (k3 - m3) • (c - d)
        = ((k1 - m1) • a + (k2 - m2) • b + (k3 - m3) • c + (k4 - m4) • d)
          - ((k1 - m1) + (k2 - m2) + (k3 - m3) + (k4 - m4)) • d := by module
      _ = 0 := by rw [h0, hsumdiff, zero_smul, sub_zero]
  have hw : (∑ i : Fin 3, (![k1 - m1, k2 - m2, k3 - m3] : Fin 3 → ℝ) i •
      (![a - d, b - d, c - d] : Fin 3 → V3) i) = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hrel
  have hz := (Fintype.linearIndependent_iff.mp hli) ![k1 - m1, k2 - m2, k3 - m3] hw
  have h1 : k1 - m1 = 0 := by simpa using hz 0
  have h2 : k2 - m2 = 0 := by simpa using hz 1
  have h3 : k3 - m3 = 0 := by simpa using hz 2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Inserting a point outside the affine span raises the affine dimension by
one (copy of PA6's private `p6_affDim_insert`). -/
private theorem p13t_affDim_insert (S : Set V3) (y : V3) (hne : S.Nonempty)
    (hy : y ∉ (affineSpan ℝ S : Set V3)) :
    affDim (insert y S) = affDim S + 1 := by
  obtain ⟨y0, hy0⟩ := hne
  have hy0S : y0 ∈ (affineSpan ℝ S : Set V3) := subset_affineSpan ℝ S hy0
  set D := vectorSpan ℝ S with hD
  have mD : ∀ a ∈ S, ∀ b ∈ S, (a - b) ∈ D := by
    intro a ha b hb
    rw [hD, vectorSpan_def]
    exact Submodule.subset_span (Set.mem_vsub.2 ⟨a, ha, b, hb, rfl⟩)
  have hvec : vectorSpan ℝ (insert y S) = D ⊔ Submodule.span ℝ {y - y0} := by
    have hgen : (y - y0) ∈ vectorSpan ℝ (insert y S) := by
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨y, Set.mem_insert _ _,
        y0, Set.mem_insert_of_mem _ hy0, rfl⟩)
    have hmono : vectorSpan ℝ S ≤ vectorSpan ℝ (insert y S) :=
      vectorSpan_mono (k := ℝ) (Set.subset_insert y S)
    have hsb : ∀ r ∈ Submodule.span ℝ {y - y0}, r ∈ vectorSpan ℝ (insert y S) := by
      intro r hm
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      exact Submodule.smul_mem _ s hgen
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      intro g hg
      obtain ⟨x, hx, x', hx', rfl⟩ := Set.mem_vsub.1 hg
      rw [SetLike.mem_coe]
      rcases Set.mem_insert_iff.1 hx with hxe | hx
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe, hxe', vsub_self]
          exact Submodule.zero_mem _
        · rw [hxe, vsub_eq_sub]
          have hv : (y - x' : V3) = (y - y0) + -(x' - y0) := by abel
          have hA : (x' - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x' hx' y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hC
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hA)
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe', vsub_eq_sub]
          have hv : (x - y : V3) = (x - y0) + -(y - y0) := by abel
          have hA : (x - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x hx y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hA
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hC)
        · exact Submodule.mem_sup_left (mD x hx x' hx')
    · intro w hw
      rcases Submodule.mem_sup.1 hw with ⟨a, ha, b, hb, hab⟩
      have haD : a ∈ vectorSpan ℝ (insert y S) := hmono ha
      have hbD : b ∈ vectorSpan ℝ (insert y S) := hsb b hb
      rw [← hab]
      exact add_mem haD hbD
  have hvD : y - y0 ∉ D := by
    intro h
    apply hy
    have hmem : (y - y0) +ᵥ y0 ∈ (affineSpan ℝ S : Set V3) :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact h) hy0S
    have h2 : (y - y0 : V3) +ᵥ y0 = y := by rw [vadd_eq_add]; abel
    rw [h2] at hmem
    exact hmem
  have hinf : D ⊓ Submodule.span ℝ {y - y0} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwK : w ∈ D := (Submodule.mem_inf.1 hw).1
    have hwS := (Submodule.mem_inf.1 hw).2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hwS
    have hs0 : s = 0 := by
      by_contra hs0
      have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
      have h2 : (s⁻¹ • (s • (y - y0)) : V3) ∈ D := Submodule.smul_mem _ _ hwK
      rw [smul_smul, hinv, one_smul] at h2
      exact hvD h2
    rw [hs0, zero_smul]
  have hvyne : (y - y0 : V3) ≠ 0 := by
    intro h0
    rw [h0] at hvD
    exact hvD (Submodule.zero_mem D)
  have hfr : Module.finrank ℝ (vectorSpan ℝ (insert y S))
      = Module.finrank ℝ (vectorSpan ℝ S) + 1 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq D (Submodule.span ℝ {y - y0})
    rw [hinf, finrank_bot] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {y - y0}) = 1 :=
      finrank_span_singleton hvyne
    rw [h3] at h2
    rw [hvec]
    omega
  have hneI : (insert y S).Nonempty := ⟨y0, Set.mem_insert_of_mem _ hy0⟩
  have hneI' : insert y S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hneI
  simp only [affDim, if_neg hneI', if_neg (Set.nonempty_iff_ne_empty.mp ⟨y0, hy0⟩)]
  rw [hfr]
  omega


/-- Monotonicity of the Voronoi list in the defining list's point set. -/
private theorem p13t_voronoiList_mono {V : Set V3} {vl ul : List V3}
    (h : setOfList vl ⊆ setOfList ul) : voronoiList V ul ⊆ voronoiList V vl := by
  intro x hx
  rw [voronoiList, voronoiSet, Set.mem_sInter] at hx ⊢
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hs
  exact hx (voronoiClosed V v) ⟨v, h hv, rfl⟩

/-- In a `barV V 2 [a,b,c]` list the three points are pairwise distinct
(set-equality of Voronoi lists forces equal affine dimensions). -/
private theorem p13t_barV2_ne (V : Set V3) (a b c : V3) (hb : barV V 2 [a,b,c]) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hv3 : voronoiNondg V [a,b,c] := hb.2 [a,b,c] ⟨⟨[], by simp⟩, by simp⟩
  have h3 : affDim (voronoiList V [a,b,c]) + 3 = 4 := hv3.2.2
  have hv2 : voronoiNondg V [a,b] := hb.2 [a,b] ⟨⟨[c], rfl⟩, by simp⟩
  have h2 : affDim (voronoiList V [a,b]) + 2 = 4 := hv2.2.2
  have hv1 : voronoiNondg V [a] := hb.2 [a] ⟨⟨[b,c], rfl⟩, by simp⟩
  have h1 : affDim (voronoiList V [a]) + 1 = 4 := hv1.2.2
  have hset1 : setOfList [a,a] = setOfList [a] := by ext x; simp [setOfList]; try tauto
  have hset2 : setOfList [a,b,a] = setOfList [a,b] := by ext x; simp [setOfList]; try tauto
  have hset3 : setOfList [a,b,b] = setOfList [a,b] := by ext x; simp [setOfList]; try tauto
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst he
    have hset : voronoiList V [a,a] = voronoiList V [a] := by
      unfold voronoiList; rw [hset1]
    rw [hset] at h2
    omega
  · intro he
    subst he
    have hset : voronoiList V [a,b,a] = voronoiList V [a,b] := by
      unfold voronoiList; rw [hset2]
    rw [hset] at h3
    omega
  · intro he
    subst he
    have hset : voronoiList V [a,b,b] = voronoiList V [a,b] := by
      unfold voronoiList; rw [hset3]
    rw [hset] at h3
    omega

/-- `s2 = omegaListN .. 2` is the circumcenter of the triangle. -/
private theorem p13t_omega2_cc (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hbar2 : barV V 2 [u0,u1,u2]) (h2lt : hl [u0,u1,u2] < Real.sqrt 2) :
    omegaListN V [u0,u1,u2,u3] 2 = circumcenter (setOfList [u0,u1,u2]) := by
  rw [OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3]
  exact XNHPWAB1 V [u0,u1,u2] 2 hp hbar2 h2lt

/-- Distance from `u0` to `omegaListN .. 2` is the triangle circumradius. -/
private theorem p13t_omega2_dist (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hbar2 : barV V 2 [u0,u1,u2]) (h2lt : hl [u0,u1,u2] < Real.sqrt 2) :
    dist u0 (omegaListN V [u0,u1,u2,u3] 2) = hl [u0,u1,u2] := by
  rw [p13t_omega2_cc V u0 u1 u2 u3 hp hbar2 h2lt]
  have h := HL_EQ_DIST0 V 2 [u0,u1,u2] hp hbar2
  rw [show hdV [u0,u1,u2] = u0 from rfl] at h
  calc dist u0 (circumcenter (setOfList [u0,u1,u2]))
      = dist (circumcenter (setOfList [u0,u1,u2])) u0 := dist_comm ..
    _ = hl [u0,u1,u2] := h.symm

/-- A point of the triangle's Voronoi list farther from `u0` than the
circumradius cannot lie in the triangle's affine hull. -/
private theorem p13t_notMem_aff_of_vor (V : Set V3) (u0 u1 u2 : V3) (x : V3)
    (hp : Packing V) (hbar2 : barV V 2 [u0,u1,u2])
    (hxvor : x ∈ voronoiList V [u0,u1,u2])
    (hxfar : hl [u0,u1,u2] < dist u0 x) :
    x ∉ (affineSpan ℝ ({u0,u1,u2} : Set V3) : Set V3) := by
  intro hmem
  have hset : ({u0,u1,u2} : Set V3) = setOfList [u0,u1,u2] := by ext x; simp [setOfList]
  have hmem' : x ∈ (affineSpan ℝ (setOfList [u0,u1,u2]) : Set V3) := by
    rwa [hset] at hmem
  have hperp := MHFTTZN4 V [u0,u1,u2] 2 x x hp hbar2
    (subset_affineSpan ℝ _ hxvor) hmem'
  have hxcc : x = circumcenter (setOfList [u0,u1,u2]) := by
    have hz : inner ℝ (x - circumcenter (setOfList [u0,u1,u2]))
        (x - circumcenter (setOfList [u0,u1,u2])) = 0 := by
      rw [inner_eq_dot]; exact hperp
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  have hd : dist u0 x = hl [u0,u1,u2] := by
    rw [hxcc]
    have h := HL_EQ_DIST0 V 2 [u0,u1,u2] hp hbar2
    rw [show hdV [u0,u1,u2] = u0 from rfl] at h
    calc dist u0 (circumcenter (setOfList [u0,u1,u2]))
        = dist (circumcenter (setOfList [u0,u1,u2])) u0 := dist_comm ..
      _ = hl [u0,u1,u2] := h.symm
  linarith


/-- Linear independence of the three differences for four points of which the
last is outside the affine hull of the first three. -/
private theorem p13t_li_triple (u0 u1 u2 s : V3)
    (hdim3 : affDim ({u0,u1,u2} : Set V3) = 2)
    (hsnot : s ∉ (affineSpan ℝ ({u0,u1,u2} : Set V3) : Set V3))
    (hu02 : u0 ≠ u2) (hu12 : u1 ≠ u2) (hs2 : s ≠ u2) (hu01 : u0 ≠ u1)
    (hs0 : u0 ≠ s) (hs1 : u1 ≠ s) :
    LinearIndependent ℝ ![u0 - u2, u1 - u2, s - u2] := by
  have hcard : (Nat.card ({u0,u1,u2,s} : Set V3) : ℤ)
      ≤ affDim ({u0,u1,u2,s} : Set V3) + 1 := by
    have hnat : Nat.card ({u0,u1,u2,s} : Set V3) ≤ 4 := by
      have hE : ({u0,u1,u2,s} : Set V3) = (({u0,u1,u2,s} : Finset V3) : Set V3) := by
        ext x; simp
      rw [hE, Nat.card_coe_set_eq, ncard_coe_finset]
      have hsub : ({u0,u1,u2,s} : Finset V3) ⊆ ([u0,u1,u2,s] : List V3).toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
          List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto
      calc ({u0,u1,u2,s} : Finset V3).card
          ≤ ([u0,u1,u2,s] : List V3).toFinset.card := Finset.card_le_card hsub
        _ ≤ ([u0,u1,u2,s] : List V3).length := List.toFinset_card_le _
        _ = 4 := rfl
    have hd4 : affDim ({u0,u1,u2,s} : Set V3) = 3 := by
      have hins : ({u0,u1,u2,s} : Set V3) = insert s ({u0,u1,u2} : Set V3) := by
        ext x; simp; tauto
      rw [hins, p13t_affDim_insert _ _ ⟨u0, by simp⟩ hsnot, hdim3]
      norm_num
    rw [hd4]
    omega
  have hfin : ({u0,u1,u2,s} : Set V3).Finite := by simp
  have hind4 : ¬affineDependent ({u0,u1,u2,s} : Set V3) :=
    p6_affdep_of_dim _ hfin hcard
  have hliSet := AFFINE_INDEPENDENT_IMP_INDEPENDENT ({u0,u1,u2,s} : Set V3) hind4 u2
    (by simp)
  let e : Fin 3 ↪ {y // y ∈ ({u0,u1,u2,s} : Set V3) \ {u2}} :=
  { toFun := fun i =>
      match i with
      | 0 => ⟨u0, by simp [hu02]⟩
      | 1 => ⟨u1, by simp [hu12]⟩
      | 2 => ⟨s, by simp [hs2]⟩
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        have h : u0 = u1 := by simpa using congrArg Subtype.val hij
        exact hu01 h
      · exfalso
        have h : u0 = s := by simpa using congrArg Subtype.val hij
        exact hs0 h
      · exfalso
        have h : u1 = u0 := by simpa using congrArg Subtype.val hij
        exact hu01 h.symm
      · rfl
      · exfalso
        have h : u1 = s := by simpa using congrArg Subtype.val hij
        exact hs1 h
      · exfalso
        have h : s = u0 := by simpa using congrArg Subtype.val hij
        exact hs0 h.symm
      · exfalso
        have h : s = u1 := by simpa using congrArg Subtype.val hij
        exact hs1 h.symm
      · rfl }
  have hcomp := hliSet.comp e e.injective
  have hfun : ((fun y : {y // y ∈ ({u0,u1,u2,s} : Set V3) \ {u2}} =>
      (y : V3) - u2) ∘ e) = ![u0 - u2, u1 - u2, s - u2] := by
    funext i; fin_cases i <;> rfl
  rwa [hfun] at hcomp

/-- Affine coordinates from linear independence of the differences from
the base point `c`: if a linear combination of `{a,b,c,d}` with zero
coefficient sum vanishes, then all coefficients vanish. -/
private theorem p13t_aff_eq_zero {a b c d : V3}
    (hli : LinearIndependent ℝ ![a - c, b - c, d - c])
    {A B C D : ℝ} (hsum : A + B + C + D = 0)
    (h : A • a + B • b + C • c + D • d = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hrel : A • (a - c) + B • (b - c) + D • (d - c) = 0 := by
    calc A • (a - c) + B • (b - c) + D • (d - c)
        = (A • a + B • b + C • c + D • d) - (A + B + C + D) • c := by
          module
      _ = 0 := by rw [h, hsum, zero_smul, sub_zero]
  have hw : (∑ i : Fin 3, (![A, B, D] : Fin 3 → ℝ) i •
      (![a - c, b - c, d - c] : Fin 3 → V3) i) = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hrel
  have hz := (Fintype.linearIndependent_iff.mp hli) ![A, B, D] hw
  have hA : A = 0 := by simpa using hz 0
  have hB : B = 0 := by simpa using hz 1
  have hD : D = 0 := by simpa using hz 2
  exact ⟨hA, hB, by linarith, hD⟩

/-- Swap of the base point in a linear independence statement for three
differences: `![a-c,b-c,d-c]` independent implies `![a-d,b-d,c-d]`
independent.  (The change of basis is `a-d = (a-c)-(d-c)`, etc.) -/
private theorem p13t_li_base_swap {a b c d : V3}
    (hli : LinearIndependent ℝ ![a - c, b - c, d - c]) :
    LinearIndependent ℝ ![a - d, b - d, c - d] := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hg' : g 0 • (a - d) + g 1 • (b - d) + g 2 • (c - d) = 0 := by
    rw [Fin.sum_univ_three] at hg
    simpa using hg
  have hrel : g 0 • (a - c) + g 1 • (b - c) + (-(g 0) - g 1 - g 2) • (d - c)
      = 0 := by
    have hexp : g 0 • (a - c) + g 1 • (b - c) + (-(g 0) - g 1 - g 2) • (d - c)
        = g 0 • (a - d) + g 1 • (b - d) + g 2 • (c - d) := by
      module
    rw [hexp]; exact hg'
  have hw : (∑ i : Fin 3,
      (![g 0, g 1, -(g 0) - g 1 - g 2] : Fin 3 → ℝ) i •
        (![a - c, b - c, d - c] : Fin 3 → V3) i) = 0 := by
    rw [Fin.sum_univ_three]
    simpa using hrel
  have hz := hli ![g 0, g 1, -(g 0) - g 1 - g 2] hw
  have h0 : g 0 = 0 := by simpa using hz 0
  have h1 : g 1 = 0 := by simpa using hz 1
  have h2 : g 2 = 0 := by
    have hz2 := hz 2
    simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hz2
    linarith
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- HOL `CONVEX_HULL_KY_LEMMA_5` (marchal2.hl:3536), affine-coordinate
form.  If `{a,b,c,d}` is affinely independent (LI of the differences from
`d`), `x ∈ hull{a,b,c}` lies off the line `ab`, and `d ∈ [x,y]`, then
`hull{a,b,c,d} ∩ hull{a,b,x,y} ⊆ hull{a,b,x,d}`. -/
private theorem p13t_hull_ky5 (a b c d x y p : V3)
    (hli : LinearIndependent ℝ ![a - d, b - d, c - d])
    (hdx : d ≠ x)
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set V3))
    (hxab : x ∉ (affineSpan ℝ ({a, b} : Set V3) : Set V3))
    (hseg : d ∈ segment ℝ x y)
    (hpd : p ∈ convexHull ℝ ({a, b, c, d} : Set V3))
    (hpxy : p ∈ convexHull ℝ ({a, b, x, y} : Set V3)) :
    p ∈ convexHull ℝ ({a, b, x, d} : Set V3) := by
  have hx4 : x ∈ convexHull ℝ ({a, b, c, c} : Set V3) := by
    rw [show ({a, b, c, c} : Set V3) = {a, b, c} from by ext z; simp]
    exact hx
  rw [CONVEX_HULL_4] at hx4
  obtain ⟨νa, νb, νc, νc', hνa, hνb, hνc, hνc', hνsum, hxeq⟩ := hx4
  have hxrepr : x = νa • a + νb • b + (νc + νc') • c := by
    rw [hxeq]; module
  rw [CONVEX_HULL_4] at hpxy
  obtain ⟨lA, lB, lX, lY, hlA, hlB, hlX, hlY, hlsum, hpeq⟩ := hpxy
  rw [mem_segment_iff_div] at hseg
  obtain ⟨α, β, hα, hβ, hαβ, hdiv⟩ := hseg
  set τ : ℝ := α / (α + β) with hτdef
  set η : ℝ := β / (α + β) with hηdef
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hτη : τ + η = 1 := by
    rw [hτdef, hηdef, ← add_div]
    field_simp
  have hηpos : 0 < η := by
    rcases lt_or_eq_of_le hη0 with h | h
    · exact h
    · exfalso
      have hηz : η = 0 := h.symm
      have hβ0 : β = 0 := by
        have hzero : β / (α + β) = 0 := by
          rw [← hηdef]; exact hηz
        rcases div_eq_zero_iff.mp hzero with h' | h'
        · exact h'
        · linarith
      have hτ1 : τ = 1 := by linarith [hτη, hηz]
      apply hdx
      calc d = τ • x + η • y := hdiv.symm
        _ = x := by rw [hτ1, hηz, one_smul, zero_smul, add_zero]
  have hyeq : y = η⁻¹ • (d - τ • x) := by
    have h1 : τ • x + η • y = d := hdiv
    have h2 : η • y = d - τ • x := by rw [← h1]; abel
    rw [← h2, smul_smul, inv_mul_cancel₀ (ne_of_gt hηpos), one_smul]
  have hy1 : lY * η⁻¹ = lY / η := by rw [div_eq_mul_inv]
  have hy2 : lY * η⁻¹ * τ = lY * τ / η := by rw [div_eq_mul_inv]; ring
  set μx : ℝ := lX - lY * τ / η with hμxdef
  have hp1 : p = lA • a + lB • b + μx • x + (lY / η) • d := by
    rw [hpeq, hyeq, hμxdef, smul_smul, smul_sub, smul_smul, hy2, hy1]
    module
  have hsumμ : lA + lB + μx + lY / η = 1 := by
    have h1 : lY / η + -(lY * τ / η) = lY := by
      have h2 : lY / η + -(lY * τ / η) = lY * (1 - τ) / η := by ring
      rw [h2, show 1 - τ = η from by linarith [hτη]]
      exact mul_div_cancel_right₀ lY (ne_of_gt hηpos)
    rw [hμxdef]
    linarith
  rw [CONVEX_HULL_4] at hpd
  obtain ⟨κa, κb, κc, κd, hκa, hκb, hκc, hκd, hκsum, hκeq⟩ := hpd
  have hp2 : p = (lA + μx * νa) • a + (lB + μx * νb) • b
      + (μx * (νc + νc')) • c + (lY / η) • d := by
    rw [hp1, hxrepr]
    module
  have hsum2 : (lA + μx * νa) + (lB + μx * νb) + (μx * (νc + νc'))
      + (lY / η) = 1 := by
    have h1 : (lA + μx * νa) + (lB + μx * νb) + (μx * (νc + νc'))
        + (lY / η)
        = (lA + lB + μx + lY / η) + μx * (νa + νb + νc + νc' - 1) := by
      ring
    rw [h1, hsumμ, hνsum]; ring
  have hcoef := p13t_aff_coords_unique hli hsum2 hκsum hp2 hκeq
  have hμν : μx * (νc + νc') = κc := hcoef.2.2.1
  have hνcpos : 0 < νc + νc' := by
    rcases lt_or_eq_of_le (add_nonneg hνc hνc') with h | h
    · exact h
    · exfalso
      apply hxab
      have hνcz : νc = 0 := by linarith
      have hνc'z : νc' = 0 := by linarith
      have hab : x = νa • a + νb • b := by
        rw [hxrepr, hνcz, hνc'z]
        simp
      have hsumab : νa + νb = 1 := by linarith [hνsum, hνcz, hνc'z]
      have hmem : x ∈ convexHull ℝ ({a, b} : Set V3) := by
        rw [convexHull_pair]
        exact ⟨νa, νb, hνa, hνb, hsumab, hab.symm⟩
      exact convexHull_subset_affineSpan _ hmem
  have hμx0 : 0 ≤ μx := by
    have hprod : 0 ≤ μx * (νc + νc') := by
      rw [hμν]; exact hκc
    exact nonneg_of_mul_nonneg_left hprod hνcpos
  rw [CONVEX_HULL_4]
  exact ⟨lA, lB, μx, lY / η, hlA, hlB, hμx0, div_nonneg hlY hηpos.le,
    hsumμ, hp1⟩

/-- Affine-coordinate uniqueness in the omega basis `{u0,s1,s2,s3}`, where
`s1` is the midpoint of `u0,u1` and `s2` has a nonzero `u2` coordinate
(`{u0,u1,u2,s3}` being affinely independent).  The matrices are triangular
after substituting `s1 = (u0+u1)/2` and `s2 = m0 u0 + m1 u1 + m2 u2`. -/
private theorem p13t_omega_coords_unique {u0 u1 u2 s1 s2 s3 p : V3}
    (hli : LinearIndependent ℝ ![u0 - u2, u1 - u2, s3 - u2])
    (hs1 : s1 = midpoint ℝ u0 u1)
    {m0 m1 m2 : ℝ} (hm2 : m2 ≠ 0) (hmsum : m0 + m1 + m2 = 1)
    (hs2 : s2 = m0 • u0 + m1 • u1 + m2 • u2)
    {k0 k1 k2 k3 l0 l1 l2 l3 : ℝ}
    (hsumk : k0 + k1 + k2 + k3 = 1)
    (hsuml : l0 + l1 + l2 + l3 = 1)
    (hpk : p = k0 • u0 + k1 • s1 + k2 • s2 + k3 • s3)
    (hpl : p = l0 • u0 + l1 • s1 + l2 • s2 + l3 • s3) :
    k0 = l0 ∧ k1 = l1 ∧ k2 = l2 ∧ k3 = l3 := by
  have hrel : (k0 - l0) • u0 + (k1 - l1) • s1 + (k2 - l2) • s2
      + (k3 - l3) • s3 = 0 := by
    calc (k0 - l0) • u0 + (k1 - l1) • s1 + (k2 - l2) • s2 + (k3 - l3) • s3
        = (k0 • u0 + k1 • s1 + k2 • s2 + k3 • s3)
          - (l0 • u0 + l1 • s1 + l2 • s2 + l3 • s3) := by module
      _ = 0 := by rw [← hpk, ← hpl, sub_self]
  have hs1half : s1 = (1/2 : ℝ) • u0 + (1/2 : ℝ) • u1 := by
    rw [hs1, midpoint_eq_smul_add, show (⅟(2:ℝ)) = (1/2:ℝ) from by norm_num]
    module
  have hsub : (k0 - l0) • u0 + (k1 - l1) • s1 + (k2 - l2) • s2
      + (k3 - l3) • s3
      = ((k0 - l0) + (k1 - l1) / 2 + (k2 - l2) * m0) • u0
        + ((k1 - l1) / 2 + (k2 - l2) * m1) • u1
        + ((k2 - l2) * m2) • u2 + (k3 - l3) • s3 := by
    rw [hs1half, hs2]
    module
  have hrel' : ((k0 - l0) + (k1 - l1) / 2 + (k2 - l2) * m0) • u0
      + ((k1 - l1) / 2 + (k2 - l2) * m1) • u1
      + ((k2 - l2) * m2) • u2 + (k3 - l3) • s3 = 0 := by
    rw [← hsub]; exact hrel
  have hsum0 : ((k0 - l0) + (k1 - l1) / 2 + (k2 - l2) * m0)
      + ((k1 - l1) / 2 + (k2 - l2) * m1) + ((k2 - l2) * m2) + (k3 - l3) = 0 := by
    have h1 : ((k0 - l0) + (k1 - l1) / 2 + (k2 - l2) * m0)
        + ((k1 - l1) / 2 + (k2 - l2) * m1) + ((k2 - l2) * m2) + (k3 - l3)
        = (k0 - l0) + (k1 - l1) + (k2 - l2) * (m0 + m1 + m2) + (k3 - l3) := by
      ring
    rw [h1, hmsum, mul_one]
    linarith
  have hzero := p13t_aff_eq_zero hli hsum0 hrel'
  obtain ⟨hA, hB, hC, hD⟩ := hzero
  have h2eq : k2 = l2 := by
    have hC' : (k2 - l2) * m2 = 0 := hC
    rcases mul_eq_zero.mp hC' with h | h
    · linarith
    · exact absurd h hm2
  have h1eq : k1 = l1 := by
    have hB' : (k1 - l1) / 2 + (k2 - l2) * m1 = 0 := hB
    rw [h2eq, sub_self, zero_mul, add_zero] at hB'
    linarith
  have h3eq : k3 = l3 := by linarith
  have h0eq : k0 = l0 := by
    have hA' : (k0 - l0) + (k1 - l1) / 2 + (k2 - l2) * m0 = 0 := hA
    rw [h1eq, h2eq] at hA'
    ring_nf at hA'
    linarith
  exact ⟨h0eq, h1eq, h2eq, h3eq⟩

/-- The circumcenter of a triangle `{u0,u1,u2}` is not on the line `u0u1`
when its circumradius strictly exceeds the half-length of `u0u1`. -/
private theorem p13t_circ2_notMem_aff_pair (V : Set V3) (u0 u1 u2 : V3)
    (hp : Packing V) (hbar2 : barV V 2 [u0, u1, u2])
    (hlt : hl [u0, u1, u2] < Real.sqrt 2) (hu01 : u0 ≠ u1) :
    circumcenter (setOfList [u0, u1, u2]) ∉
      (affineSpan ℝ ({u0, u1} : Set V3) : Set V3) := by
  intro hmem
  obtain ⟨c, hc⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq
    (p := circumcenter (setOfList [u0, u1, u2]))
    (p₁ := u0) (p₂ := u1)).mp hmem
  have hc' : circumcenter (setOfList [u0, u1, u2])
      = (1 - c) • u0 + c • u1 := by
    rw [← hc, AffineMap.lineMap_apply_module]
  set cc := circumcenter (setOfList [u0, u1, u2]) with hccdef
  have hd0 := HL_PROPERTIES V [u0, u1, u2] 2 hp hbar2 u0 (by simp [setOfList])
  have hd1 := HL_PROPERTIES V [u0, u1, u2] 2 hp hbar2 u1 (by simp [setOfList])
  have hdpos : 0 < dist u1 u0 := dist_pos.mpr (Ne.symm hu01)
  have e0 : dist cc u0 = |c| * dist u1 u0 := by
    rw [hc', dist_eq_norm]
    have he : (1 - c) • u0 + c • u1 - u0 = c • (u1 - u0) := by module
    rw [he, norm_smul, Real.norm_eq_abs]
    rw [show dist u1 u0 = ‖u1 - u0‖ from dist_eq_norm u1 u0]
  have e1 : dist cc u1 = |1 - c| * dist u1 u0 := by
    rw [hc', dist_eq_norm]
    have he : (1 - c) • u0 + c • u1 - u1 = (1 - c) • (u0 - u1) := by module
    have he2 : (1 - c) • (u0 - u1) = -((1 - c) • (u1 - u0)) := by module
    rw [he, he2, norm_neg, norm_smul, Real.norm_eq_abs]
    rw [show dist u1 u0 = ‖u1 - u0‖ from dist_eq_norm u1 u0]
  have habs : |c| = |1 - c| := by
    have h1 : dist cc u0 = dist cc u1 := by rw [hd0, hd1]
    rw [e0, e1] at h1
    exact mul_right_cancel₀ (ne_of_gt hdpos) h1
  have hc12 : c = 1/2 := by
    rcases abs_eq_abs.mp habs with h | h
    · linarith
    · linarith
  have hd : dist cc u0 = hl [u0, u1] := by
    rw [e0, hc12]
    rw [show |(1/2:ℝ)| = 1/2 from by norm_num]
    rw [p13_hl_pair u0 u1, dist_comm u1 u0]
    ring
  have hstrict : hl [u0, u1] < hl [u0, u1, u2] := by
    have h4 := XNHPWAB4 V [u0, u1, u2] 2 hp hbar2 hlt 1 2
      (by norm_num) (by norm_num)
    rwa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u2).1] at h4
  have h2eq : hl [u0, u1] = hl [u0, u1, u2] := by rw [← hd, hd0]
  linarith

/-- (2,3): `mcell2 ∩ mcell3` off `Z` lands in `B4 = aff{u0,u1,mxi}`. -/
private theorem p13t_mcell2_mcell3_subset_Z (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (h2 : p ∈ mcell 2 V ul) (h3 : p ∈ mcell 3 V ul) : p ∈ sltZ V ul := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  rw [(MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1] at h2
  rw [(MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1] at h3
  have hTR2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hcond2 : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra h
    rw [mcell2, if_neg h] at h2
    exact absurd h2 (Set.notMem_empty p)
  rw [mcell2, if_pos hcond2] at h2
  dsimp only at h2
  have hcond3 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra h
    rw [mcell3, if_neg h] at h3
    exact absurd h3 (Set.notMem_empty p)
  rw [mcell3, if_pos hcond3] at h3
  have hbar2 : barV V 2 [u0, u1, u2] := by
    rw [← hTR2]
    exact TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
  have h2lt : hl [u0, u1, u2] < Real.sqrt 2 := by
    rw [← hTR2]; exact hcond3.1
  have hH : Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := hcond3.2
  obtain ⟨s, hseg, hdist, hsm⟩ :=
    MXI_EXPLICIT_OLD V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl hcond3.1 hH
  have hdist' : dist u0 s = Real.sqrt 2 := by simpa using hdist
  have h3h0 : p ∈ convexHull ℝ (setOfList [u0, u1, u2] ∪
      ({mxi V [u0, u1, u2, u3]} : Set V3)) := by
    simpa [hTR2] using h3
  have h3h : p ∈ convexHull ℝ ({u0, u1, u2, s} : Set V3) := by
    have hset : setOfList [u0, u1, u2] ∪ ({mxi V [u0, u1, u2, u3]} : Set V3)
        = ({u0, u1, u2, s} : Set V3) := by
      ext x
      simp [setOfList, ← hsm]
      try tauto
    rwa [hset] at h3h0
  have hs2cc := p13t_omega2_cc V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2dist := p13t_omega2_dist V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2hull : omegaListN V [u0, u1, u2, u3] 2 ∈
      convexHull ℝ (setOfList [u0, u1, u2]) := by
    rw [OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3]
    exact XNHPWAB2 V [u0, u1, u2] 2 hp hbar2 h2lt
  have hs2hull' : omegaListN V [u0, u1, u2, u3] 2 ∈
      convexHull ℝ ({u0, u1, u2, u2} : Set V3) := by
    have hset : ({u0, u1, u2, u2} : Set V3) = setOfList [u0, u1, u2] := by
      ext x; simp [setOfList]; try tauto
    rw [hset]; exact hs2hull
  rw [CONVEX_HULL_4] at hs2hull'
  obtain ⟨m0, m1, m2, m3, hm0, hm1, hm2, hm3, hmsum, hs2eq⟩ := hs2hull'
  have hs2repr : omegaListN V [u0, u1, u2, u3] 2
      = m0 • u0 + m1 • u1 + (m2 + m3) • u2 := by
    rw [hs2eq]; module
  rw [CONVEX_HULL_4] at h3h
  obtain ⟨k0, k1, k2, k3, hk0, hk1, hk2, hk3, hksum, hkeq⟩ := h3h
  have h2aff : p ∈ affGe ({u0, u1} : Set V3)
      ({s, omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    have hh := h2.2
    simpa [hdV, show mxi V [u0, u1, u2, u3] = s from hsm.symm] using hh
  have hs2vor : omegaListN V [u0, u1, u2, u3] 2 ∈ voronoiList V [u0, u1, u2] := by
    have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 2 hb (by norm_num)
    rwa [hTR2] at h
  have hs3vor : omegaListN V [u0, u1, u2, u3] 3 ∈ voronoiList V [u0, u1, u2] := by
    have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 3 hb le_rfl
    rw [TRUNCATE_SIMPLEX_REFL 3 _ hb.1] at h
    refine p13t_voronoiList_mono ?_ h
    intro x hx
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hx ⊢
    tauto
  have hseg' := hseg
  rw [mem_segment_iff_div] at hseg'
  obtain ⟨α, β, hα, hβ, hαβpos, hsdiv⟩ := hseg'
  set A : ℝ := α / (α + β) with hAdef
  set B : ℝ := β / (α + β) with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hAB : A + B = 1 := by rw [hAdef, hBdef, ← add_div]; field_simp
  have hsegdiv : s = A • omegaListN V [u0, u1, u2, u3] 2
      + B • omegaListN V [u0, u1, u2, u3] 3 := hsdiv.symm
  have hsvor : s ∈ voronoiList V [u0, u1, u2] := by
    rw [hsegdiv]
    exact CONVEX_VORONOI_LIST V [u0, u1, u2] hs2vor hs3vor hA0 hB0 hAB
  have hsnot : s ∉ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) :=
    p13t_notMem_aff_of_vor V u0 u1 u2 s hp hbar2 hsvor (by rw [hdist']; exact h2lt)
  have hs3cc : omegaListN V [u0, u1, u2, u3] 3 =
      circumcenter (setOfList [u0, u1, u2, u3]) := by
    obtain ⟨a, hsing, hacc, _⟩ :=
      VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, u2, u3] hp hs hb
    have htr3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
      TRUNCATE_SIMPLEX_REFL 3 _ hb.1
    have h1 : omegaListN V [u0, u1, u2, u3] 3
        = closestPoint (voronoiList V [u0, u1, u2, u3])
          (omegaListN V [u0, u1, u2, u3] 2) := by
      show closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 2) = _
      rw [htr3]
    rw [h1, hsing, CLOSEST_POINT_SING, hacc]
  have hd03 : dist u0 (omegaListN V [u0, u1, u2, u3] 3) = hl [u0, u1, u2, u3] := by
    rw [hs3cc]
    have h := HL_EQ_DIST0 V 3 [u0, u1, u2, u3] hp hb
    rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at h
    calc dist u0 (circumcenter (setOfList [u0, u1, u2, u3]))
        = dist (circumcenter (setOfList [u0, u1, u2, u3])) u0 := dist_comm ..
      _ = hl [u0, u1, u2, u3] := h.symm
  have hs3not : omegaListN V [u0, u1, u2, u3] 3 ∉
      (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) :=
    p13t_notMem_aff_of_vor V u0 u1 u2 _ hp hbar2 hs3vor (by rw [hd03]; linarith [hcond3.2, h2lt])
  have hu0s : u0 ≠ s := fun h =>
    hsnot (h ▸ subset_affineSpan ℝ ({u0, u1, u2} : Set V3) (by simp))
  have hu1s : u1 ≠ s := fun h =>
    hsnot (h ▸ subset_affineSpan ℝ ({u0, u1, u2} : Set V3) (by simp))
  have hu0s3 : u0 ≠ omegaListN V [u0, u1, u2, u3] 3 := fun h =>
    hs3not (h ▸ subset_affineSpan ℝ ({u0, u1, u2} : Set V3) (by simp))
  have hu1s3 : u1 ≠ omegaListN V [u0, u1, u2, u3] 3 := fun h =>
    hs3not (h ▸ subset_affineSpan ℝ ({u0, u1, u2} : Set V3) (by simp))
  have hdis : Disjoint ({u0, u1} : Set V3)
      ({s, omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
    rcases hx1 with h1 | h1
    · rcases hx2 with h2 | h2
      · exact hu0s (h1.symm.trans h2)
      · exact hu0s3 (h1.symm.trans h2)
    · rcases hx2 with h2 | h2
      · exact hu1s (h1.symm.trans h2)
      · exact hu1s3 (h1.symm.trans h2)
  rw [AFF_GE_2_2 u0 u1 s (omegaListN V [u0, u1, u2, u3] 3) hdis] at h2aff
  obtain ⟨t1, t2, t3, t4, ht3, ht4, htsum, hpeq⟩ := h2aff
  -- write s3 through s and s2
  have hBpos : 0 < B := by
    rcases lt_or_eq_of_le hB0 with hbpos | hb0
    · exact hbpos
    · exfalso
      have hA1 : A = 1 := by linarith
      have hs2eq' : s = omegaListN V [u0, u1, u2, u3] 2 := by
        calc s = A • omegaListN V [u0, u1, u2, u3] 2
              + B • omegaListN V [u0, u1, u2, u3] 3 := hsegdiv
          _ = omegaListN V [u0, u1, u2, u3] 2 := by
              have hB0eq : B = 0 := hb0.symm
              rw [hA1, hB0eq, one_smul, zero_smul, add_zero]
      have : dist u0 s = hl [u0, u1, u2] := by rw [hs2eq']; exact hs2dist
      rw [hdist'] at this
      linarith
  set b1 : ℝ := B⁻¹ with hb1def
  set r : ℝ := -(A * b1) with hrdef
  have hb1β : b1 * B = 1 := by
    rw [hb1def]; exact inv_mul_cancel₀ (ne_of_gt hBpos)
  have hs3repr : omegaListN V [u0, u1, u2, u3] 3 = b1 • s
      + r • omegaListN V [u0, u1, u2, u3] 2 := by
    rw [hsegdiv]
    have h1 : b1 • (A • omegaListN V [u0, u1, u2, u3] 2
          + B • omegaListN V [u0, u1, u2, u3] 3)
        + r • omegaListN V [u0, u1, u2, u3] 2
        = (b1 * B) • omegaListN V [u0, u1, u2, u3] 3
          + (b1 * A + r) • omegaListN V [u0, u1, u2, u3] 2 := by module
    rw [h1, hb1β]
    have h2 : b1 * A + r = 0 := by rw [hrdef]; ring
    rw [h2, zero_smul, add_zero, one_smul]
  have hsum3 : b1 + r = 1 := by
    have h1 : b1 + r = b1 * (1 - A) := by rw [hrdef]; ring
    rw [h1, show 1 - A = B from by linarith, hb1β]
  have hrle : r ≤ 0 := by
    rw [hrdef]
    exact neg_nonpos.mpr (mul_nonneg hA0 (inv_nonneg.mpr hB0))
  -- two affine representations of p in the basis (u0,u1,s,u2)
  have hpc1 : p = (t1 + t4 * r * m0) • u0 + (t2 + t4 * r * m1) • u1
      + (t3 + t4 * b1) • s + (t4 * r * (m2 + m3)) • u2 := by
    rw [hpeq, hs3repr, hs2repr]
    module
  have hpc2 : p = k0 • u0 + k1 • u1 + k3 • s + k2 • u2 := by
    rw [hkeq]; module
  have hsum1 : (t1 + t4 * r * m0) + (t2 + t4 * r * m1) + (t3 + t4 * b1)
      + (t4 * r * (m2 + m3)) = 1 := by
    have e1 : (t1 + t4 * r * m0) + (t2 + t4 * r * m1) + (t3 + t4 * b1)
        + (t4 * r * (m2 + m3))
        = (t1 + t2 + t3 + t4) + t4 * (b1 + r - 1)
          + t4 * r * (m0 + m1 + m2 + m3 - 1) := by ring
    rw [e1, htsum, hsum3, hmsum]; ring
  have hsum2 : k0 + k1 + k3 + k2 = 1 := by linarith
  -- distinctness and linear independence
  obtain ⟨hu01, hu02, hu12⟩ := p13t_barV2_ne V u0 u1 u2 hbar2
  have hs2ne : s ≠ u2 := fun h => hsnot (by
    have hmem : u2 ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) :=
      subset_affineSpan ℝ _ (by simp)
    simpa [h] using hmem)
  have hdim3 : affDim ({u0, u1, u2} : Set V3) = 2 := by
    have hset : ({u0, u1, u2} : Set V3) = setOfList [u0, u1, u2] := by
      ext x; simp [setOfList]; try tauto
    rw [hset]
    exact MHFTTZN1 V [u0, u1, u2] 2 hp hbar2
  have hli := p13t_li_triple u0 u1 u2 s hdim3 hsnot hu02 hu12 hs2ne hu01 hu0s hu1s
  have hcoef := p13t_aff_coords_unique hli hsum1 hsum2 hpc1 hpc2
  have hK2le : t4 * r * (m2 + m3) ≤ 0 := by
    have h1 : r * (m2 + m3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hrle (add_nonneg hm2 hm3)
    have h2 : t4 * (r * (m2 + m3)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht4 h1
    calc t4 * r * (m2 + m3) = t4 * (r * (m2 + m3)) := by ring
      _ ≤ 0 := h2
  have hk2z : k2 = 0 := by
    have := hcoef.2.2.2
    linarith
  -- p lies in B4
  have hdir : (p - u0) ∈ (affineSpan ℝ ({u0, u1, s} : Set V3)).direction := by
    have h1 : (u1 - u0) ∈ (affineSpan ℝ ({u0, u1, s} : Set V3)).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
    have h2 : (s - u0) ∈ (affineSpan ℝ ({u0, u1, s} : Set V3)).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
    have he : p - u0 = k1 • (u1 - u0) + k3 • (s - u0) := by
      rw [hkeq, hk2z, zero_smul, add_zero]
      rw [show k0 = 1 - k1 - k3 from by linarith]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  have hB4 : p ∈ (affineSpan ℝ ({u0, u1, s} : Set V3) : Set V3) := by
    have hpv : p = (p - u0) +ᵥ u0 := by simp
    rw [hpv]
    exact AffineSubspace.vadd_mem_of_mem_direction hdir
      (subset_affineSpan ℝ _ (by simp))
  have hB4' : p ∈ (affineSpan ℝ ({hdV [u0, u1, u2, u3],
      hdV [u0, u1, u2, u3].tail, mxi V [u0, u1, u2, u3]} : Set V3) : Set V3) := by
    simpa [hdV, show mxi V [u0, u1, u2, u3] = s from hsm.symm] using hB4
  simp only [sltZ, Set.mem_union]
  tauto



/-- (0,3): `mcell0 ∩ mcell3` off `Z` lands in `B6`, and the boundary case in
`B5`.  Pyramid coordinates of the Rogers simplex: a point of
`mcell0 ∩ mcell3` has a height `t` above the plane `u0u1u2` with `t ≤ λ`,
where `mxi = s2 + λ(s3-s2)`; distance comparison forces `t = λ` and base
point `s2`, hence `p ∈ [s2,s3] = B5`, unless `t = 0` and `p` lies in the
base plane `B6`. -/
private theorem p13t_mcell0_mcell3_subset_Z (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (h0 : p ∈ mcell 0 V ul) (h3 : p ∈ mcell 3 V ul) : p ∈ sltZ V ul := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  rw [(MCELL_EXPLICIT 0 V [u0, u1, u2, u3]).1] at h0
  rw [(MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1] at h3
  rw [mcell0] at h0
  have hTR2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hcond3 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra h
    rw [mcell3, if_neg h] at h3
    exact absurd h3 (Set.notMem_empty p)
  rw [mcell3, if_pos hcond3] at h3
  have hbar2 : barV V 2 [u0, u1, u2] := by
    rw [← hTR2]
    exact TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
  have h2lt : hl [u0, u1, u2] < Real.sqrt 2 := by
    rw [← hTR2]; exact hcond3.1
  have hH : Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := hcond3.2
  set s1 : V3 := omegaListN V [u0, u1, u2, u3] 1 with hs1def
  set s2 : V3 := omegaListN V [u0, u1, u2, u3] 2 with hs2def
  set s3 : V3 := omegaListN V [u0, u1, u2, u3] 3 with hs3def
  set s : V3 := mxi V [u0, u1, u2, u3] with hsdef
  obtain ⟨s', hseg0, hdist0, hsm⟩ :=
    MXI_EXPLICIT_OLD V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl hcond3.1 hH
  have hseq : s' = s := by rw [hsm, hsdef]
  have hseg : s ∈ segment ℝ s2 s3 := by
    rw [← hseq, hs2def, hs3def]
    exact hseg0
  have hdist : dist u0 s = Real.sqrt 2 := by
    rw [← hseq]; simpa using hdist0
  have h3h : p ∈ convexHull ℝ ({u0, u1, u2, s} : Set V3) := by
    have h0h : p ∈ convexHull ℝ (setOfList [u0, u1, u2] ∪
        ({mxi V [u0, u1, u2, u3]} : Set V3)) := by
      simpa [hTR2] using h3
    have hset : setOfList [u0, u1, u2] ∪ ({mxi V [u0, u1, u2, u3]} : Set V3)
        = ({u0, u1, u2, s} : Set V3) := by
      ext x; simp [setOfList, ← hsdef]
      try tauto
    rwa [hset] at h0h
  have hfar : Real.sqrt 2 ≤ dist p u0 := by
    have hh := h0.2
    simpa [Metric.mem_ball, not_lt, show hdV [u0, u1, u2, u3] = u0 from rfl] using hh
  have hrog4 : p ∈ convexHull ℝ ({u0, s1, s2, s3} : Set V3) := by
    have h := h0.1
    rw [ROGERS_EXPLICIT V [u0, u1, u2, u3] hs hp hb] at h
    have hset : ({hdV [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3}
        : Set V3) = ({u0, s1, s2, s3} : Set V3) := by
      ext x; simp [show hdV [u0, u1, u2, u3] = u0 from rfl, ← hs1def, ← hs2def,
        ← hs3def]
    rwa [hset] at h
  -- s1 is the midpoint of u0 u1
  have hhh : hl [u0, u1] < Real.sqrt 2 := by
    have hdec : hl [u0, u1] ≤ hl [u0, u1, u2] := by
      simpa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).2.1,
        (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u0).1] using
        (HL_DECREASE V [u0, u1, u2] 2 1 hp hbar2 (by omega))
    exact lt_of_le_of_lt hdec h2lt
  have hbar1 : barV V 1 [u0, u1] := by
    rw [← (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1]
    exact TRUNCATE_SIMPLEX_BARV V 1 2 [u0, u1, u2] hbar2 (by omega)
  have hs1mid : s1 = midpoint ℝ u0 u1 := by
    rw [hs1def, OMEGA_LIST_TRUNCATE_1 V u0 u1 u2 u3,
      XNHPWAB1 V [u0, u1] 1 hp hbar1 hhh]
    have hset : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
      ext x; simp [setOfList]; try tauto
    rw [hset, CIRCUMCENTER_2]
  have hs2cc : s2 = circumcenter (setOfList [u0, u1, u2]) := by
    rw [hs2def]
    exact p13t_omega2_cc V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2dist : dist u0 s2 = hl [u0, u1, u2] := by
    rw [hs2def]
    exact p13t_omega2_dist V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2P : s2 ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) := by
    have hset : ({u0, u1, u2} : Set V3) = setOfList [u0, u1, u2] := by
      ext x; simp [setOfList]; try tauto
    rw [hs2cc, hset]
    exact BARV_CIRCUMCENTER_EXISTS V [u0, u1, u2] 2 hp hbar2
  have hs1P : s1 ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) := by
    have hmem : s1 ∈ (affineSpan ℝ ({u0, u1} : Set V3) : Set V3) := by
      rw [hs1mid]
      exact convexHull_subset_affineSpan _ (Convex.midpoint_mem
        (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (by simp)))
    have hsub : ({u0, u1} : Set V3) ⊆ ({u0, u1, u2} : Set V3) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    exact affineSpan_mono (k := ℝ) hsub hmem
  -- s3 and the normal n
  have hs3cc : s3 = circumcenter (setOfList [u0, u1, u2, u3]) := by
    obtain ⟨a, hsing, hacc, _⟩ :=
      VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, u2, u3] hp hs hb
    have htr3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
      TRUNCATE_SIMPLEX_REFL 3 _ hb.1
    have h1 : omegaListN V [u0, u1, u2, u3] 3
        = closestPoint (voronoiList V [u0, u1, u2, u3])
          (omegaListN V [u0, u1, u2, u3] 2) := by
      show closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 2) = _
      rw [htr3]
    rw [hs3def, h1, hsing, CLOSEST_POINT_SING, hacc]
  have hd03 : dist u0 s3 = hl [u0, u1, u2, u3] := by
    rw [hs3cc]
    have h := HL_EQ_DIST0 V 3 [u0, u1, u2, u3] hp hb
    rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at h
    calc dist u0 (circumcenter (setOfList [u0, u1, u2, u3]))
        = dist (circumcenter (setOfList [u0, u1, u2, u3])) u0 := dist_comm ..
      _ = hl [u0, u1, u2, u3] := h.symm
  obtain ⟨n, hn, horth⟩ :=
    BARV_CIRCUMCENTER_PROJECTION V [u0, u1, u2, u3] 3 2 hp hb (by norm_num)
  have hs3n : s3 = s2 + n := by
    rw [hs3cc, hn, hTR2, ← hs2cc]
  have hnne : n ≠ 0 := by
    intro hn0
    have hs3s2 : s3 = s2 := by rw [hs3n, hn0, add_zero]
    have h1 : dist u0 s3 = hl [u0, u1, u2, u3] := hd03
    rw [hs3s2, hs2dist] at h1
    linarith [hcond3.2, h2lt]
  have hnnI : inner ℝ n n ≠ 0 := by
    have hpos : 0 < inner ℝ n n := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.mpr hnne) 2
    exact ne_of_gt hpos
  -- orthogonality of n to the plane P
  have hspanorth : ∀ z ∈ vectorSpan ℝ ({u0, u1, u2} : Set V3), z ⬝ᵥ n = 0 := by
    intro z hz
    have hz' : z ∈ Submodule.span ℝ
        (({u0, u1, u2} : Set V3) -ᵥ ({u0, u1, u2} : Set V3)) := by
      rwa [vectorSpan_def] at hz
    refine Submodule.span_induction
      (p := fun (z : V3) (_ : z ∈ Submodule.span ℝ
        (({u0, u1, u2} : Set V3) -ᵥ ({u0, u1, u2} : Set V3))) => z ⬝ᵥ n = 0)
      ?_ ?_ ?_ ?_ hz'
    · intro z hz
      obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_vsub.1 hz
      have hv' : v ∈ setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
        rw [hTR2]; simpa [setOfList] using hv
      have hw' : w ∈ setOfList (truncateSimplex 2 [u0, u1, u2, u3]) := by
        rw [hTR2]; simpa [setOfList] using hw
      exact horth v hv' w hw'
    · simp
    · intro a b ha hb hpa hpb
      rw [WithLp.ofLp_add, add_dotProduct, hpa, hpb, add_zero]
    · intro c a ha hpa
      rw [WithLp.ofLp_smul, smul_dotProduct, hpa, smul_eq_mul, mul_zero]
  have hPorthI : ∀ x ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3),
      inner ℝ (x - s2) n = 0 := by
    intro x hx
    have hdir : (x - s2) ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3)).direction :=
      AffineSubspace.vsub_mem_direction hx hs2P
    rw [direction_affineSpan] at hdir
    have h := hspanorth _ hdir
    rwa [inner_eq_dot]
  -- coordinates of s on the segment [s2,s3]
  rw [mem_segment_iff_div] at hseg
  obtain ⟨α, β, hα, hβ, hαβpos, hsdiv⟩ := hseg
  set B : ℝ := β / (α + β) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hB1 : B ≤ 1 := by
    rw [hBdef, div_le_one hαβpos]; linarith
  have hs_eq : s = (1 - B) • s2 + B • s3 := by
    have h1 : (1 - B) = α / (α + β) := by rw [hBdef]; field_simp; ring
    rw [h1, hBdef]; exact hsdiv.symm
  have hss2 : s - s2 = B • n := by rw [hs_eq, hs3n]; module
  -- weights
  rw [CONVEX_HULL_4] at hrog4
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, hasum, haeq⟩ := hrog4
  rw [CONVEX_HULL_4] at h3h
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, hcsum, hceq⟩ := h3h
  have hdotrog : inner ℝ (p - s2) n = a3 * inner ℝ n n := by
    have hps2 : p - s2 = a0 • (u0 - s2) + a1 • (s1 - s2) + a2 • (s2 - s2)
        + a3 • (s3 - s2) := by
      have hsub : p - s2 = (a0 • u0 + a1 • s1 + a2 • s2 + a3 • s3) - s2 := by
        rw [haeq]
      rw [hsub, show a0 = 1 - a1 - a2 - a3 from by linarith]
      module
    rw [hps2]
    simp only [inner_add_left, real_inner_smul_left,
      hPorthI u0 (subset_affineSpan ℝ _ (by simp)), hPorthI s1 hs1P,
      hPorthI s2 hs2P, mul_zero, zero_add, add_zero]
    rw [show s3 - s2 = n from by rw [hs3n]; abel]
  have hdot3 : inner ℝ (p - s2) n = B * c3 * inner ℝ n n := by
    have hps2 : p - s2 = c0 • (u0 - s2) + c1 • (u1 - s2) + c2 • (u2 - s2)
        + c3 • (s - s2) := by
      have hsub : p - s2 = (c0 • u0 + c1 • u1 + c2 • u2 + c3 • s) - s2 := by
        rw [hceq]
      rw [hsub, show c0 = 1 - c1 - c2 - c3 from by linarith]
      module
    rw [hps2]
    simp only [inner_add_left, real_inner_smul_left,
      hPorthI u0 (subset_affineSpan ℝ _ (by simp)),
      hPorthI u1 (subset_affineSpan ℝ _ (by simp)),
      hPorthI u2 (subset_affineSpan ℝ _ (by simp)), mul_zero, zero_add, add_zero]
    rw [hss2]
    rw [real_inner_smul_left]
    try ring
  have ha3eqBc3 : a3 = B * c3 := by
    have h : a3 * inner ℝ n n = (B * c3) * inner ℝ n n := by
      rw [← hdotrog, hdot3]; try ring
    exact mul_right_cancel₀ hnnI h
  have ha3le : a3 ≤ B := by
    rw [ha3eqBc3]; nlinarith [hB0, hc3, hB1]
  -- decomposition p - u0
  set T : ℝ := 1 - a3 with hTdef
  set μ0 : ℝ := a0 / T with hμ0def
  set μ1 : ℝ := a1 / T with hμ1def
  set w : V3 := μ0 • (u0 - s2) + μ1 • (s1 - s2) with hwdef
  by_cases ha3one : a3 = 1
  · have ha0z : a0 = 0 := by nlinarith [hasum, ha0, ha1, ha2, ha3one]
    have ha1z : a1 = 0 := by nlinarith [hasum, ha0, ha1, ha2, ha3one]
    have ha2z : a2 = 0 := by nlinarith [hasum, ha0, ha1, ha2, ha3one]
    have hp3 : p = s3 := by
      rw [haeq, ha0z, ha1z, ha2z, ha3one]; simp
    have hB5 : p ∈ convexHull ℝ ({s2, s3} : Set V3) := by
      rw [convexHull_pair, hp3]
      exact right_mem_segment ℝ s2 s3
    have hB5' : p ∈ convexHull ℝ ({omegaListN V [u0, u1, u2, u3] 2,
        omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
      rw [← hs2def, ← hs3def]; exact hB5
    simp only [sltZ, Set.mem_union]; tauto
  have hTpos : 0 < T := by
    rw [hTdef]
    have hle : a3 ≤ 1 := by linarith [hasum, ha0, ha1, ha2]
    have hlt : a3 < 1 := lt_of_le_of_ne hle ha3one
    linarith
  have hTa : T ≠ 0 := ne_of_gt hTpos
  -- geometry: v = y+z with y ⟂ z
  obtain ⟨m, hm, hmorth⟩ :=
    BARV_CIRCUMCENTER_PROJECTION V [u0, u1, u2] 2 1 hp hbar2 (by norm_num)
  have hm' : circumcenter (setOfList (truncateSimplex 1 [u0, u1, u2])) = s1 := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).2.1]
    have hset : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
      ext x; simp [setOfList]; try tauto
    rw [hset, CIRCUMCENTER_2]; exact hs1mid.symm
  have hs2m : s2 = s1 + m := by rw [hs2cc, hm, hm']
  have hmem1 : u1 ∈ setOfList (truncateSimplex 1 [u0, u1, u2]) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).2.1]; simp [setOfList]
  have hmem0 : u0 ∈ setOfList (truncateSimplex 1 [u0, u1, u2]) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).2.1]; simp [setOfList]
  have hm0 : (u1 - u0) ⬝ᵥ m = 0 := hmorth u1 hmem1 u0 hmem0
  have hperp_yz : inner ℝ (s1 - s2) (u0 - s1) = 0 := by
    have hy : (s1 - s2 : V3) = -m := by rw [hs2m]; abel
    have hz : (u0 - s1 : V3) = (-(1/2 : ℝ)) • (u1 - u0) := by
      rw [hs1mid, left_sub_midpoint, show u0 - u1 = -(u1 - u0) from by abel,
        smul_neg, neg_smul]
      rw [show (⅟(2:ℝ)) = (1/2:ℝ) from by norm_num]
    have hmid : inner ℝ m (u1 - u0) = 0 := by
      rw [inner_eq_dot, dotProduct_comm]; exact hm0
    calc inner ℝ (s1 - s2) (u0 - s1)
        = inner ℝ (-m) ((-(1/2 : ℝ)) • (u1 - u0)) := by rw [hy, hz]
      _ = (-(1/2)) * inner ℝ (-m) (u1 - u0) :=
          real_inner_smul_right (-m) (u1 - u0) (-(1/2 : ℝ))
      _ = (-(1/2)) * (-(inner ℝ m (u1 - u0))) := by
          rw [inner_neg_left]
      _ = 0 := by rw [hmid]; ring
  have hYaddZ : ‖u0 - s2‖ ^ 2 = ‖s1 - s2‖ ^ 2 + ‖u0 - s1‖ ^ 2 := by
    have hde : (u0 - s2 : V3) = (s1 - s2) + (u0 - s1) := by abel
    rw [hde, norm_add_sq_real, hperp_yz, mul_zero, add_zero]
  have hw' : T • w = a0 • (u0 - s2) + a1 • (s1 - s2) := by
    calc T • w = T • (μ0 • (u0 - s2) + μ1 • (s1 - s2)) := by rw [hwdef]
      _ = (T * μ0) • (u0 - s2) + (T * μ1) • (s1 - s2) := by
          rw [smul_add, smul_smul, smul_smul]
      _ = a0 • (u0 - s2) + a1 • (s1 - s2) := by
          rw [hμ0def, hμ1def, mul_div_cancel₀ a0 hTa, mul_div_cancel₀ a1 hTa]
  have hp_u0 : p - u0 = (T • w - (u0 - s2)) + a3 • n := by
    have hdecomp : a0 • u0 + a1 • s1 + a2 • s2 + a3 • (s2 + n) - u0
        = (a0 • (u0 - s2) + a1 • (s1 - s2) + a3 • n) - (u0 - s2) := by
      rw [show a0 = 1 - a1 - a2 - a3 from by linarith [hasum]]
      module
    rw [haeq, hs3n, hdecomp, ← hw']
    module
  have horth_sum : inner ℝ (T • w - (u0 - s2)) n = 0 := by
    have hwP : inner ℝ w n = 0 := by
      rw [hwdef]
      simp only [inner_add_left, real_inner_smul_left,
        hPorthI u0 (subset_affineSpan ℝ _ (by simp)), hPorthI s1 hs1P,
        mul_zero, add_zero]
    simp only [inner_sub_left, real_inner_smul_left, hwP,
      hPorthI u0 (subset_affineSpan ℝ _ (by simp)), mul_zero, sub_zero]
  have hdistp : dist p u0 ^ 2 = ‖T • w - (u0 - s2)‖ ^ 2 + a3 ^ 2 * ‖n‖ ^ 2 := by
    rw [dist_eq_norm, hp_u0, norm_add_sq_real]
    have hstep : inner ℝ (T • w - (u0 - s2)) (a3 • n)
        = a3 * inner ℝ (T • w - (u0 - s2)) n :=
      real_inner_smul_right _ n a3
    rw [hstep, horth_sum, mul_zero, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ha3, mul_pow]
    try ring
  have hμ0le : μ0 ≤ 1 := by
    rw [hμ0def, div_le_one hTpos]; linarith [ha0, ha1, ha2, hasum]
  have hμ1le : μ1 ≤ 1 := by
    rw [hμ1def, div_le_one hTpos]; linarith [ha0, ha1, ha2, hasum]
  have hμ0nn : 0 ≤ μ0 := by rw [hμ0def]; exact div_nonneg ha0 hTpos.le
  have hμ1nn : 0 ≤ μ1 := by rw [hμ1def]; exact div_nonneg ha1 hTpos.le
  have hsumμ : μ0 + μ1 ≤ 1 := by
    rw [hμ0def, hμ1def, ← add_div, div_le_one hTpos]
    linarith [ha0, ha1, ha2, hasum]
  have hA1 : 0 ≤ (1 - a3) * (μ0 + μ1) :=
    mul_nonneg (by linarith) (by linarith)
  have hA1le : (1 - a3) * (μ0 + μ1) ≤ 1 := by
    have h1 : 0 ≤ 1 - a3 := by linarith
    nlinarith [h1, hsumμ]
  have hBcoef : 0 ≤ (1 - a3) * μ0 := mul_nonneg (by linarith) hμ0nn
  have hBcoefle : (1 - a3) * μ0 ≤ 1 := by
    have h1 : 0 ≤ 1 - a3 := by linarith
    nlinarith [h1, hμ0le]
  have hTvw : T • w - (u0 - s2)
      = ((1 - a3) * (μ0 + μ1) - 1) • (s1 - s2)
        + ((1 - a3) * μ0 - 1) • (u0 - s1) := by
    have hv : (u0 - s2 : V3) = (s1 - s2) + (u0 - s1) := by abel
    rw [hwdef, hTdef, hv]
    module
  have hnormw : ‖T • w - (u0 - s2)‖ ^ 2
      = ((1 - a3) * (μ0 + μ1) - 1) ^ 2 * ‖s1 - s2‖ ^ 2
        + ((1 - a3) * μ0 - 1) ^ 2 * ‖u0 - s1‖ ^ 2 := by
    rw [hTvw, norm_add_sq_real]
    simp only [real_inner_smul_left, real_inner_smul_right, hperp_yz, mul_zero,
      add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbound1 : ‖T • w - (u0 - s2)‖ ^ 2 ≤ ‖u0 - s2‖ ^ 2 := by
    rw [hnormw, hYaddZ]
    have hα : ((1 - a3) * (μ0 + μ1) - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((1 - a3) * (μ0 + μ1) - 1), hA1, hA1le]
    have hβ : ((1 - a3) * μ0 - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((1 - a3) * μ0 - 1), hBcoef, hBcoefle]
    nlinarith [mul_le_mul_of_nonneg_right hα (sq_nonneg ‖s1 - s2‖),
      mul_le_mul_of_nonneg_right hβ (sq_nonneg ‖u0 - s1‖)]
  have hsnorm : dist u0 s ^ 2 = ‖u0 - s2‖ ^ 2 + B ^ 2 * ‖n‖ ^ 2 := by
    have hsdec : (u0 - s : V3) = (u0 - s2) - B • n := by
      rw [show u0 - s = (u0 - s2) - (s - s2) from by abel, hss2]
    rw [dist_eq_norm, hsdec, norm_sub_sq_real]
    have hov : inner ℝ (u0 - s2) (B • n) = 0 := by
      simp only [real_inner_smul_right, hPorthI u0 (subset_affineSpan ℝ _ (by simp)), mul_zero]
    rw [hov, mul_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hB0, mul_pow]
    try ring
  have hdist2 : dist u0 s ^ 2 = 2 := by
    rw [hdist, Real.sq_sqrt (by norm_num)]
  have hfar2 : 2 ≤ dist p u0 ^ 2 := by
    have h1 : 0 ≤ dist p u0 - Real.sqrt 2 := by linarith
    have h2 : 0 ≤ dist p u0 + Real.sqrt 2 := by positivity
    have h3 : 0 ≤ (dist p u0 - Real.sqrt 2) * (dist p u0 + Real.sqrt 2) :=
      mul_nonneg h1 h2
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  have h1 : a3 ^ 2 * ‖n‖ ^ 2 ≤ B ^ 2 * ‖n‖ ^ 2 := by
    have hsq : a3 ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ ha3 ha3le 2
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hle2 : dist p u0 ^ 2 ≤ 2 := by
    calc dist p u0 ^ 2 = ‖T • w - (u0 - s2)‖ ^ 2 + a3 ^ 2 * ‖n‖ ^ 2 := hdistp
      _ ≤ ‖u0 - s2‖ ^ 2 + a3 ^ 2 * ‖n‖ ^ 2 :=
          by simpa [add_comm] using add_le_add_right hbound1 (a3 ^ 2 * ‖n‖ ^ 2)
      _ ≤ ‖u0 - s2‖ ^ 2 + B ^ 2 * ‖n‖ ^ 2 := by linarith [h1]
      _ = 2 := by rw [← hsnorm, hdist2]
  have hEq : dist p u0 ^ 2 = 2 := le_antisymm hle2 hfar2
  have hsum1 : ‖u0 - s2‖ ^ 2 + a3 ^ 2 * ‖n‖ ^ 2 = 2 := by
    linarith [hEq, hdistp]
  have hsum2 : ‖u0 - s2‖ ^ 2 + B ^ 2 * ‖n‖ ^ 2 = 2 := by
    linarith [hsnorm, hdist2]
  have hψeq : ‖T • w - (u0 - s2)‖ ^ 2 = ‖u0 - s2‖ ^ 2 := by
    linarith [hbound1, h1, hsum1, hsum2]
  have hνeq : a3 ^ 2 * ‖n‖ ^ 2 = B ^ 2 * ‖n‖ ^ 2 := by
    linarith [hbound1, h1, hsum1, hsum2]
  have ha3eqB : a3 = B := by
    exact (sq_eq_sq₀ ha3 hB0).mp
      (mul_right_cancel₀ (by positivity : ‖n‖ ^ 2 ≠ 0) hνeq)
  have hnormeq : ‖T • w - (u0 - s2)‖ ^ 2 = ‖u0 - s2‖ ^ 2 := hψeq
  have hw0 : w = 0 := by
    rw [hnormw, hYaddZ] at hnormeq
    have hcoefA : ((1 - a3) * (μ0 + μ1) - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((1 - a3) * (μ0 + μ1) - 1), hA1, hA1le]
    have hcoefB : ((1 - a3) * μ0 - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((1 - a3) * μ0 - 1), hBcoef, hBcoefle]
    have hleA : ((1 - a3) * (μ0 + μ1) - 1) ^ 2 * ‖s1 - s2‖ ^ 2
        ≤ ‖s1 - s2‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hcoefA
    have hleB : ((1 - a3) * μ0 - 1) ^ 2 * ‖u0 - s1‖ ^ 2
        ≤ ‖u0 - s1‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hcoefB
    have hAeq : ((1 - a3) * (μ0 + μ1) - 1) ^ 2 * ‖s1 - s2‖ ^ 2
        = ‖s1 - s2‖ ^ 2 := by linarith [hleA, hleB, hnormeq]
    have hBeq : ((1 - a3) * μ0 - 1) ^ 2 * ‖u0 - s1‖ ^ 2
        = ‖u0 - s1‖ ^ 2 := by linarith [hleA, hleB, hnormeq]
    have hnA0 : 0 ≤ 1 - (1 - a3) * (μ0 + μ1) := by linarith [hA1le]
    have hnB0 : 0 ≤ 1 - (1 - a3) * μ0 := by linarith [hBcoefle]
    by_cases hY0 : ‖s1 - s2‖ ^ 2 = 0
    · -- y = 0
      have hy0 : s1 - s2 = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hY0
        simpa using this
      by_cases hZ0 : ‖u0 - s1‖ ^ 2 = 0
      · exfalso
        have hz0 : u0 - s1 = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hZ0
          simpa using this
        have hv0 : u0 - s2 = 0 := by
          rw [show u0 - s2 = (u0 - s1) + (s1 - s2) from by abel, hz0, hy0,
            add_zero]
        have hdist0' : dist u0 s2 = 0 := by rw [dist_eq_norm, hv0, norm_zero]
        rw [hs2dist] at hdist0'
        have hu0u1 : u0 ≠ u1 := (p13t_barV2_ne V u0 u1 u2 hbar2).1
        have hsl := HL_PROPERTIES V [u0, u1, u2] 2 hp hbar2 u1 (by simp [setOfList])
        have hs2u0 : u0 = s2 := sub_eq_zero.mp hv0
        have hdist_eq : dist u0 u1 = 0 := by
          rw [hs2u0, hs2cc, hsl]
          exact hdist0'
        exact hu0u1 (dist_eq_zero.mp hdist_eq)
      · have hZpos : 0 < ‖u0 - s1‖ ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm hZ0)
        have hsqB : ((1 - a3) * μ0 - 1) ^ 2 = 1 :=
          mul_right_cancel₀ (ne_of_gt hZpos) (by simpa using hBeq)
        have hβ0 : (1 - a3) * μ0 = 0 := by
          have h2 := sq_eq_one_iff.mp hsqB
          rcases h2 with h2 | h2
          · linarith [hBcoefle]
          · linarith
        have hμ0 : μ0 = 0 := by
          rcases mul_eq_zero.mp hβ0 with h | h
          · linarith
          · exact h
        rw [hwdef, hy0, hμ0]; simp
    · -- α = 0 forces μ0 = μ1 = 0
      have hYpos : 0 < ‖s1 - s2‖ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hY0)
      have hsqA : ((1 - a3) * (μ0 + μ1) - 1) ^ 2 = 1 :=
        mul_right_cancel₀ (ne_of_gt hYpos) (by simpa using hAeq)
      have hα0 : (1 - a3) * (μ0 + μ1) = 0 := by
        have h2 := sq_eq_one_iff.mp hsqA
        rcases h2 with h2 | h2
        · linarith [hA1le]
        · linarith
      have hμsum : μ0 + μ1 = 0 := by
        rcases mul_eq_zero.mp hα0 with h | h
        · linarith
        · exact h
      have hμ0 : μ0 = 0 := by linarith
      have hμ1 : μ1 = 0 := by linarith
      rw [hwdef, hμ0, hμ1]; simp
  have hpseg : p = (1 - a3) • s2 + a3 • s3 := by
    have hp' : p - u0 = s2 - u0 + a3 • n := by
      rw [hp_u0, hw0, smul_zero, zero_sub, neg_sub]
    calc p = (p - u0) + u0 := by abel
      _ = (s2 - u0 + a3 • n) + u0 := by rw [hp']
      _ = (1 - a3) • s2 + a3 • s3 := by rw [hs3n]; module
  have hB5 : p ∈ convexHull ℝ ({omegaListN V [u0, u1, u2, u3] 2,
      omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    rw [← hs2def, ← hs3def, convexHull_pair, hpseg]
    exact ⟨1 - a3, a3, by linarith [ha3], ha3, by ring, rfl⟩
  simp only [sltZ, Set.mem_union]
  tauto

/-- (1,3): `mcell1 ∩ mcell3` off `Z` lands in `B3 ∪ B7` (HOL
SLTSTLO.hl:2437-3309).  The affine-coordinate hull-intersection lemma
`p13t_hull_ky5` rewrites `p` as a point of `hull{u0,u1,s2,s}`, and
`CONVEX_HULL_4_IMP_2_2` exhibits `p ∈ [m,n]` with `m ∈ [u0,u1]` and
`n ∈ [s2,s]`.  If `m ∈ [s1,u1]`, coefficient comparison in the omega basis
`{u0,s1,s2,s3}` puts `p` on `aff{s1,s2,s3} = B7`; if `m ∈ [u0,s1]`, the
point `q` on `[n,s1]` with `p ∈ [u0,q]` lies in the Voronoi cell of
`{u0,u1}` and inside the `√2`-ball, so its cone inequality is sharp and
cone homogeneity (the `q = u0 + t(q-u0)` scaling) puts `p` on the equality
cone `rconeEq = B3`. -/
private theorem p13t_mcell1_mcell3_subset_Z (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hm1 : p ∈ mcell 1 V ul) (hm3 : p ∈ mcell 3 V ul) : p ∈ sltZ V ul := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  rw [(MCELL_EXPLICIT 1 V [u0, u1, u2, u3]).2.1] at hm1
  rw [(MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1] at hm3
  -- the two regime conditions
  have hH : Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra hc
    rw [mcell1, if_neg hc] at hm1
    exact absurd hm1 (Set.notMem_empty p)
  rw [mcell1, if_pos hH] at hm1
  have hcond3 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra h
    rw [mcell3, if_neg h] at hm3
    exact absurd hm3 (Set.notMem_empty p)
  rw [mcell3, if_pos hcond3] at hm3
  have hTR2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hbar2 : barV V 2 [u0, u1, u2] := by
    rw [← hTR2]
    exact TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
  have h2lt : hl [u0, u1, u2] < Real.sqrt 2 := by
    rw [← hTR2]; exact hcond3.1
  set s1 : V3 := omegaListN V [u0, u1, u2, u3] 1 with hs1def
  set s2 : V3 := omegaListN V [u0, u1, u2, u3] 2 with hs2def
  set s3 : V3 := omegaListN V [u0, u1, u2, u3] 3 with hs3def
  set s : V3 := mxi V [u0, u1, u2, u3] with hsdef
  obtain ⟨s', hseg0, hdist0, hsm⟩ :=
    MXI_EXPLICIT_OLD V [u0, u1, u2, u3] u0 u1 u2 u3 hs hp hb rfl hcond3.1 hH
  have hseq : s' = s := by rw [hsm, hsdef]
  have hseg : s ∈ segment ℝ s2 s3 := by
    rw [← hseq, hs2def, hs3def]
    exact hseg0
  have hdist : dist u0 s = Real.sqrt 2 := by
    rw [← hseq]; simpa using hdist0
  -- p ∈ hull{u0,u1,u2,s}
  have h3h : p ∈ convexHull ℝ ({u0, u1, u2, s} : Set V3) := by
    have h0h : p ∈ convexHull ℝ (setOfList [u0, u1, u2] ∪
        ({mxi V [u0, u1, u2, u3]} : Set V3)) := by
      simpa [hTR2] using hm3
    have hset : setOfList [u0, u1, u2] ∪ ({mxi V [u0, u1, u2, u3]} : Set V3)
        = ({u0, u1, u2, s} : Set V3) := by
      ext x; simp [setOfList, ← hsdef]
      try tauto
    rwa [hset] at h0h
  -- p ∈ rogers = hull{u0,s1,s2,s3}
  have hrog4 : p ∈ convexHull ℝ ({u0, s1, s2, s3} : Set V3) := by
    have h := hm1.1.1
    rw [ROGERS_EXPLICIT V [u0, u1, u2, u3] hs hp hb] at h
    have hset : ({hdV [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3}
        : Set V3) = ({u0, s1, s2, s3} : Set V3) := by
      ext x; simp [show hdV [u0, u1, u2, u3] = u0 from rfl, ← hs1def, ← hs2def,
        ← hs3def]
    rwa [hset] at h
  -- the negated strict cone of mcell1
  have hnotgt : ¬ p ∈ rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2) := by
    have hh := hm1.2
    rwa [show hdV [u0, u1, u2, u3] = u0 from rfl,
      show hdV [u0, u1, u2, u3].tail = u1 from rfl,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] at hh
  -- s1 = midpoint, s2 = circumcenter of the triangle, s3 = circumcenter of ul
  have hdec : hl [u0, u1] ≤ hl [u0, u1, u2] := by
    simpa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).2.1,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u0).1] using
      (HL_DECREASE V [u0, u1, u2] 2 1 hp hbar2 (by omega))
  have hhh : hl [u0, u1] < Real.sqrt 2 := lt_of_le_of_lt hdec h2lt
  have hbar1 : barV V 1 [u0, u1] := by
    rw [← (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1]
    exact TRUNCATE_SIMPLEX_BARV V 1 2 [u0, u1, u2] hbar2 (by omega)
  have hs1mid : s1 = midpoint ℝ u0 u1 := by
    rw [hs1def, OMEGA_LIST_TRUNCATE_1 V u0 u1 u2 u3,
      XNHPWAB1 V [u0, u1] 1 hp hbar1 hhh]
    have hset : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
      ext x; simp [setOfList]; try tauto
    rw [hset, CIRCUMCENTER_2]
  have hs1' : s1 = (1/2:ℝ) • (u0 + u1) := by
    rw [hs1mid, midpoint_eq_smul_add,
      show (⅟(2:ℝ)) = (1/2:ℝ) from by norm_num]
  have hs2cc : s2 = circumcenter (setOfList [u0, u1, u2]) := by
    rw [hs2def]
    exact p13t_omega2_cc V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2dist : dist u0 s2 = hl [u0, u1, u2] := by
    rw [hs2def]
    exact p13t_omega2_dist V u0 u1 u2 u3 hp hbar2 h2lt
  have hs2hull : s2 ∈ convexHull ℝ ({u0, u1, u2} : Set V3) := by
    rw [hs2def, OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3]
    have h := XNHPWAB2 V [u0, u1, u2] 2 hp hbar2 h2lt
    have hset : setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) := by
      ext x; simp [setOfList]; try tauto
    rwa [hset] at h
  -- distinctness / dimension
  obtain ⟨hu01, hu02, hu12⟩ := p13t_barV2_ne V u0 u1 u2 hbar2
  have hdim3 : affDim ({u0, u1, u2} : Set V3) = 2 := by
    have hset : ({u0, u1, u2} : Set V3) = setOfList [u0, u1, u2] := by
      ext x; simp [setOfList]; try tauto
    rw [hset]
    exact MHFTTZN1 V [u0, u1, u2] 2 hp hbar2
  have hs2notab : s2 ∉ (affineSpan ℝ ({u0, u1} : Set V3) : Set V3) := by
    rw [hs2cc]
    exact p13t_circ2_notMem_aff_pair V u0 u1 u2 hp hbar2 h2lt hu01
  -- voronoi memberships
  have hs2vor : s2 ∈ voronoiList V [u0, u1, u2] := by
    rw [hs2def]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 2 hb (by norm_num)
    rwa [hTR2] at h
  have hs3vor : s3 ∈ voronoiList V [u0, u1, u2] := by
    rw [hs3def]
    have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 3 hb le_rfl
    rw [TRUNCATE_SIMPLEX_REFL 3 _ hb.1] at h
    refine p13t_voronoiList_mono ?_ h
    intro x hx
    simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hx ⊢
    tauto
  have hsvor : s ∈ voronoiList V [u0, u1, u2] := by
    have hseg' := hseg
    rw [mem_segment_iff_div] at hseg'
    obtain ⟨α, β, hα, hβ, hαβ, hdiv⟩ := hseg'
    rw [← hdiv]
    exact CONVEX_VORONOI_LIST V [u0, u1, u2] hs2vor hs3vor (by positivity)
      (by positivity) (by rw [← add_div]; field_simp)
  have hsnot : s ∉ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) := by
    refine p13t_notMem_aff_of_vor V u0 u1 u2 s hp hbar2 hsvor ?_
    rw [hdist]; exact h2lt
  have hu0s : u0 ≠ s := fun h => hsnot (by
    rw [← h]
    exact subset_affineSpan ℝ _ (by simp))
  have hu1s : u1 ≠ s := fun h => hsnot (by
    rw [← h]
    exact subset_affineSpan ℝ _ (by simp))
  have hs2ne : s ≠ u2 := fun h => hsnot (by
    rw [h]
    exact subset_affineSpan ℝ _ (by simp))
  have hs3cc : s3 = circumcenter (setOfList [u0, u1, u2, u3]) := by
    rw [hs3def]
    obtain ⟨a, hsing, hacc, _⟩ :=
      VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, u2, u3] hp hs hb
    have htr3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
      TRUNCATE_SIMPLEX_REFL 3 _ hb.1
    have h1 : omegaListN V [u0, u1, u2, u3] 3
        = closestPoint (voronoiList V [u0, u1, u2, u3])
          (omegaListN V [u0, u1, u2, u3] 2) := by
      show closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 2) = _
      rw [htr3]
    rw [h1, hsing, CLOSEST_POINT_SING, hacc]
  have hd03 : dist u0 s3 = hl [u0, u1, u2, u3] := by
    rw [hs3cc]
    have h := HL_EQ_DIST0 V 3 [u0, u1, u2, u3] hp hb
    rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at h
    calc dist u0 (circumcenter (setOfList [u0, u1, u2, u3]))
        = dist (circumcenter (setOfList [u0, u1, u2, u3])) u0 := dist_comm ..
      _ = hl [u0, u1, u2, u3] := h.symm
  have hs3not : s3 ∉ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) := by
    refine p13t_notMem_aff_of_vor V u0 u1 u2 s3 hp hbar2 hs3vor ?_
    rw [hd03]; linarith [hcond3.2, h2lt]
  have hu0s3 : u0 ≠ s3 := fun h => hs3not (by
    rw [← h]
    exact subset_affineSpan ℝ _ (by simp))
  have hu1s3 : u1 ≠ s3 := fun h => hs3not (by
    rw [← h]
    exact subset_affineSpan ℝ _ (by simp))
  have hs3ne2 : s3 ≠ u2 := fun h => hs3not (by
    rw [h]
    exact subset_affineSpan ℝ _ (by simp))
  -- affine independence data
  have hli_ky : LinearIndependent ℝ ![u0 - s, u1 - s, u2 - s] := by
    have hbase : LinearIndependent ℝ ![u0 - u2, u1 - u2, s - u2] :=
      p13t_li_triple u0 u1 u2 s hdim3 hsnot hu02 hu12 hs2ne hu01 hu0s hu1s
    exact p13t_li_base_swap hbase
  have hli4 : LinearIndependent ℝ ![u0 - u2, u1 - u2, s3 - u2] :=
    p13t_li_triple u0 u1 u2 s3 hdim3 hs3not hu02 hu12 hs3ne2 hu01 hu0s3 hu1s3
  have hss2 : s ≠ s2 := by
    intro h
    have hh : dist u0 s2 = Real.sqrt 2 := by rw [← h]; exact hdist
    rw [hs2dist] at hh
    linarith
  -- rogers in the `u1`-basis (s1 is the midpoint of u0 u1)
  have hrog4u : p ∈ convexHull ℝ ({u0, u1, s2, s3} : Set V3) := by
    have hr := hrog4
    rw [CONVEX_HULL_4] at hr
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hbsum, hbeq⟩ := hr
    rw [CONVEX_HULL_4]
    refine ⟨b0 + b1 * (1/2), b1 * (1/2), b2, b3, ?_, ?_, hb2, hb3, ?_, ?_⟩
    · nlinarith [hb0, hb1]
    · positivity
    · linarith
    · rw [hbeq, hs1']
      module
  -- hull-intersection lemma
  have hky := p13t_hull_ky5 u0 u1 u2 s s2 s3 p hli_ky hss2 hs2hull hs2notab
    hseg h3h hrog4u
  obtain ⟨m, n, hpmn, hmab, hncd⟩ := CONVEX_HULL_4_IMP_2_2 u0 u1 s2 s p hky
  -- segment weights
  rw [mem_segment_iff_div] at hpmn
  obtain ⟨pα, pβ, hpα, hpβ, hpαβ, hpdiv⟩ := hpmn
  set θ : ℝ := pβ / (pα + pβ) with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hpαβ]; linarith
  have hpw : p = (1 - θ) • m + θ • n := by
    have h1 : (1 - θ) = pα / (pα + pβ) := by rw [hθdef]; field_simp; ring
    rw [h1, hθdef]
    exact hpdiv.symm
  rw [mem_segment_iff_div] at hmab
  obtain ⟨mα, mβ, hmα, hmβ, hmαβ, hmdiv⟩ := hmab
  set τm : ℝ := mβ / (mα + mβ) with hτmdef
  have hτm0 : 0 ≤ τm := by rw [hτmdef]; positivity
  have hτm1 : τm ≤ 1 := by rw [hτmdef, div_le_one hmαβ]; linarith
  have hmw : m = (1 - τm) • u0 + τm • u1 := by
    have h1 : (1 - τm) = mα / (mα + mβ) := by rw [hτmdef]; field_simp; ring
    rw [h1, hτmdef]
    exact hmdiv.symm
  have hncdseg : n ∈ segment ℝ s2 s := hncd
  rw [mem_segment_iff_div] at hncd
  obtain ⟨nα, nβ, hnα, hnβ, hnαβ, hndiv⟩ := hncd
  set ν : ℝ := nβ / (nα + nβ) with hνdef
  have hν0 : 0 ≤ ν := by rw [hνdef]; positivity
  have hν1 : ν ≤ 1 := by rw [hνdef, div_le_one hnαβ]; linarith
  have hnw : n = (1 - ν) • s2 + ν • s := by
    have h1 : (1 - ν) = nα / (nα + nβ) := by rw [hνdef]; field_simp; ring
    rw [h1, hνdef]
    exact hndiv.symm
  rw [mem_segment_iff_div] at hseg
  obtain ⟨sα, sβ, hsα, hsβ, hsαβ, hsdiv⟩ := hseg
  set B : ℝ := sβ / (sα + sβ) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hB1 : B ≤ 1 := by rw [hBdef, div_le_one hsαβ]; linarith
  have hsw : s = (1 - B) • s2 + B • s3 := by
    have h1 : (1 - B) = sα / (sα + sβ) := by rw [hBdef]; field_simp; ring
    rw [h1, hBdef]
    exact hsdiv.symm
  have hnw23 : n = (1 - ν * B) • s2 + (ν * B) • s3 := by
    rw [hnw, hsw]; module
  by_cases hτhalf : (1/2 : ℝ) ≤ τm
  · -- ================= Branch A: m ∈ [s1,u1] => B7 =================
    set lam : ℝ := 2 * τm - 1 with hlamdef
    have hlam0 : 0 ≤ lam := by rw [hlamdef]; linarith
    have hlam1 : lam ≤ 1 := by rw [hlamdef]; linarith
    have hu1s1 : u1 = (2:ℝ) • s1 - u0 := by
      have h : (2:ℝ) • s1 - u0 = u1 := by rw [hs1']; module
      exact h.symm
    have hmw' : m = (1 + lam) • s1 - lam • u0 := by
      rw [hmw, hu1s1, hlamdef]
      module
    have hpsegA : p = (-(1 - θ) * lam) • u0 + ((1 - θ) * (1 + lam)) • s1
        + (θ * (1 - ν * B)) • s2 + (θ * (ν * B)) • s3 := by
      rw [hpw, hmw', hnw23]
      module
    have hsumA : (-(1 - θ) * lam) + ((1 - θ) * (1 + lam))
        + (θ * (1 - ν * B)) + (θ * (ν * B)) = 1 := by
      have h1 : (-(1 - θ) * lam) + ((1 - θ) * (1 + lam))
          + (θ * (1 - ν * B)) + (θ * (ν * B))
          = (1 - θ) * (1 - lam + lam) + θ * (1 - ν * B + ν * B) := by ring
      rw [h1]; ring
    rw [CONVEX_HULL_4] at hrog4
    obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, hasum, haeq⟩ := hrog4
    -- s2 coordinates in the u2-duplicated hull
    have hs2hull4 : s2 ∈ convexHull ℝ ({u0, u1, u2, u2} : Set V3) := by
      rw [show ({u0, u1, u2, u2} : Set V3) = {u0, u1, u2} from by ext z; simp]
      exact hs2hull
    rw [CONVEX_HULL_4] at hs2hull4
    obtain ⟨k0, k1, k2, k3, hk0, hk1, hk2, hk3, hksum, hkeq⟩ := hs2hull4
    have hs2repr : s2 = k0 • u0 + k1 • u1 + (k2 + k3) • u2 := by
      rw [hkeq]; module
    have hk23ne : k2 + k3 ≠ 0 := by
      intro hz
      apply hs2notab
      have hs2eq' : s2 = k0 • u0 + k1 • u1 := by
        rw [hs2repr, hz, zero_smul, add_zero]
      have hsum01 : k0 + k1 = 1 := by linarith
      have hmem : s2 ∈ convexHull ℝ ({u0, u1} : Set V3) := by
        rw [convexHull_pair]
        exact ⟨k0, k1, hk0, hk1, hsum01, hs2eq'.symm⟩
      exact convexHull_subset_affineSpan _ hmem
    have huniq := p13t_omega_coords_unique (u0 := u0) (u1 := u1) (u2 := u2)
      (s1 := s1) (s2 := s2) (s3 := s3) (p := p)
      (m0 := k0) (m1 := k1) (m2 := k2 + k3)
      (k0 := -(1 - θ) * lam) (k1 := (1 - θ) * (1 + lam))
      (k2 := θ * (1 - ν * B)) (k3 := θ * (ν * B))
      (l0 := a0) (l1 := a1) (l2 := a2) (l3 := a3)
      hli4 hs1mid hk23ne (by linarith) hs2repr hsumA hasum hpsegA haeq
    have hk0le : -(1 - θ) * lam ≤ 0 := by
      have h1 : 0 ≤ (1 - θ) * lam := mul_nonneg (by linarith) hlam0
      linarith
    have ha0z : a0 = 0 := by
      have hle : a0 ≤ 0 := by rw [← huniq.1]; exact hk0le
      exact le_antisymm hle ha0
    have hB7mem : p ∈ convexHull ℝ ({s1, s2, s3} : Set V3) := by
      rw [show ({s1, s2, s3} : Set V3) = {s1, s2, s3, s3} from by ext z; simp]
      rw [CONVEX_HULL_4]
      refine ⟨a1, a2, a3, 0, ha1, ha2, ha3, le_rfl, by linarith, ?_⟩
      rw [haeq, ha0z]
      simp
    have hB7mem' : p ∈ (affineSpan ℝ ({s1, s2, s3} : Set V3) : Set V3) :=
      convexHull_subset_affineSpan _ hB7mem
    have hB7 : p ∈ (affineSpan ℝ ({omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2,
        omegaListN V [u0, u1, u2, u3] 3} : Set V3) : Set V3) := by
      simpa [hs1def, hs2def, hs3def] using hB7mem'
    simp only [sltZ, Set.mem_union]
    tauto
  · -- ================= Branch B: m ∈ [u0,s1] => B3 =================
    have hτhalf' : τm ≤ 1/2 := le_of_lt (lt_of_not_ge hτhalf)
    set μ : ℝ := 2 * τm with hμdef
    have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
    have hμ1 : μ ≤ 1 := by rw [hμdef]; linarith
    have hmw' : m = (1 - μ) • u0 + μ • s1 := by
      rw [hmw, hμdef, hs1']
      module
    set τq : ℝ := (1 - θ) * μ + θ with hτqdef
    have hτq0 : 0 ≤ τq := by rw [hτqdef]; positivity
    have hτq1 : τq ≤ 1 := by rw [hτqdef]; nlinarith [hθ0, hθ1, hμ0, hμ1]
    by_cases hden : τq = 0
    · -- p = m ∈ B6
      have hθz : θ = 0 := by
        have h1 : 0 ≤ (1 - θ) * μ := mul_nonneg (by linarith) hμ0
        nlinarith [hτqdef, hden, h1, hθ0]
      have hpm : p = m := by
        rw [hpw, hθz, sub_zero, one_smul, zero_smul, add_zero]
      have hm01 : m ∈ convexHull ℝ ({u0, u1} : Set V3) := by
        rw [convexHull_pair]
        exact ⟨1 - τm, τm, by linarith [hτm1], hτm0, by ring, hmw.symm⟩
      have hmaff : m ∈ (affineSpan ℝ ({u0, u1} : Set V3) : Set V3) :=
        convexHull_subset_affineSpan _ hm01
      have hB6mem : p ∈ (affineSpan ℝ ({u0, u1, u2} : Set V3) : Set V3) := by
        rw [hpm]
        exact affineSpan_mono (k := ℝ) (by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          tauto) hmaff
      have hB6 : p ∈ (affineSpan ℝ ({hdV [u0, u1, u2, u3],
          hdV [u0, u1, u2, u3].tail,
          hdV [u0, u1, u2, u3].tail.tail} : Set V3) : Set V3) := by
        simpa [hdV] using hB6mem
      simp only [sltZ, Set.mem_union]
      tauto
    · -- main case: the point q on [n,s1]
      have hτqpos : 0 < τq := lt_of_le_of_ne hτq0 (Ne.symm hden)
      set q : V3 := (θ / τq) • n + ((1 - θ) * μ / τq) • s1 with hqdef
      have hqsmul : τq • q = θ • n + ((1 - θ) * μ) • s1 := by
        rw [hqdef, smul_add, smul_smul, smul_smul,
          mul_div_cancel₀ θ (ne_of_gt hτqpos),
          mul_div_cancel₀ ((1 - θ) * μ) (ne_of_gt hτqpos)]
      have hpq : p = (1 - τq) • u0 + τq • q := by
        have hcoef : 1 - τq = (1 - θ) * (1 - μ) := by rw [hτqdef]; ring
        rw [hpw, hmw', hnw23, hqsmul, hnw23, hcoef]
        module
      have hsegp : p ∈ segment ℝ u0 q :=
        ⟨1 - τq, τq, by linarith, hτq0, by ring, hpq.symm⟩
      have hqseg : q ∈ segment ℝ n s1 := by
        refine ⟨θ / τq, (1 - θ) * μ / τq, div_nonneg hθ0 hτq0, ?_, ?_, ?_⟩
        · exact div_nonneg (mul_nonneg (by linarith) hμ0) hτq0
        · field_simp [ne_of_gt hτqpos]; ring
        · rw [hqdef]
      -- q in the Voronoi cell of {u0,u1}
      have hs1vor : s1 ∈ voronoiList V [u0, u1] := by
        rw [hs1def, OMEGA_LIST_TRUNCATE_1 V u0 u1 u2 u3]
        have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1] 1 1 hbar1 le_rfl
        rwa [TRUNCATE_SIMPLEX_REFL 1 [u0, u1] hbar1.1] at h
      have hs2vor1 : s2 ∈ voronoiList V [u0, u1] := by
        refine p13t_voronoiList_mono ?_ hs2vor
        intro z hz
        simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
          or_false] at hz ⊢
        tauto
      have hs3vor1 : s3 ∈ voronoiList V [u0, u1] := by
        refine p13t_voronoiList_mono ?_ hs3vor
        intro z hz
        simp only [setOfList, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
          or_false] at hz ⊢
        tauto
      have hνB0 : 0 ≤ ν * B := mul_nonneg hν0 hB0
      have hνB1 : ν * B ≤ 1 := by nlinarith [hν0, hν1, hB0, hB1]
      have hnvor : n ∈ voronoiList V [u0, u1] := by
        rw [hnw23]
        exact CONVEX_VORONOI_LIST V [u0, u1] hs2vor1 hs3vor1
          (by linarith [hνB1]) hνB0 (by ring)
      have hqvor : q ∈ voronoiList V [u0, u1] := by
        rw [hqdef]
        exact CONVEX_VORONOI_LIST V [u0, u1] hnvor hs1vor
          (div_nonneg hθ0 hτq0)
          (div_nonneg (mul_nonneg (by linarith) hμ0) hτq0)
          (by field_simp [ne_of_gt hτqpos]; ring)
      -- distance bound dist(q,u0) ≤ √2
      have hd01 : dist u0 s1 = hl [u0, u1] := by
        rw [hs1mid, dist_comm, dist_midpoint_left, p13_hl_pair,
          show ‖(2:ℝ)‖ = 2 from by norm_num]
        ring
      have hs1ball : dist u0 s1 ≤ Real.sqrt 2 := by
        rw [hd01]; linarith
      have hs2ball : dist u0 s2 ≤ Real.sqrt 2 := le_of_lt (by rw [hs2dist]; exact h2lt)
      have hnball : n ∈ Metric.closedBall u0 (Real.sqrt 2) := by
        rw [Metric.mem_closedBall]
        have h := (convexOn_univ_dist u0).le_on_segment
          (mem_univ s2) (mem_univ s) hncdseg
        have h2 : max (dist s2 u0) (dist s u0) ≤ Real.sqrt 2 := by
          apply max_le
          · rwa [dist_comm]
          · rw [dist_comm, hdist]
        exact h.trans h2
      have hqball : q ∈ Metric.closedBall u0 (Real.sqrt 2) := by
        rw [Metric.mem_closedBall]
        have h := (convexOn_univ_dist u0).le_on_segment
          (mem_univ n) (mem_univ s1) hqseg
        have h2 : max (dist n u0) (dist s1 u0) ≤ Real.sqrt 2 := by
          apply max_le
          · simpa [Metric.mem_closedBall] using hnball
          · simpa [dist_comm] using hs1ball
        exact h.trans h2
      have hqdist : dist q u0 ≤ Real.sqrt 2 := by
        simpa [Metric.mem_closedBall] using hqball
      -- orthogonality (q - s1) ⊥ (u1 - u0)
      have hcc1 : circumcenter (setOfList [u0, u1]) = s1 := by
        rw [show setOfList [u0, u1] = ({u0, u1} : Set V3) from by
          ext z; simp [setOfList], CIRCUMCENTER_2]
        exact hs1mid.symm
      have hqvor' : q ∈ (affineSpan ℝ (voronoiList V [u0, u1]) : Set V3) :=
        subset_affineSpan ℝ _ hqvor
      have hu1aff : u1 ∈ (affineSpan ℝ (setOfList [u0, u1]) : Set V3) :=
        subset_affineSpan ℝ _ (by simp [setOfList])
      have horth1 := MHFTTZN4 V [u0, u1] 1 q u1 hp hbar1 hqvor' hu1aff
      have horth1i : inner ℝ (q - circumcenter (setOfList [u0, u1]))
          (u1 - circumcenter (setOfList [u0, u1])) = 0 := by
        rw [inner_eq_dot]
        exact horth1
      rw [hcc1] at horth1i
      have horth2 : inner ℝ (q - s1) (u1 - u0) = 0 := by
        have h2 : (u1 - u0 : V3) = (2:ℝ) • (u1 - s1) := by
          rw [hs1']; module
        calc inner ℝ (q - s1) (u1 - u0)
            = inner ℝ (q - s1) ((2:ℝ) • (u1 - s1)) := by rw [h2]
          _ = 2 * inner ℝ (q - s1) (u1 - s1) :=
              real_inner_smul_right (q - s1) (u1 - s1) 2
          _ = 2 * 0 := by rw [horth1i]
          _ = 0 := by ring
      have hs1u0 : (s1 - u0 : V3) = (1/2:ℝ) • (u1 - u0) := by
        rw [hs1']; module
      have hinner_q : inner ℝ (q - u0) (u1 - u0) = (1/2) * ‖u1 - u0‖^2 := by
        have hde : (q - u0 : V3) = (q - s1) + (s1 - u0) := by abel
        rw [hde, inner_add_left, horth2, zero_add, hs1u0, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
      have hinner_qd : (q - u0) ⬝ᵥ (u1 - u0) = (1/2) * ‖u1 - u0‖^2 := by
        have h := hinner_q
        rwa [inner_eq_dot] at h
      -- q is in the (closed) radial cone
      have hqineq : dist q u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2)
          ≤ inner ℝ (q - u0) (u1 - u0) := by
        rw [hinner_q]
        have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        have hAs : dist q u0 * (Real.sqrt 2)⁻¹ ≤ 1 := by
          have h1 := mul_le_mul_of_nonneg_right hqdist (inv_nonneg.mpr hs2pos.le)
          rwa [mul_inv_cancel₀ (ne_of_gt hs2pos)] at h1
        have hkey : dist q u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2)
            = (dist q u0 * (Real.sqrt 2)⁻¹) * ((‖u1 - u0‖^2) / 2) := by
          rw [p13_hl_pair,
            show dist u1 u0 = ‖u1 - u0‖ from dist_eq_norm u1 u0,
            show dist u0 u1 = ‖u1 - u0‖ from by rw [dist_eq_norm, norm_sub_rev]]
          field_simp
        rw [hkey]
        have h3 : (dist q u0 * (Real.sqrt 2)⁻¹) * ((‖u1 - u0‖^2) / 2)
            ≤ 1 * ((‖u1 - u0‖^2) / 2) :=
          mul_le_mul_of_nonneg_right hAs (by positivity)
        rw [one_mul] at h3
        calc dist q u0 * (Real.sqrt 2)⁻¹ * ((‖u1 - u0‖^2) / 2)
            ≤ (‖u1 - u0‖^2) / 2 := h3
          _ = (1/2) * ‖u1 - u0‖^2 := by ring
      have hqconed : (q - u0) ⬝ᵥ (u1 - u0)
          ≥ dist q u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2) := by
        have h := hqineq
        rwa [inner_eq_dot] at h
      have hqcone : q ∈ rconeGe u0 u1 (hl [u0, u1] / Real.sqrt 2) := by
        rw [rconeGe, Set.mem_setOf_eq]
        exact hqconed
      -- cone homogeneity: p = u0 + τq (q - u0)
      have hpd : (p - u0 : V3) = τq • (q - u0) := by
        rw [hpq]; module
      have hdistp : dist p u0 = τq * dist q u0 := by
        rw [dist_eq_norm, dist_eq_norm, hpd, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hτq0]
      have hpineq : dist p u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2)
          ≤ inner ℝ (p - u0) (u1 - u0) := by
        rw [hpd, real_inner_smul_left, hinner_q, hdistp]
        have hmul := mul_le_mul_of_nonneg_left hqineq hτq0
        rw [hinner_q] at hmul
        nlinarith [hmul]
      have hpconed : (p - u0) ⬝ᵥ (u1 - u0)
          ≥ dist p u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2) := by
        have h := hpineq
        rwa [inner_eq_dot] at h
      have hpcone : p ∈ rconeGe u0 u1 (hl [u0, u1] / Real.sqrt 2) := by
        rw [rconeGe, Set.mem_setOf_eq]
        exact hpconed
      -- equality with the strict cone complement gives B3
      have hpge : (p - u0) ⬝ᵥ (u1 - u0)
          ≥ dist p u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2) := by
        rw [rconeGe, Set.mem_setOf_eq] at hpcone
        exact hpcone
      have hple : ¬ ((p - u0) ⬝ᵥ (u1 - u0)
          > dist p u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2)) := by
        intro hgt
        apply hnotgt
        rw [rconeGt, Set.mem_setOf_eq]
        exact hgt
      have heq : (p - u0) ⬝ᵥ (u1 - u0)
          = dist p u0 * dist u1 u0 * (hl [u0, u1] / Real.sqrt 2) :=
        le_antisymm (le_of_not_gt hple) hpge
      have hB3 : p ∈ rconeEq (hdV [u0, u1, u2, u3])
          (hdV [u0, u1, u2, u3].tail)
          (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) := by
        show inner ℝ (p - hdV [u0, u1, u2, u3])
          (hdV [u0, u1, u2, u3].tail - hdV [u0, u1, u2, u3]) = _
        rw [show hdV [u0, u1, u2, u3] = u0 from rfl,
          show hdV [u0, u1, u2, u3].tail = u1 from rfl,
          (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
        rw [inner_eq_dot]
        exact heq
      simp only [sltZ, Set.mem_union]
      tauto

/-- Under `hl ul < √2` every vertex of the Rogers simplex is within `√2` of
`u0`, hence so is the whole simplex; therefore points of `mcell0` (which are
outside the open ball) lie exactly on the sphere `B2`. -/
private theorem p13t_mcell0_subset_B2 (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hlt : hl ul < Real.sqrt 2) (h0 : p ∈ mcell 0 V ul) :
    p ∈ ({w : V3 | ‖w - hdV ul‖ = Real.sqrt 2}) := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb
  rw [(MCELL_EXPLICIT 0 V [u0, u1, u2, u3]).1, mcell0] at h0
  have hfar : Real.sqrt 2 ≤ dist p u0 := by
    have hh := h0.2
    simpa [Metric.mem_ball, not_lt, show hdV [u0, u1, u2, u3] = u0 from rfl]
      using hh
  have hbar2 : barV V 2 [u0, u1, u2] := by
    rw [← (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
    exact TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
  have hdec2 : hl [u0, u1, u2] ≤ hl [u0, u1, u2, u3] := by
    have h := HL_DECREASE V [u0, u1, u2, u3] 3 2 hp hb (by omega)
    rwa [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2] at h
  have h2lt : hl [u0, u1, u2] < Real.sqrt 2 := lt_of_le_of_lt hdec2 hlt
  have hdec1 : hl [u0, u1] ≤ hl [u0, u1, u2] := by
    have h := HL_DECREASE V [u0, u1, u2] 2 1 hp hbar2 (by omega)
    rwa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1] at h
  have hbar1 : barV V 1 [u0, u1] := by
    rw [← (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1]
    exact TRUNCATE_SIMPLEX_BARV V 1 2 [u0, u1, u2] hbar2 (by omega)
  have hs1bound : dist u0 (omegaListN V [u0, u1, u2, u3] 1) ≤ Real.sqrt 2 := by
    have hs1mid : omegaListN V [u0, u1, u2, u3] 1 = midpoint ℝ u0 u1 := by
      rw [OMEGA_LIST_TRUNCATE_1 V u0 u1 u2 u3,
        XNHPWAB1 V [u0, u1] 1 hp hbar1 (lt_of_le_of_lt hdec1 h2lt)]
      have hset : setOfList [u0, u1] = ({u0, u1} : Set V3) := by
        ext x; simp [setOfList]; try tauto
      rw [hset, CIRCUMCENTER_2]
    have hd : dist u0 (omegaListN V [u0, u1, u2, u3] 1) = hl [u0, u1] := by
      rw [hs1mid, dist_comm, dist_midpoint_left, p13_hl_pair,
        show ‖(2:ℝ)‖ = 2 from by norm_num]
      ring
    rw [hd]; linarith
  have hs2bound : dist u0 (omegaListN V [u0, u1, u2, u3] 2) ≤ Real.sqrt 2 := by
    rw [p13t_omega2_dist V u0 u1 u2 u3 hp hbar2 h2lt]
    linarith
  have hs3cc : omegaListN V [u0, u1, u2, u3] 3
      = circumcenter (setOfList [u0, u1, u2, u3]) := by
    obtain ⟨a, hsing, hacc, _⟩ :=
      VORONOI_LIST_3_SINGLETON_EXPLICIT V [u0, u1, u2, u3] hp hs hb
    have htr3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
      TRUNCATE_SIMPLEX_REFL 3 _ hb.1
    have h1 : omegaListN V [u0, u1, u2, u3] 3
        = closestPoint (voronoiList V [u0, u1, u2, u3])
          (omegaListN V [u0, u1, u2, u3] 2) := by
      show closestPoint (voronoiList V (truncateSimplex 3 [u0, u1, u2, u3]))
        (omegaListN V [u0, u1, u2, u3] 2) = _
      rw [htr3]
    rw [h1, hsing, CLOSEST_POINT_SING, hacc]
  have hs3bound : dist u0 (omegaListN V [u0, u1, u2, u3] 3) ≤ Real.sqrt 2 := by
    rw [hs3cc]
    have h := HL_EQ_DIST0 V 3 [u0, u1, u2, u3] hp hb
    rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at h
    calc dist u0 (circumcenter (setOfList [u0, u1, u2, u3]))
        = dist (circumcenter (setOfList [u0, u1, u2, u3])) u0 := dist_comm ..
      _ = hl [u0, u1, u2, u3] := h.symm
      _ ≤ Real.sqrt 2 := le_of_lt hlt
  have hrog : p ∈ convexHull ℝ ({u0, omegaListN V [u0, u1, u2, u3] 1,
      omegaListN V [u0, u1, u2, u3] 2,
      omegaListN V [u0, u1, u2, u3] 3} : Set V3) := by
    have h := h0.1
    rw [ROGERS_EXPLICIT V [u0, u1, u2, u3] hs hp hb] at h
    simpa [show hdV [u0, u1, u2, u3] = u0 from rfl] using h
  have hbound : dist p u0 ≤ Real.sqrt 2 := by
    have hsub : convexHull ℝ ({u0, omegaListN V [u0, u1, u2, u3] 1,
        omegaListN V [u0, u1, u2, u3] 2,
        omegaListN V [u0, u1, u2, u3] 3} : Set V3) ⊆
        Metric.closedBall u0 (Real.sqrt 2) := by
      refine convexHull_min ?_ (convex_closedBall _ _)
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simp [Metric.mem_closedBall]
      · simpa [Metric.mem_closedBall, dist_comm] using hs1bound
      · simpa [Metric.mem_closedBall, dist_comm] using hs2bound
      · simpa [Metric.mem_closedBall, dist_comm] using hs3bound
    simpa [Metric.mem_closedBall] using hsub hrog
  have heq : dist p u0 = Real.sqrt 2 := le_antisymm hbound hfar
  simpa [dist_eq_norm, show hdV [u0, u1, u2, u3] = u0 from rfl] using heq

/-- Off `Z`, the covering cell index of a point is unique
(`i,j ≤ 4`, `p ∈ mcell i ∩ mcell j` implies `i = j`). -/
private theorem p13_cell_unique_off_Z (V : Set V3) (ul : List V3) (p : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hpZ : p ∈ rogers V ul \ sltZ V ul)
    {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 4)
    (hpi : p ∈ mcell i V ul) (hpj : p ∈ mcell j V ul) : i = j := by
  by_cases h4 : p ∈ mcell 4 V ul
  · have hlt : hl ul < Real.sqrt 2 := by
      by_contra hc
      rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4), mcell4, if_neg hc] at h4
      exact absurd h4 (Set.notMem_empty p)
    have hall : ∀ k : ℕ, k ≤ 4 → p ∈ mcell k V ul → k = 4 := by
      intro k hk hpk
      interval_cases k
      · exfalso
        apply hpZ.2
        have hB2 := p13t_mcell0_subset_B2 V ul p hs hp hb hlt hpk
        simp only [sltZ, Set.mem_union]
        tauto
      · rw [(MCELL_EXPLICIT 1 V ul).2.1, mcell1,
          if_neg (not_le.mpr hlt)] at hpk
        exact absurd hpk (Set.notMem_empty p)
      · rw [(MCELL_EXPLICIT 2 V ul).2.2.1, mcell2,
          if_neg (by intro h; exact absurd h.2 (not_le.mpr hlt))] at hpk
        exact absurd hpk (Set.notMem_empty p)
      · rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1, mcell3,
          if_neg (by intro h; exact absurd h.2 (not_le.mpr hlt))] at hpk
        exact absurd hpk (Set.notMem_empty p)
      · rfl
    rw [hall i hi hpi, hall j hj hpj]
  · have hi3 : i ≤ 3 := by
      rcases Nat.lt_or_ge i 4 with h | h
      · omega
      · exfalso
        have hEq : mcell i V ul = mcell4 V ul := (MCELL_EXPLICIT i V ul).2.2.2.2 h
        rw [hEq, ← (MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4)] at hpi
        exact h4 hpi
    have hj3 : j ≤ 3 := by
      rcases Nat.lt_or_ge j 4 with h | h
      · omega
      · exfalso
        have hEq : mcell j V ul = mcell4 V ul := (MCELL_EXPLICIT j V ul).2.2.2.2 h
        rw [hEq, ← (MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4)] at hpj
        exact h4 hpj
    interval_cases i <;> interval_cases j
    · rfl
    · exact (p13_disjoint_mcell0_mcell1 V ul p hpZ hpi hpj).elim
    · exact (p13_disjoint_mcell0_mcell2 V ul p hs hp hb hpZ hpi hpj).elim
    · exact (hpZ.2 (p13t_mcell0_mcell3_subset_Z V ul p hs hp hb hpi hpj)).elim
    · exact (p13_disjoint_mcell0_mcell1 V ul p hpZ hpj hpi).elim
    · rfl
    · exact (p13_disjoint_mcell1_mcell2 V ul p hpZ hpi hpj).elim
    · exact (hpZ.2 (p13t_mcell1_mcell3_subset_Z V ul p hs hp hb hpi hpj)).elim
    · exact (p13_disjoint_mcell0_mcell2 V ul p hs hp hb hpZ hpj hpi).elim
    · exact (p13_disjoint_mcell1_mcell2 V ul p hpZ hpj hpi).elim
    · rfl
    · exact (hpZ.2 (p13t_mcell2_mcell3_subset_Z V ul p hs hp hb hpi hpj)).elim
    · exact (hpZ.2 (p13t_mcell0_mcell3_subset_Z V ul p hs hp hb hpj hpi)).elim
    · exact (hpZ.2 (p13t_mcell1_mcell3_subset_Z V ul p hs hp hb hpj hpi)).elim
    · exact (hpZ.2 (p13t_mcell2_mcell3_subset_Z V ul p hs hp hb hpj hpi)).elim
    · rfl

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
  refine ⟨sltZ V ul, fun p hs hp hb => ⟨p13_sltZ_null V ul hs hp hb, ?_⟩⟩
  rintro ⟨hpR, hpZ⟩
  obtain ⟨i, hi4, hpi⟩ := p13_sltstlo2_exists V ul p hs hp hb ⟨hpR, hpZ⟩
  refine ⟨i, ⟨hi4, hpi⟩, ?_⟩
  rintro j ⟨hj4, hpj⟩
  exact (p13_cell_unique_off_Z V ul p hs hp hb ⟨hpR, hpZ⟩ hi4 hj4 hpi hpj).symm

/-! ## DDZUPHJ.hl: the capstone -/

/-- B7 helper: along an equal omega chain, `sqrt 2 ≤ hl ul` transfers to
`vl`. Contrapositively, `hl vl < sqrt 2` gives
`hl vl = dist (omegaList V vl) (HD vl)` (`WAUFCHE2`), and the `ul` side
bounds the same distance from below (`WAUFCHE1`), with the two distances
identified through `OMEGA_LIST_LEMMA` and the `HD` equality at `i = 0`. -/
private theorem p13_dd_hl_ge_of_omega_eq (V : Set V3) (ul vl : List V3)
    (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (homega : ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i)
    (hge : Real.sqrt 2 ≤ hl ul) : Real.sqrt 2 ≤ hl vl := by
  by_contra hcon
  have hlt : hl vl < Real.sqrt 2 := lt_of_not_ge hcon
  have hw2 := WAUFCHE2 V vl 3 hp hb2 hlt
  have hw1 := WAUFCHE1 V ul 3 hp hb1
  have hLu : omegaList V ul = omegaListN V ul 3 := by simp [omegaList, hb1.1]
  have hLv : omegaList V vl = omegaListN V vl 3 := by simp [omegaList, hb2.1]
  have hd0 : hdV ul = hdV vl := homega 0 (by norm_num)
  have heq : dist (omegaList V ul) (hdV ul) = dist (omegaList V vl) (hdV vl) := by
    rw [hLu, hLv, homega 3 (by norm_num), hd0]
  have hge' : Real.sqrt 2 ≤ dist (omegaList V vl) (hdV vl) := by
    rw [← heq]
    exact le_trans hge hw1
  rw [← hw2] at hge'
  exact absurd hge' hcon

/-- B7 helper: the `mxi` regime test `sqrt 2 ≤ hl (truncateSimplex 2 ·)`
transfers along an equal omega chain. If it failed on `vl`, `WAUFCHE2` on
the `vl` truncation would exhibit `hl (truncateSimplex 2 vl)` as the
distance of the common `(omega 2, HD)` pair, while `WAUFCHE1` on the `ul`
truncation bounds that distance below by `hl (truncateSimplex 2 ul) ≥
sqrt 2`. -/
private theorem p13_dd_hl_trunc2_ge_of_omega_eq (V : Set V3) (ul vl : List V3)
    (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (homega : ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i)
    (hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 ul)) :
    Real.sqrt 2 ≤ hl (truncateSimplex 2 vl) := by
  by_contra hcon
  have hlt : hl (truncateSimplex 2 vl) < Real.sqrt 2 := lt_of_not_ge hcon
  have hlen1 : ul.length = 4 := hb1.1
  have hlen2 : vl.length = 4 := hb2.1
  have hbaru : barV V 2 (truncateSimplex 2 ul) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 ul hb1 (by omega)
  have hbarv : barV V 2 (truncateSimplex 2 vl) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 vl hb2 (by omega)
  have hw2 := WAUFCHE2 V (truncateSimplex 2 vl) 2 hp hbarv hlt
  have hw1 := WAUFCHE1 V (truncateSimplex 2 ul) 2 hp hbaru
  have hLu : omegaList V (truncateSimplex 2 ul) = omegaListN V ul 2 :=
    OMEGA_LIST_LEMMA V ul 2 (by omega)
  have hLv : omegaList V (truncateSimplex 2 vl) = omegaListN V vl 2 :=
    OMEGA_LIST_LEMMA V vl 2 (by omega)
  have hDu : hdV (truncateSimplex 2 ul) = hdV ul := HD_TRUNCATE_SIMPLEX ul 2 (by omega)
  have hDv : hdV (truncateSimplex 2 vl) = hdV vl := HD_TRUNCATE_SIMPLEX vl 2 (by omega)
  have hd0 : hdV ul = hdV vl := homega 0 (by norm_num)
  have hchain : hl (truncateSimplex 2 ul) ≤ hl (truncateSimplex 2 vl) := by
    calc hl (truncateSimplex 2 ul)
        ≤ dist (omegaList V (truncateSimplex 2 ul)) (hdV (truncateSimplex 2 ul)) := hw1
      _ = dist (omegaListN V ul 2) (hdV ul) := by rw [hLu, hDu]
      _ = dist (omegaListN V vl 2) (hdV vl) := by rw [homega 2 (by norm_num), hd0]
      _ = dist (omegaList V (truncateSimplex 2 vl)) (hdV (truncateSimplex 2 vl)) := by
          rw [hLv, hDv]
      _ = hl (truncateSimplex 2 vl) := hw2.symm
  linarith

/-- B7 helper: the two `mxi` choices agree along an equal omega chain. In the
`omega 2` branch the regime test is transferred by
`p13_dd_hl_trunc2_ge_of_omega_eq`; in the `@`-branch the defining predicates
are literally the same (`omega 2`, `omega 3`, `HD` all agree). -/
private theorem p13_dd_mxi_eq_of_omega (V : Set V3) (ul vl : List V3)
    (hp : Packing V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (homega : ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i) :
    mxi V ul = mxi V vl := by
  have hd0 : hdV ul = hdV vl := homega 0 (by norm_num)
  by_cases h2 : Real.sqrt 2 ≤ hl (truncateSimplex 2 ul)
  · have h2v : Real.sqrt 2 ≤ hl (truncateSimplex 2 vl) :=
      p13_dd_hl_trunc2_ge_of_omega_eq V ul vl hp hb1 hb2 homega h2
    conv_lhs => rw [mxi, if_pos h2]
    conv_rhs => rw [mxi, if_pos h2v]
    rw [homega 2 (by norm_num)]
  · have h2v : ¬ Real.sqrt 2 ≤ hl (truncateSimplex 2 vl) := by
      intro hc
      exact h2 (p13_dd_hl_trunc2_ge_of_omega_eq V vl ul hp hb2 hb1
        (fun i hi => (homega i hi).symm) hc)
    conv_lhs => rw [mxi, if_neg h2]
    conv_rhs => rw [mxi, if_neg h2v]
    have hpred : (fun p : V3 => p ∈ convexHull ℝ
        ({omegaListN V ul 2, omegaListN V ul 3} : Set V3) ∧
        dist p (hdV ul) = Real.sqrt 2) =
        (fun p : V3 => p ∈ convexHull ℝ
        ({omegaListN V vl 2, omegaListN V vl 3} : Set V3) ∧
        dist p (hdV vl) = Real.sqrt 2) := by
      funext p
      rw [homega 2 (by norm_num), homega 3 (by norm_num), hd0]
    exact congrArg (fun f : V3 → Prop => Classical.epsilon f) hpred

/-- GIANT — HOL `DDZUPHJ` (DDZUPHJ.hl:59-608; concl DDZUPHJ.hl:29-34): two
`barV V 3` lists with the same full-dimensional Rogers simplex carry the
same Marchal cell of every index `k ∈ {0..4}` with nonempty `mcell k V ul`.
(HOL `k IN {0,1,2,3,4}` rendered as `k ≤ 4`.) No pack_concl interface
exists for this statement; it consumes Auto9's `TEZFFSK`/`NJIUTIU`.

FILLED (B7, 2026-10-22; HOL proof architecture `k = 4,3,2,1,0`). The omega
chain agrees by `NJIUTIU` throughout, so `HD ul = HD vl` comes straight from
its `i = 0` instance (no `ROGERS_INTER_V_LEMMA` needed). `k = 4`:
nonemptiness gives `hl ul < sqrt 2`; `TEZFFSK` at `k = 3` identifies the full
lists. `k = 3,2,1`: nonemptiness gives the circumradius regime
(`hl (truncateSimplex (k-1) ul) < sqrt 2`, `sqrt 2 ≤ hl ul`); `TEZFFSK` at
`k - 1` identifies the truncation, `p13_dd_hl_ge_of_omega_eq` transfers
`sqrt 2 ≤ hl vl`, and `mxi` agrees by `p13_dd_mxi_eq_of_omega` (which uses
`p13_dd_hl_trunc2_ge_of_omega_eq`, `WAUFCHE1/2`, `OMEGA_LIST_LEMMA`,
`HD_TRUNCATE_SIMPLEX`). `k = 2` additionally reads `{u0,u1} = {v0,v1}` off
the shared truncation (`BARV_3_EXPLICIT` + `TRUNCATE_SIMPLEX_EXPLICIT_1`),
`k = 1`'s tail case discharges the `rconeGt` factor by
`RCONE_GT_EQ_EMPTY_LEMMA` once `sqrt 2 ≤ hl (truncateSimplex 1 ·)`, and
`k = 0` is the shared Rogers simplex minus the same ball. Cell definitions
dispatch via `MCELL_EXPLICIT`. -/
theorem DDZUPHJ (V : Set V3) (ul vl : List V3) (k : ℕ)
    (hs : saturated V) (hp : Packing V) (hk : k ≤ 4)
    (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
    (hne : mcell k V ul ≠ ∅) :
    mcell k V ul = mcell k V vl := by
  have homega : ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i :=
    NJIUTIU V ul vl hs hp hb1 hb2 hrogers hdim
  have hHD : hdV ul = hdV vl := homega 0 (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk5 with rfl | rfl | rfl | rfl | rfl
  · -- ===================== k = 0 =====================
    rw [(MCELL_EXPLICIT 0 V ul).1, (MCELL_EXPLICIT 0 V vl).1]
    simp only [mcell0]
    rw [hrogers, hHD]
  · -- ===================== k = 1 =====================
    have hH : Real.sqrt 2 ≤ hl ul := by
      by_contra h
      have hempty : mcell1 V ul = ∅ := by rw [mcell1, if_neg h]
      rw [(MCELL_EXPLICIT 1 V ul).2.1, hempty] at hne
      exact hne rfl
    have hHv : Real.sqrt 2 ≤ hl vl :=
      p13_dd_hl_ge_of_omega_eq V ul vl hp hb1 hb2 homega hH
    by_cases hlt1 : hl (truncateSimplex 1 ul) < Real.sqrt 2
    · -- truncation below sqrt 2: TEZFFSK identifies the pair
      obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb1
      obtain ⟨v0, v1, v2, v3, rfl⟩ := BARV_3_EXPLICIT V vl hb2
      have htr1 : truncateSimplex 1 [u0, u1, u2, u3] =
          truncateSimplex 1 [v0, v1, v2, v3] :=
        TEZFFSK V [u0, u1, u2, u3] [v0, v1, v2, v3] 1 hs hp hb1 hb2 hrogers hdim
          (by norm_num) hlt1
      have hpair : [u0, u1] = [v0, v1] := by
        simpa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2] using htr1
      have hpair' : u0 = v0 ∧ u1 = v1 := by
        simpa [List.cons.injEq] using hpair
      have hu0 : u0 = v0 := hpair'.1
      have hu1 : u1 = v1 := hpair'.2
      have e0 : hdV [u0, u1, u2, u3] = u0 := rfl
      have e1 : hdV [u0, u1, u2, u3].tail = u1 := rfl
      have f0 : hdV [v0, v1, v2, v3] = v0 := rfl
      have f1 : hdV [v0, v1, v2, v3].tail = v1 := rfl
      conv_lhs => rw [(MCELL_EXPLICIT 1 V [u0, u1, u2, u3]).2.1, mcell1, if_pos hH]
      conv_rhs => rw [(MCELL_EXPLICIT 1 V [v0, v1, v2, v3]).2.1, mcell1, if_pos hHv]
      rw [hrogers, htr1, e0, e1, f0, f1, hu0, hu1]
    · -- truncation at least sqrt 2: both strict cones are empty
      have hge1 : Real.sqrt 2 ≤ hl (truncateSimplex 1 ul) := le_of_not_gt hlt1
      have hge1v : Real.sqrt 2 ≤ hl (truncateSimplex 1 vl) := by
        by_contra h
        have hltv : hl (truncateSimplex 1 vl) < Real.sqrt 2 := lt_of_not_ge h
        have hdimv : affDim (rogers V vl) = 3 := by rw [← hrogers]; exact hdim
        have htr := TEZFFSK V vl ul 1 hs hp hb2 hb1 hrogers.symm hdimv
          (by norm_num) hltv
        have hsmall : hl (truncateSimplex 1 ul) < Real.sqrt 2 := by
          rw [← htr]
          exact hltv
        exact absurd hsmall (not_lt.mpr hge1)
      have hempty_u : rconeGt (hdV ul) (hdV ul.tail)
          (hl (truncateSimplex 1 ul) / Real.sqrt 2) = ∅ :=
        RCONE_GT_EQ_EMPTY_LEMMA _ _ _ ((le_div_iff₀ h2pos).mpr (by linarith))
      have hempty_v : rconeGt (hdV vl) (hdV vl.tail)
          (hl (truncateSimplex 1 vl) / Real.sqrt 2) = ∅ :=
        RCONE_GT_EQ_EMPTY_LEMMA _ _ _ ((le_div_iff₀ h2pos).mpr (by linarith))
      conv_lhs => rw [(MCELL_EXPLICIT 1 V ul).2.1, mcell1, if_pos hH]
      conv_rhs => rw [(MCELL_EXPLICIT 1 V vl).2.1, mcell1, if_pos hHv]
      rw [hempty_u, hempty_v]
      simp only [Set.sdiff_empty]
      rw [hrogers, hHD]
  · -- ===================== k = 2 =====================
    obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb1
    obtain ⟨v0, v1, v2, v3, rfl⟩ := BARV_3_EXPLICIT V vl hb2
    have hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
      by_contra h
      have hempty : mcell2 V [u0, u1, u2, u3] = ∅ := by rw [mcell2, if_neg h]
      rw [(MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1, hempty] at hne
      exact hne rfl
    have htr1 : truncateSimplex 1 [u0, u1, u2, u3] =
        truncateSimplex 1 [v0, v1, v2, v3] :=
      TEZFFSK V [u0, u1, u2, u3] [v0, v1, v2, v3] 1 hs hp hb1 hb2 hrogers hdim
        (by norm_num) hcond.1
    have hge_vl : Real.sqrt 2 ≤ hl [v0, v1, v2, v3] :=
      p13_dd_hl_ge_of_omega_eq V [u0, u1, u2, u3] [v0, v1, v2, v3] hp hb1 hb2
        homega hcond.2
    have hcondv : hl (truncateSimplex 1 [v0, v1, v2, v3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [v0, v1, v2, v3] := by
      rw [← htr1]
      exact ⟨hcond.1, hge_vl⟩
    have hmxi : mxi V [u0, u1, u2, u3] = mxi V [v0, v1, v2, v3] :=
      p13_dd_mxi_eq_of_omega V [u0, u1, u2, u3] [v0, v1, v2, v3] hp hb1 hb2 homega
    have hpair : [u0, u1] = [v0, v1] := by
      simpa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
        (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2] using htr1
    have hpair' : u0 = v0 ∧ u1 = v1 := by
      simpa [List.cons.injEq] using hpair
    have hu0 : u0 = v0 := hpair'.1
    have hu1 : u1 = v1 := hpair'.2
    have e0 : hdV [u0, u1, u2, u3] = u0 := rfl
    have e1 : hdV [u0, u1, u2, u3].tail = u1 := rfl
    have f0 : hdV [v0, v1, v2, v3] = v0 := rfl
    have f1 : hdV [v0, v1, v2, v3].tail = v1 := rfl
    conv_lhs => rw [(MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1, mcell2, if_pos hcond]
    conv_rhs => rw [(MCELL_EXPLICIT 2 V [v0, v1, v2, v3]).2.2.1, mcell2, if_pos hcondv]
    dsimp only
    rw [htr1, hmxi, e0, e1, f0, f1, homega 3 (by norm_num), hu0, hu1]
  · -- ===================== k = 3 =====================
    have hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := by
      by_contra h
      have hempty : mcell3 V ul = ∅ := by rw [mcell3, if_neg h]
      rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1, hempty] at hne
      exact hne rfl
    have htr2 : truncateSimplex 2 ul = truncateSimplex 2 vl :=
      TEZFFSK V ul vl 2 hs hp hb1 hb2 hrogers hdim (by norm_num) hcond.1
    have hge_vl : Real.sqrt 2 ≤ hl vl :=
      p13_dd_hl_ge_of_omega_eq V ul vl hp hb1 hb2 homega hcond.2
    have hcondv : hl (truncateSimplex 2 vl) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl vl := by
      rw [← htr2]
      exact ⟨hcond.1, hge_vl⟩
    have hmxi : mxi V ul = mxi V vl :=
      p13_dd_mxi_eq_of_omega V ul vl hp hb1 hb2 homega
    conv_lhs => rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1, mcell3, if_pos hcond]
    conv_rhs => rw [(MCELL_EXPLICIT 3 V vl).2.2.2.1, mcell3, if_pos hcondv]
    rw [htr2, hmxi]
  · -- ===================== k = 4 =====================
    have hlt : hl ul < Real.sqrt 2 := by
      by_contra h
      have hempty : mcell4 V ul = ∅ := by rw [mcell4, if_neg h]
      rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4), hempty] at hne
      exact hne rfl
    obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hb1
    obtain ⟨v0, v1, v2, v3, rfl⟩ := BARV_3_EXPLICIT V vl hb2
    have hlt3 : hl (truncateSimplex 3 [u0, u1, u2, u3]) < Real.sqrt 2 := by
      rw [TRUNCATE_SIMPLEX_EXPLICIT_3]
      exact hlt
    have htr := TEZFFSK V [u0, u1, u2, u3] [v0, v1, v2, v3] 3 hs hp hb1 hb2
      hrogers hdim (by norm_num) hlt3
    have heq : [u0, u1, u2, u3] = [v0, v1, v2, v3] := by
      simpa [(TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3),
        (TRUNCATE_SIMPLEX_EXPLICIT_3 v0 v1 v2 v3)] using htr
    rw [heq]

end Kepler.Text
