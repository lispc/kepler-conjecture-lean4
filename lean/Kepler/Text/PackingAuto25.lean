/-
PackingAuto25: port of `scripts/packing/OXLZLEZ3.hl` (Flyspeck chapter
"packing / OXLZLEZ", T. Hales, 9038 lines; 6 `new_definition`s + 129-theorem
statement surface re-derived here — the file actually carries ~208
declarations: 6 defs + ~202 `prove_by_refinement` theorems + 2 tactic
helpers absorbed into proofs).

FILE MAP (the FINAL packing capstone)
  This is the last file of the packing chain: it proves `OXLZLEZ`,
  `!V. pack_nonlinear_non_ox3q1h /\ ox3q1h /\ packing V /\ saturated V ==>
  cell_cluster_inequality V`, i.e. the cell-cluster inequality, from the
  cc_v11 compressed-model case analysis (PackingAuto3/4: `CcV11`,
  `cc_bool_model_v11`, `cc_real_model_v11`, `GRHIDFA`).  Payload:
  (a) the leaf-ranking gadget: `s_leaf` (the set of leaves on a stem),
      `leaf_rank` (a cyclic azim-increasing parametrization of `s_leaf` by
      `0..n-1`), `gg_mcell`/`azim_mcell` (the gamma-weight and dihedral sums
      over the Marchal cells in one wedge), `cc_4` (wedge has a 4-cell);
  (b) `cc_data_v8`: the compression `cc_v11` of the geometric data of an
      edge `(u0,u1)` — the bridge object between geometry and the
      combinatorial cc_v11 model (PackingAuto3);
  (c) the wedge bookkeeping (CC_4_PROPS, CC_3_PROPS, CC_2_PROPS,
      MCELL{2,3,4}_*, EDGE_IMP_K23), the certified `real_model_*` inequality
      bank per wedge type (quarter, fhbv2, quqy, ztg4, azim1, gaz4/6/9,
      gamma_qx/8/8b/10/11, gamma10/11, pema/pemb, txq, tew, 008, cell23,
      3a/3b, gr, ox3q1h_merge), the three merged numeric inequalities
      IXPOTPA/TXQTPVC/TEWNSCJ, and the endgame: `cc_real_model_data` →
      `CELL_CLUSTER_ESTIMATE_PROPS` → `OXLZLEZ` →
      `PACKING_CHAPTER_MAIN_CONCLUSION` (via `RDWKARC` + `TSKAJXY`).

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `packing` <-> `Packing`;
    `saturated V` <-> `saturated V` (Kepler.Statement); `sum S f` <->
    `setSum` (PackingAuto2:124); `CARD` <-> `Nat.card`/`Set.ncard`.
  - `HAS_SIZE n` <-> `HasSizeP25 s n := s.Finite ∧ s.ncard = n`;
    `IMAGE f (:num) = s_leaf V ul` <-> `f '' Set.univ = s_leaf V ul`.
  - `EL i ul` <-> `elV ul i` (PackingAuto2:131, junk `0`); `SUC i` <-> `i + 1`.
  - `leaf`/`cc_ke`/`cc_cell`/`cc_uh`/`chi_msb` <-> PackingAuto18
    `leaf`/`ccKe`/`ccCell`/`ccUh`/`chiMsb`; `mcell*`, `mcell_set`, `edgeX`,
    `wedge_ge`, `gammaX`, `lmfun`, `critical_weight`, `critical_edgeX`,
    `critical_edge_y`, `beta_bump_v1`, `dihX`, `bump`, `wtcount*_y`, `radV`,
    `mxi`, `hl`, `barV`, `truncate_simplex`, `initial_sublist`, `setSum`,
    `NULLSET` <-> PackingAuto2 kit.
  - cc_v11 model: `CcV11`, `cc_*_v11`, `periodic` <-> PackingAuto3
    (`GRHIDFA_concl` is the interface consumed by `OXLZLEZ`).
  - `pack_nonlinear_non_ox3q1h`, `tsk_hyp` <-> PackingAuto21 (opaque);
    `TSKAJXY` <-> PackingAuto21:1114; `RDWKARC_concl`/`OXLZLEZ_concl` <->>
    PackingAuto2 `*_concl` (sorried conclusions).
  - real toolkit: `dih_x/dih_y/eta_y/gamma3f/delta_x/h0cut` <-> SphereKit +
    PackingAuto21 (`dihXf/dihY/eta_y/gamma3f/deltaX/h0cut`; the sphere.hl kit
    is single-sourced in `Kepler.Text.SphereKit`, atn2-merge plan §5.4 —
    the hub's duplicate defs are gone, and this file imports that module
    explicitly).  `vol4f`/`gamma4fgcy` remain as local `_p25` copies here
    (kept per plan §3; PA20's unsuffixed versions are not re-exported).
  - `_p25` opaque stand-ins (NEEDS upstream bodies):
    `ox3q1hP25` (Oxl_def.hl `ox3q1h`: the certified 4-cardinality gg-sum
      inequality of the cc_v11 real model — inside `cc_real_model_v11`'s
      `n = 4` conjunct; PackagingAuto3 has it only inline),
    `rad2XP25`/`rad2YP25` (sphere.hl `rad2_x`, `rad2_y = y_of_x rad2_x`;
      use sites only need `rad2_y ... = radV {...}^2`, TSKAJXY2.hl:455),
    `beta_bumpA_yP25` (Merge_ineq.hl `beta_bumpA_y`, the y-space bump),
    `c2089/c1946` need certified interval bounds (`Flyspeck_constants.calc`).
  - `MOD_INJ1_ALT` is `MOD_INJ1_ALT_p25` here (name taken by
    PackingAuto3:445 with an equivalent statement).
-/

import Kepler.Text.Polytope
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
import Kepler.Text.PackingAuto21
import Kepler.Text.SphereKit
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Opaque / copied upstream constants (`_p25`; see header) -/

/-- HOL `ox3q1h` (Oxl_def.hl): the certified inequality bank for the
4-cardinality quarter case of the cc_v11 model.  Its content appears as the
`(cc_card_v11 cc = 4 ∧ qu-pattern) → 0 ≤ ∑ cc_gg_v11` conjunct of
`cc_real_model_v11` (PackingAuto3.lean:162); the global constant is not
ported elsewhere.  NEEDS: exact Oxl_def.hl body. -/
def ox3q1hP25 : Prop := sorry

/-- HOL `rad2_x` (sphere.hl): squared circumradius from squared edge
lengths.  NEEDS: exact sphere.hl body. -/
noncomputable def rad2XP25 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := sorry

/-- HOL `rad2_y` (sphere.hl): `y_of_x rad2_x` — rad2_x at squared lengths.
NEEDS: sphere.hl body (only used through `radV {...}^2`, TSKAJXY2.hl:455). -/
noncomputable def rad2YP25 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  rad2XP25 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `beta_bumpA_y` (Merge_ineq.hl): the y-space bump correction of
GG_MCELL_GENERAL.  NEEDS: exact Merge_ineq.hl body. -/
noncomputable def beta_bumpA_yP25 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-- HOL `vol4f` (sphere.hl:568); PackingAuto20.lean:105 verbatim. -/
noncomputable def vol4fP25 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
      f (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
      f (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
      f (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
      f (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
      f (y6 / 2) * dihY y6 y1 y5 y3 y4 y2)

/-- HOL `gamma4fgcy` (sphere.hl:566); PackingAuto20.lean:122 verbatim. -/
noncomputable def gamma4fgcyP25 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  volY y1 y2 y3 y4 y5 y6 - vol4fP25 y1 y2 y3 y4 y5 y6 f

/-- HOL `HAS_SIZE n` (used ~40 times below). -/
def HasSizeP25 (s : Set V3) (n : ℕ) : Prop := s.Finite ∧ s.ncard = n

/-! ## Leaf-cell kit (`_p25` copies from PackingAuto18.lean; `chiMsb` and
`upsX` used to be verbatim twins here too and were deleted at the atn2 merge
(plan §5.4) — both now come from `Kepler.Text.SphereKit`.  The rest of the
section is PA18-lane-duplicated but not SphereKit material; `MCELL2_SUBSET_AFF_GE`
is *not* redeclared here (PA18's and PA21's statements differ, plan §6.1).) -/

/-- HOL `leaf` (leaf_cell.hl:17); PackingAuto18.lean:73 verbatim. -/
def leaf (V : Set V3) (ul : List V3) : Prop := barV V 2 ul ∧ hl ul < Real.sqrt 2

/-- HOL `cc_pe_exists` (leaf_cell.hl:1052-1084); PackingAuto18 verbatim. -/
theorem cc_pe_exists (V : Set V3) (ul : List V3) :
    ∃ p1 p2 : V3, Packing V → saturated V → leaf V ul →
      voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
        0 < chiMsb ul p1 := by
  sorry

/-- HOL `cc_pe1` (leaf_cell.hl:1082); PackingAuto18 verbatim. -/
noncomputable def ccPe1 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (cc_pe_exists V ul)

/-- HOL `cc_pe2` (leaf_cell.hl:1082); PackingAuto18 verbatim. -/
noncomputable def ccPe2 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (Classical.choose_spec (cc_pe_exists V ul))

/-- HOL `cc_uh_exists` (leaf_cell.hl:1120-1132); PackingAuto18 verbatim. -/
theorem cc_uh_exists (V : Set V3) (ul : List V3) :
    ∃ vl : List V3, Packing V → saturated V → leaf V ul →
      barV V 3 vl ∧ truncateSimplex 2 vl = ul ∧ omegaList V vl = ccPe1 V ul := by
  sorry

/-- HOL `cc_uh` (leaf_cell.hl:1133); PackingAuto18 verbatim. -/
noncomputable def ccUh (V : Set V3) (ul : List V3) : List V3 :=
  Classical.choose (cc_uh_exists V ul)

/-- HOL `cc_ke` (leaf_cell.hl:1136-1137); PackingAuto18 verbatim. -/
noncomputable def ccKe (V : Set V3) (ul : List V3) : ℕ :=
  if hl (ccUh V ul) < Real.sqrt 2 then 4 else 3

/-- HOL `cc_cell` (leaf_cell.hl:1142); PackingAuto18 verbatim. -/
def ccCell (V : Set V3) (ul : List V3) : Set V3 := mcell (ccKe V ul) V (ccUh V ul)

/-! ## DEFINITIONS -/

/-- HOL `s_leaf` (OXLZLEZ3.hl:24): set-valued rendering — the leaves on the
stem `[EL 0 ul, EL 1 ul]` whose cc-cell dispatch is 4 (either stem order). -/
def s_leaf (V : Set V3) (ul : List V3) : Set V3 :=
  {u | leaf V [elV ul 0, elV ul 1, u] ∧
    (ccKe V [elV ul 0, elV ul 1, u] = 4 ∨ ccKe V [elV ul 1, elV ul 0, u] = 4)}

/-- HOL `gg_mcell` (OXLZLEZ3.hl:27): gamma-weight sum over the Marchal cells
in the wedge `wedge_ge u0 u1 (f i) (f (SUC i))`. -/
noncomputable def gg_mcell (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) : ℝ :=
  setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
    X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fun X =>
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X

/-- HOL `azim_mcell` (OXLZLEZ3.hl:32): dihedral-angle sum over the same
wedge cell set. -/
noncomputable def azim_mcell (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) (i : ℕ) : ℝ :=
  setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
    X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fun X => dihX V X (u0, u1)

/-- HOL `cc_data_v8` (OXLZLEZ3.hl:36): the cc_v11 compression of the edge
data `(azim, gg, gg3a, gg3b)`, six boolean classifiers, and the leaf count. -/
noncomputable def cc_data_v8 (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) : CcV11 where
  ccReals :=
    [azim_mcell V f u0 u1,
     gg_mcell V f u0 u1,
     fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
       criticalWeight V (ccCell V [u0, u1, f i]),
     fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
       criticalWeight V (ccCell V [u1, u0, f (i + 1)])]
  ccBools :=
    [fun i => dist (f i) (f (i + 1)) < 2 * hminus,
     fun i => 2 * hminus ≤ dist (f i) (f (i + 1)) ∧
       dist (f i) (f (i + 1)) ≤ 2 * hplus,
     fun i => 2 * hplus < dist (f i) (f (i + 1)),
     fun i => dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus,
     fun i => hl [u0, u1, f i] < 1.34,
     fun i => ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
       mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))]
  ccCard := (s_leaf V [u0, u1]).ncard

/-- HOL `leaf_rank` (OXLZLEZ3.hl:53): `f` enumerates `s_leaf V ul`
cyclically with period `n`, strictly `azim`-increasing on `0..n-1`. -/
def leaf_rank (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) : Prop :=
  f '' (univ : Set ℕ) = s_leaf V ul ∧
    (∀ i, f (i + n) = f i) ∧
    ∀ i j, i < n → j < n → i < j →
      azim (elV ul 0) (elV ul 1) w0 (f i) < azim (elV ul 0) (elV ul 1) w0 (f j)

/-- HOL `cc_4` (OXLZLEZ3.hl:62): the wedge of `f i, f (SUC i)` over stem
`{u0,u1}` carries a 4-cell (a `barV V 3` list with `mcell4` in the wedge). -/
def cc_4 (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (i : ℕ) : Prop :=
  ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
    mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))

/-! ## GENERIC RESULTS -/

/-- HOL `CARD_INSERT_INTER`. -/
theorem CARD_INSERT_INTER {α : Type*} (a : α) (A B : Set α) (hB : B.Finite) :
    Set.ncard ((insert a A) ∩ B) =
      if a ∈ B ∧ a ∉ A then Set.ncard (A ∩ B) + 1 else Set.ncard (A ∩ B) := by
  by_cases h1 : a ∈ B ∧ a ∉ A
  · have hset : (insert a A) ∩ B = insert a (A ∩ B) := by
      refine Set.ext fun x => ?_
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨(rfl | hx), hxB⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxB⟩
      · rintro (rfl | ⟨hxA, hxB⟩)
        · exact ⟨Or.inl rfl, h1.1⟩
        · exact ⟨Or.inr hxA, hxB⟩
    rw [hset, Set.ncard_insert_of_notMem (fun hm => absurd hm.1 h1.2)
      (hB.subset Set.inter_subset_right), if_pos h1]
  · have hset : (insert a A) ∩ B = A ∩ B := by
      refine Set.ext fun x => ?_
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨(rfl | hx), hxB⟩
        · exact ⟨Classical.byContradiction fun hc => h1 ⟨hxB, hc⟩, hxB⟩
        · exact ⟨hx, hxB⟩
      · rintro ⟨hx, hxB⟩
        exact ⟨Or.inr hx, hxB⟩
    rw [hset, if_neg h1]

/-- HOL `CARD_INSERT_INTER_ALT`. -/
theorem CARD_INSERT_INTER_ALT {α : Type*} (a : α) (A B : Set α) (hB : B.Finite) :
    Set.ncard ((insert a A) ∩ B) =
      (if a ∈ B ∧ a ∉ A then 1 else 0) + Set.ncard (A ∩ B) := by
  rw [CARD_INSERT_INTER a A B hB]
  split_ifs with h
  · omega
  · push Not at h
    omega

/-- HOL `NUMSEG_LT`: `0..(r-1) = {i | i < r}` for `r ≠ 0`. -/
theorem NUMSEG_LT (r : ℕ) (hr : r ≠ 0) :
    (Finset.Icc 0 (r - 1) : Set ℕ) = {i | i < r} := by
  ext i
  simp only [Set.mem_setOf_eq, Finset.coe_Icc]
  constructor
  · rintro ⟨-, hi⟩
    omega
  · intro hi
    exact ⟨Nat.zero_le _, by omega⟩

/-- HOL `CARD4_IN_PAIRS`: a 4-element set written over a common pair fixes
the complementary pair. -/
theorem CARD4_IN_PAIRS {α : Type*} (a b c d e f : α)
    (h4 : Nat.card ({a, b, c, d} : Set α) = 4) (heq : ({a, b, c, d} : Set α) = {a, b, e, f}) :
    ({c, d} : Set α) = {e, f} := by
  have h4n : ({a, b, c, d} : Set α).ncard = 4 := h4
  have h3 : ∀ (x y z : α), ({x, y, z} : Set α).ncard ≤ 3 := by
    intro x y z
    have hyz : ∀ (y z : α), ({y, z} : Set α).ncard ≤ 2 := by
      intro y z
      rcases eq_or_ne y z with hh | hh
      · rw [show ({y, z} : Set α) = ({y} : Set α) from by simp [hh], Set.ncard_singleton]
        omega
      · rw [Set.ncard_pair hh]
    calc ({x, y, z} : Set α).ncard = (insert x ({y, z} : Set α)).ncard := by simp
      _ ≤ ({y, z} : Set α).ncard + 1 := Set.ncard_insert_le x _
      _ ≤ 3 := by have h2 := hyz y z; omega
  have hq4 : ∀ q : α, q ∈ ({a, b, c, d} : Set α) ↔ (q = a ∨ q = b ∨ q = c ∨ q = d) := by
    intro q; simp
  have hq3 : ∀ q : α, q ∈ ({a, b, e, f} : Set α) ↔ (q = a ∨ q = b ∨ q = e ∨ q = f) := by
    intro q; simp
  -- `c` and `d` are not in `{a, b}`
  have hc : ¬ (c = a ∨ c = b) := by
    intro hm
    have hd2 : ({a, b, c, d} : Set α) = ({a, b, d} : Set α) := by
      ext q
      rw [hq4]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
        · exact Or.inr (Or.inr hq)
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inr hq))
    rw [hd2] at h4n
    have := h3 a b d
    omega
  have hd : ¬ (d = a ∨ d = b) := by
    intro hm
    have hd2 : ({a, b, c, d} : Set α) = ({a, b, c} : Set α) := by
      ext q
      rw [hq4]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
    rw [hd2] at h4n
    have := h3 a b c
    omega
  -- `e` and `f` are not in `{a, b}`
  have he : ¬ (e = a ∨ e = b) := by
    intro hm
    have hd2 : ({a, b, e, f} : Set α) = ({a, b, f} : Set α) := by
      ext q
      rw [hq3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
        · exact Or.inr (Or.inr hq)
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inr hq))
    rw [heq, hd2] at h4n
    have := h3 a b f
    omega
  have hf : ¬ (f = a ∨ f = b) := by
    intro hm
    have hd2 : ({a, b, e, f} : Set α) = ({a, b, e} : Set α) := by
      ext q
      rw [hq3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hq
        rcases hq with hq | hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr hq)
        · rcases hm with hm | hm
          · exact Or.inl (hq.trans hm)
          · exact Or.inr (Or.inl (hq.trans hm))
      · intro hq
        rcases hq with hq | hq | hq
        · exact Or.inl hq
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr (Or.inl hq))
    rw [heq, hd2] at h4n
    have := h3 a b e
    omega
  have hce : c = e ∨ c = f := by
    have hm : c ∈ ({a, b, e, f} : Set α) := by rw [← heq]; simp
    rw [hq3] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hc
    · exact absurd (Or.inr h) hc
    · exact Or.inl h
    · exact Or.inr h
  have hdf : d = e ∨ d = f := by
    have hm : d ∈ ({a, b, e, f} : Set α) := by rw [← heq]; simp
    rw [hq3] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hd
    · exact absurd (Or.inr h) hd
    · exact Or.inl h
    · exact Or.inr h
  have hec : e = c ∨ e = d := by
    have hm : e ∈ ({a, b, c, d} : Set α) := by rw [heq]; simp
    rw [hq4] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) he
    · exact absurd (Or.inr h) he
    · exact Or.inl h
    · exact Or.inr h
  have hfd : f = c ∨ f = d := by
    have hm : f ∈ ({a, b, c, d} : Set α) := by rw [heq]; simp
    rw [hq4] at hm
    rcases hm with h | h | h | h
    · exact absurd (Or.inl h) hf
    · exact absurd (Or.inr h) hf
    · exact Or.inl h
    · exact Or.inr h
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hq
    rcases hq with hq | hq
    · rcases hce with hce | hce
      · exact Or.inl (hq.trans hce)
      · exact Or.inr (hq.trans hce)
    · rcases hdf with hdf | hdf
      · exact Or.inl (hq.trans hdf)
      · exact Or.inr (hq.trans hdf)
  · intro hq
    rcases hq with hq | hq
    · rcases hec with hec | hec
      · exact Or.inl (hq.trans hec)
      · exact Or.inr (hq.trans hec)
    · rcases hfd with hfd | hfd
      · exact Or.inl (hq.trans hfd)
      · exact Or.inr (hq.trans hfd)

/-- HOL `initial_sublist_cons` (generic in the source; instantiated at `V3`
to reuse PackingAuto2's `initialSublist`). -/
theorem initial_sublist_cons (a b : V3) (x y : List V3) :
    initialSublist (a :: x) (b :: y) ↔ a = b ∧ initialSublist x y := by
  constructor
  · rintro ⟨zl, hzl⟩
    injection hzl with h1 h2
    exact ⟨h1.symm, zl, h2⟩
  · rintro ⟨hab, zl, hzl⟩
    subst hab
    exact ⟨zl, by rw [hzl]; simp [List.cons_append]⟩
/-- HOL `COPLANAR_CONVEX_HULL_COPLANAR`. -/
theorem COPLANAR_CONVEX_HULL_COPLANAR (s : Set V3) :
    Coplanar (convexHull ℝ s) ↔ Coplanar s := by
  constructor
  · rintro ⟨u, v, w, hsub⟩
    exact ⟨u, v, w, Set.Subset.trans (subset_convexHull ℝ s) hsub⟩
  · intro h
    obtain ⟨u, v, w, hsub⟩ := h
    refine ⟨u, v, w, ?_⟩
    intro x hx
    have h1' : x ∈ (affineSpan ℝ s : Set V3) := convexHull_subset_affineSpan (s := s) hx
    have h2' : (affineSpan ℝ s : AffineSubspace ℝ V3) ≤
        affineSpan ℝ ({u, v, w} : Set V3) := affineSpan_le.mpr hsub
    exact SetLike.mem_coe.mpr (h2' h1')

/-- HOL `BARV3_SET_OF_LIST4`. -/
theorem BARV3_SET_OF_LIST4 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hb : barV V 3 ul) :
    setOfList ul = {elV ul 0, elV ul 1, elV ul 2, elV ul 3} := by
  rcases ul with _ | ⟨u0, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u1, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u2, t⟩
  · exact absurd hb.1 (by simp)
  rcases t with _ | ⟨u3, t⟩
  · exact absurd hb.1 (by simp)
  · have h4 : (u0 :: u1 :: u2 :: u3 :: t).length = 4 := hb.1
    cases t with
    | nil => ext x; simp [setOfList, elV]
    | cons e t' =>
      simp only [List.length_cons] at h4
      omega

/-- HOL `STRICT_SORT_FINITE` (OXLZLEZ3.hl:163): a finite set with an
asymmetric transitive `<<` can be enumerated by `1..n` in `<<`-increasing
order.  FAITHFUL-RESTATEMENT note: the HOL statement quantifies over all
types because HOL Light types are all inhabited; over an empty `α` the Lean
statement is FALSE (take `s = ∅`, `n = 0`: no function `ℕ → α` exists at
all), so the `Nonempty α` class side condition is added.  Proof: rank each
element by the cardinality of its strict down-set inside `s` (strictly
monotone along `lt`-comparable pairs by transitivity), then enumerate `s`
insertion-sorted by that rank (`List.Perm`/`List.Pairwise` bookkeeping). -/
theorem STRICT_SORT_FINITE {α : Type*} [Nonempty α] {lt : α → α → Prop} (s : Set α) (n : ℕ)
    (hirr : ∀ x y, x ∈ s → y ∈ s → lt x y → lt y x → x = y)
    (htr : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → lt x y → lt y z → lt x z)
    (hs : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → α, s = f '' Set.Icc 1 n ∧
      ∀ j k, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k → ¬lt (f k) (f j) := by
  classical
  -- every down-set is finite (subset of `s`)
  have Dfin : ∀ x : α, ({z : α | z ∈ s ∧ lt z x ∧ z ≠ x} : Set α).Finite :=
    fun x => hs.1.subset fun z hz => hz.1
  -- rank function: cardinality of the strict down-set
  obtain ⟨mu, hmu⟩ :
      ∃ mu : α → ℕ, ∀ x, mu x = Set.ncard {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} :=
    ⟨_, fun _ => rfl⟩
  -- the rank strictly increases along `lt`-comparable distinct pairs
  have key : ∀ x y : α, x ∈ s → y ∈ s → lt x y → x ≠ y → mu x < mu y := by
    intro x y hx hy hxy hne
    have hbelow : {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} ⊆
        {z : α | z ∈ s ∧ lt z y ∧ z ≠ y} := by
      intro z hz
      refine ⟨hz.1, htr z x y hz.1 hx hy hz.2.1 hxy, ?_⟩
      intro hzy
      have hyx : lt y x := hzy ▸ hz.2.1
      exact absurd (hzy.trans (hirr x y hx hy hxy hyx).symm) hz.2.2
    have hxnot : x ∉ ({z : α | z ∈ s ∧ lt z x ∧ z ≠ x} : Set α) := fun h => h.2.2 rfl
    have hback : ¬ ({z : α | z ∈ s ∧ lt z y ∧ z ≠ y} : Set α) ⊆
        {z : α | z ∈ s ∧ lt z x ∧ z ≠ x} := by
      intro hcon
      exact hxnot (hcon (⟨hx, hxy, hne⟩ :
        x ∈ ({z : α | z ∈ s ∧ lt z y ∧ z ≠ y} : Set α)))
    rw [hmu x, hmu y]
    exact Set.ncard_lt_ncard ⟨hbelow, hback⟩ (Dfin y)
  -- enumerate `s` as a duplicate-free list
  set l0 : List α := hs.1.toFinset.toList with hl0def
  have hl0mem : ∀ a, a ∈ l0 ↔ a ∈ s := by
    intro a
    rw [hl0def, Finset.mem_toList, Set.Finite.mem_toFinset]
  have hl0nd : l0.Nodup := by
    rw [hl0def]; exact hs.1.toFinset.nodup_toList
  have hl0len : l0.length = n := by
    rw [hl0def, Finset.length_toList, ← Set.ncard_eq_toFinset_card s hs.1]
    exact hs.2
  -- insertion-sort it by the rank
  haveI : Std.Total (fun a b => mu a ≤ mu b) := ⟨fun a b => Nat.le_total (mu a) (mu b)⟩
  haveI : IsTrans α (fun a b => mu a ≤ mu b) := ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  set l : List α := l0.insertionSort (fun a b => mu a ≤ mu b) with hldef
  have hlen : l.length = n := by
    rw [hldef]
    have hperml := (List.perm_insertionSort (fun a b => mu a ≤ mu b) l0).length_eq
    rw [hperml]; exact hl0len
  have hmem : ∀ a, a ∈ l ↔ a ∈ s := by
    intro a
    rw [hldef, List.mem_insertionSort, hl0mem a]
  have hlnd : l.Nodup := by
    rw [hldef]
    exact (List.perm_insertionSort (fun a b => mu a ≤ mu b) l0).nodup_iff.mpr hl0nd
  have hpair : l.Pairwise (fun a b => mu a ≤ mu b) := by
    rw [hldef]; exact List.pairwise_insertionSort _ l0
  refine ⟨fun i => l.getD (i - 1) (Classical.choice inferInstance), ?_, ?_⟩
  · refine Set.ext fun x => ?_
    constructor
    · intro hx
      obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp (hmem x |>.mpr hx)
      exact ⟨i + 1, ⟨by omega, by omega⟩, by
        show l.getD (i + 1 - 1) (Classical.choice inferInstance) = x
        rw [show i + 1 - 1 = i from by omega,
          List.getD_eq_getElem l (Classical.choice inferInstance) hi]
        exact hli⟩
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      show l.getD (i - 1) (Classical.choice inferInstance) ∈ s
      have hilt : i - 1 < l.length := by rw [hlen]; omega
      rw [List.getD_eq_getElem l (Classical.choice inferInstance) hilt]
      exact (hmem _).mp (List.getElem_mem _)
  · intro j k kj kk hlt
    obtain ⟨hj1, hjn⟩ := kj
    obtain ⟨hk1, hkn⟩ := kk
    have hjlt : j - 1 < l.length := by rw [hlen]; omega
    have hklt : k - 1 < l.length := by rw [hlen]; omega
    intro hlt
    have hjk : j - 1 ≠ k - 1 := by omega
    have hne' : l[k - 1] ≠ l[j - 1] := by
      intro hcon
      exact hjk (congrArg Fin.val
        (List.nodup_iff_injective_getElem.mp hlnd
          (show l[(⟨k - 1, hklt⟩ : Fin l.length).val] =
              l[(⟨j - 1, hjlt⟩ : Fin l.length).val] from hcon))).symm
    beta_reduce at hlt
    rw [List.getD_eq_getElem l (Classical.choice inferInstance) hklt,
        List.getD_eq_getElem l (Classical.choice inferInstance) hjlt] at hlt
    have hge : mu l[j - 1] ≤ mu l[k - 1] :=
      List.pairwise_iff_getElem.mp hpair (j - 1) (k - 1) hjlt hklt (by omega)
    have hmut : mu l[k - 1] < mu l[j - 1] :=
      key _ _ (hmem _ |>.mp (List.getElem_mem _)) (hmem _ |>.mp (List.getElem_mem _))
        hlt hne'
    omega

/-- HOL `MOD_INJ1_ALT` (name sufficed; PackingAuto3.lean:445 has an
equivalent theorem under this name). -/
theorem MOD_INJ1_ALT_p25 {k n : ℕ} (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0)
    (x : ℕ) : x % n ≠ (x + k) % n := by
  intro h
  have hdvd : n ∣ x + k - x := (Nat.modEq_iff_dvd' (Nat.le_add_right x k)).mp h
  rw [Nat.add_sub_cancel_left] at hdvd
  have hle : n ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

/-- HOL `MOD_PERIOD_BOUNDED_ALT`. -/
theorem MOD_PERIOD_BOUNDED_ALT {k n : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (x : ℕ) (h : (x + k) % n = x % n) : n ≤ k := by
  by_contra hc
  have hlt : k < n := by omega
  exact MOD_INJ1_ALT_p25 hn hlt hk x h.symm

/-- HOL `MOD_REFL_ALT` (`MOD_MULT` at `m, 1` after `MULT_CLAUSES`). -/
theorem MOD_REFL_ALT (m : ℕ) : m % 1 = 0 := Nat.mod_one m

/-- HOL `periodic_o`. -/
theorem periodic_o {α β : Type*} (g : α → β) {f : ℕ → α} {n : ℕ}
    (h : periodic f n) : periodic (g ∘ f) n := fun i => congrArg g (h i)

/-- HOL `periodic_shift`. -/
theorem periodic_shift {α : Type*} (k : ℕ) {f : ℕ → α} {n : ℕ}
    (h : periodic f n) : periodic (fun i => f (i + k)) n := by
  intro i
  show f (i + n + k) = f (i + k)
  have h2 : i + n + k = i + k + n := by omega
  rw [h2]
  exact h (i + k)

/-- Helper: periodicity iterated `k` times. -/
private theorem p25_periodic_mul {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n)
    (k i : ℕ) : f (i + n * k) = f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, h, ih]

/-- Helper: `f i` depends on `i` only mod `n`. -/
private theorem p25_f_mod {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n)
    (i : ℕ) : f (i % n) = f i := by
  have h1 := Nat.mod_add_div i n
  calc f (i % n) = f (i % n + n * (i / n)) := (p25_periodic_mul h (i / n) (i % n)).symm
    _ = f i := by rw [h1]

/-- HOL `PERIODIC_IMAGE`. -/
theorem PERIODIC_IMAGE {α : Type*} {f : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (h : periodic f n) : f '' {i | i < n} = f '' (univ : Set ℕ) := by
  refine Set.ext fun y => ?_
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, Set.mem_univ _, rfl⟩
  · rintro ⟨i, _, rfl⟩
    refine ⟨i % n, ?_, p25_f_mod h i⟩
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact Nat.mod_lt _ this

/-- HOL `PERIODIC_REDUCE_MOD`. -/
theorem PERIODIC_REDUCE_MOD {α : Type*} {f : ℕ → α} {n : ℕ} (hn : 1 ≤ n)
    (h : periodic f n) (i : ℕ) :
    ∃ j, j < n ∧ f i = f j ∧ f (i + 1) = f (j + 1) := by
  have h0 : i % n < n := Nat.mod_lt i (by have := hn; omega)
  refine ⟨i % n, h0, ?_, ?_⟩
  · rw [p25_f_mod h i]
  · have h1 := Nat.mod_add_div i n
    have e : i + 1 = i % n + 1 + n * (i / n) := by omega
    rw [e, p25_periodic_mul h]

/-- HOL `PERIODIC_EQ_IMAGE` (renamed from PERIODIC_INJ). -/
theorem PERIODIC_EQ_IMAGE {α : Type*} {f : ℕ → α} {n : ℕ} (_hn : n ≠ 0)
    (h : periodic f n) {i j : ℕ} (hm : i % n = j % n) : f i = f j := by
  calc f i = f (i % n) := (p25_f_mod h i).symm
    _ = f (j % n) := by rw [hm]
    _ = f j := p25_f_mod h j

/-- HOL `F_SUC_PRE`. -/
theorem F_SUC_PRE {α : Type*} {f : ℕ → α} {n : ℕ} (hn : n ≠ 0) (h : periodic f n)
    (i : ℕ) : f (i + n - 1 + 1) = f i := by
  have e : i + n - 1 + 1 = i + n := by omega
  rw [e, h]

/-- HOL `F_DEMOD`. -/
theorem F_DEMOD {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : 1 < n)
    (i : ℕ) : f (i % n) = f i ∧ f (i % n + 1) = f (i + 1) := by
  refine ⟨p25_f_mod h i, ?_⟩
  have h1 := Nat.mod_add_div i n
  have e : i + 1 = i % n + 1 + n * (i / n) := by omega
  rw [e, p25_periodic_mul h]

/-- HOL `FM_DEMOD`. -/
theorem FM_DEMOD {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : 1 < n)
    (i : ℕ) : f (i % n) = f i ∧ f (i % n + n - 1) = f (i + n - 1) := by
  refine ⟨p25_f_mod h i, ?_⟩
  have h1 := Nat.mod_add_div i n
  have e : i + n - 1 = i % n + n - 1 + n * (i / n) := by omega
  rw [e, p25_periodic_mul h]

private theorem p25_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

private theorem p25_affineSpan_three_ne_top (x v u : V3) :
    (affineSpan ℝ ({x, v, u} : Set V3)) ≠ ⊤ := by
  intro h
  have hdir : (affineSpan ℝ ({x, v, u} : Set V3)).direction = ⊤ := by
    rw [h]; exact AffineSubspace.direction_top ℝ V3 V3
  have hvs : vectorSpan ℝ ({x, v, u} : Set V3)
      = Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show x ∈ ({x, v, u} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨u, by simp, rfl⟩
  have hle : Module.finrank ℝ (affineSpan ℝ ({x, v, u} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact p25_finrank_span_pair_le_two (v - x) (u - x)
  rw [hdir, finrank_top] at hle
  exact absurd hle (by norm_num)

private theorem p25_finset_sum_smul_mem_affineSpan {T : Set V3} {s : Finset V3}
    {f : V3 → ℝ}
    (hS : ∀ w ∈ s, w ∈ (affineSpan ℝ T : Set V3))
    (hsum : ∑ w ∈ s, f w = 1) :
    ∑ w ∈ s, f w • w ∈ (affineSpan ℝ T : Set V3) := by
  have hne : s.Nonempty :=
    Finset.nonempty_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  obtain ⟨b, hb⟩ := hne
  have hbS : b ∈ (affineSpan ℝ T : Set V3) := hS b hb
  have hdir : ∑ w ∈ s, f w • (w - b) ∈ (affineSpan ℝ T).direction := by
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ (f w)
      (AffineSubspace.vsub_mem_direction (hS w hw) hbS)
  have hsub : ∑ w ∈ s, f w • (w - b) = (∑ w ∈ s, f w • w) - b := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hy : ∑ w ∈ s, f w • w = (∑ w ∈ s, f w • (w - b)) +ᵥ b := by
    rw [vadd_eq_add, hsub]
    abel
  rw [hy]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hbS

private theorem p25_affGe_subset_affineSpan (s t : Set V3) :
    affGe s t ⊆ (affineSpan ℝ (s ∪ t : Set V3) : Set V3) := by
  intro v hv
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hv
  obtain ⟨f, hfin, hcomb, _, hone⟩ := hv
  have hmem : ∀ w ∈ hfin.toFinset, w ∈ (affineSpan ℝ (s ∪ t : Set V3) : Set V3) := by
    intro w hw
    have hw' : w ∈ s ∪ t := by
      rw [← hfin.coe_toFinset]
      exact hw
    exact subset_affineSpan ℝ _ hw'
  rw [hcomb]
  exact p25_finset_sum_smul_mem_affineSpan hmem hone

/-- HOL `NULLSET_AFF_2_1`. -/
theorem NULLSET_AFF_2_1 (x y z : V3) : nullSet (affGe {x, y} {z}) := by
  have hsub := p25_affGe_subset_affineSpan ({x, y} : Set V3) ({z} : Set V3)
  have h3 : (affineSpan ℝ ({x, y} ∪ {z} : Set V3)) ≠ ⊤ := by
    rw [show ({x, y} ∪ {z} : Set V3) = ({x, y, z} : Set V3) from by
      ext q; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact p25_affineSpan_three_ne_top x y z
  refine measure_mono_null hsub ?_
  exact MeasureTheory.Measure.addHaar_affineSubspace volume
    (affineSpan ℝ ({x, y} ∪ {z} : Set V3)) h3

/-- HOL `coplanar_delta_y` (renamed from coplanar_dih_y). -/
theorem coplanar_delta_y (u0 u1 u2 u3 : V3) :
    ¬ Coplanar ({u0, u1, u2, u3} : Set V3) ↔
      0 < deltaY (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2) := by
  sorry

/-- HOL `RADV_ETAY`. -/
theorem RADV_ETAY (u0 u1 u2 : V3) (hnc : ¬ Collinear3 u0 u1 u2) :
    radV {u0, u1, u2} = eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) := by
  sorry

/-- HOL `RADV2`. -/
theorem RADV2 (u v : V3) : radV {u, v} = (1 / 2 : ℝ) * dist u v := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have h := HL_2 u v
  unfold hl at h
  rw [hset] at h
  rw [h]
  ring

/-- HOL `GDRQXLGv3`. -/
theorem GDRQXLGv3 (v0 v1 v2 v3 : V3) (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    radV {v0, v1, v2, v3} ^ 2 =
      rad2XP25 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
  sorry

/-- HOL `DIST_IMP_COLLINEAR`. -/
theorem DIST_IMP_COLLINEAR (u0 u1 u2 : V3)
    (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
    (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4) :
    ¬ Collinear3 u0 u1 u2 := by
  intro hcol
  rcases eq_or_ne u1 u0 with heq | hne
  · rw [heq, dist_self] at h1
    linarith
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := u0) (w := u1) (w1 := u2) hne).mp hcol
  have hω1 : dist u0 u1 = ‖u1 - u0‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have hω2 : dist u0 u2 = |c| * ‖u1 - u0‖ := by
    rw [dist_eq_norm, norm_sub_rev, hc, norm_smul, Real.norm_eq_abs]
  have hsub : (u1 - u2 : V3) = (1 - c) • (u1 - u0) := by
    rw [sub_smul, one_smul, ← hc]
    abel
  have hω3 : dist u1 u2 = |1 - c| * ‖u1 - u0‖ := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  rcases lt_or_ge c 1 with hc1 | hc1
  · rcases lt_or_ge 0 c with hc0 | hc0
    · have e : dist u0 u1 = dist u0 u2 + dist u1 u2 := by
        rw [hω2, hω3, hω1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c)]
        ring
      linarith
    · have e : dist u1 u2 = dist u0 u1 + dist u0 u2 := by
        rw [hω2, hω3, hω1, abs_of_nonpos (by linarith : (c : ℝ) ≤ 0),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c)]
        ring
      linarith
  · have e : dist u0 u2 = dist u0 u1 + dist u1 u2 := by
      rw [hω2, hω3, hω1, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c),
        abs_of_nonpos (by linarith : (1 - c : ℝ) ≤ 0)]
      ring
    linarith

/-- HOL `UPS_X8_POS` (needs certified interval bounds). -/
theorem UPS_X8_POS {y5 y6 : ℝ} (h5 : 2 ≤ y5) (h5' : y5 < 4) (h6 : 2 ≤ y6)
    (h6' : y6 < 4) : 0 < upsX 8 (y5 * y5) (y6 * y6) := by
  have ha : 4 ≤ y5 * y5 := by nlinarith
  have hb : y5 * y5 < 16 := by nlinarith
  have hc : 4 ≤ y6 * y6 := by nlinarith
  have hd : y6 * y6 < 16 := by nlinarith
  have key : upsX 8 (y5 * y5) (y6 * y6) =
      64 + 16 * (y5 * y5 - 4) + 16 * (y6 * y6 - 4) +
        2 * (y5 * y5 - 4) * (y6 * y6 - 4) -
        (y5 * y5 - 4) ^ 2 - (y6 * y6 - 4) ^ 2 := by
    unfold upsX
    ring
  have p1 : 0 ≤ (y5 * y5 - 4) * (y6 * y6 - 4) :=
    mul_nonneg (by linarith) (by linarith)
  have p2 : (y5 * y5 - 4) ^ 2 ≤ 12 * (y5 * y5 - 4) :=
    by have t2 : 0 ≤ (y5 * y5 - 4) * (12 - (y5 * y5 - 4)) :=
         mul_nonneg (by linarith) (by linarith)
       linarith
  have p3 : (y6 * y6 - 4) ^ 2 ≤ 12 * (y6 * y6 - 4) :=
    by have t2 : 0 ≤ (y6 * y6 - 4) * (12 - (y6 * y6 - 4)) :=
         mul_nonneg (by linarith) (by linarith)
       linarith
  rw [key]
  nlinarith

/-- HOL `DIST_IMP_UPS_X_POS`. -/
theorem DIST_IMP_UPS_X_POS (u0 u1 u2 : V3)
    (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
    (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4) :
    0 < upsX (dist u0 u1 ^ 2) (dist u0 u2 ^ 2) (dist u1 u2 ^ 2) := by
  have hnc := DIST_IMP_COLLINEAR u0 u1 u2 h1 h2 h3 h4 h5 h6
  have hd01 : dist u0 u1 ≠ 0 := by
    intro hzz
    rw [hzz] at h1
    linarith
  have hd02 : dist u0 u2 ≠ 0 := by
    intro hzz
    rw [hzz] at h2
    linarith
  have hne : u1 ≠ u0 := by
    intro hzz
    exact hd01 (by rw [hzz]; simp)
  have hne2 : u2 ≠ u0 := by
    intro hzz
    exact hd02 (by rw [hzz]; simp)
  have hv1n : (u1 - u0 : V3) ≠ 0 := by
    intro hzz
    exact hne (sub_eq_zero.mp hzz)
  have hv2n : (u2 - u0 : V3) ≠ 0 := by
    intro hzz
    exact hne2 (sub_eq_zero.mp hzz)
  have hx1n : (‖u1 - u0‖ ^ 2 : ℝ) ≠ 0 :=
    ne_of_gt (sq_pos_iff.mpr (norm_pos_iff.mpr hv1n).ne')
  have hcol0 : ¬ Collinear3 (0 : V3) (u1 - u0) (u2 - u0) := by
    intro h0
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0 : V3)) (w := u1 - u0)
      (w1 := u2 - u0) hv1n).mp h0
    exact hnc ((collinear3_iff_smul (v := u0) (w := u1) (w1 := u2) hne).mpr
      ⟨c, by simpa using hc⟩)
  -- the Gram identity for `ups_x`
  have hup : upsX (‖u1 - u0‖ ^ 2) (‖u2 - u0‖ ^ 2)
        (‖(u1 - u0) - (u2 - u0)‖ ^ 2) =
      4 * (‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
        (inner ℝ (u1 - u0) (u2 - u0)) ^ 2) := by
    have hdsq : ‖(u1 - u0) - (u2 - u0)‖ ^ 2
        = ‖u1 - u0‖ ^ 2 + ‖u2 - u0‖ ^ 2 -
          2 * inner ℝ (u1 - u0) (u2 - u0) := by
      rw [norm_sub_sq_real]
      ring
    unfold upsX
    rw [hdsq]
    ring
  have e1 : dist u0 u1 ^ 2 = ‖u1 - u0‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
  have e2 : dist u0 u2 ^ 2 = ‖u2 - u0‖ ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
  have hsub : ((u1 - u0) - (u2 - u0) : V3) = u1 - u2 := by abel
  have e3 : dist u1 u2 ^ 2 = ‖(u1 - u0) - (u2 - u0)‖ ^ 2 := by
    rw [dist_eq_norm, ← hsub]
  rw [e1, e2, e3, hup]
  -- strict Cauchy–Schwarz from non-collinearity
  have hcs : (inner ℝ (u1 - u0) (u2 - u0)) ^ 2 < ‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hnorm0 : ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 =
        ‖u1 - u0‖ ^ 2 * (‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
          (inner ℝ (u1 - u0) (u2 - u0)) ^ 2) := by
      rw [norm_sub_sq_real]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow]
      rw [sq_abs (a := inner ℝ (u1 - u0) (u2 - u0)),
        sq_abs (a := (‖u1 - u0‖ ^ 2 : ℝ))]
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    have hsq0 : ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 = 0 := by
      have hge : 0 ≤ ‖(inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
          ‖u1 - u0‖ ^ 2 • (u2 - u0)‖ ^ 2 := sq_nonneg _
      rw [hnorm0]
      have h1n : 0 ≤ ‖u1 - u0‖ ^ 2 := sq_nonneg _
      have h2n : ‖u1 - u0‖ ^ 2 * ‖u2 - u0‖ ^ 2 -
          (inner ℝ (u1 - u0) (u2 - u0)) ^ 2 ≤ 0 := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2n h1n
      rw [mul_zero] at h3
      exact le_antisymm h3 (by rw [← hnorm0]; exact hge)
    have hwz : (inner ℝ (u1 - u0) (u2 - u0)) • (u1 - u0) -
        ‖u1 - u0‖ ^ 2 • (u2 - u0) = 0 := by
      rw [← norm_eq_zero]
      exact sq_eq_zero_iff.mp hsq0
    have hcancel : ‖u1 - u0‖ ^ 2 • (u2 - u0) =
        ‖u1 - u0‖ ^ 2 •
          ((inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2) • (u1 - u0)) := by
      rw [smul_smul]
      have hscale : (‖u1 - u0‖ ^ 2 : ℝ) *
          (inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2)
          = inner ℝ (u1 - u0) (u2 - u0) := by field_simp
      rw [hscale, sub_eq_zero.mp hwz]
    have hv2eq : (u2 - u0 : V3) =
        (inner ℝ (u1 - u0) (u2 - u0) / ‖u1 - u0‖ ^ 2) • (u1 - u0) :=
      smul_right_injective _ hx1n hcancel
    exact hcol0 ((collinear3_iff_smul (v := (0 : V3)) (w := u1 - u0)
      (w1 := u2 - u0) hv1n).mpr ⟨_, by simpa using hv2eq⟩)
  linarith [hcs]

/-- HOL `dih_x < pi`: the angle computed by `atn2` from a positive first
argument stays below `pi/2` in every quadrant branch. -/
theorem DIH_X_LT_PI {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 < Real.pi := by
  unfold dihXf
  have hx : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith) hd)
  have harg : atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) < Real.pi / 2 := by
    unfold atn2
    split_ifs with hb hb2 hb3
    · have hfrac : -(deltaX4 x1 x2 x3 x4 x5 x6) /
          Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) < 1 := by
        rw [div_lt_one hx]
        have habs := abs_lt.mp hb
        linarith
      exact Real.arctan_lt_pi_div_two _
    · have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
            -(deltaX4 x1 x2 x3 x4 x5 x6) := div_pos hx hb2
      have hap := Real.arctan_pos.mpr hpos
      linarith
    · exact by
        have hge := Real.neg_pi_div_two_lt_arctan
          (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
            -(deltaX4 x1 x2 x3 x4 x5 x6))
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
    · exact absurd hx (by
        have hy : -(deltaX4 x1 x2 x3 x4 x5 x6) = 0 := by linarith
        rw [hy] at hb
        simp at hb
        have hle : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) = 0 :=
          Real.sqrt_eq_zero_of_nonpos hb
        linarith)
  linarith

/-- HOL `DIH_Y_LT_PI`. -/
theorem DIH_Y_LT_PI {y1 y2 y3 y4 y5 y6 : ℝ} (h1 : 0 < y1)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    dihY y1 y2 y3 y4 y5 y6 < Real.pi := by
  refine DIH_X_LT_PI (by positivity) hd

/-- HOL `CRITICAL_WEIGHT_POS_LE`. -/
theorem CRITICAL_WEIGHT_POS_LE (V X : Set V3) : 0 ≤ criticalWeight V X :=
  div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- HOL `GAMMAX_NO_BETA`. -/
theorem GAMMAX_NO_BETA (V : Set V3) (ul : List V3) (X : Set V3) (e : Set V3) (k : ℕ)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell k V ul)
    (hn : ¬ nullSet X) (hk : k < 4) (he : e ∈ criticalEdgeX V X)
    (hg : gammaX V X lmfun ≥ 0) :
    gammaX V X lmfun * criticalWeight V X + betaBumpV1 V e X ≥ 0 := by
  sorry

/-- HOL `REUHADY` (owned by the REUHADY.hl lane — PackingAuto24; the copy
here is the form consumed by `LEAF_RANK_REUHADY` below). -/
theorem REUHADY (V : Set V3) (u0 u1 v1 v2 : V3) (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2]) (hv : v1 ≠ v2) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧ X ⊆ wedgeGe u0 u1 v1 v2}
        (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

/-- HOL `s_leaf_leaf`. -/
theorem s_leaf_leaf (V : Set V3) (ul : List V3) (x : V3) (hx : x ∈ s_leaf V ul) :
    leaf V [elV ul 0, elV ul 1, x] := hx.1

/-- HOL `s_leaf_collinear`. -/
theorem s_leaf_collinear (V : Set V3) (ul : List V3) (x : V3) (hp : Packing V)
    (hs : saturated V) (hx : x ∈ s_leaf V ul) : ¬ Collinear3 (elV ul 0) (elV ul 1) x := by
  sorry

/-- HOL `LEAF_RANKING_LEMMA`: existence of the azim-ordered cyclic
parametrization of `s_leaf`. -/
theorem LEAF_RANKING_LEMMA (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (hn : 0 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ∃ f : ℕ → V3, f '' (univ : Set ℕ) = s_leaf V ul ∧
      (∀ i, f (i + n) = f i) ∧
      (∀ i j, i < n → j < n → i < j →
        azim (elV ul 0) (elV ul 1) w0 (f i) < azim (elV ul 0) (elV ul 1) w0 (f j)) := by
  sorry

/-- HOL `S_LEAF_SET` (definitional). -/
theorem S_LEAF_SET (V : Set V3) (ul : List V3) :
    s_leaf V ul = {u | leaf V [elV ul 0, elV ul 1, u] ∧
      (ccKe V [elV ul 0, elV ul 1, u] = 4 ∨ ccKe V [elV ul 1, elV ul 0, u] = 4)} :=
  rfl

/-- HOL `LEAF_RANK_COLLINEAR` (renamed from LEAF_RANK_COLLINEAR). -/
theorem LEAF_RANK_COLLINEAR (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (k : ℕ) (hp : Packing V) (hs : saturated V) (hr : leaf_rank V ul w0 n f) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (f k) := by
  sorry

/-- HOL `S_LEAF_SUBSET_PACKING`. -/
theorem S_LEAF_SUBSET_PACKING (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) : s_leaf V ul ⊆ V := by
  intro x hx
  have hleaf : barV V 2 [elV ul 0, elV ul 1, x] := hx.1.1
  obtain ⟨-, hpre⟩ := hleaf
  have hv := hpre [elV ul 0, elV ul 1, x] ⟨⟨[], rfl⟩, by simp⟩
  exact hv.2.1 (by simp [setOfList])

/-- HOL `S_LEAF_BOUNDED`. -/
theorem S_LEAF_BOUNDED (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) :
    s_leaf V ul ⊆ Metric.ball (elV ul 0) (2 * Real.sqrt 2) := by
  sorry

/-- HOL `S_LEAF_FINITE`. -/
theorem S_LEAF_FINITE (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) : (s_leaf V ul).Finite := by
  sorry

/-- HOL `S_LEAF_SYM`. -/
theorem S_LEAF_SYM (V : Set V3) (u0 u1 : V3) (hp : Packing V) (hs : saturated V) :
    s_leaf V [u1, u0] = s_leaf V [u0, u1] := by
  sorry

/-- HOL `S_LEAF_TRUNCATE`. -/
theorem S_LEAF_TRUNCATE (V : Set V3) (ul : List V3) :
    s_leaf V ul = s_leaf V [elV ul 0, elV ul 1] := by
  simp [s_leaf, elV]

/-- HOL `MCELL_AVOID_LEAVES`. -/
theorem MCELL_AVOID_LEAVES (V : Set V3) (ul : List V3) (X : Set V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet X) (hm : mcellSet V X) :
    ∃ v, v ∈ X ∧ ∀ u, u ∈ s_leaf V ul → ¬ v ∈ affGe {elV ul 0, elV ul 1} {u} := by
  sorry

/-- HOL `MCELL_WEDGE_UNIQUE`: a non-null cell with the stem edge sits in at
most one leaf wedge. -/
theorem MCELL_WEDGE_UNIQUE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hr : leaf_rank V ul w0 n f) (hm : mcellSet V X) (hn : ¬ nullSet X)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    ∀ i j, i < n → j < n →
      X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) →
      X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1)) → i = j := by
  sorry

/-- HOL `LEAF_RANK_PERIODIC`. -/
theorem LEAF_RANK_PERIODIC (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hr : leaf_rank V ul w0 n f) : periodic f n := hr.2.1

/-- HOL `LEAF_RANK_AZIM_INJ`. -/
theorem LEAF_RANK_AZIM_INJ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i j : ℕ) (hs : saturated V) (hp : Packing V) (hn : n ≠ 0)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    (azim (elV ul 0) (elV ul 1) (f i) (f j) = 0 ↔ i % n = j % n) := by
  sorry

/-- HOL `LEAF_RANK_AZIM_NZ`. -/
theorem LEAF_RANK_AZIM_NZ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hs : saturated V) (hp : Packing V) (hr : leaf_rank V ul w0 n f)
    (hn : 1 < n) (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ¬ (azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) = 0) := by
  sorry

/-- HOL `MCELL_IN_WEDGE`. -/
theorem MCELL_IN_WEDGE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (X : Set V3) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hr : leaf_rank V ul w0 n f) (hm : mcellSet V X) (hnn : ¬ nullSet X)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    ∃ i, i < n ∧ X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_REUHADY`. -/
theorem LEAF_RANK_REUHADY (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    azim_mcell V f (elV ul 0) (elV ul 1) i =
      azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_BIJ`. -/
theorem LEAF_RANK_BIJ (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    Set.BijOn Prod.snd
      {p : ℕ × Set V3 | p.1 < n ∧ mcellSet V p.2 ∧
        {elV ul 0, elV ul 1} ∈ edgeX V p.2 ∧
        p.2 ⊆ wedgeGe (elV ul 0) (elV ul 1) (f p.1) (f (p.1 + 1))}
      {X | mcellSet V X ∧ {elV ul 0, elV ul 1} ∈ edgeX V X} := by
  sorry

/-- HOL `LEAF_RANK_GRUTOTI` (consumes GRUTOTI via `REUHADY`; the sum of the
wedge azim-mcells around the stem is `2*pi`). -/
theorem LEAF_RANK_GRUTOTI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f)
    (hhl : hl [elV ul 0, elV ul 1] < Real.sqrt 2) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f (elV ul 0) (elV ul 1) i =
      2 * Real.pi := by
  sorry

/-- HOL `LEAF_RANK_GG_SUM`: the per-wedge gg sums telescope to the full
edge sum over all cells carrying the stem edge. -/
theorem LEAF_RANK_GG_SUM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V ul) n) (h0 : elV ul 0 ∈ V) (h1 : elV ul 1 ∈ V)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hr : leaf_rank V ul w0 n f) :
    ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f (elV ul 0) (elV ul 1) i =
      setSum {X | mcellSet V X ∧ {elV ul 0, elV ul 1} ∈ edgeX V X} fun X =>
        gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {elV ul 0, elV ul 1} X := by
  sorry

/-- HOL `MCELL2_DIHX_POS`. -/
theorem MCELL2_DIHX_POS (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell2 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    0 < dihX V X (elV ul 0, elV ul 1) := by
  sorry

/-- HOL `MCELL3_CONVEX_HULL`. -/
theorem MCELL3_CONVEX_HULL (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul)
    (hn : ¬ nullSet (mcell3 V ul)) :
    mcell3 V ul =
      convexHull ℝ ({elV ul 0, elV ul 1, elV ul 2, mxi V ul} : Set V3) := by
  sorry

/-- HOL `MCELL3_EXTREME_CARD`. -/
theorem MCELL3_EXTREME_CARD (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul)
    (hn : ¬ nullSet (mcell3 V ul)) :
    Set.ncard ({elV ul 0, elV ul 1, elV ul 2, mxi V ul} : Set V3) = 4 := by
  sorry

/-- HOL `MCELL3_DIHX`. -/
theorem MCELL3_DIHX (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell3 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) (hn : ¬ nullSet X) :
    dihX V X (elV ul 0, elV ul 1) =
      dihV (elV ul 0) (elV ul 1) (elV ul 2) (mxi V ul) := by
  sorry

/-- HOL `MCELL3_DIHX_POS`. -/
theorem MCELL3_DIHX_POS (V : Set V3) (X : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (hX : X = mcell3 V ul)
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X) :
    0 < dihX V X (elV ul 0, elV ul 1) := by
  sorry

/-- HOL `MCELL3_DOMAIN`. -/
theorem MCELL3_DOMAIN (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell3 V ul)) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (elV ul 2) ∧
      2 ≤ dist (elV ul 1) (elV ul 2) ∧ 2 ≤ dist (elV ul 0) (elV ul 2) ∧
      2 ≤ dist (elV ul 0) (elV ul 1) ∧
      dist (elV ul 1) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 1) < 2 * Real.sqrt 2 ∧
      eta_y (dist (elV ul 0) (elV ul 1)) (dist (elV ul 0) (elV ul 2))
          (dist (elV ul 1) (elV ul 2)) < Real.sqrt 2 := by
  sorry

/-- HOL `TSKAJXY_3` (the 3-cell case of the TSKAJXY bank; consumes
`pack_nonlinear_non_ox3q1h`). -/
theorem TSKAJXY_3 (V : Set V3) (X : Set V3) (ul : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) (hX : X = mcell3 V ul) (hn : ¬ nullSet X) :
    gammaX V X lmfun ≥ 0 := by
  sorry

/-- HOL `MCELL4_LEAF2`. -/
theorem MCELL4_LEAF2 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    leaf V [elV ul 0, elV ul 1, elV ul 2] := by
  sorry

/-- HOL `MCELL4_CONVEX_HULL`. -/
theorem MCELL4_CONVEX_HULL (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    mcell4 V ul = convexHull ℝ ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) := by
  sorry

/-- HOL `MCELL4_CARD4`. -/
theorem MCELL4_CARD4 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    Set.ncard ({elV ul 0, elV ul 1, elV ul 2, elV ul 3} : Set V3) = 4 := by
  sorry

/-- HOL `MCELL4_LEAF3`. -/
theorem MCELL4_LEAF3 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    leaf V [elV ul 0, elV ul 1, elV ul 3] := by
  sorry

/-- HOL `MCELL4_LEAF_S_LEAF`. -/
theorem MCELL4_LEAF_S_LEAF (V : Set V3) (ul : List V3) (u : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul))
    (hl' : leaf V [elV ul 0, elV ul 1, u]) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3)) :
    u ∈ s_leaf V [elV ul 0, elV ul 1] := by
  sorry

/-- HOL `S_LEAF_CARD2`. -/
theorem S_LEAF_CARD2 (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 ul) (hn : ¬ nullSet (mcell4 V ul)) :
    2 ≤ Set.ncard (s_leaf V [elV ul 0, elV ul 1]) := by
  sorry

/-- HOL `LEAF_RANK_ONTO`: the leaf-rank parametrization hits both vertices
of the 4-cell. -/
theorem LEAF_RANK_ONTO (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (u : V3) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : n ≠ 0)
    (hnn : ¬ nullSet (mcell4 V ul)) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3)) :
    ∃ i, i < n ∧ u = f i := by
  sorry

/-- HOL `S_LEAF_IN_WEDGE_GE`. -/
theorem S_LEAF_IN_WEDGE_GE (V : Set V3) (ul : List V3) (u w0 : V3) (n : ℕ)
    (f : ℕ → V3) (j i' : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hl' : leaf V [elV ul 0, elV ul 1, u])
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hu : u = f i') (hi' : i' < n)
    (hw : u ∈ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1))) :
    u = f j ∨ u = f (j + 1) := by
  sorry

/-- HOL `LEAF_IN_WEDGE_GE`. -/
theorem LEAF_IN_WEDGE_GE (V : Set V3) (ul : List V3) (u w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hl' : leaf V [elV ul 0, elV ul 1, u]) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul)) (hu : u ∈ ({elV ul 2, elV ul 3} : Set V3))
    (hw : u ∈ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    u = f i ∨ u = f (i + 1) := by
  sorry

/-- HOL `MCELL4_FI_EL`. -/
theorem MCELL4_FI_EL (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    ({elV ul 2, elV ul 3} : Set V3) = {f i, f (i + 1)} := by
  sorry

/-- HOL `MCELL4_FI`. -/
theorem MCELL4_FI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    mcell4 V ul = convexHull ℝ ({elV ul 0, elV ul 1, f i, f (i + 1)} : Set V3) := by
  sorry

/-- HOL `MCELL4_BARV_FI`. -/
theorem MCELL4_BARV_FI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    barV V 3 [elV ul 0, elV ul 1, f i, f (i + 1)] ∧
      mcell4 V ul = mcell4 V [elV ul 0, elV ul 1, f i, f (i + 1)] := by
  sorry

/-- HOL `MCELL4_AZIM_LT_PI`. -/
theorem MCELL4_AZIM_LT_PI (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) < Real.pi := by
  sorry

/-- HOL `MCELL4_DIHX_AZIM`. -/
theorem MCELL4_DIHX_AZIM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    dihX V (mcell4 V ul) (elV ul 0, elV ul 1) =
      azim (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK_HAS_SIZE`.  Proof: the `n`-periodicity collapses the
surjective image `f '' univ` to `f '' {i | i < n}` (PERIODIC_IMAGE), and the
strict `azim`-increase makes `f` injective there (an equal-value pair would
force `azim w0 x < azim w0 x`), so `Set.ncard (f '' Iio n) = ncard (Iio n) =
n` (InjOn.ncard_image + ncard_Iio_nat).  The geometric antecedents of the HOL
proof (S_LEAF_FINITE, LEAF_RANK_AZIM_INJ) are not needed. -/
theorem LEAF_RANK_HAS_SIZE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : n ≠ 0) (hp : Packing V) (hs : saturated V) (hr : leaf_rank V ul w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    HasSizeP25 (s_leaf V ul) n := by
  have hper : periodic f n := LEAF_RANK_PERIODIC V ul w0 n f hr
  have himg : f '' {i : ℕ | i < n} = s_leaf V ul := by
    rw [PERIODIC_IMAGE hn hper]
    exact hr.1
  refine ⟨?_, ?_⟩
  · rw [← himg]
    exact (Set.finite_Iio n).image f
  · have hinj : Set.InjOn f {i : ℕ | i < n} := by
      intro i hi j hj hij
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact absurd (hr.2.2 i j hi hj hlt) (by rw [← hij]; exact lt_irrefl _)
      · exact heq
      · exact absurd (hr.2.2 j i hj hi hgt) (by rw [hij]; exact lt_irrefl _)
    rw [← himg, Set.InjOn.ncard_image hinj]
    exact Set.ncard_Iio_nat n

/-- HOL `MCELL4_FULL_WEDGE`: the 4-cell is the unique cell in its wedge. -/
theorem MCELL4_FULL_WEDGE (V : Set V3) (X : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul)) (hm : mcellSet V X)
    (hX : X ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)))
    (he : {elV ul 0, elV ul 1} ∈ edgeX V X)
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    X = mcell4 V ul := by
  sorry

/-- HOL `MCELL4_REPARAM`. -/
theorem MCELL4_REPARAM (V : Set V3) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hc : Set.ncard (setOfList ul) = 4)
    (hs' : setOfList ul = setOfList vl) (hl : vl.length = 4)
    (hnn : ¬ nullSet (mcell4 V ul)) (hb : barV V 3 ul) :
    mcell4 V ul = mcell4 V vl ∧ barV V 3 vl := by
  sorry

/-- HOL `MCELL4_GG`: for the unique wedge cell, `gg_mcell` collapses to the
single cell weight. -/
theorem MCELL4_GG (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hb : barV V 3 ul)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hX : mcell4 V ul = mcell4 V ul)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    gg_mcell V f (elV ul 0) (elV ul 1) i =
      gammaX V (mcell4 V ul) lmfun * criticalWeight V (mcell4 V ul) +
        betaBumpV1 V {elV ul 0, elV ul 1} (mcell4 V ul) := by
  sorry

/-- HOL `LEAF_RANK_TRUNCATE`. -/
theorem LEAF_RANK_TRUNCATE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3) :
    leaf_rank V ul w0 n f = leaf_rank V [elV ul 0, elV ul 1] w0 n f := by
  unfold leaf_rank
  rw [S_LEAF_TRUNCATE]
  congr 1

/-- HOL `LEAF_RANK_S_LEAF`. -/
theorem LEAF_RANK_S_LEAF (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hr : leaf_rank V ul w0 n f) : f i ∈ s_leaf V ul := by
  have h1 : f i ∈ f '' (univ : Set ℕ) := ⟨i, Set.mem_univ _, rfl⟩
  exact hr.1 ▸ h1

/-- HOL `CC_CELL_SUBSET_WEDGE`. -/
theorem CC_CELL_SUBSET_WEDGE (V : Set V3) (ul : List V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : 1 < n)
    (he : ({u0, u1} : Set V3) = {elV ul 0, elV ul 1})
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ccCell V [u0, u1, f j] ⊆ wedgeGe (elV ul 0) (elV ul 1) (f j) (f (j + 1)) ∨
      ccCell V [u0, u1, f j] ⊆
        wedgeGe (elV ul 0) (elV ul 1) (f (j + (n - 1))) (f j) := by
  sorry

/-- HOL `WEDGE_UNIQUE_CC_CELL`: the two cc-cells never sit in the same
interior wedge. -/
theorem WEDGE_UNIQUE_CC_CELL (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f) (hn : 1 < n)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    ¬ (ccCell V [elV ul 0, elV ul 1, f j] ⊆
          wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) ∧
        ccCell V [elV ul 1, elV ul 0, f j] ⊆
          wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) := by
  sorry

/-- HOL `LEAF_RANK4_CHI_MSB`. -/
theorem LEAF_RANK4_CHI_MSB (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n) (hi : i < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    0 < chiMsb [elV ul 0, elV ul 1, f i] (f (i + 1)) := by
  sorry

/-- HOL `LEAF_RANK4_CHI_MSB_ALT`. -/
theorem LEAF_RANK4_CHI_MSB_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hnn : ¬ nullSet (mcell4 V ul))
    (hw : mcell4 V ul ⊆ wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) :
    0 < chiMsb [elV ul 0, elV ul 1, f i] (f (i + 1)) := by
  sorry

/-- HOL `CC_CELL_WEDGE_MATCH_UH`. -/
theorem CC_CELL_WEDGE_MATCH_UH (V : Set V3) (ul : List V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i j : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (he : ({u0, u1} : Set V3) = {elV ul 0, elV ul 1})
    (hw : ccCell V [u0, u1, f j] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)))
    (hk : ccKe V [u0, u1, f j] = 4) :
    ({f j, (ccUh V [u0, u1, f j]).getD 3 0} : Set V3) = {f i, f (i + 1)} := by
  sorry

/-- HOL `K4_CC_WI_ALT`. -/
theorem K4_CC_WI_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 0, elV ul 1, f i] = 4) :
    ccCell V [elV ul 0, elV ul 1, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `K4_CC_WIM`. -/
theorem K4_CC_WIM (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 1, elV ul 0, f i] = 4) :
    ccCell V [elV ul 1, elV ul 0, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f (i + (n - 1))) (f i) := by
  sorry

/-- HOL `K3_CC_WI_ALT`. -/
theorem K3_CC_WI_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 0, elV ul 1, f i] = 3) :
    ccCell V [elV ul 0, elV ul 1, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1)) := by
  sorry

/-- HOL `K3_CC_WIM_ALT`. -/
theorem K3_CC_WIM_ALT (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) (hn : 1 < n)
    (hk : ccKe V [elV ul 1, elV ul 0, f i] = 3) :
    ccCell V [elV ul 1, elV ul 0, f i] ⊆
      wedgeGe (elV ul 0) (elV ul 1) (f (i + (n - 1))) (f i) := by
  sorry

/-- HOL `NO_4CELL_IMP_K3`: a wedge with no 4-cell carries two 3-cells. -/
theorem NO_4CELL_IMP_K3 (V : Set V3) (W : Set V3) (ul : List V3) (w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [elV ul 0, elV ul 1] w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0)
    (hW : W = wedgeGe (elV ul 0) (elV ul 1) (f i) (f (i + 1))) (hn : 1 < n)
    (hno4 : ¬ ∃ vl, barV V 3 vl ∧ {elV ul 0, elV ul 1} ∈ edgeX V (mcell4 V vl) ∧
      mcell4 V vl ⊆ W) :
    ccKe V [elV ul 1, elV ul 0, f (i + 1)] = 3 ∧
      ccKe V [elV ul 0, elV ul 1, f i] = 3 ∧
      ccCell V [elV ul 0, elV ul 1, f i] ⊆ W ∧
      ccCell V [elV ul 1, elV ul 0, f (i + 1)] ⊆ W ∧
      ccCell V [elV ul 0, elV ul 1, f i] ≠
        ccCell V [elV ul 1, elV ul 0, f (i + 1)] := by
  sorry

/-- HOL `JSPEVYT_EXPLICIT`. -/
theorem JSPEVYT_EXPLICIT (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hnc : ¬ Collinear3 u0 u1 u2) (hhl : hl [u0, u1, u2] ≤ 1.34)
    (h1 : 2 * hminus ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) :
    dist u1 u2 < 2 * hminus := by
  sorry

/-- HOL `CELL_CLUSTER_ESTIMATE_REDUCE`: the per-edge statement implies the
cell-cluster inequality. -/
theorem CELL_CLUSTER_ESTIMATE_REDUCE (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hedge : ∀ u0 u1 : V3, u0 ≠ u1 → hminus ≤ hl [u0, u1] → hl [u0, u1] ≤ hplus →
      0 ≤ setSum {X | {u0, u1} ∈ edgeX V X ∧ mcellSet V X} fun X =>
        gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X) :
    cellClusterInequality V := by
  sorry

/-- HOL `cc_card_data` (field projection). -/
theorem cc_card_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_card_v11 (cc_data_v8 V f u0 u1) = Set.ncard (s_leaf V [u0, u1]) :=
  rfl

/-- HOL `cc_real_data` (field projections). -/
theorem cc_real_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_azim_v11 (cc_data_v8 V f u0 u1) = azim_mcell V f u0 u1 ∧
      cc_gg_v11 (cc_data_v8 V f u0 u1) = gg_mcell V f u0 u1 ∧
        cc_gg3a_v11 (cc_data_v8 V f u0 u1) =
            (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
              criticalWeight V (ccCell V [u0, u1, f i])) ∧
          cc_gg3b_v11 (cc_data_v8 V f u0 u1) =
            (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
              criticalWeight V (ccCell V [u1, u0, f (i + 1)])) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- HOL `cc_bool_data` (field projections). -/
theorem cc_bool_data (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_subcrit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => dist (f i) (f (i + 1)) < 2 * hminus) ∧
      cc_crit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => 2 * hminus ≤ dist (f i) (f (i + 1)) ∧
          dist (f i) (f (i + 1)) ≤ 2 * hplus) ∧
      cc_supercrit_v11 (cc_data_v8 V f u0 u1) =
        (fun i => 2 * hplus < dist (f i) (f (i + 1))) ∧
      cc_small_v11 (cc_data_v8 V f u0 u1) =
        (fun i => dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
      cc_small_eta_v11 (cc_data_v8 V f u0 u1) =
        (fun i => hl [u0, u1, f i] < 1.34) ∧
      cc_4cell_v11 (cc_data_v8 V f u0 u1) =
        (fun i => ∃ ul, barV V 3 ul ∧ {u0, u1} ∈ edgeX V (mcell4 V ul) ∧
          mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HOL `cc_bool_model_data`. -/
theorem cc_bool_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (h0 : u0 ∈ V) (h1 : u1 ∈ V) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_bool_model_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `cc_prep_model_data`. -/
theorem cc_prep_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_bool_prep_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `LEAF_DOMAIN`. -/
theorem LEAF_DOMAIN (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hl' : leaf V ul) :
    ¬ Collinear3 (elV ul 0) (elV ul 1) (elV ul 2) ∧
      2 ≤ dist (elV ul 1) (elV ul 2) ∧ 2 ≤ dist (elV ul 0) (elV ul 2) ∧
      2 ≤ dist (elV ul 0) (elV ul 1) ∧
      dist (elV ul 1) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 2) < 2 * Real.sqrt 2 ∧
      dist (elV ul 0) (elV ul 1) < 2 * Real.sqrt 2 ∧
      eta_y (dist (elV ul 0) (elV ul 1)) (dist (elV ul 0) (elV ul 2))
          (dist (elV ul 1) (elV ul 2)) < Real.sqrt 2 := by
  sorry

/-- HOL `CELL_CLUSTER_N_LE_1`: a critical stem with at most one leaf has a
nonnegative weight sum. -/
theorem CELL_CLUSTER_N_LE_1 (V : Set V3) (u0 u1 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hp : Packing V) (hs : saturated V) (hlo : hminus ≤ hl [u0, u1])
    (hhi : hl [u0, u1] ≤ hplus) (hcard : Set.ncard (s_leaf V [u0, u1]) ≤ 1) :
    0 ≤ setSum {X | {u0, u1} ∈ edgeX V X ∧ mcellSet V X} fun X =>
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X := by
  sorry

/-- HOL `RAD_PI_IMP_WEDGE4`: an angle under `pi` with radius `< sqrt 2`
forces a 4-cell in the wedge. -/
theorem RAD_PI_IMP_WEDGE4 (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (i : ℕ)
    (u0 u1 : V3) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f)
    (hapi : azim u0 u1 (f i) (f (i + 1)) < Real.pi)
    (hrad : radV {u0, u1, f i, f (i + 1)} < Real.sqrt 2) :
    ∃ ul, mcell4 V ul ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧ barV V 3 ul ∧
      {u0, u1} ∈ edgeX V (mcell4 V ul) := by
  sorry

/-- HOL `LEAF_RANK_SUC_INJ`. -/
theorem LEAF_RANK_SUC_INJ (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) : f i ≠ f (i + 1) := by
  intro heq
  have hper : periodic f n := LEAF_RANK_PERIODIC V [u0, u1] w0 n f hr
  have h1 : f i = f (i % n) := (p25_f_mod hper i).symm
  have h2 : f (i + 1) = f ((i + 1) % n) := (p25_f_mod hper (i + 1)).symm
  have h3 : i % n < n := Nat.mod_lt i (by omega)
  have h4 : (i + 1) % n < n := Nat.mod_lt _ (by omega)
  rcases lt_trichotomy (i % n) ((i + 1) % n) with hlt | heq' | hgt
  · have hord := hr.2.2 _ _ h3 h4 hlt
    rw [← h2, ← h1, heq] at hord
    linarith
  · exact absurd heq' (MOD_INJ1_ALT_p25 (by omega) (by omega) (by omega) i)
  · have hord := hr.2.2 _ _ h4 h3 hgt
    rw [← h1, ← h2, heq] at hord
    linarith

/-- HOL `DIST_I_SUCI`. -/
theorem DIST_I_SUCI (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hnc : ¬ Collinear3 u0 u1 w0) (hr : leaf_rank V [u0, u1] w0 n f) :
    2 ≤ dist (f i) (f (i + 1)) := by
  sorry

/-- HOL `WEDGE3_Y4`: a 3-cell wedge yields the analytic `y4` certificate. -/
theorem WEDGE3_Y4 (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (i : ℕ) (u0 u1 : V3)
    (y1 y2 y3 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n)
    (hp : Packing V) (hs : saturated V) (hnc : ¬ Collinear3 u0 u1 w0)
    (hr : leaf_rank V [u0, u1] w0 n f) (hcey : criticalEdgeY (dist u0 u1))
    (hno4 : ¬ ∃ vl, barV V 3 vl ∧ {u0, u1} ∈ edgeX V (mcell4 V vl) ∧
      mcell4 V vl ⊆ wedgeGe u0 u1 (f i) (f (i + 1)))
    (hy1 : y1 = dist u0 u1) (hy2 : y2 = dist u0 (f i))
    (hy3 : y3 = dist u0 (f (i + 1))) (hy5 : y5 = dist u1 (f (i + 1)))
    (hy6 : y6 = dist u1 (f i)) :
    ∃ y4, 2 ≤ y4 ∧ y4 ≤ 2 * Real.sqrt 2 ∧
      0 < deltaY y1 y2 y3 y4 y5 y6 ∧
      dihY y1 y2 y3 y4 y5 y6 ≤ azim u0 u1 (f i) (f (i + 1)) ∧
      2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6 ∧
      (azim u0 u1 (f i) (f (i + 1)) < Real.pi →
        dist (f i) (f (i + 1)) ≤ 2 * Real.sqrt 2 → y4 = dist (f i) (f (i + 1))) := by
  sorry

/-- HOL `cc_4_cc_ke4`. -/
theorem cc_4_cc_ke4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hper : periodic f n) (hn : 1 < n)
    (hl' : leaf V [u0, u1, f i]) (h4 : cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 4 := by
  sorry

/-- HOL `cc_4_cc_cell`: on a 4-cell wedge, `gg_mcell` equals the cc-cell
weight. -/
theorem cc_4_cc_cell (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hper : periodic f n)
    (hl' : leaf V [u0, u1, f i]) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    gg_mcell V f u0 u1 i =
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) +
        betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) := by
  sorry

/-- Helper: `setSum` respects set equality. -/
private theorem p25_setSum_congr {α : Type*} {s t : Set α} {g : α → ℝ} (h : s = t) :
    setSum s g = setSum t g := by
  unfold setSum
  rw [h]

/-- HOL `LEAF_RANK_PROPS`: the full leaf-rank extraction from a failing
cell-cluster inequality (the case-analysis engine). -/
theorem LEAF_RANK_PROPS (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hcc : ¬ cellClusterInequality V) (hnl : pack_nonlinear_non_ox3q1h) :
    ∃ u0 u1 n w0 f : _, 1 < n ∧ HasSizeP25 (s_leaf V [u0, u1]) n ∧ u0 ≠ u1 ∧
      hminus ≤ hl [u0, u1] ∧ hl [u0, u1] ≤ hplus ∧
      ¬ Collinear3 u0 u1 w0 ∧ leaf_rank V [u0, u1] w0 n f ∧
      u0 ∈ V ∧ u1 ∈ V ∧ periodic f n ∧
      (∀ j, leaf V [u0, u1, f j]) ∧ criticalEdgeY (dist u0 u1) ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i < 0 ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f u0 u1 i = 2 * Real.pi ∧
      (∀ i, azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1))) ∧
      cc_bool_model_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_prep_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `cc_real_dat_def`: the cc_qx/qy/qu/hassmall classes of
`cc_data_v8` in terms of `cc_4` and distances (definitional). -/
theorem cc_real_dat_def (V : Set V3) (f : ℕ → V3) (u0 u1 : V3) :
    cc_qx_v11 (cc_data_v8 V f u0 u1) =
        (fun i => cc_4 V u0 u1 f i ∧
          ¬ (dist u0 (f i) < 2 * hminus ∧
            dist u1 (f i) < 2 * hminus ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus)) ∧
      cc_qy_v11 (cc_data_v8 V f u0 u1) = (fun i => ¬ cc_4 V u0 u1 f i) ∧
      cc_qu_v11 (cc_data_v8 V f u0 u1) =
        (fun i => cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
      cc_hassmall_v11 (cc_data_v8 V f u0 u1) =
        (fun i => (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1)) < 2 * hminus) := by
  have h4 : cc_4cell_v11 (cc_data_v8 V f u0 u1) = fun i => cc_4 V u0 u1 f i := rfl
  have hsm : cc_small_v11 (cc_data_v8 V f u0 u1) =
      fun i => (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) := rfl
  have hsc : cc_subcrit_v11 (cc_data_v8 V f u0 u1) =
      fun i => dist (f i) (f (i + 1)) < 2 * hminus := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i
    simp only [cc_qx_v11, cc_qu_v11, cc_hassmall_v11, h4, hsm, hsc]
    apply propext
    tauto
  · funext i
    simp only [cc_qy_v11, h4]
  · funext i
    simp only [cc_qu_v11, cc_hassmall_v11, h4, hsm, hsc]
    apply propext
    tauto
  · funext i
    simp only [cc_hassmall_v11, hsm]

/-- HOL `real_periodic_data`: the wedge sums are `n`-periodic. -/
theorem real_periodic_data (V : Set V3) (u0 u1 : V3) (f : ℕ → V3) (n : ℕ)
    (hper : periodic f n) :
    periodic (azim_mcell V f u0 u1) n ∧ periodic (gg_mcell V f u0 u1) n ∧
      periodic (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun) n ∧
      periodic (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun) n ∧
      periodic (fun i => gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i])) n ∧
      periodic (fun i => gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)])) n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    unfold azim_mcell
    refine p25_setSum_congr ?_
    refine Set.ext fun X => ?_
    simp only [Set.mem_setOf_eq]
    rw [hper i, show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    unfold gg_mcell
    refine p25_setSum_congr ?_
    refine Set.ext fun X => ?_
    simp only [Set.mem_setOf_eq]
    rw [hper i, show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    simp only [hper i]
  · intro i
    simp only [show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]
  · intro i
    simp only [hper i]
  · intro i
    simp only [show (i + n) + 1 = i + 1 + n from by omega, hper (i + 1)]

/-- HOL `LEAF_RANK_LEAF`. -/
theorem LEAF_RANK_LEAF (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hr : leaf_rank V [u0, u1] w0 n f) : leaf V [u0, u1, f i] := by
  have h := LEAF_RANK_S_LEAF V [u0, u1] w0 n f i hr
  exact h.1

/-- HOL `cc_4_UL`. -/
theorem cc_4_UL (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    ccCell V [u0, u1, f i] = mcell4 V [u0, u1, f i, f (i + 1)] := by
  sorry

/-- HOL `EDGEX_PAIR`. -/
theorem EDGEX_PAIR (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X) :
    ∃ u v : V3, e = {u, v} ∧ u ≠ v := by
  obtain ⟨u, v, huv, _, _, huvne⟩ := he
  exact ⟨u, v, huv, huvne⟩

/-- HOL `MCELL4_EDGE_EXPLICIT`. -/
theorem MCELL4_EDGE_EXPLICIT (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet (mcell4 V [u0, u1, u2, u3]))
    (hb : barV V 3 [u0, u1, u2, u3]) :
    edgeX V (mcell4 V [u0, u1, u2, u3]) =
      {{u0, u1}, {u0, u2}, {u0, u3}, {u1, u2}, {u1, u3}, {u2, u3}} := by
  sorry

/-- HOL `CC_4_PROPS`: the full 4-cell wedge certificate. -/
theorem CC_4_PROPS (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 4 ∧
      hl [u0, u1, f i, f (i + 1)] < Real.sqrt 2 ∧
      convexHull ℝ ({u0, u1, f i, f (i + 1)} : Set V3) = ccCell V [u0, u1, f i] ∧
      ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) ∧
      ccCell V [u0, u1, f i] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u0, u1, f i] = mcell4 V [u0, u1, f i, f (i + 1)] ∧
      ¬ Collinear3 u0 u1 (f i) ∧ ¬ Collinear3 u0 u1 (f (i + 1)) ∧
      leaf V [u0, u1, f i] ∧ leaf V [u0, u1, f (i + 1)] ∧
      ¬ nullSet (ccCell V [u0, u1, f i]) ∧
      barV V 3 [u0, u1, f i, f (i + 1)] := by
  sorry

/-- HOL `CC_4_BETA_BUMP_EXPLICIT`. -/
theorem CC_4_BETA_BUMP_EXPLICIT (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n)
    (h4 : cc_4 V u0 u1 f i) (hcey : criticalEdgeY (dist u0 u1))
    (hcey' : criticalEdgeY (dist (f i) (f (i + 1))))
    (hd1 : dist u0 (f i) < 2 * hminus) (hd2 : dist u0 (f (i + 1)) < 2 * hminus)
    (hd3 : dist u1 (f i) < 2 * hminus) (hd4 : dist u1 (f (i + 1)) < 2 * hminus) :
    betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) =
      bump (dist u0 u1 / 2) - bump (dist (f i) (f (i + 1)) / 2) := by
  sorry

/-- HOL `CC_4_BETA_BUMP_0`. -/
theorem CC_4_BETA_BUMP_0 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hp : Packing V) (hs : saturated V) (hr : leaf_rank V [u0, u1] w0 n f)
    (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n) (h4 : cc_4 V u0 u1 f i)
    (hnot : ¬ (criticalEdgeY (dist u0 u1) ∧
      criticalEdgeY (dist (f i) (f (i + 1))) ∧
      dist u0 (f i) < 2 * hminus ∧ dist u0 (f (i + 1)) < 2 * hminus ∧
      dist u1 (f i) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus)) :
    betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) = 0 := by
  sorry

/-- HOL `critical_edgeX_critical_edge_y`. -/
theorem critical_edgeX_critical_edge_y (V : Set V3) (X : Set V3) (u v : V3) :
    ({u, v} : Set V3) ∈ criticalEdgeX V X ↔
      ({u, v} : Set V3) ∈ edgeX V X ∧ criticalEdgeY (dist u v) := by
  constructor
  · rintro ⟨u', v', huv, hmem, h1, h2⟩
    rw [pair_eq_pair_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨hmem, ?_⟩
      unfold criticalEdgeY
      rw [HL_2] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · refine ⟨hmem, ?_⟩
      unfold criticalEdgeY
      rw [HL_2, dist_comm] at h1 h2
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨hmem, h1, h2⟩
    have hhl := HL_2 u v
    exact ⟨u, v, rfl, hmem, by linarith, by linarith⟩

/-- HOL `critical_weight_wtcount6_y`. -/
theorem critical_weight_wtcount6_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ)
    (f : ℕ → V3) (i : ℕ) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0) (hn : 1 < n)
    (h4 : cc_4 V u0 u1 f i) (hcey : criticalEdgeY (dist u0 u1)) :
    criticalWeight V (ccCell V [u0, u1, f i]) =
      1 / (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) := by
  sorry

/-- HOL `c_4_azim_mcell_dih_y`: the 4-cell wedge dihedral is the `dih_y`
value. -/
theorem c_4_azim_mcell_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (h4 : cc_4 V u0 u1 f i) :
    azim_mcell V f u0 u1 i =
      dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  sorry

/-- HOL `NOT_COPLANAR_IMP_CARD4_ALT`. -/
theorem NOT_COPLANAR_IMP_CARD4_ALT (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    Set.ncard ({u0, u1, u2, u3} : Set V3) = 4 := by
  by_contra hcon
  push_neg at hcon
  -- some pair must coincide; then the set lives in a plane
  have hdup : u0 = u1 ∨ u0 = u2 ∨ u0 = u3 ∨ u1 = u2 ∨ u1 = u3 ∨ u2 = u3 := by
    by_contra hall
    push_neg at hall
    apply hcon
    rw [Set.ncard_insert_of_notMem (show u0 ∉ ({u1, u2, u3} : Set V3) from by simp [hall.1,
      hall.2.1, hall.2.2.1]),
      Set.ncard_insert_of_notMem (show u1 ∉ ({u2, u3} : Set V3) from by simp [hall.2.2.2.1,
        hall.2.2.2.2.1]),
      Set.ncard_insert_of_notMem (show u2 ∉ ({u3} : Set V3) from by simp [hall.2.2.2.2.2]),
      Set.ncard_singleton]
  have mem3 : ∀ (t1 t2 t3 a : V3), a = t1 ∨ a = t2 ∨ a = t3 →
      a ∈ ({t1, t2, t3} : Set V3) := by
    intro t1 t2 t3 a hh
    rcases hh with hh | hh | hh
    · simp [hh]
    · simp [hh]
    · simp [hh]
  rcases hdup with h | h | h | h | h | h
  · exact hnc ⟨u0, u2, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u2 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inl (ha.trans h.symm)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inl (ha.trans h.symm)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inl (ha.trans h.symm)))⟩
  · exact hnc ⟨u0, u2, u3, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u2 u3 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (ha.trans h))
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inl (ha.trans h.symm))))⟩
  · exact hnc ⟨u0, u1, u2, fun a ha => SetLike.mem_coe.mpr (mem_affineSpan ℝ (by
      refine mem3 u0 u1 u2 a ?_
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inr (ha.trans h.symm))))⟩

/-- HOL `radius_le_circumradius`. -/
theorem radius_le_circumradius (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    dist u0 u1 ≤ 2 * radV {u0, u1, u2, u3} := by
  sorry

/-- HOL `radius_le_circumradius_all`. -/
theorem radius_le_circumradius_all (u0 u1 u2 u3 : V3)
    (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    dist u0 u1 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u0 u2 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u0 u3 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u1 u2 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u1 u3 ≤ 2 * radV {u0, u1, u2, u3} ∧
      dist u2 u3 ≤ 2 * radV {u0, u1, u2, u3} := by
  sorry

/-- HOL `MCELL4_DOMAIN`: the 4-cell wedge distance certificate. -/
theorem MCELL4_DOMAIN (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (h4 : cc_4 V u0 u1 f i) :
    2 * hminus ≤ dist u0 u1 ∧ dist u0 u1 ≤ 2 * hplus ∧
      2 ≤ dist u0 (f i) ∧ dist u0 (f i) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u0 (f (i + 1)) ∧ dist u0 (f (i + 1)) < 2 * Real.sqrt 2 ∧
      2 ≤ dist (f i) (f (i + 1)) ∧ dist (f i) (f (i + 1)) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u1 (f i) ∧ dist u1 (f i) < 2 * Real.sqrt 2 ∧
      2 ≤ dist u1 (f (i + 1)) ∧ dist u1 (f (i + 1)) < 2 * Real.sqrt 2 ∧
      rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) < 2 ∧
      0 < deltaY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  sorry

/-- HOL `real_model_azim_c4`. -/
theorem real_model_azim_c4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i → azim_mcell V f u0 u1 i < 2.8 := by
  sorry

/-- HOL `gammaX_gamma4fgcy_ALT` (renamed from gammaX_gamm4fgcy_ALT). -/
theorem gammaX_gamma4fgcy_ALT (V : Set V3) (X : Set V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hX : X = mcell4 V [u0, u1, u2, u3]) (hn : ¬ nullSet X) :
    gammaX V X lmfun =
      gamma4fgcyP25 (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2) lmfun := by
  sorry

/-- HOL `GG_MCELL_QUARTER`: the quarter-wedge gg value. -/
theorem GG_MCELL_QUARTER (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hd1 : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)
    (hd2 : dist u0 (f (i + 1)) < 2 * hminus) (hd3 : dist u1 (f (i + 1)) < 2 * hminus)
    (hd4 : dist (f i) (f (i + 1)) < 2 * hminus)
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
        (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun := by
  sorry

/-- HOL `GG_MCELL_BETA`: the beta-wedge gg value. -/
theorem GG_MCELL_BETA (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hd1 : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)
    (hd2 : dist u0 (f (i + 1)) < 2 * hminus) (hd3 : dist u1 (f (i + 1)) < 2 * hminus)
    (hcey' : criticalEdgeY (dist (f i) (f (i + 1))))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun / 2 +
        bump (dist u0 u1 / 2) - bump (dist (f i) (f (i + 1)) / 2) := by
  sorry

/-- HOL `GG_MCELL_NONBETA`. -/
theorem GG_MCELL_NONBETA (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hnot : ¬ ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
      dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
      criticalEdgeY (dist (f i) (f (i + 1)))))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun /
        (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) := by
  sorry

/-- HOL `GG_MCELL_GENERAL`. -/
theorem GG_MCELL_GENERAL (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (h4 : cc_4 V u0 u1 f i)
    (hr : leaf_rank V [u0, u1] w0 n f) :
    gg_mcell V f u0 u1 i =
      gamma4fgcyP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) lmfun /
        (wtcount6Y (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i))) +
        beta_bumpA_yP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
          (dist (f i) (f (i + 1))) (dist u1 (f (i + 1))) (dist u1 (f i)) := by
  sorry

/-- HOL `real_model_gamma_qu`. -/
theorem real_model_gamma_qu (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `ETA_Y_POS_LE_ALT`. -/
theorem ETA_Y_POS_LE_ALT (u0 u1 u2 : V3) :
    0 ≤ eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) := by
  sorry

/-- HOL `ETA_Y_LEMMA`. -/
theorem ETA_Y_LEMMA (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
    (hr : 0 < r) (hrl : r ≤ hl [u0, u1, u2]) :
    r ^ 2 ≤ eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2 := by
  sorry

/-- HOL `ETA_Y_LEMMA_ALT`. -/
theorem ETA_Y_LEMMA_ALT (u0 u1 u2 : V3) (r : ℝ) (hnc : ¬ Collinear3 u0 u1 u2)
    (hrl : hl [u0, u1, u2] ≤ r) :
    eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) ^ 2 ≤ r ^ 2 := by
  sorry

/-- HOL `real_model_fhbv2`. -/
theorem real_model_fhbv2 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
        ¬ (hl [u0, u1, f (i + 1)] < 1.34) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_fhbv2_sym`. -/
theorem real_model_fhbv2_sym (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) ∧
        ¬ (hl [u0, u1, f i] < 1.34) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `CC_3_PROPS`: the full 3-cell wedge certificate. -/
theorem CC_3_PROPS (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1))
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (hn : 1 < n)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    ccKe V [u0, u1, f i] = 3 ∧
      barV V 3 (ccUh V [u0, u1, f i]) ∧
      barV V 3 (ccUh V [u1, u0, f (i + 1)]) ∧
      betaBumpV1 V {u0, u1} (ccCell V [u0, u1, f i]) = 0 ∧
      betaBumpV1 V {u0, u1} (ccCell V [u1, u0, f (i + 1)]) = 0 ∧
      ccKe V [u1, u0, f (i + 1)] = 3 ∧
      ccCell V [u0, u1, f i] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u1, u0, f (i + 1)] ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
      ccCell V [u0, u1, f i] ≠ ccCell V [u1, u0, f (i + 1)] ∧
      ¬ Collinear3 u0 u1 (f i) ∧ ¬ Collinear3 u0 u1 (f (i + 1)) ∧
      hl [u0, u1, f i] < Real.sqrt 2 ∧ hl [u0, u1, f (i + 1)] < Real.sqrt 2 ∧
      hl [u1, u0, f (i + 1)] < Real.sqrt 2 ∧
      leaf V [u0, u1, f i] ∧ leaf V [u0, u1, f (i + 1)] ∧
      leaf V [u1, u0, f (i + 1)] ∧
      2 ≤ dist u0 u1 ∧ 2 ≤ dist u0 (f i) ∧ 2 ≤ dist u0 (f (i + 1)) ∧
      2 ≤ dist u1 (f i) ∧ 2 ≤ dist u1 (f (i + 1)) ∧
      dist u0 u1 ≤ 2 * Real.sqrt 2 ∧ dist u0 (f i) ≤ 2 * Real.sqrt 2 ∧
      dist u0 (f (i + 1)) ≤ 2 * Real.sqrt 2 ∧
      dist u1 (f i) ≤ 2 * Real.sqrt 2 ∧
      dist u1 (f (i + 1)) ≤ 2 * Real.sqrt 2 ∧
      eta_y (dist u0 u1) (dist u0 (f i)) (dist u1 (f i)) < Real.sqrt 2 ∧
      eta_y (dist u0 u1) (dist u0 (f (i + 1))) (dist u1 (f (i + 1))) < Real.sqrt 2 ∧
      ¬ nullSet (ccCell V [u0, u1, f i]) ∧
      ¬ nullSet (ccCell V [u1, u0, f (i + 1)]) ∧
      azim_mcell V f u0 u1 i = azim u0 u1 (f i) (f (i + 1)) ∧
      (∃ y4, 2 ≤ y4 ∧ y4 ≤ 2 * Real.sqrt 2 ∧
        0 < deltaY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
          (dist u1 (f (i + 1))) (dist u1 (f i)) ∧
        dihY (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
            (dist u1 (f (i + 1))) (dist u1 (f i)) ≤ azim u0 u1 (f i) (f (i + 1)) ∧
        2 ≤ rad2YP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
          (dist u1 (f (i + 1))) (dist u1 (f i)) ∧
        (azim u0 u1 (f i) (f (i + 1)) < Real.pi ∧
            dist (f i) (f (i + 1)) ≤ 2 * Real.sqrt 2 →
          y4 = dist (f i) (f (i + 1)))) := by
  sorry

/-- HOL `real_model_gckb`. -/
theorem real_model_gckb (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, 0.606 ≤ azim_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_sum_azim`: the wedge dihedral sum is `2*pi`. -/
theorem real_model_sum_azim (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim_mcell V f u0 u1 i = 2 * Real.pi := by
  sorry

/-- HOL `real_model_ox3q1h_merge`: the ox3q1h certified 4-quarter bound. -/
theorem real_model_ox3q1h_merge (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ((Set.ncard (s_leaf V [u0, u1]) = 4 ∧ ∃ i, cc_4 V u0 u1 f i ∧
        2 * hminus ≤ dist (f i) (f (i + 1)) ∧
          dist (f i) (f (i + 1)) ≤ 2 * hplus ∧
        cc_4 V u0 u1 f (i + 1) ∧
          (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
          dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
          dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus ∧
        cc_4 V u0 u1 f (i + 2) ∧
          (dist u0 (f (i + 2)) < 2 * hminus ∧ dist u1 (f (i + 2)) < 2 * hminus) ∧
          dist u0 (f (i + 2 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 2 + 1)) < 2 * hminus ∧
          dist (f (i + 2)) (f (i + 2 + 1)) < 2 * hminus ∧
        cc_4 V u0 u1 f (i + 3) ∧
          (dist u0 (f (i + 3)) < 2 * hminus ∧ dist u1 (f (i + 3)) < 2 * hminus) ∧
          dist u0 (f (i + 3 + 1)) < 2 * hminus ∧
          dist u1 (f (i + 3 + 1)) < 2 * hminus ∧
          dist (f (i + 3)) (f (i + 3 + 1)) < 2 * hminus) →
      0 ≤ ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i) := by
  sorry

/-- HOL `mcell3_gammaX_gamma3f`. -/
theorem mcell3_gammaX_gamma3f (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    gammaX V (ccCell V [u0, u1, f i]) lmfun =
      gamma3f (dist u0 u1) (dist u0 (f i)) (dist u1 (f i)) (Real.sqrt 2) lmfun := by
  sorry

/-- HOL `mcell3_dihX_dih_y`. -/
theorem mcell3_dihX_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    dihX V (ccCell V [u0, u1, f i]) (u0, u1) =
      dihY (dist u0 u1) (dist u0 (f i)) (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2)
        (dist u1 (f i)) := by
  sorry

/-- HOL `mcell3_gammaXb_gamma3f`. -/
theorem mcell3_gammaXb_gamma3f (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun =
      gamma3f (dist u0 u1) (dist u0 (f (i + 1))) (dist u1 (f (i + 1)))
        (Real.sqrt 2) lmfun := by
  sorry

/-- HOL `mcell3_dihXb_dih_y`. -/
theorem mcell3_dihXb_dih_y (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hr : leaf_rank V [u0, u1] w0 n f) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n)
    (hn : 1 < n) (hno4 : ¬ cc_4 V u0 u1 f i) :
    dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1) =
      dihY (dist u0 u1) (dist u0 (f (i + 1))) (Real.sqrt 2) (Real.sqrt 2)
        (Real.sqrt 2) (dist u1 (f (i + 1))) := by
  sorry

/-- HOL `MCELL3_EDGE_EXPLICIT`. -/
theorem MCELL3_EDGE_EXPLICIT (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hn : ¬ nullSet (mcell3 V [u0, u1, u2, u3]))
    (hb : barV V 3 [u0, u1, u2, u3]) :
    edgeX V (mcell3 V [u0, u1, u2, u3]) =
      {{u0, u1}, {u0, u2}, {u1, u2}} := by
  sorry

/-- HOL `critical_weight1`. -/
theorem critical_weight1 (V : Set V3) (u0 u1 u2 : V3)
    (hcey : criticalEdgeY (dist u0 u1)) (hd1 : dist u0 u2 < 2 * hminus)
    (hd2 : dist u1 u2 < 2 * hminus) (hk : ccKe V [u0, u1, u2] = 3)
    (hp : Packing V) (hs : saturated V)
    (hb : barV V 3 (ccUh V [u0, u1, u2])) (hl' : leaf V [u0, u1, u2])
    (hnn : ¬ nullSet (ccCell V [u0, u1, u2])) :
    criticalWeight V (ccCell V [u0, u1, u2]) = 1 := by
  sorry

/-- HOL `critical_weight1a`. -/
theorem critical_weight1a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i)
    (hd : dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) :
    criticalWeight V (ccCell V [u0, u1, f i]) = 1 := by
  sorry

/-- HOL `critical_weight1b`. -/
theorem critical_weight1b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i)
    (hd : dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) :
    criticalWeight V (ccCell V [u1, u0, f (i + 1)]) = 1 := by
  sorry

/-- HOL `real_model_quqy`. -/
theorem real_model_quqy (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f (i + 1)) →
      0 ≤ gg_mcell V f u0 u1 i +
        gammaX V (ccCell V [u0, u1, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f (i + 1)]) := by
  sorry

/-- HOL `real_model_quqy_sym`. -/
theorem real_model_quqy_sym (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f (i + 1) ∧
            (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
            dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
            dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f i) →
      0 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u1, u0, f (i + 1)]) +
        gg_mcell V f u0 u1 (i + 1) := by
  sorry

/-- HOL `real_model_ztg4`. -/
theorem real_model_ztg4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_azim1`. -/
theorem real_model_azim1 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0659 + 0.042 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz4`. -/
theorem real_model_gaz4 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      -0.0142852 + 0.00609451 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz6`. -/
theorem real_model_gaz6 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
        dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
        dist (f i) (f (i + 1)) < 2 * hminus →
      0.161517 - 0.119482 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gamma_qx`. -/
theorem real_model_gamma_qx (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, cc_4 V u0 u1 f i →
      ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
          dist (f i) (f (i + 1)) < 2 * hminus) →
      0 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_g_qxd`. -/
theorem real_model_g_qxd (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, (cc_4 V u0 u1 f i ∧
        ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
            dist (f i) (f (i + 1)) < 2 * hminus)) →
      2.3 < azim_mcell V f u0 u1 i → 0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `wtcount6_y_sym23` (the 2-3 swap symmetry of the weight count). -/
theorem wtcount6_y_sym23 (y1 y2 y3 y4 y5 y6 : ℝ) :
    wtcount6Y y1 y2 y3 y4 y5 y6 = wtcount6Y y1 y3 y2 y4 y6 y5 := by
  unfold wtcount6Y wtcount3Y
  ring

/-- HOL `wtcount6_y_sym26` (the 2-6/3-5 swap symmetry of the weight count). -/
theorem wtcount6_y_sym26 (y1 y2 y3 y4 y5 y6 : ℝ) :
    wtcount6Y y1 y2 y3 y4 y5 y6 = wtcount6Y y1 y6 y5 y4 y3 y2 := by
  unfold wtcount6Y wtcount3Y
  ring

/-- HOL `beta_bumpA_y_sym23`. -/
theorem beta_bumpA_y_sym23 (y1 y2 y3 y4 y5 y6 : ℝ) :
    beta_bumpA_yP25 y1 y2 y3 y4 y5 y6 = beta_bumpA_yP25 y1 y3 y2 y4 y6 y5 := by
  sorry

/-- HOL `real_model_gamma10`. -/
theorem real_model_gamma10 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f (i + 1)) →
      0.0057 ≤ gg_mcell V f u0 u1 i +
        gammaX V (ccCell V [u0, u1, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f (i + 1)]) := by
  sorry

/-- HOL `real_model_gamma11`. -/
theorem real_model_gamma11 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f (i + 1) ∧
            ¬ (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus ∧
                dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1 + 1)) < 2 * hminus ∧
                dist (f (i + 1)) (f (i + 1 + 1)) < 2 * hminus)) ∧
          ((dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
            dist u0 (f (i + 1 + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1 + 1)) < 2 * hminus) ∧
          ¬ cc_4 V u0 u1 f i) →
      0.0057 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
          criticalWeight V (ccCell V [u1, u0, f (i + 1)]) +
        gg_mcell V f u0 u1 (i + 1) := by
  sorry

/-- HOL `leaf_CIHTIUM` (the certified bound makes long leaves impossible). -/
theorem leaf_CIHTIUM (V : Set V3) (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hp : Packing V) (hs : saturated V) (hl' : leaf V [u0, u1, u2])
    (hcey : criticalEdgeY (dist u0 u1)) (hd1 : 2 * hminus ≤ dist u0 u2)
    (hd2 : 2 * hminus ≤ dist u1 u2) : False := by
  sorry

/-- HOL `gamma4fgcy_sym26`.  The `delta_x`/`delta_x4`/`dih_y` family is
invariant under the edge-endpoint swap `(2 6) (3 5)` (vertex swap `v0 ↔ v1`)
and under the face swap `(2 3) (5 6)` (vertex swap `v2 ↔ v3`); both are
polynomial identities on the bodies, and the four `solY` solid angles plus
the six `dihY`-weighted edge terms of `vol4f` then match term by term. -/
theorem gamma4fgcy_sym26 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) :
    gamma4fgcyP25 y1 y2 y3 y4 y5 y6 f = gamma4fgcyP25 y1 y6 y5 y4 y3 y2 f := by
  have hD1 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX x1 x2 x3 x4 x5 x6 = deltaX x1 x6 x5 x4 x3 x2 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX; ring
  have hD2 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX x1 x2 x3 x4 x5 x6 = deltaX x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX; ring
  have hD3 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x6 x5 x4 x3 x2 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX4; ring
  have hD4 : ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      deltaX4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x3 x2 x4 x6 x5 := by
    intro x1 x2 x3 x4 x5 x6; unfold deltaX4; ring
  have hdy26 : ∀ a b c d e g : ℝ, dihY a b c d e g = dihY a g e d c b := by
    intro a b c d e g
    show dihXf (a * a) (b * b) (c * c) (d * d) (e * e) (g * g) =
      dihXf (a * a) (g * g) (e * e) (d * d) (c * c) (b * b)
    unfold dihXf
    rw [hD1 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g),
      hD3 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)]
  have hdy23 : ∀ a b c d e g : ℝ, dihY a b c d e g = dihY a c b d g e := by
    intro a b c d e g
    show dihXf (a * a) (b * b) (c * c) (d * d) (e * e) (g * g) =
      dihXf (a * a) (c * c) (b * b) (d * d) (g * g) (e * e)
    unfold dihXf
    rw [hD2 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g),
      hD4 (a * a) (b * b) (c * c) (d * d) (e * e) (g * g)]
  have hvol : volY y1 y2 y3 y4 y5 y6 = volY y1 y6 y5 y4 y3 y2 := by
    unfold volY volXf
    rw [hD1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)]
  have hsol : solY y1 y6 y5 y4 y3 y2 + solY y1 y3 y2 y4 y6 y5 +
      solY y4 y3 y5 y1 y6 y2 + solY y4 y6 y2 y1 y3 y5 =
    solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3 := by
    unfold solY
    rw [hdy26 y1 y6 y5 y4 y3 y2, hdy23 y6 y5 y1 y3 y2 y4, hdy23 y5 y1 y6 y2 y4 y3,
      hdy26 y1 y3 y2 y4 y6 y5, hdy23 y3 y2 y1 y6 y5 y4, hdy23 y2 y1 y3 y5 y4 y6,
      hdy23 y4 y3 y5 y1 y6 y2, hdy23 y3 y5 y4 y6 y2 y1, hdy23 y5 y4 y3 y2 y1 y6,
      hdy23 y4 y6 y2 y1 y3 y5, hdy23 y6 y2 y4 y3 y5 y1, hdy23 y2 y4 y6 y5 y1 y3]
    ring
  unfold gamma4fgcyP25 vol4fP25
  rw [hvol, hsol,
    hdy26 y1 y6 y5 y4 y3 y2,          -- edge y1 term
    hdy23 y6 y5 y1 y3 y2 y4,          -- edge y6 term
    hdy23 y4 y5 y3 y1 y2 y6,          -- edge y4 term
    hdy23 y2 y1 y3 y5 y4 y6]          -- edge y2 term
  ring

/-- HOL `gamma4fgcy_POS`. -/
theorem gamma4fgcy_POS (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hrad : rad2YP25 y1 y2 y3 y4 y5 y6 < 2) (hcey : criticalEdgeY y1)
    (hnot : ¬ (y2 < 2 * hminus ∧ y3 < 2 * hminus ∧ y4 < 2 * hminus ∧
        y5 < 2 * hminus ∧ y6 < 2 * hminus))
    (hb2 : 2 ≤ y2) (hb2' : y2 ≤ Real.sqrt 8) (hb3 : 2 ≤ y3) (hb3' : y3 ≤ Real.sqrt 8)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ Real.sqrt 8) (hb5 : 2 ≤ y5) (hb5' : y5 ≤ Real.sqrt 8)
    (hb6 : 2 ≤ y6) (hb6' : y6 ≤ Real.sqrt 8) :
    0 < gamma4fgcyP25 y1 y2 y3 y4 y5 y6 lmfun := by
  sorry

/-- HOL `real_model_gamma8`. -/
theorem real_model_gamma8 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          ¬ (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus)) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gamma8b`. -/
theorem real_model_gamma8b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) ∧
          ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus)) →
      0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_gaz9`. -/
theorem real_model_gaz9 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
          dist u0 (f (i + 1)) < 2 * hminus ∧ dist u1 (f (i + 1)) < 2 * hminus) →
      0.213849 - 0.119482 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_azim2`. -/
theorem real_model_azim2 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ((cc_4 V u0 u1 f i ∧
            ¬ (dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus ∧
                dist u0 (f (i + 1)) < 2 * hminus ∧
                dist u1 (f (i + 1)) < 2 * hminus ∧
                dist (f i) (f (i + 1)) < 2 * hminus)) ∧
          ((dist u0 (f i) < 2 * hminus ∧ dist u1 (f i) < 2 * hminus) ∧
            dist u0 (f (i + 1)) < 2 * hminus ∧
            dist u1 (f (i + 1)) < 2 * hminus) ∧
          2 * hplus < dist (f i) (f (i + 1))) →
      0.00457511 + 0.00609451 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `CC_3_SUM_SET`: the 3-cell wedge cell set splits into the two
cc-cells plus the rest. -/
theorem CC_3_SUM_SET (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} =
      insert (ccCell V [u0, u1, f i]) (insert (ccCell V [u1, u0, f (i + 1)])
        {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
          X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}) := by
  sorry

/-- HOL `CC_3_SUM_fn`: the corresponding sum split. -/
theorem CC_3_SUM_fn (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (fn : Set V3 → ℝ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))} fn =
      fn (ccCell V [u0, u1, f i]) + fn (ccCell V [u1, u0, f (i + 1)]) +
        setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
          X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
          X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]} fn := by
  sorry

/-- HOL `EDGE_IMP_K23`: every wedge cell over the stem edge is a 2- or
3-cell. -/
theorem EDGE_IMP_K23 (V : Set V3) (X : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hnc : ¬ Collinear3 u0 u1 w0) (hcey : criticalEdgeY (dist u0 u1))
    (hr : leaf_rank V [u0, u1] w0 n f) (hm : mcellSet V X)
    (he : {u0, u1} ∈ edgeX V X)
    (hX : X ⊆ wedgeGe u0 u1 (f i) (f (i + 1))) :
    ∃ k v1 v2, barV V 3 [u0, u1, v1, v2] ∧ (k = 2 ∨ k = 3) ∧
      X = mcell k V [u0, u1, v1, v2] := by
  sorry

/-- HOL `CC_2_PROPS`. -/
theorem CC_2_PROPS (V : Set V3) (X : Set V3) (u0 u1 : V3) (vl : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hcey : criticalEdgeY (dist u0 u1)) (hX : X = mcell2 V vl)
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 vl) :
    ¬ nullSet X ∧
      gammaX V X lmfun =
        gamma2_x_div_azim_v2 (h0cut (dist u0 u1)) (dist u0 u1 * dist u0 u1) *
          dihX V X (u0, u1) ∧
      0 < dihX V X (u0, u1) ∧
      0.008 * dihX V X (u0, u1) < gammaX V X lmfun := by
  sorry

/-- HOL `MCELL2_CRITICAL_WEIGHT1`. -/
theorem MCELL2_CRITICAL_WEIGHT1 (V : Set V3) (X : Set V3) (u0 u1 : V3)
    (vl : List V3) (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V)
    (hs : saturated V) (hcey : criticalEdgeY (dist u0 u1))
    (hX : X = mcell2 V vl) (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 vl) :
    criticalWeight V X = 1 := by
  sorry

/-- HOL `MCELL3_CRITICAL_WEIGHT`. -/
theorem MCELL3_CRITICAL_WEIGHT (V : Set V3) (X : Set V3) (u0 u1 v1 v2 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hcey : criticalEdgeY (dist u0 u1)) (hX : X = mcell3 V [u0, u1, v1, v2])
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 [u0, u1, v1, v2]) :
    criticalWeight V X =
      1 / (wtcount3Y (dist u0 u1) (dist u0 v1) (dist u1 v1)) := by
  sorry

/-- HOL `MCELL3_008`. -/
theorem MCELL3_008 (V : Set V3) (X : Set V3) (u0 u1 : V3) (ul : List V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hp : Packing V) (hs : saturated V)
    (hX : X = mcell3 V ul) (hcey : criticalEdgeY (dist u0 u1))
    (he : {u0, u1} ∈ edgeX V X) (hb : barV V 3 ul) :
    0.008 * dihX V X (u0, u1) ≤
      gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X := by
  sorry

/-- HOL `real_model_008`: the non-cc-cell remainder has weight ≥ `0.008`
times its dihedral. -/
theorem real_model_008 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
        X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}
        (fun X => 0.008 * dihX V X (u0, u1)) ≤
      setSum {X | mcellSet V X ∧ {u0, u1} ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 (f i) (f (i + 1)) ∧
        X ≠ ccCell V [u0, u1, f i] ∧ X ≠ ccCell V [u1, u0, f (i + 1)]}
        (fun X => gammaX V X lmfun * criticalWeight V X + betaBumpV1 V {u0, u1} X) := by
  sorry

/-- HOL `real_model_cell23`. -/
theorem real_model_cell23 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) +
          gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
            criticalWeight V (ccCell V [u1, u0, f (i + 1)]) ≤
        gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_cell23_008`. -/
theorem real_model_cell23_008 (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      (gammaX V (ccCell V [u0, u1, f i]) lmfun *
          criticalWeight V (ccCell V [u0, u1, f i]) -
          0.008 * dihX V (ccCell V [u0, u1, f i]) (u0, u1)) +
          (gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
              criticalWeight V (ccCell V [u1, u0, f (i + 1)]) -
            0.008 * dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1)) +
          0.008 * azim_mcell V f u0 u1 i ≤
        gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `GAMMAX_008a`. -/
theorem GAMMAX_008a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    0.008 * dihX V (ccCell V [u0, u1, f i]) (u0, u1) ≤
      gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i]) := by
  sorry

/-- HOL `GAMMAX_008b`. -/
theorem GAMMAX_008b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3) (i : ℕ)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f)
    (hno4 : ¬ cc_4 V u0 u1 f i) :
    0.008 * dihX V (ccCell V [u1, u0, f (i + 1)]) (u0, u1) ≤
      gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)]) := by
  sorry

/-- HOL `real_model_3a`. -/
theorem real_model_3a (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0 ≤ gammaX V (ccCell V [u0, u1, f i]) lmfun *
        criticalWeight V (ccCell V [u0, u1, f i]) := by
  sorry

/-- HOL `real_model_3b`. -/
theorem real_model_3b (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0 ≤ gammaX V (ccCell V [u1, u0, f (i + 1)]) lmfun *
        criticalWeight V (ccCell V [u1, u0, f (i + 1)]) := by
  sorry

/-- HOL `real_model_gr`. -/
theorem real_model_gr (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i →
      0.008 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `JSP_BOUNDS`. -/
theorem JSP_BOUNDS (u0 u1 u2 : V3) (hnl : pack_nonlinear_non_ox3q1h)
    (hnc : ¬ Collinear3 u0 u1 u2) (hhl : hl [u0, u1, u2] ≤ 1.34)
    (h1 : 2 * hminus ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2) :
    dist u0 u2 < 2 * hminus ∧ dist u1 u2 < 2 * hminus := by
  sorry

/-- HOL `real_model_pema`. -/
theorem real_model_pema (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ ¬ (hl [u0, u1, f (i + 1)] < 1.34) ∧
        azim_mcell V f u0 u1 i < 1.074 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_pemb`. -/
theorem real_model_pemb (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        ¬ (hl [u0, u1, f i] < 1.34) ∧ hl [u0, u1, f (i + 1)] < 1.34 ∧
        azim_mcell V f u0 u1 i < 1.074 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `c2089`: `atn (sqrt 3.07) < pi - 2.089` (needs certified interval
arithmetic; Flyspeck uses `Flyspeck_constants.calc`). -/
theorem c2089 : Real.arctan (Real.sqrt 3.07) < Real.pi - 2.089 := by
  sorry

/-- HOL `c1946`: `pi - 1.946 < atn (sqrt 6.45)` (same).  Proof sketch
(certified-interval, not yet formalized): `arctan √6.45 = π/2 - arctan z` with
`z = (√6.45)⁻¹`, `z² = 20/129 ≤ (63/160)²`; the Taylor envelope
`arctan z ≤ z·(1 - z²/3 + z⁴/5 - z⁶/7 + z⁸/9)` (pointwise
`(1+t²)(1-t²+t⁴-t⁶+t⁸) = 1+t¹⁰`) evaluates to `0.3751097… < 1.946 - π/2 ≤
1.946 - 3.1416/2 = 0.3752` (`Real.pi_lt_d4`). -/
theorem c1946 : Real.pi - 1.946 < Real.arctan (Real.sqrt 6.45) := by
  sorry
/-- HOL `IXPOTPA_MERGED`. -/
theorem IXPOTPA_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : Real.sqrt 8 ≤ y4) (hb4' : y4 ≤ y5 + y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
    (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
      gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
      (dihY y1 y2 y3 y4 y5 y6 -
          (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
            dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  sorry

/-- HOL `TXQTPVC_MERGED`. -/
theorem TXQTPVC_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ y5 + y6)
    (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hdi1 : dihY y1 y2 y3 y4 y5 y6 ≤ 2.089)
    (hdi2 : 1.946 ≤ dihY y1 y2 y3 y4 y5 y6)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    3 * 0.0057 ≤ gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
      gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
      (dihY y1 y2 y3 y4 y5 y6 -
          (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
            dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  sorry

/-- HOL `TEWNSCJ_MERGED`. -/
theorem TEWNSCJ_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : 2 ≤ y4) (hb4' : y4 ≤ Real.sqrt 8)
    (hrad : 2 ≤ rad2YP25 y1 y2 y3 y4 y5 y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (he1 : eta_y y1 y2 y6 ^ 2 ≤ 1.34 ^ 2) (he2 : eta_y y1 y3 y5 ^ 2 ≤ 1.34 ^ 2) :
    a_spine5 + b_spine5 * dihY y1 y2 y3 y4 y5 y6 ≤
      gamma3f y1 y2 y6 (Real.sqrt 2) lmfun +
        gamma3f y1 y3 y5 (Real.sqrt 2) lmfun +
        (dihY y1 y2 y3 y4 y5 y6 -
            (dihY y1 y2 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 +
              dihY y1 (Real.sqrt 2) y3 (Real.sqrt 2) y5 (Real.sqrt 2))) * 0.008 := by
  sorry

/-- HOL `CC_3_AZIM_LT_PI_COPLANAR`. -/
theorem CC_3_AZIM_LT_PI_COPLANAR (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (i : ℕ) (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hno4 : ¬ cc_4 V u0 u1 f i)
    (hr : leaf_rank V [u0, u1] w0 n f)
    (hapi : azim u0 u1 (f i) (f (i + 1)) < Real.pi) :
    ¬ Coplanar ({u0, u1, f i, f (i + 1)} : Set V3) := by
  sorry

/-- HOL `real_model_txq`. -/
theorem real_model_txq (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ hl [u0, u1, f (i + 1)] < 1.34 ∧
        1.946 ≤ azim_mcell V f u0 u1 i ∧ azim_mcell V f u0 u1 i ≤ 2.089 →
      3.0 * 0.0057 ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `real_model_tew`. -/
theorem real_model_tew (V : Set V3) (u0 u1 w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hn : 1 < n) (hp : Packing V) (hs : saturated V)
    (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V) (h1 : u1 ∈ V)
    (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    ∀ i, ¬ cc_4 V u0 u1 f i ∧
        hl [u0, u1, f i] < 1.34 ∧ hl [u0, u1, f (i + 1)] < 1.34 →
      a_spine5 + b_spine5 * azim_mcell V f u0 u1 i ≤ gg_mcell V f u0 u1 i := by
  sorry

/-- HOL `cc_real_model_data`: the geometric wedge data satisfies the full
cc_v11 real model (consumes all the `real_model_*` bank entries above). -/
theorem cc_real_model_data (V : Set V3) (f : ℕ → V3) (w0 : V3) (n : ℕ) (u0 u1 : V3)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) (hn : 1 < n) (hp : Packing V)
    (hs : saturated V) (hsize : HasSizeP25 (s_leaf V [u0, u1]) n) (h0 : u0 ∈ V)
    (h1 : u1 ∈ V) (hper : periodic f n) (hnc : ¬ Collinear3 u0 u1 w0)
    (hcey : criticalEdgeY (dist u0 u1)) (hr : leaf_rank V [u0, u1] w0 n f) :
    cc_real_model_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `CELL_CLUSTER_ESTIMATE_PROPS`: a failing cell-cluster inequality
yields the compressed-model witness. -/
theorem CELL_CLUSTER_ESTIMATE_PROPS (V : Set V3) (hp : Packing V) (hs : saturated V)
    (hcc : ¬ cellClusterInequality V) (hnl : pack_nonlinear_non_ox3q1h)
    (hox : ox3q1hP25) :
    ∃ u0 u1 n f, 1 < n ∧
      ∑ i ∈ Finset.Icc 0 (n - 1), gg_mcell V f u0 u1 i < 0 ∧
      n = cc_card_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_model_v11 (cc_data_v8 V f u0 u1) ∧
      cc_bool_prep_v11 (cc_data_v8 V f u0 u1) ∧
      cc_real_model_v11 (cc_data_v8 V f u0 u1) := by
  sorry

/-- HOL `OXLZLEZ`: THE CAPSTONE — the cell-cluster inequality, conditional
on the two certified Merge_ineq/Oxl_def banks.  Proof: a failure yields
(CELL_CLUSTER_ESTIMATE_PROPS) a compressed model with negative gg-sum;
`GRHIDFA_concl` (PackingAuto3, the OXLZLEZ1 conclusion) derives `False`.
DISCHARGES: does not verbatim-match `OXLZLEZ_concl` (PackingAuto2.lean:838)
which lacks the two bank antecedents. -/
theorem OXLZLEZ (V : Set V3) (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25)
    (hp : Packing V) (hs : saturated V) : cellClusterInequality V := by
  by_contra hcc
  obtain ⟨u0, u1, n, f, hn, hneg, hcard, hbm, hprep, hr⟩ :=
    CELL_CLUSTER_ESTIMATE_PROPS V hp hs hcc hnl hox
  have hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 (cc_data_v8 V f u0 u1) - 1),
      cc_gg_v11 (cc_data_v8 V f u0 u1) i < 0 := by
    rw [← hcard, (cc_real_data V f u0 u1).2.1]
    exact hneg
  exact GRHIDFA_concl _ hbm hprep hr hsum

/-- HOL `PACKING_CHAPTER_MAIN_CONCLUSION`: the packing chapter main
conclusion, via `RDWKARC` + `TSKAJXY`.  The HOL proof rewrites with
`Pack_concl.TSKAJXY_statement` and applies `Tskajxy.TSKAJXY`; the Lean
`TSKAJXY` (PackingAuto21:1114) has a non-matching conclusion surface, so
the assembly is left to the merge. -/
theorem PACKING_CHAPTER_MAIN_CONCLUSION (hkc : ¬ keplerConjecture)
    (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) :
    ∃ V : Set V3, Packing V ∧ V ⊆ ballAnnulus ∧ ¬ localAnnulusInequality V := by
  sorry

/-! ## Backfill: remaining source statements (kept with the file's section
order flattened; all giants) -/

/-- HOL `EDGE_LE_2RAD`. -/
theorem EDGE_LE_2RAD {x1 x2 x3 x4 x5 x6 : ℝ} (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6) (hup : 0 < upsX x4 x5 x6) :
    x4 ≤ 4 * rad2XP25 x1 x2 x3 x4 x5 x6 := by
  sorry

/-- HOL `RAD2_Y_SQRT8`. -/
theorem RAD2_Y_SQRT8 {y1 y2 y3 y5 y6 : ℝ} (h5 : 2 ≤ y5) (h6 : 2 ≤ y6)
    (h5' : y5 < 4) (h6' : y6 < 4)
    (hd : 0 < deltaY y1 y2 y3 (Real.sqrt 8) y5 y6) :
    2 ≤ rad2YP25 y1 y2 y3 (Real.sqrt 8) y5 y6 := by
  sorry

/-- HOL `DIHV_EQ_0_PI_EQ_COPLANAR_ALT`.  Proof: `dihV = 0` forces
`azim v0 v1 w1 w2 = 0` (below `pi` via AZIM_DIHV_SAME; above `pi` the
complement identity would push `azim` to `2*pi`), and an `azim`-zero pair
puts `w1` in the `affGt`-ray of `w2`, hence in `affineSpan {v0, v1, w2}` —
making the quadruple coplanar. -/
theorem DIHV_EQ_0_PI_EQ_COPLANAR_ALT (v0 v1 w1 w2 : V3)
    (hnc : ¬ Coplanar ({v0, v1, w1, w2} : Set V3)) :
    ¬ (dihV v0 v1 w1 w2 = 0) := by
  classical
  -- a point collinear with the axis already lives in the axis line
  have axisLine : ∀ x : V3, Collinear3 v0 v1 x →
      x ∈ (affineSpan ℝ ({v0, v1} : Set V3)) := by
    intro x hx
    have hv : v1 ≠ v0 := by
      intro he
      have hset : ({v0, v1, w1, w2} : Set V3) = ({v0, w1, w2} : Set V3) := by
        rw [he]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact hnc (by rw [hset]; exact coplanar_triple v0 w1 w2)
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := v0) (w := v1) (w1 := x) hv).mp hx
    have hmem := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ) (p₁ := v0) (p₂ := v1) (r := c)
    have heq : (c • (v1 -ᵥ v0) +ᵥ v0 : V3) = x := by
      rw [vadd_eq_add, vsub_eq_sub, ← hc]; abel
    rwa [heq] at hmem
  -- a plane spanned by the axis and either point contains the whole quadruple
  have copPlane : ∀ x y : V3, Collinear3 v0 v1 x →
      Coplanar ({v0, v1, x, y} : Set V3) := by
    intro x y hx
    refine ⟨v0, v1, y, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpe | hpe | hpe | hpe
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]
      exact SetLike.le_def.mp (affineSpan_mono ℝ (by
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto))
        (axisLine x hx)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
  have h1 : ¬ Collinear3 v0 v1 w1 := fun hc => hnc (copPlane w1 w2 hc)
  have h2 : ¬ Collinear3 v0 v1 w2 := by
    intro hc
    have hset : ({v0, v1, w1, w2} : Set V3) = ({v0, v1, w2, w1} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact hnc (by rw [hset]; exact copPlane w2 w1 hc)
  intro hdih
  rcases lt_or_ge (azim v0 v1 w1 w2) Real.pi with hlt | hge
  · have hazi : azim v0 v1 w1 w2 = 0 := by
      rw [azim_dihv_same h1 h2 hlt]; exact hdih
    have hw1gt : w1 ∈ affGt ({v0, v1} : Set V3) {w2} := (azim_eq_zero_iff h1 h2).mp hazi
    have hwv : v0 ≠ v1 := fun he => h1 (collinear3_of_eq he.symm)
    have hw20 : w2 ≠ v0 := fun he => h2 (collinear3_pair_left he)
    have hw21 : w2 ≠ v1 := fun he => h2 (collinear3_pair_right he)
    obtain ⟨c, -, h, hcomb⟩ :=
      (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w2) (y := w1) hwv hw20 hw21) |>.mp hw1gt
    refine hnc ⟨v0, v1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpe | hpe | hpe | hpe
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
    · rw [hpe]
      have hw2mem : w2 ∈ (affineSpan ℝ ({v0, v1, w2} : Set V3)) :=
        mem_affineSpan (k := ℝ) (by simp : w2 ∈ ({v0, v1, w2} : Set V3))
      have hw1eq : (w1 - w2 : V3) = (1 - c - h) • (v0 - w2) + h • (v1 - w2) := by
        rw [show (w1 : V3) = v0 + (w1 - v0) from by abel, hcomb]; module
      have hvv : (w1 - w2 : V3) ∈ vectorSpan ℝ ({v0, v1, w2} : Set V3) := by
        rw [hw1eq, vectorSpan_eq_span_vsub_set_right ℝ (show w2 ∈ ({v0, v1, w2} : Set V3) from
          by simp)]
        have himg1 : (v0 -ᵥ w2 : V3) ∈
            (fun x : V3 => x -ᵥ w2) '' ({v0, v1, w2} : Set V3) := ⟨v0, by simp, rfl⟩
        have himg2 : (v1 -ᵥ w2 : V3) ∈
            (fun x : V3 => x -ᵥ w2) '' ({v0, v1, w2} : Set V3) := ⟨v1, by simp, rfl⟩
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span himg1))
          (Submodule.smul_mem _ _ (Submodule.subset_span himg2))
      have hres := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hw2mem hvv
      rwa [vadd_eq_add, sub_add_cancel] at hres
    · rw [hpe]; exact mem_affineSpan ℝ (by simp)
  · have hazi := azim_dihv_compl h1 h2 hge
    rw [hdih] at hazi
    have h2pi := azim_lt_two_pi v0 v1 w1 w2
    linarith

/-- HOL `AZIM_ZERO_SHIFT`: two leaves subtend the same azimuth from `u2`
exactly when they lie on the same ray from the stem axis.  Both iff sides
chain through `w' ∈ affGt {u0, u1} {w}` (AZIM_EQ_AZIM ↔ AZIM_EQ_0_ALT). -/
theorem AZIM_ZERO_SHIFT (u0 u1 u2 w w' : V3)
    (h1 : ¬ Collinear3 u0 u1 u2) (h2 : ¬ Collinear3 u0 u1 w)
    (h3 : ¬ Collinear3 u0 u1 w') :
    (azim u0 u1 u2 w = azim u0 u1 u2 w' ↔ azim u0 u1 w w' = 0) :=
  (azim_eq_azim_iff h1 h2 h3).trans (azim_eq_zero_iff_alt h2 h3).symm

/-- HOL `ORDER_AZIM_SUM2Pi0`: the azim-sorted leaf walk winds once. -/
theorem ORDER_AZIM_SUM2Pi0 (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ∀ i, i < n → ¬ Collinear3 x y (g i))
    (h3 : g n = g 0) (hn : 1 < n)
    (h4 : ∀ j k, j < n → k < n → j < k → azim x y z (g j) < azim x y z (g k)) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim x y (g i) (g (i + 1)) = 2 * Real.pi := by
  sorry

private theorem p25_take_append_cancel {α : Type*} {l1 l2 : List α} (n : ℕ)
    (h : n ≤ l1.length) : (l1 ++ l2).take n = l1.take n := by
  induction l1 generalizing n with
  | nil => simp at h; simp [h]
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ n =>
      have key : (t ++ l2).take n = t.take n := ih n (Nat.le_of_succ_le_succ h)
      simp [key]

/-- HOL `INITIAL_SUBLIST_TRUNCATE`. -/
theorem INITIAL_SUBLIST_TRUNCATE (vl ul : List V3) (hl : ul.length = 4)
    (h1 : initialSublist vl ul)
    (h2 : ¬ initialSublist vl (truncateSimplex 2 ul)) : vl = ul := by
  obtain ⟨htrlen, htrsub⟩ := Classical.epsilon_spec (p := fun t : List V3 =>
      t.length = 3 ∧ initialSublist t ul)
      ⟨ul.take 3, by simp [hl], ⟨ul.drop 3, (List.take_append_drop 3 ul).symm⟩⟩
  obtain ⟨zl, hzl⟩ := htrsub
  obtain ⟨yl, hyl⟩ := h1
  have hlen : vl.length + yl.length = 4 := by rw [← hl, hyl, List.length_append]
  by_cases hk : 4 ≤ vl.length
  · have hy0 : yl.length = 0 := by omega
    have hye : yl = [] := by
      cases yl with
      | nil => rfl
      | cons a t => simp at hy0
    rw [hye, List.append_nil] at hyl
    exact hyl.symm
  · exfalso
    apply h2
    have e1 : vl = ul.take vl.length := by
      rw [hyl, p25_take_append_cancel vl.length (Nat.le_refl vl.length), List.take_length]
    have e2 : ul.take vl.length = (truncateSimplex 2 ul).take vl.length := by
      conv_lhs => rw [hzl]
      exact p25_take_append_cancel vl.length (by rw [htrlen]; omega)
    have e3 : initialSublist vl (truncateSimplex 2 ul) := by
      rw [e1, e2]
      exact ⟨(truncateSimplex 2 ul).drop vl.length,
        (List.take_append_drop vl.length (truncateSimplex 2 ul)).symm⟩
    exact absurd e3 h2

/-- HOL `NOT_COPLANAR_AFF_3`. -/
theorem NOT_COPLANAR_AFF_3 (s : Set V3) (hnc : ¬ Coplanar s) :
    affDim s = 3 := by
  sorry

/-- HOL `AFF_DEP_COPLANAR`. -/
theorem AFF_DEP_COPLANAR (a b c d : V3)
    (hc : Set.ncard ({a, b, c, d} : Set V3) = 4) :
    (affineDependent ({a, b, c, d} : Set V3) ↔ Coplanar ({a, b, c, d} : Set V3)) := by
  sorry

/-- HOL `HL_IMP_BARV`. -/
theorem HL_IMP_BARV (V : Set V3) (ul : List V3) (hp : Packing V) (hs : saturated V)
    (hnc : ¬ Coplanar (setOfList ul)) (hsub : setOfList ul ⊆ V)
    (hhl : hl ul < Real.sqrt 2) (hb : barV V 2 (truncateSimplex 2 ul))
    (hlen : ul.length = 4) : barV V 3 ul := by
  sorry

end Kepler.Text
