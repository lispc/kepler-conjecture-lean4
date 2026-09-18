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
  - real toolkit: `dih_x/dih_y/eta_y/gamma3f/delta_x/h0cut` <-> PackingAuto21
    (`dihXf/dihY/eta_y/gamma3f/deltaXf/h0cut`).  `gamma4fgcy` lives only in
    PackingAuto20, whose olean would make `dihY`/`gamma3f` ambiguous here
    (both files re-declare the hub kit), so this file does NOT import 20 and
    carries verbatim `_p25` copies of `vol4f`/`gamma4fgcy` (delete at merge).
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

/-- HOL `delta_y` (sphere.hl): `y_of_x delta_x` = `deltaXf` at squared
lengths (same `y_of_x` pattern as rad2_y, TSKAJXY2.hl:457). -/
noncomputable def deltaYP25 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

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

/-! ## Leaf-cell kit (`_p25` copies from PackingAuto18.lean; the two lanes
`PackingAuto18` and `PackingAuto21` both declare `MCELL2_SUBSET_AFF_GE` and
`atn2`, so only one is importable here — we keep 21 for the certified
nonlinear bank + real toolkit.  Delete this section at merge.) -/

/-- HOL `leaf` (leaf_cell.hl:17); PackingAuto18.lean:73 verbatim. -/
def leaf (V : Set V3) (ul : List V3) : Prop := barV V 2 ul ∧ hl ul < Real.sqrt 2

/-- HOL `chi_msb` (leaf_cell.hl:781-782); PackingAuto18.lean:91 verbatim. -/
noncomputable def chiMsb (ul : List V3) (p : V3) : ℝ :=
  (crossProduct ((ul[1]! - ul[0]! : V3) : Fin 3 → ℝ)
      ((ul[2]! - ul[0]! : V3) : Fin 3 → ℝ)) ⬝ᵥ ((p - ul[0]! : V3) : Fin 3 → ℝ)

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

/-- HOL `ups_x` (sphere.hl:122-124); PackingAuto18.lean:149 verbatim. -/
def upsX (x1 x2 x6 : ℝ) : ℝ :=
  -(x1 * x1) - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

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
  sorry

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
  sorry

/-- HOL `BARV3_SET_OF_LIST4`. -/
theorem BARV3_SET_OF_LIST4 (V : Set V3) (ul : List V3) (hp : Packing V)
    (hb : barV V 3 ul) :
    setOfList ul = {elV ul 0, elV ul 1, elV ul 2, elV ul 3} := by
  sorry

/-- HOL `STRICT_SORT_FINITE`: a finite set with an asymmetric transitive
`<<` can be enumerated by `1..n` in `<<`-increasing order. -/
theorem STRICT_SORT_FINITE {α : Type*} {lt : α → α → Prop} (s : Set α) (n : ℕ)
    (_hirr : ∀ x y, x ∈ s → y ∈ s → lt x y → lt y x → x = y)
    (_htr : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → lt x y → lt y z → lt x z)
    (_hs : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → α, s = f '' Set.Icc 1 n ∧
      ∀ j k, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k → ¬lt (f k) (f j) := by
  sorry

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

/-- HOL `NULLSET_AFF_2_1`. -/
theorem NULLSET_AFF_2_1 (x y z : V3) : nullSet (affGe {x, y} {z}) := by
  sorry

/-- HOL `coplanar_delta_y` (renamed from coplanar_dih_y). -/
theorem coplanar_delta_y (u0 u1 u2 u3 : V3) :
    ¬ Coplanar ({u0, u1, u2, u3} : Set V3) ↔
      0 < deltaYP25 (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
        (dist u1 u3) (dist u1 u2) := by
  sorry

/-- HOL `RADV_ETAY`. -/
theorem RADV_ETAY (u0 u1 u2 : V3) (hnc : ¬ Collinear3 u0 u1 u2) :
    radV {u0, u1, u2} = eta_y (dist u0 u1) (dist u0 u2) (dist u1 u2) := by
  sorry

/-- HOL `RADV2`. -/
theorem RADV2 (u v : V3) : radV {u, v} = (1 / 2 : ℝ) * dist u v := by
  sorry

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
  sorry

/-- HOL `UPS_X8_POS` (needs certified interval bounds). -/
theorem UPS_X8_POS {y5 y6 : ℝ} (h5 : 2 ≤ y5) (h5' : y5 < 4) (h6 : 2 ≤ y6)
    (h6' : y6 < 4) : 0 < upsX 8 (y5 * y5) (y6 * y6) := by
  sorry

/-- HOL `DIST_IMP_UPS_X_POS`. -/
theorem DIST_IMP_UPS_X_POS (u0 u1 u2 : V3)
    (h1 : 2 ≤ dist u0 u1) (h2 : 2 ≤ dist u0 u2) (h3 : 2 ≤ dist u1 u2)
    (h4 : dist u0 u1 < 4) (h5 : dist u0 u2 < 4) (h6 : dist u1 u2 < 4) :
    0 < upsX (dist u0 u1 ^ 2) (dist u0 u2 ^ 2) (dist u1 u2 ^ 2) := by
  sorry

/-- HOL `dih_x < pi`: the angle computed by `atn2` from a positive first
argument stays below `pi/2` in every quadrant branch. -/
theorem DIH_X_LT_PI {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaXf x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 < Real.pi := by
  unfold dihXf
  have hx : 0 < Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith) hd)
  have harg : atn2 (Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6))
      (-(deltaX4f x1 x2 x3 x4 x5 x6)) < Real.pi / 2 := by
    unfold atn2
    split_ifs with hb hb2 hb3
    · have hfrac : -(deltaX4f x1 x2 x3 x4 x5 x6) /
          Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6) < 1 := by
        rw [div_lt_one hx]
        have habs := abs_lt.mp hb
        linarith
      exact Real.arctan_lt_pi_div_two _
    · have hpos : 0 < Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6) /
            -(deltaX4f x1 x2 x3 x4 x5 x6) := div_pos hx hb2
      have hap := Real.arctan_pos.mpr hpos
      linarith
    · exact by
        have hge := Real.neg_pi_div_two_lt_arctan
          (Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6) /
            -(deltaX4f x1 x2 x3 x4 x5 x6))
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
    · exact absurd hx (by
        have hy : -(deltaX4f x1 x2 x3 x4 x5 x6) = 0 := by linarith
        rw [hy] at hb
        simp at hb
        have hle : Real.sqrt (4 * x1 * deltaXf x1 x2 x3 x4 x5 x6) = 0 :=
          Real.sqrt_eq_zero_of_nonpos hb
        linarith)
  linarith

/-- HOL `DIH_Y_LT_PI`. -/
theorem DIH_Y_LT_PI {y1 y2 y3 y4 y5 y6 : ℝ} (h1 : 0 < y1)
    (hd : 0 < deltaYP25 y1 y2 y3 y4 y5 y6) :
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
  sorry

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

/-- HOL `LEAF_RANK_HAS_SIZE`. -/
theorem LEAF_RANK_HAS_SIZE (V : Set V3) (ul : List V3) (w0 : V3) (n : ℕ) (f : ℕ → V3)
    (hn : n ≠ 0) (hp : Packing V) (hs : saturated V) (hr : leaf_rank V ul w0 n f)
    (hnc : ¬ Collinear3 (elV ul 0) (elV ul 1) w0) :
    HasSizeP25 (s_leaf V ul) n := by
  sorry

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
      0 < deltaYP25 y1 y2 y3 y4 y5 y6 ∧
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
  sorry

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
  sorry

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
  sorry

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
      0 < deltaYP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1)))
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
        0 < deltaYP25 (dist u0 u1) (dist u0 (f i)) (dist u0 (f (i + 1))) y4
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

/-- HOL `gamma4fgcy_sym26`. -/
theorem gamma4fgcy_sym26 (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) :
    gamma4fgcyP25 y1 y2 y3 y4 y5 y6 f = gamma4fgcyP25 y1 y6 y5 y4 y3 y2 f := by
  sorry

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

/-- HOL `c1946`: `pi - 1.946 < atn (sqrt 6.45)` (same). -/
theorem c1946 : Real.pi - 1.946 < Real.arctan (Real.sqrt 6.45) := by
  sorry

/-- HOL `IXPOTPA_MERGED`. -/
theorem IXPOTPA_MERGED (y1 y2 y3 y4 y5 y6 : ℝ) (hnl : pack_nonlinear_non_ox3q1h)
    (hcey : criticalEdgeY y1) (hb2 : 2 ≤ y2) (hb2' : y2 ≤ 2 * hminus)
    (hb3 : 2 ≤ y3) (hb3' : y3 ≤ 2 * hminus)
    (hb4 : Real.sqrt 8 ≤ y4) (hb4' : y4 ≤ y5 + y6)
    (hb5 : 2 ≤ y5) (hb5' : y5 ≤ 2 * hminus) (hb6 : 2 ≤ y6) (hb6' : y6 ≤ 2 * hminus)
    (hd : 0 < deltaYP25 y1 y2 y3 y4 y5 y6)
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
    (hd : 0 < deltaYP25 y1 y2 y3 y4 y5 y6)
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
theorem EDGE_LE_2RAD {x1 x2 x3 x4 x5 x6 : ℝ} (hd : 0 < deltaXf x1 x2 x3 x4 x5 x6)
    (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6) (hup : 0 < upsX x4 x5 x6) :
    x4 ≤ 4 * rad2XP25 x1 x2 x3 x4 x5 x6 := by
  sorry

/-- HOL `RAD2_Y_SQRT8`. -/
theorem RAD2_Y_SQRT8 {y1 y2 y3 y5 y6 : ℝ} (h5 : 2 ≤ y5) (h6 : 2 ≤ y6)
    (h5' : y5 < 4) (h6' : y6 < 4)
    (hd : 0 < deltaYP25 y1 y2 y3 (Real.sqrt 8) y5 y6) :
    2 ≤ rad2YP25 y1 y2 y3 (Real.sqrt 8) y5 y6 := by
  sorry

/-- HOL `DIHV_EQ_0_PI_EQ_COPLANAR_ALT`. -/
theorem DIHV_EQ_0_PI_EQ_COPLANAR_ALT (v0 v1 w1 w2 : V3)
    (hnc : ¬ Coplanar ({v0, v1, w1, w2} : Set V3)) :
    ¬ (dihV v0 v1 w1 w2 = 0) := by
  sorry

/-- HOL `AZIM_ZERO_SHIFT`. -/
theorem AZIM_ZERO_SHIFT (u0 u1 u2 w w' : V3)
    (h1 : ¬ Collinear3 u0 u1 u2) (h2 : ¬ Collinear3 u0 u1 w)
    (h3 : ¬ Collinear3 u0 u1 w') :
    (azim u0 u1 u2 w = azim u0 u1 u2 w' ↔ azim u0 u1 w w' = 0) := by
  sorry

/-- HOL `ORDER_AZIM_SUM2Pi0`: the azim-sorted leaf walk winds once. -/
theorem ORDER_AZIM_SUM2Pi0 (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ∀ i, i < n → ¬ Collinear3 x y (g i))
    (h3 : g n = g 0) (hn : 1 < n)
    (h4 : ∀ j k, j < n → k < n → j < k → azim x y z (g j) < azim x y z (g k)) :
    ∑ i ∈ Finset.Icc 0 (n - 1), azim x y (g i) (g (i + 1)) = 2 * Real.pi := by
  sorry

/-- HOL `INITIAL_SUBLIST_TRUNCATE`. -/
theorem INITIAL_SUBLIST_TRUNCATE (vl ul : List V3) (hl : ul.length = 4)
    (h1 : initialSublist vl ul)
    (h2 : ¬ initialSublist vl (truncateSimplex 2 ul)) : vl = ul := by
  sorry

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
