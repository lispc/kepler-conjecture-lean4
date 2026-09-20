/-
LocalAuto35 — Local Fan chapter appendix leftovers, single-file lane 35:

  - `scripts/local/QKNVMLB.hl` (10699 ln, 0 defs + 53 thms; H. L. Truong /
    T. Hales 2012, "remaining conclusions from appendix to Local Fan
    chapter") — the ear/diagonal combinatorics: cutting a conforming
    `scs_v39` system along a diagonal `scs_diag k p q` with the half-slice
    constructor `scs_half_slice_v39`, the propagation kit
    (`SCS_K_PRIME_CASE_3/4/5/6`, `SCS_K_PRIME_LE_GE`), the
    `is_scs`/`BBs`/`MMs` preservation of the slices
    (`SCS_HALF_SLICE_IS_SCS(_4)(_PRIME)`, `SCS_HALF_SLICE_IS_A_SCS`,
    `QKNVMLB1*`), the graph re-labelling kit (`VV_INJ`, `CARD_V_EQ_SCS_K`,
    `V/E/F_PRIME_EQ_V/E/F_vv`, `VV_SUC_EQ_RHO_NODE(_PRIME)`), the taustar
    superadditivity chain (`QKNVMLB2`, `QKNVMLB3_LE4`, `QKNVMLB3_Eq4`,
    `QKNVMLB3`) and the sum-azim identities (`SUM_AZIM_EQ_ANGLE_LE4/eq4`),
    plus the small mod-arithmetic bank (`MOD_EQ_IMP_MOD_EQ_0`,
    `SUC_MOD_NOT_EQ`, `DIAGE_VAL_P_Q`, `SUM_NUMSEG2/3`, `NUMSEG_2/3`).

FILE MAP (source order kept; every name `_p35`-suffixed; this file adds
  no definitions — the whole `scs_v39` toolkit is in LocalAuto1)
  - Mod/diag arithmetic: `MOD_EQ_IMP_MOD_EQ_0_p35`, `SCS_K_PRIME_CASE_4_p35`,
    `SCS_K_PRIME_CASE_5_p35`, `SCS_K_PRIME_CASE_6_p35`,
    `SCS_K_PRIME_CASE_3_p35`, `SCS_K_PRIME_LE_GE_p35`.
  - Slice `is_scs` propagation: `SCS_HALF_SLICE_IS_SCS_p35`,
    `SCS_HALF_SLICE_IS_SCS_4_p35`, `IS_EAR_IS_SCS_p35`,
    `SCS_HALF_SLICE_IS_SCS_4_PRIME_p35`, `SCS_HALF_SLICE_IS_SCS_PRIME_p35`,
    `SCS_HALF_SLICE_IS_A_SCS_p35`.
  - Diag-vs-edge/ear kit: `NOT_EQ_DIAG_p35`, `IN_IMAGE_VV_p35`,
    `SUC_MOD_NOT_EQ_p35`, `IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35`,
    `DIAG_NOT_IN_EDGES_p35`, `SCS_K_LE_6_p35`, `TECOXBMv2_p35`.
  - Graph re-labelling: `VV_SUC_EQ_RHO_NODE_p35`, `W_EW_K_SCS_ADD_P_p35`,
    `VV_INJ_p35`, `CARD_V_EQ_SCS_K_p35`, `V_PRIME_EQ_V_vv_p35`,
    `E_PRIME_EQ_E_vv_p35`, `F_PRIME_EQ_F_vv_p35`.
  - BBs/taustar transport: `QKNVMLB1_LE4F_p35`, `QKNVMLB1_EQ4F_p35`,
    `QKNVMLB1_p35`, `DIAG_IS_NOT_EAR_p35`, `SCS_J_DIAG_EQ_p35`,
    `DIAG_NOT_IN_SCS_J_p35`, `SCS_J_PRIME_SUBSET_SCS_J_p35`,
    `INTER_SLICE_SCS_EMPTY1_p35`, `INTER_SLICE_SCS_EMPTY_p35`,
    `QKNVMLB2_p35`, `DIST_DIAG_LE_CSTAB_p35`,
    `VV_SUC_EQ_RHO_NODE_PRIME_p35`, `SUM_AZIM_EQ_ANGLE_LE4_p35`,
    `V_SLICE_EQ_NUMSEG_p35`, `SCS_SLICE_SYM_p35`.
  - Small sum/numseg bank: `SUM_NUMSEG2_p35`, `NUMSEG_2_p35`,
    `SUM_NUMSEG3_p35`, `NUMSEG_3_p35`.
  - Slice tau bank (k' = 3 and general): `SUM_AZIM_EQ_ANGLE_EQ4_p35`,
    `CARD_FF_EQ_CARD_SLICE_FF_p35`, `CARD_SLICE_FF_LE_3_p35`,
    `CARD_FF_EQ_SCS_K_3_p35`, `QKNVMLB3_LE4_p35`, `DIAGE_VAL_P_Q_p35`,
    `QKNVMLB3_Eq4_p35`, `QKNVMLB3_p35`.

Encoding:
- All toolkit defs (`is_scs_v39`, `scs_diag`, `scs_half_slice_v39`,
  `scs_slice_v39`/`is_scs_slice_v39`, `BBs_v39`, `MMs_v39`, `is_ear_v39`,
  `dsv_v39`, `taustar_v39`, `cstab`, `rho_fun`, `rho_node1`,
  `interior_angle1`, `azim_in_fan`, `tau3`, `Periodic`) are ALREADY ported
  in `Kepler.Text.LocalAuto1` (camelCase: `isScsV39` with field accessors
  `s.k`/`s.d`/`s.a`/`s.bm`/`s.b`/`s.J` for the HOL `scs_*_v39` selectors).
- `v_prime`/`e_prime` ↦ `vPrime_p3`/`ePrime_p3`, `wedge_in_fan_gt` ↦
  `wedgeInFanGt_p3`, `hypermap (HYP (vec 0,V,E'))` ↦ carrier
  `HS : Hypermap (V3 × V3)` with the `IsHypE_p35` predicate (the LocalAuto2
  `IsHyp_p2` pattern over the LocalAuto3 `_p3` HYP pieces; NOTE: LocalAuto2
  itself is NOT importable from this lane — the LocalAuto1 + LocalAuto2
  import pair clashes on a duplicate `atn2PA18` via PackingAuto18/PackingAuto20);
  HOL `face` ↦ `Hypermap.face`; `convex_local_fan` ↦ `ConvexLocalFan`
  (LocalAuto1); `sol0`/`setSum` ↦ PackingAuto2.
- HOL `x MOD k` ↦ `x % k`; `SUC i` ↦ `i + 1`; `IMAGE vv (:num)` ↦
  `Set.range vv`; `{:num}` ↦ `(Set.univ : Set ℕ)`; `ITER n f x` ↦ `f^[n] x`;
  `CARD` ↦ `Set.ncard`; `#0.9` ↦ `0.9`; `&4` ↦ `(4 : ℝ)`.
- The tactic-lets `LEMMA_TAC` and the thrice-rebound `CASE_DIAGONAL_MOD`
  (QKNVMLB.hl:247/102/145/196; `fun (so,so1,so2) -> ...` mod-4/5/6
  instantiations of `IMP_SUC_MOD_EQ`) are proof-script plumbing, NOT
  theorems — skipped; `check_completeness_claimA_concl` (:10693) sits
  inside a trailing `(* ... *)` comment in the source — skipped.
- DISCHARGES convention: `sorry` bodies carry a `-- DISCHARGES:` marker
  naming the blocking item; mechanical proofs are discharged here.
- Fill-wave 2026-09-19 re-scan (22 sorries, no fills): the external
  blockers are still open — `XWNHLMD_MM_p26` still `sorry`
  (LocalAuto26:688; twin `XWNHLMD_MM_p33` LocalAuto33:127 also `sorry`),
  and no proved corpus twins exist for the giants (`SUM_AZIM_EQ_ANGLE_
  LE4_FUN_p18` LocalAuto18:970 `sorry`; `TECOXBM` only as the
  `Fin k`-matrix variant LocalAuto11:1105; `QKNVMLB1/2/3_concl` LocalAuto1:1664-1683
  all `sorry`). The four `SCS_HALF_SLICE_IS_SCS*` field-by-field
  verifications, the `V/E/F_PRIME` re-labelling trio, `TECOXBMv2_p35`,
  the `VV_SUC` orbit pair, and the `QKNVMLB` taustar bank remain
  self-contained giants for a dedicated wave.
-/

import Kepler.Text.Polytope
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto23
import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- The `hypermap (HYP (vec 0, V, E'))` carrier predicate: the LocalAuto2
`IsHyp_p2` pattern rendered over the LocalAuto3 `_p3` HYP pieces (LocalAuto2
is not importable here — see encoding notes). `E'` is the edge set of the
hypermap (`E UNION {{u, w}}` at the call sites). -/
def IsHypE_p35 (V : Set V3) (E : Set (Set V3)) (HS : Hypermap (V3 × V3)) : Prop :=
  (↑HS.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
    (HS.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V E ∧
    (HS.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V E ∧
    (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V E

/-! ## Mod-arithmetic and the `scs_k` case bank -/

/-- HOL `MOD_EQ_IMP_MOD_EQ_0` (QKNVMLB.hl:70). -/
theorem MOD_EQ_IMP_MOD_EQ_0_p35 {k p q : ℕ} (hk : k ≠ 0) (hmod : p % k = q % k)
    (hle : q ≤ p) : (p - q) % k = 0 := by
  have hp : p = q + (p - q) := by omega
  have h1 : (q % k + (p - q) % k) % k = q % k := by
    rw [hp, Nat.add_mod] at hmod
    exact hmod
  have htk : q % k < k := Nat.mod_lt _ (by omega)
  have hsk : (p - q) % k < k := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge (q % k + (p - q) % k) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1
    omega
  · have h2 : q % k + (p - q) % k = (q % k + (p - q) % k - k) + k * 1 := by omega
    rw [h2, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show q % k + (p - q) % k - k < k by omega)] at h1
    omega

/-- HOL `SCS_K_PRIME_CASE_4` (QKNVMLB.hl:96): cutting a k = 4 system along
a diagonal leaves a k' = 3 half slice. -/
theorem SCS_K_PRIME_CASE_4_p35 (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj) (hscs : isScsV39 s)
    (hk : s.k = 4) (hdiag : scsDiag s.k p q) : s'.k = 3 := by
  rw [hs']
  simp only [scsHalfSliceV39]
  rw [hk]
  rw [hk] at hdiag
  obtain ⟨h1, h2, h3⟩ := hdiag
  have e1 : (p + 1) % 4 = (p % 4 + 1) % 4 := by simp [Nat.add_mod]
  have e2 : (q + 1) % 4 = (q % 4 + 1) % 4 := by simp [Nat.add_mod]
  rw [e1] at h2
  rw [e2] at h3
  have hb1 : p % 4 < 4 := Nat.mod_lt _ (by omega)
  have hb2 : q % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases p % 4 <;> interval_cases q % 4 <;> omega

/-- HOL `SCS_K_PRIME_CASE_5` (QKNVMLB.hl:138). -/
theorem SCS_K_PRIME_CASE_5_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
    (hk : s.k = 5) (hdiag : scsDiag s.k p q) :
    (s'.k = 3 ∧ s''.k = 4) ∨ (s'.k = 4 ∧ s''.k = 3) := by
  rw [hs', hs'']
  simp only [scsHalfSliceV39]
  rw [hk]
  rw [hk] at hdiag
  obtain ⟨h1, h2, h3⟩ := hdiag
  have e1 : (p + 1) % 5 = (p % 5 + 1) % 5 := by simp [Nat.add_mod]
  have e2 : (q + 1) % 5 = (q % 5 + 1) % 5 := by simp [Nat.add_mod]
  rw [e1] at h2
  rw [e2] at h3
  have hb1 : p % 5 < 5 := Nat.mod_lt _ (by omega)
  have hb2 : q % 5 < 5 := Nat.mod_lt _ (by omega)
  interval_cases p % 5 <;> interval_cases q % 5 <;> omega

/-- HOL `SCS_K_PRIME_CASE_6` (QKNVMLB.hl:189). -/
theorem SCS_K_PRIME_CASE_6_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
    (hk : s.k = 6) (hdiag : scsDiag s.k p q) :
    (s'.k = 3 ∧ s''.k = 5) ∨ (s'.k = 5 ∧ s''.k = 3) ∨ (s'.k = 4 ∧ s''.k = 4) := by
  rw [hs', hs'']
  simp only [scsHalfSliceV39]
  rw [hk]
  rw [hk] at hdiag
  obtain ⟨h1, h2, h3⟩ := hdiag
  have e1 : (p + 1) % 6 = (p % 6 + 1) % 6 := by simp [Nat.add_mod]
  have e2 : (q + 1) % 6 = (q % 6 + 1) % 6 := by simp [Nat.add_mod]
  rw [e1] at h2
  rw [e2] at h3
  have hb1 : p % 6 < 6 := Nat.mod_lt _ (by omega)
  have hb2 : q % 6 < 6 := Nat.mod_lt _ (by omega)
  interval_cases p % 6 <;> interval_cases q % 6 <;> omega

/-- HOL `SCS_K_PRIME_CASE_3` (QKNVMLB.hl:245): a diagonal of a conforming
system forces `3 < k` (so `k = 3` systems have no diagonals). -/
theorem SCS_K_PRIME_CASE_3_p35 (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : 3 < s.k := by
  have hk1 : 3 ≤ s.k := hscs.2.1
  by_contra h
  have h3 : s.k = 3 := by omega
  rw [h3] at hdiag
  obtain ⟨h1, h2, h3'⟩ := hdiag
  have e1 : (p + 1) % 3 = (p % 3 + 1) % 3 := by simp [Nat.add_mod]
  have e2 : (q + 1) % 3 = (q % 3 + 1) % 3 := by simp [Nat.add_mod]
  rw [e1] at h2
  rw [e2] at h3'
  have hb1 : p % 3 < 3 := Nat.mod_lt _ (by omega)
  have hb2 : q % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases p % 3 <;> interval_cases q % 3 <;> omega

/-- HOL `SCS_K_PRIME_LE_GE` (QKNVMLB.hl:272). -/
theorem SCS_K_PRIME_LE_GE_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (s' : ScsV39)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj) :
    3 ≤ s'.k ∧ s'.k ≤ 6 ∧ s'.k < s.k := by
  have hk3 := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hk6 : s.k ≤ 6 := hscs.2.2.1
  rw [hs']
  simp only [scsHalfSliceV39]
  have hbP : p % s.k < s.k := Nat.mod_lt _ (by have := hscs.2.1; omega)
  have hbQ : q % s.k < s.k := Nat.mod_lt _ (by have := hscs.2.1; omega)
  rcases (by have := hscs.2.1; have := hscs.2.2.1; omega : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with h | h | h
  · rw [h] at hdiag hbP hbQ ⊢
    obtain ⟨h1, h2, h3⟩ := hdiag
    have e1 : (p + 1) % 4 = (p % 4 + 1) % 4 := by simp [Nat.add_mod]
    have e2 : (q + 1) % 4 = (q % 4 + 1) % 4 := by simp [Nat.add_mod]
    rw [e1] at h2
    rw [e2] at h3
    interval_cases p % 4 <;> interval_cases q % 4 <;> omega
  · rw [h] at hdiag hbP hbQ ⊢
    obtain ⟨h1, h2, h3⟩ := hdiag
    have e1 : (p + 1) % 5 = (p % 5 + 1) % 5 := by simp [Nat.add_mod]
    have e2 : (q + 1) % 5 = (q % 5 + 1) % 5 := by simp [Nat.add_mod]
    rw [e1] at h2
    rw [e2] at h3
    interval_cases p % 5 <;> interval_cases q % 5 <;> omega
  · rw [h] at hdiag hbP hbQ ⊢
    obtain ⟨h1, h2, h3⟩ := hdiag
    have e1 : (p + 1) % 6 = (p % 6 + 1) % 6 := by simp [Nat.add_mod]
    have e2 : (q + 1) % 6 = (q % 6 + 1) % 6 := by simp [Nat.add_mod]
    rw [e1] at h2
    rw [e2] at h3
    interval_cases p % 6 <;> interval_cases q % 6 <;> omega

/-! ## Slice `is_scs` propagation (source order: 305-3398) -/

/-- HOL `SCS_HALF_SLICE_IS_SCS` (QKNVMLB.hl:305, proof ~830 ln). -/
theorem SCS_HALF_SLICE_IS_SCS_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hmj : s'.J 0 (s'.k - 1) = mkj)
    (hmj' : ¬s'.J 0 (s'.k - 1))
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (hbm : s.bm p q < 4) (hcstab : 4 < s.k → s.bm p q ≤ cstab) :
    isScsV39 s' := by
  sorry
  -- DISCHARGES: field-by-field `isScsV39` verification of the half slice
  -- (source 305-1134): Periodic/Periodic2 transport through the `mod2`
  -- re-indexing of `scsHalfSliceV39`, the `a1`/`b1` diagonal override
  -- `{0, k'-1}` cases and the `scsM`-cardinality drop; needs the
  -- CASE_4/5/6 `k'`-calculus and the slice BBprime minimality lemmas.

/-- HOL `SCS_HALF_SLICE_IS_SCS_4` (QKNVMLB.hl:1134, proof ~620 ln). -/
theorem SCS_HALF_SLICE_IS_SCS_4_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hmj : s'.J 0 (s'.k - 1) = mkj)
    (hmj' : ¬s'.J 0 (s'.k - 1))
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (hbm : s.bm p q < 4) (hk : s.k = 4) :
    isScsV39 s' := by
  sorry
  -- DISCHARGES: k = 4 instance of SCS_HALF_SLICE_IS_SCS (source 1134-1758).

/-- HOL `IS_EAR_IS_SCS` (QKNVMLB.hl:1758). -/
theorem IS_EAR_IS_SCS_p35 (s : ScsV39) (h : isEarV39 s) : isScsV39 s := h.1

/-- HOL `SCS_HALF_SLICE_IS_SCS_4_PRIME` (QKNVMLB.hl:1765, proof ~670 ln). -/
theorem SCS_HALF_SLICE_IS_SCS_4_PRIME_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hmj : s'.J 0 (s'.k - 1) = mkj)
    (hear : isEarV39 s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (hbm : s.bm p q < 4) (hk : s.k = 4) :
    isScsV39 s' := by
  sorry
  -- DISCHARGES: as SCS_HALF_SLICE_IS_SCS_4 with `is_ear s''` swapped for
  -- the negated `J` conjunct (source 1765-2438).

/-- HOL `SCS_HALF_SLICE_IS_SCS_PRIME` (QKNVMLB.hl:2438, proof ~870 ln). -/
theorem SCS_HALF_SLICE_IS_SCS_PRIME_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hmj : s'.J 0 (s'.k - 1) = mkj)
    (hear : isEarV39 s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (hbm : s.bm p q < 4) (hcstab : 4 < s.k → s.bm p q ≤ cstab) :
    isScsV39 s' := by
  sorry
  -- DISCHARGES: general-k twin of SCS_HALF_SLICE_IS_SCS_4_PRIME
  -- (source 2438-3309).

/-- HOL `SCS_HALF_SLICE_IS_A_SCS` (QKNVMLB.hl:3309). -/
theorem SCS_HALF_SLICE_IS_A_SCS_p35 (s s' s'' : ScsV39) (p q : ℕ)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) : isScsV39 s' := by
  sorry
  -- DISCHARGES: source 3309-3398; follows the is_scs_slice_v39 unfolding
  -- (mkj-choice + SCS_HALF_SLICE_IS_SCS/_4/_PRIME case tree).

/-! ## Diag-vs-edge kit (source order: 3398-4024) -/

/-- HOL `NOT_EQ_DIAG` (QKNVMLB.hl:3398): a diagonal of a conforming system
has strictly positive separation, hence `u ≠ w`. -/
theorem NOT_EQ_DIAG_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (_hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w) (hBB : BBsV39 s vv) :
    u ≠ w := by
  have hk3 : 0 < s.k := by have := hscs.2.1; omega
  have hp' : p % s.k < s.k := Nat.mod_lt _ hk3
  have hq' : q % s.k < s.k := Nat.mod_lt _ hk3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
  intro he
  have h2 : (2 : ℝ) ≤ s.a (p % s.k) (q % s.k) :=
    hdiag2 (p % s.k) (q % s.k) ⟨hp', hq', fun e => hdiag.1 e⟩
  have h3 : s.a (p % s.k) (q % s.k) ≤ dist u w := by
    have hb := (hBB.2.2.1 (p % s.k) (q % s.k)).1
    rwa [hp, hq] at hb
  rw [he, dist_self] at h3
  linarith

/-- HOL `IN_IMAGE_VV` (QKNVMLB.hl:3424). -/
theorem IN_IMAGE_VV_p35 (vv : ℕ → V3) (p : ℕ) : vv p ∈ Set.range vv := ⟨p, rfl⟩

/-- HOL `SUC_MOD_NOT_EQ` (QKNVMLB.hl:3431). -/
theorem SUC_MOD_NOT_EQ_p35 {k : ℕ} (hk : 1 < k) (i : ℕ) : i % k ≠ (i + 1) % k := by
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have hik : i % k < k := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge (i % k + 1) k with h | h
  · rw [e1, Nat.mod_eq_of_lt (by omega : i % k + 1 < k)]
    omega
  · have hk1 : i % k + 1 = k := by omega
    rw [e1, hk1, Nat.mod_self]
    omega

/-- HOL `IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3` (QKNVMLB.hl:3447). -/
theorem IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 (s : ScsV39) (vv : ℕ → V3)
    (i : ℕ) (hk : 3 < s.k) (hscs : isScsV39 s) (hBB : BBsV39 s vv) :
    ¬ Collinear ℝ {(0:V3), vv (i % s.k), vv ((i + 1) % s.k)} := by
  have hk0 : 0 < s.k := by omega
  have hP : i % s.k < s.k := Nat.mod_lt _ hk0
  have hQ : (i + 1) % s.k < s.k := Nat.mod_lt _ hk0
  have hne : i % s.k ≠ (i + 1) % s.k := SUC_MOD_NOT_EQ_p35 (by omega) i
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpb, -, -, -, -, hd2, -, hbc, -, -, -⟩ := hscs
  have hp1 : Periodic (fun z => s.b (i % s.k) z) s.k := fun t => (hpb (i % s.k) t).2
  have h2' : (i % s.k + 1) % s.k = (i + 1) % s.k := Nat.mod_add_mod i s.k 1
  have hbb : s.b (i % s.k) ((i + 1) % s.k) ≤ cstab := by
    have h1 := periodic_mod_eq_p23 hp1 (i % s.k + 1)
    conv_lhs => rw [← h2']
    rw [h1]
    exact hbc (i % s.k) hk
  have hv1 : vv (i % s.k) ∈ ballAnnulus := hBB.1 ⟨i % s.k, rfl⟩
  have hv2 : vv ((i + 1) % s.k) ∈ ballAnnulus := hBB.1 ⟨(i + 1) % s.k, rfl⟩
  have h2le : (2:ℝ) ≤ s.a (i % s.k) ((i + 1) % s.k) := hd2 _ _ ⟨hP, hQ, hne⟩
  have hge2 : (2 : ℝ) ≤ ‖vv (i % s.k) - vv ((i + 1) % s.k)‖ := by
    have h2 := (hBB.2.2.1 (i % s.k) ((i + 1) % s.k)).1
    rw [dist_eq_norm] at h2
    linarith
  have hup : ‖vv (i % s.k) - vv ((i + 1) % s.k)‖ ≤ cstab := by
    have h3 := (hBB.2.2.1 (i % s.k) ((i + 1) % s.k)).2
    rw [dist_eq_norm] at h3
    linarith
  exact NONPARALLEL_BALL_ANNULUS hv1 hv2 hge2 hup

/-- HOL `DIAG_NOT_IN_EDGES` (QKNVMLB.hl:3610). -/
theorem DIAG_NOT_IN_EDGES_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
    (vv : ℕ → V3) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (_hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hE : E = Set.range fun i => {vv i, vv (i + 1)}) (hBB : BBsV39 s vv) :
    {u, w} ∉ E := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hP : p % s.k < s.k := Nat.mod_lt _ hk0
  have hQ : q % s.k < s.k := Nat.mod_lt _ hk0
  have hper : Periodic vv s.k := hBB.2.1
  have hscs0 := hscs
  have hdiag0 := hdiag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd2, -, -, -, -, -⟩ := hscs
  obtain ⟨h1, h2, h3⟩ := hdiag
  have hvvinj : ∀ a b : ℕ, a < s.k → b < s.k → a ≠ b → vv a ≠ vv b := by
    intro a b ha hb hab
    have h2 := hd2 a b ⟨ha, hb, hab⟩
    have h3 := (hBB.2.2.1 a b).1
    intro he
    rw [he, dist_self] at h3
    linarith
  have hpe : ∀ n : ℕ, vv (n % s.k) = vv n := periodic_mod_eq_p23 hper
  intro hmem
  rw [hE, Set.mem_range] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hu : u = vv x ∨ u = vv (x + 1) := by
    have h1' : (u:V3) ∈ ({u, w} : Set V3) := Set.mem_insert u _
    have h2' : u ∈ ({vv x, vv (x + 1)} : Set V3) := hx ▸ h1'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2'
    exact h2'
  have hw : w = vv x ∨ w = vv (x + 1) := by
    have h1' : (w:V3) ∈ ({u, w} : Set V3) := Set.mem_insert_of_mem u (Set.mem_singleton w)
    have h2' : w ∈ ({vv x, vv (x + 1)} : Set V3) := hx ▸ h1'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2'
    rcases h2' with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hres : ∀ n : ℕ, (n + 1) % s.k = (n % s.k + 1) % s.k := fun n =>
    (Nat.mod_add_mod n s.k 1).symm
  have huw : u ≠ w := NOT_EQ_DIAG_p35 s p q u w vv hscs0 hdiag0 _hdist hp hq hBB
  rcases hu with hu | hu
  · rcases hw with hw | hw
    · -- u = vv x, w = vv x → u = w
      exact huw (hu.trans hw.symm)
    · -- u = vv x, w = vv (x + 1)
      have hxP : vv (x % s.k) = u := by rw [hpe, hu]
      have hxQ : vv ((x + 1) % s.k) = w := by rw [hpe, hw]
      by_cases hxp : x % s.k = p % s.k
      · have h1x : vv ((x + 1) % s.k) = vv (q % s.k) := hxQ.trans hq.symm
        have h2x : (x + 1) % s.k = q % s.k := by
          by_contra hne2
          exact absurd h1x (hvvinj ((x + 1) % s.k) (q % s.k)
            (Nat.mod_lt _ hk0) hQ hne2)
        exact h2 (by rw [hres p, ← hxp, ← hres x, h2x])
      · have hdx : vv (x % s.k) = u := by rw [hpe, hu]
        have hAb := (hBB.2.2.1 (x % s.k) (p % s.k)).1
        rw [hdx, hp, dist_self] at hAb
        have h2le := hd2 (x % s.k) (p % s.k) ⟨Nat.mod_lt _ hk0, hP, hxp⟩
        linarith
  · rcases hw with hw | hw
    · -- u = vv (x + 1), w = vv x
      have hxP : vv ((x + 1) % s.k) = u := by rw [hpe, hu]
      have hxQ : vv (x % s.k) = w := by rw [hpe, hw]
      by_cases hxq : x % s.k = q % s.k
      · have h1x : vv ((x + 1) % s.k) = vv (p % s.k) := hxP.trans hp.symm
        have h2x : (x + 1) % s.k = p % s.k := by
          by_contra hne2
          exact absurd h1x (hvvinj ((x + 1) % s.k) (p % s.k)
            (Nat.mod_lt _ hk0) hP hne2)
        exact h3 (by rw [hres q, ← hxq, ← hres x, h2x])
      · have hdx : vv (x % s.k) = w := by rw [hpe, hw]
        have hAb := (hBB.2.2.1 (x % s.k) (q % s.k)).1
        rw [hdx, hq, dist_self] at hAb
        have h2le := hd2 (x % s.k) (q % s.k) ⟨Nat.mod_lt _ hk0, hQ, hxq⟩
        linarith
    · -- u = vv (x + 1), w = vv (x + 1) → u = w
      exact huw (hu.trans hw.symm)

/-- HOL `SCS_K_LE_6` (QKNVMLB.hl:3724). -/
theorem SCS_K_LE_6_p35 (s : ScsV39) (h : isScsV39 s) : s.k ≤ 6 := h.2.2.1

/-- HOL `TECOXBMv2` (QKNVMLB.hl:3730): the diag wedge contains every fan
face wedge. -/
theorem TECOXBMv2_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (_hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hBB : BBsV39 s vv) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E := by
  sorry
  -- DISCHARGES: source 3730-4024; giant aff_gt/wedge_in_fan_gt argument
  -- over the cyclic fan ordering (TECOXBM machinery of Local_lemmas).

/-! ## Graph re-labelling (source order: 4024-4838) -/

/-- HOL `VV_SUC_EQ_RHO_NODE` (QKNVMLB.hl:4024). -/
theorem VV_SUC_EQ_RHO_NODE_p35 (s : ScsV39) (k p1 p q : ℕ) (u : V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hk : s.k = k) (hp1 : vv p1 = u)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv) :
    ∀ m, (rhoNode1 FF)^[m] u = vv (m + p1) := by
  sorry
  -- DISCHARGES: source 4024-4061; the rho_node1 orbit follows the cyclic
  -- vv ordering (needs the k>3 fan acyclicity kit).

/-- HOL `W_EW_K_SCS_ADD_P` (QKNVMLB.hl:4061). -/
theorem W_EW_K_SCS_ADD_P_p35 (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (k k' : ℕ) (u w : V3) (vv : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s') (hk' : s'.k = k') (hk : s.k = k)
    (hp : vv (p % k) = u) (hq : vv (q % k) = w)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv) :
    vv (k' - 1 + p % k) = w := by
  subst hk
  have horig : s'.k = k' := hk'
  rw [← hs'] at hk'
  simp only [scsHalfSliceV39] at hk'
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk'1 : 1 ≤ k' := by have := hge.1; omega
  have hPk : p % s.k < s.k := Nat.mod_lt _ (by have := hscs.2.1; omega)
  have hper : Periodic vv s.k := hBB.2.1
  have hdm : (q + 1 + (s.k - p % s.k)) / s.k * s.k + k'
      = q + 1 + (s.k - p % s.k) := by
    have h := Nat.div_add_mod' (q + 1 + (s.k - p % s.k)) s.k
    rw [hk'] at h
    exact h
  have hA : (k' - 1 + p % s.k) + (q + 1 + (s.k - p % s.k)) / s.k * s.k
      = q + s.k := by omega
  have hkey : (k' - 1 + p % s.k) % s.k = q % s.k := by
    calc (k' - 1 + p % s.k) % s.k
        = ((k' - 1 + p % s.k) + (q + 1 + (s.k - p % s.k)) / s.k * s.k) % s.k := by
          rw [Nat.add_mul_mod_self_right]
      _ = (q + s.k) % s.k := by rw [hA]
      _ = q % s.k := Nat.add_mod_right _ _
  rw [← periodic_mod_eq_p23 hper (k' - 1 + p % s.k), hkey]
  exact hq

/-- HOL `VV_INJ` (QKNVMLB.hl:4144): vv is injective on the index window. -/
theorem VV_INJ_p35 (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (hk : s.k = k)
    (hscs : isScsV39 s) (hBB : BBsV39 s vv) :
    ∀ i j, i < k ∧ j < k ∧ i ≠ j → vv i ≠ vv j := by
  have hk3 : 0 < s.k := by have := hscs.2.1; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
  intro i j ⟨hi, hj, hne⟩ he
  rw [← hk] at hi hj
  have h2 : (2 : ℝ) ≤ s.a i j := hdiag2 i j ⟨hi, hj, hne⟩
  have h3 : s.a i j ≤ dist (vv i) (vv j) := (hBB.2.2.1 i j).1
  rw [he, dist_self] at h3
  linarith

/-- HOL `CARD_V_EQ_SCS_K` (QKNVMLB.hl:4162). -/
theorem CARD_V_EQ_SCS_K_p35 (s : ScsV39) (k p q : ℕ) (V : Set V3) (vv : ℕ → V3)
    (hk : s.k = k) (hV : Set.range vv = V) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv) : Set.ncard V = k := by
  subst hk
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hper : Periodic vv s.k := hBB.2.1
  rw [← hV, range_periodic_image_p23 vv s.k hk0 hper, Set.InjOn.ncard_image]
  · rw [Set.ncard_Iio_nat]
  · intro i hi j hj hne
    by_contra hne2
    exact absurd hne (VV_INJ_p35 s s.k vv rfl hscs hBB i j ⟨hi, hj, hne2⟩)

/-- HOL `V_PRIME_EQ_V_vv` (QKNVMLB.hl:4290, proof ~120 ln). -/
theorem V_PRIME_EQ_V_vv_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hk' : s'.k = k') (hk : s.k = k)
    (hp : vv (p % k) = u) (hq : vv (q % k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hnorm : norm (u - w) ≤ cstab)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS) :
    Set.range (fun i => vv (i % k' + p % k)) =
      vPrime_p3 V (HS.face (u, rhoNode1 FF u)) := by
  sorry
  -- DISCHARGES: source 4290-4406; the diag-closed face's vertex set is the
  -- re-indexed window (orbit + INTER_SLICE bookkeeping).

/-- HOL `E_PRIME_EQ_E_vv` (QKNVMLB.hl:4406, proof ~215 ln). -/
theorem E_PRIME_EQ_E_vv_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hk' : s'.k = k') (hk : s.k = k)
    (hp : vv (p % k) = u) (hq : vv (q % k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hnorm : norm (u - w) ≤ cstab)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS) :
    Set.range (fun i => {vv (i % k' + p % k), vv ((i + 1) % k' + p % k)}) =
      ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)) := by
  sorry
  -- DISCHARGES: source 4406-4622.

/-- HOL `F_PRIME_EQ_F_vv` (QKNVMLB.hl:4622, proof ~215 ln). -/
theorem F_PRIME_EQ_F_vv_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hk' : s'.k = k') (hk : s.k = k)
    (hp : vv (p % k) = u) (hq : vv (q % k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hnorm : norm (u - w) ≤ cstab)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS) :
    Set.range (fun i => (vv (i % k' + p % k), vv ((i + 1) % k' + p % k))) =
      HS.face (u, rhoNode1 FF u) := by
  sorry
  -- DISCHARGES: source 4622-4838.

/-! ## BBs transport / taustar bank opens (source order: 4838-5312) -/

/-- HOL `QKNVMLB1_LE4F` (QKNVMLB.hl:4838, proof ~225 ln). -/
theorem QKNVMLB1_LE4F_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (h4 : 4 < s.k ∧ s.bm p q ≤ cstab) (hMM : vv ∈ MMsV39 s) :
    BBsV39 s' vv' := by
  sorry
  -- DISCHARGES: source 4838-5064; MMs → BBs transport along the slice
  -- (a/b-window re-indexing through scsHalfSliceV39).

/-- HOL `QKNVMLB1_EQ4F` (QKNVMLB.hl:5064, proof ~160 ln). -/
theorem QKNVMLB1_EQ4F_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (h4 : 4 = s.k ∧ s.bm p q ≤ 4) (hMM : vv ∈ MMsV39 s) :
    BBsV39 s' vv' := by
  sorry
  -- DISCHARGES: source 5064-5223; k = 4 twin of QKNVMLB1_LE4F.

/-- HOL `QKNVMLB1` (QKNVMLB.hl:5223). -/
theorem QKNVMLB1_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop) (vv : ℕ → V3)
    (hMM : vv ∈ MMsV39 s) (hbm : s.bm p q < 4)
    (h4 : s.k = 4 ∨ s.bm p q ≤ cstab) (hscs : isScsV39 s) (hd' : d' < 0.9)
    (hdiag : scsDiag s.k p q) (s' : ScsV39)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj) (vv' : ℕ → V3)
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k)) :
    BBsV39 s' vv' := by
  sorry
  -- DISCHARGES: composes QKNVMLB1_EQ4F_p35 (k = 4) / QKNVMLB1_LE4F_p35
  -- (4 < k, via SCS_K_PRIME_CASE_3_p35) on the bm < 4 / bm ≤ cstab split;
  -- blocked by QKNVMLB1_LE4F/EQ4F.

/-- HOL `DIAG_IS_NOT_EAR` (QKNVMLB.hl:5265). -/
theorem DIAG_IS_NOT_EAR_p35 (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : ¬ isEarV39 s := by
  intro he
  have h3 := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hk := he.2.2.1
  omega

/-- Sandbox helper: the half slice has `k' ≥ 1` — `k' = 0` would force
`(q + 1) % s.k = p % s.k`, excluded by the diagonal. -/
private theorem halfSlice_k_pos_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hk0 : 0 < s.k) (h3 : ¬(p % s.k = (q + 1) % s.k)) :
    0 < (scsHalfSliceV39 s p q d' mkj).k := by
  have hPk : p % s.k < s.k := Nat.mod_lt _ hk0
  by_contra h0
  rw [Nat.not_lt] at h0
  rw [Nat.le_zero] at h0
  simp only [scsHalfSliceV39] at h0
  have e1 : (q + 1 + (s.k - p % s.k) + p % s.k) % s.k = p % s.k := by
    rw [Nat.add_mod, h0]
    simp
  have e2 : (q + 1 + (s.k - p % s.k) + p % s.k) = q + 1 + s.k := by omega
  rw [e2, Nat.add_mod_right] at e1
  exact h3 e1.symm

/-- Sandbox helper: the half slice's `J`-flag sits at the override pair
`(0, k' - 1)`. -/
private theorem halfSlice_J_diag_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hk1 : 0 < (q + 1 + (s.k - p % s.k)) % s.k) :
    (scsHalfSliceV39 s p q d' mkj).J 0 ((scsHalfSliceV39 s p q d' mkj).k - 1) = mkj := by
  have hcond : ({(0:ℕ) % ((q + 1 + (s.k - p % s.k)) % s.k),
      (((q + 1 + (s.k - p % s.k)) % s.k) - 1) % ((q + 1 + (s.k - p % s.k)) % s.k)} : Set ℕ)
      = {0, ((q + 1 + (s.k - p % s.k)) % s.k) - 1} := by
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [scsHalfSliceV39]
  exact if_pos hcond

/-- HOL `SCS_J_DIAG_EQ` (QKNVMLB.hl:5278). -/
theorem SCS_J_DIAG_EQ_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) :
    s'.J 0 (s'.k - 1) = s''.J 0 (s''.k - 1) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  simp only [isScsSliceV39] at hsl
  obtain ⟨hpair, -, -, -, -, -, -⟩ := hsl
  simp only [scsSliceV39, Prod.mk.injEq] at hpair
  obtain ⟨he1, he2⟩ := hpair
  rw [he2]
  simp only [scsHalfSliceV39]
  have hk'' : 0 < (p + 1 + (s.k - q % s.k)) % s.k :=
    halfSlice_k_pos_p35 s q p s''.d (s'.J 0 (s'.k - 1)) hk0 (fun e => hdiag.2.1 e.symm)
  have hcond : ({(0:ℕ) % ((p + 1 + (s.k - q % s.k)) % s.k),
      (((p + 1 + (s.k - q % s.k)) % s.k) - 1) % ((p + 1 + (s.k - q % s.k)) % s.k)} : Set ℕ)
      = {0, ((p + 1 + (s.k - q % s.k)) % s.k) - 1} := by
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
  rw [if_pos hcond]

/-- HOL `DIAG_NOT_IN_SCS_J` (QKNVMLB.hl:5303). -/
theorem DIAG_NOT_IN_SCS_J_p35 (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : ¬ s.J p q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJimp, -, -⟩ := hscs
  intro hJ
  rcases hJimp p q hJ with h | h
  · exact hdiag.2.1 h.symm
  · exact hdiag.2.2 h

/-! ## Slice/J bookkeeping and the taustar superadditivity chain
      (source order: 5312-8319) -/

/-- HOL `SCS_J_PRIME_SUBSET_SCS_J` (QKNVMLB.hl:5312). -/
theorem SCS_J_PRIME_SUBSET_SCS_J_p35 (s s' : ScsV39) (p q : ℕ) (d' : ℝ)
    (mkj : Prop) (hs' : scsHalfSliceV39 s p q d' mkj = s') (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) (i : ℕ) (hi : i < s'.k - 1)
    (hJ : s'.J i (i + 1)) :
    s.J ((i + p % s.k) % s.k) (((i + p % s.k) % s.k) + 1) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hJper, -, -, -, -, -, -, -, -, -⟩ := hscs
  rw [← hs'] at hJ hi
  simp only [scsHalfSliceV39] at hJ hi
  set K := (q + 1 + (s.k - p % s.k)) % s.k with hKdef
  have hk'eq : K = s'.k := by
    show (scsHalfSliceV39 s p q d' mkj).k = s'.k
    rw [hs']
  have hk'3 : 3 ≤ K := hk'eq ▸ hge.1
  have hik : i % K = i := Nat.mod_eq_of_lt (by omega)
  have hik1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hik, hik1] at hJ
  have hc : ¬(({i, i + 1} : Set ℕ) = {0, K - 1}) := by
    intro e
    by_cases h0 : i = 0
    · subst h0
      have h5 : (1:ℕ) ∈ ({0, K - 1} : Set ℕ) := by
        have h51 : (1:ℕ) ∈ ({0, 1} : Set ℕ) := by simp
        exact e ▸ h51
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h5
      rcases h5 with h5 | h5
      · exact absurd h5 (by norm_num)
      · omega
    · have h0n : (0:ℕ) ∉ ({i, i + 1} : Set ℕ) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      exact h0n (e ▸ (by simp : (0:ℕ) ∈ ({0, K - 1} : Set ℕ)))
  rw [if_neg hc] at hJ
  -- hJ : s.J (i + p % s.k) (i + 1 + p % s.k)
  have hp1 : Periodic (fun z => s.J z (i + 1 + p % s.k)) s.k :=
    fun t => (hJper t (i + 1 + p % s.k)).1
  have hmod1 : s.J ((i + p % s.k) % s.k) (i + 1 + p % s.k)
      = s.J (i + p % s.k) (i + 1 + p % s.k) := periodic_mod_eq_p23 hp1 (i + p % s.k)
  have hp2 : Periodic (fun z => s.J ((i + p % s.k) % s.k) z) s.k :=
    fun t => (hJper ((i + p % s.k) % s.k) t).2
  have hWb : (i + p % s.k) % s.k < s.k := Nat.mod_lt _ hk0
  have hW : (i + p % s.k) / s.k * s.k + (i + p % s.k) % s.k = i + p % s.k :=
    Nat.div_add_mod' _ _
  have hsum : i + 1 + p % s.k
      = ((i + p % s.k) % s.k + 1) + (i + p % s.k) / s.k * s.k := by
    have h1 : ((i + p % s.k) % s.k + 1) + (i + p % s.k) / s.k * s.k
        = (i + p % s.k) / s.k * s.k + (i + p % s.k) % s.k + 1 := by ring
    rw [h1, hW]
    ring
  rcases Nat.lt_or_ge ((i + p % s.k) % s.k + 1) s.k with hlt | hge2
  · have hb := periodic_mod_eq_p23 hp2 (i + 1 + p % s.k)
    have hmeq : (i + 1 + p % s.k) % s.k
        = ((i + p % s.k) % s.k + 1) % s.k := by
      rw [hsum, Nat.add_mul_mod_self_right]
    rw [hmeq, Nat.mod_eq_of_lt hlt] at hb
    rw [hb, hmod1]
    exact hJ
  · have hWk : (i + p % s.k) % s.k + 1 = s.k := by omega
    have hb := periodic_mod_eq_p23 hp2 (i + 1 + p % s.k)
    have hmeq : (i + 1 + p % s.k) % s.k
        = ((i + p % s.k) % s.k + 1) % s.k := by
      rw [hsum, Nat.add_mul_mod_self_right]
    rw [hmeq, hWk, Nat.mod_self] at hb
    have hthis : s.J ((i + p % s.k) % s.k) (((i + p % s.k) % s.k) + 1)
        = s.J ((i + p % s.k) % s.k) 0 := by
      rw [hWk]
      have hJ2 := (hJper ((i + p % s.k) % s.k) 0).2
      simpa using hJ2
    rw [hthis, hb, hmod1]
    exact hJ

/-- HOL `INTER_SLICE_SCS_EMPTY1` (QKNVMLB.hl:5371). -/
theorem INTER_SLICE_SCS_EMPTY1_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hpq : p % s.k < q % s.k) :
    {y | ∃ i < s'.k - 1, y = (i + p % s.k) % s.k} ∩
      {y | ∃ i < s''.k - 1, y = (i + q % s.k) % s.k} = ∅ := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hP : p % s.k < s.k := Nat.mod_lt _ hk0
  have hQ : q % s.k < s.k := Nat.mod_lt _ hk0
  obtain ⟨hd1, hd2, hd3⟩ := hdiag
  -- the two half-slice sizes (residue form, no wrap under P < Q and Q ≢ P - 1)
  have hk' : s'.k = q % s.k + 1 - p % s.k := by
    have hQ2 : q % s.k + 1 ≤ s.k := by omega
    have m1 : (q % s.k + 1) % s.k = (q + 1) % s.k := Nat.mod_add_mod q s.k 1
    have m2 : (q % s.k + 1 + (s.k - p % s.k)) % s.k
        = (q + 1 + (s.k - p % s.k)) % s.k := by
      calc (q % s.k + 1 + (s.k - p % s.k)) % s.k
          = ((q % s.k + 1) % s.k + (s.k - p % s.k) % s.k) % s.k := Nat.add_mod _ _ _
        _ = ((q + 1) % s.k + (s.k - p % s.k) % s.k) % s.k := by rw [m1]
        _ = (q + 1 + (s.k - p % s.k)) % s.k := (Nat.add_mod _ _ _).symm
    have h1 : q % s.k + 1 - p % s.k < s.k := by
      by_contra hge
      have hQ1 : q % s.k + 1 = s.k ∧ p % s.k = 0 := by omega
      have hqe : (q + 1) % s.k = 0 := by
        have hmeq : (q % s.k + 1) % s.k = (q + 1) % s.k := Nat.mod_add_mod q s.k 1
        rw [← hmeq, hQ1.1, Nat.mod_self]
      exact hd3 (by omega)
    rw [← hs']; simp only [scsHalfSliceV39]
    rw [← m2]
    have h3 : q % s.k + 1 + (s.k - p % s.k) = s.k + (q % s.k + 1 - p % s.k) := by omega
    rw [h3, Nat.add_mod_left, Nat.mod_eq_of_lt h1]
  have hk'' : s''.k = s.k + p % s.k + 1 - q % s.k := by
    have e2 : (p + 1) % s.k = (p % s.k + 1) % s.k := (Nat.mod_add_mod p s.k 1).symm
    rw [e2] at hd2
    have hPQ : p % s.k + 1 < q % s.k := by
      by_contra hge
      have hQb : p % s.k + 1 = q % s.k := by omega
      have hP1 : p % s.k + 1 < s.k := by omega
      exact hd2 (by rw [Nat.mod_eq_of_lt hP1]; exact hQb)
    have h1 : (s.k + p % s.k + 1) - q % s.k < s.k := by omega
    have m1 : (p % s.k + 1) % s.k = (p + 1) % s.k := Nat.mod_add_mod p s.k 1
    have m2 : (p % s.k + 1 + (s.k - q % s.k)) % s.k
        = (p + 1 + (s.k - q % s.k)) % s.k := by
      calc (p % s.k + 1 + (s.k - q % s.k)) % s.k
          = ((p % s.k + 1) % s.k + (s.k - q % s.k) % s.k) % s.k := Nat.add_mod _ _ _
        _ = ((p + 1) % s.k + (s.k - q % s.k) % s.k) % s.k := by rw [m1]
        _ = (p + 1 + (s.k - q % s.k)) % s.k := (Nat.add_mod _ _ _).symm
    rw [← hs'']; simp only [scsHalfSliceV39]
    rw [← m2]
    have h3 : p % s.k + 1 + (s.k - q % s.k) = (s.k + p % s.k + 1) - q % s.k := by omega
    rw [h3, Nat.mod_eq_of_lt h1]
  rw [hk', hk'']
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro y hy
  rw [Set.mem_inter_iff] at hy
  obtain ⟨⟨i, hi, hyi⟩, ⟨j, hj, hyj⟩⟩ := hy
  have hik : i + p % s.k < s.k := by omega
  have hy1 : y = i + p % s.k := by rw [hyi, Nat.mod_eq_of_lt hik]
  have hjk : j + q % s.k < s.k + s.k := by omega
  by_cases hlt : j + q % s.k < s.k
  · have hy2 : y = j + q % s.k := by rw [hyj, Nat.mod_eq_of_lt hlt]
    omega
  · have hy2 : y = j + q % s.k - s.k := by
      rw [hyj, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- HOL `INTER_SLICE_SCS_EMPTY` (QKNVMLB.hl:5495). -/
theorem INTER_SLICE_SCS_EMPTY_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) :
    {y | ∃ i < s'.k - 1, y = (i + p % s.k) % s.k} ∩
      {y | ∃ i < s''.k - 1, y = (i + q % s.k) % s.k} = ∅ := by
  rcases lt_trichotomy (p % s.k) (q % s.k) with h | h | h
  · exact INTER_SLICE_SCS_EMPTY1_p35 s s' s'' p q d' d'' mkj hs' hs'' hscs hdiag h
  · exact absurd h hdiag.1
  · rw [Set.inter_comm]
    exact INTER_SLICE_SCS_EMPTY1_p35 s s'' s' q p d'' d' mkj hs'' hs' hscs
      ⟨fun e => hdiag.1 e.symm, fun e => hdiag.2.2 e.symm, fun e => hdiag.2.1 e.symm⟩ h

/-- HOL `QKNVMLB2` (QKNVMLB.hl:5522, proof ~2215 ln — the giant). -/
theorem QKNVMLB2_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv vv' vv'' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'') :
    dsvV39 s vv ≤ dsvV39 s' vv' + dsvV39 s'' vv'' := by
  sorry
  -- DISCHARGES: the dsv superadditivity along the slice: dsv_J_empty on
  -- both halves, sum-split over INTER_SLICE windows, cstab-diag term
  -- = norm(u-w) bound via DIST_DIAG_LE_CSTAB (source 5522-7736).

/-- HOL `DIST_DIAG_LE_CSTAB` (QKNVMLB.hl:7736). -/
theorem DIST_DIAG_LE_CSTAB_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3)
    (hj : ¬(s.k = 4 ∧ ¬s'.J 0 (s'.k - 1)))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) :
    norm (vv (p % s.k) - vv (q % s.k)) ≤ cstab := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  obtain ⟨-, -, -, -, -, -, -, -, -, hpbm, -, -, hsym, -, -, -, -, -, -, -, -⟩ := hscs
  simp only [MMsV39, Set.mem_setOf_eq] at hMM
  obtain ⟨-, -, -, -, -, hbmle⟩ := hMM
  have hbmres : s.bm (p % s.k) (q % s.k) = s.bm p q := by
    have hP : p % s.k < s.k := Nat.mod_lt _ hk0
    have hQ : q % s.k < s.k := Nat.mod_lt _ hk0
    have hper1 : Periodic (fun z => s.bm z (q % s.k)) s.k := fun t => (hpbm t (q % s.k)).1
    have hper2 : Periodic (fun z => s.bm p z) s.k := fun t => (hpbm p t).2
    calc s.bm (p % s.k) (q % s.k) = s.bm p (q % s.k) := periodic_mod_eq_p23 hper1 p
      _ = s.bm p q := periodic_mod_eq_p23 hper2 q
  rw [← dist_eq_norm]
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl
  obtain ⟨-, -, -, -, -, hk4, -⟩ := hsl
  rcases hk4 with hk4 | hbm
  · simp only [isScsSliceV39] at hsl0
    obtain ⟨hpair, -, -, -, -, -, hear'⟩ := hsl0
    simp only [scsSliceV39, Prod.mk.injEq] at hpair
    obtain ⟨he1, he2⟩ := hpair
    have hJ' : s'.J 0 (s'.k - 1) := by
      rcases Classical.em (s'.J 0 (s'.k - 1)) with h | h
      · exact h
      · exact absurd ⟨hk4, h⟩ hj
    rcases hear' hJ' with he | he
    · obtain ⟨-, -, hk3, -, -, hJset⟩ := he
      obtain ⟨i, hseti, -, hbcst, -⟩ := hJset
      have hk3c : (q + 1 + (s.k - p % s.k)) % s.k = 3 := by
        have h3e : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
          rw [he1]; simp only [scsHalfSliceV39]
        omega
      have hJ2 : s'.J 2 3 := by
        rw [he1]
        simp only [scsHalfSliceV39]
        have hcond : ({(2:ℕ) % ((q + 1 + (s.k - p % s.k)) % s.k),
            (3 % ((q + 1 + (s.k - p % s.k)) % s.k))} : Set ℕ)
            = {0, ((q + 1 + (s.k - p % s.k)) % s.k) - 1} := by
          rw [hk3c]
          simp only [Nat.reduceMod, Nat.reduceSub]
          ext yy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        rw [if_pos hcond]
        exact hJ'
      have hi2 : i = 2 := by
        have hmem : (2:ℕ) ∈ ({i} : Set ℕ) := by rw [← hseti]; exact ⟨by omega, hJ2⟩
        simp only [Set.mem_singleton_iff] at hmem
        exact hmem.symm
      have hbcstab : s'.b 2 3 = cstab := by
        rw [hi2] at hbcst
        exact hbcst
      have hbov : s'.b 2 3 = s.bm p q := by
        rw [he1]
        simp only [scsHalfSliceV39]
        have hcond : ({(2:ℕ) % ((q + 1 + (s.k - p % s.k)) % s.k),
            (3 % ((q + 1 + (s.k - p % s.k)) % s.k))} : Set ℕ)
            = {0, ((q + 1 + (s.k - p % s.k)) % s.k) - 1} := by
          rw [hk3c]
          simp only [Nat.reduceMod, Nat.reduceSub]
          ext yy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        rw [if_pos hcond]
      have hbmfin : s.bm p q = cstab := hbov.symm.trans hbcstab
      have hdle : dist (vv (p % s.k)) (vv (q % s.k)) ≤ s.bm (p % s.k) (q % s.k) :=
        hbmle _ _
      rw [hbmres, hbmfin] at hdle
      exact hdle
    · obtain ⟨-, -, hk3, -, -, hJset⟩ := he
      obtain ⟨i, hseti, -, hbcst, -⟩ := hJset
      have hk3c : (p + 1 + (s.k - q % s.k)) % s.k = 3 := by
        have h3e : s''.k = (p + 1 + (s.k - q % s.k)) % s.k := by
          rw [he2]; simp only [scsHalfSliceV39]
        omega
      have hJ2 : s''.J 2 3 := by
        rw [he2]
        simp only [scsHalfSliceV39]
        have hcond : ({(2:ℕ) % ((p + 1 + (s.k - q % s.k)) % s.k),
            (3 % ((p + 1 + (s.k - q % s.k)) % s.k))} : Set ℕ)
            = {0, ((p + 1 + (s.k - q % s.k)) % s.k) - 1} := by
          rw [hk3c]
          simp only [Nat.reduceMod, Nat.reduceSub]
          ext yy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        rw [if_pos hcond]
        exact hJ'
      have hi2 : i = 2 := by
        have hmem : (2:ℕ) ∈ ({i} : Set ℕ) := by rw [← hseti]; exact ⟨by omega, hJ2⟩
        simp only [Set.mem_singleton_iff] at hmem
        exact hmem.symm
      have hbcstab : s''.b 2 3 = cstab := by
        rw [hi2] at hbcst
        exact hbcst
      have hbov : s''.b 2 3 = s.bm q p := by
        rw [he2]
        simp only [scsHalfSliceV39]
        have hcond : ({(2:ℕ) % ((p + 1 + (s.k - q % s.k)) % s.k),
            (3 % ((p + 1 + (s.k - q % s.k)) % s.k))} : Set ℕ)
            = {0, ((p + 1 + (s.k - q % s.k)) % s.k) - 1} := by
          rw [hk3c]
          simp only [Nat.reduceMod, Nat.reduceSub]
          ext yy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        rw [if_pos hcond]
      have hsyml : s.bm q p = s.bm p q := (hsym q p).2.2.1
      have hbmfin : s.bm p q = cstab :=
        Eq.trans hsyml.symm (hbov.symm.trans hbcstab)
      have hdle : dist (vv (p % s.k)) (vv (q % s.k)) ≤ s.bm (p % s.k) (q % s.k) :=
        hbmle _ _
      rw [hbmres, hbmfin] at hdle
      exact hdle
  · have hdle : dist (vv (p % s.k)) (vv (q % s.k)) ≤ s.bm (p % s.k) (q % s.k) :=
      hbmle _ _
    rw [hbmres] at hdle
    exact hdle.trans hbm

/-- HOL `VV_SUC_EQ_RHO_NODE_PRIME` (QKNVMLB.hl:8054). -/
theorem VV_SUC_EQ_RHO_NODE_PRIME_p35 (s : ScsV39) (k p1 p q : ℕ) (u : V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hk : s.k = k) (hp1 : vv p1 = u)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hBB : BBsV39 s vv) :
    ∀ m, (rhoNode1 FF)^[m] u = vv (m + p1) := by
  sorry
  -- DISCHARGES: source 8054-8089; k > 3 twin of VV_SUC_EQ_RHO_NODE_p35.

/-- HOL `SUM_AZIM_EQ_ANGLE_LE4` (QKNVMLB.hl:8089). -/
theorem SUM_AZIM_EQ_ANGLE_LE4_p35 (s : ScsV39) (p q : ℕ) (u : V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hk3 : ¬(s.k ≤ 3)) (hBB : BBsV39 s vv) (hscs : isScsV39 s)
    (hp : vv (p % s.k) = u)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) :
    setSum {i | i < s.k}
        (fun i => rhoFun (norm (vv (i + p % s.k))) *
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] u)) =
      setSum FF (fun e => rhoFun (norm e.1) * azimInFan e E) := by
  sorry
  -- DISCHARGES: source 8089-8202; per-face azimuth split of the vertex sum
  -- (needs the rho_node1 orbit VV_SUC_EQ_RHO_NODE_PRIME_p35 + sum-reorder).

/-- HOL `V_SLICE_EQ_NUMSEG` (QKNVMLB.hl:8202). -/
theorem V_SLICE_EQ_NUMSEG_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ)
    (mkj : Prop) (k k' : ℕ) (u : V3) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hk : s.k = k) (hk' : s'.k = k') (hp : vv (p % k) = u)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) :
    {i | i < k ∧ (rhoNode1 FF)^[i] u ∈ Set.range (fun j => vv (j % k' + p % k))} =
      {i | i < k'} := by
  sorry
  -- DISCHARGES: source 8202-8319; the slice's vertex orbit is exactly the
  -- k'-window (W_EW_K_SCS_ADD_P_p35 + injectivity).

/-- Sandbox helper: the slice condition is swap-symmetric (the mkj flags
agree by SCS_J_DIAG_EQ_p35, the numeric conjuncts reorder trivially). -/
private theorem slice_sym_aux_p35 (s s' s'' : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) (hsl : isScsSliceV39 s s' s'' p q) :
    isScsSliceV39 s s'' s' q p := by
  have hscs0 := hscs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsym, -, -, -, -, -, -, -, -⟩ := hscs
  have hsyml : s.bm q p = s.bm p q := (hsym q p).2.2.1
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl ⊢
  obtain ⟨hpair, hd1, hd2, hd3, hbm, hk4, hear⟩ := hsl
  simp only [scsSliceV39, Prod.mk.injEq] at hpair
  obtain ⟨he1, he2⟩ := hpair
  have hj := SCS_J_DIAG_EQ_p35 s s' s'' p q s'.d s''.d (s'.J 0 (s'.k - 1)) he1 he2
    hscs0 hdiag hsl0
  rw [← hj]
  refine ⟨?_, hd2, hd1, (by linarith : s.d ≤ s''.d + s'.d),
    (by rw [hsyml]; exact hbm), (by rw [hsyml]; exact hk4),
    fun hm => Or.symm (hear hm)⟩
  rw [Prod.mk.injEq]
  exact ⟨he2, he1⟩

/-- HOL `SCS_SLICE_SYM` (QKNVMLB.hl:8319). -/
theorem SCS_SLICE_SYM_p35 (s s' s'' : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) :
    isScsSliceV39 s s' s'' p q ↔ isScsSliceV39 s s'' s' q p := by
  constructor
  · exact slice_sym_aux_p35 s s' s'' p q hscs hdiag
  · intro hsl
    exact slice_sym_aux_p35 s s'' s' q p hscs
      ⟨fun e => hdiag.1 e.symm, fun e => hdiag.2.2 e.symm, fun e => hdiag.2.1 e.symm⟩ hsl

/-! ## Small sum/numseg bank (source order: 8422-8445) -/

/-- HOL `SUM_NUMSEG2` (QKNVMLB.hl:8422). -/
theorem SUM_NUMSEG2_p35 (t : ℕ → ℝ) :
    ∑ i ∈ Finset.range 3, t i = t 0 + t 1 + t 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp

/-- HOL `NUMSEG_2` (QKNVMLB.hl:8428). -/
theorem NUMSEG_2_p35 : {i : ℕ | i < 3} = {0, 1, 2} := by
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- HOL `SUM_NUMSEG3` (QKNVMLB.hl:8433). -/
theorem SUM_NUMSEG3_p35 (t : ℕ → ℝ) :
    ∑ i ∈ Finset.range 4, t i = t 0 + t 1 + t 2 + t 3 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp

/-- HOL `NUMSEG_3` (QKNVMLB.hl:8439). -/
theorem NUMSEG_3_p35 : {i : ℕ | i < 4} = {0, 1, 2, 3} := by
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-! ## Slice tau bank, k' = 3 azimuth identity and the master arrows
      (source order: 8445-10699) -/

/-- HOL `SUM_AZIM_EQ_ANGLE_EQ4` (QKNVMLB.hl:8445). -/
theorem SUM_AZIM_EQ_ANGLE_EQ4_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (vv vv' vv'' : ℕ → V3) (HS : Hypermap (V3 × V3))
    (hk' : k' = 3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hk's' : s'.k = k') (hk : s.k = k)
    (hp : vv (p % k) = u) (hq : vv (q % k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hnorm : norm (u - w) ≤ cstab)
    (hfan : ConvexLocalFan
      (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
      (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
      (HS.face (u, rhoNode1 FF u))) :
    tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
      setSum {i | i < k'}
          (fun i => rhoFun (norm (vv (i + p % k))) *
            interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
        (Real.pi + sol0) := by
  sorry
  -- DISCHARGES: source 8445-9059; k' = 3: tau3 decomposition via
  -- SUM_NUMSEG2_p35/NUMSEG_2_p35 + V/E/F_PRIME_EQ_*_p35 +
  -- SCS_HALF_SLICE_IS_A_SCS_p35 + the local-fan azimuth sum identity
  -- (SUM_AZIM over the diag-closed slice face).

/-- HOL `CARD_FF_EQ_CARD_SLICE_FF` (QKNVMLB.hl:9059). -/
theorem CARD_FF_EQ_CARD_SLICE_FF_p35 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
    (hfan : ConvexLocalFan V E FF) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
    (hHS : IsHypE_p35 V E HS)
    (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
    (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)) :
    Set.ncard FF = Set.ncard fv + Set.ncard fw - 2 := by
  sorry
  -- DISCHARGES: source 9059-9122; the diag edge splits FF into the two
  -- slice faces sharing exactly the {v,w}-edge (PROVE_THE_SLICE_ASSUMPTION
  -- + COMPATIBLE_BW_TWO_LEMMAS of Local_lemmas/Nkezbfc_local).

/-- HOL `CARD_SLICE_FF_LE_3` (QKNVMLB.hl:9122). -/
theorem CARD_SLICE_FF_LE_3_p35 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
    (hfan : ConvexLocalFan V E FF) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
    (hHS : IsHypE_p35 V E HS)
    (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
    (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)) :
    3 ≤ Set.ncard fv ∧ 3 ≤ Set.ncard fw := by
  sorry
  -- DISCHARGES: source 9122-9193; each slice face is a proper fan face
  -- (≥ 3 darts), same external kit as CARD_FF_EQ_CARD_SLICE_FF_p35.

/-- HOL `CARD_FF_EQ_SCS_K_3` (QKNVMLB.hl:9193): for k = 3 the fan has
exactly 3 darts. -/
theorem CARD_FF_EQ_SCS_K_3_p35 (s : ScsV39) (k : ℕ) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (hk : s.k = k)
    (hFF : FF = Set.range fun i => (vv i, vv (i + 1)))
    (hscs : isScsV39 s) (hk3 : k = 3) (hBB : BBsV39 s vv) : Set.ncard FF = 3 := by
  have hks : s.k = 3 := by omega
  have hper : ∀ i, vv (i + 3) = vv i := by
    have hp := hBB.2.1
    rw [hks] at hp
    exact hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
  rw [hks] at hdiag2
  have hwin : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → vv i ≠ vv j := by
    intro i j hi hj hne he
    have h2 : (2 : ℝ) ≤ s.a i j := hdiag2 i j ⟨hi, hj, hne⟩
    have h3 : s.a i j ≤ dist (vv i) (vv j) := (hBB.2.2.1 i j).1
    rw [he, dist_self] at h3
    linarith
  have hmod : ∀ i : ℕ, vv i = vv (i % 3) := by
    intro i
    have key : ∀ t : ℕ, vv (t * 3 + i % 3) = vv (i % 3) := by
      intro t
      induction t with
      | zero => simp
      | succ n ih =>
        have e : (n + 1) * 3 + i % 3 = (n * 3 + i % 3) + 3 := by ring
        rw [e, hper, ih]
    have e : i = i / 3 * 3 + i % 3 := by omega
    have h2 : (i / 3 * 3 + i % 3) % 3 = i % 3 := by omega
    rw [e, key, h2]
  have hFF' : FF = Set.range (fun i : Fin 3 => (vv (i : ℕ), vv ((i : ℕ) + 1))) := by
    rw [hFF]
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨⟨i % 3, by omega⟩, ?_⟩
      show (vv (i % 3), vv (i % 3 + 1)) = (vv i, vv (i + 1))
      have h1 := hmod i
      have h2 := hmod (i + 1)
      have h3 := hmod (i % 3 + 1)
      have e1 : (i + 1) % 3 = (i % 3 + 1) % 3 := by simp [Nat.add_mod]
      rw [h1, h2, e1, h3]
    · rintro ⟨j, rfl⟩
      exact ⟨(j : ℕ), rfl⟩
  have hinj : Function.Injective fun i : Fin 3 => (vv (i : ℕ), vv ((i : ℕ) + 1)) := by
    intro i j hij
    have he : vv (i : ℕ) = vv (j : ℕ) := by
      rw [Prod.mk.injEq] at hij
      exact hij.1
    by_contra hne
    have hie : (i : ℕ) ≠ (j : ℕ) := fun e => hne (Fin.ext e)
    exact hwin i j i.isLt j.isLt hie he
  rw [hFF', Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- HOL `QKNVMLB3_LE4` (QKNVMLB.hl:9215, proof ~965 ln — giant). -/
theorem QKNVMLB3_LE4_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv vv' vv'' : ℕ → V3)
    (hj : ¬(s.k = 4 ∧ ¬s'.J 0 (s'.k - 1)))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'') :
    taustarV39 s' vv' + taustarV39 s'' vv'' ≤ taustarV39 s vv := by
  sorry
  -- DISCHARGES: source 9215-10180; k ≠ (4, non-ear-flag) branch of the
  -- master inequality: tauFun additivity over QKNVMLB2_p35 + the k'/k''
  -- case tree from SCS_K_PRIME_CASE_5/6_p35 + TECOXBMv2/DIST_DIAG kit.

/-- HOL `DIAGE_VAL_P_Q` (QKNVMLB.hl:10180). -/
theorem DIAGE_VAL_P_Q_p35 (p q : ℕ) (h1 : p % 4 ≠ q % 4)
    (h2 : (p + 1) % 4 ≠ q % 4) (h3 : p % 4 ≠ (q + 1) % 4) :
    q % 4 = (p % 4 + 2) % 4 := by
  have e1 : (p + 1) % 4 = (p % 4 + 1) % 4 := by simp [Nat.add_mod]
  have e2 : (q + 1) % 4 = (q % 4 + 1) % 4 := by simp [Nat.add_mod]
  rw [e1] at h2
  rw [e2] at h3
  have hb1 : p % 4 < 4 := Nat.mod_lt _ (by omega)
  have hb2 : q % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases p % 4 <;> interval_cases q % 4 <;> omega

/-- HOL `QKNVMLB3_Eq4` (QKNVMLB.hl:10198, proof ~470 ln — giant). -/
theorem QKNVMLB3_Eq4_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv vv' vv'' : ℕ → V3)
    (hj : s.k = 4 ∧ ¬s'.J 0 (s'.k - 1))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'') :
    taustarV39 s' vv' + taustarV39 s'' vv'' ≤ taustarV39 s vv := by
  sorry
  -- DISCHARGES: source 10198-10665; k = 4 non-ear-flag branch: both halves
  -- have k' = 3 (SCS_K_PRIME_CASE_4_p35), tau3-tau3 ≤ tauFun via the
  -- slice-face azimuth identity SUM_AZIM_EQ_ANGLE_EQ4_p35 + DIAGE_VAL_P_Q.

/-- HOL `QKNVMLB3` (QKNVMLB.hl:10665) — the master taustar inequality. -/
theorem QKNVMLB3_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv vv' vv'' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'') :
    taustarV39 s' vv' + taustarV39 s'' vv'' ≤ taustarV39 s vv := by
  rcases Classical.em (s.k = 4 ∧ ¬s'.J 0 (s'.k - 1)) with h | h
  · exact QKNVMLB3_Eq4_p35 s s' s'' p q d' d'' mkj vv vv' vv'' h hs' hs'' hvv' hvv''
      hMM hscs hdiag hsl hd
  · exact QKNVMLB3_LE4_p35 s s' s'' p q d' d'' mkj vv vv' vv'' h hs' hs'' hvv' hvv''
      hMM hscs hdiag hsl hd
