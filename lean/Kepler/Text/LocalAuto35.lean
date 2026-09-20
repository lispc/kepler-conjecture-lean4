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
-/

import Kepler.Text.Polytope
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto3
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
  sorry
  -- DISCHARGES: full unfold of `scsHalfSliceV39` + the mod-4 diagonal
  -- calculus (`CASE_DIAGONAL_MOD` / `IMP_SUC_MOD_EQ` instantiations,
  -- QKNVMLB.hl:102) — not yet ported as reusable Lean lemmas.

/-- HOL `SCS_K_PRIME_CASE_5` (QKNVMLB.hl:138). -/
theorem SCS_K_PRIME_CASE_5_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
    (hk : s.k = 5) (hdiag : scsDiag s.k p q) :
    (s'.k = 3 ∧ s''.k = 4) ∨ (s'.k = 4 ∧ s''.k = 3) := by
  sorry
  -- DISCHARGES: mod-5 diagonal calculus (`CASE_DIAGONAL_MOD`, :145).

/-- HOL `SCS_K_PRIME_CASE_6` (QKNVMLB.hl:189). -/
theorem SCS_K_PRIME_CASE_6_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
    (hk : s.k = 6) (hdiag : scsDiag s.k p q) :
    (s'.k = 3 ∧ s''.k = 5) ∨ (s'.k = 5 ∧ s''.k = 3) ∨ (s'.k = 4 ∧ s''.k = 4) := by
  sorry
  -- DISCHARGES: mod-6 diagonal calculus (`CASE_DIAGONAL_MOD`, :196).

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
  sorry
  -- DISCHARGES: composes SCS_K_PRIME_CASE_3/4/5/6_p35 with the `3 ≤ k'`
  -- drop of the source's `LE_GE` strip (QKNVMLB.hl:272-305); needs the
  -- CASE_4/5/6 mod calculi discharged first.

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
    ¬ Collinear ℝ {(0 : V3), vv (i % s.k), vv ((i + 1) % s.k)} := by
  sorry
  -- DISCHARGES: source 3447-3610; needs the `ConvexLocalFan` branch of
  -- BBs_v39 (k > 3) plus the genericity/non-collinearity of fan vertices
  -- (localization `FAN` kit; cf. LocalAuto4/9 generic-layer).

/-- HOL `DIAG_NOT_IN_EDGES` (QKNVMLB.hl:3610). -/
theorem DIAG_NOT_IN_EDGES_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
    (vv : ℕ → V3) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (_hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hE : E = Set.range fun i => {vv i, vv (i + 1)}) (hBB : BBsV39 s vv) :
    {u, w} ∉ E := by
  sorry
  -- DISCHARGES: source 3610-3724; needs
  -- IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 (the diag edge would
  -- force a collinear fan triple).

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
  sorry
  -- DISCHARGES: source 4061-4144; needs the k' = q + 1 - (p mod k) shape
  -- of scsHalfSliceV39 (mod-arithmetic path through CASE_4/5/6).

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
  sorry
  -- DISCHARGES: source 4162-4290; image-of-numseg counting: Periodic vv k
  -- collapses the range onto i < k, VV_INJ_p35 gives injectivity there.

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

/-- HOL `SCS_J_DIAG_EQ` (QKNVMLB.hl:5278). -/
theorem SCS_J_DIAG_EQ_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) :
    s'.J 0 (s'.k - 1) = s''.J 0 (s''.k - 1) := by
  sorry
  -- DISCHARGES: source 5278-5303; both mkj flags equal the J-flag of the
  -- bm-diagonal override in scsHalfSliceV39 (PAIR_EQ on isScsSliceV39).

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
  sorry
  -- DISCHARGES: source 5312-5371; the slice J-pairs push forward along the
  -- p-shift (mod-2 table of scsHalfSliceV39).

/-- HOL `INTER_SLICE_SCS_EMPTY1` (QKNVMLB.hl:5371). -/
theorem INTER_SLICE_SCS_EMPTY1_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hpq : p % s.k < q % s.k) :
    {y | ∃ i < s'.k - 1, y = (i + p % s.k) % s.k} ∩
      {y | ∃ i < s''.k - 1, y = (i + q % s.k) % s.k} = ∅ := by
  sorry
  -- DISCHARGES: source 5371-5495; the two half-slice index windows are
  -- disjoint when the diag is oriented p < q (mod calculus + SCS_K_PRIME).

/-- HOL `INTER_SLICE_SCS_EMPTY` (QKNVMLB.hl:5495). -/
theorem INTER_SLICE_SCS_EMPTY_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) :
    {y | ∃ i < s'.k - 1, y = (i + p % s.k) % s.k} ∩
      {y | ∃ i < s''.k - 1, y = (i + q % s.k) % s.k} = ∅ := by
  sorry
  -- DISCHARGES: source 5495-5522; drops the p < q orientation via
  -- INTER_SLICE_SCS_EMPTY1_p35 + the symmetric instance.

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
  sorry
  -- DISCHARGES: source 7736-8054; the diag edge length is bm-bounded
  -- unless the k = 4 ear-flag case (is_scs_slice_v39 bm-components).

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

/-- HOL `SCS_SLICE_SYM` (QKNVMLB.hl:8319). -/
theorem SCS_SLICE_SYM_p35 (s s' s'' : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) :
    isScsSliceV39 s s' s'' p q ↔ isScsSliceV39 s s'' s' q p := by
  sorry
  -- DISCHARGES: source 8319-8422; symmetric re-pairing of the slice
  -- (isScsSliceV39 unfolding + SCS_J_DIAG_EQ_p35 + mkj-flag swap).

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
