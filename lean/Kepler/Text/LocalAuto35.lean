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

/-! ## Generic helpers (mirror of the E2 per_mod/pair_cases bank) -/

/-- A `k`-periodic one-argument function is `mod k`-blind. -/
theorem FFBD_PER1_p35 {α : Sort u} {f : ℕ → α} {k : ℕ} (hper : Periodic f k)
    (i : ℕ) : f i = f (i % k) := by
  have key : ∀ t x, f (t * k + x) = f x := by
    intro t
    induction t with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have e : (n + 1) * k + x = n * k + x + k := by ring
        rw [e, hper, ih]
  have e : i = i / k * k + i % k := (Nat.div_add_mod' i k).symm
  conv_lhs => rw [e]
  exact key (i / k) (i % k)

/-- A `k`-periodic two-argument function is `mod k`-blind in both arguments. -/
theorem FFBD_PER2_p35 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 f k) (i j : ℕ) : f i j = f (i % k) (j % k) := by
  have key1 : ∀ t x y, f (t * k + x) y = f x y := by
    intro t
    induction t with
    | zero => intro x y; simp
    | succ n ih =>
        intro x y
        have e : (n + 1) * k + x = n * k + x + k := by ring
        rw [e, (hper (n * k + x) y).1, ih]
  have key2 : ∀ t x y, f x (t * k + y) = f x y := by
    intro t
    induction t with
    | zero => intro x y; simp
    | succ n ih =>
        intro x y
        have e : (n + 1) * k + y = n * k + y + k := by ring
        rw [e, (hper x (n * k + y)).2, ih]
  conv_lhs => rw [← (Nat.div_add_mod' i k)]
  rw [key1 (i / k) (i % k) j]
  conv_lhs => rw [← (Nat.div_add_mod' j k)]
  rw [key2 (j / k) (i % k) (j % k)]

/-- Two-element set of naturals with distinct sides: two pairings only. -/
theorem FFBD_PAIR_CASES_p35 {a b c d : ℕ} (hab : a ≠ b)
    (h : ({a, b} : Set ℕ) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hmem1 : a ∈ ({c, d} : Set ℕ) := by rw [← h]; simp
  have hmem2 : b ∈ ({c, d} : Set ℕ) := by rw [← h]; simp
  rcases Set.mem_insert_iff.mp hmem1 with hac | hac
  · rcases Set.mem_insert_iff.mp hmem2 with hbc | hbc
    · exact absurd (by rw [hac, hbc]) hab
    · exact Or.inl ⟨hac, hbc⟩
  · rcases Set.mem_insert_iff.mp hmem2 with hbc | hbc
    · exact Or.inr ⟨hac, hbc⟩
    · exact absurd (by rw [hac, hbc]) hab

/-- Two-element set commutes. -/
theorem FFBD_PAIR_COMM_p35 (a b : ℕ) : ({a, b} : Set ℕ) = {b, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Cancelling a common summand inside a mod-equality. -/
theorem FFBD_MOD_CANCEL_p35 {k c x y : ℕ} (h : (x + c) % k = (y + c) % k) :
    x % k = y % k := by
  have h1 : (x % k + c % k) % k = (y % k + c % k) % k := by
    rw [← Nat.add_mod, ← Nat.add_mod]; exact h
  have hres : Nat.ModEq k (x % k) (y % k) :=
    Nat.ModEq.add_right_cancel' (c := c % k) (a := x % k) (b := y % k) h1
  simpa [Nat.ModEq] using hres

/-- Equal remainders below the modulus are equal. -/
theorem FFBD_MODEQ_EQ_p35 {k a b : ℕ} (h : a % k = b % k) (ha : a < k) (hb : b < k) :
    a = b := by
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- The successor only advances the residue: `(i+1) % k = (i % k + 1) % k`. -/
theorem FFBD_ADD1_MOD_p35 {k i : ℕ} :
    (i + 1) % k = (i % k + 1) % k := by
  have key : ∀ t x, (x + t * k) % k = x % k := by
    intro t
    induction t with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have e : x + (n + 1) * k = (x + n * k) + k := by ring
        rw [e, Nat.add_mod_right]
        exact ih x
  have e : i + 1 = (i % k + 1) + (i / k) * k := by
    have hdm : i / k * k + i % k = i := Nat.div_add_mod' i k
    omega
  rw [e, key]

/-- The successor advances the residue unless the residue sits at `k - 1`. -/
theorem FFBD_SUC_MOD_p35 {k i : ℕ} (hk0 : 0 < k) (hne : i % k ≠ k - 1) :
    (i + 1) % k = i % k + 1 := by
  have hlt : i % k < k := Nat.mod_lt i hk0
  rw [FFBD_ADD1_MOD_p35, Nat.mod_eq_of_lt (by omega)]

/-- The `{0, k'-1}` override fires on the edge `(i, i+1)` exactly at the
wrap vertex `i = k'-1` (needs `2 < k'`, i.e. `k' ≥ 3`). -/
theorem FFBD_OVERRIDE_EDGE_p35 {k' : ℕ} (hk'3 : 2 < k') (i : ℕ) :
    ({i % k', (i + 1) % k'} : Set ℕ) = {0, k' - 1} ↔ i % k' = k' - 1 := by
  have hk'0 : 0 < k' := by omega
  constructor
  · intro hov
    by_cases h : i % k' = k' - 1
    · exact h
    · exfalso
      have hsuc : (i + 1) % k' = i % k' + 1 := FFBD_SUC_MOD_p35 hk'0 h
      have hne : i % k' ≠ (i + 1) % k' := by omega
      rcases FFBD_PAIR_CASES_p35 hne hov with ⟨hi0, hjk⟩ | ⟨hik, hj0⟩
      · omega
      · omega
  · intro hov
    have hz : (i + 1) % k' = 0 := by
      rw [FFBD_ADD1_MOD_p35, hov]
      have e : k' - 1 + 1 = k' := by omega
      rw [e, Nat.mod_self]
    have heq : ({i % k', (i + 1) % k'} : Set ℕ) = {k' - 1, 0} := by
      rw [hov, hz]
    rw [heq, FFBD_PAIR_COMM_p35 (k' - 1) 0]

/-! ## The shared field-by-field core (QKNVMLB.hl:305-3309, discharged once) -/

/-- The field-by-field core: `is_scs_v39` propagates through the half-slice
constructor `scsHalfSliceV39`.  The four `SCS_HALF_SLICE_IS_SCS*` twins of
QKNVMLB.hl:305-3309 are this one proof modulo the J-diagonal override being
fed by `¬mkj` (non-PRIME twins, override vacuous) vs `is_ear s''` (PRIME
twins, override fed by the ear — see `FFBD_EAR_HOVJ_p35`); the `k = 4`
specialisation twins need nothing extra (their `hcstab` side condition is
discharged vacuously since `4 < 4` is false).  Proof follows the HOL source
conjunct-by-conjunct: the four `Periodic` components are trivial (the
half slice is unadorned), the five `Periodic2` components ride the `mod2`
re-indexing, the diagonal override `{0, k'-1}` is handled per field, and the
final heavy-edge count injects `x ↦ (x + p%k)%k` into the source heavy set
plus the single wrap-vertex image (QKNVMLB.hl:850-870). -/
theorem SCS_HALF_SLICE_FF_CORE_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hd' : d' < 0.9) (hbm4 : s.bm p q < 4)
    (hcstab : 4 < s.k → s.bm p q ≤ cstab)
    (hovJ : mkj → s.am p q = Real.sqrt 8 ∧ s.bm p q = cstab) :
    isScsV39 (scsHalfSliceV39 s p q d' mkj) := by
  -- k'-bounds first (QKNVMLB.hl:272, SCS_K_PRIME_LE_GE — in-library CLEAN piece)
  obtain ⟨hk'3, hk'6, hk'lt⟩ :=
    SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag (scsHalfSliceV39 s p q d' mkj) rfl
  obtain ⟨hd, hk3, hk6, hlo, hhi, hstr, hstr2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag2, hb3, hbc, hJ, hJ2, hcard⟩ := hscs
  have hk0 : 0 < s.k := by omega
  have hp'lt : p % s.k < s.k := Nat.mod_lt _ hk0
  have hq'lt : q % s.k < s.k := Nat.mod_lt _ hk0
  obtain ⟨k', hk'eq⟩ : ∃ k', (q + 1 + (s.k - p % s.k)) % s.k = k' := ⟨_, rfl⟩
  rw [show (scsHalfSliceV39 s p q d' mkj).k = k' from by
    simp only [scsHalfSliceV39]; rw [hk'eq]] at hk'3 hk'6 hk'lt
  have hk'0 : 0 < k' := by omega
  -- name the three re-indexed field functions of the half slice
  set a1 : ℕ → ℕ → ℝ := fun x y =>
    if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.am p q
    else s.a (x % k' + p % s.k) (y % k' + p % s.k) with ha1def
  set b1 : ℕ → ℕ → ℝ := fun x y =>
    if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.bm p q
    else s.b (x % k' + p % s.k) (y % k' + p % s.k) with hb1def
  set J1 : ℕ → ℕ → Prop := fun x y =>
    if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then mkj
    else s.J (x % k' + p % s.k) (y % k' + p % s.k) with hJ1def
  have hunf : scsHalfSliceV39 s p q d' mkj =
      ScsV39.mk k' d' a1 a1 b1 b1 J1 (fun _ => False) (fun _ => False)
        (fun _ => False) := by
    simp only [scsHalfSliceV39, ha1def, hb1def, hJ1def]
    rw [hk'eq]
  have hA1 : ∀ x y, a1 x y =
      if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.am p q
      else s.a (x % k' + p % s.k) (y % k' + p % s.k) := fun _ _ => rfl
  have hB1 : ∀ x y, b1 x y =
      if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.bm p q
      else s.b (x % k' + p % s.k) (y % k' + p % s.k) := fun _ _ => rfl
  have hJ1 : ∀ x y, J1 x y =
      if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then mkj
      else s.J (x % k' + p % s.k) (y % k' + p % s.k) := fun _ _ => rfl
  rw [hunf]
  -- the heavy-edge counting map used by the last component
  have edge_norm : ∀ (f : ℕ → ℕ → ℝ), Periodic2 f s.k →
      ∀ u : ℕ, f u (u + 1) = f (u % s.k) (u % s.k + 1) := by
    intro f hf u
    rw [FFBD_PER2_p35 hf u (u + 1), FFBD_ADD1_MOD_p35]
    rcases Nat.lt_or_ge (u % s.k + 1) s.k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · have he : u % s.k + 1 = s.k := by have := Nat.mod_lt u hk0; omega
      rw [he, Nat.mod_self]
      have h2 := (hf (u % s.k) 0).2
      rw [Nat.zero_add] at h2
      rw [h2]
  have emod : ∀ t : ℕ, (t + k') % k' = t % k' := by
    intro t
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod_of_dvd _ (Nat.dvd_refl k')]
  -- the 21 components of HOL is_scs_v39, each proved for the half slice
  have c8 : ∀ i j, a1 (i + k') j = a1 i j ∧ a1 i (j + k') = a1 i j := by
    intro i j
    simp only [hA1]
    rw [emod i, emod j]
    exact ⟨rfl, rfl⟩
  have c9 : ∀ i j, a1 (i + k') j = a1 i j ∧ a1 i (j + k') = a1 i j := c8
  have c10 : ∀ i j, b1 (i + k') j = b1 i j ∧ b1 i (j + k') = b1 i j := by
    intro i j
    simp only [hB1]
    rw [emod i, emod j]
    exact ⟨rfl, rfl⟩
  have c11 : ∀ i j, b1 (i + k') j = b1 i j ∧ b1 i (j + k') = b1 i j := c10
  have c12 : ∀ i j, J1 (i + k') j = J1 i j ∧ J1 i (j + k') = J1 i j := by
    intro i j
    simp only [hJ1]
    rw [emod i, emod j]
    exact ⟨rfl, rfl⟩
  have c13 : ∀ i j, a1 i j = a1 j i ∧ a1 i j = a1 j i ∧ b1 i j = b1 j i ∧
      b1 i j = b1 j i ∧ J1 i j = J1 j i := by
    intro i j
    simp only [hA1, hB1, hJ1]
    have hswap' : ({i % k', j % k'} : Set ℕ) = {0, k' - 1} ↔
        ({j % k', i % k'} : Set ℕ) = {0, k' - 1} := by
      constructor <;> intro hc
      · rw [FFBD_PAIR_COMM_p35 (i % k') (j % k')] at hc
        exact hc
      · rw [FFBD_PAIR_COMM_p35 (j % k') (i % k')] at hc
        exact hc
    by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
    · simp only [if_pos hov, if_pos (hswap'.mp hov)]
      trivial
    · simp only [if_neg hov, if_neg (fun hc => hov (hswap'.mpr hc))]
      have H := hsym (i % k' + p % s.k) (j % k' + p % s.k)
      exact ⟨H.1, H.1, H.2.2.2.1, H.2.2.2.1, H.2.2.2.2⟩
  have c14 : ∀ i j, a1 i j ≤ a1 i j ∧ a1 i j ≤ b1 i j ∧ b1 i j ≤ b1 i j := by
    intro i j
    simp only [hA1, hB1]
    by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
    · simp only [if_pos hov]
      exact ⟨le_refl _, (hch p q).2.1, le_refl _⟩
    · simp only [if_neg hov]
      exact ⟨le_refl _,
        (hch (i % k' + p % s.k) (j % k' + p % s.k)).1.trans
          ((hch (i % k' + p % s.k) (j % k' + p % s.k)).2.1.trans
            (hch (i % k' + p % s.k) (j % k' + p % s.k)).2.2),
        le_refl _⟩
  have c15 : ∀ i, a1 i i = 0 := by
    intro i
    simp only [hA1]
    by_cases hov : ({i % k', i % k'} : Set ℕ) = {0, k' - 1}
    · exfalso
      have hs : ({i % k', i % k'} : Set ℕ) = {i % k'} := by simp
      rw [hs] at hov
      have m1 : (0 : ℕ) ∈ ({i % k'} : Set ℕ) := by rw [hov]; simp
      have m2 : (k' - 1 : ℕ) ∈ ({i % k'} : Set ℕ) := by rw [hov]; simp
      simp only [Set.mem_singleton_iff] at m1 m2
      omega
    · rw [if_neg hov]
      exact hdiag0 _
  have c16 : ∀ i j, i < k' ∧ j < k' ∧ i ≠ j → 2 ≤ a1 i j := by
    intro i j his
    obtain ⟨hi, hj, hne⟩ := his
    simp only [hA1]
    by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
    · rw [if_pos hov]
      have h1' : 2 ≤ s.a (p % s.k) (q % s.k) := hdiag2 _ _ ⟨hp'lt, hq'lt, hdiag.1⟩
      have h3 : s.a (p % s.k) (q % s.k) ≤ s.am (p % s.k) (q % s.k) := (hch _ _).1
      have h4 : s.am (p % s.k) (q % s.k) ≤ s.am p q := by
        conv_rhs => rw [FFBD_PER2_p35 hpam p q]
      exact h1'.trans (h3.trans h4)
    · rw [if_neg hov, FFBD_PER2_p35 hpa (i % k' + p % s.k) (j % k' + p % s.k)]
      have hik' : i % k' < k' := Nat.mod_lt i hk'0
      have hjk' : j % k' < k' := Nat.mod_lt j hk'0
      have hb1' : (i % k' + p % s.k) % s.k < s.k := Nat.mod_lt _ hk0
      have hb2' : (j % k' + p % s.k) % s.k < s.k := Nat.mod_lt _ hk0
      have hne2 : (i % k' + p % s.k) % s.k ≠ (j % k' + p % s.k) % s.k := by
        intro he
        have red1 : (i % k') % s.k = i % k' := Nat.mod_eq_of_lt (by omega)
        have red2 : (j % k') % s.k = j % k' := Nat.mod_eq_of_lt (by omega)
        have red3 : i % k' = i := Nat.mod_eq_of_lt hi
        have red4 : j % k' = j := Nat.mod_eq_of_lt hj
        have h1 := FFBD_MOD_CANCEL_p35 he
        rw [red1, red2, red3, red4] at h1
        exact hne h1
      exact hdiag2 _ _ ⟨hb1', hb2', hne2⟩
  have c17 : ∀ i, k' = 3 → b1 i (i + 1) < 4 := by
    intro i hk'3e
    simp only [hB1]
    rw [show k' = 3 from hk'3e]
    have hOV := FFBD_OVERRIDE_EDGE_p35 (k' := 3) (by omega) i
    by_cases hik' : i % 3 = 3 - 1
    · rw [if_pos (hOV.mpr hik')]
      exact hbm4
    · rw [if_neg (fun hc => hik' (hOV.mp hc))]
      have hsuc : (i + 1) % 3 = i % 3 + 1 := FFBD_SUC_MOD_p35 (by omega) hik'
      have e : i % 3 + 1 + p % s.k = i % 3 + p % s.k + 1 := by omega
      rw [hsuc, e]
      have hc4 : (cstab : ℝ) < 4 := by norm_num [cstab]
      exact lt_of_le_of_lt (hbc _ (by omega)) hc4
  have c18 : ∀ i, 3 < k' → b1 i (i + 1) ≤ cstab := by
    intro i hk'gt
    simp only [hB1]
    have hOV := FFBD_OVERRIDE_EDGE_p35 (k' := k') (by omega) i
    by_cases hik' : i % k' = k' - 1
    · rw [if_pos (hOV.mpr hik')]
      rcases Nat.lt_or_ge s.k 4 with h4 | h4
      · omega
      · exact hcstab (by omega)
    · rw [if_neg (fun hc => hik' (hOV.mp hc))]
      have hsuc : (i + 1) % k' = i % k' + 1 := FFBD_SUC_MOD_p35 hk'0 hik'
      have e : i % k' + 1 + p % s.k = i % k' + p % s.k + 1 := by omega
      rw [hsuc, e]
      exact hbc _ (by omega)
  have c19 : ∀ i j, J1 i j → j % k' = (i + 1) % k' ∨ i % k' = (j + 1) % k' := by
    intro i j hJij
    rw [hJ1] at hJij
    by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
    · rw [if_pos hov] at hJij
      have hne : i % k' ≠ j % k' := by
        intro he
        rw [he] at hov
        have hsing : ({j % k', j % k'} : Set ℕ) = {j % k'} := by simp
        rw [hsing] at hov
        have m1 : (0 : ℕ) ∈ ({j % k'} : Set ℕ) := by rw [hov]; simp
        have m2 : (k' - 1 : ℕ) ∈ ({j % k'} : Set ℕ) := by rw [hov]; simp
        simp only [Set.mem_singleton_iff] at m1 m2
        omega
      rcases FFBD_PAIR_CASES_p35 hne hov with ⟨hi0, hjk⟩ | ⟨hik, hj0⟩
      · right
        rw [hi0, FFBD_ADD1_MOD_p35, hjk, show k' - 1 + 1 = k' from by omega,
          Nat.mod_self]
      · left
        rw [hj0, FFBD_ADD1_MOD_p35, hik, show k' - 1 + 1 = k' from by omega,
          Nat.mod_self]
    · rw [if_neg hov] at hJij
      have hik'lt : i % k' < k' := Nat.mod_lt i hk'0
      have hjk'lt : j % k' < k' := Nat.mod_lt j hk'0
      rcases hJ (i % k' + p % s.k) (j % k' + p % s.k) hJij with hA1' | hA2'
      · left
        have e0 : i % k' + p % s.k + 1 = i % k' + 1 + p % s.k := by omega
        rw [e0] at hA1'
        have e3 : j % k' = i % k' + 1 := by
          have hcancel := FFBD_MOD_CANCEL_p35 hA1'
          have red1 : (j % k') % s.k = j % k' := Nat.mod_eq_of_lt (by omega)
          have red2 : (i % k' + 1) % s.k = i % k' + 1 := Nat.mod_eq_of_lt (by omega)
          rw [red1, red2] at hcancel
          exact hcancel
        rw [FFBD_ADD1_MOD_p35, e3]
        exact (Nat.mod_eq_of_lt (by omega)).symm
      · right
        have e0 : j % k' + p % s.k + 1 = j % k' + 1 + p % s.k := by omega
        rw [e0] at hA2'
        have e3 : i % k' = j % k' + 1 := by
          have hcancel := FFBD_MOD_CANCEL_p35 hA2'
          have red1 : (i % k') % s.k = i % k' := Nat.mod_eq_of_lt (by omega)
          have red2 : (j % k' + 1) % s.k = j % k' + 1 := Nat.mod_eq_of_lt (by omega)
          rw [red1, red2] at hcancel
          exact hcancel
        rw [FFBD_ADD1_MOD_p35, e3]
        exact (Nat.mod_eq_of_lt (by omega)).symm
  have c20 : ∀ i j, J1 i j → a1 i j = Real.sqrt 8 ∧ b1 i j = cstab := by
    intro i j hJij
    rw [hJ1] at hJij
    by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
    · rw [if_pos hov] at hJij
      obtain ⟨e1, e2⟩ := hovJ hJij
      rw [hA1, hB1, if_pos hov, if_pos hov]
      exact ⟨e1, e2⟩
    · rw [if_neg hov] at hJij
      obtain ⟨e1, e2⟩ := hJ2 _ _ hJij
      rw [hA1, hB1, if_neg hov, if_neg hov]
      exact ⟨e1, e2⟩
  have c21 : {i | i < k' ∧ (2 * h0 < b1 i (i + 1) ∨ 2 < a1 i (i + 1))}.ncard + k' ≤ 6 := by
    set H : Set ℕ := {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))} with hHdef
    have hHfin : H.Finite := (Finset.range s.k).finite_toSet.subset (by
      intro x hx
      obtain ⟨h1, -⟩ := hx
      exact Finset.mem_range.mpr h1)
    have hcf : (H ∪ {(k' - 1 + p % s.k) % s.k}).Finite := hHfin.union (Set.finite_singleton _)
    have key : ∀ i ∈ {i | i < k' ∧ (2 * h0 < b1 i (i + 1) ∨ 2 < a1 i (i + 1))},
        (i + p % s.k) % s.k ∈ H ∪ {(k' - 1 + p % s.k) % s.k} := by
      intro i hi
      obtain ⟨hik, hheavy⟩ := hi
      have hik'lt : i % k' < k' := Nat.mod_lt i hk'0
      have hik'eq : i % k' = i := Nat.mod_eq_of_lt hik
      by_cases hov : i % k' = k' - 1
      · -- wrap vertex: the edge carries the cut-diagonal am/bm pair
        have hov' : ({i % k', (i + 1) % k'} : Set ℕ) = {0, k' - 1} :=
          (FFBD_OVERRIDE_EDGE_p35 (by omega) i).mpr hov
        rw [hB1 i (i + 1), hA1 i (i + 1), if_pos hov', if_pos hov'] at hheavy
        refine Or.inr ?_
        rw [show i = k' - 1 from by omega]
        exact Set.mem_singleton_iff.mpr rfl
      · -- plain vertex: the heavy edge is an honest source edge
        have hovn : ({i % k', (i + 1) % k'} : Set ℕ) ≠ {0, k' - 1} := by
          intro hc
          exact hov ((FFBD_OVERRIDE_EDGE_p35 (by omega) i).mp hc)
        rw [hB1 i (i + 1), hA1 i (i + 1), if_neg hovn, if_neg hovn] at hheavy
        refine Or.inl ⟨Nat.mod_lt _ hk0, ?_⟩
        have hi1 : (i + 1) % k' = i + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hi1, hik'eq] at hheavy
        have e : i + 1 + p % s.k = i + p % s.k + 1 := by omega
        rw [e] at hheavy
        rcases hheavy with h1 | h1
        · refine Or.inl ?_
          rw [edge_norm s.b hpb (i + p % s.k)] at h1
          exact h1
        · refine Or.inr ?_
          rw [edge_norm s.a hpa (i + p % s.k)] at h1
          exact h1
    have hinj : Set.InjOn (fun x => (x + p % s.k) % s.k)
        {i | i < k' ∧ (2 * h0 < b1 i (i + 1) ∨ 2 < a1 i (i + 1))} := by
      intro i1 hi1 i2 hi2 he
      obtain ⟨h1, -⟩ := hi1
      obtain ⟨h2, -⟩ := hi2
      have h12 := FFBD_MOD_CANCEL_p35 (show (i1 + p % s.k) % s.k = (i2 + p % s.k) % s.k from he)
      rw [show (i1 : ℕ) % s.k = i1 from Nat.mod_eq_of_lt (by omega),
          show (i2 : ℕ) % s.k = i2 from Nat.mod_eq_of_lt (by omega)] at h12
      exact h12
    have hsub : {i | i < k' ∧ (2 * h0 < b1 i (i + 1) ∨ 2 < a1 i (i + 1))}.ncard
        ≤ (H ∪ {(k' - 1 + p % s.k) % s.k}).ncard :=
      Set.ncard_le_ncard_of_injOn (fun x => (x + p % s.k) % s.k) key hinj hcf
    have hc3 : (H ∪ {(k' - 1 + p % s.k) % s.k}).ncard ≤ H.ncard + 1 := by
      refine le_trans (Set.ncard_union_le H {(k' - 1 + p % s.k) % s.k}) ?_
      rw [Set.ncard_singleton]
    have hc4 : H.ncard + s.k ≤ 6 := hcard
    omega
  exact ⟨hd', hk'3, hk'6, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21⟩

/-! ## The PRIME J-override feeder and the four frozen twins -/

/-- The PRIME twins' J-diagonal override feeder: `is_ear s''` (the other half
slice of the same cut) forces the `sqrt8/cstab` pair at the cut diagonal
`(p, q)`.  Wiring of QKNVMLB.hl:1765-3309: if `mkj` fires then `s''.J 2 3`
holds, so the ear's unique `J`-witness on the `k'' = 3` cycle must be the
wrap vertex `2`, whose edge `{2, 0}` is the cut diagonal and carries
`s.am q p` / `s.bm q p`; symmetry of `s` swaps the arguments. -/
theorem FFBD_EAR_HOVJ_p35 (s s'' : ScsV39) (p q : ℕ) (d'' : ℝ) (mkj : Prop)
    (hscs : isScsV39 s) (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hear : isEarV39 s'') :
    mkj → s.am p q = Real.sqrt 8 ∧ s.bm p q = cstab := by
  obtain ⟨hd, hk3, hk6, hlo, hhi, hstr, hstr2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag2, hb3, hbc, hJ, hJ2, hcard⟩ := hscs
  intro hmkj
  have hk''3 : s''.k = 3 := hear.2.2.1
  have hE3 : (p + 1 + (s.k - q % s.k)) % s.k = 3 := by
    rw [hs''] at hk''3
    simpa only [scsHalfSliceV39] using hk''3
  have hset : ({2 % 3, 3 % 3} : Set ℕ) = {0, 3 - 1} := by
    rw [show (2 % 3 : ℕ) = 2 from by decide, show (3 % 3 : ℕ) = 0 from by decide,
      show (3 - 1 : ℕ) = 2 from by decide, FFBD_PAIR_COMM_p35 2 0]
  have hJ23 : s''.J 2 3 = mkj := by
    rw [hs'']
    simp only [scsHalfSliceV39]
    rw [hE3, if_pos hset]
  have hJ23t : s''.J 2 3 := by rw [hJ23]; exact hmkj
  obtain ⟨i, hset3, hsqrt, hcst, -⟩ := hear.2.2.2.2.2
  have h2in : (2 : ℕ) ∈ ({i} : Set ℕ) := by rw [← hset3]; exact ⟨by decide, hJ23t⟩
  have hi2 : i = 2 := by
    have h := (Set.mem_singleton_iff.mp h2in)
    omega
  rw [hi2] at hsqrt hcst
  have hA23 : s''.a 2 3 = s.am q p := by
    rw [hs'']
    simp only [scsHalfSliceV39]
    rw [hE3, if_pos hset]
  have hB23 : s''.b 2 3 = s.bm q p := by
    rw [hs'']
    simp only [scsHalfSliceV39]
    rw [hE3, if_pos hset]
  constructor
  · rw [← (hsym q p).2.1, ← hA23]
    exact hsqrt
  · rw [← (hsym q p).2.2.1, ← hB23]
    exact hcst


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

  have hmkj : ¬mkj := by rw [← hmj]; exact hmj'
  rw [hs']
  exact SCS_HALF_SLICE_FF_CORE_p35 s p q d' mkj hscs hdiag hd' hbm hcstab
    (fun h => absurd h hmkj)
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

  have hmkj : ¬mkj := by rw [← hmj]; exact hmj'
  rw [hs']
  exact SCS_HALF_SLICE_FF_CORE_p35 s p q d' mkj hscs hdiag hd' hbm
    (fun h => absurd h (by omega)) (fun h => absurd h hmkj)
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

  rw [hs']
  refine SCS_HALF_SLICE_FF_CORE_p35 s p q d' mkj hscs hdiag hd' hbm
    (fun h => absurd h (by omega)) ?_
  exact FFBD_EAR_HOVJ_p35 s s'' p q d'' mkj hscs hs'' hear
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

  rw [hs']
  refine SCS_HALF_SLICE_FF_CORE_p35 s p q d' mkj hscs hdiag hd' hbm hcstab ?_
  exact FFBD_EAR_HOVJ_p35 s s'' p q d'' mkj hscs hs'' hear
  -- DISCHARGES: general-k twin of SCS_HALF_SLICE_IS_SCS_4_PRIME
  -- (source 2438-3309).

/-- HOL `SCS_HALF_SLICE_IS_A_SCS` (QKNVMLB.hl:3309). -/
theorem SCS_HALF_SLICE_IS_A_SCS_p35 (s s' s'' : ScsV39) (p q : ℕ)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) : isScsV39 s' := by

  simp only [isScsSliceV39, scsSliceV39, Prod.mk.injEq] at hsl
  obtain ⟨⟨hs', hs''⟩, hd'lt, hd''lt, hdle, hbm4, hdisj, hmkj⟩ := hsl
  have h3k : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hkcase : s.k = 4 ∨ 4 < s.k := by omega
  rcases hkcase with hk4 | hkgt
  · have hk'3 : s'.k = 3 :=
      SCS_K_PRIME_CASE_4_p35 s s' p q s'.d (s'.J 0 (s'.k - 1)) hs' hscs hk4 hdiag
    rcases Classical.em (s'.J 0 (s'.k - 1)) with hmjt | hmjf
    · rcases hmkj hmjt with hear' | hear''
      · exact IS_EAR_IS_SCS_p35 s' hear'
      · exact SCS_HALF_SLICE_IS_SCS_4_PRIME_p35 s s' s'' p q s'.d s''.d
          (s'.J 0 (s'.k - 1)) (fun _ => (0 : V3)) (fun _ => (0 : V3))
          hs' hs'' rfl hear'' rfl hscs hdiag hd'lt hbm4 hk4
    · exact SCS_HALF_SLICE_IS_SCS_4_p35 s s' s'' p q s'.d s''.d
        (s'.J 0 (s'.k - 1)) (fun _ => (0 : V3)) (fun _ => (0 : V3))
        hs' hs'' rfl hmjf rfl hscs hdiag hd'lt hbm4 hk4
  · have hcstab : 4 < s.k → s.bm p q ≤ cstab := by
      intro _
      rcases hdisj with he | hc
      · omega
      · exact hc
    rcases Classical.em (s'.J 0 (s'.k - 1)) with hmjt | hmjf
    · rcases hmkj hmjt with hear' | hear''
      · exact IS_EAR_IS_SCS_p35 s' hear'
      · exact SCS_HALF_SLICE_IS_SCS_PRIME_p35 s s' s'' p q s'.d s''.d
          (s'.J 0 (s'.k - 1)) (fun _ => (0 : V3)) (fun _ => (0 : V3))
          hs' hs'' rfl hear'' rfl hscs hdiag hd'lt hbm4 hcstab
    · exact SCS_HALF_SLICE_IS_SCS_p35 s s' s'' p q s'.d s''.d
        (s'.J 0 (s'.k - 1)) (fun _ => (0 : V3)) (fun _ => (0 : V3))
        hs' hs'' rfl hmjf rfl hscs hdiag hd'lt hbm4 hcstab
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

/-- HOL `QKNVMLB1` (QKNVMLB.hl:5223).  RULING 2026-09-21 IV: this twin's
index convention `vv (i % s'.k + p % s.k)` is the FAITHFUL encoding -- it
is verbatim the proved original's `vv'` (QKNVMLB.hl:5225).  The LA1
registry concl carries the appendix.hl:1055 statement-let form
`vv ((i+p) % s'.k)`, which is unproved upstream and is NOT bridged here;
the registry correction belongs to the registry-refactor round (ruling
recorded at LocalConcl `QKNVMLB1_discharged`). -/
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

/-- HOL `QKNVMLB2` (QKNVMLB.hl:5522, proof ~2215 ln — the giant).
RULING 2026-09-21 IV: this twin's `vv (i % s'.k + p % s.k)` /
`vv (i % s''.k + q % s.k)` convention is faithful (QKNVMLB.hl:5525/:5527);
the LA1 registry's `vv ((i+p) % s'.k)` form is the unproved
appendix.hl:1064 statement-let — see `QKNVMLB1_p35`. -/
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

/-- HOL `CARD_FF_EQ_CARD_SLICE_FF` (QKNVMLB.hl:9059).
FIDELITY (SF-83): HOL freezes `HS = hypermap (HYP (vec 0,V,E UNION {{v, w}}))`
(QKNVMLB.hl:9065); the frozen hypothesis keeps the diag-augmented edge. -/
theorem CARD_FF_EQ_CARD_SLICE_FF_p35 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
    (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
    (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
    (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
    (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)) :
    Set.ncard FF = Set.ncard fv + Set.ncard fw - 2 := by
  sorry
  -- DISCHARGES: source 9059-9122; the diag edge splits FF into the two
  -- slice faces sharing exactly the {v,w}-edge (PROVE_THE_SLICE_ASSUMPTION
  -- + COMPATIBLE_BW_TWO_LEMMAS of Local_lemmas/Nkezbfc_local).

/-- HOL `CARD_SLICE_FF_LE_3` (QKNVMLB.hl:9122).
FIDELITY (SF-83): HOL freezes `HS = hypermap (HYP (vec 0,V,E UNION {{v, w}}))`
(QKNVMLB.hl:9128); the frozen hypothesis keeps the diag-augmented edge. -/
theorem CARD_SLICE_FF_LE_3_p35 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
    (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
    (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
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

/-- HOL `QKNVMLB3` (QKNVMLB.hl:10665) — the master taustar inequality.
RULING 2026-09-21 IV: the `i % s'.k + p % s.k` convention is faithful
(QKNVMLB.hl:10667/:10669); the LA1 registry's `(i+p) % s'.k` form is the
unproved appendix.hl:1075 statement-let — see `QKNVMLB1_p35`. -/
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
