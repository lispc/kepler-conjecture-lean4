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

/-! ## Section A helpers (patch: insert after LA35:453, before :455) -/

/-- `Classical.epsilon` collapse under a uniqueness hypothesis (LA5
`epsilonFixed` pattern; local copy — LA5 not importable here). -/
private theorem epsFixed_p35 {α : Type*} [Nonempty α] {pr : α → Prop} {a : α}
    (hpa : pr a) (huniq : ∀ y, pr y → y = a) : Classical.epsilon pr = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- Window injectivity of `vv` (twin of `VV_INJ_p35`, LA35:517; duplicated as
a private helper because the orbit lemma is needed before :517). -/
private theorem vvInjAux_p35 (s : ScsV39) (vv : ℕ → V3) (hscs : isScsV39 s)
    (hBB : BBsV39 s vv) : ∀ i j, i < s.k → j < s.k → i ≠ j → vv i ≠ vv j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
  intro i j hi hj hne he
  have h2 : (2 : ℝ) ≤ s.a i j := hdiag2 i j ⟨hi, hj, hne⟩
  have h3 : s.a i j ≤ dist (vv i) (vv j) := (hBB.2.2.1 i j).1
  rw [he, dist_self] at h3
  linarith

/-- Equal `vv`-values have equal residues (periodicity + window injectivity). -/
private theorem vvModEq_p35 {vv : ℕ → V3} {k : ℕ} (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) {i j : ℕ} (h : vv i = vv j) :
    i % k = j % k := by
  by_contra hne
  have h1 : vv (i % k) = vv (j % k) := by
    rw [periodic_mod_eq_p23 hper i, periodic_mod_eq_p23 hper j, h]
  exact hinj (i % k) (j % k) (Nat.mod_lt i hk0) (Nat.mod_lt j hk0) hne h1

/-- Successor respects residue equality (periodicity). -/
private theorem vvStep_p35 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) {i j : ℕ}
    (h : i % k = j % k) : vv (i + 1) = vv (j + 1) := by
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [← periodic_mod_eq_p23 hper (i + 1), ← periodic_mod_eq_p23 hper (j + 1), e1, e2, h]

/-- Predecessor respects successor-residue equality. -/
private theorem vvModPred_p35 {k : ℕ} {i j : ℕ} (hk0 : 0 < k)
    (h : (i + 1) % k = (j + 1) % k) : i % k = j % k := by
  have hik : i % k < k := Nat.mod_lt i hk0
  have hjk : j % k < k := Nat.mod_lt j hk0
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [e1, e2] at h
  have hs : i % k + 1 = j % k + 1 ∨ (i % k + 1 = k ∧ j % k + 1 = k) := by
    rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact Or.inl h
      · have h2 : j % k + 1 = k := by omega
        rw [h2, Nat.mod_self] at h
        exact absurd h (by omega)
    · have h2 : i % k + 1 = k := by omega
      rw [h2, Nat.mod_self] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact absurd h (by omega)
      · have h3 : j % k + 1 = k := by omega
        exact Or.inr ⟨h2, h3⟩
  omega

/-- Mod-k cancellation of a common summand. -/
private theorem modAddCancel_p35 {k a b c : ℕ} (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0] at h ⊢
    simpa [Nat.mod_zero] using h
  have hak : a % k < k := Nat.mod_lt a hk0
  have hbk : b % k < k := Nat.mod_lt b hk0
  have hck : c % k < k := Nat.mod_lt c hk0
  have e1 : (a + c) % k = (a % k + c % k) % k := by rw [Nat.add_mod]
  have e2 : (b + c) % k = (b % k + c % k) % k := by rw [Nat.add_mod]
  rw [e1, e2] at h
  have d1 : (a % k + c % k) % k = a % k + c % k ∨
      (a % k + c % k) % k + k = a % k + c % k := by
    rcases Nat.lt_or_ge (a % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : a % k + c % k = (a % k + c % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show a % k + c % k - k < k by omega)]
        omega)
  have d2 : (b % k + c % k) % k = b % k + c % k ∨
      (b % k + c % k) % k + k = b % k + c % k := by
    rcases Nat.lt_or_ge (b % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hY : b % k + c % k = (b % k + c % k - k) + k * 1 := by omega
        rw [hY, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show b % k + c % k - k < k by omega)]
        omega)
  rcases d1 with d1 | d1 <;> rcases d2 with d2 | d2 <;> omega

/-- Cyclic-fan dart determinism: the rho-successor of a first coordinate is
unique (`vv`-fan specialization of HOL `DETER_RHO_NODE`, local_lemmas.hl:3093;
the local-fan detour is replaced by periodicity + injectivity). -/
private theorem vvRhoDet_p35 {vv : ℕ → V3} {FF : Set (V3 × V3)} {k : ℕ}
    (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    {a b : V3} (hab : (a, b) ∈ FF) : rhoNode1 FF a = b := by
  refine epsFixed_p35 hab ?_
  intro y hy
  rw [← hFF] at hab hy
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hy
  have hia : vv i = a := congrArg Prod.fst hi
  have hib : vv (i + 1) = b := congrArg Prod.snd hi
  have hja : vv j = a := congrArg Prod.fst hj
  have hjy : vv (j + 1) = y := congrArg Prod.snd hj
  have hmod := vvModEq_p35 hk0 hper hinj (hia.trans hja.symm)
  have hstep := vvStep_p35 hper hmod
  rw [← hjy, ← hstep]
  exact hib

/-- Cyclic-fan dart determinism, mirror direction (`ivs_rho_node1`). -/
private theorem vvIvsDet_p35 {vv : ℕ → V3} {FF : Set (V3 × V3)} {k : ℕ}
    (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    {a b : V3} (hab : (a, b) ∈ FF) : ivsRhoNode1 FF b = a := by
  refine epsFixed_p35 hab ?_
  intro c hc
  rw [← hFF] at hab hc
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hc
  have hia : vv i = a := congrArg Prod.fst hi
  have hib : vv (i + 1) = b := congrArg Prod.snd hi
  have hjc : vv j = c := congrArg Prod.fst hj
  have hjb : vv (j + 1) = b := congrArg Prod.snd hj
  have hmod1 := vvModEq_p35 hk0 hper hinj (hib.trans hjb.symm)
  have hmod2 := vvModPred_p35 hk0 hmod1
  rw [← hjc, ← periodic_mod_eq_p23 hper j, ← hmod2, periodic_mod_eq_p23 hper i]
  exact hia

/-- The rho-orbit follows the cyclic `vv` ordering (HOL `VV_SUC_EQ_RHO_NODE`
conclusion, QKNVMLB.hl:4024). -/
private theorem vvOrbit_p35 {vv : ℕ → V3} {FF : Set (V3 × V3)} {k : ℕ}
    (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (a : V3) (p1 : ℕ) (hp1 : vv p1 = a) :
    ∀ m, (rhoNode1 FF)^[m] a = vv (m + p1) := by
  intro m
  induction m with
  | zero => simpa using hp1.symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have hdart : (vv (n + p1), vv (n + 1 + p1)) ∈ FF := by
        rw [← hFF]
        refine Set.mem_range.mpr ⟨n + p1, ?_⟩
        show (vv (n + p1), vv (n + p1 + 1)) = (vv (n + p1), vv (n + 1 + p1))
        rw [Nat.add_right_comm n p1 1]
      exact vvRhoDet_p35 hk0 hper hinj hFF hdart

/-! ### TECOXBMv2 step ladder (lkgrqui-tecoxbm-w2; QKNVMLB.hl 3730-4024)

Six-step ladder along the HOL `prove_by_refinement` subgoals: step01 the
k-case split, step02 the diagonal distance lower bound, step03 the window
membership, step04/05 the per-case wedge coverage (k = 4 resp. k = 5/6;
FROZEN RESIDUALS — blocked on the TECOXBM giant, see DISCHARGES), step06 the
final assembly (closed from step01 + the residuals' conclusions). -/

/-- step01 (HOL 3743-3772): a diagonal of a conforming system forces
`k ∈ {4,5,6}` (`SCS_K_PRIME_CASE_3` + `SCS_K_LE_6` + arithmetic). -/
theorem TECOXBMv2_step01_p35 (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : s.k = 4 ∨ s.k = 5 ∨ s.k = 6 := by
  have h3 : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have h6 : s.k ≤ 6 := hscs.2.2.1
  omega

/-! ### Sector-triangle kit (lkgrqui-tecoxbm3-w2; TECOXBM1 as the
sector-triangle core, TECOXBM.hl:1456)

Premise verification (this lane, 2026-10-28; full-tree grep + `#check`
probes, see probes/): `Kepler.Geom.wedge_eq_affGt` — the open lune
`wedge v0 v1 w1 w2 = affGt {v0,v1} {w1,w2}` (HOL `WEDGE_LUNE_GT`,
flyspeck.ml:3805) — is PROVED in `Kepler/Geom/LuneVolume.lean`, which
LocalAuto1 imports, hence in scope here.  The wedgeGe↔affGe bridge
re-carving budgeted at ≈300 ln by lkgrqui-tecoxbm2-w2 is therefore
unnecessary on the open-sector side; the closed-sector side needs no bridge
either: `wedgeGe` (Kepler.Text.wedgeGe, PackingAuto2:271) is by DEFINITION
the azimuth sandwich, so `wedgeSectorMem_p35` already gives the per-vertex
azimuth bounds.  The strictness engine below is a private copy of the
slicingfan azimuth-addition lemma (declared later in the file).

Ladder after this kit (PLAN.md §1): L0/L1 (open-triangle membership,
consecutive-vertex non-collinearity), L2 (lune rewrite), L5 (cone transfer),
L6 (strict azimuth sandwich) are CLOSED here, zero sorry.  L3 (flat-dart and
diag same-azimuth exclusions) and L4 (θ = π branch bookkeeping) remain ROOTs
and are collected in the single named residual `sectorTriCore_p35`, which
replaces the two per-case step04/05 residuals. -/

/-- The `{v0}`-singleton twin of `affGt_pair_iff`: open-triangle membership
(the LuneVolume `mem_affGt_two_pairs_iff` is private and unreachable). -/
private theorem triMemAffGt_p35 {v0 x y z : V3} (hx0 : x ≠ v0) (hy0 : y ≠ v0)
    (hxy : x ≠ y) :
    z ∈ affGt ({v0} : Set V3) {x, y} ↔
      ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ z - v0 = β • (x - v0) + γ • (y - v0) := by
  have hfin : ({v0} ∪ {x, y} : Set V3).Finite :=
    Set.Finite.insert v0 (Set.Finite.insert x (Set.finite_singleton y))
  have h3 : hfin.toFinset = ({v0, x, y} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have hsum : ∀ f : V3 → ℝ, ∑ w ∈ hfin.toFinset, f w = f v0 + f x + f y := by
    intro f
    simp only [h3]
    rw [Finset.sum_insert
        (show v0 ∉ (({x, y} : Finset V3)) from by simp [Ne.symm hx0, Ne.symm hy0])]
    rw [Finset.sum_insert
        (show x ∉ (({y} : Finset V3)) from by simp [hxy])]
    rw [Finset.sum_singleton]
    ring
  have hsumv : ∀ f : V3 → ℝ, ∑ w ∈ hfin.toFinset, f w • w
      = f v0 • v0 + f x • x + f y • y := by
    intro f
    simp only [h3]
    rw [Finset.sum_insert
        (show v0 ∉ (({x, y} : Finset V3)) from by simp [Ne.symm hx0, Ne.symm hy0])]
    rw [Finset.sum_insert
        (show x ∉ (({y} : Finset V3)) from by simp [hxy])]
    rw [Finset.sum_singleton]
    abel
  unfold affGt Affsign
  constructor
  · rintro ⟨f, hf, hz, hpos, hone⟩
    rw [hsumv f] at hz
    rw [hsum f] at hone
    have hfx : 0 < f x := hpos x (by simp)
    have hfy : 0 < f y := hpos y (by simp)
    refine ⟨f x, f y, hfx, hfy, ?_⟩
    have hf0 : f v0 = 1 - f x - f y := by linarith
    rw [hz, hf0]
    module
  · rintro ⟨β, γ, hβ, hγ, hz⟩
    refine ⟨fun v => if v = x then β else if v = y then γ else 1 - β - γ, hfin,
      ?_, ?_, ?_⟩
    · rw [hsumv _]
      rw [show z = (z - v0) + v0 from (sub_add_cancel z v0).symm, hz]
      simp only [if_neg (Ne.symm hx0), if_neg (Ne.symm hy0),
        if_neg (Ne.symm hxy), if_true, if_false]
      module
    · intro w hw
      simp only []
      rcases Set.mem_insert_iff.mp hw with h | h
      · rw [if_pos h]; exact hβ
      · have h2 : w = y := Set.mem_singleton_iff.mp h
        rw [if_neg (fun he => hxy (he.symm.trans h2)), if_pos h2]
        exact hγ
    · rw [hsum _]
      simp only [if_neg (Ne.symm hx0), if_neg (Ne.symm hy0),
        if_neg (Ne.symm hxy), if_true, if_false]
      ring

/-- The two-pair twin (`mem_affGt_two_pairs_iff` shape): membership in
`affGt {v0, v1} {x, y}` with strictly positive `x`/`y` coefficients and a
free axis coefficient. -/
private theorem pairMemAffGt_p35 {v0 v1 x y z : V3} (hv01 : v0 ≠ v1)
    (hx0 : x ≠ v0) (hx1 : x ≠ v1) (hy0 : y ≠ v0) (hy1 : y ≠ v1) (hxy : x ≠ y) :
    z ∈ affGt ({v0, v1} : Set V3) {x, y} ↔
      ∃ β γ δ : ℝ, 0 < β ∧ 0 < γ ∧
        z - v0 = β • (x - v0) + γ • (y - v0) + δ • (v1 - v0) := by
  have hfin : ({v0, v1} ∪ {x, y} : Set V3).Finite :=
    (Set.Finite.insert v0 (Set.finite_singleton v1)).union
      (Set.Finite.insert x (Set.finite_singleton y))
  have h3 : hfin.toFinset = ({v0, v1, x, y} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsum : ∀ f : V3 → ℝ, ∑ w ∈ hfin.toFinset, f w
      = f v0 + f v1 + f x + f y := by
    intro f
    simp only [h3]
    rw [Finset.sum_insert
        (show v0 ∉ (({v1, x, y} : Finset V3)) from by
          simp [hv01, Ne.symm hx0, Ne.symm hy0])]
    rw [Finset.sum_insert
        (show v1 ∉ (({x, y} : Finset V3)) from by simp [Ne.symm hx1, Ne.symm hy1])]
    rw [Finset.sum_insert
        (show x ∉ (({y} : Finset V3)) from by simp [hxy])]
    rw [Finset.sum_singleton]
    ring
  have hsumv : ∀ f : V3 → ℝ, ∑ w ∈ hfin.toFinset, f w • w
      = f v0 • v0 + f v1 • v1 + f x • x + f y • y := by
    intro f
    simp only [h3]
    rw [Finset.sum_insert
        (show v0 ∉ (({v1, x, y} : Finset V3)) from by
          simp [hv01, Ne.symm hx0, Ne.symm hy0])]
    rw [Finset.sum_insert
        (show v1 ∉ (({x, y} : Finset V3)) from by simp [Ne.symm hx1, Ne.symm hy1])]
    rw [Finset.sum_insert
        (show x ∉ (({y} : Finset V3)) from by simp [hxy])]
    rw [Finset.sum_singleton]
    abel
  unfold affGt Affsign
  constructor
  · rintro ⟨f, hf, hz, hpos, hone⟩
    rw [hsumv f] at hz
    rw [hsum f] at hone
    have hfx : 0 < f x := hpos x (by simp)
    have hfy : 0 < f y := hpos y (by simp)
    refine ⟨f x, f y, f v1, hfx, hfy, ?_⟩
    have hf0 : f v0 = 1 - f v1 - f x - f y := by linarith
    rw [hz, hf0]
    module
  · rintro ⟨β, γ, δ, hβ, hγ, hz⟩
    refine ⟨fun v => if v = x then β else if v = y then γ else
      if v = v1 then δ else 1 - β - γ - δ, hfin, ?_, ?_, ?_⟩
    · rw [hsumv _]
      rw [show z = (z - v0) + v0 from (sub_add_cancel z v0).symm, hz]
      simp only [if_neg (Ne.symm hx0), if_neg (Ne.symm hy0), if_neg hv01,
        if_neg (Ne.symm hx1), if_neg (Ne.symm hy1), if_neg (Ne.symm hxy),
        if_true, if_false]
      module
    · intro w hw
      simp only []
      rcases Set.mem_insert_iff.mp hw with h | h
      · rw [if_pos h]; exact hβ
      · have h2 : w = y := Set.mem_singleton_iff.mp h
        rw [if_neg (fun he => hxy (he.symm.trans h2)), if_pos h2]
        exact hγ
    · rw [hsum _]
      simp only [if_neg (Ne.symm hx0), if_neg (Ne.symm hy0), if_neg hv01,
        if_neg (Ne.symm hx1), if_neg (Ne.symm hy1), if_neg (Ne.symm hxy),
        if_true, if_false]
      ring

/-- A successor residue is a different residue once `2 ≤ k` (private twin;
the later `wedgeModEqAddCancel_p35` cannot be referenced here). -/
private theorem triModNe_p35 {k a : ℕ} (hk2 : 2 ≤ k) : a % k ≠ (a + 1) % k := by
  intro he
  have hmod : (a + 1) % k = (a % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1:ℕ) < k by omega)]
  rw [hmod] at he
  have hlt : a % k < k := Nat.mod_lt a (by omega)
  rcases Nat.lt_or_ge (a % k + 1) k with h | h
  · rw [Nat.mod_eq_of_lt h] at he
    omega
  · have h1 : a % k + 1 = k := by omega
    rw [h1, Nat.mod_self] at he
    omega

/-- Ladder L1: consecutive window vertices are never collinear with the
origin.  Distance bounds are exactly the `NONPARALLEL_BALL_ANNULUS` inputs:
annulus norms (`hBB.1`), `2 ≤ dist` (the a-bound at residue indices, so no
`Periodic2` transport of `s.a` is needed) and `dist ≤ cstab` (the `isScsV39`
consecutive b-bound, direct at `(j, j+1)`). -/
private theorem vvNonCollStep_p35 {s : ScsV39} {vv : ℕ → V3} (hscs : isScsV39 s)
    (hBB : BBsV39 s vv) (hk3 : 3 < s.k) (i : ℕ) :
    ¬ Collinear3 0 (vv i) (vv (i + 1)) ∧
      ¬ Collinear3 0 (vv (i + s.k - 1)) (vv i) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk2 : 2 ≤ s.k := by omega
  have hper : Periodic vv s.k := hBB.2.1
  have hann : ∀ j : ℕ, vv j ∈ ballAnnulus := fun j =>
    hBB.1 (Set.mem_range.mpr ⟨j, rfl⟩)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hage, -, hbc, -, -, -⟩ := hscs
  have hstep : ∀ j : ℕ, ¬ Collinear3 0 (vv j) (vv (j + 1)) := by
    intro j
    have hres := hage (j % s.k) ((j + 1) % s.k)
      ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, triModNe_p35 hk2⟩
    have hab := (hBB.2.2.1 (j % s.k) ((j + 1) % s.k)).1
    have hab2 := (hBB.2.2.1 j (j + 1)).2
    have hveq : dist (vv (j % s.k)) (vv ((j + 1) % s.k))
        = dist (vv j) (vv (j + 1)) := by
      rw [periodic_mod_eq_p23 hper j, periodic_mod_eq_p23 hper (j + 1)]
    exact NONPARALLEL_BALL_ANNULUS (hann j) (hann (j + 1))
      (by
        calc (2:ℝ) ≤ s.a (j % s.k) ((j + 1) % s.k) := hres
          _ ≤ dist (vv (j % s.k)) (vv ((j + 1) % s.k)) := hab
          _ = dist (vv j) (vv (j + 1)) := hveq
          _ = ‖vv j - vv (j + 1)‖ := dist_eq_norm _ _)
      (hab2.trans (hbc j hk3))
  refine ⟨hstep i, ?_⟩
  have hpred := hstep (i + s.k - 1)
  have hik : vv (i + s.k - 1 + 1) = vv i := by
    rw [show i + s.k - 1 + 1 = i + s.k from by omega]
    rw [← periodic_mod_eq_p23 hper (i + s.k), Nat.add_mod_right]
    exact periodic_mod_eq_p23 hper i
  rw [hik] at hpred
  exact hpred

/-- FAN-free azimuth addition (private copy of the slicingfan
`azimAddTriple_p35`, which is declared later in the file; proof verbatim,
with the FAN hypothesis replaced by the three fan6-type non-collinearity
facts, which is all it consumes). -/
private theorem triAzimAdd_p35 {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hu : ¬ Collinear3 x v u) (h1 : ¬ Collinear3 x v w1) (h2 : ¬ Collinear3 x v w2)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr hxv)
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hu h1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hu h2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec h1 h2 hon hax hxv
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hc3 : azim x v u w2
      = azim x v u w1 + azim x v w1 w2 + (n:ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hnpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-- Ladder L5 (cone transfer): a positive combination of the two diag rays
lies in the open wedge they span with the axis, once the ray pair is
strictly placed (`0 < azim < π`); the lune rewrite is the imported
`Kepler.Geom.wedge_eq_affGt` (HOL `WEDGE_LUNE_GT`) and the membership the
two-pair characterization with zero axis coefficient. -/
private theorem coneMem_p35 {v0 ax u w t : V3} (haxu : ¬ Collinear3 v0 ax u)
    (haxw : ¬ Collinear3 v0 ax w) (huw : u ≠ w)
    (hθ0 : 0 < azim v0 ax u w) (hθπ : azim v0 ax u w < Real.pi)
    (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (ht : t - v0 = β • (u - v0) + γ • (w - v0)) :
    t ∈ wedge v0 ax u w := by
  have hv01 : v0 ≠ ax := fun he => haxu (collinear3_of_eq he.symm)
  have hrew : wedge v0 ax u w = affGt ({v0, ax} : Set V3) {u, w} :=
    wedge_eq_affGt haxu haxw hθ0 hθπ
  rw [hrew]
  refine (pairMemAffGt_p35 (v0 := v0) (v1 := ax) (x := u) (y := w) (z := t)
    hv01 (fun he => haxu (collinear3_pair_left he))
    (fun he => haxu (collinear3_pair_right he))
    (fun he => haxw (collinear3_pair_left he))
    (fun he => haxw (collinear3_pair_right he)) huw).mpr
    ⟨β, γ, 0, hβ, hγ, by rw [ht]; module⟩

/-- Ladder L6 (strict azimuth sandwich): with `p` at positive azimuth from
the sector start ray `b`, `q` further counterclockwise at total angle ≤ π,
and `r` strictly between `p` and `q` as seen from the ray through `p`, `r`
is strictly between `b` and `q`.  Route: two azimuth-addition instances
(the private copy `triAzimAdd_p35`) with the counterclockwise order resolved
by `azim_compl` — the reversed order would force `azim(b,p) > π` while
`azim(b,p) ≤ azim(b,q) ≤ π`. -/
private theorem azimSandwich_p35 {v0 ax b p q r : V3}
    (hvb : v0 ≠ ax) (haxb : ¬ Collinear3 v0 ax b) (haxp : ¬ Collinear3 v0 ax p)
    (haxq : ¬ Collinear3 v0 ax q) (haxr : ¬ Collinear3 v0 ax r)
    (hbp : 0 < azim v0 ax b p)
    (hbpq : azim v0 ax b p ≤ azim v0 ax b q)
    (hbqπ : azim v0 ax b q ≤ Real.pi)
    (hpr0 : 0 < azim v0 ax p r) (hprq : azim v0 ax p r < azim v0 ax p q) :
    0 < azim v0 ax b r ∧ azim v0 ax b r < azim v0 ax b q := by
  have hbp0 : 0 ≤ azim v0 ax b p := azim_nonneg v0 ax b p
  have hprne : azim v0 ax p r ≠ 0 := ne_of_gt hpr0
  have haddq : azim v0 ax b q = azim v0 ax b p + azim v0 ax p q :=
    triAzimAdd_p35 (Ne.symm hvb) haxb haxp haxq hbpq
  have horder : azim v0 ax b p ≤ azim v0 ax b r := by
    rcases lt_or_ge (azim v0 ax b r) (azim v0 ax b p) with hlt | hge
    · exfalso
      have haddr : azim v0 ax b p = azim v0 ax b r + azim v0 ax r p :=
        triAzimAdd_p35 (Ne.symm hvb) haxb haxr haxp hlt.le
      have hcompl : azim v0 ax r p = 2 * Real.pi - azim v0 ax p r := by
        rw [azim_compl haxp haxr, if_neg hprne]
      have hbr0 : (0:ℝ) ≤ azim v0 ax b r := azim_nonneg v0 ax b r
      have hbpπ : Real.pi < azim v0 ax b p := by
        rw [haddr, hcompl]
        linarith
      linarith
    · exact hge
  have haddr : azim v0 ax b r = azim v0 ax b p + azim v0 ax p r :=
    triAzimAdd_p35 (Ne.symm hvb) haxb haxp haxr horder
  refine ⟨by rw [haddr]; linarith, ?_⟩
  rw [haddr, haddq]
  linarith

/-- Pair-set enumeration (local copy of the mid-kit `pairMem_p35`; the mid
helper is declared later in the file and cannot be referenced here). -/
private theorem wedgePairMem_p35 {a w b c : V3} (h : ({a, w} : Set V3) = {b, c}) :
    (a = b ∨ a = c) ∧ (w = b ∨ w = c) := by
  have m1 : a ∈ ({b, c} : Set V3) := by rw [← h]; simp
  have m2 : w ∈ ({b, c} : Set V3) := by rw [← h]; simp
  refine ⟨?_, ?_⟩
  · rcases Set.mem_insert_iff.mp m1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  · rcases Set.mem_insert_iff.mp m2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Set.mem_singleton_iff.mp h2)

/-- Mod-k cancellation of a common summand (local copy of the mid-kit
`modEqAddCancel_p35`, which is declared later in the file). -/
private theorem wedgeModEqAddCancel_p35 {k i t : ℕ} (hk0 : 0 < k)
    (h : i % k = (i + t) % k) : t % k = 0 := by
  have h1 : (i % k + t % k) % k = i % k := by
    have e : (i % k + t % k) % k = (i + t) % k := by rw [Nat.add_mod i t k]
    rw [e, h]
  have hik : i % k < k := Nat.mod_lt i hk0
  have htk : t % k < k := Nat.mod_lt t hk0
  have d : (i % k + t % k) % k = i % k + t % k ∨
      (i % k + t % k) % k + k = i % k + t % k := by
    rcases Nat.lt_or_ge (i % k + t % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : i % k + t % k = (i % k + t % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show i % k + t % k - k < k by omega)]
        omega)
  rcases d with d | d <;> omega

/-- `k`-shifted indices carry the same `vv`-value (local copy of
`vvAddK_p35`, declared later in the file). -/
private theorem wedgeVvAddK_p35 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (i : ℕ) : vv (i + k) = vv i := by
  rw [← periodic_mod_eq_p23 hper (i + k), Nat.add_mod_right]
  exact periodic_mod_eq_p23 hper i

/-- The vertex and its cyclic successor differ once `3 ≤ k` (local copy of
`vvNeStep_p35`, declared later in the file). -/
private theorem wedgeVvNeStep_p35 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have h := wedgeModEqAddCancel_p35 hk0 (i := i) (t := 1) (vvModEq_p35 hk0 hper hinj hh)
  have h1 : (1:ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Edge membership in the cyclic edge set: the two neighbours (local copy
of `vvMemEdge_p35`, declared later in the file, routed through the wedge
copies above and the preceding `vvModEq_p35`/`vvStep_p35`/`vvModPred_p35`). -/
private theorem wedgeVvMemEdge_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) (w : V3) :
    w ∈ ee (vv i) E ↔ w = vv (i + k - 1) ∨ w = vv (i + 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hnosing : ∀ j : ℕ, vv j ≠ vv (j + 1) := fun j => wedgeVvNeStep_p35 hk3 hper hinj j
  show {vv i, w} ∈ E ↔ _
  constructor
  · intro hw
    rw [← hE] at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨ha, hwbc⟩ := wedgePairMem_p35 hj.symm
    rcases ha with hai | hai
    · have hmod : i % k = j % k := vvModEq_p35 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · exfalso
        have hsucc : vv j = vv (j + 1) := by
          have m : vv (j + 1) ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
          rw [hw1, hai] at m
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
          exact m.elim (fun h => h.symm) (fun h => h.symm)
        exact absurd hsucc (hnosing j)
      · refine Or.inr ?_
        rw [hw1, vvStep_p35 hper hmod]
    · have hmod1 : i % k = (j + 1) % k := vvModEq_p35 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · refine Or.inl ?_
        have hpred : (i + k - 1) % k = j % k := by
          have hstep : (i + k - 1 + 1) % k = (j + 1) % k := by
            rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
            exact hmod1
          exact vvModPred_p35 hk0 hstep
        rw [hw1, ← periodic_mod_eq_p23 hper j, ← hpred,
          periodic_mod_eq_p23 hper (i + k - 1)]
      · exfalso
        rw [← hai] at hw1
        have m : vv j ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
        rw [hw1] at m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
        have hvj : vv j = vv i := m.elim id id
        exact absurd (hvj.trans hai) (hnosing j)
  · rintro (rfl | rfl)
    · show {vv i, vv (i + k - 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i + k - 1, by
        show {vv (i + k - 1), vv (i + k - 1 + 1)} = {vv i, vv (i + k - 1)}
        rw [show i + k - 1 + 1 = i + k from by omega, wedgeVvAddK_p35 hper i]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto⟩
    · show {vv i, vv (i + 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i, rfl⟩

/-- The two-element `azimCycle`: on a neighbour set `{a, p}` (with `a ≠ p`)
the cycle successor of `p` is `a` (local copy of the bridge kit's
`azimCycle2_p35`, declared later in the file). -/
private theorem wedgeAzimCycle2_p35 {a p : V3} {W : Set V3} (v w : V3) (hap : a ≠ p)
    (hW : W = {a, p}) : azimCycle_p3 W v w p = a := by
  have hsub : ¬(W ⊆ {p}) := by
    intro hc
    exact hap (hc (by rw [hW]; simp))
  rw [azimCycle_p3, if_neg hsub]
  refine epsFixed_p35 ?_ ?_
  · rw [hW]
    refine ⟨hap, by simp, ?_⟩
    intro q hq hqp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with h | h
    · subst h
      exact Or.inr ⟨rfl, le_refl _⟩
    · exact absurd h hqp
  · intro y hy
    rw [hW] at hy
    obtain ⟨hy1, hy2, -⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
    rcases hy2 with h | h
    · exact h
    · exact absurd h hy1

/-- The cyclic predecessor and successor of `vv i` differ once `3 ≤ k`
(predecessor step of `vvInangleEq_p35`, split out for reuse). -/
private theorem wedgeCyclicNC_p35 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv (i + k - 1) ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hmod := vvModEq_p35 hk0 hper hinj hh
  have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
    have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
      rw [Nat.add_mod]
    have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by
      rw [Nat.add_mod]
    rw [g1, g2, hmod]
  rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
  have h3 := wedgeModEqAddCancel_p35 hk0 (i := i) (t := 2) hplus
  have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
  omega

/-- The two-point neighbour set at `vv i` (the `EE_p3` rendering of
`vvMemEdge_p35`). -/
private theorem wedgeCyclicEE_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    EE_p3 (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
  ext w
  exact wedgeVvMemEdge_p35 hk3 hper hinj hE i w

/-- The fan successor at a cyclic dart is the cyclic predecessor
(`sigmaFan` rendering of the `azimCycle2_p35` two-point cycle; twin of the
`hsucc` step inside `vvInangleEq_p35`). -/
private theorem wedgeCyclicSigma_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    Kepler.Text.Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1)) = vv (i + k - 1) := by
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := wedgeCyclicNC_p35 hk3 hper hinj i
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact wedgeVvMemEdge_p35 hk3 hper hinj hE i w
  have hsoe : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E = ee (vv i) E := by
    ext z
    show ({vv i, z} ∈ E ∧ z ∈ (Set.univ : Set V3)) ↔ {vv i, z} ∈ E
    simp
  have hne2 : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ≠ {vv (i + 1)} := by
    intro hc
    have hmem : vv (i + k - 1) ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E := by
      rw [hsoe, hee]
      simp
    rw [hc, Set.mem_singleton_iff] at hmem
    exact hstep hmem
  simp only [Kepler.Text.Fan.sigmaFan, if_neg hne2]
  refine epsFixed_p35 ?_ ?_
  · refine ⟨?_, hstep, ?_⟩
    · rw [hsoe, hee]
      simp
    · intro w1 hw1 hw1ne
      rw [hsoe, hee] at hw1
      rcases Set.mem_insert_iff.mp hw1 with h | h
      · rw [h]
      · exact absurd h hw1ne
  · intro z hz
    obtain ⟨hz1, hz2, -⟩ := hz
    rw [hsoe, hee] at hz1
    rcases Set.mem_insert_iff.mp hz1 with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hz2

/-- The cyclic dart's open fan wedge, concretized: at every dart of the
`k`-window cycle the `wedgeInFanGt_p3` case split resolves through the
two-point neighbour set (`TECOXBM.hl` wedge machinery specialized to the
cyclic fan; k ≥ 3). -/
theorem wedgeCyclic_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    wedgeInFanGt_p3 (vv i, vv (i + 1)) E =
      Kepler.Geom.wedge 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := wedgeCyclicNC_p35 hk3 hper hinj i
  have hee : EE_p3 (vv i) E = {vv (i + k - 1), vv (i + 1)} :=
    wedgeCyclicEE_p35 hk3 hper hinj hE i
  have hncard : 1 < (EE_p3 (vv i) E).ncard := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  simp only [wedgeInFanGt_p3]
  rw [if_pos hncard, wedgeAzimCycle2_p35 (v := 0) (w := vv i) hstep hee]

/-- The closed-sector side of the convex local fan at a cyclic dart: every
window vertex lies in the closed azimuth sector at the dart, and the sector
angle is at most `π` (the `ConvexLocalFan` conjuncts with the two-point
neighbour resolution of `azimInFan`/`wedgeInFanGe`). -/
theorem wedgeSectorMem_p35 {vv : ℕ → V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) :
    (∀ x ∈ Set.range vv, x ∈ wedgeGe 0 (vv i) (vv (i + 1)) (vv (i + k - 1))) ∧
      azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi := by
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := wedgeCyclicNC_p35 hk3 hper hinj i
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact wedgeVvMemEdge_p35 hk3 hper hinj hE i w
  have hncard : 1 < (ee (vv i) E).ncard := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hsig : Kepler.Text.Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1))
      = vv (i + k - 1) := wedgeCyclicSigma_p35 hk3 hper hinj hE i
  obtain ⟨-, hsec⟩ := hfan
  obtain ⟨hsigaz, hsige⟩ := hsec (vv i, vv (i + 1))
    (by rw [← hFF]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  constructor
  · intro x hx
    have hx2 := hsige hx
    rw [wedgeInFanGe, if_pos hncard, hsig] at hx2
    exact hx2
  · rw [azimInFan, if_pos hncard, hsig] at hsigaz
    exact hsigaz

/-! ## sector-triangle residual kit (lkgrqui-sectortri-w2, 2026-10-28)

The fan-theory input is ALREADY a hypothesis: `BBsV39` (LocalAuto1:411)
carries `(s.k ≤ 3 ∨ ConvexLocalFan (range vv) edges darts)` as its last
conjunct, and the Kepler.Text.Fan chapter (in the import closure via
LocalAuto1/3/4/PackingAuto2; `#print axioms` standard three, probe
lkgrqui-sectortri-w2/probes/probe1_fanvis.lean) supplies the neighbor
azimuth injectivity that kills the flat-dart branch. -/

/-- Unordered pair swap. -/
private theorem pairSwap_p35 {α : Type*} [DecidableEq α] (x y : α) :
    {x, y} = ({y, x} : Set α) := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- F0a: a diagonal forces `4 ≤ s.k` (for `k = 3` the three forbidden
residue equalities of `scsDiag` exhaust all residues). -/
private theorem diagKGe4_p35 {s : ScsV39} {p q : ℕ} (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : 4 ≤ s.k := by
  by_cases hk : s.k ≤ 3
  · exfalso
    have hk3 : 3 ≤ s.k := hscs.2.1
    have h3 : s.k = 3 := by omega
    rw [h3] at hdiag
    obtain ⟨h1, h2, h3'⟩ := hdiag
    have hp3 : p % 3 < 3 := Nat.mod_lt p (by omega)
    have hq3 : q % 3 < 3 := Nat.mod_lt q (by omega)
    have hpv : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hqv : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hpv with hp' <;> rcases hqv with hq' <;> omega
  · omega

/-- F0b: the fan structure extracted from `BBsV39`'s last conjunct for
`k ≥ 4` (the `s.k ≤ 3` guard is excluded by the diagonal). -/
private theorem fanOfBB_p35 {s : ScsV39} {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hk4 : 4 ≤ s.k) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) :
    Kepler.Text.Fan.FAN 0 (Set.range vv) E := by
  rcases hBB.2.2.2 with hle | hcl
  · omega
  · subst hE
    subst hFF
    exact hcl.1.1

/-- F0c: both dart edges at dart `i` (the second via periodicity). -/
private theorem dartEdgeMems_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    {vv i, vv (i + 1)} ∈ E ∧ {vv i, vv (i + k - 1)} ∈ E := by
  have h1 : ({vv i, vv (i + 1)} : Set V3) ∈
      Set.range (fun j => ({vv j, vv (j + 1)} : Set V3)) := ⟨i, rfl⟩
  have h2 : ({vv i, vv (i + k - 1)} : Set V3) ∈
      Set.range (fun j => ({vv j, vv (j + 1)} : Set V3)) := by
    refine ⟨i + k - 1, ?_⟩
    show ({vv (i + k - 1), vv (i + k - 1 + 1)} : Set V3) = {vv i, vv (i + k - 1)}
    have hk1 : (i + k - 1) + 1 = i + k := by omega
    have hk : vv ((i + k - 1) + 1) = vv i := by rw [hk1]; exact hper i
    rw [pairSwap_p35 (vv (i + k - 1)) (vv ((i + k - 1) + 1)), hk]
  rw [hE] at h1 h2
  exact ⟨h1, h2⟩

/-- L3a (flat-dart exclusion, CLOSED): the sector angle at every dart of
the cyclic fan is nonzero — the two dart neighbors would otherwise be
distinct neighbors at azimuth 0, contradicting the fan's neighbor
azimuth injectivity (`Fan.unique_azim0_point_fan`). -/
private theorem dartSpanNeCyc_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ)
    (hfan : Kepler.Text.Fan.FAN 0 (Set.range vv) E) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≠ 0 := by
  obtain ⟨hab, hac⟩ := dartEdgeMems_p35 hk3 hper hE i
  intro h0
  exact wedgeCyclicNC_p35 hk3 hper hinj i
    (Kepler.Text.Fan.unique_azim0_point_fan (x := 0) (v := vv i)
      (u := vv (i + 1)) (w := vv (i + k - 1)) (V := Set.range vv) (E := E)
      hfan hab hac h0).symm

/-- Azimuth-of-axis-point vanishes (the collinear disjunct of `azim`). -/
private theorem azimAxis_p35 {a b x : V3} (h : Collinear3 0 a x) :
    azim 0 a b x = 0 := by
  rw [azim, if_pos (Or.inr h)]

/-! ## PlaneMiss corner kit (lkgrqui-planemiss-w3, 2026-10-28)

Shared closed core for the four azimuth corners of `sectorTriPlaneMiss_p35`
(HOL TECOXBM.hl:311 `AFF_GT_INTER_AFF_SY` strictness core).  The corners
render as: C1/C3/C4 put both diagonal endpoints in the dart face plane
`aff {0, vv i, vv (i+1)}`, C2 in the span face plane `aff {0, vv i, vv (i+k-1)}`
(Kepler `azim` vanishes on the whole axis line, so the = 0 rendering is a
plane span, not a ray); and the whole ring sits in the closed half-space of
the dart face (azimuth sandwich `[0, θ] ⊆ [0, π]` through the sin bridge).
The residual exclusion (`planeCrowding`: two distinct, mutually non-adjacent
ring vertices inside one dart-face side) is the remaining named root —
cf. HOL `WEDGE_GE_EQ_AFF_GE` + `CROSS_DOT_POS_SY` σ-cycle iteration. -/

/-- dot with a right smul factor (local bridge for the cross-pairing). -/
private theorem pmDotSmul_p35 (c : ℝ) (f g : Fin 3 → ℝ) :
    g ⬝ᵥ (c • f) = c * (g ⬝ᵥ f) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- The cross pairing vanishes along the axis line. -/
private theorem pmCrossAxisZero_p35 {a b x : V3} (hx : ∃ c : ℝ, x - 0 = c • (a - 0)) :
    (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) = 0 := by
  obtain ⟨c, hc⟩ := hx
  have h2 : x - 0 = c • (a - 0) := hc
  simp only [sub_zero] at h2
  have hcoe : ((x : V3) : Fin 3 → ℝ) = c • ((a : V3) : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) h2
  rw [hcoe, pmDotSmul_p35, dotProduct_comm,
    show crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)
        = -(crossProduct (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)) from
      (cross_anticomm (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)).symm,
    dotProduct_neg, dot_cross_self (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)]
  simp

/-- Half-space bound at a dart (open-sector case; sin bridge). -/
private theorem pmCrossGe_p35 {y z x : V3} (hcolx : ¬ Collinear3 0 y x)
    (hnc : ¬ Collinear3 0 y z)
    (h0 : 0 ≤ azim 0 y z x) (hπ : azim 0 y z x ≤ Real.pi) :
    0 ≤ (crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  have h := cross_dot_fully_surrounded_ge_fan (x := 0) (v1 := y) (v := z) (u1 := x)
    hcolx hnc h0 hπ
  simpa [sub_zero] using h

/-- Half-space bound at a dart (combined, collinear fallback included):
every point whose azimuth from the dart lies in `[0, π]` sits in the closed
`{y × z ≥ 0}` half-space. -/
private theorem pmCrossGeAll_p35 {y z x : V3} (hvi0 : y ≠ 0)
    (hnc : ¬ Collinear3 0 y z)
    (h0 : 0 ≤ azim 0 y z x) (hπ : azim 0 y z x ≤ Real.pi) :
    0 ≤ (crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  by_cases hcol : Collinear3 0 y x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := y) (w1 := x) hvi0).mp hcol
    have h2 : x - 0 = c • (y - 0) := hc
    simp only [sub_zero] at h2
    rw [show ((x : V3) : Fin 3 → ℝ) = c • ((y : V3) : Fin 3 → ℝ) from
      congrArg (fun w : V3 => (w : Fin 3 → ℝ)) h2, pmDotSmul_p35, dotProduct_comm,
      show crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)
          = -(crossProduct (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)) from
        (cross_anticomm (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)).symm,
      dotProduct_neg, dot_cross_self (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)]
    simp
  · exact pmCrossGe_p35 hcol hnc h0 hπ

/-- Azimuth zero at a dart renders the point in the dart face plane span. -/
private theorem pmRender0_p35 {y z x : V3} (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hnc : ¬ Collinear3 0 y z) (h : azim 0 y z x = 0) :
    ∃ s t : ℝ, x - 0 = s • (y - 0) + t • (z - 0) := by
  by_cases hcol : Collinear3 0 y x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := y) (w1 := x) hy0).mp hcol
    exact ⟨c, 0, by rw [hc, zero_smul, add_zero]⟩
  · obtain ⟨c, hc, h2, hh⟩ :=
      (affGt_pair_iff (v0 := 0) (v1 := y) (x := z) (y := x) (Ne.symm hy0) hz0
        (fun he => hnc (by rw [he]; exact collinear3_pair_right rfl))).mp
      ((azim_eq_zero_iff_alt (v0 := 0) (v1 := y) (w := z) (x := x) hnc hcol).mp h)
    exact ⟨h2, c, by rw [hh]; module⟩

/-- Azimuth equal to the sector span renders the point in the span face
plane span (HOL `AZIM_EQ`-route through `azim_eq_azim_iff`). -/
private theorem pmRenderSpan_p35 {y z sg x : V3} (hy0 : y ≠ 0) (hsg0 : sg ≠ 0)
    (hncz : ¬ Collinear3 0 y z) (hncsg : ¬ Collinear3 0 y sg)
    (h : azim 0 y z x = azim 0 y z sg) :
    ∃ s t : ℝ, x - 0 = s • (y - 0) + t • (sg - 0) := by
  by_cases hcol : Collinear3 0 y x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := y) (w1 := x) hy0).mp hcol
    exact ⟨c, 0, by rw [hc, zero_smul, add_zero]⟩
  · obtain ⟨c, hc, h2, hh⟩ :=
      (affGt_pair_iff (v0 := 0) (v1 := y) (x := sg) (y := x) (Ne.symm hy0) hsg0
        (fun he => hncsg (by rw [he]; exact collinear3_pair_right rfl))).mp
      ((azim_eq_azim_iff (v0 := 0) (v1 := y) (w := z) (x := sg) (y := x)
        hncz hncsg hcol).mp h.symm)
    exact ⟨h2, c, by rw [hh]; module⟩

/-- Two distinct fan vertices on the same positive ray from the fan center
contradict `fan7` (singleton instance `affGe {0} {v} ∩ affGe {0} {u} =
affGe {0} ∅` while the ray `v ≠ 0` sits on the left). -/
private theorem pmSameRayKill_p35 {v u : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : Kepler.Text.Fan.FAN 0 V E) (hv : v ∈ V) (hu : u ∈ V)
    (hvu : v ≠ u) (hv0 : v ≠ 0)
    (h : ∃ t : ℝ, 0 < t ∧ u - 0 = t • (v - 0)) : False := by
  obtain ⟨t, ht, hue⟩ := h
  have h7 : Kepler.Text.Fan.fan7 0 V E := hfan.2.2.2.2.2
  have he1 : ({v} : Set V3) ∈ E ∪ {s : Set V3 | ∃ w ∈ V, s = {w}} :=
    Set.mem_union_right _ (Set.mem_setOf.mpr ⟨v, hv, rfl⟩)
  have he2 : ({u} : Set V3) ∈ E ∪ {s : Set V3 | ∃ w ∈ V, s = {w}} :=
    Set.mem_union_right _ (Set.mem_setOf.mpr ⟨u, hu, rfl⟩)
  have hEq := h7 {v} he1 {u} he2
  have htne : t ≠ 0 := ne_of_gt ht
  have hve : v - 0 = t⁻¹ • (u - 0) := by
    rw [hue, smul_smul, inv_mul_cancel₀ htne, one_smul]
  have hm1 : v ∈ affGe ({0} : Set V3) ({v} : Set V3) := by
    refine ⟨fun z => if z = v then 1 else 0, by simp, ?_, ?_, ?_⟩
    · simp [hv0]
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw]; simp
    · simp
  have hv2 : v = t⁻¹ • u := by simpa using hve
  have hu0u : u ≠ 0 := by
    intro hz
    apply hv0
    rw [hv2, hz, smul_zero]
  have hfinU : (({0} ∪ {u} : Set V3)).Finite := by simp
  have htf2 : hfinU.toFinset = ({0, u} : Finset V3) := by
    ext z
    simp
    tauto
  have hmem0 : (0:V3) ∉ ({u} : Finset V3) := fun h =>
    hu0u (Finset.mem_singleton.mp h).symm
  have hne0 : ¬ ((0:V3) = u) := fun h => hu0u h.symm
  have hb0 : (fun z : V3 => if z = u then t⁻¹ else 1 - t⁻¹) 0 = 1 - t⁻¹ := by
    show (if (0:V3) = u then (t⁻¹:ℝ) else (1 - t⁻¹:ℝ)) = 1 - t⁻¹
    rw [if_neg hne0]
  have hbu : (fun z : V3 => if z = u then t⁻¹ else 1 - t⁻¹) u = t⁻¹ := by
    show (if (u:V3) = u then (t⁻¹:ℝ) else (1 - t⁻¹:ℝ)) = t⁻¹
    rw [if_pos rfl]
  have hm2 : v ∈ affGe ({0} : Set V3) ({u} : Set V3) := by
    refine ⟨fun z => if z = u then t⁻¹ else 1 - t⁻¹, hfinU, ?_, ?_, ?_⟩
    · rw [htf2, Finset.sum_insert hmem0, Finset.sum_singleton,
        hb0, hbu, smul_zero, zero_add]
      exact hv2
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rw [hw]
      have hbe : (fun z : V3 => if z = u then t⁻¹ else 1 - t⁻¹) u = t⁻¹ := by simp
      rw [hbe]
      exact le_of_lt (inv_pos.mpr ht)
    · rw [htf2, Finset.sum_insert hmem0, if_neg hne0, Finset.sum_singleton,
        if_pos (rfl : u = u)]
      field_simp
      ring
  have hint0 : v ∈ affGe ({0} : Set V3) {v} ∩ affGe ({0} : Set V3) {u} :=
    ⟨hm1, hm2⟩
  rw [hEq] at hint0
  have hcap : ({v} ∩ {u} : Set V3) = (∅ : Set V3) := by
    ext z
    simp [hvu]
  rw [hcap] at hint0
  obtain ⟨f, hfin, hsum, -, -⟩ := hint0
  have htf : hfin.toFinset = ({(0:V3)} : Finset V3) := by
    ext z
    simp
  rw [htf] at hsum
  simp at hsum
  exact hv0 hsum

/-- Ring-level packaging of the `fan7` same-ray kill. -/
private theorem pmRingRayKill_p35 {vv : ℕ → V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : Kepler.Text.Fan.FAN 0 V E) (hV : V = Set.range vv) (i j : ℕ)
    (hj0 : vv j ≠ 0) (hij : vv i ≠ vv j)
    (h : ∃ t : ℝ, 0 < t ∧ vv i - 0 = t • (vv j - 0)) : False :=
  pmSameRayKill_p35 hfan (by rw [hV]; exact Set.mem_range.mpr ⟨j, rfl⟩)
    (by rw [hV]; exact Set.mem_range.mpr ⟨i, rfl⟩) (Ne.symm hij) hj0 h

/-- Ring-level: at every dart the whole ring sits in the closed half-space
`{vv i × vv (i+1) ≥ 0}` of the dart face (closed-sector azimuth sandwich
through the sin bridge; the collinear-on-axis-line case contributes `= 0`). -/
private theorem pmCrossGeDart_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (x : V3)
    (hx : x ∈ Set.range vv) :
    0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  obtain ⟨hsand, hθ⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i
  obtain ⟨h0le, hle⟩ := hsand x hx
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
  have hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hvi0 : vv i ≠ (0:V3) := fun hj =>
    hfan'.2.2.2.1 (hj ▸ (Set.mem_range.mpr ⟨i, rfl⟩ : vv i ∈ Set.range vv))
  by_cases hcol : Collinear3 0 (vv i) x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := vv i) (w1 := x) hvi0).mp hcol
    rw [pmCrossAxisZero_p35 (b := (vv (i + 1) : V3)) ⟨c, hc⟩]
  · exact pmCrossGe_p35 hcol hnc h0le (le_trans hle hθ)

/-- Corner C1 rendering (closed conditional): the C1 equalities put both
diagonal endpoints in the dart face plane, with the whole ring in the closed
face half-space.  The remaining exclusion (two mutually non-adjacent ring
vertices inside one face side, with `dist u w ≤ cstab`) is the named
`planeCrowding` residual. -/
private theorem pmC1Render_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (u w : V3)
    (_huR : u ∈ Set.range vv) (_hwR : w ∈ Set.range vv)
    (hu0 : azim 0 (vv i) (vv (i + 1)) u = 0)
    (hw0 : azim 0 (vv i) (vv (i + 1)) w = 0) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hvne : ∀ j : ℕ, vv j ≠ (0:V3) := by
    intro j hj
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact hfan'.2.2.2.1 (hj ▸ (Set.mem_range.mpr ⟨j, rfl⟩ : vv j ∈ Set.range vv))
  have hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)) := by
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  refine ⟨pmRender0_p35 (hvne i) (hvne (i + 1)) hnc hu0,
    pmRender0_p35 (hvne i) (hvne (i + 1)) hnc hw0,
    fun y hy => pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i y hy⟩

/-- Corner C2 rendering (closed conditional): the C2 equalities put both
diagonal endpoints in the span face plane `aff {0, vv i, vv (i+k-1)}`, with
the whole ring in the closed dart-face half-space. -/
private theorem pmC2Render_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (u w : V3)
    (_huR : u ∈ Set.range vv) (_hwR : w ∈ Set.range vv)
    (huθ : azim 0 (vv i) (vv (i + 1)) u = azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)))
    (hwθ : azim 0 (vv i) (vv (i + 1)) w = azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1))) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + k - 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + k - 1) - 0)) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hvne : ∀ j : ℕ, vv j ≠ (0:V3) := by
    intro j hj
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact hfan'.2.2.2.1 (hj ▸ (Set.mem_range.mpr ⟨j, rfl⟩ : vv j ∈ Set.range vv))
  have hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)) := by
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hncsg : ¬ Collinear3 0 (vv i) (vv (i + k - 1)) := by
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact Kepler.Text.Fan.fan_not_collinear hfan' (dartEdgeMems_p35 hk3 hper hE i).2
  refine ⟨pmRenderSpan_p35 (hvne i) (hvne (i + k - 1)) hnc hncsg huθ,
    pmRenderSpan_p35 (hvne i) (hvne (i + k - 1)) hnc hncsg hwθ,
    fun y hy => pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i y hy⟩

/-- Corner C1 at the theorem level: `isScsV39`/`BBsV39` boilerplate
extraction (`diagKGe4` gives `k ≥ 4`, so the fan disjunct resolves) plus the
C1 azimuth equalities render into the closed `pmC1Render_p35` conclusion. -/
private theorem pmC1AtDart_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (i : ℕ) (hu0 : azim 0 (vv i) (vv (i + 1)) u = 0)
    (hw0 : azim 0 (vv i) (vv (i + 1)) w = 0) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  exact pmC1Render_p35 hk3 hper hinj hE hFF hfan i u w
    (Set.mem_range.mpr ⟨p % s.k, hp⟩) (Set.mem_range.mpr ⟨q % s.k, hq⟩) hu0 hw0

/-- Corner C2 at the theorem level: same boilerplate, span-face rendering. -/
private theorem pmC2AtDart_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (i : ℕ)
    (huθ : azim 0 (vv i) (vv (i + 1)) u = azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1)))
    (hwθ : azim 0 (vv i) (vv (i + 1)) w = azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1))) :
    (∃ c d : ℝ, u - 0 = c • (vv i - 0) + d • (vv (i + s.k - 1) - 0)) ∧
    (∃ c d : ℝ, w - 0 = c • (vv i - 0) + d • (vv (i + s.k - 1) - 0)) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  exact pmC2Render_p35 hk3 hper hinj hE hFF hfan i u w
    (Set.mem_range.mpr ⟨p % s.k, hp⟩) (Set.mem_range.mpr ⟨q % s.k, hq⟩) huθ hwθ

/-! ## PlaneMiss π-corner kit (lkgrqui-planemiss2-w3, 2026-10-28)

The C3/C4 π-side rendering: `azim = π` puts the point in the dart face
plane span (frame route through `rep_smul_of_zOf`, the reverse of
`azimPlanePlace_p35`); the C3/C4 corner equalities therefore also collapse
to both diagonal endpoints lying in one dart face plane, additionally
forcing the flat sector span `θ_j = π` (when `θ_j < π` the corner is killed
outright by `wedgeSectorMem_p35`).  All four corners C1–C4 reduce to the
single named residual `pmPlaneCrowding_p35`. -/

/-- Azimuth `π` renders the point into the dart face plane span (HOL
`AZIM_EQ_0_PI_EQ_COPLANAR`-flavored; frame route). -/
private theorem pmRenderPi_p35 {a b x : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b) (h : azim 0 a b x = Real.pi) :
    ∃ s t : ℝ, x - 0 = s • (a - 0) + t • (b - 0) := by
  by_cases hcolx : Collinear3 0 a x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := a) (w1 := x) ha0).mp hcolx
    exact ⟨c, 0, by rw [hc, zero_smul, add_zero]⟩
  · obtain ⟨e1, e2, e3, hon, hal⟩ := exists_on3_eq_smul (a - 0) (sub_ne_zero.mpr ha0)
    have hax : (a - 0 : V3) = dist a 0 • e3 := by rw [dist_eq_norm]; exact hal
    obtain ⟨ψ, r1, r2, hr1, hr2, hzb, hzx⟩ := azim_frame_spec hnc hcolx hon hax
      (by simpa using ha0)
    rw [h] at hzx
    have hsplit : (((ψ + Real.pi : ℝ):ℂ) * Complex.I)
        = ((ψ:ℝ):ℂ) * Complex.I + ((Real.pi:ℝ):ℂ) * Complex.I := by
      rw [Complex.ofReal_add]; ring
    have hr1c : ((r1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr1)
    have hzx' : zOf e1 e2 (x - 0) = (((-(r2 / r1) : ℝ):ℂ)) * zOf e1 e2 (b - 0) := by
      rw [hzx, hzb, hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
      push_cast
      field_simp [hr1c]
    obtain ⟨h1, hh⟩ := rep_smul_of_zOf hon hax ha0 b x (-(r2 / r1)) hzx'
    exact ⟨h1, -(r2 / r1), by rw [hh]; exact add_comm _ _⟩

/-- Corner C3 rendering (closed conditional): `φ_u(j) = 0 ∧ φ_w(j) = π`
puts both diagonal endpoints in the dart face plane, forces the flat sector
span `θ_j = π` (the `π > θ_j` case is killed by the sector bound), and
keeps the whole ring in the closed face half-space. -/
private theorem pmC3Render_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (u w : V3)
    (_huR : u ∈ Set.range vv) (hwR : w ∈ Set.range vv)
    (hu0 : azim 0 (vv i) (vv (i + 1)) u = 0)
    (hwπ : azim 0 (vv i) (vv (i + 1)) w = Real.pi) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) = Real.pi) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hvne : ∀ j : ℕ, vv j ≠ (0:V3) := by
    intro j hj
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact hfan'.2.2.2.1 (hj ▸ (Set.mem_range.mpr ⟨j, rfl⟩ : vv j ∈ Set.range vv))
  have hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan.1.1
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  obtain ⟨hθ0, hθle⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).1 w hwR
  refine ⟨pmRender0_p35 (hvne i) (hvne (i + 1)) hnc hu0,
    pmRenderPi_p35 (hvne i) (hvne (i + 1)) hnc hwπ,
    le_antisymm (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).2
      (by rw [← hwπ]; exact hθle),
    fun y hy => pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i y hy⟩

/-- Corner C4 rendering (closed conditional): mirror of `pmC3Render_p35`
with the π-side on `u`. -/
private theorem pmC4Render_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (u w : V3)
    (huR : u ∈ Set.range vv) (_hwR : w ∈ Set.range vv)
    (huπ : azim 0 (vv i) (vv (i + 1)) u = Real.pi)
    (hw0 : azim 0 (vv i) (vv (i + 1)) w = 0) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) = Real.pi) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hvne : ∀ j : ℕ, vv j ≠ (0:V3) := by
    intro j hj
    have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := hfan.1.1
    exact hfan'.2.2.2.1 (hj ▸ (Set.mem_range.mpr ⟨j, rfl⟩ : vv j ∈ Set.range vv))
  have hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan.1.1
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  obtain ⟨hθ0, hθle⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).1 u huR
  refine ⟨pmRenderPi_p35 (hvne i) (hvne (i + 1)) hnc huπ,
    pmRender0_p35 (hvne i) (hvne (i + 1)) hnc hw0,
    le_antisymm (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).2
      (by rw [← huπ]; exact hθle),
    fun y hy => pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i y hy⟩

/-- Corner C3 at the theorem level: `isScsV39`/`BBsV39` boilerplate
extraction (`diagKGe4` gives `k ≥ 4`, so the fan disjunct resolves) plus
the C3 equalities render into the closed `pmC3Render_p35` conclusion. -/
private theorem pmC3AtDart_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (i : ℕ) (hu0 : azim 0 (vv i) (vv (i + 1)) u = 0)
    (hwπ : azim 0 (vv i) (vv (i + 1)) w = Real.pi) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1)) = Real.pi) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  exact pmC3Render_p35 hk3 hper hinj hE hFF hfan i u w
    (Set.mem_range.mpr ⟨p % s.k, hp⟩) (Set.mem_range.mpr ⟨q % s.k, hq⟩) hu0 hwπ

/-- Corner C4 at the theorem level: same boilerplate, π-side on `u`. -/
private theorem pmC4AtDart_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (i : ℕ) (huπ : azim 0 (vv i) (vv (i + 1)) u = Real.pi)
    (hw0 : azim 0 (vv i) (vv (i + 1)) w = 0) :
    (∃ s t : ℝ, u - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (∃ s t : ℝ, w - 0 = s • (vv i - 0) + t • (vv (i + 1) - 0)) ∧
    (azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1)) = Real.pi) ∧
    (∀ y ∈ Set.range vv, 0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  exact pmC4Render_p35 hk3 hper hinj hE hFF hfan i u w
    (Set.mem_range.mpr ⟨p % s.k, hp⟩) (Set.mem_range.mpr ⟨q % s.k, hq⟩) huπ hw0

/-! ## PlaneMiss endgame ladder (lkgrqui-planemiss3-w3, 2026-10-28)

Terminal-squeeze pieces staged above the `pmPlaneCrowding_p35` residual.
Rung 1 = scalar triple product algebra; rung 2 = the propagation
dichotomy (HOL TECOXBM.hl:311 CROSS_TRIPLE/SKEW segment: a ring vertex
inside the dart-`j` face plane propagates that plane to at least one of
its two ring neighbours — the σ-cycle iteration seed); rung 3 = the
annulus chord–cosine bridge with the exact winding constants
`2719/3969 = 1 - 1250/3969` (angle ≥ 2·arcsin(1/(2·h0)) ≈ 46.74°, the
k = 6 step lower bound) and `1031/5000` (angle ≤ 2·arcsin((2·h0)/4) ≈
78.15°, the k = 6 step upper bound), feeding the planar winding + metric
squeeze endgame (k ∈ {4,5,6}; k=6 diagonal-2 squeeze: min far chord
3.1065 > cstab, see DELIVERY numerics). -/

/-- Triple product cyclic permutation (Mathlib
`triple_product_permutation` + `dotProduct_comm`). -/
private theorem pmTripleCyc_p35 (f g h : Fin 3 → ℝ) :
    (crossProduct f g) ⬝ᵥ h = (crossProduct g h) ⬝ᵥ f := by
  rw [dotProduct_comm (crossProduct f g) h, triple_product_permutation h f g,
    dotProduct_comm (crossProduct g h) f]

/-- crossProduct additivity in the first slot. -/
private theorem pmCrossAddL_p35 (p q r : Fin 3 → ℝ) :
    crossProduct (p + q) r = crossProduct p r + crossProduct q r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.add_apply]

/-- crossProduct linearity in the first slot (`smul`). -/
private theorem pmCrossSmulL_p35 (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

/-- crossProduct additivity in the second slot. -/
private theorem pmCrossAddR_p35 (p q r : Fin 3 → ℝ) :
    crossProduct p (q + r) = crossProduct p q + crossProduct p r := by
  rw [← cross_anticomm (q + r) p, ← cross_anticomm q p, ← cross_anticomm r p,
    pmCrossAddL_p35, neg_add]

/-- crossProduct linearity in the second slot (`smul`). -/
private theorem pmCrossSmulR_p35 (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct p (t • r) = t • crossProduct p r := by
  rw [← cross_anticomm (t • r) p, pmCrossSmulL_p35, ← cross_anticomm p r,
    smul_neg, neg_neg]

/-- dotProduct additivity in the first slot. -/
private theorem pmDotAddL_p35 (p q r : Fin 3 → ℝ) :
    (p + q) ⬝ᵥ r = p ⬝ᵥ r + q ⬝ᵥ r := by
  unfold dotProduct
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- dotProduct additivity in the second slot. -/
private theorem pmDotAddR_p35 (p q r : Fin 3 → ℝ) :
    p ⬝ᵥ (q + r) = p ⬝ᵥ q + p ⬝ᵥ r := by
  rw [dotProduct_comm p (q + r), pmDotAddL_p35, dotProduct_comm q p,
    dotProduct_comm r p]

/-- dotProduct linearity in the first slot (`smul`). -/
private theorem pmDotSmulL_p35 (t : ℝ) (p r : Fin 3 → ℝ) :
    (t • p) ⬝ᵥ r = t * (p ⬝ᵥ r) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- dotProduct oddness in the first slot. -/
private theorem pmDotNegL_p35 (p r : Fin 3 → ℝ) : (-p) ⬝ᵥ r = -(p ⬝ᵥ r) := by
  unfold dotProduct
  simp only [Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    (neg_mul_eq_neg_mul (p i) (r i)).symm

/-- dotProduct oddness in the second slot. -/
private theorem pmDotNegR_p35 (p r : Fin 3 → ℝ) : p ⬝ᵥ (-r) = -(p ⬝ᵥ r) := by
  rw [dotProduct_comm p (-r), pmDotNegL_p35, dotProduct_comm r p]

/-- V3 face-span rendering lifted to the pi layer (the V3 `smul`/`add`
coes are `rfl` type-synonym equalities). -/
private theorem pmSpanCoe_p35 {x b c : V3}
    (hu : ∃ α β : ℝ, x - 0 = α • (b - 0) + β • (c - 0)) :
    ∃ α β : ℝ, (x : Fin 3 → ℝ) = α • (b : Fin 3 → ℝ) + β • (c : Fin 3 → ℝ) := by
  obtain ⟨α, β, hx⟩ := hu
  simp only [sub_zero] at hx
  exact ⟨α, β, congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hx⟩

/-- Norm-square bridge: `‖v‖² = v ⬝ᵥ v` on `V3`. -/
private theorem pmNormSqDot_p35 (v : V3) :
    ‖v‖ ^ 2 = (v : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have hvi : (v : Fin 3 → ℝ) i = v i := rfl
  rw [hvi, Real.norm_eq_abs, sq_abs, pow_two]

/-- The dot–norm–dist identity `x ⬝ᵥ y = (‖x‖² + ‖y‖² − dist x y²)/2`. -/
private theorem pmDotNormDist_p35 (x y : V3) :
    (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)
      = (‖x‖ ^ 2 + ‖y‖ ^ 2 - dist x y ^ 2) / 2 := by
  have hdist : dist x y = ‖x - y‖ := dist_eq_norm x y
  have hns : dist x y ^ 2
      = ((x - y : V3) : Fin 3 → ℝ) ⬝ᵥ ((x - y : V3) : Fin 3 → ℝ) := by
    rw [hdist]
    exact pmNormSqDot_p35 (x - y)
  have hcoe : ((x - y : V3) : Fin 3 → ℝ) = (x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) := rfl
  have hA : ((x : Fin 3 → ℝ) - (y : Fin 3 → ℝ))
        ⬝ᵥ ((x : Fin 3 → ℝ) - (y : Fin 3 → ℝ))
      = (x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ)
        - 2 * ((x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ))
        + (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
    have e0 : ((x : Fin 3 → ℝ) - (y : Fin 3 → ℝ))
        = (x : Fin 3 → ℝ) + -(y : Fin 3 → ℝ) := sub_eq_add_neg _ _
    rw [e0]
    simp only [pmDotAddL_p35, pmDotAddR_p35, pmDotNegR_p35, pmDotNegL_p35,
      neg_neg, dotProduct_comm (y : Fin 3 → ℝ) (x : Fin 3 → ℝ)]
    ring
  rw [hcoe] at hns
  rw [pmNormSqDot_p35 x, pmNormSqDot_p35 y, hns, hA]
  linarith

/-- **Propagation dichotomy core** (HOL TECOXBM.hl:311 CROSS_TRIPLE/SKEW):
`x` sits in the `(b, c)` face span, `D± = (b×c)·x± ≥ 0` (the `(b,c)`
half-space at the ring neighbours of `x`), and the two flanking darts at
`x` carry their closed half-space bounds against `b` and `c`.  Then the
`(b, c)` plane reaches `x⁺` or `x⁻`: if it reaches neither, the sign
algebra `0 ≤ β·D⁺`, `0 ≤ −α·D⁺`, `0 ≤ −β·D⁻`, `0 ≤ α·D⁻` (from
`x = α·b + β·c` and the triple product expansion) forces `α = β = 0`,
i.e. `x = 0`. -/
private theorem pmPropDichCore_p35 {x xp xm b c : V3}
    (hu : ∃ α β : ℝ, (x : Fin 3 → ℝ) = α • (b : Fin 3 → ℝ) + β • (c : Fin 3 → ℝ))
    (hDp : 0 ≤ (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (xp : Fin 3 → ℝ))
    (hDm : 0 ≤ (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (xm : Fin 3 → ℝ))
    (h1 : 0 ≤ (crossProduct (x : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ))
    (h2 : 0 ≤ (crossProduct (x : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ))
    (h3 : 0 ≤ (crossProduct (xm : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ))
    (h4 : 0 ≤ (crossProduct (xm : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ))
    (hx0 : (x : Fin 3 → ℝ) ≠ 0) :
    (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (xp : Fin 3 → ℝ) = 0 ∨
    (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (xm : Fin 3 → ℝ) = 0 := by
  obtain ⟨α, β, hx⟩ := hu
  have hDp' : 0 ≤ (xp : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ) := by
    rw [dotProduct_comm]; exact hDp
  have hDm' : 0 ≤ (xm : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ) := by
    rw [dotProduct_comm]; exact hDm
  -- dart-(x, x⁺) against b: β·D⁺ ≥ 0
  have e1 : (crossProduct (x : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
      = β * ((xp : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
    rw [hx, pmCrossAddL_p35, pmCrossSmulL_p35, pmCrossSmulL_p35, pmDotAddL_p35,
      pmDotSmulL_p35, pmDotSmulL_p35]
    have hb : (crossProduct (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm (crossProduct (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ))
        (b : Fin 3 → ℝ)]
      exact dot_self_cross (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ)
    have hc : (crossProduct (c : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
        = (xp : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ) := by
      rw [dotProduct_comm (crossProduct (c : Fin 3 → ℝ) (xp : Fin 3 → ℝ))
        (b : Fin 3 → ℝ),
        ← triple_product_permutation (xp : Fin 3 → ℝ) (b : Fin 3 → ℝ)
          (c : Fin 3 → ℝ)]
    rw [hb, hc]; ring
  -- dart-(x, x⁺) against c: −α·D⁺ ≥ 0
  have e2 : (crossProduct (x : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ)
      = -α * ((xp : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
    rw [hx, pmCrossAddL_p35, pmCrossSmulL_p35, pmCrossSmulL_p35, pmDotAddL_p35,
      pmDotSmulL_p35, pmDotSmulL_p35]
    have hb : (crossProduct (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ)
        = -((xp : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
      rw [dotProduct_comm (crossProduct (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ))
        (c : Fin 3 → ℝ), triple_product_permutation (c : Fin 3 → ℝ)
        (b : Fin 3 → ℝ) (xp : Fin 3 → ℝ), ← cross_anticomm (c : Fin 3 → ℝ)
        (xp : Fin 3 → ℝ), dotProduct_neg,
        ← triple_product_permutation (xp : Fin 3 → ℝ) (b : Fin 3 → ℝ)
          (c : Fin 3 → ℝ)]
    have hc : (crossProduct (c : Fin 3 → ℝ) (xp : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm (crossProduct (c : Fin 3 → ℝ) (xp : Fin 3 → ℝ))
        (c : Fin 3 → ℝ)]
      exact dot_self_cross (c : Fin 3 → ℝ) (xp : Fin 3 → ℝ)
    rw [hb, hc]; ring
  -- dart-(x⁻, x) against b: −β·D⁻ ≥ 0
  have e3 : (crossProduct (xm : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
      = -β * ((xm : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
    rw [hx, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35, pmDotAddL_p35,
      pmDotSmulL_p35, pmDotSmulL_p35]
    have hb : (crossProduct (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm (crossProduct (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ))
        (b : Fin 3 → ℝ)]
      exact dot_cross_self (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ)
    have hc : (crossProduct (xm : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
        = -((xm : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
      rw [dotProduct_comm (crossProduct (xm : Fin 3 → ℝ) (c : Fin 3 → ℝ))
        (b : Fin 3 → ℝ), ← cross_anticomm (c : Fin 3 → ℝ) (xm : Fin 3 → ℝ),
        dotProduct_neg,
        ← triple_product_permutation (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ)
          (c : Fin 3 → ℝ)]
    rw [hb, hc]; ring
  -- dart-(x⁻, x) against c: α·D⁻ ≥ 0
  have e4 : (crossProduct (xm : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ)
      = α * ((xm : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) := by
    rw [hx, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35, pmDotAddL_p35,
      pmDotSmulL_p35, pmDotSmulL_p35]
    have hb : (crossProduct (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ)
        = (xm : Fin 3 → ℝ) ⬝ᵥ crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ) := by
      rw [dotProduct_comm (crossProduct (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ))
        (c : Fin 3 → ℝ), triple_product_permutation (c : Fin 3 → ℝ)
        (xm : Fin 3 → ℝ) (b : Fin 3 → ℝ)]
    have hc : (crossProduct (xm : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm (crossProduct (xm : Fin 3 → ℝ) (c : Fin 3 → ℝ))
        (c : Fin 3 → ℝ)]
      exact dot_cross_self (xm : Fin 3 → ℝ) (c : Fin 3 → ℝ)
    rw [hb, hc]; ring
  rcases le_iff_eq_or_lt.mp hDp' with hDp0 | hDppos
  · refine Or.inl ?_
    rw [dotProduct_comm (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ))
      (xp : Fin 3 → ℝ)]
    exact hDp0.symm
  rcases le_iff_eq_or_lt.mp hDm' with hDm0 | hDmpos
  · refine Or.inr ?_
    rw [dotProduct_comm (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ))
      (xm : Fin 3 → ℝ)]
    exact hDm0.symm
  exfalso
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3; rw [e4] at h4
  have hβ : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    exact absurd h1 (not_le.mpr (by nlinarith [hneg, hDppos]))
  have hα : α ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    exact absurd h2 (not_le.mpr (by nlinarith [hpos, hDppos]))
  have hβ' : β ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    exact absurd h3 (not_le.mpr (by nlinarith [hpos, hDmpos]))
  have hα' : 0 ≤ α := by
    by_contra hneg
    push_neg at hneg
    exact absurd h4 (not_le.mpr (by nlinarith [hneg, hDmpos]))
  have hα0 : α = 0 := le_antisymm hα hα'
  have hβ0 : β = 0 := le_antisymm hβ' hβ
  rw [hα0, hβ0, zero_smul, zero_smul, add_zero] at hx
  exact hx0 hx

/-- **Propagation dichotomy at the ring** (theorem level, `pmPlaneCrowding`
hypotheses): with `u` in the `j`-th dart face span, the dart-`j` plane
reaches the ring successor or the ring predecessor of `u`.  This is the
σ-cycle seed of the HOL `AFF_GT_INTER_AFF_SY` endgame. -/
private theorem pmPropDichotomyAt_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (_hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (j : ℕ)
    (hu : ∃ c d : ℝ, u - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0)) :
    (crossProduct ((vv j : V3) : Fin 3 → ℝ) ((vv (j + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ
        ((vv (p % s.k + 1) : V3) : Fin 3 → ℝ) = 0 ∨
    (crossProduct ((vv j : V3) : Fin 3 → ℝ) ((vv (j + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ
        ((vv (p % s.k + (s.k - 1)) : V3) : Fin 3 → ℝ) = 0 := by
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have huB : u ∈ ballAnnulus := hBB.1 (Set.mem_range.mpr ⟨p % s.k, hp⟩)
  have hu2 : (2:ℝ) ≤ ‖u‖ := by
    have h1 : ¬ (dist u (0:V3) < 2) := huB.2
    have h3 : dist u (0:V3) = ‖u‖ := by
      simp [dist_eq_norm]
    linarith
  have hucoe : ((u : V3) : Fin 3 → ℝ) ≠ 0 := by
    have h4 : (4:ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [hu2]
    intro hzero
    have hsq : ‖u‖ ^ 2 = ((u : V3) : Fin 3 → ℝ) ⬝ᵥ ((u : V3) : Fin 3 → ℝ) :=
      pmNormSqDot_p35 u
    rw [hzero] at hsq
    have h0 : ((0 : Fin 3 → ℝ)) ⬝ᵥ (0 : Fin 3 → ℝ) = 0 := by
      unfold dotProduct
      simp
    rw [h0] at hsq
    linarith
  have hge : ∀ i : ℕ, ∀ y : V3, y ∈ Set.range vv →
      0 ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ) ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ
        (y : Fin 3 → ℝ) :=
    fun i y hy => pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i y hy
  have hr1 : vv j ∈ Set.range vv := Set.mem_range.mpr ⟨j, rfl⟩
  have hr2 : vv (j + 1) ∈ Set.range vv := Set.mem_range.mpr ⟨j + 1, rfl⟩
  have hrp : vv (p % s.k + 1) ∈ Set.range vv := Set.mem_range.mpr ⟨p % s.k + 1, rfl⟩
  have hrpp : vv (p % s.k + (s.k - 1)) ∈ Set.range vv :=
    Set.mem_range.mpr ⟨p % s.k + (s.k - 1), rfl⟩
  have hDp := hge j _ hrp
  have hDm := hge j _ hrpp
  have h1 := hge (p % s.k) (vv j) hr1
  have h2 := hge (p % s.k) (vv (j + 1)) hr2
  have h3 := hge (p % s.k + (s.k - 1)) (vv j) hr1
  have h4 := hge (p % s.k + (s.k - 1)) (vv (j + 1)) hr2
  have hpk : vv (p % s.k + s.k) = u := by rw [hper, hp]
  have hplus : p % s.k + (s.k - 1) + 1 = p % s.k + s.k := by omega
  rw [hplus, hpk] at h3 h4
  rw [hp] at h1 h2
  refine pmPropDichCore_p35 (pmSpanCoe_p35 hu) hDp hDm h1 h2 h3 h4 hucoe

/-- Annulus cosine upper bound at `a`-pairs (the k = 6 winding step
constant): two annulus vectors at chord ≥ 2 meet under a vector angle
whose cosine is at most `2719/3969 = 1 - 1250/3969`, i.e. the angle is ≥
`2·arcsin(1/(2·h0)) ≈ 46.74°`. -/
private theorem pmCosLe46_p35 {x y : V3} (hx2 : 2 ≤ ‖x‖) (hx : ‖x‖ ≤ 2 * h0)
    (hy2 : 2 ≤ ‖y‖) (hy : ‖y‖ ≤ 2 * h0) (hd : 2 ≤ dist x y) :
    (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) ≤ (2719 / 3969) * (‖x‖ * ‖y‖) := by
  have h02 : (2 : ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hx hy
  have hG : (2:ℝ) * (2719 / 3969) * (‖x‖ * ‖y‖) - ‖x‖ ^ 2 - ‖y‖ ^ 2 + 4 ≥ 0 := by
    have e : (2:ℝ) * (2719 / 3969) * (‖x‖ * ‖y‖) - ‖x‖ ^ 2 - ‖y‖ ^ 2 + 4
        = (63 / 25 - ‖x‖) * (63 / 25 + ‖x‖ - 2 * (2719 / 3969) * ‖y‖)
          + (63 / 25 - ‖y‖) * (63 / 25 + ‖y‖ - 2 * (2719 / 3969) * (63 / 25)) := by
      ring
    rw [e]
    have p1 : 0 ≤ (63 / 25 - ‖x‖) * (63 / 25 + ‖x‖ - 2 * (2719 / 3969) * ‖y‖) :=
      mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (63 / 25 - ‖y‖) * (63 / 25 + ‖y‖ - 2 * (2719 / 3969) * (63 / 25)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hd2 : (4:ℝ) ≤ dist x y ^ 2 := by nlinarith [hd]
  have hid := pmDotNormDist_p35 x y
  linarith

/-- Annulus cosine lower bound at `b`-pairs (the k = 6 winding step
constant): two annulus vectors at chord ≤ `2·h0` meet under a vector
angle whose cosine is at least `1031/5000 = 0.2062`, i.e. the angle is ≤
`2·arcsin((2·h0)/4) ≈ 78.15°`. -/
private theorem pmCosGe78_p35 {x y : V3} (hx2 : 2 ≤ ‖x‖) (hx : ‖x‖ ≤ 2 * h0)
    (hy2 : 2 ≤ ‖y‖) (hy : ‖y‖ ≤ 2 * h0) (hd : dist x y ≤ 2 * h0) :
    (1031 / 5000) * (‖x‖ * ‖y‖) ≤ (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have h02 : (2 : ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hx hy hd
  have hG : ‖x‖ ^ 2 + ‖y‖ ^ 2 - (63 / 25) ^ 2
      - 2 * (1031 / 5000) * (‖x‖ * ‖y‖) ≥ 0 := by
    have e : ‖x‖ ^ 2 + ‖y‖ ^ 2 - (63 / 25) ^ 2
        - 2 * (1031 / 5000) * (‖x‖ * ‖y‖)
        = (‖x‖ - 2) * (‖x‖ + 2 - 2 * (1031 / 5000) * ‖y‖)
          + (‖y‖ - 2) * (‖y‖ + 2 - 2 * (1031 / 5000) * 2) := by
      ring
    rw [e]
    have p1 : 0 ≤ (‖x‖ - 2) * (‖x‖ + 2 - 2 * (1031 / 5000) * ‖y‖) :=
      mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (‖y‖ - 2) * (‖y‖ + 2 - 2 * (1031 / 5000) * 2) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hd2 : dist x y ^ 2 ≤ (63 / 25) ^ 2 :=
    by nlinarith [hd, (dist_nonneg : (0:ℝ) ≤ dist x y)]
  have hid := pmDotNormDist_p35 x y
  linarith
/-! ## planemiss4 rungs (lkgrqui-planemiss4-w3, 2026-10-28) -/

/-- Height-squared bound over a chord ray (k = 6 diagonal-2 analytic core):
for two annulus vectors at chord in `[2, 2·h0]`, the squared height of `x`
over the `y`-ray obeys `4‖x‖²‖y‖² − (‖x‖²+‖y‖²−dist²)² ≥ (5776/625)·‖y‖²`,
i.e. the height itself is `≥ 38/25 = 1.52` (so `2h > cstab`). -/
private theorem pmHeightSq_p35 {x y : V3} (hx2 : (2:ℝ) ≤ ‖x‖) (hx : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hy : ‖y‖ ≤ 2 * h0)
    (hd2 : (2:ℝ) ≤ dist x y) (hd : dist x y ≤ 2 * h0) :
    (4:ℝ) * ‖x‖ ^ 2 * ‖y‖ ^ 2 - (‖x‖ ^ 2 + ‖y‖ ^ 2 - dist x y ^ 2) ^ 2
      ≥ (5776 / 625) * ‖y‖ ^ 2 := by
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hx hy hd
  have hf : (4:ℝ) * ‖x‖ ^ 2 * ‖y‖ ^ 2 - (‖x‖ ^ 2 + ‖y‖ ^ 2 - dist x y ^ 2) ^ 2
      = ((‖x‖ + ‖y‖) ^ 2 - dist x y ^ 2) * (dist x y ^ 2 - (‖x‖ - ‖y‖) ^ 2) := by ring
  rw [hf]
  have hd4 : (4:ℝ) ≤ dist x y ^ 2 := by nlinarith
  have hpos : 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - dist x y ^ 2 - 4 ≥ 0 := by nlinarith
  have hstep : ((‖x‖ + ‖y‖) ^ 2 - dist x y ^ 2) * (dist x y ^ 2 - (‖x‖ - ‖y‖) ^ 2)
      ≥ ((‖x‖ + ‖y‖) ^ 2 - 4) * (4 - (‖x‖ - ‖y‖) ^ 2) := by
    have idty : ((‖x‖ + ‖y‖) ^ 2 - dist x y ^ 2) * (dist x y ^ 2 - (‖x‖ - ‖y‖) ^ 2)
        = ((‖x‖ + ‖y‖) ^ 2 - 4) * (4 - (‖x‖ - ‖y‖) ^ 2)
          + (dist x y ^ 2 - 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - dist x y ^ 2 - 4) := by ring
    rw [idty]
    have t1 : (0:ℝ) ≤ (dist x y ^ 2 - 4) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 - dist x y ^ 2 - 4) :=
      mul_nonneg (by linarith) hpos
    linarith
  -- key: (‖y‖+4)(4-(‖x‖-‖y‖)²) ≥ (5776/625)·‖y‖
  have key : (‖y‖ + 4) * (4 - (‖x‖ - ‖y‖) ^ 2) ≥ (5776 / 625) * ‖y‖ := by
    rcases le_or_gt (‖x‖ - 2) (‖y‖ - 2) with hst | hst
    · have hcross : (‖y‖ + 4) * (4 - (‖x‖ - ‖y‖) ^ 2)
          = (‖y‖ + 4) * (4 - (‖y‖ - 2) ^ 2)
            + (‖x‖ - 2) * ((‖y‖ + 4) * (2 * (‖y‖ - 2) - (‖x‖ - 2))) := by ring
      have hc0 : 0 ≤ (‖x‖ - 2) * ((‖y‖ + 4) * (2 * (‖y‖ - 2) - (‖x‖ - 2))) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
      have hq0 : 0 ≤ (‖y‖ - 2) ^ 2 + (13 / 25) * (‖y‖ - 2) + (13 / 25) ^ 2 := by nlinarith
      have hq1 : 0 ≤ 6 * ((‖y‖ - 2) + 13 / 25) := by nlinarith
      have hprod : 0 ≤ (‖y‖ - 2 - 13 / 25) *
          (-1 * ((‖y‖ - 2) ^ 2 + (13 / 25) * (‖y‖ - 2) + (13 / 25) ^ 2)
            - 6 * ((‖y‖ - 2) + 13 / 25) + 4 - 5776 / 625) := by
        refine mul_nonneg_of_nonpos_of_nonpos (by linarith) ?_
        have h4 : (4:ℝ) - 5776 / 625 < 0 := by norm_num
        linarith
      have hD : (‖y‖ + 4) * (4 - (‖y‖ - 2) ^ 2) - (5776 / 625) * ‖y‖ ≥ 16065 / 15625 := by
        have e : (‖y‖ + 4) * (4 - (‖y‖ - 2) ^ 2) - (5776 / 625) * ‖y‖
            = 16065 / 15625 + (‖y‖ - 2 - 13 / 25) *
              (-1 * ((‖y‖ - 2) ^ 2 + (13 / 25) * (‖y‖ - 2) + (13 / 25) ^ 2)
                - 6 * ((‖y‖ - 2) + 13 / 25) + 4 - 5776 / 625) := by ring
        rw [e]
        exact le_add_of_nonneg_right hprod
      linarith
    · have hsb : (‖x‖ - 2) ≤ 21 / 25 := by linarith
      have hstep1 : (‖y‖ + 4) * (4 - (‖x‖ - ‖y‖) ^ 2)
          - (‖y‖ + 4) * (4 - (‖y‖ - 71 / 25) ^ 2) ≥ 0 := by
        have e : (‖y‖ + 4) * (4 - (‖x‖ - ‖y‖) ^ 2) - (‖y‖ + 4) * (4 - (‖y‖ - 71 / 25) ^ 2)
            = (‖y‖ + 4) * ((‖x‖ - 2) - 21 / 25)
              * (2 * (‖y‖ - 2) - (‖x‖ - 2) - 21 / 25) := by ring
        have hA0 : ((‖x‖ - 2) - 21 / 25) ≤ 0 := by linarith
        have hB0 : (2 * (‖y‖ - 2) - (‖x‖ - 2) - 21 / 25) ≤ 0 := by linarith
        have hAB : 0 ≤ ((‖x‖ - 2) - 21 / 25) * (2 * (‖y‖ - 2) - (‖x‖ - 2) - 21 / 25) :=
          mul_nonneg_of_nonpos_of_nonpos hA0 hB0
        rw [e]
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) hA0) hB0
      have hsq : (‖y‖ - 2 - 21 / 25) ^ 2 ≤ (21 / 25) ^ 2 := by nlinarith
      have hstep2 : (‖y‖ + 4) * (4 - (‖y‖ - 71 / 25) ^ 2) - (5776 / 625) * ‖y‖
          ≥ (6 * (4 - (21 / 25) ^ 2) - (5776 / 625) * 2) := by
        have e : (‖y‖ + 4) * (4 - (‖y‖ - 71 / 25) ^ 2) - (5776 / 625) * ‖y‖
            = (6 * (4 - (21 / 25) ^ 2) - (5776 / 625) * 2)
              + (‖y‖ - 2) * ((4 - (‖y‖ - 71 / 25) ^ 2) - 6 * (‖y‖ - 2) + 252 / 25 - 5776 / 625) := by
          ring
        rw [e]
        have hbr : (4 - (‖y‖ - 71 / 25) ^ 2) - 6 * (‖y‖ - 2) + 252 / 25 - 5776 / 625 ≥ 0 := by
          nlinarith [hsq, show (‖y‖ - 2) ^ 2 ≤ (13 / 25) * (‖y‖ - 2) from by nlinarith]
        exact le_add_of_nonneg_right (mul_nonneg (by linarith) hbr)
      have hval : (6:ℝ) * (4 - (21 / 25) ^ 2) - (5776 / 625) * 2 > 0 := by norm_num
      linarith
  -- first factor: (‖x‖+‖y‖-2)(‖x‖+‖y‖+2) ≥ ‖y‖(‖y‖+4)
  have hA1 : (‖x‖ + ‖y‖ - 2) * (‖x‖ + ‖y‖ + 2) ≥ ‖y‖ * (‖y‖ + 4) := by
    have e : (‖x‖ + ‖y‖ - 2) * (‖x‖ + ‖y‖ + 2) = ‖y‖ * (‖y‖ + 4)
        + (‖x‖ - 2) * (2 * (‖y‖ - 2) + (‖x‖ - 2) + 8) := by ring
    rw [e]; nlinarith
  have hB0 : (0:ℝ) ≤ 4 - (‖x‖ - ‖y‖) ^ 2 := by nlinarith
  have h1 : (‖x‖ + ‖y‖) ^ 2 - 4 ≥ ‖y‖ * (‖y‖ + 4) := by
    have e : (‖x‖ + ‖y‖) ^ 2 - 4 = (‖x‖ + ‖y‖ - 2) * (‖x‖ + ‖y‖ + 2) := by ring
    linarith [hA1, e]
  have hF : ((‖x‖ + ‖y‖) ^ 2 - 4) * (4 - (‖x‖ - ‖y‖) ^ 2)
      ≥ (‖y‖ * (‖y‖ + 4)) * (4 - (‖x‖ - ‖y‖) ^ 2) :=
    mul_le_mul_of_nonneg_right h1 hB0
  have hmul : (‖y‖ * (‖y‖ + 4)) * (4 - (‖x‖ - ‖y‖) ^ 2)
      ≥ (5776 / 625) * (‖y‖ * ‖y‖) := by
    have h2 : (‖y‖ * (‖y‖ + 4)) * (4 - (‖x‖ - ‖y‖) ^ 2)
        = ‖y‖ * ((‖y‖ + 4) * (4 - (‖x‖ - ‖y‖) ^ 2)) := by ring
    have h3 : (5776 / 625) * (‖y‖ * ‖y‖) = ‖y‖ * ((5776 / 625) * ‖y‖) := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left key (by linarith)
  linarith

/-- Far-diagonal cosine bridge: two annulus vectors at chord ≤ `cstab` meet
under an angle whose cosine is `≥ −10601/80000` scaled by the radii product,
i.e. the vector angle is `≤ 2·arcsin(cstab/4) ≈ 97.63°`. -/
private theorem pmFarCos_p35 {x y : V3} (hx2 : (2:ℝ) ≤ ‖x‖) (hx : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hy : ‖y‖ ≤ 2 * h0) (hd : dist x y ≤ cstab) :
    -(10601 / 80000) * (‖x‖ * ‖y‖) ≤ (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  have hc : cstab = 301 / 100 := by norm_num [cstab]
  rw [h02] at hx hy
  rw [hc] at hd
  have hG : ‖x‖ ^ 2 + ‖y‖ ^ 2 + (10601 / 40000) * (‖x‖ * ‖y‖) - (90601 / 10000) ≥ 0 := by
    have e : ‖x‖ ^ 2 + ‖y‖ ^ 2 + (10601 / 40000) * (‖x‖ * ‖y‖) - (90601 / 10000)
        = (‖x‖ - 2) * (‖x‖ + 2 + (10601 / 40000) * ‖y‖)
          + (‖y‖ - 2) * (‖y‖ + 2 + (10601 / 40000) * 2) := by ring
    rw [e]
    have p1 : 0 ≤ (‖x‖ - 2) * (‖x‖ + 2 + (10601 / 40000) * ‖y‖) :=
      mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (‖y‖ - 2) * (‖y‖ + 2 + (10601 / 40000) * 2) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hd2 : dist x y ^ 2 ≤ (301 / 100) ^ 2 :=
    by nlinarith [hd, (dist_nonneg : (0:ℝ) ≤ dist x y)]
  have hid := pmDotNormDist_p35 x y
  linarith

/-- Same-ray kill: two distinct annulus points on one ray (`c ≥ 0`) have
chord `|‖x‖ − ‖y‖| ≤ 2·h0 − 2 = 13/25 < 2`, contradicting the a-bound. -/
private theorem pmNotSameRay_p35 {x y : V3} {c : ℝ} (hx2 : (2:ℝ) ≤ ‖x‖) (hx : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hy : ‖y‖ ≤ 2 * h0) (hc : 0 ≤ c) (hxy : x - 0 = c • (y - 0))
    (hge : (2:ℝ) ≤ dist x y) : False := by
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hx hy
  have h1 : x = c • y := by simpa using hxy
  have hnym : ‖x‖ = c * ‖y‖ := by
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have h2 : x - y = (c - 1) • y := by rw [h1]; module
  have h3 : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
  have hdist : dist x y = |(c:ℝ) - 1| * ‖y‖ := by
    rw [h3, h2, norm_smul, Real.norm_eq_abs]
  rcases le_or_gt c 1 with hc1 | hc1
  · have hAbs : |(c:ℝ) - 1| = 1 - c :=
      (abs_of_nonpos (by linarith : c - 1 ≤ 0)).trans (neg_sub c 1)
    have hEq : dist x y = ‖y‖ - ‖x‖ := by rw [hdist, hAbs, hnym]; ring
    linarith [hEq, hx2, hy]
  · have hAbs : |(c:ℝ) - 1| = c - 1 := abs_of_nonneg (show (0:ℝ) ≤ c - 1 by linarith)
    have hEq : dist x y = ‖x‖ - ‖y‖ := by rw [hdist, hAbs, hnym]; ring
    linarith [hEq, hx, hy2]

/-- Basis-swap: two linearly independent vectors of the plane `span(a, b)`
regenerate `a` and `b` (the "adjacent double-P-point ⟹ equal dart planes"
rung of the winding skeleton). -/
private theorem pmSpanEq_p35 {a b u v : V3}
    (hu : ∃ c d : ℝ, u - 0 = c • (a - 0) + d • (b - 0))
    (hv : ∃ c d : ℝ, v - 0 = c • (a - 0) + d • (b - 0))
    (hnu : (0:V3) ≠ u) (hdep : ∀ c : ℝ, v - 0 ≠ c • (u - 0)) :
    (∃ e f : ℝ, a - 0 = e • (u - 0) + f • (v - 0)) ∧
      (∃ e f : ℝ, b - 0 = e • (u - 0) + f • (v - 0)) := by
  obtain ⟨α, β, hu'⟩ := hu
  obtain ⟨γ, δ, hv'⟩ := hv
  simp only [sub_zero] at hu' hv'
  have hkey : α * δ - β * γ ≠ 0 := by
    intro hzero
    rcases eq_or_ne α 0 with hα0 | hα0
    · have hub : u = β • b := by rw [hu', hα0]; simp
      have hβ0 : β ≠ 0 := by
        intro hβ0
        rw [hβ0] at hub
        exact hnu (by simpa using hub.symm)
      rcases eq_or_ne γ 0 with hγ0 | hγ0
      · have hv0 : v = δ • b := by rw [hv', hγ0]; simp
        refine hdep (δ / β) ?_
        rw [hv0, hub]
        simp only [sub_zero, smul_smul]
        field_simp
      · exfalso
        have hbc : β * γ = 0 := by
          rw [hα0, zero_mul] at hzero
          linarith
        rcases mul_eq_zero.mp hbc with h | h
        · exact hβ0 h
        · exact hγ0 h
    · refine hdep (γ / α) ?_
      have hv2 : v = (γ / α) • u := by
        have e1 : (γ / α) • u = (γ / α) • (α • a + β • b) := by rw [hu']
        have hδ : δ = β * γ / α := by
          field_simp
          linarith [hzero]
        have e2 : (γ / α) • (α • a + β • b) = γ • a + δ • b := by
          rw [smul_add, smul_smul, div_mul_cancel₀ _ hα0, hδ]
          module
        rw [e1, e2, hv']
      simpa using hv2
  refine ⟨?_, ?_⟩
  · refine ⟨δ / (α * δ - β * γ), -(β / (α * δ - β * γ)), ?_⟩
    have h1 : (α * δ - β * γ) • (a - 0) = δ • (u - 0) - β • (v - 0) := by
      rw [hu', hv']
      module
    suffices h : (α * δ - β * γ) • (a - 0)
        = (α * δ - β * γ) • ((δ / (α * δ - β * γ)) • (u - 0)
          + (-(β / (α * δ - β * γ))) • (v - 0)) by
      exact smul_right_injective V3 hkey h
    rw [h1, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hkey, mul_neg,
      mul_div_cancel₀ _ hkey]
    all_goals module
  · refine ⟨-(γ / (α * δ - β * γ)), α / (α * δ - β * γ), ?_⟩
    have h1 : (α * δ - β * γ) • (b - 0) = -(γ) • (u - 0) + α • (v - 0) := by
      rw [hu', hv']
      module
    suffices h : (α * δ - β * γ) • (b - 0)
        = (α * δ - β * γ) • ((-(γ / (α * δ - β * γ))) • (u - 0)
          + (α / (α * δ - β * γ)) • (v - 0)) by
      exact smul_right_injective V3 hkey h
    rw [h1, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hkey, mul_neg,
      mul_div_cancel₀ _ hkey]
    all_goals module

/-! ## rung 5: the k = 6 diagonal-2 squeeze package -/

/-- Right-smul for the file's dot product (twin of `pmDotSmulL_p35`). -/
private theorem pmDotSmulR_p35 (t : ℝ) (p r : Fin 3 → ℝ) :
    p ⬝ᵥ (t • r) = t * (r ⬝ᵥ p) := by
  rw [dotProduct_comm, pmDotSmulL_p35]



/-- The k = 6 diagonal-2 squeeze (conditional package): with `x1` a ring
vertex, `ν` a unit in-plane normal of the `x1`-ray, and `u`, `w` two annulus
points at chord in `[2, 2·h0]` from `x1`, decomposed on opposite sides of the
`x1`-ray (`u = a•x1 + h1•ν`, `w = b•x1 + h2•ν`, `h1 ≤ 0 ≤ h2`), the height
core `pmHeightSq_p35` forces `dist u w > cstab`. -/
private theorem pmDiag2Squeeze_p35 {u x1 w ν : V3} {a b h1 h2 : ℝ}
    (hn : ‖ν‖ = 1) (hnx : (ν : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ) = 0)
    (hucoe : u - 0 = a • (x1 - 0) + h1 • (ν - 0))
    (hwcoe : w - 0 = b • (x1 - 0) + h2 • (ν - 0))
    (hsg1 : h1 ≤ 0) (hsg2 : 0 ≤ h2)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hux : ‖u‖ ≤ 2 * h0) (hx12 : (2:ℝ) ≤ ‖x1‖)
    (hx1 : ‖x1‖ ≤ 2 * h0) (hw2 : (2:ℝ) ≤ ‖w‖) (hwx : ‖w‖ ≤ 2 * h0)
    (hdu : (2:ℝ) ≤ dist u x1) (hdu' : dist u x1 ≤ 2 * h0)
    (hdw : (2:ℝ) ≤ dist w x1) (hdw' : dist w x1 ≤ 2 * h0) :
    cstab < dist u w := by
  have hH1raw : (4:ℝ) * ‖u‖ ^ 2 * ‖x1‖ ^ 2 - (‖u‖ ^ 2 + ‖x1‖ ^ 2 - dist u x1 ^ 2) ^ 2
      ≥ (5776 / 625) * ‖x1‖ ^ 2 := pmHeightSq_p35 hu2 hux hx12 hx1 hdu hdu'
  have hH2raw : (4:ℝ) * ‖w‖ ^ 2 * ‖x1‖ ^ 2 - (‖w‖ ^ 2 + ‖x1‖ ^ 2 - dist w x1 ^ 2) ^ 2
      ≥ (5776 / 625) * ‖x1‖ ^ 2 := pmHeightSq_p35 hw2 hwx hx12 hx1 hdw hdw'
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hux hx1 hdu' hdw' hwx
  simp only [sub_zero] at hucoe hwcoe
  have hucoe' : (u : Fin 3 → ℝ) = a • (x1 : Fin 3 → ℝ) + h1 • (ν : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hucoe
  have hwcoe' : (w : Fin 3 → ℝ) = b • (x1 : Fin 3 → ℝ) + h2 • (ν : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hwcoe
  have hnn : (ν : Fin 3 → ℝ) ⬝ᵥ (ν : Fin 3 → ℝ) = 1 := by
    rw [← pmNormSqDot_p35 ν, hn]
    norm_num
  have hnvx : (x1 : Fin 3 → ℝ) ⬝ᵥ (ν : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm, hnx]
  -- scalar coordinates
  have hux1d : (u : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)
      = a * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
    rw [hucoe', pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, hnx]
    ring
  have hun : (u : Fin 3 → ℝ) ⬝ᵥ (ν : Fin 3 → ℝ) = h1 := by
    rw [hucoe', pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, hnvx, hnn]
    ring
  have hu2d : ‖u‖ ^ 2
      = a ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) + h1 ^ 2 := by
    rw [pmNormSqDot_p35 u, hucoe', pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35,
      pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      hnvx, hnx, hnn]
    ring
  have hsubu : ((u - x1 : V3) : Fin 3 → ℝ)
      = (a - 1) • (x1 : Fin 3 → ℝ) + h1 • (ν : Fin 3 → ℝ) := by
    show (u : Fin 3 → ℝ) - (x1 : Fin 3 → ℝ) = _
    rw [hucoe']
    module
  have hddu : dist u x1 ^ 2
      = (a - 1) ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) + h1 ^ 2 := by
    have h1 : dist u x1 = ‖u - x1‖ := dist_eq_norm u x1
    have h2 := pmNormSqDot_p35 (u - x1)
    rw [h1, h2, hsubu, pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35,
      pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      hnvx, hnx, hnn]
    ring
  have hwx1d : (w : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)
      = b * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
    rw [hwcoe', pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, hnx]
    ring
  have hw2d : ‖w‖ ^ 2
      = b ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) + h2 ^ 2 := by
    rw [pmNormSqDot_p35 w, hwcoe', pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35,
      pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      hnvx, hnx, hnn]
    ring
  have hsubw : ((w - x1 : V3) : Fin 3 → ℝ)
      = (b - 1) • (x1 : Fin 3 → ℝ) + h2 • (ν : Fin 3 → ℝ) := by
    show (w : Fin 3 → ℝ) - (x1 : Fin 3 → ℝ) = _
    rw [hwcoe']
    module
  have hddw : dist w x1 ^ 2
      = (b - 1) ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) + h2 ^ 2 := by
    have h1 : dist w x1 = ‖w - x1‖ := dist_eq_norm w x1
    have h2 := pmNormSqDot_p35 (w - x1)
    rw [h1, h2, hsubw, pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35,
      pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      hnvx, hnx, hnn]
    ring
  -- height core consumption
  have hx1n : ‖x1‖ ^ 2 = (x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ) := pmNormSqDot_p35 x1
  have hx1p : (0:ℝ) < (x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ) := by
    have h4 : (4:ℝ) ≤ ‖x1‖ ^ 2 := by nlinarith [hx12]
    rw [← pmNormSqDot_p35 x1]
    linarith
  have hH1' : (4:ℝ) * h1 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
      ≥ (5776 / 625) * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
    have e : (4:ℝ) * ‖u‖ ^ 2 * ‖x1‖ ^ 2 - (‖u‖ ^ 2 + ‖x1‖ ^ 2 - dist u x1 ^ 2) ^ 2
        = (4:ℝ) * h1 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
      rw [hu2d, hx1n, hddu]
      ring
    rw [e, hx1n] at hH1raw
    exact hH1raw
  have hAb1 : (1444 / 625) ≤ h1 ^ 2 := by
    have hprod : (0:ℝ) ≤ ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
        * (4 * h1 ^ 2 - 5776 / 625) := by
      have e : ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
          * (4 * h1 ^ 2 - 5776 / 625)
          = (4:ℝ) * h1 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
            - (5776 / 625) * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by ring
      rw [e]
      linarith [hH1', hx1p.le]
    rcases lt_or_ge (4 * h1 ^ 2) (5776 / 625) with hc | hc
    · exact absurd (mul_neg_of_pos_of_neg hx1p (by linarith)) (not_lt.mpr hprod)
    · linarith [hc]
  have hneg1 : h1 ≤ -(38 / 25) := by
    by_contra hcon
    have h1b : h1 > -(38 / 25) := by linarith
    have hprod : (0:ℝ) < h1 * (h1 + 38 / 25) := by
      have e : h1 * (h1 + 38 / 25) = h1 ^ 2 + (38 / 25) * h1 := by ring
      rw [e]
      linarith [hAb1, h1b]
    have hprod2 : h1 * (h1 + 38 / 25) ≤ 0 := by
      have h2n : (0:ℝ) ≤ h1 + 38 / 25 := by linarith
      have e : h1 * (h1 + 38 / 25) ≤ 0 * (h1 + 38 / 25) :=
        mul_le_mul_of_nonneg_right hsg1 h2n
      linarith [e]
    linarith
  have hH2' : (4:ℝ) * h2 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
      ≥ (5776 / 625) * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
    have e : (4:ℝ) * ‖w‖ ^ 2 * ‖x1‖ ^ 2 - (‖w‖ ^ 2 + ‖x1‖ ^ 2 - dist w x1 ^ 2) ^ 2
        = (4:ℝ) * h2 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by
      rw [hw2d, hx1n, hddw]
      ring
    rw [e, hx1n] at hH2raw
    exact hH2raw
  have hAb2 : (1444 / 625) ≤ h2 ^ 2 := by
    have hprod : (0:ℝ) ≤ ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
        * (4 * h2 ^ 2 - 5776 / 625) := by
      have e : ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
          * (4 * h2 ^ 2 - 5776 / 625)
          = (4:ℝ) * h2 ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ))
            - (5776 / 625) * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) := by ring
      rw [e]
      linarith [hH2', hx1p.le]
    rcases lt_or_ge (4 * h2 ^ 2) (5776 / 625) with hc | hc
    · exact absurd (mul_neg_of_pos_of_neg hx1p (by linarith)) (not_lt.mpr hprod)
    · linarith [hc]
  have hpos2 : (38 / 25 : ℝ) ≤ h2 := by
    rcases lt_or_ge h2 (38 / 25) with hc | hc
    · have t : (0:ℝ) < (38 / 25 - h2) * (38 / 25 + h2) := mul_pos (by linarith) (by linarith)
      nlinarith [hAb2, t]
    · exact hc
  -- squeeze
  have hsubw2 : ((u - w : V3) : Fin 3 → ℝ)
      = (a - b) • (x1 : Fin 3 → ℝ) + (h1 - h2) • (ν : Fin 3 → ℝ) := by
    show (u : Fin 3 → ℝ) - (w : Fin 3 → ℝ) = _
    rw [hucoe', hwcoe']
    module
  have hd2c : dist u w ^ 2
      = (a - b) ^ 2 * ((x1 : Fin 3 → ℝ) ⬝ᵥ (x1 : Fin 3 → ℝ)) + (h1 - h2) ^ 2 := by
    have h1 : dist u w = ‖u - w‖ := dist_eq_norm u w
    have h2 := pmNormSqDot_p35 (u - w)
    rw [h1, h2, hsubw2, pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmDotSmulL_p35,
      pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      hnvx, hnx, hnn]
    ring
  have hcstab : cstab = 301 / 100 := by norm_num [cstab]
  rw [hcstab]
  have hdiff : (76 / 25 : ℝ) ≤ h2 - h1 := by linarith
  have hsq76 : (h2 - h1) ^ 2 ≥ (76 / 25) ^ 2 := by nlinarith
  have hstep1 : (h1 - h2) ^ 2 ≤ dist u w ^ 2 := by
    rw [hd2c]
    exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg (a - b)) (le_of_lt hx1p))
  have hstep2 : (h1 - h2) ^ 2 = (h2 - h1) ^ 2 := by ring
  have hsq301 : (301 / 100 : ℝ) ^ 2 < (76 / 25) ^ 2 := by norm_num
  rcases le_or_gt (dist u w) (301 / 100) with hd | hd
  · exfalso
    have hd2le : dist u w ^ 2 ≤ (301 / 100) ^ 2 := by
      nlinarith [hd, (dist_nonneg : (0:ℝ) ≤ dist u w)]
    linarith [hstep1, hstep2, hsq76, hsq301, hd2le]
  · exact hd
/-- Unordered collinearity swap (second and third point commute). -/
private theorem coll3swap_p35 {v w1 w2 : V3} : Collinear3 v w1 w2 ↔ Collinear3 v w2 w1 := by
  show Collinear ℝ ({v, w1, w2} : Set V3) ↔ Collinear ℝ ({v, w2, w1} : Set V3)
  rw [show ({v, w1, w2} : Set V3) = ({v, w2, w1} : Set V3) from by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]

/-- In-plane azimuth placement (new kit item, lkgrqui-sectortri-asm-w3): a
point of the plane through `0`, `a`, `b` lies at azimuth `0` (positive
`b`-side, including the axis) or `π` (negative `b`-side). -/
private theorem azimPlanePlace_p35 {a b x : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b) (hx : ∃ s t : ℝ, x - 0 = s • (a - 0) + t • (b - 0)) :
    azim 0 a b x = 0 ∨ azim 0 a b x = Real.pi := by
  obtain ⟨s, t, hx'⟩ := hx
  by_cases hcolx : Collinear3 0 a x
  · exact Or.inl (by rw [azim, if_pos (Or.inr hcolx)])
  rcases lt_trichotomy t 0 with ht0 | ht00 | ht1
  · -- negative side: azimuth π (frame computation)
    have hge : (0:ℝ) ≤ azim 0 a b x := azim_nonneg 0 a b x
    have hlt : azim 0 a b x < 2 * Real.pi := azim_lt_two_pi 0 a b x
    obtain ⟨e1, e2, e3, hon, hal⟩ := exists_on3_eq_smul (a - 0) (sub_ne_zero.mpr ha0)
    have hax : (a - 0 : V3) = dist a 0 • e3 := by rw [dist_eq_norm]; exact hal
    obtain ⟨ψ, r1, r2, hr1, hr2, hzb, hzx⟩ := azim_frame_spec hnc hcolx hon hax
      (by simpa using ha0)
    have hza : zOf e1 e2 (a - 0) = 0 := zOf_axis hax hon
    have hlin : zOf e1 e2 (x - 0) = (t:ℂ) * zOf e1 e2 (b - 0) := by
      rw [hx', zOf_add, zOf_smul, zOf_smul, hza, mul_zero, zero_add]
    have hexp : Complex.exp (((Real.pi:ℝ):ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
    have hkey : (r2:ℂ) * Complex.exp (((ψ + azim 0 a b x : ℝ):ℂ) * Complex.I)
        = (((-t) * r1 : ℝ):ℂ) * Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I) := by
      have hex : Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I)
          = Complex.exp (((ψ:ℝ):ℂ) * Complex.I) * (-1) := by
        have hsplit : ((ψ + Real.pi : ℝ):ℂ) * Complex.I
            = ((ψ:ℝ):ℂ) * Complex.I + ((Real.pi:ℝ):ℂ) * Complex.I := by
          rw [Complex.ofReal_add]
          ring
        rw [hsplit, Complex.exp_add, hexp]
      rw [← hzx, hlin, hzb, hex]
      push_cast
      ring
    have hexeq : Complex.exp (((ψ + azim 0 a b x : ℝ):ℂ) * Complex.I)
        = Complex.exp (((ψ + Real.pi : ℝ):ℂ) * Complex.I) :=
      exp_pos_mul_eq hr2 (mul_pos (by linarith : (0:ℝ) < -t) hr1) hkey
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexeq
    -- hn : (ψ + θ) * I = (ψ + π) * I + n * (2 * π * I)
    have hθ : azim 0 a b x = Real.pi + (n:ℝ) * (2 * Real.pi) := by
      have h4 := hn
      push_cast at h4
      rw [add_mul, add_mul] at h4
      have h5 : ((azim 0 a b x : ℝ):ℂ) * Complex.I
          = ((Real.pi:ℝ):ℂ) * Complex.I
            + ((n:ℂ) * (2 * ((Real.pi:ℝ):ℂ) * Complex.I)) := by
        linear_combination h4
      have h6 : (((azim 0 a b x : ℝ) - Real.pi : ℝ):ℂ) * Complex.I
          = ((n:ℂ) * (2 * ((Real.pi:ℝ):ℂ))) * Complex.I := by
        rw [Complex.ofReal_sub]
        linear_combination h5
      have h10 := mul_right_cancel₀ Complex.I_ne_zero h6
      have h11 := congrArg Complex.re h10
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero] at h11
      norm_num at h11
      linarith
    have hπ0 : (0:ℝ) < Real.pi := Real.pi_pos
    have h2π : (0:ℝ) < 2 * Real.pi := by linarith
    rcases Int.lt_trichotomy n 0 with hn0 | hn00 | hn1
    · exfalso
      have hnle : ((n:ℤ):ℝ) ≤ ((-1:ℤ):ℝ) := Int.cast_le.mpr (by omega)
      simp only [Int.cast_neg, Int.cast_one] at hnle
      have hmul : (2:ℝ) * Real.pi * ((n:ℤ):ℝ) ≤ (2:ℝ) * Real.pi * (-1) :=
        mul_le_mul_of_nonneg_left hnle h2π.le
      rw [hθ] at hge
      nlinarith [hmul, hπ0]
    · refine Or.inr ?_
      rw [hθ, hn00]
      push_cast
      ring
    · exfalso
      have hnge : ((1:ℤ):ℝ) ≤ ((n:ℤ):ℝ) := Int.cast_le.mpr (by omega)
      simp only [Int.cast_one] at hnge
      have hmul : (2:ℝ) * Real.pi * 1 ≤ (2:ℝ) * Real.pi * ((n:ℤ):ℝ) :=
        mul_le_mul_of_nonneg_left hnge h2π.le
      rw [hθ] at hlt
      nlinarith [hmul, hπ0]
  · -- t = 0: x on the axis
    exfalso
    simp only [ht00, zero_smul, add_zero] at hx'
    exact hcolx ((collinear3_iff_smul ha0).mpr ⟨s, hx'⟩)
  · -- positive side: azimuth 0
    refine Or.inl ((azim_eq_zero_iff_alt hnc hcolx).mpr ?_)
    refine (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := b) (y := x)
      (Ne.symm ha0) hb0 (fun he => hnc (by rw [he]; exact collinear3_pair_right rfl))).mpr
      ⟨t, ht1, s, by rw [hx']; module⟩

/-! ## planemiss5 rungs (lkgrqui-planemiss5-w3, 2026-10-28)

The (A)-winding ladder pieces, all conditional (private, `_p35` new names):
the in-plane azimuth sign bridge, the double-face cone packaging, the
below-π sector collapse, the axis-line pair kill, and the flat-run normal
parallelism.  Insertion point: after `azimPlanePlace_p35`. -/

/-- Plane-coordinate uniqueness: the `(a, b)`-coordinates of a plane vector
are unique (`a`, `b` independent at `0`). -/
private theorem pmPlaneCoordUnique_p35 {a b : V3} (ha0 : a ≠ 0)
    (hnc : ¬ Collinear3 0 a b) {s1 t1 s2 t2 : ℝ}
    (h : s1 • (a - 0) + t1 • (b - 0) = s2 • (a - 0) + t2 • (b - 0)) :
    s1 = s2 ∧ t1 = t2 := by
  have hz : (s1 - s2) • (a - 0) + (t1 - t2) • (b - 0) = (0:V3) := by
    have e : (s1 • (a - 0) + t1 • (b - 0)) - (s2 • (a - 0) + t2 • (b - 0))
        = (s1 - s2) • (a - 0) + (t1 - t2) • (b - 0) := by
      rw [sub_smul, sub_smul]
      module
    rw [← e, h]
    simp
  rcases eq_or_ne (t1 - t2) 0 with h0 | h0
  · rw [h0, zero_smul, add_zero] at hz
    have hs : s1 - s2 = 0 := by
      by_contra hc
      refine ha0 ?_
      apply smul_right_injective V3 hc
      show (s1 - s2) • (a:V3) = (s1 - s2) • (0:V3)
      rw [show (s1 - s2) • (a:V3) = (s1 - s2) • (a - 0) from by rw [sub_zero],
        hz, smul_zero]
    exact ⟨by linarith, by linarith⟩
  · exfalso
    refine hnc ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
      ⟨-(s1 - s2) / (t1 - t2), ?_⟩)
    apply smul_right_injective V3 h0
    show (t1 - t2) • (b - 0) = (t1 - t2) • ((-(s1 - s2) / (t1 - t2)) • (a - 0))
    rw [smul_smul, mul_comm, div_mul_cancel₀ _ h0, neg_smul]
    exact (neg_eq_of_add_eq_zero_right hz).symm

/-- Plane-coordinate vanishing: `(s, t) = (0, 0)` is the only vanishing
combination of two independent plane vectors. -/
private theorem pmPlaneCoordZero_p35 {a b : V3} (ha0 : a ≠ 0)
    (hnc : ¬ Collinear3 0 a b) {s t : ℝ} (h : s • (a - 0) + t • (b - 0) = (0:V3)) :
    s = 0 ∧ t = 0 := by
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, zero_smul, add_zero] at h
    have hs : s = 0 := by
      by_contra hc
      refine ha0 ?_
      apply smul_right_injective V3 hc
      show s • (a:V3) = s • (0:V3)
      rw [show s • (a:V3) = s • (a - 0) from by rw [sub_zero], h, smul_zero]
    exact ⟨hs, ht⟩
  · exfalso
    refine hnc ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
      ⟨-s / t, ?_⟩)
    apply smul_right_injective V3 ht
    show t • (b - 0) = t • ((-s / t) • (a - 0))
    rw [smul_smul, mul_comm, div_mul_cancel₀ _ ht, neg_smul]
    exact (neg_eq_of_add_eq_zero_right h).symm

/-- **(A)-rung A1 (pm5)**: in-plane azimuth sign bridge, positive side — a
plane point `x = s•a + t•b` with `t ≥ 0` sits at azimuth `0`. -/
private theorem pmAzimPlanePos_p35 {a b x : V3} {s t : ℝ} (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hnc : ¬ Collinear3 0 a b)
    (hx : x - 0 = s • (a - 0) + t • (b - 0)) (ht : 0 ≤ t) :
    azim 0 a b x = 0 := by
  by_cases hcolx : Collinear3 0 a x
  · exact azimAxis_p35 hcolx
  · have htp : 0 < t := by
      rcases lt_trichotomy t 0 with htn | ht00 | htp
      · exact absurd htn (not_lt.mpr ht)
      · refine absurd ((collinear3_iff_smul
          (v := (0:V3)) (w := a) (w1 := x) ha0).mpr ⟨s, ?_⟩) hcolx
        rw [ht00, zero_smul, add_zero] at hx
        exact hx
      · exact htp
    exact (azim_eq_zero_iff_alt hnc hcolx).mpr
      ((affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := b) (y := x)
        (Ne.symm ha0) hb0 (fun he => hnc (by rw [he]; exact collinear3_pair_right rfl))).mpr
        ⟨t, htp, s, by rw [hx, add_comm]⟩)

/-- **(A)-rung A2 (pm5)**: in-plane azimuth sign bridge, negative side — a
plane point `x = s•a + t•b` with `t < 0` sits at azimuth `π`. -/
private theorem pmAzimPlaneNeg_p35 {a b x : V3} {s t : ℝ} (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hnc : ¬ Collinear3 0 a b)
    (hx : x - 0 = s • (a - 0) + t • (b - 0)) (ht : t < 0) :
    azim 0 a b x = Real.pi := by
  have hcolx : ¬ Collinear3 0 a x := by
    intro hcol
    obtain ⟨lam, hlam⟩ := (collinear3_iff_smul
      (v := (0:V3)) (w := a) (w1 := x) ha0).mp hcol
    have h2 : t • (b - 0) + s • (a - 0) = lam • (a - 0) := by
      rw [add_comm, ← hx, hlam]
    have htb : t • (b - 0) = (lam - s) • (a - 0) := by
      rw [sub_smul, ← h2]
      module
    have ht0 : t ≠ 0 := ne_of_lt ht
    refine hnc ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
      ⟨(lam - s) / t, ?_⟩)
    apply smul_right_injective V3 ht0
    show t • (b - 0) = t • (((lam - s) / t) • (a - 0))
    rw [smul_smul, mul_comm, div_mul_cancel₀ _ ht0]
    exact htb
  rcases azimPlanePlace_p35 ha0 hb0 hnc ⟨s, t, hx⟩ with h0 | hpi
  · exfalso
    obtain ⟨c, hc, e, he⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := b) (y := x)
        (Ne.symm ha0) hb0 (fun heq => hnc (by rw [heq]; exact collinear3_pair_right rfl))).mp
        ((azim_eq_zero_iff_alt hnc hcolx).mp h0)
    have hcoord : e • (a - 0) + c • (b - 0) = s • (a - 0) + t • (b - 0) := by
      rw [add_comm (e • (a - 0)) (c • (b - 0)), ← he, ← hx]
    have hct : c = t := (pmPlaneCoordUnique_p35 ha0 hnc hcoord).2
    linarith
  · exact hpi


/-! ## planemiss6 rungs (lkgrqui-planemiss6-w3, 2026-10-28)

The (A)-winding Fork-2 package: with `e := vv (j+2)` strictly off the dart
face plane `P := {x | ∃ s t, x - 0 = s • (vv j - 0) + t • (vv (j + 1) - 0)}`
and the sector span at dart `j` strictly below `π`, the two diagonal
endpoints `u`, `w` (which sit in `P`) are trapped in the closed positive cone
`affGe {0} {vv j, vv (j+1)}` (the b-coefficient bound from the dart-`(j+1)`
half-space and the c-coefficient bound from the dart-`(j+k-1)` half-space),
so the `fan7` cone-disjointness (`affGe` half-space distributivity, part of
`FAN 0 (Set.range vv) E`) forces each endpoint into the cone of its own
dart; the residue bookkeeping then contradicts `scsDiag` (distinct
non-adjacent residues) or the annulus (a cone point would be `0`).
Insertion point: after `pmAzimPlaneNeg_p35`, before `pmTwoFaceCone_p35`. -/

/-- Successor residues lift through the mod. -/
private theorem pmSuccMod_p35 {k : ℕ} (hk0 : 0 < k) (a : ℕ) :
    (a + 1) % k = (a % k + 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1:ℕ) < k by omega)]

/-- `(m + 1 + (k - 1)) % k = m % k` (predecessor collapse). -/
private theorem pmModSuccPred_p35 {k : ℕ} (hk0 : 0 < k) (m : ℕ) :
    (m + 1 + (k - 1)) % k = m % k := by
  rw [Nat.add_assoc]
  have h1 : 1 + (k - 1) = k := by omega
  rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.mod_lt _ hk0)]

/-- Scalar triple product, cyclic invariance. -/
private theorem pmDetCyc_p35 (p q r : Fin 3 → ℝ) :
    (crossProduct p q) ⬝ᵥ r = (crossProduct q r) ⬝ᵥ p := by
  rw [dotProduct_comm (crossProduct p q) r, dotProduct_comm (crossProduct q r) p]
  exact triple_product_permutation r p q

/-- The closed `{0}`-cone over a pair: membership from nonnegative plane
coordinates (via the `Affsign.of_triple` witness). -/
private theorem pmConeMem_p35 {b c x : V3} (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hbc : b ≠ c) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : x - 0 = α • (b - 0) + β • (c - 0)) :
    x ∈ affGe ({0} : Set V3) {b, c} := by
  simp only [sub_zero] at hx
  exact Affsign.of_triple (sgn := fun r => 0 ≤ r) α β hα hβ
    (by rw [hx]; simp) (Ne.symm hb0) (Ne.symm hc0) hbc

/-- Self-cone membership: `x` sits in the closed cone over its own dart. -/
private theorem pmSelfCone_p35 {x y : V3} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    x ∈ affGe ({0} : Set V3) {x, y} :=
  Affsign.of_triple (sgn := fun r => 0 ≤ r) 1 0 (by norm_num) (by norm_num)
    (by simp) (Ne.symm hx0) (Ne.symm hy0) hxy

/-- **(A)-rung B1 (pm6)**: the b-coefficient bound — a plane point `y =
α•b + β•c` with the dart-`(j+1)` half-space against a strictly positive
`(b × c) ⬝ᵥ e` has `0 ≤ α`. -/
private theorem pmAlphaGe_p35 {b c e y : V3} {α β : ℝ}
    (hhs : 0 ≤ (crossProduct (c : Fin 3 → ℝ) (e : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ))
    (hy : y - 0 = α • (b - 0) + β • (c - 0))
    (heh : 0 < (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (e : Fin 3 → ℝ)) :
    0 ≤ α := by
  simp only [sub_zero] at hy
  have hycoe : (y : Fin 3 → ℝ) = α • (b : Fin 3 → ℝ) + β • (c : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hy
  have hsplit : (crossProduct (c : Fin 3 → ℝ) (e : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)
      = α * ((crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (e : Fin 3 → ℝ)) := by
    rw [hycoe, pmDotAddR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      dot_self_cross c e, mul_zero, add_zero,
      dotProduct_comm b (crossProduct c e), pmDetCyc_p35 c e b, pmDetCyc_p35 e b c]
  rw [hsplit] at hhs
  by_cases hα0 : 0 ≤ α
  · exact hα0
  · exfalso
    exact absurd (mul_neg_of_neg_of_pos (lt_of_not_ge hα0) heh) (not_lt.mpr hhs)

/-- **(A)-rung B2 (pm6)**: the c-coefficient bound — a plane point `y =
α•b + β•c` with the dart-`(j+k-1)` half-space against a strictly positive
`(b × c) ⬝ᵥ d` has `0 ≤ β`. -/
private theorem pmBetaGe_p35 {b c d y : V3} {α β : ℝ}
    (hhs : 0 ≤ (crossProduct (d : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ))
    (hy : y - 0 = α • (b - 0) + β • (c - 0))
    (hdh : 0 < (crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (d : Fin 3 → ℝ)) :
    0 ≤ β := by
  simp only [sub_zero] at hy
  have hycoe : (y : Fin 3 → ℝ) = α • (b : Fin 3 → ℝ) + β • (c : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hy
  have hsplit : (crossProduct (d : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ)
      = β * ((crossProduct (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)) ⬝ᵥ (d : Fin 3 → ℝ)) := by
    rw [hycoe, pmDotAddR_p35, pmDotSmulR_p35, pmDotSmulR_p35,
      dot_cross_self d b, mul_zero, zero_add,
      dotProduct_comm c (crossProduct d b), pmDetCyc_p35 d b c]
  rw [hsplit] at hhs
  by_cases hβ0 : 0 ≤ β
  · exact hβ0
  · exfalso
    exact absurd (mul_neg_of_neg_of_pos (lt_of_not_ge hβ0) hdh) (not_lt.mpr hhs)

/-- **(A)-rung B3 (pm6): the Fork-2 kill** — with `vv (j+2)` strictly off
the dart-`j` face plane and the sector span at dart `j` strictly below `π`,
the two plane-trapped diagonal endpoints die. -/
private theorem pmFork2Kill_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (j : ℕ)
    (hu : ∃ c d : ℝ, u - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (hw : ∃ c d : ℝ, w - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (heP : ¬ ∃ c d : ℝ, vv (j + 1 + 1) - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (hθlt : azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) < Real.pi) : False := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hf7 := hfan'.2.2.2.2.2
  have hvne : ∀ i : ℕ, vv i ≠ (0:V3) := by
    intro i hi
    exact hfan'.2.2.2.1 (hi ▸ (Set.mem_range.mpr ⟨i, rfl⟩ : vv i ∈ Set.range vv))
  have hncbc : ¬ Collinear3 0 (vv j) (vv (j + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j, rfl⟩)
  have hb0 : vv j ≠ (0:V3) := hvne j
  have hc0 : vv (j + 1) ≠ (0:V3) := hvne (j + 1)
  have hbc : vv j ≠ vv (j + 1) := by
    intro he
    exact hncbc (by rw [he]; exact collinear3_pair_right rfl)
  have hθne : azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) ≠ 0 :=
    dartSpanNeCyc_p35 hk3 hper hinj hE j hfan'
  have hdP : ¬ ∃ c₁ d₁ : ℝ, vv (j + s.k - 1) - 0
        = c₁ • (vv j - 0) + d₁ • (vv (j + 1) - 0) := by
    rintro ⟨c₁, d₁, hco⟩
    rcases azimPlanePlace_p35 hb0 hc0 hncbc ⟨c₁, d₁, hco⟩ with h0 | hπ
    · exact hθne h0
    · rw [hπ] at hθlt
      exact lt_irrefl _ hθlt
  obtain ⟨hsand, hθle⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
  obtain ⟨h0e, hle⟩ := hsand (vv (j + 1 + 1))
    (Set.mem_range.mpr ⟨j + 1 + 1, rfl⟩)
  have hncbe : ¬ Collinear3 0 (vv j) (vv (j + 1 + 1)) := by
    intro hcol
    obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
      (w1 := vv (j + 1 + 1)) hb0).mp hcol
    exact heP ⟨t, 0, by rw [ht]; simp⟩
  have h0ne : azim 0 (vv j) (vv (j + 1)) (vv (j + 1 + 1)) ≠ 0 := by
    intro h0
    obtain ⟨c₁, hc1, d₁, hd1⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := vv j) (x := vv (j + 1))
        (y := vv (j + 1 + 1)) (Ne.symm hb0) hc0
        (fun heq => hbc heq.symm)).mp
        ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := vv j)
          (w := vv (j + 1)) hncbc hncbe).mp h0)
    exact heP ⟨d₁, c₁, by rw [hd1]; exact add_comm _ _⟩
  have hbed : (0:ℝ) < (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
      (vv (j + 1 + 1) : Fin 3 → ℝ) := by
    simpa [sub_zero] using cross_dot_fully_surrounded_fan (x := 0)
      (v1 := vv j) (v := vv (j + 1)) (u1 := vv (j + 1 + 1)) hncbe hncbc
      (lt_of_le_of_ne h0e (Ne.symm h0ne)) (lt_of_le_of_lt hle hθlt)
  obtain ⟨h0d, -⟩ := hsand (vv (j + s.k - 1))
    (Set.mem_range.mpr ⟨j + s.k - 1, rfl⟩)
  have hncbd : ¬ Collinear3 0 (vv j) (vv (j + s.k - 1)) := by
    intro hcol
    exact hθne (azimAxis_p35 (a := vv j) (b := vv (j + 1))
      (x := vv (j + s.k - 1)) hcol)
  have h0d' : 0 < azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) :=
    lt_of_le_of_ne h0d (fun hh => hθne hh.symm)
  have hbcd : (0:ℝ) < (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
      (vv (j + s.k - 1) : Fin 3 → ℝ) := by
    simpa [sub_zero] using cross_dot_fully_surrounded_fan (x := 0) (v1 := vv j)
      (v := vv (j + 1)) (u1 := vv (j + s.k - 1)) hncbd hncbc h0d' hθlt
  have hhse : ∀ y ∈ Set.range vv,
      0 ≤ (crossProduct (vv (j + 1) : Fin 3 → ℝ) (vv (j + 1 + 1) : Fin 3 → ℝ)) ⬝ᵥ
        (y : Fin 3 → ℝ) := fun y hy =>
    pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + 1) y hy
  have hhsd : ∀ y ∈ Set.range vv,
      0 ≤ (crossProduct (vv (j + s.k - 1) : Fin 3 → ℝ) (vv j : Fin 3 → ℝ)) ⬝ᵥ
        (y : Fin 3 → ℝ) := by
    intro y hy
    have h1 := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + s.k - 1) y hy
    have hvsi : vv ((j + s.k - 1) + 1) = vv j := by
      rw [show (j + s.k - 1) + 1 = j + s.k from by omega]
      exact wedgeVvAddK_p35 hper j
    rw [hvsi] at h1
    exact h1
  obtain ⟨αu, βu, hucoe⟩ := hu
  obtain ⟨αw, βw, hwcoe⟩ := hw
  have hαu : 0 ≤ αu := pmAlphaGe_p35
    (hhse u (Set.mem_range.mpr ⟨p % s.k, hp⟩)) hucoe hbed
  have hαw : 0 ≤ αw := pmAlphaGe_p35
    (hhse w (Set.mem_range.mpr ⟨q % s.k, hq⟩)) hwcoe hbed
  have hβu : 0 ≤ βu := pmBetaGe_p35 (hhsd u (Set.mem_range.mpr ⟨p % s.k, hp⟩)) hucoe hbcd
  have hβw : 0 ≤ βw := pmBetaGe_p35 (hhsd w (Set.mem_range.mpr ⟨q % s.k, hq⟩)) hwcoe hbcd
  have huCone : u ∈ affGe ({0} : Set V3) {vv j, vv (j + 1)} :=
    pmConeMem_p35 hb0 hc0 hbc hαu hβu hucoe
  have hwCone : w ∈ affGe ({0} : Set V3) {vv j, vv (j + 1)} :=
    pmConeMem_p35 hb0 hc0 hbc hαw hβw hwcoe
  have hpm : vv p = u := by rw [← hp]; exact (periodic_mod_eq_p23 hper p).symm
  have hqm : vv q = w := by rw [← hq]; exact (periodic_mod_eq_p23 hper q).symm
  have hEj : ({vv j, vv (j + 1)} : Set V3) ∈ E := (dartEdgeMems_p35 hk3 hper hE j).1
  have hdisj : ∀ (i : ℕ), vv i ∈ affGe ({0} : Set V3) {vv j, vv (j + 1)} →
      vv i ≠ vv j → vv i ≠ vv (j + 1) →
      vv (i + 1) ≠ vv j → vv (i + 1) ≠ vv (j + 1) → False := by
    intro i hzC h1 h2 h3 h4
    have hncdi : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
      Kepler.Text.Fan.fan_not_collinear hfan'
        (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
    have hz2 : vv i ∈ affGe ({0} : Set V3) {vv i, vv (i + 1)} :=
      pmSelfCone_p35 (hvne i) (hvne (i + 1)) (fun he =>
        hncdi (by rw [he]; exact collinear3_pair_right rfl))
    have hEi : ({vv i, vv (i + 1)} : Set V3) ∈ E := (dartEdgeMems_p35 hk3 hper hE i).1
    have hempty : ({vv j, vv (j + 1)} ∩ {vv i, vv (i + 1)} : Set V3) = ∅ := by
      ext z'
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.notMem_empty, iff_false]
      intro hcon
      obtain ⟨hA, hB⟩ := hcon
      rcases hA with hA' | hA' <;> rcases hB with hB' | hB'
      · exact h1 (hB'.symm.trans hA')
      · exact h3 (hB'.symm.trans hA')
      · exact h2 (hB'.symm.trans hA')
      · exact h4 (hB'.symm.trans hA')
    have hz0 := hf7 {vv j, vv (j + 1)}
      (Set.mem_union_left {s | ∃ v ∈ Set.range vv, s = {v}} hEj) {vv i, vv (i + 1)}
      (Set.mem_union_left {s | ∃ v ∈ Set.range vv, s = {v}} hEi)
    rw [hempty] at hz0
    have hmem : vv i ∈ (affGe ({0} : Set V3) (∅ : Set V3)) := by
      rw [← hz0]
      exact Set.mem_inter hzC hz2
    have hmem' : vv i ∈ affGe ({0} : Set V3) (∅ : Set V3) := hmem
    simp only [affGe, Affsign, Set.mem_setOf_eq] at hmem'
    rw [Set.union_empty] at hmem'
    obtain ⟨f, hf, hz, -, -⟩ := hmem'
    have hto : hf.toFinset = {0} := Set.Finite.toFinset_singleton
    rw [hto] at hz
    simp at hz
    exact hvne i hz
  -- successor = vv m transport: from `vv (i + 1) = vv m` get `vv i = vv (m + s.k - 1)`
  have hsuccpred : ∀ (i m : ℕ), vv (i + 1) = vv m → vv i = vv (m + s.k - 1) := by
    intro i m hiz
    have hstep := vvModEq_p35 hk0 hper hinj hiz
    have hsk1 : 1 ≤ s.k := by omega
    have h1 : (i + 1) + (s.k - 1) = i + s.k := by omega
    have e1 : ((i + 1) + (s.k - 1)) % s.k = (m + (s.k - 1)) % s.k :=
      Nat.ModEq.add_right (s.k - 1) hstep
    rw [h1, show (i:ℕ) + s.k = i + s.k * 1 from by rw [Nat.mul_one],
      Nat.add_mul_mod_self_left, ← Nat.add_sub_assoc hsk1 m] at e1
    have key : i % s.k = (m + s.k - 1) % s.k := e1
    rw [← periodic_mod_eq_p23 hper i, key, periodic_mod_eq_p23 hper (m + s.k - 1)]
  -- successor-on-d killer: x's successor is d and x carries plane coords
  have hsuccd : ∀ (i : ℕ) (x : V3), vv (i + 1) = vv j →
      (∃ c₁ d₁ : ℝ, x - 0 = c₁ • (vv j - 0) + d₁ • (vv (j + 1) - 0)) →
      vv i = x → False := by
    intro i x hiz hco hix
    have htr := hsuccpred i j hiz
    obtain ⟨c₁, d₁, hco'⟩ := hco
    rw [← hix, htr] at hco'
    exact hdP ⟨c₁, d₁, hco'⟩
  by_cases hu1 : u = vv j
  · have hpj : p % s.k = j % s.k :=
      vvModEq_p35 hk0 hper hinj (by rw [hpm, hu1])
    by_cases hw1 : w = vv j
    · exact hdiag.1 (by
        rw [hpj, vvModEq_p35 hk0 hper hinj (by rw [hqm, hw1])])
    by_cases hw2 : w = vv (j + 1)
    · refine hdiag.2.1 ?_
      have hqj : q % s.k = (j + 1) % s.k :=
        vvModEq_p35 hk0 hper hinj (by rw [hqm, hw2])
      rw [pmSuccMod_p35 hk0 p, hpj, hqj, ← pmSuccMod_p35 hk0 j]
    by_cases hw3 : vv (q % s.k + 1) = vv j
    · exact hsuccd (q % s.k) w hw3 ⟨αw, βw, hwcoe⟩ hq
    by_cases hw4 : vv (q % s.k + 1) = vv (j + 1)
    · have hqj : q % s.k = j % s.k := by
        have heq := vvModPred_p35 hk0 (vvModEq_p35 hk0 hper hinj hw4)
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hk0)] at heq
        exact heq
      exact hw1 (by rw [← hq, hqj, ← periodic_mod_eq_p23 hper j])
    · exact hdisj (q % s.k) (by rw [hq]; exact hwCone)
        (by rw [hq]; exact hw1) (by rw [hq]; exact hw2) hw3 hw4
  by_cases hu2 : u = vv (j + 1)
  · have hpj : p % s.k = (j + 1) % s.k :=
      vvModEq_p35 hk0 hper hinj (by rw [hpm, hu2])
    by_cases hw1 : w = vv j
    · refine hdiag.2.2 ?_
      have hqj : q % s.k = j % s.k :=
        vvModEq_p35 hk0 hper hinj (by rw [hqm, hw1])
      rw [hpj, pmSuccMod_p35 hk0 q, hqj, pmSuccMod_p35 hk0 j]
    by_cases hw2 : w = vv (j + 1)
    · exact hdiag.1 (by
        rw [hpj, vvModEq_p35 hk0 hper hinj (by rw [hqm, hw2])])
    by_cases hw3 : vv (q % s.k + 1) = vv j
    · exact hsuccd (q % s.k) w hw3 ⟨αw, βw, hwcoe⟩ hq
    by_cases hw4 : vv (q % s.k + 1) = vv (j + 1)
    · have hqj : q % s.k = j % s.k := by
        have heq := vvModPred_p35 hk0 (vvModEq_p35 hk0 hper hinj hw4)
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hk0)] at heq
        exact heq
      exact hw1 (by rw [← hq, hqj, ← periodic_mod_eq_p23 hper j])
    · exact hdisj (q % s.k) (by rw [hq]; exact hwCone)
        (by rw [hq]; exact hw1) (by rw [hq]; exact hw2) hw3 hw4
  · by_cases hu3 : vv (p % s.k + 1) = vv j
    · exact hsuccd (p % s.k) u hu3 ⟨αu, βu, hucoe⟩ hp
    by_cases hu4 : vv (p % s.k + 1) = vv (j + 1)
    · have hpj : p % s.k = j % s.k := by
        have heq := vvModPred_p35 hk0 (vvModEq_p35 hk0 hper hinj hu4)
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hk0)] at heq
        exact heq
      exact hu1 (by rw [← hp, ← periodic_mod_eq_p23 hper j]; exact congrArg vv hpj)
    · exact hdisj (p % s.k) (by rw [hp]; exact huCone)
        (by rw [hp]; exact hu1) (by rw [hp]; exact hu2) hu3 hu4
/-! ## planemiss7 rungs (lkgrqui-planemiss7-w3, 2026-10-28)

The (A)-winding closure kit, stage 1 (all private `_p35` new names, zero
sorry, no `open Classical` / `native_decide`):

1. `pmModNeGen_p35` / `pmVvModNe_p35` — modular index-arithmetic helpers.
2. `pmAzimOffPlaneNe_p35` — off-plane azimuth translator (`≠ 0` and `≠ π`).
3. `pmConeRingKill_p35` — no ring vertex (other than the dart pair and
   their cyclic neighbours) lies in the closed dart cone (`fan7`
   cone-disjointness, standalone).
4. `pmNegSideOfPi_p35` — azimuth `π` at dart `j` renders `d` in the plane
   with a strictly negative second coordinate.
5. `pmB2AntiWedge_p35` — in-plane `e` at azimuth `π` off the `b`-ray sits
   in the antipodal wedge (`ce < 0 ∧ de < 0`) and `a` sits at azimuth `π`
   of dart `j+1`.

Insertion point: immediately after `pmFork2Kill_p35`. -/

/-- Generic modular separation: for `0 < c < k` the residue cannot repeat
after a `c`-step. -/
private theorem pmModNeGen_p35 {k : ℕ} (hk0 : 0 < k) {x c : ℕ} (hc0 : 0 < c)
    (hck : c < k) (h : (x + c) % k = x % k) : False := by
  have hr : x % k < k := Nat.mod_lt x hk0
  have hc' : c % k = c := Nat.mod_eq_of_lt hck
  rw [Nat.add_mod, hc'] at h
  rcases Nat.lt_or_ge (x % k + c) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have e2 : (x % k + c) % k = (x % k + c - k) % k :=
      Nat.mod_eq_sub_mod hge
    rw [e2, Nat.mod_eq_of_lt (by omega : x % k + c - k < k)] at h
    omega

/-- Vertex-separation transport: distinct residues give distinct vertices. -/
private theorem pmVvModNe_p35 {vv : ℕ → V3} {k : ℕ} (hk0 : 0 < k)
    (hper : Periodic vv k)
    (hinj : ∀ x y : ℕ, x < k → y < k → x ≠ y → vv x ≠ vv y)
    {x y : ℕ} (hxy : x % k ≠ y % k) : vv x ≠ vv y := by
  intro heq
  exact hxy (vvModEq_p35 hk0 hper hinj heq)

/-- The anti-ray double for the `a`-line. -/
private theorem pmNegCollA_p35 {a b : V3} (ha0 : a ≠ 0)
    (hnc : ¬ Collinear3 0 a b) : ¬ Collinear3 0 a (-b) := by
  intro hcol
  obtain ⟨lam, hlam⟩ := (collinear3_iff_smul (v := (0:V3)) (w := a)
    (w1 := (-b)) ha0).mp hcol
  refine hnc ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
    ⟨-lam, ?_⟩)
  have hz : (-b - 0 : V3) = -(b - 0) := by
    simp
  have hz2 : b - 0 = -(lam • (a - 0)) := by
    rw [hz] at hlam
    rw [← hlam]
    simp
  rw [hz2, neg_smul]

/-- The `affGt {0, a} {-b}` side conditions bundle. -/
private theorem pmNegBNe_p35 {a b : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b) :
    (0:V3) ≠ a ∧ (-b) ≠ (0:V3) ∧ (-b) ≠ a := by
  refine ⟨Ne.symm ha0, ?_, ?_⟩
  · intro he
    rw [neg_eq_zero] at he
    exact hb0 he
  · intro he
    refine hnc ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
      ⟨-1, ?_⟩)
    have hb : b = -a := by
      rw [← he]
      simp
    rw [hb]
    simp [neg_one_smul, sub_zero]

/-- **(A)-rung C1 (pm7): off-plane azimuth translator** — a point strictly
off the `(a, b)` plane sits at an azimuth that is neither `0` nor `π`. -/
private theorem pmAzimOffPlaneNe_p35 {a b x : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b)
    (hx : ∀ s t : ℝ, x - 0 ≠ s • (a - 0) + t • (b - 0)) :
    azim 0 a b x ≠ 0 ∧ azim 0 a b x ≠ Real.pi := by
  have hcolx : ¬ Collinear3 0 a x := by
    intro hcol
    obtain ⟨lam, hlam⟩ := (collinear3_iff_smul (v := (0:V3)) (w := a)
      (w1 := x) ha0).mp hcol
    exact hx lam 0 (by rw [hlam]; simp)
  refine ⟨fun h0 => ?_, fun hpi => ?_⟩
  · obtain ⟨c₁, hc₁, d₁, hd₁⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := b) (y := x)
        (Ne.symm ha0) hb0 (fun he => hnc (by rw [he]; exact collinear3_pair_right rfl))).mp
        ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := a) (w := b) hnc hcolx).mp h0)
    exact hx d₁ c₁ (by rw [hd₁]; exact add_comm _ _)
  · have hnegb := pmNegCollA_p35 ha0 hnc
    obtain ⟨ha0', hb0', hba⟩ := pmNegBNe_p35 ha0 hb0 hnc
    have hπb : azim 0 a b (-b) = Real.pi :=
      pmAzimPlaneNeg_p35 ha0 hb0 hnc (x := -b) (s := 0) (t := -1)
        (by simp) (by norm_num)
    obtain ⟨c₁, hc₁, d₁, hd₁⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := -b) (y := x)
        ha0' hb0' hba).mp
        ((azim_eq_azim_iff (v0 := (0:V3)) (v1 := a) (w := b) (x := -b) (y := x)
          hnc hnegb hcolx).mp (by rw [hπb, hpi]))
    exact hx d₁ (-c₁) (by rw [hd₁]; module)

/-- **(A)-rung C2 (pm7): the standalone dart-cone ring kill** — a ring
vertex in the closed cone `affGe {0} {vv j, vv (j+1)}` must meet the dart
pair or their immediate cyclic neighbours, else the `fan7` cone
disjointness is violated. -/
private theorem pmConeRingKill_p35 {s : ScsV39} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hk4 : 4 ≤ s.k) (j i : ℕ)
    (hz : vv i ∈ affGe ({0} : Set V3) {vv j, vv (j + 1)})
    (h1 : vv i ≠ vv j) (h2 : vv i ≠ vv (j + 1))
    (h3 : vv (i + 1) ≠ vv j) (h4 : vv (i + 1) ≠ vv (j + 1)) : False := by
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hf7 := hfan'.2.2.2.2.2
  have hvne : ∀ m : ℕ, vv m ≠ (0:V3) := by
    intro m hm
    exact hfan'.2.2.2.1 (hm ▸ (Set.mem_range.mpr ⟨m, rfl⟩ : vv m ∈ Set.range vv))
  have hEj : ({vv j, vv (j + 1)} : Set V3) ∈ E := (dartEdgeMems_p35 hk3 hper hE j).1
  have hncdi : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hz2 : vv i ∈ affGe ({0} : Set V3) {vv i, vv (i + 1)} :=
    pmSelfCone_p35 (hvne i) (hvne (i + 1)) (fun he =>
      hncdi (by rw [he]; exact collinear3_pair_right rfl))
  have hEi : ({vv i, vv (i + 1)} : Set V3) ∈ E := (dartEdgeMems_p35 hk3 hper hE i).1
  have hempty : ({vv j, vv (j + 1)} ∩ {vv i, vv (i + 1)} : Set V3) = ∅ := by
    ext z'
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.notMem_empty, iff_false]
    intro hcon
    obtain ⟨hA, hB⟩ := hcon
    rcases hA with hA' | hA' <;> rcases hB with hB' | hB'
    · exact h1 (hB'.symm.trans hA')
    · exact h3 (hB'.symm.trans hA')
    · exact h2 (hB'.symm.trans hA')
    · exact h4 (hB'.symm.trans hA')
  have hz0 := hf7 {vv j, vv (j + 1)}
    (Set.mem_union_left {s | ∃ v ∈ Set.range vv, s = {v}} hEj) {vv i, vv (i + 1)}
    (Set.mem_union_left {s | ∃ v ∈ Set.range vv, s = {v}} hEi)
  rw [hempty] at hz0
  have hmem : vv i ∈ (affGe ({0} : Set V3) (∅ : Set V3)) := by
    rw [← hz0]
    exact Set.mem_inter hz hz2
  simp only [affGe, Affsign, Set.mem_setOf_eq] at hmem
  rw [Set.union_empty] at hmem
  obtain ⟨f, hf, hz, -, -⟩ := hmem
  have hto : hf.toFinset = {0} := Set.Finite.toFinset_singleton
  rw [hto] at hz
  simp at hz
  exact hvne i hz

/-- **(A)-rung C3 (pm7): the `π`-side rendering of the span vertex** — at
azimuth `π` the dart-`(j+k-1)` vertex sits in the dart-`j` plane with a
strictly negative second coordinate. -/
private theorem pmNegSideOfPi_p35 {a b d : V3} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hnc : ¬ Collinear3 0 a b) (hπ : azim 0 a b d = Real.pi) :
    ∃ γ β : ℝ, d - 0 = γ • (a - 0) + β • (b - 0) ∧ β < 0 := by
  have hnad : ¬ Collinear3 0 a d := by
    intro hcol
    rw [azimAxis_p35 hcol] at hπ
    have := Real.pi_pos
    linarith
  have hnegb := pmNegCollA_p35 ha0 hnc
  obtain ⟨ha0', hb0', hba⟩ := pmNegBNe_p35 ha0 hb0 hnc
  have hπb : azim 0 a b (-b) = Real.pi :=
    pmAzimPlaneNeg_p35 ha0 hb0 hnc (x := -b) (s := 0) (t := -1)
      (by simp) (by norm_num)
  obtain ⟨c₁, hc₁, d₁, hd₁⟩ :=
    (affGt_pair_iff (v0 := (0:V3)) (v1 := a) (x := -b) (y := d)
      ha0' hb0' hba).mp
      ((azim_eq_azim_iff (v0 := (0:V3)) (v1 := a) (w := b) (x := -b) (y := d)
        hnc hnegb hnad).mp (by rw [hπb, hπ]))
  refine ⟨d₁, -c₁, ?_, by linarith⟩
  rw [hd₁]
  module

/-- **(A)-rung C4 (pm7): the antipodal wedge** — an in-plane `e` at azimuth
`π` off the `b`-ray has both dart coordinates negative, and `a` sits at
azimuth `π` of the `(b, e)` frame. -/
private theorem pmB2AntiWedge_p35 {a b e : V3} {ce de : ℝ} (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (he0 : e ≠ 0) (hnc : ¬ Collinear3 0 a b)
    (hnce : ¬ Collinear3 0 b e)
    (hπe : azim 0 a b e = Real.pi)
    (heM : e - 0 = ce • (a - 0) + de • (b - 0))
    (hne : azim 0 b e a ≠ 0) :
    ce < 0 ∧ de < 0 ∧ azim 0 b e a = Real.pi := by
  have hde : de < 0 := by
    rcases lt_trichotomy de 0 with h | h0 | h
    · exact h
    · exfalso
      have h0' := pmAzimPlanePos_p35 ha0 hb0 hnc heM (le_of_eq h0.symm)
      rw [h0'] at hπe
      have := Real.pi_pos
      linarith
    · exfalso
      have h0' := pmAzimPlanePos_p35 ha0 hb0 hnc heM (le_of_lt h)
      rw [h0'] at hπe
      have := Real.pi_pos
      linarith
  have hce0 : ce ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at heM
    exact hnce ((collinear3_iff_smul (v := (0:V3)) (w := b) (w1 := e)
      hb0).mpr ⟨de, heM⟩)
  have hstep : ce • (a - 0) = (e - 0) - de • (b - 0) := by
    rw [heM, add_sub_cancel_right]
  have haM : a - 0 = (-(de / ce)) • (b - 0) + (1 / ce) • (e - 0) := by
    refine (smul_right_injective V3 hce0).eq_iff.mp ?_
    rw [hstep, smul_add, smul_smul, mul_neg, smul_smul]
    have hz0 : ce * (1 / ce) = 1 := by
      rw [one_div, mul_inv_cancel₀ hce0]
    have hz1 : ce * (de / ce) = de := by
      rw [mul_comm, div_mul_cancel₀ _ hce0]
    rw [hz1, hz0, one_smul, neg_smul, sub_eq_add_neg, add_comm]
  rcases lt_trichotomy ce 0 with hce | hce0' | hce
  · refine ⟨hce, hde, ?_⟩
    have hinv : (1:ℝ) / ce < 0 := by
      rw [one_div]
      exact inv_lt_zero.mpr hce
    exact pmAzimPlaneNeg_p35 hb0 he0 hnce haM hinv
  · exact absurd hce0' hce0
  · exfalso
    have hinv : (0:ℝ) < 1 / ce := by
      rw [one_div]
      exact inv_pos.mpr hce
    exact hne (pmAzimPlanePos_p35 hb0 he0 hnce haM (le_of_lt hinv))

/-- auxiliary (pm7): the contradiction engine once the Case-A successor is
known in-plane — every placement dies except the negative-`a`-coefficient
winding-order survivor. -/
private theorem pmEOffPlaneAux_p35 {s : ScsV39} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hk4 : 4 ≤ s.k) (j : ℕ)
    (hb0 : vv j ≠ (0:V3)) (hc0 : vv (j + 1) ≠ (0:V3))
    (he0 : vv (j + 1 + 1) ≠ (0:V3))
    (hbc : vv j ≠ vv (j + 1)) (hncbc : ¬ Collinear3 0 (vv j) (vv (j + 1)))
    (hv1 : vv (j + 1 + 1) ≠ vv j) (hv2 : vv (j + 1 + 1) ≠ vv (j + 1))
    (hv3 : vv (j + 2 + 1) ≠ vv j) (hv4 : vv (j + 2 + 1) ≠ vv (j + 1))
    (hθlt : azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) < Real.pi)
    (heM : ∃ c d : ℝ, vv (j + 1 + 1) - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0)) :
    ∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0) ∧
      ce < 0 := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hθne := dartSpanNeCyc_p35 hk3 hper hinj hE j hfan'
  obtain ⟨ce, de, heM'⟩ := heM
  rcases azimPlanePlace_p35 hb0 hc0 hncbc ⟨ce, de, heM'⟩ with h0e | hπe
  · -- azimuth 0: on-axis or off-axis half-plane
    by_cases hcolae : Collinear3 0 (vv j) (vv (j + 1 + 1))
    · obtain ⟨lam, hlam⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
        (w1 := vv (j + 1 + 1)) hb0).mp hcolae
      rcases lt_trichotomy lam 0 with hlam0 | hlam00 | hlam0p
      · exact ⟨lam, 0, by rw [hlam]; simp, hlam0⟩
      · exfalso
        simp only [hlam00, zero_smul, add_zero] at hlam
        exact he0 (by simpa using hlam)
      · exfalso
        refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
        exact pmConeMem_p35 hb0 hc0 hbc (le_of_lt hlam0p) (by norm_num)
          (show vv (j + 1 + 1) - 0 = lam • (vv j - 0) + (0:ℝ) • (vv (j + 1) - 0)
            from by rw [hlam]; simp)
    · obtain ⟨c₁, hc₁, d₁, hd₁⟩ :=
        (affGt_pair_iff (v0 := (0:V3)) (v1 := vv j) (x := vv (j + 1))
          (y := vv (j + 1 + 1)) (Ne.symm hb0) hc0
          (fun heq => hbc heq.symm)).mp
          ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := vv j)
            (w := vv (j + 1)) hncbc hcolae).mp h0e)
      rcases lt_trichotomy d₁ 0 with hd0 | hd00 | hd
      · exact ⟨d₁, c₁, by rw [hd₁]; exact add_comm _ _, hd0⟩
      · exfalso
        refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
        exact pmConeMem_p35 hb0 hc0 hbc (le_of_eq hd00.symm) (le_of_lt hc₁)
          (show vv (j + 1 + 1) - 0 = d₁ • (vv j - 0) + c₁ • (vv (j + 1) - 0)
            from by rw [hd₁]; exact add_comm _ _)
      · exfalso
        refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
        exact pmConeMem_p35 hb0 hc0 hbc (le_of_lt hd) (le_of_lt hc₁)
          (show vv (j + 1 + 1) - 0 = d₁ • (vv j - 0) + c₁ • (vv (j + 1) - 0)
            from by rw [hd₁]; exact add_comm _ _)
  · -- azimuth π: above the sector ceiling θ < π
    exfalso
    obtain ⟨hsand, -⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
    have hle := (hsand (vv (j + 1 + 1)) (Set.mem_range.mpr ⟨j + 2, rfl⟩)).2
    rw [hπe] at hle
    have := Real.pi_pos
    linarith

/-- **(A)-rung D1 (pm7): the Case-A fork** — with the sector span strictly
below `π`, the successor vertex `e := vv (j+2)` is either strictly off the
dart-`j` face plane (the Fork-2 input) or carries a negative `a`-coefficient
(the winding-order survivor). -/
private theorem pmEOffPlaneOfLtPi_p35 {s : ScsV39} {p q : ℕ} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (j : ℕ)
    (hθlt : azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) < Real.pi) :
    ¬ (∃ c d : ℝ, vv (j + 1 + 1) - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0)) ∨
      (∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0) ∧
        ce < 0) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hvne : ∀ m : ℕ, vv m ≠ (0:V3) := by
    intro m hm
    exact hfan'.2.2.2.1 (hm ▸ (Set.mem_range.mpr ⟨m, rfl⟩ : vv m ∈ Set.range vv))
  have hb0 : vv j ≠ (0:V3) := hvne j
  have hc0 : vv (j + 1) ≠ (0:V3) := hvne (j + 1)
  have he0 : vv (j + 1 + 1) ≠ (0:V3) := hvne (j + 1 + 1)
  have hncbc : ¬ Collinear3 0 (vv j) (vv (j + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j, rfl⟩)
  have hbc : vv j ≠ vv (j + 1) := by
    intro he
    exact hncbc (by rw [he]; exact collinear3_pair_right rfl)
  have hm22 : (j + 2) % s.k ≠ j % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j) (c := 2) (by omega) (by omega) hh
  have hm21 : (j + 2) % s.k ≠ (j + 1) % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j + 1) (c := 1) (by omega) (by omega) hh
  have hm30 : (j + 3) % s.k ≠ j % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j) (c := 3) (by omega) (by omega) hh
  have hm31 : (j + 3) % s.k ≠ (j + 1) % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j + 1) (c := 2) (by omega) (by omega) hh
  have hv1 : vv (j + 1 + 1) ≠ vv j := pmVvModNe_p35 hk0 hper hinj hm22
  have hv2 : vv (j + 1 + 1) ≠ vv (j + 1) := pmVvModNe_p35 hk0 hper hinj hm21
  have hv3 : vv (j + 2 + 1) ≠ vv j := pmVvModNe_p35 hk0 hper hinj hm30
  have hv4 : vv (j + 2 + 1) ≠ vv (j + 1) := pmVvModNe_p35 hk0 hper hinj hm31
  by_cases heM : ∃ c d : ℝ, vv (j + 1 + 1) - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0)
  · exact Or.inr (pmEOffPlaneAux_p35 hscs hBB hE hFF hk4 j hb0 hc0 he0 hbc hncbc
      hv1 hv2 hv3 hv4 hθlt heM)
  · exact Or.inl heM

/-- **(A)-rung D2 (pm7): the `θ = π` root reducer** — at a flat sector the
span vertex `d` renders on the negative `b`-side; and (i) if `e` is off the
plane both endpoints carry `α ≥ 0` (the half-plane data), while (ii) if `e`
is in the plane it either carries a negative `a`-coefficient (the
winding-order survivor) or sits in the antipodal wedge with the dart-`(j+1)`
sector flat. -/
private theorem pmBRootReduce_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (j : ℕ)
    (hu : ∃ c d : ℝ, u - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (hw : ∃ c d : ℝ, w - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (hθπ : azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) = Real.pi) :
    (∃ γ β : ℝ, vv (j + s.k - 1) - 0 = γ • (vv j - 0) + β • (vv (j + 1) - 0) ∧ β < 0) ∧
      ((¬ ∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0)) →
        (∀ cu du : ℝ, u - 0 = cu • (vv j - 0) + du • (vv (j + 1) - 0) → 0 ≤ cu) ∧
        (∀ cw dw : ℝ, w - 0 = cw • (vv j - 0) + dw • (vv (j + 1) - 0) → 0 ≤ cw)) ∧
      ((∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0)) →
        (∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0) ∧
            ce < 0) ∨
        ((∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0) ∧
            ce < 0 ∧ de < 0) ∧
          azim 0 (vv (j + 1)) (vv (j + 1 + 1)) (vv j) = Real.pi)) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hvne : ∀ m : ℕ, vv m ≠ (0:V3) := by
    intro m hm
    exact hfan'.2.2.2.1 (hm ▸ (Set.mem_range.mpr ⟨m, rfl⟩ : vv m ∈ Set.range vv))
  have hb0 : vv j ≠ (0:V3) := hvne j
  have hc0 : vv (j + 1) ≠ (0:V3) := hvne (j + 1)
  have he0 : vv (j + 1 + 1) ≠ (0:V3) := hvne (j + 1 + 1)
  have hncbc : ¬ Collinear3 0 (vv j) (vv (j + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j, rfl⟩)
  have hbc : vv j ≠ vv (j + 1) := by
    intro he
    exact hncbc (by rw [he]; exact collinear3_pair_right rfl)
  have hncbe : ¬ Collinear3 0 (vv (j + 1)) (vv (j + 1 + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j + 1, rfl⟩)
  have hm22 : (j + 2) % s.k ≠ j % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j) (c := 2) (by omega) (by omega) hh
  have hm21 : (j + 2) % s.k ≠ (j + 1) % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j + 1) (c := 1) (by omega) (by omega) hh
  have hm30 : (j + 3) % s.k ≠ j % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j) (c := 3) (by omega) (by omega) hh
  have hm31 : (j + 3) % s.k ≠ (j + 1) % s.k := fun hh =>
    pmModNeGen_p35 hk0 (x := j + 1) (c := 2) (by omega) (by omega) hh
  have hv1 : vv (j + 1 + 1) ≠ vv j := pmVvModNe_p35 hk0 hper hinj hm22
  have hv2 : vv (j + 1 + 1) ≠ vv (j + 1) := pmVvModNe_p35 hk0 hper hinj hm21
  have hv3 : vv (j + 2 + 1) ≠ vv j := pmVvModNe_p35 hk0 hper hinj hm30
  have hv4 : vv (j + 2 + 1) ≠ vv (j + 1) := pmVvModNe_p35 hk0 hper hinj hm31
  refine ⟨pmNegSideOfPi_p35 hb0 hc0 hncbc hθπ, ?_, ?_⟩
  · -- the B1 half-plane arm
    intro heP
    have hxe : ∀ s_ t : ℝ, vv (j + 1 + 1) - 0 ≠ s_ • (vv j - 0) +
        t • (vv (j + 1) - 0) := fun s_ t hst => heP ⟨s_, t, hst⟩
    obtain ⟨h0ne, hπne⟩ := pmAzimOffPlaneNe_p35 hb0 hc0 hncbc hxe
    have hcolae : ¬ Collinear3 0 (vv j) (vv (j + 1 + 1)) := by
      intro hcol
      obtain ⟨lam, hlam⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
        (w1 := vv (j + 1 + 1)) hb0).mp hcol
      exact heP ⟨lam, 0, by rw [hlam]; simp⟩
    obtain ⟨hsand, -⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
    have hle := (hsand (vv (j + 1 + 1)) (Set.mem_range.mpr ⟨j + 2, rfl⟩)).2
    have hlt : azim 0 (vv j) (vv (j + 1)) (vv (j + 1 + 1)) < Real.pi :=
      lt_of_le_of_ne (hle.trans_eq hθπ) hπne
    have h0lt : 0 < azim 0 (vv j) (vv (j + 1)) (vv (j + 1 + 1)) :=
      lt_of_le_of_ne (azim_nonneg 0 (vv j) (vv (j + 1)) (vv (j + 1 + 1)))
        (Ne.symm h0ne)
    have hbed : (0:ℝ) < (crossProduct ((vv j : V3) : Fin 3 → ℝ)
        ((vv (j + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (vv (j + 1 + 1) : Fin 3 → ℝ) := by
      simpa [sub_zero] using cross_dot_fully_surrounded_fan (x := 0)
        (v1 := vv j) (v := vv (j + 1)) (u1 := vv (j + 1 + 1)) hcolae hncbc h0lt hlt
    refine ⟨fun cu du hcu => pmAlphaGe_p35
      (pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + 1) u
        (Set.mem_range.mpr ⟨p % s.k, hp⟩)) hcu hbed,
      fun cw dw hcw => pmAlphaGe_p35
      (pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + 1) w
        (Set.mem_range.mpr ⟨q % s.k, hq⟩)) hcw hbed⟩
  · -- the B2 antipodal-wedge arm
    intro h
    obtain ⟨ce, de, heM⟩ := h
    rcases azimPlanePlace_p35 hb0 hc0 hncbc ⟨ce, de, heM⟩ with h0e | hπe
    · -- azimuth 0: negative `a`-coefficient or the cone kill
      by_cases hcolae : Collinear3 0 (vv j) (vv (j + 1 + 1))
      · obtain ⟨lam, hlam⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
          (w1 := vv (j + 1 + 1)) hb0).mp hcolae
        rcases lt_trichotomy lam 0 with hlam0 | hlam00 | hlam0p
        · exact Or.inl ⟨lam, 0, by rw [hlam]; simp, hlam0⟩
        · exfalso
          simp only [hlam00, zero_smul, add_zero] at hlam
          exact he0 (by simpa using hlam)
        · exfalso
          refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
          exact pmConeMem_p35 hb0 hc0 hbc (le_of_lt hlam0p) (by norm_num)
            (show vv (j + 1 + 1) - 0 = lam • (vv j - 0) + (0:ℝ) • (vv (j + 1) - 0)
              from by rw [hlam]; simp)
      · obtain ⟨c₁, hc₁, d₁, hd₁⟩ :=
          (affGt_pair_iff (v0 := (0:V3)) (v1 := vv j) (x := vv (j + 1))
            (y := vv (j + 1 + 1)) (Ne.symm hb0) hc0
            (fun heq => hbc heq.symm)).mp
            ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := vv j)
              (w := vv (j + 1)) hncbc hcolae).mp h0e)
        rcases lt_trichotomy d₁ 0 with hd0 | hd00 | hd
        · exact Or.inl ⟨d₁, c₁, by rw [hd₁]; exact add_comm _ _, hd0⟩
        · exfalso
          refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
          exact pmConeMem_p35 hb0 hc0 hbc (le_of_eq hd00.symm) (le_of_lt hc₁)
            (show vv (j + 1 + 1) - 0 = d₁ • (vv j - 0) + c₁ • (vv (j + 1) - 0)
              from by rw [hd₁]; exact add_comm _ _)
        · exfalso
          refine pmConeRingKill_p35 hscs hBB hE hFF hk4 j (j + 2) ?_ hv1 hv2 hv3 hv4
          exact pmConeMem_p35 hb0 hc0 hbc (le_of_lt hd) (le_of_lt hc₁)
            (show vv (j + 1 + 1) - 0 = d₁ • (vv j - 0) + c₁ • (vv (j + 1) - 0)
              from by rw [hd₁]; exact add_comm _ _)
    · -- azimuth π: the antipodal wedge + flat dart-(j+1) sector
      have hne := dartSpanNeCyc_p35 hk3 hper hinj hE (j + 1) hfan'
      rw [show (j + 1) + s.k - 1 = j + s.k from by omega,
        wedgeVvAddK_p35 hper j] at hne
      obtain ⟨hce, hde, hθ1⟩ := pmB2AntiWedge_p35 hb0 hc0 he0 hncbc hncbe hπe
        heM hne
      exact Or.inr ⟨⟨ce, de, heM, ⟨hce, hde⟩⟩, hθ1⟩

/-! ## planemiss8 rungs (lkgrqui-planemiss8-w3, 2026-10-28)

The winding-order residual root kit (all conditional, zero sorry): with the
R-tilt / R-flat survivor data in hand these rungs globalize the dart
half-space to the whole ring (every ring vertex on the closed `(a×b)`-side
of the dart-`j` face plane), flatten the successor sector (`θ_{j+1} = π`),
and detect the capped-vertex quadrant (an in-plane ring vertex whose capped
neighbor is strictly above the face plane sits in a forced `(α, β)`-quadrant
— the pm7 DELIVERY sign algebra `det(x, x⁺, ·)`).  Insertion point: after
`pmBRootReduce_p35`, before `pmPlaneCrowding_p35`. -/

/-- (pm8) Cross-dot vanishing against the first cross slot. -/
private theorem pmCrossDotSelfL_p35 (p q : Fin 3 → ℝ) :
    (crossProduct p q) ⬝ᵥ p = 0 := by
  rw [dotProduct_comm]
  exact dot_self_cross p q

/-- (pm8) Cross-dot vanishing against the second cross slot. -/
private theorem pmCrossDotSelfR_p35 (p q : Fin 3 → ℝ) :
    (crossProduct p q) ⬝ᵥ q = 0 := by
  rw [dotProduct_comm]
  exact dot_cross_self p q

/-- (pm8) Scalar triple product, slot swap (`r` and `q` exchanged). -/
private theorem pmDotCrossSwap_p35 (p q r : Fin 3 → ℝ) :
    (crossProduct p q) ⬝ᵥ r = -((crossProduct p r) ⬝ᵥ q) := by
  have h1 : (crossProduct p q) ⬝ᵥ r = (crossProduct q r) ⬝ᵥ p := pmDetCyc_p35 p q r
  have h2 : (crossProduct q r) ⬝ᵥ p
      = (-crossProduct r q) ⬝ᵥ p := by rw [cross_anticomm r q]
  have h3 : (-crossProduct r q) ⬝ᵥ p
      = -((crossProduct r q) ⬝ᵥ p) := pmDotNegL_p35 _ _
  have h4 : (crossProduct r q) ⬝ᵥ p = (crossProduct p r) ⬝ᵥ q :=
    (pmDetCyc_p35 p r q).symm
  rw [h1, h2, h3, h4]

/-- (pm8) Cross of the rendered successor against the dart pair: with `e`
rendered on the dart face as `ce•a + de•b`, `cross(b, e) = -ce • cross(a, b)`. -/
private theorem pmCrossSuccNeg_p35 {a b e : V3} {ce de : ℝ}
    (heM : e - 0 = ce • (a - 0) + de • (b - 0)) :
    (crossProduct (b : Fin 3 → ℝ) (e : Fin 3 → ℝ))
      = -ce • (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) := by
  simp only [sub_zero] at heM
  have hecoe : (e : Fin 3 → ℝ) = ce • (a : Fin 3 → ℝ) + de • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) heM
  have hbb : crossProduct (b : Fin 3 → ℝ) (b : Fin 3 → ℝ) = 0 := cross_self _
  have hba : crossProduct (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)
      = -(crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) :=
    (cross_anticomm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)).symm
  rw [hecoe, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35, hba, hbb]
  module

/-- (pm8) Cross of a rendered plane vector against the `a`-ray: with `x`
rendered as `γ•a + β•b`, `cross(x, a) = -β • cross(a, b)`. -/
private theorem pmCrossPredNeg_p35 {a b x : V3} {γ β : ℝ}
    (hxM : x - 0 = γ • (a - 0) + β • (b - 0)) :
    (crossProduct (x : Fin 3 → ℝ) (a : Fin 3 → ℝ))
      = -β • (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) := by
  simp only [sub_zero] at hxM
  have hxcoe : (x : Fin 3 → ℝ) = γ • (a : Fin 3 → ℝ) + β • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hxM
  have haa : crossProduct (a : Fin 3 → ℝ) (a : Fin 3 → ℝ) = 0 := cross_self _
  have hba : crossProduct (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)
      = -(crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) :=
    (cross_anticomm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)).symm
  rw [hxcoe, pmCrossAddL_p35, pmCrossSmulL_p35, pmCrossSmulL_p35, haa, hba]
  module

/-- **(pm8) R-tilt half-space globalizer**: whenever the successor vertex
`vv (j+2)` sits in the dart-`j` face plane with a strictly negative
`a`-coefficient (the winding-order survivor of `pmEOffPlaneOfLtPi_p35`, and
likewise the `pmBRootReduce_p35` in-plane survivor/antipodal leaves), the
dart-`(j+1)` half-space globalizes: every ring vertex lies on the closed
`(a×b)`-side of the dart-`j` face plane. -/
private theorem pmTiltUpperHalf_p35 {s : ScsV39} {p q : ℕ} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (j : ℕ)
    (hsurv : ∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) + de • (vv (j + 1) - 0) ∧
      ce < 0)
    (y : V3) (hy : y ∈ Set.range vv) :
    (0:ℝ) ≤ (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  obtain ⟨ce, de, heM, hce⟩ := hsurv
  have h1 := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + 1) y hy
  rw [pmCrossSuccNeg_p35 heM, pmDotSmulL_p35] at h1
  have hpos : (0:ℝ) < -ce := neg_pos.mpr hce
  by_contra hneg
  exact absurd (mul_neg_of_pos_of_neg hpos (lt_of_not_ge hneg)) (not_lt.mpr h1)

/-- **(pm8) R-flat(a) half-space globalizer**: whenever the span vertex
`d := vv (j+k-1)` sits in the dart-`j` face plane on the negative `b`-side
(the `pmBRootReduce_p35` flat-sector data), the dart-`(j+k-1)` half-space
globalizes: every ring vertex lies on the closed `(a×b)`-side of the face
plane. -/
private theorem pmFlatAUpperHalf_p35 {s : ScsV39} {p q : ℕ} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (j : ℕ)
    (hdsurv : ∃ γ β : ℝ, vv (j + s.k - 1) - 0 = γ • (vv j - 0) + β • (vv (j + 1) - 0) ∧
      β < 0)
    (y : V3) (hy : y ∈ Set.range vv) :
    (0:ℝ) ≤ (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ) := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  obtain ⟨γ, β, hdM, hβ⟩ := hdsurv
  have h1 := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (j + s.k - 1) y hy
  have hvk : vv ((j + s.k - 1) + 1) = vv j := by
    rw [show (j + s.k - 1) + 1 = j + s.k from by omega]
    exact wedgeVvAddK_p35 hBB.2.1 j
  rw [hvk, pmCrossPredNeg_p35 hdM, pmDotSmulL_p35] at h1
  have hpos : (0:ℝ) < -β := neg_pos.mpr hβ
  by_contra hneg
  exact absurd (mul_neg_of_pos_of_neg hpos (lt_of_not_ge hneg)) (not_lt.mpr h1)

/-- (pm8) Quadrant detector against a capped successor: an in-plane vector
`x = α•a + β•b` whose successor `x'` is strictly on the `(a×b)`-side of the
face plane and avoids the dart-`x` half-space sign on `a` and `b` is forced
into the quadrant `α ≤ 0 ∧ 0 ≤ β` (the `det(x, x⁺, ·)` sign algebra). -/
private theorem pmQuadSucc_p35 {a b x x' : V3} {α β : ℝ}
    (hxM : x - 0 = α • (a - 0) + β • (b - 0))
    (hA : (0:ℝ) ≤ (crossProduct (x : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ))
    (hB : (0:ℝ) ≤ (crossProduct (x : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ))
    (hD : (0:ℝ) < (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ)) :
    α ≤ 0 ∧ 0 ≤ β := by
  simp only [sub_zero] at hxM
  have hxcoe : (x : Fin 3 → ℝ) = α • (a : Fin 3 → ℝ) + β • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hxM
  have hexp : (crossProduct (x : Fin 3 → ℝ) (x' : Fin 3 → ℝ))
      = α • (crossProduct (a : Fin 3 → ℝ) (x' : Fin 3 → ℝ))
        + β • (crossProduct (b : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) := by
    rw [hxcoe, pmCrossAddL_p35, pmCrossSmulL_p35, pmCrossSmulL_p35]
  have hcha : (crossProduct (b : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ)
      = (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ) := by
    have h1 : (crossProduct (b : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ)
        = (crossProduct (x' : Fin 3 → ℝ) (a : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ) :=
      pmDetCyc_p35 _ _ _
    rw [h1, pmDetCyc_p35]
  have hchb : (crossProduct (a : Fin 3 → ℝ) (x' : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
      = -((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ)) :=
    pmDotCrossSwap_p35 _ _ _
  rw [hexp, pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmCrossDotSelfL_p35,
    mul_zero, zero_add, hcha] at hA
  rw [hexp, pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmCrossDotSelfL_p35,
    hchb, mul_zero, add_zero] at hB
  refine ⟨?_, ?_⟩
  · by_contra hα
    exact absurd (mul_neg_of_pos_of_neg (lt_of_not_ge hα) (neg_lt_zero.mpr hD))
      (not_lt.mpr hB)
  · by_contra hβ
    exact absurd (mul_neg_of_neg_of_pos (lt_of_not_ge hβ) hD) (not_lt.mpr hA)

/-- (pm8) Quadrant detector against a capped predecessor: an in-plane vector
`x = α•a + β•b` whose predecessor `x'` is strictly on the `(a×b)`-side of
the face plane is forced into the quadrant `0 ≤ α ∧ β ≤ 0`. -/
private theorem pmQuadPred_p35 {a b x x' : V3} {α β : ℝ}
    (hxM : x - 0 = α • (a - 0) + β • (b - 0))
    (hA : (0:ℝ) ≤ (crossProduct (x' : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ))
    (hB : (0:ℝ) ≤ (crossProduct (x' : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ))
    (hD : (0:ℝ) < (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ)) :
    0 ≤ α ∧ β ≤ 0 := by
  simp only [sub_zero] at hxM
  have hxcoe : (x : Fin 3 → ℝ) = α • (a : Fin 3 → ℝ) + β • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hxM
  have hexp : (crossProduct (x' : Fin 3 → ℝ) (x : Fin 3 → ℝ))
      = α • (crossProduct (x' : Fin 3 → ℝ) (a : Fin 3 → ℝ))
        + β • (crossProduct (x' : Fin 3 → ℝ) (b : Fin 3 → ℝ)) := by
    rw [hxcoe, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35]
  have hcha : (crossProduct (x' : Fin 3 → ℝ) (a : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)
      = (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ) :=
    pmDetCyc_p35 _ _ _
  have hchb : (crossProduct (x' : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ)
      = -((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (x' : Fin 3 → ℝ)) := by
    have h1 : (crossProduct (x' : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (a : Fin 3 → ℝ)
        = -((crossProduct (x' : Fin 3 → ℝ) (a : Fin 3 → ℝ)) ⬝ᵥ (b : Fin 3 → ℝ)) :=
      pmDotCrossSwap_p35 _ _ _
    rw [h1, hcha]
  rw [hexp, pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmCrossDotSelfR_p35,
    mul_zero, zero_add, hchb] at hA
  rw [hexp, pmDotAddL_p35, pmDotSmulL_p35, pmDotSmulL_p35, pmCrossDotSelfR_p35,
    mul_zero, add_zero, hcha] at hB
  refine ⟨?_, ?_⟩
  · by_contra hα
    exact absurd (mul_neg_of_neg_of_pos (lt_of_not_ge hα) hD) (not_lt.mpr hB)
  · by_contra hβ
    exact absurd (mul_neg_of_pos_of_neg (lt_of_not_ge hβ) (neg_lt_zero.mpr hD))
      (not_lt.mpr hA)

/-- **(pm8) Cap quadrant at the ring, successor form**: with the ring
globalized to the closed `(a×b)`-side of the dart-`j` face plane, any ring
vertex `vv m` rendered in the face plane whose successor `vv (m+1)` lies
strictly off the plane is forced into the quadrant `α ≤ 0 ∧ 0 ≤ β`. -/
private theorem pmCapQuadSucc_p35 {s : ScsV39} {p q : ℕ} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (j m : ℕ)
    (hup : ∀ y ∈ Set.range vv, (0:ℝ) ≤ (crossProduct (vv j : Fin 3 → ℝ)
      (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ))
    (hxM : ∃ α β : ℝ, vv m - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0))
    (hxp : ¬ ∃ α β : ℝ, vv (m + 1) - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0)) :
    ∃ α β : ℝ, vv m - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0) ∧ α ≤ 0 ∧ 0 ≤ β := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hvne : ∀ i : ℕ, vv i ≠ (0:V3) := by
    intro i hi
    exact hfan'.2.2.2.1 (hi ▸ (Set.mem_range.mpr ⟨i, rfl⟩ : vv i ∈ Set.range vv))
  have hncab : ¬ Collinear3 0 (vv j) (vv (j + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j, rfl⟩)
  have hncx : ¬ Collinear3 0 (vv j) (vv (m + 1)) := by
    intro hcol
    obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
      (w1 := vv (m + 1)) (hvne j)).mp hcol
    exact hxp ⟨t, 0, by rw [ht]; simp⟩
  have hx'off := pmAzimOffPlaneNe_p35 (a := vv j) (b := vv (j + 1)) (x := vv (m + 1))
    (hvne j) (hvne (j + 1)) hncab (fun s_ t_ hst => hxp ⟨s_, t_, hst⟩)
  obtain ⟨hsand, hθle⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
  obtain ⟨h0le, hleθ⟩ := hsand (vv (m + 1)) (Set.mem_range.mpr ⟨m + 1, rfl⟩)
  have h0lt : 0 < azim 0 (vv j) (vv (j + 1)) (vv (m + 1)) :=
    lt_of_le_of_ne h0le (Ne.symm hx'off.1)
  have hleπ : azim 0 (vv j) (vv (j + 1)) (vv (m + 1)) ≤ Real.pi := hleθ.trans hθle
  have hltπ : azim 0 (vv j) (vv (j + 1)) (vv (m + 1)) < Real.pi :=
    lt_of_le_of_ne hleπ hx'off.2
  have hD : (0:ℝ) < (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
      (vv (m + 1) : Fin 3 → ℝ) := by
    simpa [sub_zero] using cross_dot_fully_surrounded_fan (x := 0) (v1 := vv j)
      (v := vv (j + 1)) (u1 := vv (m + 1)) hncx hncab h0lt hltπ
  have hA := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan m (vv j)
    (Set.mem_range.mpr ⟨j, rfl⟩)
  have hB := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan m (vv (j + 1))
    (Set.mem_range.mpr ⟨j + 1, rfl⟩)
  obtain ⟨α, β, hxM'⟩ := hxM
  exact ⟨α, β, hxM', pmQuadSucc_p35 hxM' hA hB hD⟩

/-- **(pm8) Cap quadrant at the ring, predecessor form**: with the ring
globalized to the closed `(a×b)`-side of the dart-`j` face plane, any ring
vertex `vv m` rendered in the face plane whose cyclic predecessor
`vv (m+k-1)` lies strictly off the plane is forced into the quadrant
`0 ≤ α ∧ β ≤ 0`. -/
private theorem pmCapQuadPred_p35 {s : ScsV39} {p q : ℕ} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (j m : ℕ)
    (hup : ∀ y ∈ Set.range vv, (0:ℝ) ≤ (crossProduct (vv j : Fin 3 → ℝ)
      (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ (y : Fin 3 → ℝ))
    (hxM : ∃ α β : ℝ, vv m - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0))
    (hxp : ¬ ∃ α β : ℝ, vv (m + s.k - 1) - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0)) :
    ∃ α β : ℝ, vv m - 0 = α • (vv j - 0) + β • (vv (j + 1) - 0) ∧ 0 ≤ α ∧ β ≤ 0 := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  have hvne : ∀ i : ℕ, vv i ≠ (0:V3) := by
    intro i hi
    exact hfan'.2.2.2.1 (hi ▸ (Set.mem_range.mpr ⟨i, rfl⟩ : vv i ∈ Set.range vv))
  have hncab : ¬ Collinear3 0 (vv j) (vv (j + 1)) :=
    Kepler.Text.Fan.fan_not_collinear hfan'
      (by rw [← hE]; exact Set.mem_range.mpr ⟨j, rfl⟩)
  have hncx : ¬ Collinear3 0 (vv j) (vv (m + s.k - 1)) := by
    intro hcol
    obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := (0:V3)) (w := vv j)
      (w1 := vv (m + s.k - 1)) (hvne j)).mp hcol
    exact hxp ⟨t, 0, by rw [ht]; simp⟩
  have hx'off := pmAzimOffPlaneNe_p35 (a := vv j) (b := vv (j + 1))
    (x := vv (m + s.k - 1)) (hvne j) (hvne (j + 1)) hncab
    (fun s_ t_ hst => hxp ⟨s_, t_, hst⟩)
  obtain ⟨hsand, hθle⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
  obtain ⟨h0le, hleθ⟩ := hsand (vv (m + s.k - 1))
    (Set.mem_range.mpr ⟨m + s.k - 1, rfl⟩)
  have h0lt : 0 < azim 0 (vv j) (vv (j + 1)) (vv (m + s.k - 1)) :=
    lt_of_le_of_ne h0le (Ne.symm hx'off.1)
  have hleπ : azim 0 (vv j) (vv (j + 1)) (vv (m + s.k - 1)) ≤ Real.pi :=
    hleθ.trans hθle
  have hltπ : azim 0 (vv j) (vv (j + 1)) (vv (m + s.k - 1)) < Real.pi :=
    lt_of_le_of_ne hleπ hx'off.2
  have hD : (0:ℝ) < (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
      (vv (m + s.k - 1) : Fin 3 → ℝ) := by
    simpa [sub_zero] using cross_dot_fully_surrounded_fan (x := 0) (v1 := vv j)
      (v := vv (j + 1)) (u1 := vv (m + s.k - 1)) hncx hncab h0lt hltπ
  have hvk : vv ((m + s.k - 1) + 1) = vv m := by
    rw [show (m + s.k - 1) + 1 = m + s.k from by omega]
    exact wedgeVvAddK_p35 hper m
  have hA := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (m + s.k - 1) (vv j)
    (Set.mem_range.mpr ⟨j, rfl⟩)
  have hB := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (m + s.k - 1) (vv (j + 1))
    (Set.mem_range.mpr ⟨j + 1, rfl⟩)
  rw [hvk] at hA hB
  obtain ⟨α, β, hxM'⟩ := hxM
  exact ⟨α, β, hxM', pmQuadPred_p35 hxM' hA hB hD⟩

/-- **(pm8) Successor-sector flattening**: with the successor `e` rendered in
the dart-`j` face plane at a strictly negative `a`-coefficient, the dart
`(j+1)` sector span is exactly `π` (`a` sits on the negative-`e` side of the
`b`-axis: `a = (-de/ce)•b + ce⁻¹•e` with `ce⁻¹ < 0`). -/
private theorem pmFlatSuccPi_p35 {a b e : V3} {ce de : ℝ} (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hncab : ¬ Collinear3 0 a b)
    (heM : e - 0 = ce • (a - 0) + de • (b - 0)) (hce : ce < 0) :
    azim 0 b e a = Real.pi := by
  have he0 : e ≠ (0:V3) := by
    intro hzz
    have hzero : ce • (a - 0) + de • (b - 0) = (0:V3) := by
      rw [← heM, hzz]
      simp
    have hcz := (pmPlaneCoordZero_p35 ha0 hncab hzero).1
    linarith
  have hnce : ¬ Collinear3 0 b e := by
    intro hcol
    obtain ⟨t, ht⟩ := (collinear3_iff_smul (v := (0:V3)) (w := b) (w1 := e) hb0).mp hcol
    have hcoord : ce • (a - 0) + de • (b - 0) = (0:ℝ) • (a - 0) + t • (b - 0) := by
      rw [← heM, ht, zero_smul, zero_add]
    have hcz := (pmPlaneCoordUnique_p35 ha0 hncab hcoord).1
    linarith
  have hcoe : a - 0 = (-de * ce⁻¹) • (b - 0) + ce⁻¹ • (e - 0) := by
    rw [heM, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_lt hce),
      one_smul]
    module
  exact pmAzimPlaneNeg_p35 (a := b) (b := e) (x := a) hb0 he0 hnce hcoe
    (inv_lt_zero.mpr hce)

/-! ## planemiss9 rungs (lkgrqui-planemiss9-w3, 2026-10-28)

The normal-axis azimuth engine: with `axN a b := (WithLp.toLp 2
(crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ)) : V3)` the
plane-missing endgame reads in-plane polar angles as `azim 0 (axN a b) a x`
(the azimuth around the dart-face normal axis, measured from the `a`
half-plane) — the FAN-free chain engine `triAzimAdd_p35` + `azim_compl`
applies verbatim.  Insertion point: after `pmFlatSuccPi_p35`, before the
`pmPlaneCrowding_p35` docstring. -/

/-- (pm9) Collinearity is symmetric in the last two arguments. -/
private theorem pmCollSwap_p35 {a b : V3} (h : Collinear3 0 a b) : Collinear3 0 b a := by
  have hset : ({0, a, b} : Set V3) = {0, b, a} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  show Collinear ℝ ({0, b, a} : Set V3)
  rw [← hset]
  exact h

/-- (pm9) The `V3` dot is the Pi-side dot after the coercion. -/
private theorem pmCoeDot_p35 (u v : V3) :
    (u ⬝ᵥ v) = ((u : Fin 3 → ℝ) ⬝ᵥ (v : Fin 3 → ℝ)) := rfl

/-- (pm9) Zero-equality transport through the coercion. -/
private theorem pmOfLpEqZero_p35 {u : V3} (h : ((u : Fin 3 → ℝ)) = 0) :
    u = (0:V3) := by
  have h2 : ‖u‖ ^ 2 = 0 := by
    rw [pmNormSqDot_p35, h, zero_dotProduct]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)

/-- (pm9) Coercion translation for the normal axis (the type-gap piece):
the coerced cross product reads back as the Pi-side cross product. -/
private theorem pmNormalAxisCoe_p35 {a b : V3} :
    ((WithLp.toLp 2 (crossProduct ((a : V3) : Fin 3 → ℝ)
        ((b : V3) : Fin 3 → ℝ)) : V3) : Fin 3 → ℝ)
      = crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ) :=
  WithLp.ofLp_toLp 2 _

/-- (pm9) The normal axis is nonzero whenever the dart pair spans a plane. -/
private theorem pmNormalAxisNe_p35 {a b : V3} (ha0 : a ≠ (0:V3))
    (hncab : ¬ Collinear3 0 a b) :
    (WithLp.toLp 2 (crossProduct ((a : V3) : Fin 3 → ℝ)
        ((b : V3) : Fin 3 → ℝ)) : V3) ≠ (0:V3) := by
  intro hz
  have hb0 : b ≠ (0:V3) := by
    intro hbz
    exact hncab (collinear3_pair_left hbz)
  have hli : LinearIndependent ℝ (![((a : V3) : Fin 3 → ℝ),
      ((b : V3) : Fin 3 → ℝ)] : Fin 2 → (Fin 3 → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · by_contra hg0
      have hsum : (∑ j : Fin 2, g j • (![((a : V3) : Fin 3 → ℝ),
          ((b : V3) : Fin 3 → ℝ)] : Fin 2 → (Fin 3 → ℝ)) j)
          = g 0 • ((a : V3) : Fin 3 → ℝ) + g 1 • ((b : V3) : Fin 3 → ℝ) := by
        simp [Fin.sum_univ_two]
      rw [hsum] at hg
      by_cases hg1 : g 1 = 0
      · rw [hg1, zero_smul, add_zero] at hg
        exact ha0 (pmOfLpEqZero_p35 ((smul_eq_zero.mp hg).resolve_left hg0))
      · refine hncab
          ((collinear3_iff_smul (v := (0:V3)) (w := a) (w1 := b) ha0).mpr
            ⟨-g 0 / g 1, ?_⟩)
        have h1 : g 0 • ((a : V3) : Fin 3 → ℝ) + g 1 • ((b : V3) : Fin 3 → ℝ)
            = 0 := hg
        have h2 : ((b : V3) : Fin 3 → ℝ)
            = (-g 0 / g 1) • ((a : V3) : Fin 3 → ℝ) := by
          have h1' : g 1 • (((b : V3) : Fin 3 → ℝ)
              - (-g 0 / g 1) • ((a : V3) : Fin 3 → ℝ)) = 0 := by
            rw [smul_sub, show g 1 • ((b : V3) : Fin 3 → ℝ)
                = (-g 0) • ((a : V3) : Fin 3 → ℝ) from by
                rw [neg_smul]; exact eq_neg_of_add_eq_zero_right h1,
              show g 1 • ((-g 0 / g 1) • ((a : V3) : Fin 3 → ℝ))
                  = (-g 0) • ((a : V3) : Fin 3 → ℝ) from by
                rw [smul_smul]; field_simp]
            module
          exact sub_eq_zero.mp ((smul_eq_zero.mp h1').resolve_left hg1)
        have h3 := congrArg (WithLp.toLp 2) h2
        rw [WithLp.toLp_smul, WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h3
        rw [sub_zero b, sub_zero a]
        exact h3
    · by_contra hg1
      have hsum : (∑ j : Fin 2, g j • (![((a : V3) : Fin 3 → ℝ),
          ((b : V3) : Fin 3 → ℝ)] : Fin 2 → (Fin 3 → ℝ)) j)
          = g 0 • ((a : V3) : Fin 3 → ℝ) + g 1 • ((b : V3) : Fin 3 → ℝ) := by
        simp [Fin.sum_univ_two]
      rw [hsum] at hg
      by_cases hg0 : g 0 = 0
      · rw [hg0, zero_smul, zero_add] at hg
        exact hg1 ((smul_eq_zero.mp hg).resolve_right
          (fun hc => hb0 (pmOfLpEqZero_p35 hc)))
      · refine hncab (pmCollSwap_p35
          ((collinear3_iff_smul (v := (0:V3)) (w := b) (w1 := a) hb0).mpr
            ⟨-g 1 / g 0, ?_⟩))
        have h1 : g 0 • ((a : V3) : Fin 3 → ℝ) + g 1 • ((b : V3) : Fin 3 → ℝ)
            = 0 := hg
        have h2 : ((a : V3) : Fin 3 → ℝ)
            = (-g 1 / g 0) • ((b : V3) : Fin 3 → ℝ) := by
          have h1' : g 0 • (((a : V3) : Fin 3 → ℝ)
              - (-g 1 / g 0) • ((b : V3) : Fin 3 → ℝ)) = 0 := by
            rw [smul_sub, show g 0 • ((a : V3) : Fin 3 → ℝ)
                = (-g 1) • ((b : V3) : Fin 3 → ℝ) from by
                rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h1,
              show g 0 • ((-g 1 / g 0) • ((b : V3) : Fin 3 → ℝ))
                  = (-g 1) • ((b : V3) : Fin 3 → ℝ) from by
                rw [smul_smul]; field_simp]
            module
          exact sub_eq_zero.mp ((smul_eq_zero.mp h1').resolve_left hg0)
        have h3 := congrArg (WithLp.toLp 2) h2
        rw [WithLp.toLp_smul, WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h3
        rw [sub_zero a, sub_zero b]
        exact h3
  have hz0 : (crossProduct ((a : V3) : Fin 3 → ℝ)
      ((b : V3) : Fin 3 → ℝ)) = 0 := by
    have he := pmNormalAxisCoe_p35 (a := a) (b := b)
    rw [hz] at he
    exact he.symm.trans rfl
  exact ((crossProduct_ne_zero_iff_linearIndependent).mpr hli) hz0

/-- (pm9) Orthogonality non-collinearity: a nonzero vector orthogonal to a
nonzero axis is never collinear with it. -/
private theorem pmAxisOrthoNC_p35 {ax y : V3} (hax0 : ax ≠ (0:V3)) (hy0 : y ≠ (0:V3))
    (hdot : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) : ¬ Collinear3 0 ax y := by
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := ax) (w1 := y)
    hax0).mp hcol
  have hcoe : ((y : Fin 3 → ℝ)) = c • ((ax : Fin 3 → ℝ)) := by
    simpa [sub_zero] using congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hc
  have hc0 : c ≠ 0 := by
    intro hcz
    rw [hcz, zero_smul] at hcoe
    exact hy0 (pmOfLpEqZero_p35 hcoe)
  have h2 : ((y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ))
      = c * ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) := by
    rw [hcoe, pmDotSmulL_p35]
  rw [hdot] at h2
  have haxsq : ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) = 0 := by
    rcases mul_eq_zero.mp h2.symm with hc2 | hax2
    · exact absurd hc2 hc0
    · exact hax2
  exact hax0 (norm_eq_zero.mp
    (sq_eq_zero_iff.mp (by rw [pmNormSqDot_p35]; exact haxsq)))

/-- (pm9) Azimuth-zero rendering against the normal axis: `azim 0 ax a x = 0`
puts the target on the open reference ray plus axis slack
(`x = e•ax + c•a` with `c > 0`). -/
private theorem pmAzimNormalRender0_p35 {ax a x : V3} (ha0 : a ≠ (0:V3))
    (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (h : azim 0 ax a x = 0) :
    ∃ e c : ℝ, 0 < c ∧ x - 0 = e • (ax - 0) + c • (a - 0) := by
  obtain ⟨c, hc, e, he⟩ :=
    (affGt_pair_iff (v0 := (0:V3)) (v1 := ax) (x := a) (y := x)
      (fun hz => hnc (by rw [hz]; exact collinear3_of_eq rfl))
      ha0 (fun hz => hnc (by rw [hz]; exact collinear3_pair_right rfl))).mp
    ((azim_eq_zero_iff_alt (v0 := (0:V3)) (v1 := ax) (w := a) (x := x) hnc hncx).mp h)
  exact ⟨e, c, hc, by rw [he]; exact add_comm _ _⟩

/-- (pm9) **Orthogonal-frame cosine identity**: for two nonzero vectors in
the plane orthogonal to the axis, the cosine of their azimuth equals the
scaled dot product. -/
private theorem pmAzimOrthoCos_p35 {ax a x : V3} (hax0 : ax ≠ (0:V3))
    (ha0 : a ≠ (0:V3)) (hx0 : x ≠ (0:V3))
    (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (hAA : (a : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    Real.cos (azim 0 ax a x) * (‖a‖ * ‖x‖) = (a : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul ax hax0
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ :=
    azim_frame_spec (v := (0:V3)) (w := ax) (w1 := a) (w2 := x) hnc hncx hon
      (by simp only [dist_eq_norm, sub_zero]; exact halign) hax0
  set θ : ℝ := azim 0 ax a x with hθdef
  have hA1 : ((a : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) = r1 * Real.cos ψ := by
    have h := congrArg Complex.re hz1
    simpa [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
      Complex.exp_im, Real.exp_zero] using h
  have hA2 : ((a : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = r1 * Real.sin ψ := by
    have h := congrArg Complex.im hz1
    simpa [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
      Complex.exp_im, Real.exp_zero] using h
  have hX1 : ((x : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ))
      = r2 * Real.cos (ψ + θ) := by
    have h := congrArg Complex.re hz2
    simpa [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
      Complex.exp_im, Real.exp_zero] using h
  have hX2 : ((x : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ))
      = r2 * Real.sin (ψ + θ) := by
    have h := congrArg Complex.im hz2
    simpa [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
      Complex.exp_im, Real.exp_zero] using h
  have hcoe3 : ((ax : Fin 3 → ℝ)) = ‖ax‖ • ((f3 : Fin 3 → ℝ)) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) halign
  have hf3a : ((a : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := by
    rw [hcoe3] at hAA
    rw [pmDotSmulR_p35, dotProduct_comm] at hAA
    exact (mul_eq_zero.mp hAA).resolve_left (norm_ne_zero_iff.mpr hax0)
  have hf3x : ((x : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := by
    rw [hcoe3] at hXX
    rw [pmDotSmulR_p35, dotProduct_comm] at hXX
    exact (mul_eq_zero.mp hXX).resolve_left (norm_ne_zero_iff.mpr hax0)
  have hna : ‖a‖ = r1 := by
    have he := on3_expand hon a
    obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon
    have p11 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) = 1 := h11
    have p22 : ((f2 : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = 1 := h22
    have p33 : ((f3 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 1 := h33
    have p12 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = 0 := h12
    have p13 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := h13
    have p23 : ((f2 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := h23
    have hns : ((a : Fin 3 → ℝ) ⬝ᵥ (a : Fin 3 → ℝ))
        = ((a : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) ^ 2
          + ((a : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) ^ 2
          + ((a : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) ^ 2 := by
      rw [he]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, pmDotAddL_p35, pmDotAddR_p35,
        pmDotSmulL_p35, pmDotSmulR_p35, smul_eq_mul, dotProduct_comm]
      simp only [p11, p22, p33, p12, p13, p23, hf3a]
      ring
    have hsq : ‖a‖ ^ 2 = r1 ^ 2 := by
      rw [pmNormSqDot_p35 a, hns, hA1, hA2, hf3a]
      have hcss := Real.cos_sq_add_sin_sq ψ
      nlinarith [hcss, hr1]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hz | hz
    · exact hz
    · have hnz : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
      linarith
  have hnx : ‖x‖ = r2 := by
    have he := on3_expand hon x
    obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon
    have p11 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) = 1 := h11
    have p22 : ((f2 : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = 1 := h22
    have p33 : ((f3 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 1 := h33
    have p12 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = 0 := h12
    have p13 : ((f1 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := h13
    have p23 : ((f2 : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) = 0 := h23
    have hns : ((x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ))
        = ((x : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) ^ 2
          + ((x : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) ^ 2
          + ((x : Fin 3 → ℝ) ⬝ᵥ (f3 : Fin 3 → ℝ)) ^ 2 := by
      rw [he]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, pmDotAddL_p35, pmDotAddR_p35,
        pmDotSmulL_p35, pmDotSmulR_p35, smul_eq_mul, dotProduct_comm]
      simp only [p11, p22, p33, p12, p13, p23, hf3x]
      ring
    have hsq : ‖x‖ ^ 2 = r2 ^ 2 := by
      rw [pmNormSqDot_p35 x, hns, hX1, hX2, hf3x]
      have hcss := Real.cos_sq_add_sin_sq (ψ + θ)
      nlinarith [hcss, hr2]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hz | hz
    · exact hz
    · have hnz : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
      linarith
  have h11 := hon.1
  have h22 := hon.2.1
  have h33 := hon.2.2.1
  have h12 := hon.2.2.2.1
  have h13 := hon.2.2.2.2.1
  have h23 := hon.2.2.2.2.2.1
  have p21 : ((f2 : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm]
    exact h12
  have p31 : ((f3 : Fin 3 → ℝ) ⬝ᵥ (f1 : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm]
    exact h13
  have p32 : ((f3 : Fin 3 → ℝ) ⬝ᵥ (f2 : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm]
    exact h23
  have hdot : ((a : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ)) = r1 * r2 * Real.cos θ := by
    have hea := on3_expand hon a
    have hex := on3_expand hon x
    rw [hea, hex]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, pmDotAddL_p35, pmDotAddR_p35,
      pmDotSmulL_p35, pmDotSmulR_p35, smul_eq_mul]
    simp only [h11, h22, h33, h12, h13, h23, p21, p31, p32, hf3a, hf3x,
      hA1, hA2, hX1, hX2]
    have hcs : Real.cos ψ * Real.cos (ψ + θ) + Real.sin ψ * Real.sin (ψ + θ)
        = Real.cos θ := by
      have heq := Real.cos_sub (ψ + θ) ψ
      rw [show (ψ + θ) - ψ = θ from by ring] at heq
      linear_combination heq.symm
    linear_combination (r1 * r2) * hcs
  rw [hna, hnx, hdot]
  ring


/-- (pm9) **Strict-side azimuth placement** (cross-sign ⟹ polar angle): the
reference ray `a` and the target `x` in the plane orthogonal to the axis with
`(a×x)·ax > 0` place `x` strictly inside the reference half-turn:
`0 < azim 0 ax a x < π`. -/
private theorem pmAzimOrthoSideGt_p35 {ax a x : V3} (ha0 : a ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (hsign : (crossProduct (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (ax : Fin 3 → ℝ) > 0) :
    0 < azim 0 ax a x ∧ azim 0 ax a x < Real.pi := by
  have hax0 : ax ≠ (0:V3) := fun he =>
    hnc (by rw [he]; exact collinear3_of_eq rfl)
  have h0ne : azim 0 ax a x ≠ 0 := by
    intro hz
    obtain ⟨e, c, hc, hxx⟩ := pmAzimNormalRender0_p35 ha0 hnc hncx hz
    have hco : ((x : V3) : Fin 3 → ℝ)
        = e • ((ax : V3) : Fin 3 → ℝ) + c • ((a : V3) : Fin 3 → ℝ) := by
      simpa [sub_zero] using congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hxx
    have hcross : (crossProduct (a : Fin 3 → ℝ) ((x : V3) : Fin 3 → ℝ))
        ⬝ᵥ (ax : Fin 3 → ℝ) = 0 := by
      rw [hco, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35, cross_self,
        smul_zero, pmDotAddL_p35, pmDotSmulL_p35, zero_dotProduct, add_zero,
        pmDetCyc_p35, cross_self, zero_dotProduct, mul_zero]
    rw [hcross] at hsign
    exact absurd hsign (by linarith)
  have hπ : azim 0 ax a x ≤ Real.pi := by
    by_contra hgt
    have hcompl := azim_compl hnc hncx
    rw [if_neg h0ne] at hcompl
    have hle : azim 0 ax x a ≤ Real.pi := by rw [hcompl]; linarith [azim_nonneg 0 ax a x]
    have hge := pmCrossGeAll_p35 (y := ax) (z := x) (x := a) hax0 hncx
      (azim_nonneg 0 ax x a) hle
    rw [pmDetCyc_p35, show crossProduct (x : Fin 3 → ℝ) (a : Fin 3 → ℝ)
        = -(crossProduct (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)) from
      (cross_anticomm (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)).symm, pmDotNegL_p35] at hge
    linarith
  have hπne : azim 0 ax a x ≠ Real.pi := by
    intro hz
    have hcompl := azim_compl hnc hncx
    rw [if_neg h0ne, hz] at hcompl
    have hle2 : azim 0 ax x a ≤ Real.pi := by rw [hcompl]; linarith
    have hge2 := pmCrossGeAll_p35 (y := ax) (z := x) (x := a) hax0 hncx
      (azim_nonneg 0 ax x a) hle2
    rw [pmDetCyc_p35, show crossProduct (x : Fin 3 → ℝ) (a : Fin 3 → ℝ)
        = -(crossProduct (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)) from
      (cross_anticomm (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)).symm, pmDotNegL_p35] at hge2
    linarith
  exact ⟨lt_of_le_of_ne (azim_nonneg 0 ax a x) (Ne.symm h0ne),
    lt_of_le_of_ne hπ hπne⟩

/-- (pm9) **Negative-side azimuth placement**: `(a×x)·ax < 0` puts the target
in the opposite half-turn: `π < azim 0 ax a x < 2·π`. -/
private theorem pmAzimOrthoSideLt_p35 {ax a x : V3} (ha0 : a ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (hsign : (crossProduct (a : Fin 3 → ℝ) (x : Fin 3 → ℝ)) ⬝ᵥ (ax : Fin 3 → ℝ) < 0) :
    Real.pi < azim 0 ax a x ∧ azim 0 ax a x < 2 * Real.pi := by
  have hax0 : ax ≠ (0:V3) := fun he =>
    hnc (by rw [he]; exact collinear3_of_eq rfl)
  have hgt : ¬ (azim 0 ax a x ≤ Real.pi) := by
    intro hle
    have hge := pmCrossGeAll_p35 (y := ax) (z := a) (x := x) hax0 hnc
      (azim_nonneg 0 ax a x) hle
    rw [pmDetCyc_p35] at hge
    linarith
  exact ⟨not_le.mp hgt, azim_lt_two_pi 0 ax a x⟩

/-- (pm9) **FAN-free chain instance on the normal axis** (the winding engine):
with the order premise, azimuths add. -/
private theorem pmAzimNormalChain_p35 {ax a x y : V3} (hax0 : ax ≠ (0:V3))
    (hnc : ¬ Collinear3 0 ax a) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hle : azim 0 ax a x ≤ azim 0 ax a y) :
    azim 0 ax a y = azim 0 ax a x + azim 0 ax x y :=
  triAzimAdd_p35 (x := (0:V3)) (v := ax) hax0 hnc hncx hncy hle

/-- (pm9) **Azimuthal gap lower bound** (cos form): two orthogonal-to-axis
vectors at annulus norms and chord ≥ 2 meet under an azimuth whose cosine is
at most `2719/3969`, i.e. the gap is at least `2·arcsin(1/(2·h0)) ≈ 46.74°`. -/
private theorem pmAzimOrthoGap46_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : (2:ℝ) ≤ dist x y) :
    Real.cos (azim 0 ax x y) ≤ 2719 / 3969 := by
  have h1 := pmAzimOrthoCos_p35 hax0 hx0 hy0 hncx hncy hXX hYY
  have h2 := pmCosLe46_p35 hx2 hxa hy2 hya hd
  have hP : (0:ℝ) < ‖x‖ * ‖y‖ :=
    mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0)
  rw [← h1] at h2
  exact le_of_mul_le_mul_right h2 hP

/-- (pm9) **Azimuthal gap upper bound** (cos form): chord ≤ `cstab` forces the
azimuth's cosine to be at least `−10601/80000`, i.e. the gap is at most
`2·arcsin(cstab/4) ≈ 97.63°`. -/
private theorem pmAzimOrthoFarCos_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : dist x y ≤ cstab) :
    -(10601 / 80000) ≤ Real.cos (azim 0 ax x y) := by
  have h1 := pmAzimOrthoCos_p35 hax0 hx0 hy0 hncx hncy hXX hYY
  have h2 := pmFarCos_p35 hx2 hxa hy2 hya hd
  have hP : (0:ℝ) < ‖x‖ * ‖y‖ :=
    mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0)
  rw [← h1] at h2
  exact le_of_mul_le_mul_right h2 hP

/-- (pm9) **Azimuthal gap in angle form**: within `[0, π]` the cos bound turns
into the `arccos` lower bound. -/
private theorem pmAzimOrthoGapGe_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : (2:ℝ) ≤ dist x y)
    (hπ : azim 0 ax x y ≤ Real.pi) :
    Real.arccos (2719 / 3969) ≤ azim 0 ax x y := by
  have hcos := pmAzimOrthoGap46_p35 hax0 hx0 hy0 hncx hncy hXX hYY hx2 hxa hy2 hya hd
  have h2 : Real.arccos (Real.cos (azim 0 ax x y)) = azim 0 ax x y :=
    Real.arccos_cos (azim_nonneg 0 ax x y) hπ
  rw [← h2]
  exact Real.arccos_le_arccos hcos

/-! ## planemiss10 rungs (lkgrqui-planemiss10-w3, 2026-10-28)

The coplanar-triple squeeze endgame.  Three distinct axis-orthogonal annulus
points with all pairwise chords in `[2, cstab]` are contradictory: the three
azimuthal arcs around the axis sum to `2π`, each arc lands in
`[0, β] ∪ [2π-β, 2π]` with `β := arccos(-10601/80000) < 2π/3` (so at most one
"far" arc exists), and against the chord-`≥2` radius pinch the far-arc branch
collides with `dist ≤ cstab`.  This is the closed core of the root's step (i):
the blocked/same-side branch of the d = 2 squeeze needs no orientation data.
Insertion point: after `pmAzimOrthoGapGe_p35`, before the
`pmPlaneCrowding_p35` docstring. -/

/-- (pm10) **Far-arc split**: an axis-orthogonal annulus pair at chord
`≤ cstab` has its directed azimuth on one of the two near arcs:
`azim ≤ β` or `2π − azim ≤ β` where `β := arccos(−10601/80000) < 2π/3`. -/
private theorem pmOrthoTriFarSplit_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : dist x y ≤ cstab) :
    azim 0 ax x y ≤ Real.arccos (-(10601 / 80000)) ∨
      2 * Real.pi - azim 0 ax x y ≤ Real.arccos (-(10601 / 80000)) := by
  have hcos := pmAzimOrthoFarCos_p35 hax0 hx0 hy0 hncx hncy hXX hYY hx2 hxa hy2 hya hd
  have h0 : (0:ℝ) ≤ azim 0 ax x y := azim_nonneg 0 ax x y
  rcases lt_or_ge Real.pi (azim 0 ax x y) with hgt | hle
  · refine Or.inr ?_
    have h2pi : azim 0 ax x y < 2 * Real.pi := azim_lt_two_pi 0 ax x y
    have hleπ : 2 * Real.pi - azim 0 ax x y ≤ Real.pi := by linarith
    have hge0 : (0:ℝ) ≤ 2 * Real.pi - azim 0 ax x y := by linarith
    have hper : Real.cos (2 * Real.pi - azim 0 ax x y) = Real.cos (azim 0 ax x y) := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      ring
    rw [← hper] at hcos
    have h1 := Real.arccos_le_arccos hcos
    rwa [Real.arccos_cos hge0 hleπ] at h1
  · refine Or.inl ?_
    have h1 := Real.arccos_le_arccos hcos
    rwa [Real.arccos_cos h0 hle] at h1

/-- (pm10) An axis-orthogonal annulus pair at chord `≥ 2` has nonzero directed
azimuth (`cos ≤ 2719/3969 < 1 = cos 0`). -/
private theorem pmOrthoTriAzimNe0_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : (2:ℝ) ≤ dist x y) : azim 0 ax x y ≠ 0 := by
  intro hz
  have hcos := pmAzimOrthoGap46_p35 hax0 hx0 hy0 hncx hncy hXX hYY hx2 hxa hy2 hya hd
  rw [hz] at hcos
  norm_num at hcos

/-- (pm10) The cosine value of `2π/3`. -/
private theorem pmOrthoTriCos23_p35 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- (pm10) The far-arc constant is at most `2π/3`:
`arccos(−10601/80000) ≤ arccos(−1/2) = 2π/3`. -/
private theorem pmOrthoTriBetaLe_p35 :
    Real.arccos (-(10601 / 80000)) ≤ 2 * Real.pi / 3 := by
  have h023 : (0:ℝ) ≤ 2 * Real.pi / 3 := by linarith [Real.pi_pos]
  have hπ23 : 2 * Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
  have hcomp : Real.arccos (-(10601 / 80000))
      ≤ Real.arccos (Real.cos (2 * Real.pi / 3)) :=
    Real.arccos_le_arccos (show Real.cos (2 * Real.pi / 3) ≤ -(10601 / 80000) by
      rw [pmOrthoTriCos23_p35]; norm_num)
  rw [Real.arccos_cos h023 hπ23] at hcomp
  exact hcomp

/-- (pm10) **The chord-`≥2` radius pinch**: two annulus points at chord `≥ 2`
whose azimuth cosine is `≥ w` have product of norms at least
`(4 − (2·h0−2)²) / (2(1−w))` — with `e := 2(1−w)`, `(2331/625)/e ≤ ‖x‖‖y‖`. -/
private theorem pmOrthoPinch_p35 {x y : V3} {δ w e : ℝ}
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hwe : e = 2 * ((1:ℝ) - w)) (hcos : Real.cos δ ≥ w)
    (hdot : (x : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)
      = Real.cos δ * (‖x‖ * ‖y‖))
    (hd : (2:ℝ) ≤ dist x y) :
    (2331 / 625) ≤ e * (‖x‖ * ‖y‖) := by
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  rw [h02] at hxa hya
  have hxp : (0:ℝ) ≤ ‖x‖ := by linarith
  have hyp : (0:ℝ) ≤ ‖y‖ := by linarith
  have hnp : (0:ℝ) ≤ ‖x‖ * ‖y‖ := by
    nlinarith [hxp, hyp]
  have hdn := pmDotNormDist_p35 x y
  rw [hdot] at hdn
  have h2 : 2 * Real.cos δ * (‖x‖ * ‖y‖) = ‖x‖ ^ 2 + ‖y‖ ^ 2 - dist x y ^ 2 := by
    linarith
  have hsqid : (‖x‖ - ‖y‖)^2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (‖x‖ * ‖y‖) := by ring
  have h13a : ‖x‖ - ‖y‖ ≤ 13 / 25 := by linarith
  have h13b : ‖y‖ - ‖x‖ ≤ 13 / 25 := by linarith
  have hsqle : (‖x‖ - ‖y‖)^2 ≤ (13 / 25)^2 := by
    nlinarith [h13a, h13b]
  have hstep1 : (4:ℝ) - (13 / 25)^2
      ≤ 2 * (‖x‖ * ‖y‖) - 2 * Real.cos δ * (‖x‖ * ‖y‖) := by
    have h4 : (4:ℝ) ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * Real.cos δ * (‖x‖ * ‖y‖) := by
      rw [h2]; nlinarith [hd]
    nlinarith [h4, hsqid, hsqle]
  have hcw : 2 * w * (‖x‖ * ‖y‖) ≤ 2 * Real.cos δ * (‖x‖ * ‖y‖) := by
    nlinarith [hcos, hnp]
  rw [hwe]
  have hexpl : (2 - 2 * w) * (‖x‖ * ‖y‖)
      = 2 * (‖x‖ * ‖y‖) - 2 * w * (‖x‖ * ‖y‖) := by ring
  linarith

/-- (pm10) cosine values and bounds for the arc constants. -/
private theorem pmOrthoTriCosA_p35 :
    Real.cos (Real.arccos (2719 / 3969)) = 2719 / 3969 :=
  Real.cos_arccos (by norm_num : -1 ≤ (2719:ℝ) / 3969) (by norm_num : (2719:ℝ) / 3969 ≤ 1)

private theorem pmOrthoTriCosB_p35 :
    Real.cos (Real.arccos (-(10601 / 80000))) = -(10601 / 80000) :=
  Real.cos_arccos (by norm_num : -1 ≤ -((10601:ℝ) / 80000)) (by norm_num : -((10601:ℝ) / 80000) ≤ 1)

private theorem pmOrthoTriSinA_p35 :
    (7284:ℝ) / 10000 ≤ Real.sin (Real.arccos (2719 / 3969)) := by
  have h : Real.sin (Real.arccos (2719 / 3969)) = Real.sqrt (1 - (2719 / 3969) ^ 2) :=
    Real.sin_arccos (2719 / 3969)
  have h2 : ((7284:ℝ) / 10000) ^ 2 ≤ 1 - (2719 / 3969) ^ 2 := by norm_num
  have h3 := (Real.sqrt_le_sqrt_iff (show (0:ℝ) ≤ 1 - (2719 / 3969) ^ 2 by norm_num)).mpr h2
  rw [Real.sqrt_sq (show (0:ℝ) ≤ (7284:ℝ) / 10000 by norm_num)] at h3
  rw [h]
  exact h3

private theorem pmOrthoTriSinB_p35 :
    (9911:ℝ) / 10000 ≤ Real.sin (Real.arccos (-(10601 / 80000))) := by
  have h : Real.sin (Real.arccos (-((10601:ℝ) / 80000)))
      = Real.sqrt (1 - (-(10601 / 80000)) ^ 2) := Real.sin_arccos (-((10601:ℝ) / 80000))
  have h2 : ((9911:ℝ) / 10000) ^ 2 ≤ 1 - (-(10601 / 80000)) ^ 2 := by norm_num
  have h3 := (Real.sqrt_le_sqrt_iff (show (0:ℝ) ≤ 1 - (-(10601 / 80000)) ^ 2 by norm_num)).mpr h2
  rw [Real.sqrt_sq (show (0:ℝ) ≤ (9911:ℝ) / 10000 by norm_num)] at h3
  rw [h]
  exact h3

/-- (pm10) the half-arc cosine lower bound `cos(β/2) ≥ 3283/5000`. -/
private theorem pmOrthoTriHalf_p35 :
    (3283:ℝ) / 5000 ≤ Real.cos (Real.arccos (-(10601 / 80000)) / 2) := by
  have hcm := Real.cos_half
    (show -(Real.pi:ℝ) ≤ Real.arccos (-((10601:ℝ) / 80000)) from
      by linarith [Real.arccos_nonneg (-((10601:ℝ) / 80000)), Real.pi_pos])
    (Real.arccos_le_pi (-((10601:ℝ) / 80000)))
  rw [pmOrthoTriCosB_p35] at hcm
  rw [hcm]
  have h2 : ((3283:ℝ)/5000)^2 ≤ (1 + -((10601:ℝ) / 80000)) / 2 := by norm_num
  have h3 := (Real.sqrt_le_sqrt_iff (show (0:ℝ) ≤ (1 + -((10601:ℝ) / 80000)) / 2 by norm_num)).mpr h2
  rw [Real.sqrt_sq (show (0:ℝ) ≤ (3283:ℝ)/5000 by norm_num)] at h3
  exact h3

/-- (pm10) the mixed-arc cosine bound `cos(β − α) ≥ 63/100`. -/
private theorem pmOrthoTriBA_p35 :
    (63:ℝ) / 100 ≤ Real.cos (Real.arccos (-(10601 / 80000)) - Real.arccos (2719 / 3969)) := by
  have hcs : Real.cos (Real.arccos (-(10601 / 80000)) - Real.arccos (2719 / 3969))
      = Real.cos (Real.arccos (-(10601 / 80000))) * Real.cos (Real.arccos (2719 / 3969))
        + Real.sin (Real.arccos (-(10601 / 80000))) * Real.sin (Real.arccos (2719 / 3969)) :=
    Real.cos_sub _ _
  rw [hcs, pmOrthoTriCosB_p35, pmOrthoTriCosA_p35]
  have h1 := pmOrthoTriSinB_p35
  have h2 := pmOrthoTriSinA_p35
  have hsB0 : (0:ℝ) ≤ Real.sin (Real.arccos (-(10601 / 80000))) := le_trans (by norm_num) h1
  have hsA0 : (0:ℝ) ≤ Real.sin (Real.arccos (2719 / 3969)) := le_trans (by norm_num) h2
  have hprod : ((9911:ℝ)/10000) * ((7284:ℝ)/10000)
      ≤ Real.sin (Real.arccos (-(10601 / 80000))) * Real.sin (Real.arccos (2719 / 3969)) :=
    by nlinarith [h1, h2, hsB0, hsA0]
  linarith [hprod]

/-- (pm10) the doubled-arc cosine value `cos(2α) = −967039/15752961`. -/
private theorem pmOrthoTriCos2A_p35 :
    Real.cos (2 * Real.arccos (2719 / 3969)) = -(967039 / 15752961) := by
  have hcm := Real.cos_two_mul (Real.arccos (2719 / 3969))
  rw [pmOrthoTriCosA_p35] at hcm
  rw [hcm]
  norm_num

/-- (pm10) cosine is antitone on `[0, π]`. -/
private theorem pmOrthoTriCosMono_p35 {x y : ℝ} (h1 : (0:ℝ) ≤ x) (h2 : x ≤ y)
    (h3 : y ≤ Real.pi) : Real.cos y ≤ Real.cos x :=
  Real.cos_le_cos_of_nonneg_of_le_pi h1 h3 h2

/-- (pm10) azimuthal cosine is direction-symmetric off the axis. -/
private theorem pmOrthoTriCosSym_p35 {ax x y : V3}
    (hncx : ¬ Collinear3 0 ax x) (hncy : ¬ Collinear3 0 ax y)
    (hne : azim 0 ax x y ≠ 0) :
    Real.cos (azim 0 ax x y) = Real.cos (azim 0 ax y x) := by
  have hcompl := azim_compl hncx hncy
  rw [if_neg hne] at hcompl
  rw [hcompl, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring

/-- (pm10) **The far-pair dead end**: axis-orthogonal annulus points `u, v, w`
with the `(v,w)` azimuth squeezed near (`cos ≥ 3283/5000`, i.e. arc `≤ β/2`)
and the `(u,v)` azimuth far (`cos ≤ −967039/15752961`): the `(u,v)` chord
bound `≤ cstab` collapses against the chord-`≥2` radius pinch
(`‖v‖ ≥ 25900/12019 ≈ 2.155`, `‖u‖ ≥ 2` forces `dist(u,v)² ≥ 9.17 > 9.0601`). -/
private theorem pmOrthoTriDead_p35 {ax u v w : V3} (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hv0 : v ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hncu : ¬ Collinear3 0 ax u) (hncv : ¬ Collinear3 0 ax v)
    (hncw : ¬ Collinear3 0 ax w)
    (hUU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hVV : (v : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hWW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hv2 : (2:ℝ) ≤ ‖v‖) (hva : ‖v‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (hduv : dist u v ≤ cstab) (hduv2 : (2:ℝ) ≤ dist u v)
    (hdvw2 : (2:ℝ) ≤ dist v w)
    (hB : Real.cos (azim 0 ax v w) ≥ (3283:ℝ) / 5000)
    (hK : Real.cos (azim 0 ax u v) ≤ -((967039:ℝ) / 15752961)) : False := by
  have h02 : (2:ℝ) * h0 = 63 / 25 := by norm_num [h0]
  have hcs : cstab = 301 / 100 := by norm_num [cstab]
  have hnp0 : (0:ℝ) ≤ ‖u‖ * ‖v‖ := by nlinarith [hu2]
  -- pinch on the (v,w) pair: ‖v‖·‖w‖ ≥ 9324/1717
  have hdotvw : (v : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ)
      = Real.cos (azim 0 ax v w) * (‖v‖ * ‖w‖) :=
    (pmAzimOrthoCos_p35 hax0 hv0 hw0 hncv hncw hVV hWW).symm
  have hpinch := pmOrthoPinch_p35 (x := v) (y := w) (δ := azim 0 ax v w)
    (w := (3283:ℝ) / 5000) (e := (3434:ℝ) / 5000) hv2 hva hw2 hwa
    (by norm_num) hB hdotvw hdvw2
  have hnpub : ‖v‖ * ‖w‖ ≤ ((63:ℝ) / 25) * ‖v‖ := by
    have hwa' : ‖w‖ ≤ (63:ℝ) / 25 := by linarith
    nlinarith [hwa', hnp0]
  have hvge : (25900:ℝ) / 12019 ≤ ‖v‖ := by linarith
  -- the (u,v) chord identities
  have hcosuv := pmAzimOrthoCos_p35 hax0 hu0 hv0 hncu hncv hUU hVV
  have hdn := pmDotNormDist_p35 u v
  rw [hcosuv.symm] at hdn
  have h1 : dist u v ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * Real.cos (azim 0 ax u v) * (‖u‖ * ‖v‖) := by
    linarith
  have hu2sq : (4:ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [hu2]
  have hv2sq : ((25900:ℝ)/12019)^2 ≤ ‖v‖ ^ 2 := by nlinarith [hvge]
  have hnp2 : (2:ℝ) * (25900:ℝ) / 12019 ≤ ‖u‖ * ‖v‖ := by nlinarith [hu2, hvge]
  have hcn : Real.cos (azim 0 ax u v) * (‖u‖ * ‖v‖)
      ≤ -((967039:ℝ) / 15752961) * (‖u‖ * ‖v‖) := by nlinarith [hK, hnp0]
  have hcoslo : -2 * Real.cos (azim 0 ax u v) * (‖u‖ * ‖v‖)
      ≥ (2 * (967039:ℝ) / 15752961) * ((2:ℝ) * (25900:ℝ) / 12019) := by
    linarith
  have hduvle : dist u v ≤ (301:ℝ) / 100 := by rw [hcs] at hduv; exact hduv
  have hd0 : (0:ℝ) ≤ dist u v := le_trans (by norm_num) hduv2
  have hkey : dist u v ^ 2 ≤ ((301:ℝ) / 100) ^ 2 := by nlinarith [hduvle, hd0]
  have hfin : (4:ℝ) + ((25900:ℝ) / 12019) ^ 2
      + ((2 * (967039:ℝ) / 15752961)) * ((2:ℝ) * (25900:ℝ) / 12019) ≤ dist u v ^ 2 := by
    linarith
  linarith

/-- (pm10) **The far-arc squeeze** (chain-order triple, exactly one far arc):
with the arc of pair `(p,q)` far and the arcs of `(q,r)`, `(r,p)` near, the
radius pinch on a near pair against the far pair's chord bound contradicts
`dist p q ≤ cstab`. -/
private theorem pmOrthoTriFar3_p35 {ax p q r : V3} (hax0 : ax ≠ (0:V3))
    (hp0 : p ≠ (0:V3)) (hq0 : q ≠ (0:V3)) (hr0 : r ≠ (0:V3))
    (hncp : ¬ Collinear3 0 ax p) (hncq : ¬ Collinear3 0 ax q)
    (hncr : ¬ Collinear3 0 ax r)
    (hPP : (p : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hQQ : (q : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hRR : (r : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hp2 : (2:ℝ) ≤ ‖p‖) (hpa : ‖p‖ ≤ 2 * h0)
    (hq2 : (2:ℝ) ≤ ‖q‖) (hqa : ‖q‖ ≤ 2 * h0)
    (hr2 : (2:ℝ) ≤ ‖r‖) (hra : ‖r‖ ≤ 2 * h0)
    (hpq : dist p q ≤ cstab) (hqr : dist q r ≤ cstab) (hrp : dist r p ≤ cstab)
    (epq : (2:ℝ) ≤ dist p q) (eqr : (2:ℝ) ≤ dist q r) (erp : (2:ℝ) ≤ dist r p)
    (hsum : azim 0 ax p q + azim 0 ax q r + azim 0 ax r p = 2 * Real.pi)
    (h1f : 2 * Real.pi - azim 0 ax p q ≤ Real.arccos (-(10601 / 80000)))
    (h2n : azim 0 ax q r ≤ Real.arccos (-(10601 / 80000)))
    (h3n : azim 0 ax r p ≤ Real.arccos (-(10601 / 80000))) : False := by
  have hβπ : Real.arccos (-(10601 / 80000)) ≤ Real.pi :=
    le_trans pmOrthoTriBetaLe_p35 (le_of_lt (by linarith [Real.pi_pos]))
  have hB0 : (0:ℝ) ≤ azim 0 ax q r := azim_nonneg 0 ax q r
  have hC0 : (0:ℝ) ≤ azim 0 ax r p := azim_nonneg 0 ax r p
  have hBπ : azim 0 ax q r ≤ Real.pi := le_trans h2n hβπ
  have hCπ : azim 0 ax r p ≤ Real.pi := le_trans h3n hβπ
  -- both small arcs are at least α
  have hBα : Real.arccos (2719 / 3969) ≤ azim 0 ax q r := by
    have hcos := pmAzimOrthoGap46_p35 hax0 hq0 hr0 hncq hncr hQQ hRR hq2 hqa hr2 hra eqr
    have hacc := Real.arccos_cos hB0 hBπ
    have hle := Real.arccos_le_arccos hcos
    rw [hacc] at hle
    exact hle
  have hCα : Real.arccos (2719 / 3969) ≤ azim 0 ax r p := by
    have hcos := pmAzimOrthoGap46_p35 hax0 hr0 hp0 hncr hncp hRR hPP hr2 hra hp2 hpa erp
    have hacc := Real.arccos_cos hC0 hCπ
    have hle := Real.arccos_le_arccos hcos
    rw [hacc] at hle
    exact hle
  -- the small-arc sum is confined, and the far pair's cosine is at most cos(2α)
  have h2a : (2:ℝ) * Real.arccos (2719 / 3969) ≤ azim 0 ax q r + azim 0 ax r p := by
    linarith
  have hBCπ : azim 0 ax q r + azim 0 ax r p ≤ Real.pi := by
    have hBCle : azim 0 ax q r + azim 0 ax r p ≤ Real.arccos (-(10601 / 80000)) := by
      linarith
    linarith
  have hper : Real.cos (azim 0 ax p q) = Real.cos (azim 0 ax q r + azim 0 ax r p) := by
    have hp1 := Real.cos_periodic (azim 0 ax p q - 2 * Real.pi)
    rw [show azim 0 ax p q - 2 * Real.pi + 2 * Real.pi = azim 0 ax p q from by ring] at hp1
    rw [show azim 0 ax p q - 2 * Real.pi
        = -(azim 0 ax q r + azim 0 ax r p) from by linarith] at hp1
    rw [Real.cos_neg] at hp1
    exact hp1
  have hK : Real.cos (azim 0 ax p q) ≤ -((967039:ℝ) / 15752961) := by
    have hmono := pmOrthoTriCosMono_p35
      (show (0:ℝ) ≤ 2 * Real.arccos (2719 / 3969) from
        by linarith [Real.arccos_nonneg ((2719:ℝ) / 3969)])
      h2a hBCπ
    rw [pmOrthoTriCos2A_p35] at hmono
    rw [← hper] at hmono
    linarith
  -- exactly one of the two small arcs is at most β/2
  rcases lt_or_ge (azim 0 ax q r) (Real.arccos (-(10601 / 80000)) / 2) with hBh | hBg
  · exact pmOrthoTriDead_p35 hax0 hp0 hq0 hr0 hncp hncq hncr hPP hQQ hRR
      hp2 hpa hq2 hqa hr2 hra hpq epq eqr
      (show Real.cos (azim 0 ax q r) ≥ (3283:ℝ) / 5000 from
        by
          have h1 := pmOrthoTriHalf_p35
          have h2 := pmOrthoTriCosMono_p35 hB0 hBh.le
            (show Real.arccos (-(10601 / 80000)) / 2 ≤ Real.pi from
              by linarith [pmOrthoTriBetaLe_p35, Real.pi_pos])
          linarith)
      (show Real.cos (azim 0 ax p q) ≤ -((967039:ℝ) / 15752961) from hK)
  · have hCh : azim 0 ax r p ≤ Real.arccos (-(10601 / 80000)) / 2 := by linarith
    exact pmOrthoTriDead_p35 (ax := ax) (u := q) (v := p) (w := r) hax0 hq0 hp0 hr0
      hncq hncp hncr hQQ hPP hRR
      hq2 hqa hp2 hpa hr2 hra (by rw [dist_comm]; exact hpq) (by rw [dist_comm]; exact epq)
      (by rw [dist_comm]; exact erp)
      (show Real.cos (azim 0 ax p r) ≥ (3283:ℝ) / 5000 from
        by
          have hsym := pmOrthoTriCosSym_p35 hncr hncp
            (pmOrthoTriAzimNe0_p35 hax0 hr0 hp0 hncr hncp hRR hPP hr2 hra hp2 hpa
              erp)
          have h1 := pmOrthoTriHalf_p35
          have h2 := pmOrthoTriCosMono_p35 hC0 hCh
            (show Real.arccos (-(10601 / 80000)) / 2 ≤ Real.pi from
              by linarith [pmOrthoTriBetaLe_p35, Real.pi_pos])
          rw [← hsym]
          linarith)
      (show Real.cos (azim 0 ax q p) ≤ -((967039:ℝ) / 15752961) from
        by
          have hsym := pmOrthoTriCosSym_p35 hncp hncq
            (pmOrthoTriAzimNe0_p35 hax0 hp0 hq0 hncp hncq hPP hQQ hp2 hpa hq2 hqa epq)
          rw [← hsym]
          exact hK)

/-- (pm10) **The chain-order triple kill**: three distinct axis-orthogonal
annulus points, all pairwise chords in `[2, cstab]`, with the reference-frame
azimuths of the first two ordered.  The three cycle arcs sum to `2π` and each
lands in `[0, β] ∪ [2π−β, 2π]` with `β ≤ 2π/3`; either two arcs are far
(sum > `2π`), all are near (sum ≤ `3β < 2π` with the equality cascade forcing
`cos ≥ −1/2 > −10601/80000`), or one arc is far and the pinch applies. -/
private theorem pmOrthoTriCycleKill_p35 {ax p q r : V3} (hax0 : ax ≠ (0:V3))
    (hp0 : p ≠ (0:V3)) (hq0 : q ≠ (0:V3)) (hr0 : r ≠ (0:V3))
    (hncp : ¬ Collinear3 0 ax p) (hncq : ¬ Collinear3 0 ax q)
    (hncr : ¬ Collinear3 0 ax r)
    (hPP : (p : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hQQ : (q : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hRR : (r : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hp2 : (2:ℝ) ≤ ‖p‖) (hpa : ‖p‖ ≤ 2 * h0)
    (hq2 : (2:ℝ) ≤ ‖q‖) (hqa : ‖q‖ ≤ 2 * h0)
    (hr2 : (2:ℝ) ≤ ‖r‖) (hra : ‖r‖ ≤ 2 * h0)
    (hpq : dist p q ≤ cstab) (hqr : dist q r ≤ cstab) (hrp : dist r p ≤ cstab)
    (epq : (2:ℝ) ≤ dist p q) (eqr : (2:ℝ) ≤ dist q r) (erp : (2:ℝ) ≤ dist r p)
    (hord : azim 0 ax p q ≤ azim 0 ax p r) : False := by
  have hne0pr : azim 0 ax p r ≠ 0 :=
    pmOrthoTriAzimNe0_p35 hax0 hp0 hr0 hncp hncr hPP hRR hp2 hpa hr2 hra
      (by rw [dist_comm]; exact erp)
  have hchain := pmAzimNormalChain_p35 hax0 hncp hncq hncr hord
  have hcompl := azim_compl hncp hncr
  rw [if_neg hne0pr] at hcompl
  have hβπ : Real.arccos (-(10601 / 80000)) ≤ 2 * Real.pi / 3 := pmOrthoTriBetaLe_p35
  have hsum : azim 0 ax p q + azim 0 ax q r + azim 0 ax r p = 2 * Real.pi := by
    rw [← hchain, hcompl]
    ring
  have hf1 := pmOrthoTriFarSplit_p35 (x := p) (y := q) hax0 hp0 hq0 hncp hncq hPP hQQ
    hp2 hpa hq2 hqa hpq
  have hf2 := pmOrthoTriFarSplit_p35 (x := q) (y := r) hax0 hq0 hr0 hncq hncr hQQ hRR
    hq2 hqa hr2 hra hqr
  have hf3 := pmOrthoTriFarSplit_p35 (x := r) (y := p) hax0 hr0 hp0 hncr hncp hRR hPP
    hr2 hra hp2 hpa hrp
  have hC0 : (0:ℝ) ≤ azim 0 ax r p := azim_nonneg 0 ax r p
  have hA0 : (0:ℝ) ≤ azim 0 ax p q := azim_nonneg 0 ax p q
  have hB0c : (0:ℝ) ≤ azim 0 ax q r := azim_nonneg 0 ax q r
  rcases hf1 with h1n | h1f
  · rcases hf2 with h2n | h2f
    · rcases hf3 with h3n | h3f
      · -- all arcs near: the equality cascade
        have hβeq : Real.arccos (-(10601 / 80000)) = 2 * Real.pi / 3 := by
          have hsumle : azim 0 ax p q + azim 0 ax q r + azim 0 ax r p
              ≤ 3 * Real.arccos (-(10601 / 80000)) := by linarith
          linarith [hsum, hsumle, pmOrthoTriBetaLe_p35]
        have ht2 : azim 0 ax p q = Real.arccos (-(10601 / 80000)) := by linarith
        have hcA : Real.cos (azim 0 ax p q) = Real.cos (2 * Real.pi / 3) := by
          rw [ht2, hβeq]
        rw [pmOrthoTriCos23_p35] at hcA
        have hfar := pmAzimOrthoFarCos_p35 hax0 hp0 hq0 hncp hncq hPP hQQ hp2 hpa hq2 hqa hpq
        linarith
      · exact pmOrthoTriFar3_p35 (p := r) (q := p) (r := q) hax0 hr0 hp0 hq0 hncr hncp hncq
          hRR hPP hQQ hr2 hra hp2 hpa hq2 hqa hrp hpq hqr erp epq eqr
          (show azim 0 ax r p + azim 0 ax p q + azim 0 ax q r = 2 * Real.pi from
            by linarith)
          h3f h1n h2n
    · rcases hf3 with h3n | h3f
      · exact pmOrthoTriFar3_p35 (p := q) (q := r) (r := p) hax0 hq0 hr0 hp0 hncq hncr hncp
          hQQ hRR hPP hq2 hqa hr2 hra hp2 hpa hqr hrp hpq eqr erp epq
          (show azim 0 ax q r + azim 0 ax r p + azim 0 ax p q = 2 * Real.pi from
            by linarith)
          h2f h3n h1n
      · linarith [Real.pi_pos]
  · rcases hf2 with h2n | h2f
    · rcases hf3 with h3n | h3f
      · exact pmOrthoTriFar3_p35 hax0 hp0 hq0 hr0 hncp hncq hncr hPP hQQ hRR
          hp2 hpa hq2 hqa hr2 hra hpq hqr hrp epq eqr erp hsum h1f h2n h3n
      · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

/-- (pm10) **THE COPLANAR-TRIPLE SQUEEZE** (the closed step-(i) core): three
distinct axis-orthogonal annulus points with all pairwise chords in
`[2, cstab]` cannot exist.  No orientation data is needed: the reference
azimuths are ordered (or the pair `q,r` is swapped, which permutes the
hypotheses), the three cycle arcs around the axis sum to `2π`, each arc is
confined to `[0, β] ∪ [2π−β, 2π]` with `β := arccos(−10601/80000) ≤ 2π/3`,
so either two arcs are far (sum > `2π`), all are near (sum ≤ `3β ≤ 2π` with
the equality cascade forcing `cos ≥ −1/2 > −10601/80000`), or one arc is far
and the chord-`≥2` radius pinch kills the remaining pair.  This discharges
the blocked/same-side branch of the root's d = 2 squeeze endgame (the
in-plane triple `u, x₁, w` of the dart plane with pairwise chords in
`[2, cstab]`); the d ≥ 3 winding account and the off-plane branch remain
for the next lanes. -/
private theorem pmOrthoTriCstabKill_p35 {ax p q r : V3} (hax0 : ax ≠ (0:V3))
    (hp0 : p ≠ (0:V3)) (hq0 : q ≠ (0:V3)) (hr0 : r ≠ (0:V3))
    (hncp : ¬ Collinear3 0 ax p) (hncq : ¬ Collinear3 0 ax q)
    (hncr : ¬ Collinear3 0 ax r)
    (hPP : (p : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hQQ : (q : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hRR : (r : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hp2 : (2:ℝ) ≤ ‖p‖) (hpa : ‖p‖ ≤ 2 * h0)
    (hq2 : (2:ℝ) ≤ ‖q‖) (hqa : ‖q‖ ≤ 2 * h0)
    (hr2 : (2:ℝ) ≤ ‖r‖) (hra : ‖r‖ ≤ 2 * h0)
    (hpq : dist p q ≤ cstab) (hqr : dist q r ≤ cstab) (hrp : dist r p ≤ cstab)
    (epq : (2:ℝ) ≤ dist p q) (eqr : (2:ℝ) ≤ dist q r) (erp : (2:ℝ) ≤ dist r p) :
    False := by
  rcases lt_or_ge (azim 0 ax p q) (azim 0 ax p r) with hle | hge
  · exact pmOrthoTriCycleKill_p35 hax0 hp0 hq0 hr0 hncp hncq hncr hPP hQQ hRR
      hp2 hpa hq2 hqa hr2 hra hpq hqr hrp epq eqr erp hle.le
  · exact pmOrthoTriCycleKill_p35 (p := p) (q := r) (r := q) hax0 hp0 hr0 hq0 hncp hncr hncq
      hPP hRR hQQ hp2 hpa hr2 hra hq2 hqa (by rw [dist_comm]; exact hrp)
      (by rw [dist_comm]; exact hqr) (by rw [dist_comm]; exact hpq)
      (by rw [dist_comm]; exact erp) (by rw [dist_comm]; exact eqr)
      (by rw [dist_comm]; exact epq) hge

/-! ## planemiss11 rungs (lkgrqui-planemiss11-w3, 2026-10-28)

The d >= 3 winding engine: the (b) direction-engine interface (3-step chain
+ cycle sum) and the (c) counting/radius-coupling arithmetic.  The root's
d >= 3 branch splits over the two ring arcs between the diagonal endpoints
`u, w` (both in the dart plane `span {a, b}`): each arc contributes its
azimuthal displacement, the chain rule turns a run of three consecutive
in-plane steps into the arc displacement, and the counting conjunct
(`isScsV39`, `k = 6`) closes the arithmetic feed for the hexagonal squeeze. -/

/-- (pm11) cosine of `pi/3`. -/
private theorem pmOrthoTriCosPi3_p35 : Real.cos (Real.pi / 3) = 1 / 2 :=
  Real.cos_pi_div_three

/-- (pm11) `sqrt(2)/2` exceeds `10601/80000` (used to bound the far arc
constant `beta` against `3*pi/4`). -/
private theorem pmOrthoSqrt2LtA_p35 : (10601:ℝ) / 80000 < Real.sqrt 2 / 2 := by
  have h2 : ((10601:ℝ) / 80000) * ((10601:ℝ) / 80000) < 1 / 2 := by norm_num
  by_contra hge
  have hge' : (10601:ℝ) / 80000 ≥ Real.sqrt 2 / 2 := le_of_not_gt hge
  have hmul : ((10601:ℝ) / 80000) * ((10601:ℝ) / 80000)
      ≥ Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) := by
    nlinarith [hge', Real.sqrt_nonneg 2,
      sq_nonneg ((10601:ℝ) / 80000 - Real.sqrt 2 / 2)]
  have hs22 : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  rw [hs22] at hmul
  linarith

/-- (pm11) `sqrt(2)/2` exceeds `2719/3969` (used to bound the step constant
`alpha` below `pi/4`). -/
private theorem pmOrthoSqrt2HalfBig_p35 : (2719:ℝ) / 3969 < Real.sqrt 2 / 2 := by
  have h2 : ((2719:ℝ) / 3969) * ((2719:ℝ) / 3969) < 1 / 2 := by norm_num
  by_contra hge
  have hge' : (2719:ℝ) / 3969 ≥ Real.sqrt 2 / 2 := le_of_not_gt hge
  have hmul : ((2719:ℝ) / 3969) * ((2719:ℝ) / 3969)
      ≥ Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) := by
    nlinarith [hge', Real.sqrt_nonneg 2,
      sq_nonneg ((2719:ℝ) / 3969 - Real.sqrt 2 / 2)]
  have hs22 : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  rw [hs22] at hmul
  linarith

/-- (pm11) **The 3-step chain** (direction-engine interface): with the
counterclockwise order premises along an in-plane run, the azimuth from the
run head to the run tail is the sum of the three consecutive step azimuths
(the FAN-free `triAzimAdd_p35` applied twice). -/
private theorem pmOrthoArcChain3_p35 {ax p q r s : V3} (hax0 : ax ≠ (0:V3))
    (hncp : ¬ Collinear3 0 ax p) (hncq : ¬ Collinear3 0 ax q)
    (hncr : ¬ Collinear3 0 ax r) (hncs : ¬ Collinear3 0 ax s)
    (h1 : azim 0 ax p q ≤ azim 0 ax p r)
    (h2 : azim 0 ax p r ≤ azim 0 ax p s) :
    azim 0 ax p s
      = azim 0 ax p q + azim 0 ax q r + azim 0 ax r s := by
  have hstep1 := pmAzimNormalChain_p35 hax0 hncp hncq hncr h1
  have hstep2 := pmAzimNormalChain_p35 (a := p) (x := r) (y := s) hax0 hncp hncr hncs h2
  rw [hstep2, hstep1]

/-- (pm11) **The cycle-sum supplier** (Sigma = 2*pi): a monotone 3-step run
plus the closing arc sums to the full turn. -/
private theorem pmOrthoCycleSum_p35 {ax p q r s : V3} (hax0 : ax ≠ (0:V3))
    (hncp : ¬ Collinear3 0 ax p) (hncq : ¬ Collinear3 0 ax q)
    (hncr : ¬ Collinear3 0 ax r) (hncs : ¬ Collinear3 0 ax s)
    (h1 : azim 0 ax p q ≤ azim 0 ax p r)
    (h2 : azim 0 ax p r ≤ azim 0 ax p s)
    (hne : azim 0 ax p s ≠ 0) :
    azim 0 ax p q + azim 0 ax q r + azim 0 ax r s + azim 0 ax s p
      = 2 * Real.pi := by
  have hchain := pmOrthoArcChain3_p35 hax0 hncp hncq hncr hncs h1 h2
  have hcompl := azim_compl (z := (0:V3)) (w := ax) (w1 := p) (w2 := s) hncp hncs
  rw [if_neg hne] at hcompl
  rw [hcompl, hchain]
  ring

/-- (pm11) The step lower bound is unconditional: an axis-orthogonal annulus
pair at chord `>= 2` has directed azimuth at least `alpha` :=
`arccos(2719/3969)` (for azimuth beyond `pi` this is immediate). -/
private theorem pmOrthoStepGeA_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd : (2:ℝ) ≤ dist x y) :
    Real.arccos (2719 / 3969) ≤ azim 0 ax x y := by
  rcases lt_or_ge Real.pi (azim 0 ax x y) with hgt | hπ
  · have hαπ : Real.arccos (2719 / 3969) ≤ Real.pi :=
      Real.arccos_le_pi (2719 / 3969)
    linarith
  · exact pmAzimOrthoGapGe_p35 hax0 hx0 hy0 hncx hncy hXX hYY hx2 hxa hy2 hya hd
      (by linarith)

/-- (pm11) The step constant exceeds `pi/4`: since `cos(pi/4) = sqrt(2)/2 >
2719/3969` and cosine is antitone on `[0, pi]`,
`arccos(2719/3969) > pi/4`. -/
private theorem pmOrthoStepGeQuart_p35 :
    Real.pi / 4 < Real.arccos (2719 / 3969) := by
  by_contra hle
  have hαle : Real.arccos (2719 / 3969) ≤ Real.pi / 4 := by linarith
  have hmono := pmOrthoTriCosMono_p35
    (show (0:ℝ) ≤ Real.arccos (2719 / 3969) from Real.arccos_nonneg _)
    hαle (show Real.pi / 4 ≤ Real.pi from by linarith [Real.pi_pos])
  rw [pmOrthoTriCosA_p35, Real.cos_pi_div_four] at hmono
  exact absurd hmono (not_le.mpr pmOrthoSqrt2HalfBig_p35)

/-- (pm11) The far constant is below `3*pi/4`: `cos(3*pi/4) = -sqrt(2)/2 <
-10601/80000 = cos(beta)` forces `beta < 3*pi/4`. -/
private theorem pmOrthoTriBetaLt34_p35 :
    Real.arccos (-(10601 / 80000)) < 3 * Real.pi / 4 := by
  by_contra hge
  have hβge : 3 * Real.pi / 4 ≤ Real.arccos (-(10601 / 80000)) := by linarith
  have hmono := pmOrthoTriCosMono_p35
    (show (0:ℝ) ≤ 3 * Real.pi / 4 from by linarith [Real.pi_pos]) hβge
    (le_trans pmOrthoTriBetaLe_p35 (le_of_lt (by linarith [Real.pi_pos])))
  rw [pmOrthoTriCosB_p35] at hmono
  have hval : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have h34 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [h34, Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [hval] at hmono
  have hge' : (10601:ℝ) / 80000 ≥ Real.sqrt 2 / 2 := by linarith
  exact absurd hge' (not_le.mpr pmOrthoSqrt2LtA_p35)

/-- (pm11) **The step-arithmetic coupling** (chord-`2` edge): an
axis-orthogonal annulus pair at chord exactly `2` meets under an azimuth
whose cosine is at least `1/2`; with the azimuth in `[0, pi]` the step is at
most `pi/3`.  This is the `k = 6` counting feed (a `2`-`a`-conjunct edge
with realized chord pinned to its lower bound). -/
private theorem pmOrthoStepPi3_p35 {ax x y : V3} (hax0 : ax ≠ (0:V3))
    (hx0 : x ≠ (0:V3)) (hy0 : y ≠ (0:V3)) (hncx : ¬ Collinear3 0 ax x)
    (hncy : ¬ Collinear3 0 ax y)
    (hXX : (x : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hYY : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hx2 : (2:ℝ) ≤ ‖x‖) (hxa : ‖x‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hd2 : (2:ℝ) ≤ dist x y) (hdle : dist x y ≤ 2)
    (hπ : azim 0 ax x y ≤ Real.pi) :
    azim 0 ax x y ≤ Real.pi / 3 := by
  have hcos := pmAzimOrthoCos_p35 hax0 hx0 hy0 hncx hncy hXX hYY
  have hdn := pmDotNormDist_p35 x y
  rw [hdn] at hcos
  have hd2' : dist x y = 2 := le_antisymm hdle hd2
  rw [hd2'] at hcos
  have hrs0 : (0:ℝ) < ‖x‖ * ‖y‖ :=
    mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0)
  have hrssq : (0:ℝ) ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x‖ * ‖y‖ - 4 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), hx2, hy2]
  have hstep : (1:ℝ) / 2 * (‖x‖ * ‖y‖)
      ≤ Real.cos (azim 0 ax x y) * (‖x‖ * ‖y‖) := by
    rw [hcos]
    linarith
  have hkey : (1:ℝ) / 2 ≤ Real.cos (azim 0 ax x y) :=
    le_of_mul_le_mul_right hstep hrs0
  rcases lt_or_ge (azim 0 ax x y) (Real.pi / 3) with hlt | hge
  · linarith
  · rcases eq_or_lt_of_le hge with heq | hgt
    · linarith
    · exfalso
      have hmono := pmOrthoTriCosMono_p35
        (show (0:ℝ) ≤ Real.pi / 3 from by linarith [Real.pi_pos]) hgt.le hπ
      rw [pmOrthoTriCosPi3_p35] at hmono
      have heq2 : Real.cos (azim 0 ax x y) = (1:ℝ) / 2 := by linarith
      have hacos : Real.arccos (Real.cos (azim 0 ax x y)) = azim 0 ax x y :=
        Real.arccos_cos (azim_nonneg 0 ax x y) hπ
      have hp3 : Real.arccos (1 / 2) = Real.pi / 3 := by
        rw [← Real.arccos_cos (show (0:ℝ) ≤ Real.pi / 3 from by linarith [Real.pi_pos])
          (show Real.pi / 3 ≤ Real.pi from by linarith [Real.pi_pos]),
          pmOrthoTriCosPi3_p35]
      rw [← hacos, heq2, hp3] at hgt
      linarith

/-- (pm11) **The k = 6 counting conjunct** (`isScsV39` feed): with `k = 6`
the `ncard + k <= 6` conjunct is at full strength, so the big-edge set is
empty and every edge carries `a = 2` (its lower bound is tight) and
`b <= 2*h0`. -/
private theorem pmCountK6_p35 (s : ScsV39) (hscs : isScsV39 s) (hk6 : s.k = 6)
    (i : ℕ) (hi : i < 6) :
    s.a i (i + 1) = 2 ∧ s.b i (i + 1) ≤ 2 * h0 := by
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, -, -, -, -, -, hb3, -, -, -, -, hcard⟩ := hscs
  have hk4 : 4 ≤ s.k := by rw [hk6]; norm_num
  have hpos0 : (0:ℕ) < s.k :=
    Nat.lt_of_lt_of_le (show (0:ℕ) < 3 by norm_num)
      (le_trans (show (3:ℕ) ≤ 4 from by norm_num) hk4)
  have hcard' := hcard
  rw [hk6] at hcard'
  have hnc6 : {j | j < 6 ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))}.ncard = 0 := by
    omega
  have hnc0 : {j | j < s.k ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))}.ncard = 0 := by
    rw [hk6]
    exact hnc6
  have hik : i < s.k := by rw [hk6]; exact hi
  have hge : (2:ℝ) ≤ s.a i (i + 1) := by
    by_cases hlt : i + 1 < s.k
    · exact hb3 i (i + 1) ⟨hik, hlt, Nat.ne_of_lt (Nat.lt_succ_self i)⟩
    · have heq : i + 1 = s.k := by omega
      have h2 := (hpa i 0).2
      rw [Nat.zero_add] at h2
      rw [heq, h2]
      exact hb3 i 0 ⟨hik, hpos0, Nat.ne_of_gt
        (Nat.lt_of_lt_of_le (show (0:ℕ) < 3 by norm_num)
          (Nat.le_of_succ_le_succ (show 4 ≤ i + 1 from by rw [heq]; exact hk4)))⟩
  have hfin : ({j | j < s.k ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio s.k) (fun x hx => hx.1)
  have hnotin : ¬ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1)) := by
    intro hmem2
    have hpos : (0:ℕ) < {j | j < s.k ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))}.ncard :=
      (Set.ncard_pos (hs := hfin)).mpr ⟨i, hik, hmem2⟩
    rw [hnc0] at hpos
    norm_num at hpos
  have hab : ¬ (2:ℝ) < s.a i (i + 1) := fun hc => hnotin (Or.inr hc)
  have hle : s.a i (i + 1) ≤ 2 := le_of_not_gt hab
  exact ⟨le_antisymm hle hge, le_of_not_gt (fun hc => hnotin (Or.inl hc))⟩

/-- (pm11) **THE HEXAGONAL TWO-ARC SQUEEZE** (the k = 6, d = 3 core of the
d >= 3 branch): six axis-orthogonal annulus points around `ax` forming two
consecutive 3-step arcs `u -> y1 -> y2 -> w` and `w -> z1 -> z2 -> u`, with
the diagonal `u, w` at chord in `[2, cstab]` and the counterclockwise order
premises on both arcs.  The chain rule turns each arc into its azimuthal
displacement, every step is at least `alpha = arccos(2719/3969) > pi/4`, so
each displacement is at least `3*alpha > 3*pi/4 > beta`; but the far-arc
split puts at least one of the two directed azimuths (of `w, u`) on the
near arc, i.e. at most `beta` — contradiction. -/
private theorem pmOrthoHexArcKill_p35 {ax u y1 y2 w z1 z2 : V3}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hy10 : y1 ≠ (0:V3)) (hy20 : y2 ≠ (0:V3))
    (hw0 : w ≠ (0:V3)) (hz10 : z1 ≠ (0:V3)) (hz20 : z2 ≠ (0:V3))
    (hncu : ¬ Collinear3 0 ax u) (hncy1 : ¬ Collinear3 0 ax y1)
    (hncy2 : ¬ Collinear3 0 ax y2) (hncw : ¬ Collinear3 0 ax w)
    (hncz1 : ¬ Collinear3 0 ax z1) (hncz2 : ¬ Collinear3 0 ax z2)
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hY1 : (y1 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hY2 : (y2 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hZ1 : (z1 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hZ2 : (z2 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hy12 : (2:ℝ) ≤ ‖y1‖) (hy1a : ‖y1‖ ≤ 2 * h0)
    (hy22 : (2:ℝ) ≤ ‖y2‖) (hy2a : ‖y2‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (hz12 : (2:ℝ) ≤ ‖z1‖) (hz1a : ‖z1‖ ≤ 2 * h0)
    (hz22 : (2:ℝ) ≤ ‖z2‖) (hz2a : ‖z2‖ ≤ 2 * h0)
    (e1 : (2:ℝ) ≤ dist u y1) (e2 : (2:ℝ) ≤ dist y1 y2) (e3 : (2:ℝ) ≤ dist y2 w)
    (f1 : (2:ℝ) ≤ dist w z1) (f2 : (2:ℝ) ≤ dist z1 z2) (f3 : (2:ℝ) ≤ dist z2 u)
    (hd : dist u w ≤ cstab) (ed : (2:ℝ) ≤ dist u w)
    (a1 : azim 0 ax u y1 ≤ azim 0 ax u y2)
    (a2 : azim 0 ax u y2 ≤ azim 0 ax u w)
    (b1 : azim 0 ax w z1 ≤ azim 0 ax w z2)
    (b2 : azim 0 ax w z2 ≤ azim 0 ax w u) :
    False := by
  -- the far-arc split on the pair (w, u)
  have hsplit := pmOrthoTriFarSplit_p35 (x := w) (y := u) hax0 hw0 hu0 hncw hncu hW hU
    hw2 hwa hu2 hua (by rw [dist_comm]; exact hd)
  rcases hsplit with hnear | hfar
  · -- near case: the w-arc displacement is at most beta, but its three steps
    -- are each at least alpha
    have hstep1 := pmOrthoStepGeA_p35 hax0 hw0 hz10 hncw hncz1 hW hZ1 hw2 hwa hz12 hz1a f1
    have hstep2 := pmOrthoStepGeA_p35 hax0 hz10 hz20 hncz1 hncz2 hZ1 hZ2 hz12 hz1a hz22 hz2a f2
    have hstep3 := pmOrthoStepGeA_p35 hax0 hz20 hu0 hncz2 hncu hZ2 hU hz22 hz2a hu2 hua f3
    have hchain := pmOrthoArcChain3_p35 hax0 hncw hncz1 hncz2 hncu b1 b2
    rw [hchain] at hnear
    linarith [pmOrthoStepGeQuart_p35, pmOrthoTriBetaLt34_p35]
  · -- far case: azim w u >= 2*pi - beta, so azim u w <= beta; the u-arc
    -- displacement is at most beta against its three alpha steps
    have hwu0 : azim 0 ax w u ≠ 0 :=
      pmOrthoTriAzimNe0_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
        (by rw [dist_comm]; exact ed)
    have hcompl := azim_compl (z := (0:V3)) (w := ax) (w1 := w) (w2 := u) hncw hncu
    rw [if_neg hwu0] at hcompl
    have huwle : azim 0 ax u w ≤ Real.arccos (-(10601 / 80000)) := by
      rw [hcompl]
      linarith
    have hstep1 := pmOrthoStepGeA_p35 hax0 hu0 hy10 hncu hncy1 hU hY1 hu2 hua hy12 hy1a e1
    have hstep2 := pmOrthoStepGeA_p35 hax0 hy10 hy20 hncy1 hncy2 hY1 hY2 hy12 hy1a hy22 hy2a e2
    have hstep3 := pmOrthoStepGeA_p35 hax0 hy20 hw0 hncy2 hncw hY2 hW hy22 hy2a hw2 hwa e3
    have hchain := pmOrthoArcChain3_p35 hax0 hncu hncy1 hncy2 hncw a1 a2
    rw [hchain] at huwle
    linarith [pmOrthoStepGeQuart_p35, pmOrthoTriBetaLt34_p35]

-- pm11 axcheck tail (probe only; dropped from the kit proper)

/-! ## planemiss13 rungs (lkgrqui-planemiss13-w3, 2026-10-28)

The (a) branch of the winding root: the `d = 2` configuration in which the
common ring neighbour of the diagonal endpoints `u, w` sits OFF the dart
plane.  The pm9-pm11 winding account is an in-plane-pair story (an
off-plane vertex with small projection radius admits an azimuthally tiny
step at chord in `[2, cstab]`), so the off-plane branch needs the
projection-height coupling account: decompose the off-plane point along
the dart normal (`y = y' + t * ax`), read every chord to it as a
Pythagorean split between the in-plane chord of the projection `y'` and
the squared height `t ^ 2 * ‖ax‖ ^ 2`, and squeeze the height between the
double annulus chord and the ring diagonal (`t ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2
- dist u w ^ 2 / 4`, in particular `≤ cstab ^ 2 - 1`).  The kit is FAN-free
conditional (the assembly lane feeds the ring bookkeeping and the axis):
the cosine-window pair `pmOrthoOffDotGe/Le_p35` packages the degraded
azimuth interface for the projection (law-of-cosines bounds shifted by the
squared height), and the `k = 4` pieces close the abstract residue
trichotomy: in a 4-periodic ring the dart pair contains the residue-3
vertex once the residue-1 vertex is off the axis plane
(`pmOrthoOffFourthOrtho_p35`), so the forced in-plane fourth vertex hands
the configuration to the pm10 in-plane triple kill
(`pmOrthoOffK4Kill_p35`, both cases).  All pieces are new lemmas with zero
`sorry`; the residual root `pmPlaneCrowding_p35` is untouched. -/

/-- (pm13) dot-product self-expansion for a one-dimensional split. -/
private theorem pmDotSelfAdd_p35 (p q : Fin 3 → ℝ) (t : ℝ) :
    (p + t • q) ⬝ᵥ (p + t • q)
      = p ⬝ᵥ p + 2 * t * (p ⬝ᵥ q) + t ^ 2 * (q ⬝ᵥ q) := by
  rw [pmDotAddL_p35, pmDotAddR_p35, pmDotAddR_p35, pmDotSmulL_p35, pmDotSmulR_p35,
    pmDotSmulL_p35, pmDotSmulR_p35, dotProduct_comm q p]
  ring

/-- (pm13) **Pythagoras, norm form**: splitting `y = y' + t * ax` with the
first summand axis-orthogonal splits the squared norm into the projection
squared norm plus the squared height `t ^ 2 * ‖ax‖ ^ 2`. -/
private theorem pmOrthoPythNorm_p35 {ax y y' : V3} {t : ℝ}
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    ‖y‖ ^ 2 = ‖y'‖ ^ 2 + t ^ 2 * ‖ax‖ ^ 2 := by
  have hcoe : ((y' + t • ax : V3) : Fin 3 → ℝ)
      = (y' : Fin 3 → ℝ) + t • (ax : Fin 3 → ℝ) := rfl
  rw [pmNormSqDot_p35 y, pmNormSqDot_p35 y', pmNormSqDot_p35 ax, hy, hcoe,
    pmDotSelfAdd_p35 (y' : Fin 3 → ℝ) (ax : Fin 3 → ℝ) t, hyo]
  ring

/-- (pm13) **Pythagoras, chord form**: for an axis-orthogonal base point
`u`, the chord to `y` splits into the chord of the projection `y'` plus
the squared height.  This is the master identity of the off-plane
coupling account. -/
private theorem pmOrthoPythDist_p35 {ax u y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    dist u y ^ 2 = dist u y' ^ 2 + t ^ 2 * ‖ax‖ ^ 2 := by
  have hdy := pmDotNormDist_p35 u y
  have hdy' := pmDotNormDist_p35 u y'
  have hcoe : ((y' + t • ax : V3) : Fin 3 → ℝ)
      = (y' : Fin 3 → ℝ) + t • (ax : Fin 3 → ℝ) := rfl
  have hdot : ((u : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ))
      = ((u : Fin 3 → ℝ) ⬝ᵥ (y' : Fin 3 → ℝ)) := by
    rw [hy, hcoe, pmDotAddR_p35, pmDotSmulR_p35,
      dotProduct_comm (ax : Fin 3 → ℝ) (u : Fin 3 → ℝ), hU, mul_zero, add_zero]
  have hny := pmOrthoPythNorm_p35 hy hyo
  linarith

/-- (pm13) **The general projection witness** (orthogonality): with the
scalar `c` cancelling the axis component (`y*ax - c * ax*ax = 0`) the
vector `y - c * ax` is axis-orthogonal. -/
private theorem pmOrthoProjGenOrtho_p35 {ax y : V3} {c : ℝ}
    (hc : (y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)
        - c * ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) = 0) :
    (((y - c • ax : V3) : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) = 0 := by
  have hcoe : ((y - c • ax : V3) : Fin 3 → ℝ)
      = (y : Fin 3 → ℝ) - c • (ax : Fin 3 → ℝ) := rfl
  rw [hcoe, sub_eq_add_neg, ← neg_smul, pmDotAddL_p35, pmDotSmulL_p35]
  linear_combination hc

/-- (pm13) **The explicit projection** is axis-orthogonal: for `ax ≠ 0`
the vector `y - (y*ax / ax*ax) * ax` cancels the axis component. -/
private theorem pmOrthoProjOrthoC_p35 {ax y : V3} (hax0 : ax ≠ (0:V3)) :
    (((y - ((y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) /
        ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ))) • ax : V3) : Fin 3 → ℝ) ⬝ᵥ
      (ax : Fin 3 → ℝ)) = 0 := by
  have haxne : ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) ≠ 0 := by
    rw [← pmNormSqDot_p35 ax]
    exact pow_ne_zero 2 (ne_of_gt (norm_pos_iff.mpr hax0))
  apply pmOrthoProjGenOrtho_p35
  field_simp
  ring

/-- (pm13) **The explicit projection decomposition**: `y` is the sum of
its axis-orthogonal projection and the axis component. -/
private theorem pmOrthoProjRepr_p35 {ax y : V3} :
    y = (y - ((y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) /
        ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ))) • ax)
      + ((y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) /
        ((ax : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ))) • ax := by
  rw [sub_add_cancel]

/-- (pm13) **THE HEIGHT CEILING** (the projection-height coupling): if the
chords from an axis-orthogonal pair `u, w` down to `y` are both at most
`cstab`, the squared height `t ^ 2 * ‖ax‖ ^ 2` is at most
`cstab ^ 2 - dist u w ^ 2 / 4` — the in-plane triangle inequality through
the projection with the Cauchy bound `(a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)`.
Assembly feeds `2 ≤ dist u w` (the ring-diagonal `a`-conjunct) into the
corollary `pmOrthoOffHeightSqLeOne_p35`. -/
private theorem pmOrthoOffHeightSqLe_p35 {ax u w y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (huy : dist u y ≤ cstab) (hwy : dist w y ≤ cstab) :
    t ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2 - dist u w ^ 2 / 4 := by
  have hdu : dist u y ^ 2 = dist u y' ^ 2 + t ^ 2 * ‖ax‖ ^ 2 :=
    pmOrthoPythDist_p35 hU hy hyo
  have hdw : dist w y ^ 2 = dist w y' ^ 2 + t ^ 2 * ‖ax‖ ^ 2 :=
    pmOrthoPythDist_p35 hW hy hyo
  have hsqc : t ^ 2 * ‖ax‖ ^ 2 = (t * ‖ax‖) ^ 2 := by ring
  have hsnn := sq_nonneg (t * ‖ax‖)
  have hu : dist u y' ^ 2 ≤ cstab ^ 2 - t ^ 2 * ‖ax‖ ^ 2 := by
    have h1 : dist u y ^ 2 ≤ cstab ^ 2 :=
      pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist u y) huy 2
    linarith
  have hw : dist w y' ^ 2 ≤ cstab ^ 2 - t ^ 2 * ‖ax‖ ^ 2 := by
    have h1 : dist w y ^ 2 ≤ cstab ^ 2 :=
      pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist w y) hwy 2
    linarith
  have hdw' : dist w y' = dist y' w := dist_comm w y'
  rw [hdw'] at hw
  have htri : dist u w ≤ dist u y' + dist y' w := dist_triangle u y' w
  have htri2 : dist u w ^ 2 ≤ (dist u y' + dist y' w) ^ 2 :=
    pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist u w) htri 2
  have hcauchy : (dist u y' + dist y' w) ^ 2
      ≤ 2 * (dist u y' ^ 2 + dist y' w ^ 2) := by
    have h1 := sq_nonneg (dist u y' - dist y' w)
    nlinarith
  linarith

/-- (pm13) **Height ceiling, numeric form**: with the ring diagonal at
least `2` (the `isScsV39` `a`-conjunct at distinct residues), the squared
height is at most `cstab ^ 2 - 1 ≈ 8.06`, i.e. the height itself is below
`2.84`: an off-plane ring vertex sits only shallowly above the dart
plane. -/
private theorem pmOrthoOffHeightSqLeOne_p35 {ax u w y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (huy : dist u y ≤ cstab) (hwy : dist w y ≤ cstab)
    (h2 : (2:ℝ) ≤ dist u w) :
    t ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2 - 1 := by
  have h := pmOrthoOffHeightSqLe_p35 hU hW hy hyo huy hwy
  have h4 : (2:ℝ) ^ 2 ≤ dist u w ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
  norm_num at h4
  linarith

/-- (pm13) **Projected chord upper window**: the projection inherits the
far bound — a chord of at most `cstab` to the lifted point projects to a
chord of at most `cstab`. -/
private theorem pmOrthoOffProjChordLe_p35 {ax u y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (huy : dist u y ≤ cstab) : dist u y' ≤ cstab := by
  have hdu := pmOrthoPythDist_p35 hU hy hyo
  have hsqc : t ^ 2 * ‖ax‖ ^ 2 = (t * ‖ax‖) ^ 2 := by ring
  have h1 : dist u y ^ 2 ≤ cstab ^ 2 :=
    pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist u y) huy 2
  have hsq : dist u y' ^ 2 ≤ cstab ^ 2 := by
    linarith [hdu, h1, hsqc, sq_nonneg (t * ‖ax‖)]
  by_contra hcon
  have hgt : cstab < dist u y' := not_le.mp hcon
  have hc0 : (0:ℝ) ≤ cstab := le_of_lt (by norm_num [cstab])
  have hlt : cstab ^ 2 < dist u y' ^ 2 :=
    (sq_lt_sq₀ hc0 (by simp)).mpr hgt
  linarith

/-- (pm13) **Projected chord lower window**: a chord of at least `2` to
the lifted point leaves the projected chord squared at least `4 - h²` —
the height deficit is exactly what the winding account must absorb. -/
private theorem pmOrthoOffProjChordSqGe_p35 {ax u y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hge : (2:ℝ) ≤ dist u y) :
    (4:ℝ) ≤ dist u y' ^ 2 + t ^ 2 * ‖ax‖ ^ 2 := by
  have hdu := pmOrthoPythDist_p35 hU hy hyo
  have h1 : (2:ℝ) ^ 2 ≤ dist u y ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
  norm_num at h1
  linarith

/-- (pm13) **Projected norm window, lower**: a lifted annulus point
(`‖y‖ ≥ 2`) has projected norm squared at least `4 - h²`. -/
private theorem pmOrthoOffProjNormSqGe_p35 {ax y y' : V3} {t : ℝ}
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hge : (2:ℝ) ≤ ‖y‖) :
    (4:ℝ) ≤ ‖y'‖ ^ 2 + t ^ 2 * ‖ax‖ ^ 2 := by
  have hny := pmOrthoPythNorm_p35 hy hyo
  have h1 : (2:ℝ) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
  norm_num at h1
  linarith

/-- (pm13) **Projected norm window, upper**: the projection never
increases the norm (`‖y'‖ ≤ ‖y‖`). -/
private theorem pmOrthoOffProjNormLe_p35 {ax y y' : V3} {t : ℝ}
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    ‖y'‖ ≤ ‖y‖ := by
  have hny := pmOrthoPythNorm_p35 hy hyo
  have hsqc : t ^ 2 * ‖ax‖ ^ 2 = (t * ‖ax‖) ^ 2 := by ring
  have hsqle : ‖y'‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    linarith [hny, hsqc, sq_nonneg (t * ‖ax‖)]
  by_contra hcon
  have hlt : ‖y‖ < ‖y'‖ := not_le.mp hcon
  have hlt2 : ‖y‖ ^ 2 < ‖y'‖ ^ 2 := by
    nlinarith [hlt, norm_nonneg y', norm_nonneg y]
  linarith

/-- (pm13) **Cosine window, lower** (the degraded azimuth interface): the
projection dot product is at least the law-of-cosines lower bound shifted
by the squared height — `‖u‖ ^ 2 + ‖y'‖ ^ 2 - cstab ^ 2 + h² ≤ 2 * u*y'`.
Assembly converts to an azimuth window through `pmAzimOrthoCos_p35` when
the projection is nonzero and axis-plane-positioned. -/
private theorem pmOrthoOffDotGe_p35 {ax u y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (huy : dist u y ≤ cstab) :
    ‖u‖ ^ 2 + ‖y'‖ ^ 2 - cstab ^ 2 + t ^ 2 * ‖ax‖ ^ 2
      ≤ 2 * ((u : Fin 3 → ℝ) ⬝ᵥ (y' : Fin 3 → ℝ)) := by
  have hdy' := pmDotNormDist_p35 u y'
  have hdu := pmOrthoPythDist_p35 hU hy hyo
  have h1 : dist u y ^ 2 ≤ cstab ^ 2 :=
    pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist u y) huy 2
  linarith

/-- (pm13) **Cosine window, upper**: the chord lower bound `2` caps the
projection dot product — `2 * u*y' ≤ ‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + h²`.  The
pair with `pmOrthoOffDotGe_p35` is the (a)-branch feed for the winding
account: the height term `h²` widens the window exactly by the amount the
lifted chord exceeds its in-plane shadow. -/
private theorem pmOrthoOffDotLe_p35 {ax u y y' : V3} {t : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hge : (2:ℝ) ≤ dist u y) :
    2 * ((u : Fin 3 → ℝ) ⬝ᵥ (y' : Fin 3 → ℝ))
      ≤ ‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + t ^ 2 * ‖ax‖ ^ 2 := by
  have hdy' := pmDotNormDist_p35 u y'
  have hdu := pmOrthoPythDist_p35 hU hy hyo
  have h1 : (2:ℝ) ^ 2 ≤ dist u y ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
  norm_num at h1
  linarith

/-- (pm13) **THE `k = 4`, `d = 2` KILL** (abstract form): four annulus
points `u → y → w → x2` around the axis, every ring chord in
`[2, cstab]`, the diagonal `u, w` in the axis plane with the diagonal
chord in `[2, cstab]` — then `False`.  Either `y` is in the axis plane
too and `u, y, w` is an in-plane triple at pairwise chords in
`[2, cstab]` (the pm10 kill), or `y` is off the plane and the forced
fourth vertex `x2` provides the in-plane triple `u, w, x2`.  Assembly
supplies `x2 ∈` axis plane through the forcing lemma
`pmOrthoOffFourthOrtho_p35` below; all non-collinearity premises are
derived in-body from the orthogonality data (`pmAxisOrthoNC_p35`). -/
private theorem pmOrthoOffK4Kill_p35 {ax u w x2 y : V3} (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3)) (hx20 : x2 ≠ (0:V3)) (hy0 : y ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hX2 : (x2 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (hy2 : (2:ℝ) ≤ ‖y‖) (hya : ‖y‖ ≤ 2 * h0)
    (hx22 : (2:ℝ) ≤ ‖x2‖) (hx2a : ‖x2‖ ≤ 2 * h0)
    (huy : dist u y ≤ cstab) (hyw : dist y w ≤ cstab)
    (hwx2 : dist w x2 ≤ cstab) (hx2u : dist x2 u ≤ cstab)
    (hdiag : dist u w ≤ cstab)
    (euy : (2:ℝ) ≤ dist u y) (eyw : (2:ℝ) ≤ dist y w)
    (ewx2 : (2:ℝ) ≤ dist w x2) (ex2u : (2:ℝ) ≤ dist x2 u)
    (ed : (2:ℝ) ≤ dist u w) :
    False := by
  by_cases hY : ((y : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
  · -- y in the axis plane: the triple `u, y, w` dies by the pm10 kill
    have hncy : ¬ Collinear3 0 ax y := pmAxisOrthoNC_p35 hax0 hy0 hY
    have hncu : ¬ Collinear3 0 ax u := pmAxisOrthoNC_p35 hax0 hu0 hU
    have hncw : ¬ Collinear3 0 ax w := pmAxisOrthoNC_p35 hax0 hw0 hW
    exact pmOrthoTriCstabKill_p35 hax0 hu0 hy0 hw0 hncu hncy hncw hU hY hW
      hu2 hua hy2 hya hw2 hwa huy hyw (by rw [dist_comm]; exact hdiag)
      euy eyw (by rw [dist_comm]; exact ed)
  · -- y off the axis plane: the forced fourth vertex `x2` dies instead
    have hncu : ¬ Collinear3 0 ax u := pmAxisOrthoNC_p35 hax0 hu0 hU
    have hncw : ¬ Collinear3 0 ax w := pmAxisOrthoNC_p35 hax0 hw0 hW
    have hncx2 : ¬ Collinear3 0 ax x2 := pmAxisOrthoNC_p35 hax0 hx20 hX2
    exact pmOrthoTriCstabKill_p35 hax0 hu0 hw0 hx20 hncu hncw hncx2 hU hW hX2
      hu2 hua hw2 hwa hx22 hx2a hdiag hwx2 hx2u ed ewx2 ex2u

/-- (pm13) **Periodic shift**: a `k`-periodic ring can be shifted by
whole periods freely. -/
private theorem pmOrthoPeriodicShift_p35 {vv : ℕ → V3} {k : ℕ}
    (hper : Periodic vv k) (m n : ℕ) : vv (m + k * n) = vv m := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hstep : m + k * (n + 1) = (m + k * n) + k := by ring
    rw [hstep, hper, ih]

/-- (pm13) **The `k = 4` residue trichotomy** (the forcing interface): in
a 4-periodic ring, every dart pair `(vv j, vv (j+1))` is one of the four
consecutive residue pairs — so the dart-`j` plane always misses exactly
the two residues opposite `j`. -/
private theorem pmOrthoK4Cases_p35 {vv : ℕ → V3} (hper : Periodic vv 4)
    (j : ℕ) :
    (vv j = vv 0 ∧ vv (j + 1) = vv 1) ∨
    (vv j = vv 1 ∧ vv (j + 1) = vv 2) ∨
    (vv j = vv 2 ∧ vv (j + 1) = vv 3) ∨
    (vv j = vv 3 ∧ vv (j + 1) = vv 0) := by
  have hmod : j = j % 4 + 4 * (j / 4) := by
    have h := Nat.mod_add_div' j 4
    rw [Nat.mul_comm (j / 4) 4] at h
    exact h.symm
  have hvj : vv j = vv (j % 4) := by
    have h := pmOrthoPeriodicShift_p35 hper (j % 4) (j / 4)
    conv_lhs => rw [hmod]
    exact h
  have hvj1 : vv (j + 1) = vv (j % 4 + 1) := by
    have h := pmOrthoPeriodicShift_p35 hper (j % 4 + 1) (j / 4)
    have he : j + 1 = j % 4 + 1 + 4 * (j / 4) := by
      conv_lhs => rw [hmod]
      ring
    rw [he]
    exact h
  have h4 : j % 4 < 4 := Nat.mod_lt j (by norm_num)
  rcases Nat.lt_or_ge (j % 4) 2 with h2 | h2
  · rcases Nat.lt_or_ge (j % 4) 1 with h1 | h1
    · have hz : j % 4 = 0 := Nat.lt_one_iff.mp h1
      exact Or.inl ⟨by rw [hvj, hz], by rw [hvj1, hz]⟩
    · have hz : j % 4 = 1 := Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h1
      exact Or.inr (Or.inl ⟨by rw [hvj, hz], by rw [hvj1, hz]⟩)
  · rcases Nat.lt_or_ge (j % 4) 3 with h3 | h3
    · have hz : j % 4 = 2 := Nat.le_antisymm (Nat.lt_succ_iff.mp h3) h2
      exact Or.inr (Or.inr (Or.inl ⟨by rw [hvj, hz], by rw [hvj1, hz]⟩))
    · have hz : j % 4 = 3 := Nat.le_antisymm (Nat.lt_succ_iff.mp h4) h3
      refine Or.inr (Or.inr (Or.inr ⟨by rw [hvj, hz], ?_⟩))
      rw [hvj1, hz]
      exact hper 0

/-- (pm13) **The off-plane fourth-vertex forcing** (`k = 4`): in a
4-periodic ring, if both endpoints of the dart `j` lie in the axis plane
while the residue-1 vertex does not, then the residue-3 vertex is dragged
into the axis plane — the dart pair must avoid residue 1 (else one of its
members is `vv 1` against `hy1`), hence it contains residue 3 either way.
Assembly reindexes `u ↦ vv 0`, the off-plane common neighbour `x₁ ↦ vv 1`,
`w ↦ vv 2`, the forced fourth vertex `x₂ ↦ vv 3` by periodicity; the
output feeds `pmOrthoOffK4Kill_p35`. -/
private theorem pmOrthoOffFourthOrtho_p35 {vv : ℕ → V3} {ax : V3}
    (hper : Periodic vv 4) (j : ℕ)
    (hjP : (vv j : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hjp1P : (vv (j + 1) : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : ¬ ((vv 1 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)) :
    (vv 3 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0 := by
  rcases pmOrthoK4Cases_p35 hper j with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
      ⟨e1, e2⟩
  · rw [e2] at hjp1P
    exact absurd hjp1P hy1
  · rw [e1] at hjP
    exact absurd hjP hy1
  · rw [e2] at hjp1P
    exact hjp1P
  · rw [e1] at hjP
    exact hjP
/-! ## planemiss14 rungs (lkgrqui-planemiss14-w3, 2026-10-28)

The (iii) branch of the winding root: the OFF-PLANE INTERMEDIATE POINT
account — the two-point sister block of the pm13 (a) branch.  pm13
couples ONE lifted point to the in-plane diagonal pair (the master
identity `pmOrthoPythDist_p35`, the height ceiling, the shifted cosine
windows); this block couples a PAIR of lifted points to each other and
converts every window into the winding engine's currency (an azimuth
with an `arccos` window), which is the interface the assembly consumes
on every `d >= 3` arc that carries an off-plane intermediate vertex:
the two-point height split `pmOrthoOffTwoPythDist_p35`
(`dist y1 y2 ^ 2 = dist y1' y2' ^ 2 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2`, the
single-point master is the `t2 = 0` special case), the shifted window
pair `pmOrthoOffTwoDotGe/Le_p35` (the shift is the squared height
DIFFERENCE), the equal-height corollary
`pmOrthoOffTwoEqHeightChord_p35` (a same-height run projects
isometrically along itself), the clean far window
`pmOrthoOffAzimWindowFar_p35` (an axis-orthogonal pair at chord
`<= cstab` meets under `azim <= arccos((‖p‖² + ‖q‖² - cstab²)/
(2 ‖p‖ ‖q‖))` — exact norms, no annulus data), the near windows
`pmOrthoOffStepAzimGe_p35` / `pmOrthoOffTwoStepAzimGe_p35` (the
chord-`2` bound on the LIFTED chord shifts the lower window by the
squared height resp. the squared height difference), and the capstone
`pmOrthoOffMidArcWindows_p35` packaging the full `d = 3`
intermediate-arc data: the chain displacement through the two
projections plus all six windows (three steps, near and far).  The
honest content of the pm9 finding (an off-plane vertex admits
azimuthally tiny steps) is that the step bound degrades through
`‖y'‖` and `h²` — the windows stay sharp; the kill itself still needs
the direction feed, the k ∈ {5, 6} gap account and the wrap
`Σ = 2π` assembly.  All pieces are new lemmas with zero `sorry`; the
residual root `pmPlaneCrowding_p35` is untouched. -/

/-- (pm14) division bridge for the window fractions: the projected
cosine bounds come out half-cross-multiplied, the `arccos` windows need
them divided by the norm product. -/
private theorem pmOrthoOffDivBridge_p35 (B D : ℝ) (hD : D ≠ 0) :
    B / (2 * D) * D = B / 2 := by
  field_simp

/-- (pm14) `arccos` closing wrapper, near form: a cosine upper bound on
an azimuth in `[0, π]` lifts to the `arccos` floor window. -/
private theorem pmOrthoOffAzimGeOfCosLe_p35 {ax p q : V3} {c : ℝ}
    (hπ : azim 0 ax p q ≤ Real.pi)
    (h : Real.cos (azim 0 ax p q) ≤ c) :
    Real.arccos c ≤ azim 0 ax p q := by
  have h2 : Real.arccos (Real.cos (azim 0 ax p q)) = azim 0 ax p q :=
    Real.arccos_cos (azim_nonneg 0 ax p q) hπ
  rw [← h2]
  exact Real.arccos_le_arccos h

/-- (pm14) `arccos` closing wrapper, far form: a cosine lower bound on
an azimuth in `[0, π]` lifts to the `arccos` cap window. -/
private theorem pmOrthoOffAzimLeOfCosGe_p35 {ax p q : V3} {c : ℝ}
    (hπ : azim 0 ax p q ≤ Real.pi)
    (h : c ≤ Real.cos (azim 0 ax p q)) :
    azim 0 ax p q ≤ Real.arccos c := by
  have h2 : Real.arccos (Real.cos (azim 0 ax p q)) = azim 0 ax p q :=
    Real.arccos_cos (azim_nonneg 0 ax p q) hπ
  rw [← h2]
  exact Real.arccos_le_arccos h

/-- (pm14) **Two-point height split** (the pair master identity): two
lifted points split their chord into the chord of the projections plus
the squared height DIFFERENCE.  The single-point master
`pmOrthoPythDist_p35` is the `t2 = 0` special case read at the base
point. -/
private theorem pmOrthoOffTwoPythDist_p35 {ax y1 y2 y1' y2' : V3} {t1 t2 : ℝ}
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    dist y1 y2 ^ 2 = dist y1' y2' ^ 2 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2 := by
  have hdiff : y1 - y2 = (y1' - y2') + (t1 - t2) • ax := by
    rw [hy1, hy2]
    module
  have hcoeD : ((y1' - y2' : V3) : Fin 3 → ℝ)
      = (y1' : Fin 3 → ℝ) - (y2' : Fin 3 → ℝ) := rfl
  have hdo : ((y1' - y2' : V3) : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0 := by
    rw [hcoeD, sub_eq_add_neg, pmDotAddL_p35, pmDotNegL_p35, hy1o, hy2o]
    ring
  have hn := pmOrthoPythNorm_p35 (ax := ax) (y := y1 - y2)
    (y' := (y1' - y2' : V3)) (t := t1 - t2) hdiff hdo
  have hd1 : dist y1 y2 = ‖y1 - y2‖ := dist_eq_norm y1 y2
  have hd2 : dist y1' y2' = ‖y1' - y2'‖ := dist_eq_norm y1' y2'
  rw [hd1, hd2]
  exact hn

/-- (pm14) **Two-point cosine window, far**: a chord of at most
`cstab` between two lifted points bounds the projection dot product
from below — the pm13 single-point window with the height DIFFERENCE
as the shift. -/
private theorem pmOrthoOffTwoDotGe_p35 {ax y1 y2 y1' y2' : V3} {t1 t2 : ℝ}
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hd : dist y1 y2 ≤ cstab) :
    ‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - cstab ^ 2 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2
      ≤ 2 * ((y1' : Fin 3 → ℝ) ⬝ᵥ (y2' : Fin 3 → ℝ)) := by
  have hsplit := pmOrthoOffTwoPythDist_p35 hy1 hy1o hy2 hy2o
  have hwin := pmDotNormDist_p35 y1' y2'
  have h1 : dist y1 y2 ^ 2 ≤ cstab ^ 2 :=
    pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist y1 y2) hd 2
  linarith

/-- (pm14) **Two-point cosine window, near**: a chord of at least `2`
between two lifted points caps the projection dot product — the
height-difference deficit is what the winding account absorbs. -/
private theorem pmOrthoOffTwoDotLe_p35 {ax y1 y2 y1' y2' : V3} {t1 t2 : ℝ}
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hge : (2:ℝ) ≤ dist y1 y2) :
    2 * ((y1' : Fin 3 → ℝ) ⬝ᵥ (y2' : Fin 3 → ℝ))
      ≤ ‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2 := by
  have hsplit := pmOrthoOffTwoPythDist_p35 hy1 hy1o hy2 hy2o
  have hwin := pmDotNormDist_p35 y1' y2'
  have h1 : (2:ℝ) ^ 2 ≤ dist y1 y2 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hge 2
  norm_num at h1
  linarith

/-- (pm14) **Equal-height chord preservation**: two lifted points at
the SAME height project isometrically — a same-height run of ring
vertices keeps its internal chords exactly under the projection. -/
private theorem pmOrthoOffTwoEqHeightChord_p35 {ax y1 y2 y1' y2' : V3} {t : ℝ}
    (hy1 : y1 = y1' + t • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t • ax)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0) :
    dist y1 y2 = dist y1' y2' := by
  have hsplit := pmOrthoOffTwoPythDist_p35 hy1 hy1o hy2 hy2o
  norm_num at hsplit
  rcases lt_or_ge (dist y1 y2) (dist y1' y2') with hlt | hge
  · have hlt2 : dist y1 y2 ^ 2 < dist y1' y2' ^ 2 :=
      (sq_lt_sq₀ (by simp : (0:ℝ) ≤ dist y1 y2)
        (by simp : (0:ℝ) ≤ dist y1' y2')).mpr hlt
    linarith
  · have hge2 : dist y1' y2' ^ 2 ≤ dist y1 y2 ^ 2 :=
      pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist y1' y2') hge 2
    linarith

/-- (pm14) **The clean far window**: ANY axis-orthogonal pair at chord
`<= cstab` meets under an azimuth capped by the exact-norm `arccos`
fraction — no annulus data needed (the in-stack far windows pin the
constants `2719/3969` and `−10601/80000` through the annulus bounds;
this form keeps the norms free for the projected pairs whose norms are
not annulus bounds). -/
private theorem pmOrthoOffAzimWindowFar_p35 {ax p q : V3} (hax0 : ax ≠ (0:V3))
    (hp0 : p ≠ (0:V3)) (hq0 : q ≠ (0:V3))
    (hP : (p : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hQ : (q : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hd : dist p q ≤ cstab)
    (hπ : azim 0 ax p q ≤ Real.pi) :
    azim 0 ax p q
      ≤ Real.arccos ((‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2) / (2 * (‖p‖ * ‖q‖))) := by
  have hncp := pmAxisOrthoNC_p35 hax0 hp0 hP
  have hncq := pmAxisOrthoNC_p35 hax0 hq0 hQ
  have hcos := pmAzimOrthoCos_p35 hax0 hp0 hq0 hncp hncq hP hQ
  have hdot := pmDotNormDist_p35 p q
  have hstep : (‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2) / 2
      ≤ Real.cos (azim 0 ax p q) * (‖p‖ * ‖q‖) := by
    rw [hcos, hdot]
    have h1 : dist p q ^ 2 ≤ cstab ^ 2 :=
      pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist p q) hd 2
    linarith
  have hd0 : (‖p‖ * ‖q‖ : ℝ) ≠ 0 := ne_of_gt
    (mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hq0))
  have hkey : (‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2) / (2 * (‖p‖ * ‖q‖))
      ≤ Real.cos (azim 0 ax p q) := by
    have h2 := pmOrthoOffDivBridge_p35 (‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2)
      (‖p‖ * ‖q‖) hd0
    exact le_of_mul_le_mul_right (by rw [h2]; exact hstep)
      (mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hq0))
  exact pmOrthoOffAzimLeOfCosGe_p35 hπ hkey

/-- (pm14) **The lifted-step near window**: the chord-`2` bound on the
LIFTED chord `dist u y` shifts the lower `arccos` window of the
projected azimuth by the squared height `t ^ 2 * ‖ax‖ ^ 2`.  This is
the azimuth-form twin of the pm13 dot window `pmOrthoOffDotLe_p35`. -/
private theorem pmOrthoOffStepAzimGe_p35 {ax u y y' : V3} {t : ℝ}
    (hax0 : ax ≠ (0:V3)) (hu0 : u ≠ (0:V3)) (hy0 : y' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hyo : (y' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy : y = y' + t • ax)
    (hge : (2:ℝ) ≤ dist u y)
    (hπ : azim 0 ax u y' ≤ Real.pi) :
    Real.arccos ((‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + t ^ 2 * ‖ax‖ ^ 2)
        / (2 * (‖u‖ * ‖y'‖))) ≤ azim 0 ax u y' := by
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncy := pmAxisOrthoNC_p35 hax0 hy0 hyo
  have hcos := pmAzimOrthoCos_p35 hax0 hu0 hy0 hncu hncy hU hyo
  have hwin := pmOrthoOffDotLe_p35 hU hy hyo hge
  have hstep : Real.cos (azim 0 ax u y') * (‖u‖ * ‖y'‖)
      ≤ (‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + t ^ 2 * ‖ax‖ ^ 2) / 2 := by
    rw [hcos]; linarith
  have hd0 : (‖u‖ * ‖y'‖ : ℝ) ≠ 0 := ne_of_gt
    (mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hy0))
  have hkey : Real.cos (azim 0 ax u y')
      ≤ (‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + t ^ 2 * ‖ax‖ ^ 2) / (2 * (‖u‖ * ‖y'‖)) := by
    have h2 := pmOrthoOffDivBridge_p35
      (‖u‖ ^ 2 + ‖y'‖ ^ 2 - 4 + t ^ 2 * ‖ax‖ ^ 2) (‖u‖ * ‖y'‖) hd0
    exact le_of_mul_le_mul_right (by rw [h2]; exact hstep)
      (mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hy0))
  exact pmOrthoOffAzimGeOfCosLe_p35 hπ hkey

/-- (pm14) **The lifted-pair near window**: the chord-`2` bound on the
lifted pair chord shifts the lower `arccos` window of the projected
azimuth by the squared height DIFFERENCE `(t1 - t2) ^ 2 * ‖ax‖ ^ 2`. -/
private theorem pmOrthoOffTwoStepAzimGe_p35 {ax y1 y2 y1' y2' : V3} {t1 t2 : ℝ}
    (hax0 : ax ≠ (0:V3)) (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3))
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy2 : y2 = y2' + t2 • ax)
    (hge : (2:ℝ) ≤ dist y1 y2)
    (hπ : azim 0 ax y1' y2' ≤ Real.pi) :
    Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2)
        / (2 * (‖y1'‖ * ‖y2'‖))) ≤ azim 0 ax y1' y2' := by
  have hncy1 := pmAxisOrthoNC_p35 hax0 hy10 hy1o
  have hncy2 := pmAxisOrthoNC_p35 hax0 hy20 hy2o
  have hcos := pmAzimOrthoCos_p35 hax0 hy10 hy20 hncy1 hncy2 hy1o hy2o
  have hwin := pmOrthoOffTwoDotLe_p35 hy1 hy1o hy2 hy2o hge
  have hstep : Real.cos (azim 0 ax y1' y2') * (‖y1'‖ * ‖y2'‖)
      ≤ (‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2) / 2 := by
    rw [hcos]; linarith
  have hd0 : (‖y1'‖ * ‖y2'‖ : ℝ) ≠ 0 := ne_of_gt
    (mul_pos (norm_pos_iff.mpr hy10) (norm_pos_iff.mpr hy20))
  have hkey : Real.cos (azim 0 ax y1' y2')
      ≤ (‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2)
        / (2 * (‖y1'‖ * ‖y2'‖)) := by
    have h2 := pmOrthoOffDivBridge_p35
      (‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2)
      (‖y1'‖ * ‖y2'‖) hd0
    exact le_of_mul_le_mul_right (by rw [h2]; exact hstep)
      (mul_pos (norm_pos_iff.mpr hy10) (norm_pos_iff.mpr hy20))
  exact pmOrthoOffAzimGeOfCosLe_p35 hπ hkey

/-- (pm14) **THE INTERMEDIATE-ARC WINDOW PACKAGE** (the (iii) capstone):
the full `d = 3` arc `u → y1 → y2 → w` with the diagonal endpoints
`u, w` in the axis plane, both intermediate points lifted
(`y1 = y1' + t1 • ax`, `y2 = y2' + t2 • ax`), the three consecutive
chords in `[2, cstab]`, the direction-feed order premises on the
projected azimuths — packages the chain displacement
`azim u w = azim u y1' + azim y1' y2' + azim y2' w` together with ALL
SIX windows: each projected step is capped by the clean far window
(the chord bound inherits through the projection) and floored by the
height-shifted near window (the chord-`2` bound on the LIFTED chord
shifts by `t ^ 2 * ‖ax‖ ^ 2` resp. the difference shift).  This is the
single call the winding assembly makes per intermediate arc; the
remaining kill (radius-dependent window squeeze, `k ∈ {5, 6}` gap,
wrap `Σ = 2π`) is the next lane's input. -/
private theorem pmOrthoOffMidArcWindows_p35 {ax u w y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab)
    (e3 : dist y2 w ≤ cstab)
    (f1 : (2:ℝ) ≤ dist u y1) (f2 : (2:ℝ) ≤ dist y1 y2)
    (f3 : (2:ℝ) ≤ dist y2 w)
    (h1 : azim 0 ax u y1' ≤ azim 0 ax u y2')
    (h2 : azim 0 ax u y2' ≤ azim 0 ax u w)
    (hp1 : azim 0 ax u y1' ≤ Real.pi) (hp2 : azim 0 ax y1' y2' ≤ Real.pi)
    (hp3 : azim 0 ax y2' w ≤ Real.pi) :
    azim 0 ax u w
      = azim 0 ax u y1' + azim 0 ax y1' y2' + azim 0 ax y2' w
    ∧ azim 0 ax u y1'
        ≤ Real.arccos ((‖u‖ ^ 2 + ‖y1'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖u‖ * ‖y1'‖)))
    ∧ Real.arccos ((‖u‖ ^ 2 + ‖y1'‖ ^ 2 - 4 + t1 ^ 2 * ‖ax‖ ^ 2)
          / (2 * (‖u‖ * ‖y1'‖))) ≤ azim 0 ax u y1'
    ∧ azim 0 ax y1' y2'
        ≤ Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y1'‖ * ‖y2'‖)))
    ∧ Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + (t1 - t2) ^ 2 * ‖ax‖ ^ 2)
          / (2 * (‖y1'‖ * ‖y2'‖))) ≤ azim 0 ax y1' y2'
    ∧ azim 0 ax y2' w
        ≤ Real.arccos ((‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y2'‖ * ‖w‖)))
    ∧ Real.arccos ((‖w‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + t2 ^ 2 * ‖ax‖ ^ 2)
          / (2 * (‖y2'‖ * ‖w‖))) ≤ azim 0 ax y2' w := by
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncw := pmAxisOrthoNC_p35 hax0 hw0 hW
  have hncy1 := pmAxisOrthoNC_p35 hax0 hy10 hy1o
  have hncy2 := pmAxisOrthoNC_p35 hax0 hy20 hy2o
  -- the projected chords inherit the far bounds
  have hd1' : dist u y1' ≤ cstab := pmOrthoOffProjChordLe_p35 hU hy1 hy1o e1
  have hd3' : dist w y2' ≤ cstab := by
    refine pmOrthoOffProjChordLe_p35 hW hy2 hy2o ?_
    rw [dist_comm]
    exact e3
  have hspl := pmOrthoOffTwoPythDist_p35 hy1 hy1o hy2 hy2o
  have hsqn : (0:ℝ) ≤ (t1 - t2) ^ 2 * ‖ax‖ ^ 2 :=
    mul_nonneg (sq_nonneg (t1 - t2)) (sq_nonneg ‖ax‖)
  have hd12 : dist y1' y2' ≤ cstab := by
    have hsq : dist y1 y2 ^ 2 ≤ cstab ^ 2 :=
      pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist y1 y2) e2 2
    have hsq2 : dist y1' y2' ^ 2 ≤ cstab ^ 2 := by linarith
    by_contra hcon
    have hgt : cstab < dist y1' y2' := not_le.mp hcon
    have hc0 : (0:ℝ) ≤ cstab := le_of_lt (by norm_num [cstab])
    have hlt : cstab ^ 2 < dist y1' y2' ^ 2 :=
      (sq_lt_sq₀ hc0 (by simp : (0:ℝ) ≤ dist y1' y2')).mpr hgt
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pmOrthoArcChain3_p35 hax0 hncu hncy1 hncy2 hncw h1 h2
  · exact pmOrthoOffAzimWindowFar_p35 hax0 hu0 hy10 hU hy1o hd1' hp1
  · exact pmOrthoOffStepAzimGe_p35 hax0 hu0 hy10 hU hy1o hy1 f1 hp1
  · exact pmOrthoOffAzimWindowFar_p35 hax0 hy10 hy20 hy1o hy2o hd12 hp2
  · exact pmOrthoOffTwoStepAzimGe_p35 hax0 hy10 hy20 hy1o hy2o hy1 hy2 f2 hp2
  · -- far window for the (y2', w) step: the chord bound inherits through
    -- the projection; the dot window is read at the in-plane endpoint and
    -- commuted to the arc direction
    have hcosF := pmAzimOrthoCos_p35 hax0 hy20 hw0 hncy2 hncw hy2o hW
    have hdotF := pmDotNormDist_p35 w y2'
    have hcomm : ((y2' : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ))
        = ((w : Fin 3 → ℝ) ⬝ᵥ (y2' : Fin 3 → ℝ)) :=
      dotProduct_comm (y2' : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    have hstepF : (‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2) / 2
        ≤ Real.cos (azim 0 ax y2' w) * (‖y2'‖ * ‖w‖) := by
      rw [hcosF, hcomm, hdotF]
      have h1' : dist w y2' ^ 2 ≤ cstab ^ 2 :=
        pow_le_pow_left₀ (by simp : (0:ℝ) ≤ dist w y2') hd3' 2
      linarith
    have hd0F : (‖y2'‖ * ‖w‖ : ℝ) ≠ 0 := ne_of_gt
      (mul_pos (norm_pos_iff.mpr hy20) (norm_pos_iff.mpr hw0))
    have hkeyF : (‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2) / (2 * (‖y2'‖ * ‖w‖))
        ≤ Real.cos (azim 0 ax y2' w) := by
      have hbr := pmOrthoOffDivBridge_p35 (‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2)
        (‖y2'‖ * ‖w‖) hd0F
      exact le_of_mul_le_mul_right (by rw [hbr]; exact hstepF)
        (mul_pos (norm_pos_iff.mpr hy20) (norm_pos_iff.mpr hw0))
    exact pmOrthoOffAzimLeOfCosGe_p35 hp3 hkeyF
  · -- near window for the (y2', w) step: the chord-2 bound on the lifted
    -- pair (w, y2) shifts by the y2-height
    have hcos := pmAzimOrthoCos_p35 hax0 hy20 hw0 hncy2 hncw hy2o hW
    have hwin := pmOrthoOffDotLe_p35 hW hy2 hy2o (by rw [dist_comm]; exact f3)
    have hstep : Real.cos (azim 0 ax y2' w) * (‖y2'‖ * ‖w‖)
        ≤ (‖w‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + t2 ^ 2 * ‖ax‖ ^ 2) / 2 := by
      rw [hcos, dotProduct_comm (y2' : Fin 3 → ℝ) (w : Fin 3 → ℝ)]; linarith
    have hd0 : (‖y2'‖ * ‖w‖ : ℝ) ≠ 0 := ne_of_gt
      (mul_pos (norm_pos_iff.mpr hy20) (norm_pos_iff.mpr hw0))
    have hkey : Real.cos (azim 0 ax y2' w)
        ≤ (‖w‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + t2 ^ 2 * ‖ax‖ ^ 2)
          / (2 * (‖y2'‖ * ‖w‖)) := by
      have hbr := pmOrthoOffDivBridge_p35
        (‖w‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + t2 ^ 2 * ‖ax‖ ^ 2) (‖y2'‖ * ‖w‖) hd0
      exact le_of_mul_le_mul_right (by rw [hbr]; exact hstep)
        (mul_pos (norm_pos_iff.mpr hy20) (norm_pos_iff.mpr hw0))
    exact pmOrthoOffAzimGeOfCosLe_p35 hp3 hkey

-- pm14 axcheck tail (probe only; dropped from the kit proper)
/-! ## planemiss15 rungs (lkgrqui-planemiss15-w3, 2026-10-28)

The (iii) branch continues with the two residual sub-blocks of the
off-plane intermediate-point account.  **(iii-b) the in-plane partner
specialization**: when the arc tail `y2` sits IN the axis plane
(`t2 = 0`), the pm13 height ceiling instantiates at the `(u, y2)` (resp.
`(w, y2)`) pair — the lifted `y1` has both its chords ring-bounded, so its
squared height drops under `cstab ^ 2 - dist u y2 ^ 2 / 4` (numeric form
`<= cstab ^ 2 - 1`), the projected radius picks up the coupling floor
`4 - cstab ^ 2 + dist u y2 ^ 2 / 4`, the step-2 near window degenerates to
the plain `t1`-shift, and a failed (iii-a) clamp quadrant forces the
narrowed norm cap `norm y1 ^ 2 < cstab ^ 2 + 25 / 4 - dist u y2 ^ 2 / 4`.
**(iii-a) the radius-coupled window squeeze, conditional-form core**: the
pm14 warning stands — ONE arc of four-point window data has free
instances, so the kill consumes the SECOND arc plus the wrap
`Sigma = 2 * pi`.  Engine: a projected pair with both norms `>= 2` and one
`>= 5/2` has its clean far window squeezed under `arccos (11899/100000)`
(`11899/100000` is the exact minimum of `(p^2 + q^2 - cstab^2)/(2 p q)` on
that region, attained at `(2, 5/2)`); three such steps sum under
`3 * phi`, `phi := arccos (11899/100000)`, and the triple-angle identity
gives `3 * phi < 2 * pi - beta` (`cos (3 phi) = 4 c^3 - 3 c
<= -35023/100000 < -10601/80000 = cos beta`), so EITHER arc's displacement
is too short against the far-arc split on the in-plane diagonal pair
`(w, u)` — both branches die through `azim_compl`.  The honest residual of
(iii-a): the sub-`5/2` projection quadrant (some lifted projection below
the clamp — the pm9 tiny-azimuth phenomenon) is NOT killed here; the
(iii-b) in-plane-partner coupling pieces are its designated feed.  All
pieces are new lemmas with zero `sorry`; the residual root
`pmPlaneCrowding_p35` is untouched. -/

/-- (pm15, iii-b) **In-plane-partner ceiling, `u`-form**: with the arc tail
`y2` in the axis plane (`t2 = 0`), the pm13 height ceiling applies at the
pair `(u, y2)` — both chords `u-y1` and `y1-y2` are ring-bounded, so the
lifted `y1`'s squared height drops under `cstab ^ 2 - dist u y2 ^ 2 / 4`. -/
private theorem pmOrthoOffInPlaneCeilU_p35 {ax u y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab) :
    t1 ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2 - dist u y2 ^ 2 / 4 := by
  have hy2z : y2 = y2' := by rw [hy2, ht2, zero_smul, add_zero]
  have hY2 : ((y2 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) = 0 := by
    rw [hy2z]; exact hy2o
  exact pmOrthoOffHeightSqLe_p35 hU hY2 hy1 hy1o e1
    (by rw [dist_comm]; exact e2)

/-- (pm15, iii-b) **In-plane-partner ceiling, `w`-form**: the same
instantiation at the pair `(w, y2)` — the skip chord `y1-w` is the second
ring-bounded chord. -/
private theorem pmOrthoOffInPlaneCeilW_p35 {ax u w y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (ew1 : dist y1 w ≤ cstab) (e2 : dist y1 y2 ≤ cstab) :
    t1 ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2 - dist w y2 ^ 2 / 4 := by
  have hy2z : y2 = y2' := by rw [hy2, ht2, zero_smul, add_zero]
  have hY2 : ((y2 : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ)) = 0 := by
    rw [hy2z]; exact hy2o
  exact pmOrthoOffHeightSqLe_p35 hW hY2 hy1 hy1o
    (by rw [dist_comm]; exact ew1) (by rw [dist_comm]; exact e2)

/-- (pm15, iii-b) **In-plane-partner ceiling, numeric form**: with the ring
chord `dist u y2 >= 2` (the ring-distance-2 `a`-conjunct) the squared
height is at most `cstab ^ 2 - 1`. -/
private theorem pmOrthoOffInPlaneCeilNum_p35 {ax u w y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab)
    (h2d : (2:ℝ) ≤ dist u y2) :
    t1 ^ 2 * ‖ax‖ ^ 2 ≤ cstab ^ 2 - 1 := by
  have h := pmOrthoOffInPlaneCeilU_p35 hU hy2o hy2 ht2 hy1 hy1o e1 e2
  have h4 : (2:ℝ) ^ 2 ≤ dist u y2 ^ 2 := pow_le_pow_left₀ (by norm_num) h2d 2
  norm_num at h4
  linarith

/-- (pm15, iii-b) **Radius-coupling floor**: the ceiling lifts to a floor
on the projected radius — `norm y1' ^ 2 >= 4 - cstab ^ 2
+ dist u y2 ^ 2 / 4`: the larger the skip chord, the larger the projection
of the lifted point (the `(norm y1', h1)` quadrant-clamp readout feeding
(iii-a)). -/
private theorem pmOrthoOffInPlaneProjFloor_p35 {ax u w y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab)
    (h12 : (2:ℝ) ≤ ‖y1‖) :
    (4:ℝ) - cstab ^ 2 + dist u y2 ^ 2 / 4 ≤ ‖y1'‖ ^ 2 := by
  have hn := pmOrthoPythNorm_p35 hy1 hy1o
  have h4 : (2:ℝ) ^ 2 ≤ ‖y1‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h12 2
  norm_num at h4
  have hceil := pmOrthoOffInPlaneCeilU_p35 hU hy2o hy2 ht2 hy1 hy1o e1 e2
  linarith

/-- (pm15, iii-b) **Degenerate step-2 near window**: with `t2 = 0` the
two-point height-DIFFERENCE shift collapses to the plain `t1`-shift — the
step-2 near window reads `arccos((norm y1' ^ 2 + norm y2' ^ 2 - 4 +
t1 ^ 2 * norm ax ^ 2) / (2 * norm y1' * norm y2')) <= azim y1' y2'`. -/
private theorem pmOrthoOffInPlaneTwoNear_p35 {ax y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hax0 : ax ≠ (0:V3)) (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3))
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (f2 : (2:ℝ) ≤ dist y1 y2)
    (hπ : azim 0 ax y1' y2' ≤ Real.pi) :
    Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - 4 + t1 ^ 2 * ‖ax‖ ^ 2)
        / (2 * (‖y1'‖ * ‖y2'‖))) ≤ azim 0 ax y1' y2' := by
  have hwin := pmOrthoOffTwoStepAzimGe_p35 hax0 hy10 hy20 hy1o hy2o hy1 hy2 f2 hπ
  rwa [ht2, sub_zero] at hwin

/-- (pm15, iii-b) **Failed-clamp quadrant readout**: if the projection
fails the (iii-a) clamp (`norm y1' < 5/2`), the lifted norm is capped —
`norm y1 ^ 2 < cstab ^ 2 + 25 / 4 - dist u y2 ^ 2 / 4` (numerically under
`14.32`, i.e. the vertex sits in the narrow annulus `norm y1 < 3.79`):
the small-projection quadrant is a genuinely thinner configuration. -/
private theorem pmOrthoOffInPlaneSmallProjNorm_p35 {ax u w y1 y2 y1' y2' : V3}
    {t1 t2 : ℝ}
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax) (ht2 : t2 = 0)
    (hy1 : y1 = y1' + t1 • ax)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab)
    (h12 : (2:ℝ) ≤ ‖y1‖) (hlt : ‖y1'‖ < (5:ℝ) / 2) :
    ‖y1‖ ^ 2 < cstab ^ 2 + 25 / 4 - dist u y2 ^ 2 / 4 := by
  have hn := pmOrthoPythNorm_p35 hy1 hy1o
  have hsq : ‖y1'‖ ^ 2 < ((5:ℝ) / 2) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg y1') (by norm_num)).mpr hlt
  have hconv : ((5:ℝ) / 2) ^ 2 = 25 / 4 := by norm_num
  rw [hconv] at hsq
  have hceil := pmOrthoOffInPlaneCeilU_p35 hU hy2o hy2 ht2 hy1 hy1o e1 e2
  linarith

/-- (pm15, iii-a) **Fraction cap, one-sided form**: for `2 <= p` and
`5/2 <= q` the clean far-window fraction is at least `11899/100000` — the
exact minimum of `(p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * p * q)` on that
region, attained at `(p, q) = (2, 5/2)`.  Proof: the substitution
`a = p - 2`, `b = q - 5/2` expands `100000 * (p ^ 2 + q ^ 2)
- 23798 * p * q - 906010` into `100000 * (a - b) ^ 2 + 176202 * a * b +
340505 * a + 452404 * b >= 0`. -/
private theorem pmOrthoOffCapFracAux_p35 {p q : ℝ} (h2p : (2:ℝ) ≤ p)
    (h2q : (5:ℝ) / 2 ≤ q) :
    (11899:ℝ) / 100000 ≤ (p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * (p * q)) := by
  have hcs : cstab = 301 / 100 := by norm_num [cstab]
  rw [hcs]
  have hsqc : ((301:ℝ) / 100) ^ 2 = 90601 / 10000 := by norm_num
  rw [hsqc]
  have h1 : (0:ℝ) ≤ p - 2 := by linarith
  have h2 : (0:ℝ) ≤ q - 5 / 2 := by linarith
  have hab : (0:ℝ) ≤ (p - 2) * (q - 5 / 2) := mul_nonneg h1 h2
  have hsqd : (0:ℝ) ≤ (p - 2) * (p - 2) + (q - 5 / 2) * (q - 5 / 2)
      - 2 * ((p - 2) * (q - 5 / 2)) := by
    have hd : ((p - 2) - (q - 5 / 2)) ^ 2
        = (p - 2) * (p - 2) + (q - 5 / 2) * (q - 5 / 2)
          - 2 * ((p - 2) * (q - 5 / 2)) := by
      rw [pow_two]; ring
    rw [← hd]; exact sq_nonneg _
  have hkey : (11899:ℝ) / 100000 * (2 * (p * q))
      ≤ p ^ 2 + q ^ 2 - 90601 / 10000 := by
    have hexp : (100000:ℝ) * (p ^ 2 + q ^ 2) - 23798 * (p * q) - 906010
        = 100000 * ((p - 2) * (p - 2) + (q - 5 / 2) * (q - 5 / 2)
              - 2 * ((p - 2) * (q - 5 / 2)))
          + 176202 * ((p - 2) * (q - 5 / 2)) + 340505 * (p - 2)
            + 452404 * (q - 5 / 2) := by
      ring
    have hpos : (0:ℝ) ≤ (100000:ℝ) * (p ^ 2 + q ^ 2) - 23798 * (p * q)
        - 906010 := by rw [hexp]; linarith
    linarith
  have hprod : (0:ℝ) < p * q := by
    have a1 : (0:ℝ) < p := lt_of_lt_of_le (by norm_num) h2p
    have a2 : (0:ℝ) < q := lt_of_lt_of_le (by norm_num) h2q
    exact mul_pos a1 a2
  rw [le_div_iff₀ (show (0:ℝ) < 2 * (p * q) from by linarith)]
  linarith

/-- (pm15, iii-a) **Fraction cap, symmetric form**: two norms both `>= 2`
with at least one `>= 5/2` meet the far-window fraction bound
`11899/100000`. -/
private theorem pmOrthoOffCapFrac_p35 {p q : ℝ} (h2p : (2:ℝ) ≤ p)
    (h2q : (2:ℝ) ≤ q) (hmax : (5:ℝ) / 2 ≤ p ∨ (5:ℝ) / 2 ≤ q) :
    (11899:ℝ) / 100000 ≤ (p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * (p * q)) := by
  rcases hmax with hm | hm
  · have h := pmOrthoOffCapFracAux_p35 h2q hm
    rwa [show (q ^ 2 + p ^ 2 - cstab ^ 2) / (2 * (q * p))
        = (p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * (p * q)) from by ring] at h
  · exact pmOrthoOffCapFracAux_p35 h2p hm

/-- (pm15, iii-a) **Step cap**: the clean far window of a clamped
projected pair collapses to the uniform cap `arccos (11899/100000)`. -/
private theorem pmOrthoOffStepCap_p35 {ax p q : V3}
    (h2p : (2:ℝ) ≤ ‖p‖) (h2q : (2:ℝ) ≤ ‖q‖)
    (hmax : (5:ℝ) / 2 ≤ ‖p‖ ∨ (5:ℝ) / 2 ≤ ‖q‖)
    (hwin : azim 0 ax p q
      ≤ Real.arccos ((‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2) / (2 * (‖p‖ * ‖q‖)))) :
    azim 0 ax p q ≤ Real.arccos ((11899:ℝ) / 100000) :=
  le_trans hwin (Real.arccos_le_arccos (pmOrthoOffCapFrac_p35 h2p h2q hmax))

/-- (pm15, iii-a) Triple-angle identity (private `sin`-free route through
both `cos 2x` forms). -/
private theorem pmOrthoCosThreeMul_p35 (x : ℝ) :
    Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by
  have h1 : Real.cos (3 * x) = Real.cos (2 * x + x) := by congr 1; ring
  rw [h1, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  have hA := Real.cos_two_mul x
  have hB := Real.cos_two_mul' x
  have hs2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by linarith
  linear_combination -2 * Real.cos x * hs2

/-- (pm15, iii-a) **The three-step window engine**: each of the three steps
capped by `phi := arccos (11899/100000)` sums with the far constant `beta`
to less than the full turn — `3 * phi < 2 * pi - beta` because
`cos (3 phi) = 4 c ^ 3 - 3 c <= -35023/100000 < -10601/80000 = cos beta`
and cosine is decreasing on `[0, pi]`. -/
private theorem pmOrthoOffArcThreeCap_p35 {S1 S2 S3 : ℝ}
    (h1 : S1 ≤ Real.arccos ((11899:ℝ) / 100000))
    (h2 : S2 ≤ Real.arccos ((11899:ℝ) / 100000))
    (h3 : S3 ≤ Real.arccos ((11899:ℝ) / 100000)) :
    S1 + S2 + S3 + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have hp3 : Real.arccos ((1:ℝ) / 2) = Real.pi / 3 := by
    rw [← Real.arccos_cos (show (0:ℝ) ≤ Real.pi / 3 from by linarith [Real.pi_pos])
      (show Real.pi / 3 ≤ Real.pi from by linarith [Real.pi_pos]),
      pmOrthoTriCosPi3_p35]
  have h23 : Real.arccos (-(1 / 2:ℝ)) = 2 * Real.pi / 3 := by
    rw [← Real.arccos_cos (show (0:ℝ) ≤ 2 * Real.pi / 3 from by linarith [Real.pi_pos])
      (show 2 * Real.pi / 3 ≤ Real.pi from by linarith [Real.pi_pos]),
      pmOrthoTriCos23_p35]
  have hφge : Real.pi / 3 ≤ Real.arccos ((11899:ℝ) / 100000) := by
    have h := Real.arccos_le_arccos (show (11899:ℝ) / 100000 ≤ (1:ℝ) / 2 by norm_num)
    rwa [hp3] at h
  have hφle : Real.arccos ((11899:ℝ) / 100000) ≤ 2 * Real.pi / 3 := by
    have h := Real.arccos_le_arccos (show (-(1 / 2:ℝ)) ≤ (11899:ℝ) / 100000 by norm_num)
    rwa [h23] at h
  have hπle : Real.pi ≤ 3 * Real.arccos ((11899:ℝ) / 100000) := by linarith
  have h2π : 3 * Real.arccos ((11899:ℝ) / 100000) ≤ 2 * Real.pi := by linarith
  have hcos3 : Real.cos (3 * Real.arccos ((11899:ℝ) / 100000))
      ≤ -(35023:ℝ) / 100000 := by
    rw [pmOrthoCosThreeMul_p35,
      Real.cos_arccos (by norm_num : (-1:ℝ) ≤ 11899 / 100000)
        (by norm_num : (11899:ℝ) / 100000 ≤ 1)]
    norm_num
  have hper : Real.cos (2 * Real.pi - 3 * Real.arccos ((11899:ℝ) / 100000))
      = Real.cos (3 * Real.arccos ((11899:ℝ) / 100000)) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have hrev : Real.arccos (-(10601 / 80000))
      < 2 * Real.pi - 3 * Real.arccos ((11899:ℝ) / 100000) := by
    by_contra hge
    have hle : 2 * Real.pi - 3 * Real.arccos ((11899:ℝ) / 100000)
        ≤ Real.arccos (-(10601 / 80000)) := le_of_not_gt hge
    have hm := pmOrthoTriCosMono_p35
      (show (0:ℝ) ≤ 2 * Real.pi - 3 * Real.arccos ((11899:ℝ) / 100000) from by linarith)
      hle (show Real.arccos (-(10601 / 80000)) ≤ Real.pi from Real.arccos_le_pi _)
    rw [hper] at hm
    have hcβ : Real.cos (Real.arccos (-(10601 / 80000))) = -(10601 / 80000) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    linarith
  linarith

/-- (pm15, iii-a) **The single-arc big-kill**: an arc `u -> y1' -> y2' -> w`
whose three projected steps carry the pm14 clean far windows and whose four
norms meet the clamp (all `>= 2`, the lifted projections `>= 5/2`) has
displacement strictly below `2 * pi - beta`. -/
private theorem pmOrthoOffArcBigKill_p35 {ax u w y1' y2' : V3}
    (hu2 : (2:ℝ) ≤ ‖u‖) (hw2 : (2:ℝ) ≤ ‖w‖)
    (cy1 : (5:ℝ) / 2 ≤ ‖y1'‖) (cy2 : (5:ℝ) / 2 ≤ ‖y2'‖)
    (hchain : azim 0 ax u w
      = azim 0 ax u y1' + azim 0 ax y1' y2' + azim 0 ax y2' w)
    (hwin1 : azim 0 ax u y1'
        ≤ Real.arccos ((‖u‖ ^ 2 + ‖y1'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖u‖ * ‖y1'‖))))
    (hwin2 : azim 0 ax y1' y2'
        ≤ Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y1'‖ * ‖y2'‖))))
    (hwin3 : azim 0 ax y2' w
        ≤ Real.arccos ((‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y2'‖ * ‖w‖)))) :
    azim 0 ax u w + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have h2y1 : (2:ℝ) ≤ ‖y1'‖ := le_trans (by norm_num) cy1
  have h2y2 : (2:ℝ) ≤ ‖y2'‖ := le_trans (by norm_num) cy2
  have hc1 := pmOrthoOffStepCap_p35 hu2 h2y1 (Or.inr cy1) hwin1
  have hc2 := pmOrthoOffStepCap_p35 h2y1 h2y2 (Or.inl cy1) hwin2
  have hc3 := pmOrthoOffStepCap_p35 h2y2 hw2 (Or.inl cy2) hwin3
  rw [hchain]
  exact pmOrthoOffArcThreeCap_p35 hc1 hc2 hc3

/-- (pm15, iii-a) **THE TWO-ARC SQUEEZE (the conditional-form core)**: the
full `k = 6`, `d = 3` hexagon `u -> y1 -> y2 -> w -> z1 -> z2 -> u` around
the axis with BOTH intermediate points of each arc lifted, the in-plane
diagonal `u, w` an annulus pair at chord in `[2, cstab]`, both arcs
carrying the direction-feed order premises (the `pmOrthoOffMidArcWindows_p35`
input shape verbatim, both arcs), the clamp quadrant on all four lifted
projections — then `False`.  Each arc's displacement is squeezed below
`2 * pi - beta` (the big-kill), but the far-arc split on the diagonal puts
one of `azim w u`, `2 * pi - azim w u` at most `beta`, i.e. the OPPOSITE
arc's displacement at least `2 * pi - beta` — the pm14 one-arc free
instance dies against the second arc plus the `Sigma = 2 * pi` wrap. -/
private theorem pmOrthoOffTwoArcSqueeze_p35 {ax u w y1 y2 z1 z2 y1' y2' z1' z2' : V3}
    {t1 t2 s1 s2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3)) (hz10 : z1' ≠ (0:V3)) (hz20 : z2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1o : (z1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz2o : (z2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax)
    (hz1 : z1 = z1' + s1 • ax) (hz2 : z2 = z2' + s2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (cy1 : (5:ℝ) / 2 ≤ ‖y1'‖) (cy2 : (5:ℝ) / 2 ≤ ‖y2'‖)
    (cz1 : (5:ℝ) / 2 ≤ ‖z1'‖) (cz2 : (5:ℝ) / 2 ≤ ‖z2'‖)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab) (e3 : dist y2 w ≤ cstab)
    (f1 : dist w z1 ≤ cstab) (f2 : dist z1 z2 ≤ cstab) (f3 : dist z2 u ≤ cstab)
    (ed : dist u w ≤ cstab) (hdg : (2:ℝ) ≤ dist u w)
    (r1 : (2:ℝ) ≤ dist u y1) (r2 : (2:ℝ) ≤ dist y1 y2) (r3 : (2:ℝ) ≤ dist y2 w)
    (r4 : (2:ℝ) ≤ dist w z1) (r5 : (2:ℝ) ≤ dist z1 z2) (r6 : (2:ℝ) ≤ dist z2 u)
    (h1 : azim 0 ax u y1' ≤ azim 0 ax u y2')
    (h2 : azim 0 ax u y2' ≤ azim 0 ax u w)
    (hp1 : azim 0 ax u y1' ≤ Real.pi) (hp2 : azim 0 ax y1' y2' ≤ Real.pi)
    (hp3 : azim 0 ax y2' w ≤ Real.pi)
    (g1 : azim 0 ax w z1' ≤ azim 0 ax w z2')
    (g2 : azim 0 ax w z2' ≤ azim 0 ax w u)
    (hq1 : azim 0 ax w z1' ≤ Real.pi) (hq2 : azim 0 ax z1' z2' ≤ Real.pi)
    (hq3 : azim 0 ax z2' u ≤ Real.pi) :
    False := by
  have cap1 := pmOrthoOffMidArcWindows_p35 hax0 hu0 hw0 hy10 hy20 hU hW hy1o hy2o
    hy1 hy2 e1 e2 e3 r1 r2 r3 h1 h2 hp1 hp2 hp3
  have cap2 := pmOrthoOffMidArcWindows_p35 (u := w) (w := u) (y1 := z1) (y2 := z2)
    (y1' := z1') (y2' := z2') (t1 := s1) (t2 := s2)
    hax0 hw0 hu0 hz10 hz20 hW hU hz1o hz2o hz1 hz2 f1 f2 f3 r4 r5 r6 g1 g2 hq1 hq2 hq3
  have kb1 := pmOrthoOffArcBigKill_p35 hu2 hw2 cy1 cy2
    cap1.1 cap1.2.1 cap1.2.2.2.1 cap1.2.2.2.2.2.1
  have kb2 := pmOrthoOffArcBigKill_p35 (u := w) (w := u) (y1' := z1') (y2' := z2')
    hw2 hu2 cz1 cz2 cap2.1 cap2.2.1 cap2.2.2.2.1 cap2.2.2.2.2.2.1
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncw := pmAxisOrthoNC_p35 hax0 hw0 hW
  have hwune : azim 0 ax w u ≠ 0 :=
    pmOrthoTriAzimNe0_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact hdg)
  have hcompl := azim_compl (z := (0:V3)) (w := ax) (w1 := w) (w2 := u) hncw hncu
  rw [if_neg hwune] at hcompl
  rcases pmOrthoTriFarSplit_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact ed) with hnear | hfar
  · exfalso
    rw [hcompl] at kb1
    linarith
  · exfalso
    linarith

-- pm15 axcheck tail (probe only; dropped from the kit proper)

/-! ## planemiss16 rungs (lkgrqui-planemiss16-w3, 2026-10-28)

The **sub-`5/2` projection quadrant** — the honest residual the pm15
CAPSTONE `pmOrthoOffTwoArcSqueeze_p35` excludes through its four clamp
hypotheses (the pm9 micro-azimuth freedom: a lifted projection of radius
`~0.5` admits an azimuthally tiny step at chord in `[2, cstab]`).  The
attack is a continuous scan of the clamp constant.  The pm15 fraction cap
`11899/100000` is the exact value of the clean far-window fraction at the
`(2, 5/2)` corner of the clamp region; the three-step engine only needs
the fraction above `cos((2 * pi - beta) / 3) ≈ 0.0444`, and the fraction
at the `(2, 47/20)` corner, `289/5875 ≈ 0.0492`, still clears it — so the
entire clamp argument runs verbatim with `5/2` weakened to `47/20`:
**the band `[47/20, 5/2)` of the sub-`5/2` quadrant is closed
unconditionally** (the reduced CAPSTONE `pmOrthoOffTwoArcSqueezeSub25_p35`).
For the genuinely free sub-`47/20` quadrant the wave delivers the honest
sizing the pm9 lesson asks for: with one arc clamped at `47/20` the
diagonal azimuth is pinned to the near wedge (`pmOrthoOffDiagNearWedge_p35`
— the far branch dies against the clamped arc alone), and when only ONE
projection stays sub-`47/20`, the two steps adjacent to it must sum past
`2 * pi - beta - arccos (289/5875) ≈ 175.2°` (`pmOrthoOffSubQuadResidue_p35`)
— any surviving configuration bends hard around the small projection.
That pin is the feed shape the pm12 coupling account consumes.  All
pieces are new lemmas with zero `sorry`; the residual root
`pmPlaneCrowding_p35` is untouched. -/

/-- (pm16, sub-`5/2` scan) **Fraction cap on the `47/20` band, one-sided
form**: for `2 <= p` and `47/20 <= q` the clean far-window fraction is at
least `289/5875` — the exact minimum of `(p ^ 2 + q ^ 2 - cstab ^ 2) /
(2 * p * q)` on that region, attained at `(p, q) = (2, 47/20)`.  This
weakens the pm15 clamp constant: `11899/100000` is the value at `(2, 5/2)`,
and the value at the `(2, 47/20)` corner still clears the three-step
engine's threshold `cos((2 * pi - beta) / 3)`.  Proof: the substitution
`a = p - 2`, `b = q - 47/20` expands the doubled numerator into
`11750000 * (a - b) ^ 2 + 22344000 * a * b + 44283400 * a + 52913000 * b
>= 0`, `ring`-locked. -/
private theorem pmOrthoOffCapFracSub25_p35 {p q : ℝ} (h2p : (2:ℝ) ≤ p)
    (h2q : (47:ℝ) / 20 ≤ q) :
    (289:ℝ) / 5875 ≤ (p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * (p * q)) := by
  have hcs : cstab = 301 / 100 := by norm_num [cstab]
  rw [hcs]
  have hsqc : ((301:ℝ) / 100) ^ 2 = 90601 / 10000 := by norm_num
  rw [hsqc]
  have h1 : (0:ℝ) ≤ p - 2 := by linarith
  have h2 : (0:ℝ) ≤ q - 47 / 20 := by linarith
  have hab : (0:ℝ) ≤ (p - 2) * (q - 47 / 20) := mul_nonneg h1 h2
  have hsqd : (0:ℝ) ≤ (p - 2) * (p - 2) + (q - 47 / 20) * (q - 47 / 20)
      - 2 * ((p - 2) * (q - 47 / 20)) := by
    have hd : ((p - 2) - (q - 47 / 20)) ^ 2
        = (p - 2) * (p - 2) + (q - 47 / 20) * (q - 47 / 20)
          - 2 * ((p - 2) * (q - 47 / 20)) := by
      rw [pow_two]; ring
    rw [← hd]; exact sq_nonneg _
  have hkey : (289:ℝ) / 5875 * (2 * (p * q))
      ≤ p ^ 2 + q ^ 2 - 90601 / 10000 := by
    have hexp : (11750000:ℝ) * (p ^ 2 + q ^ 2)
        - (1156000:ℝ) * (p * q) - (106456175:ℝ)
        = (11750000:ℝ) * ((p - 2) * (p - 2) + (q - 47 / 20) * (q - 47 / 20)
              - 2 * ((p - 2) * (q - 47 / 20)))
          + (22344000:ℝ) * ((p - 2) * (q - 47 / 20)) + (44283400:ℝ) * (p - 2)
            + (52913000:ℝ) * (q - 47 / 20) := by
      ring
    have hpos : (0:ℝ) ≤ (11750000:ℝ) * (p ^ 2 + q ^ 2)
        - (1156000:ℝ) * (p * q) - (106456175:ℝ) := by
      rw [hexp]; linarith
    linarith
  have hprod : (0:ℝ) < p * q := by
    have a1 : (0:ℝ) < p := lt_of_lt_of_le (by norm_num) h2p
    have a2 : (0:ℝ) < q := lt_of_lt_of_le (by norm_num) h2q
    exact mul_pos a1 a2
  rw [le_div_iff₀ (show (0:ℝ) < 2 * (p * q) from by linarith)]
  linarith

/-- (pm16, sub-`5/2` scan) **Step cap on the `47/20` band**: a projected
pair whose norms meet the band disjunction (each `>= 47/20`, with the
diagonal-end side allowed down to the annulus bound `2 <= norm`) has its
clean far window squeezed under the uniform cap `arccos (289/5875)`. -/
private theorem pmOrthoOffStepCapSub25_p35 {ax p q : V3}
    (hpair : ((2:ℝ) ≤ ‖p‖ ∧ (47:ℝ) / 20 ≤ ‖q‖)
      ∨ ((47:ℝ) / 20 ≤ ‖p‖ ∧ (2:ℝ) ≤ ‖q‖))
    (hwin : azim 0 ax p q
      ≤ Real.arccos ((‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2)
        / (2 * (‖p‖ * ‖q‖)))) :
    azim 0 ax p q ≤ Real.arccos ((289:ℝ) / 5875) := by
  refine le_trans hwin (Real.arccos_le_arccos ?_)
  rcases hpair with ⟨a, b⟩ | ⟨a, b⟩
  · exact pmOrthoOffCapFracSub25_p35 a b
  · have h := pmOrthoOffCapFracSub25_p35 (p := ‖q‖) (q := ‖p‖) b a
    rwa [show (‖q‖ ^ 2 + ‖p‖ ^ 2 - cstab ^ 2) / (2 * (‖q‖ * ‖p‖))
        = (‖p‖ ^ 2 + ‖q‖ ^ 2 - cstab ^ 2) / (2 * (‖p‖ * ‖q‖)) from by ring] at h

/-- (pm16, sub-`5/2` scan) **The three-step window engine, generic form**:
with a uniform step cap `arccos c` whose triple angle beats the far
constant (`cos (3 * arccos c) <= d < -10601/80000 = cos beta`, cap at most
`2 * pi / 3`), three capped steps plus the far constant sum under the full
turn.  This factors the trigonometric skeleton of the pm15 engine
`pmOrthoOffArcThreeCap_p35` (the `11899/100000` instance) so the `47/20`
band below reuses it with new constants. -/
private theorem pmOrthoOffArcThreeCapGen_p35 {S1 S2 S3 c d : ℝ}
    (h1 : S1 ≤ Real.arccos c) (h2 : S2 ≤ Real.arccos c)
    (h3 : S3 ≤ Real.arccos c)
    (hhi : Real.arccos c ≤ 2 * Real.pi / 3)
    (hcos3 : Real.cos (3 * Real.arccos c) ≤ d)
    (hdlt : d < -(10601 / 80000)) :
    S1 + S2 + S3 + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have h2π : 3 * Real.arccos c ≤ 2 * Real.pi := by linarith
  have hper : Real.cos (2 * Real.pi - 3 * Real.arccos c)
      = Real.cos (3 * Real.arccos c) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have hrev : Real.arccos (-(10601 / 80000))
      < 2 * Real.pi - 3 * Real.arccos c := by
    by_contra hge
    have hle : 2 * Real.pi - 3 * Real.arccos c
        ≤ Real.arccos (-(10601 / 80000)) := le_of_not_gt hge
    have hm := pmOrthoTriCosMono_p35
      (show (0:ℝ) ≤ 2 * Real.pi - 3 * Real.arccos c from by linarith)
      hle (show Real.arccos (-(10601 / 80000)) ≤ Real.pi from Real.arccos_le_pi _)
    rw [hper] at hm
    have hcβ : Real.cos (Real.arccos (-(10601 / 80000))) = -(10601 / 80000) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    linarith
  linarith

/-- (pm16, sub-`5/2` scan) **The `47/20`-band cap constants**: with
`phi := arccos (289/5875) ≈ 87.18°` the cap sits below `2 * pi / 3` and
its triple angle satisfies `cos (3 * phi) = 4 c ^ 3 - 3 c
<= -14709/100000 < -10601/80000 = cos beta` (the pm15 comparison constant
`-35023/100000` belongs to the sharper `11899/100000` cap; the weaker cap
gets the weaker constant, still with a comfortable margin). -/
private theorem pmOrthoOffSub25PhiCaps_p35 :
    Real.arccos ((289:ℝ) / 5875) ≤ 2 * Real.pi / 3
    ∧ Real.cos (3 * Real.arccos ((289:ℝ) / 5875)) ≤ -(14709:ℝ) / 100000 := by
  constructor
  · have h23 : Real.arccos (-(1 / 2:ℝ)) = 2 * Real.pi / 3 := by
      rw [← Real.arccos_cos (show (0:ℝ) ≤ 2 * Real.pi / 3 from by linarith [Real.pi_pos])
        (show 2 * Real.pi / 3 ≤ Real.pi from by linarith [Real.pi_pos]),
        pmOrthoTriCos23_p35]
    have h := Real.arccos_le_arccos (show (-(1 / 2:ℝ)) ≤ (289:ℝ) / 5875 by norm_num)
    rwa [h23] at h
  · rw [pmOrthoCosThreeMul_p35,
      Real.cos_arccos (by norm_num : (-1:ℝ) ≤ 289 / 5875)
        (by norm_num : (289:ℝ) / 5875 ≤ 1)]
    norm_num

/-- (pm16, sub-`5/2` scan) **The single-arc big-kill on the `47/20` band**:
an arc `u -> y1' -> y2' -> w` whose three projected steps carry the pm14
clean far windows and whose four norms meet the band (diagonal endpoints
`>= 2`, lifted projections `>= 47/20`) has displacement strictly below
`2 * pi - beta`. -/
private theorem pmOrthoOffArcBigKillSub25_p35 {ax u w y1' y2' : V3}
    (hu2 : (2:ℝ) ≤ ‖u‖) (hw2 : (2:ℝ) ≤ ‖w‖)
    (cy1 : (47:ℝ) / 20 ≤ ‖y1'‖) (cy2 : (47:ℝ) / 20 ≤ ‖y2'‖)
    (hchain : azim 0 ax u w
      = azim 0 ax u y1' + azim 0 ax y1' y2' + azim 0 ax y2' w)
    (hwin1 : azim 0 ax u y1'
        ≤ Real.arccos ((‖u‖ ^ 2 + ‖y1'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖u‖ * ‖y1'‖))))
    (hwin2 : azim 0 ax y1' y2'
        ≤ Real.arccos ((‖y1'‖ ^ 2 + ‖y2'‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y1'‖ * ‖y2'‖))))
    (hwin3 : azim 0 ax y2' w
        ≤ Real.arccos ((‖y2'‖ ^ 2 + ‖w‖ ^ 2 - cstab ^ 2)
          / (2 * (‖y2'‖ * ‖w‖)))) :
    azim 0 ax u w + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have h2y1 : (2:ℝ) ≤ ‖y1'‖ := le_trans (by norm_num) cy1
  have h2y2 : (2:ℝ) ≤ ‖y2'‖ := le_trans (by norm_num) cy2
  have hc1 := pmOrthoOffStepCapSub25_p35 (Or.inl ⟨hu2, cy1⟩) hwin1
  have hc2 := pmOrthoOffStepCapSub25_p35 (Or.inl ⟨h2y1, cy2⟩) hwin2
  have hc3 := pmOrthoOffStepCapSub25_p35 (Or.inr ⟨cy2, hw2⟩) hwin3
  obtain ⟨hhi, hcos3⟩ := pmOrthoOffSub25PhiCaps_p35
  have hdlt : -(14709:ℝ) / 100000 < -(10601 / 80000) := by norm_num
  rw [hchain]
  exact pmOrthoOffArcThreeCapGen_p35 hc1 hc2 hc3 hhi hcos3 hdlt

/-- (pm16, sub-`5/2` scan) **THE TWO-ARC SQUEEZE, `47/20`-band form (the
reduced CAPSTONE)**: the pm15 core `pmOrthoOffTwoArcSqueeze_p35` with the
four clamp hypotheses weakened from `5/2` to `47/20` — every other
hypothesis verbatim.  The full sub-`5/2` band `[47/20, 5/2)` is thereby
closed unconditionally; what remains genuinely free is the sub-`47/20`
quadrant (the pm9 micro-azimuth phenomenon lives there), sized by
`pmOrthoOffDiagNearWedge_p35` / `pmOrthoOffSubQuadResidue_p35` below. -/
private theorem pmOrthoOffTwoArcSqueezeSub25_p35
    {ax u w y1 y2 z1 z2 y1' y2' z1' z2' : V3} {t1 t2 s1 s2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3)) (hz10 : z1' ≠ (0:V3)) (hz20 : z2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1o : (z1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz2o : (z2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax)
    (hz1 : z1 = z1' + s1 • ax) (hz2 : z2 = z2' + s2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (cy1 : (47:ℝ) / 20 ≤ ‖y1'‖) (cy2 : (47:ℝ) / 20 ≤ ‖y2'‖)
    (cz1 : (47:ℝ) / 20 ≤ ‖z1'‖) (cz2 : (47:ℝ) / 20 ≤ ‖z2'‖)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab) (e3 : dist y2 w ≤ cstab)
    (f1 : dist w z1 ≤ cstab) (f2 : dist z1 z2 ≤ cstab) (f3 : dist z2 u ≤ cstab)
    (ed : dist u w ≤ cstab) (hdg : (2:ℝ) ≤ dist u w)
    (r1 : (2:ℝ) ≤ dist u y1) (r2 : (2:ℝ) ≤ dist y1 y2) (r3 : (2:ℝ) ≤ dist y2 w)
    (r4 : (2:ℝ) ≤ dist w z1) (r5 : (2:ℝ) ≤ dist z1 z2) (r6 : (2:ℝ) ≤ dist z2 u)
    (h1 : azim 0 ax u y1' ≤ azim 0 ax u y2')
    (h2 : azim 0 ax u y2' ≤ azim 0 ax u w)
    (hp1 : azim 0 ax u y1' ≤ Real.pi) (hp2 : azim 0 ax y1' y2' ≤ Real.pi)
    (hp3 : azim 0 ax y2' w ≤ Real.pi)
    (g1 : azim 0 ax w z1' ≤ azim 0 ax w z2')
    (g2 : azim 0 ax w z2' ≤ azim 0 ax w u)
    (hq1 : azim 0 ax w z1' ≤ Real.pi) (hq2 : azim 0 ax z1' z2' ≤ Real.pi)
    (hq3 : azim 0 ax z2' u ≤ Real.pi) :
    False := by
  have cap1 := pmOrthoOffMidArcWindows_p35 hax0 hu0 hw0 hy10 hy20 hU hW hy1o hy2o
    hy1 hy2 e1 e2 e3 r1 r2 r3 h1 h2 hp1 hp2 hp3
  have cap2 := pmOrthoOffMidArcWindows_p35 (u := w) (w := u) (y1 := z1) (y2 := z2)
    (y1' := z1') (y2' := z2') (t1 := s1) (t2 := s2)
    hax0 hw0 hu0 hz10 hz20 hW hU hz1o hz2o hz1 hz2 f1 f2 f3 r4 r5 r6 g1 g2 hq1 hq2 hq3
  have kb1 := pmOrthoOffArcBigKillSub25_p35 hu2 hw2 cy1 cy2
    cap1.1 cap1.2.1 cap1.2.2.2.1 cap1.2.2.2.2.2.1
  have kb2 := pmOrthoOffArcBigKillSub25_p35 (u := w) (w := u) (y1' := z1') (y2' := z2')
    hw2 hu2 cz1 cz2 cap2.1 cap2.2.1 cap2.2.2.2.1 cap2.2.2.2.2.2.1
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncw := pmAxisOrthoNC_p35 hax0 hw0 hW
  have hwune : azim 0 ax w u ≠ 0 :=
    pmOrthoTriAzimNe0_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact hdg)
  have hcompl := azim_compl (z := (0:V3)) (w := ax) (w1 := w) (w2 := u) hncw hncu
  rw [if_neg hwune] at hcompl
  rcases pmOrthoTriFarSplit_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact ed) with hnear | hfar
  · exfalso
    rw [hcompl] at kb1
    linarith
  · exfalso
    linarith

/-- (pm16, sub-`5/2` scan) **The diagonal near-wedge pin (arc-2 clamped)**:
with the SECOND arc's lifted projections clamped at `47/20`, the far-wedge
branch of the diagonal dies against the clamped arc's three-step kill
ALONE — so the diagonal azimuth `azim w u` is pinned below `2 * pi - beta`
unconditionally, with NO hypothesis on the first arc's projections.  This
is the first half of the honest sizing of the sub-`47/20` quadrant: any
surviving configuration (in particular any with a sub-`47/20` projection
on the first arc) has its diagonal in the near wedge `azim w u <= beta`,
so the first arc must carry the full displacement `>= 2 * pi - beta`. -/
private theorem pmOrthoOffDiagNearWedge_p35 {ax u w z1 z2 z1' z2' : V3}
    {s1 s2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hz10 : z1' ≠ (0:V3)) (hz20 : z2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1o : (z1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz2o : (z2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1 : z1 = z1' + s1 • ax) (hz2 : z2 = z2' + s2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hw2 : (2:ℝ) ≤ ‖w‖)
    (cz1 : (47:ℝ) / 20 ≤ ‖z1'‖) (cz2 : (47:ℝ) / 20 ≤ ‖z2'‖)
    (f1 : dist w z1 ≤ cstab) (f2 : dist z1 z2 ≤ cstab) (f3 : dist z2 u ≤ cstab)
    (r4 : (2:ℝ) ≤ dist w z1) (r5 : (2:ℝ) ≤ dist z1 z2) (r6 : (2:ℝ) ≤ dist z2 u)
    (g1 : azim 0 ax w z1' ≤ azim 0 ax w z2')
    (g2 : azim 0 ax w z2' ≤ azim 0 ax w u)
    (hq1 : azim 0 ax w z1' ≤ Real.pi) (hq2 : azim 0 ax z1' z2' ≤ Real.pi)
    (hq3 : azim 0 ax z2' u ≤ Real.pi) :
    azim 0 ax w u + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have cap2 := pmOrthoOffMidArcWindows_p35 (u := w) (w := u) (y1 := z1) (y2 := z2)
    (y1' := z1') (y2' := z2') (t1 := s1) (t2 := s2)
    hax0 hw0 hu0 hz10 hz20 hW hU hz1o hz2o hz1 hz2 f1 f2 f3 r4 r5 r6 g1 g2 hq1 hq2 hq3
  exact pmOrthoOffArcBigKillSub25_p35 (u := w) (w := u) (y1' := z1') (y2' := z2')
    hw2 hu2 cz1 cz2 cap2.1 cap2.2.1 cap2.2.2.2.1
    cap2.2.2.2.2.2.1

/-- (pm16, sub-`5/2` scan) **THE SUB-QUADRANT RESIDUE (honest sizing)**:
in the CAPSTONE configuration with only ONE projection left unclamped
(`y1'` — the sub-`47/20` quadrant proper), the two projected steps
ADJACENT to the small projection must sum past
`2 * pi - beta - arccos (289/5875) ≈ 175.2°`: the near-wedge pin
(`pmOrthoOffDiagNearWedge_p35`) forces the first arc to carry the full
`2 * pi - beta` displacement, the third step stays under the `47/20`-band
cap, and the chain splits the rest onto the two steps touching `y1'`.
Any surviving sub-`47/20` configuration therefore bends hard around its
small projection — the feed shape the pm12 coupling account consumes. -/
private theorem pmOrthoOffSubQuadResidue_p35
    {ax u w y1 y2 z1 z2 y1' y2' z1' z2' : V3} {t1 t2 s1 s2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3)) (hz10 : z1' ≠ (0:V3)) (hz20 : z2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1o : (z1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz2o : (z2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax)
    (hz1 : z1 = z1' + s1 • ax) (hz2 : z2 = z2' + s2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (hlt : ‖y1'‖ < (47:ℝ) / 20)
    (cy2 : (47:ℝ) / 20 ≤ ‖y2'‖)
    (cz1 : (47:ℝ) / 20 ≤ ‖z1'‖) (cz2 : (47:ℝ) / 20 ≤ ‖z2'‖)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab) (e3 : dist y2 w ≤ cstab)
    (f1 : dist w z1 ≤ cstab) (f2 : dist z1 z2 ≤ cstab) (f3 : dist z2 u ≤ cstab)
    (ed : dist u w ≤ cstab) (hdg : (2:ℝ) ≤ dist u w)
    (r1 : (2:ℝ) ≤ dist u y1) (r2 : (2:ℝ) ≤ dist y1 y2) (r3 : (2:ℝ) ≤ dist y2 w)
    (r4 : (2:ℝ) ≤ dist w z1) (r5 : (2:ℝ) ≤ dist z1 z2) (r6 : (2:ℝ) ≤ dist z2 u)
    (h1 : azim 0 ax u y1' ≤ azim 0 ax u y2')
    (h2 : azim 0 ax u y2' ≤ azim 0 ax u w)
    (hp1 : azim 0 ax u y1' ≤ Real.pi) (hp2 : azim 0 ax y1' y2' ≤ Real.pi)
    (hp3 : azim 0 ax y2' w ≤ Real.pi)
    (g1 : azim 0 ax w z1' ≤ azim 0 ax w z2')
    (g2 : azim 0 ax w z2' ≤ azim 0 ax w u)
    (hq1 : azim 0 ax w z1' ≤ Real.pi) (hq2 : azim 0 ax z1' z2' ≤ Real.pi)
    (hq3 : azim 0 ax z2' u ≤ Real.pi) :
    (2:ℝ) * Real.pi - Real.arccos (-(10601 / 80000))
        - Real.arccos ((289:ℝ) / 5875)
      ≤ azim 0 ax u y1' + azim 0 ax y1' y2' := by
  have cap1 := pmOrthoOffMidArcWindows_p35 hax0 hu0 hw0 hy10 hy20 hU hW hy1o hy2o
    hy1 hy2 e1 e2 e3 r1 r2 r3 h1 h2 hp1 hp2 hp3
  have hR1 := pmOrthoOffDiagNearWedge_p35 hax0 hu0 hw0 hz10 hz20 hU hW hz1o hz2o
    hz1 hz2 hu2 hw2 cz1 cz2 f1 f2 f3 r4 r5 r6 g1 g2 hq1 hq2 hq3
  have h2y2 : (2:ℝ) ≤ ‖y2'‖ := le_trans (by norm_num) cy2
  have hS3 := pmOrthoOffStepCapSub25_p35 (Or.inr ⟨cy2, hw2⟩) cap1.2.2.2.2.2.1
  have hS3' : azim 0 ax u w
      ≤ azim 0 ax u y1' + azim 0 ax y1' y2' + Real.arccos ((289:ℝ) / 5875) := by
    rw [cap1.1]
    linarith
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncw := pmAxisOrthoNC_p35 hax0 hw0 hW
  have hwune : azim 0 ax w u ≠ 0 :=
    pmOrthoTriAzimNe0_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact hdg)
  have hcompl := azim_compl (z := (0:V3)) (w := ax) (w1 := w) (w2 := u) hncw hncu
  rw [if_neg hwune] at hcompl
  rcases pmOrthoTriFarSplit_p35 hax0 hw0 hu0 hncw hncu hW hU hw2 hwa hu2 hua
      (by rw [dist_comm]; exact ed) with hnear | hfar
  · linarith
  · exfalso
    linarith

-- pm16 axcheck tail (probe only; dropped from the kit proper)

/-! ## planemiss17 rungs (lkgrqui-planemiss17-w3, 2026-10-28)

The **(ii) coupling-account consumption interface** for the last free
sub-quadrant of the LA35 root `pmPlaneCrowding_p35`.  pm16 closed the
`[47/20, 5/2)` clamp band and pinned the sub-`47/20` residue
(`pmOrthoOffSubQuadResidue_p35`): any surviving configuration bends its
first arc hard, carrying `2 * pi - beta - arccos (289/5875) = 175.2°` of
projected step sum on the two steps that touch the small projection.
The one datum the CAPSTONE face lacks is an UPPER bound on the
ring-distance-2 JUMP CHORD `dist u y2` (`isScsV39` only gives `2 <=`).
This wave interfaces that datum without doing the pm12 (ii) coupling
account itself:

- `pmOrthoOffJumpCosPin_p35` — the trig constant behind the kill: the pin
  threshold `th0 := 2 * pi - beta - phi` has `cos th0 <= -9963/10000`
  (exact rational sine floors `sin beta >= 79294/80000`,
  `sin phi >= 11735/11750`).
- `pmOrthoOffJumpThetaPi_p35` / `pmOrthoOffJumpThetaNonneg_p35` — the
  threshold sits in `[0, pi]` (`beta + phi >= pi` is exact through the
  `cos beta <= -cos phi` antitone reading).
- `pmOrthoOffJumpChordWindow_p35` — the bridge: a jump chord
  `dist u y2 <= 399/100` squeezes the jump azimuth `azim 0 ax u y2'`
  under `arccos (-79201/80000) ~ 171.9°` (the far window read at the
  projected pair `(u, y2')` with the height term dropped through the
  two-point Pythagoras; `2 <=` on both norms is the annulus floor).
- `pmOrthoOffSubQuadKill_p35` — **THE CONDITIONAL CAPSTONE**: the pm16
  residue hypothesis face VERBATIM + the jump-chord upper bound
  `dist u y2 <= 399/100` + the jump-pair `pi` bound `azim u y2' <= pi`
  (a direction-feed datum of the same species as `hp1..hp3`) gives
  `False`.  The pin lifts the jump azimuth past `th0` (cosine at most
  `-0.9963`); the chord window caps it under `arccos (-0.9900125)`;
  `cos` monotonicity on `[0, pi]` leaves no room.
- `pmOrthoOffArcThetaCapGen_p35` / `pmOrthoOffArcTriCapGen_p35` — the
  **dual-constant (end/mid different caps) three-step engine, generic
  form**: three caps `c1 c2 c3` (end/mid split = `c2 = c3`; the pm16
  uniform engine `pmOrthoOffArcThreeCapGen_p35` = `c1 = c2 = c3`) whose
  threshold `2 * e + m`-type sum lies in `[pi, 2 * pi]` with
  `cos (c1 + c2 + c3) <= d < cos beta`, and three capped steps plus beta
  stay under the full turn.  This is the engine shape for the
  `c* ~ 2.2` end/mid split push recorded in the pm16 account.
- `pmOrthoOffCapFracEnd225_p35` — the **coupling-floor cap adapter**: a
  projected pair with the annulus floor `2 <= p` and a coupling floor
  `9/4 <= q` has its clean far window fraction at least `1/3750` (the
  exact value at `(p, q) = (2, 9/4)`; `p`-monotone while `q ^ 2 <=
  cstab ^ 2` through the `(p - 2) * (2 * p + cstab ^ 2 - q ^ 2)`
  factorization, and `>= 1 - cstab ^ 2 / (2 * p * q) >= 1 - 9.0601/12`
  by AM-GM once `q >= 3`).  With a pm12 (ii) coupling floor
  `norm y1' >= 9/4` on the small projection this caps BOTH steps
  touching it (`(u, y1')` and `(y1', y2')`).
- `pmOrthoOffArcDualCap225_p35` — engine validation at the `9/4` point:
  caps `{arccos (1/3750), arccos (1/3750), arccos (5083/35250)}` die
  against beta (exact rational double-and-add angle bookkeeping).  Honest
  note: the third cap is TIGHTER than the pm16 band cap
  `arccos (289/5875)` that the `(y2', w)` window currently delivers, so
  this instance validates the engine and sizes the docking requirement
  (a `y2'`-side coupling floor `~ 2.56` would supply it) — it is not yet
  a kill on the live window data.

All pieces are new lemmas with zero `sorry`; the residual root
`pmPlaneCrowding_p35` is untouched.  The jump-chord bound and the
jump-pair `pi` bound are EXPLICIT interface hypotheses — see the lane
DELIVERY for the pm12 post-report docking checklist. -/

/-- (pm17, ii-interface) The kill threshold `2 * pi - beta - phi` has
cosine at most `-9963/10000`: `cos (2 * pi - (beta + phi)) = cos (beta +
phi) = cos beta * cos phi - sin beta * sin phi` with the exact rational
sine floors `sin beta >= 79294/80000` (`79294 ^ 2 + 10601 ^ 2 <=
80000 ^ 2`) and `sin phi >= 11735/11750` (`11735 ^ 2 + (2 * 289) ^ 2 <=
(2 * 5875) ^ 2`). -/
private theorem pmOrthoOffJumpCosPin_p35 :
    Real.cos ((2:ℝ) * Real.pi - Real.arccos (-(10601 / 80000))
        - Real.arccos ((289:ℝ) / 5875))
      ≤ -(9963:ℝ) / 10000 := by
  have hβc : Real.cos (Real.arccos (-(10601 / 80000))) = -(10601 / 80000) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hφc : Real.cos (Real.arccos ((289:ℝ) / 5875)) = (289:ℝ) / 5875 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hβs : Real.sin (Real.arccos (-(10601 / 80000)))
      = Real.sqrt ((1:ℝ) - (-(10601 / 80000)) ^ 2) := Real.sin_arccos _
  have hφs : Real.sin (Real.arccos ((289:ℝ) / 5875))
      = Real.sqrt ((1:ℝ) - ((289:ℝ) / 5875) ^ 2) := Real.sin_arccos _
  have hper : Real.cos ((2:ℝ) * Real.pi - (Real.arccos (-(10601 / 80000))
        + Real.arccos ((289:ℝ) / 5875)))
      = Real.cos (Real.arccos (-(10601 / 80000))
        + Real.arccos ((289:ℝ) / 5875)) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have hre : ((2:ℝ) * Real.pi - Real.arccos (-(10601 / 80000))
      - Real.arccos ((289:ℝ) / 5875))
      = (2:ℝ) * Real.pi - (Real.arccos (-(10601 / 80000))
        + Real.arccos ((289:ℝ) / 5875)) := by ring
  have hadd : Real.cos (Real.arccos (-(10601 / 80000))
      + Real.arccos ((289:ℝ) / 5875))
      = Real.cos (Real.arccos (-(10601 / 80000)))
        * Real.cos (Real.arccos ((289:ℝ) / 5875))
        - Real.sin (Real.arccos (-(10601 / 80000)))
          * Real.sin (Real.arccos ((289:ℝ) / 5875)) :=
    Real.cos_add _ _
  have hsq1 : ((79294:ℝ) / 80000) ^ 2
      ≤ (1:ℝ) - (-(10601 / 80000)) ^ 2 := by norm_num
  have hsb : ((79294:ℝ) / 80000)
      ≤ Real.sin (Real.arccos (-(10601 / 80000))) := by
    rw [hβs]
    exact Real.le_sqrt_of_sq_le hsq1
  have hsq2 : ((11735:ℝ) / 11750) ^ 2
      ≤ (1:ℝ) - ((289:ℝ) / 5875) ^ 2 := by norm_num
  have hsf : ((11735:ℝ) / 11750)
      ≤ Real.sin (Real.arccos ((289:ℝ) / 5875)) := by
    rw [hφs]
    exact Real.le_sqrt_of_sq_le hsq2
  have hβs0 : (0:ℝ) ≤ Real.sin (Real.arccos (-(10601 / 80000))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hφs0 : (0:ℝ) ≤ Real.sin (Real.arccos ((289:ℝ) / 5875)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hprod : ((79294:ℝ) / 80000 * (11735 / 11750))
      ≤ Real.sin (Real.arccos (-(10601 / 80000)))
        * Real.sin (Real.arccos ((289:ℝ) / 5875)) :=
    mul_le_mul hsb hsf (by norm_num) hβs0
  rw [hre, hper, hadd, hβc, hφc]
  linarith

/-- (pm17, ii-interface) The kill threshold sits at most `pi`:
`beta + phi >= pi`, exact since `cos beta = -10601/80000 <= -289/5875 =
-cos phi` and `cos (pi - phi) = -cos phi` with `arccos` antitone. -/
private theorem pmOrthoOffJumpThetaPi_p35 :
    (2:ℝ) * Real.pi - Real.arccos (-(10601 / 80000))
        - Real.arccos ((289:ℝ) / 5875) ≤ Real.pi := by
  have hφ0 : (0:ℝ) ≤ Real.arccos ((289:ℝ) / 5875) := Real.arccos_nonneg _
  have hφπ : Real.arccos ((289:ℝ) / 5875) ≤ Real.pi := Real.arccos_le_pi _
  have hπφ : Real.pi - Real.arccos ((289:ℝ) / 5875)
      = Real.arccos (-(289 / 5875)) := by
    rw [← Real.arccos_cos (show (0:ℝ) ≤ Real.pi - Real.arccos ((289:ℝ) / 5875) by linarith)
      (show Real.pi - Real.arccos ((289:ℝ) / 5875) ≤ Real.pi by linarith),
      Real.cos_pi_sub,
      Real.cos_arccos (by norm_num : (-1:ℝ) ≤ 289 / 5875)
        (by norm_num : (289:ℝ) / 5875 ≤ 1)]
  have hle := Real.arccos_le_arccos
    (show (-(10601 / 80000):ℝ) ≤ -(289 / 5875) by norm_num)
  rw [← hπφ] at hle
  linarith

/-- (pm17, ii-interface) The kill threshold is nonnegative (both `beta`
and `phi` are at most `2 * pi / 3`). -/
private theorem pmOrthoOffJumpThetaNonneg_p35 :
    (0:ℝ) ≤ (2:ℝ) * Real.pi - Real.arccos (-(10601 / 80000))
        - Real.arccos ((289:ℝ) / 5875) := by
  obtain ⟨hφ23, -⟩ := pmOrthoOffSub25PhiCaps_p35
  have hβ23 := pmOrthoTriBetaLe_p35
  have hπpos := Real.pi_pos
  linarith

/-- (pm17, ii-interface) **The jump-chord window**: a ring-distance-2
jump `u -> y2` whose lifted chord is capped at `399/100` squeezes the
projected jump azimuth under `arccos (-79201/80000)` — the far window
read at the projected pair `(u, y2')` with the height term dropped
(two-point Pythagoras) and the annulus floors `2 <=` on both norms:
`cos(azim) * (norm u * norm y2') = u . y2' >= (4 + 4 - (399/100) ^ 2) / 2
= -79201/20000` against a product of norms `>= 4`. -/
private theorem pmOrthoOffJumpChordWindow_p35 {ax u y2 y2' : V3} {t2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hy20 : y2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2 : y2 = y2' + t2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hy22 : (2:ℝ) ≤ ‖y2'‖)
    (hpi : azim 0 ax u y2' ≤ Real.pi)
    (hj : dist u y2 ≤ (399:ℝ) / 100) :
    azim 0 ax u y2' ≤ Real.arccos (-(79201:ℝ) / 80000) := by
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncy2 := pmAxisOrthoNC_p35 hax0 hy20 hy2o
  have hcos := pmAzimOrthoCos_p35 hax0 hu0 hy20 hncu hncy2 hU hy2o
  have hlift : u = u + (0:ℝ) • ax := by rw [zero_smul, add_zero]
  have hpyth := pmOrthoOffTwoPythDist_p35 (y1 := u) (y1' := u) (t1 := (0:ℝ))
    hlift hU hy2 hy2o
  have hdsq : dist u y2' ^ 2 ≤ ((399:ℝ) / 100) ^ 2 := by
    have h0 : (0:ℝ) ≤ (0 - t2) ^ 2 * ‖ax‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h1 : dist u y2 ^ 2 ≤ ((399:ℝ) / 100) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hj 2
    linarith
  have hn1 : (2:ℝ) ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hu2 2
  have hn2 : (2:ℝ) ^ 2 ≤ ‖y2'‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hy22 2
  have hdot : (-(79201:ℝ) / 20000
      ≤ (u : Fin 3 → ℝ) ⬝ᵥ (y2' : Fin 3 → ℝ)) := by
    have hid := pmDotNormDist_p35 u y2'
    linarith
  have hd0 : (0:ℝ) < ‖u‖ * ‖y2'‖ :=
    mul_pos (norm_pos_iff.mpr hu0) (norm_pos_iff.mpr hy20)
  have hM4 : (4:ℝ) ≤ ‖u‖ * ‖y2'‖ := by
    have h := mul_le_mul hu2 hy22 (by norm_num) (norm_nonneg u)
    linarith
  have hkey : (-(79201:ℝ) / 80000) * (‖u‖ * ‖y2'‖)
      ≤ Real.cos (azim 0 ax u y2') * (‖u‖ * ‖y2'‖) := by
    have hlhs : (-(79201:ℝ) / 80000) * (‖u‖ * ‖y2'‖)
        ≤ (-(79201:ℝ) / 80000) * 4 :=
      mul_le_mul_of_nonpos_left hM4 (by norm_num)
    rw [hcos]
    linarith
  refine pmOrthoOffAzimLeOfCosGe_p35 hpi ?_
  have hrew : Real.cos (azim 0 ax u y2')
      = Real.cos (azim 0 ax u y2') * (‖u‖ * ‖y2'‖) / (‖u‖ * ‖y2'‖) := by
    field_simp
  rw [hrew, le_div_iff₀ hd0]
  exact hkey

/-- (pm17, ii-interface) **THE SUB-QUADRANT KILL (conditional CAPSTONE)**:
the pm16 residue configuration — hypothesis face VERBATIM, i.e.
`pmOrthoOffSubQuadResidue_p35`'s 49 explicit hypotheses one-for-one —
plus the pm12 (ii) coupling-account interface: the jump chord
`dist u y2` (ring distance 2) upper-bounded at `399/100`, and the
jump-pair `pi` bound `azim 0 ax u y2' <= Real.pi` (direction-feed datum,
same species as `hp1..hp3`).  The 175.2° pin lifts the jump azimuth past
`th0 = 2 * pi - beta - phi` (cosine at most `-9963/10000`); the jump
window caps it under `arccos (-79201/80000)` (cosine at least
`-79201/80000 = -0.9900125`); `cos` monotonicity on `[0, pi]` leaves no
room. -/
private theorem pmOrthoOffSubQuadKill_p35
    {ax u w y1 y2 z1 z2 y1' y2' z1' z2' : V3} {t1 t2 s1 s2 : ℝ}
    (hax0 : ax ≠ (0:V3))
    (hu0 : u ≠ (0:V3)) (hw0 : w ≠ (0:V3))
    (hy10 : y1' ≠ (0:V3)) (hy20 : y2' ≠ (0:V3)) (hz10 : z1' ≠ (0:V3)) (hz20 : z2' ≠ (0:V3))
    (hU : (u : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hW : (w : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1o : (y1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy2o : (y2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz1o : (z1' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hz2o : (z2' : Fin 3 → ℝ) ⬝ᵥ (ax : Fin 3 → ℝ) = 0)
    (hy1 : y1 = y1' + t1 • ax) (hy2 : y2 = y2' + t2 • ax)
    (hz1 : z1 = z1' + s1 • ax) (hz2 : z2 = z2' + s2 • ax)
    (hu2 : (2:ℝ) ≤ ‖u‖) (hua : ‖u‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwa : ‖w‖ ≤ 2 * h0)
    (hlt : ‖y1'‖ < (47:ℝ) / 20)
    (cy2 : (47:ℝ) / 20 ≤ ‖y2'‖)
    (cz1 : (47:ℝ) / 20 ≤ ‖z1'‖) (cz2 : (47:ℝ) / 20 ≤ ‖z2'‖)
    (e1 : dist u y1 ≤ cstab) (e2 : dist y1 y2 ≤ cstab) (e3 : dist y2 w ≤ cstab)
    (f1 : dist w z1 ≤ cstab) (f2 : dist z1 z2 ≤ cstab) (f3 : dist z2 u ≤ cstab)
    (ed : dist u w ≤ cstab) (hdg : (2:ℝ) ≤ dist u w)
    (r1 : (2:ℝ) ≤ dist u y1) (r2 : (2:ℝ) ≤ dist y1 y2) (r3 : (2:ℝ) ≤ dist y2 w)
    (r4 : (2:ℝ) ≤ dist w z1) (r5 : (2:ℝ) ≤ dist z1 z2) (r6 : (2:ℝ) ≤ dist z2 u)
    (h1 : azim 0 ax u y1' ≤ azim 0 ax u y2')
    (h2 : azim 0 ax u y2' ≤ azim 0 ax u w)
    (hp1 : azim 0 ax u y1' ≤ Real.pi) (hp2 : azim 0 ax y1' y2' ≤ Real.pi)
    (hp3 : azim 0 ax y2' w ≤ Real.pi)
    (g1 : azim 0 ax w z1' ≤ azim 0 ax w z2')
    (g2 : azim 0 ax w z2' ≤ azim 0 ax w u)
    (hq1 : azim 0 ax w z1' ≤ Real.pi) (hq2 : azim 0 ax z1' z2' ≤ Real.pi)
    (hq3 : azim 0 ax z2' u ≤ Real.pi)
    (hjr : (2:ℝ) ≤ dist u y2)
    (hjump : dist u y2 ≤ (399:ℝ) / 100)
    (hpiu : azim 0 ax u y2' ≤ Real.pi) :
    False := by
  have hpin := pmOrthoOffSubQuadResidue_p35 hax0 hu0 hw0 hy10 hy20 hz10 hz20 hU hW
    hy1o hy2o hz1o hz2o hy1 hy2 hz1 hz2 hu2 hua hw2 hwa hlt cy2 cz1 cz2
    e1 e2 e3 f1 f2 f3 ed hdg r1 r2 r3 r4 r5 r6 h1 h2 hp1 hp2 hp3 g1 g2
    hq1 hq2 hq3
  have hncu := pmAxisOrthoNC_p35 hax0 hu0 hU
  have hncy1 := pmAxisOrthoNC_p35 hax0 hy10 hy1o
  have hncy2 := pmAxisOrthoNC_p35 hax0 hy20 hy2o
  have hchain := pmAzimNormalChain_p35 (a := u) (x := y1') (y := y2')
    hax0 hncu hncy1 hncy2 h1
  have h2y2 : (2:ℝ) ≤ ‖y2'‖ := le_trans (by norm_num) cy2
  have hjw := pmOrthoOffJumpChordWindow_p35 hax0 hu0 hy20 hU hy2o hy2 hu2 h2y2
    hpiu hjump
  have hΘn := pmOrthoOffJumpThetaNonneg_p35
  have hΘπ := pmOrthoOffJumpThetaPi_p35
  have hΘcos := pmOrthoOffJumpCosPin_p35
  rw [← hchain] at hpin
  have hmono := pmOrthoTriCosMono_p35 hΘn hpin hpiu
  have hcoslo := pmOrthoTriCosMono_p35 (azim_nonneg 0 ax u y2') hjw
    (Real.arccos_le_pi _)
  rw [Real.cos_arccos (by norm_num : (-1:ℝ) ≤ -(79201:ℝ) / 80000)
    (by norm_num : -(79201:ℝ) / 80000 ≤ 1)] at hcoslo
  have hlt2 : -(9963:ℝ) / 10000 < -(79201:ℝ) / 80000 := by norm_num
  linarith

/-- (pm17, b) **The theta-cap core** (generic): `cos th <= d < cos beta`
with `th` in `[pi, 2 * pi]` forces `th + beta < 2 * pi` — the
`2 * pi`-periodicity move (`cos (2 * pi - th) = cos th`) plus `cos`
monotonicity on `[0, pi]`. -/
private theorem pmOrthoOffArcThetaCapGen_p35 {th d : ℝ}
    (hcos : Real.cos th ≤ d) (hlo : Real.pi ≤ th) (hhi : th ≤ 2 * Real.pi)
    (hdlt : d < -(10601 / 80000)) :
    th + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have hrev : Real.arccos (-(10601 / 80000)) < 2 * Real.pi - th := by
    by_contra hge
    have hle : 2 * Real.pi - th ≤ Real.arccos (-(10601 / 80000)) :=
      le_of_not_gt hge
    have hx0 : (0:ℝ) ≤ 2 * Real.pi - th := by linarith
    have hβ23 := pmOrthoTriBetaLe_p35
    have hper : Real.cos (2 * Real.pi - th) = Real.cos th := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      ring
    have hm := pmOrthoTriCosMono_p35 hx0 hle (Real.arccos_le_pi _)
    rw [hper] at hm
    have hcb : Real.cos (Real.arccos (-(10601 / 80000))) = -(10601 / 80000) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    rw [hcb] at hm
    linarith
  linarith

/-- (pm17, b) **The dual-constant (end/mid) three-step engine, generic
form**: three caps `c1 c2 c3` (end/mid split = `c2 = c3`; the pm16
uniform engine `pmOrthoOffArcThreeCapGen_p35` is `c1 = c2 = c3`) whose
threshold `c1 + c2 + c3` lies in `[pi, 2 * pi]` with
`cos (c1 + c2 + c3) <= d < cos beta`: three capped steps plus beta stay
under the full turn. -/
private theorem pmOrthoOffArcTriCapGen_p35 {S1 S2 S3 c1 c2 c3 d : ℝ}
    (h1 : S1 ≤ c1) (h2 : S2 ≤ c2) (h3 : S3 ≤ c3)
    (hlo : Real.pi ≤ c1 + c2 + c3) (hhi : c1 + c2 + c3 ≤ 2 * Real.pi)
    (hcos : Real.cos (c1 + c2 + c3) ≤ d) (hdlt : d < -(10601 / 80000)) :
    S1 + S2 + S3 + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have hcap := pmOrthoOffArcThetaCapGen_p35 hcos hlo hhi hdlt
  linarith

/-- (pm17, b) **The coupling-floor cap adapter at `9/4`**: a projected
pair with the annulus floor `2 <= p` and a coupling floor `9/4 <= q` has
its clean far window fraction at least `1/3750` (the exact value at
`(2, 9/4)`).  While `q <= cstab` the fraction is `p`-monotone through
`(p - 2) * (2 * p + cstab ^ 2 - q ^ 2) >= 0` and floors at the `9/4`
tangent `(q - 9/4) * (q + 16867/7500) >= 0`; for `q >= cstab` AM-GM gives
`>= 1 - cstab ^ 2 / (2 * p * q) >= 1 - 9.0601 / 12 > 1/3750`. -/
private theorem pmOrthoOffCapFracEnd225_p35 {p q : ℝ}
    (h2p : (2:ℝ) ≤ p) (hq : (9:ℝ) / 4 ≤ q) :
    (1:ℝ) / 3750 ≤ (p ^ 2 + q ^ 2 - cstab ^ 2) / (2 * (p * q)) := by
  have hcs : cstab = 301 / 100 := by norm_num [cstab]
  rw [hcs]
  have hsqc : ((301:ℝ) / 100) ^ 2 = 90601 / 10000 := by norm_num
  rw [hsqc]
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le (by norm_num) h2p
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le (by norm_num) hq
  have hprod : (0:ℝ) < 2 * (p * q) := by linarith [mul_pos hp0 hq0]
  rcases lt_or_ge q ((301:ℝ) / 100) with hq3 | hq3
  · -- q <= cstab: p-monotone, floor at p = 2, then the 9/4 tangent
    have hCq : q ^ 2 ≤ (90601:ℝ) / 10000 := by
      have h1 : (0:ℝ) ≤ ((301:ℝ) / 100 - q) * (((301:ℝ) / 100) + q) :=
        mul_nonneg (by linarith) (by linarith)
      linear_combination h1
    have hden : (0:ℝ) ≤ 2 * p + 90601 / 10000 - q ^ 2 := by linarith
    have hE : (0:ℝ) ≤ (p - 2) * (2 * p + 90601 / 10000 - q ^ 2) :=
      mul_nonneg (by linarith) hden
    have hcross : ((2:ℝ) * (p ^ 2 + q ^ 2 - 90601 / 10000)
        - p * ((2:ℝ) ^ 2 + q ^ 2 - 90601 / 10000))
        = (p - 2) * (2 * p + 90601 / 10000 - q ^ 2) := by ring
    have hcross2 : p * ((2:ℝ) ^ 2 + q ^ 2 - 90601 / 10000)
        ≤ (2:ℝ) * (p ^ 2 + q ^ 2 - 90601 / 10000) := by
      linear_combination hE - hcross
    have hA2 : ((1:ℝ) / 3750) * ((2:ℝ) * (2 * q))
        ≤ (2:ℝ) ^ 2 + q ^ 2 - 90601 / 10000 := by
      have hpos : (0:ℝ) ≤ (q - 9 / 4) * (q + 16867 / 7500) :=
        mul_nonneg (by linarith) (by linarith)
      linear_combination hpos
    rw [le_div_iff₀ hprod]
    linear_combination (p / 2) * hA2 + (1 / 2:ℝ) * hcross2
  · -- q >= cstab: AM-GM gives the fraction >= 1 - 9.0601 / (2 * p * q)
    have hsum : (2:ℝ) * (p * q) ≤ p ^ 2 + q ^ 2 := by
      linear_combination (sq_nonneg (p - q))
    have h6 : (6:ℝ) ≤ p * q := by
      have h := mul_le_mul h2p hq3 (by norm_num) (le_of_lt hp0)
      linarith
    rw [le_div_iff₀ hprod]
    linarith

/-- (pm17, b) **Engine validation at the `9/4` coupling point**: caps
`arccos (1/3750)` on two steps and `arccos (5083/35250)` on the third
die against beta.  `cos (2 * arccos (1/3750) + arccos (5083/35250)) <=
-1341/10000 < -10601/80000` through the exact rational floors
`sin (arccos (1/3750)) >= 14062499/14062500` and
`sin (arccos (5083/35250)) >= 34881/35250`.  Honest note: the third cap
is tighter than the pm16 band cap the `(y2', w)` window currently
delivers — this sizes the docking requirement, not a live kill. -/
private theorem pmOrthoOffArcDualCap225_p35 {S1 S2 S3 : ℝ}
    (h1 : S1 ≤ Real.arccos ((1:ℝ) / 3750))
    (h2 : S2 ≤ Real.arccos ((1:ℝ) / 3750))
    (h3 : S3 ≤ Real.arccos ((5083:ℝ) / 35250)) :
    S1 + S2 + S3 + Real.arccos (-(10601 / 80000)) < 2 * Real.pi := by
  have hπpos := Real.pi_pos
  have hπ3 : (0:ℝ) ≤ Real.pi / 3 := by linarith
  have hπ3' : Real.pi / 3 ≤ Real.pi := by linarith
  have he1 : (1:ℝ) / 3750 ≤ Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]
    norm_num
  have he2 := Real.arccos_le_arccos he1
  rw [Real.arccos_cos hπ3 hπ3'] at he2
  have hm1 : (5083:ℝ) / 35250 ≤ Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]
    norm_num
  have hm2 := Real.arccos_le_arccos hm1
  rw [Real.arccos_cos hπ3 hπ3'] at hm2
  have he0 : Real.arccos ((1:ℝ) / 3750) ≤ Real.pi / 2 := by
    have h := Real.arccos_le_arccos (show (0:ℝ) ≤ (1:ℝ) / 3750 by norm_num)
    rwa [Real.arccos_zero] at h
  have hm0 : Real.arccos ((5083:ℝ) / 35250) ≤ Real.pi / 2 := by
    have h := Real.arccos_le_arccos (show (0:ℝ) ≤ (5083:ℝ) / 35250 by norm_num)
    rwa [Real.arccos_zero] at h
  have hcose : Real.cos (Real.arccos ((1:ℝ) / 3750)) = (1:ℝ) / 3750 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hcosm : Real.cos (Real.arccos ((5083:ℝ) / 35250)) = (5083:ℝ) / 35250 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hse : ((14062499:ℝ) / 14062500)
      ≤ Real.sin (Real.arccos ((1:ℝ) / 3750)) := by
    rw [Real.sin_arccos]
    exact Real.le_sqrt_of_sq_le (by norm_num : ((14062499:ℝ) / 14062500) ^ 2
      ≤ (1:ℝ) - ((1:ℝ) / 3750) ^ 2)
  have hsm : ((34881:ℝ) / 35250)
      ≤ Real.sin (Real.arccos ((5083:ℝ) / 35250)) := by
    rw [Real.sin_arccos]
    exact Real.le_sqrt_of_sq_le (by norm_num : ((34881:ℝ) / 35250) ^ 2
      ≤ (1:ℝ) - ((5083:ℝ) / 35250) ^ 2)
  have hcos2e : Real.cos ((2:ℝ) * Real.arccos ((1:ℝ) / 3750))
      = (2:ℝ) * ((1:ℝ) / 3750) ^ 2 - 1 := by
    rw [Real.cos_two_mul, hcose]
  have hsin2e : Real.sin ((2:ℝ) * Real.arccos ((1:ℝ) / 3750))
      = (2:ℝ) * Real.sin (Real.arccos ((1:ℝ) / 3750)) * ((1:ℝ) / 3750) := by
    rw [Real.sin_two_mul, hcose]
  have hA2' : ((2:ℝ) * (14062499:ℝ) / 14062500 * ((1:ℝ) / 3750))
      ≤ (2:ℝ) * Real.sin (Real.arccos ((1:ℝ) / 3750)) * ((1:ℝ) / 3750) :=
    mul_le_mul_of_nonneg_right (by linarith [hse]) (by norm_num)
  have hse' : (0:ℝ) ≤ (2:ℝ) * Real.sin (Real.arccos ((1:ℝ) / 3750))
      * ((1:ℝ) / 3750) :=
    mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _)
        (Real.arccos_le_pi _))) (by norm_num)
  have hshift : ((2:ℝ) * (14062499:ℝ) / 14062500 * ((1:ℝ) / 3750))
        * ((34881:ℝ) / 35250)
      ≤ (2:ℝ) * Real.sin (Real.arccos ((1:ℝ) / 3750)) * ((1:ℝ) / 3750)
        * Real.sin (Real.arccos ((5083:ℝ) / 35250)) :=
    mul_le_mul hA2' hsm (by norm_num) hse'
  have hterm : ((2:ℝ) * ((1:ℝ) / 3750) ^ 2 - 1) * ((5083:ℝ) / 35250)
      - ((2:ℝ) * (14062499:ℝ) / 14062500 * ((1:ℝ) / 3750)) * ((34881:ℝ) / 35250)
      ≤ -(1341:ℝ) / 10000 := by norm_num
  have hsum2 : Real.arccos ((1:ℝ) / 3750) + Real.arccos ((1:ℝ) / 3750)
      = (2:ℝ) * Real.arccos ((1:ℝ) / 3750) := by ring
  have hlo : Real.pi ≤ Real.arccos ((1:ℝ) / 3750) + Real.arccos ((1:ℝ) / 3750)
      + Real.arccos ((5083:ℝ) / 35250) := by linarith [he2, hm2]
  have hhi : Real.arccos ((1:ℝ) / 3750) + Real.arccos ((1:ℝ) / 3750)
      + Real.arccos ((5083:ℝ) / 35250) ≤ 2 * Real.pi := by
    linarith [he0, hm0]
  refine pmOrthoOffArcTriCapGen_p35 h1 h2 h3 hlo hhi ?_
    (show -(1341:ℝ) / 10000 < -(10601 / 80000) by norm_num)
  rw [hsum2, Real.cos_add ((2:ℝ) * Real.arccos ((1:ℝ) / 3750))
    (Real.arccos ((5083:ℝ) / 35250)), hcos2e, hsin2e, hcosm]
  linarith [hterm, hshift]

-- pm17 axcheck tail (probe only; dropped from the kit proper)
/-- **THE PLANE-CROWDING RESIDUAL** (lkgrqui-planemiss2-w3): two distinct,
mutually non-adjacent (scsDiag) ring vertices can not both lie in one dart
face plane `aff {0, vv j, vv (j+1)}`.  This single named root absorbs all
four azimuth corners C1–C4 of `sectorTriPlaneMiss_p35`: C1 at dart `j`
directly; C2 at dart `j + k - 1` (the span-face plane `aff {0, vv i,
vv (i+k-1)}` is the dart-`(i+k-1)` face plane by `wedgeVvAddK_p35`); C3/C4
at dart `j` with the flat-span rendering.  HOL route (TECOXBM.hl:311
`AFF_GT_INTER_AFF_SY` endgame): (i) the whole ring sits in every dart's
closed half-space (`pmCrossGeDart_p35`, closed in this file); (ii) an
in-plane vertex propagates plane membership to its ring neighbors by the
sign algebra `det(x, x⁺, b) = β·det(b, c, x⁺)`, `det(x, x⁺, c) =
-α·det(b, c, x⁺)` against the two neighbor darts' half-spaces; (iii) with
the whole ring coplanar, the planar winding + consecutive `b ≤ cstab` +
pairwise `2 ≤ a` at distinct residues (`isScsV39`) + `ncard + k ≤ 6` +
`dist u w ≤ cstab` contradict.

pm7 status (lkgrqui-planemiss7-w3): the statement is frozen verbatim; the
body now branches on the sector span `θ_j`.  Case `θ_j < π` is CLOSED: the
successor is forced off the dart plane (`pmEOffPlaneOfLtPi_p35`) and the
Fork-2 kill closes (`pmFork2Kill_p35`).  Case `θ_j = π` is reduced by the
closed flat-sector reducer (`pmBRootReduce_p35`): the span vertex `d` sits
in the plane on the negative `b`-side, and every placement of the successor
`e` either dies (cone kill / antipodal wedge) or leaves the winding-order
survivor data (negative `a`-coefficient, or the antipodal wedge with the
dart-`(j+1)` sector flat).  The residual root (single sorry below) is the
ring winding order + annulus metric squeeze over that survivor data.

pm8 status (lkgrqui-planemiss8-w3): the statement stays frozen verbatim; the
pm8 kit (between the flat-sector reducer and this theorem) globalizes every
residual leaf's dart half-space to the whole ring, flattens the successor
sector, and detects the capped-vertex quadrants, and its two globalizers are
wired into the case branches below; the residual root is now precisely the
planar winding order + annulus metric squeeze over that data (see the root
comment below for the exact next-lane roadmap).

pm9 status (lkgrqui-planemiss9-w3): the statement stays frozen verbatim; the
pm9 kit (between `pmFlatSuccPi_p35` and this theorem) closes the normal-axis
azimuth engine — the coerced cross-product axis is nonzero
(`pmNormalAxisNe_p35`), orthogonal plane vectors are never collinear with it
(`pmAxisOrthoNC_p35`), azimuth zero renders as open-ray + axis slack
(`pmAzimNormalRender0_p35`), the cosine identity `cos(azim 0 ax a x)·(‖a‖‖x‖)
= a⬝x` holds for axis-orthogonal `a, x` (`pmAzimOrthoCos_p35`, frame
computation), the cross-sign side placement `(a×x)·ax ≷ 0 ⟹ azim 0 ax a x ≶ π`
(`pmAzimOrthoSideGt/Lt_p35`), the FAN-free additive chain instance
(`pmAzimNormalChain_p35`), and the metric gap bounds (chord ≥ 2 ⟹ azimuthal
cos ≤ 2719/3969 `pmAzimOrthoGap46_p35`; chord ≤ cstab ⟹ cos ≥ −10601/80000
`pmAzimOrthoFarCos_p35`; the `[0, π]` arccos form `pmAzimOrthoGapGe_p35`).
All standard-three (axcheck-pm9.out). The residual root narrows to: the
azimuthal step bound is an IN-PLANE-pair statement — an off-plane vertex
(`n·v > 0`, small projection radius) admits an azimuthally tiny/backtracking
step at chord ∈ [2, cstab], so the winding kill needs the in-plane
run/squeeze endgame (see the root comment below). -/
private theorem pmPlaneCrowding_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (j : ℕ)
    (hu : ∃ c d : ℝ, u - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0))
    (hw : ∃ c d : ℝ, w - 0 = c • (vv j - 0) + d • (vv (j + 1) - 0)) : False := by
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  obtain ⟨-, hθle⟩ := wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan j
  -- THE SINGLE RESIDUAL ROOT (this theorem's own sorry, until closed): the
  -- winding-order root.  Leaves reaching it carry, after the two closed
  -- reducers: (R-flat) `θ_j = π` with `d = vv (j+k-1)` in the dart-`j`
  -- plane at negative `b`-coordinate, plus either the half-plane data
  -- (`α_u, α_w ≥ 0` when `e` is off the plane) or the antipodal-wedge data
  -- (`e` at negative `a`- and `b`-coordinate with the dart-`(j+1)` sector
  -- flat); or (R-tilt) the survivor `e` at negative `a`-coefficient.
  -- pm8 (lkgrqui-planemiss8-w3) globalizes every leaf's dart half-space to
  -- the whole ring (pmTiltUpperHalf_p35 / pmFlatAUpperHalf_p35, wired below),
  -- flattens the successor sector (`pmFlatSuccPi_p35`: the survivor forces
  -- `θ_{j+1} = π`), and detects capped-vertex quadrants (`pmCapQuadSucc_p35`
  -- / `pmCapQuadPred_p35`: an in-plane vertex with a capped neighbor is
  -- forced into `α ≤ 0 ∧ 0 ≤ β` resp. `0 ≤ α ∧ β ≤ 0`).  The remaining core
  -- is the planar winding order: polar angles via the normal-axis azimuth
  -- (`azim 0 (a×b) a y`, FAN-free chain by `azimAddTriple_p35` +
  -- `azim_compl`), the step bounds (chord ≤ cstab ⟹ step ≤ 97.63° by
  -- `pmFarCos_p35`; chord ≥ 2 ⟹ step ≥ 46.74° by `pmCosLe46_p35`), and the
  -- k ∈ {4,5,6} squeeze/counting (`pmDiag2Squeeze_p35` at the common
  -- run-neighbour; k = 6 via the counting conjunct, k ∈ {4,5} via
  -- ncard ≤ 2/1).  pm9 (lkgrqui-planemiss9-w3) closes the normal-axis
  -- azimuth ENGINE (pm9 kit above, all standard-three): with `axN := (a×b)`,
  -- `azim 0 axN a x` reads in-plane polar angles; azimuth zero = open
  -- `a`-ray (pmAzimNormalRender0_p35), `cos(azim)·(‖a‖‖x‖) = a⬝x`
  -- (pmAzimOrthoCos_p35), cross-sign placement `(a×x)·ax ≷ 0 ⟹ azim ≶ π`
  -- (pmAzimOrthoSideGt/Lt_p35), additive chain (pmAzimNormalChain_p35), and
  -- the metric gap bounds for axis-orthogonal pairs: chord ≥ 2 ⟹ azimuthal
  -- cos ≤ 2719/3969 (≥ 46.74° gap), chord ≤ cstab ⟹ cos ≥ −10601/80000
  -- (≤ 97.63° gap), plus the `[0, π]` arccos form (pmAzimOrthoGap46/
  -- FarCos/GapGe_p35).  REMAINING CORE (pm9 sizing finding): the step lower
  -- bound is an IN-PLANE-pair statement — an off-plane vertex with small
  -- projection radius admits an azimuthally tiny (even backtracking) step at
  -- chord ∈ [2, cstab], so the naive 3-step arc ≥ 140.2° account fails for
  -- off-plane runs; the kill needs (i) the d = 2 squeeze at the common
  -- in-plane neighbour (pmDiag2Squeeze_p35, blocked case via the quadrant
  -- route pmCapQuadSucc/Pred_p35 + pmNotSameRay_p35 — same-azimuth in-plane
  -- pairs are same-ray kills), (ii) the d = 3 counting/angle account after
  -- planarity of the arc is established (planarity propagation: a blocked
  -- in-plane triple forces neighbour darts' planes to coincide with P), and
  -- (iii) the wrap Σ gaps = 2π for in-plane runs.  DISCHARGES: next-lane
  -- input; the ladder pieces above are all closed (standard three).
  have hroot : False := by
    sorry
  rcases lt_or_eq_of_le hθle with hθlt | hθeq
  · -- Case A: θ_j < π (Fork-2 closed; the survivor leaf globalizes the
    -- dart-(j+1) half-space by the pm8 kit)
    rcases pmEOffPlaneOfLtPi_p35 hscs hdiag hBB hE hFF j hθlt with heP | hop
    · exact pmFork2Kill_p35 hscs hdiag hp hq hBB hE hFF j hu hw heP hθlt
    · have hup : ∀ y ∈ Set.range vv, (0:ℝ) ≤
          (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
            (y : Fin 3 → ℝ) :=
        fun y hy => pmTiltUpperHalf_p35 hscs hdiag hBB hE hFF j hop y hy
      exact hroot
  · -- Case B: θ_j = π: every reducer leaf globalizes the dart half-space
    -- (in-plane successor leaves via the survivor data, off-plane successor
    -- via the negative-b-side span vertex)
    obtain ⟨hdneg, hB1, hB2⟩ :=
      pmBRootReduce_p35 hscs hdiag hp hq hBB hE hFF j hu hw hθeq
    by_cases heP : ∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) +
      de • (vv (j + 1) - 0)
    · have hsurv : ∃ ce de : ℝ, vv (j + 1 + 1) - 0 = ce • (vv j - 0) +
          de • (vv (j + 1) - 0) ∧ ce < 0 := by
        rcases hB2 heP with h | h
        · exact h
        · obtain ⟨hanti, -⟩ := h
          obtain ⟨ce, de, hM, hce, -⟩ := hanti
          exact ⟨ce, de, hM, hce⟩
      have hup : ∀ y ∈ Set.range vv, (0:ℝ) ≤
          (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
            (y : Fin 3 → ℝ) :=
        fun y hy => pmTiltUpperHalf_p35 hscs hdiag hBB hE hFF j hsurv y hy
      exact hroot
    · have hup : ∀ y ∈ Set.range vv, (0:ℝ) ≤
          (crossProduct (vv j : Fin 3 → ℝ) (vv (j + 1) : Fin 3 → ℝ)) ⬝ᵥ
            (y : Fin 3 → ℝ) :=
        fun y hy => pmFlatAUpperHalf_p35 hscs hdiag hBB hE hFF j hdneg y hy
      exact hroot
  -- DISCHARGES (next-lane input): the winding kill is the planar polar-angle
  -- chain (normal-axis azimuth) + metric squeeze (k ∈ {4,5,6} from
  -- diagKGe4/scsKLe6), fed by the pm8 globalization/quadrant data.
/-- **THE SHARPENED NAMED RESIDUAL** (lkgrqui-sectortri-w2): the diagonal
endpoints never sit together in an azimuth corner of any dart sector.
With `φ_x(j) := azim 0 (vv j) (vv (j+1)) x` and
`θ_j := azim 0 (vv j) (vv (j+1)) (vv (j+s.k-1))` (the sector span, which
`wedgeSectorMem_p35` bounds by π and `dartSpanNeCyc_p35` unbounds from 0)
the four corners are: C1 `φ_u = φ_w = 0`, C2 `φ_u = φ_w = θ`, and — for
flat darts θ = π — C3 `(φ_u, φ_w) = (0, π)`, C4 `(φ_u, φ_w) = (π, 0)`.
This is the azimuth rendering of the dart-plane miss
`¬(u ∈ aff {0, vv j, vv (j+1)} ∧ w ∈ aff {…})`, i.e. the strictness core
of HOL `AFF_GT_INTER_AFF_SY` (TECOXBM.hl:311, QKNVMLB.hl 3838-4024):
the same-azimuth pairs with axial separation and the opposite-azimuth
pairs at flat darts satisfy every readable metric conjunct (annulus
norms, a-bounds at distinct residues, consecutive b ≤ cstab, and the
ConvexLocalFan conjunct itself — a span-π dart only forces the closed
half-space), so the exclusion must come from the full fan-theory route
(HOL route: DETERMINE_WEDGE_IN_FAN + PGSQVBL + LOFA_DETERMINE_AZIM_IN_FA
+ AZIM_PI_WEDGE_GE_CROSS_DOT + WEDGE_GE_EQ_AFF_GE + AZIM_CYCLE_EQ_SIGMA_FAN
+ sigma_fan_in_set_of_edge + UNIQUE_AZIM_0_POINT_FAN + FAN_IMP_EE_EQ_SET_OF_EDGE
+ LOFA_CARD_EE_V_1; Lean-world pieces `unique_azim0_point_fan`,
`unique_azim_point_fan`, `sum2_azim_fan`, `mono_sigma_fan`,
`permutes_sigma_fan` are in the closure and standard-three, probe
probes/probe1_fanvis.lean — the remaining chain is the next lane's
sizing input). -/
private theorem sectorTriPlaneMiss_p35 {s : ScsV39} {p q : ℕ} {u w : V3}
    {E : Set (Set V3)} {FF : Set (V3 × V3)} {vv : ℕ → V3}
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (_hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) :
    ∀ j : ℕ,
      ¬(azim 0 (vv j) (vv (j + 1)) u = 0 ∧ azim 0 (vv j) (vv (j + 1)) w = 0) ∧
      ¬(azim 0 (vv j) (vv (j + 1)) u = azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1)) ∧
        azim 0 (vv j) (vv (j + 1)) w = azim 0 (vv j) (vv (j + 1)) (vv (j + s.k - 1))) ∧
      ¬(azim 0 (vv j) (vv (j + 1)) u = 0 ∧ azim 0 (vv j) (vv (j + 1)) w = Real.pi) ∧
      ¬(azim 0 (vv j) (vv (j + 1)) u = Real.pi ∧ azim 0 (vv j) (vv (j + 1)) w = 0) := by
  intro j
  have hk3 : 3 ≤ s.k := hscs.2.1
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · -- C1: both endpoints at azimuth 0 sit in the dart face plane
    obtain ⟨hu0, hw0⟩ := hc
    obtain ⟨huP, hwP, -⟩ := pmC1AtDart_p35 hscs hdiag hp hq hBB hE hFF j hu0 hw0
    exact pmPlaneCrowding_p35 hscs hdiag _hdist hp hq hBB hE hFF j huP hwP
  · -- C2: the span-face plane aff {0, vv j, vv (j+k-1)} is the dart
    -- (j+k-1) face plane (wedgeVvAddK_p35 rewrites vv (j+k) = vv j)
    obtain ⟨huθ, hwθ⟩ := hc
    obtain ⟨c1, d1, hu1⟩ := (pmC2AtDart_p35 hscs hdiag hp hq hBB hE hFF j huθ hwθ).1
    obtain ⟨c2, d2, hw1⟩ := (pmC2AtDart_p35 hscs hdiag hp hq hBB hE hFF j huθ hwθ).2.1
    have hj1 : (j + s.k - 1) + 1 = j + s.k := by omega
    have hvsi : vv (j + s.k - 1 + 1) = vv j := by
      rw [hj1]; exact wedgeVvAddK_p35 hBB.2.1 j
    refine pmPlaneCrowding_p35 hscs hdiag _hdist hp hq hBB hE hFF (j + s.k - 1) ?_ ?_
    · exact ⟨d1, c1, by rw [hu1, hvsi]; exact add_comm _ _⟩
    · exact ⟨d2, c2, by rw [hw1, hvsi]; exact add_comm _ _⟩
  · -- C3: u at azimuth 0, w at azimuth π (flat span)
    obtain ⟨hu0, hwπ⟩ := hc
    obtain ⟨huP, hwP, -, -⟩ := pmC3AtDart_p35 hscs hdiag hp hq hBB hE hFF j hu0 hwπ
    exact pmPlaneCrowding_p35 hscs hdiag _hdist hp hq hBB hE hFF j huP hwP
  · -- C4: u at azimuth π, w at azimuth 0 (flat span)
    obtain ⟨huπ, hw0⟩ := hc
    obtain ⟨huP, hwP, -, -⟩ := pmC4AtDart_p35 hscs hdiag hp hq hBB hE hFF j huπ hw0
    exact pmPlaneCrowding_p35 hscs hdiag _hdist hp hq hBB hE hFF j huP hwP
  -- DISCHARGES (lkgrqui-planemiss2-w3): source TECOXBM.hl:311
  -- (AFF_GT_INTER_AFF_SY) strictness core.  All four corners reduce to the
  -- named residual `pmPlaneCrowding_p35` (single sorryAx root): C1 @ dart
  -- j, C2 @ dart j+k-1, C3/C4 @ dart j via the π-rendering
  -- (pmRenderPi_p35).  Consumed by sectorTriCore_p35 unchanged.

/-- **(A)-rung A3 (pm5)**: the double-face cone — every ring vertex sits in
both adjacent dart-face half-spaces at dart `i` (the convex-cone form of the
closed sector: faces of dart `i` and of cyclic dart `i+k-1`). -/
private theorem pmTwoFaceCone_p35 {vv : ℕ → V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hfan : ConvexLocalFan (Set.range vv) E FF) (i : ℕ) (x : V3)
    (hx : x ∈ Set.range vv) :
    (0:ℝ) ≤ (crossProduct ((vv i : V3) : Fin 3 → ℝ)
        ((vv (i + 1) : V3) : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) ∧
    (0:ℝ) ≤ (crossProduct ((vv (i + k - 1) : V3) : Fin 3 → ℝ)
        ((vv i : V3) : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  refine ⟨pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan i x hx, ?_⟩
  have h1 := pmCrossGeDart_p35 hk3 hper hinj hE hFF hfan (i + k - 1) x hx
  have hk1 : (i + k - 1) + 1 = i + k := by omega
  have hvsi : vv ((i + k - 1) + 1) = vv i := by rw [hk1]; exact wedgeVvAddK_p35 hper i
  rw [hvsi] at h1
  exact h1

/-- **(A)-rung A4 (pm5)**: below-π sector collapse — an in-plane point whose
azimuth is bounded by a below-π sector span sits at azimuth `0`. -/
private theorem pmPlaneAzim0OfLtPi_p35 {a b x : V3} {s t : ℝ} (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hnc : ¬ Collinear3 0 a b)
    (hx : x - 0 = s • (a - 0) + t • (b - 0))
    {θ : ℝ} (hsec : azim 0 a b x ≤ θ) (hθ : θ ≤ Real.pi) (hlt : θ < Real.pi) :
    azim 0 a b x = 0 := by
  rcases azimPlanePlace_p35 ha0 hb0 hnc ⟨s, t, hx⟩ with h0 | hpi
  · exact h0
  · exfalso
    linarith

/-- **(A)-rung A5 (pm5)**: the axis-line pair kill — two distinct annulus
points on one line through `0` with the diagonal chord bounds contradict
(same ray: the chord–cosine same-ray kill; opposite rays: chord ≥ 4). -/
private theorem pmAxisPairKill_p35 {a x y : V3} {cx cy : ℝ} (ha0 : a ≠ 0)
    (hx : x - 0 = cx • (a - 0)) (hy : y - 0 = cy • (a - 0))
    (hx2 : (2:ℝ) ≤ ‖x‖) (hx' : ‖x‖ ≤ 2 * h0) (hy2 : (2:ℝ) ≤ ‖y‖) (hy' : ‖y‖ ≤ 2 * h0)
    (hxy : x ≠ y) (h2 : (2:ℝ) ≤ dist x y) (hd : dist x y ≤ cstab) : False := by
  have hx0 : x ≠ (0:V3) := by
    intro hzz
    rw [hzz] at hx2
    norm_num at hx2
  have hy0 : y ≠ (0:V3) := by
    intro hzz
    rw [hzz] at hy2
    norm_num at hy2
  have cx0 : cx ≠ 0 := by
    intro h
    rw [h, zero_smul, sub_zero] at hx
    exact hx0 hx
  have cy0 : cy ≠ 0 := by
    intro h
    rw [h, zero_smul, sub_zero] at hy
    exact hy0 hy
  have hxe : (x:V3) = cx • (a - 0) := by simpa using hx
  have hye : (y:V3) = cy • (a - 0) := by simpa using hy
  have hdn : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
  have hc4 : cstab < (4:ℝ) := by norm_num [cstab]
  rcases lt_trichotomy cx 0 with hcx | hcx0 | hcx
  · rcases lt_trichotomy cy 0 with hcy | hcy0 | hcy
    · -- both negative: same ray, positive ratio
      have hrat : x - 0 = (cx / cy) • (y - 0) := by
        rw [hx, hy, smul_smul, div_mul_cancel₀ _ cy0]
      exact pmNotSameRay_p35 (c := cx / cy) hx2 hx' hy2 hy'
        (le_of_lt (div_pos_of_neg_of_neg hcx hcy)) hrat h2
    · exact absurd hcy0 cy0
    · -- mixed signs: chord = ‖x‖ + ‖y‖ ≥ 4
      exfalso
      have hsub : x - y = (cx - cy) • (a - 0) := by rw [hxe, hye, sub_smul]
      have h3 : ‖x - y‖ = |cx - cy| * ‖a‖ := by
        rw [hsub, norm_smul, Real.norm_eq_abs]
        simp
      have h1 : ‖x‖ = |cx| * ‖a‖ := by
        rw [hxe, norm_smul, Real.norm_eq_abs]
        simp
      have h4 : ‖y‖ = |cy| * ‖a‖ := by
        rw [hye, norm_smul, Real.norm_eq_abs]
        simp
      have hX : ‖x‖ = -cx * ‖a‖ := by rw [h1, abs_of_neg hcx]
      have hY : ‖y‖ = cy * ‖a‖ := by rw [h4, abs_of_pos hcy]
      have hn : ‖x - y‖ = cy * ‖a‖ - cx * ‖a‖ := by
        rw [h3, abs_of_neg (show cx - cy < 0 by linarith)]
        ring
      linarith
  · exact absurd hcx0 cx0
  · rcases lt_trichotomy cy 0 with hcy | hcy0 | hcy
    · -- mixed signs (mirror): chord = ‖x‖ + ‖y‖ ≥ 4
      exfalso
      have hsub : x - y = (cx - cy) • (a - 0) := by rw [hxe, hye, sub_smul]
      have h3 : ‖x - y‖ = |cx - cy| * ‖a‖ := by
        rw [hsub, norm_smul, Real.norm_eq_abs]
        simp
      have h1 : ‖x‖ = |cx| * ‖a‖ := by
        rw [hxe, norm_smul, Real.norm_eq_abs]
        simp
      have h4 : ‖y‖ = |cy| * ‖a‖ := by
        rw [hye, norm_smul, Real.norm_eq_abs]
        simp
      have hX : ‖x‖ = cx * ‖a‖ := by rw [h1, abs_of_pos hcx]
      have hY : ‖y‖ = -cy * ‖a‖ := by rw [h4, abs_of_neg hcy]
      have hn : ‖x - y‖ = cx * ‖a‖ - cy * ‖a‖ := by
        rw [h3, abs_of_pos (show (0:ℝ) < cx - cy by linarith)]
        ring
      linarith
    · exact absurd hcy0 cy0
    · -- both positive: same ray, positive ratio
      have hrat : x - 0 = (cx / cy) • (y - 0) := by
        rw [hx, hy, smul_smul, div_mul_cancel₀ _ cy0]
      exact pmNotSameRay_p35 (c := cx / cy) hx2 hx' hy2 hy'
        (le_of_lt (div_pos hcx hcy)) hrat h2

/-- **(A)-rung A6 (pm5)**: flat-run normal parallelism — two independent
plane vectors of `span(a, b)` have their cross product a nonzero multiple of
`cross(a, b)` (the orientation sign is read off the ring at the next lane). -/
private theorem pmFlatRunNormal_p35 {a b p q : V3} (ha0 : a ≠ 0)
    (hncab : ¬ Collinear3 0 a b)
    (hp : ∃ s t : ℝ, p - 0 = s • (a - 0) + t • (b - 0))
    (hq : ∃ s t : ℝ, q - 0 = s • (a - 0) + t • (b - 0))
    (hncpq : ¬ Collinear3 0 p q) :
    ∃ ζ : ℝ, crossProduct (p : Fin 3 → ℝ) (q : Fin 3 → ℝ)
      = ζ • crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) ∧ ζ ≠ 0 := by
  obtain ⟨s, t, hp'⟩ := hp
  obtain ⟨s', t', hq'⟩ := hq
  simp only [sub_zero] at hp' hq'
  have hpcoe : (p : Fin 3 → ℝ) = s • (a : Fin 3 → ℝ) + t • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hp'
  have hqcoe : (q : Fin 3 → ℝ) = s' • (a : Fin 3 → ℝ) + t' • (b : Fin 3 → ℝ) :=
    congrArg (fun w : V3 => (w : Fin 3 → ℝ)) hq'
  have haa : crossProduct (a : Fin 3 → ℝ) (a : Fin 3 → ℝ) = 0 := cross_self _
  have hbb : crossProduct (b : Fin 3 → ℝ) (b : Fin 3 → ℝ) = 0 := cross_self _
  have hba : crossProduct (b : Fin 3 → ℝ) (a : Fin 3 → ℝ)
      = -(crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) :=
    (cross_anticomm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)).symm
  have hexp : crossProduct (p : Fin 3 → ℝ) (q : Fin 3 → ℝ)
      = (s * t' - s' * t) • crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) := by
    rw [hpcoe, hqcoe, pmCrossAddL_p35, pmCrossSmulL_p35, pmCrossSmulL_p35,
      pmCrossAddR_p35, pmCrossAddR_p35, pmCrossSmulR_p35, pmCrossSmulR_p35,
      pmCrossSmulR_p35, pmCrossSmulR_p35, haa, hbb, hba]
    module
  refine ⟨s * t' - s' * t, hexp, ?_⟩
  intro hzero
  have hdet : s * t' = s' * t := by linarith
  -- the determinant condition makes p and q collinear with 0
  have hcoord0 : s • (a - 0) + t • (b - 0) = (0:V3) → s = 0 ∧ t = 0 :=
    fun hco => pmPlaneCoordZero_p35 ha0 hncab hco
  have hcoordOfPz : (p:V3) = (0:V3) → s = 0 ∧ t = 0 := by
    intro hzz
    exact hcoord0 (by simpa using hp'.symm.trans hzz)
  by_cases hps : s = 0
  · rcases eq_or_ne t 0 with ht0 | ht
    · -- p = 0: {0, p, q} is a two-point set
      have hzz : (p:V3) = (0:V3) := by
        rw [hp', hps, ht0]
        simp
      exact hncpq (by
        show Collinear ℝ ({(0:V3), p, q} : Set V3)
        rw [show ({(0:V3), p, q} : Set V3) = ({(0:V3), q} : Set V3) from by
          ext z; simp [hzz]]
        exact collinear_pair ℝ (0:V3) q)
    · -- s = 0, t ≠ 0: s' = 0 and q = (t'/t) • p
      rw [hps, zero_mul, zero_sub] at hzero
      have hs'0 : s' = 0 := by
        have hst : s' * t = 0 := by linarith
        rcases mul_eq_zero.mp hst with h | h
        · exact h
        · exact absurd h ht
      have hpne : (p:V3) ≠ 0 := by
        intro hzz
        obtain ⟨hsz, htz⟩ := hcoordOfPz hzz
        exact ht htz
      refine hncpq ((collinear3_iff_smul (v := (0:V3)) (w := p) (w1 := q) hpne).mpr
        ⟨t' / t, ?_⟩)
      rw [hp', hq', hps, hs'0]
      simp only [sub_zero, zero_smul, zero_add, smul_smul,
        div_mul_cancel₀ _ ht]
  · rcases eq_or_ne t 0 with ht0 | ht
    · -- s ≠ 0, t = 0: t' = 0 and q = (s'/s) • p
      rw [ht0, mul_zero] at hdet
      have ht'0 : t' = 0 := by
        have hst : s * t' = 0 := hdet
        rcases mul_eq_zero.mp hst with h | h
        · exact absurd h hps
        · exact h
      have hpne : (p:V3) ≠ 0 := by
        intro hzz
        obtain ⟨hsz, htz⟩ := hcoordOfPz hzz
        exact hps hsz
      refine hncpq ((collinear3_iff_smul (v := (0:V3)) (w := p) (w1 := q) hpne).mpr
        ⟨s' / s, ?_⟩)
      rw [hp', hq', ht0, ht'0]
      simp only [sub_zero]
      rw [smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ hps, mul_zero]
    · -- s ≠ 0, t ≠ 0: q = (s'/s) • p
      have htrans : (s' / s) * t = t' := by
        rw [div_mul_eq_mul_div, div_eq_iff hps]
        linarith
      have hpne : (p:V3) ≠ 0 := by
        intro hzz
        obtain ⟨hsz, htz⟩ := hcoordOfPz hzz
        exact hps hsz
      refine hncpq ((collinear3_iff_smul (v := (0:V3)) (w := p) (w1 := q) hpne).mpr
        ⟨s' / s, ?_⟩)
      rw [hp', hq']
      simp only [sub_zero]
      rw [smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ hps, htrans]
/-- The on-axis x θ-boundary corner kill (new kit item). -/
private theorem axisBoundKill_p35 {b c d u w : V3} (θ' : ℝ)
    (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (hncbc : ¬ Collinear3 0 b c) (hncdb : ¬ Collinear3 0 d b)
    (hθw : azim 0 b c w = azim 0 b c d)
    (hncbw : ¬ Collinear3 0 b w)
    (haxu : Collinear3 0 b u)
    (hC1 : ¬(azim 0 d b u = 0 ∧ azim 0 d b w = 0))
    (hC2 : ¬(azim 0 d b u = θ' ∧ azim 0 d b w = θ'))
    (hC3 : ¬(azim 0 d b u = 0 ∧ azim 0 d b w = Real.pi))
    (hC4 : ¬(azim 0 d b u = Real.pi ∧ azim 0 d b w = 0))
    (hbu : azim 0 d b u ≤ θ')
    (hθ'π : θ' ≤ Real.pi) : False := by
  have hbwd : ¬ Collinear3 0 b d := coll3swap_p35.not.mp hncdb
  obtain ⟨lam, hlam⟩ := (collinear3_iff_smul hb0).mp haxu
  obtain ⟨c1, hc1, c2, hc2⟩ :=
    (affGt_pair_iff (v0 := (0:V3)) (v1 := b) (x := d) (y := w)
      (Ne.symm hb0) hd0 (fun he => hncdb (by rw [he]; exact collinear3_pair_right rfl))).mp
      ((azim_eq_azim_iff hncbc hbwd hncbw).mp hθw.symm)
  have hu' : azim 0 d b u = 0 ∨ azim 0 d b u = Real.pi :=
    azimPlanePlace_p35 hd0 hb0 hncdb ⟨0, lam, by rw [hlam]; module⟩
  have hw' : azim 0 d b w = 0 ∨ azim 0 d b w = Real.pi :=
    azimPlanePlace_p35 hd0 hb0 hncdb ⟨c1, c2, hc2⟩
  rcases hu' with hu0' | huπ <;> rcases hw' with hw0' | hwπ
  · exact hC1 ⟨hu0', hw0'⟩
  · exact hC3 ⟨hu0', hwπ⟩
  · exact hC4 ⟨huπ, hw0'⟩
  · have hθ'eq : θ' = Real.pi := le_antisymm hθ'π (by rw [← huπ]; exact hbu)
    exact hC2 (by rw [hθ'eq]; exact ⟨huπ, hwπ⟩)


/-- **THE NAMED RESIDUAL** (lkgrqui-tecoxbm3-w2): the sector-triangle core,
k-generic — exactly `TECOXBMv2_p35` without the unused `hV` hypothesis.
Ladder status: L0/L1 (membership + consecutive non-collinearity), L2 (lune
rewrite, imported `wedge_eq_affGt`), L5 (cone transfer) and L6 (strict
sandwich, `azimSandwich_p35` above) are closed; the remaining roots L3/L4
are documented in the DISCHARGES note. -/
private theorem sectorTriCore_p35 (s : ScsV39) (p q : ℕ) (u w : V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (_hdist : dist u w ≤ cstab)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E := by
  -- kit extraction: k-guards, periodicity, injectivity, the fan structure
  have hk4 : 4 ≤ s.k := diagKGe4_p35 hscs hdiag
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3 : 3 ≤ s.k := hscs.2.1
  have hk3lt : 3 < s.k := by omega
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have hfan : ConvexLocalFan (Set.range vv) E FF := by
    rcases hBB.2.2.2 with hle | hcl
    · omega
    · rw [← hE, ← hFF]
      exact hcl
  have hfan' : Kepler.Text.Fan.FAN 0 (Set.range vv) E := fanOfBB_p35 hk4 hBB hE hFF
  -- window vertices are nonzero (annulus), and the diag pair is a genuine pair
  have hvne : ∀ j : ℕ, vv j ≠ (0:V3) := by
    intro j hj
    have hm : vv j ∈ ballAnnulus := hBB.1 (Set.mem_range.mpr ⟨j, rfl⟩)
    exact hm.2 (by simp only [hj, ballAnnulus, Metric.mem_ball, dist_self]; norm_num)
  have hpk : p % s.k < s.k := Nat.mod_lt _ hk0
  have hqk : q % s.k < s.k := Nat.mod_lt _ hk0
  have huw : u ≠ w := by
    intro he
    have h : vv (p % s.k) = vv (q % s.k) := by rw [hp, hq]; exact he
    rw [periodic_mod_eq_p23 hper p, periodic_mod_eq_p23 hper q] at h
    have hm := vvModEq_p35 hk0 hper hinj h
    exact hdiag.1 hm
  have hu0 : u ≠ (0:V3) := by rw [← hp]; exact hvne _
  have hw0 : w ≠ (0:V3) := by rw [← hq]; exact hvne _
  -- the four corner exclusions at this dart and at the cyclically previous dart
  have hPM := sectorTriPlaneMiss_p35 hscs hdiag _hdist hp hq hBB hE hFF
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, (vv i, vv (i + 1)) = x :=
    Set.mem_range.mp (by rw [hFF]; exact hx)
  rw [wedgeCyclic_p35 hk3 hper hinj hE i]
  intro t ht
  obtain ⟨β, γ, hβ, hγ, htr⟩ := (triMemAffGt_p35 (v0 := (0:V3)) (x := u) (y := w) (z := t)
    hu0 hw0 huw).mp ht
  have hbne : vv i ≠ (0:V3) := hvne i
  -- dart i facts: consecutive non-collinearity, sector span in (0, π]
  obtain ⟨hncbc, hncdb⟩ := vvNonCollStep_p35 hscs hBB hk3lt i
  have hspanπ : azim (0:V3) (vv i) (vv (i + 1)) (vv (i + s.k - 1)) ≤ Real.pi :=
    (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).2
  -- both diag endpoints sit in the closed sector at dart i
  have huR : u ∈ Set.range vv := Set.mem_range.mpr ⟨p % s.k, hp⟩
  have hwR : w ∈ Set.range vv := Set.mem_range.mpr ⟨q % s.k, hq⟩
  obtain ⟨huθ0, huθ⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).1 u huR
  obtain ⟨hwθ0, hwθ⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan i).1 w hwR
  -- far-dart bundle (dart i + k - 1, axis vv (i+k-1), start ray vv i), for the
  -- two boundary kills
  have hj1 : (i + s.k - 1) + 1 = i + s.k := by omega
  have hvsi : vv ((i + s.k - 1) + 1) = vv i := by
    rw [hj1]; exact wedgeVvAddK_p35 hper i
  obtain ⟨hC1f, hC2f, hC3f, hC4f⟩ := hPM (i + s.k - 1)
  rw [hvsi] at hC1f hC2f hC3f hC4f
  have hfarθ : azim (0:V3) (vv (i + s.k - 1)) (vv i) (vv (i + s.k - 1 + s.k - 1))
      ≤ Real.pi := by
    have h := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan (i + s.k - 1)).2
    rw [hvsi] at h
    exact h
  have hfaru : azim (0:V3) (vv (i + s.k - 1)) (vv i) u
      ≤ azim (0:V3) (vv (i + s.k - 1)) (vv i) (vv (i + s.k - 1 + s.k - 1)) := by
    obtain ⟨-, h1⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan (i + s.k - 1)).1 u huR
    rw [hvsi] at h1
    exact h1
  have hfarw : azim (0:V3) (vv (i + s.k - 1)) (vv i) w
      ≤ azim (0:V3) (vv (i + s.k - 1)) (vv i) (vv (i + s.k - 1 + s.k - 1)) := by
    obtain ⟨-, h1⟩ := (wedgeSectorMem_p35 hk3 hper hinj hE hFF hfan (i + s.k - 1)).1 w hwR
    rw [hvsi] at h1
    exact h1
  -- the membership data: t = β•u + γ•w with β, γ > 0
  -- azimuth trichotomy of the diag pair at dart i
  rcases lt_trichotomy (azim (0:V3) (vv i) (vv (i + 1)) u)
      (azim (0:V3) (vv i) (vv (i + 1)) w) with hlt | heq | hgt
  · -- u strictly before w
    by_cases hφu0 : azim (0:V3) (vv i) (vv (i + 1)) u = 0
    · -- φu = 0: on-axis and in-plane sub-branches
      have hφwpos : 0 < azim (0:V3) (vv i) (vv (i + 1)) w := by linarith
      have hncbw : ¬ Collinear3 0 (vv i) w := fun hc =>
        ne_of_gt hφwpos (azimAxis_p35 hc)
      by_cases hxcol : Collinear3 0 (vv i) u
      · -- u on the dart axis: same-ray transfer, with the θ-boundary kill
        obtain ⟨lam, hlam⟩ := (collinear3_iff_smul hbne).mp hxcol
        have htin : t - 0 = γ • (w - 0) + (β * lam) • (vv i - 0) := by
          rw [htr, hlam]; module
        have hncbt : ¬ Collinear3 0 (vv i) t := by
          intro hc
          obtain ⟨α, hα⟩ := (collinear3_iff_smul hbne).mp hc
          apply hncbw
          have hk1 : γ • (w - 0) + (β * lam) • (vv i - 0) = α • (vv i - 0) := by
            rw [← htin, hα]
          have hk2 : γ • (w - 0) = (α - β * lam) • (vv i - 0) := by
            rw [sub_smul, eq_sub_iff_add_eq]
            exact hk1
          refine (collinear3_iff_smul hbne).mpr ⟨(α - β * lam) / γ, ?_⟩
          have hceq : γ * ((α - β * lam) / γ) = α - β * lam := by field_simp
          apply smul_right_injective V3 (ne_of_gt hγ)
          show γ • (w - 0) = γ • (((α - β * lam) / γ) • (vv i - 0))
          rw [smul_smul, hceq, hk2]
        have hwvne : w ≠ vv i := fun he =>
          hncbw (by rw [he]; exact collinear3_pair_right rfl)
        have htin2 : t ∈ affGt ({(0:V3), vv i} : Set V3) {w} :=
          (affGt_pair_iff (v0 := (0:V3)) (v1 := vv i) (x := w) (y := t)
            (Ne.symm hbne) hw0 hwvne).mpr ⟨γ, hγ, β * lam, htin⟩
        by_cases hwt : azim (0:V3) (vv i) (vv (i + 1)) w
            = azim (0:V3) (vv i) (vv (i + 1)) (vv (i + s.k - 1))
        · refine absurd hwt (fun hc => ?_)
          exact axisBoundKill_p35 (b := vv i) (c := vv (i + 1))
            (d := vv (i + s.k - 1)) (u := u) (w := w)
            (azim (0:V3) (vv (i + s.k - 1)) (vv i) (vv (i + s.k - 1 + s.k - 1)))
            hbne (hvne (i + s.k - 1)) hncbc hncdb hc hncbw hxcol hC1f hC2f hC3f hC4f
            hfaru hfarθ
        · have hφt : azim (0:V3) (vv i) (vv (i + 1)) t
              = azim (0:V3) (vv i) (vv (i + 1)) w :=
            ((azim_eq_azim_iff hncbc hncbw hncbt).mpr htin2).symm
          refine ⟨hncbt, ?_, ?_⟩
          · rw [hφt]; exact hφwpos
          · rw [hφt]; exact lt_of_le_of_ne hwθ hwt
      · -- u in the dart plane, off-axis: cone transfer then one sandwich step
        have hncbu : ¬ Collinear3 0 (vv i) u := hxcol
        have huw0 : azim 0 (vv i) u w = azim (0:V3) (vv i) (vv (i + 1)) w := by
          have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
            (w1 := u) (w2 := w) hbne hncbc hncbu hncbw
            (by rw [hφu0]; exact azim_nonneg 0 (vv i) (vv (i + 1)) w)
          rw [hφu0] at h
          linarith
        have hwlt : azim 0 (vv i) u w < Real.pi := by
          by_contra hge
          have hπ : azim (0:V3) (vv i) (vv (i + 1)) w = Real.pi := by
            have := hwθ
            linarith
          exact (hPM i).2.2.1 ⟨hφu0, hπ⟩
        obtain ⟨hncbt, hut0, hutw⟩ := coneMem_p35 (v0 := (0:V3)) (ax := vv i) (u := u)
          (w := w) (t := t) hncbu hncbw huw (by rw [huw0]; linarith) hwlt β γ hβ hγ htr
        have hφteq : azim (0:V3) (vv i) (vv (i + 1)) t = azim 0 (vv i) u t := by
          have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
            (w1 := u) (w2 := t) hbne hncbc hncbu hncbt
            (by rw [hφu0]; exact azim_nonneg 0 (vv i) (vv (i + 1)) t)
          rw [hφu0] at h
          linarith
        refine ⟨hncbt, ?_, ?_⟩
        · rw [hφteq]; exact hut0
        · rw [hφteq]; linarith [hutw, huw0]
    · -- 0 < φu ≤ φw: cone transfer (L5) + strict sandwich (L6)
      have hφup : 0 < azim (0:V3) (vv i) (vv (i + 1)) u :=
        lt_of_le_of_ne huθ0 (Ne.symm hφu0)
      have hncbu : ¬ Collinear3 0 (vv i) u := fun hc => hφu0 (azimAxis_p35 hc)
      have hφwp : 0 < azim (0:V3) (vv i) (vv (i + 1)) w := by linarith
      have hncbw : ¬ Collinear3 0 (vv i) w := fun hc =>
        ne_of_gt hφwp (azimAxis_p35 hc)
      have huw0 : azim 0 (vv i) u w
          = azim (0:V3) (vv i) (vv (i + 1)) w - azim (0:V3) (vv i) (vv (i + 1)) u := by
        have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
          (w1 := u) (w2 := w) hbne hncbc hncbu hncbw (le_of_lt hlt)
        linarith
      have hgapπ : azim 0 (vv i) u w < Real.pi := by linarith [huw0, hwθ, hφup]
      obtain ⟨hncbt, hut0, hutw⟩ := coneMem_p35 (v0 := (0:V3)) (ax := vv i) (u := u)
        (w := w) (t := t) hncbu hncbw huw (by rw [huw0]; linarith) hgapπ β γ hβ hγ htr
      obtain ⟨hφtp, hφtlt⟩ := azimSandwich_p35 (v0 := (0:V3)) (ax := vv i) (b := vv (i + 1))
        (p := u) (q := w) (r := t) (Ne.symm hbne) hncbc hncbu hncbw hncbt hφup
        (le_of_lt hlt) (hwθ.trans hspanπ) hut0 hutw
      refine ⟨hncbt, hφtp, ?_⟩
      linarith [hφtlt, hwθ]
  · -- equal azimuths: the whole cone collapses onto one interior ray
    have hφ0 : azim (0:V3) (vv i) (vv (i + 1)) u ≠ 0 := fun he0 =>
      (hPM i).1 ⟨he0, heq.symm.trans he0⟩
    have hφθ : azim (0:V3) (vv i) (vv (i + 1)) u
        ≠ azim (0:V3) (vv i) (vv (i + 1)) (vv (i + s.k - 1)) := fun he0 =>
      (hPM i).2.1 ⟨he0, heq.symm.trans he0⟩
    have hncbu : ¬ Collinear3 0 (vv i) u := fun hc => absurd (azimAxis_p35 hc) hφ0
    have hncbw : ¬ Collinear3 0 (vv i) w := fun hc =>
      absurd (heq.trans (azimAxis_p35 hc)) hφ0
    have hub : azim 0 (vv i) u w = 0 := by
      have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
        (w1 := u) (w2 := w) hbne hncbc hncbu hncbw (le_of_eq heq)
      linarith [h, heq]
    have hubne : u ≠ vv i := fun he2 =>
      hφ0 (by rw [he2]; exact azimAxis_p35 (collinear3_pair_right rfl))
    have hwray : w ∈ affGt ({(0:V3), vv i} : Set V3) {u} :=
      (azim_eq_zero_iff_alt hncbu hncbw).mp hub
    obtain ⟨c0, hc0, h1c, hc1⟩ := (affGt_pair_iff (v0 := (0:V3)) (v1 := vv i) (x := u)
      (y := w) (Ne.symm hbne) hu0 hubne).mp hwray
    have htray : t - 0 = (β + γ * c0) • (u - 0) + (γ * h1c) • (vv i - 0) := by
      rw [htr, hc1]; module
    have htin : t ∈ affGt ({(0:V3), vv i} : Set V3) {u} :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := vv i) (x := u) (y := t)
        (Ne.symm hbne) hu0 hubne).mpr ⟨β + γ * c0,
        by have hgc : 0 < γ * c0 := mul_pos hγ hc0; linarith, γ * h1c, htray⟩
    have hncbt : ¬ Collinear3 0 (vv i) t := by
      intro hc
      obtain ⟨α, hα⟩ := (collinear3_iff_smul hbne).mp hc
      apply hncbu
      have hk1 : (β + γ * c0) • (u - 0) + (γ * h1c) • (vv i - 0) = α • (vv i - 0) := by
        rw [← htray, hα]
      have hk2 : (β + γ * c0) • (u - 0) = (α - γ * h1c) • (vv i - 0) := by
        rw [sub_smul, eq_sub_iff_add_eq]
        exact hk1
      refine (collinear3_iff_smul hbne).mpr ⟨(α - γ * h1c) / (β + γ * c0), ?_⟩
      have hceq : (β + γ * c0) * ((α - γ * h1c) / (β + γ * c0)) = α - γ * h1c := by
        field_simp
      have hgc0 : 0 < γ * c0 := mul_pos hγ hc0
      have hpos : β + γ * c0 ≠ 0 := ne_of_gt (by linarith)
      apply smul_right_injective V3 hpos
      show (β + γ * c0) • (u - 0)
          = (β + γ * c0) • (((α - γ * h1c) / (β + γ * c0)) • (vv i - 0))
      rw [smul_smul, hceq, hk2]
    have hφt : azim (0:V3) (vv i) (vv (i + 1)) u = azim (0:V3) (vv i) (vv (i + 1)) t :=
      (azim_eq_azim_iff hncbc hncbu hncbt).mpr htin
    refine ⟨hncbt, ?_, ?_⟩
    · rw [← hφt]; exact lt_of_le_of_ne (azim_nonneg 0 (vv i) (vv (i + 1)) u) (Ne.symm hφ0)
    · rw [← hφt]; exact lt_of_le_of_ne huθ hφθ
  · -- w strictly before u: mirror of the first case
    by_cases hφw0 : azim (0:V3) (vv i) (vv (i + 1)) w = 0
    · -- φw = 0: on-axis and in-plane sub-branches
      have hφupos : 0 < azim (0:V3) (vv i) (vv (i + 1)) u := by linarith
      have hncbu : ¬ Collinear3 0 (vv i) u := fun hc =>
        ne_of_gt hφupos (azimAxis_p35 hc)
      by_cases hxwcol : Collinear3 0 (vv i) w
      · -- w on the dart axis: same-ray transfer, with the θ-boundary kill
        obtain ⟨lam, hlam⟩ := (collinear3_iff_smul hbne).mp hxwcol
        have htin : t - 0 = β • (u - 0) + (γ * lam) • (vv i - 0) := by
          rw [htr, hlam]; module
        have hncbt : ¬ Collinear3 0 (vv i) t := by
          intro hc
          obtain ⟨α, hα⟩ := (collinear3_iff_smul hbne).mp hc
          apply hncbu
          have hk1 : β • (u - 0) + (γ * lam) • (vv i - 0) = α • (vv i - 0) := by
            rw [← htin, hα]
          have hk2 : β • (u - 0) = (α - γ * lam) • (vv i - 0) := by
            rw [sub_smul, eq_sub_iff_add_eq]
            exact hk1
          refine (collinear3_iff_smul hbne).mpr ⟨(α - γ * lam) / β, ?_⟩
          have hceq : β * ((α - γ * lam) / β) = α - γ * lam := by field_simp
          apply smul_right_injective V3 (ne_of_gt hβ)
          show β • (u - 0) = β • (((α - γ * lam) / β) • (vv i - 0))
          rw [smul_smul, hceq, hk2]
        have huune : u ≠ vv i := fun he =>
          hncbu (by rw [he]; exact collinear3_pair_right rfl)
        have htin2 : t ∈ affGt ({(0:V3), vv i} : Set V3) {u} :=
          (affGt_pair_iff (v0 := (0:V3)) (v1 := vv i) (x := u) (y := t)
            (Ne.symm hbne) hu0 huune).mpr ⟨β, hβ, γ * lam, htin⟩
        by_cases hut : azim (0:V3) (vv i) (vv (i + 1)) u
            = azim (0:V3) (vv i) (vv (i + 1)) (vv (i + s.k - 1))
        · refine absurd hut (fun hc => ?_)
          exact axisBoundKill_p35 (b := vv i) (c := vv (i + 1))
            (d := vv (i + s.k - 1)) (u := w) (w := u)
            (azim (0:V3) (vv (i + s.k - 1)) (vv i) (vv (i + s.k - 1 + s.k - 1)))
            hbne (hvne (i + s.k - 1)) hncbc hncdb hc hncbu hxwcol
            (fun hc => hC1f ⟨hc.2, hc.1⟩) (fun hc => hC2f ⟨hc.2, hc.1⟩)
            (fun hc => hC4f ⟨hc.2, hc.1⟩) (fun hc => hC3f ⟨hc.2, hc.1⟩) hfarw hfarθ
        · have hφt : azim (0:V3) (vv i) (vv (i + 1)) t
              = azim (0:V3) (vv i) (vv (i + 1)) u :=
            ((azim_eq_azim_iff hncbc hncbu hncbt).mpr htin2).symm
          refine ⟨hncbt, ?_, ?_⟩
          · rw [hφt]; exact hφupos
          · rw [hφt]; exact lt_of_le_of_ne huθ hut
      · -- w in the dart plane, off-axis: cone transfer then one sandwich step
        have hncbw : ¬ Collinear3 0 (vv i) w := hxwcol
        have hwu0 : azim 0 (vv i) w u
            = azim (0:V3) (vv i) (vv (i + 1)) u - azim (0:V3) (vv i) (vv (i + 1)) w := by
          have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
            (w1 := w) (w2 := u) hbne hncbc hncbw hncbu (le_of_lt hgt)
          linarith
        have hwult : azim 0 (vv i) w u < Real.pi := by
          by_contra hge
          have hπ : azim (0:V3) (vv i) (vv (i + 1)) u = Real.pi := by
            have := huθ
            linarith
          have hz : azim (0:V3) (vv i) (vv (i + 1)) w = 0 := hφw0
          exact (hPM i).2.2.2 ⟨hπ, hz⟩
        have htw : t - 0 = γ • (w - 0) + β • (u - 0) := by rw [htr]; module
        obtain ⟨hncbt, hwt0, hwtu⟩ := coneMem_p35 (v0 := (0:V3)) (ax := vv i) (u := w)
          (w := u) (t := t) hncbw hncbu (Ne.symm huw)
          (by rw [hwu0]; linarith) hwult γ β hγ hβ htw
        have hφteq : azim (0:V3) (vv i) (vv (i + 1)) t = azim 0 (vv i) w t := by
          have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
            (w1 := w) (w2 := t) hbne hncbc hncbw hncbt
            (by rw [hφw0]; exact azim_nonneg 0 (vv i) (vv (i + 1)) t)
          rw [hφw0] at h
          linarith
        refine ⟨hncbt, ?_, ?_⟩
        · rw [hφteq]; exact hwt0
        · rw [hφteq]; linarith [hwtu, hwu0]
    · -- 0 < φw ≤ φu: cone transfer (L5) + strict sandwich (L6), w/u swapped
      have hφwp : 0 < azim (0:V3) (vv i) (vv (i + 1)) w :=
        lt_of_le_of_ne hwθ0 (Ne.symm hφw0)
      have hncbu : ¬ Collinear3 0 (vv i) u := fun hc =>
        ne_of_gt (lt_of_le_of_lt hwθ0 hgt) (azimAxis_p35 hc)
      have hncbw : ¬ Collinear3 0 (vv i) w := fun hc => hφw0 (azimAxis_p35 hc)
      have hwu0 : azim 0 (vv i) w u
          = azim (0:V3) (vv i) (vv (i + 1)) u - azim (0:V3) (vv i) (vv (i + 1)) w := by
        have h := triAzimAdd_p35 (x := (0:V3)) (v := vv i) (u := vv (i + 1))
          (w1 := w) (w2 := u) hbne hncbc hncbw hncbu (le_of_lt hgt)
        linarith
      have hwult : azim 0 (vv i) w u < Real.pi := by
        by_contra hge
        have hπ : azim (0:V3) (vv i) (vv (i + 1)) u = Real.pi := by
          have := huθ
          linarith
        have hz : azim (0:V3) (vv i) (vv (i + 1)) w = 0 := by linarith
        exact (hPM i).2.2.2 ⟨hπ, hz⟩
      have htw : t - 0 = γ • (w - 0) + β • (u - 0) := by rw [htr]; module
      obtain ⟨hncbt, hwt0, hwtu⟩ := coneMem_p35 (v0 := (0:V3)) (ax := vv i) (u := w)
        (w := u) (t := t) hncbw hncbu (Ne.symm huw)
        (by rw [hwu0]; linarith) hwult γ β hγ hβ htw
      obtain ⟨hφtp, hφtlt⟩ := azimSandwich_p35 (v0 := (0:V3)) (ax := vv i) (b := vv (i + 1))
        (p := w) (q := u) (r := t) (Ne.symm hbne) hncbc hncbw hncbu hncbt hφwp
        (le_of_lt hgt) (huθ.trans hspanπ) hwt0 hwtu
      refine ⟨hncbt, hφtp, ?_⟩
      linarith [hφtlt, huθ]
  -- DISCHARGES (lkgrqui-tecoxbm3-w2): source QKNVMLB.hl 3838-4024 via
  -- TECOXBM.hl:1456 (TECOXBM1).  Reduction obtained this lane: per dart
  -- `i`, `wedgeCyclic_p35` renders the target as
  -- `wedge 0 (vv i) (vv (i+1)) (vv (i+k-1))`; L1 gives the consecutive
  -- non-collinearity of the sector rays; the membership data is the
  -- open triangle `t = β•u + γ•w` (`triMemAffGt_p35`, 0 < β, 0 < γ);
  -- L2+L5 close the generic dart when 0 < azim(b,c) < π; L6
  -- (`azimSandwich_p35`) transfers the cone placement `azim(u,t) ∈
  -- (0, azim(u,w))` (itself from L2+L5 at the diag rays, needing
  -- `azim 0 (vv i) u w < π`) to the sector rays.
  -- REMAINING ROOT (lkgrqui-sectortri-w2 update): the flat-dart half of
  -- L3 is CLOSED below — `dartSpanNeCyc_p35` (Fan.unique_azim0_point_fan
  -- via the fan conjunct that `BBsV39` itself carries, `fanOfBB_p35`;
  -- NO LA11 Section C dependency) gives
  -- `azim 0 (vv i) (vv (i+1)) (vv (i+k-1)) ≠ 0`, and `wedgeSectorMem_p35`
  -- (above) gives the span ≤ π.  What remains is exactly the named
  -- residual `sectorTriPlaneMiss_p35` (below): the four azimuth-corner
  -- exclusions of the diag pair (u, w) at every dart — the azimuth
  -- rendering of the dart-plane miss `¬(u ∈ aff {0, vv j, vv (j+1)} ∧
  -- w ∈ aff {…})` = the strictness core of HOL AFF_GT_INTER_AFF_SY
  -- (TECOXBM.hl:311) — plus its azimuth assembly into this statement
  -- (est. ≈200–300 ln): trichotomy on `azim 0 (vv i) (vv (i+1)) u` vs
  -- `… w`; the θ-corner (C2) is consumed at dart `i+k-1`; the
  -- same-azimuth branch goes through `affGt_pair_iff` +
  -- `azim_eq_zero_iff_alt` + `triAzimAdd_p35` in both orders
  -- (`azim_compl` idempotence at 0).  `_hdist` is load-bearing: with
  -- step02 it feeds NONPARALLEL_BALL_ANNULUS, killing antipodal diag
  -- pairs (`¬ Collinear3 0 u w`).

/-- step02 (HOL 3775-3838; the per-case `SUBGOAL &2 <= norm (u - w)`, same
shape at k = 4/5/6): the diagonal distance is at least 2 — the `is_scs`
a-lower-bound at the diagonal indices transported by `BBs` (`a i j ≤
dist (vv i) (vv j)`; the NOT_EQ_DIAG_p35 core). -/
theorem TECOXBMv2_step02_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w) (hBB : BBsV39 s vv) :
    (2 : ℝ) ≤ dist u w := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hp' : p % s.k < s.k := Nat.mod_lt _ hk0
  have hq' : q % s.k < s.k := Nat.mod_lt _ hk0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd2, -, -, -, -, -⟩ := hscs
  have h2 : (2 : ℝ) ≤ s.a (p % s.k) (q % s.k) :=
    hd2 (p % s.k) (q % s.k) ⟨hp', hq', fun e => hdiag.1 e⟩
  have h3 : s.a (p % s.k) (q % s.k) ≤ dist u w := by
    have hb := (hBB.2.2.1 (p % s.k) (q % s.k)).1
    rwa [hp, hq] at hb
  exact h2.trans h3

/-- step03 (HOL 3774-3812 / 3874-3880 / 3954-3960; the per-case
`{u,w} SUBSET V_SY v` window assembly, `v = vector[vv 1;..;vv k;vv 0]`): the
diagonal endpoints lie in the k-window fan vertex set
`V_SY_p4 (cycRow_p23 vv k)` — the LocalAuto23 `IS_SCS_IN_V_SY_{4,5,6}_p23`
route replaces the HOL `IN_IMAGE_VV` + `V_E_FF_IS_SCS_CASES` combination. -/
theorem TECOXBMv2_step03_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
    (hscs : isScsV39 s) (_hdiag : scsDiag s.k p q)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hk : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) :
    {u, w} ⊆ V_SY_p4 (cycRow_p23 vv s.k) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have mem : ∀ j : ℕ, j < s.k → vv j ∈ V_SY_p4 (cycRow_p23 vv s.k) := by
    intro j hj
    rcases hk with hk | hk | hk
    · rw [hk] at hj ⊢; exact IS_SCS_IN_V_SY_4_p23 vv j hj
    · rw [hk] at hj ⊢; exact IS_SCS_IN_V_SY_5_p23 vv j hj
    · rw [hk] at hj ⊢; exact IS_SCS_IN_V_SY_6_p23 vv j hj
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [← hp]; exact mem _ (Nat.mod_lt _ hk0)
  · rw [← hq]; exact mem _ (Nat.mod_lt _ hk0)

/-- step04 (HOL 3838-3900: the `:2+2` window; `Tecoxbm.TECOXBM` consumption
TECOXBM.hl:1726): every k = 4 fan dart wedge contains the diagonal cone.
FROZEN RESIDUAL, assumption-form: `hIN`/`hVEF` are exactly the conclusions
of LocalAuto23 `IN_IS_SCS_CASE_4_p23` / `V_E_FF_IS_SCS_CASES_4_p23` (both
`sorry` there), and the wedge step itself is HOL `Tecoxbm.TECOXBM`
(TECOXBM.hl:1726 = TECOXBM1 hl:1456 + TECOXBM2 hl:1682), whose only Lean
ports are `TECOXBM1_p11`/`TECOXBM2_p11` (LocalAuto11:1515/1529) — both
`sorry`, and LocalAuto11 is unreachable from LocalAuto35 (it imports
LocalAuto2; LocalAuto1 + LocalAuto2 clash on `atn2PA18` via
PackingAuto18/PackingAuto20).  Closing this and step05 mechanically closes
TECOXBMv2_p35 (template in its DISCHARGES note). -/
theorem TECOXBMv2_step04_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hk : s.k = 4) (hdiag : scsDiag s.k p q)
    (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hIN : flattenRow_p23 vv 4 ∈
      {l : FinVec 4 3 | (∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus) ∧
        CONDITION1_SY_p4
          (fun i j => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
          (fun i j => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
          (cycRow_p23 vv 4) ∧
        CONDITION2_SY_p4 (cycRow_p23 vv 4)})
    (hVEF : V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
      E_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
      F_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E := by
  exact sectorTriCore_p35 s p q u w E FF vv hscs hdiag hdist hp hq hBB hE hFF
  -- DISCHARGES (lkgrqui-tecoxbm3-w2): body closed by the k-generic named
  -- residual `sectorTriCore_p35` (kit above); hIN/hVEF stay hypothesis-form
  -- (LA23 feeders, S7 后收敛).

/-- step05 (HOL 3874-3960 / 3954-4024: the `:2+3` resp. `:3+3` windows;
`Tecoxbm.TECOXBM` consumption): the k = 5 / k = 6 twin of step04.
FROZEN RESIDUAL, assumption-form — same blockers as step04, with the
LocalAuto23 feeders taken per branch (`IN_IS_SCS_CASE_{5,6}_p23`,
`V_E_FF_IS_SCS_CASES_{5,6}_p23`, all `sorry`). -/
theorem TECOXBMv2_step05_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hk : s.k = 5 ∨ s.k = 6) (hdiag : scsDiag s.k p q)
    (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hBB : BBsV39 s vv)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hIN : (s.k = 5 → flattenRow_p23 vv 5 ∈
          {l : FinVec 5 3 | (∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus) ∧
            CONDITION1_SY_p4
              (fun i j => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
              (fun i j => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
              (cycRow_p23 vv 5) ∧
            CONDITION2_SY_p4 (cycRow_p23 vv 5)}) ∧
      (s.k = 6 → flattenRow_p23 vv 6 ∈
          {l : FinVec 6 3 | (∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus) ∧
            CONDITION1_SY_p4
              (fun i j => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
              (fun i j => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
              (cycRow_p23 vv 6) ∧
            CONDITION2_SY_p4 (cycRow_p23 vv 6)}))
    (hVEF : (s.k = 5 → V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
          F_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) ∧
      (s.k = 6 → V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
          F_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ)) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E := by
  exact sectorTriCore_p35 s p q u w E FF vv hscs hdiag hdist hp hq hBB hE hFF
  -- DISCHARGES (lkgrqui-tecoxbm3-w2): same reduction as step04 — body
  -- closed by `sectorTriCore_p35`; hIN/hVEF stay hypothesis-form.

/-- step06 (HOL 4024 assembly: the three-case fold-back): the total
TECOXBMv2 conclusion from step01 and the per-case wedge statements.
Closed — so once step04/step05 close, `TECOXBMv2_p35` is the feeder
derivation + this lemma (template in its DISCHARGES note). -/
theorem TECOXBMv2_step06_p35 (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (vv : ℕ → V3) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q)
    (h4 : s.k = 4 → ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E)
    (h56 : s.k = 5 ∨ s.k = 6 →
      ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E) :
    ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E := by
  rcases TECOXBMv2_step01_p35 s p q hscs hdiag with h | h | h
  · exact h4 h
  · exact h56 (Or.inl h)
  · exact h56 (Or.inr h)

/-! ### TECOXBMv2 wedge kit (lkgrqui-tecoxbm2-w2; TECOXBM.hl 1682/1456)

The `Tecoxbm.TECOXBM` consumption of step04/05 splits into the
non-collinearity half (TECOXBM2, TECOXBM.hl:1682) and the wedge-coverage
half (TECOXBM1, TECOXBM.hl:1456).  This kit closes the first half genuinely
(the HOL proof of TECOXBM2 is `MATCH_MP_TAC NONPARALLEL_BALL_ANNULUS`, and
the LocalAuto4 twin is proved) and concretizes the second half to the cyclic
two-point neighbour rendering, reducing step04/05 to the sector-triangle
core stated in their DISCHARGES notes. -/

/-- TECOXBM.hl:1682 `TECOXBM2`, conclusion core (annulus packaging): two
diagonal endpoints in the ball annulus at distance in `[2, cstab]` are
non-collinear with the origin.  The B_SY1/vecmats packaging transport is:
rows of a `B_SY1` table lie in `ballAnnulus` (first `B_SY1_p4` conjunct;
for the step04/05 consumption, `hBB.1`), `2 ≤ norm (u-w)` is step02 and
`norm (u-w) ≤ cstab` the `hdist` hypothesis. -/
theorem TECOXBM2_p35 (u w : V3) (hu : u ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
    (h2 : (2:ℝ) ≤ ‖u - w‖) (hc : ‖u - w‖ ≤ cstab) : ¬ Collinear3 0 u w :=
  NONPARALLEL_BALL_ANNULUS hu hw h2 hc


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
  exact sectorTriCore_p35 s p q u w E FF vv hscs hdiag _hdist hp hq hBB hE hFF
  -- DISCHARGES (lkgrqui-tecoxbm-w2 2026-10-28; updated lkgrqui-tecoxbm2-w2;
  -- closed modulo the named residual by lkgrqui-tecoxbm3-w2): the body is
  -- the k-generic `sectorTriCore_p35` DIRECTLY (same conclusion, hV
  -- unused) — the step04/05/step06 route is recorded above but NOT taken:
  -- it would need the LA23 feeders (IN_IS_SCS_CASE_4_p23 etc., all sorry)
  -- for step04/05's hIN/hVEF, which the k-generic residual bypasses.
  -- Root set = {sectorTriCore_p35} exactly (probe-verified).
  -- source 3730-4024.  Steps 01/02/03/06 closed above (standard three); the
  -- residual debt is exactly `TECOXBMv2_step04_p35` + `TECOXBMv2_step05_p35`
  -- (per-case wedge coverage).  tecoxbm2 status: the TECOXBM2
  -- (non-collinearity) half of the giant is closed in-file
  -- (`TECOXBM2_p35`); the wedge half is reduced to the sector-triangle core
  -- documented at step04's DISCHARGES (HOL route = AFF_GT_INTER_AFF_SY +
  -- Planarity kit, no LA35-world Lean twin).  Closing template once those
  -- two close:
  --   refine TECOXBMv2_step06_p35 s p q u w E FF hscs hdiag ?_ ?_
  --   · intro _; exact TECOXBMv2_step04_p35 s p q u w E FF vv hscs rfl
  --       hdiag hdist hp hq hBB hE hFF (feeder fills)
  --   · intro h56; exact TECOXBMv2_step05_p35 s p q u w E FF vv hscs h56
  --       hdiag hdist hp hq hBB hE hFF (feeder fills)

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

  have hk0 : 0 < k := by have := hscs.2.1; omega
  have hper : Periodic vv k := by rw [← hk]; exact hBB.2.1
  have hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j := by
    intro i j hi hj hne he
    have i' : i < s.k := by rw [hk]; exact hi
    have j' : j < s.k := by rw [hk]; exact hj
    exact vvInjAux_p35 s vv hscs hBB i j i' j' hne he
  exact vvOrbit_p35 hk0 hper hinj hFF u p1 hp1
  -- DISCHARGES (lkgrqui-mid-w2 2026-10-28): source 4024-4061; the rho_node1
  -- orbit follows the cyclic vv ordering — proved via vvOrbit_p35
  -- (periodicity + window injectivity; the HOL DETER_RHO_NODE detour via the
  -- p2-layer local-fan kit is replaced by the cyclic-dart specialization).

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

/-- The vertex re-labelling of the face as pure set algebra (HOL
QKNVMLB.hl:4290-4406, EXTENSION tail): `vPrime_p3` of the k'-window dart set
is the k'-window vertex set.  The face description (the conclusion of
`F_PRIME_EQ_F_vv_p35`) enters as the hypothesis `hF`; with it the axiom face
stays inside the standard three. -/
theorem TRIO_V_OF_FACE_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
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
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
    (hF : Set.range (fun i => (vv (i % k' + p % k), vv ((i + 1) % k' + p % k))) =
      HS.face (u, rhoNode1 FF u)) :
    Set.range (fun i => vv (i % k' + p % k)) =
      vPrime_p3 V (HS.face (u, rhoNode1 FF u)) := by
  rw [← hF]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ⟨vv ((i + 1) % k' + p % k), i, rfl⟩⟩
    rw [← hV]
    exact ⟨i % k' + p % k, rfl⟩
  · rintro ⟨hVx, w', i, hdart⟩
    simp only [Prod.mk.injEq] at hdart
    obtain ⟨h1, -⟩ := hdart
    exact ⟨i, show vv (i % k' + p % k) = x from h1⟩

/-- The edge re-labelling of the face as pure set algebra (HOL
QKNVMLB.hl:4406-4622, EXTENSION tail): `ePrime_p3` of the k'-window dart set
inside `E ∪ {{u,w}}` is the k'-window undirected edge set.  The `E`-membership
of the window edges splits into the cycle branch (`i % k' < k' - 1`, the edge
`{vv a, vv (a+1)}` via `hE`) and the diagonal branch (`i % k' = k' - 1`, the
edge `{w, u}` via `W_EW_K_SCS_ADD_P_p35` + `hp`). -/
theorem TRIO_E_OF_FACE_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
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
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
    (hF : Set.range (fun i => (vv (i % k' + p % k), vv ((i + 1) % k' + p % k))) =
      HS.face (u, rhoNode1 FF u)) :
    Set.range (fun i => {vv (i % k' + p % k), vv ((i + 1) % k' + p % k)}) =
      ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)) := by
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk3 : 3 ≤ k' := by omega
  have hk'0 : 0 < k' := by omega
  have hk0 : 0 < k := by omega
  have hEdge : ∀ i : ℕ,
      {vv (i % k' + p % k), vv ((i + 1) % k' + p % k)} ∈ E ∪ {{u, w}} := by
    intro i
    have himlt : i % k' < k' := Nat.mod_lt _ hk'0
    rcases Nat.lt_or_ge (i % k') (k' - 1) with hlt | hge2
    · have himod : (i + 1) % k' = i % k' + 1 := by
        rw [Nat.add_mod]
        have h1 : (1 : ℕ) % k' = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact Nat.mod_eq_of_lt (by omega)
      have hadd : i % k' + p % k + 1 = i % k' + 1 + p % k := by omega
      refine Set.mem_union_left _ ?_
      rw [himod, ← hE, Set.mem_range]
      refine ⟨i % k' + p % k, ?_⟩
      rw [hadd]
    · have himod : i % k' = k' - 1 := le_antisymm (by omega) hge2
      have himod2 : (i + 1) % k' = 0 := by
        rw [Nat.add_mod]
        have h1 : (1 : ℕ) % k' = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, himod]
        have h2 : k' - 1 + 1 = k' := by omega
        rw [h2]
        simp
      rw [himod, himod2, Nat.zero_add,
        W_EW_K_SCS_ADD_P_p35 s s' p q d' mkj k k' u w vv hs' hk' hk hp hq hscs
          hdiag hBB, hp]
      exact Set.mem_union_right E (by simp [Set.pair_comm])
  rw [← hF]
  ext e
  constructor
  · intro hmem
    rw [Set.mem_range] at hmem
    obtain ⟨i, hei⟩ := hmem
    refine ⟨vv (i % k' + p % k), vv ((i + 1) % k' + p % k), ?_, hEdge i, i, rfl⟩
    simpa using hei.symm
  · intro hmem
    simp only [ePrime_p3, Set.mem_setOf_eq] at hmem
    obtain ⟨v', w', he, -, i, hdart⟩ := hmem
    have hd : vv (i % k' + p % k) = v' ∧ vv ((i + 1) % k' + p % k) = w' := by
      simpa using hdart
    refine ⟨i, ?_⟩
    rw [he, ← hd.1, ← hd.2]

/-! ## Bridge-wave kit: the diag-slice face-cycle azimuth kit
(lkgrqui-fprime-bridge-w2).  The `TECOXBMv2` cone inclusion extracts the
strict azimuth placement of the diagonal endpoints in the cyclic fan; on
it the augmented `azimCycle` value at the diag nodes is computed. -/

/-- Open-segment membership in the open cone `affGt {0} {a, b}` (the
`AFF_GT_1_2` midpoint fact, `t`-parametrized; `Affsign.of_triple` with
`t1 = 1 - t`, `t2 = t`). -/
private theorem segMemAffGt_p35 (a b : V3) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (1 - t) • a + t • b ∈ affGt ({0} : Set V3) {a, b} :=
  Affsign.of_triple (1 - t) t (by linarith) ht
    (by rw [smul_zero, zero_add]) (Ne.symm ha0) (Ne.symm hb0) hab

/-- The two-element `azimCycle`: on a neighbour set `{a, p}` (with `a ≠ p`)
the cycle successor of `p` is `a`. -/
private theorem azimCycle2_p35 {a p : V3} {W : Set V3} (v w : V3) (hap : a ≠ p)
    (hW : W = {a, p}) : azimCycle_p3 W v w p = a := by
  have hsub : ¬(W ⊆ {p}) := by
    intro hc
    exact hap (hc (by rw [hW]; simp))
  rw [azimCycle_p3, if_neg hsub]
  refine epsFixed_p35 ?_ ?_
  · rw [hW]
    refine ⟨hap, by simp, ?_⟩
    intro q hq hqp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with h | h
    · subst h
      exact Or.inr ⟨rfl, le_refl _⟩
    · exact absurd h hqp
  · intro y hy
    rw [hW] at hy
    obtain ⟨hy1, hy2, -⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy2
    rcases hy2 with h | h
    · exact h
    · exact absurd h hy1

/-! ## Slicing-fan kit (lkgrqui-slicingfan-w2): the diagonal sigma-table.

Closes the residual root of `F_PRIME_EQ_F_vv_p35`: the sigma-preimage
uniqueness at the two augmented diagonal nodes.  HOL anchor:
`PROVE_SLICING_FAN` (local_lemmas1.hl:1378-1846, the fan7-with-diagonal
content at :1392/:1427/:1459/:1607).  The vv-world replacement: the
`TECOXBMv2` cone inclusion gives the strict sector placement of the diagonal
endpoints (`wedgeDiagAzim_p35`); the azimuth-addition difference
`azim 0 u w (pred u) = theta_u - alpha` is `azimAddTriple_p35`, a FAN-free
clone of `Kepler.Text.Fan.sum2_azim_fan` (whose proof only consumes the
fan6 non-collinearity, never FAN membership). -/

/-- Shifted-index injectivity: equal `vv`-values at equal shifts force equal
residue windows. -/
private theorem sfVVInjShift_p35 {vv : ℕ → V3} {k : ℕ} (hk0 : 0 < k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) {a b c : ℕ}
    (hac : a < k) (hbc : b < k) (h : vv (a + c) = vv (b + c)) : a = b := by
  have hm : (a + c) % k = (b + c) % k := vvModEq_p35 hk0 hper hinj h
  have hm2 : a % k = b % k := modAddCancel_p35 hm
  rwa [Nat.mod_eq_of_lt hac, Nat.mod_eq_of_lt hbc] at hm2

/-- The vertex and its cyclic predecessor differ once `3 ≤ k`. -/
private theorem sfNePred_p35 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + k - 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have heq : (i + k) - 1 = i + (k - 1) := by omega
  have hm : i % k = ((i + k) - 1) % k := vvModEq_p35 hk0 hper hinj hh
  rw [heq] at hm
  have hm2 : (0 + i) % k = ((k - 1) + i) % k := by
    rw [Nat.zero_add, Nat.add_comm (k - 1) i]
    exact hm
  have h := modAddCancel_p35 hm2
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- The cyclic predecessor and successor differ once `4 ≤ k`. -/
private theorem sfPredNeSucc_p35 {vv : ℕ → V3} {k : ℕ} (hk4 : 4 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv (i + k - 1) ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk4
  have heq : (i + k) - 1 = i + (k - 1) := by omega
  have hm : ((i + k) - 1) % k = (i + 1) % k := vvModEq_p35 hk0 hper hinj hh
  rw [heq] at hm
  have hm2 : ((k - 1) + i) % k = (1 + i) % k := by
    rw [Nat.add_comm (k - 1) i, Nat.add_comm 1 i]
    exact hm
  have h := modAddCancel_p35 hm2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- Edge membership in the cyclic edge set: exactly the two neighbours
(kit-local copy of `vvMemEdge_p35`, which sits behind the insertion point). -/
private theorem sfMemEdge_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k) (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) (y : V3) :
    y ∈ EE_p3 (vv i) E ↔ y = vv (i + k - 1) ∨ y = vv (i + 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have heq : (i + k) - 1 = i + (k - 1) := by omega
  have hnosing : ∀ j : ℕ, vv j ≠ vv (j + 1) := by
    intro j hh
    have h := sfVVInjShift_p35 (a := 0) (b := 1) (c := j) hk0 hper hinj
      (by omega) (by omega) (by rw [Nat.zero_add, Nat.add_comm 1 j]; exact hh)
    omega
  show {vv i, y} ∈ E ↔ _
  constructor
  · intro hy
    rw [← hE] at hy
    obtain ⟨j, hj⟩ := hy
    have m1 : vv j ∈ ({vv i, y} : Set V3) := by rw [← hj]; simp
    have m2 : vv (j + 1) ∈ ({vv i, y} : Set V3) := by rw [← hj]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m1 m2
    rcases m1 with h1 | h1
    · -- vv j = vv i
      have hmod : j % k = i % k := vvModEq_p35 hk0 hper hinj h1
      rcases m2 with h2 | h2
      · -- singleton edge
        exact absurd (h1.trans h2.symm) (hnosing j)
      · refine Or.inr ?_
        rw [← h2]
        exact vvStep_p35 hper hmod
    · -- vv j = y
      rcases m2 with h2 | h2
      · -- vv (j+1) = vv i, vv j = y: y is the cyclic predecessor
        refine Or.inl ?_
        have hmod' : (j + 1) % k = i % k := vvModEq_p35 hk0 hper hinj h2
        have hstep : (j + 1) % k = (i + (k - 1) + 1) % k := by
          rw [show i + (k - 1) + 1 = i + k from by omega, Nat.add_mod_right]
          exact hmod'
        have hpred : j % k = (i + (k - 1)) % k := vvModPred_p35 hk0 hstep
        rw [heq, ← h1, ← periodic_mod_eq_p23 hper (i + (k - 1)), ← hpred,
          ← periodic_mod_eq_p23 hper j]
      · -- vv (j+1) = y = vv j: singleton edge
        exact absurd (h1.trans h2.symm) (hnosing j)
  · rintro (rfl | rfl)
    · show {vv i, vv ((i + k) - 1)} ∈ E
      rw [heq, ← hE]
      refine Set.mem_range.mpr ⟨i + (k - 1), ?_⟩
      show {vv (i + (k - 1)), vv (i + (k - 1) + 1)} = {vv i, vv (i + (k - 1))}
      rw [show i + (k - 1) + 1 = i + k from by omega, ← periodic_mod_eq_p23 hper (i + k),
        Nat.add_mod_right, periodic_mod_eq_p23 hper i]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · show {vv i, vv (i + 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i, rfl⟩

/-- FAN-free azimuth addition (`Kepler.Text.Fan.sum2_azim_fan` clone with the
`FAN x V E` hypothesis replaced by the three fan6-type non-collinearity
facts, which is all its proof consumes). -/
private theorem azimAddTriple_p35 {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hu : ¬ Collinear3 x v u) (h1 : ¬ Collinear3 x v w1) (h2 : ¬ Collinear3 x v w2)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr hxv)
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hu h1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hu h2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec h1 h2 hon hax hxv
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hc3 : azim x v u w2
      = azim x v u w1 + azim x v w1 w2 + (n:ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hnpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-- **The wedge extraction at a cyclic vertex** (the `wedgeDiagAzim` draft of
lkgrqui-fprime-bridge-w2 landed): the `TECOXBMv2` cone inclusion places the
other diagonal endpoint strictly inside the open fan sector at `vv i` and
makes it non-collinear with `0` and `vv i` (the vv-world replacement of the
strictness core of HOL `FACE_MAP_SLICING_HYP_TRANS_POINT`). -/
private theorem wedgeDiagAzim_p35 {vv : ℕ → V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {k : ℕ} (i j : ℕ) (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ a b, a < k → b < k → a ≠ b → vv a ≠ vv b)
    (hE : Set.range (fun a => {vv a, vv (a + 1)}) = E)
    (hFF : Set.range (fun a => (vv a, vv (a + 1))) = FF)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {vv i, vv j} ⊆ wedgeInFanGt_p3 x E)
    (hu0 : vv i ≠ 0) (hj0 : vv j ≠ 0) (hij : vv i ≠ vv j)
    (hnc : ¬ Collinear3 0 (vv i) (vv (i + 1)))
    (hstepne : vv (i + k - 1) ≠ vv (i + 1)) :
    ¬ Collinear3 0 (vv i) (vv j) ∧
      0 < azim 0 (vv i) (vv (i + 1)) (vv j) ∧
      azim 0 (vv i) (vv (i + 1)) (vv j) < azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hee : EE_p3 (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext y
    simpa using sfMemEdge_p35 hk3 hper hinj hE i y
  have hncard : 1 < (EE_p3 (vv i) E).ncard := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstepne])]
    simp
  have hwedge : wedgeInFanGt_p3 (vv i, vv (i + 1)) E =
      Kepler.Geom.wedge 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
    simp only [wedgeInFanGt_p3]
    rw [if_pos hncard]
    show Kepler.Geom.wedge 0 (vv i) (vv (i + 1))
        (azimCycle_p3 (EE_p3 (vv i) E) 0 (vv i) (vv (i + 1)))
      = Kepler.Geom.wedge 0 (vv i) (vv (i + 1)) (vv (i + k - 1))
    rw [azimCycle2_p35 (v := 0) (w := vv i) hstepne hee]
  -- the open-segment midpoint of the diagonal lands in the sector
  have hmidpt : (1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j
      ∈ affGt ({0} : Set V3) {vv i, vv j} :=
    segMemAffGt_p35 _ _ hu0 hj0 hij (2:ℝ)⁻¹ (by norm_num) (by norm_num)
  have hdart : (vv i, vv (i + 1)) ∈ FF := by
    rw [← hFF]; exact Set.mem_range.mpr ⟨i, rfl⟩
  have hmem := hsub _ hdart hmidpt
  rw [hwedge] at hmem
  simp only [Kepler.Geom.wedge, Set.mem_setOf_eq] at hmem
  obtain ⟨hncmid, hpos, hlt⟩ := hmem
  have hncw : ¬ Collinear3 0 (vv i) (vv j) := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := vv i) (w1 := vv j) hu0).mp hcol
    apply hncmid
    refine (collinear3_iff_smul (v := 0) (w := vv i)
      (w1 := (1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j) hu0).mpr ⟨(1 + c) / 2, ?_⟩
    have e1 : (1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j - 0
        = (1 - (2:ℝ)⁻¹) • (vv i - 0) + (2:ℝ)⁻¹ • (vv j - 0) := by module
    rw [e1, hc]
    module
  have hrayEq : azim 0 (vv i) (vv (i + 1)) (vv j)
      = azim 0 (vv i) (vv (i + 1)) ((1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j) :=
    (azim_eq_azim_iff (v0 := 0) (v1 := vv i) (w := vv (i + 1)) (x := vv j)
      (y := (1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j) hnc hncw hncmid).mpr
      ((affGt_pair_iff (v0 := 0) (v1 := vv i) (x := vv j)
          (y := (1 - (2:ℝ)⁻¹) • vv i + (2:ℝ)⁻¹ • vv j)
          (Ne.symm hu0) hj0 (fun hh => hij hh.symm)).mpr
        ⟨(2:ℝ)⁻¹, by norm_num, 1 - (2:ℝ)⁻¹, by module⟩)
  exact ⟨hncw, by rw [hrayEq]; exact hpos, by rw [hrayEq]; exact hlt⟩

/-- **The diagonal-node sigma table and sigma-preimage uniqueness** — the
residual root of `F_PRIME_EQ_F_vv_p35`, i.e. the fan7-with-diagonal content
of HOL `PROVE_SLICING_FAN` (local_lemmas1.hl:1378-1846).  At an augmented
node `u` whose neighbour set is `{pr, s, a}` (`s`/`pr` the cyclic
successor/predecessor, `a` the diagonal endpoint strictly placed inside the
open sector: `0 < azim 0 u s a < azim 0 u s pr`), the azimuth-addition
difference `azim 0 u a pr = theta_u - alpha` (`azimAddTriple_p35` +
`azim_compl`) fixes the augmented `azimCycle` on `{pr, s, a}` to the
3-cycle `s ↦ a ↦ pr ↦ s`, and the `ivsAzimCycle_p3` preimages are read off
the table (uniqueness = table + pairwise distinctness, no geometry). -/
private theorem sigmaTableDiag_p35 (u s pr a : V3)
    (hnc1 : ¬ Collinear3 0 u s) (hncp : ¬ Collinear3 0 u pr) (hspr : pr ≠ s)
    (has : a ≠ s) (hap : a ≠ pr)
    (hnca : ¬ Collinear3 0 u a)
    (hpos : 0 < azim 0 u s a)
    (hlt : azim 0 u s a < azim 0 u s pr) :
    azimCycle_p3 {pr, s, a} 0 u s = a ∧
    azimCycle_p3 {pr, s, a} 0 u a = pr ∧
    azimCycle_p3 {pr, s, a} 0 u pr = s ∧
    ivsAzimCycle_p3 {pr, s, a} 0 u a = s ∧
    ivsAzimCycle_p3 {pr, s, a} 0 u s = pr ∧
    ivsAzimCycle_p3 {pr, s, a} 0 u pr = a := by
  have hu0 : u ≠ 0 := fun he => hnc1 (collinear3_of_eq he)
  have hαne : azim 0 u s a ≠ 0 := by
    intro h
    rw [h] at hpos
    exact absurd hpos (by norm_num)
  have hθpos : 0 < azim 0 u s pr := lt_of_le_of_lt hpos.le hlt
  have hθne : azim 0 u s pr ≠ 0 := by
    intro h
    rw [h] at hθpos
    exact absurd hθpos (by norm_num)
  -- the azimuth-addition difference at the diagonal node: THE single point
  have hadd : azim 0 u s pr = azim 0 u s a + azim 0 u a pr :=
    azimAddTriple_p35 hu0 hnc1 hnca hncp hlt.le
  have hApr : azim 0 u a pr = azim 0 u s pr - azim 0 u s a := by linarith
  have hAs : azim 0 u a s = 2 * Real.pi - azim 0 u s a := by
    rw [azim_compl hnc1 hnca, if_neg hαne]
  have hPs : azim 0 u pr s = 2 * Real.pi - azim 0 u s pr := by
    rw [azim_compl hnc1 hncp, if_neg hθne]
  have hPa : azim 0 u pr a = 2 * Real.pi - azim 0 u a pr := by
    rw [azim_compl hnca hncp, if_neg (by rw [hApr]; linarith)]
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hθ2pi : azim 0 u s pr < 2 * Real.pi := azim_lt_two_pi 0 u s pr
  -- the neighbour set has three pairwise distinct points
  have hmemP : (pr : V3) ∈ ({pr, s, a} : Set V3) := by simp
  have hmemS : (s : V3) ∈ ({pr, s, a} : Set V3) := by simp
  have hsubS : ¬({pr, s, a} : Set V3) ⊆ {s} := fun hc => hspr (hc hmemP)
  have hsubA : ¬({pr, s, a} : Set V3) ⊆ {a} := fun hc => hap (hc hmemP).symm
  have hsubP : ¬({pr, s, a} : Set V3) ⊆ {pr} := fun hc => hspr.symm (hc hmemS)
  have hWne : ({pr, s, a} : Set V3) ≠ ∅ := by
    intro he
    have : (pr : V3) ∈ (∅ : Set V3) := by rw [← he]; simp
    exact absurd this (by simp)
  -- the sigma table (three entries of the augmented cycle)
  have hsigS : azimCycle_p3 {pr, s, a} 0 u s = a := by
    rw [azimCycle_p3, if_neg hsubS]
    refine epsFixed_p35 ⟨has, by simp, ?_⟩ ?_
    · intro q hq hqp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inl hlt
      · exact absurd rfl hqp
      · exact Or.inr ⟨rfl, le_refl _⟩
    · intro y hy
      obtain ⟨yne, ymem, ymin⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
      rcases ymem with rfl | rfl | rfl
      · rcases ymin a (by simp) has with h | ⟨h, -⟩
        · linarith
        · linarith
      · exact absurd rfl yne
      · rfl
  have hsigA : azimCycle_p3 {pr, s, a} 0 u a = pr := by
    rw [azimCycle_p3, if_neg hsubA]
    refine epsFixed_p35 ⟨hap.symm, by simp, ?_⟩ ?_
    · intro q hq hqp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr ⟨rfl, le_refl _⟩
      · refine Or.inl ?_
        rw [hAs, hApr]
        linarith
      · exact absurd rfl hqp
    · intro y hy
      obtain ⟨yne, ymem, ymin⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
      rcases ymem with rfl | rfl | rfl
      · rfl
      · rcases ymin pr (by simp) (fun h => hap h.symm) with h | ⟨h, -⟩
        · rw [hAs, hApr] at h
          linarith
        · rw [hAs, hApr] at h
          linarith
      · exact absurd rfl yne
  have hsigP : azimCycle_p3 {pr, s, a} 0 u pr = s := by
    rw [azimCycle_p3, if_neg hsubP]
    refine epsFixed_p35 ⟨hspr.symm, by simp, ?_⟩ ?_
    · intro q hq hqp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact absurd rfl hqp
      · exact Or.inr ⟨rfl, le_refl _⟩
      · refine Or.inl ?_
        rw [hPs, hPa, hApr]
        linarith
    · intro y hy
      obtain ⟨yne, ymem, ymin⟩ := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
      rcases ymem with rfl | rfl | rfl
      · exact absurd rfl yne
      · rfl
      · rcases ymin s (by simp) (fun h => hspr h.symm) with h | ⟨h, -⟩
        · rw [hPs, hPa, hApr] at h
          linarith
        · rw [hPs, hPa, hApr] at h
          linarith
  refine ⟨hsigS, hsigA, hsigP, ?_, ?_, ?_⟩
  · -- ivs_u(a) = s : the sigma-preimage of a is s
    rw [ivsAzimCycle_p3, if_neg hWne]
    refine epsFixed_p35 ⟨by simp, hsigS⟩ ?_
    intro y hy
    obtain ⟨ymem, hsig⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
    rcases ymem with rfl | rfl | rfl
    · rw [hsigP] at hsig
      exact absurd hsig.symm has
    · rfl
    · rw [hsigA] at hsig
      exact absurd hsig.symm hap
  · -- ivs_u(s) = pr : the sigma-preimage of s is pr
    rw [ivsAzimCycle_p3, if_neg hWne]
    refine epsFixed_p35 ⟨by simp, hsigP⟩ ?_
    intro y hy
    obtain ⟨ymem, hsig⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
    rcases ymem with rfl | rfl | rfl
    · rfl
    · rw [hsigS] at hsig
      exact absurd hsig has
    · rw [hsigA] at hsig
      exact absurd hsig hspr
  · -- ivs_u(pr) = a : the sigma-preimage of pr is a
    rw [ivsAzimCycle_p3, if_neg hWne]
    refine epsFixed_p35 ⟨by simp, hsigA⟩ ?_
    intro y hy
    obtain ⟨ymem, hsig⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
    rcases ymem with rfl | rfl | rfl
    · rw [hsigP] at hsig
      exact absurd hsig hspr.symm
    · rw [hsigS] at hsig
      exact absurd hsig hap
    · rfl

private theorem hkerMod_p35 (k x : ℕ) : (x - x % k) % k = 0 := by
  have h1 := Nat.div_add_mod x k
  have h : x - x % k = k * (x / k) := by
    calc x - x % k = (k * (x / k) + x % k) - x % k := by rw [h1]
      _ = k * (x / k) := Nat.add_sub_cancel_right _ _
  rw [h, Nat.mul_mod_right]

private theorem hadd0Mod_p35 (k : ℕ) (hk : 0 < k) :
    ∀ a c : ℕ, c % k = 0 → (a + c) % k = a % k := by
  intro a c hc
  have hcm : c = k * (c / k) := by
    have h := Nat.div_add_mod c k
    rw [hc, Nat.add_zero] at h
    exact h.symm
  rw [hcm, Nat.mul_comm k (c / k), Nat.add_mul_mod_self_right]

private theorem sfModPredCore_p35 {k x : ℕ} (hx : 0 < x) (hk : 0 < k) :
    (x - 1) % k = (x % k + k - 1) % k := by
  have hler : x % k ≤ x := Nat.mod_le x k
  rcases Nat.lt_or_ge (x % k) 1 with hr | hr
  · have hxk : x % k = 0 := by omega
    have hdm : x = k * (x / k) := by
      have h := Nat.div_add_mod x k
      rw [hxk] at h
      omega
    have hdd : 1 ≤ x / k := by
      rcases Nat.eq_zero_or_pos (x / k) with h0 | h1
      · rw [h0, Nat.mul_zero] at hdm
        omega
      · exact h1
    have hkx : k ≤ k * (x / k) := Nat.le_mul_of_pos_right k hdd
    have hmul : k * (x / k) - 1 = k * (x / k - 1) + (k - 1) := by
      have h1 : k * (x / k - 1) = k * (x / k) - k := by
        rw [Nat.mul_sub, Nat.mul_one]
      set A := k * (x / k) with hA
      have h2 : k * (x / k - 1) = A - k := h1
      have hkxA : k ≤ A := hkx
      rw [h2]
      omega
    have e1 : x - 1 = k * (x / k - 1) + (k - 1) := by
      conv_lhs => rw [hdm]
      exact hmul
    rw [e1, Nat.mul_add_mod, hxk, Nat.zero_add]
  · have hsub : x - 1 = (x % k - 1) + (x - x % k) := by omega
    rw [hsub, hadd0Mod_p35 k hk _ _ (hkerMod_p35 k x)]
    have e2 : x % k + k - 1 = (x % k - 1) + k := by omega
    rw [e2, Nat.add_mod_right]

private theorem sfModPredBack_p35 {k x : ℕ} (hk : 0 < k) :
    (x % k + k - 1) % k = (x + k - 1) % k := by
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · rw [h0, Nat.zero_mod, Nat.zero_add]
  · have hler : x % k ≤ x := Nat.mod_le x k
    rcases Nat.lt_or_ge (x % k) 1 with hr | hr
    · have hxk : x % k = 0 := by omega
      have hdm : x = k * (x / k) := by
        have h := Nat.div_add_mod x k
        rw [hxk] at h
        omega
      have e2 : x + k - 1 = k * (x / k) + (k - 1) := by
        conv_lhs => rw [hdm]
        omega
      rw [hxk, Nat.zero_add, e2, Nat.mul_add_mod]
    · have hsub : x - 1 = (x % k - 1) + (x - x % k) := by omega
      have hrw : (x - 1) % k = (x % k - 1) % k := by
        rw [hsub, hadd0Mod_p35 k hk _ _ (hkerMod_p35 k x)]
      have e2 : x + k - 1 = (x - 1) + k := by omega
      have e3 : x % k + k - 1 = (x % k - 1) + k := by omega
      rw [e3, Nat.add_mod_right, e2, Nat.add_mod_right, hrw]

private theorem sfModPred_p35 {k x y : ℕ} (hx : 0 < x) (hk : 0 < k) (h : x % k = y % k) :
    (x - 1) % k = (y + k - 1) % k := by
  rw [sfModPredCore_p35 hx hk, h]
  exact sfModPredBack_p35 hk

/-- common-summand cancellation of residue equality. -/
private theorem sfModMod_p35 {k a b c : ℕ} (h : a % k = b % k) :
    (a + c) % k = (b + c) % k :=
  Nat.ModEq.add_right c h

private theorem sfVVMod_p35 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) {a b : ℕ}
    (h : a % k = b % k) : vv a = vv b := by
  rw [← periodic_mod_eq_p23 hper a, ← periodic_mod_eq_p23 hper b, h]

private theorem sfPermPow_p35 {α : Type*} [DecidableEq α] (f : Equiv.Perm α) (n : ℕ) (x : α) :
    (f ^ n) x = (f : α → α)^[n] x := by
  have key : ∀ n x, (f ^ n) x = (f : α → α)^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply, ih]
  exact key n x

private theorem sfDartMem_p35 {a b : V3} {E : Set (Set V3)} {V : Set V3} (hE : {a, b} ∈ E) :
    (a, b) ∈ dartsOfHyp_p3 E V := by
  refine Set.mem_union_left _ ?_
  show {(a, b).1, (a, b).2} ∈ E
  simpa using hE

private theorem ivsTwo_p35 {b a c : V3} (hac : a ≠ c) :
    ivsAzimCycle_p3 ({a, c} : Set V3) 0 b a = c ∧
      ivsAzimCycle_p3 ({a, c} : Set V3) 0 b c = a := by
  have hWne : ({a, c} : Set V3) ≠ ∅ := by
    intro he
    have : (a : V3) ∈ (∅ : Set V3) := by rw [← he]; simp
    exact absurd this (by simp)
  have hσc : azimCycle_p3 ({a, c} : Set V3) 0 b c = a :=
    azimCycle2_p35 (v := 0) (w := b) hac rfl
  have hσa : azimCycle_p3 ({a, c} : Set V3) 0 b a = c := by
    have h := azimCycle2_p35 (v := 0) (w := b) (a := c) (p := a) (W := ({c, a} : Set V3))
      hac.symm rfl
    have hset : ({c, a} : Set V3) = {a, c} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at h
  constructor
  · rw [ivsAzimCycle_p3, if_neg hWne]
    refine epsFixed_p35 ⟨by simp, hσc⟩ ?_
    intro y hy
    obtain ⟨ymem, hsig⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
    rcases ymem with rfl | rfl
    · rw [hσa] at hsig
      exact absurd hsig.symm hac
    · rfl
  · rw [ivsAzimCycle_p3, if_neg hWne]
    refine epsFixed_p35 ⟨by simp, hσa⟩ ?_
    intro y hy
    obtain ⟨ymem, hsig⟩ := hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ymem
    rcases ymem with rfl | rfl
    · rfl
    · rw [hσc] at hsig
      exact absurd hsig hac


/-- interior augmented neighbourhood: away from the diagonal endpoints the
neighbour set is unchanged. -/
private theorem sfEEinterior_p35 {vv : ℕ → V3} {E : Set (Set V3)} {u w : V3} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (s : ℕ) (hsu : vv s ≠ u) (hsw : vv s ≠ w) :
    EE_p3 (vv s) (E ∪ {{u, w}}) = {vv (s + k - 1), vv (s + 1)} := by
  ext x
  have hkey := sfMemEdge_p35 hk3 hper hinj hE s x
  simp only [EE_p3, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro (h | h)
    · exact hkey.mp h
    · exfalso
      -- {vv s, x} = {u, w} forces vv s ∈ {u, w}
      have hm : vv s ∈ ({u, w} : Set V3) := by rw [← h]; simp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact hsu hm
      · exact hsw hm
  · rintro (h | h)
    · exact Or.inl (hkey.mpr (Or.inl h))
    · exact Or.inl (hkey.mpr (Or.inr h))


/-- collinearity is symmetric in the last two arguments. -/
private theorem sfCollComm_p35 {a b : V3} (h : ¬ Collinear3 0 a b) : ¬ Collinear3 0 b a := by
  intro hc
  apply h
  show Collinear ℝ ({0, a, b} : Set V3)
  have hset : ({0, a, b} : Set V3) = {0, b, a} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hc
-- HOL `F_PRIME_EQ_F_vv` (QKNVMLB.hl:4622-4838).  Residual-root status
-- (lkgrqui-slicingfan-w2): the PRECURSOR KIT IS CLOSED AND LANDED above —
-- `azimAddTriple_p35` (FAN-free azimuth addition = the azim-addition
-- difference `azim 0 u w (pred u) = theta_u - alpha`),
-- `wedgeDiagAzim_p35` (strict sector placement from the TECOXBMv2 cone
-- inclusion), `sigmaTableDiag_p35` (THE single point: the diagonal-node
-- sigma 3-cycle table + sigma-preimage uniqueness = the fan7-with-diagonal
-- content of HOL PROVE_SLICING_FAN, local_lemmas1.hl:1378-1846), plus
-- `ivsTwo_p35`/`sfEEinterior_p35`/`sfVVMod_p35`/`sfPermPow_p35`/
-- `sfDartMem_p35`/`sfModPred_p35`.  REMAINING (WIP, drafts/kit_body.lean
-- in lane snapshots): the F_PRIME body cascade — the three-class
-- ff-transition table (interior 2-cycle ivs / turning dart (pred w, w) ↦
-- (w, u) / trans dart (w, u) ↦ (u, succ u) via hivsU/hivsW above), the
-- orbit induction `hiter`, and the orbitMap assembly — all tactic-level
-- (no new mathematics; ~14 residual elaboration errors, error log
-- probes/compile_c12.log in lane snapshots).
-- DISCHARGES: source 4622-4838; V/E below close automatically (TRIO_*).
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
  -- 0. the cyclic world
  obtain ⟨-, -, -, hFaceM⟩ := hHS
  have hk0 : 0 < k := by rw [← hk]; have := hscs.2.1; omega
  have hper : Periodic vv k := by rw [← hk]; exact hBB.2.1
  have hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j := by
    intro i j hi hj hne he
    have i' : i < s.k := by rw [hk]; exact hi
    have j' : j < s.k := by rw [hk]; exact hj
    exact vvInjAux_p35 s vv hscs hBB i j i' j' hne he
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk3 : 3 ≤ k' := by rw [← hk']; exact hge.1
  have hklt : k' < k := by
    have h2 := hge.2.2
    rw [hk', hk] at h2
    exact h2
  have hk4 : 4 ≤ k := by omega
  have hk3c : 3 ≤ k := by omega
  have hk'0 : 0 < k' := by omega
  have hPk : p % k < k := Nat.mod_lt _ hk0
  have hQk : q % k < k := Nat.mod_lt _ hk0
  have h1k : (1:ℕ) % k' = 1 := Nat.mod_eq_of_lt (by omega)
  have h1k2 : (2:ℕ) % k' = 2 := Nat.mod_eq_of_lt (by omega)
  have h3sk : 3 < s.k := by rw [hk]; omega
  -- 1. non-collinearity of the four window pairs at the diagonal endpoints
  have hncU1 : ¬ Collinear3 0 u (vv (p % k + 1)) := by
    have h1 := IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 s vv (p % k) h3sk hscs hBB
    rw [hk] at h1
    have e0 : vv (p % k % k) = vv (p % k) := periodic_mod_eq_p23 hper (p % k)
    have e1 : vv ((p % k + 1) % k) = vv (p % k + 1) := periodic_mod_eq_p23 hper (p % k + 1)
    rw [e0, hp, e1] at h1
    exact h1
  have hncUp : ¬ Collinear3 0 u (vv (p % k + k - 1)) := by
    have h2 := IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 s vv (p % k + k - 1) h3sk hscs hBB
    rw [hk] at h2
    have e2 : vv ((p % k + k - 1 + 1) % k) = vv (p % k) := by
      rw [show p % k + k - 1 + 1 = p % k + k from by omega, Nat.add_mod_right,
        periodic_mod_eq_p23 hper (p % k)]
    rw [periodic_mod_eq_p23 hper (p % k + k - 1), e2, hp] at h2
    exact sfCollComm_p35 h2
  have hncW1 : ¬ Collinear3 0 w (vv (q % k + 1)) := by
    have h1 := IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 s vv (q % k) h3sk hscs hBB
    rw [hk] at h1
    have e0 : vv (q % k % k) = vv (q % k) := periodic_mod_eq_p23 hper (q % k)
    have e1 : vv ((q % k + 1) % k) = vv (q % k + 1) := periodic_mod_eq_p23 hper (q % k + 1)
    rw [e0, hq, e1] at h1
    exact h1
  have hncWp : ¬ Collinear3 0 w (vv (q % k + k - 1)) := by
    have h2 := IS_SCS_NOT_COLLINEAR_BBs_CASE_LE_PRIME_3_p35 s vv (q % k + k - 1) h3sk hscs hBB
    rw [hk] at h2
    have e2 : vv ((q % k + k - 1 + 1) % k) = vv (q % k) := by
      rw [show q % k + k - 1 + 1 = q % k + k from by omega, Nat.add_mod_right,
        periodic_mod_eq_p23 hper (q % k)]
    rw [periodic_mod_eq_p23 hper (q % k + k - 1), e2, hq] at h2
    exact sfCollComm_p35 h2
  -- 2. the strict sector placement of the diagonal endpoints (TECOXBMv2 wedge)
  have htecdist : dist u w ≤ cstab := by rw [dist_eq_norm]; exact hnorm
  have hUW : u ≠ w := NOT_EQ_DIAG_p35 s p q u w vv hscs hdiag htecdist
    (by rw [hk]; exact hp) (by rw [hk]; exact hq) hBB
  have hdiagE : {u, w} ∉ E :=
    DIAG_NOT_IN_EDGES_p35 s p q u w E vv hscs hdiag htecdist
      (by rw [hk]; exact hp) (by rw [hk]; exact hq) hE.symm hBB
  have htecc := TECOXBMv2_p35 s p q u w V E FF vv hscs hdiag htecdist
    (by rw [hk]; exact hp) (by rw [hk]; exact hq) hV hE hFF hBB
  rw [← hp, ← hq] at htecc
  have hu0 : u ≠ 0 := fun he => hncU1 (collinear3_of_eq he)
  have hw0 : w ≠ 0 := fun he => hncW1 (collinear3_of_eq he)
  have hUW' : vv (p % k) ≠ vv (q % k) := fun he => hUW (by rw [← hp, ← hq]; exact he)
  have hstepU : vv (p % k + k - 1) ≠ vv (p % k + 1) := sfPredNeSucc_p35 hk4 hper hinj (p % k)
  have hstepW : vv (q % k + k - 1) ≠ vv (q % k + 1) := sfPredNeSucc_p35 hk4 hper hinj (q % k)
  obtain ⟨hncUW, hposU, hltU⟩ := wedgeDiagAzim_p35 (k := k) (p % k) (q % k) hk3c hper hinj
    hE hFF htecc (by rw [hp]; exact hu0) (by rw [hq]; exact hw0)
    (fun he => hUW (by rw [← hp, ← hq]; exact he)) (by rw [hp]; exact hncU1) hstepU
  rw [hp, hq] at hncUW hposU hltU
  have hteccW : ∀ x ∈ FF, affGt ({0} : Set V3) {vv (q % k), vv (p % k)} ⊆ wedgeInFanGt_p3 x E := by
    intro x hx a ha
    exact htecc x hx (by simpa [Set.pair_comm] using ha)
  obtain ⟨hncWU, hposW, hltW⟩ := wedgeDiagAzim_p35 (k := k) (q % k) (p % k) hk3c hper hinj
    hE hFF hteccW (by rw [hq]; exact hw0) (by rw [hp]; exact hu0)
    (fun he => hUW (by rw [← hp, ← hq]; exact he.symm)) (by rw [hq]; exact hncW1) hstepW
  rw [hq, hp] at hncWU hposW hltW
  -- 3. the sigma tables at the two diagonal nodes (THE single point)
  have hwne1 : w ≠ vv (p % k + 1) := by
    intro h
    have hm := (sfMemEdge_p35 (k := k) hk3c hper hinj hE (p % k) w).mpr (Or.inr h)
    rw [hp] at hm
    exact hdiagE hm
  have hwneP : w ≠ vv (p % k + k - 1) := by
    intro h
    have hm := (sfMemEdge_p35 (k := k) hk3c hper hinj hE (p % k) w).mpr (Or.inl h)
    rw [hp] at hm
    exact hdiagE hm
  have huw1 : u ≠ vv (q % k + 1) := by
    intro h
    have hm := (sfMemEdge_p35 (k := k) hk3c hper hinj hE (q % k) u).mpr (Or.inr h)
    rw [hq] at hm
    exact hdiagE (by simpa [Set.pair_comm, EE_p3] using hm)
  have huwP : u ≠ vv (q % k + k - 1) := by
    intro h
    have hm := (sfMemEdge_p35 (k := k) hk3c hper hinj hE (q % k) u).mpr (Or.inl h)
    rw [hq] at hm
    exact hdiagE (by simpa [Set.pair_comm, EE_p3] using hm)
  obtain ⟨-, -, -, hivsU, -, -⟩ :=
    sigmaTableDiag_p35 (u := u) (s := vv (p % k + 1)) (pr := vv (p % k + k - 1)) (a := w)
      hncU1 hncUp (sfPredNeSucc_p35 hk4 hper hinj (p % k)) hwne1 hwneP hncUW hposU hltU
  have hBmod : (k' - 1 + p % k) % k = q % k := by
    have hW := W_EW_K_SCS_ADD_P_p35 s s' p q d' mkj k k' u w vv hs' hk' hk hp hq hscs hdiag hBB
    have hv : vv (k' - 1 + p % k) = vv (q % k) := by rw [hW, hq]
    have h := vvModEq_p35 hk0 hper hinj hv
    rwa [Nat.mod_eq_of_lt hQk] at h
  have hcongr : (k' - 2 + p % k) % k = (q % k + k - 1) % k := by
    have h : (k' - 1 + p % k - 1) % k = (q + k - 1) % k :=
      sfModPred_p35 (k := k) (x := k' - 1 + p % k) (y := q) (by omega) hk0 hBmod
    rw [show k' - 1 + p % k - 1 = k' - 2 + p % k from by omega] at h
    rw [h]
    have e1 : q % k + k - 1 = q % k + (k - 1) := by omega
    have e2 : q + k - 1 = q + (k - 1) := by omega
    rw [e2, e1, Nat.mod_add_mod]
  have hvcongr : vv (k' - 2 + p % k) = vv (q % k + k - 1) := sfVVMod_p35 hper hcongr
  have hncWp' : ¬ Collinear3 0 w (vv (k' - 2 + p % k)) := by
    rw [hvcongr]
    exact hncWp
  have hstepW' : vv (k' - 2 + p % k) ≠ vv (q % k + 1) := fun he =>
    hstepW (hvcongr.symm.trans he)
  have huwP' : u ≠ vv (k' - 2 + p % k) := fun he => huwP (he.trans hvcongr)
  have hltW' : azim 0 w (vv (q % k + 1)) u < azim 0 w (vv (q % k + 1)) (vv (k' - 2 + p % k)) := by
    rw [hvcongr]
    exact hltW
  obtain ⟨-, -, -, -, -, hivsW⟩ :=
    sigmaTableDiag_p35 (u := w) (s := vv (q % k + 1)) (pr := vv (k' - 2 + p % k)) (a := u)
      hncW1 hncWp' hstepW' huw1 huwP' hncWU hposW hltW'
  -- 4. the augmented neighbourhoods
  have hEEu : EE_p3 u (E ∪ {{u, w}}) = {vv (p % k + k - 1), vv (p % k + 1), w} := by
    ext x
    have hkey := sfMemEdge_p35 hk3c hper hinj hE (p % k) x
    rw [hp] at hkey
    simp only [EE_p3, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · rcases hkey.mp h with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
      · have hm1 : w ∈ ({u, x} : Set V3) := by rw [h]; simp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm1
        rcases hm1 with hm | hm
        · exact absurd hm.symm hUW
        · exact Or.inr (Or.inr hm.symm)
    · rintro (hx | hx | hx)
      · exact Or.inl (hkey.mpr (Or.inl hx))
      · exact Or.inl (hkey.mpr (Or.inr hx))
      · exact Or.inr (by rw [hx, Set.pair_comm])
  have hEEw : EE_p3 w (E ∪ {{u, w}}) = {vv (k' - 2 + p % k), vv (q % k + 1), u} := by
    ext x
    have hkey := sfMemEdge_p35 hk3c hper hinj hE (q % k) x
    rw [hq] at hkey
    simp only [EE_p3, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · rcases hkey.mp h with hx | hx
        · exact Or.inl (hx.trans hvcongr.symm)
        · exact Or.inr (Or.inl hx)
      · have hm1 : u ∈ ({w, x} : Set V3) := by rw [h]; simp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm1
        rcases hm1 with hm | hm
        · exact absurd hm hUW
        · exact Or.inr (Or.inr hm.symm)
    · rintro (hx | hx | hx)
      · exact Or.inl (hkey.mpr (Or.inl (hx.trans hvcongr)))
      · exact Or.inl (hkey.mpr (Or.inr hx))
      · exact Or.inr (by rw [hx, Set.pair_comm])
  -- 5. the face-map transition along the k'-window
  set R : ℕ → V3 × V3 := fun i => (vv (i % k' + p % k), vv ((i + 1) % k' + p % k)) with hRdef
  have hR0 : R 0 = (u, vv (p % k + 1)) := by
    simp only [hRdef, Nat.zero_mod, Nat.zero_add, h1k, hp,
      show (1:ℕ) + p % k = p % k + 1 from Nat.add_comm 1 (p % k)]
  have hWew : vv (k' - 1 + p % k) = w := W_EW_K_SCS_ADD_P_p35 s s' p q d' mkj k k' u w vv
    hs' hk' hk hp hq hscs hdiag hBB
  have hstep : ∀ r : ℕ, ffOfHyp_p3 0 V (E ∪ {{u, w}}) (R r) = R (r + 1) := by
    intro r
    generalize ht : r % k' = t
    have htl : t < k' := by rw [← ht]; exact Nat.mod_lt _ (by omega)
    simp only [hRdef]
    have hrw1 : vv (r % k' + p % k) = vv (t + p % k) := by rw [ht]
    rw [hrw1]
    rcases Nat.lt_or_ge t (k' - 1) with h1 | h1
    · have ht1 : (r + 1) % k' = t + 1 := by
        rw [Nat.add_mod, h1k, ht]
        exact Nat.mod_eq_of_lt (by omega)
      rcases Nat.lt_or_ge t (k' - 2) with h2 | h2
      · -- interior dart: the 2-cycle ivs
        have hrw2 : vv ((r + 1) % k' + p % k) = vv (t + 1 + p % k) := by rw [ht1]
        rw [hrw2]
        have hmem : (vv (t + p % k), vv (t + 1 + p % k))
            ∈ dartsOfHyp_p3 (E ∪ {{u, w}}) V := by
          refine Set.mem_union_left _ ?_
          show {vv (t + p % k), vv (t + 1 + p % k)} ∈ E ∪ {{u, w}}
          refine Or.inl ?_
          rw [← hE]
          exact Set.mem_range.mpr ⟨t + p % k, by rw [Nat.add_right_comm]⟩
        rw [ffOfHyp_p3, if_pos hmem]
        dsimp only
        have hshiftNe : ∀ a b : ℕ, a < k → b < k → a ≠ b → vv (a + p % k) ≠ vv (b + p % k) :=
          fun a b ha hb hne => fun he => hne (sfVVInjShift_p35 hk0 hper hinj ha hb he)
        have hbU : vv (t + 1 + p % k) ≠ u := fun he =>
          hshiftNe 0 (t + 1) (by omega) (by omega) (by omega)
            (by rw [Nat.zero_add, hp]; exact he.symm)
        have hbW : vv (t + 1 + p % k) ≠ w := fun he =>
          hshiftNe (t + 1) (k' - 1) (by omega) (by omega) (by omega) (he.trans hWew.symm)
        have hEEb : EE_p3 (vv (t + 1 + p % k)) (E ∪ {{u, w}})
            = {vv (t + p % k), vv (t + 2 + p % k)} := by
          rw [sfEEinterior_p35 hk3c hper hinj hE (t + 1 + p % k) hbU hbW]
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro (hx | hx)
            · left
              rw [hx, show t + 1 + p % k + k - 1 = t + p % k + k from by omega,
                ← periodic_mod_eq_p23 hper (t + p % k),
                ← periodic_mod_eq_p23 hper (t + p % k + k), Nat.add_mod_right]
            · right
              rw [hx, show t + 1 + p % k + 1 = t + 2 + p % k from by omega]
          · rintro (hx | hx)
            · left
              rw [hx, show t + 1 + p % k + k - 1 = t + p % k + k from by omega,
                ← periodic_mod_eq_p23 hper (t + p % k),
                ← periodic_mod_eq_p23 hper (t + p % k + k), Nat.add_mod_right]
            · right
              rw [hx, show t + 1 + p % k + 1 = t + 2 + p % k from by omega]
        have hac : vv (t + p % k) ≠ vv (t + 2 + p % k) :=
          hshiftNe t (t + 2) (by omega) (by omega) (by omega)
        rw [hEEb, (ivsTwo_p35 hac).1]
        have ht2 : (r + 1 + 1) % k' = t + 2 := by
          rw [show r + 1 + 1 = r + 2 from by omega, Nat.add_mod, h1k2, ht]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [hRdef, ht1, ht2]
      · -- the turning dart (pred w, w) ↦ (w, u)
        have ht2 : t = k' - 2 := by omega
        have hrw2 : vv ((r + 1) % k' + p % k) = w := by
          rw [show (r + 1) % k' = k' - 1 from by
            rw [Nat.add_mod, h1k, ht, ht2, show k' - 2 + 1 = k' - 1 from by omega]
            exact Nat.mod_eq_of_lt (by omega), hWew]
        rw [hrw2, ht2]
        have hmem : (vv (k' - 2 + p % k), w) ∈ dartsOfHyp_p3 (E ∪ {{u, w}}) V := by
          refine Set.mem_union_left _ ?_
          show {vv (k' - 2 + p % k), w} ∈ E ∪ {{u, w}}
          refine Or.inl ?_
          rw [hvcongr, ← hq]
          show {vv (q % k + k - 1), vv (q % k)} ∈ E
          have hz := (sfMemEdge_p35 hk3c hper hinj hE (q % k)
            (vv (q % k + k - 1))).mpr (Or.inl rfl)
          simpa [Set.pair_comm, EE_p3] using hz
        rw [ffOfHyp_p3, if_pos hmem]
        dsimp only
        rw [hEEw, hivsW]
        have htA : (r + 1) % k' = k' - 1 := by
          rw [Nat.add_mod, h1k, ht, ht2, show k' - 2 + 1 = k' - 1 from by omega]
          exact Nat.mod_eq_of_lt (by omega)
        have htB : (r + 1 + 1) % k' = 0 := by
          rw [show r + 1 + 1 = r + 2 from by omega, Nat.add_mod, h1k2, ht, ht2,
            show k' - 2 + 2 = k' from by omega, Nat.mod_self]
        simp only [hRdef, htA, htB, Nat.zero_add, hWew, hp]
    · -- the trans dart (w, u) ↦ (u, succ u)
      have ht1 : t = k' - 1 := by omega
      have hrw2 : vv ((r + 1) % k' + p % k) = u := by
        rw [show (r + 1) % k' = 0 from by
          rw [Nat.add_mod, h1k, ht, ht1, show k' - 1 + 1 = k' from by omega, Nat.mod_self],
          Nat.zero_add]
        exact hp
      rw [hrw2, ht1, hWew]
      have hmem : (w, u) ∈ dartsOfHyp_p3 (E ∪ {{u, w}}) V := by
        refine Set.mem_union_left _ ?_
        show {(w, u).1, (w, u).2} ∈ E ∪ {{u, w}}
        refine Or.inr ?_
        rw [Set.mem_singleton_iff]
        exact Set.pair_comm ((w, u).1) ((w, u).2)
      rw [ffOfHyp_p3, if_pos hmem]
      dsimp only
      rw [hEEu, hivsU]
      have htA : (r + 1) % k' = 0 := by
        rw [Nat.add_mod, h1k, ht, ht1, show k' - 1 + 1 = k' from by omega, Nat.mod_self]
      have htB : (r + 1 + 1) % k' = 1 := by
        rw [show r + 1 + 1 = r + 2 from by omega, Nat.add_mod, h1k2, ht, ht1,
          show k' - 1 + 2 = k' + 1 from by omega, Nat.add_comm, Nat.add_mod_right, h1k]
      simp only [hRdef, htA, htB, Nat.zero_add, hp,
        show (1:ℕ) + p % k = p % k + 1 from Nat.add_comm 1 (p % k)]
  -- 6. the orbit of the base dart is the k'-window
  have hRcong : ∀ a b : ℕ, a % k' = b % k' → R a = R b := by
    intro a b h
    have e1 : (a + 1) % k' = (b + 1) % k' := by
      rw [Nat.add_mod, h1k, h, Nat.add_mod b 1 k', h1k]
    simp only [hRdef, h, e1]
  have hiter : ∀ n : ℕ, (ffOfHyp_p3 0 V (E ∪ {{u, w}}))^[n] (R 0) = R (n % k') := by
    intro n
    induction n with
    | zero => rw [Function.iterate_zero_apply, Nat.zero_mod]
    | succ m ih =>
      have hm : (m + 1) % k' = (m % k' + 1) % k' := by rw [Nat.add_mod, h1k]
      rw [Function.iterate_succ_apply', ih, hstep, hm]
      exact (hRcong ((m % k' + 1) % k') (m % k' + 1) (Nat.mod_mod _ _)).symm
  -- 7. assembly
  have hrho : rhoNode1 FF u = vv (p % k + 1) := by
    have h := VV_SUC_EQ_RHO_NODE_p35 s k (p % k) p q u V E FF vv hk hp hV hE hFF hscs hdiag hBB 1
    rw [Function.iterate_one, show (1:ℕ) + p % k = p % k + 1 from Nat.add_comm 1 (p % k)] at h
    exact h
  rw [Hypermap.face, hrho]
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i % k', ?_⟩
    rw [sfPermPow_p35, hFaceM, ← hR0, hiter, Nat.mod_eq_of_lt (Nat.mod_lt i hk'0)]
    exact (hRcong i (i % k') (Nat.mod_eq_of_lt (Nat.mod_lt i hk'0)).symm).symm
  · rintro ⟨n, hn⟩
    rw [sfPermPow_p35, hFaceM, ← hR0, hiter] at hn
    exact ⟨n % k', hn⟩
  -- DISCHARGES: source 4622-4838 -- REMAINING ROOT of the trio (V/E below
  -- now close from it): the F_PRIME body cascade = WIP drafts/kit_body.lean
  -- (see the note above the statement for the precise remaining state).


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
  exact TRIO_V_OF_FACE_p35 s s' s'' p q d' d'' mkj k k' u w V E FF vv HS hs' hs''
    hk' hk hp hq hV hE hFF hnorm hscs hdiag hBB hHS
    (F_PRIME_EQ_F_vv_p35 s s' s'' p q d' d'' mkj k k' u w V E FF vv HS hs' hs''
      hk' hk hp hq hV hE hFF hnorm hscs hdiag hBB hHS)
  -- DISCHARGES: source 4290-4406 as a set-algebra corollary of the face
  -- description `F_PRIME_EQ_F_vv_p35` (the trio's remaining root above).

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
  exact TRIO_E_OF_FACE_p35 s s' s'' p q d' d'' mkj k k' u w V E FF vv HS hs' hs''
    hk' hk hp hq hV hE hFF hnorm hscs hdiag hBB hHS
    (F_PRIME_EQ_F_vv_p35 s s' s'' p q d' d'' mkj k k' u w V E FF vv HS hs' hs''
      hk' hk hp hq hV hE hFF hnorm hscs hdiag hBB hHS)
  -- DISCHARGES: source 4406-4622 as a set-algebra corollary of the face
  -- description `F_PRIME_EQ_F_vv_p35` (the trio's remaining root above).

/-! ## BBs transport / taustar bank opens (source order: 4838-5312) -/

/-! ## BBs transport head (engine-w1 E2 sub-lemma reuse; internals of
HOL QKNVMLB.hl:4838-5223) -/

/-- HOL `periodic` mod-normalisation: a `k`-periodic function is `mod k`-blind. -/
theorem per_mod_p35 {α : Sort u} {f : ℕ → α} {k : ℕ} (hper : Periodic f k)
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

/-- Two-argument mod-normalisation from `Periodic2`. -/
theorem per2_mod_p35 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
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

/-- A two-element set of naturals with distinct sides: two pairings only. -/
theorem pair_cases_p35 {a b c d : ℕ} (hab : a ≠ b)
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

/-- HOL QKNVMLB1 circuit identity (QKNVMLB.hl:4930 area): walking
`(k'-1) + p%k` lands back on `q%k` where `k' = (q + 1 + (k - t)) % k`
(the `scsHalfSliceV39` index circuit). -/
theorem circuit_p35 (k t q : ℕ) (hk0 : 0 < k) (htk : t ≤ k)
    (hk1 : 1 ≤ (q + 1 + (k - t)) % k) :
    ((q + 1 + (k - t)) % k - 1 + t) % k = q % k := by
  obtain ⟨m, hmv⟩ : ∃ m, (q + 1 + (k - t)) % k = m := ⟨_, rfl⟩
  rw [hmv]
  have hmk : m < k := by rw [← hmv]; exact Nat.mod_lt _ hk0
  have hm1 : 1 ≤ m := by rw [← hmv]; exact hk1
  have hX1 : 1 ≤ q + 1 + (k - t) := by omega
  have hXt : (q + 1 + (k - t)) - 1 + t = q + k := by omega
  have hmeq : m % k = (q + 1 + (k - t)) % k := by
    conv_lhs => rw [← hmv]
    exact Nat.mod_mod_of_dvd _ (Nat.dvd_refl k)
  have hsub := Nat.ModEq.sub_right (by omega) (by omega) hmeq
  have hadd := Nat.ModEq.add_right t hsub
  rw [hXt] at hadd
  rw [hadd, Nat.add_mod, Nat.mod_self, Nat.add_zero,
    Nat.mod_mod_of_dvd _ (Nat.dvd_refl k)]

/-- BBsV39 component 1 through the half-slice re-indexing: ballAnnulus. -/
theorem q1_range_ball_p35 (vv : ℕ → V3) (k' t : ℕ)
    (h : Set.range vv ⊆ ballAnnulus) :
    Set.range (fun i => vv (i % k' + t)) ⊆ ballAnnulus := by
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  exact h ⟨i % k' + t, rfl⟩

/-- BBsV39 component 2 through the half-slice re-indexing: Periodicity. -/
theorem q1_periodic_p35 (vv : ℕ → V3) (k' t : ℕ) :
    Periodic (fun i => vv (i % k' + t)) k' := by
  intro i
  show vv ((i + k') % k' + t) = vv (i % k' + t)
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero,
    Nat.mod_mod_of_dvd _ (Nat.dvd_refl k')]

/-- BBsV39 component 3 (the `a`/`b` window) through the half-slice
re-indexing, including the `{0, k'-1}` diagonal override fed by the
`MMs` bounds at `(p % k, q % k)` (engine-w1 `q1_window_draft` verbatim;
QKNVMLB.hl:4946-5060 segment). -/
theorem q1_window_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop) (vv : ℕ → V3)
    (hper : Periodic vv s.k) (hk0 : 0 < s.k)
    (hper2am : Periodic2 s.am s.k) (hper2bm : Periodic2 s.bm s.k)
    (ham : ∀ i j, s.am i j ≤ dist (vv i) (vv j))
    (hbm : ∀ i j, dist (vv i) (vv j) ≤ s.bm i j)
    -- the a ≤ am ≤ bm ≤ b chain of isScsV39 s (components 14 of the conjunct)
    (haw : ∀ i j, s.a i j ≤ s.am i j) (hbw : ∀ i j, s.bm i j ≤ s.b i j)
    (hk'1 : 2 ≤ (q + 1 + (s.k - p % s.k)) % s.k) :
    ∀ i j, (scsHalfSliceV39 s p q d' mkj).a i j ≤
        dist (vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
             (vv (j % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) ∧
      dist (vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
             (vv (j % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) ≤
        (scsHalfSliceV39 s p q d' mkj).b i j := by
  obtain ⟨k', hk'eq⟩ : ∃ k', (q + 1 + (s.k - p % s.k)) % s.k = k' := ⟨_, rfl⟩
  have hkP : (scsHalfSliceV39 s p q d' mkj).k = k' := by
    simp only [scsHalfSliceV39]
    rw [← hk'eq]
  have hA : ∀ x y, (scsHalfSliceV39 s p q d' mkj).a x y =
      if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.am p q
      else s.a (x % k' + p % s.k) (y % k' + p % s.k) := by
    intro x y
    simp only [scsHalfSliceV39]
    rw [← hk'eq]
  have hB : ∀ x y, (scsHalfSliceV39 s p q d' mkj).b x y =
      if ({x % k', y % k'} : Set ℕ) = {0, k' - 1} then s.bm p q
      else s.b (x % k' + p % s.k) (y % k' + p % s.k) := by
    intro x y
    simp only [scsHalfSliceV39]
    rw [← hk'eq]
  have hksk : p % s.k ≤ s.k := Nat.le_of_lt (Nat.mod_lt p hk0)
  -- MMs bounds at (p % k, q % k), folded to the mod-normal form
  have core : s.am p q ≤ dist (vv (p % s.k)) (vv (q % s.k)) ∧
      dist (vv (p % s.k)) (vv (q % s.k)) ≤ s.bm p q := by
    constructor
    · rw [per2_mod_p35 hper2am]; exact ham _ _
    · rw [per2_mod_p35 hper2bm]; exact hbm _ _
  have hcircuit : (k' - 1 + p % s.k) % s.k = q % s.k := by
    rw [← hk'eq]
    exact circuit_p35 s.k (p % s.k) q hk0 hksk (by omega)
  intro i j
  by_cases hov : ({i % k', j % k'} : Set ℕ) = {0, k' - 1}
  · rw [hA i j, hB i j, if_pos hov, if_pos hov]
    have hne : i % k' ≠ j % k' := by
      intro he
      rw [he] at hov
      have hsing : ({j % k', j % k'} : Set ℕ) = {j % k'} := by simp
      rw [hsing] at hov
      have m1 : (0 : ℕ) ∈ ({j % k'} : Set ℕ) := by rw [hov]; simp
      have m2 : (k' - 1 : ℕ) ∈ ({j % k'} : Set ℕ) := by rw [hov]; simp
      simp only [Set.mem_singleton_iff] at m1 m2
      omega
    rcases pair_cases_p35 hne hov with ⟨hi0, hjk⟩ | ⟨hik, hj0⟩
    · rw [hkP, hi0, hjk, zero_add,
        per_mod_p35 hper (k' - 1 + p % s.k), hcircuit]
      exact core
    · rw [hkP, hik, hj0, zero_add,
        per_mod_p35 hper (k' - 1 + p % s.k), hcircuit, dist_comm]
      exact core
  · rw [hA i j, hB i j, if_neg hov, if_neg hov, hkP]
    exact ⟨(haw _ _).trans (ham _ _), (hbm _ _).trans (hbw _ _)⟩

/-- The first three `BBsV39` components of the half-slice realisation
(range/periodicity/window), bundled once for the LE4F/EQ4F twins
(HOL QKNVMLB.hl:4873-4946 segment). -/
theorem q1_head_p35 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop) (vv : ℕ → V3)
    (hBB : BBsV39 s vv) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hMM : vv ∈ MMsV39 s) :
    Set.range (fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) ⊆ ballAnnulus ∧
    Periodic (fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
      (scsHalfSliceV39 s p q d' mkj).k ∧
    (∀ i j, (scsHalfSliceV39 s p q d' mkj).a i j ≤
        dist (vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
             (vv (j % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) ∧
      dist (vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
             (vv (j % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) ≤
        (scsHalfSliceV39 s p q d' mkj).b i j) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hP2am : Periodic2 s.am s.k := hscs.2.2.2.2.2.2.2.2.1
  have hP2bm : Periodic2 s.bm s.k := hscs.2.2.2.2.2.2.2.2.2.1
  have hab := hscs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨q1_range_ball_p35 vv _ (p % s.k) hBB.1, q1_periodic_p35 vv _ (p % s.k),
    q1_window_p35 s p q d' mkj vv hBB.2.1 hk0 hP2am hP2bm hMM.2.2.2.2.1
      hMM.2.2.2.2.2 (fun i j => (hab i j).1) (fun i j => (hab i j).2.2)
      (by have h := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag _ rfl
          simp only [scsHalfSliceV39] at h
          omega)⟩

/-- HOL SUBGOAL of the LE4F segment: `norm (u - w) <= cstab`, from the
`bm p q <= cstab` hypothesis through the MMs bound and `periodic2`
(QKNVMLB.hl LE4F second script block). -/
theorem q1_norm_diag_p35 (s : ScsV39) (p q : ℕ) (vv : ℕ → V3)
    (hP2bm : Periodic2 s.bm s.k) (hMM : vv ∈ MMsV39 s) (hc : s.bm p q ≤ cstab) :
    norm (vv (p % s.k) - vv (q % s.k)) ≤ cstab := by
  have h1 : dist (vv (p % s.k)) (vv (q % s.k)) ≤ s.bm (p % s.k) (q % s.k) :=
    hMM.2.2.2.2.2 _ _
  rw [per2_mod_p35 hP2bm p q] at hc
  rw [← dist_eq_norm]
  exact h1.trans hc

/-- HOL `EJRCFJD` (Local_lemmas1.hl:5967): the diag-slicing
convex-local-fan lemma, rendered in the `IsHypE_p35` carrier form (the HOL
`HS = hypermap (HYP (vec 0,V,E UNION {{v,w}}))` equation becomes the
existential `HS`; cf. the encoding notes at the `V/E/F_PRIME` trio).
NEEDS: `THE_SLICING_INTO_2_LEMMA` + `PROVE_THE_SLICE_ASSUMPTION`
(Local_lemmas1 -- LocalAuto2-importing world, unreachable from LA35
imports) -- bridge wave, same home as `F_PRIME_EQ_F_vv_p35` (estimate and
plan: lkgrqui-qknv2-w2 DELIVERY §3.3).  `EJRCFJD_p8` (LocalAuto8) is the
NKEZBFC.hl:1685 `slicev/slicee/slicef` rendering of the same HOL family;
this `_p35` form is the Local_lemmas1.hl:5967 one consumed by
`QKNVMLB1_LE4F/EQ4F` (the `!x. x IN FF ==> aff_gt {vec 0} {v, w} SUBSET
wedge_in_fan_gt x E` hypothesis is `TECOXBMv2_p35`'s conclusion). -/
theorem EJRCFJD_p35 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (v w : V3)
    (hfan : ConvexLocalFan V E FF) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E) :
    ∃ HS : Hypermap (V3 × V3), IsHypE_p35 V (E ∪ {{v, w}}) HS ∧
      ConvexLocalFan (vPrime_p3 V (HS.face (v, rhoNode1 FF v)))
        (ePrime_p3 (E ∪ {{v, w}}) (HS.face (v, rhoNode1 FF v)))
        (HS.face (v, rhoNode1 FF v)) ∧
      ConvexLocalFan (vPrime_p3 V (HS.face (w, rhoNode1 FF w)))
        (ePrime_p3 (E ∪ {{w, v}}) (HS.face (w, rhoNode1 FF w)))
        (HS.face (w, rhoNode1 FF w)) := by
  sorry
  -- DISCHARGES: local_lemmas1.hl:5967 (bridge wave; THE_SLICING_INTO_2_LEMMA
  -- + PROVE_THE_SLICE_ASSUMPTION unreachable from the LA35 import face).

/-- HOL `QKNVMLB1_LE4F` (QKNVMLB.hl:4838, proof ~225 ln). -/
theorem QKNVMLB1_LE4F_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv vv' : ℕ → V3)
    (hs' : s' = scsHalfSliceV39 s p q d' mkj)
    (hs'' : s'' = scsHalfSliceV39 s q p d'' mkj)
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hd' : d' < 0.9)
    (h4 : 4 < s.k ∧ s.bm p q ≤ cstab) (hMM : vv ∈ MMsV39 s) :
    BBsV39 s' vv' := by
  subst hs'
  subst hvv'
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hBB : BBsV39 s vv := hMM.1.1.1
  -- HOL script blocks 2-4: range / periodicity / a-b window through the
  -- half-slice re-indexing (QKNVMLB.hl:4873-5060, engine-w1 sub-lemmas).
  obtain ⟨h1, h2, h3⟩ := q1_head_p35 s p q d' mkj vv hBB hscs hdiag hMM
  refine ⟨h1, h2, h3, ?_⟩
  -- component 4 (HOL: cases on `3 <= k' ==> k' <= 3 \/ ~(k' <= 3)`).
  have hP2bm : Periodic2 s.bm s.k := hscs.2.2.2.2.2.2.2.2.2.1
  rcases Nat.lt_or_ge (scsHalfSliceV39 s p q d' mkj).k 4 with hk'3 | hk'4
  · -- k' <= 3: the fan disjunct is trivial.
    exact Or.inl (by omega)
  · -- 4 <= k': the half slice is a genuine diag slice of the s-fan
    -- (HOL final script block, QKNVMLB.hl:5040-5064).
    refine Or.inr ?_
    have hfan0 : ConvexLocalFan (Set.range vv)
        (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) := by
      rcases hBB.2.2.2 with hle | hfan
      · omega
      · exact hfan
    -- HOL SUBGOAL norm (u - w) <= cstab from the bm p q <= cstab hypothesis.
    have hnorm : norm (vv (p % s.k) - vv (q % s.k)) ≤ cstab :=
      q1_norm_diag_p35 s p q vv hP2bm hMM h4.2
    have huw : vv (p % s.k) ≠ vv (q % s.k) :=
      NOT_EQ_DIAG_p35 s p q _ _ vv hscs hdiag hnorm rfl rfl hBB
    -- TECOXBMv2: the diag wedge contains every fan face wedge.
    have hwedge := TECOXBMv2_p35 s p q (vv (p % s.k)) (vv (q % s.k))
      (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) vv hscs hdiag hnorm rfl rfl rfl rfl rfl hBB
    -- EJRCFJD: the diag slice of the s-fan is again a convex local fan.
    obtain ⟨HS, hHS, hfanU, -⟩ :=
      EJRCFJD_p35 (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) (vv (p % s.k)) (vv (q % s.k))
        hfan0 (IN_IMAGE_VV_p35 vv (p % s.k)) (IN_IMAGE_VV_p35 vv (q % s.k)) huw hwedge
    -- the V/E/F_PRIME re-labelling trio identifies the re-indexed sets with
    -- the slice face's vertex/edge/dart sets.
    have hVp := V_PRIME_EQ_V_vv_p35 s (scsHalfSliceV39 s p q d' mkj) s'' p q d' d'' mkj
      s.k (scsHalfSliceV39 s p q d' mkj).k (vv (p % s.k)) (vv (q % s.k))
      (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) vv HS rfl hs''.symm rfl rfl rfl rfl rfl rfl rfl
      hnorm hscs hdiag hBB hHS
    have hEp := E_PRIME_EQ_E_vv_p35 s (scsHalfSliceV39 s p q d' mkj) s'' p q d' d'' mkj
      s.k (scsHalfSliceV39 s p q d' mkj).k (vv (p % s.k)) (vv (q % s.k))
      (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) vv HS rfl hs''.symm rfl rfl rfl rfl rfl rfl rfl
      hnorm hscs hdiag hBB hHS
    have hFp := F_PRIME_EQ_F_vv_p35 s (scsHalfSliceV39 s p q d' mkj) s'' p q d' d'' mkj
      s.k (scsHalfSliceV39 s p q d' mkj).k (vv (p % s.k)) (vv (q % s.k))
      (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) vv HS rfl hs''.symm rfl rfl rfl rfl rfl rfl rfl
      hnorm hscs hdiag hBB hHS
    rw [hVp, hEp, hFp]
    exact hfanU

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
  subst hs'
  subst hvv'
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hBB : BBsV39 s vv := hMM.1.1.1
  -- HOL script blocks 2-4: range / periodicity / a-b window through the
  -- half-slice re-indexing (QKNVMLB.hl:5085-5185; same sub-lemmas as LE4F).
  obtain ⟨h1, h2, h3⟩ := q1_head_p35 s p q d' mkj vv hBB hscs hdiag hMM
  refine ⟨h1, h2, h3, ?_⟩
  -- component 4: k = 4 forces s'.k = 3 (SCS_K_PRIME_CASE_4), so the fan
  -- disjunct is trivial (HOL final script block, QKNVMLB.hl:5186-5223).
  have hk3 : (scsHalfSliceV39 s p q d' mkj).k = 3 :=
    SCS_K_PRIME_CASE_4_p35 s _ p q d' mkj rfl hscs h4.1.symm hdiag
  exact Or.inl (by omega)

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
  -- engine-w1 E2 assembly (verified real-form body): k = 4 -> EQ4F;
  -- else bm <= cstab with 4 < k -> LE4F (the k = 4 + bm <= cstab corner
  -- also goes to EQ4F via cstab < 4).
  have h3k : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hc4 : cstab ≤ 4 := by norm_num [cstab]
  rcases h4 with hk4 | hcstab
  · exact QKNVMLB1_EQ4F_p35 (s'' := scsHalfSliceV39 s q p d' mkj) s s' p q d' mkj vv vv'
      hs' rfl hvv' hscs hdiag hd' ⟨hk4.symm, le_of_lt hbm⟩ hMM
  · rcases Nat.eq_or_lt_of_le (by omega : 4 ≤ s.k) with he4 | hk4
    · exact QKNVMLB1_EQ4F_p35 (s'' := scsHalfSliceV39 s q p d' mkj) s s' p q d' mkj vv vv'
        hs' rfl hvv' hscs hdiag hd' ⟨he4, by linarith⟩ hMM
    · exact QKNVMLB1_LE4F_p35 (s'' := scsHalfSliceV39 s q p d' mkj) s s' p q d' mkj vv vv'
        hs' rfl hvv' hscs hdiag hd' ⟨hk4, hcstab⟩ hMM

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

/-! ## QKNVMLB2 step kit (source 5522-7735; the mkj = false branch)

Steps for the dsv superadditivity along the slice: 01 not-ear + negative-sign
dsv form; 02 the corner split of the J-sum; 03 nonnegativity of the J-sum
term; 04 the half-slice corner J-edge is the mkj flag; 05 re-indexing of the
half-slice interior J-sum to the s-frame (SUM_EQ_GENERAL); 06 the mkj =
false branch of QKNVMLB2 assembled from 01-05) and 07 the mkj = true branch
(HOL 6135-7735: ear / non-ear half dsv forms with the live diagonal corner
terms, the both-ears subcase via the DIST_DIAG argument under the live flag);
`QKNVMLB2_p35` below assembles both branches through the flag-mkj bridge
`q2flagEq`, all inside the standard three. -/


open scoped BigOperators

private theorem q2setSumCongr {α : Type*} {A : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ A, f a = g a) : setSum A f = setSum A g := by
  unfold setSum
  split
  · exact Finset.sum_congr rfl fun a ha => h a ((Set.Finite.mem_toFinset _) |>.mp ha)
  · rfl

private theorem q2setSumNonneg {α : Type*} {A : Set α} {f : α → ℝ}
    (hfin : A.Finite) (h : ∀ a ∈ A, 0 ≤ f a) : 0 ≤ setSum A f := by
  unfold setSum
  rw [dif_pos hfin]
  exact Finset.sum_nonneg fun a ha => h a ((Set.Finite.mem_toFinset hfin) |>.mp ha)

private theorem q2setSumUnion {α : Type*} {A B : Set α} {f : α → ℝ}
    (hA : A.Finite) (hB : B.Finite) (hd : A ∩ B = ∅) :
    setSum (A ∪ B) f = setSum A f + setSum B f := by
  have hu : (A ∪ B).Finite := hA.union hB
  unfold setSum at *
  rw [dif_pos hu, dif_pos hA, dif_pos hB, Set.Finite.toFinset_union hA hB hu]
  refine Finset.sum_union (Finset.disjoint_left.mpr fun a ha hb => ?_)
  have hmem : a ∈ (A ∩ B : Set α) :=
    ⟨(Set.Finite.mem_toFinset hA) |>.mp ha, (Set.Finite.mem_toFinset hB) |>.mp hb⟩
  rw [hd] at hmem
  exact hmem

private theorem q2setSumGeUnion2 {A B C : Set ℕ} {f : ℕ → ℝ}
    (hA : A.Finite) (hB : B.Finite) (hC : C.Finite)
    (hsub : B ∪ C ⊆ A) (hdisj : B ∩ C = ∅)
    (hf : ∀ a ∈ A, 0 ≤ f a) :
    setSum B f + setSum C f ≤ setSum A f := by
  have hdis : Disjoint hB.toFinset hC.toFinset :=
    Finset.disjoint_left.mpr fun a ha hb => by
      have hb' : a ∈ (C : Set ℕ) := (Set.Finite.mem_toFinset hC) |>.mp hb
      have hmem : a ∈ (B ∩ C : Set ℕ) :=
        ⟨(Set.Finite.mem_toFinset hB) |>.mp ha, hb'⟩
      rw [hdisj] at hmem
      exact hmem
  have key : ∑ w ∈ hB.toFinset ∪ hC.toFinset, f w ≤ ∑ w ∈ hA.toFinset, f w := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro a ha
      rw [Finset.mem_union] at ha
      rcases ha with ha | ha
      · exact (Set.Finite.mem_toFinset hA) |>.mpr
          (hsub (Or.inl ((Set.Finite.mem_toFinset hB) |>.mp ha)))
      · exact (Set.Finite.mem_toFinset hA) |>.mpr
          (hsub (Or.inr ((Set.Finite.mem_toFinset hC) |>.mp ha)))
    · exact fun a ha _ => hf a ((Set.Finite.mem_toFinset hA) |>.mp ha)
  unfold setSum at *
  rw [dif_pos hB, dif_pos hC, dif_pos hA]
  calc (∑ w ∈ hB.toFinset, f w) + ∑ w ∈ hC.toFinset, f w
      = ∑ w ∈ hB.toFinset ∪ hC.toFinset, f w := (Finset.sum_union hdis).symm
    _ ≤ ∑ w ∈ hA.toFinset, f w := key

private theorem q2setSumSingleton {α : Type*} [DecidableEq α] {a : α} {f : α → ℝ} :
    setSum {a} f = f a := by
  have hfin : ({a} : Set α).Finite := Set.finite_singleton a
  show (if h : ({a} : Set α).Finite then ∑ w ∈ h.toFinset, f w else 0) = f a
  rw [dif_pos hfin, Set.Finite.toFinset_singleton hfin]
  exact Finset.sum_singleton (f := f) (a := a)

/-! ## q2a (step01): the negative-sign dsv form of `s` -/

/-- `s` is not an ear: `DIAG_IS_NOT_EAR_p35` at the QKNVMLB2 context. -/
theorem QKNVMLB2_step01_notEar_p35 (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) : ¬ isEarV39 s :=
  DIAG_IS_NOT_EAR_p35 s p q hscs hdiag

/-- HOL `dsv_v39` with the ear branch resolved to the `-1` sign. -/
theorem QKNVMLB2_step01_dsv_p35 (s : ScsV39) (p q : ℕ) (vv : ℕ → V3)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) :
    dsvV39 s vv = s.d - 0.1 *
      setSum {i | i < s.k ∧ s.J i (i + 1)} (fun i => cstab - dist (vv i) (vv (i + 1))) := by
  have hne := QKNVMLB2_step01_notEar_p35 s p q hscs hdiag
  unfold dsvV39
  rw [if_neg hne]
  ring

/-! ## q2b (step02): the corner split of the J-sum -/

/-- The J-index set of a system `t` splits into the interior indices
`i < t.k - 1` plus the corner `t.k - 1` (whose J-edge is `(t.k-1, t.k)`). -/
theorem QKNVMLB2_step02_cornerSplit_p35 (t : ScsV39) (f : ℕ → ℝ) (ht : 0 < t.k) :
    setSum {i | i < t.k ∧ t.J i (i + 1)} f =
      setSum {i | i < t.k - 1 ∧ t.J i (i + 1)} f +
        (if t.J (t.k - 1) (t.k - 1 + 1) then f (t.k - 1) else 0) := by
  by_cases hJ : t.J (t.k - 1) (t.k - 1 + 1)
  · have hset : {i | i < t.k ∧ t.J i (i + 1)}
        = {i | i < t.k - 1 ∧ t.J i (i + 1)} ∪ {t.k - 1} := by
      ext i
      by_cases hik : i = t.k - 1
      · subst hik
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, hJi⟩
          exact Or.inr trivial
        · rintro (⟨hlt, hJi⟩ | hin)
          · exact (Nat.lt_irrefl (t.k - 1) hlt).elim
          · exact ⟨by omega, hJ⟩
      · simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hlt, hJi⟩
          exact Or.inl ⟨by omega, hJi⟩
        · rintro (⟨hlt, hJi⟩ | hin)
          · exact ⟨by omega, hJi⟩
          · omega
    have hfin1 : ({i | i < t.k - 1 ∧ t.J i (i + 1)} : Set ℕ).Finite :=
      (Set.finite_lt_nat t.k).subset fun i hi => by
        simp only [Set.mem_setOf_eq] at hi ⊢
        omega
    have hfin2 : ({t.k - 1} : Set ℕ).Finite := Set.finite_singleton _
    have hd : ({i | i < t.k - 1 ∧ t.J i (i + 1)} : Set ℕ) ∩ {t.k - 1} = ∅ := by
      ext i
      constructor
      · rintro ⟨⟨hlt, hJi⟩, hi⟩
        simp only [Set.mem_singleton_iff] at hi
        subst hi
        omega
      · rintro hmem
        exact absurd hmem (by simp)
    rw [hset, q2setSumUnion hfin1 hfin2 hd, q2setSumSingleton, if_pos hJ]
  · have hset : {i | i < t.k ∧ t.J i (i + 1)}
        = {i | i < t.k - 1 ∧ t.J i (i + 1)} := by
      ext i
      by_cases hik : i = t.k - 1
      · subst hik
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨-, hJi⟩
          exact absurd hJi hJ
        · rintro ⟨hlt, hJi⟩
          omega
      · simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hlt, hJi⟩
          exact ⟨by omega, hJi⟩
        · rintro ⟨hlt, hJi⟩
          exact ⟨by omega, hJi⟩
    rw [hset, if_neg hJ, add_zero]

/-! ## q2c (step03): nonnegativity of the J-sum term -/

/-- `cstab - dist (vv i) (vv (i+1)) ≥ 0`: MMs gives `dist ≤ bm`, `is_scs`
chains `bm ≤ b` and, for `3 < k`, `b i (i+1) ≤ cstab`. -/
theorem QKNVMLB2_step03_p35 (s : ScsV39) (p q : ℕ) (vv : ℕ → V3) (hMM : vv ∈ MMsV39 s)
    (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (i : ℕ) :
    0 ≤ cstab - dist (vv i) (vv (i + 1)) := by
  have hk3 : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  simp only [MMsV39, Set.mem_setOf_eq] at hMM
  obtain ⟨-, -, -, -, -, hbmle⟩ := hMM
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hch, -, -, -, hbc, -, -, -⟩ := hscs
  have h1 : dist (vv i) (vv (i + 1)) ≤ s.bm i (i + 1) := hbmle i (i + 1)
  have h2 : s.bm i (i + 1) ≤ s.b i (i + 1) := (hch i (i + 1)).2.2
  have h3 : s.b i (i + 1) ≤ cstab := hbc i hk3
  linarith

/-! ## q2d (step04): the corner J-edge of a half slice is the mkj flag -/

/-- On the override pair `(k'-1, k')` the half slice carries exactly the
`mkj` flag (and the override bound `s.bm p q`). -/
theorem QKNVMLB2_step04_corner_p35 (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s') (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) :
    s'.J (s'.k - 1) (s'.k - 1 + 1) = mkj ∧
      s'.b (s'.k - 1) (s'.k - 1 + 1) = s.bm p q := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hK : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']
    simp only [scsHalfSliceV39]
  have hk3 : 3 ≤ (q + 1 + (s.k - p % s.k)) % s.k := by omega
  have hk'1 : 1 ≤ (q + 1 + (s.k - p % s.k)) % s.k := by omega
  -- the override-pair test at (k'-1, k')
  have hmod1 : ((q + 1 + (s.k - p % s.k)) % s.k - 1) % ((q + 1 + (s.k - p % s.k)) % s.k)
      = (q + 1 + (s.k - p % s.k)) % s.k - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hmod2 : ((q + 1 + (s.k - p % s.k)) % s.k - 1 + 1) % ((q + 1 + (s.k - p % s.k)) % s.k)
      = 0 := by
    have heq : (q + 1 + (s.k - p % s.k)) % s.k - 1 + 1
        = (q + 1 + (s.k - p % s.k)) % s.k := by omega
    rw [heq]
    simp
  have hcond : ({((q + 1 + (s.k - p % s.k)) % s.k - 1)
        % ((q + 1 + (s.k - p % s.k)) % s.k),
      ((q + 1 + (s.k - p % s.k)) % s.k - 1 + 1) % ((q + 1 + (s.k - p % s.k)) % s.k)} : Set ℕ)
      = {0, (q + 1 + (s.k - p % s.k)) % s.k - 1} := by
    rw [hmod1, hmod2]
    ext yy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h
  constructor
  · rw [← hs']
    simp only [scsHalfSliceV39]
    exact if_pos hcond
  · rw [← hs']
    simp only [scsHalfSliceV39]
    exact if_pos hcond

/-- The T-window translated from the half-slice interior J-set (the set
whose `setSum` is the `s`-frame form of the half's interior J-sum). -/
private def q2T1set (s : ScsV39) (p : ℕ) (s' : ScsV39) : Set ℕ :=
  {j | ∃ i, i < s'.k - 1 ∧ s'.J i (i + 1) ∧ j = (i + p % s.k) % s.k}

/-- step05 (HOL 5725-5830, SUM_EQ_GENERAL): the half-slice interior J-sum
equals the `s`-frame sum over the translated window `q2T1set`. -/
theorem QKNVMLB2_step05_reindex_p35 (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3) (hs' : scsHalfSliceV39 s p q d' mkj = s') (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) (hMM : vv ∈ MMsV39 s) :
    setSum {i | i < s'.k - 1 ∧ s'.J i (i + 1)}
        (fun i => cstab - dist (vv (i % s'.k + p % s.k))
            (vv ((i + 1) % s'.k + p % s.k))) =
      setSum (q2T1set s p s') (fun j => cstab - dist (vv j) (vv (j + 1))) := by
  -- periodicity of vv from the MMs → BBs membership
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hper : Periodic vv s.k := hBB.2.1
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk3 : 3 ≤ s'.k := hge.1
  have hkl : s'.k < s.k := hge.2.2
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  -- A = the interior J-index set, g = the translation
  set A : Set ℕ := {i | i < s'.k - 1 ∧ s'.J i (i + 1)} with hAdef
  set g : ℕ → ℕ := fun i => (i + p % s.k) % s.k with hgdef
  -- the translated window is the image g '' A
  have himg : q2T1set s p s' = g '' A := by
    ext j
    simp only [q2T1set, Set.mem_image, hAdef, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hJi, hj⟩
      exact ⟨i, ⟨hi, hJi⟩, hj.symm⟩
    · rintro ⟨i, ⟨hi, hJi⟩, hj⟩
      exact ⟨i, hi, hJi, hj.symm⟩
  -- g is injective on A (as s'.k ≤ s.k)
  have hinj : ∀ x ∈ A, ∀ y ∈ A, g x = g y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hxl, -⟩ := hx
    obtain ⟨hyl, -⟩ := hy
    have hxy2 : (x + p % s.k) % s.k = (y + p % s.k) % s.k := hxy
    have hmod : x ≡ y [MOD s.k] := Nat.ModEq.add_right_cancel' (p % s.k) hxy2
    have h3 : x % s.k = y % s.k := hmod
    have h1 : x % s.k = x := Nat.mod_eq_of_lt (by omega)
    have h2 : y % s.k = y := Nat.mod_eq_of_lt (by omega)
    omega
  -- finiteness
  have hAfin : A.Finite := (Set.finite_lt_nat (s'.k - 1)).subset fun i hi => hi.1
  have hBfin : (g '' A).Finite := hAfin.image g
  -- summand congruence on A (interior indices are mod-free)
  have hcongr : ∀ i ∈ A,
      cstab - dist (vv (i % s'.k + p % s.k)) (vv ((i + 1) % s'.k + p % s.k))
        = cstab - dist (vv (g i)) (vv (g i + 1)) := by
    rintro i ⟨hi, -⟩
    have him : i % s'.k = i := Nat.mod_eq_of_lt (by omega)
    have him2 : (i + 1) % s'.k = i + 1 := Nat.mod_eq_of_lt (by omega)
    -- periodicity translates the g-form back
    have hp1 : vv (g i) = vv (i + p % s.k) := by
      show vv ((i + p % s.k) % s.k) = vv (i + p % s.k)
      exact periodic_mod_eq_p23 hper (i + p % s.k)
    have hp2 : vv (g i + 1) = vv (i + 1 + p % s.k) := by
      show vv ((i + p % s.k) % s.k + 1) = vv (i + 1 + p % s.k)
      rw [← periodic_mod_eq_p23 hper ((i + p % s.k) % s.k + 1), Nat.mod_add_mod,
        show i + p % s.k + 1 = i + 1 + p % s.k by omega,
        periodic_mod_eq_p23 hper (i + 1 + p % s.k)]
    rw [him, him2, hp1, hp2]
  -- the sum re-indexing (Finset.sum_image) after pointwise congruence
  rw [himg, q2setSumCongr hcongr]
  have hinj2 : Set.InjOn g (hAfin.toFinset : Set ℕ) := by
    intro x hx y hy hxy
    exact hinj x ((Set.Finite.mem_toFinset hAfin) |>.mp hx) y
      ((Set.Finite.mem_toFinset hAfin) |>.mp hy) hxy
  unfold setSum
  rw [dif_pos hBfin, dif_pos hAfin,
    Set.Finite.toFinset_image g hAfin hBfin,
    Finset.sum_image (f := fun j => cstab - dist (vv j) (vv (j + 1))) hinj2]


/-! ## q2f (step06): the mkj = false branch of QKNVMLB2 (HOL 5600-6135)

dsv superadditivity along the slice when the override flag is off: the
J-sum of `s` dominates the two translated interior windows (SCS_J_PRIME_
SUBSET_SCS_J + INTER_SLICE_SCS_EMPTY + SUM_DIFF/SUM_POS_LE in HOL), each
each half's dsv is at least `d - 0.1 * S`, and `s.d <= d' + d''` finishes
the arithmetic.  Consumes only CLEAN kit + the lane's step01-05. -/

theorem QKNVMLB2_step06_mkjFalse_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' vv'' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'')
    (hmkj : ¬mkj) :
    dsvV39 s vv ≤ dsvV39 s' vv' + dsvV39 s'' vv'' := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have h3k : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hge' := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hdiag2 : scsDiag s.k q p :=
    ⟨fun e => hdiag.1 e.symm, fun e => hdiag.2.2 e.symm, fun e => hdiag.2.1 e.symm⟩
  have hge'' := SCS_K_PRIME_LE_GE_p35 s q p d'' mkj hscs hdiag2 s'' hs''.symm
  have hk'l : s'.k < s.k := hge'.2.2
  have hk''l : s''.k < s.k := hge''.2.2
  -- the two translated interior windows
  set T1 : Set ℕ :=
    {j | ∃ i, i < s'.k - 1 ∧ s'.J i (i + 1) ∧ j = (i + p % s.k) % s.k} with hT1def
  set T2 : Set ℕ :=
    {j | ∃ i, i < s''.k - 1 ∧ s''.J i (i + 1) ∧ j = (i + q % s.k) % s.k} with hT2def
  -- (a) both windows sit inside the J-index set of s
  have hT1J : T1 ⊆ {j | j < s.k ∧ s.J j (j + 1)} := by
    rintro j ⟨i, hi, hJi, hj⟩
    rw [hj]
    refine ⟨Nat.mod_lt _ hk0, ?_⟩
    exact SCS_J_PRIME_SUBSET_SCS_J_p35 s s' p q d' mkj hs' hscs hdiag i hi hJi
  have hT2J : T2 ⊆ {j | j < s.k ∧ s.J j (j + 1)} := by
    rintro j ⟨i, hi, hJi, hj⟩
    rw [hj]
    refine ⟨Nat.mod_lt _ hk0, ?_⟩
    exact SCS_J_PRIME_SUBSET_SCS_J_p35 s s'' q p d'' mkj hs'' hscs hdiag2 i hi hJi
  -- (c) the windows are disjoint (INTER_SLICE_SCS_EMPTY)
  have hdisj : T1 ∩ T2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro j hj
    rw [Set.mem_inter_iff] at hj
    obtain ⟨⟨i1, hi1, hJ1, hj1⟩, ⟨i2, hi2, hJ2, hj2⟩⟩ := hj
    have hW := INTER_SLICE_SCS_EMPTY_p35 s s' s'' p q d' d'' mkj hs' hs'' hscs hdiag
    have hmem : j ∈ ({y | ∃ i, i < s'.k - 1 ∧ y = (i + p % s.k) % s.k} ∩
        {y | ∃ i, i < s''.k - 1 ∧ y = (i + q % s.k) % s.k} : Set ℕ) :=
      ⟨⟨i1, hi1, hj1⟩, ⟨i2, hi2, hj2⟩⟩
    rw [hW] at hmem
    exact hmem
  -- finiteness
  have hJsfin : ({j | j < s.k ∧ s.J j (j + 1)} : Set ℕ).Finite :=
    (Set.finite_lt_nat s.k).subset fun j hj => hj.1
  have hA0fin : ({i | i < s'.k - 1} : Set ℕ).Finite := Set.finite_lt_nat _
  have hA0fin2 : ({i | i < s''.k - 1} : Set ℕ).Finite := Set.finite_lt_nat _
  have hT1fin : T1.Finite := by
    refine (hA0fin.image (fun i => (i + p % s.k) % s.k)).subset ?_
    rintro j ⟨i, hi, hJi, hj⟩
    exact ⟨i, hi, hj.symm⟩
  have hT2fin : T2.Finite := by
    refine (hA0fin2.image (fun i => (i + q % s.k) % s.k)).subset ?_
    rintro j ⟨i, hi, hJi, hj⟩
    exact ⟨i, hi, hj.symm⟩
  -- (e) the window sums are bounded by the J-sum of s and nonnegative
  have hnonneg : setSum T1 (fun j => cstab - dist (vv j) (vv (j + 1)))
      + setSum T2 (fun j => cstab - dist (vv j) (vv (j + 1)))
      ≤ setSum {j | j < s.k ∧ s.J j (j + 1)}
          (fun j => cstab - dist (vv j) (vv (j + 1))) :=
    q2setSumGeUnion2 hJsfin hT1fin hT2fin (Set.union_subset hT1J hT2J) hdisj
      (fun j _ => QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j)
  have hS1pos : 0 ≤ setSum T1 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    refine q2setSumNonneg hT1fin ?_
    rintro j _
    exact QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j
  have hS2pos : 0 ≤ setSum T2 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    refine q2setSumNonneg hT2fin ?_
    rintro j _
    exact QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j
  -- the s-side dsv form (step01)
  have hstep1 := QKNVMLB2_step01_dsv_p35 s p q vv hscs hdiag
  -- the half-slice dsv forms: corner split (step02) + corner flag (step04)
  have hk'0 : 0 < s'.k := by omega
  have hk''0 : 0 < s''.k := by omega
  have hsplit' : setSum {i | i < s'.k ∧ s'.J i (i + 1)}
      (fun i => cstab - dist (vv (i % s'.k + p % s.k))
          (vv ((i + 1) % s'.k + p % s.k)))
      = setSum T1 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    rw [QKNVMLB2_step02_cornerSplit_p35 s'
      (fun i => cstab - dist (vv (i % s'.k + p % s.k))
          (vv ((i + 1) % s'.k + p % s.k))) hk'0,
      (QKNVMLB2_step04_corner_p35 s s' p q d' mkj hs' hscs hdiag).1,
      if_neg hmkj, add_zero]
    exact QKNVMLB2_step05_reindex_p35 s s' p q d' mkj vv hs' hscs hdiag hMM
  have hsplit'' : setSum {i | i < s''.k ∧ s''.J i (i + 1)}
      (fun i => cstab - dist (vv (i % s''.k + q % s.k))
          (vv ((i + 1) % s''.k + q % s.k)))
      = setSum T2 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    rw [QKNVMLB2_step02_cornerSplit_p35 s''
      (fun i => cstab - dist (vv (i % s''.k + q % s.k))
          (vv ((i + 1) % s''.k + q % s.k))) hk''0,
      (QKNVMLB2_step04_corner_p35 s s'' q p d'' mkj hs'' hscs hdiag2).1,
      if_neg hmkj, add_zero]
    exact QKNVMLB2_step05_reindex_p35 s s'' q p d'' mkj vv hs'' hscs hdiag2 hMM
  have hdsv' : dsvV39 s' vv'
      = s'.d + 0.1 * (if isEarV39 s' then (1:ℝ) else -1) *
        setSum {i | i < s'.k ∧ s'.J i (i + 1)}
          (fun i => cstab - dist (vv (i % s'.k + p % s.k))
              (vv ((i + 1) % s'.k + p % s.k))) := by
    unfold dsvV39
    rw [hvv']
  have hdsv'' : dsvV39 s'' vv''
      = s''.d + 0.1 * (if isEarV39 s'' then (1:ℝ) else -1) *
        setSum {i | i < s''.k ∧ s''.J i (i + 1)}
          (fun i => cstab - dist (vv (i % s''.k + q % s.k))
              (vv ((i + 1) % s''.k + q % s.k))) := by
    unfold dsvV39
    rw [hvv'']
  rw [hsplit'] at hdsv'
  rw [hsplit''] at hdsv''
  -- the ear-sign corner terms dominate the negative-sign forms
  have hb1 : -(0.1 * setSum T1 (fun j => cstab - dist (vv j) (vv (j + 1))))
      ≤ 0.1 * (if isEarV39 s' then (1:ℝ) else -1) *
        setSum T1 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    by_cases he : isEarV39 s'
    · rw [if_pos he]; linarith
    · rw [if_neg he]; linarith
  have hb2 : -(0.1 * setSum T2 (fun j => cstab - dist (vv j) (vv (j + 1))))
      ≤ 0.1 * (if isEarV39 s'' then (1:ℝ) else -1) *
        setSum T2 (fun j => cstab - dist (vv j) (vv (j + 1))) := by
    by_cases he : isEarV39 s''
    · rw [if_pos he]; linarith
    · rw [if_neg he]; linarith
  have hd'eq : s'.d = d' := by rw [← hs']; simp [scsHalfSliceV39]
  have hd''eq : s''.d = d'' := by rw [← hs'']; simp [scsHalfSliceV39]
  linarith

/-! ## q2g support: corner arithmetic, ear / non-ear half dsv forms, DIST_DIAG -/

/-- new plumbing: single-window domination (subset + nonnegativity). -/
private theorem q2setSumSub {A B : Set ℕ} {f : ℕ → ℝ} (hA : A.Finite) (hB : B.Finite)
    (hsub : B ⊆ A) (hf : ∀ a ∈ A, 0 ≤ f a) : setSum B f ≤ setSum A f := by
  unfold setSum
  rw [dif_pos hB, dif_pos hA]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro a ha
    exact (Set.Finite.mem_toFinset hA) |>.mpr (hsub ((Set.Finite.mem_toFinset hB) |>.mp ha))
  · exact fun a ha _ => hf a ((Set.Finite.mem_toFinset hA) |>.mp ha)

/-- mod-shift: `q` may be absorbed into its residue inside a sum mod `n`. -/
private theorem q2modShift (q r X n : ℕ) : (q + r + X) % n = (q % n + r + X) % n := by
  have h : (q + (r + X)) % n = (q % n + (r + X)) % n :=
    (Nat.mod_modEq q n).symm.add_right (r + X)
  rwa [← Nat.add_assoc, ← Nat.add_assoc] at h

/-- With `k' = (q + 1 + (k - p % k)) % k` and `3 ≤ k'`, the corner vertex
index `k' - 1 + p % k` reduces to `q % k` modulo `k`. -/
private theorem q2cornerIdx (k p q : ℕ) (hk6 : k ≤ 6) (hk3 : 3 < k)
    (hp : p % k < k) (hq : q % k < k)
    (hk' : 3 ≤ (q + 1 + (k - p % k)) % k) :
    ((q + 1 + (k - p % k)) % k - 1 + p % k) % k = q % k := by
  rcases (by omega : k = 4 ∨ k = 5 ∨ k = 6) with h | h | h
  · rw [h] at hp hq hk' ⊢
    rw [q2modShift q 1 (4 - p % 4) 4] at hk' ⊢
    interval_cases p % 4 <;> interval_cases q % 4 <;> omega
  · rw [h] at hp hq hk' ⊢
    rw [q2modShift q 1 (5 - p % 5) 5] at hk' ⊢
    interval_cases p % 5 <;> interval_cases q % 5 <;> omega
  · rw [h] at hp hq hk' ⊢
    rw [q2modShift q 1 (6 - p % 6) 6] at hk' ⊢
    interval_cases p % 6 <;> interval_cases q % 6 <;> omega

/-! ## the flag-override lemma: the (0, k'-1) J-pair carries exactly mkj -/

private theorem q2flagOverride (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s') (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) :
    s'.J 0 (s'.k - 1) = mkj := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hK : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']; simp only [scsHalfSliceV39]
  have hK0 : 0 < (q + 1 + (s.k - p % s.k)) % s.k := by omega
  have hm2 : ((q + 1 + (s.k - p % s.k)) % s.k - 1)
        % ((q + 1 + (s.k - p % s.k)) % s.k)
      = (q + 1 + (s.k - p % s.k)) % s.k - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hcond : ({(0:ℕ) % ((q + 1 + (s.k - p % s.k)) % s.k),
      ((q + 1 + (s.k - p % s.k)) % s.k - 1) % ((q + 1 + (s.k - p % s.k)) % s.k)} : Set ℕ)
      = {0, (q + 1 + (s.k - p % s.k)) % s.k - 1} := by
    rw [Nat.zero_mod, hm2]
  rw [← hs']
  simp only [scsHalfSliceV39]
  rw [if_pos hcond]

/-! ## the DIST_DIAG argument with flag-true hypothesis -/

/-- `DIST_DIAG_LE_CSTAB` (QKNVMLB.hl:7736) with `hj` resolved by the live
override flag (mkj = true makes the flag `s'.J 0 (s'.k-1)` true, which is
exactly what the `s.k = 4` ear case needs). -/
private theorem q2distDiagLe (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3)
    (hJ' : s'.J 0 (s'.k - 1))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) :
    dist (vv (p % s.k)) (vv (q % s.k)) ≤ cstab := by
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
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl
  obtain ⟨-, -, -, -, -, hk4, -⟩ := hsl
  rcases hk4 with hk4 | hbm
  · simp only [isScsSliceV39] at hsl0
    obtain ⟨hpair, -, -, -, -, -, hear'⟩ := hsl0
    simp only [scsSliceV39, Prod.mk.injEq] at hpair
    obtain ⟨he1, he2⟩ := hpair
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

/-! ## the ear-half dsv form -/

/-- An ear half with the live override flag: its full J-set is the corner
singleton, so its dsv is `d' + 0.1 * (cstab - dist(u,w))` with `u = vv (p % k)`,
`w = vv (q % k)` (HOL 6330-6400, the `is_ear` expansion). -/
private theorem q2earDsv (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv vv' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hea : isEarV39 s') (hmkj : mkj) :
    dsvV39 s' vv' = d' + 0.1 * (cstab - dist (vv (p % s.k)) (vv (q % s.k))) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk6 : s.k ≤ 6 := hscs.2.2.1
  have h3k : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hper : Periodic vv s.k := hBB.2.1
  obtain ⟨-, -, hk3, -, -, ⟨i, hJset, -, -, -⟩⟩ := id hea
  -- the override J-pair (k'-1, k') = (2, 3) carries mkj = true
  have hK : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']; simp only [scsHalfSliceV39]
  have hstep4 := QKNVMLB2_step04_corner_p35 s s' p q d' mkj hs' hscs hdiag
  rw [hk3] at hstep4
  simp only [Nat.reduceSub, Nat.reduceAdd] at hstep4
  have hJ2p : s'.J 2 3 := by rw [hstep4.1]; exact hmkj
  -- hence the ear's J-index is 2 and its J-set is {2}
  have hmem : (2:ℕ) ∈ ({i} : Set ℕ) := by rw [← hJset]; exact ⟨by omega, hJ2p⟩
  simp only [Set.mem_singleton_iff] at hmem
  have hi2 : i = 2 := hmem.symm
  rw [hi2] at hJset
  -- the corner-index arithmetic: (2 + p % s.k) reduces to q % s.k
  have hK3 : (q + 1 + (s.k - p % s.k)) % s.k = 3 := by rw [← hK]; exact hk3
  have hci := q2cornerIdx s.k p q hk6 h3k (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0)
    (le_of_eq hK3.symm)
  rw [hK3] at hci
  simp only [Nat.reduceSub] at hci
  have hp1 : vv (2 + p % s.k) = vv (q % s.k) := by
    rw [show vv (2 + p % s.k) = vv ((2 + p % s.k) % s.k) from
      (periodic_mod_eq_p23 hper (2 + p % s.k)).symm, hci]
  -- the dsv unfolding
  have hd'eq : s'.d = d' := by rw [← hs']; simp [scsHalfSliceV39]
  unfold dsvV39
  rw [hvv', if_pos hea, hk3, hJset, q2setSumSingleton]
  simp only [Nat.reduceMod, Nat.reduceAdd, Nat.zero_add]
  rw [hp1, dist_comm (vv (q % s.k)) (vv (p % s.k)), hd'eq]
  ring

/-! ## the non-ear-half dsv form -/

/-- A non-ear half with the live override flag: corner split (step02) +
interior re-index (step05) + the diagonal corner term. -/
private theorem q2nonEarDsv (s s' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv vv' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hne' : ¬ isEarV39 s') (hmkj : mkj) :
    dsvV39 s' vv' = d' - 0.1 * (setSum (q2T1set s p s')
        (fun j => cstab - dist (vv j) (vv (j + 1)))
      + (cstab - dist (vv (p % s.k)) (vv (q % s.k)))) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk'0 : 0 < s'.k := by omega
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hper : Periodic vv s.k := hBB.2.1
  have hfl : s'.J (s'.k - 1) (s'.k - 1 + 1) := by
    rw [(QKNVMLB2_step04_corner_p35 s s' p q d' mkj hs' hscs hdiag).1]; exact hmkj
  -- the corner-index arithmetic: (s'.k - 1 + p % s.k) reduces to q % s.k
  have hK : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']; simp only [scsHalfSliceV39]
  have hk'K : 3 ≤ (q + 1 + (s.k - p % s.k)) % s.k := by omega
  have hci := q2cornerIdx s.k p q hscs.2.2.1 (SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag)
    (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hk'K
  rw [← hK] at hci
  have hmod1 : (s'.k - 1) % s'.k = s'.k - 1 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (s'.k - 1 + 1) % s'.k = 0 := by
    have h1 : s'.k - 1 + 1 = s'.k := by omega
    rw [h1, Nat.mod_self]
  have hp1 : vv (s'.k - 1 + p % s.k) = vv (q % s.k) := by
    rw [show vv (s'.k - 1 + p % s.k) = vv ((s'.k - 1 + p % s.k) % s.k) from
      (periodic_mod_eq_p23 hper (s'.k - 1 + p % s.k)).symm, hci]
  -- the full J-sum: interior window + live corner
  have hfull : setSum {i | i < s'.k ∧ s'.J i (i + 1)}
        (fun i => cstab - dist (vv (i % s'.k + p % s.k))
            (vv ((i + 1) % s'.k + p % s.k)))
      = setSum (q2T1set s p s') (fun j => cstab - dist (vv j) (vv (j + 1)))
        + (cstab - dist (vv (p % s.k)) (vv (q % s.k))) := by
    rw [QKNVMLB2_step02_cornerSplit_p35 s'
      (fun i => cstab - dist (vv (i % s'.k + p % s.k))
          (vv ((i + 1) % s'.k + p % s.k))) hk'0,
      if_pos hfl,
      QKNVMLB2_step05_reindex_p35 s s' p q d' mkj vv hs' hscs hdiag hMM]
    simp only [hmod1, hmod2, Nat.zero_add]
    rw [hp1, dist_comm (vv (q % s.k)) (vv (p % s.k))]
  -- assemble
  have hd'eq : s'.d = d' := by rw [← hs']; simp [scsHalfSliceV39]
  unfold dsvV39
  rw [hvv', if_neg hne', hfull, hd'eq]
  ring

/-! ## q2g (step07): the mkj = true branch of QKNVMLB2 (HOL 6135-7735) -/

theorem QKNVMLB2_step07_mkjTrue_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv vv' vv'' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'')
    (hmkj : mkj) :
    dsvV39 s vv ≤ dsvV39 s' vv' + dsvV39 s'' vv'' := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  -- the slice unpacking (keep an intact copy for q2distDiagLe)
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl
  obtain ⟨hpair, -, -, -, -, hk4, hear'⟩ := hsl
  -- the live flags at (0, k'-1) / (0, k''-1)
  have hflag0' : s'.J 0 (s'.k - 1) := by
    rw [q2flagOverride s s' p q d' mkj hs' hscs hdiag]; exact hmkj
  have hdiag2 : scsDiag s.k q p :=
    ⟨fun e => hdiag.1 e.symm, fun e => hdiag.2.2 e.symm, fun e => hdiag.2.1 e.symm⟩
  have hflag0'' : s''.J 0 (s''.k - 1) := by
    rw [q2flagOverride s s'' q p d'' mkj hs'' hscs hdiag2]; exact hmkj
  rcases hear' hflag0' with hea | hea
  · -- ear s'
    rcases Classical.em (isEarV39 s'') with heb | hnb
    · -- both ears: the two corner terms are +0.1 each; need dist(u,w) ≤ cstab
      have hstep1 := QKNVMLB2_step01_dsv_p35 s p q vv hscs hdiag
      have hfin : ({j | j < s.k ∧ s.J j (j + 1)} : Set ℕ).Finite :=
        (Set.finite_lt_nat s.k).subset fun j hj => hj.1
      have hS0 : 0 ≤ setSum {j | j < s.k ∧ s.J j (j + 1)}
          (fun j => cstab - dist (vv j) (vv (j + 1))) :=
        q2setSumNonneg hfin (fun j _ => QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j)
      have hd'1 := q2earDsv s s' p q d' mkj vv vv' hs' hvv' hMM hscs hdiag hea hmkj
      have hd'2 := q2earDsv s s'' q p d'' mkj vv vv'' hs'' hvv'' hMM hscs hdiag2 heb hmkj
      have hdist := q2distDiagLe s s' s'' p q d' d'' mkj vv hflag0' hs' hs'' hMM hscs
        hdiag hsl0
      have hdsymm : dist (vv (p % s.k)) (vv (q % s.k))
          = dist (vv (q % s.k)) (vv (p % s.k)) := dist_comm _ _
      linarith
    · -- ear s' + non-ear s'': corner terms cancel; window T2 dominates
      have hstep1 := QKNVMLB2_step01_dsv_p35 s p q vv hscs hdiag
      have hfin : ({j | j < s.k ∧ s.J j (j + 1)} : Set ℕ).Finite :=
        (Set.finite_lt_nat s.k).subset fun j hj => hj.1
      have hd'1 := q2earDsv s s' p q d' mkj vv vv' hs' hvv' hMM hscs hdiag hea hmkj
      have hd'2 := q2nonEarDsv s s'' q p d'' mkj vv vv'' hs'' hvv'' hMM hscs hdiag2
        hnb hmkj
      have hA0fin : ({i | i < s''.k - 1} : Set ℕ).Finite := Set.finite_lt_nat _
      have hT2fin : (q2T1set s q s'').Finite := by
        refine (hA0fin.image (fun i => (i + q % s.k) % s.k)).subset ?_
        rintro j ⟨i, hi, hJi, hj⟩
        exact ⟨i, hi, hj.symm⟩
      have hT2sub : q2T1set s q s'' ⊆ {j | j < s.k ∧ s.J j (j + 1)} := by
        rintro j ⟨i, hi, hJi, hj⟩
        rw [hj]
        refine ⟨Nat.mod_lt _ hk0, ?_⟩
        exact SCS_J_PRIME_SUBSET_SCS_J_p35 s s'' q p d'' mkj hs'' hscs hdiag2 i hi hJi
      have hge2 := q2setSumSub hfin hT2fin hT2sub
        (fun j _ => QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j)
      have hdsymm : dist (vv (p % s.k)) (vv (q % s.k))
          = dist (vv (q % s.k)) (vv (p % s.k)) := dist_comm _ _
      linarith
  · -- ear s''
    rcases Classical.em (isEarV39 s') with heb | hnb
    · -- both ears (mirror)
      have hstep1 := QKNVMLB2_step01_dsv_p35 s p q vv hscs hdiag
      have hfin : ({j | j < s.k ∧ s.J j (j + 1)} : Set ℕ).Finite :=
        (Set.finite_lt_nat s.k).subset fun j hj => hj.1
      have hS0 : 0 ≤ setSum {j | j < s.k ∧ s.J j (j + 1)}
          (fun j => cstab - dist (vv j) (vv (j + 1))) :=
        q2setSumNonneg hfin (fun j _ => QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j)
      have hd'1 := q2earDsv s s' p q d' mkj vv vv' hs' hvv' hMM hscs hdiag heb hmkj
      have hd'2 := q2earDsv s s'' q p d'' mkj vv vv'' hs'' hvv'' hMM hscs hdiag2 hea hmkj
      have hdist := q2distDiagLe s s' s'' p q d' d'' mkj vv hflag0' hs' hs'' hMM hscs
        hdiag hsl0
      have hdsymm : dist (vv (p % s.k)) (vv (q % s.k))
          = dist (vv (q % s.k)) (vv (p % s.k)) := dist_comm _ _
      linarith
    · -- non-ear s' + ear s'': mirror of the mixed case with window T1
      have hstep1 := QKNVMLB2_step01_dsv_p35 s p q vv hscs hdiag
      have hfin : ({j | j < s.k ∧ s.J j (j + 1)} : Set ℕ).Finite :=
        (Set.finite_lt_nat s.k).subset fun j hj => hj.1
      have hd'1 := q2nonEarDsv s s' p q d' mkj vv vv' hs' hvv' hMM hscs hdiag hnb hmkj
      have hd'2 := q2earDsv s s'' q p d'' mkj vv vv'' hs'' hvv'' hMM hscs hdiag2 hea hmkj
      have hA0fin : ({i | i < s'.k - 1} : Set ℕ).Finite := Set.finite_lt_nat _
      have hT1fin : (q2T1set s p s').Finite := by
        refine (hA0fin.image (fun i => (i + p % s.k) % s.k)).subset ?_
        rintro j ⟨i, hi, hJi, hj⟩
        exact ⟨i, hi, hj.symm⟩
      have hT1sub : q2T1set s p s' ⊆ {j | j < s.k ∧ s.J j (j + 1)} := by
        rintro j ⟨i, hi, hJi, hj⟩
        rw [hj]
        refine ⟨Nat.mod_lt _ hk0, ?_⟩
        exact SCS_J_PRIME_SUBSET_SCS_J_p35 s s' p q d' mkj hs' hscs hdiag i hi hJi
      have hge1 := q2setSumSub hfin hT1fin hT1sub
        (fun j _ => QKNVMLB2_step03_p35 s p q vv hMM hscs hdiag j)
      have hdsymm : dist (vv (p % s.k)) (vv (q % s.k))
          = dist (vv (q % s.k)) (vv (p % s.k)) := dist_comm _ _
      linarith

/-! ## q2h: the flag↔mkj bridge -/

/-- The flag-mkj bridge: `is_scs_slice`'s first conjunct pins both half
slices to the flag `s'.J 0 (s'.k-1)`, so comparing with `hs'` at the
override pair gives `mkj = flag`. -/
private theorem q2flagEq (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (hs' : scsHalfSliceV39 s p q d' mkj = s') (hscs : isScsV39 s)
    (hdiag : scsDiag s.k p q) (hsl : isScsSliceV39 s s' s'' p q) :
    mkj = (s'.J 0 (s'.k - 1)) := by
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hK : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']; simp only [scsHalfSliceV39]
  have hK0 : 0 < (q + 1 + (s.k - p % s.k)) % s.k := by omega
  have hm2 : ((q + 1 + (s.k - p % s.k)) % s.k - 1)
        % ((q + 1 + (s.k - p % s.k)) % s.k)
      = (q + 1 + (s.k - p % s.k)) % s.k - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hcond : ({(0:ℕ) % ((q + 1 + (s.k - p % s.k)) % s.k),
      ((q + 1 + (s.k - p % s.k)) % s.k - 1) % ((q + 1 + (s.k - p % s.k)) % s.k)} : Set ℕ)
      = {0, (q + 1 + (s.k - p % s.k)) % s.k - 1} := by
    rw [Nat.zero_mod, hm2]
  -- s'.d = d' and s' = scsHalfSliceV39 s p q d' (s'.J 0 (s'.k-1))
  have hd'eq : s'.d = d' := by rw [← hs']; simp [scsHalfSliceV39]
  have hpair := hsl.1
  simp only [scsSliceV39, Prod.mk.injEq] at hpair
  obtain ⟨he1, -⟩ := hpair
  rw [hd'eq] at he1
  -- apply the J-projection at (0, k'-1) to the two equal half slices
  have heq : scsHalfSliceV39 s p q d' mkj = scsHalfSliceV39 s p q d' (s'.J 0 (s'.k - 1)) :=
    Eq.trans hs' he1
  have hJ := congrArg (fun t : ScsV39 => t.J 0 (t.k - 1)) heq
  simp only [scsHalfSliceV39] at hJ
  rw [if_pos hcond, if_pos hcond] at hJ
  exact hJ

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
  have hmeq : mkj = (s'.J 0 (s'.k - 1)) :=
    q2flagEq s s' s'' p q d' d'' mkj hs' hscs hdiag hsl
  subst hmeq
  rcases Classical.em (s'.J 0 (s'.k - 1)) with hflag | hflag
  · exact QKNVMLB2_step07_mkjTrue_p35 s s' s'' p q d' d'' (s'.J 0 (s'.k - 1)) vv vv'
      vv'' hs' hs'' hvv' hvv'' hMM hscs hdiag hsl hd hflag
  · exact QKNVMLB2_step06_mkjFalse_p35 s s' s'' p q d' d'' (s'.J 0 (s'.k - 1)) vv vv'
      vv'' hs' hs'' hvv' hvv'' hMM hscs hdiag hsl hd hflag
  -- DISCHARGES: source 5522-7735 complete.  The mkj = false branch is
  -- `QKNVMLB2_step06_mkjFalse_p35`, the mkj = true branch is
  -- `QKNVMLB2_step07_mkjTrue_p35` (ear / non-ear half dsv forms with the live
  -- diagonal corner terms cancelling by dist symmetry; the both-ears subcase
  -- via `q2distDiagLe` — the DIST_DIAG argument under the live flag), both
  -- assembled through the flag-mkj bridge `q2flagEq`.

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

/-! ## Section B helpers (patch: insert after LA35:1017, before :1019) -/

/-- Unordered-pair equality splits into the two pairings. -/
private theorem pairMem_p35 {a w b c : V3} (h : ({a, w} : Set V3) = {b, c}) :
    (a = b ∨ a = c) ∧ (w = b ∨ w = c) := by
  have m1 : a ∈ ({b, c} : Set V3) := by rw [← h]; simp
  have m2 : w ∈ ({b, c} : Set V3) := by rw [← h]; simp
  refine ⟨?_, ?_⟩
  · rcases Set.mem_insert_iff.mp m1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  · rcases Set.mem_insert_iff.mp m2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Set.mem_singleton_iff.mp h2)

/-- `k ∣ t` from `i ≡ i + t (mod k)`. -/
private theorem modEqAddCancel_p35 {k i t : ℕ} (hk0 : 0 < k) (h : i % k = (i + t) % k) :
    t % k = 0 := by
  have h1 : (i % k + t % k) % k = i % k := by
    have e : (i % k + t % k) % k = (i + t) % k := by rw [Nat.add_mod i t k]
    rw [e, h]
  have hik : i % k < k := Nat.mod_lt i hk0
  have htk : t % k < k := Nat.mod_lt t hk0
  have d : (i % k + t % k) % k = i % k + t % k ∨
      (i % k + t % k) % k + k = i % k + t % k := by
    rcases Nat.lt_or_ge (i % k + t % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : i % k + t % k = (i % k + t % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show i % k + t % k - k < k by omega)]
        omega)
  rcases d with d | d <;> omega

/-- `k`-shifted indices carry the same `vv`-value. -/
private theorem vvAddK_p35 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) (i : ℕ) :
    vv (i + k) = vv i := by
  rw [← periodic_mod_eq_p23 hper (i + k), Nat.add_mod_right]
  exact periodic_mod_eq_p23 hper i

/-- A `1 % k = 0` hypothesis forces `k ≤ 1`. -/
private theorem modOneZero_le_p35 {k : ℕ} (h : (1:ℕ) % k = 0) : k ≤ 1 := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · omega
  · have h1 : (1:ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- The vertex and its cyclic successor differ once `3 ≤ k`. -/
private theorem vvNeStep_p35 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have h := modEqAddCancel_p35 hk0 (i := i) (t := 1) (vvModEq_p35 hk0 hper hinj hh)
  exact absurd hk3 (by have := modOneZero_le_p35 h; omega)

/-- The vertex and its cyclic predecessor differ once `3 ≤ k`. -/
private theorem vvNePred_p35 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + k - 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hh2 : vv i = vv (i + (k - 1)) := by
    have hsub : (i + k) - 1 = i + (k - 1) := by omega
    calc vv i = vv (i + k - 1) := hh
      _ = vv ((i + k) - 1) := rfl
      _ = vv (i + (k - 1)) := by rw [hsub]
  have h := modEqAddCancel_p35 hk0 (i := i) (t := k - 1) (vvModEq_p35 hk0 hper hinj hh2)
  have hmod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Edge membership in the cyclic edge set: the two neighbours. -/
private theorem vvMemEdge_p35 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k) (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) (w : V3) :
    w ∈ ee (vv i) E ↔ w = vv (i + k - 1) ∨ w = vv (i + 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  -- singleton-edge contradiction: vv j = vv (j + 1) is impossible for k ≥ 3
  have hnosing : ∀ j : ℕ, vv j ≠ vv (j + 1) := fun j => vvNeStep_p35 hk3 hper hinj j
  show {vv i, w} ∈ E ↔ _
  constructor
  · intro hw
    rw [← hE] at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨ha, hwbc⟩ := pairMem_p35 hj.symm
    rcases ha with hai | hai
    · have hmod : i % k = j % k := vvModEq_p35 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · exfalso
        -- w = vv j: the pair {vv j, vv (j+1)} must be the singleton {vv i}
        have hsucc : vv j = vv (j + 1) := by
          have m : vv (j + 1) ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
          rw [hw1, hai] at m
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
          exact m.elim (fun h => h.symm) (fun h => h.symm)
        exact absurd hsucc (hnosing j)
      · refine Or.inr ?_
        rw [hw1, vvStep_p35 hper hmod]
    · have hmod1 : i % k = (j + 1) % k := vvModEq_p35 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · -- w = vv j = the cyclic predecessor of vv i
        refine Or.inl ?_
        have hpred : (i + k - 1) % k = j % k := by
          have hstep : (i + k - 1 + 1) % k = (j + 1) % k := by
            rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
            exact hmod1
          exact vvModPred_p35 hk0 hstep
        rw [hw1, ← periodic_mod_eq_p23 hper j, ← hpred,
          periodic_mod_eq_p23 hper (i + k - 1)]
      · exfalso
        -- w = vv (j + 1) = vv i: singleton edge again
        rw [← hai] at hw1
        have m : vv j ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
        rw [hw1] at m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
        have hvj : vv j = vv i := m.elim id id
        exact absurd (hvj.trans hai) (hnosing j)
  · rintro (rfl | rfl)
    · show {vv i, vv (i + k - 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i + k - 1, by
        show {vv (i + k - 1), vv (i + k - 1 + 1)} = {vv i, vv (i + k - 1)}
        rw [show i + k - 1 + 1 = i + k from by omega, vvAddK_p35 hper i]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto⟩
    · show {vv i, vv (i + 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i, rfl⟩

/-- The interior angle at a cyclic vertex equals the fan azimuth of its dart
(cyclic-fan specialization of HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM`,
Nkezbfc.hl:39, via the two-point neighbour set). -/
private theorem vvInangleEq_p35 {vv : ℕ → V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF) (i : ℕ) :
    interiorAngle1 0 FF (vv i) = azimInFan (vv i, vv (i + 1)) E := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := by
    intro hh
    have hmod := vvModEq_p35 hk0 hper hinj hh
    have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
      have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
        rw [Nat.add_mod]
      have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by rw [Nat.add_mod]
      rw [g1, g2, hmod]
    rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
    have h3 := modEqAddCancel_p35 hk0 (i := i) (t := 2) hplus
    have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact vvMemEdge_p35 hk3 hper hinj hE i w
  have hnc : (ee (vv i) E).ncard = 2 := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hcond : 1 < (ee (vv i) E).ncard := by rw [hnc]; omega
  have hsoe : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E = ee (vv i) E := by
    ext z
    show ({vv i, z} ∈ E ∧ z ∈ (Set.univ : Set V3)) ↔ {vv i, z} ∈ E
    simp
  have hne2 : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ≠ {vv (i + 1)} := by
    intro hc
    have hmem : vv (i + k - 1) ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E := by
      rw [hsoe, hee]
      simp
    rw [hc, Set.mem_singleton_iff] at hmem
    exact hstep hmem
  have hsucc : Kepler.Text.Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1)) =
      vv (i + k - 1) := by
    simp only [Kepler.Text.Fan.sigmaFan, if_neg hne2]
    refine epsFixed_p35 ?_ ?_
    · refine ⟨?_, hstep, ?_⟩
      · rw [hsoe, hee]
        simp
      · intro w1 hw1 hw1ne
        rw [hsoe, hee] at hw1
        rcases Set.mem_insert_iff.mp hw1 with h | h
        · rw [h]
        · exact absurd h hw1ne
    · intro z hz
      obtain ⟨hz1, hz2, -⟩ := hz
      rw [hsoe, hee] at hz1
      rcases Set.mem_insert_iff.mp hz1 with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hz2
  show azim 0 (vv i) (rhoNode1 FF (vv i)) (ivsRhoNode1 FF (vv i))
    = azimInFan (vv i, vv (i + 1)) E
  have hrho : rhoNode1 FF (vv i) = vv (i + 1) :=
    vvRhoDet_p35 hk0 hper hinj hFF (by rw [← hFF]; exact Set.mem_range.mpr ⟨i, rfl⟩)
  have hivs : ivsRhoNode1 FF (vv i) = vv (i + k - 1) :=
    vvIvsDet_p35 hk0 hper hinj hFF (by
      rw [← hFF]
      refine Set.mem_range.mpr ⟨i + k - 1, ?_⟩
      show (vv (i + k - 1), vv (i + k - 1 + 1)) = (vv (i + k - 1), vv i)
      rw [show i + k - 1 + 1 = i + k from by omega, vvAddK_p35 hper i])
  rw [hrho, hivs, ← hsucc, azimInFan, if_pos hcond]

/-- `setSum` over `{i | i < k}` folds to a `Finset.range k` sum. -/
private theorem setSum_Iio_p35 (f : ℕ → ℝ) (k : ℕ) :
    setSum {i | i < k} f = ∑ i ∈ Finset.range k, f i := by
  rw [setSum]
  have hfin : {i | i < k}.Finite := Set.finite_Iio k
  rw [dif_pos hfin]
  have hEq : hfin.toFinset = Finset.range k := by
    ext i
    simp [Set.mem_toFinset, Finset.mem_range]
  rw [hEq]

/-- The cyclic dart set folds to a `Finset.range k` sum. -/
private theorem setSum_FF_p35 (vv : ℕ → V3) (g : V3 × V3 → ℝ) (k : ℕ) (hk0 : 0 < k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) :
    setSum (Set.range (fun i => (vv i, vv (i + 1)))) g
      = ∑ i ∈ Finset.range k, g (vv i, vv (i + 1)) := by
  have hperd : Periodic (fun i => (vv i, vv (i + 1))) k := by
    intro i
    show (vv (i + k), vv (i + k + 1)) = (vv i, vv (i + 1))
    rw [hper i, Nat.add_right_comm i k 1, hper (i + 1)]
  have hrange : Set.range (fun i => (vv i, vv (i + 1)))
      = (fun i => (vv i, vv (i + 1))) '' Set.Iio k :=
    range_periodic_image_p23 _ k hk0 hperd
  have hfin : ((fun i => (vv i, vv (i + 1))) '' Set.Iio k).Finite :=
    Set.Finite.image _ (Set.finite_Iio k)
  have hinj3 : ∀ x ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      ∀ y ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      (vv x, vv (x + 1)) = (vv y, vv (y + 1)) → x = y := by
    intro x hx y hy hxy
    have hxk : x < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hx
    have hyk : y < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hy
    by_contra hne
    have hfst : vv x = vv y := congrArg Prod.fst hxy
    exact hinj x y hxk hyk hne hfst
  have hEq2 : hfin.toFinset =
      (Set.Finite.toFinset (Set.finite_Iio k)).image (fun i => (vv i, vv (i + 1))) := by
    ext x
    simp [Set.mem_image, Set.Finite.mem_toFinset, Set.mem_Iio]
  have hEq3 : (Set.Finite.toFinset (Set.finite_Iio k)) = Finset.range k := by
    ext i
    simp [Set.mem_toFinset, Finset.mem_range]
  rw [hrange, setSum, dif_pos hfin, hEq2, Finset.sum_image hinj3, hEq3]

/-- Cyclic shift of a `range k` sum. -/
private theorem sum_shift_p35 (G : ℕ → ℝ) (k c : ℕ) (hk0 : 0 < k)
    (hper : Periodic G k) :
    ∑ i ∈ Finset.range k, G (i + c) = ∑ i ∈ Finset.range k, G i := by
  have hstep : ∀ i ∈ Finset.range k, G (i + c) = G ((i + c) % k) := fun i _ =>
    (periodic_mod_eq_p23 hper (i + c)).symm
  refine Finset.sum_bij (fun i _ => (i + c) % k)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hk0))
    (fun i hi j hj hij =>
      have h1 : i % k = j % k := modAddCancel_p35 (c := c) hij
      have h2 : i = j := by
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h1
        exact h1
      h2)
    (fun t ht =>
      have htk : t < k := Finset.mem_range.mp ht
      have hck : c % k < k := Nat.mod_lt c hk0
      have hck2 : c % k ≤ c := Nat.mod_le c k
      ⟨(t + k - c % k) % k, Finset.mem_range.mpr (Nat.mod_lt _ hk0),
        by
          have e1 : Nat.ModEq k ((t + k - c % k) % k) (t + k - c % k) :=
            Nat.mod_mod_of_dvd _ (Nat.dvd_refl k)
          have e2 : Nat.ModEq k ((t + k - c % k) % k + c) ((t + k - c % k) + c) :=
            Nat.ModEq.add_right c e1
          have e4 : Nat.ModEq k (t + k) t := Nat.add_mod_right t k
          have gc : Nat.ModEq k c (c % k) :=
            Nat.ModEq.symm (Nat.mod_mod_of_dvd c (Nat.dvd_refl k))
          have ee : Nat.ModEq k ((t + k - c % k) + c) ((t + k - c % k) + c % k) :=
            Nat.ModEq.add_left _ gc
          have g2 : (t + k - c % k) + c % k = t + k := by omega
          rw [g2] at ee
          have hchain : Nat.ModEq k ((t + k - c % k) % k + c) t := e2.trans (ee.trans e4)
          rw [hchain]
          exact Nat.mod_eq_of_lt htk⟩)
    (fun a ha => hstep a ha)

/-- HOL `VV_SUC_EQ_RHO_NODE_PRIME` (QKNVMLB.hl:8054). -/
theorem VV_SUC_EQ_RHO_NODE_PRIME_p35 (s : ScsV39) (k p1 p q : ℕ) (u : V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
    (hk : s.k = k) (hp1 : vv p1 = u)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hBB : BBsV39 s vv) :
    ∀ m, (rhoNode1 FF)^[m] u = vv (m + p1) := by

  have hk0 : 0 < k := by have := hscs.2.1; omega
  have hper : Periodic vv k := by rw [← hk]; exact hBB.2.1
  have hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j := by
    intro i j hi hj hne he
    have i' : i < s.k := by rw [hk]; exact hi
    have j' : j < s.k := by rw [hk]; exact hj
    exact vvInjAux_p35 s vv hscs hBB i j i' j' hne he
  exact vvOrbit_p35 hk0 hper hinj hFF u p1 hp1
  -- DISCHARGES (lkgrqui-mid-w2 2026-10-28): source 8054-8089; k > 3 twin of
  -- VV_SUC_EQ_RHO_NODE_p35 — same vvOrbit_p35 route (hk3 unused).

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

  have hkle : 3 ≤ s.k := by omega
  have hk0 : 0 < s.k := lt_of_le_of_lt (by norm_num) hkle
  have hper : Periodic vv s.k := hBB.2.1
  have hinj := vvInjAux_p35 s vv hscs hBB
  have horbit := vvOrbit_p35 hk0 hper hinj hFF u (p % s.k) hp
  have hAng := vvInangleEq_p35 hkle hper hinj hE hFF
  have hGper : Periodic
      (fun j => rhoFun (norm (vv j)) * azimInFan (vv j, vv (j + 1)) E) s.k := by
    intro j
    show rhoFun (norm (vv (j + s.k))) * azimInFan (vv (j + s.k), vv (j + s.k + 1)) E
      = rhoFun (norm (vv j)) * azimInFan (vv j, vv (j + 1)) E
    rw [hper j, Nat.add_right_comm j s.k 1, hper (j + 1)]
  have hL : setSum {i | i < s.k}
      (fun i => rhoFun (norm (vv (i + p % s.k))) *
        interiorAngle1 0 FF ((rhoNode1 FF)^[i] u))
      = ∑ i ∈ Finset.range s.k,
          (fun j => rhoFun (norm (vv j)) * azimInFan (vv j, vv (j + 1)) E)
            (i + p % s.k) := by
    rw [setSum_Iio_p35]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [horbit i, hAng]
  have hR : setSum FF (fun e => rhoFun (norm e.1) * azimInFan e E)
      = ∑ i ∈ Finset.range s.k,
          (fun j => rhoFun (norm (vv j)) * azimInFan (vv j, vv (j + 1)) E) i := by
    rw [← hFF, setSum_FF_p35 vv (fun e => rhoFun (norm e.1) * azimInFan e E) s.k hk0 hper hinj]
  rw [hL, hR]
  exact sum_shift_p35 _ s.k (p % s.k) hk0 hGper
  -- DISCHARGES (lkgrqui-mid-w2 2026-10-28): source 8089-8202; per-face azimuth
  -- split of the vertex sum — vvOrbit_p35 (replacing VV_SUC_EQ_RHO_NODE_PRIME)
  -- + the cyclic-fan interiorAngle1 = azimInFan identity (vvInangleEq_p35, the
  -- two-point-neighbour specialization of CONVEX_LOFA_IMP_INANGLE_EQ_AZIM)
  -- + the setSum re-index (setSum_Iio_p35 / setSum_FF_p35 / sum_shift_p35).

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

  have hk0 : 0 < k := by have := hscs.2.1; omega
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hge := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hk'0 : 0 < k' := by have := hge.1; rw [hk'] at this; omega
  have hk'k : k' < k := by rw [← hk', ← hk]; exact hge.2.2
  have hper : Periodic vv k := by rw [← hk]; exact hBB.2.1
  have hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j := by
    intro i j hi hj hne he
    have i' : i < s.k := by rw [hk]; exact hi
    have j' : j < s.k := by rw [hk]; exact hj
    exact vvInjAux_p35 s vv hscs hBB i j i' j' hne he
  have horbit := vvOrbit_p35 hk0 hper hinj hFF u (p % k) hp
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_Iio, Set.mem_range]
  constructor
  · rintro ⟨hik, j, hj⟩
    rw [horbit i] at hj
    have hmodEq : (j % k' + p % k) % k = (i + p % k) % k :=
      vvModEq_p35 hk0 hper hinj hj
    have h1 : j % k' % k = i % k := modAddCancel_p35 (c := p % k) hmodEq
    have hjk : j % k' < k' := Nat.mod_lt j hk'0
    have hjk2 : j % k' < k := lt_of_lt_of_le hjk (Nat.le_of_lt hk'k)
    rw [Nat.mod_eq_of_lt hjk2, Nat.mod_eq_of_lt hik] at h1
    omega
  · intro hik
    refine ⟨lt_of_lt_of_le hik (Nat.le_of_lt hk'k), i, ?_⟩
    rw [horbit i, Nat.mod_eq_of_lt hik]
  -- DISCHARGES (lkgrqui-mid-w2 2026-10-28): source 8202-8319; the slice's
  -- vertex orbit is exactly the k'-window — vvOrbit_p35 + SCS_K_PRIME_LE_GE
  -- (3 ≤ k' < k) + residue arithmetic (i ≡ j % k' mod k, both < k ⇒ i = j % k').

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

-- SUM_AZIM_EQ_ANGLE_EQ4_p35 (SF-86, lkgrqui-eq4-w3 2026-10-28): the frozen
-- statement dropped the `IsHypE_p35 V (E ∪ {{u, w}}) HS` carrier its HOL
-- original (QKNVMLB.hl:8445) pins via the canonical hypermap, so as stated
-- it has countermodels (HS := hypermapOfFan 0 V E). Ruled: + hHS. The
-- declaration now lives at EOF below (after its proved twin), closed by
-- `exact SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 ..`.

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

/-! ## lkgrqui-le4eq4-fin-w2: the le4eq4-w2 helper kit (26 private pieces) inlined verbatim, plus the final bookkeeping assembly `tausplit_le4` and the window azimuth-sum identity `winSum_le4`. -/
/-! ## Azimuth three-point addition (verbatim port of TopologyFan.lean
`azim_sum_core` / `sum4_azim_fan`; only `Kepler.Geom` primitives of
`AzimLemmas.lean` are used, which are on this file's import face). -/

private theorem azimSumCore_le4 {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hncu : ¬ Collinear3 x v u) (hnc1 : ¬ Collinear3 x v w1)
    (hnc2 : ¬ Collinear3 x v w2) :
    ∃ n : ℤ, azim x v u w2 =
      azim x v u w1 + azim x v w1 w2 + (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr (fun he => hxv he))
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hncu hnc1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hncu hnc2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec hnc1 hnc2 hon hax hxv
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  refine ⟨n, ?_⟩
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2

private theorem azimSplit_le4 {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hncu : ¬ Collinear3 x v u) (hnc1 : ¬ Collinear3 x v w1)
    (hnc2 : ¬ Collinear3 x v w2)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨n, hc3⟩ := azimSumCore_le4 hxv hncu hnc1 hnc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-! ## Annulus chord separation, `dist < 4` variant (LocalAuto4
`nonparallel_ball_annulus_aux` with the bound generalized to `< 4`; the
`≤ cstab`/`≤ 3.62` variants are LocalAuto4, the `< 4` one only LocalAuto38). -/

private theorem noncollAnnulus4_le4 {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (h2 : 2 ≤ dist v w) (h4 : dist v w < 4) :
    ¬ Collinear3 (0:V3) v w := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hv
  obtain ⟨hw2, hwu⟩ := ballAnnulus_norm_bounds hw
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hv2; norm_num at hv2
  have h0126 : h0 = 1.26 := rfl
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul hvne).mp hcol
  have hwv : w = c • v := by simpa using hc
  have e2 : ‖w‖ = |c| * ‖v‖ := by rw [hwv, norm_smul, Real.norm_eq_abs]
  by_cases hc0 : 0 ≤ c
  · have e3 : ‖w‖ = c * ‖v‖ := by rw [e2, abs_of_nonneg hc0]
    have e1 : ‖v - w‖ = |(1 - c) * ‖v‖| := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖v‖)]
    have habs : (1 - c) * ‖v‖ = ‖v‖ - c * ‖v‖ := by ring
    have e4 : ‖v - w‖ = |‖v‖ - ‖w‖| := by
      rw [e1, habs, e3]
    have hb : |‖v‖ - ‖w‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h02 : h0 < 2 := by norm_num [h0126]
    rw [dist_eq_norm] at h2
    rw [e4] at h2
    linarith
  · have e1 : ‖v - w‖ = ‖v‖ + ‖w‖ := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - c)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : c < 0)]
      ring
    rw [dist_eq_norm] at h4
    rw [e1] at h4
    linarith

/-! ## Cyclic-fan dart kit (the mid-w2 private helpers, duplicated here:
they are `private` in LocalAuto35 and not importable). -/

private theorem epsFixed_le4 {α : Type*} [Nonempty α] {pr : α → Prop} {a : α}
    (hpa : pr a) (huniq : ∀ y, pr y → y = a) : Classical.epsilon pr = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

private theorem pairMem_le4 {a w b c : V3} (h : ({a, w} : Set V3) = {b, c}) :
    (a = b ∨ a = c) ∧ (w = b ∨ w = c) := by
  have m1 : a ∈ ({b, c} : Set V3) := by rw [← h]; simp
  have m2 : w ∈ ({b, c} : Set V3) := by rw [← h]; simp
  refine ⟨?_, ?_⟩
  · rcases Set.mem_insert_iff.mp m1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  · rcases Set.mem_insert_iff.mp m2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Set.mem_singleton_iff.mp h2)

private theorem modEqAddCancel_le4 {k i t : ℕ} (hk0 : 0 < k) (h : i % k = (i + t) % k) :
    t % k = 0 := by
  have h1 : (i % k + t % k) % k = i % k := by
    have e : (i % k + t % k) % k = (i + t) % k := by rw [Nat.add_mod i t k]
    rw [e, h]
  have hik : i % k < k := Nat.mod_lt i hk0
  have htk : t % k < k := Nat.mod_lt t hk0
  have d : (i % k + t % k) % k = i % k + t % k ∨
      (i % k + t % k) % k + k = i % k + t % k := by
    rcases Nat.lt_or_ge (i % k + t % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : i % k + t % k = (i % k + t % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show i % k + t % k - k < k by omega)]
        omega)
  rcases d with d | d <;> omega

private theorem modOneZero_le_le4 {k : ℕ} (h : (1:ℕ) % k = 0) : k ≤ 1 := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · omega
  · have h1 : (1:ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
    omega

private theorem vvAddK_le4 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) (i : ℕ) :
    vv (i + k) = vv i := by
  rw [← periodic_mod_eq_p23 hper (i + k), Nat.add_mod_right]
  exact periodic_mod_eq_p23 hper i

private theorem vvModEq_le4 {vv : ℕ → V3} {k : ℕ} (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) {i j : ℕ} (h : vv i = vv j) :
    i % k = j % k := by
  by_contra hne
  have h1 : vv (i % k) = vv (j % k) := by
    rw [periodic_mod_eq_p23 hper i, periodic_mod_eq_p23 hper j, h]
  exact hinj (i % k) (j % k) (Nat.mod_lt i hk0) (Nat.mod_lt j hk0) hne h1

private theorem vvStep_le4 {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) {i j : ℕ}
    (h : i % k = j % k) : vv (i + 1) = vv (j + 1) := by
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [← periodic_mod_eq_p23 hper (i + 1), ← periodic_mod_eq_p23 hper (j + 1), e1, e2, h]

private theorem vvModPred_le4 {k : ℕ} {i j : ℕ} (hk0 : 0 < k)
    (h : (i + 1) % k = (j + 1) % k) : i % k = j % k := by
  have hik : i % k < k := Nat.mod_lt i hk0
  have hjk : j % k < k := Nat.mod_lt j hk0
  have e1 : (i + 1) % k = (i % k + 1) % k := by simp [Nat.add_mod]
  have e2 : (j + 1) % k = (j % k + 1) % k := by simp [Nat.add_mod]
  rw [e1, e2] at h
  have hs : i % k + 1 = j % k + 1 ∨ (i % k + 1 = k ∧ j % k + 1 = k) := by
    rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact Or.inl h
      · have h2 : j % k + 1 = k := by omega
        rw [h2, Nat.mod_self] at h
        exact absurd h (by omega)
    · have h2 : i % k + 1 = k := by omega
      rw [h2, Nat.mod_self] at h
      rcases Nat.lt_or_ge (j % k + 1) k with hlt2 | hge2
      · rw [Nat.mod_eq_of_lt hlt2] at h
        exact absurd h (by omega)
      · have h3 : j % k + 1 = k := by omega
        exact Or.inr ⟨h2, h3⟩
  omega

private theorem modAddCancel_le4 {k a b c : ℕ} (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0] at h ⊢
    simpa [Nat.mod_zero] using h
  have hak : a % k < k := Nat.mod_lt a hk0
  have hbk : b % k < k := Nat.mod_lt b hk0
  have hck : c % k < k := Nat.mod_lt c hk0
  have e1 : (a + c) % k = (a % k + c % k) % k := by rw [Nat.add_mod]
  have e2 : (b + c) % k = (b % k + c % k) % k := by rw [Nat.add_mod]
  rw [e1, e2] at h
  have d1 : (a % k + c % k) % k = a % k + c % k ∨
      (a % k + c % k) % k + k = a % k + c % k := by
    rcases Nat.lt_or_ge (a % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hX : a % k + c % k = (a % k + c % k - k) + k * 1 := by omega
        rw [hX, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show a % k + c % k - k < k by omega)]
        omega)
  have d2 : (b % k + c % k) % k = b % k + c % k ∨
      (b % k + c % k) % k + k = b % k + c % k := by
    rcases Nat.lt_or_ge (b % k + c % k) k with hlt | hge
    · exact Or.inl (Nat.mod_eq_of_lt hlt)
    · refine Or.inr (by
        have hY : b % k + c % k = (b % k + c % k - k) + k * 1 := by omega
        rw [hY, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show b % k + c % k - k < k by omega)]
        omega)
  rcases d1 with d1 | d1 <;> rcases d2 with d2 | d2 <;> omega

private theorem vvNeStep_le4 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have h := modEqAddCancel_le4 hk0 (i := i) (t := 1) (vvModEq_le4 hk0 hper hinj hh)
  exact absurd hk3 (by have := modOneZero_le_le4 h; omega)

private theorem vvNePred_le4 {vv : ℕ → V3} {k : ℕ} (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) (i : ℕ) :
    vv i ≠ vv (i + k - 1) := by
  intro hh
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hh2 : vv i = vv (i + (k - 1)) := by
    have hsub : (i + k) - 1 = i + (k - 1) := by omega
    calc vv i = vv (i + k - 1) := hh
      _ = vv ((i + k) - 1) := rfl
      _ = vv (i + (k - 1)) := by rw [hsub]
  have h := modEqAddCancel_le4 hk0 (i := i) (t := k - 1) (vvModEq_le4 hk0 hper hinj hh2)
  have hmod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  omega

private theorem vvMemEdge_le4 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ} (hk3 : 3 ≤ k)
    (hper : Periodic vv k) (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) (w : V3) :
    w ∈ ee (vv i) E ↔ w = vv (i + k - 1) ∨ w = vv (i + 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hnosing : ∀ j : ℕ, vv j ≠ vv (j + 1) := fun j => vvNeStep_le4 hk3 hper hinj j
  show {vv i, w} ∈ E ↔ _
  constructor
  · intro hw
    rw [← hE] at hw
    obtain ⟨j, hj⟩ := hw
    obtain ⟨ha, hwbc⟩ := pairMem_le4 hj.symm
    rcases ha with hai | hai
    · have hmod : i % k = j % k := vvModEq_le4 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · exfalso
        have hsucc : vv j = vv (j + 1) := by
          have m : vv (j + 1) ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
          rw [hw1, hai] at m
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
          exact m.elim (fun h => h.symm) (fun h => h.symm)
        exact absurd hsucc (hnosing j)
      · refine Or.inr ?_
        rw [hw1, vvStep_le4 hper hmod]
    · have hmod1 : i % k = (j + 1) % k := vvModEq_le4 hk0 hper hinj hai
      rcases hwbc with hw1 | hw1
      · refine Or.inl ?_
        have hpred : (i + k - 1) % k = j % k := by
          have hstep : (i + k - 1 + 1) % k = (j + 1) % k := by
            rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
            exact hmod1
          exact vvModPred_le4 hk0 hstep
        rw [hw1, ← periodic_mod_eq_p23 hper j, ← hpred,
          periodic_mod_eq_p23 hper (i + k - 1)]
      · exfalso
        rw [← hai] at hw1
        have m : vv j ∈ ({vv i, w} : Set V3) := by rw [← hj]; simp
        rw [hw1] at m
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m
        have hvj : vv j = vv i := m.elim id id
        exact absurd (hvj.trans hai) (hnosing j)
  · rintro (rfl | rfl)
    · show {vv i, vv (i + k - 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i + k - 1, by
        show {vv (i + k - 1), vv (i + k - 1 + 1)} = {vv i, vv (i + k - 1)}
        rw [show i + k - 1 + 1 = i + k from by omega, vvAddK_le4 hper i]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto⟩
    · show {vv i, vv (i + 1)} ∈ E
      rw [← hE]
      exact Set.mem_range.mpr ⟨i, rfl⟩

/-- The fan successor at a cyclic-fan dart is the cyclic predecessor. -/
private theorem sigmaFanVal_le4 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    Kepler.Text.Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1)) = vv (i + k - 1) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := by
    intro hh
    have hmod := vvModEq_le4 hk0 hper hinj hh
    have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
      have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
        rw [Nat.add_mod]
      have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by rw [Nat.add_mod]
      rw [g1, g2, hmod]
    rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
    have h3 := modEqAddCancel_le4 hk0 (i := i) (t := 2) hplus
    have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact vvMemEdge_le4 hk3 hper hinj hE i w
  have hnc : (ee (vv i) E).ncard = 2 := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hcond : 1 < (ee (vv i) E).ncard := by rw [hnc]; omega
  have hsoe : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E = ee (vv i) E := by
    ext z
    show ({vv i, z} ∈ E ∧ z ∈ (Set.univ : Set V3)) ↔ {vv i, z} ∈ E
    simp
  have hne2 : Kepler.Text.Fan.setOfEdge (vv i) Set.univ E ≠ {vv (i + 1)} := by
    intro hc
    have hmem : vv (i + k - 1) ∈ Kepler.Text.Fan.setOfEdge (vv i) Set.univ E := by
      rw [hsoe, hee]
      simp
    rw [hc, Set.mem_singleton_iff] at hmem
    exact hstep hmem
  simp only [Kepler.Text.Fan.sigmaFan, if_neg hne2]
  refine epsFixed_le4 ?_ ?_
  · refine ⟨?_, hstep, ?_⟩
    · rw [hsoe, hee]
      simp
    · intro w1 hw1 hw1ne
      rw [hsoe, hee] at hw1
      rcases Set.mem_insert_iff.mp hw1 with h | h
      · rw [h]
      · exact absurd h hw1ne
  · intro z hz
    obtain ⟨hz1, hz2, -⟩ := hz
    rw [hsoe, hee] at hz1
    rcases Set.mem_insert_iff.mp hz1 with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hz2

/-- The fan azimuth of a cyclic dart is the three-point azimuth to the cyclic
predecessor (cyclic-fan specialization of HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM`,
Nkezbfc.hl:39, via the two-point neighbour set). -/
private theorem azimInFanVal_le4 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) (i : ℕ) :
    azimInFan (vv i, vv (i + 1)) E = azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hsucc := sigmaFanVal_le4 hk3 hper hinj hE i
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := by
    intro hh
    have hmod := vvModEq_le4 hk0 hper hinj hh
    have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
      have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
        rw [Nat.add_mod]
      have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by rw [Nat.add_mod]
      rw [g1, g2, hmod]
    rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
    have h3 := modEqAddCancel_le4 hk0 (i := i) (t := 2) hplus
    have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact vvMemEdge_le4 hk3 hper hinj hE i w
  have hnc : (ee (vv i) E).ncard = 2 := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hcond : 1 < (ee (vv i) E).ncard := by rw [hnc]; omega
  rw [azimInFan, if_pos hcond, hsucc]

/-- The closed fan wedge at a cyclic dart, definitionally. -/
private theorem wedgeMem_le4 {vv : ℕ → V3} {E : Set (Set V3)} {k : ℕ}
    (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E) {i : ℕ} {z : V3}
    (hz : z ∈ wedgeInFanGe (vv i, vv (i + 1)) E) :
    0 ≤ azim 0 (vv i) (vv (i + 1)) z ∧
      azim 0 (vv i) (vv (i + 1)) z ≤ azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hk0 : 0 < k := lt_of_le_of_lt (by norm_num) hk3
  have hstep : vv (i + k - 1) ≠ vv (i + 1) := by
    intro hh
    have hmod := vvModEq_le4 hk0 hper hinj hh
    have hplus : ((i + k - 1) + 1) % k = ((i + 1) + 1) % k := by
      have g1 : ((i + k - 1) + 1) % k = ((i + k - 1) % k + 1 % k) % k := by
        rw [Nat.add_mod]
      have g2 : ((i + 1) + 1) % k = ((i + 1) % k + 1 % k) % k := by rw [Nat.add_mod]
      rw [g1, g2, hmod]
    rw [show (i + k - 1) + 1 = i + k from by omega, Nat.add_mod_right] at hplus
    have h3 := modEqAddCancel_le4 hk0 (i := i) (t := 2) hplus
    have h4 : (2:ℕ) % k = 2 := Nat.mod_eq_of_lt (by omega)
    omega
  have hee : ee (vv i) E = {vv (i + k - 1), vv (i + 1)} := by
    ext w
    exact vvMemEdge_le4 hk3 hper hinj hE i w
  have hnc : (ee (vv i) E).ncard = 2 := by
    rw [hee, Set.ncard_insert_of_notMem
      (show vv (i + k - 1) ∉ ({vv (i + 1)} : Set V3) from by simp [hstep])]
    simp
  have hcond : 1 < (ee (vv i) E).ncard := by rw [hnc]; omega
  have hsucc := sigmaFanVal_le4 hk3 hper hinj hE i
  have hw : wedgeInFanGe (vv i, vv (i + 1)) E
      = wedgeGe 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
    rw [wedgeInFanGe, if_pos hcond, hsucc]
  rw [hw, wedgeGe, Set.mem_setOf_eq] at hz
  exact hz


/-! ## `setSum` / cardinality of the cyclic dart set, window periodicity and
injectivity, and the window-sum split (mid-w2 `setSum_FF_p35` /
`CARD_FF_EQ_SCS_K_3_p35` generalized to arbitrary `k ≥ 3`). -/

/-- `setSum` over `{i | i < k}` folds to a `Finset.range k` sum. -/
private theorem setSumIio_le4 (f : ℕ → ℝ) (k : ℕ) :
    setSum {i | i < k} f = ∑ i ∈ Finset.range k, f i := by
  rw [setSum]
  have hfin : {i | i < k}.Finite := Set.finite_Iio k
  rw [dif_pos hfin]
  have hEq : hfin.toFinset = Finset.range k := by
    ext i
    simp [Set.mem_toFinset, Finset.mem_range]
  rw [hEq]

/-- The cyclic dart set folds to a `Finset.range k` sum. -/
private theorem setSumDarts_le4 (vv : ℕ → V3) (g : V3 × V3 → ℝ) (k : ℕ) (hk0 : 0 < k)
    (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) :
    setSum (Set.range (fun i => (vv i, vv (i + 1)))) g
      = ∑ i ∈ Finset.range k, g (vv i, vv (i + 1)) := by
  have hperd : Periodic (fun i => (vv i, vv (i + 1))) k := by
    intro i
    show (vv (i + k), vv (i + k + 1)) = (vv i, vv (i + 1))
    rw [hper i, Nat.add_right_comm i k 1, hper (i + 1)]
  have hrange : Set.range (fun i => (vv i, vv (i + 1)))
      = (fun i => (vv i, vv (i + 1))) '' Set.Iio k :=
    range_periodic_image_p23 _ k hk0 hperd
  have hfin : ((fun i => (vv i, vv (i + 1))) '' Set.Iio k).Finite :=
    Set.Finite.image _ (Set.finite_Iio k)
  have hinj3 : ∀ x ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      ∀ y ∈ (Set.Finite.toFinset (Set.finite_Iio k)),
      (vv x, vv (x + 1)) = (vv y, vv (y + 1)) → x = y := by
    intro x hx y hy hxy
    have hxk : x < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hx
    have hyk : y < k := by simpa [Set.mem_toFinset, Set.mem_Iio] using hy
    by_contra hne
    have hfst : vv x = vv y := congrArg Prod.fst hxy
    exact hinj x y hxk hyk hne hfst
  have hEq2 : hfin.toFinset =
      (Set.Finite.toFinset (Set.finite_Iio k)).image (fun i => (vv i, vv (i + 1))) := by
    ext x
    simp [Set.mem_image, Set.Finite.mem_toFinset, Set.mem_Iio]
  have hEq3 : (Set.Finite.toFinset (Set.finite_Iio k)) = Finset.range k := by
    ext i
    simp [Set.mem_toFinset, Finset.mem_range]
  rw [hrange, setSum, dif_pos hfin, hEq2, Finset.sum_image hinj3, hEq3]

/-- The cyclic dart set has cardinality `k` (generalized
`CARD_FF_EQ_SCS_K_3_p35`). -/
private theorem ncardDarts_le4 (vv : ℕ → V3) (k : ℕ) (hk0 : 0 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j) :
    (Set.range fun i => (vv i, vv (i + 1))).ncard = k := by
  have hperd : Periodic (fun i => (vv i, vv (i + 1))) k := by
    intro i
    show (vv (i + k), vv (i + k + 1)) = (vv i, vv (i + 1))
    rw [hper i, Nat.add_right_comm i k 1, hper (i + 1)]
  rw [range_periodic_image_p23 _ k hk0 hperd, Set.InjOn.ncard_image]
  · rw [Set.ncard_Iio_nat]
  · intro i hi j hj hne
    have hik : i < k := hi
    have hjk : j < k := hj
    have hmod : i % k = j % k :=
      vvModEq_le4 hk0 hper hinj (congrArg Prod.fst hne)
    rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at hmod
    exact hmod

/-- The half-slice vertex map is `k'`-periodic. -/
private theorem perWin_le4 {vv : ℕ → V3} {k k' p : ℕ} (hk'0 : 0 < k')
    (hper : Periodic vv k) : Periodic (fun i => vv (i % k' + p % k)) k' := by
  intro i
  show vv ((i + k') % k' + p % k) = vv (i % k' + p % k)
  rw [Nat.add_mod_right]

/-- The half-slice vertex map is injective on the window (`k' < k`). -/
private theorem injWin_le4 {vv : ℕ → V3} {k k' p : ℕ} (hk0 : 0 < k) (hk'0 : 0 < k')
    (hk'k : k' < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    {i j : ℕ} (hi : i < k') (hj : j < k')
    (h : vv (i % k' + p % k) = vv (j % k' + p % k)) : i = j := by
  have hmod : (i % k' + p % k) % k = (j % k' + p % k) % k := vvModEq_le4 hk0 hper hinj h
  have h1 : i % k' % k = j % k' % k := modAddCancel_le4 hmod
  have hik : i % k' < k' := Nat.mod_lt i hk'0
  have hjk : j % k' < k' := Nat.mod_lt j hk'0
  have e1 : i % k' % k = i % k' :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hik (Nat.le_of_lt hk'k))
  have e2 : j % k' % k = j % k' :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hjk (Nat.le_of_lt hk'k))
  rw [e1, e2, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1
  exact h1

/-- A window sum starts with its first term (`m ≥ 1`). -/
private theorem windowSumSucc_le4 (G : ℕ → ℝ) (c : ℕ) : ∀ m, 0 < m →
    ∑ t ∈ Finset.range m, G (c + t) = G c + ∑ t ∈ Finset.range (m - 1), G (c + 1 + t) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
    intro hm
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simp
    · have hm1 : n + 1 - 1 = n := by omega
      rw [hm1, Finset.sum_range_succ']
      have hcongr : ∑ t ∈ Finset.range n, G (c + (t + 1))
          = ∑ t ∈ Finset.range n, G (c + 1 + t) :=
        Finset.sum_congr rfl fun t _ => by ring
      have hz : G (c + 0) = G c := by rw [Nat.add_zero]
      linarith

/-- The two window arcs of a cycle cover it with exactly the two endpoints
double-counted. -/
private theorem sumSplit_le4 (G : ℕ → ℝ) (k a b : ℕ) (hk0 : 0 < k)
    (hGper : Periodic G k) (hab : a < b) (hbk : b < k) :
    ∑ i ∈ Finset.range k, G i + G a + G b
      = ∑ i ∈ Finset.range (b + 1 - a), G (a + i)
        + ∑ j ∈ Finset.range (k + a + 1 - b), G (b + j) := by
  have hkb1 : 0 < k - b := by omega
  have hL1 : ∑ i ∈ Finset.range k, G i
      = ∑ i ∈ Finset.range (b + 1), G i + ∑ i ∈ Finset.range (k - b - 1), G (b + 1 + i) := by
    have hk : k = (b + 1) + (k - b - 1) := by omega
    conv_lhs => rw [hk]
    rw [Finset.sum_range_add]
  have hL2 : ∑ i ∈ Finset.range (b + 1), G i
      = ∑ i ∈ Finset.range a, G i
        + (G a + ∑ i ∈ Finset.range (b - a), G (a + 1 + i)) := by
    have h1 : b + 1 = a + (b + 1 - a) := by omega
    conv_lhs => rw [h1]
    rw [Finset.sum_range_add, windowSumSucc_le4 G a (b + 1 - a) (by omega)]
    have h2 : b - a = b + 1 - a - 1 := by omega
    rw [h2]
  have hR1 : ∑ i ∈ Finset.range (b + 1 - a), G (a + i)
      = G a + ∑ i ∈ Finset.range (b - a), G (a + 1 + i) := by
    have h := windowSumSucc_le4 G a (b + 1 - a) (by omega)
    have hba : b + 1 - a - 1 = b - a := by omega
    rw [h, hba]
  have hR2 : ∑ j ∈ Finset.range (k + a + 1 - b), G (b + j)
      = ∑ t ∈ Finset.range (k - b), G (b + t) + ∑ j ∈ Finset.range (a + 1), G j := by
    have hk2 : k + a + 1 - b = (k - b) + (a + 1) := by omega
    conv_lhs => rw [hk2]
    rw [Finset.sum_range_add]
    have hR2b : ∑ x ∈ Finset.range (a + 1), G (b + ((k - b) + x))
        = ∑ x ∈ Finset.range (a + 1), G x := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hje : b + ((k - b) + j) = k + j := by omega
      rw [hje, Nat.add_comm k j, hGper j]
    rw [hR2b]
  have hR3 : ∑ t ∈ Finset.range (k - b), G (b + t)
      = G b + ∑ t ∈ Finset.range (k - b - 1), G (b + 1 + t) :=
    windowSumSucc_le4 G b (k - b) hkb1
  have hR4 : ∑ j ∈ Finset.range (a + 1), G j = ∑ j ∈ Finset.range a, G j + G a :=
    Finset.sum_range_succ _ a
  linarith

/-- The half-slice window sizes add up to `k + 2` (diag boundaries excluded by
`scs_diag`). -/
private theorem hksum_le4 (k a b k' k'' : ℕ) (hk4 : 4 ≤ k)
    (ha : a < k) (hb : b < k) (hd1 : ¬(a = b))
    (hd2 : (a + 1) % k ≠ b) (hd3 : a ≠ (b + 1) % k)
    (e1 : k' = (b + 1 + (k - a)) % k) (e2 : k'' = (a + 1 + (k - b)) % k) :
    k' + k'' = k + 2 := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hb1 : 0 < b + 1 - a := by omega
    have hlt1 : b + 1 - a < k := by
      rcases Nat.eq_zero_or_pos a with ha0 | hap
      · subst ha0
        rcases Nat.lt_or_ge (b + 1) k with h | h2
        · omega
        · have hb1k : (b + 1) % k = 0 := by
            have hbe : b + 1 = k := by omega
            subst hbe
            exact Nat.mod_self _
          exact absurd hb1k.symm hd3
      · omega
    have hb2 : a + 1 < b := by
      rcases Nat.lt_or_ge (a + 1) b with h | h
      · exact h
      · have hbe : b = a + 1 := by omega
        have hlt : (a + 1) % k = a + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hbe] at hd2
        exact absurd hlt hd2
    have hk'v : k' = b + 1 - a := by
      have h1 : b + 1 + (k - a) = (b + 1 - a) + k := by omega
      rw [e1, h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
    have hk''v : k'' = k + a + 1 - b := by
      have h2 : a + 1 + (k - b) = k + a + 1 - b := by omega
      rw [e2, h2, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hab1 : 0 < a + 1 - b := by omega
    have hlt2 : a + 1 - b < k := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbp
      · subst hb0
        rcases Nat.lt_or_ge (a + 1) k with h | h2
        · omega
        · have ha1k : (a + 1) % k = 0 := by
            have hae : a + 1 = k := by omega
            subst hae
            exact Nat.mod_self _
          exact absurd ha1k hd2
      · omega
    have hb1 : b + 1 < a := by
      rcases Nat.lt_or_ge (b + 1) a with h | h
      · exact h
      · have hae : a = b + 1 := by omega
        have hlt : (b + 1) % k = b + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hae] at hd3
        exact absurd hlt.symm hd3
    have hk'v : k' = k + b + 1 - a := by
      have h1 : b + 1 + (k - a) = k + b + 1 - a := by omega
      rw [e1, h1, Nat.mod_eq_of_lt (by omega)]
    have hk''v : k'' = a + 1 - b := by
      have h2 : a + 1 + (k - b) = (a + 1 - b) + k := by omega
      rw [e2, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
    omega


/-! ## C3③c/③d main-kit: tau decomposition of a window system, the
`azim ≤ π → dihV` bridge (LocalAuto38 `p38_azim_eq_dihV` copy; LuneVolume's
`azim_dihv_same`/`azim_dihv_compl` are public and on the import face), and
the two distance bound helpers. -/

/-- On `azim ≤ π` the azimuth equals the geometric dihedral (copy of
LocalAuto38 `p38_azim_eq_dihV`). -/
private theorem azimEqDihv_le4 {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hp : azim v w v1 v2 ≤ Real.pi) :
    azim v w v1 v2 = dihV v w v1 v2 := by
  rcases lt_or_eq_of_le hp with hlt | heq
  · exact azim_dihv_same h1 h2 hlt
  · have hle : Real.pi ≤ azim v w v1 v2 := by rw [heq]
    have hc := azim_dihv_compl h1 h2 hle
    rw [heq]
    linarith

/-- Edge-adjacent window vertices are at distance `≤ cstab` (the `3 < k`
`b`-bound of `isScsV39` transported through `BBs`). -/
private theorem distPairCstab_le4 {s : ScsV39} {vv : ℕ → V3} {k : ℕ} (hk : s.k = k)
    (hscs : isScsV39 s) (hBB : BBsV39 s vv) (hk3 : 3 < k) (i : ℕ) :
    dist (vv i) (vv (i + 1)) ≤ cstab := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hchain, -, -, -, hbc, -, -, -⟩ := hscs
  have hk3s : 3 < s.k := by rw [hk]; exact hk3
  have hd1 : dist (vv i) (vv (i + 1)) ≤ s.b i (i + 1) := (hBB.2.2.1 i (i + 1)).2
  have hbb : s.b i (i + 1) ≤ cstab := hbc i hk3s
  exact hd1.trans hbb

/-- Residue form of the edge distance bound. -/
private theorem distPairCstabMod_le4 {s : ScsV39} {vv : ℕ → V3} {k : ℕ} (hk : s.k = k)
    (hscs : isScsV39 s) (hBB : BBsV39 s vv) (hk3 : 3 < k) (hper : Periodic vv k) (i : ℕ) :
    dist (vv (i % k)) (vv ((i + 1) % k)) ≤ cstab := by
  have hd := distPairCstab_le4 hk hscs hBB hk3 (i % k)
  have hcong : ((i % k) + 1) % k = (i + 1) % k := by
    rw [@Nat.add_mod i 1 k, show (1:ℕ) % k = 1 from Nat.mod_eq_of_lt (show (1:ℕ) < k from by omega)]
  have he : vv ((i % k) + 1) = vv ((i + 1) % k) := by
    rw [← periodic_mod_eq_p23 hper (i % k + 1), ← hcong]
  rw [he] at hd
  exact hd

/-- The diagonal pair of the slice is at distance `< 4` (`bm p q < 4` of
`isScsSliceV39` + the `MMs` `bm`-upper bound, transported to the residues). -/
private theorem distDiag4_le4 {s : ScsV39} {vv : ℕ → V3} {k p q : ℕ} (hk : s.k = k)
    (hscs : isScsV39 s) (hMM : vv ∈ MMsV39 s) (hk0 : 0 < k) (hbm : s.bm p q < 4) :
    dist (vv (p % k)) (vv (q % k)) < 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hpbm, -, -, -, -, -, -, -, -, -, -, -⟩ := hscs
  rw [hk] at hpbm
  simp only [MMsV39, Set.mem_setOf_eq] at hMM
  obtain ⟨-, -, -, -, -, hbmle⟩ := hMM
  have hp' : p % k < k := Nat.mod_lt _ hk0
  have hq' : q % k < k := Nat.mod_lt _ hk0
  have hres : s.bm (p % k) (q % k) = s.bm p q := by
    have hper1 : Periodic (fun z => s.bm z (q % k)) k := fun t => (hpbm t (q % k)).1
    have hper2 : Periodic (fun z => s.bm p z) k := fun t => (hpbm p t).2
    calc s.bm (p % k) (q % k) = s.bm p (q % k) := periodic_mod_eq_p23 hper1 p
      _ = s.bm p q := periodic_mod_eq_p23 hper2 q
  have hd : dist (vv (p % k)) (vv (q % k)) ≤ s.bm (p % k) (q % k) :=
    hbmle (p % k) (q % k)
  rw [hres] at hd
  exact lt_of_le_of_lt hd hbm

/-- The taustar of a `k'`-window system, in azimuth-sum form (`k' ≥ 3`; the
`k' = 3` branch consumes the tau3-azimuth transport `hslot`). -/
private theorem halfTau_le4 (w : ℕ → V3) (k' : ℕ) (E' : Set (Set V3)) (FF' : Set (V3 × V3))
    (s' : ScsV39) (hk's' : s'.k = k')
    (hk'3 : 3 ≤ k') (hper' : Periodic w k')
    (hinj' : ∀ i j, i < k' → j < k' → i ≠ j → w i ≠ w j)
    (hE' : Set.range (fun i => {w i, w (i + 1)}) = E')
    (hFF' : Set.range (fun i => (w i, w (i + 1))) = FF')
    (hslot : k' = 3 → tau3 (w 0) (w 1) (w 2)
      = ∑ i ∈ Finset.range k', rhoFun (norm (w i)) * azimInFan (w i, w (i + 1)) E'
        - (Real.pi + sol0)) :
    taustarV39 s' w = ∑ i ∈ Finset.range k', rhoFun (norm (w i)) * azimInFan (w i, w (i + 1)) E'
      - (Real.pi + sol0) * ((k' - 2 : ℕ) : ℝ) - dsvV39 s' w := by
  rcases Nat.eq_or_lt_of_le hk'3 with h3 | h3
  · rw [taustarV39, if_pos (by rw [hk's']; omega), hslot h3.symm, h3.symm]
    simp
  · have hk'0 : 0 < k' := by omega
    have hns : ¬(s'.k ≤ 3) := Nat.not_le.mpr (by rw [hk's']; omega)
    rw [taustarV39, if_neg hns, tauFun,
      setSumDarts_le4 w _ k' hk'0 hper' hinj',
      ncardDarts_le4 w k' hk'0 hper' hinj', hE']


/-- A nonzero residue-step separates residues (wrapper). -/
private theorem stepNe_le4 {k i t : ℕ} (hk3 : 3 ≤ k) (ht : t % k ≠ 0) :
    ¬(i % k = (i + t) % k) := fun hh => ht (modEqAddCancel_le4 (by omega) hh)

/-! ## The diagonal azimuth split at a dart (the corner identity closing the
window bookkeeping: the fan azimuth at `(i, i+1)` splits at the diagonal ray
`j` because the wedge at the dart contains every vertex — the definitional
convexity conjunct of `ConvexLocalFan`). -/

private theorem splitDart_le4 {s : ScsV39} {vv : ℕ → V3} {k i j : ℕ}
    (hk : s.k = k) (hscs : isScsV39 s) (hBB : BBsV39 s vv) (hk3 : 3 < k)
    (hconv : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))))
    (hper : Periodic vv k)
    (hinjM : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hij4 : dist (vv i) (vv j) < 4) (hij2 : 2 ≤ dist (vv i) (vv j))
    (hijne : ¬(i % k = j % k)) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1))
      = azim 0 (vv i) (vv (i + 1)) (vv j)
        + azim 0 (vv i) (vv j) (vv (i + k - 1)) := by
  have hk0 : 0 < k := by omega
  have hsub : Set.range vv ⊆ ballAnnulus := hBB.1
  have hvne : ∀ x, vv x ≠ 0 := by
    intro x hx
    obtain ⟨h2, -⟩ := ballAnnulus_norm_bounds (hsub (Set.mem_range_self x))
    rw [hx, norm_zero] at h2
    exact absurd h2 (by norm_num)
  have hlem : (1:ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hne1 : ¬(i % k = (i + 1) % k) :=
    stepNe_le4 (k := k) (i := i) (t := 1) (by omega)
      (by
        intro hh
        rw [Nat.mod_eq_of_lt (by omega)] at hh
        omega)
  have hnekm1 : ¬(i % k = (i + k - 1) % k) := by
    have h := stepNe_le4 (k := k) (i := i) (t := k - 1) (by omega)
      (by
        have hkm1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
        rw [hkm1]
        omega)
    exact fun hh =>
      h (hh.trans (congrArg (fun n : ℕ => n % k)
        (show i + k - 1 = i + (k - 1) from by omega)))
  have twoLe : ∀ x y : ℕ, ¬(x % k = y % k) → 2 ≤ dist (vv x) (vv y) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
    rw [hk] at hdiag2
    intro x y hne
    have hxk : x % k < k := Nat.mod_lt x hk0
    have hyk : y % k < k := Nat.mod_lt y hk0
    have h1 : (2 : ℝ) ≤ s.a (x % k) (y % k) := hdiag2 (x % k) (y % k) ⟨hxk, hyk, hne⟩
    have h2 : s.a (x % k) (y % k) ≤ dist (vv (x % k)) (vv (y % k)) :=
      (hBB.2.2.1 (x % k) (y % k)).1
    have h3 : dist (vv (x % k)) (vv (y % k)) = dist (vv x) (vv y) := by
      rw [periodic_mod_eq_p23 hper x, periodic_mod_eq_p23 hper y]
    rw [← h3]
    exact h1.trans h2
  have ann : ∀ x : ℕ, vv x ∈ ballAnnulus := fun x => hsub (Set.mem_range_self x)
  have dist362 : ∀ x : ℕ, ‖vv x - vv (x + 1)‖ ≤ 3.62 := by
    intro x
    have hd := distPairCstab_le4 hk hscs hBB hk3 x
    rw [dist_eq_norm] at hd
    have hc : (cstab:ℝ) = 3.01 := rfl
    exact le_trans (hd.trans (by rw [hc])) (by norm_num)
  have hxv : vv i ≠ 0 := hvne i
  have hncu : ¬ Collinear3 0 (vv i) (vv (i + 1)) :=
    NONPARALLEL_BALL_ANNULUS362 (ann i) (ann (i + 1)) (twoLe i (i + 1) hne1) (dist362 i)
  have hnc1 : ¬ Collinear3 0 (vv i) (vv j) :=
    noncollAnnulus4_le4 (ann i) (ann j) hij2 hij4
  have hd2 : dist (vv (i + k - 1)) (vv (i + k)) ≤ cstab := by
    have hd := distPairCstabMod_le4 hk hscs hBB hk3 hper (i + k - 1)
    rw [show i + k - 1 + 1 = i + k from by omega,
      periodic_mod_eq_p23 hper (i + k - 1), periodic_mod_eq_p23 hper (i + k)] at hd
    exact hd
  have hvk : vv (i + k) = vv i := vvAddK_le4 hper i
  have hd2' : dist (vv i) (vv (i + k - 1)) ≤ cstab := by
    rw [dist_comm] at hd2
    rw [hvk] at hd2
    exact hd2
  have hnc2 : ¬ Collinear3 0 (vv i) (vv (i + k - 1)) :=
    NONPARALLEL_BALL_ANNULUS362 (ann i) (ann (i + k - 1)) (twoLe i (i + k - 1) hnekm1)
      (by
        rw [dist_eq_norm] at hd2'
        exact le_trans hd2' (by norm_num [cstab]))
  have hdart : (vv i, vv (i + 1)) ∈ (Set.range fun i => (vv i, vv (i + 1))) :=
    Set.mem_range.mpr ⟨i, rfl⟩
  have hwedge := by
    rcases hconv with ⟨-, hconv2⟩
    have hm := hconv2 (vv i, vv (i + 1)) hdart
    have hm2 := hm.2 (Set.mem_range_self j)
    exact wedgeMem_le4 (hk3 := by omega) hper hinjM rfl (hz := hm2)
  exact azimSplit_le4 hxv hncu hnc1 hnc2 hwedge.2

/-- `Collinear3` argument swap (the underlying set is the same). -/
private theorem coll3_swap_le4 {a b c : V3} (h : Collinear3 a b c) : Collinear3 a c b := by
  unfold Collinear3 at h ⊢
  have hset : ({a, c, b} : Set V3) = {a, b, c} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact h

/-! ## The `k' = 3` tau3-azimuth transport (window specialization of HOL
8445-9059 `SUM_AZIM_EQ_ANGLE_EQ4`; the slot pi-bounds come from the
definitional convexity conjuncts plus the diagonal azimuth split). -/

private theorem slots3_le4 {s : ScsV39} {vv : ℕ → V3} {k p q : ℕ}
    (hk : s.k = k) (hscs : isScsV39 s) (hBB : BBsV39 s vv) (hk3 : 3 < k)
    (hconv : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))))
    (hper : Periodic vv k)
    (hinjM : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hMM : vv ∈ MMsV39 s) (hbm4 : s.bm p q < 4)
    (hd1 : ¬(p % k = q % k)) (hd2 : ¬((p + 1) % k = q % k))
    (hpq2 : (p % k + 2) % k = q % k)
    (E' : Set (Set V3))
    (hE' : Set.range (fun i => {vv (i % 3 + p % k), vv ((i + 1) % 3 + p % k)}) = E') :
    tau3 (vv (p % k)) (vv (1 % 3 + p % k)) (vv (2 % 3 + p % k))
      = ∑ i ∈ Finset.range 3, rhoFun (norm (vv (i % 3 + p % k))) *
          azimInFan (vv (i % 3 + p % k), vv ((i + 1) % 3 + p % k)) E'
        - (Real.pi + sol0) := by
  have hk0 : 0 < k := by omega
  have hq' : q % k < k := Nat.mod_lt q hk0
  have hsub : Set.range vv ⊆ ballAnnulus := hBB.1
  -- the three window vertices and the master transports
  have hw1 : vv (1 % 3 + p % k) = vv (p % k + 1) := by
    rw [show (1:ℕ) % 3 = 1 from rfl, Nat.add_comm]
  have hw2 : vv (2 % 3 + p % k) = vv (q % k) := by
    rw [show (2:ℕ) % 3 = 2 from rfl, Nat.add_comm,
      ← periodic_mod_eq_p23 hper (p % k + 2), hpq2]
  have hw3 : vv (3 % 3 + p % k) = vv (p % k) := by
    rw [show (3:ℕ) % 3 = 0 from rfl, Nat.zero_add]
  have hw4 : vv (4 % 3 + p % k) = vv (p % k + 1) := by
    rw [show (4:ℕ) % 3 = 1 from rfl, Nat.add_comm]
  -- distance facts
  have twoLe : ∀ x y : ℕ, ¬(x % k = y % k) → 2 ≤ dist (vv x) (vv y) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
    rw [hk] at hdiag2
    intro x y hne
    have hxk : x % k < k := Nat.mod_lt x hk0
    have hyk : y % k < k := Nat.mod_lt y hk0
    have h1 : (2 : ℝ) ≤ s.a (x % k) (y % k) := hdiag2 (x % k) (y % k) ⟨hxk, hyk, hne⟩
    have h2 : s.a (x % k) (y % k) ≤ dist (vv (x % k)) (vv (y % k)) :=
      (hBB.2.2.1 (x % k) (y % k)).1
    have h3 : dist (vv (x % k)) (vv (y % k)) = dist (vv x) (vv y) := by
      rw [periodic_mod_eq_p23 hper x, periodic_mod_eq_p23 hper y]
    rw [← h3]
    exact h1.trans h2
  have hduv1 : dist (vv (p % k)) (vv (p % k + 1)) ≤ cstab :=
    distPairCstab_le4 hk hscs hBB hk3 (p % k)
  have hdv1w : dist (vv (p % k + 1)) (vv (p % k + 2)) ≤ cstab :=
    distPairCstab_le4 hk hscs hBB hk3 (p % k + 1)
  have hduw : dist (vv (p % k)) (vv (q % k)) < 4 :=
    distDiag4_le4 hk hscs hMM hk0 hbm4
  have hne01 : ¬((p % k) % k = (p % k + 1) % k) :=
    stepNe_le4 (k := k) (i := p % k) (t := 1) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
  -- non-collinearity kit (Collinear3 is set-based, so argument swaps are rfl)
  have hnorm362 : ∀ x : ℕ, ‖vv x - vv (x + 1)‖ ≤ 3.62 := by
    intro x
    have hd := distPairCstab_le4 hk hscs hBB hk3 x
    rw [dist_eq_norm] at hd
    have hc : (cstab:ℝ) = 3.01 := rfl
    exact hd.trans (by rw [hc]; norm_num)
  have hnc01 : ¬ Collinear3 0 (vv (p % k)) (vv (p % k + 1)) :=
    NONPARALLEL_BALL_ANNULUS362 (hsub (Set.mem_range_self (p % k)))
      (hsub (Set.mem_range_self (p % k + 1))) (twoLe (p % k) (p % k + 1) hne01)
      (hnorm362 (p % k))
  have hnc0w : ¬ Collinear3 0 (vv (p % k)) (vv (q % k)) :=
    noncollAnnulus4_le4 (hsub (Set.mem_range_self (p % k)))
      (hsub (Set.mem_range_self (q % k)))
      (twoLe (p % k) (q % k) (fun hh => hd1 (by
        rw [Nat.mod_eq_of_lt (Nat.mod_lt p hk0), Nat.mod_eq_of_lt hq'] at hh
        exact hh)))
      hduw
  have hnc1w : ¬ Collinear3 0 (vv (p % k + 1)) (vv (q % k)) := by
    have hd : dist (vv (p % k + 1)) (vv (q % k)) ≤ cstab := by
      have h2 := hdv1w
      have hq2 : vv (p % k + 2) = vv (q % k) := by
        rw [← periodic_mod_eq_p23 hper (p % k + 2), hpq2]
      rw [hq2] at h2
      exact h2
    have hne1w : ¬((p % k + 1) % k = q % k) := by
      have htr : (p + 1) % k = (p % k + 1) % k := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1:ℕ) < k from by omega)]
      rw [← htr]
      exact hd2
    have h2 := twoLe (p % k + 1) (q % k) (fun hh => hne1w
      (by rw [Nat.mod_eq_of_lt hq'] at hh; exact hh))
    have hd3 : ‖vv (p % k + 1) - vv (q % k)‖ ≤ 3.62 := by
      rw [dist_eq_norm] at hd
      exact le_trans hd (by norm_num [cstab])
    exact NONPARALLEL_BALL_ANNULUS362 (hsub (Set.mem_range_self (p % k + 1)))
      (hsub (Set.mem_range_self (q % k))) h2 hd3
  -- master darts and their azimuth values
  have hdart0 : (vv (p % k), vv (p % k + 1)) ∈
      (Set.range fun i => (vv i, vv (i + 1))) := Set.mem_range.mpr ⟨p % k, rfl⟩
  have hdart1 : (vv (p % k + 1), vv (p % k + 2)) ∈
      (Set.range fun i => (vv i, vv (i + 1))) := Set.mem_range.mpr ⟨p % k + 1, rfl⟩
  have hdartq : (vv (q % k), vv (q % k + 1)) ∈
      (Set.range fun i => (vv i, vv (i + 1))) := Set.mem_range.mpr ⟨q % k, rfl⟩
  have hval0 : azimInFan (vv (p % k), vv (p % k + 1))
      (Set.range fun i => {vv i, vv (i + 1)})
      = azim 0 (vv (p % k)) (vv (p % k + 1)) (vv (p % k + k - 1)) :=
    azimInFanVal_le4 (by omega) hper hinjM rfl (p % k)
  have hval1 : azimInFan (vv (p % k + 1), vv (p % k + 2))
      (Set.range fun i => {vv i, vv (i + 1)})
      = azim 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k)) := by
    have hin := azimInFanVal_le4 (by omega) hper hinjM rfl (p % k + 1)
    have hvt2 : vv (p % k + 2) = vv (q % k) := by
      rw [← periodic_mod_eq_p23 hper (p % k + 2), hpq2]
    have hvt3 : vv (p % k + 1 + k - 1) = vv (p % k) := by
      rw [show p % k + 1 + k - 1 = p % k + k from by omega, vvAddK_le4 hper (p % k)]
    rw [hin, hvt2, hvt3]
  have hvalq : azimInFan (vv (q % k), vv (q % k + 1))
      (Set.range fun i => {vv i, vv (i + 1)})
      = azim 0 (vv (q % k)) (vv (q % k + 1)) (vv (q % k + k - 1)) :=
    azimInFanVal_le4 (by omega) hper hinjM rfl (q % k)
  -- the diagonal azimuth splits at the two diag darts
  have htr : ∀ hh : (p % k) % k = (q % k) % k, p % k = q % k :=
    fun hh => (Nat.mod_eq_of_lt (Nat.mod_lt p hk0)).symm.trans
      (hh.trans (Nat.mod_eq_of_lt hq'))
  have hduws : dist (vv (q % k)) (vv (p % k)) < 4 := by
    rw [dist_comm]
    exact hduw
  have hsplitu := by
    refine splitDart_le4 hk hscs hBB hk3 hconv hper hinjM hduw
      (twoLe (p % k) (q % k) (fun hh => hd1 (htr hh)))
      (fun hh => hd1 (htr hh))
  have hsplitq := by
    refine splitDart_le4 hk hscs hBB hk3 hconv hper hinjM hduws
      (twoLe (q % k) (p % k) (fun hh => hd1 (htr hh.symm)))
      (fun hh => hd1 (htr hh.symm))
  -- slot bounds
  have hpiA : azim 0 (vv (p % k)) (vv (p % k + 1)) (vv (q % k)) ≤ Real.pi := by
    obtain ⟨-, hconv2⟩ := hconv
    have hwedge := (wedgeMem_le4 (hk3 := by omega) hper hinjM rfl
      (hz := (hconv2 (vv (p % k), vv (p % k + 1)) hdart0).2
        (Set.mem_range_self (q % k)))).2
    have hpi := (hconv2 (vv (p % k), vv (p % k + 1)) hdart0).1
    rw [hval0] at hpi
    exact le_trans hwedge hpi
  have hpiB : azim 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k)) ≤ Real.pi := by
    obtain ⟨-, hconv2⟩ := hconv
    have hpi := (hconv2 (vv (p % k + 1), vv (p % k + 2)) hdart1).1
    rw [hval1] at hpi
    exact hpi
  have hpiC : azim 0 (vv (q % k)) (vv (p % k)) (vv (p % k + 1)) ≤ Real.pi := by
    have hsplit := hsplitq
    obtain ⟨-, hconv2⟩ := hconv
    have hwedge := (wedgeMem_le4 (hk3 := by omega) hper hinjM rfl
      (hz := (hconv2 (vv (q % k), vv (q % k + 1)) hdartq).2
        (Set.mem_range_self (p % k)))).2
    have hvtq : vv (q % k + k - 1) = vv (p % k + 1) := by
      have hpredq : (q % k + k - 1) % k = (p % k + 1) % k := by
        have hstep : (q % k + k - 1 + 1) % k = (p % k + 1 + 1) % k := by
          have e1 : q % k + k - 1 + 1 = q % k + k := by omega
          have e2 : (q % k + k) % k = q % k := by
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq']
          have e3 : (p % k + 1 + 1) % k = (p % k + 2) % k := rfl
          rw [e1, e2, e3, hpq2]
        exact vvModPred_le4 hk0 hstep
      rw [← periodic_mod_eq_p23 hper (q % k + k - 1), hpredq,
        periodic_mod_eq_p23 hper (p % k + 1)]
    rw [hvtq] at hsplit
    have hge : (0:ℝ) ≤ azim 0 (vv (q % k)) (vv (q % k + 1)) (vv (p % k)) :=
      azim_nonneg _ _ _ _
    have hL : azim 0 (vv (q % k)) (vv (q % k + 1)) (vv (q % k + k - 1)) ≤ Real.pi := by
      rw [← hvalq]
      exact (hconv2 (vv (q % k), vv (q % k + 1)) hdartq).1
    have hL' : azim 0 (vv (q % k)) (vv (q % k + 1)) (vv (p % k + 1)) ≤ Real.pi := by
      rw [← hvtq]
      exact hL
    linarith
  -- the dihV = azim bridges
  have hslotA : azim 0 (vv (p % k)) (vv (p % k + 1)) (vv (q % k))
      = dihV 0 (vv (p % k)) (vv (p % k + 1)) (vv (q % k)) :=
    azimEqDihv_le4 hnc01 hnc0w hpiA
  have hslotB : azim 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k))
      = dihV 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k)) :=
    azimEqDihv_le4 hnc1w (fun hh => hnc01 (coll3_swap_le4 hh)) hpiB
  have hslotC : azim 0 (vv (q % k)) (vv (p % k)) (vv (p % k + 1))
      = dihV 0 (vv (q % k)) (vv (p % k)) (vv (p % k + 1)) :=
    azimEqDihv_le4 (fun hh => hnc0w (coll3_swap_le4 hh))
      (fun hh => hnc1w (coll3_swap_le4 hh)) hpiC
  -- the window sum in azimuth form
  have hwper : Periodic (fun i => vv (i % 3 + p % k)) 3 := perWin_le4 (by norm_num) hper
  have hwinj : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      vv (i % 3 + p % k) ≠ vv (j % 3 + p % k) := by
    intro i j hi hj hne he
    exact hne (injWin_le4 hk0 (by norm_num) (by omega) hper hinjM hi hj he)
  have hvalw0 : rhoFun (norm (vv (0 % 3 + p % k))) *
      azimInFan (vv (0 % 3 + p % k), vv ((0 + 1) % 3 + p % k)) E'
      = rhoFun (norm (vv (p % k))) * azim 0 (vv (p % k)) (vv (p % k + 1)) (vv (q % k)) := by
    have hin := azimInFanVal_le4 (by norm_num) hwper hwinj hE' 0
    have hw0 : vv (0 % 3 + p % k) = vv (p % k) := by
      rw [show (0:ℕ) % 3 = 0 from rfl, Nat.zero_add]
    have hwt1 : vv ((0 + 1) % 3 + p % k) = vv (p % k + 1) := by
      rw [show (0:ℕ) + 1 = 1 from rfl, Nat.add_comm]
    have hwt2 : vv ((0 + 3 - 1) % 3 + p % k) = vv (q % k) := by
      rw [show (0 + 3 - 1) % 3 = 2 from rfl]
      exact hw2
    rw [hin, hw0, hwt1, hwt2]
  have hvalw1 : rhoFun (norm (vv (1 % 3 + p % k))) *
      azimInFan (vv (1 % 3 + p % k), vv ((1 + 1) % 3 + p % k)) E'
      = rhoFun (norm (vv (p % k + 1))) * azim 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k)) := by
    have hin := azimInFanVal_le4 (by norm_num) hwper hwinj hE' 1
    have hwt1 : vv ((1 + 1) % 3 + p % k) = vv (q % k) := by
      rw [show (1 + 1) % 3 = 2 from rfl]
      exact hw2
    have hwt2 : vv ((1 + 3 - 1) % 3 + p % k) = vv (p % k) := by
      rw [show (1 + 3 - 1) % 3 = 0 from rfl]
      exact hw3
    rw [hin, hw1, hwt1, hwt2]
  have hvalw2 : rhoFun (norm (vv (2 % 3 + p % k))) *
      azimInFan (vv (2 % 3 + p % k), vv ((2 + 1) % 3 + p % k)) E'
      = rhoFun (norm (vv (q % k))) * azim 0 (vv (q % k)) (vv (p % k)) (vv (p % k + 1)) := by
    have hin := azimInFanVal_le4 (by norm_num) hwper hwinj hE' 2
    have hwt1 : vv ((2 + 1) % 3 + p % k) = vv (p % k) := by
      rw [show (2 + 1) % 3 = 0 from rfl]
      exact hw3
    have hwt2 : vv ((2 + 3 - 1) % 3 + p % k) = vv (p % k + 1) := by
      rw [show (2 + 3 - 1) % 3 = 1 from rfl]
      exact hw4
    rw [hin, hw2, hwt1, hwt2]
  have hsum : ∑ i ∈ Finset.range 3, rhoFun (norm (vv (i % 3 + p % k))) *
        azimInFan (vv (i % 3 + p % k), vv ((i + 1) % 3 + p % k)) E'
      = rhoFun (norm (vv (p % k))) * azim 0 (vv (p % k)) (vv (p % k + 1)) (vv (q % k))
        + rhoFun (norm (vv (p % k + 1))) * azim 0 (vv (p % k + 1)) (vv (q % k)) (vv (p % k))
        + rhoFun (norm (vv (q % k))) * azim 0 (vv (q % k)) (vv (p % k)) (vv (p % k + 1)) := by
    rw [SUM_NUMSEG2_p35]
    rw [hvalw0, hvalw1, hvalw2]
  -- final assembly: tau3 unfold + the three bridges
  rw [hw1, hw2, SUM_NUMSEG2_p35, hvalw0, hvalw1, hvalw2, tau3,
    hslotA, hslotB, hslotC, rho_rho_fun, rho_rho_fun, rho_rho_fun]

private theorem winSum_le4 (vv : ℕ → V3) (G : ℕ → ℝ) (k a b k' : ℕ)
    (E' : Set (Set V3))
    (hk0 : 0 < k) (hk2 : 2 ≤ k) (ha : a < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hk'3 : 3 ≤ k') (hk'v : k' = (b + 1 + (k - a)) % k)
    (hb : b < k)
    (hE' : Set.range (fun i => ({vv (i % k' + a), vv ((i + 1) % k' + a)} : Set V3)) = E')
    (hGper : Periodic G k)
    (hGdef : ∀ i, G i = rhoFun (norm (vv i)) * azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1))) :
    (∑ i ∈ Finset.range k',
        rhoFun (norm (vv (i % k' + a))) *
          azimInFan (vv (i % k' + a), vv ((i + 1) % k' + a)) E')
      = rhoFun (norm (vv a)) * azim 0 (vv a) (vv (a + 1)) (vv b)
        + (∑ t ∈ Finset.range (k' - 2), G (a + 1 + t)
          + rhoFun (norm (vv b)) * azim 0 (vv b) (vv a) (vv (b + k - 1))) := by
  have hk'0 : 0 < k' := lt_of_le_of_lt (by norm_num) hk'3
  have hp' : Periodic (fun i => vv (i % k' + a)) k' := by
    intro i
    show vv ((i + k') % k' + a) = vv (i % k' + a)
    rw [Nat.add_mod_right]
  -- the window size is one of the two arc lengths
  have hcaseA : a < b → k' = b + 1 - a := by
    intro hlt
    have hdegen : ¬(a = 0 ∧ b = k - 1) := by
      rintro ⟨ha0, hb1⟩
      rw [ha0, hb1] at hk'v
      rw [show k - 1 + 1 + (k - 0) = k + k from by omega, Nat.add_mod_right,
        Nat.mod_self] at hk'v
      omega
    have hv : b + 1 + (k - a) = (b + 1 - a) + k := by omega
    rw [hk'v, hv, Nat.add_mod_right]
    refine Nat.mod_eq_of_lt ?_
    rcases Nat.lt_or_ge (b + 1 - a) k with hlt2 | hge2
    · exact hlt2
    · exact absurd (by omega : a = 0 ∧ b = k - 1) hdegen
  have hcaseB : ¬(b ≤ a ∧ a ≤ b + 1) := by
    rintro ⟨h1, h2⟩
    have hv : b + 1 + (k - a) = k ∨ b + 1 + (k - a) = k + 1 := by omega
    rcases hv with hv | hv
    · rw [hv] at hk'v
      rw [Nat.mod_self] at hk'v
      omega
    · rw [hv, show k + 1 = 1 + k from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)] at hk'v
      omega
  have hcaseC : b + 2 ≤ a → k' = k + b + 1 - a := by
    intro hbig
    have hvlt : b + 1 + (k - a) < k := by omega
    rw [hk'v, Nat.mod_eq_of_lt hvlt]
    omega
  have hk'c : k' = b + 1 - a ∨ k' = k + b + 1 - a := by
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact Or.inl (hcaseA hlt)
    · rcases Nat.lt_or_ge b (a - 1) with h2 | h2
      · exact Or.inr (hcaseC (by omega))
      · have h3 : a ≤ b + 1 := by omega
        exact absurd ⟨hge, h3⟩ hcaseB
  have hndegen : ¬(k' = b + 1 - a ∧ a = 0 ∧ b = k - 1) := by
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le b) hb
    have hmodlt := Nat.mod_lt (b + 1 + (k - a)) hkpos
    rintro ⟨h1, ha0, hb1⟩
    omega
  have hk'k : k' < k := by
    rcases hk'c with h | h
    · by_contra hge
      exact hndegen ⟨h, by omega, by omega⟩
    · omega
  have hinj' : ∀ i j : ℕ, i < k' → j < k' → i ≠ j →
      vv (i % k' + a) ≠ vv (j % k' + a) := by
    intro i j hi hj hne he
    refine hne ?_
    have hmod : (i % k' + a) % k = (j % k' + a) % k := vvModEq_le4 hk0 hper hinj he
    have h1 : i % k' % k = j % k' % k := modAddCancel_le4 hmod
    have hik : i % k' < k' := Nat.mod_lt i hk'0
    have hjk : j % k' < k' := Nat.mod_lt j hk'0
    have e1 : i % k' % k = i % k' := Nat.mod_eq_of_lt (lt_of_lt_of_le hik (Nat.le_of_lt hk'k))
    have e2 : j % k' % k = j % k' := Nat.mod_eq_of_lt (lt_of_lt_of_le hjk (Nat.le_of_lt hk'k))
    rw [e1, e2, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1
    exact h1
  have hpk : ∀ i : ℕ, vv ((i + k) % k) = vv i := by
    intro i
    rw [Nat.add_mod_right]
    exact periodic_mod_eq_p23 hper i
  have hpk2 : ∀ i : ℕ, vv (i + k) = vv i := fun i =>
    (periodic_mod_eq_p23 hper (i + k)).symm.trans (hpk i)
  -- the two residue transports
  have t1 : vv (a + k' - 1) = vv b := by
    rcases hk'c with hk'c | hk'c
    · rw [hk'c, show a + (b + 1 - a) - 1 = b from by omega]
    · rw [hk'c, show a + (k + b + 1 - a) - 1 = b + k from by omega, hpk2 b]
  have t3 : vv (a + k' - 2) = vv (b + k - 1) := by
    rcases hk'c with hk'c | hk'c
    · rw [hk'c, show a + (b + 1 - a) - 2 = b - 1 from by omega,
        show b + k - 1 = b - 1 + k from by omega, hpk2 (b - 1)]
    · rw [hk'c, show a + (k + b + 1 - a) - 2 = b + k - 1 from by omega]
  -- index reductions inside the window
  have hred1 : ∀ t : ℕ, t < k' - 2 → (1 + t) % k' = 1 + t := fun t ht =>
    Nat.mod_eq_of_lt (by omega)
  have hred2 : ∀ t : ℕ, t < k' - 2 → (1 + t + 1) % k' = 2 + t := fun t ht => by
    rw [show 1 + t + 1 = 2 + t from by ring]
    exact Nat.mod_eq_of_lt (by omega)
  have hred3 : ∀ t : ℕ, t < k' - 2 → t % k' = t := fun t ht =>
    Nat.mod_eq_of_lt (by omega)
  have hred4 : ∀ t : ℕ, t < k' - 2 → (1 + t + k' - 1) % k' = t := by
    intro t ht
    rw [show 1 + t + k' - 1 = t + k' from by omega, Nat.add_mod_right]
    exact hred3 t ht
  set f : ℕ → ℝ := fun i => rhoFun (norm (vv (i % k' + a))) *
    azimInFan (vv (i % k' + a), vv ((i + 1) % k' + a)) E' with hfdef
  have peel : ∀ (g : ℕ → ℝ) (m : ℕ), 2 ≤ m →
      ∑ i ∈ Finset.range m, g i = g 0 + (∑ i ∈ Finset.range (m - 2), g (1 + i) + g (m - 1)) := by
    intro g m hm2
    have e1 : m = 1 + (m - 1) := by omega
    conv_lhs => rw [e1]
    rw [Finset.sum_range_add, Finset.sum_range_one]
    have e2 : m - 1 = (m - 2) + 1 := by omega
    rw [e2, Finset.sum_range_succ]
    try rw [show 1 + (m - 2) = m - 1 from by omega]
    try rw [show m - 2 + 1 = m - 1 from by omega]
  have hf0 : f 0 = rhoFun (norm (vv a)) * azim 0 (vv a) (vv (a + 1)) (vv b) := by
    show rhoFun (norm (vv (0 % k' + a))) *
        azimInFan (vv (0 % k' + a), vv ((0 + 1) % k' + a)) E'
      = rhoFun (norm (vv a)) * azim 0 (vv a) (vv (a + 1)) (vv b)
    rw [azimInFanVal_le4 hk'3 hp' hinj' hE' 0]
    simp only [Nat.zero_mod, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (show (1:ℕ) < k' by omega),
      Nat.mod_eq_of_lt (show k' - 1 < k' by omega),
      Nat.add_comm 1 a, Nat.add_comm (k' - 1) a,
      show a + (k' - 1) = a + k' - 1 from by omega, t1]
  have hfl : f (k' - 1) = rhoFun (norm (vv b)) * azim 0 (vv b) (vv a) (vv (b + k - 1)) := by
    show rhoFun (norm (vv ((k' - 1) % k' + a))) *
        azimInFan (vv ((k' - 1) % k' + a), vv ((k' - 1 + 1) % k' + a)) E'
      = rhoFun (norm (vv b)) * azim 0 (vv b) (vv a) (vv (b + k - 1))
    rw [azimInFanVal_le4 hk'3 hp' hinj' hE' (k' - 1),
      show (k' - 1) % k' = k' - 1 from Nat.mod_eq_of_lt (by omega),
      show (k' - 1 + 1) % k' = 0 from by rw [show k' - 1 + 1 = k' from by omega, Nat.mod_self],
      Nat.zero_add,
      show (k' - 1 + k' - 1) % k' = k' - 2 from by
        rw [show k' - 1 + k' - 1 = (k' - 2) + k' from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)],
      Nat.add_comm (k' - 1) a, show a + (k' - 1) = a + k' - 1 from by omega, t1,
      Nat.add_comm (k' - 2) a, show a + (k' - 2) = a + k' - 2 from by omega, t3]
  have hfi : ∀ t : ℕ, t < k' - 2 → f (1 + t) = G (a + 1 + t) := by
    intro t ht
    show rhoFun (norm (vv ((1 + t) % k' + a))) *
        azimInFan (vv ((1 + t) % k' + a), vv ((1 + t + 1) % k' + a)) E'
      = G (a + 1 + t)
    rw [azimInFanVal_le4 hk'3 hp' hinj' hE' (1 + t), hred1 t ht, hred2 t ht, hred4 t ht,
      hGdef (a + 1 + t),
      show 1 + t + a = a + 1 + t from by ring,
      show 2 + t + a = a + 1 + t + 1 from by omega,
      show a + 1 + t + k - 1 = a + t + k from by omega, vvAddK_le4 hper (a + t),
      Nat.add_comm t a]
  have hint : ∑ i ∈ Finset.range (k' - 2), f (1 + i)
      = ∑ i ∈ Finset.range (k' - 2), G (a + 1 + i) :=
    Finset.sum_congr rfl fun t ht => hfi t (Finset.mem_range.mp ht)
  rw [peel f k' (by omega), hf0, hfl, hint]

/-- The final assembly: `tausplit_le4`.  The two giants are this with the
branch flag `hj` dropped (it is not consumed). -/
private theorem tausplit_le4 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (vv vv' vv'' : ℕ → V3)
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
    (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
    (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hd : s.d ≤ d' + d'') :
    taustarV39 s' vv' + taustarV39 s'' vv'' ≤ taustarV39 s vv := by
  subst hvv'
  subst hvv''
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl
  obtain ⟨hpair, hd1, hd2, hds, hbm, hk4, hear⟩ := hsl
  -- master facts
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3s : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hdiag0 := hdiag
  obtain ⟨hdiagA, hdiagB, hdiagC⟩ := hdiag0
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hper : Periodic vv s.k := hBB.2.1
  have hdiag1 : ¬(p % s.k = q % s.k) := hdiagA
  have hdiag2 : ¬((p + 1) % s.k = q % s.k) := hdiagB
  have hdiag3 : ¬(p % s.k = (q + 1) % s.k) := hdiagC
  have hinjM : ∀ i j, i < s.k → j < s.k → i ≠ j → vv i ≠ vv j := fun i j hi hj hne he =>
    vvInjAux_p35 s vv hscs hBB i j hi hj hne he
  have hconv : ConvexLocalFan (Set.range vv)
      (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
      (Set.range fun i => (vv i, vv (i + 1))) := by
    rcases hBB.2.2.2 with hle | hfan
    · exact absurd hle (by omega)
    · exact hfan
  have hp'k : p % s.k < s.k := Nat.mod_lt _ hk0
  have hq'k : q % s.k < s.k := Nat.mod_lt _ hk0
  set E : Set (Set V3) := Set.range fun i => ({vv i, vv (i + 1)} : Set V3) with hEdef
  set FF : Set (V3 × V3) := Set.range fun i => (vv i, vv (i + 1)) with hFFdef
  set G : ℕ → ℝ := fun i => rhoFun (norm (vv i)) * azim 0 (vv i) (vv (i + 1))
    (vv (i + s.k - 1)) with hGdef
  have hGdefi : ∀ i, G i = rhoFun (norm (vv i)) * azim 0 (vv i) (vv (i + 1))
      (vv (i + s.k - 1)) := fun i => by rw [hGdef]
  have hGper : Periodic G s.k := by
    intro i
    show rhoFun (norm (vv (i + s.k))) * azim 0 (vv (i + s.k)) (vv (i + s.k + 1))
        (vv (i + s.k + s.k - 1))
      = rhoFun (norm (vv i)) * azim 0 (vv i) (vv (i + 1)) (vv (i + s.k - 1))
    rw [show i + s.k + s.k - 1 = i + s.k - 1 + s.k from by omega,
      vvAddK_le4 hper (i + s.k - 1),
      show i + s.k + 1 = i + 1 + s.k from by omega, vvAddK_le4 hper (i + 1),
      vvAddK_le4 hper i]
  -- window sizes and residue normalizations
  have hsk' : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by rw [← hs']; simp only [scsHalfSliceV39]
  have hsk'' : s''.k = (p + 1 + (s.k - q % s.k)) % s.k := by
    rw [← hs'']; simp only [scsHalfSliceV39]
  have e1' : (q % s.k + 1 + (s.k - p % s.k)) % s.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    have hL : (q % s.k + (1 + (s.k - p % s.k))) % s.k
        = (q % s.k % s.k + (1 + (s.k - p % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    have hR : (q + (1 + (s.k - p % s.k))) % s.k
        = (q % s.k + (1 + (s.k - p % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    rw [Nat.add_assoc, Nat.add_assoc, hL, hR, Nat.mod_mod]
  have e2' : (p % s.k + 1 + (s.k - q % s.k)) % s.k = (p + 1 + (s.k - q % s.k)) % s.k := by
    have hL : (p % s.k + (1 + (s.k - q % s.k))) % s.k
        = (p % s.k % s.k + (1 + (s.k - q % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    have hR : (p + (1 + (s.k - q % s.k))) % s.k
        = (p % s.k + (1 + (s.k - q % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    rw [Nat.add_assoc, Nat.add_assoc, hL, hR, Nat.mod_mod]
  have hsk'q : s'.k = (q % s.k + 1 + (s.k - p % s.k)) % s.k := by rw [hsk', ← e1']
  have hsk''q : s''.k = (p % s.k + 1 + (s.k - q % s.k)) % s.k := by rw [hsk'', ← e2']
  have hge' := SCS_K_PRIME_LE_GE_p35 s p q d' mkj hscs hdiag s' hs'.symm
  have hge'' := SCS_K_PRIME_LE_GE_p35 s q p d'' mkj hscs
    (⟨fun h => hdiag.1 h.symm, fun h => hdiag.2.2 h.symm, fun h => hdiag.2.1 h.symm⟩ :
      scsDiag s.k q p) s'' hs''.symm
  have hk'0 : 0 < s'.k := lt_of_le_of_lt (by norm_num) hge'.1
  have hk'k : s'.k < s.k := hge'.2.2
  have hk''0 : 0 < s''.k := lt_of_le_of_lt (by norm_num) hge''.1
  have hk''k : s''.k < s.k := hge''.2.2
  have hsumkk : s'.k + s''.k = s.k + 2 := by
    have hk6 : s.k ≤ 6 := hscs.2.2.1
    rcases (by omega : s.k = 4 ∨ s.k = 5 ∨ s.k = 6) with hk | hk | hk
    · rw [hk] at hdiagA hdiagB hdiagC hsk'q hsk''q ⊢
      have e1 : (p + 1) % 4 = (p % 4 + 1) % 4 := by simp [Nat.add_mod]
      have e2 : (q + 1) % 4 = (q % 4 + 1) % 4 := by simp [Nat.add_mod]
      rw [e1] at hdiagB
      rw [e2] at hdiagC
      have hb1 : p % 4 < 4 := Nat.mod_lt _ (by omega)
      have hb2 : q % 4 < 4 := Nat.mod_lt _ (by omega)
      interval_cases p % 4 <;> interval_cases q % 4 <;> omega
    · rw [hk] at hdiagA hdiagB hdiagC hsk'q hsk''q ⊢
      have e1 : (p + 1) % 5 = (p % 5 + 1) % 5 := by simp [Nat.add_mod]
      have e2 : (q + 1) % 5 = (q % 5 + 1) % 5 := by simp [Nat.add_mod]
      rw [e1] at hdiagB
      rw [e2] at hdiagC
      have hb1 : p % 5 < 5 := Nat.mod_lt _ (by omega)
      have hb2 : q % 5 < 5 := Nat.mod_lt _ (by omega)
      interval_cases p % 5 <;> interval_cases q % 5 <;> omega
    · rw [hk] at hdiagA hdiagB hdiagC hsk'q hsk''q ⊢
      have e1 : (p + 1) % 6 = (p % 6 + 1) % 6 := by simp [Nat.add_mod]
      have e2 : (q + 1) % 6 = (q % 6 + 1) % 6 := by simp [Nat.add_mod]
      rw [e1] at hdiagB
      rw [e2] at hdiagC
      have hb1 : p % 6 < 6 := Nat.mod_lt _ (by omega)
      have hb2 : q % 6 < 6 := Nat.mod_lt _ (by omega)
      interval_cases p % 6 <;> interval_cases q % 6 <;> omega
  have hcast : (Real.pi + sol0) * ((s'.k - 2 : ℕ) : ℝ)
      + (Real.pi + sol0) * ((s''.k - 2 : ℕ) : ℝ)
      = (Real.pi + sol0) * ((s.k - 2 : ℕ) : ℝ) := by
    have hn2 : s'.k - 2 + (s''.k - 2) = s.k - 2 := by omega
    rw [← mul_add, ← Nat.cast_add, hn2]
  -- window periodicity / injectivity / edge-dart sets
  have hper' : Periodic (fun i => vv (i % s'.k + p % s.k)) s'.k := perWin_le4 hk'0 hper
  have hinj' : ∀ i j : ℕ, i < s'.k → j < s'.k → i ≠ j →
      vv (i % s'.k + p % s.k) ≠ vv (j % s'.k + p % s.k) := fun i j hi hj hne he =>
    hne (injWin_le4 hk0 hk'0 hk'k hper hinjM hi hj he)
  have hper'' : Periodic (fun i => vv (i % s''.k + q % s.k)) s''.k := perWin_le4 hk''0 hper
  have hinj'' : ∀ i j : ℕ, i < s''.k → j < s''.k → i ≠ j →
      vv (i % s''.k + q % s.k) ≠ vv (j % s''.k + q % s.k) := fun i j hi hj hne he =>
    hne (injWin_le4 hk0 hk''0 hk''k hper hinjM hi hj he)
  set E' : Set (Set V3) := Set.range fun i =>
    ({vv (i % s'.k + p % s.k), vv ((i + 1) % s'.k + p % s.k)} : Set V3) with hE'def
  set FF' : Set (V3 × V3) := Set.range fun i =>
    (vv (i % s'.k + p % s.k), vv ((i + 1) % s'.k + p % s.k)) with hFF'def
  set E'' : Set (Set V3) := Set.range fun i =>
    ({vv (i % s''.k + q % s.k), vv ((i + 1) % s''.k + q % s.k)} : Set V3) with hE''def
  set FF'' : Set (V3 × V3) := Set.range fun i =>
    (vv (i % s''.k + q % s.k), vv ((i + 1) % s''.k + q % s.k)) with hFF''def
  -- the k' = 3 slot transports (slots3)
  have hslot' : s'.k = 3 → tau3 (vv (0 % s'.k + p % s.k)) (vv (1 % s'.k + p % s.k))
      (vv (2 % s'.k + p % s.k))
      = ∑ i ∈ Finset.range s'.k, rhoFun (norm (vv (i % s'.k + p % s.k))) *
          azimInFan (vv (i % s'.k + p % s.k), vv ((i + 1) % s'.k + p % s.k)) E'
        - (Real.pi + sol0) := by
    intro hk'3
    have hpq2 : (p % s.k + 2) % s.k = q % s.k := by
      have hk3' : (q % s.k + 1 + (s.k - p % s.k)) % s.k = 3 := by rw [← hsk'q, hk'3]
      rcases Nat.lt_or_ge (q % s.k + 1) (p % s.k) with hlt | hge
      · have hvlt : q % s.k + 1 + (s.k - p % s.k) < s.k := by omega
        rw [Nat.mod_eq_of_lt hvlt] at hk3'
        rw [show p % s.k + 2 = q % s.k + s.k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hq'k]
      · rcases Nat.eq_or_lt_of_le hge with heq | hlt
        · rw [show q % s.k + 1 + (s.k - p % s.k) = s.k from by omega, Nat.mod_self] at hk3'
          omega
        · have hv2 : q % s.k + 1 + (s.k - p % s.k)
              = (q % s.k + 1 - p % s.k) + s.k := by omega
          rw [hv2, Nat.add_mod_right] at hk3'
          rcases (by omega :
              q % s.k + 1 - p % s.k < s.k ∨ q % s.k + 1 - p % s.k = s.k) with hc | hc
          · rw [Nat.mod_eq_of_lt hc] at hk3'
            rw [show p % s.k + 2 = q % s.k from by omega,
              Nat.mod_eq_of_lt hq'k]
          · rw [hc, Nat.mod_self] at hk3'
            omega
    rw [hk'3, Nat.zero_mod, Nat.zero_add]
    refine slots3_le4 rfl hscs hBB hk3s hconv hper hinjM hMM hbm hdiag1 hdiag2 hpq2 E' ?_
    rw [hE'def]
    funext i
    rw [hk'3]
  have hslot'' : s''.k = 3 → tau3 (vv (0 % s''.k + q % s.k)) (vv (1 % s''.k + q % s.k))
      (vv (2 % s''.k + q % s.k))
      = ∑ i ∈ Finset.range s''.k, rhoFun (norm (vv (i % s''.k + q % s.k))) *
          azimInFan (vv (i % s''.k + q % s.k), vv ((i + 1) % s''.k + q % s.k)) E''
        - (Real.pi + sol0) := by
    intro hk''3
    have hpq2 : (q % s.k + 2) % s.k = p % s.k := by
      have hk3'' : (p % s.k + 1 + (s.k - q % s.k)) % s.k = 3 := by rw [← hsk''q, hk''3]
      rcases Nat.lt_or_ge (p % s.k + 1) (q % s.k) with hlt | hge
      · have hvlt : p % s.k + 1 + (s.k - q % s.k) < s.k := by omega
        rw [Nat.mod_eq_of_lt hvlt] at hk3''
        rw [show q % s.k + 2 = p % s.k + s.k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hp'k]
      · rcases Nat.eq_or_lt_of_le hge with heq | hlt
        · rw [show p % s.k + 1 + (s.k - q % s.k) = s.k from by omega, Nat.mod_self] at hk3''
          omega
        · have hv2 : p % s.k + 1 + (s.k - q % s.k)
              = (p % s.k + 1 - q % s.k) + s.k := by omega
          rw [hv2, Nat.add_mod_right] at hk3''
          rcases (by omega :
              p % s.k + 1 - q % s.k < s.k ∨ p % s.k + 1 - q % s.k = s.k) with hc | hc
          · rw [Nat.mod_eq_of_lt hc] at hk3''
            rw [show q % s.k + 2 = p % s.k from by omega,
              Nat.mod_eq_of_lt hp'k]
          · rw [hc, Nat.mod_self] at hk3''
            omega
    have hsyml : s.bm q p = s.bm p q := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsym, -, -, -, -, -, -, -, -⟩ := hscs
      exact (hsym q p).2.2.1
    rw [hk''3, Nat.zero_mod, Nat.zero_add]
    refine slots3_le4 rfl hscs hBB hk3s hconv hper hinjM hMM (by rw [hsyml]; exact hbm)
      (fun h => hdiag1 h.symm) (fun h => hdiag3 h.symm) hpq2 E'' ?_
    rw [hE''def]
    funext i
    rw [hk''3]
  -- the three halfTau instances
  have hm : taustarV39 s vv
      = ∑ i ∈ Finset.range s.k, rhoFun (norm (vv i)) * azimInFan (vv i, vv (i + 1)) E
        - (Real.pi + sol0) * ((s.k - 2 : ℕ) : ℝ) - dsvV39 s vv :=
    halfTau_le4 vv s.k E FF s rfl (le_of_lt hk3s) hper hinjM rfl rfl
      (fun h3 => absurd h3 (by omega))
  have hmsum : ∑ i ∈ Finset.range s.k, rhoFun (norm (vv i)) * azimInFan (vv i, vv (i + 1)) E
      = ∑ i ∈ Finset.range s.k, G i :=
    Finset.sum_congr rfl fun i _ => by
      rw [azimInFanVal_le4 (le_of_lt hk3s) hper hinjM rfl i]
  have hm' : taustarV39 s' (fun i => vv (i % s'.k + p % s.k))
      = ∑ i ∈ Finset.range s'.k, rhoFun (norm (vv (i % s'.k + p % s.k))) *
          azimInFan (vv (i % s'.k + p % s.k), vv ((i + 1) % s'.k + p % s.k)) E'
        - (Real.pi + sol0) * ((s'.k - 2 : ℕ) : ℝ)
        - dsvV39 s' (fun i => vv (i % s'.k + p % s.k)) :=
    halfTau_le4 (fun i => vv (i % s'.k + p % s.k)) s'.k E' FF' s' rfl hge'.1 hper' hinj'
      rfl rfl hslot'
  have hm'' : taustarV39 s'' (fun i => vv (i % s''.k + q % s.k))
      = ∑ i ∈ Finset.range s''.k, rhoFun (norm (vv (i % s''.k + q % s.k))) *
          azimInFan (vv (i % s''.k + q % s.k), vv ((i + 1) % s''.k + q % s.k)) E''
        - (Real.pi + sol0) * ((s''.k - 2 : ℕ) : ℝ)
        - dsvV39 s'' (fun i => vv (i % s''.k + q % s.k)) :=
    halfTau_le4 (fun i => vv (i % s''.k + q % s.k)) s''.k E'' FF'' s'' rfl hge''.1 hper''
      hinj'' rfl rfl hslot''
  -- the two diagonal corner splits
  have hduw4 : dist (vv (p % s.k)) (vv (q % s.k)) < 4 := distDiag4_le4 rfl hscs hMM hk0 hbm
  have h2pq : 2 ≤ dist (vv (p % s.k)) (vv (q % s.k)) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdiag2, -, -, -, -, -⟩ := hscs
    have h1 : (2 : ℝ) ≤ s.a (p % s.k) (q % s.k) :=
      hdiag2 (p % s.k) (q % s.k) ⟨hp'k, hq'k, fun h => hdiag1 h⟩
    have h2 := (hBB.2.2.1 (p % s.k) (q % s.k)).1
    exact h1.trans h2
  have hne2 : ¬((p % s.k) % s.k = (q % s.k) % s.k) := by
    intro h
    refine hdiag.1 ?_
    rwa [Nat.mod_eq_of_lt hp'k, Nat.mod_eq_of_lt hq'k] at h
  have hspl_p := splitDart_le4 rfl hscs hBB hk3s hconv hper hinjM hduw4 h2pq hne2
  have hduw4' : dist (vv (q % s.k)) (vv (p % s.k)) < 4 := by rw [dist_comm]; exact hduw4
  have h2qp : 2 ≤ dist (vv (q % s.k)) (vv (p % s.k)) := by rw [dist_comm]; exact h2pq
  have hne2' : ¬((q % s.k) % s.k = (p % s.k) % s.k) := by
    intro h
    refine hdiag1 ?_
    rw [Nat.mod_eq_of_lt hp'k, Nat.mod_eq_of_lt hq'k] at h
    exact h.symm
  have hspl_q := splitDart_le4 rfl hscs hBB hk3s hconv hper hinjM hduw4' h2qp hne2'
  have hGa' : G (p % s.k)
      = rhoFun (norm (vv (p % s.k))) * azim 0 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (q % s.k))
        + rhoFun (norm (vv (p % s.k))) * azim 0 (vv (p % s.k)) (vv (q % s.k))
          (vv (p % s.k + s.k - 1)) := by
    rw [hGdefi (p % s.k), hspl_p, mul_add]
  have hGb' : G (q % s.k)
      = rhoFun (norm (vv (q % s.k))) * azim 0 (vv (q % s.k)) (vv (q % s.k + 1)) (vv (p % s.k))
        + rhoFun (norm (vv (q % s.k))) * azim 0 (vv (q % s.k)) (vv (p % s.k))
          (vv (q % s.k + s.k - 1)) := by
    rw [hGdefi (q % s.k), hspl_q, mul_add]
  -- the window azimuth-sum identities
  have hw' := winSum_le4 vv G s.k (p % s.k) (q % s.k) s'.k E' hk0 (by omega) hp'k hper
    hinjM hge'.1 (by rw [hsk', ← e1']) hq'k (by rw [hE'def]) hGper hGdefi
  have hw'' := winSum_le4 vv G s.k (q % s.k) (p % s.k) s''.k E'' hk0 (by omega) hq'k hper
    hinjM hge''.1 (by rw [hsk'', ← e2']) hp'k (by rw [hE''def]) hGper hGdefi
  -- dsv superadditivity and the metric bookkeeping
  have hq2 := QKNVMLB2_p35 s s' s'' p q d' d'' mkj vv (fun i => vv (i % s'.k + p % s.k))
    (fun i => vv (i % s''.k + q % s.k)) hs' hs'' rfl rfl hMM hscs hdiag hsl0 hd
  have hS' : (∑ i ∈ Finset.range s'.k, rhoFun (norm (vv (i % s'.k + p % s.k))) *
        azimInFan (vv (i % s'.k + p % s.k), vv ((i + 1) % s'.k + p % s.k)) E')
      + (∑ i ∈ Finset.range s''.k, rhoFun (norm (vv (i % s''.k + q % s.k))) *
        azimInFan (vv (i % s''.k + q % s.k), vv ((i + 1) % s''.k + q % s.k)) E'')
      = ∑ i ∈ Finset.range s.k, G i := by
    have peelG : ∀ (c m : ℕ), 2 ≤ m →
        ∑ i ∈ Finset.range m, G (c + i)
          = G c + (∑ i ∈ Finset.range (m - 2), G (c + 1 + i) + G (c + (m - 1))) := by
      intro c m hm2
      have e1 : m = 1 + (m - 1) := by omega
      conv_lhs => rw [e1]
      rw [Finset.sum_range_add, Finset.sum_range_one, Nat.add_zero]
      have e2 : m - 1 = (m - 2) + 1 := by omega
      rw [e2, Finset.sum_range_succ, show 1 + (m - 2) = m - 1 from by omega, Nat.add_zero]
      rw [show m - 2 + 1 = m - 1 from by omega,
        Finset.sum_congr rfl fun x _ =>
          (by rw [← Nat.add_assoc] : G (c + (1 + x)) = G (c + 1 + x))]
    rcases Nat.lt_or_ge (p % s.k) (q % s.k) with hlt | hge
    · -- p-window is the short arc: k' = q' + 1 - p', k'' = p' + 1 + (s.k - q')
      have hv : q % s.k + 1 + (s.k - p % s.k) = (q % s.k + 1 - p % s.k) + s.k := by omega
      have hk'c : s'.k = q % s.k + 1 - p % s.k := by
        have h5 : s'.k = (q % s.k + 1 - p % s.k) % s.k := by
          rw [hsk', ← e1', hv, Nat.add_mod_right]
        have hdegen1 : ¬(p % s.k = 0 ∧ q % s.k = s.k - 1) := by
          rintro ⟨h1, h2⟩
          have hq1 : (q % s.k + 1) % s.k = (q + 1) % s.k := Nat.mod_add_mod q s.k 1
          have h9 : (q % s.k + 1) % s.k = 0 := by
            rw [h2, show s.k - 1 + 1 = s.k from by omega, Nat.mod_self]
          refine hdiagC ?_
          rw [h1]
          exact (hq1.symm.trans h9).symm
        have h6 : (q % s.k + 1 - p % s.k) % s.k = q % s.k + 1 - p % s.k :=
          Nat.mod_eq_of_lt (by omega)
        rw [h5, h6]
      have hgap1 : p % s.k + 2 ≤ q % s.k := by omega
      have hv2 : p % s.k + 1 + (s.k - q % s.k) < s.k := by omega
      have hk''c : s''.k = s.k + p % s.k + 1 - q % s.k := by
        rw [hsk'', ← e2', Nat.mod_eq_of_lt hv2]
        omega
      have arc1 : ∑ i ∈ Finset.range s'.k, G (p % s.k + i)
          = G (p % s.k) + (∑ t ∈ Finset.range (s'.k - 2), G (p % s.k + 1 + t)
            + G (q % s.k)) := by
        rw [hk'c, peelG (p % s.k) _ (by omega),
          show p % s.k + (q % s.k + 1 - p % s.k - 1) = q % s.k from by omega]
      have arc2 : ∑ j ∈ Finset.range s''.k, G (q % s.k + j)
          = G (q % s.k) + (∑ t ∈ Finset.range (s''.k - 2), G (q % s.k + 1 + t)
            + G (p % s.k)) := by
        rw [hk''c, peelG (q % s.k) _ (by omega),
          show q % s.k + (s.k + p % s.k + 1 - q % s.k - 1) = p % s.k + s.k from by omega,
          hGper (p % s.k)]
      have hspl := sumSplit_le4 G s.k (p % s.k) (q % s.k) hk0 hGper hlt hq'k
      rw [← hk'c, ← hk''c] at hspl
      rw [hw', hw'']
      linarith
    · -- q-window is the short arc: k'' = p' + 1 - q', k' = s.k + q' + 1 - p'
      rcases Nat.lt_or_ge (p % s.k) (q % s.k + 2) with h12 | h12
      · -- p' = q' + 1 forces k' = 0, contradicting 3 ≤ k'
        have hp12 : p % s.k = q % s.k + 1 := by omega
        rw [show q % s.k + 1 + (s.k - p % s.k) = s.k from by omega,
          Nat.mod_self] at hsk'q
        exact absurd hsk'q.symm (by have hk3 := hge'.1; omega)
      · have hv : q % s.k + 1 + (s.k - p % s.k) < s.k := by omega
        have hk'c : s'.k = s.k + q % s.k + 1 - p % s.k := by
          rw [hsk', ← e1', Nat.mod_eq_of_lt hv]
          omega
        have hp20 : ¬(p % s.k = s.k - 1 ∧ q % s.k = 0) := by
          rintro ⟨h1, h2⟩
          have h3 : s''.k = (p % s.k + 1 + (s.k - q % s.k)) % s.k := hsk''q
          rw [show p % s.k + 1 + (s.k - q % s.k) = s.k + s.k from by omega,
            Nat.add_mod_right, Nat.mod_self] at h3
          omega
        have hdegen2 : ¬(q % s.k = 0 ∧ p % s.k = s.k - 1) := by
          rintro ⟨h2, h1⟩
          have hp1 : (p % s.k + 1) % s.k = 0 := by
            rw [h1, show s.k - 1 + 1 = s.k from by omega, Nat.mod_self]
          have hp1' : (p % s.k + 1) % s.k = (p + 1) % s.k := Nat.mod_add_mod p s.k 1
          refine hdiagB ?_
          rw [← hp1', hp1]
          exact h2.symm
        have hlt2k : p % s.k + 1 - q % s.k < s.k := by omega
        have hv2 : p % s.k + 1 + (s.k - q % s.k) = (p % s.k + 1 - q % s.k) + s.k := by omega
        have hk''c : s''.k = p % s.k + 1 - q % s.k := by
          rw [hsk'', ← e2', hv2, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2k]
        have arc1 : ∑ j ∈ Finset.range s''.k, G (q % s.k + j)
            = G (q % s.k) + (∑ t ∈ Finset.range (s''.k - 2), G (q % s.k + 1 + t)
              + G (p % s.k)) := by
          rw [hk''c, peelG (q % s.k) _ (by omega),
            show q % s.k + (p % s.k + 1 - q % s.k - 1) = p % s.k from by omega]
        have arc2 : ∑ i ∈ Finset.range s'.k, G (p % s.k + i)
            = G (p % s.k) + (∑ t ∈ Finset.range (s'.k - 2), G (p % s.k + 1 + t)
              + G (q % s.k)) := by
          rw [hk'c, peelG (p % s.k) _ (by omega),
            show p % s.k + (s.k + q % s.k + 1 - p % s.k - 1) = q % s.k + s.k from by omega,
            hGper (q % s.k)]
        have hspl := sumSplit_le4 G s.k (q % s.k) (p % s.k) hk0 hGper
          (by omega) hp'k
        rw [← hk''c, ← hk'c] at hspl
        rw [hw', hw'']
        linarith
  -- the giants
  rw [hm', hm'', hm, hmsum]
  linarith

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
  exact tausplit_le4 s s' s'' p q d' d'' mkj vv vv' vv'' hs' hs'' hvv' hvv''
      hMM hscs hdiag hsl hd
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
  exact tausplit_le4 s s' s'' p q d' d'' mkj vv vv' vv'' hs' hs'' hvv' hvv''
      hMM hscs hdiag hsl hd
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

/-! ## lkgrqui-eq4-w3 (2026-10-28): 3-window face determinations and the
      corrected `SUM_AZIM_EQ_ANGLE_EQ4` twin.  The frozen root
      `SUM_AZIM_EQ_ANGLE_EQ4_p35` above is unprovable as stated (missing
      `IsHypE_p35` carrier; see the DISCHARGES note there); this wave proves
      the full content under the corrected statement. -/

/-- Peel an additive `c` out of a residue equality of small indices. -/
private theorem modPeel_p35 {k a b c : ℕ} (ha : a < k) (hb : b < k)
    (h : (a + c) % k = (b + c) % k) : a = b := by
  have e1 : (a % k + c % k) % k = (a + c) % k := by rw [← Nat.add_mod]
  have e2 : (b % k + c % k) % k = (b + c) % k := by rw [← Nat.add_mod]
  have h1 : (a % k + c % k) % k = (b % k + c % k) % k := by rw [e1, e2, h]
  have h2 := modAddCancel_p35 (k := k) (a := a % k) (b := b % k) (c := c % k) h1
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at h2
  exact h2

/-- The out-dart of a 3-window face vertex (epsilon determined by window
injectivity): the slice-face specialization of HOL `DETER_RHO_NODE`
(local_lemmas.hl:3093) over the `F_PRIME_EQ_F_vv_p35` face description. -/
private theorem face3Rho_p35 {vv : ℕ → V3} {k p : ℕ} {Ff : Set (V3 × V3)}
    (hk0 : 0 < k) (hk3 : 3 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFf : Set.range (fun i => (vv (i % 3 + p), vv ((i + 1) % 3 + p))) = Ff)
    (i : ℕ) (hi : i < 3) :
    rhoNode1 Ff (vv (p + i)) = vv ((i + 1) % 3 + p) := by
  have hmem : (vv (p + i), vv ((i + 1) % 3 + p)) ∈ Ff := by
    rw [← hFf]
    refine Set.mem_range.mpr ⟨i, ?_⟩
    rw [Nat.mod_eq_of_lt hi, Nat.add_comm i p]
  refine epsFixed_p35 hmem ?_
  intro y hy
  rw [← hFf] at hy
  obtain ⟨j, hj⟩ := hy
  have h1 : vv (j % 3 + p) = vv (p + i) := congrArg Prod.fst hj
  have h2 : vv ((j + 1) % 3 + p) = y := congrArg Prod.snd hj
  have hmod : (j % 3 + p) % k = (p + i) % k := vvModEq_p35 hk0 hper hinj h1
  rw [Nat.add_comm p i] at hmod
  have hpeel : j % 3 = i :=
    modPeel_p35 (show j % 3 < k by omega) (show i < k by omega) hmod
  have e3 : (j + 1) % 3 = (i + 1) % 3 := by
    rw [Nat.add_mod, Nat.add_mod, hpeel, Nat.mod_eq_of_lt (show (1:ℕ) < 3 by omega),
      Nat.mod_eq_of_lt hi]
  rw [← h2, e3]

/-- The in-dart of a 3-window face vertex (mirror of `face3Rho_p35`,
HOL `DETER_IVS_RHO_NODE` specialization). -/
private theorem face3Ivs_p35 {vv : ℕ → V3} {k p : ℕ} {Ff : Set (V3 × V3)}
    (hk0 : 0 < k) (hk3 : 3 < k) (hper : Periodic vv k)
    (hinj : ∀ i j, i < k → j < k → i ≠ j → vv i ≠ vv j)
    (hFf : Set.range (fun i => (vv (i % 3 + p), vv ((i + 1) % 3 + p))) = Ff)
    (i : ℕ) (hi : i < 3) :
    ivsRhoNode1 Ff (vv (p + i)) = vv ((i + 2) % 3 + p) := by
  have hi2 : (i + 2) % 3 < 3 := Nat.mod_lt _ (by omega)
  have e7 : ((i + 2) % 3 + 1) % 3 = i := by interval_cases i <;> norm_num
  have hmem : (vv ((i + 2) % 3 + p), vv (p + i)) ∈ Ff := by
    rw [← hFf]
    refine Set.mem_range.mpr ⟨(i + 2) % 3, ?_⟩
    rw [show ((i + 2) % 3) % 3 = (i + 2) % 3 from Nat.mod_eq_of_lt hi2,
      Nat.add_comm ((i + 2) % 3) p, e7, Nat.add_comm i p]
  refine epsFixed_p35 hmem ?_
  intro c hc
  rw [← hFf] at hc
  obtain ⟨j, hj⟩ := hc
  have h1 : vv (j % 3 + p) = c := congrArg Prod.fst hj
  have h2 : vv ((j + 1) % 3 + p) = vv (p + i) := congrArg Prod.snd hj
  have hmod : ((j + 1) % 3 + p) % k = (p + i) % k := vvModEq_p35 hk0 hper hinj h2
  rw [Nat.add_comm p i] at hmod
  have hpeel : (j + 1) % 3 = i :=
    modPeel_p35 (show (j + 1) % 3 < k by omega) (show i < k by omega) hmod
  have hjm : j % 3 = (i + 2) % 3 := by interval_cases i <;> omega
  rw [← h1, hjm]

/-- Core of the corrected HOL `SUM_AZIM_EQ_ANGLE_EQ4` (QKNVMLB.hl:8445)
rendering: everything except the face re-labelling, which enters as the
hypothesis `hF` (discharged below by `F_PRIME_EQ_F_vv_p35`). -/
private theorem eq4Core_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
    (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
    (hs' : scsHalfSliceV39 s p q d' mkj = s')
    (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
    (hsl : isScsSliceV39 s s' s'' p q) (hk'3 : s'.k = 3)
    (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
    (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hnorm : norm (u - w) ≤ cstab)
    (hF : Set.range (fun i => (vv (i % 3 + p % s.k), vv ((i + 1) % 3 + p % s.k))) =
      HS.face (u, rhoNode1 FF u)) :
    tau3 (vv (0 % 3 + p % s.k)) (vv (1 % 3 + p % s.k)) (vv (2 % 3 + p % s.k)) =
      setSum {i | i < 3}
          (fun i => rhoFun (norm (vv (i + p % s.k))) *
            interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
        (Real.pi + sol0) := by
  -- numerics
  have hk0 : 0 < s.k := by have := hscs.2.1; omega
  have hk3s : 3 < s.k := SCS_K_PRIME_CASE_3_p35 s p q hscs hdiag
  have hq'k : q % s.k < s.k := Nat.mod_lt q hk0
  have hp'k : p % s.k < s.k := Nat.mod_lt p hk0
  have hBB : BBsV39 s vv := hMM.1.1.1
  have hper : Periodic vv s.k := hBB.2.1
  have hinj : ∀ i j, i < s.k → j < s.k → i ≠ j → vv i ≠ vv j := fun i j hi hj hne he =>
    vvInjAux_p35 s vv hscs hBB i j hi hj hne he
  have hk'3 : s'.k = 3 := hk'3
  obtain ⟨hdiagA, hdiagB, hdiagC⟩ := hdiag
  have hsl0 := hsl
  simp only [isScsSliceV39] at hsl0
  obtain ⟨-, -, -, -, hbm4, -, -⟩ := hsl0
  -- the k' = 3 residue identity (window closes at the diagonal)
  have hsk' : s'.k = (q + 1 + (s.k - p % s.k)) % s.k := by
    rw [← hs']; simp only [scsHalfSliceV39]
  have e1' : (q % s.k + 1 + (s.k - p % s.k)) % s.k
      = (q + 1 + (s.k - p % s.k)) % s.k := by
    have hL : (q % s.k + (1 + (s.k - p % s.k))) % s.k
        = (q % s.k % s.k + (1 + (s.k - p % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    have hR : (q + (1 + (s.k - p % s.k))) % s.k
        = (q % s.k + (1 + (s.k - p % s.k)) % s.k) % s.k := Nat.add_mod _ _ _
    rw [Nat.add_assoc, Nat.add_assoc, hL, hR, Nat.mod_mod]
  have hsk'q : s'.k = (q % s.k + 1 + (s.k - p % s.k)) % s.k := by rw [hsk', ← e1']
  have hpq2 : (p % s.k + 2) % s.k = q % s.k := by
    have hk3' : (q % s.k + 1 + (s.k - p % s.k)) % s.k = 3 := by rw [← hsk'q, hk'3]
    rcases Nat.lt_or_ge (q % s.k + 1) (p % s.k) with hlt | hge
    · have hvlt : q % s.k + 1 + (s.k - p % s.k) < s.k := by omega
      rw [Nat.mod_eq_of_lt hvlt] at hk3'
      rw [show p % s.k + 2 = q % s.k + s.k from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hq'k]
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · rw [show q % s.k + 1 + (s.k - p % s.k) = s.k from by omega, Nat.mod_self] at hk3'
        omega
      · have hv2 : q % s.k + 1 + (s.k - p % s.k)
            = (q % s.k + 1 - p % s.k) + s.k := by omega
        rw [hv2, Nat.add_mod_right] at hk3'
        rcases (by omega :
            q % s.k + 1 - p % s.k < s.k ∨ q % s.k + 1 - p % s.k = s.k) with hc | hc
        · rw [Nat.mod_eq_of_lt hc] at hk3'
          rw [show p % s.k + 2 = q % s.k from by omega,
            Nat.mod_eq_of_lt hq'k]
        · rw [hc, Nat.mod_self] at hk3'
          omega
  -- window-slot normalizations
  have vmod0 : vv (0 % 3 + p % s.k) = vv (p % s.k) := by rw [Nat.zero_mod, Nat.zero_add]
  have vmod1 : vv (1 % 3 + p % s.k) = vv (p % s.k + 1) := by
    rw [show (1:ℕ) % 3 = 1 from rfl, Nat.add_comm]
  have vmod2 : vv (2 % 3 + p % s.k) = vv (p % s.k + 2) := by
    rw [show (2:ℕ) % 3 = 2 from rfl, Nat.add_comm]
  have vwt1 : vv ((0 + 1) % 3 + p % s.k) = vv (p % s.k + 1) := by
    rw [show ((0:ℕ) + 1) % 3 = 1 from rfl, Nat.add_comm]
  have vwt2 : vv ((1 + 1) % 3 + p % s.k) = vv (p % s.k + 2) := by
    rw [show ((1:ℕ) + 1) % 3 = 2 from rfl, Nat.add_comm]
  have vwt3 : vv ((2 + 1) % 3 + p % s.k) = vv (p % s.k) := by
    rw [show ((2:ℕ) + 1) % 3 = 0 from rfl, Nat.zero_add]
  have vwt4 : vv ((0 + 3 - 1) % 3 + p % s.k) = vv (p % s.k + 2) := by
    rw [show ((0:ℕ) + 3 - 1) % 3 = 2 from rfl, Nat.add_comm]
  have vwt5 : vv ((1 + 3 - 1) % 3 + p % s.k) = vv (p % s.k) := by
    rw [show ((1:ℕ) + 3 - 1) % 3 = 0 from rfl, Nat.zero_add]
  have vwt6 : vv ((2 + 3 - 1) % 3 + p % s.k) = vv (p % s.k + 1) := by
    rw [show ((2:ℕ) + 3 - 1) % 3 = 1 from rfl, Nat.add_comm]
  have vwt7 : vv ((1 + 2) % 3 + p % s.k) = vv (p % s.k) := by
    rw [show ((1:ℕ) + 2) % 3 = 0 from rfl, Nat.zero_add]
  have vwt8 : vv ((2 + 2) % 3 + p % s.k) = vv (p % s.k + 1) := by
    rw [show ((2:ℕ) + 2) % 3 = 1 from rfl, Nat.add_comm]
  -- the full fan
  have hconv : ConvexLocalFan (Set.range vv)
      (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
      (Set.range fun i => (vv i, vv (i + 1))) := by
    rcases hBB.2.2.2 with hle | hfan0
    · exact absurd hle (by omega)
    · exact hfan0
  -- window periodicity / injectivity
  have hwper : Periodic (fun i => vv (i % 3 + p % s.k)) 3 := perWin_le4 (by norm_num) hper
  have hwinj : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j →
      vv (i % 3 + p % s.k) ≠ vv (j % 3 + p % s.k) := fun i j hi hj hne he =>
    hne (injWin_le4 hk0 (by norm_num) hk3s hper hinj hi hj he)
  -- the window edge set and the slots3 transport
  set E'w : Set (Set V3) :=
    Set.range fun i => ({vv (i % 3 + p % s.k), vv ((i + 1) % 3 + p % s.k)} : Set V3) with hEw
  have hslot := slots3_le4 rfl hscs hBB hk3s hconv hper hinj hMM hbm4 hdiagA hdiagB hpq2 E'w
    hEw.symm
  -- window azimuth values in three-point form
  have hav0 : azimInFan (vv (p % s.k), vv (p % s.k + 1)) E'w
      = azim 0 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (p % s.k + 2)) := by
    have h0 := azimInFanVal_le4 (vv := fun t => vv (t % 3 + p % s.k)) (E := E'w) (k := 3)
      (by norm_num) hwper hwinj hEw.symm 0
    rw [vmod0, vwt1, vwt4] at h0
    exact h0
  have hav1 : azimInFan (vv (p % s.k + 1), vv (p % s.k + 2)) E'w
      = azim 0 (vv (p % s.k + 1)) (vv (p % s.k + 2)) (vv (p % s.k)) := by
    have h1 := azimInFanVal_le4 (vv := fun t => vv (t % 3 + p % s.k)) (E := E'w) (k := 3)
      (by norm_num) hwper hwinj hEw.symm 1
    rw [vmod1, vwt2, vwt5] at h1
    exact h1
  have hav2 : azimInFan (vv (p % s.k + 2), vv (p % s.k)) E'w
      = azim 0 (vv (p % s.k + 2)) (vv (p % s.k)) (vv (p % s.k + 1)) := by
    have h2 := azimInFanVal_le4 (vv := fun t => vv (t % 3 + p % s.k)) (E := E'w) (k := 3)
      (by norm_num) hwper hwinj hEw.symm 2
    rw [vmod2, vwt3, vwt6] at h2
    exact h2
  -- the interior angles at the three window vertices of the face
  have hia0 : interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k))
      = azim 0 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (p % s.k + 2)) := by
    show azim 0 (vv (p % s.k))
      (rhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k)))
      (ivsRhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k))) = _
    rw [show vv (p % s.k) = vv (p % s.k + 0) from by rw [Nat.add_zero],
      face3Rho_p35 hk0 hk3s hper hinj hF 0 (by omega),
      face3Ivs_p35 hk0 hk3s hper hinj hF 0 (by omega), Nat.add_zero, vwt1, vwt4]
  have hia1 : interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 1))
      = azim 0 (vv (p % s.k + 1)) (vv (p % s.k + 2)) (vv (p % s.k)) := by
    show azim 0 (vv (p % s.k + 1))
      (rhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 1)))
      (ivsRhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 1))) = _
    rw [face3Rho_p35 hk0 hk3s hper hinj hF 1 (by omega),
      face3Ivs_p35 hk0 hk3s hper hinj hF 1 (by omega), vwt2, vwt7]
  have hia2 : interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 2))
      = azim 0 (vv (p % s.k + 2)) (vv (p % s.k)) (vv (p % s.k + 1)) := by
    show azim 0 (vv (p % s.k + 2))
      (rhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 2)))
      (ivsRhoNode1 (HS.face (u, rhoNode1 FF u)) (vv (p % s.k + 2))) = _
    rw [face3Rho_p35 hk0 hk3s hper hinj hF 2 (by omega),
      face3Ivs_p35 hk0 hk3s hper hinj hF 2 (by omega), vwt3, vwt8]
  -- orbit normalizations
  have horbit := vvOrbit_p35 hk0 hper hinj hFF u (p % s.k) hp
  have ho0 : (rhoNode1 FF)^[0] u = vv (p % s.k) := by rw [horbit 0, Nat.zero_add]
  have ho1 : (rhoNode1 FF)^[1] u = vv (p % s.k + 1) := by rw [horbit 1, Nat.add_comm]
  have ho2 : (rhoNode1 FF)^[2] u = vv (p % s.k + 2) := by rw [horbit 2, Nat.add_comm]
  -- left side in three-point form
  have eL : tau3 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (p % s.k + 2))
      = rhoFun (norm (vv (p % s.k))) * azim 0 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (p % s.k + 2))
        + rhoFun (norm (vv (p % s.k + 1))) * azim 0 (vv (p % s.k + 1)) (vv (p % s.k + 2)) (vv (p % s.k))
        + rhoFun (norm (vv (p % s.k + 2))) * azim 0 (vv (p % s.k + 2)) (vv (p % s.k)) (vv (p % s.k + 1))
        - (Real.pi + sol0) := by
    have h1 := slots3_le4 rfl hscs hBB hk3s hconv hper hinj hMM hbm4 hdiagA hdiagB hpq2 E'w
      hEw.symm
    rw [SUM_NUMSEG2_p35, vmod0, vmod1, vmod2, hav0, hav1, hav2] at h1
    exact h1
  -- right side in three-point form
  have eR : setSum {i | i < 3}
          (fun i => rhoFun (norm (vv (i + p % s.k))) *
            interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u))
      - (Real.pi + sol0)
      = rhoFun (norm (vv (p % s.k))) * azim 0 (vv (p % s.k)) (vv (p % s.k + 1)) (vv (p % s.k + 2))
        + rhoFun (norm (vv (p % s.k + 1))) * azim 0 (vv (p % s.k + 1)) (vv (p % s.k + 2)) (vv (p % s.k))
        + rhoFun (norm (vv (p % s.k + 2))) * azim 0 (vv (p % s.k + 2)) (vv (p % s.k)) (vv (p % s.k + 1))
        - (Real.pi + sol0) := by
    rw [setSum_Iio_p35, SUM_NUMSEG2_p35, ho0, ho1, ho2, Nat.zero_add,
      Nat.add_comm 1 (p % s.k), Nat.add_comm 2 (p % s.k), hia0, hia1, hia2]
  rw [vmod0, vmod1, vmod2]
  exact eL.trans eR.symm
  -- DISCHARGES (lkgrqui-eq4-w3 2026-10-28): source 8445-9059 with the face
  -- re-labelling factored out as `hF`.  Route: slots3_le4 (the tau3 →
  -- window-azimInFan transport, the k' = 3 slot of the HOL NUMSEG_2/
  -- SUM_NUMSEG2 decomposition) + azimInFanVal_le4 (the two-point-neighbour
  -- specialization of CONVEX_LOFA_IMP_INANGLE_EQ_AZIM) + face3Rho/face3Ivs
  -- (the DETER_RHO_NODE/IVS pair on the `hF` face) + vvOrbit_p35 (VV_SUC_EQ_
  -- RHO_NODE) + setSum_Iio_p35/SUM_NUMSEG2_p35 re-indexing.

/-- Corrected rendering of HOL `SUM_AZIM_EQ_ANGLE_EQ4` (QKNVMLB.hl:8445):
identical to `SUM_AZIM_EQ_ANGLE_EQ4_p35` plus the carrier hypothesis
`hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS`.  The frozen root dropped exactly this
hypothesis when abstracting the canonical hypermap
`hypermap (HYP (vec 0, V, E UNION {{u, w}}))`; without it the statement has
countermodels (HS := the full-fan hypermap `hypermapOfFan 0 V E` satisfies
`hfan`, while `HS.face (u, rhoNode1 FF u)` is the full dart cycle, on which
the goal's RHS interior angles differ from the slice-face split).  With the
ruling that adds `hHS` to the frozen root, closing it is
`exact SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 ...` on the unchanged statement body. -/
theorem SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
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
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
    (hfan : ConvexLocalFan
      (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
      (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
      (HS.face (u, rhoNode1 FF u))) :
    tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
      setSum {i | i < k'}
          (fun i => rhoFun (norm (vv (i + p % k))) *
            interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
        (Real.pi + sol0) := by
  subst hk'
  subst hk
  refine eq4Core_p35 s s' s'' p q d' d'' mkj u w V E FF vv HS hs' hMM hscs hdiag hsl
    hk's' hp hq hV hE hFF hnorm ?_
  exact F_PRIME_EQ_F_vv_p35 s s' s'' p q d' d'' mkj s.k 3 u w V E FF vv HS hs' hs''
    hk's' rfl hp hq hV hE hFF hnorm hscs hdiag hMM.1.1.1 hHS
  -- DISCHARGES (lkgrqui-eq4-w3 2026-10-28): composes eq4Core_p35 with the
  -- face re-labelling F_PRIME_EQ_F_vv_p35 under the IsHypE_p35 carrier —
  -- the faithful rendering of the HOL canonical hypermap
  -- `hypermap (HYP (vec 0, V, E UNION {{u, w}}))`.


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
    (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
    (hfan : ConvexLocalFan
      (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
      (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
      (HS.face (u, rhoNode1 FF u))) :
    tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
      setSum {i | i < k'}
          (fun i => rhoFun (norm (vv (i + p % k))) *
            interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
        (Real.pi + sol0) := by
  exact SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 s s' s'' p q d' d'' mkj k k' u w V E FF
    vv vv' vv'' HS hk' hs' hs'' hvv' hvv'' hMM hscs hdiag hsl hk's' hk hp hq hV hE
    hFF hnorm hHS hfan
  -- DISCHARGES: source 8445-9059; k' = 3: tau3 decomposition via
  -- SUM_NUMSEG2_p35/NUMSEG_2_p35 + V/E/F_PRIME_EQ_*_p35 +
  -- SCS_HALF_SLICE_IS_A_SCS_p35 + the local-fan azimuth sum identity
  -- (SUM_AZIM over the diag-closed slice face).
  -- lkgrqui-eq4-w3 2026-10-28: this frozen statement is NOT provable as
  -- stated. The only hypothesis constraining `HS` is `hfan`, and
  -- `HS := hypermapOfFan 0 V E` (the FULL-fan hypermap, Fan.lean:1169)
  -- satisfies it: then `vPrime_p3 V (HS.face (u, rhoNode1 FF u)) = V` and
  -- `ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)) = E` (the diag
  -- `{u, w}` is realized by no full-fan dart), so `hfan` reduces to the
  -- full-fan `ConvexLocalFan V E FF` from `hMM`, while
  -- `HS.face (u, rhoNode1 FF u)` is the full dart cycle on which the RHS
  -- interior angles differ from the slice-face split (e.g. the i = 0 term
  -- is `azim 0 u u1 (full-fan pred of u)`, strictly larger than the slice
  -- term `azim 0 u u1 w` by the diag split). HOL is safe because it pins the
  -- hypermap to the canonical `hypermap (HYP (vec 0, V, E UNION {{u, w}}))`;
  -- the Lean freezing abstracted `HS` and dropped exactly that carrier
  -- (`IsHypE_p35 V (E ∪ {{u, w}}) HS`) that its own DISCHARGES recipe
  -- (V/E/F_PRIME_EQ_*_p35) consumes. Closing needs a statement ruling: add
  -- that one hypothesis, then `exact SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 ...`
  -- (below, fully proved, standard three).

end Kepler.Text

-- lkgrqui-eq4-w3 axiom audit (mandate premise ① + ladder; full names,
-- outside the namespace).  Expected standard three for every entry.
#print axioms Kepler.Text.SUM_AZIM_EQ_ANGLE_EQ4_p35
#print axioms Kepler.Text.SUM_AZIM_EQ_ANGLE_EQ4_HS_p35
#print axioms Kepler.Text.eq4Core_p35
#print axioms Kepler.Text.face3Rho_p35
#print axioms Kepler.Text.face3Ivs_p35
#print axioms Kepler.Text.modPeel_p35
#print axioms Kepler.Text.QKNVMLB3_LE4_p35
#print axioms Kepler.Text.QKNVMLB1_LE4F_p35
#print axioms Kepler.Text.QKNVMLB1_EQ4F_p35
#print axioms Kepler.Text.SUM_AZIM_EQ_ANGLE_LE4_p35
#print axioms Kepler.Text.tausplit_le4
#print axioms Kepler.Text.slots3_le4
#print axioms Kepler.Text.F_PRIME_EQ_F_vv_p35
#print axioms Kepler.Text.V_PRIME_EQ_V_vv_p35
#print axioms Kepler.Text.E_PRIME_EQ_E_vv_p35
#print axioms Kepler.Text.TRIO_V_OF_FACE_p35
#print axioms Kepler.Text.TRIO_E_OF_FACE_p35
#print axioms Kepler.Text.TECOXBMv2_p35
#print axioms Kepler.Text.pmPlaneCrowding_p35
#print axioms Kepler.Text.EJRCFJD_p35
#print axioms Kepler.Text.SCS_HALF_SLICE_IS_A_SCS_p35
#print axioms Kepler.Text.VV_INJ_p35
-- sorry-slot census (expected 5 = the five LA35 roots, unchanged)
