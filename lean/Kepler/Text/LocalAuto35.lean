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
