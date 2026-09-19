/-
Hexagons: remaining conclusions from the appendix to the Local Fan chapter.

HOL source: Flyspeck `hexagons.hl` (Hexagons module, 2012-04-01, 2171 lines;
consumes `main_nonlinear_terminal_v11`). This is the detailed port of the
`is_scs_v39` verifications for the terminal systems, the diag-stabilisation
kit around `scs_6I1`, the `AQICLXA`/`FZIOTEF`/`FUNOUYH` slicing arrows, and
the master `OEHDBEN` arrow breaking the hexagon into ears.

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(v i,v j)` <-> `dist (v i) (v j)`.
- The `scs_v39` record and all toolkit defs (`is_scs_v39`, `scs_basic_v39`,
  `scs_arrow_v39`, `scs_diag`, `scs_stab_diag_v39`, `scs_half_slice_v39`,
  `scs_prop_equ_v39`, `psort`, `funlist_v39`, `cs_adj`, `mk_unadorned_v39`,
  `MMs_v39`, `scs_M`) are already ported in `Kepler.Text.LocalAuto1`
  (camelCase); the concrete systems `scs_6I1`..`scs_4M6'` likewise. This file
  adds the one missing system `scs_5M3` (hexagons.hl:153) as `scs5M3`.
- `sqrt8` <-> `Real.sqrt 8`; `#1.26` <-> `h0`; `#3.01` <-> `cstab`;
  `#0.616` and other decimal literals are exact literals; `&6` <-> `(6:ℝ)`.
- HOL `SUC n` <-> `n + 1`; `{i | P}` <-> setOf; `psort (k) (i,j)` <-
  `psort k (i, j)`; `CARD` <-> `Set.ncard`/`Nat.card` as convenient.
- Ledger (W-waves update): all 10 `SCS_*_IS_SCS`, `SCS_M_5M2`, `DIAD_PSORT_IMP_DIAD`,
  `DIAG_SCS_M_EQ`, `STAB_6I1_SCS`, `EXPAND_STAB_DIAG`, `EQ_DIAG_STAB_6I1_02/03`,
  `SET_EQ_DIAG_STAB_6I1_02/03`, `SET_EQ_DIAG_STAB_6I1`, `OEHDBEN_PRIME`,
  `OEHDBEN` are fully proved (5 `is_scs_adj` systems via `Kepler.Text.LocalAuto22`'s
  W5 kit, 5 funlist systems + `STAB_6I1_SCS` by direct residue case work here).
  Remaining `sorry`s (7): `AQICLXA_SLICE`/`FUNOUYH_SLICE` (NEED
   `LocalAuto1.LKGRQUI_concl`), `AQICLXA`/`FZIOTEF` (NEED `YXIONXL3_concl` +
   `PROP_EQU_IS_SCS`), and the three `main_nonlinear_terminal_v11` implications
   (NEED the mnt11 lane: RRCWNSJ/JCYFMRP/JLXFDMJ/MXQTIED, all LocalAuto1).
- Fill-wave 2026-09-19 re-scan: all 7 blockers still open. `LKGRQUI_concl`
  (LocalAuto1:950), `YXIONXL3_concl` (LocalAuto1:945), `RRCWNSJ_concl`
  (:1334), `JCYFMRP_concl` (:1342), `JLXFDMJ_concl` (:1371), `MXQTIED_concl`
  (:1098), `PEDSLGV2_concl` (:1397) all still `sorry`; the proved
  `LocalAuto12.YXIONXL3`/`PROP_EQU_IS_SCS` twins only help downstream of
  `AQICLXA_SLICE`/`FUNOUYH_SLICE`; `main_nonlinear_terminal_v11` is an opaque
  `def ... := sorry` (LocalAuto1:793), so the three mnt11 implications cannot
  extract content from the hypothesis. `MMS_IMP_BBS_p28`/`CHANGE_W_IN_BBS_MOD_
  IS_SCS_p28` (LocalAuto28, proved) are auxiliary only. No fills this round;
  statements and NEEDS notes unchanged.
- No `native_decide` anywhere; `sorry` bodies carry `-- NEEDS:` markers
  naming the missing HOL inputs (the big `SCS_TAC` rewrites).
- Same-wave files LocalAuto19/21-27 are NOT imported; nothing from them is
  needed, so no `_p20` copies of foreign material were required.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto22
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Preliminaries (hexagons.hl:77-176) -/

/-- HOL `PSORT_5_EXPLICIT` (hexagons.hl:119): the full 5x5 `psort 5` table
plus the extra 4/3-row entries. -/
theorem PSORT_5_EXPLICIT :
    psort 5 (0, 0) = (0, 0) ∧ psort 5 (1, 1) = (1, 1) ∧ psort 5 (2, 2) = (2, 2) ∧
    psort 5 (3, 3) = (3, 3) ∧ psort 5 (4, 4) = (4, 4) ∧ psort 5 (0, 1) = (0, 1) ∧
    psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧ psort 5 (0, 4) = (0, 4) ∧
    psort 5 (1, 0) = (0, 1) ∧ psort 5 (1, 2) = (1, 2) ∧ psort 5 (1, 3) = (1, 3) ∧
    psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 0) = (0, 2) ∧ psort 5 (2, 1) = (1, 2) ∧
    psort 5 (2, 3) = (2, 3) ∧ psort 5 (2, 4) = (2, 4) ∧ psort 5 (3, 0) = (0, 3) ∧
    psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧ psort 5 (3, 4) = (3, 4) ∧
    psort 5 (4, 0) = (0, 4) ∧ psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
    psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 5) = (0, 4) ∧ psort 4 (3, 4) = (0, 3) ∧
    psort 3 (2, 0) = (0, 2) ∧ psort 3 (2, 1) = (1, 2) ∧ psort 3 (1, 0) = (0, 1) := by
  decide +revert

/-- HOL `PSORT_3456_PERIODIC` (hexagons.hl:157). -/
theorem PSORT_3456_PERIODIC (i j : ℕ) :
    psort 3 (i + 3, j) = psort 3 (i, j) ∧ psort 3 (i, j + 3) = psort 3 (i, j) ∧
    psort 4 (i + 4, j) = psort 4 (i, j) ∧ psort 4 (i, j + 4) = psort 4 (i, j) ∧
    psort 5 (i + 5, j) = psort 5 (i, j) ∧ psort 5 (i, j + 5) = psort 5 (i, j) ∧
    psort 6 (i + 6, j) = psort 6 (i, j) ∧ psort 6 (i, j + 6) = psort 6 (i, j) := by
  simp [psort]

/-- HOL `sqrt8_LE_6` (hexagons.hl:189). -/
theorem sqrt8_LE_6 : Real.sqrt 8 ≤ 6 :=
  le_trans (Real.sqrt_le_sqrt (by norm_num : (8:ℝ) ≤ 36)) (by norm_num)

/-- HOL `sqrt8_LE_CSTAB` (hexagons.hl:194). -/
theorem sqrt8_LE_CSTAB : Real.sqrt 8 ≤ cstab :=
  le_trans (Real.sqrt_le_sqrt (by norm_num : (8:ℝ) ≤ 9)) (by norm_num [cstab])

/-- HOL `LE_sqrt8_2` (hexagons.hl:200). -/
theorem LE_sqrt8_2 : (2 : ℝ) ≤ Real.sqrt 8 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

/-- HOL `LE_sqrt8_2h0` (hexagons.hl:205). -/
theorem LE_sqrt8_2h0 : 2 * h0 ≤ Real.sqrt 8 :=
  (Real.le_sqrt (by norm_num [h0]) (by norm_num)).2 (by norm_num [h0])

/-- HOL `LT_sqrt8_2h0` (hexagons.hl:211). -/
theorem LT_sqrt8_2h0 : 2 * h0 < Real.sqrt 8 :=
  Real.lt_sqrt_of_sq_lt (by norm_num [h0] : (2 * h0) ^ 2 < 8)

/-- HOL `MOD_PERIODIC` (hexagons.hl:220). -/
theorem MOD_PERIODIC (k i : ℕ) (_hk : k ≠ 0) :
    (i + k) % k = i % k ∧ (i + k + 1) % k = (i + 1) % k := by
  constructor
  · simp
  · rw [Nat.add_right_comm i k 1, Nat.add_mod_right]

/-- Numeric facts used throughout (`h0 = 1.26`, `cstab = 3.01`). -/
theorem le_cstab_two_p20 : (2 : ℝ) ≤ cstab := by norm_num [cstab]

theorem two_lt_two_h0_p20 : (2 : ℝ) < 2 * h0 := by norm_num [h0]

theorem four_h0_lt_six_p20 : 4 * h0 < 6 := by norm_num [h0]

theorem two_h0_le_cstab_p20 : 2 * h0 ≤ cstab := by norm_num [h0, cstab]

/-- `psort` is symmetric in its pair argument. -/
theorem psort_swap_p20 (k i j : ℕ) : psort k (i, j) = psort k (j, i) := by
  simp only [psort]
  by_cases h1 : i % k ≤ j % k <;> by_cases h2 : j % k ≤ i % k
  · rw [if_pos h1, if_pos h2, Nat.le_antisymm h1 h2]
  · rw [if_pos h1, if_neg h2]
  · rw [if_neg h1, if_pos h2]
  · omega

/-- `psort` equality decomposes into unordered residue pairs. -/
theorem psort_eq_cases_p20 {k a b c d : ℕ}
    (h : psort k (c, d) = psort k (a, b)) :
    (c % k = a % k ∧ d % k = b % k) ∨ (c % k = b % k ∧ d % k = a % k) := by
  simp only [psort] at h
  by_cases h1 : a % k ≤ b % k <;> by_cases h2 : c % k ≤ d % k <;>
    simp only [h1, h2, if_true, if_false, Prod.mk.injEq] at h
  · exact Or.inl ⟨h.1, h.2⟩
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.1, h.2⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- HOL `DIAG_NOT_PSORT` (YRTAFYH.hl): a diagonal `psort` never equals the
`psort` of a vertex-successor edge pair. -/
theorem diag_not_edge_psort_p20 {k i j : ℕ} (p : ℕ) (hk2 : 1 < k)
    (hd : scsDiag k i j) : ¬(psort k (i, j) = psort k (p, p + 1)) := by
  intro heq
  rcases psort_eq_cases_p20 heq.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine hd.2.1 ?_
    have h1 : (i + 1) % k = (i % k + 1 % k) % k := Nat.add_mod i 1 k
    have h2 : (p + 1) % k = (p % k + 1 % k) % k := Nat.add_mod p 1 k
    rw [h1, ← e1]
    exact h2.symm.trans e2
  · refine hd.2.2 ?_
    have h1 : (j + 1) % k = (j % k + 1 % k) % k := Nat.add_mod j 1 k
    have h2 : (p + 1) % k = (p % k + 1 % k) % k := Nat.add_mod p 1 k
    rw [h1, ← e1]
    exact (h2.symm.trans e2).symm

/-- HOL `PSORT_MOD` (hexagons.hl:1891). -/
theorem PSORT_MOD (k i j : ℕ) (_hk : k ≠ 0) :
    psort k (i % k, j % k) = psort k (i, j) := by
  simp only [psort, Nat.mod_mod]

/-- HOL `DIAG_MOD` (hexagons.hl:1910). -/
theorem DIAG_MOD (k i j : ℕ) (_hk : k ≠ 0) :
    scsDiag k (i % k) (j % k) ↔ scsDiag k i j := by
  rw [scsDiag, scsDiag, Nat.mod_mod, Nat.mod_mod,
    Nat.mod_add_mod i k 1, Nat.mod_add_mod j k 1]

/-- HOL `scs_5M3` (hexagons.hl:153): the fifth M-row system, `mk_unadorned_v39`
over the `funlist_v39` tables with diagonal `2` / `2*h0` at `k = 5`. -/
noncomputable def scs5M3 : ScsV39 :=
  mkUnadornedV39 5 0.616
    (funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
      ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)

/-! ## `is_scs_v39` verifications and basic invariants
(hexagons.hl:226-1050) -/

/-- HOL `SCS_6I1_IS_SCS` (hexagons.hl:226). Discharged via the `is_scs_adj_p22`
kit of LocalAuto22 (W5 wave; `dTame 6 = 0.712 < 0.9`, edge bounds `2*h0 ≤ cstab`). -/
theorem SCS_6I1_IS_SCS : isScsV39 scs6I1 := is_scs_6I1_p22

/-- HOL `DIST_LE_IMP_A_LE` (hexagons.hl:262). -/
theorem DIST_LE_IMP_A_LE (s : ScsV39) (v : ℕ → V3) (i j : ℕ) (a : ℝ)
    (hbb : BBsV39 s v) (hd : dist (v i) (v j) ≤ a) : s.a i j ≤ a :=
  le_trans (hbb.2.2.1 i j).1 hd

/-- Numeric strict facts for the M-row edge sets. -/
theorem two_h0_lt_cstab_p20 : 2 * h0 < cstab := by norm_num [h0, cstab]

/-- `funlistV39` tables only read residues: `(i % k, j % k)` entry equals the
`(i, j)` entry (hexagons.hl `PSORT_MOD` applied to the whole table). -/
theorem funlist_mod_p20 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ)
    (_hk : k ≠ 0) :
    funlistV39 data d k (i % k) (j % k) = funlistV39 data d k i j := by
  simp only [funlistV39, psort, Nat.mod_mod]

/-- `funlistV39` tables are 2-periodic in `k` (hexagons.hl `PSORT_3456_PERIODIC`). -/
theorem periodic2_funlist_p20 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k : ℕ) :
    Periodic2 (funlistV39 data d k) k := by
  intro i j
  simp [funlistV39, psort, Nat.add_mod_right]

/-- The strict `2 < 2*h0` edge fact. -/
theorem two_lt_two_h0' : (2 : ℝ) < 2 * h0 := two_lt_two_h0_p20

/-- HOL `SCS_3M1_IS_SCS` (hexagons.hl:273). Direct `is_scs_v39` verification of
the funlist tables (SCS_TAC expansion: 9 residue cases per table column). -/
theorem SCS_3M1_IS_SCS : isScsV39 scs3M1 := by
  unfold isScsV39 scs3M1 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0)] 2 3) 3 :=
    periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab)] (2 * h0) 3) 3 :=
    periodic2_funlist_p20 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 3, periodic_empty 3,
    periodic_empty 3, periodic_empty 3, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hz2 : j % 3 < 3 := Nat.mod_lt j (by omega)
    interval_cases i % 3 <;> interval_cases j % 3 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hz2 : j % 3 < 3 := Nat.mod_lt j (by omega)
    interval_cases i % 3 <;> interval_cases j % 3 <;> simp [assocdV39] <;>
      norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  · intro i hk3
    rw [← funlist_mod_p20 [((0, 1), cstab)] (2 * h0) 3 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 3 1]
    have hz : i % 3 < 3 := Nat.mod_lt i (by omega)
    interval_cases i % 3 <;> simp [funlistV39, psort, assocdV39] <;>
      norm_num [h0, cstab]
  · intro i hk3
    omega
  · have key : ∀ r : ℕ, r < 3 →
        ((2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 r ((r + 1) % 3) ∨
            2 < funlistV39 [((0, 1), 2 * h0)] 2 3 r ((r + 1) % 3)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20, two_lt_two_h0'] <;>
        norm_num [h0, cstab]
    have hS : {i | i < 3 ∧ (2 * h0 < funlistV39 [((0, 1), cstab)] (2 * h0) 3 i (i + 1) ∨
        2 < funlistV39 [((0, 1), 2 * h0)] 2 3 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), cstab)] (2 * h0) 3 i (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2 * h0)] 2 3 i (i + 1) (by omega),
        ← Nat.mod_add_mod i 3 1]
      rw [key (i % 3) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- HOL `SCS_5M1_IS_SCS` (hexagons.hl:341). Direct `is_scs_v39` verification;
the five diagonal pairs never hit a table slot, so edge bounds are `2*h0 ≤ cstab`
(hexagons.hl uses `DIAG_NOT_PSORT` for the same reading). -/
theorem SCS_5M1_IS_SCS : isScsV39 scs5M1 := by
  unfold isScsV39 scs5M1 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5) 5 :=
    periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) 5 :=
    periodic2_funlist_p20 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 5, periodic_empty 5,
    periodic_empty 5, periodic_empty 5, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39] <;>
      norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  · intro i hk3
    omega
  · intro i hk5
    rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 5 1]
    have hz : i % 5 < 5 := Nat.mod_lt i (by omega)
    interval_cases i % 5 <;> simp [funlistV39, psort, assocdV39] <;>
      norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 5 →
        ((2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
              ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 r ((r + 1) % 5) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              r ((r + 1) % 5)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20, two_lt_two_h0'] <;>
        norm_num [h0, cstab]
    have hS : {i | i < 5 ∧ (2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6),
              ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
          ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
          ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i (i + 1) (by omega),
        ← Nat.mod_add_mod i 5 1]
      rw [key (i % 5) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- HOL `SCS_4M2_IS_SCS` (hexagons.hl:761). Direct `is_scs_v39` verification of
the funlist tables. -/
theorem SCS_4M2_IS_SCS : isScsV39 scs4M2 := by
  unfold isScsV39 scs4M2 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0),
        ((1, 3), 2 * h0)] 2 4) 4 := periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
      4 := periodic2_funlist_p20 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 4, periodic_empty 4,
    periodic_empty 4, periodic_empty 4, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by omega)
    interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by omega)
    interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39] <;>
      norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  · intro i hk3
    omega
  · intro i hk4
    rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i
        (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
    have hz : i % 4 < 4 := Nat.mod_lt i (by omega)
    interval_cases i % 4 <;> simp [funlistV39, psort, assocdV39] <;>
      norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 4 →
        ((2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4
              r ((r + 1) % 4) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4
              r ((r + 1) % 4)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20, two_lt_two_h0'] <;>
        norm_num [h0, cstab]
    have hS : {i | i < 4 ∧ (2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6),
              ((1, 3), 6)] (2 * h0) 4 i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4
              i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i
          (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4 i
          (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
      rw [key (i % 4) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- HOL `SCS_5I1_IS_SCS` (hexagons.hl:422). Discharged via `is_scs_adj_p22`. -/
theorem SCS_5I1_IS_SCS : isScsV39 scs5I1 := is_scs_5I1_p22

/-- HOL `SCS_5I2_IS_SCS` (hexagons.hl:491). Discharged via `is_scs_adj_p22`. -/
theorem SCS_5I2_IS_SCS : isScsV39 scs5I2 := is_scs_5I2_p22

/-- HOL `SCS_5I3_IS_SCS` (hexagons.hl:565). Direct `is_scs_v39` verification of
the funlist tables (the strict `2*h0 < sqrt8` edge fact enters the card bound). -/
theorem SCS_5I3_IS_SCS : isScsV39 scs5I3 := by
  unfold isScsV39 scs5I3 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5) 5 :=
    periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) 5 :=
    periodic2_funlist_p20 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 5, periodic_empty 5,
    periodic_empty 5, periodic_empty 5, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39] <;>
      first | exact LE_sqrt8_2h0 | norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;>
      first | norm_num [h0, cstab] | exact LE_sqrt8_2
  · intro i hk3
    omega
  · intro i hk5
    rw [← funlist_mod_p20 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 5 1]
    have hz : i % 5 < 5 := Nat.mod_lt i (by omega)
    interval_cases i % 5 <;> simp [funlistV39, psort, assocdV39] <;>
      first | exact sqrt8_LE_CSTAB | norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 5 →
        ((2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
              ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 r ((r + 1) % 5) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              r ((r + 1) % 5)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20, two_lt_two_h0',
          LT_sqrt8_2h0] <;> norm_num [h0, cstab]
    have hS : {i | i < 5 ∧ (2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6),
              ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5
              i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
              ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5
              i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
          ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
          ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i (i + 1)
          (by omega), ← Nat.mod_add_mod i 5 1]
      rw [key (i % 5) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- HOL `SCS_5M2_IS_SCS` (hexagons.hl:665). Direct `is_scs_v39` verification of
the funlist tables. -/
theorem SCS_5M2_IS_SCS : isScsV39 scs5M2 := by
  unfold isScsV39 scs5M2 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab),
        ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5) 5 :=
    periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5) 5 :=
    periodic2_funlist_p20 _ _ _
  refine ⟨by norm_num, by norm_num, by norm_num, periodic_empty 5, periodic_empty 5,
    periodic_empty 5, periodic_empty 5, pa, pa, pb, pb,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ hj => False.elim hj,
    fun _ _ hj => False.elim hj, ?_⟩
  · intro i j
    simp only [funlistV39, psort]
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]
  · intro i j
    simp only [funlistV39, psort]
    refine ⟨le_refl _, ?_, le_refl _⟩
    have hz1 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hz2 : j % 5 < 5 := Nat.mod_lt j (by omega)
    interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39] <;>
      norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;> norm_num [h0, cstab]
  · intro i hk3
    omega
  · intro i hk5
    rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 5 1]
    have hz : i % 5 < 5 := Nat.mod_lt i (by omega)
    interval_cases i % 5 <;> simp [funlistV39, psort, assocdV39] <;>
      norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 5 →
        ((2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6),
              ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 r ((r + 1) % 5) ∨
            2 < funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab),
              ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5
              r ((r + 1) % 5)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20] <;>
        norm_num [h0, cstab]
    have hS : {i | i < 5 ∧ (2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6),
              ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5
              i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab),
              ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5
              i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
          ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
          ((1, 4), cstab), ((2, 4), cstab)] 2 5 i (i + 1) (by omega),
        ← Nat.mod_add_mod i 5 1]
      rw [key (i % 5) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp
    all_goals norm_num

/-- HOL `SCS_6M1_IS_SCS` (hexagons.hl:853). Discharged via `is_scs_adj_p22`. -/
theorem SCS_6M1_IS_SCS : isScsV39 scs6M1 := is_scs_6M1_p22

/-- HOL `SCS_6T1_IS_SCS` (hexagons.hl:889). Discharged via `is_scs_adj_p22`. -/
theorem SCS_6T1_IS_SCS : isScsV39 scs6T1 := is_scs_6T1_p22

/-- HOL `SCS_6I1_BASIC` (hexagons.hl:934). -/
theorem SCS_6I1_BASIC : scsBasicV39 scs6I1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_6T1_BASIC` (hexagons.hl:937). -/
theorem SCS_6T1_BASIC : scsBasicV39 scs6T1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_6M1_BASIC` (hexagons.hl:940). -/
theorem SCS_6M1_BASIC : scsBasicV39 scs6M1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3M1_BASIC` (hexagons.hl:944). -/
theorem SCS_3M1_BASIC : scsBasicV39 scs3M1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3T1_BASIC` (hexagons.hl:948). -/
theorem SCS_3T1_BASIC : scsBasicV39 scs3T1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3T4_BASIC` (hexagons.hl:951). -/
theorem SCS_3T4_BASIC : scsBasicV39 scs3T4 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5M1_BASIC` (hexagons.hl:955). -/
theorem SCS_5M1_BASIC : scsBasicV39 scs5M1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5M2_BASIC` (hexagons.hl:958). -/
theorem SCS_5M2_BASIC : scsBasicV39 scs5M2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5I1_BASIC` (hexagons.hl:963). -/
theorem SCS_5I1_BASIC : scsBasicV39 scs5I1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5I2_BASIC` (hexagons.hl:966). -/
theorem SCS_5I2_BASIC : scsBasicV39 scs5I2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5I3_BASIC` (hexagons.hl:969). -/
theorem SCS_5I3_BASIC : scsBasicV39 scs5I3 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M2_BASIC` (hexagons.hl:972). -/
theorem SCS_4M2_BASIC : scsBasicV39 scs4M2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M6_BASIC` (hexagons.hl:976). -/
theorem SCS_4M6_BASIC : scsBasicV39 scs4M6' := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_6I1` (hexagons.hl:982). -/
theorem K_SCS_6I1 : scs6I1.k = 6 := rfl

/-- HOL `K_SCS_6T1` (hexagons.hl:985). -/
theorem K_SCS_6T1 : scs6T1.k = 6 := rfl

/-- HOL `K_SCS_3M1` (hexagons.hl:989). -/
theorem K_SCS_3M1 : scs3M1.k = 3 := rfl

/-- HOL `K_SCS_3T1` (hexagons.hl:992). -/
theorem K_SCS_3T1 : scs3T1.k = 3 := rfl

/-- HOL `K_SCS_3T4` (hexagons.hl:995). -/
theorem K_SCS_3T4 : scs3T4.k = 3 := rfl

/-- HOL `K_SCS_5M1` (hexagons.hl:999). -/
theorem K_SCS_5M1 : scs5M1.k = 5 := rfl

/-- HOL `K_SCS_5M2` (hexagons.hl:1002). -/
theorem K_SCS_5M2 : scs5M2.k = 5 := rfl

/-- HOL `K_SCS_5I1` (hexagons.hl:1005). -/
theorem K_SCS_5I1 : scs5I1.k = 5 := rfl

/-- HOL `K_SCS_5I2` (hexagons.hl:1009). -/
theorem K_SCS_5I2 : scs5I2.k = 5 := rfl

/-- HOL `K_SCS_5I3` (hexagons.hl:1013). -/
theorem K_SCS_5I3 : scs5I3.k = 5 := rfl

/-- HOL `K_SCS_4M2` (hexagons.hl:1019). -/
theorem K_SCS_4M2 : scs4M2.k = 4 := rfl

/-- HOL `K_SCS_4M6` (hexagons.hl:1022). -/
theorem K_SCS_4M6 : scs4M6'.k = 4 := rfl

/-- HOL `J_SCS_3M1` (hexagons.hl:1028). -/
theorem J_SCS_3M1 (i i1 j : ℕ) : (scsPropEquV39 scs3M1 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T4` (hexagons.hl:1032). -/
theorem J_SCS_3T4 (i i1 j : ℕ) : (scsPropEquV39 scs3T4 i).J i1 j = False := rfl

/-- HOL `J_SCS_5M1` (hexagons.hl:1037). -/
theorem J_SCS_5M1 (i i1 j : ℕ) : (scsPropEquV39 scs5M1 i).J i1 j = False := rfl

/-- HOL `J_SCS_4M2` (hexagons.hl:1040). -/
theorem J_SCS_4M2 (i i1 j : ℕ) : (scsPropEquV39 scs4M2 i).J i1 j = False := rfl

/-- Periodicity folds to mod-periodicity. -/
theorem periodic_mod_p20 {f : ℕ → V3} {k : ℕ} (hper : Periodic f k) (i : ℕ) :
    f i = f (i % k) := by
  have key : ∀ m r, f (k * m + r) = f r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
        intro r
        have hE : k * (m + 1) + r = k * m + r + k := by ring
        rw [hE, hper, ih]
  have hI : i = k * (i / k) + i % k := (Nat.div_add_mod i k).symm
  nth_rewrite 1 [hI]
  exact key (i / k) (i % k)

/-- HOL `DIST_PSORT` (hexagons.hl:1047). -/
theorem DIST_PSORT (v : ℕ → V3) (k : ℕ) (i j i' j' : ℕ)
    (hper : Periodic v k) (_hk : k ≠ 0)
    (h : psort k (i, j) = psort k (i', j')) :
    dist (v i') (v j') = dist (v i) (v j) := by
  have e1 : v i = v (i % k) := periodic_mod_p20 hper i
  have e2 : v j = v (j % k) := periodic_mod_p20 hper j
  have e3 : v i' = v (i' % k) := periodic_mod_p20 hper i'
  have e4 : v j' = v (j' % k) := periodic_mod_p20 hper j'
  simp only [psort] at h
  by_cases h1 : i % k ≤ j % k <;> by_cases h2 : i' % k ≤ j' % k <;>
    simp only [h1, h2, Prod.mk.injEq, if_true, if_false] at h
  all_goals
    rw [e1, e2, e3, e4, h.1, h.2]
    try rw [dist_comm]

/-- HOL `STAB_BB` (hexagons.hl:1066). -/
theorem STAB_BB (s : ScsV39) (v : ℕ → V3) (i j : ℕ) (_hs : isScsV39 s)
    (hd : dist (v i) (v j) ≤ cstab) (hbb : BBsV39 s v) :
    BBsV39 (scsStabDiagV39 s i j) v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  have hk : s.k ≠ 0 := by have := _hs.2.1; omega
  refine ⟨h1, h2, fun i' j' => ?_, h4⟩
  have hle := h3 i' j'
  simp only [scsStabDiagV39, mkUnadornedV39]
  constructor
  · exact hle.1
  · split
    · next hpeq =>
        rw [DIST_PSORT v s.k i j i' j' h2 hk hpeq]
        exact hd
    · exact hle.2

/-- HOL `SCS_K_D_A_STAB_EQ` (hexagons.hl:1084). -/
theorem SCS_K_D_A_STAB_EQ (s : ScsV39) (i j : ℕ) :
    (scsStabDiagV39 s i j).d = s.d ∧ (scsStabDiagV39 s i j).k = s.k ∧
      ∀ i' j', (scsStabDiagV39 s i j).a i' j' = s.a i' j' :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- HOL `DIAG_SCS_M_EQ` (hexagons.hl:1090). -/
theorem DIAG_SCS_M_EQ (s : ScsV39) (i j : ℕ) (hs : isScsV39 s)
    (hd : scsDiag s.k i j) : scsM s = scsM (scsStabDiagV39 s i j) := by
  have hk2 : 1 < s.k := by have := hs.2.1; omega
  ext x
  simp only [scsM, Set.mem_setOf_eq]
  have hb : ∀ p q : ℕ, (scsStabDiagV39 s i j).b p q =
      if psort s.k (i, j) = psort s.k (p, q) then cstab else s.b p q :=
    fun p q => rfl
  have hbE : (scsStabDiagV39 s i j).b x (x + 1) = s.b x (x + 1) := by
    rw [hb x (x + 1), if_neg (diag_not_edge_psort_p20 x hk2 hd)]
  constructor
  · rintro ⟨hlt, h⟩
    rw [hbE]
    exact ⟨hlt, h⟩
  · rintro ⟨hlt, h⟩
    rw [hbE] at h
    exact ⟨hlt, h⟩

/-- HOL `DIAD_PSORT_IMP_DIAD` (hexagons.hl:1098). -/
theorem DIAD_PSORT_IMP_DIAD (k i j i' j' : ℕ) (hk : k ≠ 0)
    (hd : scsDiag k i j) (hp : psort k (i', j') = psort k (i, j)) :
    scsDiag k i' j' := by
  have hps : (i' % k = i % k ∧ j' % k = j % k) ∨ (i' % k = j % k ∧ j' % k = i % k) :=
    psort_eq_cases_p20 hp
  refine ⟨?_, ?_, ?_⟩
  · rcases hps with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · intro hc
      exact hd.1 (e1.symm.trans (hc.trans e2))
    · intro hc
      exact hd.1 ((e2.symm.trans hc.symm).trans e1)
  · rcases hps with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [Nat.add_mod, e1, e2]
      have h2 := hd.2.1
      rw [Nat.add_mod] at h2
      exact h2
    · rw [Nat.add_mod, e1, e2]
      have h3 := hd.2.2
      rw [Nat.add_mod] at h3
      exact fun hc => h3 hc.symm
  · rcases hps with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [Nat.add_mod, e1, e2]
      have h3 := hd.2.2
      rw [Nat.add_mod] at h3
      exact h3
    · rw [Nat.add_mod, e1, e2]
      have h2 := hd.2.1
      rw [Nat.add_mod] at h2
      exact fun hc => h2 hc.symm

/-- HOL `PEDSLGV1` (hexagons.hl:1124). Derived from the (upstream, appendix
lane) `PEDSLGV1_concl` of LocalAuto1, whose proof is itself still pending. -/
theorem PEDSLGV1 (v : ℕ → V3) (i j : ℕ) (hv : v ∈ MMsV39 scs6I1)
    (hd : scsDiag 6 i j) (hdist : dist (v i) (v j) ≤ cstab) :
    v ∈ MMsV39 (scsStabDiagV39 scs6I1 i j) :=
  PEDSLGV1_concl v i j hv hd hdist

/-! ## The `scs_6M1` vs `scs_6I1` lane (hexagons.hl:1165-1258) -/

/-- The two adjacency disjuncts of `csAdj` are ruled out on a diagonal. -/
theorem diag_not_adj_p20 {k : ℕ} {i j : ℕ} (hd : scsDiag k i j) :
    ¬(j % k = (i + 1) % k ∨ (j + 1) % k = i % k) := by
  rintro (h | h)
  · exact hd.2.1 h.symm
  · exact hd.2.2 h.symm

/-- Edge-pair mod-6 facts: `(i+1, i)` and `(i+2, i)` are never equal mod 6. -/
theorem mod6_edge_facts_p20 (i : ℕ) :
    i % 6 ≠ (i + 1) % 6 ∧ (i + 1) % 6 ≠ i % 6 ∧
    i % 6 ≠ (i + 2) % 6 ∧ (i + 2) % 6 ≠ i % 6 := by
  have hz : i % 6 < 6 := Nat.mod_lt i (by omega)
  have r1 : (i + 1) % 6 = (i % 6 + 1) % 6 := (Nat.mod_add_mod i 6 1).symm
  have r2 : (i + 2) % 6 = (i % 6 + 2) % 6 := (Nat.mod_add_mod i 6 2).symm
  rw [r1, r2]
  interval_cases (i % 6) <;> decide

/-- HOL `K_SCS_6M1` (hexagons.hl:1165). -/
theorem K_SCS_6M1 : scs6M1.k = 6 ∧ scs6M1.d = scs6I1.d := ⟨rfl, rfl⟩

/-- HOL `D_6M1_EQ_6I1` (hexagons.hl:1169). -/
theorem D_6M1_EQ_6I1 : scs6M1.d = scs6I1.d := rfl

/-- HOL `A_6M1_EQ_6I1_EDGE` (hexagons.hl:1174). -/
theorem A_6M1_EQ_6I1_EDGE (i : ℕ) :
    scs6M1.a i (i + 1) = scs6I1.a i (i + 1) := by
  simp [scs6M1, scs6I1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- HOL `SCS_M_6I1_EQ_6M1` (hexagons.hl:1177). -/
theorem SCS_M_6I1_EQ_6M1 : scsM scs6I1 = scsM scs6M1 := by
  ext i
  simp [scsM, Set.mem_setOf_eq, scs6I1, scs6M1, mkUnadornedV39, csAdj,
    mod6_edge_facts_p20 i]

/-- HOL `BB_6I1_IS_BB_6M1` (hexagons.hl:1182). -/
theorem BB_6I1_IS_BB_6M1 (v : ℕ → V3) (hbb : BBsV39 scs6I1 v)
    (hdiag : ∀ i j, scsDiag 6 i j → cstab ≤ dist (v i) (v j)) :
    BBsV39 scs6M1 v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  simp only [scs6I1, mkUnadornedV39, csAdj] at hle1
  constructor
  · show csAdj 6 2 cstab i j ≤ dist (v i) (v j)
    unfold csAdj
    by_cases e1 : i % 6 = j % 6
    · rw [if_pos e1] at hle1 ⊢; exact hle1
    · rw [if_neg e1] at hle1 ⊢
      by_cases e2 : j % 6 = (i + 1) % 6 ∨ (j + 1) % 6 = i % 6
      · rw [if_pos e2] at hle1 ⊢; exact hle1
      · rw [if_neg e2] at hle1 ⊢
        exact hdiag i j ⟨e1, fun hc => e2 (Or.inl hc.symm), fun hc => e2 (Or.inr hc.symm)⟩
  · exact hle2

/-- Monotonicity of `csAdj` in the two corner values. -/
theorem csAdj_le_p20 (k : ℕ) (a1 a1' a2 a2' : ℝ) (i j : ℕ) (h1 : a1 ≤ a1')
    (h2 : a2 ≤ a2') : csAdj k a1 a2 i j ≤ csAdj k a1' a2' i j := by
  unfold csAdj
  split_ifs with e
  · exact le_refl 0
  · exact h1
  · exact h2

/-- HOL `A_6I1_LE_A_6M1` (hexagons.hl:1217). -/
theorem A_6I1_LE_A_6M1 (i j : ℕ) : scs6I1.a i j ≤ scs6M1.a i j :=
  csAdj_le_p20 6 2 2 (2 * h0) cstab i j (le_refl 2) two_h0_le_cstab_p20

/-- HOL `B_6I1_LE_B_6M1` (hexagons.hl:1221). -/
theorem B_6I1_LE_B_6M1 (i j : ℕ) : scs6M1.b i j = scs6I1.b i j := rfl

/-- HOL `PEDSLGV2` (hexagons.hl, between 1221 and 1259). Derived from the
(upstream, appendix lane) `PEDSLGV2_concl` of LocalAuto1, whose proof is
itself still pending. -/
theorem PEDSLGV2 (v : ℕ → V3) (hv : v ∈ MMsV39 scs6I1)
    (hdiag : ∀ i j, scsDiag 6 i j → cstab ≤ dist (v i) (v j)) :
    v ∈ MMsV39 scs6M1 :=
  PEDSLGV2_concl v hv hdiag

/-- HOL `STAB_6I1_SCS` (hexagons.hl:1259). The 20-conjunct `is_scs_v39`
verification of the stabilised system: the `csAdj` a-table is untouched and the
b-table is overridden by `cstab` exactly on the `psort`-slot of the diagonal
pair `(i, j)`, which no edge pair hits (`diag_not_edge_psort_p20`). -/
theorem STAB_6I1_SCS (i j : ℕ) (hd : scsDiag scs6I1.k i j) :
    isScsV39 (scsStabDiagV39 scs6I1 i j) ∧
      scsBasicV39 (scsStabDiagV39 scs6I1 i j) := by
  have hdd : scsDiag 6 i j := hd
  have hk1 : (1 : ℕ) < 6 := by norm_num
  have hE : ∀ p : ℕ, ¬(2 * h0 < (if psort 6 (i, j) = psort 6 (p, p + 1) then cstab
        else csAdj 6 (2 * h0) 6 p (p + 1)) ∨ 2 < csAdj 6 2 (2 * h0) p (p + 1)) := by
    intro p h
    rcases h with hc | hc
    · simp only [csAdj] at hc
      rw [if_neg (diag_not_edge_psort_p20 p hk1 hdd), if_neg (mod6_edge_facts_p20 p).1,
        if_pos (Or.inl trivial)] at hc
      exact lt_irrefl (2 * h0) hc
    · simp only [csAdj] at hc
      rw [if_neg (mod6_edge_facts_p20 p).1,
        if_pos (Or.inl trivial)] at hc
      exact lt_irrefl 2 hc
  constructor
  · unfold isScsV39
    simp only [scsStabDiagV39, mkUnadornedV39, scs6I1]
    refine ⟨by norm_num [dTame], by norm_num, by norm_num, periodic_empty 6,
      periodic_empty 6, periodic_empty 6, periodic_empty 6, periodic2_cs_adj_p22,
      periodic2_cs_adj_p22, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
      fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
    · intro p q
      dsimp only
      have h6 : Periodic2 (csAdj 6 (2 * h0) 6) 6 := periodic2_cs_adj_p22
      rw [show psort 6 (p + 6, q) = psort 6 (p, q) by simp only [psort, Nat.add_mod_right],
        h6 p q |>.1,
        show psort 6 (p, q + 6) = psort 6 (p, q) by simp only [psort, Nat.add_mod_right],
        h6 p q |>.2]
      exact ⟨rfl, rfl⟩
    · intro p q
      dsimp only
      have h6 : Periodic2 (csAdj 6 (2 * h0) 6) 6 := periodic2_cs_adj_p22
      rw [show psort 6 (p + 6, q) = psort 6 (p, q) by simp only [psort, Nat.add_mod_right],
        h6 p q |>.1,
        show psort 6 (p, q + 6) = psort 6 (p, q) by simp only [psort, Nat.add_mod_right],
        h6 p q |>.2]
      exact ⟨rfl, rfl⟩
    · intro p q
      refine ⟨csAdj_swap_p22, csAdj_swap_p22, ?_, ?_⟩
      · have hps : psort 6 (q, p) = psort 6 (p, q) := psort_swap_p20 6 q p
        rw [hps, csAdj_swap_p22]
      · have hps : psort 6 (q, p) = psort 6 (p, q) := psort_swap_p20 6 q p
        rw [hps, csAdj_swap_p22]
        exact ⟨rfl, trivial⟩
    · intro p q
      refine ⟨le_refl _, ?_, le_refl _⟩
      show csAdj 6 2 (2 * h0) p q ≤ (if psort 6 (i, j) = psort 6 (p, q) then cstab
        else csAdj 6 (2 * h0) 6 p q)
      unfold csAdj
      split_ifs <;> norm_num [h0, cstab]
    · intro p
      simp [csAdj]
    · intro p q hpq
      obtain ⟨hp, hq, hne⟩ := hpq
      have e1 : p % 6 = p := Nat.mod_eq_of_lt hp
      have e2 : q % 6 = q := Nat.mod_eq_of_lt hq
      simp only [csAdj, e1, e2]
      split_ifs with hc
      · exact absurd (by rw [hc]) hne
      · norm_num
      · norm_num [h0]
    · intro p h3
      omega
    · intro p _
      show (if psort 6 (i, j) = psort 6 (p, p + 1) then cstab
          else csAdj 6 (2 * h0) 6 p (p + 1)) ≤ cstab
      rw [if_neg (diag_not_edge_psort_p20 p hk1 hdd)]
      unfold csAdj
      split_ifs with h1 h2
      · norm_num [cstab]
      · exact two_h0_le_cstab_p20
      · exact (h2 (Or.inl rfl)).elim
    · show {p | p < 6 ∧ (2 * h0 < (if psort 6 (i, j) = psort 6 (p, p + 1) then cstab
            else csAdj 6 (2 * h0) 6 p (p + 1)) ∨
          2 < csAdj 6 2 (2 * h0) p (p + 1))}.ncard + 6 ≤ 6
      have hEmp : {p | p < 6 ∧ (2 * h0 < (if psort 6 (i, j) = psort 6 (p, p + 1) then
            cstab else csAdj 6 (2 * h0) 6 p (p + 1)) ∨
          2 < csAdj 6 2 (2 * h0) p (p + 1))} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 (fun p hp => hE p hp.2)
      rw [hEmp, Set.ncard_empty]
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_DIAG_SCS_6I1_02` (hexagons.hl:1269). -/
theorem SCS_DIAG_SCS_6I1_02 : scsDiag scs6I1.k 0 2 := by
  rw [K_SCS_6I1]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_6I1_03` (hexagons.hl:1274). -/
theorem SCS_DIAG_SCS_6I1_03 : scsDiag scs6I1.k 0 3 := by
  rw [K_SCS_6I1]; unfold scsDiag; decide

/-- HOL `BASIC_HALF_SLICE_STAB` (hexagons.hl:1280). -/
theorem BASIC_HALF_SLICE_STAB (s : ScsV39) (i j p q : ℕ) (d' : ℝ)
    (_hb : scsBasicV39 s) :
    scsBasicV39 (scsHalfSliceV39 (scsStabDiagV39 s i j) p q d' False) := by
  constructor
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro i'' j''
    simp only [scsHalfSliceV39]
    split <;> rfl

/-- HOL `D_HALF_SLICE` (hexagons.hl:1292). -/
theorem D_HALF_SLICE (s : ScsV39) (i j p q : ℕ) (d' : ℝ) (mkj : Prop) :
    (scsHalfSliceV39 (scsStabDiagV39 s i j) p q d' mkj).d = d' := rfl

/-- HOL `BAISC_PROP_EQU` (hexagons.hl:1295). -/
theorem BAISC_PROP_EQU (s : ScsV39) (i : ℕ) (hb : scsBasicV39 s) :
    scsBasicV39 (scsPropEquV39 s i) := by
  obtain ⟨hu, hJ⟩ := hb
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun i' j' => hJ (i + i') (i + j')⟩
  · funext x; exact congrFun hlo (i + x)
  · funext x; exact congrFun hhi (i + x)
  · funext x; exact congrFun hstr (i + x)
  · exact congrArg (fun f : ℕ → ℕ → ℝ => fun j j' => f (i + j) (i + j')) ham
  · exact congrArg (fun f : ℕ → ℕ → ℝ => fun j j' => f (i + j) (i + j')) hbm

/-- HOL `K_SCS_PROP_EUQ` (hexagons.hl:1299). -/
theorem K_SCS_PROP_EUQ (s : ScsV39) (i : ℕ) : (scsPropEquV39 s i).k = s.k := rfl

/-! ## Slicing arrows around `scs_6I1` and M-row bounds
(hexagons.hl:1307-1738) -/

/-- HOL `AQICLXA_SLICE` (hexagons.hl:1307). -/
theorem AQICLXA_SLICE :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs5M1 1} := by
  sorry
  -- NEEDS: LocalAuto1.LKGRQUI_concl (appendix.hl:1144, proof pending) plus
  -- the local `is_scs_slice_v39` side conditions: the pair equality
  -- `(propEqu scs_3M1 1, propEqu scs_5M1 1) = scs_slice_v39 (stab 6I1 0 2)
  -- 0 2 0.103 0.616 False` (funlist table match, 9 + 25 residue cells),
  -- `dTame 6 = 0.712 ≤ 0.719`, `bm 0 2 = cstab < 4`, `mkj = False`.

/-- HOL `FZIOTEF_UNION` (hexagons.hl:1433). -/
theorem FZIOTEF_UNION (S1 S2 S3 S4 : Set ScsV39)
    (h12 : scsArrowV39 S1 S2) (h34 : scsArrowV39 S3 S4) :
    scsArrowV39 (S1 ∪ S3) (S2 ∪ S4) := by
  obtain ⟨ha12, hb12⟩ := h12
  obtain ⟨ha34, hb34⟩ := h34
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases (Set.mem_union _ _ _).1 hs with h | h
    · exact ha12 s h
    · exact ha34 s h
  · rcases hb12 with h | ⟨s, hs, hne⟩
    · rcases hb34 with h' | ⟨s, hs', hne'⟩
      · refine Or.inl (fun s' hs' => ?_)
        rcases (Set.mem_union _ _ _).1 hs' with h'' | h''
        · exact h s' h''
        · exact h' s' h''
      · exact Or.inr ⟨s, Set.mem_union_right _ hs', hne'⟩
    · exact Or.inr ⟨s, Set.mem_union_left _ hs, hne⟩

/-- HOL `AQICLXA` (hexagons.hl:1449). -/
theorem AQICLXA :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs3M1, scs5M1} := by
  sorry
  -- NEEDS: AQICLXA_SLICE above plus FZIOTEF_TRANS/FZIOTEF_UNION algebra with
  -- the half-arrows `{propEqu scs_3M1 1} → {scs_3M1}` and
  -- `{propEqu scs_5M1 1} → {scs_5M1}`; those are `LocalAuto1.YXIONXL3_concl`
  -- (appendix.hl:1141, proof pending) at shift 2 / 4 composed with the
  -- definitional `scs_prop_equ_v39 (scs_prop_equ_v39 s i) j =
  -- scs_prop_equ_v39 s (i + j)` and mod-k collapse (needs PROP_EQU_IS_SCS,
  -- LocalAuto12:424, proof pending, only for the isScs half).

/-- HOL `FUNOUYH_SLICE` (hexagons.hl:1474). -/
theorem FUNOUYH_SLICE :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3}
      {scsPropEquV39 scs4M2 1, scsPropEquV39 scs4M2 1} := by
  sorry
  -- NEEDS: LocalAuto1.LKGRQUI_concl (appendix.hl:1144, proof pending) plus
  -- the local `is_scs_slice_v39` side conditions for the `(0, 3)` half-slices
  -- against `propEqu scs_4M2 1` (funlist table match, 16 + 16 residue cells,
  -- `d' = d'' = 0.3789`, `bm 0 3 = cstab < 4`, `mkj = False`).

/-- HOL `FZIOTEF` (hexagons.hl:1592). -/
theorem FZIOTEF :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2} := by
  sorry
  -- NEEDS: FUNOUYH_SLICE above plus FZIOTEF_TRANS algebra with the half-arrow
  -- `{propEqu scs_4M2 1} → {scs_4M2}` (`LocalAuto1.YXIONXL3_concl` at shift 3,
  -- proof pending, composed with `propEqu (propEqu scs_4M2 1) 3 = scs_4M2`,
  -- needs PROP_EQU_IS_SCS for the isScs half).

/-- HOL `h0_LT_B_SCS_6M1` (hexagons.hl:1610). -/
theorem h0_LT_B_SCS_6M1 :
    (∀ i j, scsDiag 6 i j → 4 * h0 < scs6M1.b i j) ∧
      (∀ i j, scsDiag 6 i j → scs6M1.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · simp only [scs6M1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact four_h0_lt_six_p20
  · simp only [scs6M1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact le_refl cstab

/-- HOL `h0_LT_B_SCS_6I1` (hexagons.hl:1620). -/
theorem h0_LT_B_SCS_6I1 :
    (∀ i j, scsDiag 6 i j → 4 * h0 < scs6I1.b i j) ∧
      (∀ i j, scsDiag 6 i j → scs6I1.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · simp only [scs6I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact four_h0_lt_six_p20
  · simp only [scs6I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact two_h0_le_cstab_p20

/-- HOL `h0_LT_B_SCS_5I1` (hexagons.hl:1629). -/
theorem h0_LT_B_SCS_5I1 :
    (∀ i j, scsDiag 5 i j → 4 * h0 < scs5I1.b i j) ∧
      (∀ i j, scsDiag 5 i j → scs5I1.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · simp only [scs5I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact four_h0_lt_six_p20
  · simp only [scs5I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
    exact two_h0_le_cstab_p20

/-- Every value carried by the `scs_5M2` a-table is at most `cstab`. -/
theorem assocd_le_cstab_p20 (a : ℕ × ℕ) :
    ∀ l : List ((ℕ × ℕ) × ℝ), (∀ p ∈ l, p.2 ≤ cstab) → ∀ d : ℝ, d ≤ cstab →
      assocdV39 a l d ≤ cstab := by
  intro l
  induction l with
  | nil => intro _ d hd; exact hd
  | cons h t ih =>
      intro hmem d hd
      simp only [assocdV39]
      split
      · next e => exact hmem h (List.mem_cons.2 (Or.inl rfl))
      · next => exact ih (fun p hp => hmem p (List.mem_cons_of_mem _ hp)) d hd

/-- HOL `h0_LT_B_SCS_5M2` (hexagons.hl:1647). -/
theorem h0_LT_B_SCS_5M2 :
    ∀ i j, scsDiag 5 i j → scs5M2.a i j ≤ cstab := by
  intro i j hd
  have hne : ¬(i % 5 = j % 5) := hd.1
  simp only [scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
    ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j ≤ cstab
  unfold funlistV39
  rw [if_neg hne]
  exact assocd_le_cstab_p20 (psort 5 (i, j)) _ (by simp [le_cstab_two_p20]) 2
    le_cstab_two_p20

/-- HOL `h0_EQ_B_SCS_6I1` (hexagons.hl:1659). -/
theorem h0_EQ_B_SCS_6I1 :
    (∀ i j, scsDiag 6 i j → scs6I1.b i j = 6) ∧
      (∀ i j, scsDiag 6 i j → scs6I1.a i j = 2 * h0) := by
  constructor <;> intro i j hd
  · simp only [scs6I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
  · simp only [scs6I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]

/-- HOL `h0_EQ_B_SCS_5I1` (hexagons.hl:1668). -/
theorem h0_EQ_B_SCS_5I1 :
    (∀ i j, scsDiag 5 i j → scs5I1.b i j = 6) ∧
      (∀ i j, scsDiag 5 i j → scs5I1.a i j = 2 * h0) := by
  constructor <;> intro i j hd
  · simp only [scs5I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]
  · simp only [scs5I1, mkUnadornedV39, csAdj, if_neg hd.1, if_neg (diag_not_adj_p20 hd)]

/-- HOL `h0_LT_B_SCS_5I2` (hexagons.hl:1638). -/
theorem h0_LT_B_SCS_5I2 :
    (∀ i j, scsDiag 5 i j → 4 * h0 < scs5I2.b i j) ∧
      (∀ i j, scsDiag 5 i j → scs5I2.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · simp only [scs5I2, mkUnadornedV39, csAdj, if_neg hd.1,
      if_neg (diag_not_adj_p20 hd)]
    exact four_h0_lt_six_p20
  · simp only [scs5I2, mkUnadornedV39, csAdj, if_neg hd.1,
      if_neg (diag_not_adj_p20 hd)]
    exact sqrt8_LE_CSTAB

/-- HOL `h0_EQ_B_SCS_5I2` (hexagons.hl:1675). -/
theorem h0_EQ_B_SCS_5I2 :
    (∀ i j, scsDiag 5 i j → scs5I2.b i j = 6) ∧
      (∀ i j, scsDiag 5 i j → scs5I2.a i j = Real.sqrt 8) := by
  constructor <;> intro i j hd
  · simp only [scs5I2, mkUnadornedV39, csAdj, if_neg hd.1,
      if_neg (diag_not_adj_p20 hd)]
  · simp only [scs5I2, mkUnadornedV39, csAdj, if_neg hd.1,
      if_neg (diag_not_adj_p20 hd)]

/-- HOL `B_LE_CSTAB_6M1` (hexagons.hl:1687). -/
theorem B_LE_CSTAB_6M1 :
    (∀ i, scs6M1.b i (i + 1) ≤ cstab) ∧ (∀ i, scs6M1.b i (i + 1) ≤ 2 * h0) ∧
      (∀ i, (2 : ℝ) < scs6M1.b i (i + 1)) ∧ (∀ i, scs6M1.a i (i + 1) = 2) := by
  have hb : ∀ i, scs6M1.b i (i + 1) = 2 * h0 := by
    intro i
    simp [scs6M1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [hb i]; exact two_h0_le_cstab_p20
  · intro i; rw [hb i]
  · intro i; rw [hb i]; exact two_lt_two_h0_p20
  · intro i
    simp [scs6M1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge b-value of `scs_6M1`. -/
theorem b_edge_6M1_p20 (i : ℕ) : scs6M1.b i (i + 1) = 2 * h0 := by
  simp [scs6M1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge a-value of `scs_6M1`. -/
theorem a_edge_6M1_p20 (i : ℕ) : scs6M1.a i (i + 1) = 2 := by
  simp [scs6M1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge b-value of `scs_6I1`. -/
theorem b_edge_6I1_p20 (i : ℕ) : scs6I1.b i (i + 1) = 2 * h0 := by
  simp [scs6I1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge a-value of `scs_6I1`. -/
theorem a_edge_6I1_p20 (i : ℕ) : scs6I1.a i (i + 1) = 2 := by
  simp [scs6I1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge b-value of `scs_6T1`. -/
theorem b_edge_6T1_p20 (i : ℕ) : scs6T1.b i (i + 1) = 2 := by
  simp [scs6T1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- Edge a-value of `scs_6T1`. -/
theorem a_edge_6T1_p20 (i : ℕ) : scs6T1.a i (i + 1) = 2 := by
  simp [scs6T1, mkUnadornedV39, csAdj, mod6_edge_facts_p20 i]

/-- HOL `SCS_M_6M1` (hexagons.hl:1705). -/
theorem SCS_M_6M1 : scsM scs6M1 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 (fun i hi => ?_)
  simp only [scsM, Set.mem_setOf_eq] at hi
  rw [b_edge_6M1_p20, a_edge_6M1_p20] at hi
  rcases hi.2 with h | h
  · simp at h
  · simp at h

/-- HOL `CARD_SCS_M_6M1` (hexagons.hl:1699). -/
theorem CARD_SCS_M_6M1 : Set.ncard (scsM scs6M1) ≤ 1 := by
  rw [SCS_M_6M1]; simp

/-- HOL `SCS_M_6T1` (hexagons.hl:1713). -/
theorem SCS_M_6T1 : scsM scs6T1 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 (fun i hi => ?_)
  simp only [scsM, Set.mem_setOf_eq] at hi
  rw [b_edge_6T1_p20, a_edge_6T1_p20] at hi
  rcases hi.2 with h | h
  · exact absurd h (by norm_num [h0])
  · exact lt_irrefl 2 h

/-- HOL `SCS_M_5M2` (hexagons.hl:1719). Edge reading over the five residues:
`2*h0 < cstab` only at the `(0,1)` edge, and every `scs_5M2` a-edge is `2`. -/
theorem SCS_M_5M2 : scsM scs5M2 = {0} := by
  have key : ∀ r : ℕ, r < 5 →
      ((2 * h0 < funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
            ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 r ((r + 1) % 5) ∨
          2 < funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
            ((1, 4), cstab), ((2, 4), cstab)] 2 5 r ((r + 1) % 5)) ↔ r = 0) := by
    intro r hr
    interval_cases r <;>
      simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20] <;>
      norm_num [h0, cstab]
  ext i
  simp only [scsM, scs5M2, mkUnadornedV39, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlt, h⟩
    rw [← funlist_mod_p20 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
        ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) (by omega),
      ← funlist_mod_p20 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
        ((1, 4), cstab), ((2, 4), cstab)] 2 5 i (i + 1) (by omega),
      ← Nat.mod_add_mod i 5 1] at h
    rw [key (i % 5) (Nat.mod_lt i (by omega))] at h
    omega
  · rintro rfl
    simp [funlistV39, psort, assocdV39, two_h0_lt_cstab_p20]

/-! ## Mod/symmetrie kit and terminal implications (hexagons.hl:1740-2165) -/

/-- HOL `SCS_6M1_IMP_SCS_6T1` (hexagons.hl:1740). -/
theorem SCS_6M1_IMP_SCS_6T1 (hmn : main_nonlinear_terminal_v11) :
    ∀ v : ℕ → V3, v ∈ MMsV39 scs6M1 →
      (∀ i j, scsDiag 6 i j → cstab < dist (v i) (v j)) →
      v ∈ MMsV39 scs6T1 := by
  sorry
  -- NEEDS: the mnt11 lane, all proof-pending in LocalAuto1: RRCWNSJ_concl
  -- (appendix.hl:1321), JCYFMRP_concl (:1329), JLXFDMJ_concl (:1357),
  -- MXQTIED_concl (:1288), plus Nuxcoea.MMS_IMP_BBS /
  -- CHANGE_W_IN_BBS_MOD_IS_SCS and SCS_6M1_IS_SCS / SCS_6T1_IS_SCS (here).

/-- HOL `SCS_6I1_IMP_SCS_6T1` (hexagons.hl:1812). -/
theorem SCS_6I1_IMP_SCS_6T1 (hmn : main_nonlinear_terminal_v11) :
    ∀ v : ℕ → V3, v ∈ MMsV39 scs6I1 →
      (∀ i j, scsDiag 6 i j → cstab < dist (v i) (v j)) →
      v ∈ MMsV39 scs6T1 := by
  sorry
  -- NEEDS: SCS_6M1_IMP_SCS_6T1 above (mnt11 lane) plus PEDSLGV2 (LocalAuto1,
  -- proof pending); the isScs half closes via STAB_6I1_SCS + SCS_6T1_IS_SCS.

/-- HOL `SCS_6I1_BERAK_BY_CSTAB` (hexagons.hl:1831). -/
theorem SCS_6I1_BERAK_BY_CSTAB (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6I1}
      ({scs6T1} ∪ {x | ∃ i j, scsDiag 6 i j ∧ x = scsStabDiagV39 scs6I1 i j}) := by
  sorry
  -- DISCHARGES: hexagons.hl; arrow combining SCS_6I1_IMP_SCS_6T1 with the
  -- diag-stabilisation destinations.

/-- HOL `STAB_MOD` (hexagons.hl:1903). -/
theorem STAB_MOD (s : ScsV39) (i j : ℕ) (hs : isScsV39 s) :
    scsStabDiagV39 s (i % s.k) (j % s.k) = scsStabDiagV39 s i j := by
  have hk : s.k ≠ 0 := by have := hs.2.1; omega
  simp only [scsStabDiagV39, mkUnadornedV39, PSORT_MOD s.k i j hk]

/-- HOL `SET_STAB_6I1` (hexagons.hl:1913). -/
theorem SET_STAB_6I1 :
    {x | ∃ i j, scsDiag 6 i j ∧ x = scsStabDiagV39 scs6I1 i j} =
      {x | ∃ i j, scsDiag 6 (i % 6) (j % 6) ∧
        x = scsStabDiagV39 scs6I1 (i % 6) (j % 6)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 6 i j (by omega)).mpr hd,
      (STAB_MOD scs6I1 i j SCS_6I1_IS_SCS).symm⟩
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 6 i j (by omega)).mp hd,
      STAB_MOD scs6I1 i j SCS_6I1_IS_SCS⟩

/-- HOL `DIAG_EQ_ADD` (hexagons.hl:1918). -/
theorem DIAG_EQ_ADD (i j : ℕ) :
    scsDiag 6 (i % 6) (j % 6) ↔
      i % 6 = (j % 6 + 2) % 6 ∨ i % 6 = (j % 6 + 3) % 6 ∨
        j % 6 = (i % 6 + 2) % 6 ∨ j % 6 = (i % 6 + 3) % 6 := by
  have hz1 : i % 6 < 6 := Nat.mod_lt i (by omega)
  have hz2 : j % 6 < 6 := Nat.mod_lt j (by omega)
  interval_cases i % 6 <;> interval_cases j % 6 <;>
    simp [scsDiag] <;> decide

/-- HOL `PSORT_EQ_SYM` (hexagons.hl:1935). -/
theorem PSORT_EQ_SYM (s : ScsV39) (i j i' j' : ℕ) :
    (psort s.k (j, i) = psort s.k (j', i')) ↔ (psort s.k (i, j) = psort s.k (j', i')) := by
  rw [psort_swap_p20 s.k j i]

/-- HOL `STAB_SYM` (hexagons.hl:1940). -/
theorem STAB_SYM (s : ScsV39) (i j : ℕ) :
    scsStabDiagV39 s i j = scsStabDiagV39 s j i := by
  simp only [scsStabDiagV39, mkUnadornedV39, psort_swap_p20]

/-- `STAB_MOD` specialised to an already-reduced second index. -/
theorem stab_mod_lt_p20 (a b : ℕ) (hb : b % 6 = b) :
    scsStabDiagV39 scs6I1 (a % 6) b = scsStabDiagV39 scs6I1 a b := by
  have hk : scs6I1.k = 6 := rfl
  have h := STAB_MOD scs6I1 a b SCS_6I1_IS_SCS
  rw [hk] at h
  rwa [hb] at h

/-- HOL `EXPAND_STAB_DIAG` (hexagons.hl:1947). The six diagonal classes of
`scs_6I1`, routed through `STAB_MOD`/`STAB_SYM`/`Nat.mod_eq_of_lt`. -/
theorem EXPAND_STAB_DIAG :
    {x | ∃ i j, (i % 6 = (j % 6 + 2) % 6 ∨ i % 6 = (j % 6 + 3) % 6 ∨
          j % 6 = (i % 6 + 2) % 6 ∨ j % 6 = (i % 6 + 3) % 6) ∧
        x = scsStabDiagV39 scs6I1 (i % 6) (j % 6)} =
      {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 2) i} ∪
        {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 3) i} := by
  ext x
  constructor
  · rintro ⟨i, j, hd4, rfl⟩
    have hzj : j % 6 < 6 := Nat.mod_lt j (by omega)
    have hzi : i % 6 < 6 := Nat.mod_lt i (by omega)
    rcases hd4 with h | h | h | h
    · refine Set.mem_union_left _ ⟨j % 6, hzj, ?_⟩
      rw [h, stab_mod_lt_p20 (j % 6 + 2) (j % 6) (Nat.mod_mod j 6)]
    · refine Set.mem_union_right _ ⟨j % 6, hzj, ?_⟩
      rw [h, stab_mod_lt_p20 (j % 6 + 3) (j % 6) (Nat.mod_mod j 6)]
    · refine Set.mem_union_left _ ⟨i % 6, hzi, ?_⟩
      rw [h, STAB_SYM, stab_mod_lt_p20 (i % 6 + 2) (i % 6) (Nat.mod_mod i 6)]
    · refine Set.mem_union_right _ ⟨i % 6, hzi, ?_⟩
      rw [h, STAB_SYM, stab_mod_lt_p20 (i % 6 + 3) (i % 6) (Nat.mod_mod i 6)]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨i + 2, i, Or.inl ?_, ?_⟩
      · rw [Nat.mod_eq_of_lt hi]
      · rw [Nat.mod_eq_of_lt hi]
        exact (stab_mod_lt_p20 (i + 2) i (Nat.mod_eq_of_lt hi)).symm
    · refine ⟨i + 3, i, Or.inr (Or.inl ?_), ?_⟩
      · rw [Nat.mod_eq_of_lt hi]
      · rw [Nat.mod_eq_of_lt hi]
        exact (stab_mod_lt_p20 (i + 3) i (Nat.mod_eq_of_lt hi)).symm

/-- HOL `EQ_DIAG_STAB_6I1_02` (hexagons.hl:1994). `WKEIDFT` at
`(p, q) = (i, i+2)`, `(p', q') = (0, 2)` (so `p' + q = p + q'`), with the
`(i+2, i)` source re-oriented by `STAB_SYM`. -/
theorem EQ_DIAG_STAB_6I1_02 (i : ℕ) :
    scsArrowV39 {scsStabDiagV39 scs6I1 (i + 2) i}
      {scsStabDiagV39 scs6I1 0 2} := by
  have h := WKEIDFT_concl scs6I1 2 (2 * h0) (2 * h0) 6 i (i + 2) 0 2
    SCS_6I1_IS_SCS SCS_6I1_BASIC
    (fun x => a_edge_6I1_p20 x) (fun x => b_edge_6I1_p20 x)
    (by simp)
    (fun x y hxy => (h0_EQ_B_SCS_6I1.2 x y hxy).trans_le two_h0_le_cstab_p20)
    (fun x y hxy => h0_EQ_B_SCS_6I1.2 x y hxy)
    (fun x y hxy => h0_EQ_B_SCS_6I1.1 x y hxy)
  rw [← STAB_SYM scs6I1 i (i + 2)]
  exact h

/-- HOL `EQ_DIAG_STAB_6I1_03` (hexagons.hl:2020). Analogue of
`EQ_DIAG_STAB_6I1_02` for the `(0, 3)` diagonal. -/
theorem EQ_DIAG_STAB_6I1_03 (i : ℕ) :
    scsArrowV39 {scsStabDiagV39 scs6I1 (i + 3) i}
      {scsStabDiagV39 scs6I1 0 3} := by
  have h := WKEIDFT_concl scs6I1 2 (2 * h0) (2 * h0) 6 i (i + 3) 0 3
    SCS_6I1_IS_SCS SCS_6I1_BASIC
    (fun x => a_edge_6I1_p20 x) (fun x => b_edge_6I1_p20 x)
    (by simp)
    (fun x y hxy => (h0_EQ_B_SCS_6I1.2 x y hxy).trans_le two_h0_le_cstab_p20)
    (fun x y hxy => h0_EQ_B_SCS_6I1.2 x y hxy)
    (fun x y hxy => h0_EQ_B_SCS_6I1.1 x y hxy)
  rw [← STAB_SYM scs6I1 i (i + 3)]
  exact h

/-- HOL `SET_EQ_DIAG_STAB_6I1_02` (hexagons.hl:2046). Dichotomy over the
`MMs`-emptiness of the common target; each of the six classes is routed
through its instantiation of `EQ_DIAG_STAB_6I1_02`. -/
theorem SET_EQ_DIAG_STAB_6I1_02 :
    scsArrowV39 {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 2) i}
      {scsStabDiagV39 scs6I1 0 2} := by
  by_cases h02 : MMsV39 (scsStabDiagV39 scs6I1 0 2) = ∅
  · refine ⟨fun s hs => ?_, Or.inl (fun s hs => ?_)⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact (STAB_6I1_SCS 0 2 SCS_DIAG_SCS_6I1_02).1
    · rw [Set.mem_setOf_eq] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      obtain ⟨-, dich⟩ := EQ_DIAG_STAB_6I1_02 i
      rcases dich with h1 | ⟨s2, hmem2, hne2⟩
      · exact h1 _ rfl
      · rw [Set.mem_singleton_iff] at hmem2
        subst hmem2
        exact absurd h02 hne2
  · refine ⟨fun s hs => ?_, Or.inr ⟨scsStabDiagV39 scs6I1 0 2, rfl, h02⟩⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (STAB_6I1_SCS 0 2 SCS_DIAG_SCS_6I1_02).1

/-- HOL `SET_EQ_DIAG_STAB_6I1_03` (hexagons.hl:2077). Analogue of
`SET_EQ_DIAG_STAB_6I1_02` for the `(0, 3)` diagonal. -/
theorem SET_EQ_DIAG_STAB_6I1_03 :
    scsArrowV39 {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 3) i}
      {scsStabDiagV39 scs6I1 0 3} := by
  by_cases h03 : MMsV39 (scsStabDiagV39 scs6I1 0 3) = ∅
  · refine ⟨fun s hs => ?_, Or.inl (fun s hs => ?_)⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact (STAB_6I1_SCS 0 3 SCS_DIAG_SCS_6I1_03).1
    · rw [Set.mem_setOf_eq] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      obtain ⟨-, dich⟩ := EQ_DIAG_STAB_6I1_03 i
      rcases dich with h1 | ⟨s2, hmem2, hne2⟩
      · exact h1 _ rfl
      · rw [Set.mem_singleton_iff] at hmem2
        subst hmem2
        exact absurd h03 hne2
  · refine ⟨fun s hs => ?_, Or.inr ⟨scsStabDiagV39 scs6I1 0 3, rfl, h03⟩⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (STAB_6I1_SCS 0 3 SCS_DIAG_SCS_6I1_03).1

/-- HOL `SET_EQ_DIAG_STAB_6I1` (hexagons.hl:2105). Route each diagonal
class through `SET_STAB_6I1`/`EXPAND_STAB_DIAG` into the two target classes,
then dichotomise over the `MMs`-emptiness of both targets. -/
theorem SET_EQ_DIAG_STAB_6I1 :
    scsArrowV39 {x | ∃ i j, scsDiag 6 i j ∧ x = scsStabDiagV39 scs6I1 i j}
      {scsStabDiagV39 scs6I1 0 2, scsStabDiagV39 scs6I1 0 3} := by
  have key : ∀ x ∈ {x | ∃ i j, scsDiag 6 i j ∧ x = scsStabDiagV39 scs6I1 i j},
      x ∈ {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 2) i} ∪
        {x | ∃ i, i < 6 ∧ x = scsStabDiagV39 scs6I1 (i + 3) i} := by
    rintro x ⟨i, j, hd, hx⟩
    rw [hx]
    have hsm : scsStabDiagV39 scs6I1 i j = scsStabDiagV39 scs6I1 (i % 6) (j % 6) := by
      have h := STAB_MOD scs6I1 i j SCS_6I1_IS_SCS
      rw [show scs6I1.k = 6 from rfl] at h
      exact h.symm
    have hdd : scsDiag 6 (i % 6) (j % 6) := (DIAG_MOD 6 i j (by omega)).mpr hd
    have hz1 : i % 6 < 6 := Nat.mod_lt i (by omega)
    have hz2 : j % 6 < 6 := Nat.mod_lt j (by omega)
    rcases (DIAG_EQ_ADD i j).mp hdd with h | h | h | h
    · refine Set.mem_union_left _ ⟨j % 6, hz2, ?_⟩
      rw [hsm, h, stab_mod_lt_p20 (j % 6 + 2) (j % 6) (Nat.mod_mod j 6)]
    · refine Set.mem_union_right _ ⟨j % 6, hz2, ?_⟩
      rw [hsm, h, stab_mod_lt_p20 (j % 6 + 3) (j % 6) (Nat.mod_mod j 6)]
    · refine Set.mem_union_left _ ⟨i % 6, hz1, ?_⟩
      rw [hsm, h, STAB_SYM, stab_mod_lt_p20 (i % 6 + 2) (i % 6) (Nat.mod_mod i 6)]
    · refine Set.mem_union_right _ ⟨i % 6, hz1, ?_⟩
      rw [hsm, h, STAB_SYM, stab_mod_lt_p20 (i % 6 + 3) (i % 6) (Nat.mod_mod i 6)]
  by_cases h02 : MMsV39 (scsStabDiagV39 scs6I1 0 2) = ∅
  · by_cases h03 : MMsV39 (scsStabDiagV39 scs6I1 0 3) = ∅
    · obtain ⟨is02, dich02⟩ := SET_EQ_DIAG_STAB_6I1_02
      obtain ⟨is03, dich03⟩ := SET_EQ_DIAG_STAB_6I1_03
      unfold scsArrowV39
      refine ⟨fun s hs => ?_, Or.inl (fun s hs => ?_)⟩
      · rw [Set.mem_insert_iff] at hs
        rcases hs with rfl | hs
        · exact is02 _ (by simp)
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact is03 _ rfl
      · rcases key _ hs with hx | hx
        · rcases dich02 with h1 | ⟨s2, hmem2, hne2⟩
          · exact h1 _ hx
          · rw [Set.mem_singleton_iff] at hmem2
            subst hmem2
            exact absurd h02 hne2
        · rcases dich03 with h3 | ⟨s3, hmem3, hne3⟩
          · exact h3 _ hx
          · rw [Set.mem_singleton_iff] at hmem3
            subst hmem3
            exact absurd h03 hne3
    · unfold scsArrowV39
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [Set.mem_insert_iff] at hs
        rcases hs with rfl | hs
        · exact (STAB_6I1_SCS 0 2 SCS_DIAG_SCS_6I1_02).1
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact (STAB_6I1_SCS 0 3 SCS_DIAG_SCS_6I1_03).1
      · apply Or.inr
        apply Exists.intro (scsStabDiagV39 scs6I1 0 3)
        constructor
        · simp
        · exact fun hh => h03 hh
  · unfold scsArrowV39
    refine ⟨fun s hs => ?_, Or.inr (Exists.intro (scsStabDiagV39 scs6I1 0 2) ?_)⟩
    · rw [Set.mem_insert_iff] at hs
      rcases hs with rfl | hs
      · exact (STAB_6I1_SCS 0 2 SCS_DIAG_SCS_6I1_02).1
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact (STAB_6I1_SCS 0 3 SCS_DIAG_SCS_6I1_03).1
    · constructor
      · simp
      · exact fun hh => h02 hh

/-- HOL `OEHDBEN_PRIME` (hexagons.hl:2117). `FZIOTEF_TRANS` through
`{scs_6T1} ∪ {stab i j | diag}`, the two arrows being
`SCS_6I1_BERAK_BY_CSTAB` and `FZIOTEF_UNION (FZIOTEF_REFL scs_6T1)
SET_EQ_DIAG_STAB_6I1`. -/
theorem OEHDBEN_PRIME (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6I1}
      {scs6T1, scsStabDiagV39 scs6I1 0 2, scsStabDiagV39 scs6I1 0 3} := by
  have hrefl : scsArrowV39 {scs6T1} {scs6T1} :=
    FZIOTEF_REFL _ (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact SCS_6T1_IS_SCS)
  have hunion : scsArrowV39 ({scs6T1} ∪ {x | ∃ i j, scsDiag 6 i j ∧
        x = scsStabDiagV39 scs6I1 i j})
      ({scs6T1} ∪ {scsStabDiagV39 scs6I1 0 2, scsStabDiagV39 scs6I1 0 3}) :=
    FZIOTEF_UNION _ _ _ _ hrefl SET_EQ_DIAG_STAB_6I1
  exact FZIOTEF_TRANS _ _ _ (SCS_6I1_BERAK_BY_CSTAB hmn) hunion

/-- HOL `OEHDBEN` (hexagons.hl:2135): the master arrow breaking the hexagon
into the 6T1 / 5M1 / 4M2 / 3M1 terminals. `FZIOTEF_TRANS` through the
`OEHDBEN_PRIME` middle set, then `FZIOTEF_UNION (FZIOTEF_REFL scs_6T1)
(FZIOTEF_UNION AQICLXA FZIOTEF)`. -/
theorem OEHDBEN (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3M1} := by
  have hrefl : scsArrowV39 {scs6T1} {scs6T1} :=
    FZIOTEF_REFL _ (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact SCS_6T1_IS_SCS)
  have hset : (({scs6T1} ∪ ({scs3M1, scs5M1} ∪ {scs4M2}) : Set ScsV39)) =
      {scs6T1, scs5M1, scs4M2, scs3M1} := by
    ext s
    simp [Set.mem_insert_iff]
    tauto
  have hunion : scsArrowV39 ({scs6T1, scsStabDiagV39 scs6I1 0 2,
        scsStabDiagV39 scs6I1 0 3})
      ({scs6T1} ∪ ({scs3M1, scs5M1} ∪ {scs4M2})) :=
    FZIOTEF_UNION _ _ _ _ hrefl (FZIOTEF_UNION _ _ _ _ AQICLXA FZIOTEF)
  rw [hset] at hunion
  exact FZIOTEF_TRANS _ _ _ (OEHDBEN_PRIME hmn) hunion
