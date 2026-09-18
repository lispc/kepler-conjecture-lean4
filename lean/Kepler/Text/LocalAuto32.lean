/-
LocalAuto32 — the ninth micro-file bundle of the appendix-to-Local-Fan
wave (skeleton-first pass). Single source:

  - `scripts/local/MIQMCSN.hl` (3469 ln, 5 defs + 114 thms; the file's
    `SCS_TAC` is a HOL *tactic* (rewrite bag), not a theorem, and is
    absorbed into the Lean `simp [isScsV39, mkUnadornedV39, psort,
    funlistV39, ...]` expansions) — the terminal `MMs`-decay chain:
    the five prime/quasi systems (`scs_3T4_prime2`, `scs_3T3_prime`,
    `scs_3M1_prime`, `scs_4M8_02`, `scs_4M8_13`), their `is_scs` /
    `scs_basic` / `scs_k` / `J`-empty verifications, the
    prime-to-standard `BB`/`MM`/arrow steps for the 3-row systems, the
    `scs_stab_diag` slicing chains for `scs_4M7`/`scs_4M8`, the
    `main_nonlinear_terminal_v11` extremal dichotomies
    (`EXTREMAL_SCS_4M6`, `MIN_NOT_STAND_4M7/4M8`), the 4M6/4M7/4M8
    one-step arrows, and the headline `MIQMCSN`:
    `scs_arrow_v39 {scs_4M8} {scs_4M6', scs_3T7, scs_3T4}`.

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(v i,v j)` <->
  `dist (v i) (v j)`; `&2` <-> `(2:ℝ)`; `#0.513` <-> `0.513`;
  `#3.62` <-> `3.62`; `F` (HOL false) <-> `False`.
- All toolkit defs (`ScsV39`, `isScsV39`, `unadornedV39`,
  `mkUnadornedV39`, `funlistV39`, `psort`, `BBsV39`, `MMsV39`,
  `scsBasicV39`, `scsDiag`, `scsArrowV39`, `scsStabDiagV39`,
  `scsHalfSliceV39`, `scsPropEquV39`, `scsOppV39`, `peropp`,
  `peropp2`, `main_nonlinear_terminal_v11`, the concrete systems
  `scs4T3..scs4M8`) are already ported in `Kepler.Text.LocalAuto1`
  (camelCase); `h0 = 1.26` lives in `Kepler.Text.PackingAuto2`,
  `cstab = 3.01` in `Kepler.Text.LocalAuto1`.
- HOL `scs_k_v39 s` <-> `s.k`; `scs_a_v39 s i j` <-> `s.a i j`;
  `scs_J_v39 s i j` <-> `s.J i j`; `MMs_v39 s = {}` <->
  `MMsV39 s = ∅`; `MMs_v39 s v` <-> `v ∈ MMsV39 s`.
- HOL set-builders `{f i j | scs_diag 4 i j}` <->
  `{s | ∃ i j, scsDiag 4 i j ∧ s = f i j}`; `{a,b,c}` <-> `{a, b, c}`;
  `UNION` <-> `∪`.
- Same-wave workers own LocalAuto28-31/33 (MIQMCSN neighbours); they
  are NOT imported. `scs_3T4_prime` (HIJQAHA.hl:510, not yet ported by
  any earlier lane) is carried here as the `_p32` copy
  `scs3T4Prime_p32` with a NEEDS marker.
- No `native_decide`; proved items are definitional foldings (`rfl`),
  `psort`/`funlistV39` evaluation, and mod/order arithmetic. The
  `is_scs_v39` verifications, the stability kit (`YRTAFYH` consumers)
  and the `main_nonlinear_terminal_v11` giants are `sorry`.

FILE MAP
  Section 0 (defs): `scs3T4Prime2`, `scs3T3Prime`, `scs3M1Prime`,
    `scs4M8_02`, `scs4M8_13` (MIQMCSN.hl:82-116) plus the foreign
    `scs3T4Prime_p32` copy (HIJQAHA.hl:510).
  Section 1 (arithmetic helpers): `PSORT_5_EXPLICIT_p32` (proved),
    `small_nz_p32` (proved), `mod_prep_p32` (proved),
    `suc_ex_p32` (proved).
  Section 2 (IS_SCS): `SCS_4T3_IS_SCS_p32`,
    `SCS_4M8_02_IS_SCS_p32`, `SCS_4M8_13_IS_SCS_p32`,
    `SCS_3T4_prime2_IS_SCS_p32`, `SCS_3T3_prime_IS_SCS_p32`,
    `SCS_3M1_prime_IS_SCS_p32`, `SCS_3T7_IS_SCS_p32` (all sorry).
  Section 3 (BASIC/K/J kit): `*_BASIC_p32` (proved, definitional),
    `K_SCS_*_p32` (proved, rfl), `J_SCS_*_p32` (proved, rfl);
    3T4-prime/3T3-prime/3M1-prime BB/MM/arrow steps (sorry);
    4M7/4M8 stab-diag BB/MM steps (sorry).
  Section 4 (4M7 slices): `SET_STAB_4M7_p32` (proved),
    `EXPAND_STAB_DIAG_4M7_p32`, `SET_EQ_DIAG_STAB_4M7_p32`,
    `SCS_4M7_SLICE_13_p32`, `SCS_4M7_SLICE_13_ARROW_3T4_p32`,
    `SCS_4M7_SLICE_02_p32`, `SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32`,
    `STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32` (sorry).
  Section 5 (4M8 slices): `SET_STAB_4M8_p32` (proved),
    `EXPAND_STAB_DIAG_4M8_p32`, `SET_EQ_DIAG_STAB_4M8_p32`,
    `PROP_OPP_DIAG_4M8_13_p32`, `STAB_4M8_02_ARROW_4M8_13_p32`,
    `SCS_4M8_SLICE_13_p32`, `SCS_4M8_SLICE_13_ARROW_3T4_p32`,
    `SCS_4M8_SLICE_02_ARROW_3T4_p32`, `SET_STAB_4M8_ARROW_3T4_p32`
    (sorry).
  Section 6 (4M6): `h0_LT_B_SCS_4M6_p32` (proved),
    `SCS_4M6_STAND_OR_PRO_p32` (proved), `SCS_4M6_STAND_p32`
    (proved), `h0_CSTAB_LT_4_p32` (proved), `EXTREMAL_SCS_4M6_p32`,
    `BB_4M6_IMP_scs_4T3_p32`, `MM_4M6_IMP_MM_4T3_p32`,
    `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`, `NWDGKXH_p32` (sorry).
  Section 7 (4M7): `h0_LT_B_SCS_4M7_p32` (proved),
    `SCS_4M7_STAND_OR_PRO_p32` (proved), `SCS_4M7_STAND_p32`
    (proved), `MIN_NOT_STAND_4M7_p32` .. `SCS_4M7_ARROW_STAB_4M7_4M6_p32`
    (sorry), `K_SCS_OPP_4M6_p32` (proved),
    `SCS_4M6_OPP_IS_SCS_p32`, `YOBIMPP_p32` (sorry).
  Section 8 (4M8): `h0_LT_B_SCS_4M8_p32` (proved),
    `SCS_4M8_STAND_OR_PRO_p32` (proved), `SCS_4M8_STAND_p32`
    (proved), `MIN_NOT_STAND_4M8_p32` .. `SCS_4M8_ARROW_STEP_ONE_p32`
    (sorry).
  Section 9 (diag + half-slice kit): `SCS_DIAG_SCS_4M8_02_02_p32`,
    `SCS_DIAG_SCS_4M8_02_13_p32`, `SCS_DIAG_SCS_4M8_13_13_p32`
    (proved, decide), `STAB_4M8_02_SCS_p32`, `STAB_4M8_13_SCS_p32`
    (sorry), `BASIC_HALF_SLICE_p32` (proved), `D_HALF_SLICE1_p32`
    (proved), `J_SCS_3T7_OPP_PROP_p32`, `J_SCS_3T7_OPP_p32`
    (proved).
  Section 10 (3T7 chain + MIQMCSN): `SCS_4M8_02_SLICE_02_p32`,
    `SCS_4M8_13_SLICE_13_p32`, `SCS_4M8_13_ARROW_3T7_p32`,
    `K_SCS_OPP_3T7_p32` (proved), `SCS_3T7_OPP_IS_SCS_p32`,
    `SCS_4M8_13_ARROW_3T7_OPP_p32`, `PROP_OPP_4M8_13_p32`,
    `SCS_4M8_02_ARROW_4M8_13_p32`, `SCS_4M8_02_ARROW_3T7_p32`,
    `MIQMCSN_p32` (sorry).

  DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
  HOL input (stability kit / nonlinear terminal / FZIOTEF chains);
  the proved items use definitional folding and arithmetic only.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto20
import Mathlib

set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: the five systems (MIQMCSN.hl:82-116) -/

/-- HOL `scs_3T4_prime2` (MIQMCSN.hl:82). -/
noncomputable def scs3T4Prime2 : ScsV39 :=
  mkUnadornedV39 3 0.2759
    (funlistV39 [((0, 1), 2), ((0, 2), cstab)] (2 * h0) 3)
    (funlistV39 [((0, 1), 2 * h0)] cstab 3)

/-- HOL `scs_3T3_prime` (MIQMCSN.hl:91). -/
noncomputable def scs3T3Prime : ScsV39 :=
  mkUnadornedV39 3 0.476
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    (funlistV39 [] cstab 3)

/-- HOL `scs_3M1_prime` (MIQMCSN.hl:100). -/
noncomputable def scs3M1Prime : ScsV39 :=
  mkUnadornedV39 3 0.103
    (funlistV39 [((0, 1), cstab)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)

/-- HOL `scs_4M8_02` (MIQMCSN.hl:107). -/
noncomputable def scs4M8_02 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 3.62),
      ((1, 3), 6)] 2 4)

/-- HOL `scs_4M8_13` (MIQMCSN.hl:113). -/
noncomputable def scs4M8_13 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6),
      ((1, 3), 3.62)] 2 4)

/-- HOL `scs_3T4_prime` (HIJQAHA.hl:510; `_p32` copy — the Hexagons lane
owns the canonical port; NEEDS Kepler.Text Hijqaha to replace this). -/
noncomputable def scs3T4Prime_p32 : ScsV39 :=
  mkUnadornedV39 3 0.2759
    (funlistV39 [((0, 1), 2), ((1, 2), cstab)] (2 * h0) 3)
    (funlistV39 [((0, 1), 2 * h0)] cstab 3)

/-! ## Section 1: arithmetic helpers (MIQMCSN.hl:120-200) -/

/-- HOL `PSORT_5_EXPLICIT` (MIQMCSN.hl:120). -/
theorem PSORT_5_EXPLICIT_p32 :
    psort 5 (0, 0) = (0, 0) ∧ psort 5 (1, 1) = (1, 1) ∧
    psort 5 (2, 2) = (2, 2) ∧ psort 5 (3, 3) = (3, 3) ∧
    psort 5 (4, 4) = (4, 4) ∧ psort 5 (0, 1) = (0, 1) ∧
    psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧
    psort 5 (0, 4) = (0, 4) ∧ psort 5 (1, 0) = (0, 1) ∧
    psort 5 (1, 2) = (1, 2) ∧ psort 5 (1, 3) = (1, 3) ∧
    psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 0) = (0, 2) ∧
    psort 5 (2, 1) = (1, 2) ∧ psort 5 (2, 3) = (2, 3) ∧
    psort 5 (2, 4) = (2, 4) ∧ psort 5 (3, 0) = (0, 3) ∧
    psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧
    psort 5 (3, 4) = (3, 4) ∧ psort 5 (4, 0) = (0, 4) ∧
    psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
    psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 5) = (0, 4) ∧
    psort 5 (3, 5) = (0, 3) ∧ psort 5 (2, 5) = (0, 2) ∧
    psort 5 (1, 5) = (0, 1) ∧ psort 5 (5, 1) = (0, 1) ∧
    psort 5 (5, 2) = (0, 2) ∧ psort 5 (5, 3) = (0, 3) ∧
    psort 5 (5, 4) = (0, 4) ∧ psort 5 (5, 5) = (0, 0) ∧
    psort 5 (5, 6) = (0, 1) ∧ psort 5 (5, 7) = (0, 2) ∧
    psort 5 (4, 6) = (1, 4) ∧ psort 5 (6, 4) = (1, 4) ∧
    psort 5 (6, 5) = (0, 1) ∧ psort 5 (6, 7) = (1, 2) ∧
    psort 5 (7, 5) = (0, 2) ∧ psort 5 (7, 6) = (1, 2) ∧
    psort 5 (7, 7) = (2, 2) ∧ psort 5 (6, 6) = (1, 1) ∧
    psort 4 (3, 4) = (0, 3) ∧ psort 3 (2, 0) = (0, 2) ∧
    psort 3 (2, 1) = (1, 2) ∧ psort 3 (1, 0) = (0, 1) ∧
    psort 4 (0, 0) = (0, 0) ∧ psort 4 (1, 1) = (1, 1) ∧
    psort 4 (2, 2) = (2, 2) ∧ psort 4 (3, 3) = (3, 3) ∧
    psort 4 (4, 3) = (0, 3) ∧ psort 4 (4, 4) = (0, 0) ∧
    psort 4 (0, 2) = (0, 2) ∧ psort 4 (4, 5) = (0, 1) ∧
    psort 4 (5, 4) = (0, 1) ∧ psort 4 (5, 5) = (1, 1) ∧
    psort 4 (1, 4) = (0, 1) ∧ psort 4 (2, 5) = (1, 2) ∧
    psort 4 (3, 6) = (2, 3) := by
  repeat' constructor

/-- HOL `small_nz` (MIQMCSN.hl:186). -/
theorem small_nz_p32 :
    (1:ℕ) ≠ 0 ∧ (2:ℕ) ≠ 0 ∧ (3:ℕ) ≠ 0 ∧ (4:ℕ) ≠ 0 ∧ (5:ℕ) ≠ 0 ∧ (6:ℕ) ≠ 0 :=
  by decide

/-- HOL `mod_prep` (MIQMCSN.hl:190). -/
theorem mod_prep_p32 (i k : ℕ) :
    i + 3 = 1 * 3 + i ∧ i + 4 = 1 * 4 + i ∧ i + 5 = 1 * 5 + i ∧
    i + 6 = 1 * 6 + i ∧ (1 * k + i + 1) = 1 * k + (i + 1) := by
  constructor <;> omega

/-- HOL `suc_ex` (MIQMCSN.hl:195). -/
theorem suc_ex_p32 :
    (0:ℕ) + 1 = 1 ∧ 1 + 1 = 2 ∧ 2 + 1 = 3 ∧ 3 + 1 = 4 ∧ 4 + 1 = 5 ∧
    5 + 1 = 6 ∧ 6 + 1 = 7 ∧ 7 + 1 = 8 := by
  decide

/-! ### `_p32` substrate: `funlist_v39` mod invariance -/

/-- `funlist_v39` only sees its indices through `psort k`, hence is
mod-`k` invariant in both arguments (HOL `CHANGE_A_SCS_MOD` kit). -/
theorem funlist_mod_p32 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ)
    (hk : k ≠ 0) :
    funlistV39 data d k i j = funlistV39 data d k (i % k) (j % k) := by
  unfold funlistV39
  rw [PSORT_MOD k i j hk, Nat.mod_mod i k, Nat.mod_mod j k]

/-- Mod-`k` invariance along a step edge `(i, i + 1)`. -/
theorem funlist_step_mod_p32 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i : ℕ)
    (hk : k ≠ 0) :
    funlistV39 data d k i (i + 1) = funlistV39 data d k (i % k) (i % k + 1) := by
  unfold funlistV39
  rw [(PSORT_MOD k i (i + 1) hk).symm,
    (Nat.ModEq.add (Nat.mod_modEq i k) (Nat.ModEq.refl 1)).symm,
    (PSORT_MOD k (i % k) (i % k + 1) hk).symm,
    Nat.mod_mod i k]

/-! ## Section 2: `is_scs_v39` verifications (MIQMCSN.hl:213-840) -/

/-- HOL `SCS_4T3_IS_SCS` (MIQMCSN.hl:213). -/
theorem SCS_4T3_IS_SCS_p32 : isScsV39 scs4T3 := by
  sorry
  -- NEEDS: hexagons-style SCS_TAC expansion of `is_scs_v39 scs_4T3`
  -- (22-conjunct unfolding: periodicity/symmetry via PSORT_MOD,
  -- FUNLIST_EXPLICIT; card bound needs ncard = 2 on the a-edge set).

/-- HOL `SCS_4M8_02_IS_SCS` (MIQMCSN.hl:320). -/
theorem SCS_4M8_02_IS_SCS_p32 : isScsV39 scs4M8_02 := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_4M8_02` (as above).

/-- HOL `SCS_4M8_13_IS_SCS` (MIQMCSN.hl:434). -/
theorem SCS_4M8_13_IS_SCS_p32 : isScsV39 scs4M8_13 := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_4M8_13` (as above).

/-- HOL `SCS_3T4_prime2_IS_SCS` (MIQMCSN.hl:549). -/
theorem SCS_3T4_prime2_IS_SCS_p32 : isScsV39 scs3T4Prime2 := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_3T4_prime2` (as above).

/-- HOL `SCS_3T3_prime_IS_SCS` (MIQMCSN.hl:621). -/
theorem SCS_3T3_prime_IS_SCS_p32 : isScsV39 scs3T3Prime := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_3T3_prime` (as above).

/-- HOL `SCS_3M1_prime_IS_SCS` (MIQMCSN.hl:694). -/
theorem SCS_3M1_prime_IS_SCS_p32 : isScsV39 scs3M1Prime := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_3M1_prime` (as above).

/-- HOL `SCS_3T7_IS_SCS` (MIQMCSN.hl:766). -/
theorem SCS_3T7_IS_SCS_p32 : isScsV39 scs3T7 := by
  sorry
  -- NEEDS: SCS_TAC expansion of `is_scs_v39 scs_3T7` (as above).

/-! ## Section 3: BASIC / K / J kit (MIQMCSN.hl:841-916) -/

/-- HOL `SCS_3T4_prime2_BASIC` (MIQMCSN.hl:841). -/
theorem SCS_3T4_prime2_BASIC_p32 : scsBasicV39 scs3T4Prime2 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_3T4_prime2` (MIQMCSN.hl:844). -/
theorem K_SCS_3T4_prime2_p32 : scs3T4Prime2.k = 3 := rfl

/-- HOL `J_SCS_3T4_prime2` (MIQMCSN.hl:847). -/
theorem J_SCS_3T4_prime2_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T4Prime2 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T4_prime2_1` (MIQMCSN.hl:850). -/
theorem J_SCS_3T4_prime2_1_p32 (i1 j : ℕ) :
    scs3T4Prime2.J i1 j = False := rfl

/-- HOL `SCS_3T7_BASIC` (MIQMCSN.hl:853). -/
theorem SCS_3T7_BASIC_p32 : scsBasicV39 scs3T7 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_3T7` (MIQMCSN.hl:856). -/
theorem K_SCS_3T7_p32 : scs3T7.k = 3 := rfl

/-- HOL `J_SCS_3T7` (MIQMCSN.hl:859). -/
theorem J_SCS_3T7_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T7 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T7_1` (MIQMCSN.hl:864). -/
theorem J_SCS_3T7_1_p32 (i1 j : ℕ) :
    scs3T7.J i1 j = False := rfl

/-- HOL `SCS_3T3_prime_BASIC` (MIQMCSN.hl:867). -/
theorem SCS_3T3_prime_BASIC_p32 : scsBasicV39 scs3T3Prime :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_3T3_prime` (MIQMCSN.hl:870). -/
theorem K_SCS_3T3_prime_p32 : scs3T3Prime.k = 3 := rfl

/-- HOL `J_SCS_3T3_prime` (MIQMCSN.hl:873). -/
theorem J_SCS_3T3_prime_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T3Prime i).J i1 j = False := rfl

/-- HOL `SCS_3M1_prime_BASIC` (MIQMCSN.hl:877). -/
theorem SCS_3M1_prime_BASIC_p32 : scsBasicV39 scs3M1Prime :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_3M1_prime` (MIQMCSN.hl:880). -/
theorem K_SCS_3M1_prime_p32 : scs3M1Prime.k = 3 := rfl

/-- HOL `J_SCS_3M1_prime` (MIQMCSN.hl:883). -/
theorem J_SCS_3M1_prime_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs3M1Prime i).J i1 j = False := rfl

/-- HOL `SCS_4T3_BASIC` (MIQMCSN.hl:887). -/
theorem SCS_4T3_BASIC_p32 : scsBasicV39 scs4T3 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4T3` (MIQMCSN.hl:890). -/
theorem K_SCS_4T3_p32 : scs4T3.k = 4 := rfl

/-- HOL `J_SCS_4T3` (MIQMCSN.hl:893). -/
theorem J_SCS_4T3_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs4T3 i).J i1 j = False := rfl

/-- HOL `SCS_4M8_02_BASIC` (MIQMCSN.hl:897). -/
theorem SCS_4M8_02_BASIC_p32 : scsBasicV39 scs4M8_02 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4M8_02` (MIQMCSN.hl:900). -/
theorem K_SCS_4M8_02_p32 : scs4M8_02.k = 4 := rfl

/-- HOL `J_SCS_4M8_02` (MIQMCSN.hl:903). -/
theorem J_SCS_4M8_02_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M8_02 i).J i1 j = False := rfl

/-- HOL `SCS_4M8_13_BASIC` (MIQMCSN.hl:907). -/
theorem SCS_4M8_13_BASIC_p32 : scsBasicV39 scs4M8_13 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4M8_13` (MIQMCSN.hl:910). -/
theorem K_SCS_4M8_13_p32 : scs4M8_13.k = 4 := rfl

/-- HOL `J_SCS_4M8_13` (MIQMCSN.hl:913). -/
theorem J_SCS_4M8_13_p32 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M8_13 i).J i1 j = False := rfl

/-! ### 3-row prime-to-standard steps (MIQMCSN.hl:918-1075) -/

/-- HOL `BB_3T4_prime2_IMP_scs_3T4` (MIQMCSN.hl:918). -/
theorem BB_3T4_prime2_IMP_scs_3T4_p32 (v : ℕ → V3)
    (h : BBsV39 scs3T4Prime2 v) : BBsV39 scs3T4 v := by
  sorry
  -- NEEDS: FUNLIST_EXPLICIT pointwise re-index of `BBs_v39` +
  -- `scs_3T4_prime2 → scs_3T4` table comparison (SCS_TAC +
  -- K_SCS_3T4_prime2_p32 / SCS_3T4_IS_SCS).

/-- HOL `MM_3T4_prime2_IMP_MM_3T4` (MIQMCSN.hl:931). -/
theorem MM_3T4_prime2_IMP_MM_3T4_p32 (v : ℕ → V3)
    (h : v ∈ MMsV39 scs3T4Prime2) : MMsV39 scs3T4 ≠ ∅ := by
  sorry
  -- NEEDS: Ppbtydq.XWNHLMD_MM + Nuxcoea.MMS_IMP_BBS +
  -- BB_3T4_prime2_IMP_scs_3T4_p32 + the IS_SCS/BASIC kit above.

/-- HOL `SCS_3T4_prime2_ARROW_MM_3T4` (MIQMCSN.hl:943). -/
theorem SCS_3T4_prime2_ARROW_MM_3T4_p32 :
    scsArrowV39 {scs3T4Prime2} {scs3T4} := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + SCS_4T3_IS_SCS + MM_3T4_prime2
  -- case split (XWNHLMD_MM chain).

/-- HOL `BB_3T3_prime_IMP_scs_3T3` (MIQMCSN.hl:973). -/
theorem BB_3T3_prime_IMP_scs_3T3_p32 (v : ℕ → V3)
    (h : BBsV39 scs3T3Prime v) : BBsV39 scs3T3 v := by
  sorry
  -- NEEDS: FUNLIST_EXPLICIT pointwise re-index of `BBs_v39`
  -- (3T3_prime → 3T3 table comparison).

/-- HOL `MM_3T3_prime_IMP_MM_3T3` (MIQMCSN.hl:985). -/
theorem MM_3T3_prime_IMP_MM_3T3_p32 (v : ℕ → V3)
    (h : v ∈ MMsV39 scs3T3Prime) : MMsV39 scs3T3 ≠ ∅ := by
  sorry
  -- NEEDS: XWNHLMD_MM + MMS_IMP_BBS + BB_3T3_prime_IMP_scs_3T3_p32.

/-- HOL `SCS_3T3_prime_ARROW_MM_3T3` (MIQMCSN.hl:996). -/
theorem SCS_3T3_prime_ARROW_MM_3T3_p32 :
    scsArrowV39 {scs3T3Prime} {scs3T3} := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + SCS_3T3_IS_SCS + MM_3T3_prime
  -- case split.

/-- HOL `BB_3M1_prime_IMP_scs_3M1` (MIQMCSN.hl:1024). -/
theorem BB_3M1_prime_IMP_scs_3M1_p32 (v : ℕ → V3)
    (h : BBsV39 scs3M1Prime v) : BBsV39 scs3M1 v := by
  sorry
  -- NEEDS: FUNLIST_EXPLICIT pointwise re-index of `BBs_v39`
  -- (3M1_prime → 3M1 table comparison).

/-- HOL `MM_3M1_prime_IMP_MM_3M1` (MIQMCSN.hl:1036). -/
theorem MM_3M1_prime_IMP_MM_3M1_p32 (v : ℕ → V3)
    (h : v ∈ MMsV39 scs3M1Prime) : MMsV39 scs3M1 ≠ ∅ := by
  sorry
  -- NEEDS: XWNHLMD_MM + MMS_IMP_BBS + BB_3M1_prime_IMP_scs_3M1_p32.

/-- HOL `SCS_3M1_prime_ARROW_MM_3M1` (MIQMCSN.hl:1047). -/
theorem SCS_3M1_prime_ARROW_MM_3M1_p32 :
    scsArrowV39 {scs3M1Prime} {scs3M1} := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + SCS_3M1_IS_SCS + MM_3M1_prime
  -- case split.

/-! ### 4M7 stab-diag BB/MM steps (MIQMCSN.hl:1077-1130) -/

/-- HOL `BB_4M7_IMP_BB_STAN_4M7` (MIQMCSN.hl:1077). -/
theorem BB_4M7_IMP_BB_STAN_4M7_p32 (v : ℕ → V3) (i j : ℕ)
    (h1 : BBsV39 scs4M7 v) (h2 : scsDiag 4 i j)
    (h3 : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M7 i j) v := by
  sorry
  -- NEEDS: BBs_v39 + scs_stab_diag_v39 pointwise unfolding
  -- (B_EQ_PSORT on the (i,j) slot) + BB_4M7 hypothesis.

/-- HOL `MM_4M7_IMP_STAB_4M7` (MIQMCSN.hl:1101). -/
theorem MM_4M7_IMP_STAB_4M7_p32 (v : ℕ → V3) (i j : ℕ)
    (h1 : v ∈ MMsV39 scs4M7) (h2 : scsDiag 4 i j)
    (h3 : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M7 i j) ≠ ∅ := by
  sorry
  -- NEEDS: XWNHLMD_MM + MMS_IMP_BBS + BB_4M7_IMP_BB_STAN_4M7_p32.

/-- `_p32` substrate: `scs_stab_diag_v39` is mod-`k` invariant in its
diagonal indices (HOL `STAB_MOD`). -/
theorem stabDiag_mod_p32 (s : ScsV39) (hk : s.k ≠ 0) (i j : ℕ) :
    scsStabDiagV39 s i j = scsStabDiagV39 s (i % s.k) (j % s.k) := by
  have hps : psort s.k (i, j) = psort s.k (i % s.k, j % s.k) :=
    (PSORT_MOD s.k i j hk).symm
  show mkUnadornedV39 s.k s.d s.a
      (fun i' j' => if psort s.k (i, j) = psort s.k (i', j') then cstab
        else s.b i' j') =
    mkUnadornedV39 s.k s.d s.a
      (fun i' j' => if psort s.k (i % s.k, j % s.k) = psort s.k (i', j') then
        cstab else s.b i' j')
  rw [hps]

/-- HOL `K_SCS_4M7` (hexagons.hl; substrate twin used by the stab-diag
slicing below). -/
theorem K_SCS_4M7_p32 : scs4M7.k = 4 := rfl

/-- HOL `SET_STAB_4M7` (MIQMCSN.hl:1120). -/
theorem SET_STAB_4M7_p32 :
    {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M7 i j} =
    {s | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
      s = scsStabDiagV39 scs4M7 (i % 4) (j % 4)} := by
  have h4 : (4:ℕ) ≠ 0 := by omega
  apply Set.ext
  intro s
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    refine ⟨i % 4, j % 4, ?_, ?_⟩
    · have h' := (DIAG_MOD 4 i j h4).mpr hd
      simpa only [Nat.mod_mod] using h'
    · have he := stabDiag_mod_p32 scs4M7 h4 i j
      simp only [Nat.mod_mod, K_SCS_4M7_p32] at he ⊢
      exact he
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i % 4, j % 4, hd, rfl⟩
  -- NEEDS: STAB_MOD + DIAG_MOD (both discharged by `stabDiag_mod_p32`
  -- and the hexagons `DIAG_MOD` twin).

/-- HOL `EXPAND_STAB_DIAG_4M7` (MIQMCSN.hl:1124). -/
theorem EXPAND_STAB_DIAG_4M7_p32 :
    {s | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧
      s = scsStabDiagV39 scs4M7 (i % 4) (j % 4)} =
    {s | ∃ i, i < 4 ∧ s = scsStabDiagV39 scs4M7 (i + 2) i} := by
  sorry
  -- NEEDS: EXPAND_STAB_DIAG_4 (hexagons) — residue enumeration
  -- i%4 ∈ {0,1,2,3} collapsing to the two records (0,2)/(1,3).

/-- HOL `SET_EQ_DIAG_STAB_4M7` (MIQMCSN.hl:1131). -/
theorem SET_EQ_DIAG_STAB_4M7_p32 :
    scsArrowV39 {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M7 i j}
      {scsStabDiagV39 scs4M7 0 2, scsStabDiagV39 scs4M7 1 3} := by
  sorry
  -- NEEDS: EXPAND_STAB_DIAG_4M7_p32 + EXPAND_DIAG_4V + FZIOTEF_UNION.

/-- HOL `SCS_4M7_SLICE_13` (MIQMCSN.hl:1182). -/
theorem SCS_4M7_SLICE_13_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M7 1 3}
      {scsPropEquV39 scs3T4Prime_p32 2, scs3T4Prime2} := by
  sorry
  -- NEEDS: Lkgrqui.LKGRQUI + SCS_DIAG_SCS_4M7_13 (hexagons: 1 3 is a
  -- 4-diagonal) + STAB_4M7_SCS + is_scs_slice_v39 unfolding.

/-- HOL `SCS_4M7_SLICE_13_ARROW_3T4` (MIQMCSN.hl:1308). -/
theorem SCS_4M7_SLICE_13_ARROW_3T4_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M7 1 3} {scs3T4} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_3T4_prime 2, scs_3T4_prime2} +
  -- SCS_4M7_SLICE_13_p32 + SCS_3T4_prime2_ARROW_MM_3T4_p32 +
  -- PRO_EQU_ID1/YXIONXL3 (prop_equ collapse of scs_3T4_prime 2).

/-- HOL `SCS_4M7_SLICE_02` (MIQMCSN.hl:1326). -/
theorem SCS_4M7_SLICE_02_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M7 0 2}
      {scsPropEquV39 scs3T3Prime 1, scsPropEquV39 scs3M1Prime 1} := by
  sorry
  -- NEEDS: Lkgrqui.LKGRQUI + SCS_DIAG_SCS_4M7_02 (hexagons: 0 2 is a
  -- 4-diagonal) + STAB_4M7_SCS + is_scs_slice_v39 unfolding.

/-- HOL `SCS_4M7_SLICE_02_ARROW_3T3_3M1` (MIQMCSN.hl:1454). -/
theorem SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M7 0 2} {scs3T3, scs3M1} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_3T3_prime 1, scs_3M1_prime 1} +
  -- SCS_4M7_SLICE_02_p32 + the two prime ARROW_MM twins + PRO_EQU_ID1.

/-- HOL `STAB_SCS_4M7_ARROW_3T3_3M1_3T4` (MIQMCSN.hl:1484). -/
theorem STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32 :
    scsArrowV39 {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M7 i j}
      {scs3T3, scs3M1, scs3T4} := by
  sorry
  -- NEEDS: SET_EQ_DIAG_STAB_4M7_p32 + FZIOTEF_UNION +
  -- SCS_4M7_SLICE_13_ARROW_3T4_p32 + SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32.

/-! ## Section 5: 4M8 stab-diag slicing (MIQMCSN.hl:1497-1810) -/

/-- HOL `BB_4M8_IMP_BB_STAN_4M8` (MIQMCSN.hl:1497). -/
theorem BB_4M8_IMP_BB_STAN_4M8_p32 (v : ℕ → V3) (i j : ℕ)
    (h1 : BBsV39 scs4M8 v) (h2 : scsDiag 4 i j)
    (h3 : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M8 i j) v := by
  sorry
  -- NEEDS: BBs_v39 + scs_stab_diag_v39 pointwise unfolding
  -- (B_EQ_PSORT on the (i,j) slot) + BB_4M8 hypothesis.

/-- HOL `MM_4M8_IMP_STAB_4M8` (MIQMCSN.hl:1521). -/
theorem MM_4M8_IMP_STAB_4M8_p32 (v : ℕ → V3) (i j : ℕ)
    (h1 : v ∈ MMsV39 scs4M8) (h2 : scsDiag 4 i j)
    (h3 : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M8 i j) ≠ ∅ := by
  sorry
  -- NEEDS: XWNHLMD_MM + MMS_IMP_BBS + BB_4M8_IMP_BB_STAN_4M8_p32.

/-- HOL `SET_STAB_4M8` (MIQMCSN.hl:1539). -/
theorem SET_STAB_4M8_p32 :
    {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M8 i j} =
    {s | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
      s = scsStabDiagV39 scs4M8 (i % 4) (j % 4)} := by
  have h4 : (4:ℕ) ≠ 0 := by omega
  have hk4 : scs4M8.k = 4 := rfl
  apply Set.ext
  intro s
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    refine ⟨i % 4, j % 4, ?_, ?_⟩
    · have h' := (DIAG_MOD 4 i j h4).mpr hd
      simpa only [Nat.mod_mod] using h'
    · have he := stabDiag_mod_p32 scs4M8 h4 i j
      simp only [Nat.mod_mod, hk4] at he ⊢
      exact he
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i % 4, j % 4, hd, rfl⟩

/-- HOL `EXPAND_STAB_DIAG_4M8` (MIQMCSN.hl:1543). -/
theorem EXPAND_STAB_DIAG_4M8_p32 :
    {s | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧
      s = scsStabDiagV39 scs4M8 (i % 4) (j % 4)} =
    {s | ∃ i, i < 4 ∧ s = scsStabDiagV39 scs4M8 (i + 2) i} := by
  sorry
  -- NEEDS: EXPAND_STAB_DIAG_4 (hexagons) — residue enumeration
  -- i%4 ∈ {0,1,2,3} collapsing to the two records (0,2)/(1,3).

/-- HOL `SET_EQ_DIAG_STAB_4M8` (MIQMCSN.hl:1550). -/
theorem SET_EQ_DIAG_STAB_4M8_p32 :
    scsArrowV39 {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M8 i j}
      {scsStabDiagV39 scs4M8 0 2, scsStabDiagV39 scs4M8 1 3} := by
  sorry
  -- NEEDS: EXPAND_STAB_DIAG_4M8_p32 + EXPAND_DIAG_4V + FZIOTEF_UNION.

/-- HOL `PROP_OPP_DIAG_4M8_13` (MIQMCSN.hl:1603). -/
theorem PROP_OPP_DIAG_4M8_13_p32 :
    scsStabDiagV39 scs4M8 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4M8 0 2)) 2 := by
  sorry
  -- NEEDS: scs_inj on the two records + psort/peropp2 mod-4 case work
  -- (PSORT_MOD, MOD_ADD_MOD, FUNLIST_EXPLICIT).

/-- HOL `STAB_4M8_02_ARROW_4M8_13` (MIQMCSN.hl:1637). -/
theorem STAB_4M8_02_ARROW_4M8_13_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M8 0 2} {scsStabDiagV39 scs4M8 1 3} := by
  sorry
  -- NEEDS: PROP_OPP_DIAG_4M8_13_p32 + YXIONXL2 (opp arrow) +
  -- YXIONXL3/OPP_IS_SCS.

/-- HOL `SCS_4M8_SLICE_13` (MIQMCSN.hl:1655). -/
theorem SCS_4M8_SLICE_13_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M8 1 3} {scs3T4Prime2} := by
  sorry
  -- NEEDS: Lkgrqui.LKGRQUI + SCS_DIAG_SCS_4M8_13 +
  -- STAB_4M8_SCS (hexagons) + is_scs_slice_v39 unfolding.

/-- HOL `SCS_4M8_SLICE_13_ARROW_3T4` (MIQMCSN.hl:1784). -/
theorem SCS_4M8_SLICE_13_ARROW_3T4_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M8 1 3} {scs3T4} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_3T4_prime2} + SCS_4M8_SLICE_13_p32 +
  -- SCS_3T4_prime2_ARROW_MM_3T4_p32.

/-- HOL `SCS_4M8_SLICE_02_ARROW_3T4` (MIQMCSN.hl:1792). -/
theorem SCS_4M8_SLICE_02_ARROW_3T4_p32 :
    scsArrowV39 {scsStabDiagV39 scs4M8 0 2} {scs3T4} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_stab_diag_v39 scs_4M8 1 3} +
  -- STAB_4M8_02_ARROW_4M8_13_p32 + SCS_4M8_SLICE_13_ARROW_3T4_p32.

/-- HOL `SET_STAB_4M8_ARROW_3T4` (MIQMCSN.hl:1799). -/
theorem SET_STAB_4M8_ARROW_3T4_p32 :
    scsArrowV39 {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M8 i j}
      {scs3T4} := by
  sorry
  -- NEEDS: SET_EQ_DIAG_STAB_4M8_p32 + FZIOTEF_UNION +
  -- SCS_4M8_SLICE_13_ARROW_3T4_p32 + SCS_4M8_SLICE_02_ARROW_3T4_p32.

/-! ## Section 6: the 4M6 dichotomy (MIQMCSN.hl:1812-2130) -/

/-- HOL `h0_LT_B_SCS_4M6` (MIQMCSN.hl:1812). -/
theorem h0_LT_B_SCS_4M6_p32 :
    (∀ i j, scsDiag 4 i j → 4 * h0 < scs4M6'.b i j) ∧
    (∀ i j, scsDiag 4 i j → scs4M6'.a i j ≤ cstab) := by
  have hb : ∀ i j, scs4M6'.b i j = scs4M6'.b (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i j =
      funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 (i % 4) (j % 4)
    exact funlist_mod_p32
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i j (by omega)
  have ha : ∀ i j, scs4M6'.a i j = scs4M6'.a (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 (i % 4) (j % 4)
    exact funlist_mod_p32
      [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j (by omega)
  constructor
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [hb]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M6', mkUnadornedV39, funlistV39, psort, assocdV39, h0]
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [ha]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M6', mkUnadornedV39, funlistV39, psort, assocdV39, cstab]

/-- HOL `SCS_4M6_STAND_OR_PRO` (MIQMCSN.hl:1825). -/
theorem SCS_4M6_STAND_OR_PRO_p32 (i : ℕ) :
    scs4M6'.a i (i + 1) = 2 ∧ scs4M6'.b i (i + 1) = 2 * h0 ∨
    scs4M6'.a i (i + 1) = 2 * h0 ∧ scs4M6'.b i (i + 1) = cstab := by
  have ha : scs4M6'.a i (i + 1) = scs4M6'.a (i % 4) (i % 4 + 1) := by
    show funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i (i + 1) =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 (i % 4)
        (i % 4 + 1)
    exact funlist_step_mod_p32
      [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i (by omega)
  have hb : scs4M6'.b i (i + 1) = scs4M6'.b (i % 4) (i % 4 + 1) := by
    show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i (i + 1) =
      funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 (i % 4)
        (i % 4 + 1)
    exact funlist_step_mod_p32
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 i (by omega)
  rw [ha, hb]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
  interval_cases i % 4 <;> simp [scs4M6', mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `SCS_4M6_STAND` (MIQMCSN.hl:1844). -/
theorem SCS_4M6_STAND_p32 :
    scs4M6'.a 1 2 = 2 ∧ scs4M6'.a 2 3 = 2 ∧ scs4M6'.a 3 4 = 2 ∧
    scs4M6'.a 0 1 = 2 * h0 ∧ scs4M6'.a 1 4 = 2 * h0 ∧
    scs4M6'.b 0 1 = cstab := by
  simp [scs4M6', mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `h0_CSTAB_LT_4` (MIQMCSN.hl:1850). -/
theorem h0_CSTAB_LT_4_p32 :
    2 < 2 * h0 ∧ cstab < 4 ∧ 2 ≤ 2 * h0 ∧ cstab ≤ 4 ∧ 2 * h0 < 4 ∧
    2 < 4 ∧ 2 * h0 ≠ 2 := by
  norm_num [h0, cstab]

/-- HOL `EXTREMAL_SCS_4M6` (MIQMCSN.hl:1855). -/
theorem EXTREMAL_SCS_4M6_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M6' →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 1) (v 2) = 2 ∧ dist (v 2) (v 3) = 2 ∧
    dist (v 3) (v 0) = 2 ∧ dist (v 0) (v 1) = cstab := by
  sorry
  -- NEEDS: main_nonlinear_terminal_v11 + MMS_IMP_BBS + BB_VV_FUN_EQ
  -- + SCS_4M6_STAND_OR_PRO_p32 + VASYYAU (str case split).

/-- HOL `BB_4M6_IMP_scs_4T3` (MIQMCSN.hl:1992). -/
theorem BB_4M6_IMP_scs_4T3_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M6' →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    BBsV39 scs4T3 v := by
  sorry
  -- NEEDS: EXTREMAL_SCS_4M6_p32 + BBs_v39 pointwise table match
  -- (FUNLIST_EXPLICIT on scs_4T3 vs the extremal distances).

/-- HOL `MM_4M6_IMP_MM_4T3` (MIQMCSN.hl:2031). -/
theorem MM_4M6_IMP_MM_4T3_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M6' →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    MMsV39 scs4T3 ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M6_IMP_scs_4T3_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `SCS_4M6_ARROW_SCS_4T3_STAB_4M6` (MIQMCSN.hl:2048). -/
theorem SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 :
    main_nonlinear_terminal_v11 →
    scsArrowV39 {scs4M6'}
      ({scs4T3} ∪ {s | ∃ i j, scsDiag 4 i j ∧
        s = scsStabDiagV39 scs4M6' i j}) := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + EXTREMAL_SCS_4M6_p32 (dist on
  -- diagonals) + STAB_MOD/YRTAFYH kit on the stab branch.

/-- HOL `NWDGKXH` (MIQMCSN.hl:2110). -/
theorem NWDGKXH_p32 :
    main_nonlinear_terminal_v11 → scsArrowV39 {scs4M6'} {scs4T3, scs4T5} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via ({scs_4T3} ∪ stab-diag set) +
  -- SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 + hexagons arrow
  -- stab-diag-of-4M6 → {scs_4T3, scs_4T5}.

/-! ## Section 7: the 4M7 dichotomy (MIQMCSN.hl:2130-2490) -/

/-- HOL `h0_LT_B_SCS_4M7` (MIQMCSN.hl:2130). -/
theorem h0_LT_B_SCS_4M7_p32 :
    (∀ i j, scsDiag 4 i j → 4 * h0 < scs4M7.b i j) ∧
    (∀ i j, scsDiag 4 i j → scs4M7.a i j ≤ cstab) := by
  have hb : ∀ i j, scs4M7.b i j = scs4M7.b (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6),
        ((1, 3), 6)] (2 * h0) 4 i j =
      funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6),
        ((1, 3), 6)] (2 * h0) 4 (i % 4) (j % 4)
    exact funlist_mod_p32 _ _ _ _ _ (by omega)
  have ha : ∀ i j, scs4M7.a i j = scs4M7.a (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab),
        ((1, 3), cstab)] 2 4 i j =
      funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab),
        ((1, 3), cstab)] 2 4 (i % 4) (j % 4)
    exact funlist_mod_p32 _ _ _ _ _ (by omega)
  constructor
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [hb]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M7, mkUnadornedV39, funlistV39, psort, assocdV39, h0]
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [ha]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M7, mkUnadornedV39, funlistV39, psort, assocdV39, cstab]

/-- HOL `SCS_4M7_STAND_OR_PRO` (MIQMCSN.hl:2143). -/
theorem SCS_4M7_STAND_OR_PRO_p32 (i : ℕ) :
    scs4M7.a i (i + 1) = 2 ∧ scs4M7.b i (i + 1) = 2 * h0 ∨
    scs4M7.a i (i + 1) = 2 * h0 ∧ scs4M7.b i (i + 1) = cstab := by
  have ha : scs4M7.a i (i + 1) = scs4M7.a (i % 4) (i % 4 + 1) :=
    funlist_step_mod_p32
      [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4
      i (by omega)
  have hb : scs4M7.b i (i + 1) = scs4M7.b (i % 4) (i % 4 + 1) :=
    funlist_step_mod_p32
      [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6), ((1, 3), 6)]
      (2 * h0) 4 i (by omega)
  rw [ha, hb]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
  interval_cases i % 4 <;> simp [scs4M7, mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `SCS_4M7_STAND` (MIQMCSN.hl:2160). -/
theorem SCS_4M7_STAND_p32 :
    scs4M7.a 0 1 = 2 * h0 ∧ scs4M7.a 1 2 = 2 * h0 ∧ scs4M7.a 2 5 = 2 * h0 ∧
    scs4M7.b 1 2 = cstab ∧ scs4M7.b 0 1 = cstab := by
  simp [scs4M7, mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `MIN_NOT_STAND_4M7` (MIQMCSN.hl:2166). -/
theorem MIN_NOT_STAND_4M7_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M7 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 1) (v 2) = 2 * h0 ∨ dist (v 0) (v 1) = 2 * h0 := by
  sorry
  -- NEEDS: main_nonlinear_terminal_v11 + MMS_IMP_BBS + BB_VV_FUN_EQ +
  -- SCS_4M7_STAND_OR_PRO_p32 + VASYYAU (str case split).

/-- HOL `BB_4M7_IMP_4M6_12` (MIQMCSN.hl:2226). -/
theorem BB_4M7_IMP_4M6_12_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M7 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 1) (v 2) = 2 * h0 → BBsV39 scs4M6' v := by
  sorry
  -- NEEDS: MIN_NOT_STAND_4M7_p32 + BBs_v39 pointwise table match.

/-- HOL `MM_4M7_IMP_MM_4M6_12` (MIQMCSN.hl:2262). -/
theorem MM_4M7_IMP_MM_4M6_12_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M7 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 1) (v 2) = 2 * h0 → MMsV39 scs4M6' ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M7_IMP_4M6_12_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `BB_4M7_IMP_4M6_01` (MIQMCSN.hl:2283). -/
theorem BB_4M7_IMP_4M6_01_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M7 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = 2 * h0 →
    BBsV39 (scsPropEquV39 (scsOppV39 scs4M6') 1) v := by
  sorry
  -- NEEDS: MIN_NOT_STAND_4M7_p32 + BBs_v39 / scs_opp_v39 /
  -- scs_prop_equ_v39 pointwise re-index.

/-- HOL `MM_4M7_IMP_MM_4M6_01` (MIQMCSN.hl:2327). -/
theorem MM_4M7_IMP_MM_4M6_01_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M7 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = 2 * h0 →
    MMsV39 (scsPropEquV39 (scsOppV39 scs4M6') 1) ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M7_IMP_4M6_01_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `SCS_4M7_ARROW_STAB_4M7_4M6` (MIQMCSN.hl:2361). -/
theorem SCS_4M7_ARROW_STAB_4M7_4M6_p32 :
    main_nonlinear_terminal_v11 →
    scsArrowV39 {scs4M7}
      ({scs4M6', scsPropEquV39 (scsOppV39 scs4M6') 1} ∪
        {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M7 i j}) := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + BB/MM_4M7_IMP_* twins + STAB_MOD /
  -- YRTAFYH kit on the stab branch.

/-- HOL `K_SCS_OPP_4M6` (MIQMCSN.hl:2443). -/
theorem K_SCS_OPP_4M6_p32 : (scsOppV39 scs4M6').k = 4 := rfl

/-- HOL `SCS_4M6_OPP_IS_SCS` (MIQMCSN.hl:2447). -/
theorem SCS_4M6_OPP_IS_SCS_p32 : isScsV39 (scsOppV39 scs4M6') := by
  sorry
  -- NEEDS: hexagons OPP_IS_SCS kit (peropp/peropp2 mod-4 periodicity +
  -- symmetry + ordering + card bound for scs_4M6').

/-- HOL `YOBIMPP` (MIQMCSN.hl:2453). -/
theorem YOBIMPP_p32 :
    main_nonlinear_terminal_v11 →
    scsArrowV39 {scs4M7} {scs4M6', scs3T3, scs3M1, scs3T4} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via SCS_4M7_ARROW_STAB_4M7_4M6_p32 +
  -- STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32 + SCS_OPP_REFL /
  -- YXIONXL2 on scs_prop_equ_v39 (scs_opp_v39 scs_4M6') 1.

/-! ## Section 8: the 4M8 dichotomy (MIQMCSN.hl:2491-3053) -/

/-- HOL `BB_4M8_IMP_4M6_23` (MIQMCSN.hl:2491). -/
theorem BB_4M8_IMP_4M6_23_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 2) (v 3) = 2 * h0 → BBsV39 scs4M6' v := by
  sorry
  -- NEEDS: VASYYAU / main_nonlinear_terminal_v11 + BBs_v39 pointwise
  -- table match (4M8 → 4M6' via the 23-edge rotation).

/-- HOL `MM_4M8_IMP_MM_4M6_23` (MIQMCSN.hl:2527). -/
theorem MM_4M8_IMP_MM_4M6_23_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 2) (v 3) = 2 * h0 → MMsV39 scs4M6' ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M8_IMP_4M6_23_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `BB_4M8_IMP_4M6_01` (MIQMCSN.hl:2548). -/
theorem BB_4M8_IMP_4M6_01_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = 2 * h0 → BBsV39 (scsOppV39 scs4M6') v := by
  sorry
  -- NEEDS: VASYYAU / main_nonlinear_terminal_v11 + BBs_v39 through
  -- scs_opp_v39 (peropp2 re-index).

/-- HOL `MM_4M8_IMP_MM_4M6_01` (MIQMCSN.hl:2594). -/
theorem MM_4M8_IMP_MM_4M6_01_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = 2 * h0 → MMsV39 (scsOppV39 scs4M6') ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M8_IMP_4M6_01_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `h0_LT_B_SCS_4M8` (MIQMCSN.hl:2627). -/
theorem h0_LT_B_SCS_4M8_p32 :
    (∀ i j, scsDiag 4 i j → 4 * h0 < scs4M8.b i j) ∧
    (∀ i j, scsDiag 4 i j → scs4M8.a i j ≤ cstab) := by
  have hb : ∀ i j, scs4M8.b i j = scs4M8.b (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6),
        ((1, 3), 6)] (2 * h0) 4 i j =
      funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6),
        ((1, 3), 6)] (2 * h0) 4 (i % 4) (j % 4)
    exact funlist_mod_p32 _ _ _ _ _ (by omega)
  have ha : ∀ i j, scs4M8.a i j = scs4M8.a (i % 4) (j % 4) := by
    intro i j
    show funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab),
        ((1, 3), cstab)] 2 4 i j =
      funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab),
        ((1, 3), cstab)] 2 4 (i % 4) (j % 4)
    exact funlist_mod_p32 _ _ _ _ _ (by omega)
  constructor
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [hb]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M8, mkUnadornedV39, funlistV39, psort, assocdV39, h0]
  · intro i j hd
    have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have h4' : j % 4 < 4 := Nat.mod_lt j (by omega)
    have hr : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    have hs : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    have hi1 : (i + 1) % 4 = (i % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq i 4) (Nat.ModEq.refl 1)).symm
    have hj1 : (j + 1) % 4 = (j % 4 + 1) % 4 :=
      (Nat.ModEq.add (Nat.mod_modEq j 4) (Nat.ModEq.refl 1)).symm
    obtain ⟨hd1, hd2, hd3⟩ := hd
    rw [ha]
    rcases hr with hr | hr | hr | hr <;> rcases hs with hs | hs | hs | hs <;>
      simp only [hr, hs, hi1, hj1] at hd1 hd2 hd3 ⊢ <;>
      first
        | exact absurd trivial hd1
        | exact absurd trivial hd2
        | exact absurd trivial hd3
        | norm_num [scs4M8, mkUnadornedV39, funlistV39, psort, assocdV39, cstab]

/-- HOL `SCS_4M8_STAND_OR_PRO` (MIQMCSN.hl:2640). -/
theorem SCS_4M8_STAND_OR_PRO_p32 (i : ℕ) :
    scs4M8.a i (i + 1) = 2 ∧ scs4M8.b i (i + 1) = 2 * h0 ∨
    scs4M8.a i (i + 1) = 2 * h0 ∧ scs4M8.b i (i + 1) = cstab := by
  have ha : scs4M8.a i (i + 1) = scs4M8.a (i % 4) (i % 4 + 1) :=
    funlist_step_mod_p32
      [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4
      i (by omega)
  have hb : scs4M8.b i (i + 1) = scs4M8.b (i % 4) (i % 4 + 1) :=
    funlist_step_mod_p32
      [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6), ((1, 3), 6)]
      (2 * h0) 4 i (by omega)
  rw [ha, hb]
  have h4 : i % 4 < 4 := Nat.mod_lt i (by omega)
  interval_cases i % 4 <;> simp [scs4M8, mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `SCS_4M8_STAND` (MIQMCSN.hl:2659). -/
theorem SCS_4M8_STAND_p32 :
    scs4M8.a 0 1 = 2 * h0 ∧ scs4M8.a 1 2 = 2 ∧ scs4M8.a 2 5 = 2 ∧
    scs4M8.b 1 2 = 2 * h0 ∧ scs4M8.b 0 1 = cstab ∧ scs4M8.a 2 3 = 2 * h0 ∧
    scs4M8.a 3 4 = 2 ∧ scs4M8.b 2 3 = cstab ∧ scs4M8.a 1 4 = 2 * h0 ∧
    scs4M8.a 3 6 = 2 * h0 := by
  simp [scs4M8, mkUnadornedV39, funlistV39, psort, assocdV39]

/-- HOL `MIN_NOT_STAND_4M8` (MIQMCSN.hl:2669). -/
theorem MIN_NOT_STAND_4M8_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 2) (v 3) = 2 * h0 ∨ dist (v 0) (v 1) = 2 * h0 ∨
    (dist (v 0) (v 1) = cstab ∧ dist (v 1) (v 2) = 2 ∧
      dist (v 2) (v 3) = cstab ∧ dist (v 3) (v 0) = 2) := by
  sorry
  -- NEEDS: main_nonlinear_terminal_v11 + MMS_IMP_BBS + BB_VV_FUN_EQ +
  -- SCS_4M8_STAND_OR_PRO_p32 + SCS_4M8_STAND_p32 + VASYYAU.

/-- HOL `BB_4M8_IMP_scs_4M8_02` (MIQMCSN.hl:2757). -/
theorem BB_4M8_IMP_scs_4M8_02_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = cstab → dist (v 1) (v 2) = 2 →
    dist (v 2) (v 3) = cstab → dist (v 3) (v 0) = 2 →
    dist (v 0) (v 2) ≤ 3.62 → BBsV39 scs4M8_02 v := by
  sorry
  -- NEEDS: MIN_NOT_STAND_4M8_p32 + BBs_v39 pointwise table match
  -- (FUNLIST_EXPLICIT on scs_4M8_02).

/-- HOL `MM_4M8_IMP_MM_4M8_02` (MIQMCSN.hl:2796). -/
theorem MM_4M8_IMP_MM_4M8_02_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = cstab → dist (v 1) (v 2) = 2 →
    dist (v 2) (v 3) = cstab → dist (v 3) (v 0) = 2 →
    dist (v 0) (v 2) ≤ 3.62 → MMsV39 scs4M8_02 ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M8_IMP_scs_4M8_02_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `BB_4M8_IMP_scs_4M8_13` (MIQMCSN.hl:2814). -/
theorem BB_4M8_IMP_scs_4M8_13_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = cstab → dist (v 1) (v 2) = 2 →
    dist (v 2) (v 3) = cstab → dist (v 3) (v 0) = 2 →
    dist (v 1) (v 3) ≤ 3.62 → BBsV39 scs4M8_13 v := by
  sorry
  -- NEEDS: MIN_NOT_STAND_4M8_p32 + BBs_v39 pointwise table match
  -- (FUNLIST_EXPLICIT on scs_4M8_13).

/-- HOL `MM_4M8_IMP_MM_4M8_13` (MIQMCSN.hl:2853). -/
theorem MM_4M8_IMP_MM_4M8_13_p32 :
    main_nonlinear_terminal_v11 → ∀ v : ℕ → V3, v ∈ MMsV39 scs4M8 →
    (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) →
    dist (v 0) (v 1) = cstab → dist (v 1) (v 2) = 2 →
    dist (v 2) (v 3) = cstab → dist (v 3) (v 0) = 2 →
    dist (v 1) (v 3) ≤ 3.62 → MMsV39 scs4M8_13 ≠ ∅ := by
  sorry
  -- NEEDS: BB_4M8_IMP_scs_4M8_13_p32 + XWNHLMD_MM + MMS_IMP_BBS.

/-- HOL `SCS_4M8_ARROW_STEP_ONE` (MIQMCSN.hl:2874). -/
theorem SCS_4M8_ARROW_STEP_ONE_p32 :
    main_nonlinear_terminal_v11 →
    scsArrowV39 {scs4M8}
      ({scs4M6', scsOppV39 scs4M6', scs4M8_02, scs4M8_13} ∪
        {s | ∃ i j, scsDiag 4 i j ∧ s = scsStabDiagV39 scs4M8 i j}) := by
  sorry
  -- NEEDS: scs_arrow_v39 unfolding + BB/MM_4M8_IMP_* twins + STAB_MOD /
  -- YRTAFYH kit on the stab branch.

/-! ## Section 9: diag + half-slice kit (MIQMCSN.hl:3016-3074) -/

/-- HOL `SCS_DIAG_SCS_4M8_02_02` (MIQMCSN.hl:3016). -/
theorem SCS_DIAG_SCS_4M8_02_02_p32 : scsDiag scs4M8_02.k 0 2 := by
  unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M8_02_13` (MIQMCSN.hl:3020). -/
theorem SCS_DIAG_SCS_4M8_02_13_p32 : scsDiag scs4M8_02.k 1 3 := by
  unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M8_13_13` (MIQMCSN.hl:3024). -/
theorem SCS_DIAG_SCS_4M8_13_13_p32 : scsDiag scs4M8_13.k 1 3 := by
  unfold scsDiag; decide

/-- HOL `STAB_4M8_02_SCS` (MIQMCSN.hl:3029). -/
theorem STAB_4M8_02_SCS_p32 (i j : ℕ) (h : scsDiag scs4M8_02.k i j) :
    isScsV39 (scsStabDiagV39 scs4M8_02 i j) ∧
    scsBasicV39 (scsStabDiagV39 scs4M8_02 i j) := by
  sorry
  -- NEEDS: Yrtafyh.YRTAFYH (stability kit: is_scs + basic preserved by
  -- scs_stab_diag_v39 on a diagonal of an is_scs system).

/-- HOL `STAB_4M8_13_SCS` (MIQMCSN.hl:3042). -/
theorem STAB_4M8_13_SCS_p32 (i j : ℕ) (h : scsDiag scs4M8_13.k i j) :
    isScsV39 (scsStabDiagV39 scs4M8_13 i j) ∧
    scsBasicV39 (scsStabDiagV39 scs4M8_13 i j) := by
  sorry
  -- NEEDS: Yrtafyh.YRTAFYH (as above, for scs_4M8_13).

/-- HOL `BASIC_HALF_SLICE` (MIQMCSN.hl:3054). -/
theorem BASIC_HALF_SLICE_p32 (s : ScsV39) (p q : ℕ) (d' : ℝ)
    (h : scsBasicV39 s) : scsBasicV39 (scsHalfSliceV39 s p q d' False) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro i j
  simp only [scsHalfSliceV39]
  split <;> simp [h.2]

/-- HOL `D_HALF_SLICE1` (MIQMCSN.hl:3059). -/
theorem D_HALF_SLICE1_p32 (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop) :
    (scsHalfSliceV39 s p q d' mkj).d = d' := rfl

/-- HOL `J_SCS_3T7_OPP_PROP` (MIQMCSN.hl:3062). -/
theorem J_SCS_3T7_OPP_PROP_p32 (i i1 j : ℕ) :
    (scsPropEquV39 (scsOppV39 scs3T7) i).J i1 j = False := rfl

/-- HOL `J_SCS_3T7_OPP` (MIQMCSN.hl:3068). -/
theorem J_SCS_3T7_OPP_p32 (i1 j : ℕ) :
    (scsOppV39 scs3T7).J i1 j = False := rfl

/-! ## Section 10: the 3T7 chain and MIQMCSN (MIQMCSN.hl:3075-3469) -/

/-- HOL `SCS_4M8_02_SLICE_02` (MIQMCSN.hl:3075). -/
theorem SCS_4M8_02_SLICE_02_p32 :
    scsArrowV39 {scs4M8_02} {scsPropEquV39 (scsOppV39 scs3T7) 2} := by
  sorry
  -- NEEDS: Lkgrqui.LKGRQUI + SCS_DIAG_SCS_4M8_02_02/_13_p32 +
  -- STAB_4M8_02_SCS_p32 + is_scs_slice_v39 unfolding.

/-- HOL `SCS_4M8_13_SLICE_13` (MIQMCSN.hl:3207). -/
theorem SCS_4M8_13_SLICE_13_p32 :
    scsArrowV39 {scs4M8_13} {scsPropEquV39 scs3T7 1} := by
  sorry
  -- NEEDS: Lkgrqui.LKGRQUI + SCS_DIAG_SCS_4M8_13_13_p32 +
  -- STAB_4M8_13_SCS_p32 + is_scs_slice_v39 unfolding.

/-- HOL `SCS_4M8_13_ARROW_3T7` (MIQMCSN.hl:3336). -/
theorem SCS_4M8_13_ARROW_3T7_p32 :
    scsArrowV39 {scs4M8_13} {scs3T7} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_prop_equ_v39 scs_3T7 1} +
  -- SCS_4M8_13_SLICE_13_p32 + PRO_EQU_ID1/YXIONXL3 collapse.

/-- HOL `K_SCS_OPP_3T7` (MIQMCSN.hl:3346). -/
theorem K_SCS_OPP_3T7_p32 : (scsOppV39 scs3T7).k = 3 := rfl

/-- HOL `SCS_3T7_OPP_IS_SCS` (MIQMCSN.hl:3350). -/
theorem SCS_3T7_OPP_IS_SCS_p32 : isScsV39 (scsOppV39 scs3T7) := by
  sorry
  -- NEEDS: hexagons OPP_IS_SCS kit (peropp/peropp2 mod-3 periodicity +
  -- symmetry + ordering + card bound for scs_3T7).

/-- HOL `SCS_4M8_13_ARROW_3T7_OPP` (MIQMCSN.hl:3357). -/
theorem SCS_4M8_13_ARROW_3T7_OPP_p32 :
    scsArrowV39 {scs4M8_02} {scsOppV39 scs3T7} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_4M8_13} + SCS_4M8_02_ARROW_4M8_13_p32
  -- + SCS_4M8_13_ARROW_3T7_p32 + YXIONXL2 (opp arrow on scs_3T7).

/-- HOL `PROP_OPP_4M8_13` (MIQMCSN.hl:3377). -/
theorem PROP_OPP_4M8_13_p32 :
    scs4M8_13 = scsPropEquV39 (scsOppV39 scs4M8_02) 2 := by
  sorry
  -- NEEDS: scs_inj on the two records + psort/peropp2 mod-4 case work
  -- (PSORT_MOD, MOD_ADD_MOD, FUNLIST_EXPLICIT).

/-- HOL `SCS_4M8_02_ARROW_4M8_13` (MIQMCSN.hl:3410). -/
theorem SCS_4M8_02_ARROW_4M8_13_p32 :
    scsArrowV39 {scs4M8_02} {scs4M8_13} := by
  sorry
  -- NEEDS: PROP_OPP_4M8_13_p32 + YXIONXL2 (opp arrow) + YXIONXL3 /
  -- OPP_IS_SCS on scs_4M8_02.

/-- HOL `SCS_4M8_02_ARROW_3T7` (MIQMCSN.hl:3428). -/
theorem SCS_4M8_02_ARROW_3T7_p32 :
    scsArrowV39 {scs4M8_02} {scs3T7} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via {scs_4M8_13} + SCS_4M8_02_ARROW_4M8_13_p32
  -- + SCS_4M8_13_ARROW_3T7_p32.

/-- HOL `MIQMCSN` (MIQMCSN.hl:3436). -/
theorem MIQMCSN_p32 :
    main_nonlinear_terminal_v11 →
    scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4} := by
  sorry
  -- NEEDS: FZIOTEF_TRANS via ({scs_4M6', scs_opp_v39 scs_4M6',
  -- scs_4M8_02, scs_4M8_13} ∪ stab-diag set) + SCS_4M8_ARROW_STEP_ONE_p32
  -- + SET_STAB_4M8_ARROW_3T4_p32 + SCS_4M8_02_ARROW_3T7_p32 +
  -- YXIONXL2/SCS_OPP_REFL on scs_opp_v39 scs_4M6'.
