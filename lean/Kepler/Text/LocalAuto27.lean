/-
LocalAuto27 — the eighth micro-file bundle of the appendix-to-Local-Fan
wave (skeleton-first pass). Eight files, 27 theorems:

  - `scripts/local/TFITSKC.hl` (673 ln, 5 thms) — the `MMs` diag bounds
    (`SCS_DIAG_A_LE_DIST`), the a-edge pin `DIST_EQ_2_IMP_A_EQ_2`, the
    step-2 mod-diag `SCS_DIAG_2`, and the `TFITSKCv1`/`TFITSKC` diag
    collapse.
  - `scripts/local/JCYFMRP.hl` (625 ln, 5 thms) — `J_EMPY_CASES_A_EQ_2*`
    (non-adjacent J-emptyness from a-edges = 2), `DIST_EDGE_LE_CSTAB_CASE_LE3`,
    `SCS_M_LE_1`, and the `JCYFMRP` conclusion.
  - `scripts/local/JLXFDMJ.hl` (825 ln, 6 thms) — the `scs_M` cardinality
    kit (`SCS_M_EQ_0`, `FINITE_SCS_M`, `SCS_A_2`, `SCS_M_EQ_1`,
    `SCS_M_LE_K`) and the main `JLXFDMJ`.
  - `scripts/local/SGTRNAF.hl` (191 ln, 2 thms) — `UXCKFPE2`, `SGTRNAF`
    (lower-bound scs telescoping; the packing chapter consumes `SGTRNAF`
    through the regime-ANCHOR `sgtrnaf_p12` in `Kepler.Text.LocalAuto12`).
  - `scripts/local/HXHYTIJ.hl` (131 ln, 1 thm) — the index-dominated
    taustar comparison `HXHYTIJ`.
  - `scripts/local/AYQJTMD.hl` (237 ln, 5 thms) — `XWITCCN2`,
    `unadorned_MMs`, `S_INIT_IS_UNADORNED`, `AYQJTMD`, `EAPGLE` (the
    s_init_list branch of the JEJTVGB registry).
  - `scripts/local/FEKTYIY.hl` (212 ln, 1 thm) — non-coplanarity of an `MMs`
    realisation.
  - `scripts/local/LKGRQUI.hl` (269 ln, 2 thms) — `SLICE_IS_UNADORNED`,
    `LKGRQUI` (arrow to the half-slice pair).

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(v i, v j)` <->
  `dist (v i) (v j)`.
- All toolkit defs (`is_scs_v39`, `scs_M`, `MMs_v39`, `BBs_v39`,
  `BBprime*_v39`, `scs_basic_v39`, `scs_generic`, `scs_diag`,
  `scs_arrow_v39`, `scs_half_slice_v39`, `is_scs_slice_v39`,
  `unadorned_v39`, `s_init_list_v39`, `JEJTVGB_assume_v39`,
  `main_nonlinear_terminal_v11`) are already ported in
  `Kepler.Text.LocalAuto1` (camelCase); this file only adds the `_p27`
  substrate (mod-periodicity folding, mod step/pred arithmetic,
  `sqrt8 ≠ 2`) and the 27 statements.
- `sqrt8` <-> `Real.sqrt 8`; `#1.26` <-> `h0`; `#3.01` <-> `cstab`.
- HOL `CARD` <-> `Set.ncard` (via `scsM`/`scs_M`); `{i | P}` <-> setOf;
  `SUC n` <-> `n + 1`; HOL `={}` <-> `= ∅`.
- Registry twins already carried as axioms in `LocalAuto1` (the `*_concl`
  theorems `HXHYTIJ_concl`..`TFITSKC_concl`) are NOT used to discharge;
  the faithful local statements here are kept independent (`_p27`-suffixed).
- No `native_decide`; the proved items are mechanical (mod/order arithmetic,
  definitional folding of `scsHalfSliceV39`, choice/`min_num` arguments).
  The giants are `sorry`.
- Fill-wave 2026-10-28 (lane la27-eapgle-w2): `EAPGLE_p27` discharged
    (6 sorries remain) via the reified registry-arrow twin `ZITHLQN_p25`
    (new import LocalAuto25, acyclic: it imports LA1/LA23 only) + the
    `AYQJTMD_p27` contrapositive; the axiom face inherits `sorryAx` only
    (see the EAPGLE docstring for the two root families).
- Fill-wave 2026-09-19: `SCS_M_LE_1_p27` and `HXHYTIJ_p27` discharged
    (10 sorries remain). Fill-wave 2026-09-21: `XWITCCN2_p27` and
    `AYQJTMD_p27` discharged (8 sorries remain) via the new Section F1
    `sInitListV39` `isScs` substrate (`s_init_scs_p27` and its `init*` tables,
    including a direct `isScsV39 scs4I3` built off `periodic2_funlist_p20`;
    upstream `XWITCCN` in LocalAuto36 is NOT used). Blocker re-scan:
    `LKGRQUI_concl`/`YXIONXL3_concl`/`CUXVZOZ_concl` still `sorry` in
    LocalAuto1; `XWITCCN` still `sorry` in LocalAuto36; `SCS_M_EQ_1` content
    still missing corpus-wide.

FILE MAP
  Section 0 (`_p27` substrate; see ENCODING): `periodic_mod_p27`,
    `periodic2_mod_p27`, `mod_add_c_p27`, `ne_step_mod_p27`,
    `succ_mod_ne_p27`, `pred_mod_eq_p27`, `sqrt8_ne_2_p27`, plus
    `SCS_A_2_p27` (HOL `SCS_A_2`, JLXFDMJ.hl:148; shared by Sections
    A/B/C).
  Section A (TFITSKC): `SCS_DIAG_A_LE_DIST_p27` (proved),
    `DIST_EQ_2_IMP_A_EQ_2_p27` (proved), `SCS_DIAG_2_p27` (proved),
    `TFITSKCv1_p27` (sorry), `TFITSKC_p27` (sorry).
  Section B (JCYFMRP): `J_EMPY_CASES_A_EQ_2_p27` (proved),
    `DIST_EDGE_LE_CSTAB_CASE_LE3_p27` (proved),
    `J_EMPY_CASES_A_EQ_2_V1_p27` (proved), `SCS_M_LE_1_p27` (proved
    2026-09-19: direct residue pin off the card ≤ 1 split; needs no
    SCS_M_EQ_1), `JCYFMRP_p27` (**PROVED 2026-11-12**, lane jcyfmrp-w2:
    HOL JCYFMRP.hl:256-608 via the DAG-unlocked `CUXVZOZ_p21` (LA21) +
    `SCS_M_LE_1_p27`; J-empty branch through `ODXLSTCv2_p28` (LA28);
    all-flat/lunar forks killed by the private geo kit + `FEKTYIY_p27`;
    axioms = standard three).
  Section C (JLXFDMJ): `SCS_M_EQ_0_p27` (proved), `FINITE_SCS_M_p27`
    (proved), `SCS_M_EQ_1_p27` (proved; singleton instance of `SCS_M_LE_1_p27`),
    `SCS_M_LE_K_p27` (proved), `JLXFDMJ_p27` (sorry; NEEDS the
    `CHANGE_B/A_SCS_MOD` folds plus `SCS_M_EQ_1_p27`, now proved);
    `SCS_A_2_p27` lives in Section 0.
  Section D (SGTRNAF): `UXCKFPE2_p27` (proved 2026-09-18 via
    `UXCKFPE_p24`), `SGTRNAF_p27` (proved 2026-09-18).
  Section E (HXHYTIJ): `HXHYTIJ_p27` (proved 2026-09-19: the
    `min_num`/choice argument done directly over the `BBprime`/`BBindexMin`
    definitions).
  Section F (AYQJTMD): Section F1 = the `sInitListV39` `isScs` substrate
    (`init_pair_01_p27`, `init7a/b_p27`, `init8a/b_p27`,
    `init8_isScs_p27` — `isScsV39 scs4I3` - `s_init_scs_p27`, proved
    2026-09-21; entries 1-6 via `is_scs_*_p22`, entry 7 via
    `SCS_5I3_IS_SCS`); Section F2 = `XWITCCN2_p27` (proved 2026-09-21 via
    `s_init_scs_p27` + `UXCKFPE2_p27` — the earlier NEEDS note about the
    sorried `XWITCCN` in LocalAuto36:1511/LocalAuto1:671 is obsolete),
    `unadorned_MMs_p27` (proved 2026-09-18), `S_INIT_IS_UNADORNED_p27`
    (proved 2026-09-18), `AYQJTMD_p27` (proved 2026-09-21 via
    `SGTRNAF_p27` + `s_init_scs_p27` + `S_INIT_IS_UNADORNED_p27`),
    `EAPGLE_p27` (discharged 2026-10-28, lane la27-eapgle-w2: the HOL
    `ZITHLQN` route — the reified LA25 twin `ZITHLQN_p25` (LocalAuto25,
    supersedes the la27-eapgle-w1 draft's `ZITHLQN_concl` re-route, whose
    LocalAuto1 body is still a blanket `sorry`) + the `AYQJTMD_p27`
    contrapositive; zero new sorries, sorry-inherited axiom face — see the
    EAPGLE docstring).
  Section G (FEKTYIY): `FEKTYIY_p27` (proved 2026-11-05, lane m1a-root-w6).

  Section H (LKGRQUI): `SLICE_IS_UNADORNED_p27` (proved),
    `LKGRQUI_p27` (sorry).

  DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
  HOL input; the proved items use mod/order arithmetic only.
-/

import Kepler.Text.LocalAuto1
-- FEKTYIY (2026-11-05, lane m1a-root-w6): the fan-azimuth engine
-- `AZIM_PI_ITER_LOCAL_FAN_p37` (LA37) and the `interiorAngle1 = azimInFan`
-- identity `LOFA_IMP_INANGLE_EQ_AZIM_p14` (LA14). Acyclic: LA14's closure
-- (71 modules) contains neither LA27 nor LA25.
import Kepler.Text.LocalAuto14
-- Row/capstone import (2026-09-18 fill wave): LocalAuto24 carries the proved
-- `UXCKFPE_p24` case assembly (`BBprimeV39 s ≠ ∅` from `BBs` + `taustar < 0`;
-- its k = 3..6 case lemmas remain `sorry` in that lane). Importability
-- verified empirically: LA24's chain (LA1/LA17/LA20/LA22/LA23) carries no
-- `atn2` conflict with this file's substrate.
import Kepler.Text.LocalAuto24
-- EAPGLE re-route (2026-10-28, lane la27-eapgle-w2): the reified
-- registry-arrow twin `ZITHLQN_p25` (LocalAuto25, wave la27-zithlqn-w1)
-- replaces the still-`sorry` LocalAuto1 arrow `ZITHLQN_concl` on this
-- file's EAPGLE path. Acyclic: LocalAuto25 imports LA1/LA23/Mathlib only.
import Kepler.Text.LocalAuto25
-- JCYFMRP proof wave (2026-11-12, lane jcyfmrp-w2/dagcut-w2): the DAG-cut
-- unlock edge + the one-layer donor modules of `JCYFMRP_p27` (HOL
-- JCYFMRP.hl:256-608).  All verified acyclic from LA27 (closure re-check
-- 2026-11-12): LA21/LA23/LA28/LA31/LA34/LA3/LA5/LA9/ConicCapVolume none
-- reaches LA27.  LA26/LA18 stay unreachable (they import LA27); their
-- content consumed here is inlined (orbit facts via LA37/AzimBridge,
-- flat-arc kit ported under a private name).
import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto28
import Kepler.Text.LocalAuto31
import Kepler.Text.LocalAuto34
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto9
import Kepler.Text.ConicCapVolume
import Kepler.Text.LocalAuto35
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Section 0: `_p27` substrate -/

/-- Mod-periodicity folding for the 1D `Periodic` components of the scs
record (universe-polymorphic twin of LocalAuto20 `periodic_mod_p20`). -/
theorem periodic_mod_p27 {α : Sort u} {f : ℕ → α} (hper : Periodic f n) (i : ℕ) :
    f i = f (i % n) := by
  have key : ∀ m r, f (n * m + r) = f r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
        intro r
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, hper, ih]
  have hI : i = n * (i / n) + i % n := (Nat.div_add_mod i n).symm
  nth_rewrite 1 [hI]
  exact key (i / n) (i % n)

/-- Mod-periodicity folding for the `Periodic2` (matrix) components. -/
theorem periodic2_mod_p27 {α : Sort u} {f : ℕ → ℕ → α} (hper : Periodic2 f n)
    (i j : ℕ) : f i j = f (i % n) (j % n) := by
  have key1 : ∀ m r s, f (n * m + r) s = f r s := by
    intro m
    induction m with
    | zero => intro r s; simp
    | succ m ih =>
        intro r s
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, (hper (n * m + r) s).1, ih]
  have key2 : ∀ m r s, f s (n * m + r) = f s r := by
    intro m
    induction m with
    | zero => intro r s; simp
    | succ m ih =>
        intro r s
        have hE : n * (m + 1) + r = n * m + r + n := by ring
        rw [hE, (hper s (n * m + r)).2, ih]
  have hI : i = n * (i / n) + i % n := (Nat.div_add_mod i n).symm
  have hJ : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  nth_rewrite 1 [hI]
  nth_rewrite 1 [hJ]
  rw [key1 (i / n) (i % n) (n * (j / n) + j % n), key2 (j / n) (j % n) (i % n)]

/-- Folding `(i % k + c) % k` back to `(i + c) % k` for `c < k`. -/
theorem mod_add_c_p27 {k i c : ℕ} (hc : c < k) : (i % k + c) % k = (i + c) % k := by
  have hcmod : c % k = c := Nat.mod_eq_of_lt hc
  calc
    (i % k + c) % k = (i % k + c % k) % k := by rw [hcmod]
    _ = (i + c) % k := (Nat.add_mod i c k).symm

/-- A mod-`k` step of positive size below `k` moves off its residue. -/
theorem ne_step_mod_p27 {k r c : ℕ} : 0 < c → c < k → r < k → r ≠ (r + c) % k := by
  intro hc0 hck hrk
  by_cases h1 : r + c < k
  · intro heq
    have hmod : (r + c) % k = r + c := Nat.mod_eq_of_lt h1
    rw [hmod] at heq
    omega
  · intro heq
    have hge : k ≤ r + c := le_of_not_gt h1
    have hstep : (r + c) % k = r + c - k := by
      have hsub : r + c = k + (r + c - k) := (Nat.add_sub_of_le hge).symm
      calc
        (r + c) % k = (k + (r + c - k)) % k := by
          conv_lhs =>
            rw [hsub]
        _ = (r + c - k) % k := by
          rw [Nat.add_mod, Nat.mod_self]
          rw [zero_add, Nat.mod_mod]
        _ = r + c - k := Nat.mod_eq_of_lt (by omega)
    rw [hstep] at heq
    omega

/-- Successor is injective on `Z/kZ` for `1 < k`. -/
theorem succ_mod_ne_p27 {k i : ℕ} (hk : 1 < k) : i % k ≠ (i + 1) % k := by
  have hkpos : 0 < k := by omega
  have hm : (i + 1) % k = (i % k + 1) % k := by
    rw [Nat.add_mod]
    rw [show 1 % k = 1 by exact Nat.mod_eq_of_lt hk]
  rw [hm]
  exact ne_step_mod_p27 (r := i % k) (c := 1) (by norm_num) hk (Nat.mod_lt i hkpos)

/-- Predecessor cancellation on mod residues below `k > 1`. -/
theorem pred_mod_eq_p27 {k a b : ℕ} : a < k → b < k → 1 < k →
    (a + 1) % k = (b + 1) % k → a = b := by
  intro hak hbk hk h
  by_cases hA : a + 1 = k
  · have h0 : (a + 1) % k = 0 := by rw [hA, Nat.mod_self]
    rw [h0] at h
    have hdisj : b + 1 < k ∨ b + 1 = k := by omega
    rcases hdisj with hblt | hbeq
    · rw [Nat.mod_eq_of_lt hblt] at h
      omega
    · omega
  · have hAlt : a + 1 < k := by omega
    have hAa : (a + 1) % k = a + 1 := Nat.mod_eq_of_lt hAlt
    rw [hAa] at h
    have hdisj : b + 1 < k ∨ b + 1 = k := by omega
    rcases hdisj with hblt | hbeq
    · have hBb : (b + 1) % k = b + 1 := Nat.mod_eq_of_lt hblt
      rw [hBb] at h
      omega
    · rw [hbeq, Nat.mod_self] at h
      omega

/-- `Geomdetail.db_t0_sq8`: `sqrt 8 ≠ 2`. -/
theorem sqrt8_ne_2_p27 : Real.sqrt 8 ≠ 2 := by
  intro h
  have hsq : (Real.sqrt 8) ^ 2 = (8 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

/-- HOL `SCS_A_2` (JLXFDMJ.hl:148): every a-edge is at least 2. Shared by
Sections A/B/C (used by `DIST_EQ_2_IMP_A_EQ_2` below it). -/
theorem SCS_A_2_p27 (s : ScsV39) : isScsV39 s → ∀ i, 2 ≤ s.a i (i + 1) := by
  intro hs i
  obtain ⟨hd, hk1, hk2, lp, hp, sp, sp2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  have hk1' : 1 < s.k := by omega
  have hkpos : 0 < s.k := by omega
  have hmoda := periodic2_mod_p27 hpa i (i + 1)
  rw [hmoda]
  exact hdiag (i % s.k) ((i + 1) % s.k)
    ⟨Nat.mod_lt i hkpos, Nat.mod_lt (i + 1) hkpos, succ_mod_ne_p27 hk1'⟩

/-! ## Section A: TFITSKC -/

/-- HOL `SCS_DIAG_A_LE_DIST` (TFITSKC.hl:94). -/
theorem SCS_DIAG_A_LE_DIST_p27 (s : ScsV39) (v : ℕ → V3) :
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
        4 * h0 < s.b i j) →
      ∀ i j, scsDiag s.k i j → s.a i j < dist (v i) (v j) := by
  intro h i j hd
  obtain ⟨hal, hlt, _⟩ := h i j hd
  nlinarith

/-- HOL `DIST_EQ_2_IMP_A_EQ_2` (TFITSKC.hl:102). -/
theorem DIST_EQ_2_IMP_A_EQ_2_p27 (s : ScsV39) (v : ℕ → V3) (i : ℕ) :
    isScsV39 s → BBsV39 s v → dist (v i) (v (i + 1)) = 2 → s.a i (i + 1) = 2 := by
  intro hs hbb hd
  have h2le : 2 ≤ s.a i (i + 1) := SCS_A_2_p27 s hs i
  have hle : s.a i (i + 1) ≤ dist (v i) (v (i + 1)) := (hbb.2.2.1 i (i + 1)).1
  nlinarith

/-- HOL `SCS_DIAG_2` (TFITSKC.hl:115): the step-2 diag is a genuine
`scs_diag` for `3 < k`. -/
theorem SCS_DIAG_2_p27 (k i : ℕ) : 3 < k → scsDiag k i (i + 2) := by
  intro hk
  have hkpos : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hk2 : 2 < k := by omega
  unfold scsDiag
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hn : i % k ≠ (i % k + 2) % k :=
      ne_step_mod_p27 (r := i % k) (c := 2) (by norm_num) hk2 (Nat.mod_lt i hkpos)
    have hm : (i % k + 2) % k = (i + 2) % k := mod_add_c_p27 (i := i) (c := 2) hk2
    exact hn (heq.trans hm.symm)
  · intro heq
    have hn : (i + 1) % k ≠ ((i + 1) % k + 1) % k :=
      ne_step_mod_p27 (r := (i + 1) % k) (c := 1) (by norm_num) hk1
        (Nat.mod_lt (i + 1) hkpos)
    have hm : ((i + 1) % k + 1) % k = (i + 2) % k :=
      mod_add_c_p27 (i := i + 1) (c := 1) hk1
    exact hn (heq.trans hm.symm)
  · intro heq
    have hn : i % k ≠ (i % k + 3) % k :=
      ne_step_mod_p27 (r := i % k) (c := 3) (by norm_num) hk (Nat.mod_lt i hkpos)
    have hm : (i % k + 3) % k = (i + 3) % k := mod_add_c_p27 (i := i) (c := 3) hk
    exact hn (heq.trans hm.symm)

/-- HOL `TFITSKCv1_concl` (TFITSKC.hl:127). -/
theorem TFITSKCv1_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
        (∀ i', ¬ s.J (i + 2) i') →
          s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) → 3 < s.k → isScsV39 s →
            v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
              s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
                dist (v i) (v (i + 1)) = 2 →
                  dist (v i) (v (i + 1)) < s.b i (i + 1) →
                    (∀ i j, scsDiag s.k i j →
                      s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j) →
                      dist (v (i + 1)) (v (i + 2)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS the diag->strict-inequality nonlinearity
    -- (`CHANGE_A_SCS_MOD` folding + the a,b near-diagonal linear program missing
    -- from the module's port) feeding off `main_nonlinear_terminal_v11`.

/-- HOL `TFITSKC_concl` (TFITSKC.hl:636). Note the registry twin
`TFITSKC_concl` (LocalAuto1) strengthens `s.b (i+1)(i+2) ≤ 2*h0` to `=`; this
statement follows the source (`≤`). -/
theorem TFITSKC_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
        s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) → 3 < s.k → isScsV39 s →
          v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
            s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
              dist (v i) (v (i + 1)) = 2 → 2 < s.b i (i + 1) →
                (∀ i j, scsDiag s.k i j →
                  s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j) →
                  dist (v (i + 1)) (v (i + 2)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS `TFITSKCv1`; the `i'` J-emptyness premise is derived
    -- in the source from `scs_basic_v39` (`scs_J_v39 s (SUC(SUC i)) i' = False`).

/-! ## Section B: JCYFMRP -/

/-- HOL `J_EMPY_CASES_A_EQ_2` (JCYFMRP.hl:93). -/
theorem J_EMPY_CASES_A_EQ_2_p27 (s : ScsV39) :
    (∀ i, s.a i (i + 1) = 2) → isScsV39 s → ∀ i x, ¬ s.J i x := by
  intro hEdge hs
  obtain ⟨hd, hk1, hk2, lp, hp, sp, sp2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  have hk1' : 1 < s.k := by omega
  have hkpos : 0 < s.k := by omega
  intro i x hJ
  have hmod : x % s.k = (i + 1) % s.k ∨ i % s.k = (x + 1) % s.k := hJmod i x hJ
  rcases hmod with hxA | hxB
  · have ha : s.a (i % s.k) (x % s.k) = Real.sqrt 8 := by
      rw [← periodic2_mod_p27 hpa i x]
      exact (hJsq i x hJ).1
    have hsq : s.a (i % s.k) ((i + 1) % s.k) = Real.sqrt 8 := by
      rw [← hxA]
      exact ha
    have hmod1 : ((i % s.k) + 1) % s.k = (i + 1) % s.k :=
      mod_add_c_p27 (i := i) (c := 1) hk1'
    have hrel : s.a (i % s.k) ((i + 1) % s.k) = s.a (i % s.k) ((i % s.k) + 1) := by
      rw [← hmod1]
      have hper := periodic2_mod_p27 hpa (i % s.k) ((i % s.k) + 1)
      rw [Nat.mod_mod] at hper
      exact hper.symm
    have h2 : s.a (i % s.k) ((i % s.k) + 1) = 2 := hEdge (i % s.k)
    have heq : Real.sqrt 8 = 2 := by nlinarith [hsq, hrel, h2]
    exact sqrt8_ne_2_p27 heq
  · have ha : s.a (i % s.k) (x % s.k) = Real.sqrt 8 := by
      rw [← periodic2_mod_p27 hpa i x]
      exact (hJsq i x hJ).1
    rw [hxB] at ha
    have hsymv := (hsym (x % s.k) ((x + 1) % s.k)).1
    have hsq : s.a (x % s.k) ((x + 1) % s.k) = Real.sqrt 8 := hsymv.trans ha
    have hmod1 : ((x % s.k) + 1) % s.k = (x + 1) % s.k :=
      mod_add_c_p27 (i := x) (c := 1) hk1'
    have hrel : s.a (x % s.k) ((x + 1) % s.k) = s.a (x % s.k) ((x % s.k) + 1) := by
      rw [← hmod1]
      have hper := periodic2_mod_p27 hpa (x % s.k) ((x % s.k) + 1)
      rw [Nat.mod_mod] at hper
      exact hper.symm
    have h2 : s.a (x % s.k) ((x % s.k) + 1) = 2 := hEdge (x % s.k)
    have heq : Real.sqrt 8 = 2 := by nlinarith [hsq, hrel, h2]
    exact sqrt8_ne_2_p27 heq

/-- HOL `DIST_EDGE_LE_CSTAB_CASE_LE3` (JCYFMRP.hl:119). -/
theorem DIST_EDGE_LE_CSTAB_CASE_LE3_p27 (s : ScsV39) (v : ℕ → V3) (i : ℕ) :
    3 < s.k → BBsV39 s v → isScsV39 s → dist (v i) (v (i + 1)) ≤ cstab := by
  intro hk hbb hs
  obtain ⟨hd, hk1, hk2, lp, hp, sp, sp2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  have hble : dist (v i) (v (i + 1)) ≤ s.b i (i + 1) := (hbb.2.2.1 i (i + 1)).2
  have hb : s.b i (i + 1) ≤ cstab := hbc i hk
  nlinarith

/-- HOL `J_EMPY_CASES_A_EQ_2_V1` (JCYFMRP.hl:129). -/
theorem J_EMPY_CASES_A_EQ_2_V1_p27 (s : ScsV39) (i : ℕ) :
    s.a i (i + 1) = 2 → s.a (i + 1) (i + 2) = 2 → isScsV39 s →
      ∀ x, ¬ s.J (i + 1) x := by
  intro hA hA2 hs
  obtain ⟨hd, hk1, hk2, lp, hp, sp, sp2, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hs
  have hk1' : 1 < s.k := by omega
  have hkpos : 0 < s.k := by omega
  intro x hJ
  have hmod : x % s.k = (i + 2) % s.k ∨ (i + 1) % s.k = (x + 1) % s.k :=
    hJmod (i + 1) x hJ
  rcases hmod with hxA | hxB
  · have ha : s.a ((i + 1) % s.k) (x % s.k) = Real.sqrt 8 := by
      rw [← periodic2_mod_p27 hpa (i + 1) x]
      exact (hJsq (i + 1) x hJ).1
    have hsq : s.a ((i + 1) % s.k) ((i + 2) % s.k) = Real.sqrt 8 := by
      rw [← hxA]
      exact ha
    have h2' : s.a ((i + 1) % s.k) ((i + 2) % s.k) = 2 := by
      rw [← periodic2_mod_p27 hpa (i + 1) (i + 2)]
      exact hA2
    have heq : Real.sqrt 8 = 2 := by nlinarith [hsq, h2']
    exact sqrt8_ne_2_p27 heq
  · have ha : s.a ((i + 1) % s.k) (x % s.k) = Real.sqrt 8 := by
      rw [← periodic2_mod_p27 hpa (i + 1) x]
      exact (hJsq (i + 1) x hJ).1
    have hmodxy : x % s.k = i % s.k :=
      pred_mod_eq_p27 (Nat.mod_lt x hkpos) (Nat.mod_lt i hkpos) hk1' (by
        calc
          (x % s.k + 1) % s.k = (x + 1) % s.k := mod_add_c_p27 (i := x) (c := 1) hk1'
          _ = (i + 1) % s.k := hxB.symm
          _ = (i % s.k + 1) % s.k := (mod_add_c_p27 (i := i) (c := 1) hk1').symm)
    rw [hmodxy] at ha
    have hsymv := (hsym (i % s.k) ((i + 1) % s.k)).1
    have hsq : s.a (i % s.k) ((i + 1) % s.k) = Real.sqrt 8 := hsymv.trans ha
    have h2' : s.a (i % s.k) ((i + 1) % s.k) = 2 := by
      rw [← periodic2_mod_p27 hpa i (i + 1)]
      exact hA
    have heq : Real.sqrt 8 = 2 := by nlinarith [hsq, h2']
    exact sqrt8_ne_2_p27 heq

/-- HOL `SCS_M_LE_1` (JCYFMRP.hl:162). Note the `p % k` on the RHS is the
HOL form `p MOD scs_k_v39 s`.
DISCHARGED: the `CARD ≤ 1`-branch of the `scs_M` residue extraction done
directly (the source splits on `CARD (scs_M s) = 0` / = 1 and re-uses
SCS_M_EQ_0 / SCS_M_EQ_1): the pinned residue `p` is read off the at-most-one
card bound (`Set.ncard_eq_zero`/`Set.ncard_eq_one` via `FINITE_SCS_M_p27`),
every non-pinned index leaves `scs_M s` by the residue pin, the `scs_M`
negation gives `b ≤ 2*h0 ∧ a ≤ 2` at the folded residues
(`periodic2_mod_p27`), and `SCS_A_2_p27` turns `a ≤ 2` into `a = 2`. -/
theorem SCS_M_LE_1_p27 (s : ScsV39) :
    (scsM s).ncard ≤ 1 → isScsV39 s →
      ∃ p, ∀ i, ¬ (i % s.k = p % s.k) → s.b i (i + 1) ≤ 2 * h0 ∧ s.a i (i + 1) = 2 := by
  intro hcard hs
  have h2 : ∀ i, 2 ≤ s.a i (i + 1) := SCS_A_2_p27 s hs
  obtain ⟨-, hk3, -, -, -, -, -, hpa, -, -, hpb, -, -, -, -, -, -, -, -, -⟩ := hs
  -- `FINITE_SCS_M_p27` (Section C) is only defined below; inlined here.
  have hfin : (scsM s).Finite :=
    (Set.finite_lt_nat s.k).subset (fun i hi => by rw [scsM] at hi; exact hi.1)
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℕ, ∀ q ∈ scsM s, q % s.k = p0 % s.k := by
    by_cases h0 : (scsM s).ncard = 0
    · refine ⟨0, fun q hq => absurd hq ?_⟩
      rw [(Set.ncard_eq_zero hfin).mp h0]
      exact fun hc => hc
    · have h1 : (scsM s).ncard = 1 := by omega
      obtain ⟨q, hq⟩ := Set.ncard_eq_one.mp h1
      refine ⟨q, fun r hr => ?_⟩
      rw [hq, Set.mem_singleton_iff] at hr
      exact congrArg (fun n => n % s.k) hr
  refine ⟨p0, fun i hi => ?_⟩
  have hrk : i % s.k < s.k := Nat.mod_lt i (by omega)
  have hnotkey : i % s.k ∉ scsM s := by
    intro hc
    have hmod : (i % s.k) % s.k = i % s.k := Nat.mod_mod _ _
    have hkey := hp0 (i % s.k) hc
    rw [hmod] at hkey
    exact hi hkey
  simp only [scsM, Set.mem_setOf_eq] at hnotkey
  have hnb : ¬(2 * h0 < s.b (i % s.k) (i % s.k + 1)) := fun hc =>
    hnotkey ⟨hrk, Or.inl hc⟩
  have hna : ¬(2 < s.a (i % s.k) (i % s.k + 1)) := fun hc =>
    hnotkey ⟨hrk, Or.inr hc⟩
  have hstep : (i + 1) % s.k = (i % s.k + 1) % s.k :=
    (mod_add_c_p27 (i := i) (c := 1) (by omega)).symm
  have hbr : s.b (i % s.k) ((i + 1) % s.k) = s.b (i % s.k) (i % s.k + 1) := by
    rw [hstep, periodic2_mod_p27 hpb (i % s.k) (i % s.k + 1), Nat.mod_mod]
  have har : s.a (i % s.k) ((i + 1) % s.k) = s.a (i % s.k) (i % s.k + 1) := by
    rw [hstep, periodic2_mod_p27 hpa (i % s.k) (i % s.k + 1), Nat.mod_mod]
  rw [periodic2_mod_p27 hpb i (i + 1), hbr]
  rw [periodic2_mod_p27 hpa i (i + 1), har]
  exact ⟨not_lt.mp hnb, le_antisymm (not_lt.mp hna) (h2 (i % s.k))⟩

/-! ## Section G: FEKTYIY (relocated 2026-11-12, lane jcyfmrp-w2: moved
verbatim above `JCYFMRP_p27`, which now consumes it — dependency order;
content byte-identical, statement untouched) -/

/-- HOL `FEKTYIY` (FEKTYIY.hl:91). -/
theorem FEKTYIY_p27 : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k → ¬Coplanar (({0} ∪ Set.range v : Set V3)) := by
  intro s v hs hMM hk hcop
  classical
  -- `MMs` gives the `BBs` realisation and negative taustar
  -- (the Section-H helper `mm_BBs_taustar_p27` is declared below this point,
  -- so its two-line unpacking is inlined here)
  have hMMdata : BBsV39 s v ∧ taustarV39 s v < 0 := by
    have h := hMM
    simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
    exact ⟨h.1.1.1, h.1.1.2.2⟩
  obtain ⟨hBB, hta⟩ := hMMdata
  -- keep `hBB` (the `obtain` below consumes its copy)
  have hBB' := hBB
  obtain ⟨-, hper, -, h4⟩ := hBB'
  let V : Set V3 := Set.range v
  let E : Set (Set V3) := Set.range fun i : ℕ => ({v i, v (i + 1)} : Set V3)
  let FF : Set (V3 × V3) := Set.range fun i : ℕ => (v i, v (i + 1))
  have hclf : ConvexLocalFan V E FF := by
    rcases h4 with h3 | hcf
    · omega
    · exact hcf
  have hlf : LocalFan V E FF := hclf.1
  have hedge : ∀ u ∈ V, ∃ w, {u, w} ∈ E := by
    rintro u ⟨i, rfl⟩
    exact ⟨v (i + 1), ⟨i, rfl⟩⟩
  have hlf2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hlf hedge
  -- the `rho_node1` orbit runs through the cyclic `v` window
  have horbit : ∀ p1 m : ℕ, (rhoNode1 FF)^[m] (v p1) = v (m + p1) := by
    intro p1 m
    exact VV_SUC_EQ_RHO_NODE_PRIME_p35 s s.k p1 0 0 (v p1) V E FF v
      rfl rfl rfl rfl rfl hs (by omega) hBB m
  -- cardinality of the vertex set
  have hk0 : 0 < s.k := by omega
  have hdiag : scsDiag s.k 0 2 := by
    unfold scsDiag
    have h1 : 1 % s.k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : 2 % s.k = 2 := Nat.mod_eq_of_lt (by omega)
    have h3 : 3 % s.k = 3 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.zero_mod, h1, h2, h3]
    omega
  have hcard : V.ncard = s.k := CARD_V_EQ_SCS_K_p35 s s.k 0 2 V v rfl rfl hs hdiag hBB
  -- predecessor identification: `ivs_rho_node1` is the cyclic predecessor
  have hivs : ∀ i : ℕ, ivsRhoNode1 FF (v i) = v (i + (s.k - 1)) := by
    intro i
    have h1 := ITER_CARD_MINUS1_EQ_IVS_RN1 hlf2 (v := v i)
      (Set.mem_range.mpr ⟨i, rfl⟩)
    rw [hcard] at h1
    have h2 : (rhoNode1_p2 FF)^[s.k - 1] (v i) = v (s.k - 1 + i) := horbit i (s.k - 1)
    rw [h2, Nat.add_comm (s.k - 1) i] at h1
    exact h1.symm
  -- successor identification
  have hrho : ∀ i : ℕ, rhoNode1 FF (v i) = v (i + 1) := by
    intro i
    exact DETER_RHO_NODE hlf2 (v := v i) (w := v (i + 1))
      (Set.mem_range.mpr ⟨i, rfl⟩)
  -- the fan orbit window is the whole vertex set
  have hU : {z : V3 | ∃ n ≤ s.k + 1, z = (rhoNode1 FF)^[n] (v 0)} = V := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [horbit 0 n, Nat.add_zero]
      exact Set.mem_range.mpr ⟨n, rfl⟩
    · rintro ⟨m, rfl⟩
      refine ⟨m % s.k, ?_, ?_⟩
      · have := Nat.mod_lt m hk0; omega
      · rw [horbit 0 (m % s.k), Nat.add_zero]
        exact (periodic_mod_eq_p23 hper m).symm
  -- coplanarity gives a plane through 0 containing all vertices
  obtain ⟨P, hplane, hsub⟩ := coplanar_eq_coplanar_alt.mp hcop
  obtain ⟨a, b, c, hnc, rfl⟩ := hplane
  have h0P : (0 : V3) ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (Or.inl rfl)
  have hsubV : V ⊆ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) :=
    fun z hz => hsub (Or.inr hz)
  have hPlaneP : PlaneP_p37 (affineSpan ℝ ({a, b, c} : Set V3)) := ⟨a, b, c, hnc, rfl⟩
  -- hence every turn of the rho orbit is a straight angle
  have hazim_iter := AZIM_PI_ITER_LOCAL_FAN_p37 (V := V) (E := E) (FF := FF)
    (v := v 0) (l := s.k + 1) (U := V) (P := affineSpan ℝ ({a, b, c} : Set V3))
    hlf (Set.mem_range.mpr ⟨0, rfl⟩) hU hPlaneP h0P hsubV
  have hiter : ∀ i < s.k, azim 0 (v i) (v (i + (s.k - 1))) (v (i + 1)) = Real.pi := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have h := hazim_iter (s.k - 1) (by omega)
      rw [horbit 0 (s.k - 1 + 1), horbit 0 (s.k - 1), horbit 0 (s.k - 1 + 2)] at h
      simp only [Nat.add_zero] at h
      have e1 : v (s.k - 1 + 1) = v 0 := by
        rw [show s.k - 1 + 1 = s.k from by omega]
        simpa using hper 0
      have e3 : v (s.k - 1 + 2) = v 1 := by
        rw [show s.k - 1 + 2 = 1 + s.k from by omega]
        exact hper 1
      rw [e1, e3] at h
      simpa [Nat.zero_add] using h
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hi' : i' < s.k := by omega
      have h := hazim_iter i' (by omega)
      rw [horbit 0 (i' + 1), horbit 0 i', horbit 0 (i' + 2)] at h
      simp only [Nat.add_zero] at h
      have e1 : v i' = v (i' + 1 + (s.k - 1)) := by
        rw [show i' + 1 + (s.k - 1) = i' + s.k from by omega]
        exact (hper i').symm
      rw [e1] at h
      exact h
  -- complement the azimuth: from `i+k-1 -> i+1` to `i+1 -> i+k-1`
  have hazim : ∀ i < s.k, azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1))) = Real.pi := by
    intro i hi
    rw [AZIM_COMPL_EXT (0 : V3) (v i) (v (i + (s.k - 1))) (v (i + 1))]
    rw [if_neg (by rw [hiter i hi]; exact Real.pi_ne_zero), hiter i hi]
    ring
  -- every fan azimuth of the realisation is a straight angle
  have hazimFan : ∀ e ∈ FF, azimInFan e E = Real.pi := by
    rintro e ⟨i, rfl⟩
    have hin := LOFA_IMP_INANGLE_EQ_AZIM_p14 V E FF (v i) hlf hedge
      (Set.mem_range.mpr ⟨i, rfl⟩)
    rw [hrho i] at hin
    rw [← hin]
    show azim 0 (v i) (rhoNode1 FF (v i)) (ivsRhoNode1 FF (v i)) = Real.pi
    rw [hrho i, hivs i]
    -- fold the index modulo `k`: the finite fan uses the cyclic window only
    have hperEq : ∀ x y : ℕ, x % s.k = y % s.k → v x = v y := by
      intro x y hxy
      rw [← periodic_mod_eq_p23 hper x, ← periodic_mod_eq_p23 hper y, hxy]
    have hmod1 : v i = v (i % s.k) := hperEq i (i % s.k) (by rw [Nat.mod_mod])
    have hmod2 : v (i + 1) = v (i % s.k + 1) := by
      refine hperEq (i + 1) (i % s.k + 1) ?_
      rw [Nat.add_mod i 1 s.k, Nat.add_mod (i % s.k) 1 s.k, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : 1 < s.k)]
    have hmod3 : v (i + (s.k - 1)) = v (i % s.k + (s.k - 1)) := by
      refine hperEq (i + (s.k - 1)) (i % s.k + (s.k - 1)) ?_
      rw [Nat.add_mod i (s.k - 1) s.k, Nat.add_mod (i % s.k) (s.k - 1) s.k, Nat.mod_mod]
    rw [hmod1, hmod2, hmod3]
    exact hazim (i % s.k) (Nat.mod_lt i hk0)
  -- the dart set is finite and its `sol_local` excess sum vanishes
  have hperFF : Periodic (fun i : ℕ => (v i, v (i + 1))) s.k := by
    intro i
    have h2 : v (i + s.k + 1) = v (i + 1) := by
      rw [Nat.add_right_comm i s.k 1]
      exact hper (i + 1)
    show (v (i + s.k), v (i + s.k + 1)) = (v i, v (i + 1))
    rw [hper i, h2]
  have hfinFF : FF.Finite := by
    show (Set.range fun i : ℕ => (v i, v (i + 1))).Finite
    rw [range_periodic_image_p23 (fun i : ℕ => (v i, v (i + 1))) s.k hk0 hperFF]
    exact (Set.finite_Iio s.k).image _
  have hsum : setSum FF (fun e => azimInFan e E - Real.pi) = 0 := by
    unfold setSum
    rw [dif_pos hfinFF]
    refine Finset.sum_eq_zero (fun e he => ?_)
    have hmem : e ∈ FF := hfinFF.mem_toFinset.mp he
    rw [hazimFan e hmem]
    ring
  -- contradiction with JKQEWGV1
  have hJK := JKQEWGV1_p23 s v hs hk hBB hta
  rw [Set.image_univ, Set.image_univ] at hJK
  have hsol : solLocal E FF = 2 * Real.pi := by
    unfold solLocal
    rw [hsum]
    ring
  rw [hsol] at hJK
  linarith [Real.pi_pos]
  -- PROVED (2026-11-05, lane m1a-root-w6): under coplanarity the LA37 engine
  -- `AZIM_PI_ITER_LOCAL_FAN_p37` makes every turn of the rho orbit a straight
  -- angle, so each `azimInFan` of `FF` is `pi` and `solLocal = 2*pi`, against
  -- `JKQEWGV1_p23` (`solLocal < pi`).

/-- JCYFMRP proof-wave kit (2026-11-12, lane jcyfmrp-w2): the flat-arc
coplanarity lemma, ported from LA18's private `la18au_arc_mem` (LA18:1940,
the AURSIPD geo engine — LA18 imports LA27 so it is not importable from
here).  The periodicity input is this file's own `periodic_mod_p27`; the
coplanarity step is `AZIM_EQ_0_PI_IMP_COPLANAR` (ConicCapVolume, newly
imported); the affine-span step is `coplanar_in_affine_hull_p14` (LA14).
Statement and proof structure follow the LA18 original line for line. -/
private theorem jcyfmrp_arc_mem (v : ℕ → V3) (k a b : ℕ)
    (hk3 : 3 < k) (hper : Periodic v k)
    (hinj : ∀ x y, x < k → y < k → x ≠ y → v x ≠ v y)
    (hgen : ∀ x y : ℕ, v x ≠ v y → ¬ Collinear ℝ ({0, v x, v y} : Set V3))
    (hflat : ∀ t, a < t → t < b →
      azim 0 (v t) (v (t + 1)) (v (t + (k - 1))) = Real.pi)
    (_hb : b < a + k) :
    ∀ t, a ≤ t → t ≤ b → v t ∈ affineSpan ℝ ({0, v a, v (a + 1)} : Set V3) := by
  have hk0 : 0 < k := by omega
  let P : AffineSubspace ℝ V3 := affineSpan ℝ ({0, v a, v (a + 1)} : Set V3)
  have hva : v a ∈ P := mem_affineSpan ℝ (by simp)
  have hva1 : v (a + 1) ∈ P := mem_affineSpan ℝ (by simp)
  have hstep : ∀ t, a + 1 ≤ t → t < b → v (t - 1) ∈ P → v t ∈ P →
      v (t + 1) ∈ P := by
    intro t hat htb hprev hvt
    have hflat_t := hflat t (by omega) htb
    have hper1 : v (t + (k - 1)) = v (t - 1) := by
      have he : t + (k - 1) = (t - 1) + k := by omega
      rw [he, hper (t - 1)]
    have hcop0 : Coplanar ({0, v t, v (t + 1), v (t - 1)} : Set V3) :=
      AZIM_EQ_0_PI_IMP_COPLANAR 0 (v t) (v (t + 1)) (v (t - 1))
        (Or.inr (by rw [← hper1]; exact hflat_t))
    have hcop : Coplanar ({v (t + 1), 0, v t, v (t - 1)} : Set V3) := by
      have hs : ({v (t + 1), 0, v t, v (t - 1)} : Set V3)
          = {0, v t, v (t + 1), v (t - 1)} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hs]
      exact hcop0
    have hne : v t ≠ v (t - 1) := by
      intro heq
      have hmod : t % k = (t - 1) % k := by
        by_contra hne'
        exact hinj (t % k) ((t - 1) % k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0)
          hne' (by rw [← periodic_mod_p27 hper t, ← periodic_mod_p27 hper (t - 1)]; exact heq)
      have hA : (t % k + 1) % k = ((t - 1) % k + 1) % k := by rw [hmod]
      have hB : ((t - 1) % k + 1) % k = ((t - 1) + 1) % k := by
        rw [Nat.add_mod (t - 1) 1 k, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
      have hC : ((t - 1) + 1) % k = t % k := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ t)]
      have hmodstep : (t % k + 1) % k = t % k := hA.trans (hB.trans hC)
      rcases lt_or_ge (t % k + 1) k with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hmodstep
        omega
      · have hr : t % k < k := Nat.mod_lt _ hk0
        have heqk : t % k + 1 = k := by omega
        rw [heqk, Nat.mod_self] at hmodstep
        omega
    have hnc : ¬ Collinear ℝ ({0, v t, v (t - 1)} : Set V3) := hgen t (t - 1) hne
    have hmem := coplanar_in_affine_hull_p14 0 (v t) (v (t - 1)) (v (t + 1))
      hnc hcop
    have hle : affineSpan ℝ ({0, v t, v (t - 1)} : Set V3) ≤ P := by
      rw [affineSpan_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact hvt
      · exact hprev
    exact hle hmem
  have hmain : ∀ t, a + 1 ≤ t → t ≤ b → v t ∈ P := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro hat htb
      by_cases ht : t = a + 1
      · rw [ht]
        exact hva1
      · have ht2 : a + 2 ≤ t := by omega
        have hb1 : t - 1 < b := by omega
        have h1 : a + 1 ≤ t - 1 := by omega
        have hprev : v ((t - 1) - 1) ∈ P := by
          rcases Nat.eq_or_lt_of_le (by omega : a ≤ (t - 1) - 1) with heq | hlt
          · rw [← heq]
            exact hva
          · exact ih ((t - 1) - 1) (by omega) (by omega) (by omega)
        have hvt : v (t - 1) ∈ P := by
          rcases Nat.eq_or_lt_of_le h1 with heq | hlt
          · rw [← heq]
            exact hva1
          · exact ih (t - 1) (by omega) h1 (by omega)
        have hstepv := hstep (t - 1) h1 hb1 hprev hvt
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hstepv
  intro t hat htb
  rcases Nat.eq_or_lt_of_le hat with heq | hlt
  · rw [← heq]
    exact hva
  · exact hmain t (by omega) htb

/-- JCYFMRP proof-wave kit: the cycle diagonal `(i + k - 1, i + 1)` is a
genuine `scsDiag` for `3 < k` (the discharges are `k ∣ 2` / `k ∣ 3`
contradictions).  Used for the `CUXVZOZ_p21` distance side condition. -/
private theorem jcyfmrp_diag_ps (k i : ℕ) (hk : 3 < k) :
    scsDiag k (i + k - 1) (i + 1) := by
  have hk0 : 0 < k := by omega
  have h1k : 1 < k := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- (i + k - 1) % k ≠ (i + 1) % k
    by_cases hi : i = 0
    · subst hi
      rw [show (0 + k - 1) % k = k - 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)],
        show (0 + 1) % k = 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]]
      omega
    · rw [show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right]
      intro h
      have hme : (i - 1) ≡ (i + 1) [MOD k] := h
      have hdiv : k ∣ (i + 1) - (i - 1) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hme
      have := Nat.le_of_dvd (by omega) hdiv
      omega
  · -- ((i + k - 1) + 1) % k ≠ ((i + 1) + 1) % k
    rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
    intro h
    have hme : i ≡ i + 1 [MOD k] := h
    have hdiv : k ∣ (i + 1) - i := (Nat.modEq_iff_dvd' (by omega)).mp hme
    have := Nat.le_of_dvd (by omega) hdiv
    omega
  · -- (i + k - 1) % k ≠ ((i + 1) + 1) % k
    by_cases hi : i = 0
    · subst hi
      rw [show (0 + k - 1) % k = k - 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)],
        show (0 + 1 + 1) % k = 2 by
          rw [Nat.zero_add, one_add_one_eq_two, Nat.mod_eq_of_lt (by omega)]]
      omega
    · rw [show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right]
      intro h
      have hme : (i - 1) ≡ i + 1 + 1 [MOD k] := h
      have hdiv : k ∣ (i + 1 + 1) - (i - 1) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hme
      have := Nat.le_of_dvd (by omega) hdiv
      omega

/-- JCYFMRP proof-wave kit: the mirror diagonal `(i + 1, i + k - 1)`
(consumed by the `SYNQIWN_p22` `hc` side condition). -/
private theorem jcyfmrp_diag_sp (k i : ℕ) (hk : 3 < k) :
    scsDiag k (i + 1) (i + k - 1) := by
  have hk0 : 0 < k := by omega
  have h1k : 1 < k := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- (i + 1) % k ≠ (i + k - 1) % k
    by_cases hi : i = 0
    · subst hi
      rw [show (0 + 1) % k = 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)],
        show (0 + k - 1) % k = k - 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]]
      omega
    · rw [show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right]
      intro h
      have hme : (i - 1) ≡ (i + 1) [MOD k] := h.symm
      have hdiv : k ∣ (i + 1) - (i - 1) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hme
      have := Nat.le_of_dvd (by omega) hdiv
      omega
  · -- ((i + 1) + 1) % k ≠ (i + k - 1) % k
    by_cases hi : i = 0
    · subst hi
      rw [show (0 + 1 + 1) % k = 2 by
          rw [Nat.zero_add, one_add_one_eq_two, Nat.mod_eq_of_lt (by omega)],
        show (0 + k - 1) % k = k - 1 by
          rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]]
      omega
    · rw [show i + k - 1 = (i - 1) + k from by omega, Nat.add_mod_right]
      intro h
      have hme : (i - 1) ≡ i + 1 + 1 [MOD k] := h.symm
      have hdiv : k ∣ (i + 1 + 1) - (i - 1) :=
        (Nat.modEq_iff_dvd' (by omega)).mp hme
      have := Nat.le_of_dvd (by omega) hdiv
      omega
  · -- (i + 1) % k ≠ ((i + k - 1) + 1) % k
    rw [show i + k - 1 + 1 = i + k from by omega, Nat.add_mod_right]
    exact (succ_mod_ne_p27 (k := k) (i := i) h1k).symm

/-- JCYFMRP proof-wave kit: AURSIPD's geo block (LA18:2242-2293) in
residue form — if every vertex whose residue avoids the two exception
residues `r1 r2` is flat (`azim = pi`), then `{0} ∪ range v` is coplanar.
Shared by the all-flat branch of the main case split and the lunar fork
of the J-empty branch (the FEKTYIY contradiction is applied by callers). -/
private theorem jcyfmrp_flat_residues_coplanar (s : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hMM : v ∈ MMsV39 s) (hk3 : 3 < s.k)
    (hBB : BBsV39 s v) (hper : Periodic v s.k)
    (hgen0 : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)))
    (r1 r2 : ℕ) (hr1 : r1 < s.k) (hr2 : r2 < s.k) (hne : r1 ≠ r2)
    (hflatt : ∀ t : ℕ, t % s.k ≠ r1 → t % s.k ≠ r2 →
      azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi) :
    Coplanar (({0} ∪ Set.range v : Set V3)) := by
  have hk0 : 0 < s.k := by omega
  have hclf : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hBB.2.2.2 with h3le | hcf
    · omega
    · exact hcf
  have hinj : ∀ x y, x < s.k → y < s.k → x ≠ y → v x ≠ v y :=
    fun x y hx hy hxy => VV_INJ_p35 s s.k v rfl hs hBB x y ⟨hx, hy, hxy⟩
  have hgen_ncol : ∀ x y : ℕ, v x ≠ v y →
      ¬ Collinear ℝ ({0, v x, v y} : Set V3) := by
    intro x y hxy
    refine PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 _ _ _ (v x) (v y)
      hclf.1 ⟨x, rfl⟩ ⟨y, rfl⟩ hxy hgen0
  have hmod_ne_gen : ∀ p q t : ℕ, p < s.k → q < s.k → p < q → q < t →
      t < p + s.k → t % s.k ≠ p ∧ t % s.k ≠ q := by
    intro p q t hp hq hpq ht1 ht2
    by_cases htk : t < s.k
    · rw [Nat.mod_eq_of_lt htk]
      exact ⟨by omega, by omega⟩
    · have e : t % s.k = t - s.k := by
        have h1 : t % s.k = (t - s.k) % s.k := by
          rw [← Nat.add_mod_right (t - s.k) s.k,
            Nat.sub_add_cancel (show s.k ≤ t from le_of_not_gt htk)]
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [e]
      refine ⟨?_, ?_⟩
      · intro h
        have : t = p + s.k := by omega
        omega
      · intro h
        have : t = q + s.k := by omega
        omega
  have hflatwin : ∀ a b : ℕ, b < a + s.k →
      (∀ t, a < t → t < b → t % s.k ≠ r1 ∧ t % s.k ≠ r2) →
      ∀ t, a ≤ t → t ≤ b →
      v t ∈ affineSpan ℝ ({0, v a, v (a + 1)} : Set V3) := fun a b hb hw =>
    jcyfmrp_arc_mem v s.k a b hk3 hper hinj hgen_ncol
      (fun t h1 h2 => hflatt t (hw t h1 h2).1 (hw t h1 h2).2) hb
  have geo : ∀ p q : ℕ, p < s.k → q < s.k → p < q →
      (∀ t, p < t → t < q → t % s.k ≠ r1 ∧ t % s.k ≠ r2) →
      (∀ t, q < t → t < p + s.k → t % s.k ≠ r1 ∧ t % s.k ≠ r2) →
      Coplanar (({0} ∪ Set.range v : Set V3)) := by
    intro p q hp hq hpq hw1 hw2
    have harc1 := hflatwin p q (by omega) hw1
    have harc2 := hflatwin q (p + s.k) (by omega) hw2
    have hnc : ¬ Collinear ℝ ({0, v p, v q} : Set V3) :=
      hgen_ncol p q (hinj p q hp hq (by omega))
    have hP1_le : affineSpan ℝ ({0, v p, v (p + 1)} : Set V3)
        ≤ affineSpan ℝ ({0, v p, v q} : Set V3) := by
      rw [affineSpan_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
      · have hcop : Coplanar ({v (p + 1), 0, v p, v q} : Set V3) := by
          refine ⟨0, v p, v (p + 1), ?_⟩
          intro z hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact mem_affineSpan ℝ (by simp)
          · exact mem_affineSpan ℝ (by simp)
          · exact mem_affineSpan ℝ (by simp)
          · exact harc1 q (by omega) (by omega)
        exact coplanar_in_affine_hull_p14 0 (v p) (v q) (v (p + 1)) hnc hcop
    have hQsub : affineSpan ℝ ({0, v q, v (q + 1)} : Set V3)
        ≤ affineSpan ℝ ({0, v p, v q} : Set V3) := by
      rw [affineSpan_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
      · have hiQ : v p ∈ affineSpan ℝ ({0, v q, v (q + 1)} : Set V3) := by
          have h := harc2 (p + s.k) (by omega) (le_refl _)
          have e : v (p + s.k) = v p := hper p
          rwa [e] at h
        have hcop : Coplanar ({v (q + 1), 0, v p, v q} : Set V3) := by
          refine ⟨0, v q, v (q + 1), ?_⟩
          intro z hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact mem_affineSpan ℝ (by simp)
          · exact mem_affineSpan ℝ (by simp)
          · exact hiQ
          · exact mem_affineSpan ℝ (by simp)
        exact coplanar_in_affine_hull_p14 0 (v p) (v q) (v (q + 1)) hnc hcop
    have hPall : ∀ t : ℕ, v t ∈ affineSpan ℝ ({0, v p, v q} : Set V3) := by
      intro t
      have hvmod : v t = v (t % s.k) := periodic_mod_p27 hper t
      rw [hvmod]
      have htmod : t % s.k < s.k := Nat.mod_lt _ hk0
      by_cases hti : t % s.k < p
      · have hmem := harc2 (t % s.k + s.k) (by omega) (by omega)
        have heq : v (t % s.k + s.k) = v (t % s.k) := hper _
        rw [heq] at hmem
        exact hQsub hmem
      · have hge : p ≤ t % s.k := by omega
        by_cases hle : t % s.k ≤ q
        · exact hP1_le (harc1 (t % s.k) hge hle)
        · exact hQsub (harc2 (t % s.k) (by omega) (by omega))
    refine ⟨0, v p, v q, ?_⟩
    intro z hz
    rcases hz with rfl | hz
    · exact mem_affineSpan ℝ (by simp)
    · obtain ⟨t, rfl⟩ := hz
      exact hPall t
  by_cases hlt : r1 < r2
  · refine geo r1 r2 hr1 hr2 hlt (fun t h1 h2 => ⟨?_, ?_⟩)
      (fun t h1 h2 => hmod_ne_gen r1 r2 t hr1 hr2 hlt h1 h2)
    · rw [Nat.mod_eq_of_lt (by omega : t < s.k)]; omega
    · rw [Nat.mod_eq_of_lt (by omega : t < s.k)]; omega
  · have hgt : r2 < r1 := Nat.lt_of_le_of_ne (by omega) (Ne.symm hne)
    refine geo r2 r1 hr2 hr1 hgt (fun t h1 h2 => ⟨?_, ?_⟩)
      (fun t h1 h2 => ⟨(hmod_ne_gen r2 r1 t hr2 hr1 hgt h1 h2).2,
        (hmod_ne_gen r2 r1 t hr2 hr1 hgt h1 h2).1⟩)
    · rw [Nat.mod_eq_of_lt (by omega : t < s.k)]; omega
    · rw [Nat.mod_eq_of_lt (by omega : t < s.k)]; omega

/-- HOL `JCYFMRP_concl` (JCYFMRP.hl:240). -/
theorem JCYFMRP_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3),
        3 < s.k → isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
          (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
            (∀ i, s.a i (i + 1) = 2) →
              (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
                ∃ i, dist (v i) (v (i + 1)) = 2 := by
  intro hmnl s v hk3 hs hMMs hgen hbasic hb hM ha2 hadiag
  classical
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hMMs
  have hta : taustarV39 s v < 0 := by
    have h1 := hMMs
    simp only [MMsV39, Set.mem_setOf_eq] at h1
    have h2 := h1.1
    simp only [BBprime2V39, Set.mem_setOf_eq] at h2
    have h3 := h2.1
    simp only [BBprimeV39, Set.mem_setOf_eq] at h3
    exact h3.2.2
  have hBBc := hBB
  obtain ⟨-, hper, -, h4⟩ := hBBc
  have hsc := hs
  obtain ⟨hd0, hk1, hk2, hplo, hphi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag, hb3, hbc, hJmod, hJsq, hcard⟩ := hsc
  have hk0 : 0 < s.k := by omega
  have h1k : 1 < s.k := by omega
  set V : Set V3 := Set.range v with hVdef
  set E : Set (Set V3) := Set.range (fun i => ({v i, v (i + 1)} : Set V3)) with hEdef
  set FF : Set (V3 × V3) := Set.range (fun i => (v i, v (i + 1))) with hFFdef
  have hk3' : ¬ s.k ≤ 3 := by omega
  have hclf : ConvexLocalFan V E FF := by
    rcases h4 with h3le | hcf
    · exact absurd h3le hk3'
    · simpa only [hVdef, hEdef, hFFdef] using hcf
  have hlf : LocalFan V E FF := hclf.1
  -- orbit facts (LA22 `RRCWNS_WEAK_p22` route: `DETER_RHO_NODE` /
  -- `PRE_IVS_RHO_NODE1_DETE` on the AzimBridge `localFan_p2` encoding)
  have hlf3 : localFan_p3 V E FF := localFanEquiv_p35.mp hlf
  have hlf2 : localFan_p2 V E FF := localFan_p2.of_localFan_p3 hlf3
  have hpro2 := (LOCAL_FAN_RHO_NODE_PROS2 hlf2).2
  -- two-regularity lower bound for the scs fan, via `w1TwoLe_p35`
  -- (AzimBridge) on the `localFan_p3` encoding (`EE_p3` is defeq to `ee`).
  have hreg : ∀ u ∈ V, 2 ≤ (ee u E).ncard := fun u hu => w1TwoLe_p35 hlf3 u hu
  have hpro : ∀ x ∈ V, (x, rhoNode1 FF x) ∈ FF := fun x hx => by
    have h := hpro2 x hx
    simpa only [rhoNode1, rhoNode1_p2] using h
  have hrho : ∀ i, rhoNode1 FF (v i) = v (i + 1) := by
    intro i
    have hrp : rhoNode1_p2 FF (v i) = v (i + 1) :=
      DETER_RHO_NODE hlf2 (v := v i) (w := v (i + 1))
        (show (v i, v (i + 1)) ∈ FF from Set.mem_range.mpr ⟨i, rfl⟩)
    simpa only [rhoNode1, rhoNode1_p2] using hrp
  have hivs : ∀ i, ivsRhoNode1 FF (v i) = v (i + (s.k - 1)) := by
    intro i
    have hmem : (v (i + (s.k - 1)), v i) ∈ FF := by
      refine Set.mem_range.mpr ⟨i + (s.k - 1), ?_⟩
      have hper1 : v (i + (s.k - 1) + 1) = v i := by
        rw [show i + (s.k - 1) + 1 = i + s.k by omega]
        exact hper i
      rw [hper1]
    have hip : ivsRhoNode1_p2 FF (v i) = v (i + (s.k - 1)) :=
      PRE_IVS_RHO_NODE1_DETE hlf2 hmem
    simpa only [ivsRhoNode1, ivsRhoNode1_p2] using hip
  have hid : ∀ i, interiorAngle1 0 FF (v i)
      = azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1))) := fun i => by
    simp only [interiorAngle1, hrho i, hivs i]
  -- interior-angle upper bound (≤ π) from the convex-fan wedge condition
  have hle_pi : ∀ i, azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1))) ≤ Real.pi := by
    intro i
    have hvi : v i ∈ V := ⟨i, rfl⟩
    have hx : (v i, rhoNode1 FF (v i)) ∈ FF := hpro _ hvi
    have hconv := hclf.2 _ hx
    have h2e : 2 ≤ (ee (v i) E).ncard := hreg _ hvi
    have hlt : 1 < (ee (v i) E).ncard := by omega
    have hvm : v (i + (s.k - 1)) ∈ V := ⟨i + (s.k - 1), rfl⟩
    have hw : v (i + (s.k - 1)) ∈ wedgeGe 0 (v i) (rhoNode1 FF (v i))
        (sigmaFan 0 Set.univ E (v i) (rhoNode1 FF (v i))) := by
      have h := hconv.2 hvm
      unfold wedgeInFanGe at h
      rw [if_pos hlt] at h
      exact h
    have hazi : azim 0 (v i) (rhoNode1 FF (v i))
        (sigmaFan 0 Set.univ E (v i) (rhoNode1 FF (v i))) ≤ Real.pi := by
      have h := hconv.1
      unfold azimInFan at h
      rw [if_pos hlt] at h
      exact h
    have hchain : azim 0 (v i) (rhoNode1 FF (v i)) (v (i + (s.k - 1)))
        ≤ azim 0 (v i) (rhoNode1 FF (v i))
          (sigmaFan 0 Set.univ E (v i) (rhoNode1 FF (v i))) := hw.2
    rw [hrho i] at hchain hazi
    exact hchain.trans hazi
  have hgen0 : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) :=
    hgen
  by_cases hex : ∃ i, dist (v i) (v (i + 1)) = 2
  · exact hex
  · push_neg at hex
    have hgt2 : ∀ i, 2 < dist (v i) (v (i + 1)) := by
      intro i
      have h2a : 2 ≤ s.a i (i + 1) := SCS_A_2_p27 s hs i
      have hle : s.a i (i + 1) ≤ dist (v i) (v (i + 1)) := (hBB.2.2.1 i (i + 1)).1
      have h2d : 2 ≤ dist (v i) (v (i + 1)) := le_trans h2a hle
      have hne := hex i
      exact lt_of_le_of_ne h2d (Ne.symm hne)
    by_cases hn2 : ∀ i, ‖v i‖ = 2
    · -- main branch: `SCS_M_LE_1` pin + `SYNQIWN` half-plane bound
      obtain ⟨p, hp⟩ := SCS_M_LE_1_p27 s hM hs
      have hpi2 : ∀ i, i % s.k ≠ p % s.k → i % s.k ≠ (p + 1) % s.k →
          Real.pi / 2 < azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1))) := by
        intro i hi1 hi2
        have him1 : (i - 1) % s.k ≠ p % s.k := by
          by_cases h0 : i = 0
          · subst h0
            have e0 : (0 - 1 : ℕ) % s.k = 0 % s.k := rfl
            rw [e0]
            exact hi1
          · intro hc
            apply hi2
            have e1 : i % s.k = ((i - 1) + 1) % s.k := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
            rw [e1, show ((i - 1) + 1) % s.k = ((i - 1) % s.k + 1) % s.k from
                (mod_add_c_p27 (i := i - 1) (c := 1) h1k).symm, hc,
              show (p % s.k + 1) % s.k = (p + 1) % s.k from
                mod_add_c_p27 (i := p) (c := 1) h1k]
        have h1b : s.b i (i + 1) ≤ 2 * h0 := (hp i hi1).1
        have he2 : dist (v i) (v (i + s.k - 1)) ≤ 2 * h0 := by
          by_cases h0 : i = 0
          · subst h0
            rw [show (0 : ℕ) + s.k - 1 = s.k - 1 by omega]
            have hk1m : (s.k - 1) % s.k ≠ p % s.k := by
              rw [Nat.mod_eq_of_lt (by omega : s.k - 1 < s.k)]
              intro h
              apply hi2
              rw [show (p + 1) % s.k = (p % s.k + 1) % s.k from
                  (mod_add_c_p27 (i := p) (c := 1) h1k).symm, ← h,
                show s.k - 1 + 1 = s.k from Nat.sub_add_cancel (by omega : 1 ≤ s.k),
                Nat.mod_self, Nat.zero_mod]
            have hb2 := hp (s.k - 1) hk1m
            rw [show s.k - 1 + 1 = s.k from Nat.sub_add_cancel (by omega : 1 ≤ s.k)]
              at hb2
            have hle : dist (v (s.k - 1)) (v s.k) ≤ s.b (s.k - 1) s.k :=
              (hBB.2.2.1 (s.k - 1) s.k).2
            have e3 : v s.k = v 0 := by
              have h := hper 0
              rw [Nat.zero_add] at h
              exact h
            rw [e3] at hle
            have e2 : dist (v 0) (v (s.k - 1)) = dist (v (s.k - 1)) (v 0) :=
              dist_comm _ _
            rw [e2]
            exact le_trans hle hb2.1
          · have hge1 : 1 ≤ i := by omega
            have e1 : i + s.k - 1 = (i - 1) + s.k := by omega
            have hva : v (i + s.k - 1) = v (i - 1) := by
              rw [e1]; exact hper (i - 1)
            rw [hva]
            have hb2 := hp (i - 1) him1
            rw [Nat.sub_add_cancel hge1] at hb2
            have hle : dist (v (i - 1)) (v i) ≤ s.b (i - 1) i :=
              (hBB.2.2.1 (i - 1) i).2
            have e2 : dist (v i) (v (i - 1)) = dist (v (i - 1)) (v i) :=
              dist_comm _ _
            rw [e2]
            exact le_trans hle hb2.1
        have hc : cstab ≤ dist (v (i + 1)) (v (i + s.k - 1)) :=
          le_of_lt (hadiag (i + 1) (i + s.k - 1) (jcyfmrp_diag_sp s.k i hk3)).2
        have hears : (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + s.k - 1)) = 2) ∨
            (norm (v (i + s.k - 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
            (norm (v (i + 1)) = 2 ∧ norm (v (i + s.k - 1)) = 2) ∨
            (dist (v i) (v (i + 1)) = 2 ∧ dist (v i) (v (i + s.k - 1)) = 2) ∨
            (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
            (norm (v (i + s.k - 1)) = 2 ∧ dist (v i) (v (i + s.k - 1)) = 2) := by
          have hn1 : norm (v (i + 1)) = 2 := hn2 (i + 1)
          have hnm : norm (v (i + s.k - 1)) = 2 := hn2 (i + s.k - 1)
          exact Or.inr (Or.inr (Or.inl ⟨hn1, hnm⟩))
        have hsp := SYNQIWN_p22 hmnl s v i s.k hs hBB rfl hk3 hears
          (le_trans (hBB.2.2.1 i (i + 1)).2 h1b) he2 hc
        rwa [← show i + (s.k - 1) = i + s.k - 1 from by omega] at hsp
      have hsplit : (∀ i, i % s.k ≠ p % s.k → i % s.k ≠ (p + 1) % s.k →
          Real.pi ≤ azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1)))) ∨
        ¬(∀ i, i % s.k ≠ p % s.k → i % s.k ≠ (p + 1) % s.k →
          Real.pi ≤ azim 0 (v i) (v (i + 1)) (v (i + (s.k - 1)))) :=
        Classical.em _
      rcases hsplit with hall | hnot
      · -- all-flat branch: coplanarity contradicts FEKTYIY
        have hne' : p % s.k ≠ (p + 1) % s.k := succ_mod_ne_p27 h1k
        have hflatt : ∀ t, t % s.k ≠ p % s.k → t % s.k ≠ (p + 1) % s.k →
            azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi :=
          fun t h1 h2 => le_antisymm (hle_pi t) (hall t h1 h2)
        have hcop := jcyfmrp_flat_residues_coplanar s v hs hMMs hk3 hBB hper hgen0
          (p % s.k) ((p + 1) % s.k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hne' hflatt
        exact absurd hcop (FEKTYIY_p27 s v hs hMMs hk3)
      · -- boundary branch: `CUXVZOZ_p21` at the vertex with azim < π
        push_neg at hnot
        obtain ⟨i, hi1, hi2, hlt⟩ := hnot
        have e1 : i + (s.k - 1) = i + s.k - 1 := by omega
        have hdd := hadiag (i + s.k - 1) (i + 1) (jcyfmrp_diag_ps s.k i hk3)
        have hd3 : (3 : ℝ) ≤ cstab := by unfold cstab; norm_num
        have hd : 3 ≤ dist (v (i + (s.k - 1))) (v (i + 1)) := by
          rw [e1]
          linarith
        have ha' : ∀ i2 j2, scsDiag s.k i2 j2 →
            psort s.k (i2, j2) ≠ psort s.k (i + (s.k - 1), i + 1) →
            s.a i2 j2 < dist (v i2) (v j2) := fun i2 j2 hd2 _ =>
          lt_of_le_of_lt (hadiag i2 j2 hd2).1 (hadiag i2 j2 hd2).2
        have hang : interiorAngle1 0 FF (v i) < Real.pi := by
          rw [hid i]; exact hlt
        have hcase2 : Real.pi / 2 < interiorAngle1 0 FF (v i) ∨
            interiorAngle1 0 FF (v (i + 1)) < Real.pi :=
          Or.inl (by rw [hid i]; exact hpi2 i hi1 hi2)
        have ha12 : s.a i (i + 1) = 2 := (hp i hi1).2
        have hb12 : s.b i (i + 1) ≤ 2 * h0 := (hp i hi1).1
        have h2le : 2 ≤ dist (v (i + (s.k - 1))) (v i) := by
          by_cases h0 : i = 0
          · subst h0
            rw [show (0 : ℕ) + (s.k - 1) = s.k - 1 from zero_add _]
            have h2a : 2 ≤ s.a (s.k - 1) 0 :=
              hdiag (s.k - 1) 0 ⟨by omega, by omega, by omega⟩
            exact le_trans h2a ((hBB.2.2.1 (s.k - 1) 0).1)
          · have hge1 : 1 ≤ i := by omega
            have e2 : i + (s.k - 1) = (i - 1) + s.k := by omega
            have hva : v (i + (s.k - 1)) = v (i - 1) := by
              rw [e2]; exact hper (i - 1)
            rw [hva]
            have h2a : 2 ≤ s.a (i - 1) i := by
              have e3 : s.a (i - 1) i = s.a ((i - 1) % s.k) (i % s.k) :=
                periodic2_mod_p27 hpa (i - 1) i
              rw [e3]
              refine hdiag ((i - 1) % s.k) (i % s.k)
                ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, ?_⟩
              intro h
              have hsne : (i - 1) % s.k ≠ i % s.k := by
                rw [show i % s.k = ((i - 1) + 1) % s.k from
                    by rw [Nat.sub_add_cancel hge1]]
                exact succ_mod_ne_p27 (k := s.k) (i := i - 1) h1k
              exact hsne h
            exact le_trans h2a ((hBB.2.2.1 (i - 1) i).1)
        have hdc : dist (v (i + (s.k - 1))) (v i) ≤ cstab := by
          have hle := DIST_EDGE_LE_CSTAB_CASE_LE3_p27 s v (i + s.k - 1) hk3 hBB hs
          rw [show i + s.k - 1 + 1 = i + s.k from by omega, hper, ← e1] at hle
          exact hle
        refine ⟨i, CUXVZOZ_p21 hmnl s FF s.k i v hFFdef hs rfl hk3 hMMs hbasic hgen
          hd ha' hb hang hcase2 ha12 hb12 h2le hdc⟩
    · -- J-empty branch: `ODXLSTCv2` at a vertex with norm ≠ 2
      push_neg at hn2
      obtain ⟨i0, hi0⟩ := hn2
      have hJ : ∀ x, ¬ s.J i0 x := J_EMPY_CASES_A_EQ_2_p27 s ha2 hs i0
      have hcirc : ¬ Circular V E := by
        have hq := JKQEWGV2_p23 s v hs hk3 hBB hta
        simpa only [hVdef, hEdef, Set.image_univ] using hq
      have hlt2 : ∀ i, ¬(i % s.k = i0 % s.k) → s.a i0 i < dist (v i0) (v i) := by
        intro i hci
        by_cases had1 : i % s.k = (i0 + 1) % s.k
        · have e1 : s.a i0 i = s.a i0 (i0 + 1) := by
            rw [periodic2_mod_p27 hpa i0 i, periodic2_mod_p27 hpa i0 (i0 + 1),
              had1]
          rw [e1, ha2]
          have hvv : v i = v (i0 + 1) :=
            CHANGE_W_IN_BBS_MOD_IS_SCS_p28 s v i (i0 + 1) hs hBB had1
          rw [hvv]
          exact hgt2 i0
        · by_cases had2 : (i + 1) % s.k = i0 % s.k
          · have e1 : s.a i0 i = s.a i (i + 1) := by
              rw [(hsym i0 i).1, periodic2_mod_p27 hpa i i0,
                periodic2_mod_p27 hpa i (i + 1), had2.symm]
            rw [e1, ha2]
            have hvv : v i0 = v (i + 1) :=
              CHANGE_W_IN_BBS_MOD_IS_SCS_p28 s v i0 (i + 1) hs hBB had2.symm
            rw [hvv, dist_comm]
            exact hgt2 i
          · have hd2 : scsDiag s.k i0 i :=
              ⟨fun h => hci h.symm, fun h => had1 h.symm, fun h => had2 h.symm⟩
            exact lt_of_le_of_lt (hadiag i0 i hd2).1 (hadiag i0 i hd2).2
      rcases CIZMRRH hlf3 with hgen3 | hcirc3 | hlun3
      · have hlunar : ∀ (V2 : Set V3) (E2 : Set (Set V3)) (v1 : V3),
            V2 = Set.range v → E2 = Set.range (fun i => {v i, v (i + 1)}) →
              ¬ Lunar v1 (v i0) V2 E2 := by
          intro V2 E2 v1 hV2 hE2 hl
          apply hgen3.2
          refine Or.inr ⟨v1, v i0, ?_⟩
          have hl' : Lunar v1 (v i0) V E := by rwa [hV2, hE2] at hl
          simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hl'
        exact False.elim (ODXLSTCv2_p28 s s.k v i0 hs hMMs rfl hk3
          (fun i hd => hb i0 i hd) hi0 hlt2 hJ hlunar)
      · exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
      · obtain ⟨v', w', hl3⟩ := hlun3.1
        have hlun : Lunar v' w' V E := by
          simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hl3
        have hflatI : ∀ u ∈ V \ {v', w'}, interiorAngle1 0 FF u = Real.pi :=
          (HKIRPEP_ALT_p37 hclf hlun).1
        obtain ⟨j, hjv'⟩ := hlun.2.1 (show v' ∈ ({v', w'} : Set V3) by simp)
        obtain ⟨j2, hjw'⟩ := hlun.2.1 (show w' ∈ ({v', w'} : Set V3) by simp)
        subst hjv'; subst hjw'
        have hinj : ∀ x y, x < s.k → y < s.k → x ≠ y → v x ≠ v y :=
          fun x y hx hy hxy => VV_INJ_p35 s s.k v rfl hs hBB x y ⟨hx, hy, hxy⟩
        have hmodv : ∀ a b : ℕ, v a = v b → a % s.k = b % s.k := by
          intro a b hab
          by_contra hab'
          exact hinj (a % s.k) (b % s.k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0)
            hab' (by rw [← periodic_mod_p27 hper a, ← periodic_mod_p27 hper b]; exact hab)
        have hne2 : j % s.k ≠ j2 % s.k := by
          intro h
          apply hlun.2.2.1
          rw [periodic_mod_p27 hper j, periodic_mod_p27 hper j2, h]
        have hflatt2 : ∀ t, t % s.k ≠ j % s.k → t % s.k ≠ j2 % s.k →
            azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi := by
          intro t ht1 ht2
          have hmem : v t ∈ V \ {v j, v j2} := by
            refine ⟨⟨t, rfl⟩, ?_⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨fun hc => absurd (hmodv t j hc) ht1,
              fun hc => absurd (hmodv t j2 hc) ht2⟩
          have hI := hflatI _ hmem
          rw [hid t] at hI
          exact hI
        have hcop2 := jcyfmrp_flat_residues_coplanar s v hs hMMs hk3 hBB hper hgen0
          (j % s.k) (j2 % s.k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hne2 hflatt2
        exact absurd hcop2 (FEKTYIY_p27 s v hs hMMs hk3)
  -- DISCHARGES (2026-11-12, lane jcyfmrp-w2): HOL JCYFMRP.hl:256-608 via the
  -- unlocked `CUXVZOZ_p21` (LA21) + `SCS_M_LE_1_p27`; the J-empty branch
  -- routes through `ODXLSTCv2_p28` (LA28); the all-flat and lunar cases are
  -- killed by the ported AURSIPD geo kit + `FEKTYIY_p27`.  Zero new sorries;
  -- axioms face = standard three.

/-! ## Section C: JLXFDMJ -/

/-- HOL `FINITE_SCS_M` (JLXFDMJ.hl:139). -/
theorem FINITE_SCS_M_p27 (s : ScsV39) : (scsM s).Finite := by
  exact (Set.finite_lt_nat s.k).subset (by
    intro i hi
    rw [scsM] at hi
    exact hi.1)

/-- HOL `SCS_M_EQ_0` (JLXFDMJ.hl:92). -/
theorem SCS_M_EQ_0_p27 (s : ScsV39) :
    isScsV39 s → (∀ i, s.a i (i + 1) = 2) → (scsM s).ncard = 0 → scsM s = ∅ := by
  intro hs hA hcard0
  rw [Set.ncard_eq_zero (FINITE_SCS_M_p27 s)] at hcard0
  exact hcard0

/-- HOL `SCS_M_LE_K` (JLXFDMJ.hl:207): with empty `scs_M` no residue lies in
it (stated in the `< k` form used by the archive). -/
theorem SCS_M_LE_K_p27 (s : ScsV39) :
    scsM s = ∅ → ∀ i, i % s.k ∈ scsM s → i % s.k < s.k := by
  intro h i hi
  rw [h] at hi
  exact False.elim hi

/-- HOL `SCS_M_EQ_1` (JLXFDMJ.hl:159).  SF-97 (2026-11-03): the first
rendering (`3 ≤ k → (∀ i, a < b) → isScs → i ∈ scsM s → (scsM s).ncard = 1`)
inverted the HOL direction and is FALSE (scsgeneric-recon witness: k = 4,
edges 0 and 1 both pinned at (2.5, 2.6) give `scsM s = {0, 1}`).  HOL takes
the singleton `scs_M s = {x}` as a premise and concludes the pinned-edge
shape off `x`; it is the singleton instance of `SCS_M_LE_1_p27`. -/
theorem SCS_M_EQ_1_p27 (s : ScsV39) (x : ℕ) :
    scsM s = {x} → isScsV39 s →
      ∀ i, ¬ (i % s.k = x) → s.b i (i + 1) ≤ 2 * h0 ∧ s.a i (i + 1) = 2 := by
  intro hM hs
  have hcard : (scsM s).ncard ≤ 1 := by rw [hM, Set.ncard_singleton]
  obtain ⟨p, hp⟩ := SCS_M_LE_1_p27 s hcard hs
  have hx : x ∈ scsM s := by rw [hM]; exact Set.mem_singleton x
  have hx' := hx
  simp only [scsM, Set.mem_setOf_eq] at hx'
  have hxp : x = p % s.k := by
    by_contra hne
    have hxx : ¬ (x % s.k = p % s.k) := by rw [Nat.mod_eq_of_lt hx'.1]; exact hne
    obtain ⟨hb, ha⟩ := hp x hxx
    rcases hx'.2 with h | h
    · exact absurd hb (not_le.mpr h)
    · rw [ha] at h; exact lt_irrefl _ h
  intro i hi
  apply hp i
  rw [← hxp]; exact hi

/-- HOL `JLXFDMJ_concl` (JLXFDMJ.hl:214). The `∀ j` premise uses the faithful
`j % s.k ∉ scsM s` (HOL `~(j MOD k IN scs_M_v39 s)`). -/
theorem JLXFDMJ_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
        isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
          dist (v i) (v (i + 1)) = 2 →
            (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
              (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
                (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
                  s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
                    ∀ j, j % s.k ∉ scsM s → dist (v j) (v (j + 1)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS `SCS_M_EQ_1` and the `CHANGE_B/A_SCS_MOD` folds
    -- matching `j % k` against the single `scs_M` index; then a `P_BBQUESTION`
    -- a=2, b≤2h0 edge-variation step over `main_nonlinear_terminal_v11`.

/-! ## Section D: SGTRNAF -/

/-- HOL `UXCKFPE2` (SGTRNAF.hl:75).
DISCHARGED: `UXCKFPE_p24` (LocalAuto24, the proved k = 3..6 case assembly;
its case lemmas remain `sorry` in that lane) gives `BBprimeV39 s ≠ ∅`, so the
index image `BBindexV39 s '' BBprimeV39 s` is a nonempty set of naturals;
its least element `BBindexMinV39 s` (`minNum` = `Classical.epsilon`, least by
`Nat.sInf`) is attained, and the attaining witness lands in `BBprime2V39 s`.
RESIDUAL: the depth sits in LocalAuto24's `XWITCCN_CASE_*_IS_SCS_p24`. -/
theorem UXCKFPE2_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  intro s vv hs hBB hta
  have hbp : (BBprimeV39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE_p24 s vv hs hBB hta
  have himage : (BBindexV39 s '' BBprimeV39 s).Nonempty := by
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hbp
    exact ⟨BBindexV39 s w, w, hw, rfl⟩
  have hmin : BBindexMinV39 s ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, BBindexMinV39 s ≤ m :=
    Classical.epsilon_spec (p := fun n => n ∈ BBindexV39 s '' BBprimeV39 s ∧
      ∀ m ∈ BBindexV39 s '' BBprimeV39 s, n ≤ m)
      ⟨sInf _, Nat.sInf_mem himage, fun m hm => Nat.sInf_le hm⟩
  obtain ⟨w, hwprime, hwidx⟩ := hmin.1
  intro hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  exact hcon w ⟨hwprime, hwidx⟩

/-- HOL `SGTRNAF` (SGTRNAF.hl:166). Consumed by the packing chapter through
the regime-ANCHOR `sgtrnaf_p12` (LocalAuto12:272).
DISCHARGED: `UXCKFPE2_p27` gives `BBprime2V39 s ≠ ∅` and `unadorned_MMs_p27`
rewrites `MMsV39 s` to it (the HOL proof is `MATCH_MP_TAC UXCKFPE2` after
rewriting `MMs` via `unadorned_MMs`). -/
theorem SGTRNAF_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    unadornedV39 s → BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  intro s vv hs hu hBB hta
  -- `unadorned_MMs_p27` (Section F) is declared below; the MMs membership is
  -- inlined here (False-vacuous str/lo/hi guards, a/am and b/bm bounds).
  have h2 : (BBprime2V39 s : Set (ℕ → V3)) ≠ ∅ := UXCKFPE2_p27 s vv hs hBB hta
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  intro hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  obtain ⟨w, hwprime, hwidx⟩ := Set.nonempty_iff_ne_empty.mpr h2
  exact hcon w ⟨⟨hwprime, hwidx⟩,
    fun i hi => by rw [hstr] at hi; exact hi.elim,
    fun i hi => by rw [hlo] at hi; exact hi.elim,
    fun i hi => by rw [hhi] at hi; exact hi.elim,
    fun i j => by rw [← ham]; exact (hwprime.1.2.2.1 i j).1,
    fun i j => by rw [← hbm]; exact (hwprime.1.2.2.1 i j).2⟩

/-! ## Section E: HXHYTIJ -/

/-- HOL `HXHYTIJ` (HXHYTIJ.hl:79).
DISCHARGED: the `min_num`/choice argument of the source, done directly: if
`taustar vv ≥ taustar ww` then `ww` itself attains the `BBs`-minimum (the
`BBprime` minimality of `vv` transfers through `taustar ww ≤ taustar vv`), so
`BBindex ww` lies in the index image and the `BBindexMin` choice value
(`minNum` = least element, attained as in `UXCKFPE2_p27`) bounds it, while
`BBindex vv = BBindexMin` by `BBprime2` membership. The `isScsV39 s`
hypothesis is carried but not needed for this reading. -/
theorem HXHYTIJ_p27 : ∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww := by
  intro s vv ww _hs hvv hww
  by_cases hlt : taustarV39 s vv < taustarV39 s ww
  · exact Or.inl hlt
  · right
    have hle : taustarV39 s ww ≤ taustarV39 s vv := not_lt.mp hlt
    have hwp : ww ∈ (BBprimeV39 s : Set (ℕ → V3)) :=
      ⟨hww, fun w' hw' => le_trans hle (hvv.1.2.1 w' hw'),
        lt_of_le_of_lt hle hvv.1.2.2⟩
    have himage : BBindexV39 s ww ∈ BBindexV39 s '' BBprimeV39 s :=
      ⟨ww, hwp, rfl⟩
    have himageN : (BBindexV39 s '' BBprimeV39 s).Nonempty := ⟨_, himage⟩
    have hmin : ∀ m ∈ BBindexV39 s '' BBprimeV39 s, BBindexMinV39 s ≤ m :=
      (Classical.epsilon_spec (p := fun n => n ∈ BBindexV39 s '' BBprimeV39 s ∧
        ∀ m ∈ BBindexV39 s '' BBprimeV39 s, n ≤ m)
        ⟨sInf _, Nat.sInf_mem himageN, fun m hm => Nat.sInf_le hm⟩).2
    exact hvv.2.trans_le (hmin _ himage)

/-! ## Section F: AYQJTMD -/

/-! ### Section F1: the `sInitListV39` `isScs` substrate (2026-09-21 fill wave)

`s_init_scs_p27` below closes the only gap between the s_init section (`Section
F2`) and the proved `UXCKFPE2_p27`/`SGTRNAF_p27` of Section D: an
`isScsV39` certificate for every `sInitListV39` member. Entries 1-6 of the
list are the named `scs6I1`..`scs4I2` constants, so their `is_scs_*_p22`
(LocalAuto22) certificates apply up to `rfl`; entry 7 and entry 8 are inlined
`a_pro` lambdas, so `init7a/b_p27`, `init8a/b_p27` identify them with the
`funlistV39` tables of `scs5I3`/`scs4I3`, and `SCS_5I3_IS_SCS` /
`init8_isScs_p27` give the certificates.

The `init_pair_01_p27` set-equality rewrite is only needed so `simp` can see
the `{i, j} = {0, 1}` guards as arithmetic; `periodic2_funlist_p20` and
`funlist_mod_p20` (LocalAuto20) drive the periodicity/cardinality of
`init8_isScs_p27`. -/

/-- `{a, b} = {0, 1}` (a set of two naturals) iff one is `0` and the other
`1`; rewrites the `{i, j} = {0, 1}` guards of the raw `a_pro` lambdas in
`sInitListV39` into arithmetic for `simp`. -/
@[simp]
theorem init_pair_01_p27 (a b : ℕ) : ({a, b} : Set ℕ) = {0, 1} ↔
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have ha : a = 0 ∨ a = 1 := by
      have : a ∈ ({0, 1} : Set ℕ) := by rw [← h]; simp
      simpa using this
    have hb : b = 0 ∨ b = 1 := by
      have : b ∈ ({0, 1} : Set ℕ) := by rw [← h]; simp
      simpa using this
    rcases ha with ha0 | ha1
    · rcases hb with hb0 | hb1
      · exfalso
        have : (1 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
        have hc : (1 : ℕ) = a ∨ (1 : ℕ) = b := by simpa using this
        omega
      · left; exact ⟨ha0, hb1⟩
    · rcases hb with hb0 | hb1
      · right; exact ⟨ha1, hb0⟩
      · exfalso
        have : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
        have hc : (0 : ℕ) = a ∨ (0 : ℕ) = b := by simpa using this
        omega
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals ext x
    all_goals simp
    all_goals omega

/-- The sInit entry-7 a-field: the inlined `a_pro` lambda (k = 5) equals the
`funlistV39` table of `scs5I3` (its a-value `2` = the `d` default). -/
theorem init7a_p27 :
    (fun i j =>
      if i % 5 = j % 5 then 0
      else if ({i % 5, j % 5} : Set ℕ) = {0, 1} then 2 * h0
      else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then 2 else 2 * h0) =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
        ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 := by
  funext i j
  have hi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj : j % 5 < 5 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 5 1]
  rw [← Nat.mod_add_mod j 5 1]
  simp only [funlistV39, psort]
  interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]

theorem init7b_p27 :
    (fun i j =>
      if i % 5 = j % 5 then 0
      else if ({i % 5, j % 5} : Set ℕ) = {0, 1} then Real.sqrt 8
      else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then 2 * h0 else 6) =
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6),
        ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 := by
  funext i j
  have hi : i % 5 < 5 := Nat.mod_lt i (by omega)
  have hj : j % 5 < 5 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 5 1]
  rw [← Nat.mod_add_mod j 5 1]
  simp only [funlistV39, psort]
  interval_cases i % 5 <;> interval_cases j % 5 <;> simp [assocdV39]

theorem init8a_p27 :
    (fun i j =>
      if i % 4 = j % 4 then 0
      else if ({i % 4, j % 4} : Set ℕ) = {0, 1} then 2 * h0
      else if j % 4 = (i + 1) % 4 ∨ (j + 1) % 4 = i % 4 then 2 else Real.sqrt 8) =
      funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2 4 := by
  funext i j
  have hi : i % 4 < 4 := Nat.mod_lt i (by omega)
  have hj : j % 4 < 4 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 4 1]
  rw [← Nat.mod_add_mod j 4 1]
  simp only [funlistV39, psort]
  interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]

theorem init8b_p27 :
    (fun i j =>
      if i % 4 = j % 4 then 0
      else if ({i % 4, j % 4} : Set ℕ) = {0, 1} then Real.sqrt 8
      else if j % 4 = (i + 1) % 4 ∨ (j + 1) % 4 = i % 4 then 2 * h0 else 6) =
      funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4 := by
  funext i j
  have hi : i % 4 < 4 := Nat.mod_lt i (by omega)
  have hj : j % 4 < 4 := Nat.mod_lt j (by omega)
  rw [← Nat.mod_add_mod i 4 1]
  rw [← Nat.mod_add_mod j 4 1]
  simp only [funlistV39, psort]
  interval_cases i % 4 <;> interval_cases j % 4 <;> simp [assocdV39]

/-- `isScsV39 scs4I3` (the sInit entry-8 system, k = 4). Built directly over
`periodic2_funlist_p20`; the mod-step arithmetic and the `√8` bounds use only
LocalAuto20 kit (`LE_sqrt8_2`, `sqrt8_LE_6`, `LE_sqrt8_2h0`, `LT_sqrt8_2h0`,
`sqrt8_LE_CSTAB`, `two_lt_two_h0'`, `two_h0_lt_cstab_p20`). -/
theorem init8_isScs_p27 : isScsV39 scs4I3 := by
  unfold isScsV39 scs4I3 mkUnadornedV39
  dsimp only
  have pa : Periodic2 (funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8),
        ((1, 3), Real.sqrt 8)] 2 4) 4 := periodic2_funlist_p20 _ _ _
  have pb : Periodic2 (funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
        (2 * h0) 4) 4 := periodic2_funlist_p20 _ _ _
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
      first | exact LE_sqrt8_2h0 | exact sqrt8_LE_6 | exact LE_sqrt8_2 | norm_num [h0, cstab]
  · intro i; simp [funlistV39]
  · intro i j ⟨hik, hjk, hne⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [funlistV39, psort, assocdV39] <;>
      first | exact LE_sqrt8_2 | exact LE_sqrt8_2h0 | norm_num [h0, cstab]
  · intro i hk3
    omega
  · intro i hk4
    rw [← funlist_mod_p20 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
        (2 * h0) 4 i (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
    have hz : i % 4 < 4 := Nat.mod_lt i (by omega)
    interval_cases i % 4 <;> simp [funlistV39, psort, assocdV39] <;>
      first | exact sqrt8_LE_CSTAB | norm_num [h0, cstab]
  · have key : ∀ r : ℕ, r < 4 →
        ((2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
              (2 * h0) 4 r ((r + 1) % 4) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
              2 4 r ((r + 1) % 4)) ↔ r = 0) := by
      intro r hr
      interval_cases r <;>
        simp [funlistV39, psort, assocdV39, LT_sqrt8_2h0]
    have hS : {i | i < 4 ∧ (2 * h0 < funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6),
              ((1, 3), 6)] (2 * h0) 4 i (i + 1) ∨
            2 < funlistV39 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
              2 4 i (i + 1))} = {0} := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [← funlist_mod_p20 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((1, 3), 6)]
          (2 * h0) 4 i (i + 1) (by omega),
        ← funlist_mod_p20 [((0, 1), 2 * h0), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)]
          2 4 i (i + 1) (by omega), ← Nat.mod_add_mod i 4 1]
      rw [key (i % 4) (Nat.mod_lt i (by omega))]
      omega
    rw [hS]
    simp

/-- Every `sInitListV39` member is an `isScsV39` system: entries 1-6 are the
named `scs6I1`..`scs4I2` constants (`is_scs_*_p22`, LocalAuto22); entry 7 is
`scs5I3` (`SCS_5I3_IS_SCS`, LocalAuto20) and entry 8 is `scs4I3`
(`init8_isScs_p27`), after the inlined `a_pro` lambdas are identified with the
`funlistV39` tables via `init7a/b_p27`, `init8a/b_p27`. -/
theorem s_init_scs_p27 (s : ScsV39) (hs : s ∈ sInitListV39) : isScsV39 s := by
  simp only [sInitListV39, List.mem_cons, List.not_mem_nil] at hs
  rcases hs with he | he | he | he | he | he | he | he | he
  · rw [he]; exact is_scs_6I1_p22
  · rw [he]; exact is_scs_5I1_p22
  · rw [he]; exact is_scs_4I1_p22
  · rw [he]; exact is_scs_3I1_p22
  · rw [he]; exact is_scs_5I2_p22
  · rw [he]; exact is_scs_4I2_p22
  · rw [he]
    rw [init7a_p27, init7b_p27]
    exact SCS_5I3_IS_SCS
  · rw [he]
    rw [init8a_p27, init8b_p27]
    exact init8_isScs_p27
  · exact absurd he (by simp)

/-! ### Section F2: `XWITCCN2`, `unadorned_MMs`, `S_INIT_IS_UNADORNED`, `AYQJTMD`, `EAPGLE` -/

/-- HOL `XWITCCN2` (AYQJTMD.hl:72).
DISCHARGED: `s_init_scs_p27` (Section F1) gives `isScsV39 s` for every
`sInitListV39` member, so `UXCKFPE2_p27` (Section D) applies with
`taustarV39 s vv < 0`. -/
theorem XWITCCN2_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  intro s vv hs hBB hta
  exact UXCKFPE2_p27 s vv (s_init_scs_p27 s hs) hBB hta

/-- HOL `unadorned_MMs` (AYQJTMD.hl:161). Also the engine of `SGTRNAF`.
DISCHARGED: definitional — for an unadorned system the `str`/`lo`/`hi`
guards are `False`-vacuous and `a = am`, `b = bm` turn the `MMs` tail bounds
into the `BBs` bounds, so `MMsV39 s = BBprime2V39 s` outright. -/
theorem unadorned_MMs_p27 : ∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s := by
  intro s hu
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  ext vv
  simp only [MMsV39, BBprime2V39, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨hp, hidx⟩ := h
    refine ⟨⟨hp, hidx⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i hi => by rw [hstr] at hi; exact hi.elim
    · exact fun i hi => by rw [hlo] at hi; exact hi.elim
    · exact fun i hi => by rw [hhi] at hi; exact hi.elim
    · intro i j
      rw [← ham]
      exact (hp.1.2.2.1 i j).1
    · intro i j
      rw [← hbm]
      exact (hp.1.2.2.1 i j).2

/-- HOL `S_INIT_IS_UNADORNED` (AYQJTMD.hl:194).
DISCHARGED: all eight `sInitListV39` entries are `mkUnadornedV39` records,
whose `lo`/`hi`/`str` fields are `False` and whose `a`/`b` equal their
`am`/`bm` fields definitionally. -/
theorem S_INIT_IS_UNADORNED_p27 : ∀ s, s ∈ sInitListV39 → unadornedV39 s := by
  intro s hs
  simp only [sInitListV39, List.mem_cons, List.not_mem_nil] at hs
  rcases hs with h | h | h | h | h | h | h | h | h
  <;> first
    | (rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    | exact absurd h (by simp)

/-- HOL `AYQJTMD` (AYQJTMD.hl:206).
DISCHARGED: `s_init_scs_p27` (Section F1) plus `S_INIT_IS_UNADORNED_p27`
put `s` in the scope of `SGTRNAF_p27` (Section D), giving `MMsV39 s ≠ ∅`. -/
theorem AYQJTMD_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  intro s vv hs hBB hta
  exact SGTRNAF_p27 s vv (s_init_scs_p27 s hs) (S_INIT_IS_UNADORNED_p27 s hs) hBB hta

/-- HOL `EAPGLE` (AYQJTMD.hl:222).
DISCHARGED (la27-eapgle-w2 2026-10-28): the HOL route — apply the registry
arrow, here the REIFIED LA25 twin `ZITHLQN_p25` (LocalAuto25, statement
identical to the still-`sorry` LocalAuto1 registry arrow `ZITHLQN_concl`,
whose blanket body is thereby bypassed on this path), and kill its
`taustar < 0` branch with the contrapositive of `AYQJTMD_p27` (Section F2;
this is exactly what HOL EAPGLE consumes at AYQJTMD.hl:232-241). Honest
face: zero new sorries; the axiom face inherits `sorryAx` from two
corpus-blocked root families — `exists_vv_p25` (LocalAuto25, the `rhoNode1`
dart-cycle enumerator inside `ZITHLQN_p25`'s Section-A assembly; FF→rhoNode1
dart-layer bridge is a corpus-level blocker) and the `UXCKFPE_p24` k = 3
case `XWITCCN_CASE_3_IS_SCS_p24` → LA23 `bodyClosed_p23` /
`continuousOn_tauFun_p23` (the k = 4/5/6 cases are real bodies), via
`UXCKFPE2_p27`/`SGTRNAF_p27`/`AYQJTMD_p27`. -/
theorem EAPGLE_p27 :
    (∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39 := by
  intro h
  refine ZITHLQN_p25 ?_
  intro s hs vv hBB
  -- the taustar dichotomy; the negative branch dies on the contrapositive
  -- of AYQJTMD_p27 against the hypothesis `MMsV39 s = ∅`
  have hsplit : taustarV39 s vv < 0 ∨ 0 ≤ taustarV39 s vv := by
    by_contra hcon
    rw [not_or] at hcon
    linarith
  rcases hsplit with hneg | hpos
  · exact absurd (h s hs) (AYQJTMD_p27 s vv hs hBB hneg)
  · exact hpos

/-! ## Section H: LKGRQUI -/

/-- HOL `SLICE_IS_UNADORNED` (LKGRQUI.hl:82). -/
theorem SLICE_IS_UNADORNED_p27 :
    ∀ s p q d' mkj, unadornedV39 (scsHalfSliceV39 s p q d' mkj) := by
  intro s p q d' mkj
  simp [unadornedV39, scsHalfSliceV39]

/-- MMs membership factors into the BBs + negative-taustar pair consumed
by SGTRNAF (BBprimeV39 components 1 and 3). -/
theorem mm_BBs_taustar_p27 (s : ScsV39) (vv : ℕ → V3) (h : vv ∈ MMsV39 s) :
    BBsV39 s vv ∧ taustarV39 s vv < 0 := by
  simp only [MMsV39, BBprime2V39, BBprimeV39, Set.mem_setOf_eq] at h
  exact ⟨h.1.1.1, h.1.1.2.2⟩

/-- `scsDiag` is symmetric under swapping the two indices. -/
theorem scsDiag_symm_p27 {k i j : ℕ} (h : scsDiag k i j) : scsDiag k j i :=
  ⟨fun hc => h.1 hc.symm, fun hc => h.2.2 hc.symm, fun hc => h.2.1 hc.symm⟩

/-- HOL `LKGRQUI` (LKGRQUI.hl:87).  Assembly over the LA35 engine
(`SCS_HALF_SLICE_IS_A_SCS_p35` / `SCS_SLICE_SYM_p35` / `QKNVMLB1_p35` /
`QKNVMLB3_p35`) + `SLICE_IS_UNADORNED_p27` + `SGTRNAF_p27`; the body is a
real proof (lkgrqui-engine-w1 E4) and its axiom face follows the LA35 roots
as they close. -/
theorem LKGRQUI_p27 : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
    isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    scsArrowV39 {s} {s', s''} := by
  intro s s' s'' p q d' d'' mkj hscs hdiag hsl
  have hscs0 := hscs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsymrec, -, -, -, -, -, -, -, -⟩ := hscs0
  have hsl0 := hsl
  simp only [isScsSliceV39, scsSliceV39, Prod.mk.injEq] at hsl
  obtain ⟨⟨hs', hs''⟩, hd'lt, hd''lt, hdle, hbm4, hdisj, hmkj⟩ := hsl
  -- both halves conform: E1 on the slice and on its SCS_SLICE_SYM flip
  have hscs' : isScsV39 s' :=
    SCS_HALF_SLICE_IS_A_SCS_p35 s s' s'' p q hscs hdiag hsl0
  have hsym : isScsSliceV39 s s'' s' q p :=
    (SCS_SLICE_SYM_p35 s s' s'' p q hscs hdiag).mp hsl0
  have hscs'' : isScsV39 s'' :=
    SCS_HALF_SLICE_IS_A_SCS_p35 s s'' s' q p hscs (scsDiag_symm_p27 hdiag) hsym
  -- both halves adorned-free
  have hun' : unadornedV39 s' := by
    rw [hs']; exact SLICE_IS_UNADORNED_p27 s p q s'.d (s'.J 0 (s'.k - 1))
  have hun'' : unadornedV39 s'' := by
    rw [hs'']; exact SLICE_IS_UNADORNED_p27 s q p s''.d (s'.J 0 (s'.k - 1))
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases Set.mem_insert_iff.mp ht with he | ht2
    · rw [he]; exact hscs'
    · rw [Set.mem_singleton_iff.mp ht2]; exact hscs''
  · rcases eq_empty_or_nonempty (MMsV39 s) with h0 | h0
    · left
      intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      exact h0
    · right
      obtain ⟨vv, hvv⟩ := h0
      obtain ⟨hBB, hta⟩ := mm_BBs_taustar_p27 s vv hvv
      -- BBs transport into both halves (E2 twice) + taustar superadditivity (E3)
      have hBB1 : BBsV39 s' (fun i => vv (i % s'.k + p % s.k)) :=
        QKNVMLB1_p35 s p q s'.d (s'.J 0 (s'.k - 1)) vv hvv hbm4 hdisj hscs hd'lt
          hdiag s' hs' _ rfl
      have hbm4' : s.bm q p < 4 := by
        rw [← (hsymrec p q).2.2.1]
        exact hbm4
      have hdisj' : s.k = 4 ∨ s.bm q p ≤ cstab := by
        rw [← (hsymrec p q).2.2.1]
        exact hdisj
      have hBB2 : BBsV39 s'' (fun i => vv (i % s''.k + q % s.k)) :=
        QKNVMLB1_p35 s q p s''.d (s'.J 0 (s'.k - 1)) vv hvv hbm4' hdisj' hscs
          hd''lt (scsDiag_symm_p27 hdiag) s'' hs'' _ rfl
      have hsum := QKNVMLB3_p35 s s' s'' p q s'.d s''.d (s'.J 0 (s'.k - 1)) vv
        (fun i => vv (i % s'.k + p % s.k)) (fun i => vv (i % s''.k + q % s.k))
        hs'.symm hs''.symm rfl rfl hvv hscs hdiag hsl0 hdle
      have hneg : taustarV39 s' (fun i => vv (i % s'.k + p % s.k)) < 0 ∨
          taustarV39 s'' (fun i => vv (i % s''.k + q % s.k)) < 0 := by
        by_contra hcon
        rw [not_or] at hcon
        linarith
      rcases hneg with h1 | h2
      · refine ⟨s', Set.mem_insert s' {s''}, ?_⟩
        exact SGTRNAF_p27 s' _ hscs' hun' hBB1 h1
      · refine ⟨s'', Set.mem_insert_of_mem _ (Set.mem_singleton _), ?_⟩
        exact SGTRNAF_p27 s'' _ hscs'' hun'' hBB2 h2