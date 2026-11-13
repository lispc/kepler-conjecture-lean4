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
    `TFITSKCv1_p27` (proved), `TFITSKC_p27` (proved).
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

/-- TFITSKCv1 proof-wave kit (2026-11-12, lane tfitskcv1-w1): the
mod-`k` distinctness from a diagonal, the generic-fan flat-node geometry
(`PROPERTIES_GENERIC` + `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` +
`AFF_GE_TO_AFF_GT2_GE1` + `FAN_IMP_NOT_IN_AFF_GE`, HOL TFITSKC.hl:200-264),
the `CIZMRRH`-lunar fork killed by the JCYFMRP coplanarity engine +
`FEKTYIY_p27` (HOL handles it with the `ODXLSTCv2`/`NUXCOEAv2`/`CJBDXXN`
w2-machinery; the coplanarity route is the same mathematical content with
fewer cases), and the two `CUXVZOZ_p21` closers.  Declared after
`jcyfmrp_flat_residues_coplanar` (the lunar fork consumes it), hence
`TFITSKCv1_p27` itself is proved at this point of the file. -/
private theorem tfitskcv1_ne_of_diag (s : ScsV39) (v : ℕ → V3) (hs : isScsV39 s)
    (hBB : BBsV39 s v) {a b : ℕ} (hd : scsDiag s.k a b) : v a ≠ v b := by
  have hk0 : 0 < s.k := by have := hs.2.1; omega
  have hinj := VV_INJ_p35 s s.k v rfl hs hBB
  intro he
  have h2 : v (a % s.k) = v (b % s.k) := by
    rw [← periodic_mod_p27 hBB.2.1 a, ← periodic_mod_p27 hBB.2.1 b]
    exact he
  exact hinj (a % s.k) (b % s.k) ⟨Nat.mod_lt _ hk0, Nat.mod_lt _ hk0, hd.1⟩ h2

/-- TFITSKCv1 proof-wave kit: at a generic-fan node `v l` whose interior
angle is flat (`azim 0 (v l) (v (l+1)) (v (l + k - 1)) = pi`), the two
neighbour vertices are not collinear with the origin and `v l` lies in the
open affine wedge of them.  Shared by the `NUXCOEAv2_p28` / `IMJXPHRv2_p28`
applications at `l := i+1` and `l := i+2` (HOL TFITSKC.hl:200-264 and
:483-524 respectively, modulo the periodicity fold `v (l + k - 1) = v (l-1)`). -/
private theorem tfitskcv1_geo (s : ScsV39) (v : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hBB : BBsV39 s v)
    (hg2 : generic_p2 (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)))
    (hlf2 : localFan_p2 (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))))
    (l : ℕ)
    (hπ : azim 0 (v l) (v (l + 1)) (v (l + (s.k - 1))) = Real.pi)
    (hne1 : v (l + 1) ≠ v (l + (s.k - 1)))
    (hne2 : v l ≠ v (l + 1)) (hne3 : v l ≠ v (l + (s.k - 1))) :
    ¬ Collinear ℝ ({0, v (l + 1), v (l + (s.k - 1))} : Set V3) ∧
      v l ∈ affGt {0} ({v (l + 1), v (l + (s.k - 1))} : Set V3) := by
  have hlf2c := hlf2
  obtain ⟨-, -, -, -, -, hfan2, -, -⟩ := hlf2c
  have hlV : v l ∈ Set.range v := ⟨l, rfl⟩
  have hl1 : v (l + 1) ∈ Set.range v := ⟨l + 1, rfl⟩
  have hlm : v (l + (s.k - 1)) ∈ Set.range v := ⟨l + (s.k - 1), rfl⟩
  have hnc1 : ¬ Collinear ℝ ({0, v (l + 1), v (l + (s.k - 1))} : Set V3) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf2 (fun _ _ => True.intro) hg2 (v (l + 1)) hl1
      (v (l + (s.k - 1))) hlm hne1.symm
  have h1 : ¬ Collinear3 (0 : V3) (v l) (v (l + (s.k - 1))) := by
    have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf2 (fun _ _ => True.intro) hg2 (v l) hlV
      (v (l + (s.k - 1))) hlm hne3.symm
    simpa only [Collinear3] using h
  have h2 : ¬ Collinear3 (0 : V3) (v l) (v (l + 1)) := by
    have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf2 (fun _ _ => True.intro) hg2 (v l) hlV
      (v (l + 1)) hl1 hne2.symm
    simpa only [Collinear3] using h
  have hdis : affGe ({0} : Set V3) ({v l, v (l + 1)} : Set V3) ∩
      affLt ({0} : Set V3) ({v (l + (s.k - 1))} : Set V3) = ∅ :=
    hg2 (v l) (v (l + 1)) (v (l + (s.k - 1)))
      (Set.mem_range.mpr ⟨l, rfl⟩) hlm
  have hst : v l ∈ affGe ({0} : Set V3) ({v (l + (s.k - 1)), v (l + 1)} : Set V3) :=
    GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE (u := v (l + (s.k - 1))) (v := v l) (w := v (l + 1))
      h1 h2 hπ hdis
  have hne0a : (0 : V3) ≠ v l := fun h0 => hfan2.2.2.2.1 (h0 ▸ hlV)
  have hne0b : (0 : V3) ≠ v (l + 1) := fun h0 => hfan2.2.2.2.1 (h0 ▸ hl1)
  have hne0c : (0 : V3) ≠ v (l + (s.k - 1)) := fun h0 => hfan2.2.2.2.1 (h0 ▸ hlm)
  have hst2 := AFF_GE_TO_AFF_GT2_GE1 (x := (0 : V3)) (u := v (l + (s.k - 1))) (v := v (l + 1))
    (Ne.symm hne0c) (Ne.symm hne0b)
  rw [hst2] at hst
  refine ⟨hnc1, ?_⟩
  rcases (Set.mem_union _ _ _).mp hst with h | h
  · rcases (Set.mem_union _ _ _).mp h with h | h
    · rwa [Set.pair_comm] at h
    · exact absurd h (FAN_IMP_NOT_IN_AFF_GE hfan2
        (by simp only [Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hlV, hlm⟩)
        hne3)
  · exact absurd h (FAN_IMP_NOT_IN_AFF_GE hfan2
      (by simp only [Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hlV, hl1⟩)
      hne2)

/-- TFITSKCv1 proof-wave kit: the `CIZMRRH` lunar fork is impossible —
`HKIRPEP_ALT_p37` makes every non-apex vertex flat, so all residues but the
two apex residues are flat and `jcyfmrp_flat_residues_coplanar` +
`FEKTYIY_p27` give the contradiction (the JCYFMRP-p27 lunar pattern). -/
private theorem tfitskcv1_lunar_false (s : ScsV39) (v : ℕ → V3)
    (hs : isScsV39 s) (hMMs : v ∈ MMsV39 s) (hk3 : 3 < s.k) (hBB : BBsV39 s v)
    (hper : Periodic v s.k)
    (hgen0 : Generic (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)))
    (hclf : ConvexLocalFan (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3))
      (Set.range fun i => (v i, v (i + 1))))
    (hid : ∀ j, interiorAngle1 0 (Set.range fun i => (v i, v (i + 1))) (v j)
      = azim 0 (v j) (v (j + 1)) (v (j + (s.k - 1))))
    (hlun3 : (∃ a b, lunar_p3 (a, b) (Set.range v)
        (Set.range fun i => ({v i, v (i + 1)} : Set V3))) ∧
      ¬(generic_p3 (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) ∨
        circular_p3 (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)))) :
    False := by
  obtain ⟨v', w', hl3⟩ := hlun3.1
  have hlun : Lunar v' w' (Set.range v) (Set.range fun i => ({v i, v (i + 1)} : Set V3)) := by
    simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hl3
  have hflatI := (HKIRPEP_ALT_p37 hclf hlun).1
  obtain ⟨j, hjv'⟩ := hlun.2.1 (show v' ∈ ({v', w'} : Set V3) by simp)
  obtain ⟨j2, hjw'⟩ := hlun.2.1 (show w' ∈ ({v', w'} : Set V3) by simp)
  subst hjv'; subst hjw'
  have hk0 : 0 < s.k := by omega
  have hinj : ∀ x y, x < s.k → y < s.k → x ≠ y → v x ≠ v y :=
    fun x y hx hy hxy => VV_INJ_p35 s s.k v rfl hs hBB x y ⟨hx, hy, hxy⟩
  have hmodv : ∀ a b : ℕ, v a = v b → a % s.k = b % s.k := by
    intro a b hab
    by_contra hab'
    exact hinj (a % s.k) (b % s.k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hab'
      (by rw [← periodic_mod_p27 hper a, ← periodic_mod_p27 hper b]; exact hab)
  have hne2 : j % s.k ≠ j2 % s.k := by
    intro h
    apply hlun.2.2.1
    rw [periodic_mod_p27 hper j, periodic_mod_p27 hper j2, h]
  have hflatt2 : ∀ t, t % s.k ≠ j % s.k → t % s.k ≠ j2 % s.k →
      azim 0 (v t) (v (t + 1)) (v (t + (s.k - 1))) = Real.pi := by
    intro t ht1 ht2
    have hmem : v t ∈ Set.range v \ {v j, v j2} := by
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

/-- TFITSKCv1 proof-wave kit: the `CUXVZOZ_p21` closer at `p1 := i + 1`
with all the shared side conditions discharged from the hypotheses of
`TFITSKCv1_p27` (HOL TFITSKC.hl:331-364, obligation discharge at :338-374).
Only `hang` / `hcase` vary between the two consumers. -/
private theorem tfitskcv1_cuxvzoz (s : ScsV39) (v : ℕ → V3) (i : ℕ)
    (hmnl : main_nonlinear_terminal_v11) (FF : Set (V3 × V3))
    (hFF : FF = Set.range fun j => (v j, v (j + 1)))
    (hs : isScsV39 s) (hk3 : 3 < s.k) (hMMs : v ∈ MMsV39 s)
    (hbasic : scsBasicV39 s) (hgen : scsGeneric v) (hBB : BBsV39 s v)
    (ha12 : s.a (i + 1) (i + 2) = 2) (hb12 : s.b (i + 1) (i + 2) ≤ 2 * h0)
    (hd01 : dist (v i) (v (i + 1)) = 2)
    (hadiag : ∀ i2 j2, scsDiag s.k i2 j2 →
      s.a i2 j2 ≤ cstab ∧ cstab < dist (v i2) (v j2) ∧ 4 * h0 < s.b i2 j2)
    (hper : Periodic v s.k)
    (hang : interiorAngle1 0 FF (v (i + 1)) < Real.pi)
    (hcase : Real.pi / 2 < interiorAngle1 0 FF (v (i + 1)) ∨
      interiorAngle1 0 FF (v (i + 2)) < Real.pi) :
    dist (v (i + 1)) (v (i + 2)) = 2 := by
  have hc3 : (3 : ℝ) ≤ cstab := by unfold cstab; norm_num
  have hdg : scsDiag s.k i (i + 2) := SCS_DIAG_2_p27 s.k i hk3
  have hdd := hadiag i (i + 2) hdg
  have e0 : i + 1 + (s.k - 1) = i + s.k := by omega
  have e1 : v (i + 1 + (s.k - 1)) = v i := by rw [e0]; exact hper i
  have e2 : i + 1 + 1 = i + 2 := rfl
  have hd : 3 ≤ dist (v (i + 1 + (s.k - 1))) (v (i + 1 + 1)) := by
    rw [e1, e2]; linarith
  have ha : ∀ i2 j2, scsDiag s.k i2 j2 →
      psort s.k (i2, j2) ≠ psort s.k (i + 1 + (s.k - 1), i + 1 + 1) →
      s.a i2 j2 < dist (v i2) (v j2) := fun i2 j2 hd2 _ =>
    lt_of_le_of_lt (hadiag i2 j2 hd2).1 (hadiag i2 j2 hd2).2.1
  have hb : ∀ i2 j2, scsDiag s.k i2 j2 → 4 * h0 < s.b i2 j2 := fun i2 j2 hd2 =>
    (hadiag i2 j2 hd2).2.2
  have h2 : (2 : ℝ) ≤ dist (v (i + 1 + (s.k - 1))) (v (i + 1)) := by
    rw [e1, hd01]
  have hdc : dist (v (i + 1 + (s.k - 1))) (v (i + 1)) ≤ cstab := by
    rw [e1, hd01]; unfold cstab; norm_num
  have hres := CUXVZOZ_p21 hmnl s FF s.k (i + 1) v hFF hs rfl hk3 hMMs hbasic hgen
    hd ha hb hang hcase ha12 hb12 h2 hdc
  rw [e2] at hres
  exact hres

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
  intro hmnl s v i hJ2 hab23 hk3 hs hMMs hgen hbasic ha12 hb12 hd01 hdb0 hadiag
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
  set E : Set (Set V3) := Set.range (fun j => ({v j, v (j + 1)} : Set V3)) with hEdef
  set FF : Set (V3 × V3) := Set.range (fun j => (v j, v (j + 1))) with hFFdef
  have hk3' : ¬ s.k ≤ 3 := by omega
  have hclf : ConvexLocalFan V E FF := by
    rcases h4 with h3le | hcf
    · exact absurd h3le hk3'
    · simpa only [hVdef, hEdef, hFFdef] using hcf
  have hlf : LocalFan V E FF := hclf.1
  have hlf3 : localFan_p3 V E FF := localFanEquiv_p35.mp hlf
  have hlf2 : localFan_p2 V E FF := localFan_p2.of_localFan_p3 hlf3
  have hconv2 : convexLocalFan_p2 V E FF := w15_clf2 hclf
  have hrho2 : ∀ j, rhoNode1_p2 FF (v j) = v (j + 1) := fun j =>
    DETER_RHO_NODE hlf2 (v := v j) (w := v (j + 1))
      (show (v j, v (j + 1)) ∈ FF from Set.mem_range.mpr ⟨j, rfl⟩)
  have hrho : ∀ j, rhoNode1 FF (v j) = v (j + 1) := by
    intro j
    have hrp : rhoNode1_p2 FF (v j) = v (j + 1) := hrho2 j
    simpa only [rhoNode1, rhoNode1_p2] using hrp
  have hivs : ∀ j, ivsRhoNode1 FF (v j) = v (j + (s.k - 1)) := by
    intro j
    have hmem : (v (j + (s.k - 1)), v j) ∈ FF := by
      refine Set.mem_range.mpr ⟨j + (s.k - 1), ?_⟩
      have hper1 : v (j + (s.k - 1) + 1) = v j := by
        rw [show j + (s.k - 1) + 1 = j + s.k by omega]
        exact hper j
      rw [hper1]
    have hip : ivsRhoNode1_p2 FF (v j) = v (j + (s.k - 1)) :=
      PRE_IVS_RHO_NODE1_DETE hlf2 hmem
    simpa only [ivsRhoNode1, ivsRhoNode1_p2] using hip
  have hid : ∀ j, interiorAngle1 0 FF (v j)
      = azim 0 (v j) (v (j + 1)) (v (j + (s.k - 1))) := fun j => by
    simp only [interiorAngle1, hrho j, hivs j]
  have hgen0 : Generic (Set.range v)
      (Set.range fun j => ({v j, v (j + 1)} : Set V3)) := hgen
  have hinj : ∀ x y, x < s.k → y < s.k → x ≠ y → v x ≠ v y :=
    fun x y hx hy hxy => VV_INJ_p35 s s.k v rfl hs hBB x y ⟨hx, hy, hxy⟩
  have hmodv : ∀ a b : ℕ, v a = v b → a % s.k = b % s.k := by
    intro a b hab
    by_contra hab'
    exact hinj (a % s.k) (b % s.k) (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) hab'
      (by rw [← periodic_mod_p27 hper a, ← periodic_mod_p27 hper b]; exact hab)
  have hcirc : ¬ Circular V E := by
    have hq := JKQEWGV2_p23 s v hs hk3 hBB hta
    simpa only [hVdef, hEdef, Set.image_univ] using hq
  have hai : s.a i (i + 1) = 2 := DIST_EQ_2_IMP_A_EQ_2_p27 s v i hs hBB hd01
  have hJ1 : ∀ x, ¬ s.J (i + 1) x := J_EMPY_CASES_A_EQ_2_V1_p27 s i hai ha12 hs
  have h2le : (2 : ℝ) ≤ dist (v (i + 1)) (v (i + 2)) :=
    le_trans (SCS_A_2_p27 s hs (i + 1)) ((hBB.2.2.1 (i + 1) (i + 2)).1)
  by_cases hd2case : dist (v (i + 1)) (v (i + 2)) = 2
  · exact hd2case
  · have h12 : 2 < dist (v (i + 1)) (v (i + 2)) :=
      lt_of_le_of_ne h2le (Ne.symm hd2case)
    have hbann : v (i + 2) ∈ ballAnnulus := WL_IN_BALL_ANNULUS_p28 s v (i + 2) hBB
    rw [ballAnnulus, Set.mem_diff, Metric.mem_closedBall, Metric.mem_ball,
      dist_eq_norm, sub_zero] at hbann
    obtain ⟨hup, hlo⟩ := hbann
    have hnl : 2 ≤ ‖v (i + 2)‖ := le_of_not_gt hlo
    have haz1 : azim 0 (v (i + 1)) (v (i + 2)) (v i) ≤ Real.pi := by
      have h := IN_V_IMP_AZIM_LESS_PI hconv2 (v (i + 1)) (Set.mem_range.mpr ⟨i + 1, rfl⟩)
        (v i) (Set.mem_range.mpr ⟨i, rfl⟩)
      rwa [hrho2 (i + 1), show i + 1 + 1 = i + 2 from rfl] at h
    rcases le_iff_eq_or_lt.mp haz1 with heq1 | hlt1
    · -- Branch `azim (w1) = pi`: the `NUXCOEAv2_p28` route (HOL :269-321).
      rcases CIZMRRH hlf3 with hgen3 | hcirc3 | hlun3
      · -- generic fan: `NUXCOEAv2` at `l := i+1`, `j := i`.
        have hg2 : generic_p2 V E := hgen3.1
        have hlunar1 : ∀ (V2 : Set V3) (E2 : Set (Set V3)) (v1 : V3),
            V2 = Set.range v →
              E2 = Set.range (fun j => ({v j, v (j + 1)} : Set V3)) →
                ¬ Lunar v1 (v (i + 1)) V2 E2 := by
          intro V2 E2 v1 hV2 hE2 hl
          apply hgen3.2
          refine Or.inr ⟨v1, v (i + 1), ?_⟩
          have hl' : Lunar v1 (v (i + 1)) V E := by rwa [hV2, hE2] at hl
          simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hl'
        have hneA : v (i + 2) ≠ v (i + 1 + (s.k - 1)) := by
          rw [show i + 1 + (s.k - 1) = i + s.k from by omega, hper i]
          exact (tfitskcv1_ne_of_diag s v hs hBB (SCS_DIAG_2_p27 s.k i hk3)).symm
        have hneB : v (i + 1) ≠ v (i + 2) := by
          intro he
          have hmod : (i + 1) % s.k = (i + 2) % s.k := hmodv (i + 1) (i + 2) he
          exact succ_mod_ne_p27 h1k hmod
        have hneC : v (i + 1) ≠ v (i + 1 + (s.k - 1)) := by
          rw [show i + 1 + (s.k - 1) = i + s.k from by omega, hper i]
          intro he
          have hmod : (i + 1) % s.k = i % s.k := hmodv (i + 1) i he
          exact succ_mod_ne_p27 h1k hmod.symm
        have haz1f : azim 0 (v (i + 1)) (v (i + 1 + 1)) (v (i + 1 + (s.k - 1)))
            = Real.pi := by
          rw [show i + 1 + (s.k - 1) = i + s.k from by omega, hper i,
            show i + 1 + 1 = i + 2 from rfl]
          exact heq1
        obtain ⟨hnc1, haff1⟩ :=
          tfitskcv1_geo s v s.k rfl hk3 hs hBB hg2 hlf2 (i + 1) haz1f hneA hneB hneC
        have haj1 : s.a i (i + 1) = dist (v i) (v (i + 1)) := by
          rw [hd01]
          exact hai
        have hP1 := NUXCOEAv2_p28 s s.k v (i + 1) i rfl hk3 hs hMMs haz1f hnc1 haff1
          (Or.inr rfl) haj1 hdb0
          (fun m hd => (hadiag (i + 1) m hd).2.2)
          (fun m hd => SCS_DIAG_A_LE_DIST_p27 s v hadiag (i + 1) m hd)
          hJ1 hlunar1
        have hd2' : dist (v (i + 1)) (v (i + 2)) = 2 := by
          have h1 := hP1.1
          rw [show i + 1 + 1 = i + 2 from rfl] at h1
          rw [← h1]
          exact ha12
        exact hd2'
      · exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
      · exact (tfitskcv1_lunar_false s v hs hMMs hk3 hBB hper hgen0 hclf hid hlun3).elim
    · -- Branch `azim (w1) < pi`.
      have hang1 : interiorAngle1 0 FF (v (i + 1)) < Real.pi := by
        rw [hid (i + 1), show i + 1 + 1 = i + 2 from rfl,
          show i + 1 + (s.k - 1) = i + s.k from by omega, hper i]
        exact hlt1
      rcases eq_or_lt_of_le hnl with heqn | hgtn
      · -- `norm (v (i+2)) = 2`: `SYNQIWN` feeds `CUXVZOZ`'s left case.
        have h2h0 : (2 : ℝ) ≤ 2 * h0 := by unfold h0; norm_num
        have hsyn : Real.pi / 2 < azim 0 (v (i + 1)) (v (i + 2)) (v i) := by
          have hsp := SYNQIWN_p22 hmnl s v (i + 1) s.k hs hBB rfl hk3
            (Or.inl ⟨by rw [show i + 1 + 1 = i + 2 from rfl]; exact heqn.symm,
              by rw [show i + 1 + s.k - 1 = i + s.k from by omega, hper i, dist_comm,
                hd01]⟩)
            (le_trans (hBB.2.2.1 (i + 1) (i + 2)).2 hb12)
            (by
              rw [show i + 1 + s.k - 1 = i + s.k from by omega, hper i, dist_comm, hd01]
              exact h2h0)
            (by
              rw [show i + 1 + 1 = i + 2 from rfl,
                show i + 1 + s.k - 1 = i + s.k from by omega, hper i, dist_comm]
              exact le_of_lt (hadiag i (i + 2) (SCS_DIAG_2_p27 s.k i hk3)).2.1)
          rwa [show i + 1 + 1 = i + 2 from rfl,
            show i + 1 + s.k - 1 = i + s.k from by omega, hper i] at hsp
        have hsynw : Real.pi / 2 < interiorAngle1 0 FF (v (i + 1)) := by
          rw [hid (i + 1), show i + 1 + 1 = i + 2 from rfl,
            show i + 1 + (s.k - 1) = i + s.k from by omega, hper i]
          exact hsyn
        exact tfitskcv1_cuxvzoz s v i hmnl FF hFFdef hs hk3 hMMs hbasic hgen hBB
          ha12 hb12 hd01 hadiag hper hang1 (Or.inl hsynw)
      · -- `2 < norm (v (i+2))`: split on `azim (w2)`.
        have hgtn' : ‖v (i + 2)‖ ≠ 2 := ne_of_gt hgtn
        have haz2 : azim 0 (v (i + 2)) (v (i + 3)) (v (i + 1)) ≤ Real.pi := by
          have h := IN_V_IMP_AZIM_LESS_PI hconv2 (v (i + 2)) (Set.mem_range.mpr ⟨i + 2, rfl⟩)
            (v (i + 1)) (Set.mem_range.mpr ⟨i + 1, rfl⟩)
          rwa [hrho2 (i + 2), show i + 2 + 1 = i + 3 from rfl] at h
        rcases le_iff_eq_or_lt.mp haz2 with heq2 | hlt2
        · -- Branch `azim (w2) = pi`: `NUXCOEAv2_p28` / `IMJXPHRv2_p28` at
          -- `l := i+2` (HOL :527-546, VASYYAU-style pin dichotomy).
          rcases CIZMRRH hlf3 with hgen3 | hcirc3 | hlun3
          · have hg2 : generic_p2 V E := hgen3.1
            have hlunar2 : ∀ (V2 : Set V3) (E2 : Set (Set V3)) (v1 : V3),
                V2 = Set.range v →
                  E2 = Set.range (fun j => ({v j, v (j + 1)} : Set V3)) →
                    ¬ Lunar v1 (v (i + 2)) V2 E2 := by
              intro V2 E2 v1 hV2 hE2 hl
              apply hgen3.2
              refine Or.inr ⟨v1, v (i + 2), ?_⟩
              have hl' : Lunar v1 (v (i + 2)) V E := by rwa [hV2, hE2] at hl
              simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hl'
            have hneA2 : v (i + 3) ≠ v (i + 2 + (s.k - 1)) := by
              rw [show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1)]
              exact (tfitskcv1_ne_of_diag s v hs hBB (SCS_DIAG_2_p27 s.k (i + 1) hk3)).symm
            have hneB2 : v (i + 2) ≠ v (i + 3) := by
              intro he
              have hmod : (i + 2) % s.k = (i + 3) % s.k := hmodv (i + 2) (i + 3) he
              exact succ_mod_ne_p27 h1k hmod
            have hneC2 : v (i + 2) ≠ v (i + 2 + (s.k - 1)) := by
              rw [show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1)]
              intro he
              have hmod : (i + 2) % s.k = (i + 1) % s.k := hmodv (i + 2) (i + 1) he
              exact (succ_mod_ne_p27 h1k (i := i + 1)).symm hmod
            have haz2f : azim 0 (v (i + 2)) (v (i + 2 + 1)) (v (i + 2 + (s.k - 1)))
                = Real.pi := by
              rw [show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1),
                show i + 2 + 1 = i + 3 from rfl]
              exact heq2
            obtain ⟨hnc2, haff2⟩ :=
              tfitskcv1_geo s v s.k rfl hk3 hs hBB hg2 hlf2 (i + 2) haz2f hneA2 hneB2 hneC2
            have hfold : s.a (i + 2) (i + 1 + s.k) = s.a (i + 2) (i + 1) := by
              rw [periodic2_mod_p27 hpa (i + 2) (i + 1 + s.k),
                periodic2_mod_p27 hpa (i + 2) (i + 1), Nat.add_mod_right]
            have h23le : s.a (i + 2) (i + 3) ≤ dist (v (i + 2)) (v (i + 3)) :=
              (hBB.2.2.1 (i + 2) (i + 3)).1
            rcases eq_or_lt_of_le h23le with ha23 | ha23
            · -- the `(i+2, i+3)` edge is pinned: `NUXCOEAv2` at `j := i+3`.
              have haj2 : s.a (i + 3) (i + 2) = dist (v (i + 3)) (v (i + 2)) := by
                rw [(hsym (i + 3) (i + 2)).1, dist_comm]
                exact ha23
              have hbj2 : dist (v (i + 3)) (v (i + 2)) < s.b (i + 3) (i + 2) := by
                rw [← haj2, (hsym (i + 3) (i + 2)).1, ← (hsym (i + 2) (i + 3)).2.2.2.1]
                exact hab23
              have hP2 := NUXCOEAv2_p28 s s.k v (i + 2) (i + 3) rfl hk3 hs hMMs haz2f
                hnc2 haff2 (Or.inl rfl) haj2 hbj2
                (fun m hd => (hadiag (i + 2) m hd).2.2)
                (fun m hd => SCS_DIAG_A_LE_DIST_p27 s v hadiag (i + 2) m hd)
                hJ2 hlunar2
              have hQ2 := hP2.2
              rw [show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1)] at hQ2
              rw [hfold, (hsym (i + 2) (i + 1)).1] at hQ2
              have hdq : dist (v (i + 2)) (v (i + 1)) = 2 := by
                rw [← hQ2]
                exact ha12
              rw [← hdq]
              exact dist_comm _ _
            · -- the `(i+2, i+3)` edge is slack: `IMJXPHRv2` (`norm != 2`).
              have hP3 := IMJXPHRv2_p28 s s.k v (i + 2) rfl hs hMMs haz2f hk3 hnc2 haff2
                (fun m hd => (hadiag (i + 2) m hd).2.2)
                hgtn'
                (fun m hd => SCS_DIAG_A_LE_DIST_p27 s v hadiag (i + 2) m hd)
                hJ2 hlunar2
              have hQ3 := hP3.2
              rw [show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1)] at hQ3
              rw [hfold, (hsym (i + 2) (i + 1)).1] at hQ3
              have hdq3 : dist (v (i + 2)) (v (i + 1)) = 2 := by
                rw [← hQ3]
                exact ha12
              rw [← hdq3]
              exact dist_comm _ _
          · exact absurd (by simpa only [circular_p3, Circular] using hcirc3.1) hcirc
          · exact (tfitskcv1_lunar_false s v hs hMMs hk3 hBB hper hgen0 hclf hid hlun3).elim
        · -- Branch `azim (w2) < pi`: `CUXVZOZ`'s right case (HOL :550-564 via
          -- the mirrored `CJBDXXN`, which `tfitskcv1_cuxvzoz` subsumes).
          have hang2 : interiorAngle1 0 FF (v (i + 2)) < Real.pi := by
            rw [hid (i + 2), show i + 2 + 1 = i + 3 from rfl,
              show i + 2 + (s.k - 1) = i + 1 + s.k from by omega, hper (i + 1)]
            exact hlt2
          exact tfitskcv1_cuxvzoz s v i hmnl FF hFFdef hs hk3 hMMs hbasic hgen hBB
            ha12 hb12 hd01 hadiag hper hang1 (Or.inr hang2)
  -- DISCHARGES (2026-11-12, lane tfitskcv1-w1): HOL TFITSKC.hl:144-631 via
  -- the dagcut/g482-unlocked closers — `NUXCOEAv2_p28` (flat node `i+1`),
  -- `CUXVZOZ_p21` (azim `< pi` at `i+1`, two hcase feeds), and
  -- `IMJXPHRv2_p28`/`NUXCOEAv2_p28` at the flat node `i+2` under the
  -- `norm (v (i+2)) = 2 / > 2` split; the `CIZMRRH` circular fork is killed
  -- by `JKQEWGV2_p23` and the lunar fork by the JCYFMRP coplanarity engine
  -- (`HKIRPEP_ALT_p37` + `jcyfmrp_flat_residues_coplanar` + `FEKTYIY_p27`).
  -- Zero new sorries; axioms face = standard three.

/-- HOL `TFITSKC_concl` (TFITSKC.hl:636). Note the registry twin
`TFITSKC_concl` (LocalAuto1) strengthens `s.b (i+1)(i+2) ≤ 2*h0` to `=`; this
statement follows the source (`≤`). -/
-- Placement (lane tfitskc-w1, 2026-11-13): declared after `TFITSKCv1_p27` for
-- Lean's declaration order (HOL proves `TFITSKC` by `MP_TAC TFITSKCv1`,
-- TFITSKC.hl:649-659); docstring + statement byte-identical to the skeleton.
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
  intro hmnl s v i hab23 hk3 hs hMMs hgen hbasic ha12 hb12 hd01 hb0gt hadiag
  have hJ2 : ∀ i', ¬ s.J (i + 2) i' := fun i' hJ => (hbasic.2 (i + 2) i') ▸ hJ
  have hdb0 : dist (v i) (v (i + 1)) < s.b i (i + 1) := by
    rw [hd01]; exact hb0gt
  exact TFITSKCv1_p27 hmnl s v i hJ2 hab23 hk3 hs hMMs hgen hbasic ha12 hb12
    hd01 hdb0 hadiag
  -- DISCHARGES (2026-11-13, lane tfitskc-w1): HOL TFITSKC.hl:649-659 — the
  -- 13-line wrapper on `TFITSKCv1_p27`.  The J-emptyness premise is discharged
  -- from `scsBasicV39` (`s.J i j = False`, the HOL `scs_basic` unfolding at
  -- TFITSKC.hl:655-656), and the strict bound `dist (v i) (v (i+1)) < b i (i+1)`
  -- is `hb0gt` with `hd01` rewrote.

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

/-! ## Section JLXFDMJ (lane jlxfdmj-w4, 2026-11-13): opposite-system kit + the
`3 < s.k` main propagation lemma

  Private ports of the HOL `JLXFDMJ` proof (`scripts/local/JLXFDMJ.hl:227-818`):
  the opposite-system kit (`scsOppV39` SCS + generic/basic transports), the
  backward propagation step `jlx_bwd_step` (HOL `CQAOQLR` opposite route), the
  modular-distance arithmetic (`jlx_fwd_dist_spec`/`jlx_bwd_dist_spec` +
  uniqueness/complement), and the main lemma `jlxfdmj_ge4` = HOL `JLXFDMJ`
  restricted to `3 < scs_k_v39 s` (the HOL statement's first hypothesis; the
  registry summary `appendix.hl` dropped it — SF draft in the lane delivery).
  `JLXFDMJ_p27` itself keeps its unfilled proof pending that SF decision
  (k = 3 case); its axiom face is unchanged.
-/

/-! ### jlxfdmj-w2: opposite-system kit (private ports; every source proved) -/

-- ——— swbopp kit: verbatim from LocalAuto24 `swbopp_*` (private, LA24:1191-1300) ———

/-- Residue `φ x = k - (x % k + 1)` is below `k` for `1 ≤ k`. (LA24 `swbopp_phi_lt`.) -/
private theorem jlxswb_phi_lt {k : ℕ} (hk : 1 ≤ k) (x : ℕ) :
    k - (x % k + 1) < k := by
  have h : x % k < k := Nat.mod_lt x (by omega)
  omega

/-- Equal residues below `k` give equal indices. (LA24 `swbopp_mod_eq`.) -/
private theorem jlxswb_mod_eq {k p q : ℕ} (h : p % k = q % k) (hp : p < k)
    (hq : q < k) : p = q := by
  have h1 : p % k = p := Nat.mod_eq_of_lt hp
  have h2 : q % k = q := Nat.mod_eq_of_lt hq
  omega

/-- HOL `OPP_SUC_MOD`: `φ` is an involution on residues. (LA24 `swbopp_phi_inv`.) -/
private theorem jlxswb_phi_inv {k : ℕ} (hk : k ≠ 0) (x : ℕ) :
    k - ((k - (x % k + 1)) % k + 1) = x % k := by
  have hlt : x % k < k := Nat.mod_lt x (by omega)
  have h1 : (k - (x % k + 1)) % k = k - (x % k + 1) :=
    Nat.mod_eq_of_lt (by have := hlt; omega)
  rw [h1]
  omega

/-- The `φ`-pair `(φ i, φ (i + 1))` is a reversed adjacent pair modulo `k`.
(LA24 `swbopp_pair_adj`.) -/
private theorem jlxswb_pair_adj {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    k - (i % k + 1) = (k - ((i + 1) % k + 1) + 1) % k := by
  have hi : i % k < k := Nat.mod_lt i (by omega)
  by_cases hlt : i % k + 1 < k
  · have hw1 : (i + 1) % k = i % k + 1 := by
      rw [← Nat.mod_add_mod i k 1]
      exact Nat.mod_eq_of_lt hlt
    rw [hw1]
    have hR : k - (i % k + 1 + 1) + 1 < k := by have := hi; omega
    rw [Nat.mod_eq_of_lt hR]
    omega
  · have heq : i % k + 1 = k := by omega
    have hw1 : (i + 1) % k = 0 := by
      rw [← Nat.mod_add_mod i k 1, heq, Nat.mod_self]
    rw [hw1, heq, Nat.sub_self]
    have hR : k - (0 + 1 : ℕ) + 1 = k := by omega
    rw [hR, Nat.mod_self]

/-- Orientation swap for the `φ`-pair (LA24 `swbopp_adj_swap`). -/
private theorem jlxswb_adj_swap {k : ℕ} (hk : 1 ≤ k) {x y : ℕ}
    (h : (k - (y % k + 1)) % k = (k - (x % k + 1) + 1) % k) :
    x % k = (y + 1) % k := by
  have hx : x % k < k := Nat.mod_lt x (by omega)
  have hy : y % k < k := Nat.mod_lt y (by omega)
  have hmod : (k - (y % k + 1)) % k = k - (y % k + 1) :=
    Nat.mod_eq_of_lt (by have := hy; omega)
  rw [hmod] at h
  have hrhs : (k - (x % k + 1) + 1) % k = (k - x % k) % k := by
    have hsh : k - (x % k + 1) + 1 = k - x % k := by have := hx; omega
    rw [hsh]
  rw [hrhs] at h
  rw [(Nat.mod_add_mod y k 1).symm]
  by_cases hx0 : x % k = 0
  · have h2 : (k - x % k) % k = 0 := by rw [hx0, Nat.sub_zero, Nat.mod_self]
    rw [h2] at h
    have hyk : y % k + 1 = k := by have := h; have := hy; omega
    rw [hx0, hyk, Nat.mod_self]
  · have h2 : (k - x % k) % k = k - x % k :=
      Nat.mod_eq_of_lt (by have := hx; omega)
    rw [h2] at h
    have hxy : y % k + 1 = x % k := by
      have h3 := h; have := hy; have := hx; omega
    rw [hxy]
    exact (Nat.mod_modEq x k).symm

/-- Adjacent-pair value transport (LA24 `swbopp_b_adj`). -/
private theorem jlxswb_b_adj {k : ℕ} {b : ℕ → ℕ → ℝ}
    (hk : 1 ≤ k) (hper : Periodic2 b k) (hsymg : ∀ i j, b i j = b j i)
    {x y : ℕ} (h : x % k = (y + 1) % k) :
    b x y = b (y % k) (y % k + 1) := by
  have hk0 : k ≠ 0 := by omega
  have hylt : y % k < k := Nat.mod_lt y (by omega)
  have hyk : (y + 1) % k = (y % k + 1) % k := (Nat.mod_add_mod y k 1).symm
  rw [hyk] at h
  have hred : b (x % k) (y % k) = b x y :=
    (periodic2Mod1 hk0 hper x (y % k)).trans (periodic2Mod2 hk0 hper x y)
  rw [← hred]
  by_cases hlt : y % k + 1 < k
  · have hxk : x % k = y % k + 1 := by rw [h, Nat.mod_eq_of_lt hlt]
    rw [hxk, hsymg (y % k + 1) (y % k)]
  · have heq : y % k + 1 = k := by omega
    have hxk : x % k = 0 := by rw [h, heq, Nat.mod_self]
    rw [hxk, hsymg 0 (y % k)]
    exact (hper (y % k) 0).2.symm.trans
      (congrArg (b (y % k)) (show (0 : ℕ) + k = y % k + 1 from by rw [Nat.zero_add, heq]))

/-- Pointwise key (LA24 `swbopp_key`). -/
private theorem jlxswb_key {k : ℕ} {g : ℕ → ℕ → ℝ}
    (hk : 1 ≤ k) (hper : Periodic2 g k) (hsymg : ∀ i j, g i j = g j i) (i : ℕ) :
    g (k - (i % k + 1)) (k - ((i + 1) % k + 1))
      = g (k - 1 - ((i + 1) % k)) (k - 1 - ((i + 1) % k) + 1) := by
  have htr := jlxswb_b_adj (b := g) hk hper hsymg
    (x := k - (i % k + 1)) (y := k - ((i + 1) % k + 1))
    (by rw [Nat.mod_eq_of_lt (jlxswb_phi_lt hk i)]; exact jlxswb_pair_adj hk i)
  rw [htr, Nat.mod_eq_of_lt (jlxswb_phi_lt hk (i + 1))]
  rw [show k - ((i + 1) % k + 1) = k - 1 - ((i + 1) % k) from by
    have hw : (i + 1) % k < k := Nat.mod_lt (i + 1) (by omega)
    omega]

/-- HOL `OPP_IS_SCS` (verbatim from LA24 `swb_opp_isscs_p24`, private). -/
private theorem jlx_opp_isscs (s : ScsV39) (hs : isScsV39 s) : isScsV39 (scsOppV39 s) := by
  obtain ⟨hd, h3, hk6, hlo, hhi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym5, hch, hdiag0,
    hdiag, hb3, hbc, hjn, hjab, hcard⟩ := hs
  have hk3' : 3 ≤ s.k := h3
  have hk6' : s.k ≤ 6 := hk6
  have hpa' : Periodic2 s.a s.k := hpa
  have hpb' : Periodic2 s.b s.k := hpb
  have hsymA : ∀ i j, s.a i j = s.a j i := fun i j => (hsym5 i j).1
  have hsymB : ∀ i j, s.b i j = s.b j i := fun i j => (hsym5 i j).2.2.2.1
  have hjn' : ∀ i j, s.J i j → j % s.k = (i + 1) % s.k ∨ i % s.k = (j + 1) % s.k := hjn
  have hjab' : ∀ i j, s.J i j → s.a i j = Real.sqrt 8 ∧ s.b i j = cstab := hjab
  have hcard' : {i | i < s.k ∧ (2 * h0 < s.b i (i + 1) ∨ 2 < s.a i (i + 1))}.ncard + s.k ≤ 6 := hcard
  have hk0 : s.k ≠ 0 := by omega
  have hmodlt : ∀ i : ℕ, i % s.k < s.k := fun i => Nat.mod_lt i (by omega)
  have hlt : ∀ i, s.k - (i % s.k + 1) < s.k := by
    intro i
    have := hmodlt i
    omega
  have hflipinj : ∀ i j, i < s.k → j < s.k → s.k - (i % s.k + 1) = s.k - (j % s.k + 1) → i = j := by
    intro i j hi hj hc
    have h4 : i % s.k = j % s.k := by
      have h2 := hmodlt i
      have h3 := hmodlt j
      omega
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h4
    exact h4
  have key : ∀ y x : ℕ, y < s.k → x < s.k → s.k - (x + 1) = (s.k - y) % s.k → y = (x + 1) % s.k := by
    intro y x hy hx hc
    have hs : (x + 1) % s.k = (x % s.k + 1) % s.k :=
      Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq x s.k))
    rw [hs, Nat.mod_eq_of_lt hx]
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      rw [Nat.sub_zero, Nat.mod_self] at hc
      have hxy : x + 1 = s.k := by omega
      rw [hxy, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)] at hc
      have hxy : x + 1 = y := by omega
      rw [hxy, Nat.mod_eq_of_lt hy]
  show isScsV39 (ScsV39.mk s.k s.d (peropp2 s.a s.k) (peropp2 s.am s.k) (peropp2 s.bm s.k)
    (peropp2 s.b s.k) (peropp2 s.J s.k) (peropp s.lo s.k) (peropp s.hi s.k)
    (peropp s.str s.k))
  refine ⟨hd, hk3', hk6', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact peropp_periodic s.lo s.k
  · exact peropp_periodic s.hi s.k
  · exact peropp_periodic s.str s.k
  · exact peropp_periodic s.str s.k
  · intro p q
    show s.a (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.a (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.am (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.am (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.am (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.am (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.bm (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.bm (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.bm (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.bm (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.b (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1))
        = s.b (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.b (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1))
        = s.b (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    show s.J (s.k - ((p + s.k) % s.k + 1)) (s.k - (q % s.k + 1)) =
        s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) ∧
      s.J (s.k - (p % s.k + 1)) (s.k - ((q + s.k) % s.k + 1)) =
        s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    rw [Nat.add_mod_right, Nat.add_mod_right]
    exact ⟨rfl, rfl⟩
  · intro p q
    exact ⟨(hsym5 (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).1,
      (hsym5 (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.1,
      (hsym5 (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.1,
      (hsym5 (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.2.1,
      (hsym5 (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))).2.2.2.2⟩
  · intro p q
    exact hch (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
  · intro p
    exact hdiag0 (s.k - (p % s.k + 1))
  · intro p q hpq
    have hne : s.k - (p % s.k + 1) ≠ s.k - (q % s.k + 1) := by
      intro hcon
      have e1 : s.k - ((s.k - (p % s.k + 1)) % s.k + 1) = p % s.k := jlxswb_phi_inv hk0 p
      have e2 : s.k - ((s.k - (q % s.k + 1)) % s.k + 1) = q % s.k := jlxswb_phi_inv hk0 q
      rw [Nat.mod_eq_of_lt (jlxswb_phi_lt (by omega) p)] at e1
      rw [Nat.mod_eq_of_lt (jlxswb_phi_lt (by omega) q)] at e2
      exact hpq.2.2 (jlxswb_mod_eq (k := s.k) (by rw [← e1, ← e2, hcon]) hpq.1 hpq.2.1)
    show 2 ≤ s.a (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1))
    exact hdiag _ _ ⟨jlxswb_phi_lt (by omega) p, jlxswb_phi_lt (by omega) q, hne⟩
  · intro p hp3
    show s.b (s.k - (p % s.k + 1)) (s.k - ((p + 1) % s.k + 1)) < 4
    rw [jlxswb_key (by omega) hpb hsymB p]
    exact hb3 _ hp3
  · intro p hp6
    show s.b (s.k - (p % s.k + 1)) (s.k - ((p + 1) % s.k + 1)) ≤ cstab
    rw [jlxswb_key (by omega) hpb hsymB p]
    exact hbc _ hp6
  · intro p q hpq
    show q % s.k = (p + 1) % s.k ∨ p % s.k = (q + 1) % s.k
    have hJs : s.J (s.k - (p % s.k + 1)) (s.k - (q % s.k + 1)) := hpq
    rcases hjn' _ _ hJs with h | h
    · exact Or.inr (jlxswb_adj_swap (by omega) h)
    · exact Or.inl (jlxswb_adj_swap (by omega) h)
  · intro p q hpq
    exact hjab' _ _ hpq
  · show {i | i < s.k ∧ (2 * h0 < s.b (s.k - (i % s.k + 1))
        (s.k - ((i + 1) % s.k + 1)) ∨
        2 < s.a (s.k - (i % s.k + 1)) (s.k - ((i + 1) % s.k + 1)))}.ncard + s.k ≤ 6
    have hcardT : {i | i < s.k ∧ (2 * h0 < s.b (s.k - (i % s.k + 1))
          (s.k - ((i + 1) % s.k + 1)) ∨
        2 < s.a (s.k - (i % s.k + 1)) (s.k - ((i + 1) % s.k + 1)))}.ncard
        = {j | j < s.k ∧ (2 * h0 < s.b j (j + 1) ∨ 2 < s.a j (j + 1))}.ncard := by
      refine Set.ncard_congr
        (f := fun i (_ : i ∈ (_ : Set ℕ)) => s.k - 1 - ((i + 1) % s.k)) ?_ ?_ ?_
      · rintro i ⟨hi, hbad | hbad⟩
        · have hlt : (i + 1) % s.k < s.k := Nat.mod_lt (i + 1) (by omega)
          refine ⟨by omega, ?_⟩
          rw [jlxswb_key (by omega) hpb hsymB i] at hbad
          exact Or.inl hbad
        · have hlt : (i + 1) % s.k < s.k := Nat.mod_lt (i + 1) (by omega)
          refine ⟨by omega, ?_⟩
          rw [jlxswb_key (by omega) hpa hsymA i] at hbad
          exact Or.inr hbad
      · rintro i j hi hb hcon
        obtain ⟨hi, -⟩ := hi
        obtain ⟨hj, -⟩ := hb
        have hcon' : s.k - 1 - ((i + 1) % s.k) = s.k - 1 - ((j + 1) % s.k) := hcon
        by_cases hik : i + 1 < s.k
        · by_cases hjk : j + 1 < s.k
          · have e1 : (i + 1) % s.k = i + 1 := Nat.mod_eq_of_lt hik
            have e2 : (j + 1) % s.k = j + 1 := Nat.mod_eq_of_lt hjk
            rw [e1, e2] at hcon'
            omega
          · have e1 : (i + 1) % s.k = i + 1 := Nat.mod_eq_of_lt hik
            have hjk1 : j + 1 = s.k := by omega
            have e2 : (j + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            rw [e1, e2] at hcon'
            omega
        · by_cases hjk : j + 1 < s.k
          · have hjk1 : i + 1 = s.k := by omega
            have e1 : (i + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            have e2 : (j + 1) % s.k = j + 1 := Nat.mod_eq_of_lt hjk
            rw [e1, e2] at hcon'
            omega
          · have hik1 : i + 1 = s.k := by omega
            have hjk1 : j + 1 = s.k := by omega
            have e1 : (i + 1) % s.k = 0 := by rw [hik1, Nat.mod_self]
            have e2 : (j + 1) % s.k = 0 := by rw [hjk1, Nat.mod_self]
            rw [e1, e2] at hcon'
            omega
      · rintro j ⟨hj, hbad⟩
        set i := (2 * s.k - 2 - j) % s.k with hiv
        have hi : i < s.k := by rw [hiv]; exact Nat.mod_lt _ (by omega)
        have hi1 : (i + 1) % s.k = (2 * s.k - 1 - j) % s.k := by
          rw [hiv, Nat.mod_add_mod (2 * s.k - 2 - j) s.k 1,
            show 2 * s.k - 2 - j + 1 = 2 * s.k - 1 - j from by omega]
        have hfi : s.k - 1 - ((i + 1) % s.k) = j := by
          rw [hi1]
          by_cases hjk1 : j = s.k - 1
          · rw [hjk1, show 2 * s.k - 1 - (s.k - 1) = s.k from by omega, Nat.mod_self]
            omega
          · have hmod : (2 * s.k - 1 - j) % s.k = s.k - 1 - j := by
              have hj2 : j ≤ s.k - 2 := by omega
              rw [show 2 * s.k - 1 - j = s.k + (s.k - 1 - j) from by omega,
                Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_modEq _ _,
                Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
            omega
        refine ⟨i, ⟨hi, ?_⟩, hfi⟩
        rw [jlxswb_key (by omega) hpb hsymB i, jlxswb_key (by omega) hpa hsymA i, hfi]
        exact hbad
    rw [hcardT]
    exact hcard'

-- ——— SYM_0 kit: verbatim from LocalAuto16 (private, LA16:1295-1512) ———

/-- HOL `ELEMENT1_SYM_0`. (LA16 `ELEMENT1_SYM_0_p16`.) -/
private theorem jlx_element1_sym (a : V3) :
    ({-a} : Set V3) = (fun x : V3 => -x) '' {a} := by
  simp

/-- The negation map on `V3` is injective. (LA16 `negInjSym_p16`.) -/
private theorem jlx_neg_inj_sym : Function.Injective (fun x : V3 => -x) :=
  fun _ _ h => by simpa using h

/-- HOL `ELEMENT2_SYM_0`. (LA16 `element2Neg_p16`.) -/
private theorem jlx_element2_neg (a b : V3) :
    ({-a, -b} : Set V3) = Set.image (fun x : V3 => -x) ({a, b} : Set V3) := by
  rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL `REFL_SYM_0`. (LA16 `reflNeg_p16`.) -/
private theorem jlx_refl_neg (A : Set V3) :
    Set.image (fun x : V3 => -x) (Set.image (fun x : V3 => -x) A) = A := by
  simp

/-- HOL `INTER_SYM_0`. (LA16 `interNeg_p16`.) -/
private theorem jlx_inter_neg (e1 e2 : Set V3) :
    Set.image (fun x : V3 => -x) (e1 ∩ e2)
      = Set.image (fun x : V3 => -x) e1 ∩ Set.image (fun x : V3 => -x) e2 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨⟨y, hy1, rfl⟩, ⟨y, hy2, rfl⟩⟩
  · rintro ⟨⟨y1, hy1, rfl⟩, ⟨y2, hy2, hy12⟩⟩
    have hyy : y1 = y2 := neg_inj.mp hy12.symm
    exact ⟨y1, ⟨hy1, hyy ▸ hy2⟩, rfl⟩

/-- HOL `VEC0_SYM_0`. (LA16 `vec0Neg_p16`.) -/
private theorem jlx_vec0_neg :
    Set.image (fun x : V3 => -x) ({0} : Set V3) = ({0} : Set V3) := by
  ext x
  simp

/-- HOL `AFF_GE_VEC0_SYM_0` / `AFF_LT_VEC0_SYM_0`, sign-generic core.
(LA16 `affsignNegPt_p16`.) -/
private theorem jlx_affsign_neg {e : Set V3} {w : V3} {sgn : ℝ → Prop}
    (hw : Affsign sgn ({0} : Set V3) (Set.image (fun x : V3 => -x) e) w) :
    Affsign sgn ({0} : Set V3) e (-w) := by
  obtain ⟨f, hfin, hwv, hfp, hfsum⟩ := hw
  have hU : Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
      = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e := by
    rw [Set.image_union, jlx_vec0_neg]
  have hfinA : ((({0} : Set V3) ∪ e : Set V3)).Finite :=
    (Set.finite_image_iff jlx_neg_inj_sym.injOn).mp (by rw [hU]; exact hfin)
  have heq : hfin.toFinset = hfinA.toFinset.image (fun x : V3 => -x) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_image,
      Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨0, Or.inl rfl, by simp⟩
      · exact ⟨y, Or.inr hy, rfl⟩
    · rintro ⟨a, (rfl | hy), rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inr ⟨a, hy, rfl⟩
  refine ⟨fun y => f (-y), hfinA, ?_, ?_, ?_⟩
  · calc -w = ∑ x ∈ hfin.toFinset, f x • (-x) := by
          rw [hwv]
          simp only [Finset.sum_neg_distrib, smul_neg]
      _ = ∑ x ∈ hfinA.toFinset.image (fun x : V3 => -x), f x • (-x) := by rw [heq]
      _ = ∑ y ∈ hfinA.toFinset, f (-y) • y := by
          simp only [Finset.sum_image (f := fun z : V3 => f z • (-z))
            (g := fun x : V3 => -x) jlx_neg_inj_sym.injOn, neg_neg]
  · intro z hz
    exact hfp (-z) ⟨z, hz, rfl⟩
  · show (∑ y ∈ hfinA.toFinset, f (-y)) = 1
    rw [← Finset.sum_image (f := f) (g := fun x : V3 => -x) jlx_neg_inj_sym.injOn, ← heq]
    exact hfsum

/-- HOL `AFF_GE_VEC0_SYM_0`. (LA16 `affGeNeg_p16`.) -/
private theorem jlx_affGe_neg (e : Set V3) :
    affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affGe ({0} : Set V3) e) := by
  ext v
  constructor
  · intro hv
    have hv' : Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3)
        (Set.image (fun x : V3 => -x) e) v := hv
    refine ⟨-v, ?_, by simp⟩
    show Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3) e (-v)
    exact jlx_affsign_neg (sgn := fun x : ℝ => 0 ≤ x) hv'
  · rintro ⟨u, hu, rfl⟩
    show Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3)
      (Set.image (fun x : V3 => -x) e) (-u)
    refine jlx_affsign_neg (sgn := fun x : ℝ => 0 ≤ x)
      (e := Set.image (fun x : V3 => -x) e) ?_
    rw [jlx_refl_neg e]
    exact hu

/-- HOL `AFF_LT_VEC0_SYM_0`. (LA16 `affLtNeg_p16`.) -/
private theorem jlx_affLt_neg (e : Set V3) :
    affLt ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affLt ({0} : Set V3) e) := by
  ext v
  constructor
  · intro hv
    have hv' : Affsign (fun x : ℝ => x < 0) ({0} : Set V3)
        (Set.image (fun x : V3 => -x) e) v := hv
    refine ⟨-v, ?_, by simp⟩
    show Affsign (fun x : ℝ => x < 0) ({0} : Set V3) e (-v)
    exact jlx_affsign_neg (sgn := fun x : ℝ => x < 0) hv'
  · rintro ⟨u, hu, rfl⟩
    show Affsign (fun x : ℝ => x < 0) ({0} : Set V3)
      (Set.image (fun x : V3 => -x) e) (-u)
    refine jlx_affsign_neg (sgn := fun x : ℝ => x < 0)
      (e := Set.image (fun x : V3 => -x) e) ?_
    rw [jlx_refl_neg e]
    exact hu

/-- A `k`-periodic sequence satisfies `v k = v 0`. (LA16 `periodicZero_p16`.) -/
private theorem jlx_periodic_zero {v : ℕ → V3} {k : ℕ} (hper : Periodic v k) :
    v k = v 0 := by
  have h := hper 0
  rwa [Nat.zero_add] at h

/-- The opposite of an edge is an edge (LA16 `oppEdgeIndex_p16`). -/
private theorem jlx_opp_edge_index {v : ℕ → V3} {k : ℕ} (hk : 1 < k)
    (hper : Periodic v k) (i : ℕ) :
    ∃ j : ℕ, ({v (k - (i % k + 1)), v (k - ((i + 1) % k + 1))} : Set V3)
      = ({v j, v (j + 1)} : Set V3) := by
  have hp : i % k < k := Nat.mod_lt _ (by omega)
  have hq : (i + 1) % k = (i % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hk]
  rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
  · refine ⟨k - (i % k) - 2, ?_⟩
    have hq' : (i + 1) % k = i % k + 1 := by rw [hq, Nat.mod_eq_of_lt hlt]
    have e1 : k - (i % k + 1) = k - (i % k) - 2 + 1 := by omega
    have e2 : k - (i % k + 1 + 1) = k - (i % k) - 2 := by omega
    rw [hq', e1, e2, Set.pair_comm]
  · have hpk : i % k + 1 = k := by omega
    refine ⟨k - 1, ?_⟩
    have hq0 : (i + 1) % k = 0 := by rw [hq, hpk, Nat.mod_self]
    have e1 : k - (i % k + 1) = 0 := by rw [hpk, Nat.sub_self]
    have e2 : k - ((i + 1) % k + 1) = k - 1 := by rw [hq0]
    have hk1 : k - 1 + 1 = k := by omega
    rw [e1, e2, hk1, jlx_periodic_zero hper, Set.pair_comm]

/-- HOL `SCS_GENERIC_SYM_0` (LA16:1464, verbatim body). -/
private theorem jlx_generic_opp (s : ScsV39) (v : ℕ → V3) (h1 : BBsV39 s v)
    (h2 : isScsV39 s) (h3 : scsGeneric v) :
    scsGeneric (fun i => -(v (s.k - (i % s.k + 1)))) := by
  have hper : Periodic v s.k := by
    have h := h1
    unfold BBsV39 at h
    exact h.2.1
  have hk3 : 3 ≤ s.k := by
    have h := h2
    unfold isScsV39 at h
    exact h.2.1
  have hk : 1 < s.k := by omega
  unfold scsGeneric Generic at h3 ⊢
  intro v' w u hmem hu
  obtain ⟨i, hi⟩ := hmem
  obtain ⟨j, hj⟩ := hu
  have hV : -u ∈ Set.range v := by
    refine ⟨s.k - (j % s.k + 1), ?_⟩
    rw [← hj]
    simp
  have hE : ({-v', -w} : Set V3) ∈ Set.range (fun i => ({v i, v (i + 1)} : Set V3)) := by
    have hstep : ({-v', -w} : Set V3)
        = Set.image (fun x : V3 => -x)
            ({-(v (s.k - (i % s.k + 1))), -(v (s.k - ((i + 1) % s.k + 1)))} : Set V3) := by
      rw [jlx_element2_neg, ← hi]
    rw [hstep]
    have hneg : Set.image (fun x : V3 => -x)
        ({-(v (s.k - (i % s.k + 1))), -(v (s.k - ((i + 1) % s.k + 1)))} : Set V3)
        = ({v (s.k - (i % s.k + 1)), v (s.k - ((i + 1) % s.k + 1))} : Set V3) := by
      rw [← jlx_element2_neg (-(v (s.k - (i % s.k + 1))))
        (-(v (s.k - ((i + 1) % s.k + 1))))]
      simp
    rw [hneg]
    obtain ⟨m, hm⟩ := jlx_opp_edge_index hk hper i
    rw [hm]
    exact ⟨m, rfl⟩
  have hgen := h3 (-v') (-w) (-u) hE hV
  have hkey : Set.image (fun x : V3 => -x)
      (affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u}) = ∅ := by
    rw [jlx_inter_neg, ← jlx_affGe_neg {v', w}, ← jlx_affLt_neg {u},
      ← jlx_element2_neg v' w, ← jlx_element1_sym u]
    exact hgen
  calc affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u}
      = Set.image (fun x : V3 => -x)
          (Set.image (fun x : V3 => -x)
            (affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u})) :=
        (jlx_refl_neg _).symm
    _ = Set.image (fun x : V3 => -x) ∅ := by rw [hkey]
    _ = ∅ := by simp

-- ——— small opp facts (LA16 `SUC_OPP_ID_p16` / `A_B_J_SCS_OPP_p16`) ———

/-- HOL `SUC_OPP_ID` (LA16:1281). -/
theorem jlx_suc_opp_id {k i : ℕ} (hk : 1 < k) :
    (k - (i % k + 1) + 1) % k = (k - i % k) % k := by
  have hq : i % k < k := Nat.mod_lt _ (by omega)
  rw [show k - (i % k + 1) + 1 = k - i % k by omega]

/-- HOL `A_B_J_SCS_OPP` (LA16:1289): the `a`/`b`/`J` slots of `scsOppV39`. -/
theorem jlx_a_b_j_opp (s : ScsV39) :
    (∀ i j, (scsOppV39 s).a i j = s.a (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) ∧
    (∀ i j, (scsOppV39 s).b i j = s.b (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) ∧
    (∀ i j, (scsOppV39 s).J i j ↔ s.J (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => Iff.rfl⟩

/-- HOL `DIAG_OPP` (LA16:1547, verbatim body). -/
theorem jlx_diag_opp (k i j : ℕ) (hk : 3 < k) (h : scsDiag k i j) :
    scsDiag k (k - (i % k + 1)) (k - (j % k + 1)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hik : i % k < k := Nat.mod_lt _ (by omega)
  have hjk : j % k < k := Nat.mod_lt _ (by omega)
  have mi : k - (i % k + 1) < k := by omega
  have mj : k - (j % k + 1) < k := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    rw [Nat.mod_eq_of_lt mi, Nat.mod_eq_of_lt mj] at hc
    omega
  · -- ¬((i' + 1) % k = j' % k)
    intro heq
    rcases Nat.eq_zero_or_pos (i % k) with hq | hq
    · have hx : k - (i % k + 1) + 1 = k := by rw [hq]; omega
      rw [hx, Nat.mod_self] at heq
      rw [Nat.mod_eq_of_lt mj] at heq
      have hjk1 : j % k + 1 = k := by omega
      have hj1 : (j + 1) % k = (j % k + 1) % k := (Nat.mod_add_mod j k 1).symm
      rw [hj1, hjk1, Nat.mod_self] at h3
      exact h3 (by rw [hq])
    · have hL : (k - (i % k + 1) + 1) % k = k - i % k := by
        rw [show k - (i % k + 1) + 1 = k - i % k by omega]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hL, Nat.mod_eq_of_lt mj] at heq
      have hjq : i % k = j % k + 1 := by omega
      have hj1 : (j + 1) % k = j % k + 1 := by
        rw [← Nat.mod_add_mod j k 1, Nat.mod_eq_of_lt (by omega)]
      rw [hj1] at h3
      exact h3 hjq
  · -- ¬(i' % k = (j' + 1) % k)
    intro heq
    rw [Nat.mod_eq_of_lt mi,
      show k - (j % k + 1) + 1 = k - j % k by omega] at heq
    rcases Nat.eq_zero_or_pos (j % k) with hqj | hqj
    · rw [hqj, Nat.sub_zero, Nat.mod_self] at heq
      -- heq : k - (i % k + 1) = 0
      have hik1 : i % k + 1 = k := by omega
      have hip1 : (i + 1) % k = 0 := by
        rw [← Nat.mod_add_mod i k 1, hik1, Nat.mod_self]
      rw [hip1] at h2
      exact h2 hqj.symm
    · rw [Nat.mod_eq_of_lt (by omega : k - j % k < k)] at heq
      -- heq : k - (i % k + 1) = k - j % k
      have hjq : j % k = i % k + 1 := by omega
      have hip1 : (i + 1) % k = i % k + 1 := by
        rw [← Nat.mod_add_mod i k 1, Nat.mod_eq_of_lt (by omega : i % k + 1 < k)]
      rw [hip1] at h2
      exact h2 hjq.symm

/-- HOL `BASIC_OPP` (LA16:1540 route): `scsBasicV39` transports to the
opposite system. -/
theorem jlx_basic_opp (s : ScsV39) (h1 : isScsV39 s) (h2 : scsBasicV39 s) :
    scsBasicV39 (scsOppV39 s) := by
  obtain ⟨hu, hJ⟩ := h2
  obtain ⟨hlo, hhi, hstr, ham, hbm⟩ := hu
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · funext i
      simp [scsOppV39, peropp, hlo]
    · funext i
      simp [scsOppV39, peropp, hhi]
    · funext i
      simp [scsOppV39, peropp, hstr]
    · funext i j
      simp [scsOppV39, peropp2, ham]
    · funext i j
      simp [scsOppV39, peropp2, hbm]
  · intro i j
    show s.J (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1)) = False
    exact hJ (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))



/-- Residue fold A: the `(i'+1)`-slot of the opposite re-indexing lands on
`i+1` (`i' = k - (r+1)`, `r = (i+2) % k`). -/
private theorem jlx_fldA {k r : ℕ} (hk : 1 ≤ k) (hr : r < k) :
    (k - ((k - r) % k + 1)) % k = (r + k - 1) % k := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self]
    have e1 : k - (0 + 1) = k - 1 := by omega
    have e2 : (0 : ℕ) + k - 1 = k - 1 := by omega
    rw [e1, e2]
  · have hlt : k - r < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have e1 : k - (k - r + 1) = r - 1 := by omega
    rw [e1, Nat.mod_eq_of_lt (show r - 1 < k by omega)]
    have e2 : r + k - 1 = r - 1 + k := by omega
    rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (show r - 1 < k by omega)]

/-- Residue fold B: the `(i'+2)`-slot lands on `i`. -/
private theorem jlx_fldB {k r : ℕ} (hk : 4 ≤ k) (hr : r < k) :
    (k - ((k - r + 1) % k + 1)) % k = (r + k - 2) % k := by
  rcases Nat.lt_or_ge r 1 with h1 | h1
  · -- r = 0
    have hr0 : r = 0 := by omega
    rw [hr0, Nat.sub_zero]
    have e1 : (k + 1) % k = 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (show (1:ℕ) < k by omega),
        Nat.mod_eq_of_lt (show (1:ℕ) < k by omega)]
    rw [e1]
    have e2 : k - (1 + 1) = k - 2 := by omega
    have e3 : (0 : ℕ) + k - 2 = k - 2 := by omega
    rw [e2, e3]
  · rcases Nat.lt_or_ge r 2 with h2 | h2
    · -- r = 1
      have hr1 : r = 1 := by omega
      rw [hr1]
      have e1 : k - 1 + 1 = k := by omega
      rw [e1, Nat.mod_self]
      have e2 : k - (0 + 1) = k - 1 := by omega
      have e3 : (1 : ℕ) + k - 2 = k - 1 := by omega
      rw [e2, e3]
    · have hlt : k - r + 1 < k := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have e1 : k - (k - r + 1 + 1) = r - 2 := by omega
      rw [e1, Nat.mod_eq_of_lt (show r - 2 < k by omega)]
      have e2 : r + k - 2 = r - 2 + k := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (show r - 2 < k by omega)]

/-- Residue fold C: the `i'`-slot lands on `i+2`. -/
private theorem jlx_fldC {k r : ℕ} (hk : 1 ≤ k) (hr : r < k) :
    (k - ((k - (r + 1)) % k + 1)) % k = r := by
  rcases Nat.lt_or_ge (r + 1) k with hlt | hge
  · have hlt2 : k - (r + 1) < k := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    have e1 : k - (k - (r + 1) + 1) = r := by omega
    rw [e1, Nat.mod_eq_of_lt hr]
  · have heq : r + 1 = k := by omega
    rw [heq, Nat.sub_self, Nat.zero_mod]
    have e1 : k - (0 + 1) = k - 1 := by omega
    rw [e1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Opposite-system backward propagation step (HOL CQAOQLR.hl:259-322 route):
from edge `j+1 = 2` and the pin at `j`, conclude edge `j = 2`. Consumes
`TFITSKC_p27` on `(scsOppV39 s, fun i => -(peropp v s.k i))` at the
HOL index `i' = k - SUC((j+2) MOD k)`. -/
private theorem jlx_bwd_step (hmnl : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (hk3 : 3 < s.k) (hs : isScsV39 s) (hMMs : v ∈ MMsV39 s)
    (hgen : scsGeneric v) (hbasic : scsBasicV39 s)
    (hlt : ∀ i, s.a i (i + 1) < s.b i (i + 1))
    (hdiag : ∀ i j, scsDiag s.k i j →
      s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j)
    (j : ℕ) (hpin : s.a j (j + 1) = 2 ∧ s.b j (j + 1) ≤ 2 * h0)
    (hstep : dist (v (j + 1)) (v (j + 2)) = 2) :
    dist (v j) (v (j + 1)) = 2 := by
  have hsC := hs
  obtain ⟨hd0, hk1, hk2, hplo, hphi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag2, hb3, hbc, hJmod, hJsq, hcard⟩ := hsC
  have hk0 : s.k ≠ 0 := by omega
  have hk1' : 1 < s.k := by omega
  have hk4 : 4 ≤ s.k := by omega
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hMMs
  have hper : Periodic v s.k := hBB.2.1
  set r : ℕ := (j + 2) % s.k with hrdef
  have hr : r < s.k := Nat.mod_lt _ (by omega)
  set i' : ℕ := s.k - (r + 1) with hi'def
  have ei'1 : i' + 1 = s.k - r := by rw [hi'def]; omega
  have ei'2 : i' + 2 = s.k - r + 1 := by rw [hi'def]; omega
  have ei'3 : i' + 3 = s.k - r + 2 := by rw [hi'def]; omega
  -- MM / generic / basic of the opposite system
  have hMMs' : MMsV39 (scsOppV39 s) (fun i => -(peropp v s.k i)) :=
    MM_SCS_OPP_fb s v s.k rfl hs (by omega) hMMs
  have hs' : isScsV39 (scsOppV39 s) := jlx_opp_isscs s hs
  have hgen' : scsGeneric (fun i => -(peropp v s.k i)) :=
    jlx_generic_opp s v hBB hs hgen
  have hbasic' : scsBasicV39 (scsOppV39 s) := jlx_basic_opp s hs hbasic
  have hk3' : 3 < (scsOppV39 s).k := hk3
  -- diag trio for the opposite system
  have hdiag' : ∀ p q, scsDiag s.k p q →
      (scsOppV39 s).a p q ≤ cstab ∧
        cstab < dist (-(peropp v s.k p)) (-(peropp v s.k q)) ∧
          4 * h0 < (scsOppV39 s).b p q := by
    intro p q hpq
    have hd2 := jlx_diag_opp s.k p q hk3 hpq
    have e1 := hdiag _ _ hd2
    refine ⟨e1.1, ?_, e1.2.2⟩
    have hm := e1.2.1
    rw [← dist_neg_neg] at hm
    exact hm
  -- the a/b folds at (i'+1, i'+2): land on (j+1, j)
  have fldA1 : (s.k - ((i' + 1) % s.k + 1)) % s.k = (j + 1) % s.k := by
    rw [ei'1, jlx_fldA (by omega) hr, hrdef]
    have e : ((j + 2) % s.k + (s.k - 1)) % s.k = (j + 2 + (s.k - 1)) % s.k :=
      Nat.ModEq.add_right (s.k - 1) (Nat.mod_modEq (j + 2) s.k)
    rw [show (j + 2) % s.k + s.k - 1 = (j + 2) % s.k + (s.k - 1) from by omega,
      e, show j + 2 + (s.k - 1) = j + 1 + s.k from by omega, Nat.add_mod_right]
  have fldB1 : (s.k - ((i' + 2) % s.k + 1)) % s.k = j % s.k := by
    rw [ei'2, jlx_fldB hk4 hr, hrdef]
    have e : ((j + 2) % s.k + (s.k - 2)) % s.k = (j + 2 + (s.k - 2)) % s.k :=
      Nat.ModEq.add_right (s.k - 2) (Nat.mod_modEq (j + 2) s.k)
    rw [show (j + 2) % s.k + s.k - 2 = (j + 2) % s.k + (s.k - 2) from by omega,
      e, show j + 2 + (s.k - 2) = j + s.k from by omega, Nat.add_mod_right]
  have fldC0 : (s.k - (i' % s.k + 1)) % s.k = (j + 2) % s.k := by
    rw [hi'def, jlx_fldC (by omega) hr, ← hrdef]
  have fldD0 : (s.k - ((i' + 3) % s.k + 1)) % s.k = (j + s.k - 1) % s.k := by
    have bridge : (r + s.k - 3) % s.k = (j + s.k - 1) % s.k := by
      have h2 : r % s.k = (j + 2) % s.k := by rw [hrdef, Nat.mod_mod]
      have h3 := (Nat.ModEq.add_right (s.k - 3)
        (show r ≡ j + 2 [MOD s.k] from h2) : r + (s.k - 3) ≡ j + 2 + (s.k - 3) [MOD s.k])
      rw [show j + s.k - 1 = j + 2 + (s.k - 3) from by omega,
        show r + s.k - 3 = r + (s.k - 3) from by omega]
      exact h3
    rw [← bridge]
    by_cases h0 : r = 0
    · rw [h0] at hr
      rw [ei'3, h0]
      have a2 : (s.k + 2) % s.k = 2 := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (show (2:ℕ) < s.k by omega),
          Nat.mod_eq_of_lt (show (2:ℕ) < s.k by omega)]
      rw [show s.k - 0 + 2 = s.k + 2 from by omega, a2]
      have a3 : s.k - (2 + 1) = s.k - 3 := by omega
      rw [a3, Nat.mod_eq_of_lt (by omega), show (0:ℕ) + s.k - 3 = s.k - 3 from by omega,
        Nat.mod_eq_of_lt (by omega)]
    · by_cases h1 : r = 1
      · rw [h1] at hr
        rw [ei'3, h1]
        have a2 : (s.k + 1) % s.k = 1 := by
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add,
            Nat.mod_eq_of_lt (show (1:ℕ) < s.k by omega),
            Nat.mod_eq_of_lt (show (1:ℕ) < s.k by omega)]
        rw [show s.k - 1 + 2 = s.k + 1 from by omega, a2]
        have a3 : s.k - (1 + 1) = s.k - 2 := by omega
        rw [a3, Nat.mod_eq_of_lt (by omega), show (1:ℕ) + s.k - 3 = s.k - 2 from by omega,
          Nat.mod_eq_of_lt (by omega)]
      · by_cases h2 : r = 2
        · rw [h2] at hr
          rw [ei'3, h2]
          have a2 : s.k - 2 + 2 = s.k := by omega
          rw [a2, Nat.mod_self]
          have a3 : s.k - (0 + 1) = s.k - 1 := by omega
          rw [a3, Nat.mod_eq_of_lt (by omega), show (2:ℕ) + s.k - 3 = s.k - 1 from by omega,
            Nat.mod_eq_of_lt (by omega)]
        · have h3 : 3 ≤ r := by omega
          rw [ei'3]
          have hlt2 : s.k - r + 2 < s.k := by omega
          rw [Nat.mod_eq_of_lt hlt2]
          have a3 : s.k - (s.k - r + 2 + 1) = r - 3 := by omega
          rw [a3, Nat.mod_eq_of_lt (show r - 3 < s.k by omega),
            show r + s.k - 3 = r - 3 + s.k from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (show r - 3 < s.k by omega)]
  -- P7/P8: a'/b' at (i'+1, i'+2) = a/b at (j+1, j) = a/b at j (sym)
  have foldAB : ∀ g : ℕ → ℕ → ℝ, Periodic2 g s.k → (∀ x y, g x y = g y x) →
      g (s.k - ((i' + 1) % s.k + 1)) (s.k - ((i' + 2) % s.k + 1)) = g j (j + 1) := by
    intro g hpg hsg
    have e := (periodic2Mod1 hk0 hpg (s.k - ((i' + 1) % s.k + 1))
      (s.k - ((i' + 2) % s.k + 1))).symm.trans
      (periodic2Mod2 hk0 hpg ((s.k - ((i' + 1) % s.k + 1)) % s.k)
        (s.k - ((i' + 2) % s.k + 1))).symm
    rw [e, fldA1, fldB1,
      periodic2Mod1 hk0 hpg (j + 1) (j % s.k), periodic2Mod2 hk0 hpg (j + 1) j,
      hsg (j + 1) j]
  have hP7 : (scsOppV39 s).a (i' + 1) (i' + 2) = 2 :=
    (foldAB s.a hpa fun x y => (hsym x y).1).trans hpin.1
  have hP8 : (scsOppV39 s).b (i' + 1) (i' + 2) ≤ 2 * h0 := by
    have e := foldAB s.b hpb fun x y => (hsym x y).2.2.2.1
    rw [show (scsOppV39 s).b (i' + 1) (i' + 2) = s.b j (j + 1) from e]
    exact hpin.2
  -- P9: dist (v' i') (v' (i'+1)) = 2 —— the known edge (j+1, j+2)
  have foldV1 : v (s.k - ((i' + 1) % s.k + 1)) = v (j + 1) := by
    have h1 := periodic_mod_p27 hper (s.k - ((i' + 1) % s.k + 1))
    rw [fldA1] at h1
    exact h1.trans (periodic_mod_p27 hper (j + 1)).symm
  have foldV2 : v (s.k - (i' % s.k + 1)) = v (j + 2) := by
    have h1 := periodic_mod_p27 hper (s.k - (i' % s.k + 1))
    rw [fldC0] at h1
    exact h1.trans (periodic_mod_p27 hper (j + 2)).symm
  have hP9 : dist (-(peropp v s.k i')) (-(peropp v s.k (i' + 1))) = 2 := by
    rw [dist_neg_neg, show peropp v s.k i' = v (s.k - (i' % s.k + 1)) from rfl,
      show peropp v s.k (i' + 1) = v (s.k - ((i' + 1) % s.k + 1)) from rfl,
      foldV2, foldV1, dist_comm]
    exact hstep
  -- P10: 2 < b' i' (i'+1) —— folds to 2 < b (j+1) (j+2)
  have foldB2 : s.b (s.k - (i' % s.k + 1)) (s.k - ((i' + 1) % s.k + 1))
      = s.b (j + 1) (j + 2) := by
    have e := (periodic2Mod1 hk0 hpb (s.k - (i' % s.k + 1))
      (s.k - ((i' + 1) % s.k + 1))).symm.trans
      (periodic2Mod2 hk0 hpb ((s.k - (i' % s.k + 1)) % s.k)
        (s.k - ((i' + 1) % s.k + 1))).symm
    rw [e, fldC0, fldA1,
      periodic2Mod1 hk0 hpb (j + 2) ((j + 1) % s.k), periodic2Mod2 hk0 hpb (j + 2) (j + 1),
      (hsym (j + 2) (j + 1)).2.2.2.1]
  have hP10 : 2 < (scsOppV39 s).b i' (i' + 1) := by
    rw [show (scsOppV39 s).b i' (i' + 1)
        = s.b (s.k - (i' % s.k + 1)) (s.k - ((i' + 1) % s.k + 1)) from rfl,
      foldB2]
    have h2 := SCS_A_2_p27 s hs (j + 1)
    exact lt_of_le_of_lt h2 (hlt (j + 1))
  -- P1: a' (i'+2) (i'+3) < b' (i'+2) (i'+3) —— folds to a/b at (j+k-1, j)
  have foldA2 : (scsOppV39 s).a (i' + 2) (i' + 3) = s.a (j + s.k - 1) j := by
    have e := (periodic2Mod1 hk0 hpa (s.k - ((i' + 2) % s.k + 1))
      (s.k - ((i' + 3) % s.k + 1))).symm.trans
      (periodic2Mod2 hk0 hpa ((s.k - ((i' + 2) % s.k + 1)) % s.k)
        (s.k - ((i' + 3) % s.k + 1))).symm
    rw [show (scsOppV39 s).a (i' + 2) (i' + 3)
        = s.a (s.k - ((i' + 2) % s.k + 1)) (s.k - ((i' + 3) % s.k + 1)) from rfl,
      e, fldB1, fldD0,
      periodic2Mod1 hk0 hpa j ((j + s.k - 1) % s.k), periodic2Mod2 hk0 hpa j (j + s.k - 1),
      (hsym j (j + s.k - 1)).1]
  have foldB3 : (scsOppV39 s).b (i' + 2) (i' + 3) = s.b (j + s.k - 1) j := by
    have e := (periodic2Mod1 hk0 hpb (s.k - ((i' + 2) % s.k + 1))
      (s.k - ((i' + 3) % s.k + 1))).symm.trans
      (periodic2Mod2 hk0 hpb ((s.k - ((i' + 2) % s.k + 1)) % s.k)
        (s.k - ((i' + 3) % s.k + 1))).symm
    rw [show (scsOppV39 s).b (i' + 2) (i' + 3)
        = s.b (s.k - ((i' + 2) % s.k + 1)) (s.k - ((i' + 3) % s.k + 1)) from rfl,
      e, fldB1, fldD0,
      periodic2Mod1 hk0 hpb j ((j + s.k - 1) % s.k), periodic2Mod2 hk0 hpb j (j + s.k - 1),
      (hsym j (j + s.k - 1)).2.2.2.1]
  have hP1 : (scsOppV39 s).a (i' + 2) (i' + 3) < (scsOppV39 s).b (i' + 2) (i' + 3) := by
    rw [foldA2, foldB3]
    have h := hlt (j + s.k - 1)
    have e1 : j + s.k - 1 + 1 = j + s.k := by omega
    have e2 : s.a (j + s.k - 1) (j + s.k) = s.a (j + s.k - 1) j :=
      (hpa (j + s.k - 1) j).2
    have e3 : s.b (j + s.k - 1) (j + s.k) = s.b (j + s.k - 1) j :=
      (hpb (j + s.k - 1) j).2
    rwa [e1, e2, e3] at h
  -- the TFITSKC step on the opposite system
  have hres0 := TFITSKC_p27 hmnl (scsOppV39 s) (fun i => -(peropp v s.k i)) i'
    hP1 hk3' hs' hMMs' hgen' hbasic' hP7 hP8 hP9 hP10 hdiag'
  have hres : dist (-(peropp v s.k (i' + 1))) (-(peropp v s.k (i' + 2))) = 2 := hres0
  rw [dist_neg_neg,
    show peropp v s.k (i' + 1) = v (s.k - ((i' + 1) % s.k + 1)) from rfl,
    show peropp v s.k (i' + 2) = v (s.k - ((i' + 2) % s.k + 1)) from rfl,
    foldV1] at hres
  have foldV3 : v (s.k - ((i' + 2) % s.k + 1)) = v j := by
    have h1 := periodic_mod_p27 hper (s.k - ((i' + 2) % s.k + 1))
    rw [fldB1] at h1
    exact h1.trans (periodic_mod_p27 hper j).symm
  rw [foldV3, dist_comm] at hres
  exact hres

/-! ### jlxfdmj-w4: modular-distance arithmetic (self-contained, kernel-checked) -/

/-- Forward mod-distance spec: `(b + k - a) % k` is the unique `d < k` with
`(a + d) % k = b` (for `a, b < k`, `1 ≤ k`). -/
private theorem jlx_fwd_dist_spec {k a b : ℕ} (hk : 1 ≤ k) (ha : a < k) (hb : b < k) :
    (a + (b + k - a) % k) % k = b := by
  by_cases hab : a < b
  · have h1 : b + k - a = (b - a) + k := by omega
    have h2 : b - a < k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    have h3 : a + (b - a) = b := by omega
    rw [h3, Nat.mod_eq_of_lt hb]
  · by_cases heq : a = b
    · subst b
      have h1 : a + k - a = k := by omega
      rw [h1, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt ha]
    · have h2 : a - b < k := by omega
      have h1 : b + k - a = k - (a - b) := by omega
      have h3 : a + (k - (a - b)) = k + b := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : k - (a - b) < k), h3, Nat.add_mod_left,
        Nat.mod_eq_of_lt hb]

/-- Uniqueness of the forward mod-distance. -/
private theorem jlx_fwd_dist_unique {k a b l : ℕ} (hk : 1 ≤ k) (ha : a < k)
    (_hb : b < k) (h : (a + l) % k = b) : l % k = (b + k - a) % k := by
  have hr : l % k < k := Nat.mod_lt _ (by omega)
  have h1 : (a + l % k) % k = b := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt ha] at h
    exact h
  by_cases hlt : a + l % k < k
  · rw [Nat.mod_eq_of_lt hlt] at h1
    have h2 : b + k - a = l % k + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_mod]
  · have hge : k ≤ a + l % k := by omega
    have h2 : a + l % k = (a + l % k - k) + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a + l % k - k < k)] at h1
    have h3 : b + k - a = l % k := by omega
    rw [h3, Nat.mod_mod]

/-- Backward mod-distance spec: `(a + k - b) % k` is the unique `m < k` with
`(a + k - m) % k = b` (for `a, b < k`, `1 ≤ k`). -/
private theorem jlx_bwd_dist_spec {k a b : ℕ} (_hk : 1 ≤ k) (ha : a < k) (hb : b < k) :
    (a + k - (a + k - b) % k) % k = b := by
  by_cases hab : a < b
  · have h1 : a + k - b < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : a + k - (a + k - b) = b := by omega
    rw [h2, Nat.mod_eq_of_lt hb]
  · by_cases heq : a = b
    · subst b
      have h1 : a + k - a = k := by omega
      rw [h1, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · have h2 : a - b < k := by omega
      have h1 : a + k - b = (a - b) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
      have h3 : a + k - (a - b) = k + b := by omega
      rw [h3, Nat.add_mod_left, Nat.mod_eq_of_lt hb]

/-- Complement relation: backward distance is `k - forward distance`. -/
private theorem jlx_bwd_of_fwd {k a b : ℕ} (hk : 1 ≤ k) (ha : a < k) (hb : b < k)
    (hne : a ≠ b) : (a + k - b) % k = k - (b + k - a) % k := by
  by_cases hab : a < b
  · have h1 : a + k - b < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : b + k - a = (b - a) + k := by omega
    have h3 : b - a < k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h3]
    omega
  · have hbe : b < a := by omega
    have h1 : b + k - a = k - (a - b) := by omega
    have h1' : k - (a - b) < k := by omega
    rw [h1, Nat.mod_eq_of_lt h1']
    have h2 : a + k - b = (a - b) + k := by omega
    have h3 : a - b < k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h3]
    omega

/-- Uniqueness of the backward mod-distance (for `1 ≤ m ≤ k`). -/
private theorem jlx_bwd_dist_unique {k a b m : ℕ} (hk : 1 ≤ k) (ha : a < k) (hb : b < k)
    (hne : a ≠ b) (hm1 : 1 ≤ m) (hmk : m ≤ k) (h : (a + k - m) % k = b) :
    m = (a + k - b) % k := by
  have hmk' : k - m < k := by omega
  have e : a + k - m = a + (k - m) := by omega
  have h1 : (a + (k - m)) % k = b := by rw [← e]; exact h
  have h2 : (k - m) % k = (b + k - a) % k := jlx_fwd_dist_unique hk ha hb h1
  rw [Nat.mod_eq_of_lt hmk'] at h2
  have h4 : (a + k - b) % k = m := by
    rw [jlx_bwd_of_fwd hk ha hb hne]
    rw [← h2]
    omega
  exact h4.symm






/-- Main lemma, `3 < s.k` case: HOL `JLXFDMJ` (JLXFDMJ.hl:227-818) — the seed
edge propagates to every edge whose residue is not the unique `scs_M` index. -/
private theorem jlxfdmj_ge4 (hmnl : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
      3 < s.k → isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
        dist (v i) (v (i + 1)) = 2 →
        (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
        (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
        (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
        s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
        ∀ j, j % s.k ∉ scsM s → dist (v j) (v (j + 1)) = 2 := by
  intro s v i hk3 hs hMMs hgen hbasic hseed hb4 hM ha4 hlt ha0 hb0 j hj
  have hsC := hs
  obtain ⟨hd0, hk1, hk2, hplo, hphi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym, hch,
    hdiag0, hdiag2, hb3, hbc, hJmod, hJsq, hcard⟩ := hsC
  have hk0 : s.k ≠ 0 := by omega
  have hk1' : 1 < s.k := by omega
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hMMs
  have hper : Periodic v s.k := hBB.2.1
  have hadiag3 : ∀ p q, scsDiag s.k p q →
      s.a p q ≤ cstab ∧ cstab < dist (v p) (v q) ∧ 4 * h0 < s.b p q :=
    fun p q hd => ⟨(ha4 p q hd).1, (ha4 p q hd).2, hb4 p q hd⟩
  -- the unified "bad residue" `x` with pins
  obtain ⟨x, hMx, hpin, hxE⟩ : ∃ x : ℕ, (∀ y : ℕ, y ∈ scsM s → y = x) ∧
      (∀ r : ℕ, r % s.k ≠ x → s.a r (r + 1) = 2 ∧ s.b r (r + 1) ≤ 2 * h0) ∧
      (x = s.k ∨ x ∈ scsM s) := by
    by_cases hE : (scsM s).Nonempty
    · obtain ⟨x, hx⟩ := hE
      have hsingle : scsM s = {x} := by
        apply Set.Subset.antisymm
        · intro y hy
          exact Set.mem_singleton_iff.mpr
            ((Set.ncard_le_one (FINITE_SCS_M_p27 s)).mp hM y hy x hx)
        · intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hx
      refine ⟨x, ?_, ?_, Or.inr hx⟩
      · intro y hy
        have h1 : y ∈ ({x} : Set ℕ) := by rw [← hsingle]; exact hy
        exact Set.mem_singleton_iff.mp h1
      · intro r hrx
        obtain ⟨hbl, hal⟩ := SCS_M_EQ_1_p27 s x hsingle hs r hrx
        exact ⟨hal, hbl⟩
    · have hM0 : scsM s = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
      refine ⟨s.k, ?_, ?_, Or.inl rfl⟩
      · intro y hy
        rw [hM0] at hy
        exact ((Set.mem_empty_iff_false y).mp hy).elim
      · intro r _
        have hmem : ∀ t : ℕ, ¬ (2 * h0 < s.b (t % s.k) (t % s.k + 1) ∨
            2 < s.a (t % s.k) (t % s.k + 1)) := by
          intro t hcon
          have h1 : t % s.k ∈ scsM s := by
            rw [scsM]
            exact ⟨Nat.mod_lt _ (by omega), hcon⟩
          rw [hM0] at h1
          exact h1
        have hpin0 : ∀ t : ℕ, s.a t (t + 1) = 2 ∧ s.b t (t + 1) ≤ 2 * h0 := by
          intro t
          have hb : s.b (t % s.k) (t % s.k + 1) ≤ 2 * h0 :=
            not_lt.mp (fun h => hmem t (Or.inl h))
          have ha : s.a (t % s.k) (t % s.k + 1) ≤ 2 :=
            not_lt.mp (fun h => hmem t (Or.inr h))
          have ha' : 2 ≤ s.a (t % s.k) (t % s.k + 1) := SCS_A_2_p27 s hs (t % s.k)
          have ha2 : s.a (t % s.k) (t % s.k + 1) = 2 := le_antisymm ha ha'
          have e1 : s.a t (t + 1) = s.a (t % s.k) (t % s.k + 1) := by
            calc s.a t (t + 1) = s.a (t % s.k) ((t + 1) % s.k) :=
                periodic2_mod_p27 hpa t (t + 1)
              _ = s.a (t % s.k) ((t % s.k + 1) % s.k) :=
                congrArg (s.a (t % s.k)) (mod_add_c_p27 (c := 1) hk1').symm
              _ = s.a (t % s.k) (t % s.k + 1) := by
                rw [periodic2_mod_p27 hpa (t % s.k) (t % s.k + 1), Nat.mod_mod]
          have e2 : s.b t (t + 1) = s.b (t % s.k) (t % s.k + 1) := by
            calc s.b t (t + 1) = s.b (t % s.k) ((t + 1) % s.k) :=
                periodic2_mod_p27 hpb t (t + 1)
              _ = s.b (t % s.k) ((t % s.k + 1) % s.k) :=
                congrArg (s.b (t % s.k)) (mod_add_c_p27 (c := 1) hk1').symm
              _ = s.b (t % s.k) (t % s.k + 1) := by
                rw [periodic2_mod_p27 hpb (t % s.k) (t % s.k + 1), Nat.mod_mod]
          exact ⟨by rw [e1, ha2], by rw [e2]; exact hb⟩
        exact hpin0 r
  -- seed at the seed residue
  have hi0' : i % s.k < s.k := Nat.mod_lt _ (by omega)
  have hr0' : j % s.k < s.k := Nat.mod_lt _ (by omega)
  have hseed0 : dist (v (i % s.k)) (v (i % s.k + 1)) = 2 := by
    have e1 : v (i % s.k) = v i := (periodic_mod_p27 hper i).symm
    have e2 : v (i % s.k + 1) = v (i + 1) := by
      have w1 := periodic_mod_p27 hper (i % s.k + 1)
      have w2 : (i % s.k + 1) % s.k = (i + 1) % s.k := mod_add_c_p27 (c := 1) hk1'
      rw [w2] at w1
      exact w1.trans (periodic_mod_p27 hper (i + 1)).symm
    rw [← e1] at hseed
    rw [← e2] at hseed
    exact hseed
  have hi_ne_x : i % s.k ≠ x := by
    intro hcon
    have hmem : i % s.k ∈ scsM s := by
      rcases hxE with hxe | hxe
      · rw [hxe] at hcon
        exact absurd hcon (Nat.ne_of_lt hi0')
      · rw [← hcon] at hxe
        exact hxe
    rw [scsM] at hmem
    obtain ⟨-, hbad | hbad⟩ := hmem
    · have e2i : s.b i (i + 1) = s.b (i % s.k) (i % s.k + 1) := by
        calc s.b i (i + 1) = s.b (i % s.k) ((i + 1) % s.k) :=
            periodic2_mod_p27 hpb i (i + 1)
          _ = s.b (i % s.k) ((i % s.k + 1) % s.k) :=
            congrArg (s.b (i % s.k)) (mod_add_c_p27 (c := 1) hk1').symm
          _ = s.b (i % s.k) (i % s.k + 1) := by
            rw [periodic2_mod_p27 hpb (i % s.k) (i % s.k + 1), Nat.mod_mod]
      rw [← e2i] at hbad
      exact not_lt.mpr hb0 hbad
    · have e1i : s.a i (i + 1) = s.a (i % s.k) (i % s.k + 1) := by
        calc s.a i (i + 1) = s.a (i % s.k) ((i + 1) % s.k) :=
            periodic2_mod_p27 hpa i (i + 1)
          _ = s.a (i % s.k) ((i % s.k + 1) % s.k) :=
            congrArg (s.a (i % s.k)) (mod_add_c_p27 (c := 1) hk1').symm
          _ = s.a (i % s.k) (i % s.k + 1) := by
            rw [periodic2_mod_p27 hpa (i % s.k) (i % s.k + 1), Nat.mod_mod]
      rw [← e1i, ha0] at hbad
      exact lt_irrefl _ hbad
  have hr_ne_x : j % s.k ≠ x := by
    intro hcon
    apply hj
    rcases hxE with hxe | hxe
    · rw [hxe] at hcon
      exact absurd hcon (Nat.ne_of_lt hr0')
    · rw [← hcon] at hxe
      exact hxe
  -- the two single-step propagations
  have hfwd : ∀ y : ℕ, dist (v y) (v (y + 1)) = 2 → (y + 1) % s.k ≠ x →
      dist (v (y + 1)) (v (y + 2)) = 2 := by
    intro y hy hxy
    have pin1 := hpin (y + 1) hxy
    exact TFITSKC_p27 hmnl s v y (hlt (y + 2)) hk3 hs hMMs hgen hbasic pin1.1 pin1.2 hy
      (lt_of_le_of_lt (SCS_A_2_p27 s hs y) (hlt y)) hadiag3
  have hbwd : ∀ y : ℕ, dist (v (y + 1)) (v (y + 2)) = 2 → y % s.k ≠ x →
      dist (v y) (v (y + 1)) = 2 := fun y hy hxy =>
    jlx_bwd_step hmnl s v hk3 hs hMMs hgen hbasic hlt hadiag3 y (hpin y hxy) hy
  -- residue bookkeeping
  set i0 := i % s.k with hi0def
  set r0 := j % s.k with hr0def
  have hi0 : i0 < s.k := by rw [hi0def]; exact Nat.mod_lt _ (by omega)
  have hr0 : r0 < s.k := by rw [hr0def]; exact Nat.mod_lt _ (by omega)
  set df : ℕ := if x = s.k then s.k else (x + s.k - i0) % s.k with hdfdef
  set dr : ℕ := (r0 + s.k - i0) % s.k with hdrdef
  -- forward arc
  have hF : ∀ m : ℕ, (∀ l : ℕ, 1 ≤ l → l ≤ m → (i0 + l) % s.k ≠ x) →
      dist (v (i0 + m)) (v (i0 + m + 1)) = 2 := by
    intro m
    induction m with
    | zero => intro _; exact hseed0
    | succ n ih =>
        intro hbound
        have h1 : dist (v (i0 + n)) (v (i0 + n + 1)) = 2 :=
          ih (fun l h1 h2 => hbound l h1 (by omega))
        have hx1 : (i0 + n + 1) % s.k ≠ x := hbound (n + 1) (by omega) (by omega)
        exact hfwd (i0 + n) h1 hx1
  have hseedK : dist (v (i0 + s.k)) (v (i0 + s.k + 1)) = 2 := by
    rw [hper i0, show i0 + s.k + 1 = i0 + 1 + s.k from by omega, hper (i0 + 1)]
    exact hseed0
  -- backward arc from `i0 + s.k`
  have hB : ∀ m : ℕ, m ≤ s.k → (∀ l : ℕ, l < m → (i0 + s.k - 1 - l) % s.k ≠ x) →
      dist (v (i0 + s.k - m)) (v (i0 + s.k - m + 1)) = 2 := by
    intro m
    induction m with
    | zero => intro _ _; exact hseedK
    | succ n ih =>
        intro hnk hbound
        have h1 : dist (v (i0 + s.k - n)) (v (i0 + s.k - n + 1)) = 2 :=
          ih (by omega) (fun l hl => hbound l (by omega))
        have hy1 : dist (v (i0 + s.k - (n + 1) + 1)) (v (i0 + s.k - (n + 1) + 2)) = 2 := by
          have e2 : i0 + s.k - (n + 1) + 1 = i0 + s.k - n := by omega
          have e3 : i0 + s.k - (n + 1) + 2 = i0 + s.k - n + 1 := by omega
          rw [e2, e3]; exact h1
        have hxy : (i0 + s.k - (n + 1)) % s.k ≠ x := by
          have e4 : i0 + s.k - 1 - n = i0 + s.k - (n + 1) := by omega
          rw [← e4]; exact hbound n (by omega)
        exact hbwd (i0 + s.k - (n + 1)) hy1 hxy
  -- transfer helpers
  have ev_of : ∀ y : ℕ, y % s.k = r0 → (y + 1) % s.k = (j + 1) % s.k →
      dist (v y) (v (y + 1)) = 2 → dist (v j) (v (j + 1)) = 2 := by
    intro y hm1 hm2 hdist
    have w1 := periodic_mod_p27 hper y
    rw [hm1] at w1
    have w2 := periodic_mod_p27 hper (y + 1)
    rw [hm2] at w2
    rw [← w1.trans (periodic_mod_p27 hper j).symm,
      ← w2.trans (periodic_mod_p27 hper (j + 1)).symm]
    exact hdist
  -- case analysis on the bad residue
  rcases hxE with hxe | hxe
  · -- `x = s.k`: the forward arc is always clean
    subst x
    have harc : ∀ l : ℕ, 1 ≤ l → l ≤ dr → (i0 + l) % s.k ≠ s.k :=
      fun l _ _ hcon => Nat.ne_of_lt (Nat.mod_lt _ (by omega)) hcon
    have edr : (i0 + dr) % s.k = r0 := by
      have hm : dr ≡ r0 + s.k - i0 [MOD s.k] := by rw [hdrdef]; exact Nat.mod_modEq _ _
      have h2 : (i0 + dr) % s.k = (i0 + (r0 + s.k - i0)) % s.k := hm.add_left i0
      have h4 : i0 + (r0 + s.k - i0) = r0 + s.k := by omega
      rw [h2, h4, Nat.add_mod_right, Nat.mod_eq_of_lt hr0]
    have edr1 : (i0 + dr + 1) % s.k = (j + 1) % s.k := by
      rw [Nat.add_mod, edr, Nat.mod_eq_of_lt (show (1:ℕ) < s.k by omega),
        hr0def, mod_add_c_p27 (c := 1) hk1']
    exact ev_of (i0 + dr) edr edr1 (hF dr harc)
  · -- `x ∈ scsM s` (hence `x < s.k`)
    have hxk : x < s.k := by
      rw [scsM] at hxe
      exact hxe.1
    have hdf : df = (x + s.k - i0) % s.k := by
      rw [hdfdef]
      exact if_neg (Nat.ne_of_lt hxk)
    by_cases hlt : dr < df
    · -- forward arc from the seed
      have harc : ∀ l : ℕ, 1 ≤ l → l ≤ dr → (i0 + l) % s.k ≠ x := by
        intro l h1 h2 hcon
        have hlmod : l % s.k = df := by
          have h := jlx_fwd_dist_unique (k := s.k) (a := i0) (b := x) (l := l)
            (by omega) hi0 hxk hcon
          rwa [← hdf] at h
        have hml := Nat.mod_le l s.k
        omega
      have edr : (i0 + dr) % s.k = r0 := by
        have hm : dr ≡ r0 + s.k - i0 [MOD s.k] := by rw [hdrdef]; exact Nat.mod_modEq _ _
        have h2 : (i0 + dr) % s.k = (i0 + (r0 + s.k - i0)) % s.k := hm.add_left i0
        have h4 : i0 + (r0 + s.k - i0) = r0 + s.k := by omega
        rw [h2, h4, Nat.add_mod_right, Nat.mod_eq_of_lt hr0]
      have edr1 : (i0 + dr + 1) % s.k = (j + 1) % s.k := by
        rw [Nat.add_mod, edr, Nat.mod_eq_of_lt (show (1:ℕ) < s.k by omega),
          hr0def, mod_add_c_p27 (c := 1) hk1']
      exact ev_of (i0 + dr) edr edr1 (hF dr harc)
    · -- backward arc from `i0 + s.k`
      have hdf1 : 1 ≤ df := by
        by_contra hcon
        have hdf0 : df = 0 := by omega
        have hspec := jlx_fwd_dist_spec (k := s.k) (a := i0) (b := x) (by omega) hi0 hxk
        rw [← hdf] at hspec
        rw [hdf0, Nat.add_zero, Nat.mod_eq_of_lt hi0] at hspec
        exact hi_ne_x hspec
      have hdr1 : 1 ≤ dr := by omega
      have hi0r0 : i0 ≠ r0 := by
        intro hc
        have h1 : dr = 0 := by
          rw [hdrdef, ← hc, Nat.add_sub_cancel_left, Nat.mod_self]
        omega
      set db : ℕ := (i0 + s.k - r0) % s.k with hdbdef
      have hdbk : db ≤ s.k := by
        rw [hdbdef]
        exact (Nat.mod_lt _ (by omega)).le
      have hdb2 : db = s.k - dr := by
        rw [hdbdef, hdrdef]
        exact jlx_bwd_of_fwd (k := s.k) (a := i0) (b := r0) (by omega) hi0 hr0 hi0r0
      have edb : (i0 + s.k - db) % s.k = r0 := by
        rw [hdbdef]
        exact jlx_bwd_dist_spec (k := s.k) (a := i0) (b := r0) (by omega) hi0 hr0
      have hBdb : dist (v (i0 + s.k - db)) (v (i0 + s.k - db + 1)) = 2 := by
        apply hB db hdbk
        intro l hlb hcon
        have hm1 : 1 ≤ l + 1 := by omega
        have hmk : l + 1 ≤ s.k := by omega
        have hmm : (i0 + s.k - (l + 1)) % s.k = x := by
          have e : i0 + s.k - 1 - l = i0 + s.k - (l + 1) := by omega
          rw [e] at hcon
          exact hcon
        have hmu := jlx_bwd_dist_unique (k := s.k) (a := i0) (b := x) (m := l + 1)
          (by omega) hi0 hxk hi_ne_x hm1 hmk hmm
        have hxm : (i0 + s.k - x) % s.k = s.k - df := by
          rw [hdf]
          exact jlx_bwd_of_fwd (k := s.k) (a := i0) (b := x) (by omega) hi0 hxk hi_ne_x
        have hmdf : l + 1 = s.k - df := by rw [hmu, hxm]
        have hmb : l + 1 = db := by omega
        rw [hmb] at hmm
        rw [edb] at hmm
        exact hr_ne_x hmm
      have edb1 : (i0 + s.k - db + 1) % s.k = (j + 1) % s.k := by
        rw [Nat.add_mod, edb, Nat.mod_eq_of_lt (show (1:ℕ) < s.k by omega),
          hr0def, mod_add_c_p27 (c := 1) hk1']
      exact ev_of (i0 + s.k - db) edb edb1 hBdb

/-- Public form of the landed `jlxfdmj_ge4` with the HOL premise `3 < s.k`
(`JLXFDMJ.hl:214-224`; recovered from lane `jlxfdmj-w1`'s public
`JLXFDMJ_ge4_p27`).  Consumers are all `k ∈ {4,5,6}` (`scs6M1`/`scs6I1` k=6,
LA33 k=4, `scs5M2` k=5), so they discharge `3 < s.k` by `norm_num`.  The
original `JLXFDMJ_p27` statement is untouched (k=3 case remains open). -/
theorem JLXFDMJ_ge4_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
        3 < s.k → isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
          dist (v i) (v (i + 1)) = 2 →
            (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
              (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
                (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
                  s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
                    ∀ j, j % s.k ∉ scsM s → dist (v j) (v (j + 1)) = 2 := by
  exact jlxfdmj_ge4

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