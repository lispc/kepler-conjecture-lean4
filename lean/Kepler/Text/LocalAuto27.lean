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
- Fill-wave 2026-09-19: `SCS_M_LE_1_p27` and `HXHYTIJ_p27` discharged
  (10 sorries remain). Blocker re-scan: `LKGRQUI_concl`/`YXIONXL3_concl`/
  `CUXVZOZ_concl` still `sorry` in LocalAuto1; `XWITCCN` still `sorry` in
  LocalAuto36; `SCS_M_EQ_1` content still missing corpus-wide.

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
    SCS_M_EQ_1), `JCYFMRP_p27` (sorry; NEEDS `CUXVZOZ`, still `sorry` in
    LocalAuto1:1616).
  Section C (JLXFDMJ): `SCS_M_EQ_0_p27` (proved), `FINITE_SCS_M_p27`
    (proved), `SCS_M_EQ_1_p27` (sorry; NEEDS the `scs_M` boundary
    structure — isScs's ncard budget only bounds `k ≥ 4` cases), 
    `SCS_M_LE_K_p27` (proved), `JLXFDMJ_p27` (sorry; NEEDS
    `SCS_M_EQ_1_p27`); `SCS_A_2_p27` lives in Section 0.
  Section D (SGTRNAF): `UXCKFPE2_p27` (proved 2026-09-18 via
    `UXCKFPE_p24`), `SGTRNAF_p27` (proved 2026-09-18).
  Section E (HXHYTIJ): `HXHYTIJ_p27` (proved 2026-09-19: the
    `min_num`/choice argument done directly over the `BBprime`/`BBindexMin`
    definitions).
  Section F (AYQJTMD): `XWITCCN2_p27` (sorry; NEEDS the `XEIJITAF`
    s_init cases — `XWITCCN` still `sorry` in LocalAuto36:1511 and
    LocalAuto1:671; no `s_init`-member `isScsV39` lemma exists yet),
    `unadorned_MMs_p27` (proved 2026-09-18), `S_INIT_IS_UNADORNED_p27`
    (proved 2026-09-18), `AYQJTMD_p27` (sorry; NEEDS `XWITCCN2_p27` —
    its other two inputs are proved here), `EAPGLE_p27` (sorry; NEEDS
    the JEJTVGB registry, LocalAuto1:541-547, `ZITHLQN_concl` pending).
  Section G (FEKTYIY): `FEKTYIY_p27` (sorry).

  Section H (LKGRQUI): `SLICE_IS_UNADORNED_p27` (proved),
    `LKGRQUI_p27` (sorry).

  DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
  HOL input; the proved items use mod/order arithmetic only.
-/

import Kepler.Text.LocalAuto1
-- Row/capstone import (2026-09-18 fill wave): LocalAuto24 carries the proved
-- `UXCKFPE_p24` case assembly (`BBprimeV39 s ≠ ∅` from `BBs` + `taustar < 0`;
-- its k = 3..6 case lemmas remain `sorry` in that lane). Importability
-- verified empirically: LA24's chain (LA1/LA17/LA20/LA22/LA23) carries no
-- `atn2` conflict with this file's substrate.
import Kepler.Text.LocalAuto24
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

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

/-- HOL `JCYFMRP_concl` (JCYFMRP.hl:240). -/
theorem JCYFMRP_p27 :
    main_nonlinear_terminal_v11 →
      ∀ (s : ScsV39) (v : ℕ → V3),
        3 < s.k → isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
          (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
            (∀ i, s.a i (i + 1) = 2) →
              (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
                ∃ i, dist (v i) (v (i + 1)) = 2 := by
  sorry
    -- DISCHARGES: NEEDS `CUXVZOZ` (the linear loop reaching the boundary)
    -- composed with the `SCS_M_LE_1` pinned-edge lemma.

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

/-- HOL `SCS_M_EQ_1` (JLXFDMJ.hl:159). -/
theorem SCS_M_EQ_1_p27 (s : ScsV39) (i : ℕ) :
    3 ≤ s.k → (∀ i, s.a i (i + 1) < s.b i (i + 1)) → isScsV39 s →
      i ∈ scsM s → (scsM s).ncard = 1 := by
  sorry
    -- DISCHARGES: NEEDS the `scs_M` boundary structure (a diagonal value hits
    -- 2·h0 / 2 exactly once because a < b holds at every edge); the source
    -- reasons on the `V{0,1,2}` archive cells.

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

/-- HOL `XWITCCN2` (AYQJTMD.hl:72). -/
theorem XWITCCN2_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ := by
  sorry
    -- DISCHARGES: NEEDS the `XEIJITAF`/`UXCKFPE2` s_init cases of the
    -- `taustar < 0` non-emptiness for the s_init list.

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

/-- HOL `AYQJTMD` (AYQJTMD.hl:206). -/
theorem AYQJTMD_p27 : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ := by
  sorry
    -- DISCHARGES: NEEDS `XWITCCN2` + `S_INIT_IS_UNADORNED` +
    -- `unadorned_MMs` (the source rewrites `MMs` back to `BBprime2`).

/-- HOL `EAPGLE` (AYQJTMD.hl:222). -/
theorem EAPGLE_p27 :
    (∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39 := by
  sorry
    -- DISCHARGES: NEEDS `AYQJTMD` modulo the six JEJTVGB items
    -- (the `JEJTVGB_concl`/`JEJTVGB_assume_v39` registry, LocalAuto1:544).

/-! ## Section G: FEKTYIY -/

/-- HOL `FEKTYIY` (FEKTYIY.hl:91). -/
theorem FEKTYIY_p27 : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k → ¬Coplanar (({0} ∪ Set.range v : Set V3)) := by
  sorry
    -- DISCHARGES: NEEDS the ball-annulus/non-coplanarity of an equilateral
    -- `MMs` realisation (`v` not contained in any plane through 0).

/-! ## Section H: LKGRQUI -/

/-- HOL `SLICE_IS_UNADORNED` (LKGRQUI.hl:82). -/
theorem SLICE_IS_UNADORNED_p27 :
    ∀ s p q d' mkj, unadornedV39 (scsHalfSliceV39 s p q d' mkj) := by
  intro s p q d' mkj
  simp [unadornedV39, scsHalfSliceV39]

/-- HOL `LKGRQUI` (LKGRQUI.hl:87). -/
theorem LKGRQUI_p27 : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop),
    isScsV39 s → (s', s'') = scsSliceV39 s p q d' d'' mkj →
    scsArrowV39 {s} {s', s''} := by
  sorry
    -- DISCHARGES: NEEDS `SLICE_IS_UNADORNED` fold of `scs_arrow_v39` +
    -- the `is_scs_slice` boundary-collar estimates transferring the
    -- `BBs` boundlessness (`BB` transfer lemmas of the source).