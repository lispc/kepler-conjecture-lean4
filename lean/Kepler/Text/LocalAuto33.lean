/-
LocalAuto33 — Local Fan chapter appendix leftovers, two-file bundle
(skeleton-first pass, lane 33):

  - `scripts/local/AUEAHEH.hl` (2960 ln, 0 defs + 101 thms; H. L. Truong /
    T. Hales 2012-2013, "remaining conclusions from appendix to Local Fan
    chapter") — the diag-stabilisation arrow tree over the k = 4 systems:
    the `4I1 → 3M1` slice (`SCS_4I1_SLICE_02`/`AUEAHEH`), the four
    `BB_4X_IMP_BB_4Y` / `MM_4X_IMP_4Y` family struts
    (4I3→4T4/4M6', 4M2→4M6', 4M3'→4M6', 4M4'→4M7, 4M5'→4M8, 4M6'→4T5),
    the `stab → prop_equ/opp` re-indexing identities
    (`PROP_OPP_DIAG_*_13`), the slice arrows to the ear systems
    (`SCS_4M2_SLICE_13` .. `SCS_4M5_SLICE_13`, `SCS_4M4_SLICE_02`), the
    `SET_STAB`/`EXPAND_STAB_DIAG`/`SET_EQ_DIAG_STAB` set normalisations
    and the master arrows `VQFYMZY`/`BNAWVNH`/`RAWZDIB`/`MFKLVDK`/`RYPDIXT`.
  - `scripts/local/ARDBZYE.hl` (2907 ln, 0 defs + 81 thms) — the
    `scs_4I2` / `scs_4I1` terminal kit: the `is_scs_v39` / `scs_basic_v39`
    / `scs_k_v39` / `scs_J_v39` fact bank for the k = 4 concrete systems,
    the `scs_M`-emptyness quartet, the mod-4 diag calculus
    (`SCS_DIAG_4_CASES`, `SCS_DIAG_ADD1`, `SCS_DIAG_4_ADD*`,
    `EXPAND_DIAG_4(V)`, `EXPAND_STAB_DIAG_4`), the straightness /
    `EDGE_EQ_2` / `ear_acute` case bank consuming
    `main_nonlinear_terminal_v11`, and the master arrows `ARDBZYE`
    (`4I2 → 4T1, 4T2`) and `FYSSVEV` (`4I1 → 4I2, stab 4I1 0 2`).

FILE MAP (all names `_p33`-suffixed; source order kept inside each section)
  Section 0 (shared kit, this lane): `YXIONXL2_p33`, `OPP_IS_SCS_p33`
    (NEEDS the v39 twins of the Ocbicby lemmas — LocalAuto13's are over
    `ScsV39P13`), the mod-4 diag kit (`EXPAND_DIAG_4_p33`/`EXPAND_DIAG_4V_p33`
    — ARDBZYE items kept in Section 0 for the forward reference from
    `SET_EQ_DIAG_STAB_GEN4_p33`), the mod-4 diag case split
    `diag_pair_cases_p33`, the
    a/b table evaluations `a_diag_*_p33` / `b_diag_*_p33` / `a_edge_*` /
    `b_edge_*`, the general-k=4 set lemmas `SET_STAB_GEN4_p33`,
    `EXPAND_STAB_DIAG_GEN4_p33`, `SET_EQ_DIAG_STAB_GEN4_p33` (each
    instantiated once per concrete system), the stab field kit
    `stab_d_eq_p33`, `MMs_imp_BBs_p33`, the arrow scaffolds
    `ARROW_SPLIT_p33`, `FZIOTEF_SUBSET_p33`, `PRO_EQU_INV_p33` and the
    `pe_*_arrow_p33` prop-equation inverses.
  Section R (ARDBZYE, 81 thms): `GSXRFWM1_p33` .. `FYSSVEV_p33`.
  Section A (AUEAHEH, 101 thms): `SCS_DIAG_SCS_4I1_02_p33` ..
    `MM_4M6_IMP_STAB_4M6_p33`.

Encoding:
- HOL `real^3` <-> `V3` (Kepler.Geom); `dist(v i,v j)` <->
  `dist (v i) (v j)`; `vec 0` <-> `0`; `pi` <-> `Real.pi`.
- All toolkit defs (`is_scs_v39`, `scs_basic_v39`, `scs_M`, `MMs_v39`,
  `BBs_v39`, `scs_diag`, `scs_arrow_v39`, `scs_stab_diag_v39`,
  `scs_half_slice_v39`, `scs_slice_v39`, `scs_prop_equ_v39`,
  `scs_opp_v39`, `psort`, `funlist_v39`, `cs_adj`,
  `main_nonlinear_terminal_v11` and the concrete systems `scs_4I1` ..
  `scs_4M8`, `scs_3M1`, `scs_3T1`, `scs_3T3`, `scs_3T4`, `scs_3T6'`) are
  already ported in `Kepler.Text.LocalAuto1` (camelCase); this file adds
  no definitions.
- HOL `x MOD k` <-> `x % k`; `SUC i` <-> `i + 1`; `&n` <-> `(n : ℝ)`;
  `{}` <-> `∅`; `CARD` <-> `Set.ncard`; `{x | P}` set-builders <-> setOf.
- `sqrt8` <-> `Real.sqrt 8`; `cstab`, `h0` from `LocalAuto1`; `ups_x` <->
  `upsX` (Kepler.Geom); `dih_y` <-> `dihY_p18` (LocalAuto18).
- Same-wave files LocalAuto28-32 are NOT imported; everything this lane
  needs from them is re-stated here as `_p33` twins with NEEDS markers
  (`YXIONXL2_p33`, `OPP_IS_SCS_p33`).
- Proved items: mod/order arithmetic (`omega`, `decide`), definitional
  fold of `funlistV39`/`csAdj`/`scsStabDiagV39` tables, and assembly of
  the imported scaffolds (`FZIOTEF_*`, `STAB_BB`, `YRTAFYH_p17`,
  `XWNHLMD_MM_p26`, `PRO_EQU_ID1`, `YXIONXL3`).  Items whose own body is
  complete but rest on a `sorry`-typed upstream twin are annotated
  "proved modulo ..." in their docstring.
- Giants are `sorry`; every `sorry` carries a NEEDS note naming the
  blocking HOL input (DISCHARGES convention).

DISCHARGES: nothing yet (skeleton-first pass; the sorry'd items are the
BB-table comparisons, the half-slice/prop-equ table identities, the
opp-invariance twins and the `main_nonlinear_terminal_v11` case banks).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto17
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto20
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: shared kit (`_p33`) -/

/-- HOL `YXIONXL2` (Ocbicby.hl; the terminal arrow to the opposite system).
NEEDS: the `ScsV39` twin of `LocalAuto13.YXIONXL2_p13` (the peropp
re-indexing transports `BBprime`/`MMs` for `3 < k`). -/
theorem YXIONXL2_p33 (s : ScsV39) (hs : isScsV39 s) (hk : 3 < s.k) :
    scsArrowV39 {s} {scsOppV39 s} := sorry
  -- DISCHARGES: NEEDS Ocbicby.hl `YXIONXL2` over `ScsV39`.

/-- HOL `OPP_IS_SCS` (Ocbicby.hl:2536).  NEEDS: the `ScsV39` twin of
`LocalAuto13.OPP_IS_SCS_p13` (the 20-conjunct `is_scs_v39` check of
`peropp2 s.a k` records). -/
theorem OPP_IS_SCS_p33 (s : ScsV39) (hs : isScsV39 s) : isScsV39 (scsOppV39 s) := sorry
  -- DISCHARGES: NEEDS Ocbicby.hl `OPP_IS_SCS` over `ScsV39`.

/-- HOL `PROP_EQU_IS_SCS` (YXIONXL.hl:589).  NEEDS: the heavy conjunct is
the `is_scs_v39` ncard bound via the bijection `j ↦ (i + j) % k`
(`LocalAuto12.PROP_EQU_IS_SCS` is the same statement). -/
theorem PROP_EQU_IS_SCS_p33 {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) : isScsV39 (scsPropEquV39 s i) := sorry
  -- DISCHARGES: NEEDS YXIONXL.hl PROP_EQU_IS_SCS.

/-- HOL `YXIONXL3` (YXIONXL.hl:2573): cyclic re-indexing is an arrow.
NEEDS: `PROP_EQU_IS_SCS_p33` + `TRANS_MMS_SUBSET` (`LocalAuto12.YXIONXL3`
is the same statement). -/
theorem YXIONXL3_p33 (s : ScsV39) (i : ℕ) (hs : isScsV39 s) :
    scsArrowV39 {s} {scsPropEquV39 s i} := sorry
  -- DISCHARGES: NEEDS YXIONXL.hl YXIONXL3.

/-- HOL `PRO_EQU_ID1` (YXIONXL.hl:2212): the finite-order identity of the
prop-equation re-indexing (`LocalAuto12.PRO_EQU_ID1` is the same
statement, where it is proved). -/
theorem PRO_EQU_ID1_p33 {s : ScsV39} {k : ℕ} (hk : s.k = k) (hs : isScsV39 s)
    (i : ℕ) : s = scsPropEquV39 (scsPropEquV39 s i) (k - i % k) := sorry
  -- DISCHARGES: NEEDS YXIONXL.hl PRO_EQU_ID1 (mod-cycle arithmetic).

/-- HOL `XWNHLMD_MM` (PPBTYDQ.hl:560; `LocalAuto26.XWNHLMD_MM_p26` is the
same statement).  NEEDS: `XWITCCN` / `MMS_NONEMPTY` from taustar < 0. -/
theorem XWNHLMD_MM_p33 (s s' : ScsV39) (v : ℕ → V3) (hs : isScsV39 s)
    (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
    (hk : s.k = s'.k) (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
    (hds : s.d ≤ s'.d) : MMsV39 s' ≠ ∅ := sorry
  -- DISCHARGES: NEEDS PPBTYDQ.hl XWNHLMD_MM.

theorem stab_d_eq_p33 (s : ScsV39) (i j : ℕ) : (scsStabDiagV39 s i j).d = s.d := rfl

theorem MMs_imp_BBs_p33 {s : ScsV39} {v : ℕ → V3} (hv : v ∈ MMsV39 s) : BBsV39 s v := by
  obtain ⟨⟨⟨hbb, -, -⟩, -⟩, -, -, -, -⟩ := hv
  exact hbb

/-- The mod-4 residue case split of a `scs_diag 4` pair. -/
theorem diag_pair_cases_p33 (i j : ℕ) (h : scsDiag 4 i j) :
    (i % 4 = 0 ∧ j % 4 = 2) ∨ (i % 4 = 1 ∧ j % 4 = 3) ∨
      (i % 4 = 2 ∧ j % 4 = 0) ∨ (i % 4 = 3 ∧ j % 4 = 1) := by
  have h1 : i % 4 < 4 := Nat.mod_lt i (by omega)
  have h2 : j % 4 < 4 := Nat.mod_lt j (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := h
  have e1 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  have e2 : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
  rcases e1 with hi | hi | hi | hi <;> rcases e2 with hj | hj | hj | hj <;> omega

/-- HOL `EXPAND_DIAG_4` (ARDBZYE.hl:1947; kept in Section 0 for the
forward reference from `SET_EQ_DIAG_STAB_GEN4_p33`). -/
theorem EXPAND_DIAG_4_p33 (i j : ℕ) (h : scsDiag 4 i j) : j % 4 = (i + 2) % 4 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals omega

/-- HOL `EXPAND_DIAG_4V` (ARDBZYE.hl:2772; kept in Section 0 for the
forward reference from `SET_EQ_DIAG_STAB_GEN4_p33`). -/
theorem EXPAND_DIAG_4V_p33 (i j : ℕ) : scsDiag 4 i j ↔ j % 4 = (i + 2) % 4 := by
  constructor
  · exact EXPAND_DIAG_4_p33 i j
  · intro h
    rw [scsDiag]
    omega

/-! ### a/b table evaluations (csAdj systems) -/

theorem a_edge_4I1_p33 (i : ℕ) : scs4I1.a i (i + 1) = 2 := by
  simp only [scs4I1, mkUnadornedV39, csAdj, if_neg (by omega : ¬(i % 4 = (i + 1) % 4))]
  simp

theorem b_edge_4I1_p33 (i : ℕ) : scs4I1.b i (i + 1) = 2 * h0 := by
  simp only [scs4I1, mkUnadornedV39, csAdj, if_neg (by omega : ¬(i % 4 = (i + 1) % 4))]
  simp

theorem a_diag_4I1_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4I1.a i j = 2 * h0 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [scs4I1, mkUnadornedV39, csAdj]; split_ifs <;> first | rfl | (exfalso; omega)

theorem b_diag_4I1_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4I1.b i j = 6 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [scs4I1, mkUnadornedV39, csAdj]; split_ifs <;> first | rfl | (exfalso; omega)

theorem a_edge_4I2_p33 (i : ℕ) : scs4I2.a i (i + 1) = 2 := by
  simp only [scs4I2, mkUnadornedV39, csAdj, if_neg (by omega : ¬(i % 4 = (i + 1) % 4))]
  simp

theorem b_edge_4I2_p33 (i : ℕ) : scs4I2.b i (i + 1) = 2 * h0 := by
  simp only [scs4I2, mkUnadornedV39, csAdj, if_neg (by omega : ¬(i % 4 = (i + 1) % 4))]
  simp

theorem a_diag_4I2_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4I2.a i j = 3 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [scs4I2, mkUnadornedV39, csAdj]; split_ifs <;> first | rfl | (exfalso; omega)

theorem b_diag_4I2_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4I2.b i j = 6 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [scs4I2, mkUnadornedV39, csAdj]; split_ifs <;> first | rfl | (exfalso; omega)


/-- NEEDS: `is_scs_v39 scs_4M6'` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M6_p33 : isScsV39 scs4M6' := sorry

/-- NEEDS: `is_scs_v39 scs_4M7` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M7_p33 : isScsV39 scs4M7 := sorry

/-- NEEDS: `is_scs_v39 scs_4M8` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M8_p33 : isScsV39 scs4M8 := sorry

/-- NEEDS: `is_scs_v39 scs_4M3'` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M3_p33 : isScsV39 scs4M3' := sorry

/-- NEEDS: `is_scs_v39 scs_4M4'` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M4_p33 : isScsV39 scs4M4' := sorry

/-- NEEDS: `is_scs_v39 scs_4M5'` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_4M5_p33 : isScsV39 scs4M5' := sorry

theorem K_SCS_4M3_p33 : scs4M3'.k = 4 := rfl

theorem K_SCS_4M4_p33 : scs4M4'.k = 4 := rfl

theorem K_SCS_4M5_p33 : scs4M5'.k = 4 := rfl

theorem K_SCS_4M7_p33 : scs4M7.k = 4 := rfl

theorem K_SCS_4M8_p33 : scs4M8.k = 4 := rfl

theorem SCS_4M3_BASIC_p33 : scsBasicV39 scs4M3' := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem SCS_4M4_BASIC_p33 : scsBasicV39 scs4M4' := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem SCS_4M5_BASIC_p33 : scsBasicV39 scs4M5' := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem SCS_4M7_BASIC_p33 : scsBasicV39 scs4M7 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

theorem SCS_4M8_BASIC_p33 : scsBasicV39 scs4M8 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- Reflexive arrow on a singleton system. -/
theorem REFL_SING_p33 (y : ScsV39) (h : isScsV39 y) : scsArrowV39 {y} {y} :=
  FZIOTEF_REFL _ (fun t ht => by rw [Set.mem_singleton_iff] at ht; subst ht; exact h)

/-- The `{s} → {y}` arrow scaffold: `y` is `is_scs`, and any `MMs`-witness
for `s` yields a witness for `y`. -/
theorem ARROW_SING_p33 (s y : ScsV39) (hisy : isScsV39 y)
    (hmm : ∀ v : ℕ → V3, v ∈ MMsV39 s → MMsV39 y ≠ ∅) : scsArrowV39 {s} {y} := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at ht; subst ht; exact hisy
  · by_cases hex : (MMsV39 s).Nonempty
    · obtain ⟨v, hv⟩ := hex
      exact Or.inr ⟨y, rfl, hmm v hv⟩
    · refine Or.inl fun t ht => ?_
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact Set.not_nonempty_iff_eq_empty.mp hex

/-! ### a-table evaluations at diag pairs (funlist systems) -/

theorem a_diag_4I3_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4I3.a i j = Real.sqrt 8 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4I3, mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M2_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M2.a i j = 2 * h0 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M2, mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M3_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M3'.a i j = Real.sqrt 8 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M3', mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M4_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M4'.a i j = 2 * h0 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M4', mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M5_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M5'.a i j = 2 * h0 := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M5', mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M6_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M6'.a i j = cstab := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M6', mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M7_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M7.a i j = cstab := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M7, mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

theorem a_diag_4M8_p33 (i j : ℕ) (h : scsDiag 4 i j) : scs4M8.a i j = cstab := by
  rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
  all_goals simp [scs4M8, mkUnadornedV39, funlistV39, psort, assocdV39, r1, r2, h.1]

/-- The `YRTAFYH` instantiation for k = 4 systems used by every
`STAB_*_SCS` below (proved modulo `LocalAuto17.YRTAFYH_p17`). -/
theorem STAB_SCS_p33 (s : ScsV39) (hs : isScsV39 s) (hb : scsBasicV39 s)
    (hk : s.k = 4) (hab : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab)
    (i j : ℕ) (h : scsDiag 4 i j) :
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) :=
  YRTAFYH_p17 s i j hs hb (by omega) (by rw [hk]; exact h) (hab i j h)

/-- The `BBs` stabilisation strut (`hexagons.hl STAB_BB`), packaged for the
ARDBZYE/AUEAHEH statements. -/
theorem BB_STAN_p33 (s : ScsV39) (hs : isScsV39 s) (v : ℕ → V3) (i j : ℕ)
    (hbb : BBsV39 s v) (hd : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 s i j) v := STAB_BB s v i j hs hd hbb

/-- The `MMs` stabilisation strut (`XWNHLMD_MM`), packaged. -/
theorem MM_STAN_p33 (s : ScsV39) (hs : isScsV39 s) (hb : scsBasicV39 s)
    {v : ℕ → V3} (i j : ℕ) (h : scsDiag s.k i j)
    (hstab : isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j))
    (hv : v ∈ MMsV39 s) (hd : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 s i j) ≠ ∅ :=
  XWNHLMD_MM_p33 s _ v hs hstab.1 hb hstab.2 rfl hv
    (BB_STAN_p33 s hs v i j (MMs_imp_BBs_p33 hv) hd) (stab_d_eq_p33 s i j ▸ le_refl _)

/-! ### General k = 4 set normalisations -/

theorem STAB_MOD4_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 4) (i j : ℕ) :
    scsStabDiagV39 s (i % 4) (j % 4) = scsStabDiagV39 s i j := by
  rw [← hk]; exact STAB_MOD s i j hs

/-- HOL `SET_STAB_4I1`-family, for a general k = 4 system. -/
theorem SET_STAB_GEN4_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 4) :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 s i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧ x = scsStabDiagV39 s (i % 4) (j % 4)} := by
  ext x
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    refine ⟨i, j, (DIAG_MOD 4 i j (by omega)).mpr hd, ?_⟩
    rw [STAB_MOD4_p33 s hs hk i j]
  · rintro ⟨i, j, hd, rfl⟩
    refine ⟨i, j, (DIAG_MOD 4 i j (by omega)).mp hd, ?_⟩
    rw [STAB_MOD4_p33 s hs hk i j]

/-- HOL `EXPAND_STAB_DIAG_4`, for a general k = 4 system. -/
theorem EXPAND_STAB_DIAG_GEN4_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 4) :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 s (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 s (i + 2) i} := by
  ext x
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    refine ⟨i % 4, Nat.mod_lt _ (by omega), ?_⟩
    rw [hj, ← STAB_MOD4_p33 s hs hk (i % 4 + 2) (i % 4),
      ← STAB_MOD4_p33 s hs hk (i % 4) ((i % 4 + 2) % 4)]
    simp only [Nat.mod_mod]
    rw [STAB_SYM]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, i + 2, by omega, ?_⟩
    rw [STAB_MOD4_p33 s hs hk i (i + 2), STAB_SYM]

/-- HOL `SET_EQ_DIAG_STAB_4I3`-family, for a general k = 4 system. -/
theorem SET_EQ_DIAG_STAB_GEN4_p33 (s : ScsV39) (hs : isScsV39 s) (hb : scsBasicV39 s)
    (hk : s.k = 4) (hab : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab) :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 s i j}
      {scsStabDiagV39 s 0 2, scsStabDiagV39 s 1 3} := by
  have hdiag02 : scsDiag 4 0 2 := by unfold scsDiag; decide
  have hdiag13 : scsDiag 4 1 3 := by unfold scsDiag; decide
  have his : ∀ t ∈ ({scsStabDiagV39 s 0 2, scsStabDiagV39 s 1 3} : Set ScsV39),
      isScsV39 t := by
        intro t ht
        rcases ht with heq | heq
        · subst heq; exact (STAB_SCS_p33 s hs hb hk hab 0 2 hdiag02).1
        · subst heq; exact (STAB_SCS_p33 s hs hb hk hab 1 3 hdiag13).1
  have hEq : {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 s (i + 2) i} =
      ({scsStabDiagV39 s 0 2, scsStabDiagV39 s 1 3} : Set ScsV39) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · exact Or.inl (STAB_SYM s 0 2).symm
      · exact Or.inr (STAB_SYM s 1 3).symm
      · exact Or.inl (by rw [← STAB_MOD4_p33 s hs hk 4 2])
      · exact Or.inr (by rw [← STAB_MOD4_p33 s hs hk 5 3])
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, (show scsStabDiagV39 s 0 2 = scsStabDiagV39 s (0 + 2) 0 from
          STAB_SYM s 0 2)⟩
      · exact ⟨1, by omega, (show scsStabDiagV39 s 1 3 = scsStabDiagV39 s (1 + 2) 1 from
          STAB_SYM s 1 3)⟩
  have hmid : {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
      x = scsStabDiagV39 s (i % 4) (j % 4)} =
      {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 s (i % 4) (j % 4)} := by
    ext x
    constructor
    · rintro ⟨i, j, hd, hx⟩
      have hd' : j % 4 = (i % 4 + 2) % 4 := by
        simpa using (EXPAND_DIAG_4V_p33 (i % 4) (j % 4)).mp hd
      exact ⟨i, j, hd', hx⟩
    · rintro ⟨i, j, hd, hx⟩
      exact ⟨i, j, (EXPAND_DIAG_4V_p33 (i % 4) (j % 4)).mpr (by simpa using hd), hx⟩
  refine FZIOTEF_TRANS _ _ _ ?_ (FZIOTEF_REFL _ his)
  rw [SET_STAB_GEN4_p33 s hs hk, hmid, EXPAND_STAB_DIAG_GEN4_p33 s hs hk, hEq]
  exact FZIOTEF_REFL _ his

/-- The inverse prop-equation arrow for k = 3 systems: `{pe s i} → {s}`.
(`scs_3M1 = scs_prop_equ_v39 (scs_prop_equ_v39 scs_3M1 1) 2` etc.)
Proved modulo `LocalAuto12.PRO_EQU_ID1` / `YXIONXL3`. -/
theorem PRO_EQU_INV_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 3) (i : ℕ) :
    scsArrowV39 {scsPropEquV39 s i} {s} := by
  have hpe : isScsV39 (scsPropEquV39 s i) := PROP_EQU_IS_SCS_p33 hk hs i
  have h := YXIONXL3_p33 (scsPropEquV39 s i) (3 - i % 3) hpe
  rw [← PRO_EQU_ID1_p33 hk hs i] at h
  exact h

/-- NEEDS: `is_scs_v39 scs_3T1` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_3T1_p33 : isScsV39 scs3T1 := sorry

/-- NEEDS: `is_scs_v39 scs_3T4` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_3T4_p33 : isScsV39 scs3T4 := sorry

/-- NEEDS: `is_scs_v39 scs_3T6'` (LocalAuto22 OCBICBY funlist card kit). -/
theorem is_scs_3T6_p33 : isScsV39 scs3T6' := sorry

theorem pe_3M1_arrow_p33 :
    scsArrowV39 {scsPropEquV39 scs3M1 1} {scs3M1} :=
  PRO_EQU_INV_p33 scs3M1 SCS_3M1_IS_SCS K_SCS_3M1 1

theorem pe_3T1_arrow_p33 :
    scsArrowV39 {scsPropEquV39 scs3T1 1} {scs3T1} :=
  PRO_EQU_INV_p33 scs3T1 is_scs_3T1_p33 K_SCS_3T1 1

theorem pe_3T4_arrow_p33 :
    scsArrowV39 {scsPropEquV39 scs3T4 2} {scs3T4} :=
  PRO_EQU_INV_p33 scs3T4 is_scs_3T4_p33 K_SCS_3T4 2

theorem pe_3T6_arrow_p33 :
    scsArrowV39 {scsPropEquV39 scs3T6' 2} {scs3T6'} :=
  PRO_EQU_INV_p33 scs3T6' is_scs_3T6_p33 rfl 2

/-- Arrow padding: `S ⊆ T` with `T` all-`is_scs` gives `S → T`. -/
theorem FZIOTEF_SUBSET_p33 (S T : Set ScsV39) (hsub : S ⊆ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 S T := by
  refine ⟨fun t ht => hisT t ht, ?_⟩
  by_cases hx : ∃ s, s ∈ S ∧ MMsV39 s ≠ ∅
  · obtain ⟨s, hs, hne⟩ := hx
    exact Or.inr ⟨s, hsub hs, hne⟩
  · refine Or.inl fun t ht => ?_
    by_contra hne
    exact hx ⟨t, ht, hne⟩

/-- Combine two arrows landing in the same target set. -/
theorem FZIOTEF_BOTH_p33 (S1 S3 T : Set ScsV39) (h1 : scsArrowV39 S1 T)
    (h3 : scsArrowV39 S3 T) (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 (S1 ∪ S3) T :=
  FZIOTEF_TRANS _ _ _ (FZIOTEF_UNION _ _ _ _ h1 h3)
    (FZIOTEF_SUBSET_p33 (T ∪ T) T (fun a h => Or.elim (Set.mem_union _ _ _ |>.1 h) id id) hisT)

/-- Arrow padding of a singleton into a target set. -/
theorem SING_PAD_p33 (a : ScsV39) (T : Set ScsV39) (ha : a ∈ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 {a} T :=
  FZIOTEF_SUBSET_p33 {a} T (fun t h => by rw [Set.mem_singleton_iff] at h; subst h; exact ha) hisT

/-- `pe scs_3M1 1 → T` for any `is_scs` target `T` containing `scs_3M1`. -/
theorem pe_3M1_pad_p33 {T : Set ScsV39} (ha : scs3M1 ∈ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 {scsPropEquV39 scs3M1 1} T :=
  FZIOTEF_TRANS _ _ _ (pe_3M1_arrow_p33) (SING_PAD_p33 scs3M1 T ha hisT)

/-- `pe scs_3T1 1 → T` for any `is_scs` target `T` containing `scs_3T1`. -/
theorem pe_3T1_pad_p33 {T : Set ScsV39} (ha : scs3T1 ∈ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 {scsPropEquV39 scs3T1 1} T :=
  FZIOTEF_TRANS _ _ _ (pe_3T1_arrow_p33) (SING_PAD_p33 scs3T1 T ha hisT)

/-- `pe scs_3T4 2 → T` for any `is_scs` target `T` containing `scs_3T4`. -/
theorem pe_3T4_pad_p33 {T : Set ScsV39} (ha : scs3T4 ∈ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 {scsPropEquV39 scs3T4 2} T :=
  FZIOTEF_TRANS _ _ _ (pe_3T4_arrow_p33) (SING_PAD_p33 scs3T4 T ha hisT)

/-- `pe scs_3T6' 2 → T` for any `is_scs` target `T` containing `scs_3T6'`. -/
theorem pe_3T6_pad_p33 {T : Set ScsV39} (ha : scs3T6' ∈ T)
    (hisT : ∀ t ∈ T, isScsV39 t) : scsArrowV39 {scsPropEquV39 scs3T6' 2} T :=
  FZIOTEF_TRANS _ _ _ (pe_3T6_arrow_p33) (SING_PAD_p33 scs3T6' T ha hisT)

/-- The `{s} → {y} ∪ stab-set` arrow scaffold: a realisation either has all
diag distances `> cstab` (arrow to `y`) or stabilises some diagonal
(arrow into the stab set). -/
theorem ARROW_SPLIT_p33 (s y : ScsV39) (S : Set ScsV39) (hisy : isScsV39 y)
    (hS : ∀ t ∈ S, isScsV39 t)
    (hy : ∀ v : ℕ → V3, v ∈ MMsV39 s →
      (∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) → MMsV39 y ≠ ∅)
    (hst : ∀ v : ℕ → V3, v ∈ MMsV39 s →
      (∃ i j, scsDiag 4 i j ∧ dist (v i) (v j) ≤ cstab) → ∃ t ∈ S, MMsV39 t ≠ ∅) :
    scsArrowV39 {s} ({y} ∪ S) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases Set.mem_union _ _ _ |>.1 ht with h | h
    · rw [Set.mem_singleton_iff] at h; subst h; exact hisy
    · exact hS t h
  · by_cases hx : (MMsV39 s).Nonempty
    · obtain ⟨v, hv⟩ := hx
      by_cases hd : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)
      · exact Or.inr ⟨y, Set.mem_union_left _ (Set.mem_singleton y), hy v hv hd⟩
      · push_neg at hd
        obtain ⟨i, j, hdiag, hle⟩ := hd
        obtain ⟨t, htS, htne⟩ := hst v hv ⟨i, j, hdiag, hle⟩
        exact Or.inr ⟨t, Set.mem_union_right _ htS, htne⟩
    · refine Or.inl fun t ht => ?_
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact Set.not_nonempty_iff_eq_empty.mp hx

/-! ## Section R: ARDBZYE (ARDBZYE.hl, 81 theorems, source order) -/

/-- HOL `GSXRFWM1` (ARDBZYE.hl:98).  NEEDS: the k = 4 genericity of an
`MMs` realisation (the `RRCWNSJ`-style case bank over the b-table). -/
theorem GSXRFWM1_p33 (s : ScsV39) (v : ℕ → V3) (hs : isScsV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s) (hb : ∀ i, s.b i (i + 1) ≤ cstab) : scsGeneric v := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl GSXRFWM1 (b-edge ≤ cstab ⇒ generic).

/-- HOL `SCS_B_LE_CSTAB` (ARDBZYE.hl:356): the `is_scs_v39` b-edge bound. -/
theorem SCS_B_LE_CSTAB_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 4) (i : ℕ) :
    s.b i (i + 1) ≤ cstab := by
  have h18 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact h18 i (by omega)

/-- HOL `GSXRFWM` (ARDBZYE.hl:366). Proved modulo `GSXRFWM1_p33`. -/
theorem GSXRFWM_p33 (s : ScsV39) (v : ℕ → V3) (hs : isScsV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s) : scsGeneric v :=
  GSXRFWM1_p33 s v hs hk hv fun i => SCS_B_LE_CSTAB_p33 s hs hk i

/-- HOL `PSORT_5_EXPLICIT` (ARDBZYE.hl:376); the full 57-clause table. -/
theorem PSORT_5_EXPLICIT_p33 :
    psort 5 (0, 0) = (0, 0) ∧ psort 5 (1, 1) = (1, 1) ∧ psort 5 (2, 2) = (2, 2) ∧
    psort 5 (3, 3) = (3, 3) ∧ psort 5 (4, 4) = (4, 4) ∧ psort 5 (0, 1) = (0, 1) ∧
    psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧ psort 5 (0, 4) = (0, 4) ∧
    psort 5 (1, 0) = (0, 1) ∧ psort 5 (1, 2) = (1, 2) ∧ psort 5 (1, 3) = (1, 3) ∧
    psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 0) = (0, 2) ∧ psort 5 (2, 1) = (1, 2) ∧
    psort 5 (2, 3) = (2, 3) ∧ psort 5 (2, 4) = (2, 4) ∧ psort 5 (3, 0) = (0, 3) ∧
    psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧ psort 5 (3, 4) = (3, 4) ∧
    psort 5 (4, 0) = (0, 4) ∧ psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
    psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 5) = (0, 4) ∧ psort 5 (3, 5) = (0, 3) ∧
    psort 5 (2, 5) = (0, 2) ∧ psort 5 (1, 5) = (0, 1) ∧ psort 5 (5, 1) = (0, 1) ∧
    psort 5 (5, 2) = (0, 2) ∧ psort 5 (5, 3) = (0, 3) ∧ psort 5 (5, 4) = (0, 4) ∧
    psort 5 (5, 5) = (0, 0) ∧ psort 5 (5, 6) = (0, 1) ∧ psort 5 (5, 7) = (0, 2) ∧
    psort 5 (4, 6) = (1, 4) ∧ psort 5 (6, 4) = (1, 4) ∧ psort 5 (6, 5) = (0, 1) ∧
    psort 5 (6, 7) = (1, 2) ∧ psort 5 (7, 5) = (0, 2) ∧ psort 5 (7, 6) = (1, 2) ∧
    psort 5 (7, 7) = (2, 2) ∧ psort 5 (6, 6) = (1, 1) ∧ psort 4 (3, 4) = (0, 3) ∧
    psort 3 (2, 0) = (0, 2) ∧ psort 3 (2, 1) = (1, 2) ∧ psort 3 (1, 0) = (0, 1) ∧
    psort 4 (0, 0) = (0, 0) ∧ psort 4 (1, 1) = (1, 1) ∧ psort 4 (2, 2) = (2, 2) ∧
    psort 4 (3, 3) = (3, 3) ∧ psort 4 (4, 3) = (0, 3) ∧ psort 4 (4, 4) = (0, 0) ∧
    psort 4 (0, 2) = (0, 2) ∧ psort 4 (4, 5) = (0, 1) ∧ psort 4 (5, 4) = (0, 1) ∧
    psort 4 (5, 5) = (1, 1) := by
  repeat' first
    | constructor
    | decide

/-- HOL `SCS_4I2_IS_SCS` (ARDBZYE.hl:454). -/
theorem SCS_4I2_IS_SCS_p33 : isScsV39 scs4I2 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4I2_p22 (funlist card kit).

/-- HOL `SCS_4I1_IS_SCS` (ARDBZYE.hl:547). -/
theorem SCS_4I1_IS_SCS_p33 : isScsV39 scs4I1 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4I1_p22 (cs_adj card kit).

/-- HOL `SCS_4T1_IS_SCS` (ARDBZYE.hl:592). -/
theorem SCS_4T1_IS_SCS_p33 : isScsV39 scs4T1 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4T1_p22 (cs_adj card kit).

/-- HOL `SCS_4T2_IS_SCS` (ARDBZYE.hl:684). -/
theorem SCS_4T2_IS_SCS_p33 : isScsV39 scs4T2 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4T2_p22 (cs_adj card kit).

/-- HOL `SCS_4T4_IS_SCS` (ARDBZYE.hl:778). -/
theorem SCS_4T4_IS_SCS_p33 : isScsV39 scs4T4 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4T4_p22 (funlist card kit).

/-- HOL `SCS_4T5_IS_SCS` (ARDBZYE.hl:886). -/
theorem SCS_4T5_IS_SCS_p33 : isScsV39 scs4T5 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4T5_p22 (funlist card kit).

/-- HOL `SCS_4I3_IS_SCS` (ARDBZYE.hl:995). -/
theorem SCS_4I3_IS_SCS_p33 : isScsV39 scs4I3 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_4I3_p22 (funlist card kit).

/-- HOL `SCS_3T3_IS_SCS` (ARDBZYE.hl:1104). -/
theorem SCS_3T3_IS_SCS_p33 : isScsV39 scs3T3 := sorry
  -- DISCHARGES: NEEDS LocalAuto22.is_scs_3T3_p22 (funlist card kit).

/-- HOL `SCS_4I2_BASIC` (ARDBZYE.hl:1200). -/
theorem SCS_4I2_BASIC_p33 : scsBasicV39 scs4I2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4I2` (ARDBZYE.hl:1203). -/
theorem K_SCS_4I2_p33 : scs4I2.k = 4 := rfl

/-- HOL `SCS_4I1_BASIC` (ARDBZYE.hl:1206). -/
theorem SCS_4I1_BASIC_p33 : scsBasicV39 scs4I1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4I1` (ARDBZYE.hl:1209). -/
theorem K_SCS_4I1_p33 : scs4I1.k = 4 := rfl

/-- HOL `J_SCS_4I1` (ARDBZYE.hl:1212). -/
theorem J_SCS_4I1_p33 (i i1 j : ℕ) : (scsPropEquV39 scs4I1 i).J i1 j = False := rfl

/-- HOL `SCS_4T1_BASIC` (ARDBZYE.hl:1216). -/
theorem SCS_4T1_BASIC_p33 : scsBasicV39 scs4T1 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4T1` (ARDBZYE.hl:1219). -/
theorem K_SCS_4T1_p33 : scs4T1.k = 4 := rfl

/-- HOL `SCS_4T2_BASIC` (ARDBZYE.hl:1222). -/
theorem SCS_4T2_BASIC_p33 : scsBasicV39 scs4T2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4T2` (ARDBZYE.hl:1225). -/
theorem K_SCS_4T2_p33 : scs4T2.k = 4 := rfl

/-- HOL `SCS_4T4_BASIC` (ARDBZYE.hl:1228). -/
theorem SCS_4T4_BASIC_p33 : scsBasicV39 scs4T4 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4T4` (ARDBZYE.hl:1231). -/
theorem K_SCS_4T4_p33 : scs4T4.k = 4 := rfl

/-- HOL `J_SCS_3T4_1` (ARDBZYE.hl:1234). -/
theorem J_SCS_3T4_1_p33 (i1 j : ℕ) : scs3T4.J i1 j = False := rfl

/-- HOL `SCS_4I3_BASIC` (ARDBZYE.hl:1238). -/
theorem SCS_4I3_BASIC_p33 : scsBasicV39 scs4I3 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4I3` (ARDBZYE.hl:1241). -/
theorem K_SCS_4I3_p33 : scs4I3.k = 4 := rfl

/-- HOL `SCS_3T3_BASIC` (ARDBZYE.hl:1244). -/
theorem SCS_3T3_BASIC_p33 : scsBasicV39 scs3T3 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_3T3` (ARDBZYE.hl:1247). -/
theorem K_SCS_3T3_p33 : scs3T3.k = 3 := rfl

/-- HOL `J_SCS_3T3` (ARDBZYE.hl:1250). -/
theorem J_SCS_3T3_p33 (i i1 j : ℕ) : (scsPropEquV39 scs3T3 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T3_1` (ARDBZYE.hl:1253). -/
theorem J_SCS_3T3_1_p33 (i1 j : ℕ) : scs3T3.J i1 j = False := rfl

/-- HOL `SCS_4T5_BASIC` (ARDBZYE.hl:1258). -/
theorem SCS_4T5_BASIC_p33 : scsBasicV39 scs4T5 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `K_SCS_4T5` (ARDBZYE.hl:1261). -/
theorem K_SCS_4T5_p33 : scs4T5.k = 4 := rfl

/-- HOL `B_LE_CSTAB_SCS_4I2` (ARDBZYE.hl:1264). -/
theorem B_LE_CSTAB_SCS_4I2_p33 :
    (∀ i, scs4I2.b i (i + 1) ≤ cstab) ∧
      (∀ i, scs4I2.a i (i + 1) = 2 ∧ scs4I2.b i (i + 1) ≤ 2 * h0) := by
  refine ⟨fun i => ?_, fun i => ⟨a_edge_4I2_p33 i, ?_⟩⟩
  · rw [b_edge_4I2_p33]; exact two_h0_le_cstab_p20
  · rw [b_edge_4I2_p33]

/-- HOL `B_LE_CSTAB_SCS_4I1` (ARDBZYE.hl:1273). -/
theorem B_LE_CSTAB_SCS_4I1_p33 (i : ℕ) : scs4I1.b i (i + 1) ≤ cstab := by
  rw [b_edge_4I1_p33]; exact two_h0_le_cstab_p20

/-- HOL `h0_LT_B_SCS_4I2` (ARDBZYE.hl:1282). -/
theorem h0_LT_B_SCS_4I2_p33 :
    (∀ i j, scsDiag 4 i j → 4 * h0 < scs4I2.b i j) ∧
      (∀ i j, scsDiag 4 i j → scs4I2.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · rw [b_diag_4I2_p33 i j hd]; exact four_h0_lt_six_p20
  · rw [a_diag_4I2_p33 i j hd]; norm_num [cstab]

/-- HOL `h0_LT_B_SCS_4I1` (ARDBZYE.hl:1291). -/
theorem h0_LT_B_SCS_4I1_p33 :
    (∀ i j, scsDiag 4 i j → 4 * h0 < scs4I1.b i j) ∧
      (∀ i j, scsDiag 4 i j → scs4I1.a i j ≤ cstab) := by
  constructor <;> intro i j hd
  · rw [b_diag_4I1_p33 i j hd]; exact four_h0_lt_six_p20
  · rw [a_diag_4I1_p33 i j hd]; exact two_h0_le_cstab_p20

/-- HOL `SCS_4I2_GENERIC` (ARDBZYE.hl:1305). Proved modulo `GSXRFWM_p33`. -/
theorem SCS_4I2_GENERIC_p33 (v : ℕ → V3) (hv : v ∈ MMsV39 scs4I2) : scsGeneric v :=
  GSXRFWM_p33 scs4I2 v SCS_4I2_IS_SCS_p33 K_SCS_4I2_p33 hv

/-- HOL `A_LT_B_4I2` (ARDBZYE.hl:1313). -/
theorem A_LT_B_4I2_p33 :
    (∀ i, 2 < scs4I2.b i (i + 1)) ∧ (∀ i, scs4I2.a i (i + 1) = 2) := by
  refine ⟨fun i => ?_, fun i => a_edge_4I2_p33 i⟩
  rw [b_edge_4I2_p33]; exact two_lt_two_h0_p20

/-- HOL `A_LT_B_4I1` (ARDBZYE.hl:1321). -/
theorem A_LT_B_4I1_p33 :
    (∀ i, 2 < scs4I1.b i (i + 1)) ∧ (∀ i, scs4I1.a i (i + 1) = 2) := by
  refine ⟨fun i => ?_, fun i => a_edge_4I1_p33 i⟩
  rw [b_edge_4I1_p33]; exact two_lt_two_h0_p20

/-- HOL `SCS_M_4I2` (ARDBZYE.hl:1337). -/
theorem SCS_M_4I2_p33 : scsM scs4I2 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 (fun i hi => ?_)
  simp only [scsM, Set.mem_setOf_eq] at hi
  rw [b_edge_4I2_p33, a_edge_4I2_p33] at hi
  rcases hi.2 with h | h
  · exact absurd h (lt_irrefl _)
  · exact absurd h (by norm_num)

/-- HOL `CARD_SCS_M_4I2` (ARDBZYE.hl:1330). -/
theorem CARD_SCS_M_4I2_p33 : Set.ncard (scsM scs4I2) ≤ 1 := by
  rw [SCS_M_4I2_p33]; simp

/-- HOL `SCS_M_4I1` (ARDBZYE.hl:1349). -/
theorem SCS_M_4I1_p33 : scsM scs4I1 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 (fun i hi => ?_)
  simp only [scsM, Set.mem_setOf_eq] at hi
  rw [b_edge_4I1_p33, a_edge_4I1_p33] at hi
  rcases hi.2 with h | h
  · exact absurd h (lt_irrefl _)
  · exact absurd h (by norm_num)

/-- HOL `CARD_SCS_M_4I1` (ARDBZYE.hl:1343). -/
theorem CARD_SCS_M_4I1_p33 : Set.ncard (scsM scs4I1) ≤ 1 := by
  rw [SCS_M_4I1_p33]; simp

/-- HOL `SCS_4I2_IMP_SCS_4T1` (ARDBZYE.hl:1357).  NEEDS: the terminal
ear-diagram case bank (consumes `ear_acute_p33`/`EDGE_EQ_2_4I2_*`). -/
theorem SCS_4I2_IMP_SCS_4T1_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
    (hv : v ∈ MMsV39 scs4I2)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4T1 ≠ ∅ := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SCS_4I2_IMP_SCS_4T1 (main_nonlinear_terminal
  -- case bank + 3≤ diag + straightness calculus).

/-- HOL `SCS_DIAG_4_CASES` (ARDBZYE.hl:1439). -/
theorem SCS_DIAG_4_CASES_p33 (i j : ℕ) :
    scsDiag 4 i j ↔ (i % 4 = 0 ∧ j % 4 = 2) ∨ (i % 4 = 1 ∧ j % 4 = 3) ∨
      (j % 4 = 0 ∧ i % 4 = 2) ∨ (j % 4 = 1 ∧ i % 4 = 3) := by
  constructor
  · intro h
    rcases diag_pair_cases_p33 i j h with ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩
    · exact Or.inl ⟨r1, r2⟩
    · exact Or.inr (Or.inl ⟨r1, r2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨r2, r1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨r2, r1⟩))
  · rintro (⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩ | ⟨r1, r2⟩)
    <;> rw [scsDiag] <;> omega

/-- HOL `WLOG_4_BB_SCS` (ARDBZYE.hl:1455).  NEEDS: the diag case split +
point symmetry transfer of `P` along the `BBs` realisation. -/
theorem WLOG_4_BB_SCS_p33 (s : ScsV39) (v : ℕ → V3) (i j : ℕ) (P : V3 → V3 → Prop)
    (hs : isScsV39 s) (hbb : BBsV39 s v) (hk : s.k = 4) (hd : scsDiag 4 i j)
    (hsym : ∀ i' j', P (v i') (v j') ↔ P (v j') (v i'))
    (hP : P (v i) (v j)) : P (v 0) (v 2) ∨ P (v 1) (v 3) := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl WLOG_4_BB_SCS (mod-4 residue cases).

/-- HOL `WLOG_4_BB_SCS_DIAG` (ARDBZYE.hl:1482).  NEEDS: as
`WLOG_4_BB_SCS_p33`, with the two swap symmetries of the 4-ary `P`. -/
theorem WLOG_4_BB_SCS_DIAG_p33 (s : ScsV39) (v : ℕ → V3) (i j : ℕ)
    (P : V3 → V3 → V3 → V3 → Prop) (hs : isScsV39 s) (hbb : BBsV39 s v)
    (hk : s.k = 4) (hd : scsDiag 4 i j)
    (hsym1 : ∀ a b c d : ℕ, P (v a) (v b) (v c) (v d) ↔ P (v b) (v a) (v c) (v d))
    (hsym2 : ∀ a b c d : ℕ, P (v a) (v b) (v c) (v d) ↔ P (v a) (v b) (v d) (v c))
    (hP : P (v i) (v j) (v (i + 1)) (v (j + 1))) :
    P (v 0) (v 2) (v 1) (v 3) ∨ P (v 1) (v 3) (v 0) (v 2) := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl WLOG_4_BB_SCS_DIAG.

/-- HOL `DIST_DIAG_2_CASES_EQ_3` (ARDBZYE.hl:1536).  NEEDS: the diag case
bank over the two parallel diagonals of the `4I2` realisation. -/
theorem DIST_DIAG_2_CASES_EQ_3_p33 (v : ℕ → V3) (i j : ℕ) (hv : v ∈ MMsV39 scs4I2)
    (hd : scsDiag 4 i j) (h1 : dist (v i) (v j) = 3)
    (h2 : dist (v (i + 1)) (v (j + 1)) = 3) :
    dist (v 0) (v 2) = 3 ∧ dist (v 1) (v 3) = 3 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl DIST_DIAG_2_CASES_EQ_3.

/-- HOL `ASSUME_MIN_DIAG` (ARDBZYE.hl:1550).  NEEDS: the min-diag WLOG
selection over the two diagonal classes. -/
theorem ASSUME_MIN_DIAG_p33 (v : ℕ → V3)
    (h : ∀ i j, v ∈ MMsV39 scs4I2 → scsDiag 4 i j → dist (v i) (v j) ≤ cstab →
      dist (v i) (v j) ≤ dist (v (i + 1)) (v (j + 1)) →
      MMsV39 scs4T1 ≠ ∅ ∨ MMsV39 scs4T2 ≠ ∅)
    (i j : ℕ) (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j)
    (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 scs4T1 ≠ ∅ ∨ MMsV39 scs4T2 ≠ ∅ := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl ASSUME_MIN_DIAG.

/-- HOL `SCS_4I2_3_LE_A` (ARDBZYE.hl:1676): the a-diag value of `4I2` is 3. -/
theorem SCS_4I2_3_LE_A_p33 (v : ℕ → V3) (hbb : BBsV39 scs4I2 v) (i j : ℕ)
    (hd : scsDiag 4 i j) : 3 ≤ dist (v i) (v j) := by
  have h := (hbb.2.2.1 i j).1
  rw [a_diag_4I2_p33 i j hd] at h
  exact h

/-- HOL `SCS_DIAG_ADD1` (ARDBZYE.hl:1730). -/
theorem SCS_DIAG_ADD1_p33 (i j : ℕ) (h : scsDiag 4 i j) : scsDiag 4 (i + 1) (j + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  constructor <;> omega

/-- HOL `ear_acute` (ARDBZYE.hl:1751).  NEEDS: `main_nonlinear_terminal_v11`
(y-row 2..2h0, y5 ≥ 3 ⇒ dih_y < π/2). -/
theorem ear_acute_p33 (_hmn : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 →
      2 ≤ y3 → y3 ≤ 2 * h0 → 2 ≤ y4 → y4 ≤ 2 * h0 → 2 ≤ y6 → y6 ≤ 2 * h0 →
      3 ≤ y5 → 0 < upsX (y1 ^ 2) (y3 ^ 2) (y5 ^ 2) →
      dihY_p18 y1 y2 y3 y4 y5 y6 < Real.pi / 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl ear_acute (terminal_nonlinear instance).

/-- HOL `SCS_DIAG_4_ADD2` (ARDBZYE.hl:1787). -/
theorem SCS_DIAG_4_ADD2_p33 (i : ℕ) : scsDiag 4 (i + 1) (i + 3) :=
  ⟨by omega, by omega, by omega⟩

/-- HOL `SCS_DIAG_4_ADD0` (ARDBZYE.hl:1792). -/
theorem SCS_DIAG_4_ADD0_p33 (i : ℕ) : scsDiag 4 i (i + 2) :=
  ⟨by omega, by omega, by omega⟩

/-- HOL `EDGE_4I2_LE_2H0` (ARDBZYE.hl:1801). -/
theorem EDGE_4I2_LE_2H0_p33 (v : ℕ → V3) (hbb : BBsV39 scs4I2 v) (i : ℕ) :
    dist (v i) (v (i + 1)) ≤ 2 * h0 ∧ 2 ≤ dist (v i) (v (i + 1)) := by
  have hb := (hbb.2.2.1 i (i + 1)).2
  have ha := (hbb.2.2.1 i (i + 1)).1
  rw [b_edge_4I2_p33] at hb
  rw [a_edge_4I2_p33] at ha
  exact ⟨hb, ha⟩

/-- HOL `SCS_4I2_STRAIGHT` (ARDBZYE.hl:1813).  NEEDS: `ear_acute_p33` via
the y-coordinates of the `4I2` realisation. -/
theorem SCS_4I2_STRAIGHT_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i : ℕ)
    (hv : v ∈ MMsV39 scs4I2) : azim 0 (v i) (v (i + 1)) (v (i + 3)) < Real.pi := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SCS_4I2_STRAIGHT.

/-- HOL `SCS_4I2_STRAIGHT_ALL` (ARDBZYE.hl:1919).  NEEDS: as
`SCS_4I2_STRAIGHT_p33`, instantiated at the four residues. -/
theorem SCS_4I2_STRAIGHT_ALL_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
    (hv : v ∈ MMsV39 scs4I2) :
    azim 0 (v 0) (v 1) (v 3) < Real.pi ∧ azim 0 (v 1) (v 2) (v 0) < Real.pi ∧
      azim 0 (v 2) (v 3) (v 1) < Real.pi ∧ azim 0 (v 3) (v 0) (v 2) < Real.pi := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SCS_4I2_STRAIGHT_ALL.

/-- HOL `EDGE_EQ_2_4I2` (ARDBZYE.hl:1965).  NEEDS: the terminal case bank. -/
theorem EDGE_EQ_2_4I2_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i j : ℕ)
    (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j) (h3a : 3 ≤ dist (v i) (v j))
    (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    dist (v (i + 1)) (v (i + 2)) = 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EDGE_EQ_2_4I2.

/-- HOL `EXPAND_DIAG_4_DIST` (ARDBZYE.hl:2084).  NEEDS: as `EDGE_EQ_2_4I2_p33`. -/
theorem EXPAND_DIAG_4_DIST_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
    (i j : ℕ) (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j)
    (h3a : 3 ≤ dist (v i) (v j)) (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    3 ≤ dist (v i) (v (i + 2)) ∧ 3 < dist (v (i + 1)) (v (i + 3)) := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EXPAND_DIAG_4_DIST.

/-- HOL `B_LE_CSTAB_SCS_4I2_prime` (ARDBZYE.hl:2107). -/
theorem B_LE_CSTAB_SCS_4I2_prime_p33 (i : ℕ) :
    scs4I2.a (i + 1) (1 * 4 + i) = 2 ∧ scs4I2.b (i + 1) (1 * 4 + i) ≤ 2 * h0 := by
  have hneg : ¬((i + 1) % 4 = (1 * 4 + i) % 4) := by omega
  have hpos : (1 * 4 + i) % 4 = ((i + 1) + 1) % 4 ∨
      (1 * 4 + i + 1) % 4 = (i + 1) % 4 := by omega
  refine ⟨?_, ?_⟩
  · simp only [scs4I2, mkUnadornedV39, csAdj, if_neg hneg, if_pos hpos]
  · simp only [scs4I2, mkUnadornedV39, csAdj, if_neg hneg, if_pos hpos]
    exact le_refl _

/-- HOL `EDGE_EQ_2_4I2_1` (ARDBZYE.hl:2118).  NEEDS: as `EDGE_EQ_2_4I2_p33`. -/
theorem EDGE_EQ_2_4I2_1_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i j : ℕ)
    (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j) (h3a : 3 ≤ dist (v i) (v j))
    (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    dist (v i) (v (i + 1)) = 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EDGE_EQ_2_4I2_1.

/-- HOL `EDGE_EQ_2_4I2_2` (ARDBZYE.hl:2235).  NEEDS: as `EDGE_EQ_2_4I2_p33`. -/
theorem EDGE_EQ_2_4I2_2_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i j : ℕ)
    (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j) (h3a : 3 ≤ dist (v i) (v j))
    (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    dist (v (i + 2)) (v (i + 3)) = 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EDGE_EQ_2_4I2_2.

/-- HOL `EDGE_EQ_2_4I2_3` (ARDBZYE.hl:2256).  NEEDS: as `EDGE_EQ_2_4I2_p33`. -/
theorem EDGE_EQ_2_4I2_3_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i j : ℕ)
    (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j) (h3a : 3 ≤ dist (v i) (v j))
    (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    dist (v i) (v (i + 3)) = 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EDGE_EQ_2_4I2_3.

/-- HOL `EDGE_EQ_2_4I2_ALL` (ARDBZYE.hl:2282).  NEEDS: as `EDGE_EQ_2_4I2_p33`. -/
theorem EDGE_EQ_2_4I2_ALL_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3) (i j : ℕ)
    (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j) (h3a : 3 ≤ dist (v i) (v j))
    (h3b : 3 < dist (v (i + 1)) (v (j + 1))) :
    ∀ i', dist (v i') (v (i' + 1)) = 2 := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EDGE_EQ_2_4I2_ALL.

/-- HOL `MM_4I2_IMP_4T2_4T1` (ARDBZYE.hl:2339).  NEEDS: the terminal
min-diag case bank. -/
theorem MM_4I2_IMP_4T2_4T1_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
    (i j : ℕ) (hv : v ∈ MMsV39 scs4I2) (hd : scsDiag 4 i j)
    (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 scs4T1 ≠ ∅ ∨ MMsV39 scs4T2 ≠ ∅ := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl MM_4I2_IMP_4T2_4T1.

/-- HOL `ARDBZYE` (ARDBZYE.hl:2514), the master `4I2` arrow.  NEEDS:
`SCS_4I2_IMP_SCS_4T1_p33` + `MM_4I2_IMP_4T2_4T1_p33` assembly. -/
theorem ARDBZYE_p33 (_hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4I2} {scs4T1, scs4T2} := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl ARDBZYE.

/-- HOL `SCS_4I1_IMP_SCS_4I2` (ARDBZYE.hl:2575).  NEEDS: the terminal case
bank (the 4I1 b-table dominates 4I2's away from the diagonals). -/
theorem SCS_4I1_IMP_SCS_4I2_p33 (_hmn : main_nonlinear_terminal_v11) (v : ℕ → V3)
    (hv : v ∈ MMsV39 scs4I1)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4I2 ≠ ∅ := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SCS_4I1_IMP_SCS_4I2.

/-- HOL `SCS_4I1_STAB_DIAG` (ARDBZYE.hl:2642). -/
theorem SCS_4I1_STAB_DIAG_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4I1 v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4I1 i j) v :=
  BB_STAN_p33 scs4I1 SCS_4I1_IS_SCS_p33 v i j hbb hc

/-- HOL `STAB_4I1_SCS` (ARDBZYE.hl:2679). -/
theorem STAB_4I1_SCS_p33 (i j : ℕ) (h : scsDiag scs4I1.k i j) :
    isScsV39 (scsStabDiagV39 scs4I1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs4I1 i j) :=
  STAB_SCS_p33 scs4I1 SCS_4I1_IS_SCS_p33 SCS_4I1_BASIC_p33 K_SCS_4I1_p33
    (fun i' j' hd => by rw [a_diag_4I1_p33 i' j' hd]; exact two_h0_le_cstab_p20) i j
    (show scsDiag 4 i j from h)

/-- HOL `MM_4I1_IMP_STAB_4I1` (ARDBZYE.hl:2689). -/
theorem MM_4I1_IMP_STAB_4I1_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4I1)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4I1 i j) ≠ ∅ :=
  MM_STAN_p33 scs4I1 SCS_4I1_IS_SCS_p33 SCS_4I1_BASIC_p33 i j
    (show scsDiag scs4I1.k i j from hd) (STAB_4I1_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4I1_ARROW_SCS_4I2_STAB_4I1` (ARDBZYE.hl:2707).  NEEDS:
`SCS_4I1_IMP_SCS_4I2_p33` in the all-diags-open branch. -/
theorem SCS_4I1_ARROW_SCS_4I2_STAB_4I1_p33 (_hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4I1}
      ({scs4I2} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I1 i j}) := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SCS_4I1_ARROW_SCS_4I2_STAB_4I1.

/-- HOL `SET_STAB_4I1` (ARDBZYE.hl:2768). -/
theorem SET_STAB_4I1_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I1 i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4I1 (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4I1 SCS_4I1_IS_SCS_p33 K_SCS_4I1_p33

/-- HOL `EXPAND_STAB_DIAG_4` (ARDBZYE.hl:2796). -/
theorem EXPAND_STAB_DIAG_4_p33 (s : ScsV39) (hs : isScsV39 s) (hk : s.k = 4) :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 s (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 s (i + 2) i} :=
  EXPAND_STAB_DIAG_GEN4_p33 s hs hk

/-- HOL `EXPAND_STAB_DIAG_4I1` (ARDBZYE.hl:2818). -/
theorem EXPAND_STAB_DIAG_4I1_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4I1 (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4I1 (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4I1 SCS_4I1_IS_SCS_p33 K_SCS_4I1_p33

/-- HOL `h0_EQ_B_SCS_4I1` (ARDBZYE.hl:2826). -/
theorem h0_EQ_B_SCS_4I1_p33 :
    (∀ i j, scsDiag 4 i j → scs4I1.b i j = 6) ∧
      (∀ i j, scsDiag 4 i j → scs4I1.a i j = 2 * h0) := by
  constructor <;> intro i j hd
  · rw [b_diag_4I1_p33 i j hd]
  · rw [a_diag_4I1_p33 i j hd]

/-- HOL `EQ_DIAG_STAB_4I1_02` (ARDBZYE.hl:2835).  NEEDS: the dsv/BB-minimum
transfer between the two diagonal stabilisations of `4I1` (b-tables
cstab/6 swapped at the two diag classes; a-tables agree). -/
theorem EQ_DIAG_STAB_4I1_02_p33 (i : ℕ) :
    scsArrowV39 {scsStabDiagV39 scs4I1 (i + 2) i} {scsStabDiagV39 scs4I1 0 2} := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl EQ_DIAG_STAB_4I1_02.

/-- HOL `SET_EQ_DIAG_STAB_4I1_02` (ARDBZYE.hl:2860).  NEEDS:
`EQ_DIAG_STAB_4I1_02_p33` across the four residues. -/
theorem SET_EQ_DIAG_STAB_4I1_02_p33 :
    scsArrowV39 {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4I1 (i + 2) i}
      {scsStabDiagV39 scs4I1 0 2} := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SET_EQ_DIAG_STAB_4I1_02.

/-- HOL `SET_EQ_DIAG_STAB_4I1` (ARDBZYE.hl:2875).  NEEDS:
`SET_EQ_DIAG_STAB_4I1_02_p33` + the set normalisations. -/
theorem SET_EQ_DIAG_STAB_4I1_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I1 i j}
      {scsStabDiagV39 scs4I1 0 2} := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl SET_EQ_DIAG_STAB_4I1.

/-- HOL `FYSSVEV` (ARDBZYE.hl:2881).  NEEDS:
`SCS_4I1_ARROW_SCS_4I2_STAB_4I1_p33` + `SET_EQ_DIAG_STAB_4I1_p33`. -/
theorem FYSSVEV_p33 (_hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2} := sorry
  -- DISCHARGES: NEEDS ARDBZYE.hl FYSSVEV.

/-! ## Section A: AUEAHEH (AUEAHEH.hl, 101 theorems, source order) -/

/-- HOL `SCS_DIAG_SCS_4I1_02` (AUEAHEH.hl:101). -/
theorem SCS_DIAG_SCS_4I1_02_p33 : scsDiag scs4I1.k 0 2 := by
  rw [K_SCS_4I1_p33]; unfold scsDiag; decide

/-- HOL `SCS_4I1_SLICE_02` (AUEAHEH.hl:107): the LKGRQUI half-slice of
`stab 4I1 0 2` at `(0, 2)`.  NEEDS: the half-slice/prop-equ table identity
(the `scs_half_slice_v39` fold at `k' = 3` against `scs_prop_equ_v39
scs_3M1 1`, a 3×3 mod-case check plus J/D collars). -/
theorem SCS_4I1_SLICE_02_p33 :
    scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scsPropEquV39 scs3M1 1} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4I1_SLICE_02 (slice table identity).

/-- HOL `AUEAHEH` (AUEAHEH.hl:245). Proved modulo `SCS_4I1_SLICE_02_p33`,
via `PRO_EQU_ID1_p33`/`YXIONXL3_p33` (`3M1 = pe (pe 3M1 1) 2`). -/
theorem AUEAHEH_p33 :
    scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1} :=
  FZIOTEF_TRANS _ _ _ SCS_4I1_SLICE_02_p33 (pe_3M1_arrow_p33)

/-- HOL `BB_4I3_IMP_4T4` (AUEAHEH.hl:258).  NEEDS: the pointwise a/b-table
comparison of `stab 4I3 1 3` against `scs_4T4` (they agree off the diag
classes; the diag entries transfer via `a = √8 ≤ cstab`). -/
theorem BB_4I3_IMP_4T4_p33 (v : ℕ → V3)
    (hbb : BBsV39 (scsStabDiagV39 scs4I3 1 3) v) : BBsV39 scs4T4 v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4I3_IMP_4T4 (funlist table comparison).

/-- HOL `STAB_4I3_SCS` (AUEAHEH.hl:274). -/
theorem STAB_4I3_SCS_p33 (i j : ℕ) (h : scsDiag scs4I3.k i j) :
    isScsV39 (scsStabDiagV39 scs4I3 i j) ∧ scsBasicV39 (scsStabDiagV39 scs4I3 i j) :=
  STAB_SCS_p33 scs4I3 SCS_4I3_IS_SCS_p33 SCS_4I3_BASIC_p33 K_SCS_4I3_p33
    (fun i' j' hd => by rw [a_diag_4I3_p33 i' j' hd]; exact sqrt8_LE_CSTAB) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M2_SCS` (AUEAHEH.hl:285). -/
theorem STAB_4M2_SCS_p33 (i j : ℕ) (h : scsDiag scs4M2.k i j) :
    isScsV39 (scsStabDiagV39 scs4M2 i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M2 i j) :=
  STAB_SCS_p33 scs4M2 SCS_4M2_IS_SCS SCS_4M2_BASIC K_SCS_4M2
    (fun i' j' hd => by rw [a_diag_4M2_p33 i' j' hd]; exact two_h0_le_cstab_p20) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M3_SCS` (AUEAHEH.hl:297). -/
theorem STAB_4M3_SCS_p33 (i j : ℕ) (h : scsDiag scs4M3'.k i j) :
    isScsV39 (scsStabDiagV39 scs4M3' i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M3' i j) :=
  STAB_SCS_p33 scs4M3' is_scs_4M3_p33 SCS_4M3_BASIC_p33 K_SCS_4M3_p33
    (fun i' j' hd => by rw [a_diag_4M3_p33 i' j' hd]; exact sqrt8_LE_CSTAB) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M4_SCS` (AUEAHEH.hl:309). -/
theorem STAB_4M4_SCS_p33 (i j : ℕ) (h : scsDiag scs4M4'.k i j) :
    isScsV39 (scsStabDiagV39 scs4M4' i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M4' i j) :=
  STAB_SCS_p33 scs4M4' is_scs_4M4_p33 SCS_4M4_BASIC_p33 K_SCS_4M4_p33
    (fun i' j' hd => by rw [a_diag_4M4_p33 i' j' hd]; exact two_h0_le_cstab_p20) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M5_SCS` (AUEAHEH.hl:323). -/
theorem STAB_4M5_SCS_p33 (i j : ℕ) (h : scsDiag scs4M5'.k i j) :
    isScsV39 (scsStabDiagV39 scs4M5' i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M5' i j) :=
  STAB_SCS_p33 scs4M5' is_scs_4M5_p33 SCS_4M5_BASIC_p33 K_SCS_4M5_p33
    (fun i' j' hd => by rw [a_diag_4M5_p33 i' j' hd]; exact two_h0_le_cstab_p20) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M6_SCS` (AUEAHEH.hl:337). -/
theorem STAB_4M6_SCS_p33 (i j : ℕ) (h : scsDiag scs4M6'.k i j) :
    isScsV39 (scsStabDiagV39 scs4M6' i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M6' i j) :=
  STAB_SCS_p33 scs4M6' is_scs_4M6_p33 SCS_4M6_BASIC K_SCS_4M6
    (fun i' j' hd => by rw [a_diag_4M6_p33 i' j' hd]) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M7_SCS` (AUEAHEH.hl:350). -/
theorem STAB_4M7_SCS_p33 (i j : ℕ) (h : scsDiag scs4M7.k i j) :
    isScsV39 (scsStabDiagV39 scs4M7 i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M7 i j) :=
  STAB_SCS_p33 scs4M7 is_scs_4M7_p33 SCS_4M7_BASIC_p33 K_SCS_4M7_p33
    (fun i' j' hd => by rw [a_diag_4M7_p33 i' j' hd]) i j
    (show scsDiag 4 i j from h)

/-- HOL `STAB_4M8_SCS` (AUEAHEH.hl:363). -/
theorem STAB_4M8_SCS_p33 (i j : ℕ) (h : scsDiag scs4M8.k i j) :
    isScsV39 (scsStabDiagV39 scs4M8 i j) ∧ scsBasicV39 (scsStabDiagV39 scs4M8 i j) :=
  STAB_SCS_p33 scs4M8 is_scs_4M8_p33 SCS_4M8_BASIC_p33 K_SCS_4M8_p33
    (fun i' j' hd => by rw [a_diag_4M8_p33 i' j' hd]) i j
    (show scsDiag 4 i j from h)

/-- HOL `SCS_DIAG_SCS_4I3_02` (AUEAHEH.hl:375). -/
theorem SCS_DIAG_SCS_4I3_02_p33 : scsDiag scs4I3.k 0 2 := by
  rw [K_SCS_4I3_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4I3_13` (AUEAHEH.hl:379). -/
theorem SCS_DIAG_SCS_4I3_13_p33 : scsDiag scs4I3.k 1 3 := by
  rw [K_SCS_4I3_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M2_02` (AUEAHEH.hl:384). -/
theorem SCS_DIAG_SCS_4M2_02_p33 : scsDiag scs4M2.k 0 2 := by
  rw [K_SCS_4M2]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M2_13` (AUEAHEH.hl:388). -/
theorem SCS_DIAG_SCS_4M2_13_p33 : scsDiag scs4M2.k 1 3 := by
  rw [K_SCS_4M2]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M3_02` (AUEAHEH.hl:393). -/
theorem SCS_DIAG_SCS_4M3_02_p33 : scsDiag scs4M3'.k 0 2 := by
  rw [K_SCS_4M3_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M3_13` (AUEAHEH.hl:397). -/
theorem SCS_DIAG_SCS_4M3_13_p33 : scsDiag scs4M3'.k 1 3 := by
  rw [K_SCS_4M3_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M4_02` (AUEAHEH.hl:401). -/
theorem SCS_DIAG_SCS_4M4_02_p33 : scsDiag scs4M4'.k 0 2 := by
  rw [K_SCS_4M4_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M4_13` (AUEAHEH.hl:405). -/
theorem SCS_DIAG_SCS_4M4_13_p33 : scsDiag scs4M4'.k 1 3 := by
  rw [K_SCS_4M4_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M5_02` (AUEAHEH.hl:409). -/
theorem SCS_DIAG_SCS_4M5_02_p33 : scsDiag scs4M5'.k 0 2 := by
  rw [K_SCS_4M5_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M5_13` (AUEAHEH.hl:413). -/
theorem SCS_DIAG_SCS_4M5_13_p33 : scsDiag scs4M5'.k 1 3 := by
  rw [K_SCS_4M5_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M6_02` (AUEAHEH.hl:417). -/
theorem SCS_DIAG_SCS_4M6_02_p33 : scsDiag scs4M6'.k 0 2 := by
  rw [K_SCS_4M6]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M6_13` (AUEAHEH.hl:421). -/
theorem SCS_DIAG_SCS_4M6_13_p33 : scsDiag scs4M6'.k 1 3 := by
  rw [K_SCS_4M6]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M7_02` (AUEAHEH.hl:426). -/
theorem SCS_DIAG_SCS_4M7_02_p33 : scsDiag scs4M7.k 0 2 := by
  rw [K_SCS_4M7_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M7_13` (AUEAHEH.hl:430). -/
theorem SCS_DIAG_SCS_4M7_13_p33 : scsDiag scs4M7.k 1 3 := by
  rw [K_SCS_4M7_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M8_02` (AUEAHEH.hl:434). -/
theorem SCS_DIAG_SCS_4M8_02_p33 : scsDiag scs4M8.k 0 2 := by
  rw [K_SCS_4M8_p33]; unfold scsDiag; decide

/-- HOL `SCS_DIAG_SCS_4M8_13` (AUEAHEH.hl:438). -/
theorem SCS_DIAG_SCS_4M8_13_p33 : scsDiag scs4M8.k 1 3 := by
  rw [K_SCS_4M8_p33]; unfold scsDiag; decide

/-- HOL `MM_4I3_IMP_4T4` (AUEAHEH.hl:443). Proved modulo
`BB_4I3_IMP_4T4_p33`. -/
theorem MM_4I3_IMP_4T4_p33 {v : ℕ → V3}
    (hv : v ∈ MMsV39 (scsStabDiagV39 scs4I3 1 3)) : MMsV39 scs4T4 ≠ ∅ := by
  obtain ⟨h1, h2⟩ := STAB_4I3_SCS_p33 1 3 SCS_DIAG_SCS_4I3_13_p33
  refine XWNHLMD_MM_p33 _ scs4T4 v h1 SCS_4T4_IS_SCS_p33 h2 SCS_4T4_BASIC_p33 rfl hv
    (BB_4I3_IMP_4T4_p33 v (MMs_imp_BBs_p33 hv)) ?_
  rw [stab_d_eq_p33]; exact le_refl _

/-- HOL `SCS_4I3_ARROW_4T4` (AUEAHEH.hl:460). Proved modulo
`BB_4I3_IMP_4T4_p33`. -/
theorem SCS_4I3_ARROW_4T4_p33 :
    scsArrowV39 {scsStabDiagV39 scs4I3 1 3} {scs4T4} :=
  ARROW_SING_p33 _ _ SCS_4T4_IS_SCS_p33 (fun v hv => MM_4I3_IMP_4T4_p33 hv)

/-- HOL `PROP_OPP_DIAG_4I3_13` (AUEAHEH.hl:487).  NEEDS: the
`peropp2`-re-indexing table identity (stab 1 3 = pe (opp (stab 0 2)) 2). -/
theorem PROP_OPP_DIAG_4I3_13_p33 :
    scsStabDiagV39 scs4I3 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4I3 0 2)) 2 := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl PROP_OPP_DIAG_4I3_13 (PSORT_MOD case tree).

/-- HOL `STAB_4I3_02_ARROW_4I3_13` (AUEAHEH.hl:521). Proved modulo
`PROP_OPP_DIAG_4I3_13_p33` and the `YXIONXL2_p33`/`OPP_IS_SCS_p33` twins. -/
theorem STAB_4I3_02_ARROW_4I3_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scsStabDiagV39 scs4I3 1 3} := by
  rw [PROP_OPP_DIAG_4I3_13_p33]
  have h1 := (STAB_4I3_SCS_p33 0 2 SCS_DIAG_SCS_4I3_02_p33).1
  refine FZIOTEF_TRANS _ {scsOppV39 (scsStabDiagV39 scs4I3 0 2)} _ ?_ ?_
  · exact YXIONXL2_p33 _ h1 (by decide)
  · exact YXIONXL3_p33 _ 2 (OPP_IS_SCS_p33 _ h1)

/-- HOL `ZNLLLDL` (AUEAHEH.hl:539). Proved modulo `BB_4I3_IMP_4T4_p33`. -/
theorem ZNLLLDL_p33 :
    scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scs4T4} :=
  FZIOTEF_TRANS _ _ _ (STAB_4I3_02_ARROW_4I3_13_p33) (SCS_4I3_ARROW_4T4_p33)

/-- HOL `BB_4I3_IMP_BB_4M6` (AUEAHEH.hl:547).  NEEDS: the pair-class a/b
transfer between the `4I3` and `4M6'` tables (edges agree; diag entries via
`cstab < dist`). -/
theorem BB_4I3_IMP_BB_4M6_p33 (v : ℕ → V3) (hbb : BBsV39 scs4I3 v)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    BBsV39 scs4M6' v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4I3_IMP_BB_4M6.

/-- HOL `MM_4I3_IMP_4M6` (AUEAHEH.hl:581). Proved modulo
`BB_4I3_IMP_BB_4M6_p33`. -/
theorem MM_4I3_IMP_4M6_p33 {v : ℕ → V3} (hv : v ∈ MMsV39 scs4I3)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4M6' ≠ ∅ :=
  XWNHLMD_MM_p33 scs4I3 scs4M6' v SCS_4I3_IS_SCS_p33 is_scs_4M6_p33
    SCS_4I3_BASIC_p33 SCS_4M6_BASIC rfl hv
    (BB_4I3_IMP_BB_4M6_p33 v (MMs_imp_BBs_p33 hv) hdiag)
    (by norm_num [scs4I3, scs4M6', mkUnadornedV39])

/-- HOL `BB_4I3_IMP_BB_STAN_4I3` (AUEAHEH.hl:599). -/
theorem BB_4I3_IMP_BB_STAN_4I3_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4I3 v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4I3 i j) v :=
  BB_STAN_p33 scs4I3 SCS_4I3_IS_SCS_p33 v i j hbb hc

/-- HOL `MM_4I3_IMP_STAB_4I3` (AUEAHEH.hl:623). -/
theorem MM_4I3_IMP_STAB_4I3_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4I3)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4I3 i j) ≠ ∅ :=
  MM_STAN_p33 scs4I3 SCS_4I3_IS_SCS_p33 SCS_4I3_BASIC_p33 i j
    (show scsDiag scs4I3.k i j from hd) (STAB_4I3_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4I3_ARROW_SCS_4M6_STAB_4I3` (AUEAHEH.hl:639). Proved modulo
`BB_4I3_IMP_BB_4M6_p33`. -/
theorem SCS_4I3_ARROW_SCS_4M6_STAB_4I3_p33 :
    scsArrowV39 {scs4I3}
      ({scs4M6'} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I3 i j}) :=
  ARROW_SPLIT_p33 scs4I3 scs4M6' _ is_scs_4M6_p33
    (by intro t ht
        obtain ⟨i, j, hd, rfl⟩ := ht
        exact (STAB_4I3_SCS_p33 i j hd).1)
    (fun v hv hall => MM_4I3_IMP_4M6_p33 hv hall)
    (by intro v hv hdiag
        obtain ⟨i, j, hd, hc⟩ := hdiag
        exact ⟨scsStabDiagV39 scs4I3 i j, ⟨i, j, hd, rfl⟩,
          MM_4I3_IMP_STAB_4I3_p33 i j hv hd hc⟩)

/-- HOL `SET_STAB_4I3` (AUEAHEH.hl:708). -/
theorem SET_STAB_4I3_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I3 i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4I3 (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4I3 SCS_4I3_IS_SCS_p33 K_SCS_4I3_p33

/-- HOL `EXPAND_STAB_DIAG_4I3` (AUEAHEH.hl:712). -/
theorem EXPAND_STAB_DIAG_4I3_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4I3 (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4I3 (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4I3 SCS_4I3_IS_SCS_p33 K_SCS_4I3_p33

/-- HOL `SET_EQ_DIAG_STAB_4I3` (AUEAHEH.hl:719). -/
theorem SET_EQ_DIAG_STAB_4I3_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I3 i j}
      {scsStabDiagV39 scs4I3 0 2, scsStabDiagV39 scs4I3 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4I3 SCS_4I3_IS_SCS_p33 SCS_4I3_BASIC_p33 K_SCS_4I3_p33
    (fun i j hd => by rw [a_diag_4I3_p33 i j hd]; exact sqrt8_LE_CSTAB)

/-- HOL `VQFYMZY` (AUEAHEH.hl:772). Proved modulo `BB_4I3_IMP_4T4_p33` and
`BB_4I3_IMP_BB_4M6_p33`. -/
theorem VQFYMZY_p33 : scsArrowV39 {scs4I3} {scs4M6', scs4T4} := by
  have hisT : ∀ t ∈ ({scs4M6', scs4T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h
    · subst h; exact is_scs_4M6_p33
    · subst h; exact SCS_4T4_IS_SCS_p33
  have hstab : scsArrowV39
      {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4I3 i j} {scs4T4} :=
    FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4I3_p33)
      (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4I3 0 2} {scsStabDiagV39 scs4I3 1 3}
        {scs4T4} (ZNLLLDL_p33) (SCS_4I3_ARROW_4T4_p33)
      (fun t ht => by
        have h2 := Set.mem_singleton_iff.mp ht
        subst h2
        exact SCS_4T4_IS_SCS_p33))
  refine FZIOTEF_TRANS _ _ _ (SCS_4I3_ARROW_SCS_4M6_STAB_4I3_p33) ?_
  refine FZIOTEF_TRANS _ _ _
    (FZIOTEF_UNION _ _ _ _ (REFL_SING_p33 scs4M6' is_scs_4M6_p33) hstab) ?_
  exact FZIOTEF_SUBSET_p33 _ _
    (by intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at ht ⊢
        tauto)
    hisT

/-- HOL `BB_4M2_IMP_BB_4M6` (AUEAHEH.hl:801).  NEEDS: as
`BB_4I3_IMP_BB_4M6_p33`, over the `4M2`/`4M6'` tables. -/
theorem BB_4M2_IMP_BB_4M6_p33 (v : ℕ → V3) (hbb : BBsV39 scs4M2 v)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    BBsV39 scs4M6' v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4M2_IMP_BB_4M6.

/-- HOL `MM_4M2_IMP_4M6` (AUEAHEH.hl:836). Proved modulo
`BB_4M2_IMP_BB_4M6_p33`. -/
theorem MM_4M2_IMP_4M6_p33 {v : ℕ → V3} (hv : v ∈ MMsV39 scs4M2)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4M6' ≠ ∅ :=
  XWNHLMD_MM_p33 scs4M2 scs4M6' v SCS_4M2_IS_SCS is_scs_4M6_p33
    SCS_4M2_BASIC SCS_4M6_BASIC rfl hv
    (BB_4M2_IMP_BB_4M6_p33 v (MMs_imp_BBs_p33 hv) hdiag)
    (by norm_num [scs4M2, scs4M6', mkUnadornedV39])

/-- HOL `BB_4M2_IMP_BB_STAN_4M2` (AUEAHEH.hl:855). -/
theorem BB_4M2_IMP_BB_STAN_4M2_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4M2 v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M2 i j) v :=
  BB_STAN_p33 scs4M2 SCS_4M2_IS_SCS v i j hbb hc

/-- HOL `MM_4M2_IMP_STAB_4M2` (AUEAHEH.hl:880). -/
theorem MM_4M2_IMP_STAB_4M2_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4M2)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M2 i j) ≠ ∅ :=
  MM_STAN_p33 scs4M2 SCS_4M2_IS_SCS SCS_4M2_BASIC i j
    (show scsDiag scs4M2.k i j from hd) (STAB_4M2_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4M2_ARROW_SCS_4M6_STAB_4M2` (AUEAHEH.hl:898). Proved modulo
`BB_4M2_IMP_BB_4M6_p33`. -/
theorem SCS_4M2_ARROW_SCS_4M6_STAB_4M2_p33 :
    scsArrowV39 {scs4M2}
      ({scs4M6'} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M2 i j}) :=
  ARROW_SPLIT_p33 scs4M2 scs4M6' _ is_scs_4M6_p33
    (by intro t ht
        obtain ⟨i, j, hd, rfl⟩ := ht
        exact (STAB_4M2_SCS_p33 i j hd).1)
    (fun v hv hall => MM_4M2_IMP_4M6_p33 hv hall)
    (by intro v hv hdiag
        obtain ⟨i, j, hd, hc⟩ := hdiag
        exact ⟨scsStabDiagV39 scs4M2 i j, ⟨i, j, hd, rfl⟩,
          MM_4M2_IMP_STAB_4M2_p33 i j hv hd hc⟩)

/-- HOL `SET_STAB_4M2` (AUEAHEH.hl:968). -/
theorem SET_STAB_4M2_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M2 i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4M2 (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4M2 SCS_4M2_IS_SCS K_SCS_4M2

/-- HOL `EXPAND_STAB_DIAG_4M2` (AUEAHEH.hl:972). -/
theorem EXPAND_STAB_DIAG_4M2_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4M2 (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4M2 (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4M2 SCS_4M2_IS_SCS K_SCS_4M2

/-- HOL `SET_EQ_DIAG_STAB_4M2` (AUEAHEH.hl:979). -/
theorem SET_EQ_DIAG_STAB_4M2_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M2 i j}
      {scsStabDiagV39 scs4M2 0 2, scsStabDiagV39 scs4M2 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4M2 SCS_4M2_IS_SCS SCS_4M2_BASIC K_SCS_4M2
    (fun i j hd => by rw [a_diag_4M2_p33 i j hd]; exact two_h0_le_cstab_p20)

/-- HOL `PROP_OPP_DIAG_4M2_13` (AUEAHEH.hl:1033).  NEEDS: as
`PROP_OPP_DIAG_4I3_13_p33`, over the `4M2` tables. -/
theorem PROP_OPP_DIAG_4M2_13_p33 :
    scsStabDiagV39 scs4M2 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4M2 0 2)) 2 := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl PROP_OPP_DIAG_4M2_13.

/-- HOL `STAB_4M2_02_ARROW_4M2_13` (AUEAHEH.hl:1064). Proved modulo
`PROP_OPP_DIAG_4M2_13_p33`. -/
theorem STAB_4M2_02_ARROW_4M2_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M2 0 2} {scsStabDiagV39 scs4M2 1 3} := by
  rw [PROP_OPP_DIAG_4M2_13_p33]
  have h1 := (STAB_4M2_SCS_p33 0 2 SCS_DIAG_SCS_4M2_02_p33).1
  refine FZIOTEF_TRANS _ {scsOppV39 (scsStabDiagV39 scs4M2 0 2)} _ ?_ ?_
  · exact YXIONXL2_p33 _ h1 (by decide)
  · exact YXIONXL3_p33 _ 2 (OPP_IS_SCS_p33 _ h1)

/-- HOL `SCS_4M2_SLICE_13` (AUEAHEH.hl:1081).  NEEDS: the half-slice table
identity of `stab 4M2 1 3` at `(1, 3)` against `pe scs_3M1 1` / `scs_3T4`. -/
theorem SCS_4M2_SLICE_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M2 1 3}
      {scsPropEquV39 scs3M1 1, scs3T4} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4M2_SLICE_13 (LKGRQUI slice identity).

/-- HOL `BNAWVNH` (AUEAHEH.hl:1204). Proved modulo the `4M2` BB strut and
the slice/opp twins. -/
theorem BNAWVNH_p33 : scsArrowV39 {scs4M2} {scs4M6', scs3M1, scs3T4} := by
  have hisT : ∀ t ∈ ({scs4M6', scs3M1, scs3T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h | h
    · subst h; exact is_scs_4M6_p33
    · subst h; exact SCS_3M1_IS_SCS
    · subst h; exact is_scs_3T4_p33
  have hisM : ∀ t ∈ ({scs3M1, scs3T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h
    · subst h; exact SCS_3M1_IS_SCS
    · subst h; exact is_scs_3T4_p33
  have hstab : scsArrowV39
      {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M2 i j}
      {scs3M1, scs3T4} :=
    FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4M2_p33)
      (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4M2 0 2} {scsStabDiagV39 scs4M2 1 3}
        {scs3M1, scs3T4}
        (FZIOTEF_TRANS _ _ _ (STAB_4M2_02_ARROW_4M2_13_p33)
          (FZIOTEF_TRANS _ _ _ (SCS_4M2_SLICE_13_p33)
            (FZIOTEF_BOTH_p33 {scsPropEquV39 scs3M1 1} {scs3T4} {scs3M1, scs3T4}
              (pe_3M1_pad_p33 (Set.mem_insert _ _) hisM)
              (SING_PAD_p33 scs3T4 _ (Set.mem_insert_of_mem _ rfl) hisM)
              hisM)))
        (FZIOTEF_TRANS _ _ _ (SCS_4M2_SLICE_13_p33)
          (FZIOTEF_BOTH_p33 {scsPropEquV39 scs3M1 1} {scs3T4} {scs3M1, scs3T4}
            (pe_3M1_pad_p33 (Set.mem_insert _ _) hisM)
            (SING_PAD_p33 scs3T4 _ (Set.mem_insert_of_mem _ rfl) hisM)
            hisM))
        hisM)
  refine FZIOTEF_TRANS _ _ _ (SCS_4M2_ARROW_SCS_4M6_STAB_4M2_p33) ?_
  refine FZIOTEF_TRANS _ _ _
    (FZIOTEF_UNION _ _ _ _ (REFL_SING_p33 scs4M6' is_scs_4M6_p33) hstab) ?_
  exact FZIOTEF_SUBSET_p33 _ _
    (by intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at ht ⊢
        tauto)
    hisT

/-- HOL `BB_4M3_IMP_BB_4M6` (AUEAHEH.hl:1256).  NEEDS: as
`BB_4I3_IMP_BB_4M6_p33`, over the `4M3'`/`4M6'` tables. -/
theorem BB_4M3_IMP_BB_4M6_p33 (v : ℕ → V3) (hbb : BBsV39 scs4M3' v)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    BBsV39 scs4M6' v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4M3_IMP_BB_4M6.

/-- HOL `MM_4M3_IMP_4M6` (AUEAHEH.hl:1292). Proved modulo
`BB_4M3_IMP_BB_4M6_p33`. -/
theorem MM_4M3_IMP_4M6_p33 {v : ℕ → V3} (hv : v ∈ MMsV39 scs4M3')
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4M6' ≠ ∅ :=
  XWNHLMD_MM_p33 scs4M3' scs4M6' v is_scs_4M3_p33 is_scs_4M6_p33
    SCS_4M3_BASIC_p33 SCS_4M6_BASIC rfl hv
    (BB_4M3_IMP_BB_4M6_p33 v (MMs_imp_BBs_p33 hv) hdiag)
    (by norm_num [scs4M3', scs4M6', mkUnadornedV39])

/-- HOL `BB_4M3_IMP_BB_STAN_4M3` (AUEAHEH.hl:1311). -/
theorem BB_4M3_IMP_BB_STAN_4M3_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4M3' v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M3' i j) v :=
  BB_STAN_p33 scs4M3' is_scs_4M3_p33 v i j hbb hc

/-- HOL `MM_4M3_IMP_STAB_4M3` (AUEAHEH.hl:1338). -/
theorem MM_4M3_IMP_STAB_4M3_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4M3')
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M3' i j) ≠ ∅ :=
  MM_STAN_p33 scs4M3' is_scs_4M3_p33 SCS_4M3_BASIC_p33 i j
    (show scsDiag scs4M3'.k i j from hd) (STAB_4M3_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4M3_ARROW_SCS_4M6_STAB_4M3` (AUEAHEH.hl:1357). Proved modulo
`BB_4M3_IMP_BB_4M6_p33`. -/
theorem SCS_4M3_ARROW_SCS_4M6_STAB_4M3_p33 :
    scsArrowV39 {scs4M3'}
      ({scs4M6'} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M3' i j}) :=
  ARROW_SPLIT_p33 scs4M3' scs4M6' _ is_scs_4M6_p33
    (by intro t ht
        obtain ⟨i, j, hd, rfl⟩ := ht
        exact (STAB_4M3_SCS_p33 i j hd).1)
    (fun v hv hall => MM_4M3_IMP_4M6_p33 hv hall)
    (by intro v hv hdiag
        obtain ⟨i, j, hd, hc⟩ := hdiag
        exact ⟨scsStabDiagV39 scs4M3' i j, ⟨i, j, hd, rfl⟩,
          MM_4M3_IMP_STAB_4M3_p33 i j hv hd hc⟩)

/-- HOL `SET_STAB_4M3` (AUEAHEH.hl:1428). -/
theorem SET_STAB_4M3_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M3' i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4M3' (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4M3' is_scs_4M3_p33 K_SCS_4M3_p33

/-- HOL `EXPAND_STAB_DIAG_4M3` (AUEAHEH.hl:1432). -/
theorem EXPAND_STAB_DIAG_4M3_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4M3' (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4M3' (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4M3' is_scs_4M3_p33 K_SCS_4M3_p33

/-- HOL `SET_EQ_DIAG_STAB_4M3` (AUEAHEH.hl:1439). -/
theorem SET_EQ_DIAG_STAB_4M3_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M3' i j}
      {scsStabDiagV39 scs4M3' 0 2, scsStabDiagV39 scs4M3' 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4M3' is_scs_4M3_p33 SCS_4M3_BASIC_p33 K_SCS_4M3_p33
    (fun i j hd => by rw [a_diag_4M3_p33 i j hd]; exact sqrt8_LE_CSTAB)

/-- HOL `PROP_OPP_DIAG_4M3_13` (AUEAHEH.hl:1522).  NEEDS: as
`PROP_OPP_DIAG_4I3_13_p33`, over the `4M3'` tables. -/
theorem PROP_OPP_DIAG_4M3_13_p33 :
    scsStabDiagV39 scs4M3' 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4M3' 0 2)) 2 := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl PROP_OPP_DIAG_4M3_13.

/-- HOL `STAB_4M3_02_ARROW_4M3_13` (AUEAHEH.hl:1539). Proved modulo
`PROP_OPP_DIAG_4M3_13_p33`. -/
theorem STAB_4M3_02_ARROW_4M3_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M3' 0 2} {scsStabDiagV39 scs4M3' 1 3} := by
  rw [PROP_OPP_DIAG_4M3_13_p33]
  have h1 := (STAB_4M3_SCS_p33 0 2 SCS_DIAG_SCS_4M3_02_p33).1
  refine FZIOTEF_TRANS _ {scsOppV39 (scsStabDiagV39 scs4M3' 0 2)} _ ?_ ?_
  · exact YXIONXL2_p33 _ h1 (by decide)
  · exact YXIONXL3_p33 _ 2 (OPP_IS_SCS_p33 _ h1)

/-- HOL `SCS_4M3_SLICE_13` (AUEAHEH.hl:1752).  NEEDS: the half-slice table
identity against `pe scs_3T1 1` / `pe scs_3T6' 2`. -/
theorem SCS_4M3_SLICE_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M3' 1 3}
      {scsPropEquV39 scs3T1 1, scsPropEquV39 scs3T6' 2} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4M3_SLICE_13 (LKGRQUI slice identity).

/-- HOL `RAWZDIB` (AUEAHEH.hl:1764). Proved modulo the `4M3'` BB strut and
the slice/pe twins. -/
theorem RAWZDIB_p33 : scsArrowV39 {scs4M3'} {scs4M6', scs3T1, scs3T6'} := by
  have hisT : ∀ t ∈ ({scs4M6', scs3T1, scs3T6'} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h | h
    · subst h; exact is_scs_4M6_p33
    · subst h; exact is_scs_3T1_p33
    · subst h; exact is_scs_3T6_p33
  have hisM : ∀ t ∈ ({scs3T1, scs3T6'} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h
    · subst h; exact is_scs_3T1_p33
    · subst h; exact is_scs_3T6_p33
  have hstab : scsArrowV39
      {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M3' i j}
      {scs3T1, scs3T6'} :=
    FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4M3_p33)
      (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4M3' 0 2} {scsStabDiagV39 scs4M3' 1 3}
        {scs3T1, scs3T6'}
        (FZIOTEF_TRANS _ _ _ (STAB_4M3_02_ARROW_4M3_13_p33)
          (FZIOTEF_TRANS _ _ _ (SCS_4M3_SLICE_13_p33)
            (FZIOTEF_BOTH_p33 {scsPropEquV39 scs3T1 1} {scsPropEquV39 scs3T6' 2}
              {scs3T1, scs3T6'}
              (pe_3T1_pad_p33 (Set.mem_insert _ _) hisM)
              (pe_3T6_pad_p33 (Set.mem_insert_of_mem _ rfl) hisM)
              hisM)))
        (FZIOTEF_TRANS _ _ _ (SCS_4M3_SLICE_13_p33)
          (FZIOTEF_BOTH_p33 {scsPropEquV39 scs3T1 1} {scsPropEquV39 scs3T6' 2}
            {scs3T1, scs3T6'}
            (pe_3T1_pad_p33 (Set.mem_insert _ _) hisM)
            (pe_3T6_pad_p33 (Set.mem_insert_of_mem _ rfl) hisM)
            hisM))
        hisM)
  refine FZIOTEF_TRANS _ _ _ (SCS_4M3_ARROW_SCS_4M6_STAB_4M3_p33) ?_
  refine FZIOTEF_TRANS _ _ _
    (FZIOTEF_UNION _ _ _ _ (REFL_SING_p33 scs4M6' is_scs_4M6_p33) hstab) ?_
  exact FZIOTEF_SUBSET_p33 _ _
    (by intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at ht ⊢
        tauto)
    hisT

/-- HOL `BB_4M4_IMP_BB_4M7` (AUEAHEH.hl:2303).  NEEDS: as
`BB_4I3_IMP_BB_4M6_p33`, over the `4M4'`/`4M7` tables. -/
theorem BB_4M4_IMP_BB_4M7_p33 (v : ℕ → V3) (hbb : BBsV39 scs4M4' v)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    BBsV39 scs4M7 v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4M4_IMP_BB_4M7.

/-- HOL `MM_4M4_IMP_4M7` (AUEAHEH.hl:2347). Proved modulo
`BB_4M4_IMP_BB_4M7_p33`. -/
theorem MM_4M4_IMP_4M7_p33 {v : ℕ → V3} (hv : v ∈ MMsV39 scs4M4')
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4M7 ≠ ∅ :=
  XWNHLMD_MM_p33 scs4M4' scs4M7 v is_scs_4M4_p33 is_scs_4M7_p33
    SCS_4M4_BASIC_p33 SCS_4M7_BASIC_p33 rfl hv
    (BB_4M4_IMP_BB_4M7_p33 v (MMs_imp_BBs_p33 hv) hdiag)
    (by norm_num [scs4M4', scs4M7, mkUnadornedV39])

/-- HOL `BB_4M4_IMP_BB_STAN_4M4` (AUEAHEH.hl:2365). -/
theorem BB_4M4_IMP_BB_STAN_4M4_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4M4' v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M4' i j) v :=
  BB_STAN_p33 scs4M4' is_scs_4M4_p33 v i j hbb hc

/-- HOL `MM_4M4_IMP_STAB_4M4` (AUEAHEH.hl:2365 ff). -/
theorem MM_4M4_IMP_STAB_4M4_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4M4')
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M4' i j) ≠ ∅ :=
  MM_STAN_p33 scs4M4' is_scs_4M4_p33 SCS_4M4_BASIC_p33 i j
    (show scsDiag scs4M4'.k i j from hd) (STAB_4M4_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4M4_ARROW_SCS_4M7_STAB_4M4` (AUEAHEH.hl:1814). Proved modulo
`BB_4M4_IMP_BB_4M7_p33`. -/
theorem SCS_4M4_ARROW_SCS_4M7_STAB_4M4_p33 :
    scsArrowV39 {scs4M4'}
      ({scs4M7} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M4' i j}) :=
  ARROW_SPLIT_p33 scs4M4' scs4M7 _ is_scs_4M7_p33
    (by intro t ht
        obtain ⟨i, j, hd, rfl⟩ := ht
        exact (STAB_4M4_SCS_p33 i j hd).1)
    (fun v hv hall => MM_4M4_IMP_4M7_p33 hv hall)
    (by intro v hv hdiag
        obtain ⟨i, j, hd, hc⟩ := hdiag
        exact ⟨scsStabDiagV39 scs4M4' i j, ⟨i, j, hd, rfl⟩,
          MM_4M4_IMP_STAB_4M4_p33 i j hv hd hc⟩)

/-- HOL `SET_STAB_4M4` (AUEAHEH.hl:1885). -/
theorem SET_STAB_4M4_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M4' i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4M4' (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4M4' is_scs_4M4_p33 K_SCS_4M4_p33

/-- HOL `EXPAND_STAB_DIAG_4M4` (AUEAHEH.hl:1889). -/
theorem EXPAND_STAB_DIAG_4M4_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4M4' (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4M4' (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4M4' is_scs_4M4_p33 K_SCS_4M4_p33

/-- HOL `SET_EQ_DIAG_STAB_4M4` (AUEAHEH.hl:1896). -/
theorem SET_EQ_DIAG_STAB_4M4_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M4' i j}
      {scsStabDiagV39 scs4M4' 0 2, scsStabDiagV39 scs4M4' 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4M4' is_scs_4M4_p33 SCS_4M4_BASIC_p33 K_SCS_4M4_p33
    (fun i j hd => by rw [a_diag_4M4_p33 i j hd]; exact two_h0_le_cstab_p20)

/-- HOL `SCS_4M4_SLICE_13` (AUEAHEH.hl:1948).  NEEDS: the half-slice table
identity against `pe scs_3T4 2` / `scs_3T4`. -/
theorem SCS_4M4_SLICE_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M4' 1 3}
      {scsPropEquV39 scs3T4 2, scs3T4} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4M4_SLICE_13 (LKGRQUI slice identity).

/-- HOL `SCS_4M4_SLICE_02` (AUEAHEH.hl:2075).  NEEDS: the half-slice table
identity against `scs_3T3` / `pe scs_3M1 1`. -/
theorem SCS_4M4_SLICE_02_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M4' 0 2}
      {scs3T3, scsPropEquV39 scs3M1 1} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4M4_SLICE_02 (LKGRQUI slice identity).

/-- HOL `MFKLVDK` (AUEAHEH.hl:2211). Proved modulo the `4M4'` BB strut and
the slice/pe twins. -/
theorem MFKLVDK_p33 :
    scsArrowV39 {scs4M4'} {scs4M7, scs3T3, scs3M1, scs3T4} := by
  have hisT : ∀ t ∈ ({scs4M7, scs3T3, scs3M1, scs3T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h | h | h
    · subst h; exact is_scs_4M7_p33
    · subst h; exact SCS_3T3_IS_SCS_p33
    · subst h; exact SCS_3M1_IS_SCS
    · subst h; exact is_scs_3T4_p33
  have hisM : ∀ t ∈ ({scs3T3, scs3M1, scs3T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h | h
    · subst h; exact SCS_3T3_IS_SCS_p33
    · subst h; exact SCS_3M1_IS_SCS
    · subst h; exact is_scs_3T4_p33
  have hstab : scsArrowV39
      {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M4' i j}
      {scs3T3, scs3M1, scs3T4} :=
    FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4M4_p33)
      (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4M4' 0 2} {scsStabDiagV39 scs4M4' 1 3}
        {scs3T3, scs3M1, scs3T4}
        (FZIOTEF_TRANS _ _ _ (SCS_4M4_SLICE_02_p33)
          (FZIOTEF_BOTH_p33 {scs3T3} {scsPropEquV39 scs3M1 1} {scs3T3, scs3M1, scs3T4}
            (SING_PAD_p33 scs3T3 _ (Set.mem_insert _ _) hisM)
            (pe_3M1_pad_p33 (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hisM)
            hisM))
        (FZIOTEF_TRANS _ _ _ (SCS_4M4_SLICE_13_p33)
          (FZIOTEF_BOTH_p33 {scsPropEquV39 scs3T4 2} {scs3T4} {scs3T3, scs3M1, scs3T4}
            (pe_3T4_pad_p33 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)) hisM)
            (SING_PAD_p33 scs3T4 _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
              hisM)
            hisM))
        hisM)
  refine FZIOTEF_TRANS _ _ _ (SCS_4M4_ARROW_SCS_4M7_STAB_4M4_p33) ?_
  refine FZIOTEF_TRANS _ _ _
    (FZIOTEF_UNION _ _ _ _ (REFL_SING_p33 scs4M7 is_scs_4M7_p33) hstab) ?_
  exact FZIOTEF_SUBSET_p33 _ _
    (by intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at ht ⊢
        tauto)
    hisT

/-- HOL `BB_4M5_IMP_BB_4M8` (AUEAHEH.hl:2712).  NEEDS: as
`BB_4I3_IMP_BB_4M6_p33`, over the `4M5'`/`4M8` tables. -/
theorem BB_4M5_IMP_BB_4M8_p33 (v : ℕ → V3) (hbb : BBsV39 scs4M5' v)
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    BBsV39 scs4M8 v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4M5_IMP_BB_4M8.

/-- HOL `MM_4M5_IMP_4M8` (AUEAHEH.hl:2729). Proved modulo
`BB_4M5_IMP_BB_4M8_p33`. -/
theorem MM_4M5_IMP_4M8_p33 {v : ℕ → V3} (hv : v ∈ MMsV39 scs4M5')
    (hdiag : ∀ i j, scsDiag 4 i j → cstab < dist (v i) (v j)) :
    MMsV39 scs4M8 ≠ ∅ :=
  XWNHLMD_MM_p33 scs4M5' scs4M8 v is_scs_4M5_p33 is_scs_4M8_p33
    SCS_4M5_BASIC_p33 SCS_4M8_BASIC_p33 rfl hv
    (BB_4M5_IMP_BB_4M8_p33 v (MMs_imp_BBs_p33 hv) hdiag)
    (by norm_num [scs4M5', scs4M8, mkUnadornedV39])

/-- HOL `BB_4M5_IMP_BB_STAN_4M5` (AUEAHEH.hl:2745). -/
theorem BB_4M5_IMP_BB_STAN_4M5_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4M5' v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M5' i j) v :=
  BB_STAN_p33 scs4M5' is_scs_4M5_p33 v i j hbb hc

/-- HOL `MM_4M5_IMP_STAB_4M5` (AUEAHEH.hl:2808). -/
theorem MM_4M5_IMP_STAB_4M5_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4M5')
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M5' i j) ≠ ∅ :=
  MM_STAN_p33 scs4M5' is_scs_4M5_p33 SCS_4M5_BASIC_p33 i j
    (show scsDiag scs4M5'.k i j from hd) (STAB_4M5_SCS_p33 i j hd) hv hc

/-- HOL `SCS_4M5_ARROW_SCS_4M8_STAB_4M5` (AUEAHEH.hl:2365). Proved modulo
`BB_4M5_IMP_BB_4M8_p33`. -/
theorem SCS_4M5_ARROW_SCS_4M8_STAB_4M5_p33 :
    scsArrowV39 {scs4M5'}
      ({scs4M8} ∪ {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M5' i j}) :=
  ARROW_SPLIT_p33 scs4M5' scs4M8 _ is_scs_4M8_p33
    (by intro t ht
        obtain ⟨i, j, hd, rfl⟩ := ht
        exact (STAB_4M5_SCS_p33 i j hd).1)
    (fun v hv hall => MM_4M5_IMP_4M8_p33 hv hall)
    (by intro v hv hdiag
        obtain ⟨i, j, hd, hc⟩ := hdiag
        exact ⟨scsStabDiagV39 scs4M5' i j, ⟨i, j, hd, rfl⟩,
          MM_4M5_IMP_STAB_4M5_p33 i j hv hd hc⟩)

/-- HOL `SET_STAB_4M5` (AUEAHEH.hl:2436). -/
theorem SET_STAB_4M5_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M5' i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4M5' (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4M5' is_scs_4M5_p33 K_SCS_4M5_p33

/-- HOL `EXPAND_STAB_DIAG_4M5` (AUEAHEH.hl:2440). -/
theorem EXPAND_STAB_DIAG_4M5_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4M5' (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4M5' (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4M5' is_scs_4M5_p33 K_SCS_4M5_p33

/-- HOL `SET_EQ_DIAG_STAB_4M5` (AUEAHEH.hl:2447). -/
theorem SET_EQ_DIAG_STAB_4M5_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M5' i j}
      {scsStabDiagV39 scs4M5' 0 2, scsStabDiagV39 scs4M5' 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4M5' is_scs_4M5_p33 SCS_4M5_BASIC_p33 K_SCS_4M5_p33
    (fun i j hd => by rw [a_diag_4M5_p33 i j hd]; exact two_h0_le_cstab_p20)

/-- HOL `PROP_OPP_DIAG_4M5_13` (AUEAHEH.hl:2533).  NEEDS: as
`PROP_OPP_DIAG_4I3_13_p33`, over the `4M5'` tables. -/
theorem PROP_OPP_DIAG_4M5_13_p33 :
    scsStabDiagV39 scs4M5' 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4M5' 0 2)) 2 := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl PROP_OPP_DIAG_4M5_13.

/-- HOL `STAB_4M5_02_ARROW_4M5_13` (AUEAHEH.hl:2550). Proved modulo
`PROP_OPP_DIAG_4M5_13_p33`. -/
theorem STAB_4M5_02_ARROW_4M5_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M5' 0 2} {scsStabDiagV39 scs4M5' 1 3} := by
  rw [PROP_OPP_DIAG_4M5_13_p33]
  have h1 := (STAB_4M5_SCS_p33 0 2 SCS_DIAG_SCS_4M5_02_p33).1
  refine FZIOTEF_TRANS _ {scsOppV39 (scsStabDiagV39 scs4M5' 0 2)} _ ?_ ?_
  · exact YXIONXL2_p33 _ h1 (by decide)
  · exact YXIONXL3_p33 _ 2 (OPP_IS_SCS_p33 _ h1)

/-- HOL `SCS_4M5_SLICE_13` (AUEAHEH.hl:2831).  NEEDS: the half-slice table
identity of `stab 4M5' 1 3` against `scs_3T4`. -/
theorem SCS_4M5_SLICE_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M5' 1 3} {scs3T4} := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl SCS_4M5_SLICE_13 (LKGRQUI slice identity).

/-- HOL `RYPDIXT` (AUEAHEH.hl:2845). Proved modulo the `4M5'` BB strut and
the slice/opp twins. -/
theorem RYPDIXT_p33 : scsArrowV39 {scs4M5'} {scs4M8, scs3T4} := by
  have hisT : ∀ t ∈ ({scs4M8, scs3T4} : Set ScsV39), isScsV39 t := by
    intro t ht
    rcases ht with h | h
    · subst h; exact is_scs_4M8_p33
    · subst h; exact is_scs_3T4_p33
  have hstab : scsArrowV39
      {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M5' i j} {scs3T4} :=
    FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4M5_p33)
      (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4M5' 0 2} {scsStabDiagV39 scs4M5' 1 3}
        {scs3T4}
        (FZIOTEF_TRANS _ _ _ (STAB_4M5_02_ARROW_4M5_13_p33)
          (FZIOTEF_TRANS _ _ _ (SCS_4M5_SLICE_13_p33)
            (SING_PAD_p33 scs3T4 _ rfl
              (fun t ht => by
                have h2 := Set.mem_singleton_iff.mp ht
                subst h2
                exact is_scs_3T4_p33))))
        (FZIOTEF_TRANS _ _ _ (SCS_4M5_SLICE_13_p33)
          (SING_PAD_p33 scs3T4 _ rfl
            (fun t ht => by
              have h2 := Set.mem_singleton_iff.mp ht
              subst h2
              exact is_scs_3T4_p33)))
        (fun t ht => by
          have h2 := Set.mem_singleton_iff.mp ht
          subst h2
          exact is_scs_3T4_p33))
  refine FZIOTEF_TRANS _ _ _ (SCS_4M5_ARROW_SCS_4M8_STAB_4M5_p33) ?_
  refine FZIOTEF_TRANS _ _ _
    (FZIOTEF_UNION _ _ _ _ (REFL_SING_p33 scs4M8 is_scs_4M8_p33) hstab) ?_
  exact FZIOTEF_SUBSET_p33 _ _
    (by intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] at ht ⊢
        tauto)
    hisT

/-- HOL `BB_4M6_IMP_4T5` (AUEAHEH.hl:2894).  NEEDS: the pointwise a/b-table
comparison of `stab 4M6' 1 3` against `scs_4T5`. -/
theorem BB_4M6_IMP_4T5_p33 (v : ℕ → V3)
    (hbb : BBsV39 (scsStabDiagV39 scs4M6' 1 3) v) : BBsV39 scs4T5 v := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl BB_4M6_IMP_4T5 (funlist table comparison).

/-- HOL `MM_4M6_IMP_4T5` (AUEAHEH.hl:2729). Proved modulo
`BB_4M6_IMP_4T5_p33`. -/
theorem MM_4M6_IMP_4T5_p33 {v : ℕ → V3}
    (hv : v ∈ MMsV39 (scsStabDiagV39 scs4M6' 1 3)) : MMsV39 scs4T5 ≠ ∅ := by
  obtain ⟨h1, h2⟩ := STAB_4M6_SCS_p33 1 3 SCS_DIAG_SCS_4M6_13_p33
  refine XWNHLMD_MM_p33 _ scs4T5 v h1 SCS_4T5_IS_SCS_p33 h2 SCS_4T5_BASIC_p33 rfl hv
    (BB_4M6_IMP_4T5_p33 v (MMs_imp_BBs_p33 hv)) ?_
  rw [stab_d_eq_p33]; exact le_refl _

/-- HOL `STAB_4M6_13_ARROW_4T5` (AUEAHEH.hl:2745). Proved modulo
`BB_4M6_IMP_4T5_p33`. -/
theorem STAB_4M6_13_ARROW_4T5_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M6' 1 3} {scs4T5} :=
  ARROW_SING_p33 _ _ SCS_4T5_IS_SCS_p33 (fun v hv => MM_4M6_IMP_4T5_p33 hv)

/-- HOL `PROP_OPP_DIAG_4M6_13` (AUEAHEH.hl:2835).  NEEDS: as
`PROP_OPP_DIAG_4I3_13_p33`, over the `4M6'` tables. -/
theorem PROP_OPP_DIAG_4M6_13_p33 :
    scsStabDiagV39 scs4M6' 1 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs4M6' 0 2)) 2 := sorry
  -- DISCHARGES: NEEDS AUEAHEH.hl PROP_OPP_DIAG_4M6_13.

/-- HOL `STAB_4M6_02_ARROW_4M6_13` (AUEAHEH.hl:2808). Proved modulo
`PROP_OPP_DIAG_4M6_13_p33`. -/
theorem STAB_4M6_02_ARROW_4M6_13_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M6' 0 2} {scsStabDiagV39 scs4M6' 1 3} := by
  rw [PROP_OPP_DIAG_4M6_13_p33]
  have h1 := (STAB_4M6_SCS_p33 0 2 SCS_DIAG_SCS_4M6_02_p33).1
  refine FZIOTEF_TRANS _ {scsOppV39 (scsStabDiagV39 scs4M6' 0 2)} _ ?_ ?_
  · exact YXIONXL2_p33 _ h1 (by decide)
  · exact YXIONXL3_p33 _ 2 (OPP_IS_SCS_p33 _ h1)

/-- HOL `STAB_4M6_02_ARROW_4T5` (AUEAHEH.hl:2831 region). -/
theorem STAB_4M6_02_ARROW_4T5_p33 :
    scsArrowV39 {scsStabDiagV39 scs4M6' 0 2} {scs4T5} :=
  FZIOTEF_TRANS _ _ _ (STAB_4M6_02_ARROW_4M6_13_p33) (STAB_4M6_13_ARROW_4T5_p33)

/-- HOL `SET_STAB_4M6` (AUEAHEH.hl:2831). -/
theorem SET_STAB_4M6_p33 :
    {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M6' i j} =
      {x | ∃ i j, scsDiag 4 (i % 4) (j % 4) ∧
        x = scsStabDiagV39 scs4M6' (i % 4) (j % 4)} :=
  SET_STAB_GEN4_p33 scs4M6' is_scs_4M6_p33 K_SCS_4M6

/-- HOL `EXPAND_STAB_DIAG_4M6` (AUEAHEH.hl:2835). -/
theorem EXPAND_STAB_DIAG_4M6_p33 :
    {x | ∃ i j, j % 4 = (i % 4 + 2) % 4 ∧ x = scsStabDiagV39 scs4M6' (i % 4) (j % 4)} =
      {x | ∃ i, i < 4 ∧ x = scsStabDiagV39 scs4M6' (i + 2) i} :=
  EXPAND_STAB_DIAG_4_p33 scs4M6' is_scs_4M6_p33 K_SCS_4M6

/-- HOL `SET_EQ_DIAG_STAB_4M6` (AUEAHEH.hl:2842). -/
theorem SET_EQ_DIAG_STAB_4M6_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M6' i j}
      {scsStabDiagV39 scs4M6' 0 2, scsStabDiagV39 scs4M6' 1 3} :=
  SET_EQ_DIAG_STAB_GEN4_p33 scs4M6' is_scs_4M6_p33 SCS_4M6_BASIC K_SCS_4M6
    (fun i j hd => by rw [a_diag_4M6_p33 i j hd])

/-- HOL `SET_STAB_4M6_ARROW_4T5` (AUEAHEH.hl:2894). -/
theorem SET_STAB_4M6_ARROW_4T5_p33 :
    scsArrowV39 {x | ∃ i j, scsDiag 4 i j ∧ x = scsStabDiagV39 scs4M6' i j}
      {scs4T5} :=
  FZIOTEF_TRANS _ _ _ (SET_EQ_DIAG_STAB_4M6_p33)
    (FZIOTEF_BOTH_p33 {scsStabDiagV39 scs4M6' 0 2} {scsStabDiagV39 scs4M6' 1 3}
      {scs4T5} (STAB_4M6_02_ARROW_4T5_p33) (STAB_4M6_13_ARROW_4T5_p33)
      (fun t ht => by
        have h2 := Set.mem_singleton_iff.mp ht
        subst h2
        exact SCS_4T5_IS_SCS_p33))

/-- HOL `BB_4M6_IMP_BB_STAN_4M6` (AUEAHEH.hl:2906). -/
theorem BB_4M6_IMP_BB_STAN_4M6_p33 (v : ℕ → V3) (i j : ℕ) (hbb : BBsV39 scs4M6' v)
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    BBsV39 (scsStabDiagV39 scs4M6' i j) v :=
  BB_STAN_p33 scs4M6' is_scs_4M6_p33 v i j hbb hc

/-- HOL `MM_4M6_IMP_STAB_4M6` (AUEAHEH.hl:2930). -/
theorem MM_4M6_IMP_STAB_4M6_p33 {v : ℕ → V3} (i j : ℕ) (hv : v ∈ MMsV39 scs4M6')
    (hd : scsDiag 4 i j) (hc : dist (v i) (v j) ≤ cstab) :
    MMsV39 (scsStabDiagV39 scs4M6' i j) ≠ ∅ :=
  MM_STAN_p33 scs4M6' is_scs_4M6_p33 SCS_4M6_BASIC i j
    (show scsDiag scs4M6'.k i j from hd) (STAB_4M6_SCS_p33 i j hd) hv hc

end Kepler.Text
