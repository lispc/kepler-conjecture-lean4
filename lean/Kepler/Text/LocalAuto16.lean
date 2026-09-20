/-
LocalAuto16: port of four Flyspeck files feeding the terminal SCS
case-analysis, as one bundle,

  - `scripts/local/JEJTVGB.hl` (253 lines, 1 def + 5 theorems) —
    "Appendix, Main Estimate, check_completeness" (H. L. Truong /
    T. Hales, 2013): the single-step arrow transitivity
    `SCS_ARROW_TRANS_SING`, the case breakdown of
    `JEJTVGB_assume_v39` into the 23 terminal arrows, the assembly
    `JEJTVGB`, and the `lp_main_estimate` definition alias with its
    two bridging theorems.
  - `scripts/local/XIVPHKS.hl` (487 lines, 3 theorems, J. Harrison
    2013): the wedge-membership induction `XIVPHKS` (Lemma 7.143) and
    its index-shifted twin `XIVPHKS_SHIFT`, plus the azimuth
    permutation lemma `FSQKWKK` (Lemma 7.141).
  - `scripts/local/BKOSSGE.hl` (396 lines, 12 theorems, T. Hales
    2013): the `scs_3M1` ear split `BKOSSGE`, the analysis kit
    (`cos_bounds_0_pi`, `INV_ARCLENGTH`, the `dih_y` / `taum`
    continuity suite, `UPS_X_STD_POS`), the ear-angle registry
    `ear_acute` and the quad registry pair `quad_nonexist_849` /
    `quad_diag_362`.
  - `scripts/local/CQAOQLR.hl` (335 lines, 1 def + 11 theorems,
    H. L. Truong 2012): the opposite-system (k - SUC(. mod k))
    modular kit, `ELEMENT1_SYM_0` / `SCS_GENERIC_SYM_0`,
    `UNADORNED_OPP` / `BASIC_OPP` / `DIAG_OPP`, the registry
    conclusion `CQAOQLR_concl` and the ear-reciprocity theorem
    `CQAOQLR`.

FILE MAP
  Section A (JEJTVGB): `scsArrowTransSing_p16`, the 23-arrow
    `JEJTVGB_case_breakdown_p16`, `JEJTVGB_p16` (assembled from the
    appendix `*_concl` arrows of LocalAuto1 plus `BKOSSGE_p16`), the
    definition `lp_main_estimate`, `lp_main_estimate_JEJTVGB_p16`,
    `nonlinear_imp_lp_main_estimate_p16`.
  Section B (XIVPHKS): `FSQKWKK_p16`, `XIVPHKS_p16`,
    `XIVPHKS_SHIFT_p16`.
  Section C (BKOSSGE): `cos_bounds_0_pi_p16`, `ear_acute_p16`,
    `quad_nonexist_849_p16`, `quad_diag_362_p16`,
    `INV_ARCLENGTH_p16`, `taum_dih_y_p16`,
    `real_continuous_dih_y_wrt4/5/6_p16`, `real_continuous_taum_p16`,
    `UPS_X_STD_POS_p16`, `BKOSSGE_p16`.
  Section D (CQAOQLR): `K_SUC_2_MOD_SUB_p16`,
    `K_SUC_2_MOD_SUB_ID_p16`, `A_B_J_SCS_OPP_p16`, `SUC_OPP_ID_p16`,
    `K_SUC_2_MOD_F_SUB_ID_p16`, `ELEMENT1_SYM_0_p16`,
    `SCS_GENERIC_SYM_0_p16`, the definition `CQAOQLR_concl_p16`,
    `UNADORNED_OPP_p16`, `BASIC_OPP_p16`, `DIAG_OPP_p16`,
    `CQAOQLR_p16`.

ENCODING NOTES
  - Every new declaration carries the `_p16` suffix (same-wave lanes
    own LocalAuto12-15/17/18; nothing is imported from them, and any
    helper that would live there is left to the NEEDS markers below).
  - The scs_v39 lane (`ScsV39`, `isScsV39`, `MMsV39`, `BBsV39`,
    `scsArrowV39`, `scsStabDiagV39`, `scsDiag`, `scsOppV39`,
    `peropp`/`peropp2`, `unadornedV39`, `scsBasicV39`, `scsGeneric`,
    the concrete systems `scs6I1`..`scs3M1`, `cstab`, `rho`,
    `JEJTVGB_assume_v39`, `JEJTVGB_concl`,
    `main_nonlinear_terminal_v11`, and every quoted `*_concl` arrow)
    is the LocalAuto1 port and is imported, not copied.
  - The sphere.hl kit has no importable port in this file's import
    graph: PackingAuto18 (via LocalAuto1) and PackingAuto20 (via
    LocalAuto2/11) define the SAME `Kepler.Text` names (`atn2PA18`,
    `dih_y`, ...) and Lean rejects importing both sides, while the
    scs lane of this file mandates LocalAuto1.  So verbatim `_p16`
    copies are included: `atn2_p16` / `deltaXf_p16` / `deltaX4f_p16`
    / `dihXf_p16` / `dihY_p16` (= sphere.hl `dih_y` via
    `y_of_x`), `deltaY_p16` (= sphere.hl `delta_y`), and the opaque
    registry signature `taum_p16` (Terminal.hl's `taum`; no port in
    the corpus).  All are merge candidates for the owning wave.
    `ups_x`/`arclength`/`TRI_UPS_X_STRICT_POS` come from PackingAuto18
    via LocalAuto1 (unambiguous on this side).
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `0`;
    `dist(v,w)` <-> `dist v w`; `sqrt8` <-> `Real.sqrt 8`; `#3.62`
    is the exact literal `3.62`; `real_continuous f atreal x` <->
    `ContinuousAt f x` (HOL's `atreal` is `at` within `UNIV`);
    `collinear {vec 0, u, w}` <-> `Collinear3 0 u w`; HOL `numseg`
    `p..q` <-> `Finset.Icc p q`; `wedge_ge` <-> `wedgeGe`
    (PackingAuto2).  `scs_J_v39` is Prop-valued, so the `J` clause of
    `A_B_J_SCS_OPP_p16` is an `Iff` where HOL has `=`.
  - `JEJTVGB_assume_v39` / `JEJTVGB_concl` / `CQAOQLR_concl` /
    `lp_main_estimate` are Prop-valued defs (the statement registry,
    as in LocalAuto1).  The giants keep `sorry` bodies: the 23-arrow
    breakdown (NEEDS the terminal-arrows-to-empty theorem OCBICBY,
    `s_init_list_alt` and `scs_arrow_sing_empty`), both XIVPHKS
    inductions (NEEDS `sum3/4/5_azim_fan`, `AZIM_DIHV_SAME_STRONG`,
    the Localization wedge kit), `ear_acute` /
    `quad_nonexist_849` / `quad_diag_362` (NEEDS the nonlinear
    registry entries `get_main_nonlinear "2485876245a"` /
    `"8495326405"` / `"2171548893"`), `taum_dih_y` (NEEDS the real
    `taum` definition), `SCS_GENERIC_SYM_0` (NEEDS the Xwitccn /
    In_sym_0 symmetry kit), and the two assembly giants `BKOSSGE_p16`
    and `CQAOQLR_p16` (NEEDS TFITSKC / MM_SCS_OPP / OPP_IS_SCS /
    CHANGE_*_SCS_MOD).

DISCHARGES: `BKOSSGE_p16` is verbatim
  `LocalAuto1.BKOSSGE_concl` (`scsArrowV39 {scs3M1} {scs3T1, scs3T5}`);
when the BKOSSGE wave lands, that appendix sorry disappears through
this file.  All other items here discharge nothing yet.
-/

import Kepler.Text.LocalAuto1
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section A: JEJTVGB.hl (appendix, main estimate, check completeness) -/

/-- HOL `BKOSSGE` (BKOSSGE.hl:304), stated here because `JEJTVGB_p16`
consumes it; the proof body sits in Section C.  Verbatim
`LocalAuto1.BKOSSGE_concl` (appendix.hl:1564). -/
theorem BKOSSGE_p16 : scsArrowV39 {scs3M1} {scs3T1, scs3T5} := by
  sorry

/-- HOL `SCS_ARROW_TRANS_SING` (JEJTVGB.hl:14): one-step transitivity of
`scs_arrow_v39` into the empty target. -/
theorem scsArrowTransSing_p16 (a : ScsV39) (S : Set ScsV39)
    (h : scsArrowV39 {a} S) (hS : ∀ x ∈ S, scsArrowV39 {x} (∅ : Set ScsV39)) :
    scsArrowV39 {a} (∅ : Set ScsV39) := by
  refine ⟨fun s hs => absurd hs (by simp), ?_⟩
  refine Or.inl (fun s hs => ?_)
  by_contra hne
  have hex : ∃ x ∈ S, MMsV39 x ≠ ∅ := by
    rcases h.2 with h1 | h2
    · exact absurd (h1 s hs) hne
    · exact h2
  obtain ⟨x, hxS, hms⟩ := hex
  rcases (hS x hxS).2 with h3 | h3
  · exact hms (h3 x (by simp))
  · exact absurd h3 (by simp)

/-- HOL `JEJTVGB_case_breakdown` (JEJTVGB.hl:23): the terminal arrow
case breakdown — 23 single arrows (annotated in the source by their
registry names) imply `JEJTVGB_assume_v39`.
NEEDS: Ocbicby.OCBICBY (terminal systems have no MM), Jotswix
`s_init_list_alt` / `LFLACKU`, Ocbicby `scs_arrow_sing_empty`
(EAPGLE reduction of `JEJTVGB_assume_v39` to the empty-MM branch). -/
theorem JEJTVGB_case_breakdown_p16 (h : main_nonlinear_terminal_v11)
    (a01 : scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3M1})               -- OEHDBEN
    (a02 : scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2})            -- OTMTOTJ1
    (a03 : scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2})            -- OTMTOTJ2
    (a04 : scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4, scs5M2})            -- OTMTOTJ3
    (a05 : scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4, scs5M2})            -- OTMTOTJ4
    (a06 : scsArrowV39 {scs5M2} {scs5T1, scsStabDiagV39 scs5I2 0 2,
      scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs4M6', scs4M7, scs4M8, scs3T1, scs3T4})      -- HIJQAHA
    (a07 : scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs3M1, scs4M2})            -- CNICGSF1
    (a08 : scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs3T1, scs4M3'})           -- CNICGSF2
    (a09 : scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs3T4, scs4M2})            -- CNICGSF3
    (a10 : scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1})           -- CNICGSF4
    (a11 : scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs3M1, scs4M5'})           -- CNICGSF5
    (a12 : scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2})            -- FYSSVEV
    (a13 : scsArrowV39 {scs4I2} {scs4T1, scs4T2})                               -- ARDBZYE
    (a14 : scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1})                    -- AUEAHEH
    (a15 : scsArrowV39 {scs4I3} {scs4M6', scs4T4})                              -- VQFYMZY
    (a16 : scsArrowV39 {scs4M2} {scs4M6', scs3M1, scs3T4})                      -- BNAWVNH
    (a17 : scsArrowV39 {scs4M3'} {scs4M6', scs3T1, scs3T6'})                    -- RAWZDIB
    (a18 : scsArrowV39 {scs4M4'} {scs4M7, scs3T3, scs3M1, scs3T4})              -- MFKLVDK
    (a19 : scsArrowV39 {scs4M5'} {scs4M8, scs3T4})                              -- RYPDIXT
    (a20 : scsArrowV39 {scs4M6'} {scs4T3, scs4T5})                              -- NWDGKXH
    (a21 : scsArrowV39 {scs4M7} {scs4M6', scs3T3, scs3M1, scs3T4})              -- YOBIMPP
    (a22 : scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4})                      -- MIQMCSN
    (a23 : scsArrowV39 {scs3M1} {scs3T1, scs3T5}) :                             -- BKOSSGE
    JEJTVGB_assume_v39 := by
  sorry

/-- HOL `JEJTVGB` (JEJTVGB.hl:218): `main_nonlinear_terminal_v11` implies
`JEJTVGB_assume_v39`.
NEEDS: Hexagons.OEHDBEN — the arrow in the JEJTVGB.hl breakdown reads
`{scs6I1} -> {scs6T1, scs5M1, scs4M2, scs3M1}` (hexagons.hl:2135), while
LocalAuto1's registry binding `OEHDBEN_concl` (appendix.hl:1394) carries
the older `{..., scs3T1}` form, so the mechanical assembly
(`JEJTVGB_case_breakdown_p16` + the 22 remaining `*_concl` arrows +
`BKOSSGE_p16`) is short exactly that one theorem.  In HOL the step is
pure rewriting (`REWRITE_TAC (map UNDISCH2 [...])`). -/
theorem JEJTVGB_p16 (h : main_nonlinear_terminal_v11) : JEJTVGB_assume_v39 := by
  sorry

/-- HOL `lp_main_estimate` (JEJTVGB.hl:232, `new_definition` of the
equation with `Appendix.JEJTVGB_concl`). -/
def lp_main_estimate : Prop := JEJTVGB_concl

/-- HOL `lp_main_estimate_JEJTVGB` (JEJTVGB.hl:236). -/
theorem lp_main_estimate_JEJTVGB_p16 :
    JEJTVGB_assume_v39 ↔ lp_main_estimate := Iff.rfl

/-- HOL `nonlinear_imp_lp_main_estimate` (JEJTVGB.hl:244). -/
theorem nonlinear_imp_lp_main_estimate_p16 :
    main_nonlinear_terminal_v11 → lp_main_estimate := fun h =>
  lp_main_estimate_JEJTVGB_p16.2 (JEJTVGB_p16 h)

/-! ## Section B: XIVPHKS.hl (wedge-membership induction, Lemma 7.143) -/

/-- HOL `FSQKWKK` (XIVPHKS.hl:17, Lemma 7.141).
NEEDS: Local_lemmas `SIN_AZIM_POS_PI_LT` / `SIN_AZIM_MUTUAL_SROSS`
(the azimuth-sine SROSS kit) and `CROSS_TRIPLE`; no counterpart of the
sine-of-azim layer exists in Kepler.Geom yet. -/
theorem FSQKWKK_p16 (v0 v1 v2 v3 : V3) (h : azim v0 v1 v2 v3 ≤ Real.pi) :
    azim v0 v2 v3 v1 ≤ Real.pi := by
  sorry

/-- HOL `XIVPHKS` (XIVPHKS.hl:29, Lemma 7.143): under the local
non-collinearity, small-diagonal (`< e`) and ear-angle (`2e < a ≤ π`)
hypotheses, consecutive wedges absorb the whole chain in both
directions.  HOL `n - 1 = r` kept verbatim (ℕ truncated subtraction).
NEEDS: Localization `wedge_ge` unfolding, Local_lemmas
`AZIM_SPEC_DEGENERATE`, Polar_fan `AZIM_DIHV_SAME_STRONG`, Fan
`sum3/4/5_azim_fan`, `AZIM_REFL` at the degenerate indices — the full
induction of the source. -/
theorem XIVPHKS_p16 (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ) (n r : ℕ)
    (w : ℕ → V3) (hn : 1 ≤ n) (hr : n - 1 = r)
    (hpair : (Set.Icc (0:ℕ) n).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hd : (fun i j k => dihV 0 (w i) (w j) (w k)) = d)
    (ha : (fun i j k => azim 0 (w i) (w j) (w k)) = a)
    (hW : (fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))) = W)
    (he : 0 < 2 * e)
    (h1 : ∀ i ∈ Finset.Icc 1 r, 2 * e < a i (i + 1) (i - 1))
    (h2 : ∀ i ∈ Finset.Icc 1 r, a i (i + 1) (i - 1) ≤ Real.pi)
    (h3 : ∀ p q, ({p, q, q + 1} : Finset ℕ) ⊆ Finset.Icc 0 r → p ≠ q →
      p ≠ q + 1 → d p q (q + 1) < e)
    (h4 : ∀ p q, ({p, p + 1, q} : Finset ℕ) ⊆ Finset.Icc 0 r → q > p + 1 →
      d p (p + 1) q < e)
    (h5 : ∀ p q, ({p + 1, p, q} : Finset ℕ) ⊆ Finset.Icc 0 r → q < p →
      d (p + 1) p q < e) :
    (∀ k j, j + k ≤ r → w j ∈ W (j + k)) ∧
    (∀ k j, 1 ≤ j → j + k ≤ r → w (j + k) ∈ W j) := by
  sorry

/-- HOL `XIVPHKS_SHIFT` (XIVPHKS.hl:278): the same induction with the
straight angles in `1..(r+1)` (indices shifted by one).
NEEDS: same kit as `XIVPHKS_p16` plus Local_lemmas1
`FST_LST_IN_WEDGE_GE`. -/
theorem XIVPHKS_SHIFT_p16 (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ)
    (r : ℕ) (w : ℕ → V3)
    (hpair1 : (Set.Icc (0:ℕ) (r + 1)).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hpair2 : (Set.Icc (1:ℕ) (r + 2)).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hd : (fun i j k => dihV 0 (w i) (w j) (w k)) = d)
    (ha : (fun i j k => azim 0 (w i) (w j) (w k)) = a)
    (hW : (fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))) = W)
    (he : 0 < 2 * e)
    (h1 : ∀ i ∈ Finset.Icc 1 (r + 1), 2 * e < a i (i + 1) (i - 1))
    (h2 : ∀ i ∈ Finset.Icc 1 (r + 1), a i (i + 1) (i - 1) ≤ Real.pi)
    (h3 : ∀ p q, ({p, q, q + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) → p ≠ q →
      p ≠ q + 1 → d p q (q + 1) < e)
    (h4 : ∀ p q, ({p, p + 1, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) →
      q > p + 1 → d p (p + 1) q < e)
    (h5 : ∀ p q, ({p + 1, p, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) → q < p →
      d (p + 1) p q < e) :
    (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w j ∈ W (j + k)) ∧
    (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w (j + k) ∈ W j) := by
  sorry

/-! ## Section C: BKOSSGE.hl — sphere.hl kit (`_p16` copies)

PackingAuto18 (via LocalAuto1) and PackingAuto20 (via LocalAuto2/11)
export identical `Kepler.Text.atn2PA18`/`dihY`/... names and cannot be
imported together; this file needs LocalAuto1's scs lane, so the kit is
copied verbatim (merge note: delete against the owning wave). -/

/-- HOL `atn2PA18` (sphere.hl:48-52); verbatim twin of the PackingAuto18 /
PackingAuto20 renderings. -/
noncomputable def atn2_p16 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y)
  else Real.pi

/-- HOL `delta_x` (sphere.hl:86). -/
noncomputable def deltaXf_p16 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- HOL `delta_x4` (sphere.hl:110). -/
noncomputable def deltaX4f_p16 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `dih_x` (sphere.hl:153). -/
noncomputable def dihXf_p16 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.pi / 2 +
    atn2_p16 (Real.sqrt (4 * x1 * deltaXf_p16 x1 x2 x3 x4 x5 x6))
      (-(deltaX4f_p16 x1 x2 x3 x4 x5 x6))

/-- HOL `dih_y` (sphere.hl:159). -/
noncomputable def dihY_p16 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihXf_p16 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `delta_y` (sphere.hl): `y_of_x delta_x`. -/
noncomputable def deltaY_p16 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  deltaXf_p16 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- NEEDS: HOL `taum` (Terminal.hl): the truncated tau of a quad (6
y-slots); opaque registry signature (twin of LocalAuto11 `taum_p11`). -/
noncomputable def taum_p16 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ := sorry

/-! ## BKOSSGE.hl theorems -/

/-- HOL `cos_bounds_0_pi` (BKOSSGE.hl:14). -/
theorem cos_bounds_0_pi_p16 (z : ℝ) (h1 : 0 < z) (h2 : z < Real.pi) :
    -1 < Real.cos z ∧ Real.cos z < 1 := by
  have hc : Real.cos Real.pi < Real.cos z :=
    Real.cos_lt_cos_of_nonneg_of_le_pi h1.le le_rfl h2
  have h2' : Real.cos z < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) h2.le h1
  rw [Real.cos_pi] at hc
  rw [Real.cos_zero] at h2'
  exact ⟨hc, h2'⟩

/-- HOL `ear_acute` (BKOSSGE.hl:33).
NEEDS: Terminal.get_main_nonlinear "2485876245a" (the nonlinear registry
entry; lives in main_nonlinear_terminal_v11, another wave),
Trigonometry.IHIQXLM, Tskajxy.ATN2_Y_NEG, ATN_BOUNDS, and the
`dih_x_alt` rendering of `dih_y`. -/
theorem ear_acute_p16 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      2 ≤ y4 → y4 ≤ 2 * h0 → 2 ≤ y6 → y6 ≤ 2 * h0 → 3 ≤ y5 →
      0 < upsXPA18 (y1 * y1) (y3 * y3) (y5 * y5) →
      dihY_p16 y1 y2 y3 y4 y5 y6 < Real.pi / 2 := by
  sorry

/-- HOL `quad_nonexist_849` (BKOSSGE.hl:69).
NEEDS: Terminal.get_main_nonlinear "8495326405" and
Terminal.DELTA_Y_POS_4POINTS. -/
theorem quad_nonexist_849_p16 (h : main_nonlinear_terminal_v11) :
    ¬ ∃ (v1 v2 v3 v4 : V3), dist v1 v2 = 2 ∧ dist v2 v3 = 2 ∧ dist v3 v4 = 2 ∧
      dist v1 v4 = 2 * h0 ∧ cstab ≤ dist v1 v3 ∧ cstab ≤ dist v2 v4 := by
  sorry

/-- HOL `quad_diag_362` (BKOSSGE.hl:92): the shorter diagonal of a
cstab quad is below 3.62.
NEEDS: Terminal.get_main_nonlinear "2171548893" and
Terminal.DELTA_Y_POS_4POINTS. -/
theorem quad_diag_362_p16 (h : main_nonlinear_terminal_v11) :
    ∀ (v1 v2 v3 v4 : V3), dist v1 v2 = 2 → dist v2 v3 = cstab →
      dist v3 v4 = 2 → dist v1 v4 = cstab →
      dist v1 v3 ≤ 3.62 ∨ dist v2 v4 ≤ 3.62 := by
  sorry

/-- HOL `INV_ARCLENGTH` (BKOSSGE.hl:114): on `(0, π)` the `arclength`
functional inverts the chord-length formula.  The `atn2PA18` unfolding of
`arcLength` is reached through the local `∀ g` statement (discharged by
`rfl`), since the bare `atn2PA18` name is ambiguous in this import graph. -/
theorem INV_ARCLENGTH_p16 (y1 y3 z : ℝ) (hz1 : 0 < z) (hz2 : z < Real.pi)
    (hy1 : 0 < y1) (hy3 : 0 < y3) :
    0 < y1 ^ 2 + y3 ^ 2 - 2 * y1 * y3 * Real.cos z ∧
      z = arcLength y1 y3
        (Real.sqrt (y1 ^ 2 + y3 ^ 2 - 2 * y1 * y3 * Real.cos z)) := by
  have hcosb := cos_bounds_0_pi_p16 z hz1 hz2
  have hDpos : 0 < y1 ^ 2 + y3 ^ 2 - 2 * y1 * y3 * Real.cos z := by
    have he : y1 ^ 2 + y3 ^ 2 - 2 * y1 * y3 * Real.cos z
        = (y1 - y3) * (y1 - y3) + 2 * y1 * y3 * (1 - Real.cos z) := by ring
    rw [he]
    have h1c : 0 < 1 - Real.cos z := by linarith
    have h5 : 0 < 2 * y1 * y3 * (1 - Real.cos z) :=
      mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * y1) hy3) h1c
    linarith [mul_self_nonneg (y1 - y3)]
  refine ⟨hDpos, ?_⟩
  set D : ℝ := y1 ^ 2 + y3 ^ 2 - 2 * y1 * y3 * Real.cos z with hD
  have hsq : Real.sqrt D * Real.sqrt D = D := by
    rw [← pow_two, Real.sq_sqrt hDpos.le]
  have hpp : 0 < 2 * y1 * y3 := mul_pos (by linarith : (0:ℝ) < 2 * y1) hy3
  have hs : 0 < Real.sin z := Real.sin_pos_of_mem_Ioo ⟨hz1, hz2⟩
  have hupsv : upsXPA18 (y1 * y1) (y3 * y3) D = (2 * y1 * y3 * Real.sin z) ^ 2 := by
    simp only [upsXPA18]
    have htrig : Real.sin z ^ 2 + Real.cos z ^ 2 = 1 := Real.sin_sq_add_cos_sq z
    linear_combination
      (-(D - (y1 * y1 + y3 * y3) - 2 * y1 * y3 * Real.cos z)) * hD +
        -(2 * y1 * y3) ^ 2 * htrig
  have hY : D - y1 * y1 - y3 * y3 = -(2 * y1 * y3 * Real.cos z) := by
    rw [hD]; ring
  simp only [arcLength]
  rw [hsq, hupsv, Real.sqrt_sq (by positivity), hY]
  -- the `atn2PA18` value: `π/2 + atn2PA18 (2 y1 y3 sin z) (-(2 y1 y3 cos z)) = z`
  have key : ∀ g : ℝ → ℝ → ℝ,
      (∀ x y : ℝ, g x y = if |y| < x then Real.arctan (y / x)
        else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
        else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y) else Real.pi) →
      Real.pi / 2 + g (2 * y1 * y3 * Real.sin z) (-(2 * y1 * y3 * Real.cos z)) = z := by
    intro g hg
    rw [hg]
    set X : ℝ := 2 * y1 * y3 * Real.sin z with hX
    set Y : ℝ := -(2 * y1 * y3 * Real.cos z) with hYd
    have hXpos : 0 < X := by
      rw [hX]
      exact mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * y1) hy3) hs
    by_cases hbr : |Y| < X
    · -- branch `|Y| < X`: `arctan (Y/X) = z - π/2`
      rw [if_pos hbr]
      have hmem : z - Real.pi / 2 ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
      have h1 : Real.sin (z - Real.pi / 2) = -Real.cos z := by
        rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
      have h2 : Real.cos (z - Real.pi / 2) = Real.sin z := by
        rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
      have hsn : Real.sin z ≠ 0 := ne_of_gt hs
      have h2p : (2:ℝ) * y1 * y3 ≠ 0 := ne_of_gt hpp
      have htan : Real.tan (z - Real.pi / 2) = Y / X := by
        rw [Real.tan_eq_sin_div_cos, h1, h2, hYd, hX]
        field_simp
        try ring
      rw [show Y / X = Real.tan (z - Real.pi / 2) from htan.symm,
        Real.arctan_tan hmem.1 hmem.2]
      ring
    · -- branch `|Y| ≥ X`
      have hnlt : ¬(|Y| < X) := hbr
      have hle : X ≤ |Y| := not_lt.1 hbr
      rcases lt_trichotomy Y 0 with hYneg | hY0 | hYpos
      · -- branch `Y < 0` (so `z < π/2`): `arctan (X/Y) = -z`
        rw [if_neg hnlt, if_neg (by linarith : ¬(0 < Y)), if_pos hYneg]
        have hzlt : z < Real.pi / 2 := by
          by_contra hcon
          have hcon' : Real.pi / 2 ≤ z := not_lt.1 hcon
          have hnp : Real.cos z ≤ 0 := by
            rcases lt_or_eq_of_le hcon' with h | h
            · have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi
                (x := Real.pi / 2) (y := z) (by have := Real.pi_pos; linarith)
                hz2.le h
              rw [Real.cos_pi_div_two] at h1
              linarith
            · rw [← h, Real.cos_pi_div_two]
          have hpple : 2 * y1 * y3 * Real.cos z ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hpp.le hnp
          have : 0 ≤ Y := by rw [hYd]; linarith
          linarith
        have hmem : -z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨by linarith, by linarith⟩
        have hsn : Real.sin z ≠ 0 := ne_of_gt hs
        have hc0 : Real.cos z ≠ 0 := by
          have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi
            (x := z) (y := Real.pi / 2) hz1.le (by linarith) hzlt
          rw [Real.cos_pi_div_two] at h1
          linarith
        have htan : Real.tan (-z) = X / Y := by
          rw [Real.tan_eq_sin_div_cos, Real.sin_neg, Real.cos_neg, hX, hYd]
          field_simp
        rw [show X / Y = Real.tan (-z) from htan.symm,
          Real.arctan_tan hmem.1 hmem.2]
        linarith
      · -- `Y = 0` contradicts `X ≤ |Y|`
        exfalso
        rw [hY0] at hle
        simp at hle
        linarith
      · -- branch `0 < Y` (so `z > π/2`): `arctan (X/Y) = π - z`
        rw [if_neg hnlt, if_pos hYpos]
        have hzgt : Real.pi / 2 < z := by
          rcases lt_trichotomy z (Real.pi / 2) with h | h | h
          · exfalso
            have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi
              (x := z) (y := Real.pi / 2) hz1.le (by linarith) h
            rw [Real.cos_pi_div_two] at h1
            have hppc : 0 < 2 * y1 * y3 * Real.cos z :=
              mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * y1) hy3) h1
            have : Y < 0 := by rw [hYd]; linarith
            linarith
          · exfalso
            rw [h, Real.cos_pi_div_two] at hYd
            simp at hYd
            linarith
          · exact h
        have hmem : Real.pi - z ∈
            Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
        have hcosne : Real.cos z ≠ 0 := by
          have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi
            (x := Real.pi / 2) (y := z) (by have := Real.pi_pos; linarith)
            hz2.le hzgt
          rw [Real.cos_pi_div_two] at h1
          exact ne_of_lt h1
        have htan : Real.tan (Real.pi - z) = X / Y := by
          rw [show Real.pi - z = -z + Real.pi by ring, Real.tan_periodic,
            Real.tan_neg, Real.tan_eq_sin_div_cos, hX, hYd]
          field_simp
          try ring
        rw [show X / Y = Real.tan (Real.pi - z) from htan.symm,
          Real.arctan_tan hmem.1 hmem.2]
        linarith
  exact key (fun x y => if |y| < x then Real.arctan (y / x)
    else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
    else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y) else Real.pi)
    (fun _ _ => rfl) |>.symm

/-- HOL `taum_dih_y` (BKOSSGE.hl:168).
NEEDS: the real Terminal.hl `taum` definition (`taum_p16` is the opaque
registry signature), Sphere.sol_y / lnazim / rho unfoldings and
Nonlinear_lemma.sol0_const1. -/
theorem taum_dih_y_p16 (y1 y2 y3 y4 y5 y6 : ℝ) :
    taum_p16 y1 y2 y3 y4 y5 y6 =
      rho y1 * dihY_p16 y1 y2 y3 y4 y5 y6 +
        rho y2 * dihY_p16 y2 y3 y1 y5 y6 y4 +
        rho y3 * dihY_p16 y3 y1 y2 y6 y4 y5 - (Real.pi + sol0) := by
  sorry

/-- HOL `real_continuous_dih_y_wrt4` (BKOSSGE.hl:181).
NEEDS: Ocbicby.derived_form_dih_x_wrt_x4 (the `dih_x` derivative in the
`y4` slot, via Calc_derivative.derived_form) and the
continuity-under-composition kit. -/
theorem real_continuous_dih_y_wrt4_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY_p16 y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsXPA18 (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsXPA18 (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY_p16 y1 y2 y3 q y5 y6) y4 := by
  sorry

/-- HOL `real_continuous_dih_y_wrt5` (BKOSSGE.hl:211).
NEEDS: Ocbicby.derived_form_dih_x_wrt_x5. -/
theorem real_continuous_dih_y_wrt5_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY_p16 y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsXPA18 (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsXPA18 (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY_p16 y1 y2 y3 y4 q y6) y5 := by
  sorry

/-- HOL `real_continuous_dih_y_wrt6` (BKOSSGE.hl:241).
NEEDS: Ocbicby.derived_form_dih_x_wrt_x6. -/
theorem real_continuous_dih_y_wrt6_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY_p16 y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsXPA18 (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsXPA18 (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY_p16 y1 y2 y3 y4 y5 q) y6 := by
  sorry

/-- HOL `real_continuous_taum` (BKOSSGE.hl:271).
NEEDS: `taum_dih_y_p16` (the real `taum`), Merge_ineq.delta_y_sym /
ups_x_sym and the `real_continuous_dih_y_wrt*_p16` suite. -/
theorem real_continuous_taum_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY_p16 y1 y2 y3 y4 y5 y6)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hu1 : 0 < upsXPA18 (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsXPA18 (y2 * y2) (y3 * y3) (y4 * y4))
    (hu3 : 0 < upsXPA18 (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => taum_p16 y1 y2 y3 q y5 y6) y4 := by
  sorry

/-- HOL `UPS_X_STD_POS` (BKOSSGE.hl:291); via PackingAuto18's
`TRI_UPS_X_STRICT_POS` with the `h0 = 1.26` box. -/
theorem UPS_X_STD_POS_p16 (y1 y2 y3 : ℝ) (h1 : 2 ≤ y1) (h1' : y1 ≤ 2 * h0)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ 2 * h0) (h3 : 2 ≤ y3) (h3' : y3 ≤ 2 * h0) :
    0 < upsXPA18 (y1 * y1) (y2 * y2) (y3 * y3) := by
  have h0v : h0 = 1.26 := rfl
  exact TRI_UPS_X_STRICT_POS y1 y2 y3 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

/-! ## Section D: CQAOQLR.hl (opposite-system modular kit) -/

/-- HOL `K_SUC_2_MOD_SUB` (CQAOQLR.hl:95). -/
theorem K_SUC_2_MOD_SUB_p16 {k i : ℕ} (hk : 1 < k) :
    (k - ((i + 2) % k + 1) + 1) % k = (k - ((i + 1) % k + 1)) % k := by
  have hq : (i + 1) % k < k := Nat.mod_lt _ (by omega)
  have h3 : ((i + 1) % k + 1) % k = (i + 2) % k := Nat.mod_add_mod _ _ _
  rcases lt_or_eq_of_le (show (i + 1) % k + 1 ≤ k from by omega) with hlt | heq
  · rw [← h3, Nat.mod_eq_of_lt hlt]
    rw [Nat.mod_eq_of_lt (by omega : k - ((i + 1) % k + 1 + 1) + 1 < k)]
    rw [Nat.mod_eq_of_lt (by omega : k - ((i + 1) % k + 1) < k)]
    omega
  · rw [← h3, heq, Nat.mod_self, Nat.sub_self, Nat.zero_mod]
    have hx : k - (0 + 1) + 1 = k := by omega
    rw [hx, Nat.mod_self]

/-- HOL `K_SUC_2_MOD_SUB_ID` (CQAOQLR.hl:100). -/
theorem K_SUC_2_MOD_SUB_ID_p16 {k i : ℕ} (hk : 1 < k) :
    (k - ((i + 2) % k + 1) + 2) % k = (k - (i % k + 1)) % k := by
  have hq : i % k < k := Nat.mod_lt _ (by omega)
  have e2 : (i + 2) % k = (i % k + 2) % k := (Nat.mod_add_mod i k 2).symm
  rcases lt_trichotomy (i % k + 2) k with hlt | heq | hgt
  · rw [e2, Nat.mod_eq_of_lt hlt]
    rw [Nat.mod_eq_of_lt (by omega : k - (i % k + 2 + 1) + 2 < k)]
    rw [Nat.mod_eq_of_lt (by omega : k - (i % k + 1) < k)]
    omega
  · rw [e2, heq, Nat.mod_self]
    have hR : k - (i % k + 1) = 1 := by omega
    rw [hR, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
    have hx : k - (0 + 1) + 2 = 1 + k := by omega
    rw [hx, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : (1:ℕ) < k)]
  · have hval : (i % k + 2) % k = i % k + 2 - k := by
      have hx : i % k + 2 = (i % k + 2 - k) + k := by omega
      conv_lhs => rw [hx]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i % k + 2 - k < k)]
    rw [e2, hval]
    have hL : k - (i % k + 2 - k + 1) + 2 = k + (k - (i % k + 1)) := by omega
    rw [hL, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : k - (i % k + 1) < k)]

/-- HOL `SUC_OPP_ID` (CQAOQLR.hl:118). -/
theorem SUC_OPP_ID_p16 {k i : ℕ} (hk : 1 < k) :
    (k - (i % k + 1) + 1) % k = (k - i % k) % k := by
  have hq : i % k < k := Nat.mod_lt _ (by omega)
  rw [show k - (i % k + 1) + 1 = k - i % k by omega]

/-- HOL `A_B_J_SCS_OPP` (CQAOQLR.hl:113): the `a`/`b`/`J` slots of
`scs_opp_v39` are the `peropp2` images (the `J` clause is an `Iff` since
`scs_J_v39` is Prop-valued). -/
theorem A_B_J_SCS_OPP_p16 (s : ScsV39) :
    (∀ i j, (scsOppV39 s).a i j = s.a (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) ∧
    (∀ i j, (scsOppV39 s).b i j = s.b (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) ∧
    (∀ i j, (scsOppV39 s).J i j ↔ s.J (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => Iff.rfl⟩

/-- HOL `ELEMENT1_SYM_0` (CQAOQLR.hl:148). -/
theorem ELEMENT1_SYM_0_p16 (a : V3) : ({-a} : Set V3) = (fun x : V3 => -x) '' {a} := by
  simp

/-- HOL `SCS_GENERIC_SYM_0` (CQAOQLR.hl:156).
NEEDS: the Xwitccn / In_sym_0 symmetry kit — OPP_IMAGE_V_EQ_NEG,
OPP_IMAGE_E_EQ_NEG, ELEMENT2_SYM_0, AFF_GE_VEC0_SYM_0,
AFF_LT_VEC0_SYM_0, REFL_SYM_0, SET_EQ_SYM_0 — none of it is in the
corpus yet. -/
theorem SCS_GENERIC_SYM_0_p16 (s : ScsV39) (v : ℕ → V3) (h1 : BBsV39 s v)
    (h2 : isScsV39 s) (h3 : scsGeneric v) :
    scsGeneric (fun i => -(v (s.k - (i % s.k + 1)))) := by
  sorry

/-- HOL `CQAOQLR_concl` (CQAOQLR.hl:233, term-level `let` registry). -/
def CQAOQLR_concl_p16 : Prop :=
  main_nonlinear_terminal_v11 → ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
    3 < s.k →
    isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → 2 < s.b (i + 1) (i + 2) →
    s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    s.a (i + s.k - 1) i < s.b (i + s.k - 1) i →
    s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    (dist (v i) (v (i + 1)) = 2 ↔ dist (v (i + 1)) (v (i + 2)) = 2)

/-- HOL `UNADORNED_OPP` (CQAOQLR.hl:175). -/
theorem UNADORNED_OPP_p16 (s : ScsV39) (_h1 : isScsV39 s) (h2 : unadornedV39 s) :
    unadornedV39 (scsOppV39 s) := by
  obtain ⟨hlo, hhi, hstr, ha, hb⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp [scsOppV39, peropp, hlo]
  · funext i; simp [scsOppV39, peropp, hhi]
  · funext i; simp [scsOppV39, peropp, hstr]
  · funext i j; simp [scsOppV39, peropp2, ha]
  · funext i j; simp [scsOppV39, peropp2, hb]

/-- HOL `BASIC_OPP` (CQAOQLR.hl:181). -/
theorem BASIC_OPP_p16 (s : ScsV39) (h1 : isScsV39 s) (h2 : scsBasicV39 s) :
    scsBasicV39 (scsOppV39 s) := by
  obtain ⟨hu, hJ⟩ := h2
  exact ⟨UNADORNED_OPP_p16 s h1 hu, fun i j => by simp [scsOppV39, peropp2, hJ]⟩

/-- HOL `DIAG_OPP` (CQAOQLR.hl:186): diagonality is preserved under the
opposite-system index map `n ↦ k - SUC (n mod k)`. -/
theorem DIAG_OPP_p16 (k i j : ℕ) (hk : 3 < k) (h : scsDiag k i j) :
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

/-- HOL `K_SUC_2_MOD_F_SUB_ID` (CQAOQLR.hl:133).
NEEDS: the HOL `SUC_MOD_EQ_MOD_SUC` / `MOD_SUC_MOD` modular-kit route
(the `i + k - 1` slot needs the `i % k = 0` / `i % k ≥ 1` split on
`(i + k - 1) % k`, which resists a short `omega` rendering). -/
theorem K_SUC_2_MOD_F_SUB_ID_p16 {k i : ℕ} (hk : 1 < k) :
    (k - ((i + 2) % k + 1) + 3) % k = (k - ((i + k - 1) % k + 1)) % k := by
  sorry

/-- HOL `CQAOQLR` (CQAOQLR.hl:247): the ear-reciprocity conclusion.
NEEDS: TFITSKC, MM_SCS_OPP, OPP_IS_SCS, SCS_GENERIC_SYM_0_p16,
BASIC_OPP_p16, MMS_IMP_BBS, CHANGE_W_IN_BBS_MOD_IS_SCS,
CHANGE_A/B_SCS_MOD, DIAG_OPP_p16 — the CQAOQLR assembly. -/
theorem CQAOQLR_p16 : CQAOQLR_concl_p16 := by
  sorry

/-! Coverage note: every JEJTVGB.hl / XIVPHKS.hl / BKOSSGE.hl /
CQAOQLR.hl item is carried above.  Proved: SCS_ARROW_TRANS_SING,
lp_main_estimate_JEJTVGB, nonlinear_imp_lp_main_estimate,
cos_bounds_0_pi, INV_ARCLENGTH, UPS_X_STD_POS, K_SUC_2_MOD_SUB,
K_SUC_2_MOD_SUB_ID, SUC_OPP_ID, A_B_J_SCS_OPP, ELEMENT1_SYM_0,
UNADORNED_OPP, BASIC_OPP, DIAG_OPP (14).  Sorried (giants / registry):
JEJTVGB_case_breakdown, JEJTVGB, FSQKWKK, XIVPHKS, XIVPHKS_SHIFT,
ear_acute, quad_nonexist_849, quad_diag_362, taum_dih_y,
real_continuous_dih_y_wrt4/5/6, real_continuous_taum, BKOSSGE,
SCS_GENERIC_SYM_0, K_SUC_2_MOD_F_SUB_ID, CQAOQLR (16), plus the
opaque `taum_p16` signature. -/
