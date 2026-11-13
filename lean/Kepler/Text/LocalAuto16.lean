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
    `JEJTVGB_case_breakdown_p16`, the definition `lp_main_estimate`,
    `lp_main_estimate_JEJTVGB_p16`.  (`JEJTVGB_p16` and
    `nonlinear_imp_lp_main_estimate_p16` upshifted to `LocalConcl` verbatim
    on 2026-11-12, lane defix-small-w1 DEF-FIX 1B: they consume `OEHDBEN`,
    which moved there with the SCS_6I1 chain and which LA16 cannot reach --
    `LocalConcl` imports this file, so the import would cycle.)
  Section B (XIVPHKS): moved verbatim to `Kepler.Text.XivphksKit`
    (`FSQKWKK_p16`, `XIVPHKS_p16`, `XIVPHKS_SHIFT_p16`), re-exported
    through the import below.
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
  - DEDUP 2026-09-17: the sphere.hl kit is single-sourced in
    `Kepler.Text.SphereKit`; the seven verbatim `_p16` copies that used to
    sit here (the `atn2`/`deltaX`/`deltaX4`/`dihXf`/`dihY`/`deltaY` twins
    and the opaque `taum` registry-signature stub) were deleted against it
    after verifying every body identical (the `taum` stub was upgraded to
    SphereKit's real `taum` body).  Uses resolve via the SphereKit import.
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
    as in LocalAuto1).  The remaining giants keep `sorry` bodies: the
    23-arrow breakdown (NEEDS the terminal-arrows-to-empty theorem
    OCBICBY, `s_init_list_alt` and `scs_arrow_sing_empty`), both
    XIVPHKS inductions (NEEDS `sum3/4/5_azim_fan`,
    `AZIM_DIHV_SAME_STRONG`, the Localization wedge kit), the
    continuity suite `real_continuous_dih_y_wrt4/5/6` /
    `real_continuous_taum`, and the assembly giant `CQAOQLR_p16`
    (NEEDS TFITSKC / MM_SCS_OPP / OPP_IS_SCS / CHANGE_*_SCS_MOD).
    Wave w15 (`la16-gap-w1`, 2026-11-05) closed `ear_acute`, the quad
    pair `quad_nonexist_849` / `quad_diag_362`, `taum_dih_y` and
    `K_SUC_2_MOD_F_SUB_ID`; wave w17 (`la16-sym-w1`, 2026-11-05) closed
    `SCS_GENERIC_SYM_0`.

DISCHARGES: `BKOSSGE_p16` is verbatim
  `LocalAuto1.BKOSSGE_concl` (`scsArrowV39 {scs3M1} {scs3T1, scs3T5}`);
when the BKOSSGE wave lands, that appendix sorry disappears through
this file.  All other items here discharge nothing yet.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto20
import Kepler.Text.LocalAuto21
-- MOVED-decl consumer (dagcut-w2): `taum_dih_y_p16` now lives in
-- LocalAuto21; LA16 keeps using it (LA16:1349) and `#print axioms`
-- (LA16:1843) through this import. Acyclic: LA21 no longer imports LA16.
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto27
import Kepler.Text.LocalAuto28
-- LA1 root unlock (lane la1-bimport-w1): the clean `*_p33` donors
-- (`AUEAHEH_p33`, `VQFYMZY_p33`, `BNAWVNH_p33`, `RAWZDIB_p33`,
-- `MFKLVDK_p33`, `RYPDIXT_p33`) live in LocalAuto33, which this module
-- could not previously see.  Static import DAG: no path LA33 ->* LA16.
import Kepler.Text.LocalAuto33
import Kepler.Text.SphereKit
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto7
import Kepler.Text.XivphksKit
import Kepler.Text.TopologyFan
-- vasw0-w1 (2026-11-13): `MM_SCS_OPP_fb` for the CQAOQLR opposite-system
-- direction.  Acyclic: FanBaseKit imports only LA1/LA3/AzimLemmas, none of
-- which reaches LA16.
import Kepler.Text.FanBaseKit
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section A: JEJTVGB.hl (appendix, main estimate, check completeness) -/

/-! ### p16h_* helper block (JEJTVGB wave; pure addition, zero-taint kit)

Assembly kit closing `BKOSSGE_p16` and `JEJTVGB_case_breakdown_p16`
(HOL BKOSSGE.hl:304-396 / JEJTVGB.hl:23-230); the assembled `JEJTVGB_p16`
(and its consumer `nonlinear_imp_lp_main_estimate_p16`) upshifted to
`LocalConcl` verbatim on 2026-11-12 (lane defix-small-w1, DEF-FIX 1B),
since they consume `OEHDBEN`, which moved there with the SCS_6I1 chain.
Every item
here is self-contained: no `main_nonlinear_terminal_v11` premise, no
sorried upstream arrow is *declared* here (the sorried arrows are only
*consumed* at the assembly sites, as the ledger allows).  Consumed
upstream (assembly level): LocalAuto22.OCBICBY_p22 / scs_arrow_sing_empty_p22 /
is_scs_3{M1,T1,T5}_p22, LocalAuto23.s_init_list_alt_p23 / LFLACKU_p23,
LocalAuto26.XWNHLMD_MM_p26, LocalAuto27.EAPGLE_p27, LocalAuto28.MMS_IMP_BBS_p28. -/

/-- `scsBasicV39` holds for every `mkUnadornedV39` system: it is plainly
unadorned (`a = am`, `b = bm`, `lo = hi = str = False`) and its `J` is
everywhere `False`. -/
theorem p16h_basic_mk (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) :
    scsBasicV39 (mkUnadornedV39 k d a b) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- Residues mod 3 exhaust the three classes. -/
theorem p16h_mod3_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega

/-- Periodicity transport for the 3-systems: a 3-periodic list is a
function of its residue. -/
theorem p16h_periodic3 {v : ℕ → V3} (hp : Periodic v 3) (i : ℕ) :
    v i = v (i % 3) := by
  have step : ∀ n m : ℕ, v (m + n * 3) = v m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ k ih =>
        intro m
        have he : m + (k + 1) * 3 = (m + k * 3) + 3 := by
          rw [Nat.succ_mul, Nat.add_assoc]
        rw [he, hp]
        exact ih m
  have hstep := step (i / 3) (i % 3)
  have he : i % 3 + (i / 3) * 3 = i := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div i 3
  rw [he] at hstep
  exact hstep

/-- Slot table of `scs3M1`'s lower matrix (`funlist [(0,1) ↦ 2*h0] 2 3`). -/
theorem p16h_a_3M1 (i j : ℕ) : scs3M1.a i j =
    (if i % 3 = j % 3 then 0
      else if psort 3 (i, j) = psort 3 (0, 1) then 2 * h0 else 2) := rfl

/-- Slot table of `scs3M1`'s upper matrix (`funlist [(0,1) ↦ cstab] (2*h0) 3`). -/
theorem p16h_b_3M1 (i j : ℕ) : scs3M1.b i j =
    (if i % 3 = j % 3 then 0
      else if psort 3 (i, j) = psort 3 (0, 1) then cstab else 2 * h0) := rfl

/-- Slot table of `scs3T1`'s lower matrix (`funlist [(0,1) ↦ sqrt8] 2 3`). -/
theorem p16h_a_3T1 (i j : ℕ) : scs3T1.a i j =
    (if i % 3 = j % 3 then 0
      else if psort 3 (i, j) = psort 3 (0, 1) then Real.sqrt 8 else 2) := rfl

/-- Slot table of `scs3T5`'s upper matrix (`funlist [(0,1) ↦ sqrt8] (2*h0) 3`). -/
theorem p16h_b_3T5 (i j : ℕ) : scs3T5.b i j =
    (if i % 3 = j % 3 then 0
      else if psort 3 (i, j) = psort 3 (0, 1) then Real.sqrt 8 else 2 * h0) := rfl

/-- The `(0, 1)`-class of `psort 3` spelled out. -/
theorem p16h_psort01 (i j : ℕ) :
    (psort 3 (i, j) = psort 3 (0, 1) ↔
      i % 3 = 0 ∧ j % 3 = 1 ∨ i % 3 = 1 ∧ j % 3 = 0) := by
  show (if i % 3 ≤ j % 3 then (i % 3, j % 3) else (j % 3, i % 3)) =
      (if (0:ℕ) % 3 ≤ 1 % 3 then (0 % 3, 1 % 3) else (1 % 3, 0 % 3)) ↔ _
  by_cases h : i % 3 ≤ j % 3
  · rw [if_pos h, if_pos (by omega), Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · omega
  · push_neg at h
    rw [if_neg (by omega), if_pos (by omega), Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · omega
      · exact ⟨h2, h1⟩

/-- BBs transport `scs3M1 → scs3T5` on the `dist(v 0, v 1) ≤ sqrt8` branch:
the two systems share `k`, `d` and the whole `a` matrix, and their `b`
matrices agree off the `(0, 1)` class (HOL BKOSSGE.hl:326-374). -/
theorem p16h_bbs_3T5 {v : ℕ → V3} (hv : BBsV39 scs3M1 v)
    (hd : dist (v 0) (v 1) ≤ Real.sqrt 8) : BBsV39 scs3T5 v := by
  have hper : ∀ i : ℕ, v i = v (i % 3) := fun i => p16h_periodic3 hv.2.1 i
  have hub : ∀ i j, dist (v i) (v j) ≤ scs3T5.b i j := by
    intro i j
    rcases p16h_mod3_cases i with hi | hi | hi <;>
      rcases p16h_mod3_cases j with hj | hj | hj <;>
      rw [p16h_b_3T5, hper i, hper j] <;>
      simp only [p16h_psort01, hi, hj, reduceIte] <;>
      first
        | exact hd
        | (rw [dist_comm]; exact hd)
        | exact (hv.2.2.1 0 2).2
        | exact (hv.2.2.1 1 2).2
        | exact (hv.2.2.1 2 0).2
        | exact (hv.2.2.1 2 1).2
        | simp
  exact ⟨hv.1, hv.2.1, fun i j => And.intro (hv.2.2.1 i j).1 (hub i j),
    Or.inl (le_refl _)⟩

/-- BBs transport `scs3M1 → scs3T1` on the `sqrt8 ≤ dist(v 0, v 1)` branch:
the two systems share `k` and the whole `b` matrix, and their `a` matrices
agree off the `(0, 1)` class (HOL BKOSSGE.hl:376-395). -/
theorem p16h_bbs_3T1 {v : ℕ → V3} (hv : BBsV39 scs3M1 v)
    (hd : Real.sqrt 8 ≤ dist (v 0) (v 1)) : BBsV39 scs3T1 v := by
  have hper : ∀ i : ℕ, v i = v (i % 3) := fun i => p16h_periodic3 hv.2.1 i
  have hlo : ∀ i j, scs3T1.a i j ≤ dist (v i) (v j) := by
    intro i j
    rcases p16h_mod3_cases i with hi | hi | hi <;>
      rcases p16h_mod3_cases j with hj | hj | hj <;>
      rw [p16h_a_3T1, hper i, hper j] <;>
      simp only [p16h_psort01, hi, hj, reduceIte] <;>
      first
        | exact hd
        | (rw [dist_comm]; exact hd)
        | exact (hv.2.2.1 0 2).1
        | exact (hv.2.2.1 1 2).1
        | exact (hv.2.2.1 2 0).1
        | exact (hv.2.2.1 2 1).1
        | simp
  exact ⟨hv.1, hv.2.1, fun i j => And.intro (hlo i j) ((hv.2.2.1 i j).2),
    Or.inl (le_refl _)⟩

/-- HOL `BKOSSGE` (BKOSSGE.hl:304), stated here because `JEJTVGB_p16`
consumes it; the proof body sits in Section C.  Verbatim
`LocalAuto1.BKOSSGE_concl` (appendix.hl:1564). -/
theorem BKOSSGE_p16 : scsArrowV39 {scs3M1} {scs3T1, scs3T5} := by
  refine ⟨fun s hs => ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact is_scs_3T1_p22
    · exact is_scs_3T5_p22
  · rcases Classical.em (MMsV39 scs3M1 = ∅) with hE | hNE
    · refine Or.inl (fun s' hs' => ?_)
      simp only [Set.mem_singleton_iff] at hs'
      subst hs'
      exact hE
    · obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hNE
      have hbb : BBsV39 scs3M1 v := MMS_IMP_BBS_p28 scs3M1 v hv
      rcases le_or_gt (dist (v 0) (v 1)) (Real.sqrt 8) with hle | hlt
      · refine Or.inr ⟨scs3T5, by simp, ?_⟩
        exact XWNHLMD_MM_p26 scs3M1 scs3T5 v is_scs_3M1_p22 is_scs_3T5_p22
          (p16h_basic_mk _ _ _ _) (p16h_basic_mk _ _ _ _) rfl hv
          (p16h_bbs_3T5 hbb hle) (le_refl _)
      · refine Or.inr ⟨scs3T1, by simp, ?_⟩
        exact XWNHLMD_MM_p26 scs3M1 scs3T1 v is_scs_3M1_p22 is_scs_3T1_p22
          (p16h_basic_mk _ _ _ _) (p16h_basic_mk _ _ _ _) rfl hv
          (p16h_bbs_3T1 hbb (le_of_lt hlt))
          (show ((0.103:ℝ) ≤ 0.11) by norm_num)

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

/-- One-step transitivity through a one-element target list. -/
theorem p16h_kill1 (a x1 : ScsV39) (h : scsArrowV39 {a} ({x1} : Set ScsV39))
    (h1 : scsArrowV39 {x1} (∅ : Set ScsV39)) : scsArrowV39 {a} (∅ : Set ScsV39) :=
  scsArrowTransSing_p16 a _ h (by
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact h1)

/-- One-step transitivity through a two-element target list. -/
theorem p16h_kill2 (a x1 x2 : ScsV39)
    (h : scsArrowV39 {a} ({x1, x2} : Set ScsV39))
    (h1 : scsArrowV39 {x1} (∅ : Set ScsV39)) (h2 : scsArrowV39 {x2} (∅ : Set ScsV39)) :
    scsArrowV39 {a} (∅ : Set ScsV39) :=
  scsArrowTransSing_p16 a _ h (by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2)

/-- One-step transitivity through a three-element target list. -/
theorem p16h_kill3 (a x1 x2 x3 : ScsV39)
    (h : scsArrowV39 {a} ({x1, x2, x3} : Set ScsV39))
    (h1 : scsArrowV39 {x1} (∅ : Set ScsV39)) (h2 : scsArrowV39 {x2} (∅ : Set ScsV39))
    (h3 : scsArrowV39 {x3} (∅ : Set ScsV39)) : scsArrowV39 {a} (∅ : Set ScsV39) :=
  scsArrowTransSing_p16 a _ h (by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3)

/-- One-step transitivity through a four-element target list. -/
theorem p16h_kill4 (a x1 x2 x3 x4 : ScsV39)
    (h : scsArrowV39 {a} ({x1, x2, x3, x4} : Set ScsV39))
    (h1 : scsArrowV39 {x1} (∅ : Set ScsV39)) (h2 : scsArrowV39 {x2} (∅ : Set ScsV39))
    (h3 : scsArrowV39 {x3} (∅ : Set ScsV39)) (h4 : scsArrowV39 {x4} (∅ : Set ScsV39)) :
    scsArrowV39 {a} (∅ : Set ScsV39) :=
  scsArrowTransSing_p16 a _ h (by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4)

/-- One-step transitivity through a ten-element target list (the `HIJQAHA`
slot). -/
theorem p16h_kill10 (a x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ScsV39)
    (h : scsArrowV39 {a} ({x1, x2, x3, x4, x5, x6, x7, x8, x9, x10} : Set ScsV39))
    (h1 : scsArrowV39 {x1} (∅ : Set ScsV39)) (h2 : scsArrowV39 {x2} (∅ : Set ScsV39))
    (h3 : scsArrowV39 {x3} (∅ : Set ScsV39)) (h4 : scsArrowV39 {x4} (∅ : Set ScsV39))
    (h5 : scsArrowV39 {x5} (∅ : Set ScsV39)) (h6 : scsArrowV39 {x6} (∅ : Set ScsV39))
    (h7 : scsArrowV39 {x7} (∅ : Set ScsV39)) (h8 : scsArrowV39 {x8} (∅ : Set ScsV39))
    (h9 : scsArrowV39 {x9} (∅ : Set ScsV39))
    (h10 : scsArrowV39 {x10} (∅ : Set ScsV39)) : scsArrowV39 {a} (∅ : Set ScsV39) :=
  scsArrowTransSing_p16 a _ h (by
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10)

/-- Arrow transport along set equalities (the `_concl` registry sometimes
enumerates an arrow's target set in a different order than the frozen
breakdown slots). -/
theorem p16h_arrow_congr {S1 S2 S1' S2' : Set ScsV39}
    (ha : scsArrowV39 S1 S2) (h1 : S1 = S1') (h2 : S2 = S2') :
    scsArrowV39 S1' S2' := by
  rw [← h1, ← h2]; exact ha


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
  -- OCBICBY: the 14 T-row systems arrow to the empty system (HOL JEJTVGB.hl:62).
  obtain ⟨o61, o51, o41, o42, o43, o44, o45, o31, -, o33, o34, o35, o36, o37⟩ :=
    OCBICBY_p22 h
  -- The SCS_ARROW_TRANS_SING walk (HOL JEJTVGB.hl:64-215), bottoms up.
  have e3M1 : scsArrowV39 {scs3M1} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a23 o31 o35
  have e46 : scsArrowV39 {scs4M6'} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a20 o43 o45
  have e47 : scsArrowV39 {scs4M7} (∅ : Set ScsV39) :=
    p16h_kill4 _ _ _ _ _ a21 e46 o33 e3M1 o34
  have e48 : scsArrowV39 {scs4M8} (∅ : Set ScsV39) :=
    p16h_kill3 _ _ _ _ a22 e46 o37 o34
  have e45 : scsArrowV39 {scs4M5'} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a19 e48 o34
  have e44 : scsArrowV39 {scs4M4'} (∅ : Set ScsV39) :=
    p16h_kill4 _ _ _ _ _ a18 e47 o33 e3M1 o34
  have e43 : scsArrowV39 {scs4M3'} (∅ : Set ScsV39) :=
    p16h_kill3 _ _ _ _ a17 e46 o31 o36
  have e42 : scsArrowV39 {scs4M2} (∅ : Set ScsV39) :=
    p16h_kill3 _ _ _ _ a16 e46 e3M1 o34
  have e4I3 : scsArrowV39 {scs4I3} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a15 e46 o44
  have eSD41 : scsArrowV39 {scsStabDiagV39 scs4I1 0 2} (∅ : Set ScsV39) :=
    p16h_kill1 _ _ a14 e3M1
  have e4I2 : scsArrowV39 {scs4I2} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a13 o41 o42
  have e4I1 : scsArrowV39 {scs4I1} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a12 e4I2 eSD41
  have eSD52 : scsArrowV39 {scsStabDiagV39 scs5M1 2 4} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a11 e3M1 e45
  have eSD53 : scsArrowV39 {scsStabDiagV39 scs5M1 0 3} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a10 e44 e3M1
  have eSD51 : scsArrowV39 {scsStabDiagV39 scs5M1 0 2} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a09 o34 e42
  have eSDI52 : scsArrowV39 {scsStabDiagV39 scs5I2 0 2} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a08 o31 e43
  have eSDI51 : scsArrowV39 {scsStabDiagV39 scs5I1 0 2} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a07 e3M1 e42
  have e5M2 : scsArrowV39 {scs5M2} (∅ : Set ScsV39) :=
    p16h_kill10 _ _ _ _ _ _ _ _ _ _ _ a06 o51 eSDI52 eSD51 eSD53 eSD52 e46 e47 e48
      o31 o34
  have e5M1 : scsArrowV39 {scs5M1} (∅ : Set ScsV39) :=
    p16h_kill4 _ _ _ _ _ a05 eSD51 eSD53 eSD52 e5M2
  have e5I3 : scsArrowV39 {scs5I3} (∅ : Set ScsV39) :=
    p16h_kill4 _ _ _ _ _ a04 eSD51 eSD53 eSD52 e5M2
  have e5I2 : scsArrowV39 {scs5I2} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a03 eSDI52 e5M2
  have e5I1 : scsArrowV39 {scs5I1} (∅ : Set ScsV39) :=
    p16h_kill2 _ _ _ a02 eSDI51 e5M2
  have e6I1 : scsArrowV39 {scs6I1} (∅ : Set ScsV39) :=
    p16h_kill4 _ _ _ _ _ a01 o61 e5M1 e42 e3M1
  -- Final kill (HOL JEJTVGB.hl:217): EAPGLE + s_init_list_alt + LFLACKU.
  refine EAPGLE_p27 ?_
  intro s hs
  rw [s_init_list_alt_p23] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (scs_arrow_sing_empty_p22 scs6I1).1 e6I1
  · exact (scs_arrow_sing_empty_p22 scs5I1).1 e5I1
  · exact (scs_arrow_sing_empty_p22 scs4I1).1 e4I1
  · exact (scs_arrow_sing_empty_p22 scs3I1).1 (LFLACKU_p23 h)
  · exact (scs_arrow_sing_empty_p22 scs5I2).1 e5I2
  · exact (scs_arrow_sing_empty_p22 scs4I2).1 e4I2
  · exact (scs_arrow_sing_empty_p22 scs5I3).1 e5I3
  · exact (scs_arrow_sing_empty_p22 scs4I3).1 e4I3

/-- HOL `lp_main_estimate` (JEJTVGB.hl:232, `new_definition` of the
equation with `Appendix.JEJTVGB_concl`). -/
def lp_main_estimate : Prop := JEJTVGB_concl

/-- HOL `lp_main_estimate_JEJTVGB` (JEJTVGB.hl:236). -/
theorem lp_main_estimate_JEJTVGB_p16 :
    JEJTVGB_assume_v39 ↔ lp_main_estimate := Iff.rfl

/-! ## Section B: XIVPHKS.hl (moved to `Kepler.Text.XivphksKit`)

The sine-of-azimuth algebra kit, `FSQKWKK_p16`, `XIVPHKS_p16` and
`XIVPHKS_SHIFT_p16` were extracted verbatim (2026-11-05) into the
shared module `Kepler.Text.XivphksKit`, so that `LocalAuto14` can
consume them without the `LocalAuto16 → LocalAuto27 → LocalAuto14`
import cycle.  The declaration names are unchanged and re-exported
here through the import above. -/


/-! ## Section C: BKOSSGE.hl -/

-- DEDUP 2026-09-17: the seven verbatim sphere-kit `_p16` copies that used
-- to sit here (the `atn2`/`deltaX`/`deltaX4`/`dihXf`/`dihY`/`deltaY` twins
-- and the opaque `taum` registry-signature stub) are deleted against the
-- canonical `Kepler.Text.SphereKit` definitions; every body was verified
-- identical before deletion (the `taum` stub upgrades to SphereKit's real
-- `taum` body).  Remaining uses resolve through the SphereKit import.

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

/-- Helper (ported 2026-11-05 from LA33's `atn2_neg_of_y_neg_p33`):
`atn2 x y` is negative whenever `y < 0` (both branches of the
definition). -/
private theorem atn2_neg_of_y_neg_p16 {x y : ℝ} (hy : y < 0) : atn2 x y < 0 := by
  unfold atn2
  by_cases h : |y| < x
  · rw [if_pos h]
    refine Real.arctan_lt_zero.mpr ?_
    exact div_neg_of_neg_of_pos hy (by linarith [abs_nonneg y])
  · rw [if_neg h, if_neg (by linarith), if_pos hy]
    have := Real.neg_pi_div_two_lt_arctan (x / y)
    linarith

/-- Helper (ported 2026-11-05 from LA33's `upsX_factor_p33`): the
upsilon determinant factors as a Heron product. -/
private theorem upsX_factor_p16 (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c) = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  unfold upsX
  ring

/-- Helper (ported 2026-11-05 from LA33's `ups_triangle_p33`):
`ups_x a² b² c² > 0` forces the triangle inequality `c < a + b`. -/
private theorem ups_triangle_p16 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 0 < upsX (a * a) (b * b) (c * c)) : c < a + b := by
  by_contra hle
  push_neg at hle
  have hfac := upsX_factor_p16 a b c
  have h4 : a + b - c ≤ 0 := by linarith
  have h2 : 0 < -a + b + c := by nlinarith
  have h3 : 0 < a - b + c := by nlinarith
  have h1 : 0 < a + b + c := by linarith
  have hprod : 0 < (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
    rw [← hfac]
    simpa only [pow_two] using h
  have hnonpos : (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) ≤ 0 := by
    have hab : 0 ≤ (a + b + c) * (-a + b + c) * (a - b + c) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hab h4
  linarith

/-- HOL `ear_acute` (BKOSSGE.hl:33).  PROVED 2026-11-05 (`la16-gap-w1`):
proof body ported verbatim from LA33's `ear_acute_p33`
(standard-three); the registry instance `2485876245a` comes from the
hypothesis `main_nonlinear_terminal_v11`, and the `dihY`/atn2 rendering
plus the Heron factorization of `upsX` close the bound. -/
theorem ear_acute_p16 (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      2 ≤ y4 → y4 ≤ 2 * h0 → 2 ≤ y6 → y6 ≤ 2 * h0 → 3 ≤ y5 →
      0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) →
      dihY y1 y2 y3 y4 y5 y6 < Real.pi / 2 := by
  intro y1 y2 y3 y4 y5 y6 hy1 hy1u hy2 hy2u hy3 hy3u hy4 hy4u hy6 hy6u hy5 hups
  have h0val : h0 = (1.26 : ℝ) := rfl
  have h2h0 : (2 : ℝ) * h0 = 2.52 := by rw [h0val]; norm_num
  have h1pos : (0 : ℝ) < y1 := by linarith
  have h3pos : (0 : ℝ) < y3 := by linarith
  have h5pos : (0 : ℝ) < y5 := by linarith
  have hupper : y5 < y1 + y3 := ups_triangle_p16 h1pos h3pos h5pos hups
  have hy5u : y5 ≤ 2 * (2.52 : ℝ) := by
    have h1u : y1 ≤ 2 * h0 := hy1u
    have h3u : y3 ≤ 2 * h0 := hy3u
    nlinarith
  -- registry entry
  have hreg : mainEstimate_2485876245a :=
    h "2485876245a" (by simp [mainNonlinearTerminalV11Ids_t11])
  have hdelta : 0 < delta4Y y1 y2 y3 y4 y5 y6 :=
    hreg y1 y2 y3 y4 y5 y6 hy1 (by rw [← h2h0]; exact hy1u) hy2 (by rw [← h2h0]; exact hy2u)
      hy3 (by rw [← h2h0]; exact hy3u) hy4 (by rw [← h2h0]; exact hy4u) (by linarith) hy5u
      hy6 (by rw [← h2h0]; exact hy6u)
  -- unfold dihY into its atn2 form
  have hdih : dihY y1 y2 y3 y4 y5 y6
      = Real.pi / 2 + atn2
          (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
          (-(delta4Y y1 y2 y3 y4 y5 y6)) := by
    simp only [dihY, dihXf, deltaY, delta4Y, yOfX]
  rw [hdih]
  have hneg : atn2 (Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
      (-(delta4Y y1 y2 y3 y4 y5 y6)) < 0 :=
    atn2_neg_of_y_neg_p16 (by linarith)
  linarith

/-! ### `DELTA_Y_POS_4POINTS` kit (ported 2026-11-05 from LA38)

The quad registry pair below needs the Cayley–Menger nonnegativity
`DELTA_Y_POS_4POINTS`; LA16's import face does not contain it (and
importing `LocalAuto38` would drag 36 unrelated sorries into the
dependency graph), so the proved LA38 kit is copied here as a private
block: `p16_cos_law`, `p16_deltaX_gram_aux`, `p16_det_gram_eq`,
`p16_det_gram_nn` and `p16_deltaY_pos_4` (all standard-three in LA38),
with the wrapper `DELTA_Y_POS_4POINTS_p16`.  Bodies are verbatim except
for the `p38_` → `p16_` rename. -/

private theorem p16_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem p16_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem p16_coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

/-- The cosine law — `2·(x⬝y)` from the squared lengths. -/
private theorem p16_cos_law (x y : V3) :
    2 * (x ⬝ᵥ y) = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - dist x y * dist x y := by
  have h1 : dist x y * dist x y
      = ((x - y : V3) : Fin 3 → ℝ) ⬝ᵥ ((x - y : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two]
    exact norm_sq_eq_dot (x - y)
  have h2 : ‖x‖ * ‖x‖ = (x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  have h3 : ‖y‖ * ‖y‖ = (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  rw [h1, h2, h3, p16_coe_sub]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm]
  ring

/-- The Gram-form of `delta_x` with the Gram entries given directly
(`2p = a+b−f`, `2q = a+c−e`, `2r = b+c−d`). -/
private theorem p16_deltaX_gram_aux (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    deltaX a b c d e f =
      4 * (a * (b * c - r ^ 2) - p * (p * c - q * r) + q * (p * r - b * q)) := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX]
  ring

/-- The Gram determinant of three vectors equals the determinant of the
matrix with those rows, squared. -/
private theorem p16_det_gram_eq (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w))
      = Matrix.det
          (Matrix.of fun i j =>
            (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
              (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j) := by
  rw [Matrix.det_fin_three]
  simp [dotProduct, Matrix.of_apply, mul_comm]
  ring

private theorem p16_det_gram_nn (u v w : Fin 3 → ℝ) :
    0 ≤ u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w)) := by
  have hdet := p16_det_gram_eq u v w
  have hGM : (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j)
      = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) *
        (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i) := by
    ext i j
    simp [Matrix.mul_apply, dotProduct, Matrix.of_apply]
  have hdMt : Matrix.det (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
      = Matrix.det (Matrix.of fun i j =>
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) := by
    rw [← show Matrix.transpose (Matrix.of fun i j =>
          (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
        = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) from rfl,
      Matrix.det_transpose]
  rw [hdet, hGM, Matrix.det_mul, hdMt]
  linarith [sq_nonneg (Matrix.det (Matrix.of fun i j =>
    (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j)), pow_two (Matrix.det (Matrix.of
    fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j))]

/-- Cayley–Menger nonnegativity for a tetrahedron with apex `0` — the
`DELTA_Y_POS_4POINTS` content. -/
private theorem p16_deltaY_pos_4 (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) := by
  have hA : dist v0 v1 * dist v0 v1
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v1 - v0)
  have hB : dist v0 v2 * dist v0 v2
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v2 - v0)
  have hC : dist v0 v3 * dist v0 v3
      = ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v3 - v0)
  have hP : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v2 * dist v1 v2 := by
    have hc := p16_cos_law (v1 - v0) (v2 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hB] at hc
    rw [show dist v1 v2 = dist (v1 - v0) (v2 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hQ : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v3 * dist v1 v3 := by
    have hc := p16_cos_law (v1 - v0) (v3 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hC] at hc
    rw [show dist v1 v3 = dist (v1 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hR : 2 * (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v2 v3 * dist v2 v3 := by
    have hc := p16_cos_law (v2 - v0) (v3 - v0)
    rw [show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hB, hC] at hc
    rw [show dist v2 v3 = dist (v2 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  rw [deltaY, hA, hB, hC,
    p16_deltaX_gram_aux
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (dist v2 v3 * dist v2 v3) (dist v1 v3 * dist v1 v3)
      (dist v1 v2 * dist v1 v2)
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      hP hQ hR]
  linarith [p16_det_gram_nn ((v1 - v0 : V3) : Fin 3 → ℝ)
    ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ)]

/-- HOL `DELTA_Y_POS_4POINTS` (terminal.hl:537), ported from LA38
(standard-three): the Cayley–Menger nonnegativity used by the quad
registry pair below. -/
private theorem DELTA_Y_POS_4POINTS_p16 (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) :=
  p16_deltaY_pos_4 v0 v1 v2 v3

/-- HOL `quad_nonexist_849` (BKOSSGE.hl:69).  PROVED 2026-11-05
(`la16-gap-w1`): project the `8495326405` registry entry at
`(d34, d23, d13, d12, d14, d24)`, use the triangle bound for the two
long diagonals, and contradict `DELTA_Y_POS_4POINTS_p16`. -/
theorem quad_nonexist_849_p16 (h : main_nonlinear_terminal_v11) :
    ¬ ∃ (v1 v2 v3 v4 : V3), dist v1 v2 = 2 ∧ dist v2 v3 = 2 ∧ dist v3 v4 = 2 ∧
      dist v1 v4 = 2 * h0 ∧ cstab ≤ dist v1 v3 ∧ cstab ≤ dist v2 v4 := by
  rintro ⟨v1, v2, v3, v4, h12, h23, h34, h14, h13, h24⟩
  have hreg : mainEstimate_8495326405 :=
    h "8495326405" (by simp [mainNonlinearTerminalV11Ids_t11])
  have hpos := DELTA_Y_POS_4POINTS_p16 v3 v4 v2 v1
  have hneg : deltaY 2 2 (dist v1 v3) 2 (2 * h0) (dist v2 v4) < 0 := by
    refine hreg 2 2 (dist v1 v3) 2 (2 * h0) (dist v2 v4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simpa [cstab] using h13
    · calc dist v1 v3 ≤ dist v1 v2 + dist v2 v3 := dist_triangle v1 v2 v3
        _ = 4 := by rw [h12, h23]; norm_num
        _ ≤ 6 := by norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simpa [cstab] using h24
    · calc dist v2 v4 ≤ dist v2 v3 + dist v3 v4 := dist_triangle v2 v3 v4
        _ = 4 := by rw [h23, h34]; norm_num
        _ ≤ 6 := by norm_num
  have hpos' : 0 ≤ deltaY 2 2 (dist v1 v3) 2 (2 * h0) (dist v2 v4) := by
    simpa [h12, h23, h34, h14, dist_comm] using hpos
  linarith

/-- HOL `quad_diag_362` (BKOSSGE.hl:92): the shorter diagonal of a
cstab quad is below 3.62.  PROVED 2026-11-05 (`la16-gap-w1`): negate,
project the `2171548893` registry entry at
`(d34, d23, d13, d12, d14, d24)`, and contradict
`DELTA_Y_POS_4POINTS_p16`. -/
theorem quad_diag_362_p16 (h : main_nonlinear_terminal_v11) :
    ∀ (v1 v2 v3 v4 : V3), dist v1 v2 = 2 → dist v2 v3 = cstab →
      dist v3 v4 = 2 → dist v1 v4 = cstab →
      dist v1 v3 ≤ 3.62 ∨ dist v2 v4 ≤ 3.62 := by
  intro v1 v2 v3 v4 h12 h23 h34 h14
  by_contra hcon
  rw [not_or] at hcon
  have hd13 : 3.62 < dist v1 v3 := not_le.mp hcon.1
  have hd24 : 3.62 < dist v2 v4 := not_le.mp hcon.2
  have hreg : mainEstimate_2171548893 :=
    h "2171548893" (by simp [mainNonlinearTerminalV11Ids_t11])
  have hpos := DELTA_Y_POS_4POINTS_p16 v3 v4 v2 v1
  have hc : cstab = 3.01 := rfl
  have hneg : deltaY 2 cstab (dist v1 v3) 2 cstab (dist v2 v4) < 0 := by
    refine hreg 2 cstab (dist v1 v3) 2 cstab (dist v2 v4)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · norm_num
    · norm_num
    · rw [hc]
    · rw [hc]
    · linarith
    · calc dist v1 v3 ≤ dist v1 v2 + dist v2 v3 := dist_triangle v1 v2 v3
        _ = 2 + cstab := by rw [h12, h23]
        _ = 5.01 := by rw [hc]; norm_num
        _ ≤ 6 := by norm_num
    · norm_num
    · norm_num
    · rw [hc]
    · rw [hc]
    · linarith
    · calc dist v2 v4 ≤ dist v2 v3 + dist v3 v4 := dist_triangle v2 v3 v4
        _ = cstab + 2 := by rw [h23, h34]
        _ = 5.01 := by rw [hc]; norm_num
        _ ≤ 6 := by norm_num
  have hpos' : 0 ≤ deltaY 2 cstab (dist v1 v3) 2 cstab (dist v2 v4) := by
    simpa [h12, h23, h34, h14, dist_comm] using hpos
  linarith

/-- HOL `INV_ARCLENGTH` (BKOSSGE.hl:114): on `(0, π)` the `arclength`
functional inverts the chord-length formula.  The `atn2` unfolding of
`arcLength` is reached through the local `∀ g` statement (discharged by
`rfl`), since the bare `atn2` name is ambiguous in this import graph. -/
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
  have hupsv : upsX (y1 * y1) (y3 * y3) D = (2 * y1 * y3 * Real.sin z) ^ 2 := by
    simp only [upsX]
    have htrig : Real.sin z ^ 2 + Real.cos z ^ 2 = 1 := Real.sin_sq_add_cos_sq z
    linear_combination
      (-(D - (y1 * y1 + y3 * y3) - 2 * y1 * y3 * Real.cos z)) * hD +
        -(2 * y1 * y3) ^ 2 * htrig
  have hY : D - y1 * y1 - y3 * y3 = -(2 * y1 * y3 * Real.cos z) := by
    rw [hD]; ring
  simp only [arcLength]
  rw [hsq, hupsv, Real.sqrt_sq (by positivity), hY]
  -- the `atn2` value: `π/2 + atn2 (2 y1 y3 sin z) (-(2 y1 y3 cos z)) = z`
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

/-! ### Local `atn2` continuity kit (Route B, clean)

`atn2` is this repository's own two-argument arctangent (`SphereKit.atn2`);
Mathlib has no `Real.atan2`.  The `dih_y`/`taum` continuity suite is therefore
closed here with a small local kit instead of consuming Ocbicby's
still-open `derived_form_dih_x_wrt_x{4,5,6}_p22`.  On the open half-plane
`x > 0`, `atn2 x y` is exactly `Real.arctan (y / x)`, so continuity in a
`dih_y` slot reduces to `Real.continuous_arctan` composed with a rational
function.  The `sqrt` argument of `dih_x` is positive at the base point
because `deltaY > 0` and `y1 > 0`; the `upsX` hypotheses are not needed for
continuity (they enter only the derivative kit of Ocbicby). -/

/-- `atn2 x y = Real.arctan (y / x)` on the right half-plane `0 < x`
(all three branches of the `atn2` definition agree there). -/
private theorem atn2_eq_arctan_div_p16 {x y : ℝ} (hx : 0 < x) :
    atn2 x y = Real.arctan (y / x) := by
  unfold atn2
  by_cases h : |y| < x
  · rw [if_pos h]
  · rw [if_neg h]
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    by_cases hy : 0 < y
    · rw [if_pos hy]
      have hpos : 0 < y / x := div_pos hy hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_pos hpos]
      ring
    · rw [if_neg hy]
      have hyn : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
      rw [if_pos hyn]
      have hneg : y / x < 0 := div_neg_of_neg_of_pos hyn hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_neg hneg]
      ring

/-- Chain rule for `atn2` at a point where the first argument is positive:
continuity of `q ↦ atn2 (f q) (g q)` from continuity of `f` and `g`. -/
private theorem continuousAt_atn2_comp_p16 {f g : ℝ → ℝ} {q0 : ℝ}
    (hf : ContinuousAt f q0) (hg : ContinuousAt g q0) (hpos : 0 < f q0) :
    ContinuousAt (fun q => atn2 (f q) (g q)) q0 := by
  have hcont : ContinuousAt (fun q => Real.arctan (g q / f q)) q0 :=
    Real.continuous_arctan.continuousAt.comp' (hg.div hf hpos.ne')
  refine hcont.congr ?_
  filter_upwards [hf.eventually (isOpen_Ioi.mem_nhds hpos)] with q hq
  exact (atn2_eq_arctan_div_p16 hq).symm

/-- `dihXf` is continuous in its fourth slot at points where the `atn2` first
argument `sqrt (4 x1 deltaX)` is positive. -/
private theorem continuousAt_dihXf_wrt4_p16 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 q x5 x6) x4 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 q x5 x6)) x4 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 q x5 x6)) x4 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_p16 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 q x5 x6))
        (-(deltaX4 x1 x2 x3 q x5 x6))) x4 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihXf` is continuous in its fifth slot. -/
private theorem continuousAt_dihXf_wrt5_p16 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 x4 q x6) x5 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6)) x5 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 x4 q x6)) x5 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_p16 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6))
        (-(deltaX4 x1 x2 x3 x4 q x6))) x5 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihXf` is continuous in its sixth slot. -/
private theorem continuousAt_dihXf_wrt6_p16 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 x4 x5 q) x6 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 q)) x6 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 x4 x5 q)) x6 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_p16 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 q))
        (-(deltaX4 x1 x2 x3 x4 x5 q))) x6 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihY` is continuous in its fourth slot (`dihXf` at `x4 = y4 * y4`). -/
private theorem continuousAt_dihY_wrt4_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 q y5 y6) y4 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y4 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (q * q)
      (y5 * y5) (y6 * y6)) y4 :=
    (continuousAt_dihXf_wrt4_p16 (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `dihY` is continuous in its fifth slot. -/
private theorem continuousAt_dihY_wrt5_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 q y6) y5 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y5 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (q * q) (y6 * y6)) y5 :=
    (continuousAt_dihXf_wrt5_p16 (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `dihY` is continuous in its sixth slot. -/
private theorem continuousAt_dihY_wrt6_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 y5 q) y6 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y6 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (q * q)) y6 :=
    (continuousAt_dihXf_wrt6_p16 (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `deltaY` is invariant under the slot permutation `(1 2 3)(4 5 6)` used
by the second term of `taum_dih_y_p16` (a polynomial symmetry of `deltaX`). -/
private theorem deltaY_rot231564_p16 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y2 y3 y1 y5 y6 y4 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

/-- `deltaY` is invariant under the slot permutation `(1 3 2)(4 6 5)` used
by the third term of `taum_dih_y_p16` (the inverse rotation). -/
private theorem deltaY_rot312645_p16 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y3 y1 y2 y6 y4 y5 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

/-- `upsX` is symmetric in its first two arguments. -/
private theorem upsX_swap12_p16 (a b c : ℝ) : upsX a b c = upsX b a c := by
  unfold upsX
  ring

/-- HOL `real_continuous_dih_y_wrt4` (BKOSSGE.hl:181).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean): `dihY` in the `y4` slot is `dihXf` at
`x4 = y4 * y4`, whose only non-polynomial ingredient is `atn2`, continuous
at a positive first argument via the local `atn2` kit.  No Ocbicby
`derived_form_dih_x_wrt_x4` input (that upstream is still unproved). -/
theorem real_continuous_dih_y_wrt4_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 q y5 y6) y4 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt4_p16 y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_dih_y_wrt5` (BKOSSGE.hl:211).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean), same local `atn2` kit as `wrt4`. -/
theorem real_continuous_dih_y_wrt5_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 q y6) y5 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt5_p16 y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_dih_y_wrt6` (BKOSSGE.hl:241).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean), same local `atn2` kit as `wrt4`. -/
theorem real_continuous_dih_y_wrt6_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 y5 q) y6 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt6_p16 y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_taum` (BKOSSGE.hl:271).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean): rewrite `taum` by `taum_dih_y_p16` and
apply the `dih_y` slot suite to the three rotated `dihY` terms.  The two
rotations are `deltaY` permutation identities (`ring`) plus one `upsX`
swap; no Ocbicby `derived_form_*` input. -/
theorem real_continuous_taum_p16 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hu3 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => taum y1 y2 y3 q y5 y6) y4 := by
  have hd1 : 0 < deltaY y2 y3 y1 y5 y6 y4 := by
    rw [deltaY_rot231564_p16]
    exact hdy
  have hd2 : 0 < deltaY y3 y1 y2 y6 y4 y5 := by
    rw [deltaY_rot312645_p16]
    exact hdy
  have h1 := real_continuous_dih_y_wrt4_p16 y1 y2 y3 y4 y5 y6 hdy hy1 hu1 hu3
  have h2 := real_continuous_dih_y_wrt6_p16 y2 y3 y1 y5 y6 y4 hd1 hy2 hu2
    (by rw [upsX_swap12_p16]; exact hu1)
  have h3 := real_continuous_dih_y_wrt5_p16 y3 y1 y2 y6 y4 y5 hd2 hy3
    (by rw [upsX_swap12_p16]; exact hu3) (by rw [upsX_swap12_p16]; exact hu2)
  have hsum : ContinuousAt (fun q =>
      rho y1 * dihY y1 y2 y3 q y5 y6 +
        rho y2 * dihY y2 y3 y1 y5 y6 q +
        rho y3 * dihY y3 y1 y2 y6 q y5 - (Real.pi + sol0)) y4 :=
    (((continuousAt_const.mul h1).add (continuousAt_const.mul h2)).add
      (continuousAt_const.mul h3)).sub continuousAt_const
  refine hsum.congr ?_
  filter_upwards with q
  exact (taum_dih_y_p16 y1 y2 y3 q y5 y6).symm

/-- HOL `UPS_X_STD_POS` (BKOSSGE.hl:291); via PackingAuto18's
`TRI_UPS_X_STRICT_POS` with the `h0 = 1.26` box. -/
theorem UPS_X_STD_POS_p16 (y1 y2 y3 : ℝ) (h1 : 2 ≤ y1) (h1' : y1 ≤ 2 * h0)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ 2 * h0) (h3 : 2 ≤ y3) (h3' : y3 ≤ 2 * h0) :
    0 < upsX (y1 * y1) (y2 * y2) (y3 * y3) := by
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

/-! ## `SCS_GENERIC_SYM_0` kit (Xwitccn / In_sym_0 symmetry, CQAOQLR.hl:83-175)

Sign-negation transfer for the `scs_generic` hypothesis.  The proof follows
the HOL route: the opposite-index ranges are the negated ranges
(`OPP_IMAGE_V_EQ_NEG` / `OPP_IMAGE_E_EQ_NEG`; the edge form is inlined as
`oppEdgeIndex_p16`), `Generic` is applied at `(-v', -w, -u)`, and the
conclusion is pulled back through `AFF_GE_VEC0_SYM_0` /
`AFF_LT_VEC0_SYM_0` (sign-generic core `affsignNegPt_p16`) and
`REFL_SYM_0` / `INTER_SYM_0`.  All items are private; the `*_SYM_0` names
are the HOL anchors. -/

/-- The negation map on `V3` is injective (shared step of the `*_SYM_0` kit). -/
private theorem negInjSym_p16 : Function.Injective (fun x : V3 => -x) :=
  fun _ _ h => by simpa using h

/-- HOL `ELEMENT2_SYM_0`: `{--a, --b} = IMAGE (λx. --x) {a,b}`. -/
private theorem element2Neg_p16 (a b : V3) :
    ({-a, -b} : Set V3) = Set.image (fun x : V3 => -x) ({a, b} : Set V3) := by
  rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL `REFL_SYM_0`: negation is an involution on sets. -/
private theorem reflNeg_p16 (A : Set V3) :
    Set.image (fun x : V3 => -x) (Set.image (fun x : V3 => -x) A) = A := by
  simp

/-- HOL `INTER_SYM_0`: negation distributes over `∩` (it is injective). -/
private theorem interNeg_p16 (e1 e2 : Set V3) :
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

/-- HOL `VEC0_SYM_0`: the origin is fixed by negation. -/
private theorem vec0Neg_p16 :
    Set.image (fun x : V3 => -x) ({0} : Set V3) = ({0} : Set V3) := by
  ext x
  simp

/-! ### affine transfer with `{0}` base -/

/-- HOL `AFF_GE_VEC0_SYM_0` / `AFF_LT_VEC0_SYM_0`, sign-generic core:
if `w` is an `sgn`-combination of `{0} ∪ (-e)` then `-w` is one of `{0} ∪ e`
(the coefficients are transported by `f ↦ f ∘ neg`, the extreme value `0`
being fixed by negation). -/
private theorem affsignNegPt_p16 {e : Set V3} {w : V3} {sgn : ℝ → Prop}
    (hw : Affsign sgn ({0} : Set V3) (Set.image (fun x : V3 => -x) e) w) :
    Affsign sgn ({0} : Set V3) e (-w) := by
  obtain ⟨f, hfin, hwv, hfp, hfsum⟩ := hw
  have hU : Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
      = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e := by
    rw [Set.image_union, vec0Neg_p16]
  have hfinA : ((({0} : Set V3) ∪ e : Set V3)).Finite :=
    (Set.finite_image_iff negInjSym_p16.injOn).mp (by rw [hU]; exact hfin)
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
            (g := fun x : V3 => -x) negInjSym_p16.injOn, neg_neg]
  · intro z hz
    exact hfp (-z) ⟨z, hz, rfl⟩
  · show (∑ y ∈ hfinA.toFinset, f (-y)) = 1
    rw [← Finset.sum_image (f := f) (g := fun x : V3 => -x) negInjSym_p16.injOn, ← heq]
    exact hfsum

/-- HOL `AFF_GE_VEC0_SYM_0`: `aff_ge {vec 0} (IMAGE (λx. --x) e)`
`= IMAGE (λx. --x) (aff_ge {vec 0} e)`. -/
private theorem affGeNeg_p16 (e : Set V3) :
    affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affGe ({0} : Set V3) e) := by
  ext v
  constructor
  · intro hv
    have hv' : Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3)
        (Set.image (fun x : V3 => -x) e) v := hv
    refine ⟨-v, ?_, by simp⟩
    show Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3) e (-v)
    exact affsignNegPt_p16 (sgn := fun x : ℝ => 0 ≤ x) hv'
  · rintro ⟨u, hu, rfl⟩
    show Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3)
      (Set.image (fun x : V3 => -x) e) (-u)
    refine affsignNegPt_p16 (sgn := fun x : ℝ => 0 ≤ x)
      (e := Set.image (fun x : V3 => -x) e) ?_
    rw [reflNeg_p16 e]
    exact hu

/-- HOL `AFF_LT_VEC0_SYM_0`: `aff_lt {vec 0} (IMAGE (λx. --x) e)`
`= IMAGE (λx. --x) (aff_lt {vec 0} e)`. -/
private theorem affLtNeg_p16 (e : Set V3) :
    affLt ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affLt ({0} : Set V3) e) := by
  ext v
  constructor
  · intro hv
    have hv' : Affsign (fun x : ℝ => x < 0) ({0} : Set V3)
        (Set.image (fun x : V3 => -x) e) v := hv
    refine ⟨-v, ?_, by simp⟩
    show Affsign (fun x : ℝ => x < 0) ({0} : Set V3) e (-v)
    exact affsignNegPt_p16 (sgn := fun x : ℝ => x < 0) hv'
  · rintro ⟨u, hu, rfl⟩
    show Affsign (fun x : ℝ => x < 0) ({0} : Set V3)
      (Set.image (fun x : V3 => -x) e) (-u)
    refine affsignNegPt_p16 (sgn := fun x : ℝ => x < 0)
      (e := Set.image (fun x : V3 => -x) e) ?_
    rw [reflNeg_p16 e]
    exact hu

/-! ### opposite-edge index arithmetic -/

/-- A `k`-periodic sequence satisfies `v k = v 0`. -/
private theorem periodicZero_p16 {v : ℕ → V3} {k : ℕ} (hper : Periodic v k) :
    v k = v 0 := by
  have h := hper 0
  rwa [Nat.zero_add] at h

/-- The opposite of an edge is an edge (HOL `OPP_IMAGE_E_EQ`, membership
form): every `{v (k - SUC (i MOD k)), v (k - SUC (SUC i MOD k))}` is some
`{v j, v (SUC j)}`. -/
private theorem oppEdgeIndex_p16 {v : ℕ → V3} {k : ℕ} (hk : 1 < k)
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
    rw [e1, e2, hk1, periodicZero_p16 hper, Set.pair_comm]

/-- HOL `SCS_GENERIC_SYM_0` (CQAOQLR.hl:156).
DISCHARGED 2026-11-05 (`la16-sym-w1`): opposite-index range transport
(`OPP_IMAGE_V_EQ_NEG` is immediate, `OPP_IMAGE_E_EQ_NEG` is inlined as
`oppEdgeIndex_p16`) plus the `{0}`-base affine transfer
`AFF_GE_VEC0_SYM_0` / `AFF_LT_VEC0_SYM_0` and `REFL/INTER_SYM_0`.
`BBsV39` supplies `Periodic v s.k`, `isScsV39` supplies `3 ≤ s.k`; no
sorry-bearing upstream is consumed. -/
theorem SCS_GENERIC_SYM_0_p16 (s : ScsV39) (v : ℕ → V3) (h1 : BBsV39 s v)
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
      rw [element2Neg_p16, ← hi]
    rw [hstep]
    have hneg : Set.image (fun x : V3 => -x)
        ({-(v (s.k - (i % s.k + 1))), -(v (s.k - ((i + 1) % s.k + 1)))} : Set V3)
        = ({v (s.k - (i % s.k + 1)), v (s.k - ((i + 1) % s.k + 1))} : Set V3) := by
      rw [← element2Neg_p16 (-(v (s.k - (i % s.k + 1))))
        (-(v (s.k - ((i + 1) % s.k + 1))))]
      simp
    rw [hneg]
    obtain ⟨m, hm⟩ := oppEdgeIndex_p16 hk hper i
    rw [hm]
    exact ⟨m, rfl⟩
  have hgen := h3 (-v') (-w) (-u) hE hV
  have hkey : Set.image (fun x : V3 => -x)
      (affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u}) = ∅ := by
    rw [interNeg_p16, ← affGeNeg_p16 {v', w}, ← affLtNeg_p16 {u},
      ← element2Neg_p16 v' w, ← ELEMENT1_SYM_0_p16 u]
    exact hgen
  calc affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u}
      = Set.image (fun x : V3 => -x)
          (Set.image (fun x : V3 => -x)
            (affGe ({0} : Set V3) {v', w} ∩ affLt ({0} : Set V3) {u})) :=
        (reflNeg_p16 _).symm
    _ = Set.image (fun x : V3 => -x) ∅ := by rw [hkey]
    _ = ∅ := by simp

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

/-- HOL `K_SUC_2_MOD_F_SUB_ID` (CQAOQLR.hl:133).  PROVED 2026-11-05
(`la16-gap-w1`): split on `i % k` (zero, `k-2`, `k-1`, and the strict
middle), reduce both `(i+2) % k` and `(i+k-1) % k` through
`Nat.mod_add_mod` / `Nat.add_mod`, and close each branch with
`Nat.mod_eq_of_lt` + `omega`. -/
theorem K_SUC_2_MOD_F_SUB_ID_p16 {k i : ℕ} (hk : 1 < k) :
    (k - ((i + 2) % k + 1) + 3) % k = (k - ((i + k - 1) % k + 1)) % k := by
  set q := i % k with hqdef
  have hq : q < k := Nat.mod_lt _ (by omega)
  have e2 : (i + 2) % k = (q + 2) % k := by
    rw [hqdef]
    exact (Nat.mod_add_mod i k 2).symm
  have ek : (i + k - 1) % k = (q + k - 1) % k := by
    have h1 : i + k - 1 = i + (k - 1) := by omega
    have h2 : q + k - 1 = q + (k - 1) := by omega
    rw [h1, h2, hqdef, Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
  rw [e2, ek]
  rcases Nat.eq_zero_or_pos q with hq0 | hqp
  · rw [hq0]
    have hL : (k - (((0:ℕ) + 2) % k + 1) + 3) % k = 0 := by
      rcases eq_or_lt_of_le (show 2 ≤ k by omega) with hk2 | hk3
      · subst hk2; norm_num
      · rw [Nat.mod_eq_of_lt (by omega : 2 < k)]
        have h : k - (2 + 1) + 3 = k := by omega
        rw [h, Nat.mod_self]
    have hR : (k - (((0:ℕ) + k - 1) % k + 1)) % k = 0 := by
      have h1 : (0 + k - 1) % k = k - 1 := by
        rw [show (0:ℕ) + k - 1 = k - 1 by omega]
        exact Nat.mod_eq_of_lt (by omega : k - 1 < k)
      rw [h1]
      have h2 : k - (k - 1 + 1) = 0 := by omega
      rw [h2, Nat.zero_mod]
    rw [hL, hR]
  · rcases lt_trichotomy q (k - 2) with hlt | heq | hgt
    · -- 1 ≤ q ≤ k-3
      have hqk : q + 2 < k := by omega
      have hL : (k - ((q + 2) % k + 1) + 3) % k = k - q := by
        rw [Nat.mod_eq_of_lt hqk]
        have h : k - (q + 2 + 1) + 3 = k - q := by omega
        rw [h, Nat.mod_eq_of_lt (by omega : k - q < k)]
      have hR : (k - ((q + k - 1) % k + 1)) % k = k - q := by
        have h1 : q + k - 1 = (q - 1) + k := by omega
        have h2 : ((q - 1) + k) % k = q - 1 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : q - 1 < k), Nat.mod_self,
            Nat.add_zero, Nat.mod_eq_of_lt (by omega : q - 1 < k)]
        rw [h1, h2]
        have h3 : k - (q - 1 + 1) = k - q := by omega
        rw [h3, Nat.mod_eq_of_lt (by omega : k - q < k)]
      rw [hL, hR]
    · -- q = k-2 (so k ≥ 3)
      have hk3 : 3 ≤ k := by omega
      have hL : (k - ((q + 2) % k + 1) + 3) % k = 2 := by
        rw [heq, show k - 2 + 2 = k by omega, Nat.mod_self]
        have h : k - (0 + 1) + 3 = k + 2 := by omega
        rw [h]
        simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : 2 < k)]
      have hR : (k - ((q + k - 1) % k + 1)) % k = 2 := by
        rw [heq]
        have h1 : k - 2 + k - 1 = (k - 3) + k := by omega
        have h2 : ((k - 3) + k) % k = k - 3 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 3 < k), Nat.mod_self,
            Nat.add_zero, Nat.mod_eq_of_lt (by omega : k - 3 < k)]
        rw [h1, h2]
        have h3 : k - (k - 3 + 1) = 2 := by omega
        rw [h3, Nat.mod_eq_of_lt (by omega : 2 < k)]
      rw [hL, hR]
    · -- q = k-1
      have hqk1 : q = k - 1 := by omega
      have hk2 : 2 ≤ k := by omega
      have hL : (k - ((q + 2) % k + 1) + 3) % k = 1 := by
        rw [hqk1, show k - 1 + 2 = k + 1 by omega]
        have h2 : (k + 1) % k = 1 := by
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add]
          simp only [Nat.mod_eq_of_lt (by omega : 1 < k)]
        rw [h2]
        have h3 : k - (1 + 1) + 3 = k + 1 := by omega
        rw [h3]
        exact h2
      have hR : (k - ((q + k - 1) % k + 1)) % k = 1 := by
        rw [hqk1]
        have h1 : k - 1 + k - 1 = (k - 2) + k := by omega
        have h2 : ((k - 2) + k) % k = k - 2 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 2 < k), Nat.mod_self,
            Nat.add_zero, Nat.mod_eq_of_lt (by omega : k - 2 < k)]
        rw [h1, h2]
        have h3 : k - (k - 2 + 1) = 1 := by omega
        rw [h3]
        exact Nat.mod_eq_of_lt (by omega : 1 < k)
      rw [hL, hR]

/-- HOL `CQAOQLR` (CQAOQLR.hl:247-335): the ear-reciprocity iff.
Forward direction: `TFITSKC_p27` at `i` (the distance-2 hypothesis
propagates across the short ear).  Backward direction: the same lemma on
the opposite system `scsOppV39 s` with the negated peropp sequence at the
mirrored index `j0 = k - SUC((i + 2) MOD k)`, whose hypotheses unfold to
the given ones via the Section-D modular kit (`K_SUC_2_MOD_SUB` /
`K_SUC_2_MOD_SUB_ID` / `K_SUC_2_MOD_F_SUB_ID` / `SUC_OPP_ID`-free
`peropp` value computation), `A_B_J_SCS_OPP` and `DIAG_OPP`.  Assembled
2026-11-13 (lane vasw0-w1); consumes `MM_SCS_OPP_fb` (FanBaseKit) — the
one import added for this proof. -/
theorem CQAOQLR_p16 : CQAOQLR_concl_p16 := by
  intro hmn s v i hk3 his hMMs hgen hbasic hdiag
  intro hb01 hb12e hab23 habk1
  intro ha01 _hb01v _ha12 hb12v
  have hisD := his
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-, hsym, -,-,-,-,-,-,-⟩ := hisD
  constructor
  · -- forward: `TFITSKC` at `i`
    intro hd01
    exact TFITSKC_p27 hmn s v i hab23 hk3 his hMMs hgen hbasic _ha12 hb12v
      hd01 hb01 hdiag
  · -- backward: `TFITSKC` on the opposite system at the mirrored index
    intro hd12
    have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hMMs
    have hk1 : 1 < s.k := by omega
    have hk3' : ¬(s.k ≤ 3) := by omega
    have his' : isScsV39 (scsOppV39 s) := OPP_IS_SCS_p33 s his
    have hMMs' : MMsV39 (scsOppV39 s) (fun n => -(peropp v s.k n)) :=
      MM_SCS_OPP_fb s v s.k rfl his hk3' hMMs
    have hgen' : scsGeneric (fun n => -(peropp v s.k n)) :=
      SCS_GENERIC_SYM_0_p16 s v hBB his hgen
    have hbasic' : scsBasicV39 (scsOppV39 s) := BASIC_OPP_p16 s his hbasic
    have dneg : ∀ x y : V3, dist (-x) (-y) = dist x y := by
      intro x y
      have h : (-x) - (-y) = -(x - y) := by
        rw [sub_eq_add_neg, neg_neg, neg_sub, sub_eq_add_neg]
        exact add_comm (-x) y
      rw [dist_eq_norm, dist_eq_norm, h, norm_neg]
    set j0 := s.k - ((i + 2) % s.k + 1) with hj0
    have hm0 := Nat.mod_lt i (show 0 < s.k by omega)
    have hm1 := Nat.mod_lt (i + 1) (show 0 < s.k by omega)
    have hm2 := Nat.mod_lt (i + 2) (show 0 < s.k by omega)
    have hmk := Nat.mod_lt (i + s.k - 1) (show 0 < s.k by omega)
    have hsub : ∀ m : ℕ, m < s.k → s.k - (s.k - (m + 1) + 1) = m :=
      fun m hm => by omega
    have hj0lt : j0 < s.k := by rw [hj0]; omega
    -- the peropp values at `j0, j0+1, j0+2, j0+3`
    have hj01 : (j0 + 1) % s.k = s.k - ((i + 1) % s.k + 1) := by
      rw [hj0, K_SUC_2_MOD_SUB_p16 hk1]
      exact Nat.mod_eq_of_lt (by omega)
    have hj02 : (j0 + 2) % s.k = s.k - (i % s.k + 1) := by
      rw [hj0, K_SUC_2_MOD_SUB_ID_p16 hk1]
      exact Nat.mod_eq_of_lt (by omega)
    have hj03 : (j0 + 3) % s.k = s.k - ((i + s.k - 1) % s.k + 1) := by
      rw [hj0, K_SUC_2_MOD_F_SUB_ID_p16 hk1]
      exact Nat.mod_eq_of_lt (by omega)
    have hj0m : j0 % s.k = j0 := Nat.mod_eq_of_lt hj0lt
    have e0 : peropp v s.k j0 = v (i + 2) := by
      show v (s.k - (j0 % s.k + 1)) = v (i + 2)
      rw [hj0m, hj0, hsub _ hm2]
      exact periodic_mod_eq_p23 hBB.2.1 (i + 2)
    have e1 : peropp v s.k (j0 + 1) = v (i + 1) := by
      show v (s.k - ((j0 + 1) % s.k + 1)) = v (i + 1)
      rw [hj01, hsub _ hm1]
      exact periodic_mod_eq_p23 hBB.2.1 (i + 1)
    have e2 : peropp v s.k (j0 + 2) = v i := by
      show v (s.k - ((j0 + 2) % s.k + 1)) = v i
      rw [hj02, hsub _ hm0]
      exact periodic_mod_eq_p23 hBB.2.1 i
    have e3 : peropp v s.k (j0 + 3) = v (i + s.k - 1) := by
      show v (s.k - ((j0 + 3) % s.k + 1)) = v (i + s.k - 1)
      rw [hj03, hsub _ hmk]
      exact periodic_mod_eq_p23 hBB.2.1 (i + s.k - 1)
    -- the `a`/`b` slots of the opposite system at the needed indices
    have hABJ := A_B_J_SCS_OPP_p16 s
    have haopp := hABJ.1
    have hbopp := hABJ.2.1
    have ca : ∀ m n : ℕ, s.a (m % s.k) (n % s.k) = s.a m n := fun m n =>
      CHANGE_A_SCS_MOD_p28 s his _ _ _ _ (by rw [Nat.mod_mod]) (by rw [Nat.mod_mod])
    have cb : ∀ m n : ℕ, s.b (m % s.k) (n % s.k) = s.b m n := fun m n =>
      CHANGE_B_SCS_MOD_p28 s his _ _ _ _ (by rw [Nat.mod_mod]) (by rw [Nat.mod_mod])
    -- `TFITSKC` hypotheses on the opposite system
    have hab23' : (scsOppV39 s).a (j0 + 2) (j0 + 3) < (scsOppV39 s).b (j0 + 2) (j0 + 3) := by
      have ea : (scsOppV39 s).a (j0 + 2) (j0 + 3) = s.a (i % s.k) ((i + s.k - 1) % s.k) := by
        rw [haopp, hj02, hj03, hsub _ hm0, hsub _ hmk]
      have eb : (scsOppV39 s).b (j0 + 2) (j0 + 3) = s.b (i % s.k) ((i + s.k - 1) % s.k) := by
        rw [hbopp, hj02, hj03, hsub _ hm0, hsub _ hmk]
      rw [ea, eb, ca i ((i + s.k - 1)), cb i ((i + s.k - 1))]
      have h1 := (hsym i (i + s.k - 1)).1
      have h2 := (hsym (i + s.k - 1) i).2.2.2.1
      rw [h1]
      exact lt_of_lt_of_eq habk1 h2
    have ha12' : (scsOppV39 s).a (j0 + 1) (j0 + 2) = 2 := by
      have ea : (scsOppV39 s).a (j0 + 1) (j0 + 2) = s.a ((i + 1) % s.k) (i % s.k) := by
        rw [haopp, hj01, hj02, hsub _ hm1, hsub _ hm0]
      rw [ea, ca (i + 1) i, (hsym i (i + 1)).1.symm]
      exact ha01
    have hb12' : (scsOppV39 s).b (j0 + 1) (j0 + 2) ≤ 2 * h0 := by
      have eb : (scsOppV39 s).b (j0 + 1) (j0 + 2) = s.b ((i + 1) % s.k) (i % s.k) := by
        rw [hbopp, hj01, hj02, hsub _ hm1, hsub _ hm0]
      rw [eb, cb (i + 1) i, (hsym i (i + 1)).2.2.2.1.symm]
      exact _hb01v
    have hd01' : dist (-(peropp v s.k j0)) (-(peropp v s.k (j0 + 1))) = 2 := by
      rw [e0, e1, dneg, dist_comm]
      exact hd12
    have hb0gt' : 2 < (scsOppV39 s).b j0 (j0 + 1) := by
      have eb : (scsOppV39 s).b j0 (j0 + 1) = s.b ((i + 2) % s.k) ((i + 1) % s.k) := by
        rw [hbopp, hj0m, hj01, hj0, hsub _ hm2, hsub _ hm1]
      rw [eb, cb (i + 2) (i + 1), (hsym (i + 1) (i + 2)).2.2.2.1.symm]
      exact hb12e
    have hadiag' : ∀ x y : ℕ, scsDiag (scsOppV39 s).k x y →
        (scsOppV39 s).a x y ≤ cstab ∧
          cstab < dist (-(peropp v s.k x)) (-(peropp v s.k y)) ∧
          4 * h0 < (scsOppV39 s).b x y := by
      intro x y hxy
      have hxy' := DIAG_OPP_p16 s.k x y hk3 hxy
      have hd := hdiag _ _ hxy'
      refine ⟨?_, ?_, ?_⟩
      · rw [haopp]
        exact hd.1
      · have ex : peropp v s.k x = v (s.k - (x % s.k + 1)) := rfl
        have ey : peropp v s.k y = v (s.k - (y % s.k + 1)) := rfl
        rw [ex, ey, dneg]
        exact hd.2.1
      · rw [hbopp]
        exact hd.2.2
    have hcon := TFITSKC_p27 hmn (scsOppV39 s) (fun n => -(peropp v s.k n)) j0
      hab23' hk3 his' hMMs' hgen' hbasic' ha12' hb12' hd01' hb0gt' hadiag'
    rw [e1, e2, dneg, dist_comm] at hcon
    exact hcon

/-! Coverage note: every JEJTVGB.hl / XIVPHKS.hl / BKOSSGE.hl /
CQAOQLR.hl item is carried above (the XIVPHKS.hl items now live in
`Kepler.Text.XivphksKit` and are re-exported through the import).
Proved: SCS_ARROW_TRANS_SING, lp_main_estimate_JEJTVGB,
nonlinear_imp_lp_main_estimate, cos_bounds_0_pi, ear_acute, INV_ARCLENGTH,
UPS_X_STD_POS, quad_nonexist_849, quad_diag_362, taum_dih_y,
K_SUC_2_MOD_SUB, K_SUC_2_MOD_SUB_ID, SUC_OPP_ID, K_SUC_2_MOD_F_SUB_ID,
A_B_J_SCS_OPP, ELEMENT1_SYM_0, UNADORNED_OPP, BASIC_OPP, DIAG_OPP,
FSQKWKK, XIVPHKS, XIVPHKS_SHIFT, real_continuous_dih_y_wrt4/5/6,
real_continuous_taum, SCS_GENERIC_SYM_0 (27), CQAOQLR (28; assembled
2026-11-13 lane vasw0-w1 — TFITSKC forward + opposite-system backward,
consuming `MM_SCS_OPP_fb` via the FanBaseKit import above).  Zero sorries
remain in this file.  The `_p16` sphere-kit copies were deduped
into `Kepler.Text.SphereKit` 2026-09-17. -/

/-! ## w13 axiom audit (closed items only) -/

#print axioms FSQKWKK_p16
#print axioms AZIM_DIHV_SAME_STRONG

/-! ## w14 axiom audit (closed items only) -/

#print axioms XIVPHKS_p16
#print axioms XIVPHKS_SHIFT_p16

/-! ## w15 axiom audit (closed items only, 2026-11-05 `la16-gap-w1`) -/

#print axioms DELTA_Y_POS_4POINTS_p16
#print axioms ear_acute_p16
#print axioms quad_nonexist_849_p16
#print axioms quad_diag_362_p16
#print axioms taum_dih_y_p16
#print axioms K_SUC_2_MOD_F_SUB_ID_p16

/-! ## w16 axiom audit (closed items only, 2026-11-05 `la16-cont-w1`) -/

#print axioms atn2_eq_arctan_div_p16
#print axioms continuousAt_atn2_comp_p16
#print axioms continuousAt_dihXf_wrt4_p16
#print axioms continuousAt_dihXf_wrt5_p16
#print axioms continuousAt_dihXf_wrt6_p16
#print axioms continuousAt_dihY_wrt4_p16
#print axioms continuousAt_dihY_wrt5_p16
#print axioms continuousAt_dihY_wrt6_p16
#print axioms deltaY_rot231564_p16
#print axioms deltaY_rot312645_p16
#print axioms upsX_swap12_p16
#print axioms real_continuous_dih_y_wrt4_p16
#print axioms real_continuous_dih_y_wrt5_p16
#print axioms real_continuous_dih_y_wrt6_p16
#print axioms real_continuous_taum_p16

/-! ## w17 axiom audit (closed items only, 2026-11-05 `la16-sym-w1`) -/

#print axioms SCS_GENERIC_SYM_0_p16
