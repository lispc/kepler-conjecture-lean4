/-
LocalConcl — ASSEMBLY file for the `Kepler.Text.LocalAuto1.lean` appendix
registry: every sorried `*_concl` interface statement is matched against its
downstream proved twin in `LocalAuto2-38`, and dischargeable ones are bound
here as `<name>_discharged : <statement>`.

LocalAuto1 cannot import the discharging waves (import cycle), so the
binding happens here: this file imports the LocalAuto waves and re-exposes
the discharged contracts under their registry names with the `_discharged`
suffix.

LEDGER (LocalAuto1 sorried `*_concl` interface statements: 90)

  Dischargeable: 10        Discharged: 10        Blocked: 80

  Discharged here (twin · shape status):
    YXIONXL1_discharged  := LocalAuto12.YXIONXL1       (verbatim twin)
    EYYPQDW3_discharged  := LocalAuto17 kit via shim   (twin had extra
                                `s = 1 ∨ s = -1` antecedent, unused by the
                                continuity kernel; shim re-derives the v2
                                continuity from `MK_PLANAR_V3_DEFOR_V2_FUN_p17`)
    GSXRFWM_discharged   := LocalAuto33.GSXRFWM_p33    (verbatim twin)
    AUEAHEH_discharged   := LocalAuto33.AUEAHEH_p33    (verbatim twin)
    ZNLLLDL_discharged   := LocalAuto33.ZNLLLDL_p33    (verbatim twin)
    VQFYMZY_discharged   := LocalAuto33.VQFYMZY_p33    (shim: target set
                                permutation `{scs4M6', scs4T4} = {scs4T4, scs4M6'}`)
    BNAWVNH_discharged   := LocalAuto33.BNAWVNH_p33    (shim: set permutation)
    RAWZDIB_discharged   := LocalAuto33.RAWZDIB_p33    (shim: set permutation)
    MFKLVDK_discharged   := LocalAuto33.MFKLVDK_p33    (shim: set permutation)
    RYPDIXT_discharged   := LocalAuto33.RYPDIXT_p33    (shim: set permutation)

  Blocked, with reasons.

  (a) No downstream twin anywhere in LocalAuto2-38 (11):
      HFNXPZA, EQTTNZI1, EQTTNZI2, DRNDRDV, ASSWPOW, EFLYGAU, BJTDWPS,
      OTMTOTJ1, OTMTOTJ2, OTMTOTJ3, OTMTOTJ4.

  (b) Twin is circular — it is proved *from* the LocalAuto1 registry sorry
      itself (re-export), so a discharge would be vacuous (11):
      ZITHLQN (ZITHLQN_p25 = `ZITHLQN_concl h`), WGDHPPI (WGDHPPI_p25),
      TUAPYYU (TUAPYYU_p25 = `fun _ => TUAPYYU_concl`),
      YEBWJNG (YEBWJNG_p25), WKZZEEH (WKZZEEH_p25), PWEIWBZ (PWEIWBZ_p25),
      VASYYAU (VASYYAU_p25), WKEIDFT (WKEIDFT_concl_p24 = `WKEIDFT_concl`),
      PEDSLGV1 (LocalAuto20.PEDSLGV1), PEDSLGV2 (LocalAuto20.PEDSLGV2),
      OIQKKEP (OIQKKEP_p26 = `exact OIQKKEP_concl ...`).

  (c) Downstream twin exists but is itself sorried (50):
      unadorned_MMs (unadorned_MMs_p27), XWITCCN (LocalAuto36 master + p27),
      XWITCCN2 (XWITCCN2_p27), AYQJTMD (AYQJTMD_p27), EAPGLE (EAPGLE_p27),
      JKQEWGV1/JKQEWGV2/JKQEWGV3 (LocalAuto23:954/962/971),
      MHAEYJN (MHAEYJN_p37), ZLZTHIC (ZLZTHIC_p14), VPWSHTO (VPWSHTO_p15),
      UAGHHBM (UAGHHBM_p30), YXIONXL2 (YXIONXL2_p13/_p33),
      YXIONXL3 (LocalAuto12:665, YXIONXL3_p33), LKGRQUI (LKGRQUI_p27),
      HXHYTIJ (HXHYTIJ_p27), ODXLSTCv2 (ODXLSTCv2_p28/_p31),
      IMJXPHRv2 (IMJXPHRv2_p28), NUXCOEAv2 (NUXCOEAv2_p28),
      PQCSXWG1 (PQCSXWG1_p11), EYYPQDW (EYYPQDW_p17), FEKTYIY (FEKTYIY_p27),
      AURSIPD (AURSIPD_p18), PPBTYDQ (PPBTYDQ_p26), MXQTIED (MXQTIED_p26),
      SYNQIWN (SYNQIWN_p22), AXJRPNC (AXJRPNC_p26), RRCWNSJ (RRCWNSJ_p26),
      JCYFMRP (JCYFMRP_p27), TFITSKC (TFITSKC_p27), CQAOQLR (CQAOQLR_p16),
      JLXFDMJ (JLXFDMJ_p27), AQICLXA (LocalAuto20:507),
      FUNOUYH (FUNOUYH_SLICE, LocalAuto20:514), OEHDBEN (LocalAuto20:802),
      HIJQAHA (HIJQAHA_p29), CNICGSF1-5 (LocalAuto18:1091-1120),
      ARDBZYE (ARDBZYE_p33), FYSSVEV (FYSSVEV_p33), NWDGKXH (NWDGKXH_p32),
      YOBIMPP (YOBIMPP_p32), MIQMCSN (MIQMCSN_p32), LFLACKU (LFLACKU_p23),
      BKOSSGE (BKOSSGE_p16), QKNVMLB1 (QKNVMLB1_p35),
      QKNVMLB2 (QKNVMLB2_p35).

  (d) Twin proved (code-complete) but shape delta is not bridgeable (8):
      PQCSXWG2 — PQCSXWG2_p11 concludes continuity of `mkSimplex1_p11`, whose
        `d5` is `deltaX5f` (`... - x1*x3 - x4*x6 + x1*x4`, Nonlin_def.hl
        rendering) while LocalAuto1.`mkSimplex1` uses its local `deltaX5`
        (sphere.hl verbatim, without those terms): the two completions differ,
        so the twin does not transfer.
      EYYPQDW2 — EYYPQDW2_p17 needs an extra `s = 1 ∨ s = -1` antecedent
        (absent from the registry concl); the unused-in-kernel positivity
        input `upsX_pos_of_noncollinear_p17` is private to LocalAuto17, and
        the concl's hypotheses do not pin `s`.
      TBRMXRZ1 — TBRMXRZ1_p22 composes in the opposite order (`g ∘ f`, needs
        the inner slope `g'` and `0 < f'` which the registry concl does not
        carry).
      VPWSHTO — VPWSHTO_PRIME_p15 concludes a different form (∃ i ∈ Icc 0 4
        with diagonal bounds ≤ 1+√5) and lacks the registry concl's
        `2 < dist` disjuncts.
      XWNHLMD — XWNHLMD_p26 has an extra `s.d ≤ s'.d` antecedent not carried
        by (nor derivable from) the registry concl.
      CUXVZOZ / CJBDXXN — the p21 twins take `mainNonlinearTerminalV11_p21`,
        a *different* opaque registry Prop from LocalAuto1's
        `main_nonlinear_terminal_v11`; no bridge exists between the two
        anchors.
      QKNVMLB3 — QKNVMLB3_p35 uses the index convention `vv (i % s'.k +
        p % s.k)` where the registry concl uses `vv ((i + p) % s'.k)`; the
        conventions disagree off the mod boundary and no transport is
        derivable.

  IMPORT CAVEATS.  (1) `Kepler.Text.LocalAnchors` cannot be co-imported with
  `Kepler.Text.LocalAuto1` at all: both declare `Kepler.Text.scsBasicV39`
  (the anchor's `J`-explicit predicate vs the appendix record lane's
  `unadornedV39 s ∧ ∀ i j, s.J i j = False`), and importing both fails with
  `environment already contains 'Kepler.Text.scsBasicV39'` — this is exactly
  why the anchor lane deliberately does not import the appendix lane.  This
  assembly therefore imports the appendix lane (everything here is phrased in
  LocalAuto1's vocabulary); LocalAnchors' three EXTERNAL-ANCHOR sorries
  (`scsTerminalEdgeEq2Anchor`, `scs4I2Imp4T1Anchor`, `scsSliceArrowAnchor`)
  stay untouched in their own module.
  (2) `Kepler.Text.LocalAuto3` fails to build on this checkout
  (pre-existing elaboration errors at LocalAuto3.lean:757+), and
  LocalAuto5/6/10/35 import it; those five modules are therefore not imported
  here.  No owed discharge lives in them (the QKNVMLB trio's twins live in
  LocalAuto35 and are blocked under (c)/(d) regardless).
  (3) The corpus carries two mutually-exclusive kit branches: PackingAuto18
  (`atn2PA18`/`upsXPA18`/`cross3`) vs PackingAuto20/21/25 (same names, re-rendered).
  LocalAuto1's tree loads the former; `Kepler.Text.LocalAuto2` imports
  `Kepler.Text.PackingAuto20`, so LocalAuto2 and its dependents LocalAuto9
  and LocalAuto11 cannot be co-imported with LocalAuto1.  Those three are
  skipped — no owed discharge lives in them (LocalAuto11's PQCSXWG twins are
  blocked under (d) regardless).

  Every `<name>_discharged` below is `sorry`-free; note the discharged
  statements transitively rest on upstream sorry'd inputs of their waves
  (the DISCHARGES convention of the corpus), which is the registry's
  intended granularity.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto7
import Kepler.Text.LocalAuto8
import Kepler.Text.LocalAuto12
import Kepler.Text.LocalAuto13
import Kepler.Text.LocalAuto14
import Kepler.Text.LocalAuto15
import Kepler.Text.LocalAuto16
import Kepler.Text.LocalAuto17
import Kepler.Text.LocalAuto18
import Kepler.Text.LocalAuto19
import Kepler.Text.LocalAuto20
import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto24
import Kepler.Text.LocalAuto25
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto27
import Kepler.Text.LocalAuto28
import Kepler.Text.LocalAuto29
import Kepler.Text.LocalAuto30
import Kepler.Text.LocalAuto31
import Kepler.Text.LocalAuto32
import Kepler.Text.LocalAuto33
import Kepler.Text.LocalAuto34
import Kepler.Text.LocalAuto36
import Kepler.Text.LocalAuto37
import Kepler.Text.LocalAuto38
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Shims (explicit bridging lemmas, documented in the ledger) -/

/-- Bridge for `cross3` continuity (LocalAuto17's helper of the same shape is
private): `cross3 u w` is the Mathlib `crossProduct` (a `LinearMap` in `w`)
read back into `V3`. -/
private theorem continuousAt_cross3_right_lc (u v : V3) :
    ContinuousAt (fun w : V3 => cross3 u w) v := by
  refine Continuous.continuousAt ?_
  have h1 : Continuous fun w : V3 => (w : Fin 3 → ℝ) :=
    PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have h2 : Continuous fun w : V3 =>
      (WithLp.toLp 2 (crossProduct (u : Fin 3 → ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ) : V3) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
      ((LinearMap.continuous_of_finiteDimensional
        (crossProduct (u : Fin 3 → ℝ))).comp h1)
  simpa only [cross3] using h2

/-- Bridge for the target-set permutations of the LocalAuto33 arrow twins:
`scsArrowV39` is invariant under replacement of the target set by an equal
one. -/
private theorem arrowSetRight {S1 S2 T : Set ScsV39} (h : scsArrowV39 S1 S2)
    (he : S2 = T) : scsArrowV39 S1 T := by
  rw [← he]; exact h

/-! ## Discharges -/

/-- `LocalAuto1.YXIONXL1_concl` discharged by the proved LocalAuto12 twin
(verbatim twin). -/
theorem YXIONXL1_discharged :
    ∀ (s t : ScsV39), isScsV39 s → transferV39 s t → scsArrowV39 {s} {t} :=
  @YXIONXL1

/-- `LocalAuto1.EYYPQDW3_concl` discharged through the LocalAuto17 kit.
`EYYPQDW3_p17` would need an extra `s = 1 ∨ s = -1` antecedent (which its own
continuity kernel never uses): `mk_planar2` is affine-plus-cross3 in its `v2`
slot with an `s`-scalar that is *constant* in `v2`, so the continuity holds
for every `s` — re-derived here from the proved representation lemma. -/
theorem EYYPQDW3_discharged :
    ∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsXPA18 x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2 := by
  intro v0 v1 v2 x1 x2 x3 x5 x6 s _h1 _h2 _h3 _h5 _h6 _hnc _hx1 _hx2 _hx6 _hups
  rw [MK_PLANAR_V3_DEFOR_V2_FUN_p17 v0 v1 x1 x2 x3 x5 x6 s]
  simp only [v3DeforV2_p17]
  have hc : ContinuousAt
      (fun w : V3 => cross3 (v1 - v0) (cross3 (v1 - v0) (w - v0))) v2 :=
    (continuousAt_cross3_right_lc _ _).comp
      ((continuousAt_cross3_right_lc _ _).comp
        (continuousAt_id.sub continuousAt_const))
  refine ContinuousAt.add ?_ continuousAt_const
  refine ContinuousAt.add continuousAt_const ?_
  exact hc.const_smul (s / x1 * Real.sqrt (upsXPA18 x1 x3 x5 / upsXPA18 x1 x2 x6))

/-- `LocalAuto1.GSXRFWM_concl` discharged by the proved LocalAuto33 twin
(verbatim twin; modulo the wave's own sorried `GSXRFWM1_p33` input). -/
theorem GSXRFWM_discharged :
    ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → s.k = 4 → v ∈ MMsV39 s →
      scsGeneric v :=
  GSXRFWM_p33

/-- `LocalAuto1.AUEAHEH_concl` discharged by the proved LocalAuto33 twin
(verbatim; modulo the wave's sorried slice identity `SCS_4I1_SLICE_02_p33`). -/
theorem AUEAHEH_discharged :
    scsArrowV39 {scsStabDiagV39 scs4I1 0 2} {scs3M1} :=
  AUEAHEH_p33

/-- `LocalAuto1.ZNLLLDL_concl` discharged by the proved LocalAuto33 twin
(verbatim; modulo the wave's sorried `BB_4I3_IMP_4T4_p33` input). -/
theorem ZNLLLDL_discharged :
    scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scs4T4} :=
  ZNLLLDL_p33

/-- `LocalAuto1.VQFYMZY_concl` discharged by the LocalAuto33 twin modulo the
set-permutation shim (`{scs4M6', scs4T4} = {scs4T4, scs4M6'}`). -/
theorem VQFYMZY_discharged :
    scsArrowV39 {scs4I3} {scs4T4, scs4M6'} :=
  arrowSetRight VQFYMZY_p33 (by ext t; simp; tauto)

/-- `LocalAuto1.BNAWVNH_concl` discharged by the LocalAuto33 twin modulo the
set-permutation shim (`{scs4M6', scs3M1, scs3T4} = {scs3M1, scs3T4, scs4M6'}`). -/
theorem BNAWVNH_discharged :
    scsArrowV39 {scs4M2} {scs3M1, scs3T4, scs4M6'} :=
  arrowSetRight BNAWVNH_p33 (by ext t; simp; tauto)

/-- `LocalAuto1.RAWZDIB_concl` discharged by the LocalAuto33 twin modulo the
set-permutation shim (`{scs4M6', scs3T1, scs3T6'} = {scs3T1, scs3T6', scs4M6'}`). -/
theorem RAWZDIB_discharged :
    scsArrowV39 {scs4M3'} {scs3T1, scs3T6', scs4M6'} :=
  arrowSetRight RAWZDIB_p33 (by ext t; simp; tauto)

/-- `LocalAuto1.MFKLVDK_concl` discharged by the LocalAuto33 twin modulo the
set-permutation shim
(`{scs4M7, scs3T3, scs3M1, scs3T4} = {scs3M1, scs3T4, scs3T3, scs4M7}`). -/
theorem MFKLVDK_discharged :
    scsArrowV39 {scs4M4'} {scs3M1, scs3T4, scs3T3, scs4M7} :=
  arrowSetRight MFKLVDK_p33 (by ext t; simp; tauto)

/-- `LocalAuto1.RYPDIXT_concl` discharged by the LocalAuto33 twin modulo the
set-permutation shim (`{scs4M8, scs3T4} = {scs3T4, scs4M8}`). -/
theorem RYPDIXT_discharged :
    scsArrowV39 {scs4M5'} {scs3T4, scs4M8} :=
  arrowSetRight RYPDIXT_p33 (by ext t; simp; tauto)

end Kepler.Text
