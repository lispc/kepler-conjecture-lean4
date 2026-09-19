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

  Re-swept 2026-09-19 against LocalAuto2-38 (all upstream fill waves,
  incl. LA17 master EYYPQDW_p17, LA12 prop_equ/YXIONXL3 chain, LA27
  unadorned_MMs/HXHYTIJ twins, LA34 V3_DEFOR tower, LA29 SCS_*_IS_SCS,
  LA36 SCS_*_IS_TRI_STABLE, LA25 ZITHLQN_CASE_4/5/6, LA20 OEHDBEN).

  Discharged: 16        Blocked: 74

  Discharged here (twin · shape status):
    YXIONXL1_discharged  := LocalAuto12.YXIONXL1       (verbatim twin)
    YXIONXL3_discharged  := LocalAuto12.YXIONXL3       (verbatim twin; NEW
                                2026-09-19 -- LA12 now proves it in-file via
                                PROP_EQU_IS_SCS + TRANS_MMS_SUBSET)
    EYYPQDW_discharged   := LocalAuto17.EYYPQDW_p17    (verbatim twin; NEW
                                2026-09-19 -- the master Cayley-identity
                                fill wave landed)
    EYYPQDW2_discharged  := LocalAuto17 kit via shim   (NEW 2026-09-19; twin
                                had extra `s = 1 OR s = -1` antecedent; shim
                                re-derives the x3-slice continuity from
                                `MK_PLANAR_V3_DEFOR_V1_FUN_p17` +
                                `continuousAt_sqrt_upsX_mid` -- `s` is a
                                constant scalar, no sign input needed)
    EYYPQDW3_discharged  := LocalAuto17 kit via shim   (twin had extra
                                `s = 1 OR s = -1` antecedent, unused by the
                                continuity kernel; shim re-derives the v2
                                continuity from `MK_PLANAR_V3_DEFOR_V2_FUN_p17`)
    unadorned_MMs_discharged := LocalAuto27.unadorned_MMs_p27 (verbatim
                                twin; NEW 2026-09-19 -- definitional proof)
    HXHYTIJ_discharged   := LocalAuto27.HXHYTIJ_p27    (verbatim twin; NEW
                                2026-09-19)
    PQCSXWG2_discharged  := LocalAuto11.PQCSXWG2_p11   (NEW 2026-09-19; via
                                shim `mkSimplex1_eq_p11` -- post the
                                2026-09-17 deltaX5 dedup the two defs are
                                term-identical (`rfl`); `Collinear3` is
                                definitionally `Collinear R {.,.,.}`. The
                                former (d) body-mismatch blocker is void.)
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

  (b) Twin is circular -- it is proved *from* the LocalAuto1 registry sorry
      itself (re-export), so a discharge would be vacuous (11):
      ZITHLQN (ZITHLQN_p25 = `ZITHLQN_concl h`; the PROVED CASE_3/4/5/6_p25
        are only BBs-realisation components, not the implication),
      WGDHPPI (WGDHPPI_p25), TUAPYYU (TUAPYYU_p25 = `fun _ => TUAPYYU_concl`),
      YEBWJNG (YEBWJNG_p25), WKZZEEH (WKZZEEH_p25), PWEIWBZ (PWEIWBZ_p25),
      VASYYAU (VASYYAU_p25), WKEIDFT (WKEIDFT_concl_p24 = `WKEIDFT_concl`;
      the v2 `WKEIDFT`/`WKEIDFT_EQU_V2` remain sorried),
      PEDSLGV1 (LocalAuto20.PEDSLGV1), PEDSLGV2 (LocalAuto20.PEDSLGV2),
      OIQKKEP (OIQKKEP_p26 = `exact OIQKKEP_concl ...`).

  (c) Downstream twin exists but is itself sorried (45):
      XWITCCN (LA36 CASE_3/4/5 + LA24 CASE_* all sorried; no master),
      XWITCCN2 (XWITCCN2_p27), AYQJTMD (AYQJTMD_p27), EAPGLE (EAPGLE_p27),
      JKQEWGV1/JKQEWGV2/JKQEWGV3 (LocalAuto23 twins sorried),
      MHAEYJN (MHAEYJN_p37; LA37 currently does not build, see caveat 5),
      ZLZTHIC (ZLZTHIC_p14), UAGHHBM (UAGHHBM_p30 sorried; needs the
        restriction-isScs fork not in any importable lane),
      YXIONXL2 (YXIONXL2_p33 sorried with extra `3 < s.k` antecedent;
        YXIONXL2_p13 lives on the wrong lane type `ScsV39P13`),
      LKGRQUI (LKGRQUI_p27), ODXLSTCv2 (ODXLSTCv2_p28/_p31),
      IMJXPHRv2 (IMJXPHRv2_p28; LA34's IMJXPHR_p34 master still sorried),
      NUXCOEAv2 (NUXCOEAv2_p28), PQCSXWG1 (PQCSXWG1_p11),
      FEKTYIY (FEKTYIY_p27), AURSIPD (AURSIPD_p18), PPBTYDQ (PPBTYDQ_p26),
      MXQTIED (MXQTIED_p26), SYNQIWN (SYNQIWN_p22), AXJRPNC (AXJRPNC_p26),
      RRCWNSJ (RRCWNSJ_p26), JCYFMRP (JCYFMRP_p27 + _V2/_V3_p29),
      TFITSKC (TFITSKC_p27), CQAOQLR (CQAOQLR_p16), JLXFDMJ (JLXFDMJ_p27),
      AQICLXA (LocalAuto20), FUNOUYH (FUNOUYH_SLICE, LocalAuto20),
      HIJQAHA (HIJQAHA_p29), CNICGSF1-5 (LocalAuto18 twins sorried),
      ARDBZYE (ARDBZYE_p33), FYSSVEV (FYSSVEV_p33), NWDGKXH (NWDGKXH_p32),
      YOBIMPP (YOBIMPP_p32), MIQMCSN (MIQMCSN_p32), LFLACKU (LFLACKU_p23),
      BKOSSGE (BKOSSGE_p16), QKNVMLB1 (QKNVMLB1_p35),
      QKNVMLB2 (QKNVMLB2_p35), YRTAFYH (YRTAFYH_p17, giant case tree;
        newly tracked -- was missing from the previous ledger's lists).

  (d) Twin proved (code-complete) but shape delta is not bridgeable (7):
      OEHDBEN -- LocalAuto20.OEHDBEN/OEHDBEN_PRIME are now PROVED but (i)
        consume `main_nonlinear_terminal_v11` (opaque registry Prop, no
        bridge to the LA21 anchor) and (ii) conclude the target
        `{scs6T1, scs5M1, scs4M2, scs3M1}` where the registry concl wants
        `scs3T1` in that slot.
      PQCSXWG2 -- discharged 2026-09-19, see above (the former body-mismatch
        blocker was voided by the deltaX5 dedup).
      EYYPQDW2 -- discharged 2026-09-19, see above.
      TBRMXRZ1 -- TBRMXRZ1_p22 composes in the opposite order (`g o f`, needs
        the inner slope `g'` and `0 < f'` which the registry concl does not
        carry; it concludes `reEqvl h' g'` vs the registry's `reEqvl f' h'`).
      VPWSHTO -- VPWSHTO_p15 (base, still sorried) and VPWSHTO_PRIME_p15
        conclude the `EXISTS i IN Icc 0 4` diagonal-bounds form and lack the
        registry concl's `2 < dist`/distinctness witness conjuncts.
      XWNHLMD -- XWNHLMD_p26 has an extra `s.d <= s'.d` antecedent not carried
        by (nor derivable from) the registry concl, and its kernel
        XWNHLMD_MM_p26 is still sorried.
      CUXVZOZ / CJBDXXN -- the p21 twins take `mainNonlinearTerminalV11_p21`,
        a *different* opaque registry Prop from LocalAuto1's
        `main_nonlinear_terminal_v11`; no bridge exists between the two
        anchors.
      QKNVMLB3 -- QKNVMLB3_p35 is now PROVED, but its realisation arguments
        use the index convention `vv (i % s'.k + p % s.k)` and the
        `scsHalfSliceV39 s p q d' mkj = s'` equation form, where the registry
        concl uses `vv ((i + p) % s'.k)` and the `(s', s'') = scsSliceV39 ...`
        tuple form; the conventions disagree off the mod boundary and no
        transport is derivable.

  Sweep notes (2026-09-19).  LA29's 16 `SCS_*_IS_SCS`, LA36's 8
  `SCS_*_IS_TRI_STABLE`, LA34's `BBS_IMP_CONVEX_LOCAL_FAN`/V3_DEFOR relabel
  tower and LA25's `ZITHLQN_CASE_4/5/6` are component lemmas feeding the
  still-sorried wave masters above; none of them is a `*_concl` twin.
  LA12's prop_equ chain (PROP_EQU_IS_SCS / TRANS_MMS_SUBSET / YXIONXL3) is
  the engine of the new YXIONXL3 discharge.

  IMPORT CAVEATS.  (1) `Kepler.Text.LocalAnchors` cannot be co-imported with
  `Kepler.Text.LocalAuto1` at all: both declare `Kepler.Text.scsBasicV39`
  (the anchor's `J`-explicit predicate vs the appendix record lane's
  `unadornedV39 s AND (ALL i j. s.J i j = False)`), and importing both fails with
  `environment already contains 'Kepler.Text.scsBasicV39'` -- this is exactly
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
  (3) LIFTED 2026-09-19: the SphereKit dedup removed the PackingAuto20/21/25
  re-renderings of `atn2`/`upsX`/`cross3`, so LocalAuto2/9/11 are now
  co-importable with LocalAuto1's tree.  `Kepler.Text.LocalAuto11` is
  imported here this wave (it hosts the proved PQCSXWG2_p11).  LocalAuto2/9
  contain no owed discharges and are pulled in only transitively.
  (4) `Kepler.Text.LocalAuto7` is dropped this wave: it declares
  `Kepler.Text.LOCAL_FAN_ORBIT_MAP_EXPLICIT`, a duplicate of the LocalAuto2
  declaration pulled in via LocalAuto11, and co-import fails with
  `environment already contains` on that name.  LocalAuto7 hosts no
  `*_concl` twins (pure polar-fan/azim/rhoNode toolkit), so nothing is lost;
  re-admit once the corpus dedups the two ports.
  (5) `Kepler.Text.LocalAuto37` is dropped this wave: it fails to build on
  this checkout -- its `XRECQNS_UPDATE_p37` proof targets the pre-upgrade
  `LocalFan = True` stub and no longer typechecks after LocalAuto1's LocalFan
  stub upgrade (in flight).  It hosts no proved twins (MHAEYJN_p37 is
  sorried; MHAEYJN stays blocked under (c) regardless); re-admit when
  LocalAuto37 is repaired.
  blocked under (d) regardless).

  Every `<name>_discharged` below is `sorry`-free; note the discharged
  statements transitively rest on upstream sorry'd inputs of their waves
  (the DISCHARGES convention of the corpus), which is the registry's
  intended granularity.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto4
import Kepler.Text.LocalAuto11
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

/-- Bridge `mkSimplex1` (LocalAuto1) and `mkSimplex1_p11` (LocalAuto11):
post the 2026-09-17 `deltaX5` dedup both bodies are term-identical —
LocalAuto1's `mkSimplex1` resolves `d`/`d5`/`d4` against the canonical
`SphereKit` defs and its `cross3` is definitionally the `toLp`/`crossProduct`
read-back that `mkSimplex1_p11` spells out. -/
private theorem mkSimplex1_eq_p11 (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) :
    mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 =
      mkSimplex1_p11 v0 v1 v2 x1 x2 x3 x4 x5 x6 := rfl

/-- Bridge for `EYYPQDW2`: continuity of the `mk_planar2` `x3`-slice's
`sqrt` factor. `upsX x1 · x5` is a polynomial in the middle slot and the
denominator `upsX x1 x2 x6` is a constant (rendered as a product by the
inverse to stay junk-safe when it is `0`); `Real.sqrt` is continuous
everywhere under the junk-value convention. Note no `s = ±1` sign input is
needed — `s` is a constant scalar of the slice. -/
private theorem continuousAt_sqrt_upsX_mid {x1 x3 x5 : ℝ} :
    ContinuousAt
      (fun q : ℝ => Real.sqrt (upsX x1 q x5 / upsX x1 x2 x6)) x3 := by
  have hup : Continuous fun q : ℝ => upsX x1 q x5 := by
    simp only [upsX]; continuity
  simp only [div_eq_mul_inv]
  exact Real.continuous_sqrt.continuousAt.comp
    (hup.continuousAt.mul continuousAt_const)

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
      0 < upsX x1 x3 x5 →
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
  exact hc.const_smul (s / x1 * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6))

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

/-- `LocalAuto1.YXIONXL3_concl` discharged by the LocalAuto12 twin
(`YXIONXL3`, now PROVED in-file via `PROP_EQU_IS_SCS` + `TRANS_MMS_SUBSET`;
verbatim twin). -/
theorem YXIONXL3_discharged : ∀ (s : ScsV39) (i : ℕ), isScsV39 s →
    scsArrowV39 {s} {scsPropEquV39 s i} :=
  @YXIONXL3

/-- `LocalAuto1.EYYPQDW_concl` discharged by the LocalAuto17 master
`EYYPQDW_p17` (fill wave 2026-09-19, via the proved Cayley-norm identities);
verbatim twin. -/
theorem EYYPQDW_discharged :
    ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 → s = 1 ∨ s = -1 →
      v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s →
      Coplanar ({v0, v1, v2, v3} : Set V3) ∧
      x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
      ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0) :=
  @EYYPQDW_p17

/-- `LocalAuto1.EYYPQDW2_concl` discharged through the LocalAuto17 kit with a
sign-elimination shim. `EYYPQDW2_p17` needs an extra `s = 1 ∨ s = -1`
antecedent (absent from the registry concl); but `s` is a *constant* scalar
of the `x3`-slice, so the continuity holds for every `s` — re-derived here
from `MK_PLANAR_V3_DEFOR_V1_FUN_p17` + `continuousAt_sqrt_upsX_mid` (which
only consumes the registry hypothesis `0 < upsX x1 x3 x5`). -/
theorem EYYPQDW2_discharged :
    ∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3 := by
  intro v0 v1 v2 x1 x2 x3 x5 x6 s h1 _ _ _ _ _ _ _ _ _
  have hcore : ContinuousAt
      (fun x3 : ℝ => v3DeforV1_p17 s (v1 - v0) (v2 - v0) x1 x2 x5 x6 x3 + v0) x3 := by
    unfold v3DeforV1_p17
    refine ContinuousAt.add ?_ continuousAt_const
    have hq : Continuous fun q : ℝ => x1 + q - x5 := by continuity
    have hA : ContinuousAt
        (fun q : ℝ => ((x1 + q - x5) / (2 * x1)) • (v1 - v0 : V3)) x3 :=
      (hq.continuousAt.div
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ) * x1) x3)
        (by linarith : (2 : ℝ) * x1 ≠ 0)).smul
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (v1 - v0 : V3)) x3)
    have hB : ContinuousAt (fun q : ℝ =>
        ((s / x1) * Real.sqrt (upsX x1 q x5 / upsX x1 x2 x6)) •
          cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0))) x3 :=
      (continuousAt_const : ContinuousAt (fun _ : ℝ => s / x1) x3).mul
        continuousAt_sqrt_upsX_mid |>.smul
        (continuousAt_const : ContinuousAt (fun _ : ℝ =>
          cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0))) x3)
    exact hA.add hB
  exact ContinuousAt.congr hcore
    (Filter.Eventually.of_forall fun q =>
      congrFun (MK_PLANAR_V3_DEFOR_V1_FUN_p17 v0 v1 v2 x1 x2 x5 x6 s).symm q)

/-- `LocalAuto1.unadorned_MMs_concl` discharged by the proved LocalAuto27
twin `unadorned_MMs_p27` (definitional: for an unadorned system the
str/lo/hi guards are `False`-vacuous; verbatim twin). -/
theorem unadorned_MMs_discharged :
    ∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s :=
  @unadorned_MMs_p27

/-- `LocalAuto1.HXHYTIJ_concl` discharged by the proved LocalAuto27 twin
`HXHYTIJ_p27` (verbatim twin). -/
theorem HXHYTIJ_discharged : ∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww :=
  @HXHYTIJ_p27

/-- `LocalAuto1.PQCSXWG2_concl` discharged by the proved LocalAuto11 twin
`PQCSXWG2_p11` (the registry's former (d)-blocker is gone: post the
2026-09-17 `deltaX5` dedup `mkSimplex1 = mkSimplex1_p11` — shim
`mkSimplex1_eq_p11` — and `Collinear3` is definitionally
`Collinear ℝ {·, ·, ·}`). -/
theorem PQCSXWG2_discharged : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    ContinuousAt (fun q => mkSimplex1 v0 v1 v2 x1 x2 x3 x4 q x6) x5 := by
  intro v0 v1 v2 v3 x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 hnc hx1 hx2 hx6 hd _hv3
  have h := PQCSXWG2_p11 v0 v1 v2 x1 x2 x3 x4 x5 x6
    ⟨h1, h2, h3, h4, h5, h6, hnc, hx1, hx2, hx6, hd⟩
  simpa only [mkSimplex1_eq_p11] using h

end Kepler.Text
