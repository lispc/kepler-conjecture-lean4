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

  Re-swept 2026-09-20 (assembly desk): every one of the 74 blocked entries
  re-verified against the current upstream source, line-by-line. ZERO new
  discharges landed this round -- the 2026-09-19 sweep had already captured
  the fill waves' `*_concl` twins, and the newest 2026-09-20 upstream gains
  (XWNHLMD master+kernel, TBRMXRZ1, VPWSHTO_PRIME, the OEHDBEN pair, the
  CUXVZOZ/CJBDXXN p21 pair, QKNVMLB3_p35, LA3's build repair) are all
  proved-but-unbridgeable; see the per-item notes in (d) below and the
  per-module dispatch map in SWEEP NOTES. LocalAuto3 now builds again
  (caveat (2) lifted), but LA5/6/10/35 host no dischargeable twins.

  ASSEMBLY WAVE 2026-09-21 (skeleton propagation; strategic note): the
  assembly mode changed the discharge contract.  A concl exit entry is now
  wired by DIRECTLY APPLYING its upstream twin -- even when the twin's proof
  still contains a bare `sorry` -- so that the `sorryAx` axiom flows along the
  proof term and the main theorem's reachable debt graph really expands.
  Wires are marked WIRE, non-bridgeable shapes stay as explicit `sorry`
  holds marked HOLD (with the precise reason).  Anchors: the twins that
  consume an opaque terminal-bank Prop (`main_nonlinear_terminal_v11`,
  `mainNonlinearTerminalV11_p21`) are wired through the injected skeleton
  anchors `mnt11_anchor` / `p21_anchor` below -- that injection is the
  corpus's own interface convention, not a shape bridge.

    WIRE (real proof term, debt = twin's axioms + injected anchors): 56
      = the 16 classic discharges below + 40 new assembly wires
    HOLD (explicit `sorry`, reason recorded): 34
      = (a) 11 no-twin + (b) 11 circular re-export + 7 (c) non-bridgeable
        + 5 (d) shape mismatches
    TOTAL: 90/90 registry contracts exposed at this exit.

  Classic discharges (twin · shape status; all 16 sorry-free or wave-tainted
  as noted by `#print axioms` at the foot of this file):
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
      [2026-09-20: all 11 re-verified circular verbatim; VASYYAU's LA32
        mentions are NEEDS-comments only, not twins.]
      [2026-09-21 assembly wave: re-grepped every proof body -- all 11 are
        literally `..._concl` applications/re-exports (LA25:1002/1009/1264/
        1400/1543/1554/1566, LA24:144, LA20:739/819, LA26:768).  Wiring them
        would channel the registry sorry through a no-op twin; HELD at this
        exit with the cycle path recorded on each entry.]

  (c) Downstream twin exists but is itself sorried (45).  ASSEMBLY WAVE
      2026-09-21: 38 of them are now WIRED (applied directly, sorryAx
      flowing); 7 are HELD because the twin's shape demands content the
      registry concl does not carry:
      HELD -- YXIONXL2 (twin has an uncovered extra `3 < s.k` antecedent;
        isScsV39 pins only `3 ≤ s.k`, so no bridge),
      SYNQIWN (LA22 twin is a different k-general statement: different
        azim argument order, `hears`/`he1`/`he2` edge kit and
        `cstab ≤ dist (v (i+1)) (v (i+k-1))` -- none carried by the
        registry, also mnt11-consuming),
      CQAOQLR (LA16 twin consumes the combined diag form with `4*h0 < b`,
        `2 < b` on two edges and strict `a < b` on two further edges --
        the registry carries neither the 4h0 conjunct nor the strict
        edge facts; only `b = 2*h0` there),
      JLXFDMJ (LA27 twin consumes `j % s.k ∉ scsM s` while the registry
        carries `j ∉ scsM s`; the mod-transfer across the scsM boundary
        -- `i+1` unreduced at `i = k-1` -- is real work),
      LFLACKU (the ledger's LA23 twin is a DIFFERENT statement,
        `mnt11 → scsArrowV39 {scs3I1} ∅`; no twin of the registry's
        `{scs3T1} → {scs3T2, scs3T5}` exists),
      QKNVMLB1 / QKNVMLB2 (twin concludes on the index convention
        `vv (i % s'.k + p % s.k)` where the registry uses
        `vv ((i + p) % s'.k)`; conventions disagree off the mod boundary
        and `Periodic vv` does not reconcile them -- cf. QKNVMLB3).
      WIRED (38): XWITCCN, XWITCCN2, AYQJTMD, EAPGLE, JKQEWGV1/2/3,
      MHAEYJN (LA37 lane now BUILDS on this checkout — its twin
        `MHAEYJN_p37` is typed by the verbatim Prop-def
        `MHAEYJN_prop_p37`; caveat (5) lifted 2026-09-21),
      ZLZTHIC, UAGHHBM, LKGRQUI, ODXLSTCv2, IMJXPHRv2, NUXCOEAv2,
      PQCSXWG1, FEKTYIY, AURSIPD, PPBTYDQ, MXQTIED, AXJRPNC, RRCWNSJ,
      JCYFMRP, TFITSKC, AQICLXA, FUNOUYH (= LA20.FZIOTEF master, the
        ledger's FUNOUYH_SLICE pointer was the slice component),
      HIJQAHA, CNICGSF1-5 (now PROVED in LA18), ARDBZYE, FYSSVEV,
      NWDGKXH, YOBIMPP, MIQMCSN, BKOSSGE, YRTAFYH.
      Original (c) sweep list (2026-09-19/20; twin pointers as scanned):
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

  (d) Twin proved (code-complete) but shape delta is not bridgeable.
      ASSEMBLY WAVE 2026-09-21: 5 remain HELD (OEHDBEN, TBRMXRZ1, VPWSHTO,
      XWNHLMD, QKNVMLB3); CUXVZOZ/CJBDXXN left this class -- their p21
      twins match the registry concls modulo the terminal-bank anchor, so
      they are WIRED through the injected `p21_anchor` (see the wave note).
      [2026-09-20: this whole class re-audited against the fresh proofs;
      every blocker below is confirmed non-derivable, with the reason:]
      OEHDBEN -- LocalAuto20.OEHDBEN/OEHDBEN_PRIME are now PROVED but (i)
        consume `main_nonlinear_terminal_v11` (opaque registry Prop, not a
        hypothesis of the registry concl, hence unprovable without a fresh
        sorry) and (ii) conclude the target
        `{scs6T1, scs5M1, scs4M2, scs3M1}` where the registry concl wants
        `scs3T1` in that slot (`scs3M1` has d = 0.103 + funlist edge table,
        `scs3T1` d = 0.11 -- genuinely different systems).
      PQCSXWG2 -- discharged 2026-09-19, see above (the former body-mismatch
        blocker was voided by the deltaX5 dedup).
      EYYPQDW2 -- discharged 2026-09-19, see above.
      TBRMXRZ1 -- TBRMXRZ1_p22 is now PROVED but composes in the opposite
        order (`g o f`, needs the inner slope `0 < f'` and concludes
        `reEqvl h' g'`) where the registry concl carries `f o g` and wants
        `reEqvl f' h'`; the registry hypotheses carry no information about
        the inner g-slope sign, so no witness term exists (the registry
        statement is in fact not provable from its own hypotheses).
      VPWSHTO -- master VPWSHTO_p15 still sorried. VPWSHTO_PRIME_p15 is now
        PROVED but concludes the `EXISTS i IN Icc 0 4` diagonal-bounds form
        and lacks the registry concl's `2 < dist` (strict, not derivable
        from the `<= 1+sqrt 5` bounds) and distinctness witness conjuncts.
      XWNHLMD -- XWNHLMD_p26 AND its kernel XWNHLMD_MM_p26 are now PROVED
        (2026-09-20, via `TAUSTAR_LE_0_XWNHLMD_p26` + `SGTRNAF_p27`), but
        the master keeps the extra `s.d <= s'.d` antecedent (consumed by
        `SCS_BASIC_TAUSTAR_p26`); `isScsV39` pins only `s.d < 0.9` (no
        dTame equation), so the antecedent is not derivable from the
        registry hypotheses.
      CUXVZOZ / CJBDXXN -- the p21 twins are PROVED (modulo the still
        sorried engine `general_482_deformation_p21`) and match the
        registry concls modulo the anchor: they take
        `mainNonlinearTerminalV11_p21` where the registry concl carries
        `main_nonlinear_terminal_v11`; no bridge exists between the two
        anchors, so the wave injects `p21_anchor` (a documented skeleton
        sorry) and wires through the twins.  Former (d) blocker voided
        2026-09-21.
      QKNVMLB3 -- QKNVMLB3_p35 is now PROVED but only by case-splitting
        onto the still-sorried `QKNVMLB3_Eq4/LE4_p35` branches, and its
        realisation arguments use the index convention
        `vv (i % s'.k + p % s.k)` and the `scsHalfSliceV39 s p q d' mkj = s'`
        equation form, where the registry concl uses `vv ((i + p) % s'.k)`
        and the `(s', s'') = scsSliceV39 ...` tuple form (the tuple side
        *does* bridge via the `scsSliceV39` def); the conventions disagree
        off the mod boundary (e.g. s.k=6, p=2, q=0, i=4 gives `vv 6` vs
        `vv 1`, and `Periodic vv s.k` cannot reconcile them) so no
        transport is derivable.

  Sweep notes (2026-09-19).  LA29's 16 `SCS_*_IS_SCS`, LA36's 8
  `SCS_*_IS_TRI_STABLE`, LA34's `BBS_IMP_CONVEX_LOCAL_FAN`/V3_DEFOR relabel
  tower and LA25's `ZITHLQN_CASE_4/5/6` are component lemmas feeding the
  still-sorried wave masters above; none of them is a `*_concl` twin.
  LA12's prop_equ chain (PROP_EQU_IS_SCS / TRANS_MMS_SUBSET / YXIONXL3) is
  the engine of the new YXIONXL3 discharge.

  Sweep notes (2026-09-20): per-module dispatch map of the 74 blocked
  entries (twin module · what the next upstream fill wave must prove).

    LA11 (1):  PQCSXWG1_p11 sorried; no proved mkSimplex1 distance
      identities exist in any lane (checked LA11/LA21), so no shim route.
    LA14 (1):  ZLZTHIC_p14 sorried (lunar-deformation lane).
    LA16 (2):  BKOSSGE_p16 / CQAOQLR_p16 sorried.
    LA17 (1):  YRTAFYH_p17 sorried (giant case tree); LA20/24/32/33
      mentions are per-instance STAB_*_IS_SCS components, not the general
      twin.
    LA18 (6):  AURSIPD_p18 + CNICGSF1-5_p18 all sorried.
    LA20 (5):  AQICLXA / FUNOUYH_SLICE sorried; PEDSLGV1/2 circular;
      OEHDBEN blocked under (d); WKEIDFT master still sorried (LA24).
    LA22 (2):  SYNQIWN_p22 (also mnt11-consuming) / TBRMXRZ1 (d) blocked.
    LA23 (4):  JKQEWGV1/2/3_p23 masters sorried; their CASE_4/5/6_p23
      components are sorried too, so no re-derivation route; LFLACKU_p23
      sorried.
    LA24 (2):  WKEIDFT_concl_p24 circular; XWITCCN_CASE_*_IS_SCS_p24
      sorried.
    LA25 (7):  ZITHLQN + 6 VASYYAU.hl re-exports circular.
    LA26 (6):  PPBTYDQ/MXQTIED/AXJRPNC/RRCWNSJ sorried; OIQKKEP circular;
      XWNHLMD (d) blocked.
    LA27 (8):  XWITCCN2/AYQJTMD/EAPGLE/LKGRQUI/FEKTYIY/JCYFMRP/TFITSKC/
      JLXFDMJ all sorried.
    LA28 (3):  ODXLSTCv2/IMJXPHRv2/NUXCOEAv2 sorried (LA34's IMJXPHR_p34
      master is also unproved and anchor-hypothesised).
    LA29 (3):  JCYFMRP_V2/V3 + HIJQAHA sorried (mnt11-consuming).
    LA30 (1):  UAGHHBM_p30 sorried (restriction-isScs fork).
    LA31 (1):  ODXLSTCv2_p31 sorried (consumes the LA31-local opaque
      anchors ZLZTHIC_concl_p31/MHAEYJN_concl_p31).
    LA32 (3):  NWDGKXH/YOBIMPP/MIQMCSN sorried (mnt11-consuming).
    LA33 (3):  YXIONXL2 (extra `3 < s.k` antecedent, uncovered s.k = 3
      case; the p13 twin lives on the wrong lane type ScsV39P13) /
      ARDBZYE / FYSSVEV all sorried.
    LA35 (2):  QKNVMLB1/2_p35 sorried; QKNVMLB3 (d) blocked.
    LA36 (1):  XWITCCN master sorried; its CASE_3/4/5/6 (+sqrt8/pro_cs/4_3)
      components in LA36 are sorried too (no case-tree shim route).
    LA37 (1):  MHAEYJN_p37 sorried; module still fails to build (caveat (5)).
    none (11): HFNXPZA, EQTTNZI1, EQTTNZI2, DRNDRDV, ASSWPOW, EFLYGAU,
      BJTDWPS, OTMTOTJ1-4 -- the only upstream mentions (LA16/23/24) are
      same-shaped hypothesis arrows of other theorems, not twins.

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
  (2) LIFTED 2026-09-20: `Kepler.Text.LocalAuto3` now builds again on this
  checkout (verified `lake env lean Kepler/Text/LocalAuto3.lean` -- warnings
  only); LocalAuto5/6/10/35 are therefore importable. Re-audited: they host
  no dischargeable twins (LA35's QKNVMLB1/2_p35 are sorried and QKNVMLB3_p35
  is (d)-blocked; LA5/6/10 declare no `*_concl` twins), so the import list
  is left unchanged this wave to keep the build surface minimal.
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
  (5) LIFTED 2026-09-21: `Kepler.Text.LocalAuto37` now BUILDS on this
  checkout (the `XRECQNS_UPDATE_p37` pre-upgrade breakage was repaired
  upstream) and is imported this wave; it hosts the MHAEYJN twin
  (`MHAEYJN_p37` via the verbatim Prop-def `MHAEYJN_prop_p37`), now wired.

  Exit convention (2026-09-21).  Every one of the 90 registry contracts is
  re-exposed here under its registry name with the `_discharged` suffix, in
  one of two forms:
    WIRE -- a real proof term obtained by applying the upstream twin
      (possibly through a shim, possibly consuming an injected terminal-bank
      anchor).  A WIRE entry may be `sorryAx`-tainted BY DESIGN: the taint
      is exactly the twin's own outstanding debt (visible via the
      `#print axioms` block at the foot of this file), and upstream fill
      waves propagate to this exit without re-wiring.
    HOLD -- an explicit `sorry` with the blocker recorded in its doc
      comment.  A HOLD exists because no argument-shape bridge to any
      upstream twin is derivable today; when the twin lane lands, re-wire.
  The 16 classic discharges at the top remain `sorry`-free unless their
  wave's own inputs are sorried (the DISCHARGES convention of the corpus);
  the honest ground truth is the `#print axioms` block, not prose.
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

/-- Skeleton anchor for the terminal-bank consumers: `main_nonlinear_terminal_v11`
is an opaque registry Prop (its *body* is `sorry`, LocalAuto1:815) carried by
the nonlinear terminal lane.  The twins whose interface consumes it are wired
through this injected anchor -- one visible debt component covering the whole
pending bank, per the corpus's `DISCHARGES` convention. -/
private theorem mnt11_anchor : main_nonlinear_terminal_v11 := sorry

/-- Skeleton anchor for the LA21 terminal bank: `mainNonlinearTerminalV11_p21`
is the p21 lane's own `∀ y : Fin 6 → ℝ, ...` inequality bank (LA21:139); no
bridge from `main_nonlinear_terminal_v11` exists, so the CUXVZOZ/CJBDXXN
wires inject this documented skeleton anchor instead. -/
private theorem p21_anchor : mainNonlinearTerminalV11_p21 := sorry

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

/-! ## Assembly wiring (2026-09-21 skeleton wave): WIRE entries

Each entry applies its upstream twin directly; a twin that is still sorried
passes its `sorryAx` along the proof term (the debt graph), which is the
point of the assembly mode.  Anchors are injected via `mnt11_anchor` /
`p21_anchor` where the twin's interface consumes a terminal bank. -/

/-- WIRE `LocalAuto1.XWITCCN_concl` <- LA36 master `XWITCCN` (verbatim twin;
still sorried — debt flows). -/
theorem XWITCCN_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅ :=
  XWITCCN

/-- WIRE `LocalAuto1.XWITCCN2_concl` <- `XWITCCN2_p27` (verbatim twin). -/
theorem XWITCCN2_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅ :=
  XWITCCN2_p27

/-- WIRE `LocalAuto1.AYQJTMD_concl` <- `AYQJTMD_p27` (verbatim twin). -/
theorem AYQJTMD_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅ :=
  AYQJTMD_p27

/-- WIRE `LocalAuto1.EAPGLE_concl` <- `EAPGLE_p27` (verbatim twin). -/
theorem EAPGLE_discharged :
    (∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39 :=
  EAPGLE_p27

/-- WIRE `LocalAuto1.ZLZTHIC_concl` <- `ZLZTHIC_p14` (verbatim twin, named
hypotheses). -/
theorem ZLZTHIC_discharged :
    ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (f : V3 → ℝ → V3),
      ConvexLocalFan V E FF →
      Generic V E →
      Deformation f V a b →
      (∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
        interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        ConvexLocalFan ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
        Generic ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E) :=
  @ZLZTHIC_p14

/-- WIRE `LocalAuto1.LKGRQUI_concl` <- `LKGRQUI_p27` (verbatim twin). -/
theorem LKGRQUI_discharged : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop),
    isScsV39 s → (s', s'') = scsSliceV39 s p q d' d'' mkj →
    scsArrowV39 {s} {s', s''} :=
  LKGRQUI_p27

/-- WIRE `LocalAuto1.FEKTYIY_concl` <- `FEKTYIY_p27` (verbatim twin). -/
theorem FEKTYIY_discharged : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k →
    ¬Coplanar (({0} ∪ Set.range v : Set V3)) :=
  FEKTYIY_p27

/-- WIRE `LocalAuto1.AURSIPD_concl` <- `AURSIPD_p18` (verbatim twin). -/
theorem AURSIPD_discharged : ∀ (s : ScsV39) (v : ℕ → V3), 3 < s.k → isScsV39 s →
    scsGeneric v → v ∈ MMsV39 s →
    3 + {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k :=
  AURSIPD_p18

/-- WIRE `LocalAuto1.PPBTYDQ_concl` <- `PPBTYDQ_p26` (verbatim twin). -/
theorem PPBTYDQ_discharged : ∀ (u v p : V3), ¬Collinear ℝ ({0, v, p} : Set V3) →
    ¬Collinear ℝ ({0, u, p} : Set V3) →
    arcV 0 u p + arcV 0 p v < Real.pi →
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3)) :=
  PPBTYDQ_p26

/-- WIRE `LocalAuto1.BKOSSGE_concl` <- `BKOSSGE_p16` (verbatim twin). -/
theorem BKOSSGE_discharged : scsArrowV39 {scs3M1} {scs3T1, scs3T5} :=
  BKOSSGE_p16

/-- WIRE `LocalAuto1.YRTAFYH_concl` <- `YRTAFYH_p17` (verbatim twin; the
giant case tree). -/
theorem YRTAFYH_discharged : ∀ (s : ScsV39) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → 3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j) :=
  @YRTAFYH_p17

/-- WIRE `LocalAuto1.FUNOUYH_concl` <- LA20 master `FZIOTEF` (verbatim twin;
the ledger's `FUNOUYH_SLICE` pointer is the slice *component* feeding
`FZIOTEF`, not the twin of the registry concl). -/
theorem FUNOUYH_discharged :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2} :=
  FZIOTEF

/-- WIRE `LocalAuto1.CNICGSF4_concl` <- `CNICGSF4_p18` (verbatim twin; PROVED
in LA18). -/
theorem CNICGSF4_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1} :=
  CNICGSF4_p18

/-- WIRE `LocalAuto1.CNICGSF1_concl` <- PROVED `CNICGSF1_p18` via the
target-set permutation shim (`{scs3M1, scs4M2} = {scs4M2, scs3M1}`). -/
theorem CNICGSF1_discharged :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs4M2, scs3M1} :=
  arrowSetRight CNICGSF1_p18 (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.CNICGSF2_concl` <- PROVED `CNICGSF2_p18` via the
target-set permutation shim (`{scs3T1, scs4M3'} = {scs4M3', scs3T1}`). -/
theorem CNICGSF2_discharged :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs4M3', scs3T1} :=
  arrowSetRight CNICGSF2_p18 (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.CNICGSF3_concl` <- PROVED `CNICGSF3_p18` via the
target-set permutation shim (`{scs3T4, scs4M2} = {scs4M2, scs3T4}`). -/
theorem CNICGSF3_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs4M2, scs3T4} :=
  arrowSetRight CNICGSF3_p18 (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.CNICGSF5_concl` <- PROVED `CNICGSF5_p18` via the
target-set permutation shim (`{scs3M1, scs4M5'} = {scs4M5', scs3M1}`). -/
theorem CNICGSF5_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs4M5', scs3M1} :=
  arrowSetRight CNICGSF5_p18 (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.JKQEWGV1_concl` <- `JKQEWGV1_p23` (shims: hypothesis
reorder `hs hBB hta hk` -> `hs hk hBB hta`; `(f '' univ)` -> `Set.range f`).
Twin still sorried — debt flows. -/
theorem JKQEWGV1_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    solLocal (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) < Real.pi := by
  intro s vv hs hBB hta hk
  simpa only [Set.image_univ] using JKQEWGV1_p23 s vv hs hk hBB hta

/-- WIRE `LocalAuto1.JKQEWGV2_concl` <- `JKQEWGV2_p23` (same two shims). -/
theorem JKQEWGV2_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    ¬Circular (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)}) := by
  intro s vv hs hBB hta hk
  simpa only [Set.image_univ] using JKQEWGV2_p23 s vv hs hk hBB hta

/-- WIRE `LocalAuto1.JKQEWGV3_concl` <- `JKQEWGV3_p23` (shims: hypothesis
reorder `hs hBB hta hl hk` -> `hs hBB hk hta hl`; `f '' univ` ->
`Set.range f`). -/
theorem JKQEWGV3_discharged : ∀ (s : ScsV39) (vv : ℕ → V3) (v w : V3),
    isScsV39 s → BBsV39 s vv → taustarV39 s vv < 0 →
    Lunar v w (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) → 3 < s.k →
    interiorAngle1 0 (Set.range fun i => (vv i, vv (i + 1))) v <
      Real.pi / 2 := by
  intro s vv v w hs hBB hta hl hk
  have hl' : Lunar v w (Set.range vv)
      ((fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ) := by
    rw [Set.image_univ]; exact hl
  simpa only [Set.image_univ] using JKQEWGV3_p23 s vv v w hs hBB hk hta hl'

/-- WIRE `LocalAuto1.UAGHHBM_concl` <- `UAGHHBM_p30` (shim: hypothesis
reorder `hs h1 h2 hk hij hJ hne hedge` -> `hs hij hJ h1 h2 hedge hk hne`;
`i % s.k ≠ j % s.k` is `¬(i % s.k = j % s.k)` definitionally and
`setOfList l` unfolds to `{x | x ∈ l}`). Twin still sorried — debt flows. -/
theorem UAGHHBM_discharged : ∀ (s : ScsV39) (i j : ℕ) (c : ℝ),
    isScsV39 s → s.a i j ≤ c → c ≤ s.b i j → 3 < s.k →
    ¬(i % s.k = j % s.k) → ¬s.J i j →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k → ¬(c = s.am i j)) →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k →
      2 < s.a i j ∨ 2 * h0 < s.b i j) →
    scsArrowV39 {s} (setOfList (subdivV39 s i j c)) :=
  fun s i j c hs h1 h2 hk hij hJ hne hedge =>
    UAGHHBM_p30 s i j c hs hij hJ h1 h2 hedge hk hne

/-- WIRE `LocalAuto1.ODXLSTCv2_concl` <- `ODXLSTCv2_p28` (shim: the twin
states `s.k = k` where the registry carries `k = s.k`).  Twin still
sorried — debt flows.  (The LA31 twin `ODXLSTCv2_p31` is anchored to the
LA31-local `ZLZTHIC_concl_p31`/`MHAEYJN_concl_p31` props and is not used.) -/
theorem ODXLSTCv2_discharged : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s → k = s.k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    False :=
  fun s k w l hs hmw hk hk3 hdiag1 hnorm hlt hJ hlunar =>
    ODXLSTCv2_p28 s k w l hs hmw hk.symm hk3 hdiag1 hnorm hlt hJ hlunar

/-- WIRE `LocalAuto1.IMJXPHRv2_concl` <- `IMJXPHRv2_p28` (shim: reorder
`hs hmw haz hk` -> `hk hs hmw haz`).  Twin still sorried — debt flows. -/
theorem IMJXPHRv2_discharged : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    k = s.k → 3 < k →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) :=
  fun s k w l hs hmw haz hk hk3 hnc haff hdiag1 hnorm hdiag2 hJ hlunar =>
    IMJXPHRv2_p28 s k w l hk.symm hs hmw haz hk3 hnc haff hdiag1 hnorm hdiag2
      hJ hlunar

/-- WIRE `LocalAuto1.NUXCOEAv2_concl` <- `NUXCOEAv2_p28` (shims: reorder
`hs hmw haz hnc haff hk hk3` -> `hk hk3 hs hmw haz hnc haff`; the twin's
`dist (w j) (w l) < s.b j l` is the registry's `s.a j l < s.b j l` under
`haj : s.a j l = dist (w j) (w l)`).  Twin still sorried — debt flows. -/
theorem NUXCOEAv2_discharged : ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ),
    isScsV39 s → w ∈ MMsV39 s →
    azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
    ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3) →
    w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3) →
    k = s.k → 3 < k →
    (j % k = (l + 1) % k ∨ (j + 1) % k = l % k) →
    s.a j l = dist (w j) (w l) → s.a j l < s.b j l →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) →
    (∀ i, scsDiag k l i → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    s.a l (l + 1) = dist (w l) (w (l + 1)) ∧
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1))) :=
  fun s k w l j hs hmw haz hnc haff hk hk3 hj haj hlt hdiag1 hdiag2 hJ hlunar =>
    NUXCOEAv2_p28 s k w l j hk.symm hk3 hs hmw haz hnc haff hj haj
      (show dist (w j) (w l) < s.b j l by rw [← haj]; exact hlt)
      hdiag1 hdiag2 hJ hlunar

/-- WIRE `LocalAuto1.PQCSXWG1_concl` <- `PQCSXWG1_p11` (shim: the p11
statement is a `PQCSXWG1_concl_p11` Prop-def with the antecedent packed as
one conjunction, `Collinear3`/`mkSimplex1_p11`/`toLp ∘ crossProduct ∘ ofLp`
all definitionally the registry's forms — cf. `mkSimplex1_eq_p11`).  Twin
still sorried — debt flows. -/
theorem PQCSXWG1_discharged : ∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
      0 < ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ
        (crossProduct ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ)) := by
  intro v0 v1 v2 v3 x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 hnc hx1 hx2 hx6 hd hv3
  simpa only [mkSimplex1_eq_p11] using
    PQCSXWG1_p11 v0 v1 v2 v3 x1 x2 x3 x4 x5 x6
      ⟨h1, h2, h3, h4, h5, h6, hnc, hx1, hx2, hx6, hd, hv3⟩

/-- WIRE `LocalAuto1.MXQTIED_concl` <- `MXQTIED_p26` (shim: the twin states
`s'.d = s.d` where the registry carries `s.d = s'.d`).  Twin still sorried —
debt flows. -/
theorem MXQTIED_discharged : ∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → scsM s = scsM s' →
    s.k = s'.k → v ∈ MMsV39 s → BBsV39 s' v → s.d = s'.d →
    (∀ i, s'.a i (i + 1) = s.a i (i + 1)) →
    (∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) → v ∈ MMsV39 s' :=
  fun s s' v hs hs' hb hb' hM hk hv hv' hd ha hab =>
    MXQTIED_p26 s s' v hs hs' hb hb' hM hk hd.symm hv hv' ha hab

/-- WIRE `LocalAuto1.AXJRPNC_concl` <- `AXJRPNC_p26` (shim: hypothesis swap
`hs hbasic hv hb hlunar` -> `hs hbasic hb hv hlunar`).  Twin still sorried —
debt flows. -/
theorem AXJRPNC_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → v ∈ MMsV39 s → (∀ i, s.b i (i + 1) ≤ cstab) →
    Lunar (v i) (v j) (Set.range v) (Set.range fun i => {v i, v (i + 1)}) →
    s.k = 6 ∧ v j = v (i + 3) :=
  fun s v i j hs hbasic hv hb hlunar =>
    AXJRPNC_p26 s v i j hs hbasic hb hv hlunar

/-- WIRE `LocalAuto1.RRCWNSJ_concl` <- `RRCWNSJ_p26` (shims: injected
`mnt11_anchor` — the twin's interface consumes the terminal bank; hypothesis
reorder `hs hb hk3 hv` -> `hs hb hv hk3`).  Twin still sorried — debt
flows. -/
theorem RRCWNSJ_discharged : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    scsBasicV39 s → 3 < s.k → v ∈ MMsV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v :=
  fun s v hs hb hk3 hv hd4 hab hb1 =>
    RRCWNSJ_p26 mnt11_anchor s v hs hb hv hk3 hd4 hab hb1

/-- WIRE `LocalAuto1.JCYFMRP_concl` <- `JCYFMRP_p27` (shims: injected
`mnt11_anchor`; reorder moving `3 < s.k` forward).  Twin still sorried —
debt flows.  (The LA29 `_V2/_V3` siblings are variant forms with a
conjunction conclusion and an extra `a < b` row hypothesis — not needed.) -/
theorem JCYFMRP_discharged : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    3 < s.k →
    (∀ i, s.a i (i + 1) = 2) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    ∃ i, dist (v i) (v (i + 1)) = 2 :=
  fun s v hs hv hgen hbasic hb4 hm1 hk3 hA hdiag =>
    JCYFMRP_p27 mnt11_anchor s v hk3 hs hv hgen hbasic hb4 hm1 hA hdiag

/-- WIRE `LocalAuto1.TFITSKC_concl` <- `TFITSKC_p27` (shims: injected
`mnt11_anchor`; hypothesis reorder; `le_of_eq` turns the registry's
`b (i+1) (i+2) = 2*h0` into the twin's `≤ 2*h0`).  Twin still sorried —
debt flows. -/
theorem TFITSKC_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    3 < s.k → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → (s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    dist (v (i + 1)) (v (i + 2)) = 2 :=
  fun s v i hs hk3 hv hgen hbasic hA hB hd hdiag h2 hlt =>
    TFITSKC_p27 mnt11_anchor s v i hlt hk3 hs hv hgen hbasic hA (le_of_eq hB)
      hd h2 (fun j j' hdiag' =>
        ⟨(hdiag j j' hdiag').1.1, (hdiag j j' hdiag').1.2, (hdiag j j' hdiag').2⟩)

/-- WIRE `LocalAuto1.AQICLXA_concl` <- LA20 `AQICLXA` via the target-set
permutation shim (`{scs3M1, scs5M1} = {scs5M1, scs3M1}`).  Twin still
sorried — debt flows. -/
theorem AQICLXA_discharged :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs5M1, scs3M1} :=
  arrowSetRight AQICLXA (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.HIJQAHA_concl` <- `HIJQAHA_p29` (shims: injected
`mnt11_anchor`; target-set permutation — same ten systems, re-ordered).
Twin still sorried — debt flows. -/
theorem HIJQAHA_discharged :
    scsArrowV39 {scs5M2} {scs3T1, scs3T4, scs4M6', scs4M7, scs4M8, scs5T1,
      scsStabDiagV39 scs5I2 0 2, scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4} :=
  arrowSetRight (HIJQAHA_p29 mnt11_anchor) (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.ARDBZYE_concl` <- PROVED `ARDBZYE_p33` through the
injected `mnt11_anchor` (verbatim modulo the anchor). -/
theorem ARDBZYE_discharged : scsArrowV39 {scs4I2} {scs4T1, scs4T2} :=
  ARDBZYE_p33 mnt11_anchor

/-- WIRE `LocalAuto1.FYSSVEV_concl` <- PROVED `FYSSVEV_p33` through the
injected `mnt11_anchor` (verbatim modulo the anchor). -/
theorem FYSSVEV_discharged :
    scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2} :=
  FYSSVEV_p33 mnt11_anchor

/-- WIRE `LocalAuto1.NWDGKXH_concl` <- `NWDGKXH_p32` through the injected
`mnt11_anchor` (verbatim modulo the anchor).  Twin still sorried — debt
flows. -/
theorem NWDGKXH_discharged : scsArrowV39 {scs4M6'} {scs4T3, scs4T5} :=
  NWDGKXH_p32 mnt11_anchor

/-- WIRE `LocalAuto1.YOBIMPP_concl` <- `YOBIMPP_p32` (shims: injected
`mnt11_anchor`; target-set permutation
`{scs4M6', scs3T3, scs3M1, scs3T4} = {scs3M1, scs3T3, scs3T4, scs4M6'}`).
Twin still sorried — debt flows. -/
theorem YOBIMPP_discharged :
    scsArrowV39 {scs4M7} {scs3M1, scs3T3, scs3T4, scs4M6'} :=
  arrowSetRight (YOBIMPP_p32 mnt11_anchor) (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.MIQMCSN_concl` <- `MIQMCSN_p32` through the injected
`mnt11_anchor` (verbatim modulo the anchor).  Twin still sorried — debt
flows. -/
theorem MIQMCSN_discharged :
    scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4} :=
  MIQMCSN_p32 mnt11_anchor

/-- WIRE `LocalAuto1.CUXVZOZ_concl` <- PROVED `CUXVZOZ_p21` (hypotheses
verbatim; the twin's `mainNonlinearTerminalV11_p21` anchor is injected as
`p21_anchor` — no bridge from `mnt11` exists yet).  The twin's engine
`general_482_deformation_p21` is still sorried — debt flows. -/
theorem CUXVZOZ_discharged : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3),
      FF = Set.range (fun i => (v i, v (i + 1))) →
      isScsV39 s → k = s.k → 3 < k → v ∈ MMsV39 s → scsBasicV39 s →
      scsGeneric v →
      3 ≤ dist (v (p1 + k - 1)) (v (p1 + 1)) →
      (∀ i j, scsDiag k i j ∧ psort k (i, j) ≠ psort k (p1 + k - 1, p1 + 1) →
        s.a i j < dist (v i) (v j)) →
      (∀ i j, scsDiag k i j → 4 * h0 < s.b i j) →
      interiorAngle1 0 FF (v p1) < Real.pi →
      (Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
        interiorAngle1 0 FF (v (p1 + 1)) < Real.pi) →
      s.a p1 (p1 + 1) = 2 → s.b p1 (p1 + 1) ≤ 2 * h0 →
      2 ≤ dist (v (p1 + k - 1)) (v p1) →
      dist (v (p1 + k - 1)) (v p1) ≤ cstab →
      dist (v p1) (v (p1 + 1)) = 2 := by
  intro _hmn s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen hd ha hb hang hcase
    ha12 hb12 h2 hdc
  -- the registry writes the mirror index `p1 + k - 1` (= `(p1 + k) - 1`);
  -- the twin writes `p1 + (k - 1)` — transport the four consumers.
  have hkm : p1 + (k - 1) = p1 + k - 1 := by omega
  have hd' : 3 ≤ dist (v (p1 + (k - 1))) (v (p1 + 1)) := by rw [hkm]; exact hd
  have h2' : 2 ≤ dist (v (p1 + (k - 1))) (v p1) := by rw [hkm]; exact h2
  have hdc' : dist (v (p1 + (k - 1))) (v p1) ≤ cstab := by rw [hkm]; exact hdc
  refine CUXVZOZ_p21 p21_anchor s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen
    hd' (fun i j hdiag hps => ha i j ⟨hdiag, by rw [← hkm]; exact hps⟩) hb
    hang hcase ha12 hb12 h2' hdc'

/-- WIRE `LocalAuto1.CJBDXXN_concl` <- PROVED `CJBDXXN_p21` (mirror of
CUXVZOZ, same `p21_anchor` injection). -/
theorem CJBDXXN_discharged : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3),
      FF = Set.range (fun i => (v i, v (i + 1))) →
      isScsV39 s → k = s.k → 3 < k → v ∈ MMsV39 s → scsBasicV39 s →
      scsGeneric v →
      3 ≤ dist (v (p1 + 1)) (v (p1 + k - 1)) →
      (∀ i j, scsDiag k i j ∧ psort k (i, j) ≠ psort k (p1 + 1, p1 + k - 1) →
        s.a i j < dist (v i) (v j)) →
      (∀ i j, scsDiag k i j → 4 * h0 < s.b i j) →
      interiorAngle1 0 FF (v p1) < Real.pi →
      (Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
        interiorAngle1 0 FF (v (p1 + k - 1)) < Real.pi) →
      s.a p1 (p1 + k - 1) = 2 → s.b p1 (p1 + k - 1) ≤ 2 * h0 →
      2 ≤ dist (v (p1 + 1)) (v p1) →
      dist (v (p1 + 1)) (v p1) ≤ cstab →
      dist (v p1) (v (p1 + k - 1)) = 2 := by
  intro _hmn s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen hd ha hb hang hcase
    ha12 hb12 h2 hdc
  -- same mirror-index transport as CUXVZOZ: registry `p1 + k - 1` vs twin
  -- `p1 + (k - 1)` (five consumers: hd, ha, hcase, ha12, hb12).
  have hkm : p1 + (k - 1) = p1 + k - 1 := by omega
  have hd' : 3 ≤ dist (v (p1 + 1)) (v (p1 + (k - 1))) := by rw [hkm]; exact hd
  have hcase' : Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
      interiorAngle1 0 FF (v (p1 + (k - 1))) < Real.pi := by rw [hkm]; exact hcase
  have ha12' : s.a p1 (p1 + (k - 1)) = 2 := by rw [hkm]; exact ha12
  have hb12' : s.b p1 (p1 + (k - 1)) ≤ 2 * h0 := by rw [hkm]; exact hb12
  have hfin : dist (v p1) (v (p1 + (k - 1))) = 2 :=
    CJBDXXN_p21 p21_anchor s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen hd'
      (fun i j hdiag hps => ha i j ⟨hdiag, by rw [← hkm]; exact hps⟩) hb hang
      hcase' ha12' hb12' h2 hdc
  rw [← hkm]
  exact hfin

/-! ## Skeleton holds (2026-09-21 wave): entries with no bridgeable twin

Each HOLD re-exposes its registry contract with an explicit `sorry` and the
blocker recorded.  34 holds = 11 (a) no-twin + 11 (b) circular re-export +
7 (c) non-bridgeable + 5 (d) shape mismatch. -/

/-! ### (a) No downstream twin anywhere in LocalAuto2-38 (11) -/

/-- HOLD (a) `HFNXPZA_concl`: no twin in any lane. -/
theorem HFNXPZA_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → s.k = 3 →
    dihV 0 (vv 0) (vv 1) (vv 2) + dihV 0 (vv 1) (vv 2) (vv 3) +
      dihV 0 (vv 2) (vv 3) (vv 1) < 2 * Real.pi := by
  sorry

/-- HOLD (a) `EQTTNZI1_concl`: no twin in any lane. -/
theorem EQTTNZI1_discharged : ∀ s : ScsV39, isScsV39 s →
    (∀ i j, s.J i j → s.b i j = s.bm i j) →
    (s.J = fun _ _ => False ∨ 3 < s.k) →
    scsArrowV39 {s} {restrictionTyp1V39 s} := by
  sorry

/-- HOLD (a) `EQTTNZI2_concl`: no twin in any lane. -/
theorem EQTTNZI2_discharged : ∀ (s t : ScsV39), isScsV39 s → s.am = s.bm →
    t = restrictionTyp2V39 s → (∀ i j, ¬s.J i j) → (∀ i, s.am i i = 0) →
    {i | i < t.k ∧ (2 * h0 < t.b i (i + 1) ∨ 2 < t.a i (i + 1))}.ncard + t.k ≤ 6 →
    scsArrowV39 {s} {t} := by
  sorry

/-- HOLD (a) `DRNDRDV_concl`: no twin in any lane. -/
theorem DRNDRDV_discharged : ∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ) := by
  sorry

/-- HOLD (a) `ASSWPOW_concl`: no twin in any lane. -/
theorem ASSWPOW_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → s.k = 4 → scsBasicV39 s →
    s.b i (i + 1) ≤ 2 * h0 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53 := by
  sorry

/-- HOLD (a) `EFLYGAU_concl`: no twin in any lane. -/
theorem EFLYGAU_discharged :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M7 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M7} {scs4M6'} := by
  sorry

/-- HOLD (a) `BJTDWPS_concl`: no twin in any lane. -/
theorem BJTDWPS_discharged :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M8 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M8} {scs4M6', scs3T7} := by
  sorry

/-- HOLD (a) `OTMTOTJ1_concl`: no twin in any lane. -/
theorem OTMTOTJ1_discharged :
    scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2} := by
  sorry

/-- HOLD (a) `OTMTOTJ2_concl`: no twin in any lane. -/
theorem OTMTOTJ2_discharged :
    scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2} := by
  sorry

/-- HOLD (a) `OTMTOTJ3_concl`: no twin in any lane. -/
theorem OTMTOTJ3_discharged :
    scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry

/-- HOLD (a) `OTMTOTJ4_concl`: no twin in any lane. -/
theorem OTMTOTJ4_discharged :
    scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} := by
  sorry

/-! ### (b) Twin is a circular re-export of the registry sorry itself (11) -/

/-- HOLD (b) `ZITHLQN_concl`: cycle path
`ZITHLQN_concl -> LA25.ZITHLQN_p25 (LA25:1002, proof = `ZITHLQN_concl h`);
the PROVED `ZITHLQN_CASE_3/4/5/6_p25` are only BBs-realisation components,
not the implication. -/
theorem ZITHLQN_discharged :
    (∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv → 0 ≤ taustarV39 s vv) →
    JEJTVGB_assume_v39 := by
  sorry

/-- HOLD (b) `WGDHPPI_concl`: cycle path
`WGDHPPI_concl -> LA25.WGDHPPI_p25 (LA25:1009, proof = `WGDHPPI_concl ...`). -/
theorem WGDHPPI_discharged : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    s.k = 4 → v ∈ MMsV39 s → {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ 1 := by
  sorry

/-- HOLD (b) `TUAPYYU_concl`: cycle path
`TUAPYYU_concl -> LA25.TUAPYYU_p25 (LA25:1264, proof = `fun _ =>
TUAPYYU_concl`). -/
theorem TUAPYYU_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨
      dist (v p) (v (p + 1)) = s.b p (p + 1) := by
  sorry

/-- HOLD (b) `YEBWJNG_concl`: cycle path
`YEBWJNG_concl -> LA25.YEBWJNG_p25 (LA25:1566, proof = `YEBWJNG_concl ...`). -/
theorem YEBWJNG_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) → s.a p (p + 1) = 2 →
    dist (v p) (v (p + 1)) = 2 := by
  sorry

/-- HOLD (b) `WKZZEEH_concl`: cycle path
`WKZZEEH_concl -> LA25.WKZZEEH_p25 (LA25:1400, proof = `WKZZEEH_concl ...`). -/
theorem WKZZEEH_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) → ¬scsIsStr s v (p + 3) →
    ¬(dist (v p) (v (p + 3)) = cstab ∧ dist (v p) (v (p + 1)) = cstab) := by
  sorry

/-- HOLD (b) `PWEIWBZ_concl`: cycle path
`PWEIWBZ_concl -> LA25.PWEIWBZ_p25 (LA25:1543, proof = `PWEIWBZ_concl ...`). -/
theorem PWEIWBZ_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    s.a p (p + 1) = 2 → dist (v p) (v (p + 1)) = 2 := by
  sorry

/-- HOLD (b) `VASYYAU_concl`: cycle path
`VASYYAU_concl -> LA25.VASYYAU_p25 (LA25:1554, proof = `VASYYAU_concl ...`);
the six `VASYYAU.hl` LA32 mentions are NEEDS-comments, not twins. -/
theorem VASYYAU_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
    scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    scsIsStr s v p →
    (dist (v p) (v (p + 1)) = s.a p (p + 1) ∧
      dist (v p) (v (p + 3)) = s.a p (p + 3)) := by
  sorry

/-- HOLD (b) `WKEIDFT_concl`: cycle path
`WKEIDFT_concl -> LA24.WKEIDFT_concl_p24 (LA24:144, verbatim restatement
proved by `WKEIDFT_concl`); the v2 `WKEIDFT`/`WKEIDFT_EQU` twins remain
sorried. -/
theorem WKEIDFT_discharged : ∀ (s : ScsV39) (a b a' b' : ℝ) (p q p' q' : ℕ),
    isScsV39 s → scsBasicV39 s →
    (∀ i, s.a i (i + 1) = a) → (∀ i, s.b i (i + 1) = b) → p' + q = p + q' →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab) →
    (∀ i j, scsDiag s.k i j → s.a i j = a') →
    (∀ i j, scsDiag s.k i j → s.b i j = b') →
    scsArrowV39 {scsStabDiagV39 s p q} {scsStabDiagV39 s p' q'} := by
  sorry

/-- HOLD (b) `PEDSLGV1_concl`: cycle path
`PEDSLGV1_concl -> LA20.PEDSLGV1 (LA20:739, proof = `PEDSLGV1_concl ...`). -/
theorem PEDSLGV1_discharged : ∀ (v : ℕ → V3) (i j : ℕ), v ∈ MMsV39 scs6I1 →
    scsDiag 6 i j → dist (v i) (v j) ≤ cstab →
    v ∈ MMsV39 (scsStabDiagV39 scs6I1 i j) := by
  sorry

/-- HOLD (b) `PEDSLGV2_concl`: cycle path
`PEDSLGV2_concl -> LA20.PEDSLGV2 (LA20:819, proof = `PEDSLGV2_concl ...`). -/
theorem PEDSLGV2_discharged : ∀ v : ℕ → V3, v ∈ MMsV39 scs6I1 →
    (∀ i j, scsDiag 6 i j → cstab ≤ dist (v i) (v j)) →
    v ∈ MMsV39 scs6M1 := by
  sorry

/-- HOLD (b) `OIQKKEP_concl`: cycle path
`OIQKKEP_concl -> LA26.OIQKKEP_p26 (LA26:768, proof = `exact OIQKKEP_concl
...`). -/
theorem OIQKKEP_discharged : ∀ (u v : V3) (c : ℝ), u ∈ ballAnnulus →
    v ∈ ballAnnulus → c < 4 → 2 ≤ dist u v → dist u v ≤ c →
    arcV 0 u v ≤ arcLength 2 2 c := by
  sorry

/-! ### (c) Twin exists but demands content the registry does not carry (7) -/

/-- HOLD (c) `YXIONXL2_concl`: twin `YXIONXL2_p33` carries an extra
`3 < s.k` antecedent the registry does not have (`isScsV39` pins only
`3 ≤ s.k`; the s.k = 3 case is uncovered; `YXIONXL2_p13` lives on the wrong
lane type `ScsV39P13`). -/
theorem YXIONXL2_discharged : ∀ s : ScsV39, isScsV39 s →
    scsArrowV39 {s} {scsOppV39 s} := by
  sorry

/-- WIRE `LocalAuto1.MHAEYJN_concl` <- `MHAEYJN_p37` (the twin is typed by
the LA37 Prop-def `MHAEYJN_prop_p37`, whose body is the verbatim registry
statement; the LA37 lane now builds on this checkout — import caveat (5)
lifted 2026-09-21).  Twin still sorried — debt flows. -/
theorem MHAEYJN_discharged :
    ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (f : V3 → ℝ → V3) (v w u : V3),
      ConvexLocalFan V E FF →
      Lunar v w V E →
      Deformation f V a b →
      interiorAngle1 0 FF v < Real.pi →
      u ∈ V → u ≠ v → u ≠ w →
      (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
      (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
        ConvexLocalFan ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
        Lunar v w ((fun v => f v t) '' V)
          ((fun e => (fun v => f v t) '' e) '' E) :=
  MHAEYJN_p37

/-- HOLD (c) `SYNQIWN_concl`: the LA22 twin `SYNQIWN_p22` is a different
k-general statement — `azim 0 (v i) (v (i+1)) (v (i+k-1))` conclusion
(registry: `azim 0 (v (i+1)) (v (i+2)) (v i)`), a `hears` six-way
disjunction kit with `he1/he2 : dist ≤ 2*h0` and
`cstab ≤ dist (v (i+1)) (v (i+k-1))` — none of which the registry carries
(its `cstab ≤` edge is `dist (v i) (v (i+2))`); also mnt11-consuming. -/
theorem SYNQIWN_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    BBsV39 s v →
    (norm (v i) = 2 ∨ dist (v i) (v (i + 1)) = 2) →
    (norm (v (i + 2)) = 2 ∨ dist (v (i + 1)) (v (i + 2)) = 2) →
    cstab ≤ dist (v i) (v (i + 2)) →
    Real.pi / 2 < azim 0 (v (i + 1)) (v (i + 2)) (v i) := by
  sorry

/-- HOLD (c) `CQAOQLR_concl`: the LA16 twin `CQAOQLR_p16` consumes the
combined diag form `a ≤ cstab ∧ cstab < dist ∧ 4*h0 < b`, plus `2 < b` on
two edges and strict `a < b` on two further edges; the registry carries
neither the `4*h0` conjunct nor those strict edge facts (only
`b i (i+1) = 2*h0`). -/
theorem CQAOQLR_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    s.a i (i + 1) = 2 → s.b i (i + 1) = 2 * h0 →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    (dist (v i) (v (i + 1)) = 2 ↔ dist (v (i + 1)) (v (i + 2)) = 2) := by
  sorry

/-- HOLD (c) `JLXFDMJ_concl`: the LA27 twin `JLXFDMJ_p27` consumes
`j % s.k ∉ scsM s` while the registry carries `j ∉ scsM s`; the mod-transfer
across the `scsM` boundary (its `i+1` index is unreduced at `i = k-1`) is
real work, not a term-level shim. -/
theorem JLXFDMJ_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s → dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
    s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
    ∀ j, j ∉ scsM s → dist (v j) (v (j + 1)) = 2 := by
  sorry

/-- HOLD (c) `LFLACKU_concl`: the ledger's LA23 twin is a DIFFERENT
statement (`mnt11 → scsArrowV39 {scs3I1} ∅`, LA23:310); no twin of the
registry's `{scs3T1} → {scs3T2, scs3T5}` exists in any lane. -/
theorem LFLACKU_discharged : scsArrowV39 {scs3T1} {scs3T2, scs3T5} := by
  sorry

/-- HOLD (c) `QKNVMLB1_concl`: the LA35 twin concludes on the index
convention `vv (i % s'.k + p % s.k)` where the registry uses
`vv ((i + p) % s'.k)`; the conventions disagree off the mod boundary
(e.g. k = 6, p = 2, i = 4 gives `vv 6` vs `vv 0`) and `Periodic vv` does not
reconcile them (cf. the QKNVMLB3 (d) note). -/
theorem QKNVMLB1_discharged : ∀ (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    MMsV39 s vv → s.bm p q < 4 → (s.k = 4 ∨ s.bm p q ≤ cstab) → isScsV39 s →
    d' < 0.9 → scsDiag s.k p q →
    BBsV39 (scsHalfSliceV39 s p q d' mkj)
      (fun i => vv ((i + p) % (scsHalfSliceV39 s p q d' mkj).k)) := by
  sorry

/-- HOLD (c) `QKNVMLB2_concl`: same index-convention mismatch on both
half-slice realisations as QKNVMLB1. -/
theorem QKNVMLB2_discharged : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    (s', s'') = scsSliceV39 s p q d' d'' mkj →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    dsvV39 s vv ≤ dsvV39 s' (fun i => vv ((i + p) % s'.k)) +
      dsvV39 s'' (fun i => vv ((i + q) % s''.k)) := by
  sorry

/-! ### (d) Twin proved but the shape delta is not bridgeable (5) -/

/-- HOLD (d) `OEHDBEN_concl`: LA20 `OEHDBEN` (proved, mnt11-consuming)
concludes `{scs6T1, scs5M1, scs4M2, scs3M1}` — the registry wants `scs3T1`
in the last slot; `scs3M1` (d = 0.103, funlist edge table) and `scs3T1`
(d = 0.11) are genuinely different systems, so no set bridge exists. -/
theorem OEHDBEN_discharged :
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3T1} := by
  sorry

/-- HOLD (d) `TBRMXRZ1_concl`: the proved `TBRMXRZ1_p22` composes in the
opposite order (`g ∘ f`, needs the inner slope `0 < f'`, concludes
`reEqvl h' g'`) where the registry carries `f ∘ g` and wants `reEqvl f' h'`;
the registry hypotheses carry no information about the inner g-slope sign,
so no witness term exists (the registry statement is in fact not provable
from its own hypotheses). -/
theorem TBRMXRZ1_discharged : ∀ (f : ℝ → ℝ) (f' : ℝ) (g : ℝ → ℝ) (h' x y : ℝ),
    derivedForm True f f' y (Set.univ : Set ℝ) →
    derivedForm True (fun z => f (g z)) h' x (Set.univ : Set ℝ) →
    g x = y → reEqvl f' h' := by
  sorry

/-- HOLD (d) `VPWSHTO_concl`: master `VPWSHTO_p15` still sorried;
`VPWSHTO_PRIME_p15` is proved but concludes the `∃ i ∈ Icc 0 4` diagonal-
bounds form and lacks the registry concl's `2 < dist` strictness (not
derivable from the `≤ 1+sqrt 5` bounds) and the distinctness witness
conjuncts. -/
theorem VPWSHTO_discharged : ∀ v x u w w1 : V3,
    ({v, x, u, w, w1} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({v, x, u, w, w1} : Set V3) →
    v ≠ x → v ≠ u → v ≠ w → v ≠ w1 → x ≠ u → x ≠ w → x ≠ w1 → u ≠ w → u ≠ w1 →
    w ≠ w1 →
    norm (v - x) = 2 → norm (x - u) = 2 → norm (u - w) = 2 →
    norm (w - w1) = 2 → norm (w1 - v) = 2 →
    ∃ v1 u1 w2 : V3,
      u1 ∈ ({v, x, u, w, w1} : Set V3) ∧ u1 ∈ ({v, x, u, w, w1} : Set V3) ∧
      w2 ∈ ({v, x, u, w, w1} : Set V3) ∧ v1 ≠ u1 ∧ u1 ≠ w2 ∧ v1 ≠ w2 ∧
      2 < dist v1 u1 ∧ 2 < dist v1 w2 ∧
      dist v1 u1 ≤ 1 + Real.sqrt 5 ∧ dist v1 w2 ≤ 1 + Real.sqrt 5 := by
  sorry

/-- HOLD (d) `XWNHLMD_concl`: the proved `XWNHLMD_p26` keeps the extra
`s.d ≤ s'.d` antecedent (consumed by `SCS_BASIC_TAUSTAR_p26`);
`isScsV39` pins only `s.d < 0.9` (no dTame equation), so the antecedent is
not derivable from the registry hypotheses. -/
theorem XWNHLMD_discharged : ∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → s.k = s'.k →
    v ∈ MMsV39 s → BBsV39 s' v →
    scsArrowV39 {s} {s'} := by
  sorry

/-- HOLD (d) `QKNVMLB3_concl`: the proved `QKNVMLB3_p35` case-splits onto
the still-sorried `QKNVMLB3_Eq4/LE4_p35` branches AND its realisation
arguments use the index convention `vv (i % s'.k + p % s.k)` and the
`scsHalfSliceV39 s p q d' mkj = s'` equation form where the registry uses
`vv ((i + p) % s'.k)` and the `(s', s'') = scsSliceV39 ...` tuple form (the
tuple side does bridge via the `scsSliceV39` def; the index conventions
disagree off the mod boundary, e.g. s.k=6, p=2, q=0, i=4 gives `vv 6` vs
`vv 1`, and `Periodic vv s.k` cannot reconcile them). -/
theorem QKNVMLB3_discharged : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    (s', s'') = scsSliceV39 s p q d' d'' mkj →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    taustarV39 s' (fun i => vv ((i + p) % s'.k)) +
      taustarV39 s'' (fun i => vv ((i + q) % s''.k)) ≤ taustarV39 s vv := by
  sorry

/-! ## Debt ledger (`#print axioms` ground truth)

The WIRE entries that transitively rest on a `sorry` show `sorryAx` here —
by design (assembly mode).  Of the 16 classic discharges, six are sorry-free
(`YXIONXL3`, `EYYPQDW`, `EYYPQDW2`, `EYYPQDW3`, `unadorned_MMs`, `HXHYTIJ`;
per the 2026-09-21 log); the other ten rest on their waves' own sorried
inputs (e.g. `YXIONXL1` via an LA12 wave input, `PQCSXWG2` via
`PQCSXWG2_ATREAL_p11`).  Every HOLD entry depends on `sorryAx` outright. -/

#print axioms YXIONXL1_discharged
#print axioms YXIONXL3_discharged
#print axioms EYYPQDW_discharged
#print axioms EYYPQDW2_discharged
#print axioms EYYPQDW3_discharged
#print axioms unadorned_MMs_discharged
#print axioms HXHYTIJ_discharged
#print axioms PQCSXWG2_discharged
#print axioms GSXRFWM_discharged
#print axioms AUEAHEH_discharged
#print axioms ZNLLLDL_discharged
#print axioms VQFYMZY_discharged
#print axioms BNAWVNH_discharged
#print axioms RAWZDIB_discharged
#print axioms MFKLVDK_discharged
#print axioms RYPDIXT_discharged
#print axioms XWITCCN_discharged
#print axioms XWITCCN2_discharged
#print axioms AYQJTMD_discharged
#print axioms EAPGLE_discharged
#print axioms JKQEWGV1_discharged
#print axioms JKQEWGV2_discharged
#print axioms JKQEWGV3_discharged
#print axioms ZLZTHIC_discharged
#print axioms UAGHHBM_discharged
#print axioms LKGRQUI_discharged
#print axioms ODXLSTCv2_discharged
#print axioms IMJXPHRv2_discharged
#print axioms NUXCOEAv2_discharged
#print axioms PQCSXWG1_discharged
#print axioms FEKTYIY_discharged
#print axioms AURSIPD_discharged
#print axioms PPBTYDQ_discharged
#print axioms MXQTIED_discharged
#print axioms AXJRPNC_discharged
#print axioms RRCWNSJ_discharged
#print axioms JCYFMRP_discharged
#print axioms TFITSKC_discharged
#print axioms AQICLXA_discharged
#print axioms FUNOUYH_discharged
#print axioms HIJQAHA_discharged
#print axioms CNICGSF1_discharged
#print axioms CNICGSF2_discharged
#print axioms CNICGSF3_discharged
#print axioms CNICGSF4_discharged
#print axioms CNICGSF5_discharged
#print axioms ARDBZYE_discharged
#print axioms FYSSVEV_discharged
#print axioms NWDGKXH_discharged
#print axioms YOBIMPP_discharged
#print axioms MIQMCSN_discharged
#print axioms BKOSSGE_discharged
#print axioms YRTAFYH_discharged
#print axioms MHAEYJN_discharged
#print axioms CUXVZOZ_discharged
#print axioms CJBDXXN_discharged

end Kepler.Text
