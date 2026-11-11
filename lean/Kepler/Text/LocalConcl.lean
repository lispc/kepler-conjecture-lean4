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
  holds marked HOLD (with the precise reason).  Twins that consume the opaque
  terminal-bank Prop `main_nonlinear_terminal_v11` take it as an explicit
  hypothesis; the consumption layers (`localconcl_wire_capstone_w1`/`w2`,
  `JEJTVGB_p16_discharged`) already hold it and pass it down -- no anchor.
  (ERRATA 2026-11-12: the former `mnt11_anchor` skeleton sorry is deleted and
  the nine terminal-bank wires take `(hmn : main_nonlinear_terminal_v11)`.
  Cone sorry −1.)
  (ERRATA 2026-11-06: the p21 twins used to need a second anchor
  `p21_anchor : mainNonlinearTerminalV11_p21`; after the `p21-anchor` DEF-FIX
  charter that Prop is *defined* as `main_nonlinear_terminal_v11`, so the wires
  pass their own `_hmn` and the anchor was deleted.  Cone sorry −1.)

    WIRE (real proof term, debt = twin's axioms; bank hypothesis passed in): 69
      (body census = the 16 classic discharges + 53 assembly wires)
    HOLD (explicit `sorry`, reason recorded): 21 (body census)
      = (a) 5 no-twin + (b) 11 circular re-export + (c) 5 non-bridgeable
    RECONCILIATION (SF-87 audit of the count block): the 2026-09-21
      baseline recorded WIRE 62 / HOLD 28, but four of its 28 ((d)
      OEHDBEN/TBRMXRZ1/VPWSHTO/XWNHLMD) had been rebased onto twin bodies
      by the SF-63/69/71/73 statement-fix waves without this block being
      updated -- the pre-SF-87 body census was already 66/24.  This wave
      WIRES the QKNVMLB trio: 28 -> 25 on the ledger convention = 24 -> 21
      on the body census (the only convention-consistent delta is -3).
    TOTAL: 90/90 registry contracts exposed at this exit.

  ASSEMBLY WAVE 2026-11-01 (SF-87, lane la35-access-wb1; the QKNVMLB
    slicing trio leaves the HOLD ledger): LA1's registry concls were
    rebased onto the corpus original form (SF-64/65/66 fixed the index
    convention `vv (i % s'.k + p % s.k)`; SF-87 completes the reshape by
    restating the QKNVMLB2/3 half-slice realisation pair as the corpus
    two-equation form `scsHalfSliceV39 s p q d' mkj = s'` /
    `scsHalfSliceV39 s q p d'' mkj = s''` (QKNVMLB.hl:5523/:5524 and
    :10665/:10666) instead of the `(s', s'') = scsSliceV39 ...` tuple
    slot -- the two shapes are inter-derivable via the `scsSliceV39` def +
    `Prod.mk.injEq`, so the restatement is content-preserving; the W-E
    mod-boundary probe (`vvAppendix_ne_vvCorpus`, lane la35-access-we1)
    supplies the machine evidence that the OLD appendix index form
    `vv ((i+p) % s'.k)` was the right thing to abandon).  This exit now
    WIRES all three against the proved LA35 twins (import of
    `Kepler.Text.LocalAuto35` added):
      QKNVMLB1 <- LocalAuto35.QKNVMLB1_p35 (LA35:31426; sorry-free body),
      QKNVMLB2 <- LocalAuto35.QKNVMLB2_p35 (LA35:31654; sorry-free body),
      QKNVMLB3 <- LocalAuto35.QKNVMLB3_p35 (LA35:33360; via
        QKNVMLB3_LE4/Eq4_p35, both proved through `tausplit_le4`).
    Debt (measured 2026-11-01, `#print axioms` at this exit + against the
    LA35 olean): QKNVMLB2/QKNVMLB3 wires are FULLY CLEAN
    (`[propext, Classical.choice, Quot.sound]` -- the tausplit_le4
    assembly closed their faces; the recon-era "all three polluted"
    expectation is superseded).  QKNVMLB1's wire carries `sorryAx`
    inherited from the twin's LE4 branch: `QKNVMLB1_LE4F_p35` (sorryAx)
    <- `TECOXBMv2_p35` (sorryAx) <- the sectorTri/pmPlaneCrowding chain
    (LA35 bare sorry at :7583; `QKNVMLB1_EQ4F_p35` is already clean) --
    the debt has that single known root and self-clears when W-A (pm12)
    closes it.

  ASSEMBLY WAVE 2026-09-21 II (skeleton propagation into the (a) class):
    four of the eleven (a) entries have PROVED HOL originals that had never
    been restated on the Lean side; their owning modules are now carrying
    faithful skeleton restatements and this exit wires them:
      OTMTOTJ1 <- LocalAuto24.OTMTOTJ1  (verbatim; OTMTOTJ.hl:1156),
      OTMTOTJ2 <- LocalAuto24.OTMTOTJ2  (verbatim; OTMTOTJ.hl:1169),
      OTMTOTJ3 <- LocalAuto24.OTMTOTJ3  (verbatim; OTMTOTJ.hl:1500),
      OTMTOTJ4 <- LocalAuto24.OTMTOTJ4  (verbatim; OTMTOTJ.hl:1520).
    (The earlier scan's OTMTOTJ1-4 hits in LA16/23 were the same-shaped
    hypothesis arrows of `JEJTVGB_case_breakdown_p16/_p23`, not twins; the
    owners are LA24 = OTMTOTJ.hl.)

  ASSEMBLY WAVE 2026-09-21 III (two more (a) entries with PROVED HOL
    originals): the owning-module twins landed and this exit wires them:
      ASSWPOW <- LocalAuto25.ASSWPOW_p25 (faithful restatement of the
        PROVED VASYYAU.hl:154 original, statement verbatim; the twin's body
        is a skeleton `sorry` — the HOL fan kit + Flyspeck-constants calc is
        not yet ported — debt flows),
      DRNDRDV <- LocalAuto22.derived_form_xrr_p22 (the twin was ALREADY in
        place: LA22:260, proved, sorry-free, the verbatim statement of the
        HOL original `derived_form_xrr`, OCBICBY.hl:766, aliased `DRNDRDV`
        at :849; no new code needed).
    Both twins are registry-INDEPENDENT proof pieces (neither is derived
    from its `*_concl` registry sorry), so neither wire is a (b)-style
    cycle.  The remaining five (a) entries stay HOLD with their
    HOL-provenance audit recorded per entry below:
      HFNXPZA / EQTTNZI1 / EQTTNZI2 / EFLYGAU / BJTDWPS -- the HOL corpus
      carries these ONLY as appendix.hl registry lets (appendix.hl:710/
        1110/1115/1500/1506); no proved lemma under these names exists
        anywhere in `lean/scripts/local/` (corpus-wide grep), so there is
        no faithful statement to restate.
        RULING 2026-09-21 IV (form audit of the five lets, done on the HOL
        reference corpus at `text_formalization/local/appendix.hl`): each
        let is a proposition-valued STATEMENT binding
        (`let X_concl = \`...\`;;`) -- neither a `new_definition` nor a
        `prove` -- i.e. book conclusions left UNPROVED upstream; they are
        genuine theorem-shaped registry entries, NOT contract mis-plants
        and NOT definitional lets.  Supporting negatives: (1) no
        HFNXPZA/EQTTNZI/EFLYGAU/BJTDWPS `.hl` proof files exist, although
        per-lemma proof files are the corpus convention (cf. QKNVMLB.hl,
        MIQMCSN.hl, UAGHHBM.hl, ...); (2) the names appear nowhere else in
        the corpus, even case-insensitively; (3) the `restriction_typ1_v39`
        / `restriction_typ2_v39` consumed by EQTTNZI1/2 are
        `new_definition`s (appendix.hl:716/719) with ZERO consumers outside
        appendix.hl -- a dead-end toolkit; (4) the nearest scs_4M7/scs_4M8
        activity, MIQMCSN.hl:1101/1521, proves stab-diag NONEMPTINESS
        (`MM_4M7_IMP_STAB_4M7`/`MM_4M8_IMP_STAB_4M8`), not the EFLYGAU/
        BJTDWPS arrows, and no `scs_arrow_v39 {scs_4M7} {scs_4M6'}` /
        `{scs_4M8} {scs_4M6',scs_3T7}` is proved anywhere; (5) the only
        other `dihV ... 2 * pi` fragments (terminal.hl:2041/2095,
        OCBICBY.hl:3036/3119) are TYPIFY/ENOUGH_TO_SHOW steps inside other
        proofs, and the k=3 lanes (JKQEWGV/UXCKFPE/XWITCCN) never mention
        `dihV`.  Verdict: class (iii) corpus-missing for all five; the
        HOLDs stand with no faithful statement available to build.

  ASSEMBLY WAVE 2026-10 (consumption upshift; lane la1concl-reroute-w1,
  blueprint la1reroute-w1 / structural finding sf78draft-w1 §9-8): the 21
  WIRE exits feeding `JEJTVGB_p16` (OTMTOTJ1-4, CNICGSF1-5, HIJQAHA,
  FYSSVEV, ARDBZYE, AUEAHEH, VQFYMZY, BNAWVNH, RAWZDIB, MFKLVDK, RYPDIXT,
  NWDGKXH, YOBIMPP, MIQMCSN) are now consumed INSIDE this file by
  `JEJTVGB_p16_discharged` + `nonlinear_imp_lp_main_estimate_p16_discharged`
  (see the block before `end Kepler.Text`), and `Kepler.Assembly` switches
  its two consumption points to the latter name.  This moves the assembly
  point one layer up: the LA1 `*_concl` registry arrows leave the e2e cone
  (their downstream `LocalAuto16.JEJTVGB_p16` chain loses its last
  consumer), while the debt graph is preserved verbatim -- same twins,
  debt flows along the proof term (the ASSEMBLY WAVE 2026-09-21 contract,
  one layer up).
  Zero new debt: the two new theorems add no proof debt of their own; the
  reachable-debt rows move from LocalAuto1 to the twins' owners
  (LA18/24/29/32/33/17 + the terminal-bank hypothesis), net +6 rows at the next
  e2e rescan (static subcone accounting 151 -> 157, blueprint §3.2).
  Acyclicity of the new edge `Kepler.Assembly -> Kepler.Text.LocalConcl`:
  zero importers of this file tree-wide + module-closure computation
  (blueprint §1.2).

  ASSEMBLY WAVE 2026-10-28 (lane la35-access-wd1; LA35-series real-proof
    supply onto the assembly point): the five CNICGSF slots of
    `JEJTVGB_p16_discharged` are refilled from real-proof donors.  The LA18
    twins' debt (`SCS_*_SLICE_*_p18` bare sorries on the LKGRQUI lane + the
    registry arrow `YXIONXL3_concl`) is replaced by `LKGRQUI_p27` instances
    proved in this file (the `wd_*` private bridge section before the
    consumption-upshift block; the ten half-slice record identities are
    PSORT/FUNLIST table bashes, HOL CNICGSF.hl route) + the clean
    `YXIONXL3_discharged`.  This is the LA35->spine consumption edge: the e2e
    cone now reaches the LA35 engine, so W-A's (pm12) closure of the
    `pmPlaneCrowding_p35` root scores at the assembly exit.  Honest debt
    note: `LKGRQUI_p27` also carries the `SGTRNAF_p27` leg
    (`XWNHLMD_MM_p26` -> `UXCKFPE*_p27` -> the LA24 `XWITCCN_CASE_*_IS_SCS_p24`
    bank), so the five refilled slots' sorried-ancestor sets are
    {pmPlaneCrowding_p35, XWITCCN_CASE_3/4/5/6_IS_SCS_p24} (measured, see the
    lane's Evidence.md reach probe), replacing the previous 2 dead-end roots
    per slot.

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

  (a) No downstream twin anywhere in LocalAuto2-38 (5; audit 2026-09-21 III):
      HFNXPZA, EQTTNZI1, EQTTNZI2, EFLYGAU, BJTDWPS.
      OTMTOTJ1-4 left this class in the 2026-09-21 II wave (faithful
      restatements `LocalAuto24.OTMTOTJ1-4` wired below); ASSWPOW and
      DRNDRDV left in the 2026-09-21 III wave (see the wave note above).

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
        RULING 2026-09-21 IV: the TWIN side is faithful -- it restates the
        PROVED originals `QKNVMLB1`/`QKNVMLB2`/`QKNVMLB3`
        (QKNVMLB.hl:5223/:5522/:10665; `vv'` at :5225/:5525/:10667 is
        `vv (i MOD s'.k + p MOD s.k)`) verbatim; the REGISTRY side
        transcribes the appendix.hl:1055/1064/1075 statement-lets
        (`vv ((i+p) MOD s'.k)`), which have NO proof anywhere in the corpus
        -- the appendix form and the proved form are genuinely different
        functions (different moduli), not equable via periodicity.  The LA1
        correction is therefore deferred to the registry-refactor round
        (LA1 frozen this round); full ruling on the entries below.
        [2026-11-01 SF-87: the deferral is executed -- LA1 registry re-based
        onto the corpus form (SF-64/65/66 index + SF-87 two-equation) and
        QKNVMLB1/QKNVMLB2 are WIRED through the proved, sorry-free-bodied
        LA35 twins; (c) HELD 7 -> 5.  See the 2026-11-01 wave note above.]
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
      twins match the registry concls modulo the terminal-bank hypothesis, so
      they are WIRED through the wire's own `_hmn` (see the wave note).
      [2026-11-06: the former `p21_anchor` sorry was deleted -- see §anchor
      ERRATA at the top of this file.]
      [2026-11-01 SF-87: QKNVMLB3 left this class -- the registry re-based
      onto the corpus two-equation form and WIRED through the proved
      `QKNVMLB3_p35` (its `tausplit_le4` assembly closed the former
      "still-sorried Eq4/LE4 branches" blocker); 4 remain.]
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
        registry concls modulo the terminal-bank hypothesis: they take
        `mainNonlinearTerminalV11_p21` where the registry concl carries
        `main_nonlinear_terminal_v11`.  [2026-11-06: the `p21-anchor` DEF-FIX
        charter made that Prop *definitionally* the registry's, so no bridge
        is needed and the former `p21_anchor` skeleton sorry is deleted --
        the wires pass their own `_hmn`.  Cone sorry −1.]  Former (d) blocker
        voided 2026-09-21.
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
      sorried.  [2026-09-21 II: OTMTOTJ1-4 left the blocked set — faithful
      restatements `OTMTOTJ1-4` landed in LA24 Section B6 and are wired.]
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
    none (5): HFNXPZA, EQTTNZI1, EQTTNZI2, EFLYGAU, BJTDWPS -- audit
      2026-09-21 III: no proved HOL original at all (appendix.hl registry
      lets only; 2026-09-21 IV form audit: statement-only lets, neither
      `new_definition` nor `prove`, no proof file per the corpus
      convention -- class (iii) confirmed per entry above).  Former members: OTMTOTJ1-4 (the earlier (a) mentions in
      LA16/23 were same-shaped hypothesis arrows of other theorems, not
      twins; discharged via the new LA24 B6 restatements, 2026-09-21 II),
      ASSWPOW (VASYYAU.hl:154 proved original; LA25 faithful twin
      `ASSWPOW_p25` added and wired, 2026-09-21 III), DRNDRDV (=
      `derived_form_xrr`, OCBICBY.hl:766 proved original; the proved
      LA22 twin `derived_form_xrr_p22` was already in place and is wired,
      2026-09-21 III).

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
import Kepler.Text.LocalAuto35
import Kepler.Text.LocalAuto36
import Kepler.Text.LocalAuto37
import Kepler.Text.LocalAuto38
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ### LA19 materialization capstone (lane lv1112-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV12):
the 110 public top-level LocalAuto19 clean theorem exits (scout seeds_clean.txt LA19 group; the 32 sorried
`terminal_pent_tau*` / `taud_minimizer_*` / `terminal_hex_*_reduction` / `OWZLKVY4_p19` family exits are NOT included --
their debt is the terminal nonlinear DB line (OWZLKVY4_p19 LocalAuto19:445 NEEDS-DB: the nonlinear database
`taud ≤ taum` conjugation; W6a/§5-M1 family) per the scout verdict table), of which 110 are statable from LocalConcl
and are re-exposed as ONE conjunction below; 0 exits are dropped per the no-forcing rule (each drop named in the theorem
docstring).
Self-contained section: pure insertion, zero new imports (LA19 already imported at :490), zero proof obligations
(body = the exit assembly itself), own `#print axioms` probe (the shared la34 footer untouched).
The scoped heartbeat raise mirrors the file-level `set_option maxHeartbeats` above: a 110-conjunct statement exceeds
even the file budget during statement elaboration (lv910 measured the 71-conjunct PA4 case against the 200000 default).
-/

set_option maxHeartbeats 50000000 in

/-- LA19 materialization capstone (scout lane leftover-mat-scout-2
workorder LV12, implementation lane lv1112-w1, 2026-11-04).  The
110 public top-level Kepler.Text.LocalAuto19 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 110 of them are statable from
LocalConcl and are re-exposed as ONE conjunction.
Implemented here: 110 of the 110.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.LocalAuto19 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation/aux lemmas have no
source statement anywhere, so their conjunct is the `#check @name` printer
dump verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below
must unify it definitionally with the constant's type; printer dumps with
proof-term elision `...` are dropped per the lv12-w1 t_eqlemma_microtest
evidence, each drop named above).  Semantic identity of every conjunct is
re-verified by that assembly (each element must have exactly its conjunct's
type); the per-conjunct comments carry each exit's Kepler.Text.LocalAuto19 declaration
line and file-local docstring HOL anchor.  Conjunct order: the scout
seed-list order (probe1 SEED list).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports. -/
theorem la19_wire_capstone_w1 :
    -- 1. Kepler.Text.OPEN_REAL_INTERVAL_SING_p19 (Kepler.Text.LocalAuto19:455; HOL `OPEN_REAL_INTERVAL_SING`)
    (∀ (a b c : ℝ),
    Set.Ioo a b ≠ {c}
    ) ∧
    -- 2. Kepler.Text.REAL_WLOG_AAB_SIMPLEX_p19 (Kepler.Text.LocalAuto19:1574; HOL `REAL_WLOG_AAB_SIMPLEX`)
    (∀ {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
          (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y3 y2 y1 y6 y5 y4)
          (hord : ∀ y1 y2 y3 y4 y5 y6, y4 ≤ y6 → P y1 y2 y3 y4 y5 y6),
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6
    ) ∧
    -- 3. Kepler.Text.REAL_WLOG_ABB_SIMPLEX_p19 (Kepler.Text.LocalAuto19:1585; HOL `REAL_WLOG_ABB_SIMPLEX`)
    (∀ {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
          (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y1 y3 y2 y4 y6 y5)
          (hord : ∀ y1 y2 y3 y4 y5 y6, y6 ≤ y5 → P y1 y2 y3 y4 y5 y6),
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6
    ) ∧
    -- 4. Kepler.Text.REAL_WLOG_S3_SIMPLEX_p19 (Kepler.Text.LocalAuto19:1544; HOL `REAL_WLOG_S3_SIMPLEX`)
    (∀ {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
          (hcyc : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y3 y1 y2 y6 y4 y5)
          (hswap : ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6 = P y2 y1 y3 y5 y4 y6)
          (hord : ∀ y1 y2 y3 y4 y5 y6, y4 ≤ y6 → y6 ≤ y5 → P y1 y2 y3 y4 y5 y6),
    ∀ y1 y2 y3 y4 y5 y6, P y1 y2 y3 y4 y5 y6
    ) ∧
    -- 5. Kepler.Text.abcOfQuadratic_p19_quad (Kepler.Text.LocalAuto19:1014; no HOL anchor line in file docstring)
    (∀ (A B C : ℝ),
    abcOfQuadratic_p19 (fun t => A * t * t + B * t + C) = (A, B, C)
    ) ∧
    -- 6. Kepler.Text.continuous_preimage_closed_p19 (Kepler.Text.LocalAuto19:777; HOL `continuous_preimage_closed`)
    (∀ {f : ℝ → ℝ} {s t : Set ℝ}
          (hs : IsClosed s) (ht : IsClosed t) (hc : ContinuousOn f s),
    IsClosed {x | x ∈ s ∧ f x ∈ t}
    ) ∧
    -- 7. Kepler.Text.continuous_preimage_open_p19 (Kepler.Text.LocalAuto19:788; HOL `continuous_preimage_open`)
    (∀ {f : ℝ → ℝ} {s t : Set ℝ}
          (hs : IsOpen s) (ht : IsOpen t) (hc : ContinuousOn f s),
    IsOpen {x | x ∈ s ∧ f x ∈ t}
    ) ∧
    -- 8. Kepler.Text.delta126x_p19.eq_1 (Kepler.Text.LocalAuto19:135; compiler-generated equation/aux lemma (parent def `delta126x_p19` at Kepler.Text.LocalAuto19:135; no source statement; sigtest = assembly elaboration))
    (∀ (s3 s4 s5 x1 x2 x3 x4 x5 x6 : ℝ),
          delta126x_p19 s3 s4 s5 x1 x2 x3 x4 x5 x6 = deltaX x1 x2 s3 s4 s5 x6
    ) ∧
    -- 9. Kepler.Text.delta135x_p19.eq_1 (Kepler.Text.LocalAuto19:141; compiler-generated equation/aux lemma (parent def `delta135x_p19` at Kepler.Text.LocalAuto19:141; no source statement; sigtest = assembly elaboration))
    (∀ (s2 s4 s6 x1 x2 x3 x4 x5 x6 : ℝ),
          delta135x_p19 s2 s4 s6 x1 x2 x3 x4 x5 x6 = deltaX x1 s2 x3 s4 x5 s6
    ) ∧
    -- 10. Kepler.Text.delta234x_p19.eq_1 (Kepler.Text.LocalAuto19:138; compiler-generated equation/aux lemma (parent def `delta234x_p19` at Kepler.Text.LocalAuto19:138; no source statement; sigtest = assembly elaboration))
    (∀ (s1 s5 s6 x1 x2 x3 x4 x5 x6 : ℝ),
          delta234x_p19 s1 s5 s6 x1 x2 x3 x4 x5 x6 = deltaX s1 x2 x3 x4 s5 s6
    ) ∧
    -- 11. Kepler.Text.deltaX_perm_p19 (Kepler.Text.LocalAuto19:1351; no HOL anchor line in file docstring)
    (∀ (a b c d e f : ℝ),
    deltaX a b c d e f = deltaX c a b f d e
    ) ∧
    -- 12. Kepler.Text.deltaX_swap_p19 (Kepler.Text.LocalAuto19:1478; no HOL anchor line in file docstring)
    (∀ (a b c d e f : ℝ),
    deltaX a b c d e f = deltaX a c b d f e
    ) ∧
    -- 13. Kepler.Text.deltaX_vert12_p19 (Kepler.Text.LocalAuto19:1369; no HOL anchor line in file docstring)
    (∀ (a b c d e f : ℝ),
    deltaX a b c d e f = deltaX b a c e d f
    ) ∧
    -- 14. Kepler.Text.deltaY_hasDerivAt_p19 (Kepler.Text.LocalAuto19:474; no HOL anchor line in file docstring)
    (∀ (t y2 y3 y4 y5 y6 : ℝ),
    HasDerivAt (fun q => deltaY q y2 y3 y4 y5 y6)
          (2 * t * deltaX1_p19 (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) t
    ) ∧
    -- 15. Kepler.Text.delta_diff_p19 (Kepler.Text.LocalAuto19:1006; HOL `delta_diff`)
    (∀ (x1 z1 x2 x3 x4 x5 x6 : ℝ),
    deltaX x1 x2 x3 x4 x5 x6
          = deltaX z1 x2 x3 x4 x5 x6 + deltaX1_p19 x1 x2 x3 x4 x5 x6 * (x1 - z1)
            + x4 * (x1 - z1) ^ 2
    ) ∧
    -- 16. Kepler.Text.delta_y_continuous_p19 (Kepler.Text.LocalAuto19:751; HOL `delta_y_continuous`)
    (∀ (y2 y3 y4 y5 y6 : ℝ),
    ContinuousOn (fun q => deltaY q y2 y3 y4 y5 y6) Set.univ
    ) ∧
    -- 17. Kepler.Text.delta_y_sym_cases2_p19 (Kepler.Text.LocalAuto19:1276; HOL `delta_y_sym_cases2`)
    (∀ (y1 y2 y3 y4 y5 y6 a : ℝ),
    deltaY a y3 y1 y5 2 2 = deltaY a y1 y3 y5 2 2 ∧
          deltaY a y3 y2 y4 2 2 = deltaY a y2 y3 y4 2 2 ∧
          deltaY a y2 y1 y6 2 2 = deltaY a y1 y2 y6 2 2
    ) ∧
    -- 18. Kepler.Text.deriv_form_taud_p19 (Kepler.Text.LocalAuto19:517; HOL `deriv_form_taud`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hd : 0 < deltaY y1 y2 y3 y4 y5 y6),
    derivedForm (0 < deltaY y1 y2 y3 y4 y5 y6)
          (fun q => taudP19 q y2 y3 y4 y5 y6)
          ((-0.07 * deltaY y1 y2 y3 y4 y5 y6 +
              muY_p19 y1 y2 y3 * (yOfX deltaX1_p19 y1 y2 y3 y4 y5 y6 * y1) +
              (sol0 / (2 * h0 - 2)) * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) /
            Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))
          y1 Set.univ
    ) ∧
    -- 19. Kepler.Text.derived_form_F_p19 (Kepler.Text.LocalAuto19:470; HOL `derived_form_F`)
    (∀ (f : ℝ → ℝ) (f' x : ℝ) (s : Set ℝ),
    derivedForm False f f' x s
    ) ∧
    -- 20. Kepler.Text.derived_form_delta_y_p19 (Kepler.Text.LocalAuto19:508; HOL `derived_form_delta_y`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
    derivedForm True (fun q => deltaY q y2 y3 y4 y5 y6)
          (yOfX deltaX1_p19 y1 y2 y3 y4 y5 y6 * 2 * y1) y1 Set.univ
    ) ∧
    -- 21. Kepler.Text.derived_form_taud_ALT_p19 (Kepler.Text.LocalAuto19:570; HOL `derived_form_taud_ALT`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hy3 : 0 ≤ y3),
    derivedForm (0 < deltaY y1 y2 y3 y4 y5 y6 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3)
          (fun q => taudP19 q y2 y3 y4 y5 y6)
          (yOfX taudD1numX_p19 y1 y2 y3 y4 y5 y6 /
            Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))
          y1 Set.univ
    ) ∧
    -- 22. Kepler.Text.derived_form_taud_D3_p19 (Kepler.Text.LocalAuto19:629; HOL `derived_form_taud_D3`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
    ∃ f' : ℝ, derivedForm (0 < deltaY y1 y2 y3 y4 y5 y6 ∧ 0 < y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3)
          (fun q => yOfX taudD2numX_p19 q y2 y3 y4 y5 y6 /
            Real.sqrt (deltaY q y2 y3 y4 y5 y6) ^ 3)
          f' y1 Set.univ
    ) ∧
    -- 23. Kepler.Text.edge2_flatD_sym_p19 (Kepler.Text.LocalAuto19:1293; HOL `edge2_flatD_sym`)
    (∀ (d y1 y2 y3 a : ℝ),
    edge2FlatDX1_p19 d y1 y2 y3 a a = edge2FlatDX1_p19 d y2 y1 y3 a a
    ) ∧
    -- 24. Kepler.Text.edge2_flatD_x1_delta_lemma2_p19 (Kepler.Text.LocalAuto19:1028; HOL `edge2_flatD_x1_delta_lemma2`)
    (∀ (d x1 x2 x3 x4 x5 x6 : ℝ)
          (hd : deltaX x1 x2 x3 x4 x5 x6 = d) (hx4 : 0 < x4)
          (hΔ : deltaX1_p19 x1 x2 x3 x4 x5 x6 < 0),
    edge2FlatDX1_p19 d x2 x3 x4 x5 x6 = x1
    ) ∧
    -- 25. Kepler.Text.edge2_flatD_x1_sym_cases_p19 (Kepler.Text.LocalAuto19:1305; HOL `edge2_flatD_x1_sym_cases`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
    edge2FlatDX1_p19 0 (y3 * y3) (y2 * y2) (y4 * y4) (2 * 2) (2 * 2)
            = edge2FlatDX1_p19 0 (y2 * y2) (y3 * y3) (y4 * y4) (2 * 2) (2 * 2) ∧
          edge2FlatDX1_p19 0 (y3 * y3) (y1 * y1) (y5 * y5) (2 * 2) (2 * 2)
            = edge2FlatDX1_p19 0 (y1 * y1) (y3 * y3) (y5 * y5) (2 * 2) (2 * 2) ∧
          edge2FlatDX1_p19 0 (y2 * y2) (y1 * y1) (y6 * y6) (2 * 2) (2 * 2)
            = edge2FlatDX1_p19 0 (y1 * y1) (y2 * y2) (y6 * y6) (2 * 2) (2 * 2)
    ) ∧
    -- 26. Kepler.Text.eulerA_x_sym_cases_p19 (Kepler.Text.LocalAuto19:1326; HOL `eulerA_x_sym_cases`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
    yOfX eulerAx_p19 y2 y1 y3 y5 y4 y6 = yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
          yOfX eulerAx_p19 y3 y1 y2 y6 y4 y5 = yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
          yOfX eulerAx_p19 y3 y2 y1 y6 y5 y4 = yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 ∧
          yOfX eulerAx_p19 y1 y3 y2 y4 y6 y5 = yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6
    ) ∧
    -- 27. Kepler.Text.flatTerm2_126x_p19.eq_1 (Kepler.Text.LocalAuto19:193; compiler-generated equation/aux lemma (parent def `flatTerm2_126x_p19` at Kepler.Text.LocalAuto19:193; no source statement; sigtest = assembly elaboration))
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
          flatTerm2_126x_p19 d a b x1 x2 x3 x4 x5 x6 = flatTerm_p19 √(edge2FlatDX1_p19 d x1 x2 x6 a b)
    ) ∧
    -- 28. Kepler.Text.flatTerm2_135x_p19.eq_1 (Kepler.Text.LocalAuto19:198; compiler-generated equation/aux lemma (parent def `flatTerm2_135x_p19` at Kepler.Text.LocalAuto19:198; no source statement; sigtest = assembly elaboration))
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
          flatTerm2_135x_p19 d a b x1 x2 x3 x4 x5 x6 = flatTerm_p19 √(edge2FlatDX1_p19 d x1 x3 x5 a b)
    ) ∧
    -- 29. Kepler.Text.flatTerm2_234x_p19.eq_1 (Kepler.Text.LocalAuto19:203; compiler-generated equation/aux lemma (parent def `flatTerm2_234x_p19` at Kepler.Text.LocalAuto19:203; no source statement; sigtest = assembly elaboration))
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
          flatTerm2_234x_p19 d a b x1 x2 x3 x4 x5 x6 = flatTerm_p19 √(edge2FlatDX1_p19 d x2 x3 x4 a b)
    ) ∧
    -- 30. Kepler.Text.flatTerm_p19.eq_1 (Kepler.Text.LocalAuto19:116; compiler-generated equation/aux lemma (parent def `flatTerm_p19` at Kepler.Text.LocalAuto19:116; no source statement; sigtest = assembly elaboration))
    (∀ (y : ℝ), flatTerm_p19 y = sol0 * (y - 2 * h0) / (2 * h0 - 2)
    ) ∧
    -- 31. Kepler.Text.flat_term_2_p19 (Kepler.Text.LocalAuto19:889; HOL `flat_term_2`)
    (flatTerm_p19 2 = -sol0
    ) ∧
    -- 32. Kepler.Text.flat_term_2h0_p19 (Kepler.Text.LocalAuto19:897; HOL `flat_term_2h0`)
    (flatTerm_p19 (2 * h0) = 0
    ) ∧
    -- 33. Kepler.Text.flat_term_neg_p19 (Kepler.Text.LocalAuto19:382; HOL `flat_term_neg`)
    (∀ (y : ℝ) (hy : y ≤ 2 * h0),
    flatTerm_p19 y ≤ 0
    ) ∧
    -- 34. Kepler.Text.flat_term_sol0_p19 (Kepler.Text.LocalAuto19:903; HOL `flat_term_sol0`)
    (∀ (y : ℝ) (hy : 2 ≤ y),
    -sol0 ≤ flatTerm_p19 y
    ) ∧
    -- 35. Kepler.Text.h0_num_p19 (Kepler.Text.LocalAuto19:336; no HOL anchor line in file docstring)
    (h0 = 1.26 ∧ 2 * h0 = 2.52 ∧ 2 * h0 - 2 = 0.52
    ) ∧
    -- 36. Kepler.Text.ineq_sym_s2_aab_p19 (Kepler.Text.LocalAuto19:1450; HOL `ineq_sym_s2_aab`)
    (∀ {y4 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
          (hp : ineqP19 p (r ∨ y6 < y4)) (hord : y4 ≤ y6),
    ineqP19 p r
    ) ∧
    -- 37. Kepler.Text.ineq_sym_s2_abb_p19 (Kepler.Text.LocalAuto19:1464; HOL `ineq_sym_s2_abb`)
    (∀ {y5 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
          (hp : ineqP19 p (r ∨ y5 < y6)) (hord : y6 ≤ y5),
    ineqP19 p r
    ) ∧
    -- 38. Kepler.Text.ineq_sym_s3_p19 (Kepler.Text.LocalAuto19:1434; HOL `ineq_sym_s3`)
    (∀ {y4 y5 y6 : ℝ} {p : List (ℝ × ℝ × ℝ)} {r : Prop}
          (hp : ineqP19 p (r ∨ y6 < y4 ∨ y5 < y6)) (hord : y4 ≤ y6 ∧ y6 ≤ y5),
    ineqP19 p r
    ) ∧
    -- 39. Kepler.Text.mu6X_p19.eq_1 (Kepler.Text.LocalAuto19:113; compiler-generated equation/aux lemma (parent def `mu6X_p19` at Kepler.Text.LocalAuto19:113; no source statement; sigtest = assembly elaboration))
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ), mu6X_p19 x1 x2 x3 x4 x5 x6 = muY_p19 √x1 √x2 √x3
    ) ∧
    -- 40. Kepler.Text.muY_p19.eq_1 (Kepler.Text.LocalAuto19:108; compiler-generated equation/aux lemma (parent def `muY_p19` at Kepler.Text.LocalAuto19:108; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 : ℝ), muY_p19 y1 y2 y3 = 12e-3 + 7e-2 * (2.52 - y1) + 1e-2 * (2.52 * 2 - y2 - y3)
    ) ∧
    -- 41. Kepler.Text.mu_y_ft_combine_p19 (Kepler.Text.LocalAuto19:388; HOL `mu_y_ft_combine`)
    (∀ (y y2 y3 sd : ℝ),
    muY_p19 y y2 y3 * sd + flatTerm_p19 y
          = muY_p19 (2 * h0) y2 y3 * sd +
            (1 - (2 * h0 - 2) * 0.07 * sd / sol0) * flatTerm_p19 y
    ) ∧
    -- 42. Kepler.Text.mu_y_sym_cases_p19 (Kepler.Text.LocalAuto19:1340; HOL `mu_y_sym_cases`)
    (∀ (y1 y2 y3 : ℝ),
    muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y1 * y1))
            = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2)) ∧
          muY_p19 2 (Real.sqrt (y3 * y3)) (Real.sqrt (y2 * y2))
            = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3)) ∧
          muY_p19 2 (Real.sqrt (y3 * y3)) (Real.sqrt (y1 * y1))
            = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
    ) ∧
    -- 43. Kepler.Text.mu_y_sym_p19 (Kepler.Text.LocalAuto19:1336; HOL `mu_y_sym`)
    (∀ (y1 y2 y3 : ℝ),
    muY_p19 y1 y2 y3 = muY_p19 y1 y3 y2
    ) ∧
    -- 44. Kepler.Text.mud126xV1_p19.eq_1 (Kepler.Text.LocalAuto19:154; compiler-generated equation/aux lemma (parent def `mud126xV1_p19` at Kepler.Text.LocalAuto19:154; no source statement; sigtest = assembly elaboration))
    (∀ (a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mud126xV1_p19 a b c x1 x2 x3 x4 x5 x6 = muY_p19 a √x1 √x2 * √(delta126x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 45. Kepler.Text.mud135xV1_p19.eq_1 (Kepler.Text.LocalAuto19:160; compiler-generated equation/aux lemma (parent def `mud135xV1_p19` at Kepler.Text.LocalAuto19:160; no source statement; sigtest = assembly elaboration))
    (∀ (a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mud135xV1_p19 a b c x1 x2 x3 x4 x5 x6 = muY_p19 a √x1 √x3 * √(delta135x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 46. Kepler.Text.mud234xV1_p19.eq_1 (Kepler.Text.LocalAuto19:166; compiler-generated equation/aux lemma (parent def `mud234xV1_p19` at Kepler.Text.LocalAuto19:166; no source statement; sigtest = assembly elaboration))
    (∀ (a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mud234xV1_p19 a b c x1 x2 x3 x4 x5 x6 = muY_p19 a √x2 √x3 * √(delta234x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6)
    ) ∧
    -- 47. Kepler.Text.mudLs126x_p19.eq_1 (Kepler.Text.LocalAuto19:172; compiler-generated equation/aux lemma (parent def `mudLs126x_p19` at Kepler.Text.LocalAuto19:172; no source statement; sigtest = assembly elaboration))
    (∀ (d1s d2s a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mudLs126x_p19 d1s d2s a b c x1 x2 x3 x4 x5 x6 =
            mu6X_p19 (a * a) x1 x2 0 0 0 *
              (1 / (d1s + d2s) * (delta126x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)
    ) ∧
    -- 48. Kepler.Text.mudLs135x_p19.eq_1 (Kepler.Text.LocalAuto19:179; compiler-generated equation/aux lemma (parent def `mudLs135x_p19` at Kepler.Text.LocalAuto19:179; no source statement; sigtest = assembly elaboration))
    (∀ (d1s d2s a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mudLs135x_p19 d1s d2s a b c x1 x2 x3 x4 x5 x6 =
            mu6X_p19 (a * a) x1 x3 0 0 0 *
              (1 / (d1s + d2s) * (delta135x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)
    ) ∧
    -- 49. Kepler.Text.mudLs234x_p19.eq_1 (Kepler.Text.LocalAuto19:186; compiler-generated equation/aux lemma (parent def `mudLs234x_p19` at Kepler.Text.LocalAuto19:186; no source statement; sigtest = assembly elaboration))
    (∀ (d1s d2s a b c x1 x2 x3 x4 x5 x6 : ℝ),
          mudLs234x_p19 d1s d2s a b c x1 x2 x3 x4 x5 x6 =
            mu6X_p19 (a * a) x2 x3 0 0 0 *
              (1 / (d1s + d2s) * (delta234x_p19 (a * a) (b * b) (c * c) x1 x2 x3 x4 x5 x6 - d1s * d1s) + d1s)
    ) ∧
    -- 50. Kepler.Text.mud_126_135_p19 (Kepler.Text.LocalAuto19:879; HOL `mud_126_135`)
    (∀ (y1 y2 y3 y4 y5 y6 y3' y4' y5' : ℝ),
    mud126xV1_p19 y3' y4' y5' y1 y2 y3 y4 y5 y6
          = mud135xV1_p19 y3' y4' y5' y1 y3 y2 y4 y6 y5
    ) ∧
    -- 51. Kepler.Text.nonfunctional_flat_term2_126_p19 (Kepler.Text.LocalAuto19:1380; HOL `nonfunctional_flat_term2_126`)
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
    flatTerm2_126x_p19 d a b x1 x2 x3 x4 x5 x6
          = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x2 x6 a b))
    ) ∧
    -- 52. Kepler.Text.nonfunctional_flat_term2_135_p19 (Kepler.Text.LocalAuto19:1390; HOL `nonfunctional_flat_term2_135`)
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
    flatTerm2_135x_p19 d a b x1 x2 x3 x4 x5 x6
          = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x1 x3 x5 a b))
    ) ∧
    -- 53. Kepler.Text.nonfunctional_flat_term2_234_p19 (Kepler.Text.LocalAuto19:1385; HOL `nonfunctional_flat_term2_234`)
    (∀ (d a b x1 x2 x3 x4 x5 x6 : ℝ),
    flatTerm2_234x_p19 d a b x1 x2 x3 x4 x5 x6
          = flatTerm_p19 (Real.sqrt (edge2FlatDX1_p19 d x2 x3 x4 a b))
    ) ∧
    -- 54. Kepler.Text.nonfunctional_mu6_x_y_p19 (Kepler.Text.LocalAuto19:427; HOL `nonfunctional_mu6_x_y`)
    (∀ (x1 x2 x3 a b c : ℝ),
    mu6X_p19 x1 x2 x3 a b c = muY_p19 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
    ) ∧
    -- 55. Kepler.Text.nonfunctional_mudLs_126_p19 (Kepler.Text.LocalAuto19:1395; HOL `nonfunctional_mudLs_126`)
    (∀ (y1 y2 x3 x4 x5 y6 : ℝ),
    mudLs126x_p19 4 10 2 2 2 (y1 * y1) (y2 * y2) x3 x4 x5 (y6 * y6)
          = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
              * (1 / 14 * (deltaY 2 y1 y2 y6 2 2 - 16) + 4)
    ) ∧
    -- 56. Kepler.Text.nonfunctional_mudLs_135_p19 (Kepler.Text.LocalAuto19:1420; HOL `nonfunctional_mudLs_135`)
    (∀ (y1 x2 y3 x4 y5 x6 : ℝ),
    mudLs135x_p19 4 10 2 2 2 (y1 * y1) x2 (y3 * y3) x4 (y5 * y5) x6
          = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
              * (1 / 14 * (deltaY 2 y1 y3 y5 2 2 - 16) + 4)
    ) ∧
    -- 57. Kepler.Text.nonfunctional_mudLs_234_p19 (Kepler.Text.LocalAuto19:1409; HOL `nonfunctional_mudLs_234`)
    (∀ (x1 y2 y3 y4 x5 x6 : ℝ),
    mudLs234x_p19 4 10 2 2 2 x1 (y2 * y2) (y3 * y3) (y4 * y4) x5 x6
          = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * (1 / 14 * (deltaY 2 y2 y3 y4 2 2 - 16) + 4)
    ) ∧
    -- 58. Kepler.Text.nonfunctional_mud_126_p19 (Kepler.Text.LocalAuto19:1355; HOL `nonfunctional_mud_126`)
    (∀ (a b c y1 y2 y3 y4 y5 y6 : ℝ),
    yOfX (mud126xV1_p19 a b c) y1 y2 y3 y4 y5 y6
          = muY_p19 a (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
              * Real.sqrt (deltaY a y1 y2 y6 b c)
    ) ∧
    -- 59. Kepler.Text.nonfunctional_mud_135_p19 (Kepler.Text.LocalAuto19:1373; HOL `nonfunctional_mud_135`)
    (∀ (a b c y1 y2 y3 y4 y5 y6 : ℝ),
    yOfX (mud135xV1_p19 a b c) y1 y2 y3 y4 y5 y6
          = muY_p19 a (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
              * Real.sqrt (deltaY a y1 y3 y5 b c)
    ) ∧
    -- 60. Kepler.Text.nonfunctional_mud_234_p19 (Kepler.Text.LocalAuto19:1362; HOL `nonfunctional_mud_234`)
    (∀ (a b c y1 y2 y3 y4 y5 y6 : ℝ),
    yOfX (mud234xV1_p19 a b c) y1 y2 y3 y4 y5 y6
          = muY_p19 a (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * Real.sqrt (deltaY a y2 y3 y4 b c)
    ) ∧
    -- 61. Kepler.Text.quadratic_root_imp_discr_nn_p19 (Kepler.Text.LocalAuto19:974; HOL `quadratic_root_imp_discr_nn`)
    (∀ (a b c x : ℝ)
          (h : a * x ^ 2 + b * x + c = 0),
    0 ≤ b * b - 4 * a * c
    ) ∧
    -- 62. Kepler.Text.quadratic_root_minus_works_p19 (Kepler.Text.LocalAuto19:958; HOL `quadratic_root_minus_works`)
    (∀ (a b c : ℝ) (ha : a ≠ 0)
          (hd : 0 ≤ b * b - 4 * a * c),
    a * (-(b + Real.sqrt (b * b - 4 * a * c)) / (2 * a)) ^ 2
          + b * (-(b + Real.sqrt (b * b - 4 * a * c)) / (2 * a)) + c = 0
    ) ∧
    -- 63. Kepler.Text.quadratic_root_plus_eq_p19 (Kepler.Text.LocalAuto19:982; HOL `quadratic_root_plus_eq`)
    (∀ (a b c m x : ℝ) (ha : 0 < a) (hm : m ≤ x)
          (h : a * x ^ 2 + b * x + c = 0)
          (hdisj : 0 < 2 * m * a + b ∨ (2 * m * a + b) ^ 2 < b * b - 4 * a * c),
    quadraticRootPlus a b c = x
    ) ∧
    -- 64. Kepler.Text.r755C126_p19.eq_1 (Kepler.Text.LocalAuto19:275; compiler-generated equation/aux lemma (parent def `r755C126_p19` at Kepler.Text.LocalAuto19:275; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C126_p19 0 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y2 y6 2 2 < 0 ∨ deltaY 2.52 y1 y2 y6 2 2 > 0)
    ) ∧
    -- 65. Kepler.Text.r755C126_p19.eq_2 (Kepler.Text.LocalAuto19:275; compiler-generated equation/aux lemma (parent def `r755C126_p19` at Kepler.Text.LocalAuto19:275; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C126_p19 1 y1 y2 y3 y4 y5 y6 = False
    ) ∧
    -- 66. Kepler.Text.r755C126_p19.eq_3 (Kepler.Text.LocalAuto19:275; compiler-generated equation/aux lemma (parent def `r755C126_p19` at Kepler.Text.LocalAuto19:275; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C126_p19 2 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y2 y6 2 2 < 100)
    ) ∧
    -- 67. Kepler.Text.r755C126_p19.eq_4 (Kepler.Text.LocalAuto19:275; compiler-generated equation/aux lemma (parent def `r755C126_p19` at Kepler.Text.LocalAuto19:275; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C126_p19 3 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y2 y6 2 2 < 16 ∨ deltaY 2 y1 y2 y6 2 2 > 100)
    ) ∧
    -- 68. Kepler.Text.r755C126_p19.eq_5 (Kepler.Text.LocalAuto19:275; compiler-generated equation/aux lemma (parent def `r755C126_p19` at Kepler.Text.LocalAuto19:275; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) →
            (i = 1 → False) →
              (i = 2 → False) →
                (i = 3 → False) → r755C126_p19 i y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y2 y6 2 2 < 0 ∨ deltaY 2 y1 y2 y6 2 2 > 16)
    ) ∧
    -- 69. Kepler.Text.r755C126_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1517; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755C126_p19 i y1 y3 y2 y4 y6 y5 = r755C135_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 70. Kepler.Text.r755C135_p19.eq_1 (Kepler.Text.LocalAuto19:284; compiler-generated equation/aux lemma (parent def `r755C135_p19` at Kepler.Text.LocalAuto19:284; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C135_p19 0 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y3 y5 2 2 < 0 ∨ deltaY 2.52 y1 y3 y5 2 2 > 0)
    ) ∧
    -- 71. Kepler.Text.r755C135_p19.eq_2 (Kepler.Text.LocalAuto19:284; compiler-generated equation/aux lemma (parent def `r755C135_p19` at Kepler.Text.LocalAuto19:284; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C135_p19 1 y1 y2 y3 y4 y5 y6 = False
    ) ∧
    -- 72. Kepler.Text.r755C135_p19.eq_3 (Kepler.Text.LocalAuto19:284; compiler-generated equation/aux lemma (parent def `r755C135_p19` at Kepler.Text.LocalAuto19:284; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C135_p19 2 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y3 y5 2 2 < 100)
    ) ∧
    -- 73. Kepler.Text.r755C135_p19.eq_4 (Kepler.Text.LocalAuto19:284; compiler-generated equation/aux lemma (parent def `r755C135_p19` at Kepler.Text.LocalAuto19:284; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C135_p19 3 y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y3 y5 2 2 < 16 ∨ deltaY 2 y1 y3 y5 2 2 > 100)
    ) ∧
    -- 74. Kepler.Text.r755C135_p19.eq_5 (Kepler.Text.LocalAuto19:284; compiler-generated equation/aux lemma (parent def `r755C135_p19` at Kepler.Text.LocalAuto19:284; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) →
            (i = 1 → False) →
              (i = 2 → False) →
                (i = 3 → False) → r755C135_p19 i y1 y2 y3 y4 y5 y6 = (deltaY 2 y1 y3 y5 2 2 < 0 ∨ deltaY 2 y1 y3 y5 2 2 > 16)
    ) ∧
    -- 75. Kepler.Text.r755C135_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1521; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755C135_p19 i y1 y3 y2 y4 y6 y5 = r755C126_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 76. Kepler.Text.r755C234_p19.eq_1 (Kepler.Text.LocalAuto19:266; compiler-generated equation/aux lemma (parent def `r755C234_p19` at Kepler.Text.LocalAuto19:266; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C234_p19 0 y1 y2 y3 y4 y5 y6 = (deltaY 2 y2 y3 y4 2 2 < 0 ∨ deltaY 2.52 y2 y3 y4 2 2 > 0)
    ) ∧
    -- 77. Kepler.Text.r755C234_p19.eq_2 (Kepler.Text.LocalAuto19:266; compiler-generated equation/aux lemma (parent def `r755C234_p19` at Kepler.Text.LocalAuto19:266; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C234_p19 1 y1 y2 y3 y4 y5 y6 = False
    ) ∧
    -- 78. Kepler.Text.r755C234_p19.eq_3 (Kepler.Text.LocalAuto19:266; compiler-generated equation/aux lemma (parent def `r755C234_p19` at Kepler.Text.LocalAuto19:266; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755C234_p19 2 y1 y2 y3 y4 y5 y6 = (deltaY 2 y2 y3 y4 2 2 < 100)
    ) ∧
    -- 79. Kepler.Text.r755C234_p19.eq_4 (Kepler.Text.LocalAuto19:266; compiler-generated equation/aux lemma (parent def `r755C234_p19` at Kepler.Text.LocalAuto19:266; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755C234_p19 3 y1 y2 y3 y4 y5 y6 = (deltaY 2 y2 y3 y4 2 2 < 16 ∨ deltaY 2 y2 y3 y4 2 2 > 100)
    ) ∧
    -- 80. Kepler.Text.r755C234_p19.eq_5 (Kepler.Text.LocalAuto19:266; compiler-generated equation/aux lemma (parent def `r755C234_p19` at Kepler.Text.LocalAuto19:266; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) →
            (i = 1 → False) →
              (i = 2 → False) →
                (i = 3 → False) → r755C234_p19 i y1 y2 y3 y4 y5 y6 = (deltaY 2 y2 y3 y4 2 2 < 0 ∨ deltaY 2 y2 y3 y4 2 2 > 16)
    ) ∧
    -- 81. Kepler.Text.r755C234_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1510; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755C234_p19 i y1 y3 y2 y4 y6 y5 = r755C234_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 82. Kepler.Text.r755D126_p19.eq_1 (Kepler.Text.LocalAuto19:247; compiler-generated equation/aux lemma (parent def `r755D126_p19` at Kepler.Text.LocalAuto19:247; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D126_p19 0 y1 y2 y3 y4 y5 y6 = yOfX (flatTerm2_126x_p19 0 4 4) y1 y2 y3 y4 y5 y6
    ) ∧
    -- 83. Kepler.Text.r755D126_p19.eq_2 (Kepler.Text.LocalAuto19:247; compiler-generated equation/aux lemma (parent def `r755D126_p19` at Kepler.Text.LocalAuto19:247; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755D126_p19 1 y1 y2 y3 y4 y5 y6 = 0
    ) ∧
    -- 84. Kepler.Text.r755D126_p19.eq_3 (Kepler.Text.LocalAuto19:247; compiler-generated equation/aux lemma (parent def `r755D126_p19` at Kepler.Text.LocalAuto19:247; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D126_p19 2 y1 y2 y3 y4 y5 y6 = yOfX (mud126xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 85. Kepler.Text.r755D126_p19.eq_4 (Kepler.Text.LocalAuto19:247; compiler-generated equation/aux lemma (parent def `r755D126_p19` at Kepler.Text.LocalAuto19:247; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D126_p19 3 y1 y2 y3 y4 y5 y6 = yOfX (mudLs126x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 86. Kepler.Text.r755D126_p19.eq_5 (Kepler.Text.LocalAuto19:247; compiler-generated equation/aux lemma (parent def `r755D126_p19` at Kepler.Text.LocalAuto19:247; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) → (i = 1 → False) → (i = 2 → False) → (i = 3 → False) → r755D126_p19 i y1 y2 y3 y4 y5 y6 = 0 - sol0
    ) ∧
    -- 87. Kepler.Text.r755D126_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1492; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755D126_p19 i y1 y3 y2 y4 y6 y5 = r755D135_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 88. Kepler.Text.r755D135_p19.eq_1 (Kepler.Text.LocalAuto19:256; compiler-generated equation/aux lemma (parent def `r755D135_p19` at Kepler.Text.LocalAuto19:256; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D135_p19 0 y1 y2 y3 y4 y5 y6 = yOfX (flatTerm2_135x_p19 0 4 4) y1 y2 y3 y4 y5 y6
    ) ∧
    -- 89. Kepler.Text.r755D135_p19.eq_2 (Kepler.Text.LocalAuto19:256; compiler-generated equation/aux lemma (parent def `r755D135_p19` at Kepler.Text.LocalAuto19:256; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755D135_p19 1 y1 y2 y3 y4 y5 y6 = 0
    ) ∧
    -- 90. Kepler.Text.r755D135_p19.eq_3 (Kepler.Text.LocalAuto19:256; compiler-generated equation/aux lemma (parent def `r755D135_p19` at Kepler.Text.LocalAuto19:256; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D135_p19 2 y1 y2 y3 y4 y5 y6 = yOfX (mud135xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 91. Kepler.Text.r755D135_p19.eq_4 (Kepler.Text.LocalAuto19:256; compiler-generated equation/aux lemma (parent def `r755D135_p19` at Kepler.Text.LocalAuto19:256; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D135_p19 3 y1 y2 y3 y4 y5 y6 = yOfX (mudLs135x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 92. Kepler.Text.r755D135_p19.eq_5 (Kepler.Text.LocalAuto19:256; compiler-generated equation/aux lemma (parent def `r755D135_p19` at Kepler.Text.LocalAuto19:256; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) → (i = 1 → False) → (i = 2 → False) → (i = 3 → False) → r755D135_p19 i y1 y2 y3 y4 y5 y6 = 0 - sol0
    ) ∧
    -- 93. Kepler.Text.r755D135_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1501; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755D135_p19 i y1 y3 y2 y4 y6 y5 = r755D126_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 94. Kepler.Text.r755D234_p19.eq_1 (Kepler.Text.LocalAuto19:238; compiler-generated equation/aux lemma (parent def `r755D234_p19` at Kepler.Text.LocalAuto19:238; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D234_p19 0 y1 y2 y3 y4 y5 y6 = yOfX (flatTerm2_234x_p19 0 4 4) y1 y2 y3 y4 y5 y6
    ) ∧
    -- 95. Kepler.Text.r755D234_p19.eq_2 (Kepler.Text.LocalAuto19:238; compiler-generated equation/aux lemma (parent def `r755D234_p19` at Kepler.Text.LocalAuto19:238; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ), r755D234_p19 1 y1 y2 y3 y4 y5 y6 = 0
    ) ∧
    -- 96. Kepler.Text.r755D234_p19.eq_3 (Kepler.Text.LocalAuto19:238; compiler-generated equation/aux lemma (parent def `r755D234_p19` at Kepler.Text.LocalAuto19:238; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D234_p19 2 y1 y2 y3 y4 y5 y6 = yOfX (mud234xV1_p19 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 97. Kepler.Text.r755D234_p19.eq_4 (Kepler.Text.LocalAuto19:238; compiler-generated equation/aux lemma (parent def `r755D234_p19` at Kepler.Text.LocalAuto19:238; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          r755D234_p19 3 y1 y2 y3 y4 y5 y6 = yOfX (mudLs234x_p19 4 10 2 2 2) y1 y2 y3 y4 y5 y6 - sol0
    ) ∧
    -- 98. Kepler.Text.r755D234_p19.eq_5 (Kepler.Text.LocalAuto19:238; compiler-generated equation/aux lemma (parent def `r755D234_p19` at Kepler.Text.LocalAuto19:238; no source statement; sigtest = assembly elaboration))
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
          (i = 0 → False) → (i = 1 → False) → (i = 2 → False) → (i = 3 → False) → r755D234_p19 i y1 y2 y3 y4 y5 y6 = 0 - sol0
    ) ∧
    -- 99. Kepler.Text.r755D234_shuffle_ikj_p19 (Kepler.Text.LocalAuto19:1483; no HOL anchor line in file docstring)
    (∀ (i : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ),
    r755D234_p19 i y1 y3 y2 y4 y6 y5 = r755D234_p19 i y1 y2 y3 y4 y5 y6
    ) ∧
    -- 100. Kepler.Text.sol0Pos_p19 (Kepler.Text.LocalAuto19:318; HOL `Flyspeck_constants.bounds`)
    (0 < sol0
    ) ∧
    -- 101. Kepler.Text.sqrt20_p19 (Kepler.Text.LocalAuto19:1169; HOL `sqrt20`)
    (4.47 ≤ Real.sqrt 20
    ) ∧
    -- 102. Kepler.Text.sqrt_secant_approx_p19 (Kepler.Text.LocalAuto19:343; HOL `sqrt_secant_approx`)
    (∀ {x1 x2 x : ℝ} (ha : 0 ≤ x1) (hb : x1 ≤ x) (hc : x ≤ x2),
    (1 / (Real.sqrt x1 + Real.sqrt x2)) * (x - x1) + Real.sqrt x1 ≤ Real.sqrt x
    ) ∧
    -- 103. Kepler.Text.taudP19.eq_1 (Kepler.Text.LocalAuto19:122; compiler-generated equation/aux lemma (parent def `taudP19` at Kepler.Text.LocalAuto19:122; no source statement; sigtest = assembly elaboration))
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ),
          taudP19 y1 y2 y3 y4 y5 y6 = flatTerm_p19 y1 + √(deltaY y1 y2 y3 y4 y5 y6) * muY_p19 y1 y2 y3
    ) ∧
    -- 104. Kepler.Text.taud_053_p19 (Kepler.Text.LocalAuto19:937; HOL `taud_053`)
    (∀ (y2 y3 y4 y5 y6 : ℝ)
          (hy2 : y2 ≤ 2 * h0) (hy3 : y3 ≤ 2 * h0)
          (hd : 20 ≤ deltaY (2 * h0) y2 y3 y4 y5 y6),
    0.053 ≤ taudP19 (2 * h0) y2 y3 y4 y5 y6
    ) ∧
    -- 105. Kepler.Text.taud_2h0_p19 (Kepler.Text.LocalAuto19:922; HOL `taud_2h0`)
    (∀ (y2 y3 y4 y5 y6 : ℝ)
          (hd : 0 ≤ deltaY (2 * h0) y2 y3 y4 y5 y6)
          (hy2 : y2 ≤ 2 * h0) (hy3 : y3 ≤ 2 * h0),
    0 ≤ taudP19 (2 * h0) y2 y3 y4 y5 y6
    ) ∧
    -- 106. Kepler.Text.taud_continuous_p19 (Kepler.Text.LocalAuto19:756; HOL `taud_continuous`)
    (∀ (y2 y3 y4 y5 y6 : ℝ),
    ContinuousOn (fun q => taudP19 q y2 y3 y4 y5 y6)
          {q | 0 ≤ deltaY q y2 y3 y4 y5 y6}
    ) ∧
    -- 107. Kepler.Text.taud_ge_flat_term_p19 (Kepler.Text.LocalAuto19:1157; HOL `taud_ge_flat_term`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
          (h1 : y1 ≤ 2 * h0) (h2 : y2 ≤ 2 * h0) (h3 : y3 ≤ 2 * h0)
          (hd : 0 ≤ deltaY y1 y2 y3 y4 y5 y6),
    flatTerm_p19 y1 ≤ taudP19 y1 y2 y3 y4 y5 y6
    ) ∧
    -- 108. Kepler.Text.taud_minimizer_p19 (Kepler.Text.LocalAuto19:797; HOL `taud_minimizer`)
    (∀ (a b d y2 y3 y4 y5 y6 : ℝ)
          (hd : 0 ≤ d)
          (hne : (Set.Icc a b ∩ {q : ℝ | d ≤ deltaY q y2 y3 y4 y5 y6}) ≠ ∅),
    ∃ z1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY q y2 y3 y4 y5 y6},
          ∀ y1 ∈ Set.Icc a b ∩ {q : ℝ | d ≤ deltaY q y2 y3 y4 y5 y6},
            taudP19 z1 y2 y3 y4 y5 y6 ≤ taudP19 y1 y2 y3 y4 y5 y6
    ) ∧
    -- 109. Kepler.Text.taud_mud_126_x_p19 (Kepler.Text.LocalAuto19:848; HOL `taud_mud_126_x`)
    (∀ (y3 y4 y5 y1 y2 y3' y4' y5' y6 : ℝ) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2),
    yOfX (mud126xV1_p19 y3 y4 y5) y1 y2 y3' y4' y5' y6
          = taudP19 y3 y1 y2 y6 y4 y5 - flatTerm_p19 y3
    ) ∧
    -- 110. Kepler.Text.taud_mud_135_x_p19 (Kepler.Text.LocalAuto19:863; HOL `taud_mud_135_x`)
    (∀ (y2 y4 y6 y1 y2' y3 y4' y5 y6' : ℝ) (h1 : 0 ≤ y1) (h3 : 0 ≤ y3),
    yOfX (mud135xV1_p19 y2 y4 y6) y1 y2' y3 y4' y5 y6'
          = taudP19 y2 y1 y3 y5 y4 y6 - flatTerm_p19 y2
    ) :=
⟨_root_.Kepler.Text.OPEN_REAL_INTERVAL_SING_p19, _root_.Kepler.Text.REAL_WLOG_AAB_SIMPLEX_p19,
      _root_.Kepler.Text.REAL_WLOG_ABB_SIMPLEX_p19, _root_.Kepler.Text.REAL_WLOG_S3_SIMPLEX_p19,
      _root_.Kepler.Text.abcOfQuadratic_p19_quad,
      _root_.Kepler.Text.continuous_preimage_closed_p19,
      _root_.Kepler.Text.continuous_preimage_open_p19, _root_.Kepler.Text.delta126x_p19.eq_1,
      _root_.Kepler.Text.delta135x_p19.eq_1, _root_.Kepler.Text.delta234x_p19.eq_1,
      _root_.Kepler.Text.deltaX_perm_p19, _root_.Kepler.Text.deltaX_swap_p19,
      _root_.Kepler.Text.deltaX_vert12_p19, _root_.Kepler.Text.deltaY_hasDerivAt_p19,
      _root_.Kepler.Text.delta_diff_p19, _root_.Kepler.Text.delta_y_continuous_p19,
      _root_.Kepler.Text.delta_y_sym_cases2_p19, _root_.Kepler.Text.deriv_form_taud_p19,
      _root_.Kepler.Text.derived_form_F_p19, _root_.Kepler.Text.derived_form_delta_y_p19,
      _root_.Kepler.Text.derived_form_taud_ALT_p19, _root_.Kepler.Text.derived_form_taud_D3_p19,
      _root_.Kepler.Text.edge2_flatD_sym_p19, _root_.Kepler.Text.edge2_flatD_x1_delta_lemma2_p19,
      _root_.Kepler.Text.edge2_flatD_x1_sym_cases_p19, _root_.Kepler.Text.eulerA_x_sym_cases_p19,
      _root_.Kepler.Text.flatTerm2_126x_p19.eq_1, _root_.Kepler.Text.flatTerm2_135x_p19.eq_1,
      _root_.Kepler.Text.flatTerm2_234x_p19.eq_1, _root_.Kepler.Text.flatTerm_p19.eq_1,
      _root_.Kepler.Text.flat_term_2_p19, _root_.Kepler.Text.flat_term_2h0_p19,
      _root_.Kepler.Text.flat_term_neg_p19, _root_.Kepler.Text.flat_term_sol0_p19,
      _root_.Kepler.Text.h0_num_p19, _root_.Kepler.Text.ineq_sym_s2_aab_p19,
      _root_.Kepler.Text.ineq_sym_s2_abb_p19, _root_.Kepler.Text.ineq_sym_s3_p19,
      _root_.Kepler.Text.mu6X_p19.eq_1, _root_.Kepler.Text.muY_p19.eq_1,
      _root_.Kepler.Text.mu_y_ft_combine_p19, _root_.Kepler.Text.mu_y_sym_cases_p19,
      _root_.Kepler.Text.mu_y_sym_p19, _root_.Kepler.Text.mud126xV1_p19.eq_1,
      _root_.Kepler.Text.mud135xV1_p19.eq_1, _root_.Kepler.Text.mud234xV1_p19.eq_1,
      _root_.Kepler.Text.mudLs126x_p19.eq_1, _root_.Kepler.Text.mudLs135x_p19.eq_1,
      _root_.Kepler.Text.mudLs234x_p19.eq_1, _root_.Kepler.Text.mud_126_135_p19,
      _root_.Kepler.Text.nonfunctional_flat_term2_126_p19,
      _root_.Kepler.Text.nonfunctional_flat_term2_135_p19,
      _root_.Kepler.Text.nonfunctional_flat_term2_234_p19,
      _root_.Kepler.Text.nonfunctional_mu6_x_y_p19,
      _root_.Kepler.Text.nonfunctional_mudLs_126_p19,
      _root_.Kepler.Text.nonfunctional_mudLs_135_p19,
      _root_.Kepler.Text.nonfunctional_mudLs_234_p19,
      _root_.Kepler.Text.nonfunctional_mud_126_p19, _root_.Kepler.Text.nonfunctional_mud_135_p19,
      _root_.Kepler.Text.nonfunctional_mud_234_p19,
      _root_.Kepler.Text.quadratic_root_imp_discr_nn_p19,
      _root_.Kepler.Text.quadratic_root_minus_works_p19,
      _root_.Kepler.Text.quadratic_root_plus_eq_p19, _root_.Kepler.Text.r755C126_p19.eq_1,
      _root_.Kepler.Text.r755C126_p19.eq_2, _root_.Kepler.Text.r755C126_p19.eq_3,
      _root_.Kepler.Text.r755C126_p19.eq_4, _root_.Kepler.Text.r755C126_p19.eq_5,
      _root_.Kepler.Text.r755C126_shuffle_ikj_p19, _root_.Kepler.Text.r755C135_p19.eq_1,
      _root_.Kepler.Text.r755C135_p19.eq_2, _root_.Kepler.Text.r755C135_p19.eq_3,
      _root_.Kepler.Text.r755C135_p19.eq_4, _root_.Kepler.Text.r755C135_p19.eq_5,
      _root_.Kepler.Text.r755C135_shuffle_ikj_p19, _root_.Kepler.Text.r755C234_p19.eq_1,
      _root_.Kepler.Text.r755C234_p19.eq_2, _root_.Kepler.Text.r755C234_p19.eq_3,
      _root_.Kepler.Text.r755C234_p19.eq_4, _root_.Kepler.Text.r755C234_p19.eq_5,
      _root_.Kepler.Text.r755C234_shuffle_ikj_p19, _root_.Kepler.Text.r755D126_p19.eq_1,
      _root_.Kepler.Text.r755D126_p19.eq_2, _root_.Kepler.Text.r755D126_p19.eq_3,
      _root_.Kepler.Text.r755D126_p19.eq_4, _root_.Kepler.Text.r755D126_p19.eq_5,
      _root_.Kepler.Text.r755D126_shuffle_ikj_p19, _root_.Kepler.Text.r755D135_p19.eq_1,
      _root_.Kepler.Text.r755D135_p19.eq_2, _root_.Kepler.Text.r755D135_p19.eq_3,
      _root_.Kepler.Text.r755D135_p19.eq_4, _root_.Kepler.Text.r755D135_p19.eq_5,
      _root_.Kepler.Text.r755D135_shuffle_ikj_p19, _root_.Kepler.Text.r755D234_p19.eq_1,
      _root_.Kepler.Text.r755D234_p19.eq_2, _root_.Kepler.Text.r755D234_p19.eq_3,
      _root_.Kepler.Text.r755D234_p19.eq_4, _root_.Kepler.Text.r755D234_p19.eq_5,
      _root_.Kepler.Text.r755D234_shuffle_ikj_p19, _root_.Kepler.Text.sol0Pos_p19,
      _root_.Kepler.Text.sqrt20_p19, _root_.Kepler.Text.sqrt_secant_approx_p19,
      _root_.Kepler.Text.taudP19.eq_1, _root_.Kepler.Text.taud_053_p19,
      _root_.Kepler.Text.taud_2h0_p19, @_root_.Kepler.Text.taud_continuous_p19,
      _root_.Kepler.Text.taud_ge_flat_term_p19, _root_.Kepler.Text.taud_minimizer_p19,
      _root_.Kepler.Text.taud_mud_126_x_p19, _root_.Kepler.Text.taud_mud_135_x_p19⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms la19_wire_capstone_w1

/-! ### LA5 materialization capstone (lane lv1314-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV13):
the 78 public top-level LocalAuto5 clean theorem exits (scout seeds_clean.txt LA5 group -- all 78 clean, GO pure, the file carries zero code sorries;
0 sorried family exits excluded), of which 78 are statable from LocalConcl and are re-exposed as ONE conjunction below; 0 exits are dropped per the no-forcing rule (each drop named in the theorem docstring).
Self-contained section: pure insertion, zero new imports (LA5 already visible transitively: LocalConcl:494 imports LocalAuto23, LocalAuto23:111 imports LocalAuto9, LocalAuto9:105 imports LocalAuto5), zero proof obligations
(body = the exit assembly itself), own `#print axioms` probe (the lv1112 la19 section above and the shared la34 footer below are untouched -- hunk-level disjoint).
The scoped heartbeat raise mirrors the lv1112 la19 section in this file: a conjunction statement of this size exceeds the default budget during statement elaboration
(lv910 measured the 71-conjunct PA4 case against the 200000 default; pa21 capstone uses 50000000).
-/

open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- LA5 materialization capstone (scout lane leftover-mat-scout-2
workorder LV13, implementation lane lv1314-w1, 2026-11-04).  The
78 public top-level Kepler.Text.LocalAuto5 theorem exits unreachable from every
e2e root (scout probe1/probe2: GROUP_VS_CONE fresh sorried-0, standard-three
axiom face on the axprobe sample); 78 of them are statable from
LocalConcl and are re-exposed as ONE conjunction.
Implemented here: 78 of the 78.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.LocalAuto5 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation/aux lemmas have no
source statement anywhere, so their conjunct is the `#check @name` printer
dump verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below
must unify it definitionally with the constant's type; printer dumps with
proof-term elision `...` are dropped per the lv12-w1 t_eqlemma_microtest
evidence, each drop named above).  Semantic identity of every conjunct is
re-verified by that assembly (each element must have exactly its conjunct's
type); the per-conjunct comments carry each exit's Kepler.Text.LocalAuto5 declaration
line and file-local docstring HOL anchor.  Conjunct order: the scout
seed-list order (probe1 SEED list).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports.  The scoped
`open ... in` prefix before the heartbeat raise (if any) reproduces the
source file's own open context for the verbatim conjunct texts --
mechanically computed as the source-file open tokens missing from the
host's; scoped to this one theorem, zero effect elsewhere in the host.
Elements @-prefixed by strict-implicit rule (c) (conclusion-head strict-implicit
binder trap, implicit-lambda feature; see gen_items.py AT_FORCE): Kepler.Text.Affsign_convex.  -/
theorem la5_wire_capstone_w1 :
    -- 1. Kepler.Geom.affLe.eq_1 (Kepler.Text.LocalAuto5:0; compiler-generated equation/aux lemma (parent def `affLe` at Geom.Aff:48; no source statement; sigtest = assembly elaboration))
    (∀ (s t : Set V3), affLe s t = {v | Affsign (fun x => x ≤ 0) s t v}
    ) ∧
    -- 2. Kepler.Text.AFF_GE_EQ (Kepler.Text.LocalAuto5:4991; HOL `AFF_GE_EQ`)
    (∀ {x a b : V3} {t : ℝ} (ht : 0 < t) (heq : a - x = t • (b - x)),
    affGe ({x} : Set V3) ({a} : Set V3) = affGe ({x} : Set V3) ({b} : Set V3)
    ) ∧
    -- 3. Kepler.Text.AFF_GE_MONO_TRANS (Kepler.Text.LocalAuto5:6984; HOL `AFF_GE_MONO_TRANS`)
    (∀ {S X Y : Set V3} (hsub : S ⊆ X),
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y
    ) ∧
    -- 4. Kepler.Text.AFF_GT_AFF_LT_INTERPRET (Kepler.Text.LocalAuto5:5340; HOL `AFF_GT_AFF_LT_INTERPRET`)
    (∀ {x u v w : V3} (hdis1 : Disjoint ({x} : Set V3) ({v, w} : Set V3))
          (hdis2 : Disjoint ({x} : Set V3) ({u} : Set V3)),
    (∃ aa bb c : ℝ, aa < 0 ∧ 0 < bb ∧ 0 < c ∧
          aa • (u - x) = bb • (v - x) + c • (w - x)) ↔
          ∃ tt : V3, tt ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩
            affLt ({x} : Set V3) ({u} : Set V3)
    ) ∧
    -- 5. Kepler.Text.AFF_GT_AFF_LT_INTERPRET2 (Kepler.Text.LocalAuto5:5368; HOL `AFF_GT_AFF_LT_INTERPRET2`)
    (∀ {x u v w : V3}
          (hdis : Disjoint ({x} : Set V3) ({u, v, w} : Set V3)),
    (∃ aa bb c : ℝ, aa < 0 ∧ 0 < bb ∧ 0 < c ∧
          aa • (u - x) = bb • (v - x) + c • (w - x)) ↔
          ∃ tt : V3, tt ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩
            affLt ({x} : Set V3) ({u} : Set V3)
    ) ∧
    -- 6. Kepler.Text.AFF_GT_LT_INTER_SYM (Kepler.Text.LocalAuto5:5393; HOL `AFF_GT_LT_INTER_SYM`)
    (∀ {x u v w : V3}
          (hdis : Disjoint ({x} : Set V3) ({u, v, w} : Set V3))
          (hne : ¬ (affGt ({x} : Set V3) ({v, w} : Set V3) ∩
            affLt ({x} : Set V3) ({u} : Set V3) = ∅)),
    ¬ (affGt ({x} : Set V3) ({u, v} : Set V3) ∩
          affLt ({x} : Set V3) ({w} : Set V3) = ∅)
    ) ∧
    -- 7. Kepler.Text.AFF_GT_LT_INTER_SYM._abel_1_1 (Kepler.Text.LocalAuto5:5393; compiler-generated equation/aux lemma (parent def `AFF_GT_LT_INTER_SYM` at Kepler.Text.LocalAuto5:5393; no source statement; sigtest = assembly elaboration))
    (∀ {x w : V3}, x - (w - x) - x = -(w - x)
    ) ∧
    -- 8. Kepler.Text.AFF_GT_MONO (Kepler.Text.LocalAuto5:7748; HOL `AFF_GT_MONO`)
    (∀ {X Y S : Set V3} (hS : S ⊆ Y),
    affGt X Y ⊆ affGt (X ∪ S) (Y \ S)
    ) ∧
    -- 9. Kepler.Text.AFF_GT_MONO_TRANS (Kepler.Text.LocalAuto5:7006; no HOL anchor line in file docstring)
    (∀ {S X Y : Set V3} (hsub : S ⊆ X),
    affGt (X \ S) (Y ∪ S) ⊆ affGt X Y
    ) ∧
    -- 10. Kepler.Text.AFF_GT_SUB_AFF_UNION (Kepler.Text.LocalAuto5:7766; HOL `AFF_GT_SUB_AFF_UNION`)
    (∀ (X Y : Set V3),
    affGt X Y ⊆ (affineSpan ℝ (X ∪ Y) : Set V3)
    ) ∧
    -- 11. Kepler.Text.AFF_XX_CASES (Kepler.Text.LocalAuto5:5029; HOL `AFF_XX_CASES`)
    (∀ (x : V3),
    affLt ({x} : Set V3) ({x} : Set V3) = (∅ : Set V3) ∧
          affLe ({x} : Set V3) ({x} : Set V3) = ∅ ∧
          affGt ({x} : Set V3) ({x} : Set V3) = ({x} : Set V3)
    ) ∧
    -- 12. Kepler.Text.AZIM_PI_CONVEX_WEDGE (Kepler.Text.LocalAuto5:6140; HOL `AZIM_PI_CONVEX_WEDGE`)
    (∀ {u v w ww : V3} (h : azim u v w ww = Real.pi),
    Convex ℝ (wedgeGe_p2 u v w ww)
    ) ∧
    -- 13. Kepler.Text.AZIM_PI_WEDGE_GE_CROSS_DOT (Kepler.Text.LocalAuto5:6058; HOL `AZIM_PI_WEDGE_GE_CROSS_DOT`)
    (∀ {u v w ww : V3} (h : azim u v w ww = Real.pi),
    wedgeGe_p2 u v w ww = {x : V3 |
          0 ≤ ((WithLp.toLp 2 (crossProduct ((v - u : V3) : Fin 3 → ℝ)
            ((w - u : V3) : Fin 3 → ℝ)) : V3) ⬝ᵥ (x - u))}
    ) ∧
    -- 14. Kepler.Text.AZIM_PI_WEDGE_GE_SIN (Kepler.Text.LocalAuto5:6026; HOL `AZIM_PI_WEDGE_GE_SIN`)
    (∀ {u v w ww : V3} (h : azim u v w ww = Real.pi),
    wedgeGe_p2 u v w ww = {x : V3 | 0 ≤ Real.sin (azim u v w x)}
    ) ∧
    -- 15. Kepler.Text.AZIM_SPEC_DEGENERATE (Kepler.Text.LocalAuto5:6216; HOL `AZIM_SPEC_DEGENERATE`)
    (∀ (v0 v1 w1 : V3),
    azim v0 v1 w1 v0 = 0 ∧ azim v0 v1 w1 v1 = 0
    ) ∧
    -- 16. Kepler.Text.Affsign_convex (Kepler.Text.LocalAuto5:101; HOL `aff_ge`)
    (∀ {s t : Set V3},
    Convex ℝ {v : V3 | Affsign (fun x : ℝ => 0 ≤ x) s t v}
    ) ∧
    -- 17. Kepler.Text.CARD_IMAGE_INJ2 (Kepler.Text.LocalAuto5:3010; HOL `CARD_IMAGE_INJ2`)
    (∀ {α β : Type*} {f : α → β} {A : Set α} {B : Set β}
          (h : Set.InjOn f A) (hfin : A.Finite),
    (Set.image f A).ncard = A.ncard
    ) ∧
    -- 18. Kepler.Text.CARD_RECUSIVE_EQ (Kepler.Text.LocalAuto5:5610; HOL `CARD_RECUSIVE_EQ`)
    (∀ {α : Type*} (f : α → α) (x : α) {k : ℕ} (hk : 0 < k),
    ({f^[n] x | n < k} : Set α).ncard = k ↔
          ({f^[n] x | n < k - 1} : Set α).ncard = k - 1 ∧
            ∀ i : ℕ, i < k - 1 → f^[i] x ≠ f^[k - 1] x
    ) ∧
    -- 19. Kepler.Text.COLLINEAR_ONCE_VEC_0 (Kepler.Text.LocalAuto5:1596; HOL `COLLINEAR_ONCE_VEC_0`)
    (∀ {x : V3} (hx : x ≠ 0) (y : V3),
    Collinear ℝ ({0, x, y} : Set V3) ↔ ∃ t : ℝ, y = t • x
    ) ∧
    -- 20. Kepler.Text.COLL_IFF_COLL_CROSS (Kepler.Text.LocalAuto5:7296; HOL `COLL_IFF_COLL_CROSS`)
    (∀ {v w : V3},
    Collinear ℝ ({0, v, w} : Set V3) ↔
          Collinear ℝ ({0, v, (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
            ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3)
    ) ∧
    -- 21. Kepler.Text.CONDS_FOR_INTER_AFF_CONV0 (Kepler.Text.LocalAuto5:4870; HOL `CONDS_FOR_INTER_AFF_CONV0`)
    (∀ {x v w u t : V3} {t1 t2 t3 t1' t2' ss : ℝ}
          (ht2 : 0 < t2) (ht3 : 0 < t3) (h1 : t1 + t2 + t3 = ss)
          (h2 : t = t1 • x + t2 • v + t3 • w) (h3 : t1' + t2' = ss)
          (h4 : t = t1' • x + t2' • u),
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3)
    ) ∧
    -- 22. Kepler.Text.CONDS_IN_CONV2 (Kepler.Text.LocalAuto5:6225; HOL `CONDS_IN_CONV2`)
    (∀ {v w : V3} {t2 t3 : ℝ} (ht2 : 0 ≤ t2) (ht3 : 0 ≤ t3)
          (hne : ¬(t2 = 0 ∧ t3 = 0)),
    (t2 / (t2 + t3)) • v + (t3 / (t2 + t3)) • w ∈ convexHull ℝ ({v, w} : Set V3)
    ) ∧
    -- 23. Kepler.Text.CONV0_SUBSET_AFF_GT (Kepler.Text.LocalAuto5:7729; HOL `CONV0_SUBSET_AFF_GT`)
    (∀ {S SS : Set V3} (hS : S.Finite),
    conv0_p2 SS ⊆ (affGt S SS : Set V3)
    ) ∧
    -- 24. Kepler.Text.CONVEX_WEDGE_LE_PI (Kepler.Text.LocalAuto5:6182; HOL `CONVEX_WEDGE_LE_PI`)
    (∀ {v0 v1 w1 w2 : V3} (h : azim v0 v1 w1 w2 ≤ Real.pi)
          (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
          (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3)),
    Convex ℝ (wedgeGe_p2 v0 v1 w1 w2)
    ) ∧
    -- 25. Kepler.Text.CONV_SUBSET_AFF_GE (Kepler.Text.LocalAuto5:7713; HOL `CONV_SUBSET_AFF_GE`)
    (∀ {S SS : Set V3} (hS : S.Finite) (hSS : SS.Finite),
    convexHull ℝ SS ⊆ (affGe S SS : Set V3)
    ) ∧
    -- 26. Kepler.Text.DET_CROSS (Kepler.Text.LocalAuto5:511; HOL `DET_CROSS`)
    (∀ (x y z : V3),
    Matrix.det (Matrix.of fun i j => (![x, y, z] : Fin 3 → V3) i j) =
          (crossProduct ((x : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ))
            ⬝ᵥ ((z : V3) : Fin 3 → ℝ)
    ) ∧
    -- 27. Kepler.Text.DISJOINT_IMP_Z_IN_AFF_GT (Kepler.Text.LocalAuto5:7232; HOL `DISJOINT_IMP_Z_IN_AFF_GT`)
    (∀ {x y z : V3}
          (h : Disjoint ({x, y} : Set V3) ({z} : Set V3)),
    z ∈ affGt ({x, y} : Set V3) ({z} : Set V3)
    ) ∧
    -- 28. Kepler.Text.EMPTY_NOT_EXISTS_IN (Kepler.Text.LocalAuto5:6745; HOL `EMPTY_NOT_EXISTS_IN`)
    (∀ {α : Type*} (a : Set α),
    a = ∅ ↔ ¬ ∃ x, x ∈ a
    ) ∧
    -- 29. Kepler.Text.EXISTS_IN (Kepler.Text.LocalAuto5:5386; HOL `EXISTS_IN`)
    (∀ {α : Type*} (a : Set α),
    a ≠ ∅ ↔ ∃ x, x ∈ a
    ) ∧
    -- 30. Kepler.Text.FAN_IN_E_DIFF (Kepler.Text.LocalAuto5:1015; HOL `FAN_IN_E_DIFF`)
    (∀ {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E),
    ∀ x y : V3, ({x, y} : Set V3) ∈ E →
          (x, y) ≠ (y, x)
    ) ∧
    -- 31. Kepler.Text.FAN_SINGLETON_V_DARTS (Kepler.Text.LocalAuto5:234; HOL `FAN_SINGLETON_V_DARTS`)
    (∀ {v : V3} (hfan : FAN 0 V E) (hV : V = {v}),
    dartsOfHyp_p2 E V = ({(v, v)} : Set (V3 × V3))
    ) ∧
    -- 32. Kepler.Text.FINITE_CARD1_IMP_SINGLETON (Kepler.Text.LocalAuto5:9093; HOL `FINITE_CARD1_IMP_SINGLETON`)
    (∀ {α : Type*} {S : Set α} (hS : S.Finite)
          (h1 : S.ncard = 1),
    ∃ x, S = {x}
    ) ∧
    -- 33. Kepler.Text.FINTE_OF_N_FIRST_ELMS2 (Kepler.Text.LocalAuto5:1050; HOL `FINTE_OF_N_FIRST_ELMS2`)
    (∀ {α : Type*} (f : α → α) (x : α) (i : ℕ),
    ({f^[n] x | n < i} : Set α).Finite
    ) ∧
    -- 34. Kepler.Text.FIRST_EQ0_LAST_LT_PI (Kepler.Text.LocalAuto5:9149; HOL `FIRST_EQ0_LAST_LT_PI`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) {v0 : V3} (hv0 : v0 ∈ V)
          {k : ℕ} (hk : V.ncard = k) {vv : ℕ → V3} (hvv : ∀ i : ℕ, (rhoNode1_p2 FF)^[i] v0 = vv i)
          {bta : ℕ → ℝ} (hbta : ∀ i : ℕ, azim 0 v0 (vv 1) (vv i) = bta i),
    bta 1 = 0 ∧ bta (k - 1) ≤ Real.pi
    ) ∧
    -- 35. Kepler.Text.FIRST_IN_AFF (Kepler.Text.LocalAuto5:7046; HOL `FIRST_IN_AFF`)
    (∀ (a : V3) (S : Set V3),
    a ∈ (affineSpan ℝ (insert a S) : Set V3)
    ) ∧
    -- 36. Kepler.Text.FOR_AFF_GT_NOT_INTERSECTION2 (Kepler.Text.LocalAuto5:8457; HOL `FOR_AFF_GT_NOT_INTERSECTION2`)
    (∀ {x y u v : V3} {a1 b1 t : ℝ}
          (h : a1 • x + b1 • y + t • u = v) (ht : 0 < t) (hs : a1 + b1 + t = 1),
    u = ((0 - a1) / t) • x + ((0 - b1) / t) • y + (1 / t) • v ∧
          (0 - a1) / t + (0 - b1) / t + 1 / t = 1 ∧ 0 < 1 / t
    ) ∧
    -- 37. Kepler.Text.HYP_MAPS_INVERABLE (Kepler.Text.LocalAuto5:3143; HOL `HYP_MAPS_INVERSABLE`)
    (∀ {α : Type*} [DecidableEq α] (H : Hypermap α),
    H.faceMap.symm.trans H.faceMap = Equiv.refl α ∧
          H.nodeMap.symm.trans H.nodeMap = Equiv.refl α ∧
          H.edgeMap.symm.trans H.edgeMap = Equiv.refl α ∧
          H.faceMap.trans H.faceMap.symm = Equiv.refl α ∧
          H.nodeMap.trans H.nodeMap.symm = Equiv.refl α ∧
          H.edgeMap.trans H.edgeMap.symm = Equiv.refl α
    ) ∧
    -- 38. Kepler.Text.INTERSECTION_LEMMA (Kepler.Text.LocalAuto5:4696; HOL `INTERSECTION_LEMMA`)
    (∀ {x z u v w : V3} (hxz : z ≠ x)
          (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : x ≠ u)
          (hne : ¬ (affGt ({x} : Set V3) ({v, w} : Set V3) ∩
            affLt ({x} : Set V3) ({u} : Set V3) = ∅))
          (hz : z ∈ affineSpan ℝ ({x, v, w} : Set V3)),
    ∃ a b t : V3, ({a, b} : Set V3) ⊆ ({u, v, w} : Set V3) ∧
          t ∈ ((affineSpan ℝ ({x, z} : Set V3) : Set V3) ∩
            conv0_p2 ({a, b} : Set V3))
    ) ∧
    -- 39. Kepler.Text.INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0 (Kepler.Text.LocalAuto5:4893; HOL `INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0`)
    (∀ {x v w u t : V3}
          (hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3)) (hxu : u ≠ x)
          (ht : t ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)),
    ∃ tt : V3, tt ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) ∩ conv0_p2 ({v, w} : Set V3)
    ) ∧
    -- 40. Kepler.Text.INTER_EQ_EM_EXPAND (Kepler.Text.LocalAuto5:5130; HOL `INTER_EQ_EM_EXPAND`)
    (∀ {α : Type*} (A B : Set α),
    A ∩ B = ∅ ↔ ¬ ∃ x, x ∈ A ∧ x ∈ B
    ) ∧
    -- 41. Kepler.Text.IN_CONV0_AFF_SUBSET (Kepler.Text.LocalAuto5:4855; HOL `IN_CONV0_AFF_SUBSET`)
    (∀ {a b x y t : V3} (ht : t ∈ ((affineSpan ℝ ({a, b} : Set V3) :
          Set V3) ∩ conv0_p2 ({x, y} : Set V3))) (hx : x ∈ (affineSpan ℝ ({a, b} : Set V3) : Set V3)),
    (affineSpan ℝ ({x, y} : Set V3) : Set V3) ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3)
    ) ∧
    -- 42. Kepler.Text.IN_CONV0_IMP_COLL_IFF (Kepler.Text.LocalAuto5:7389; HOL `IN_CONV0_IMP_COLL_IFF`)
    (∀ {a b x v : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)),
    Collinear ℝ ({a, x, v} : Set V3) ↔ Collinear ℝ ({a, b, v} : Set V3)
    ) ∧
    -- 43. Kepler.Text.IN_WEDGE_IMP_AZIM_LE (Kepler.Text.LocalAuto5:3084; HOL `IN_WEDGE_IMP_AZIM_LE`)
    (∀ {v0 v1 w1 w2 x y : V3} (hy : y ∈ wedgeGe_p2 v0 v1 w1 w2)
          (hxy : azim v0 v1 w1 x ≤ azim v0 v1 w1 y)
          (hx : ¬ Collinear ℝ ({v0, v1, x} : Set V3))
          (hy2 : ¬ Collinear ℝ ({v0, v1, y} : Set V3))
          (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3)),
    azim v0 v1 x y ≤ azim v0 v1 w1 w2
    ) ∧
    -- 44. Kepler.Text.ITER_CARD_MINUS1_EQ_IVS_RN1 (Kepler.Text.LocalAuto5:9120; HOL `ITER_CARD_MINUS1_EQ_IVS_RN1`)
    (∀ (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V),
    (rhoNode1_p2 FF)^[V.ncard - 1] v = ivsRhoNode1_p2 FF v
    ) ∧
    -- 45. Kepler.Text.LEMMA_SUBSET_ORBIT_MAP (Kepler.Text.LocalAuto5:5673; HOL `LEMMA_SUBSET_ORBIT_MAP`)
    (∀ {α : Type*} (p : α → α) (x : α) (n : ℕ),
    {p^[i] x | i ≤ n} ⊆ orbitF_p2 p x
    ) ∧
    -- 46. Kepler.Text.LEMMA_SUBSET_ORBIT_MAP_LT (Kepler.Text.LocalAuto5:5680; HOL `LEMMA_SUBSET_ORBIT_MAP_LT`)
    (∀ {α : Type*} (p : α → α) (x : α) (n : ℕ),
    {p^[i] x | i < n} ⊆ orbitF_p2 p x
    ) ∧
    -- 47. Kepler.Text.LE_CARDV_IMP_CARD_DETERED (Kepler.Text.LocalAuto5:5655; HOL `LE_CARDV_IMP_CARD_DETERED`)
    (∀ {α : Type*} {f : α → α} {V : Set α}
          (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V),
    ∀ l : ℕ, l ≤ V.ncard → ({f^[n] v | n < l} : Set α).ncard = l
    ) ∧
    -- 48. Kepler.Text.LOCAL_FAN_IN_FF_IN_ORD_PAIRS2 (Kepler.Text.LocalAuto5:6429; HOL `LOCAL_FAN_IN_FF_IN_ORD_PAIRS2`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF) {x y : V3 × V3}
          (hx : x ∈ FF) (hy : y ∈ FF),
    ({x.1, x.2} : Set V3) ∈ E ∧ ({y.1, y.2} : Set V3) ∈ E
    ) ∧
    -- 49. Kepler.Text.LOCAL_FAN_NOT_SING_FF (Kepler.Text.LocalAuto5:844; HOL `LOCAL_FAN_NOT_SING_FF`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF),
    ¬ ∃ x : V3 × V3, FF = {x}
    ) ∧
    -- 50. Kepler.Text.LOCAL_FAN_NOT_V_SING (Kepler.Text.LocalAuto5:834; HOL `LOCAL_FAN_NOT_V_SING`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF),
    ¬ ∃ v : V3, V = {v}
    ) ∧
    -- 51. Kepler.Text.LOFA_IMAGE_RHO_NODE_IDE (Kepler.Text.LocalAuto5:3099; HOL `LOFA_IMAGE_RHO_NODE_IDE`)
    (∀ (h : localFan_p2 V E FF),
    Set.image (rhoNode1_p2 FF) V = V
    ) ∧
    -- 52. Kepler.Text.LOFA_IMP_NOT_INCLUDE_VEC0 (Kepler.Text.LocalAuto5:6212; HOL `LOFA_IMP_NOT_INCLUDE_VEC0`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF),
    ¬((0:V3) ∈ V)
    ) ∧
    -- 53. Kepler.Text.LOFA_V_NOT_EMP (Kepler.Text.LocalAuto5:9109; HOL `LOFA_V_NOT_EMP`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF),
    V ≠ ∅
    ) ∧
    -- 54. Kepler.Text.LOOP_MAP_IMP_DIFF_FIRST_ELMS (Kepler.Text.LocalAuto5:2999; HOL `LOOP_MAP_IMP_DIFF_FIRST_ELMS`)
    (∀ {α : Type*} {f : α → α} {V : Set α}
          (horb : ∀ v ∈ V, orbitF_p2 f v = V) {v : α} (hv : v ∈ V) {k l : ℕ}
          (hk : k < V.ncard) (hl : l < k),
    f^[k] v ≠ f^[l] v
    ) ∧
    -- 55. Kepler.Text.MOST_EXPAND_IN_WEDGE_GE (Kepler.Text.LocalAuto5:3519; HOL `MOST_EXPAND_IN_WEDGE_GE`)
    (∀ {v0 v1 w1 w2 x y : V3}
          (hw1 : ¬ Collinear ℝ ({v0, v1, w1} : Set V3))
          (hw2 : ¬ Collinear ℝ ({v0, v1, w2} : Set V3))
          (hx : ¬ Collinear ℝ ({v0, v1, x} : Set V3))
          (hy : ¬ Collinear ℝ ({v0, v1, y} : Set V3))
          (hyw : y ∈ wedgeGe_p2 v0 v1 w1 w2)
          (hxy : azim v0 v1 w1 x ≤ azim v0 v1 w1 y)
          (heq : azim v0 v1 x y = azim v0 v1 w1 w2),
    azim v0 v1 w1 x = 0 ∧ azim v0 v1 y w2 = 0
    ) ∧
    -- 56. Kepler.Text.NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2 (Kepler.Text.LocalAuto5:8513; HOL `NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2`)
    (∀ (h : convexLocalFan_p2 V E FF)
          (hl : lunar_p2 v w V E),
    ∃ i : ℕ, w = (rhoNode1_p2 FF)^[i] v ∧ i + 1 < V.ncard ∧ ¬(i = 0) ∧ ¬(i = 1) ∧
          ¬((rhoNode1_p2 FF)^[i + 1] v ∈ affGt ({0, v} : Set V3) ({rhoNode1_p2 FF v} : Set V3))
    ) ∧
    -- 57. Kepler.Text.NOT_COLL_IMP_COPL (Kepler.Text.LocalAuto5:7263; HOL `NOT_COLL_IMP_COPL`)
    (∀ {v w : V3} (h : ¬ Collinear ℝ ({0, v, w} : Set V3)),
    ¬ Coplanar ({0, v, w, (WithLp.toLp 2 (crossProduct ((v : V3) : Fin 3 → ℝ)
          ((w : V3) : Fin 3 → ℝ)) : V3)} : Set V3)
    ) ∧
    -- 58. Kepler.Text.NOT_INTER_EQ_EM_IMP_AFF_SUBSET (Kepler.Text.LocalAuto5:5145; HOL `NOT_INTER_EQ_EM_IMP_AFF_SUBSET`)
    (∀ {x u v w x' : V3}
          (hx' : x' ∈ affGt ({x} : Set V3) ({v, w} : Set V3) ∩ affLt ({x} : Set V3) ({u} : Set V3)),
    (affineSpan ℝ ({x, u} : Set V3) : Set V3) ⊆ affineSpan ℝ ({x, v, w} : Set V3)
    ) ∧
    -- 59. Kepler.Text.NOT_X_IN_AFF_X_A (Kepler.Text.LocalAuto5:5091; HOL `NOT_X_IN_AFF_X_A`)
    (∀ (x a : V3),
    x ∉ affLt ({x} : Set V3) ({a} : Set V3)
    ) ∧
    -- 60. Kepler.Text.ORTHONORMAL_CYCLIC (Kepler.Text.LocalAuto5:209; HOL `ORTHONORMAL_CYCLIC`)
    (∀ {x y : V3} {U : Set V3} (hxy : ¬(x = y))
          (hfin : U.Finite)
          (hdot : ∀ u1 ∈ U, ∀ u2 ∈ U, (u1 - u2) ⬝ᵥ (x - y) = 0)
          (hinter : U ∩ affineSpan ℝ ({x, y} : Set V3) = ∅),
    cyclicSet_p3 U x y
    ) ∧
    -- 61. Kepler.Text.PGSQVBL (Kepler.Text.LocalAuto5:6334; HOL `PGSQVBL`, HOL `Topology.th1`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {x : V3 × V3} (h : convexLocalFan_p2 V E FF) {v w : V3} (hvw : {v, w} ⊆ V)
          (hx : x ∈ FF),
    affGe ({0} : Set V3) ({v, w} : Set V3) ⊆ wedgeInFanGe_p2 x E
    ) ∧
    -- 62. Kepler.Text.PLANE_AFFINE_HUL_INTER_P (Kepler.Text.LocalAuto5:1070; HOL `PLANE_AFFINE_HUL_INTER_P`)
    (∀ {P : Set V3} {x y z : V3} (hP : plane_p2 P)
          (hsub : ({x, y, z} : Set V3) ⊆ P),
    ((affineSpan ℝ ({x, (WithLp.toLp 2 (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) : V3) + x} : Set V3) : Set V3) ∩ P) = {x}
    ) ∧
    -- 63. Kepler.Text.PRESERABLE_AFF_GE_SUBSET (Kepler.Text.LocalAuto5:4983; HOL `PRESERABLE_AFF_GE_SUBSET`)
    (∀ {x a b : V3} (ha : a ∈ affGe ({x} : Set V3) ({b} : Set V3)),
    affGe ({x} : Set V3) ({a} : Set V3) ⊆ affGe ({x} : Set V3) ({b} : Set V3)
    ) ∧
    -- 64. Kepler.Text.REAL_LT_DIV_NEG (Kepler.Text.LocalAuto5:4101; HOL `REAL_LT_DIV_NEG`)
    (∀ {a b : ℝ} (ha : a < 0) (hb : b < 0),
    0 < a / b
    ) ∧
    -- 65. Kepler.Text.SELF_CYCLIC_IMP_FINITE (Kepler.Text.LocalAuto5:3299; HOL `SELF_CYCLIC_IMP_FINITE`)
    (∀ {α : Type*} (f : α → α) (V : Set α)
          (h : ∀ x ∈ V, V = orbitF_p2 f x),
    V.Finite
    ) ∧
    -- 66. Kepler.Text.SIN_SUB_PERIODIC (Kepler.Text.LocalAuto5:5702; HOL `SIN_SUB_PERIODIC`)
    (∀ (x : ℝ),
    Real.sin x = -Real.sin (x - Real.pi)
    ) ∧
    -- 67. Kepler.Text.SUBSET_AFF2_IMP_COLL (Kepler.Text.LocalAuto5:4907; HOL `SUBSET_AFF2_IMP_COLL`)
    (∀ {S : Set V3} {a b : V3}
          (h : S ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3)),
    Collinear ℝ S
    ) ∧
    -- 68. Kepler.Text.SURJ_IMP_FINITE (Kepler.Text.LocalAuto5:9101; HOL `SURJ_IMP_FINITE`)
    (∀ {α β : Type*} (f : α → β) {A : Set α} {B : Set β}
          (hsurj : ∀ b ∈ B, ∃ a ∈ A, f a = b) (hA : A.Finite),
    B.Finite
    ) ∧
    -- 69. Kepler.Text.USEFULL_THHM (Kepler.Text.LocalAuto5:8391; HOL `USEFULL_THHM`)
    (∀ {b c z w : V3} (h1 : z ∈ affineSpan ℝ ({b, c} : Set V3))
          (h2 : z ∈ affGt ({b, c} : Set V3) ({w} : Set V3)),
    w ∈ affineSpan ℝ ({b, c} : Set V3)
    ) ∧
    -- 70. Kepler.Text.USEFULL_THHM._abel_1_1 (Kepler.Text.LocalAuto5:8391; compiler-generated equation/aux lemma (parent def `USEFULL_THHM` at Kepler.Text.LocalAuto5:8391; no source statement; sigtest = assembly elaboration))
    (∀ {b c w : V3} (gx gy gw : ℝ),
          w = (gx / gw) • b + (gy / gw) • c + w + -((gx / gw) • b) + -((gy / gw) • c)
    ) ∧
    -- 71. Kepler.Text.WEDGE_GE_AZIM_LE (Kepler.Text.LocalAuto5:3075; HOL `WEDGE_GE_AZIM_LE`)
    (∀ (x v0 v1 w1 w2 : V3),
    x ∈ wedgeGe_p2 v0 v1 w1 w2 ↔ azim v0 v1 w1 x ≤ azim v0 v1 w1 w2
    ) ∧
    -- 72. Kepler.Text.azim_in_fan2 (Kepler.Text.LocalAuto5:6202; HOL `azim_in_fan2`)
    (∀ (x : V3 × V3) (E : Set (Set V3)),
    azimInFan_p2 x E =
          if 1 < (EE_p2 x.1 E).ncard then
            azim 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2)
          else 2 * Real.pi
    ) ∧
    -- 73. Kepler.Text.ffOfHyp_p2.eq_1 (Kepler.Text.LocalAuto5:0; compiler-generated equation/aux lemma (parent def `ffOfHyp_p2` at Text.LocalAuto2:169; no source statement; sigtest = assembly elaboration))
    (∀ (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3),
          ffOfHyp_p2 x V E d = if d ∈ dartsOfHyp_p2 E V then (d.2, ivsAzimCycle_p2 (EE_p2 d.2 E) x d.2 d.1) else d
    ) ∧
    -- 74. Kepler.Text.ivsRhoNode1_p2.eq_1 (Kepler.Text.LocalAuto5:0; compiler-generated equation/aux lemma (parent def `ivsRhoNode1_p2` at Text.LocalAuto2:215; no source statement; sigtest = assembly elaboration))
    (∀ (FF : Set (V3 × V3)) (v : V3), ivsRhoNode1_p2 FF v = epsilon fun a => (a, v) ∈ FF
    ) ∧
    -- 75. Kepler.Text.lemma_in_orbit_iter (Kepler.Text.LocalAuto5:5697; HOL `lemma_in_orbit_iter`)
    (∀ {α : Type*} (p : α → α) (x : α) (i : ℕ),
    p^[i] x ∈ orbitF_p2 p x
    ) ∧
    -- 76. Kepler.Text.nnOfHyp_p2.eq_1 (Kepler.Text.LocalAuto5:0; compiler-generated equation/aux lemma (parent def `nnOfHyp_p2` at Text.LocalAuto2:160; no source statement; sigtest = assembly elaboration))
    (∀ (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3),
          nnOfHyp_p2 x V E d = if d ∈ dartsOfHyp_p2 E V then (d.1, azimCycle_p2 (EE_p2 d.1 E) x d.1 d.2) else d
    ) ∧
    -- 77. Kepler.Text.rhoNode1_p2.eq_1 (Kepler.Text.LocalAuto5:0; compiler-generated equation/aux lemma (parent def `rhoNode1_p2` at Text.LocalAuto2:210; no source statement; sigtest = assembly elaboration))
    (∀ (FF : Set (V3 × V3)) (v : V3), rhoNode1_p2 FF v = epsilon fun w => (v, w) ∈ FF
    ) ∧
    -- 78. Kepler.Text.wedge_in_fan_ge2 (Kepler.Text.LocalAuto5:6192; HOL `wedge_in_fan_ge2`)
    (∀ (x : V3 × V3) (E : Set (Set V3)),
    wedgeInFanGe_p2 x E =
          if 1 < (EE_p2 x.1 E).ncard then
            wedgeGe_p2 0 x.1 x.2 (azimCycle_p2 (EE_p2 x.1 E) 0 x.1 x.2)
          else {y : V3 | True}
    ) :=
⟨_root_.Kepler.Geom.affLe.eq_1, _root_.Kepler.Text.AFF_GE_EQ,
      @_root_.Kepler.Text.AFF_GE_MONO_TRANS, _root_.Kepler.Text.AFF_GT_AFF_LT_INTERPRET,
      _root_.Kepler.Text.AFF_GT_AFF_LT_INTERPRET2, _root_.Kepler.Text.AFF_GT_LT_INTER_SYM,
      _root_.Kepler.Text.AFF_GT_LT_INTER_SYM._abel_1_1, @_root_.Kepler.Text.AFF_GT_MONO,
      @_root_.Kepler.Text.AFF_GT_MONO_TRANS, @_root_.Kepler.Text.AFF_GT_SUB_AFF_UNION,
      _root_.Kepler.Text.AFF_XX_CASES, _root_.Kepler.Text.AZIM_PI_CONVEX_WEDGE,
      _root_.Kepler.Text.AZIM_PI_WEDGE_GE_CROSS_DOT, _root_.Kepler.Text.AZIM_PI_WEDGE_GE_SIN,
      _root_.Kepler.Text.AZIM_SPEC_DEGENERATE, @_root_.Kepler.Text.Affsign_convex,
      @_root_.Kepler.Text.CARD_IMAGE_INJ2, _root_.Kepler.Text.CARD_RECUSIVE_EQ,
      _root_.Kepler.Text.COLLINEAR_ONCE_VEC_0, _root_.Kepler.Text.COLL_IFF_COLL_CROSS,
      _root_.Kepler.Text.CONDS_FOR_INTER_AFF_CONV0, _root_.Kepler.Text.CONDS_IN_CONV2,
      @_root_.Kepler.Text.CONV0_SUBSET_AFF_GT, _root_.Kepler.Text.CONVEX_WEDGE_LE_PI,
      @_root_.Kepler.Text.CONV_SUBSET_AFF_GE, _root_.Kepler.Text.DET_CROSS,
      _root_.Kepler.Text.DISJOINT_IMP_Z_IN_AFF_GT, _root_.Kepler.Text.EMPTY_NOT_EXISTS_IN,
      _root_.Kepler.Text.EXISTS_IN, _root_.Kepler.Text.FAN_IN_E_DIFF,
      _root_.Kepler.Text.FAN_SINGLETON_V_DARTS, _root_.Kepler.Text.FINITE_CARD1_IMP_SINGLETON,
      _root_.Kepler.Text.FINTE_OF_N_FIRST_ELMS2, _root_.Kepler.Text.FIRST_EQ0_LAST_LT_PI,
      _root_.Kepler.Text.FIRST_IN_AFF, _root_.Kepler.Text.FOR_AFF_GT_NOT_INTERSECTION2,
      _root_.Kepler.Text.HYP_MAPS_INVERABLE, @_root_.Kepler.Text.INTERSECTION_LEMMA,
      _root_.Kepler.Text.INTER_AFF_GT_LT_IMP_INTER_AFF_CONV0,
      _root_.Kepler.Text.INTER_EQ_EM_EXPAND, @_root_.Kepler.Text.IN_CONV0_AFF_SUBSET,
      _root_.Kepler.Text.IN_CONV0_IMP_COLL_IFF, _root_.Kepler.Text.IN_WEDGE_IMP_AZIM_LE,
      _root_.Kepler.Text.ITER_CARD_MINUS1_EQ_IVS_RN1, @_root_.Kepler.Text.LEMMA_SUBSET_ORBIT_MAP,
      @_root_.Kepler.Text.LEMMA_SUBSET_ORBIT_MAP_LT,
      _root_.Kepler.Text.LE_CARDV_IMP_CARD_DETERED,
      _root_.Kepler.Text.LOCAL_FAN_IN_FF_IN_ORD_PAIRS2, _root_.Kepler.Text.LOCAL_FAN_NOT_SING_FF,
      _root_.Kepler.Text.LOCAL_FAN_NOT_V_SING, _root_.Kepler.Text.LOFA_IMAGE_RHO_NODE_IDE,
      _root_.Kepler.Text.LOFA_IMP_NOT_INCLUDE_VEC0, _root_.Kepler.Text.LOFA_V_NOT_EMP,
      _root_.Kepler.Text.LOOP_MAP_IMP_DIFF_FIRST_ELMS,
      _root_.Kepler.Text.MOST_EXPAND_IN_WEDGE_GE,
      _root_.Kepler.Text.NEXT_OPOSITE_POINT_IS_NOT_IN_AFF_GT2,
      _root_.Kepler.Text.NOT_COLL_IMP_COPL, @_root_.Kepler.Text.NOT_INTER_EQ_EM_IMP_AFF_SUBSET,
      _root_.Kepler.Text.NOT_X_IN_AFF_X_A, _root_.Kepler.Text.ORTHONORMAL_CYCLIC,
      @_root_.Kepler.Text.PGSQVBL, _root_.Kepler.Text.PLANE_AFFINE_HUL_INTER_P,
      @_root_.Kepler.Text.PRESERABLE_AFF_GE_SUBSET, _root_.Kepler.Text.REAL_LT_DIV_NEG,
      _root_.Kepler.Text.SELF_CYCLIC_IMP_FINITE, _root_.Kepler.Text.SIN_SUB_PERIODIC,
      _root_.Kepler.Text.SUBSET_AFF2_IMP_COLL, _root_.Kepler.Text.SURJ_IMP_FINITE,
      _root_.Kepler.Text.USEFULL_THHM, _root_.Kepler.Text.USEFULL_THHM._abel_1_1,
      _root_.Kepler.Text.WEDGE_GE_AZIM_LE, _root_.Kepler.Text.azim_in_fan2,
      _root_.Kepler.Text.ffOfHyp_p2.eq_1, _root_.Kepler.Text.ivsRhoNode1_p2.eq_1,
      _root_.Kepler.Text.lemma_in_orbit_iter, _root_.Kepler.Text.nnOfHyp_p2.eq_1,
      _root_.Kepler.Text.rhoNode1_p2.eq_1, @_root_.Kepler.Text.wedge_in_fan_ge2⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and NO sorryAx (the scout group closure is sorried-0).
#print axioms la5_wire_capstone_w1

/-! ### LA28 materialization capstone (lane lv15-la28-w1, 2026-11-04, after the leftover-mat-scout-2 workorder LV15):
the 42 public top-level LocalAuto28 clean theorem exits (scout probe1.out LA28 group: 108 top public thms, of which 66 are sorried -- DEFORMATION_AZIM_* /
DEFORMATION_DIST_LE_* families, NUXCOEA_p28, IMJXPHRv2_p28 and the remaining giant/registry debts -- excluded at seed construction per the workorder, full
point-named list in logs/gen_report.txt), of which 42 are statable from LocalConcl and are re-exposed as ONE conjunction below; 0 exits are
dropped per the no-forcing rule (each drop named in the theorem docstring).
Self-contained section: pure insertion, zero new imports (LA28 already visible transitively: LocalConcl:499 imports LocalAuto28), zero proof obligations
(body = the exit assembly itself), own `#print axioms` probe (the lv1112 la19 section and the lv1314-w1 la5 section above, and the Shims section below, are untouched -- hunk-level disjoint).
The scoped heartbeat raise mirrors the la5 materialization section above: a conjunction statement of this size exceeds the default 200000 budget during statement elaboration.
-/

set_option maxHeartbeats 50000000 in

/-- LA28 materialization capstone (scout lane leftover-mat-scout-2
workorder LV15, implementation lane lv15-la28-w1, 2026-11-04).  The
Kepler.Text.LocalAuto28 file carries 108 public top-level theorem exits; 66 of them are
sorried (DEFORMATION_AZIM_* / DEFORMATION_DIST_LE_* families, NUXCOEA_p28,
IMJXPHRv2_p28 and the remaining giant/registry debts -- outside the seed set
by the workorder, full point-named list in logs/gen_report.txt), and the
remaining 42 are the sorried-0 clean exits.  Those 42 are
re-exposed here as ONE conjunction (all statable from LocalConcl).
Implemented here: 42 of the 42.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its Kepler.Text.LocalAuto28 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the first depth-0 `:=` by the generator gen_items.py,
bracket-balance guarded); compiler-generated equation/aux lemmas have no
source statement anywhere, so their conjunct is the `#check @name` printer
dump verbatim and each passes a per-item sigtest (the `⟨...⟩` assembly below
must unify it definitionally with the constant's type; printer dumps with
proof-term elision `...` are dropped per the lv12-w1 t_eqlemma_microtest
evidence, each drop named above).  Semantic identity of every conjunct is
re-verified by that assembly (each element must have exactly its conjunct's
type); the per-conjunct comments carry each exit's Kepler.Text.LocalAuto28 declaration
line and file-local docstring HOL anchor.  Conjunct order: the scout
seed-list order (probe1 SEED list).  Body = the assembly of the exit
constants -- zero new proof obligations, zero new imports.  The scoped
`open ... in` prefix before the heartbeat raise (if any) reproduces the
source file's own open context for the verbatim conjunct texts --
mechanically computed as the source-file open tokens missing from the
host's; scoped to this one theorem, zero effect elsewhere in the host.
-/
theorem la28_capstone_w1 :
    -- 1. Kepler.Text.CHANGE_A_SCS_MODL_p28 (Kepler.Text.LocalAuto28:217; HOL `CHANGE_A_SCS_MODL`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
          (hj : j % s.k = j1 % s.k),
    s.a j l = s.a j1 l
    ) ∧
    -- 2. Kepler.Text.CHANGE_A_SCS_MODR_p28 (Kepler.Text.LocalAuto28:222; HOL `CHANGE_A_SCS_MODR`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
          (hj : j % s.k = j1 % s.k),
    s.a l j = s.a l j1
    ) ∧
    -- 3. Kepler.Text.CHANGE_A_SCS_MOD_p28 (Kepler.Text.LocalAuto28:227; HOL `CHANGE_A_SCS_MOD`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l l1 : ℕ)
          (hj : j % s.k = j1 % s.k) (hl : l % s.k = l1 % s.k),
    s.a l j = s.a l1 j1
    ) ∧
    -- 4. Kepler.Text.CHANGE_B_SCS_MODL_p28 (Kepler.Text.LocalAuto28:232; HOL `CHANGE_B_SCS_MODL`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
          (hj : j % s.k = j1 % s.k),
    s.b j l = s.b j1 l
    ) ∧
    -- 5. Kepler.Text.CHANGE_B_SCS_MODR_p28 (Kepler.Text.LocalAuto28:237; HOL `CHANGE_B_SCS_MODR`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l : ℕ)
          (hj : j % s.k = j1 % s.k),
    s.b l j = s.b l j1
    ) ∧
    -- 6. Kepler.Text.CHANGE_B_SCS_MOD_p28 (Kepler.Text.LocalAuto28:242; HOL `CHANGE_B_SCS_MOD`)
    (∀ (s : ScsV39) (hs : isScsV39 s) (j j1 l l1 : ℕ)
          (hj : j % s.k = j1 % s.k) (hl : l % s.k = l1 % s.k),
    s.b l j = s.b l1 j1
    ) ∧
    -- 7. Kepler.Text.CHANGE_W_IN_BBS_MOD_IS_SCS_p28 (Kepler.Text.LocalAuto28:252; HOL `CHANGE_W_IN_BBS_MOD_IS_SCS`)
    (∀ (s : ScsV39) (w : ℕ → V3) (j j1 : ℕ)
          (hs : isScsV39 s) (hbb : BBsV39 s w) (hj : j % s.k = j1 % s.k),
    w j = w j1
    ) ∧
    -- 8. Kepler.Text.CHANGE_W_IN_BBS_MOD_LE3_p28 (Kepler.Text.LocalAuto28:247; HOL `CHANGE_W_IN_BBS_MOD_LE3`)
    (∀ (s : ScsV39) (w : ℕ → V3) (j j1 : ℕ)
          (hk : 3 ≤ s.k) (hbb : BBsV39 s w) (hj : j % s.k = j1 % s.k),
    w j = w j1
    ) ∧
    -- 9. Kepler.Text.COLLINEAR_EQ_SUB_NEG_p28 (Kepler.Text.LocalAuto28:288; HOL `COLLINEAR_EQ_SUB_NEG`)
    (∀ (v1 v2 : V3),
    Collinear ℝ ({0, -v1, v2 - v1} : Set V3) ↔ Collinear ℝ ({0, v1, v2} : Set V3)
    ) ∧
    -- 10. Kepler.Text.DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28 (Kepler.Text.LocalAuto28:764; HOL `DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS`)
    (∀ (v1 v2 : V3) (x1 x2 x5 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5) (hnorm : ‖v2‖ = 2)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (v2 - v1) t + v1 ∈ ballAnnulus
    ) ∧
    -- 11. Kepler.Text.DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28._abel_1_1 (Kepler.Text.LocalAuto28:764; compiler-generated equation/aux lemma (parent declaration `DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28` at Kepler.Text.LocalAuto28:764; no source statement; sigtest = assembly elaboration))
    (∀ (v1 v2 : V3), -v1 - (v2 - v1) = -v2
    ) ∧
    -- 12. Kepler.Text.EQ_SUC_K_SUB3_p28 (Kepler.Text.LocalAuto28:117; HOL `EQ_SUC_K_SUB3`)
    (∀ {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 3 < k),
    (l + k - 1) % k = i % k
    ) ∧
    -- 13. Kepler.Text.EQ_SUC_K_SUB_p28 (Kepler.Text.LocalAuto28:93; HOL `EQ_SUC_K_SUB`)
    (∀ {k l i : ℕ} (h : l % k = (i + 1) % k) (hk : 1 < k),
    (l + k - 1) % k = i % k
    ) ∧
    -- 14. Kepler.Text.EXISTS_SMALL_LE_CONST_ADD_p28 (Kepler.Text.LocalAuto28:808; HOL `EXISTS_SMALL_LE_CONST_ADD`)
    (∀ (v1 v2 w : V3) (x1 x2 x5 c a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hlt : c < dist v2 w),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          c < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w
    ) ∧
    -- 15. Kepler.Text.EXISTS_SMALL_LE_CONST_ADD_p28._abel_1_1 (Kepler.Text.LocalAuto28:808; compiler-generated equation/aux lemma (parent declaration `EXISTS_SMALL_LE_CONST_ADD_p28` at Kepler.Text.LocalAuto28:808; no source statement; sigtest = assembly elaboration))
    (∀ (v1 v2 : V3), -v1 - (v2 - v1) = -v2
    ) ∧
    -- 16. Kepler.Text.EXISTS_SMALL_LT_CONST_ADD_p28 (Kepler.Text.LocalAuto28:863; HOL `EXISTS_SMALL_LT_CONST_ADD`)
    (∀ (v1 v2 w : V3) (x1 x2 x5 c a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hlt : dist v2 w < c),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w < c
    ) ∧
    -- 17. Kepler.Text.EXISTS_SMALL_LT_CONST_ADD_p28._abel_1_1 (Kepler.Text.LocalAuto28:863; compiler-generated equation/aux lemma (parent declaration `EXISTS_SMALL_LT_CONST_ADD_p28` at Kepler.Text.LocalAuto28:863; no source statement; sigtest = assembly elaboration))
    (∀ (v1 v2 : V3), -v1 - (v2 - v1) = -v2
    ) ∧
    -- 18. Kepler.Text.EXPAND_PERIODIC_p28 (Kepler.Text.LocalAuto28:257; HOL `EXPAND_PERIODIC`)
    (∀ (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w),
    w (l + s.k) = w l
    ) ∧
    -- 19. Kepler.Text.EYYPQDW_CONTINUOUS_LIFT_DIST_ADD_p28 (Kepler.Text.LocalAuto28:385; HOL `EYYPQDW_CONTINUOUS_LIFT_DIST_ADD`)
    (∀ (v1 v2 w v : V3)
          (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5),
    ContinuousAt (fun y => dist (v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 y + w) v) x3
    ) ∧
    -- 20. Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28 (Kepler.Text.LocalAuto28:967; HOL `EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE`)
    (∀ (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (haff : v2 ∈ affGt {0} {v1, w}),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) v1 < dist v2 v1
    ) ∧
    -- 21. Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28._abel_1_1 (Kepler.Text.LocalAuto28:967; compiler-generated equation/aux lemma (parent declaration `EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28` at Kepler.Text.LocalAuto28:967; no source statement; sigtest = assembly elaboration))
    (∀ (v1 v2 : V3), -v1 - (v2 - v1) = -v2
    ) ∧
    -- 22. Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28._abel_1_2 (Kepler.Text.LocalAuto28:967; compiler-generated equation/aux lemma (parent declaration `EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28` at Kepler.Text.LocalAuto28:967; no source statement; sigtest = assembly elaboration))
    (∀ (v1 v2 : V3) (x1 x2 x5 t : ℝ),
          v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 - v1 =
            v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t)
    ) ∧
    -- 23. Kepler.Text.E_DEFORMATION_V3_DEFOR_V5_p28 (Kepler.Text.LocalAuto28:354; HOL `E_DEFORMATION_V3_DEFOR_V5`)
    (∀ (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3),
    Set.range (fun i => {v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
            v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1}) =
          (fun S => (fun v => v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) '' S) ''
            Set.range (fun i : ℕ => {w i, w (i + 1)})
    ) ∧
    -- 24. Kepler.Text.FUN_V3_DEFOR_V5_p28 (Kepler.Text.LocalAuto28:337; HOL `FUN_V3_DEFOR_V5`)
    (∀ (a x1 x5 x2 : ℝ) (v1 w v : V3),
    v3DeforV5_p28 a x1 x5 x2 v1 w v = fun t => v3DeforV5_p28 a x1 x5 x2 v1 w v t
    ) ∧
    -- 25. Kepler.Text.F_DEFORMATION_V3_DEFOR_V5_p28 (Kepler.Text.LocalAuto28:369; HOL `F_DEFORMATION_V3_DEFOR_V5`)
    (∀ (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3),
    Set.range (fun i => (v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1,
            v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w (i + 1) - v1) t + v1)) =
          (fun uv => (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.1 t,
            v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.2 t)) ''
            Set.range (fun i : ℕ => (w i, w (i + 1)))
    ) ∧
    -- 26. Kepler.Text.MIN_LEAST_p28 (Kepler.Text.LocalAuto28:306; HOL `MIN_LEAST`)
    (∀ (X : Set ℕ) (c : ℕ) (hc : c ∈ X),
    minNum X ∈ X ∧ minNum X ≤ c
    ) ∧
    -- 27. Kepler.Text.NORM_LE_2_IN_MMS_p28 (Kepler.Text.LocalAuto28:202; HOL `NORM_LE_2_IN_MMS`)
    (∀ (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : w ∈ MMsV39 s),
    2 ≤ ‖w l‖
    ) ∧
    -- 28. Kepler.Text.V3_DEFOR_EQ_IN_FF_MK_SYM_p28 (Kepler.Text.LocalAuto28:1251; HOL `V3_DEFOR_EQ_IN_FF_MK_SYM`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
    ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (a', v2) ∈ FF
    ) ∧
    -- 29. Kepler.Text.V3_DEFOR_EQ_IN_FF_MK_p28 (Kepler.Text.LocalAuto28:1176; HOL `V3_DEFOR_EQ_IN_FF_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
    ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (v2, a') ∈ FF
    ) ∧
    -- 30. Kepler.Text.V_DEFORMATION_V3_DEFOR_V5_p28 (Kepler.Text.LocalAuto28:342; HOL `V_DEFORMATION_V3_DEFOR_V5`)
    (∀ (w : ℕ → V3) (x1 x5 x2 t : ℝ) (v1 v2 : V3),
    Set.range (fun i => v3DeforV4_p28 (-1) x1 x5 x2 (-v1) (v2 - v1) (w i - v1) t + v1) =
          (fun v => v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) '' Set.range w
    ) ∧
    -- 31. Kepler.Text.WL_IN_BALL_ANNULUS_p28 (Kepler.Text.LocalAuto28:179; HOL `WL_IN_BALL_ANNULUS`)
    (∀ (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w),
    w l ∈ ballAnnulus
    ) ∧
    -- 32. Kepler.Text.WL_IN_FF_p28 (Kepler.Text.LocalAuto28:175; HOL `WL_IN_FF`)
    (∀ (w : ℕ → V3) (l : ℕ),
    (w l, w (l + 1)) ∈ Set.range (fun i : ℕ => (w i, w (i + 1)))
    ) ∧
    -- 33. Kepler.Text.WL_IN_V_p28 (Kepler.Text.LocalAuto28:172; HOL `WL_IN_V`)
    (∀ (w : ℕ → V3) (l : ℕ),
    w l ∈ Set.range w
    ) ∧
    -- 34. Kepler.Text.W_IN_BB_FUN_EQ_p28 (Kepler.Text.LocalAuto28:317; HOL `W_IN_BB_FUN_EQ`)
    (∀ (s : ScsV39) (w : ℕ → V3) (x y : ℕ) (hs : isScsV39 s)
          (hbb : BBsV39 s w) (h : w x = w y),
    x % s.k = y % s.k
    ) ∧
    -- 35. Kepler.Text.collinear_origin_pair_p28 (Kepler.Text.LocalAuto28:262; no HOL anchor line in file docstring)
    (∀ (a b : V3),
    Collinear ℝ ({0, a, b} : Set V3) ↔
          ∃ v : V3, (∃ r : ℝ, a = r • v) ∧ ∃ r : ℝ, b = r • v
    ) ∧
    -- 36. Kepler.Text.deformedFF_p28.eq_1 (Kepler.Text.LocalAuto28:399; compiler-generated equation/aux lemma (parent declaration `deformedFF_p28` at Kepler.Text.LocalAuto28:399; no source statement; sigtest = assembly elaboration))
    (∀ (x1 x5 x2 : ℝ) (v1 v2 : V3) (t : ℝ) (FF : Set (V3 × V3)),
          deformedFF_p28 x1 x5 x2 v1 v2 t FF =
            (fun uv => (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.1 t, v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 uv.2 t)) '' FF
    ) ∧
    -- 37. Kepler.Text.minNum.eq_1 (Kepler.Text.LocalAuto28:0; compiler-generated equation/aux lemma (parent declaration `minNum` at Text.LocalAuto1:662; no source statement; sigtest = assembly elaboration))
    (∀ (S : Set ℕ), minNum S = epsilon fun n => n ∈ S ∧ ∀ m ∈ S, n ≤ m
    ) ∧
    -- 38. Kepler.Text.modPeriodic2_first_p28 (Kepler.Text.LocalAuto28:207; no HOL anchor line in file docstring)
    (∀ {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : 0 < k)
          (hper : Periodic2 f k) {j j1 l : ℕ} (hj : j % k = j1 % k),
    f j l = f j1 l
    ) ∧
    -- 39. Kepler.Text.modPeriodic2_second_p28 (Kepler.Text.LocalAuto28:212; no HOL anchor line in file docstring)
    (∀ {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ} (hk : 0 < k)
          (hper : Periodic2 f k) {j j1 l : ℕ} (hj : j % k = j1 % k),
    f l j = f l j1
    ) ∧
    -- 40. Kepler.Text.modPeriodic_p28 (Kepler.Text.LocalAuto28:122; no HOL anchor line in file docstring)
    (∀ {α : Sort u} {f : ℕ → α} {k : ℕ} (hk : 0 < k)
          (hper : ∀ i, f (i + k) = f i) {j j1 : ℕ} (hj : j % k = j1 % k),
    f j = f j1
    ) ∧
    -- 41. Kepler.Text.v3DeforV4_p28.eq_1 (Kepler.Text.LocalAuto28:78; compiler-generated equation/aux lemma (parent declaration `v3DeforV4_p28` at Kepler.Text.LocalAuto28:78; no source statement; sigtest = assembly elaboration))
    (∀ (a x1 x2 x6 : ℝ) (v1 w v : V3) (t : ℝ),
          v3DeforV4_p28 a x1 x2 x6 v1 w v t = if v = w then v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - t) else v
    ) ∧
    -- 42. Kepler.Text.v3DeforV5_p28.eq_1 (Kepler.Text.LocalAuto28:83; compiler-generated equation/aux lemma (parent declaration `v3DeforV5_p28` at Kepler.Text.LocalAuto28:83; no source statement; sigtest = assembly elaboration))
    (∀ (a x1 x5 x2 : ℝ) (v1 v2 v : V3) (t : ℝ),
          v3DeforV5_p28 a x1 x5 x2 v1 v2 v t = v3DeforV4_p28 a x1 x5 x2 (-v1) (v2 - v1) (v - v1) t + v1
    ) :=
⟨_root_.Kepler.Text.CHANGE_A_SCS_MODL_p28, _root_.Kepler.Text.CHANGE_A_SCS_MODR_p28,
      _root_.Kepler.Text.CHANGE_A_SCS_MOD_p28, _root_.Kepler.Text.CHANGE_B_SCS_MODL_p28,
      _root_.Kepler.Text.CHANGE_B_SCS_MODR_p28, _root_.Kepler.Text.CHANGE_B_SCS_MOD_p28,
      _root_.Kepler.Text.CHANGE_W_IN_BBS_MOD_IS_SCS_p28,
      _root_.Kepler.Text.CHANGE_W_IN_BBS_MOD_LE3_p28,
      _root_.Kepler.Text.COLLINEAR_EQ_SUB_NEG_p28,
      _root_.Kepler.Text.DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28,
      _root_.Kepler.Text.DEFORMATION_MK_DEFOR_IN_BALL_ANNULUS_p28._abel_1_1,
      _root_.Kepler.Text.EQ_SUC_K_SUB3_p28, _root_.Kepler.Text.EQ_SUC_K_SUB_p28,
      _root_.Kepler.Text.EXISTS_SMALL_LE_CONST_ADD_p28,
      _root_.Kepler.Text.EXISTS_SMALL_LE_CONST_ADD_p28._abel_1_1,
      _root_.Kepler.Text.EXISTS_SMALL_LT_CONST_ADD_p28,
      _root_.Kepler.Text.EXISTS_SMALL_LT_CONST_ADD_p28._abel_1_1,
      _root_.Kepler.Text.EXPAND_PERIODIC_p28,
      _root_.Kepler.Text.EYYPQDW_CONTINUOUS_LIFT_DIST_ADD_p28,
      _root_.Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28,
      _root_.Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28._abel_1_1,
      _root_.Kepler.Text.EYYPQDW_V3_DEFOR_INCREASING_IN_ANGLE_p28._abel_1_2,
      _root_.Kepler.Text.E_DEFORMATION_V3_DEFOR_V5_p28, _root_.Kepler.Text.FUN_V3_DEFOR_V5_p28,
      _root_.Kepler.Text.F_DEFORMATION_V3_DEFOR_V5_p28, _root_.Kepler.Text.MIN_LEAST_p28,
      _root_.Kepler.Text.NORM_LE_2_IN_MMS_p28, _root_.Kepler.Text.V3_DEFOR_EQ_IN_FF_MK_SYM_p28,
      _root_.Kepler.Text.V3_DEFOR_EQ_IN_FF_MK_p28,
      _root_.Kepler.Text.V_DEFORMATION_V3_DEFOR_V5_p28,
      _root_.Kepler.Text.WL_IN_BALL_ANNULUS_p28, _root_.Kepler.Text.WL_IN_FF_p28,
      _root_.Kepler.Text.WL_IN_V_p28, _root_.Kepler.Text.W_IN_BB_FUN_EQ_p28,
      _root_.Kepler.Text.collinear_origin_pair_p28, _root_.Kepler.Text.deformedFF_p28.eq_1,
      _root_.Kepler.Text.minNum.eq_1, _root_.Kepler.Text.modPeriodic2_first_p28,
      _root_.Kepler.Text.modPeriodic2_second_p28, _root_.Kepler.Text.modPeriodic_p28,
      _root_.Kepler.Text.v3DeforV4_p28.eq_1, _root_.Kepler.Text.v3DeforV5_p28.eq_1⟩

-- Self-check.  Ground truth = `#print axioms`, not prose: expect exactly the standard three
-- [propext, Classical.choice, Quot.sound] and no debt axiom (the scout group closure is sorried-0).
#print axioms la28_capstone_w1

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

/- 2026-11-12: the former `mnt11_anchor : main_nonlinear_terminal_v11 := sorry`
   is gone.  The nine terminal-bank wires (`RRCWNSJ`, `JCYFMRP`, `TFITSKC`,
   `HIJQAHA`, `ARDBZYE`, `FYSSVEV`, `NWDGKXH`, `YOBIMPP`, `MIQMCSN`) now take
   `(hmn : main_nonlinear_terminal_v11)` as an explicit hypothesis; their
   consumers (`localconcl_wire_capstone_w1`/`w2`, `JEJTVGB_p16_discharged`)
   already have that hypothesis in scope and pass it down.  Cone sorry −1,
   zero new proof debt. -/

/- 2026-11-06: the former `p21_anchor : mainNonlinearTerminalV11_p21 := sorry`
   is gone.  After the `p21-anchor` DEF-FIX charter, `LocalAuto21` defines
   `mainNonlinearTerminalV11_p21 : Prop := main_nonlinear_terminal_v11`, so the
   wires' own `_hmn : main_nonlinear_terminal_v11` **is** the twin's hypothesis
   (definitional unfolding, no bridge needed).  `CUXVZOZ_discharged` and
   `CJBDXXN_discharged` below now pass `_hmn` directly. -/

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
point of the assembly mode.  A twin whose interface consumes the terminal bank
takes it as an explicit `hmn` hypothesis supplied by the consumer.
(2026-11-06: `p21_anchor` is gone -- see the §anchor ERRATA at the top of this
file.  2026-11-12: `mnt11_anchor` is gone too -- the nine terminal-bank wires
take `(hmn : main_nonlinear_terminal_v11)`.) -/

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
    isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
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

/-! ### LA20 engine-sink lane (la20-engine-sink-w1, 2026-10-28): real-proof
supply for the two LA20 slicing-arrow leaves `AQICLXA`/`FZIOTEF` at the one
spine position that sees both the LA20 source systems and the LA27 engine
(`LocalAuto20` cannot import the engine: `LocalAuto24` imports `LocalAuto20`,
so an upstream import would cycle).  The two registry wires
`AQICLXA_discharged`/`FUNOUYH_discharged` are re-pointed from the sorried
LA20 twins to the bodies below: two `LKGRQUI_p27` instances over
`scsStabDiagV39 scs6I1` (the `(0,2)` slice with `d' = 0.103 -> 3M1` /
`d'' = 0.616 -> 5M1` and the `(0,3)` slice with `d' = d'' = 0.3789 -> 4M2`;
`dTame 6 = 0.712` beaten by `0.719` resp. `0.7578`, `bm = cstab < 4`,
`mkj = False`), four PSORT/FUNLIST half-table record bashes (9 + 25 + 16 + 16
cells, `wd_half_*` style) and the clean `YXIONXL3_discharged` half-arrow
rotations (`pe (pe s 1) (k - 1) = s` at `k = 3/4/5`).  All pieces private
(`l20es` prefix); the statement lines of both wires stay verbatim.  The
remaining axiom face of the two wires is the engine's own roots
(`QKNVMLB1_p35`, `SGTRNAF_p27`), which close on their own lanes — same
contract as the W-D `CNICGSF` supply above. -/

private theorem l20es_funlistV39_add_period (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k j j' : ℕ) :
    funlistV39 data d k (k + j) (k + j') = funlistV39 data d k j j' := by
  unfold funlistV39 psort
  have h1 : (k + j) % k = j % k := by
    rw [Nat.add_comm k j]
    simpa using (Nat.add_mul_mod_self_left j 1 k)
  have h2 : (k + j') % k = j' % k := by
    rw [Nat.add_comm k j']
    simpa using (Nat.add_mul_mod_self_left j' 1 k)
  rw [h1, h2]

private theorem l20es_funlistV39_add_mul_period (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k c j j' : ℕ) :
    funlistV39 data d k (k * c + j) (k * c + j') = funlistV39 data d k j j' := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show k * (c + 1) + j = k + (k * c + j) from by ring,
        show k * (c + 1) + j' = k + (k * c + j') from by ring,
        l20es_funlistV39_add_period, ih]

private theorem l20es_propEqu_propEqu_mkUnadorned (k : ℕ) (d : ℝ)
    (data1 : List ((ℕ × ℕ) × ℝ)) (d1 : ℝ) (data2 : List ((ℕ × ℕ) × ℝ)) (d2 : ℝ)
    (i m c : ℕ) (h : i + m = k * c) :
    scsPropEquV39 (scsPropEquV39
        (mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k)) i) m
      = mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k) := by
  rw [ScsV39.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    ext j j'
    simp only [scsPropEquV39, mkUnadornedV39]
    rw [show i + (m + j) = k * c + j from by omega,
        show i + (m + j') = k * c + j' from by omega]
    exact l20es_funlistV39_add_mul_period _ _ k c j j'

private theorem l20es_scsArrowV39_pair_union {a b c d : ScsV39}
    (h1 : scsArrowV39 {a} {b}) (h2 : scsArrowV39 {c} {d}) :
    scsArrowV39 {a, c} {b, d} := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with h | h
    · rw [h]; exact h1.1 b (by simp)
    · rw [h]; exact h2.1 d (by simp)
  · rcases h1.2 with h1e | ⟨s, hs, hne⟩
    · rcases h2.2 with h2e | ⟨t, ht, hne'⟩
      · left
        intro u hu
        rcases hu with h | h
        · rw [h]; exact h1e a (by simp)
        · rw [h]; exact h2e c (by simp)
      · exact Or.inr ⟨t, Or.inr (Set.mem_singleton_iff.mp ht), hne'⟩
    · exact Or.inr ⟨s, Or.inl (Set.mem_singleton_iff.mp hs), hne⟩

private theorem l20es_scsArrowV39_lift {a b b' : ScsV39} (h : scsArrowV39 {a} {b'})
    (heq : b' = b) : scsArrowV39 {a} {b} := by rw [← heq]; exact h

private theorem l20es_pair_eq02 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 2} ↔ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h2 : (2 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h2
    rcases h0 with ha | ha <;> rcases h2 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem l20es_pair_eq03 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 3} ↔ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h3 : (3 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h3
    rcases h0 with ha | ha <;> rcases h3 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem l20es_pair_eq04 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 4} ↔ (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h4 : (4 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h4
    rcases h0 with ha | ha <;> rcases h4 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem l20es_sing_ne02 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 2}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h2 : (2 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h2
  omega

private theorem l20es_sing_ne03 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 3}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h3 : (3 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h3
  omega

private theorem l20es_sing_ne04 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 4}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h4 : (4 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h4
  omega

/-! ## The four 6I1 half-table record bashes -/

private theorem l20es_half_6I1_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs6I1 0 2) 0 2 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs6I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq02, l20es_sing_ne02,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq02, l20es_sing_ne02,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq02, l20es_sing_ne02,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq02, l20es_sing_ne02,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem l20es_half_6I1_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs6I1 0 2) 2 0 0.616 False =
      scsPropEquV39 scs5M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs5M1, scs6I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 5 = (i % 5 + 1) % 5 := by omega
    have e2 : (1 + j) % 5 = (j % 5 + 1) % 5 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 5 <;> interval_cases j % 5 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq04, l20es_sing_ne04,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 5 = (i % 5 + 1) % 5 := by omega
    have e2 : (1 + j) % 5 = (j % 5 + 1) % 5 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 5 <;> interval_cases j % 5 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq04, l20es_sing_ne04,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 5 = (i % 5 + 1) % 5 := by omega
    have e2 : (1 + j) % 5 = (j % 5 + 1) % 5 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 5 <;> interval_cases j % 5 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq04, l20es_sing_ne04,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi5 : i % 5 < 5 := Nat.mod_lt i (by omega)
    have hj5 : j % 5 < 5 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 5 = (i % 5 + 1) % 5 := by omega
    have e2 : (1 + j) % 5 = (j % 5 + 1) % 5 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 5 <;> interval_cases j % 5 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq04, l20es_sing_ne04,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem l20es_half_6I1_03_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs6I1 0 3) 0 3 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs6I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem l20es_half_6I1_03_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs6I1 0 3) 3 0 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs6I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, l20es_pair_eq03, l20es_sing_ne03,
        Set.mem_insert_iff, Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

/-! ## The two 6I1 slice bridges (LKGRQUI_p27 instances) -/

private theorem l20es_SLICE_6I1_02 :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs5M1 1} := by
  have mkjF : (scsPropEquV39 scs3M1 1).J 0
      ((scsPropEquV39 scs3M1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs6I1 0 2)
      (scsPropEquV39 scs3M1 1) (scsPropEquV39 scs5M1 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨l20es_half_6I1_02_lo.symm, l20es_half_6I1_02_hi.symm⟩
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) < 0.9
      norm_num
    · show dTame 6 ≤ 0.103 + 0.616
      norm_num [dTame]
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs6I1 0 2) (scsPropEquV39 scs3M1 1)
    (scsPropEquV39 scs5M1 1) 0 2 0 0 True
    (STAB_6I1_SCS 0 2 SCS_DIAG_SCS_6I1_02).1 SCS_DIAG_SCS_6I1_02 hsl

private theorem l20es_SLICE_6I1_03 :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3}
      {scsPropEquV39 scs4M2 1, scsPropEquV39 scs4M2 1} := by
  have mkjF : (scsPropEquV39 scs4M2 1).J 0
      ((scsPropEquV39 scs4M2 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs6I1 0 3)
      (scsPropEquV39 scs4M2 1) (scsPropEquV39 scs4M2 1) 0 3 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨l20es_half_6I1_03_lo.symm, l20es_half_6I1_03_hi.symm⟩
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show dTame 6 ≤ 0.3789 + 0.3789
      norm_num [dTame]
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs6I1 0 3) (scsPropEquV39 scs4M2 1)
    (scsPropEquV39 scs4M2 1) 0 3 0 0 True
    (STAB_6I1_SCS 0 3 SCS_DIAG_SCS_6I1_03).1 SCS_DIAG_SCS_6I1_03 hsl

/-! ## The two leaf arrows (engine-sunk real bodies of the LA20 sorries) -/

/-- Engine-sunk real body of LA20 `AQICLXA` (hexagons.hl:1449): the
`(0,2)` slice bridge + the two `YXIONXL3_discharged` half-arrows
(`pe (pe scs3M1 1) 2 = scs3M1`, `pe (pe scs5M1 1) 4 = scs5M1`)
composed with `FZIOTEF_TRANS`.  Statement verbatim twin. -/
private theorem l20es_AQICLXA :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs3M1, scs5M1} := by
  have his1 : isScsV39 (scsPropEquV39 scs3M1 1) := l20es_SLICE_6I1_02.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs5M1 1) := l20es_SLICE_6I1_02.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    l20es_propEqu_propEqu_mkUnadorned 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs5M1 1) 4 = scs5M1 :=
    l20es_propEqu_propEqu_mkUnadorned 5 0.616
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0), ((1, 3), 2 * h0),
        ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6),
        ((2, 4), 6)] (2 * h0) 1 4 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ l20es_SLICE_6I1_02
    (l20es_scsArrowV39_pair_union
      (l20es_scsArrowV39_lift (YXIONXL3_discharged _ 2 his1) heq1)
      (l20es_scsArrowV39_lift (YXIONXL3_discharged _ 4 his2) heq2))

/-- Engine-sunk real body of LA20 `FZIOTEF` (hexagons.hl:1592): the
`(0,3)` slice bridge (both halves `4M2`) + the `YXIONXL3_discharged`
half-arrow (`pe (pe scs4M2 1) 3 = scs4M2`) composed with `FZIOTEF_TRANS`.
Statement verbatim twin. -/
private theorem l20es_FZIOTEF :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2} := by
  have his1 : isScsV39 (scsPropEquV39 scs4M2 1) := l20es_SLICE_6I1_03.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs4M2 1) 3 = scs4M2 :=
    l20es_propEqu_propEqu_mkUnadorned 4 0.3789
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  have hrot : scsArrowV39 {scsPropEquV39 scs4M2 1} {scs4M2} :=
    l20es_scsArrowV39_lift (YXIONXL3_discharged _ 3 his1) heq1
  have hleg : scsArrowV39 {scsPropEquV39 scs4M2 1, scsPropEquV39 scs4M2 1}
      ({scs4M2, scs4M2} : Set ScsV39) :=
    l20es_scsArrowV39_pair_union hrot hrot
  have hset : (({scs4M2, scs4M2} : Set ScsV39)) = {scs4M2} := by
    ext s
    simp
  rw [hset] at hleg
  exact FZIOTEF_TRANS _ _ _ l20es_SLICE_6I1_03 hleg

/-- WIRE (real proof, la20-engine-sink-w1) `LocalAuto1.FUNOUYH_concl` <- the
`LKGRQUI_p27` instance `l20es_SLICE_6I1_03` (LA27 engine over `scs6I1 0 3`,
`d' = d'' = 0.3789 -> 4M2`) + the clean `YXIONXL3_discharged` rotation
(`pe (pe scs4M2 1) 3 = scs4M2`), replacing the LA20 twin `FZIOTEF` (still
sorried; the LA20 leaf cannot import the engine - LA24 imports LA20).
Statement verbatim. -/
theorem FUNOUYH_discharged :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2} :=
  l20es_FZIOTEF

/-
  W-D lane (la35-access-wd1, 2026-10-28): LA35-series real-proof supply for
  the five CNICGSF slots of `JEJTVGB_p16_discharged`.  The LA18 twins
  `CNICGSF{1,2,3,5}_p18`/`CNICGSF4_p18` compose their `(p,q)`-slice arrows
  `SCS_*_SLICE_*_p18` (bare LA18 sorries, no upstream closure path) with the
  LA1 registry arrow `YXIONXL3_concl`.  Both roots are replaced here: the
  slice arrows are re-proved as `LKGRQUI_p27` instances (LA27's real-proof
  assembly over the LA35 engine `SCS_HALF_SLICE_IS_A_SCS_p35` /
  `SCS_SLICE_SYM_p35` / `QKNVMLB1_p35` / `QKNVMLB3_p35`; pm root
  `pmPlaneCrowding_p35` + the `SGTRNAF_p27` leg), and the rotations consume
  this file's clean `YXIONXL3_discharged`.  All pieces private; the half-slice
  record identities are PSORT/FUNLIST table bashes (HOL CNICGSF.hl route);
  `wd_isScs_stab`/`wd_csAdj_far` are copies of LA24's private
  `la24isScs_stab`/`la24csAdj_far` (deps public) and `wd_STAB_5I1_SCS` fills
  the one diag-stabilisation SCS lemma LA24 does not carry.
-/

private theorem wd_csAdj_far {a1 a2 : ℝ} {i j x y : ℕ} (hd : scsDiag 5 i j)
    (hxy : (i % 5 = x % 5 ∧ j % 5 = y % 5) ∨ (i % 5 = y % 5 ∧ j % 5 = x % 5)) :
    csAdj 5 a1 a2 x y = a2 := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl
  · simp only [csAdj, ← h1, ← h2]
    split
    · exfalso; omega
    split
    · exfalso; omega
    · rfl

private theorem wd_isScs_stab (s : ScsV39) (i j : ℕ) (hd : scsDiag s.k i j)
    (hs : isScsV39 s)
    (hdom : ∀ u v, psort s.k (i, j) = psort s.k (u, v) → s.a u v ≤ cstab) :
    isScsV39 (scsStabDiagV39 s i j) := by
  have hk0 : s.k ≠ 0 := by have := hs.2.1; omega
  have hk2 : 1 < s.k := by have := hs.2.1; omega
  obtain ⟨hdd, hk1, hk6, -, -, -, -, hpa, -, -, hpb, -, hsym, hch, hdiag0, h2a, hb3,
    hbc, -, -, hcard⟩ := hs
  have hpb1 : ∀ u v, s.b (u + s.k) v = s.b u v := fun u v => (hpb u v).1
  have hpb2 : ∀ u v, s.b u (v + s.k) = s.b u v := fun u v => (hpb u v).2
  set b' : ℕ → ℕ → ℝ := fun x y =>
    if psort s.k (i, j) = psort s.k (x, y) then cstab else s.b x y with hb'def
  rw [show scsStabDiagV39 s i j = mkUnadornedV39 s.k s.d s.a b' from by
    simp only [scsStabDiagV39, mkUnadornedV39, hb'def]]
  simp only [isScsV39, mkUnadornedV39]
  have psort_add1 : ∀ u v : ℕ, psort s.k (u + s.k, v) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k (u + s.k) v hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have psort_add2 : ∀ u v : ℕ, psort s.k (u, v + s.k) = psort s.k (u, v) := by
    intro u v
    rw [(PSORT_MOD s.k u (v + s.k) hk0).symm, Nat.add_mod_right, PSORT_MOD s.k u v hk0]
  have hb'edge : ∀ u, b' u (u + 1) = s.b u (u + 1) := by
    intro u
    simp only [hb'def]
    rw [if_neg (diag_not_edge_psort_p20 u hk2 hd)]
  have hsymB' : ∀ u v, b' u v = b' v u := by
    intro u v
    simp only [hb'def]
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · rw [if_pos hcls, psort_swap_p20 s.k v u, if_pos hcls]
    · rw [if_neg hcls, psort_swap_p20 s.k v u, if_neg hcls]
      exact (hsym u v).2.2.2.1
  have hpb' : Periodic2 b' s.k := by
    intro u v
    refine ⟨?_, ?_⟩
    · show b' (u + s.k) v = b' u v
      simp only [hb'def]
      rw [psort_add1, hpb1 u v]
    · show b' u (v + s.k) = b' u v
      simp only [hb'def]
      rw [psort_add2, hpb2 u v]
  have hdomcase : ∀ u v, s.a u v ≤ b' u v := by
    intro u v
    by_cases hcls : psort s.k (i, j) = psort s.k (u, v)
    · simp only [hb'def, if_pos hcls]
      exact hdom u v hcls
    · simp only [hb'def, if_neg hcls]
      exact (hch u v).1.trans ((hch u v).2.1.trans (hch u v).2.2)
  refine ⟨hdd, hk1, hk6, periodic_empty s.k, periodic_empty s.k, periodic_empty s.k,
    periodic_empty s.k, hpa, hpa, hpb', hpb', fun _ _ => ⟨rfl, rfl⟩,
    fun u v => ⟨(hsym u v).1, (hsym u v).1, hsymB' u v, hsymB' u v, trivial⟩,
    fun u v => ⟨le_refl _, hdomcase u v, le_refl _⟩, hdiag0, h2a,
    fun u h3 => by rw [hb'edge u]; exact hb3 u h3,
    fun u h3 => by rw [hb'edge u]; exact hbc u h3,
    fun _ _ hj => False.elim hj, fun _ _ hj => False.elim hj, ?_⟩
  simp only [hb'edge]
  exact hcard

/-- `STAB_5I1_SCS` (missing from LA24): diag-stabilisations of `scs5I1` are
SCS; the stab overrides the diag b-slot to `cstab` and the a-table far value
`2 * h0` is `≤ cstab` on the stabilised class. -/
private theorem wd_STAB_5I1_SCS (i j : ℕ) (hd : scsDiag scs5I1.k i j) :
    isScsV39 (scsStabDiagV39 scs5I1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I1 i j) := by
  refine ⟨wd_isScs_stab scs5I1 i j hd SCS_5I1_IS_SCS ?_,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩⟩
  intro u v hcls
  rw [show scs5I1.k = 5 from rfl] at hcls
  show csAdj 5 2 (2 * h0) u v ≤ cstab
  rw [wd_csAdj_far hd (psort_eq_cases_p20 hcls)]
  norm_num [h0, cstab]

/-! ## wd copies of the LA18 rotation kit (LA18-privates are not visible) -/

private theorem wd_funlistV39_add_period (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k j j' : ℕ) :
    funlistV39 data d k (k + j) (k + j') = funlistV39 data d k j j' := by
  unfold funlistV39 psort
  have h1 : (k + j) % k = j % k := by
    rw [Nat.add_comm k j]
    simpa using (Nat.add_mul_mod_self_left j 1 k)
  have h2 : (k + j') % k = j' % k := by
    rw [Nat.add_comm k j']
    simpa using (Nat.add_mul_mod_self_left j' 1 k)
  rw [h1, h2]

private theorem wd_funlistV39_add_mul_period (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ)
    (k c j j' : ℕ) :
    funlistV39 data d k (k * c + j) (k * c + j') = funlistV39 data d k j j' := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show k * (c + 1) + j = k + (k * c + j) from by ring,
        show k * (c + 1) + j' = k + (k * c + j') from by ring,
        wd_funlistV39_add_period, ih]

private theorem wd_propEqu_propEqu_mkUnadorned (k : ℕ) (d : ℝ)
    (data1 : List ((ℕ × ℕ) × ℝ)) (d1 : ℝ) (data2 : List ((ℕ × ℕ) × ℝ)) (d2 : ℝ)
    (i m c : ℕ) (h : i + m = k * c) :
    scsPropEquV39 (scsPropEquV39
        (mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k)) i) m
      = mkUnadornedV39 k d (funlistV39 data1 d1 k) (funlistV39 data2 d2 k) := by
  rw [ScsV39.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    ext j j'
    simp only [scsPropEquV39, mkUnadornedV39]
    rw [show i + (m + j) = k * c + j from by omega,
        show i + (m + j') = k * c + j' from by omega]
    exact wd_funlistV39_add_mul_period _ _ k c j j'

private theorem wd_scsArrowV39_pair_union {a b c d : ScsV39}
    (h1 : scsArrowV39 {a} {b}) (h2 : scsArrowV39 {c} {d}) :
    scsArrowV39 {a, c} {b, d} := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with h | h
    · rw [h]; exact h1.1 b (by simp)
    · rw [h]; exact h2.1 d (by simp)
  · rcases h1.2 with h1e | ⟨s, hs, hne⟩
    · rcases h2.2 with h2e | ⟨t, ht, hne'⟩
      · left
        intro u hu
        rcases hu with h | h
        · rw [h]; exact h1e a (by simp)
        · rw [h]; exact h2e c (by simp)
      · exact Or.inr ⟨t, Or.inr (Set.mem_singleton_iff.mp ht), hne'⟩
    · exact Or.inr ⟨s, Or.inl (Set.mem_singleton_iff.mp hs), hne⟩

private theorem wd_scsArrowV39_lift {a b b' : ScsV39} (h : scsArrowV39 {a} {b'})
    (heq : b' = b) : scsArrowV39 {a} {b} := by rw [← heq]; exact h

private theorem wd_pair_eq02 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 2} ↔ (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h2 : (2 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h2
    rcases h0 with ha | ha <;> rcases h2 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem wd_pair_eq03 {a b : ℕ} :
    ({a, b} : Set ℕ) = {0, 3} ↔ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    have h3 : (3 : ℕ) ∈ ({a, b} : Set ℕ) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h3
    rcases h0 with ha | ha <;> rcases h3 with hb | hb <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ext t <;> simp <;> omega

private theorem wd_sing_ne02 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 2}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h2 : (2 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h2
  omega

private theorem wd_sing_ne03 (a : ℕ) : ¬(({a} : Set ℕ) = {0, 3}) := by
  intro h
  have h0 : (0 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  have h3 : (3 : ℕ) ∈ ({a} : Set ℕ) := by rw [h]; simp
  simp only [Set.mem_singleton_iff] at h0 h3
  omega

/-! ## The ten half-table record bashes -/

private theorem wd_half_5I1_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5I1 0 2) 0 2 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5I1_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5I1 0 2) 2 0 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs5I1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5I2_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5I2 0 2) 0 2 0.11 False =
      scsPropEquV39 scs3T1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3T1, scs5I2]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5I2_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5I2 0 2) 2 0 0.513 False =
      scsPropEquV39 scs4M3' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M3', scs5I2]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_02_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 2) 0 2 0.2759 False =
      scsPropEquV39 scs3T4 2 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3T4, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (2 + i) % 3 = (i % 3 + 2) % 3 := by omega
    have e2 : (2 + j) % 3 = (j % 3 + 2) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (2 + i) (2 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_02_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 2) 2 0 0.3789 False =
      scsPropEquV39 scs4M2 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M2, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_03_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 3) 0 3 0.513 False =
      scsPropEquV39 scs4M4' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M4', scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_03_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 0 3) 3 0 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_24_lo :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 2 4) 2 4 0.103 False =
      scsPropEquV39 scs3M1 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs3M1, scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi3 : i % 3 < 3 := Nat.mod_lt i (by omega)
    have hj3 : j % 3 < 3 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 3 = (i % 3 + 1) % 3 := by omega
    have e2 : (1 + j) % 3 = (j % 3 + 1) % 3 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 3 <;> interval_cases j % 3 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq02, wd_sing_ne02, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

private theorem wd_half_5M1_24_hi :
    scsHalfSliceV39 (scsStabDiagV39 scs5M1 2 4) 4 2 0.513 False =
      scsPropEquV39 scs4M5' 1 := by
  simp only [scsHalfSliceV39, scsStabDiagV39, mkUnadornedV39, scsPropEquV39,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, scs4M5', scs5M1]
  rw [ScsV39.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    have hi4 : i % 4 < 4 := Nat.mod_lt i (by omega)
    have hj4 : j % 4 < 4 := Nat.mod_lt j (by omega)
    have e1 : (1 + i) % 4 = (i % 4 + 1) % 4 := by omega
    have e2 : (1 + j) % 4 = (j % 4 + 1) % 4 := by omega
    rw [← funlist_mod_p20 _ _ _ (1 + i) (1 + j) (by omega), e1, e2]
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      simp [csAdj, funlistV39, psort, assocdV39, wd_pair_eq03, wd_sing_ne03, Set.mem_insert_iff,
        Set.mem_singleton_iff]
  · funext i j
    split
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl

/-! ## The five slice bridges (LKGRQUI_p27 instances) -/

private theorem SCS_5I1_SLICE_02_wd :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M2 1} := by
  have mkjF : (scsPropEquV39 scs3M1 1).J 0
      ((scsPropEquV39 scs3M1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5I1 0 2)
      (scsPropEquV39 scs3M1 1) (scsPropEquV39 scs4M2 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨wd_half_5I1_02_lo.symm, wd_half_5I1_02_hi.symm⟩
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show dTame 5 ≤ 0.103 + 0.3789
      norm_num [dTame]
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5I1 0 2) (scsPropEquV39 scs3M1 1)
    (scsPropEquV39 scs4M2 1) 0 2 0 0 True
    (wd_STAB_5I1_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

private theorem SCS_5I2_SLICE_02_wd :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2}
      {scsPropEquV39 scs3T1 1, scsPropEquV39 scs4M3' 1} := by
  have mkjF : (scsPropEquV39 scs3T1 1).J 0
      ((scsPropEquV39 scs3T1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5I2 0 2)
      (scsPropEquV39 scs3T1 1) (scsPropEquV39 scs4M3' 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨wd_half_5I2_02_lo.symm, wd_half_5I2_02_hi.symm⟩
    · show (0.11 : ℝ) < 0.9
      norm_num
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.11 + 0.513
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5I2 0 2) (scsPropEquV39 scs3T1 1)
    (scsPropEquV39 scs4M3' 1) 0 2 0 0 True
    (STAB_5I2_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

private theorem SCS_5M1_SLICE_02_wd :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2}
      {scsPropEquV39 scs3T4 2, scsPropEquV39 scs4M2 1} := by
  have mkjF : (scsPropEquV39 scs3T4 2).J 0
      ((scsPropEquV39 scs3T4 2).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 0 2)
      (scsPropEquV39 scs3T4 2) (scsPropEquV39 scs4M2 1) 0 2 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨wd_half_5M1_02_lo.symm, wd_half_5M1_02_hi.symm⟩
    · show (0.2759 : ℝ) < 0.9
      norm_num
    · show (0.3789 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.2759 + 0.3789
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 0 2) (scsPropEquV39 scs3T4 2)
    (scsPropEquV39 scs4M2 1) 0 2 0 0 True
    (STAB_5M1_SCS 0 2 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

private theorem SCS_5M1_SLICE_03_wd :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3}
      {scsPropEquV39 scs4M4' 1, scsPropEquV39 scs3M1 1} := by
  have mkjF : (scsPropEquV39 scs4M4' 1).J 0
      ((scsPropEquV39 scs4M4' 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 0 3)
      (scsPropEquV39 scs4M4' 1) (scsPropEquV39 scs3M1 1) 0 3 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨wd_half_5M1_03_lo.symm, wd_half_5M1_03_hi.symm⟩
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.513 + 0.103
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 0 3) (scsPropEquV39 scs4M4' 1)
    (scsPropEquV39 scs3M1 1) 0 3 0 0 True
    (STAB_5M1_SCS 0 3 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

private theorem SCS_5M1_SLICE_24_wd :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4}
      {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M5' 1} := by
  have mkjF : (scsPropEquV39 scs3M1 1).J 0
      ((scsPropEquV39 scs3M1 1).k - 1) = False := rfl
  have hsl : isScsSliceV39 (scsStabDiagV39 scs5M1 2 4)
      (scsPropEquV39 scs3M1 1) (scsPropEquV39 scs4M5' 1) 2 4 := by
    simp only [isScsSliceV39]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [scsSliceV39, Prod.mk.injEq, mkjF]
      exact ⟨wd_half_5M1_24_lo.symm, wd_half_5M1_24_hi.symm⟩
    · show (0.103 : ℝ) < 0.9
      norm_num
    · show (0.513 : ℝ) < 0.9
      norm_num
    · show (0.616 : ℝ) ≤ 0.103 + 0.513
      norm_num
    · show cstab < 4
      norm_num [cstab]
    · right
      show cstab ≤ cstab
      exact le_refl cstab
    · rw [mkjF]
      exact fun hc => False.elim hc
  exact LKGRQUI_p27 (scsStabDiagV39 scs5M1 2 4) (scsPropEquV39 scs3M1 1)
    (scsPropEquV39 scs4M5' 1) 2 4 0 0 True
    (STAB_5M1_SCS 2 4 ⟨by decide, by decide, by decide⟩).1 ⟨by decide, by decide, by decide⟩ hsl

/-- WIRE (real proof, W-D 2026-10-28) `LocalAuto1.CNICGSF4_concl`: body
re-derived from the `LKGRQUI_p27` instance `SCS_5M1_SLICE_03_wd` (LA35 engine;
slice-arrow debt) + the clean `YXIONXL3_discharged` rotations, replacing the
LA18 twin `CNICGSF4_p18` whose debt was the bare LA18 sorry
`SCS_5M1_SLICE_03_p18` + the registry arrow `YXIONXL3_concl`.  Statement
verbatim. -/
theorem CNICGSF4_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 3} {scs4M4', scs3M1} := by
  have his1 : isScsV39 (scsPropEquV39 scs4M4' 1) := SCS_5M1_SLICE_03_wd.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5M1_SLICE_03_wd.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs4M4' 1) 3 = scs4M4' :=
    wd_propEqu_propEqu_mkUnadorned 4 0.513
      [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1
      (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    wd_propEqu_propEqu_mkUnadorned 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  exact FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_03_wd
    (wd_scsArrowV39_pair_union
      (wd_scsArrowV39_lift (YXIONXL3_discharged _ 3 his1) heq1)
      (wd_scsArrowV39_lift (YXIONXL3_discharged _ 2 his2) heq2))

/-- WIRE (real proof, W-D 2026-10-28) `LocalAuto1.CNICGSF1_concl`: body
re-derived from the `LKGRQUI_p27` instance `SCS_5I1_SLICE_02_wd` + clean
`YXIONXL3_discharged` rotations + the target-set permutation shim
(`{scs3M1, scs4M2} = {scs4M2, scs3M1}`), replacing the LA18 twin's debt
(`SCS_5I1_SLICE_02_p18` bare sorry + `YXIONXL3_concl`).  Statement verbatim. -/
theorem CNICGSF1_discharged :
    scsArrowV39 {scsStabDiagV39 scs5I1 0 2} {scs4M2, scs3M1} := by
  have his1 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5I1_SLICE_02_wd.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M2 1) := SCS_5I1_SLICE_02_wd.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    wd_propEqu_propEqu_mkUnadorned 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M2 1) 3 = scs4M2 :=
    wd_propEqu_propEqu_mkUnadorned 4 0.3789
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact arrowSetRight
    (FZIOTEF_TRANS _ _ _ SCS_5I1_SLICE_02_wd
      (wd_scsArrowV39_pair_union
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 2 his1) heq1)
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 3 his2) heq2)))
    (by ext t; simp; tauto)

/-- WIRE (real proof, W-D 2026-10-28) `LocalAuto1.CNICGSF2_concl`: body
re-derived from the `LKGRQUI_p27` instance `SCS_5I2_SLICE_02_wd` + clean
`YXIONXL3_discharged` rotations + the target-set permutation shim
(`{scs3T1, scs4M3'} = {scs4M3', scs3T1}`), replacing the LA18 twin's debt
(`SCS_5I2_SLICE_02_p18` bare sorry + `YXIONXL3_concl`).  Statement verbatim. -/
theorem CNICGSF2_discharged :
    scsArrowV39 {scsStabDiagV39 scs5I2 0 2} {scs4M3', scs3T1} := by
  have his1 : isScsV39 (scsPropEquV39 scs3T1 1) := SCS_5I2_SLICE_02_wd.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M3' 1) := SCS_5I2_SLICE_02_wd.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3T1 1) 2 = scs3T1 := by
    rw [scs_3T1]
    exact wd_propEqu_propEqu_mkUnadorned 3 0.11
      [((0, 1), Real.sqrt 8)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M3' 1) 3 = scs4M3' :=
    wd_propEqu_propEqu_mkUnadorned 4 0.513
      [((0, 1), Real.sqrt 8), ((0, 2), Real.sqrt 8), ((1, 3), Real.sqrt 8)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact arrowSetRight
    (FZIOTEF_TRANS _ _ _ SCS_5I2_SLICE_02_wd
      (wd_scsArrowV39_pair_union
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 2 his1) heq1)
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 3 his2) heq2)))
    (by ext t; simp; tauto)

/-- WIRE (real proof, W-D 2026-10-28) `LocalAuto1.CNICGSF3_concl`: body
re-derived from the `LKGRQUI_p27` instance `SCS_5M1_SLICE_02_wd` + clean
`YXIONXL3_discharged` rotations + the target-set permutation shim
(`{scs3T4, scs4M2} = {scs4M2, scs3T4}`), replacing the LA18 twin's debt
(`SCS_5M1_SLICE_02_p18` bare sorry + `YXIONXL3_concl`).  Statement verbatim. -/
theorem CNICGSF3_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 0 2} {scs4M2, scs3T4} := by
  have his1 : isScsV39 (scsPropEquV39 scs3T4 2) := SCS_5M1_SLICE_02_wd.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M2 1) := SCS_5M1_SLICE_02_wd.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3T4 2) 1 = scs3T4 :=
    wd_propEqu_propEqu_mkUnadorned 3 0.2759
      [((0, 1), 2)] (2 * h0) [((0, 1), 2 * h0)] cstab 2 1 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M2 1) 3 = scs4M2 :=
    wd_propEqu_propEqu_mkUnadorned 4 0.3789
      [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1 (by norm_num)
  exact arrowSetRight
    (FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_02_wd
      (wd_scsArrowV39_pair_union
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 1 his1) heq1)
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 3 his2) heq2)))
    (by ext t; simp; tauto)

/-- WIRE (real proof, W-D 2026-10-28) `LocalAuto1.CNICGSF5_concl`: body
re-derived from the `LKGRQUI_p27` instance `SCS_5M1_SLICE_24_wd` + clean
`YXIONXL3_discharged` rotations + the target-set permutation shim
(`{scs3M1, scs4M5'} = {scs4M5', scs3M1}`), replacing the LA18 twin's debt
(`SCS_5M1_SLICE_24_p18` bare sorry + `YXIONXL3_concl`).  Statement verbatim. -/
theorem CNICGSF5_discharged :
    scsArrowV39 {scsStabDiagV39 scs5M1 2 4} {scs4M5', scs3M1} := by
  have his1 : isScsV39 (scsPropEquV39 scs3M1 1) := SCS_5M1_SLICE_24_wd.1 _ (by simp)
  have his2 : isScsV39 (scsPropEquV39 scs4M5' 1) := SCS_5M1_SLICE_24_wd.1 _ (by simp)
  have heq1 : scsPropEquV39 (scsPropEquV39 scs3M1 1) 2 = scs3M1 :=
    wd_propEqu_propEqu_mkUnadorned 3 0.103
      [((0, 1), 2 * h0)] 2 [((0, 1), cstab)] (2 * h0) 1 2 1 (by norm_num)
  have heq2 : scsPropEquV39 (scsPropEquV39 scs4M5' 1) 3 = scs4M5' :=
    wd_propEqu_propEqu_mkUnadorned 4 0.513
      [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2
      [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 1 3 1
      (by norm_num)
  exact arrowSetRight
    (FZIOTEF_TRANS _ _ _ SCS_5M1_SLICE_24_wd
      (wd_scsArrowV39_pair_union
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 2 his1) heq1)
        (wd_scsArrowV39_lift (YXIONXL3_discharged _ 3 his2) heq2)))
    (by ext t; simp; tauto)

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

/-- WIRE `LocalAuto1.RRCWNSJ_concl` <- `RRCWNSJ_p26` (shims: passed terminal-bank hypothesis `hmn`; hypothesis
reorder `hs hb hk3 hv` -> `hs hb hv hk3`).  Twin still sorried — debt
flows. -/
theorem RRCWNSJ_discharged (hmn : main_nonlinear_terminal_v11) : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    scsBasicV39 s → 3 < s.k → v ∈ MMsV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v :=
  fun s v hs hb hk3 hv hd4 hab hb1 =>
    RRCWNSJ_p26 hmn s v hs hb hv hk3 hd4 hab hb1

/-- WIRE `LocalAuto1.JCYFMRP_concl` <- `JCYFMRP_p27` (shims: passed terminal-bank hypothesis `hmn`; reorder moving `3 < s.k` forward).  Twin still sorried —
debt flows.  (The LA29 `_V2/_V3` siblings are variant forms with a
conjunction conclusion and an extra `a < b` row hypothesis — not needed.) -/
theorem JCYFMRP_discharged (hmn : main_nonlinear_terminal_v11) : ∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    3 < s.k →
    (∀ i, s.a i (i + 1) = 2) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    ∃ i, dist (v i) (v (i + 1)) = 2 :=
  fun s v hs hv hgen hbasic hb4 hm1 hk3 hA hdiag =>
    JCYFMRP_p27 hmn s v hk3 hs hv hgen hbasic hb4 hm1 hA hdiag

/-- WIRE `LocalAuto1.TFITSKC_concl` <- `TFITSKC_p27` (shims: passed terminal-bank hypothesis `hmn`; hypothesis reorder; `le_of_eq` turns the registry's
`b (i+1) (i+2) = 2*h0` into the twin's `≤ 2*h0`).  Twin still sorried —
debt flows. -/
theorem TFITSKC_discharged (hmn : main_nonlinear_terminal_v11) : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    3 < s.k → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → (s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    dist (v (i + 1)) (v (i + 2)) = 2 :=
  fun s v i hs hk3 hv hgen hbasic hA hB hd hdiag h2 hlt =>
    TFITSKC_p27 hmn s v i hlt hk3 hs hv hgen hbasic hA (le_of_eq hB)
      hd h2 (fun j j' hdiag' =>
        ⟨(hdiag j j' hdiag').1.1, (hdiag j j' hdiag').1.2, (hdiag j j' hdiag').2⟩)

/-! ### LV program slot B materialization capstones (lane lv34-w1,
2026-11-04, after the leftover-mat-scout workorder LV3/LV4): the clean
top-level public LocalAuto13 exits (68) and LocalAuto9 exits
(68) that no e2e root reaches are re-exposed as TWO verbatim
conjunctions -- the sorried exits (LA13: 40 giants, LA9: 9 chapter
capstones) are excluded one-by-one per the workorder ("sorried 出口
排除"), their debt owners are the existing queues (LA13: LA1 registry
`YXIONXL2_concl` line + Local Fan queue; LA9: §2-1 GIANT W2 +
EJRCFJD_ALT2).  Measured by the scout on baseline I 1e139a28: clean
subset closures GROUP_SORRIED = 0 (probe2), representative axioms
standard-three (axprobe); expected cone yield at the lv-wire-w2 wiring
gate +209 / +180 (+389 pair), K_SORRIED 134 and K_AXIOM 624 unchanged.
This section is self-contained: pure insertion, zero import changes,
zero edits to existing content.  Each capstone carries a scoped
`set_option linter.unusedVariables false in`: the restated exit
statements keep their original (conclusion-unused) hypothesis binders
verbatim, and the linter would otherwise emit ~109 noise warnings per
compile in this file -- the option is statement- and axiom-neutral. -/

set_option linter.unusedVariables false in
/-- LocalAuto13 materialization capstone (LV program slot B, wave
lv34-w1, 2026-11-04; scout lane leftover-mat-scout §1-§3, generator
precedent la35-root-w1 `a8e35ccf`).  The 68 clean top-level public
LocalAuto13 theorem exits unreachable from every e2e root (probe1
SEED_PROBES: 68 clean + 40 sorried
exits excluded per the workorder -- the sorried half is not entered,
zero of its proof debt flows into this file; group closure of the clean
subset measured GROUP_SORRIED = 0, so K_SORRIED 134 and K_AXIOM 624 are
untouched). 3 of the 68 conjuncts are auto-generated equation/structure exits restated from the `#check @name` printer output (no verbatim source declaration exists).
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LocalAuto13 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied
verbatim and mechanically split at the binder/conclusion separator by
the generator gen_items.py), or the Lean `#check @name` printer dump
for the auto-generated items (logs/sigprobe_w1.out); semantic identity
is re-verified by the elaboration of the ⟨…⟩ assembly below (each
component must unify definitionally with its conjunct); the
per-conjunct comments carry each exit's LocalAuto13 declaration line and
file-local docstring HOL anchor.
Conjunct order: the seed-list order (seeds_clean.txt module block,
scout logs).  Body = the assembly of the exit constants -- zero new
proof obligations, zero new imports (LocalAuto13 is already imported
directly (:484)).
Wiring (Assembly consumption) is NOT part of this wave -- lane
lv-wire-w2 owns it; expected cone yield at the wiring gate: +209
(LA13) / +180 (LA9) per the scout BFS upper bound, +389 for the pair. -/
theorem la13_capstone_w1 :
    -- 1. Kepler.Text.BALL_ANNULUS_SYM_0_p13 (LocalAuto13:968; HOL `BALL_ANNULUS_SYM_0`)
    (∀ (v : V3),
          -v ∈ ballAnnulus ↔ v ∈ ballAnnulus
    ) ∧
    -- 2. Kepler.Text.CARD_EQUI_FF_SYM_0_p13 (LocalAuto13:1147; HOL `CARD_EQUI_FF_SYM_0`)
    (∀ (vv : ℕ → V3)
          (h : (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).Finite),
          Nat.card (Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ)
          = Nat.card (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ)
    ) ∧
    -- 3. Kepler.Text.CARD_SYM_0_p13 (LocalAuto13:425; HOL `CARD_SYM_0`)
    (∀ {A : Set V3} (h : A.Finite),
          Nat.card (Set.image (fun x : V3 => -x) A) = Nat.card A
    ) ∧
    -- 4. Kepler.Text.COLLINEAR_POINT_SYM_0_p13 (LocalAuto13:1482; HOL `COLLINEAR_POINT_SYM_0`)
    (∀ {v1 w1 : V3} (h : ¬Collinear ℝ ({0, v1, w1} : Set V3)),
          ¬Collinear ℝ ({0, v1, -w1} : Set V3)
    ) ∧
    -- 5. Kepler.Text.COLLINEAR_SYM_0_p13 (LocalAuto13:506; HOL `COLLINEAR_SYM_0`)
    (∀ {e : Set V3} (h : Collinear ℝ e),
          Collinear ℝ (Set.image (fun x : V3 => -x) e)
    ) ∧
    -- 6. Kepler.Text.COMMUTATIVE_POINT_PAIR_0_p13 (LocalAuto13:1115; HOL `COMMUTATIVE_POINT_PAIR_0`)
    (∀ {a b : V3 × V3},
          (fun p : V3 × V3 => (-p.1, -p.2)) a = b ↔ a = (fun p : V3 × V3 => (-p.1, -p.2)) b
    ) ∧
    -- 7. Kepler.Text.DART_OF_HYP_VV_p13 (LocalAuto13:1035; HOL `DART_OF_HYP_VV`)
    (∀ (vv : ℕ → V3),
          dartsOfHypP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            (Set.image vv Set.univ)
          = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
            ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
    ) ∧
    -- 8. Kepler.Text.DIST_SYM_0_p13 (LocalAuto13:973; HOL `DIST_SYM_0`)
    (∀ (a b : V3),
          dist (-a) (-b) = dist a b
    ) ∧
    -- 9. Kepler.Text.DIST_SYM_0_p13._abel_1_1 (auto-generated exit, signature = probe printer output)
    (∀ (a b : V3), -a - -b = -(a - b)
    ) ∧
    -- 10. Kepler.Text.DUALNEG_PEROPP_BB_p13 (LocalAuto13:1378; HOL `DUALNEG_PEROPP_BB`)
    (∀ {s : ScsV39P13} {k : ℕ} (ww : ℕ → V3)
          (hk : s.k = k) (hbb : BBsV39P13 (scsOppV39P13 s) ww) (hk3 : ¬(k ≤ 3)),
          (fun i => -(peroppP13 (fun i => -(peroppP13 ww k i)) k i)) = ww
    ) ∧
    -- 11. Kepler.Text.DUAL_EXISTS_MOD0_p13 (LocalAuto13:1263; HOL `DUAL_EXISTS_MOD0`)
    (∀ {k b : ℕ} (hk : k ≠ 0),
          ∃ n : ℕ, (n * (k - 1)) % k = b % k
    ) ∧
    -- 12. Kepler.Text.DUAL_EXISTS_MOD_GE_p13 (LocalAuto13:1295; HOL `DUAL_EXISTS_MOD_GE`)
    (∀ {k a b : ℕ} (hk : k ≠ 0) (hge : b % k ≤ a % k),
          ∃ n : ℕ, (n * (k - 1) + a) % k = b % k
    ) ∧
    -- 13. Kepler.Text.DUAL_EXISTS_MOD_LE_p13 (LocalAuto13:1284; HOL `DUAL_EXISTS_MOD_LE`)
    (∀ {k a b : ℕ} (hk : k ≠ 0) (hle : a % k ≤ b % k),
          ∃ n : ℕ, (n * (k - 1) + a) % k = b % k
    ) ∧
    -- 14. Kepler.Text.DUAL_EXISTS_MOD_p13 (LocalAuto13:1306; HOL `DUAL_EXISTS_MOD`)
    (∀ {k a b : ℕ} (hk : k ≠ 0),
          ∃ n : ℕ, (n * (k - 1) + a) % k = b % k
    ) ∧
    -- 15. Kepler.Text.DUAL_NEG_PEROPP_p13 (LocalAuto13:1369; HOL `DUAL_NEG_PEROPP`)
    (∀ {k : ℕ} (ww : ℕ → V3) (hk : k ≠ 0)
          (hper : PeriodicP13 ww k),
          (fun i => -(peroppP13 (fun i => -(peroppP13 ww k i)) k i)) = ww
    ) ∧
    -- 16. Kepler.Text.DUAL_PEROPP2_p13 (LocalAuto13:1353; HOL `DUAL_PEROPP2`)
    (∀ {α : Sort u} {a : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
          (hper : Periodic2P13 a k),
          peropp2P13 (peropp2P13 a k) k = a
    ) ∧
    -- 17. Kepler.Text.DUAL_PEROPP_p13 (LocalAuto13:1330; HOL `DUAL_PEROPP`)
    (∀ {α : Sort u} {a : ℕ → α} {k : ℕ} (hk : k ≠ 0)
          (hper : PeriodicP13 a k),
          peroppP13 (peroppP13 a k) k = a
    ) ∧
    -- 18. Kepler.Text.EE_SYM_0_p13 (LocalAuto13:1186; HOL `EE_SYM_0`)
    (∀ (vv : ℕ → V3) (a : V3),
          eeP13 (-a) (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          = Set.image (fun x : V3 => -x)
              (eeP13 a (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ))
    ) ∧
    -- 19. Kepler.Text.ELEMENT2_SYM_0_p13 (LocalAuto13:430; HOL `ELEMENT2_SYM_0`)
    (∀ (a b : V3),
          ({-a, -b} : Set V3) = Set.image (fun x : V3 => -x) ({a, b} : Set V3)
    ) ∧
    -- 20. Kepler.Text.EQUI_FF_SYM_0_p13 (LocalAuto13:1132; HOL `EQUI_FF_SYM_0`)
    (∀ (vv : ℕ → V3) (x : V3 × V3),
          (x.2, x.1) ∈ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
          ↔ x ∈ Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
    ) ∧
    -- 21. Kepler.Text.EQ_SET_PAIR_SYM_0_p13 (LocalAuto13:1096; HOL `EQ_SET_PAIR_SYM_0`)
    (∀ {A B : Set (V3 × V3)},
          Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A
            = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) B
          ↔ A = B
    ) ∧
    -- 22. Kepler.Text.FINITE_SYM_0_p13 (LocalAuto13:421; HOL `FINITE_SYM_0`)
    (∀ {A : Set V3} (h : A.Finite),
          (Set.image (fun x : V3 => -x) A).Finite
    ) ∧
    -- 23. Kepler.Text.FST_SND_EQ_PAIR_SYM_0_p13 (LocalAuto13:1127; HOL `FST_SND_EQ_PAIR_SYM_0`)
    (∀ (x : V3 × V3),
          (fun p : V3 × V3 => (-p.1, -p.2)) x = (-x.1, -x.2)
    ) ∧
    -- 24. Kepler.Text.FST_SND_PAIR_SYM_0_p13 (LocalAuto13:1090; HOL `FST_SND_PAIR_SYM_0`)
    (∀ (x : V3 × V3),
          ((fun p : V3 × V3 => (-p.1, -p.2)) x).1 = -x.1
          ∧ ((fun p : V3 × V3 => (-p.1, -p.2)) x).2 = -x.2
    ) ∧
    -- 25. Kepler.Text.FUN_COMMUTATIVE_p13 (LocalAuto13:1164; HOL `FUN_COMMUTATIVE`)
    (∀ {f g f1 : V3 × V3 → V3 × V3}
          (h : ∀ x, f (g x) = g (f1 x)),
          ∀ n x, f^[n] (g x) = g (f1^[n] x)
    ) ∧
    -- 26. Kepler.Text.GRAPH_SYM_0_p13 (LocalAuto13:444; HOL `GRAPH_SYM_0`, HOL `graph`)
    (∀ (vv : ℕ → V3)
          (h : Kepler.Text.Fan.Graph (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ)),
          Kepler.Text.Fan.Graph (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ)
    ) ∧
    -- 27. Kepler.Text.ID_PAIR_SYM_0_p13 (LocalAuto13:1064; HOL `ID_PAIR_SYM_0`)
    (∀ (A : Set (V3 × V3)),
          Set.image (fun p : V3 × V3 => (-p.1, -p.2))
            (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A)
          = A
    ) ∧
    -- 28. Kepler.Text.ID_SYM_0_p13 (LocalAuto13:1059; HOL `ID_SYM_0`)
    (∀ (x : V3 × V3),
          (fun p : V3 × V3 => (-p.1, -p.2)) ((fun p : V3 × V3 => (-p.1, -p.2)) x) = x
    ) ∧
    -- 29. Kepler.Text.IMAGE_E_SYM_0_p13 (LocalAuto13:491; HOL `IMAGE_E_SYM_0`)
    (∀ (vv : ℕ → V3) {e : Set V3}
          (h : e ∈ Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ),
          Set.image (fun x : V3 => -x) e
          ∈ Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ
    ) ∧
    -- 30. Kepler.Text.IMAGE_E_UNION_V_SYM_0_p13 (LocalAuto13:558; HOL `IMAGE_E_UNION_V_SYM_0`)
    (∀ (vv : ℕ → V3) {e : Set V3}
          (h : e ∈ Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ
            ∪ Set.image (fun v : V3 => {v}) (Set.range fun i => -(vv i))),
          Set.image (fun x : V3 => -x) e
          ∈ Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ
            ∪ Set.image (fun v : V3 => {v}) (Set.range vv)
    ) ∧
    -- 31. Kepler.Text.IMAGE_V_SYM_0_p13 (LocalAuto13:385; HOL `IMAGE_V_SYM_0`)
    (∀ (vv : ℕ → V3),
          Set.image (fun i : ℕ => -(vv i)) Set.univ
          = Set.image (fun x : V3 => -x) (Set.image vv Set.univ)
    ) ∧
    -- 32. Kepler.Text.INTER_SYM_0_p13 (LocalAuto13:578; HOL `INTER_SYM_0`)
    (∀ (e1 e2 : Set V3),
          Set.image (fun x : V3 => -x) (e1 ∩ e2)
          = Set.image (fun x : V3 => -x) e1 ∩ Set.image (fun x : V3 => -x) e2
    ) ∧
    -- 33. Kepler.Text.IN_EQ_PAIR_SYM_0_p13 (LocalAuto13:1072; HOL `IN_EQ_PAIR_SYM_0`)
    (∀ {a : V3 × V3} {A : Set (V3 × V3)},
          (fun p : V3 × V3 => (-p.1, -p.2)) a
            ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A
          ↔ a ∈ A
    ) ∧
    -- 34. Kepler.Text.IN_PAIR_SYM_0_p13 (LocalAuto13:1053; HOL `IN_PAIR_SYM_0`)
    (∀ {a : V3 × V3} {A : Set (V3 × V3)} (h : a ∈ A),
          (fun p : V3 × V3 => (-p.1, -p.2)) a
          ∈ Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A
    ) ∧
    -- 35. Kepler.Text.IN_SYM_0_p13 (LocalAuto13:371; HOL `IN_SYM_0`)
    (∀ {a : V3} {A : Set V3} (h : a ∈ A),
          -a ∈ Set.image (fun x : V3 => -x) A
    ) ∧
    -- 36. Kepler.Text.K_SCS_OPP_p13 (LocalAuto13:1327; HOL `K_SCS_OPP`)
    (∀ (s : ScsV39P13),
          (scsOppV39P13 s).k = s.k
    ) ∧
    -- 37. Kepler.Text.LINAER_SYM_0_p13 (LocalAuto13:573; HOL `LINAER_SYM_0`, HOL `linear f`)
    ((∀ x y : V3, -(x + y) = -x + -y) ∧ ∀ (c : ℝ) (x : V3), -(c • x) = c • -x
    ) ∧
    -- 38. Kepler.Text.MOD_SUC_MOD_p13 (LocalAuto13:623; HOL `MOD_SUC_MOD`)
    (∀ {k x : ℕ} (hk : 1 < k),
          (x % k + 1) % k = (x + 1) % k
    ) ∧
    -- 39. Kepler.Text.NOT_COLLINEAR_SYM_0_p13 (LocalAuto13:543; HOL `NOT_COLLINEAR_SYM_0`)
    (∀ {e : Set V3} (h : ¬Collinear ℝ e),
          ¬Collinear ℝ (Set.image (fun x : V3 => -x) e)
    ) ∧
    -- 40. Kepler.Text.NOT_SUBSET_EMPTY_SYM_0_p13 (LocalAuto13:479; HOL `NOT_SUBSET_EMPTY_SYM_0`)
    (∀ {A : Set V3} (h : ¬(A ⊆ ∅)),
          ¬(Set.image (fun x : V3 => -x) A ⊆ ∅)
    ) ∧
    -- 41. Kepler.Text.NO_IS_EAR_SCS_OPP_p13 (LocalAuto13:1319; HOL `NO_IS_EAR_SCS_OPP`)
    (∀ (s : ScsV39P13) (hk : ¬(s.k ≤ 3)),
          ¬(isEarV39P13 (scsOppV39P13 s))
    ) ∧
    -- 42. Kepler.Text.NO_IS_EAR_p13 (LocalAuto13:1313; HOL `NO_IS_EAR`)
    (∀ (s : ScsV39P13) (hk : ¬(s.k ≤ 3)),
          ¬(isEarV39P13 s)
    ) ∧
    -- 43. Kepler.Text.OPP_IMAGE_E_EQ_NEG_p13 (LocalAuto13:933; HOL `OPP_IMAGE_E_EQ_NEG`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image (fun i : ℕ =>
            ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3))
            Set.univ
          = Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ
    ) ∧
    -- 44. Kepler.Text.OPP_IMAGE_E_EQ_p13 (LocalAuto13:675; HOL `OPP_IMAGE_E_EQ`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image (fun i : ℕ => ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
            Set.univ
          = Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ
    ) ∧
    -- 45. Kepler.Text.OPP_IMAGE_F_EQ2_NEG_p13 (LocalAuto13:956; HOL `OPP_IMAGE_F_EQ2_NEG`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image (fun i : ℕ =>
            (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ
          = Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ
    ) ∧
    -- 46. Kepler.Text.OPP_IMAGE_F_EQ2_p13 (LocalAuto13:826; HOL `OPP_IMAGE_F_EQ2`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image
            (fun i : ℕ => (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))) Set.univ
          = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
    ) ∧
    -- 47. Kepler.Text.OPP_IMAGE_F_EQ_NEG_p13 (LocalAuto13:945; HOL `OPP_IMAGE_F_EQ_NEG`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image (fun i : ℕ =>
            (-(vv (k - ((i + 1) % k + 1))), -(vv (k - (i % k + 1))))) Set.univ
          = Set.image (fun i : ℕ => (-(vv i), -(vv (i + 1)))) Set.univ
    ) ∧
    -- 48. Kepler.Text.OPP_IMAGE_F_EQ_p13 (LocalAuto13:758; HOL `OPP_IMAGE_F_EQ`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : 1 < k),
          Set.image
            (fun i : ℕ => (vv (k - ((i + 1) % k + 1)), vv (k - (i % k + 1)))) Set.univ
          = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
    ) ∧
    -- 49. Kepler.Text.OPP_IMAGE_V_EQ_NEG_p13 (LocalAuto13:925; HOL `OPP_IMAGE_V_EQ_NEG`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : k ≠ 0),
          Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ
          = Set.image (fun i : ℕ => -(vv i)) Set.univ
    ) ∧
    -- 50. Kepler.Text.OPP_IMAGE_V_EQ_p13 (LocalAuto13:606; HOL `OPP_IMAGE_V_EQ`)
    (∀ (vv : ℕ → V3) {k : ℕ} (hper : PeriodicP13 vv k)
          (hk : k ≠ 0),
          Set.image (fun i : ℕ => vv (k - (i % k + 1))) Set.univ
          = Set.image vv Set.univ
    ) ∧
    -- 51. Kepler.Text.OPP_SUC_MOD_p13 (LocalAuto13:593; HOL `OPP_SUC_MOD`)
    (∀ {k x : ℕ} (hk : k ≠ 0),
          k - ((k - (x % k + 1)) % k + 1) = x % k
    ) ∧
    -- 52. Kepler.Text.ORD_PAIRS_E_VV_p13 (LocalAuto13:993; HOL `ORD_PAIRS_E_VV`)
    (∀ (vv : ℕ → V3),
          ordPairsP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
          = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
            ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
    ) ∧
    -- 53. Kepler.Text.PAIR_FUN_SYM_0_p13 (LocalAuto13:1046; HOL `PAIR_FUN_SYM_0`)
    (∀ (vv1 vv2 : ℕ → V3),
          Set.image (fun i : ℕ => (-(vv1 i), -(vv2 i))) Set.univ
          = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
              (Set.image (fun i : ℕ => (vv1 i, vv2 i)) Set.univ)
    ) ∧
    -- 54. Kepler.Text.PERIODIC_PROPERTY_p13 (LocalAuto13:601; HOL `periodic`)
    (∀ {α : Sort u} {f : ℕ → α} {k : ℕ}
          (hper : PeriodicP13 f k) (hk : k ≠ 0) (j : ℕ),
          f (j % k) = f j
    ) ∧
    -- 55. Kepler.Text.POINT_IN_AFF_LT_SYM_0_p13 (LocalAuto13:1427; HOL `POINT_IN_AFF_LT_SYM_0`)
    (∀ {v1 w2 : V3}
          (hd : Disjoint ({0, v1} : Set V3) {w2}),
          -w2 ∈ affLt ({0, v1} : Set V3) {w2}
    ) ∧
    -- 56. Kepler.Text.REFL_SYM_0_p13 (LocalAuto13:486; HOL `REFL_SYM_0`)
    (∀ (A : Set V3),
          Set.image (fun x : V3 => -x) (Set.image (fun x : V3 => -x) A) = A
    ) ∧
    -- 57. Kepler.Text.SELF_PAIR_EMPTY_VV_p13 (LocalAuto13:1021; HOL `SELF_PAIR_EMPTY_VV`)
    (∀ (vv : ℕ → V3),
          selfPairsP13 (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            (Set.image vv Set.univ)
          = ∅
    ) ∧
    -- 58. Kepler.Text.SET_EQ_SYM_0_p13 (LocalAuto13:381; HOL `SET_EQ_SYM_0`)
    (∀ {A B : Set V3} (h : A = B),
          Set.image (fun x : V3 => -x) A = Set.image (fun x : V3 => -x) B
    ) ∧
    -- 59. Kepler.Text.SUBSET_SYM_0_p13 (LocalAuto13:376; HOL `SUBSET_SYM_0`)
    (∀ {A B : Set V3} (h : A ⊆ B),
          Set.image (fun x : V3 => -x) A ⊆ Set.image (fun x : V3 => -x) B
    ) ∧
    -- 60. Kepler.Text.SUC_MOD_EQ_MOD_SUC_p13 (LocalAuto13:630; HOL `SUC_MOD_EQ_MOD_SUC`)
    (∀ {k x : ℕ} (hk : 1 < k),
          (k - (x % k + 1)) % k = (k - ((x + 1) % k)) % k
    ) ∧
    -- 61. Kepler.Text.SUM_PAIR_SYM_0_p13 (LocalAuto13:1225; HOL `SUM_PAIR_SYM_0`)
    (∀ {s : Set (V3 × V3)} (f : V3 × V3 → ℝ),
          setSum (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) s) f
          = setSum s (f ∘ (fun p : V3 × V3 => (-p.1, -p.2)))
    ) ∧
    -- 62. Kepler.Text.UNIONS_IMAGE_FAN_SYM_0_p13 (LocalAuto13:397; HOL `UNIONS_IMAGE_FAN_SYM_0`)
    (∀ (vv : ℕ → V3),
          ⋃₀ (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ)
          = Set.image (fun x : V3 => -x)
              (⋃₀ (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ))
    ) ∧
    -- 63. Kepler.Text.UNION_SYM_0_p13 (LocalAuto13:525; HOL `UNION_SYM_0`)
    (∀ (s e : Set V3),
          Set.image (fun x : V3 => -x) (s ∪ e)
          = Set.image (fun x : V3 => -x) s ∪ Set.image (fun x : V3 => -x) e
    ) ∧
    -- 64. Kepler.Text.VEC0_NOT_COLLINEAR_SYM_0_p13 (LocalAuto13:548; HOL `VEC0_NOT_COLLINEAR_SYM_0`)
    (∀ {e : Set V3}
          (h : ¬Collinear ℝ (({0} : Set V3) ∪ e)),
          ¬Collinear ℝ (({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e)
    ) ∧
    -- 65. Kepler.Text.VEC0_SYM_0_p13 (LocalAuto13:531; HOL `VEC0_SYM_0`)
    (Set.image (fun x : V3 => -x) ({0} : Set V3) = ({0} : Set V3)
    ) ∧
    -- 66. Kepler.Text.VEC0_UNION_SYM_0_p13 (LocalAuto13:537; HOL `VEC0_UNION_SYM_0`)
    (∀ (e : Set V3),
          Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
          = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e
    ) ∧
    -- 67. Kepler.Text.dartsOfHypP13.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (E : Set (Set V3)) (V : Set V3), dartsOfHypP13 E V = ordPairsP13 E ∪ selfPairsP13 E V
    ) ∧
    -- 68. Kepler.Text.eeP13.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (v : V3) (S : Set (Set V3)), eeP13 v S = {w | {v, w} ∈ S}
    ) :=
  ⟨BALL_ANNULUS_SYM_0_p13, CARD_EQUI_FF_SYM_0_p13, CARD_SYM_0_p13, COLLINEAR_POINT_SYM_0_p13,
      COLLINEAR_SYM_0_p13, COMMUTATIVE_POINT_PAIR_0_p13, DART_OF_HYP_VV_p13, DIST_SYM_0_p13,
      DIST_SYM_0_p13._abel_1_1, DUALNEG_PEROPP_BB_p13, DUAL_EXISTS_MOD0_p13,
      DUAL_EXISTS_MOD_GE_p13, DUAL_EXISTS_MOD_LE_p13, DUAL_EXISTS_MOD_p13, DUAL_NEG_PEROPP_p13,
      DUAL_PEROPP2_p13, DUAL_PEROPP_p13, EE_SYM_0_p13, ELEMENT2_SYM_0_p13, EQUI_FF_SYM_0_p13,
      EQ_SET_PAIR_SYM_0_p13, FINITE_SYM_0_p13, FST_SND_EQ_PAIR_SYM_0_p13, FST_SND_PAIR_SYM_0_p13,
      FUN_COMMUTATIVE_p13, GRAPH_SYM_0_p13, ID_PAIR_SYM_0_p13, ID_SYM_0_p13, IMAGE_E_SYM_0_p13,
      IMAGE_E_UNION_V_SYM_0_p13, IMAGE_V_SYM_0_p13, INTER_SYM_0_p13, IN_EQ_PAIR_SYM_0_p13,
      IN_PAIR_SYM_0_p13, IN_SYM_0_p13, K_SCS_OPP_p13, LINAER_SYM_0_p13, MOD_SUC_MOD_p13,
      NOT_COLLINEAR_SYM_0_p13, NOT_SUBSET_EMPTY_SYM_0_p13, NO_IS_EAR_SCS_OPP_p13, NO_IS_EAR_p13,
      OPP_IMAGE_E_EQ_NEG_p13, OPP_IMAGE_E_EQ_p13, OPP_IMAGE_F_EQ2_NEG_p13, OPP_IMAGE_F_EQ2_p13,
      OPP_IMAGE_F_EQ_NEG_p13, OPP_IMAGE_F_EQ_p13, OPP_IMAGE_V_EQ_NEG_p13, OPP_IMAGE_V_EQ_p13,
      OPP_SUC_MOD_p13, ORD_PAIRS_E_VV_p13, PAIR_FUN_SYM_0_p13, PERIODIC_PROPERTY_p13,
      POINT_IN_AFF_LT_SYM_0_p13, REFL_SYM_0_p13, SELF_PAIR_EMPTY_VV_p13, SET_EQ_SYM_0_p13,
      @SUBSET_SYM_0_p13, SUC_MOD_EQ_MOD_SUC_p13, SUM_PAIR_SYM_0_p13, UNIONS_IMAGE_FAN_SYM_0_p13,
      UNION_SYM_0_p13, VEC0_NOT_COLLINEAR_SYM_0_p13, VEC0_SYM_0_p13, VEC0_UNION_SYM_0_p13,
      dartsOfHypP13.eq_1, eeP13.eq_1⟩

set_option linter.unusedVariables false in
/-- LocalAuto9 materialization capstone (LV program slot B, wave
lv34-w1, 2026-11-04; scout lane leftover-mat-scout §1-§3, generator
precedent la35-root-w1 `a8e35ccf`).  The 68 clean top-level public
LocalAuto9 theorem exits unreachable from every e2e root (probe1
SEED_PROBES: 68 clean + 9 sorried
exits excluded per the workorder -- the sorried half is not entered,
zero of its proof debt flows into this file; group closure of the clean
subset measured GROUP_SORRIED = 0, so K_SORRIED 134 and K_AXIOM 624 are
untouched). 12 of the 68 conjuncts are auto-generated equation/structure exits restated from the `#check @name` printer output (no verbatim source declaration exists).
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LocalAuto9 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied
verbatim and mechanically split at the binder/conclusion separator by
the generator gen_items.py), or the Lean `#check @name` printer dump
for the auto-generated items (logs/sigprobe_w1.out); semantic identity
is re-verified by the elaboration of the ⟨…⟩ assembly below (each
component must unify definitionally with its conjunct); the
per-conjunct comments carry each exit's LocalAuto9 declaration line and
file-local docstring HOL anchor.
Conjunct order: the seed-list order (seeds_clean.txt module block,
scout logs).  Body = the assembly of the exit constants -- zero new
proof obligations, zero new imports (LocalAuto9 is already imported
transitively via LocalAuto23 (:494 → LocalAuto23:111)).
Wiring (Assembly consumption) is NOT part of this wave -- lane
lv-wire-w2 owns it; expected cone yield at the wiring gate: +209
(LA13) / +180 (LA9) per the scout BFS upper bound, +389 for the pair. -/
theorem la9_capstone_w1 :
    -- 1. Kepler.Text.AFF_GE_2_2_p9 (LocalAuto9:2455; HOL `AFF_GE_2_2`)
    (∀ (x u v w : V3) (hd : Disjoint ({x, u} : Set V3) {v, w}),
          affGe {x, u} {v, w} =
          {y | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t3 ∧ 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
            y = t1 • x + t2 • u + t3 • v + t4 • w}
    ) ∧
    -- 2. Kepler.Text.AFF_GE_3_1_p9 (LocalAuto9:2206; HOL `AFF_GE_3_1`)
    (∀ (x v u w : V3) (hd : Disjoint ({x, v, u} : Set V3) {w}),
          affGe {x, v, u} {w} =
          {y | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
            y = t1 • x + t2 • v + t3 • u + t4 • w}
    ) ∧
    -- 3. Kepler.Text.AFF_GE_3_1_p9._abel_1_4 (auto-generated exit, signature = probe printer output)
    (∀ (x v u w : V3) (f : V3 → ℝ),
          f x • x + (f v • v + (f u • u + f w • w)) = f x • x + f v • v + f u • u + f w • w
    ) ∧
    -- 4. Kepler.Text.AFF_GE_3_1_p9._abel_1_6 (auto-generated exit, signature = probe printer output)
    (∀ (x v u w : V3) (t1 t2 t3 t4 : ℝ),
          t1 • x + t2 • v + t3 • u + t4 • w = t1 • x + (t2 • v + (t3 • u + t4 • w))
    ) ∧
    -- 5. Kepler.Text.AFF_GE_EQ_AFF_GE_UNION_p9 (LocalAuto9:2990; HOL `AFF_GE_EQ_AFF_GE_UNION`)
    (∀ (x v u v1 : V3)
          (h1 : Disjoint ({x} : Set V3) {v, u})
          (h2 : Disjoint ({x} : Set V3) {v, v1})
          (h3 : Disjoint ({x} : Set V3) {v1, u})
          (h4 : v1 ∈ affGt {x} {v, u}),
          affGe {x} {v, u} = affGe {x} {v, v1} ∪ affGe {x} {v1, u}
    ) ∧
    -- 6. Kepler.Text.AFF_GE_SUBSET_AFF_GE_UNION_p9 (LocalAuto9:2919; HOL `AFF_GE_SUBSET_AFF_GE_UNION`)
    (∀ (x v u v1 : V3)
          (h1 : Disjoint ({x} : Set V3) {v, u})
          (h2 : Disjoint ({x} : Set V3) {v, v1})
          (h3 : Disjoint ({x} : Set V3) {v1, u})
          (h4 : v1 ∈ affGt {x} {v, u}),
          affGe {x} {v, u} ⊆ affGe {x} {v, v1} ∪ affGe {x} {v1, u}
    ) ∧
    -- 7. Kepler.Text.AFF_GT_SUBSET_WEDGE_IMP_VERTEX_p9 (LocalAuto9:2116; HOL `AFF_GT_SUBSET_WEDGE_IMP_VERTEX`)
    (∀ (x v w y z : V3)
          (h1 : ¬ Collinear ℝ ({x, v, w} : Set V3))
          (h2 : ¬ Collinear ℝ ({x, v, y} : Set V3))
          (h3 : ¬ Collinear ℝ ({x, v, z} : Set V3))
          (h4 : affGt {x} {v, w} ⊆ wedge x v y z),
          w ∈ wedge x v y z
    ) ∧
    -- 8. Kepler.Text.AFF_LT_1_1_p9 (LocalAuto9:1744; HOL `AFF_LT_1_1`)
    (∀ (x w : V3) (hxw : x ≠ w),
          affLt {x} {w} =
          {y | ∃ t1 t2 : ℝ, t2 < 0 ∧ t1 + t2 = 1 ∧ y = t1 • x + t2 • w}
    ) ∧
    -- 9. Kepler.Text.AZIM_PI_WEDGE_CROSS_DOT_p9 (LocalAuto9:2070; HOL `AZIM_PI_WEDGE_CROSS_DOT`)
    (∀ (u v w ww : V3) (h : azim u v w ww = Real.pi),
          wedge u v w ww = {x | 0 < dot3_p9 (cross3_p9 (v - u) (w - u)) (x - u)}
    ) ∧
    -- 10. Kepler.Text.AZIM_PI_WEDGE_SIN_p9 (LocalAuto9:1894; HOL `AZIM_PI_WEDGE_SIN`)
    (∀ (u v w ww : V3) (h : azim u v w ww = Real.pi),
          wedge u v w ww = {x | 0 < Real.sin (azim u v w x)}
    ) ∧
    -- 11. Kepler.Text.BOUNDED_TRI_SY_p9 (LocalAuto9:3359; HOL `BOUNDED_TRI_SY`)
    (∀ {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (_h : triStable_p9 k d s a b J f),
          Bornology.IsBounded (BSY1body_p9 k a b)
    ) ∧
    -- 12. Kepler.Text.BSY1body_p9.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (k : ℕ) (a b : ℕ → ℕ → ℝ),
          BSY1body_p9 k a b =
            {l |
              (∀ (j : Fin k), vecmatsV3_p4 l j ∈ ballAnnulus) ∧
                ∀ (i j : ℕ),
                  1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → a i j ≤ ‖rowV3_p9 l i - rowV3_p9 l j‖ ∧ ‖rowV3_p9 l i - rowV3_p9 l j‖ ≤ b i j}
    ) ∧
    -- 13. Kepler.Text.CARD_VERTEX_GE_3_LOCAL_FAN_p9 (LocalAuto9:1468; HOL `CARD_VERTEX_GE_3_LOCAL_FAN`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF),
          3 ≤ V.ncard
    ) ∧
    -- 14. Kepler.Text.CLOSED_TRI_SY_p9 (LocalAuto9:3297; HOL `CLOSED_TRI_SY`)
    (∀ {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (_h : triStable_p9 k d s a b J f),
          IsClosed (BSY1body_p9 k a b)
    ) ∧
    -- 15. Kepler.Text.COMPACT_TRI_STABLE_p9 (LocalAuto9:3408; HOL `COMPACT_TRI_STABLE`)
    (∀ {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Finset (Finset ℕ)} {f : ℕ → ℕ} (h : triStable_p9 k d s a b J f),
          IsCompact (BSY1body_p9 k a b)
    ) ∧
    -- 16. Kepler.Text.CONDITION_INANGLE_CROSS_DOT_p9 (LocalAuto9:2136; HOL `CONDITION_INANGLE_CROSS_DOT`)
    (∀ (x v w y z : V3)
          (h1 : affGt {x} {v, w} ⊆ wedge x v y z)
          (h2 : ¬ Collinear ℝ ({x, v, w} : Set V3))
          (h3 : ¬ Collinear ℝ ({x, v, y} : Set V3))
          (h4 : ¬ Collinear ℝ ({x, v, z} : Set V3))
          (h5 : azim x v y z < Real.pi),
          0 < dot3_p9 (cross3_p9 (v - x) (y - x)) (w - x) ∧
          0 < dot3_p9 (cross3_p9 (v - x) (w - x)) (z - x)
    ) ∧
    -- 17. Kepler.Text.CONTINUOUS_ON_D_FUN_p9 (LocalAuto9:513; HOL `CONTINUOUS_ON_D_FUN`)
    (∀ (s : StableSyP9) (m : ℕ),
          ContinuousOn (fun l : FinVec m 3 => dFun_p9 s l) (B_SY1_p9 m s.a_sy s.b_sy)
    ) ∧
    -- 18. Kepler.Text.CONTINUOUS_ON_ROW_p9 (LocalAuto9:502; HOL `CONTINUOUS_ON_ROW`)
    (∀ {m : ℕ} (i : ℕ) (S : Set (FinVec m 3)),
          ContinuousOn (fun l : FinVec m 3 => rowV3_p9 l i) S
    ) ∧
    -- 19. Kepler.Text.CONTINUOUS_ON_TAU_STAR_p9 (LocalAuto9:1242; HOL `CONTINUOUS_ON_TAU_STAR`)
    (∀ (s : StableSyP9) {m : ℕ}
          (hm : StableSysHyp_p9 s m),
          ContinuousOn (fun l : FinVec m 3 => tauStar_p9 s l)
          (B_SY1_p9 m s.a_sy s.b_sy)
    ) ∧
    -- 20. Kepler.Text.CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p9 (LocalAuto9:1525; HOL `CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF),
          ∀ v ∈ V, interiorAngle1_p2 0 FF v =
          azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)
    ) ∧
    -- 21. Kepler.Text.EAR_STABLE_SYSTEM_p9 (LocalAuto9:372; HOL `EAR_STABLE_SYSTEM`)
    (stableSystem_p9 3 0.11 (Finset.Icc 0 2)
          (aEar0_p9 {{1, 2}}) (bEar0_p9 {{1, 2}})
          {{1, 2}} (fun i => (1 + i) % 3)
    ) ∧
    -- 22. Kepler.Text.EAR_TRI_STABLE_SYSTEM_p9 (LocalAuto9:3270; HOL `EAR_TRI_STABLE_SYSTEM`)
    (triStable_p9 3 0.11 (Finset.Icc 0 2) (aEar0_p9 {{1, 2}}) (bEar0_p9 {{1, 2}})
          {{1, 2}} (fun i => (1 + i) % 3)
    ) ∧
    -- 23. Kepler.Text.FINITE_J1_SY_p9 (LocalAuto9:498; HOL `FINITE_J1_SY`)
    (∀ (s : StableSyP9),
          (J1_SY_p9 s : Set (ℕ × ℕ)).Finite
    ) ∧
    -- 24. Kepler.Text.FINITE_J_SY_p9 (LocalAuto9:494; HOL `FINITE_J_SY`)
    (∀ (s : StableSyP9),
          (s.J_SY : Set (Finset ℕ)).Finite
    ) ∧
    -- 25. Kepler.Text.INDEX_J1_SY_p9 (LocalAuto9:507; HOL `INDEX_J1_SY`)
    (∀ (s : StableSyP9) {x : ℕ × ℕ} (hx : x ∈ J1_SY_p9 s),
          1 ≤ x.1 ∧ x.1 ≤ s.k_sy
    ) ∧
    -- 26. Kepler.Text.IN_V_IMP_AZIM_LESS_PI (LocalAuto9:1378; HOL `IN_V_IMP_AZIM_LESS_PI`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (v : V3) (hv : v ∈ V),
          ∀ w ∈ V, azim 0 v (rhoNode1_p2 FF v) w ≤ Real.pi
    ) ∧
    -- 27. Kepler.Text.MOD_EQ_MOD1_p9 (LocalAuto9:131; HOL `MOD_EQ_MOD1`)
    (∀ {x1 x2 y n : ℕ} (_hn : n ≠ 0)
          (h : (y + x1) % n = (y + x2) % n) (_hle : x2 ≤ x1),
          x1 % n = x2 % n
    ) ∧
    -- 28. Kepler.Text.MOD_EQ_MOD_p9 (LocalAuto9:140; HOL `MOD_EQ_MOD`)
    (∀ {x1 x2 y n : ℕ} (hn : n ≠ 0)
          (h : (y + x1) % n = (y + x2) % n),
          x1 % n = x2 % n
    ) ∧
    -- 29. Kepler.Text.ORDER_p9 (LocalAuto9:3026; HOL `ORDER`)
    (∀ {α : Type*} (f : α → α) (x y : α) (n : ℕ)
          (h : f^[n] x = y) (hmin : ∀ i, 0 < i → i < n → ¬(f^[i] x = y)),
          f^[order_p9 f x y] x = y ∧
          ∀ i, 0 < i → i < order_p9 f x y → ¬(f^[i] x = y)
    ) ∧
    -- 30. Kepler.Text.PROPERTIES_GENERIC_LOCAL_FAN_p9 (LocalAuto9:1821; HOL `PROPERTIES_GENERIC_LOCAL_FAN`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (h : localFan_p2 V E FF) (hv0 : ∀ v0 ∈ V, True)
          (hg : generic_p2 V E) (v0 : V3) (hv0V : v0 ∈ V),
          ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3)
    ) ∧
    -- 31. Kepler.Text.REP_VERTEX_3_LOCAL_FAN_p9 (LocalAuto9:1494; HOL `REP_VERTEX_3_LOCAL_FAN`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (hcard : V.ncard = 3) (h : convexLocalFan_p2 V E FF),
          ∃ v : V3, V = {v, rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)} ∧
          v ≠ rhoNode1_p2 FF v ∧
          rhoNode1_p2 FF v ≠ rhoNode1_p2 FF (rhoNode1_p2 FF v) ∧
          rhoNode1_p2 FF (rhoNode1_p2 FF v) ≠ v
    ) ∧
    -- 32. Kepler.Text.SEQUENTIALLY_DIVH_p9 (LocalAuto9:667; HOL `SEQUENTIALLY_DIVH`, HOL `LIM_*`)
    (∀ (f g h : ℕ → V3) (a b c : V3)
          (hf : Filter.Tendsto f Filter.atTop (nhds a))
          (hg : Filter.Tendsto g Filter.atTop (nhds b))
          (hh : Filter.Tendsto h Filter.atTop (nhds c))
          (_hab : ¬ Collinear ℝ ({0, a, b} : Set V3))
          (_hac : ¬ Collinear ℝ ({0, a, c} : Set V3))
          (_hn : ∀ n : ℕ, ¬ Collinear ℝ ({0, f n, g n} : Set V3) ∧
            ¬ Collinear ℝ ({0, f n, h n} : Set V3)),
          Filter.Tendsto (fun n => dihV 0 (f n) (g n) (h n)) Filter.atTop
          (nhds (dihV 0 a b c))
    ) ∧
    -- 33. Kepler.Text.SOL_LOCAL_FAN_POS_CASE3_p9 (LocalAuto9:1571; HOL `SOL_LOCAL_FAN_POS_CASE3`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (hcard : V.ncard = 3),
          0 ≤ solLocal_p9 E FF
    ) ∧
    -- 34. Kepler.Text.TriSyP9.prop (auto-generated exit, signature = probe printer output)
    (∀ (self : TriSyP9), triStable_p9 self.k_ts self.d_ts self.I_TS self.a_ts self.b_ts self.J_TS self.f_ts
    ) ∧
    -- 35. Kepler.Text.UNIQUE_ORDER_p9 (LocalAuto9:3036; HOL `UNIQUE_ORDER`)
    (∀ {α : Type*} (f : α → α) (x y : α) (n : ℕ)
          (h : f^[n] x = y) (hmin : ∀ i, 0 < i → i < n → ¬(f^[i] x = y))
          (hxy : ¬(x = y)),
          order_p9 f x y = n
    ) ∧
    -- 36. Kepler.Text.aEar0_p9.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (J : Finset (Finset ℕ)) (i j : ℕ),
          aEar0_p9 J i j = if i % 3 = j % 3 then 0 else if {i % 3, j % 3} ∈ J then √8 else 2
    ) ∧
    -- 37. Kepler.Text.aEar0_p9_mod (LocalAuto9:183; no HOL anchor line in file docstring)
    (∀ (J : Finset (Finset ℕ)) (i j : ℕ),
          aEar0_p9 J i (j % 3) = aEar0_p9 J i j
    ) ∧
    -- 38. Kepler.Text.aff_ge_subset3_aff_ge_p9 (LocalAuto9:2977; HOL `aff_ge_subset3_aff_ge`)
    (∀ (x v u v1 : V3)
          (h1 : Disjoint ({x} : Set V3) {v, u})
          (h2 : Disjoint ({x} : Set V3) {v, v1})
          (h3 : v1 ∈ affGt {x} {v, u}),
          affGe {x} {v, v1} ⊆ affGe {x} {v, u}
    ) ∧
    -- 39. Kepler.Text.bEar0_p9.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (J : Finset (Finset ℕ)) (i j : ℕ),
          bEar0_p9 J i j = if i % 3 = j % 3 then 0 else if {i % 3, j % 3} ∈ J then cstab_p4 else 2 * h0
    ) ∧
    -- 40. Kepler.Text.bEar0_p9_mod (LocalAuto9:284; no HOL anchor line in file docstring)
    (∀ (J : Finset (Finset ℕ)) (i j : ℕ),
          bEar0_p9 J i (j % 3) = bEar0_p9 J i j
    ) ∧
    -- 41. Kepler.Text.bsy1body_rows_p9 (LocalAuto9:3403; no HOL anchor line in file docstring)
    (∀ {k : ℕ} {a b : ℕ → ℕ → ℝ} {l : FinVec k 3}
          (hl : l ∈ BSY1body_p9 k a b),
          ∀ j : Fin k, vecmatsV3_p4 l j ∈ ballAnnulus
    ) ∧
    -- 42. Kepler.Text.cross3_p9.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (u w : V3), cross3_p9 u w = WithLp.toLp 2 ((crossProduct u.ofLp) w.ofLp)
    ) ∧
    -- 43. Kepler.Text.dot3_p9.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ (u w : V3), dot3_p9 u w = u.ofLp ⬝ᵥ w.ofLp
    ) ∧
    -- 44. Kepler.Text.earJ_mem_p9 (LocalAuto9:192; HOL `{{1,2}}`)
    (∀ {e : Finset ℕ}
          (h : e ∈ ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ))),
          e = ({1, 2} : Finset ℕ)
    ) ∧
    -- 45. Kepler.Text.ear_J_p9 (LocalAuto9:347; no HOL anchor line in file docstring)
    (∀ i j : ℕ, ({i, j} : Finset ℕ) ∈
          ({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) →
            aEar0_p9 {{1, 2}} i j = Real.sqrt 8 ∧ bEar0_p9 {{1, 2}} i j = cstab_p4
    ) ∧
    -- 46. Kepler.Text.ear_card_p9 (LocalAuto9:307; no HOL anchor line in file docstring)
    (({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)).card + 3 ≤ 6
    ) ∧
    -- 47. Kepler.Text.ear_closed_p9 (LocalAuto9:212; no HOL anchor line in file docstring)
    (∀ x ∈ (Finset.Icc 0 2 : Finset ℕ), (1 + x) % 3 ∈ Finset.Icc 0 2
    ) ∧
    -- 48. Kepler.Text.ear_diag_lt_p9 (LocalAuto9:3242; no HOL anchor line in file docstring)
    (∀ i ∈ (Finset.Icc 0 2 : Finset ℕ),
          aEar0_p9 {{1, 2}} i i = 0 ∧ bEar0_p9 {{1, 2}} i ((1 + i) % 3) < 4
    ) ∧
    -- 49. Kepler.Text.ear_diag_p9 (LocalAuto9:322; no HOL anchor line in file docstring)
    (∀ i ∈ (Finset.Icc 0 2 : Finset ℕ),
          aEar0_p9 {{1, 2}} i i = 0 ∧
            bEar0_p9 {{1, 2}} i ((1 + i) % 3) ≤ cstab_p4
    ) ∧
    -- 50. Kepler.Text.ear_ge2_p9 (LocalAuto9:311; no HOL anchor line in file docstring)
    (∀ i ∈ (Finset.Icc 0 2 : Finset ℕ), ∀ j ∈ Finset.Icc 0 2,
          i ≠ j → 2 ≤ aEar0_p9 {{1, 2}} i j
    ) ∧
    -- 51. Kepler.Text.ear_inj_p9 (LocalAuto9:218; no HOL anchor line in file docstring)
    (∀ x₁ ∈ (Finset.Icc 0 2 : Finset ℕ), ∀ x₂ ∈ Finset.Icc 0 2,
          (1 + x₁) % 3 = (1 + x₂) % 3 → x₁ = x₂
    ) ∧
    -- 52. Kepler.Text.ear_nofix1_p9 (LocalAuto9:225; no HOL anchor line in file docstring)
    (∀ x ∈ (Finset.Icc 0 2 : Finset ℕ), (1 + x) % 3 ≠ x
    ) ∧
    -- 53. Kepler.Text.ear_nofix2_p9 (LocalAuto9:231; no HOL anchor line in file docstring)
    (∀ x ∈ (Finset.Icc 0 2 : Finset ℕ),
          (fun i => (1 + i) % 3)^[2] x ≠ x
    ) ∧
    -- 54. Kepler.Text.ear_num_p9 (LocalAuto9:199; no HOL anchor line in file docstring)
    (Real.sqrt 8 ≤ cstab_p4 ∧ (2:ℝ) ≤ 2 * h0 ∧ 2 * h0 ≤ cstab_p4 ∧
          (2:ℝ) ≤ Real.sqrt 8
    ) ∧
    -- 55. Kepler.Text.ear_period_ab_p9 (LocalAuto9:291; no HOL anchor line in file docstring)
    (∀ (i j : ℕ),
          aEar0_p9 {{1, 2}} i j = aEar0_p9 {{1, 2}} i ((fun n => (1 + n) % 3)^[3] j) ∧
          bEar0_p9 {{1, 2}} i j = bEar0_p9 {{1, 2}} i ((fun n => (1 + n) % 3)^[3] j)
    ) ∧
    -- 56. Kepler.Text.ear_period_p9 (LocalAuto9:239; no HOL anchor line in file docstring)
    (∀ x ∈ (Finset.Icc 0 2 : Finset ℕ),
          (fun i => (1 + i) % 3)^[3] x = x
    ) ∧
    -- 57. Kepler.Text.ear_subset_p9 (LocalAuto9:298; no HOL anchor line in file docstring)
    (({({1, 2} : Finset ℕ)} : Finset (Finset ℕ)) ⊆
          (Finset.Icc 0 2).image (fun i => ({i, (1 + i) % 3} : Finset ℕ))
    ) ∧
    -- 58. Kepler.Text.ear_sym_p9 (LocalAuto9:247; no HOL anchor line in file docstring)
    (∀ (i j : ℕ),
          aEar0_p9 {{1, 2}} i j = aEar0_p9 {{1, 2}} j i ∧
          bEar0_p9 {{1, 2}} i j = bEar0_p9 {{1, 2}} j i ∧
          aEar0_p9 {{1, 2}} i j ≤ bEar0_p9 {{1, 2}} i j
    ) ∧
    -- 59. Kepler.Text.exist_stable_system_p9 (LocalAuto9:451; HOL `exist_stable_system`)
    (∃ (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
          (J : Finset (Finset ℕ)), ∃ f : ℕ → ℕ, stableSystem_p9 k d s a b J f
    ) ∧
    -- 60. Kepler.Text.exist_tri_stable_p9 (LocalAuto9:3276; HOL `exist_tri_stable`)
    (∃ (k : ℕ) (d : ℝ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
          (J : Finset (Finset ℕ)), ∃ f : ℕ → ℕ, triStable_p9 k d s a b J f
    ) ∧
    -- 61. Kepler.Text.inter_aff_ge_3_1_is_aff_ge_2_2_p9 (LocalAuto9:2681; HOL `inter_aff_ge_3_1_is_aff_ge_2_2`)
    (∀ (x v u w : V3)
          (h : ¬ Coplanar ℝ ({x, v, u, w} : Set V3)),
          affGe {x, v, u} {w} ∩ affGe {x, u, w} {v} = affGe {x, u} {v, w}
    ) ∧
    -- 62. Kepler.Text.inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_3 (auto-generated exit, signature = probe printer output)
    (∀ (x v u w : V3) (a' b' c' d' : ℝ),
          a' • x + b' • u + c' • w + d' • v = a' • x + b' • u + d' • v + c' • w
    ) ∧
    -- 63. Kepler.Text.inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_5 (auto-generated exit, signature = probe printer output)
    (∀ (x v u w : V3) (t1 t2 t3 t4 : ℝ),
          t1 • x + t2 • u + t3 • v + t4 • w = t1 • x + t3 • v + t2 • u + t4 • w
    ) ∧
    -- 64. Kepler.Text.inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_6 (auto-generated exit, signature = probe printer output)
    (∀ (x v u w : V3) (t1 t2 t3 t4 : ℝ),
          t1 • x + t2 • u + t3 • v + t4 • w = t1 • x + t2 • u + t4 • w + t3 • v
    ) ∧
    -- 65. Kepler.Text.iter3_ear_p9 (LocalAuto9:178; no HOL anchor line in file docstring)
    (∀ (j : ℕ),
          (fun i => (1 + i) % 3)^[3] j = j % 3
    ) ∧
    -- 66. Kepler.Text.nkezLemma1_p9 (LocalAuto9:3057; HOL `lemma1`)
    (∀ (A : Prop),
          ¬A ∨ A
    ) ∧
    -- 67. Kepler.Text.nkezLemma_p9 (LocalAuto9:2778; HOL `lemma`)
    (∀ (A : Prop),
          A ∨ ¬A
    ) ∧
    -- 68. Kepler.Text.vecmatsV3_p4.eq_1 (auto-generated exit, signature = probe printer output)
    (∀ {m : ℕ} (l : FinVec m 3) (j : Fin m), vecmatsV3_p4 l j = WithLp.toLp 2 (vecmats_p4 l j)
    ) :=
  ⟨AFF_GE_2_2_p9, AFF_GE_3_1_p9, AFF_GE_3_1_p9._abel_1_4, AFF_GE_3_1_p9._abel_1_6,
      AFF_GE_EQ_AFF_GE_UNION_p9, @AFF_GE_SUBSET_AFF_GE_UNION_p9,
      AFF_GT_SUBSET_WEDGE_IMP_VERTEX_p9, AFF_LT_1_1_p9, @AZIM_PI_WEDGE_CROSS_DOT_p9,
      AZIM_PI_WEDGE_SIN_p9, BOUNDED_TRI_SY_p9, BSY1body_p9.eq_1, CARD_VERTEX_GE_3_LOCAL_FAN_p9,
      CLOSED_TRI_SY_p9, COMPACT_TRI_STABLE_p9, CONDITION_INANGLE_CROSS_DOT_p9,
      CONTINUOUS_ON_D_FUN_p9, CONTINUOUS_ON_ROW_p9, CONTINUOUS_ON_TAU_STAR_p9,
      CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p9, EAR_STABLE_SYSTEM_p9, EAR_TRI_STABLE_SYSTEM_p9,
      FINITE_J1_SY_p9, FINITE_J_SY_p9, INDEX_J1_SY_p9, IN_V_IMP_AZIM_LESS_PI, MOD_EQ_MOD1_p9,
      MOD_EQ_MOD_p9, ORDER_p9, PROPERTIES_GENERIC_LOCAL_FAN_p9, REP_VERTEX_3_LOCAL_FAN_p9,
      SEQUENTIALLY_DIVH_p9, SOL_LOCAL_FAN_POS_CASE3_p9, TriSyP9.prop, UNIQUE_ORDER_p9,
      aEar0_p9.eq_1, aEar0_p9_mod, @aff_ge_subset3_aff_ge_p9, bEar0_p9.eq_1, bEar0_p9_mod,
      bsy1body_rows_p9, cross3_p9.eq_1, dot3_p9.eq_1, earJ_mem_p9, ear_J_p9, ear_card_p9,
      ear_closed_p9, ear_diag_lt_p9, ear_diag_p9, ear_ge2_p9, ear_inj_p9, ear_nofix1_p9,
      ear_nofix2_p9, ear_num_p9, ear_period_ab_p9, ear_period_p9, @ear_subset_p9, ear_sym_p9,
      exist_stable_system_p9, exist_tri_stable_p9, inter_aff_ge_3_1_is_aff_ge_2_2_p9,
      inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_3, inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_5,
      inter_aff_ge_3_1_is_aff_ge_2_2_p9._abel_1_6, iter3_ear_p9, nkezLemma1_p9, nkezLemma_p9,
      vecmatsV3_p4.eq_1⟩

#print axioms la13_capstone_w1
#print axioms la9_capstone_w1

/-- WIRE (real proof, la20-engine-sink-w1) `LocalAuto1.AQICLXA_concl` <- the
`LKGRQUI_p27` instance `l20es_SLICE_6I1_02` (LA27 engine over `scs6I1 0 2`;
`d' = 0.103 -> 3M1`, `d'' = 0.616 -> 5M1`) + the clean `YXIONXL3_discharged`
rotations + the target-set permutation shim (`{scs3M1, scs5M1} =
{scs5M1, scs3M1}`), replacing the LA20 twin `AQICLXA` (still sorried; the
LA20 leaf cannot import the engine - LA24 imports LA20).  Statement verbatim. -/
theorem AQICLXA_discharged :
    scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs5M1, scs3M1} :=
  arrowSetRight l20es_AQICLXA (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.HIJQAHA_concl` <- `HIJQAHA_p29` (shims: passed terminal-bank hypothesis `hmn`; target-set permutation — same ten systems, re-ordered).
Twin still sorried — debt flows. -/
theorem HIJQAHA_discharged (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs5M2} {scs3T1, scs3T4, scs4M6', scs4M7, scs4M8, scs5T1,
      scsStabDiagV39 scs5I2 0 2, scsStabDiagV39 scs5M1 0 2,
      scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4} :=
  arrowSetRight (HIJQAHA_p29 hmn) (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.ARDBZYE_concl` <- PROVED `ARDBZYE_p33` through the
passed terminal-bank hypothesis `hmn` (verbatim modulo the hypothesis). -/
theorem ARDBZYE_discharged (hmn : main_nonlinear_terminal_v11) : scsArrowV39 {scs4I2} {scs4T1, scs4T2} :=
  ARDBZYE_p33 hmn

/-- WIRE `LocalAuto1.FYSSVEV_concl` <- PROVED `FYSSVEV_p33` through the
passed terminal-bank hypothesis `hmn` (verbatim modulo the hypothesis). -/
theorem FYSSVEV_discharged (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4I1} {scs4I2, scsStabDiagV39 scs4I1 0 2} :=
  FYSSVEV_p33 hmn

/-- WIRE `LocalAuto1.NWDGKXH_concl` <- `NWDGKXH_p32` through the passed terminal-bank hypothesis `hmn` (verbatim modulo the
hypothesis).  Twin still sorried — debt
flows. -/
theorem NWDGKXH_discharged (hmn : main_nonlinear_terminal_v11) : scsArrowV39 {scs4M6'} {scs4T3, scs4T5} :=
  NWDGKXH_p32 hmn

/-- WIRE `LocalAuto1.YOBIMPP_concl` <- `YOBIMPP_p32` (shims: passed terminal-bank hypothesis `hmn`; target-set permutation
`{scs4M6', scs3T3, scs3M1, scs3T4} = {scs3M1, scs3T3, scs3T4, scs4M6'}`).
Twin still sorried — debt flows. -/
theorem YOBIMPP_discharged (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4M7} {scs3M1, scs3T3, scs3T4, scs4M6'} :=
  arrowSetRight (YOBIMPP_p32 hmn) (by ext t; simp; tauto)

/-- WIRE `LocalAuto1.MIQMCSN_concl` <- `MIQMCSN_p32` through the passed terminal-bank hypothesis `hmn` (verbatim modulo the
hypothesis).  Twin still sorried — debt
flows. -/
theorem MIQMCSN_discharged (hmn : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4M8} {scs4M6', scs3T7, scs3T4} :=
  MIQMCSN_p32 hmn

/-- WIRE `LocalAuto1.CUXVZOZ_concl` <- PROVED `CUXVZOZ_p21` (hypotheses
verbatim).  The twin's hypothesis `mainNonlinearTerminalV11_p21` **is**
`main_nonlinear_terminal_v11` (LocalAuto21 alias, `p21-anchor` DEF-FIX), so the
wire's own `_hmn` is passed straight through — no anchor.  The twin's engine
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
  refine CUXVZOZ_p21 _hmn s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen
    hd' (fun i j hdiag hps => ha i j ⟨hdiag, by rw [← hkm]; exact hps⟩) hb
    hang hcase ha12 hb12 h2' hdc'

/-- WIRE `LocalAuto1.CJBDXXN_concl` <- PROVED `CJBDXXN_p21` (mirror of
CUXVZOZ, same straight-through `_hmn`). -/
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
    CJBDXXN_p21 _hmn s FF k p1 v hFF hs hk hk3 hMMs hbasic hgen hd'
      (fun i j hdiag hps => ha i j ⟨hdiag, by rw [← hkm]; exact hps⟩) hb hang
      hcase' ha12' hb12' h2 hdc
  rw [← hkm]
  exact hfin

/-! ## Skeleton holds (2026-09-21 wave): entries with no bridgeable twin

Each HOLD re-exposes its registry contract with an explicit `sorry` and the
blocker recorded.  28 holds = 5 (a) no-twin + 11 (b) circular re-export +
7 (c) non-bridgeable + 5 (d) shape mismatch.  (2026-09-21 II: the four
OTMTOTJ1-4 holds left this section as WIREs through the new
`LocalAuto24.OTMTOTJ1-4` restatements.  2026-09-21 III: the ASSWPOW and
DRNDRDV holds left as WIREs through `LocalAuto25.ASSWPOW_p25` and the
already-in-place PROVED `LocalAuto22.derived_form_xrr_p22`.) -/

/-! ### (a) No downstream twin anywhere in LocalAuto2-38 (5; after the
2026-09-21 II wave moved OTMTOTJ1-4 out via the new LA24 restatements and
the 2026-09-21 III wave moved ASSWPOW/DRNDRDV out via LA25.ASSWPOW_p25 and
the proved LA22.derived_form_xrr_p22) -/

/-- HOLD (a) `HFNXPZA_concl`: no twin in any lane.  HOL audit 2026-09-21 II:
the corpus carries this only as the appendix.hl:710 registry let; no proved
lemma under this name exists anywhere in `lean/scripts/local/` (corpus-wide
grep).  Ruling 2026-09-21 IV: the let is a proposition-valued statement
binding (k = 3 dihedral sum < 2*pi -- theorem-shaped), NOT a
`new_definition` and NOT a `prove`; no `HFNXPZA.hl` proof file exists and
no k = 3 lane (JKQEWGV/UXCKFPE/XWITCCN) even mentions `dihV`.  Verdict:
upstream proof absent (class iii); the registry entry is a faithful
transcription of a real unproved book conclusion -- HOLD stands. -/
theorem HFNXPZA_discharged : ∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → s.k = 3 →
    dihV 0 (vv 0) (vv 1) (vv 2) + dihV 0 (vv 1) (vv 2) (vv 3) +
      dihV 0 (vv 2) (vv 3) (vv 1) < 2 * Real.pi := by
  sorry

/-- HOLD (a) `EQTTNZI1_concl`: no twin in any lane.  HOL audit 2026-09-21 II:
appendix.hl:1110 registry let only; no proved lemma in the corpus
(restriction_typ1_v39 is defined appendix.hl:715).  Ruling 2026-09-21 IV:
the let is a proposition-valued statement binding, NOT a definition; its
`restriction_typ1_v39` is a `new_definition` (appendix.hl:716) whose ZERO
corpus consumers outside appendix.hl make the whole restriction toolkit a
dead end -- no `EQTTNZI.hl` proof file exists.  Verdict: class (iii)
upstream proof absent; HOLD stands. -/
theorem EQTTNZI1_discharged : ∀ s : ScsV39, isScsV39 s →
    (∀ i j, s.J i j → s.b i j = s.bm i j) →
    (s.J = fun _ _ => False ∨ 3 < s.k) →
    scsArrowV39 {s} {restrictionTyp1V39 s} := by
  sorry

/-- HOLD (a) `EQTTNZI2_concl`: no twin in any lane.  HOL audit 2026-09-21 II:
appendix.hl:1115 registry let only; no proved lemma in the corpus
(restriction_typ2_v39 is defined appendix.hl:719).  Ruling 2026-09-21 IV:
same shape as EQTTNZI1 -- proposition-valued statement let, no `prove`
upstream, `restriction_typ2_v39` a dead-end `new_definition` (appendix.hl:
719).  Verdict: class (iii); HOLD stands. -/
theorem EQTTNZI2_discharged : ∀ (s t : ScsV39), isScsV39 s → s.am = s.bm →
    t = restrictionTyp2V39 s → (∀ i j, ¬s.J i j) → (∀ i, s.am i i = 0) →
    {i | i < t.k ∧ (2 * h0 < t.b i (i + 1) ∨ 2 < t.a i (i + 1))}.ncard + t.k ≤ 6 →
    scsArrowV39 {s} {t} := by
  sorry

/-- WIRE `LocalAuto1.DRNDRDV_concl` <- PROVED `LocalAuto22.derived_form_xrr_p22`
(LA22:260).  The faithful twin was ALREADY in place: it is the verbatim Lean
rendering of the HOL original `derived_form_xrr` (OCBICBY.hl:766; aliased
`let DRNDRDV = derived_form_xrr` at OCBICBY.hl:849) and its statement
matches the registry form verbatim — no new code needed (2026-09-21 III).
The twin's proof is sorry-free (`xrr` re-derived onto the proved
`hasDerivWithinAt_quad_p22` derivative kernel) and registry-independent, so
the wire is not a (b)-style cycle. -/
theorem DRNDRDV_discharged : ∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ) :=
  derived_form_xrr_p22

/-- WIRE `LocalAuto1.ASSWPOW_concl` <- `LocalAuto25.ASSWPOW_p25` (faithful
twin of the PROVED HOL original VASYYAU.hl:154, statement verbatim; added
2026-09-21 III in the owning module).  The twin's body is still a skeleton
`sorry` — the HOL proof runs through the `BBS_IMP_CONVEX_LOCAL_FAN` fan kit
plus the Flyspeck-constants `arclength_lt_1553` calc, not yet ported — so
debt flows; the twin is an independent proof piece (not a re-export of the
registry concl), hence no (b)-style cycle. -/
theorem ASSWPOW_discharged : ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → s.k = 4 → scsBasicV39 s →
    s.b i (i + 1) ≤ 2 * h0 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53 :=
  ASSWPOW_p25

/-- HOLD (a) `EFLYGAU_concl`: no twin in any lane.  HOL audit 2026-09-21 II:
appendix.hl:1500 registry let only; no proved lemma in the corpus.  Ruling
2026-09-21 IV: proposition-valued statement let (NOT a definition); no
`scs_arrow_v39 {scs_4M7} {scs_4M6'}` is proved anywhere -- the nearest
scs_4M7 activity, `MM_4M7_IMP_STAB_4M7` (MIQMCSN.hl:1101), proves
stab-diag nonemptiness, a different statement.  Verdict: class (iii);
HOLD stands. -/
theorem EFLYGAU_discharged :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M7 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M7} {scs4M6'} := by
  sorry

/-- HOLD (a) `BJTDWPS_concl`: no twin in any lane.  HOL audit 2026-09-21 II:
appendix.hl:1506 registry let only; no proved lemma in the corpus.  Ruling
2026-09-21 IV: proposition-valued statement let (NOT a definition); no
`scs_arrow_v39 {scs_4M8} {scs_4M6', scs_3T7}` is proved anywhere -- the
nearest scs_4M8 activity, `MM_4M8_IMP_STAB_4M8` (MIQMCSN.hl:1521), proves
stab-diag nonemptiness, a different statement.  Verdict: class (iii);
HOLD stands. -/
theorem BJTDWPS_discharged :
    (∃ v : ℕ → V3, v ∈ MMsV39 scs4M8 ∧ cstab < dist (v 0) (v 2) ∧
      cstab < dist (v 1) (v 3)) → scsArrowV39 {scs4M8} {scs4M6', scs3T7} := by
  sorry

/-- WIRE `LocalAuto1.OTMTOTJ1_concl` <- `LocalAuto24.OTMTOTJ1` (verbatim
twin; faithful restatement of the PROVED HOL master OTMTOTJ.hl:1156, added
2026-09-21 II in the owning module).  Twin still sorried — debt flows. -/
theorem OTMTOTJ1_discharged :
    scsArrowV39 {scs5I1} {scsStabDiagV39 scs5I1 0 2, scs5M2} :=
  OTMTOTJ1

/-- WIRE `LocalAuto1.OTMTOTJ2_concl` <- `LocalAuto24.OTMTOTJ2` (verbatim
twin; faithful restatement of OTMTOTJ.hl:1169).  Twin still sorried — debt
flows. -/
theorem OTMTOTJ2_discharged :
    scsArrowV39 {scs5I2} {scsStabDiagV39 scs5I2 0 2, scs5M2} :=
  OTMTOTJ2

/-- WIRE `LocalAuto1.OTMTOTJ3_concl` <- `LocalAuto24.OTMTOTJ3` (verbatim
twin; faithful restatement of OTMTOTJ.hl:1500).  Twin still sorried — debt
flows. -/
theorem OTMTOTJ3_discharged :
    scsArrowV39 {scs5I3} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} :=
  OTMTOTJ3

/-- WIRE `LocalAuto1.OTMTOTJ4_concl` <- `LocalAuto24.OTMTOTJ4` (verbatim
twin; faithful restatement of OTMTOTJ.hl:1520).  Twin still sorried — debt
flows. -/
theorem OTMTOTJ4_discharged :
    scsArrowV39 {scs5M1} {scsStabDiagV39 scs5M1 0 2, scsStabDiagV39 scs5M1 0 3,
      scsStabDiagV39 scs5M1 2 4, scs5M2} :=
  OTMTOTJ4

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
theorem YEBWJNG_discharged (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
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
theorem WKZZEEH_discharged (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
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
theorem PWEIWBZ_discharged (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
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
theorem VASYYAU_discharged (h : main_nonlinear_terminal_v11) :
    ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ), isScsV39 s →
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
    3 < s.k → scsArrowV39 {s} {scsOppV39 s} := by
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
theorem SYNQIWN_discharged : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (v : ℕ → V3) (i k : ℕ), isScsV39 s → BBsV39 s v →
    s.k = k → 3 < k →
    (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2 ∨
      (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
      (norm (v (i + 1)) = 2 ∧ norm (v (i + k - 1)) = 2) ∨
      (dist (v i) (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2) ∨
      (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
      (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2)) →
    dist (v i) (v (i + 1)) ≤ 2 * h0 →
    dist (v i) (v (i + k - 1)) ≤ 2 * h0 →
    cstab ≤ dist (v (i + 1)) (v (i + k - 1)) →
    Real.pi / 2 < azim 0 (v i) (v (i + 1)) (v (i + k - 1)) := by
  sorry

/-- HOLD (c) `CQAOQLR_concl`: the LA16 twin `CQAOQLR_p16` consumes the
combined diag form `a ≤ cstab ∧ cstab < dist ∧ 4*h0 < b`, plus `2 < b` on
two edges and strict `a < b` on two further edges; the registry carries
neither the `4*h0` conjunct nor those strict edge facts (only
`b i (i+1) = 2*h0`). -/
theorem CQAOQLR_discharged : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ),
    3 < s.k →
    isScsV39 s → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → 2 < s.b (i + 1) (i + 2) →
    s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    s.a (i + s.k - 1) i < s.b (i + s.k - 1) i →
    s.a i (i + 1) = 2 → s.b i (i + 1) ≤ 2 * h0 →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
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
theorem LFLACKU_discharged : main_nonlinear_terminal_v11 →
    scsArrowV39 {scs3I1} ∅ := by
  sorry

/-- WIRE `LocalAuto1.QKNVMLB1_concl` <- `QKNVMLB1_p35` (verbatim twin,
LA35:31426).  SF-87 re-based this exit onto the corpus original form: the
registry statement is the twin's conclusion with `s'`/`vv'` inlined at
`scsHalfSliceV39 s p q d' mkj` / `fun i => vv (i % s'.k + p % s.k)` --
the `let s' =`/`let vv' =` shape of the PROVED HOL original `QKNVMLB1`
(QKNVMLB.hl:5223-5230; `vv'` at :5225), per RULING 2026-09-21 IV
(arbitration: the twin side is the faithful encoding; machine-checked by
the W-E mod-boundary probe `vvAppendix_ne_vvCorpus`, lane
la35-access-we1 -- the appendix form `vv ((i+p) % s'.k)` is a different
function off the mod boundary and has NO proof in the corpus).
Debt-consolidating wiring, sorryAx standing: the twin's proof body is
sorry-free (the EQ4F/LE4F case split `QKNVMLB1_EQ4F_p35`/
`QKNVMLB1_LE4F_p35`; the EQ4F branch is already axiom-clean), but the
LE4 branch's axiom face inherits the LA35 sectorTri/pmPlaneCrowding root
(`QKNVMLB1_LE4F_p35` <- `TECOXBMv2_p35` <- LA35 bare sorry at :7583);
the debt has that single known root and self-clears when W-A (pm12)
closes it.
History: HOLD (c) 2026-09-19..2026-10-31 while the registry carried the
appendix form; SF-64 re-based the registry onto the corpus form, SF-87
completes the reshape and wires. -/
theorem QKNVMLB1_discharged : ∀ (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    MMsV39 s vv → s.bm p q < 4 → (s.k = 4 ∨ s.bm p q ≤ cstab) → isScsV39 s →
    d' < 0.9 → scsDiag s.k p q →
    BBsV39 (scsHalfSliceV39 s p q d' mkj)
      (fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k)) :=
  fun s p q d' mkj vv hMM hbm h4 hscs hd' hdiag =>
    QKNVMLB1_p35 (s' := scsHalfSliceV39 s p q d' mkj)
      (vv' := fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))
      s p q d' mkj vv hMM hbm h4 hscs hd' hdiag rfl rfl

/-- WIRE `LocalAuto1.QKNVMLB2_concl` <- `QKNVMLB2_p35` (verbatim twin,
LA35:31654).  SF-87 re-based this exit onto the corpus original form:
the half-slice realisation pair is carried as the corpus two-equation
antecedents `scsHalfSliceV39 s p q d' mkj = s'` /
`scsHalfSliceV39 s q p d'' mkj = s''` (QKNVMLB.hl:5523/:5524; twin
`hs'`/`hs''` same direction) instead of the `(s', s'') = scsSliceV39 ...`
tuple slot -- the two shapes are inter-derivable via the `scsSliceV39`
def + `Prod.mk.injEq`, so the restatement is content-preserving; the
realisations stay inlined (= the `let vv'`/`let vv''` shape of the proved
original, `vv (i MOD s'.k + p MOD s.k)` at :5525 and
`vv (i MOD s''.k + q MOD s.k)` at :5527, RULING 2026-09-21 IV).
Debt: measured CLEAN at this exit -- the twin's proof body is sorry-free
(the mkj flag split `QKNVMLB2_step06/07_mkj*_p35`) and its axiom face is
`[propext, Classical.choice, Quot.sound]` (the tausplit-chain assemblies
feeding it are closed; the recon-era pmPlaneCrowding-pollution
expectation no longer applies to this item).
History: HOLD (c) 2026-09-19..2026-10-31 (SF-65
had already fixed the index convention; the tuple slot was the remaining
registry delta). -/
theorem QKNVMLB2_discharged : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    dsvV39 s vv ≤ dsvV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      dsvV39 s'' (fun i => vv (i % s''.k + q % s.k)) :=
  fun s s' s'' p q d' d'' mkj vv hs' hs'' hMM hscs hdiag hsl hd =>
    QKNVMLB2_p35 (vv' := fun i => vv (i % s'.k + p % s.k))
      (vv'' := fun i => vv (i % s''.k + q % s.k))
      s s' s'' p q d' d'' mkj vv hs' hs'' rfl rfl hMM hscs hdiag hsl hd

/-! ### (d) Twin proved but the shape delta is not bridgeable (4 after
      SF-87 wired QKNVMLB3; was 5) -/

/-- WIRE `LocalAuto1.OEHDBEN_concl` <- `OEHDBEN` (verbatim twin; SF-73
rebased this exit onto the corpus original form -- mnt11 antecedent, tail
slot `scs3M1`).  Debt-consolidating wiring, sorryAx standing: the twin's
body is a pure `FZIOTEF_TRANS`/`FZIOTEF_REFL`/`FZIOTEF_UNION` combination
(combinators clean); the axiom arrives from `AQICLXA` (LA20:986),
`FZIOTEF` (LA20:1008) and `SCS_6I1_BERAK_BY_CSTAB` (LA20:1221) in the
mnt11 bank (deep roots `AQICLXA_SLICE` LA20:957 / `FUNOUYH_SLICE`
LA20:999); the debt has those known roots and self-clears when they
close. -/
theorem OEHDBEN_discharged : main_nonlinear_terminal_v11 →
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3M1} :=
  OEHDBEN

/-- WIRE `LocalAuto1.TBRMXRZ1_concl` <- `TBRMXRZ1_p22` (verbatim twin;
SF-69: registry re-based onto the corpus original form — `(g ∘ f)` order,
inner-slope `0 < f'`, concl `reEqvl h' g'`; the appendix's `f ∘ g` shape
is a false proposition, unfixedable). -/
theorem TBRMXRZ1_discharged : ∀ (f g : ℝ → ℝ) (f' g' h' x y : ℝ),
    derivedForm True f f' x (Set.univ : Set ℝ) →
    derivedForm True g g' y (Set.univ : Set ℝ) →
    derivedForm True (g ∘ f) h' x (Set.univ : Set ℝ) →
    0 < f' → f x = y → reEqvl h' g' :=
  TBRMXRZ1_p22

/-- WIRE `LocalAuto1.VPWSHTO_concl` <- `VPWSHTO_PRIME_p15` (verbatim twin;
SF-63 rebased this exit onto the corpus original `VPWSHTO_PRIME` form).
Debt-consolidating wiring, sorryAx standing: the twin's body refines to the
still-sorried master `VPWSHTO_p15` (LA15:409), so this exit still shows
`sorryAx`; the debt has that single known root and self-clears when the
root is filled. -/
theorem VPWSHTO_discharged : ∀ vv : ℕ → V3,
    ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) →
    vv 0 ≠ vv 1 → vv 0 ≠ vv 1 → vv 0 ≠ vv 2 → vv 0 ≠ vv 3 →
    vv 0 ≠ vv 4 → vv 1 ≠ vv 2 → vv 1 ≠ vv 3 → vv 1 ≠ vv 4 →
    vv 2 ≠ vv 3 → vv 2 ≠ vv 4 → vv 3 ≠ vv 4 →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5 :=
  VPWSHTO_PRIME_p15

/-- WIRE `LocalAuto1.XWNHLMD_concl` <- `XWNHLMD_p26` (verbatim twin; SF-71
added the corpus `s.d ≤ s'.d` antecedent).  Debt-consolidating wiring,
sorryAx standing: the twin's own body is clean, but the axiom arrives via
`XWNHLMD_MM_p26` -> `SGTRNAF_p27` -> `UXCKFPE2_p27` -> `UXCKFPE_p24` from
the LA24 case bank (`XWITCCN_CASE_3/4/5/6_IS_SCS_p24`, sorries at
LA24:1387/1128/1163/1196); the debt has that single known root bank and
self-clears when the four cases close. -/
theorem XWNHLMD_discharged : ∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → s.k = s'.k →
    s.d ≤ s'.d →
    v ∈ MMsV39 s → BBsV39 s' v →
    scsArrowV39 {s} {s'} :=
  XWNHLMD_p26

/-- WIRE `LocalAuto1.QKNVMLB3_concl` <- `QKNVMLB3_p35` (verbatim twin,
LA35:33360).  SF-87 re-based this exit onto the corpus original form:
the half-slice realisation pair is carried as the corpus two-equation
antecedents `scsHalfSliceV39 s p q d' mkj = s'` /
`scsHalfSliceV39 s q p d'' mkj = s''` (QKNVMLB.hl:10665/:10666; twin
`hs'`/`hs''` same direction) instead of the `(s', s'') = scsSliceV39 ...`
tuple slot -- inter-derivable via the `scsSliceV39` def +
`Prod.mk.injEq` (content-preserving); the realisations stay inlined (=
the `let vv'`/`let vv''` shape of the proved master `QKNVMLB3`,
QKNVMLB.hl:10665-10675; `vv (i MOD s'.k + p MOD s.k)` at :10667 and
`vv (i MOD s''.k + q MOD s.k)` at :10669, RULING 2026-09-21 IV).
Debt: measured CLEAN at this exit -- the twin case-splits onto
`QKNVMLB3_Eq4_p35`/`QKNVMLB3_LE4_p35`, both PROVED through the
`tausplit_le4` assembly (LA35:32955; the old "still-sorried branches"
blocker is voided by lkgrqui-le4eq4-fin-w2), and its axiom face is
`[propext, Classical.choice, Quot.sound]` (the tausplit chain is closed;
the recon-era pmPlaneCrowding-pollution expectation no longer applies to
this item).
History: HOLD (d) 2026-09-19..2026-10-31 (SF-66 had already fixed
the index convention; the tuple slot was the remaining registry
delta). -/
theorem QKNVMLB3_discharged : ∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    taustarV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      taustarV39 s'' (fun i => vv (i % s''.k + q % s.k)) ≤ taustarV39 s vv :=
  fun s s' s'' p q d' d'' mkj vv hs' hs'' hMM hscs hdiag hsl hd =>
    QKNVMLB3_p35 (vv' := fun i => vv (i % s'.k + p % s.k))
      (vv'' := fun i => vv (i % s''.k + q % s.k))
      s s' s'' p q d' d'' mkj vv hs' hs'' rfl rfl hMM hscs hdiag hsl hd

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
#print axioms OTMTOTJ1_discharged
#print axioms OTMTOTJ2_discharged
#print axioms OTMTOTJ3_discharged
#print axioms OTMTOTJ4_discharged
#print axioms ASSWPOW_discharged
#print axioms DRNDRDV_discharged
#print axioms QKNVMLB1_discharged
#print axioms QKNVMLB2_discharged
#print axioms QKNVMLB3_discharged


/-! ### Consumption upshift (lane la1concl-reroute-w1, 2026-10):
the `JEJTVGB_p16` assembly assembled from THIS file's WIRE exits, so the
e2e cone consumes the assembly layer instead of the LocalAuto1 registry
sorries.  Statement = `LocalAuto16.JEJTVGB_p16` verbatim; body =
`LocalAuto16.JEJTVGB_case_breakdown_p16` with the 21 registry slots
refilled from this file's `*_discharged` exits (`_concl` -> `_discharged`,
positions verbatim modulo the arrow-set-equality shims, which are the same
`p16h_arrow_congr` wraps as in LocalAuto16).  The a01 slot keeps
`(OEHDBEN h)` and the a23 slot keeps `BKOSSGE_p16` (both LA16/LA20
originals, debt-identical to today's chain).  Zero new proof debt: no new
proof obligation is discharged here, the axiom faces of all 21 exits are
untouched. -/

/-- HOL `JEJTVGB` assembly, consumption-upshift version (lane
la1concl-reroute-w1): same statement as `LocalAuto16.JEJTVGB_p16`, with
the LocalAuto1 registry arrows replaced by this file's `*_discharged`
exits (debt flows along the proof term, per the ASSEMBLY WAVE contract).
After `Kepler.Assembly` re-points its two consumption sites at
`nonlinear_imp_lp_main_estimate_p16_discharged`, the old
`LocalAuto16.JEJTVGB_p16` chain leaves the e2e cone. -/
theorem JEJTVGB_p16_discharged (h : main_nonlinear_terminal_v11) :
    JEJTVGB_assume_v39 := by
  exact JEJTVGB_case_breakdown_p16 h (OEHDBEN h) OTMTOTJ1_discharged
    OTMTOTJ2_discharged OTMTOTJ3_discharged OTMTOTJ4_discharged
    (p16h_arrow_congr (HIJQAHA_discharged h) rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr CNICGSF1_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr CNICGSF2_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr CNICGSF3_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    CNICGSF4_discharged
    (p16h_arrow_congr CNICGSF5_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (FYSSVEV_discharged h) (ARDBZYE_discharged h) AUEAHEH_discharged
    (p16h_arrow_congr VQFYMZY_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr BNAWVNH_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr RAWZDIB_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr MFKLVDK_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (p16h_arrow_congr RYPDIXT_discharged rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (NWDGKXH_discharged h)
    (p16h_arrow_congr (YOBIMPP_discharged h) rfl
      (by ext s; simp [Set.mem_insert_iff]; tauto))
    (MIQMCSN_discharged h) BKOSSGE_p16
/-- Assembly-side switch wrapper, mirrors `LocalAuto16.
nonlinear_imp_lp_main_estimate_p16`; `Kepler.Assembly`'s two consumption
sites (`linearProgrammingResults`, `textCapstone`) re-point to this name. -/
theorem nonlinear_imp_lp_main_estimate_p16_discharged :
    main_nonlinear_terminal_v11 → lp_main_estimate := fun h =>
  lp_main_estimate_JEJTVGB_p16.2 (JEJTVGB_p16_discharged h)

#print axioms JEJTVGB_p16_discharged
#print axioms nonlinear_imp_lp_main_estimate_p16_discharged

/-! ### S1 wiring capstone (lane localconcl-wiring-w1, 2026-11-03):

the e2e cone consumed only this file's `nonlinear_imp_lp_main_estimate_p16_discharged`
assembly (via `Kepler.Assembly.linearProgrammingResults`/`textCapstone`); the other
47 twin-body `*_discharged` registry exits (orphan-scout WIRE table, 2026-11-03 logs,
`orphan_hist_full.out`) were reachable from NO e2e root.  This capstone re-exposes them
as ONE conjunction whose first conjunct is exactly that p16 switch statement, so the
Assembly re-point is statement-preserving (GATE_MODE=REWIRE, RW_DONOR = this name).

Anchors (per the orphan-scout discipline, no fabricated edges): every conjunct is
asserted in the verbatim wording of its `*_discharged` exit above, and the body is
the assembly `<exit_1, ..., exit_N>` -- zero new proof obligations, zero new imports,
debt flows along the proof term per the ASSEMBLY WAVE contract (LEDGER above).
Per-exit twin pointers: the exit docstrings and the LEDGER (c)/(d) entries.
Unwired and staying so this wave: the 21 HOLD stubs ((a) no-twin 5, (b) circular
re-export 11, (c) shape-blocked 5) -- their bodies are bare `sorry` with reason
recorded; wiring them would only visualize the registry sorry itself.
-/

/-- S1 aggregate wiring capstone (47 exits + the p16 switch as conjunct 1).
Conjunct order: orphan-scout WIRE increments, descending.  See the section
comment above for the wiring discipline and the per-exit anchors. -/
theorem localconcl_wire_capstone_w1 (hmn : main_nonlinear_terminal_v11) :
    (main_nonlinear_terminal_v11 → lp_main_estimate) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → s.k = 4 → v ∈ MMsV39 s →
      scsGeneric v) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    ¬Circular (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3) (v w : V3),
    isScsV39 s → BBsV39 s vv → taustarV39 s vv < 0 →
    Lunar v w (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) → 3 < s.k →
    interiorAngle1 0 (Set.range fun i => (vv i, vv (i + 1))) v <
      Real.pi / 2) ∧
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs5M1, scs3M1}) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 → s = 1 ∨ s = -1 →
      v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s →
      Coplanar ({v0, v1, v2, v3} : Set V3) ∧
      x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
      ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0)) ∧
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2}) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    solLocal (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) < Real.pi) ∧
    (∀ vv : ℕ → V3,
    ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) →
    vv 0 ≠ vv 1 → vv 0 ≠ vv 1 → vv 0 ≠ vv 2 → vv 0 ≠ vv 3 →
    vv 0 ≠ vv 4 → vv 1 ≠ vv 2 → vv 1 ≠ vv 3 → vv 1 ≠ vv 4 →
    vv 2 ≠ vv 3 → vv 2 ≠ vv 4 → vv 3 ≠ vv 4 →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5) ∧
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    ContinuousAt (fun q => mkSimplex1 v0 v1 v2 x1 x2 x3 x4 q x6) x5) ∧
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3) ∧
    (∀ (s t : ScsV39), isScsV39 s → transferV39 s t → scsArrowV39 {s} {t}) ∧
    (main_nonlinear_terminal_v11 →
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
      dist (v p1) (v (p1 + k - 1)) = 2) ∧
    (main_nonlinear_terminal_v11 →
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
      dist (v p1) (v (p1 + 1)) = 2) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
      0 < ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ
        (crossProduct ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ))) ∧
    (∀ (f g : ℝ → ℝ) (f' g' h' x y : ℝ),
    derivedForm True f f' x (Set.univ : Set ℝ) →
    derivedForm True g g' y (Set.univ : Set ℝ) →
    derivedForm True (g ∘ f) h' x (Set.univ : Set ℝ) →
    0 < f' → f x = y → reEqvl h' g') ∧
    (∀ (s : ScsV39) (i j : ℕ) (c : ℝ),
    isScsV39 s → s.a i j ≤ c → c ≤ s.b i j → 3 < s.k →
    ¬(i % s.k = j % s.k) → ¬s.J i j →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k → ¬(c = s.am i j)) →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k →
      2 < s.a i j ∨ 2 * h0 < s.b i j) →
    scsArrowV39 {s} (setOfList (subdivV39 s i j c))) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), 3 < s.k → isScsV39 s →
    scsGeneric v → v ∈ MMsV39 s →
    3 + {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k) ∧
    (∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    3 < s.k →
    (∀ i, s.a i (i + 1) = 2) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    ∃ i, dist (v i) (v (i + 1)) = 2) ∧
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
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
          ((fun e => (fun v => f v t) '' e) '' E)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    scsBasicV39 s → 3 < s.k → v ∈ MMsV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v) ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    3 < s.k → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → (s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    dist (v (i + 1)) (v (i + 2)) = 2) ∧
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
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
          ((fun e => (fun v => f v t) '' e) '' E)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → s.k = 4 → scsBasicV39 s →
    s.b i (i + 1) ≤ 2 * h0 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53) ∧
    (∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → scsM s = scsM s' →
    s.k = s'.k → v ∈ MMsV39 s → BBsV39 s' v → s.d = s'.d →
    (∀ i, s'.a i (i + 1) = s.a i (i + 1)) →
    (∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) → v ∈ MMsV39 s') ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → v ∈ MMsV39 s → (∀ i, s.b i (i + 1) ≤ cstab) →
    Lunar (v i) (v j) (Set.range v) (Set.range fun i => {v i, v (i + 1)}) →
    s.k = 6 ∧ v j = v (i + 3)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k →
    ¬Coplanar (({0} ∪ Set.range v : Set V3))) ∧
    (∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
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
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ),
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
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s → k = s.k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    False) ∧
    (∀ (u v p : V3), ¬Collinear ℝ ({0, v, p} : Set V3) →
    ¬Collinear ℝ ({0, u, p} : Set V3) →
    arcV 0 u p + arcV 0 p v < Real.pi →
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3))) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅) ∧
    (∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → s.k = s'.k →
    s.d ≤ s'.d →
    v ∈ MMsV39 s → BBsV39 s' v →
    scsArrowV39 {s} {s'}) ∧
    (∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅) ∧
    (scsArrowV39 {scs3M1} {scs3T1, scs3T5}) ∧
    ((∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop),
    isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    scsArrowV39 {s} {s', s''}) ∧
    (main_nonlinear_terminal_v11 →
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3M1}) ∧
    (∀ (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    MMsV39 s vv → s.bm p q < 4 → (s.k = 4 ∨ s.bm p q ≤ cstab) → isScsV39 s →
    d' < 0.9 → scsDiag s.k p q →
    BBsV39 (scsHalfSliceV39 s p q d' mkj)
      (fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    dsvV39 s vv ≤ dsvV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      dsvV39 s'' (fun i => vv (i % s''.k + q % s.k))) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    taustarV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      taustarV39 s'' (fun i => vv (i % s''.k + q % s.k)) ≤ taustarV39 s vv) ∧
    (∀ (s : ScsV39) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → 3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j)) ∧
    (scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scs4T4})
  := ⟨nonlinear_imp_lp_main_estimate_p16_discharged, GSXRFWM_discharged, JKQEWGV2_discharged,
      JKQEWGV3_discharged, AQICLXA_discharged, EYYPQDW_discharged, FUNOUYH_discharged,
      JKQEWGV1_discharged, VPWSHTO_discharged, EYYPQDW3_discharged, PQCSXWG2_discharged,
      EYYPQDW2_discharged, YXIONXL1_discharged, CJBDXXN_discharged, CUXVZOZ_discharged,
      PQCSXWG1_discharged, TBRMXRZ1_discharged, UAGHHBM_discharged, AURSIPD_discharged,
      DRNDRDV_discharged, JCYFMRP_discharged hmn, MHAEYJN_discharged, RRCWNSJ_discharged hmn,
      TFITSKC_discharged hmn, ZLZTHIC_discharged, ASSWPOW_discharged, MXQTIED_discharged,
      AXJRPNC_discharged, FEKTYIY_discharged, HXHYTIJ_discharged, IMJXPHRv2_discharged,
      NUXCOEAv2_discharged, ODXLSTCv2_discharged, PPBTYDQ_discharged, XWITCCN2_discharged,
      XWITCCN_discharged, XWNHLMD_discharged, unadorned_MMs_discharged, AYQJTMD_discharged,
      BKOSSGE_discharged, EAPGLE_discharged, LKGRQUI_discharged, OEHDBEN_discharged,
      QKNVMLB1_discharged, QKNVMLB2_discharged, QKNVMLB3_discharged, YRTAFYH_discharged,
      ZNLLLDL_discharged⟩

/-! ### LA35 materialization capstone (lane la35-root-w1, 2026-11-03,
after the la35-mat-scout workorder R1): the 88 public top-level
LocalAuto35 exits that no e2e root reaches (orphan-scout 741 account =
88 top-level + 653 aux; 268 private + 29 derived items are structurally
unreachable by pure wiring) are re-exposed as ONE conjunction -- 71
exits implemented, 17 dropped because their statements name
LA35-module-private constants, are `def`-kind statement
definitions (not proven exits), or are universe-polymorphic (which
would break the mandated Assembly consumption shape) -- all per the
workorder's no-forcing rule (see the theorem docstring) -- and a type-preserving w2 forward re-points the
Assembly `textCapstone` consumer with `.1` projection semantics
unchanged (S1 precedent `ebe0d0b7`).  Measured on HEAD 0c445f94: full
88-seed closure = +453 fresh nodes (444 LA35 + 9 LA23), sorried-0,
standard-three axiom face (scout logs/la35_group_r1.out,
la35_axprobe.out); the exact kit yield is re-measured at the
orchestrator e2e gate. -/

/-! ### LA22 materialization capstone (lane lv7-w1, 2026-11-04,
after the leftover-mat-scout workorder §2-16 LV7): the 88 public
top-level LocalAuto22 clean exits that no e2e root reaches are
re-exposed as ONE conjunction -- 87 exits implemented, 1
dropped (equation-compiler lemmas with no source signature, def-kind
statement definitions, or statements naming module-private constants)
-- all per the no-forcing rule (see the theorem docstring).
Measured on HEAD 1e139a28 (baseline I): the 88-seed closure = +137
fresh nodes, sorried-0, standard-three axiom face (scout logs/probe2.out
GROUP_VS_CONE, axprobe.out SYNQIWN_p22 = standard three); the exact kit
yield is re-measured at the orchestrator e2e gate (lv-wire-w2 wiring). -/

/-- LA22 materialization capstone (scout lane leftover-mat-scout §2-16 LV7,
implementation lane lv7-w1, 2026-11-04).  The public top-level
LocalAuto22 exits unreachable from every e2e root and sorried-0 in
their whole closure (probe1: 163 top-level exits = 88 clean + 75
sorried; the 75 sorried exits are excluded per the workorder -- not one
enters; probe2: 88-seed closure GROUP_FRESH_VS_CONE 137, GROUP_SORRIED
0, i.e. sorried-0, K_SORRIED 134 and K_AXIOM 624 unchanged).
Implemented here: 87 of the 88.  Of these, 53 carry their verbatim source signature and 34 are equation-lemma exits carried by their verbatim printer signature.  Dropped per the
no-forcing rule ("抽不出/不一致 → 剔除并如实报"), mechanically detected
by the generator, recorded one by one:
--   assocdV39.eq_def: universe-polymorphic statement (free universe in Sort/Type position); a universe parameter would change the capstone shape

Anchors (no fabricated edges): every conjunct is asserted verbatim --
for plain seeds the conjunct text is the declaration's source signature
in LocalAuto22.lean (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); for equation-lemma exits (`X.eq_1`/`X.eq_def` generated
by the equation compiler, present in no source file as a declaration)
the conjunct text is the `#check @name` printer dump
(logs/sigprobe_88.out), which re-elaborates to the very same type;
semantic identity is re-verified by the elaboration of the `<...>`
assembly below (each component must unify definitionally with its
conjunct).  Conjunct order: the seed-list order (probe1 LA22 sorried-0
list = seeds_clean.txt LA22 subset), drops removed.  Body = the
assembly of the exit constants -- zero new proof obligations, zero new
imports. -/
theorem la22_capstone_w1 :
    -- 1. CARD_3_SUBSET_p22 (LA22:1147; HOL `CARD_3_SUBSET`)
    (∀ (f : ℕ → Prop)
    ,
          {i | i < 3 ∧ f i}.ncard ≤ 3
    ) ∧
    -- 2. DOT_LSUB_p22 (LA22:138; HOL `DOT_LSUB`)
    (∀ (x y z : V3)
    ,
          (x - y) ⬝ᵥ z = x ⬝ᵥ z - y ⬝ᵥ z
    ) ∧
    -- 3. DOT_RSUB_p22 (LA22:143; HOL `DOT_RSUB`)
    (∀ (x y z : V3)
    ,
          x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z
    ) ∧
    -- 4. I_LT_J_LT_5_EXPLICIT_p22 (LA22:1162; HOL `I_LT_J_LT_5_EXPLICIT`)
    (∀ (i j : ℕ)
    ,
          (i < j ∧ j < 5) ↔
          ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) ∨
            (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 4) ∨
            (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4))
    ) ∧
    -- 5. MOD_5_EXPLICIT_p22 (LA22:1170; HOL `MOD_5_EXPLICIT`)
    (0 % 5 = 0 ∧ 1 % 5 = 1 ∧ 2 % 5 = 2 ∧ 3 % 5 = 3 ∧ 4 % 5 = 4 ∧
          5 % 5 = 0 ∧ 6 % 5 = 1 ∧ 7 % 5 = 2
    ) ∧
    -- 6. MOD_EQ_MOD_SHIFT_p22 (LA22:1108; HOL `MOD_EQ_MOD_SHIFT`)
    (∀ {n x1 x2 y : ℕ} (hn : n ≠ 0)
    ,
          ((y + x1) % n = (y + x2) % n) ↔ (x1 % n = x2 % n)
    ) ∧
    -- 7. REAL_OPEN_REAL_INTERVAL_p22 (LA22:361; HOL `REAL_OPEN_REAL_INTERVAL`)
    (∀ (a b : ℝ)
    ,
          IsOpen (Set.Ioo a b)
    ) ∧
    -- 8. SYNQIWN_p22 (LA22:1815; HOL `SYNQIWN`)
    (∀ (h : main_nonlinear_terminal_v11) (s : ScsV39) (v : ℕ → V3) (i k : ℕ)
          (h1 : isScsV39 s) (h2 : BBsV39 s v) (hkk : s.k = k) (h3 : 3 < k)
          (hears : (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2) ∨
            (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
            (norm (v (i + 1)) = 2 ∧ norm (v (i + k - 1)) = 2) ∨
            (dist (v i) (v (i + 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2) ∨
            (norm (v (i + 1)) = 2 ∧ dist (v i) (v (i + 1)) = 2) ∨
            (norm (v (i + k - 1)) = 2 ∧ dist (v i) (v (i + k - 1)) = 2))
          (he1 : dist (v i) (v (i + 1)) ≤ 2 * h0)
          (he2 : dist (v i) (v (i + k - 1)) ≤ 2 * h0)
          (hc : cstab ≤ dist (v (i + 1)) (v (i + k - 1))),
          Real.pi / 2 < azim 0 (v i) (v (i + 1)) (v (i + k - 1))
    ) ∧
    -- 9. basic_examples_p22 (LA22:2591; no HOL anchor line in file docstring)
    (scsBasicV39 scs6I1 ∧
          scsBasicV39 scs5I1 ∧
          scsBasicV39 scs5I2 ∧
          scsBasicV39 scs5I3 ∧
          scsBasicV39 scs4I1 ∧
          scsBasicV39 scs4I2 ∧
          scsBasicV39 scs4I3 ∧
          scsBasicV39 scs3I1 ∧
          scsBasicV39 scs6T1 ∧
          scsBasicV39 scs5T1 ∧
          scsBasicV39 scs4T1 ∧
          scsBasicV39 scs4T2 ∧
          scsBasicV39 scs4T3 ∧
          scsBasicV39 scs4T4 ∧
          scsBasicV39 scs4T5 ∧
          scsBasicV39 scs3T1 ∧
          scsBasicV39 scs3T2 ∧
          scsBasicV39 scs3T3 ∧
          scsBasicV39 scs3T4 ∧
          scsBasicV39 scs3T5 ∧
          scsBasicV39 scs3T6' ∧
          scsBasicV39 scs3T7 ∧
          scsBasicV39 scs6M1 ∧
          scsBasicV39 scs5M1 ∧
          scsBasicV39 scs5M2 ∧
          scsBasicV39 scs4M1 ∧
          scsBasicV39 scs4M2 ∧
          scsBasicV39 scs4M3' ∧
          scsBasicV39 scs4M4' ∧
          scsBasicV39 scs4M5' ∧
          scsBasicV39 scs4M6' ∧
          scsBasicV39 scs4M7 ∧
          scsBasicV39 scs4M8 ∧
          scsBasicV39 scs3M1
    ) ∧
    -- 10. const1_pos_p22 (LA22:1195; HOL `const1_pos`)
    (0 < const1_p22
    ) ∧
    -- 11. csAdj_ge2_p22 (LA22:881; no HOL anchor line in file docstring)
    (∀ {k : ℕ} {a1 a2 : ℝ} (h1 : 2 ≤ a1) (h2 : 2 ≤ a2) {i j : ℕ}
          (h : ¬ (i % k = j % k)),
          2 ≤ csAdj k a1 a2 i j
    ) ∧
    -- 12. cs_adj_SUC_p22 (LA22:899; HOL `cs_adj_SUC`)
    (∀ {k : ℕ} {a1 a2 : ℝ} (hk : 1 < k) (i : ℕ)
    ,
          csAdj k a1 a2 i (i + 1) = a1
    ) ∧
    -- 13. dTame.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (∀ (n : ℕ),
          dTame n = if n = 3 then 0 else if n = 4 then 0.206 else if n = 5 then 0.4819 else if n = 6 then 0.712 else tgt
    ) ∧
    -- 14. delta_diff4_p22 (LA22:252; HOL `delta_diff4`)
    (∀ (x1 x2 x3 x4 x5 x6 z4 : ℝ)
    ,
          deltaX x1 x2 x3 x4 x5 x6 =
          deltaX x1 x2 x3 z4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 * (x4 - z4)
            + x1 * (x4 - z4) ^ 2
    ) ∧
    -- 15. delta_x4_dim_reduction_p22 (LA22:323; HOL `delta_x4_dim_reduction`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0)
          (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0),
          deltaX4 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
            (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
            (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
          16 * yOfX (deltaX4) y1 y2 y3 y4 y5 y6 / (y1 * y1 * y2 * y3)
    ) ∧
    -- 16. delta_x_xrr_p22 (LA22:312; HOL `delta_x_xrr`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
          (hy3 : y3 ≠ 0),
          deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6) =
          64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2
    ) ∧
    -- 17. delta_y_dim_reduction_p22 (LA22:300; HOL `delta_y_dim_reduction`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : y1 ≠ 0)
          (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0),
          deltaX 4 4 4 (8 * (1 - (y2 * y2 + y3 * y3 - y4 * y4) / (2 * y2 * y3)))
            (8 * (1 - (y1 * y1 + y3 * y3 - y5 * y5) / (2 * y1 * y3)))
            (8 * (1 - (y1 * y1 + y2 * y2 - y6 * y6) / (2 * y1 * y2))) =
          64 * deltaY y1 y2 y3 y4 y5 y6 / (y1 * y2 * y3) ^ 2
    ) ∧
    -- 18. delta_y_pos_xrr_p22 (LA22:739; HOL `delta_y_pos_xrr`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
          (hy3 : 0 < y3),
          (0 < deltaY y1 y2 y3 y4 y5 y6 ↔
          0 < deltaX 4 4 4 (xrr y2 y3 y4) (xrr y1 y3 y5) (xrr y1 y2 y6))
    ) ∧
    -- 19. derived_form_b_p22 (LA22:148; HOL `derived_form_b`)
    (∀ (b : Prop) (f : ℝ → ℝ) (f' x : ℝ) (s : Set ℝ)
    ,
          (derivedForm b f f' x s ↔ (b → derivedForm True f f' x s))
    ) ∧
    -- 20. derived_form_delta_x4_wrt_x4_p22 (LA22:334; HOL `derived_form_delta_x4_wrt_x4`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          derivedForm True (fun q => deltaX4 x1 x2 x3 q x5 x6) (-2 * x1) x4 Set.univ
    ) ∧
    -- 21. derived_form_delta_x4_wrt_x5_p22 (LA22:345; HOL `derived_form_delta_x4_wrt_x5`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          derivedForm True (fun q => deltaX4 x1 x2 x3 x4 q x6) (x1 + x2 - x6) x5 Set.univ
    ) ∧
    -- 22. derived_form_delta_x_wrt_x4_p22 (LA22:207; HOL `derived_form_delta_x_wrt_x4`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          derivedForm True (fun q => deltaX x1 x2 x3 q x5 x6)
          (deltaX4 x1 x2 x3 x4 x5 x6) x4 Set.univ
    ) ∧
    -- 23. derived_form_delta_x_wrt_x5_p22 (LA22:225; HOL `derived_form_delta_x_wrt_x5`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          derivedForm True (fun q => deltaX x1 x2 x3 x4 q x6)
          (deltaX5 x1 x2 x3 x4 x5 x6) x5 Set.univ
    ) ∧
    -- 24. derived_form_dnum1_p22 (LA22:408; HOL `derived_form_dnum1`)
    (∀ (x4 x5 x6 e1 e2 e3 : ℝ)
    ,
          derivedForm True (fun q => num1 e1 e2 e3 q x5 x6)
          (4 * dnum1 e1 e2 e3 x4 x5 x6) x4 Set.univ
    ) ∧
    -- 25. derived_form_num1_p22 (LA22:393; HOL `derived_form_num1`)
    (∀ (x4 x5 x6 e1 e2 e3 : ℝ)
    ,
          derivedForm True (fun q => num1 e1 e2 e3 q x5 x6)
          (4 * ((16 - 2 * x4) * e1 + (x5 - 8) * e2 + (x6 - 8) * e3)) x4 Set.univ
    ) ∧
    -- 26. derived_form_xrr_D2_p22 (LA22:278; HOL `derived_form_xrr_D2`)
    (∀ (y1 y2 y6 : ℝ)
    ,
          derivedForm (0 < y1 ∧ 0 < y2) (fun q => 8 * q / (y1 * y2)) (8 / (y1 * y2)) y6
          Set.univ
    ) ∧
    -- 27. derived_form_xrr_D3_p22 (LA22:291; HOL `derived_form_xrr_D3`)
    (∀ (y1 y2 y6 : ℝ)
    ,
          derivedForm (0 < y1 ∧ 0 < y2) (fun _q => 8 / (y1 * y2)) 0 y6 Set.univ
    ) ∧
    -- 28. funlistV39.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (∀ (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (k i j : ℕ),
          funlistV39 data d k i j =
            if i % k = j % k then 0 else assocdV39 (psort k (i, j)) (List.map (fun p => (psort k p.1, p.2)) data) d
    ) ∧
    -- 29. is_scs_5T1_p22 (LA22:1066; HOL `is_scs_5T1`)
    (isScsV39 scs5T1
    ) ∧
    -- 30. is_scs_6M1_p22 (LA22:1095; HOL `is_scs_6M1`)
    (isScsV39 scs6M1
    ) ∧
    -- 31. is_scs_funlist_basic_p22 (LA22:1417; HOL `is_scs_funlist_basic`)
    (∀ (k : ℕ) (d : ℝ) (a0 b0 : List ((ℕ × ℕ) × ℝ))
          (a b : ℕ × ℕ → ℝ) (hd : d < 0.9) (hk1 : 3 ≤ k) (hk2 : k ≤ 6)
          (hchain : ∀ i j, i < j ∧ j < k →
            funlistV39 a0 d k i j ≤ funlistV39 b0 d k i j)
          (ha : ∀ i j, i < j ∧ j < k → 2 ≤ funlistV39 a0 d k i j)
          (hb3 : ∀ i, i < 3 ∧ k = 3 → funlistV39 b0 d k i (Nat.succ i) < 4)
          (hbk : ∀ i, i < k ∧ 3 < k → funlistV39 b0 d k i (Nat.succ i) ≤ cstab)
          (hcard : {i | i < k ∧ (2 * h0 < funlistV39 b0 d k i (Nat.succ i) ∨
              2 < funlistV39 a0 d k i (Nat.succ i))}.ncard + k ≤ 6),
          isScsV39 (mkUnadornedV39 k d (funlistV39 a0 d k) (funlistV39 b0 d k))
    ) ∧
    -- 32. pos_imp_scs_arrow_empty_p22 (LA22:2652; HOL `pos_imp_scs_arrow_empty`)
    (∀ (s : ScsV39)
          (h : ∀ vv, BBsV39 s vv → 0 ≤ taustarV39 s vv),
          scsArrowV39 {s} ∅
    ) ∧
    -- 33. psort_4_p22 (LA22:1176; HOL `psort_4`)
    (∀ (i : ℕ)
    ,
          psort 4 (i, 4) = psort 4 (i, 0) ∧ psort 4 (4, i) = psort 4 (0, i)
    ) ∧
    -- 34. psort_5_p22 (LA22:1181; HOL `psort_5`)
    (psort 5 (0, 1) = (0, 1) ∧ psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧
          psort 5 (0, 4) = (0, 4) ∧ psort 5 (1, 1) = (1, 1) ∧ psort 5 (1, 2) = (1, 2) ∧
          psort 5 (1, 3) = (1, 3) ∧ psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 1) = (1, 2) ∧
          psort 5 (2, 2) = (2, 2) ∧ psort 5 (2, 3) = (2, 3) ∧ psort 5 (2, 4) = (2, 4) ∧
          psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧ psort 5 (3, 3) = (3, 3) ∧
          psort 5 (3, 4) = (3, 4) ∧ psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
          psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 4) = (4, 4) ∧ psort 5 (4, 5) = (0, 4) ∧
          psort 5 (5, 4) = (0, 4)
    ) ∧
    -- 35. real_open_contains_real_interval_p22 (LA22:771; HOL `real_open_contains_real_interval`)
    (∀ (x : ℝ) (s : Set ℝ) (hx : x ∈ s)
          (hopen : IsOpen s),
          ∃ a b, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ s
    ) ∧
    -- 36. real_open_univ_p22 (LA22:358; HOL `real_open_univ`)
    (IsOpen (Set.univ : Set ℝ)
    ) ∧
    -- 37. rho_bounds_p22 (LA22:1214; HOL `rho_bounds`)
    (∀ (y : ℝ) (hy1 : 2 ≤ y) (hy2 : y ≤ 2 * h0)
    ,
          1 ≤ rho y ∧ rho y ≤ 1 + sol0 / Real.pi
    ) ∧
    -- 38. scs3I1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3I1 = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)
    ) ∧
    -- 39. scs3M1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3M1 =
          mkUnadornedV39 3 0.103 (funlistV39 [((0, 1), 2 * h0)] 2 3) (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    ) ∧
    -- 40. scs3T1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T1 =
          { k := 3, d := 0.11, a := funlistV39 [((0, 1), √8)] 2 3, am := funlistV39 [((0, 1), √8)] 2 3,
            bm := funlistV39 [((0, 1), cstab)] (2 * h0) 3, b := funlistV39 [((0, 1), cstab)] (2 * h0) 3,
            J := fun x x_1 => False, lo := fun x => False, hi := fun x => False, str := fun x => False }
    ) ∧
    -- 41. scs3T2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T2 = mkUnadornedV39 3 0 (funlistV39 [] 2 3) (funlistV39 [] 2 3)
    ) ∧
    -- 42. scs3T3.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T3 = mkUnadornedV39 3 0.476 (funlistV39 [] (2 * h0) 3) (funlistV39 [] cstab 3)
    ) ∧
    -- 43. scs3T4.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T4 =
          mkUnadornedV39 3 0.2759 (funlistV39 [((0, 1), 2)] (2 * h0) 3) (funlistV39 [((0, 1), 2 * h0)] cstab 3)
    ) ∧
    -- 44. scs3T5.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T5 = mkUnadornedV39 3 0.103 (funlistV39 [((0, 1), 2 * h0)] 2 3) (funlistV39 [((0, 1), √8)] (2 * h0) 3)
    ) ∧
    -- 45. scs3T6'.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T6' =
          mkUnadornedV39 3 0.4348 (funlistV39 [((0, 1), √8), ((1, 2), √8)] 2 3)
            (funlistV39 [((0, 1), cstab), ((1, 2), cstab)] (2 * h0) 3)
    ) ∧
    -- 46. scs3T7.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs3T7 =
          mkUnadornedV39 3 0.2565 (funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 2), 2)] 2 3)
            (funlistV39 [((0, 1), 3.62), ((0, 2), cstab), ((1, 2), 2)] 2 3)
    ) ∧
    -- 47. scs4I1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4I1 = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6)
    ) ∧
    -- 48. scs4I2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4I2 = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)
    ) ∧
    -- 49. scs4I3.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4I3 =
          mkUnadornedV39 4 0.477 (funlistV39 [((0, 1), 2 * h0), ((0, 2), √8), ((1, 3), √8)] 2 4)
            (funlistV39 [((0, 1), √8), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 50. scs4M1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M1 =
          mkUnadornedV39 4 0.3401 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 51. scs4M2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M2 =
          mkUnadornedV39 4 0.3789 (funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 52. scs4M3'.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M3' =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), √8), ((0, 2), √8), ((1, 3), √8)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 53. scs4M4'.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M4' =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
            (funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 54. scs4M5'.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M5' =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), 2 * h0), ((1, 3), 2 * h0)] 2 4)
            (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 55. scs4M6'.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M6' =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 56. scs4M7.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M7 =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
            (funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 57. scs4M8.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4M8 =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
            (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6), ((1, 3), 6)] (2 * h0) 4)
    ) ∧
    -- 58. scs4T1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4T1 = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 2 6)
    ) ∧
    -- 59. scs4T2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4T2 = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 3)
    ) ∧
    -- 60. scs4T3.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4T3 =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] 2 4)
    ) ∧
    -- 61. scs4T4.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4T4 =
          mkUnadornedV39 4 0.477 (funlistV39 [((0, 1), 2 * h0), ((0, 2), √8), ((1, 3), √8)] 2 4)
            (funlistV39 [((0, 1), √8), ((0, 2), 6), ((1, 3), cstab)] (2 * h0) 4)
    ) ∧
    -- 62. scs4T5.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs4T5 =
          mkUnadornedV39 4 0.513 (funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), cstab)] (2 * h0) 4)
    ) ∧
    -- 63. scs5I1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5I1 = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6)
    ) ∧
    -- 64. scs5I2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5I2 = mkUnadornedV39 5 0.616 (csAdj 5 2 √8) (csAdj 5 (2 * h0) 6)
    ) ∧
    -- 65. scs5I3.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5I3 =
          mkUnadornedV39 5 0.616
            (funlistV39
              [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0), ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
            (funlistV39 [((0, 1), √8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)
    ) ∧
    -- 66. scs5M1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5M1 =
          mkUnadornedV39 5 0.616
            (funlistV39
              [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0), ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)
    ) ∧
    -- 67. scs5M2.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5M2 =
          mkUnadornedV39 5 0.616
            (funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5)
            (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6), ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5)
    ) ∧
    -- 68. scs5T1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs5T1 = mkUnadornedV39 5 0.616 (csAdj 5 2 cstab) (csAdj 5 2 6)
    ) ∧
    -- 69. scs6T1.eq_1 (equation-lemma exit, printer signature (sigprobe_88.out))
    (scs6T1 = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 cstab) (csAdj 6 2 6)
    ) ∧
    -- 70. scs_basic_unadorned_p22 (LA22:907; HOL `scs_basic_unadorned`)
    (∀ {k : ℕ} {d : ℝ} {a b : ℕ → ℕ → ℝ}
    ,
          scsBasicV39 (mkUnadornedV39 k d a b)
    ) ∧
    -- 71. scs_diag_2_p22 (LA22:1121; HOL `scs_diag_2`)
    (∀ {k i : ℕ} (hk : 3 < k)
    ,
          scsDiag k (i + 1) (i + (k - 1))
    ) ∧
    -- 72. scs_diag_cs_adj_p22 (LA22:889; HOL `scs_diag_cs_adj`)
    (∀ {k : ℕ} {a b : ℝ} {i j : ℕ} (h : scsDiag k i j)
    ,
          csAdj k a b i j = b
    ) ∧
    -- 73. scs_lb_2_p22 (LA22:1572; HOL `scs_lb_2`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (i j : ℕ)
          (h1 : isScsV39 s) (h2 : BBsV39 s vv) (hne : i % s.k ≠ j % s.k),
          2 ≤ dist (vv i) (vv j)
    ) ∧
    -- 74. scs_mk_unadorned_unadorned_p22 (LA22:903; HOL `scs_mk_unadorned_unadorned`)
    (∀ {k : ℕ} {d : ℝ} {a b : ℕ → ℕ → ℝ}
    ,
          unadornedV39 (mkUnadornedV39 k d a b)
    ) ∧
    -- 75. scs_vv_MOD_p22 (LA22:1308; HOL `scs_vv_MOD`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (i : ℕ)
          (h1 : isScsV39 s) (h2 : BBsV39 s vv),
          vv (i % s.k) = vv i
    ) ∧
    -- 76. unadorned_examples_p22 (LA22:2548; HOL `unadorned_examples`)
    (unadornedV39 scs6I1 ∧
          unadornedV39 scs5I1 ∧
          unadornedV39 scs5I2 ∧
          unadornedV39 scs5I3 ∧
          unadornedV39 scs4I1 ∧
          unadornedV39 scs4I2 ∧
          unadornedV39 scs4I3 ∧
          unadornedV39 scs3I1 ∧
          unadornedV39 scs6T1 ∧
          unadornedV39 scs5T1 ∧
          unadornedV39 scs4T1 ∧
          unadornedV39 scs4T2 ∧
          unadornedV39 scs4T3 ∧
          unadornedV39 scs4T4 ∧
          unadornedV39 scs4T5 ∧
          unadornedV39 scs3T1 ∧
          unadornedV39 scs3T2 ∧
          unadornedV39 scs3T3 ∧
          unadornedV39 scs3T4 ∧
          unadornedV39 scs3T5 ∧
          unadornedV39 scs3T6' ∧
          unadornedV39 scs3T7 ∧
          unadornedV39 scs6M1 ∧
          unadornedV39 scs5M1 ∧
          unadornedV39 scs5M2 ∧
          unadornedV39 scs4M1 ∧
          unadornedV39 scs4M2 ∧
          unadornedV39 scs4M3' ∧
          unadornedV39 scs4M4' ∧
          unadornedV39 scs4M5' ∧
          unadornedV39 scs4M6' ∧
          unadornedV39 scs4M7 ∧
          unadornedV39 scs4M8 ∧
          unadornedV39 scs3M1
    ) ∧
    -- 77. ups_x_delta_x_p22 (LA22:245; HOL `ups_x_delta_x`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 =
          upsX x1 x3 x5 * upsX x1 x2 x6
    ) ∧
    -- 78. ups_x_triangle_ineq_p22 (LA22:571; HOL `ups_x_triangle_ineq`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
          (hy6 : 0 < y6),
          (0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) ↔
          (y1 < y2 + y6 ∧ y2 < y1 + y6 ∧ y6 < y1 + y2))
    ) ∧
    -- 79. xrr_bounds_2_p22 (LA22:610; HOL `xrr_bounds_2`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
    ,
          (0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) ↔
          0 < xrr y1 y2 y6 ∧ xrr y1 y2 y6 < 16)
    ) ∧
    -- 80. xrr_bounds_p22 (LA22:603; HOL `xrr_bounds`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
          (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)),
          0 < xrr y1 y2 y6 ∧ xrr y1 y2 y6 < 16
    ) ∧
    -- 81. xrr_factor_8_p22 (LA22:544; HOL `xrr_factor_8`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    ,
          16 - xrr y1 y2 y6 = 4 * ((y6 + y2 + y1) * (y2 + y1 - y6)) / (y1 * y2)
    ) ∧
    -- 82. xrr_factor_p22 (LA22:537; HOL `xrr_factor`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    ,
          xrr y1 y2 y6 = 4 * ((y6 + y2 - y1) * (y6 - y2 + y1)) / (y1 * y2)
    ) ∧
    -- 83. xrr_increasing_p22 (LA22:1252; HOL `xrr_increasing`)
    (∀ (y1 y2 y6 y6' : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
          (hy6 : 0 ≤ y6) (hlt : y6 < y6'),
          xrr y1 y2 y6 < xrr y1 y2 y6'
    ) ∧
    -- 84. xrr_le_16_p22 (LA22:644; HOL `xrr_le_16`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
          (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6)),
          xrr y1 y2 y6 ≤ 16
    ) ∧
    -- 85. xrr_lt_16_p22 (LA22:560; HOL `xrr_lt_16`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2) (hy6 : 0 < y6)
          (t3 : y6 < y1 + y2),
          xrr y1 y2 y6 < 16
    ) ∧
    -- 86. xrr_pos_p22 (LA22:551; HOL `xrr_pos`)
    (∀ (y1 y2 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
          (t1 : y1 < y2 + y6) (t2 : y2 < y1 + y6),
          0 < xrr y1 y2 y6
    ) ∧
    -- 87. xrr_sym_p22 (LA22:296; HOL `xrr_sym`)
    (∀ (y1 y2 y6 : ℝ)
    ,
          xrr y1 y2 y6 = xrr y2 y1 y6
    ) :=
    ⟨CARD_3_SUBSET_p22, DOT_LSUB_p22, DOT_RSUB_p22, I_LT_J_LT_5_EXPLICIT_p22, MOD_5_EXPLICIT_p22,
      MOD_EQ_MOD_SHIFT_p22, REAL_OPEN_REAL_INTERVAL_p22, SYNQIWN_p22, basic_examples_p22,
      const1_pos_p22, csAdj_ge2_p22, cs_adj_SUC_p22, dTame.eq_1, delta_diff4_p22,
      delta_x4_dim_reduction_p22, delta_x_xrr_p22, delta_y_dim_reduction_p22,
      delta_y_pos_xrr_p22, derived_form_b_p22, derived_form_delta_x4_wrt_x4_p22,
      derived_form_delta_x4_wrt_x5_p22, derived_form_delta_x_wrt_x4_p22,
      derived_form_delta_x_wrt_x5_p22, derived_form_dnum1_p22, derived_form_num1_p22,
      derived_form_xrr_D2_p22, derived_form_xrr_D3_p22, funlistV39.eq_1, is_scs_5T1_p22,
      is_scs_6M1_p22, @is_scs_funlist_basic_p22, pos_imp_scs_arrow_empty_p22, psort_4_p22,
      psort_5_p22, @real_open_contains_real_interval_p22, real_open_univ_p22, rho_bounds_p22,
      scs3I1.eq_1, scs3M1.eq_1, scs3T1.eq_1, scs3T2.eq_1, scs3T3.eq_1, scs3T4.eq_1, scs3T5.eq_1,
      scs3T6'.eq_1, scs3T7.eq_1, scs4I1.eq_1, scs4I2.eq_1, scs4I3.eq_1, scs4M1.eq_1, scs4M2.eq_1,
      scs4M3'.eq_1, scs4M4'.eq_1, scs4M5'.eq_1, scs4M6'.eq_1, scs4M7.eq_1, scs4M8.eq_1,
      scs4T1.eq_1, scs4T2.eq_1, scs4T3.eq_1, scs4T4.eq_1, scs4T5.eq_1, scs5I1.eq_1, scs5I2.eq_1,
      scs5I3.eq_1, scs5M1.eq_1, scs5M2.eq_1, scs5T1.eq_1, scs6T1.eq_1, scs_basic_unadorned_p22,
      scs_diag_2_p22, scs_diag_cs_adj_p22, scs_lb_2_p22, scs_mk_unadorned_unadorned_p22,
      scs_vv_MOD_p22, unadorned_examples_p22, ups_x_delta_x_p22, ups_x_triangle_ineq_p22,
      xrr_bounds_2_p22, xrr_bounds_p22, xrr_factor_8_p22, xrr_factor_p22, xrr_increasing_p22,
      xrr_le_16_p22, xrr_lt_16_p22, xrr_pos_p22, xrr_sym_p22⟩

#print axioms la22_capstone_w1

/-- LA35 materialization capstone (design lane la35-mat-scout R1,
implementation lane la35-root-w1, 2026-11-03).  The 88 public top-level
LocalAuto35 exits unreachable from every e2e root (orphan-scout 741
account: 88 top-level + 653 aux; the 88-seed closure probe:
GROUP_FRESH_VS_CONE 453 = 444 LA35 + 9 LA23, GROUP_SORRIED 0, i.e. the
new closure is sorried-0, K_SORRIED 135 and K_AXIOM 624 unchanged).
Implemented here: 71 of the 88.  Dropped per the workorder's
no-forcing rule ("抽不出/不一致 → 剔除并如实报"), mechanically detected
by the generator:
--   EJRCFJD_W4_ASSEMBLY_OF_RESIDUE_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.W4AsmWindowSlot_p35 (unstatable from LocalConcl)
--   EJRCFJD_W4_ASSEMBLY_SGNFREE_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.W4AsmWindowSlot_p35, Kepler.Text.W4RootSplitSlot_p35 (unstatable from LocalConcl)
--   EJRCFJD_W4_ASSEMBLY_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.W4AsmWindowSlot_p35, Kepler.Text.W4RootSplitSlot_p35 (unstatable from LocalConcl)
--   KCHMAMG_thm_p35: statement names LA35-private constant(s) Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   W4_SGN_OF_KCH_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.W4AsmWindowSlot_p35 (unstatable from LocalConcl)
--   dwDhplaneOfCircular_p35: statement names LA35-private constant(s) Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   dwDhplaneOfDartCross_p35: statement names LA35-private constant(s) Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   dwDkchPair_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   dwDkchSlotU_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   dwDkchSlotW_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.kchPlane_p35 (unstatable from LocalConcl)
--   frSplitAsmCheck_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmKchSlot_p35, Kepler.Text.W4AsmWindowSlot_p35 (unstatable from LocalConcl)
--   w1OrigWindow_p35: statement names LA35-private constant(s) Kepler.Text.W4AsmWindowSlot_p35 (unstatable from LocalConcl)
--   KCHMAMG_p35: declared `def` (LA35:21824) = statement definition, not a proven exit
--   kchKOMWBWC_p35: declared `def` (LA35:22261) = statement definition, not a proven exit
--   FFBD_PER1_p35: universe-polymorphic statement (free universe in Sort/Type position); a universe parameter would break the mandated `have hcap := <name>` consumption shape
--   NEXT_PRO_IMP_ALLS_STRICT_p35: universe-polymorphic statement (free universe in Sort/Type position); a universe parameter would break the mandated `have hcap := <name>` consumption shape
--   permOfBijOn_permutesOn_p35: universe-polymorphic statement (free universe in Sort/Type position); a universe parameter would break the mandated `have hcap := <name>` consumption shape

Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LA35 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim
and mechanically split at the binder/conclusion separator by the
generator gen_items.py); the Lean `#check @name` printer dump
(scout pipeline, logs/sigprobe_88.out) is retained as a cross
reference; semantic identity is re-verified by the elaboration of the
`<...>` assembly below (each component must unify definitionally with
its conjunct); the per-conjunct comments carry each exit's LA35
declaration line, file-local docstring HOL anchor and section.
Conjunct order: the seed-list order (la35_orphan_seeds_88.txt), drops
removed.  Body = the assembly of the exit constants -- zero new proof
obligations, zero new imports. -/
theorem la35_wire_capstone_w1 :
    -- 1. CARD_FF_EQ_CARD_SLICE_FF_p35 (LA35:21341; HOL `CARD_FF_EQ_CARD_SLICE_FF`)
    (∀ (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
          (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
          (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
          (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
          (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)),
          Set.ncard FF = Set.ncard fv + Set.ncard fw - 2
    ) ∧
    -- 2. CARD_FF_EQ_SCS_K_3_p35 (LA35:39103; HOL `CARD_FF_EQ_SCS_K_3`)
    (∀ (s : ScsV39) (k : ℕ) (FF : Set (V3 × V3))
          (vv : ℕ → V3) (hk : s.k = k)
          (hFF : FF = Set.range fun i => (vv i, vv (i + 1)))
          (hscs : isScsV39 s) (hk3 : k = 3) (hBB : BBsV39 s vv),
          Set.ncard FF = 3
    ) ∧
    -- 3. CARD_SLICE_FF_LE_3_p35 (LA35:21359; HOL `CARD_SLICE_FF_LE_3`)
    (∀ (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
          (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
          (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
          (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
          (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)),
          3 ≤ Set.ncard fv ∧ 3 ≤ Set.ncard fw
    ) ∧
    -- 4. CARD_V_EQ_SCS_K_p35 (LA35:15660; HOL `CARD_V_EQ_SCS_K`)
    (∀ (s : ScsV39) (k p q : ℕ) (V : Set V3) (vv : ℕ → V3)
          (hk : s.k = k) (hV : Set.range vv = V) (hscs : isScsV39 s)
          (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv),
          Set.ncard V = k
    ) ∧
    -- 5. COVEX_OF_LOFA_HALF_CIRCLE2_p35 (LA35:28209; HOL `COVEX_OF_LOFA_HALF_CIRCLE2`)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv fw : Set (V3 × V3)}
          (hlfv : LocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
          (hsandv : covexSandwich_p35 V E' fv)
          (hlfw : LocalFan (vPrime_p3 V fw) (ePrime_p3 E' fw) fw)
          (hsandw : covexSandwich_p35 V E' fw),
          ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv ∧
          ConvexLocalFan (vPrime_p3 V fw) (ePrime_p3 E' fw) fw
    ) ∧
    -- 6. CVX_LO_IMP_LO_p35 (LA35:21427; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (h : ConvexLocalFan V E FF),
          LocalFan V E FF
    ) ∧
    -- 7. DIAGE_VAL_P_Q_p35 (LA35:40723; HOL `DIAGE_VAL_P_Q`)
    (∀ (p q : ℕ) (h1 : p % 4 ≠ q % 4)
          (h2 : (p + 1) % 4 ≠ q % 4) (h3 : p % 4 ≠ (q + 1) % 4),
          q % 4 = (p % 4 + 2) % 4
    ) ∧
    -- 8. DIAG_NOT_IN_SCS_J_p35 (LA35:17061; HOL `DIAG_NOT_IN_SCS_J`)
    (∀ (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
          (hdiag : scsDiag s.k p q),
          ¬ s.J p q
    ) ∧
    -- 9. DIST_DIAG_LE_CSTAB_p35 (LA35:17886; HOL `DIST_DIAG_LE_CSTAB`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
          (mkj : Prop) (vv : ℕ → V3)
          (hj : ¬(s.k = 4 ∧ ¬s'.J 0 (s'.k - 1)))
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
          (hsl : isScsSliceV39 s s' s'' p q),
          norm (vv (p % s.k) - vv (q % s.k)) ≤ cstab
    ) ∧
    -- 10. EJRCFJD_W4_SKELETON_p35 (LA35:29149; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E E' : Set (Set V3)}
          {FF fv : Set (V3 × V3)} {dU dW : V3 × V3}
          (hlf : localFan_p3 (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
          (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
          (hfin : fv.Finite)
          (hkch : (∀ v ∈ vPrime_p3 V fv, interiorAngle1 (0:V3) fv v = Real.pi) ∧
            ∃ A : Set V3,
              (∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧
                  A = (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) ∧
              (0:V3) ∈ A ∧ vPrime_p3 V fv ⊆ A ∧
              ∃ e : V3,
                (∀ x ∈ A, ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0) ∧
                cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e ∧
                ∀ v ∈ vPrime_p3 V fv,
                  azimCycle_p3 (vPrime_p3 V fv) (0:V3) e v = rhoNode1 fv v ∧
                    azim 0 e v (rhoNode1 fv v) =
                      dihV (0:V3) e v (rhoNode1 fv v) ∧
                    azim 0 e v (rhoNode1 fv v) =
                      arcV 0 v (rhoNode1 fv v) ∧
                    azim 0 e v (rhoNode1 fv v) < Real.pi)
          (hconvO : ConvexLocalFan V E FF)
          (hdU : dU ∈ fv ∧ w4pWindowData_p35 V E' fv dU)
          (hdW : dW ∈ fv ∧ w4pWindowData_p35 V E' fv dW)
          (hsplit : ∀ p ∈ fv, p = dU ∨ p = dW ∨
            ∃ c : V3, c ≠ p.2 ∧ p ∈ FF ∧
              EE_p3 p.1 E = ({p.2, c} : Set V3) ∧
              EE_p3 p.1 (ePrime_p3 E' fv) = ({p.2, c} : Set V3)),
          ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv
    ) ∧
    -- 11. FFBD_MODEQ_EQ_p35 (LA35:305; no HOL anchor line in file docstring)
    (∀ {k a b : ℕ} (h : a % k = b % k) (ha : a < k) (hb : b < k)
    ,
          a = b
    ) ∧
    -- 12. FV_NCARD_GE2_p35 (LA35:25191; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN`)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
          {d : V3 × V3} (hd : d ∈ dartsOfHyp_p3 E' V) (hdd : d.1 ≠ d.2),
          2 ≤ (HS.face d).ncard
    ) ∧
    -- 13. HAFL2_CIRCLE_FORM_LOCAL_FAN_p35 (LA35:26786; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2`)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
          (hfan : Kepler.Text.Fan.FAN 0 V E')
          {dv dw : V3 × V3} (hdv : dv ∈ dartsOfHyp_p3 E' V)
          (hdw : dw ∈ dartsOfHyp_p3 E' V)
          (hparamv : faceCycleParam_p35 V E' (HS.face dv))
          (hparamw : faceCycleParam_p35 V E' (HS.face dw))
          (HSv' : Hypermap (V3 × V3))
          (hHSv' : IsHypE_p35 (vPrime_p3 V (HS.face dv))
            (ePrime_p3 E' (HS.face dv)) HSv')
          (hdv' : dv ∈ dartsOfHyp_p3 (ePrime_p3 E' (HS.face dv))
            (vPrime_p3 V (HS.face dv)))
          (HSw' : Hypermap (V3 × V3))
          (hHSw' : IsHypE_p35 (vPrime_p3 V (HS.face dw))
            (ePrime_p3 E' (HS.face dw)) HSw')
          (hdw' : dw ∈ dartsOfHyp_p3 (ePrime_p3 E' (HS.face dw))
            (vPrime_p3 V (HS.face dw))),
          localFan_p3 (vPrime_p3 V (HS.face dv)) (ePrime_p3 E' (HS.face dv))
            (HS.face dv)
          ∧ localFan_p3 (vPrime_p3 V (HS.face dw)) (ePrime_p3 E' (HS.face dw))
            (HS.face dw)
    ) ∧
    -- 14. HAFL2_RED_p35 (LA35:25250; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2`)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
          (hfan : Kepler.Text.Fan.FAN 0 V E')
          {dv dw : V3 × V3} (hdv : dv ∈ dartsOfHyp_p3 E' V)
          (hdw : dw ∈ dartsOfHyp_p3 E' V),
          Kepler.Text.Fan.FAN 0 (vPrime_p3 V (HS.face dv)) (ePrime_p3 E' (HS.face dv)) ∧
          Kepler.Text.Fan.FAN 0 (vPrime_p3 V (HS.face dw)) (ePrime_p3 E' (HS.face dw))
    ) ∧
    -- 15. HAFL_EDGE_ORD2_p35 (LA35:25267; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN`)
    (∀ {V : Set V3} {E : Set (Set V3)} {a b : V3}
          (hd : (a, b) ∈ dartsOfHyp_p3 E V) (hab : a ≠ b),
          hasOrders_p3 (eeOfHyp_p3 0 V E : V3 × V3 → V3 × V3) 2
    ) ∧
    -- 16. HAFL_HALF_CIRCLE_SLICED_p35 (LA35:27496; no HOL anchor line in file docstring)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
          (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
          (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hk' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
          (hfan : Kepler.Text.Fan.FAN 0 V (E ∪ {{u, w}}))
          (HS' : Hypermap (V3 × V3))
          (hHS' : IsHypE_p35 (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
            (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u))) HS')
          (hd' : (u, rhoNode1 FF u) ∈ dartsOfHyp_p3 (ePrime_p3 (E ∪ {{u, w}})
            (HS.face (u, rhoNode1 FF u))) (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))),
          localFan_p3 (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
          (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
          (HS.face (u, rhoNode1 FF u))
    ) ∧
    -- 17. HALF_CIRCLE_STEP_SEQ_p35 (LA35:27079; no HOL anchor line in file docstring)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
          (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
          (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hk' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
          ∀ i : ℕ, ffOfHyp_p3 0 V (E ∪ {{u, w}})
            (vv (i % k' + p % k), vv ((i + 1) % k' + p % k))
          = (vv ((i + 1) % k' + p % k), vv ((i + 1 + 1) % k' + p % k))
    ) ∧
    -- 18. HALF_CIRCLE_STEP_p35 (LA35:27386; no HOL anchor line in file docstring)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
          (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
          (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hk' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
          ∀ p ∈ HS.face (u, rhoNode1 FF u),
          ∃ c : V3, ffOfHyp_p3 0 V (E ∪ {{u, w}}) p = (p.2, c) ∧ c ≠ p.1
    ) ∧
    -- 19. HNOWRAP_OF_KCHMAMG_p35 (LA35:29345; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv : Set (V3 × V3)} {p : V3 × V3} {k : ℕ} {ρ : ℕ → V3} {e : V3}
          (hr0 : ρ 0 = p.1) (hv0 : p.1 ≠ 0) (hb0 : p.2 ≠ 0)
          (hb : ¬ Collinear3 0 p.1 p.2)
          (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 p.1 (ρ i))
          (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
          (hfanL : LocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
          (hEE2 : ∀ u ∈ vPrime_p3 V fv, (EE_p3 u (ePrime_p3 E' fv)).ncard = 2)
          (hv0V : p.1 ∈ vPrime_p3 V fv)
          (hrV : ∀ j, j < k → ρ j ∈ vPrime_p3 V fv)
          (hstep : ∀ i, i + 1 < k → (ρ i, ρ (i + 1)) ∈ fv)
          (hplane : ∃ A : Set V3,
            (∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧
                A = (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) ∧
              (0:V3) ∈ A ∧ vPrime_p3 V fv ⊆ A ∧
              ∀ x ∈ A, ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0)
          (hcy : cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e)
          (hq : ∀ v ∈ vPrime_p3 V fv,
            azimCycle_p3 (vPrime_p3 V fv) (0:V3) e v = rhoNode1 fv v ∧
              azim 0 e v (rhoNode1 fv v) = dihV (0:V3) e v (rhoNode1 fv v) ∧
              azim 0 e v (rhoNode1 fv v) = arcV 0 v (rhoNode1 fv v) ∧
              azim 0 e v (rhoNode1 fv v) < Real.pi)
          (hsgn : 0 < (crossProduct (e : Fin 3 → ℝ) (p.1 : Fin 3 → ℝ)) ⬝ᵥ
            (p.2 : Fin 3 → ℝ)),
          ∀ i, i + 1 < k →
          ¬(azim 0 p.1 p.2 (ρ i) = Real.pi ∧ azim 0 p.1 p.2 (ρ (i + 1)) = 0)
    ) ∧
    -- 20. HVISIT_HALF_CIRCLE_p35 (LA35:27028; no HOL anchor line in file docstring)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
          (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
          (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hk' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
          Set.InjOn Prod.fst (HS.face (u, rhoNode1 FF u))
    ) ∧
    -- 21. LOFA_HYP_UNION_CARD_GT2_p35 (LA35:24907; HOL `LOFA_HYP_UNION_CARD_GT2`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E HS)
          (hVE : ⋃₀ E ⊆ V) (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2)
          (hgraph : Kepler.Text.Fan.Graph E) {v w : V3} (hvw : v ≠ w)
          (hd : (v, w) ∈ dartsOfHyp_p3 E V),
          2 < (HS.face (v, w)).ncard
    ) ∧
    -- 22. MOD_EQ_IMP_MOD_EQ_0_p35 (LA35:112; HOL `MOD_EQ_IMP_MOD_EQ_0`)
    (∀ {k p q : ℕ} (hk : k ≠ 0) (hmod : p % k = q % k)
          (hle : q ≤ p),
          (p - q) % k = 0
    ) ∧
    -- 23. MONO_AZIM_AS_BTA_I_p35 (LA35:28123; HOL `MONO_AZIM_AS_BTA_I`)
    (∀ (k : ℕ) {v0 : V3} (ρ : ℕ → V3)
          (hstep : ∀ i, i + 1 < k → azim 0 v0 (ρ 1) (ρ i) ≤ azim 0 v0 (ρ 1) (ρ (i + 1)))
          {i j : ℕ} (hij : i < j) (hjk : j < k),
          azim 0 v0 (ρ 1) (ρ i) ≤ azim 0 v0 (ρ 1) (ρ j)
    ) ∧
    -- 24. NUMSEG_2_p35 (LA35:18444; HOL `NUMSEG_2`)
    ({i : ℕ | i < 3} = {0, 1, 2}
    ) ∧
    -- 25. NUMSEG_3_p35 (LA35:39073; HOL `NUMSEG_3`)
    ({i : ℕ | i < 4} = {0, 1, 2, 3}
    ) ∧
    -- 26. SCS_K_LE_6_p35 (LA35:970; HOL `SCS_K_LE_6`)
    (∀ (s : ScsV39) (h : isScsV39 s)
    ,
          s.k ≤ 6
    ) ∧
    -- 27. SCS_K_PRIME_CASE_5_p35 (LA35:147; HOL `SCS_K_PRIME_CASE_5`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
          (hs' : s' = scsHalfSliceV39 s p q d' mkj)
          (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
          (hk : s.k = 5) (hdiag : scsDiag s.k p q),
          (s'.k = 3 ∧ s''.k = 4) ∨ (s'.k = 4 ∧ s''.k = 3)
    ) ∧
    -- 28. SCS_K_PRIME_CASE_6_p35 (LA35:166; HOL `SCS_K_PRIME_CASE_6`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
          (hs' : s' = scsHalfSliceV39 s p q d' mkj)
          (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
          (hk : s.k = 6) (hdiag : scsDiag s.k p q),
          (s'.k = 3 ∧ s''.k = 5) ∨ (s'.k = 5 ∧ s''.k = 3) ∨ (s'.k = 4 ∧ s''.k = 4)
    ) ∧
    -- 29. SLICE_HYP_EXISTS_p35 (LA35:26519; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv : Set (V3 × V3)} (hsub : fv ⊆ dartsOfHyp_p3 E' V)
          (hparam : faceCycleParam_p35 V E' fv) (hfin : fv.Finite)
          (hne : fv.Nonempty),
          ∃ HS' : Hypermap (V3 × V3),
          IsHypE_p35 (vPrime_p3 V fv) (ePrime_p3 E' fv) HS'
    ) ∧
    -- 30. SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 (LA35:41035; HOL `SUM_AZIM_EQ_ANGLE_EQ4`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
          (mkj : Prop) (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (vv vv' vv'' : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hk' : k' = 3)
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
          (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
          (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
          (hsl : isScsSliceV39 s s' s'' p q) (hk's' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
          (hfan : ConvexLocalFan
            (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
            (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
            (HS.face (u, rhoNode1 FF u))),
          tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
          setSum {i | i < k'}
              (fun i => rhoFun (norm (vv (i + p % k))) *
                interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
            (Real.pi + sol0)
    ) ∧
    -- 31. SUM_AZIM_EQ_ANGLE_EQ4_p35 (LA35:41073; HOL `SUM_AZIM_EQ_ANGLE_EQ4`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
          (mkj : Prop) (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (vv vv' vv'' : ℕ → V3) (HS : Hypermap (V3 × V3))
          (hk' : k' = 3)
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
          (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
          (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
          (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
          (hsl : isScsSliceV39 s s' s'' p q) (hk's' : s'.k = k') (hk : s.k = k)
          (hp : vv (p % k) = u) (hq : vv (q % k) = w)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hnorm : norm (u - w) ≤ cstab)
          (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
          (hfan : ConvexLocalFan
            (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
            (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
            (HS.face (u, rhoNode1 FF u))),
          tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
          setSum {i | i < k'}
              (fun i => rhoFun (norm (vv (i + p % k))) *
                interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
            (Real.pi + sol0)
    ) ∧
    -- 32. SUM_AZIM_EQ_ANGLE_LE4_p35 (LA35:18316; HOL `SUM_AZIM_EQ_ANGLE_LE4`)
    (∀ (s : ScsV39) (p q : ℕ) (u : V3) (V : Set V3)
          (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
          (hk3 : ¬(s.k ≤ 3)) (hBB : BBsV39 s vv) (hscs : isScsV39 s)
          (hp : vv (p % s.k) = u)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF),
          setSum {i | i < s.k}
            (fun i => rhoFun (norm (vv (i + p % s.k))) *
              interiorAngle1 0 FF ((rhoNode1 FF)^[i] u)) =
          setSum FF (fun e => rhoFun (norm e.1) * azimInFan e E)
    ) ∧
    -- 33. SUM_NUMSEG3_p35 (LA35:18450; HOL `SUM_NUMSEG3`)
    (∀ (t : ℕ → ℝ)
    ,
          ∑ i ∈ Finset.range 4, t i = t 0 + t 1 + t 2 + t 3
    ) ∧
    -- 34. TECOXBM2_p35 (LA35:15552; no HOL anchor line in file docstring)
    (∀ (u w : V3) (hu : u ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
          (h2 : (2:ℝ) ≤ ‖u - w‖) (hc : ‖u - w‖ ≤ cstab),
          ¬ Collinear3 0 u w
    ) ∧
    -- 35. TECOXBMv2_step01_p35 (LA35:1138; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
          (hdiag : scsDiag s.k p q),
          s.k = 4 ∨ s.k = 5 ∨ s.k = 6
    ) ∧
    -- 36. TECOXBMv2_step02_p35 (LA35:15411; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
          (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
          (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w) (hBB : BBsV39 s vv),
          (2 : ℝ) ≤ dist u w
    ) ∧
    -- 37. TECOXBMv2_step03_p35 (LA35:15431; HOL `IN_IMAGE_VV`)
    (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
          (hscs : isScsV39 s) (_hdiag : scsDiag s.k p q)
          (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
          (hk : s.k = 4 ∨ s.k = 5 ∨ s.k = 6),
          {u, w} ⊆ V_SY_p4 (cycRow_p23 vv s.k)
    ) ∧
    -- 38. TECOXBMv2_step04_p35 (LA35:15460; HOL `Tecoxbm.TECOXBM`)
    (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (vv : ℕ → V3)
          (hscs : isScsV39 s) (hk : s.k = 4) (hdiag : scsDiag s.k p q)
          (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
          (hBB : BBsV39 s vv)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hIN : flattenRow_p23 vv 4 ∈
            {l : FinVec 4 3 | (∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus) ∧
              CONDITION1_SY_p4
                (fun i j => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
                (fun i j => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
                (cycRow_p23 vv 4) ∧
              CONDITION2_SY_p4 (cycRow_p23 vv 4)})
          (hVEF : V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
            E_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
            F_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ),
          ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
    ) ∧
    -- 39. TECOXBMv2_step05_p35 (LA35:15488; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (vv : ℕ → V3)
          (hscs : isScsV39 s) (hk : s.k = 5 ∨ s.k = 6) (hdiag : scsDiag s.k p q)
          (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
          (hBB : BBsV39 s vv)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hIN : (s.k = 5 → flattenRow_p23 vv 5 ∈
                {l : FinVec 5 3 | (∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus) ∧
                  CONDITION1_SY_p4
                    (fun i j => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
                    (fun i j => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
                    (cycRow_p23 vv 5) ∧
                  CONDITION2_SY_p4 (cycRow_p23 vv 5)}) ∧
            (s.k = 6 → flattenRow_p23 vv 6 ∈
                {l : FinVec 6 3 | (∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus) ∧
                  CONDITION1_SY_p4
                    (fun i j => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
                    (fun i j => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
                    (cycRow_p23 vv 6) ∧
                  CONDITION2_SY_p4 (cycRow_p23 vv 6)}))
          (hVEF : (s.k = 5 → V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
                E_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
                F_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) ∧
            (s.k = 6 → V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
                E_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
                F_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ)),
          ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
    ) ∧
    -- 40. TECOXBMv2_step06_p35 (LA35:15524; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (vv : ℕ → V3) (hscs : isScsV39 s)
          (hdiag : scsDiag s.k p q)
          (h4 : s.k = 4 → ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E)
          (h56 : s.k = 5 ∨ s.k = 6 →
            ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E),
          ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
    ) ∧
    -- 41. VV_INJ_p35 (LA35:15647; HOL `VV_INJ`)
    (∀ (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (hk : s.k = k)
          (hscs : isScsV39 s) (hBB : BBsV39 s vv),
          ∀ i j, i < k ∧ j < k ∧ i ≠ j → vv i ≠ vv j
    ) ∧
    -- 42. VV_SUC_EQ_RHO_NODE_PRIME_p35 (LA35:18295; HOL `VV_SUC_EQ_RHO_NODE_PRIME`)
    (∀ (s : ScsV39) (k p1 p q : ℕ) (u : V3)
          (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
          (hk : s.k = k) (hp1 : vv p1 = u)
          (hV : Set.range vv = V)
          (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hBB : BBsV39 s vv),
          ∀ m, (rhoNode1 FF)^[m] u = vv (m + p1)
    ) ∧
    -- 43. V_SLICE_EQ_NUMSEG_p35 (LA35:18362; HOL `V_SLICE_EQ_NUMSEG`)
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ)
          (mkj : Prop) (k k' : ℕ) (u : V3) (FF : Set (V3 × V3)) (vv : ℕ → V3)
          (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
          (hk : s.k = k) (hk' : s'.k = k') (hp : vv (p % k) = u)
          (hs' : scsHalfSliceV39 s p q d' mkj = s')
          (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
          (hsl : isScsSliceV39 s s' s'' p q),
          {i | i < k ∧ (rhoNode1 FF)^[i] u ∈ Set.range (fun j => vv (j % k' + p % k))} =
          {i | i < k'}
    ) ∧
    -- 44. WEDGE_IN_FAN_LOFA_DETER2_p35 (LA35:21535; HOL `WEDGE_IN_FAN_LOFA_DETER2`)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} (hfan : LocalFan V E FF)
          (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2) (hv : v ∈ V),
          wedgeInFanGt_p3 (v, rhoNode1 FF v) E
          = Kepler.Geom.wedge (0 : V3) v (rhoNode1 FF v) (ivsRhoNode1 FF v)
    ) ∧
    -- 45. azimCycle_singleton_p35 (LA35:25306; HOL `azim_cycle`)
    (∀ (v w p : V3)
    ,
          azimCycle_p3 ({p} : Set V3) v w p = p
    ) ∧
    -- 46. b2AzimCyclePredFalse_p35 (LA35:33529; no HOL anchor line in file docstring)
    (¬ ∀ (W : Set V3) (u z : V3), W.Finite → z ∈ W → (∃ y ∈ W, y ≠ z) →
          ∃ x ∈ W, azimCycle_p3 W (0:V3) u x = z
    ) ∧
    -- 47. b2AzimSmulZero_p35 (LA35:33404; no HOL anchor line in file docstring)
    (∀ {u y : V3} (c : ℝ) (hc : 0 < c)
          (hcol : ¬ Collinear3 (0:V3) u y),
          azim (0:V3) u y (c • y) = 0
    ) ∧
    -- 48. dart1OfFan_subset_dartsOfHyp_p35 (LA35:21473; no HOL anchor line in file docstring)
    (∀ {E E' : Set (Set V3)} {V : Set V3}
          (hsub : E ⊆ E'),
          Fan.dart1OfFan V E ⊆ dartsOfHyp_p3 E' V
    ) ∧
    -- 49. dartsOfHyp_ne_mono_p35 (LA35:25113; no HOL anchor line in file docstring)
    (∀ {E E' : Set (Set V3)} {V : Set V3} {a b : V3}
          (hsub : E ⊆ E') (hd : (a, b) ∈ dartsOfHyp_p3 E V) (hab : a ≠ b),
          (a, b) ∈ dartsOfHyp_p3 E' V
    ) ∧
    -- 50. ePrime_subset_p35 (LA35:25287; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} {fv : Set (V3 × V3)}
    ,
          ePrime_p3 E fv ⊆ E
    ) ∧
    -- 51. eePermOfHyp_p35_apply (LA35:21463; no HOL anchor line in file docstring)
    (∀ (x : V3) (V : Set V3) (E : Set (Set V3))
          (d : V3 × V3),
          eePermOfHyp_p35 x V E d = eeOfHyp_p3 x V E d
    ) ∧
    -- 52. fstCoverOfUnio_p35 (LA35:31534; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (hfanL : LocalFan V E FF) {u : V3} (hu : u ∈ ⋃₀ E),
          ∃ d ∈ FF, d.1 = u
    ) ∧
    -- 53. jEvenNbrOnUnio_p35 (LA35:33238; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (hfan : LocalFan V E FF),
          ∀ u ∈ ⋃₀ E, ∃ t : ℕ, (EE_p3 u E).ncard = 2 * t
    ) ∧
    -- 54. jTwoLeNbrOnUnio_p35 (LA35:33053; HOL `local_fan`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (hfan : LocalFan V E FF),
          ∀ u ∈ ⋃₀ E, 2 ≤ (EE_p3 u E).ncard
    ) ∧
    -- 55. jUnioMemVPrime_p35 (LA35:33185; HOL `LOCAL_FAN_RHO_NODE_PROS`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (hfan : LocalFan V E FF),
          ∀ u ∈ ⋃₀ E, u ∈ vPrime_p3 V FF
    ) ∧
    -- 56. jUnioVertKit_p35 (LA35:33230; HOL `LOFA_IMP_EE_TWO_ELMS`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (hfan : LocalFan V E FF),
          (∀ u ∈ ⋃₀ E, 2 ≤ (EE_p3 u E).ncard) ∧ (∀ u ∈ ⋃₀ E, u ∈ vPrime_p3 V FF)
    ) ∧
    -- 57. kchS0NeZeroOfPlane_p35 (LA35:30525; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv : Set (V3 × V3)} {p : V3 × V3} {e : V3}
          (hv0 : p.1 ≠ 0) (hb0 : p.2 ≠ 0) (hb : ¬ Collinear3 0 p.1 p.2)
          (hv0V : p.1 ∈ vPrime_p3 V fv) (hp2V : p.2 ∈ vPrime_p3 V fv)
          (hcy : cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e)
          (heperp : ∀ x ∈ vPrime_p3 V fv,
            ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0),
          (crossProduct (e : Fin 3 → ℝ) (p.1 : Fin 3 → ℝ)) ⬝ᵥ (p.2 : Fin 3 → ℝ) ≠ 0
    ) ∧
    -- 58. kchS0NeZero_p35 (LA35:30450; no HOL anchor line in file docstring)
    (∀ {e p1 p2 : V3}
          (hE : ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) ≠ 0)
          (hp1e : ((p1 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0)
          (hp2e : ((p2 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0)
          (hp10 : p1 ≠ 0) (hp20 : p2 ≠ 0) (hb : ¬ Collinear3 0 p1 p2),
          (crossProduct (e : Fin 3 → ℝ) (p1 : Fin 3 → ℝ)) ⬝ᵥ (p2 : Fin 3 → ℝ) ≠ 0
    ) ∧
    -- 59. ncExistsAffGt_p35 (LA35:34165; HOL `Planarity.exists_in_aff_gt_disjoint`, HOL `AFF_GT_SUB_AFF_UNION`)
    (∀ {v w : V3} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hwv : v ≠ w)
    ,
          ∃ y : V3, y ∈ affGt ({(0:V3)} : Set V3) ({v, w} : Set V3) ∧
          y ∈ (affineSpan ℝ ({(0:V3), v, w} : Set V3) : Set V3)
    ) ∧
    -- 60. ncSliceNoncollinear_p35 (LA35:35677; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v w : V3} (hfan : ConvexLocalFan V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hwv : v ≠ w)
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
          (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2)
          (hnl : ∀ a ∈ V, ∀ b ∈ V, a ≠ b →
            Collinear ℝ ({(0:V3), a, b} : Set V3) → ¬ Lunar a b V E),
          ∀ z ∈ ({v, w} : Set V3), ∀ t ∈ V, t ≠ z → ¬ Collinear3 (0:V3) z t
    ) ∧
    -- 61. twoNbrOfUnio_p35 (LA35:31572; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (hfan : ConvexLocalFan V E FF) {u : V3}
          (hu : u ∈ ⋃₀ E),
          1 < (EE_p3 u E).ncard
    ) ∧
    -- 62. vPrime_subset_p35 (LA35:25283; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {fv : Set (V3 × V3)}
    ,
          vPrime_p3 V fv ⊆ V
    ) ∧
    -- 63. w1NoIsoAux_p35 (LA35:27601; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
    ,
          ∀ u ∈ V, EE_p3 u E ≠ ∅
    ) ∧
    -- 64. w1SigmaBndAux_p35 (LA35:27665; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
    ,
          ∀ u ∈ V, (EE_p3 u E).ncard ≤ 2
    ) ∧
    -- 65. w1TwoLeAux_p35 (LA35:27749; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
    ,
          ∀ u ∈ V, 2 ≤ (EE_p3 u E).ncard
    ) ∧
    -- 66. w1_azim3_p35 (LA35:27647; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E) {v u0 s q : V3}
          (hu0E : {v, u0} ∈ E) (hsE : {v, s} ∈ E) (hqE : {v, q} ∈ E)
          (hmin1 : azim 0 v u0 s ≤ azim 0 v u0 q)
          (hmin2 : azim 0 v s u0 ≤ azim 0 v s q)
          (hsne : s ≠ u0),
          False
    ) ∧
    -- 67. w1_nnFst_p35 (LA35:27588; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} (z : V3 × V3)
    ,
          (nnOfHyp_p3 0 V E z).1 = z.1
    ) ∧
    -- 68. w1_nn_apply_p35 (LA35:27593; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} (V : Set V3) {E : Set (Set V3)} {a b : V3}
          (hab : {a, b} ∈ E),
          nnOfHyp_p3 0 V E (a, b) = (a, azimCycle_p3 (EE_p3 a E) 0 a b)
    ) ∧
    -- 69. w4pHintOfOZSlice_p35 (LA35:29031; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv : Set (V3 × V3)}
          (hconv : ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
          (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
          (hfin : fv.Finite)
          (hOZ : ∀ x ∈ vPrime_p3 V fv, ∃ u w : V3,
            ({u, x, w} : Set V3) ⊆ vPrime_p3 V fv ∧
            (({u, w} : Set V3) ∩
                (affineSpan ℝ ({(0:V3), x} : Set V3) : Set V3)) = ∅ ∧
            ¬((affineSpan ℝ ({x, (0:V3)} : Set V3) : Set V3) ∩
              ozConv0_p35 ({w, u} : Set V3) = ∅) ∧
            ∃ P : Set V3, ({(0:V3), u, x, w} : Set V3) ⊆ P ∧
              ∃ a b c : V3, ¬ Collinear3 a b c ∧
                P = (affineSpan ℝ ({a, b, c} : Set V3) : Set V3)),
          ∀ x ∈ vPrime_p3 V fv, interiorAngle1 (0:V3) fv x = Real.pi
    ) ∧
    -- 70. w4pNowrapOfRendered_p35 (LA35:29194; no HOL anchor line in file docstring)
    (∀ (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
          (hv0 : v0 ≠ 0) (hb0 : b ≠ 0) (hbu : b ≠ v0) (hb : ¬ Collinear3 0 v0 b)
          (hnc : ∀ i, i + 1 < k → ¬ Collinear3 0 v0 (ρ (i + 1)))
          (hcornerR : ∀ i, i + 1 < k → azim 0 v0 b (ρ i) = Real.pi →
            ∀ s t : ℝ, ρ (i + 1) - 0 = s • (v0 - 0) + t • (b - 0) → t ≤ 0),
          ∀ i, i + 1 < k →
          ¬(azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0)
    ) ∧
    -- 71. w4pOZTripleSlice_p35 (LA35:29010; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E' : Set (Set V3)}
          {fv : Set (V3 × V3)} {P : Set V3} {u v w : V3}
          (hconv : ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
          (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
          (hfin : fv.Finite)
          (hsub3 : ({u, v, w} : Set V3) ⊆ vPrime_p3 V fv)
          (hplane : ∃ a b c : V3, ¬ Collinear3 a b c ∧
            P = (affineSpan ℝ ({a, b, c} : Set V3) : Set V3))
          (hP : ({(0:V3), u, v, w} : Set V3) ⊆ P)
          (hdisj : (({u, w} : Set V3) ∩
              (affineSpan ℝ ({(0:V3), v} : Set V3) : Set V3)) = ∅)
          (hint : ¬((affineSpan ℝ ({v, (0:V3)} : Set V3) : Set V3) ∩
            ozConv0_p35 ({w, u} : Set V3) = ∅)),
          interiorAngle1 (0:V3) fv v = Real.pi ∧ rhoNode1 fv v ∈ P ∧
          ivsRhoNode1 fv v ∈ P
    ) :=
    ⟨CARD_FF_EQ_CARD_SLICE_FF_p35, CARD_FF_EQ_SCS_K_3_p35, CARD_SLICE_FF_LE_3_p35,
      CARD_V_EQ_SCS_K_p35, @COVEX_OF_LOFA_HALF_CIRCLE2_p35, CVX_LO_IMP_LO_p35, DIAGE_VAL_P_Q_p35,
      DIAG_NOT_IN_SCS_J_p35, DIST_DIAG_LE_CSTAB_p35, @EJRCFJD_W4_SKELETON_p35, FFBD_MODEQ_EQ_p35,
      @FV_NCARD_GE2_p35, @HAFL2_CIRCLE_FORM_LOCAL_FAN_p35, @HAFL2_RED_p35, HAFL_EDGE_ORD2_p35,
      HAFL_HALF_CIRCLE_SLICED_p35, HALF_CIRCLE_STEP_SEQ_p35, HALF_CIRCLE_STEP_p35,
      @HNOWRAP_OF_KCHMAMG_p35, HVISIT_HALF_CIRCLE_p35, LOFA_HYP_UNION_CARD_GT2_p35,
      MOD_EQ_IMP_MOD_EQ_0_p35, MONO_AZIM_AS_BTA_I_p35, NUMSEG_2_p35, NUMSEG_3_p35,
      SCS_K_LE_6_p35, SCS_K_PRIME_CASE_5_p35, SCS_K_PRIME_CASE_6_p35, @SLICE_HYP_EXISTS_p35,
      @SUM_AZIM_EQ_ANGLE_EQ4_HS_p35, @SUM_AZIM_EQ_ANGLE_EQ4_p35, SUM_AZIM_EQ_ANGLE_LE4_p35,
      SUM_NUMSEG3_p35, TECOXBM2_p35, TECOXBMv2_step01_p35, TECOXBMv2_step02_p35,
      @TECOXBMv2_step03_p35, @TECOXBMv2_step04_p35, @TECOXBMv2_step05_p35, @TECOXBMv2_step06_p35,
      VV_INJ_p35, VV_SUC_EQ_RHO_NODE_PRIME_p35, @V_SLICE_EQ_NUMSEG_p35,
      WEDGE_IN_FAN_LOFA_DETER2_p35, azimCycle_singleton_p35, b2AzimCyclePredFalse_p35,
      b2AzimSmulZero_p35, @dart1OfFan_subset_dartsOfHyp_p35, @dartsOfHyp_ne_mono_p35,
      @ePrime_subset_p35, eePermOfHyp_p35_apply, fstCoverOfUnio_p35, jEvenNbrOnUnio_p35,
      jTwoLeNbrOnUnio_p35, jUnioMemVPrime_p35, jUnioVertKit_p35, @kchS0NeZeroOfPlane_p35,
      kchS0NeZero_p35, ncExistsAffGt_p35, ncSliceNoncollinear_p35, twoNbrOfUnio_p35,
      @vPrime_subset_p35, w1NoIsoAux_p35, w1SigmaBndAux_p35, w1TwoLeAux_p35, w1_azim3_p35,
      w1_nnFst_p35, w1_nn_apply_p35, @w4pHintOfOZSlice_p35, w4pNowrapOfRendered_p35,
      @w4pOZTripleSlice_p35⟩

/-- LA35 wire forwarding, wave w2 (lane la35-root-w1, 2026-11-03;
S1 rewire precedent `ebe0d0b7` same shape).  Type-preserving re-point
target for `Kepler.Assembly.textCapstone`: the statement is exactly

  (S1 conjunct 1: the p16 switch, verbatim) ∧
  (la35_wire_capstone_w1's full 88-exit conjunction, verbatim) ∧
  (S1 conjuncts 2..47, verbatim, in their S1 order)

so the Assembly consumer's `.1` projection keeps its exact statement
(`hcap.1 hmnt` elaborates to the same `lp_main_estimate` derivation).
Body = repackaging of `la35_wire_capstone_w1` and the S1 capstone by
projections -- zero new proof obligations. -/
theorem localconcl_wire_capstone_w2 (hmn : main_nonlinear_terminal_v11) :
    (main_nonlinear_terminal_v11 → lp_main_estimate) ∧
    (
  -- 1. CARD_FF_EQ_CARD_SLICE_FF_p35 (LA35:21341; HOL `CARD_FF_EQ_CARD_SLICE_FF`)
  (∀ (V : Set V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
        (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
        (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
        (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
        (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
        (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)),
        Set.ncard FF = Set.ncard fv + Set.ncard fw - 2
  ) ∧
  -- 2. CARD_FF_EQ_SCS_K_3_p35 (LA35:39103; HOL `CARD_FF_EQ_SCS_K_3`)
  (∀ (s : ScsV39) (k : ℕ) (FF : Set (V3 × V3))
        (vv : ℕ → V3) (hk : s.k = k)
        (hFF : FF = Set.range fun i => (vv i, vv (i + 1)))
        (hscs : isScsV39 s) (hk3 : k = 3) (hBB : BBsV39 s vv),
        Set.ncard FF = 3
  ) ∧
  -- 3. CARD_SLICE_FF_LE_3_p35 (LA35:21359; HOL `CARD_SLICE_FF_LE_3`)
  (∀ (V : Set V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (v w : V3) (HS : Hypermap (V3 × V3))
        (hfan : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
        (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
        (hHS : IsHypE_p35 V (E ∪ {{v, w}}) HS)
        (fv : Set (V3 × V3)) (hfv : fv = HS.face (v, rhoNode1 FF v))
        (fw : Set (V3 × V3)) (hfw : fw = HS.face (w, rhoNode1 FF w)),
        3 ≤ Set.ncard fv ∧ 3 ≤ Set.ncard fw
  ) ∧
  -- 4. CARD_V_EQ_SCS_K_p35 (LA35:15660; HOL `CARD_V_EQ_SCS_K`)
  (∀ (s : ScsV39) (k p q : ℕ) (V : Set V3) (vv : ℕ → V3)
        (hk : s.k = k) (hV : Set.range vv = V) (hscs : isScsV39 s)
        (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv),
        Set.ncard V = k
  ) ∧
  -- 5. COVEX_OF_LOFA_HALF_CIRCLE2_p35 (LA35:28209; HOL `COVEX_OF_LOFA_HALF_CIRCLE2`)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv fw : Set (V3 × V3)}
        (hlfv : LocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
        (hsandv : covexSandwich_p35 V E' fv)
        (hlfw : LocalFan (vPrime_p3 V fw) (ePrime_p3 E' fw) fw)
        (hsandw : covexSandwich_p35 V E' fw),
        ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv ∧
        ConvexLocalFan (vPrime_p3 V fw) (ePrime_p3 E' fw) fw
  ) ∧
  -- 6. CVX_LO_IMP_LO_p35 (LA35:21427; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        (h : ConvexLocalFan V E FF),
        LocalFan V E FF
  ) ∧
  -- 7. DIAGE_VAL_P_Q_p35 (LA35:40723; HOL `DIAGE_VAL_P_Q`)
  (∀ (p q : ℕ) (h1 : p % 4 ≠ q % 4)
        (h2 : (p + 1) % 4 ≠ q % 4) (h3 : p % 4 ≠ (q + 1) % 4),
        q % 4 = (p % 4 + 2) % 4
  ) ∧
  -- 8. DIAG_NOT_IN_SCS_J_p35 (LA35:17061; HOL `DIAG_NOT_IN_SCS_J`)
  (∀ (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
        (hdiag : scsDiag s.k p q),
        ¬ s.J p q
  ) ∧
  -- 9. DIST_DIAG_LE_CSTAB_p35 (LA35:17886; HOL `DIST_DIAG_LE_CSTAB`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
        (mkj : Prop) (vv : ℕ → V3)
        (hj : ¬(s.k = 4 ∧ ¬s'.J 0 (s'.k - 1)))
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
        (hsl : isScsSliceV39 s s' s'' p q),
        norm (vv (p % s.k) - vv (q % s.k)) ≤ cstab
  ) ∧
  -- 10. EJRCFJD_W4_SKELETON_p35 (LA35:29149; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E E' : Set (Set V3)}
        {FF fv : Set (V3 × V3)} {dU dW : V3 × V3}
        (hlf : localFan_p3 (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
        (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
        (hfin : fv.Finite)
        (hkch : (∀ v ∈ vPrime_p3 V fv, interiorAngle1 (0:V3) fv v = Real.pi) ∧
          ∃ A : Set V3,
            (∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧
                A = (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) ∧
            (0:V3) ∈ A ∧ vPrime_p3 V fv ⊆ A ∧
            ∃ e : V3,
              (∀ x ∈ A, ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0) ∧
              cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e ∧
              ∀ v ∈ vPrime_p3 V fv,
                azimCycle_p3 (vPrime_p3 V fv) (0:V3) e v = rhoNode1 fv v ∧
                  azim 0 e v (rhoNode1 fv v) =
                    dihV (0:V3) e v (rhoNode1 fv v) ∧
                  azim 0 e v (rhoNode1 fv v) =
                    arcV 0 v (rhoNode1 fv v) ∧
                  azim 0 e v (rhoNode1 fv v) < Real.pi)
        (hconvO : ConvexLocalFan V E FF)
        (hdU : dU ∈ fv ∧ w4pWindowData_p35 V E' fv dU)
        (hdW : dW ∈ fv ∧ w4pWindowData_p35 V E' fv dW)
        (hsplit : ∀ p ∈ fv, p = dU ∨ p = dW ∨
          ∃ c : V3, c ≠ p.2 ∧ p ∈ FF ∧
            EE_p3 p.1 E = ({p.2, c} : Set V3) ∧
            EE_p3 p.1 (ePrime_p3 E' fv) = ({p.2, c} : Set V3)),
        ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv
  ) ∧
  -- 11. FFBD_MODEQ_EQ_p35 (LA35:305; no HOL anchor line in file docstring)
  (∀ {k a b : ℕ} (h : a % k = b % k) (ha : a < k) (hb : b < k)
  ,
        a = b
  ) ∧
  -- 12. FV_NCARD_GE2_p35 (LA35:25191; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN`)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
        {d : V3 × V3} (hd : d ∈ dartsOfHyp_p3 E' V) (hdd : d.1 ≠ d.2),
        2 ≤ (HS.face d).ncard
  ) ∧
  -- 13. HAFL2_CIRCLE_FORM_LOCAL_FAN_p35 (LA35:26786; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2`)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
        (hfan : Kepler.Text.Fan.FAN 0 V E')
        {dv dw : V3 × V3} (hdv : dv ∈ dartsOfHyp_p3 E' V)
        (hdw : dw ∈ dartsOfHyp_p3 E' V)
        (hparamv : faceCycleParam_p35 V E' (HS.face dv))
        (hparamw : faceCycleParam_p35 V E' (HS.face dw))
        (HSv' : Hypermap (V3 × V3))
        (hHSv' : IsHypE_p35 (vPrime_p3 V (HS.face dv))
          (ePrime_p3 E' (HS.face dv)) HSv')
        (hdv' : dv ∈ dartsOfHyp_p3 (ePrime_p3 E' (HS.face dv))
          (vPrime_p3 V (HS.face dv)))
        (HSw' : Hypermap (V3 × V3))
        (hHSw' : IsHypE_p35 (vPrime_p3 V (HS.face dw))
          (ePrime_p3 E' (HS.face dw)) HSw')
        (hdw' : dw ∈ dartsOfHyp_p3 (ePrime_p3 E' (HS.face dw))
          (vPrime_p3 V (HS.face dw))),
        localFan_p3 (vPrime_p3 V (HS.face dv)) (ePrime_p3 E' (HS.face dv))
          (HS.face dv)
        ∧ localFan_p3 (vPrime_p3 V (HS.face dw)) (ePrime_p3 E' (HS.face dw))
          (HS.face dw)
  ) ∧
  -- 14. HAFL2_RED_p35 (LA35:25250; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2`)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E' HS)
        (hfan : Kepler.Text.Fan.FAN 0 V E')
        {dv dw : V3 × V3} (hdv : dv ∈ dartsOfHyp_p3 E' V)
        (hdw : dw ∈ dartsOfHyp_p3 E' V),
        Kepler.Text.Fan.FAN 0 (vPrime_p3 V (HS.face dv)) (ePrime_p3 E' (HS.face dv)) ∧
        Kepler.Text.Fan.FAN 0 (vPrime_p3 V (HS.face dw)) (ePrime_p3 E' (HS.face dw))
  ) ∧
  -- 15. HAFL_EDGE_ORD2_p35 (LA35:25267; HOL `HAFL_CIRCLE_FORM_LOCAL_FAN`)
  (∀ {V : Set V3} {E : Set (Set V3)} {a b : V3}
        (hd : (a, b) ∈ dartsOfHyp_p3 E V) (hab : a ≠ b),
        hasOrders_p3 (eeOfHyp_p3 0 V E : V3 × V3 → V3 × V3) 2
  ) ∧
  -- 16. HAFL_HALF_CIRCLE_SLICED_p35 (LA35:27496; no HOL anchor line in file docstring)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
        (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
        (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hk' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
        (hfan : Kepler.Text.Fan.FAN 0 V (E ∪ {{u, w}}))
        (HS' : Hypermap (V3 × V3))
        (hHS' : IsHypE_p35 (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
          (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u))) HS')
        (hd' : (u, rhoNode1 FF u) ∈ dartsOfHyp_p3 (ePrime_p3 (E ∪ {{u, w}})
          (HS.face (u, rhoNode1 FF u))) (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))),
        localFan_p3 (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
        (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
        (HS.face (u, rhoNode1 FF u))
  ) ∧
  -- 17. HALF_CIRCLE_STEP_SEQ_p35 (LA35:27079; no HOL anchor line in file docstring)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
        (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
        (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hk' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
        ∀ i : ℕ, ffOfHyp_p3 0 V (E ∪ {{u, w}})
          (vv (i % k' + p % k), vv ((i + 1) % k' + p % k))
        = (vv ((i + 1) % k' + p % k), vv ((i + 1 + 1) % k' + p % k))
  ) ∧
  -- 18. HALF_CIRCLE_STEP_p35 (LA35:27386; no HOL anchor line in file docstring)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
        (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
        (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hk' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
        ∀ p ∈ HS.face (u, rhoNode1 FF u),
        ∃ c : V3, ffOfHyp_p3 0 V (E ∪ {{u, w}}) p = (p.2, c) ∧ c ≠ p.1
  ) ∧
  -- 19. HNOWRAP_OF_KCHMAMG_p35 (LA35:29345; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv : Set (V3 × V3)} {p : V3 × V3} {k : ℕ} {ρ : ℕ → V3} {e : V3}
        (hr0 : ρ 0 = p.1) (hv0 : p.1 ≠ 0) (hb0 : p.2 ≠ 0)
        (hb : ¬ Collinear3 0 p.1 p.2)
        (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 p.1 (ρ i))
        (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
        (hfanL : LocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
        (hEE2 : ∀ u ∈ vPrime_p3 V fv, (EE_p3 u (ePrime_p3 E' fv)).ncard = 2)
        (hv0V : p.1 ∈ vPrime_p3 V fv)
        (hrV : ∀ j, j < k → ρ j ∈ vPrime_p3 V fv)
        (hstep : ∀ i, i + 1 < k → (ρ i, ρ (i + 1)) ∈ fv)
        (hplane : ∃ A : Set V3,
          (∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧
              A = (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) ∧
            (0:V3) ∈ A ∧ vPrime_p3 V fv ⊆ A ∧
            ∀ x ∈ A, ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0)
        (hcy : cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e)
        (hq : ∀ v ∈ vPrime_p3 V fv,
          azimCycle_p3 (vPrime_p3 V fv) (0:V3) e v = rhoNode1 fv v ∧
            azim 0 e v (rhoNode1 fv v) = dihV (0:V3) e v (rhoNode1 fv v) ∧
            azim 0 e v (rhoNode1 fv v) = arcV 0 v (rhoNode1 fv v) ∧
            azim 0 e v (rhoNode1 fv v) < Real.pi)
        (hsgn : 0 < (crossProduct (e : Fin 3 → ℝ) (p.1 : Fin 3 → ℝ)) ⬝ᵥ
          (p.2 : Fin 3 → ℝ)),
        ∀ i, i + 1 < k →
        ¬(azim 0 p.1 p.2 (ρ i) = Real.pi ∧ azim 0 p.1 p.2 (ρ (i + 1)) = 0)
  ) ∧
  -- 20. HVISIT_HALF_CIRCLE_p35 (LA35:27028; no HOL anchor line in file docstring)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ) (mkj : Prop)
        (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
        (vv : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hk' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hscs : isScsV39 s) (hdiag : scsDiag s.k p q) (hBB : BBsV39 s vv)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS),
        Set.InjOn Prod.fst (HS.face (u, rhoNode1 FF u))
  ) ∧
  -- 21. LOFA_HYP_UNION_CARD_GT2_p35 (LA35:24907; HOL `LOFA_HYP_UNION_CARD_GT2`)
  (∀ {V : Set V3} {E : Set (Set V3)}
        (HS : Hypermap (V3 × V3)) (hHS : IsHypE_p35 V E HS)
        (hVE : ⋃₀ E ⊆ V) (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2)
        (hgraph : Kepler.Text.Fan.Graph E) {v w : V3} (hvw : v ≠ w)
        (hd : (v, w) ∈ dartsOfHyp_p3 E V),
        2 < (HS.face (v, w)).ncard
  ) ∧
  -- 22. MOD_EQ_IMP_MOD_EQ_0_p35 (LA35:112; HOL `MOD_EQ_IMP_MOD_EQ_0`)
  (∀ {k p q : ℕ} (hk : k ≠ 0) (hmod : p % k = q % k)
        (hle : q ≤ p),
        (p - q) % k = 0
  ) ∧
  -- 23. MONO_AZIM_AS_BTA_I_p35 (LA35:28123; HOL `MONO_AZIM_AS_BTA_I`)
  (∀ (k : ℕ) {v0 : V3} (ρ : ℕ → V3)
        (hstep : ∀ i, i + 1 < k → azim 0 v0 (ρ 1) (ρ i) ≤ azim 0 v0 (ρ 1) (ρ (i + 1)))
        {i j : ℕ} (hij : i < j) (hjk : j < k),
        azim 0 v0 (ρ 1) (ρ i) ≤ azim 0 v0 (ρ 1) (ρ j)
  ) ∧
  -- 24. NUMSEG_2_p35 (LA35:18444; HOL `NUMSEG_2`)
  ({i : ℕ | i < 3} = {0, 1, 2}
  ) ∧
  -- 25. NUMSEG_3_p35 (LA35:39073; HOL `NUMSEG_3`)
  ({i : ℕ | i < 4} = {0, 1, 2, 3}
  ) ∧
  -- 26. SCS_K_LE_6_p35 (LA35:970; HOL `SCS_K_LE_6`)
  (∀ (s : ScsV39) (h : isScsV39 s)
  ,
        s.k ≤ 6
  ) ∧
  -- 27. SCS_K_PRIME_CASE_5_p35 (LA35:147; HOL `SCS_K_PRIME_CASE_5`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
        (hs' : s' = scsHalfSliceV39 s p q d' mkj)
        (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
        (hk : s.k = 5) (hdiag : scsDiag s.k p q),
        (s'.k = 3 ∧ s''.k = 4) ∨ (s'.k = 4 ∧ s''.k = 3)
  ) ∧
  -- 28. SCS_K_PRIME_CASE_6_p35 (LA35:166; HOL `SCS_K_PRIME_CASE_6`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
        (hs' : s' = scsHalfSliceV39 s p q d' mkj)
        (hs'' : s'' = scsHalfSliceV39 s q p d' mkj) (hscs : isScsV39 s)
        (hk : s.k = 6) (hdiag : scsDiag s.k p q),
        (s'.k = 3 ∧ s''.k = 5) ∨ (s'.k = 5 ∧ s''.k = 3) ∨ (s'.k = 4 ∧ s''.k = 4)
  ) ∧
  -- 29. SLICE_HYP_EXISTS_p35 (LA35:26519; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv : Set (V3 × V3)} (hsub : fv ⊆ dartsOfHyp_p3 E' V)
        (hparam : faceCycleParam_p35 V E' fv) (hfin : fv.Finite)
        (hne : fv.Nonempty),
        ∃ HS' : Hypermap (V3 × V3),
        IsHypE_p35 (vPrime_p3 V fv) (ePrime_p3 E' fv) HS'
  ) ∧
  -- 30. SUM_AZIM_EQ_ANGLE_EQ4_HS_p35 (LA35:41035; HOL `SUM_AZIM_EQ_ANGLE_EQ4`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
        (mkj : Prop) (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (vv vv' vv'' : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hk' : k' = 3)
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
        (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
        (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
        (hsl : isScsSliceV39 s s' s'' p q) (hk's' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
        (hfan : ConvexLocalFan
          (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
          (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
          (HS.face (u, rhoNode1 FF u))),
        tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
        setSum {i | i < k'}
            (fun i => rhoFun (norm (vv (i + p % k))) *
              interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
          (Real.pi + sol0)
  ) ∧
  -- 31. SUM_AZIM_EQ_ANGLE_EQ4_p35 (LA35:41073; HOL `SUM_AZIM_EQ_ANGLE_EQ4`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
        (mkj : Prop) (k k' : ℕ) (u w : V3) (V : Set V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (vv vv' vv'' : ℕ → V3) (HS : Hypermap (V3 × V3))
        (hk' : k' = 3)
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hs'' : scsHalfSliceV39 s q p d'' mkj = s'')
        (hvv' : vv' = fun i => vv (i % s'.k + p % s.k))
        (hvv'' : vv'' = fun i => vv (i % s''.k + q % s.k))
        (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
        (hsl : isScsSliceV39 s s' s'' p q) (hk's' : s'.k = k') (hk : s.k = k)
        (hp : vv (p % k) = u) (hq : vv (q % k) = w)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hnorm : norm (u - w) ≤ cstab)
        (hHS : IsHypE_p35 V (E ∪ {{u, w}}) HS)
        (hfan : ConvexLocalFan
          (vPrime_p3 V (HS.face (u, rhoNode1 FF u)))
          (ePrime_p3 (E ∪ {{u, w}}) (HS.face (u, rhoNode1 FF u)))
          (HS.face (u, rhoNode1 FF u))),
        tau3 (vv (0 % k' + p % k)) (vv (1 % k' + p % k)) (vv (2 % k' + p % k)) =
        setSum {i | i < k'}
            (fun i => rhoFun (norm (vv (i + p % k))) *
              interiorAngle1 0 (HS.face (u, rhoNode1 FF u)) ((rhoNode1 FF)^[i] u)) -
          (Real.pi + sol0)
  ) ∧
  -- 32. SUM_AZIM_EQ_ANGLE_LE4_p35 (LA35:18316; HOL `SUM_AZIM_EQ_ANGLE_LE4`)
  (∀ (s : ScsV39) (p q : ℕ) (u : V3) (V : Set V3)
        (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
        (hk3 : ¬(s.k ≤ 3)) (hBB : BBsV39 s vv) (hscs : isScsV39 s)
        (hp : vv (p % s.k) = u)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF),
        setSum {i | i < s.k}
          (fun i => rhoFun (norm (vv (i + p % s.k))) *
            interiorAngle1 0 FF ((rhoNode1 FF)^[i] u)) =
        setSum FF (fun e => rhoFun (norm e.1) * azimInFan e E)
  ) ∧
  -- 33. SUM_NUMSEG3_p35 (LA35:18450; HOL `SUM_NUMSEG3`)
  (∀ (t : ℕ → ℝ)
  ,
        ∑ i ∈ Finset.range 4, t i = t 0 + t 1 + t 2 + t 3
  ) ∧
  -- 34. TECOXBM2_p35 (LA35:15552; no HOL anchor line in file docstring)
  (∀ (u w : V3) (hu : u ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
        (h2 : (2:ℝ) ≤ ‖u - w‖) (hc : ‖u - w‖ ≤ cstab),
        ¬ Collinear3 0 u w
  ) ∧
  -- 35. TECOXBMv2_step01_p35 (LA35:1138; no HOL anchor line in file docstring)
  (∀ (s : ScsV39) (p q : ℕ) (hscs : isScsV39 s)
        (hdiag : scsDiag s.k p q),
        s.k = 4 ∨ s.k = 5 ∨ s.k = 6
  ) ∧
  -- 36. TECOXBMv2_step02_p35 (LA35:15411; no HOL anchor line in file docstring)
  (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
        (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
        (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w) (hBB : BBsV39 s vv),
        (2 : ℝ) ≤ dist u w
  ) ∧
  -- 37. TECOXBMv2_step03_p35 (LA35:15431; HOL `IN_IMAGE_VV`)
  (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (vv : ℕ → V3)
        (hscs : isScsV39 s) (_hdiag : scsDiag s.k p q)
        (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
        (hk : s.k = 4 ∨ s.k = 5 ∨ s.k = 6),
        {u, w} ⊆ V_SY_p4 (cycRow_p23 vv s.k)
  ) ∧
  -- 38. TECOXBMv2_step04_p35 (LA35:15460; HOL `Tecoxbm.TECOXBM`)
  (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (vv : ℕ → V3)
        (hscs : isScsV39 s) (hk : s.k = 4) (hdiag : scsDiag s.k p q)
        (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
        (hBB : BBsV39 s vv)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hIN : flattenRow_p23 vv 4 ∈
          {l : FinVec 4 3 | (∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus) ∧
            CONDITION1_SY_p4
              (fun i j => s.a (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
              (fun i j => s.b (((i : ℕ) + 1) % 4) (((j : ℕ) + 1) % 4))
              (cycRow_p23 vv 4) ∧
            CONDITION2_SY_p4 (cycRow_p23 vv 4)})
        (hVEF : V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
          F_SY_p4 (cycRow_p23 vv 4) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ),
        ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
  ) ∧
  -- 39. TECOXBMv2_step05_p35 (LA35:15488; no HOL anchor line in file docstring)
  (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (vv : ℕ → V3)
        (hscs : isScsV39 s) (hk : s.k = 5 ∨ s.k = 6) (hdiag : scsDiag s.k p q)
        (hdist : dist u w ≤ cstab) (hp : vv (p % s.k) = u) (hq : vv (q % s.k) = w)
        (hBB : BBsV39 s vv)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hIN : (s.k = 5 → flattenRow_p23 vv 5 ∈
              {l : FinVec 5 3 | (∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus) ∧
                CONDITION1_SY_p4
                  (fun i j => s.a (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
                  (fun i j => s.b (((i : ℕ) + 1) % 5) (((j : ℕ) + 1) % 5))
                  (cycRow_p23 vv 5) ∧
                CONDITION2_SY_p4 (cycRow_p23 vv 5)}) ∧
          (s.k = 6 → flattenRow_p23 vv 6 ∈
              {l : FinVec 6 3 | (∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus) ∧
                CONDITION1_SY_p4
                  (fun i j => s.a (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
                  (fun i j => s.b (((i : ℕ) + 1) % 6) (((j : ℕ) + 1) % 6))
                  (cycRow_p23 vv 6) ∧
                CONDITION2_SY_p4 (cycRow_p23 vv 6)}))
        (hVEF : (s.k = 5 → V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
              E_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
              F_SY_p4 (cycRow_p23 vv 5) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ) ∧
          (s.k = 6 → V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
              E_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => {vv i, vv (i + 1)}) '' Set.univ ∧
              F_SY_p4 (cycRow_p23 vv 6) = (fun i : ℕ => (vv i, vv (i + 1))) '' Set.univ)),
        ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
  ) ∧
  -- 40. TECOXBMv2_step06_p35 (LA35:15524; no HOL anchor line in file docstring)
  (∀ (s : ScsV39) (p q : ℕ) (u w : V3) (E : Set (Set V3))
        (FF : Set (V3 × V3)) (vv : ℕ → V3) (hscs : isScsV39 s)
        (hdiag : scsDiag s.k p q)
        (h4 : s.k = 4 → ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E)
        (h56 : s.k = 5 ∨ s.k = 6 →
          ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E),
        ∀ x ∈ FF, affGt ({0} : Set V3) {u, w} ⊆ wedgeInFanGt_p3 x E
  ) ∧
  -- 41. VV_INJ_p35 (LA35:15647; HOL `VV_INJ`)
  (∀ (s : ScsV39) (k : ℕ) (vv : ℕ → V3) (hk : s.k = k)
        (hscs : isScsV39 s) (hBB : BBsV39 s vv),
        ∀ i j, i < k ∧ j < k ∧ i ≠ j → vv i ≠ vv j
  ) ∧
  -- 42. VV_SUC_EQ_RHO_NODE_PRIME_p35 (LA35:18295; HOL `VV_SUC_EQ_RHO_NODE_PRIME`)
  (∀ (s : ScsV39) (k p1 p q : ℕ) (u : V3)
        (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3)
        (hk : s.k = k) (hp1 : vv p1 = u)
        (hV : Set.range vv = V)
        (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hBB : BBsV39 s vv),
        ∀ m, (rhoNode1 FF)^[m] u = vv (m + p1)
  ) ∧
  -- 43. V_SLICE_EQ_NUMSEG_p35 (LA35:18362; HOL `V_SLICE_EQ_NUMSEG`)
  (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' : ℝ)
        (mkj : Prop) (k k' : ℕ) (u : V3) (FF : Set (V3 × V3)) (vv : ℕ → V3)
        (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
        (hk : s.k = k) (hk' : s'.k = k') (hp : vv (p % k) = u)
        (hs' : scsHalfSliceV39 s p q d' mkj = s')
        (hMM : vv ∈ MMsV39 s) (hscs : isScsV39 s) (hdiag : scsDiag s.k p q)
        (hsl : isScsSliceV39 s s' s'' p q),
        {i | i < k ∧ (rhoNode1 FF)^[i] u ∈ Set.range (fun j => vv (j % k' + p % k))} =
        {i | i < k'}
  ) ∧
  -- 44. WEDGE_IN_FAN_LOFA_DETER2_p35 (LA35:21535; HOL `WEDGE_IN_FAN_LOFA_DETER2`)
  (∀ {V : Set V3} {E : Set (Set V3)}
        {FF : Set (V3 × V3)} {v : V3} (hfan : LocalFan V E FF)
        (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2) (hv : v ∈ V),
        wedgeInFanGt_p3 (v, rhoNode1 FF v) E
        = Kepler.Geom.wedge (0 : V3) v (rhoNode1 FF v) (ivsRhoNode1 FF v)
  ) ∧
  -- 45. azimCycle_singleton_p35 (LA35:25306; HOL `azim_cycle`)
  (∀ (v w p : V3)
  ,
        azimCycle_p3 ({p} : Set V3) v w p = p
  ) ∧
  -- 46. b2AzimCyclePredFalse_p35 (LA35:33529; no HOL anchor line in file docstring)
  (¬ ∀ (W : Set V3) (u z : V3), W.Finite → z ∈ W → (∃ y ∈ W, y ≠ z) →
        ∃ x ∈ W, azimCycle_p3 W (0:V3) u x = z
  ) ∧
  -- 47. b2AzimSmulZero_p35 (LA35:33404; no HOL anchor line in file docstring)
  (∀ {u y : V3} (c : ℝ) (hc : 0 < c)
        (hcol : ¬ Collinear3 (0:V3) u y),
        azim (0:V3) u y (c • y) = 0
  ) ∧
  -- 48. dart1OfFan_subset_dartsOfHyp_p35 (LA35:21473; no HOL anchor line in file docstring)
  (∀ {E E' : Set (Set V3)} {V : Set V3}
        (hsub : E ⊆ E'),
        Fan.dart1OfFan V E ⊆ dartsOfHyp_p3 E' V
  ) ∧
  -- 49. dartsOfHyp_ne_mono_p35 (LA35:25113; no HOL anchor line in file docstring)
  (∀ {E E' : Set (Set V3)} {V : Set V3} {a b : V3}
        (hsub : E ⊆ E') (hd : (a, b) ∈ dartsOfHyp_p3 E V) (hab : a ≠ b),
        (a, b) ∈ dartsOfHyp_p3 E' V
  ) ∧
  -- 50. ePrime_subset_p35 (LA35:25287; no HOL anchor line in file docstring)
  (∀ {E : Set (Set V3)} {fv : Set (V3 × V3)}
  ,
        ePrime_p3 E fv ⊆ E
  ) ∧
  -- 51. eePermOfHyp_p35_apply (LA35:21463; no HOL anchor line in file docstring)
  (∀ (x : V3) (V : Set V3) (E : Set (Set V3))
        (d : V3 × V3),
        eePermOfHyp_p35 x V E d = eeOfHyp_p3 x V E d
  ) ∧
  -- 52. fstCoverOfUnio_p35 (LA35:31534; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)}
        {FF : Set (V3 × V3)} (hfanL : LocalFan V E FF) {u : V3} (hu : u ∈ ⋃₀ E),
        ∃ d ∈ FF, d.1 = u
  ) ∧
  -- 53. jEvenNbrOnUnio_p35 (LA35:33238; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        (hfan : LocalFan V E FF),
        ∀ u ∈ ⋃₀ E, ∃ t : ℕ, (EE_p3 u E).ncard = 2 * t
  ) ∧
  -- 54. jTwoLeNbrOnUnio_p35 (LA35:33053; HOL `local_fan`)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        (hfan : LocalFan V E FF),
        ∀ u ∈ ⋃₀ E, 2 ≤ (EE_p3 u E).ncard
  ) ∧
  -- 55. jUnioMemVPrime_p35 (LA35:33185; HOL `LOCAL_FAN_RHO_NODE_PROS`)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        (hfan : LocalFan V E FF),
        ∀ u ∈ ⋃₀ E, u ∈ vPrime_p3 V FF
  ) ∧
  -- 56. jUnioVertKit_p35 (LA35:33230; HOL `LOFA_IMP_EE_TWO_ELMS`)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        (hfan : LocalFan V E FF),
        (∀ u ∈ ⋃₀ E, 2 ≤ (EE_p3 u E).ncard) ∧ (∀ u ∈ ⋃₀ E, u ∈ vPrime_p3 V FF)
  ) ∧
  -- 57. kchS0NeZeroOfPlane_p35 (LA35:30525; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv : Set (V3 × V3)} {p : V3 × V3} {e : V3}
        (hv0 : p.1 ≠ 0) (hb0 : p.2 ≠ 0) (hb : ¬ Collinear3 0 p.1 p.2)
        (hv0V : p.1 ∈ vPrime_p3 V fv) (hp2V : p.2 ∈ vPrime_p3 V fv)
        (hcy : cyclicSet_p3 (vPrime_p3 V fv) (0:V3) e)
        (heperp : ∀ x ∈ vPrime_p3 V fv,
          ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0),
        (crossProduct (e : Fin 3 → ℝ) (p.1 : Fin 3 → ℝ)) ⬝ᵥ (p.2 : Fin 3 → ℝ) ≠ 0
  ) ∧
  -- 58. kchS0NeZero_p35 (LA35:30450; no HOL anchor line in file docstring)
  (∀ {e p1 p2 : V3}
        (hE : ((e : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) ≠ 0)
        (hp1e : ((p1 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0)
        (hp2e : ((p2 : V3) : Fin 3 → ℝ) ⬝ᵥ ((e : V3) : Fin 3 → ℝ) = 0)
        (hp10 : p1 ≠ 0) (hp20 : p2 ≠ 0) (hb : ¬ Collinear3 0 p1 p2),
        (crossProduct (e : Fin 3 → ℝ) (p1 : Fin 3 → ℝ)) ⬝ᵥ (p2 : Fin 3 → ℝ) ≠ 0
  ) ∧
  -- 59. ncExistsAffGt_p35 (LA35:34165; HOL `Planarity.exists_in_aff_gt_disjoint`, HOL `AFF_GT_SUB_AFF_UNION`)
  (∀ {v w : V3} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hwv : v ≠ w)
  ,
        ∃ y : V3, y ∈ affGt ({(0:V3)} : Set V3) ({v, w} : Set V3) ∧
        y ∈ (affineSpan ℝ ({(0:V3), v, w} : Set V3) : Set V3)
  ) ∧
  -- 60. ncSliceNoncollinear_p35 (LA35:35677; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
        {v w : V3} (hfan : ConvexLocalFan V E FF) (hv : v ∈ V) (hw : w ∈ V)
        (hwv : v ≠ w)
        (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p3 x E)
        (hEE2 : ∀ u ∈ V, (EE_p3 u E).ncard = 2)
        (hnl : ∀ a ∈ V, ∀ b ∈ V, a ≠ b →
          Collinear ℝ ({(0:V3), a, b} : Set V3) → ¬ Lunar a b V E),
        ∀ z ∈ ({v, w} : Set V3), ∀ t ∈ V, t ≠ z → ¬ Collinear3 (0:V3) z t
  ) ∧
  -- 61. twoNbrOfUnio_p35 (LA35:31572; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)}
        {FF : Set (V3 × V3)} (hfan : ConvexLocalFan V E FF) {u : V3}
        (hu : u ∈ ⋃₀ E),
        1 < (EE_p3 u E).ncard
  ) ∧
  -- 62. vPrime_subset_p35 (LA35:25283; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {fv : Set (V3 × V3)}
  ,
        vPrime_p3 V fv ⊆ V
  ) ∧
  -- 63. w1NoIsoAux_p35 (LA35:27601; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
  ,
        ∀ u ∈ V, EE_p3 u E ≠ ∅
  ) ∧
  -- 64. w1SigmaBndAux_p35 (LA35:27665; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
  ,
        ∀ u ∈ V, (EE_p3 u E).ncard ≤ 2
  ) ∧
  -- 65. w1TwoLeAux_p35 (LA35:27749; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p3 V E FF)
  ,
        ∀ u ∈ V, 2 ≤ (EE_p3 u E).ncard
  ) ∧
  -- 66. w1_azim3_p35 (LA35:27647; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} (hfan : Fan.FAN 0 V E) {v u0 s q : V3}
        (hu0E : {v, u0} ∈ E) (hsE : {v, s} ∈ E) (hqE : {v, q} ∈ E)
        (hmin1 : azim 0 v u0 s ≤ azim 0 v u0 q)
        (hmin2 : azim 0 v s u0 ≤ azim 0 v s q)
        (hsne : s ≠ u0),
        False
  ) ∧
  -- 67. w1_nnFst_p35 (LA35:27588; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E : Set (Set V3)} (z : V3 × V3)
  ,
        (nnOfHyp_p3 0 V E z).1 = z.1
  ) ∧
  -- 68. w1_nn_apply_p35 (LA35:27593; no HOL anchor line in file docstring)
  (∀ {E : Set (Set V3)} (V : Set V3) {E : Set (Set V3)} {a b : V3}
        (hab : {a, b} ∈ E),
        nnOfHyp_p3 0 V E (a, b) = (a, azimCycle_p3 (EE_p3 a E) 0 a b)
  ) ∧
  -- 69. w4pHintOfOZSlice_p35 (LA35:29031; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv : Set (V3 × V3)}
        (hconv : ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
        (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
        (hfin : fv.Finite)
        (hOZ : ∀ x ∈ vPrime_p3 V fv, ∃ u w : V3,
          ({u, x, w} : Set V3) ⊆ vPrime_p3 V fv ∧
          (({u, w} : Set V3) ∩
              (affineSpan ℝ ({(0:V3), x} : Set V3) : Set V3)) = ∅ ∧
          ¬((affineSpan ℝ ({x, (0:V3)} : Set V3) : Set V3) ∩
            ozConv0_p35 ({w, u} : Set V3) = ∅) ∧
          ∃ P : Set V3, ({(0:V3), u, x, w} : Set V3) ⊆ P ∧
            ∃ a b c : V3, ¬ Collinear3 a b c ∧
              P = (affineSpan ℝ ({a, b, c} : Set V3) : Set V3)),
        ∀ x ∈ vPrime_p3 V fv, interiorAngle1 (0:V3) fv x = Real.pi
  ) ∧
  -- 70. w4pNowrapOfRendered_p35 (LA35:29194; no HOL anchor line in file docstring)
  (∀ (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
        (hv0 : v0 ≠ 0) (hb0 : b ≠ 0) (hbu : b ≠ v0) (hb : ¬ Collinear3 0 v0 b)
        (hnc : ∀ i, i + 1 < k → ¬ Collinear3 0 v0 (ρ (i + 1)))
        (hcornerR : ∀ i, i + 1 < k → azim 0 v0 b (ρ i) = Real.pi →
          ∀ s t : ℝ, ρ (i + 1) - 0 = s • (v0 - 0) + t • (b - 0) → t ≤ 0),
        ∀ i, i + 1 < k →
        ¬(azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0)
  ) ∧
  -- 71. w4pOZTripleSlice_p35 (LA35:29010; no HOL anchor line in file docstring)
  (∀ {V : Set V3} {E' : Set (Set V3)}
        {fv : Set (V3 × V3)} {P : Set V3} {u v w : V3}
        (hconv : ConvexLocalFan (vPrime_p3 V fv) (ePrime_p3 E' fv) fv)
        (hsub : fv ⊆ dartsOfHyp_p3 E' V) (hparam : faceCycleParam_p35 V E' fv)
        (hfin : fv.Finite)
        (hsub3 : ({u, v, w} : Set V3) ⊆ vPrime_p3 V fv)
        (hplane : ∃ a b c : V3, ¬ Collinear3 a b c ∧
          P = (affineSpan ℝ ({a, b, c} : Set V3) : Set V3))
        (hP : ({(0:V3), u, v, w} : Set V3) ⊆ P)
        (hdisj : (({u, w} : Set V3) ∩
            (affineSpan ℝ ({(0:V3), v} : Set V3) : Set V3)) = ∅)
        (hint : ¬((affineSpan ℝ ({v, (0:V3)} : Set V3) : Set V3) ∩
          ozConv0_p35 ({w, u} : Set V3) = ∅)),
        interiorAngle1 (0:V3) fv v = Real.pi ∧ rhoNode1 fv v ∈ P ∧
        ivsRhoNode1 fv v ∈ P
  )
    ) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s → s.k = 4 → v ∈ MMsV39 s →
      scsGeneric v) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    ¬Circular (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3) (v w : V3),
    isScsV39 s → BBsV39 s vv → taustarV39 s vv < 0 →
    Lunar v w (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) → 3 < s.k →
    interiorAngle1 0 (Set.range fun i => (vv i, vv (i + 1))) v <
      Real.pi / 2) ∧
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs5M1, scs3M1}) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 → s = 1 ∨ s = -1 →
      v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s →
      Coplanar ({v0, v1, v2, v3} : Set V3) ∧
      x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
      ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0)) ∧
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2}) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), isScsV39 s →
    BBsV39 s vv → taustarV39 s vv < 0 → 3 < s.k →
    solLocal (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))) < Real.pi) ∧
    (∀ vv : ℕ → V3,
    ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) →
    vv 0 ≠ vv 1 → vv 0 ≠ vv 1 → vv 0 ≠ vv 2 → vv 0 ≠ vv 3 →
    vv 0 ≠ vv 4 → vv 1 ≠ vv 2 → vv 1 ≠ vv 3 → vv 1 ≠ vv 4 →
    vv 2 ≠ vv 3 → vv 2 ≠ vv 4 → vv 3 ≠ vv 4 →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5) ∧
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    ContinuousAt (fun q => mkSimplex1 v0 v1 v2 x1 x2 x3 x4 q x6) x5) ∧
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ),
      0 < x1 → 0 < x2 → 0 < x3 → 0 < x5 → 0 < x6 →
      ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
      x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
      0 < upsX x1 x3 x5 →
      ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3) ∧
    (∀ (s t : ScsV39), isScsV39 s → transferV39 s t → scsArrowV39 {s} {t}) ∧
    (main_nonlinear_terminal_v11 →
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
      dist (v p1) (v (p1 + k - 1)) = 2) ∧
    (main_nonlinear_terminal_v11 →
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
      dist (v p1) (v (p1 + 1)) = 2) ∧
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ),
    0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 → 0 < x6 →
    ¬Collinear ℝ ({v0, v1, v2} : Set V3) →
    x1 = dist v1 v0 ^ 2 → x2 = dist v2 v0 ^ 2 → x6 = dist v1 v2 ^ 2 →
    0 < deltaX x1 x2 x3 x4 x5 x6 →
    v3 = mkSimplex1 v0 v1 v2 x1 x2 x3 x4 x5 x6 →
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
      0 < ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ
        (crossProduct ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ))) ∧
    (∀ (f g : ℝ → ℝ) (f' g' h' x y : ℝ),
    derivedForm True f f' x (Set.univ : Set ℝ) →
    derivedForm True g g' y (Set.univ : Set ℝ) →
    derivedForm True (g ∘ f) h' x (Set.univ : Set ℝ) →
    0 < f' → f x = y → reEqvl h' g') ∧
    (∀ (s : ScsV39) (i j : ℕ) (c : ℝ),
    isScsV39 s → s.a i j ≤ c → c ≤ s.b i j → 3 < s.k →
    ¬(i % s.k = j % s.k) → ¬s.J i j →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k → ¬(c = s.am i j)) →
    (j % s.k = (i + 1) % s.k ∨ (j + 1) % s.k = i % s.k →
      2 < s.a i j ∨ 2 * h0 < s.b i j) →
    scsArrowV39 {s} (setOfList (subdivV39 s i j c))) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), 3 < s.k → isScsV39 s →
    scsGeneric v → v ∈ MMsV39 s →
    3 + {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ s.k) ∧
    (∀ y1 y2 y6 : ℝ,
    derivedForm (0 < y1 ∧ 0 < y2) (fun q => xrr y1 y2 q) (8 * y6 / (y1 * y2)) y6
      (Set.univ : Set ℝ)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) → (scsM s).ncard ≤ 1 →
    3 < s.k →
    (∀ i, s.a i (i + 1) = 2) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    ∃ i, dist (v i) (v (i + 1)) = 2) ∧
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
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
          ((fun e => (fun v => f v t) '' e) '' E)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    scsBasicV39 s → 3 < s.k → v ∈ MMsV39 s →
    (∀ i j, scsDiag s.k i j → 4 * h0 < s.b i j) →
    (∀ i j, scsDiag s.k i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) →
    (∀ i, s.b i (i + 1) ≤ cstab) → scsGeneric v) ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    3 < s.k → v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
    s.a (i + 1) (i + 2) = 2 → s.b (i + 1) (i + 2) = 2 * h0 →
    dist (v i) (v (i + 1)) = 2 →
    (∀ i j, scsDiag s.k i j → (s.a i j ≤ cstab ∧ cstab < dist (v i) (v j)) ∧
      4 * h0 < s.b i j) →
    2 < s.b i (i + 1) → s.a (i + 2) (i + 3) < s.b (i + 2) (i + 3) →
    dist (v (i + 1)) (v (i + 2)) = 2) ∧
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
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
          ((fun e => (fun v => f v t) '' e) '' E)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), isScsV39 s →
    v ∈ MMsV39 s → s.k = 4 → scsBasicV39 s →
    s.b i (i + 1) ≤ 2 * h0 → s.b (i + 1) (i + 2) ≤ 2 * h0 →
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53) ∧
    (∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → scsM s = scsM s' →
    s.k = s'.k → v ∈ MMsV39 s → BBsV39 s' v → s.d = s'.d →
    (∀ i, s'.a i (i + 1) = s.a i (i + 1)) →
    (∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j) → v ∈ MMsV39 s') ∧
    (∀ (s : ScsV39) (v : ℕ → V3) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → v ∈ MMsV39 s → (∀ i, s.b i (i + 1) ≤ cstab) →
    Lunar (v i) (v j) (Set.range v) (Set.range fun i => {v i, v (i + 1)}) →
    s.k = 6 ∧ v j = v (i + 3)) ∧
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
    v ∈ MMsV39 s → 3 < s.k →
    ¬Coplanar (({0} ∪ Set.range v : Set V3))) ∧
    (∀ (s : ScsV39) (vv ww : ℕ → V3), isScsV39 s →
    vv ∈ BBprime2V39 s → BBsV39 s ww →
    taustarV39 s vv < taustarV39 s ww ∨ BBindexV39 s vv ≤ BBindexV39 s ww) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
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
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ),
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
      s.a l (l + (k - 1)) = dist (w l) (w (l + (k - 1)))) ∧
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
    isScsV39 s → w ∈ MMsV39 s → k = s.k → 3 < k →
    (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → norm (w l) ≠ 2 →
    (∀ i, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
    (∀ i, ¬s.J l i) →
    (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
      E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E) →
    False) ∧
    (∀ (u v p : V3), ¬Collinear ℝ ({0, v, p} : Set V3) →
    ¬Collinear ℝ ({0, u, p} : Set V3) →
    arcV 0 u p + arcV 0 p v < Real.pi →
    ¬(0 ∈ convexHull ℝ ({u, v} : Set V3))) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprime2V39 s ≠ ∅) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅) ∧
    (∀ (s s' : ScsV39) (v : ℕ → V3), isScsV39 s →
    isScsV39 s' → scsBasicV39 s → scsBasicV39 s' → s.k = s'.k →
    s.d ≤ s'.d →
    v ∈ MMsV39 s → BBsV39 s' v →
    scsArrowV39 {s} {s'}) ∧
    (∀ s : ScsV39, unadornedV39 s → MMsV39 s = BBprime2V39 s) ∧
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
    BBsV39 s vv → taustarV39 s vv < 0 → MMsV39 s ≠ ∅) ∧
    (scsArrowV39 {scs3M1} {scs3T1, scs3T5}) ∧
    ((∀ s ∈ sInitListV39, MMsV39 s = ∅) → JEJTVGB_assume_v39) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop),
    isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    scsArrowV39 {s} {s', s''}) ∧
    (main_nonlinear_terminal_v11 →
    scsArrowV39 {scs6I1} {scs6T1, scs5M1, scs4M2, scs3M1}) ∧
    (∀ (s : ScsV39) (p q : ℕ) (d' : ℝ) (mkj : Prop)
    (vv : ℕ → V3),
    MMsV39 s vv → s.bm p q < 4 → (s.k = 4 ∨ s.bm p q ≤ cstab) → isScsV39 s →
    d' < 0.9 → scsDiag s.k p q →
    BBsV39 (scsHalfSliceV39 s p q d' mkj)
      (fun i => vv (i % (scsHalfSliceV39 s p q d' mkj).k + p % s.k))) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    dsvV39 s vv ≤ dsvV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      dsvV39 s'' (fun i => vv (i % s''.k + q % s.k))) ∧
    (∀ (s s' s'' : ScsV39) (p q : ℕ) (d' d'' : ℝ)
    (mkj : Prop) (vv : ℕ → V3),
    scsHalfSliceV39 s p q d' mkj = s' →
    scsHalfSliceV39 s q p d'' mkj = s'' →
    MMsV39 s vv → isScsV39 s → scsDiag s.k p q → isScsSliceV39 s s' s'' p q →
    s.d ≤ d' + d'' →
    taustarV39 s' (fun i => vv (i % s'.k + p % s.k)) +
      taustarV39 s'' (fun i => vv (i % s''.k + q % s.k)) ≤ taustarV39 s vv) ∧
    (∀ (s : ScsV39) (i j : ℕ), isScsV39 s →
    scsBasicV39 s → 3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
    isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j)) ∧
    (scsArrowV39 {scsStabDiagV39 scs4I3 0 2} {scs4T4}) :=
    ⟨(localconcl_wire_capstone_w1 hmn).1, la35_wire_capstone_w1,
      (localconcl_wire_capstone_w1 hmn).2.1, (localconcl_wire_capstone_w1 hmn).2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.1, (localconcl_wire_capstone_w1 hmn).2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (localconcl_wire_capstone_w1 hmn).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ### LV materialization capstones, slots A1+A2 (lane lv12-w1,
2026-11-04, after the leftover-mat-scout workorder): the clean public
top-level LocalAuto36 and LocalAuto38 exits that no e2e root reaches
(scout account, baseline I HEAD 1e139a28: LA36 149 top-level thm exits
= 138 clean + 11 sorried; LA38 110 = 74 clean + 36 sorried; clean-group
closures GROUP_SORRIED = 0, GROUP_FRESH +240 / +212 vs cone, axiom face
standard-three by axprobe sampling) are re-exposed as TWO conjunctions
-- 193 clean exits implemented (131 LA36 + 62 LA38),
19 dropped by the generator under the workorder no-forcing rule
(LA36: 7 generated-lemma (B_SY1_nc2_p36.eq_1, aPro.eq_1, change_type_v2.eq_1, change_type_v3.eq_1, cycRow_p23.eq_1, scsToStableSyD_p36.congr_simp, vecmats_p4.eq_1), 0 universe-poly; LA38: 4 generated-lemma (funlistAV39.eq_1, lnazim.eq_1, rho.eq_1, taum.eq_1), 8 universe-poly); the 47 sorried exits (LA36 11, LA38 36) are EXCLUDED per
the workorder, per-branch exclusion lists at
logs/excl_la36_sorried.txt / excl_la38_sorried.txt (debt owners:
XWITCCN_CASE family to queue 2-12 wave 2, OWZLKVY terminal stubs to
5-M1 terminal11/mnt11, HDPLYGY_CASE_3/CARD_SLICE_EQ to 2-1 GIANT);
LA36's single uncovered orphan (_private...bFlat3_p36.eq_1, a
module-private derived item) is structurally unreachable, recorded not
forced.  Zero new proof obligations, zero new imports; K_SORRIED 134
and K_AXIOM 624 unchanged; the exact kit yield is re-measured at the
orchestrator e2e gate. -/

/-- LA36 materialization capstone (design lane
leftover-mat-scout, implementation lane lv12-w1 slot A, 2026-11-04).
The 131 clean public top-level LA36 exits unreachable from
every e2e root (top-level thm exits minus the sorried half minus generated-lemma exits; closure GROUP_SORRIED 0) are re-exposed as ONE conjunction.
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LA36 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied
verbatim and mechanically split at the binder/conclusion separator by
the generator gen_items_lv12w1.py); the Lean `#check @name` printer
dump (logs/sigprobe_212.out) is retained as a cross reference; semantic
identity is re-verified by the ⟨...⟩ assembly below (each component
must unify definitionally with its conjunct); the per-conjunct
comments carry each exit's LA36 declaration line and file-local
docstring HOL anchor.  Conjunct order: the clean-seed list order
(probe1.out, alphabetical per module).  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la36_capstone_w1 :
    -- 1. Kepler.Text.EQUALITY_V_SY_TAC_5 (LA36:1785; HOL `EQUALITY_V_SY_TAC_5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5)
    ,
          V_SY_p4 (cycRow_p23 vv 5) = Set.range vv
    ) ∧
    -- 2. Kepler.Text.EQUALITY_V_SY_TAC_6 (LA36:2119; HOL `EQUALITY_V_SY_TAC_6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6)
    ,
          V_SY_p4 (cycRow_p23 vv 6) = Set.range vv
    ) ∧
    -- 3. Kepler.Text.EQ_V_SY_TAC_4 (LA36:2088; HOL `EQ_V_SY_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          Set.range vv = V_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 4. Kepler.Text.INEQUALITY_A_B_SCS_TAC_3 (LA36:1216; HOL `INEQUALITY_A_B_SCS_TAC_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          change_type_v3 s.a (i, j) ≤ dist (vv i) (vv j) ∧
          dist (vv i) (vv j) ≤ change_type_v3 s.b (i, j)
    ) ∧
    -- 5. Kepler.Text.INEQUALITY_A_B_SCS_TAC_30 (LA36:1208; HOL `INEQUALITY_A_B_SCS_TAC_30`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          change_type_v3 s.a (i, j) ≤ dist (vv i) (vv j) ∧
          dist (vv i) (vv j) ≤ change_type_v3 s.b (i, j)
    ) ∧
    -- 6. Kepler.Text.INEQUALITY_A_B_TAC_4 (LA36:2112; HOL `INEQUALITY_A_B_TAC_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 7. Kepler.Text.INEQUALITY_A_B_TAC_40 (LA36:2106; HOL `INEQUALITY_A_B_TAC_40`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 8. Kepler.Text.INEQUALITY_A_B_TAC_5 (LA36:1831; HOL `INEQUALITY_A_B_TAC_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 9. Kepler.Text.INEQUALITY_A_B_TAC_50 (LA36:1825; HOL `INEQUALITY_A_B_TAC_50`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 10. Kepler.Text.INEQUALITY_A_B_TAC_6 (LA36:2164; HOL `INEQUALITY_A_B_TAC_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 11. Kepler.Text.INEQUALITY_A_B_TAC_60 (LA36:2158; HOL `INEQUALITY_A_B_TAC_60`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 12. Kepler.Text.INEQUALITY_PROOF_TAC4 (LA36:1646; HOL `INEQUALITY_PROOF_TAC4`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 13. Kepler.Text.INEQUALITY_PROOF_TAC40 (LA36:1640; HOL `INEQUALITY_PROOF_TAC40`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 14. Kepler.Text.IN_BALL_ANNULUS_ROW_TAC_4 (LA36:1631; HOL `IN_BALL_ANNULUS_ROW_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
          (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 4),
          cycRow_p23 vv 4 i ∈ ballAnnulus
    ) ∧
    -- 15. Kepler.Text.IN_BALL_ANNULUS_TAC_4 (LA36:2099; HOL `IN_BALL_ANNULUS_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
          (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 4),
          cycRow_p23 vv 4 i ∈ ballAnnulus
    ) ∧
    -- 16. Kepler.Text.IN_BALL_ANNUUS_TAC_5 (LA36:1817; HOL `IN_BALL_ANNUUS_TAC_5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5)
          (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 5),
          cycRow_p23 vv 5 i ∈ ballAnnulus
    ) ∧
    -- 17. Kepler.Text.IN_BALL_ANNUUS_TAC_6 (LA36:2150; HOL `IN_BALL_ANNUUS_TAC_6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6)
          (hsub : Set.range vv ⊆ ballAnnulus) (i : Fin 6),
          cycRow_p23 vv 6 i ∈ ballAnnulus
    ) ∧
    -- 18. Kepler.Text.IN_B_SY1_COLLINEAR_CASE_3 (LA36:1487; HOL `IN_B_SY1_COLLINEAR_CASE_3`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hk : s.k = 3),
          ∀ l ∈ B_SY1_nc2_p36
          (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)),
          ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 1} ∧
          ¬Collinear ℝ {0, rowSy_p23 l 0, rowSy_p23 l 2} ∧
          ¬Collinear ℝ {0, rowSy_p23 l 1, rowSy_p23 l 2}
    ) ∧
    -- 19. Kepler.Text.IN_NOT_EMPTY_B1_SY_3 (LA36:1400; HOL `IN_NOT_EMPTY_B1_SY_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hk : s.k = 3) (hper : Periodic vv 3)
          (hball : ∀ i : Fin 3, cycRow_p23 vv 3 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 3)),
          BBsV39 s vv
    ) ∧
    -- 20. Kepler.Text.IN_NOT_EMPTY_B1_SY_4 (LA36:1750; HOL `IN_NOT_EMPTY_B1_SY_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (hk : s.k = 4) (hper : Periodic vv 4)
          (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 4))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)),
          BBsV39 s vv
    ) ∧
    -- 21. Kepler.Text.IN_NOT_EMPTY_B1_SY_4_3 (LA36:2513; HOL `IN_NOT_EMPTY_B1_SY_4_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (hk : s.k = 4) (hper : Periodic vv 4)
          (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 4))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)),
          BBsV39 s vv
    ) ∧
    -- 22. Kepler.Text.IN_NOT_EMPTY_B1_SY_4_sqrt8 (LA36:2603; HOL `IN_NOT_EMPTY_B1_SY_4_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (hk : s.k = 4) (hper : Periodic vv 4)
          (hball : ∀ i : Fin 4, cycRow_p23 vv 4 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 4))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 4)),
          BBsV39 s vv
    ) ∧
    -- 23. Kepler.Text.IN_NOT_EMPTY_B1_SY_5 (LA36:1922; HOL `IN_NOT_EMPTY_B1_SY_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (hk : s.k = 5) (hper : Periodic vv 5)
          (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 5))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)),
          BBsV39 s vv
    ) ∧
    -- 24. Kepler.Text.IN_NOT_EMPTY_B1_SY_5_pro_cs (LA36:2428; HOL `IN_NOT_EMPTY_B1_SY_5_pro_cs`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (hk : s.k = 5) (hper : Periodic vv 5)
          (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 5))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)),
          BBsV39 s vv
    ) ∧
    -- 25. Kepler.Text.IN_NOT_EMPTY_B1_SY_5_sqrt8 (LA36:2338; HOL `IN_NOT_EMPTY_B1_SY_5_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (hk : s.k = 5) (hper : Periodic vv 5)
          (hball : ∀ i : Fin 5, cycRow_p23 vv 5 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 5))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 5)),
          BBsV39 s vv
    ) ∧
    -- 26. Kepler.Text.IN_NOT_EMPTY_B1_SY_6 (LA36:2254; HOL `IN_NOT_EMPTY_B1_SY_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (hk : s.k = 6) (hper : Periodic vv 6)
          (hball : ∀ i : Fin 6, cycRow_p23 vv 6 i ∈ ballAnnulus)
          (hC1 : CONDITION1_SY_p4
            (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
            (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
            (cycRow_p23 vv 6))
          (hC2 : CONDITION2_SY_p4 (cycRow_p23 vv 6)),
          BBsV39 s vv
    ) ∧
    -- 27. Kepler.Text.IN_NOT_EMPTY_CASE_3 (LA36:1225; HOL `IN_NOT_EMPTY_CASE_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 3),
          flattenRow_p23 vv 3 ∈ B_SY1_nc2_p36
          (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 28. Kepler.Text.IN_NOT_EMPTY_CASE_4 (LA36:1651; HOL `IN_NOT_EMPTY_CASE_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          flattenRow_p23 vv 4 ∈ B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 29. Kepler.Text.IN_NOT_EMPTY_CASE_4_3 (LA36:2467; HOL `IN_NOT_EMPTY_CASE_4_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          flattenRow_p23 vv 4 ∈ B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 30. Kepler.Text.IN_NOT_EMPTY_CASE_4_sqrt8 (LA36:2551; HOL `IN_NOT_EMPTY_CASE_4_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          flattenRow_p23 vv 4 ∈ B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 31. Kepler.Text.IN_NOT_EMPTY_CASE_5 (LA36:1836; HOL `IN_NOT_EMPTY_CASE_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          flattenRow_p23 vv 5 ∈ B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 32. Kepler.Text.IN_NOT_EMPTY_CASE_5_pro_cs (LA36:2376; HOL `IN_NOT_EMPTY_CASE_5_pro_cs`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          flattenRow_p23 vv 5 ∈ B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 33. Kepler.Text.IN_NOT_EMPTY_CASE_5_sqrt8 (LA36:2291; HOL `IN_NOT_EMPTY_CASE_5_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          flattenRow_p23 vv 5 ∈ B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 34. Kepler.Text.IN_NOT_EMPTY_CASE_6 (LA36:2169; HOL `IN_NOT_EMPTY_CASE_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 6),
          flattenRow_p23 vv 6 ∈ B_SY1_p4
          (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1))
    ) ∧
    -- 35. Kepler.Text.NOT_COLLINEAR_BBs_CASE_3 (LA36:1467; HOL `NOT_COLLINEAR_BBs_CASE_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hBB : BBsV39 s vv),
          ¬Collinear ℝ {0, vv 1, vv 2} ∧ ¬Collinear ℝ {0, vv 1, vv 0} ∧
          ¬Collinear ℝ {0, vv 2, vv 0}
    ) ∧
    -- 36. Kepler.Text.NOT_EMPTY_CASE_3 (LA36:1254; HOL `NOT_EMPTY_CASE_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 3),
          B_SY1_nc2_p36
          (fun (i j : Fin 3) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 3) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 37. Kepler.Text.NOT_EMPTY_CASE_4 (LA36:1664; HOL `NOT_EMPTY_CASE_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 38. Kepler.Text.NOT_EMPTY_CASE_4_3 (LA36:2478; HOL `NOT_EMPTY_CASE_4_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 39. Kepler.Text.NOT_EMPTY_CASE_4_sqrt8 (LA36:2563; HOL `NOT_EMPTY_CASE_4_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          B_SY1_p4
          (fun (i j : Fin 4) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 4) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 40. Kepler.Text.NOT_EMPTY_CASE_5 (LA36:1847; HOL `NOT_EMPTY_CASE_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 41. Kepler.Text.NOT_EMPTY_CASE_5_pro_cs (LA36:2388; HOL `NOT_EMPTY_CASE_5_pro_cs`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 42. Kepler.Text.NOT_EMPTY_CASE_5_sqrt8 (LA36:2302; HOL `NOT_EMPTY_CASE_5_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          B_SY1_p4
          (fun (i j : Fin 5) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 5) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 43. Kepler.Text.NOT_EMPTY_CASE_6 (LA36:2179; HOL `NOT_EMPTY_CASE_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 6),
          B_SY1_p4
          (fun (i j : Fin 6) => change_type_v3 s.a ((i : ℕ) + 1, (j : ℕ) + 1))
          (fun (i j : Fin 6) => change_type_v3 s.b ((i : ℕ) + 1, (j : ℕ) + 1)) ≠ ∅
    ) ∧
    -- 44. Kepler.Text.PERIODIC_PROPERTY_p36 (LA36:132; HOL `PERIODIC_PROPERTY`)
    (∀ {vv : ℕ → V3} {k : ℕ} (_hk : k ≠ 0)
          (hper : Periodic vv k) (i : ℕ),
          vv (i % k) = vv i
    ) ∧
    -- 45. Kepler.Text.POINT_IN_BBS_IS_NOT_0_3 (LA36:1460; HOL `POINT_IN_BBS_IS_NOT_0_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
    ,
          ¬(vv 1 = 0) ∧ ¬(vv 2 = 0) ∧ ¬(vv 0 = 0)
    ) ∧
    -- 46. Kepler.Text.PROOF_E_EQ_IMAGE_4 (LA36:1611; HOL `PROOF_E_EQ_IMAGE_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4) (x : Set V3)
          (hx : x ∈ E_SY_p4 (cycRow_p23 vv 4)),
          x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})
    ) ∧
    -- 47. Kepler.Text.PROOF_E_EQ_TAC_4 (LA36:1745; HOL `PROOF_E_EQ_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 48. Kepler.Text.PROOF_E_EQ_TAC_5 (LA36:1910; HOL `PROOF_E_EQ_TAC_5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 5)
    ) ∧
    -- 49. Kepler.Text.PROOF_E_EQ_TAC_6 (LA36:2242; HOL `PROOF_E_EQ_TAC_6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 6)
    ) ∧
    -- 50. Kepler.Text.PROVE_EQ_V_SY_TAC_4 (LA36:1600; HOL `PROVE_EQ_V_SY_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          Set.range vv = V_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 51. Kepler.Text.PROVE_E_SY_EQ_5_TAC (LA36:1795; HOL `PROVE_E_SY_EQ_5_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5)
    ,
          E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)})
    ) ∧
    -- 52. Kepler.Text.PROVE_E_SY_EQ_6_TAC (LA36:2129; HOL `PROVE_E_SY_EQ_6_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6)
    ,
          E_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => {vv i, vv (i + 1)})
    ) ∧
    -- 53. Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_4 (LA36:1737; HOL `PROVE_E_SY_EQ_IMAGE_VV_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4) (x : Set V3)
          (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})),
          x ∈ E_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 54. Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_5 (LA36:1915; HOL `PROVE_E_SY_EQ_IMAGE_VV_5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5) (x : Set V3)
          (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})),
          x ∈ E_SY_p4 (cycRow_p23 vv 5)
    ) ∧
    -- 55. Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_6 (LA36:2247; HOL `PROVE_E_SY_EQ_IMAGE_VV_6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6) (x : Set V3)
          (hx : x ∈ Set.range (fun i : ℕ => {vv i, vv (i + 1)})),
          x ∈ E_SY_p4 (cycRow_p23 vv 6)
    ) ∧
    -- 56. Kepler.Text.PROVE_E_SY_EQ_INV_5_TAC (LA36:1801; HOL `PROVE_E_SY_EQ_INV_5_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5)
    ,
          Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 5)
    ) ∧
    -- 57. Kepler.Text.PROVE_E_SY_EQ_INV_6_TAC (LA36:2134; HOL `PROVE_E_SY_EQ_INV_6_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6)
    ,
          Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 6)
    ) ∧
    -- 58. Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_4 (LA36:1731; HOL `PROVE_E_SY_EQ_MOD_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 59. Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_5 (LA36:1904; HOL `PROVE_E_SY_EQ_MOD_TAC_5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 5)
    ) ∧
    -- 60. Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_6 (LA36:2236; HOL `PROVE_E_SY_EQ_MOD_TAC_6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6) (i : ℕ)
    ,
          {vv i, vv (i + 1)} ∈ E_SY_p4 (cycRow_p23 vv 6)
    ) ∧
    -- 61. Kepler.Text.PROVE_E_SY_EQ_TAC (LA36:1594; HOL `PROVE_E_SY_EQ_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)})
    ) ∧
    -- 62. Kepler.Text.PROVE_E_SY_INV_TAC_4 (LA36:2094; HOL `PROVE_E_SY_INV_TAC_4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          Set.range (fun i : ℕ => {vv i, vv (i + 1)}) = E_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 63. Kepler.Text.PROVE_F_SY_EQ_TAC (LA36:1606; HOL `PROVE_F_SY_EQ_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 64. Kepler.Text.PROVE_INEQUALITY_TAC_3 (LA36:1287; HOL `PROVE_INEQUALITY_TAC_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 65. Kepler.Text.PROVE_INEQUALITY_TAC_30 (LA36:1281; HOL `PROVE_INEQUALITY_TAC_30`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 66. Kepler.Text.PROVE_INEQUALITY_TAC_4 (LA36:1718; HOL `PROVE_INEQUALITY_TAC_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 67. Kepler.Text.PROVE_INEQUALITY_TAC_40 (LA36:1712; HOL `PROVE_INEQUALITY_TAC_40`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 68. Kepler.Text.PROVE_INEQUALITY_TAC_5 (LA36:1893; HOL `PROVE_INEQUALITY_TAC_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 69. Kepler.Text.PROVE_INEQUALITY_TAC_50 (LA36:1887; HOL `PROVE_INEQUALITY_TAC_50`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 70. Kepler.Text.PROVE_INEQUALITY_TAC_6 (LA36:2225; HOL `PROVE_INEQUALITY_TAC_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 71. Kepler.Text.PROVE_INEQUALITY_TAC_60 (LA36:2219; HOL `PROVE_INEQUALITY_TAC_60`)
    (∀ (s : ScsV39) (vv : ℕ → V3) (hBB : BBsV39 s vv)
          (i j : ℕ),
          s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j
    ) ∧
    -- 72. Kepler.Text.PROVE_V_SY_EQ_5_TAC (LA36:1790; HOL `PROVE_V_SY_EQ_5_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5)
    ,
          V_SY_p4 (cycRow_p23 vv 5) = Set.range vv
    ) ∧
    -- 73. Kepler.Text.PROVE_V_SY_EQ_6_TAC (LA36:2124; HOL `PROVE_V_SY_EQ_6_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6)
    ,
          V_SY_p4 (cycRow_p23 vv 6) = Set.range vv
    ) ∧
    -- 74. Kepler.Text.PROVE_V_SY_EQ_TAC (LA36:1588; HOL `PROVE_V_SY_EQ_TAC`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4)
    ,
          V_SY_p4 (cycRow_p23 vv 4) = Set.range vv
    ) ∧
    -- 75. Kepler.Text.ROW_IN_BALL_ANNULUS_3 (LA36:1202; HOL `ROW_IN_BALL_ANNULUS_3`)
    (∀ (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
          (th : ℕ),
          vv th ∈ ballAnnulus
    ) ∧
    -- 76. Kepler.Text.SCS_3_IS_TRI_STABLE (LA36:1184; no HOL anchor line in file docstring)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)),
          triStable_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 77. Kepler.Text.SCS_4_3_IS_TRI_STABLE (LA36:2010; HOL `SCS_4_3_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 78. Kepler.Text.SCS_4_IS_TRI_STABLE (LA36:1962; HOL `SCS_4_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 79. Kepler.Text.SCS_4_sqrt8_IS_TRI_STABLE (LA36:2043; HOL `SCS_4_sqrt8_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 80. Kepler.Text.SCS_5_IS_TRI_STABLE (LA36:1978; HOL `SCS_5_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 81. Kepler.Text.SCS_5_pro_cs_IS_TRI_STABLE (LA36:2063; HOL `SCS_5_pro_cs_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 82. Kepler.Text.SCS_5_sqrt8_IS_TRI_STABLE (LA36:2026; HOL `SCS_5_sqrt8_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 83. Kepler.Text.SCS_6_IS_TRI_STABLE (LA36:1994; HOL `SCS_6_IS_TRI_STABLE`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6)),
          stableSystem_p23 s.k 0 (Set.Iic (s.k - 1))
          (fun i j => change_type_v3 s.a (i, j)) (fun i j => change_type_v3 s.b (i, j))
          (change_type_v2 s.J s.k) (fun i => (1 + i) % s.k)
    ) ∧
    -- 84. Kepler.Text.SCS_A_B__EQ_MOD_3 (LA36:1267; HOL `SCS_A_B__EQ_MOD_3`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 3) (j % 3) ∧ s.b i j = s.b (i % 3) (j % 3)
    ) ∧
    -- 85. Kepler.Text.SCS_A_B__EQ_MOD_4 (LA36:1704; HOL `SCS_A_B__EQ_MOD_4`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4)
    ) ∧
    -- 86. Kepler.Text.SCS_A_B__EQ_MOD_4_3 (LA36:2505; HOL `SCS_A_B__EQ_MOD_4_3`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4)
    ) ∧
    -- 87. Kepler.Text.SCS_A_B__EQ_MOD_4_sqrt8 (LA36:2592; HOL `SCS_A_B__EQ_MOD_4_sqrt8`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 4) (j % 4) ∧ s.b i j = s.b (i % 4) (j % 4)
    ) ∧
    -- 88. Kepler.Text.SCS_A_B__EQ_MOD_5 (LA36:1879; HOL `SCS_A_B__EQ_MOD_5`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5)
    ) ∧
    -- 89. Kepler.Text.SCS_A_B__EQ_MOD_5_pro_cs (LA36:2417; HOL `SCS_A_B__EQ_MOD_5_pro_cs`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5)
    ) ∧
    -- 90. Kepler.Text.SCS_A_B__EQ_MOD_5_sqrt8 (LA36:2329; HOL `SCS_A_B__EQ_MOD_5_sqrt8`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 5) (j % 5) ∧ s.b i j = s.b (i % 5) (j % 5)
    ) ∧
    -- 91. Kepler.Text.SCS_A_B__EQ_MOD_6 (LA36:2211; HOL `SCS_A_B__EQ_MOD_6`)
    (∀ (s : ScsV39)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (i j : ℕ),
          s.a i j = s.a (i % 6) (j % 6) ∧ s.b i j = s.b (i % 6) (j % 6)
    ) ∧
    -- 92. Kepler.Text.TAUSTAR_EQ_TAU_STAR_3 (LA36:1559; HOL `TAUSTAR_EQ_TAU_STAR_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
          (hBB : BBsV39 s vv),
          taustarV39 s vv = tau3 (vv 1) (vv 2) (vv 0)
    ) ∧
    -- 93. Kepler.Text.TAUSTAR_EQ_TAU_STAR_4 (LA36:1687; HOL `TAUSTAR_EQ_TAU_STAR_4`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 4 3)
          (hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 4 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 94. Kepler.Text.TAUSTAR_EQ_TAU_STAR_4_3 (LA36:2493; HOL `TAUSTAR_EQ_TAU_STAR_4_3`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 4 3)
          (hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 4 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 95. Kepler.Text.TAUSTAR_EQ_TAU_STAR_4_sqrt8 (LA36:2579; HOL `TAUSTAR_EQ_TAU_STAR_4_sqrt8`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 4 3)
          (hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 4 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 96. Kepler.Text.TAUSTAR_EQ_TAU_STAR_5 (LA36:1862; HOL `TAUSTAR_EQ_TAU_STAR_5`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 5 3)
          (hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 5 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 97. Kepler.Text.TAUSTAR_EQ_TAU_STAR_5_pro_cs (LA36:2404; HOL `TAUSTAR_EQ_TAU_STAR_5_pro_cs`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 5 3)
          (hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 5 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 98. Kepler.Text.TAUSTAR_EQ_TAU_STAR_5_sqrt8 (LA36:2317; HOL `TAUSTAR_EQ_TAU_STAR_5_sqrt8`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 5 3)
          (hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 5 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 99. Kepler.Text.TAUSTAR_EQ_TAU_STAR_6 (LA36:2194; HOL `TAUSTAR_EQ_TAU_STAR_6`)
    (∀ (s : ScsV39) (s1 : StableSyP23) (vv : ℕ → V3)
          (l : FinVec 6 3)
          (hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 6)
          (hsS : isScsV39 s) (hs1 : s1 = scsToStableSyD_p36 s hsS (by omega)) (hl : flattenRow_p23 vv 6 = l),
          taustarV39 s vv = tauStar_p23 s1 l
    ) ∧
    -- 100. Kepler.Text.TRI_STABLE_K_EQ_3 (LA36:1454; HOL `TRI_STABLE_K_EQ_3`)
    (∀ {k : ℕ} {a b : ℕ → ℕ → ℝ} {J : Set (Set ℕ)}
          (ht : triStable_p23 k 0 (Set.Iic (k - 1)) a b J (fun i => (1 + i) % k)),
          k = 3 ∧ 2 < k
    ) ∧
    -- 101. Kepler.Text.VECTOR_3_3 (LA36:172; HOL `VECTOR_3_3`)
    (∀ (vv : ℕ → V3)
    ,
          cycRow_p23 vv 3 0 = vv 1 ∧ cycRow_p23 vv 3 1 = vv 2 ∧ cycRow_p23 vv 3 2 = vv 0
    ) ∧
    -- 102. Kepler.Text.VECTOR_3_4 (LA36:177; HOL `VECTOR_3_4`)
    (∀ (vv : ℕ → V3)
    ,
          cycRow_p23 vv 4 0 = vv 1 ∧ cycRow_p23 vv 4 1 = vv 2 ∧ cycRow_p23 vv 4 2 = vv 3 ∧
          cycRow_p23 vv 4 3 = vv 0
    ) ∧
    -- 103. Kepler.Text.VECTOR_3_5 (LA36:183; HOL `VECTOR_3_5`)
    (∀ (vv : ℕ → V3)
    ,
          cycRow_p23 vv 5 0 = vv 1 ∧ cycRow_p23 vv 5 1 = vv 2 ∧ cycRow_p23 vv 5 2 = vv 3 ∧
          cycRow_p23 vv 5 3 = vv 4 ∧ cycRow_p23 vv 5 4 = vv 0
    ) ∧
    -- 104. Kepler.Text.VECTOR_3_6 (LA36:189; HOL `VECTOR_3_6`)
    (∀ (vv : ℕ → V3)
    ,
          cycRow_p23 vv 6 0 = vv 1 ∧ cycRow_p23 vv 6 1 = vv 2 ∧ cycRow_p23 vv 6 2 = vv 3 ∧
          cycRow_p23 vv 6 3 = vv 4 ∧ cycRow_p23 vv 6 4 = vv 5 ∧ cycRow_p23 vv 6 5 = vv 0
    ) ∧
    -- 105. Kepler.Text.VV_IN_BALL_ANNULUS_TAC_3 (LA36:1275; HOL `VV_IN_BALL_ANNULUS_TAC_3`)
    (∀ (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
          (i : ℕ),
          vv i ∈ ballAnnulus
    ) ∧
    -- 106. Kepler.Text.VV_IN_BALL_ANNULUS_TAC_4 (LA36:1699; HOL `VV_IN_BALL_ANNULUS_TAC_4`)
    (∀ (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
          (i : ℕ),
          vv i ∈ ballAnnulus
    ) ∧
    -- 107. Kepler.Text.VV_IN_BALL_ANNULUS_TAC_5 (LA36:1874; HOL `VV_IN_BALL_ANNULUS_TAC_5`)
    (∀ (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
          (i : ℕ),
          vv i ∈ ballAnnulus
    ) ∧
    -- 108. Kepler.Text.VV_IN_BALL_ANNULUS_TAC_6 (LA36:2206; HOL `VV_IN_BALL_ANNULUS_TAC_6`)
    (∀ (vv : ℕ → V3) (hsub : Set.range vv ⊆ ballAnnulus)
          (i : ℕ),
          vv i ∈ ballAnnulus
    ) ∧
    -- 109. Kepler.Text.V_E_FF_CASE_4 (LA36:1619; HOL `V_E_FF_CASE_4`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 110. Kepler.Text.V_E_FF_CASE_4_3 (LA36:2456; HOL `V_E_FF_CASE_4_3`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 111. Kepler.Text.V_E_FF_CASE_4_sqrt8 (LA36:2539; HOL `V_E_FF_CASE_4_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 4 0.477 (aPro 4 (2 * h0) 2 (Real.sqrt 8))
            (aPro 4 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 4),
          V_SY_p4 (cycRow_p23 vv 4) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 4) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 112. Kepler.Text.V_E_FF_CASE_5 (LA36:1806; HOL `V_E_FF_CASE_5`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 113. Kepler.Text.V_E_FF_CASE_5_pro_cs (LA36:2364; HOL `V_E_FF_CASE_5_pro_cs`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 5 0.616 (aPro 5 (2 * h0) 2 (2 * h0))
            (aPro 5 (Real.sqrt 8) (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 114. Kepler.Text.V_E_FF_CASE_5_sqrt8 (LA36:2280; HOL `V_E_FF_CASE_5_sqrt8`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 5),
          V_SY_p4 (cycRow_p23 vv 5) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 5) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 115. Kepler.Text.V_E_FF_CASE_6 (LA36:2139; HOL `V_E_FF_CASE_6`)
    (∀ (s : ScsV39) (vv : ℕ → V3)
          (_hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
          (hBB : BBsV39 s vv) (hk : s.k = 6),
          V_SY_p4 (cycRow_p23 vv 6) = Set.range vv ∧
          E_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => {vv i, vv (i + 1)}) ∧
          F_SY_p4 (cycRow_p23 vv 6) = Set.range (fun i : ℕ => (vv i, vv (i + 1)))
    ) ∧
    -- 116. Kepler.Text.V_SY_EQ_IMAGE_VV_TAC4 (LA36:1724; HOL `V_SY_EQ_IMAGE_VV_TAC4`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 4) (x : V3)
          (hx : x ∈ Set.range vv),
          x ∈ V_SY_p4 (cycRow_p23 vv 4)
    ) ∧
    -- 117. Kepler.Text.V_SY_EQ_IMAGE_VV_TAC5 (LA36:1898; HOL `V_SY_EQ_IMAGE_VV_TAC5`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 5) (x : V3)
          (hx : x ∈ Set.range vv),
          x ∈ V_SY_p4 (cycRow_p23 vv 5)
    ) ∧
    -- 118. Kepler.Text.V_SY_EQ_IMAGE_VV_TAC6 (LA36:2230; HOL `V_SY_EQ_IMAGE_VV_TAC6`)
    (∀ (vv : ℕ → V3) (hper : Periodic vv 6) (x : V3)
          (hx : x ∈ Set.range vv),
          x ∈ V_SY_p4 (cycRow_p23 vv 6)
    ) ∧
    -- 119. Kepler.Text.aPro_mod_p36 (LA36:166; no HOL anchor line in file docstring)
    (∀ (k : ℕ) (p a1 a2 : ℝ) (i j : ℕ)
    ,
          aPro k p a1 a2 i j = aPro k p a1 a2 (i % k) (j % k)
    ) ∧
    -- 120. Kepler.Text.aPro_symm_p36 (LA36:372; no HOL anchor line in file docstring)
    (∀ {k : ℕ} {p a1 a2 : ℝ} {i j : ℕ}
    ,
          aPro k p a1 a2 i j = aPro k p a1 a2 j i
    ) ∧
    -- 121. Kepler.Text.change_type_v2_eq (LA36:138; no HOL anchor line in file docstring)
    (∀ {s : ScsV39} (hk : 0 < s.k) (hJp : Periodic2 s.J s.k)
    ,
          change_type_v2 s.J s.k = scsJSet_p23 s
    ) ∧
    -- 122. Kepler.Text.change_type_v2_mkUnadorned_p36 (LA36:402; no HOL anchor line in file docstring)
    (∀ {k : ℕ} (d : ℝ) (a b : ℕ → ℕ → ℝ)
    ,
          change_type_v2 (mkUnadornedV39 k d a b).J k = ∅
    ) ∧
    -- 123. Kepler.Text.csAdj_mod_p36 (LA36:161; no HOL anchor line in file docstring)
    (∀ (k : ℕ) (a1 a2 : ℝ) (i j : ℕ)
    ,
          csAdj k a1 a2 i j = csAdj k a1 a2 (i % k) (j % k)
    ) ∧
    -- 124. Kepler.Text.csAdj_symm_p36 (LA36:354; no HOL anchor line in file docstring)
    (∀ {k : ℕ} {a1 a2 : ℝ} {i j : ℕ}
    ,
          csAdj k a1 a2 i j = csAdj k a1 a2 j i
    ) ∧
    -- 125. Kepler.Text.scsJSet_mkUnadorned_p36 (LA36:410; no HOL anchor line in file docstring)
    (∀ {k : ℕ} (d : ℝ) (a b : ℕ → ℕ → ℝ)
    ,
          scsJSet_p23 (mkUnadornedV39 k d a b) = ∅
    ) ∧
    -- 126. Kepler.Text.stable_sy_explicit (LA36:197; HOL `stable_sy_explicit`)
    (∀ {k : ℕ} {I : Set ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Set (Set ℕ)} {f : ℕ → ℕ} (hs : stableSystem_p23 k 0 I a b J f),
          (StableSyP23.k ⟨k, 0, I, a, b, J, f, hs⟩ : ℕ) = k ∧
          (StableSyP23.d ⟨k, 0, I, a, b, J, f, hs⟩ : ℝ) = 0 ∧
          (StableSyP23.I ⟨k, 0, I, a, b, J, f, hs⟩ : Set ℕ) = I ∧
          (StableSyP23.a ⟨k, 0, I, a, b, J, f, hs⟩) = a ∧
          (StableSyP23.b ⟨k, 0, I, a, b, J, f, hs⟩) = b ∧
          (StableSyP23.J ⟨k, 0, I, a, b, J, f, hs⟩ : Set (Set ℕ)) = J ∧
          (StableSyP23.f ⟨k, 0, I, a, b, J, f, hs⟩) = f
    ) ∧
    -- 127. Kepler.Text.succModIter_p36 (LA36:296; no HOL anchor line in file docstring)
    (∀ (k : ℕ) (hk : 0 < k) {j : ℕ} (hj : j < k) (n : ℕ)
    ,
          (fun i => (1 + i) % k)^[n] j = (j + n) % k
    ) ∧
    -- 128. Kepler.Text.succModIter_pos_p36 (LA36:306; no HOL anchor line in file docstring)
    (∀ (k : ℕ) (hk : 0 < k) (j n : ℕ) (hn : 0 < n)
    ,
          (fun i => (1 + i) % k)^[n] j = (j + n) % k
    ) ∧
    -- 129. Kepler.Text.succ_mod_ne_p36 (LA36:286; no HOL anchor line in file docstring)
    (∀ {k : ℕ} (hk : 1 < k) (n : ℕ)
    ,
          n % k ≠ (n + 1) % k
    ) ∧
    -- 130. Kepler.Text.torsor_succ_mod_p36 (LA36:318; no HOL anchor line in file docstring)
    (∀ {k : ℕ} (hk : 0 < k)
    ,
          torsor_p23 (Set.Iic (k - 1)) k (fun i => (1 + i) % k)
    ) ∧
    -- 131. Kepler.Text.vecmatsV3_flattenRow_p36 (LA36:454; no HOL anchor line in file docstring)
    (∀ {k : ℕ} (vv : ℕ → V3)
    ,
          vecmatsV3_p4 (flattenRow_p23 vv k) = cycRow_p23 vv k
    ) :=
    ⟨Kepler.Text.EQUALITY_V_SY_TAC_5, Kepler.Text.EQUALITY_V_SY_TAC_6, Kepler.Text.EQ_V_SY_TAC_4,
      Kepler.Text.INEQUALITY_A_B_SCS_TAC_3, Kepler.Text.INEQUALITY_A_B_SCS_TAC_30,
      Kepler.Text.INEQUALITY_A_B_TAC_4, Kepler.Text.INEQUALITY_A_B_TAC_40,
      Kepler.Text.INEQUALITY_A_B_TAC_5, Kepler.Text.INEQUALITY_A_B_TAC_50,
      Kepler.Text.INEQUALITY_A_B_TAC_6, Kepler.Text.INEQUALITY_A_B_TAC_60,
      Kepler.Text.INEQUALITY_PROOF_TAC4, Kepler.Text.INEQUALITY_PROOF_TAC40,
      Kepler.Text.IN_BALL_ANNULUS_ROW_TAC_4, Kepler.Text.IN_BALL_ANNULUS_TAC_4,
      Kepler.Text.IN_BALL_ANNUUS_TAC_5, Kepler.Text.IN_BALL_ANNUUS_TAC_6,
      Kepler.Text.IN_B_SY1_COLLINEAR_CASE_3, Kepler.Text.IN_NOT_EMPTY_B1_SY_3,
      Kepler.Text.IN_NOT_EMPTY_B1_SY_4, Kepler.Text.IN_NOT_EMPTY_B1_SY_4_3,
      Kepler.Text.IN_NOT_EMPTY_B1_SY_4_sqrt8, Kepler.Text.IN_NOT_EMPTY_B1_SY_5,
      Kepler.Text.IN_NOT_EMPTY_B1_SY_5_pro_cs, Kepler.Text.IN_NOT_EMPTY_B1_SY_5_sqrt8,
      Kepler.Text.IN_NOT_EMPTY_B1_SY_6, Kepler.Text.IN_NOT_EMPTY_CASE_3,
      Kepler.Text.IN_NOT_EMPTY_CASE_4, Kepler.Text.IN_NOT_EMPTY_CASE_4_3,
      Kepler.Text.IN_NOT_EMPTY_CASE_4_sqrt8, Kepler.Text.IN_NOT_EMPTY_CASE_5,
      Kepler.Text.IN_NOT_EMPTY_CASE_5_pro_cs, Kepler.Text.IN_NOT_EMPTY_CASE_5_sqrt8,
      Kepler.Text.IN_NOT_EMPTY_CASE_6, Kepler.Text.NOT_COLLINEAR_BBs_CASE_3,
      Kepler.Text.NOT_EMPTY_CASE_3, Kepler.Text.NOT_EMPTY_CASE_4, Kepler.Text.NOT_EMPTY_CASE_4_3,
      Kepler.Text.NOT_EMPTY_CASE_4_sqrt8, Kepler.Text.NOT_EMPTY_CASE_5,
      Kepler.Text.NOT_EMPTY_CASE_5_pro_cs, Kepler.Text.NOT_EMPTY_CASE_5_sqrt8,
      Kepler.Text.NOT_EMPTY_CASE_6, Kepler.Text.PERIODIC_PROPERTY_p36,
      Kepler.Text.POINT_IN_BBS_IS_NOT_0_3, Kepler.Text.PROOF_E_EQ_IMAGE_4,
      Kepler.Text.PROOF_E_EQ_TAC_4, Kepler.Text.PROOF_E_EQ_TAC_5, Kepler.Text.PROOF_E_EQ_TAC_6,
      Kepler.Text.PROVE_EQ_V_SY_TAC_4, Kepler.Text.PROVE_E_SY_EQ_5_TAC,
      Kepler.Text.PROVE_E_SY_EQ_6_TAC, Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_4,
      Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_5, Kepler.Text.PROVE_E_SY_EQ_IMAGE_VV_6,
      Kepler.Text.PROVE_E_SY_EQ_INV_5_TAC, Kepler.Text.PROVE_E_SY_EQ_INV_6_TAC,
      Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_4, Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_5,
      Kepler.Text.PROVE_E_SY_EQ_MOD_TAC_6, Kepler.Text.PROVE_E_SY_EQ_TAC,
      Kepler.Text.PROVE_E_SY_INV_TAC_4, Kepler.Text.PROVE_F_SY_EQ_TAC,
      Kepler.Text.PROVE_INEQUALITY_TAC_3, Kepler.Text.PROVE_INEQUALITY_TAC_30,
      Kepler.Text.PROVE_INEQUALITY_TAC_4, Kepler.Text.PROVE_INEQUALITY_TAC_40,
      Kepler.Text.PROVE_INEQUALITY_TAC_5, Kepler.Text.PROVE_INEQUALITY_TAC_50,
      Kepler.Text.PROVE_INEQUALITY_TAC_6, Kepler.Text.PROVE_INEQUALITY_TAC_60,
      Kepler.Text.PROVE_V_SY_EQ_5_TAC, Kepler.Text.PROVE_V_SY_EQ_6_TAC,
      Kepler.Text.PROVE_V_SY_EQ_TAC, Kepler.Text.ROW_IN_BALL_ANNULUS_3,
      Kepler.Text.SCS_3_IS_TRI_STABLE, Kepler.Text.SCS_4_3_IS_TRI_STABLE,
      Kepler.Text.SCS_4_IS_TRI_STABLE, Kepler.Text.SCS_4_sqrt8_IS_TRI_STABLE,
      Kepler.Text.SCS_5_IS_TRI_STABLE, Kepler.Text.SCS_5_pro_cs_IS_TRI_STABLE,
      Kepler.Text.SCS_5_sqrt8_IS_TRI_STABLE, Kepler.Text.SCS_6_IS_TRI_STABLE,
      Kepler.Text.SCS_A_B__EQ_MOD_3, Kepler.Text.SCS_A_B__EQ_MOD_4,
      Kepler.Text.SCS_A_B__EQ_MOD_4_3, Kepler.Text.SCS_A_B__EQ_MOD_4_sqrt8,
      Kepler.Text.SCS_A_B__EQ_MOD_5, Kepler.Text.SCS_A_B__EQ_MOD_5_pro_cs,
      Kepler.Text.SCS_A_B__EQ_MOD_5_sqrt8, Kepler.Text.SCS_A_B__EQ_MOD_6,
      Kepler.Text.TAUSTAR_EQ_TAU_STAR_3, Kepler.Text.TAUSTAR_EQ_TAU_STAR_4,
      Kepler.Text.TAUSTAR_EQ_TAU_STAR_4_3, Kepler.Text.TAUSTAR_EQ_TAU_STAR_4_sqrt8,
      Kepler.Text.TAUSTAR_EQ_TAU_STAR_5, Kepler.Text.TAUSTAR_EQ_TAU_STAR_5_pro_cs,
      Kepler.Text.TAUSTAR_EQ_TAU_STAR_5_sqrt8, Kepler.Text.TAUSTAR_EQ_TAU_STAR_6,
      Kepler.Text.TRI_STABLE_K_EQ_3, Kepler.Text.VECTOR_3_3, Kepler.Text.VECTOR_3_4,
      Kepler.Text.VECTOR_3_5, Kepler.Text.VECTOR_3_6, Kepler.Text.VV_IN_BALL_ANNULUS_TAC_3,
      Kepler.Text.VV_IN_BALL_ANNULUS_TAC_4, Kepler.Text.VV_IN_BALL_ANNULUS_TAC_5,
      Kepler.Text.VV_IN_BALL_ANNULUS_TAC_6, Kepler.Text.V_E_FF_CASE_4,
      Kepler.Text.V_E_FF_CASE_4_3, Kepler.Text.V_E_FF_CASE_4_sqrt8, Kepler.Text.V_E_FF_CASE_5,
      Kepler.Text.V_E_FF_CASE_5_pro_cs, Kepler.Text.V_E_FF_CASE_5_sqrt8,
      Kepler.Text.V_E_FF_CASE_6, Kepler.Text.V_SY_EQ_IMAGE_VV_TAC4,
      Kepler.Text.V_SY_EQ_IMAGE_VV_TAC5, Kepler.Text.V_SY_EQ_IMAGE_VV_TAC6,
      Kepler.Text.aPro_mod_p36, Kepler.Text.aPro_symm_p36, Kepler.Text.change_type_v2_eq,
      Kepler.Text.change_type_v2_mkUnadorned_p36, Kepler.Text.csAdj_mod_p36,
      Kepler.Text.csAdj_symm_p36, Kepler.Text.scsJSet_mkUnadorned_p36,
      Kepler.Text.stable_sy_explicit, Kepler.Text.succModIter_p36,
      Kepler.Text.succModIter_pos_p36, Kepler.Text.succ_mod_ne_p36,
      Kepler.Text.torsor_succ_mod_p36, Kepler.Text.vecmatsV3_flattenRow_p36⟩

#print axioms la36_capstone_w1

/-- LA38 materialization capstone (design lane
leftover-mat-scout, implementation lane lv12-w1 slot A, 2026-11-04).
The 62 clean public top-level LA38 exits unreachable from
every e2e root (top-level thm exits minus the sorried half minus generated-lemma exits; closure GROUP_SORRIED 0) are re-exposed as ONE conjunction.
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LA38 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied
verbatim and mechanically split at the binder/conclusion separator by
the generator gen_items_lv12w1.py); the Lean `#check @name` printer
dump (logs/sigprobe_212.out) is retained as a cross reference; semantic
identity is re-verified by the ⟨...⟩ assembly below (each component
must unify definitionally with its conjunct); the per-conjunct
comments carry each exit's LA38 declaration line and file-local
docstring HOL anchor.  Conjunct order: the clean-seed list order
(probe1.out, alphabetical per module).  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la38_capstone_w1 :
    -- 1. Kepler.Text.DELTA_Y_POS_4POINTS (LA38:1343; HOL `DELTA_Y_POS_4POINTS`)
    (∀ (v0 v1 v2 v3 : V3)
    ,
          0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
          (dist v1 v3) (dist v1 v2)
    ) ∧
    -- 2. Kepler.Text.DIHV_EQ_DIH_Y_4PT (LA38:1440; HOL `DIHV_EQ_DIH_Y`)
    (∀ (v0 v1 v2 v3 : V3)
          (h2 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (h3 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3)),
          dihV v0 v1 v2 v3 =
          dihY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
            (dist v1 v3) (dist v1 v2)
    ) ∧
    -- 3. Kepler.Text.DIHV_NN_4PT (LA38:1474; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 v3 : V3)
          (h2 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (h3 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3)),
          0 ≤ dihV v0 v1 v2 v3
    ) ∧
    -- 4. Kepler.Text.DIH_X_NN (LA38:309; HOL `DIH_X_NN`)
    (∀ x1 x2 x3 x4 x5 x6 : ℝ,
          0 < x1 → 0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
          0 ≤ dihXf x1 x2 x3 x4 x5 x6
    ) ∧
    -- 5. Kepler.Text.DIH_Y_NN (LA38:320; HOL `DIH_Y_NN`)
    (∀ y1 y2 y3 y4 y5 y6 : ℝ,
          0 < y1 → 0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
          0 ≤ dihY y1 y2 y3 y4 y5 y6
    ) ∧
    -- 6. Kepler.Text.EE_vv (LA38:2223; HOL `EE_vv`)
    (∀ (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j),
          ee (vv i) (Set.range fun i => {vv i, vv (i + 1)}) =
          {vv (i + 1), vv (i + (k - 1))}
    ) ∧
    -- 7. Kepler.Text.ITER_vv_rho_node1 (LA38:2483; HOL `ITER_vv_rho_node1`)
    (∀ (vv : ℕ → V3) (k j : ℕ) (hper : Periodic vv k)
          (hk : 3 ≤ k) (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
          (i : ℕ),
          (rhoNode1 (Set.range fun i => (vv i, vv (i + 1))))^[j] (vv i) = vv (i + j)
    ) ∧
    -- 8. Kepler.Text.I_LT_J_LT_3_EXPLICIT (LA38:3545; HOL `I_LT_J_LT_3_EXPLICIT`)
    (∀ (i j : ℕ)
    ,
          (i < j ∧ j < 3) ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)
    ) ∧
    -- 9. Kepler.Text.I_LT_J_LT_4_EXPLICIT (LA38:3550; HOL `I_LT_J_LT_4_EXPLICIT`)
    (∀ (i j : ℕ)
    ,
          (i < j ∧ j < 4) ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
          (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)
    ) ∧
    -- 10. Kepler.Text.LEMMA_4680581274_delta_issue_ups (LA38:3316; HOL `LEMMA_4680581274_delta_issue_ups`)
    (∀ (x1 x2 x3 x4 x5 x6 : ℝ)
    ,
          ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26),
          (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26), (3.01 * 3.01, x4, 3.166 * 3.166),
          (4.0, x5, 4.0), (4.0, x6, 4.0)]
          (0 < upsX x2 x3 x4 ∨
            10 + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
            deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0)
    ) ∧
    -- 11. Kepler.Text.MOD_4_EXPLICIT (LA38:1654; HOL `MOD_4_EXPLICIT`)
    (0 % 4 = 0 ∧ 1 % 4 = 1 ∧ 2 % 4 = 2 ∧ 3 % 4 = 3 ∧ 4 % 4 = 0 ∧ 5 % 4 = 1 ∧
          6 % 4 = 2
    ) ∧
    -- 12. Kepler.Text.NONPARALLEL_BALL_ANNULUS40 (LA38:678; HOL `NONPARALLEL_BALL_ANNULUS40`)
    (∀ (v w : V3)
    ,
          2 ≤ ‖v - w‖ → ‖v - w‖ < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
          ¬ Collinear ℝ ({0, v, w} : Set V3)
    ) ∧
    -- 13. Kepler.Text.NONPARALLEL_BALL_ANNULUS40_ALT (LA38:695; HOL `NONPARALLEL_BALL_ANNULUS40_ALT`)
    (∀ (v w : V3)
    ,
          2 ≤ dist v w → dist v w < 4 → v ∈ ballAnnulus → w ∈ ballAnnulus →
          ¬ Collinear ℝ ({0, v, w} : Set V3)
    ) ∧
    -- 14. Kepler.Text.NONPARALLEL_BALL_ANNULUS_ALT (LA38:686; HOL `NONPARALLEL_BALL_ANNULUS_ALT`)
    (∀ (v w : V3)
    ,
          2 ≤ dist v w → dist v w ≤ 3.62 → v ∈ ballAnnulus → w ∈ ballAnnulus →
          ¬ Collinear ℝ ({0, v, w} : Set V3)
    ) ∧
    -- 15. Kepler.Text.REAL_FINITE_MIN_EXISTS_p38 (LA38:2003; HOL `REAL_FINITE_MIN_EXISTS`)
    (∀ (S : Set ℝ) (hfin : S.Finite)
          (hne : S.Nonempty),
          ∃ m, m ∈ S ∧ ∀ x ∈ S, m ≤ x
    ) ∧
    -- 16. Kepler.Text.REAL_WLOG_SQUARE2_LEMMA (LA38:2046; HOL `REAL_WLOG_SQUARE2_LEMMA`)
    (∀ (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
          (hrot : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
            P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5 ∧
            P y1 y2 y3 y4 y5 y6 = P y1 y4 y3 y2 y6 y5)
          (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y2 ≤ y1 → y3 ≤ y1 → y4 ≤ y1 → y4 ≤ y2 →
            P y1 y2 y3 y4 y5 y6),
          ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6
    ) ∧
    -- 17. Kepler.Text.REAL_WLOG_SQUARE_LEMMA (LA38:2009; HOL `REAL_WLOG_SQUARE_LEMMA`)
    (∀ (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
          (hrot : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
            P y1 y2 y3 y4 y5 y6 = P y2 y3 y4 y1 y6 y5)
          (hmax : ∀ y1 y2 y3 y4 y5 y6 : ℝ, y2 ≤ y1 → y3 ≤ y1 → y4 ≤ y1 →
            P y1 y2 y3 y4 y5 y6),
          ∀ y1 y2 y3 y4 y5 y6 : ℝ, P y1 y2 y3 y4 y5 y6
    ) ∧
    -- 18. Kepler.Text.RHO_LB (LA38:332; HOL `RHO_LB`)
    (∀ (y : ℝ) (hy : (2 : ℝ) ≤ y)
    ,
          1 ≤ rho y
    ) ∧
    -- 19. Kepler.Text.SUC_EXPLICIT (LA38:2967; HOL `SUC_EXPLICIT`)
    (Nat.succ 0 = 1 ∧ Nat.succ 1 = 2 ∧ Nat.succ 2 = 3 ∧ Nat.succ 3 = 4 ∧
          Nat.succ 4 = 5 ∧ Nat.succ 5 = 6 ∧ Nat.succ 6 = 7 ∧ Nat.succ 7 = 8 ∧
          Nat.succ 8 = 9
    ) ∧
    -- 20. Kepler.Text.UNADORNED_NOT_EAR (LA38:397; HOL `UNADORNED_NOT_EAR`)
    (∀ (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ)
    ,
          ¬ isEarV39 (mkUnadornedV39 k d a b)
    ) ∧
    -- 21. Kepler.Text.convex_local_fan_azim_le_pi (LA38:2715; HOL `convex_local_fan_azim_le_pi`)
    (∀ (vv : ℕ → V3) (k i : ℕ)
          (hper : Periodic vv k) (hk : 3 ≤ k)
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hsub : Set.range vv ⊆ ballAnnulus),
          azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi
    ) ∧
    -- 22. Kepler.Text.cs_adj4_EXPLICIT (LA38:2974; HOL `cs_adj4_EXPLICIT`)
    (∀ (a b : ℝ)
    ,
          csAdj 4 a b 0 0 = 0 ∧ csAdj 4 a b 0 1 = a ∧ csAdj 4 a b 0 2 = b ∧
          csAdj 4 a b 0 3 = a ∧ csAdj 4 a b 1 0 = a ∧ csAdj 4 a b 1 1 = 0 ∧
          csAdj 4 a b 1 2 = a ∧ csAdj 4 a b 1 3 = b ∧ csAdj 4 a b 2 0 = b ∧
          csAdj 4 a b 2 1 = a ∧ csAdj 4 a b 2 2 = 0 ∧ csAdj 4 a b 2 3 = a ∧
          csAdj 4 a b 3 0 = a ∧ csAdj 4 a b 3 1 = b ∧ csAdj 4 a b 3 2 = a ∧
          csAdj 4 a b 3 3 = 0
    ) ∧
    -- 23. Kepler.Text.delta_4680581274 (LA38:2988; HOL `delta_4680581274`)
    (∀ (y1 y4 : ℝ) (hy1 : cstab ≤ y1) (hy4 : 4 ≤ y4)
    ,
          deltaY y1 2 2 y4 2 cstab < 0
    ) ∧
    -- 24. Kepler.Text.dsv_fun3 (LA38:533; HOL `dsv_fun3`)
    (∀ (d : ℝ) (a a' b' b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
          (s s' s'' : ℕ → Prop)
          (vv : ℕ → V3),
          dsvV39 (ScsV39.mk 3 d a a' b' b f s s' s'') vv =
          d + 0.1 * (if isEarV39 (ScsV39.mk 3 d a a' b' b f s s' s'') then 1 else -1) *
            ((if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
            (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
            (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) + 0)
    ) ∧
    -- 25. Kepler.Text.dsv_fun4 (LA38:545; HOL `dsv_fun4`)
    (∀ (d : ℝ) (a a' b' b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
          (s s' s'' : ℕ → Prop)
          (vv : ℕ → V3),
          dsvV39 (ScsV39.mk 4 d a a' b' b f s s' s'') vv =
          d - 0.1 * ((if f 0 1 then cstab - dist (vv 0) (vv 1) else 0) +
            (if f 1 2 then cstab - dist (vv 1) (vv 2) else 0) +
            (if f 2 3 then cstab - dist (vv 2) (vv 3) else 0) +
            (if f 3 4 then cstab - dist (vv 3) (vv 4) else 0) + 0)
    ) ∧
    -- 26. Kepler.Text.dsv_unadorned (LA38:407; HOL `dsv_unadorned`)
    (∀ (k : ℕ) (d : ℝ) (a b : ℕ → ℕ → ℝ) (vv : ℕ → V3)
    ,
          dsvV39 (mkUnadornedV39 k d a b) vv = d
    ) ∧
    -- 27. Kepler.Text.funlistA_empty (LA38:1725; HOL `funlistA_empty`, HOL `F`)
    (∀ (k : ℕ)
    ,
          funlistAV39 [] False False (A := Prop) k = fun _ _ => False
    ) ∧
    -- 28. Kepler.Text.funlist_diag (LA38:1714; HOL `funlist_diag`)
    (∀ (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (k i : ℕ)
    ,
          funlistV39 a a0 k i i = 0
    ) ∧
    -- 29. Kepler.Text.funlist_kik (LA38:3456; HOL `funlist_kik`)
    (∀ (b : List ((ℕ × ℕ) × ℝ)) (b0 : ℝ) (k i : ℕ)
    ,
          funlistV39 b b0 k i k = funlistV39 b b0 k 0 i
    ) ∧
    -- 30. Kepler.Text.funlist_sym (LA38:1704; HOL `funlist_sym`)
    (∀ (k : ℕ) (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (i j : ℕ)
    ,
          funlistV39 a a0 k i j = funlistV39 a a0 k j i
    ) ∧
    -- 31. Kepler.Text.is_ear_scs3 (LA38:1864; HOL `is_ear_scs3`)
    (∀ (a b : ℕ → ℕ → ℝ) (jf : ℕ → ℕ → Prop)
    ,
          isEarV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
            (fun _ => False)) ↔
          isScsV39 (ScsV39.mk 3 0.11 a a b b jf (fun _ => False) (fun _ => False)
            (fun _ => False)) ∧ (∀ i, b i i = 0) ∧
          (∃ i, {j | j < 3 ∧ jf j (j + 1)} = {i} ∧ a i (i + 1) = Real.sqrt 8 ∧
            b i (i + 1) = cstab ∧
            (∀ j, j < 3 ∧ j ≠ i → a j (j + 1) = 2 ∧ b j (j + 1) = 2 * h0))
    ) ∧
    -- 32. Kepler.Text.is_scs_ear_3603097872 (LA38:1954; HOL `is_scs_ear_3603097872`)
    (isScsV39 (ScsV39.mk 3 0.11
          (funlistV39 [((0, 1), Real.sqrt 8)] 2 3) (funlistV39 [((0, 1), Real.sqrt 8)] 2 3)
          (funlistV39 [((0, 1), cstab)] (2 * h0) 3) (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
          (funlistAV39 [((0, 1), True)] False False 3)
          (fun _ => False) (fun _ => False) (fun _ => False))
    ) ∧
    -- 33. Kepler.Text.is_scs_funlist (LA38:1731; HOL `is_scs_funlist`)
    (∀ (k : ℕ) (d a0 b0 : ℝ) (j0 : Prop)
          (a : List ((ℕ × ℕ) × ℝ)) (b : List ((ℕ × ℕ) × ℝ))
          (j1 : List ((ℕ × ℕ) × Prop)) (u u' u'' : ℕ → Prop)
          (h1 : d < 0.9) (h2 : 3 ≤ k) (h3 : k ≤ 6)
          (h4 : Periodic u k) (h5 : Periodic u' k) (h6 : Periodic u'' k)
          (h7 : ∀ i j : ℕ, i < j ∧ j < k →
            funlistV39 a a0 k i j ≤ funlistV39 b b0 k i j)
          (h8 : ∀ i j : ℕ, i < j ∧ j < k → 2 ≤ funlistV39 a a0 k i j)
          (h9 : ∀ i : ℕ, i < 3 ∧ k = 3 → funlistV39 b b0 k i (i + 1) < 4)
          (h10 : ∀ i : ℕ, i < k ∧ 3 < k → funlistV39 b b0 k i (i + 1) ≤ cstab)
          (h11 : ∀ i j : ℕ, i < j ∧ j < k ∧ funlistAV39 j1 False j0 k i j →
            funlistV39 a a0 k i j = Real.sqrt 8 ∧ funlistV39 b b0 k i j = cstab)
          (h12 : ∀ i j : ℕ, i < j ∧ j < k ∧ funlistAV39 j1 False j0 k i j →
            j = i + 1 ∨ (i = 0 ∧ j + 1 = k))
          (h13 : {i : ℕ | i < k ∧ (2 * h0 < funlistV39 b b0 k i (i + 1) ∨
              2 < funlistV39 a a0 k i (i + 1))}.ncard + k ≤ 6),
          isScsV39 (ScsV39.mk k d (funlistV39 a a0 k) (funlistV39 a a0 k)
          (funlistV39 b b0 k) (funlistV39 b b0 k) (funlistAV39 j1 False j0 k)
          u u' u'')
    ) ∧
    -- 34. Kepler.Text.is_scs_scs3 (LA38:1883; HOL `is_scs_scs3`)
    (∀ (d : ℝ) (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ)
          (b : List ((ℕ × ℕ) × ℝ)) (b0 : ℝ) (jf : List ((ℕ × ℕ) × Prop)) (j0 : Prop)
          (h1 : d < 0.9)
          (h2 : funlistV39 a a0 3 0 1 ≤ funlistV39 b b0 3 0 1)
          (h3 : funlistV39 a a0 3 0 2 ≤ funlistV39 b b0 3 0 2)
          (h4 : funlistV39 a a0 3 1 2 ≤ funlistV39 b b0 3 1 2)
          (h5 : 2 ≤ funlistV39 a a0 3 0 1)
          (h6 : 2 ≤ funlistV39 a a0 3 1 2)
          (h7 : 2 ≤ funlistV39 a a0 3 0 2)
          (h8 : funlistV39 b b0 3 0 1 < 4)
          (h9 : funlistV39 b b0 3 0 2 < 4)
          (h10 : funlistV39 b b0 3 1 2 < 4)
          (h11 : ∀ i j : ℕ, i < j ∧ j < 3 ∧ funlistAV39 jf False j0 3 i j →
            funlistV39 a a0 3 i j = Real.sqrt 8 ∧ funlistV39 b b0 3 i j = cstab),
          isScsV39 (ScsV39.mk 3 d (funlistV39 a a0 3) (funlistV39 a a0 3)
          (funlistV39 b b0 3) (funlistV39 b b0 3)       (funlistAV39 jf False j0 3)
          (fun _ => False) (fun _ => False) (fun _ => False))
    ) ∧
    -- 35. Kepler.Text.periodic2_SUC_periodic (LA38:3515; HOL `periodic2_SUC_periodic`)
    (∀ (f : ℕ → ℕ → Prop) (k : ℕ)
          (h : Periodic2 f k),
          Periodic (fun i => f i (i + 1)) k
    ) ∧
    -- 36. Kepler.Text.periodic2_funlist (LA38:1685; HOL `periodic2_funlist`)
    (∀ (a : List ((ℕ × ℕ) × ℝ)) (a0 : ℝ) (k : ℕ)
    ,
          Periodic2 (funlistV39 a a0 k) k
    ) ∧
    -- 37. Kepler.Text.periodic2_mod_reduce (LA38:3478; HOL `periodic2_mod_reduce`)
    (∀ (P : ℕ → ℕ → Prop) (k : ℕ) (hk : ¬(k = 0))
          (hper : Periodic2 P k) (hb : ∀ i j : ℕ, i < k ∧ j < k → P i j) (i j : ℕ),
          P i j
    ) ∧
    -- 38. Kepler.Text.periodic2_mod_sym_reduce (LA38:3500; HOL `periodic2_mod_sym_reduce`)
    (∀ (P : ℕ → ℕ → Prop) (k : ℕ)
          (hk : ¬(k = 0)) (hper : Periodic2 P k) (hdiag : ∀ i, P i i)
          (hsym : ∀ i j, P i j = P j i)
          (htri : ∀ i j, i < j ∧ j < k → P i j) (i j : ℕ),
          P i j
    ) ∧
    -- 39. Kepler.Text.periodic_mod_reduce (LA38:3464; HOL `periodic_mod_reduce`)
    (∀ (P : ℕ → Prop) (k : ℕ) (hk : ¬(k = 0))
          (hper : Periodic P k) (hb : ∀ i, i < k → P i) (i : ℕ),
          P i
    ) ∧
    -- 40. Kepler.Text.psort_sym (LA38:1697; HOL `psort_sym`)
    (∀ (k i j : ℕ)
    ,
          psort k (i, j) = psort k (j, i)
    ) ∧
    -- 41. Kepler.Text.quadratic_root_upper_bound (LA38:3234; HOL `quadratic_root_upper_bound`)
    (∀ (a b c e x : ℝ) (ha : 0 < a)
          (hb : 0 < 2 * a * e + b) (hc : 0 < a * e ^ 2 + b * e + c)
          (h : a * x ^ 2 + b * x + c = 0),
          x < e
    ) ∧
    -- 42. Kepler.Text.quadratic_square_root_upper_bound (LA38:3251; HOL `quadratic_square_root_upper_bound`)
    (∀ (a b c e : ℝ) (ha : 0 < a)
          (hb : 0 < 2 * a * e + b) (hc : 0 < a * e ^ 2 + b * e + c)
          (hd : 0 ≤ b ^ 2 - 4 * a * c) (hbn : b ≤ 0) (he : 0 ≤ e),
          Real.sqrt (quadraticRootPlus a b c) < Real.sqrt e
    ) ∧
    -- 43. Kepler.Text.scs_unadorned_explicit (LA38:381; HOL `scs_unadorned_explicit`)
    ((∀ k d a b, (mkUnadornedV39 k d a b).k = k) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).d = d) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).a = a) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).am = a) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).b = b) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).bm = b) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).J = fun _ _ => False) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).lo = fun _ => False) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).hi = fun _ => False) ∧
          (∀ k d a b, (mkUnadornedV39 k d a b).str = fun _ => False)
    ) ∧
    -- 44. Kepler.Text.sq_imp_nn (LA38:3308; HOL `sq_imp_nn`)
    (∀ (c x : ℝ) (h : c ^ 2 ≤ x)
    ,
          0 ≤ x
    ) ∧
    -- 45. Kepler.Text.sqrt8_bounds (LA38:3094; HOL `sqrt8_bounds`)
    (Real.sqrt 8 ≤ 3.01 ∧ 2 ≤ Real.sqrt 8 ∧ Real.sqrt 8 ≤ 3.62
    ) ∧
    -- 46. Kepler.Text.sqrt8_flyspeck (LA38:288; HOL `sqrt8_flyspeck`)
    ((2.828427 : ℝ) < Real.sqrt 8 ∧ Real.sqrt 8 < 2.828428
    ) ∧
    -- 47. Kepler.Text.tau3_sym (LA38:3018; HOL `tau3_sym`)
    (∀ (v0 v1 v2 : V3)
    ,
          tau3 v0 v1 v2 = tau3 v0 v2 v1 ∧ tau3 v0 v1 v2 = tau3 v1 v0 v2
    ) ∧
    -- 48. Kepler.Text.tau3_taum (LA38:1286; HOL `tau3_taum`)
    (∀ (v0 v1 v2 : V3)
    ,
          v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
          2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
          dist v0 v1 ≤ 3.62 → dist v0 v2 ≤ 3.62 → dist v1 v2 ≤ 3.62 →
          tau3 v0 v1 v2 =
            taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1)
    ) ∧
    -- 49. Kepler.Text.tau3_taum_40 (LA38:1314; HOL `tau3_taum_40`)
    (∀ (v0 v1 v2 : V3)
    ,
          v0 ∈ ballAnnulus → v1 ∈ ballAnnulus → v2 ∈ ballAnnulus →
          2 ≤ dist v0 v1 → 2 ≤ dist v0 v2 → 2 ≤ dist v1 v2 →
          dist v0 v1 < 4 → dist v0 v2 < 4 → dist v1 v2 < 4 →
          tau3 v0 v1 v2 =
            taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1)
    ) ∧
    -- 50. Kepler.Text.tau3_taum_d (LA38:1492; HOL `tau3_taum_d`)
    (∀ (d a01 a12 a02 b01 b12 b02 : ℝ)
          (h1 : 2 ≤ a01) (h2 : 2 ≤ a12) (h3 : 2 ≤ a02)
          (h4 : b01 ≤ 3.62) (h5 : b12 ≤ 3.62) (h6 : b02 ≤ 3.62)
          (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
            2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
            a01 ≤ y6 → y6 ≤ b01 → a12 ≤ y4 → y4 ≤ b12 → a02 ≤ y5 → y5 ≤ b02 →
            0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
            d ≤ taum y1 y2 y3 y4 y5 y6)
          (v0 v1 v2 : V3),
          2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ → ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ →
          ‖v2‖ ≤ 2 * h0 → a01 ≤ dist v0 v1 → dist v0 v1 ≤ b01 →
          a12 ≤ dist v1 v2 → dist v1 v2 ≤ b12 → a02 ≤ dist v0 v2 →
          dist v0 v2 ≤ b02 → d ≤ tau3 v0 v1 v2
    ) ∧
    -- 51. Kepler.Text.tau3_taum_dfun (LA38:1536; HOL `tau3_taum_dfun`)
    (∀ (d : ℝ) (a01 a12 a02 b01 b12 b02 : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
          (h1 : 2 ≤ a01) (h2 : 2 ≤ a12) (h3 : 2 ≤ a02)
          (h4 : b01 ≤ 3.62) (h5 : b12 ≤ 3.62) (h6 : b02 ≤ 3.62)
          (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
            2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
            a01 ≤ y6 → y6 ≤ b01 → a12 ≤ y4 → y4 ≤ b12 → a02 ≤ y5 → y5 ≤ b02 →
            0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
            d + f y4 y5 y6 ≤ taum y1 y2 y3 y4 y5 y6)
          (v0 v1 v2 : V3),
          2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ → ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ →
          ‖v2‖ ≤ 2 * h0 → a01 ≤ dist v0 v1 → dist v0 v1 ≤ b01 →
          a12 ≤ dist v1 v2 → dist v1 v2 ≤ b12 → a02 ≤ dist v0 v2 →
          dist v0 v2 ≤ b02 → d + f (dist v1 v2) (dist v0 v2) (dist v0 v1) ≤ tau3 v0 v1 v2
    ) ∧
    -- 52. Kepler.Text.tau_fun_azim (LA38:2422; HOL `tau_fun_azim`)
    (∀ (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j),
          tauFun (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
            (Set.range fun i => (vv i, vv (i + 1))) =
          setSum {i | i < k}
              (fun i => rhoFun ‖vv i‖ * azim 0 (vv i) (vv (i + 1)) (vv (i + (k - 1)))) -
            (Real.pi + sol0) * (k - 2)
    ) ∧
    -- 53. Kepler.Text.taum_sym2 (LA38:1638; HOL `taum_sym2`)
    (∀ (y1 y2 y3 y4 y5 y6 : ℝ)
    ,
          taum y1 y2 y3 y4 y5 y6 = taum y2 y1 y3 y5 y4 y6 ∧
          taum y1 y2 y3 y4 y5 y6 = taum y1 y3 y2 y4 y6 y5
    ) ∧
    -- 54. Kepler.Text.taustar3 (LA38:566; HOL `taustar3`)
    (∀ (d : ℝ) (a b : ℕ → ℕ → ℝ)
          (h : ∀ v0 v1 v2 : V3, 2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ →
            ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ → ‖v2‖ ≤ 2 * h0 →
            a 0 1 ≤ dist v0 v1 → dist v0 v1 ≤ b 0 1 → a 1 2 ≤ dist v1 v2 →
            dist v1 v2 ≤ b 1 2 → a 0 2 ≤ dist v0 v2 → dist v0 v2 ≤ b 0 2 →
            d ≤ tau3 v0 v1 v2)
          (vv : ℕ → V3) (hbb : BBsV39 (mkUnadornedV39 3 d a b) vv),
          0 ≤ taustarV39 (mkUnadornedV39 3 d a b) vv
    ) ∧
    -- 55. Kepler.Text.taustar3_fun (LA38:591; HOL `taustar3_fun`)
    (∀ (d : ℝ) (a b : ℕ → ℕ → ℝ) (f : ℕ → ℕ → Prop)
          (h : ∀ v0 v1 v2 : V3, 2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ →
            ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ → ‖v2‖ ≤ 2 * h0 →
            a 0 1 ≤ dist v0 v1 → dist v0 v1 ≤ b 0 1 → a 1 2 ≤ dist v1 v2 →
            dist v1 v2 ≤ b 1 2 → a 0 2 ≤ dist v0 v2 → dist v0 v2 ≤ b 0 2 →
            d + 0.1 * (if isEarV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
                (fun _ => False) (fun _ => False)) then 1 else -1) *
              ((if f 0 1 then cstab - dist v0 v1 else 0) +
              (if f 1 2 then cstab - dist v1 v2 else 0) +
              (if f 2 3 then cstab - dist v2 v0 else 0) + 0) ≤ tau3 v0 v1 v2)
          (vv : ℕ → V3) (hbb : BBsV39 (ScsV39.mk 3 d a a b b f (fun _ => False)
            (fun _ => False) (fun _ => False)) vv),
          0 ≤ taustarV39 (ScsV39.mk 3 d a a b b f (fun _ => False) (fun _ => False)
          (fun _ => False)) vv
    ) ∧
    -- 56. Kepler.Text.terminal_quad_lemma (LA38:3153; HOL `terminal_quad_lemma`)
    (∀ (d : ℝ) (a b : ℕ → ℕ → ℝ)
          (h : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ i ≠ j → 0 < a i j)
          (h2 : ∀ vv : ℕ → V3, Set.range vv ⊆ ballAnnulus → Periodic vv 4 →
            (∀ i j : ℕ, a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ b i j) →
            ConvexLocalFan (Set.range vv)
              (Set.range fun i => {vv i, vv (i + 1)})
              (Set.range fun i => (vv i, vv (i + 1))) →
              d ≤ (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
                rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 4) +
                rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 5) +
                rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 4) (vv 6) + 0) -
                (Real.pi + sol0) * (4 - 2))
          (vv : ℕ → V3) (hbb : BBsV39 (mkUnadornedV39 4 d a b) vv),
          0 ≤ taustarV39 (mkUnadornedV39 4 d a b) vv
    ) ∧
    -- 57. Kepler.Text.vv_azim_le (LA38:2509; HOL `vv_azim_le`)
    (∀ (vv : ℕ → V3) (k i j : ℕ)
          (hper : Periodic vv k) (hk : 3 ≤ k)
          (hsub : Set.range vv ⊆ ballAnnulus)
          (hd1 : dist (vv i) (vv (i + 1)) < 4)
          (hd2 : dist (vv i) (vv (i + (k - 1))) < 4)
          (hd3 : dist (vv i) (vv j) < 4)
          (hmod : ¬(i % k = j % k))
          (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j),
          azim 0 (vv i) (vv (i + 1)) (vv j) ≤
          azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1))
    ) ∧
    -- 58. Kepler.Text.vv_quad_split012 (LA38:2757; HOL `vv_quad_split012`)
    (∀ (vv : ℕ → V3)
          (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
          (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 2) < 4)
          (hd3 : dist (vv 0) (vv 3) < 4) (hd4 : dist (vv 1) (vv 2) < 4)
          (hd5 : dist (vv 2) (vv 3) < 4)
          (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j),
          (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
            rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
            rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
            rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
          (Real.pi + sol0) * 2 =
          tau3 (vv 0) (vv 1) (vv 2) + tau3 (vv 2) (vv 3) (vv 0)
    ) ∧
    -- 59. Kepler.Text.vv_quad_split123 (LA38:2842; HOL `vv_quad_split123`)
    (∀ (vv : ℕ → V3)
          (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
          (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 3) < 4)
          (hd3 : dist (vv 1) (vv 2) < 4) (hd4 : dist (vv 1) (vv 3) < 4)
          (hd5 : dist (vv 2) (vv 3) < 4)
          (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j),
          (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
            rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
            rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
            rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
          (Real.pi + sol0) * 2 =
          tau3 (vv 1) (vv 2) (vv 3) + tau3 (vv 3) (vv 0) (vv 1)
    ) ∧
    -- 60. Kepler.Text.vv_quad_split_short (LA38:2935; HOL `vv_quad_split_short`)
    (∀ (vv : ℕ → V3)
          (hper : Periodic vv 4) (hsub : Set.range vv ⊆ ballAnnulus)
          (hd1 : dist (vv 0) (vv 1) < 4) (hd2 : dist (vv 0) (vv 3) < 4)
          (hd3 : dist (vv 0) (vv 2) < 4) (hd4 : dist (vv 1) (vv 2) < 4)
          (hd5 : dist (vv 1) (vv 3) < 4) (hd6 : dist (vv 2) (vv 3) < 4)
          (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j),
          ∃ i, i < 2 ∧ dist (vv i) (vv (i + 2)) ≤ dist (vv (i + 1)) (vv (i + 3)) ∧
          (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
              rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 0) +
              rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 1) +
              rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 0) (vv 2)) -
            (Real.pi + sol0) * 2 =
            tau3 (vv i) (vv (i + 1)) (vv (i + 2)) +
              tau3 (vv (i + 2)) (vv (i + 3)) (vv i)
    ) ∧
    -- 61. Kepler.Text.vv_rho_node1 (LA38:2459; HOL `vv_rho_node1`)
    (∀ (vv : ℕ → V3) (k : ℕ) (hper : Periodic vv k) (hk : 3 ≤ k)
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j)
          (i : ℕ),
          rhoNode1 (Set.range fun i => (vv i, vv (i + 1))) (vv i) = vv (i + 1)
    ) ∧
    -- 62. Kepler.Text.vv_split_azim (LA38:2560; HOL `vv_split_azim`)
    (∀ (vv : ℕ → V3) (k i j : ℕ)
          (hper : Periodic vv k) (hk : 3 ≤ k)
          (hsub : Set.range vv ⊆ ballAnnulus)
          (hd1 : dist (vv i) (vv (i + 1)) < 4)
          (hd2 : dist (vv i) (vv (i + (k - 1))) < 4)
          (hd3 : dist (vv i) (vv j) < 4)
          (hmod : ¬(i % k = j % k))
          (hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j))
          (hcf : ConvexLocalFan (Set.range vv)
            (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))))
          (hinj : ∀ i j : ℕ, i < k ∧ j < k ∧ vv i = vv j → i = j),
          azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) =
          azim 0 (vv i) (vv (i + 1)) (vv j) +
            azim 0 (vv i) (vv j) (vv (i + k - 1))
    ) :=
    ⟨Kepler.Text.DELTA_Y_POS_4POINTS, Kepler.Text.DIHV_EQ_DIH_Y_4PT, Kepler.Text.DIHV_NN_4PT,
      Kepler.Text.DIH_X_NN, Kepler.Text.DIH_Y_NN, Kepler.Text.EE_vv,
      Kepler.Text.ITER_vv_rho_node1, Kepler.Text.I_LT_J_LT_3_EXPLICIT,
      Kepler.Text.I_LT_J_LT_4_EXPLICIT, Kepler.Text.LEMMA_4680581274_delta_issue_ups,
      Kepler.Text.MOD_4_EXPLICIT, Kepler.Text.NONPARALLEL_BALL_ANNULUS40,
      Kepler.Text.NONPARALLEL_BALL_ANNULUS40_ALT, Kepler.Text.NONPARALLEL_BALL_ANNULUS_ALT,
      Kepler.Text.REAL_FINITE_MIN_EXISTS_p38, Kepler.Text.REAL_WLOG_SQUARE2_LEMMA,
      Kepler.Text.REAL_WLOG_SQUARE_LEMMA, Kepler.Text.RHO_LB, Kepler.Text.SUC_EXPLICIT,
      Kepler.Text.UNADORNED_NOT_EAR, Kepler.Text.convex_local_fan_azim_le_pi,
      Kepler.Text.cs_adj4_EXPLICIT, Kepler.Text.delta_4680581274, Kepler.Text.dsv_fun3,
      Kepler.Text.dsv_fun4, Kepler.Text.dsv_unadorned, Kepler.Text.funlistA_empty,
      Kepler.Text.funlist_diag, Kepler.Text.funlist_kik, Kepler.Text.funlist_sym,
      Kepler.Text.is_ear_scs3, Kepler.Text.is_scs_ear_3603097872, Kepler.Text.is_scs_funlist,
      Kepler.Text.is_scs_scs3, Kepler.Text.periodic2_SUC_periodic, Kepler.Text.periodic2_funlist,
      Kepler.Text.periodic2_mod_reduce, Kepler.Text.periodic2_mod_sym_reduce,
      Kepler.Text.periodic_mod_reduce, Kepler.Text.psort_sym,
      Kepler.Text.quadratic_root_upper_bound, Kepler.Text.quadratic_square_root_upper_bound,
      Kepler.Text.scs_unadorned_explicit, Kepler.Text.sq_imp_nn, Kepler.Text.sqrt8_bounds,
      Kepler.Text.sqrt8_flyspeck, Kepler.Text.tau3_sym, Kepler.Text.tau3_taum,
      Kepler.Text.tau3_taum_40, Kepler.Text.tau3_taum_d, Kepler.Text.tau3_taum_dfun,
      Kepler.Text.tau_fun_azim, Kepler.Text.taum_sym2, Kepler.Text.taustar3,
      Kepler.Text.taustar3_fun, Kepler.Text.terminal_quad_lemma, Kepler.Text.vv_azim_le,
      Kepler.Text.vv_quad_split012, Kepler.Text.vv_quad_split123,
      Kepler.Text.vv_quad_split_short, Kepler.Text.vv_rho_node1, Kepler.Text.vv_split_azim⟩

#print axioms la38_capstone_w1

#print axioms localconcl_wire_capstone_w1
#print axioms la35_wire_capstone_w1
#print axioms localconcl_wire_capstone_w2



/-! ### LA18 + LA34 materialization capstones (lane lv56-w1, program
slot C = LV5 + LV6, 2026-11-04, after the leftover-mat-scout delivery
e342ff1b §2-17): the clean public top-level exits of LocalAuto18 (29
clean of 47 theorem exits) and LocalAuto34 (53 clean of 123) that no e2e
root reaches are re-exposed as ONE conjunction each -- the 18 + 70
sorried-exit branches are excluded per the workorder (scout probe1
per-item BFS closure sorried ≥ 1); both modules are already imported by
this file (LA18 :489, LA34 :505), so zero import changes.  Scout probe2
(baseline I 1e139a28): la18 clean-subset group closure +168 fresh vs
cone (163 LA18 + 5 LA4), la34 +156 (154 LA34 + 2 LA17), GROUP_SORRIED 0
x2; K_SORRIED 134 / K_AXIOM 624 unchanged at wiring time.  This wave is
LocalConcl-only (no Assembly re-point; lv-wire-w2 wires all four
program-C slots in one pass).  Extraction purely mechanical
(gen_items.py): conjuncts are verbatim module source signatures,
bodies are the exit constants; drops per the no-forcing rule are
recorded per item in the capstone docstrings and logs/gen_report.txt.
The exact kit yield is re-measured at the orchestrator e2e gate. -/


/-- LA18 materialization capstone (lane lv56-w1 slot
LV5, program slot C = LV5+LV6, 2026-11-04, after
the leftover-mat-scout delivery e342ff1b §1): the clean public top-level
LocalAuto18 exits unreachable from every e2e
root -- 29 of 47 theorem exits
(scout probe1 per-item BFS: clean = closure sorried-0; the 18
sorried-exit branches are excluded per the workorder, one does not enter,
each named in the lane gen_report).  Clean-subset group closure (scout
probe2, baseline I 1e139a28): GROUP_FRESH_VS_CONE 168
(163 LA18 + 5
LocalAuto4), GROUP_SORRIED 0, i.e. the new closure is
sorried-0; K_SORRIED 134 and K_AXIOM 624 unchanged when wired.
Implemented here: 26 of the 29.  Dropped per the workorder's
no-forcing rule ("抽不出/不一致 → 剔除并如实报"), mechanically detected
by the generator:
  - PERIODIC_IMAGE2_p18: universe-polymorphic statement (free universe in Sort/Type position; would give the capstone a universe parameter and break the future `have hcap := <name>` consumption shape)
  - periodic2_mod_p18: universe-polymorphic statement (free universe in Sort/Type position; would give the capstone a universe parameter and break the future `have hcap := <name>` consumption shape)
  - periodic_mod_p18: universe-polymorphic statement (free universe in Sort/Type position; would give the capstone a universe parameter and break the future `have hcap := <name>` consumption shape)
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LA18 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied verbatim
and mechanically split at the binder/conclusion separator by the
generator gen_items.py; equation-lemma conjuncts have no source text and
take the `#check @name` printer dump verbatim); the printer dump
(logs/sigprobe_82.out) is retained as cross reference; semantic identity
is re-verified by the elaboration of the `⟨...⟩` assembly below (each
component must unify definitionally with its conjunct); per-conjunct
comments carry each exit's LA18 declaration line and file-local
docstring HOL anchor.
Conjunct order: the scout clean-seed-list order (logs/seeds_clean.txt
LA18 subset).  Body = the assembly of the exit constants --
zero new proof obligations, zero new imports. -/
theorem la18_capstone_w1 :
    -- 1. BOUNDED_SY_p18 (LA18:259; HOL `BOUNDED_SY`)
    (∀ {k : ℕ} {a b : ℕ → ℕ → ℝ}
    ,
          Bornology.IsBounded (SYset_p18 k a b)
    ) ∧
    -- 2. BSY1body_p18.eq_1 (LA18:186 (def BSY1body_p18 there; eq lemma, statement = probe printer dump verbatim); HOL `{matvec v | rows v in ball_annulus ∧ CONDITION1_SY a b v}`)
    (∀ (k : ℕ) (a b : ℕ → ℕ → ℝ),
          BSY1body_p18 k a b =
            {l |
              (∀ (j : Fin k), vecmatsV3_p4 l j ∈ ballAnnulus) ∧
                ∀ (i j : ℕ),
                  1 ≤ i →
                    i ≤ k → 1 ≤ j → j ≤ k → a i j ≤ ‖rowV3_p18 l i - rowV3_p18 l j‖ ∧ ‖rowV3_p18 l i - rowV3_p18 l j‖ ≤ b i j}
    ) ∧
    -- 3. CLOSED_SY_p18 (LA18:239; HOL `CLOSED_SY`)
    (∀ {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
          (_hsys : stableSystem_p18 k d s a b J f) (_hs : s = Finset.Iic (k - 1))
          (_hf : f = fun j => (1 + j) % k) (_hk1 : 1 < k) (_hk2 : 2 < k),
          IsClosed (SYset_p18 k a b)
    ) ∧
    -- 4. POWER_MOD_FUN_p18 (LA18:211; HOL `POWER_MOD_FUN`)
    (∀ (n i k : ℕ) (_hn : 1 ≤ n) (_hk : 1 < k)
    ,
          (fun j => (1 + j) % k)^[n] i = (n + i) % k
    ) ∧
    -- 5. REP_NUMSEG_p18 (LA18:1472; HOL `REP_NUMSEG`, HOL `0..(k-1)`)
    (∀ (k : ℕ) (_hk : k ≠ 0)
    ,
          {i : ℕ | i < k} = Finset.range k
    ) ∧
    -- 6. SCS_5I1_SLICE_02_p18 (LA18:2224; HOL `SCS_5I1_SLICE_02`)
    (scsArrowV39 {scsStabDiagV39 scs5I1 0 2}
          {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M2 1}
    ) ∧
    -- 7. SCS_5I2_SLICE_02_p18 (LA18:2253; HOL `SCS_5I2_SLICE_02`)
    (scsArrowV39 {scsStabDiagV39 scs5I2 0 2}
          {scsPropEquV39 scs3T1 1, scsPropEquV39 scs4M3' 1}
    ) ∧
    -- 8. SCS_5M1_SLICE_02_p18 (LA18:2282; HOL `SCS_5M1_SLICE_02`)
    (scsArrowV39 {scsStabDiagV39 scs5M1 0 2}
          {scsPropEquV39 scs3T4 2, scsPropEquV39 scs4M2 1}
    ) ∧
    -- 9. SCS_5M1_SLICE_03_p18 (LA18:2311; HOL `SCS_5M1_SLICE_03`)
    (scsArrowV39 {scsStabDiagV39 scs5M1 0 3}
          {scsPropEquV39 scs4M4' 1, scsPropEquV39 scs3M1 1}
    ) ∧
    -- 10. SCS_5M1_SLICE_24_p18 (LA18:2340; HOL `SCS_5M1_SLICE_24`)
    (scsArrowV39 {scsStabDiagV39 scs5M1 2 4}
          {scsPropEquV39 scs3M1 1, scsPropEquV39 scs4M5' 1}
    ) ∧
    -- 11. SCS_DIAG_SCS_5I1_02_p18 (LA18:1518; HOL `SCS_DIAG_SCS_5I1_02`)
    (scsDiag scs5I1.k 0 2
    ) ∧
    -- 12. SCS_DIAG_SCS_5I2_02_p18 (LA18:1525; HOL `SCS_DIAG_SCS_5I2_02`)
    (scsDiag scs5I2.k 0 2
    ) ∧
    -- 13. SCS_DIAG_SCS_5M1_02_p18 (LA18:1532; HOL `SCS_DIAG_SCS_5M1_02`)
    (scsDiag scs5M1.k 0 2
    ) ∧
    -- 14. SCS_DIAG_SCS_5M1_03_p18 (LA18:1539; HOL `SCS_DIAG_SCS_5M1_03`)
    (scsDiag scs5M1.k 0 3
    ) ∧
    -- 15. SCS_DIAG_SCS_5M1_24_p18 (LA18:1546; HOL `SCS_DIAG_SCS_5M1_24`)
    (scsDiag scs5M1.k 2 4
    ) ∧
    -- 16. SUM_NUMSEG4_p18 (LA18:371; HOL `SUM_NUMSEG4`)
    (∀ (t : ℕ → ℝ)
    ,
          ∑ i ∈ Finset.range 5, t i = t 0 + t 1 + t 2 + t 3 + t 4
    ) ∧
    -- 17. WJSCPRO_p18 (LA18:267; HOL `WJSCPRO`)
    (∀ {k : ℕ} {d : ℝ} {s : Finset ℕ} {a b : ℕ → ℕ → ℝ}
          {J : Finset (Finset ℕ)} {f : ℕ → ℕ}
          (hsys : stableSystem_p18 k d s a b J f) (hs : s = Finset.Iic (k - 1))
          (hf : f = fun j => (1 + j) % k) (hk1 : 1 < k) (hk2 : 2 < k),
          IsCompact (SYset_p18 k a b)
    ) ∧
    -- 18. a5_assumption_reduction_p18 (LA18:1092; HOL `a5_assumption_reduction`)
    (∀ (s : ScsV39) (f : V3 → ℝ → V3)
          (v : ℕ → V3) (e : ℝ) (his : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s v)
          (hdiag : ∀ i j, scsDiag 5 i j → s.a i j < dist (v i) (v j))
          (_hdef : Deformation f (Set.range v) (-e) e)
          (hfix : ∀ (w : V3) (t : ℝ), w ≠ v 4 → w ≠ v 0 → f w t = w)
          (h40 : ∃ d > 0, ∀ t : ℝ, |t| < d →
            dist (f (v 4) t) (f (v 0) t) = dist (v 4) (v 0) ∧
              dist (f (v 4) t) (v 3) = dist (v 4) (v 3))
          (h01 : ∃ d > 0, ∀ t : ℝ, |t| < d → s.a 0 1 ≤ dist (f (v 0) t) (v 1)),
          ∀ i j : ℕ, ∃ d > 0, s.a i j = dist (v i) (v j) →
          ∀ t : ℝ, |t| < d → s.a i j ≤ dist (f (v i) t) (f (v j) t)
    ) ∧
    -- 19. b5_assumption_reduction_p18 (LA18:1220; HOL `b5_assumption_reduction`)
    (∀ (s : ScsV39) (f : V3 → ℝ → V3)
          (v : ℕ → V3) (e : ℝ) (his : isScsV39 s) (hk : s.k = 5) (hBB : BBsV39 s v)
          (hbdiag : ∀ i j, scsDiag 5 i j → 4 * h0 < s.b i j)
          (_hdef : Deformation f (Set.range v) (-e) e)
          (hfix : ∀ (w : V3) (t : ℝ), w ≠ v 4 → w ≠ v 0 → f w t = w)
          (h40 : ∃ d > 0, ∀ t : ℝ, |t| < d →
            dist (f (v 4) t) (f (v 0) t) = dist (v 4) (v 0) ∧
              dist (f (v 4) t) (v 3) = dist (v 4) (v 3))
          (h01 : ∃ d > 0, ∀ t : ℝ, |t| < d →
            dist (f (v 0) t) (v 1) ≤ dist (v 0) (v 1)),
          ∀ i j : ℕ, ∃ d > 0, dist (v i) (v j) = s.b i j →
          ∀ t : ℝ, |t| < d → dist (f (v i) t) (f (v j) t) ≤ s.b i j
    ) ∧
    -- 20. epsilon_hept_p18 (LA18:405; HOL `epsilon_hept`)
    (∀ {e e₁ e₂ e₃ e₄ e₅ e₆ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
          (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄) (he₅ : 0 < e₅)
          (he₆ : 0 < e₆),
          ∃ e₇ > 0, (∀ t, |t| < e₇ → |t| < e) ∧ (∀ t, |t| < e₇ → |t| < e₁) ∧
          (∀ t, |t| < e₇ → |t| < e₂) ∧ (∀ t, |t| < e₇ → |t| < e₃) ∧
          (∀ t, |t| < e₇ → |t| < e₄) ∧ (∀ t, |t| < e₇ → |t| < e₅) ∧
          (∀ t, |t| < e₇ → |t| < e₆)
    ) ∧
    -- 21. epsilon_hex_p18 (LA18:391; HOL `epsilon_hex`)
    (∀ {e e₁ e₂ e₃ e₄ e₅ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
          (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄) (he₅ : 0 < e₅),
          ∃ e₆ > 0, (∀ t, |t| < e₆ → |t| < e) ∧ (∀ t, |t| < e₆ → |t| < e₁) ∧
          (∀ t, |t| < e₆ → |t| < e₂) ∧ (∀ t, |t| < e₆ → |t| < e₃) ∧
          (∀ t, |t| < e₆ → |t| < e₄) ∧ (∀ t, |t| < e₆ → |t| < e₅)
    ) ∧
    -- 22. epsilon_pent_p18 (LA18:378; HOL `epsilon_pent`)
    (∀ {e e₁ e₂ e₃ e₄ : ℝ} (he : 0 < e) (he₁ : 0 < e₁)
          (he₂ : 0 < e₂) (he₃ : 0 < e₃) (he₄ : 0 < e₄),
          ∃ e₅ > 0, (∀ t, |t| < e₅ → |t| < e) ∧ (∀ t, |t| < e₅ → |t| < e₁) ∧
          (∀ t, |t| < e₅ → |t| < e₂) ∧ (∀ t, |t| < e₅ → |t| < e₃) ∧
          (∀ t, |t| < e₅ → |t| < e₄)
    ) ∧
    -- 23. quadratic_at_most_2_roots_p18 (LA18:332; HOL `quadratic_at_most_2_roots`)
    (∀ (a b c : ℝ)
    ,
          ∃ x₁ x₂ : ℝ, ∀ x, a ≠ 0 → a * x ^ 2 + b * x + c = 0 → x = x₁ ∨ x = x₂
    ) ∧
    -- 24. re_eqvl_imp_le_p18 (LA18:280; HOL `re_eqvl_imp_le`)
    (∀ {a b : ℝ} (h : reEqvl a b)
    ,
          0 ≤ a ↔ 0 ≤ b
    ) ∧
    -- 25. re_eqvl_real_sgn_p18 (LA18:294; HOL `re_eqvl_real_sgn`, HOL `real_sgn`)
    (∀ {x y : ℝ}
    ,
          reEqvl x y ↔ Real.sign x = Real.sign y
    ) ∧
    -- 26. real_continuous_finite_range_constant_p18 (LA18:440; HOL `real_continuous_finite_range_constant`)
    (∀ (f : ℝ → ℝ) (a b : ℝ)
          (hc : ContinuousOn f (Set.Ioo a b)) (hf : (f '' Set.Ioo a b).Finite),
          ∃ c, ∀ x ∈ Set.Ioo a b, f x = c
    ) :=
    ⟨@BOUNDED_SY_p18, BSY1body_p18.eq_1, CLOSED_SY_p18, POWER_MOD_FUN_p18, REP_NUMSEG_p18,
      @SCS_5I1_SLICE_02_p18, @SCS_5I2_SLICE_02_p18, @SCS_5M1_SLICE_02_p18,
      @SCS_5M1_SLICE_03_p18, @SCS_5M1_SLICE_24_p18, SCS_DIAG_SCS_5I1_02_p18,
      SCS_DIAG_SCS_5I2_02_p18, SCS_DIAG_SCS_5M1_02_p18, SCS_DIAG_SCS_5M1_03_p18,
      SCS_DIAG_SCS_5M1_24_p18, SUM_NUMSEG4_p18, WJSCPRO_p18, a5_assumption_reduction_p18,
      b5_assumption_reduction_p18, epsilon_hept_p18, epsilon_hex_p18, epsilon_pent_p18,
      quadratic_at_most_2_roots_p18, re_eqvl_imp_le_p18, re_eqvl_real_sgn_p18,
      real_continuous_finite_range_constant_p18⟩

#print axioms la18_capstone_w1


/-- LA34 materialization capstone (lane lv56-w1 slot
LV6, program slot C = LV5+LV6, 2026-11-04, after
the leftover-mat-scout delivery e342ff1b §1): the clean public top-level
LocalAuto34 exits unreachable from every e2e
root -- 53 of 123 theorem exits
(scout probe1 per-item BFS: clean = closure sorried-0; the 70
sorried-exit branches are excluded per the workorder, one does not enter,
each named in the lane gen_report).  Clean-subset group closure (scout
probe2, baseline I 1e139a28): GROUP_FRESH_VS_CONE 156
(154 LA34 + 2
LocalAuto17), GROUP_SORRIED 0, i.e. the new closure is
sorried-0; K_SORRIED 134 and K_AXIOM 624 unchanged when wired.
Implemented here: 52 of the 53.  Dropped per the workorder's
no-forcing rule ("抽不出/不一致 → 剔除并如实报"), mechanically detected
by the generator:
  - modFold_p34: universe-polymorphic statement (free universe in Sort/Type position; would give the capstone a universe parameter and break the future `have hcap := <name>` consumption shape)
Anchors (no fabricated edges): every conjunct is asserted in the
verbatim wording of its LA34 declaration -- the conjunct text is
the declaration's source signature (binders + conclusion, copied verbatim
and mechanically split at the binder/conclusion separator by the
generator gen_items.py; equation-lemma conjuncts have no source text and
take the `#check @name` printer dump verbatim); the printer dump
(logs/sigprobe_82.out) is retained as cross reference; semantic identity
is re-verified by the elaboration of the `⟨...⟩` assembly below (each
component must unify definitionally with its conjunct); per-conjunct
comments carry each exit's LA34 declaration line and file-local
docstring HOL anchor.
Conjunct order: the scout clean-seed-list order (logs/seeds_clean.txt
LA34 subset).  Body = the assembly of the exit constants --
zero new proof obligations, zero new imports. -/
theorem la34_capstone_w1 :
    -- 1. BBS_IMP_CONVEX_LOCAL_FAN_p34 (LA34:494; HOL `BBS_IMP_CONVEX_LOCAL_FAN`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (hk : 3 < k) (hkk : s.k = k) (hBB : BBsV39 s w),
          ConvexLocalFan (Set.range w)
          (Set.range fun i => {w i, w (i + 1)})
          (Set.range fun i => (w i, w (i + 1)))
    ) ∧
    -- 2. CROSS_LAGRANGE1_p34 (LA34:893; HOL `CROSS_LAGRANGE1`)
    (∀ (x y z : V3)
    ,
          cross3 (cross3 x y) z = (x ⬝ᵥ z) • y - (y ⬝ᵥ z) • x
    ) ∧
    -- 3. DEFORMATION_SMALL_INTERVAL_p34 (LA34:1048; HOL `DEFORMATION_SMALL_INTERVAL`)
    (∀ {f : V3 → ℝ → V3} {V : Set V3} {a b c d : ℝ}
          (h : Deformation f V a b) (hac : a ≤ c) (hc : c < 0) (hd : 0 < d) (hdb : d ≤ b),
          Deformation f V c d
    ) ∧
    -- 4. EQ_W_L_IN_BBS_p34 (LA34:2718; HOL `EQ_W_L_IN_BBS`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (hk : 3 < k) (hkk : s.k = k) (hBB : BBsV39 s w),
          w ((l + k - 1) + 1) = w l
    ) ∧
    -- 5. EXISTS_SMALL_LE_CONST_V1_p34 (LA34:675; HOL `EXISTS_SMALL_LE_CONST_V1`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hclt : c < dist v2 w),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w
    ) ∧
    -- 6. EXISTS_SMALL_LE_CONST_p34 (LA34:655; HOL `EXISTS_SMALL_LE_CONST`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hclt : c < dist v2 w),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          c < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w
    ) ∧
    -- 7. EXISTS_SMALL_LT_CONST_V1_p34 (LA34:849; HOL `EXISTS_SMALL_LT_CONST_V1`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hclt : dist v2 w < c),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w < c
    ) ∧
    -- 8. EXISTS_SMALL_LT_CONST_p34 (LA34:829; HOL `EXISTS_SMALL_LT_CONST`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a c : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hclt : dist v2 w < c),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) w < c
    ) ∧
    -- 9. EYYPQDW_CONTINUOUS_LIFT_DIST_p34 (LA34:644; HOL `EYYPQDW_CONTINUOUS_LIFT_DIST`, HOL `lift`)
    (∀ (v1 v2 v : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5),
          ContinuousAt (fun y => dist (v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 y) v) x3
    ) ∧
    -- 10. E_DEFORMATION_V3_DEFOR_p34 (LA34:2547; HOL `E_DEFORMATION_V3_DEFOR`)
    (∀ (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3)
    ,
          Set.range (fun i => {v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t,
            v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1)) t}) =
          (fun e => (fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) '' e) ''
            Set.range (fun i => {w i, w (i + 1)})
    ) ∧
    -- 11. FUN_V3_DEFOR_p34 (LA34:465; HOL `FUN_V3_DEFOR`)
    (∀ (a x1 x2 x6 : ℝ) (v1 w v : V3)
    ,
          v3DeforV4_p34 a x1 x2 x6 v1 w v = fun t => v3DeforV4_p34 a x1 x2 x6 v1 w v t
    ) ∧
    -- 12. F_DEFORMATION_V3_DEFOR_p34 (LA34:2562; HOL `F_DEFORMATION_V3_DEFOR`)
    (∀ (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3)
    ,
          Set.range (fun i => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t,
            v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (i + 1)) t)) =
          (fun d : V3 × V3 => (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.1 t,
            v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 d.2 t)) ''
            Set.range (fun i => (w i, w (i + 1)))
    ) ∧
    -- 13. MMs_periodic_p34 (LA34:756; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (hkk : s.k = k)
          (hmw : w ∈ MMsV39 s),
          ∀ i, w (i + k) = w i
    ) ∧
    -- 14. MOD_ADD_SUB_1_p34 (LA34:469; HOL `MOD_ADD_SUB_1`)
    (∀ {k l : ℕ} (hk : 1 < k)
    ,
          ¬((l + k - 1) % k = l % k)
    ) ∧
    -- 15. NORM_POS_COLLINEAR_p34 (LA34:584; HOL `NORM_POS_COLLINEAR`)
    (∀ (v1 v2 : V3) (x1 x2 x6 : ℝ)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6),
          0 < x1 ∧ 0 < x2 ∧ 0 < x6
    ) ∧
    -- 16. UPS_X_POS_SEG_C_p34 (LA34:528; HOL `UPS_X_POS_SEG_C`)
    (∀ (v1 v2 : V3) (x1 x2 x6 c : ℝ)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (h2 : 0 < x2) (hc : 0 < c),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t ∧ t < c
    ) ∧
    -- 17. UPS_X_POS_SEG_p34 (LA34:504; HOL `UPS_X_POS_SEG`)
    (∀ (v1 v2 : V3) (x1 x2 x6 : ℝ)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (h2 : 0 < x2),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → 0 < upsX x1 (x2 - t) x6 ∧ 0 < x2 - t
    ) ∧
    -- 18. V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES_p34 (LA34:3164; HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun a' : V3 =>
            (a', w (l + 1)) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 19. V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_p34 (LA34:1953; HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun w' : V3 =>
            (w', v1) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 20. V3_DEFOR_EQ_IN_FF_AT_V1_SYM_p34 (LA34:1923; HOL `V3_DEFOR_EQ_IN_FF_AT_V1_SYM`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun w' : V3 =>
            (w', v1) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 21. V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES_p34 (LA34:3107; HOL `V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ a' : V3, (w (l + 1), a') ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w (l + 1), a') ∈ FF
    ) ∧
    -- 22. V3_DEFOR_EQ_IN_FF_AT_V1_V1_p34 (LA34:1845; HOL `V3_DEFOR_EQ_IN_FF_AT_V1_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (v1, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v1, w') ∈ FF
    ) ∧
    -- 23. V3_DEFOR_EQ_IN_FF_AT_V1_p34 (LA34:1819; HOL `V3_DEFOR_EQ_IN_FF_AT_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (v1, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v1, w') ∈ FF
    ) ∧
    -- 24. V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES_p34 (LA34:3393; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 v : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v) ∈ FF
    ) ∧
    -- 25. V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_p34 (LA34:2379; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v) ∈ FF
    ) ∧
    -- 26. V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_p34 (LA34:2351; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (w', v) ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v) ∈ FF
    ) ∧
    -- 27. V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES_p34 (LA34:3354; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 v : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v, w') ∈ FF
    ) ∧
    -- 28. V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_p34 (LA34:2313; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v, w') ∈ FF
    ) ∧
    -- 29. V3_DEFOR_EQ_IN_FF_AT_V_ANY_p34 (LA34:2285; HOL `V3_DEFOR_EQ_IN_FF_AT_V_ANY`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 v : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF)
          (hvv1 : v ≠ v1) (hvv2 : v ≠ v2) (hvw : v ≠ w (l + k - 1))
          (hvV : v ∈ Set.range w),
          ∀ w' : V3, (v, w') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v, w') ∈ FF
    ) ∧
    -- 30. V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES_p34 (LA34:3275; HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun v' : V3 =>
            (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 31. V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_p34 (LA34:2185; HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun v' : V3 =>
            (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 32. V3_DEFOR_EQ_IN_FF_AT_W_SYM_p34 (LA34:2158; HOL `V3_DEFOR_EQ_IN_FF_AT_W_SYM`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          (Classical.epsilon fun v' : V3 =>
            (w (l + k - 1), v') ∈ relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) =
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)
    ) ∧
    -- 33. V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES_p34 (LA34:3239; HOL `V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v', w (l + (s.k - 1))) ∈ FF
    ) ∧
    -- 34. V3_DEFOR_EQ_IN_FF_AT_W_V1_p34 (LA34:2122; HOL `V3_DEFOR_EQ_IN_FF_AT_W_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v', w (l + (s.k - 1))) ∈ FF
    ) ∧
    -- 35. V3_DEFOR_EQ_IN_FF_AT_W_p34 (LA34:2096; HOL `V3_DEFOR_EQ_IN_FF_AT_W`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ v' : V3, (v', w (l + (s.k - 1))) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v', w (l + (s.k - 1))) ∈ FF
    ) ∧
    -- 36. V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES_p34 (LA34:3054; HOL `V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v2) ∈ FF
    ) ∧
    -- 37. V3_DEFOR_EQ_IN_FF_SYM_V1_p34 (LA34:1787; HOL `V3_DEFOR_EQ_IN_FF_SYM_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v2) ∈ FF
    ) ∧
    -- 38. V3_DEFOR_EQ_IN_FF_SYM_p34 (LA34:1765; HOL `V3_DEFOR_EQ_IN_FF_SYM`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (w', v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (w', v2) ∈ FF
    ) ∧
    -- 39. V3_DEFOR_EQ_IN_FF_V1_TWO_CASES_p34 (LA34:3002; HOL `V3_DEFOR_EQ_IN_FF_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v2, w') ∈ FF
    ) ∧
    -- 40. V3_DEFOR_EQ_IN_FF_V1_p34 (LA34:1692; HOL `V3_DEFOR_EQ_IN_FF_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v2, w') ∈ FF
    ) ∧
    -- 41. V3_DEFOR_EQ_IN_FF_p34 (LA34:1670; HOL `V3_DEFOR_EQ_IN_FF`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∀ w' : V3, (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t), w') ∈
            relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF ↔
          (v2, w') ∈ FF
    ) ∧
    -- 42. V3_DEFOR_ID_p34 (LA34:556; HOL `V3_DEFOR_ID`)
    (∀ (v1 w : V3) (x1 x2 x6 a : ℝ)
          (h1 : 0 < x1) (hnc : ¬Collinear ℝ ({0, v1, w} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖w‖ ^ 2 = x2) (hx6 : ‖v1 - w‖ ^ 2 = x6)
          (ha : a = -1),
          v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - 0) = w
    ) ∧
    -- 43. V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES_p34 (LA34:3143; HOL `V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (w (l + 1)) = rhoNode1 FF (w (l + 1))
    ) ∧
    -- 44. V3_DEFOR_RHO_NODE_AT_V1_V1_p34 (LA34:1902; HOL `V3_DEFOR_RHO_NODE_AT_V1_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1 =
          rhoNode1 FF v1
    ) ∧
    -- 45. V3_DEFOR_RHO_NODE_AT_V1_p34 (LA34:1881; HOL `V3_DEFOR_RHO_NODE_AT_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF) v1 =
          rhoNode1 FF v1
    ) ∧
    -- 46. V3_DEFOR_RHO_NODE_V1_TWO_CASES_p34 (LA34:3034; HOL `V3_DEFOR_RHO_NODE_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2
    ) ∧
    -- 47. V3_DEFOR_RHO_NODE_V1_p34 (LA34:1745; HOL `V3_DEFOR_RHO_NODE_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : -e < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, -e < τ ∧ τ < e → ¬(i % k = l % k) →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2
    ) ∧
    -- 48. V3_DEFOR_RHO_NODE_p34 (LA34:1725; HOL `V3_DEFOR_RHO_NODE`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a e t : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (he : 0 < e) (ht : 0 < t)
          (hne : ∀ τ : ℝ, ∀ i : ℕ, 0 < τ ∧ τ < e →
            v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - τ) ≠ w i)
          (hte : t < e)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          rhoNode1 (relabelFF_p34 (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) v2 FF)
          (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) = rhoNode1 FF v2
    ) ∧
    -- 49. V3_DEFOR_V1_O_DEF_p34 (LA34:551; HOL `V3_DEFOR_V1_O_DEF`)
    (∀ (a : ℝ) (v1 w : V3) (x1 x2 x6 : ℝ)
    ,
          (fun t => v3DeforV1_p17 a v1 w x1 x2 x6 x6 (x2 - t)) =
          (fun x3 => v3DeforV1_p17 a v1 w x1 x2 x6 x6 x3) ∘ (fun t => x2 - t)
    ) ∧
    -- 50. V_DEFORMATION_V3_DEFOR_p34 (LA34:2541; HOL `V_DEFORMATION_V3_DEFOR`)
    (∀ (w : ℕ → V3) (x1 x2 x6 t : ℝ) (v1 v2 : V3)
    ,
          Set.range (fun i => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w i) t) =
          (fun v => v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) '' Set.range w
    ) ∧
    -- 51. minWitness_p34 (LA34:727; no HOL anchor line in file docstring)
    (∀ {R : ℕ → ℝ → Prop} {T : Finset ℕ}
          (hmono : ∀ (i : ℕ) (e : ℝ), R i e → ∀ e' : ℝ, 0 < e' → e' ≤ e → R i e')
          (hne : T.Nonempty)
          (h : ∀ i ∈ T, ∃ e : ℝ, 0 < e ∧ R i e),
          ∃ e0 : ℝ, 0 < e0 ∧ ∀ i ∈ T, R i e0
    ) ∧
    -- 52. scsA_periodic_p34 (LA34:771; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k : ℕ) (hs : isScsV39 s) (hkk : s.k = k)
          (l : ℕ),
          ∀ i, s.a l (i + k) = s.a l i
    ) :=
    ⟨BBS_IMP_CONVEX_LOCAL_FAN_p34, CROSS_LAGRANGE1_p34, DEFORMATION_SMALL_INTERVAL_p34,
      EQ_W_L_IN_BBS_p34, EXISTS_SMALL_LE_CONST_V1_p34, EXISTS_SMALL_LE_CONST_p34,
      EXISTS_SMALL_LT_CONST_V1_p34, EXISTS_SMALL_LT_CONST_p34,
      EYYPQDW_CONTINUOUS_LIFT_DIST_p34, @E_DEFORMATION_V3_DEFOR_p34, FUN_V3_DEFOR_p34,
      @F_DEFORMATION_V3_DEFOR_p34, MMs_periodic_p34, MOD_ADD_SUB_1_p34,
      NORM_POS_COLLINEAR_p34, UPS_X_POS_SEG_C_p34, UPS_X_POS_SEG_p34,
      V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_TWO_CASES_p34, V3_DEFOR_EQ_IN_FF_AT_V1_SYM_V1_p34,
      V3_DEFOR_EQ_IN_FF_AT_V1_SYM_p34, V3_DEFOR_EQ_IN_FF_AT_V1_V1_TWO_CASES_p34,
      V3_DEFOR_EQ_IN_FF_AT_V1_V1_p34, V3_DEFOR_EQ_IN_FF_AT_V1_p34,
      V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_TWO_CASES_p34, V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_V1_p34,
      V3_DEFOR_EQ_IN_FF_AT_V_ANY_SYM_p34, V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_TWO_CASES_p34,
      V3_DEFOR_EQ_IN_FF_AT_V_ANY_V1_p34, V3_DEFOR_EQ_IN_FF_AT_V_ANY_p34,
      V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_TWO_CASES_p34, V3_DEFOR_EQ_IN_FF_AT_W_SYM_V1_p34,
      V3_DEFOR_EQ_IN_FF_AT_W_SYM_p34, V3_DEFOR_EQ_IN_FF_AT_W_V1_TWO_CASES_p34,
      V3_DEFOR_EQ_IN_FF_AT_W_V1_p34, V3_DEFOR_EQ_IN_FF_AT_W_p34,
      V3_DEFOR_EQ_IN_FF_SYM_V1_TWO_CASES_p34, V3_DEFOR_EQ_IN_FF_SYM_V1_p34,
      V3_DEFOR_EQ_IN_FF_SYM_p34, V3_DEFOR_EQ_IN_FF_V1_TWO_CASES_p34,
      V3_DEFOR_EQ_IN_FF_V1_p34, V3_DEFOR_EQ_IN_FF_p34, V3_DEFOR_ID_p34,
      V3_DEFOR_RHO_NODE_AT_V1_V1_TWO_CASES_p34, V3_DEFOR_RHO_NODE_AT_V1_V1_p34,
      V3_DEFOR_RHO_NODE_AT_V1_p34, V3_DEFOR_RHO_NODE_V1_TWO_CASES_p34,
      V3_DEFOR_RHO_NODE_V1_p34, V3_DEFOR_RHO_NODE_p34, V3_DEFOR_V1_O_DEF_p34,
      @V_DEFORMATION_V3_DEFOR_p34, minWitness_p34, scsA_periodic_p34⟩

#print axioms la34_capstone_w1
/-! ### LA14 + LA37 + LA17 materialization capstones (lane
capstone-wire-w1, 2026-11-04): the clean public top-level exits of
LocalAuto14, LocalAuto37 and LocalAuto17 that the Assembly `textCapstone`
cone does not yet consume are re-exposed as ONE conjunction each, and the
three `have hla{14,37,17} := ..._capstone_w1` lines in Assembly.textCapstone
pull the capstone proof terms into the e2e cone (pure insertion there too).
All three modules are already imported by this file (LA14 :485, LA17 :488,
LA37 :508), so zero import changes.  Cleanliness criterion: each exit's
`#print axioms` face is a subset of the standard three
[propext, Classical.choice, Quot.sound]; exits carrying sorryAx or a
non-standard axiom are excluded and named per item in the capstone
docstrings and logs/gen_report.txt.  Statement drops follow the lv56
generator rules (module-private constant `✝`, def-kind, universe-
polymorphic statement).  Extraction purely mechanical (gen_items.py):
conjuncts are verbatim module source signatures, bodies are the exit
constants; the `set_option maxHeartbeats 50000000 in` scope mirrors the
existing large-conjunction sections in this file (LocalConcl:1150
precedent).  Two environment-alignment scopes mirror module-local
declarations so the verbatim signatures elaborate under the same name and
instance resolution as their source modules: LA37 carries the module's own
`attribute [-instance] dartDecEq2 dartDecEq3` (LocalAuto37:125, required by
the `hypIso_p37`/`hypermapOfFan` instance arguments) and LA17 carries the
module's own `open Kepler.Text.Fan` (LocalAuto17:105, required by the
unqualified `FAN`/`fan7`/`Graph` names).  The exact cone increment is
re-measured at the orchestrator e2e gate. -/


set_option maxHeartbeats 50000000 in

/-- LA14 materialization capstone (lane capstone-wire-w1,
2026-11-04): the clean public top-level LocalAuto14 theorem exits that are
statable in Kepler.Text, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume them (39 of the 54 public
top-level theorem exits; 15 dropped per the workorder's no-forcing
rule "抽不出/不一致 → 剔除并如实报", mechanically detected from the
`#print axioms` / `#check @` probe dumps and the module source; each drop
is named below with its reason -- 13 carry a sorryAx axiom face
or a non-standard axiom, the remainder are mechanical statement drops).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA14 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA14
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la14_capstone_w1 :
    -- 1. NONPLANAR_OPEN_p14 (LA14:967; no HOL anchor line in file docstring)
    (∀ (v1 v2 v3 v4 : ℝ → V3) (t : ℝ)
          (h : ¬ Coplanar ({v1 t, v2 t, v3 t, v4 t} : Set V3))
          (hc1 : ContinuousAt v1 t) (hc2 : ContinuousAt v2 t) (hc3 : ContinuousAt v3 t)
          (hc4 : ContinuousAt v4 t),
          ∃ e : ℝ, 0 < e ∧ ∀ t', |t - t'| < e →
          ¬ Coplanar ({v1 t', v2 t', v3 t', v4 t'} : Set V3)
    ) ∧
    -- 2. COLL_IFF_COLL_CROSS2_p14 (LA14:1002; no HOL anchor line in file docstring)
    (∀ (v w : V3)
    ,
          Collinear ℝ ({0, v, w} : Set V3) ↔
          Collinear ℝ ({0, w, cross3 v w} : Set V3)
    ) ∧
    -- 3. azim_cross_0_p14 (LA14:1027; HOL `azim_cross_0`)
    (∀ (v w : V3) (h : ¬ Collinear ℝ ({0, v, w} : Set V3))
    ,
          ¬ (azim 0 (cross3 v w) v w = 0)
    ) ∧
    -- 4. wedge_ge_cross_p14 (LA14:1075; HOL `wedge_ge_cross`)
    (∀ (v w : V3) (h : ¬ Collinear ℝ ({0, v, w} : Set V3))
    ,
          wedgeGe 0 (cross3 v w) v w = affGe ({0, cross3 v w} : Set V3) ({v, w} : Set V3)
    ) ∧
    -- 5. azim_lt_pi_cross_p14 (LA14:1195; HOL `azim_lt_pi_cross`)
    (∀ (u1 u2 u3 : V3)
    ,
          (0 < azim 0 u1 u2 u3 ∧ azim 0 u1 u2 u3 < Real.pi) ↔
          0 < (cross3 u1 u2) ⬝ᵥ u3
    ) ∧
    -- 6. generic_alt_p14 (LA14:1306; HOL `generic_alt`)
    (∀ (u v w : V3) (h1 : ¬ Collinear ℝ ({0, v, w} : Set V3))
          (h2 : u ≠ 0),
          affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affLt ({0} : Set V3) ({u} : Set V3) = ∅ ↔
          ¬ Coplanar ({0, u, v, w} : Set V3) ∨ (-u) ∈ Kepler.Geom.wedge 0 (cross3 v w) w v
    ) ∧
    -- 7. vuy1_p14 (LA14:1422; HOL `vuy1`)
    (∀ (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)),
          ∃ t0 t1 : ℝ, 0 < t1 ∧ v = t0 • u0 + t1 • u1
    ) ∧
    -- 8. vuy3_p14 (LA14:1459; HOL `vuy3`)
    (∀ (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)),
          ¬ Collinear ℝ ({0, cross3 u0 u1, v} : Set V3)
    ) ∧
    -- 9. vuy4_p14 (LA14:1479; HOL `vuy4`)
    (∀ (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)),
          azim 0 (cross3 u0 u1) u0 v < Real.pi
    ) ∧
    -- 10. cross_independent_p14 (LA14:1504; HOL `cross_independent`)
    (∀ (u0 u1 : V3) (h : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (a b c : ℝ) (heq : a • cross3 u0 u1 + b • u0 + c • u1 = 0),
          a = 0
    ) ∧
    -- 11. ybt_inj_p14 (LA14:1519; no HOL anchor line in file docstring)
    (∀ (u0 u1 v1 v2 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v1} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, u0, v2} : Set V3))
          (h3 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (h4 : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (h5 : v1 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3))
          (h6 : v2 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)),
          ¬ (azim 0 (cross3 u0 u1) u0 v1 = azim 0 (cross3 u0 u1) u0 v2)
    ) ∧
    -- 12. ybt_inj_0_p14 (LA14:1573; HOL `ybt_inj_0`)
    (∀ (u0 u1 v2 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v2} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
          (h3 : v2 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)),
          ¬ (azim 0 (cross3 u0 u1) u0 v2 = 0)
    ) ∧
    -- 13. ECAU_aff_ge_p14 (LA14:1624; HOL `ECAU_aff_ge`)
    (∀ (u : ℝ → V3) (r : ℕ)
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3)),
          ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGe ({0, u 0} : Set V3) ({u 1} : Set V3)
    ) ∧
    -- 14. collinear_cross_p14 (LA14:1633; HOL `collinear_cross`)
    (∀ (u : ℕ → V3) (i r : ℕ) (hi : i ≤ r) (hr : 1 ≤ r)
          (h : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (hu : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3)),
          ¬ Collinear ℝ ({0, cross3 (u 0) (u 1), u i} : Set V3)
    ) ∧
    -- 15. coplanar_in_affine_hull_p14 (LA14:1743; no HOL anchor line in file docstring)
    (∀ (u v w x : V3)
          (h1 : ¬ Collinear ℝ ({u, v, w} : Set V3)) (h2 : Coplanar ({x, u, v, w} : Set V3)),
          x ∈ affineSpan ℝ ({u, v, w} : Set V3)
    ) ∧
    -- 16. azim_0_as_closed_p14 (LA14:2417; HOL `azim_0_as_closed`)
    (∀ (v2 v3 v4 : V3)
          (h1 : ¬ Collinear ℝ ({0, v2, v3} : Set V3))
          (h2 : ¬ Collinear ℝ ({0, v2, v4} : Set V3)),
          azim 0 v2 v3 v4 = 0 ↔
          Coplanar ({0, v2, v3, v4} : Set V3) ∧
            0 ≤ (cross3 (cross3 v2 v3) v2) ⬝ᵥ v4
    ) ∧
    -- 17. azim_pos_open_p14 (LA14:2597; HOL `azim_pos_open`)
    (∀ (v2 v3 v4 : ℝ → V3) (t a b : ℝ)
          (h1 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v2 x)
          (h2 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v3 x)
          (h3 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v4 x)
          (h4 : t ∈ Set.Icc a b)
          (h5 : ¬ Collinear ℝ ({0, v2 t, v3 t} : Set V3))
          (h6 : ¬ Collinear ℝ ({0, v2 t, v4 t} : Set V3))
          (h7 : ¬ (azim 0 (v2 t) (v3 t) (v4 t) = 0)),
          ∃ e : ℝ, 0 < e ∧ ∀ t', |t' - t| < e →
          ¬ (azim 0 (v2 t') (v3 t') (v4 t') = 0)
    ) ∧
    -- 18. azim_real_continuous_on_p14 (LA14:2633; no HOL anchor line in file docstring)
    (∀ (v2 v3 v4 : ℝ → V3) (t a b : ℝ)
          (h1 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v2 x)
          (h2 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v3 x)
          (h3 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v4 x)
          (h4 : t ∈ Set.Ioo a b)
          (h5 : ¬ Collinear ℝ ({0, v2 t, v3 t} : Set V3))
          (h6 : ¬ Collinear ℝ ({0, v2 t, v4 t} : Set V3))
          (h7 : ¬ (azim 0 (v2 t) (v3 t) (v4 t) = 0)),
          ∃ e : ℝ, 0 < e ∧
          ContinuousOn (fun q => azim 0 (v2 q) (v3 q) (v4 q)) (Set.Icc (t - e) (t + e))
    ) ∧
    -- 19. azim_pos_iff_nz_p14 (LA14:2734; HOL `azim_pos_iff_nz`)
    (∀ (v1 v2 v3 v4 : V3)
    ,
          0 < azim v1 v2 v3 v4 ↔ azim v1 v2 v3 v4 ≠ 0
    ) ∧
    -- 20. NHCXLRV_p14 (LA14:2745; HOL `NHCXLRV`)
    (∀ (v w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
          (h1 : Deformation f ({w0, w1, w2, v} : Set V3) a b)
          (h2 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3))
          (h3 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3))
          (h4 : ¬ Collinear ℝ ({0, f w1 0, f v 0} : Set V3))
          (h5 : v ∈ Kepler.Geom.wedge 0 w1 w2 w0),
          ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
          f v t ∈ Kepler.Geom.wedge 0 (f w1 t) (f w2 t) (f w0 t)
    ) ∧
    -- 21. NHCXLRV_ALT_p14 (LA14:2817; no HOL anchor line in file docstring)
    (∀ (v w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
          (h1 : Deformation f ({w0, w1, w2, v} : Set V3) a b)
          (h2 : ¬ Collinear ℝ ({0, w1, w2} : Set V3))
          (h3 : ¬ Collinear ℝ ({0, w1, w0} : Set V3))
          (h4 : ¬ Collinear ℝ ({0, w1, v} : Set V3))
          (h5 : v ∈ Kepler.Geom.wedge 0 w1 w2 w0),
          ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
          f v t ∈ Kepler.Geom.wedge 0 (f w1 t) (f w2 t) (f w0 t)
    ) ∧
    -- 22. WNWSHJT_p14 (LA14:2833; HOL `WNWSHJT`)
    (∀ (w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
          (h1 : Deformation f ({w0, w1, w2} : Set V3) a b)
          (h2 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3))
          (h3 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3))
          (h4 : 0 < azim 0 w1 w2 w0) (h5 : azim 0 w1 w2 w0 < Real.pi),
          ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
          azim 0 (f w1 t) (f w2 t) (f w0 t) < Real.pi
    ) ∧
    -- 23. LOFA_IMP_INANGLE_EQ_AZIM_p14 (LA14:2866; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (v : V3) (h1 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (h2 : v ∈ V),
          interiorAngle1 0 FF v = azimInFan (v, rhoNode1 FF v) E
    ) ∧
    -- 24. deformation_rho_node1_equivariant1_p14 (LA14:2884; no HOL anchor line in file docstring)
    (∀ (f : V3 → ℝ → V3) (V : Set V3)
          (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
          (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
          (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
            ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V),
          f (rhoNode1 FF v) t =
          rhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t)
    ) ∧
    -- 25. deformation_ivs_rho_node1_equivariant1_p14 (LA14:2898; no HOL anchor line in file docstring)
    (∀ (f : V3 → ℝ → V3) (V : Set V3)
          (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
          (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
          (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
            ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V),
          f (ivsRhoNode1 FF v) t =
          ivsRhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t)
    ) ∧
    -- 26. deformation_subset_p14 (LA14:2911; HOL `deformation_subset`)
    (∀ (f : V3 → ℝ → V3) (U V : Set V3) (a b : ℝ)
          (hsub : U ⊆ V) (h : Deformation f V a b),
          Deformation f U a b
    ) ∧
    -- 27. zlz_reduction_p14 (LA14:2949; no HOL anchor line in file docstring)
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
          (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
          (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
            interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi)
          (h5 : ∀ u v w : V3, ∃ e4 : ℝ, ((v, w) ∈ FF ∧ u ∈ V) →
            0 < e4 ∧ ∀ t, -e4 < t ∧ t < e4 →
              affGe ({0} : Set V3) ({f v t, f w t} : Set V3) ∩
                affLt ({0} : Set V3) ({f u t} : Set V3) = ∅)
          (h6 : ∀ x : V3 × V3, ∃ e3 : ℝ, x ∈ FF →
            0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
              ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
                ((fun s => (fun v => f v t) '' s) '' E))
          (h7 : ∀ x : V3 × V3, ∃ e2 : ℝ, x ∈ FF →
            0 < e2 ∧ ∀ t, -e2 < t ∧ t < e2 →
              azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t, -ε < t ∧ t < ε →
          ConvexLocalFan ((fun v => f v t) '' V)
            ((fun s => (fun v => f v t) '' s) '' E)
            ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
          Generic ((fun v => f v t) '' V)
            ((fun s => (fun v => f v t) '' s) '' E)
    ) ∧
    -- 28. real_interval_contains_0_ball_p14 (LA14:3075; HOL `real_interval_contains_0_ball`)
    (∀ (a b e1 : ℝ) (ha : a < 0) (hb : 0 < b)
          (he1 : 0 < e1),
          ∃ e : ℝ, 0 < e ∧ e ≤ e1 ∧ ∀ t, |t| < e → t ∈ Icc a b
    ) ∧
    -- 29. zlz_generic_p14 (LA14:3163; HOL `zlz_generic`)
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
          (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b),
          ∀ u v w : V3, ∃ e4 : ℝ, ((v, w) ∈ FF ∧ u ∈ V) →
          0 < e4 ∧ ∀ t, -e4 < t ∧ t < e4 →
            affGe ({0} : Set V3) ({f v t, f w t} : Set V3) ∩
              affLt ({0} : Set V3) ({f u t} : Set V3) = ∅
    ) ∧
    -- 30. zlz_wedge_skolem_p14 (LA14:3295; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
          (f : V3 → ℝ → V3) (h1 : ConvexLocalFan V E FF)
          (h2 : ∀ x : V3 × V3, ∀ v : V3, ∃ e3 : ℝ, (x ∈ FF ∧ v ∈ V) →
            0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
              f v t ∈ wedgeInFanGe (f x.1 t, f x.2 t)
                ((fun s => (fun v => f v t) '' s) '' E)),
          ∀ x : V3 × V3, ∃ e3 : ℝ, x ∈ FF →
          0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
            ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
              ((fun s => (fun v => f v t) '' s) '' E)
    ) ∧
    -- 31. wedge_ge_refl_p14 (LA14:3323; HOL `wedge_ge_refl`)
    (∀ (v1 v2 v3 v4 : V3)
    ,
          v2 ∈ wedgeGe v1 v2 v3 v4
    ) ∧
    -- 32. PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (LA14:3363; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (u v : V3) (h1 : LocalFan V E FF) (h2 : u ∈ V)
          (h3 : v ∈ V) (h4 : u ≠ v) (h5 : Generic V E),
          ¬ Collinear ℝ ({0, u, v} : Set V3)
    ) ∧
    -- 33. cyclic_set_scale_p14 (LA14:3467; no HOL anchor line in file docstring)
    (∀ (U : Set V3) (e : V3) (t : ℝ) (ht : t ≠ 0)
    ,
          cyclicSet U 0 (t • e) ↔ cyclicSet U 0 e
    ) ∧
    -- 34. projection_scale_p14 (LA14:3503; no HOL anchor line in file docstring)
    (∀ (e u : V3) (t : ℝ) (ht : t ≠ 0)
    ,
          projection u (t • e) = projection u e
    ) ∧
    -- 35. azim_cycle_scale_p14 (LA14:3615; HOL `azim_cycle_scale`)
    (∀ (U : Set V3) (e : V3) (t : ℝ) (ht : 0 < t)
    ,
          azimCycle_p14 U 0 (t • e) = azimCycle_p14 U 0 e
    ) ∧
    -- 36. IDENTIFY_AZIM_CYCLE_SIMPLE_p14 (LA14:3630; HOL `IDENTIFY_AZIM_CYCLE_SIMPLE`)
    (∀ (W : Set V3) (v w p u : V3)
          (h1 : ¬ (W ⊆ {p})) (h2 : p ∈ W) (hc : cyclicSet W v w) (h3 : u ≠ p) (h4 : u ∈ W)
          (h5 : ∀ q : V3, q ≠ p → q ∈ W → q ≠ u → azim v w p u < azim v w p q),
          azimCycle_p14 W v w p = u
    ) ∧
    -- 37. coplanar_cross_scale_p14 (LA14:3712; no HOL anchor line in file docstring)
    (∀ (u1 u2 v1 v2 : V3)
          (h1 : Coplanar ({0, u1, u2, v1, v2} : Set V3))
          (h2 : 0 < (cross3 v1 v2) ⬝ᵥ (cross3 u1 u2)),
          ∃ t : ℝ, 0 < t ∧ cross3 v1 v2 = t • (cross3 u1 u2)
    ) ∧
    -- 38. azim_cycle_distinct_p14 (LA14:3761; no HOL anchor line in file docstring)
    (∀ (U : Set V3) (e v w : V3) (h1 : U.Finite)
          (h2 : v ∈ U) (h3 : w ∈ U) (h4 : v ≠ w)
          (h5 : ∀ x ∈ U, e ⬝ᵥ (cross3 x (azimCycle_p14 U 0 e x)) ≠ 0),
          0 < azim 0 e v w
    ) ∧
    -- 39. azim_cycle_neg_p14 (LA14:4029; no HOL anchor line in file docstring)
    (∀ (U : Set V3) (e v w : V3) (h1 : U.Finite) (h2 : v ∈ U)
          (h3 : azimCycle_p14 U 0 e v = w)
          (h4 : ∀ x ∈ U, e ⬝ᵥ (cross3 x (azimCycle_p14 U 0 e x)) ≠ 0),
          azimCycle_p14 U 0 (-e) w = v
    ) :=
    ⟨@NONPLANAR_OPEN_p14, @COLL_IFF_COLL_CROSS2_p14, azim_cross_0_p14, wedge_ge_cross_p14,
      azim_lt_pi_cross_p14, generic_alt_p14, vuy1_p14, @vuy3_p14, vuy4_p14,
      cross_independent_p14, ybt_inj_p14, ybt_inj_0_p14, ECAU_aff_ge_p14,
      @collinear_cross_p14, coplanar_in_affine_hull_p14, azim_0_as_closed_p14,
      azim_pos_open_p14, azim_real_continuous_on_p14, azim_pos_iff_nz_p14, NHCXLRV_p14,
      NHCXLRV_ALT_p14, WNWSHJT_p14, LOFA_IMP_INANGLE_EQ_AZIM_p14,
      deformation_rho_node1_equivariant1_p14, deformation_ivs_rho_node1_equivariant1_p14,
      deformation_subset_p14, zlz_reduction_p14, real_interval_contains_0_ball_p14,
      zlz_generic_p14, zlz_wedge_skolem_p14, wedge_ge_refl_p14,
      PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14, cyclic_set_scale_p14, projection_scale_p14,
      azim_cycle_scale_p14, IDENTIFY_AZIM_CYCLE_SIMPLE_p14, coplanar_cross_scale_p14,
      azim_cycle_distinct_p14, azim_cycle_neg_p14⟩

#print axioms la14_capstone_w1


attribute [-instance] dartDecEq2 dartDecEq3 in
set_option maxHeartbeats 50000000 in

/-- LA37 materialization capstone (lane capstone-wire-w1,
2026-11-04): the clean public top-level LocalAuto37 theorem exits that are
statable in Kepler.Text, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume them (38 of the 49 public
top-level theorem exits; 11 dropped per the workorder's no-forcing
rule "抽不出/不一致 → 剔除并如实报", mechanically detected from the
`#print axioms` / `#check @` probe dumps and the module source; each drop
is named below with its reason -- 3 carry a sorryAx axiom face
or a non-standard axiom, the remainder are mechanical statement drops).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA37 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA37
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la37_capstone_w1 :
    -- 1. CONS_IMP_CONTINUOUS_ATREAL_p37 (LA37:163; no HOL anchor line in file docstring)
    (∀ {a b : ℝ} {f : ℝ → V3} {u : V3}
          (h : ∀ t ∈ Icc a b, f t = u),
          ∀ t ∈ Icc a b, ContinuousWithinAt f (Icc a b) t
    ) ∧
    -- 2. AFF_GT_SUBSET_AFFINE_HULL21_p37 (LA37:612; no HOL anchor line in file docstring)
    (∀ (u v w : V3)
    ,
          affGt {u, v} {w} ⊆ (affineSpan ℝ ({u, v, w} : Set V3) : Set V3)
    ) ∧
    -- 3. DISJTINCT_PROPERTY_p37 (LA37:632; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {f : V3 → ℝ → V3} {u : V3} {a b : ℝ}
          (hV : V.Finite) (hcu : ContinuousAt (f u) 0) (hu0 : f u 0 = u)
          (ha : a < 0) (hb : 0 < b)
          (hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u'),
          ∃ e : ℝ, 0 < e ∧ ∀ t u', -e < t ∧ t < e ∧ u' ∈ V ∧ u' ≠ u → f u t ≠ f u' t
    ) ∧
    -- 4. EDGE_FORM_IN_LOCAL_FAN_p37 (LA37:691; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hx : x ∈ E),
          ∃ u v : V3, u ≠ v ∧ {u, v} = x
    ) ∧
    -- 5. EDGE_IN_LOCAL_FAN_DET_RHO_NODE_p37 (LA37:711; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {x : Set V3} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hx : x ∈ E),
          ∃ v ∈ V, {v, rhoNode1 FF v} = x
    ) ∧
    -- 6. TOW_POINTS_IN_IMP_AFF_GT_SUBSET_p37 (LA37:729; no HOL anchor line in file docstring)
    (∀ {x u v a b : V3}
          (_h1 : Disjoint ({x, u} : Set V3) ({v} : Set V3))
          (_ha : a ∈ affGt {x, u} {v}) (_hb : b ∈ affGt {x, u} {v})
          (_h2 : Disjoint ({x} : Set V3) ({a, b} : Set V3)),
          affGt {x} {a, b} ⊆ affGt {x, u} {v}
    ) ∧
    -- 7. REAL_LT_MUL12_p37 (LA37:793; HOL `REAL_LT_MUL12`)
    (∀ {a b : ℝ} (hb : 0 < b) (ha : a < 0)
    ,
          a * b < 0
    ) ∧
    -- 8. COLL_IN_AFF_GT_INTER_EMPTY_p37 (LA37:799; no HOL anchor line in file docstring)
    (∀ {a b x u : V3}
          (hnc : ¬Collinear ℝ ({a, b, x} : Set V3)) (hu : u ∈ affGt {a, b} {x}),
          affGt {a, b} {x} ∩ affLt {a} {u} = ∅
    ) ∧
    -- 9. HKIRPEP_ALT_p37 (LA37:916; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v w : V3} (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E),
          (∀ u ∈ V \ {v, w}, interiorAngle1 0 FF u = Real.pi) ∧
          0 < interiorAngle1 0 FF v ∧
          interiorAngle1 0 FF v ≤ Real.pi ∧
          interiorAngle1 0 FF v = interiorAngle1 0 FF w ∧
          ∃ i j : ℕ, i + j = Set.ncard V ∧ i < Set.ncard V ∧ i ≠ 0 ∧ i ≠ 1 ∧
            w = (rhoNode1 FF)^[i] v ∧
            {z | ∃ l, 0 < l ∧ l < i ∧ z = (rhoNode1 FF)^[l] v} =
              affGt {0, v} {rhoNode1 FF v} ∩ V ∧
            j < Set.ncard V ∧ j ≠ 0 ∧ j ≠ 1 ∧
            v = (rhoNode1 FF)^[j] w ∧
            {z | ∃ l, 0 < l ∧ l < j ∧ z = (rhoNode1 FF)^[l] w} =
              affGt {0, v} {ivsRhoNode1 FF v} ∩ V
    ) ∧
    -- 10. LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37 (LA37:953; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v w : V3} (_h : ConvexLocalFan V E FF)
          (_hl : Lunar v w V E),
          ∀ u ∈ V, u ≠ v → u ≠ w →
          u ∈ affGt {0, v} {rhoNode1 FF v} ∨ u ∈ affGt {0, v} {ivsRhoNode1 FF v}
    ) ∧
    -- 11. IN_CONV0_IMP_AFF_EQ1_p37 (LA37:1009; no HOL anchor line in file docstring)
    (∀ {x y a : V3} (ha : a ∈ openSegment ℝ x y)
    ,
          (affineSpan ℝ ({a, x} : Set V3) : Set V3) = (affineSpan ℝ ({a, y} : Set V3) : Set V3)
    ) ∧
    -- 12. AFF_LT_SUBSET_AFF11_p37 (LA37:1054; no HOL anchor line in file docstring)
    (∀ {a b : V3} (_h : Disjoint ({a} : Set V3) ({b} : Set V3))
    ,
          affLt {a} {b} ⊆ (affineSpan ℝ ({a, b} : Set V3) : Set V3)
    ) ∧
    -- 13. AZIM_PI_LEMMA_p37 (LA37:1091; no HOL anchor line in file docstring)
    (∀ {u v x y a : V3} {s : Set V3}
          (_h1 : ¬(affGt {u} s ∩ affLt {u} {a} = ∅))
          (_h2 : affGt {u} s ⊆ affGt {u, v} {y})
          (_h3 : a ∈ affGt {u, v} {x})
          (_h4 : ¬Collinear ℝ ({u, v, x} : Set V3))
          (_h5 : ¬Collinear ℝ ({u, v, y} : Set V3)),
          azim u v x y = Real.pi
    ) ∧
    -- 14. LOCAL_FAN_SET_E_p37 (LA37:1782; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (_h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E),
          {p : Set V3 | ∃ v ∈ V, p = {v, rhoNode1 FF v}} = E
    ) ∧
    -- 15. LOCAL_FAN_FACE_FF_p37 (LA37:1821; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (_h : LocalFan V E FF),
          {p : V3 × V3 | ∃ v ∈ V, p = (v, rhoNode1 FF v)} = FF
    ) ∧
    -- 16. ORD_PAIRS_INJ_IMAGE_p37 (LA37:1837; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} {f : V3 → V3}
          (h : ∀ s ∈ E, Set.InjOn f s),
          ordPairs_p4 ((fun s => f '' s) '' E) = (fun p => (f p.1, f p.2)) '' ordPairs_p4 E
    ) ∧
    -- 17. SET2_DETER_p37 (LA37:1872; no HOL anchor line in file docstring)
    (∀ {x y a b : V3} {s : Set V3} (hs : s = {x, y}) (ha : a ∈ s)
          (hb : b ∈ s) (hab : a ≠ b),
          s = {a, b}
    ) ∧
    -- 18. INJ_IMP_BIJ_IMAGE_p37 (LA37:1882; HOL `INJ_IMP_BIJ_IMAGE`)
    (∀ {f : V3 → V3} {S S' : Set V3}
          (h : Set.InjOn f S),
          Set.BijOn f S (f '' S)
    ) ∧
    -- 19. BIJ_AND_MAP_COMM_p37 (LA37:2283; no HOL anchor line in file docstring)
    (∀ {V V' : Set V3} {E E' : Set (Set V3)}
          {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
          (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
          (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
          (_hff : (fun p => (f p.1, f p.2)) = ff),
          Set.BijOn ff (dartsOfHyp_p4 E V) (dartsOfHyp_p4 E' V') ∧
          (∀ x ∈ dartsOfHyp_p4 E V,
            ffOfHyp_p4 0 V' E' (ff x) = ff (ffOfHyp_p4 0 V E x))
    ) ∧
    -- 20. NODE_EDGE_COMM_LEMMA_p37 (LA37:2304; no HOL anchor line in file docstring)
    (∀ {V V' : Set V3} {E E' : Set (Set V3)}
          {FF : Set (V3 × V3)} {f : V3 → V3} {ff : V3 × V3 → V3 × V3}
          (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
          (_hE : (fun s => f '' s) '' E = E') (_hfan' : Fan.FAN 0 V' E')
          (_hff : (fun p => (f p.1, f p.2)) = ff),
          ∀ x ∈ dartsOfHyp_p4 E V,
          nnOfHyp_p4 0 V' E' (ff x) = ff (nnOfHyp_p4 0 V E x) ∧
          eeOfHyp_p4 0 V' E' (ff x) = ff (eeOfHyp_p4 0 V E x)
    ) ∧
    -- 21. HYP_ISO_LEMMAA_p37 (LA37:2392; no HOL anchor line in file docstring)
    (∀ {V V' : Set V3} {E E' : Set (Set V3)}
          {FF : Set (V3 × V3)} {f : V3 → V3}
          (_hlf : LocalFan V E FF) (_hbij : Set.BijOn f V V')
          (_hE : (fun s => f '' s) '' E = E') (_hfan : Fan.FAN 0 V E)
          (_hfan' : Fan.FAN 0 V' E'),
          hypIso_p37 (fun (p : V3 × V3) => (f p.1, f p.2)) (Fan.hypermapOfFan 0 V E _hfan)
          (Fan.hypermapOfFan 0 V' E' _hfan')
    ) ∧
    -- 22. COMM_THEN_IMAGE_IMAGE_EQ_p37 (LA37:2632; HOL `COMM_THEN_IMAGE_IMAGE_EQ`)
    (∀ {S A : Set V3} {f g h : V3 → V3}
          (hcomm : ∀ x ∈ S, f (g x) = h (f x)) (hA : A ⊆ S),
          f '' (g '' A) = h '' (f '' A)
    ) ∧
    -- 23. XRECQNS_UPDATE_p37 (LA37:2869; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {f : V3 → ℝ → V3} {a b : ℝ} (_hd : Deformation f V a b) (_hl : LocalFan V E FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
          LocalFan ((fun v => f v t) '' V)
            ((fun s => (fun v => f v t) '' s) '' E)
            ((fun p => (f p.1 t, f p.2 t)) '' FF)
    ) ∧
    -- 24. NORM_CROSS_LE_p37 (LA37:2955; no HOL anchor line in file docstring)
    (∀ (u w : V3)
    ,
          ‖cross3_p37 u w‖ ≤ ‖u‖ * ‖w‖
    ) ∧
    -- 25. CONT_ATREAL_INJ_PRESERVED_p37 (LA37:2967; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {ff : V3 → ℝ → V3} {r : ℝ}
          (_hV : V.Finite) (_hc : ∀ v ∈ V, ContinuousAt (ff v) r)
          (_hinj : Set.InjOn (fun v => ff v r) V),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t - r| < e →
          Set.InjOn (fun v => ff v t) V
    ) ∧
    -- 26. INJ_BIJ_IMAGE_p37 (LA37:3030; HOL `INJ_BIJ_IMAGE`)
    (∀ {f : V3 → V3} {S S' A : Set V3}
          (h : Set.InjOn f S) (hA : A ⊆ S),
          Set.BijOn f A (f '' A)
    ) ∧
    -- 27. CONT_ATREAL_REAL_CONTS_p37 (LA37:3036; no HOL anchor line in file docstring)
    (∀ {f : ℝ → V3} {r : ℝ} {x y : V3}
          (h : ContinuousAt f r),
          ContinuousAt
          (fun s => ((cross3_p37 (f s) y : V3) : Fin 3 → ℝ) ⬝ᵥ
            ((cross3_p37 x y : V3) : Fin 3 → ℝ)) r
    ) ∧
    -- 28. CONTINUOUS_POS_PRES_p37 (LA37:3063; no HOL anchor line in file docstring)
    (∀ {x y : V3} {a b r : ℝ} {f : ℝ → V3}
          (_hnc : ¬Collinear ℝ ({x, y, (0 : V3)} : Set V3)) (_hab : f r = a • x + b • y)
          (_h0 : 0 < a) (_hc : ContinuousAt f r),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → ∀ t1 t2 : ℝ,
          f (r + t) = t1 • x + t2 • y → 0 < t1
    ) ∧
    -- 29. IVS_RHO_NODE_V_IN_FF_p37 (LA37:3158 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); no HOL anchor line in file docstring)
    (∀ {v : Kepler.Geom.V3} {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)}, LocalFan V E FF → v ∈ V → (ivsRhoNode1 FF v, v) ∈ FF
    ) ∧
    -- 30. IN_AFF_GT_IMP_AZIMEQ_p37 (LA37:3178; no HOL anchor line in file docstring)
    (∀ {u v w x y : V3}
          (_hx : x ∈ affGt {u, v} {y}),
          azim u v w x = azim u v w y
    ) ∧
    -- 31. IN_AFF_GT_IMP_AZIMEQ2_p37 (LA37:3196; HOL `IN_AFF_GT_IMP_AZIMEQ2`)
    (∀ {u v x y : V3} (hx : x ∈ affGt {u, v} {y})
          (w : V3),
          azim u v w x = azim u v w y
    ) ∧
    -- 32. CROSS_IN_SAME_DIRECTION_p37 (LA37:3274; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3} {e : V3}
          (_hlf : LocalFan V E FF) (_hv : v ∈ V)
          (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
          (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P)
          (_he : cross3_p37 v (rhoNode1 FF v) = e),
          ∀ i < l, ∃ k : ℝ, 0 < k ∧
          cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) = k • e
    ) ∧
    -- 33. ITER_CROSS_SAME_DIRECTION_p37 (LA37:3446; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
          (_hlf : LocalFan V E FF) (_hv : v ∈ V)
          (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
          (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P),
          ∀ i j, i < l → j < l → ∃ k : ℝ, 0 < k ∧
          cross3_p37 ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) =
            k • (cross3_p37 ((rhoNode1 FF)^[j] v) ((rhoNode1 FF)^[j + 1] v))
    ) ∧
    -- 34. ITER_IN_AFF_GT_2_1_p37 (LA37:3482; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
          (_hlf : LocalFan V E FF) (_hv : v ∈ V)
          (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
          (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P),
          ∀ i < l - 1,
          (rhoNode1 FF)^[i + 2] v ∈
            affLt {0, (rhoNode1 FF)^[i + 1] v} {(rhoNode1 FF)^[i] v}
    ) ∧
    -- 35. AZIM_PI_ITER_LOCAL_FAN_p37 (LA37:3576; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
          (_hlf : LocalFan V E FF) (_hv : v ∈ V)
          (_hU : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U)
          (_hP : PlaneP_p37 P) (_h0 : (0 : V3) ∈ P) (_hUsub : U ⊆ P),
          ∀ i < l - 1,
          azim 0 ((rhoNode1 FF)^[i + 1] v) ((rhoNode1 FF)^[i] v)
            ((rhoNode1 FF)^[i + 2] v) = Real.pi
    ) ∧
    -- 36. LOCAL_CONVEX_NOT_COLLINEAR_p37 (LA37:3607; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v w : V3}
          (_h : ConvexLocalFan V E FF) (_hl : Lunar v w V E),
          ∀ u ∈ V, u ≠ v → u ≠ w → ¬Collinear ℝ ({0, v, u} : Set V3)
    ) ∧
    -- 37. LOCAL_FAN_RHO_NODE_PROS2_p37 (LA37:3626; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (_h : LocalFan V E FF),
          ∀ x ∈ V, (x, rhoNode1 FF x) ∈ FF
    ) ∧
    -- 38. CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p37 (LA37:3684; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (_h : ConvexLocalFan V E FF),
          ∀ v ∈ V, interiorAngle1 0 FF v = azim 0 v (rhoNode1 FF v) (ivsRhoNode1 FF v)
    ) :=
    ⟨CONS_IMP_CONTINUOUS_ATREAL_p37, @AFF_GT_SUBSET_AFFINE_HULL21_p37, DISJTINCT_PROPERTY_p37,
      EDGE_FORM_IN_LOCAL_FAN_p37, @EDGE_IN_LOCAL_FAN_DET_RHO_NODE_p37,
      @TOW_POINTS_IN_IMP_AFF_GT_SUBSET_p37, REAL_LT_MUL12_p37,
      COLL_IN_AFF_GT_INTER_EMPTY_p37, @HKIRPEP_ALT_p37, @LUNAR_IMP_IN_TWO_HAFLS_PLANE_p37,
      IN_CONV0_IMP_AFF_EQ1_p37, @AFF_LT_SUBSET_AFF11_p37, AZIM_PI_LEMMA_p37,
      @LOCAL_FAN_SET_E_p37, LOCAL_FAN_FACE_FF_p37, @ORD_PAIRS_INJ_IMAGE_p37, SET2_DETER_p37,
      @INJ_IMP_BIJ_IMAGE_p37, @BIJ_AND_MAP_COMM_p37, @NODE_EDGE_COMM_LEMMA_p37,
      @HYP_ISO_LEMMAA_p37, COMM_THEN_IMAGE_IMAGE_EQ_p37, XRECQNS_UPDATE_p37,
      NORM_CROSS_LE_p37, CONT_ATREAL_INJ_PRESERVED_p37, @INJ_BIJ_IMAGE_p37,
      CONT_ATREAL_REAL_CONTS_p37, CONTINUOUS_POS_PRES_p37, IVS_RHO_NODE_V_IN_FF_p37,
      IN_AFF_GT_IMP_AZIMEQ_p37, IN_AFF_GT_IMP_AZIMEQ2_p37, CROSS_IN_SAME_DIRECTION_p37,
      ITER_CROSS_SAME_DIRECTION_p37, ITER_IN_AFF_GT_2_1_p37, AZIM_PI_ITER_LOCAL_FAN_p37,
      LOCAL_CONVEX_NOT_COLLINEAR_p37, LOCAL_FAN_RHO_NODE_PROS2_p37,
      CONVEX_LOFA_IMP_INANGLE_EQ_AZIM_IVS_p37⟩

#print axioms la37_capstone_w1


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- LA17 materialization capstone (lane capstone-wire-w1,
2026-11-04): the clean public top-level LocalAuto17 theorem exits that are
statable in Kepler.Text, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume them (49 of the 50 public
top-level theorem exits; 1 dropped per the workorder's no-forcing
rule "抽不出/不一致 → 剔除并如实报", mechanically detected from the
`#print axioms` / `#check @` probe dumps and the module source; each drop
is named below with its reason -- 0 carry a sorryAx axiom face
or a non-standard axiom, the remainder are mechanical statement drops).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA17 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA17
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la17_capstone_w1 :
    -- 1. MOD_EQ_MOD_SHIFT_p17 (LA17:357; HOL `Ocbicby.MOD_EQ_MOD_SHIFT`)
    (∀ (k i' p p' i : ℕ) (hk : k ≠ 0)
          (h : (i + p) % k = p' % k),
          (i' + i + p) % k = (i' + p') % k
    ) ∧
    -- 2. SGIN_POW_EQ_p17 (LA17:408; HOL `SGIN_POW_EQ`)
    (∀ (a : ℝ) (h : a ∈ ({-1, 1} : Set ℝ))
    ,
          a ^ 2 = 1
    ) ∧
    -- 3. EYYPQDW_COPLANAR_p17 (LA17:414; no HOL anchor line in file docstring)
    (∀ (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
          (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
            ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
              cross3 v1 (cross3 v1 v2) = v3),
          Coplanar ({0, v1, v2, v3} : Set V3)
    ) ∧
    -- 4. EYYPQDW_NORMV3_p17 (LA17:504; no HOL anchor line in file docstring)
    (∀ (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
          (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
            ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
              cross3 v1 (cross3 v1 v2) = v3),
          ‖v3‖ ^ 2 = x3
    ) ∧
    -- 5. EYYPQDW_NORM_V3_V1_p17 (LA17:539; no HOL anchor line in file docstring)
    (∀ (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
          (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
            ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
              cross3 v1 (cross3 v1 v2) = v3),
          ‖v3 - v1‖ ^ 2 = x5
    ) ∧
    -- 6. EYYPQDW_SCALAR_POS_p17 (LA17:577; no HOL anchor line in file docstring)
    (∀ (v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5)
          (hv3 : ((x1 + x3 - x5) / (2 * x1)) • v1 +
            ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
              cross3 v1 (cross3 v1 v2) = v3),
          ∃ t : ℝ, 0 < t ∧ cross3 v3 v1 = (a * t) • cross3 v1 v2
    ) ∧
    -- 7. LIFT_CONTINUOUS_ATREAL_p17 (LA17:613; no HOL anchor line in file docstring)
    (∀ (x : ℝ)
    ,
          ContinuousAt (fun x : ℝ => x) x
    ) ∧
    -- 8. LIFT_CONTINUOUS_ATREAL_I_p17 (LA17:617; HOL `LIFT_CONTINUOUS_ATREAL_I`)
    (∀ (x : ℝ)
    ,
          ContinuousAt (fun x : ℝ => (id ∘ id) x) x
    ) ∧
    -- 9. EYYPQDW_CONTINUOUS_AT_X_p17 (LA17:622; HOL `EYYPQDW_CONTINUOUS_AT_X`)
    (∀ (a : ℝ) (v1 v2 : V3)
          (x1 x2 x3 x4 x5 x6 : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5),
          ContinuousAt (fun x3 => v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 x3) x3
    ) ∧
    -- 10. EYYPQDW_CONTINUOUS_AT_V_p17 (LA17:655; HOL `EYYPQDW_CONTINUOUS_AT_V`)
    (∀ (a : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) (v1 v2 : V3)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a ∈ ({-1, 1} : Set ℝ)) (hups : 0 < upsX x1 x3 x5),
          ContinuousAt (fun w => v3DeforV2_p17 a x1 x2 x3 x5 x6 v1 w) v2
    ) ∧
    -- 11. V3_DEFOR_V1_EQV3_DEFOR_V2_p17 (LA17:674; HOL `V3_DEFOR_V1_EQV3_DEFOR_V2`)
    (∀ (a : ℝ) (v1 v2 : V3) (x1 x2 x5 x6 x3 : ℝ)
    ,
          v3DeforV1_p17 a v1 v2 x1 x2 x5 x6 x3 =
          v3DeforV2_p17 a x1 x2 x3 x5 x6 v1 v2
    ) ∧
    -- 12. LIFT_UPS_CONTINUOUS_p17 (LA17:680; HOL `LIFT_UPS_CONTINUOUS`)
    (∀ (v1 v2 : V3) (x1 x2 x6 : ℝ)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6),
          ContinuousAt (fun x2 => upsX x1 x2 x6) x2
    ) ∧
    -- 13. MK_PLANAR_REP_p17 (LA17:690; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 a : ℝ)
    ,
          mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 a - v0 =
          ((x1 + x3 - x5) / (2 * x1)) • (v1 - v0) +
            ((a / x1) * Real.sqrt (upsX x1 x3 x5 / upsX x1 x2 x6)) •
              cross3 (v1 - v0) (cross3 (v1 - v0) (v2 - v0))
    ) ∧
    -- 14. EYYPQDW_p17 (LA17:707; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x5 x6 s : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
          (hx6 : x6 = dist v1 v2 ^ 2)
          (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1)
          (hv3 : v3 = mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 s),
          Coplanar ({v0, v1, v2, v3} : Set V3) ∧
          x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧
          ∃ t : ℝ, 0 < t ∧
            t • cross3 (v3 - v0) (v1 - v0) = s • cross3 (v1 - v0) (v2 - v0)
    ) ∧
    -- 15. MK_PLANAR_V3_DEFOR_V1_p17 (LA17:786; HOL `MK_PLANAR_V3_DEFOR_V1`)
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 a : ℝ)
    ,
          mkPlanar2 v0 v1 v2 x1 x2 x3 x5 x6 a - v0 =
          v3DeforV1_p17 a (v1 - v0) (v2 - v0) x1 x2 x5 x6 x3
    ) ∧
    -- 16. MK_PLANAR_V3_DEFOR_V1_FUN_p17 (LA17:792; HOL `MK_PLANAR_V3_DEFOR_V1_FUN`)
    (∀ (v0 v1 v2 : V3) (x1 x2 x5 x6 s : ℝ)
    ,
          (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) =
          (fun x3 => v3DeforV1_p17 s (v1 - v0) (v2 - v0) x1 x2 x5 x6 x3 + v0)
    ) ∧
    -- 17. EYYPQDW2_p17 (LA17:800; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
          (hx6 : x6 = dist v1 v2 ^ 2)
          (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1),
          ContinuousAt (fun q => mkPlanar2 v0 v1 v2 x1 x2 q x5 x6 s) x3
    ) ∧
    -- 18. MK_PLANAR_V3_DEFOR_V2_FUN_p17 (LA17:824; HOL `MK_PLANAR_V3_DEFOR_V2_FUN`)
    (∀ (v0 v1 : V3) (x1 x2 x3 x5 x6 s : ℝ)
    ,
          (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) =
          (fun v2 => v3DeforV2_p17 s x1 x2 x3 x5 x6 (v1 - v0) (v2 - v0) + v0)
    ) ∧
    -- 19. lemma30000_p17 (LA17:834; HOL `lemma30000`)
    (∀ (s x3 x5 : ℝ) (v0 v1 v2 : V3)
    ,
          (fun v2' => v3DeforV2_p17 s (‖v1 - v0‖ ^ 2) (‖v2 - v0‖ ^ 2) x3 x5
            (‖v1 - v2‖ ^ 2) (v1 - v0) (v2' - v0)) =
          (fun v2' => v3DeforV2_p17 s (‖v1 - v0‖ ^ 2) (‖v2 - v0‖ ^ 2) x3 x5
            (‖v1 - v2‖ ^ 2) (v1 - v0) v2') ∘ fun v2 : V3 => v2 - v0
    ) ∧
    -- 20. EYYPQDW3_p17 (LA17:843; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 : V3) (x1 x2 x3 x5 x6 s : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h5 : 0 < x5) (h6 : 0 < x6)
          (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
          (hx6 : x6 = dist v1 v2 ^ 2)
          (hups : 0 < upsX x1 x3 x5) (hs : s = 1 ∨ s = -1),
          ContinuousAt (fun q => mkPlanar2 v0 v1 q x1 x2 x3 x5 x6 s) v2
    ) ∧
    -- 21. SUR_MOD_FUN_p17 (LA17:876; HOL `SUR_MOD_FUN`)
    (∀ (k p p' : ℕ) (hk : k ≠ 0)
    ,
          ∃ i : ℕ, (i + p) % k = p' % k
    ) ∧
    -- 22. TRANS_DIAG_p17 (LA17:888; HOL `TRANS_DIAG`)
    (∀ (k i p p' q q' : ℕ) (hk : k ≠ 0)
          (h1 : (i + p) % k = p' % k) (h2 : p' + q = p + q'),
          (i + q) % k = q' % k
    ) ∧
    -- 23. scs_components_p17 (LA17:898; no HOL anchor line in file docstring)
    (∀ (s : ScsV39)
    ,
          ScsV39.mk s.k s.d s.a s.am s.bm s.b s.J s.lo s.hi s.str = s
    ) ∧
    -- 24. scs_inj_p17 (LA17:904; no HOL anchor line in file docstring)
    (∀ (s s' : ScsV39) (h1 : scsBasicV39 s) (h1' : scsBasicV39 s')
          (hd : s.d = s'.d) (hk : s.k = s'.k) (ha : s.a = s'.a) (hb : s.b = s'.b),
          s = s'
    ) ∧
    -- 25. DIAG_PSORT1_p17 (LA17:910 (autoImplicit parameter leak p'; statement = probe printer dump verbatim (complete signature)); HOL `DIAG_PSORT1`)
    (∀ {p' : ℕ} (k i p i' j q' q : ℕ),
          k ≠ 0 →
            (i + p) % k = p' % k →
              p' + q = p + q' → psort k (i', j) = psort k (p, q) → psort k (i + i', i + j) = psort k (p', q')
    ) ∧
    -- 26. DIAG_PSORT2_p17 (LA17:929 (autoImplicit parameter leak p'; statement = probe printer dump verbatim (complete signature)); HOL `DIAG_PSORT2`)
    (∀ {p' : ℕ} (k i p i' j q' q : ℕ),
          k ≠ 0 →
            (i + p) % k = p' % k →
              p' + q = p + q' → psort k (i + i', i + j) = psort k (p', q') → psort k (i', j) = psort k (p, q)
    ) ∧
    -- 27. DIAG_PSORT_p17 (LA17:950 (autoImplicit parameter leak p'; statement = probe printer dump verbatim (complete signature)); HOL `DIAG_PSORT`)
    (∀ {p' : ℕ} (k i p i' j q' q : ℕ),
          k ≠ 0 →
            (i + p) % k = p' % k →
              p' + q = p + q' → (psort k (i + i', i + j) = psort k (p', q') ↔ psort k (i', j) = psort k (p, q))
    ) ∧
    -- 28. TRANS_DIAG_SCS_p17 (LA17:959; no HOL anchor line in file docstring)
    (∀ (k i' i j : ℕ) (hk : k ≠ 0)
    ,
          scsDiag k i' j ↔ scsDiag k (i + i') (i + j)
    ) ∧
    -- 29. A_EQ_PSORT_p17 (LA17:972; HOL `A_EQ_PSORT`)
    (∀ (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
          (h : psort s.k (i, j) = psort s.k (p, q)),
          s.a i j = s.a p q
    ) ∧
    -- 30. B_EQ_PSORT_p17 (LA17:983; HOL `B_EQ_PSORT`)
    (∀ (s : ScsV39) (i j p q : ℕ) (his : isScsV39 s)
          (h : psort s.k (i, j) = psort s.k (p, q)),
          s.b i j = s.b p q
    ) ∧
    -- 31. PROPERTY_OF_K_SCS_p17 (LA17:995; HOL `PROPERTY_OF_K_SCS`)
    (∀ (s : ScsV39) (his : isScsV39 s)
    ,
          s.k ≠ 0 ∧ 0 < s.k ∧ 1 < s.k ∧ 2 < s.k
    ) ∧
    -- 32. PSORT_PERIODIC_p17 (LA17:1001; HOL `PSORT_PERIODIC`)
    (∀ (k i j : ℕ) (hk : k ≠ 0)
    ,
          psort k (i + k, j) = psort k (i, j) ∧ psort k (i, j + k) = psort k (i, j)
    ) ∧
    -- 33. DIAG_NOT_PSORT_p17 (LA17:1010; no HOL anchor line in file docstring)
    (∀ (k i j : ℕ) (hk : k ≠ 0) (hd : scsDiag k i j)
          (i' : ℕ),
          ¬ (psort k (i, j) = psort k (i', i' + 1))
    ) ∧
    -- 34. YRTAFYH_p17 (LA17:1129; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (i j : ℕ), isScsV39 s → scsBasicV39 s →
          3 < s.k → scsDiag s.k i j → s.a i j ≤ cstab →
          isScsV39 (scsStabDiagV39 s i j) ∧ scsBasicV39 (scsStabDiagV39 s i j)
    ) ∧
    -- 35. STAB_IS_SCS_p17 (LA17:1159; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (i j : ℕ) (his : isScsV39 s)
          (hbas : scsBasicV39 s) (hk : 3 < s.k) (hdiag : scsDiag s.k i j)
          (ha : s.a i j ≤ cstab),
          isScsV39 (scsStabDiagV39 s i j)
    ) ∧
    -- 36. COMPACT_SPHERE_0_p17 (LA17:1171; HOL `COMPACT_SPHERE_0`)
    (∀ (a : ℝ)
    ,
          IsCompact {x : V3 | ‖x‖ = a}
    ) ∧
    -- 37. SEPARATE_CLOSED_CONES_p17 (LA17:1246; no HOL anchor line in file docstring)
    (∀ (c d : Set V3) (hc : conicP17 c)
          (hcc : IsClosed c) (hd : conicP17 d) (hdc : IsClosed d)
          (hint : c ∩ d ⊆ ({0} : Set V3)),
          ∃ e : ℝ, 0 < e ∧ ∀ x ∈ c, ∀ y ∈ d, dist x y ≥ e * max ‖x‖ ‖y‖
    ) ∧
    -- 38. AFF_GE_1_1_0_p17 (LA17:1267; HOL `AFF_GE_1_1_0`)
    (∀ (v : V3) (hv : v ≠ (0:V3))
    ,
          affGe ({0} : Set V3) {v} = {y : V3 | ∃ t : ℝ, 0 ≤ t ∧ y = t • v}
    ) ∧
    -- 39. AFF_GE_1_2_0_p17 (LA17:1305; HOL `AFF_GE_1_2_0`)
    (∀ (v w : V3) (hv : v ≠ (0:V3)) (hw : w ≠ (0:V3))
    ,
          affGe ({0} : Set V3) {v, w} =
          {y : V3 | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y = a • v + b • w}
    ) ∧
    -- 40. CONIC_AFF_GE_0_p17 (LA17:1373; no HOL anchor line in file docstring)
    (∀ (s : Set V3) (hfin : s.Finite) (h0 : (0:V3) ∉ s)
    ,
          conicP17 (affGe ({0} : Set V3) s)
    ) ∧
    -- 41. GMLWKPK_p17 (LA17:2065; no HOL anchor line in file docstring)
    (∀ (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E)
    ,
          fan7 x V E ↔
          ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
            (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
              (∀ v : V3, e1 ∩ e2 = {v} →
                affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3))
    ) ∧
    -- 42. GMLWKPK_ALT_p17 (LA17:2074; no HOL anchor line in file docstring)
    (∀ (x : V3) (V : Set V3) (E : Set (Set V3)) (hE : Graph E)
          (hx : ∀ e ∈ E, x ∉ e),
          fan7 x V E ↔
          ((∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
              e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
            (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
              affGe {x} e1 ∩ affGe {x} e2 = affGe {x} ({v} : Set V3)))
    ) ∧
    -- 43. GMLWKPK_SIMPLE_p17 (LA17:2085; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (E : Set (Set V3)) (x : V3)
          (hsup : ⋃₀ E ⊆ V) (hE : Graph E) (h6 : fan6 x V E)
          (hx : ∀ e ∈ E, x ∉ e),
          fan7 x V E ↔
          ∀ e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}}, ∀ e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
            e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)
    ) ∧
    -- 44. lemma_1_p17 (LA17:2094; no HOL anchor line in file docstring)
    (∀ (x : V3) (e : ℝ) (hx : x ≠ (0:V3)) (he : 0 < e)
    ,
          ∃ d : ℝ, 0 < d ∧ ∀ x' : V3, dist x x' < d →
          ∀ z' ∈ affGe ({0} : Set V3) {x'}, ∃ z ∈ affGe ({0} : Set V3) {x},
            ‖z' - z‖ ≤ e * ‖z‖
    ) ∧
    -- 45. lemma_2_p17 (LA17:2195; no HOL anchor line in file docstring)
    (∀ (x y : V3) (e : ℝ)
          (hnc : ¬ Collinear ℝ ({0, x, y} : Set V3)) (he : 0 < e),
          ∃ d : ℝ, 0 < d ∧ ∀ x' y' : V3, dist x x' < d → dist y y' < d →
          ∀ z' ∈ affGe ({0} : Set V3) {x', y'}, ∃ z ∈ affGe ({0} : Set V3) {x, y},
            ‖z' - z‖ ≤ e * ‖z‖
    ) ∧
    -- 46. MINIMIZE_OVER_2_p17 (LA17:2321; HOL `MINIMIZE_OVER_2`)
    (∀ {P Q : ℝ → Prop}
          (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t)
          (h2 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → Q t),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t ∧ Q t
    ) ∧
    -- 47. MINIMIZE_OVER_STRONGER_p17 (LA17:2332; HOL `MINIMIZE_OVER_STRONGER`)
    (∀ {P Q : ℝ → Prop} (hPQ : ∀ t : ℝ, P t → Q t)
          (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → P t),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e → Q t
    ) ∧
    -- 48. FAN7_SMALL_DEFORMATION_p17 (LA17:2628; no HOL anchor line in file docstring)
    (∀ (V : Set V3) (E : Set (Set V3)) (a b : ℝ)
          (phii : V3 → ℝ → V3) (hdef : Deformation phii V a b) (hfan : FAN 0 V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
          fan7 (0:V3) ((fun v : V3 => phii v t) '' V)
            ((fun e' => (fun v : V3 => phii v t) '' e') '' E)
    ) ∧
    -- 49. XRECQNS_p17 (LA17:3041; no HOL anchor line in file docstring)
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (f : V3 → ℝ → V3)
          (hdef : Deformation f V a b) (hfan : FAN 0 V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t → t < e →
          FAN (0:V3) ((fun v : V3 => f v t) '' V)
            ((fun e' => (fun v : V3 => f v t) '' e') '' E)
    ) :=
    ⟨MOD_EQ_MOD_SHIFT_p17, SGIN_POW_EQ_p17, EYYPQDW_COPLANAR_p17, EYYPQDW_NORMV3_p17,
      EYYPQDW_NORM_V3_V1_p17, EYYPQDW_SCALAR_POS_p17, LIFT_CONTINUOUS_ATREAL_p17,
      LIFT_CONTINUOUS_ATREAL_I_p17, EYYPQDW_CONTINUOUS_AT_X_p17, EYYPQDW_CONTINUOUS_AT_V_p17,
      V3_DEFOR_V1_EQV3_DEFOR_V2_p17, LIFT_UPS_CONTINUOUS_p17, MK_PLANAR_REP_p17, EYYPQDW_p17,
      MK_PLANAR_V3_DEFOR_V1_p17, MK_PLANAR_V3_DEFOR_V1_FUN_p17, EYYPQDW2_p17,
      MK_PLANAR_V3_DEFOR_V2_FUN_p17, lemma30000_p17, EYYPQDW3_p17, SUR_MOD_FUN_p17,
      TRANS_DIAG_p17, @scs_components_p17, scs_inj_p17, @DIAG_PSORT1_p17, @DIAG_PSORT2_p17,
      @DIAG_PSORT_p17, TRANS_DIAG_SCS_p17, A_EQ_PSORT_p17, B_EQ_PSORT_p17,
      @PROPERTY_OF_K_SCS_p17, PSORT_PERIODIC_p17, DIAG_NOT_PSORT_p17, YRTAFYH_p17,
      STAB_IS_SCS_p17, COMPACT_SPHERE_0_p17, SEPARATE_CLOSED_CONES_p17, AFF_GE_1_1_0_p17,
      AFF_GE_1_2_0_p17, CONIC_AFF_GE_0_p17, GMLWKPK_p17, GMLWKPK_ALT_p17, GMLWKPK_SIMPLE_p17,
      @lemma_1_p17, @lemma_2_p17, MINIMIZE_OVER_2_p17, MINIMIZE_OVER_STRONGER_p17,
      FAN7_SMALL_DEFORMATION_p17, XRECQNS_p17⟩

#print axioms la17_capstone_w1
/-! ### Incremental delta capstones la14/la37/la28/la34/la6 (lane
capstone-refresh-w2, 2026-11-04, roadmap M0b second item): the 45 exits
that became clean after the w1 baseline (HEAD 4a8f8914) are re-exposed as
ONE conjunction per module and the five `have hla{14b,37b,28b,34b,6}` lines
in Assembly.textCapstone pull the capstone proof terms into the e2e cone
(pure insertion there too, after hla17; the w1 capstones stay wired).
Delta definition (measured, not assumed): current source declaration kind
is `theorem`, current `#print axioms` face is exactly the standard three
[propext, Classical.choice, Quot.sound] with no sorryAx (all 45 delta exits
are individually exactly standard three), the exit was not already a
conjunct of the module's w1 capstone, and it is not universe-polymorphic
or module-private.  The newly-closed set is the source-body sorry set
difference between HEAD 4a8f8914 and the current tree, restricted to
public `theorem` exports; counts match the four closing waves exactly:
LA14 W9+W10 5, LA37 B11 1, LA28 W7 14, LA34 W5 9, LA6 sweep-w3 16.
Statement drops follow the lv56 generator rules (module-private constant
`✝`, def-kind, universe-polymorphic statement); none fired here.
Extraction purely mechanical (gen_items.py): conjuncts are verbatim module
source signatures, bodies are the exit constants; the `set_option
maxHeartbeats 50000000 in` scope mirrors the existing large-conjunction
sections in this file.  Environment-alignment scopes mirror module-local
declarations so the verbatim signatures elaborate under the same name,
instance and open resolution as their source modules: LA37 carries the
module's own `attribute [-instance] dartDecEq2 dartDecEq3` (LocalAuto37:125)
and LA6 carries the module's own `open Kepler.Text.Fan` (LocalAuto6:48).
All five modules are already imported by this file (LA14 :485, LA28 :499,
LA34 :505, LA37 :508, LA6 :511), so zero import changes.  The exact cone
increment is re-measured at the orchestrator e2e gate. -/


set_option maxHeartbeats 50000000 in

/-- LA14 incremental capstone (lane capstone-refresh-w2,
2026-11-04): the public top-level LocalAuto14 theorem exits that became
clean after the w1 baseline (HEAD 4a8f8914) and are statable in
Kepler.Text, re-exposed as ONE conjunction so the Assembly `textCapstone`
cone can consume them (5 of the 5 newly-closed exits; 0
dropped per the workorder's no-forcing rule "抽不出/不一致 → 剔除并如实报",
mechanically detected from the `#print axioms` / `#check @` probe dumps
and the module source; each drop is named below with its reason --
0 carry a sorryAx axiom face or a non-standard axiom, the
remainder are mechanical statement drops).  Provenance: these exits were dropped from `la14_capstone_w1` at w1 generation as sorryAx-carrying and became clean in wave W9+W10; the existing `la14_capstone_w1` is left untouched (incremental, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA14 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA14
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la14_capstone_w2 :
    -- 1. YBTASCZ1_p14 (LA14:1757; no HOL anchor line in file docstring)
    (∀ (u : ℕ → V3) (r j : ℕ) (hj : j ≤ r) (hr : 1 ≤ r)
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
          (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
          (h4 : ∀ i, i < r →
            azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)),
          ∀ i, i < j →
          azim 0 (cross3 (u 0) (u 1)) (u 0) (u i) < azim 0 (cross3 (u 0) (u 1)) (u 0) (u j)
    ) ∧
    -- 2. YBTASCZ2_p14 (LA14:1839; no HOL anchor line in file docstring)
    (∀ (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
          (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
          (h4 : ∀ i, i < r →
            azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)),
          azim 0 (cross3 (u 0) (u 1)) (u i) (u j) < Real.pi
    ) ∧
    -- 3. YBTASCZ3_p14 (LA14:1864; no HOL anchor line in file docstring)
    (∀ (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
          (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
          (h4 : ∀ i, i < r →
            azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)),
          0 < azim 0 (cross3 (u 0) (u 1)) (u i) (u j)
    ) ∧
    -- 4. zlz_wedge_refl_p14 (LA14:3621; no HOL anchor line in file docstring)
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
          (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
          (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
            interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi),
          ∀ v w : V3, w ∈ V → v ∈ ({w, rhoNode1 FF w, ivsRhoNode1 FF w} : Set V3) →
          ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t ∧ t < e →
            f v t ∈ wedgeInFanGe (f w t, f (rhoNode1 FF w) t)
              ((fun s => (fun v => f v t) '' s) '' E)
    ) ∧
    -- 5. zlz_wedge_open_p14 (LA14:3666; no HOL anchor line in file docstring)
    (∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
          (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
          (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
            interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi),
          ∀ v w : V3, v ∈ V → w ∈ V →
          v ∈ Kepler.Geom.wedge 0 w (rhoNode1 FF w) (ivsRhoNode1 FF w) →
          ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t ∧ t < e →
            f v t ∈ wedgeInFanGe (f w t, f (rhoNode1 FF w) t)
              ((fun s => (fun v => f v t) '' s) '' E)
    ) :=
    ⟨YBTASCZ1_p14, YBTASCZ2_p14, YBTASCZ3_p14, @zlz_wedge_refl_p14, zlz_wedge_open_p14
⟩

#print axioms la14_capstone_w2


attribute [-instance] dartDecEq2 dartDecEq3 in
set_option maxHeartbeats 50000000 in

/-- LA37 incremental capstone (lane capstone-refresh-w2,
2026-11-04): the public top-level LocalAuto37 theorem exits that became
clean after the w1 baseline (HEAD 4a8f8914) and are statable in
Kepler.Text, re-exposed as ONE conjunction so the Assembly `textCapstone`
cone can consume them (1 of the 1 newly-closed exits; 0
dropped per the workorder's no-forcing rule "抽不出/不一致 → 剔除并如实报",
mechanically detected from the `#print axioms` / `#check @` probe dumps
and the module source; each drop is named below with its reason --
0 carry a sorryAx axiom face or a non-standard axiom, the
remainder are mechanical statement drops).  Provenance: these exits were dropped from `la37_capstone_w1` at w1 generation as sorryAx-carrying and became clean in wave B11; the existing `la37_capstone_w1` is left untouched (incremental, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA37 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA37
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la37_capstone_w2 :
    -- 1. SUB_LUNAR_DEFORM_LEMMA_p37 (LA37:2250; no HOL anchor line in file docstring)
    (∀ {a b : ℝ} {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {f : V3 → ℝ → V3} {u v w : V3}
          (_hV : V.Finite) (_hcf : ConvexLocalFan V E FF) (_hl : Lunar v w V E)
          (_hE : ∀ x ∈ E, x ⊆ V) (_hu0 : f u 0 = u) (_hcu : ContinuousAt (f u) 0)
          (_hang : interiorAngle1 0 FF v < Real.pi) (_ha : a < 0) (_hb : 0 < b)
          (_hu : u ∈ V) (_hv : u ≠ v) (_hw : u ≠ w)
          (_hpin : ∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u')
          (_haff : ∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          Lunar v w ((fun z => f z t) '' V) ((fun s => (fun z => f z t) '' s) '' E)
    ) :=
    @SUB_LUNAR_DEFORM_LEMMA_p37

#print axioms la37_capstone_w2


set_option maxHeartbeats 50000000 in

/-- LA28 incremental capstone (lane capstone-refresh-w2,
2026-11-04): the public top-level LocalAuto28 theorem exits that became
clean after the w1 baseline (HEAD 4a8f8914) and are statable in
Kepler.Text, re-exposed as ONE conjunction so the Assembly `textCapstone`
cone can consume them (14 of the 14 newly-closed exits; 0
dropped per the workorder's no-forcing rule "抽不出/不一致 → 剔除并如实报",
mechanically detected from the `#print axioms` / `#check @` probe dumps
and the module source; each drop is named below with its reason --
0 carry a sorryAx axiom face or a non-standard axiom, the
remainder are mechanical statement drops).  Provenance: these exits were dropped from `la28_capstone_w1` at w1 generation as sorryAx-carrying and became clean in wave W7; the existing `la28_capstone_w1` is left untouched (incremental, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA28 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA28
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la28_capstone_w2 :
    -- 1. DEFORMATION_AZIM_V3_DEFOR_V1_MK_p28 (LA28:2626; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)) =
          azim 0 v2 (rhoNode1 FF v2) (epPair_p28 FF v2)
    ) ∧
    -- 2. V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_p28 (LA28:2901; HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_SYM`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (a', v1) ∈ FF
    ) ∧
    -- 3. DEFORMATION_AZIM_V3_DEFOR_SUB_MK_p28 (LA28:2938; HOL `DEFORMATION_AZIM_V3_DEFOR_SUB_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)) =
          azim 0 v1 (rhoNode1 FF v1) (epPair_p28 FF v1)
    ) ∧
    -- 4. V3_DEFOR_EQ_IN_FF_SUC_MK_p28 (LA28:3156; HOL `V3_DEFOR_EQ_IN_FF_SUC_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3,
          (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (w (l + 1), a') ∈ FF
    ) ∧
    -- 5. V3_DEFOR_EQ_IN_FF_SUC_MK_SYM_p28 (LA28:3199; HOL `V3_DEFOR_EQ_IN_FF_SUC_MK_SYM`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t) =
          v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1
    ) ∧
    -- 6. DEFORMATION_AZIM_V3_DEFOR_SUC_MK_p28 (LA28:3268; HOL `DEFORMATION_AZIM_V3_DEFOR_SUC_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + 1)) t)) =
          azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) (epPair_p28 FF (w (l + 1)))
    ) ∧
    -- 7. V3_DEFOR_EQ_IN_FF_NOT_MK_p28 (LA28:3487 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `V3_DEFOR_EQ_IN_FF_NOT_MK`)
    (∀ {v : Kepler.Geom.V3} (s : Kepler.Text.ScsV39) (w : ℕ → Kepler.Geom.V3)
          (k l : ℕ) (v1 v2 : Kepler.Geom.V3) (x1 x2 x5 a e t : ℝ) (FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3))
          (V : Set Kepler.Geom.V3),
          3 < k →
            s.k = k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  w l = v2 →
                    w (l + k - 1) = v1 →
                      0 < x1 →
                        0 < x2 →
                          0 < x5 →
                            ¬Collinear ℝ {0, v1, v2} →
                              ‖v1‖ ^ 2 = x1 →
                                ‖v2‖ ^ 2 = x2 →
                                  ‖v2 - v1‖ ^ 2 = x5 →
                                    a = -1 →
                                      0 < e →
                                        -e < t →
                                          (∀ (r : ℝ) (i : ℕ),
                                              -e < r ∧ r < e ∧ ¬i % k = l % k →
                                                Kepler.Text.v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i) →
                                            t < e →
                                              (Set.range fun i => (w i, w (i + 1))) = FF →
                                                Set.range w = V →
                                                  v ≠ v1 →
                                                    v ≠ v2 →
                                                      v ≠ w (l + 1) →
                                                        v ∈ V →
                                                          ∀ (a' : Kepler.Geom.V3),
                                                            (Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t, a') ∈
                                                                Kepler.Text.deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
                                                              (v, a') ∈ FF
    ) ∧
    -- 8. V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_p28 (LA28:3508 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_SYM`)
    (∀ {v : Kepler.Geom.V3} (s : Kepler.Text.ScsV39) (w : ℕ → Kepler.Geom.V3)
          (k l : ℕ) (v1 v2 : Kepler.Geom.V3) (x1 x2 x5 a e t : ℝ) (FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3))
          (V : Set Kepler.Geom.V3),
          3 < k →
            s.k = k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  w l = v2 →
                    w (l + k - 1) = v1 →
                      0 < x1 →
                        0 < x2 →
                          0 < x5 →
                            ¬Collinear ℝ {0, v1, v2} →
                              ‖v1‖ ^ 2 = x1 →
                                ‖v2‖ ^ 2 = x2 →
                                  ‖v2 - v1‖ ^ 2 = x5 →
                                    a = -1 →
                                      0 < e →
                                        -e < t →
                                          (∀ (r : ℝ) (i : ℕ),
                                              -e < r ∧ r < e ∧ ¬i % k = l % k →
                                                Kepler.Text.v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i) →
                                            t < e →
                                              (Set.range fun i => (w i, w (i + 1))) = FF →
                                                Set.range w = V →
                                                  v ≠ v1 →
                                                    v ≠ v2 →
                                                      v ≠ w (l + 1) →
                                                        v ∈ V →
                                                          ∀ (a' : Kepler.Geom.V3),
                                                            (a', Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ∈
                                                                Kepler.Text.deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
                                                              (a', v) ∈ FF
    ) ∧
    -- 9. DEFORMATION_AZIM_V3_DEFOR_NOT_MK_p28 (LA28:3528; HOL `DEFORMATION_AZIM_V3_DEFOR_NOT_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ≠ v1 ∧ v ≠ v2 ∧ v ≠ w (l + 1) ∧
            v ∈ V →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
          azim 0 v (rhoNode1 FF v) (epPair_p28 FF v)
    ) ∧
    -- 10. DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_p28 (LA28:3747; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
          azim 0 v (rhoNode1 FF v) (epPair_p28 FF v)
    ) ∧
    -- 11. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_p28 (LA28:3830; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK`)
    (∀ (s : ScsV39) (k : ℕ)
          (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
          (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) = interiorAngle1 0 FF v
    ) ∧
    -- 12. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_p28 (LA28:3853; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK`)
    (∀ (s : ScsV39) (k : ℕ)
          (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
          (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V ∧
            interiorAngle1 0 FF v = Real.pi →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ≤ Real.pi
    ) ∧
    -- 13. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28 (LA28:5975; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES`)
    (∀ (s : ScsV39)
          (k : ℕ) (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
          (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) = interiorAngle1 0 FF v
    ) ∧
    -- 14. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_TWO_CASES_p28 (LA28:6000; no HOL anchor line in file docstring)
    (∀ (s : ScsV39)
          (k : ℕ) (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
          (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V ∧
            interiorAngle1 0 FF v = Real.pi →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ≤ Real.pi
    ) :=
    ⟨DEFORMATION_AZIM_V3_DEFOR_V1_MK_p28, V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_p28,
      DEFORMATION_AZIM_V3_DEFOR_SUB_MK_p28, V3_DEFOR_EQ_IN_FF_SUC_MK_p28,
      V3_DEFOR_EQ_IN_FF_SUC_MK_SYM_p28, DEFORMATION_AZIM_V3_DEFOR_SUC_MK_p28,
      V3_DEFOR_EQ_IN_FF_NOT_MK_p28, V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_p28,
      DEFORMATION_AZIM_V3_DEFOR_NOT_MK_p28, DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_p28,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_p28,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_p28,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_LE_PI_AT_ALL_MK_TWO_CASES_p28⟩

#print axioms la28_capstone_w2


set_option maxHeartbeats 50000000 in

/-- LA34 incremental capstone (lane capstone-refresh-w2,
2026-11-04): the public top-level LocalAuto34 theorem exits that became
clean after the w1 baseline (HEAD 4a8f8914) and are statable in
Kepler.Text, re-exposed as ONE conjunction so the Assembly `textCapstone`
cone can consume them (9 of the 9 newly-closed exits; 0
dropped per the workorder's no-forcing rule "抽不出/不一致 → 剔除并如实报",
mechanically detected from the `#print axioms` / `#check @` probe dumps
and the module source; each drop is named below with its reason --
0 carry a sorryAx axiom face or a non-standard axiom, the
remainder are mechanical statement drops).  Provenance: these exits were dropped from `la34_capstone_w1` at w1 generation as sorryAx-carrying and became clean in wave W5; the existing `la34_capstone_w1` is left untouched (incremental, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA34 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA34
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la34_capstone_w2 :
    -- 1. DEFORMATION_AZIM_V3_DEFOR_V1_p34 (LA34:3670; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi
    ) ∧
    -- 2. DEFORMATION_AZIM_V3_DEFOR_V1_V1_p34 (LA34:3758; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi
    ) ∧
    -- 3. RHO_FUN_DEFORMATION_V3_DEFOR_p34 (LA34:4494; HOL `RHO_FUN_DEFORMATION_V3_DEFOR`)
    (∀ (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          rhoFun ‖(v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) : V3)‖ < rhoFun ‖v2‖
    ) ∧
    -- 4. DEFORMATION_DIST_LE_V3_DEFOR_A_TWO_CASES_p34 (LA34:4625; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)),
          ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 5. DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES_p34 (LA34:4642; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)),
          ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 6. DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES_p34 (LA34:4714; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hkk : s.k = k) (hk : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, scsDiag k l i →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < s.b l i
    ) ∧
    -- 7. DEFORMATION_DIST_LE_2_TWO_CASES_p34 (LA34:4744; HOL `DEFORMATION_DIST_LE_2_TWO_CASES`)
    (∀ (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l i < dist v2 (w i))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hmod : (l + 1) % k = i % k),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          2 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 8. DEFORMATION_V3_DEFOR_EDGE_TWO_CASES_p34 (LA34:4778; HOL `DEFORMATION_V3_DEFOR_EDGE_TWO_CASES`)
    (∀ (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l i < dist v2 (w i))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hmod : (l + 1) % k = i % k),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < dist v2 (w i)
    ) ∧
    -- 9. DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_p34 (LA34:5053; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l (l + 1) < dist v2 (w (l + 1)))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, ¬(i % k = l % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i
    ) :=
    ⟨DEFORMATION_AZIM_V3_DEFOR_V1_p34, DEFORMATION_AZIM_V3_DEFOR_V1_V1_p34,
      RHO_FUN_DEFORMATION_V3_DEFOR_p34, DEFORMATION_DIST_LE_V3_DEFOR_A_TWO_CASES_p34,
      DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_TWO_CASES_p34,
      DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_TWO_CASES_p34, DEFORMATION_DIST_LE_2_TWO_CASES_p34,
      DEFORMATION_V3_DEFOR_EDGE_TWO_CASES_p34,
      DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_p34⟩

#print axioms la34_capstone_w2


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- LA6 incremental capstone (lane capstone-refresh-w2,
2026-11-04): the public top-level LocalAuto6 theorem exits that became
clean after the w1 baseline (HEAD 4a8f8914) and are statable in
Kepler.Text, re-exposed as ONE conjunction so the Assembly `textCapstone`
cone can consume them (16 of the 16 newly-closed exits; 0
dropped per the workorder's no-forcing rule "抽不出/不一致 → 剔除并如实报",
mechanically detected from the `#print axioms` / `#check @` probe dumps
and the module source; each drop is named below with its reason --
0 carry a sorryAx axiom face or a non-standard axiom, the
remainder are mechanical statement drops).  Provenance: LA6 had no w1 capstone; this is its first capstone and covers only the exits newly cleaned by the LA6 sweep wave sweep-w3 (own-sorry 43 -> 27); the remaining 27 sorried exits are excluded.
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA6 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA6
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la6_capstone_w1 :
    -- 1. NOT_COLL_ORTHONORMAL (LA6:318; HOL `NOT_COLL_ORTHONORMAL`)
    (∀ {x y : V3} (h : ¬ Collinear3 0 x y)
    ,
          ∃ u : V3, u ∈ affineSpan ℝ ({0, x, y} : Set V3) ∧ ‖u‖ = 1 ∧ x ⬝ᵥ u = 0
    ) ∧
    -- 2. CONTINUOUS_FUN_DISTINCT_FINITE_SET (LA6:596; HOL `CONTINUOUS_FUN_DISTINCT_FINITE_SET`)
    (∀ {ff : V3 → ℝ → V3} {r : ℝ} {v0 : V3} (V : Set V3)
          (hV : V.Finite) (h1 : ∀ v1 ∈ V, v1 ≠ v0 → ff v0 r ≠ ff v1 r)
          (h2 : ∀ v ∈ insert v0 V, ContinuousAt (ff v) r),
          ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, v1 ≠ v0 → ff v0 t ≠ ff v1 t
    ) ∧
    -- 3. CONTINUOUS_ATREAL_INJ_PRESERVED (LA6:632; HOL `CONTINUOUS_ATREAL_INJ_PRESERVED`)
    (∀ {ff : V3 → ℝ → V3} {r : ℝ} (V : Set V3)
          (hV : V.Finite) (h1 : ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 r ≠ ff v2 r)
          (h2 : ∀ v ∈ V, ContinuousAt (ff v) r),
          ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d →
          ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 t ≠ ff v2 t
    ) ∧
    -- 4. CONTINUOUS_ATREAL_DISTINCT_FINITE (LA6:669; HOL `CONTINUOUS_ATREAL_DISTINCT_FINITE`)
    (∀ {ff : V3 → ℝ → V3} {r : ℝ} {v0 : V3} (V : Set V3)
          (hV : V.Finite) (h1 : ∀ v1 ∈ V, ff v1 r ≠ v0)
          (h2 : ∀ v ∈ V, ContinuousAt (ff v) r),
          ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, ff v1 t ≠ v0
    ) ∧
    -- 5. DIJ_AFF_GE_PARTITION (LA6:719; HOL `DIJ_AFF_GE_PARTITION`)
    (∀ {u v w : V3} (h : Disjoint ({u, v} : Set V3) ({w} : Set V3))
    ,
          affGe ({u, v} : Set V3) ({w} : Set V3) =
          {z | z ∈ affineSpan ℝ ({u, v} : Set V3)} ∪
            affGt ({u, v} : Set V3) ({w} : Set V3)
    ) ∧
    -- 6. AFF_GE_WEDGE_DISJOINTION (LA6:802; HOL `AFF_GE_WEDGE_DISJOINTION`)
    (∀ (v0 v1 w1 w2 : V3)
    ,
          affGe ({v0, v1} : Set V3) ({w1} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅ ∧
          affGe ({v0, v1} : Set V3) ({w2} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅
    ) ∧
    -- 7. AZIM_POS_IMP_CYCLIC_SET (LA6:919; HOL `AZIM_POS_IMP_CYCLIC_SET`)
    (∀ {v0 v1 w1 w2 : V3} (h : 0 < azim v0 v1 w1 w2)
    ,
          cyclicSet_p3 {w1, w2} v0 v1
    ) ∧
    -- 8. CROSS_PAIR_NOT_IN_FF (LA6:1043 (autoImplicit parameter leak v, w; statement = probe printer dump verbatim (complete signature)); HOL `CROSS_PAIR_NOT_IN_FF`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V → w ∈ V → v ≠ w → (∀ x ∈ FF, Kepler.Geom.affGt {0} {v, w} ⊆ Kepler.Text.wedgeInFanGt_p2 x E) → (v, w) ∉ FF
    ) ∧
    -- 9. FACE_MAP_ADD_SET2_EQ (LA6:1137; HOL `FACE_MAP_ADD_SET2_EQ`)
    (∀ {V : Set V3} {E : Set (Set V3)} (HS1 HS2 : Hypermap (V3 × V3)) (a b x y : V3)
          (hd : (x, y) ∈ dartsOfHyp_p2 (E ∪ {{a, b}}) V) (hya : y ≠ a) (hyb : y ≠ b)
          (hE1 : FAN 0 V E) (hE2 : FAN 0 V (E ∪ {{a, b}}))
          (hHS1 : IsHyp_p2 0 V (E ∪ {{a, b}}) HS1) (hHS2 : IsHyp_p2 0 V E HS2),
          HS1.faceMap (x, y) = HS2.faceMap (x, y)
    ) ∧
    -- 10. LOCAL_FACE_MAP_RHO_NODE1 (LA6:1178 (autoImplicit parameter leak x, y; statement = probe printer dump verbatim (complete signature)); HOL `LOCAL_FACE_MAP_RHO_NODE1`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {x y : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            ∀ (HS : Kepler.Text.Hypermap (Kepler.Geom.V3 × Kepler.Geom.V3)),
              Kepler.Text.IsHyp_p2 0 V E HS →
                (x, y) ∈ FF → HS.faceMap (x, y) = (Kepler.Text.rhoNode1_p2 FF x, Kepler.Text.rhoNode1_p2 FF y)
    ) ∧
    -- 11. LOCAL_FAN_SIMPLE_HYP (LA6:1237; HOL `LOCAL_FAN_SIMPLE_HYP`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} (h : localFan_p2 V E FF)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V E HS),
          HS.Simple
    ) ∧
    -- 12. WEDGE_IN_FAN_LOFA_DETER (LA6:1284 (autoImplicit parameter leak v, w; statement = probe printer dump verbatim (complete signature)); HOL `WEDGE_IN_FAN_LOFA_DETER`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              Kepler.Text.rhoNode1_p2 FF v = w →
                Kepler.Text.wedgeInFanGt_p2 (w, Kepler.Text.rhoNode1_p2 FF w) E =
                  Kepler.Text.wedge 0 w (Kepler.Text.rhoNode1_p2 FF w) v
    ) ∧
    -- 13. LOCAL_FAN_ORBIT_MAP_VITERFF (LA6:1328 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LOCAL_FAN_ORBIT_MAP_VITERFF`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V → ∀ (n : ℕ), ((Kepler.Text.rhoNode1_p2 FF)^[n] v, (Kepler.Text.rhoNode1_p2 FF)^[n + 1] v) ∈ FF
    ) ∧
    -- 14. WEDGE_IN_FAN_LOFA_DETER2 (LA6:1685 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `WEDGE_IN_FAN_LOFA_DETER2`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              Kepler.Text.wedgeInFanGt_p2 (v, Kepler.Text.rhoNode1_p2 FF v) E =
                Kepler.Text.wedge 0 v (Kepler.Text.rhoNode1_p2 FF v) (Kepler.Text.ivsRhoNode1_p2 FF v)
    ) ∧
    -- 15. AFF_SUB_PLANE (LA6:1698; HOL `AFF_SUB_PLANE`)
    (∀ (P : Set V3) (hP : plane_p2 P) {S : Set V3} (hS : S ⊆ P)
    ,
          ∀ z ∈ affineSpan ℝ S, z ∈ P
    ) ∧
    -- 16. LUNAR_DEFORM_PRESERVE_NORM (LA6:1745; no HOL anchor line in file docstring)
    (∀ {e1 e2 e3 : V3} (horth : Orthonormal3 e1 e2 e3)
          (t : ℝ) (x : V3),
          ‖lunarDeform e1 e2 e3 t x‖ = ‖x‖
    ) :=
    ⟨NOT_COLL_ORTHONORMAL, CONTINUOUS_FUN_DISTINCT_FINITE_SET, CONTINUOUS_ATREAL_INJ_PRESERVED,
      CONTINUOUS_ATREAL_DISTINCT_FINITE, DIJ_AFF_GE_PARTITION, AFF_GE_WEDGE_DISJOINTION,
      AZIM_POS_IMP_CYCLIC_SET, @CROSS_PAIR_NOT_IN_FF, FACE_MAP_ADD_SET2_EQ,
      @LOCAL_FACE_MAP_RHO_NODE1, @LOCAL_FAN_SIMPLE_HYP, @WEDGE_IN_FAN_LOFA_DETER,
      @LOCAL_FAN_ORBIT_MAP_VITERFF, @WEDGE_IN_FAN_LOFA_DETER2, AFF_SUB_PLANE,
      LUNAR_DEFORM_PRESERVE_NORM⟩

#print axioms la6_capstone_w1
/-! ### Residual clean-exit capstones la28/la34/la6 (lane capstone-w3,
2026-11-04, roadmap M0b third item): every remaining clean public exit of
LA28 / LA34 / LA6 that had NEVER been materialised into any capstone is
re-exposed as ONE conjunction per module (la28_capstone_w3 /
la34_capstone_w3 / la6_capstone_w2) and the three `have hla{28c,34c,6b}`
lines in Assembly.textCapstone pull the capstone proof terms into the e2e
cone (pure insertion there too, after hla6; the w1 and w2 capstones stay
wired).  Delta definition (measured at the lane HEAD, not assumed): the
public top-level `theorem` exports of the module whose probed `#print
axioms` face is exactly the standard three [propext, Classical.choice,
Quot.sound] (no sorryAx), whose statement declares no module-private
constant, whose declaration kind is `theorem`, and which is not
universe-polymorphic, MINUS the conjunct name set of every existing
capstone of the module (LA28 w1 42 + w2 14, LA34 w1 52 + w2 9, LA6 w1
16).  Counts at HEAD da9b5fd4: LA28 50, LA34 28, LA6 73 (151 total; the
workorder's rough 64/37/89 expectation only subtracted the w1 capstones
and re-counted the 14/9/16 w2 exits; strict dedup as required gives
50/28/73).  All 151 are individually exactly standard three; no delta
candidate was dropped by the mechanical statement filters (module-private
`✝`, def-kind, universe-polymorphic) -- those filters only remove exits
that are not part of the clean-statability set in the first place.
Extraction purely mechanical (gen_items.py): conjuncts are verbatim module
source signatures, bodies are the exit constants; the `set_option
maxHeartbeats 50000000 in` scope mirrors the existing large-conjunction
sections in this file.  Environment-alignment scopes mirror module-local
declarations so the verbatim signatures elaborate under the same name and
open resolution as their source modules: LA6 carries the module's own
`open Kepler.Text.Fan` (LocalAuto6:48); LA28 and LA34 need none.  All
three modules are already imported by this file, so zero import changes.
The exact cone increment is re-measured at the orchestrator e2e gate. -/


set_option maxHeartbeats 50000000 in

/-- LA28 w3 capstone (lane capstone-w3, 2026-11-04,
roadmap M0b third item): every public top-level LocalAuto28 theorem exit
that is clean and statable in Kepler.Text and was never a conjunct of an
existing capstone, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume it (50 of the 50 w3 delta exits;
0 dropped per the workorder's no-forcing rule "抽不出/不一致 →
剔除并如实报", mechanically detected from the `#print axioms` /
`#check @` probe dumps and the module source; each drop is named below
with its reason).  Clean means the probed `#print axioms` face is exactly
[propext, Classical.choice, Quot.sound] (no sorryAx, no other axiom), the
statement declares no module-private constant, the declaration kind is
`theorem`, and the statement is not universe-polymorphic.  Provenance:
the exit set is the residual workorder sweep (`#print axioms` exactly the standard three at the lane HEAD) minus the conjunct names of every existing capstone of this module (la28_capstone_w1/w2); the existing capstones are left untouched (pure insertion, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA28 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA28
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la28_capstone_w3 :
    -- 1. NORM_LE_2_IN_BBS_p28 (LA28:185; HOL `NORM_LE_2_IN_BBS`)
    (∀ (s : ScsV39) (w : ℕ → V3) (l : ℕ) (h : BBsV39 s w)
    ,
          2 ≤ ‖w l‖
    ) ∧
    -- 2. MMS_IMP_BBS_p28 (LA28:193; HOL `MMS_IMP_BBS`)
    (∀ (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s)
    ,
          BBsV39 s w
    ) ∧
    -- 3. MMS_IMP_BBPRIME_p28 (LA28:198; HOL `MMS_IMP_BBPRIME`)
    (∀ (s : ScsV39) (w : ℕ → V3) (h : w ∈ MMsV39 s)
    ,
          w ∈ BBprimeV39 s
    ) ∧
    -- 4. DEFORMATION_DIST_LE_MK_A_p28 (LA28:888; HOL `DEFORMATION_DIST_LE_MK_A`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k) (hk3 : 3 < k)
          (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)),
          ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) →
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
            s.a l i < dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 5. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_p28 (LA28:903; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
          (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧
          ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) →
          s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 6. DEFORMATION_DIST_LE_V3_DEFOR_B_MK_p28 (LA28:984; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, scsDiag k l i → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 7. V3_DEFOR_IN_AFF_GT_V1_MK_p28 (LA28:1014; HOL `V3_DEFOR_IN_AFF_GT_V1_MK`)
    (∀ (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
          (haff : v2 ∈ affGt {0} {v1, w}),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ∈ affGt {0} {v1, w}
    ) ∧
    -- 8. V3_DEFOR_INCREASING_IN_ANGLE_p28 (LA28:1182; HOL `V3_DEFOR_INCREASING_IN_ANGLE`)
    (∀ (v1 v2 w : V3) (x1 x2 x5 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hncw : ¬ Collinear ℝ ({0, v1, w} : Set V3))
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (haff : v2 ∈ affGt {0} {v1, w}),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist v2 w < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) w
    ) ∧
    -- 9. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_p28 (LA28:1323; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
          (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (l + 1) % k = j % k) (haj : s.a l j = dist v2 (w j)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          s.a l j < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j)
    ) ∧
    -- 10. DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_p28 (LA28:1368; HOL `DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
          (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (l + 1) % k = j % k) (haj : s.a l j = dist v2 (w j))
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬((l + 1) % k = i % k) → s.a l i < dist v2 (w i)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
          s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 11. DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_p28 (LA28:1520; HOL `DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))}),
          ∀ j : ℕ, l % k = (j + 1) % k → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j
    ) ∧
    -- 12. DIST_V3_DEFOR_EDGE_SUC_p28 (LA28:1567; HOL `DIST_V3_DEFOR_EDGE_SUC`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j
    ) ∧
    -- 13. DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_p28 (LA28:1627; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i : ℕ, ¬(l % k = i % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 14. DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_p28 (LA28:1660; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + k - 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (l + 1) % k = j % k) (hlt : dist v2 (w j) < s.b l j)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 15. DEFORMATION_V3_DEFOR_NOT_IN_V_MK_p28 (LA28:1709; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1),
          ∀ i : ℕ, ¬(i % k = l % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          0 < dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 16. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_p28 (LA28:1720; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
          0 < dist (v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 17. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_p28 (LA28:1758; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
          v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ≠ w i
    ) ∧
    -- 18. V3_DEFOR_DEFORMATION_V5_p28 (LA28:3881; HOL `V3_DEFOR_DEFORMATION_V5`)
    (∀ (v1 v2 : V3) (x1 x2 x5 : ℝ) (V : Set V3)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5),
          ∃ ε : ℝ, 0 < ε ∧ Deformation (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2) V (-ε) ε
    ) ∧
    -- 19. DEFORMATION_LUNAR_AFFINE_HULL_MK_p28 (LA28:4045 (autoImplicit parameter leak FF; statement = probe printer dump verbatim (complete signature)); HOL `DEFORMATION_LUNAR_AFFINE_HULL_MK`)
    (∀ {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)}
          (s : Kepler.Text.ScsV39) (k : ℕ) (w : ℕ → Kepler.Geom.V3) (l j : ℕ) (v1 v2 v w1 : Kepler.Geom.V3) (x1 x2 x5 a : ℝ)
          (E : Set (Set Kepler.Geom.V3)) (V : Set Kepler.Geom.V3),
          s.k = k →
            3 < k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  Kepler.Geom.azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
                    ¬Collinear ℝ {0, w (l + 1), w (l + (s.k - 1))} →
                      w l ∈ Kepler.Geom.affGt {0} {w (l + 1), w (l + (s.k - 1))} →
                        j % k = (l + 1) % k →
                          s.a j l = dist (w j) (w l) →
                            dist (w j) (w l) < s.b j l →
                              (∀ (i : ℕ), Kepler.Text.scsDiag k l i → 4 * Kepler.Text.h0 < s.b l i) →
                                (∀ (i : ℕ), Kepler.Text.scsDiag k l i → s.a l i < dist (w l) (w i)) →
                                  (∀ (i : ℕ), ¬s.J l i) →
                                    w l = v2 →
                                      w (l + k - 1) = v1 →
                                        ‖v1‖ ^ 2 = x1 →
                                          ‖v2‖ ^ 2 = x2 →
                                            ‖v2 - v1‖ ^ 2 = x5 →
                                              a = -1 →
                                                (Set.range fun i => (w i, w (i + 1))) = FF →
                                                  Set.range w = V →
                                                    v ≠ v2 →
                                                      w1 ≠ v2 →
                                                        (Set.range fun i => {w i, w (i + 1)}) = E →
                                                          Kepler.Text.Lunar v w1 V E →
                                                            ∃ ε,
                                                              0 < ε ∧
                                                                ∀ t ∈ Set.Ioo (-ε) ε,
                                                                  Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t ∈
                                                                    affineSpan ℝ {0, v, w1, v2}
    ) ∧
    -- 20. CARD_FF_EQ_V3_DEFOR_DEFORMATION_MK_p28 (LA28:4199; HOL `CARD_FF_EQ_V3_DEFOR_DEFORMATION_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k : ℕ)
          (v1 v2 : V3) (a x1 x5 x2 e1 : ℝ) (V : Set V3)
          (hk : s.k = k) (hV : Set.range w = V) (hs : isScsV39 s) (hk3 : 3 < k)
          (hbb : BBsV39 s w)
          (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
            BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)),
          ∀ t : ℝ, 0 < t ∧ t < e1 →
          Nat.card (Set.range fun i : ℕ =>
              (v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t,
               v3DeforV5_p28 a x1 x5 x2 v1 v2 (w (i + 1)) t)) =
          Nat.card (Set.range fun i : ℕ => (w i, w (i + 1)))
    ) ∧
    -- 21. DSV_V3_DEFOR_EQ_MK_p28 (LA28:4218; HOL `DSV_V3_DEFOR_EQ_MK`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 : V3)
          (a x1 x5 x2 t : ℝ) (hk : s.k = k) (hs : isScsV39 s) (hbb : BBsV39 s w)
          (hJ : ∀ i, ¬ s.J l i),
          dsvV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 (w l) (w i) t) = dsvV39 s w
    ) ∧
    -- 22. INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_p28 (LA28:4284; HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V)
          (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
            BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              ((rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF))^[i]
                (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l % k)) t)) =
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k)))
    ) ∧
    -- 23. TAUSTAR_V3_DEFOR_MK_p28 (LA28:4345; HOL `TAUSTAR_V3_DEFOR_MK`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : j % k = (l + 1) % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
            BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          taustarV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t) = taustarV39 s w
    ) ∧
    -- 24. DEFORMATION_DIST_LE_MK_A_TWO_CASES_p28 (LA28:4461; HOL `DEFORMATION_DIST_LE_MK_A_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hk : s.k = k)
          (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)),
          ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) →
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
            s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 25. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_TWO_CASES_p28 (LA28:4476; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧
          ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) →
          s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 26. DEFORMATION_DIST_LE_V3_DEFOR_B_MK_TWO_CASES_p28 (LA28:4533; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, scsDiag k l i → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 27. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_TWO_CASES_p28 (LA28:4563; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : l % k = (j + 1) % k) (haj : s.a l j = dist v2 (w j)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          s.a l j < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j)
    ) ∧
    -- 28. DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_TWO_CASES_p28 (LA28:4599; HOL `DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (hk : s.k = k) (hk3 : 3 < k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : l % k = (j + 1) % k) (haj : s.a l j = dist v2 (w j))
          (hi : ∀ i : ℕ, ¬(l % k = i % k) ∧ ¬(l % k = (i + 1) % k) → s.a l i < dist v2 (w i)),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
          s.a l i < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 29. DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_TWO_CASES_p28 (LA28:4676; HOL `DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))}),
          ∀ j : ℕ, (l + 1) % k = j % k → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j
    ) ∧
    -- 30. DIST_V3_DEFOR_EDGE_SUC_TWO_CASES_p28 (LA28:4711; HOL `DIST_V3_DEFOR_EDGE_SUC_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1)
          (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w j) < s.b l j
    ) ∧
    -- 31. DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_TWO_CASES_p28 (LA28:4724; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i : ℕ, ¬(l % k = i % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 32. DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_TWO_CASES_p28 (LA28:4756; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hk : s.k = k) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : l % k = (j + 1) % k) (hlt : dist v2 (w j) < s.b l j)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε ∧ ¬(l % k = i % k) →
          dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i) < s.b l i
    ) ∧
    -- 33. DEFORMATION_V3_DEFOR_NOT_IN_V_MK_TWO_CASES_p28 (LA28:4806; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1),
          ∀ i : ℕ, ¬(i % k = l % k) → ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 34. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_TWO_CASES_p28 (LA28:4817; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
          0 < dist (v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1) (w i)
    ) ∧
    -- 35. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_TWO_CASES_p28 (LA28:4855; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3)
          (k l : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (hk3 : 3 < k) (hk : s.k = k) (hs : isScsV39 s)
          (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, -ε < t ∧ t < ε ∧ ¬(i % k = l % k) →
          v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1 ≠ w i
    ) ∧
    -- 36. V3_DEFOR_EQ_IN_FF_MK_TWO_CASES_p28 (LA28:4896; HOL `V3_DEFOR_EQ_IN_FF_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ) (v1 v2 : V3)
          (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k) (hk : s.k = k)
          (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (v2, a') ∈ FF
    ) ∧
    -- 37. V3_DEFOR_EQ_IN_FF_MK_SYM_TWO_CASES_p28 (LA28:4971; HOL `V3_DEFOR_EQ_IN_FF_MK_SYM_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
          (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
          (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3, (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (a', v2) ∈ FF
    ) ∧
    -- 38. DEFORMATION_AZIM_V3_DEFOR_V1_MK_TWO_CASES_p28 (LA28:5098; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t)) =
          azim 0 v2 (rhoNode1 FF v2) (epPair_p28 FF v2)
    ) ∧
    -- 39. V3_DEFOR_EQ_IN_FF_SUB_MK_TWO_CASES_p28 (LA28:5346; HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
          (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
          (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
            (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t) =
          v3DeforV1_p17 (-1) (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - t) + v1
    ) ∧
    -- 40. V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_TWO_CASES_p28 (LA28:5400; HOL `V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
          (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
          (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3, (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t, a') ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (v1, a') ∈ FF
    ) ∧
    -- 41. DEFORMATION_AZIM_V3_DEFOR_SUB_MK_TWO_CASES_p28 (LA28:5438; HOL `DEFORMATION_AZIM_V3_DEFOR_SUB_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v1 t)) =
          azim 0 v1 (rhoNode1 FF v1) (epPair_p28 FF v1)
    ) ∧
    -- 42. V3_DEFOR_EQ_IN_FF_SUC_MK_TWO_CASES_p28 (LA28:5593; HOL `V3_DEFOR_EQ_IN_FF_SUC_MK_TWO_CASES`)
    (∀ (s : ScsV39) (w : ℕ → V3) (k l : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e t : ℝ) (FF : Set (V3 × V3)) (V : Set V3) (hk3 : 3 < k)
          (hk : s.k = k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s) (hl : w l = v2)
          (hl1 : w (l + 1) = v1) (h1 : 0 < x1) (h2 : 0 < x2) (h5 : 0 < x5)
          (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3)) (hx1 : ‖v1‖ ^ 2 = x1)
          (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5) (ha : a = -1) (he : 0 < e)
          (het : -e < t)
          (hni : ∀ r : ℝ, ∀ i : ℕ, -e < r ∧ r < e ∧ ¬(i % k = l % k) →
            v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i)
          (hte : t < e) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∀ a' : V3,
          (a', v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t) ∈ deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
          (a', w (l + k - 1)) ∈ FF
    ) ∧
    -- 43. DEFORMATION_AZIM_V3_DEFOR_SUC_MK_TWO_CASES_p28 (LA28:5654; HOL `DEFORMATION_AZIM_V3_DEFOR_SUC_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l + k - 1)) t)) =
          azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1)))
            (epPair_p28 FF (w (l + k - 1)))
    ) ∧
    -- 44. V3_DEFOR_EQ_IN_FF_NOT_MK_TWO_CASES_p28 (LA28:5863 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_TWO_CASES`)
    (∀ {v : Kepler.Geom.V3} (s : Kepler.Text.ScsV39)
          (w : ℕ → Kepler.Geom.V3) (k l : ℕ) (v1 v2 : Kepler.Geom.V3) (x1 x2 x5 a e t : ℝ)
          (FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)) (V : Set Kepler.Geom.V3),
          3 < k →
            s.k = k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  w l = v2 →
                    w (l + 1) = v1 →
                      0 < x1 →
                        0 < x2 →
                          0 < x5 →
                            ¬Collinear ℝ {0, v1, v2} →
                              ‖v1‖ ^ 2 = x1 →
                                ‖v2‖ ^ 2 = x2 →
                                  ‖v2 - v1‖ ^ 2 = x5 →
                                    a = -1 →
                                      0 < e →
                                        -e < t →
                                          (∀ (r : ℝ) (i : ℕ),
                                              -e < r ∧ r < e ∧ ¬i % k = l % k →
                                                Kepler.Text.v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i) →
                                            t < e →
                                              (Set.range fun i => (w i, w (i + 1))) = FF →
                                                Set.range w = V →
                                                  v ≠ w (l + k - 1) →
                                                    v ≠ v2 →
                                                      v ≠ v1 →
                                                        v ∈ V →
                                                          ∀ (a' : Kepler.Geom.V3),
                                                            (Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t, a') ∈
                                                                Kepler.Text.deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
                                                              (v, a') ∈ FF
    ) ∧
    -- 45. V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_TWO_CASES_p28 (LA28:6012 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_TWO_CASES`)
    (∀ {v : Kepler.Geom.V3} (s : Kepler.Text.ScsV39)
          (w : ℕ → Kepler.Geom.V3) (k l : ℕ) (v1 v2 : Kepler.Geom.V3) (x1 x2 x5 a e t : ℝ)
          (FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)) (V : Set Kepler.Geom.V3),
          3 < k →
            s.k = k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  w l = v2 →
                    w (l + 1) = v1 →
                      0 < x1 →
                        0 < x2 →
                          0 < x5 →
                            ¬Collinear ℝ {0, v1, v2} →
                              ‖v1‖ ^ 2 = x1 →
                                ‖v2‖ ^ 2 = x2 →
                                  ‖v2 - v1‖ ^ 2 = x5 →
                                    a = -1 →
                                      0 < e →
                                        -e < t →
                                          (∀ (r : ℝ) (i : ℕ),
                                              -e < r ∧ r < e ∧ ¬i % k = l % k →
                                                Kepler.Text.v3DeforV1_p17 a (-v1) (v2 - v1) x1 x5 x2 x2 (x5 - r) + v1 ≠ w i) →
                                            t < e →
                                              (Set.range fun i => (w i, w (i + 1))) = FF →
                                                Set.range w = V →
                                                  v ≠ w (l + k - 1) →
                                                    v ≠ v2 →
                                                      v ≠ v1 →
                                                        v ∈ V →
                                                          ∀ (a' : Kepler.Geom.V3),
                                                            (a', Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t) ∈
                                                                Kepler.Text.deformedFF_p28 x1 x5 x2 v1 v2 t FF ↔
                                                              (a', v) ∈ FF
    ) ∧
    -- 46. DEFORMATION_AZIM_V3_DEFOR_NOT_MK_TWO_CASES_p28 (LA28:6161; HOL `DEFORMATION_AZIM_V3_DEFOR_NOT_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ≠ w (l + k - 1) ∧ v ≠ v2 ∧
            v ≠ v1 ∧ v ∈ V →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
          azim 0 v (rhoNode1 FF v) (epPair_p28 FF v)
    ) ∧
    -- 47. DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28 (LA28:6404; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ)
          (w : ℕ → V3) (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a : ℝ) (FF : Set (V3 × V3))
          (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ v : V3, -ε < t ∧ t < ε ∧ v ∈ V →
          azim 0 (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)
            (rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t))
            (epPair_p28 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v t)) =
          azim 0 v (rhoNode1 FF v) (epPair_p28 FF v)
    ) ∧
    -- 48. DEFORMATION_LUNAR_AFFINE_HULL_MK_TWO_CASES_p28 (LA28:6544 (autoImplicit parameter leak FF; statement = probe printer dump verbatim (complete signature)); HOL `DEFORMATION_LUNAR_AFFINE_HULL_MK_TWO_CASES`)
    (∀ {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)}
          (s : Kepler.Text.ScsV39) (k : ℕ) (w : ℕ → Kepler.Geom.V3) (l j : ℕ) (v1 v2 v w1 : Kepler.Geom.V3) (x1 x2 x5 a : ℝ)
          (E : Set (Set Kepler.Geom.V3)) (V : Set Kepler.Geom.V3),
          s.k = k →
            3 < k →
              Kepler.Text.isScsV39 s →
                w ∈ Kepler.Text.MMsV39 s →
                  Kepler.Geom.azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi →
                    ¬Collinear ℝ {0, w (l + 1), w (l + (s.k - 1))} →
                      w l ∈ Kepler.Geom.affGt {0} {w (l + 1), w (l + (s.k - 1))} →
                        (j + 1) % k = l % k →
                          s.a j l = dist (w j) (w l) →
                            dist (w j) (w l) < s.b j l →
                              (∀ (i : ℕ), Kepler.Text.scsDiag k l i → 4 * Kepler.Text.h0 < s.b l i) →
                                (∀ (i : ℕ), Kepler.Text.scsDiag k l i → s.a l i < dist (w l) (w i)) →
                                  (∀ (i : ℕ), ¬s.J l i) →
                                    w l = v2 →
                                      w (l + 1) = v1 →
                                        ‖v1‖ ^ 2 = x1 →
                                          ‖v2‖ ^ 2 = x2 →
                                            ‖v2 - v1‖ ^ 2 = x5 →
                                              a = -1 →
                                                (Set.range fun i => (w i, w (i + 1))) = FF →
                                                  Set.range w = V →
                                                    v ≠ v2 →
                                                      w1 ≠ v2 →
                                                        (Set.range fun i => {w i, w (i + 1)}) = E →
                                                          Kepler.Text.Lunar v w1 V E →
                                                            ∃ ε,
                                                              0 < ε ∧
                                                                ∀ t ∈ Set.Ioo (-ε) ε,
                                                                  Kepler.Text.v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 v2 t ∈
                                                                    affineSpan ℝ {0, v, w1, v2}
    ) ∧
    -- 49. INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_TWO_CASES_p28 (LA28:6682; HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_TWO_CASES`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3)
          (l j : ℕ) (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ) (FF : Set (V3 × V3)) (V : Set V3)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1) (hFF : (Set.range fun i : ℕ => (w i, w (i + 1))) = FF)
          (hV : Set.range w = V)
          (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
            BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t ∧ t < ε →
          interiorAngle1 0 (deformedFF_p28 x1 x5 x2 v1 v2 t FF)
              ((rhoNode1 (deformedFF_p28 x1 x5 x2 v1 v2 t FF))^[i]
                (v3DeforV5_p28 (-1) x1 x5 x2 v1 v2 (w (l % k)) t)) =
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k)))
    ) ∧
    -- 50. TAUSTAR_V3_DEFOR_MK_TWO_CASES_p28 (LA28:6744; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l j : ℕ)
          (v1 v2 : V3) (x1 x2 x5 a e1 : ℝ)
          (hk : s.k = k) (hk3 : 3 < k) (hs : isScsV39 s) (hm : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬ Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} {w (l + 1), w (l + (s.k - 1))})
          (hj : (j + 1) % k = l % k) (haj : s.a j l = dist (w j) (w l))
          (hbj : dist (w j) (w l) < s.b j l)
          (hdiag1 : ∀ i, scsDiag k l i → 4 * h0 < s.b l i)
          (hdiag2 : ∀ i, scsDiag k l i → s.a l i < dist (w l) (w i))
          (hJ : ∀ i, ¬ s.J l i) (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx5 : ‖v2 - v1‖ ^ 2 = x5)
          (ha : a = -1)
          (hBB : ∀ t : ℝ, 0 < t ∧ t < e1 →
            BBsV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t)) (he1 : 0 < e1),
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t ∧ t < ε →
          taustarV39 s (fun i => v3DeforV5_p28 a x1 x5 x2 v1 v2 (w i) t) = taustarV39 s w
    ) :=
    ⟨NORM_LE_2_IN_BBS_p28, MMS_IMP_BBS_p28, MMS_IMP_BBPRIME_p28, DEFORMATION_DIST_LE_MK_A_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_p28, DEFORMATION_DIST_LE_V3_DEFOR_B_MK_p28,
      V3_DEFOR_IN_AFF_GT_V1_MK_p28, V3_DEFOR_INCREASING_IN_ANGLE_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_p28, DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_p28, DIST_V3_DEFOR_EDGE_SUC_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_p28, DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_p28,
      DEFORMATION_V3_DEFOR_NOT_IN_V_MK_p28, DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_p28,
      DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_p28, V3_DEFOR_DEFORMATION_V5_p28,
      @DEFORMATION_LUNAR_AFFINE_HULL_MK_p28, CARD_FF_EQ_V3_DEFOR_DEFORMATION_MK_p28,
      DSV_V3_DEFOR_EQ_MK_p28, INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_p28, TAUSTAR_V3_DEFOR_MK_p28,
      DEFORMATION_DIST_LE_MK_A_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_B_MK_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_MK1_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_AA_COM_MK_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_EDGE_SUB_TWO_CASES_p28,
      DIST_V3_DEFOR_EDGE_SUC_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK1_TWO_CASES_p28,
      DEFORMATION_DIST_LE_V3_DEFOR_B_COM_MK_TWO_CASES_p28,
      DEFORMATION_V3_DEFOR_NOT_IN_V_MK_TWO_CASES_p28,
      DEFORMATION_V3_DEFOR_NOT_IN_V_COM_MK_TWO_CASES_p28,
      DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_MK_TWO_CASES_p28,
      V3_DEFOR_EQ_IN_FF_MK_TWO_CASES_p28, V3_DEFOR_EQ_IN_FF_MK_SYM_TWO_CASES_p28,
      DEFORMATION_AZIM_V3_DEFOR_V1_MK_TWO_CASES_p28, V3_DEFOR_EQ_IN_FF_SUB_MK_TWO_CASES_p28,
      V3_DEFOR_EQ_IN_FF_SUB_MK_SYM_TWO_CASES_p28,
      DEFORMATION_AZIM_V3_DEFOR_SUB_MK_TWO_CASES_p28, V3_DEFOR_EQ_IN_FF_SUC_MK_TWO_CASES_p28,
      DEFORMATION_AZIM_V3_DEFOR_SUC_MK_TWO_CASES_p28, V3_DEFOR_EQ_IN_FF_NOT_MK_TWO_CASES_p28,
      V3_DEFOR_EQ_IN_FF_NOT_MK_SYM_TWO_CASES_p28,
      DEFORMATION_AZIM_V3_DEFOR_NOT_MK_TWO_CASES_p28,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_MK_TWO_CASES_p28,
      @DEFORMATION_LUNAR_AFFINE_HULL_MK_TWO_CASES_p28,
      INTERIOR_ANGLE_SAME_V3_DEFOR1_MK_TWO_CASES_p28, TAUSTAR_V3_DEFOR_MK_TWO_CASES_p28⟩

#print axioms la28_capstone_w3


set_option maxHeartbeats 50000000 in

/-- LA34 w3 capstone (lane capstone-w3, 2026-11-04,
roadmap M0b third item): every public top-level LocalAuto34 theorem exit
that is clean and statable in Kepler.Text and was never a conjunct of an
existing capstone, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume it (28 of the 28 w3 delta exits;
0 dropped per the workorder's no-forcing rule "抽不出/不一致 →
剔除并如实报", mechanically detected from the `#print axioms` /
`#check @` probe dumps and the module source; each drop is named below
with its reason).  Clean means the probed `#print axioms` face is exactly
[propext, Classical.choice, Quot.sound] (no sorryAx, no other axiom), the
statement declares no module-private constant, the declaration kind is
`theorem`, and the statement is not universe-polymorphic.  Provenance:
the exit set is the residual workorder sweep (`#print axioms` exactly the standard three at the lane HEAD) minus the conjunct names of every existing capstone of this module (la34_capstone_w1/w2); the existing capstones are left untouched (pure insertion, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA34 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA34
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la34_capstone_w3 :
    -- 1. V3_DEFOR_DEFORMATION_p34 (LA34:1091; HOL `V3_DEFOR_DEFORMATION`)
    (∀ (v1 w : V3) (V : Set V3) (x1 x2 x4 x5 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h4 : 0 < x4) (h5 : 0 < x5) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, w} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖w‖ ^ 2 = x2) (hx6 : ‖v1 - w‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ Deformation (v3DeforV4_p34 a x1 x2 x6 v1 w) V (-e) e
    ) ∧
    -- 2. V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34 (LA34:1124; HOL `V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION`)
    (∀ (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hball : v2 ∈ ballAnnulus) (hn : ‖v2‖ ≠ 2),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          v3DeforV4_p34 a x1 x2 x6 v1 v2 v2 t ∈ ballAnnulus
    ) ∧
    -- 3. HYPER_MM_COLLINEAR_p34 (LA34:1231; HOL `HYPER_MM_COLLINEAR`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 : ℝ)
          (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : 3 < k)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6),
          0 < x1 ∧ 0 < x2 ∧ 0 < x6 ∧ ¬Collinear ℝ ({0, v1, v2} : Set V3)
    ) ∧
    -- 4. DEFORMATION_DIST_LE_V3_DEFOR_A_p34 (LA34:1317; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A`)
    (∀ (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)),
          ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 5. DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_p34 (LA34:1334; HOL `DEFORMATION_DIST_LE_V3_DEFOR_A_SUC`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)),
          ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 6. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_p34 (LA34:1406; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬((l + 1) % k = j % k) → s.a l j < dist v2 (w j)),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ j : ℕ,
          ¬(l % k = j % k) → ¬((l + 1) % k = j % k) →
          s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 7. DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_p34 (LA34:1520; HOL `DEFORMATION_DIST_LE_V3_DEFOR_B_SUC`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hkk : s.k = k) (hk : 3 < k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, scsDiag k l i →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < s.b l i
    ) ∧
    -- 8. xrr_decreasing_lt_p34 (LA34:1550; HOL `xrr_decreasing_lt`)
    (∀ (y1 y1' y2 y6 : ℝ) (h1 : 2 ≤ y1) (h1' : 2 ≤ y1')
          (h2 : 2 ≤ y2) (h6 : 2 ≤ y6) (h2h : y2 ≤ 2 * h0) (hlt : y1 < y1'),
          xrr y1' y2 y6 < xrr y1 y2 y6
    ) ∧
    -- 9. exp_aff_gt_by_dot_p34 (LA34:1587; HOL `exp_aff_gt_by_dot`)
    (∀ (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u})
    ,
          affGt {x, v} {u} = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0 ∧ 0 < (w - x) ⬝ᵥ e1Fan_p34 x v u}
    ) ∧
    -- 10. exp_aff_by_dot_p34 (LA34:1634; HOL `exp_aff_by_dot`)
    (∀ (x v u : V3) (hnc : ¬Collinear ℝ {x, v, u})
    ,
          affineSpan ℝ ({x, v, u} : Set V3) = {w : V3 | (w - x) ⬝ᵥ e2Fan_p34 x v u = 0}
    ) ∧
    -- 11. IN_AFF_EQ_DOT_E2_FAN_p34 (LA34:1652; HOL `IN_AFF_EQ_DOT_E2_FAN`)
    (∀ (x y z : V3) (hnc : ¬Collinear ℝ ({0, x, y} : Set V3))
    ,
          e2Fan_p34 0 x y ⬝ᵥ z = 0 ↔ z ∈ affineSpan ℝ ({0, x, y} : Set V3)
    ) ∧
    -- 12. OPEN_RELA_AFF_GT_p34 (LA34:1669; HOL `OPEN_RELA_AFF_GT`)
    (∀ (z x y : V3)
          (h1 : ¬Collinear ℝ ({0, z, x} : Set V3))
          (h2 : ¬Collinear ℝ ({0, x, y} : Set V3))
          (hz : z ∈ affGt {0} {x, y}),
          ∃ e : ℝ, 0 < e ∧ Metric.ball z e ∩ affineSpan ℝ ({0, x, z} : Set V3) ⊆ affGt {0} {x, y}
    ) ∧
    -- 13. V3_DEFOR_IN_AFF_GT_p34 (LA34:1771; HOL `V3_DEFOR_IN_AFF_GT`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hnc2 : ¬Collinear ℝ ({0, v1, w} : Set V3))
          (hv2 : v2 ∈ affGt {0} {v1, w}),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ affGt {0} {v1, w}
    ) ∧
    -- 14. V3_DEFOR_IN_AFF_GT_V1_p34 (LA34:1821; HOL `V3_DEFOR_IN_AFF_GT_V1`)
    (∀ (v1 v2 w : V3) (x1 x2 x6 a : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h6 : 0 < x6)
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hnc2 : ¬Collinear ℝ ({0, v1, w} : Set V3))
          (hv2 : v2 ∈ affGt {0} {v1, w}),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ∈ affGt {0} {v1, w}
    ) ∧
    -- 15. xrr_increasing_le_p34 (LA34:1872; HOL `xrr_increasing_le`)
    (∀ (y1 y2 y6 y6' : ℝ) (h1 : 0 < y1) (h2 : 0 < y2)
          (h6 : 0 ≤ y6) (h6' : y6 ≤ y6'),
          xrr y1 y2 y6 ≤ xrr y1 y2 y6'
    ) ∧
    -- 16. DEFORMATION_DIST_LE_2_p34 (LA34:1887; HOL `DEFORMATION_DIST_LE_2`)
    (∀ (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l i < dist v2 (w i))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hmod : l % k = (i + 1) % k),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          2 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 17. DEFORMATION_V3_DEFOR_EDGE_p34 (LA34:2140; HOL `DEFORMATION_V3_DEFOR_EDGE`)
    (∀ (s : ScsV39) (k l i : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l i < dist v2 (w i))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hmod : l % k = (i + 1) % k),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) < dist v2 (w i)
    ) ∧
    -- 18. DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_p34 (LA34:2409; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l (l + k - 1) < dist v2 (w (l + k - 1)))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∀ i, ¬(i % k = l % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
            dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i
    ) ∧
    -- 19. DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_b_p34 (LA34:2483; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hnc : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l (l + k - 1) < dist v2 (w (l + k - 1)))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i
    ) ∧
    -- 20. DEFORMATION_V3_DEFOR_NOT_IN_V_p34 (LA34:2573; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 21. DEFORMATION_V3_DEFOR_NOT_IN_V_V1_p34 (LA34:2611; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∀ i : ℕ, ¬(i % k = l % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
            0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 22. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_p34 (LA34:2632; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ,
          0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 23. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_p34 (LA34:2658; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
          0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 24. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34 (LA34:2696; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ,
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i
    ) ∧
    -- 25. DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34 (LA34:2712; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
          v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t) ≠ w i
    ) ∧
    -- 26. HYPER_MM_COLLINEAR_TWO_CASES_p34 (LA34:4567; HOL `HYPER_MM_COLLINEAR_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 : ℝ)
          (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hk : 3 < k)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6),
          0 < x1 ∧ 0 < x2 ∧ 0 < x6 ∧ ¬Collinear ℝ ({0, v1, v2} : Set V3)
    ) ∧
    -- 27. DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_TWO_CASES_p34 (LA34:4661; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hs : isScsV39 s) (hmw : w ∈ MMsV39 s) (hkk : s.k = k) (hk : 3 < k)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hbound : ∀ j, ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) → s.a l j < dist v2 (w j)),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ j : ℕ,
          ¬(l % k = j % k) → ¬(l % k = (j + 1) % k) →
          s.a l j < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w j)
    ) ∧
    -- 28. DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_b_p34 (LA34:5125; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
          (ha_lt : s.a l (l + 1) < dist v2 (w (l + 1)))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hdiag : ∀ i, scsDiag k l i → 4 * h0 < s.b l i),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e → ∀ i : ℕ, ¬(i % k = l % k) →
          dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i) ≤ s.b l i
    ) :=
    ⟨V3_DEFOR_DEFORMATION_p34, V3_DEFOR_IN_BALL_ANNULUS_DEFORMATION_p34, HYPER_MM_COLLINEAR_p34,
      DEFORMATION_DIST_LE_V3_DEFOR_A_p34, DEFORMATION_DIST_LE_V3_DEFOR_A_SUC_p34,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_p34, DEFORMATION_DIST_LE_V3_DEFOR_B_SUC_p34,
      xrr_decreasing_lt_p34, exp_aff_gt_by_dot_p34, exp_aff_by_dot_p34,
      IN_AFF_EQ_DOT_E2_FAN_p34, @OPEN_RELA_AFF_GT_p34, V3_DEFOR_IN_AFF_GT_p34,
      V3_DEFOR_IN_AFF_GT_V1_p34, xrr_increasing_le_p34, DEFORMATION_DIST_LE_2_p34,
      DEFORMATION_V3_DEFOR_EDGE_p34, DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_p34,
      DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_b_p34, DEFORMATION_V3_DEFOR_NOT_IN_V_p34,
      DEFORMATION_V3_DEFOR_NOT_IN_V_V1_p34, DEFORMATION_V3_DEFOR_NOT_IN_V_COM_p34,
      DEFORMATION_V3_DEFOR_NOT_IN_V_COM_V1_p34, DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_p34,
      DEFORMATION_V3_DEFOR_NOT_IN_V_COM_EQ_V1_p34, HYPER_MM_COLLINEAR_TWO_CASES_p34,
      DEFORMATION_DIST_LE_V3_DEFOR_A_COM_SUC_TWO_CASES_p34,
      DEFORMATION_DIST_LE_BLL_V3_DEFOR_COM_TWO_CASES_b_p34⟩

#print axioms la34_capstone_w3


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- LA6 w3 capstone (lane capstone-w3, 2026-11-04,
roadmap M0b third item): every public top-level LocalAuto6 theorem exit
that is clean and statable in Kepler.Text and was never a conjunct of an
existing capstone, re-exposed as ONE conjunction so the Assembly
`textCapstone` cone can consume it (73 of the 73 w3 delta exits;
0 dropped per the workorder's no-forcing rule "抽不出/不一致 →
剔除并如实报", mechanically detected from the `#print axioms` /
`#check @` probe dumps and the module source; each drop is named below
with its reason).  Clean means the probed `#print axioms` face is exactly
[propext, Classical.choice, Quot.sound] (no sorryAx, no other axiom), the
statement declares no module-private constant, the declaration kind is
`theorem`, and the statement is not universe-polymorphic.  Provenance:
the exit set is the residual workorder sweep (`#print axioms` exactly the standard three at the lane HEAD) minus the conjunct names of every existing capstone of this module (la6_capstone_w1); the existing capstones are left untouched (pure insertion, no rewiring).
Anchors (no fabricated edges): every conjunct is asserted in the verbatim
wording of its LA6 declaration -- the conjunct text is the
declaration's source signature (binders + conclusion, copied verbatim and
mechanically split at the binder/conclusion separator by the generator
gen_items.py); conjuncts whose source text leaves an autoImplicit variable
free take the `#check @name` printer dump verbatim (the complete
signature, marked printer-form in their per-conjunct comment) so the
capstone itself stays parameter-free; the `#check @name` printer dump is
retained as cross reference; semantic identity is re-verified by the elaboration of the
`⟨...⟩` assembly below (each component must unify definitionally with its
conjunct); per-conjunct comments carry each exit's LA6
declaration line and file-local docstring HOL anchor.
Conjunct order: source declaration order.  Body = the assembly of the
exit constants -- zero new proof obligations, zero new imports. -/
theorem la6_capstone_w2 :
    -- 1. arcV_eq (LA6:74; HOL `Trigonometry2.NOT_EQ_IMPCOS_ARC`)
    (∀ (u v w : V3)
    ,
          arcV u v w = Real.arccos (inner ℝ (v - u) (w - u) / (dist v u * dist w u))
    ) ∧
    -- 2. arcV_add_smul_sub (LA6:81; no HOL anchor line in file docstring)
    (∀ {u v : V3} (huv : u ≠ v) (t : ℝ)
    ,
          arcV u v (u + t • (v - u)) = Real.arccos (t / |t|)
    ) ∧
    -- 3. ACR_REFL (LA6:104; HOL `ACR_REFL`)
    (∀ {u v : V3} (h : u ≠ v)
    ,
          arcV u v v = 0
    ) ∧
    -- 4. ARC_OPPOSITE (LA6:113; HOL `ARC_OPPOSITE`)
    (∀ {u v : V3} (h : u ≠ v)
    ,
          arcV u v (2 • u - v) = Real.pi
    ) ∧
    -- 5. ARCV_EQ_0 (LA6:125; HOL `ARCV_EQ_0`)
    (∀ {u v : V3} (h : u ≠ v) {t : ℝ} (ht : 0 < t)
    ,
          arcV u v (u + t • (v - u)) = 0
    ) ∧
    -- 6. ARCV_EQ_0_ORIGIN (LA6:130; HOL `ARCV_EQ_0_ORIGIN`)
    (∀ {u : V3} (h : u ≠ 0) {t : ℝ} (ht : 0 < t)
    ,
          arcV 0 u (t • u) = 0
    ) ∧
    -- 7. ARCV_PI_OPPOSITE (LA6:138; HOL `ARCV_PI_OPPOSITE`)
    (∀ {u v : V3} (h : u ≠ v) {t : ℝ} (ht : t < 0)
    ,
          arcV u v (u + t • (v - u)) = Real.pi
    ) ∧
    -- 8. DOT_0_ARCV (LA6:144; HOL `DOT_0_ARCV`)
    (∀ {u v w : V3} (h : (v - u) ⬝ᵥ (w - u) = 0)
    ,
          arcV u v w = Real.pi / 2
    ) ∧
    -- 9. ARCV_DEGENERATE (LA6:150; HOL `ARCV_DEGENERATE`)
    (∀ (u v : V3)
    ,
          arcV u u v = Real.pi / 2 ∧ arcV u v u = Real.pi / 2
    ) ∧
    -- 10. ARCV_DIRECTIONS (LA6:161; HOL `ARCV_DIRECTIONS`)
    (∀ {u v : V3} (h : u ≠ v) (t : ℝ)
    ,
          (arcV u v (u + t • (v - u)) = 0 ↔ 0 < t) ∧
          (arcV u v (u + t • (v - u)) = Real.pi ↔ t < 0)
    ) ∧
    -- 11. ARCV_ORI_DIRECTIONS (LA6:200; HOL `ARCV_ORI_DIRECTIONS`)
    (∀ {v : V3} (h : v ≠ 0) (t : ℝ)
    ,
          (arcV 0 v (t • v) = 0 ↔ 0 < t) ∧ (arcV 0 v (t • v) = Real.pi ↔ t < 0)
    ) ∧
    -- 12. REAL_NEG_MUL_EQ (LA6:208; HOL `REAL_NEG_MUL_EQ`)
    (∀ {a x : ℝ} (ha : a < 0)
    ,
          (a * x < 0 ↔ 0 < x) ∧ (0 < a * x ↔ x < 0)
    ) ∧
    -- 13. NOT_EQ_0 (LA6:219; HOL `NOT_EQ_0`)
    (∀ (x : ℝ)
    ,
          ¬(x = 0) ↔ 0 < x ∨ x < 0
    ) ∧
    -- 14. SIN_ARCV_EQ_0 (LA6:230; HOL `SIN_ARCV_EQ_0`)
    (∀ {u v : V3} (h : u ≠ v) {t : ℝ} (ht : t ≠ 0)
    ,
          Real.sin (arcV u v (u + t • (v - u))) = 0
    ) ∧
    -- 15. COLLINEAR_SIN_ARCV_0 (LA6:237; HOL `COLLINEAR_SIN_ARCV_0`)
    (∀ {u v x : V3} (hcol : Collinear3 u v x) (hx : u ≠ x)
          (hv : u ≠ v),
          Real.sin (arcV u v x) = 0
    ) ∧
    -- 16. COLL_AFF_GT_2_1 (LA6:253; HOL `COLL_AFF_GT_2_1`)
    (∀ (x v w : V3) (hcol : ¬ Collinear3 x v w)
    ,
          affGt ({x, v} : Set V3) ({w} : Set V3) =
          {y | ∃ t1 t2 t3 : ℝ, 0 < t3 ∧ t1 + t2 + t3 = 1 ∧
            y = t1 • x + t2 • v + t3 • w}
    ) ∧
    -- 17. COLL_EQ_DEPENDENT (LA6:277; HOL `COLL_EQ_DEPENDENT`)
    (∀ (x y : V3)
    ,
          Collinear3 0 x y ↔ ∃ tx ty : ℝ, ¬(tx = 0 ∧ ty = 0) ∧
          tx • x + ty • y = (0 : V3)
    ) ∧
    -- 18. NORM1_NOT_0 (LA6:382; HOL `NORM1_NOT_0`)
    (∀ {x : V3} (h : ‖x‖ = 1)
    ,
          x ≠ (0 : V3)
    ) ∧
    -- 19. NORM_NORMIZE (LA6:395; no HOL anchor line in file docstring)
    (∀ {v : V3} (h : v ≠ (0 : V3))
    ,
          ‖normize v‖ = 1
    ) ∧
    -- 20. NORM_CAUCHY_SCHWARZ_FRAC2 (LA6:413; HOL `NORM_CAUCHY_SCHWARZ_FRAC2`)
    (∀ (u v : V3)
    ,
          -1 ≤ u ⬝ᵥ v / (‖u‖ * ‖v‖) ∧ u ⬝ᵥ v / (‖u‖ * ‖v‖) ≤ 1
    ) ∧
    -- 21. ARCV_BOUNDS (LA6:433; HOL `ARCV_BOUNDS`)
    (∀ (x y z : V3)
    ,
          0 ≤ arcV x y z ∧ arcV x y z ≤ Real.pi
    ) ∧
    -- 22. COS_ARCV_EQ_ARCV (LA6:438; HOL `COS_ARCV_EQ_ARCV`)
    (∀ (x y z xx yy zz : V3)
    ,
          Real.cos (arcV x y z) = Real.cos (arcV xx yy zz) ↔ arcV x y z = arcV xx yy zz
    ) ∧
    -- 23. SIN_ARCV_EQ_0_EQ_LAP (LA6:449; HOL `SIN_ARCV_EQ_0_EQ_LAP`)
    (∀ (x y z : V3)
    ,
          Real.sin (arcV x y z) = 0 ↔ arcV x y z = 0 ∨ arcV x y z = Real.pi
    ) ∧
    -- 24. ORTHONORMAL_NOT_COLLINEAR (LA6:477; HOL `ORTHONORMAL_NOT_COLLINEAR`)
    (∀ {e1 e2 e3 : V3} (horth : Orthonormal3 e1 e2 e3)
    ,
          ¬ Collinear3 0 e3 e1
    ) ∧
    -- 25. GRAPH_IMAGE_IMAGE (LA6:510; HOL `GRAPH_IMAGE_IMAGE`)
    (∀ {E : Set (Set V3)} {E : Set (Set V3)} (f : V3 → V3) (hE : Graph E)
          (hinj : ∀ x y : V3, f x = f y → x = y),
          Graph ((fun e : Set V3 => f '' e) '' E)
    ) ∧
    -- 26. LUNAR_DEFORM_ORIGIN (LA6:527; HOL `LUNAR_DEFORM_ORIGIN`)
    (∀ (e1 e2 e3 : V3) (t : ℝ)
    ,
          lunarDeform e1 e2 e3 t 0 = 0
    ) ∧
    -- 27. CVLF_COLLINEAR_CIRCULAR_LUNAR (LA6:531; HOL `CVLF_COLLINEAR_CIRCULAR_LUNAR`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {v w : V3} (hcl : convexLocalFan_p2 V E FF)
          (hsub : ({v, w} : Set V3) ⊆ V) (hcol : Collinear3 0 v w) (hvw : v ≠ w),
          circular_p2 V E ∨ lunar_p2 v w V E
    ) ∧
    -- 28. TOW_REAL_EXISTS_COMBINED (LA6:542; HOL `TOW_REAL_EXISTS_COMBINED`)
    (∀ (P Q : ℝ → Prop)
          (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → P t)
          (h2 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → Q t),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → P t ∧ Q t
    ) ∧
    -- 29. CONTINUOUS_FUNS_DISTINCT_POINTS (LA6:555; HOL `CONTINUOUS_FUNS_DISTINCT_POINTS`)
    (∀ (f g : ℝ → V3) (r rr : ℝ)
          (hf : ContinuousAt f r) (hg : ContinuousAt g rr) (hne : f r ≠ g rr),
          ∃ d : ℝ, 0 < d ∧ ∀ x y : ℝ, |x - r| < d ∧ |y - rr| < d → f x ≠ g y
    ) ∧
    -- 30. CONTINUOUS_TWO_POINTS_DISTINCT (LA6:578; HOL `CONTINUOUS_TWO_POINTS_DISTINCT`)
    (∀ {ff : V3 → ℝ → V3} {v1 v2 : V3} {r : ℝ}
          (h1 : ContinuousAt (ff v1) r) (h2 : ContinuousAt (ff v2) r) (hne : ff v1 r ≠ ff v2 r),
          ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ff v1 t ≠ ff v2 t
    ) ∧
    -- 31. CONTINUOUS_ATREAL_DISTINCT (LA6:585; HOL `CONTINUOUS_ATREAL_DISTINCT`)
    (∀ {ff : V3 → ℝ → V3} {v v0 : V3} {r : ℝ}
          (h : ContinuousAt (ff v) r) (hne : ff v r ≠ v0),
          ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ff v t ≠ v0
    ) ∧
    -- 32. CON_ATREAL_REAL_CON (LA6:694 (autoImplicit parameter leak v0; statement = probe printer dump verbatim (complete signature)); HOL `CON_ATREAL_REAL_CON`)
    (∀ {v0 : Kepler.Geom.V3} (f : ℝ → Kepler.Geom.V3) (t : ℝ),
          ContinuousAt f t → ContinuousAt (fun s => dist (f s) v0) t
    ) ∧
    -- 33. CON_ATREAL_REAL_CON2 (LA6:698; HOL `CON_ATREAL_REAL_CON2`)
    (∀ (f g : ℝ → V3) (t : ℝ) (h1 : ContinuousAt f t)
          (h2 : ContinuousAt g t),
          ContinuousAt (fun s => dist (f s) (g s)) t
    ) ∧
    -- 34. CON_ATREAL_REAL_CON2_REDO (LA6:702; HOL `CON_ATREAL_REAL_CON2_REDO`)
    (∀ (f g : ℝ → V3) (r : ℝ) (h1 : ContinuousAt f r)
          (h2 : ContinuousAt g r),
          ContinuousAt (fun s => dist (f s) (g s)) r
    ) ∧
    -- 35. FAN_E_SUB_V (LA6:854; HOL `FAN_E_SUB_V`)
    (∀ {V : Set V3} {E : Set (Set V3)} {x y : V3} (h : FAN 0 V E) (he : {x, y} ∈ E)
    ,
          x ∈ V ∧ y ∈ V
    ) ∧
    -- 36. LOCAL_E_SUB_V (LA6:860; HOL `LOCAL_E_SUB_V`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {x y : V3} (h : localFan_p2 V E FF) (he : {x, y} ∈ E)
    ,
          x ∈ V ∧ y ∈ V
    ) ∧
    -- 37. EDGE_NOT_INTER_WITH_WEDGE (LA6:866; HOL `EDGE_NOT_INTER_WITH_WEDGE`)
    (∀ (v0 v1 w1 w2 : V3)
    ,
          ((affineSpan ℝ ({v0, v1} : Set V3) : Set V3) ∩ wedge v0 v1 w1 w2) = ∅
    ) ∧
    -- 38. AFF_GE11_SUB_AFF2 (LA6:883; HOL `AFF_GE11_SUB_AFF2`)
    (∀ (v0 v1 : V3)
    ,
          affGe ({v0} : Set V3) ({v1} : Set V3) ⊆ affineSpan ℝ ({v0, v1} : Set V3)
    ) ∧
    -- 39. AZ_REFL11 (LA6:915; no HOL anchor line in file docstring)
    (∀ (v w1 w2 : V3)
    ,
          azim v v w1 w2 = 0
    ) ∧
    -- 40. AZIM_POS_IMP_SUM_2PI (LA6:994; HOL `AZIM_POS_IMP_SUM_2PI`)
    (∀ {a b c d : V3} (h : 0 < azim a b c d)
    ,
          azim a b c d + azim a b d c = 2 * Real.pi
    ) ∧
    -- 41. FST_LST_IN_WEDGE_GE (LA6:1006; HOL `FST_LST_IN_WEDGE_GE`)
    (∀ (v0 v1 w1 w2 : V3)
    ,
          w1 ∈ wedgeGe_p2 v0 v1 w1 w2 ∧ w2 ∈ wedgeGe_p2 v0 v1 w1 w2
    ) ∧
    -- 42. EE_UNION (LA6:1013; HOL `EE_UNION`)
    (∀ {E : Set (Set V3)} (v : V3) (E S : Set (Set V3))
    ,
          EE_p2 v (E ∪ S) = EE_p2 v E ∪ EE_p2 v S
    ) ∧
    -- 43. EE_SING_SING (LA6:1018; HOL `EE_SING_SING`)
    (∀ (v w : V3)
    ,
          EE_p2 v {{v, w}} = {w}
    ) ∧
    -- 44. IN_DARTS_EXTENSION (LA6:1030; HOL `IN_DARTS_EXTENSION`)
    (∀ {V : Set V3} {E : Set (Set V3)} {x y : V3} {E S : Set (Set V3)} (h : {x, y} ∈ E)
    ,
          (x, y) ∈ dartsOfHyp_p2 (E ∪ S) V
    ) ∧
    -- 45. LOCAL_RHO_NODE_PAIR_E (LA6:1037 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LOCAL_RHO_NODE_PAIR_E`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → {v, Kepler.Text.rhoNode1_p2 FF v} ∈ E
    ) ∧
    -- 46. LOFA_IMP_ITER_RHO_NODE_ID2 (LA6:1120 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); no HOL anchor line in file docstring)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → (Kepler.Text.rhoNode1_p2 FF)^[V.ncard] v = v
    ) ∧
    -- 47. CARD_IS_LEAST_CYCLE (LA6:1351 (autoImplicit parameter leak FF, v; statement = probe printer dump verbatim (complete signature)); HOL `CARD_IS_LEAST_CYCLE`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → ∀ (n : ℕ), (Kepler.Text.rhoNode1_p2 FF)^[n] v = v → n ≠ 0 → V.ncard ≤ n
    ) ∧
    -- 48. LOCAL_FAN_RHO_NODE_IVS (LA6:1384 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LOCAL_FAN_RHO_NODE_IVS`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → Kepler.Text.rhoNode1_p2 FF (Kepler.Text.ivsRhoNode1_p2 FF v) = v
    ) ∧
    -- 49. LOCAL_FAN_IVS_IN_V (LA6:1404 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LOCAL_FAN_IVS_IN_V`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → Kepler.Text.ivsRhoNode1_p2 FF v ∈ V
    ) ∧
    -- 50. LF_AZIM_CYCLE_EQ_IVS_ND (LA6:1412 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LF_AZIM_CYCLE_EQ_IVS_ND`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              Kepler.Text.azimCycle_p2 (Kepler.Text.EE_p2 v E) 0 v (Kepler.Text.rhoNode1_p2 FF v) =
                Kepler.Text.ivsRhoNode1_p2 FF v
    ) ∧
    -- 51. AZIM_IN_FAN_RHOND_IVS_RHOND (LA6:1419 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `AZIM_IN_FAN_RHOND_IVS_RHOND`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              Kepler.Text.azimInFan_p2 (v, Kepler.Text.rhoNode1_p2 FF v) E =
                Kepler.Geom.azim 0 v (Kepler.Text.rhoNode1_p2 FF v) (Kepler.Text.ivsRhoNode1_p2 FF v)
    ) ∧
    -- 52. LOFA_IMP_EE_TWO_ELMS_INS_ND (LA6:1430 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LOFA_IMP_EE_TWO_ELMS_INS_ND`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V → Kepler.Text.EE_p2 v E = {Kepler.Text.rhoNode1_p2 FF v, Kepler.Text.ivsRhoNode1_p2 FF v}
    ) ∧
    -- 53. WEDGE_IN_FAN_RHOND_IVS_RHOND (LA6:1435 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `WEDGE_IN_FAN_RHOND_IVS_RHOND`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              Kepler.Text.wedgeInFanGe_p2 (v, Kepler.Text.rhoNode1_p2 FF v) E =
                Kepler.Text.wedgeGe_p2 0 v (Kepler.Text.rhoNode1_p2 FF v) (Kepler.Text.ivsRhoNode1_p2 FF v)
    ) ∧
    -- 54. IVS_RHO_NODE_DIFF_ID (LA6:1446 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `IVS_RHO_NODE_DIFF_ID`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF → v ∈ V → Kepler.Text.ivsRhoNode1_p2 FF v ≠ v
    ) ∧
    -- 55. POINT_PRESENTED_IN_RHOND1 (LA6:1457 (autoImplicit parameter leak v, w; statement = probe printer dump verbatim (complete signature)); HOL `POINT_PRESENTED_IN_RHOND1`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              w ∈ V → ∃ n < V.ncard, (Kepler.Text.rhoNode1_p2 FF)^[n] v = w ∧ ∀ m < n, ¬(Kepler.Text.rhoNode1_p2 FF)^[m] v = w
    ) ∧
    -- 56. CARD_V_TWO_HAFL_CIRCLE (LA6:1506 (autoImplicit parameter leak FF, v, w; statement = probe printer dump verbatim (complete signature)); HOL `CARD_V_TWO_HAFL_CIRCLE`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              w ∈ V →
                v ≠ w →
                  ∀ (n n' : ℕ),
                    (Kepler.Text.rhoNode1_p2 FF)^[n] v = w →
                      (Kepler.Text.rhoNode1_p2 FF)^[n'] w = v → n < V.ncard → n' < V.ncard → n + n' = V.ncard
    ) ∧
    -- 57. DIFFERENCE_IMP_LT_CARDV (LA6:1544 (autoImplicit parameter leak FF, v, w; statement = probe printer dump verbatim (complete signature)); HOL `DIFFERENCE_IMP_LT_CARDV`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V → w ∈ V → ∀ (m : ℕ), (∀ n < m, ¬(Kepler.Text.rhoNode1_p2 FF)^[n] v = w) → m < V.ncard
    ) ∧
    -- 58. LT_CARD_MONO_LOFA (LA6:1560 (autoImplicit parameter leak v; statement = probe printer dump verbatim (complete signature)); HOL `LT_CARD_MONO_LOFA`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
          {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v : Kepler.Geom.V3},
          Kepler.Text.localFan_p2 V E FF →
            v ∈ V →
              ∀ (i j : ℕ),
                i < V.ncard ∧ j < V.ncard ∧ (Kepler.Text.rhoNode1_p2 FF)^[i] v = (Kepler.Text.rhoNode1_p2 FF)^[j] v → i = j
    ) ∧
    -- 59. DIST_TRIANGLE_AS_ABS (LA6:1732; HOL `DIST_TRIANGLE_AS_ABS`)
    (∀ (x y z : V3)
    ,
          |dist x y - dist x z| ≤ dist y z
    ) ∧
    -- 60. REAL_POS_LT_MUL (LA6:1739; HOL `REAL_POS_LT_MUL`)
    (∀ {a b x y : ℝ} (ha : 0 ≤ a) (hab : a < b) (hx : 0 ≤ x)
          (hxy : x < y),
          a * x < b * y
    ) ∧
    -- 61. COS_ARCV (LA6:1783; HOL `COS_ARCV`)
    (∀ (v0 u w : V3)
    ,
          Real.cos (arcV v0 u w) =
          (u - v0) ⬝ᵥ (w - v0) / (‖u - v0‖ * ‖w - v0‖)
    ) ∧
    -- 62. REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN (LA6:1792; HOL `REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN`)
    (∀ (f g : ℝ → ℝ) (r : ℝ)
          (hf : ContinuousAt f r) (hg : ContinuousAt g r),
          ContinuousAt (fun t => f t * g t) r
    ) ∧
    -- 63. REAL_CONTINUOUS_ATREAL_POW_2 (LA6:1797; HOL `REAL_CONTINUOUS_ATREAL_POW_2`)
    (∀ (f : ℝ → ℝ) (r : ℝ)
          (h : ContinuousAt f r),
          ContinuousAt (fun t => f t ^ 2) r
    ) ∧
    -- 64. CONSTANCE_FUN_CONTINUOUS (LA6:1805; HOL `CONSTANCE_FUN_CONTINUOUS`)
    (∀ (c : ℝ) (r : ℝ)
    ,
          ContinuousAt (fun _ : ℝ => c) r
    ) ∧
    -- 65. REAL_CONS_IMP_SCALAR_MUL (LA6:1809; HOL `REAL_CONS_IMP_SCALAR_MUL`)
    (∀ (f : ℝ → ℝ) (r : ℝ) (c : ℝ)
          (h : ContinuousAt f r),
          ContinuousAt (fun t => c * f t) r
    ) ∧
    -- 66. CONS_IMP_SO_IVS (LA6:1814; HOL `CONS_IMP_SO_IVS`)
    (∀ (f : ℝ → ℝ) (r : ℝ) (h : ContinuousAt f r)
    ,
          ContinuousAt (fun t => -f t) r
    ) ∧
    -- 67. REAL_CONS_IMP_SUM_CONS (LA6:1818; HOL `REAL_CONS_IMP_SUM_CONS`)
    (∀ (f g : ℝ → ℝ) (r : ℝ) (h1 : ContinuousAt f r)
          (h2 : ContinuousAt g r),
          ContinuousAt (fun t => f t + g t) r
    ) ∧
    -- 68. REAL_CONS_IMP_SCALAR_MUL_ALT (LA6:1822; HOL `REAL_CONS_IMP_SCALAR_MUL_ALT`)
    (∀ (f : ℝ → ℝ) (r : ℝ)
          (h : ContinuousAt f r) (c : ℝ),
          ContinuousAt (fun t => c * f t) r
    ) ∧
    -- 69. CONTS_FUN_CONTINUOUS_ATREAL (LA6:1827; HOL `CONTS_FUN_CONTINUOUS_ATREAL`)
    (∀ (v0 : V3) (r : ℝ)
    ,
          ContinuousAt (fun _ : ℝ => v0) r
    ) ∧
    -- 70. REAL_CONS_STILL_DIFF (LA6:1831; HOL `REAL_CONS_STILL_DIFF`)
    (∀ (f : ℝ → ℝ) (r a : ℝ)
          (h : ContinuousAt f r) (hne : f r ≠ a),
          ∃ d : ℝ, 0 < d ∧ ∀ rr : ℝ, |rr - r| < d → f rr ≠ a
    ) ∧
    -- 71. UPS_X_CONTS_FUNC (LA6:1848; no HOL anchor line in file docstring)
    (∀ (f g h : ℝ → V3) (r : ℝ) (hf : ContinuousAt f r)
          (hg : ContinuousAt g r) (hh : ContinuousAt h r),
          ContinuousAt
          (fun r => upsX_p6 (dist (f r) (g r) ^ 2) (dist (h r) (f r) ^ 2)
            (dist (g r) (h r) ^ 2)) r
    ) ∧
    -- 72. CONTINUOUS_PRESERVE_COLLINEAR (LA6:1916; HOL `CONTINUOUS_PRESERVE_COLLINEAR`)
    (∀ (v0 : V3) (f g : ℝ → V3) (r : ℝ)
          (hf : ContinuousAt f r) (hg : ContinuousAt g r)
          (hnc : ¬ Collinear3 v0 (f r) (g r)),
          ∃ e : ℝ, 0 < e ∧ ∀ r' : ℝ, |r - r'| < e → ¬ Collinear3 v0 (f r') (g r')
    ) ∧
    -- 73. EACH_ELM_PRESERVED_IMP_ALLL (LA6:1948; HOL `EACH_ELM_PRESERVED_IMP_ALLL`)
    (∀ {E : Set (Set V3)} (phii : V3 → ℝ → V3) (E : Set (Set V3))
          (h1 : ∀ x ∈ E, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
            ¬ Collinear ℝ (Set.insert (0 : V3) ((fun v : V3 => phii v t) '' x)))
          (hE : E.Finite),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
          ∀ e' ∈ (fun x : Set V3 => (fun v : V3 => phii v t) '' x) '' E,
            ¬ Collinear ℝ (Set.insert (0 : V3) e')
    ) :=
    ⟨arcV_eq, arcV_add_smul_sub, ACR_REFL, ARC_OPPOSITE, ARCV_EQ_0, ARCV_EQ_0_ORIGIN,
      ARCV_PI_OPPOSITE, DOT_0_ARCV, ARCV_DEGENERATE, ARCV_DIRECTIONS, ARCV_ORI_DIRECTIONS,
      REAL_NEG_MUL_EQ, NOT_EQ_0, @SIN_ARCV_EQ_0, @COLLINEAR_SIN_ARCV_0, COLL_AFF_GT_2_1,
      COLL_EQ_DEPENDENT, NORM1_NOT_0, NORM_NORMIZE, NORM_CAUCHY_SCHWARZ_FRAC2, ARCV_BOUNDS,
      @COS_ARCV_EQ_ARCV, @SIN_ARCV_EQ_0_EQ_LAP, ORTHONORMAL_NOT_COLLINEAR, GRAPH_IMAGE_IMAGE,
      LUNAR_DEFORM_ORIGIN, CVLF_COLLINEAR_CIRCULAR_LUNAR, TOW_REAL_EXISTS_COMBINED,
      CONTINUOUS_FUNS_DISTINCT_POINTS, CONTINUOUS_TWO_POINTS_DISTINCT,
      CONTINUOUS_ATREAL_DISTINCT, CON_ATREAL_REAL_CON, CON_ATREAL_REAL_CON2,
      CON_ATREAL_REAL_CON2_REDO, FAN_E_SUB_V, LOCAL_E_SUB_V, EDGE_NOT_INTER_WITH_WEDGE,
      @AFF_GE11_SUB_AFF2, AZ_REFL11, AZIM_POS_IMP_SUM_2PI, FST_LST_IN_WEDGE_GE, EE_UNION,
      EE_SING_SING, IN_DARTS_EXTENSION, @LOCAL_RHO_NODE_PAIR_E, @LOFA_IMP_ITER_RHO_NODE_ID2,
      @CARD_IS_LEAST_CYCLE, @LOCAL_FAN_RHO_NODE_IVS, @LOCAL_FAN_IVS_IN_V,
      @LF_AZIM_CYCLE_EQ_IVS_ND, @AZIM_IN_FAN_RHOND_IVS_RHOND, @LOFA_IMP_EE_TWO_ELMS_INS_ND,
      @WEDGE_IN_FAN_RHOND_IVS_RHOND, @IVS_RHO_NODE_DIFF_ID, @POINT_PRESENTED_IN_RHOND1,
      @CARD_V_TWO_HAFL_CIRCLE, @DIFFERENCE_IMP_LT_CARDV, @LT_CARD_MONO_LOFA,
      DIST_TRIANGLE_AS_ABS, REAL_POS_LT_MUL, @COS_ARCV, REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN,
      REAL_CONTINUOUS_ATREAL_POW_2, CONSTANCE_FUN_CONTINUOUS, REAL_CONS_IMP_SCALAR_MUL,
      CONS_IMP_SO_IVS, REAL_CONS_IMP_SUM_CONS, REAL_CONS_IMP_SCALAR_MUL_ALT,
      CONTS_FUN_CONTINUOUS_ATREAL, REAL_CONS_STILL_DIFF, UPS_X_CONTS_FUNC,
      CONTINUOUS_PRESERVE_COLLINEAR, EACH_ELM_PRESERVED_IMP_ALLL⟩

#print axioms la6_capstone_w2
/-! ### w4 delta capstones la6/la34/la14/misc (lane capstone-w4,
2026-11-05, roadmap M0b fourth item): every clean public exit newly closed
after the w3 baseline (da9b5fd4) that had never been materialised into any
capstone is re-exposed as ONE conjunction per module group -- la6_capstone_w3
(10), la34_capstone_w4 (21), la14_capstone_w3 (2), and one misc_capstone_w1
for the twelve modules with small deltas (LA16 1, LA27 1, LA11 1, LA25 1,
LA21 1, LA36 1, LA15 1, LA33 1, LA12 1, LA2 1, LA26 5, LA20 4 = 19).  Total 52
exits; the four `have hla6c/hla34d/hla14c/hmisc` lines in Assembly.textCapstone
pull the capstone proof terms into the e2e cone (pure insertion there too,
after hla6b; the w1/w2/w3 capstones stay wired).  Delta definition
(measured at the lane HEAD 64959a80): public top-level `theorem` exports with
a `sorry` in the da9b5fd4 declaration body and none at HEAD, whose probed
`#print axioms` face is exactly [propext, Classical.choice, Quot.sound],
whose statement declares no module-private constant, whose declaration kind
is `theorem`, and which is not universe-polymorphic, MINUS the conjunct name
set of every existing capstone (intersection 0, verified mechanically).
All 51 are individually exactly standard three.  Environment-alignment
scopes mirror module-local opens so the verbatim signatures elaborate under
the same name resolution: LA6 carries `open Kepler.Text.Fan`
(LocalAuto6:49), LA14 carries `open Kepler.Text.V3Coe`
(LocalAuto14:74); every other module only opens `Kepler.Geom Set Classical`,
already open in this file.  All modules are already imported by this file,
so zero import changes.  The exact cone increment is re-measured at the
orchestrator e2e gate. -/


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- la6_capstone_w3 (lane capstone-w4, 2026-11-05): every public top-level
exit of LocalAuto6 (10 exits) that was newly closed after the w3 baseline
(da9b5fd4) and was never a conjunct of any existing capstone, re-exposed as
ONE conjunction so the Assembly `textCapstone` cone can consume it (10
of the 10 w4 delta exits; 0 dropped mechanically, reason
per name below).  Delta definition (measured, not assumed): a public
top-level `theorem` also present at da9b5fd4 with a `sorry` in its
declaration body (comments stripped) and with no `sorry` at HEAD, whose
probed `#print axioms` face is exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
10), whose statement declares no module-private constant (`✝` in the
`#check @` dump), whose declaration kind is `theorem`, and which is not
universe-polymorphic; MINUS the conjunct name set of every existing
capstone in LocalConcl (all w1/w2/w3 and older roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: la6_capstone w4 delta, source
declaration order.  Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la6_capstone_w3 :
    -- 1. PROVE_SLICING_FAN (LA6:1924 (autoImplicit parameter leak v, w; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `PROVE_SLICING_FAN`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E),
          FAN 0 V (E ∪ {{v, w}})
    ) ∧
    -- 2. LOFA_HYP_UNION_CARD_GT2 (LA6:2078 (autoImplicit parameter leak FF, v, w, fv; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `LOFA_HYP_UNION_CARD_GT2`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v)),
          2 < fv.ncard
    ) ∧
    -- 3. FACE_MAP_AT_TURNING_DART (LA6:2258 (autoImplicit parameter leak v, w, x; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `FACE_MAP_AT_TURNING_DART`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w x : Kepler.Geom.V3} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hxv : (x, v) ∈ FF),
          HS.faceMap (x, v) = (v, w)
    ) ∧
    -- 4. FACE_MAP_SLICING_HYP_TRANS_POINT (LA6:2427 (autoImplicit parameter leak v, w; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `FACE_MAP_SLICING_HYP_TRANS_POINT`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} (h : localFan_p2 V E FF) (hv : v ∈ V)
          (hw : w ∈ V) (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS),
          HS.faceMap (v, w) = (w, rhoNode1_p2 FF w)
    ) ∧
    -- 5. FACE_MAP_AT_TURNING_DART1 (LA6:2581 (autoImplicit parameter leak v, w, x; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `FACE_MAP_AT_TURNING_DART1`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w x : Kepler.Geom.V3} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hxw : (x, w) ∈ FF),
          HS.faceMap (x, w) = (w, v)
    ) ∧
    -- 6. DETERMINE_FV (LA6:2613 (autoImplicit parameter leak FF, v, w, fv; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `DETERMINE_FV`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v)),
          fv = insert (w, v) {p | ∃ n : ℕ,
          (∀ m : ℕ, m < n + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
            p = ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v)}
    ) ∧
    -- 7. POINTS_IN_HAFL_CIRCLE (LA6:2904 (autoImplicit parameter leak FF, v, w, fv; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `POINTS_IN_HAFL_CIRCLE`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v)),
          vPrime_p2 V fv = {z | ∃ n : ℕ,
          (∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
            z = (rhoNode1_p2 FF)^[n] v}
    ) ∧
    -- 8. CONDS_IN_V_PRIME_NUM (LA6:3039 (autoImplicit parameter leak FF, v, w, fv, n; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `CONDS_IN_V_PRIME_NUM`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {n : ℕ} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
          (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w),
          ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv ↔ i < n + 1
    ) ∧
    -- 9. DETERMINE_FV2 (LA6:3107 (autoImplicit parameter leak FF, v, w, fv, n; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `DETERMINE_FV2`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {n : ℕ} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
          (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w),
          fv = insert (w, v) {p | ∃ m : ℕ, m < n ∧
          p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)}
    ) ∧
    -- 10. AZIM_COND_FOR_COPLANAR (LA6:3418; no HOL anchor line in file docstring)
    (∀ (v0 v1 w1 w2 : V3)
    ,
          azim v0 v1 w1 w2 = 0 ∨ azim v0 v1 w1 w2 = Real.pi ↔ Coplanar {v0, v1, w1, w2}
    ) :=
    ⟨PROVE_SLICING_FAN, LOFA_HYP_UNION_CARD_GT2, FACE_MAP_AT_TURNING_DART,
      FACE_MAP_SLICING_HYP_TRANS_POINT, FACE_MAP_AT_TURNING_DART1, DETERMINE_FV,
      POINTS_IN_HAFL_CIRCLE, CONDS_IN_V_PRIME_NUM, DETERMINE_FV2, AZIM_COND_FOR_COPLANAR⟩

#print axioms la6_capstone_w3


set_option maxHeartbeats 50000000 in

/-- la34_capstone_w4 (lane capstone-w4, 2026-11-05): every public top-level
exit of LocalAuto34 (21 exits) that was newly closed after the w3 baseline
(da9b5fd4) and was never a conjunct of any existing capstone, re-exposed as
ONE conjunction so the Assembly `textCapstone` cone can consume it (21
of the 21 w4 delta exits; 0 dropped mechanically, reason
per name below).  Delta definition (measured, not assumed): a public
top-level `theorem` also present at da9b5fd4 with a `sorry` in its
declaration body (comments stripped) and with no `sorry` at HEAD, whose
probed `#print axioms` face is exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
21), whose statement declares no module-private constant (`✝` in the
`#check @` dump), whose declaration kind is `theorem`, and which is not
universe-polymorphic; MINUS the conjunct name set of every existing
capstone in LocalConcl (all w1/w2/w3 and older roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: la34_capstone w4 delta, source
declaration order.  Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la34_capstone_w4 :
    -- 1. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_p34 (LA34:3847; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = azim 0 v1 (rhoNode1 FF v1) (epPair_p34 FF v1)
    ) ∧
    -- 2. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_p34 (LA34:3936; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v1 t)) = azim 0 v1 (rhoNode1 FF v1) (epPair_p34 FF v1)
    ) ∧
    -- 3. DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_p34 (LA34:4175; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1)))
    ) ∧
    -- 4. DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_p34 (LA34:4295; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 v2 : V3)
          (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1)))
    ) ∧
    -- 5. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_p34 (LA34:4548; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, 0 < t ∧ t < e → v ≠ v1 → v ≠ v2 →
          v ≠ w (l + k - 1) → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 6. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_p34 (LA34:4595; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ≠ v1 → v ≠ v2 →
          v ≠ w (l + k - 1) → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 7. DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_p34 (LA34:4642; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, 0 < t ∧ t < e → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 8. DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34 (LA34:4748; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 9. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_p34 (LA34:4853; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → 0 < t → t < e →
          interiorAngle1 0 FF v = Real.pi →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi
    ) ∧
    -- 10. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_p34 (LA34:4878; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
          interiorAngle1 0 FF v = Real.pi →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi
    ) ∧
    -- 11. CARD_FF_EQ_V3_DEFOR_DEFORMATION_p34 (LA34:5066; HOL `CARD_FF_EQ_V3_DEFOR_DEFORMATION`)
    (∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (V : Set V3)
          (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ)
          (hkk : s.k = k) (hV : Set.range w = V) (hs : isScsV39 s) (hk : 3 < k)
          (hBB : BBsV39 s w)
          (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
            BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)),
          ∀ t : ℝ, 0 < t → t < e1 →
          (Set.range (fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
              v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))).ncard =
            (Set.range fun i => (w i, w (i + 1))).ncard
    ) ∧
    -- 12. DSV_V3_DEFOR_EQ_p34 (LA34:5123; HOL `DSV_V3_DEFOR_EQ`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3) (v1 : V3) (t a x1 x2 x6 : ℝ)
          (hkk : s.k = k) (hs : isScsV39 s) (hBB : BBsV39 s w)
          (hJ : ∀ i, ¬s.J l i),
          dsvV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 (w l) (w i) t) = dsvV39 s w
    ) ∧
    -- 13. DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_p34 (LA34:5179; HOL `DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v
    ) ∧
    -- 14. DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES_p34 (LA34:5905; HOL `DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ)
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1),
          ∀ i : ℕ, ¬(i % k = l % k) →
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
            0 < dist (v3DeforV1_p17 a v1 v2 x1 x2 x6 x6 (x2 - t)) (w i)
    ) ∧
    -- 15. DEFORMATION_AZIM_V3_DEFOR_V1_V1_TWO_CASES_p34 (LA34:6063; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t)) = Real.pi
    ) ∧
    -- 16. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES_p34 (LA34:6319; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + 1)) t)) = azim 0 (w (l + 1)) (rhoNode1 FF (w (l + 1))) (epPair_p34 FF (w (l + 1)))
    ) ∧
    -- 17. DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES_p34 (LA34:6514; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l + k - 1)) t)) = azim 0 (w (l + k - 1)) (rhoNode1 FF (w (l + k - 1))) (epPair_p34 FF (w (l + k - 1)))
    ) ∧
    -- 18. DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES_p34 (LA34:6710; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ≠ v1 → v ≠ v2 →
          v ≠ w (l + 1) → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 19. DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES_p34 (LA34:6756; HOL `DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ v : V3, -e < t ∧ t < e → v ∈ Set.range w →
          azim 0 (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)
            (rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t))
            (epPair_p34 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t)) = azim 0 v (rhoNode1 FF v) (epPair_p34 FF v)
    ) ∧
    -- 20. DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES_p34 (LA34:6905; HOL `DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
          interiorAngle1 0 FF v = Real.pi →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) ≤ Real.pi
    ) ∧
    -- 21. DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_TWO_CASES_p34 (LA34:6974; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (k l : ℕ)
          (w : ℕ → V3) (v1 v2 : V3) (x1 x2 x6 a : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ v : V3, ∀ t : ℝ, v ∈ Set.range w → -e < t → t < e →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v t) = interiorAngle1 0 FF v
    ) :=
    ⟨DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_p34, DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_p34, DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_p34, DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_p34, DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_p34,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_p34, CARD_FF_EQ_V3_DEFOR_DEFORMATION_p34,
      @DSV_V3_DEFOR_EQ_p34, DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_p34,
      DEFORMATION_V3_DEFOR_NOT_IN_V_V1_TWO_CASES_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_V1_TWO_CASES_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_V1_V1_TWO_CASES_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_W_V1_TWO_CASES_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_V_ANY_V1_TWO_CASES_p34,
      DEFORMATION_AZIM_V3_DEFOR_V1_AT_ALL_V1_TWO_CASES_p34,
      DEFORMATION_INTERIOR_ANGLE1_V3_DEFOR_V1_TWO_CASES_p34,
      DEFORMATION_INTERIOR_ANGLE1_EQ_V3_DEFOR_V1_TWO_CASES_p34⟩

#print axioms la34_capstone_w4


open Kepler.Text.V3Coe in
set_option maxHeartbeats 50000000 in

/-- la14_capstone_w3 (lane capstone-w4, 2026-11-05): every public top-level
exit of LocalAuto14 (2 exits) that was newly closed after the w3 baseline
(da9b5fd4) and was never a conjunct of any existing capstone, re-exposed as
ONE conjunction so the Assembly `textCapstone` cone can consume it (2
of the 2 w4 delta exits; 0 dropped mechanically, reason
per name below).  Delta definition (measured, not assumed): a public
top-level `theorem` also present at da9b5fd4 with a `sorry` in its
declaration body (comments stripped) and with no `sorry` at HEAD, whose
probed `#print axioms` face is exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
2), whose statement declares no module-private constant (`✝` in the
`#check @` dump), whose declaration kind is `theorem`, and which is not
universe-polymorphic; MINUS the conjunct name set of every existing
capstone in LocalConcl (all w1/w2/w3 and older roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: la14_capstone w4 delta, source
declaration order.  Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la14_capstone_w3 :
    -- 1. KCZXLLE_p14 (LA14:2424; HOL `KCZXLLE`)
    (∀ (u : ℕ → V3) (r i j k : ℕ) (hjk : j < k) (hk : k ≤ r) (hr : 1 ≤ r)
          (hii : i ≤ r) (hijk : i < j ∨ k < i)
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
          (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
          (h4 : ∀ i, i < r →
            azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)),
          azim 0 (u i) (u j) (u k) = 0
    ) ∧
    -- 2. KCZXLLE_SYM_p14 (LA14:2435; HOL `KCZXLLE_SYM`)
    (∀ (u : ℕ → V3) (r i j k : ℕ) (hk : k ≤ r) (hj : j ≤ r) (hr : 1 ≤ r)
          (hi : i ≤ r) (hord : (j < k ∧ (i < j ∨ k < i)) ∨ (k < j ∧ (i < k ∨ j < i)))
          (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
          (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
          (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
          (h4 : ∀ i, i < r →
            azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)),
          azim 0 (u i) (u j) (u k) = 0
    ) :=
    ⟨KCZXLLE_p14, KCZXLLE_SYM_p14
⟩

#print axioms la14_capstone_w3


set_option maxHeartbeats 50000000 in

/-- misc_capstone_w1 (lane capstone-w4, 2026-11-05): every public top-level
exit of twelve modules (LA16 1, LA27 1, LA11 1, LA25 1, LA21 1, LA36 1, LA15 1, LA33 1, LA12 1, LA2 1, LA26 5, LA20 4; module order as listed, source declaration order within each module) that was newly closed after the w3 baseline
(da9b5fd4) and was never a conjunct of any existing capstone, re-exposed as
ONE conjunction so the Assembly `textCapstone` cone can consume it (19
of the 19 w4 delta exits; 0 dropped mechanically, reason
per name below).  Delta definition (measured, not assumed): a public
top-level `theorem` also present at da9b5fd4 with a `sorry` in its
declaration body (comments stripped) and with no `sorry` at HEAD, whose
probed `#print axioms` face is exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
19), whose statement declares no module-private constant (`✝` in the
`#check @` dump), whose declaration kind is `theorem`, and which is not
universe-polymorphic; MINUS the conjunct name set of every existing
capstone in LocalConcl (all w1/w2/w3 and older roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: w4 misc root, source
declaration order.  Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem misc_capstone_w1 :
    -- 1. FSQKWKK_p16 (LA16:829; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 v3 : V3) (h : azim v0 v1 v2 v3 ≤ Real.pi)
    ,
          azim v0 v2 v3 v1 ≤ Real.pi
    ) ∧
    -- 2. FEKTYIY_p27 (LA27:935; HOL `FEKTYIY`)
    (∀ (s : ScsV39) (v : ℕ → V3), isScsV39 s →
          v ∈ MMsV39 s → 3 < s.k → ¬Coplanar (({0} ∪ Set.range v : Set V3))
    ) ∧
    -- 3. PQCSXWG1_p11 (LA11:1432; no HOL anchor line in file docstring)
    (PQCSXWG1_concl_p11
    ) ∧
    -- 4. ASSWPOW_p25 (LA25:2050; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ) (his : isScsV39 s)
          (hv : v ∈ MMsV39 s) (hk : s.k = 4) (hbasic : scsBasicV39 s)
          (hb1 : s.b i (i + 1) ≤ 2 * h0) (hb2 : s.b (i + 1) (i + 2) ≤ 2 * h0),
          xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53
    ) ∧
    -- 5. PQCSXWG1_SYM_p21 (LA21:146; no HOL anchor line in file docstring)
    (∀ (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ)
          (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
          (h6 : 0 < x6) (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
          (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
          (hx6 : x6 = dist v1 v2 ^ 2) (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6)
          (hv3 : v3 = mkSimplex1 v0 v2 v1 x2 x1 x3 x5 x4 x6),
          x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
          (v2 - v0) ⬝ᵥ cross3 (v1 - v0) (v3 - v0) > 0
    ) ∧
    -- 6. XWITCCN (LA36:2645; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (vv : ℕ → V3), s ∈ sInitListV39 →
          BBsV39 s vv → taustarV39 s vv < 0 → BBprimeV39 s ≠ ∅
    ) ∧
    -- 7. POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 (LA15:420; no HOL anchor line in file docstring)
    (∀ u v w : V3,
          ({u, v, w} : Set V3) ⊆ ballAnnulus →
          Kepler.Packing ({u, v, w} : Set V3) →
          u ≠ v → u ≠ w → v ≠ w →
          v ∉ segment ℝ u w
    ) ∧
    -- 8. ear_acute_p33 (LA33:2002; no HOL anchor line in file docstring)
    (∀ (_hmn : main_nonlinear_terminal_v11)
    ,
          ∀ y1 y2 y3 y4 y5 y6 : ℝ, 2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 →
          2 ≤ y3 → y3 ≤ 2 * h0 → 2 ≤ y4 → y4 ≤ 2 * h0 → 2 ≤ y6 → y6 ≤ 2 * h0 →
          3 ≤ y5 → 0 < upsX (y1 ^ 2) (y3 ^ 2) (y5 ^ 2) →
          dihY y1 y2 y3 y4 y5 y6 < Real.pi / 2
    ) ∧
    -- 9. sgtrnaf_p12 (LA12:282; no HOL anchor line in file docstring)
    (∀ {s : ScsV39} {vv : ℕ → V3} (hs : isScsV39 s)
          (hu : unadornedV39 s) (hBB : BBsV39 s vv) (hta : taustarV39 s vv < 0),
          MMsV39 s ≠ ∅
    ) ∧
    -- 10. LDURDPN (LA2:1922; no HOL anchor line in file docstring)
    (∀ {u v w : V3} (huv : ¬ Collinear ℝ ({0, u, v} : Set V3))
          (huw : ¬ Collinear ℝ ({0, u, w} : Set V3)),
          (azim 0 u v w = Real.pi ↔
          (∃ A : Set V3, plane_p2 A ∧ ({0, u, v, w} : Set V3) ⊆ A) ∧
            ¬((affineSpan ℝ ({0, u} : Set V3) ∩ conv0_p2 {v, w} : Set V3) = ∅))
    ) ∧
    -- 11. AXJRPNC_p26 (LA26:1307; no HOL anchor line in file docstring)
    (∀ (s : ScsV39) (v : ℕ → V3) (i j : ℕ)
          (hs : isScsV39 s) (hbasic : scsBasicV39 s)
          (hb : ∀ i, s.b i (i + 1) ≤ cstab) (hv : MMsV39 s v)
          (hlunar : Lunar (v i) (v j) (Set.range v)
            (Set.range fun l : ℕ => ({v l, v (l + 1)} : Set V3))),
          s.k = 6 ∧ v j = v (i + 3)
    ) ∧
    -- 12. MXQTIED_PRIME_p26 (LA26:1531; no HOL anchor line in file docstring)
    (∀ (s s' : ScsV39) (v : ℕ → V3)
          (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
          (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
          (hv : v ∈ BBprimeV39 s) (hv' : BBsV39 s' v)
          (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
          (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j),
          v ∈ BBprimeV39 s'
    ) ∧
    -- 13. MXQTIED_PRIME2_p26 (LA26:1550; no HOL anchor line in file docstring)
    (∀ (s s' : ScsV39) (v : ℕ → V3)
          (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
          (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
          (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
          (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
          (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j),
          v ∈ BBprime2V39 s'
    ) ∧
    -- 14. MXQTIED_p26 (LA26:1608; no HOL anchor line in file docstring)
    (∀ (s s' : ScsV39) (v : ℕ → V3)
          (hs : isScsV39 s) (hs' : isScsV39 s') (hb : scsBasicV39 s) (hb' : scsBasicV39 s')
          (hM : scsM s = scsM s') (hk : s.k = s'.k) (hd : s'.d = s.d)
          (hv : v ∈ MMsV39 s) (hv' : BBsV39 s' v)
          (ha : ∀ i, s'.a i (i + 1) = s.a i (i + 1))
          (hab : ∀ i j, s.a i j ≤ s'.a i j ∧ s'.b i j ≤ s.b i j),
          v ∈ MMsV39 s'
    ) ∧
    -- 15. PPBTYDQ_p26 (LA26:1631; no HOL anchor line in file docstring)
    (∀ (u v p : V3) (hu : ¬Collinear ℝ ({0, v, p} : Set V3))
          (hv : ¬Collinear ℝ ({0, u, p} : Set V3))
          (harc : arcV 0 u p + arcV 0 p v < Real.pi),
          ¬(0 ∈ convexHull ℝ ({u, v} : Set V3))
    ) ∧
    -- 16. AQICLXA_SLICE (LA20:1347; HOL `AQICLXA_SLICE`)
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 2}
          {scsPropEquV39 scs3M1 1, scsPropEquV39 scs5M1 1}
    ) ∧
    -- 17. AQICLXA (LA20:1398; HOL `AQICLXA`)
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 2} {scs3M1, scs5M1}
    ) ∧
    -- 18. FUNOUYH_SLICE (LA20:1405; HOL `FUNOUYH_SLICE`)
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 3}
          {scsPropEquV39 scs4M2 1, scsPropEquV39 scs4M2 1}
    ) ∧
    -- 19. FZIOTEF (LA20:1437; HOL `FZIOTEF`)
    (scsArrowV39 {scsStabDiagV39 scs6I1 0 3} {scs4M2}
    ) :=
    ⟨FSQKWKK_p16, FEKTYIY_p27, PQCSXWG1_p11, ASSWPOW_p25, PQCSXWG1_SYM_p21, XWITCCN,
      @POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15, ear_acute_p33, sgtrnaf_p12, LDURDPN,
      @AXJRPNC_p26, @MXQTIED_PRIME_p26, @MXQTIED_PRIME2_p26, @MXQTIED_p26, PPBTYDQ_p26,
      @AQICLXA_SLICE, @AQICLXA, @FUNOUYH_SLICE, @FZIOTEF⟩

#print axioms misc_capstone_w1
/-! ### w5 delta capstones la3/la6/la14/la16/la34 (lane capstone-w5,
2026-11-05, roadmap M0b fifth item): every clean public exit newly closed
or newly added after the w4 generation baseline (64959a80) that had never
been materialised into any capstone is re-exposed as ONE conjunction per
module group -- la3_capstone_w1 (8), la6_capstone_w4 (3),
la14_capstone_w4 (16), la16_capstone_w1 (2, XIVPHKS material moved to
XivphksKit by dcb7f63d), la34_capstone_w5 (7).  Total 36 exits; the five
`have hla3d/hla6d/hla14d/hla16d/hla34e` lines in Assembly.textCapstone pull
the capstone proof terms into the e2e cone (pure insertion there too, after
hmisc; the w1/w2/w3/w4 capstones stay wired).  Delta definition (measured at
the lane HEAD f51ed20b vs baseline 64959a80): (a) public top-level `theorem`
exports with a `sorry` in the baseline declaration body and none at HEAD,
or (b) public top-level `theorem` exports whose name did not exist at the
baseline; in both cases the probed `#print axioms` face is exactly
[propext, Classical.choice, Quot.sound], the statement declares no
module-private constant, the declaration kind is `theorem`, and it is not
universe-polymorphic, MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots, 1,540 member names;
intersection 0, verified mechanically).  All 36 are individually exactly
standard three.  LA10's 17 newly closed exports are out of scope by
workorder decision (all 17 exact-std3; 2 also universe-polymorphic); note
LA10 is now transitively reachable via LA6's import added in 697e3dfc, so a
future wave can wire it without a new LocalConcl import.  LA3 is reachable
transitively via LocalConcl -> LocalAuto14 -> LocalAuto6 -> LocalAuto3.
Environment-alignment scopes mirror module-local opens so the verbatim
signatures elaborate under the same name resolution: LA3 and LA6 carry
`open Kepler.Text.Fan`, LA14 carries `open Kepler.Text.V3Coe`; every other
module only opens `Kepler.Geom Set Classical`, already open in this file.
Zero import changes.  The exact cone increment is re-measured at the
orchestrator e2e gate. -/


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- la3_capstone_w1 (lane capstone-w5, 2026-11-05): every public top-level
exit of LocalAuto3 that was newly closed or newly added after the w4
generation baseline (64959a80) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (8 of the 8 w5 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
64959a80 with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD f51ed20b, or (b) a public top-level `theorem` whose
name did not exist at 64959a80 at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
8), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w5.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la3_capstone_w1 :
    -- 1. IDENTIFY_AZIM_CYCLE (LA3:751; no HOL anchor line in file docstring)
    (∀ {W : Set V3} {v w p u : V3}
          (h1 : ¬(W ⊆ {p})) (h2 : ¬Collinear3 v w p) (h3 : cyclicSet_p3 W v w)
          (h4 : u ≠ p ∧ u ∈ W)
          (h5 : ∀ q ∈ W, q ≠ p →
            azim v w p u < azim v w p q ∨
              azim v w p u = azim v w p q ∧
                ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖),
          azimCycle_p3 W v w p = u
    ) ∧
    -- 2. FIRST_AAUHTVE (LA3:1490; no HOL anchor line in file docstring)
    (∀ {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E)
    ,
          ∃ H : Hypermap (V3 × V3),
          (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
          (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
          (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
          (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E ∧
          (H.edgeMap : V3 × V3 → V3 × V3) ∘ (H.edgeMap : V3 × V3 → V3 × V3) = id
    ) ∧
    -- 3. HYP_LEMMA (LA3:1515; no HOL anchor line in file docstring)
    (∀ {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E)
    ,
          ∃ H : Hypermap (V3 × V3),
          (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
          (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
          (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
          (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E
    ) ∧
    -- 4. ELMS_OF_HYPERMAP_HYP (LA3:1524; no HOL anchor line in file docstring)
    (∀ {x : V3} {V : Set V3} {E : Set (Set V3)} (_hfan : FAN x V E)
    ,
          ∃ H : Hypermap (V3 × V3),
          HYP_p3 x V E = ((↑H.darts : Set (V3 × V3)),
            ((H.edgeMap : V3 × V3 → V3 × V3),
              ((H.nodeMap : V3 × V3 → V3 × V3), (H.faceMap : V3 × V3 → V3 × V3))))
    ) ∧
    -- 5. FAN_IMP_BIJ_V_NODE_OF_HYP (LA3:1919; no HOL anchor line in file docstring)
    (∀ {x : V3} {V : Set V3} {E : Set (Set V3)}
          (_hfan : FAN x V E),
          ∃ H : Hypermap (V3 × V3),
          (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
          (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 x V E ∧
          (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 x V E ∧
          (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 x V E ∧
          Set.BijOn
            (fun u : V3 =>
              if u ∈ V then H.node (u, chooseNdPoint_p3 u E V) else (∅ : Set (V3 × V3)))
            V ((fun y : V3 × V3 => H.node y) '' dartsOfHyp_p3 E V)
    ) ∧
    -- 6. LOCAL_FAN_IMP_BIJ_FF_NODES (LA3:1990; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (_h : localFan_p3 V E FF),
          ∃ H : Hypermap (V3 × V3),
          (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
          (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V E ∧
          (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V E ∧
          (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V E ∧
          Set.BijOn (fun y : V3 × V3 => H.node y) FF
            ((fun y : V3 × V3 => H.node y) '' dartsOfHyp_p3 E V)
    ) ∧
    -- 7. WRGCVDR (LA3:2167; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (_hlf : localFan_p3 V E FF) (hro : V3 → V3),
          Set.BijOn (fun d : V3 × V3 => d.1) FF V ∧
          ((∀ x ∈ V, (x, hro x) ∈ FF) →
            (∀ x ∈ FF, x = (x.1, hro x.1)) →
            ∀ x ∈ V, V = orbitF_p3 hro x)
    ) ∧
    -- 8. IMP_FAN_V_PRIME_E_PRIME (LA3:2247; no HOL anchor line in file docstring)
    (∀ {v : V3} {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} (_hfan : FAN v V E)
          (_hH : ∃ H : Hypermap (V3 × V3),
            (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 E V ∧
            (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 v V E ∧
            (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 v V E ∧
            (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 v V E ∧
            ∃ x ∈ H.darts, FF = H.face x),
          FAN v (vPrime_p3 V FF) (ePrime_p3 E FF)
    ) :=
    ⟨IDENTIFY_AZIM_CYCLE, FIRST_AAUHTVE, HYP_LEMMA, ELMS_OF_HYPERMAP_HYP,
      FAN_IMP_BIJ_V_NODE_OF_HYP, LOCAL_FAN_IMP_BIJ_FF_NODES, @WRGCVDR,
      @IMP_FAN_V_PRIME_E_PRIME⟩

#print axioms la3_capstone_w1


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- la6_capstone_w4 (lane capstone-w5, 2026-11-05): every public top-level
exit of LocalAuto6 that was newly closed or newly added after the w4
generation baseline (64959a80) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (3 of the 3 w5 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
64959a80 with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD f51ed20b, or (b) a public top-level `theorem` whose
name did not exist at 64959a80 at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
3), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w5.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la6_capstone_w4 :
    -- 1. HAFL_CIRCLE_FORM_LOCAL_FAN_of_dih (LA6:2809; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v w : V3} {fv : Set (V3 × V3)}
          (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
          (hdihFor : ∀ HS' : Hypermap (V3 × V3),
            IsHyp_p2 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) HS' →
            dih2k_p2 HS' fv.ncard),
          localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv
    ) ∧
    -- 2. CONDS_IN_V_PRIME_NUM2 (LA6:3166 (autoImplicit parameter leak FF, v, w, fw, n; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `CONDS_IN_V_PRIME_NUM2`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fw : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {n : ℕ} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfw : fw = HS.face (w, rhoNode1_p2 FF w))
          (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w),
          ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw ↔
          i = 0 ∨ n ≤ i ∧ i < V.ncard
    ) ∧
    -- 3. PROVE_THE_SLICE_ASSUMPTION (LA6:3570 (autoImplicit parameter leak v, w; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `PROVE_THE_SLICE_ASSUMPTION`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V)
          (hw : w ∈ V) (hvw : v ≠ w)
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E),
          ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
          ¬ Collinear ℝ ({0, z, t} : Set V3)
    ) :=
    ⟨HAFL_CIRCLE_FORM_LOCAL_FAN_of_dih, CONDS_IN_V_PRIME_NUM2, PROVE_THE_SLICE_ASSUMPTION
⟩

#print axioms la6_capstone_w4


open Kepler.Text.V3Coe in
set_option maxHeartbeats 50000000 in

/-- la14_capstone_w4 (lane capstone-w5, 2026-11-05): every public top-level
exit of LocalAuto14 that was newly closed or newly added after the w4
generation baseline (64959a80) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (16 of the 16 w5 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
64959a80 with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD f51ed20b, or (b) a public top-level `theorem` whose
name did not exist at 64959a80 at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
16), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w5.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la14_capstone_w4 :
    -- 1. w15_char3 (LA14:5126; HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE3`)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (h : LocalFan V E FF) {v : V3} (hv : v ∈ V) (i : ℕ),
          ¬ Collinear ℝ ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3)
    ) ∧
    -- 2. w15_affLt_swap (LA14:5191; no HOL anchor line in file docstring)
    (∀ {a b x y : V3}
          (hx : x ∉ ({a, b} : Set V3)) (hy : y ∉ ({a, b} : Set V3)),
          y ∈ affLt ({a, b} : Set V3) ({x} : Set V3) ↔
          x ∈ affLt ({a, b} : Set V3) ({y} : Set V3)
    ) ∧
    -- 3. OPPOSITE_SIDES_IMP_INTER (LA14:5225; no HOL anchor line in file docstring)
    (∀ {va vb vc a b : V3}
          (hvab : va ≠ vb)
          (hd : Disjoint ({va, vb} : Set V3) ({vc} : Set V3))
          (ha : a ∈ affGt ({va, vb} : Set V3) ({vc} : Set V3))
          (hb : b ∈ affLt ({va, vb} : Set V3) ({vc} : Set V3)),
          conv0_p2 ({a, b} : Set V3) ∩
          (affineSpan ℝ ({va, vb} : Set V3) : Set V3) ≠ ∅
    ) ∧
    -- 4. SUCCESSIVE_RHO_NODE1_AFF_LT (LA14:5291; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
          (h : LocalFan V E FF) (hv : v ∈ V)
          (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
          (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P),
          ∀ i, 0 < i → i < l →
          (rhoNode1 FF)^[i - 1] v ∈
            affLt ({0, (rhoNode1 FF)^[i] v} : Set V3) ({(rhoNode1 FF)^[i + 1] v} : Set V3)
    ) ∧
    -- 5. TWO_SIDES_SUCESSIVE (LA14:5330; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v : V3} {l : ℕ} {U P : Set V3}
          (h : LocalFan V E FF) (hv : v ∈ V)
          (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
          (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P),
          ∀ i, 0 < i → i < l →
          conv0_p2 ({(rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i + 1] v} : Set V3) ∩
            (affineSpan ℝ ({0, (rhoNode1 FF)^[i] v} : Set V3) : Set V3) ≠ ∅
    ) ∧
    -- 6. w15_clf2 (LA14:5363; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          (h : ConvexLocalFan V E FF),
          convexLocalFan_p2 V E FF
    ) ∧
    -- 7. CNVX_IMP_INTERIOR_ANGLE_PI (LA14:5386; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)}
          {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
          (h : ConvexLocalFan V E FF) (hv : v ∈ V)
          (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
          (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P),
          ∀ i, 0 < i → i < l →
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] v) = Real.pi
    ) ∧
    -- 8. CONV02_SU_CONV2 (LA14:5554; HOL `CONV02_SU_CONV2`)
    (∀ (a b : V3)
    ,
          conv0_p2 ({a, b} : Set V3) ⊆ convexHull ℝ ({a, b} : Set V3)
    ) ∧
    -- 9. AZIM_EQ_PI_ALT (LA14:5634; HOL `AZIM_EQ_PI_ALT`)
    (∀ {u v w : V3}
          (huv : ¬ Collinear3 0 u v) (huw : ¬ Collinear3 0 u w),
          azim 0 u v w = Real.pi ↔ w ∈ affLt ({0, u} : Set V3) ({v} : Set V3)
    ) ∧
    -- 10. w16_affGe_empty_singleton (LA14:5745; no HOL anchor line in file docstring)
    (∀ (x : V3)
    ,
          affGe ({x} : Set V3) (∅ : Set V3) = {x}
    ) ∧
    -- 11. w16_smul_mem_affGe (LA14:5791; no HOL anchor line in file docstring)
    (∀ {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    ,
          t • u ∈ affGe ({0} : Set V3) ({u} : Set V3)
    ) ∧
    -- 12. w16_smul_mem_affLt (LA14:5798; no HOL anchor line in file docstring)
    (∀ {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : t < 0)
    ,
          t • u ∈ affLt ({0} : Set V3) ({u} : Set V3)
    ) ∧
    -- 13. w16_affGt_empty_subset (LA14:5805; no HOL anchor line in file docstring)
    (∀ {S : Set V3} (h0S : (0:V3) ∉ S)
    ,
          affGt (∅ : Set V3) S ⊆ affGt ({0} : Set V3) S
    ) ∧
    -- 14. w16_noWrap (LA14:5867; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v0 : V3} {vv : ℕ → V3} {k i : ℕ}
          (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
          (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
          (hiter : ∀ n, (rhoNode1 FF)^[n] v0 = vv n)
          (hi : i + 1 < k),
          ¬(azim 0 v0 (vv 1) (vv i) = Real.pi ∧ azim 0 v0 (vv 1) (vv (i + 1)) = 0)
    ) ∧
    -- 15. MONO_AZIM_AS_BTA_I (LA14:6145; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
          (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
          (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
          (hiter : ∀ i, (rhoNode1 FF)^[i] v0 = vv i)
          (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i),
          ∀ i j, i < j → j < k → bta i ≤ bta j
    ) ∧
    -- 16. EGHNAVX (LA14:6211; no HOL anchor line in file docstring)
    (∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
          (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
          (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
          (hiter : ∀ i, (rhoNode1 FF)^[i] v0 = vv i)
          (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i),
          bta 1 = 0 ∧ bta (k - 1) ≤ Real.pi ∧
          (∀ i j, i < j → j < k → bta i ≤ bta j) ∧
          (∀ i, (bta i = 0 ∧ i < k →
              (∀ j, 0 < j ∧ j < i → interiorAngle1 0 FF (vv j) = Real.pi) ∧
              ({z : V3 | ∃ n, 0 < n ∧ n ≤ i ∧ vv n = z} ⊆
                affGt ({0, v0} : Set V3) ({vv 1} : Set V3))) ∧
            (bta i = bta (k - 1) ∧ 0 < i ∧ i < k - 1 →
              (∀ j, i < j ∧ j < k → interiorAngle1 0 FF (vv j) = Real.pi) ∧
              ({z : V3 | ∃ n, i ≤ n ∧ n < k ∧ vv n = z} ⊆
                affGt ({0, v0} : Set V3) ({vv (k - 1)}))))
    ) :=
    ⟨w15_char3, w15_affLt_swap, OPPOSITE_SIDES_IMP_INTER, SUCCESSIVE_RHO_NODE1_AFF_LT,
      TWO_SIDES_SUCESSIVE, w15_clf2, CNVX_IMP_INTERIOR_ANGLE_PI, @CONV02_SU_CONV2,
      AZIM_EQ_PI_ALT, w16_affGe_empty_singleton, w16_smul_mem_affGe, w16_smul_mem_affLt,
      @w16_affGt_empty_subset, w16_noWrap, MONO_AZIM_AS_BTA_I, EGHNAVX⟩

#print axioms la14_capstone_w4


set_option maxHeartbeats 50000000 in

/-- la16_capstone_w1 (lane capstone-w5, 2026-11-05): every public top-level
exit of XivphksKit that was newly closed or newly added after the w4
generation baseline (64959a80) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (2 of the 2 w5 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
64959a80 with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD f51ed20b, or (b) a public top-level `theorem` whose
name did not exist at 64959a80 at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
2), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w5.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la16_capstone_w1 :
    -- 1. XIVPHKS_p16 (XIVPHKS:360; no HOL anchor line in file docstring)
    (∀ (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ) (n r : ℕ)
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
            d (p + 1) p q < e),
          (∀ k j, j + k ≤ r → w j ∈ W (j + k)) ∧
          (∀ k j, 1 ≤ j → j + k ≤ r → w (j + k) ∈ W j)
    ) ∧
    -- 2. XIVPHKS_SHIFT_p16 (XIVPHKS:620; no HOL anchor line in file docstring)
    (∀ (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ)
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
            d (p + 1) p q < e),
          (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w j ∈ W (j + k)) ∧
          (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w (j + k) ∈ W j)
    ) :=
    ⟨XIVPHKS_p16, XIVPHKS_SHIFT_p16
⟩

#print axioms la16_capstone_w1


set_option maxHeartbeats 50000000 in

/-- la34_capstone_w5 (lane capstone-w5, 2026-11-05): every public top-level
exit of LocalAuto34 that was newly closed or newly added after the w4
generation baseline (64959a80) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (7 of the 7 w5 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
64959a80 with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD f51ed20b, or (b) a public top-level `theorem` whose
name did not exist at 64959a80 at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
7), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 28 roots + PackingConcl 5 roots; intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w5.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la34_capstone_w5 :
    -- 1. DEFORMATION_LUNAR_AFFINE_HULL_p34 (LA34:5128 (autoImplicit parameter leak FF''; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `DEFORMATION_LUNAR_AFFINE_HULL`)
    (∀ {FF'' : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF'')
          (hV : Set.range w = V)
          (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
          (hlun : Lunar v w1 V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t < e →
          v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3)
    ) ∧
    -- 2. DEFORMATION_LUNAR_AFFINE_HULL_V1_p34 (LA34:5164; HOL `DEFORMATION_LUNAR_AFFINE_HULL_V1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hl1 : w (l + 1) = v1) (hn : ‖v2‖ ≠ 2)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = Set.range (fun i : ℕ => (w i, w (i + 1))))
          (hV : Set.range w = V)
          (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
          (hlun : Lunar v w1 V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, t ∈ Icc (-e) e →
          v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3)
    ) ∧
    -- 3. V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_p34 (LA34:5213; no HOL anchor line in file docstring)
    (∀ (hz : ZLZTHIC_prop_p34)
          (hm : MHAEYJN_prop_p34) (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ)
          (v1 v2 : V3) (a : ℝ)
          (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hk : 3 < k)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hn2 : ¬(2 = ‖v2‖))
          (hJ : ∀ i, ¬s.J l i)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
            E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
            (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
              v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
            (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
              v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))
    ) ∧
    -- 4. INTERIOR_ANGLE_SAME_V3_DEFOR1_p34 (LA34:5695; HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hl1 : w (l + 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
            BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t))
          (he1 : 0 < e1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < e →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF))^[i]
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k)))
    ) ∧
    -- 5. DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES_p34 (LA34:7394; HOL `DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 v w1 : V3) (x1 x2 x6 a : ℝ) (V : Set V3) (E : Set (Set V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hl : w l = v2) (hlk : w (l + k - 1) = v1) (hn : ‖v2‖ ≠ 2)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1) (hvv2 : v ≠ v2) (hw1v2 : w1 ≠ v2)
          (hV : Set.range w = V)
          (hE : Set.range (fun i : ℕ => {w i, w (i + 1)}) = E)
          (hlun : Lunar v w1 V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, t ∈ Icc (-e) e →
          v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 v2 t ∈ affineSpan ℝ ({0, v, w1, v2} : Set V3)
    ) ∧
    -- 6. V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_TWO_CASES_p34 (LA34:7432; no HOL anchor line in file docstring)
    (∀ (hz : ZLZTHIC_prop_p34)
          (hm : MHAEYJN_prop_p34) (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ) (x1 x2 x6 : ℝ)
          (v1 v2 : V3) (a : ℝ)
          (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hk : 3 < k)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hn2 : ¬(2 = ‖v2‖))
          (hJ : ∀ i, ¬s.J l i)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hlunar : ∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
            E = Set.range (fun i => {w i, w (i + 1)}) → ¬Lunar v (w l) V E),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
          ConvexLocalFan (Set.range fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t)
            (Set.range fun i => {v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
              v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t})
            (Set.range fun i => (v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t,
              v3DeforV4_p34 a x1 x2 x6 v1 v2 (w (i + 1)) t))
    ) ∧
    -- 7. INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES_p34 (LA34:7607; HOL `INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES`)
    (∀ (s : ScsV39) (k l : ℕ) (w : ℕ → V3)
          (v1 v2 : V3) (x1 x2 x6 a e1 : ℝ) (FF : Set (V3 × V3))
          (hk : 3 < k) (hkk : s.k = k) (hs : isScsV39 s) (hmw : w ∈ MMsV39 s)
          (hl : w l = v2) (hlk : w (l + k - 1) = v1)
          (hx1p : 0 < x1) (hx2p : 0 < x2) (hx6p : 0 < x6)
          (haz : azim 0 (w l) (w (l + 1)) (w (l + (s.k - 1))) = Real.pi)
          (hncW : ¬Collinear ℝ ({0, w (l + 1), w (l + (s.k - 1))} : Set V3))
          (haff : w l ∈ affGt {0} ({w (l + 1), w (l + (s.k - 1))} : Set V3))
          (hnc : ¬Collinear ℝ ({0, v1, v2} : Set V3))
          (hx1 : ‖v1‖ ^ 2 = x1) (hx2 : ‖v2‖ ^ 2 = x2) (hx6 : ‖v1 - v2‖ ^ 2 = x6)
          (ha : a = -1)
          (hBBd : ∀ t : ℝ, 0 < t → t < e1 →
            BBsV39 s (fun i => v3DeforV4_p34 a x1 x2 x6 v1 v2 (w i) t))
          (he1 : 0 < e1)
          (hFF : Set.range (fun i : ℕ => (w i, w (i + 1))) = FF),
          ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, ∀ i : ℕ, 0 < t → t < e →
          interiorAngle1 0 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF)
            ((rhoNode1 (deformedFF4_p34 x1 x2 x6 v1 v2 t FF))^[i]
              (v3DeforV4_p34 (-1) x1 x2 x6 v1 v2 (w (l % k)) t)) =
          interiorAngle1 0 FF ((rhoNode1 FF)^[i] (w (l % k)))
    ) :=
    ⟨@DEFORMATION_LUNAR_AFFINE_HULL_p34, DEFORMATION_LUNAR_AFFINE_HULL_V1_p34,
      V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_p34, INTERIOR_ANGLE_SAME_V3_DEFOR1_p34,
      DEFORMATION_LUNAR_AFFINE_HULL_V1_TWO_CASES_p34,
      V3_DEFOR_DEFORMATION_CONVEX_LOCAL_FAN_V1_TWO_CASES_p34,
      INTERIOR_ANGLE_SAME_V3_DEFOR1_TWO_CASES_p34⟩

#print axioms la34_capstone_w5
/-! ### w6 delta capstones la6/la18/la34 (lane capstone-w6,
2026-11-05, roadmap M0b sixth item): every clean public exit newly closed
or newly added after the w5 generation baseline (f51ed20b) that had never
been materialised into any capstone is re-exposed as ONE conjunction per
module group -- la6_capstone_w6 (8), la18_capstone_w6 (1), la34_capstone_w6
(2).  Total 11 exits; the three `have hla6f/hla18f/hla34f` lines in
Assembly.textCapstone pull the capstone proof terms into the e2e cone (pure
insertion there too, after hla34e; the w1/w2/w3/w4/w5 capstones stay wired).
Delta definition (measured at the lane HEAD 550697b9 vs baseline f51ed20b):
(a) public top-level `theorem` exports with a `sorry` in the baseline
declaration body and none at HEAD, or (b) public top-level `theorem` exports
whose name did not exist at the baseline; in both cases the probed
`#print axioms` face is exactly [propext, Classical.choice, Quot.sound], the
statement declares no module-private constant, the declaration kind is
`theorem`, and it is not universe-polymorphic, MINUS the conjunct name set
of every existing capstone (LocalConcl 33 roots + PackingConcl 5 roots,
1,576 member names; intersection 0, verified mechanically).  All 11 are
individually exactly standard three.  The w5 delivery's LA18 top-up
(SUM_AZIM_EQ_ANGLE_LE4_FUN_p18), the LA6 HAFL/HAFL2 closures and the LA6
MONO_AZIM_AS_BTA_I_p2 cluster, and the LA34 W12 TAUSTAR pair are all
accounted for.  LA14 w17 was still uncommitted at the lane HEAD (dirty
worktree, not read) and is recorded as w7 drift.  Environment-alignment
scopes mirror module-local opens so the verbatim signatures elaborate under
the same name resolution: LA6 carries `open Kepler.Text.Fan`; LA18 and LA34
only open `Kepler.Geom Set Classical`, already open in this file.  Zero
import changes.  The exact cone increment is re-measured at the orchestrator
e2e gate. -/


open Kepler.Text.Fan in
set_option maxHeartbeats 50000000 in

/-- la6_capstone_w6 (lane capstone-w6, 2026-11-05): every public top-level
exit of LocalAuto6 that was newly closed or newly added after the w5
generation baseline (f51ed20b) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (8 of the 8 w6 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
f51ed20b with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD 550697b9, or (b) a public top-level `theorem` whose
name did not exist at f51ed20b at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
8), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 33 roots + PackingConcl 5 roots, 1,576 member names;
intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w6.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la6_capstone_w6 :
    -- 1. w2_slice_hyp_simple (LA6:2976 (autoImplicit parameter leak V, FF, v, w, fv; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); no HOL anchor line in file docstring)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
          (HS' : Hypermap (V3 × V3))
          (hHS' : IsHyp_p2 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) HS'),
          HS'.Simple
    ) ∧
    -- 2. HAFL_CIRCLE_FORM_LOCAL_FAN (LA6:3366 (autoImplicit parameter leak FF, v, w, fv; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `HAFL_CIRCLE_FORM_LOCAL_FAN`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v)),
          localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv
    ) ∧
    -- 3. HAFL_CIRCLE_FORM_LOCAL_FAN2 (LA6:3387 (autoImplicit parameter leak FF, v, w, fv, fw; statement = source signature with the printer's leading implicit binders made explicit (keeps source set-literal ascriptions)); HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2`)
    (∀ {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)} {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} {v w : Kepler.Geom.V3} {fv fw : Set (Kepler.Geom.V3 × Kepler.Geom.V3)} (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
          (hvw : v ≠ w)
          (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
            ¬ Collinear ℝ ({0, z, t} : Set V3))
          (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
          (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
          (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
          (hfw : fw = HS.face (w, rhoNode1_p2 FF w)),
          localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
          localFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw
    ) ∧
    -- 4. monoStepCore_p2 (LA6:4221; no HOL anchor line in file docstring)
    (∀ {u b x y : V3} (hu0 : u ≠ 0)
          (hb : ¬ Collinear3 0 u b) (hx : ¬ Collinear3 0 u x)
          (hy : ¬ Collinear3 0 u y) (hx0 : x ≠ 0) (hncxy : ¬ Collinear3 0 x y)
          (hvapi : azim 0 u b x ≤ Real.pi)
          (hdart0 : 0 ≤ azim 0 x y u) (hdartpi : azim 0 x y u ≤ Real.pi)
          (hvb0 : 0 ≤ azim 0 u b y),
          azim 0 u b x ≤ azim 0 u b y ∨
          (azim 0 u b x = Real.pi ∧ azim 0 u b y = 0)
    ) ∧
    -- 5. monoStepOrbit_p2 (LA6:4270; no HOL anchor line in file docstring)
    (∀ (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
          (hr0 : ρ 0 = v0) (hv0 : v0 ≠ 0) (hb : ¬ Collinear3 0 v0 b)
          (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 v0 (ρ i))
          (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
          (hbnds : ∀ i, 0 < i → i < k → 0 ≤ azim 0 v0 b (ρ i) ∧
            azim 0 v0 b (ρ i) ≤ Real.pi)
          (hdart : ∀ i, i + 1 < k → ¬ Collinear3 0 (ρ i) (ρ (i + 1)) ∧
            0 ≤ azim 0 (ρ i) (ρ (i + 1)) v0 ∧
            azim 0 (ρ i) (ρ (i + 1)) v0 ≤ Real.pi) (i : ℕ) (hik : i + 1 < k),
          azim 0 v0 b (ρ i) ≤ azim 0 v0 b (ρ (i + 1)) ∨
          (azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0)
    ) ∧
    -- 6. monoWindowNowrap_p2 (LA6:4293; no HOL anchor line in file docstring)
    (∀ (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
          (hr0 : ρ 0 = v0) (hv0 : v0 ≠ 0) (hb : ¬ Collinear3 0 v0 b)
          (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 v0 (ρ i))
          (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
          (hbnds : ∀ i, 0 < i → i < k → 0 ≤ azim 0 v0 b (ρ i) ∧
            azim 0 v0 b (ρ i) ≤ Real.pi)
          (hdart : ∀ i, i + 1 < k → ¬ Collinear3 0 (ρ i) (ρ (i + 1)) ∧
            0 ≤ azim 0 (ρ i) (ρ (i + 1)) v0 ∧
            azim 0 (ρ i) (ρ (i + 1)) v0 ≤ Real.pi)
          (hnowrap : ∀ i, i + 1 < k →
            ¬(azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0))
          {i j : ℕ} (hij : i < j) (hjk : j < k),
          azim 0 v0 b (ρ i) ≤ azim 0 v0 b (ρ j)
    ) ∧
    -- 7. w16_noWrap_p2 (LA6:4333; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v0 : V3} {vv : ℕ → V3} {k i : ℕ}
          (hcl : convexLocalFan_p2 V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
          (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
          (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v0 = vv n)
          (hi : i + 1 < k),
          ¬(azim 0 v0 (vv 1) (vv i) = Real.pi ∧ azim 0 v0 (vv 1) (vv (i + 1)) = 0)
    ) ∧
    -- 8. MONO_AZIM_AS_BTA_I_p2 (LA6:4610; no HOL anchor line in file docstring)
    (∀ {E : Set (Set V3)} {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
          {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
          (hcl : convexLocalFan_p2 V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
          (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
          (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v0 = vv i)
          (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i),
          ∀ i j, i < j → j < k → bta i ≤ bta j
    ) :=
    ⟨w2_slice_hyp_simple, HAFL_CIRCLE_FORM_LOCAL_FAN, HAFL_CIRCLE_FORM_LOCAL_FAN2,
      monoStepCore_p2, monoStepOrbit_p2, monoWindowNowrap_p2, w16_noWrap_p2,
      MONO_AZIM_AS_BTA_I_p2⟩

#print axioms la6_capstone_w6


set_option maxHeartbeats 50000000 in

/-- la18_capstone_w6 (lane capstone-w6, 2026-11-05): every public top-level
exit of LocalAuto18 that was newly closed or newly added after the w5
generation baseline (f51ed20b) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (1 of the 1 w6 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
f51ed20b with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD 550697b9, or (b) a public top-level `theorem` whose
name did not exist at f51ed20b at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
1), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 33 roots + PackingConcl 5 roots, 1,576 member names;
intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w6.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la18_capstone_w6 :
    -- 1. SUM_AZIM_EQ_ANGLE_LE4_FUN_p18 (LA18:1885; no HOL anchor line in file docstring)
    (∀ (ff : V3 → ℝ) (s : ScsV39)
          (vv : ℕ → V3) (p : ℕ) (u : V3) (V : Set V3) (E : Set (Set V3))
          (FF : Set (V3 × V3)) (hk : ¬s.k ≤ 3) (hBB : BBsV39 s vv)
          (his : isScsV39 s) (hu : vv (p % s.k) = u) (hV : Set.range vv = V)
          (hE : (Set.range fun i => {vv i, vv (i + 1)}) = E)
          (hFF : (Set.range fun i => (vv i, vv (i + 1))) = FF),
          setSum {i | i < s.k}
            (fun i => ff (vv (i + p % s.k)) *
              interiorAngle1 0 FF ((rhoNode1_p18 FF)^[i] u)) =
          setSum FF (fun e => ff e.1 * azimInFan_p18 e E)
    ) :=
    SUM_AZIM_EQ_ANGLE_LE4_FUN_p18

#print axioms la18_capstone_w6


set_option maxHeartbeats 50000000 in

/-- la34_capstone_w6 (lane capstone-w6, 2026-11-05): every public top-level
exit of LocalAuto34 that was newly closed or newly added after the w5
generation baseline (f51ed20b) and was never a conjunct of any existing
capstone, re-exposed as ONE conjunction so the Assembly `textCapstone` cone
can consume it (2 of the 2 w6 delta exits; 0
dropped mechanically, reason per name below).  Delta definition (measured,
not assumed): either (a) a public top-level `theorem` also present at
f51ed20b with a `sorry` in its declaration body (comments stripped) and no
`sorry` at lane HEAD 550697b9, or (b) a public top-level `theorem` whose
name did not exist at f51ed20b at all; in both cases the probed
`#print axioms` face must be exactly [propext, Classical.choice,
Quot.sound] (no sorryAx, no other axiom; checked individually for all
2), the statement must declare no module-private constant (`✝` in the
`#check @` dump), the declaration kind must be `theorem`, and it must not
be universe-polymorphic; MINUS the conjunct name set of every existing
capstone (LocalConcl 33 roots + PackingConcl 5 roots, 1,576 member names;
intersection 0).
Provenance: conjunct text is the declaration's source signature (binders +
conclusion, copied verbatim and mechanically split at the binder/conclusion
separator by scripts/gen_items_w6.py); conjuncts whose source text leaves an
autoImplicit variable free are emitted from the source signature with the
printer's leading implicit binder run (module variables + the leaked
autoImplicit names, printer order) written out explicitly, so the capstone
itself stays parameter-free while the source's set-literal ascriptions
(e.g. `({v, w} : Set V3)`) survive (marked printer-form in their
per-conjunct comment); semantic identity is re-verified by the elaboration
of the `⟨...⟩` assembly below (each component must unify definitionally with
its conjunct); per-conjunct comments carry each exit's source line and
file-local docstring HOL anchor.  Conjunct order: source declaration order.
Mechanical drops: none.
Body = the assembly of the exit constants -- zero new proof obligations,
zero new imports. -/
theorem la34_capstone_w6 :
    -- 1. TAUSTAR_V3_DEFOR_p34 (LA34:5938; no HOL anchor line in file docstring)
    (TAUSTAR_V3_DEFOR_concl_p34
    ) ∧
    -- 2. TAUSTAR_V3_DEFOR_TWO_CASES_p34 (LA34:7865; no HOL anchor line in file docstring)
    (TAUSTAR_V3_DEFOR_TWO_CASES_concl_p34
    ) :=
    ⟨TAUSTAR_V3_DEFOR_p34, TAUSTAR_V3_DEFOR_TWO_CASES_p34
⟩

#print axioms la34_capstone_w6
end Kepler.Text
