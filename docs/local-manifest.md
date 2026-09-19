# Local Chapter Port Manifest — Flyspeck `local/` → Lean `LocalAuto1..N`

Source: `lean/scripts/local/*.hl` (68 files, 174,695 lines, chapter "Local Fan").
Target: `lean/Kepler/Text/LocalAuto*.lean`, conventions: `V3 = ℝ³`, faithful statements,
DISCHARGES-docstrings, skeleton-first (statement + `sorry`, proofs discharged later).

## Totals
68 files (1 scratch, skip) · **2843** `let=prove` theorems · **243** `new_definition`s
(largest: appendix 89 incl. concl-registry lets, localization 40, WRGCVDR 23) ·
2513 distinct ALL-CAPS `let` names incl. tactic-helper lemmas (XWITCCN 105, IMJXPHR 113).

## Capstone & downstream contract
- Local chapter's culminating artifact: the **main-estimate terminal case bank** in `terminal.hl`
  (`main_nonlinear_terminal_v11 ==> <y1..y6 box constraints>`, 115 proves; hash-gadget
  `get_main_nonlinear`) + statement registry `appendix.hl` (`MHAEYJN_concl`, `ZLZTHIC_concl`,
  `VPWSHTO_concl`, `YRTAFYH_concl`, `BKOSSGE_concl`; shared constants `cstab`, `rho_fun`,
  `tau_fun`, `arc1553_v39`, `BBs_v39`, `MMs_v39`).
- The inequality consumed by counting_spheres/assembly is **`local_annulus_inequality`** — a
  *definition* at `packing/pack_defs.hl:202` (NOT in local/), already stubbed Lean-side as
  `localAnnulusInequalityP22` at `PackingAuto22.lean:226` ("NEEDS pack1.hl"). TVERBERG /
  LEO / WEDGEBELL are **absent from this snapshot** (upstream tame/ineq chapters not present);
  declare their anchors in a shared bridge module.

## External (non-local) anchors — declare once, import everywhere
| anchor | origin | used by |
|---|---|---|
| `main_nonlinear_terminal_v11` | Nonlinear chapter (not in snapshot) | 20 local files (terminal, pent_hex, hexagons, MIQMCSN, …) |
| `scs_basic_v39`/`scs_*_v39` family | tame/scs defs (BBs/MMs local copies live in appendix.hl) | 15+ files |
| `local_annulus_inequality`, `pack_ineq_def_a` | packing/pack_defs.hl:202 | PackingAuto22 consumer |
| `PACKING`, `VOLP`, `BUMP`, `mcell`, `beta_bump`, `dihX`, `sol`, `rhazim`, `delta_x` | fan/graphs/packing/Mathlib kits (Lean: PackingAuto1–25, Geom/Azim·SolidAngle·WedgeVolume) | scattered |
| HOL core (`SUC`, `IMAGE`, `SUBSET`, `MOD`, `ITER`, …) | Mathlib | everywhere (ignore) |

## Scratch / duplicates
| file | verdict |
|---|---|
| `RNSYJXM-compiled.hl` | SKIP — 0 defs/0 proves, `needs tame/ssreflect/tame_lemmas-compiled.hl` (absent). Compiled artifact. |
| `YXIONXL.hl` vs `YXIONXL2.hl` | NOT duplicates: same header but **zero** name overlap (40 vs 105). v1 = BB-transfer lemmas; v2 = continuation. Port both. |
| `terminal.hl` | keep; carries "temporary: merge with main_nonlinear_terminal_v11" note — external anchor, don't merge. |
| `appendix.hl` | def/concl registry, not leftover — foundation (port first). |

## Dependency shape
`flyspeck_needs` DAG is flat (only `terminal→appendix`); real coupling is `open Module` +
identifier refs: **47/68 files sit in one mutual-open SCC** → no strict topological order;
skeleton-first with `sorry` is mandatory. `in` column = refs-in (gravity): WRGCVDR/appendix/
terminal 67, pent_hex 66, local_lemmas 64, NKEZBFC/OCBICBY 62, lp_details 60, polar_fan 57.

## Per-file inventory (defs = `new_definition`, thm = `let=prove`, caps = ALL-CAPS lets, in = refs-in)
| file | lines | defs | thm | caps | in | wave |
|---|---|---|---|---|---|---|
| IMJXPHR | 11028 | 1 | 117 | 113 | 5 | W6 |
| QKNVMLB | 10699 | 0 | 53 | 49 | 6 | W6 |
| XWITCCN | 8020 | 2 | 77 | 105 | 7 | W6 |
| NUXCOEA | 7741 | 1 | 101 | 98 | 10 | W5 |
| local_lemmas | 7463 | 3 | 194 | 211 | 18 | W2 |
| local_lemmas1 | 6531 | 4 | 109 | 116 | 12 | W2 |
| lunar_deform | 5039 | 0 | 42 | 53 | 13 | W7 |
| OCBICBY | 4788 | 0 | 150 | 33 | 17 | W4 |
| MTUWLUN | 4562 | 14 | 24 | 38 | 15 | W2 |
| CUXVZOZ | 4348 | 0 | 62 | 12 | 18 | W4 |
| HIJQAHA | 4145 | 4 | 112 | 71 | 11 | W5 |
| terminal | 4133 | 1 | 115 | 31 | 20 | W7 |
| UAGHHBM | 4106 | 0 | 47 | 44 | 9 | W5 |
| JOTSWIX | 3922 | 0 | 20 | 15 | 13 | W4 |
| ZLZTHIC | 3781 | 0 | 54 | 23 | 14 | W3 |
| ODXLSTC | 3689 | 1 | 55 | 52 | 9 | W5 |
| YXIONXL2 | 3528 | 0 | 105 | 103 | 9 | W3 |
| MIQMCSN | 3469 | 3 | 114 | 86 | 10 | W5 |
| polar_fan | 3362 | 2 | 52 | 47 | 15 | W2 |
| WRGCVDR | 3331 | 23 | 97 | 101 | 20 | W1 |
| dih2k | 3320 | 15 | 95 | 100 | 16 | W1 |
| JKQEWGV | 3307 | 0 | 26 | 36 | 12 | W4 |
| WJSCPRO | 3216 | 0 | 4 | 4 | 13 | W3 |
| ZITHLQN | 3202 | 0 | 26 | 16 | 13 | W4 |
| pent_hex | 3187 | 0 | 81 | 7 | 17 | W4 |
| AUEAHEH | 2960 | 0 | 101 | 101 | 8 | W5 |
| VPWSHTO | 2925 | 0 | 28 | 28 | 11 | W3 |
| ARDBZYE | 2907 | 0 | 81 | 77 | 9 | W5 |
| VASYYAU | 2861 | 0 | 35 | 27 | 9 | W4 |
| UXCKFPE | 2648 | 2 | 20 | 57 | 8 | W4 |
| NKEZBFC | 2618 | 8 | 29 | 24 | 15 | W2 |
| YXIONXL | 2610 | 0 | 39 | 38 | 9 | W3 |
| LVDUCXU | 2311 | 0 | 50 | 55 | 15 | W2 |
| hexagons | 2171 | 1 | 106 | 93 | 9 | W4 |
| IUNBUIG | 1888 | 0 | 22 | 7 | 11 | W3 |
| AURSIPD | 1850 | 0 | 4 | 4 | 8 | W3 |
| HDPLYGY | 1844 | 14 | 26 | 27 | 14 | W2 |
| lp_details | 1768 | 1 | 40 | 7 | 15 | W2 |
| TECOXBM | 1742 | 0 | 8 | 8 | 13 | W2 |
| localization | 1595 | 40 | 43 | 28 | 14 | W1 |
| appendix | 1571 | 89 | 21 | 0 | 20 | W1 |
| OTMTOTJ | 1542 | 0 | 47 | 49 | 9 | W4 |
| AXJRPNC | 1058 | 0 | 9 | 5 | 8 | W4 |
| deformation | 1040 | 1 | 16 | 13 | 11 | W3 |
| CNICGSF | 908 | 0 | 15 | 16 | 8 | W3 |
| RRCWNSJ | 878 | 0 | 8 | 7 | 8 | W4 |
| WKEIDFT | 834 | 0 | 19 | 17 | 9 | W4 |
| JLXFDMJ | 825 | 0 | 6 | 6 | 8 | W4 |
| GBYCPXS | 690 | 0 | 12 | 12 | 11 | W4 |
| TFITSKC | 673 | 0 | 5 | 4 | 8 | W4 |
| JCYFMRP | 625 | 0 | 5 | 5 | 8 | W4 |
| PPBTYDQ | 614 | 0 | 15 | 15 | 8 | W4 |
| YRTAFYH | 520 | 0 | 14 | 12 | 9 | W3 |
| EYYPQDW | 517 | 2 | 19 | 18 | 9 | W3 |
| XIVPHKS | 487 | 0 | 3 | 3 | 11 | W3 |
| RNSYJXM-compiled | 397 | 0 | 0 | 1 | 4 | SKIP |
| BKOSSGE | 396 | 0 | 12 | 3 | 10 | W3 |
| PCRTTID | 367 | 9 | 6 | 7 | 12 | W2 |
| CQAOQLR | 335 | 0 | 11 | 11 | 8 | W3 |
| PQCSXWG | 320 | 1 | 14 | 14 | 12 | W2 |
| LKGRQUI | 269 | 0 | 2 | 2 | 8 | W4 |
| JEJTVGB | 253 | 1 | 5 | 2 | 7 | W3 |
| AYQJTMD | 237 | 0 | 5 | 4 | 9 | W4 |
| FEKTYIY | 212 | 0 | 1 | 1 | 8 | W4 |
| SGTRNAF | 191 | 0 | 2 | 2 | 8 | W4 |
| HXHYTIJ | 131 | 0 | 1 | 1 | 8 | W4 |
| LDURDPN | 126 | 0 | 5 | 5 | 8 | W1 |
| LFJCIXP | 64 | 0 | 1 | 1 | 7 | W1 |

## Port plan — waves (independent files parallel within a wave), 45 modules
| wave | modules | files | focus |
|---|---|---|---|
| W1 | LocalAuto1–4 | localization+LDURDPN+LFJCIXP; WRGCVDR; appendix; dih2k | local_fan/cyclic_on/azim_in_fan/wedge kit; concl registry + BBs/MMs + cstab/rho/tau; ball_annulus+dih2k defs |
| W2 | LocalAuto5–12 | local_lemmas; local_lemmas1; polar_fan; MTUWLUN; HDPLYGY; NKEZBFC; PCRTTID; LVDUCXU; lp_details; PQCSXWG; TECOXBM | lemma banks, scs coordinate/stability defs (11 files → pair to 9 modules) |
| W3 | LocalAuto13–24 | YXIONXL, YXIONXL2, ZLZTHIC, VPWSHTO, JEJTVGB, XIVPHKS, BKOSSGE, EYYPQDW, deformation, WJSCPRO, IUNBUIG, CQAOQLR, YRTAFYH, CNICGSF, AURSIPD | scs transfer/BB-bridge machinery, small files batched |
| W4 | LocalAuto25–36 | pent_hex, hexagons, CUXVZOZ, OCBICBY, JOTSWIX, JKQEWGV, WKEIDFT, OTMTOTJ, UXCKFPE, VASYYAU, ZITHLQN, RRCWNSJ, GBYCPXS, PPBTYDQ, AXJRPNC, TFITSKC, JCYFMRP, JLXFDMJ, SGTRNAF, HXHYTIJ, AYQJTMD, FEKTYIY, LKGRQUI | terminal-case splitters (main_nonlinear_terminal_v11 consumers); micro-files merged into shared modules |
| W5 | LocalAuto37–41 | NUXCOEA, MIQMCSN, AUEAHEH, ARDBZYE, HIJQAHA, ODXLSTC, UAGHHBM | big lemma banks incl. BBs/MMs annulus analysis |
| W6 | LocalAuto42–44 | IMJXPHR, QKNVMLB, XWITCCN | giants: deformation/azim continuity (IMJXPHR), ear/diagonal combinatorics (QKNVMLB), inequality_A_B case machine (XWITCCN) |
| W7 | LocalAuto45 | lunar_deform + terminal | capstone: MHAEYJN deformation lemmas + main-estimate terminal case bank; ends in bridge def matching `localAnnulusInequalityP22` |

## Lean-side kits needed per wave
| wave | kits |
|---|---|
| W1 | `Fan.lean`, `Hypermap.lean`, `Geom/Azim+SolidAngle+WedgeVolume`; new: scs_v39 record (BBs/MMs) |
| W2 | W1 + `Geom/Volume`, `VectorAngleLemmas`, `TopologyFan`; `PackingAuto` mcell/voronoi names as anchors |
| W3 | W2 + `Planarity*` (dart/hypermap traversal), `PackingAuto` rogers/marchal statement anchors |
| W4 | W2 + LP-style arithmetic bank (delta_x/delta_y, REAL_LINEAR-style); `PolyAuto` polyhedron lemmas |
| W5 | `PackingAuto1–25` anchors (mcell, beta_bump, dihX, sol), `Geom/LuneVolume` |
| W6 | full PackingAuto kit + `Polytope.lean` (convex local fan ↔ polyhedron) |
| W7 | everything above; emit statements matching `PackingAuto22.localAnnulusInequalityP22` contract |

## Top risks
1. **IMJXPHR** (11k lines, 117 thm): deformation/azim continuity — measure-theory-flavored, worst proof surface.
2. **XWITCCN** (8k): `INEQUALITY_A_B_TAC_*` tactic family — tactic helpers became ALL-CAPS theorems; needs faithful tactic-replay redesign.
3. **terminal** + `main_nonlinear_terminal_v11` anchor: hash-keyed `get_main_nonlinear` gadget + 20-file external anchor from an absent chapter — must be re-declared in W1 bridge module.

## Surprises
- TVERBERG/LEO/WEDGEBELL are **not** in this snapshot (upstream tame/ineq missing); the real capstone def `local_annulus_inequality` lives in packing/pack_defs.hl:202 and is already stubbed Lean-side (PackingAuto22.lean:226).
- Dep graph is one giant 47-file SCC — batches are pragmatic, not topological; `sorry`-first is unavoidable.
- appendix.hl's 89 "defs" are mostly statement-registry lets (`*_concl`) — a ready-made skeleton source.
- YXIONXL/YXIONXL2 share header/prefix but zero content overlap.

## Fill ledger — 2026-09-18 proof-fill pass (worker: LocalAuto30/31)

| module | sorry before | filled | sorry after | notes |
|---|---|---|---|---|
| LocalAuto30.lean (UAGHHBM) | 7 | 6 | 1 | All six `c = am` Section G lemmas proved in-file: HOL `IMP_SUC_MOD_EQ` cell-cancellation reduced to `psort_suc_edge_p30`/`psort_suc_ne_p30` (+ `suc_mod_ne_p30`) — a psort-match with a successor cell forces the cyclic-edge condition, where `hedge` fires against `ham`; off the edge no cell is matched, so the BBindex sets agree pointwise. Remaining: `UAGHHBM_p30` (needs `isScsV39` of each restriction — the ~1600-line HOL `RESA_TAC` fork bash; not present in any importable lane). |
| LocalAuto31.lean (ODXLSTC) | 24 | 6 | 18 | Filled: 4× `DEFORMATION_DIST_LE_BLL_EDGE{,2}{,_LE3}` via shared `distEdge_p31` (annulus norms + `2 ≤ scs_a` at cyclic edges ⇒ positive `(w l - w i)·w l`, in-file `CLOSER_POINTS_LEMMA_p31` shim ⇒ strict `b`-window); `CARD_V_EQ_SCS_K1_p31` via in-file `VV_INJ_p31` shim + periodicity (the HOL route's `V_E_FF_IS_SCS_CASES_*_p23` are themselves `sorry` stubs — not usable); `DSV_WW_DEFOR_EQ_p31` (empty J-row + J-symmetry ⇒ J-darts avoid `l`, `VV_INJ_p31` + `setSum_congr_p31`). Remaining 18 all share two root blockers, cited in their NEEDS notes: (a) `LocalFan` is the registry stub `fun _ _ _ => True` (LocalAuto1.lean:138) — every local-fan-conditioned lemma is information-theoretically unprovable from its hypotheses; the HOL kit exists only against the different predicate `localFan_p2` (LocalAuto5), and `JKQEWGV2` exists only as `sorry` stubs (LocalAuto1/LocalAuto23); (b) `AZIM_SPECIAL_SCALE`/`AZIM_SCALE_ALL` unported (gap documented in PlanarityAuto8; Kepler.Geom.Azim has no scale lemma). |

Shims added (documented in-file): LocalAuto31 `SUC_MOD_NOT_EQ_p31`, `VV_INJ_p31`
(same proofs as LocalAuto35 `SUC_MOD_NOT_EQ_p35`/`VV_INJ_p35`, re-derived because
importing LocalAuto35 would drag the `Polytope`→Planarity chain and the `atn2`
PackingAuto18/20 clash into this branch), `CLOSER_POINTS_LEMMA_p31`,
`setSum_congr_p31`, private `distEdge_p31`. LocalAuto30: `suc_mod_ne_p30`,
`psort_suc_edge_p30`, `psort_suc_ne_p30`. No new imports; no statements changed;
both modules compile 0 errors (38-way lane preserved).
## Fill ledger — 2026-09-19 proof-fill pass (worker: LocalAuto29/31)

| module | sorry before | filled | sorry after | notes |
|---|---|---|---|---|
| LocalAuto29.lean (HIJQAHA) | 47 | 19 | 28 | Filled: all 16 `SCS_*_IS_SCS` giants — `SCS_5T1_IS_SCS_p29` by direct invocation of LocalAuto22's **proved** `is_scs_adj_p22` csAdj machine (the LA22 twin `is_scs_5T1_p22` is that invocation with only its trivial `h5 : 3 < 5 → 2 ≤ 2*h0 ∧ 2 = 2` side condition left `sorry`; LA22 reaches this file transitively via LocalAuto20, no import added); the other 15 funlist-table systems (5M3, 3T1, 3T4, 3T6', 3T1', 3T4', 4M3', 4M4', 4M5', 4M6', 4M7, 4M8 and the 4M6/4M7/4M8 primes) via a factored in-file skeleton `isScs_mkFunlist_p29` (the proved LocalAuto20 `SCS_5M2_IS_SCS` 21-conjunct boilerplate) + `funlist3/4_symm_p29` + `interval_cases` residue sweeps — the LA22 `is_scs_*_p22` twins of these targets are all still `sorry`, so nothing else was importable; and the 3 `STAB_5I1/5I2/5M3_SCS_p29` diag-stab verifications by the proved LocalAuto20 `STAB_6I1_SCS` method at `k = 5` (`diag_not_edge_psort_p20` keeps the `cstab` override off edge pairs; `csAdj_adj_p22`/`periodic2_cs_adj_p22`/`csAdj_swap_p22`; funlist twin via `stab5M3_edge_p29`, card set `{0}` as in `SCS_5M2_IS_SCS`). Remaining 28 NEEDS re-verified live: `XWNHLMD_MM_p26` still `sorry` (LocalAuto26:688) blocks all `MM_*_IMP_MM_STAB_*`/`MM_*_IMP_MM_*`; `scsArrowV39` = isScs(S2) ∧ (MMs(S1)=∅ ∨ ∃S2 MMs≠∅) so the `SCS_*_ARROW_MM_*`/`SET_EQ_DIAG_STAB_5M3_*` arrows additionally need the target `IS_SCS` twins and MMs-nonemptiness; slices blocked by `LKGRQUI_concl`/`YXIONXL3_concl` (LocalAuto1 pending) and `FZIOTEF` (LocalAuto20 `sorry`); `JCYFMRP_p27` still `sorry`; no proved `xrr ≤ 15.53` envelope; `main_nonlinear_terminal_v11` consumers unproven. |
| LocalAuto31.lean (ODXLSTC) | 18 | 1 | 17 | Filled: `CARD_FF_EQ_WW_DEFORMATION_p31` — shim replacing the HOL `LOFA_IMP_CARD_FF_V_EQ` local-fan route (unavailable: `LocalFan` stub): both dart ranges counted to `k` by the in-file `dartRange_ncard_p31` core (`Finset.range k` image + injOn, same counting as `CARD_V_EQ_SCS_K1_p31`); original family residue-injective by `VV_INJ_p31` (`congrArg Prod.fst`), deformed family by dart-by-dart residue case analysis — a deformed head/tail equals the shrink `(1-t)•w l` only at residue `l % k`, and the two head/tail equations force `a = b` unless `k ∤ 1, 2` (excluded by `3 < k`; `hsucc_eq`/`hsucc_ne`/`htwo_ne` residue kit). Remaining 17 root blockers re-verified live: `LocalFan` still the stub `True` (LocalAuto1:138), `AZIM_SPECIAL_SCALE`/`AZIM_SCALE_ALL` still unported (PlanarityAuto8 gap note unchanged), `JKQEWGV2` still `sorry` (LocalAuto1/23). |

Shims added (documented in-file): LocalAuto29 private `isScs_mkFunlist_p29`,
`funlist_symm_p29`, `funlist3_symm_p29`, `funlist4_symm_p29`, `stab5M3_edge_p29`
(no new imports — LocalAuto22's kit reaches this file transitively through
LocalAuto20). LocalAuto31 private `dartRange_ncard_p31`. No statements changed;
both modules compile 0 errors; the 21-conjunct `isScsV39`/`STAB_*_SCS`
verifications are honest direct proofs, not axiom shortcuts.



## Fill ledger — 2026-09-19 proof-fill pass (worker: LocalAuto13/17/26)

| module | sorry before | filled | sorry after | notes |
|---|---|---|---|---|
| LocalAuto13.lean (YXIONXL2) | 47 | 4 | 43 | Filled: `EE_SYM_0_p13` (elementwise: negation transports two-point sets via new private `image_neg_pair_p13`, so `{-a, w} ∈ E'` ↔ `{a, -w} ∈ E`), `SUM_PAIR_SYM_0_p13` (the neg-pair map is an involution `m∘m = id`, so finiteness transports through `image m (image m s) = s` and `Finset.sum_image` reindexes the finite branch; both sides `0` in the infinite branch), `COLLINEAR_SYM_0_p13` + `COLLINEAR_POINT_SYM_0_p13` (`collinear_iff_of_mem` at the negated anchor / at `0` with `w1 = -(-w1)`). Remaining 43 NEEDS re-verified live: the 4 `AFF_{GE,LT}_{COMMUTATIVE,VEC0}_SYM_0` family is mechanical (weight transport under negation) but left for the next batch; `POINT_IN_AFF_LT_SYM_0_p13` is UNPROVABLE AS STATED — counterexample `w2 = 0`, `v1 ≠ 0`: `Affsign` forces `f w2 < 0` with `w2` also in the base `{0, v1}`, and `∑ f = 1` + zero target vector are then incompatible; the HOL source (src:1324) presumably assumes `w2 ≠ 0` — left `sorry` with an in-file note (statements untouched); `AZIM_*SYM` quintet needs a negation-equivariance kit over `azim_frame_spec` (none upstream: AzimLemmas has no NEG lemmas); the 28 scs/hypermap giants still blocked (scs record lane + hypermap-of-HYP foundation parallel-in-flight). |
| LocalAuto17.lean (EYYPQDW/YRTAFYH/deformation) | 11 | 3 | 8 | Filled: `EYYPQDW_NORMV3_p17` + `EYYPQDW_NORM_V3_V1_p17` — the Cayley identities reduce to the orthogonal split `normsq_add_orth_p17` (norm_add_sq_real + `dot_cross3_v1_X_p17`), the cross-term norm `‖cross3 v1 (cross3 v1 v2)‖² = x1 * upsX x1 x2 x6 / 4` (new private `normsq_double_cross_p17`, via Mathlib `cross_dot_cross` twice — the same route as the file's own `upsX_pos_of_noncollinear_p17`), and the sign scalar squaring to `upsX x1 x3 x5 / (upsX x1 x2 x6 * x1²)` (`SGIN_POW_EQ_p17` + `Real.sq_sqrt`); and `EYYPQDW_p17` (the master): both Cayley norms applied at the translated pair `(v1-v0, v2-v0)` via `MK_PLANAR_REP_p17`, coplanarity because Lagrange makes the double-cross a `u1,u2`-combination inside `vectorSpan {v0,v1,v2}`, and the `t > 0` witness `(√ …)⁻¹` off `cross3_X_smul_p17` — DISCHARGES LocalAuto1.EYYPQDW_concl. Remaining 8 re-verified live: `YRTAFYH_p17` (20-conjunct scs re-verification), `SEPARATE_CLOSED_CONES_p17`/`lemma_2_p17`/`GMLWKPK{,_ALT,_SIMPLE}_p17`/`FAN7_SMALL_DEFORMATION_p17`/`XRECQNS_p17` — no proved twins upstream (LA28 fill-kit says the IMJXPHR parents were still sorried there; deformation chain roots in `SEPARATE_CLOSED_CONES`, unproven anywhere). |
| LocalAuto26.lean (RRCWNSJ/AXJRPNC/PPBTYDQ/GBYCPXS) | 14 | 3 | 11 | Filled: `arclength222h0_p26` + `arclength_2h0_cstab_p26` — numeric `atn2` first-branch breakdowns (the `ATN_UPS_X_BREAKDOWN1` role): `h0 = 1.26`/`cstab = 3.01` make `|c²−a²−b²| < sqrt (upsX 4 4 c²)` true on the `atn2` first branch, the `2h0` arc's arctangent negative, and `1.0601/√62.876 < 1.6496/√61.279` (squared: 111.1 < 171.1... cert in-file) folds the sum below `pi` via `arctan_lt_arctan_iff`; and `BB_VV_FUN_EQ_p26` — forward = the `W_IN_BB_FUN_EQ` quasi-injectivity mirrored from the LocalAuto28 fill (16th `isScsV39` conjunct + `BBsV39` bounds collapsing `dist = 0`), backward = `periodic_mod_eq_p23` mod-folding. Remaining 11 re-verified live: `BB_RHO_NODE_IVS_p26` blocked by `VV_SUC_EQ_RHO_NODE_PRIME` (still `sorry` in LA35), `RRCWNSJ_p26`/`AXJRPNC_p26` blocked by `JKQEWGV2`/lunar machinery, `MXQTIED_PRIME_p26`/`MXQTIED_PRIME2_p26`/`MXQTIED_p26` blocked by `BB_simplify`/`MXQTIED_INDEX` (the `s.a ≤ s'.a`/`s'.b ≤ s.b` bound transport is not def-level), `PPBTYDQ_p26`/`XWNHLMD_MM_p26` blocked by convex-hull-arcV/`MMS_NONEMPTY` kits, `TAU_FUN_LE_p26`/`CIRCULAR_SOL_EQ_2PI_p26` blocked by `LOFA_DETERMINE_AZIM_IN_FA`/`CONVEX_LOFA_IMP_INANGLE_EQ_AZIM` (LA9 `sorry`), `NOT_CIRCULAR_SY_p26` inner `sorry` = the `convexLocalFan_p4 → ConvexLocalFan` hypermap bridge (LA4 `hyp_p4`-based vs LA1 `LocalFan` — needs the hypermap coincidence kit). |

Shims added (documented in-file): LocalAuto17 private `normsq_smul_p17`,
`normsq_add_orth_p17`, `normsq_double_cross_p17`. LocalAuto13 private
`image_neg_pair_p13`. No new imports (LA17's fills run on the in-file
cross3/dot fill-kit + Mathlib `cross_dot_cross`/`dotProduct_sub`; LA26's
`BB_VV_FUN_EQ_p26` reuses the importable LocalAuto23 `periodic_mod_eq_p23`
and mirrors LA28's `W_IN_BB_FUN_EQ` proof in-file since LocalAuto28 has no
olean on this branch). No statements changed; all three modules compile
0 errors (`lake env lean`, traces removed first).
