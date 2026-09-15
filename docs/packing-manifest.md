# Packing Chapter Port Manifest (Flyspeck HL → Lean 4)

Source: `lean/scripts/packing/*.hl` (43 files, ~119k lines; `flyspeck_devol.hl` excluded from counts).
Targets: new `lean/Kepler/Text/PackingAuto*.lean` modules. Conventions: `V3 = ℝ³`, `space3`,
`Packing` (Kepler/Statement.lean:35), `sol`/`radialNorm` (Kepler/Geom/Volume.lean).

## 1. Totals

| Metric | Value |
|---|---|
| Substantive HL files | 42 (+ flyspeck_devol.hl, statement-only bridge) |
| `new_definition` total | 113 |
| ALL-CAPS `let NAME = prove` theorems | ~1114 (1661 binds incl. tactics/concl) |
| Largest files (lines) | Rogers 10872, OXLZLEZ3 9038, REUHADY 8357, GRUTOTI 8005, counting_spheres 7335 |

## 2. Per-file inventory (defs / thms / top external packing deps)

| HL file | defs | thms | lines | needs most (declared + name-derived) |
|---|---|---|---|---|
| pack1 | 10 | 3 | 602 | none (root; Voronoï open/closed cells) |
| pack2 | 0 | 33 | 521 | pack1; **defines `PACKING` cluster predicate** (Lean: already `Packing`) |
| pack_defs | 51 | 5 | 213 | pack1/2; mcell0–mcell4, cell_params, left_action_list |
| pack_concl | 1 | 0 | 344 | pack1/2; holds `*_concl` statements (URRPHBZ3_concl, GLTVHUM…) |
| pack3 | 1 | 142 | 2529 | pack2, pack_defs (truncate_simplex, omega_list) |
| TARJJUW | 2 | 13 | 577 | none declared (self-contained) |
| OXLZLEZ1 | 23 | 13 | 578 | none (cc_*_model_v1..v11 defs) |
| OXLZLEZ2 | 0 | 39 | 4522 | OXLZLEZ1 |
| bump | 0 | 57 | 1274 | (no declared) uses OXLZLEZ*, Rogers cones; beta_bump |
| Rogers | 0 | 111 | 10872 | pack3, pack_defs, OXLZLEZ2 |
| marchal1 | 0 | 17 | 541 | Rogers, pack1, pack_defs |
| EMNWUUS | 0 | 2 | 525 | marchal1, pack1-3 |
| NJIUTIU | 0 | 2 | 581 | marchal1/2, Rogers |
| TEZFFSK | 0 | 1 | 586 | Rogers, NJIUTIU |
| RVFXZBU | 0 | 1 | 198 | marchal1/2, Rogers |
| HDTFNFZ | 0 | 1 | 114 | marchal2, LEPJBDJ |
| LEPJBDJ | 0 | 2 | 927 | marchal1/2, Rogers |
| marchal2 | 1 | 76 | 6603 | marchal1, Rogers, URRPHBZ2, pack3 |
| YNHYJIT | 0 | 1 | 107 | marchal1/2 (left-action invariance; tiny, real) |
| URRPHBZ1 | 0 | 4 | 688 | marchal1/2 (measurable mcell) |
| URRPHBZ2 | 0 | 6 | 972 | marchal2, LEPJBDJ (eventually-radial mcell4) |
| URRPHBZ3 | 0 | 0 | 71 | capstone; proves `URRPHBZ3_concl` from pack_concl |
| marchal3 | 4 | 57 | 6809 | marchal1/2 + 8 small files |
| DDZUPHJ | 0 | 2 | 611 | marchal1/2, TEZFFSK, NJIUTIU |
| KIZHLTL | 0 | 3 | 1032 | marchal2/3, GRUTOTI, AJRIPQN |
| QZYZMJC | 0 | 2 | 1111 | marchal1/2/3, AJRIPQN |
| QZKSYKG | 0 | 7 | 2255 | Rogers, marchal1/2, YNHYJIT |
| SLTSTLO | 0 | 3 | 3692 | marchal2/3, EMNWUUS, OXLZLEZ2 |
| AJRIPQN | 0 | 4 | 1051 | marchal1/2, SLTSTLO, URRPHBZ1 |
| leaf_cell | 6 | 116 | 4306 | bump, marchal1/2/3, Rogers, AJRIPQN |
| sum_gamma | 1 | 1 | 1465 | bump, UPFZBZM, marchal2/3 |
| UPFZBZM_support_lemmas | 0 | 7 | 374 | pack_defs, pack1-3 |
| UPFZBZM | 0 | 3 | 238 | KIZHLTL, sum_gamma, marchal3 |
| RDWKARC | 0 | 6 | 318 | UPFZBZM, sum_gamma, marchal3 |
| YSSKQOY | 3 | 12 | 551 | TSKAJXY1, counting_spheres (arg lemma bank) |
| TSKAJXY1 | 0 | 6 | 5668 | hub: opens 28 files; carries SET_RULE/SET_TAC + support |
| TSKAJXY2 | 1 | 1 | 731 | TSKAJXY1 (special cases 0/3/4-cells) |
| TSKAJXY3 | 1 | 66 | 2288 | TSKAJXY1 → 2 (remaining cases) |
| counting_spheres | 1 | 92 | 7335 | YSSKQOY, TSKAJXY1, marchal*, Rogers |
| GRUTOTI | 0 | 1 | 8005 | ~everything incl. TSKAJXY3, OXLZLEZ2 |
| REUHADY | 1 | 10 | 8357 | ~everything incl. OXLZLEZ3, RDWKARC |
| OXLZLEZ3 | 6 | 129 | 9038 | 24 files — near-final capstone |

Note: name-derived edges include false positives (HOL builtins TABLE/DROP/REVERSE/HD);
declared `open`/`flyspeck_needs` was used as ground truth for ordering. Apparent cycles
(pack1↔pack2, OXLZLEZ1↔2, UPFZBZM↔_support) dissolve under declared deps.

## 3. External dependencies (not in packing/)

| Dependency | Used by | Count / examples | Lean counterpart |
|---|---|---|---|
| **Vukhacky_tactics + Hales_tactic** | 27 / 10 files | NEW_GOAL 4422, REWRITE_WITH 2963, EXPAND_TAC 2953, UP_ASM_TAC 2713, INTRO_TAC 1004, TYPIFY 960 | **must build a Lean tactic shim first** (biggest cross-cutting cost) |
| **Marchal_cells_2_new** (missing from export!) | 28 files | mcell_set, mcell42/445, *_concl | reconstruct module PackingDefs (MarchalCells2New) |
| Sphere / euler_main_theorem / voronoi / marchal_cells_2 | 29 / 9 / 1 / 8 | barV, hl, omega, azim/dist lemmas | Kepler/Text/Fan, Hypermap, Planarity* |
| formal inequalities (ineq, merge_ineq, flyspeck_constants) | ~6 | beta_bump, delta parameters | Kepler/LP, Kepler/Interval |
| vol chapter (`vol` ×290, radial_norm, sol) | all measure files | vol(ball), sol | Kepler/Geom/Volume.lean ✓ (sol, radialNorm, volume.real) |
| earlier-chapter statements | — | `PACKING` (→ Statement.lean:35 ✓), `saturated` (⚠ not yet on Lean side — port with pack_defs wave), `VOLP`/`BUMP` chapter theorems | Statement.lean + new |

## 4. Scratch / duplicates classification

- **flyspeck_devol.hl** — statement-only bridge (volume-free final statement). Skip; fold 3 theorems into final `PackingConcl.lean`.
- **URRPHBZ1/2/3** — NOT duplicates: a 3-part series. 1 = measurable mcell (re-exports `MEASURABLE_MCELL` as URRPHBZ1), 2 = eventually-radial mcell4, 3 = 71-line capstone using `URRPHBZ3_concl` from pack_concl. Port in order 1→2→3.
- **TSKAJXY1/2/3** — layered: 1 = 5668-line lemma bank + re-exported SET_RULE/SET_TAC, 2 = 0/3/4-cell special cases, 3 = remaining cases (66 thms). Strict chain 1→2→3.
- **UPFZBZM vs UPFZBZM_support_lemmas** — support file first (374 ln), main (238 ln); mutual name-cycle is an artifact.
- **YNHYJIT** — small but genuine (107 ln, 1 thm). Keep.
- **bump.hl** — "REDO THE beta_bump" header; single-version here (no duplicate found).

## 5. Proposed port plan

Prereq batch **P0**: `VukhackyTactics.lean` (NEW_GOAL/REWRITE_WITH/UP_ASM_TAC/EXPAND_TAC/INTRO_TAC as Lean tactics) + `MarchalCells2New.lean` (missing mcell_set family) + `Saturated.lean`.

| Module | Covers | Content | Batch |
|---|---|---|---|
| PackingAuto1 | pack1, pack2 | Voronoï open/closed cells, PACKING | B1 |
| PackingAuto2 | pack_defs, pack_concl | 51 mcell defs + all *_concl statements | B1 |
| PackingAuto3 | TARJJUW, OXLZLEZ1 | self-contained + cc-model defs | B1 (∥) |
| PackingAuto4 | OXLZLEZ2, bump | compressed models (39) + beta_bump (57) | B2 (∥) |
| PackingAuto5 | pack3, Rogers part A | truncate/omega (142) + Rogers bounds | B2 |
| PackingAuto6 | Rogers part B, marchal1 | Rogers (split 2 modules) + marchal1 | B3 |
| PackingAuto7 | EMNWUUS, NJIUTIU, TEZFFSK, RVFXZBU, HDTFNFZ, LEPJBDJ, YNHYJIT, URRPHBZ1 | 8 small independent files | B4 (parallel wave) |
| PackingAuto8 | marchal2, URRPHBZ2, SLTSTLO, DDZUPHJ | marchal cells II | B5 (∥) |
| PackingAuto9 | marchal3, URRPHBZ3, QZKSYKG, QZYZMJC, KIZHLTL | marchal cells III | B6 |
| PackingAuto10 | leaf_cell, AJRIPQN, sum_gamma, YSSKQOY | leaf/cell machinery | B7 (∥) |
| PackingAuto11 | UPFZBZM_support, UPFZBZM, RDWKARC | cluster annulus inequalities | B7 (∥) |
| PackingAuto12 | TSKAJXY1 → TSKAJXY2 → TSKAJXY3 | hub chain (sequential) | B8 |
| PackingAuto13 | counting_spheres | sphere counting (92) | B9 |
| PackingAuto14 | GRUTOTI ∥ REUHADY | two giants, parallelizable | B10 |
| PackingAuto15 | OXLZLEZ3 (+ flyspeck_devol stmt) | final capstone (129) | B11 |

15 modules ≈ 11 sequential batches; batches B1/B4/B7/B10 are internally parallel.
Dependency spine: Auto1→2→(3,4)→5→6→7→8→9→(10,11,12)→13→(14)→15.
