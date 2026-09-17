/-
LocalAuto29 — the ninth micro-file bundle of the appendix-to-Local-Fan
wave (skeleton-first pass). Source: `scripts/local/HIJQAHA.hl`
(4145 ln, 6 `new_definition`s + 112 `prove` items), the terminal
5M2-exhaustion chain of the Local Fan appendix.

Sections (HOL order):
  A. `scs_5M2` edge/diag transfer kit: `SCS_5I1_STAB_DIAG_2h0` (to the
     `scs_5I2` diag-stab), `MM_5M2_IMP_MM_STAB_5I2`, the `2h0_sqrt8`
     window to `scs_5I3`, the edge-pin pair
     `SCS_5M2_EDGE_LE_2H0{,_IMP_0}` (a `> 2*h0` edge forces `l = 0`),
     `MM_5M2_IMP_MM_STAB_5I3`, `SCS_5I1_STAB_DIAG_sqrt8` (to the
     `scs_5M2` diag-stab).
  B. New concrete systems: `scs_5M3` (also carried by
     `Kepler.Text.LocalAuto20` as `scs5M3`; NEEDS merge — this file
     reuses that definition and does NOT restate it), `scs_3T4_prime`,
     `scs_4M6_prime`, `scs_4M7_prime`, `scs_3T1_prime` (via
     `scs_3T1_PRELIM_prime` + the `mk_unadorned_v39` equation), and
     `scs_4M8_prime`. Then `PSORT_5_EXPLICIT` (the 48-row psort table)
     and the `H_SCS_TAC` rewrite kit it feeds.
  C. Per-system `IS_SCS` / `BASIC` / `K` / `J` registries for
     5T1, 5M3, 3T4, 3T6', 3T1, 3T1', 3T4', 4M6', 4M5', 4M6', 4M4',
     4M3', 4M7, 4M7', 4M8, 4M8' (16 IS_SCS giants, 13 BASIC,
     13 K, 12 J).
  D. The `scs_5M3` diag-stab slice kit: `STAB_*_SCS`, the three
     `SCS_DIAG_SCS_5M3_*` computations, `SCS_5M3_SLICE_{02,03,24}`
     arrows, the `*_prime → plain` `BBs`/`MMs`/arrow bridges for
     3T4/4M6/3T1/4M7/4M8, `PROP_OPP_DIAG_5M3_{03,02}`,
     the `{stab_diag i j | diag 5 i j}` set expansions
     (`SET_STAB_5M3`, `EXPAND_STAB_DIAG_5M3`, `SET_EQ_DIAG_STAB_5M3`,
     `SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4`), and the finale
     `SCS_5M2_IMP_SCS_5T1`, `HIJ_STEP_1`, `HIJQAHA`.
  E. The 5M2 auxiliary bounds (`h0_LT_B_SCS_5M2`, `B_LE_CSTAB_5M2`,
     `B_LE_CSTAB_5M2_A_LT_B`, `CARD_SCS_M_5M2`, `SCS_M_5M2`),
     `JCYFMRP_V2/V3`, `ARC_222`, `xrr_le_1553{,_BB}`, `J_SCS_5M2_0`.

Encoding (inherits `Kepler.Text.Polytope` / `Kepler.Text.LocalAuto1`):
- HOL `real^3` <-> `V3`; `dist(v i, v j)` <-> `dist (v i) (v j)`;
  `vec 0` <-> `(0 : V3)`; `collinear` <-> `Collinear ℝ`.
- All toolkit defs live in `Kepler.Text.LocalAuto1` (`isScsV39`,
  `scsBasicV39`, `MMsV39`, `BBsV39`, `scsDiag`, `scsStabDiagV39`,
  `scsPropEquV39`, `scsOppV39`, `scsArrowV39`, `scsM`, `funlistV39`,
  `psort`, `xrr`, `main_nonlinear_terminal_v11`); `arcLength` is
  `Kepler.Text.PackingAuto18.arcLength`.
- `scs_k_v39 s` <-> `s.k`, `scs_J_v39 s i j` <-> `s.J i j`,
  `scs_a_v39`/`scs_b_v39` <-> `s.a`/`s.b`; `SUC n` <-> `n + 1`;
  `~(X = {})` <-> `X ≠ ∅`; `sqrt8` <-> `Real.sqrt 8`;
  `#15.53` <-> `15.53`.
- HOL defines `STAB_5M3_SCS` twice with identical statements
  (HL5 lines 2219 and 2354, the second shadowing the first); both
  bindings are ported (`STAB_5M3_SCS_p29`, `STAB_5M3_SCS_v2_p29`).
- HOL `check_completeness_claimA_concl` is an `Ineq.mk_tplate`
  registry template (not a portable statement); it is skipped here,
  consistent with the registry-twin convention of `LocalAuto27`
  (the `*_concl` axioms in `Kepler.Text.LocalAuto1` carry it).
- Same-wave note: `LocalAuto28`/`LocalAuto30-33` are NOT imported;
  nothing from this file depends on them (no `_p29` copies of
  other-wave material were needed beyond the `scs5M3` reuse above).
- No `native_decide`. Proved items are the mechanical registries
  (BASIC/K/J definitional folding, the `scsDiag` numeral checks,
  the `PSORT_5_EXPLICIT` table, the `scs_3T1_prime` equation, and
  `J_SCS_5M2_0`); all geometric giants are `sorry` with DISCHARGES
  notes.

FILE MAP
  Definitions (`scs5M3` reused from `Kepler.Text.LocalAuto20`):
    `scs3T4Prime_p29` (HOL `scs_3T4_prime`), `scs4M6Prime_p29`,
    `scs4M7Prime_p29`, `scs3T1Prime_p29` (HOL `scs_3T1_prime`,
    defined through the `scs_3T1_PRELIM_prime` tuple so that the
    `mk_unadorned_v39` equation `scs3T1Prime_eq_p29` is `rfl`),
    `scs4M8Prime_p29`.
  Section A (5M2 transfer kit): `SCS_5I1_STAB_DIAG_2h0_p29` (sorry),
    `MM_5M2_IMP_MM_STAB_5I2_p29` (sorry),
    `SCS_5I1_STAB_DIAG_2h0_sqrt8_p29` (sorry),
    `SCS_5M2_EDGE_LE_2H0_p29` (sorry),
    `SCS_5M2_EDGE_LE_2H0_IMP_0_p29` (sorry),
    `MM_5M2_IMP_MM_STAB_5I3_p29` (sorry),
    `SCS_5I1_STAB_DIAG_sqrt8_p29` (sorry).
  Section B: `PSORT_5_EXPLICIT_p29` (proved).
  Section C: `SCS_*_IS_SCS_p29` x16 (sorry), `SCS_*_BASIC_p29` x13
    (proved), `K_SCS_*_p29` x13 (proved), `J_SCS_*_p29` x12
    (proved).
  Section D: `STAB_5I1_SCS_p29` (sorry), `STAB_5I2_SCS_p29` (sorry),
    `STAB_5M3_SCS_p29` (sorry), `STAB_5M3_SCS_v2_p29` (sorry, the
    HOL duplicate binding), `SCS_5M3_STAB_DIAG_sqrt8_p29` (sorry),
    `SCS_DIAG_SCS_5M3_{02,03,24}_p29` (proved),
    `MM_5M2_IMP_MM_STAB_5M3_p29` (sorry), the BB/MM/arrow bridges
    for 3T4/4M6/3T1/4M7/4M8 primes (sorry),
    `SCS_5M3_SLICE_{02,03,24}_p29` (sorry),
    `SCS_5M3_{02,03,24}_ARROW_*_p29` (sorry),
    `PROP_OPP_DIAG_5M3_{03,02}_p29` (sorry),
    `SET_STAB_5M3_p29`, `EXPAND_STAB_DIAG_5M3_p29`,
    `SET_EQ_DIAG_STAB_5M3_p29`,
    `SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4_p29` (sorry).
  Section E: `h0_LT_B_SCS_5M2_p29`, `B_LE_CSTAB_5M2_p29`,
    `B_LE_CSTAB_5M2_A_LT_B_p29`, `CARD_SCS_M_5M2_p29`,
    `SCS_M_5M2_p29` (sorry), `JCYFMRP_V2_p29`, `JCYFMRP_V3_p29`
    (sorry), `ARC_222_p29` (sorry), `xrr_le_1553_p29`,
    `xrr_le_1553_BB_p29` (sorry), `J_SCS_5M2_0_p29` (proved),
    `SCS_5M2_IMP_SCS_5T1_p29`, `HIJ_STEP_1_p29`, `HIJQAHA_p29`
    (sorry).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto20
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section B0: the new concrete systems (HIJQAHA.hl:505-548) -/

/-- HOL `scs_3T4_prime` (HIJQAHA.hl:510). -/
noncomputable def scs3T4Prime_p29 : ScsV39 :=
  mkUnadornedV39 3 0.2759
    (funlistV39 [((0, 1), 2), ((1, 2), cstab)] (2 * h0) 3)
    (funlistV39 [((0, 1), 2 * h0)] cstab 3)

/-- HOL `scs_4M6_prime` (HIJQAHA.hl:516). -/
noncomputable def scs4M6Prime_p29 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_4M7_prime` (HIJQAHA.hl:522). -/
noncomputable def scs4M7Prime_p29 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), cstab), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((1, 2), cstab), ((0, 2), 6), ((1, 3), 6),
      ((1, 3), 6)] (2 * h0) 4)

/-- HOL `scs_3T1_PRELIM_prime` (HIJQAHA.hl:528): the raw `scs_v39` tuple
defining `scs_3T1_prime`. -/
noncomputable def scs3T1Prime_p29 : ScsV39 :=
  ScsV39.mk 3 0.11 (funlistV39 [((0, 1), cstab)] 2 3)
    (funlistV39 [((0, 1), cstab)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3)
    (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False)

/-- HOL `scs_3T1_prime` (HIJQAHA.hl:536): the `mk_unadorned_v39` equation. -/
theorem scs3T1Prime_eq_p29 : scs3T1Prime_p29 = mkUnadornedV39 3 0.11
    (funlistV39 [((0, 1), cstab)] 2 3)
    (funlistV39 [((0, 1), cstab)] (2 * h0) 3) := rfl

/-- HOL `scs_4M8_prime` (HIJQAHA.hl:545). -/
noncomputable def scs4M8Prime_p29 : ScsV39 :=
  mkUnadornedV39 4 0.513
    (funlistV39 [((0, 1), 2 * h0), ((2, 3), cstab), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4)
    (funlistV39 [((0, 1), cstab), ((2, 3), cstab), ((0, 2), 6), ((1, 3), 6),
      ((1, 3), 6)] (2 * h0) 4)

/-- HOL `PSORT_5_EXPLICIT` (HIJQAHA.hl:552). -/
theorem PSORT_5_EXPLICIT_p29 :
    psort 5 (0, 0) = (0, 0) ∧ psort 5 (1, 1) = (1, 1) ∧
    psort 5 (2, 2) = (2, 2) ∧ psort 5 (3, 3) = (3, 3) ∧
    psort 5 (4, 4) = (4, 4) ∧ psort 5 (0, 1) = (0, 1) ∧
    psort 5 (0, 2) = (0, 2) ∧ psort 5 (0, 3) = (0, 3) ∧
    psort 5 (0, 4) = (0, 4) ∧ psort 5 (1, 0) = (0, 1) ∧
    psort 5 (1, 2) = (1, 2) ∧ psort 5 (1, 3) = (1, 3) ∧
    psort 5 (1, 4) = (1, 4) ∧ psort 5 (2, 0) = (0, 2) ∧
    psort 5 (2, 1) = (1, 2) ∧ psort 5 (2, 3) = (2, 3) ∧
    psort 5 (2, 4) = (2, 4) ∧ psort 5 (3, 0) = (0, 3) ∧
    psort 5 (3, 1) = (1, 3) ∧ psort 5 (3, 2) = (2, 3) ∧
    psort 5 (3, 4) = (3, 4) ∧ psort 5 (4, 0) = (0, 4) ∧
    psort 5 (4, 1) = (1, 4) ∧ psort 5 (4, 2) = (2, 4) ∧
    psort 5 (4, 3) = (3, 4) ∧ psort 5 (4, 5) = (0, 4) ∧
    psort 5 (3, 5) = (0, 3) ∧ psort 5 (2, 5) = (0, 2) ∧
    psort 5 (1, 5) = (0, 1) ∧ psort 5 (5, 1) = (0, 1) ∧
    psort 5 (5, 2) = (0, 2) ∧ psort 5 (5, 3) = (0, 3) ∧
    psort 5 (5, 4) = (0, 4) ∧ psort 5 (5, 5) = (0, 0) ∧
    psort 5 (5, 6) = (0, 1) ∧ psort 5 (5, 7) = (0, 2) ∧
    psort 5 (4, 6) = (1, 4) ∧ psort 5 (6, 4) = (1, 4) ∧
    psort 5 (6, 5) = (0, 1) ∧ psort 5 (6, 7) = (1, 2) ∧
    psort 5 (7, 5) = (0, 2) ∧ psort 5 (7, 6) = (1, 2) ∧
    psort 5 (7, 7) = (2, 2) ∧ psort 5 (6, 6) = (1, 1) ∧
    psort 4 (3, 4) = (0, 3) ∧ psort 3 (2, 0) = (0, 2) ∧
    psort 3 (2, 1) = (1, 2) ∧ psort 3 (1, 0) = (0, 1) := by
  simp only [psort]
  repeat' constructor

/-! ## Section A: the `scs_5M2` transfer kit (HIJQAHA.hl:97-495) -/

/-- HOL `SCS_5I1_STAB_DIAG_2h0` (HIJQAHA.hl:97). -/
theorem SCS_5I1_STAB_DIAG_2h0_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    (∀ i, dist (v i) (v (i + 1)) ≤ 2 * h0) →
    BBsV39 (scsStabDiagV39 scs5I2 i j) v := by
  sorry
  -- DISCHARGES: HL SCS_TAC expansion of `scs_5I2`/`scs_5M2` tables plus
  -- `stab_diag` folding; the a-edge `≤ 2*h0` hypothesis pins the
  -- lowered diagonal bounds.

/-- HOL `MM_5M2_IMP_MM_STAB_5I2` (HIJQAHA.hl:209). -/
theorem MM_5M2_IMP_MM_STAB_5I2_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    v ∈ MMsV39 scs5M2 → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    (∀ i, dist (v i) (v (i + 1)) ≤ 2 * h0) →
    MMsV39 (scsStabDiagV39 scs5I2 i j) ≠ ∅ := by
  sorry
  -- DISCHARGES: HL SCS_TAC + `MMs` nonemptyness from the transferred
  -- `BBs` witness via `SCS_5I1_STAB_DIAG_2h0` and `taustar` negativity.

/-- HOL `SCS_5I1_STAB_DIAG_2h0_sqrt8` (HIJQAHA.hl:229). -/
theorem SCS_5I1_STAB_DIAG_2h0_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 ≤ dist (v 0) (v 1) → dist (v 0) (v 1) ≤ Real.sqrt 8 →
    BBsV39 (scsStabDiagV39 scs5I3 i j) v := by
  sorry
  -- DISCHARGES: HL SCS_TAC expansion of the `scs_5I3` funlist tables
  -- against the `2*h0 ≤ dist(v 0,v 1) ≤ sqrt8` window.

/-- HOL `SCS_5M2_EDGE_LE_2H0` (HIJQAHA.hl:379). -/
theorem SCS_5M2_EDGE_LE_2H0_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) → l % 5 ≠ 0 → False := by
  sorry
  -- DISCHARGES: HL case analysis on `l MOD 5` with the `scs_5M2`
  -- b-table (`cstab` edge bounds) contradicting `2*h0 <` off vertex 0.

/-- HOL `SCS_5M2_EDGE_LE_2H0_IMP_0` (HIJQAHA.hl:408). -/
theorem SCS_5M2_EDGE_LE_2H0_IMP_0_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) → l % 5 = 0 := by
  sorry
  -- DISCHARGES: HL `MESON[SCS_5M2_EDGE_LE_2H0]` — classical contrapose
  -- of `SCS_5M2_EDGE_LE_2H0_p29`.

/-- HOL `MM_5M2_IMP_MM_STAB_5I3` (HIJQAHA.hl:419). -/
theorem MM_5M2_IMP_MM_STAB_5I3_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    v ∈ MMsV39 scs5M2 → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) →
    dist (v l) (v (l + 1)) ≤ Real.sqrt 8 →
    MMsV39 (scsStabDiagV39 scs5I3 i j) ≠ ∅ := by
  sorry
  -- DISCHARGES: HL SCS_TAC on the `scs_5I3` tables with the
  -- `(2*h0, sqrt8]` edge window; nonemptyness via `MMs` transfer.

/-- HOL `SCS_5I1_STAB_DIAG_sqrt8` (HIJQAHA.hl:452). -/
theorem SCS_5I1_STAB_DIAG_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    Real.sqrt 8 ≤ dist (v 0) (v 1) →
    BBsV39 (scsStabDiagV39 scs5M2 i j) v := by
  sorry
  -- DISCHARGES: HL SCS_TAC on `scs_stab_diag_v39 scs_5M2`: the stabbed
  -- b-table is `cstab` exactly at the psort(5,(i,j)) pair, so the
  -- `sqrt8 ≤` edge bound covers the raised diagonal.

/-! ## Section C1: `is_scs_v39` verifications (HIJQAHA.hl:616-2067) -/

/-- HOL `SCS_5T1_IS_SCS` (HIJQAHA.hl:616). -/
theorem SCS_5T1_IS_SCS_p29 : isScsV39 scs5T1 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_5T1` (`cs_adj` tables,
  -- `d_tame 5`, MOD-periodicity case work).

/-- HOL `SCS_5M3_IS_SCS` (HIJQAHA.hl:688). -/
theorem SCS_5M3_IS_SCS_p29 : isScsV39 scs5M3 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_5M3` funlist tables
  -- (`PSORT_5_EXPLICIT_p29`, `FUNLIST_EXPLICIT`).

/-- HOL `SCS_3T4_IS_SCS` (HIJQAHA.hl:780). -/
theorem SCS_3T4_IS_SCS_p29 : isScsV39 scs3T4 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_3T4`.

/-- HOL `SCS_3T6_IS_SCS` (HIJQAHA.hl:853). -/
theorem SCS_3T6_IS_SCS_p29 : isScsV39 scs3T6' := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_3T6'`.

/-- HOL `SCS_3T1_prime_IS_SCS` (HIJQAHA.hl:912). -/
theorem SCS_3T1_prime_IS_SCS_p29 : isScsV39 scs3T1Prime_p29 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC via `scs_3T1_prime` equation
  -- (`scs3T1Prime_eq_p29`), then the 3-row case work.

/-- HOL `SCS_3T1_IS_SCS` (HIJQAHA.hl:988). -/
theorem SCS_3T1_IS_SCS_p29 : isScsV39 scs3T1 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_3T1`.

/-- HOL `SCS_3T4_prime_IS_SCS` (HIJQAHA.hl:1068). -/
theorem SCS_3T4_prime_IS_SCS_p29 : isScsV39 scs3T4Prime_p29 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_3T4_prime`.

/-- HOL `SCS_4M6_IS_SCS` (HIJQAHA.hl:1140). -/
theorem SCS_4M6_IS_SCS_p29 : isScsV39 scs4M6' := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M6'`.

/-- HOL `SCS_4M5_IS_SCS` (HIJQAHA.hl:1234). -/
theorem SCS_4M5_IS_SCS_p29 : isScsV39 scs4M5' := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M5'`.

/-- HOL `SCS_4M6_prime_IS_SCS` (HIJQAHA.hl:1355). -/
theorem SCS_4M6_prime_IS_SCS_p29 : isScsV39 scs4M6Prime_p29 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M6_prime`.

/-- HOL `SCS_4M4_IS_SCS` (HIJQAHA.hl:1447). -/
theorem SCS_4M4_IS_SCS_p29 : isScsV39 scs4M4' := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M4'`.

/-- HOL `SCS_4M3_IS_SCS` (HIJQAHA.hl:1548). -/
theorem SCS_4M3_IS_SCS_p29 : isScsV39 scs4M3' := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M3'`.

/-- HOL `SCS_4M7_IS_SCS` (HIJQAHA.hl:1649). -/
theorem SCS_4M7_IS_SCS_p29 : isScsV39 scs4M7 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M7` (note the doubled
  -- `(1,3)` row in the b-table, verbatim from the source).

/-- HOL `SCS_4M7_prime_IS_SCS` (HIJQAHA.hl:1753). -/
theorem SCS_4M7_prime_IS_SCS_p29 : isScsV39 scs4M7Prime_p29 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M7_prime`.

/-- HOL `SCS_4M8_IS_SCS` (HIJQAHA.hl:1855). -/
theorem SCS_4M8_IS_SCS_p29 : isScsV39 scs4M8 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M8`.

/-- HOL `SCS_4M8_prime_IS_SCS` (HIJQAHA.hl:1959). -/
theorem SCS_4M8_prime_IS_SCS_p29 : isScsV39 scs4M8Prime_p29 := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC expansion of `scs_4M8_prime`.

/-! ## Section C2: `scs_basic_v39` (HIJQAHA.hl:2068-2112) -/

/-- HOL `SCS_5M3_BASIC` (HIJQAHA.hl:2068). -/
theorem SCS_5M3_BASIC_p29 : scsBasicV39 scs5M3 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_5T1_BASIC` (HIJQAHA.hl:2071). -/
theorem SCS_5T1_BASIC_p29 : scsBasicV39 scs5T1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M6_prime_BASIC` (HIJQAHA.hl:2076). -/
theorem SCS_4M6_prime_BASIC_p29 : scsBasicV39 scs4M6Prime_p29 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M7_prime_BASIC` (HIJQAHA.hl:2079). -/
theorem SCS_4M7_prime_BASIC_p29 : scsBasicV39 scs4M7Prime_p29 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M4_BASIC` (HIJQAHA.hl:2082). -/
theorem SCS_4M4_BASIC_p29 : scsBasicV39 scs4M4' :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M7_BASIC` (HIJQAHA.hl:2086). -/
theorem SCS_4M7_BASIC_p29 : scsBasicV39 scs4M7 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M3_BASIC` (HIJQAHA.hl:2089). -/
theorem SCS_4M3_BASIC_p29 : scsBasicV39 scs4M3' :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M5_BASIC` (HIJQAHA.hl:2092). -/
theorem SCS_4M5_BASIC_p29 : scsBasicV39 scs4M5' :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3T4_prime_BASIC` (HIJQAHA.hl:2095). -/
theorem SCS_3T4_prime_BASIC_p29 : scsBasicV39 scs3T4Prime_p29 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3T6_BASIC` (HIJQAHA.hl:2098). -/
theorem SCS_3T6_BASIC_p29 : scsBasicV39 scs3T6' :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_3T1_prime_BASIC` (HIJQAHA.hl:2102). -/
theorem SCS_3T1_prime_BASIC_p29 : scsBasicV39 scs3T1Prime_p29 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M8_prime_BASIC` (HIJQAHA.hl:2105). -/
theorem SCS_4M8_prime_BASIC_p29 : scsBasicV39 scs4M8Prime_p29 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- HOL `SCS_4M8_BASIC` (HIJQAHA.hl:2109). -/
theorem SCS_4M8_BASIC_p29 : scsBasicV39 scs4M8 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-! ## Section C3: the `scs_k_v39` projections (HIJQAHA.hl:2113-2153) -/

/-- HOL `K_SCS_5M3` (HIJQAHA.hl:2113). -/
theorem K_SCS_5M3_p29 : scs5M3.k = 5 := rfl

/-- HOL `K_SCS_5T1` (HIJQAHA.hl:2116). -/
theorem K_SCS_5T1_p29 : scs5T1.k = 5 := rfl

/-- HOL `K_SCS_3T4_prime` (HIJQAHA.hl:2119). -/
theorem K_SCS_3T4_prime_p29 : scs3T4Prime_p29.k = 3 := rfl

/-- HOL `K_SCS_3T6` (HIJQAHA.hl:2122). -/
theorem K_SCS_3T6_p29 : scs3T6'.k = 3 := rfl

/-- HOL `K_SCS_4M4` (HIJQAHA.hl:2125). -/
theorem K_SCS_4M4_p29 : scs4M4'.k = 4 := rfl

/-- HOL `K_SCS_4M5` (HIJQAHA.hl:2128). -/
theorem K_SCS_4M5_p29 : scs4M5'.k = 4 := rfl

/-- HOL `K_SCS_4M3` (HIJQAHA.hl:2131). -/
theorem K_SCS_4M3_p29 : scs4M3'.k = 4 := rfl

/-- HOL `K_SCS_4M6_prime` (HIJQAHA.hl:2134). -/
theorem K_SCS_4M6_prime_p29 : scs4M6Prime_p29.k = 4 := rfl

/-- HOL `K_SCS_3T1_prime` (HIJQAHA.hl:2137). -/
theorem K_SCS_3T1_prime_p29 : scs3T1Prime_p29.k = 3 := rfl

/-- HOL `K_SCS_4M7_prime` (HIJQAHA.hl:2141). -/
theorem K_SCS_4M7_prime_p29 : scs4M7Prime_p29.k = 4 := rfl

/-- HOL `K_SCS_4M7` (HIJQAHA.hl:2144). -/
theorem K_SCS_4M7_p29 : scs4M7.k = 4 := rfl

/-- HOL `K_SCS_4M8_prime` (HIJQAHA.hl:2148). -/
theorem K_SCS_4M8_prime_p29 : scs4M8Prime_p29.k = 4 := rfl

/-- HOL `K_SCS_4M8` (HIJQAHA.hl:2151). -/
theorem K_SCS_4M8_p29 : scs4M8.k = 4 := rfl

/-! ## Section C4: the `scs_J_v39` emptiness registries (HIJQAHA.hl:2155-2193) -/

/-- HOL `J_SCS_3T4_prime` (HIJQAHA.hl:2155). -/
theorem J_SCS_3T4_prime_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T4Prime_p29 i).J i1 j = False := rfl

/-- HOL `J_SCS_4M4` (HIJQAHA.hl:2159). -/
theorem J_SCS_4M4_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M4' i).J i1 j = False := rfl

/-- HOL `J_SCS_4M3` (HIJQAHA.hl:2163). -/
theorem J_SCS_4M3_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M3' i).J i1 j = False := rfl

/-- HOL `J_SCS_4M5` (HIJQAHA.hl:2166). -/
theorem J_SCS_4M5_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M5' i).J i1 j = False := rfl

/-- HOL `J_SCS_4M6_prime` (HIJQAHA.hl:2169). -/
theorem J_SCS_4M6_prime_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M6Prime_p29 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T1_prime` (HIJQAHA.hl:2172). -/
theorem J_SCS_3T1_prime_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T1Prime_p29 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T1` (HIJQAHA.hl:2175). -/
theorem J_SCS_3T1_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T1 i).J i1 j = False := rfl

/-- HOL `J_SCS_3T6` (HIJQAHA.hl:2178). -/
theorem J_SCS_3T6_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs3T6' i).J i1 j = False := rfl

/-- HOL `J_SCS_4M7_prime` (HIJQAHA.hl:2181). -/
theorem J_SCS_4M7_prime_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M7Prime_p29 i).J i1 j = False := rfl

/-- HOL `J_SCS_4M7` (HIJQAHA.hl:2184). -/
theorem J_SCS_4M7_J_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M7 i).J i1 j = False := rfl

/-- HOL `J_SCS_4M8` (HIJQAHA.hl:2187). -/
theorem J_SCS_4M8_p29 (i i1 j : ℕ) :
    (scsPropEquV39 scs4M8 i).J i1 j = False := rfl

/-- HOL `J_SCS_4M8_prime1` (HIJQAHA.hl:2190): directly on `scs_4M8_prime`,
without the `scs_prop_equ_v39` wrapper. -/
theorem J_SCS_4M8_prime1_p29 (i1 j : ℕ) :
    scs4M8Prime_p29.J i1 j = False := rfl

/-! ## Section D1: diag-stab verifications and `scs_5M3` basics
(HIJQAHA.hl:2196-2363) -/

/-- HOL `STAB_5I1_SCS` (HIJQAHA.hl:2196). -/
theorem STAB_5I1_SCS_p29 (i j : ℕ) : scsDiag scs5I1.k i j →
    isScsV39 (scsStabDiagV39 scs5I1 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I1 i j) := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC on the `scs_stab_diag_v39` unfolding of
  -- `scs_5I1` (`cs_adj`/`d_tame` periodicity case work).

/-- HOL `STAB_5I2_SCS` (HIJQAHA.hl:2207). -/
theorem STAB_5I2_SCS_p29 (i j : ℕ) : scsDiag scs5I2.k i j →
    isScsV39 (scsStabDiagV39 scs5I2 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5I2 i j) := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC on the `scs_stab_diag_v39` unfolding of
  -- `scs_5I2`.

/-- HOL `STAB_5M3_SCS` (HIJQAHA.hl:2219). -/
theorem STAB_5M3_SCS_p29 (i j : ℕ) : scsDiag scs5M3.k i j →
    isScsV39 (scsStabDiagV39 scs5M3 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5M3 i j) := by
  sorry
  -- DISCHARGES: HL H_SCS_TAC on the `scs_stab_diag_v39` unfolding of
  -- `scs_5M3` funlist tables.

/-- HOL `STAB_5M3_SCS` — the SHADOWING DUPLICATE binding (HIJQAHA.hl:2354):
identical statement re-proved in the source (the second `let` shadows the
first); ported as its own binding for faithfulness. -/
theorem STAB_5M3_SCS_v2_p29 : ∀ (i j : ℕ), scsDiag scs5M3.k i j →
    isScsV39 (scsStabDiagV39 scs5M3 i j) ∧ scsBasicV39 (scsStabDiagV39 scs5M3 i j) :=
  STAB_5M3_SCS_p29

/-- HOL `SCS_5M3_STAB_DIAG_sqrt8` (HIJQAHA.hl:2231). -/
theorem SCS_5M3_STAB_DIAG_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    Real.sqrt 8 ≤ dist (v 0) (v 1) →
    BBsV39 (scsStabDiagV39 scs5M3 i j) v := by
  sorry
  -- DISCHARGES: HL SCS_TAC on the `scs_5M3` stabbed b-table; the
  -- `sqrt8 ≤` edge bound covers the raised `cstab` diagonal.

/-- HOL `SCS_DIAG_SCS_5M3_02` (HIJQAHA.hl:2305). -/
theorem SCS_DIAG_SCS_5M3_02_p29 : scsDiag scs5M3.k 0 2 := by
  rw [K_SCS_5M3_p29]
  unfold scsDiag
  decide

/-- HOL `SCS_DIAG_SCS_5M3_03` (HIJQAHA.hl:2309). -/
theorem SCS_DIAG_SCS_5M3_03_p29 : scsDiag scs5M3.k 0 3 := by
  rw [K_SCS_5M3_p29]
  unfold scsDiag
  decide

/-- HOL `SCS_DIAG_SCS_5M3_24` (HIJQAHA.hl:2313). -/
theorem SCS_DIAG_SCS_5M3_24_p29 : scsDiag scs5M3.k 2 4 := by
  rw [K_SCS_5M3_p29]
  unfold scsDiag
  decide

/-- HOL `MM_5M2_IMP_MM_STAB_5M3` (HIJQAHA.hl:2318). -/
theorem MM_5M2_IMP_MM_STAB_5M3_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    v ∈ MMsV39 scs5M2 → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    Real.sqrt 8 ≤ dist (v l) (v (l + 1)) →
    MMsV39 (scsStabDiagV39 scs5M3 i j) ≠ ∅ := by
  sorry
  -- DISCHARGES: HL SCS_TAC on the `scs_5M3` stabbed tables with the
  -- `sqrt8 ≤` edge bound; nonemptyness via `MMs` transfer.

/-! ## Section D2: prime-to-plain bridges and the `scs_5M3` slices
(HIJQAHA.hl:2365-3101) -/

/-- HOL `BB_3T4_prime_IMP_scs_3T4` (HIJQAHA.hl:2365). -/
theorem BB_3T4_prime_IMP_scs_3T4_p29 (v : ℕ → V3) :
    BBsV39 scs3T4Prime_p29 v → BBsV39 scs3T4 v := by
  sorry
  -- DISCHARGES: HL SCS_TAC table comparison: `scs_3T4_prime` carries the
  -- extra `(1,2) -> cstab` lower row, dominating `scs_3T4`'s `2*h0`
  -- default once `2*h0 ≤ cstab` is used.

/-- HOL `MM_3T4_prime_IMP_MM_3T4` (HIJQAHA.hl:2378). -/
theorem MM_3T4_prime_IMP_MM_3T4_p29 (v : ℕ → V3) :
    v ∈ MMsV39 scs3T4Prime_p29 → MMsV39 scs3T4 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL MESON over `SCS_3T4_IS_SCS`, `K_SCS_3T4{,_prime}`,
  -- membership, and `BB_3T4_prime_IMP_scs_3T4`.

/-- HOL `SCS_3T4_prime_ARROW_MM_3T4` (HIJQAHA.hl:2390). -/
theorem SCS_3T4_prime_ARROW_MM_3T4_p29 :
    scsArrowV39 {scs3T4Prime_p29} {scs3T4} := by
  sorry
  -- DISCHARGES: HL `SCS_TAC` + the two preceding bridges.

/-- HOL `BB_4M6_prime_IMP_scs_4M6` (HIJQAHA.hl:2415). -/
theorem BB_4M6_prime_IMP_scs_4M6_p29 (v : ℕ → V3) :
    BBsV39 scs4M6Prime_p29 v → BBsV39 scs4M6' v := by
  sorry
  -- DISCHARGES: HL SCS_TAC table comparison of `scs_4M6_prime` against
  -- `scs_4M6'` (lower rows of `scs_4M6'` are pointwise smaller).

/-- HOL `MM_4M6_prime_IMP_MM_4M6` (HIJQAHA.hl:2436). -/
theorem MM_4M6_prime_IMP_MM_4M6_p29 (v : ℕ → V3) :
    v ∈ MMsV39 scs4M6Prime_p29 → MMsV39 scs4M6' ≠ ∅ := by
  sorry
  -- DISCHARGES: HL MESON over `SCS_4M6_IS_SCS`, `K_SCS_4M6{,_prime}`,
  -- membership, and `BB_4M6_prime_IMP_scs_4M6`.

/-- HOL `SCS_4M6_prime_ARROW_MM_4M6` (HIJQAHA.hl:2449). -/
theorem SCS_4M6_prime_ARROW_MM_4M6_p29 :
    scsArrowV39 {scs4M6Prime_p29} {scs4M6'} := by
  sorry
  -- DISCHARGES: HL `SCS_TAC` + the two preceding bridges.

/-- HOL `SCS_5M3_SLICE_02` (HIJQAHA.hl:2475): the 0-2 diag-stab of
`scs_5M3` arrows to the pair of prop-equa slices. -/
theorem SCS_5M3_SLICE_02_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 0 2}
      {scsPropEquV39 scs3T4Prime_p29 2, scsPropEquV39 scs4M6Prime_p29 1} := by
  sorry
  -- DISCHARGES: HL `is_scs_slice_v39` verification plus the slice
  -- arrow machinery (`SLICE_IS_UNADORNED`, `LKGRQUI` kit).

/-- HOL `SCS_5M3_02_ARROW_3T4_4M6` (HIJQAHA.hl:2594). -/
theorem SCS_5M3_02_ARROW_3T4_4M6_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 0 2} {scs3T4, scs4M6'} := by
  sorry
  -- DISCHARGES: HL FTRANS over `SCS_5M3_SLICE_02`, the prop-equa arrow
  -- `YXIONXL3`, and the two prime bridges.

/-- HOL `BB_3T1_prime_IMP_scs_3T1` (HIJQAHA.hl:2756). -/
theorem BB_3T1_prime_IMP_scs_3T1_p29 (v : ℕ → V3) :
    BBsV39 scs3T1Prime_p29 v → BBsV39 scs3T1 v := by
  sorry
  -- DISCHARGES: HL SCS_TAC table comparison: `sqrt8 ≤ cstab` on the
  -- (0,1) lower row, other rows equal.

/-- HOL `MM_3T1_prime_IMP_MM_3T1` (HIJQAHA.hl:2771). -/
theorem MM_3T1_prime_IMP_MM_3T1_p29 (v : ℕ → V3) :
    v ∈ MMsV39 scs3T1Prime_p29 → MMsV39 scs3T1 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL MESON over `SCS_3T1_IS_SCS`, `K_SCS_3T1{,_prime}`,
  -- membership, and `BB_3T1_prime_IMP_scs_3T1`.

/-- HOL `SCS_3T1_prime_ARROW_MM_3T1` (HIJQAHA.hl:2786). -/
theorem SCS_3T1_prime_ARROW_MM_3T1_p29 :
    scsArrowV39 {scs3T1Prime_p29} {scs3T1} := by
  sorry
  -- DISCHARGES: HL `SCS_TAC` + the two preceding bridges.

/-- HOL `BB_4M7_prime_IMP_scs_4M7` (HIJQAHA.hl:2813). -/
theorem BB_4M7_prime_IMP_scs_4M7_p29 (v : ℕ → V3) :
    BBsV39 scs4M7Prime_p29 v → BBsV39 scs4M7 v := by
  sorry
  -- DISCHARGES: HL SCS_TAC table comparison of `scs_4M7_prime` against
  -- `scs_4M7` (identical tables up to row order).

/-- HOL `MM_4M7_prime_IMP_MM_4M7` (HIJQAHA.hl:2827). -/
theorem MM_4M7_prime_IMP_MM_4M7_p29 (v : ℕ → V3) :
    v ∈ MMsV39 scs4M7Prime_p29 → MMsV39 scs4M7 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL MESON over `SCS_4M7_IS_SCS`, `K_SCS_4M7{,_prime}`,
  -- membership, and `BB_4M7_prime_IMP_scs_4M7`.

/-- HOL `SCS_4M7_prime_ARROW_MM_4M7` (HIJQAHA.hl:2842). -/
theorem SCS_4M7_prime_ARROW_MM_4M7_p29 :
    scsArrowV39 {scs4M7Prime_p29} {scs4M7} := by
  sorry
  -- DISCHARGES: HL `SCS_TAC` + the two preceding bridges.

/-- HOL `SCS_5M3_03_ARROW_3T1_4M7` (HIJQAHA.hl:2867). -/
theorem SCS_5M3_03_ARROW_3T1_4M7_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 0 3} {scs4M7, scs3T1} := by
  sorry
  -- DISCHARGES: HL FTRANS over the 0-3 slice pair and the prime
  -- bridges for 3T1 and 4M7.

/-- HOL `BB_4M8_prime_IMP_scs_4M8` (HIJQAHA.hl:3018). -/
theorem BB_4M8_prime_IMP_scs_4M8_p29 (v : ℕ → V3) :
    BBsV39 scs4M8Prime_p29 v → BBsV39 scs4M8 v := by
  sorry
  -- DISCHARGES: HL SCS_TAC table comparison of `scs_4M8_prime` against
  -- `scs_4M8` (identical tables up to row order).

/-- HOL `MM_4M8_prime_IMP_MM_4M8` (HIJQAHA.hl:3032). -/
theorem MM_4M8_prime_IMP_MM_4M8_p29 (v : ℕ → V3) :
    v ∈ MMsV39 scs4M8Prime_p29 → MMsV39 scs4M8 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL MESON over `SCS_4M8_IS_SCS`, `K_SCS_4M8{,_prime}`,
  -- membership, and `BB_4M8_prime_IMP_scs_4M8`.

/-- HOL `SCS_4M8_prime_ARROW_MM_4M8` (HIJQAHA.hl:3047). -/
theorem SCS_4M8_prime_ARROW_MM_4M8_p29 :
    scsArrowV39 {scs4M8Prime_p29} {scs4M8} := by
  sorry
  -- DISCHARGES: HL `SCS_TAC` + the two preceding bridges.

/-- HOL `SCS_5M3_SLICE_24` (HIJQAHA.hl:2896). -/
theorem SCS_5M3_SLICE_24_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 2 4}
      {scsPropEquV39 scs3T1Prime_p29 1, scsPropEquV39 scs4M8Prime_p29 3} := by
  sorry
  -- DISCHARGES: HL `is_scs_slice_v39` verification plus the slice
  -- arrow machinery.

/-- HOL `SCS_5M3_SLICE_03` (HIJQAHA.hl:2623). -/
theorem SCS_5M3_SLICE_03_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 0 3}
      {scsPropEquV39 scs4M7Prime_p29 1, scsPropEquV39 scs3T1Prime_p29 1} := by
  sorry
  -- DISCHARGES: HL `is_scs_slice_v39` verification plus the slice
  -- arrow machinery.

/-- HOL `SCS_5M3_24_ARROW_3T1_4M8` (HIJQAHA.hl:3073). -/
theorem SCS_5M3_24_ARROW_3T1_4M8_p29 :
    scsArrowV39 {scsStabDiagV39 scs5M3 2 4} {scs3T1, scs4M8} := by
  sorry
  -- DISCHARGES: HL FTRANS over `SCS_5M3_SLICE_24`, the prop-equa
  -- arrow, and the prime bridges for 3T1 and 4M8.

/-- HOL `PROP_OPP_DIAG_5M3_03` (HIJQAHA.hl:3103). -/
theorem PROP_OPP_DIAG_5M3_03_p29 :
    scsStabDiagV39 scs5M3 0 3 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M3 1 3)) 3 := by
  sorry
  -- DISCHARGES: HL definitional expansion of `scs_stab_diag_v39` /
  -- `scs_opp_v39` / `scs_prop_equ_v39` with the `psort` tables
  -- (`PSORT_5_EXPLICIT`, `PSORT_PERIODIC`).

/-- HOL `PROP_OPP_DIAG_5M3_02` (HIJQAHA.hl:3142). -/
theorem PROP_OPP_DIAG_5M3_02_p29 :
    scsStabDiagV39 scs5M3 0 2 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M3 1 4)) 3 := by
  sorry
  -- DISCHARGES: HL definitional expansion as for the 0-3 twin.

/-! ## Section D3: the `{stab_diag i j | diag 5 i j}` set expansions
(HIJQAHA.hl:3179-3313) -/

/-- HOL `SET_STAB_5M3` (HIJQAHA.hl:3179). -/
theorem SET_STAB_5M3_p29 :
    {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5M3 i j = t} =
    {t | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
      scsStabDiagV39 scs5M3 (i % 5) (j % 5) = t} := by
  sorry
  -- DISCHARGES: HL set-equality sweep through the `MOD 5` residues
  -- (`PSORT_PERIODIC`, `DIAG_MOD`).

/-- HOL `EXPAND_STAB_DIAG_5M3` (HIJQAHA.hl:3184). -/
theorem EXPAND_STAB_DIAG_5M3_p29 :
    {t | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      scsStabDiagV39 scs5M3 (i % 5) (j % 5) = t} =
    {t | ∃ i, i < 5 ∧ scsStabDiagV39 scs5M3 (i + 2) i = t} := by
  sorry
  -- DISCHARGES: HL residue case work listing the five stab pairs
  -- (`(0,3),(3,0),(0,2),(2,0),(1,4),(4,1),(2,4),(4,2),(3,1),(1,3)`
  -- collapsing to the `i+2` enumeration).

/-- HOL `SET_EQ_DIAG_STAB_5M3` (HIJQAHA.hl:3192). -/
theorem SET_EQ_DIAG_STAB_5M3_p29 :
    scsArrowV39 {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5M3 i j = t}
      {scsStabDiagV39 scs5M3 0 2, scsStabDiagV39 scs5M3 0 3,
        scsStabDiagV39 scs5M3 2 4} := by
  sorry
  -- DISCHARGES: HL `SET_EQ` reorientation (`psort` symmetry) plus
  -- FZIOTEF over the three representative diag-stabs.

/-- HOL `SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4` (HIJQAHA.hl:3299). -/
theorem SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4_p29 :
    scsArrowV39 {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5M3 i j = t}
      {scs4M6', scs4M7, scs4M8, scs3T1, scs3T4} := by
  sorry
  -- DISCHARGES: HL FTRANS over `SET_EQ_DIAG_STAB_5M3`, the three
  -- composite slice arrows, and the prime bridges.

/-! ## Section E: the `scs_5M2` auxiliary bounds and the finale
(HIJQAHA.hl:3315-4145) -/

/-- HOL `h0_LT_B_SCS_5M2` (HIJQAHA.hl:3315). -/
theorem h0_LT_B_SCS_5M2_p29 :
    (∀ i j, scsDiag 5 i j → 4 * h0 < scs5M2.b i j) ∧
      (∀ i j, scsDiag 5 i j → scs5M2.a i j ≤ cstab) := by
  sorry
  -- DISCHARGES: HL funlist table evaluation on the five diagonal
  -- residue pairs (`FUNLIST_EXPLICIT`, `PSORT_5_EXPLICIT`, `4*h0 < 6`).

/-- HOL `B_LE_CSTAB_5M2` (HIJQAHA.hl:3328). -/
theorem B_LE_CSTAB_5M2_p29 :
    (∀ i, scs5M2.b i (i + 1) ≤ cstab) ∧ (∀ i, scs5M2.a i (i + 1) = 2) := by
  sorry
  -- DISCHARGES: HL funlist table evaluation on the edge residue pairs
  -- (`(0,1) -> cstab/2`, others default `2*h0`/`2`).

/-- HOL `B_LE_CSTAB_5M2_A_LT_B` (HIJQAHA.hl:3347). -/
theorem B_LE_CSTAB_5M2_A_LT_B_p29 : ∀ i : ℕ, 2 < scs5M2.b i (i + 1) := by
  sorry
  -- DISCHARGES: HL funlist table evaluation (`2 < cstab` and
  -- `2 < 2*h0` on the edge residue pairs).

/-- HOL `CARD_SCS_M_5M2` (HIJQAHA.hl:3369). -/
theorem CARD_SCS_M_5M2_p29 : (scsM scs5M2).ncard ≤ 1 := by
  sorry
  -- DISCHARGES: HL residue case work: only `i = 0` satisfies
  -- `2*h0 < scs_5M2.b i (i+1)`, so `scs_M` is a singleton
  -- (uses `SCS_M_5M2` or the direct finite-card bound).

/-- HOL `SCS_M_5M2` (HIJQAHA.hl:3395). -/
theorem SCS_M_5M2_p29 : scsM scs5M2 = {0} := by
  sorry
  -- DISCHARGES: HL funlist evaluation over the five residues:
  -- `2*h0 < cstab` only at `i = 0`, and `2 < 2` fails elsewhere.

/-- HOL `JCYFMRP_V2` (HIJQAHA.hl:3420). -/
theorem JCYFMRP_V2_p29 : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (v : ℕ → V3) (i : ℕ), 3 < s.k → isScsV39 s →
      v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
      dist (v i) (v (i + 1)) = 2 → (scsM s).ncard ≤ 1 →
      (∀ i j, scsDiag s.k i j →
        s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j) →
      (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
      ∃ i1, s.b i1 (i1 + 1) ≤ 2 * h0 ∧ s.a i1 (i1 + 1) = 2 ∧
        dist (v i1) (v (i1 + 1)) = 2 := by
  sorry
  -- DISCHARGES: HL `MP` on `JCYFMRP_concl`-class machinery with the
  -- fixed `i` edge hypothesis carried through the `scs_M` case split.

/-- HOL `JCYFMRP_V3` (HIJQAHA.hl:3487). -/
theorem JCYFMRP_V3_p29 : main_nonlinear_terminal_v11 →
    ∀ (s : ScsV39) (v : ℕ → V3), 3 < s.k → isScsV39 s →
      v ∈ MMsV39 s → scsGeneric v → scsBasicV39 s →
      (scsM s).ncard ≤ 1 →
      (∀ i j, scsDiag s.k i j →
        s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧ 4 * h0 < s.b i j) →
      (∀ i, s.a i (i + 1) < s.b i (i + 1)) →
      (∀ i, s.a i (i + 1) = 2) →
      ∃ i1, s.b i1 (i1 + 1) ≤ 2 * h0 ∧ s.a i1 (i1 + 1) = 2 ∧
        dist (v i1) (v (i1 + 1)) = 2 := by
  sorry
  -- DISCHARGES: HL `MP` on the JCYFMRP conclusion with the uniform
  -- `a(i,i+1) = 2` row.

/-- HOL `ARC_222` (HIJQAHA.hl:3512). -/
theorem ARC_222_p29 : arcLength 2 2 2 = Real.pi / 3 := by
  sorry
  -- DISCHARGES: HL `atn2`/`ups_x` evaluation: `arctan(sqrt 3)` branch
  -- of `arclength 2 2 2` with the exact `pi/3` identity.

/-- HOL `xrr_le_1553` (HIJQAHA.hl:3517). -/
theorem xrr_le_1553_p29 : ∀ v u w : V3, v ∈ ballAnnulus → u ∈ ballAnnulus →
    w ∈ ballAnnulus → ¬Collinear ℝ ({0, v, u} : Set V3) →
    dist v w = 2 → dist w u = 2 →
    xrr (norm v) (norm u) (norm (v - u)) ≤ 15.53 := by
  sorry
  -- DISCHARGES: HL geometric case analysis on the annulus radii with
  -- the `xrr` monotone envelope at the `2,2` dipole.

/-- HOL `xrr_le_1553_BB` (HIJQAHA.hl:3559). -/
theorem xrr_le_1553_BB_p29 (s : ScsV39) (v : ℕ → V3) (i : ℕ)
    (hbb : BBsV39 s v) : dist (v i) (v (i + 1)) = 2 →
    dist (v (i + 1)) (v (i + 2)) = 2 →
    ¬Collinear ℝ ({0, v i, v (i + 2)} : Set V3) →
    xrr (norm (v i)) (norm (v (i + 2))) (norm (v i - v (i + 2))) ≤ 15.53 := by
  sorry
  -- DISCHARGES: HL application of `xrr_le_1553` to `v i, v (i+2), v (i+1)`
  -- inside the `BBs` annulus.

/-- HOL `J_SCS_5M2_0` (HIJQAHA.hl:3574). -/
theorem J_SCS_5M2_0_p29 : ∀ (i j : ℕ), ¬scs5M2.J j i := by
  intro i j
  simp [scs5M2, mkUnadornedV39]

/-- HOL `SCS_5M2_IMP_SCS_5T1` (HIJQAHA.hl:3579). -/
theorem SCS_5M2_IMP_SCS_5T1_p29 : main_nonlinear_terminal_v11 →
    ∀ v : ℕ → V3, v ∈ MMsV39 scs5M2 →
      (∀ i j, scsDiag 5 i j → cstab < dist (v i) (v j)) →
      MMsV39 scs5T1 ≠ ∅ := by
  sorry
  -- DISCHARGES: HL terminal-nonlinear inequality machinery: the
  -- `scs_5M2` realisation with all diag distances `> cstab` realises
  -- `scs_5T1` with negative taustar.

/-- HOL `HIJ_STEP_1` (HIJQAHA.hl:3949). -/
theorem HIJ_STEP_1_p29 : main_nonlinear_terminal_v11 →
    scsArrowV39 {scs5M2}
      ({scs5T1} ∪
        {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5I2 i j = t} ∪
        {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5I3 i j = t} ∪
        {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5M3 i j = t}) := by
  sorry
  -- DISCHARGES: HL FTRANS assembling the edge case split on
  -- `dist(v 0, v 1)`: `≤ 2*h0` (5I2 stab), `≤ sqrt8` (5I3 stab),
  -- `> sqrt8` (5M3 stab), and the all-diag-`> cstab` case (5T1).

/-- HOL `HIJQAHA` (HIJQAHA.hl:4096): the file's title conclusion. -/
theorem HIJQAHA_p29 : main_nonlinear_terminal_v11 →
    scsArrowV39 {scs5M2}
      {scs5T1, scsStabDiagV39 scs5I2 0 2, scsStabDiagV39 scs5M1 0 2,
        scsStabDiagV39 scs5M1 0 3, scsStabDiagV39 scs5M1 2 4, scs4M6',
        scs4M7, scs4M8, scs3T1, scs3T4} := by
  sorry
  -- DISCHARGES: HL FTRANS over `HIJ_STEP_1`, `SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4`,
  -- and the earlier `scs_5M1` diag-stab registry (OXLZLEZ wave).

end Kepler.Text
