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
- No `native_decide`. Proved items: the mechanical registries
  (BASIC/K/J definitional folding, the `scsDiag` numeral checks,
  the `PSORT_5_EXPLICIT` table, the `scs_3T1_prime` equation, and
  `J_SCS_5M2_0`), plus 21 discharged sorries (see FILE MAP): the
  Section E `scs_5M2` table/`scs_M` registries, `ARC_222` (via
  PackingAuto18 `arclength2`), the Section A `BBs` edge/stab
  transfers (proved `STAB_BB`-pattern shim `stabBB_p29` + residue
  case work), the pure-table prime-to-plain `BBs` bridges, the
  `stab`-record set identities, and the two `PROP_OPP_DIAG_5M3`
  definitional twins. Remaining 47 sorries: no importable proved
  blocker exists — the `IS_SCS` giants, the `MMs`-witness steps
  (blocked by the still-`sorry` `XWNHLMD_MM` kit), the
  arrow/slice compositions and the `main_nonlinear_terminal_v11`
  consumers — each carries a NEEDS note naming its blocker.

FILE MAP
  Definitions (`scs5M3` reused from `Kepler.Text.LocalAuto20`):
    `scs3T4Prime_p29` (HOL `scs_3T4_prime`), `scs4M6Prime_p29`,
    `scs4M7Prime_p29`, `scs3T1Prime_p29` (HOL `scs_3T1_prime`,
    defined through the `scs_3T1_PRELIM_prime` tuple so that the
    `mk_unadorned_v39` equation `scs3T1Prime_eq_p29` is `rfl`),
    `scs4M8Prime_p29`.
  Section A (5M2 transfer kit): `SCS_5I1_STAB_DIAG_2h0_p29`
    (DISCHARGED), `MM_5M2_IMP_MM_STAB_5I2_p29` (sorry; NEEDS
    `XWNHLMD_MM`-class `MMs` transfer, still `sorry` in
    LocalAuto26), `SCS_5I1_STAB_DIAG_2h0_sqrt8_p29` (DISCHARGED),
    `SCS_5M2_EDGE_LE_2H0_p29` (DISCHARGED),
    `SCS_5M2_EDGE_LE_2H0_IMP_0_p29` (DISCHARGED),
    `MM_5M2_IMP_MM_STAB_5I3_p29` (sorry; NEEDS `XWNHLMD_MM`),
    `SCS_5I1_STAB_DIAG_sqrt8_p29` (DISCHARGED).
  Section B: `PSORT_5_EXPLICIT_p29` (proved).
  Section C: `SCS_*_IS_SCS_p29` x16 (sorry; NEEDS the 20-conjunct
    funlist/csAdj table verifications — no proved instance of any
    of the 16 targets exists in LocalAuto1-38/PackingAuto1-25),
    `SCS_*_BASIC_p29` x13 (proved), `K_SCS_*_p29` x13 (proved),
    `J_SCS_*_p29` x12 (proved).
  Section D: `STAB_5I1_SCS_p29` (sorry; NEEDS `isScsV39` of the
    stabbed tables), `STAB_5I2_SCS_p29` (sorry; same),
    `STAB_5M3_SCS_p29` (sorry; same), `STAB_5M3_SCS_v2_p29`
    (derived from `STAB_5M3_SCS_p29`, hence still `sorry`; the
    HOL duplicate binding),
    `SCS_5M3_STAB_DIAG_sqrt8_p29` (DISCHARGED),
    `SCS_DIAG_SCS_5M3_{02,03,24}_p29` (proved),
    `MM_5M2_IMP_MM_STAB_5M3_p29` (sorry; NEEDS `XWNHLMD_MM`), the
    BB bridges `BB_{3T4,4M6,3T1,4M7,4M8}_prime_IMP_*_p29`
    (DISCHARGED), the MM/arrow bridges
    `MM_*_IMP_MM_*_p29` x5, `SCS_*_ARROW_MM_*_p29` x5 (sorry;
    NEEDS `SCS_*_IS_SCS` + `MMs` witnesses),
    `SCS_5M3_SLICE_{02,03,24}_p29` (sorry; NEEDS the slice kit),
    `SCS_5M3_{02,03,24}_ARROW_*_p29` (sorry; NEEDS FTRANS over
    the slices),
    `PROP_OPP_DIAG_5M3_{03,02}_p29` (DISCHARGED),
    `SET_STAB_5M3_p29`, `EXPAND_STAB_DIAG_5M3_p29` (DISCHARGED),
    `SET_EQ_DIAG_STAB_5M3_p29`,
    `SET_EQ_DIAG_STAB_5M3_IMP_SCS_3_4_p29` (sorry; NEEDS
    `STAB_5M3_SCS` + `MMs` witnesses).
  Section E: `h0_LT_B_SCS_5M2_p29`, `B_LE_CSTAB_5M2_p29`,
    `B_LE_CSTAB_5M2_A_LT_B_p29`, `CARD_SCS_M_5M2_p29`,
    `SCS_M_5M2_p29` (DISCHARGED; the LocalAuto20 twin was itself
    still `sorry` at fill time, so discharged here directly),
    `JCYFMRP_V2_p29`, `JCYFMRP_V3_p29` (sorry; NEEDS the
    `JCYFMRP` conclusion machinery, `sorry` in LocalAuto1/27),
    `ARC_222_p29` (DISCHARGED via PackingAuto18 `arclength2`),
    `xrr_le_1553_p29`, `xrr_le_1553_BB_p29` (sorry; NEEDS the
    `xrr` monotone-envelope kit), `J_SCS_5M2_0_p29` (proved),
    `SCS_5M2_IMP_SCS_5T1_p29`, `HIJ_STEP_1_p29`, `HIJQAHA_p29`
    (sorry; NEEDS `main_nonlinear_terminal_v11` consumers).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto20
import Kepler.Text.PackingAuto18
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

/-! ## Section A0: proved table-arithmetic helpers (HIJQAHA `FUNLIST_EXPLICIT`
lane): the residue case work the HOL `SCS_TAC` bag performed -/

private theorem penta_p29 (n : ℕ) :
    n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
  omega

private theorem funlist_mod5_p29 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (i j : ℕ) :
    funlistV39 data d 5 i j = funlistV39 data d 5 (i % 5) (j % 5) := by
  unfold funlistV39
  rw [PSORT_MOD 5 i j (by norm_num), Nat.mod_mod i 5, Nat.mod_mod j 5]

private theorem psort_mod5_p29 (a b : ℕ) :
    psort 5 (a, b % 5) = psort 5 (a, b) := by
  simp only [psort, Nat.mod_mod]

private theorem funlist_edge5_p29 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (i : ℕ) :
    funlistV39 data d 5 i (i + 1) = funlistV39 data d 5 (i % 5) (i % 5 + 1) := by
  unfold funlistV39
  rw [(PSORT_MOD 5 i (i + 1) (by norm_num)).symm,
    show (i + 1) % 5 = (i % 5 + 1) % 5 from (Nat.mod_add_mod i 5 1).symm,
    Nat.mod_mod i 5, psort_mod5_p29]

/-- Edge value of the `scs_5M2` b-table: `cstab` at the `(0,1)` edge,
`2*h0` on the other four edges. -/
private theorem b_edge_5M2_p29 (i : ℕ) :
    scs5M2.b i (i + 1) = if i % 5 = 0 then cstab else 2 * h0 := by
  simp only [scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i (i + 1) = _
  rw [funlist_edge5_p29]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
    simp only [hi] <;>
    simp [funlistV39, psort, assocdV39]

/-- Edge value of the `scs_5M2` a-table: constantly `2`. -/
private theorem a_edge_5M2_p29 (i : ℕ) : scs5M2.a i (i + 1) = 2 := by
  simp only [scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
    ((1, 4), cstab), ((2, 4), cstab)] 2 5 i (i + 1) = 2
  rw [funlist_edge5_p29]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
    simp only [hi] <;>
    simp [funlistV39, psort, assocdV39]

/-- DISCHARGE SHIM for the Section A stab transfers: LocalAuto20 `STAB_BB`
with `isScsV39 s` weakened to `s.k ≠ 0` (its only use in that proof);
proof identical to the LocalAuto20 original. -/
private theorem stabBB_p29 (s : ScsV39) (v : ℕ → V3) (i j : ℕ) (hk : s.k ≠ 0)
    (hd : dist (v i) (v j) ≤ cstab) (hbb : BBsV39 s v) :
    BBsV39 (scsStabDiagV39 s i j) v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  refine ⟨h1, h2, fun i' j' => ?_, h4⟩
  have hle := h3 i' j'
  simp only [scsStabDiagV39, mkUnadornedV39]
  constructor
  · exact hle.1
  · split
    · next hpeq =>
        rw [DIST_PSORT v s.k i j i' j' h2 hk hpeq]
        exact hd
    · exact hle.2

/-! ## Section A1: `BBs` transfer through the system comparisons
(HL SCS_TAC table-comparison lane, discharged by residue case work) -/

private theorem v_eq_of_mod5_p29 {v : ℕ → V3} (hper : Periodic v 5) {i j : ℕ}
    (h : i % 5 = j % 5) : v i = v j := by
  rw [periodic_mod_p20 hper i, periodic_mod_p20 hper j, h]

private theorem dist_eq_zero_mod5_p29 {v : ℕ → V3} (hper : Periodic v 5) {i j : ℕ}
    (h : i % 5 = j % 5) : dist (v i) (v j) = 0 := by
  rw [v_eq_of_mod5_p29 hper h, dist_self]

private theorem dist_edge_fwd_p29 {v : ℕ → V3} (hper : Periodic v 5) {i j : ℕ}
    (h : j % 5 = (i + 1) % 5) : dist (v i) (v j) = dist (v i) (v (i + 1)) := by
  rw [periodic_mod_p20 hper j, periodic_mod_p20 hper (i + 1), h]

private theorem dist_edge_bwd_p29 {v : ℕ → V3} (hper : Periodic v 5) {i j : ℕ}
    (h : (j + 1) % 5 = i % 5) : dist (v i) (v j) = dist (v j) (v (j + 1)) := by
  rw [dist_comm, periodic_mod_p20 hper i, periodic_mod_p20 hper (j + 1), h]

private theorem dist_key01_p29 {v : ℕ → V3} (hper : Periodic v 5) {i j : ℕ}
    (h : psort 5 (i, j) = (0, 1)) : dist (v i) (v j) = dist (v 0) (v 1) := by
  have hk01 : psort 5 (0, 1) = psort 5 (i, j) := by rw [h]; simp [psort]
  exact DIST_PSORT v 5 0 1 i j hper (by norm_num) hk01

/-- The `scs_5M2` b-table is `6` on every diagonal pair. -/
private theorem b5M2_diag6_p29 (i j : ℕ) (h1 : i % 5 ≠ j % 5)
    (h2 : j % 5 ≠ (i + 1) % 5) (h3 : (j + 1) % 5 ≠ i % 5) :
    scs5M2.b i j = 6 := by
  simp only [scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j = 6
  have e1 : (i + 1) % 5 = (i % 5 + 1) % 5 := (Nat.mod_add_mod i 5 1).symm
  have e2 : (j + 1) % 5 = (j % 5 + 1) % 5 := (Nat.mod_add_mod j 5 1).symm
  simp only [e1, e2] at h2 h3 ⊢
  rw [funlist_mod5_p29 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) i j]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;> omega

/-- `scs_5I2.a ≤ scs_5M2.a` pointwise. -/
private theorem a5I2_le_a5M2_p29 (i j : ℕ) : scs5I2.a i j ≤ scs5M2.a i j := by
  simp only [scs5I2, mkUnadornedV39, scs5M2, mkUnadornedV39]
  show csAdj 5 2 (Real.sqrt 8) i j ≤ funlistV39 [((0, 1), 2), ((0, 2), cstab),
    ((0, 3), cstab), ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j
  unfold csAdj
  have e1 : (i + 1) % 5 = (i % 5 + 1) % 5 := (Nat.mod_add_mod i 5 1).symm
  have e2 : (j + 1) % 5 = (j % 5 + 1) % 5 := (Nat.mod_add_mod j 5 1).symm
  rw [e1, e2]
  rw [funlist_mod5_p29 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab),
    ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 i j]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [csAdj, funlistV39, psort, assocdV39] <;>
  first | omega | exact sqrt8_LE_CSTAB | norm_num [h0, cstab]

/-- `scs_5M3.a ≤ scs_5M2.a` off the `(0,1)` edge class (there the 5M3
lower bound `2*h0` beats `5M2`'s `2` and needs the edge hypothesis). -/
private theorem psort5_val_p29 (i j : ℕ) :
    psort 5 (i, j) =
      (if i % 5 ≤ j % 5 then (i % 5, j % 5) else (j % 5, i % 5)) := rfl

private theorem key01_ne_pair_p29 (i j : ℕ) (h : psort 5 (i, j) ≠ (0, 1)) :
    (i % 5 ≠ 0 ∨ j % 5 ≠ 1) ∧ (i % 5 ≠ 1 ∨ j % 5 ≠ 0) := by
  by_cases hle : i % 5 ≤ j % 5
  · have h1 : ¬(i % 5 = 0 ∧ j % 5 = 1) := by
      rintro ⟨hc1, hc2⟩
      exact h (by rw [psort5_val_p29, if_pos hle, hc1, hc2])
    have h2 : ¬(i % 5 = 1 ∧ j % 5 = 0) := by
      rintro ⟨hc1, hc2⟩
      exact absurd (show i % 5 ≤ j % 5 by omega) (by omega)
    refine ⟨?_, ?_⟩
    · by_cases hc1 : i % 5 = 0
      · right
        rintro hc2
        exact h1 ⟨hc1, hc2⟩
      · left
        exact hc1
    · by_cases hc2 : j % 5 = 0
      · left
        rintro hc1
        exact h2 ⟨hc1, hc2⟩
      · right
        exact hc2
  · have h1 : ¬(i % 5 = 0 ∧ j % 5 = 1) := by
      rintro ⟨hc1, hc2⟩
      exact absurd (show i % 5 ≤ j % 5 by omega) (by omega)
    have h2 : ¬(i % 5 = 1 ∧ j % 5 = 0) := by
      rintro ⟨hc1, hc2⟩
      exact h (by rw [psort5_val_p29, if_neg hle, hc2, hc1])
    refine ⟨?_, ?_⟩
    · by_cases hc1 : i % 5 = 0
      · right
        rintro hc2
        exact h1 ⟨hc1, hc2⟩
      · left
        exact hc1
    · by_cases hc2 : j % 5 = 0
      · left
        rintro hc1
        exact h2 ⟨hc1, hc2⟩
      · right
        exact hc2

private theorem psort_key01_ne_p29 (i j : ℕ) (hkey : psort 5 (i, j) = (0, 1)) :
    i % 5 ≠ j % 5 := by
  rintro cc
  have hval : psort 5 (i, j) = (i % 5, i % 5) := by
    rw [psort5_val_p29, ← cc]
    exact if_pos (le_refl _)
  rw [hval, Prod.mk.injEq] at hkey
  omega

private theorem a5M3_le_a5M2_off01_p29 (i j : ℕ)
    (hz1 : i % 5 ≠ 0 ∨ j % 5 ≠ 1) (hz2 : i % 5 ≠ 1 ∨ j % 5 ≠ 0) :
    scs5M3.a i j ≤ scs5M2.a i j := by
  simp only [scs5M3, mkUnadornedV39, scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
    ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j ≤
    funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
      ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j
  rw [funlist_mod5_p29 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
      ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 i j,
    funlist_mod5_p29 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
      ((1, 4), cstab), ((2, 4), cstab)] 2 i j]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

/-- The `scs_5I3.a` table is `2*h0 ≤ scs_5M2.a` off the `(0,1)` class. -/
private theorem a5I3_le_a5M2_off01_p29 (i j : ℕ)
    (hz1 : i % 5 ≠ 0 ∨ j % 5 ≠ 1) (hz2 : i % 5 ≠ 1 ∨ j % 5 ≠ 0) :
    scs5I3.a i j ≤ scs5M2.a i j := by
  simp only [scs5I3, mkUnadornedV39, scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
    ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i j ≤
    funlistV39 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
      ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j
  rw [funlist_mod5_p29 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
      ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 i j,
    funlist_mod5_p29 [((0, 1), 2), ((0, 2), cstab), ((0, 3), cstab), ((1, 3), cstab),
      ((1, 4), cstab), ((2, 4), cstab)] 2 i j]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

/-- The `scs_5M2.b` bound transfers to `scs_5I3.b` off the `(0,1)` class
(there `5I3` demands `≤ sqrt8` directly). -/
private theorem b5M2_le_b5I3_off01_p29 (i j : ℕ)
    (hz1 : i % 5 ≠ 0 ∨ j % 5 ≠ 1) (hz2 : i % 5 ≠ 1 ∨ j % 5 ≠ 0) :
    scs5M2.b i j ≤ scs5I3.b i j := by
  simp only [scs5M2, mkUnadornedV39, scs5I3, mkUnadornedV39]
  show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j ≤
    funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j
  rw [funlist_mod5_p29 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) i j,
    funlist_mod5_p29 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) i j]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

/-- `scs_5I2.b` values by pair class. -/
private theorem b5I2_val_p29 (i j : ℕ) :
    scs5I2.b i j =
      if i % 5 = j % 5 then 0
      else if j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5 then 2 * h0 else 6 := by
  simp only [scs5I2, mkUnadornedV39, csAdj]

/-- `BBs scs_5M2 vv → BBs scs_5I2 vv` given the `2*h0` edge bounds. -/
private theorem bbs_5I2_of_bbs_5M2_p29 (v : ℕ → V3) (hbb : BBsV39 scs5M2 v)
    (he : ∀ i, dist (v i) (v (i + 1)) ≤ 2 * h0) : BBsV39 scs5I2 v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  constructor
  · exact le_trans (a5I2_le_a5M2_p29 i j) hle1
  · rw [b5I2_val_p29]
    by_cases heq : i % 5 = j % 5
    · rw [if_pos heq, dist_eq_zero_mod5_p29 h2 heq]
    · by_cases hadj : j % 5 = (i + 1) % 5 ∨ (j + 1) % 5 = i % 5
      · rw [if_neg heq, if_pos hadj]
        rcases hadj with hadj | hadj
        · rw [dist_edge_fwd_p29 h2 hadj]; exact he i
        · rw [dist_edge_bwd_p29 h2 hadj]; exact he j
      · rw [b5M2_diag6_p29 i j heq
          (fun cc => hadj (Or.inl cc)) (fun cc => hadj (Or.inr cc))] at hle2
        rw [if_neg heq, if_neg hadj]
        exact hle2

/-- `scs_5I3.a` at the `(0,1)` class. -/
private theorem a5I3_key01_p29 (i j : ℕ) (hkey : psort 5 (i, j) = (0, 1)) :
    scs5I3.a i j = 2 * h0 := by
  simp only [scs5I3, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), 2 * h0), ((0, 3), 2 * h0),
    ((1, 3), 2 * h0), ((1, 4), 2 * h0), ((2, 4), 2 * h0)] 2 5 i j = 2 * h0
  unfold funlistV39
  have hne := psort_key01_ne_p29 i j hkey
  rw [if_neg hne, hkey]
  simp [assocdV39, List.map, psort]

/-- `scs_5I3.b` at the `(0,1)` class. -/
private theorem b5I3_key01_p29 (i j : ℕ) (hkey : psort 5 (i, j) = (0, 1)) :
    scs5I3.b i j = Real.sqrt 8 := by
  simp only [scs5I3, mkUnadornedV39]
  show funlistV39 [((0, 1), Real.sqrt 8), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j = Real.sqrt 8
  unfold funlistV39
  have hne := psort_key01_ne_p29 i j hkey
  rw [if_neg hne, hkey]
  simp [assocdV39, List.map, psort]

/-- `scs_5M3.a` at the `(0,1)` class. -/
private theorem a5M3_key01_p29 (i j : ℕ) (hkey : psort 5 (i, j) = (0, 1)) :
    scs5M3.a i j = 2 * h0 := by
  simp only [scs5M3, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
    ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 5 i j = 2 * h0
  unfold funlistV39
  have hne := psort_key01_ne_p29 i j hkey
  rw [if_neg hne, hkey]
  simp [assocdV39, List.map, psort]

/-- `BBs scs_5M2 vv → BBs scs_5I3 vv` given the edge window. -/
private theorem bbs_5I3_of_bbs_5M2_p29 (v : ℕ → V3) (hbb : BBsV39 scs5M2 v)
    (hlo : 2 * h0 ≤ dist (v 0) (v 1)) (hhi : dist (v 0) (v 1) ≤ Real.sqrt 8) :
    BBsV39 scs5I3 v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  by_cases hkey : psort 5 (i, j) = (0, 1)
  · have hde := dist_key01_p29 h2 hkey
    rw [a5I3_key01_p29 i j hkey, b5I3_key01_p29 i j hkey]
    exact ⟨by rw [hde]; exact hlo, by rw [hde]; exact hhi⟩
  · obtain ⟨hz1, hz2⟩ := key01_ne_pair_p29 i j hkey
    exact ⟨le_trans (a5I3_le_a5M2_off01_p29 i j hz1 hz2) hle1,
      le_trans hle2 (b5M2_le_b5I3_off01_p29 i j hz1 hz2)⟩

/-- The `scs_5M3` and `scs_5M2` b-tables coincide. -/
private theorem b5M3_eq_b5M2_p29 (i j : ℕ) : scs5M3.b i j = scs5M2.b i j := rfl

/-- `BBs scs_5M2 vv → BBs scs_5M3 vv` given the `(0,1)`-edge lower bound. -/
private theorem bbs_5M3_of_bbs_5M2_p29 (v : ℕ → V3) (hbb : BBsV39 scs5M2 v)
    (hlo : 2 * h0 ≤ dist (v 0) (v 1)) : BBsV39 scs5M3 v := by
  obtain ⟨h1, h2, h3, h4⟩ := hbb
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  by_cases hkey : psort 5 (i, j) = (0, 1)
  · have hde := dist_key01_p29 h2 hkey
    rw [a5M3_key01_p29 i j hkey, b5M3_eq_b5M2_p29]
    exact ⟨by rw [hde]; exact hlo, hle2⟩
  · obtain ⟨hz1, hz2⟩ := key01_ne_pair_p29 i j hkey
    rw [b5M3_eq_b5M2_p29]
    exact ⟨le_trans (a5M3_le_a5M2_off01_p29 i j hz1 hz2) hle1, hle2⟩

/-! ## Section A: the `scs_5M2` transfer kit (HIJQAHA.hl:97-495) -/

/-- HOL `SCS_5I1_STAB_DIAG_2h0` (HIJQAHA.hl:97). DISCHARGED: the SCS_TAC
table expansion `5M2 → 5I2` (`bbs_5I2_of_bbs_5M2_p29`: `5I2.a ≤ 5M2.a`
pointwise, `5I2.b` edges from the `2*h0` hypothesis, diagonals from
`5M2.b = 6`) followed by the stab transfer (`stabBB_p29`, the proved
LocalAuto20 `STAB_BB` step). -/
theorem SCS_5I1_STAB_DIAG_2h0_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    (∀ i, dist (v i) (v (i + 1)) ≤ 2 * h0) →
    BBsV39 (scsStabDiagV39 scs5I2 i j) v := by
  intro v i j hbb _hdij hdist hed
  have hk5 : scs5I2.k = 5 := rfl
  exact stabBB_p29 scs5I2 v i j (by rw [hk5]; norm_num) hdist
    (bbs_5I2_of_bbs_5M2_p29 v hbb hed)

/-- HOL `MM_5M2_IMP_MM_STAB_5I2` (HIJQAHA.hl:209). -/
theorem MM_5M2_IMP_MM_STAB_5I2_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    v ∈ MMsV39 scs5M2 → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    (∀ i, dist (v i) (v (i + 1)) ≤ 2 * h0) →
    MMsV39 (scsStabDiagV39 scs5I2 i j) ≠ ∅ := by
  sorry
  -- DISCHARGES: HL SCS_TAC + `MMs` nonemptyness from the transferred
  -- `BBs` witness via `SCS_5I1_STAB_DIAG_2h0` and `taustar` negativity.

/-- HOL `SCS_5I1_STAB_DIAG_2h0_sqrt8` (HIJQAHA.hl:229). DISCHARGED: the
SCS_TAC table expansion `5M2 → 5I3` (`bbs_5I3_of_bbs_5M2_p29`: the
`(0,1)`-edge class pinned by the `2*h0 ≤ d ≤ sqrt8` window, other edges
by the `2*h0` hypothesis, diagonals by `5M2`) plus the stab transfer. -/
theorem SCS_5I1_STAB_DIAG_2h0_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 ≤ dist (v 0) (v 1) → dist (v 0) (v 1) ≤ Real.sqrt 8 →
    BBsV39 (scsStabDiagV39 scs5I3 i j) v := by
  intro v i j hbb _hdij hdist hlo hhi
  have hk5 : scs5I3.k = 5 := rfl
  exact stabBB_p29 scs5I3 v i j (by rw [hk5]; norm_num) hdist
    (bbs_5I3_of_bbs_5M2_p29 v hbb hlo hhi)

/-- HOL `SCS_5M2_EDGE_LE_2H0` (HIJQAHA.hl:379). DISCHARGED: residue case
work on the `scs_5M2` edge b-values (`b_edge_5M2_p29`): off vertex 0 the
edge bound is `2*h0`, contradicting `2*h0 <`. -/
theorem SCS_5M2_EDGE_LE_2H0_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) → l % 5 ≠ 0 → False := by
  intro v i j l hbb _hd _hp hlt hne
  obtain ⟨-, -, hbnd, -⟩ := hbb
  have hle := hbnd l (l + 1)
  rw [b_edge_5M2_p29] at hle
  split_ifs at hle with hz
  · exact hne hz
  · exact absurd hlt (not_lt.2 hle.2)

/-- HOL `SCS_5M2_EDGE_LE_2H0_IMP_0` (HIJQAHA.hl:408). DISCHARGED: classical
contrapose of `SCS_5M2_EDGE_LE_2H0_p29` (the HL MESON step). -/
theorem SCS_5M2_EDGE_LE_2H0_IMP_0_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) → l % 5 = 0 := by
  intro v i j l hbb hd hp hlt
  by_cases h : l % 5 = 0
  · exact h
  · exact (SCS_5M2_EDGE_LE_2H0_p29 v i j l hbb hd hp hlt h).elim

/-- HOL `MM_5M2_IMP_MM_STAB_5I3` (HIJQAHA.hl:419). -/
theorem MM_5M2_IMP_MM_STAB_5I3_p29 : ∀ (v : ℕ → V3) (i j l : ℕ),
    v ∈ MMsV39 scs5M2 → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    2 * h0 < dist (v l) (v (l + 1)) →
    dist (v l) (v (l + 1)) ≤ Real.sqrt 8 →
    MMsV39 (scsStabDiagV39 scs5I3 i j) ≠ ∅ := by
  sorry
  -- DISCHARGES: HL SCS_TAC on the `scs_5I3` tables with the
  -- `(2*h0, sqrt8]` edge window; nonemptyness via `MMs` transfer.

/-- HOL `SCS_5I1_STAB_DIAG_sqrt8` (HIJQAHA.hl:452). DISCHARGED: the
stab-diag `BBs` transfer for a same-system stab — LocalAuto20's proved
`STAB_BB` step (importable, shape-matching modulo its `isScsV39 s`
hypothesis, whose only use is `s.k ≠ 0`; supplied here explicitly by the
`stabBB_p29` shim below). -/
theorem SCS_5I1_STAB_DIAG_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    Real.sqrt 8 ≤ dist (v 0) (v 1) →
    BBsV39 (scsStabDiagV39 scs5M2 i j) v := by
  intro v i j hbb _hdij hdist _hsqrt
  have hk5 : scs5M2.k = 5 := rfl
  exact stabBB_p29 scs5M2 v i j (by rw [hk5]; norm_num) hdist hbb

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

/-- HOL `SCS_5M3_STAB_DIAG_sqrt8` (HIJQAHA.hl:2231). DISCHARGED: the
SCS_TAC table expansion `5M2 → 5M3` (`bbs_5M3_of_bbs_5M2_p29`: identical
b-tables, `5M3.a` dominating `5M2.a` off the `(0,1)` class with the
`sqrt8 ≤ d(0,1)` hypothesis pinning that class) plus the stab transfer. -/
theorem SCS_5M3_STAB_DIAG_sqrt8_p29 : ∀ (v : ℕ → V3) (i j : ℕ),
    BBsV39 scs5M2 v → scsDiag 5 i j → dist (v i) (v j) ≤ cstab →
    Real.sqrt 8 ≤ dist (v 0) (v 1) →
    BBsV39 (scsStabDiagV39 scs5M3 i j) v := by
  intro v i j hbb _hdij hdist hlo
  have hk5 : scs5M3.k = 5 := rfl
  exact stabBB_p29 scs5M3 v i j (by rw [hk5]; norm_num) hdist
    (bbs_5M3_of_bbs_5M2_p29 v hbb (le_trans LE_sqrt8_2h0 hlo))

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

/-! ### Proved prime-to-plain `BBs` table comparisons (HL SCS_TAC lane) -/

private theorem penta3_p29 (n : ℕ) :
    n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  omega

private theorem penta4_p29 (n : ℕ) :
    n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  omega

private theorem funlist_mod3_p29 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (i j : ℕ) :
    funlistV39 data d 3 i j = funlistV39 data d 3 (i % 3) (j % 3) := by
  unfold funlistV39
  rw [PSORT_MOD 3 i j (by norm_num), Nat.mod_mod i 3, Nat.mod_mod j 3]

private theorem funlist_mod4_p29 (data : List ((ℕ × ℕ) × ℝ)) (d : ℝ) (i j : ℕ) :
    funlistV39 data d 4 i j = funlistV39 data d 4 (i % 4) (j % 4) := by
  unfold funlistV39
  rw [PSORT_MOD 4 i j (by norm_num), Nat.mod_mod i 4, Nat.mod_mod j 4]

/-- `scs_3T1.a ≤ scs_3T1_prime.a` pointwise. -/
private theorem a3T1_le_p29 (i j : ℕ) : scs3T1.a i j ≤ scs3T1Prime_p29.a i j := by
  simp only [scs_3T1, mkUnadornedV39, scs3T1Prime_p29, mkUnadornedV39]
  show funlistV39 [((0, 1), Real.sqrt 8)] 2 3 i j ≤
    funlistV39 [((0, 1), cstab)] 2 3 i j
  rw [funlist_mod3_p29 [((0, 1), Real.sqrt 8)] 2 i j,
    funlist_mod3_p29 [((0, 1), cstab)] 2 i j]
  rcases penta3_p29 i with hi | hi | hi <;>
  rcases penta3_p29 j with hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | exact sqrt8_LE_CSTAB

private theorem b3T1_eq_p29 (i j : ℕ) : scs3T1Prime_p29.b i j = scs3T1.b i j := rfl

/-- `scs_3T4.a ≤ scs_3T4_prime.a` pointwise. -/
private theorem a3T4_le_p29 (i j : ℕ) : scs3T4.a i j ≤ scs3T4Prime_p29.a i j := by
  simp only [scs3T4, mkUnadornedV39, scs3T4Prime_p29, mkUnadornedV39]
  show funlistV39 [((0, 1), 2)] (2 * h0) 3 i j ≤
    funlistV39 [((0, 1), 2), ((1, 2), cstab)] (2 * h0) 3 i j
  rw [funlist_mod3_p29 [((0, 1), 2)] (2 * h0) i j,
    funlist_mod3_p29 [((0, 1), 2), ((1, 2), cstab)] (2 * h0) i j]
  rcases penta3_p29 i with hi | hi | hi <;>
  rcases penta3_p29 j with hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

private theorem b3T4_eq_p29 (i j : ℕ) : scs3T4Prime_p29.b i j = scs3T4.b i j := rfl

/-- `scs_4M6'.a ≤ scs_4M6_prime.a` pointwise. -/
private theorem a4M6_le_p29 (i j : ℕ) : scs4M6'.a i j ≤ scs4M6Prime_p29.a i j := by
  simp only [scs4M6', mkUnadornedV39, scs4M6Prime_p29, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j ≤
    funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j
  rw [funlist_mod4_p29 [((0, 1), 2 * h0), ((0, 2), cstab), ((1, 3), cstab)] 2 i j,
    funlist_mod4_p29 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 i j]
  rcases penta4_p29 i with hi | hi | hi | hi <;>
  rcases penta4_p29 j with hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

private theorem b4M6_eq_p29 (i j : ℕ) : scs4M6Prime_p29.b i j = scs4M6'.b i j := rfl

/-- `scs_4M7.a ≤ scs_4M7_prime.a` pointwise. -/
private theorem a4M7_le_p29 (i j : ℕ) : scs4M7.a i j ≤ scs4M7Prime_p29.a i j := by
  simp only [scs4M7, mkUnadornedV39, scs4M7Prime_p29, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4 i j ≤
    funlistV39 [((0, 1), cstab), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4 i j
  rw [funlist_mod4_p29 [((0, 1), 2 * h0), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 i j,
    funlist_mod4_p29 [((0, 1), cstab), ((1, 2), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 i j]
  rcases penta4_p29 i with hi | hi | hi | hi <;>
  rcases penta4_p29 j with hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

private theorem b4M7_eq_p29 (i j : ℕ) : scs4M7Prime_p29.b i j = scs4M7.b i j := rfl

/-- `scs_4M8.a ≤ scs_4M8_prime.a` pointwise. -/
private theorem a4M8_le_p29 (i j : ℕ) : scs4M8.a i j ≤ scs4M8Prime_p29.a i j := by
  simp only [scs4M8, mkUnadornedV39, scs4M8Prime_p29, mkUnadornedV39]
  show funlistV39 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4 i j ≤
    funlistV39 [((0, 1), 2 * h0), ((2, 3), cstab), ((0, 2), cstab),
      ((1, 3), cstab)] 2 4 i j
  rw [funlist_mod4_p29 [((0, 1), 2 * h0), ((2, 3), 2 * h0), ((0, 2), cstab),
      ((1, 3), cstab)] 2 i j,
    funlist_mod4_p29 [((0, 1), 2 * h0), ((2, 3), cstab), ((0, 2), cstab),
      ((1, 3), cstab)] 2 i j]
  rcases penta4_p29 i with hi | hi | hi | hi <;>
  rcases penta4_p29 j with hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first | omega | norm_num [h0, cstab]

private theorem b4M8_eq_p29 (i j : ℕ) : scs4M8Prime_p29.b i j = scs4M8.b i j := rfl

/-- HOL `BB_3T4_prime_IMP_scs_3T4` (HIJQAHA.hl:2365). -/

theorem BB_3T4_prime_IMP_scs_3T4_p29 (v : ℕ → V3) (h : BBsV39 scs3T4Prime_p29 v) :
    BBsV39 scs3T4 v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  exact ⟨le_trans (a3T4_le_p29 i j) hle1, hle2.trans (le_of_eq (b3T4_eq_p29 i j))⟩
  -- DISCHARGED: table comparison (`a3T4_le_p29`; identical b-tables).

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
theorem BB_4M6_prime_IMP_scs_4M6_p29 (v : ℕ → V3) (h : BBsV39 scs4M6Prime_p29 v) :
    BBsV39 scs4M6' v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  exact ⟨le_trans (a4M6_le_p29 i j) hle1, hle2.trans (le_of_eq (b4M6_eq_p29 i j))⟩
  -- DISCHARGED: table comparison (`a4M6_le_p29`; identical b-tables).

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
theorem BB_3T1_prime_IMP_scs_3T1_p29 (v : ℕ → V3) (h : BBsV39 scs3T1Prime_p29 v) :
    BBsV39 scs3T1 v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  exact ⟨le_trans (a3T1_le_p29 i j) hle1, hle2.trans (le_of_eq (b3T1_eq_p29 i j))⟩
  -- DISCHARGED: table comparison (`a3T1_le_p29`, `b3T1_le_p29`).

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
theorem BB_4M7_prime_IMP_scs_4M7_p29 (v : ℕ → V3) (h : BBsV39 scs4M7Prime_p29 v) :
    BBsV39 scs4M7 v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  exact ⟨le_trans (a4M7_le_p29 i j) hle1, hle2.trans (le_of_eq (b4M7_eq_p29 i j))⟩
  -- DISCHARGED: table comparison (`a4M7_le_p29`; identical b-tables).

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
theorem BB_4M8_prime_IMP_scs_4M8_p29 (v : ℕ → V3) (h : BBsV39 scs4M8Prime_p29 v) :
    BBsV39 scs4M8 v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i j => ?_, h4⟩
  obtain ⟨hle1, hle2⟩ := h3 i j
  exact ⟨le_trans (a4M8_le_p29 i j) hle1, hle2.trans (le_of_eq (b4M8_eq_p29 i j))⟩
  -- DISCHARGED: table comparison (`a4M8_le_p29`; identical b-tables).

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
  simp only [scsStabDiagV39, scsPropEquV39, scsOppV39, mkUnadornedV39,
    ScsV39.mk.injEq]
  repeat' constructor
  all_goals
    funext i j
    simp only [scs5M3, mkUnadornedV39, peropp2, peropp]
    have e1 := Nat.add_mod 3 i 5
    have e2 := Nat.add_mod 3 j 5
    rw [e1, e2]
    try rw [psort5_val_p29]
    try rw [psort5_val_p29]
    try rw [funlist_mod5_p29 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
      ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 i j]
    try rw [funlist_mod5_p29 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) i j]
    rcases penta_p29 i with hi | hi | hi | hi | hi <;>
    rcases penta_p29 j with hj | hj | hj | hj | hj <;>
    simp only [hi, hj] <;>
    simp [funlistV39, psort, assocdV39] <;>
    omega
  -- DISCHARGED: HL definitional expansion of `scs_stab_diag_v39` /
  -- `scs_opp_v39` / `scs_prop_equ_v39` with the `psort` tables
  -- (`PSORT_5_EXPLICIT`, `PSORT_PERIODIC`), done as a 25-residue sweep.

/-- HOL `PROP_OPP_DIAG_5M3_02` (HIJQAHA.hl:3142). -/
theorem PROP_OPP_DIAG_5M3_02_p29 :
    scsStabDiagV39 scs5M3 0 2 =
      scsPropEquV39 (scsOppV39 (scsStabDiagV39 scs5M3 1 4)) 3 := by
  simp only [scsStabDiagV39, scsPropEquV39, scsOppV39, mkUnadornedV39,
    ScsV39.mk.injEq]
  repeat' constructor
  all_goals
    funext i j
    simp only [scs5M3, mkUnadornedV39, peropp2, peropp]
    have e1 := Nat.add_mod 3 i 5
    have e2 := Nat.add_mod 3 j 5
    rw [e1, e2]
    try rw [psort5_val_p29]
    try rw [psort5_val_p29]
    try rw [funlist_mod5_p29 [((0, 1), 2 * h0), ((0, 2), cstab), ((0, 3), cstab),
      ((1, 3), cstab), ((1, 4), cstab), ((2, 4), cstab)] 2 i j]
    try rw [funlist_mod5_p29 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
      ((1, 4), 6), ((2, 4), 6)] (2 * h0) i j]
    rcases penta_p29 i with hi | hi | hi | hi | hi <;>
    rcases penta_p29 j with hj | hj | hj | hj | hj <;>
    simp only [hi, hj] <;>
    simp [funlistV39, psort, assocdV39] <;>
    omega
  -- DISCHARGED: HL definitional expansion as for the 0-3 twin.

/-! ## Section D3: the `{stab_diag i j | diag 5 i j}` set expansions
(HIJQAHA.hl:3179-3313) -/

/-- DISCHARGE SHIM: the `stab_diag` record only sees its indices through
`psort 5`, hence is `i % 5, j % 5`-invariant (the `PSORT_PERIODIC`/`MOD`
sweep of the HOL `SET_STAB` lane). -/
private theorem stab_mod_p29 (i j : ℕ) :
    scsStabDiagV39 scs5M3 (i % 5) (j % 5) = scsStabDiagV39 scs5M3 i j := by
  refine scs_inj _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩ rfl rfl rfl ?_
  funext a b
  simp only [scsStabDiagV39, mkUnadornedV39]
  show (if psort 5 (i % 5, j % 5) = psort 5 (a, b) then cstab else scs5M3.b a b) =
    (if psort 5 (i, j) = psort 5 (a, b) then cstab else scs5M3.b a b)
  rw [PSORT_MOD 5 i j (by norm_num)]

private theorem stab_eq_of_key_p29 (i j i' j' : ℕ)
    (h : psort 5 (i, j) = psort 5 (i', j')) :
    scsStabDiagV39 scs5M3 i j = scsStabDiagV39 scs5M3 i' j' := by
  refine scs_inj _ _ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩ rfl rfl rfl ?_
  funext a b
  simp only [scsStabDiagV39, mkUnadornedV39]
  show (if psort 5 (i, j) = psort 5 (a, b) then cstab else scs5M3.b a b) =
    (if psort 5 (i', j') = psort 5 (a, b) then cstab else scs5M3.b a b)
  rw [h]

/-- The distance-2 diag keys of `Z/5`. -/
private theorem diag2_keys_p29 (i j : ℕ)
    (hrel : i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) :
    psort 5 (i % 5, j % 5) = (0, 2) ∨ psort 5 (i % 5, j % 5) = (1, 3) ∨
    psort 5 (i % 5, j % 5) = (2, 4) ∨ psort 5 (i % 5, j % 5) = (0, 3) ∨
    psort 5 (i % 5, j % 5) = (1, 4) := by
  rw [psort5_val_p29]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp at hrel ⊢ <;>
  omega

/-- HOL `SET_STAB_5M3` (HIJQAHA.hl:3179). DISCHARGED: `DIAG_MOD` plus the
`psort`-invariance of the stab record (`stab_mod_p29`). -/
theorem SET_STAB_5M3_p29 :
    {t | ∃ i j, scsDiag 5 i j ∧ scsStabDiagV39 scs5M3 i j = t} =
    {t | ∃ i j, scsDiag 5 (i % 5) (j % 5) ∧
      scsStabDiagV39 scs5M3 (i % 5) (j % 5) = t} := by
  ext t
  constructor
  · rintro ⟨i, j, hd, rfl⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by norm_num)).mpr hd, stab_mod_p29 i j⟩
  · rintro ⟨i, j, hd, heq⟩
    exact ⟨i, j, (DIAG_MOD 5 i j (by norm_num)).mp hd,
      (stab_mod_p29 i j).symm.trans heq⟩

/-- HOL `EXPAND_STAB_DIAG_5M3` (HIJQAHA.hl:3184). DISCHARGED: residue case
work listing the ten distance-2 pairs, collapsing to the five `(i + 2, i)`
representatives (`stab_eq_of_key_p29`). -/
theorem EXPAND_STAB_DIAG_5M3_p29 :
    {t | ∃ i j, (i % 5 = (j % 5 + 2) % 5 ∨ j % 5 = (i % 5 + 2) % 5) ∧
      scsStabDiagV39 scs5M3 (i % 5) (j % 5) = t} =
    {t | ∃ i, i < 5 ∧ scsStabDiagV39 scs5M3 (i + 2) i = t} := by
  ext t
  constructor
  · rintro ⟨i, j, hrel, heq⟩
    rcases diag2_keys_p29 i j hrel with hk | hk | hk | hk | hk
    · exact ⟨0, by norm_num, (stab_eq_of_key_p29 2 0 (i % 5) (j % 5)
        (by rw [hk]; simp [psort])).trans heq⟩
    · exact ⟨1, by norm_num, (stab_eq_of_key_p29 3 1 (i % 5) (j % 5)
        (by rw [hk]; simp [psort])).trans heq⟩
    · exact ⟨2, by norm_num, (stab_eq_of_key_p29 4 2 (i % 5) (j % 5)
        (by rw [hk]; simp [psort])).trans heq⟩
    · exact ⟨3, by norm_num, (stab_eq_of_key_p29 5 3 (i % 5) (j % 5)
        (by rw [hk]; simp [psort])).trans heq⟩
    · exact ⟨4, by norm_num, (stab_eq_of_key_p29 6 4 (i % 5) (j % 5)
        (by rw [hk]; simp [psort])).trans heq⟩
  · rintro ⟨i, hi5, heq⟩
    refine ⟨i + 2, i, Or.inl (Nat.mod_add_mod i 5 2).symm, ?_⟩
    rw [stab_mod_p29 (i + 2) i]
    exact heq

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

/-- HOL `h0_LT_B_SCS_5M2` (HIJQAHA.hl:3315). DISCHARGED: the a-bound is the
proved LocalAuto20 twin `h0_LT_B_SCS_5M2` (shape-matching, importable);
the b-bound is the funlist table evaluation on the five diagonal residue
pairs (`4*h0 < 6`), done by residue case work. -/
theorem h0_LT_B_SCS_5M2_p29 :
    (∀ i j, scsDiag 5 i j → 4 * h0 < scs5M2.b i j) ∧
      (∀ i j, scsDiag 5 i j → scs5M2.a i j ≤ cstab) := by
  refine ⟨fun i j hd => ?_, fun i j hd => h0_LT_B_SCS_5M2 i j hd⟩
  obtain ⟨h1, h2, h3⟩ := hd
  simp only [scs5M2, mkUnadornedV39]
  show funlistV39 [((0, 1), cstab), ((0, 2), 6), ((0, 3), 6), ((1, 3), 6),
    ((1, 4), 6), ((2, 4), 6)] (2 * h0) 5 i j > 4 * h0
  rw [funlist_mod5_p29]
  rcases penta_p29 i with hi | hi | hi | hi | hi <;>
  rcases penta_p29 j with hj | hj | hj | hj | hj <;>
  simp only [hi, hj] <;>
  simp [funlistV39, psort, assocdV39] <;>
  first
    | exact four_h0_lt_six_p20
    | omega

/-- HOL `B_LE_CSTAB_5M2` (HIJQAHA.hl:3328). DISCHARGED: edge residue case
work via `b_edge_5M2_p29` / `a_edge_5M2_p29` (`2*h0 ≤ cstab` is
LocalAuto20 `two_h0_le_cstab_p20`). -/
theorem B_LE_CSTAB_5M2_p29 :
    (∀ i, scs5M2.b i (i + 1) ≤ cstab) ∧ (∀ i, scs5M2.a i (i + 1) = 2) := by
  constructor
  · intro i
    rw [b_edge_5M2_p29]
    split_ifs with h5
    · exact le_rfl
    · exact two_h0_le_cstab_p20
  · intro i
    rw [a_edge_5M2_p29]

/-- HOL `B_LE_CSTAB_5M2_A_LT_B` (HIJQAHA.hl:3347). DISCHARGED: edge residue
case work (`2 < cstab`, `2 < 2*h0`). -/
theorem B_LE_CSTAB_5M2_A_LT_B_p29 : ∀ i : ℕ, 2 < scs5M2.b i (i + 1) := by
  intro i
  rw [b_edge_5M2_p29]
  split_ifs with h5
  · norm_num [cstab]
  · exact two_lt_two_h0_p20

/-- HOL `SCS_M_5M2` (HIJQAHA.hl:3395). DISCHARGED: funlist evaluation over
the five edge residues: `2*h0 < cstab` only at `i % 5 = 0` (and `2 < 2`
fails everywhere since `a(i,i+1) = 2`). The LocalAuto20 twin of this item
is itself `sorry`, so it is discharged here directly. -/
theorem SCS_M_5M2_p29 : scsM scs5M2 = {0} := by
  ext i
  simp only [scsM, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have hk : scs5M2.k = 5 := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hi5, hval⟩ := h
    rw [hk] at hi5
    rw [b_edge_5M2_p29, a_edge_5M2_p29] at hval
    rcases hval with hval | hval
    · split_ifs at hval with h5
      · rw [Nat.mod_eq_of_lt hi5] at h5
        exact h5
      · exact absurd hval (lt_irrefl (2 * h0))
    · exact absurd hval (by norm_num)
  · subst h
    refine ⟨by rw [hk]; norm_num, ?_⟩
    rw [b_edge_5M2_p29]
    refine Or.inl ?_
    norm_num [h0, cstab]

/-- HOL `CARD_SCS_M_5M2` (HIJQAHA.hl:3369). DISCHARGED: from the singleton
computation `SCS_M_5M2_p29`. -/
theorem CARD_SCS_M_5M2_p29 : (scsM scs5M2).ncard ≤ 1 := by
  rw [SCS_M_5M2_p29]
  simp

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

/-- HOL `ARC_222` (HIJQAHA.hl:3512). DISCHARGED: the `arclength2` route —
PackingAuto18's proved `arclength2` (importable, shape-matching) at `h = 1`
plus the `arccos (1/2) = pi/3` evaluation, exactly the `e4` step of the
PROVED `PackingAuto18.yssk_reduction` (small documented shim). -/
theorem ARC_222_p29 : arcLength 2 2 2 = Real.pi / 3 := by
  have h1 : arcLength 2 (2 * 1) 2 = Real.arccos (1 / 2) :=
    arclength2 (by norm_num) (by have hv : h0 = 1.26 := rfl; linarith)
  rw [show 2 * 1 = (2:ℝ) from by ring] at h1
  rw [h1, Real.arccos_eq_pi_div_two_sub_arcsin, ← Real.sin_pi_div_six,
    Real.arcsin_sin] <;> linarith [Real.pi_pos]

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
