/-
LocalAuto25 — Local Fan chapter appendix leftovers, two-file bundle
(skeleton-first pass):

  - `scripts/local/VASYYAU.hl` (2861 ln, 35 thms; H. L. Truong 2012) — the
    k = 4 quad-closing kit: the stratum-count bound `WGDHPPI`, the
    `arclength_lt_1553` numeric lemma, the mod-4 case kit
    (`NOT_MOD_4_CASES`/`_3`), `SCS_STR_CASES_4`, the `NEHXMWH`/
    `NEHXMWH1`/`TUAPYYU` registry chain, the `scs_M`-cases quartet
    (`SCS_M_CASES_4_LE_2`/`_EQ`/`_EQ1`, `B_LE_2h0(_2)_SCS_M_4*`),
    `WKZZEEH`, the a/b edge-value kit (`BASIC_IMP_NOT_J`,
    `CONDTION_A_LT_B`, `A_EQ2_IMP_B`, `A_EQ2h0_IMP_B`, `A_NOT_EQ2_IMP_B`,
    `B_LE_2h0_IMP_B`), the `scs_is_str` mod kit (`STR_MOD_EQ`,
    `IN_SCS_STR_CASES_4`, `FINITE_SET_STR`, `NOT_STR_IN_CASES_4`/`_1`),
    `PRO_ADD_NOT_IN_SCS_M`, `SCS_A_SYM`/`SCS_B_SYM`, `PWEIWBZ`,
    `h0_CSTAB_LT_4` and the master arrow `VASYYAU`.
  - `scripts/local/ZITHLQN.hl` (3202 ln, 26 thms; H. L. Truong 2012) — the
    `s_init_list` empty-J kit (`s_init_J_empty`, `dsv_scs_init`), the
    cyclic-enumeration lemmas (`exists_point_in_V`, `exists_vv_FF`,
    `exists_vv`, `exists_vv3`), the mod-3 bookkeeping kit (`SUC_MOD_*`,
    `IMP_SUC_MOD_EQ*`, `CHOOSE_MOD_3`), the `SMALL_BALL_ANNULUS_6*`
    trio, the `cs_adj` identity `CS_ADJ`, the eight scs-realisation
    verifications `ZITHLQN_CASE_3/4/5/6`, `ZITHLQN_CASE_5_pro_cs`,
    `ZITHLQN_CASE_4_3`, `ZITHLQN_CASE_5_sqrt8`, `ZITHLQN_CASE_4_pro_cs`,
    and the final registry arrow `ZITHLQN`
    (`0 <= taustar_v39` on `s_init_list` implies `JEJTVGB_assume_v39`).

FILE MAP
  Section 0 (`_p25` substrate; see ENCODING): `aPro_p25` (the HOL `a_pro`
    inlined in `sInitListV39` entries 7-8), `periodic2_mod_eq_p25` /
    `periodic2_suc_mod_eq_p25` (two-index `Periodic2` → mod bridges;
    twins of the same-wave LocalAuto26 `_p26` copies).
  Section A (ZITHLQN): `s_init_J_empty_p25` (proved), `dsv_scs_init_p25`
    (proved), `exists_point_in_V_p25` (proved), `exists_vv_FF_p25` (sorry),
    `exists_vv_p25` (sorry), the mod-3 kit `SUC_MOD_NOT_EQ_p25`,
    `SUC_MOD_EQ1_p25`, `SUC_MOD_EQ_p25`, `NOT_IMP_SUC_MOD_EQ_p25`,
    `IMP_SUC_MOD_EQ1_p25`, `IMP_SUC_MOD_EQ_p25`, `CHOOSE_MOD_3_p25` (all
    proved), `SMALL_BALL_ANNULUS_6_p25` / `_sqrt8` / `_3` (proved),
    `CS_ADJ_p25` (proved, definitional), `ZITHLQN_CASE_3_p25` (proved; the
    csAdj value-table exemplar), `ZITHLQN_CASE_4_p25`, `ZITHLQN_CASE_5_p25`,
    `ZITHLQN_CASE_6_p25`, `ZITHLQN_CASE_4_3_p25`, `ZITHLQN_CASE_5_sqrt8_p25`
    (all proved via the generic `bbsV39_csAdj_cycle_p25` value-table kit),
    `ZITHLQN_CASE_5_pro_cs_p25`, `ZITHLQN_CASE_4_pro_cs_p25` (proved via the
    `bbsV39_aPro_cycle_p25` kit), `exists_vv3_p25` (proved), `ZITHLQN_p25`
    (proved; re-export of the LocalAuto1 registry arrow `ZITHLQN_concl`).
  Section B (VASYYAU): `WGDHPPI_p25` (re-export of LocalAuto1
    `WGDHPPI_concl`), `DIST_V_IN_BB_LE_C_p25` (proved),
    `arclength_lt_1553_p25` (proved: atn2 case splits + tan double-angle +
    exact decimal norm_num), `YEBWJNG_p25` (re-export),
    `NOT_MOD_4_CASES_p25` / `_3` (proved), `SCS_STR_CASES_4_p25`
    (proved), the registry defs `NEHXMWH_concl_p25` / `NEHXMWH1_concl_p25`
    / `TUAPYYU_concl_p25` with `TUAPYYU1_p25`, `TUAPYYU_p25`,
    `TUAPYYU_IMP_CASES_p25`, the scsM quartet `SCS_M_CASES_4_LE_2_p25`
    (proved from the isScsV39 cardinality conjunct), `SCS_M_CASES_4_EQ_p25`,
    `B_LE_2h0_SCS_M_4_p25`, `B_LE_2h0_2_SCS_M_4_p25`,
    `B_LE_2h0_2_SCS_M_4_pair_p25` (the second HOL
    `B_LE_2h0_2_SCS_M_4`), `SCS_M_CASES_4_EQ1_p25`,
    `B_LE_2h0_2_SCS_M_4_1_p25` (all proved), `WKZZEEH_p25` (re-export),
    the edge-value kit `BASIC_IMP_NOT_J_p25`, `CONDTION_A_LT_B_p25`,
    `A_EQ2_IMP_B_p25`, `A_EQ2h0_IMP_B_p25`, `A_NOT_EQ2_IMP_B_p25`,
    `B_LE_2h0_IMP_B_p25` (proved), `STR_MOD_EQ_p25`,
    `IN_SCS_STR_CASES_4_p25`, `FINITE_SET_STR_p25`,
    `NOT_STR_IN_CASES_4_p25`, `NOT_STR_IN_CASES_4_1_p25`,
    `PRO_ADD_NOT_IN_SCS_M_p25`, `SCS_A_SYM_p25`, `SCS_B_SYM_p25`,
    `h0_CSTAB_LT_4_p25` (all proved), `PWEIWBZ_p25`, `VASYYAU_p25`
    (re-exports of the LocalAuto1 registry twins).
  HOL `check_completeness_claimA_concl` is commented out in both sources
  (VASYYAU.hl:2855, ZITHLQN.hl:3196) and is not ported.

ENCODING NOTES
  - Import discipline: LocalAuto1 (the scs record `ScsV39`, `isScsV39`
    whose 21st conjunct is exactly the `scs_M` cardinality bound,
    `BBsV39`, `MMsV39`, `scsM`, `scsIsStr`, `scsDiag`, `csAdj`,
    `mkUnadornedV39`, `sInitListV39`, `taustarV39`, `dsvV39`,
    `JEJTVGB_assume_v39`, `cstab`, and the `*_concl` registry twins) and
    LocalAuto23 (`periodic_mod_eq_p23`). Same-wave LocalAuto24/26 are NOT
    imported; the Periodic2 bridges are carried as `_p25` twins (NEEDS
    merge with LocalAuto26 `periodic2_mod_eq_p26`).
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `dist(v i, v j)` ↔ `dist (v i) (v j)`;
    `vec 0` ↔ `0`; `interior_angle1` ↔ `interiorAngle1`; the `scs_*_v39`
    accessors ↔ `ScsV39` projections; `IMAGE f (:num)` ↔ `Set.range f`;
    HOL `CARD` ↔ `Set.ncard`; `SUC n` ↔ `n + 1`; `MEM s l` ↔ `s ∈ l`.
  - `sqrt8` ↔ `Real.sqrt 8`; `#0.616`/`#0.467`/`#0.477` are exact decimal
    literals; `h0` = 1.26 (PackingAuto2), `cstab` = 3.01 (LocalAuto1).
  - The HOL `let upperbd = &6 in let a_pro = ... in mk_unadorned_v39 k d A B`
    scs displays are encoded by `mkUnadornedV39 k d (csAdj k .. ..)
    (csAdj k .. ..)` / `aPro_p25 k p a1 a2`, matching `sInitListV39`
    entries 1-8 term by term.
  - `main_nonlinear_terminal_v11` is the LocalAuto1 registry Prop.
  - DISCHARGES: every `sorry` carries a NEEDS note naming the blocking
    kit; proved items are mechanical (mod arithmetic, set bookkeeping,
    csAdj value tables, `norm_num` numerics).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto23
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p25` substrate -/

/-- HOL `a_pro` (appendix.hl:484): inlined in `sInitListV39` entries 7-8
(`ZITHLQN_CASE_5_pro_cs` / `ZITHLQN_CASE_4_pro_cs` displays). -/
noncomputable def aPro_p25 (k : ℕ) (p a1 a2 : ℝ) (i j : ℕ) : ℝ :=
  if i % k = j % k then 0
  else if ({i % k, j % k} : Set ℕ) = {0, 1} then p
  else if j % k = (i + 1) % k ∨ (j + 1) % k = i % k then a1 else a2

/-- Two-index periodicity collapses to mod indices. Verbatim twin of
LocalAuto26 `periodic2_mod_eq_p26`. NEEDS: merge. -/
theorem periodic2_mod_eq_p25 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
    (hp : Periodic2 f k) (i j : ℕ) : f (i % k) (j % k) = f i j := by
  have h1 : ∀ q i j, f (i + k * q) j = f i j := by
    intro q
    induction q with
    | zero => intro i j; simp
    | succ n ih =>
        intro i j
        rw [show i + k * (n + 1) = i + k * n + k by ring]
        exact (hp (i + k * n) j).1.trans (ih i j)
  have h2 : ∀ q i j, f i (j + k * q) = f i j := by
    intro q
    induction q with
    | zero => intro i j; simp
    | succ n ih =>
        intro i j
        rw [show j + k * (n + 1) = j + k * n + k by ring]
        exact (hp i (j + k * n)).2.trans (ih i j)
  have hi := Nat.mod_add_div i k
  have hj := Nat.mod_add_div j k
  calc f (i % k) (j % k)
    _ = f (i % k + k * (i / k)) (j % k) := (h1 (i / k) (i % k) (j % k)).symm
    _ = f (i % k + k * (i / k)) (j % k + k * (j / k)) :=
      (h2 (j / k) (i % k + k * (i / k)) (j % k)).symm
    _ = f i j := by rw [hi, hj]

/-- The step-(successor) two-index bridge. Twin of the LocalAuto26
`CHANGE_*_SCS_MOD` role. NEEDS: merge. -/
theorem periodic2_suc_mod_eq_p25 {α : Sort u} {f : ℕ → ℕ → α} {k : ℕ}
    (hp : Periodic2 f k) (i : ℕ) : f (i % k) ((i % k) + 1) = f i (i + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hlt : i % k < k := Nat.mod_lt i hk
    have e : ((i % k) + 1) % k = (i + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq i k)
    calc f (i % k) ((i % k) + 1)
      _ = f ((i % k) % k) (((i % k) + 1) % k) :=
        (periodic2_mod_eq_p25 hp (i % k) ((i % k) + 1)).symm
      _ = f i (i + 1) := by
          rw [Nat.mod_eq_of_lt hlt, e, periodic2_mod_eq_p25 hp i (i + 1)]

/-! ## Section A: ZITHLQN (Zithlqn.hl) -/

/-- HOL `s_init_J_empty` (ZITHLQN.hl:32): every initial system has the
empty arrow predicate. -/
theorem s_init_J_empty_p25 (s : ScsV39) (hs : s ∈ sInitListV39) :
    s.J = fun _ _ => False := by
  simp only [sInitListV39, List.mem_cons, List.not_mem_nil] at hs
  rcases hs with h | h | h | h | h | h | h | h | h
  <;> first | (rw [h]; rfl) | exact absurd h (by simp)

/-- HOL `dsv_scs_init` (ZITHLQN.hl:41). -/
theorem dsv_scs_init_p25 (s : ScsV39) (hs : s ∈ sInitListV39) (vv : ℕ → V3) :
    dsvV39 s vv = s.d :=
  dsv_J_empty s vv (s_init_J_empty_p25 s hs)

/-- HOL `exists_point_in_V` (ZITHLQN.hl:50). -/
theorem exists_point_in_V_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (h3 : ncard V ≥ 3) (_h6 : ncard V ≤ 6) : ∃ v : V3, v ∈ V := by
  by_contra hc
  push Not at hc
  have h0 : V = ∅ := Set.eq_empty_iff_forall_notMem.mpr hc
  rw [h0] at h3
  simp at h3

/-- HOL `SUC_MOD_NOT_EQ` (ZITHLQN.hl:483). -/
theorem SUC_MOD_NOT_EQ_p25 (i : ℕ) : ¬(i % 3 = (i + 1) % 3) := by omega

/-- HOL `SUC_MOD_EQ1` (ZITHLQN.hl:523). -/
theorem SUC_MOD_EQ1_p25 (i j : ℕ) (h : (i + 1) % 3 = (j + 1) % 3) (_hij : i ≤ j) :
    i % 3 = j % 3 := by omega

/-- HOL `SUC_MOD_EQ` (ZITHLQN.hl:620). -/
theorem SUC_MOD_EQ_p25 (i j : ℕ) (h : (i + 1) % 3 = (j + 1) % 3) :
    i % 3 = j % 3 := by omega

/-- HOL `NOT_IMP_SUC_MOD_EQ` (ZITHLQN.hl:639). -/
theorem NOT_IMP_SUC_MOD_EQ_p25 (i j : ℕ) (h : ¬(i % 3 = j % 3)) :
    ¬((i + 1) % 3 = (j + 1) % 3) := by omega

/-- HOL `IMP_SUC_MOD_EQ1` (ZITHLQN.hl:647); HOL `Nat.ModEq` bookkeeping
(the `i <= j` hypothesis is carried for fidelity, it is unused). -/
theorem IMP_SUC_MOD_EQ1_p25 (k i j : ℕ) (hk : k ≠ 0) (h : i % k = j % k) (_hij : i ≤ j) :
    (i + 1) % k = (j + 1) % k :=
  Nat.ModEq.add_right 1 h

/-- HOL `IMP_SUC_MOD_EQ` (ZITHLQN.hl:749). -/
theorem IMP_SUC_MOD_EQ_p25 (k i j : ℕ) (_hk : k ≠ 0) (h : i % k = j % k) :
    (i + 1) % k = (j + 1) % k :=
  Nat.ModEq.add_right 1 h

/-- HOL `CHOOSE_MOD_3` (ZITHLQN.hl:766). -/
theorem CHOOSE_MOD_3_p25 (i j : ℕ) (h1 : ¬(i % 3 = j % 3))
    (h2 : ¬((j + 1) % 3 = i % 3)) : j % 3 = (i + 1) % 3 := by omega

/-- HOL `CS_ADJ` (ZITHLQN.hl:918): definitional identity. -/
theorem CS_ADJ_p25 :
    csAdj = fun (k : ℕ) (a1 a2 : ℝ) (i j : ℕ) =>
      (if i % k = j % k then 0
       else if j % k = (i + 1) % k ∨ (j + 1) % k = i % k then a1 else a2) :=
  rfl

/-- Ball-annulus membership: the annulus bounds (PackingAuto2
`ballAnnulus = closedBall 0 (2*h0) \ ball 0 2`). -/
theorem ballAnnulus_norm_bounds_p25 {x : V3} (hx : x ∈ ballAnnulus) :
    2 ≤ dist x 0 ∧ dist x 0 ≤ 2 * h0 := by
  have h1 : x ∈ Metric.closedBall (0 : V3) (2 * h0) := hx.1
  have h2 : x ∉ Metric.ball (0 : V3) 2 := hx.2
  exact ⟨le_of_not_gt fun hh => h2 (Metric.mem_ball.mpr hh), Metric.mem_closedBall.mp h1⟩

/-! ### The SMALL_BALL_ANNULUS_6 trio -/

/-- HOL `SMALL_BALL_ANNULUS_6` (ZITHLQN.hl:814): the annulus supplies the
`dist <= &6` upper bound on top of the assumed lower bound. -/
theorem SMALL_BALL_ANNULUS_6_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (hlb : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (v w : V3) (hne : v ≠ w) (hv : v ∈ V) (hw : w ∈ V) (hE : {v, w} ∉ E) :
    2 * h0 ≤ dist v w ∧ dist v w ≤ 6 := by
  refine ⟨hlb v w hne hv hw hE, ?_⟩
  obtain ⟨d0, d0'⟩ := ballAnnulus_norm_bounds_p25 (hb hv)
  obtain ⟨e0, _⟩ := ballAnnulus_norm_bounds_p25 (hb hw)
  calc dist v w ≤ dist v 0 + dist 0 w := dist_triangle v 0 w
    _ = dist v 0 + dist w 0 := by rw [dist_comm 0 w]
    _ ≤ 2 * h0 + 2 * h0 := by linarith
    _ ≤ 6 := by norm_num [h0]

/-- HOL `SMALL_BALL_ANNULUS_6_sqrt8` (ZITHLQN.hl:850). -/
theorem SMALL_BALL_ANNULUS_6_sqrt8_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (hlb : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → Real.sqrt 8 ≤ dist v w)
    (v w : V3) (hne : v ≠ w) (hv : v ∈ V) (hw : w ∈ V) (hE : {v, w} ∉ E) :
    Real.sqrt 8 ≤ dist v w ∧ dist v w ≤ 6 := by
  refine ⟨hlb v w hne hv hw hE, ?_⟩
  obtain ⟨d0, d0'⟩ := ballAnnulus_norm_bounds_p25 (hb hv)
  obtain ⟨e0, _⟩ := ballAnnulus_norm_bounds_p25 (hb hw)
  calc dist v w ≤ dist v 0 + dist 0 w := dist_triangle v 0 w
    _ = dist v 0 + dist w 0 := by rw [dist_comm 0 w]
    _ ≤ 2 * h0 + 2 * h0 := by linarith
    _ ≤ 6 := by norm_num [h0]

/-- HOL `SMALL_BALL_ANNULUS_6_3` (ZITHLQN.hl:884). -/
theorem SMALL_BALL_ANNULUS_6_3_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (hlb : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 3 ≤ dist v w)
    (v w : V3) (hne : v ≠ w) (hv : v ∈ V) (hw : w ∈ V) (hE : {v, w} ∉ E) :
    3 ≤ dist v w ∧ dist v w ≤ 6 := by
  refine ⟨hlb v w hne hv hw hE, ?_⟩
  obtain ⟨d0, d0'⟩ := ballAnnulus_norm_bounds_p25 (hb hv)
  obtain ⟨e0, _⟩ := ballAnnulus_norm_bounds_p25 (hb hw)
  calc dist v w ≤ dist v 0 + dist 0 w := dist_triangle v 0 w
    _ = dist v 0 + dist w 0 := by rw [dist_comm 0 w]
    _ ≤ 2 * h0 + 2 * h0 := by linarith
    _ ≤ 6 := by norm_num [h0]

/-! ### Cyclic enumeration of a local fan -/

/-- HOL `exists_vv_FF` (ZITHLQN.hl:70): the `rho_node1`-cycle enumeration.
NEEDS: the Fan-chapter cycle kit (`ITER`, `DETER_RHO_NODE`,
`LOCAL_FAN_ITER_RHO_NODE_IN_V`, `POWER_TO_ITER`) — not yet ported. -/
theorem exists_vv_FF_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_h3 : 3 ≤ ncard V) (_h6 : ncard V ≤ 6) (v w : V3) (_hvw : (v, w) ∈ FF) :
    ∃ vv : ℕ → V3, vv 0 = v ∧ vv 1 = w ∧
      (∀ i, vv i = vv (i % ncard V)) ∧
      (∀ i j, vv i = vv j → i % ncard V = j % ncard V) ∧
      (Set.range vv : Set V3) = V ∧
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E ∧
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF := by
  sorry

/-- HOL `exists_vv` (ZITHLQN.hl:288). NEEDS: same cycle kit as
`exists_vv_FF_p25`. -/
theorem exists_vv_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_h3 : 3 ≤ ncard V) (_h6 : ncard V ≤ 6) :
    ∃ vv : ℕ → V3, (∀ i, vv i = vv (i % ncard V)) ∧
      (∀ i j, vv i = vv j → i % ncard V = j % ncard V) ∧
      (Set.range vv : Set V3) = V ∧
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E ∧
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF := by
  sorry

/-- HOL `exists_vv3` (ZITHLQN.hl:2325): the explicit triangle witness. -/
theorem exists_vv3_p25 (v1 v2 v3 : V3) (vv : ℕ → V3) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3))
    (hn1 : 2 ≤ norm v1) (hn2 : 2 ≤ norm v2) (hn3 : 2 ≤ norm v3)
    (hm1 : norm v1 ≤ 2 * h0) (hm2 : norm v2 ≤ 2 * h0) (hm3 : norm v3 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd13 : 2 ≤ dist v1 v3) (hd23 : 2 ≤ dist v2 v3)
    (he12 : dist v1 v2 ≤ 2 * h0) (he13 : dist v1 v3 ≤ 2 * h0) (he23 : dist v2 v3 ≤ 2 * h0)
    (hvv : ∀ i, vv i = if i % 3 = 0 then v1 else if i % 3 = 1 then v2 else v3)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    (∀ i, vv (i % ncard V) = vv i) ∧ V ⊆ ballAnnulus ∧ ncard V = 3 ∧
      ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0 := by
  have hd1 : v1 ≠ v2 := by intro h; rw [h] at hd12; norm_num at hd12
  have hd2 : v1 ≠ v3 := by intro h; rw [h] at hd13; norm_num at hd13
  have hd3 : v2 ≠ v3 := by intro h; rw [h] at hd23; norm_num at hd23
  have hmem : ∀ x : V3, x ∈ V ↔ (x = v1 ∨ x = v2 ∨ x = v3) := by
    intro x
    rw [← hV]
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
      rw [hvv i]
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
    · rintro (rfl | rfl | rfl)
      · exact Set.mem_range.mpr ⟨0, by simp [hvv 0]⟩
      · exact Set.mem_range.mpr ⟨1, by simp [hvv 1]⟩
      · exact Set.mem_range.mpr ⟨2, by simp [hvv 2]⟩
  have hVeq : V = insert v1 (insert v2 {v3}) := by
    ext x
    simp [hmem]
  have hmA : v1 ∉ insert v2 ({v3} : Set V3) := by
    intro hm
    rcases Set.mem_insert_iff.mp hm with h | h
    · exact hd1 h
    · exact hd2 (Set.mem_singleton_iff.mp h)
  have hmB : v2 ∉ ({v3} : Set V3) := fun hm => hd3 (Set.mem_singleton_iff.mp hm)
  have hcard : ncard V = 3 := by
    rw [hVeq, Set.ncard_insert_of_notMem hmA, Set.ncard_insert_of_notMem hmB,
      Set.ncard_singleton]
  have hIn : ∀ a : V3, 2 ≤ norm a → norm a ≤ 2 * h0 → a ∈ ballAnnulus := by
    intro a h2 h3
    have hd : dist a 0 = norm a := dist_zero_right a
    have hc : dist a 0 ≤ 2 * h0 := by rw [hd]; exact h3
    have hnb : ¬(dist a 0 < 2) := by rw [hd]; exact not_lt.mpr h2
    exact (⟨Metric.mem_closedBall.mpr hc, fun hb => hnb (Metric.mem_ball.mp hb)⟩ :
      a ∈ ballAnnulus)
  refine ⟨fun i => ?_, fun x hx => ?_, hcard, fun v w hvw => ?_⟩
  · rw [hcard, hvv (i % 3), hvv i]
    have he : (i % 3) % 3 = i % 3 := by omega
    rw [he]
  · rcases (hmem x).mp hx with h | h | h
    · rw [h]; exact hIn v1 hn1 hm1
    · rw [h]; exact hIn v2 hn2 hm2
    · rw [h]; exact hIn v3 hn3 hm3
  · rw [← hE] at hvw
    obtain ⟨i, hi⟩ := Set.mem_range.mp hvw
    have hvi : vv i ≠ vv (i + 1) := by
      intro hc2
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
      · have h1 : (i + 1) % 3 = 1 := by omega
        rw [hvv i, hvv (i + 1), h, h1] at hc2
        simpa using hd1 hc2
      · have h1 : (i + 1) % 3 = 2 := by omega
        rw [hvv i, hvv (i + 1), h, h1] at hc2
        simpa using hd3 hc2
      · have h1 : (i + 1) % 3 = 0 := by omega
        rw [hvv i, hvv (i + 1), h, h1] at hc2
        simpa using hd2 hc2.symm
    have hbound : 2 ≤ dist (vv i) (vv (i + 1)) ∧ dist (vv i) (vv (i + 1)) ≤ 2 * h0 := by
      rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
      · have h1 : (i + 1) % 3 = 1 := by omega
        rw [hvv i, hvv (i + 1)]
        simp only [h, h1]
        exact ⟨hd12, he12⟩
      · have h1 : (i + 1) % 3 = 2 := by omega
        rw [hvv i, hvv (i + 1)]
        simp only [h, h1]
        exact ⟨hd23, he23⟩
      · have h1 : (i + 1) % 3 = 0 := by omega
        rw [hvv i, hvv (i + 1)]
        simp only [h, h1]
        exact ⟨by rw [dist_comm]; exact hd13, by rw [dist_comm]; exact he13⟩
    have hvne : v ≠ w := by
      intro hc
      have k1 : vv i = v ∨ vv i = w := by
        have hm : vv i ∈ ({v, w} : Set V3) := by rw [← hi]; simp
        simpa using hm
      have k2 : vv (i + 1) = v ∨ vv (i + 1) = w := by
        have hm : vv (i + 1) ∈ ({v, w} : Set V3) := by rw [← hi]; simp
        simpa using hm
      rw [hc] at k1 k2
      rcases k1 with e1 | e1 <;> rcases k2 with e2 | e2 <;> exact hvi (e1.trans e2.symm)
    have m1 : v = vv i ∨ v = vv (i + 1) := by
      have hm : v ∈ ({vv i, vv (i + 1)} : Set V3) := by rw [hi]; simp
      simpa using hm
    have m2 : w = vv i ∨ w = vv (i + 1) := by
      have hm : w ∈ ({vv i, vv (i + 1)} : Set V3) := by rw [hi]; simp
      simpa using hm
    rcases m1 with h1 | h1 <;> rcases m2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hvne
    · rw [h1, h2]; exact hbound
    · rw [h1, h2]
      exact ⟨by rw [dist_comm]; exact hbound.1, by rw [dist_comm]; exact hbound.2⟩
    · exact absurd (h1.trans h2.symm) hvne
/-! ### The scs-realisation verifications -/

/-- HOL `ZITHLQN_CASE_3` (ZITHLQN.hl:929): the triangle `csAdj` system.
The value-table exemplar for the CASE_4/5/6 family (residue enumeration
over `i % 3, j % 3`). -/
theorem ZITHLQN_CASE_3_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (hb : V ⊆ ballAnnulus) (hc : ncard V = 3)
    (hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (hs : s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6))
    (hper : ∀ i, vv (i % ncard V) = vv i)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  subst hs
  simp only [BBsV39]
  have hper3 : ∀ i, vv (i % 3) = vv i := by
    intro i
    have h := hper i
    rwa [hc] at h
  refine ⟨fun x hx => ?_, fun i => ?_, fun i j => ?_, Or.inl (le_refl _)⟩
  · exact hb (by rw [← hV]; exact hx)
  · show vv (i + 3) = vv i
    have he : (i + 3) % 3 = i % 3 := by omega
    rw [← hper3 (i + 3), he, hper3]
  · have key : ∀ a b : ℕ, a % 3 = b % 3 → dist (vv a) (vv b) = 0 := by
      intro a b hab
      have hEq : vv a = vv b := by rw [← hper3 a, hab, ← hper3 b]
      rw [hEq, dist_self]
    have pairSwap : ∀ (x y : V3), ({x, y} : Set V3) = {y, x} := by
      intro x y
      ext z
      simp
      tauto
    have hstep : ∀ r r' : ℕ, r < 3 → r' < 3 → r ≠ r' →
        ∃ n : ℕ, ({vv n, vv (n + 1)} : Set V3) = {vv r, vv r'} := by
      intro r r' _hr _hr' _hne
      have hconv : ∀ m : ℕ, vv m = vv (m % 3) := fun m => (hper3 m).symm
      interval_cases r <;> interval_cases r' <;> (try omega)
      · exact ⟨0, by rw [hconv 0, hconv 1]⟩
      · exact ⟨2, by rw [hconv 2, hconv 3, pairSwap]⟩
      · exact ⟨0, by rw [hconv 0, hconv 1, pairSwap]⟩
      · exact ⟨1, by rw [hconv 1, hconv 2]⟩
      · exact ⟨2, by rw [hconv 2, hconv 3]⟩
      · exact ⟨1, by rw [hconv 1, hconv 2, pairSwap]⟩
    have hedge : ∀ i j : ℕ, i % 3 ≠ j % 3 → {vv i, vv j} ∈ E := by
      intro i j hij
      rw [← hE]
      obtain ⟨n, hn⟩ := hstep (i % 3) (j % 3) (by omega) (by omega) hij
      exact Set.mem_range.mpr ⟨n, by rw [hn, hper3 i, hper3 j]⟩
    rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hi | hi | hi <;>
      rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with hj | hj | hj
    · have he := key i j (by omega)
      simp only [mkUnadornedV39, csAdj, hi, hj, he]
      norm_num
    · have h1 : (i + 1) % 3 = 1 := by omega
      have h2 : (j + 1) % 3 = 2 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have h1 : (i + 1) % 3 = 1 := by omega
      have h2 : (j + 1) % 3 = 0 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have h1 : (i + 1) % 3 = 2 := by omega
      have h2 : (j + 1) % 3 = 1 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have he := key i j (by omega)
      simp only [mkUnadornedV39, csAdj, hi, hj, he]
      norm_num
    · have h1 : (i + 1) % 3 = 2 := by omega
      have h2 : (j + 1) % 3 = 0 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have h1 : (i + 1) % 3 = 0 := by omega
      have h2 : (j + 1) % 3 = 1 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have h1 : (i + 1) % 3 = 0 := by omega
      have h2 : (j + 1) % 3 = 2 := by omega
      simp only [mkUnadornedV39, csAdj, hi, hj, h1, h2]
      exact hd _ _ (hedge i j (by omega))
    · have he := key i j (by omega)
      simp only [mkUnadornedV39, csAdj, hi, hj, he]
      norm_num

/-! ### The csAdj cycle value-table kit -/

/-- Two-element sets commute (used for the unordered cycle-edge pairs). -/
theorem setPair_comm_p25 {α : Type u} (x y : α) : ({x, y} : Set α) = {y, x} := by
  ext z
  simp
  tauto

/-- Successor residues differ once `2 ≤ k`. -/
theorem succ_mod_ne_p25 {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : ¬(n % k = (n + 1) % k) := by
  have hr : n % k < k := Nat.mod_lt n (by omega)
  rcases Nat.lt_or_ge (n % k) (k - 1) with h | h
  · have h2 : n % k + 1 < k := by omega
    rw [← Nat.mod_add_mod n k 1, Nat.mod_eq_of_lt h2]
    omega
  · have h2 : n % k + 1 = k := by omega
    rw [← Nat.mod_add_mod n k 1, h2, Nat.mod_self]
    omega

/-- An adjacent-residue pair of a periodic cycle is a cycle edge. -/
theorem vvEdge_mem_p25 {k : ℕ} (hk : 0 < k) {vv : ℕ → V3} {E : Set (Set V3)}
    (hper : ∀ i, vv (i % k) = vv i)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    {i j : ℕ} (h : j % k = (i + 1) % k ∨ (j + 1) % k = i % k) :
    ({vv i, vv j} : Set V3) ∈ E := by
  rcases h with h | h
  · have h1 : (i % k + 1) % k = (i + 1) % k := Nat.mod_add_mod i k 1
    have hvj : vv j = vv (i % k + 1) := by
      rw [← hper j, h, ← h1, hper]
    rw [← hper i, hvj, ← hE]
    exact Set.mem_range.mpr ⟨i % k, rfl⟩
  · have h1 : (j % k + 1) % k = (j + 1) % k := Nat.mod_add_mod j k 1
    have hvi : vv i = vv (j % k + 1) := by
      rw [← hper i, ← h, ← h1, hper]
    rw [hvi, setPair_comm_p25, ← hper j, ← hE]
    exact Set.mem_range.mpr ⟨j % k, rfl⟩

/-- A non-adjacent, non-diagonal residue pair of a periodic cycle is not an
edge. -/
theorem vvEdge_notMem_p25 {k : ℕ} (hk : 2 ≤ k) {vv : ℕ → V3} {E : Set (Set V3)}
    (hper : ∀ i, vv (i % k) = vv i)
    (hinj : ∀ i j, vv i = vv j → i % k = j % k)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    {i j : ℕ} (hns : ¬(i % k = j % k))
    (hna : ¬(j % k = (i + 1) % k ∨ (j + 1) % k = i % k)) :
    ({vv i, vv j} : Set V3) ∉ E := by
  intro hm
  rw [← hE] at hm
  obtain ⟨n, hn⟩ := Set.mem_range.mp hm
  have hvne : vv i ≠ vv j := fun hcon => hns (hinj i j hcon)
  have m1 : vv n ∈ ({vv i, vv j} : Set V3) := by
    rw [← hn]; simp
  have m2 : vv (n + 1) ∈ ({vv i, vv j} : Set V3) := by
    rw [← hn]; simp
  rcases Set.mem_insert_iff.mp m1 with e1 | e1 <;>
    rcases Set.mem_insert_iff.mp m2 with e2 | e2
  · exact succ_mod_ne_p25 hk n (hinj n (n + 1) (e1.trans e2.symm))
  · exfalso
    apply hna
    have r1 : n % k = i % k := hinj n i e1
    have r2 : (n + 1) % k = j % k := hinj (n + 1) j e2
    have h1 : (n % k + 1) % k = (n + 1) % k := Nat.mod_add_mod n k 1
    have h2 : (i % k + 1) % k = (i + 1) % k := Nat.mod_add_mod i k 1
    rw [r1] at h1
    omega
  · exfalso
    apply hna
    refine Or.inr ?_
    have r1 : n % k = j % k := hinj n j e1
    have r2 : (n + 1) % k = i % k := hinj (n + 1) i e2
    have h1 : (n % k + 1) % k = (n + 1) % k := Nat.mod_add_mod n k 1
    have h2 : (j % k + 1) % k = (j + 1) % k := Nat.mod_add_mod j k 1
    rw [r1] at h1
    omega
  · exact succ_mod_ne_p25 hk n (hinj (n + 1) n (e2.trans e1.symm)).symm

/-- Any two points of a ball-annulus set are at distance at most `&6`
(the `upperbd` triangle bound). -/
theorem dist_le_6_of_ballAnnulus_p25 {V : Set V3} (hsub : V ⊆ ballAnnulus)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ V) : dist v w ≤ 6 := by
  obtain ⟨_, d1⟩ := ballAnnulus_norm_bounds_p25 (hsub hv)
  obtain ⟨_, d2⟩ := ballAnnulus_norm_bounds_p25 (hsub hw)
  calc dist v w ≤ dist v 0 + dist 0 w := dist_triangle v 0 w
    _ = dist v 0 + dist w 0 := by rw [dist_comm 0 w]
    _ ≤ 2 * h0 + 2 * h0 := by linarith
    _ ≤ 6 := by norm_num [h0]

/-- The generic csAdj cycle value table over an unadorned system with
`4 ≤ k ≤ 6`: same residues give `0/0`, adjacent residues are cycle edges
realising the `(2, 2*h0)` band, and everything else is a non-edge realising
the `(a2, b2)` band with `b2 = 6`. Method of `ZITHLQN_CASE_3_p25`. -/
theorem bbsV39_csAdj_cycle_p25 (k : ℕ) (d a2 b2 : ℝ) (s : ScsV39) (vv : ℕ → V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hs : s = mkUnadornedV39 k d (csAdj k 2 a2) (csAdj k (2 * h0) b2))
    (hk4 : 4 ≤ k) (_hk6 : k ≤ 6)
    (hper : ∀ i, vv (i % k) = vv i)
    (hinj : ∀ i j, vv i = vv j → i % k = j % k)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (hlf : ConvexLocalFan V E FF)
    (hsub : V ⊆ ballAnnulus)
    (hd : ∀ v w : V3, ({v, w} : Set V3) ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (hlow : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → ({v, w} : Set V3) ∉ E → a2 ≤ dist v w)
    (hb2 : b2 = 6) :
    BBsV39 s vv := by
  subst hs
  simp only [BBsV39, mkUnadornedV39]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hV]; exact hsub
  · intro i
    have he : (i + k) % k = i % k := Nat.add_mod_right i k
    rw [← hper (i + k), he, hper]
  · intro i j
    by_cases hsame : i % k = j % k
    · have hvE : vv i = vv j := by rw [← hper i, ← hper j, hsame]
      have av : csAdj k 2 a2 i j = 0 := by simp only [csAdj, hsame, ↓reduceIte]
      have bv : csAdj k (2 * h0) b2 i j = 0 := by simp only [csAdj, hsame, ↓reduceIte]
      rw [av, bv, hvE, dist_self]
      exact ⟨le_refl _, le_refl _⟩
    · by_cases hadj : (j % k = (i + 1) % k ∨ (j + 1) % k = i % k)
      · have hemem : ({vv i, vv j} : Set V3) ∈ E :=
          vvEdge_mem_p25 (by omega) hper hE hadj
        have hdb := hd (vv i) (vv j) hemem
        have av : csAdj k 2 a2 i j = 2 := by
          simp only [csAdj, hsame, ↓reduceIte]
          exact if_pos hadj
        have bv : csAdj k (2 * h0) b2 i j = 2 * h0 := by
          simp only [csAdj, hsame, ↓reduceIte]
          exact if_pos hadj
        rw [av, bv]; exact hdb
      · have hne' : vv i ≠ vv j := fun hcon => hsame (hinj i j hcon)
        have hmem : ({vv i, vv j} : Set V3) ∉ E :=
          vvEdge_notMem_p25 (by omega) hper hinj hE hsame hadj
        have hv : vv i ∈ V := by rw [← hV]; exact Set.mem_range.mpr ⟨i, rfl⟩
        have hw : vv j ∈ V := by rw [← hV]; exact Set.mem_range.mpr ⟨j, rfl⟩
        have hlo := hlow (vv i) (vv j) hne' hv hw hmem
        have hhi : dist (vv i) (vv j) ≤ 6 := dist_le_6_of_ballAnnulus_p25 hsub hv hw
        have av : csAdj k 2 a2 i j = a2 := by
          simp only [csAdj, hsame, ↓reduceIte]
          exact if_neg hadj
        have bv : csAdj k (2 * h0) b2 i j = b2 := by
          simp only [csAdj, hsame, ↓reduceIte]
          exact if_neg hadj
        rw [av, bv, hb2]
        exact ⟨hlo, hhi⟩
  · refine Or.inr ?_
    rw [hV, hE, hFF]
    exact hlf

/-- HOL `ZITHLQN_CASE_4` (ZITHLQN.hl:1029): the csAdj value table on the 16
residue pairs (method of `ZITHLQN_CASE_3_p25` via
`bbsV39_csAdj_cycle_p25`), with the diagonal band `2*h0 ≤ dist ≤ &6` from
`SMALL_BALL_ANNULUS_6_p25`'s triangle bound and the fan transfer into the
fourth `BBsV39` conjunct. -/
theorem ZITHLQN_CASE_4_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 4)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_hs : s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 4) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 4 = j % 4 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_csAdj_cycle_p25 4 (dTame 4) (2 * h0) 6 s vv V E FF _hs (by omega) (by omega)
    hper hinj _hV _hE _hFF _hlf _hb _hd _hne rfl

/-- HOL `ZITHLQN_CASE_5` (ZITHLQN.hl:1180): as CASE_4, over the 25 residue
pairs of the pentagon cycle. -/
theorem ZITHLQN_CASE_5_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 5)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_hs : s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 5) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 5 = j % 5 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_csAdj_cycle_p25 5 (dTame 5) (2 * h0) 6 s vv V E FF _hs (by omega) (by omega)
    hper hinj _hV _hE _hFF _hlf _hb _hd _hne rfl

/-- HOL `ZITHLQN_CASE_6` (ZITHLQN.hl:1329): as CASE_4, over the 36 residue
pairs of the hexagon cycle. -/
theorem ZITHLQN_CASE_6_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 6)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_hs : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 6) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 6 = j % 6 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_csAdj_cycle_p25 6 (dTame 6) (2 * h0) 6 s vv V E FF _hs (by omega) (by omega)
    hper hinj _hV _hE _hFF _hlf _hb _hd _hne rfl

/-- The generic `aPro` cycle value table (the `sInitListV39` entries 7-8
displays): same residues give `0/0`; the `{0, 1}` residue pair is the
exceptional `{vv 0, vv 1} = {v0, w0}` edge realising the
`(2*h0, sqrt8)` band; other adjacent residues are cycle edges realising
`(2, 2*h0)`; everything else is a non-edge realising `(a2, 6)`. -/
theorem bbsV39_aPro_cycle_p25 (k : ℕ) (d a2 : ℝ) (s : ScsV39) (vv : ℕ → V3)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hs : s = mkUnadornedV39 k d (aPro_p25 k (2 * h0) 2 a2)
      (aPro_p25 k (Real.sqrt 8) (2 * h0) 6))
    (hk4 : 4 ≤ k)
    (hper : ∀ i, vv (i % k) = vv i)
    (hinj : ∀ i j, vv i = vv j → i % k = j % k)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (hlf : ConvexLocalFan V E FF)
    (hsub : V ⊆ ballAnnulus)
    (hd : ∀ v w : V3, ({v, w} : Set V3) ∈ E →
      ({v, w} : Set V3) ≠ ({vv 0, vv 1} : Set V3) →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (hv0 : 2 * h0 ≤ dist (vv 0) (vv 1)) (hw0 : dist (vv 0) (vv 1) ≤ Real.sqrt 8)
    (hlow : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → ({v, w} : Set V3) ∉ E → a2 ≤ dist v w) :
    BBsV39 s vv := by
  subst hs
  simp only [BBsV39, mkUnadornedV39]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hV]; exact hsub
  · intro i
    have he : (i + k) % k = i % k := Nat.add_mod_right i k
    rw [← hper (i + k), he, hper]
  · intro i j
    by_cases hsame : i % k = j % k
    · have hvE : vv i = vv j := by rw [← hper i, ← hper j, hsame]
      have av : aPro_p25 k (2 * h0) 2 a2 i j = 0 := by
        simp only [aPro_p25, hsame, ↓reduceIte]
      have bv : aPro_p25 k (Real.sqrt 8) (2 * h0) 6 i j = 0 := by
        simp only [aPro_p25, hsame, ↓reduceIte]
      rw [av, bv, hvE, dist_self]
      exact ⟨le_refl _, le_refl _⟩
    · by_cases h01 : ({i % k, j % k} : Set ℕ) = {0, 1}
      · have m1 : i % k = 0 ∨ i % k = 1 := by
          have hm : i % k ∈ ({0, 1} : Set ℕ) := by rw [← h01]; simp
          simp at hm
          exact hm
        have m2 : j % k = 0 ∨ j % k = 1 := by
          have hm : j % k ∈ ({0, 1} : Set ℕ) := by rw [← h01]; simp
          simp at hm
          exact hm
        have h0k : (0 : ℕ) % k = 0 := Nat.zero_mod k
        have h1k : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
        rcases m1 with hi0 | hi1
        · rcases m2 with hj0 | hj1
          · exact absurd (hi0.trans hj0.symm) hsame
          · have hvi : vv i = vv 0 := by rw [← hper i, hi0]
            have hvj : vv j = vv 1 := by rw [← hper j, hj1]
            have av : aPro_p25 k (2 * h0) 2 a2 i j = 2 * h0 := by
              simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            have bv : aPro_p25 k (Real.sqrt 8) (2 * h0) 6 i j = Real.sqrt 8 := by
              simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            rw [av, bv, hvi, hvj]
            exact ⟨hv0, hw0⟩
        · rcases m2 with hj0 | hj1
          · have hvi : vv i = vv 1 := by rw [← hper i, hi1]
            have hvj : vv j = vv 0 := by rw [← hper j, hj0]
            have av : aPro_p25 k (2 * h0) 2 a2 i j = 2 * h0 := by
              simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            have bv : aPro_p25 k (Real.sqrt 8) (2 * h0) 6 i j = Real.sqrt 8 := by
              simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            rw [av, bv, hvi, hvj, dist_comm]
            exact ⟨hv0, hw0⟩
          · exact absurd (hi1.trans hj1.symm) hsame
      · by_cases hadj : (j % k = (i + 1) % k ∨ (j + 1) % k = i % k)
        · have hemem : ({vv i, vv j} : Set V3) ∈ E :=
            vvEdge_mem_p25 (by omega) hper hE hadj
          have hne0 : ({vv i, vv j} : Set V3) ≠ ({vv 0, vv 1} : Set V3) := by
            intro hc
            apply h01
            have q1 : vv i = vv 0 ∨ vv i = vv 1 := by
              have hq : vv i ∈ ({vv 0, vv 1} : Set V3) := by rw [← hc]; simp
              simp at hq
              exact hq
            have q2 : vv j = vv 0 ∨ vv j = vv 1 := by
              have hq : vv j ∈ ({vv 0, vv 1} : Set V3) := by rw [← hc]; simp
              simp at hq
              exact hq
            have h0k : (0 : ℕ) % k = 0 := Nat.zero_mod k
            have h1k : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
            rcases q1 with r1 | r1 <;> rcases q2 with r2 | r2
            · exact absurd (hinj i j (r1.trans r2.symm)) hsame
            · have i0 : i % k = 0 := by rw [hinj i 0 r1]; exact h0k
              have j1 : j % k = 1 := by rw [hinj j 1 r2]; exact h1k
              rw [i0, j1]
            · have i1 : i % k = 1 := by rw [hinj i 1 r1]; exact h1k
              have j0 : j % k = 0 := by rw [hinj j 0 r2]; exact h0k
              rw [i1, j0, setPair_comm_p25]
            · exact absurd (hinj i j (r1.trans r2.symm)) hsame
          have hdb := hd (vv i) (vv j) hemem hne0
          have av : aPro_p25 k (2 * h0) 2 a2 i j = 2 := by
            simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            rcases hadj with h | h
            · exact if_pos (Or.inl h)
            · exact if_pos (Or.inr h)
          have bv : aPro_p25 k (Real.sqrt 8) (2 * h0) 6 i j = 2 * h0 := by
            simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            rcases hadj with h | h
            · exact if_pos (Or.inl h)
            · exact if_pos (Or.inr h)
          rw [av, bv]; exact hdb
        · have hne' : vv i ≠ vv j := fun hcon => hsame (hinj i j hcon)
          have hmem : ({vv i, vv j} : Set V3) ∉ E :=
            vvEdge_notMem_p25 (by omega) hper hinj hE hsame hadj
          have hv : vv i ∈ V := by rw [← hV]; exact Set.mem_range.mpr ⟨i, rfl⟩
          have hw : vv j ∈ V := by rw [← hV]; exact Set.mem_range.mpr ⟨j, rfl⟩
          have hlo := hlow (vv i) (vv j) hne' hv hw hmem
          have hhi : dist (vv i) (vv j) ≤ 6 := dist_le_6_of_ballAnnulus_p25 hsub hv hw
          have av : aPro_p25 k (2 * h0) 2 a2 i j = a2 := by
            simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            exact if_neg hadj
          have bv : aPro_p25 k (Real.sqrt 8) (2 * h0) 6 i j = 6 := by
            simp only [aPro_p25, hsame, ↓reduceIte, h01, ↓reduceIte]
            exact if_neg hadj
          rw [av, bv]
          exact ⟨hlo, hhi⟩
  · refine Or.inr ?_
    rw [hV, hE, hFF]
    exact hlf

/-- HOL `ZITHLQN_CASE_5_pro_cs` (ZITHLQN.hl:1478): the `a_pro` pentagon
(sInitListV39 entry 7). aPro value table over the 25 residue pairs via
`bbsV39_aPro_cycle_p25`: the `{0, 1}` residue pair is the `{v0, w0}` edge
(`2*h0 ≤ dist ≤ sqrt8`), other adjacent pairs are edges, distance-2 pairs
are non-edges, plus the fan transfer. -/
theorem ZITHLQN_CASE_5_pro_cs_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39) (v0 w0 : V3)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 5)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_he : ({v0, w0} : Set V3) ∈ E)
    (_hv0 : 2 * h0 ≤ dist v0 w0) (_hw0 : dist v0 w0 ≤ Real.sqrt 8)
    (_hs : s = mkUnadornedV39 5 0.616 (aPro_p25 5 (2 * h0) 2 (2 * h0))
      (aPro_p25 5 (Real.sqrt 8) (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (_hvv0 : vv 0 = v0) (_hvv1 : vv 1 = w0) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 5) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 5 = j % 5 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_aPro_cycle_p25 5 0.616 (2 * h0) s vv V E FF _hs (by omega)
    hper hinj _hV _hE _hFF _hlf _hb
    (fun v w hvw hne => _hd v w hvw (by rw [← _hvv0, ← _hvv1]; exact hne))
    (by rw [_hvv0, _hvv1]; exact _hv0) (by rw [_hvv0, _hvv1]; exact _hw0)
    _hne

/-- HOL `ZITHLQN_CASE_4_3` (ZITHLQN.hl:1750): the `&3` diagonal quad
(sInitListV39 entry 6). csAdj value table with diagonal band `&3 ≤ dist ≤
&6` (lower bound from the `&3` non-edge hypothesis, upper bound from the
annulus triangle bound). -/
theorem ZITHLQN_CASE_4_3_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 4)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 3 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_hs : s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 4) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 4 = j % 4 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_csAdj_cycle_p25 4 0.467 3 6 s vv V E FF _hs (by omega) (by omega)
    hper hinj _hV _hE _hFF _hlf _hb _hd _hne rfl

/-- HOL `ZITHLQN_CASE_5_sqrt8` (ZITHLQN.hl:1901): the `sqrt8` diagonal
pentagon (sInitListV39 entry 5). csAdj value table with diagonal band
`sqrt8 ≤ dist ≤ &6`. -/
theorem ZITHLQN_CASE_5_sqrt8_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 5)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → Real.sqrt 8 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_hs : s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 5) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 5 = j % 5 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_csAdj_cycle_p25 5 0.616 (Real.sqrt 8) 6 s vv V E FF _hs (by omega) (by omega)
    hper hinj _hV _hE _hFF _hlf _hb _hd _hne rfl

/-- HOL `ZITHLQN_CASE_4_pro_cs` (ZITHLQN.hl:2057): the `a_pro` quad
(sInitListV39 entry 8). aPro value table over the 16 residue pairs via
`bbsV39_aPro_cycle_p25`: the `{0, 1}` residue pair is the `{v0, w0}` edge
(`2*h0 ≤ dist ≤ sqrt8`), other adjacent pairs are edges, diagonals are
non-edges (`sqrt8 ≤ dist ≤ &6`), plus the fan transfer. -/
theorem ZITHLQN_CASE_4_pro_cs_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39) (v0 w0 : V3)
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_hc : ncard V = 4)
    (_hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → Real.sqrt 8 ≤ dist v w)
    (_hd : ∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (_he : ({v0, w0} : Set V3) ∈ E)
    (_hv0 : 2 * h0 ≤ dist v0 w0) (_hw0 : dist v0 w0 ≤ Real.sqrt 8)
    (_hs : s = mkUnadornedV39 4 0.477 (aPro_p25 4 (2 * h0) 2 (Real.sqrt 8))
      (aPro_p25 4 (Real.sqrt 8) (2 * h0) 6))
    (_hper : ∀ i, vv (i % ncard V) = vv i)
    (_hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (_hV : (Set.range vv : Set V3) = V)
    (_hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (_hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (_hvv0 : vv 0 = v0) (_hvv1 : vv 1 = w0) :
    BBsV39 s vv := by
  have hper : ∀ i, vv (i % 4) = vv i := by
    intro i
    have h := _hper i
    rwa [_hc] at h
  have hinj : ∀ i j, vv i = vv j → i % 4 = j % 4 := by
    intro i j hij
    have h := _hinj i j hij
    rwa [_hc] at h
  exact bbsV39_aPro_cycle_p25 4 0.477 (Real.sqrt 8) s vv V E FF _hs (by omega)
    hper hinj _hV _hE _hFF _hlf _hb
    (fun v w hvw hne => _hd v w hvw (by rw [← _hvv0, ← _hvv1]; exact hne))
    (by rw [_hvv0, _hvv1]; exact _hv0) (by rw [_hvv0, _hvv1]; exact _hw0)
    _hne

/-- HOL `ZITHLQN` (ZITHLQN.hl:2465): the final registry arrow; the
LocalAuto1 twin `ZITHLQN_concl` has the identical statement. -/
theorem ZITHLQN_p25 (h : ∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv →
    0 ≤ taustarV39 s vv) : JEJTVGB_assume_v39 := ZITHLQN_concl h

/-! ## Section B: VASYYAU (Vasyyau.hl) -/

/-- HOL `WGDHPPI` (VASYYAU.hl:100): at most one straight (str) index.
Re-export of the LocalAuto1 registry twin `WGDHPPI_concl`. -/
theorem WGDHPPI_p25 (s : ScsV39) (v : ℕ → V3) (his : isScsV39 s) (hk : s.k = 4)
    (hv : v ∈ MMsV39 s) : {i | i < s.k ∧ scsIsStr s v i}.ncard ≤ 1 :=
  WGDHPPI_concl s v his hk hv

/-- HOL `DIST_V_IN_BB_LE_C` (VASYYAU.hl:111). -/
theorem DIST_V_IN_BB_LE_C_p25 (s : ScsV39) (v : ℕ → V3) (i : ℕ) (c : ℝ)
    (hc : s.b i (i + 1) ≤ c) (hb : BBsV39 s v) : dist (v i) (v (i + 1)) ≤ c :=
  (hb.2.2.1 i (i + 1)).2.trans hc

/-- HOL `arclength_lt_1553` (VASYYAU.hl:121): both arcLength displays are
unfolded to their `atn2` case splits; the comparison `arctan (n2/7.53) <
2 * arctan (1.6496/n1)` reduces via `Real.arctan_tan` to the tangent
double-angle identity `tan (2 arctan u) = 2u/(1-u²)`, with the final
numeric band proved by exact decimal `norm_num` arithmetic on
`(1.6496/√(6.3504·9.6496))` vs `√(15.53·0.47)/7.53`. -/
theorem arclength_lt_1553_p25 :
    2 * arcLength 2 2 (2 * h0) < arcLength 2 2 (Real.sqrt 15.53) := by
  have hh0 : h0 = 1.26 := rfl
  simp only [arcLength]
  obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = (2 * h0) * (2 * h0) := ⟨_, rfl⟩
  rw [← hxd]
  obtain ⟨n1, hn1d⟩ : ∃ n1 : ℝ, n1 = Real.sqrt (upsX (2 * 2) (2 * 2) x) := ⟨_, rfl⟩
  rw [← hn1d]
  obtain ⟨y2, hy2d⟩ : ∃ y2 : ℝ, y2 = Real.sqrt 15.53 * Real.sqrt 15.53 := ⟨_, rfl⟩
  rw [← hy2d]
  obtain ⟨n2, hn2d⟩ : ∃ n2 : ℝ, n2 = Real.sqrt (upsX (2 * 2) (2 * 2) y2) := ⟨_, rfl⟩
  rw [← hn2d]
  have hx : x = 6.3504 := by rw [hxd, hh0]; norm_num
  have hup1 : upsX (2 * 2) (2 * 2) x = 6.3504 * 9.6496 := by
    rw [hx]; simp only [upsX]; norm_num
  have hy1 : x - 2 * 2 - 2 * 2 = -(1.6496 : ℝ) := by rw [hx]; norm_num
  have hnpos : 0 < n1 := by rw [hn1d, hup1]; exact Real.sqrt_pos.mpr (by norm_num)
  have habs1 : |x - 2 * 2 - 2 * 2| < n1 := by
    rw [hy1, abs_of_neg (by norm_num : (-(1.6496 : ℝ)) < 0), hn1d, hup1]
    refine Real.lt_sqrt_of_sq_lt ?_
    norm_num
  have hneg1 : (-(1.6496 : ℝ)) / n1 = -((1.6496 : ℝ) / n1) := by ring
  have hatn1 : atn2 n1 (x - 2 * 2 - 2 * 2) = -Real.arctan (1.6496 / n1) := by
    rw [atn2, if_pos habs1, hy1, hneg1, Real.arctan_neg]
  have hy2sq : y2 = 15.53 := by
    rw [hy2d, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 15.53)]
  have hy2 : y2 - 2 * 2 - 2 * 2 = 7.53 := by rw [hy2sq]; norm_num
  have hy2pos : 0 < y2 - 2 * 2 - 2 * 2 := by rw [hy2]; norm_num
  have hup2 : upsX (2 * 2) (2 * 2) y2 = 15.53 * 0.47 := by
    rw [hy2sq]; simp only [upsX]; norm_num
  have hn2pos : 0 < n2 := by rw [hn2d, hup2]; exact Real.sqrt_pos.mpr (by norm_num)
  have hn2lt : n2 < 7.53 := by
    rw [hn2d, hup2]
    calc (Real.sqrt (15.53 * 0.47) : ℝ) < Real.sqrt ((7.53 : ℝ) ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 7.53 := Real.sqrt_sq (by norm_num)
  have hnotabs : ¬(|y2 - 2 * 2 - 2 * 2| < n2) := by
    rw [hy2, abs_of_pos (by norm_num : (0 : ℝ) < 7.53)]
    exact not_lt.mpr hn2lt.le
  have hatn2 : atn2 n2 (y2 - 2 * 2 - 2 * 2) = Real.pi / 2 - Real.arctan (n2 / 7.53) := by
    rw [atn2, if_neg hnotabs, if_pos hy2pos, hy2]
  rw [hatn1, hatn2]
  have hApos : 0 < Real.arctan (1.6496 / n1) :=
    Real.arctan_pos.mpr (div_pos (by norm_num) hnpos)
  have hu : (1.6496 : ℝ) / n1 < 1 := by
    refine (div_lt_one hnpos).mpr ?_
    rw [hn1d, hup1]
    refine Real.lt_sqrt_of_sq_lt ?_
    norm_num
  have hAlt : Real.arctan (1.6496 / n1) < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_lt_arctan_iff.mpr hu
  have hA2 : 2 * Real.arctan (1.6496 / n1) < Real.pi / 2 := by linarith
  have hπhalf : (0:ℝ) < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have hπn : -(Real.pi) / 2 < 0 := by rw [neg_div]; linarith
  have hAne : ∀ k : ℤ, Real.arctan (1.6496 / n1) ≠ (2 * k + 1) * Real.pi / 2 := by
    intro k hc
    by_cases h0 : k = 0
    · simp [h0] at hc
      linarith [hc, hAlt, hπhalf]
    · rcases lt_or_ge (0 : ℤ) k with hk | hk
      · have h1z : (1 : ℤ) ≤ 2 * k + 1 := by omega
        have hc1 : (1 : ℝ) ≤ 2 * ↑k + 1 := by exact_mod_cast h1z
        rw [hc] at hAlt
        have hge : Real.pi / 2 ≤ (2 * ↑k + 1) * Real.pi / 2 := by
          rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2)]
          have hb : Real.pi ≤ (2 * ↑k + 1) * Real.pi := by
            linarith [mul_le_mul_of_nonneg_right hc1 Real.pi_pos.le]
          exact mul_le_mul_of_nonneg_right hb (by norm_num : (0:ℝ) ≤ 2)
        linarith
      · have h1z : (2 * k + 1 : ℤ) ≤ -1 := by omega
        have hc1 : (2:ℝ) * ↑k + 1 ≤ -(1:ℝ) := by exact_mod_cast h1z
        rw [hc] at hApos
        have hle : (2 * ↑k + 1) * Real.pi / 2 ≤ -(Real.pi) / 2 := by
          rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2)]
          have hb : (2 * ↑k + 1) * Real.pi ≤ -Real.pi := by
            linarith [mul_le_mul_of_nonneg_right hc1 Real.pi_pos.le, Real.pi_pos]
          exact mul_le_mul_of_nonneg_right hb (by norm_num : (0:ℝ) ≤ 2)
        have h7 : (2 * ↑k + 1) * Real.pi / 2 < -(Real.pi) / 2 := by linarith
        exact absurd hApos (not_lt.mpr (le_trans (le_of_lt h7) (le_of_lt hπn)))
  have htan : Real.tan (2 * Real.arctan (1.6496 / n1))
      = 2 * (1.6496 / n1) / (1 - (1.6496 / n1) ^ 2) := by
    rw [show 2 * Real.arctan (1.6496 / n1)
          = Real.arctan (1.6496 / n1) + Real.arctan (1.6496 / n1) from by ring,
      Real.tan_add (Or.inl ⟨hAne, hAne⟩), Real.tan_arctan]
    ring
  have hsqrtden : Real.sqrt (6.3504 * 9.6496) = n1 := by rw [hn1d, hup1]
  have hsqrtB : Real.sqrt ((15.53 : ℝ) * 0.47) = n2 := by rw [hn2d, hup2]
  have hD : (0 : ℝ) < 6.3504 * 9.6496 - 1.6496 ^ 2 := by norm_num
  have h7 : (0 : ℝ) < 7.53 := by norm_num
  have hrhs : (2 * (1.6496 / Real.sqrt (6.3504 * 9.6496)))
        / (1 - (1.6496 / Real.sqrt (6.3504 * 9.6496)) ^ 2)
      = 2 * 1.6496 * Real.sqrt (6.3504 * 9.6496)
        / (6.3504 * 9.6496 - 1.6496 ^ 2) := by
    have hAsq : (Real.sqrt (6.3504 * 9.6496)) ^ 2 = 6.3504 * 9.6496 :=
      Real.sq_sqrt (by norm_num)
    have hDne : ((6.3504 * 9.6496 - 1.6496 ^ 2 : ℝ)) ≠ 0 := by norm_num
    field_simp [hAsq, hDne]
    · rw [hAsq]; exact div_self hDne
  have hmain : Real.sqrt ((15.53 : ℝ) * 0.47) * (6.3504 * 9.6496 - 1.6496 ^ 2)
      < 2 * 1.6496 * Real.sqrt (6.3504 * 9.6496) * 7.53 := by
    have e1 : (Real.sqrt ((15.53 : ℝ) * 0.47) * (6.3504 * 9.6496 - 1.6496 ^ 2)) ^ 2
        < (2 * 1.6496 * Real.sqrt (6.3504 * 9.6496) * 7.53) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15.53 * 0.47),
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6.3504 * 9.6496)]
      norm_num
    have hpos1 : (0 : ℝ) ≤ Real.sqrt ((15.53 : ℝ) * 0.47)
        * (6.3504 * 9.6496 - 1.6496 ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (by norm_num)
    have hpos2 : (0 : ℝ) ≤ 2 * 1.6496 * Real.sqrt (6.3504 * 9.6496) * 7.53 :=
      mul_nonneg (by positivity) (by norm_num)
    have e2 := Real.sqrt_lt_sqrt (sq_nonneg _) e1
    rwa [Real.sqrt_sq hpos1, Real.sqrt_sq hpos2] at e2
  have hcmp : n2 / 7.53 < Real.tan (2 * Real.arctan (1.6496 / n1)) := by
    rw [htan, ← hsqrtden, ← hsqrtB, hrhs]
    rw [div_lt_div_iff₀ h7 hD]
    exact hmain
  have hfinal : Real.arctan (n2 / 7.53) < 2 * Real.arctan (1.6496 / n1) := by
    have hrefl : 2 * Real.arctan (1.6496 / n1)
        = Real.arctan (Real.tan (2 * Real.arctan (1.6496 / n1))) :=
      (Real.arctan_tan (by linarith) hA2).symm
    rw [hrefl, Real.arctan_lt_arctan_iff]
    exact hcmp
  linarith

/-- HOL `NOT_MOD_4_CASES` (VASYYAU.hl:386). -/
theorem NOT_MOD_4_CASES_p25 (i p : ℕ) :
    (¬(i % 4 = (p + 2) % 4)) ↔
      (i % 4 = p % 4 ∨ i % 4 = (p + 1) % 4 ∨ i % 4 = (p + 3) % 4) := by
  omega

/-- HOL `NOT_MOD_4_CASES_3` (VASYYAU.hl:405). -/
theorem NOT_MOD_4_CASES_3_p25 (i p : ℕ) :
    (¬(i % 4 = (p + 3) % 4)) ↔
      (i % 4 = p % 4 ∨ i % 4 = (p + 1) % 4 ∨ i % 4 = (p + 2) % 4) := by
  omega

/-- HOL `STR_MOD_EQ` (VASYYAU.hl:969): `scs_is_str` is mod-invariant. -/
theorem STR_MOD_EQ_p25 (s : ScsV39) (v : ℕ → V3) (k : ℕ) (his : isScsV39 s)
    (hk : s.k = k) (hv : v ∈ MMsV39 s) (p : ℕ) :
    scsIsStr s v (p % k) ↔ scsIsStr s v p := by
  subst hk
  have hBB : BBsV39 s v := hv.1.1.1
  have hp := hBB.2.1
  have hconv : ∀ q : ℕ, scsIsStr s v (q % s.k) = scsIsStr s v q := by
    intro q
    have h23 := periodic_mod_eq_p23 hp
    have h1 : ((q % s.k) + 1) % s.k = (q + 1) % s.k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq q s.k)
    have h2 : ((q % s.k) + (s.k - 1)) % s.k = (q + (s.k - 1)) % s.k :=
      Nat.ModEq.add_right (s.k - 1) (Nat.mod_modEq q s.k)
    simp only [scsIsStr]
    congr 1
    rw [h23 q, ← h23 ((q % s.k) + 1), h1, h23 (q + 1),
      ← h23 ((q % s.k) + (s.k - 1)), h2, h23 (q + (s.k - 1))]
  exact Iff.of_eq (hconv p)

/-- HOL `SCS_STR_CASES_4` (VASYYAU.hl:424): with two adjacent non-str
indices, at least one of the two remaining indices is non-str. -/
theorem SCS_STR_CASES_4_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hk : s.k = 4) (hv : v ∈ MMsV39 s) (h1 : ¬scsIsStr s v p)
    (h2 : ¬scsIsStr s v (p + 1)) :
    ¬scsIsStr s v (p + 3) ∨ ¬scsIsStr s v (p + 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc3, hc2⟩ := hcon
  have hW := WGDHPPI_p25 s v his hk hv
  have hS : ({i | i < s.k ∧ scsIsStr s v i} : Set ℕ).Finite :=
    (Set.finite_Iio s.k).subset fun x hx => Set.mem_Iio.mpr hx.1
  have hme : ∀ q : ℕ, scsIsStr s v q → q % 4 ∈ {i | i < s.k ∧ scsIsStr s v i} := by
    intro q hq
    refine ⟨by omega, ?_⟩
    exact (STR_MOD_EQ_p25 s v 4 his hk hv q).mpr hq
  have m3 := hme (p + 3) hc3
  have m2 := hme (p + 2) hc2
  have hpair : ({(p + 3) % 4, (p + 2) % 4} : Set ℕ) ⊆ {i | i < s.k ∧ scsIsStr s v i} := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact m3
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact m2
  have hle := Set.ncard_le_ncard hpair hS
  rw [Set.ncard_pair (by omega : (p + 3) % 4 ≠ (p + 2) % 4)] at hle
  omega

/-- HOL `NEHXMWH_concl` (VASYYAU.hl:498): the quad endpoint registry
display (FF-image form). -/
def NEHXMWH_concl_p25 : Prop :=
  main_nonlinear_terminal_v11 → ∀ (s : ScsV39) (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ),
    (Set.range fun i => (v i, v (i + 1)) : Set (V3 × V3)) = FF →
    isScsV39 s → s.k = 4 → v ∈ MMsV39 s → scsBasicV39 s → scsGeneric v →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, i % 4 ≠ (p + 2) % 4 → interiorAngle1 0 FF (v i) < Real.pi) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨ dist (v p) (v (p + 1)) = s.b p (p + 1)

/-- HOL `NEHXMWH1_concl` (VASYYAU.hl:510): the `p+3` variant. -/
def NEHXMWH1_concl_p25 : Prop :=
  main_nonlinear_terminal_v11 → ∀ (s : ScsV39) (FF : Set (V3 × V3)) (v : ℕ → V3) (p : ℕ),
    (Set.range fun i => (v i, v (i + 1)) : Set (V3 × V3)) = FF →
    isScsV39 s → s.k = 4 → v ∈ MMsV39 s → scsBasicV39 s → scsGeneric v →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, i % 4 ≠ (p + 3) % 4 → interiorAngle1 0 FF (v i) < Real.pi) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨ dist (v p) (v (p + 1)) = s.b p (p + 1)

/-- HOL `TUAPYYU_concl` (VASYYAU.hl:498-640 block): the `mk_imp` chain
target. -/
def TUAPYYU_concl_p25 : Prop :=
  main_nonlinear_terminal_v11 → ∀ (s : ScsV39) (v : ℕ → V3) (p : ℕ),
    isScsV39 s → scsBasicV39 s → s.k = 4 → v ∈ MMsV39 s →
    (∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j) →
    (∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) →
    ¬scsIsStr s v p → ¬scsIsStr s v (p + 1) →
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∨ dist (v p) (v (p + 1)) = s.b p (p + 1)

/-- HOL `TUAPYYU1` (VASYYAU.hl:536) = `mk_imp (NEHXMWH1_concl,
mk_imp (NEHXMWH_concl, TUAPYYU_concl))`. NEEDS: the interior-angle
machinery (`BBS_IMP_CONVEX_LOCAL_FAN`, `BB_RHO_NODE_IVS`,
`IN_V_IMP_AZIM_LESS_PI`, the `ivs_rho_node1` bridge) — the JOTSWIX/
Local_lemmas kit, not yet ported. -/
theorem TUAPYYU1_p25 : NEHXMWH1_concl_p25 → NEHXMWH_concl_p25 → TUAPYYU_concl_p25 := by
  sorry

/-- HOL `TUAPYYU` (VASYYAU.hl:640): from `TUAPYYU1` via the JOTSWIX quad
endpoint lemmas (`NEHXMWH`/`BZQNDMN`, ported as LocalAuto23
`NEHXMWH_p23`/`BZQNDMN_p23`); discharged here by the identical LocalAuto1
registry twin. -/
theorem TUAPYYU_p25 : TUAPYYU_concl_p25 := fun _ => TUAPYYU_concl

/-- HOL `TUAPYYU_IMP_CASES` (VASYYAU.hl:1058): the endpoint distance is one
of `&2, &2*h0, cstab`. -/
theorem TUAPYYU_IMP_CASES_p25 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (h1 : isScsV39 s) (h2 : scsBasicV39 s) (h3 : s.k = 4)
    (h4 : v ∈ MMsV39 s)
    (h5 : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (h6 : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h7 : ¬scsIsStr s v p) (h8 : ¬scsIsStr s v (p + 1)) :
    dist (v p) (v (p + 1)) = 2 ∨ dist (v p) (v (p + 1)) = 2 * h0 ∨
      dist (v p) (v (p + 1)) = cstab := by
  rcases h6 p with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rcases TUAPYYU_p25 h s v p h1 h2 h3 h4 h5 h6 h7 h8 with he | he
    · left; rw [he, a1]
    · right; left; rw [he, a2]
  · rcases TUAPYYU_p25 h s v p h1 h2 h3 h4 h5 h6 h7 h8 with he | he
    · right; left; rw [he, a1]
    · right; right; rw [he, a2]

/-- HOL `SCS_M_CASES_4_LE_2` (VASYYAU.hl:652): the `scs_M` cardinality —
exactly the 21st `isScsV39` conjunct specialised to `k = 4`. -/
theorem SCS_M_CASES_4_LE_2_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4) :
    (scsM s).ncard ≤ 2 := by
  have hcard := his.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [hk] at hcard
  simp only [scsM]
  rw [hk]
  omega

/-- HOL `SCS_M_CASES_4_EQ` (VASYYAU.hl:662). -/
theorem SCS_M_CASES_4_EQ_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {(p % 4), ((p + 3) % 4)} ⊆ scsM s) :
    scsM s = {(p % 4), ((p + 3) % 4)} := by
  have hle := SCS_M_CASES_4_LE_2_p25 s his hk
  have hfin : (scsM s).Finite :=
    (Set.finite_Iio s.k).subset fun x hx => Set.mem_Iio.mpr hx.1
  have hcard : ({(p % 4), ((p + 3) % 4)} : Set ℕ).ncard = 2 :=
    Set.ncard_pair (by omega)
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hle) hfin).symm

/-- HOL `B_LE_2h0_SCS_M_4` (VASYYAU.hl:676). -/
theorem B_LE_2h0_SCS_M_4_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {(p % 4), ((p + 3) % 4)} ⊆ scsM s) :
    s.b (p + 1) (p + 2) ≤ 2 * h0 := by
  have hEQ := SCS_M_CASES_4_EQ_p25 s his hk hsub
  obtain ⟨_, h3k, _, _, _, _, _, _, _, _, hpb, _, _, _, _, _, _, _, _, _, _⟩ := his
  -- 21 conjuncts: 1:d<0.9 2:3≤k 3:k≤6 4-7:Periodic 8:Pa 9:Pam 10:Pbm 11:Pb 12:PJ
  -- 13:sym 14:chain 15:aii 16:2≤a 17:b3 18:bc 19:Jadj 20:Jsqrt 21:card
  have hlt : (p + 1) % 4 < s.k := by omega
  have hnm : (p + 1) % 4 ∉ scsM s := by
    intro hmem
    rw [hEQ] at hmem
    rcases Set.mem_insert_iff.mp hmem with hh | hh
    · omega
    · rw [Set.mem_singleton_iff] at hh
      omega
  simp only [scsM, Set.mem_setOf_eq] at hnm
  have hnb : ¬(2 * h0 < s.b ((p + 1) % 4) (((p + 1) % 4) + 1)) := fun hq =>
    hnm ⟨hlt, Or.inl hq⟩
  have e : s.b (p + 1) (p + 2) = s.b ((p + 1) % 4) (((p + 1) % 4) + 1) := by
    rw [hk] at hpb
    exact (periodic2_suc_mod_eq_p25 hpb (p + 1)).symm
  rw [e]
  exact le_of_not_gt hnb

/-- HOL `B_LE_2h0_2_SCS_M_4` (VASYYAU.hl:695): the `(p+2, p+3)` edge. -/
theorem B_LE_2h0_2_SCS_M_4_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {(p % 4), ((p + 3) % 4)} ⊆ scsM s) :
    s.b (p + 2) (p + 3) ≤ 2 * h0 := by
  have hEQ := SCS_M_CASES_4_EQ_p25 s his hk hsub
  obtain ⟨_, h3k, _, _, _, _, _, _, _, _, hpb, _, _, _, _, _, _, _, _, _, _⟩ := his
  -- 21 conjuncts: 1:d<0.9 2:3≤k 3:k≤6 4-7:Periodic 8:Pa 9:Pam 10:Pbm 11:Pb 12:PJ
  -- 13:sym 14:chain 15:aii 16:2≤a 17:b3 18:bc 19:Jadj 20:Jsqrt 21:card
  have hlt : (p + 2) % 4 < s.k := by omega
  have hnm : (p + 2) % 4 ∉ scsM s := by
    intro hmem
    rw [hEQ] at hmem
    rcases Set.mem_insert_iff.mp hmem with hh | hh
    · omega
    · rw [Set.mem_singleton_iff] at hh
      omega
  simp only [scsM, Set.mem_setOf_eq] at hnm
  have hnb : ¬(2 * h0 < s.b ((p + 2) % 4) (((p + 2) % 4) + 1)) := fun hq =>
    hnm ⟨hlt, Or.inl hq⟩
  have e : s.b (p + 2) (p + 3) = s.b ((p + 2) % 4) (((p + 2) % 4) + 1) := by
    rw [hk] at hpb
    exact (periodic2_suc_mod_eq_p25 hpb (p + 2)).symm
  rw [e]
  exact le_of_not_gt hnb

/-- HOL `B_LE_2h0_2_SCS_M_4` (VASYYAU.hl:714, second declaration of the
same name): the conjunction of both edges. -/
theorem B_LE_2h0_2_SCS_M_4_pair_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {(p % 4), ((p + 3) % 4)} ⊆ scsM s) :
    s.b (p + 1) (p + 2) ≤ 2 * h0 ∧ s.b (p + 2) (p + 3) ≤ 2 * h0 :=
  ⟨B_LE_2h0_SCS_M_4_p25 s his hk hsub, B_LE_2h0_2_SCS_M_4_p25 s his hk hsub⟩
/-- HOL `SCS_M_CASES_4_EQ1` (VASYYAU.hl:1073): the `p+1, p+3` pair. -/
theorem SCS_M_CASES_4_EQ1_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {((p + 1) % 4), ((p + 3) % 4)} ⊆ scsM s) :
    scsM s = {((p + 1) % 4), ((p + 3) % 4)} := by
  have hle := SCS_M_CASES_4_LE_2_p25 s his hk
  have hfin : (scsM s).Finite :=
    (Set.finite_Iio s.k).subset fun x hx => Set.mem_Iio.mpr hx.1
  have hcard : ({(p + 1) % 4, ((p + 3) % 4)} : Set ℕ).ncard = 2 :=
    Set.ncard_pair (by omega)
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hle) hfin).symm

/-- HOL `B_LE_2h0_2_SCS_M_4_1` (VASYYAU.hl:1090): the `(p+2, p+3)` edge
from the `p+1, p+3` pair. -/
theorem B_LE_2h0_2_SCS_M_4_1_p25 (s : ScsV39) (his : isScsV39 s) (hk : s.k = 4)
    (hsub : {((p + 1) % 4), ((p + 3) % 4)} ⊆ scsM s) :
    s.b (p + 2) (p + 3) ≤ 2 * h0 := by
  have hEQ := SCS_M_CASES_4_EQ1_p25 s his hk hsub
  obtain ⟨_, h3k, _, _, _, _, _, _, _, _, hpb, _, _, _, _, _, _, _, _, _, _⟩ := his
  have hlt : (p + 2) % 4 < s.k := by omega
  have hnm : (p + 2) % 4 ∉ scsM s := by
    intro hmem
    rw [hEQ] at hmem
    rcases Set.mem_insert_iff.mp hmem with hh | hh
    · omega
    · rw [Set.mem_singleton_iff] at hh
      omega
  simp only [scsM, Set.mem_setOf_eq] at hnm
  have hnb : ¬(2 * h0 < s.b ((p + 2) % 4) (((p + 2) % 4) + 1)) := fun hq =>
    hnm ⟨hlt, Or.inl hq⟩
  have e : s.b (p + 2) (p + 3) = s.b ((p + 2) % 4) (((p + 2) % 4) + 1) := by
    rw [hk] at hpb
    exact (periodic2_suc_mod_eq_p25 hpb (p + 2)).symm
  rw [e]
  exact le_of_not_gt hnb

/-- HOL `WKZZEEH` (VASYYAU.hl:720). Re-export of the LocalAuto1 registry
twin `WKZZEEH_concl`. -/
theorem WKZZEEH_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h1 : ¬scsIsStr s v p) (h2 : ¬scsIsStr s v (p + 1))
    (h3 : ¬scsIsStr s v (p + 3)) :
    ¬(dist (v p) (v (p + 3)) = cstab ∧ dist (v p) (v (p + 1)) = cstab) :=
  WKZZEEH_concl s v p his hbasic hk hv hdiag hval h1 h2 h3

/-- HOL `BASIC_IMP_NOT_J` (VASYYAU.hl:915). -/
theorem BASIC_IMP_NOT_J_p25 (s : ScsV39) (hb : scsBasicV39 s) (p i : ℕ) :
    s.J p i = False := hb.2 p i

/-- HOL `CONDTION_A_LT_B` (VASYYAU.hl:919). -/
theorem CONDTION_A_LT_B_p25 (s : ScsV39) (h : ∀ i : ℕ,
    (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
    (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab)) (i : ℕ) :
    s.a i (i + 1) < s.b i (i + 1) := by
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; norm_num [h0]
  · rw [h1, h2]; norm_num [h0, cstab]

/-- HOL `A_EQ2_IMP_B` (VASYYAU.hl:928). -/
theorem A_EQ2_IMP_B_p25 (s : ScsV39) (p : ℕ) (h : ∀ i : ℕ,
    (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
    (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hp : s.a p (p + 1) = 2) : s.b p (p + 1) = 2 * h0 := by
  rcases h p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · rw [h1] at hp; norm_num [h0] at hp

/-- HOL `A_EQ2h0_IMP_B` (VASYYAU.hl:938). -/
theorem A_EQ2h0_IMP_B_p25 (s : ScsV39) (p : ℕ) (h : ∀ i : ℕ,
    (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
    (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hp : s.a p (p + 1) = 2 * h0) : s.b p (p + 1) = cstab := by
  rcases h p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hp; norm_num [h0] at hp
  · exact h2

/-- HOL `A_NOT_EQ2_IMP_B` (VASYYAU.hl:949). -/
theorem A_NOT_EQ2_IMP_B_p25 (s : ScsV39) (p : ℕ) (h : ∀ i : ℕ,
    (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
    (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hp : ¬(s.a p (p + 1) = 2)) :
    s.a p (p + 1) = 2 * h0 ∧ s.b p (p + 1) = cstab := by
  rcases h p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h1 hp
  · exact ⟨h1, h2⟩

/-- HOL `B_LE_2h0_IMP_B` (VASYYAU.hl:958). -/
theorem B_LE_2h0_IMP_B_p25 (s : ScsV39) (p : ℕ) (h : ∀ i : ℕ,
    (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
    (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hle : s.b p (p + 1) ≤ 2 * h0) :
    s.a p (p + 1) = 2 ∧ s.b p (p + 1) = 2 * h0 := by
  rcases h p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · rw [h2] at hle; norm_num [h0, cstab] at hle

/-- HOL `IN_SCS_STR_CASES_4` (VASYYAU.hl:987). -/
theorem IN_SCS_STR_CASES_4_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hk : s.k = 4) (hv : v ∈ MMsV39 s) (hstr : scsIsStr s v p) :
    p % 4 ∈ {i | i < s.k ∧ scsIsStr s v i} :=
  ⟨by omega, (STR_MOD_EQ_p25 s v 4 his hk hv p).mpr hstr⟩

/-- HOL `FINITE_SET_STR` (VASYYAU.hl:998). -/
theorem FINITE_SET_STR_p25 (k : ℕ) (s : ScsV39) (v : ℕ → V3) :
    ({i | i < k ∧ scsIsStr s v i} : Set ℕ).Finite :=
  (Set.finite_Iio k).subset fun x hx => Set.mem_Iio.mpr hx.1

/-- HOL `NOT_STR_IN_CASES_4` (VASYYAU.hl:1004): the three successor
indices are non-str. -/
theorem NOT_STR_IN_CASES_4_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hk : s.k = 4) (hv : v ∈ MMsV39 s) (hstr : scsIsStr s v p) :
    ¬scsIsStr s v (p + 1) ∧ ¬scsIsStr s v (p + 2) ∧ ¬scsIsStr s v (p + 3) := by
  have hW := WGDHPPI_p25 s v his hk hv
  have hS := FINITE_SET_STR_p25 s.k s v
  have hme : ∀ q : ℕ, scsIsStr s v q → q % 4 ∈ {i | i < s.k ∧ scsIsStr s v i} := by
    intro q hq
    exact ⟨by omega, (STR_MOD_EQ_p25 s v 4 his hk hv q).mpr hq⟩
  have hcontra : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → scsIsStr s v (p + j) → False := by
    intro j hj hsj hc
    have m0 := hme p hstr
    have mj := hme (p + j) hc
    have hpair : ({p % 4, (p + j) % 4} : Set ℕ) ⊆ {i | i < s.k ∧ scsIsStr s v i} := by
      intro x hx
      rw [Set.mem_insert_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact m0
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact mj
    have hle := Set.ncard_le_ncard hpair hS
    rw [Set.ncard_pair (show p % 4 ≠ (p + j) % 4 by omega)] at hle
    omega
  exact ⟨fun hc => hcontra 1 (by omega) (by omega) hc,
    fun hc => hcontra 2 (by omega) (by omega) hc,
    fun hc => hcontra 3 (by omega) (by omega) hc⟩

/-- HOL `NOT_STR_IN_CASES_4_1` (VASYYAU.hl:1032): the `p+1` variant. -/
theorem NOT_STR_IN_CASES_4_1_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hk : s.k = 4) (hv : v ∈ MMsV39 s) (hstr : scsIsStr s v (p + 1)) :
    ¬scsIsStr s v p ∧ ¬scsIsStr s v (p + 2) ∧ ¬scsIsStr s v (p + 3) := by
  obtain ⟨h2, h3, h4⟩ := NOT_STR_IN_CASES_4_p25 s v (p + 1) his hk hv hstr
  refine ⟨fun hp => h4 ?_, h2, h3⟩
  have hmp := (STR_MOD_EQ_p25 s v 4 his hk hv p).mpr hp
  have he : scsIsStr s v (p + 4) = scsIsStr s v ((p + 4) % 4) :=
    (propext (STR_MOD_EQ_p25 s v 4 his hk hv (p + 4))).symm
  rw [he, show (p + 4) % 4 = p % 4 from by omega]
  exact hmp

/-- HOL `PRO_ADD_NOT_IN_SCS_M` (VASYYAU.hl:1047): an `a = &2*h0` edge
puts its residue in `scs_M`. -/
theorem PRO_ADD_NOT_IN_SCS_M_p25 (s : ScsV39) (i k : ℕ) (his : isScsV39 s)
    (hk : s.k = k) (hval : s.a i (i + 1) = 2 * h0) : i % k ∈ scsM s := by
  obtain ⟨_, h3k, _, _, _, _, _, hpa, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := his
  rw [hk] at h3k hpa
  simp only [scsM, Set.mem_setOf_eq]
  rw [hk]
  have hlt : i % k < k := Nat.mod_lt i (by omega)
  refine ⟨hlt, Or.inr ?_⟩
  rw [periodic2_suc_mod_eq_p25 hpa i, hval]
  norm_num [h0]

/-- HOL `SCS_A_SYM` (VASYYAU.hl:1111). -/
theorem SCS_A_SYM_p25 (s : ScsV39) (his : isScsV39 s) (i j : ℕ) :
    s.a i j = s.a j i :=
  (his.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).1

/-- HOL `SCS_B_SYM` (VASYYAU.hl:1116). -/
theorem SCS_B_SYM_p25 (s : ScsV39) (his : isScsV39 s) (i j : ℕ) :
    s.b i j = s.b j i :=
  (his.2.2.2.2.2.2.2.2.2.2.2.2.1 i j).2.2.2.1

/-- HOL `h0_CSTAB_LT_4` (VASYYAU.hl:2355). -/
theorem h0_CSTAB_LT_4_p25 :
    2 < 2 * h0 ∧ cstab < 4 ∧ 2 ≤ 2 * h0 ∧ cstab ≤ 4 ∧ 2 * h0 < 4 ∧ 2 < 4 := by
  norm_num [h0, cstab]

/-- HOL `PWEIWBZ` (VASYYAU.hl:1126). Re-export of the LocalAuto1 registry
twin `PWEIWBZ_concl`. -/
theorem PWEIWBZ_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha : s.a p (p + 1) = 2) : dist (v p) (v (p + 1)) = 2 :=
  PWEIWBZ_concl s v p his hbasic hk hv hdiag hval ha

/-- HOL `VASYYAU` (VASYYAU.hl:2366): the master str-case conclusion.
Re-export of the LocalAuto1 registry twin `VASYYAU_concl`. -/
theorem VASYYAU_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hstr : scsIsStr s v p) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∧ dist (v p) (v (p + 3)) = s.a p (p + 3) :=
  VASYYAU_concl s v p his hbasic hk hv hdiag hval hstr

/-- HOL `YEBWJNG` (VASYYAU.hl:292). Re-export of the LocalAuto1 registry
twin `YEBWJNG_concl`. -/
theorem YEBWJNG_p25 (s : ScsV39) (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h1 : ¬scsIsStr s v p) (h2 : ¬scsIsStr s v (p + 1)) (ha : s.a p (p + 1) = 2) :
    dist (v p) (v (p + 1)) = 2 :=
  YEBWJNG_concl s v p his hbasic hk hv hdiag hval h1 h2 ha
