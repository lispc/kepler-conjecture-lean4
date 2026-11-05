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
    (statement verbatim; body assembled IN PLACE by wave la27-zithlqn-w1
    from the Section-A kit — `exists_vv_p25` parameterises each fan, the
    `exists_vv3_p25`/`ZITHLQN_CASE_*` components realise the systems, and
    the private `zithlqnRot_w1` rotation kit re-anchors the two `a_pro`
    cases, so `exists_vv_FF_p25` is not consumed any more; the only
    inherited root is `exists_vv_p25`'s own `sorry`). It is therefore no
    longer a re-export of the LocalAuto1 registry arrow `ZITHLQN_concl`
    (which itself stays `sorry`: LA25 imports LA1, so the LA1 twin cannot
    cite any of this kit — the arrow direction blocks an LA1-side
    assembly).
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
    kit; after the 2026-09-21 re-scan the only three sorries are the two
    `rhoNode1`-cycle enumerators (`exists_vv_FF_p25`/`exists_vv_p25`, blocked
    by the unported `ITER`/dart-layer orbit kit) and `TUAPYYU1_p25` (blocked
    by the interior-angle→azim kit, whose LocalAuto23 plug-ins are still
    `sorry`). Of the 7 circuit-concl twins
    (ZITHLQN/WGDHPPI/TUAPYYU/YEBWJNG/WKZZEEH/PWEIWBZ/VASYYAU) six are kept
    as LocalAuto1 registry re-exports (LocalConcl category (b): vacuous, not
    discharges); ZITHLQN left the class on 2026-10-28 (wave la27-zithlqn-w1
    assembled its body in place from the Section-A kit, statement verbatim;
    inherited taint: the single `exists_vv_p25` root). Proved items are mechanical (mod arithmetic, set
    bookkeeping, csAdj value tables, `norm_num` numerics).
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto23
import Kepler.Text.AzimBridge
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

/-! ### The rhoNode1 dart-cycle kit (wave la25-rhonode1-w1)

The HOL `exists_vv`/`exists_vv_FF` witness `vv := fun i => ITER i (rho_node1 FF) v`
is rebuilt here on the p2 bridge: `LocalFan` lands in the `localFan_p2` world
via AzimBridge `localFan_p2.of_LocalFan_noIso` (the no-isolated-vertices premise
is the LA1 `LocalFan` 2-regular conjunct `∀ u ∈ V, (ee u E).ncard = 2` via
`w1hedge`), where the public `WRGCVDR_BIJ` / `WRGCVDR_ORBIT` (LocalAuto2) supply
the dart bijection and the orbit condition. `rhoNode1_p2` is the same
`Classical.epsilon` construction as LA1's `rhoNode1` (defeq, see
`rhoNode1_p2_eq`), so the p2 facts transfer verbatim; the orbit-cycle engine
(`w1cycMul`/`w1cycMod`/`w1orbitKey`/`w1orbitCycle`) is the generic LA7 `w6a_*`
kit rebuilt (private there). Import note: AzimBridge is already in the
transitive environment of every LA25 consumer (LA24 → LA36 → AzimBridge), and
LA7/la36 witness the LA1+LA23+AzimBridge co-existence. -/

/-- `rhoNode1_p2` (LA2:210) is LA1's `rhoNode1` (LocalAuto1:100) verbatim. -/
private theorem rhoNode1_p2_eq (FF : Set (V3 × V3)) : rhoNode1_p2 FF = rhoNode1 FF := rfl

/-- Every vertex of `V` lies on an edge (from the 2-regular conjunct). -/
private theorem w1hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E) ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

/-- The first component of a dart is a vertex (p2 dart bijection, maps-to half). -/
private theorem w1fstMem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hlf : LocalFan V E FF) (h3 : 3 ≤ ncard V) {v w : V3} (hvw : (v, w) ∈ FF) :
    v ∈ V := by
  have hcopy := hlf
  obtain ⟨-, -, -, -, -, h2reg⟩ := hcopy
  obtain ⟨hmap, -, -⟩ := WRGCVDR_BIJ (localFan_p2.of_LocalFan_noIso hlf (w1hedge h2reg))
  exact hmap hvw

/-- `Classical.epsilon` collapse under a uniqueness hypothesis (LA7 `w6a_epsilon_fixed`). -/
private theorem w1epsFixed {α : Type*} [Nonempty α] {p : α → Prop} {a : α} (hpa : p a)
    (huniq : ∀ y, p y → y = a) : Classical.epsilon p = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- LA7 `w6a_deter` (HOL `DETER_RHO_NODE`): the dart out of `v` is determined. -/
private theorem w1deter_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) {v w : V3} (hw : (v, w) ∈ FF) : rhoNode1_p2 FF v = w := by
  obtain ⟨-, hinj, -⟩ := WRGCVDR_BIJ h
  exact w1epsFixed hw fun y hy => (congrArg Prod.snd (hinj hw hy rfl)).symm

/-- LA5 `LOCAL_FAN_RHO_NODE_PROS` (15-line `WRGCVDR_BIJ` derivation). -/
private theorem w1rhoPro_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) :
    (∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF) ∧ ∀ d ∈ FF, d = (d.1, rhoNode1_p2 FF d.1) := by
  obtain ⟨hmap, hinj, hsurj⟩ := WRGCVDR_BIJ h
  have hleft : ∀ x ∈ V, (x, rhoNode1_p2 FF x) ∈ FF := by
    intro x hx
    obtain ⟨d, hd, hfd⟩ := hsurj hx
    have hdeq : (x, d.2) = d := Prod.ext hfd.symm rfl
    have hmemFF : (x, d.2) ∈ FF := by
      rw [hdeq]
      exact hd
    exact Classical.epsilon_spec (p := fun w => (x, w) ∈ FF) ⟨d.2, hmemFF⟩
  refine ⟨hleft, fun d hd => ?_⟩
  exact (hinj (hleft d.1 (hmap hd)) hd rfl).symm

/-- q-periodic points stay fixed under multiples of the period (LA7 copy). -/
private theorem w1cycMul {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (k : ℕ) : f^[k * q] x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, hqx, ih]

/-- Index reduction modulo a period (LA7 copy). -/
private theorem w1cycMod {α : Type*} (f : α → α) {x : α} {q : ℕ}
    (hqx : f^[q] x = x) (n : ℕ) : f^[n] x = f^[n % q] x := by
  have hsplit : n / q * q + n % q = n := Nat.div_add_mod' n q
  have hqx' : f^[q] (f^[n % q] x) = f^[n % q] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hqx]
  calc f^[n] x = f^[n / q * q + n % q] x := by rw [hsplit]
    _ = f^[n / q * q] (f^[n % q] x) := Function.iterate_add_apply f (n / q * q) (n % q) x
    _ = f^[n % q] x := w1cycMul f hqx' (n / q)

/-- Under the orbit condition, coinciding iterates force periodicity at the
index difference (LA7 copy). -/
private theorem w1orbitKey {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) {i j : ℕ}
    (hij2 : i ≤ j) (hij : f^[i] x = f^[j] x) : f^[j - i] x = x := by
  have hEq : j - i + i = j := by omega
  have hy : f^[j] x = f^[j - i] (f^[i] x) := by
    have h := Function.iterate_add_apply f (j - i) i x
    rwa [hEq] at h
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hyV : f^[i] x ∈ V := hmem i
  have hxO : x ∈ orbitF_p2 f (f^[i] x) := by rw [horb (f^[i] x) hyV]; exact hx
  obtain ⟨t, hxt⟩ := hxO
  have hfix : f^[j - i] (f^[i] x) = f^[i] x := hy.symm.trans hij.symm
  calc f^[j - i] x = f^[j - i] (f^[t] (f^[i] x)) := by rw [hxt]
    _ = f^[(j - i) + t] (f^[i] x) := (Function.iterate_add_apply f (j - i) t (f^[i] x)).symm
    _ = f^[t + (j - i)] (f^[i] x) := by rw [Nat.add_comm]
    _ = f^[t] (f^[j - i] (f^[i] x)) := Function.iterate_add_apply f t (j - i) (f^[i] x)
    _ = f^[t] (f^[i] x) := by rw [hfix]
    _ = x := hxt

/-- The orbit condition makes `V` a finite cycle; `p` is a common period with
`0 < p`, the first `p` iterates are pairwise distinct and exhaust `V`, and
`V.ncard = p` (LA7 `w6a_orbit_cycle` copy). -/
private theorem w1orbitCycle {α : Type*} {f : α → α} {V : Set α}
    (horb : ∀ x ∈ V, orbitF_p2 f x = V) {x : α} (hx : x ∈ V) :
    ∃ p : ℕ, 0 < p ∧ f^[p] x = x ∧
      (∀ i j : ℕ, i < j → j < p → f^[i] x ≠ f^[j] x) ∧
      ({f^[n] x | n < p} : Set α) = V ∧ V.ncard = p := by
  have hmem : ∀ n : ℕ, f^[n] x ∈ V := by
    intro n
    rw [← horb x hx]
    exact ⟨n, rfl⟩
  have hper : ∃ p : ℕ, 0 < p ∧ f^[p] x = x := by
    have hfx : f x ∈ V := hmem 1
    have hxO : x ∈ orbitF_p2 f (f x) := by rw [horb (f x) hfx]; exact hx
    obtain ⟨n, hn⟩ := hxO
    exact ⟨n + 1, Nat.succ_pos n, by rw [Function.iterate_succ_apply f n x]; exact hn⟩
  have hp0 : 0 < Nat.find hper := (Nat.find_spec hper).1
  have hpx : f^[Nat.find hper] x = x := (Nat.find_spec hper).2
  have hmin : ∀ m : ℕ, 0 < m → m < Nat.find hper → f^[m] x ≠ x :=
    fun m hm0 hmlt hcon => Nat.find_min hper hmlt ⟨hm0, hcon⟩
  have hkey : ∀ i j : ℕ, i ≤ j → f^[i] x = f^[j] x → f^[j - i] x = x :=
    fun i j hle hij' => w1orbitKey horb hx hle hij'
  have hdis : ∀ i j : ℕ, i < j → j < Nat.find hper → f^[i] x ≠ f^[j] x := by
    intro i j hij hjp hcon
    exact hmin (j - i) (by omega) (by omega) (hkey i j (Nat.le_of_lt hij) hcon)
  have hset : ({f^[n] x | n < Nat.find hper} : Set α) = V := by
    ext y
    constructor
    · rintro ⟨n, -, rfl⟩
      exact hmem n
    · intro hy
      have hYO : y ∈ orbitF_p2 f x := by rw [horb x hx]; exact hy
      obtain ⟨m, hm⟩ := hYO
      refine ⟨m % Nat.find hper, Nat.mod_lt _ hp0, ?_⟩
      rw [← w1cycMod f hpx m]
      exact hm
  have hcard : V.ncard = Nat.find hper := by
    have himage : ({f^[n] x | n < Nat.find hper} : Set α) =
        (fun n : ℕ => f^[n] x) '' Set.Iio (Nat.find hper) := rfl
    rw [← hset, himage]
    have hInj : Set.InjOn (fun n : ℕ => f^[n] x) (Set.Iio (Nat.find hper)) := by
      intro i hi j hj hcon
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact absurd hcon (hdis i j h (Set.mem_Iio.mp hj))
      · exact h
      · exact absurd hcon.symm (hdis j i h (Set.mem_Iio.mp hi))
    rw [Set.InjOn.ncard_image hInj]
    exact Set.ncard_Iio_nat _
  exact ⟨Nat.find hper, hp0, hpx, hdis, hset, hcard⟩

/-- An orbit that returns within two steps lives in a 2-point set. -/
private theorem w1orbit2 {α : Type*} {f : α → α} {u : α} (h2u : f (f u) = u) (n : ℕ) :
    f^[n] u ∈ ({u, f u} : Set α) := by
  induction n with
  | zero => exact Set.mem_insert _ _
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases Set.mem_insert_iff.mp ih with heq | heq
      · rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · rw [heq, h2u]
        exact Set.mem_insert _ _

/-- Under the orbit condition the rho-node has no fixed point above cardinal 3. -/
private theorem w1noFix {V : Set V3} {FF : Set (V3 × V3)}
    (horb : ∀ v ∈ V, orbitF_p2 (rhoNode1 FF) v = V) {u : V3} (hu : u ∈ V)
    (h3 : 3 ≤ ncard V) : (rhoNode1 FF) u ≠ u := by
  intro hfix
  have hsingle : orbitF_p2 (rhoNode1 FF) u = {u} := by
    ext y
    simp only [orbitF_p2, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, hfix]
    · intro h
      exact ⟨0, by rw [h]; rfl⟩
  have hV1 : V = {u} := by rw [← horb u hu, hsingle]
  rw [hV1] at h3
  simp only [Set.ncard_singleton] at h3
  omega

/-- LA5 `LOCAL_FAN_IN_FF_IN_ORD_PAIRS` role: darts of the face are ordered
pairs of edges; the self-pair branch dies on `w1noFix` + `3 ≤ ncard V`. -/
private theorem w1ffEdge_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (h3 : 3 ≤ ncard V) {d : V3 × V3} (hd : d ∈ FF) :
    {d.1, d.2} ∈ E := by
  have hc := h
  have horb1 : ∀ v ∈ V, orbitF_p2 (rhoNode1 FF) v = V := fun v hv =>
    WRGCVDR_ORBIT hc v hv
  obtain ⟨H, hdarts, -, -, -, -, ⟨z, hz, hFF⟩, -⟩ := h
  have hinf : d ∈ H.face z := by rw [← hFF]; exact hd
  have hdD : d ∈ (↑H.darts : Set (V3 × V3)) := H.face_subset_darts hz hinf
  rw [hdarts] at hdD
  rcases Set.mem_or_mem_of_mem_union hdD with ho | hs
  · show {d.1, d.2} ∈ E
    exact ho
  · exfalso
    have hs' : d.1 = d.2 ∧ d.1 ∈ V ∧ EE_p2 d.1 E = ∅ := hs
    obtain ⟨hdu, hdV, -⟩ := hs'
    have hd' : (d.1, d.2) ∈ FF := hd
    have hfx : rhoNode1 FF d.1 = d.1 := (w1deter_p2 hc hd').trans hdu.symm
    exact w1noFix horb1 hdV h3 hfx

/-! ### Cyclic enumeration of a local fan -/

/-- Shared body of `exists_vv_FF_p25` / `exists_vv_p25` (ZITHLQN.hl:70/:288):
the HOL witness `vv := fun i => ITER i (rho_node1 FF) v`, assembled from the
dart-cycle kit above. `vv (i+1) = rhoNode1 FF (vv i)` is carried for the
`exists_vv_FF_p25` anchor. -/
private theorem exists_vv_aux_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hlf : ConvexLocalFan V E FF) (h3 : 3 ≤ ncard V) (x : V3) (hx : x ∈ V) :
    ∃ vv : ℕ → V3, vv 0 = x ∧
      (∀ i, vv (i + 1) = rhoNode1 FF (vv i)) ∧
      (∀ i, vv i = vv (i % ncard V)) ∧
      (∀ i j, vv i = vv j → i % ncard V = j % ncard V) ∧
      (Set.range vv : Set V3) = V ∧
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E ∧
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF := by
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hlf.1
  have hp2 := localFan_p2.of_LocalFan_noIso hlf.1 (w1hedge h2reg)
  have horb : ∀ v ∈ V, orbitF_p2 (rhoNode1 FF) v = V := fun v hv =>
    WRGCVDR_ORBIT hp2 v hv
  obtain ⟨hmap, -, -⟩ := WRGCVDR_BIJ hp2
  have hpro : ∀ y ∈ V, (y, (rhoNode1 FF) y) ∈ FF := fun y hy =>
    (w1rhoPro_p2 hp2).1 y hy
  have hfV : ∀ i : ℕ, (rhoNode1 FF)^[i] x ∈ V := by
    intro i
    have h1 : (rhoNode1 FF)^[i] x ∈ orbitF_p2 (rhoNode1 FF) x := ⟨i, rfl⟩
    rwa [horb x hx] at h1
  obtain ⟨p, hp0, hpx, hdis, hset, hcard⟩ := w1orbitCycle horb hx
  have hV : (Set.range fun i => (rhoNode1 FF)^[i] x : Set V3) = V := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      have hy' : ((rhoNode1 FF)^[i] x : V3) ∈
          ({(rhoNode1 FF)^[n] x | n < p} : Set V3) :=
        ⟨i % p, Nat.mod_lt i hp0, (w1cycMod _ hpx i).symm⟩
      rwa [hset] at hy'
    · intro hy
      have hy' : y ∈ ({(rhoNode1 FF)^[n] x | n < p} : Set V3) := by rwa [hset]
      obtain ⟨n, -, hn'⟩ := hy'
      exact ⟨n, hn'⟩
  have hE : (Set.range fun i =>
      ({(rhoNode1 FF)^[i] x, (rhoNode1 FF)^[i + 1] x} : Set V3)) = E := by
    ext Z
    constructor
    · rintro ⟨i, rfl⟩
      show ({(rhoNode1 FF)^[i] x, (rhoNode1 FF)^[i + 1] x} : Set V3) ∈ E
      have hdart : (((rhoNode1 FF)^[i] x, (rhoNode1 FF)^[i + 1] x) : V3 × V3) ∈ FF := by
        rw [Function.iterate_succ_apply']
        exact hpro _ (hfV i)
      exact w1ffEdge_p2 hp2 h3 hdart
    · intro hZ
      obtain ⟨hfin, hc⟩ := hfan.2.1 Z hZ
      have h2 : Z.ncard = 2 := by
        rw [Set.ncard_eq_toFinset_card Z hfin]
        exact hc
      obtain ⟨u, w, huw, rfl⟩ := Set.ncard_eq_two.mp h2
      have huV : u ∈ V := by
        refine FAN_EDGE_EL_V (u := w) hfan ?_
        rw [Set.pair_comm]
        exact hZ
      have hwV : w ∈ V := FAN_EDGE_EL_V (u := u) hfan hZ
      have hwE : w ∈ ee u E := hZ
      obtain ⟨k, hk⟩ := Set.mem_range.mp (by rw [hV]; exact huV)
      have hfuu : (rhoNode1 FF) u ∈ ee u E := by
        show ({u, rhoNode1 FF u} : Set V3) ∈ E
        exact w1ffEdge_p2 hp2 h3 (hpro u huV)
      have hpre : ∃ a ∈ V, (rhoNode1 FF) a = u := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · refine ⟨(rhoNode1 FF)^[p - 1] x, hfV (p - 1), ?_⟩
          have hp1 : p - 1 + 1 = p := by omega
          calc (rhoNode1 FF) ((rhoNode1 FF)^[p - 1] x)
              = (rhoNode1 FF)^[p - 1 + 1] x := (Function.iterate_succ_apply' _ _ _).symm
            _ = (rhoNode1 FF)^[p] x := by rw [hp1]
            _ = x := hpx
            _ = u := hk
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          refine ⟨(rhoNode1 FF)^[m] x, hfV m, ?_⟩
          calc (rhoNode1 FF) ((rhoNode1 FF)^[m] x)
              = (rhoNode1 FF)^[m + 1] x := (Function.iterate_succ_apply' _ _ _).symm
            _ = u := hk
      obtain ⟨a, haV, haf⟩ := hpre
      have hae : a ∈ ee u E := by
        have hE1 : ({a, (rhoNode1 FF) a} : Set V3) ∈ E := w1ffEdge_p2 hp2 h3 (hpro a haV)
        rw [haf, Set.pair_comm] at hE1
        exact hE1
      have hne2 : a ≠ (rhoNode1 FF) u := by
        intro hcon
        have h2u : (rhoNode1 FF) ((rhoNode1 FF) u) = u :=
          (congrArg (rhoNode1 FF) hcon).symm.trans haf
        have hVsub : V ⊆ ({u, (rhoNode1 FF) u} : Set V3) := by
          intro y hy
          have hyo : y ∈ orbitF_p2 (rhoNode1 FF) u := by rw [horb u huV]; exact hy
          obtain ⟨n, hn⟩ := hyo
          rw [← hn]
          exact w1orbit2 h2u n
        have hune : u ≠ (rhoNode1 FF) u := fun h => w1noFix horb huV h3 h.symm
        have h1le : ncard V ≤ 2 := by
          refine le_trans (Set.ncard_le_ncard hVsub
            (Set.Finite.insert u (Set.finite_singleton ((rhoNode1 FF) u)))) ?_
          rw [Set.ncard_pair hune]
        omega
      have hfu_a : (rhoNode1 FF) u ≠ a := fun h => hne2 h.symm
      have hsub2 : ({(rhoNode1 FF) u, a} : Set V3) ⊆ ee u E := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with heq | heq
        · rw [heq]; exact hfuu
        · rw [heq]; exact hae
      have heq2 : ee u E = ({(rhoNode1 FF) u, a} : Set V3) := by
        have heeFin : (ee u E).Finite :=
          hfan.2.2.1.1.subset fun z hz => FAN_EDGE_EL_V hfan hz
        refine (Set.eq_of_subset_of_ncard_le hsub2 ?_ heeFin).symm
        rw [h2reg u huV, Set.ncard_pair (a := (rhoNode1 FF) u) (b := a) hfu_a]
      rw [heq2] at hwE
      rcases Set.mem_insert_iff.mp hwE with hwf | hwa
      · exact ⟨k, by
          show ({(rhoNode1 FF)^[k] x, (rhoNode1 FF)^[k + 1] x} : Set V3) = {u, w}
          rw [Function.iterate_succ_apply', hk, hwf]⟩
      · have hfw : (rhoNode1 FF) w = u := by rw [hwa]; exact haf
        obtain ⟨m, hm⟩ := Set.mem_range.mp (by rw [hV]; exact hwV)
        refine ⟨m, ?_⟩
        show ({(rhoNode1 FF)^[m] x, (rhoNode1 FF)^[m + 1] x} : Set V3) = {u, w}
        rw [Function.iterate_succ_apply', hm, hfw]
        exact Set.pair_comm w u
  have hFF : (Set.range fun i =>
      (((rhoNode1 FF)^[i] x, (rhoNode1 FF)^[i + 1] x) : V3 × V3)) = FF := by
    ext d
    constructor
    · rintro ⟨i, rfl⟩
      show (((rhoNode1 FF)^[i] x, (rhoNode1 FF)^[i + 1] x) : V3 × V3) ∈ FF
      rw [Function.iterate_succ_apply']
      exact hpro _ (hfV i)
    · intro hd
      have hde : d = (d.1, (rhoNode1 FF) d.1) := (w1rhoPro_p2 hp2).2 d hd
      have hd1V : d.1 ∈ V := hmap hd
      obtain ⟨k, hk⟩ := Set.mem_range.mp (by rw [hV]; exact hd1V)
      refine Set.mem_range.mpr ⟨k, ?_⟩
      show (((rhoNode1 FF)^[k] x, (rhoNode1 FF)^[k + 1] x) : V3 × V3) = d
      rw [hde, ← hk, Function.iterate_succ_apply']
  refine ⟨fun i => (rhoNode1 FF)^[i] x, rfl, fun i => Function.iterate_succ_apply' _ i x,
    ?_, ?_, hV, hE, hFF⟩
  · intro i
    show (rhoNode1 FF)^[i] x = (rhoNode1 FF)^[i % ncard V] x
    rw [w1cycMod (rhoNode1 FF) hpx i, hcard]
  · intro i j hij
    have hci : (rhoNode1 FF)^[i] x = (rhoNode1 FF)^[i % p] x := w1cycMod _ hpx i
    have hcj : (rhoNode1 FF)^[j] x = (rhoNode1 FF)^[j % p] x := w1cycMod _ hpx j
    have hcon : (rhoNode1 FF)^[i % p] x = (rhoNode1 FF)^[j % p] x := by
      rw [← hci, ← hcj]; exact hij
    rcases Nat.lt_trichotomy (i % p) (j % p) with h | h | h
    · exact absurd hcon (hdis _ _ h (Nat.mod_lt j hp0))
    · rw [hcard]; exact h
    · exact absurd hcon.symm (hdis _ _ h (Nat.mod_lt i hp0))


/-- HOL `exists_vv_FF` (ZITHLQN.hl:70): the `rho_node1`-cycle enumeration.
The HOL proof witnesses `vv := fun i => ITER i (rho_node1 FF) v` from the dart
`(v,w) ∈ FF`; `DETER_RHO_NODE` gives `vv 1 = w`, and the mod-periodicity /
injectivity / `range vv = V` / `range {vv i, vv (i+1)} = E` / `range (vv i,
vv (i+1)) = FF` identities come from `POWER_TO_ITER`, `LOFA_IMP_ITER_RHO_NODE_ID2`,
`Hypermap.power_map_fix_point`, `LT_CARD_MONO_LOFA`, `LOCAL_FAN_ORBIT_MAP_VITER*`,
`LOCAL_RHO_NODE_PAIR_E`, `LOCAL_FAN_RHO_NODE_PROS` (Local_lemmas/Wrgcvdr/Tecoxbm).
DISCHARGES: none of that `rhoNode1`-iterate↔`orbitMap (hypermapOfFan ...).faceMap`
dart-layer kit is ported on this side (LocalAuto1 only has the `LocalFan`/`Dih2k`
head and the generic `Hypermap.orbitMap` permutation theory; no FF→`rhoNode1`
dynamics bridge), so a non-vacuous proof is impossible here. NEEDS: the
polar-fan/dart-layer bridge, then `exists_point_in_V_p25` seeds `exists_vv_p25`. -/
theorem exists_vv_FF_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_h3 : 3 ≤ ncard V) (_h6 : ncard V ≤ 6) (v w : V3) (_hvw : (v, w) ∈ FF) :
    ∃ vv : ℕ → V3, vv 0 = v ∧ vv 1 = w ∧
      (∀ i, vv i = vv (i % ncard V)) ∧
      (∀ i j, vv i = vv j → i % ncard V = j % ncard V) ∧
      (Set.range vv : Set V3) = V ∧
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E ∧
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF := by
  obtain ⟨-, -, -, -, -, h2reg⟩ := _hlf.1
  obtain ⟨vv, h0, hsucc, hper, hinj, hV, hE, hFF⟩ :=
    exists_vv_aux_p25 V E FF _hlf _h3 v (w1fstMem _hlf.1 _h3 _hvw)
  refine ⟨vv, h0, ?_, hper, hinj, hV, hE, hFF⟩
  have h1 : vv 1 = rhoNode1 FF (vv 0) := hsucc 0
  rw [h1, h0]
  exact w1deter_p2 (localFan_p2.of_LocalFan_noIso _hlf.1 (w1hedge h2reg)) _hvw

/-- HOL `exists_vv` (ZITHLQN.hl:288). NEEDS: same `rhoNode1`-iterate cycle
kit as `exists_vv_FF_p25`; HOL seeds the base point via `exists_point_in_V`
(= the proved `exists_point_in_V_p25` here). -/
theorem exists_vv_p25 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (_hlf : ConvexLocalFan V E FF) (_hp : Kepler.Packing V) (_hb : V ⊆ ballAnnulus)
    (_h3 : 3 ≤ ncard V) (_h6 : ncard V ≤ 6) :
    ∃ vv : ℕ → V3, (∀ i, vv i = vv (i % ncard V)) ∧
      (∀ i j, vv i = vv j → i % ncard V = j % ncard V) ∧
      (Set.range vv : Set V3) = V ∧
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E ∧
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF := by
  obtain ⟨v, hv⟩ := exists_point_in_V_p25 V E FF _hlf _hp _hb _h3 _h6
  obtain ⟨vv, -, -, hper, hinj, hV, hE, hFF⟩ :=
    exists_vv_aux_p25 V E FF _hlf _h3 v hv
  exact ⟨vv, hper, hinj, hV, hE, hFF⟩

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

/-- **zithlqn membership bridge (wave la27-zithlqn-w1).** The eight
`sInitListV39` entries as a disjunction of definitional equalities; the
caller picks a branch by `rfl`. (Avoids `simp` over-normalising the
membership goal.) -/
private theorem zithlqn_mem_w1 (s : ScsV39)
    (h : s = mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6) ∨
      s = mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6) ∨
      s = mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6) ∨
      s = mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) ∨
      s = mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6) ∨
      s = mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6) ∨
      s = mkUnadornedV39 5 0.616 (aPro_p25 5 (2 * h0) 2 (2 * h0))
        (aPro_p25 5 (Real.sqrt 8) (2 * h0) 6) ∨
      s = mkUnadornedV39 4 0.477 (aPro_p25 4 (2 * h0) 2 (Real.sqrt 8))
        (aPro_p25 4 (Real.sqrt 8) (2 * h0) 6)) :
    s ∈ sInitListV39 := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]; exact List.Mem.head _
  · rw [h]; exact List.Mem.tail _ (List.Mem.head _)
  · rw [h]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))))
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))
  · rw [h]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

/-- **zithlqn rotation kit (wave la27-zithlqn-w1).** Re-indexing a periodic
enumeration by a fixed offset preserves periodicity, index-injectivity and
all three range equalities. This lets the unanchored `exists_vv_p25` witness
serve the two `a_pro` cases (the HOL anchors them via `exists_vv_FF`, which
would additionally need the `LOFA_IN_E_IMP_IN_FF` dart bridge, unavailable in
this import world). -/
private theorem zithlqnRot_shift_w1 (n j : ℕ) (vv : ℕ → V3) (hn : 0 < n)
    (hper : ∀ i, vv (i % n) = vv i) (m : ℕ) :
    ∃ k : ℕ, vv (k + j) = vv m ∧ vv (k + 1 + j) = vv (m + 1) := by
  by_cases hmj : j ≤ m
  · refine ⟨m - j, ?_, ?_⟩
    · rw [Nat.sub_add_cancel hmj]
    · rw [show m - j + 1 + j = m + 1 from by omega]
  · have hmul : j + 1 ≤ n * (j + 1) := Nat.le_mul_of_pos_left (j + 1) hn
    have hjle : j ≤ m + n * (j + 1) := by omega
    refine ⟨m + n * (j + 1) - j, ?_, ?_⟩
    · rw [Nat.sub_add_cancel hjle, ← hper, Nat.add_mul_mod_self_left, hper]
    · rw [show m + n * (j + 1) - j + 1 + j = m + 1 + n * (j + 1) from by omega, ← hper,
        Nat.add_mul_mod_self_left, hper]

private theorem zithlqnRot_w1 (n : ℕ) (vv : ℕ → V3) (j : ℕ) (hn : 0 < n)
    (hper : ∀ i, vv (i % n) = vv i) (hinj : ∀ a b, vv a = vv b → a % n = b % n) :
    (∀ m, vv ((m % n) + j) = vv (m + j)) ∧
    (∀ a b, vv (a + j) = vv (b + j) → a % n = b % n) ∧
    ((Set.range fun m => vv (m + j) : Set V3) = (Set.range vv : Set V3)) ∧
    ((Set.range (fun m => ({vv (m + j), vv (m + 1 + j)} : Set V3)) : Set (Set V3)) =
      (Set.range fun m => ({vv m, vv (m + 1)} : Set V3))) ∧
    ((Set.range (fun m => ((vv (m + j), vv (m + 1 + j)) : V3 × V3)) : Set (V3 × V3)) =
      (Set.range fun m => ((vv m, vv (m + 1)) : V3 × V3))) := by
  constructor
  · intro m
    have hkey : ((m % n) + j) ≡ (m + j) [MOD n] := by
      have e1 : (m % n) + j ≡ (m % n) + j % n [MOD n] :=
        Nat.ModEq.add_left _ (Nat.mod_modEq j n).symm
      have e2 : (m % n) + j % n ≡ m + j % n [MOD n] := Nat.ModEq.add_right _ (Nat.mod_modEq m n)
      have e3 : m + j % n ≡ m + j [MOD n] := Nat.ModEq.add_left _ (Nat.mod_modEq j n)
      exact e1.trans (e2.trans e3)
    rw [← hper ((m % n) + j), hkey, ← hper (m + j)]
  · constructor
    · intro a b hab
      have h1 : (a + j) ≡ (b + j) [MOD n] := hinj (a + j) (b + j) hab
      show a ≡ b [MOD n]
      exact Nat.ModEq.add_right_cancel' j h1
    · constructor
      · ext y
        constructor
        · rintro ⟨m, rfl⟩
          exact ⟨m + j, rfl⟩
        · rintro ⟨m, rfl⟩
          obtain ⟨k, e1, -⟩ := zithlqnRot_shift_w1 n j vv hn hper m
          exact ⟨k, e1⟩
      · constructor
        · ext Z
          constructor
          · rintro ⟨m, hm⟩
            refine ⟨m + j, ?_⟩
            simp only []
            rw [← hm]
            simp only []
            rw [Nat.add_right_comm m j 1]
          · rintro ⟨m, rfl⟩
            obtain ⟨k, e1, e2⟩ := zithlqnRot_shift_w1 n j vv hn hper m
            refine ⟨k, ?_⟩
            show ({vv (k + j), vv (k + 1 + j)} : Set V3) = ({vv m, vv (m + 1)} : Set V3)
            rw [e1, e2]
        · ext Z
          constructor
          · rintro ⟨m, hm⟩
            refine ⟨m + j, ?_⟩
            simp only []
            rw [← hm]
            simp only []
            rw [Nat.add_right_comm m j 1]
          · rintro ⟨m, rfl⟩
            obtain ⟨k, e1, e2⟩ := zithlqnRot_shift_w1 n j vv hn hper m
            refine ⟨k, ?_⟩
            show ((vv (k + j), vv (k + 1 + j)) : V3 × V3) = (vv m, vv (m + 1))
            rw [e1, e2]

/-- **zithlqn std-case worker (wave la27-zithlqn-w1).** One `csAdj` initial
system, one cardinality branch: parameterise the fan by `exists_vv_p25`,
realise it through the value-table case lemma, then read
`taustarV39 = tauFun − s.d` off the wave hypothesis. -/
private theorem zithlqnStd_w1 (h : ∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv →
    0 ≤ taustarV39 s vv)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (k : ℕ) (d : ℝ) (s : ScsV39)
    (hlf : ConvexLocalFan V E FF) (hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (h3 : 3 ≤ V.ncard) (h6 : V.ncard ≤ 6) (hk : V.ncard = k) (hk3 : 3 < k)
    (hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (hd : ∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (hcase : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3) (s : ScsV39),
      ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus → V.ncard = k →
      (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w) →
      (∀ v w : V3, {v, w} ∈ E → 2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
      s = mkUnadornedV39 k d (csAdj k 2 (2 * h0)) (csAdj k (2 * h0) 6) →
      (∀ i, vv (i % V.ncard) = vv i) →
      (∀ i j, vv i = vv j → i % V.ncard = j % V.ncard) →
      (Set.range vv : Set V3) = V →
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E →
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF →
      BBsV39 s vv)
    (hmem : s ∈ sInitListV39)
    (hseq : s = mkUnadornedV39 k d (csAdj k 2 (2 * h0)) (csAdj k (2 * h0) 6))
    (hsd : s.d = d) :
    d ≤ tauFun V E FF := by
  have hsk : s.k = k := by rw [hseq]; rfl
  obtain ⟨vv, hper, hinj, hV, hE, hFF⟩ := exists_vv_p25 V E FF hlf hp hb h3 h6
  have hBB : BBsV39 s vv :=
    hcase V E FF vv s hlf hp hb hk hne hd hseq (fun i => (hper i).symm) hinj hV hE hFF
  have hts : 0 ≤ taustarV39 s vv := h s hmem vv hBB
  rw [taustarV39, if_neg (by rw [hsk]; omega)] at hts
  rw [hV, hE, hFF, dsv_scs_init_p25 s hmem vv, hsd] at hts
  linarith

/-- **zithlqn a_pro pentagon in the corpus-original `2 * h0` band (wave
la27-zithlqn-w1).** The landed `ZITHLQN_CASE_5_pro_cs_p25` states its
non-edge slot in the strengthened `sqrt8` band, which `JEJTVGB_pent_pro_concl`
does not provide (its own band is `2 * h0`; the HOL original
ZITHLQN.hl:1478 also carries `2 * h0`). This wrapper re-derives the
realisation straight from the generic `bbsV39_aPro_cycle_p25` kit, whose
`hlow` slot is already `a2`-parameterised (`a2 = 2 * h0` for the pentagon). -/
private theorem zithlqnCase5Pro2h0_w1 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (vv : ℕ → V3) (s : ScsV39) (v0 w0 : V3)
    (hlf : ConvexLocalFan V E FF) (hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (hc : ncard V = 5)
    (hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → 2 * h0 ≤ dist v w)
    (hd : ∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (he : ({v0, w0} : Set V3) ∈ E)
    (hv0 : 2 * h0 ≤ dist v0 w0) (hw0 : dist v0 w0 ≤ Real.sqrt 8)
    (hseq : s = mkUnadornedV39 5 0.616 (aPro_p25 5 (2 * h0) 2 (2 * h0))
      (aPro_p25 5 (Real.sqrt 8) (2 * h0) 6))
    (hper : ∀ i, vv (i % ncard V) = vv i)
    (hinj : ∀ i j, vv i = vv j → i % ncard V = j % ncard V)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (hvv0 : vv 0 = v0) (hvv1 : vv 1 = w0) :
    BBsV39 s vv := by
  have hper5 : ∀ i, vv (i % 5) = vv i := by
    intro i
    have h := hper i
    rwa [hc] at h
  have hinj5 : ∀ i j, vv i = vv j → i % 5 = j % 5 := by
    intro i j hij
    have h := hinj i j hij
    rwa [hc] at h
  exact bbsV39_aPro_cycle_p25 5 0.616 (2 * h0) s vv V E FF hseq (by omega) hper5 hinj5
    hV hE hFF hlf hb (fun v w hvw hvne => hd v w hvw (by rw [← hvv0, ← hvv1]; exact hvne))
    (by rw [hvv0, hvv1]; exact hv0) (by rw [hvv0, hvv1]; exact hw0)
    (fun v w hvw hvin hwv hvne => hne v w hvw hvin hwv hvne)

/-- **zithlqn a_pro worker (wave la27-zithlqn-w1).** The pro-edge band is
anchored at an (unordered) cycle position: parameterise the fan, locate the
edge inside the cycle image, split by orientation, and re-index the witness
by `zithlqnRot_w1` so that the anchor sits at positions 0/1. `c2` is the
non-edge band demanded by the supplied case lemma (`sqrt 8` for the quad,
`2 * h0` for the pentagon wrapper). -/
private theorem zithlqnPro_w1 (h : ∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv →
    0 ≤ taustarV39 s vv)
    (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (k : ℕ) (d : ℝ) (c1 c2 : ℝ) (s : ScsV39)
    (hlf : ConvexLocalFan V E FF) (hp : Kepler.Packing V) (hb : V ⊆ ballAnnulus)
    (hc : V.ncard = k) (h3 : 3 ≤ V.ncard) (hk3 : 3 < k)
    (hne : ∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → c2 ≤ dist v w)
    (hcase : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) (vv : ℕ → V3) (s : ScsV39)
      (v0 w0 : V3), ConvexLocalFan V E FF → Kepler.Packing V → V ⊆ ballAnnulus →
      V.ncard = k →
      (∀ v w : V3, v ≠ w → v ∈ V → w ∈ V → {v, w} ∉ E → c2 ≤ dist v w) →
      (∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({v0, w0} : Set V3) →
        2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
      ({v0, w0} : Set V3) ∈ E → 2 * h0 ≤ dist v0 w0 → dist v0 w0 ≤ Real.sqrt 8 →
      s = mkUnadornedV39 k d (aPro_p25 k (2 * h0) 2 c1)
        (aPro_p25 k (Real.sqrt 8) (2 * h0) 6) →
      (∀ i, vv (i % V.ncard) = vv i) →
      (∀ i j, vv i = vv j → i % V.ncard = j % V.ncard) →
      (Set.range vv : Set V3) = V →
      (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E →
      (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF →
      vv 0 = v0 → vv 1 = w0 → BBsV39 s vv)
    (hmem : s ∈ sInitListV39)
    (hseq : s = mkUnadornedV39 k d (aPro_p25 k (2 * h0) 2 c1)
      (aPro_p25 k (Real.sqrt 8) (2 * h0) 6))
    (hsd : s.d = d)
    (vv : ℕ → V3)
    (hper : ∀ i, vv i = vv (i % V.ncard)) (hinj : ∀ i j, vv i = vv j → i % V.ncard = j % V.ncard)
    (hV : (Set.range vv : Set V3) = V)
    (hE : (Set.range fun i => {vv i, vv (i + 1)} : Set (Set V3)) = E)
    (hFF : (Set.range fun i => (vv i, vv (i + 1)) : Set (V3 × V3)) = FF)
    (p q : V3)
    (hband : ∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({p, q} : Set V3) →
      2 ≤ dist v w ∧ dist v w ≤ 2 * h0)
    (he : ({p, q} : Set V3) ∈ E)
    (hv0 : 2 * h0 ≤ dist p q) (hw0 : dist p q ≤ Real.sqrt 8) :
    d ≤ tauFun V E FF := by
  have hpos : (0:ℝ) < 2 * h0 := by norm_num [h0]
  have hper' : ∀ i, vv (i % V.ncard) = vv i := fun i => (hper i).symm
  obtain ⟨i0, hi0⟩ := Set.mem_range.mp
    (show ({p, q} : Set V3) ∈
      Set.range (fun i => ({vv i, vv (i + 1)} : Set V3)) from by rw [hE]; exact he)
  obtain ⟨rot1, rot2, rotV, rotE, rotP⟩ :=
    zithlqnRot_w1 V.ncard vv i0 (by omega) hper' hinj
  have hswap : ({q, p} : Set V3) = ({p, q} : Set V3) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hpne : vv i0 ≠ vv (i0 + 1) := by
    intro hEq
    rw [hEq] at hi0
    have hsub : ∀ z : V3, z ∈ ({p, q} : Set V3) → z = vv (i0 + 1) := by
      intro z hz
      rw [← hi0] at hz
      simpa using hz
    rw [(hsub p (by simp)).trans (hsub q (by simp)).symm, dist_self] at hv0
    linarith
  have hsplit : (vv i0 = p ∧ vv (i0 + 1) = q) ∨ (vv i0 = q ∧ vv (i0 + 1) = p) := by
    have hmem2 : ∀ z : V3, z ∈ ({vv i0, vv (i0 + 1)} : Set V3) → z ∈ ({p, q} : Set V3) := by
      intro z hz
      rw [hi0] at hz
      exact hz
    have m1 : vv i0 ∈ ({p, q} : Set V3) := hmem2 _ (by simp)
    have m2 : vv (i0 + 1) ∈ ({p, q} : Set V3) := hmem2 _ (by simp)
    rcases Set.mem_insert_iff.mp m1 with r1 | r1 <;>
      rcases Set.mem_insert_iff.mp m2 with r2 | r2
    · exact absurd (r1.trans r2.symm) hpne
    · exact Or.inl ⟨r1, r2⟩
    · exact Or.inr ⟨r1, r2⟩
    · exact absurd (r1.trans r2.symm) hpne
  have core : ∀ a b : V3,
      (∀ v w : V3, {v, w} ∈ E → {v, w} ≠ ({a, b} : Set V3) →
        2 ≤ dist v w ∧ dist v w ≤ 2 * h0) →
      ({a, b} : Set V3) ∈ E → 2 * h0 ≤ dist a b → dist a b ≤ Real.sqrt 8 →
      vv i0 = a → vv (i0 + 1) = b → d ≤ tauFun V E FF := by
    intro a b hband he' hva hvb r1 r2
    have hsk : s.k = k := by rw [hseq]; rfl
    have hBB : BBsV39 s (fun m => vv (m + i0)) :=
      hcase V E FF (fun m => vv (m + i0)) s a b hlf hp hb hc hne hband he' hva hvb hseq
        rot1 rot2 (rotV.trans hV) (rotE.trans hE) (rotP.trans hFF)
        (by rw [Nat.zero_add i0]; exact r1) (by rw [Nat.add_comm 1 i0]; exact r2)
    have hts : 0 ≤ taustarV39 s (fun m => vv (m + i0)) := h s hmem _ hBB
    simp only [taustarV39] at hts
    rw [if_neg (by rw [hsk]; omega)] at hts
    rw [rotV, rotE, rotP, hV, hE, hFF,
      dsv_scs_init_p25 s hmem (fun m => vv (m + i0)), hsd] at hts
    linarith
  rcases hsplit with ⟨r1, r2⟩ | ⟨r1, r2⟩
  · exact core p q hband he hv0 hw0 r1 r2
  · refine core q p ?_ ?_ ?_ ?_ r1 r2
    · intro v w hvw hvne
      refine hband v w hvw ?_
      intro hEq
      apply hvne
      rw [hEq, hswap]
    · rw [hswap]; exact he
    · rw [dist_comm]; exact hv0
    · rw [dist_comm]; exact hw0

/-- HOL `ZITHLQN` (ZITHLQN.hl:2465): the final registry arrow, assembled in
place (wave la27-zithlqn-w1) from the Section-A realisation kit:
`exists_vv_p25` parameterises each fan, the eight `ZITHLQN_CASE_*` value
tables realise the corresponding initial system, `exists_vv3_p25` serves the
triangle item, and `zithlqnStd_w1`/`zithlqnPro_w1` do the per-case wiring
(the two `a_pro` cases via the rotation kit instead of HOL's `exists_vv_FF`,
which is not consumed any more). Statement verbatim; the only inherited root
is `exists_vv_p25`'s own `sorryAx` (the corpus-blocked `rhoNode1`
dart-cycle enumerator). -/
theorem ZITHLQN_p25 (h : ∀ s ∈ sInitListV39, ∀ vv : ℕ → V3, BBsV39 s vv →
    0 ≤ taustarV39 s vv) : JEJTVGB_assume_v39 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- JEJTVGB_std_concl (dTame ncard ≤ tauFun, ncard ∈ {4,5,6})
    intro V E FF hlf hp hb h4 h6 hne hd
    rcases (by omega : V.ncard = 4 ∨ V.ncard = 5 ∨ V.ncard = 6) with hk | hk | hk
    · rw [hk]
      refine zithlqnStd_w1 h V E FF 4 (dTame 4)
        (mkUnadornedV39 4 (dTame 4) (csAdj 4 2 (2 * h0)) (csAdj 4 (2 * h0) 6))
        hlf hp hb (by omega) (by omega) hk (by omega) hne hd
        ZITHLQN_CASE_4_p25 (zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inl rfl)))) rfl rfl
    · rw [hk]
      refine zithlqnStd_w1 h V E FF 5 (dTame 5)
        (mkUnadornedV39 5 (dTame 5) (csAdj 5 2 (2 * h0)) (csAdj 5 (2 * h0) 6))
        hlf hp hb (by omega) (by omega) hk (by omega) hne hd
        ZITHLQN_CASE_5_p25 (zithlqn_mem_w1 _ (Or.inr (Or.inl rfl))) rfl rfl
    · rw [hk]
      refine zithlqnStd_w1 h V E FF 6 (dTame 6)
        (mkUnadornedV39 6 (dTame 6) (csAdj 6 2 (2 * h0)) (csAdj 6 (2 * h0) 6))
        hlf hp hb (by omega) (by omega) hk (by omega) hne hd
        ZITHLQN_CASE_6_p25 (zithlqn_mem_w1 _ (Or.inl rfl)) rfl rfl
  · -- JEJTVGB_std3_concl (0 ≤ tau3 v1 v2 v3)
    intro v1 v2 v3 hn1 hn2 hn3 hm1 hm2 hm3 hd12 hd13 hd23 he12 he13 he23
    set vv : ℕ → V3 := fun i => if i % 3 = 0 then v1 else if i % 3 = 1 then v2 else v3
    have hvv : ∀ i, vv i = if i % 3 = 0 then v1 else if i % 3 = 1 then v2 else v3 :=
      fun i => rfl
    obtain ⟨hper, hball, hc, hd'⟩ :=
      exists_vv3_p25 v1 v2 v3 vv (Set.range vv : Set V3)
        (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
        (Set.range fun i => ((vv i, vv (i + 1)) : V3 × V3))
        hn1 hn2 hn3 hm1 hm2 hm3 hd12 hd13 hd23 he12 he13 he23 hvv rfl rfl rfl
    have hBB : BBsV39 (mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)) vv :=
      ZITHLQN_CASE_3_p25 (Set.range vv : Set V3)
        (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
        (Set.range fun i => ((vv i, vv (i + 1)) : V3 × V3)) vv _ hball hc hd' rfl hper rfl rfl rfl
    have hmem :
        mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) ∈ sInitListV39 :=
      zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hts : 0 ≤ taustarV39 (mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0))
        (csAdj 3 (2 * h0) 6)) vv := h _ hmem vv hBB
    rw [taustarV39, if_pos (by decide)] at hts
    have hdd : (mkUnadornedV39 3 (dTame 3) (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6)).d = 0 := rfl
    rw [dsv_scs_init_p25 _ hmem vv, hdd] at hts
    have e0 : vv 0 = v1 := by rw [hvv 0]; simp
    have e1 : vv 1 = v2 := by rw [hvv 1]; simp
    have e2 : vv 2 = v3 := by rw [hvv 2]; simp
    rw [e0, e1, e2] at hts
    linarith
  · -- JEJTVGB_pent_diag_concl (0.616 ≤ tauFun, sqrt8-diagonal pentagon)
    intro V E FF hlf hp hb hc hne hd
    obtain ⟨vv, hper, hinj, hV, hE, hFF⟩ :=
      exists_vv_p25 V E FF hlf hp hb (by omega) (by omega)
    have hBB := ZITHLQN_CASE_5_sqrt8_p25 V E FF vv
      (mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6)) hlf hp hb hc hne hd
      rfl (fun i => (hper i).symm) hinj hV hE hFF
    have hmem :
        mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6) ∈ sInitListV39 :=
      zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have hts : 0 ≤ taustarV39 (mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8))
        (csAdj 5 (2 * h0) 6)) vv := h _ hmem vv hBB
    rw [taustarV39, if_neg (by decide)] at hts
    rw [hV, hE, hFF, dsv_scs_init_p25 _ hmem vv] at hts
    have hdd : (mkUnadornedV39 5 0.616 (csAdj 5 2 (Real.sqrt 8)) (csAdj 5 (2 * h0) 6)).d = 0.616 :=
      rfl
    rw [hdd] at hts
    linarith
  · -- JEJTVGB_pent_pro_concl (0.616 ≤ tauFun, a_pro pentagon)
    intro V E FF hlf hp hb hc hne hex
    obtain ⟨v0, w0, hband, he, hv0, hw0⟩ := hex
    obtain ⟨vv, hper, hinj, hV, hE, hFF⟩ :=
      exists_vv_p25 V E FF hlf hp hb (by omega) (by omega)
    refine zithlqnPro_w1 h V E FF 5 0.616 (2 * h0) (2 * h0)
      (mkUnadornedV39 5 0.616 (aPro_p25 5 (2 * h0) 2 (2 * h0))
        (aPro_p25 5 (Real.sqrt 8) (2 * h0) 6))
      hlf hp hb hc (by omega) (by omega) hne zithlqnCase5Pro2h0_w1
      (zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
      rfl rfl vv hper hinj hV hE hFF v0 w0 hband he hv0 hw0
  · -- JEJTVGB_quad_pro_concl (0.477 ≤ tauFun, a_pro quad)
    intro V E FF hlf hp hb hc hne hex
    obtain ⟨v0, w0, hband, he, hv0, hw0⟩ := hex
    obtain ⟨vv, hper, hinj, hV, hE, hFF⟩ :=
      exists_vv_p25 V E FF hlf hp hb (by omega) (by omega)
    refine zithlqnPro_w1 h V E FF 4 0.477 (Real.sqrt 8) (Real.sqrt 8)
      (mkUnadornedV39 4 0.477 (aPro_p25 4 (2 * h0) 2 (Real.sqrt 8))
        (aPro_p25 4 (Real.sqrt 8) (2 * h0) 6))
      hlf hp hb hc (by omega) (by omega) hne ZITHLQN_CASE_4_pro_cs_p25
      (zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
      rfl rfl vv hper hinj hV hE hFF v0 w0 hband he hv0 hw0
  · -- JEJTVGB_quad_diag_concl (0.467 ≤ tauFun, &3-diagonal quad)
    intro V E FF hlf hp hb hc hne hd
    obtain ⟨vv, hper, hinj, hV, hE, hFF⟩ :=
      exists_vv_p25 V E FF hlf hp hb (by omega) (by omega)
    have hBB := ZITHLQN_CASE_4_3_p25 V E FF vv
      (mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)) hlf hp hb hc hne hd
      rfl (fun i => (hper i).symm) hinj hV hE hFF
    have hmem :
        mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6) ∈ sInitListV39 :=
      zithlqn_mem_w1 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    have hts : 0 ≤ taustarV39 (mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)) vv :=
      h _ hmem vv hBB
    rw [taustarV39, if_neg (by decide)] at hts
    rw [hV, hE, hFF, dsv_scs_init_p25 _ hmem vv] at hts
    have hdd : (mkUnadornedV39 4 0.467 (csAdj 4 2 3) (csAdj 4 (2 * h0) 6)).d = 0.467 := rfl
    rw [hdd] at hts
    linarith

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

private theorem w5asswp_atn2_eq_arctan {x y : ℝ} (hx : 0 < x) :
    atn2 x y = Real.arctan (y / x) := by
  rw [atn2]
  split_ifs with hb1 hb2 hb3
  · rfl
  · have hz : 0 < y / x := div_pos hb2 hx
    have hinv := Real.arctan_inv_of_pos hz
    rw [inv_div] at hinv
    linarith
  · have hy0 : y < 0 := hb3
    have hz : y / x < 0 := div_neg_of_neg_of_pos hy0 hx
    have hinv := Real.arctan_inv_of_neg hz
    rw [inv_div] at hinv
    linarith
  · have hy0 : y = 0 := le_antisymm (by linarith) (by linarith)
    rw [hy0] at hb1
    simp at hb1
    exact absurd hx (not_lt.mpr hb1)

private theorem w5asswp_cos_pi_half_add (w : ℝ) :
    Real.cos (Real.pi / 2 + w) = -Real.sin w := by
  rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

private theorem w5asswp_arctan_mem (z : ℝ) :
    Real.arctan z < Real.pi / 2 ∧ -Real.pi / 2 < Real.arctan z := by
  constructor
  · exact Real.arctan_lt_pi_div_two z
  · have h := Real.arctan_lt_pi_div_two (-z)
    rw [Real.arctan_neg] at h
    linarith

private theorem w5asswp_arclength222_eq_acos {c : ℝ} (hc2 : 2 ≤ c) (hc4 : c < 4) :
    arcLength 2 2 c = Real.arccos ((8 - c * c) / 8) := by
  have hc0 : (0:ℝ) ≤ c := by linarith
  have hpos : (0:ℝ) < 16 - c * c := by nlinarith
  have hup : upsX (2 * 2) (2 * 2) (c * c) = c ^ 2 * (16 - c * c) := by
    simp only [upsX]
    ring
  have hx : Real.sqrt (upsX (2 * 2) (2 * 2) (c * c)) = c * Real.sqrt (16 - c * c) := by
    rw [hup, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0]
  have hxpos : (0:ℝ) < c * Real.sqrt (16 - c * c) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr hpos)
  have hxne : c * Real.sqrt (16 - c * c) ≠ 0 := ne_of_gt hxpos
  have hX2Y2 : (c * Real.sqrt (16 - c * c)) ^ 2 + (c * c - 8) ^ 2 = 64 := by
    have hsq : (c * Real.sqrt (16 - c * c)) ^ 2 = c ^ 2 * (16 - c * c) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith : (0:ℝ) ≤ 16 - c * c)]
    rw [hsq]
    ring
  have hdL : arcLength 2 2 c
      = Real.pi / 2 + atn2 (Real.sqrt (upsX (2 * 2) (2 * 2) (c * c)))
          (c * c - 2 * 2 - 2 * 2) := rfl
  have hsimp : (c * c - 2 * 2 - 2 * 2 : ℝ) = c * c - 8 := by ring
  rw [hdL, hsimp, hx, w5asswp_atn2_eq_arctan hxpos]
  refine (Real.arccos_eq_of_eq_cos ?_ ?_ ?_).symm
  · obtain ⟨_, hlo⟩ :=
      w5asswp_arctan_mem ((c * c - 8) / (c * Real.sqrt (16 - c * c)))
    linarith [Real.pi_pos]
  · obtain ⟨hhi, _⟩ :=
      w5asswp_arctan_mem ((c * c - 8) / (c * Real.sqrt (16 - c * c)))
    linarith [Real.pi_pos]
  · rw [w5asswp_cos_pi_half_add, Real.sin_arctan]
    have hsq0 : Real.sqrt (16 - c * c) ≠ 0 :=
      fun he => absurd (Real.sqrt_pos.mpr hpos) (by rw [he]; simp)
    have hsq0b : Real.sqrt (16 - c ^ 2) ≠ 0 := by rw [pow_two]; exact hsq0
    have hsq2 : (c * Real.sqrt (16 - c * c)) ^ 2 ≠ 0 :=
      fun he => hxne (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp he)
    have hsq1 : (1:ℝ) + ((c * c - 8) / (c * Real.sqrt (16 - c * c))) ^ 2
        = 64 / (c * Real.sqrt (16 - c * c)) ^ 2 := by
      rw [div_pow, ← div_self hsq2, ← add_div, hX2Y2]
    rw [hsq1, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 64),
      show (Real.sqrt 64 : ℝ) = 8 from by norm_num,
      Real.sqrt_sq (by nlinarith : (0:ℝ) ≤ c * Real.sqrt (16 - c * c))]
    rw [show ((c * c - 8) / (c * Real.sqrt (16 - c * c))
          / (8 / (c * Real.sqrt (16 - c * c))) : ℝ) = (c * c - 8) / 8
      from by field_simp [hsq0b],
      show (8:ℝ) - c * c = -(c * c - 8) from by ring, neg_div]

private theorem w5asswp_xrr_eq (A C : V3) (hA : A ≠ 0) (hC : C ≠ 0) :
    xrr (‖A‖) (‖C‖) (dist A C) = 8 * (1 - Real.cos (arcV 0 A C)) := by
  have hAn : (0:ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  have hCn : (0:ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hratio : -(1:ℝ) ≤ inner ℝ A C / (‖A‖ * ‖C‖) ∧ inner ℝ A C / (‖A‖ * ‖C‖) ≤ 1 := by
    have h := abs_real_inner_div_norm_mul_norm_le_one A C
    rw [abs_le] at h
    exact h
  have harc : arcV 0 A C = Real.arccos (inner ℝ A C / (‖A‖ * ‖C‖)) := by
    simp only [arcV, dist_zero_right, sub_zero, WithLp.ofLp_zero, sub_zero,
      Kepler.Geom.inner_eq_dot]
  have hcos : Real.cos (arcV 0 A C) = inner ℝ A C / (‖A‖ * ‖C‖) := by
    rw [harc, Real.cos_arccos hratio.1 hratio.2]
  have hdist : dist A C ^ 2 = ‖A‖ ^ 2 + ‖C‖ ^ 2 - 2 * (inner ℝ A C) := by
    rw [dist_eq_norm, norm_sub_sq_real]
    ring
  rw [hcos]
  simp only [xrr]
  have hne : ‖A‖ * ‖C‖ ≠ 0 := ne_of_gt (mul_pos hAn hCn)
  field_simp
  nlinarith [hdist]

/-- HOL `ASSWPOW` (VASYYAU.hl:154): the `xrr ≤ #15.53` diagonal bound on a
basic `k = 4` system (the numeric content is exactly the
`arclength_lt_1553_p25` arcLength constant above).  Faithful twin of the
LocalAuto1 registry statement `ASSWPOW_concl` (appendix.hl:1452; statement
verbatim).  PROVED here via the origin-angle route: with `A = v i`,
`B = v (i+1)`, `C = v (i+2)` all in the ball annulus (`MMs` gives `BBs`) and
both short edges `≤ 2 h0` with lower bound `2`, `OIQKKEP_concl` bounds each
of `arcV 0 A B` / `arcV 0 B C` by `arcLength 2 2 (2 h0)`; the vector angle
triangle inequality `InnerProductGeometry.angle_le_angle_add_angle` gives
`arcV 0 A C ≤ 2 * arcLength 2 2 (2 h0) < arcLength 2 2 (sqrt 15.53)` by
`arclength_lt_1553_p25`, and `xrr = 8 (1 - cos (arcV 0 A C))` closes the
numeric end.  The twin is an INDEPENDENT proof piece — NOT derived from the
registry `ASSWPOW_concl` — so the LocalConcl wiring is not a (b)-style
cycle. -/
theorem ASSWPOW_p25 (s : ScsV39) (v : ℕ → V3) (i : ℕ) (his : isScsV39 s)
    (hv : v ∈ MMsV39 s) (hk : s.k = 4) (hbasic : scsBasicV39 s)
    (hb1 : s.b i (i + 1) ≤ 2 * h0) (hb2 : s.b (i + 1) (i + 2) ≤ 2 * h0) :
    xrr (norm (v i)) (norm (v (i + 2))) (dist (v i) (v (i + 2))) ≤ 15.53 := by
  obtain ⟨hd, hk3, hk6, -, -, -, -, hpa, -, -, -, -, hsym, hch, hdiag0, hdiag,
    hb3, hbc, -, -, hcard⟩ := his
  have hbb : BBsV39 s v := hv.1.1.1
  have hann : ∀ n, v n ∈ ballAnnulus := fun n => hbb.1 ⟨n, rfl⟩
  have hpa4 : Periodic2 s.a 4 := hk ▸ hpa
  have hdiag4 : ∀ i j, i < 4 ∧ j < 4 ∧ i ≠ j → 2 ≤ s.a i j := hk ▸ hdiag
  -- lower/upper bounds on the two short edges
  have hlow1 : (2:ℝ) ≤ dist (v i) (v (i + 1)) := by
    have h4a : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h4b : (i + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hne : i % 4 ≠ (i + 1) % 4 := succ_mod_ne_p25 (k := 4) (by norm_num) i
    have ha2 : 2 ≤ s.a i (i + 1) := by
      rw [← periodic2_mod_eq_p25 hpa4 i (i + 1)]
      exact hdiag4 _ _ ⟨h4a, h4b, hne⟩
    exact ha2.trans (hbb.2.2.1 i (i + 1)).1
  have hlow2 : (2:ℝ) ≤ dist (v (i + 1)) (v (i + 2)) := by
    have h4a : (i + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h4b : (i + 2) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hne : (i + 1) % 4 ≠ (i + 2) % 4 := by
      have h := succ_mod_ne_p25 (k := 4) (by norm_num) (i + 1)
      simpa [show (i + 1) + 1 = i + 2 by ring] using h
    have ha2 : 2 ≤ s.a (i + 1) (i + 2) := by
      rw [← periodic2_mod_eq_p25 hpa4 (i + 1) (i + 2)]
      exact hdiag4 _ _ ⟨h4a, h4b, hne⟩
    exact ha2.trans (hbb.2.2.1 (i + 1) (i + 2)).1
  have hd1 : dist (v i) (v (i + 1)) ≤ 2 * h0 := (hbb.2.2.1 i (i + 1)).2.trans hb1
  have hd2 : dist (v (i + 1)) (v (i + 2)) ≤ 2 * h0 :=
    (hbb.2.2.1 (i + 1) (i + 2)).2.trans hb2
  have hc4 : 2 * h0 < 4 := by
    have hh0 : h0 = 1.26 := rfl
    rw [hh0]; norm_num
  have hθ1 := OIQKKEP_concl (v i) (v (i + 1)) (2 * h0) (hann i) (hann (i + 1))
    hc4 hlow1 hd1
  have hθ2 := OIQKKEP_concl (v (i + 1)) (v (i + 2)) (2 * h0) (hann (i + 1))
    (hann (i + 2)) hc4 hlow2 hd2
  have hsum : arcV 0 (v i) (v (i + 2)) ≤ 2 * arcLength 2 2 (2 * h0) := by
    have htri : arcV 0 (v i) (v (i + 2)) ≤
        arcV 0 (v i) (v (i + 1)) + arcV 0 (v (i + 1)) (v (i + 2)) := by
      have h := InnerProductGeometry.angle_le_angle_add_angle (v i) (v (i + 1)) (v (i + 2))
      simpa [arcV, InnerProductGeometry.angle, Kepler.Geom.inner_eq_dot, dist_eq_norm]
        using h
    linarith
  have hlt : arcV 0 (v i) (v (i + 2)) < arcLength 2 2 (Real.sqrt 15.53) :=
    lt_of_le_of_lt hsum arclength_lt_1553_p25
  -- numeric endpoint
  have hsq : Real.sqrt 15.53 ^ 2 = (15.53 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn := Real.sqrt_nonneg (15.53 : ℝ)
  have hc2 : (2:ℝ) ≤ Real.sqrt 15.53 := by nlinarith
  have hc4' : Real.sqrt 15.53 < 4 := by nlinarith
  have hval : arcLength 2 2 (Real.sqrt 15.53) = Real.arccos ((8 - 15.53) / 8) := by
    rw [w5asswp_arclength222_eq_acos hc2 hc4']
    congr 1
    nlinarith [hsq]
  have hcos0 : Real.cos (arcLength 2 2 (Real.sqrt 15.53)) = (8 - 15.53) / 8 := by
    rw [hval, Real.cos_arccos (by norm_num) (by norm_num)]
  have hlepi : arcLength 2 2 (Real.sqrt 15.53) ≤ Real.pi := by
    rw [hval]; exact Real.arccos_le_pi _
  have hcos_gt : (8 - 15.53) / 8 < Real.cos (arcV 0 (v i) (v (i + 2))) := by
    rw [← hcos0]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) hlepi hlt
  -- nonzero norms
  have hann2 : ∀ n, (2:ℝ) ≤ ‖v n‖ := by
    intro n
    have h := hann n
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_self] at h
    rw [← dist_zero_right]
    exact le_of_not_gt h.2
  have hA : v i ≠ 0 := by
    intro h
    have := hann2 i
    rw [h, norm_zero] at this
    norm_num at this
  have hC : v (i + 2) ≠ 0 := by
    intro h
    have := hann2 (i + 2)
    rw [h, norm_zero] at this
    norm_num at this
  have hxrr := w5asswp_xrr_eq (v i) (v (i + 2)) hA hC
  rw [hxrr]
  nlinarith

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
mk_imp (NEHXMWH_concl, TUAPYYU_concl))`. DISCHARGES: HOL derives the two
`interior_angle1 ... < pi` antecedent blocks (the `(p+3)` block feeds
NEHXMWH1 via BZQNDMN, the `(p+2)` block feeds NEHXMWH) from
`¬scsIsStr p ∧ ¬scsIsStr (p+1)` through the azim machinery
`MMS_IMP_BBS` + `BBS_IMP_CONVEX_LOCAL_FAN` (fan from BBs) +
`BB_RHO_NODE_IVS` + `Local_lemmas.IN_V_IMP_AZIM_LESS_PI`, then applies
`NOT_MOD_4_CASES`/`NOT_MOD_4_CASES_3`. None of that is ported here, and the
two plug-ins `LocalAuto23.NEHXMWH_p23` / `BZQNDMN_p23` are themselves still
`sorry` (need the same kit + terminal registry 5541487347). A vacuous
re-export `fun _ _ => TUAPYYU_p25` exists but is the LocalConcl-documented
circular pattern (TUAPYYU_concl is a LocalAuto1 registry `sorry`), so left
as a genuine `sorry`. NEEDS: the interior-angle→azim kit (JOTSWIX/
Local_lemmas), then the LocalAuto23 twins. -/
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
theorem WKZZEEH_p25 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h1 : ¬scsIsStr s v p) (h2 : ¬scsIsStr s v (p + 1))
    (h3 : ¬scsIsStr s v (p + 3)) :
    ¬(dist (v p) (v (p + 3)) = cstab ∧ dist (v p) (v (p + 1)) = cstab) :=
  WKZZEEH_concl h s v p his hbasic hk hv hdiag hval h1 h2 h3

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
theorem PWEIWBZ_p25 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (ha : s.a p (p + 1) = 2) : dist (v p) (v (p + 1)) = 2 :=
  PWEIWBZ_concl h s v p his hbasic hk hv hdiag hval ha

/-- HOL `VASYYAU` (VASYYAU.hl:2366): the master str-case conclusion.
Re-export of the LocalAuto1 registry twin `VASYYAU_concl`. -/
theorem VASYYAU_p25 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (hstr : scsIsStr s v p) :
    dist (v p) (v (p + 1)) = s.a p (p + 1) ∧ dist (v p) (v (p + 3)) = s.a p (p + 3) :=
  VASYYAU_concl h s v p his hbasic hk hv hdiag hval hstr

/-- HOL `YEBWJNG` (VASYYAU.hl:292). Re-export of the LocalAuto1 registry
twin `YEBWJNG_concl`. -/
theorem YEBWJNG_p25 (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h1 : ¬scsIsStr s v p) (h2 : ¬scsIsStr s v (p + 1)) (ha : s.a p (p + 1) = 2) :
    dist (v p) (v (p + 1)) = 2 :=
  YEBWJNG_concl h s v p his hbasic hk hv hdiag hval h1 h2 ha
