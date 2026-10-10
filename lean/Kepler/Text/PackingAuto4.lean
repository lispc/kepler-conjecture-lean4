/-
Kepler Text / PackingAuto4 — skeleton port of two HOL Light sources of the
Flyspeck packing chapter:

  * `scripts/packing/OXLZLEZ2.hl` (4522 lines): the compressed-model
    ("Carmichael-style") case analysis. 39 theorems over the `cc_*_v11`
    compressed-cell model, culminating in the D-case contradiction
    `GRHIDFA` (a negative `sum cc_gg_v11` forces a contradiction).
  * `scripts/packing/bump.hl` (1274 lines): the `beta_bump` definition and
    its calculus (57 theorems, `bump.hl:10` "REDO THE beta_bump"). The
    edge-symmetry kit: `BETA_BUMP_INVOLUTION*`, `MCELL4_EDGE_OPP`,
    `SUM_BETA_BUMP_LEMMA`, `BOUND_BETA_BUMP`.

## File map

1. Private copies (`_p4` suffix) of the `cc_*_v11` compressed-model
   definitions from `OXLZLEZ1.hl` (lines 23-136) — `-- NEEDS: PackingAuto3`
   marker: the parallel lane ports these verbatim into `PackingAuto3`; at
   merge time the `_p4` copies below are deleted and replaced by imports.
2. The    39 `OXLZLEZ2.hl` theorems (statements faithful to the HL
   `prove(_by_refinement)` goals; short arithmetic/modular ones proved,
   the case-analysis giants `sorry`ed — this is a SKELETON batch).
   2b. Public `*_v11` twins: the nine OXLZLEZ1 conclusion statements
   re-exposed over `PackingAuto3`'s public `CcV11` interface (PA3 is
   imported for this; PA3's closure is PA2/Polytope/Statement/Mathlib, so
   the co-import is clash-free), verbatim to PA3's `*_concl` rows — this
   is what lets `PackingConcl` discharge its Auto3 family.
3. `betaBump` (HL `beta_bump_v1`, `pack_defs.hl:180-187`) — see its
   docstring for the integral-semantics encoding note — plus the `bump.hl`
   theorem kit.

## Encoding notes

* HOL `real^3` ↔ `V3` (Kepler.Geom); `packing V` ↔ `Packing`
  (Kepler.Statement, definitional to `Set V3` since both abbreviate
  `EuclideanSpace ℝ (Fin 3)`); `NULLSET` ↔ `nullSet`, `radV`, `barV`,
  `mcell`, `VX`, `edgeX`, `critical_edgeX`, `subcritical_edgeX`, `bump`,
  `h0/hminus/hplus`, `set_of_list`, `truncate_simplex` all come from
  `Kepler.Text.PackingAuto2` (the verbatim `pack_defs.hl` port; merge-note
  precedent: import instead of re-copy).
* `sum (0..n) f` ↔ `Finset.sum (Finset.Icc 0 n) f`; `sum S f` over a set ↔
  `setSum`; `CARD s` ↔ `Nat.card`.
* beta_bump encoding (see `betaBump` docstring): the historical
  integral-over-Rogers-cones `beta_bump` was REDONE in flyspeck as the
  closed-form `beta_bump_v1 = bump (radV e) - bump (radV e')`; `bump h =
  0.005 * (1 - (h-h0)^2/(hplus-h0)^2)` is a quadratic in `hl`, so all its
  calculus ultimately rests on `sqrt`/quadratic inequalities; the cones
  (`rcone_ge`/`rcone_gt`, PackingAuto2) survive only inside the `mcell`
  layer.
* HL bool-valued index functions (`cc_*_v11 cc : num->bool`) are ported as
  `ℕ → Prop` predicates (`= true` on the underlying `Bool` array); HL
  `periodic` on bool functions becomes `periodicPropP4` (Iff), on real
  functions `periodicP4` (Eq).
-/

-- NOTE: `Kepler.Text.PackingAuto1` is NOT imported: it and PackingAuto2
-- both define `Kepler.Text.saturated` (PackingAuto1:voronoi chain vs
-- PackingAuto2:263 `pack_defs` port), and co-importing fails at the
-- environment level. Every primitive the bump.hl kit needs (`saturated`,
-- `Packing` via Kepler.Statement, the `pack_defs` cell kit) is provided by
-- PackingAuto2; PackingAuto1's voronoi/measure chain is not referenced by
-- any statement in this file.
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto3
-- AJRIPQN-port: the `LEPJBDJ`/`LEPJBDJ_0` pair (PA11, fully proved) is the
-- missing ingredient of the `HDTFNFZ` kit (`VX V X = V ∩ X`) that the
-- bump-cluster fills below consume. PA11's import closure is
-- PA2/PA5/PA6/PA7/PA8/Polytope — it does not reach PA4, so the edge is acyclic
-- (PA4's only importer is PackingConcl).
import Kepler.Text.PackingAuto11
import Kepler.Text.Polytope
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## 1. Compressed-cell model (`OXLZLEZ1.hl` private `_p4` copies) -/
-- NEEDS: PackingAuto3 (parallel lane ports `cc_*_v11` verbatim; delete the
-- `_p4` copies below and import at merge time)

/-- HL `cc_v11` (OXLZLEZ1.hl:27, type definition): an abstract record
pairing the real array `[azim; gg; gg3a; gg3b]`, the bool array
`[subcrit; crit; supercrit; small; small_eta; 4cell]` and the cycle
cardinality. -/
private structure CC4P4 where
  reals : Fin 4 → ℕ → ℝ
  bools : Fin 6 → ℕ → Bool
  cardA : ℕ

/-- HL `cc_card_v11` (OXLZLEZ1.hl:33). -/
private def ccCardP4 (cc : CC4P4) : ℕ := cc.cardA

/-- HL `cc_azim_v11` (OXLZLEZ1.hl:35): `EL 0 (cc_real_v11 cc) i`. -/
private def ccAzimP4 (cc : CC4P4) : ℕ → ℝ := cc.reals 0

/-- HL `cc_gg_v11` (OXLZLEZ1.hl:36): `EL 1 (cc_real_v11 cc) i`. -/
private def ccGgP4 (cc : CC4P4) : ℕ → ℝ := cc.reals 1

/-- HL `cc_gg3a_v11` (OXLZLEZ1.hl:37): `EL 2 (cc_real_v11 cc) i`. -/
private def ccGg3aP4 (cc : CC4P4) : ℕ → ℝ := cc.reals 2

/-- HL `cc_gg3b_v11` (OXLZLEZ1.hl:38): `EL 3 (cc_real_v11 cc) i`. -/
private def ccGg3bP4 (cc : CC4P4) : ℕ → ℝ := cc.reals 3

/-- HL `cc_subcrit_v11` (OXLZLEZ1.hl:41): `EL 0 (cc_bool_v11 cc) i`. -/
private abbrev ccSubcritP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 0 i = true

/-- HL `cc_crit_v11` (OXLZLEZ1.hl:42). -/
private abbrev ccCritP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 1 i = true

/-- HL `cc_supercrit_v11` (OXLZLEZ1.hl:43). -/
private abbrev ccSupercritP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 2 i = true

/-- HL `cc_small_v11` (OXLZLEZ1.hl:44). -/
private abbrev ccSmallP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 3 i = true

/-- HL `cc_small_eta_v11` (OXLZLEZ1.hl:45). -/
private abbrev ccSmallEtaP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 4 i = true

/-- HL `cc_4cell_v11` (OXLZLEZ1.hl:46). -/
private abbrev cc4CellP4 (cc : CC4P4) : ℕ → Prop := fun i => cc.bools 5 i = true

/-- HL `cc_hassmall_v11` (OXLZLEZ1.hl:49-50). -/
private abbrev ccHasSmallP4 (cc : CC4P4) (i : ℕ) : Prop :=
  ccSmallP4 cc i ∧ ccSmallP4 cc (i + 1)

/-- HL `cc_qu_v11` (OXLZLEZ1.hl:52). -/
private abbrev ccQuP4 (cc : CC4P4) (i : ℕ) : Prop :=
  ccHasSmallP4 cc i ∧ cc4CellP4 cc i ∧ ccSubcritP4 cc i

/-- HL `cc_qx_v11` (OXLZLEZ1.hl:53). -/
private abbrev ccQxP4 (cc : CC4P4) (i : ℕ) : Prop := cc4CellP4 cc i ∧ ¬ccQuP4 cc i

/-- HL `cc_qy_v11` (OXLZLEZ1.hl:54). -/
private abbrev ccQyP4 (cc : CC4P4) (i : ℕ) : Prop := ¬cc4CellP4 cc i

/-- HL `cc_size_v11` (OXLZLEZ1.hl:56-58):
`CARD {i | i IN 0..(cc_card_v11 cc - 1) /\ p i}`. -/
private noncomputable def ccSizeP4 (cc : CC4P4) (p : ℕ → Prop) : ℝ :=
  Nat.card {i : ℕ | i < ccCardP4 cc ∧ p i}

/-- HL `periodic` (OXLZLEZ1.hl:59): `periodic (f:num->A) n =
!i. f (i + n) = f i`. -/
private abbrev periodicP4 {α : Type} (f : ℕ → α) (n : ℕ) : Prop :=
  ∀ i, f (i + n) = f i

/-- HL `periodic` at bool functions (`Iff` rendering of bool equality). -/
private abbrev periodicPropP4 (f : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ i, (f (i + n) ↔ f i)

/-- HL `cc_bool_model_v11` (OXLZLEZ1.hl:61-77). -/
private abbrev ccBoolModelP4 (cc : CC4P4) : Prop :=
  ccCardP4 cc ≠ 0 ∧
  periodicPropP4 (ccSubcritP4 cc) (ccCardP4 cc) ∧
  periodicPropP4 (ccCritP4 cc) (ccCardP4 cc) ∧
  periodicPropP4 (ccSupercritP4 cc) (ccCardP4 cc) ∧
  periodicPropP4 (ccSmallP4 cc) (ccCardP4 cc) ∧
  periodicPropP4 (ccSmallEtaP4 cc) (ccCardP4 cc) ∧
  periodicPropP4 (cc4CellP4 cc) (ccCardP4 cc) ∧
  (∀ i, ¬(ccCritP4 cc i ∧ ccSupercritP4 cc i)) ∧
  (∀ i, ¬(ccCritP4 cc i ∧ ccSubcritP4 cc i)) ∧
  (∀ i, ¬(ccSupercritP4 cc i ∧ ccSubcritP4 cc i)) ∧
  (∀ i, cc4CellP4 cc i → ccCritP4 cc i ∨ ccSubcritP4 cc i ∨ ccSupercritP4 cc i) ∧
  (∀ i, ccSmallEtaP4 cc i → ccSmallP4 cc i)

/-- HL `cc_bool_prep_v11` (OXLZLEZ1.hl:79). -/
private abbrev ccBoolPrepP4 (cc : CC4P4) : Prop :=
  ∀ i, ccQyP4 cc i → ¬ccQyP4 cc (i + 1)

/-- HL `cc_eps` (OXLZLEZ1.hl:23). -/
private def ccEpsP4 : ℝ := 0.0057

/-- Flyspeck `a_spine5` (` sphere.hl` family, spine constants). -/
private def aSpine5P4 : ℝ := 0.0560305

/-- Flyspeck `b_spine5`. -/
private def bSpine5P4 : ℝ := -0.0445813

/-- HL `cc_real_model_v11` (OXLZLEZ1.hl:81-136): the full numeric model —
periodicity of the real arrays, the general bounds (gckb, azim_c4, angle
sum, ox3q1h), the quarter bounds (gamma_qu, fhbv2, quqy, ztg4, azim1,
gaz4, gaz6), the nonquarter 4-cell bounds (gamma_qx, g_qxd, gamma10,
gamma11, gamma8, gaz9, azim2) and the 23-cell bounds (quqy splits, cell3/
grki, pem, tew, txq). HL line comments preserved as conjunct comments. -/
private abbrev ccRealModelP4 (cc : CC4P4) : Prop :=
  periodicP4 (ccAzimP4 cc) (ccCardP4 cc) ∧
  periodicP4 (ccGgP4 cc) (ccCardP4 cc) ∧
  periodicP4 (ccGg3aP4 cc) (ccCardP4 cc) ∧
  periodicP4 (ccGg3bP4 cc) (ccCardP4 cc) ∧
  -- general bounds
  (∀ i, 0.606 ≤ ccAzimP4 cc i) ∧ -- gckb
  (∀ i, cc4CellP4 cc i → ccAzimP4 cc i < 2.8) ∧ -- azim_c4
  (Finset.sum (Finset.Icc 0 (ccCardP4 cc)) (ccAzimP4 cc) = 2 * Real.pi) ∧
  ((ccCardP4 cc = 4 ∧ ∃ i, cc4CellP4 cc i ∧ ccCritP4 cc i ∧
      ccQuP4 cc (i + 1) ∧ ccQuP4 cc (i + 2) ∧ ccQuP4 cc (i + 3)) →
    0 ≤ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc)) ∧ -- ox3q1h
  -- quarters
  (∀ i, ccQuP4 cc i → -ccEpsP4 ≤ ccGgP4 cc i) ∧ -- gamma_qu
  (∀ i, ccQuP4 cc i ∧ ¬ccSmallEtaP4 cc i → ccEpsP4 ≤ ccGgP4 cc i) ∧ -- fhbv2
  (∀ i, ccQuP4 cc i ∧ ¬ccSmallEtaP4 cc (i + 1) → ccEpsP4 ≤ ccGgP4 cc i) ∧ -- fhbv2
  (∀ i, ccQuP4 cc i ∧ ccQyP4 cc (i + 1) →
    0 ≤ ccGgP4 cc i + ccGg3aP4 cc (i + 1)) ∧ -- quqy
  (∀ i, ccQuP4 cc (i + 1) ∧ ccQyP4 cc i →
    0 ≤ ccGg3bP4 cc i + ccGgP4 cc (i + 1)) ∧ -- quqy
  (∀ i, cc4CellP4 cc i →
    aSpine5P4 + bSpine5P4 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- ztg4
  (∀ i, ccQuP4 cc i →
    -0.0659 + 0.042 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- azim1
  (∀ i, ccQuP4 cc i →
    -0.0142852 + 0.00609451 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- gaz4
  (∀ i, ccQuP4 cc i →
    0.161517 - 0.119482 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- gaz6
  -- nonquarter 4-cells
  (∀ i, ccQxP4 cc i → 0 ≤ ccGgP4 cc i) ∧ -- gamma_qx
  (∀ i, ccQxP4 cc i ∧ 2.3 < ccAzimP4 cc i → ccEpsP4 ≤ ccGgP4 cc i) ∧ -- g_qxd
  (∀ i, ccQxP4 cc i ∧ ccHasSmallP4 cc i ∧ ccQyP4 cc (i + 1) →
    ccEpsP4 ≤ ccGgP4 cc i + ccGg3aP4 cc (i + 1)) ∧ -- gamma10
  (∀ i, ccQxP4 cc (i + 1) ∧ ccHasSmallP4 cc (i + 1) ∧ ccQyP4 cc i →
    ccEpsP4 ≤ ccGg3bP4 cc i + ccGgP4 cc (i + 1)) ∧ -- gamma11
  (∀ i, ccQxP4 cc i ∧ ccSmallP4 cc i ∧ ¬ccSmallP4 cc (i + 1) →
    ccEpsP4 ≤ ccGgP4 cc i) ∧ -- gamma8
  (∀ i, ccQxP4 cc i ∧ ccSmallP4 cc (i + 1) ∧ ¬ccSmallP4 cc i →
    ccEpsP4 ≤ ccGgP4 cc i) ∧ -- gamma8
  (∀ i, ccQxP4 cc i ∧ ccHasSmallP4 cc i →
    0.213849 - 0.119482 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- gaz9
  (∀ i, ccQxP4 cc i ∧ ccHasSmallP4 cc i ∧ ccSupercritP4 cc i →
    0.00457511 + 0.00609451 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- azim2
  -- 23-cells
  (∀ i, ccQyP4 cc i → ccGg3aP4 cc i + ccGg3bP4 cc i ≤ ccGgP4 cc i) ∧
  (∀ i, ccQyP4 cc i → 0 ≤ ccGg3aP4 cc i) ∧
  (∀ i, ccQyP4 cc i → 0 ≤ ccGg3bP4 cc i) ∧
  (∀ i, ccQyP4 cc i → 0.008 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- cell3, grki
  (∀ i, ccQyP4 cc i ∧ ccSmallEtaP4 cc i ∧ ¬ccSmallEtaP4 cc (i + 1) ∧
    ccAzimP4 cc i < 1.074 →
    aSpine5P4 + bSpine5P4 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- pem
  (∀ i, ccQyP4 cc i ∧ ¬ccSmallEtaP4 cc i ∧ ccSmallEtaP4 cc (i + 1) ∧
    ccAzimP4 cc i < 1.074 →
    aSpine5P4 + bSpine5P4 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- pem
  (∀ i, ccQyP4 cc i ∧ ccSmallEtaP4 cc i ∧ ccSmallEtaP4 cc (i + 1) →
    aSpine5P4 + bSpine5P4 * ccAzimP4 cc i ≤ ccGgP4 cc i) ∧ -- tew
  (∀ i, ccQyP4 cc i ∧ ccSmallEtaP4 cc i ∧ ccSmallEtaP4 cc (i + 1) ∧
    1.946 ≤ ccAzimP4 cc i ∧ ccAzimP4 cc i ≤ 2.089 →
    3.0 * ccEpsP4 ≤ ccGgP4 cc i) -- txq

/-! ## 2. `OXLZLEZ2.hl`: the compressed-model case analysis (39 theorems)

Statements faithful to the HL goals; premises rendered as explicit
hypotheses (`ccBoolModelP4` / `ccBoolPrepP4` / `ccRealModelP4` / negative
`sum`). Proofs: the short modular/arithmetic lemmas are proved; the
case-analysis giants (`sorry`) are the fill-in work of later lanes. -/

/-- OXLZLEZ2.hl:183. -/
theorem QU_OR_QXY (cc : CC4P4) (i : ℕ) :
    ccQuP4 cc i ∨ ccQxP4 cc i ∨ ccQyP4 cc i := by
  by_cases h : cc.bools 5 i = true
  · by_cases hq : ccQuP4 cc i
    · exact Or.inl hq
    · exact Or.inr (Or.inl (show cc4CellP4 cc i ∧ ¬ccQuP4 cc i from ⟨h, hq⟩))
  · exact Or.inr (Or.inr h)

/-- OXLZLEZ2.hl:193. -/
theorem SUM_POS_LT_NUMSEG (m n : ℕ) (f : ℕ → ℝ) (hmn : m ≤ n)
    (h : ∀ p, m ≤ p → p ≤ n → 0 < f p) :
    0 < Finset.sum (Finset.Icc m n) f :=
  Finset.sum_pos (fun p hp => h p (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hp).2)
    ⟨m, Finset.mem_Icc.mpr ⟨le_refl m, hmn⟩⟩

/-- OXLZLEZ2.hl:398. -/
theorem SUM_BETA {α : Type*} (S : Set α) (f : α → ℝ) :
    setSum S (fun x => f x) = setSum S f := rfl

/-- OXLZLEZ2.hl:403 (`LXDEYBO_concl`, OXLZLEZ1.hl:142). -/
theorem LXDEYBO (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ccSizeP4 cc (cc4CellP4 cc) ≤ 4 := by sorry

/-- OXLZLEZ2.hl:564 (`MTMLSRF_concl`, OXLZLEZ1.hl:135). -/
theorem MTMLSRF (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ∃ i, 0 < i ∧ ccGgP4 cc i < 0 ∧ ccQuP4 cc i ∧
      cc4CellP4 cc (i + 1) ∧ cc4CellP4 cc (i - 1) := by sorry

/-- OXLZLEZ2.hl:1074. -/
theorem MOD_INJ1 (n k : ℕ) (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0) (x : ℕ) :
    x % n ≠ (x + k) % n := by
  intro heq
  have hd : n ∣ (x + k) - x := (Nat.modEq_iff_dvd' (Nat.le_add_right x k)).mp heq
  rw [Nat.add_sub_cancel_left] at hd
  exact hk0 (Nat.eq_zero_of_dvd_of_lt hd hk)

/-- OXLZLEZ2.hl:1100 (`WKR_COMPTED`). -/
theorem WKR_COMPTED (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ∃ i j k : ℕ, ¬(i = j ∨ j = k ∨ k = i) ∧
      i ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) ∧
      j ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) ∧
      k ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) ∧
      cc4CellP4 cc i ∧ cc4CellP4 cc j ∧ cc4CellP4 cc k := by sorry

/-- OXLZLEZ2.hl:1195/1225 (`oxl6142`, alias `CHQSQEY`; `CHQSQEY_concl`,
OXLZLEZ1.hl:135). -/
theorem CHQSQEY (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    3 ≤ ccSizeP4 cc (cc4CellP4 cc) := by sorry

/-- OXLZLEZ2.hl:1228. -/
theorem THREE_LE_CC_CARD (cc : CC4P4) (_h1 : ccBoolModelP4 cc)
    (_h2 : ccBoolPrepP4 cc) (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    3 ≤ ccCardP4 cc := by sorry

/-- OXLZLEZ2.hl:1255. -/
theorem THREE_MOD_CONSECUTIVES (i n : ℕ) (hi : 0 < i) (hn : 3 ≤ n) :
    ¬((i - 1) % n = i % n ∨ i % n = (i + 1) % n ∨ (i + 1) % n = (i - 1) % n) := by
  intro h
  rcases h with h | h | h
  · have hd : n ∣ i - (i - 1) := (Nat.modEq_iff_dvd' (by omega)).mp h
    have hle := Nat.le_of_dvd (show 0 < i - (i - 1) from by omega) hd
    omega
  · have hd : n ∣ (i + 1) - i := (Nat.modEq_iff_dvd' (by omega)).mp h
    have hle := Nat.le_of_dvd (show 0 < (i + 1) - i from by omega) hd
    omega
  · have hd : n ∣ (i + 1) - (i - 1) := (Nat.modEq_iff_dvd' (by omega)).mp h.symm
    have hle := Nat.le_of_dvd (show 0 < (i + 1) - (i - 1) from by omega) hd
    omega

/-- OXLZLEZ2.hl:1281. -/
theorem MOD_PERIOD_BOUNDED (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) (x : ℕ) :
    (x + k) % n = x % n → n ≤ k := by
  intro heq
  have hd : n ∣ (x + k) - x := (Nat.modEq_iff_dvd' (Nat.le_add_right x k)).mp heq.symm
  rw [Nat.add_sub_cancel_left] at hd
  exact Nat.le_of_dvd (show 0 < k from by omega) hd

/-- OXLZLEZ2.hl:1293. -/
theorem MOD_PERIOD_BOUNDED2 (nn m i k : ℕ) (hnn : nn ≠ 0) (hmk : m ≤ k)
    (h : (i + k) % nn ∈ (fun x => (i + x) % nn) '' {x | x < m}) : nn ≤ k := by
  simp only [Set.mem_image, Set.mem_setOf_eq] at h
  obtain ⟨x, hxm, hx⟩ := h
  have hxi : i + x ≤ i + k := by omega
  have hd : nn ∣ (i + k) - (i + x) :=
    (Nat.modEq_iff_dvd' hxi).mp hx
  rw [show i + k - (i + x) = k - x from by omega] at hd
  have hle := Nat.le_of_dvd (show 0 < k - x from by omega) hd
  omega

/-- OXLZLEZ2.hl:1322 (`UNPNFVW_concl`, OXLZLEZ1.hl:139). -/
theorem UNPNFVW (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ccSizeP4 cc (ccQyP4 cc) ≤ 1 := by sorry

/-- OXLZLEZ2.hl:1735. -/
theorem CC_4CELL_QUQX (cc : CC4P4) (i : ℕ) :
    cc4CellP4 cc i ↔ ccQuP4 cc i ∨ ccQxP4 cc i := by
  constructor
  · intro h
    by_cases hq : ccQuP4 cc i
    · exact Or.inl hq
    · exact Or.inr ⟨h, hq⟩
  · rintro (h | h)
    · exact h.2.1
    · exact h.1

/-- OXLZLEZ2.hl:1740. -/
theorem QX_NN00 (cc : CC4P4) (_hb : ccBoolModelP4 cc) (hr : ccRealModelP4 cc)
    (i : ℕ) (hqx : ccQxP4 cc i) : 0 ≤ ccGgP4 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -⟩ := hr
  exact h18 i hqx

/-- OXLZLEZ2.hl:1745. -/
theorem QY_NN00 (cc : CC4P4) (_hb : ccBoolModelP4 cc) (hr : ccRealModelP4 cc)
    (i : ℕ) (hqy : ccQyP4 cc i) : 0 ≤ ccGgP4 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h26, h27, h28, -⟩ := hr
  have h1 := h26 i hqy
  have h2 := h27 i hqy
  have h3 := h28 i hqy
  linarith

/-- OXLZLEZ2.hl:1752. -/
theorem NUMSEG_SET_VER (m : ℕ) : (Finset.Icc 0 m : Set ℕ) = {i | i ≤ m} := by
  ext i
  simp only [Finset.mem_coe, Finset.mem_Icc, Set.mem_setOf_eq]
  omega

/-- OXLZLEZ2.hl:1761. -/
theorem FINITE_INITIAL_SEG2 (n : ℕ) : {i : ℕ | i < n}.Finite := by
  have h : {i : ℕ | i < n} = (Finset.range n : Set ℕ) := by
    ext i; simp [Finset.mem_range]
  exact h ▸ (Finset.range n).finite_toSet

/-- OXLZLEZ2.hl:1768. -/
theorem CARD_MOD_NUMSEG (n m i : ℕ) (_hm : m ≤ n) :
    Nat.card {x : ℕ | ∃ k < m, x = (i + k) % n} = m := by sorry

/-- OXLZLEZ2.hl:1805. -/
theorem MOD_NUMSEG (n i : ℕ) (hn : n ≠ 0) :
    (Finset.Icc 0 (n - 1) : Set ℕ) = (fun x => (i + x) % n) '' {x | x < n} := by
  ext x
  simp only [Finset.mem_coe, Finset.mem_Icc, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hx⟩
    have hx' : x < n := by omega
    refine ⟨(x + n - i % n) % n, Nat.mod_lt _ (by omega), ?_⟩
    calc (i + (x + n - i % n) % n) % n
        = (i % n + (x + n - i % n) % n) % n := (Nat.mod_add_mod i n _).symm
      _ = ((x + n - i % n) % n + i % n) % n := by rw [Nat.add_comm]
      _ = ((x + n - i % n) + i % n) % n := Nat.mod_add_mod _ _ _
      _ = (i % n + (x + n - i % n)) % n := by rw [Nat.add_comm]
      _ = (x + n) % n := by
        have him : i % n < n := Nat.mod_lt i (by omega)
        have hle : i % n ≤ x + n := le_trans (le_of_lt him) (by omega)
        rw [Nat.add_sub_cancel' hle]
      _ = x % n := Nat.add_mod_right x n
      _ = x := Nat.mod_eq_of_lt hx'
  · rintro ⟨k, hk, rfl⟩
    have hlt : (i + k) % n < n := Nat.mod_lt (i + k) (by omega)
    exact ⟨by omega, by omega⟩

/-- OXLZLEZ2.hl:1830. -/
theorem IPVICGW_C33 (cc : CC4P4) (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧
    ccRealModelP4 cc ∧ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (_hc : ccCardP4 cc = 3) (i : ℕ) : ccSmallP4 cc i := by sorry

/-- OXLZLEZ2.hl:2009. -/
theorem UNIQUE_QY (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ∀ j, ccQyP4 cc j ∧ j ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) →
      ∀ k, k ≠ j ∧ k ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) →
        ¬ccQyP4 cc k := by sorry

/-- OXLZLEZ2.hl:2052. -/
theorem UNIQUE_QY2 (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ∀ j, ccQyP4 cc j ∧ j ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) →
      ∀ k, ccQyP4 cc k ∧ k ∈ (Finset.Icc 0 (ccCardP4 cc - 1) : Set ℕ) →
        k = j := by sorry

/-- OXLZLEZ2.hl:2068. -/
theorem IPVICGW_C43_C44 (cc : CC4P4) (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧
    ccRealModelP4 cc ∧ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (_hc : ccCardP4 cc = 4) (i : ℕ) : ccSmallP4 cc i := by sorry

/-- OXLZLEZ2.hl:2464. -/
theorem EXISTS_QY_CARD5 (cc : CC4P4) (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧
    ccRealModelP4 cc ∧ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (_hc : ccCardP4 cc = 5) : ∃ i, i < 5 ∧ ccQyP4 cc i := by sorry

/-- OXLZLEZ2.hl:2500. -/
theorem NUMSEG_INTER_22 (nn i x : ℕ) (hnn : nn ≠ 0) :
    (i ≤ x ∧ x ≤ i + nn - 1) ↔ ∃ k < nn, x = i + k := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - i, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

/-- OXLZLEZ2.hl:2513. -/
theorem PERIODIC_IMAGE_EQUAL (nn i : ℕ) (hnn : nn ≠ 0) {A : Type} (f : ℕ → A)
    (hf : periodicP4 f nn) :
    (fun x => f x) '' (Finset.Icc 0 (nn - 1) : Set ℕ) =
      (fun x => f x) '' (Finset.Icc i (i + nn - 1) : Set ℕ) := by
  have key : ∀ x : ℕ, f x = f (x % nn) := by
    intro x
    have gen : ∀ d x : ℕ, x < (d + 1) * nn → f x = f (x % nn) := by
      intro d
      induction d with
      | zero =>
        intro x hx
        rw [Nat.mod_eq_of_lt (by simpa using hx)]
      | succ d ih =>
        intro x hx
        by_cases hlt : x < nn
        · rw [Nat.mod_eq_of_lt hlt]
        · have hxn : nn ≤ x := by omega
          have hx2 : x < (d + 1) * nn + nn := by
            have h3 := hx
            rw [show (d + 1 + 1) * nn = (d + 1) * nn + nn from by ring] at h3
            exact h3
          rw [show x = x - nn + nn from by omega, hf (x - nn),
            ih (x - nn) (by omega), Nat.add_mod_right]
    exact gen x x (by
      have h1 : 1 ≤ nn := Nat.pos_of_ne_zero hnn
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self x)
        (Nat.le_mul_of_pos_right (x + 1) h1))
  have hi1 : (Finset.Icc i (i + nn - 1) : Set ℕ) = (fun x => i + x) '' {x | x < nn} := by
    ext y
    simp only [Finset.mem_coe, Finset.mem_Icc, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨y - i, by omega, by omega⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [hi1, MOD_NUMSEG nn i hnn, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  rw [key (i + x)]

/-- OXLZLEZ2.hl:2527. -/
theorem CARD5_1074_LE_QYI (cc : CC4P4) (i : ℕ)
    (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧ ccRealModelP4 cc ∧
      Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (_h4c : ∀ j, cc4CellP4 cc j →
      aSpine5P4 + bSpine5P4 * ccAzimP4 cc j ≤ ccGgP4 cc j)
    (_hqy : ∀ j, ccQyP4 cc j → 0.008 * ccAzimP4 cc j ≤ ccGgP4 cc j)
    (_hqyi : ccQyP4 cc i) (_hc : ccCardP4 cc = 5)
    (_hper : periodicP4 (ccGgP4 cc) (ccCardP4 cc))
    (_hgb : ∀ j, 0.606 ≤ ccAzimP4 cc j)
    (_hsum : Finset.sum (Finset.Icc 0 (ccCardP4 cc)) (ccAzimP4 cc) = 2 * Real.pi)
    (_h1074 : 1.074 ≤ ccAzimP4 cc i) :
    0 ≤ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) := by sorry

/-- OXLZLEZ2.hl:3229. -/
theorem PRE_IPVICGW (cc : CC4P4) (h : ccBoolModelP4 cc ∧ ccBoolPrepP4 cc ∧
    ccRealModelP4 cc ∧ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (_hc : ccCardP4 cc = 5) :
    0 ≤ Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) := by sorry

/-- OXLZLEZ2.hl:3264. -/
theorem CC_CARD_LESS_THAN_5 (cc : CC4P4) (_h1 : ccBoolModelP4 cc)
    (_h2 : ccBoolPrepP4 cc) (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ccCardP4 cc ≤ 5 := by sorry

/-- OXLZLEZ2.hl:3308 (`IPVICGW_concl`, OXLZLEZ1.hl:548). -/
theorem IPVICGW (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (i : ℕ) : ccSmallP4 cc i := by sorry

/-- OXLZLEZ2.hl:3320 (`RSIWAMP_concl`, OXLZLEZ1.hl:554). -/
theorem RSIWAMP (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ccCardP4 cc ≤ 4 := by sorry

/-- OXLZLEZ2.hl:3341. -/
theorem LEAST_BOUND_CC_GG (cc : CC4P4)
    (h1 : ∀ i, ccQuP4 cc i → -ccEpsP4 ≤ ccGgP4 cc i)
    (h2 : ∀ i, ccQxP4 cc i → 0 ≤ ccGgP4 cc i)
    (h3 : ∀ i, ccQyP4 cc i → 0 ≤ ccGgP4 cc i) (i : ℕ) :
    -ccEpsP4 ≤ ccGgP4 cc i := by
  rcases QU_OR_QXY cc i with h | h | h
  · exact h1 i h
  · exact le_trans (by norm_num [ccEpsP4]) (h2 i h)
  · exact le_trans (by norm_num [ccEpsP4]) (h3 i h)

/-- OXLZLEZ2.hl:3361. -/
theorem LITTLE_CC_GG3BB (cc : CC4P4) (i : ℕ)
    (h1 : ∀ j, ccQyP4 cc j → 0 ≤ ccGg3bP4 cc j)
    (h2 : ∀ j, ccQuP4 cc (j + 1) ∧ ccQyP4 cc j →
      0 ≤ ccGg3bP4 cc j + ccGgP4 cc (j + 1))
    (h3 : ∀ j, ccQyP4 cc j → 0 ≤ ccGgP4 cc j)
    (h4 : ∀ j, ccQxP4 cc j → 0 ≤ ccGgP4 cc j)
    (h5 : ccQyP4 cc i) : 0 ≤ ccGg3bP4 cc i + ccGgP4 cc (i + 1) := by
  rcases QU_OR_QXY cc (i + 1) with h | h | h
  · exact h2 i ⟨h, h5⟩
  · have hg := h4 (i + 1) h
    have hb := h1 i h5
    linarith
  · have hg := h3 (i + 1) h
    have hb := h1 i h5
    linarith

/-- OXLZLEZ2.hl:3379. -/
theorem LITTLE_CC_GG3AA (cc : CC4P4) (nn : ℕ) (i : ℕ)
    (h1 : ∀ j, ccQyP4 cc j → 0 ≤ ccGg3aP4 cc j)
    (h2 : ∀ j, ccQuP4 cc j ∧ ccQyP4 cc (j + 1) →
      0 ≤ ccGgP4 cc j + ccGg3aP4 cc (j + 1))
    (h3 : ∀ j, ccQyP4 cc j → 0 ≤ ccGgP4 cc j)
    (h4 : ∀ j, ccQxP4 cc j → 0 ≤ ccGgP4 cc j)
    (hpqy : periodicPropP4 (ccQyP4 cc) nn)
    (hpgg3a : periodicP4 (ccGg3aP4 cc) nn)
    (hnn : nn ≠ 0)
    (h5 : ccQyP4 cc i) : 0 ≤ ccGgP4 cc (i + nn - 1) + ccGg3aP4 cc i := by
  have hj : i + nn - 1 + 1 = i + nn := by omega
  rcases QU_OR_QXY cc (i + nn - 1) with hq | hx | hy
  · have hbound := h2 (i + nn - 1) ⟨hq, by rw [hj]; exact (hpqy i).mpr h5⟩
    rw [hj] at hbound
    rw [← hpgg3a i]
    exact hbound
  · have hg := h4 (i + nn - 1) hx
    have ha := h1 i h5
    linarith
  · have hg := h3 (i + nn - 1) hy
    have ha := h1 i h5
    linarith

/-- OXLZLEZ2.hl:3457 (`UTEOITF_concl`, OXLZLEZ1.hl:~3440). -/
theorem UTEOITF (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (i : ℕ) : cc4CellP4 cc i := by sorry

/-- OXLZLEZ2.hl:3919. -/
theorem GRHIDFA_ALT (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    ccCardP4 cc ≠ 4 := by sorry

/-- OXLZLEZ2.hl:4241. -/
theorem NOT_QY_LEM (cc : CC4P4) (h1 : ccBoolModelP4 cc) (h2 : ccBoolPrepP4 cc)
    (h3 : ccRealModelP4 cc)
    (h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0)
    (i : ℕ) : ¬ccQyP4 cc i := fun hqy =>
  hqy (UTEOITF cc h1 h2 h3 h4 i)

/-- OXLZLEZ2.hl:4249 (`LUIKGMH_concl`, OXLZLEZ1.hl:~4231). -/
theorem LUIKGMH (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    4 ≤ ccCardP4 cc := by sorry

/-- OXLZLEZ2.hl:4512 (`GRHIDFA_concl`, OXLZLEZ1.hl:~4236): the D-case
capstone — a negative `sum cc_gg_v11` over a compressed model is
impossible. -/
theorem GRHIDFA (cc : CC4P4) (_h1 : ccBoolModelP4 cc) (_h2 : ccBoolPrepP4 cc)
    (_h3 : ccRealModelP4 cc)
    (_h4 : Finset.sum (Finset.Icc 0 (ccCardP4 cc - 1)) (ccGgP4 cc) < 0) :
    False := by sorry

/-! ## 2b. Public `CcV11` twins of the nine OXLZLEZ1 conclusions

The 39-theorem wave above lives over the file-private `CC4P4` record, so
outside modules could never name these twins — `PackingConcl`'s whole
Auto3 `OXLZLEZ1.hl` family stayed unwired ("parallel private encoding").
The nine theorems below repeat the *statement* half over `PackingAuto3`'s
public `CcV11` encoding (PA3 imported above), verbatim to PA3's
`*_concl` rows / HOL originals.  Proof bodies stay `sorry` (skeleton
batch): the private `CC4P4` twins of section 2 are the eventual proof
bank these rows will be discharged from. -/

/-- OXLZLEZ1.hl:135-136 (`CHQSQEY_concl`); public `CcV11` twin of
`CHQSQEY` above. -/
theorem CHQSQEY_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) := by sorry

/-- OXLZLEZ1.hl:138-140 (`MTMLSRF_concl`); public `CcV11` twin of
`MTMLSRF` above. -/
theorem MTMLSRF_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1) := by sorry

/-- OXLZLEZ1.hl:142-143 (`LXDEYBO_concl`); public `CcV11` twin of
`LXDEYBO` above. -/
theorem LXDEYBO_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_4cell_v11 cc) ≤ 4 := by sorry

/-- OXLZLEZ1.hl:145-146 (`UNPNFVW_concl`); public `CcV11` twin of
`UNPNFVW` above. -/
theorem UNPNFVW_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_qy_v11 cc) ≤ 1 := by sorry

/-- OXLZLEZ1.hl:156-157 (`IPVICGW_concl`); public `CcV11` twin of
`IPVICGW` above. -/
theorem IPVICGW_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_small_v11 cc i := by sorry

/-- OXLZLEZ1.hl:159-160 (`RSIWAMP_concl`); public `CcV11` twin of
`RSIWAMP` above. -/
theorem RSIWAMP_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_card_v11 cc ≤ 4 := by sorry

/-- OXLZLEZ1.hl:167-168 (`UTEOITF_concl`); public `CcV11` twin of
`UTEOITF` above. -/
theorem UTEOITF_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_4cell_v11 cc i := by sorry

/-- OXLZLEZ1.hl:170-171 (`LUIKGMH_concl`); public `CcV11` twin of
`LUIKGMH` above. -/
theorem LUIKGMH_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    4 ≤ cc_card_v11 cc := by sorry

/-- OXLZLEZ1.hl:173-174 (`GRHIDFA_concl`); public `CcV11` twin of
`GRHIDFA` above: the D-case capstone `False`. -/
theorem GRHIDFA_v11 (cc : CcV11) (_hb : cc_bool_model_v11 cc)
    (_hp : cc_bool_prep_v11 cc) (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    False := by sorry

/-! ## 3. `betaBump` and the `bump.hl` calculus

`beta_bump` encoding note. Flyspeck's ORIGINAL `beta_bump` (the one
bump.hl:10 says "REDO") was an integral: the volume of the radial bump
`\w ↦ bump |w - u|` (`bump` = the d0-beta quadratic above) accumulated over
the Rogers cones / matching Voronoi regions at the two endpoints of the
critical edge `e` — i.e. a `volume`-integral of the quadratic over
`rcone_ge`/`rcone_gt` wedges, scaled by `1/(2 h0)`. That integral was
REWRITTEN (sqrt/quadratic inequalities; the Rogers cones live only inside
the `mcell` layer) into the closed form ported here as `betaBump` (HL
`beta_bump_v1`, `pack_defs.hl:180-187`): the difference of the bump
quadratic at the two circumradii `bump (radV e) - bump (radV e')`, active
precisely on the critical-edge pair `(e, e')` of a non-null Marchal cell
whose every other edge is subcritical. `betaBumpV1` (same body) already
exists in PackingAuto2; the copy below is the verbatim-faithful in-file
definition for this batch's self-containment. -/

/-- HOL `beta_bump_v1` (pack_defs.hl:180-187; the redo of the integral-based
`beta_bump`; see the section note above for the integral semantics and the
closed-form rewrite). -/
noncomputable def betaBump (V : Set V3) (e : Set V3) (X : Set V3) : ℝ :=
  let e' := VX V X \ e
  if X ∈ mcellSet V ∧ ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧
      e' ∈ criticalEdgeX V X ∧
      ∀ f ∈ edgeX V X, f = e ∨ f = e' ∨ f ∈ subcriticalEdgeX V X then
    bump (radV e) - bump (radV e')
  else 0

namespace BumpP4

/-! ### AJRIPQN-port kit (HDTFNFZ / bump-cluster prerequisites)

The bump cluster below (HDTFNFZ_SUBSET … SUM_BETA_BUMP_LEMMA, HOL bump.hl
211-1198) is blocked in the HOL sources by `Ajripqn.AJRIPQN` only through the
`cell_params`-uniqueness theorems (`MCELL_CELL_PARAMETERS_EXIST` family,
which remain open with NEEDS notes). Everything else in the cluster needs
only `HDTFNFZ` (`VX V X = V ∩ X`), whose proof route (HDTFNFZ.hl:44-111, as
assembled in PackingAuto17's `hdtfnfz_p17`) consumes just the PA11 pair
`LEPJBDJ`/`LEPJBDJ_0` plus the epsilon-witness trick for `cell_params`. The
private `_p4` lemmas below re-prove that kit in-file; no statement from any
an unproved upstream theorem is consumed. -/

/-- Prefix spec for `truncateSimplex` once the list is long enough (the
epsilon in `truncateSimplex` has a witness only under `ul.length ≥ j + 1`). -/
private theorem truncateSimplex_spec_p4 {ul : List V3} {j : ℕ} (h : j + 1 ≤ ul.length) :
    (truncateSimplex j ul).length = j + 1 ∧ initialSublist (truncateSimplex j ul) ul := by
  refine Classical.epsilon_spec
    (p := fun vl : List V3 => vl.length = j + 1 ∧ initialSublist vl ul) ⟨ul.take (j + 1), ?_, ?_⟩
  · rw [List.length_take]
    omega
  · exact ⟨ul.drop (j + 1), (List.take_append_drop (j + 1) ul).symm⟩

/-- Same-length initial sublists coincide. -/
private theorem initialSublist_length_p4 {xl yl : List V3} (h : initialSublist xl yl)
    (hl : xl.length = yl.length) : xl = yl := by
  obtain ⟨t, ht⟩ := h
  subst ht
  rw [List.length_append] at hl
  have h0 : t.length = 0 := by omega
  rw [List.length_eq_zero_iff.1 h0, List.append_nil]

/-- `setOfList (truncateSimplex 0 ul)` is the singleton of the head. -/
private theorem setOfList_truncateSimplex0_p4 {ul : List V3} (h : 0 < ul.length) :
    setOfList (truncateSimplex 0 ul) = {hdV ul} := by
  rcases ul with _ | ⟨a, t⟩
  · simp at h
  · obtain ⟨hl, hin⟩ := truncateSimplex_spec_p4 (ul := a :: t) (j := 0) (by omega)
    have heq : truncateSimplex 0 (a :: t) = [a] := by
      obtain ⟨y, hy⟩ := hin
      rcases hc : truncateSimplex 0 (a :: t) with _ | ⟨b, s⟩
      · rw [hc] at hl; simp at hl
      · rw [hc] at hl hy
        have hs0 : s = [] := by
          rw [List.length_cons] at hl
          exact List.length_eq_zero_iff.1 (by omega)
        rw [List.cons_append, hs0, List.nil_append] at hy
        have hba : b = a := (List.cons.inj hy).1.symm
        rw [hs0, hba]
    rw [heq]
    simp [setOfList, hdV]

/-- A length-4 list equals its own 3-truncation as a set. -/
private theorem setOfList_truncateSimplex3_p4 {ul : List V3} (h : ul.length = 4) :
    setOfList (truncateSimplex 3 ul) = setOfList ul := by
  obtain ⟨hl, hin⟩ := truncateSimplex_spec_p4 (ul := ul) (j := 3) (by omega)
  have heq : truncateSimplex 3 ul = ul := initialSublist_length_p4 hin (by rw [hl, h])
  rw [heq]

/-- The `cell_params` pair of a candidate cell `X = mcell k V ul` satisfies
the defining predicate (HL HDTFNFZ.hl:53-78 `SELECT_AX` at `((if k ≤ 3 then k
else 4), ul)`; here the `k ≥ 4` branch is the `mcell` dispatch itself, so no
PA12 `MCELL_EXPLICIT` is needed). -/
private theorem cellParams_spec_p4 {V : Set V3} {ul : List V3} {k : ℕ} {X : Set V3}
    (hbar : barV V 3 ul) (hX : X = mcell k V ul) :
    (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧
      X = mcell (cellParams V X).1 V (cellParams V X).2 := by
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 := by
    rcases Nat.lt_or_ge k 4 with hk | hk
    · exact ⟨(k, ul), by omega, hbar, hX⟩
    · refine ⟨(4, ul), le_refl 4, hbar, ?_⟩
      rw [hX]
      have hdispatch : mcell k V ul = mcell4 V ul := by
        simp only [mcell]
        split_ifs with h0 h1 h2 h3
        · omega
        · omega
        · omega
        · omega
        · rfl
      rw [hdispatch]
      rfl
  exact Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2) hex

/-- HOL `HDTFNFZ` (HDTFNFZ.hl:44-111): the vertex set of a non-null cell is
`V ∩ X`. Route as in PackingAuto17's `hdtfnfz_p17`: `cellParams_spec_p4`
identifies the parameter pair, the `k' = 0` branch is `LEPJBDJ_0`, the
`k' > 0` branch is `LEPJBDJ`, and the empty-cell branch dies by
`measure_empty`. -/
private theorem hdtfnfz_p4 {V : Set V3} {ul : List V3} {k : ℕ} {X : Set V3}
    (hsat : saturated V) (hpack : Packing V) (hbar : barV V 3 ul)
    (hX : X = mcell k V ul) (hnull : ¬nullSet X) :
    VX V X = V ∩ X := by
  obtain ⟨h4, hbar', hX'⟩ := cellParams_spec_p4 hbar hX
  set N := cellParams V X with hN
  have hne : mcell N.1 V N.2 ≠ ∅ := by
    intro hc
    refine hnull ?_
    show MeasureTheory.volume X = 0
    rw [hX', hc]
    exact MeasureTheory.measure_empty
  have hvx : VX V X = (if N.1 = 0 then ∅
      else setOfList (truncateSimplex (N.1 - 1) N.2)) := by
    simp only [VX, if_neg hnull, ← hN]
  rw [hvx, hX']
  rcases Nat.eq_zero_or_pos N.1 with h0 | h0
  · rw [if_pos h0, h0, LEPJBDJ_0 V N.2 hsat hpack hbar']
  · rw [if_neg (by omega : N.1 ≠ 0),
      LEPJBDJ V N.2 N.1 hsat hpack hbar' (by omega) h4 hne]

/-- `barV` prefix lists with the same point set have the same length: the
`voronoiNondg` length formula `affDim (voronoiList) + length = 4` and the fact
that `voronoiList` only sees `setOfList` (PackingAuto2 `voronoiList`). -/
private theorem barV_length_inj_p4 {V : Set V3} {ul : List V3} (hb : barV V 3 ul)
    {w1 w2 : List V3} (h1 : initialSublist w1 ul) (h01 : 0 < w1.length)
    (h2 : initialSublist w2 ul) (h02 : 0 < w2.length)
    (hS : setOfList w1 = setOfList w2) : w1.length = w2.length := by
  have hd1 := hb.2 w1 ⟨h1, h01⟩
  have hd2 := hb.2 w2 ⟨h2, h02⟩
  have hvo : voronoiList V w1 = voronoiList V w2 := by
    show voronoiSet V (setOfList w1) = voronoiSet V (setOfList w2)
    rw [hS]
  have e1 : affDim (voronoiList V w1) + (w1.length : ℤ) = 4 := hd1.2.2
  have e2 : affDim (voronoiList V w2) + (w2.length : ℤ) = 4 := hd2.2.2
  rw [hvo] at e1
  omega

/-- The four points of a `barV V 3` list are pairwise distinct: if
`el i = el j` with `i < j` then the first `j` points and the first `j + 1`
points have the same set, so the two prefixes coincide as lists of different
lengths — contradicting `barV_length_inj_p4`. -/
private theorem barV_elV_ne_p4 {V : Set V3} {ul : List V3} (hb : barV V 3 ul)
    {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) : elV ul i ≠ elV ul j := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  have key : ∀ (w1 w2 : List V3), initialSublist w1 [u0, u1, u2, u3] →
      initialSublist w2 [u0, u1, u2, u3] → 0 < w1.length → 0 < w2.length →
      setOfList w1 = setOfList w2 → w1.length = w2.length :=
    fun w1 w2 ha1 ha2 hl1 hl2 hS => barV_length_inj_p4 hb ha1 hl1 ha2 hl2 hS
  intro hcon
  interval_cases i <;> interval_cases j <;> simp [elV] at hcon
  · omega
  · -- (0, 1): u0 = u1
    exact absurd (key [u0] [u0, u1] ⟨[u1, u2, u3], rfl⟩ ⟨[u2, u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (0, 2): u0 = u2
    exact absurd (key [u0, u1] [u0, u1, u2] ⟨[u2, u3], rfl⟩ ⟨[u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (0, 3): u0 = u3
    exact absurd (key [u0, u1, u2] [u0, u1, u2, u3] ⟨[u3], rfl⟩ ⟨[], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (1, 0): u1 = u0
    exact absurd (key [u0, u1] [u0] ⟨[u2, u3], rfl⟩ ⟨[u1, u2, u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · omega
  · -- (1, 2): u1 = u2
    exact absurd (key [u0, u1] [u0, u1, u2] ⟨[u2, u3], rfl⟩ ⟨[u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (1, 3): u1 = u3
    exact absurd (key [u0, u1, u2] [u0, u1, u2, u3] ⟨[u3], rfl⟩ ⟨[], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (2, 0): u2 = u0
    exact absurd (key [u0, u1, u2] [u0, u1] ⟨[u3], rfl⟩ ⟨[u2, u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (2, 1): u2 = u1
    exact absurd (key [u0, u1, u2] [u0, u1] ⟨[u3], rfl⟩ ⟨[u2, u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · omega
  · -- (2, 3): u2 = u3
    exact absurd (key [u0, u1, u2] [u0, u1, u2, u3] ⟨[u3], rfl⟩ ⟨[], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (3, 0): u3 = u0
    exact absurd (key [u0, u1, u2, u3] [u0, u1, u2] ⟨[], rfl⟩ ⟨[u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (3, 1): u3 = u1
    exact absurd (key [u0, u1, u2, u3] [u0, u1, u2] ⟨[], rfl⟩ ⟨[u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · -- (3, 2): u3 = u2
    exact absurd (key [u0, u1, u2, u3] [u0, u1, u2] ⟨[], rfl⟩ ⟨[u3], rfl⟩ (by simp) (by simp)
      (by ext x; simp [setOfList, hcon] <;> try tauto)) (by simp)
  · omega

/-- No edges off an empty vertex set. -/
private theorem edgeX_empty_p4 {V : Set V3} {X : Set V3} (h : VX V X = ∅) :
    edgeX V X = ∅ := by
  ext e
  simp only [edgeX, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_iff]
  constructor
  · rintro ⟨u, v, rfl, hu, -, -⟩
    rw [h] at hu
    exact hu
  · exact fun hc => hc.elim

/-- No edges off a subsingleton vertex set. -/
private theorem edgeX_subsingleton_p4 {V : Set V3} {X : Set V3} {v : V3}
    (h : VX V X ⊆ {v}) : edgeX V X = ∅ := by
  ext e
  simp only [edgeX, Set.mem_setOf_eq, Set.mem_empty_iff_false, false_iff]
  constructor
  · rintro ⟨u, w, rfl, hu, hw, huvw⟩
    have hu' : u = v := h hu
    have hw' : w = v := h hw
    rw [hu', hw'] at huvw
    exact huvw rfl
  · exact fun hc => hc.elim

/-- An initial sublist's point set is contained in the host's. -/
private theorem setOfList_initialSublist_p4 {xl yl : List V3} (h : initialSublist xl yl) :
    setOfList xl ⊆ setOfList yl := by
  rintro x hx
  obtain ⟨t, ht⟩ := h
  rw [ht]
  simp only [setOfList, List.mem_append]
  exact Or.inl hx

/-- `hdV` is `elV · 0`. -/
private theorem hdV_elV_p4 (ul : List V3) : hdV ul = elV ul 0 := by
  cases ul with
  | nil => simp [hdV, elV]
  | cons a t => simp [hdV, elV]

/-- Membership of an explicit pair edge, given the vertex set (HL
bump.hl:806/956 helper form: `edgeX` membership ↔ two distinct vertices). -/
private theorem edgeX_pair_iff_p4 {V : Set V3} {X : Set V3} {s : Set V3}
    (hvx : VX V X = s) {u v : V3} :
    ({u, v} : Set V3) ∈ edgeX V X ↔ u ≠ v ∧ {u, v} ⊆ s := by
  simp only [edgeX, Set.mem_setOf_eq, hvx]
  constructor
  · rintro ⟨u', v', hpair, hu', hv', hne'⟩
    have h1 : u ∈ ({u', v'} : Set V3) := by rw [← hpair]; simp
    have h2 : v ∈ ({u', v'} : Set V3) := by rw [← hpair]; simp
    refine ⟨?_, ?_⟩
    · intro huv
      subst huv
      have hsub' : ({u', v'} : Set V3) ⊆ {u} := by
        rw [← hpair]
        exact Set.insert_subset_iff.2 ⟨by simp, Set.Subset.rfl⟩
      have h3 : u' = u := Set.mem_singleton_iff.1 (hsub' (by simp))
      have h4 : v' = u := Set.mem_singleton_iff.1 (hsub' (by simp))
      exact absurd (h3.trans h4.symm) hne'
    · intro x hx
      have hx' : x ∈ ({u', v'} : Set V3) := by rw [← hpair]; exact hx
      rcases Set.mem_insert_iff.1 hx' with hxe | hxe
      · rw [hxe]
        exact hu'
      · rw [Set.mem_singleton_iff.1 hxe]
        exact hv'
  · rintro ⟨huv, hsub⟩
    exact ⟨u, v, rfl, hsub (by simp), hsub (by simp : v ∈ ({u, v} : Set V3)), huv⟩

/-- `mcell` dispatch at `k = 0` (the public `MCELL0` below is stated only
later in this file, so the kit carries its own copy). -/
private theorem mcell0_dispatch_p4 (V : Set V3) (ul : List V3) :
    mcell0 V ul = mcell 0 V ul := by
  simp [mcell]

/-- `mcell` dispatch at `k = 1`. -/
private theorem mcell1_dispatch_p4 (V : Set V3) (ul : List V3) :
    mcell1 V ul = mcell 1 V ul := by
  simp [mcell]

end BumpP4

namespace BumpP4

/-- HL `BIJ` rendered over sets. -/
private def BIJP4 {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  Set.BijOn f s t

/-- bump.hl:25: beta reduction of an ordered-pair lambda. -/
theorem BETA_ORDERED_PAIR_THM {α β γ : Type} (g : α → β → γ) (x : α × β) :
    (fun p => g p.1 p.2) x = g x.1 x.2 := rfl

/-- bump.hl:37. -/
theorem BIJ_SUM {α β : Type} [Fintype α] [Fintype β] (A : Set α) (B : Set β)
    (f : β → ℝ) (ab : α ≃ β) (_h : Set.BijOn ab A B) :
    setSum A (fun a => f (ab a)) = setSum B f := by
  have hBimg : Set.image ab A = B := Set.BijOn.image_eq _h
  have hA : A.Finite := Set.toFinite A
  have hBfinA : (Set.image ab A).Finite := hA.image ab
  haveI : Fintype ↑(Set.image ab A) := hBfinA.fintype
  haveI : Fintype ↑A := hA.fintype
  rw [← hBimg]
  classical
  simp only [setSum, dif_pos hA, dif_pos hBfinA]
  simp only [Set.Finite.toFinset_image ab hA hBfinA]
  convert
    (Finset.sum_image (f := fun x : β => f x) (g := ab) (s := hA.toFinset)
      (fun x _ y _ hxy => ab.injective hxy)).symm <;>
    · rfl

/-- bump.hl:47. -/
theorem EL_EXPLICIT (h : V3) (t : List V3) :
    elV (h :: t) 0 = h ∧ elV (h :: t) 1 = hdV t := by
  cases t with
  | nil => simp [elV, hdV]
  | cons a tl => simp [elV, hdV]

/-- bump.hl:61. -/
theorem LENGTH1 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 1) :
    ul = [ul.getD 0 default] := by
  match h : ul with
  | [_] => rfl
  | [] => simp_all
  | _a :: _b :: _tl => simp_all

/-- bump.hl:71. -/
theorem LENGTH2 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 2) :
    ul = [ul.getD 0 default, ul.getD 1 default] := by
  match h : ul with
  | [_, _] => rfl
  | [] => simp_all
  | _a :: [] => simp_all
  | _a :: _b :: _c :: _tl => simp_all

/-- bump.hl:83. -/
theorem LENGTH3 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 3) :
    ul = [ul.getD 0 default, ul.getD 1 default, ul.getD 2 default] := by
  match h : ul with
  | [_, _, _] => rfl
  | [] => simp_all
  | _a :: [] => simp_all
  | _a :: _b :: [] => simp_all
  | _a :: _b :: _c :: _d :: _tl => simp_all

/-- bump.hl:95. -/
theorem LENGTH4 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 4) :
    ul = [ul.getD 0 default, ul.getD 1 default, ul.getD 2 default,
      ul.getD 3 default] := by
  match h : ul with
  | [_, _, _, _] => rfl
  | [] => simp_all
  | _a :: [] => simp_all
  | _a :: _b :: [] => simp_all
  | _a :: _b :: _c :: [] => simp_all
  | _a :: _b :: _c :: _d :: _e :: _tl => simp_all

/-- bump.hl:120. -/
theorem set_of_list2_explicit {α : Type} (a b : α) :
    setOfList [a, b] = {a, b} := by
  ext x
  simp [setOfList]


/-- bump.hl:130. -/
theorem set_of_list3_explicit {α : Type} (a b c : α) :
    setOfList [a, b, c] = {a, b, c} := by
  ext x
  simp [setOfList]


/-- bump.hl:144. -/
theorem set_of_list4_explicit {α : Type} (a b c d : α) :
    setOfList [a, b, c, d] = {a, b, c, d} := by
  ext x
  simp [setOfList]


/-- bump.hl:107. -/
theorem set_of_list2 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 2) :
    setOfList ul = {ul.getD 0 default, ul.getD 1 default} := by
  cases ul with
  | nil => simp at h
  | cons a tl =>
    cases tl with
    | nil => simp at h
    | cons b tl2 =>
      cases tl2 with
      | nil => exact set_of_list2_explicit a b
      | cons c tl3 => simp at h

/-- bump.hl:154. -/
theorem set_of_list3 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 3) :
    setOfList ul =
      {ul.getD 0 default, ul.getD 1 default, ul.getD 2 default} := by
  cases ul with
  | nil => simp at h
  | cons a tl =>
    cases tl with
    | nil => simp at h
    | cons b tl2 =>
      cases tl2 with
      | nil => simp at h
      | cons c tl3 =>
        cases tl3 with
        | nil => exact set_of_list3_explicit a b c
        | cons d tl4 => simp at h

/-- bump.hl:169. -/
theorem set_of_list4 {α : Type} [Inhabited α] (ul : List α) (h : ul.length = 4) :
    setOfList ul =
      {ul.getD 0 default, ul.getD 1 default, ul.getD 2 default,
        ul.getD 3 default} := by
  cases ul with
  | nil => simp at h
  | cons a tl =>
    cases tl with
    | nil => simp at h
    | cons b tl2 =>
      cases tl2 with
      | nil => simp at h
      | cons c tl3 =>
        cases tl3 with
        | nil => simp at h
        | cons d tl4 =>
          cases tl4 with
          | nil => exact set_of_list4_explicit a b c d
          | cons e tl5 => simp at h

/-- bump.hl:179. -/
theorem SET_OF_LIST_TRUNCATE_1 (ul : List V3) (h : 2 ≤ ul.length) :
    setOfList (truncateSimplex 1 ul) = {elV ul 0, elV ul 1} := by
  cases ul with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      have hw : (truncateSimplex 1 (a :: b :: t2)).length = 1 + 1 ∧
          initialSublist (truncateSimplex 1 (a :: b :: t2)) (a :: b :: t2) :=
        Classical.epsilon_spec
          (p := fun vl : List V3 => vl.length = 1 + 1 ∧ initialSublist vl (a :: b :: t2))
          ⟨[a, b], rfl, ⟨t2, rfl⟩⟩
      have heqL : truncateSimplex 1 (a :: b :: t2) = [a, b] := by
        -- same-length initial sublists coincide (PA5 INITIAL_SUBLIST_UNIQUE, inlined)
        have hgen : ∀ xl yl : List V3, initialSublist xl (a :: b :: t2) → xl.length = 2 →
            initialSublist yl (a :: b :: t2) → yl.length = 2 → xl = yl := by
          intro xl yl hp1 hp2 hp3 hp4
          obtain ⟨t1, ht1⟩ := hp1
          obtain ⟨t2', ht2⟩ := hp3
          have heq : xl ++ t1 = yl ++ t2' := by rw [← ht1, ht2]
          rcases List.append_eq_append_iff.1 heq with ⟨t, rfl, -⟩ | ⟨t, rfl, -⟩
          · rw [List.length_append, hp2] at hp4
            have ht0 : t.length = 0 := by omega
            rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
          · rw [List.length_append, hp4] at hp2
            have ht0 : t.length = 0 := by omega
            rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
        exact hgen _ _ hw.2 hw.1 ⟨t2, rfl⟩ rfl
      rw [heqL]
      ext x
      simp [setOfList, elV]

/-- bump.hl:194. -/
theorem SET_OF_LIST_TRUNCATE_2 (ul : List V3) (h : 3 ≤ ul.length) :
    setOfList (truncateSimplex 2 ul) = {elV ul 0, elV ul 1, elV ul 2} := by
  cases ul with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => simp at h
      | cons c t3 =>
        have hw : (truncateSimplex 2 (a :: b :: c :: t3)).length = 2 + 1 ∧
            initialSublist (truncateSimplex 2 (a :: b :: c :: t3)) (a :: b :: c :: t3) :=
          Classical.epsilon_spec
            (p := fun vl : List V3 => vl.length = 2 + 1 ∧ initialSublist vl (a :: b :: c :: t3))
            ⟨[a, b, c], rfl, ⟨t3, rfl⟩⟩
        have heqL : truncateSimplex 2 (a :: b :: c :: t3) = [a, b, c] := by
          -- same-length initial sublists coincide (PA5 INITIAL_SUBLIST_UNIQUE, inlined)
          have hgen : ∀ xl yl : List V3, initialSublist xl (a :: b :: c :: t3) →
              xl.length = 3 → initialSublist yl (a :: b :: c :: t3) → yl.length = 3 →
              xl = yl := by
            intro xl yl hp1 hp2 hp3 hp4
            obtain ⟨t1, ht1⟩ := hp1
            obtain ⟨t3', ht2⟩ := hp3
            have heq : xl ++ t1 = yl ++ t3' := by rw [← ht1, ht2]
            rcases List.append_eq_append_iff.1 heq with ⟨t, rfl, -⟩ | ⟨t, rfl, -⟩
            · rw [List.length_append, hp2] at hp4
              have ht0 : t.length = 0 := by omega
              rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
            · rw [List.length_append, hp4] at hp2
              have ht0 : t.length = 0 := by omega
              rw [List.length_eq_zero_iff.1 ht0, List.append_nil]
          exact hgen _ _ hw.2 hw.1 ⟨t3, rfl⟩ rfl
        rw [heqL]
        ext x
        simp [setOfList, elV]

/-- bump.hl:211. -/
theorem VX_EMPTY (V : Set V3) (vl : List V3) (k : ℕ) (h : nullSet (mcell k V vl)) :
    VX V (mcell k V vl) = ∅ := by
  simp [VX, h]

/-- bump.hl:220. -/
theorem RIJRIED (V : Set V3) (vl : List V3) (k : ℕ) (h : nullSet (mcell k V vl)) :
    edgeX V (mcell k V vl) = ∅ := by
  have := VX_EMPTY V vl k h
  simp [edgeX, this]

/-- bump.hl:232. -/
theorem HDTFNFZ_SUBSET (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) (_hX : X = mcell k V ul) :
    VX V X ⊆ V ∩ X := by
  by_cases hn : nullSet X
  · intro x hx
    simp only [VX, if_pos hn] at hx
    exact hx.elim
  · rw [hdtfnfz_p4 _hs _hp _hb _hX hn]

/-- bump.hl:248. -/
theorem HDTFNFZ_ALT (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul)
    (_hX : X = mcell k V ul) (_hn : ¬nullSet X) :
    VX V X = V ∩ X := by
  exact hdtfnfz_p4 _hs _hp _hb _hX _hn

/-- bump.hl:262. -/
theorem VORONOI_V (V : Set V3) (w : V3) (hw : w ∈ V) :
    V ∩ voronoiClosed V w = {w} := by
  ext x
  have hwx : dist w w = 0 := dist_self w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hV, hv⟩
    have := hv x hV
    simpa [hwx] using this
  · rintro rfl
    exact ⟨hw, fun v _ => by rw [dist_self]; exact dist_nonneg⟩

/-- bump.hl:273. -/
theorem V_CELL0_EMPTY (V : Set V3) (vl : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 vl) :
    V ∩ mcell0 V vl = ∅ := by
  rw [mcell0_dispatch_p4]
  exact LEPJBDJ_0 V vl _hs _hp _hb

/-- bump.hl:300. -/
theorem V_CELL1_SINGLE (V : Set V3) (vl : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 vl) :
    V ∩ mcell1 V vl ⊆ {hdV vl} := by
  by_cases h0 : mcell 1 V vl = ∅
  · simp [mcell1_dispatch_p4, h0]
  · have hkey := LEPJBDJ V vl 1 _hs _hp _hb (by omega) (by omega) h0
    rw [mcell1_dispatch_p4, hkey,
      setOfList_truncateSimplex0_p4 (by have := _hb.1; omega)]

/-- bump.hl:327. -/
theorem EDGE_IMP_K2 (V : Set V3) (vl : List V3) (k : ℕ) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 vl) (_hk : k ≤ 1) :
    edgeX V (mcell k V vl) = ∅ := by
  have hVX0 : ∀ X : Set V3, nullSet X → VX V X = ∅ := by
    intro X hn
    simp only [VX, if_pos hn]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: the vertex set is empty (LEPJBDJ_0)
    have hVX : VX V (mcell 0 V vl) = ∅ := by
      by_cases hn : nullSet (mcell 0 V vl)
      · exact hVX0 _ hn
      · rw [hdtfnfz_p4 _hs _hp _hb rfl hn, LEPJBDJ_0 V vl _hs _hp _hb]
    rw [edgeX_empty_p4 hVX]
  · -- k = 1: the vertex set is empty (null case) or the singleton {hdV vl}
    have hk1 : k = 1 := by omega
    subst hk1
    by_cases hn : nullSet (mcell 1 V vl)
    · rw [edgeX_empty_p4 (hVX0 _ hn)]
    · have hne : mcell 1 V vl ≠ ∅ := by
        intro hc
        refine hn ?_
        rw [hc]
        exact MeasureTheory.measure_empty
      have hVX : VX V (mcell 1 V vl) ⊆ {hdV vl} := by
        rw [hdtfnfz_p4 _hs _hp _hb rfl hn,
          LEPJBDJ V vl 1 _hs _hp _hb (by omega) (by omega) hne,
          setOfList_truncateSimplex0_p4 (by have := _hb.1; omega)]
      rw [edgeX_subsingleton_p4 hVX]

/-- bump.hl:358. -/
theorem MCELL2_VERTEX (V : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) :
    VX V (mcell2 V ul) ⊆ {elV ul 0, elV ul 1} := by
  have hdis : mcell2 V ul = mcell 2 V ul := by simp [mcell]
  rw [hdis]
  by_cases hn : nullSet (mcell 2 V ul)
  · simp only [VX, if_pos hn]
    exact Set.empty_subset _
  · have hne : mcell 2 V ul ≠ ∅ := by
      intro hc
      refine hn ?_
      rw [hc]
      exact MeasureTheory.measure_empty
    rw [hdtfnfz_p4 _hs _hp _hb rfl hn,
      LEPJBDJ V ul 2 _hs _hp _hb (by omega) (by omega) hne,
      show (2 : ℕ) - 1 = 1 from rfl,
      SET_OF_LIST_TRUNCATE_1 ul (by have := _hb.1; omega)]

/-- bump.hl:428. -/
theorem MCELL2_EDGE (V : Set V3) (ul : List V3) (e : Set V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_he : e ∈ edgeX V (mcell2 V ul)) :
    e = {elV ul 0, elV ul 1} := by
  obtain ⟨u, v, rfl, hu, hv, huv⟩ := _he
  have hsub : VX V (mcell2 V ul) ⊆ {elV ul 0, elV ul 1} :=
    MCELL2_VERTEX V ul _hs _hp _hb
  have hu' : u = elV ul 0 ∨ u = elV ul 1 := by
    rcases Set.mem_insert_iff.1 (hsub hu) with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.1 h)
  have hv' : v = elV ul 0 ∨ v = elV ul 1 := by
    rcases Set.mem_insert_iff.1 (hsub hv) with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.1 h)
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact absurd rfl huv
  · rfl
  · ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · exact absurd rfl huv

/-- bump.hl:448. -/
theorem MCELL4 (V : Set V3) (ul : List V3) : mcell4 V ul = mcell 4 V ul := by
  simp [mcell]

/-- bump.hl:456. -/
theorem MCELL3 (V : Set V3) (ul : List V3) : mcell3 V ul = mcell 3 V ul := by
  simp [mcell]

/-- bump.hl:464. -/
theorem MCELL2 (V : Set V3) (ul : List V3) : mcell2 V ul = mcell 2 V ul := by
  simp [mcell]

/-- bump.hl:472. -/
theorem MCELL1 (V : Set V3) (ul : List V3) : mcell1 V ul = mcell 1 V ul := by
  simp [mcell]

/-- bump.hl:480. -/
theorem MCELL0 (V : Set V3) (ul : List V3) : mcell0 V ul = mcell 0 V ul := by
  simp [mcell]

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:488. -/
theorem MCELL_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
    (_hk : k ≤ 4) (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell k V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = k := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:513. -/
theorem MCELL4_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 4 := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:523. -/
theorem MCELL3_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 3 := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:533. -/
theorem MCELL2_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell2 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 2 := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:543. -/
theorem MCELL_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3) (k : ℕ)
    (_hk : k ≤ 4) (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell k V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell k V vl ∧ barV V 3 vl := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:568. -/
theorem MCELL4_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell4 V vl ∧ barV V 3 vl := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:580. -/
theorem MCELL3_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell3 V vl ∧ barV V 3 vl := by sorry

  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

/-- bump.hl:592. -/
theorem MCELL2_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell2 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell2 V vl ∧ barV V 3 vl := by sorry

/-- bump.hl:604. -/
theorem MCELL4_VX (V : Set V3) (ul : List V3) (X : Set V3) (_hp : Packing V)
    (_hs : saturated V) (_hX : X = mcell4 V ul) (_hb : barV V 3 ul) :
    VX V X ⊆ setOfList (cellParams V X).2 := by
  obtain ⟨h4, hbar', -⟩ :=
    cellParams_spec_p4 (k := 4) (ul := ul) (X := X) _hb (by rw [_hX]; simp [mcell])
  by_cases hn : nullSet X
  · intro x hx
    simp only [VX, if_pos hn] at hx
    exact hx.elim
  · intro x hx
    simp only [VX, if_neg hn] at hx
    by_cases h0 : (cellParams V X).1 = 0
    · rw [if_pos h0] at hx
      exact hx.elim
    · rw [if_neg h0] at hx
      exact setOfList_initialSublist_p4
        (truncateSimplex_spec_p4 (ul := (cellParams V X).2)
          (j := (cellParams V X).1 - 1) (by have := hbar'.1; have := h4; omega)).2 hx

/-- bump.hl:629. -/
  -- NEEDS (AJRIPQN-port): 唯一缺口 = Ajripqn.AJRIPQN 的「i = j」半支
  -- (cellParams 唯一性)。HOL 原文 Ajripqn.hl:89-1048，消费点 bump.hl:488。
  -- 缺件：SLTSTLO2(PA13:428 GIANT)/DDZUPHJ(PA13:457)/QZKSYKG1-2(PA14 GIANT) 仍未证；
  -- GLTVHUM_concl(PA2:3458)/DUUNHOR_concl(PA2:3500)/SLTSTLO1(PA13) 均已证
  -- （2026-10-08 收割波核实）；TIWWFYQ(PA5)/RVFXZBU(PA10) 已证。
  -- PA17:310 已备忠实陈述+全套已证辅助 kit。

theorem MCELL3_VX (V : Set V3) (ul : List V3) (X : Set V3) (_hp : Packing V)
    (_hs : saturated V) (_hX : X = mcell3 V ul) (_hb : barV V 3 ul) :
    VX V X ⊆ setOfList (truncateSimplex 2 (cellParams V X).2) := by sorry

/-- bump.hl:648. -/
theorem MCELL4_SET_OF_LIST_VX (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hn : ¬nullSet X) (_hb : barV V 3 ul) :
    setOfList ul = V ∩ X := by
  have hne : mcell4 V ul ≠ ∅ := by
    intro hc
    refine _hn ?_
    rw [_hX, hc]
    exact MeasureTheory.measure_empty
  rw [_hX, show mcell4 V ul = mcell 4 V ul from by simp [mcell],
    LEPJBDJ V ul 4 _hs _hp _hb (by omega) (by omega) hne,
    ← setOfList_truncateSimplex3_p4 (by have := _hb.1; omega)]

/-- bump.hl:694. -/
theorem MCELL3_SET_OF_LIST_VX (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hn : ¬nullSet X) (_hb : barV V 3 ul) :
    setOfList (truncateSimplex 2 ul) = V ∩ X := by
  have hne : mcell3 V ul ≠ ∅ := by
    intro hc
    refine _hn ?_
    rw [_hX, hc]
    exact MeasureTheory.measure_empty
  rw [_hX, show mcell3 V ul = mcell 3 V ul from by simp [mcell],
    LEPJBDJ V ul 3 _hs _hp _hb (by omega) (by omega) hne,
    show (3 : ℕ) - 1 = 2 from rfl]

/-- bump.hl:766. -/
theorem MCELL4_EDGE (V : Set V3) (ul : List V3) (u v : V3) (_hp : Packing V)
    (_hs : saturated V) (_hn : ¬nullSet (mcell4 V ul)) (_hb : barV V 3 ul) :
    ({u, v} : Set V3) ∈ edgeX V (mcell4 V ul) ↔
      u ≠ v ∧ {u, v} ⊆ setOfList ul := by
  have hdis : mcell4 V ul = mcell 4 V ul := by simp [mcell]
  have hn' : ¬nullSet (mcell 4 V ul) := fun hc => _hn (by rw [hdis]; exact hc)
  have hne : mcell 4 V ul ≠ ∅ := fun hc =>
    hn' (by rw [hc]; exact MeasureTheory.measure_empty)
  have hvx : VX V (mcell 4 V ul) = setOfList ul := by
    rw [hdtfnfz_p4 _hs _hp _hb rfl hn',
      LEPJBDJ V ul 4 _hs _hp _hb (by omega) (by omega) hne,
      setOfList_truncateSimplex3_p4 (by have := _hb.1; omega)]
  rw [hdis]
  exact edgeX_pair_iff_p4 hvx

/-- bump.hl:786. -/
theorem MCELL3_EDGE (V : Set V3) (ul : List V3) (u v : V3) (_hp : Packing V)
    (_hs : saturated V) (_hn : ¬nullSet (mcell3 V ul)) (_hb : barV V 3 ul) :
    ({u, v} : Set V3) ∈ edgeX V (mcell3 V ul) ↔
      u ≠ v ∧ {u, v} ⊆ setOfList (truncateSimplex 2 ul) := by
  have hdis : mcell3 V ul = mcell 3 V ul := by simp [mcell]
  have hn' : ¬nullSet (mcell 3 V ul) := fun hc => _hn (by rw [hdis]; exact hc)
  have hne : mcell 3 V ul ≠ ∅ := fun hc =>
    hn' (by rw [hc]; exact MeasureTheory.measure_empty)
  have hvx : VX V (mcell 3 V ul) = setOfList (truncateSimplex 2 ul) := by
    rw [hdtfnfz_p4 _hs _hp _hb rfl hn',
      LEPJBDJ V ul 3 _hs _hp _hb (by omega) (by omega) hne]
  rw [hdis]
  exact edgeX_pair_iff_p4 hvx

/-- bump.hl:806. -/
theorem EDGE_MCELL_EL (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X) :
    ∃ u v : V3, e = {u, v} ∧ u ≠ v := by
  obtain ⟨u, v, rfl, -, -, huv⟩ := he
  exact ⟨u, v, rfl, huv⟩

/-- bump.hl:816. -/
theorem MCELL_EDGE (V : Set V3) (ul : List V3) (k : ℕ) (e : Set V3) (_hk : k < 4)
    (_hp : Packing V) (_hs : saturated V) (_hn : ¬nullSet (mcell k V ul))
    (_hb : barV V 3 ul) (_he : e ∈ edgeX V (mcell k V ul)) :
    e ⊆ setOfList (truncateSimplex 2 ul) := by
  have hne : mcell k V ul ≠ ∅ := by
    intro hc
    refine _hn ?_
    rw [hc]
    exact MeasureTheory.measure_empty
  have hle : 3 ≤ ul.length := by have := _hb.1; omega
  obtain ⟨p, q, rfl, hp, hq, -⟩ := _he
  have hVX : VX V (mcell k V ul) = V ∩ mcell k V ul :=
    hdtfnfz_p4 _hs _hp _hb rfl _hn
  have hp' : p ∈ V ∩ mcell k V ul := by rw [← hVX]; exact hp
  have hq' : q ∈ V ∩ mcell k V ul := by rw [← hVX]; exact hq
  interval_cases k
  · rw [LEPJBDJ_0 V ul _hs _hp _hb] at hp'
    exact hp'.elim
  · rw [LEPJBDJ V ul 1 _hs _hp _hb (by omega) (by omega) hne,
      setOfList_truncateSimplex0_p4 (by have := _hb.1; omega)] at hp' hq'
    rw [SET_OF_LIST_TRUNCATE_2 ul hle]
    intro y hy
    rcases Set.mem_insert_iff.1 hy with hxe | hxe
    · rw [hxe, Set.mem_singleton_iff.1 hp', hdV_elV_p4]
      simp
    · rw [hxe, Set.mem_singleton_iff.1 hq', hdV_elV_p4]
      simp
  · rw [LEPJBDJ V ul 2 _hs _hp _hb (by omega) (by omega) hne,
      show (2 : ℕ) - 1 = 1 from rfl,
      SET_OF_LIST_TRUNCATE_1 ul (by have := _hb.1; omega)] at hp' hq'
    rw [SET_OF_LIST_TRUNCATE_2 ul hle]
    intro y hy
    have hsub21 : ({elV ul 0, elV ul 1} : Set V3) ⊆ {elV ul 0, elV ul 1, elV ul 2} := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with h | h
      · rw [h]
        simp
      · rw [Set.mem_singleton_iff.1 h]
        simp
    rcases Set.mem_insert_iff.1 hy with hxe | hxe
    · rw [hxe]
      exact hsub21 hp'
    · rw [Set.mem_singleton_iff.1 hxe]
      exact hsub21 hq'
  · rw [LEPJBDJ V ul 3 _hs _hp _hb (by omega) (by omega) hne,
      show (3 : ℕ) - 1 = 2 from rfl,
      SET_OF_LIST_TRUNCATE_2 ul hle] at hp' hq'
    rw [SET_OF_LIST_TRUNCATE_2 ul hle]
    intro y hy
    rcases Set.mem_insert_iff.1 hy with hxe | hxe
    · rw [hxe]
      exact hp'
    · rw [Set.mem_singleton_iff.1 hxe]
      exact hq'

/-- bump.hl:871. -/
theorem CARD2_EDGEX (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X) :
    Nat.card e = 2 := by
  obtain ⟨u, v, rfl, huv⟩ := EDGE_MCELL_EL V X e he
  classical
  rw [Nat.card_eq_fintype_card]
  have hfin : Fintype ↑({u, v} : Set V3) :=
    @Fintype.ofFinite _ (Set.toFinite ({u, v} : Set V3))
  simp [huv]

/-- bump.hl:882. -/
theorem DIFF_EDGEX (V : Set V3) (X : Set V3) (ul : List V3) (k : ℕ) (e : Set V3)
    (_hk : k < 4) (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell k V ul)
    (_hn : ¬nullSet X) (_hb : barV V 3 ul) (_he : e ∈ edgeX V X) :
    VX V X \ e ∉ edgeX V X := by
  -- AJRIPQN-port note: direct pigeonhole — both `e` and `VX \ e` sit inside
  -- the 3-point truncation set (MCELL_EDGE twice), are disjoint, and carry
  -- two distinct points each: four distinct points in a three-point set.
  intro hcon
  rw [_hX] at _he hcon
  have hn' : ¬nullSet (mcell k V ul) := by rw [← _hX]; exact _hn
  obtain ⟨p, q, rfl, hp, hq, hpq⟩ := _he
  obtain ⟨p', q', heq', hp', hq', hpq'⟩ := hcon
  have hp'sub : p' ∈ VX V (mcell k V ul) \ ({p, q} : Set V3) := by rw [heq']; simp
  have hq'sub : q' ∈ VX V (mcell k V ul) \ ({p, q} : Set V3) := by rw [heq']; simp
  have hd1 : p' ≠ p ∧ p' ≠ q := by
    have h1 : p' ∉ ({p, q} : Set V3) ∧ p' ∈ VX V (mcell k V ul) := by
      simp only [Set.mem_sdiff] at hp'sub
      tauto
    exact ⟨fun h => h1.1 (by simp [h]), fun h => h1.1 (by simp [h])⟩
  have hd2 : q' ≠ p ∧ q' ≠ q := by
    have h1 : q' ∉ ({p, q} : Set V3) ∧ q' ∈ VX V (mcell k V ul) := by
      simp only [Set.mem_sdiff] at hq'sub
      tauto
    exact ⟨fun h => h1.1 (by simp [h]), fun h => h1.1 (by simp [h])⟩
  have hE : ({p, q} : Set V3) ⊆ setOfList (truncateSimplex 2 ul) :=
    MCELL_EDGE V ul k ({p, q}) _hk _hp _hs hn' _hb (⟨p, q, rfl, hp, hq, hpq⟩)
  have hE' : (VX V (mcell k V ul) \ ({p, q} : Set V3))
      ⊆ setOfList (truncateSimplex 2 ul) :=
    MCELL_EDGE V ul k (VX V (mcell k V ul) \ {p, q}) _hk _hp _hs hn' _hb
      (⟨p', q', heq', hp', hq', hpq'⟩)
  rw [heq'] at hE'
  have hS : ({p, q, p', q'} : Set V3) ⊆ setOfList (truncateSimplex 2 ul) := by
    intro z hz
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · exact hE (by rw [hz]; simp)
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · exact hE (by rw [hz]; simp)
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · exact hE' (by rw [hz]; simp)
    · exact hE' (by rw [hz]; simp)
  have hsub : ({p, q, p', q'} : Set V3)
      ⊆ ({elV ul 0, elV ul 1, elV ul 2} : Set V3) := by
    intro z hz
    have hz' : z ∈ setOfList (truncateSimplex 2 ul) := hS hz
    rw [SET_OF_LIST_TRUNCATE_2 ul (by have := _hb.1; omega)] at hz'
    exact hz'
  have h4 : ({p, q, p', q'} : Set V3).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (s := ({q, p', q'} : Set V3))
        (by simp [hpq, Ne.symm hd1.1, Ne.symm hd1.2, Ne.symm hd2.1, Ne.symm hd2.2]),
      Set.ncard_insert_of_notMem (s := ({p', q'} : Set V3))
        (by simp [hpq', Ne.symm hd1.2, Ne.symm hd2.2]),
      Set.ncard_insert_of_notMem (s := ({q'} : Set V3)) (by simp [hpq'])]
    simp
  have h3 : ({elV ul 0, elV ul 1, elV ul 2} : Set V3).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (s := ({elV ul 1, elV ul 2} : Set V3))
        (by simp [barV_elV_ne_p4 _hb (i := 0) (j := 1) (by omega) (by omega) (by omega),
          barV_elV_ne_p4 _hb (i := 0) (j := 2) (by omega) (by omega) (by omega)]),
      Set.ncard_insert_of_notMem (s := ({elV ul 2} : Set V3))
        (by simp [barV_elV_ne_p4 _hb (i := 1) (j := 2) (by omega) (by omega) (by omega)])]
    simp
  have hle : ({p, q, p', q'} : Set V3).ncard
      ≤ ({elV ul 0, elV ul 1, elV ul 2} : Set V3).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h4, h3] at hle
  exact absurd hle (by omega)

/-- bump.hl:940 (`MCELL_BUMP_0`; the bump.hl:851 twin is its commented
`beta_bumpA` predecessor). -/
theorem MCELL_BUMP_0 (V : Set V3) (ul : List V3) (e : Set V3) (k : ℕ)
    (_hk : k < 4) (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul)
    (_hn : ¬nullSet (mcell k V ul)) :
    betaBump V e (mcell k V ul) = 0 := by
  -- AJRIPQN-port note: discharged WITHOUT the cellParams-uniqueness cluster —
  -- the bump condition needs BOTH `e` and `e' = VX \ e` critical, and either
  -- `e ∈ edgeX` (then DIFF_EDGEX kills `e' ∈ edgeX`) or `e ∉ edgeX` (then
  -- `e ∉ criticalEdgeX` by the defining setOf) makes the condition fail.
  by_cases he : e ∈ edgeX V (mcell k V ul)
  · have hdiff : VX V (mcell k V ul) \ e ∉ edgeX V (mcell k V ul) :=
      DIFF_EDGEX V (mcell k V ul) ul k e _hk _hp _hs rfl _hn _hb he
    simp only [betaBump]
    rw [if_neg (fun hcon => by
      have hc := hcon.2.2.2.1
      simp only [criticalEdgeX, Set.mem_setOf_eq] at hc
      obtain ⟨u, v, -, hxe, -, -⟩ := hc
      exact hdiff hxe)]
  · simp only [betaBump]
    rw [if_neg (fun hcon => by
      have hc := hcon.2.2.1
      simp only [criticalEdgeX, Set.mem_setOf_eq] at hc
      obtain ⟨u, v, -, hxe, -, -⟩ := hc
      exact he hxe)]

/-- bump.hl:920. -/
theorem CRITICAL_EDGEX_ALT (V : Set V3) (X : Set V3) (e : Set V3) :
    e ∈ criticalEdgeX V X ↔ e ∈ edgeX V X ∧ hminus ≤ radV e ∧ radV e ≤ hplus := by
  have hlr : ∀ u v : V3, hl [u, v] = radV ({u, v} : Set V3) := by
    intro u v
    simp only [hl, setOfList]
    congr 1
    ext x
    simp
  simp only [criticalEdgeX, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, v, rfl, he, hlo, hhi⟩
    rw [hlr u v] at hlo hhi
    exact ⟨he, hlo, hhi⟩
  · rintro ⟨he, hlo, hhi⟩
    obtain ⟨u, v, rfl, -, -, -⟩ :=
      (fun hx : e ∈ edgeX V X =>
        (hx : ∃ u v : V3, e = {u, v} ∧ u ∈ VX V X ∧ v ∈ VX V X ∧ u ≠ v)) he
    rw [← hlr u v] at hlo hhi
    exact ⟨u, v, rfl, he, hlo, hhi⟩

/-- bump.hl:930. -/
theorem SUBCRITICAL_EDGEX_ALT (V : Set V3) (X : Set V3) (e : Set V3) :
    e ∈ subcriticalEdgeX V X ↔ e ∈ edgeX V X ∧ radV e < hminus := by
  have hlr : ∀ u v : V3, hl [u, v] = radV ({u, v} : Set V3) := by
    intro u v
    simp only [hl, setOfList]
    congr 1
    ext x
    simp
  simp only [subcriticalEdgeX, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, v, rfl, he, hlo⟩
    rw [hlr u v] at hlo
    exact ⟨he, hlo⟩
  · rintro ⟨he, hlo⟩
    obtain ⟨u, v, rfl, -, -, -⟩ :=
      (fun hx : e ∈ edgeX V X =>
        (hx : ∃ u v : V3, e = {u, v} ∧ u ∈ VX V X ∧ v ∈ VX V X ∧ u ≠ v)) he
    rw [← hlr u v] at hlo
    exact ⟨u, v, rfl, he, hlo⟩

/-- bump.hl:956. -/
theorem MCELL4_EDGE_OPP (V : Set V3) (ul : List V3) (_hp : Packing V)
    (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul)) :
    VX V (mcell4 V ul) \ {elV ul 0, elV ul 1} = {elV ul 2, elV ul 3} := by
  have hdis : mcell4 V ul = mcell 4 V ul := by simp [mcell]
  have hn' : ¬nullSet (mcell 4 V ul) := fun hc => _hn (by rw [hdis]; exact hc)
  have hne : mcell 4 V ul ≠ ∅ := fun hc =>
    hn' (by rw [hc]; exact MeasureTheory.measure_empty)
  have hvx : VX V (mcell 4 V ul) = setOfList ul := by
    rw [hdtfnfz_p4 _hs _hp _hb rfl hn',
      LEPJBDJ V ul 4 _hs _hp _hb (by omega) (by omega) hne,
      setOfList_truncateSimplex3_p4 (by have := _hb.1; omega)]
  rw [hdis, hvx]
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul _hb
  subst hul
  have hE0 : elV [u0, u1, u2, u3] 0 = u0 := rfl
  have hE1 : elV [u0, u1, u2, u3] 1 = u1 := rfl
  have hE2 : elV [u0, u1, u2, u3] 2 = u2 := rfl
  have hE3 : elV [u0, u1, u2, u3] 3 = u3 := rfl
  have hset : setOfList [u0, u1, u2, u3]
      = {elV [u0, u1, u2, u3] 0, elV [u0, u1, u2, u3] 1,
          elV [u0, u1, u2, u3] 2, elV [u0, u1, u2, u3] 3} := by
    rw [hE0, hE1, hE2, hE3]
    ext x
    simp [setOfList]
  have d02 : u2 ≠ u0 := by
    simpa [elV] using barV_elV_ne_p4 _hb (i := 2) (j := 0) (by omega) (by omega) (by omega)
  have d03 : u3 ≠ u0 := by
    simpa [elV] using barV_elV_ne_p4 _hb (i := 3) (j := 0) (by omega) (by omega) (by omega)
  have d12 : u2 ≠ u1 := by
    simpa [elV] using barV_elV_ne_p4 _hb (i := 2) (j := 1) (by omega) (by omega) (by omega)
  have d13 : u3 ≠ u1 := by
    simpa [elV] using barV_elV_ne_p4 _hb (i := 3) (j := 1) (by omega) (by omega) (by omega)
  ext x
  rw [hset, Set.mem_sdiff, hE0, hE1, hE2, hE3]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨h4, hn0, hn1⟩
    rcases h4 with h0 | h1 | h2 | h3
    · exact absurd h0 hn0
    · exact absurd h1 hn1
    · exact Or.inl h2
    · exact Or.inr h3
  · intro hx
    rcases hx with hxe | hxe
    · have hx2 : x = u2 := hxe
      exact ⟨by simp [hx2], fun hc => d02 (hx2.symm.trans hc),
        fun hc => d12 (hx2.symm.trans hc)⟩
    · have hx3 : x = u3 := Set.mem_singleton_iff.1 hxe
      exact ⟨by simp [hx3], fun hc => d03 (hx3.symm.trans hc),
        fun hc => d13 (hx3.symm.trans hc)⟩

/-- bump.hl:999. -/
theorem MCELL_BUMP_OPP (V : Set V3) (ul : List V3) (_hp : Packing V)
    (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul))
    (_hc : ({elV ul 2, elV ul 3} : Set V3) ∉ criticalEdgeX V (mcell4 V ul)) :
    betaBump V {elV ul 0, elV ul 1} (mcell4 V ul) = 0 := by
  have hopp : VX V (mcell4 V ul) \ {elV ul 0, elV ul 1} = {elV ul 2, elV ul 3} :=
    MCELL4_EDGE_OPP V ul _hp _hs _hb _hn
  simp only [betaBump, hopp]
  rw [if_neg (fun hcon => _hc hcon.2.2.2.1)]

/-- bump.hl:1051. -/
theorem BETA_BUMP_INVOLUTION (V : Set V3) (X : Set V3) (r : Set V3 → Set V3)
    (e : Set V3) (_hs : saturated V) (_hp : Packing V) (_hm : X ∈ mcellSet V)
    (_he : e ∈ criticalEdgeX V X) (hr : (fun e => VX V X \ e) = r) :
    r (r e) = e := by
  have hsub : e ⊆ VX V X := by
    obtain ⟨u, v, rfl, hu, -, -⟩ := _he
    simp only [edgeX, Set.mem_setOf_eq] at hu
    obtain ⟨w, w', heq, hw, hw', -⟩ := hu
    have h1 : u ∈ ({u, v} : Set V3) := by simp
    have h2 : v ∈ ({u, v} : Set V3) := by simp
    rw [heq] at h1 h2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rcases (by simpa using h1 : x = w ∨ x = w') with hue | hue
      · subst hue; exact hw
      · subst hue; exact hw'
    · rcases (by simpa using h2 : x = w ∨ x = w') with hve | hve
      · subst hve; exact hw
      · subst hve; exact hw'
  rw [← hr]
  show VX V X \ (VX V X \ e) = e
  ext x
  simp only [Set.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hc
    exact h2 ⟨h1, hc⟩
  · intro hx
    refine ⟨hsub hx, ?_⟩
    intro hcon
    exact hcon.2 hx

/-- bump.hl:1069. -/
theorem BETA_BUMP_ALT (V : Set V3) (X : Set V3) (r : Set V3 → Set V3) (e : Set V3)
    (_hs : saturated V) (_hp : Packing V) (_hm : X ∈ mcellSet V)
    (hr : (fun e => VX V X \ e) = r) :
    betaBump V e X =
      if ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧ r e ∈ criticalEdgeX V X ∧
          (∀ f ∈ edgeX V X, f = e ∨ f = r e ∨ f ∈ subcriticalEdgeX V X) then
        bump (radV e) - bump (radV (r e))
      else 0 := by
  have hr' : ∀ w : Set V3, r w = VX V X \ w := fun w => by rw [← hr]
  simp only [betaBump]
  rw [hr']
  by_cases hc : ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧ VX V X \ e ∈ criticalEdgeX V X ∧
      (∀ f ∈ edgeX V X, f = e ∨ f = VX V X \ e ∨ f ∈ subcriticalEdgeX V X)
  · have hcond : X ∈ mcellSet V ∧ ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧
      VX V X \ e ∈ criticalEdgeX V X ∧
      (∀ f ∈ edgeX V X, f = e ∨ f = VX V X \ e ∨ f ∈ subcriticalEdgeX V X) := ⟨_hm, hc⟩
    rw [if_pos hcond, if_pos hc]
  · rw [if_neg (fun hconj => hc ⟨hconj.2.1, hconj.2.2.1, hconj.2.2.2.1, hconj.2.2.2.2⟩),
      if_neg hc]

/-- bump.hl:1086. -/
theorem BETA_BUMP_INVOLUTION_CRITICAL (V : Set V3) (X : Set V3)
    (r : Set V3 → Set V3) (e : Set V3) (_hs : saturated V) (_hp : Packing V)
    (_hm : X ∈ mcellSet V) (_he : e ∈ criticalEdgeX V X)
    (_hb : betaBump V e X ≠ 0) (hr : (fun e => VX V X \ e) = r) :
    r e ∈ criticalEdgeX V X := by
  have hr' : ∀ w : Set V3, r w = VX V X \ w := fun w => by rw [← hr]
  by_contra hcon
  simp only [betaBump] at _hb
  rw [if_neg (fun hconj => hcon (by rw [hr']; exact hconj.2.2.2.1))] at _hb
  exact _hb rfl

/-- bump.hl:1100. -/
theorem BETA_BUMP_INVOLUTION_NEG (V : Set V3) (X : Set V3) (r : Set V3 → Set V3)
    (e : Set V3) (_hs : saturated V) (_hp : Packing V) (_hm : X ∈ mcellSet V)
    (_he : e ∈ criticalEdgeX V X) (_hb : betaBump V e X ≠ 0)
    (hr : (fun e => VX V X \ e) = r) :
    betaBump V (r e) X = -betaBump V e X := by
  have hr' : ∀ w : Set V3, r w = VX V X \ w := fun w => by rw [← hr]
  have hsub : e ⊆ VX V X := by
    simp only [criticalEdgeX, Set.mem_setOf_eq] at _he
    obtain ⟨u, v, rfl, hxe, -, -⟩ := _he
    obtain ⟨w, w', heq, hw, hw', -⟩ := hxe
    have hu' : u = w ∨ u = w' := by
      have hmem : u ∈ ({w, w'} : Set V3) := by rw [← heq]; simp
      simpa using hmem
    have hv' : v = w ∨ v = w' := by
      have hmem : v ∈ ({w, w'} : Set V3) := by rw [← heq]; simp
      simpa using hmem
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | rfl
    · rcases hu' with h | h
      · rw [h]
        exact hw
      · rw [h]
        exact hw'
    · rcases hv' with h | h
      · rw [h]
        exact hw
      · rw [h]
        exact hw'
  have hE0 : VX V X \ (VX V X \ e) = e := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hx
      exact h2 ⟨h1, hx⟩
    · intro hx
      exact ⟨hsub hx, fun h => h.2 hx⟩
  have hcond : X ∈ mcellSet V ∧ ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧
      VX V X \ e ∈ criticalEdgeX V X ∧
      ∀ f ∈ edgeX V X, f = e ∨ f = VX V X \ e ∨ f ∈ subcriticalEdgeX V X := by
    by_contra hcf
    simp only [betaBump] at _hb
    rw [if_neg (fun hconj => hcf ⟨hconj.1, hconj.2.1, hconj.2.2.1, hconj.2.2.2.1,
      hconj.2.2.2.2⟩)] at _hb
    exact _hb rfl
  have hc2 : X ∈ mcellSet V ∧ ¬nullSet X ∧ VX V X \ e ∈ criticalEdgeX V X ∧
      e ∈ criticalEdgeX V X ∧
      ∀ f ∈ edgeX V X, f = VX V X \ e ∨ f = e ∨ f ∈ subcriticalEdgeX V X :=
    ⟨hcond.1, hcond.2.1, hcond.2.2.2.1, hcond.2.2.1, fun f hf => by
      rcases hcond.2.2.2.2 f hf with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)⟩
  simp only [betaBump, hr', hE0]
  rw [if_pos hc2, if_pos hcond]
  ring

/-- bump.hl:1129. -/
theorem BETA_BUMP_INVOLUTION_BIJ (V : Set V3) (X : Set V3) (s : Set (Set V3))
    (r : Set V3 → Set V3) (_hs : saturated V) (_hp : Packing V)
    (_hm : X ∈ mcellSet V)
    (_hsdef : {e | e ∈ criticalEdgeX V X ∧ betaBump V e X ≠ 0} = s)
    (hr : (fun e => VX V X \ e) = r) :
    BIJP4 r s s := by
  have hmem : ∀ e ∈ s, e ∈ criticalEdgeX V X ∧ betaBump V e X ≠ 0 := by
    intro e he
    rw [← _hsdef] at he
    exact he
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hcrit, hne⟩ := hmem e he
    have hrc := BETA_BUMP_INVOLUTION_CRITICAL V X r e _hs _hp _hm hcrit hne hr
    have hrne := BETA_BUMP_INVOLUTION_NEG V X r e _hs _hp _hm hcrit hne hr
    rw [← _hsdef]
    refine ⟨hrc, fun hzero => hne ?_⟩
    rw [hrne] at hzero
    linarith
  · intro e he f hf hcon
    have h1 := BETA_BUMP_INVOLUTION V X r e _hs _hp _hm (hmem e he).1 hr
    have h2 := BETA_BUMP_INVOLUTION V X r f _hs _hp _hm (hmem f hf).1 hr
    rw [← h1, ← h2, hcon]
  · intro y hy
    obtain ⟨hcrit, hne⟩ := hmem y hy
    have hrcy := BETA_BUMP_INVOLUTION_CRITICAL V X r y _hs _hp _hm hcrit hne hr
    have hrny := BETA_BUMP_INVOLUTION_NEG V X r y _hs _hp _hm hcrit hne hr
    rw [← _hsdef]
    refine ⟨r y, ⟨hrcy, fun hzero => hne ?_⟩, ?_⟩
    · rw [hrny] at hzero
      linarith
    · exact BETA_BUMP_INVOLUTION V X r y _hs _hp _hm hcrit hr

/-- bump.hl:1169. -/
theorem SUM_BETA_BUMP_LEMMA (V : Set V3) (X : Set V3) (_hs : saturated V)
    (_hp : Packing V) (_hm : X ∈ mcellSet V) :
    setSum {e | e ∈ criticalEdgeX V X} (fun e => betaBump V e X) = 0 := by
  classical
  set r : Set V3 → Set V3 := fun e => VX V X \ e with hrdef
  have hr' : (fun e => VX V X \ e) = r := rfl
  -- the vertex set of `X` is (empty or) a list-point-set, hence finite
  have hfinVX : (VX V X).Finite := by
    by_cases hn : nullSet X
    · simp only [VX, if_pos hn]
      exact Set.finite_empty
    · simp only [VX, if_pos hn]
      split_ifs
      · exact Set.finite_empty
      · exact Set.Finite.ofFinset
          (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset
          (fun x => by simp [setOfList])
  have hfinE : (edgeX V X).Finite := by
    have hsub : edgeX V X
        ⊆ (fun p : V3 × V3 => ({p.1, p.2} : Set V3)) '' (VX V X ×ˢ VX V X) := by
      rintro e ⟨u, v, rfl, hu, hv, -⟩
      exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
    exact (Set.Finite.image _ (hfinVX.prod hfinVX)).subset hsub
  have hfin : {e : Set V3 | e ∈ criticalEdgeX V X}.Finite := by
    refine Set.Finite.subset hfinE ?_
    intro e he
    simp only [criticalEdgeX, Set.mem_setOf_eq] at he
    obtain ⟨u, v, rfl, hxe, -, -⟩ := he
    exact hxe
  haveI : Fintype ↥({e : Set V3 | e ∈ criticalEdgeX V X} : Set (Set V3)) := hfin.fintype
  set F := hfin.toFinset.filter (fun e => betaBump V e X ≠ 0) with hFdef
  -- split the sum: the `β = 0` part contributes nothing
  have hsplit : ∑ e ∈ hfin.toFinset, betaBump V e X
      = ∑ e ∈ F, betaBump V e X := by
    rw [hFdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e he => ?_)
    by_cases hm : betaBump V e X = 0
    · rw [if_neg (fun hne => absurd hm hne), hm]
    · rw [if_pos hm]
  have hFmaps : ∀ e ∈ F, r e ∈ F := by
    intro e he
    have hne : betaBump V e X ≠ 0 := (Finset.mem_filter.1 he).2
    have hcrit : e ∈ criticalEdgeX V X := by simpa using (Finset.mem_filter.1 he).1
    have hrc := BETA_BUMP_INVOLUTION_CRITICAL V X r e _hs _hp _hm hcrit hne hr'
    have hrne := BETA_BUMP_INVOLUTION_NEG V X r e _hs _hp _hm hcrit hne hr'
    refine Finset.mem_filter.2 ⟨by simpa using hrc, fun hzero => hne ?_⟩
    rw [hrne] at hzero
    linarith
  have hFinv : ∀ e ∈ F, r (r e) = e := fun e he =>
    BETA_BUMP_INVOLUTION V X r e _hs _hp _hm (by simpa using
      (Finset.mem_filter.1 he).1) hr'
  have hFpair : ∀ e ∈ F, betaBump V (r e) X = -betaBump V e X := fun e he =>
    BETA_BUMP_INVOLUTION_NEG V X r e _hs _hp _hm (by simpa using
      (Finset.mem_filter.1 he).1) (by simpa using (Finset.mem_filter.1 he).2) hr'
  have hFsum : ∑ e ∈ F, betaBump V e X = 0 := by
    have hinj : ∀ e ∈ F, ∀ f ∈ F, r e = r f → e = f := by
      intro e he f hf hcon
      rw [← hFinv e he, ← hFinv f hf, hcon]
    have hFimg : F.image r = F := by
      ext e
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact hFmaps f hf
      · intro he
        exact ⟨r e, hFmaps e he, hFinv e he⟩
    have hre : ∑ e ∈ F.image r, betaBump V e X
        = ∑ e ∈ F, betaBump V (r e) X := by
      rw [Finset.sum_image (fun x hx y hy hcon =>
        hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hcon)]
    have hFI : ∑ e ∈ F.image r, betaBump V e X
        = ∑ e ∈ F, betaBump V e X := by
      rw [hFimg]
    have hpairS : ∑ e ∈ F, betaBump V (r e) X
        = -∑ e ∈ F, betaBump V e X := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun e he => hFpair e he)
    linarith [hre, hFI, hpairS]
  rw [setSum, dif_pos hfin, hsplit, hFsum]

/-- bump.hl:1198. -/
theorem REAL_ABS_TRIANGLE_BOUND (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    abs x ≤ abs a + abs b := by
  rcases le_or_gt a 0 with ha0 | ha0
  · rcases le_or_gt 0 b with hb0 | hb0
    · rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx, abs_of_nonneg hb0]
        linarith [abs_nonneg a, abs_nonneg b]
      · rw [abs_of_nonpos (le_of_lt hx), abs_of_nonpos ha0]
        linarith [abs_nonneg b]
    · rw [abs_of_nonpos (le_of_lt (show x < 0 from by linarith)),
        abs_of_nonpos ha0, abs_of_nonpos (le_of_lt (show b < 0 from by linarith))]
      linarith
  · have h1 : 0 ≤ x := le_trans (le_of_lt ha0) ha
    have h2 : 0 ≤ b := le_trans h1 hb
    rw [abs_of_nonneg h1, abs_of_nonneg (le_of_lt ha0), abs_of_nonneg h2]
    linarith

/-- bump.hl:1206. -/
theorem CRITICAL_EDGEX_BOUND :
    ∃ c1 : ℝ, ∀ (V : Set V3) (X : Set V3) (e : Set V3),
      e ∈ criticalEdgeX V X → abs (radV e - h0) ≤ c1 := by
  refine ⟨max (abs (hminus - h0)) (abs (hplus - h0)), fun V X e he => ?_⟩
  simp only [criticalEdgeX, Set.mem_setOf_eq] at he
  obtain ⟨u, v, rfl, -, hlo, hhi⟩ := he
  have hlr : hl [u, v] = radV ({u, v} : Set V3) := by
    simp only [hl, setOfList]
    congr 1
    ext x
    simp
  rw [hlr] at hlo hhi
  rcases le_or_gt (radV ({u, v} : Set V3)) h0 with hr | hr
  · rw [abs_of_nonpos (show radV ({u, v} : Set V3) - h0 ≤ 0 from by linarith)]
    calc -(radV ({u, v} : Set V3) - h0) = h0 - radV ({u, v} : Set V3) := by ring
      _ ≤ h0 - hminus := by linarith
      _ = abs (h0 - hminus) :=
          (abs_of_nonneg (show 0 ≤ h0 - hminus from by linarith)).symm
      _ = abs (hminus - h0) := abs_sub_comm _ _
      _ ≤ max (abs (hminus - h0)) (abs (hplus - h0)) := le_max_left _ _
  · rw [abs_of_nonneg (show 0 ≤ radV ({u, v} : Set V3) - h0 from by linarith)]
    calc radV ({u, v} : Set V3) - h0 ≤ hplus - h0 := by linarith
      _ = abs (hplus - h0) :=
          (abs_of_nonneg (show 0 ≤ hplus - h0 from by linarith)).symm
      _ ≤ max (abs (hminus - h0)) (abs (hplus - h0)) := le_max_right _ _

/-- bump.hl:1219. -/
theorem ABS_BUMP (h c1 : ℝ) (hc : abs (h - h0) ≤ c1) :
    abs (bump h) ≤ abs 0.005 * (1 + c1 ^ 2 / abs ((hplus - h0) ^ 2)) := by
  have hden : (0:ℝ) < abs ((hplus - h0) ^ 2) :=
    abs_pos.mpr (pow_ne_zero 2 (show hplus - h0 ≠ 0 by norm_num [hplus, h0]))
  have hsq : abs (h - h0) ^ 2 ≤ c1 ^ 2 := by
    nlinarith [abs_nonneg (h - h0), hc]
  unfold bump
  have h1 : abs (1 - (h - h0) ^ 2 / (hplus - h0) ^ 2)
      ≤ 1 + abs ((h - h0) ^ 2) / abs ((hplus - h0) ^ 2) := by
    have hq : abs ((h - h0) ^ 2 / (hplus - h0) ^ 2)
        ≤ abs ((h - h0) ^ 2) / abs ((hplus - h0) ^ 2) := by
      rw [abs_div]
    rcases le_or_gt 1 ((h - h0) ^ 2 / (hplus - h0) ^ 2) with hx | hx
    · rw [abs_of_nonpos (by linarith)]
      linarith [le_abs_self ((h - h0) ^ 2 / (hplus - h0) ^ 2), hq]
    · rw [abs_of_pos (by linarith)]
      linarith [neg_le_abs ((h - h0) ^ 2 / (hplus - h0) ^ 2), hq]
  have hD : (0:ℝ) < (abs ((hplus - h0) ^ 2))⁻¹ := inv_pos.mpr hden
  have hsq2 : abs ((h - h0) ^ 2) ≤ c1 ^ 2 := by rw [abs_pow]; exact hsq
  have h2 : abs ((h - h0) ^ 2) / abs ((hplus - h0) ^ 2)
      ≤ c1 ^ 2 / abs ((hplus - h0) ^ 2) := by
    rw [div_eq_inv_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hsq2 (le_of_lt hD)
  calc abs (0.005 * (1 - (h - h0) ^ 2 / (hplus - h0) ^ 2))
      = abs 0.005 * abs (1 - (h - h0) ^ 2 / (hplus - h0) ^ 2) := abs_mul _ _
    _ ≤ abs 0.005 * (1 + c1 ^ 2 / abs ((hplus - h0) ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [h1, h2]) (abs_nonneg _)

/-- bump.hl:1244. -/
theorem BOUND_BETA_BUMP :
    ∃ c : ℝ, ∀ (V : Set V3) (X : Set V3) (e : Set V3), saturated V → Packing V →
      X ∈ mcellSet V → e ∈ criticalEdgeX V X → betaBump V e X ≤ c := by
  obtain ⟨c1, hc1⟩ := CRITICAL_EDGEX_BOUND
  have hbound : (0:ℝ) ≤ abs 0.005 * (1 + c1 ^ 2 / abs ((hplus - h0) ^ 2)) := by
    refine mul_nonneg (abs_nonneg _) ?_
    have h1 : (0:ℝ) ≤ c1 ^ 2 := sq_nonneg c1
    have h2 : (0:ℝ) ≤ abs ((hplus - h0) ^ 2) := abs_nonneg _
    have h3 : (0:ℝ) ≤ c1 ^ 2 / abs ((hplus - h0) ^ 2) := div_nonneg h1 h2
    linarith
  refine ⟨2 * abs 0.005 * (1 + c1 ^ 2 / abs ((hplus - h0) ^ 2)),
    fun V X e _ _ _ he => ?_⟩
  by_cases hcond : X ∈ mcellSet V ∧ ¬nullSet X ∧ e ∈ criticalEdgeX V X ∧
      VX V X \ e ∈ criticalEdgeX V X ∧
      ∀ f ∈ edgeX V X, f = e ∨ f = VX V X \ e ∨ f ∈ subcriticalEdgeX V X
  · have hb : betaBump V e X = bump (radV e) - bump (radV (VX V X \ e)) := by
      simp only [betaBump]
      rw [if_pos hcond]
    rw [hb]
    have hab := ABS_BUMP (radV e) c1 (hc1 V X e he)
    have hab' := ABS_BUMP (radV (VX V X \ e)) c1 (hc1 V X (VX V X \ e) hcond.2.2.2.1)
    calc bump (radV e) - bump (radV (VX V X \ e))
        ≤ abs (bump (radV e)) + abs (bump (radV (VX V X \ e))) := by
          linarith [le_abs_self (bump (radV e)),
            neg_le_abs (bump (radV (VX V X \ e)))]
      _ ≤ 2 * abs 0.005 * (1 + c1 ^ 2 / abs ((hplus - h0) ^ 2)) := by linarith
  · simp only [betaBump]
    rw [if_neg hcond]
    linarith

end BumpP4
