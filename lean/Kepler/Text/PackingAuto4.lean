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

/-- HL `BIJ` rendered over sets. -/
private def BIJP4 {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  Set.BijOn f s t

/-- bump.hl:25: beta reduction of an ordered-pair lambda. -/
theorem BETA_ORDERED_PAIR_THM {α β γ : Type} (g : α → β → γ) (x : α × β) :
    (fun p => g p.1 p.2) x = g x.1 x.2 := rfl

/-- bump.hl:37. -/
theorem BIJ_SUM {α β : Type} [Fintype α] [Fintype β] (A : Set α) (B : Set β)
    (f : β → ℝ) (ab : α ≃ β) (_h : Set.BijOn ab A B) :
    setSum A (fun a => f (ab a)) = setSum B f := by sorry

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
    setOfList (truncateSimplex 1 ul) = {elV ul 0, elV ul 1} := by sorry

/-- bump.hl:194. -/
theorem SET_OF_LIST_TRUNCATE_2 (ul : List V3) (h : 3 ≤ ul.length) :
    setOfList (truncateSimplex 2 ul) = {elV ul 0, elV ul 1, elV ul 2} := by sorry

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
    VX V X ⊆ V ∩ X := by sorry

/-- bump.hl:248. -/
theorem HDTFNFZ_ALT (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul)
    (_hX : X = mcell k V ul) (_hn : ¬nullSet X) :
    VX V X = V ∩ X := by sorry

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
    V ∩ mcell0 V vl = ∅ := by sorry

/-- bump.hl:300. -/
theorem V_CELL1_SINGLE (V : Set V3) (vl : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 vl) :
    V ∩ mcell1 V vl ⊆ {hdV vl} := by sorry

/-- bump.hl:327. -/
theorem EDGE_IMP_K2 (V : Set V3) (vl : List V3) (k : ℕ) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 vl) (_hk : k ≤ 1) :
    edgeX V (mcell k V vl) = ∅ := by sorry

/-- bump.hl:358. -/
theorem MCELL2_VERTEX (V : Set V3) (ul : List V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) :
    VX V (mcell2 V ul) ⊆ {elV ul 0, elV ul 1} := by sorry

/-- bump.hl:428. -/
theorem MCELL2_EDGE (V : Set V3) (ul : List V3) (e : Set V3) (_hs : saturated V)
    (_hp : Packing V) (_hb : barV V 3 ul) (_he : e ∈ edgeX V (mcell2 V ul)) :
    e = {elV ul 0, elV ul 1} := by sorry

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

/-- bump.hl:488. -/
theorem MCELL_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (k : ℕ) (X : Set V3)
    (_hk : k ≤ 4) (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell k V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = k := by sorry

/-- bump.hl:513. -/
theorem MCELL4_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 4 := by sorry

/-- bump.hl:523. -/
theorem MCELL3_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 3 := by sorry

/-- bump.hl:533. -/
theorem MCELL2_CELL_PARAMETERS_EXIST (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell2 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) :
    (cellParams V X).1 = 2 := by sorry

/-- bump.hl:543. -/
theorem MCELL_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3) (k : ℕ)
    (_hk : k ≤ 4) (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell k V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell k V vl ∧ barV V 3 vl := by sorry

/-- bump.hl:568. -/
theorem MCELL4_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell4 V vl ∧ barV V 3 vl := by sorry

/-- bump.hl:580. -/
theorem MCELL3_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell3 V vl ∧ barV V 3 vl := by sorry

/-- bump.hl:592. -/
theorem MCELL2_PARAM_UL (V : Set V3) (ul vl : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell2 V ul)
    (_hb : barV V 3 ul) (_hn : ¬nullSet X) (_hvl : vl = (cellParams V X).2) :
    X = mcell2 V vl ∧ barV V 3 vl := by sorry

/-- bump.hl:604. -/
theorem MCELL4_VX (V : Set V3) (ul : List V3) (X : Set V3) (_hp : Packing V)
    (_hs : saturated V) (_hX : X = mcell4 V ul) (_hb : barV V 3 ul) :
    VX V X ⊆ setOfList (cellParams V X).2 := by sorry

/-- bump.hl:629. -/
theorem MCELL3_VX (V : Set V3) (ul : List V3) (X : Set V3) (_hp : Packing V)
    (_hs : saturated V) (_hX : X = mcell3 V ul) (_hb : barV V 3 ul) :
    VX V X ⊆ setOfList (truncateSimplex 2 (cellParams V X).2) := by sorry

/-- bump.hl:648. -/
theorem MCELL4_SET_OF_LIST_VX (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell4 V ul)
    (_hn : ¬nullSet X) (_hb : barV V 3 ul) :
    setOfList ul = V ∩ X := by sorry

/-- bump.hl:694. -/
theorem MCELL3_SET_OF_LIST_VX (V : Set V3) (ul : List V3) (X : Set V3)
    (_hp : Packing V) (_hs : saturated V) (_hX : X = mcell3 V ul)
    (_hn : ¬nullSet X) (_hb : barV V 3 ul) :
    setOfList (truncateSimplex 2 ul) = V ∩ X := by sorry

/-- bump.hl:766. -/
theorem MCELL4_EDGE (V : Set V3) (ul : List V3) (u v : V3) (_hp : Packing V)
    (_hs : saturated V) (_hn : ¬nullSet (mcell4 V ul)) (_hb : barV V 3 ul) :
    ({u, v} : Set V3) ∈ edgeX V (mcell4 V ul) ↔
      u ≠ v ∧ {u, v} ⊆ setOfList ul := by sorry

/-- bump.hl:786. -/
theorem MCELL3_EDGE (V : Set V3) (ul : List V3) (u v : V3) (_hp : Packing V)
    (_hs : saturated V) (_hn : ¬nullSet (mcell3 V ul)) (_hb : barV V 3 ul) :
    ({u, v} : Set V3) ∈ edgeX V (mcell3 V ul) ↔
      u ≠ v ∧ {u, v} ⊆ setOfList (truncateSimplex 2 ul) := by sorry

/-- bump.hl:806. -/
theorem EDGE_MCELL_EL (V : Set V3) (X : Set V3) (e : Set V3) (he : e ∈ edgeX V X) :
    ∃ u v : V3, e = {u, v} ∧ u ≠ v := by
  obtain ⟨u, v, rfl, -, -, huv⟩ := he
  exact ⟨u, v, rfl, huv⟩

/-- bump.hl:816. -/
theorem MCELL_EDGE (V : Set V3) (ul : List V3) (k : ℕ) (e : Set V3) (_hk : k < 4)
    (_hp : Packing V) (_hs : saturated V) (_hn : ¬nullSet (mcell k V ul))
    (_hb : barV V 3 ul) (_he : e ∈ edgeX V (mcell k V ul)) :
    e ⊆ setOfList (truncateSimplex 2 ul) := by sorry

/-- bump.hl:940 (`MCELL_BUMP_0`; the bump.hl:851 twin is its commented
`beta_bumpA` predecessor). -/
theorem MCELL_BUMP_0 (V : Set V3) (ul : List V3) (e : Set V3) (k : ℕ)
    (_hk : k < 4) (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul)
    (_hn : ¬nullSet (mcell k V ul)) :
    betaBump V e (mcell k V ul) = 0 := by sorry

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
    VX V X \ e ∉ edgeX V X := by sorry

/-- bump.hl:920. -/
theorem CRITICAL_EDGEX_ALT (V : Set V3) (X : Set V3) (e : Set V3) :
    e ∈ criticalEdgeX V X ↔ e ∈ edgeX V X ∧ hminus ≤ radV e ∧ radV e ≤ hplus := by
  sorry

/-- bump.hl:930. -/
theorem SUBCRITICAL_EDGEX_ALT (V : Set V3) (X : Set V3) (e : Set V3) :
    e ∈ subcriticalEdgeX V X ↔ e ∈ edgeX V X ∧ radV e < hminus := by
  sorry

/-- bump.hl:956. -/
theorem MCELL4_EDGE_OPP (V : Set V3) (ul : List V3) (_hp : Packing V)
    (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul)) :
    VX V (mcell4 V ul) \ {elV ul 0, elV ul 1} = {elV ul 2, elV ul 3} := by sorry

/-- bump.hl:999. -/
theorem MCELL_BUMP_OPP (V : Set V3) (ul : List V3) (_hp : Packing V)
    (_hs : saturated V) (_hb : barV V 3 ul) (_hn : ¬nullSet (mcell4 V ul))
    (_hc : ({elV ul 2, elV ul 3} : Set V3) ∉ criticalEdgeX V (mcell4 V ul)) :
    betaBump V {elV ul 0, elV ul 1} (mcell4 V ul) = 0 := by sorry

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
      else 0 := by sorry

/-- bump.hl:1086. -/
theorem BETA_BUMP_INVOLUTION_CRITICAL (V : Set V3) (X : Set V3)
    (r : Set V3 → Set V3) (e : Set V3) (_hs : saturated V) (_hp : Packing V)
    (_hm : X ∈ mcellSet V) (_he : e ∈ criticalEdgeX V X)
    (_hb : betaBump V e X ≠ 0) (hr : (fun e => VX V X \ e) = r) :
    r e ∈ criticalEdgeX V X := by sorry

/-- bump.hl:1100. -/
theorem BETA_BUMP_INVOLUTION_NEG (V : Set V3) (X : Set V3) (r : Set V3 → Set V3)
    (e : Set V3) (_hs : saturated V) (_hp : Packing V) (_hm : X ∈ mcellSet V)
    (_he : e ∈ criticalEdgeX V X) (_hb : betaBump V e X ≠ 0)
    (hr : (fun e => VX V X \ e) = r) :
    betaBump V (r e) X = -betaBump V e X := by sorry

/-- bump.hl:1129. -/
theorem BETA_BUMP_INVOLUTION_BIJ (V : Set V3) (X : Set V3) (s : Set (Set V3))
    (r : Set V3 → Set V3) (_hs : saturated V) (_hp : Packing V)
    (_hm : X ∈ mcellSet V)
    (_hsdef : {e | e ∈ criticalEdgeX V X ∧ betaBump V e X ≠ 0} = s)
    (hr : (fun e => VX V X \ e) = r) :
    BIJP4 r s s := by sorry

/-- bump.hl:1169. -/
theorem SUM_BETA_BUMP_LEMMA (V : Set V3) (X : Set V3) (_hs : saturated V)
    (_hp : Packing V) (_hm : X ∈ mcellSet V) :
    setSum {e | e ∈ criticalEdgeX V X} (fun e => betaBump V e X) = 0 := by sorry

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
  sorry

/-- bump.hl:1244. -/
theorem BOUND_BETA_BUMP :
    ∃ c : ℝ, ∀ (V : Set V3) (X : Set V3) (e : Set V3), saturated V → Packing V →
      X ∈ mcellSet V → e ∈ criticalEdgeX V X → betaBump V e X ≤ c := by
  sorry

end BumpP4
