/-
TARJJUW + OXLZLEZ1 (packing chapter) port to Lean 4.

HOL sources (persistent copies): `lean/scripts/packing/TARJJUW.hl` and
`lean/scripts/packing/OXLZLEZ1.hl`.

Encoding: HOL `real^3` ↔ `V3` (Kepler.Geom = `EuclideanSpace ℝ (Fin 3)`); HOL
`packing` ↔ `Kepler.Packing` (Kepler/Statement.lean, `Sphere.packing` reading
`dist < 2 → u = v`); HOL `dist(vec 0, v)` ↔ `dist (0 : V3) v`; HOL `dot` ↔
`⬝ᵥ` (dotProduct); HOL `bounded P` ↔ `∃ B, ∀ p ∈ P, ‖p‖ ≤ B`; HOL `INTERS` ↔
`⋂₀`; HOL `sum (0..n-1) f` ↔ `∑ i ∈ Finset.Icc 0 (n-1), f i` (natural
subtraction kept verbatim); HOL `EL k L` on the model lists ↔
`List.getD L k default`; HOL type `cc_v11` (defined via
`pair_of_cc_v11 : cc_v11 -> ((num->real) list) # ((num->bool) list) # num`)
is represented directly by the corresponding nested tuple structure.

`CHANGE_TARJJUW_5` is stated in the HOL source with conclusion
`norm p < norm p` (an absurdity used to derive a contradiction inside
`CHANGE_TARJJUW_10`); here it is stated as the equivalent `False`.
-/

import Kepler.Text.Polytope
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## TARJJUW: definitions (TARJJUW.hl:21-30) -/

/-- HOL `weakly_saturated` (TARJJUW.hl:21-25). -/
def weakly_saturated (V : Set V3) (r r' : ℝ) : Prop :=
  ∀ v : V3, 2 ≤ dist (0 : V3) v → dist (0 : V3) v ≤ r' →
    ∃ u : V3, u ∈ V ∧ u ≠ 0 ∧ dist u v < r

/-- HOL `half_spaces` (TARJJUW.hl:27-30). -/
def half_spaces (a : V3) (b : ℝ) : Set V3 :=
  {x : V3 | a ⬝ᵥ x ≤ b}

/-! ## OXLZLEZ1: the cc_v11 model (OXLZLEZ1.hl:19-133) -/

/-- HOL `cc_eps` (OXLZLEZ1.hl:23). -/
def cc_eps : ℝ := 0.0057

/-- Flyspeck constant `a_spine5` (sphere.hl:632, verbatim body `#0.0560305`;
twins: `aSpine5` (IneqClosureDefs.lean:598), `aSpine5P4` (PackingAuto4.lean:178,
private)).  2026-10-13 wave (SF-41): the former `opaque` declaration is
re-pointed to the verbatim body — `rad2XP25` precedent
(PackingAuto25.lean:91-98).  Statement sites are textually unchanged (the two
constants occur only inside `cc_real_model_v11` here) and the
`TEWNSCJ_MERGED` bridge `a_spine5 = aSpine5` is now `rfl`. -/
def a_spine5 : ℝ := 0.0560305

/-- Flyspeck constant `b_spine5` (sphere.hl:634, verbatim body
`--#0.0445813`; twins: `bSpine5` (IneqClosureDefs.lean:601), `bSpine5P4`
(PackingAuto4.lean:181, private)). -/
def b_spine5 : ℝ := -0.0445813

/-- HOL type `cc_v11` (OXLZLEZ1.hl:25-27): represented by the tuple
`((num->real) list) # ((num->bool) list) # num` that `pair_of_cc_v11`
projects. -/
structure CcV11 where
  /-- The `(num->real) list` component. -/
  ccReals : List (ℕ → ℝ)
  /-- The `(num->bool) list` component. -/
  ccBools : List (ℕ → Prop)
  /-- The `num` component. -/
  ccCard : ℕ

/-- HOL `pair_of_cc_v11` (OXLZLEZ1.hl:27). -/
def pair_of_cc_v11 (cc : CcV11) : List (ℕ → ℝ) × (List (ℕ → Prop) × ℕ) :=
  (cc.ccReals, cc.ccBools, cc.ccCard)

/-- HOL `cc_real_v11` (OXLZLEZ1.hl:31). -/
def cc_real_v11 (cc : CcV11) : List (ℕ → ℝ) := (pair_of_cc_v11 cc).1

/-- HOL `cc_bool_v11` (OXLZLEZ1.hl:32). -/
def cc_bool_v11 (cc : CcV11) : List (ℕ → Prop) := (pair_of_cc_v11 cc).2.1

/-- HOL `cc_card_v11` (OXLZLEZ1.hl:33). -/
def cc_card_v11 (cc : CcV11) : ℕ := (pair_of_cc_v11 cc).2.2

/-- HOL `cc_azim_v11` (OXLZLEZ1.hl:35). -/
def cc_azim_v11 (cc : CcV11) (i : ℕ) : ℝ := (cc_real_v11 cc).getD 0 (fun _ => 0) i

/-- HOL `cc_gg_v11` (OXLZLEZ1.hl:36). -/
def cc_gg_v11 (cc : CcV11) (i : ℕ) : ℝ := (cc_real_v11 cc).getD 1 (fun _ => 0) i

/-- HOL `cc_gg3a_v11` (OXLZLEZ1.hl:37). -/
def cc_gg3a_v11 (cc : CcV11) (i : ℕ) : ℝ := (cc_real_v11 cc).getD 2 (fun _ => 0) i

/-- HOL `cc_gg3b_v11` (OXLZLEZ1.hl:38). -/
def cc_gg3b_v11 (cc : CcV11) (i : ℕ) : ℝ := (cc_real_v11 cc).getD 3 (fun _ => 0) i

/-- HOL `cc_subcrit_v11` (OXLZLEZ1.hl:41). -/
def cc_subcrit_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 0 (fun _ => False) i

/-- HOL `cc_crit_v11` (OXLZLEZ1.hl:42). -/
def cc_crit_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 1 (fun _ => False) i

/-- HOL `cc_supercrit_v11` (OXLZLEZ1.hl:43). -/
def cc_supercrit_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 2 (fun _ => False) i

/-- HOL `cc_small_v11` (OXLZLEZ1.hl:44). -/
def cc_small_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 3 (fun _ => False) i

/-- HOL `cc_small_eta_v11` (OXLZLEZ1.hl:45). -/
def cc_small_eta_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 4 (fun _ => False) i

/-- HOL `cc_4cell_v11` (OXLZLEZ1.hl:46). -/
def cc_4cell_v11 (cc : CcV11) (i : ℕ) : Prop := (cc_bool_v11 cc).getD 5 (fun _ => False) i

/-- HOL `cc_hassmall_v11` (OXLZLEZ1.hl:49-50). -/
def cc_hassmall_v11 (cc : CcV11) (i : ℕ) : Prop :=
  cc_small_v11 cc i ∧ cc_small_v11 cc (i + 1)

/-- HOL `cc_qu_v11` (OXLZLEZ1.hl:52). -/
def cc_qu_v11 (cc : CcV11) (i : ℕ) : Prop :=
  cc_hassmall_v11 cc i ∧ cc_4cell_v11 cc i ∧ cc_subcrit_v11 cc i

/-- HOL `cc_qx_v11` (OXLZLEZ1.hl:53). -/
def cc_qx_v11 (cc : CcV11) (i : ℕ) : Prop := cc_4cell_v11 cc i ∧ ¬cc_qu_v11 cc i

/-- HOL `cc_qy_v11` (OXLZLEZ1.hl:54). -/
def cc_qy_v11 (cc : CcV11) (i : ℕ) : Prop := ¬cc_4cell_v11 cc i

/-- HOL `cc_size_v11` (OXLZLEZ1.hl:56-57). -/
noncomputable def cc_size_v11 (cc : CcV11) (p : ℕ → Prop) : ℕ :=
  (Finset.filter p (Finset.Icc 0 (cc_card_v11 cc - 1))).card

/-- HOL `periodic` (OXLZLEZ1.hl:59). -/
def periodic {α : Type*} (f : ℕ → α) (n : ℕ) : Prop := ∀ i, f (i + n) = f i

/-- HOL `cc_bool_model_v11` (OXLZLEZ1.hl:61-74). -/
def cc_bool_model_v11 (cc : CcV11) : Prop :=
  cc_card_v11 cc ≠ 0 ∧
  periodic (cc_subcrit_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_crit_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_supercrit_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_small_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_small_eta_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_4cell_v11 cc) (cc_card_v11 cc) ∧
  (∀ i, ¬(cc_crit_v11 cc i ∧ cc_supercrit_v11 cc i)) ∧
  (∀ i, ¬(cc_crit_v11 cc i ∧ cc_subcrit_v11 cc i)) ∧
  (∀ i, ¬(cc_supercrit_v11 cc i ∧ cc_subcrit_v11 cc i)) ∧
  (∀ i, cc_4cell_v11 cc i → cc_crit_v11 cc i ∨ cc_subcrit_v11 cc i ∨ cc_supercrit_v11 cc i) ∧
  (∀ i, cc_small_eta_v11 cc i → cc_small_v11 cc i)

/-- HOL `cc_bool_prep_v11` (OXLZLEZ1.hl:76). -/
def cc_bool_prep_v11 (cc : CcV11) : Prop := ∀ i, cc_qy_v11 cc i → ¬cc_qy_v11 cc (i + 1)

/-- HOL `cc_real_model_v11` (OXLZLEZ1.hl:80-133). -/
def cc_real_model_v11 (cc : CcV11) : Prop :=
  periodic (cc_azim_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_gg_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_gg3a_v11 cc) (cc_card_v11 cc) ∧
  periodic (cc_gg3b_v11 cc) (cc_card_v11 cc) ∧
  (∀ i, (0.606 : ℝ) ≤ cc_azim_v11 cc i) ∧
  (∀ i, cc_4cell_v11 cc i → cc_azim_v11 cc i < 2.8) ∧
  (∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc i = 2 * Real.pi) ∧
  ((cc_card_v11 cc = 4 ∧ ∃ i, cc_4cell_v11 cc i ∧ cc_crit_v11 cc i ∧
      cc_qu_v11 cc (i + 1) ∧ cc_qu_v11 cc (i + 2) ∧ cc_qu_v11 cc (i + 3)) →
    (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i → -cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i ∧ ¬cc_small_eta_v11 cc i → cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i ∧ ¬cc_small_eta_v11 cc (i + 1) → cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i ∧ cc_qy_v11 cc (i + 1) →
    (0 : ℝ) ≤ cc_gg_v11 cc i + cc_gg3a_v11 cc (i + 1)) ∧
  (∀ i, cc_qu_v11 cc (i + 1) ∧ cc_qy_v11 cc i →
    (0 : ℝ) ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1)) ∧
  (∀ i, cc_4cell_v11 cc i → a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i → (-0.0659 : ℝ) + 0.042 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i → (-0.0142852 : ℝ) + 0.00609451 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qu_v11 cc i → (0.161517 : ℝ) - 0.119482 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i → (0 : ℝ) ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i ∧ 2.3 < cc_azim_v11 cc i → cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i ∧ cc_hassmall_v11 cc i ∧ cc_qy_v11 cc (i + 1) →
    cc_eps ≤ cc_gg_v11 cc i + cc_gg3a_v11 cc (i + 1)) ∧
  (∀ i, cc_qx_v11 cc (i + 1) ∧ cc_hassmall_v11 cc (i + 1) ∧ cc_qy_v11 cc i →
    cc_eps ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1)) ∧
  (∀ i, cc_qx_v11 cc i ∧ cc_small_v11 cc i ∧ ¬cc_small_v11 cc (i + 1) →
    cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i ∧ cc_small_v11 cc (i + 1) ∧ ¬cc_small_v11 cc i →
    cc_eps ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i ∧ cc_hassmall_v11 cc i →
    (0.213849 : ℝ) - 0.119482 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qx_v11 cc i ∧ cc_hassmall_v11 cc i ∧ cc_supercrit_v11 cc i →
    (0.00457511 : ℝ) + 0.00609451 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i → cc_gg3a_v11 cc i + cc_gg3b_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i → (0 : ℝ) ≤ cc_gg3a_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i → (0 : ℝ) ≤ cc_gg3b_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i → (0.008 : ℝ) * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i ∧ cc_small_eta_v11 cc i ∧ ¬cc_small_eta_v11 cc (i + 1) ∧
    cc_azim_v11 cc i < 1.074 → a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i ∧ ¬cc_small_eta_v11 cc i ∧ cc_small_eta_v11 cc (i + 1) ∧
    cc_azim_v11 cc i < 1.074 → a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i ∧ cc_small_eta_v11 cc i ∧ cc_small_eta_v11 cc (i + 1) →
    a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i) ∧
  (∀ i, cc_qy_v11 cc i ∧ cc_small_eta_v11 cc i ∧ cc_small_eta_v11 cc (i + 1) ∧
    (1.946 : ℝ) ≤ cc_azim_v11 cc i ∧ cc_azim_v11 cc i ≤ 2.089 →
    (3 : ℝ) * cc_eps ≤ cc_gg_v11 cc i)

/-! ## TARJJUW: elementary lemmas (TARJJUW.hl:33-80) -/

/-- Key dot-product / norm identity used in `CHANGE_TARJJUW_5`. -/
private theorem two_dot_norms (u v : V3) :
    2 * (u ⬝ᵥ v) = ‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2 := by
  have h4 : inner ℝ u v = u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have h1 := real_inner_sub_sub_self u v
  have h2 := real_inner_self_eq_norm_sq (u - v)
  have h3 := real_inner_self_eq_norm_sq u
  have h5 := real_inner_self_eq_norm_sq v
  rw [← h4]
  linarith

/-- Dot product with zero on `V3`. -/
private theorem dot_zero_right (u : V3) : u ⬝ᵥ (0 : V3) = 0 :=
  dotProduct_zero u

/-- HOL `CHANGE_TARJJUW_1` (TARJJUW.hl:33-38): rescaling to length `r'`. -/
theorem CHANGE_TARJJUW_1 {v p : V3} {r' : ℝ} (hr' : 0 < r') (hp : p ≠ 0)
    (hv : v = (r' / ‖p‖) • p) : r' = ‖v‖ := by
  subst hv
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr' hpn)]
  field_simp

/-- HOL `CHANGE_TARJJUW_2` (TARJJUW.hl:43-44). -/
theorem CHANGE_TARJJUW_2 {v p : V3} {r' : ℝ} (hp : p ≠ 0)
    (hv : v = (r' / ‖p‖) • p) : r' • p = ‖p‖ • v := by
  subst hv
  rw [smul_smul]
  have hnz : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  congr 1
  field_simp

/-- HOL `CHANGE_TARJJUW_3` (TARJJUW.hl:48-62). -/
theorem CHANGE_TARJJUW_3 {V : Set V3} {u : V3} (_hV : Packing V)
    (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2) (hu : u ∈ V) : 2 ≤ ‖u‖ := by
  have h1 := hsub hu
  have h2 := (Set.mem_sdiff u).mp h1 |>.2
  rw [Metric.mem_ball, dist_zero_right] at h2
  exact le_of_not_gt h2

/-- HOL `CHANGE_TARJJUW_31` (TARJJUW.hl:66-76). -/
theorem CHANGE_TARJJUW_31 {V : Set V3} {u : V3} (hV : Packing V)
    (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2) (hu : u ∈ V) : u ≠ 0 := by
  have h2 := CHANGE_TARJJUW_3 hV hsub hu
  intro h0
  rw [h0, norm_zero] at h2
  linarith

/-- HOL `CHANGE_TARJJUW_4` (TARJJUW.hl:80). -/
theorem CHANGE_TARJJUW_4 {u v : V3} {r : ℝ} (h : dist u v < r) :
    dist u v ^ 2 < r ^ 2 := by
  have hd : 0 ≤ dist u v := dist_nonneg
  exact sq_lt_sq' (by linarith) h

/-- HOL `CHANGE_TARJJUW_5` (TARJJUW.hl:84-259). The hypothesis list is
contradictory; the HOL source states this with the absurd conclusion
`norm p < norm p`, used to close a contradiction in `CHANGE_TARJJUW_10`. -/
theorem CHANGE_TARJJUW_5 {V : Set V3} {g : V3 → ℝ} {r r' : ℝ} {u v p : V3}
    (hV : Packing V) (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2) (hr : 2 ≤ r)
    (hr' : r ≤ r') (hp : p ≠ 0) (hg : g u * r' / 2 < ‖p‖)
    (hv : v = (r' / ‖p‖) • p) (hup : u ⬝ᵥ p ≤ g u) (_hu0 : u ≠ 0)
    (hduv : dist u v < r) (huV : u ∈ V) : False := by
  have hr'2 : 2 ≤ r' := by linarith
  have hr'0 : 0 < r' := by linarith
  have h1 : r' = ‖v‖ := CHANGE_TARJJUW_1 hr'0 hp hv
  have hp' : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hCT2 := CHANGE_TARJJUW_2 hp hv
  have hdoteq : r' * (u ⬝ᵥ p) = ‖p‖ * (u ⬝ᵥ v) := by
    have h0 := congrArg (fun w : V3 => u ⬝ᵥ w) hCT2
    simp only [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul] at h0
    exact h0
  have hle1 : ‖p‖ * (u ⬝ᵥ v) ≤ g u * r' := by
    have hm : r' * (u ⬝ᵥ p) ≤ r' * g u := mul_le_mul_of_nonneg_left hup (le_of_lt hr'0)
    linarith
  have hstep : ‖p‖ * (u ⬝ᵥ v) < 2 * ‖p‖ := by linarith
  have huv2 : u ⬝ᵥ v < 2 := by
    exact lt_of_mul_lt_mul_left (by rwa [mul_comm 2 ‖p‖] at hstep) hp'.le
  have hid : 2 * (u ⬝ᵥ v) = ‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2 := two_dot_norms u v
  have hnormu : 2 ≤ ‖u‖ := CHANGE_TARJJUW_3 hV hsub huV
  have hnormv : ‖v‖ = r' := h1.symm
  have hdistnv : ‖u - v‖ = dist u v := (dist_eq_norm u v).symm
  have hduv2 : dist u v ^ 2 < r ^ 2 := CHANGE_TARJJUW_4 hduv
  have h4u : (4 : ℝ) ≤ ‖u‖ ^ 2 := by nlinarith
  have hr2 : r ^ 2 ≤ r' ^ 2 := by nlinarith
  have hlower : 4 + r' ^ 2 - r ^ 2 < 2 * (u ⬝ᵥ v) := by
    rw [hid, hnormv, hdistnv]
    linarith
  have hup2 : 2 * (u ⬝ᵥ v) < 4 := by linarith
  linarith

/-! ## TARJJUW: half-space intersection (TARJJUW.hl:263-377) -/

/-- HOL `CHANGE_TARJJUW_6` (TARJJUW.hl:263-291). -/
theorem CHANGE_TARJJUW_6 {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ} {u p : V3}
    (_hr : 2 ≤ r) (_hr' : r ≤ r') (_hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (_hfin : V.Finite) (_hV : Packing V) (_hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) (hp : p ∈ P) (hu : u ∈ V) :
    p ∈ half_spaces u (g u) := by
  subst hP
  exact Set.mem_sInter.mp hp _ (Set.mem_image_of_mem _ hu)

/-- HOL `CHANGE_TARJJUW_7` (TARJJUW.hl:294-307). -/
theorem CHANGE_TARJJUW_7 {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ} {u p : V3}
    (_hr : 2 ≤ r) (_hr' : r ≤ r') (_hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (_hfin : V.Finite) (_hV : Packing V) (_hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) (huV : u ∈ V)
    (hp : p ∈ P) : u ⬝ᵥ p ≤ g u :=
  CHANGE_TARJJUW_6 _hr _hr' _hsub _hfin _hV _hws hP hp huV

/-- HOL `CHANGE_TARJJUW_71` (TARJJUW.hl:310-321). -/
theorem CHANGE_TARJJUW_71 {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ}
    (_hr : 2 ≤ r) (_hr' : r ≤ r') (_hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (_hfin : V.Finite) (_hV : Packing V) (_hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) (p u : V3)
    (hp : p ∈ P) (hu : u ∈ V) : u ⬝ᵥ p ≤ g u :=
  CHANGE_TARJJUW_7 _hr _hr' _hsub _hfin _hV _hws hP hu hp

/-- HOL `FININTE_GFUN` (TARJJUW.hl:324-339). -/
theorem FININTE_GFUN {V : Set V3} {g : V3 → ℝ} {r' : ℝ} (hfin : V.Finite)
    (hne : V.Nonempty) :
    ((fun u : V3 => g u * r' / 2) '' V).Finite ∧
      ((fun u : V3 => g u * r' / 2) '' V).Nonempty :=
  ⟨hfin.image _, hne.image _⟩

/-- HOL `CHANGE_TARJJUW_9` (TARJJUW.hl:343-377). -/
theorem CHANGE_TARJJUW_9 {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ}
    (_hr : 2 ≤ r) (_hr' : r ≤ r') (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (hfin : V.Finite) (hV : Packing V) (_hne : V.Nonempty)
    (_hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) : polyhedron P := by
  subst hP
  refine ⟨(fun w => half_spaces w (g w)) '' V, hfin.image _, rfl, ?_⟩
  rintro h ⟨u, hu, rfl⟩
  exact ⟨u, g u, CHANGE_TARJJUW_31 hV hsub hu, rfl⟩

/-- HOL `CHANGE_TARJJUW_10` (TARJJUW.hl:379-552). -/
theorem CHANGE_TARJJUW_10 {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ} {u : V3}
    (hr : 2 ≤ r) (hr' : r ≤ r') (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (hfin : V.Finite) (hV : Packing V) (hne : V.Nonempty)
    (hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) (_huV : u ∈ V)
    (_hPpoly : polyhedron P) : ∃ B : ℝ, ∀ p ∈ P, ‖p‖ ≤ B := by
  have hr'2 : 2 ≤ r' := by linarith
  have hr'0 : 0 < r' := by linarith
  by_contra hnb
  push Not at hnb
  obtain ⟨B, -, hBmax⟩ :=
    Set.exists_max_image ((fun w : V3 => g w * r' / 2) '' V) id
      (FININTE_GFUN hfin hne).1 (FININTE_GFUN hfin hne).2
  obtain ⟨p₀, hp₀P, hBp₀⟩ := hnb B
  have hgall : ∀ w ∈ V, g w * r' / 2 < ‖p₀‖ := by
    intro w hw
    have hmem : g w * r' / 2 ∈ (fun w : V3 => g w * r' / 2) '' V := ⟨w, hw, rfl⟩
    have hle : g w * r' / 2 ≤ B := hBmax _ hmem
    linarith
  by_cases hp₀ : p₀ = 0
  · obtain ⟨w, hw⟩ := hne
    have h1 : w ⬝ᵥ p₀ ≤ g w := CHANGE_TARJJUW_71 hr hr' hsub hfin hV hws hP p₀ w hp₀P hw
    rw [hp₀, dot_zero_right] at h1
    have hg0 : g w * r' / 2 < (0 : ℝ) := by
      have hpos := hgall w hw
      rwa [hp₀, norm_zero] at hpos
    have hgw : g w < 0 := by
      by_contra hge
      have hge' : 0 ≤ g w := le_of_not_gt hge
      have hp2 : (0 : ℝ) ≤ g w * r' / 2 :=
        div_nonneg (mul_nonneg hge' (le_of_lt hr'0)) (by norm_num)
      linarith
    linarith
  · have hvnorm : dist (0 : V3) ((r' / ‖p₀‖) • p₀) = r' := by
      rw [dist_zero_left]
      exact (CHANGE_TARJJUW_1 hr'0 hp₀ rfl).symm
    have hv1 : 2 ≤ dist (0 : V3) ((r' / ‖p₀‖) • p₀) := by rw [hvnorm]; exact hr'2
    obtain ⟨u', hu'V, hu'0, hdu'v⟩ :=
      hws ((r' / ‖p₀‖) • p₀) hv1 hvnorm.le
    have hup' : u' ⬝ᵥ p₀ ≤ g u' := CHANGE_TARJJUW_71 hr hr' hsub hfin hV hws hP p₀ u' hp₀P hu'V
    exact CHANGE_TARJJUW_5 hV hsub hr hr' hp₀ (hgall u' hu'V) rfl hup' hu'0 hdu'v hu'V

/-- HOL `TARJJUW` (TARJJUW.hl:555-574). -/
theorem TARJJUW {V P : Set V3} {g : V3 → ℝ} {r r' : ℝ}
    (hr : 2 ≤ r) (hr' : r ≤ r') (hsub : V ⊆ univ \ Metric.ball (0 : V3) 2)
    (hfin : V.Finite) (hV : Packing V) (hne : V.Nonempty)
    (hws : weakly_saturated V r r')
    (hP : P = ⋂₀ ((fun w => half_spaces w (g w)) '' V)) :
    ∃ B : ℝ, ∀ p ∈ P, ‖p‖ ≤ B := by
  obtain ⟨u, hu⟩ := id hne
  exact CHANGE_TARJJUW_10 hr hr' hsub hfin hV hne hws hP hu
    (CHANGE_TARJJUW_9 hr hr' hsub hfin hV hne hws hP)

/-! ## OXLZLEZ1: periodicity toolkit (OXLZLEZ1.hl:184-574) -/

/-- HOL `periodic_nk` (OXLZLEZ1.hl:184-197). -/
theorem periodic_nk {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (_hn : 0 < n)
    (i k : ℕ) : f (i + k * n) = f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact (h (i + k * n)).trans ih

/-- HOL `periodic_mod` (OXLZLEZ1.hl:199-209). -/
theorem periodic_mod {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n) (hn : n ≠ 0)
    (m : ℕ) : f m = f (m % n) := by
  have h2 : m % n + m / n * n = m := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div m n
  calc f m = f (m % n + m / n * n) := by rw [h2]
    _ = f (m % n) := periodic_nk h (Nat.pos_of_ne_zero hn) (m % n) (m / n)

/-- HOL `MOD_IN_NUMSEG` (OXLZLEZ1.hl:211-221). -/
theorem MOD_IN_NUMSEG {m n : ℕ} (hn : n ≠ 0) : m % n ∈ Finset.Icc 0 (n - 1) := by
  refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
  have hlt := Nat.mod_lt m (Nat.pos_of_ne_zero hn)
  omega

/-- HOL `MOD_INJ` (OXLZLEZ1.hl:223-260). -/
theorem MOD_INJ {n r a b : ℕ} (hn : n ≠ 0) (ha : a ∈ Finset.Icc r (n - 1 + r))
    (hb : b ∈ Finset.Icc r (n - 1 + r)) (h : a % n = b % n) : a = b := by
  have key : ∀ x y : ℕ, x ≤ y → y - x < n → x % n = y % n → x = y := by
    intro x y hle hd heq
    have hxm : x % n < n := Nat.mod_lt x (Nat.pos_of_ne_zero hn)
    have hy : y = x + (y - x) := by omega
    rw [hy, Nat.add_mod, Nat.mod_eq_of_lt hd] at heq
    rcases Nat.lt_or_ge (x % n + (y - x)) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at heq; omega
    · have hsplit : x % n + (y - x) = (x % n + (y - x) - n) + n := by omega
      rw [hsplit, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : x % n + (y - x) - n < n)] at heq
      omega
  rcases le_total a b with hab | hba
  · have hd : b - a < n := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
      obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hb
      omega
    exact key a b hab hd h
  · have hd : a - b < n := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
      obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hb
      omega
    exact (key b a hba hd h.symm).symm

/-- HOL `MOD_INJ1_ALT` (OXLZLEZ1.hl:263-274). -/
theorem MOD_INJ1_ALT {k n : ℕ} (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0) (x : ℕ) :
    x % n ≠ (x + k) % n := by
  intro h
  have hxm : x % n < n := Nat.mod_lt x (Nat.pos_of_ne_zero hn)
  rw [Nat.add_mod, Nat.mod_eq_of_lt hk] at h
  rcases Nat.lt_or_ge (x % n + k) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · have hsplit : x % n + k = (x % n + k - n) + n := by omega
    rw [hsplit, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : x % n + k - n < n)] at h
    exact hk0 (by omega)

/-- HOL `MOD_SURJ` (OXLZLEZ1.hl:277-305). -/
theorem MOD_SURJ {n r a : ℕ} (hn : n ≠ 0) (ha : a ≤ n - 1) :
    ∃ b, b ∈ Finset.Icc r (n - 1 + r) ∧ b % n = a := by
  obtain ⟨q, m, heq, hlt⟩ : ∃ q m : ℕ, n * q + m = r ∧ m < n :=
    ⟨r / n, r % n, Nat.div_add_mod r n, Nat.mod_lt r (Nat.pos_of_ne_zero hn)⟩
  rcases Nat.lt_or_ge a m with hlt | hge
  · refine ⟨a + n + n * q, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : a < n)]
  · refine ⟨a + n * q, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : a < n)]

/-- HOL `BIJ_SUM` (OXLZLEZ1.hl:307-315), restated over `Finset`s. -/
theorem BIJ_SUM {β γ : Type*} {A : Finset β} {B : Finset γ} {f : γ → ℝ} {ab : β → γ}
    (hmaps : ∀ x ∈ A, ab x ∈ B) (hinj : ∀ x ∈ A, ∀ y ∈ A, ab x = ab y → x = y)
    (hsurj : ∀ y ∈ B, ∃ x ∈ A, ab x = y) :
    ∑ x ∈ A, f (ab x) = ∑ x ∈ B, f x := by
  have hB : B = A.image ab := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hsurj x hx
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, rfl⟩
      exact hmaps y hy
  rw [hB]
  exact (Finset.sum_image hinj).symm

/-- HOL `periodic_sum` (OXLZLEZ1.hl:318-345). -/
theorem periodic_sum {f : ℕ → ℝ} {n : ℕ} (h : periodic f n) (hn : n ≠ 0) (i : ℕ) :
    ∑ x ∈ Finset.Icc i (n - 1 + i), f x = ∑ x ∈ Finset.range n, f x := by
  induction i with
  | zero => rw [Nat.add_zero, ← Nat.range_eq_Icc_zero_sub_one n hn]
  | succ i ih =>
    have heq : n - 1 + (i + 1) = n + i := by omega
    rw [heq]
    have hsplit : ∑ x ∈ Finset.Icc i (n + i), f x
        = f i + ∑ x ∈ Finset.Icc (i + 1) (n + i), f x := by
      have hIcc : Finset.Icc i (n + i) = insert i (Finset.Icc (i + 1) (n + i)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          omega
        · rintro (h | ⟨h1, h2⟩)
          · omega
          · omega
      rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hA : ∑ x ∈ Finset.Icc i (n + i), f x
        = ∑ x ∈ Finset.Icc i (n - 1 + i), f x + f (n + i) := by
      have heq2 : n - 1 + i + 1 = n + i := by omega
      rw [← heq2]
      exact Finset.sum_Icc_succ_top (show i ≤ n - 1 + i + 1 by omega) f
    have hper : f (n + i) = f i := by
      rw [Nat.add_comm]
      exact h i
    linarith

/-- HOL `periodic_fn` (OXLZLEZ1.hl:347-359). -/
theorem periodic_fn {cc : CcV11} (hb : cc_bool_model_v11 cc) :
    periodic (cc_hassmall_v11 cc) (cc_card_v11 cc) ∧
    periodic (cc_qu_v11 cc) (cc_card_v11 cc) ∧
    periodic (cc_qx_v11 cc) (cc_card_v11 cc) ∧
    periodic (cc_qy_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, h1, -, -, h4, -, h6, -, -, -, -⟩ := hb
  have hps : ∀ i, cc_hassmall_v11 cc (i + cc_card_v11 cc) = cc_hassmall_v11 cc i := by
    intro i
    simp only [cc_hassmall_v11]
    rw [Nat.add_right_comm, h4 i, h4 (i + 1)]
  have hpq : ∀ i, cc_qu_v11 cc (i + cc_card_v11 cc) = cc_qu_v11 cc i := by
    intro i
    simp only [cc_qu_v11]
    rw [hps i, h6 i, h1 i]
  refine ⟨hps, hpq, fun i => ?_, fun i => ?_⟩
  · simp only [cc_qx_v11]
    rw [h6 i, hpq i]
  · simp only [cc_qy_v11]
    rw [h6 i]

/-! ## OXLZLEZ1: model consequences (OXLZLEZ1.hl:362-516) -/

/-- HOL `QX_NN` (OXLZLEZ1.hl:362-371, `gamma_qx`). -/
theorem QX_NN {cc : CcV11} (_hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    {i : ℕ} (h : cc_qx_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgam, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -⟩ := hr
  exact hgam i h

/-- HOL `QY_NN` (OXLZLEZ1.hl:373-384, 23-cell bounds). -/
theorem QY_NN {cc : CcV11} (_hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    {i : ℕ} (h : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h26, h27, h28, -, -, -, -, -⟩ := hr
  have ha := h27 i h
  have hbb := h28 i h
  have hsu := h26 i h
  linarith

/-- HOL `QY_QX_QU` (OXLZLEZ1.hl:386-395). -/
theorem QY_QX_QU {cc : CcV11} (_hb : cc_bool_model_v11 cc) (i : ℕ) :
    cc_qu_v11 cc i ∨ cc_qy_v11 cc i ∨ cc_qx_v11 cc i := by
  by_cases h4 : cc_4cell_v11 cc i
  · by_cases hqu : cc_qu_v11 cc i
    · exact Or.inl hqu
    · exact Or.inr (Or.inr ⟨h4, hqu⟩)
  · exact Or.inr (Or.inl h4)

/-- HOL `QUARTER1` (OXLZLEZ1.hl:397-452). -/
theorem QUARTER1 {cc : CcV11} (hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    1 ≤ cc_size_v11 cc (cc_qu_v11 cc) := by
  have hcard : cc_card_v11 cc ≠ 0 := hb.1
  by_cases hex : ∃ i, cc_qu_v11 cc i
  · obtain ⟨i, hi⟩ := hex
    have hmem : i % cc_card_v11 cc ∈
        Finset.filter (cc_qu_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
      refine Finset.mem_filter.mpr ⟨MOD_IN_NUMSEG hcard, ?_⟩
      obtain ⟨-, hqup, -, -⟩ := periodic_fn hb
      have hk := periodic_nk hqup (Nat.pos_of_ne_zero hcard) (i % cc_card_v11 cc)
        (i / cc_card_v11 cc)
      have hi2 : i % cc_card_v11 cc + i / cc_card_v11 cc * cc_card_v11 cc = i := by
        rw [Nat.mul_comm]
        exact Nat.mod_add_div i (cc_card_v11 cc)
      rw [hi2] at hk
      rw [← hk]
      exact hi
    exact Finset.one_le_card.mpr ⟨i % cc_card_v11 cc, hmem⟩
  · push Not at hex
    have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i := by
      refine Finset.sum_nonneg (fun j hj => ?_)
      rcases QY_QX_QU hb j with hq | hqy | hqx
      · exact absurd hq (hex j)
      · exact QY_NN hb hr hqy
      · exact QX_NN hb hr hqx
    linarith

/-- HOL `QU_EXISTS` (OXLZLEZ1.hl:454-476). -/
theorem QU_EXISTS {cc : CcV11} (hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ q, cc_qu_v11 cc q ∧ q ∈ Finset.Icc 0 (cc_card_v11 cc - 1) := by
  have h1 := QUARTER1 hb hr hsum
  obtain ⟨q, hq⟩ := Finset.one_le_card.mp h1
  have h2 := Finset.mem_filter.mp hq
  exact ⟨q, h2.2, h2.1⟩

/-- HOL `CC_CARD2` (OXLZLEZ1.hl:478-516). -/
theorem CC_CARD2 {cc : CcV11} (hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    2 ≤ cc_card_v11 cc := by
  have h0 : cc_card_v11 cc ≠ 0 := hb.1
  have h1 : cc_card_v11 cc ≠ 1 := by
    intro hc
    obtain ⟨q, hq, hqI⟩ := QU_EXISTS hb hr hsum
    have hn1 : cc_card_v11 cc - 1 = 0 := by omega
    obtain ⟨hqI1, hqI2⟩ := Finset.mem_Icc.mp hqI
    rw [hn1] at hqI2
    have hq0 : q = 0 := by omega
    subst hq0
    obtain ⟨-, -, -, -, -, h6, h7, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -⟩ := hr
    have hsumazim : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc i
        = 2 * Real.pi := h7
    rw [hn1, Finset.Icc_self, Finset.sum_singleton] at hsumazim
    have hlt : cc_azim_v11 cc 0 < 2.8 := h6 0 hq.2.1
    have hpi : (2.8 : ℝ) < 2 * Real.pi := by
      have := Real.pi_gt_three
      linarith
    linarith
  omega

/-- HOL `periodic_numseg` (OXLZLEZ1.hl:518-532). -/
theorem periodic_numseg {p : ℕ → Prop} {n : ℕ} (h : periodic p n) (hn : n ≠ 0)
    (hseg : ∀ i, i ∈ Finset.Icc 0 (n - 1) → p i) (i : ℕ) : p i := by
  have h1 := periodic_mod h hn i
  have h2 : i % n ≤ n - 1 := by
    have hlt := Nat.mod_lt i (Nat.pos_of_ne_zero hn)
    omega
  rw [h1]
  exact hseg (i % n) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, h2⟩)

/-- HOL `BIJ_NUMSEG` (OXLZLEZ1.hl:534-551), restated over `Finset`s. -/
theorem BIJ_NUMSEG (s a b : ℕ) :
    (∀ x ∈ Finset.Icc a b, x + s ∈ Finset.Icc (a + s) (b + s)) ∧
    (∀ x ∈ Finset.Icc a b, ∀ y ∈ Finset.Icc a b, x + s = y + s → x = y) ∧
    (∀ y ∈ Finset.Icc (a + s) (b + s), ∃ x ∈ Finset.Icc a b, x + s = y) := by
  constructor
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  constructor
  · intro x _ y _ hxy
    omega
  · intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hy
    exact ⟨y - s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩

/-- HOL `PERIODIC_PROPERTY` (OXLZLEZ1.hl:553-574). -/
theorem PERIODIC_PROPERTY {α : Type*} {vv : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (h : periodic vv k) (i : ℕ) : vv (i % k) = vv i :=
  (periodic_mod h hk i).symm

/-! ## OXLZLEZ1: main conclusions (statement level; heavy, not proved here) -/

/-- HOL `CHQSQEY_concl` (OXLZLEZ1.hl:135-136). -/
theorem CHQSQEY_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) := by sorry

/-- HOL `MTMLSRF_concl` (OXLZLEZ1.hl:138-140). -/
theorem MTMLSRF_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1) := by sorry

/-- HOL `LXDEYBO_concl` (OXLZLEZ1.hl:142-143). -/
theorem LXDEYBO_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_4cell_v11 cc) ≤ 4 := by sorry

/-- HOL `UNPNFVW_concl` (OXLZLEZ1.hl:145-146). -/
theorem UNPNFVW_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_qy_v11 cc) ≤ 1 := by sorry

/-- HOL `IPVICGW_concl` (OXLZLEZ1.hl:156-157). -/
theorem IPVICGW_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_small_v11 cc i := by sorry

/-- HOL `RSIWAMP_concl` (OXLZLEZ1.hl:159-160). -/
theorem RSIWAMP_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_card_v11 cc ≤ 4 := by sorry

/-- HOL `UTEOITF_concl` (OXLZLEZ1.hl:167-168). -/
theorem UTEOITF_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ i, cc_4cell_v11 cc i := by sorry

/-- HOL `LUIKGMH_concl` (OXLZLEZ1.hl:170-171). -/
theorem LUIKGMH_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    4 ≤ cc_card_v11 cc := by sorry

/-- HOL `GRHIDFA_concl` (OXLZLEZ1.hl:173-174): the main conclusion `False`. -/
theorem GRHIDFA_concl (cc : CcV11) (_hb : cc_bool_model_v11 cc) (_hp : cc_bool_prep_v11 cc)
    (_hr : cc_real_model_v11 cc)
    (_hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    False := by sorry

/-! ## OXLZLEZ2: shared kit (OXLZLEZ2.hl:183-3451; GRHIDFA wave plan W1)

Port of the tactical-infrastructure / intra-chapter kit consumed by the
OXLZLEZ2 conclusion ladder (WAVES §4 W1 task list, 17 items).  Encoding
differences from the PA4 reference rows (PackingAuto4.lean §2, CC4P4): the
`getD` accessors `cc_azim_v11`/`cc_gg_v11`/`cc_gg3a_v11`/`cc_gg3b_v11` stand in
for `cc.reals k i`, the Prop predicates `cc_small_v11` etc. stand in for
`cc.bools k i = true`, and `periodic` (equality of predicates) replaces
`periodicPropP4` (Iff).  All rows below are fully proved, with no unproved
placeholders.  Rows are ordered by their OXLZLEZ2.hl anchor. -/

/-- OXLZLEZ2.hl:183.  PA4 reference: PackingAuto4.lean:257 (proven). -/
theorem p3g_QU_OR_QXY (cc : CcV11) (i : ℕ) :
    cc_qu_v11 cc i ∨ cc_qx_v11 cc i ∨ cc_qy_v11 cc i := by
  by_cases h : cc_4cell_v11 cc i
  · by_cases hq : cc_qu_v11 cc i
    · exact Or.inl hq
    · exact Or.inr (Or.inl (show cc_4cell_v11 cc i ∧ ¬cc_qu_v11 cc i from ⟨h, hq⟩))
  · exact Or.inr (Or.inr h)

/-- OXLZLEZ2.hl:186.  `QX_NN` with the `#0.0 = &0` rewrite applied; the numeral
distinction does not exist in Lean, so this row is an alias of `QX_NN`. -/
theorem p3g_QX_NN0 {cc : CcV11} (hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    {i : ℕ} (h : cc_qx_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i := QX_NN hb hr h

/-- OXLZLEZ2.hl:187.  Alias of `QY_NN`, same reading as `p3g_QX_NN0`. -/
theorem p3g_QY_NN0 {cc : CcV11} (hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    {i : ℕ} (h : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i := QY_NN hb hr h

/-- OXLZLEZ2.hl:193.  PA4 reference: PackingAuto4.lean:266 (proven). -/
theorem p3g_SUM_POS_LT_NUMSEG (m n : ℕ) (f : ℕ → ℝ) (hmn : m ≤ n)
    (h : ∀ p, m ≤ p → p ≤ n → 0 < f p) :
    0 < Finset.sum (Finset.Icc m n) f :=
  Finset.sum_pos (fun p hp => h p (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hp).2)
    ⟨m, Finset.mem_Icc.mpr ⟨le_refl m, hmn⟩⟩

/-- OXLZLEZ2.hl:398.  HOL states the row for the set-sum `sum S`; PA3 sums over
`Finset.Icc`, so the carrier is rendered as a `Finset` (form note, not a
statement change: β-contraction under the sum is definitional). -/
theorem p3g_SUM_BETA {α : Type*} (S : Finset α) (f : α → ℝ) :
    Finset.sum S (fun x => f x) = Finset.sum S f := rfl

/-- OXLZLEZ2.hl:1255.  PA4 reference: PackingAuto4.lean:321 (proven). -/
theorem p3g_THREE_MOD_CONSECUTIVES (i n : ℕ) (hi : 0 < i) (hn : 3 ≤ n) :
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

/-- OXLZLEZ2.hl:1281.  PA4 reference: PackingAuto4.lean:336 (proven). -/
theorem p3g_MOD_PERIOD_BOUNDED (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) (x : ℕ) :
    (x + k) % n = x % n → n ≤ k := by
  intro heq
  have hd : n ∣ (x + k) - x := (Nat.modEq_iff_dvd' (Nat.le_add_right x k)).mp heq.symm
  rw [Nat.add_sub_cancel_left] at hd
  exact Nat.le_of_dvd (show 0 < k from by omega) hd

/-- OXLZLEZ2.hl:1293.  PA4 reference: PackingAuto4.lean:344 (proven). -/
theorem p3g_MOD_PERIOD_BOUNDED2 (nn m i k : ℕ) (hnn : nn ≠ 0) (hmk : m ≤ k)
    (h : (i + k) % nn ∈ (fun x => (i + x) % nn) '' {x | x < m}) : nn ≤ k := by
  simp only [Set.mem_image, Set.mem_setOf_eq] at h
  obtain ⟨x, hxm, hx⟩ := h
  have hxi : i + x ≤ i + k := by omega
  have hd : nn ∣ (i + k) - (i + x) :=
    (Nat.modEq_iff_dvd' hxi).mp hx
  rw [show i + k - (i + x) = k - x from by omega] at hd
  have hle := Nat.le_of_dvd (show 0 < k - x from by omega) hd
  omega

/-- OXLZLEZ2.hl:1735.  PA4 reference: PackingAuto4.lean:362 (proven). -/
theorem p3g_CC_4CELL_QUQX (cc : CcV11) (i : ℕ) :
    cc_4cell_v11 cc i ↔ cc_qu_v11 cc i ∨ cc_qx_v11 cc i := by
  constructor
  · intro h
    by_cases hq : cc_qu_v11 cc i
    · exact Or.inl hq
    · exact Or.inr ⟨h, hq⟩
  · rintro (h | h)
    · exact h.2.1
    · exact h.1

/-- OXLZLEZ2.hl:1740.  PA4 reference: PackingAuto4.lean:374 (proven); HOL closes
by `ASM_SIMP_TAC[QX_NN0]`, mirrored here via the PA3 `QX_NN`. -/
theorem p3g_QX_NN00 (cc : CcV11) (_hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    (i : ℕ) (hqx : cc_qx_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i :=
  QX_NN _hb hr hqx

/-- OXLZLEZ2.hl:1745.  PA4 reference: PackingAuto4.lean:380 (proven); HOL closes
by `ASM_SIMP_TAC[QY_NN0]`, mirrored here via the PA3 `QY_NN`. -/
theorem p3g_QY_NN00 (cc : CcV11) (_hb : cc_bool_model_v11 cc) (hr : cc_real_model_v11 cc)
    (i : ℕ) (hqy : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i :=
  QY_NN _hb hr hqy

/-- OXLZLEZ2.hl:1752.  PA4 reference: PackingAuto4.lean:390 (proven). -/
theorem p3g_NUMSEG_SET_VER (m : ℕ) : (Finset.Icc 0 m : Set ℕ) = {i | i ≤ m} := by
  ext i
  simp only [Finset.mem_coe, Finset.mem_Icc, Set.mem_setOf_eq]
  omega

/-- OXLZLEZ2.hl:1758 (`REWRITE_RULE[NUMSEG_SET_VER]` of `FINITE_NUMSEG`
specialized at `0`). -/
theorem p3g_FINITE_INITIAL_SEG (m : ℕ) : {i : ℕ | i ≤ m}.Finite := by
  rw [← p3g_NUMSEG_SET_VER m]
  exact (Finset.Icc 0 m).finite_toSet

/-- OXLZLEZ2.hl:1761.  PA4 reference: PackingAuto4.lean:396 (proven); HOL closes
by `FINITE_SUBSET` against `FINITE_INITIAL_SEG`, mirrored here. -/
theorem p3g_FINITE_INITIAL_SEG2 (n : ℕ) : {i : ℕ | i < n}.Finite := by
  refine Set.Finite.subset (p3g_FINITE_INITIAL_SEG n) ?_
  intro i hi
  exact le_of_lt (Set.mem_setOf_eq.mp hi)

/-- OXLZLEZ2.hl:1768.  The one W1 row without a proven PA4 reference
(PA4:402 is a stub): finiteness of the `m`-block of residues.  Lean proof:
the residue set is the image of `Finset.range m` under `fun k => (i + k) % n`,
with injectivity on the range from `Nat.modEq_iff_dvd'` and `m ≤ n` (HOL
routes the same argument through `FINITE_IMAGE`/`CARD_INSERT`). -/
theorem p3g_CARD_MOD_NUMSEG (n m i : ℕ) (hm : m ≤ n) :
    Nat.card {x : ℕ | ∃ k < m, x = (i + k) % n} = m := by
  have hinj : Set.InjOn (fun k => (i + k) % n) (Finset.range m) := by
    intro k hk l hl hkl
    simp only [Finset.mem_coe, Finset.mem_range] at hk hl
    have hkn : k < n := lt_of_lt_of_le hk hm
    have hln : l < n := lt_of_lt_of_le hl hm
    have hmod : (i + k) % n = (i + l) % n := hkl
    rcases le_total k l with hkle | hlle
    · have hd : n ∣ (i + l) - (i + k) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
      rw [show (i + l) - (i + k) = l - k from by omega] at hd
      have hd0 : l - k = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd : n ∣ (i + k) - (i + l) := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      rw [show (i + k) - (i + l) = k - l from by omega] at hd
      have hd0 : k - l = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  have hset : {x : ℕ | ∃ k < m, x = (i + k) % n}
      = ((Finset.range m).image (fun k => (i + k) % n) : Set ℕ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_image, Finset.mem_coe,
      Finset.mem_range, eq_comm]
  have hfin : (((Finset.range m).image (fun k => (i + k) % n) : Finset ℕ) : Set ℕ).Finite :=
    ((Finset.range m).image (fun k => (i + k) % n)).finite_toSet
  rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin,
    Set.Finite.toFinset_eq_toFinset hfin, Finset.toFinset_coe,
    Finset.card_image_of_injOn hinj, Finset.card_range]

/-- OXLZLEZ2.hl:1805.  PA4 reference: PackingAuto4.lean:406 (proven, direct
`ext` in place of the HOL `CARD_SUBSET_EQ` detour). -/
theorem p3g_MOD_NUMSEG (n i : ℕ) (hn : n ≠ 0) :
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

/-- OXLZLEZ2.hl:2803: curried `MOD_INJ1` (`REWRITE_RULE[GSYM
RIGHT_FORALL_IMP_THM]`); PA3 already carries the same statement as
`MOD_INJ1_ALT` (OXLZLEZ1.hl:263), so the row is a one-line bridge. -/
theorem p3g_MOD_INJ11 (n k : ℕ) (hn : n ≠ 0) (hk : k < n) (hk0 : k ≠ 0) (x : ℕ) :
    x % n ≠ (x + k) % n := MOD_INJ1_ALT hn hk hk0 x

/-- OXLZLEZ2.hl:2806 (proved in HOL from `Flyspeck_constants.bounds`).  Lean
takes the same decimal bounds from Mathlib's `π` bounds
(Mathlib/Analysis/Real/Pi/Bounds.lean: `pi_gt_d6`/`pi_lt_d4`). -/
theorem p3g_PI_BOUNDS : (3.14159 : ℝ) < Real.pi ∧ Real.pi < 3.1416 := by
  constructor
  · exact lt_trans (by norm_num : (3.14159 : ℝ) < 3.141592) Real.pi_gt_d6
  · exact Real.pi_lt_d4

/-- OXLZLEZ2.hl:3341.  PA4 reference: PackingAuto4.lean:548 (proven). -/
theorem p3g_LEAST_BOUND_CC_GG (cc : CcV11)
    (h1 : ∀ i, cc_qu_v11 cc i → -cc_eps ≤ cc_gg_v11 cc i)
    (h2 : ∀ i, cc_qx_v11 cc i → (0 : ℝ) ≤ cc_gg_v11 cc i)
    (h3 : ∀ i, cc_qy_v11 cc i → (0 : ℝ) ≤ cc_gg_v11 cc i) (i : ℕ) :
    -cc_eps ≤ cc_gg_v11 cc i := by
  rcases p3g_QU_OR_QXY cc i with h | h | h
  · exact h1 i h
  · exact le_trans (by norm_num [cc_eps]) (h2 i h)
  · exact le_trans (by norm_num [cc_eps]) (h3 i h)

/-- OXLZLEZ2.hl:3354: `periodic_mod` with the inner `!m` curried out
(`RIGHT_FORALL_IMP_THM`); PA3's `periodic_mod` is already in that curried
shape, so the row is an alias. -/
theorem p3g_periodic_mod1 {α : Type*} {f : ℕ → α} {n : ℕ} (h : periodic f n)
    (hn : n ≠ 0) (m : ℕ) : f m = f (m % n) := periodic_mod h hn m

/-- OXLZLEZ2.hl:3361.  PA4 reference: PackingAuto4.lean:559 (proven). -/
theorem p3g_LITTLE_CC_GG3BB (cc : CcV11) (i : ℕ)
    (h1 : ∀ j, cc_qy_v11 cc j → (0 : ℝ) ≤ cc_gg3b_v11 cc j)
    (h2 : ∀ j, cc_qu_v11 cc (j + 1) ∧ cc_qy_v11 cc j →
      (0 : ℝ) ≤ cc_gg3b_v11 cc j + cc_gg_v11 cc (j + 1))
    (h3 : ∀ j, cc_qy_v11 cc j → (0 : ℝ) ≤ cc_gg_v11 cc j)
    (h4 : ∀ j, cc_qx_v11 cc j → (0 : ℝ) ≤ cc_gg_v11 cc j)
    (h5 : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1) := by
  rcases p3g_QU_OR_QXY cc (i + 1) with h | h | h
  · exact h2 i ⟨h, h5⟩
  · have hg := h4 (i + 1) h
    have hb := h1 i h5
    linarith
  · have hg := h3 (i + 1) h
    have hb := h1 i h5
    linarith

/-- OXLZLEZ2.hl:3373 (`SPEC 1 MOD_MULT_ADD` with `1 * n + p` normalised to
`p + n`); identical to Lean-core `Nat.add_mod_right`. -/
theorem p3g_MOD_ADD_CANCEL (p n : ℕ) : (p + n) % n = p % n := Nat.add_mod_right p n

/-- OXLZLEZ2.hl:3379.  PA4 reference: PackingAuto4.lean:576 (proven), with the
PA3 `periodic` (equality of predicates) replacing `periodicPropP4` (Iff). -/
theorem p3g_LITTLE_CC_GG3AA (cc : CcV11) (nn : ℕ) (i : ℕ)
    (h1 : ∀ j, cc_qy_v11 cc j → (0 : ℝ) ≤ cc_gg3a_v11 cc j)
    (h2 : ∀ j, cc_qu_v11 cc j ∧ cc_qy_v11 cc (j + 1) →
      (0 : ℝ) ≤ cc_gg_v11 cc j + cc_gg3a_v11 cc (j + 1))
    (h3 : ∀ j, cc_qy_v11 cc j → (0 : ℝ) ≤ cc_gg_v11 cc j)
    (h4 : ∀ j, cc_qx_v11 cc j → (0 : ℝ) ≤ cc_gg_v11 cc j)
    (hpqy : periodic (cc_qy_v11 cc) nn)
    (hpgg3a : periodic (cc_gg3a_v11 cc) nn)
    (hnn : nn ≠ 0)
    (h5 : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc (i + nn - 1) + cc_gg3a_v11 cc i := by
  have hj : i + nn - 1 + 1 = i + nn := by omega
  rcases p3g_QU_OR_QXY cc (i + nn - 1) with hq | hx | hy
  · have hbound := h2 (i + nn - 1) ⟨hq, by rw [hj, hpqy i]; exact h5⟩
    rw [hj] at hbound
    rw [← hpgg3a i]
    exact hbound
  · have hg := h4 (i + nn - 1) hx
    have ha := h1 i h5
    linarith
  · have hg := h3 (i + nn - 1) hy
    have ha := h1 i h5
    linarith

/-- OXLZLEZ2.hl:3431 (`SIMP_RULE[...] (SPEC (m+1) SUM_CLAUSES_LEFT)`). -/
theorem p3g_SUM_NUMSEG2 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc m (m + 1), f i = f m + f (m + 1) := by
  have hIcc : Finset.Icc m (m + 1) = insert m (Finset.Icc (m + 1) (m + 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · rintro (h | h)
      · omega
      · omega
  rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), Finset.Icc_self,
    Finset.sum_singleton]

/-- OXLZLEZ2.hl:3434 (`SIMP_RULE[...] (SPEC (m+2) SUM_CLAUSES_LEFT)`, consuming
`SUM_NUMSEG2`). -/
theorem p3g_SUM_NUMSEG33 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc m (m + 2), f i = f m + f (m + 1) + f (m + 2) := by
  have hIcc : Finset.Icc m (m + 2) = insert m (Finset.Icc (m + 1) (m + 2)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · rintro (h | h)
      · omega
      · omega
  rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), p3g_SUM_NUMSEG2]
  ring

/-- OXLZLEZ2.hl:3438 (`REWRITE_RULE[(a+1)+1 = a+2] SUM_NUMSEG33`). -/
theorem p3g_SUM_NUMSEG3 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc m (m + 2), f i = f m + f (m + 1) + f (m + 2) :=
  p3g_SUM_NUMSEG33 f m

/-- OXLZLEZ2.hl:3442 (`SIMP_RULE[...] (SPEC (m+3) SUM_CLAUSES_LEFT)`, consuming
`SUM_NUMSEG3`). -/
theorem p3g_SUM_NUMSEG44 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc m (m + 3), f i = f m + f (m + 1) + f (m + 2) + f (m + 3) := by
  have hIcc : Finset.Icc m (m + 3) = insert m (Finset.Icc (m + 1) (m + 3)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · rintro (h | h)
      · omega
      · omega
  rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), p3g_SUM_NUMSEG3]
  ring

/-- OXLZLEZ2.hl:3445 (`REWRITE_RULE[...] SUM_NUMSEG44`). -/
theorem p3g_SUM_NUMSEG4 (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc m (m + 3), f i = f m + f (m + 1) + f (m + 2) + f (m + 3) :=
  p3g_SUM_NUMSEG44 f m


/-! ## OXLZLEZ2: intra-chapter summary (OXLZLEZ2.hl:403-1734; GRHIDFA wave plan W2)

Port of the W2 wave (WAVES §W2): the seven intra-chapter rows consumed by the
OXLZLEZ2 conclusion ladder — `LXDEYBO`, `MTMLSRF` (the largest single block of
the whole lane, HOL 510 lines), `WKR_COMPTED`, `oxl6142` (= `CHQSQEY`),
`THREE_LE_CC_CARD` and `UNPNFVW`.  Rows are inserted in dependency order (the
HOL order LXDEYBO, MTMLSRF, WKR_COMPTED, oxl6142, CHQSQEY, THREE_LE_CC_CARD,
UNPNFVW is respected; WKR_COMPTED comes after MTMLSRF because the HOL proof
consumes it).  The `MTMLSRF_concl`/`UNPNFVW_concl` statement stubs above (W5
scope) are not touched.  All rows below are fully proved, with no unproved
placeholders.  Pointwise access to the 33 conjuncts of `cc_real_model_v11`
goes through the `p3h_rm_*` accessors, mirroring the HOL `ASM_SEARCH`
retrievals. -/

/-- `SUM_SUBSET_SIMPLE` (OXLZLEZ2 tactic kit): summing over a sub-`Finset` is
monotone when the summand is nonnegative on the difference. -/
private theorem p3h_sum_le_sum_of_subset {f : ℕ → ℝ} {t u : Finset ℕ}
    (hsub : t ⊆ u) (hpos : ∀ x ∈ u, x ∉ t → 0 ≤ f x) :
    ∑ x ∈ t, f x ≤ ∑ x ∈ u, f x := by
  have h1 : ∑ x ∈ u \ t, f x + ∑ x ∈ t, f x = ∑ x ∈ u, f x := Finset.sum_sdiff hsub
  have h2 : 0 ≤ ∑ x ∈ u \ t, f x := by
    refine Finset.sum_nonneg fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    exact hpos x hx1 hx2
  rw [← h1]
  linarith

/-- `SUM_CONST` specialised to `ℝ` (HOL `SUM_CONST` gives `card • a`). -/
private theorem p3h_sum_const_real (s : Finset ℕ) (a : ℝ) : ∑ i ∈ s, a = s.card * a := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-- `cc_real_model_v11` conjunct 1: `periodic (cc_azim_v11 cc) (cc_card_v11 cc)`. -/
private theorem p3h_rm_periodic_azim {cc : CcV11} (hr : cc_real_model_v11 cc) :
    periodic (cc_azim_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨h1, -⟩ := hr
  exact h1

/-- `cc_real_model_v11` conjunct 2. -/
private theorem p3h_rm_periodic_gg {cc : CcV11} (hr : cc_real_model_v11 cc) :
    periodic (cc_gg_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, h2, -⟩ := hr
  exact h2

/-- `cc_real_model_v11` conjunct 3. -/
private theorem p3h_rm_periodic_gg3a {cc : CcV11} (hr : cc_real_model_v11 cc) :
    periodic (cc_gg3a_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, -, h3, -⟩ := hr
  exact h3

/-- `cc_real_model_v11` conjunct 4. -/
private theorem p3h_rm_periodic_gg3b {cc : CcV11} (hr : cc_real_model_v11 cc) :
    periodic (cc_gg3b_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, -, -, h4, -⟩ := hr
  exact h4

/-- `cc_real_model_v11` conjunct 5. -/
private theorem p3h_rm_azim_lb {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ) :
    (0.606 : ℝ) ≤ cc_azim_v11 cc i := by
  obtain ⟨-, -, -, -, h5, -⟩ := hr
  exact h5 i

/-- `cc_real_model_v11` conjunct 6. -/
private theorem p3h_rm_azim_4cell {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_4cell_v11 cc i) : cc_azim_v11 cc i < 2.8 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := hr
  exact h6 i h

/-- `cc_real_model_v11` conjunct 7. -/
private theorem p3h_rm_sum_azim {cc : CcV11} (hr : cc_real_model_v11 cc) :
    ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc i = 2 * Real.pi := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hr
  exact h7

/-- `cc_real_model_v11` conjunct 12. -/
private theorem p3h_rm_qu_qy_next {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h1 : cc_qu_v11 cc i) (h2 : cc_qy_v11 cc (i + 1)) :
    (0 : ℝ) ≤ cc_gg_v11 cc i + cc_gg3a_v11 cc (i + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := hr
  exact h12 i ⟨h1, h2⟩

/-- `cc_real_model_v11` conjunct 13. -/
private theorem p3h_rm_qu_next_qy {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h1 : cc_qu_v11 cc (i + 1)) (h2 : cc_qy_v11 cc i) :
    (0 : ℝ) ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := hr
  exact h13 i ⟨h1, h2⟩

/-- `cc_real_model_v11` conjunct 14. -/
private theorem p3h_rm_4cell_spine {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_4cell_v11 cc i) : a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := hr
  exact h14 i h

/-- `cc_real_model_v11` conjunct 18. -/
private theorem p3h_rm_qx_nn {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_qx_v11 cc i) : (0 : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -⟩ := hr
  exact h18 i h

/-- `cc_real_model_v11` conjunct 26. -/
private theorem p3h_rm_qy_le {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_qy_v11 cc i) : cc_gg3a_v11 cc i + cc_gg3b_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h26, -⟩ := hr
  exact h26 i h

/-- `cc_real_model_v11` conjunct 27. -/
private theorem p3h_rm_qy_gg3a {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg3a_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h27, -⟩ := hr
  exact h27 i h

/-- `cc_real_model_v11` conjunct 28. -/
private theorem p3h_rm_qy_gg3b {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_qy_v11 cc i) : (0 : ℝ) ≤ cc_gg3b_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h28, -⟩ := hr
  exact h28 i h

/-- `cc_real_model_v11` conjunct 29. -/
private theorem p3h_rm_qy_azim {cc : CcV11} (hr : cc_real_model_v11 cc) {i : ℕ}
    (h : cc_qy_v11 cc i) : (0.008 : ℝ) * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, h29, -⟩ := hr
  exact h29 i h

/-- `cc_bool_model_v11` conjunct 7. -/
private theorem p3h_bm_periodic_4cell {cc : CcV11} (hb : cc_bool_model_v11 cc) :
    periodic (cc_4cell_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hb
  exact h7

/-- `periodic_fn` (OXLZLEZ1.hl:347) consequence: `periodic (cc_qu_v11 cc)`. -/
private theorem p3h_pf_qu {cc : CcV11} (hb : cc_bool_model_v11 cc) :
    periodic (cc_qu_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, hq, -, -⟩ := periodic_fn hb
  exact hq

/-- `periodic_fn` consequence: `periodic (cc_qy_v11 cc)`. -/
private theorem p3h_pf_qy {cc : CcV11} (hb : cc_bool_model_v11 cc) :
    periodic (cc_qy_v11 cc) (cc_card_v11 cc) := by
  obtain ⟨-, -, -, hqy⟩ := periodic_fn hb
  exact hqy

/-- OXLZLEZ2.hl:564 (`MTMLSRF`, proving `MTMLSRF_concl` OXLZLEZ1.hl:138) —
checkpoint 2a of WAVES §W2.  The proof is the HOL partition argument: under
the negation of the conclusion, the index circle `1..nn` splits into
`ss` (negative-gg `qu` indices), `sab` (their `qy` successors/predecessors'
shifted partners, covered by the `gg3a`/`gg3b` nonnegativity rows), and a
residual with `gg ≥ 0`; the two cyclic-shift correspondences
(`∑ saa gg3a = ∑ sa (gg3a (i+1))`, `∑ sbb gg3b = ∑ sb (gg3b (i-1))`) reduce
the shifted sums to the rows 12/13 of `cc_real_model_v11`, forcing
`0 ≤ ∑₁..nn gg = ∑₀..nn-1 gg < 0`. -/
theorem p3h_MTMLSRF (cc : CcV11) (_hp : cc_bool_prep_v11 cc) (hb : cc_bool_model_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1) := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have h2nn : 2 ≤ cc_card_v11 cc := CC_CARD2 hb hr hsum
  set nn := cc_card_v11 cc with hnn_def
  -- periodicity, re-typed at nn
  have hpgg : periodic (cc_gg_v11 cc) nn := p3h_rm_periodic_gg hr
  have hpgg3a : periodic (cc_gg3a_v11 cc) nn := p3h_rm_periodic_gg3a hr
  have hpgg3b : periodic (cc_gg3b_v11 cc) nn := p3h_rm_periodic_gg3b hr
  have hpqu : periodic (cc_qu_v11 cc) nn := p3h_pf_qu hb
  have hpqy : periodic (cc_qy_v11 cc) nn := p3h_pf_qy hb
  have e_gg_nn0 : cc_gg_v11 cc nn = cc_gg_v11 cc 0 := by
    have h := hpgg 0; rwa [Nat.zero_add] at h
  have e_gg_nn1 : cc_gg_v11 cc (nn + 1) = cc_gg_v11 cc 1 := by
    have h := hpgg 1; rwa [Nat.add_comm] at h
  have e_qu_nn0 : cc_qu_v11 cc nn = cc_qu_v11 cc 0 := by
    have h := hpqu 0; rwa [Nat.zero_add] at h
  have e_qu_nn1 : cc_qu_v11 cc (nn + 1) = cc_qu_v11 cc 1 := by
    have h := hpqu 1; rwa [Nat.add_comm] at h
  have e_qy_nn0 : cc_qy_v11 cc nn = cc_qy_v11 cc 0 := by
    have h := hpqy 0; rwa [Nat.zero_add] at h
  have e_qy_nn1 : cc_qy_v11 cc (nn + 1) = cc_qy_v11 cc 1 := by
    have h := hpqy 1; rwa [Nat.add_comm] at h
  have e_gg3a_nn1 : cc_gg3a_v11 cc (nn + 1) = cc_gg3a_v11 cc 1 := by
    have h := hpgg3a 1; rwa [Nat.add_comm] at h
  have e_gg3b_nn0 : cc_gg3b_v11 cc nn = cc_gg3b_v11 cc 0 := by
    have h := hpgg3b 0; rwa [Nat.zero_add] at h
  by_cases hfull : ∃ i, 0 < i ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
      cc_4cell_v11 cc (i + 1) ∧ cc_4cell_v11 cc (i - 1)
  · exact hfull
  · push_neg at hfull
    -- hfull : ∀ i, 0 < i → gg i < 0 → qu i → ¬(4cell (i+1) ∧ 4cell (i-1))
    have H : ∀ i, 0 < i → cc_gg_v11 cc i < 0 → cc_qu_v11 cc i →
        cc_4cell_v11 cc (i + 1) → ¬ cc_4cell_v11 cc (i - 1) := hfull
    set S : Finset ℕ := Finset.Icc 1 nn with hS_def
    set u : ℕ → ℕ := fun i => if i = nn then 1 else i + 1 with hu_def
    have hmemS : ∀ i, i ∈ S ↔ 1 ≤ i ∧ i ≤ nn := fun i => by
      rw [hS_def]; simp only [Finset.mem_Icc]
    have hnnS : nn ∈ S := (hmemS nn).mpr ⟨by omega, le_refl nn⟩
    -- the six sets of the HOL proof
    set sa : Finset ℕ :=
      S.filter (fun i => cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧ cc_qy_v11 cc (i + 1)) with hsa_def
    set sb : Finset ℕ :=
      S.filter (fun i => cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧ cc_qy_v11 cc (i - 1)) with hsb_def
    set ss : Finset ℕ :=
      S.filter (fun i => cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i) with hss_def
    set saa : Finset ℕ :=
      S.filter (fun x => cc_qy_v11 cc x ∧ cc_gg_v11 cc (x - 1) < 0 ∧ cc_qu_v11 cc (x - 1))
        with hsaa_def
    set sbb : Finset ℕ :=
      S.filter (fun x => cc_qy_v11 cc x ∧ cc_gg_v11 cc (x + 1) < 0 ∧ cc_qu_v11 cc (x + 1))
        with hsbb_def
    set sab : Finset ℕ :=
      S.filter (fun x => cc_qy_v11 cc x ∧
        ((cc_gg_v11 cc (x + 1) < 0 ∧ cc_qu_v11 cc (x + 1)) ∨
          (cc_gg_v11 cc (x - 1) < 0 ∧ cc_qu_v11 cc (x - 1)))) with hsab_def
    -- membership characterisations
    have msa : ∀ i, i ∈ sa ↔ (i ∈ S ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
        cc_qy_v11 cc (i + 1)) := fun i => by
      rw [hsa_def]; simp only [Finset.mem_filter]
    have msb : ∀ i, i ∈ sb ↔ (i ∈ S ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧
        cc_qy_v11 cc (i - 1)) := fun i => by
      rw [hsb_def]; simp only [Finset.mem_filter]
    have mss : ∀ i, i ∈ ss ↔ (i ∈ S ∧ cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i) := fun i => by
      rw [hss_def]; simp only [Finset.mem_filter]
    have msaa : ∀ x, x ∈ saa ↔ (x ∈ S ∧ cc_qy_v11 cc x ∧ cc_gg_v11 cc (x - 1) < 0 ∧
        cc_qu_v11 cc (x - 1)) := fun x => by
      rw [hsaa_def]; simp only [Finset.mem_filter]
    have msbb : ∀ x, x ∈ sbb ↔ (x ∈ S ∧ cc_qy_v11 cc x ∧ cc_gg_v11 cc (x + 1) < 0 ∧
        cc_qu_v11 cc (x + 1)) := fun x => by
      rw [hsbb_def]; simp only [Finset.mem_filter]
    have msab : ∀ x, x ∈ sab ↔ (x ∈ S ∧ cc_qy_v11 cc x ∧
        ((cc_gg_v11 cc (x + 1) < 0 ∧ cc_qu_v11 cc (x + 1)) ∨
          (cc_gg_v11 cc (x - 1) < 0 ∧ cc_qu_v11 cc (x - 1)))) := fun x => by
      rw [hsab_def]; simp only [Finset.mem_filter]
    -- basic inclusions and disjointness
    have hsa_ss : sa ⊆ ss := by
      intro x hx
      rw [msa x] at hx
      rw [mss x]
      exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
    have hssS : ss ⊆ S := Finset.filter_subset _ _
    have hsabS : sab ⊆ S := Finset.filter_subset _ _
    have hdisj : Disjoint ss sab := by
      rw [Finset.disjoint_left]
      intro a ha hab
      rw [mss a] at ha
      rw [msab a] at hab
      exact hab.2.1 ha.2.2.2.1
    have hsaa_sab : saa ⊆ sab := by
      intro x hx
      rw [msaa x] at hx
      rw [msab x]
      exact ⟨hx.1, hx.2.1, Or.inr ⟨hx.2.2.1, hx.2.2.2⟩⟩
    have hsbb_sab : sbb ⊆ sab := by
      intro x hx
      rw [msbb x] at hx
      rw [msab x]
      exact ⟨hx.1, hx.2.1, Or.inl ⟨hx.2.2.1, hx.2.2.2⟩⟩
    have hss_sa_sb : ss \ sa ⊆ sb := by
      intro x hx
      obtain ⟨hix, hnx⟩ := Finset.mem_sdiff.mp hx
      rw [mss x] at hix
      obtain ⟨hxS, hxg, hxu⟩ := hix
      have hnotsa : ¬ (cc_gg_v11 cc x < 0 ∧ cc_qu_v11 cc x ∧ cc_qy_v11 cc (x + 1)) :=
        fun hc => hnx ((msa x).mpr ⟨hxS, hc⟩)
      have h4next : cc_4cell_v11 cc (x + 1) := by
        by_contra hcon
        exact hnotsa ⟨hxg, hxu, hcon⟩
      have hx0 : 0 < x := by have h := (hmemS x).mp hxS; omega
      have hn4m : ¬ cc_4cell_v11 cc (x - 1) := H x hx0 hxg hxu h4next
      rw [msb x]
      exact ⟨hxS, hxg, hxu, hn4m⟩
    -- the cyclic successor `u` on {1..nn} and its two shift identities
    have hu_of_ne : ∀ i, i ≠ nn → u i = i + 1 := by
      intro i hi; simp only [hu_def, if_neg hi]
    have hu_nn : u nn = 1 := by simp only [hu_def, if_pos rfl]
    have hu_inj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j := by
      intro i hi j hj hij
      rw [hmemS] at hi hj
      rcases eq_or_ne i nn with hin | hin
      · subst hin
        rw [hu_nn] at hij
        rcases eq_or_ne j nn with hjn | hjn
        · exact hjn.symm
        · rw [hu_of_ne j hjn] at hij; omega
      · rcases eq_or_ne j nn with hjn | hjn
        · subst hjn
          rw [hu_of_ne i hin, hu_nn] at hij; omega
        · rw [hu_of_ne i hin, hu_of_ne j hjn] at hij; omega
    have himg_saa : saa = sa.image u := by
      ext x
      rw [msaa x, Finset.mem_image]
      constructor
      · rintro ⟨hxS, hqyx, hcbg, hcbq⟩
        obtain ⟨hx1, hx2⟩ := (hmemS x).mp hxS
        rcases Nat.lt_or_ge x 2 with hxlt | hxge
        · have hxe : x = 1 := by omega
          subst hxe
          exact ⟨nn, (msa nn).mpr ⟨hnnS, by rw [e_gg_nn0]; exact hcbg,
            by rw [e_qu_nn0]; exact hcbq, by rw [e_qy_nn1]; exact hqyx⟩, hu_nn⟩
        · refine ⟨x - 1, (msa (x - 1)).mpr ⟨(hmemS (x - 1)).mpr ⟨by omega, by omega⟩,
            hcbg, hcbq, ?_⟩, ?_⟩
          · rw [show (x - 1) + 1 = x from by omega]
            exact hqyx
          · rw [hu_of_ne (x - 1) (by omega)]
            omega
      · rintro ⟨i, hi, rfl⟩
        rw [msa i] at hi
        obtain ⟨hiS, hgi, hqui, hqyi1⟩ := hi
        obtain ⟨hi1, hi2⟩ := (hmemS i).mp hiS
        rcases eq_or_ne i nn with hin | hin
        · subst hin
          rw [hu_nn]
          refine ⟨(hmemS 1).mpr ⟨le_refl 1, by omega⟩, ?_, ?_, ?_⟩
          · rw [← e_qy_nn1]; exact hqyi1
          · show cc_gg_v11 cc 0 < 0
            rw [← e_gg_nn0]; exact hgi
          · show cc_qu_v11 cc 0
            rw [← e_qu_nn0]; exact hqui
        · rw [hu_of_ne i hin]
          refine ⟨(hmemS (i + 1)).mpr ⟨by omega, by omega⟩, hqyi1, ?_, ?_⟩
          · show cc_gg_v11 cc i < 0
            exact hgi
          · show cc_qu_v11 cc i
            exact hqui
    have himg_sb : sb = sbb.image u := by
      ext y
      rw [msb y, Finset.mem_image]
      constructor
      · rintro ⟨hyS, hgy, hquy, hqym⟩
        obtain ⟨hy1, hy2⟩ := (hmemS y).mp hyS
        rcases Nat.lt_or_ge y 2 with hylt | hyge
        · have hye : y = 1 := by omega
          subst hye
          exact ⟨nn, (msbb nn).mpr ⟨hnnS, by rw [e_qy_nn0]; exact hqym,
            by rw [e_gg_nn1]; exact hgy, by rw [e_qu_nn1]; exact hquy⟩, hu_nn⟩
        · refine ⟨y - 1, (msbb (y - 1)).mpr ⟨(hmemS (y - 1)).mpr ⟨by omega, by omega⟩,
            hqym, ?_, ?_⟩, ?_⟩
          · rw [show (y - 1) + 1 = y from by omega]; exact hgy
          · rw [show (y - 1) + 1 = y from by omega]; exact hquy
          · rw [hu_of_ne (y - 1) (by omega)]
            omega
      · rintro ⟨x, hx, rfl⟩
        rw [msbb x] at hx
        obtain ⟨hxS, hqyx, hgx1, hqux1⟩ := hx
        obtain ⟨hx1, hx2⟩ := (hmemS x).mp hxS
        rcases eq_or_ne x nn with hxn | hxn
        · subst hxn
          rw [hu_nn]
          refine ⟨(hmemS 1).mpr ⟨le_refl 1, by omega⟩, ?_, ?_, ?_⟩
          · show cc_gg_v11 cc 1 < 0
            rw [← e_gg_nn1]; exact hgx1
          · show cc_qu_v11 cc 1
            rw [← e_qu_nn1]; exact hqux1
          · show cc_qy_v11 cc 0
            rw [← e_qy_nn0]; exact hqyx
        · rw [hu_of_ne x hxn]
          refine ⟨(hmemS (x + 1)).mpr ⟨by omega, by omega⟩, hgx1, hqux1, ?_⟩
          show cc_qy_v11 cc x
          exact hqyx
    -- the two shift sums
    have hshift1 : ∑ x ∈ saa, cc_gg3a_v11 cc x = ∑ i ∈ sa, cc_gg3a_v11 cc (i + 1) := by
      rw [himg_saa, Finset.sum_image (fun i hi j hj hij =>
        hu_inj i ((msa i).mp hi).1 j ((msa j).mp hj).1 hij)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases eq_or_ne i nn with hin | hin
      · subst hin
        rw [hu_nn, e_gg3a_nn1]
      · rw [hu_of_ne i hin]
    have hshift2 : ∑ x ∈ sbb, cc_gg3b_v11 cc x = ∑ i ∈ sb, cc_gg3b_v11 cc (i - 1) := by
      rw [himg_sb, Finset.sum_image (fun x hx y hy hxy =>
        hu_inj x ((msbb x).mp hx).1 y ((msbb y).mp hy).1 hxy)]
      refine Finset.sum_congr rfl fun x hx => ?_
      rcases eq_or_ne x nn with hxn | hxn
      · subst hxn
        rw [hu_nn]
        show cc_gg3b_v11 cc nn = cc_gg3b_v11 cc 0
        rw [e_gg3b_nn0]
      · rw [hu_of_ne x hxn]
        rfl
    -- the nonnegative pieces of the partition
    have hsa_pos : (0 : ℝ) ≤ ∑ i ∈ sa, (cc_gg3a_v11 cc (i + 1) + cc_gg_v11 cc i) := by
      refine Finset.sum_nonneg fun i hi => ?_
      rw [msa i] at hi
      obtain ⟨-, hgi, hqui, hqyi1⟩ := hi
      linarith [p3h_rm_qu_qy_next hr hqui hqyi1]
    have hssa_pos : (0 : ℝ) ≤ ∑ i ∈ ss \ sa, (cc_gg3b_v11 cc (i - 1) + cc_gg_v11 cc i) := by
      refine Finset.sum_nonneg fun i hi => ?_
      obtain ⟨hiss, hnsa⟩ := Finset.mem_sdiff.mp hi
      rw [mss i] at hiss
      obtain ⟨hiS, hgi, hqui⟩ := hiss
      have hnotsa : ¬ (cc_gg_v11 cc i < 0 ∧ cc_qu_v11 cc i ∧ cc_qy_v11 cc (i + 1)) :=
        fun hc => hnsa ((msa i).mpr ⟨hiS, hc⟩)
      have h4next : cc_4cell_v11 cc (i + 1) := by
        by_contra hcon
        exact hnotsa ⟨hgi, hqui, hcon⟩
      have hi0 : 0 < i := by have h := (hmemS i).mp hiS; omega
      have hn4m : ¬ cc_4cell_v11 cc (i - 1) := H i hi0 hgi hqui h4next
      have hqi1 : (i - 1) + 1 = i := by have h := (hmemS i).mp hiS; omega
      have hkey := p3h_rm_qu_next_qy (i := i - 1) hr (by rw [hqi1]; exact hqui) hn4m
      rw [hqi1] at hkey
      linarith
    have hss_split : ∑ i ∈ ss, cc_gg_v11 cc i
        = ∑ i ∈ ss \ sa, cc_gg_v11 cc i + ∑ i ∈ sa, cc_gg_v11 cc i := by
      have h1 : ∑ i ∈ ss \ sa, cc_gg_v11 cc i + ∑ i ∈ sa, cc_gg_v11 cc i
          = ∑ i ∈ ss, cc_gg_v11 cc i := Finset.sum_sdiff hsa_ss
      linarith
    have hsb_ge : ∑ i ∈ ss \ sa, cc_gg3b_v11 cc (i - 1)
        ≤ ∑ i ∈ sb, cc_gg3b_v11 cc (i - 1) := by
      refine p3h_sum_le_sum_of_subset hss_sa_sb ?_
      intro x hx _hnot
      rw [msb x] at hx
      exact p3h_rm_qy_gg3b hr hx.2.2.2
    have hmain : (0 : ℝ) ≤ ∑ x ∈ saa, cc_gg3a_v11 cc x + ∑ x ∈ sbb, cc_gg3b_v11 cc x
        + ∑ i ∈ ss, cc_gg_v11 cc i := by
      have e1 := hshift1
      have e2 := hshift2
      have e3 := hss_split
      have e4 := hsa_pos
      have e5 := hssa_pos
      have e6 := hsb_ge
      have ed1 : ∑ i ∈ sa, cc_gg3a_v11 cc (i + 1) + ∑ i ∈ sa, cc_gg_v11 cc i
          = ∑ i ∈ sa, (cc_gg3a_v11 cc (i + 1) + cc_gg_v11 cc i) := by
        rw [Finset.sum_add_distrib]
      have ed2 : ∑ i ∈ ss \ sa, cc_gg3b_v11 cc (i - 1) + ∑ i ∈ ss \ sa, cc_gg_v11 cc i
          = ∑ i ∈ ss \ sa, (cc_gg3b_v11 cc (i - 1) + cc_gg_v11 cc i) := by
        rw [Finset.sum_add_distrib]
      linarith
    -- the sab cover
    have hsg : ∑ i ∈ ss ∪ sab, cc_gg_v11 cc i
        = ∑ i ∈ ss, cc_gg_v11 cc i + ∑ i ∈ sab, cc_gg_v11 cc i :=
      Finset.sum_union hdisj
    have hA1 : ∑ x ∈ saa, cc_gg3a_v11 cc x ≤ ∑ x ∈ sab, cc_gg3a_v11 cc x := by
      refine p3h_sum_le_sum_of_subset hsaa_sab ?_
      intro x hx _hnot
      rw [msab x] at hx
      exact p3h_rm_qy_gg3a hr hx.2.1
    have hB1 : ∑ x ∈ sbb, cc_gg3b_v11 cc x ≤ ∑ x ∈ sab, cc_gg3b_v11 cc x := by
      refine p3h_sum_le_sum_of_subset hsbb_sab ?_
      intro x hx _hnot
      rw [msab x] at hx
      exact p3h_rm_qy_gg3b hr hx.2.1
    have hAB : ∑ x ∈ sab, cc_gg3a_v11 cc x + ∑ x ∈ sab, cc_gg3b_v11 cc x
        ≤ ∑ x ∈ sab, cc_gg_v11 cc x := by
      have h1 : ∑ x ∈ sab, cc_gg3a_v11 cc x + ∑ x ∈ sab, cc_gg3b_v11 cc x
          = ∑ x ∈ sab, (cc_gg3a_v11 cc x + cc_gg3b_v11 cc x) := by
        rw [Finset.sum_add_distrib]
      have h2 : ∑ x ∈ sab, (cc_gg3a_v11 cc x + cc_gg3b_v11 cc x)
          ≤ ∑ x ∈ sab, cc_gg_v11 cc x := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [msab x] at hx
        exact p3h_rm_qy_le hr hx.2.1
      linarith
    have hsgS : ss ∪ sab ⊆ S := Finset.union_subset hssS hsabS
    have hS_split : ∑ i ∈ S \ (ss ∪ sab), cc_gg_v11 cc i + ∑ i ∈ ss ∪ sab, cc_gg_v11 cc i
        = ∑ i ∈ S, cc_gg_v11 cc i := Finset.sum_sdiff hsgS
    have hdiff_pos : (0 : ℝ) ≤ ∑ i ∈ S \ (ss ∪ sab), cc_gg_v11 cc i := by
      refine Finset.sum_nonneg fun x hx => ?_
      obtain ⟨hxS, hnot⟩ := Finset.mem_sdiff.mp hx
      have hnotss : x ∉ ss := fun hc => hnot (Finset.mem_union_left _ hc)
      by_cases hgx : cc_gg_v11 cc x < 0
      · exfalso
        have hnqu : ¬ cc_qu_v11 cc x := fun hqu => hnotss ((mss x).mpr ⟨hxS, hgx, hqu⟩)
        rcases QY_QX_QU hb x with hqu | hqy | hqx
        · exact hnqu hqu
        · linarith [p3g_QY_NN0 hb hr hqy, hgx]
        · linarith [p3h_rm_qx_nn hr hqx, hgx]
      · exact le_of_not_gt hgx
    have hSpos : (0 : ℝ) ≤ ∑ i ∈ S, cc_gg_v11 cc i := by
      have h1 := hmain
      have h2 := hsg
      have h3 := hA1
      have h4 := hB1
      have h5 := hAB
      have h6 := hS_split
      have h7 := hdiff_pos
      linarith
    -- ∑₀..nn-1 gg = ∑₁..nn gg (periodic_sum with i = 1)
    have hper : ∑ i ∈ Finset.Icc 0 (nn - 1), cc_gg_v11 cc i
        = ∑ i ∈ S, cc_gg_v11 cc i := by
      have h2 : Finset.Icc 1 (nn - 1 + 1) = Finset.Icc 1 nn := by
        ext x
        simp only [Finset.mem_Icc]
        omega
      have h3 : Finset.Icc 0 (nn - 1) = Finset.range nn := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_range]
        omega
      rw [h3]
      have h1 := periodic_sum hpgg hnn0 1
      rw [h2] at h1
      rw [hS_def]
      exact h1.symm
    exfalso
    linarith

/-- OXLZLEZ2.hl:1100 (`WKR_COMPTED`).  The HOL row carries the explicit
hypothesis `indSet = 0..cc_card_v11 cc - 1`, a pure abbreviation consumed to
read `i IN indSet`; here the `Finset` is written out directly. -/
theorem p3h_WKR_COMPTED (cc : CcV11) (_hp : cc_bool_prep_v11 cc) (hb : cc_bool_model_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∃ i j k, ¬(i = j ∨ j = k ∨ k = i) ∧
      i ∈ Finset.Icc 0 (cc_card_v11 cc - 1) ∧ j ∈ Finset.Icc 0 (cc_card_v11 cc - 1) ∧
        k ∈ Finset.Icc 0 (cc_card_v11 cc - 1) ∧
        cc_4cell_v11 cc i ∧ cc_4cell_v11 cc j ∧ cc_4cell_v11 cc k := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have h2nn : 2 ≤ cc_card_v11 cc := CC_CARD2 hb hr hsum
  have hper4 : periodic (cc_4cell_v11 cc) (cc_card_v11 cc) := p3h_bm_periodic_4cell hb
  have hperazim : periodic (cc_azim_v11 cc) (cc_card_v11 cc) := p3h_rm_periodic_azim hr
  have hmod4 : ∀ x, cc_4cell_v11 cc (x % cc_card_v11 cc) = cc_4cell_v11 cc x :=
    fun x => (periodic_mod hper4 hnn0 x).symm
  obtain ⟨i, hi0, higi, hqui, h4p, h4m⟩ := p3h_MTMLSRF cc _hp hb hr hsum
  have h4i : cc_4cell_v11 cc i := hqui.2.1
  by_cases hnn2 : cc_card_v11 cc = 2
  · -- card = 2 is impossible: both azim values are 4cell-bounded by 2.8, but sum to 2π
    exfalso
    have hsumazim := p3h_rm_sum_azim hr
    rw [hnn2] at hsumazim
    have h01 : ∑ j ∈ Finset.Icc 0 1, cc_azim_v11 cc j = cc_azim_v11 cc 0 + cc_azim_v11 cc 1 :=
      p3g_SUM_NUMSEG2 _ 0
    have ha1 : cc_azim_v11 cc i < 2.8 := p3h_rm_azim_4cell hr h4i
    have ha2 : cc_azim_v11 cc (i + 1) < 2.8 := p3h_rm_azim_4cell hr h4p
    have m1 : cc_azim_v11 cc (i % 2) = cc_azim_v11 cc i := by
      have h := periodic_mod hperazim hnn0 i
      rw [hnn2] at h
      exact h.symm
    have m2 : cc_azim_v11 cc ((i + 1) % 2) = cc_azim_v11 cc (i + 1) := by
      have h := periodic_mod hperazim hnn0 (i + 1)
      rw [hnn2] at h
      exact h.symm
    have hne : i % 2 ≠ (i + 1) % 2 :=
      p3g_MOD_INJ11 2 1 (by omega) (by omega) (by omega) i
    have hmod2 : ∀ k : ℕ, k % 2 = 0 ∨ k % 2 = 1 := fun k => by omega
    rcases hmod2 i with r1 | r1 <;> rcases hmod2 (i + 1) with r2 | r2
    · exact absurd (show i % 2 = (i + 1) % 2 from by rw [r1, r2]) hne
    · have hchain : 2 * Real.pi = cc_azim_v11 cc i + cc_azim_v11 cc (i + 1) := by
        rw [← hsumazim, h01, ← m1, ← m2, r1, r2]
      have hpi : (2 : ℝ) * Real.pi > 5.6 := by linarith [p3g_PI_BOUNDS.1]
      linarith
    · have hchain : 2 * Real.pi = cc_azim_v11 cc i + cc_azim_v11 cc (i + 1) := by
        rw [← hsumazim, h01, ← m1, ← m2, r1, r2, add_comm]
      have hpi : (2 : ℝ) * Real.pi > 5.6 := by linarith [p3g_PI_BOUNDS.1]
      linarith
    · exact absurd (show i % 2 = (i + 1) % 2 from by rw [r1, r2]) hne
  · -- card ≥ 3: the three cyclic residues of the MTMLSRF witness are distinct 4cells
    have h3nn : 3 ≤ cc_card_v11 cc := by omega
    refine ⟨(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc,
      p3g_THREE_MOD_CONSECUTIVES i (cc_card_v11 cc) hi0 h3nn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact MOD_IN_NUMSEG hnn0
    · exact MOD_IN_NUMSEG hnn0
    · exact MOD_IN_NUMSEG hnn0
    · rw [hmod4 (i - 1)]; exact h4m
    · rw [hmod4 i]; exact h4i
    · rw [hmod4 (i + 1)]; exact h4p

/-- OXLZLEZ2.hl:1195 (`oxl6142`, proving `CHQSQEY_concl` OXLZLEZ1.hl:135):
three pairwise-distinct 4cell indices force the 4cell count up to 3. -/
theorem p3h_oxl6142 (cc : CcV11) (hb : cc_bool_model_v11 cc) (hp : cc_bool_prep_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) := by
  obtain ⟨a, b, c, habc, ha, hbb, hc, h4a, h4b, h4c⟩ := p3h_WKR_COMPTED cc hp hb hr hsum
  have hsub : ({a, b, c} : Finset ℕ) ⊆
      Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact ⟨ha, h4a⟩
    · exact ⟨hbb, h4b⟩
    · exact ⟨hc, h4c⟩
  have hbne : a ∉ ({b, c} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact habc (Or.inl rfl)
    · exact habc (Or.inr (Or.inr rfl))
  have hcne : b ∉ ({c} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    intro hbc
    exact habc (Or.inr (Or.inl hbc))
  have hcard3 : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem hbne, Finset.card_insert_of_notMem hcne,
      Finset.card_singleton]
  have hsize : cc_size_v11 cc (cc_4cell_v11 cc)
      = (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  rw [hsize]
  calc 3 = ({a, b, c} : Finset ℕ).card := hcard3.symm
    _ ≤ (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card :=
      Finset.card_le_card hsub

/-- OXLZLEZ2.hl:1225 (`CHQSQEY = oxl6142`). -/
theorem p3h_CHQSQEY (cc : CcV11) (hb : cc_bool_model_v11 cc) (hp : cc_bool_prep_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_size_v11 cc (cc_4cell_v11 cc) := p3h_oxl6142 cc hb hp hr hsum

/-- OXLZLEZ2.hl:1228 (`THREE_LE_CC_CARD`) — the WAVES §W2 acceptance anchor
(common predecessor of the `IPVICGW` and `UTEOITF` ladders). -/
theorem p3h_THREE_LE_CC_CARD (cc : CcV11) (hb : cc_bool_model_v11 cc)
    (hp : cc_bool_prep_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    3 ≤ cc_card_v11 cc := by
  have h3 := p3h_oxl6142 cc hb hp hr hsum
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hcard : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    have h : Finset.Icc 0 (cc_card_v11 cc - 1) = Finset.range (cc_card_v11 cc) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [h, Finset.card_range]
  calc 3 ≤ (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card :=
      by exact h3
    _ ≤ (Finset.Icc 0 (cc_card_v11 cc - 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = cc_card_v11 cc := hcard

/-- OXLZLEZ2.hl:403 (`LXDEYBO`, proving `LXDEYBO_concl` OXLZLEZ1.hl:142).  The
`cc_bool_prep_v11` hypothesis is present in the frozen conclusion but unused
by the proof (as in HOL). -/
theorem p3h_LXDEYBO (cc : CcV11) (_hp : cc_bool_prep_v11 cc) (hb : cc_bool_model_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_4cell_v11 cc) ≤ 4 := by
  set nn := cc_card_v11 cc with hnn_def
  have h7 : ∑ i ∈ Finset.Icc 0 (nn - 1), cc_azim_v11 cc i = 2 * Real.pi :=
    p3h_rm_sum_azim hr
  set S : Finset ℕ := Finset.Icc 0 (nn - 1) with hS_def
  set ss : Finset ℕ := S.filter (cc_4cell_v11 cc) with hss_def
  have hsize : cc_size_v11 cc (cc_4cell_v11 cc) = ss.card := rfl
  by_cases hcd : 4 < ss.card
  · exfalso
    have h5cd : 5 ≤ ss.card := by omega
    -- ∑ ss gg ≤ ∑ S gg (the complement is qy, with gg ≥ 0 there)
    have hc1 : ∑ i ∈ ss, cc_gg_v11 cc i ≤ ∑ i ∈ S, cc_gg_v11 cc i := by
      refine p3h_sum_le_sum_of_subset (Finset.filter_subset _ _) ?_
      intro x hx hnotin
      have hx4 : ¬ cc_4cell_v11 cc x := fun h4 => hnotin (Finset.mem_filter.mpr ⟨hx, h4⟩)
      exact p3g_QY_NN0 hb hr hx4
    -- pointwise spine bound on ss
    have hpoint : ∀ x ∈ ss, a_spine5 + b_spine5 * cc_azim_v11 cc x ≤ cc_gg_v11 cc x := by
      intro x hx
      exact p3h_rm_4cell_spine hr (Finset.mem_filter.mp hx).2
    have hc2 : ∑ i ∈ ss, (a_spine5 + b_spine5 * cc_azim_v11 cc i)
        ≤ ∑ i ∈ ss, cc_gg_v11 cc i := Finset.sum_le_sum hpoint
    -- ∑ ss (a + b·azim) = card(ss) · a + b · ∑ ss azim
    have hc3 : ∑ i ∈ ss, (a_spine5 + b_spine5 * cc_azim_v11 cc i)
        = ss.card * a_spine5 + b_spine5 * ∑ i ∈ ss, cc_azim_v11 cc i := by
      rw [Finset.sum_add_distrib, p3h_sum_const_real, Finset.mul_sum]
    -- ∑ ss azim ≤ ∑ S azim = 2π
    have hc4 : ∑ i ∈ ss, cc_azim_v11 cc i ≤ 2 * Real.pi := by
      have h1 : ∑ i ∈ ss, cc_azim_v11 cc i ≤ ∑ i ∈ S, cc_azim_v11 cc i := by
        refine p3h_sum_le_sum_of_subset (Finset.filter_subset _ _) ?_
        intro x hx hnotin
        have hx4 : ¬ cc_4cell_v11 cc x := fun h4 => hnotin (Finset.mem_filter.mpr ⟨hx, h4⟩)
        linarith [p3h_rm_azim_lb hr x]
      linarith [h1, h7]
    -- numerics: 5 · a_spine5 + b_spine5 · 2π > 0 (uses π < 3.1416)
    have hb5 : b_spine5 < 0 := by norm_num [b_spine5]
    have hpi : Real.pi < 3.1416 := p3g_PI_BOUNDS.2
    have h2pi : (2 : ℝ) * Real.pi < 6.2832 := by linarith
    have hkey : (0 : ℝ) < 5 * a_spine5 + b_spine5 * (2 * Real.pi) := by
      have h3 : b_spine5 * (6.2832 : ℝ) < b_spine5 * (2 * Real.pi) :=
        mul_lt_mul_of_neg_left h2pi hb5
      have h4 : (0 : ℝ) < 5 * a_spine5 + b_spine5 * (6.2832 : ℝ) := by
        norm_num [a_spine5, b_spine5]
      linarith
    have hsspos : (0 : ℝ) < ∑ i ∈ ss, cc_gg_v11 cc i := by
      have hcard5 : ((5 : ℕ) : ℝ) ≤ ss.card := by exact_mod_cast h5cd
      have hb2 : b_spine5 * (2 * Real.pi) ≤ b_spine5 * ∑ i ∈ ss, cc_azim_v11 cc i :=
        mul_le_mul_of_nonpos_left hc4 hb5.le
      have hc5 : (5 : ℝ) * a_spine5 ≤ ss.card * a_spine5 :=
        mul_le_mul_of_nonneg_right hcard5 (by norm_num [a_spine5])
      linarith
    linarith
  · -- the wanted bound
    rw [hsize]
    exact le_of_not_gt hcd

/-- OXLZLEZ2.hl:1322 (`UNPNFVW`, proving `UNPNFVW_concl` OXLZLEZ1.hl:145) —
the closing row of WAVES §W2.  Split on the 4cell count `sz`: if `sz = 3`
the three cyclic residues of the MTMLSRF witness exhaust the 4cell set and a
further 4cell residue forces `card = 3` (all residues 4cell) or `card = 4`
(with `cc_bool_prep_v11` giving exactly one `qy` residue); if `sz = 4` the
two-element `qy` subset contributes at least `2·0.606·0.008` to the gg-sum
while the four 4cells, weighted by the spine bound against the azim sum
`2π`, stay above zero — contradicting `∑ gg < 0`. -/
theorem p3h_UNPNFVW (cc : CcV11) (hp : cc_bool_prep_v11 cc) (hb : cc_bool_model_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_size_v11 cc (cc_qy_v11 cc) ≤ 1 := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have h3nn : 3 ≤ cc_card_v11 cc := p3h_THREE_LE_CC_CARD cc hb hp hr hsum
  have h3size := p3h_CHQSQEY cc hb hp hr hsum
  have h4size := p3h_LXDEYBO cc hp hb hr hsum
  have hper4 : periodic (cc_4cell_v11 cc) (cc_card_v11 cc) := p3h_bm_periodic_4cell hb
  have hpqy : periodic (cc_qy_v11 cc) (cc_card_v11 cc) := p3h_pf_qy hb
  have hmod4 : ∀ x, cc_4cell_v11 cc (x % cc_card_v11 cc) = cc_4cell_v11 cc x :=
    fun x => (periodic_mod hper4 hnn0 x).symm
  have hmodqy : ∀ x, cc_qy_v11 cc (x % cc_card_v11 cc) = cc_qy_v11 cc x :=
    fun x => (periodic_mod hpqy hnn0 x).symm
  have hsize4 : cc_size_v11 cc (cc_4cell_v11 cc)
      = (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hsizeqy : cc_size_v11 cc (cc_qy_v11 cc)
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hcard_ind : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    have h : Finset.Icc 0 (cc_card_v11 cc - 1) = Finset.range (cc_card_v11 cc) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [h, Finset.card_range]
  obtain ⟨i, hi0, higi, hqui, h4p, h4m⟩ := p3h_MTMLSRF cc hp hb hr hsum
  have h4i : cc_4cell_v11 cc i := hqui.2.1
  -- the three cyclic residues of the witness
  have hthree : ¬((i - 1) % cc_card_v11 cc = i % cc_card_v11 cc ∨
      i % cc_card_v11 cc = (i + 1) % cc_card_v11 cc ∨
      (i + 1) % cc_card_v11 cc = (i - 1) % cc_card_v11 cc) :=
    p3g_THREE_MOD_CONSECUTIVES i (cc_card_v11 cc) hi0 h3nn
  have h4ia : cc_4cell_v11 cc ((i - 1) % cc_card_v11 cc) := by
    rw [hmod4 (i - 1)]; exact h4m
  have h4ib : cc_4cell_v11 cc (i % cc_card_v11 cc) := by
    rw [hmod4 i]; exact h4i
  have h4ic : cc_4cell_v11 cc ((i + 1) % cc_card_v11 cc) := by
    rw [hmod4 (i + 1)]; exact h4p
  by_cases hsz3 : cc_size_v11 cc (cc_4cell_v11 cc) = 3
  · -- the three residues exhaust the 4cell set
    have hbne : (i - 1) % cc_card_v11 cc ∉
        ({i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hthree (Or.inl h)
      · exact hthree (Or.inr (Or.inr h.symm))
    have hcne : i % cc_card_v11 cc ∉ ({(i + 1) % cc_card_v11 cc} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      intro h
      exact hthree (Or.inr (Or.inl h))
    have hcard3set : ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc,
        (i + 1) % cc_card_v11 cc} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem hbne, Finset.card_insert_of_notMem hcne,
        Finset.card_singleton]
    have hsub1 : ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc,
        (i + 1) % cc_card_v11 cc} : Finset ℕ) ⊆
        Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact ⟨MOD_IN_NUMSEG hnn0, h4ia⟩
      · exact ⟨MOD_IN_NUMSEG hnn0, h4ib⟩
      · exact ⟨MOD_IN_NUMSEG hnn0, h4ic⟩
    have hcell_eq : Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))
        = ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
          Finset ℕ) := by
      refine (Finset.eq_of_subset_of_card_le hsub1 ?_).symm
      rw [hcard3set, ← hsize4, hsz3]
    by_cases h4n2 : cc_4cell_v11 cc ((i + 2) % cc_card_v11 cc)
    · -- a fourth 4cell residue in the 3-set forces card = 3, hence no qy at all
      have hmem : (i + 2) % cc_card_v11 cc ∈
          ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
            Finset ℕ) := by
        rw [← hcell_eq]
        exact Finset.mem_filter.mpr ⟨MOD_IN_NUMSEG hnn0, h4n2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hnn3 : cc_card_v11 cc = 3 := by
        rcases hmem with heq | heq | heq
        · have hd : cc_card_v11 cc ∣ (i + 2) - (i - 1) :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
        · exfalso
          have hd : cc_card_v11 cc ∣ (i + 2) - i :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
        · exfalso
          have hd : cc_card_v11 cc ∣ (i + 2) - (i + 1) :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
      have hind_eq : Finset.Icc 0 (cc_card_v11 cc - 1)
          = Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
        refine (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_).symm
        rw [hcard_ind, ← hsize4, hsz3]
        omega
      have hqy_empty : (Finset.Icc 0 (cc_card_v11 cc - 1)).filter (cc_qy_v11 cc) = ∅ := by
        rw [hind_eq]
        ext x
        constructor
        · intro hx
          obtain ⟨hx1, hxq⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hx4⟩ := Finset.mem_filter.mp hx1
          exact (hxq hx4).elim
        · intro h
          exact absurd h (Finset.notMem_empty x)
      rw [hsizeqy, hqy_empty, Finset.card_empty]
      exact Nat.zero_le 1
    · -- cc_bool_prep_v11 propagates ¬4cell to (i+3), bounding card by 4
      have hqy2 : cc_qy_v11 cc (i + 2) := by
        rw [← hmodqy (i + 2)]
        exact h4n2
      have h4i3 : cc_4cell_v11 cc (i + 3) := by
        have hn : ¬ cc_qy_v11 cc (i + 3) := hp (i + 2) hqy2
        by_contra hcon
        exact hn hcon
      have h4n3 : cc_4cell_v11 cc ((i + 3) % cc_card_v11 cc) := by
        rw [hmod4 (i + 3)]
        exact h4i3
      have hmem3 : (i + 3) % cc_card_v11 cc ∈
          ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
            Finset ℕ) := by
        rw [← hcell_eq]
        exact Finset.mem_filter.mpr ⟨MOD_IN_NUMSEG hnn0, h4n3⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem3
      have hnn4le : cc_card_v11 cc ≤ 4 := by
        rcases hmem3 with heq | heq | heq
        · have hd : cc_card_v11 cc ∣ (i + 3) - (i - 1) :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
        · have hd : cc_card_v11 cc ∣ (i + 3) - i :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
        · exfalso
          have hd : cc_card_v11 cc ∣ (i + 3) - (i + 1) :=
            (Nat.modEq_iff_dvd' (by omega)).mp heq.symm
          have h := Nat.le_of_dvd (by omega) hd
          omega
      have hie_not : (i + 2) % cc_card_v11 cc ∉
          ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
            Finset ℕ) := by
        rw [← hcell_eq]
        intro hm
        exact h4n2 (Finset.mem_filter.mp hm).2
      have hset_card : (insert ((i + 2) % cc_card_v11 cc)
          ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
            Finset ℕ)).card = 4 := by
        rw [Finset.card_insert_of_notMem hie_not, hcard3set]
      have hset_sub : (insert ((i + 2) % cc_card_v11 cc)
          ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
            Finset ℕ)) ⊆ Finset.Icc 0 (cc_card_v11 cc - 1) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | hx
        · exact MOD_IN_NUMSEG hnn0
        · rcases hx with rfl | rfl | rfl
          · exact MOD_IN_NUMSEG hnn0
          · exact MOD_IN_NUMSEG hnn0
          · exact MOD_IN_NUMSEG hnn0
      have hind_eq2 : Finset.Icc 0 (cc_card_v11 cc - 1)
          = insert ((i + 2) % cc_card_v11 cc)
            ({(i - 1) % cc_card_v11 cc, i % cc_card_v11 cc, (i + 1) % cc_card_v11 cc} :
              Finset ℕ) := by
        refine (Finset.eq_of_subset_of_card_le hset_sub ?_).symm
        rw [hcard_ind, hset_card]
        omega
      have hqy_eq : (Finset.Icc 0 (cc_card_v11 cc - 1)).filter (cc_qy_v11 cc)
          = ({(i + 2) % cc_card_v11 cc} : Finset ℕ) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hxind, hxqy⟩
          rw [hind_eq2] at hxind
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxind
          rcases hxind with rfl | hxind
          · exact rfl
          · rcases hxind with rfl | rfl | rfl
            · exact (hxqy h4ia).elim
            · exact (hxqy h4ib).elim
            · exact (hxqy h4ic).elim
        · rintro rfl
          exact ⟨MOD_IN_NUMSEG hnn0, h4n2⟩
      rw [hsizeqy, hqy_eq, Finset.card_singleton]
  · -- sz = 4: the numeric contradiction
    push_neg at hsz3
    have hsz4 : cc_size_v11 cc (cc_4cell_v11 cc) = 4 := by omega
    by_contra hcon
    push_neg at hcon
    set qyset : Finset ℕ :=
      (Finset.Icc 0 (cc_card_v11 cc - 1)).filter (cc_qy_v11 cc) with hqyset_def
    set cells : Finset ℕ :=
      (Finset.Icc 0 (cc_card_v11 cc - 1)).filter (cc_4cell_v11 cc) with hcells_def
    have hcardqy : qyset.card = cc_size_v11 cc (cc_qy_v11 cc) := rfl
    have hcardcells : cells.card = cc_size_v11 cc (cc_4cell_v11 cc) := rfl
    obtain ⟨t, htsub, htcard⟩ :=
      Finset.exists_subset_card_eq (show 2 ≤ qyset.card by omega)
    obtain ⟨x, y, hxy, htx⟩ := Finset.card_eq_two.mp htcard
    subst htx
    have hxq : cc_qy_v11 cc x := (Finset.mem_filter.mp (htsub (by simp))).2
    have hyq : cc_qy_v11 cc y := (Finset.mem_filter.mp (htsub (by simp))).2
    -- the qy side of the gg-sum carries at least 2 · 0.606 · 0.008
    have hqy_lb : (0.009696 : ℝ) ≤ ∑ i ∈ qyset, cc_gg_v11 cc i := by
      have hsplit : ∑ i ∈ qyset \ {x, y}, cc_gg_v11 cc i + ∑ i ∈ {x, y}, cc_gg_v11 cc i
          = ∑ i ∈ qyset, cc_gg_v11 cc i := Finset.sum_sdiff htsub
      have hpos : (0 : ℝ) ≤ ∑ i ∈ qyset \ {x, y}, cc_gg_v11 cc i := by
        refine Finset.sum_nonneg fun a ha => ?_
        obtain ⟨ha1, -⟩ := Finset.mem_sdiff.mp ha
        exact p3g_QY_NN0 hb hr (Finset.mem_filter.mp ha1).2
      have hpair : ∑ i ∈ ({x, y} : Finset ℕ), cc_gg_v11 cc i
          = cc_gg_v11 cc x + cc_gg_v11 cc y := by
        rw [Finset.sum_insert (show x ∉ ({y} : Finset ℕ) from fun h => hxy (Finset.mem_singleton.mp h)),
          Finset.sum_singleton]
      have hgx := p3h_rm_qy_azim hr hxq
      have hgy := p3h_rm_qy_azim hr hyq
      have hax := p3h_rm_azim_lb hr x
      have hay := p3h_rm_azim_lb hr y
      have hcx : (0.004848 : ℝ) ≤ 0.008 * cc_azim_v11 cc x := by nlinarith
      have hcy : (0.004848 : ℝ) ≤ 0.008 * cc_azim_v11 cc y := by nlinarith
      linarith
    have hqy_azim_lb : (1.212 : ℝ) ≤ ∑ i ∈ qyset, cc_azim_v11 cc i := by
      have hsplit : ∑ i ∈ qyset \ {x, y}, cc_azim_v11 cc i
          + ∑ i ∈ {x, y}, cc_azim_v11 cc i = ∑ i ∈ qyset, cc_azim_v11 cc i :=
        Finset.sum_sdiff htsub
      have hpos : (0 : ℝ) ≤ ∑ i ∈ qyset \ {x, y}, cc_azim_v11 cc i := by
        refine Finset.sum_nonneg fun a ha => ?_
        obtain ⟨ha1, -⟩ := Finset.mem_sdiff.mp ha
        linarith [p3h_rm_azim_lb hr a]
      have hpair : ∑ i ∈ ({x, y} : Finset ℕ), cc_azim_v11 cc i
          = cc_azim_v11 cc x + cc_azim_v11 cc y := by
        rw [Finset.sum_insert (show x ∉ ({y} : Finset ℕ) from fun h => hxy (Finset.mem_singleton.mp h)),
          Finset.sum_singleton]
      linarith [hsplit, hpos, hpair, p3h_rm_azim_lb hr x, p3h_rm_azim_lb hr y]
    -- the 4cell side stays above the spine-weighted azim bound
    have hcellpoint : ∀ j ∈ cells, a_spine5 + b_spine5 * cc_azim_v11 cc j
        ≤ cc_gg_v11 cc j := by
      intro j hj
      exact p3h_rm_4cell_spine hr (Finset.mem_filter.mp hj).2
    have hcells_lb : (4 : ℝ) * a_spine5 + b_spine5 * ∑ i ∈ cells, cc_azim_v11 cc i
        ≤ ∑ i ∈ cells, cc_gg_v11 cc i := by
      have h1 : ∑ i ∈ cells, (a_spine5 + b_spine5 * cc_azim_v11 cc i)
          ≤ ∑ i ∈ cells, cc_gg_v11 cc i := Finset.sum_le_sum hcellpoint
      have h2 : ∑ i ∈ cells, (a_spine5 + b_spine5 * cc_azim_v11 cc i)
          = (4 : ℝ) * a_spine5 + b_spine5 * ∑ i ∈ cells, cc_azim_v11 cc i := by
        have h2' : ∑ i ∈ cells, (a_spine5 + b_spine5 * cc_azim_v11 cc i)
            = (cells.card : ℝ) * a_spine5 + b_spine5 * ∑ i ∈ cells, cc_azim_v11 cc i := by
          rw [Finset.sum_add_distrib, p3h_sum_const_real, Finset.mul_sum]
        rw [hsz4] at hcardcells
        have hcc : ((cells.card : ℕ) : ℝ) = (4 : ℝ) := by exact_mod_cast hcardcells
        rw [hcc] at h2'
        exact h2'
      linarith
    -- the azim sum splits over qyset ∪ cells
    have hunion : Finset.Icc 0 (cc_card_v11 cc - 1) = qyset ∪ cells := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hx
        by_cases h4 : cc_4cell_v11 cc x
        · exact Or.inr (Finset.mem_filter.mpr ⟨hx, h4⟩)
        · exact Or.inl (Finset.mem_filter.mpr ⟨hx, h4⟩)
      · rintro (hx | hx)
        · exact (Finset.mem_filter.mp hx).1
        · exact (Finset.mem_filter.mp hx).1
    have hdisj2 : Disjoint qyset cells := by
      rw [Finset.disjoint_left]
      intro a ha hc
      exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hc).2
    have hsumazim := p3h_rm_sum_azim hr
    have hpart : ∑ i ∈ qyset, cc_azim_v11 cc i + ∑ i ∈ cells, cc_azim_v11 cc i
        = 2 * Real.pi := by
      have h1 : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc i
          = ∑ i ∈ qyset, cc_azim_v11 cc i + ∑ i ∈ cells, cc_azim_v11 cc i := by
        rw [hunion, Finset.sum_union hdisj2]
      rw [← h1]
      exact hsumazim
    have hsumsplit : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i
        = ∑ i ∈ qyset, cc_gg_v11 cc i + ∑ i ∈ cells, cc_gg_v11 cc i := by
      rw [hunion, Finset.sum_union hdisj2]
    have hb5 : b_spine5 < 0 := by norm_num [b_spine5]
    have hpi : Real.pi < 3.1416 := p3g_PI_BOUNDS.2
    have hkey : (0 : ℝ) < 0.009696 + (4 * a_spine5
        + b_spine5 * ((2 : ℝ) * Real.pi - 1.212)) := by
      have h2 : (2 : ℝ) * Real.pi - 1.212 < 5.0712 := by linarith
      have h3 : b_spine5 * (5.0712 : ℝ) < b_spine5 * ((2 : ℝ) * Real.pi - 1.212) :=
        mul_lt_mul_of_neg_left h2 hb5
      have h4 : (0 : ℝ) < 0.009696 + (4 * a_spine5 + b_spine5 * (5.0712 : ℝ)) := by
        norm_num [a_spine5, b_spine5]
      linarith
    have hfinal : (0 : ℝ) < ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i := by
      have h1 := hcells_lb
      have h2 : ∑ i ∈ cells, cc_azim_v11 cc i
          = 2 * Real.pi - ∑ i ∈ qyset, cc_azim_v11 cc i := by linarith [hpart]
      have h3 : b_spine5 * ((2 : ℝ) * Real.pi - 1.212)
          ≤ b_spine5 * ∑ i ∈ cells, cc_azim_v11 cc i := by
        have hle : ∑ i ∈ cells, cc_azim_v11 cc i ≤ (2 : ℝ) * Real.pi - 1.212 := by
          linarith [h2, hqy_azim_lb]
        exact mul_le_mul_of_nonpos_left hle hb5.le
      have h4 : (0 : ℝ) ≤ ∑ i ∈ qyset, cc_gg_v11 cc i := by linarith [hqy_lb]
      have h5 := hkey
      linarith
    linarith

/-! ## OXLZLEZ2 W3: IPVICGW 支 (OXLZLEZ2.hl:1830-3315; GRHIDFA wave plan W3)

Port of the W3 wave (WAVES §W3, 10 rows): the `IPVICGW` ladder — `IPVICGW_C33`,
`UNIQUE_QY`, `UNIQUE_QY2`, `IPVICGW_C43_C44`, `EXISTS_QY_CARD5`,
`CARD5_1074_LE_QYI`, `CARD5_LT_1074_QYI`, `PRE_IPVICGW`,
`CC_CARD_LESS_THAN_5` and `IPVICGW`, all consuming the W1 kit (`p3g_*`) and the
W2 block (`p3h_*`).  Rows are inserted in dependency order (the HOL order
C33, UNIQUE_QY, UNIQUE_QY2, C43_C44, EXISTS_QY_CARD5, CARD5_1074_LE_QYI,
CARD5_LT_1074_QYI, PRE_IPVICGW, CC_CARD_LESS_THAN_5, IPVICGW is respected).
`CARD5_LT_1074_QYI` is a new row without a PA4 stub: its statement is frozen
verbatim from the HOL goal OXLZLEZ2.hl:2811-2825 (see DELIVERY.md for the
premise table).  All rows below are fully proved, with no unproved
placeholders.  The nine conclusion stubs above are not touched. -/

/-- `Finset.Icc 0 (n-1) = Finset.range n` for `n ≠ 0` (W2 inline step,
factored out; used by every `periodic_sum` consumer below). -/
private theorem p3i_Icc0_eq_range (n : ℕ) (hn : n ≠ 0) :
    Finset.Icc 0 (n - 1) = Finset.range n := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

/-- `cc_real_model_v11` conjunct 9. -/
private theorem p3i_rm_qu_neg_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h : cc_qu_v11 cc i) : (-cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := hr
  exact h9 i h

/-- `cc_real_model_v11` conjunct 10. -/
private theorem p3i_rm_qu_eta_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qu_v11 cc i) (h2 : ¬cc_small_eta_v11 cc i) : (cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := hr
  exact h10 i ⟨h1, h2⟩

/-- `cc_real_model_v11` conjunct 11. -/
private theorem p3i_rm_qu_eta_next_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qu_v11 cc i) (h2 : ¬cc_small_eta_v11 cc (i + 1)) :
    (cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := hr
  exact h11 i ⟨h1, h2⟩

/-- `cc_real_model_v11` conjunct 20. -/
private theorem p3i_rm_qx_hassmall_qy_next_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ) (h1 : cc_qx_v11 cc i) (h2 : cc_hassmall_v11 cc i) (h3 : cc_qy_v11 cc (i + 1)) :
    (cc_eps : ℝ) ≤ cc_gg_v11 cc i + cc_gg3a_v11 cc (i + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h20, -⟩ := hr
  exact h20 i ⟨h1, h2, h3⟩

/-- `cc_real_model_v11` conjunct 21. -/
private theorem p3i_rm_qx_next_hassmall_qy_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ) (h1 : cc_qx_v11 cc (i + 1)) (h2 : cc_hassmall_v11 cc (i + 1))
    (h3 : cc_qy_v11 cc i) : (cc_eps : ℝ) ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21, -⟩ := hr
  exact h21 i ⟨h1, h2, h3⟩

/-- `cc_real_model_v11` conjunct 22. -/
private theorem p3i_rm_qx_small_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qx_v11 cc i) (h2 : cc_small_v11 cc i) (h3 : ¬cc_small_v11 cc (i + 1)) :
    (cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -⟩ := hr
  exact h22 i ⟨h1, h2, h3⟩

/-- `cc_real_model_v11` conjunct 23. -/
private theorem p3i_rm_qx_small_next_eps {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qx_v11 cc i) (h2 : cc_small_v11 cc (i + 1)) (h3 : ¬cc_small_v11 cc i) :
    (cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, -⟩ := hr
  exact h23 i ⟨h1, h2, h3⟩

/-- `cc_real_model_v11` conjunct 30. -/
private theorem p3i_rm_qy_eta_prev_spine {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qy_v11 cc i) (h2 : cc_small_eta_v11 cc i) (h3 : ¬cc_small_eta_v11 cc (i + 1))
    (h4 : cc_azim_v11 cc i < 1.074) :
    a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, h30, -⟩ := hr
  exact h30 i ⟨h1, h2, h3, h4⟩

/-- `cc_real_model_v11` conjunct 31. -/
private theorem p3i_rm_qy_eta_next_spine {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qy_v11 cc i) (h2 : ¬cc_small_eta_v11 cc i) (h3 : cc_small_eta_v11 cc (i + 1))
    (h4 : cc_azim_v11 cc i < 1.074) :
    a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, h31, -⟩ := hr
  exact h31 i ⟨h1, h2, h3, h4⟩

/-- `cc_real_model_v11` conjunct 32. -/
private theorem p3i_rm_qy_eta_both_spine {cc : CcV11} (hr : cc_real_model_v11 cc) (i : ℕ)
    (h1 : cc_qy_v11 cc i) (h2 : cc_small_eta_v11 cc i) (h3 : cc_small_eta_v11 cc (i + 1)) :
    a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, h32, -⟩ := hr
  exact h32 i ⟨h1, h2, h3⟩

/-- Every index carries `gg ≥ -cc_eps`: rows 9/18 of `cc_real_model_v11`
plus `QY_NN`, split by `QU_OR_QXY` (HOL subgoal of CARD5_LT_1074_QYI). -/
private theorem p3i_gg_ge_neg_eps {cc : CcV11} (hb : cc_bool_model_v11 cc)
    (hr : cc_real_model_v11 cc) (i : ℕ) : (-cc_eps : ℝ) ≤ cc_gg_v11 cc i := by
  rcases p3g_QU_OR_QXY cc i with h | h | h
  · exact p3i_rm_qu_neg_eps hr i h
  · exact le_trans (by norm_num [cc_eps]) (p3h_rm_qx_nn hr h)
  · exact le_trans (by norm_num [cc_eps]) (p3g_QY_NN00 cc hb hr i h)

/-- The index circle `0..card-1` splits into the `qy` and the `4cell` indices
(the HOL `SET_RULE`/`CARD_UNION` steps of EXISTS_QY_CARD5 and
CC_CARD_LESS_THAN_5). -/
private theorem p3i_split_qy_4cell (cc : CcV11) (hb : cc_bool_model_v11 cc) :
    (Finset.Icc 0 (cc_card_v11 cc - 1)).card
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card
        + (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hcardIcc : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    rw [p3i_Icc0_eq_range _ hnn0, Finset.card_range]
  have hunion : Finset.Icc 0 (cc_card_v11 cc - 1)
      = Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))
        ∪ Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hx
      by_cases h4 : cc_4cell_v11 cc x
      · exact Or.inr ⟨hx, h4⟩
      · exact Or.inl ⟨hx, h4⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
  have hdisj : Disjoint (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)))
      (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))) := by
    rw [Finset.disjoint_left]
    intro a ha hc'
    exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hc').2
  have h1 : (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card
      + (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))
          ∪ Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card :=
    (Finset.card_union_of_disjoint hdisj).symm
  rw [h1, ← hunion, hcardIcc]

/-- OXLZLEZ2.hl:1830 (`IPVICGW_C33`). -/
theorem p3i_IPVICGW_C33 (cc : CcV11)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ))
    (hc : cc_card_v11 cc = 3) (i : ℕ) : cc_small_v11 cc i := by
  obtain ⟨hb, hp, hr, hsum⟩ := h
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hbk := hb
  obtain ⟨-, -, -, -, hpsmall, -, hp4, -⟩ := hbk
  rw [hc] at hpsmall
  have hn3 : (3 : ℕ) ≠ 0 := by omega
  have h3sz := p3h_CHQSQEY cc hb hp hr hsum
  have hsize4 : cc_size_v11 cc (cc_4cell_v11 cc)
      = (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hcardIcc : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    rw [p3i_Icc0_eq_range _ hnn0, Finset.card_range]
  have hfil3 : (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card
      = 3 := by
    have hle : (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card
        ≤ (Finset.Icc 0 (cc_card_v11 cc - 1)).card :=
      Finset.card_le_card
        (Finset.filter_subset (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)))
    rw [hcardIcc] at hle
    rw [← hsize4]
    omega
  have hIcc4 : Finset.Icc 0 (cc_card_v11 cc - 1)
      = Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
    have hsub : Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))
        ⊆ Finset.Icc 0 (cc_card_v11 cc - 1) :=
      Finset.filter_subset (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcardIcc, ← hsize4]
    omega
  have h4all : ∀ j ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_4cell_v11 cc j := by
    intro j hj
    have hj2 : j ∈ Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1)) := by
      rw [← hIcc4]
      exact hj
    exact (Finset.mem_filter.mp hj2).2
  by_cases hqx : ∀ j ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_qx_v11 cc j
  · exfalso
    have hpos : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc j :=
      Finset.sum_nonneg fun j hj => p3g_QX_NN00 cc hb hr j (hqx j hj)
    linarith
  · push_neg at hqx
    obtain ⟨i', hi'c, hi'qx⟩ := hqx
    have h4i' : cc_4cell_v11 cc i' := h4all i' hi'c
    have hqui' : cc_qu_v11 cc i' := by
      by_cases hq : cc_qu_v11 cc i'
      · exact hq
      · exact absurd (show cc_qx_v11 cc i' from ⟨h4i', hq⟩) hi'qx
    have hs1 : cc_small_v11 cc i' := hqui'.1.1
    have hs2 : cc_small_v11 cc (i' + 1) := hqui'.1.2
    by_cases hs3 : cc_small_v11 cc (i' + 2)
    · -- residues of i', i'+1, i'+2 cover ℤ/3, so small propagates everywhere
      have hd1 : i' % 3 ≠ (i' + 1) % 3 :=
        MOD_INJ1_ALT hn3 (show (1 : ℕ) < 3 by omega) (show (1 : ℕ) ≠ 0 by omega) i'
      have hd2 : i' % 3 ≠ (i' + 2) % 3 :=
        MOD_INJ1_ALT hn3 (show (2 : ℕ) < 3 by omega) (show (2 : ℕ) ≠ 0 by omega) i'
      have hd3 : (i' + 1) % 3 ≠ (i' + 2) % 3 :=
        MOD_INJ1_ALT hn3 (show (1 : ℕ) < 3 by omega) (show (1 : ℕ) ≠ 0 by omega) (i' + 1)
      rw [periodic_mod hpsmall hn3 i]
      rcases (show i % 3 = i' % 3 ∨ i % 3 = (i' + 1) % 3 ∨ i % 3 = (i' + 2) % 3 from by omega) with
        r | r | r
      · rw [r, ← periodic_mod hpsmall hn3 i']
        exact hs1
      · rw [r, ← periodic_mod hpsmall hn3 (i' + 1)]
        exact hs2
      · rw [r, ← periodic_mod hpsmall hn3 (i' + 2)]
        exact hs3
    · -- everything is 4cell, (i'+1) and (i'+2) are qx, and the gg-sum over one
      -- period is a sum of three nonneg terms
      have h4allx : ∀ x, cc_4cell_v11 cc x := by
        intro x
        rw [periodic_mod hp4 hnn0 x]
        exact h4all _ (MOD_IN_NUMSEG hnn0)
      have hnq1 : ¬ cc_qu_v11 cc (i' + 1) := fun hq => hs3 hq.1.2
      have hnq2 : ¬ cc_qu_v11 cc (i' + 2) := fun hq => hs3 hq.1.1
      have hqx1 : cc_qx_v11 cc (i' + 1) := ⟨h4allx (i' + 1), hnq1⟩
      have hqx2 : cc_qx_v11 cc (i' + 2) := ⟨h4allx (i' + 2), hnq2⟩
      have hg1 : (cc_eps : ℝ) ≤ cc_gg_v11 cc (i' + 1) :=
        p3i_rm_qx_small_eps hr (i' + 1) hqx1 hs2 hs3
      have hg2 : (0 : ℝ) ≤ cc_gg_v11 cc (i' + 2) := p3h_rm_qx_nn hr hqx2
      have hg0 : (-cc_eps : ℝ) ≤ cc_gg_v11 cc i' := p3i_rm_qu_neg_eps hr i' hqui'
      have hpgg : periodic (cc_gg_v11 cc) (cc_card_v11 cc) := p3h_rm_periodic_gg hr
      have htop : cc_card_v11 cc - 1 + i' = i' + 2 := by omega
      have h1 := periodic_sum hpgg hnn0 i'
      rw [htop] at h1
      rw [p3i_Icc0_eq_range _ hnn0, ← h1, p3g_SUM_NUMSEG3] at hsum
      linarith

/-- OXLZLEZ2.hl:2009 (`UNIQUE_QY`). -/
theorem p3i_UNIQUE_QY (cc : CcV11) (_hb : cc_bool_model_v11 cc) (hp : cc_bool_prep_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ j, cc_qy_v11 cc j ∧ j ∈ (Finset.Icc 0 (cc_card_v11 cc - 1) : Set ℕ) →
      ∀ k, k ≠ j ∧ k ∈ (Finset.Icc 0 (cc_card_v11 cc - 1) : Set ℕ) →
        ¬cc_qy_v11 cc k := by
  intro j hj k hk hqk
  obtain ⟨hjy, hjm⟩ := hj
  obtain ⟨hkj, hkm⟩ := hk
  have hjm' : j ∈ Finset.Icc 0 (cc_card_v11 cc - 1) := Finset.mem_coe.mp hjm
  have hkm' : k ∈ Finset.Icc 0 (cc_card_v11 cc - 1) := Finset.mem_coe.mp hkm
  have hcard2 : (insert j ({k} : Finset ℕ)).card = 2 := by
    rw [Finset.card_insert_of_notMem
      (show j ∉ ({k} : Finset ℕ) from fun h => hkj (Finset.mem_singleton.mp h).symm),
      Finset.card_singleton]
  have hle : (insert j ({k} : Finset ℕ)).card
      ≤ (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hjm', hjy⟩
    · exact Finset.mem_filter.mpr ⟨hkm', hqk⟩
  have hsize : cc_size_v11 cc (cc_qy_v11 cc)
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have h1 := p3h_UNPNFVW cc hp _hb hr hsum
  omega

/-- OXLZLEZ2.hl:2052 (`UNIQUE_QY2`). -/
theorem p3i_UNIQUE_QY2 (cc : CcV11) (_hb : cc_bool_model_v11 cc) (hp : cc_bool_prep_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    ∀ j, cc_qy_v11 cc j ∧ j ∈ (Finset.Icc 0 (cc_card_v11 cc - 1) : Set ℕ) →
      ∀ k, cc_qy_v11 cc k ∧ k ∈ (Finset.Icc 0 (cc_card_v11 cc - 1) : Set ℕ) →
        k = j := by
  intro j hj k hk
  by_cases hne : k = j
  · exact hne
  · exact absurd hk.1 (p3i_UNIQUE_QY cc _hb hp hr hsum j hj k ⟨hne, hk.2⟩)

/-- `UNIQUE_QY2` in residue form: two `qy` indices agree modulo
`cc_card_v11 cc` (HOL `MOD_INJ11` assembly of UNIQUE_QY2). -/
private theorem p3i_qy_unique_mod {cc : CcV11} (hb : cc_bool_model_v11 cc)
    (hp : cc_bool_prep_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ))
    (w : ℕ) (hw : cc_qy_v11 cc w) (x : ℕ) (hx : cc_qy_v11 cc x) :
    x % cc_card_v11 cc = w % cc_card_v11 cc := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hpqy : periodic (cc_qy_v11 cc) (cc_card_v11 cc) := p3h_pf_qy hb
  exact p3i_UNIQUE_QY2 cc hb hp hr hsum (w % cc_card_v11 cc)
    ⟨by rw [← periodic_mod hpqy hnn0 w]; exact hw, Finset.mem_coe.mpr (MOD_IN_NUMSEG hnn0)⟩
    (x % cc_card_v11 cc)
    ⟨by rw [← periodic_mod hpqy hnn0 x]; exact hx, Finset.mem_coe.mpr (MOD_IN_NUMSEG hnn0)⟩

/-- OXLZLEZ2.hl:2068 (`IPVICGW_C43_C44`).  With `cc_card_v11 cc = 4` and a
witness `i` that is not small, the residues `i, i+1, i+2, i+3` carry at most
one `qy` (UNIQUE_QY2 + `MOD_INJ1`), and on each configuration of the
`qu`/`qx`/`qy` types the four gg-values combine with rows 9/12/13/18/22/23 and
the QY/QX nonnegativity to `0 ≤ ∑ gg` — contradicting `∑ gg < 0`. -/
theorem p3i_IPVICGW_C43_C44 (cc : CcV11)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ))
    (hc : cc_card_v11 cc = 4) (i : ℕ) : cc_small_v11 cc i := by
  obtain ⟨hb, hp, hr, hsum⟩ := h
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hbk := hb
  obtain ⟨-, -, -, -, hpsmall, -, -, -⟩ := hbk
  have hpqy : periodic (cc_qy_v11 cc) (cc_card_v11 cc) := p3h_pf_qy hb
  have hpgg : periodic (cc_gg_v11 cc) (cc_card_v11 cc) := p3h_rm_periodic_gg hr
  by_contra hns
  have hs4eq : cc_small_v11 cc (i + 3 + 1) = cc_small_v11 cc i := by
    have h := periodic_nk hpsmall (Nat.pos_of_ne_zero hnn0) i 1
    rw [Nat.one_mul, hc] at h
    exact h
  have hnqu : ¬ cc_qu_v11 cc i := fun hq => hns hq.1.1
  have hnqu3 : ¬ cc_qu_v11 cc (i + 3) := by
    intro hq
    have hh : cc_hassmall_v11 cc (i + 3) := hq.1
    have h34 : cc_small_v11 cc (i + 3 + 1) := hh.2
    rw [hs4eq] at h34
    exact hns h34
  have hsum4 : ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc x
      = cc_gg_v11 cc i + cc_gg_v11 cc (i + 1) + cc_gg_v11 cc (i + 2)
        + cc_gg_v11 cc (i + 3) := by
    have htop : cc_card_v11 cc - 1 + i = i + 3 := by omega
    have h1 := periodic_sum hpgg hnn0 i
    rw [htop] at h1
    rw [p3i_Icc0_eq_range _ hnn0, ← h1, p3g_SUM_NUMSEG4]
  -- rows 22/23 specialised at the witness and at i+3 (via small (i+4) = small i)
  have hR23 : cc_qx_v11 cc i → cc_small_v11 cc (i + 1) →
      (cc_eps : ℝ) ≤ cc_gg_v11 cc i :=
    fun hqx hs => p3i_rm_qx_small_next_eps hr i hqx hs hns
  have hR22 : cc_qx_v11 cc (i + 3) → cc_small_v11 cc (i + 3) →
      (cc_eps : ℝ) ≤ cc_gg_v11 cc (i + 3) :=
    fun hqx hs => p3i_rm_qx_small_eps hr (i + 3) hqx hs (by intro h34; rw [hs4eq] at h34; exact hns h34)
  -- the two adjacent-pair arguments (rows 13+26+27 and 12+26+28)
  have hpairAB : ∀ x, cc_qy_v11 cc x → cc_qu_v11 cc (x + 1) →
      (0 : ℝ) ≤ cc_gg_v11 cc x + cc_gg_v11 cc (x + 1) := by
    intro x hqy hqu
    have h1 := p3h_rm_qu_next_qy hr hqu hqy
    have h2 := p3h_rm_qy_le hr hqy
    have h3 := p3h_rm_qy_gg3a hr hqy
    linarith
  have hpairCD : ∀ x, cc_qu_v11 cc x → cc_qy_v11 cc (x + 1) →
      (0 : ℝ) ≤ cc_gg_v11 cc x + cc_gg_v11 cc (x + 1) := by
    intro x hqu hqy
    have h1 := p3h_rm_qu_qy_next hr hqu hqy
    have h2 := p3h_rm_qy_le hr hqy
    have h3 := p3h_rm_qy_gg3b hr hqy
    linarith
  have hqx0 : ∀ x, cc_qx_v11 cc x → (0 : ℝ) ≤ cc_gg_v11 cc x := fun x hx => p3h_rm_qx_nn hr hx
  have hqy0 : ∀ x, cc_qy_v11 cc x → (0 : ℝ) ≤ cc_gg_v11 cc x :=
    fun x hx => p3g_QY_NN00 cc hb hr x hx
  have hquE : ∀ x, cc_qu_v11 cc x → (-cc_eps : ℝ) ≤ cc_gg_v11 cc x :=
    fun x hx => p3i_rm_qu_neg_eps hr x hx
  have hi_case : cc_qx_v11 cc i ∨ cc_qy_v11 cc i := by
    rcases p3g_QU_OR_QXY cc i with h | h | h
    · exact absurd h hnqu
    · exact Or.inl h
    · exact Or.inr h
  have hi3_case : cc_qx_v11 cc (i + 3) ∨ cc_qy_v11 cc (i + 3) := by
    rcases p3g_QU_OR_QXY cc (i + 3) with h | h | h
    · exact absurd h hnqu3
    · exact Or.inl h
    · exact Or.inr h
  rcases hi_case with hqi | hqi <;> rcases hi3_case with hq3 | hq3
  · -- Case BB: qx i (hqi), qx (i+3) (hq3)
    by_cases hq1 : cc_qy_v11 cc (i + 1)
    · -- qy (i+1) is the unique qy residue, so (i+2) is 4cell
      have hnq2 : ¬ cc_qy_v11 cc (i + 2) := fun hq2 =>
        (MOD_INJ1_ALT hnn0 (show (1 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
          (show (1 : ℕ) ≠ 0 by omega) (i + 1))
          (p3i_qy_unique_mod hb hp hr hsum (i + 1) hq1 (i + 2) hq2).symm
      have h4c2 : cc_4cell_v11 cc (i + 2) := not_not.mp hnq2
      rcases (p3g_CC_4CELL_QUQX cc (i + 2)).mp h4c2 with hq2' | hq2'
      · -- qu (i+2): the pair (i+1, i+2) is nonnegative by rows 13/26/27
        have hp := hpairAB (i + 1) hq1 hq2'
        linarith [hsum4, hsum, hp, hqy0 (i + 1) hq1, hqx0 i hqi, hqx0 (i + 3) hq3]
      · linarith [hsum4, hsum, hqy0 (i + 1) hq1, hqx0 (i + 2) hq2', hqx0 i hqi,
          hqx0 (i + 3) hq3]
    · by_cases hq2 : cc_qy_v11 cc (i + 2)
      · -- qy (i+2) with ¬qy (i+1): the pair (i+1, i+2) is nonnegative by rows 12/26/28
        have h4c1 : cc_4cell_v11 cc (i + 1) := not_not.mp hq1
        rcases (p3g_CC_4CELL_QUQX cc (i + 1)).mp h4c1 with hq1' | hq1'
        · have hp := hpairCD (i + 1) hq1' hq2
          linarith [hsum4, hsum, hp, hqy0 (i + 2) hq2, hqx0 i hqi, hqx0 (i + 3) hq3]
        · linarith [hsum4, hsum, hqx0 (i + 1) hq1', hqy0 (i + 2) hq2, hqx0 i hqi,
            hqx0 (i + 3) hq3]
      · -- no qy among (i+1), (i+2): four qu/qx configurations
        have h4c1 : cc_4cell_v11 cc (i + 1) := not_not.mp hq1
        have h4c2 : cc_4cell_v11 cc (i + 2) := not_not.mp hq2
        rcases (p3g_CC_4CELL_QUQX cc (i + 1)).mp h4c1 with hq1' | hq1' <;>
          rcases (p3g_CC_4CELL_QUQX cc (i + 2)).mp h4c2 with hq2' | hq2'
        · -- qu (i+1), qu (i+2): rows 23 and 22 give cc_eps at i and i+3
          have hs1 : cc_small_v11 cc (i + 1) := hq1'.1.1
          have hh2 : cc_hassmall_v11 cc (i + 2) := hq2'.1
          have hs3 : cc_small_v11 cc (i + 3) := hh2.2
          have hgi := hR23 hqi hs1
          have hg3 := hR22 hq3 hs3
          linarith [hsum4, hsum, hgi, hg3, hquE (i + 1) hq1', hquE (i + 2) hq2']
        · have hs1 : cc_small_v11 cc (i + 1) := hq1'.1.1
          have hgi := hR23 hqi hs1
          linarith [hsum4, hsum, hgi, hquE (i + 1) hq1', hqx0 (i + 2) hq2',
            hqx0 (i + 3) hq3]
        · have hh2 : cc_hassmall_v11 cc (i + 2) := hq2'.1
          have hs3 : cc_small_v11 cc (i + 3) := hh2.2
          have hg3 := hR22 hq3 hs3
          linarith [hsum4, hsum, hg3, hquE (i + 2) hq2', hqx0 (i + 1) hq1', hqx0 i hqi]
        · linarith [hsum4, hsum, hqx0 (i + 1) hq1', hqx0 (i + 2) hq2', hqx0 i hqi,
            hqx0 (i + 3) hq3]
  · -- Case AC: qx i (hqi), qy (i+3) (hq3): qy (i+3) is the unique qy residue
    have hnq1 : ¬ cc_qy_v11 cc (i + 1) := fun hq1 =>
      (MOD_INJ1_ALT hnn0 (show (2 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (2 : ℕ) ≠ 0 by omega) (i + 1))
        (p3i_qy_unique_mod hb hp hr hsum (i + 3) hq3 (i + 1) hq1)
    have hnq2 : ¬ cc_qy_v11 cc (i + 2) := fun hq2 =>
      (MOD_INJ1_ALT hnn0 (show (1 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (1 : ℕ) ≠ 0 by omega) (i + 2))
        (p3i_qy_unique_mod hb hp hr hsum (i + 3) hq3 (i + 2) hq2)
    have h4c1 : cc_4cell_v11 cc (i + 1) := not_not.mp hnq1
    have h4c2 : cc_4cell_v11 cc (i + 2) := not_not.mp hnq2
    rcases (p3g_CC_4CELL_QUQX cc (i + 1)).mp h4c1 with hq1' | hq1' <;>
      rcases (p3g_CC_4CELL_QUQX cc (i + 2)).mp h4c2 with hq2' | hq2'
    · -- qu (i+1), qu (i+2): row 23 at i and the pair (i+2, i+3) by rows 12/26/28
      have hs1 : cc_small_v11 cc (i + 1) := hq1'.1.1
      have hgi := hR23 hqi hs1
      have hp := hpairCD (i + 2) hq2' hq3
      linarith [hsum4, hsum, hgi, hquE (i + 1) hq1', hp]
    · have hs1 : cc_small_v11 cc (i + 1) := hq1'.1.1
      have hgi := hR23 hqi hs1
      linarith [hsum4, hsum, hgi, hquE (i + 1) hq1', hqx0 (i + 2) hq2', hqy0 (i + 3) hq3]
    · have hp := hpairCD (i + 2) hq2' hq3
      linarith [hsum4, hsum, hp, hqx0 (i + 1) hq1', hqx0 i hqi]
    · linarith [hsum4, hsum, hqx0 (i + 1) hq1', hqx0 (i + 2) hq2', hqx0 i hqi,
        hqy0 (i + 3) hq3]

  · -- Case AB: qy i (hqi), qx (i+3) (hq3): qy i is the unique qy residue
    have hnq1 : ¬ cc_qy_v11 cc (i + 1) := fun hq1 =>
      (MOD_INJ1_ALT hnn0 (show (1 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (1 : ℕ) ≠ 0 by omega) i)
        (p3i_qy_unique_mod hb hp hr hsum i hqi (i + 1) hq1).symm
    have hnq2 : ¬ cc_qy_v11 cc (i + 2) := fun hq2 =>
      (MOD_INJ1_ALT hnn0 (show (2 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (2 : ℕ) ≠ 0 by omega) i)
        (p3i_qy_unique_mod hb hp hr hsum i hqi (i + 2) hq2).symm
    have h4c1 : cc_4cell_v11 cc (i + 1) := not_not.mp hnq1
    have h4c2 : cc_4cell_v11 cc (i + 2) := not_not.mp hnq2
    rcases (p3g_CC_4CELL_QUQX cc (i + 1)).mp h4c1 with hq1' | hq1' <;>
      rcases (p3g_CC_4CELL_QUQX cc (i + 2)).mp h4c2 with hq2' | hq2'
    · -- qu (i+1), qu (i+2)
      have hs1 : cc_small_v11 cc (i + 1) := hq1'.1.1
      have hh2 : cc_hassmall_v11 cc (i + 2) := hq2'.1
      have hs3 : cc_small_v11 cc (i + 3) := hh2.2
      have hp := hpairAB i hqi hq1'
      have hg3 := hR22 hq3 hs3
      linarith [hsum4, hsum, hp, hquE (i + 2) hq2', hg3]
    · -- qu (i+1), qx (i+2)
      have hp := hpairAB i hqi hq1'
      linarith [hsum4, hsum, hp, hqx0 (i + 2) hq2', hqx0 (i + 3) hq3]
    · -- qx (i+1), qu (i+2)
      have hh2 : cc_hassmall_v11 cc (i + 2) := hq2'.1
      have hs3 : cc_small_v11 cc (i + 3) := hh2.2
      have hg3 := hR22 hq3 hs3
      linarith [hsum4, hsum, hqy0 i hqi, hqx0 (i + 1) hq1', hquE (i + 2) hq2', hg3]
    · linarith [hsum4, hsum, hqy0 i hqi, hqx0 (i + 1) hq1', hqx0 (i + 2) hq2',
        hqx0 (i + 3) hq3]
  · -- Case: qy i (hqi), qy (i+3) (hq3): two distinct qy residues contradict UNIQUE_QY2
    exact absurd ((p3i_qy_unique_mod hb hp hr hsum i hqi (i + 3) hq3).symm)
      (MOD_INJ1_ALT hnn0 (show (3 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (3 : ℕ) ≠ 0 by omega) i)
/-- OXLZLEZ2.hl:2464 (`EXISTS_QY_CARD5`). -/
theorem p3i_EXISTS_QY_CARD5 (cc : CcV11)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ))
    (hc : cc_card_v11 cc = 5) : ∃ i, i < 5 ∧ cc_qy_v11 cc i := by
  obtain ⟨hb, hp, hr, hsum⟩ := h
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hqy1 := p3h_UNPNFVW cc hp hb hr hsum
  have h4le := p3h_LXDEYBO cc hp hb hr hsum
  have hsizeqy : cc_size_v11 cc (cc_qy_v11 cc)
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hsize4 : cc_size_v11 cc (cc_4cell_v11 cc)
      = (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hcardIcc : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    rw [p3i_Icc0_eq_range _ hnn0, Finset.card_range]
  have hsplit := p3i_split_qy_4cell cc hb
  have hqycard : 1 ≤ (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := by
    rw [← hsizeqy]
    omega
  obtain ⟨x, hx⟩ := Finset.one_le_card.mp hqycard
  refine ⟨x, ?_, (Finset.mem_filter.mp hx).2⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
  omega

/-- OXLZLEZ2.hl:2527 (`CARD5_1074_LE_QYI`).  The 4cell part of one
card-period window around `i` is spine-bounded, the `qy` witness contributes
`0.008·azim i`, and the azim sums reassemble to `2π` — the numeric key is
`0.008·1.074 + 4·a_spine5 + b_spine5·(2π - 1.074) > 0` via `π < 3.1416`. -/
theorem p3i_CARD5_1074_LE_QYI (cc : CcV11) (i : ℕ)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k < (0 : ℝ))
    (h4c : ∀ j, cc_4cell_v11 cc j → a_spine5 + b_spine5 * cc_azim_v11 cc j ≤ cc_gg_v11 cc j)
    (hqy : ∀ j, cc_qy_v11 cc j → (0.008 : ℝ) * cc_azim_v11 cc j ≤ cc_gg_v11 cc j)
    (hqyi : cc_qy_v11 cc i) (hc : cc_card_v11 cc = 5)
    (hper : periodic (cc_gg_v11 cc) (cc_card_v11 cc))
    (hgb : ∀ j, (0.606 : ℝ) ≤ cc_azim_v11 cc j)
    (hsum : ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc k = (2 : ℝ) * Real.pi)
    (h1074 : (1.074 : ℝ) ≤ cc_azim_v11 cc i) :
    (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k := by
  obtain ⟨hb, hp, hr, hggsum⟩ := h
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have h5 : (5 : ℕ) ≠ 0 := by omega
  have huniq := p3i_qy_unique_mod hb hp hr hggsum i hqyi
  have hnotqy : ∀ k : ℕ, 0 < k → k < 5 → ¬ cc_qy_v11 cc (i + k) := by
    intro k hk0 hk5 hq
    have h1 := huniq (i + k) hq
    rw [hc] at h1
    exact (p3g_MOD_INJ11 5 k h5 (by omega) (by omega) i) h1.symm
  have h4w : ∀ k : ℕ, 0 < k → k < 5 → cc_4cell_v11 cc (i + k) := fun k hk0 hk5 =>
    not_not.mp (hnotqy k hk0 hk5)
  have hpergg5 : periodic (cc_gg_v11 cc) 5 := by rw [← hc]; exact hper
  have hpazim5 : periodic (cc_azim_v11 cc) 5 := by
    rw [← hc]; exact p3h_rm_periodic_azim hr
  have htop : (5 : ℕ) - 1 + i = i + 4 := by omega
  have hWgg : ∑ x ∈ Finset.Icc i (i + 4), cc_gg_v11 cc x
      = ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc x := by
    rw [← htop, periodic_sum hpergg5 h5 i, p3i_Icc0_eq_range _ hnn0, hc]
  have hWazim : ∑ x ∈ Finset.Icc i (i + 4), cc_azim_v11 cc x
      = ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc x := by
    rw [← htop, periodic_sum hpazim5 h5 i, p3i_Icc0_eq_range _ hnn0, hc]
  have hsplit : Finset.Icc i (i + 4) = insert i (Finset.Icc (i + 1) (i + 4)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · rintro (h | ⟨h1, h2⟩)
      · omega
      · omega
  have hmem : i ∉ Finset.Icc (i + 1) (i + 4) := by
    simp only [Finset.mem_Icc]
    omega
  have hWgg2 : ∑ x ∈ Finset.Icc i (i + 4), cc_gg_v11 cc x
      = cc_gg_v11 cc i + ∑ x ∈ Finset.Icc (i + 1) (i + 4), cc_gg_v11 cc x := by
    rw [hsplit, Finset.sum_insert hmem]
  have hWazim2 : ∑ x ∈ Finset.Icc i (i + 4), cc_azim_v11 cc x
      = cc_azim_v11 cc i + ∑ x ∈ Finset.Icc (i + 1) (i + 4), cc_azim_v11 cc x := by
    rw [hsplit, Finset.sum_insert hmem]
  have hSS4 : ∀ x ∈ Finset.Icc (i + 1) (i + 4), cc_4cell_v11 cc x := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    have hk0 : 0 < x - i := by omega
    have hk5 : x - i < 5 := by omega
    have h3 := h4w (x - i) hk0 hk5
    rw [show x = i + (x - i) from by omega]
    exact h3
  have hSSgg : ∑ x ∈ Finset.Icc (i + 1) (i + 4), cc_gg_v11 cc x
      ≥ ∑ x ∈ Finset.Icc (i + 1) (i + 4), (a_spine5 + b_spine5 * cc_azim_v11 cc x) :=
    Finset.sum_le_sum fun x hx => h4c x (hSS4 x hx)
  have hcardSS : (Finset.Icc (i + 1) (i + 4)).card = 4 := by
    have hSS : Finset.Icc (i + 1) (i + 4) = (Finset.range 4).image (fun k => i + 1 + k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨x - (i + 1), by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        omega
    rw [hSS, Finset.card_image_of_injOn fun k _ l _ hkl => by simpa using Nat.add_left_cancel hkl,
      Finset.card_range]
  have hSSexpand : ∑ x ∈ Finset.Icc (i + 1) (i + 4), (a_spine5 + b_spine5 * cc_azim_v11 cc x)
      = (4 : ℝ) * a_spine5 + b_spine5 * ∑ x ∈ Finset.Icc (i + 1) (i + 4), cc_azim_v11 cc x := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardSS, Finset.mul_sum]
    ring
  have hSSazim : ∑ x ∈ Finset.Icc (i + 1) (i + 4), cc_azim_v11 cc x
      = (2 : ℝ) * Real.pi - cc_azim_v11 cc i := by
    linarith [hWazim, hWazim2, hsum]
  rw [hSSazim] at hSSexpand
  have hgi : (0.008 : ℝ) * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := hqy i hqyi
  have hb5 : b_spine5 < 0 := by norm_num [b_spine5]
  have hpi : Real.pi < 3.1416 := p3g_PI_BOUNDS.2
  have hle : (2 : ℝ) * Real.pi - cc_azim_v11 cc i ≤ 5.2092 := by linarith
  have hkey : b_spine5 * 5.2092 ≤ b_spine5 * ((2 : ℝ) * Real.pi - cc_azim_v11 cc i) :=
    mul_le_mul_of_nonpos_left hle hb5.le
  have h1074le : (0.008 : ℝ) * 1.074 ≤ 0.008 * cc_azim_v11 cc i :=
    mul_le_mul_of_nonneg_left h1074 (by norm_num)
  have hfinal : (0 : ℝ) < (0.008 : ℝ) * 1.074 + (4 : ℝ) * a_spine5 + b_spine5 * 5.2092 := by
    norm_num [a_spine5, b_spine5]
  rw [← hWgg, hWgg2]
  linarith [hSSgg, hSSexpand, hkey, hgi, h1074le, hfinal]

/-- OXLZLEZ2.hl:2811 (`CARD5_LT_1074_QYI`; PA4 has no stub row — new row,
statement frozen verbatim from the HOL goal, see DELIVERY.md).  If some
`small_eta` flag holds at `i` or `i+1`, rows 30/31/32 give the spine bound at
`i` and all five window gg's are spine-bounded (`5·a_spine5 + b_spine5·2π > 0`);
otherwise rows 20/21/22/23 and the -cc_eps floor split the gg-sum into
`gg i - (gg3a i + gg3b i)` plus two nonnegative triples, and row 26 closes. -/
theorem p3i_CARD5_LT_1074_QYI (cc : CcV11) (i : ℕ)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k < (0 : ℝ))
    (hqyi : cc_qy_v11 cc i) (hc : cc_card_v11 cc = 5)
    (hlt : cc_azim_v11 cc i < (1.074 : ℝ)) :
    (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k := by
  obtain ⟨hb, hp, hr, hggsum⟩ := h
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have h5 : (5 : ℕ) ≠ 0 := by omega
  have hneg : ∀ x, (-cc_eps : ℝ) ≤ cc_gg_v11 cc x := fun x => p3i_gg_ge_neg_eps hb hr x
  have huniq := p3i_qy_unique_mod hb hp hr hggsum i hqyi
  have hnotqy : ∀ k : ℕ, 0 < k → k < 5 → ¬ cc_qy_v11 cc (i + k) := by
    intro k hk0 hk5 hq
    have h1 := huniq (i + k) hq
    rw [hc] at h1
    exact (p3g_MOD_INJ11 5 k h5 (by omega) (by omega) i) h1.symm
  by_cases heta : cc_small_eta_v11 cc i ∨ cc_small_eta_v11 cc (i + 1)
  · -- spine bound at i, then the five-window spine sum
    have hspine : a_spine5 + b_spine5 * cc_azim_v11 cc i ≤ cc_gg_v11 cc i := by
      by_cases he1 : cc_small_eta_v11 cc i
      · by_cases he2 : cc_small_eta_v11 cc (i + 1)
        · exact p3i_rm_qy_eta_both_spine hr i hqyi he1 he2
        · exact p3i_rm_qy_eta_prev_spine hr i hqyi he1 he2 hlt
      · rcases heta with h | h
        · exact absurd h he1
        · exact p3i_rm_qy_eta_next_spine hr i hqyi he1 h hlt
    have h4w : ∀ k : ℕ, 0 < k → k < 5 → cc_4cell_v11 cc (i + k) := fun k hk0 hk5 =>
      not_not.mp (hnotqy k hk0 hk5)
    have hpergg5 : periodic (cc_gg_v11 cc) 5 := by rw [← hc]; exact p3h_rm_periodic_gg hr
    have hpazim5 : periodic (cc_azim_v11 cc) 5 := by
      rw [← hc]; exact p3h_rm_periodic_azim hr
    have htop : (5 : ℕ) - 1 + i = i + 4 := by omega
    have hWgg : ∑ x ∈ Finset.Icc i (i + 4), cc_gg_v11 cc x
        = ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc x := by
      rw [← htop, periodic_sum hpergg5 h5 i, p3i_Icc0_eq_range _ hnn0, hc]
    have hWazim : ∑ x ∈ Finset.Icc i (i + 4), cc_azim_v11 cc x
        = ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_azim_v11 cc x := by
      rw [← htop, periodic_sum hpazim5 h5 i, p3i_Icc0_eq_range _ hnn0, hc]
    have hpt : ∀ x ∈ Finset.Icc i (i + 4),
        a_spine5 + b_spine5 * cc_azim_v11 cc x ≤ cc_gg_v11 cc x := by
      intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
      by_cases hxi : x = i
      · rw [hxi]
        exact hspine
      · have hk0 : 0 < x - i := by omega
        have hk5 : x - i < 5 := by omega
        have h3 := p3h_rm_4cell_spine hr (h4w (x - i) hk0 hk5)
        rw [show x = i + (x - i) from by omega]
        exact h3
    have hlb : ∑ x ∈ Finset.Icc i (i + 4), (a_spine5 + b_spine5 * cc_azim_v11 cc x)
        ≤ ∑ x ∈ Finset.Icc i (i + 4), cc_gg_v11 cc x := Finset.sum_le_sum hpt
    have hcardW : (Finset.Icc i (i + 4)).card = 5 := by
      have hW : Finset.Icc i (i + 4) = (Finset.range 5).image (fun k => i + k) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨x - i, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩
          omega
      rw [hW, Finset.card_image_of_injOn fun k _ l _ hkl => by simpa using Nat.add_left_cancel hkl,
        Finset.card_range]
    have hexpand : ∑ x ∈ Finset.Icc i (i + 4), (a_spine5 + b_spine5 * cc_azim_v11 cc x)
        = (5 : ℝ) * a_spine5 + b_spine5 * ∑ x ∈ Finset.Icc i (i + 4), cc_azim_v11 cc x := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardW, Finset.mul_sum]
      ring
    have hsumazim := p3h_rm_sum_azim hr
    rw [hWazim, hsumazim] at hexpand
    have hb5 : b_spine5 < 0 := by norm_num [b_spine5]
    have hpi : Real.pi < 3.1416 := p3g_PI_BOUNDS.2
    have hkey : (0 : ℝ) < (5 : ℝ) * a_spine5 + b_spine5 * ((2 : ℝ) * Real.pi) := by
      have h2 : (2 : ℝ) * Real.pi < 6.2832 := by linarith
      have h3 : b_spine5 * (6.2832 : ℝ) < b_spine5 * ((2 : ℝ) * Real.pi) :=
        mul_lt_mul_of_neg_left h2 hb5
      have h4 : (0 : ℝ) < (5 : ℝ) * a_spine5 + b_spine5 * 6.2832 := by
        norm_num [a_spine5, b_spine5]
      linarith
    linarith [hWgg, hlb, hexpand, hkey]
  · -- no small_eta flag at i or i+1: the combinatorial triple decomposition
    push_neg at heta
    obtain ⟨he1, he2⟩ := heta
    have hq1n : ¬ cc_qy_v11 cc (i + 1) := fun hq1 =>
      (p3g_MOD_INJ11 (cc_card_v11 cc) 1 hnn0
        (show (1 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (1 : ℕ) ≠ 0 by omega) i)
        (huniq (i + 1) hq1).symm
    have hq2n : ¬ cc_qy_v11 cc (i + 2) := fun hq2 =>
      (p3g_MOD_INJ11 (cc_card_v11 cc) 2 hnn0
        (show (2 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (2 : ℕ) ≠ 0 by omega) i)
        (huniq (i + 2) hq2).symm
    have hq3n : ¬ cc_qy_v11 cc (i + 3) := fun hq3 =>
      (p3g_MOD_INJ11 (cc_card_v11 cc) 3 hnn0
        (show (3 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (3 : ℕ) ≠ 0 by omega) i)
        (huniq (i + 3) hq3).symm
    have hq4n : ¬ cc_qy_v11 cc (i + 4) := fun hq4 =>
      (p3g_MOD_INJ11 (cc_card_v11 cc) 4 hnn0
        (show (4 : ℕ) < cc_card_v11 cc by rw [hc]; omega)
        (show (4 : ℕ) ≠ 0 by omega) i)
        (huniq (i + 4) hq4).symm
    have h4c1 : cc_4cell_v11 cc (i + 1) := not_not.mp hq1n
    have h4c2 : cc_4cell_v11 cc (i + 2) := not_not.mp hq2n
    have h4c3 : cc_4cell_v11 cc (i + 3) := not_not.mp hq3n
    have h4c4 : cc_4cell_v11 cc (i + 4) := not_not.mp hq4n
    have hA : (0 : ℝ) ≤ cc_gg3b_v11 cc i + cc_gg_v11 cc (i + 1) + cc_gg_v11 cc (i + 2) := by
      have hg3b : (0 : ℝ) ≤ cc_gg3b_v11 cc i := p3h_rm_qy_gg3b hr hqyi
      by_cases hs2 : cc_small_v11 cc (i + 2)
      · rcases (p3g_CC_4CELL_QUQX cc (i + 1)).mp h4c1 with hqu1 | hqx1
        · have h10 := p3i_rm_qu_eta_eps hr (i + 1) hqu1 he2
          linarith [h10, hneg (i + 2), hg3b]
        · by_cases hs1 : cc_small_v11 cc (i + 1)
          · have h21 := p3i_rm_qx_next_hassmall_qy_eps hr i hqx1 ⟨hs1, hs2⟩ hqyi
            linarith [h21, hneg (i + 2), hg3b]
          · have h23 := p3i_rm_qx_small_next_eps hr (i + 1) hqx1 hs2 hs1
            linarith [h23, hneg (i + 2), hg3b]
      · have hnqu1 : ¬ cc_qu_v11 cc (i + 1) := fun hq => hs2 hq.1.2
        have hnqu2 : ¬ cc_qu_v11 cc (i + 2) := fun hq => hs2 hq.1.1
        have hqx1 : cc_qx_v11 cc (i + 1) := ⟨h4c1, hnqu1⟩
        have hqx2 : cc_qx_v11 cc (i + 2) := ⟨h4c2, hnqu2⟩
        have hg1 := p3h_rm_qx_nn hr hqx1
        have hg2 := p3h_rm_qx_nn hr hqx2
        linarith [hg1, hg2, hg3b]
    have hB : (0 : ℝ) ≤ cc_gg3a_v11 cc i + cc_gg_v11 cc (i + 3) + cc_gg_v11 cc (i + 4) := by
      have hg3a : (0 : ℝ) ≤ cc_gg3a_v11 cc i := p3h_rm_qy_gg3a hr hqyi
      have hmod5 : (i + 5) % cc_card_v11 cc = i % cc_card_v11 cc := by
        rw [hc]; exact Nat.add_mod_right i 5
      have hbk2 := hb
      obtain ⟨-, -, -, -, -, hpeta, -⟩ := hbk2
      have heta5 : ¬ cc_small_eta_v11 cc (i + 5) := by
        rw [periodic_mod hpeta hnn0 (i + 5), hmod5, ← periodic_mod hpeta hnn0 i]
        exact he1
      have hpqy : periodic (cc_qy_v11 cc) (cc_card_v11 cc) := p3h_pf_qy hb
      have hp3a : periodic (cc_gg3a_v11 cc) (cc_card_v11 cc) := p3h_rm_periodic_gg3a hr
      by_cases hs4 : cc_small_v11 cc (i + 4)
      · rcases (p3g_CC_4CELL_QUQX cc (i + 4)).mp h4c4 with hqu4 | hqx4
        · have h11 := p3i_rm_qu_eta_next_eps hr (i + 4) hqu4 heta5
          linarith [h11, hneg (i + 3), hg3a]
        · by_cases hs5 : cc_small_v11 cc (i + 5)
          · have hqy5 : cc_qy_v11 cc (i + 5) := by
              rw [periodic_mod hpqy hnn0 (i + 5), hmod5, ← periodic_mod hpqy hnn0 i]
              exact hqyi
            have h20 := p3i_rm_qx_hassmall_qy_next_eps hr (i + 4) hqx4 ⟨hs4, hs5⟩ hqy5
            have hga5 : cc_gg3a_v11 cc (i + 5) = cc_gg3a_v11 cc i := by
              rw [periodic_mod hp3a hnn0 (i + 5), hmod5, ← periodic_mod hp3a hnn0 i]
            rw [hga5] at h20
            linarith [h20, hneg (i + 3), hg3a]
          · have h22 := p3i_rm_qx_small_eps hr (i + 4) hqx4 hs4 hs5
            linarith [h22, hneg (i + 3), hg3a]
      · have hnqu3 : ¬ cc_qu_v11 cc (i + 3) := fun hq => hs4 (hq.1).2
        have hnqu4 : ¬ cc_qu_v11 cc (i + 4) := fun hq => hs4 hq.1.1
        have hqx3 : cc_qx_v11 cc (i + 3) := ⟨h4c3, hnqu3⟩
        have hqx4 : cc_qx_v11 cc (i + 4) := ⟨h4c4, hnqu4⟩
        have hg3 := p3h_rm_qx_nn hr hqx3
        have hg4 := p3h_rm_qx_nn hr hqx4
        linarith [hg3, hg4, hg3a]
    have hgi0 : (0 : ℝ) ≤ cc_gg_v11 cc i := p3g_QY_NN00 cc hb hr i hqyi
    have hle26 : cc_gg3a_v11 cc i + cc_gg3b_v11 cc i ≤ cc_gg_v11 cc i := p3h_rm_qy_le hr hqyi
    have hpergg5 : periodic (cc_gg_v11 cc) 5 := by rw [← hc]; exact p3h_rm_periodic_gg hr
    have htop : (5 : ℕ) - 1 + i = i + 4 := by omega
    have hsplit : Finset.Icc i (i + 4) = insert i (Finset.Icc (i + 1) (i + 4)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        omega
      · rintro (h | ⟨h1, h2⟩)
        · omega
        · omega
    have hmem : i ∉ Finset.Icc (i + 1) (i + 4) := by
      simp only [Finset.mem_Icc]
      omega
    have hsum5 : ∑ x ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc x
        = cc_gg_v11 cc i + cc_gg_v11 cc (i + 1) + cc_gg_v11 cc (i + 2)
          + cc_gg_v11 cc (i + 3) + cc_gg_v11 cc (i + 4) := by
      have h1 := periodic_sum hpergg5 h5 i
      rw [htop] at h1
      rw [p3i_Icc0_eq_range _ hnn0, hc, ← h1, hsplit, Finset.sum_insert hmem, p3g_SUM_NUMSEG4]
      ring
    rw [hsum5]
    linarith [hA, hB, hgi0, hle26]

/-- OXLZLEZ2.hl:3229 (`PRE_IPVICGW`). -/
theorem p3i_PRE_IPVICGW (cc : CcV11)
    (h : cc_bool_model_v11 cc ∧ cc_bool_prep_v11 cc ∧ cc_real_model_v11 cc ∧
      ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k < (0 : ℝ))
    (hc : cc_card_v11 cc = 5) :
    (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc k := by
  obtain ⟨j, -, hjqy⟩ := p3i_EXISTS_QY_CARD5 cc h hc
  by_cases hlt : cc_azim_v11 cc j < (1.074 : ℝ)
  · exact p3i_CARD5_LT_1074_QYI cc j h hjqy hc hlt
  · exact p3i_CARD5_1074_LE_QYI cc j h (fun k hk => p3h_rm_4cell_spine h.2.2.1 hk)
      (fun k hk => p3h_rm_qy_azim h.2.2.1 hk) hjqy hc (p3h_rm_periodic_gg h.2.2.1)
      (fun k => p3h_rm_azim_lb h.2.2.1 k) (p3h_rm_sum_azim h.2.2.1) (le_of_not_gt hlt)

/-- OXLZLEZ2.hl:3264 (`CC_CARD_LESS_THAN_5`). -/
theorem p3i_CC_CARD_LESS_THAN_5 (cc : CcV11) (hb : cc_bool_model_v11 cc)
    (hp : cc_bool_prep_v11 cc) (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ)) :
    cc_card_v11 cc ≤ 5 := by
  have hnn0 : cc_card_v11 cc ≠ 0 := hb.1
  have hqy1 := p3h_UNPNFVW cc hp hb hr hsum
  have h4le := p3h_LXDEYBO cc hp hb hr hsum
  have hsizeqy : cc_size_v11 cc (cc_qy_v11 cc)
      = (Finset.filter (cc_qy_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hsize4 : cc_size_v11 cc (cc_4cell_v11 cc)
      = (Finset.filter (cc_4cell_v11 cc) (Finset.Icc 0 (cc_card_v11 cc - 1))).card := rfl
  have hcardIcc : (Finset.Icc 0 (cc_card_v11 cc - 1)).card = cc_card_v11 cc := by
    rw [p3i_Icc0_eq_range _ hnn0, Finset.card_range]
  have hsplit := p3i_split_qy_4cell cc hb
  omega

/-- OXLZLEZ2.hl:3308 (`IPVICGW`, proving `IPVICGW_concl` OXLZLEZ1.hl:548). -/
theorem p3i_IPVICGW (cc : CcV11) (hb : cc_bool_model_v11 cc) (hp : cc_bool_prep_v11 cc)
    (hr : cc_real_model_v11 cc)
    (hsum : ∑ i ∈ Finset.Icc 0 (cc_card_v11 cc - 1), cc_gg_v11 cc i < (0 : ℝ))
    (i : ℕ) : cc_small_v11 cc i := by
  by_cases hc3 : cc_card_v11 cc = 3
  · exact p3i_IPVICGW_C33 cc ⟨hb, hp, hr, hsum⟩ hc3 i
  by_cases hc4 : cc_card_v11 cc = 4
  · exact p3i_IPVICGW_C43_C44 cc ⟨hb, hp, hr, hsum⟩ hc4 i
  have h3 : 3 ≤ cc_card_v11 cc := p3h_THREE_LE_CC_CARD cc hb hp hr hsum
  have h5le : cc_card_v11 cc ≤ 5 := p3i_CC_CARD_LESS_THAN_5 cc hb hp hr hsum
  have hnn5 : cc_card_v11 cc = 5 := by omega
  have hcon := p3i_PRE_IPVICGW cc ⟨hb, hp, hr, hsum⟩ hnn5
  linarith

end Kepler.Text
