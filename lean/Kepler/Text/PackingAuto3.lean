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

/-- Flyspeck constant `a_spine5` (defined in Flyspeck_constants outside
OXLZLEZ1.hl; kept opaque here — together with `b_spine5` it only occurs
inside `cc_real_model_v11`, and every theorem below is conditional on it). -/
opaque a_spine5 : ℝ

/-- Flyspeck constant `b_spine5`. -/
opaque b_spine5 : ℝ

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

end Kepler.Text
