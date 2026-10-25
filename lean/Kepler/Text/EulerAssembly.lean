/-
Kepler.Text.EulerAssembly — Euler 泛型立体角工程 W4 波 (lane BE): assembly +
rescaling.  Builds the geometric half of the Euler solid-angle anchor and
assembles the two halves into the 6-premise anchor.

Provenance (HOL originals under `reference/flyspeck/text_formalization/`):
  * `ea4_eulerP`     : sphere.hl:394 `euler_p` (via `ylist`, sphere.hl:387).
  * translation      : merge_ineq.hl:899-916 —
                       `dist y1 y2 y3 + y1*(w2 dot w3) + ... = eulerA_x`.
  * rescale algebra  : euler_complement.hl `LEMMA_FOR_EULER_AFTER_RESCALE`
                       (euler_p scales by m*n*p under edge rescaling).
  * unit angle sum   : euler_main_theorem.hl:42-59 `EULER_ANGLE_SUM_rescal`
                       (norm w_i = 1 case), closing via W3
                       `ea3_derivative_wrt_a` (euler_multivariate.hl:351).
  * full triangle    : euler_main_theorem.hl:514 `EULER_TRIANGLE` via
                       euler_complement.hl:326 `EULER_FORMULA_RESCALE`
                       (unit box -> all shapes, W2 `ea2_dihv_rescale_unchanged`
                       + `ea2_sqrt_delta_rescale` + atn2 homogeneity).
  * assembly         : merge_ineq.hl:841 `sol_x_sol_euler_x` (six premises,
                       premise-for-premise) via W2 `ea2_simplex_exists` +
                       `ea2_dihV_dih_x`.
  * anchor           : `p21k_euler_anchor` (PackingAuto21:10973) verbatim
                       mirror `ea1_euler_anchor6` (W1); the W1 premise gap
                       `0 < x2 /\ 0 < x3` (merge:1060 vs merge:841) is closed
                       here by deriving both from `0 < x1`, `0 < upsX x1 x2 x6`
                       (`4*x1*x6 - (x2-x1-x6)^2 > 0` bounds
                       `x2 > (sqrt x1 - sqrt x6)^2 >= 0`).

Imports only the three signed Euler modules + canonical kits; no
PackingAuto21/25/22.  All proofs complete; no gap words anywhere.
-/

import Kepler.Text.SphereKit
import Kepler.Text.IneqClosureDefs
import Kepler.Text.EulerAtn2Kit
import Kepler.Text.EulerSimplexGeom
import Kepler.Text.EulerDerivCore
import Kepler.Geom.LuneVolume
import Mathlib

open Kepler.Geom

noncomputable section

namespace Kepler.Text

/-! ## §0 Atoms: distances, dots, collinearity permutations, ups bounds -/

private theorem ea4_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl

private theorem ea4_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = ((a : V3) : Fin 3 → ℝ) - ((b : V3) : Fin 3 → ℝ) := rfl

private theorem ea4_dist_sq (x y : V3) :
    dist x y ^ 2 = ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) := by
  have h : dist x y ^ 2 = ((y - x : V3)) ⬝ᵥ ((y - x : V3)) := by
    rw [dist_eq_norm, show (x : V3) - y = -((y : V3) - x) from by abel, norm_neg,
      norm_sq_eq_dot]
  rw [h]

private theorem ea4_dmix (f g : Fin 3 → ℝ) :
    (f - g) ⬝ᵥ (f - g) = f ⬝ᵥ f + g ⬝ᵥ g - 2 * (f ⬝ᵥ g) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm f g]
  ring

/-- The law of cosines at the dot level (Collect_geom `DIST_POW2_DOT`). -/
private theorem ea4_law_cos (a b c : V3) :
    dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2
      = 2 * (((b - a : V3) : Fin 3 → ℝ) ⬝ᵥ ((c - a : V3) : Fin 3 → ℝ)) := by
  rw [ea4_dist_sq a b, ea4_dist_sq a c, ea4_dist_sq b c]
  have hcb : ((c - b : V3) : Fin 3 → ℝ)
      = ((c - a : V3) : Fin 3 → ℝ) - ((b - a : V3) : Fin 3 → ℝ) := by
    rw [show (c : V3) - b = (c - a : V3) - (b - a : V3) from by abel, ea4_coe_sub]
  rw [hcb, ea4_dmix,
    dotProduct_comm (((c - a : V3) : Fin 3 → ℝ)) (((b - a : V3) : Fin 3 → ℝ))]
  ring

/-- `ups_x` is symmetric in its first two arguments (Collect_geom `UPS_X_SYM`). -/
private theorem ea4_upsX_sym (a b c : ℝ) : upsX a b c = upsX b a c := by
  simp only [upsX]; ring

/-- Three-point collinearity is invariant under swapping the last two points. -/
private theorem ea4_collinear3_right (a b c : V3) :
    Collinear3 a b c ↔ Collinear3 a c b := by
  have key : ∀ p q r : V3, Collinear3 p q r → Collinear3 p r q := by
    intro p q r hcol
    refine hcol.subset ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  unfold Collinear3
  exact ⟨fun h => key a b c h, fun h => key a c b h⟩

/-- Gram form of the ups bound at a unit leading edge: `ups_x 1 1 x = x(4-x)`. -/
private theorem ea4_ups4_unit (x : ℝ) : upsX (1:ℝ) 1 x = x * (4 - x) := by
  simp only [upsX]; ring

/-- From `0 < ups_x 1 1 x` read off `0 < x < 4` (both factors of `x(4-x)`). -/
private theorem ea4_unit_lt4 {x : ℝ} (h : 0 < upsX (1:ℝ) 1 x) : 0 < x ∧ x < 4 := by
  rw [ea4_ups4_unit x] at h
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exfalso
    have t : x * (4 - x) ≤ 0 := by
      calc x * (4 - x) = -((-x) * (4 - x)) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (by linarith) (by linarith))
    linarith
  · exfalso
    have h0 : x * (4 - x) = 0 := by rw [hx]; norm_num
    linarith
  · rcases lt_trichotomy x 4 with hx2 | hx2 | hx2
    · exact ⟨hx, hx2⟩
    · exfalso
      have h0 : x * (4 - x) = 0 := by rw [hx2]; norm_num
      linarith
    · exfalso
      have t : x * (4 - x) ≤ 0 := by
        calc x * (4 - x) = -((x - 4) * x) := by ring
          _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (by linarith) (by linarith))
      linarith

/-- The key 6-premise fact (closes the W1 recorded merge gap): positive `ups_x`
with a positive first entry forces the other two entries positive, since
`ups_x a b c = 4ac - (b-a-c)^2` bounds `b > (sqrt a - sqrt c)^2 >= 0`. -/
private theorem ea4_pos_of_upsX_pos {a b c : ℝ} (ha : 0 < a) (h : 0 < upsX a b c) :
    0 < b ∧ 0 < c := by
  have hkey : upsX a b c = 4 * a * c - (b - a - c) ^ 2 := by
    simp only [upsX]; ring
  rw [hkey] at h
  have hge : (0:ℝ) ≤ (b - a - c) ^ 2 := sq_nonneg _
  have hac : (0:ℝ) < 4 * a * c := by linarith
  have h4c : (0:ℝ) < 4 * c := by
    have hEq : a * (4 * c) = 4 * a * c := by ring
    have h0 : a * 0 < a * (4 * c) := by rw [mul_zero, hEq]; exact hac
    exact lt_of_mul_lt_mul_left h0 ha.le
  have hc : (0:ℝ) < c := by
    have hd4 : (0:ℝ) < 4 := by norm_num
    have h5 : c = 4 * c / 4 := by field_simp
    rw [h5]; exact div_pos h4c hd4
  have hsm : Real.sqrt (a * c) = Real.sqrt a * Real.sqrt c := Real.sqrt_mul ha.le c
  have hsqrtac : (2 * Real.sqrt (a * c)) ^ 2 = 4 * a * c := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ha.le hc.le)]
    ring
  have hlt : (b - a - c) ^ 2 < (2 * Real.sqrt (a * c)) ^ 2 := by
    rw [hsqrtac]; linarith
  have habs : |b - a - c| < 2 * Real.sqrt (a * c) := by
    have hh := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (a * c))] at hh
  obtain ⟨hlo, -⟩ := abs_lt.mp habs
  have hbound : (Real.sqrt a - Real.sqrt c) ^ 2 = a + c - 2 * Real.sqrt (a * c) := by
    have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    linear_combination (norm := ring_nf) hsa + hsc + 2 * hsm
  have hb : (0:ℝ) < b := by
    linarith [hlo, hbound, sq_nonneg (Real.sqrt a - Real.sqrt c)]
  exact ⟨hb, hc⟩

/-- First quadrant: on `0 < a` the value is `arctan (b / a)` (verbatim copy of
the W1 private atom, which is not exported). -/
private theorem ea4_atn2_xpos (a b : ℝ) (ha : 0 < a) : atn2 a b = Real.arctan (b / a) := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · rfl
  · have hba : 0 < b / a := div_pos h2 ha
    rw [show a / b = (b / a)⁻¹ from by field_simp, Real.arctan_inv_of_pos hba]
    ring
  · have hz : 0 < -(b / a) := by
      rw [neg_pos]
      exact div_neg_of_neg_of_pos h3 ha
    have h1' : a / b = -(-(b / a))⁻¹ := by field_simp
    have h2' : b / a = -(-(b / a)) := by ring
    rw [h1', Real.arctan_neg, Real.arctan_inv_of_pos hz, h2', Real.arctan_neg]
    ring
  · have hb0 : b = 0 := by linarith
    rw [hb0] at h1
    simp at h1
    linarith

/-- `atn2` is positively homogeneous in both arguments (the scaling step of
HOL `EULER_FORMULA_RESCALE`: `sqrt d = m*n*p * sqrt d'`, `2*p = m*n*p * 2*p'`). -/
theorem ea4_atn2_smul {c a b : ℝ} (hc : 0 < c) :
    atn2 (c * a) (c * b) = atn2 a b := by
  have hcb : |c * b| = c * |b| := by rw [abs_mul, abs_of_pos hc]
  have hcond : |c * b| < c * a ↔ |b| < a := by
    rw [hcb]
    constructor
    · intro hh; exact lt_of_mul_lt_mul_left hh hc.le
    · intro hh; exact mul_lt_mul_of_pos_left hh hc
  have hcbne : b ≠ 0 → (c * b : ℝ) ≠ 0 := fun hh => mul_ne_zero (ne_of_gt hc) hh
  unfold atn2
  rcases lt_or_ge (abs b) a with h1 | h1
  · rw [if_pos (hcond.mpr h1), if_pos h1,
      show (c * b) / (c * a) = b / a from by field_simp]
  · rw [if_neg (not_lt.mpr (by rw [hcb]; exact mul_le_mul_of_nonneg_left h1 hc.le)),
      if_neg (not_lt.mpr h1)]
    rcases lt_trichotomy b 0 with h2 | h2 | h2
    · have hcbneg : c * b < 0 := by
        have ht := mul_lt_mul_of_pos_left h2 hc
        rwa [mul_zero] at ht
      rw [if_neg (by linarith : ¬ (0:ℝ) < c * b), if_neg (by linarith : ¬ (0:ℝ) < b),
        if_pos hcbneg, if_pos (by linarith : b < 0),
        show (c * a) / (c * b) = a / b from by field_simp [hcbne (ne_of_lt h2)]]
    · subst h2
      norm_num
    · rw [if_pos (mul_pos hc h2), if_pos h2,
        show (c * a) / (c * b) = a / b from by field_simp [hcbne (ne_of_gt h2)]]

/-! ## §1 `euler_p` and the translation to `eulerA_x` -/

/-- HOL `euler_p` (sphere.hl:394, via `ylist` sphere.hl:387): the functional
`y1*y2*y3 + y1*(w2 dot w3) + y2*(w1 dot w3) + y3*(w1 dot w2)` with
`y_i = dist v0 v_i`, `w_i = v_i - v0` (the two inner slots are stated in the
`w1 dot w3` orientation that the law of cosines produces; mathematically the
HOL `w3 dot w1` / `w2 dot w1` by dot symmetry). -/
noncomputable def ea4_eulerP (v0 v1 v2 v3 : V3) : ℝ :=
  dist v0 v1 * dist v0 v2 * dist v0 v3
    + dist v0 v1 * (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
    + dist v0 v2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
    + dist v0 v3 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))

/-- The merge_ineq.hl:899-916 translation (HOL `euler_p_eulerA_x`): `euler_p`
is `eulerA_x` at the squared edge lengths (the law of cosines turns each
`x2 + x3 - x4` into `2 * w dot w`; `sqrt (dist^2) = dist`).  This is the
by-product consumed by LocalAuto22:161 once that lane's `euler_p` stub gains
its body (same shape as `euler_p_eulerA_x_p22` there). -/
theorem ea4_euler_p_eulerAX (v0 v1 v2 v3 : V3) :
    ea4_eulerP v0 v1 v2 v3 =
      ea1_eulerAX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
  unfold ea4_eulerP ea1_eulerAX
  have hs1 : Real.sqrt (dist v0 v1 ^ 2) = dist v0 v1 := Real.sqrt_sq dist_nonneg
  have hs2 : Real.sqrt (dist v0 v2 ^ 2) = dist v0 v2 := Real.sqrt_sq dist_nonneg
  have hs3 : Real.sqrt (dist v0 v3 ^ 2) = dist v0 v3 := Real.sqrt_sq dist_nonneg
  rw [hs1, hs2, hs3, ea4_law_cos v0 v2 v3, ea4_law_cos v0 v1 v3, ea4_law_cos v0 v1 v2]
  ring

/-- The rescale algebra (`LEMMA_FOR_EULER_AFTER_RESCALE`, euler_complement.hl):
under a positive rescaling of the three edges out of `v0`, `euler_p` scales by
exactly `m * n * p` — every term carries one factor of each edge. -/
theorem ea4_euler_after_rescale (v0 v1 v2 v3 u0 u1 u2 u3 : V3) (m n p : ℝ)
    (hm1 : v1 - v0 = m • (u1 - u0)) (hm2 : v2 - v0 = n • (u2 - u0))
    (hm3 : v3 - v0 = p • (u3 - u0)) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) :
    ea4_eulerP v0 v1 v2 v3 = (m * n * p) * ea4_eulerP u0 u1 u2 u3 := by
  have e1 : dist v0 v1 = m * dist u0 u1 := by
    rw [dist_eq_norm, show (v0 : V3) - v1 = -((v1 : V3) - v0) from by abel, norm_neg, hm1,
      norm_smul, Real.norm_eq_abs, abs_of_pos hm, ← dist_eq_norm, dist_comm u1 u0]
  have e2 : dist v0 v2 = n * dist u0 u2 := by
    rw [dist_eq_norm, show (v0 : V3) - v2 = -((v2 : V3) - v0) from by abel, norm_neg, hm2,
      norm_smul, Real.norm_eq_abs, abs_of_pos hn, ← dist_eq_norm, dist_comm u2 u0]
  have e3 : dist v0 v3 = p * dist u0 u3 := by
    rw [dist_eq_norm, show (v0 : V3) - v3 = -((v3 : V3) - v0) from by abel, norm_neg, hm3,
      norm_smul, Real.norm_eq_abs, abs_of_pos hp, ← dist_eq_norm, dist_comm u3 u0]
  have f1 : (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = (n * p) * (((u2 - u0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((u3 - u0 : V3) : Fin 3 → ℝ)) := by
    rw [hm2, hm3, ea4_coe_smul, ea4_coe_smul, dotProduct_smul, smul_dotProduct]
    ring
  have f2 : (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = (m * p) * (((u1 - u0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((u3 - u0 : V3) : Fin 3 → ℝ)) := by
    rw [hm1, hm3, ea4_coe_smul, ea4_coe_smul, dotProduct_smul, smul_dotProduct]
    ring
  have f3 : (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      = (m * n) * (((u1 - u0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((u2 - u0 : V3) : Fin 3 → ℝ)) := by
    rw [hm1, hm2, ea4_coe_smul, ea4_coe_smul, dotProduct_smul, smul_dotProduct]
    ring
  unfold ea4_eulerP
  rw [e1, e2, e3, f1, f2, f3]
  ring

/-! ## §2 The unit box: EULER_ANGLE_SUM_rescal -/

/-- HOL `EULER_ANGLE_SUM_rescal` (euler_main_theorem.hl:42-59): the Euler
angle sum for a tetrahedron whose three edges out of `v0` have unit length,
i.e. the `x1 = x2 = x3 = 1` box.  Noncollinearity comes from `0 < delta_x`
(W2 `ea2_not_collinear_of_delta_pos`), the three angles collapse to
`pi/2 - atn(L_i / (2 sqrt d))` with `L_i = -2x+2y+2z-yz` the rotated
`delta_x4` at the unit box, and the identity closes with W3
`ea3_derivative_wrt_a` at `(x4, x5, x6)`. -/
theorem ea4_euler_angle_sum_rescal (v0 v1 v2 v3 : V3) (x4 x5 x6 : ℝ)
    (e4 : dist v2 v3 ^ 2 = x4) (e5 : dist v1 v3 ^ 2 = x5) (e6 : dist v1 v2 ^ 2 = x6)
    (h1 : dist v0 v1 = 1) (h2 : dist v0 v2 = 1) (h3 : dist v0 v3 = 1)
    (hd : 0 < deltaX (1:ℝ) 1 1 x4 x5 x6) :
    dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 - Real.pi
      = Real.pi - 2 * atn2 (Real.sqrt (deltaX (1:ℝ) 1 1 x4 x5 x6))
          (2 * ea4_eulerP v0 v1 v2 v3) := by
  -- the Gram core of the unit box
  have hDkey : deltaX (1:ℝ) 1 1 x4 x5 x6 = upsX x4 x5 x6 - x4 * x5 * x6 := by
    simp only [deltaX, upsX]; ring
  -- noncollinearity from `0 < d` (HOL DELTA_X_LT_0_COLLINEAR)
  have hdD : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [h1, h2, h3, e4, e5, e6]; simp only [one_pow]; exact hd
  have hnc := ea2_not_collinear_of_delta_pos v0 v1 v2 v3 hdD
  -- the ups bounds at the unit box, each from a noncollinear triple
  have hu_x6 : 0 < upsX (1:ℝ) 1 x6 := by
    have ht := (ea2_upsX_pos_iff v0 v1 v2).mpr hnc.1
    rwa [h1, h2, one_pow, e6] at ht
  have hu_x5 : 0 < upsX (1:ℝ) 1 x5 := by
    have ht := (ea2_upsX_pos_iff v0 v1 v3).mpr hnc.2.1
    rwa [h1, h3, one_pow, e5] at ht
  have hu_x4 : 0 < upsX (1:ℝ) 1 x4 := by
    have ht := (ea2_upsX_pos_iff v0 v3 v2).mpr hnc.2.2
    rwa [h3, h2, one_pow, dist_comm v3 v2, e4] at ht
  have hp4 := ea4_unit_lt4 hu_x4
  have hp5 := ea4_unit_lt4 hu_x5
  have hp6 := ea4_unit_lt4 hu_x6
  -- the six ups premises for the dihV -> dihXf bridges (three rotations)
  have hb1 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v1 v2 ^ 2) :=
    (ea2_upsX_pos_iff v0 v1 v2).mpr hnc.1
  have hb2 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v3 ^ 2) (dist v1 v3 ^ 2) :=
    (ea2_upsX_pos_iff v0 v1 v3).mpr hnc.2.1
  have hb3 : 0 < upsX (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) := by
    have ht := (ea2_upsX_pos_iff v0 v3 v2).mpr hnc.2.2
    rwa [ea4_upsX_sym, dist_comm v3 v2] at ht
  have hb4 : 0 < upsX (dist v0 v2 ^ 2) (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) :=
    (ea2_upsX_pos_iff v0 v2 v1).mpr
      (fun hcol => hnc.1 ((ea4_collinear3_right v0 v1 v2).mpr hcol))
  have hb5 : 0 < upsX (dist v0 v3 ^ 2) (dist v0 v1 ^ 2) (dist v3 v1 ^ 2) :=
    (ea2_upsX_pos_iff v0 v3 v1).mpr
      (fun hcol => hnc.2.1 ((ea4_collinear3_right v0 v1 v3).mpr hcol))
  have hb6 : 0 < upsX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v3 v2 ^ 2) :=
    (ea2_upsX_pos_iff v0 v3 v2).mpr hnc.2.2
  -- shared numeric atoms
  set D : ℝ := deltaX (1:ℝ) 1 1 x4 x5 x6 with hDdef
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hd
  have h2sD : 0 < 2 * Real.sqrt D := by linarith
  have hsq4 : Real.sqrt (4 * D) = 2 * Real.sqrt D := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  have d4unit : deltaX4 (1:ℝ) 1 1 x4 x5 x6 = -2 * x4 + 2 * x5 + 2 * x6 - x5 * x6 := by
    simp only [deltaX4]; ring
  -- the distance-form rewrite atoms for the three rotated dihXf tuples
  have hDsym : ∀ a b c : ℝ, deltaX (1:ℝ) 1 1 a b c = deltaX (1:ℝ) 1 1 c a b := by
    intro a b c
    simp only [deltaX]
    ring
  have hDf1 : deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) = D := by
    rw [h1, h2, h3, e4, e5, e6]; simp only [one_pow]; exact hDdef.symm
  have hD4f1 : deltaX4 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)
      = deltaX4 (1:ℝ) 1 1 x4 x5 x6 := by
    rw [h1, h2, h3, e4, e5, e6]; simp only [one_pow]
  have hDf2 : deltaX (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v0 v1 ^ 2)
      (dist v3 v1 ^ 2) (dist v2 v1 ^ 2) (dist v2 v3 ^ 2) = D := by
    rw [h2, h3, h1]; simp only [one_pow]
    rw [dist_comm v3 v1, e5, dist_comm v2 v1, e6, e4, hDsym x5 x6 x4]
  have hD4f2 : deltaX4 (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v0 v1 ^ 2)
      (dist v3 v1 ^ 2) (dist v2 v1 ^ 2) (dist v2 v3 ^ 2)
      = deltaX4 (1:ℝ) 1 1 x5 x6 x4 := by
    rw [h2, h3, h1]; simp only [one_pow]
    rw [dist_comm v3 v1, e5, dist_comm v2 v1, e6, e4]
  have hDf3 : deltaX (dist v0 v3 ^ 2) (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
      (dist v1 v2 ^ 2) (dist v3 v2 ^ 2) (dist v3 v1 ^ 2) = D := by
    rw [h3, h1, h2]; simp only [one_pow]
    rw [dist_comm v3 v2, e4, dist_comm v3 v1, e5, e6, ← hDsym x4 x5 x6]
  have hD4f3 : deltaX4 (dist v0 v3 ^ 2) (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
      (dist v1 v2 ^ 2) (dist v3 v2 ^ 2) (dist v3 v1 ^ 2)
      = deltaX4 (1:ℝ) 1 1 x6 x4 x5 := by
    rw [h3, h1, h2]; simp only [one_pow]
    rw [dist_comm v3 v2, e4, dist_comm v3 v1, e5, e6]
  -- the three angles collapse to the three ea3 slots
  have halpha1 : dihV v0 v1 v2 v3
      = Real.pi / 2 - Real.arctan ((-2 * x4 + 2 * x5 + 2 * x6 - x5 * x6) / (2 * Real.sqrt D)) := by
    rw [ea2_dihV_dih_x v0 v1 v2 v3 hb1 hb2, dihXf, hDf1, hD4f1,
      show (4:ℝ) * dist v0 v1 ^ 2 = 4 from by rw [h1]; norm_num,
      d4unit, hsq4, ea1_atn2_rneg _ _ (Or.inr h2sD), ea4_atn2_xpos _ _ h2sD]
    ring
  have halpha2 : dihV v0 v2 v3 v1
      = Real.pi / 2 - Real.arctan ((-2 * x5 + 2 * x6 + 2 * x4 - x6 * x4) / (2 * Real.sqrt D)) := by
    rw [ea2_dihV_dih_x v0 v2 v3 v1 hb3 hb4, dihXf, hDf2, hD4f2,
      show (4:ℝ) * dist v0 v2 ^ 2 = 4 from by rw [h2]; norm_num,
      show deltaX4 (1:ℝ) 1 1 x5 x6 x4 = -2 * x5 + 2 * x6 + 2 * x4 - x6 * x4 from by
        simp only [deltaX4]; ring,
      hsq4, ea1_atn2_rneg _ _ (Or.inr h2sD), ea4_atn2_xpos _ _ h2sD]
    ring
  have halpha3 : dihV v0 v3 v1 v2
      = Real.pi / 2 - Real.arctan ((-2 * x6 + 2 * x4 + 2 * x5 - x4 * x5) / (2 * Real.sqrt D)) := by
    rw [ea2_dihV_dih_x v0 v3 v1 v2 hb5 hb6, dihXf, hDf3, hD4f3,
      show (4:ℝ) * dist v0 v3 ^ 2 = 4 from by rw [h3]; norm_num,
      show deltaX4 (1:ℝ) 1 1 x6 x4 x5 = -2 * x6 + 2 * x4 + 2 * x5 - x4 * x5 from by
        simp only [deltaX4]; ring,
      hsq4, ea1_atn2_rneg _ _ (Or.inr h2sD), ea4_atn2_xpos _ _ h2sD]
    ring
  -- euler_p at the unit box = 4 - (x4+x5+x6)/2, so 2p = 8 - x4 - x5 - x6
  have hpE : 2 * ea4_eulerP v0 v1 v2 v3 = 8 - x4 - x5 - x6 := by
    have htr := ea4_euler_p_eulerAX v0 v1 v2 v3
    rw [htr, h1, h2, h3, e4, e5, e6]
    simp only [one_pow, ea1_eulerAX, Real.sqrt_one]
    linarith
  -- the W3 identity at (x4, x5, x6), restated in D
  have hsum := ea3_derivative_wrt_a x4 x5 x6 (by rw [← hDkey]; exact hd)
    ⟨hp4.1, hp5.1, hp6.1⟩ ⟨hp4.2, hp5.2, hp6.2⟩
  rw [← hDkey] at hsum
  -- assembly
  rw [halpha1, halpha2, halpha3, hpE,
    ea4_atn2_xpos (Real.sqrt D) (8 - x4 - x5 - x6) hsD]
  linarith [hsum]

/-! ## §3 EULER_TRIANGLE (unit box -> all shapes) -/

/-- HOL `EULER_TRIANGLE` (euler_main_theorem.hl:504-518, i.e. the
`EULER_FORMULA_RESCALE` direction realized): for any tetrahedron with
`0 < delta_x`, the three solid-angle angles satisfy
`alpha1 + alpha2 + alpha3 - pi = pi - 2 * atn2 (sqrt d) (2 * euler_p)`. -/
theorem ea4_euler_triangle (v0 v1 v2 v3 : V3)
    (hd : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)) :
    dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 - Real.pi
      = Real.pi - 2 * atn2 (Real.sqrt (deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
          (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)))
          (2 * ea4_eulerP v0 v1 v2 v3) := by
  -- Step 1: the three edges out of v0 are nondegenerate (else d = 0)
  have hd1 : 0 < dist v0 v1 := by
    by_contra hcon
    have hz : dist v0 v1 = 0 := le_antisymm (le_of_not_gt hcon) dist_nonneg
    have hv1 : v0 = v1 := dist_eq_zero.mp hz
    subst hv1
    rw [dist_self, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hd
    have h0 : deltaX 0 (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2)
        (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) = 0 := by unfold deltaX; ring
    rw [h0] at hd
    linarith
  have hd2 : 0 < dist v0 v2 := by
    by_contra hcon
    have hz : dist v0 v2 = 0 := le_antisymm (le_of_not_gt hcon) dist_nonneg
    have hv2 : v0 = v2 := dist_eq_zero.mp hz
    subst hv2
    rw [dist_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), dist_comm v1 v0] at hd
    have h0 : deltaX (dist v0 v1 ^ 2) 0 (dist v0 v3 ^ 2) (dist v0 v3 ^ 2)
        (dist v1 v3 ^ 2) (dist v0 v1 ^ 2) = 0 := by unfold deltaX; ring
    rw [h0] at hd
    linarith
  have hd3 : 0 < dist v0 v3 := by
    by_contra hcon
    have hz : dist v0 v3 = 0 := le_antisymm (le_of_not_gt hcon) dist_nonneg
    have hv3 : v0 = v3 := dist_eq_zero.mp hz
    subst hv3
    rw [dist_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), dist_comm v2 v0, dist_comm v1 v0] at hd
    have h0 : deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) 0 (dist v0 v2 ^ 2)
        (dist v0 v1 ^ 2) (dist v1 v2 ^ 2) = 0 := by unfold deltaX; ring
    rw [h0] at hd
    linarith
  -- Step 2: rescale each edge to unit length about v0
  set u1 : V3 := v0 + (dist v0 v1)⁻¹ • (v1 - v0 : V3) with hu1def
  set u2 : V3 := v0 + (dist v0 v2)⁻¹ • (v2 - v0 : V3) with hu2def
  set u3 : V3 := v0 + (dist v0 v3)⁻¹ • (v3 - v0 : V3) with hu3def
  have hdu1 : (u1 - v0 : V3) = (dist v0 v1)⁻¹ • (v1 - v0 : V3) := by
    rw [hu1def]; abel
  have hdu2 : (u2 - v0 : V3) = (dist v0 v2)⁻¹ • (v2 - v0 : V3) := by
    rw [hu2def]; abel
  have hdu3 : (u3 - v0 : V3) = (dist v0 v3)⁻¹ • (v3 - v0 : V3) := by
    rw [hu3def]; abel
  have hD1 : (v1 - v0 : V3) = dist v0 v1 • (u1 - v0 : V3) := by
    rw [hdu1, smul_smul, mul_inv_cancel₀ (ne_of_gt hd1), one_smul]
  have hD2 : (v2 - v0 : V3) = dist v0 v2 • (u2 - v0 : V3) := by
    rw [hdu2, smul_smul, mul_inv_cancel₀ (ne_of_gt hd2), one_smul]
  have hD3 : (v3 - v0 : V3) = dist v0 v3 • (u3 - v0 : V3) := by
    rw [hdu3, smul_smul, mul_inv_cancel₀ (ne_of_gt hd3), one_smul]
  -- Step 3: dihV is rescale-invariant
  have halpha1 : dihV v0 v1 v2 v3 = dihV v0 u1 u2 u3 :=
    ea2_dihv_rescale_unchanged v0 v1 v2 v3 v0 u1 u2 u3 (dist v0 v1) (dist v0 v2)
      (dist v0 v3) hD1 hD2 hD3 hd1 hd2 hd3
  have halpha2 : dihV v0 v2 v3 v1 = dihV v0 u2 u3 u1 :=
    ea2_dihv_rescale_unchanged v0 v2 v3 v1 v0 u2 u3 u1 (dist v0 v2) (dist v0 v3)
      (dist v0 v1) hD2 hD3 hD1 hd2 hd3 hd1
  have halpha3 : dihV v0 v3 v1 v2 = dihV v0 u3 u1 u2 :=
    ea2_dihv_rescale_unchanged v0 v3 v1 v2 v0 u3 u1 u2 (dist v0 v3) (dist v0 v1)
      (dist v0 v2) hD3 hD1 hD2 hd3 hd1 hd2
  -- Step 4: sqrt delta_x rescales by m*n*p
  have hmnp : 0 < dist v0 v1 * dist v0 v2 * dist v0 v3 :=
    mul_pos (mul_pos hd1 hd2) hd3
  have hsqrt : Real.sqrt (deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2))
      = (dist v0 v1 * dist v0 v2 * dist v0 v3) * Real.sqrt (deltaX (dist v0 u1 ^ 2)
        (dist v0 u2 ^ 2) (dist v0 u3 ^ 2) (dist u2 u3 ^ 2) (dist u1 u3 ^ 2)
        (dist u1 u2 ^ 2)) :=
    ea2_sqrt_delta_rescale v0 v1 v2 v3 v0 u1 u2 u3 (dist v0 v1) (dist v0 v2)
      (dist v0 v3) hD1 hD2 hD3 hd1.le hd2.le hd3.le
  have hS : 0 < Real.sqrt (deltaX (dist v0 u1 ^ 2) (dist v0 u2 ^ 2) (dist v0 u3 ^ 2)
      (dist u2 u3 ^ 2) (dist u1 u3 ^ 2) (dist u1 u2 ^ 2)) := by
    by_contra hle
    have hzero : Real.sqrt (deltaX (dist v0 u1 ^ 2) (dist v0 u2 ^ 2) (dist v0 u3 ^ 2)
        (dist u2 u3 ^ 2) (dist u1 u3 ^ 2) (dist u1 u2 ^ 2)) = 0 :=
      le_antisymm (le_of_not_gt hle) (Real.sqrt_nonneg _)
    rw [hzero] at hsqrt
    have hpos : 0 < Real.sqrt (deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)) := Real.sqrt_pos.mpr hd
    linarith
  have hd' : 0 < deltaX (dist v0 u1 ^ 2) (dist v0 u2 ^ 2) (dist v0 u3 ^ 2)
      (dist u2 u3 ^ 2) (dist u1 u3 ^ 2) (dist u1 u2 ^ 2) := by
    by_contra hle
    have hzero : Real.sqrt (deltaX (dist v0 u1 ^ 2) (dist v0 u2 ^ 2) (dist v0 u3 ^ 2)
        (dist u2 u3 ^ 2) (dist u1 u3 ^ 2) (dist u1 u2 ^ 2)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hle)
    rw [hzero] at hS
    linarith
  -- Step 5: unit distances
  have hu1d : dist v0 u1 = 1 := by
    rw [dist_eq_norm, show (v0 : V3) - u1 = -((u1 : V3) - v0) from by abel, norm_neg,
      hdu1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd1), ← dist_eq_norm,
      dist_comm v1 v0, inv_mul_cancel₀ (ne_of_gt hd1)]
  have hu2d : dist v0 u2 = 1 := by
    rw [dist_eq_norm, show (v0 : V3) - u2 = -((u2 : V3) - v0) from by abel, norm_neg,
      hdu2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd2), ← dist_eq_norm,
      dist_comm v2 v0, inv_mul_cancel₀ (ne_of_gt hd2)]
  have hu3d : dist v0 u3 = 1 := by
    rw [dist_eq_norm, show (v0 : V3) - u3 = -((u3 : V3) - v0) from by abel, norm_neg,
      hdu3, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd3), ← dist_eq_norm,
      dist_comm v3 v0, inv_mul_cancel₀ (ne_of_gt hd3)]
  -- Step 6: the unit case, then rescale the atn2 arguments back
  have hdD' : 0 < deltaX (1:ℝ) 1 1 (dist u2 u3 ^ 2) (dist u1 u3 ^ 2)
      (dist u1 u2 ^ 2) := by
    have hc := hd'
    rw [show dist v0 u1 ^ 2 = (1:ℝ) from by rw [hu1d]; norm_num,
      show dist v0 u2 ^ 2 = (1:ℝ) from by rw [hu2d]; norm_num,
      show dist v0 u3 ^ 2 = (1:ℝ) from by rw [hu3d]; norm_num] at hc
    exact hc
  have hunit := ea4_euler_angle_sum_rescal v0 u1 u2 u3 (dist u2 u3 ^ 2)
    (dist u1 u3 ^ 2) (dist u1 u2 ^ 2) rfl rfl rfl hu1d hu2d hu3d hdD'
  have hp2 : 2 * ea4_eulerP v0 v1 v2 v3
      = (dist v0 v1 * dist v0 v2 * dist v0 v3)
        * (2 * ea4_eulerP v0 u1 u2 u3) := by
    rw [ea4_euler_after_rescale v0 v1 v2 v3 v0 u1 u2 u3 (dist v0 v1) (dist v0 v2)
      (dist v0 v3) hD1 hD2 hD3 hd1 hd2 hd3]
    ring
  rw [halpha1, halpha2, halpha3, hsqrt, hp2, hu1d, hu2d, hu3d]
  simp only [one_pow]
  rw [ea4_atn2_smul hmnp]
  exact hunit

/-! ## §4 Assembly: sol_x = sol_euler_x and the 6-premise anchor -/

/-- HOL `sol_x_sol_euler_x` (merge_ineq.hl:841-916), premise-for-premise with
`sol_euler_x` inlined as `2 * atn2 (2 * eulerA_x) (sqrt delta_x)`
(sphere.hl:735): at a proper tetrahedron the dihXf solid angle equals the
euler arctangent form.  The witness simplex comes from W2
`ea2_simplex_exists`, the three angles from `ea4_euler_triangle`, and the
`pi/2` swap from W1 `ea1_pi2_sub_atn2`. -/
theorem ea4_sol_x_sol_euler_x (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (u1 : 0 < upsX x1 x2 x6) (u2 : 0 < upsX x2 x3 x4)
    (u3 : 0 < upsX x1 x3 x5) (he : 0 < ea1_eulerAX x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    solX x1 x2 x3 x4 x5 x6 =
      2 * atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
        (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) := by
  obtain ⟨v0, v1, v2, v3, e01, e02, e03, e23, e13, e12, -, -, -, -⟩ :=
    ea2_simplex_exists x1 x2 x3 x4 x5 x6 h1 u1 hd
  -- the three dihV bridges, at the three rotations
  have c1 : dihV v0 v1 v2 v3 = dihXf x1 x2 x3 x4 x5 x6 := by
    rw [ea2_dihV_dih_x v0 v1 v2 v3 (by rw [e01, e02, e12]; exact u1)
        (by rw [e01, e03, e13]; exact u3),
      e01, e02, e03, e23, e13, e12]
  have c2 : dihV v0 v2 v3 v1 = dihXf x2 x3 x1 x5 x6 x4 := by
    have hu := ea2_dihV_dih_x v0 v2 v3 v1
      (by rw [e02, e03, e23]; exact u2)
      (by rw [e02, e01, show dist v2 v1 ^ 2 = x6 from by rw [dist_comm v2 v1]; exact e12];
          rw [ea4_upsX_sym]; exact u1)
    rw [hu, e02, e03, e01, show dist v3 v1 ^ 2 = x5 from by rw [dist_comm v3 v1]; exact e13,
      show dist v2 v1 ^ 2 = x6 from by rw [dist_comm v2 v1]; exact e12, e23]
  have c3 : dihV v0 v3 v1 v2 = dihXf x3 x1 x2 x6 x4 x5 := by
    have hu := ea2_dihV_dih_x v0 v3 v1 v2
      (by rw [e03, e01, show dist v3 v1 ^ 2 = x5 from by rw [dist_comm v3 v1]; exact e13];
          rw [ea4_upsX_sym]; exact u3)
      (by rw [e03, e02, show dist v3 v2 ^ 2 = x4 from by rw [dist_comm v3 v2]; exact e23];
          rw [ea4_upsX_sym]; exact u2)
    rw [hu, e03, e01, e02, e12,
      show dist v3 v2 ^ 2 = x4 from by rw [dist_comm v3 v2]; exact e23,
      show dist v3 v1 ^ 2 = x5 from by rw [dist_comm v3 v1]; exact e13]
  -- the angle-sum identity at the witness simplex
  have hdD : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [e01, e02, e03, e23, e13, e12]; exact hd
  -- the pi/2 swap (merge_ineq.hl:893-897, pi2_sub_atn2)
  have hswap : Real.pi - 2 * atn2 (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6))
        (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
      = 2 * atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
        (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) := by
    have hkey := ea1_pi2_sub_atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
      (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) (by linarith) (Real.sqrt_pos.mpr hd)
    calc Real.pi - 2 * atn2 (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6))
          (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
        = Real.pi - 2 * (Real.pi / 2 - atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
            (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6))) := by rw [← hkey]
      _ = 2 * atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
            (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) := by ring
  unfold solX
  rw [← c1, ← c2, ← c3, ea4_euler_triangle v0 v1 v2 v3 hdD,
    e01, e02, e03, e23, e13, e12, ea4_euler_p_eulerAX v0 v1 v2 v3,
    e01, e02, e03, e23, e13, e12, hswap]

/-- The 6-premise anchor `ea1_euler_anchor6` (verbatim mirror of PA21
`p21k_euler_anchor`): the strengthened merge of merge_ineq.hl:841
`sol_x_sol_euler_x` (six premises, proved above) with merge:1060
`sol_x_sol_x_sqrtdelta` (W1 `ea1_sol_euler_x_sqrtdelta`).  The W1-recorded
premise gap closes here: `0 < x2` and `0 < x3` follow from the six premises
via `ea4_pos_of_upsX_pos` (`4*x1*x6 > (x2-x1-x6)^2` bounds
`x2 > (sqrt x1 - sqrt x6)^2 >= 0`).  W5 wiring: one `exact` after
`ea1_eulerAX = eulerAX` (`rfl`, identical bodies). -/
theorem ea4_euler_anchor6 : ea1_euler_anchor6 := by
  intro x1 x2 x3 x4 x5 x6 h1 u1 u2 u3 he hd
  obtain ⟨h2, -⟩ := ea4_pos_of_upsX_pos h1 u1
  obtain ⟨h3, -⟩ := ea4_pos_of_upsX_pos h2 u2
  rw [ea4_sol_x_sol_euler_x x1 x2 x3 x4 x5 x6 h1 u1 u2 u3 he hd,
    ea1_sol_euler_x_sqrtdelta x1 x2 x3 x4 x5 x6 h1 h2 h3 he hd.le]

end Kepler.Text
