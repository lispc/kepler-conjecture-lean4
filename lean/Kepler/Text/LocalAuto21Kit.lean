/-
LocalAuto21Kit — staging leaf for the `CUXVZOZ.hl` simplex-completion kit
(HOL anchors CUXVZOZ.hl:113 `simplex_unique`, :232 `mk_simplex_uniq`), real
proofs consumed by the LocalAuto21 wave-2 rewiring.

Leaf module discipline: imports only `V3Coe` + `LocalAuto1` + `LocalAuto11`
(their transitive closures bring `PackingAuto18` — `cross3`/`reEqvl`/
`delta_delta_x`/`POS_EQ_NOT_COPLANANR`/`coplanar_eq_coplanar_alt` — and
`Kepler.Geom.Azim` — `Collinear3`/`collinear3_iff_smul` — plus
`Kepler.Geom.Coplanar.coplanar_triple`).  No `LocalAuto21` import: at
integration `LocalAuto21` will import THIS module (one-way edge, no cycle)
and its `simplex_unique_p21` / `mk_simplex_uniq_p21` stubs close by one-line
`exact` to the theorems below.

The `w2_*` private helpers reprove the small cross3/dot algebra that sits
`private` in LocalAuto17/LocalAuto14 (invisible cross-module) — statements
are standard Mathlib-facing facts, no HOL content.
-/
import Kepler.Text.V3Coe
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto11
import Mathlib

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom

/-! ## Private cross3 / dot algebra (LA17-style helpers, local copies) -/

private theorem w2_dot_smul_left (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem w2_dot_smul_right (t : ℝ) (a b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem w2_dot_add_left (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem w2_dot_add_right (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem w2_dot_add4 (u v w z : V3) :
    (u + v) ⬝ᵥ (w + z) = u ⬝ᵥ w + u ⬝ᵥ z + v ⬝ᵥ w + v ⬝ᵥ z := by
  simp only [w2_dot_add_right, w2_dot_add_left]
  ring

private theorem w2_dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem w2_dot_sub_left (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem w2_dot_sub_right (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem w2_dot_neg_neg (x y : V3) : (-x) ⬝ᵥ (-y) = x ⬝ᵥ y := by
  simp [dotProduct]

private theorem w2_dot_zero_left (x : V3) : (0 : V3) ⬝ᵥ x = 0 := by
  simp [dotProduct]

private theorem w2_cross3_self (a : V3) : cross3 a a = 0 := by
  simp only [cross3, cross_self, WithLp.toLp_zero]

private theorem w2_cross3_smul_left (a : V3) (c : ℝ) (x : V3) :
    cross3 (c • a) x = c • cross3 a x := by
  simp only [cross3, WithLp.ofLp_smul, map_smul]
  rfl

private theorem w2_cross3_zero_left (v : V3) : cross3 0 v = 0 := by
  conv_lhs => rw [show (0 : V3) = (0 : ℝ) • v from by simp]
  rw [w2_cross3_smul_left, w2_cross3_self, smul_zero]

private theorem w2_cross3_zero_right (u : V3) : cross3 u 0 = 0 := by
  simp [cross3, map_zero]

private theorem w2_dot_cross3_self_left (a b : V3) : a ⬝ᵥ cross3 a b = 0 :=
  dot_self_cross (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem w2_dot_cross3_self_right (a b : V3) : b ⬝ᵥ cross3 a b = 0 :=
  dot_cross_self (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- Cyclic invariance of the scalar triple product `T(a,b,c) = T(c,a,b)`. -/
private theorem w2_triple_cyclic (a b c : V3) :
    a ⬝ᵥ cross3 b c = c ⬝ᵥ cross3 a b := by
  simp only [cross3, dotProduct, cross_apply,
    Fin.sum_univ_three, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- Lagrange's identity in `V3`: `(a⬝a)(b⬝b) − (a⬝b)² = ‖a × b‖²`. -/
private theorem w2_lagrange (a b : V3) :
    (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) * (a ⬝ᵥ b) = cross3 a b ⬝ᵥ cross3 a b := by
  simp only [cross3, dotProduct, cross_apply,
    Fin.sum_univ_three, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- `‖x‖² = x ⬝ᵥ x` on `V3` (V3Coe bridge). -/
private theorem w2_norm_sq (x : V3) : ‖x‖ ^ 2 = x ⬝ᵥ x := by
  rw [Kepler.Text.V3Coe.norm_sq_eq_dotProduct]

private theorem w2_dot_pos_of_ne {x : V3} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  rw [← w2_norm_sq]
  exact pow_pos (norm_pos_iff.2 hx) 2

private theorem w2_dotP (x y : V3) : (x ⬝ᵥ y : ℝ) = (x.ofLp ⬝ᵥ y.ofLp : ℝ) := rfl

private theorem w2_add_coe {x y : V3} :
    ((x + y : V3) : Fin 3 → ℝ)
      = ((x : Fin 3 → ℝ) + (y : Fin 3 → ℝ) : Fin 3 → ℝ) := rfl

private theorem w2_smul_coe (c : ℝ) (x : V3) :
    ((c • x : V3) : Fin 3 → ℝ) = (c • (x : Fin 3 → ℝ) : Fin 3 → ℝ) := rfl

private theorem w2_sub_coe {x y z w : V3} (h : x - y = z - w) :
    ((z : Fin 3 → ℝ) - (w : Fin 3 → ℝ) : Fin 3 → ℝ)
      = ((x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) : Fin 3 → ℝ) := by
  have e1 : ((z : Fin 3 → ℝ) - (w : Fin 3 → ℝ) : Fin 3 → ℝ)
      = ((z - w : V3) : Fin 3 → ℝ) := rfl
  have e2 : ((x : Fin 3 → ℝ) - (y : Fin 3 → ℝ) : Fin 3 → ℝ)
      = ((x - y : V3) : Fin 3 → ℝ) := rfl
  rw [e1, e2, h]

private theorem w2_dot_add4P (u v w z : Fin 3 → ℝ) :
    ((u + v) ⬝ᵥ (w + z) : ℝ)
      = (u ⬝ᵥ w + u ⬝ᵥ z + v ⬝ᵥ w + v ⬝ᵥ z : ℝ) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  ring

private theorem w2_lagrangeP (a b : Fin 3 → ℝ) :
    (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) * (a ⬝ᵥ b)
      = (crossProduct a b ⬝ᵥ crossProduct a b : ℝ) := by
  rw [cross_apply]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.head_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- A nonzero cross product forces non-collinearity of `{0, u, v}` (LA17 copy,
pivot-flipped to the `smul_left` direction). -/
private theorem w2_not_collinear_of_cross_ne_zero {u v : V3} (h : cross3 u v ≠ 0) :
    ¬ Collinear ℝ ({0, u, v} : Set V3) := by
  intro hc
  apply h
  by_cases hu : u = 0
  · rw [hu]; exact w2_cross3_zero_left v
  · by_cases hv : v = 0
    · rw [hv]; exact w2_cross3_zero_right u
    · have hcv : Collinear3 (0 : V3) v u := by
        show Collinear ℝ ({0, v, u} : Set V3)
        rw [show ({0, v, u} : Set V3) = ({0, u, v} : Set V3) from by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
        exact hc
      obtain ⟨c, hc'⟩ :=
        (collinear3_iff_smul (v := (0 : V3)) (w := v) (w1 := u) hv).mp hcv
      have hc'' : u = c • v := by simpa using hc'
      rw [hc'', w2_cross3_smul_left, w2_cross3_self, smul_zero]

/-- Collinearity is invariant under translation by `-v0` (LA7-style copy). -/
private theorem w2_collinear_sub_v0 (v0 : V3) (s : Set V3) :
    Collinear ℝ ((fun z : V3 => z - v0) '' s) ↔ Collinear ℝ s := by
  constructor
  · intro hcol
    obtain ⟨p₀, vec, hall⟩ :=
      (collinear_iff_exists_forall_eq_smul_vadd ((fun z : V3 => z - v0) '' s)).mp hcol
    refine (collinear_iff_exists_forall_eq_smul_vadd s).mpr ⟨p₀ + v0, vec, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := hall (p - v0) (Set.mem_image_of_mem _ hp)
    refine ⟨r, ?_⟩
    show p = r • vec +ᵥ (p₀ + v0)
    have hp2 : p = (p - v0) +ᵥ v0 := by
      simp only [vadd_eq_add]; abel
    rw [hp2, hr]
    simp only [vadd_eq_add]
    abel
  · intro hcol
    obtain ⟨p₀, vec, hall⟩ :=
      (collinear_iff_exists_forall_eq_smul_vadd s).mp hcol
    refine (collinear_iff_exists_forall_eq_smul_vadd _).mpr ⟨p₀ - v0, vec, fun p' hp' => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hp'
    obtain ⟨r, hr⟩ := hall p hp
    refine ⟨r, ?_⟩
    show p - v0 = r • vec +ᵥ (p₀ - v0)
    rw [hr]
    simp only [vadd_eq_add]
    abel

/-- `homog_2x2` copy (LA21's public twin is unreachable from this leaf). -/
private theorem w2_homog_2x2 (a b c d x y : ℝ) (hdet : a * d - b * c ≠ 0)
    (h1 : a * x + b * y = 0) (h2 : c * x + d * y = 0) : x = 0 ∧ y = 0 := by
  have e1 : (a * d - b * c) * x = d * (a * x + b * y) - b * (c * x + d * y) := by ring
  have e2 : (a * d - b * c) * y = a * (c * x + d * y) - c * (a * x + b * y) := by ring
  rw [h1, h2] at e1 e2
  simp only [mul_zero, sub_zero] at e1 e2
  rcases mul_eq_zero.mp e1 with hx | hx
  · simp [hdet] at hx
  · refine ⟨hx, ?_⟩
    rcases mul_eq_zero.mp e2 with hy | hy
    · simp [hdet] at hy
    · exact hy

/-- Squared distances are equal only up to sign; both are nonnegative. -/
private theorem w2_sq_dist_eq {x y : ℝ} (h : x ^ 2 = y ^ 2) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact h1
  · linarith

/-! ## Coordinate helpers over the basis `{a, b, n}` -/

private theorem w2_sum3 (a b n : V3) (g : Fin 3 → ℝ) :
    ∑ i : Fin 3, g i • (![a, b, n] i) = g 0 • a + g 1 • b + g 2 • n := by
  rw [Fin.sum_univ_three]
  simp only [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

private theorem w2_coord_dot_a (a b n : V3) (hna : n ⬝ᵥ a = 0) (g : Fin 3 → ℝ) :
    (g 0 • a + g 1 • b + g 2 • n) ⬝ᵥ a = g 0 * (a ⬝ᵥ a) + g 1 * (b ⬝ᵥ a) := by
  rw [w2_dot_add_left, w2_dot_add_left, w2_dot_smul_left, w2_dot_smul_left,
    w2_dot_smul_left, hna, mul_zero, add_zero]

private theorem w2_coord_dot_b (a b n : V3) (hnb : n ⬝ᵥ b = 0) (g : Fin 3 → ℝ) :
    (g 0 • a + g 1 • b + g 2 • n) ⬝ᵥ b = g 0 * (a ⬝ᵥ b) + g 1 * (b ⬝ᵥ b) := by
  rw [w2_dot_add_left, w2_dot_add_left, w2_dot_smul_left, w2_dot_smul_left,
    w2_dot_smul_left, hnb, mul_zero, add_zero]

private theorem w2_coord_dot_n (a b n : V3) (han : a ⬝ᵥ n = 0) (hbn : b ⬝ᵥ n = 0)
    (g : Fin 3 → ℝ) :
    (g 0 • a + g 1 • b + g 2 • n) ⬝ᵥ n = g 2 * (n ⬝ᵥ n) := by
  simp only [w2_dot_add_left, w2_dot_smul_left, han, hbn, mul_zero, add_zero,
    zero_add]

private theorem w2_dot_exp (u w : V3) :
    (u - w) ⬝ᵥ (u - w) = u ⬝ᵥ u - 2 * (u ⬝ᵥ w) + w ⬝ᵥ w := by
  rw [w2_dot_sub_right, w2_dot_sub_left, w2_dot_sub_left, w2_dot_comm w u]
  ring

private theorem w2_dist_sq (u w : V3) : dist u w ^ 2 = (w - u) ⬝ᵥ (w - u) := by
  rw [dist_eq_norm, norm_sub_rev, w2_norm_sq, WithLp.ofLp_sub]

private theorem w2_coplanar_of_pair_eq {S : Set V3} {a b c : V3}
    (hS : S = ({a, b, c} : Set V3)) : Coplanar S := by
  rw [hS]; exact coplanar_triple a b c

/-! ## HOL `simplex_unique` (CUXVZOZ.hl:113) -/

/-- HOL `simplex_unique` (CUXVZOZ.hl:113): a tetrahedron completion is
uniquely determined by the three distances and the orientation class
(`re_eqvl` of the scalar triple products).  Port of the HOL
`NONCOPLANAR_3_BASIS`-expansion argument: expand `v3 - v0`, `v3' - v0` in the
basis `{v1 - v0, v2 - v0, (v1-v0) × (v2-v0)}`, kill the first two coordinates
with the distance equations + `homog_2x2` (Gram determinant `= ‖n‖² > 0` by
Lagrange), then the orientation class + `‖v3‖² = ‖v3'‖²` force the third
coordinate, with the sign fixed by `re_eqvl`. -/
theorem simplex_unique_w2 (v0 v1 v2 v3 v3' : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (d0 : dist v0 v3 = dist v0 v3') (d1 : dist v1 v3 = dist v1 v3')
    (d2 : dist v2 v3 = dist v2 v3')
    (hre : reEqvl ((v3 - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0))
      ((v3' - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0))) : v3 = v3' := by
  set a : V3 := v1 - v0 with ha
  set b : V3 := v2 - v0 with hb
  set n : V3 := cross3 a b with hndef
  set p : V3 := v3 - v0 with hpdef
  set q : V3 := v3' - v0 with hqdef
  -- collinearity transports to the origin
  have hnc0 : ¬ Collinear ℝ ({0, a, b} : Set V3) := by
    have himg : ({0, a, b} : Set V3)
        = (fun z : V3 => z - v0) '' ({v0, v1, v2} : Set V3) := by
      ext z
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨v0, by simp, (by simp : v0 - v0 = 0)⟩
        · exact ⟨v1, by simp, (by rw [ha] : v1 - v0 = a)⟩
        · exact ⟨v2, by simp, (by rw [hb] : v2 - v0 = b)⟩
      · rintro ⟨w, hw, rfl⟩
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (Or.inl (by rw [ha]))
        · exact Or.inr (Or.inr (by rw [hb]))
    rw [himg, w2_collinear_sub_v0]
    exact hnc
  have hnz : n ≠ 0 := by
    intro h0
    apply hnc0
    -- transport n = 0 to the Pi-level cross product
    have hcz : (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) ⬝ᵥ
        crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) : ℝ) = 0 := by
      have h1 : WithLp.ofLp (cross3 a b)
          = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) := rfl
      rw [← h1, ← hndef, h0, WithLp.ofLp_zero, dotProduct_zero]
    -- Lagrange turns it into the Cauchy–Schwarz equality case
    have hdet0 : (a.ofLp ⬝ᵥ a.ofLp : ℝ) * (b.ofLp ⬝ᵥ b.ofLp : ℝ)
        - (a.ofLp ⬝ᵥ b.ofLp : ℝ) * (a.ofLp ⬝ᵥ b.ofLp : ℝ) = 0 := by
      rw [w2_lagrangeP, hcz]
    have hprod : ‖a‖ ^ 2 * ‖b‖ ^ 2 = (inner ℝ a b : ℝ) ^ 2 := by
      rw [w2_norm_sq a, w2_norm_sq b, Kepler.Text.V3Coe.inner_eq_dotProduct]
      linear_combination hdet0
    by_cases ha0' : ‖a‖ = 0
    · rw [norm_eq_zero] at ha0'
      rw [ha0', show ({0, (0 : V3), b} : Set V3) = ({(0 : V3), b} : Set V3) from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact collinear_pair ℝ 0 b
    by_cases hb0' : ‖b‖ = 0
    · rw [norm_eq_zero] at hb0'
      rw [hb0', show ({0, a, (0 : V3)} : Set V3) = ({0, a} : Set V3) from by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      exact collinear_pair ℝ 0 a
    · -- |inner| = ‖a‖‖b‖ with both norms positive: Cauchy equality case
      have hpos : (0 : ℝ) < ‖a‖ * ‖b‖ :=
        mul_pos (norm_pos_iff.mpr (fun h => ha0' (by rw [h, norm_zero])))
          (norm_pos_iff.mpr (fun h => hb0' (by rw [h, norm_zero])))
      have hsq2 : (inner ℝ a b : ℝ) ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
        rw [← hprod, mul_pow]
      -- Cauchy equality case: b = c • a for some c
      have hcs2 : ‖b‖ • a = ‖a‖ • b ∨ ‖-b‖ • a = ‖a‖ • (-b) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with heq | heq
        · exact Or.inl ((inner_eq_norm_mul_iff_real (x := a) (y := b)).mp heq)
        · exact Or.inr ((inner_eq_norm_mul_iff_real (x := a) (y := -b)).mp
            (show inner ℝ a (-b) = ‖a‖ * ‖(-b : V3)‖ from by
              rw [inner_neg_right, norm_neg, heq]
              ring))
      rcases hcs2 with heq2 | heq2
      · have hcb : b = (‖b‖ / ‖a‖) • a := by
          calc b = ((‖a‖ : ℝ)⁻¹) • ((‖a‖ : ℝ) • b) := (inv_smul_smul₀ ha0' b).symm
            _ = ((‖a‖ : ℝ)⁻¹) • ((‖b‖ : ℝ) • a) := by rw [← heq2]
            _ = (((‖a‖ : ℝ)⁻¹ * ‖b‖)) • a := smul_smul _ _ _
            _ = (‖b‖ / ‖a‖) • a := by
                congr 1
                rw [div_eq_inv_mul]
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨0, a, fun p hp => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨‖b‖ / ‖a‖, by rw [vadd_eq_add, add_zero]; exact hcb⟩
      · have h2 : (‖a‖ : ℝ) • b = -((‖b‖ : ℝ) • a) := by
          have h := heq2
          rw [norm_neg, smul_neg] at h
          simpa using (congrArg Neg.neg h).symm
        have hcb : b = (-(‖b‖ / ‖a‖)) • a := by
          calc b = ((‖a‖ : ℝ)⁻¹) • ((‖a‖ : ℝ) • b) := (inv_smul_smul₀ ha0' b).symm
            _ = ((‖a‖ : ℝ)⁻¹) • (-((‖b‖ : ℝ) • a)) := by rw [h2]
            _ = -((((‖a‖ : ℝ)⁻¹ * ‖b‖)) • a) := by rw [smul_neg, smul_smul]
            _ = (-(‖b‖ / ‖a‖)) • a := by
                rw [neg_smul]
                congr 1
                rw [div_eq_inv_mul]
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨0, a, fun p hp => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨-(‖b‖ / ‖a‖), by rw [vadd_eq_add, add_zero]; exact hcb⟩
  have hnn : 0 < n ⬝ᵥ n := w2_dot_pos_of_ne hnz
  have hnna : a ⬝ᵥ n = 0 := w2_dot_cross3_self_left a b
  have hnnb : b ⬝ᵥ n = 0 := w2_dot_cross3_self_right a b
  have hnna' : n ⬝ᵥ a = 0 := (w2_dot_comm n a).trans hnna
  have hnnb' : n ⬝ᵥ b = 0 := (w2_dot_comm n b).trans hnnb
  have hdet : (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) * (a ⬝ᵥ b) ≠ 0 := by
    rw [w2_lagrange a b, ← hndef]
    exact ne_of_gt hnn
  -- linear independence of ![a, b, n]
  have hli : LinearIndependent ℝ ![a, b, n] := by
    rw [Fintype.linearIndependent_iffₛ]
    intro f g hfg
    have h2 : f 2 = g 2 := by
      have h3 := congrArg (fun s : V3 => s ⬝ᵥ n) hfg
      simp only [w2_sum3 a b n f, w2_sum3 a b n g] at h3
      rw [w2_coord_dot_n a b n hnna hnnb f, w2_coord_dot_n a b n hnna hnnb g] at h3
      exact mul_right_cancel₀ hnn.ne' h3
    have hsa : f 0 * (a ⬝ᵥ a) + f 1 * (b ⬝ᵥ a)
        = g 0 * (a ⬝ᵥ a) + g 1 * (b ⬝ᵥ a) := by
      have h3 := congrArg (fun s : V3 => s ⬝ᵥ a) hfg
      simp only [w2_sum3 a b n f, w2_sum3 a b n g] at h3
      rw [w2_coord_dot_a a b n hnna' f, w2_coord_dot_a a b n hnna' g] at h3
      exact h3
    have hsb : f 0 * (a ⬝ᵥ b) + f 1 * (b ⬝ᵥ b)
        = g 0 * (a ⬝ᵥ b) + g 1 * (b ⬝ᵥ b) := by
      have h3 := congrArg (fun s : V3 => s ⬝ᵥ b) hfg
      simp only [w2_sum3 a b n f, w2_sum3 a b n g] at h3
      rw [w2_coord_dot_b a b n hnnb' f, w2_coord_dot_b a b n hnnb' g] at h3
      exact h3
    have hsa' : (a ⬝ᵥ a) * (f 0 - g 0) + (a ⬝ᵥ b) * (f 1 - g 1) = 0 := by
      rw [w2_dot_comm b a] at hsa
      linear_combination hsa
    have hsb' : (a ⬝ᵥ b) * (f 0 - g 0) + (b ⬝ᵥ b) * (f 1 - g 1) = 0 := by
      linear_combination hsb
    obtain ⟨h4, h5⟩ := w2_homog_2x2 (a ⬝ᵥ a) (a ⬝ᵥ b) (a ⬝ᵥ b) (b ⬝ᵥ b)
      (f 0 - g 0) (f 1 - g 1) hdet hsa' hsb'
    intro i
    fin_cases i
    · exact sub_eq_zero.mp h4
    · exact sub_eq_zero.mp h5
    · exact h2
  have hspan : Submodule.span ℝ (Set.range (![a, b, n])) = (⊤ : Submodule ℝ V3) := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range (![a, b, n]))) = 3 := by
      rw [finrank_span_eq_card hli]
      simp
    have h2 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    exact Submodule.eq_top_of_finrank_eq (by rw [h1, h2])
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
    (x := p) (v := (![a, b, n]))).1 (by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨r', hr'⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
    (x := q) (v := (![a, b, n]))).1 (by rw [hspan]; exact Submodule.mem_top)
  have hr3 : r 0 • a + r 1 • b + r 2 • n = p := by
    simpa [Fin.sum_univ_three] using hr
  have hr'3 : r' 0 • a + r' 1 • b + r' 2 • n = q := by
    simpa [Fin.sum_univ_three] using hr'
  -- distance equations into dot-product relations
  have hsq0 : p ⬝ᵥ p = q ⬝ᵥ q := by
    have e0 : dist v0 v3 ^ 2 = dist v0 v3' ^ 2 := by rw [d0]
    rw [w2_dist_sq, w2_dist_sq, ← hpdef, ← hqdef] at e0
    exact e0
  have hsq1' : (v3 - v1) ⬝ᵥ (v3 - v1) = (v3' - v1) ⬝ᵥ (v3' - v1) := by
    have e1 : dist v1 v3 ^ 2 = dist v1 v3' ^ 2 := by rw [d1]
    rw [w2_dist_sq, w2_dist_sq] at e1
    exact e1
  have hsq1 : p ⬝ᵥ a = q ⬝ᵥ a := by
    have hpq1 : v3 - v1 = p - a := by rw [hpdef, ha]; abel
    have hpq2 : v3' - v1 = q - a := by rw [hqdef, ha]; abel
    have e1 : (p - a) ⬝ᵥ (p - a) = (q - a) ⬝ᵥ (q - a) := by
      rw [show ((p - a : V3) : Fin 3 → ℝ)
          = (p.ofLp - a.ofLp : Fin 3 → ℝ) from rfl,
        show ((q - a : V3) : Fin 3 → ℝ)
          = (q.ofLp - a.ofLp : Fin 3 → ℝ) from rfl,
        w2_sub_coe hpq1, w2_sub_coe hpq2]
      exact hsq1'
    rw [w2_dot_exp p a, w2_dot_exp q a, hsq0] at e1
    linarith
  have hsq2' : (v3 - v2) ⬝ᵥ (v3 - v2) = (v3' - v2) ⬝ᵥ (v3' - v2) := by
    have e2 : dist v2 v3 ^ 2 = dist v2 v3' ^ 2 := by rw [d2]
    rw [w2_dist_sq, w2_dist_sq] at e2
    exact e2
  have hsq2 : p ⬝ᵥ b = q ⬝ᵥ b := by
    have hpq3 : v3 - v2 = p - b := by rw [hpdef, hb]; abel
    have hpq4 : v3' - v2 = q - b := by rw [hqdef, hb]; abel
    have e2 : (p - b) ⬝ᵥ (p - b) = (q - b) ⬝ᵥ (q - b) := by
      rw [show ((p - b : V3) : Fin 3 → ℝ) = (p.ofLp - b.ofLp : Fin 3 → ℝ) from rfl,
        show ((q - b : V3) : Fin 3 → ℝ) = (q.ofLp - b.ofLp : Fin 3 → ℝ) from rfl,
        w2_sub_coe hpq3, w2_sub_coe hpq4]
      exact hsq2'
    rw [w2_dot_exp p b, w2_dot_exp q b, hsq0] at e2
    linarith
  -- Gram system kills the first two coordinates
  have hsysa : r 0 * (a ⬝ᵥ a) + r 1 * (b ⬝ᵥ a)
      = r' 0 * (a ⬝ᵥ a) + r' 1 * (b ⬝ᵥ a) := by
    have e1 : p ⬝ᵥ a = r 0 * (a ⬝ᵥ a) + r 1 * (b ⬝ᵥ a) := by
      rw [← hr3, w2_coord_dot_a a b n hnna' r]
    have e2 : q ⬝ᵥ a = r' 0 * (a ⬝ᵥ a) + r' 1 * (b ⬝ᵥ a) := by
      rw [← hr'3, w2_coord_dot_a a b n hnna' r']
    rw [hsq1] at e1
    linarith
  have hsysb : r 0 * (a ⬝ᵥ b) + r 1 * (b ⬝ᵥ b)
      = r' 0 * (a ⬝ᵥ b) + r' 1 * (b ⬝ᵥ b) := by
    have e1 : p ⬝ᵥ b = r 0 * (a ⬝ᵥ b) + r 1 * (b ⬝ᵥ b) := by
      rw [← hr3, w2_coord_dot_b a b n hnnb' r]
    have e2 : q ⬝ᵥ b = r' 0 * (a ⬝ᵥ b) + r' 1 * (b ⬝ᵥ b) := by
      rw [← hr'3, w2_coord_dot_b a b n hnnb' r']
    rw [hsq2] at e1
    linarith
  have hsysa2 := hsysa
  rw [w2_dot_comm b a] at hsysa2
  obtain ⟨hf0, hf1⟩ := w2_homog_2x2 (a ⬝ᵥ a) (a ⬝ᵥ b) (a ⬝ᵥ b) (b ⬝ᵥ b)
    (r 0 - r' 0) (r 1 - r' 1) hdet
    (by linear_combination hsysa2) (by linear_combination hsysb)
  have hf0' : r 0 = r' 0 := sub_eq_zero.mp hf0
  have hf1' : r 1 = r' 1 := sub_eq_zero.mp hf1
  -- third coordinate: Pythagoras against the common part `u`
  set u : V3 := r 0 • a + r 1 • b with hudef
  have hpu : p = u + r 2 • n := by rw [hudef, ← hr3]
  have hqu : q = u + r' 2 • n := by rw [hudef, ← hr'3, hf0', hf1']
  have huperp : u ⬝ᵥ n = 0 := by
    rw [hudef, w2_dot_add_left, w2_dot_smul_left, w2_dot_smul_left, hnna, hnnb,
      mul_zero, mul_zero, zero_add]
  have hsqn : ∀ c : ℝ, (c • n) ⬝ᵥ (c • n) = c * c * (n ⬝ᵥ n) := by
    intro c
    rw [w2_dot_smul_left, w2_dot_smul_right]
    ring
  have hpyth : ∀ x y : V3, x ⬝ᵥ y = 0 →
      (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + y ⬝ᵥ y := by
    intro x y hxy
    rw [w2_dot_add4 x y x y, hxy, w2_dot_comm y x, hxy]
    ring
  have hsplit : r 2 * r 2 * (n ⬝ᵥ n) = r' 2 * r' 2 * (n ⬝ᵥ n) := by
    have e := hsq0
    rw [hpu, hqu] at e
    have huperpP : (u.ofLp ⬝ᵥ n.ofLp : ℝ) = 0 := (w2_dotP u n).symm.trans huperp
    have hcommUP : (n.ofLp ⬝ᵥ u.ofLp : ℝ) = (u.ofLp ⬝ᵥ n.ofLp : ℝ) :=
      dotProduct_comm n.ofLp u.ofLp
    have hpythP : ∀ x y : Fin 3 → ℝ, (x ⬝ᵥ y : ℝ) = 0 →
        ((x + y) ⬝ᵥ (x + y) : ℝ) = (x ⬝ᵥ x : ℝ) + (y ⬝ᵥ y : ℝ) := by
      intro x y hxy
      rw [add_dotProduct, dotProduct_add, dotProduct_add, hxy, dotProduct_comm y x,
        hxy]
      ring
    have hupSq : ∀ c : ℝ,
        ((c • (n.ofLp : Fin 3 → ℝ)) ⬝ᵥ (c • (n.ofLp : Fin 3 → ℝ)) : ℝ)
          = (c * c) * (n.ofLp ⬝ᵥ n.ofLp : ℝ) := by
      intro c
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul] at e
    rw [hpythP u.ofLp (r 2 • n.ofLp) (by
          rw [dotProduct_smul, huperpP, smul_zero]),
      hpythP u.ofLp (r' 2 • n.ofLp) (by
          rw [dotProduct_smul, huperpP, smul_zero])] at e
    rw [hupSq (r 2), hupSq (r' 2)] at e
    linarith
  -- sign of the third coordinate is fixed by the orientation class
  obtain ⟨s, hs, he⟩ := hre
  have e1 : p ⬝ᵥ n = r 2 * (n ⬝ᵥ n) := by
    rw [hpu, w2_dot_add_left, w2_dot_smul_left, huperp, zero_add]
  have e2 : q ⬝ᵥ n = r' 2 * (n ⬝ᵥ n) := by
    rw [hqu, w2_dot_add_left, w2_dot_smul_left, huperp, zero_add]
  rw [e1, e2] at he
  have hc : r 2 = s * r' 2 := by
    refine mul_right_cancel₀ hnn.ne' ?_
    rw [he]; ring
  have hthird : r 2 = r' 2 := by
    by_cases hz : r' 2 = 0
    · rw [hz, mul_zero] at hc
      rw [hc, hz]
    · have hk := hsplit
      rw [hc] at hk
      have hkey : s * s * (r' 2 * r' 2) = r' 2 * r' 2 := by
        refine mul_right_cancel₀ hnn.ne' ?_
        calc (s * s * (r' 2 * r' 2)) * (n ⬝ᵥ n)
            = (s * r' 2) * (s * r' 2) * (n ⬝ᵥ n) := by ring
          _ = r' 2 * r' 2 * (n ⬝ᵥ n) := hk
          _ = (r' 2 * r' 2) * (n ⬝ᵥ n) := by ring
      have hprod : (s * s - 1) * (r' 2 * r' 2) = 0 := by
        linear_combination hkey
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have hs1 : s * s = 1 := by linarith
        rcases mul_self_eq_mul_self_iff.mp
          (show (s : ℝ) * s = 1 * 1 from by rw [hs1]; ring) with heq | heq
        · rw [heq, one_mul] at hc; exact hc
        · exact absurd heq (by linarith)
      · rcases mul_eq_zero.mp h1 with h3 | h3
        · exact absurd h3 hz
        · exact absurd h3 hz
  have ep : v3 = v0 + p := by rw [hpdef]; abel
  have eq' : v3' = v0 + q := by rw [hqdef]; abel
  rw [ep, eq', hpu, hqu, hthird]

/-! ## HOL `mk_simplex_uniq` (CUXVZOZ.hl:232) -/

/-- HOL `mk_simplex_uniq` (CUXVZOZ.hl:232): `mk_simplex1` returns its
non-coplanar completion target.  Port of the HOL argument: `PQCSXWG1`
supplies the three distances of the constructed point (whence the three
distance hypotheses of `simplex_unique`) and its positivity clause combined
with the hypothesis triple product fixes the orientation class (both triple
products are positive up to the cyclic identity, so `re_eqvl` witnesses the
ratio). -/
theorem mk_simplex_uniq_w2 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (hpos : (v1 - v0) ⬝ᵥ cross3 (v2 - v0) (v3 - v0) > 0) :
    mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) = v3 := by
  -- pairwise distinctness off non-coplanarity
  have hd01 : v0 ≠ v1 := fun he => hnc (w2_coplanar_of_pair_eq (a := v1) (b := v2)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  have hd02 : v0 ≠ v2 := fun he => hnc (w2_coplanar_of_pair_eq (a := v1) (b := v2)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  have hd03 : v0 ≠ v3 := fun he => hnc (w2_coplanar_of_pair_eq (a := v1) (b := v2)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  have hd12 : v1 ≠ v2 := fun he => hnc (w2_coplanar_of_pair_eq (a := v0) (b := v2)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  have hd13 : v1 ≠ v3 := fun he => hnc (w2_coplanar_of_pair_eq (a := v0) (b := v2)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  have hd23 : v2 ≠ v3 := fun he => hnc (w2_coplanar_of_pair_eq (a := v0) (b := v1)
    (c := v3) (by rw [he]; ext q; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff]; tauto))
  -- collinearity of three vertices makes the tetrahedron coplanar
  have hncol : ¬ Collinear ℝ ({v0, v1, v2} : Set V3) := by
    intro hcol
    apply hnc
    by_cases hv01 : v0 = v1
    · refine ⟨v0, v2, v3, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · rw [← hv01]; exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
    · refine ⟨v0, v1, v3, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
      · have hv2 : p ∈ line[ℝ, v0, v1] :=
          hcol.mem_affineSpan_of_mem_of_ne (p₁ := v0) (p₂ := v1)
            (by simp) (by simp) (by simp) hv01
        have hmono : affineSpan ℝ ({v0, v1} : Set V3) ≤
            affineSpan ℝ ({v0, v1, v3} : Set V3) :=
          affineSpan_mono ℝ (by
            intro q hq
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
            tauto)
        exact hmono hv2
      · exact mem_affineSpan ℝ (by simp)
  -- `PQCSXWG1` on the constructed point
  have hdelta : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [← delta_delta_x]
    exact (POS_EQ_NOT_COPLANANR v0 v1 v2 v3).2
      (fun hc => hnc (coplanar_eq_coplanar_alt.mpr hc))
  have hx1 : dist v0 v1 ^ 2 = dist v1 v0 ^ 2 := by rw [dist_comm]
  have hx2 : dist v0 v2 ^ 2 = dist v2 v0 ^ 2 := by rw [dist_comm]
  have hx6 : dist v1 v2 ^ 2 = dist v1 v2 ^ 2 := rfl
  obtain ⟨e0, e1, e2, hchi⟩ := PQCSXWG1_p11 v0 v1 v2
    (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2))
    (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2)
    (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)
    ⟨pow_pos (dist_pos.2 hd01) 2, pow_pos (dist_pos.2 hd02) 2,
      pow_pos (dist_pos.2 hd03) 2, pow_pos (dist_pos.2 hd23) 2,
      pow_pos (dist_pos.2 hd13) 2, pow_pos (dist_pos.2 hd12) 2, hncol,
      hx1, hx2, hx6, hdelta, rfl⟩
  have d0 : dist v0 v3 = dist v0 (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2)
      (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2)
      (dist v1 v2 ^ 2)) := by
    refine w2_sq_dist_eq e0 dist_nonneg dist_nonneg |>.trans ?_
    rw [dist_comm]
  have d1 : dist v1 v3 = dist v1 (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2)
      (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2)
      (dist v1 v2 ^ 2)) := by
    refine w2_sq_dist_eq e1 dist_nonneg dist_nonneg |>.trans ?_
    rw [dist_comm]
  have d2 : dist v2 v3 = dist v2 (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2)
      (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2)
      (dist v1 v2 ^ 2)) := by
    refine w2_sq_dist_eq e2 dist_nonneg dist_nonneg |>.trans ?_
    rw [dist_comm]
  -- orientation class: both triple products are positive (cyclic identity)
  have hQpos : 0 < (v1 - v0) ⬝ᵥ cross3 (v2 - v0)
      (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) - v0) := hchi
  have hre' : reEqvl ((v3 - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0))
      ((mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) - v0)
          ⬝ᵥ cross3 (v1 - v0) (v2 - v0)) := by
    have hposP : (0 : ℝ) < ((v3 - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0) : ℝ) := by
      rw [(w2_triple_cyclic (v1 - v0) (v2 - v0) (v3 - v0)).symm]
      exact hpos
    have hQposP : (0 : ℝ) < ((mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
        (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) - v0)
      ⬝ᵥ cross3 (v1 - v0) (v2 - v0) : ℝ) := by
      rw [(w2_triple_cyclic (v1 - v0) (v2 - v0)
        (mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
          (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) - v0)).symm]
      exact hQpos
    refine ⟨((v3 - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0) : ℝ)
        / ((mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
            (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) - v0)
          ⬝ᵥ cross3 (v1 - v0) (v2 - v0) : ℝ),
      div_pos hposP hQposP, ?_⟩
    rw [div_mul_cancel₀ _ (ne_of_gt hQposP)]
  exact (simplex_unique_w2 v0 v1 v2 v3 _ hncol d0 d1 d2 hre').symm

end Kepler.Text
