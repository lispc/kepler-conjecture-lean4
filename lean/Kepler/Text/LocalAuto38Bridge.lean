/-
LocalAuto38Bridge — clash-free re-host of the LocalAuto38 public 4-point
`DIHV_EQ_DIH_Y` bridge for the PackingAuto21 consumer (fill wave 2026-09-30,
LA38 wrapper lane -> GAMMAX_GAMMA2_X assembly).

WHY A BRIDGE MODULE: `PackingAuto21` cannot `import Kepler.Text.LocalAuto38`
outright — LA38's closure brings `Kepler.Text.LocalAuto1`, whose
`Kepler.Text.rho` (LocalAuto1.lean:180) collides with the homograph
`Kepler.Text.rho` of `Kepler.Text.IneqClosureDefs` (:752), which PA21 must
import.  This module's import closure (Kepler.Geom.LuneVolume, SphereKit,
TopologyFan, Mathlib) is a strict subset of PA21's environment (TopologyFan/
Fan/Hypermap arrive via PackingAuto18), so importing it is clash-free.

CONTENT: verbatim private twins of the LocalAuto38 apex-0 engine
(`p38_dihV_eq_dihY`, LocalAuto38 fill wave 2026-09-28) plus its supporting
kit and the 2026-09-30 public wrappers, renamed with the `_B` suffix:
- `DIHV_EQ_DIH_Y_4PT_B` = LocalAuto38 `DIHV_EQ_DIH_Y_4PT`
  (¬Collinear {v0,v1,v2} → ¬Collinear {v0,v1,v3} → dihV = dih_y);
- `DIHV_NN_4PT_B`       = LocalAuto38 `DIHV_NN_4PT` (nonneg companion);
- `DIH_Y_NN_B`          = LocalAuto38 `DIH_Y_NN` (terminal.hl:114);
- `DELTA_Y_POS_4POINTS_B` = LocalAuto38 `DELTA_Y_POS_4POINTS` (terminal.hl:537).
MERGE NOTE: delete this module and repoint PA21 at LocalAuto38 when the
LocalAuto1/IneqClosureDefs `rho` homograph is resolved tree-wide.

AXIOM-FACE (reconciliation lane 2026-10-08, `#print axioms` measured): the
four public `_B` theorems depend only on
`[propext, Classical.choice, Quot.sound]` — sorryAx-free, the same face as
the LocalAuto38 originals (`DIH_Y_NN`/`DELTA_Y_POS_4POINTS`/
`DIHV_EQ_DIH_Y_4PT`/`DIHV_NN_4PT` all measure the standard three).  This
module adds no axiom debt to PA21's closure.

RECONCILIATION (commit b24014d0 flags a "LA38Bridge 'PROVED' 注记与实测不符"
item): the "PROVED" wording is NOT carried by this file — it lives in
PackingAuto21's header note (:89-106, DEDUP/CLOSED 2026-09-30) and describes
the PA21 consumer `GAMMAX_GAMMA2_X`.  Measured: `GAMMAX_GAMMA2_X` is
statement-level proved (no literal `sorry` in its body) but axiom-face
tainted (`sorryAx`) via its PA21/PA14-side consumers — `MCELL2_SOL`/
`MCELL2_VOL`/`MCELL2_VOL_SPLIT_EXPLICIT`/`GAMMAX_MCELL2`/`MCELL2_DIHX`
(PA21) and `MCELL2_PERMUTE_01` (PA14:822): real proof bodies carrying
transitive taint; PA14's own header names the literal leaves
(`ynhyjit_p14` i=3, the `LEFT_ACTION_LIST_PROPERTIES` S₃ giant;
`QZKSYKG1`/`QZKSYKG2`).  The taint does NOT route through the `_B`
wrappers; softening the PA21 note is the PA21 lane's edit.
-/

import Kepler.Geom.LuneVolume
import Kepler.Text.SphereKit
import Kepler.Text.TopologyFan
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- verbatim twin: LocalAuto38 `half_pi_add_atn2_nn_p38` -/
private theorem half_pi_add_atn2_nn_p38 {x y : ℝ} (hx : 0 ≤ x) :
    (0 : ℝ) ≤ Real.pi / 2 + atn2 x y := by
  rw [atn2]
  split
  · have h := Real.neg_pi_div_two_lt_arctan (y / x)
    linarith
  split
  · have h := Real.arctan_lt_pi_div_two (x / y)
    linarith [Real.pi_pos, h]
  split
  · have hxy : x / y ≤ 0 := by
      refine div_nonpos_of_nonneg_of_nonpos hx ?_
      linarith
    have h1 : Real.arctan (x / y) ≤ 0 := Real.arctan_le_zero.mpr hxy
    linarith
  · have h := Real.pi_pos
    linarith

/-- copied: LocalAuto38:309 -/
theorem DIH_Y_NN_B :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      0 < y1 → 0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      0 ≤ dihY y1 y2 y3 y4 y5 y6 := by
  intro y1 y2 y3 y4 y5 y6 _ _
  show 0 ≤ Real.pi / 2 + atn2
      (Real.sqrt (4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3)
        (y4 * y4) (y5 * y5) (y6 * y6)))
      (-(deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)))
  exact half_pi_add_atn2_nn_p38 (Real.sqrt_nonneg _)

private theorem p38_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem p38_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem p38_coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

/-- Helper (2026-09-28): the cosine law — `2·(x⬝y)` from the squared
lengths. -/
private theorem p38_cos_law (x y : V3) :
    2 * (x ⬝ᵥ y) = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - dist x y * dist x y := by
  have h1 : dist x y * dist x y
      = ((x - y : V3) : Fin 3 → ℝ) ⬝ᵥ ((x - y : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two]
    exact norm_sq_eq_dot (x - y)
  have h2 : ‖x‖ * ‖x‖ = (x : Fin 3 → ℝ) ⬝ᵥ (x : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  have h3 : ‖y‖ * ‖y‖ = (y : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ) := by
    rw [← norm_sq_eq_dot, pow_two]
  rw [h1, h2, h3, p38_coe_sub]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm]
  ring

/-- Helper (2026-09-28): the analytic rendering `π/2 + atn2 s (−t) =
arccos (t / √(s²+t²))` on the nondegenerate half-plane `0 ≤ s`,
`0 < s² + t²`. -/
private theorem p38_atn2_arccos {s t : ℝ} (hs : 0 ≤ s) (hr : 0 < s ^ 2 + t ^ 2) :
    Real.pi / 2 + atn2 s (-t) = Real.arccos (t / Real.sqrt (s * s + t * t)) := by
  have hr0 : 0 < s * s + t * t := by
    have h9 : s * s = s ^ 2 := by ring
    have h10 : t * t = t ^ 2 := by ring
    rw [h9, h10]
    exact hr
  have hr' : Real.sqrt (s * s + t * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr0)
  rw [atn2]
  split
  · next h =>
    -- branch `|−t| < s`: atn2 = arctan (−t/s)
    have hs1 : 0 < s := by
      rcases abs_lt.mp h with ⟨h1, h2⟩
      have h9 : -t = -1 * t := by ring
      linarith
    have hden : Real.sqrt (1 + (-(t / s)) ^ 2) = Real.sqrt (s * s + t * t) / s := by
      have he : 1 + (-(t / s)) ^ 2 = (s * s + t * t) / (s * s) := by
        field_simp
      rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
        Real.sqrt_mul_self (le_of_lt hs1)]
    have hcos : t / Real.sqrt (s * s + t * t)
        = Real.cos (Real.pi / 2 + Real.arctan (-(t / s))) := by
      rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_arctan,
        hden]
      field_simp [show s ≠ 0 from ne_of_gt hs1, hr']
      ring
    rw [hcos, show -t / s = -(t / s) from by ring]
    exact (Real.arccos_cos
      (x := Real.pi / 2 + Real.arctan (-(t / s)))
      (by linarith [Real.neg_pi_div_two_lt_arctan (-(t / s))])
      (by linarith [Real.arctan_lt_pi_div_two (-(t / s))])).symm
  · next h1 =>
    split
    · next h2 =>
      -- branch `0 < −t`: atn2 = π/2 − arctan (s/(−t))
      have hyt : t < 0 := by
        have h9 : -t = -1 * t := by ring
        linarith
      have ht0 : (t : ℝ) ≠ 0 := ne_of_lt hyt
      have hden : Real.sqrt (1 + (s / -t) ^ 2) = Real.sqrt (s * s + t * t) / -t := by
        have he : 1 + (s / -t) ^ 2 = (s * s + t * t) / (t * t) := by
          rw [div_pow, show (-t) ^ 2 = t ^ 2 from by ring,
            eq_div_iff (mul_ne_zero ht0 ht0)]
          field_simp
          ring
        rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
          show (t * t) = t ^ 2 from by ring, Real.sqrt_sq_eq_abs, abs_of_neg hyt]
      have hcos : t / Real.sqrt (s * s + t * t)
          = Real.cos (Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t))) := by
        have eA : Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t))
            = Real.pi - Real.arctan (s / -t) := by ring
        rw [eA, Real.cos_pi_sub, Real.cos_arctan, hden]
        field_simp [ht0, hr']
      rw [hcos]
      have hA0 : 0 ≤ s / -t := div_nonneg hs (le_of_lt h2)
      exact (Real.arccos_cos
        (x := Real.pi / 2 + (Real.pi / 2 - Real.arctan (s / -t)))
        (by linarith [Real.arctan_nonneg.mpr hA0, Real.arctan_lt_pi_div_two (s / -t),
          Real.pi_pos])
        (by linarith [Real.arctan_nonneg.mpr hA0, Real.arctan_lt_pi_div_two (s / -t),
          Real.pi_pos])).symm
    · next h3 =>
      split
      · next h4 =>
        -- branch `−t < 0`: atn2 = −π/2 − arctan (s/(−t))
        have hyt : 0 < t := by
          have h9 : -t = -1 * t := by ring
          linarith
        have ht0 : (t : ℝ) ≠ 0 := ne_of_gt hyt
        have hden : Real.sqrt (1 + (s / -t) ^ 2) = Real.sqrt (s * s + t * t) / t := by
          have he : 1 + (s / -t) ^ 2 = (s * s + t * t) / (t * t) := by
            rw [div_pow, show (-t) ^ 2 = t ^ 2 from by ring,
              eq_div_iff (mul_ne_zero ht0 ht0)]
            field_simp
            ring
          rw [he, Real.sqrt_div (by positivity : (0:ℝ) ≤ s * s + t * t),
            show (t * t) = t ^ 2 from by ring, Real.sqrt_sq_eq_abs, abs_of_pos hyt]
        have hcos : t / Real.sqrt (s * s + t * t)
            = Real.cos (Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t))) := by
          have eA : Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t))
              = -(Real.arctan (s / -t)) := by ring
          rw [eA, Real.cos_neg, Real.cos_arctan, hden]
          field_simp [ht0, hr']
        rw [hcos]
        have hA0 : s / -t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hs (le_of_lt h4)
        have hA1 : Real.arctan (s / -t) ≤ 0 := by
          have h2x : 0 ≤ -(s / -t) := by linarith
          have h3x := Real.arctan_nonneg.mpr h2x
          rw [Real.arctan_neg] at h3x
          linarith
        exact (Real.arccos_cos
          (x := Real.pi / 2 + (-(Real.pi / 2) - Real.arctan (s / -t)))
          (by linarith)
          (by linarith [Real.neg_pi_div_two_lt_arctan (s / -t), Real.pi_pos])).symm
      · next h5 =>
        -- junk branch: `−t = 0` and `s = 0` contradict `0 < s² + t²`
        exfalso
        have h6 : -t = 0 := le_antisymm (not_lt.mp h3) (not_lt.mp h5)
        have ht0 : t = 0 := by
          have h9 : -t = -1 * t := by ring
          linarith
        have h7 : s = 0 := by
          have h8 : ¬ (0 < s) := fun hc => h1 (by simpa [h6] using hc)
          linarith
        rw [h7, ht0] at hr0
        norm_num at hr0
/-- Helper (2026-09-28): `ups_x` in Gram form from `2p = a + b − f`. -/
private theorem p38_upsX_gram (a b f p : ℝ) (h : 2 * p = a + b - f) :
    upsX a b f = 4 * (a * b - p * p) := by
  simp only [upsX]
  linear_combination (2 * p + a + b - f) * h

/-- Helper (2026-09-28): `delta_x4` is `4·(a·r̃ − p̃·q̃)` in Gram form. -/
private theorem p38_deltaX4_gram (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    deltaX4 a b c d e f = 4 * (a * r - p * q) := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX4]
  ring

/-- Helper (2026-09-28): `4·x1·delta_x + delta_x4² =
ups_x(x1,x2,x6)·ups_x(x1,x3,x5)`. -/
private theorem p38_ups_delta (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2 =
      upsX a b f * upsX a c e := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX, deltaX4, upsX]
  ring

/-- Helper (proved here 2026-09-28): the Gram-form of `delta_x` with the
Gram entries given directly (`2p = a+b−f`, `2q = a+c−e`, `2r = b+c−d`). -/
private theorem p38_deltaX_gram_aux (a b c d e f p q r : ℝ)
    (hp : 2 * p = a + b - f) (hq : 2 * q = a + c - e) (hr : 2 * r = b + c - d) :
    deltaX a b c d e f =
      4 * (a * (b * c - r ^ 2) - p * (p * c - q * r) + q * (p * r - b * q)) := by
  have hd : d = b + c - 2 * r := by linarith
  have he : e = a + c - 2 * q := by linarith
  have hf : f = a + b - 2 * p := by linarith
  subst hd; subst he; subst hf
  simp only [deltaX]
  ring

/-- Helper (proved here 2026-09-28): the Gram determinant of three vectors
equals the determinant of the matrix with those rows, squared — hence
nonnegative. -/
private theorem p38_det_gram_eq (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w))
      = Matrix.det
          (Matrix.of fun i j =>
            (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
              (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j) := by
  rw [Matrix.det_fin_three]
  simp [dotProduct, Matrix.of_apply, mul_comm]
  ring

private theorem p38_det_gram_nn (u v w : Fin 3 → ℝ) :
    0 ≤ u ⬝ᵥ u * (v ⬝ᵥ v * w ⬝ᵥ w - (v ⬝ᵥ w) ^ 2)
      - (u ⬝ᵥ v) * ((u ⬝ᵥ v) * w ⬝ᵥ w - (u ⬝ᵥ w) * (v ⬝ᵥ w))
      + (u ⬝ᵥ w) * ((u ⬝ᵥ v) * (v ⬝ᵥ w) - v ⬝ᵥ v * (u ⬝ᵥ w)) := by
  have hdet := p38_det_gram_eq u v w
  have hGM : (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i ⬝ᵥ
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j)
      = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) *
        (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i) := by
    ext i j
    simp [Matrix.mul_apply, dotProduct, Matrix.of_apply]
  have hdMt : Matrix.det (Matrix.of fun i j =>
      (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
      = Matrix.det (Matrix.of fun i j =>
        (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) := by
    rw [← show Matrix.transpose (Matrix.of fun i j =>
          (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) j i)
        = (Matrix.of fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j) from rfl,
      Matrix.det_transpose]
  rw [hdet, hGM, Matrix.det_mul, hdMt]
  linarith [sq_nonneg (Matrix.det (Matrix.of fun i j =>
    (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j)), pow_two (Matrix.det (Matrix.of
    fun i j => (![u, v, w] : Fin 3 → (Fin 3 → ℝ)) i j))]

/-- Helper (2026-09-28): Cayley–Menger nonnegativity for a tetrahedron with
apex `0` — the `DELTA_Y_POS_4POINTS` content (that theorem now cites this
lemma; the copy here is needed because `tau3_taum` precedes it). -/

private theorem p38_deltaY_pos_4 (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) := by
  have hA : dist v0 v1 * dist v0 v1
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v1 - v0)
  have hB : dist v0 v2 * dist v0 v2
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v2 - v0)
  have hC : dist v0 v3 * dist v0 v3
      = ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) := by
    rw [dist_eq_norm, ← pow_two, norm_sub_rev]
    exact norm_sq_eq_dot (v3 - v0)
  have hP : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v2 * dist v1 v2 := by
    have hc := p38_cos_law (v1 - v0) (v2 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hB] at hc
    rw [show dist v1 v2 = dist (v1 - v0) (v2 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hQ : 2 * (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v1 v3 * dist v1 v3 := by
    have hc := p38_cos_law (v1 - v0) (v3 - v0)
    rw [show ‖(v1 - v0 : V3)‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hA, hC] at hc
    rw [show dist v1 v3 = dist (v1 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  have hR : 2 * (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      = ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ)
        + ((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
        - dist v2 v3 * dist v2 v3 := by
    have hc := p38_cos_law (v2 - v0) (v3 - v0)
    rw [show ‖(v2 - v0 : V3)‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev],
      show ‖(v3 - v0 : V3)‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev]] at hc
    rw [hB, hC] at hc
    rw [show dist v2 v3 = dist (v2 - v0) (v3 - v0) from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]
    exact hc
  rw [deltaY, hA, hB, hC,
    p38_deltaX_gram_aux
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v1 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v3 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (dist v2 v3 * dist v2 v3) (dist v1 v3 * dist v1 v3)
      (dist v1 v2 * dist v1 v2)
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v2 - v0 : V3) : Fin 3 → ℝ))
      (((v1 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      (((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ))
      hP hQ hR]
  linarith [p38_det_gram_nn ((v1 - v0 : V3) : Fin 3 → ℝ)
    ((v2 - v0 : V3) : Fin 3 → ℝ) ((v3 - v0 : V3) : Fin 3 → ℝ)]

/-- The `DIHV_EQ_DIH_Y` bridge (2026-09-28): at a tetrahedron with apex `0`,
the geometric dihedral `dihV 0 w1 w2 w3` equals the analytic `dih_y` of the
squared-length box — both angles have cosine
`deltaX4 x / √(4·x1·deltaX x + deltaX4 x²)`.  `hΔy` is the Cayley–Menger
nonnegativity (`p38_deltaY_pos_4`). -/
private theorem p38_dihV_eq_dihY (w1 w2 w3 : V3)
    (hw1 : 0 < ‖w1‖)
    (hΔy : 0 ≤ deltaY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2))
    (hu2 : 0 < upsX (‖w1‖ * ‖w1‖) (‖w2‖ * ‖w2‖) (dist w1 w2 * dist w1 w2))
    (hu3 : 0 < upsX (‖w1‖ * ‖w1‖) (‖w3‖ * ‖w3‖) (dist w1 w3 * dist w1 w3)) :
    dihV 0 w1 w2 w3 =
      dihY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2) := by
  set a : ℝ := ‖w1‖ * ‖w1‖ with ha
  set b : ℝ := ‖w2‖ * ‖w2‖ with hb
  set c : ℝ := ‖w3‖ * ‖w3‖ with hc
  set d : ℝ := dist w2 w3 * dist w2 w3 with hd
  set e : ℝ := dist w1 w3 * dist w1 w3 with he
  set f : ℝ := dist w1 w2 * dist w1 w2 with hf
  set p : ℝ := w1 ⬝ᵥ w2 with hp
  set q : ℝ := w1 ⬝ᵥ w3 with hq
  set r : ℝ := w2 ⬝ᵥ w3 with hr
  have gA : a = w1 ⬝ᵥ w1 := by rw [ha, ← norm_sq_eq_dot, pow_two]
  have gB : b = w2 ⬝ᵥ w2 := by rw [hb, ← norm_sq_eq_dot, pow_two]
  have gC : c = w3 ⬝ᵥ w3 := by rw [hc, ← norm_sq_eq_dot, pow_two]
  have hP' : 2 * p = a + b - f := p38_cos_law w1 w2
  have hQ' : 2 * q = a + c - e := p38_cos_law w1 w3
  have hR' : 2 * r = b + c - d := p38_cos_law w2 w3
  have hU2 : upsX a b f = 4 * (a * b - p * p) := p38_upsX_gram a b f p hP'
  have hU3 : upsX a c e = 4 * (a * c - q * q) := p38_upsX_gram a c e q hQ'
  have hD4 : deltaX4 a b c d e f = 4 * (a * r - p * q) :=
    p38_deltaX4_gram a b c d e f p q r hP' hQ' hR'
  have hUD : 4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2
      = upsX a b f * upsX a c e := p38_ups_delta a b c d e f p q r hP' hQ' hR'
  have hap : (0:ℝ) < a := by positivity
  have hΔx : deltaX a b c d e f
      = deltaY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2) := by
    rw [deltaY, ← ha, ← hb, ← hc, ← hd, ← he, ← hf]
  have hΔ0 : 0 ≤ 4 * a * deltaX a b c d e f := by
    have h1x : 0 ≤ deltaX a b c d e f := by rw [hΔx]; exact hΔy
    exact mul_nonneg (by positivity) h1x
  have hden : 0 < 4 * a * deltaX a b c d e f + deltaX4 a b c d e f ^ 2 := by
    rw [hUD]; exact mul_pos hu2 hu3
  have hdihY : dihY ‖w1‖ ‖w2‖ ‖w3‖ (dist w2 w3) (dist w1 w3) (dist w1 w2)
      = Real.pi / 2 + atn2 (Real.sqrt (4 * a * deltaX a b c d e f))
          (-(deltaX4 a b c d e f)) := by
    rw [dihY, show ‖w1‖ * ‖w1‖ = a from ha.symm, show ‖w2‖ * ‖w2‖ = b from hb.symm,
      show ‖w3‖ * ‖w3‖ = c from hc.symm,
      show dist w2 w3 * dist w2 w3 = d from hd.symm,
      show dist w1 w3 * dist w1 w3 = e from he.symm,
      show dist w1 w2 * dist w1 w2 = f from hf.symm, dihXf]
  have hdihv0 : dihV 0 w1 w2 w3
      = arcV 0 (a • w2 - p • w1) (a • w3 - q • w1) := by
    unfold dihV
    dsimp only
    simp only [sub_zero]
    rw [dotProduct_comm w2 w1, dotProduct_comm w3 w1, ← gA, ← hp, ← hq]
  have harc : arcV 0 (a • w2 - p • w1) (a • w3 - q • w1)
      = Real.arccos (((a • w2 - p • w1 : V3) ⬝ᵥ (a • w3 - q • w1))
        / (dist (a • w2 - p • w1) (0:V3) * dist (a • w3 - q • w1) (0:V3))) := by
    rw [arcV]
    simp only [p38_coe_zero, p38_coe_sub, p38_coe_smul, sub_zero, dist_zero_right]
  have hnum : ((a • w2 - p • w1 : V3) ⬝ᵥ (a • w3 - q • w1)) = a * (a * r - p * q) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w2 w1, ← gA, ← hp, ← hq, ← hr]
    ring
  have hab1 : 0 < a * b - p * p := by linarith
  have hab2 : 0 < a * c - q * q := by linarith
  have hnn2 : ((a • w2 - p • w1 : V3) ⬝ᵥ (a • w2 - p • w1)) = a * (a * b - p * p) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w2 w1, ← gA, ← hp, ← gB]
    ring
  have hnn3 : ((a • w3 - q • w1 : V3) ⬝ᵥ (a • w3 - q • w1)) = a * (a * c - q * q) := by
    simp only [p38_coe_sub, p38_coe_smul]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_comm w3 w1, ← gA, ← hq, ← gC]
    ring
  have hdist2 : dist (a • w2 - p • w1) (0:V3) = Real.sqrt (a * (a * b - p * p)) := by
    rw [dist_zero_right, ← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_dot]
    exact congrArg Real.sqrt hnn2
  have hdist3 : dist (a • w3 - q • w1) (0:V3) = Real.sqrt (a * (a * c - q * q)) := by
    rw [dist_zero_right, ← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_dot]
    exact congrArg Real.sqrt hnn3
  have hden' : dist (a • w2 - p • w1) (0:V3) * dist (a • w3 - q • w1) (0:V3)
      = a * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
    rw [hdist2, hdist3]
    calc Real.sqrt (a * (a * b - p * p)) * Real.sqrt (a * (a * c - q * q))
        = Real.sqrt ((a * (a * b - p * p)) * (a * (a * c - q * q))) :=
          (Real.sqrt_mul (by positivity : (0:ℝ) ≤ a * (a * b - p * p)) _).symm
      _ = Real.sqrt ((a * a) * ((a * b - p * p) * (a * c - q * q))) := by
          rw [show (a * (a * b - p * p)) * (a * (a * c - q * q))
            = (a * a) * ((a * b - p * p) * (a * c - q * q)) from by ring]
      _ = a * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
          rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ a * a),
            Real.sqrt_mul_self (le_of_lt hap)]
  have harg : (a * (a * r - p * q)) / (a * Real.sqrt ((a * b - p * p) * (a * c - q * q)))
      = deltaX4 a b c d e f / Real.sqrt (4 * a * deltaX a b c d e f
        + deltaX4 a b c d e f ^ 2) := by
    rw [hUD, hD4, hU2, hU3]
    have hsq16 : Real.sqrt ((4:ℝ) * (a * b - p * p) * (4 * (a * c - q * q)))
        = 4 * Real.sqrt ((a * b - p * p) * (a * c - q * q)) := by
      rw [show (4:ℝ) * (a * b - p * p) * (4 * (a * c - q * q))
            = 16 * ((a * b - p * p) * (a * c - q * q)) from by ring,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 16)]
      have h16 : Real.sqrt 16 = 4 := by norm_num
      rw [h16]
    rw [hsq16]
    have hane : a ≠ 0 := ne_of_gt hap
    have hzne : Real.sqrt ((a * b - p * p) * (a * c - q * q)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (mul_pos hab1 hab2))
    field_simp [hane, hzne]
  rw [hdihv0, harc, hnum, hden', harg, hdihY]
  have hdens : 0 < (Real.sqrt (4 * a * deltaX a b c d e f)) ^ 2
      + deltaX4 a b c d e f ^ 2 := by
    rw [Real.sq_sqrt hΔ0]
    exact hden
  have hz := p38_atn2_arccos (s := Real.sqrt (4 * a * deltaX a b c d e f))
    (t := deltaX4 a b c d e f) (Real.sqrt_nonneg _) hdens
  rw [show Real.sqrt (4 * a * deltaX a b c d e f)
        * Real.sqrt (4 * a * deltaX a b c d e f)
      = (Real.sqrt (4 * a * deltaX a b c d e f)) ^ 2 from by ring,
    show deltaX4 a b c d e f * deltaX4 a b c d e f
      = deltaX4 a b c d e f ^ 2 from by ring,
    Real.sq_sqrt hΔ0] at hz
  exact hz.symm
/-- HOL `DELTA_Y_POS_4POINTS` (terminal.hl:537). DISCHARGED 2026-09-28:
`delta_y` is 4× the Gram determinant of the three edge vectors `v1 − v0`,
`v2 − v0`, `v3 − v0` (via `p38_deltaX_gram`), the cross terms come from
`‖x − y‖²` dot expansions, and the Gram determinant equals
`det M · det Mᵀ = det M² ≥ 0` (`p38_det_gram_nn`). -/
theorem DELTA_Y_POS_4POINTS_B (v0 v1 v2 v3 : V3) :
    0 ≤ deltaY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
      (dist v1 v3) (dist v1 v2) :=
  p38_deltaY_pos_4 v0 v1 v2 v3

/-! ### The public 4-point `DIHV_EQ_DIH_Y` bridge (fill wave 2026-09-30)

The apex-0 engine `p38_dihV_eq_dihY` is private; the PA21 lane
(`PackingAuto21.GAMMAX_GAMMA2_X`, the TSKAJXY3.hl:2070 assembly) consumes the
bridge in general position.  The two `¬Collinear` premises feed the matching
`0 < ups_x` factors of the engine through the Gram/Lagrange identity — the
`LocalAuto17.lean:183 upsX_pos_of_noncollinear_p17` route (`cross3`-free
re-derivation: the Gram bracket `‖v1‖²‖v2‖² − (v1·v2)²` vanishes exactly in
the Cauchy–Schwarz equality case, i.e. collinearity). -/

/-- Helper (2026-09-30, the LocalAuto17:183 `upsX_pos_of_noncollinear_p17`
twin re-mirrored on this import lane): the Gram determinant `ups_x` of an
origin-apex pair is positive as soon as the pair is non-collinear at the
origin — `ups_x = 4·(‖v1‖²‖v2‖² − (v1·v2)²)` (`p38_cos_law` + `p38_upsX_gram`),
and the bracket is forced positive by the Cauchy–Schwarz equality case. -/
private theorem p38_upsX_pos_noncollinear {v1 v2 : V3}
    (hnc : ¬ Collinear ℝ ({(0:V3), v1, v2} : Set V3)) :
    0 < upsX (‖v1‖ * ‖v1‖) (‖v2‖ * ‖v2‖) (dist v1 v2 * dist v1 v2) := by
  have hv1 : v1 ≠ 0 := by
    intro h; subst h
    exact hnc (by simpa using collinear_pair ℝ (0:V3) v2)
  have hgram : 0 < (‖v1‖ * ‖v1‖) * (‖v2‖ * ‖v2‖) - (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) := by
    by_contra hle
    have hAB : (‖v1‖ * ‖v1‖) * (‖v2‖ * ‖v2‖) ≤ (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) :=
      by linarith [not_lt.mp hle]
    have hcs : |v1 ⬝ᵥ v2| ≤ ‖v1‖ * ‖v2‖ := by
      rw [← inner_eq_dot]
      exact abs_real_inner_le_norm (x := v1) (y := v2)
    have hBA : (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2) ≤ (‖v1‖ * ‖v1‖) * (‖v2‖ * ‖v2‖) := by
      calc (v1 ⬝ᵥ v2) * (v1 ⬝ᵥ v2)
          = |v1 ⬝ᵥ v2| * |v1 ⬝ᵥ v2| := (abs_mul_abs_self _).symm
        _ ≤ (‖v1‖ * ‖v2‖) * (‖v1‖ * ‖v2‖) := by
            nlinarith [hcs, abs_nonneg (v1 ⬝ᵥ v2),
              mul_nonneg (norm_nonneg v1) (norm_nonneg v2)]
        _ = (‖v1‖ * ‖v1‖) * (‖v2‖ * ‖v2‖) := by ring
    have hsqm : (‖v1‖ * ‖v2‖) * (‖v1‖ * ‖v2‖)
        = (‖v1‖ * ‖v1‖) * (‖v2‖ * ‖v2‖) := by ring
    have habs : |v1 ⬝ᵥ v2| = ‖v1‖ * ‖v2‖ := by
      refine (mul_self_inj_of_nonneg (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
      rw [abs_mul_abs_self, hsqm]
      linarith
    have hinner : ‖inner ℝ v1 v2‖ = ‖v1‖ * ‖v2‖ := by
      rw [inner_eq_dot, Real.norm_eq_abs]; exact habs
    rcases ((norm_inner_eq_norm_tfae ℝ v1 v2).out 0 2).mp hinner with h0 | ⟨c, hc⟩
    · exact hv1 h0
    · exact hnc (collinear3_iff_smul (v := (0:V3)) (w := v1) (w1 := v2) hv1 |>.mpr
        ⟨c, by simpa using hc⟩)
  rw [p38_upsX_gram (‖v1‖ * ‖v1‖) (‖v2‖ * ‖v2‖) (dist v1 v2 * dist v1 v2)
    (v1 ⬝ᵥ v2) (p38_cos_law v1 v2)]
  linarith

/-- Helper (2026-09-30): `dihV` is translation invariant — the general
tetrahedron reduces to the apex-0 form of `p38_dihV_eq_dihY`. -/
private theorem p38_dihV_sub (v0 v1 v2 v3 : V3) :
    dihV v0 v1 v2 v3 = dihV 0 (v1 - v0) (v2 - v0) (v3 - v0) := by
  unfold dihV
  dsimp only
  simp only [sub_zero]

/-- Helper (2026-09-30): collinearity survives translation — the direction
the 4-point bridge needs (apex-0 triple back to general position). -/
private theorem p38_collinear_sub {v0 v1 v2 : V3}
    (h : Collinear ℝ ({(0:V3), v1 - v0, v2 - v0} : Set V3)) :
    Collinear ℝ ({v0, v1, v2} : Set V3) := by
  rw [collinear_iff_of_mem
    (show (v1 - v0 : V3) ∈ ({(0:V3), v1 - v0, v2 - v0} : Set V3) from by simp)] at h
  obtain ⟨v, hv⟩ := h
  rw [collinear_iff_of_mem (show v1 ∈ ({v0, v1, v2} : Set V3) from by simp)]
  refine ⟨v, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp
  · obtain ⟨r, hr⟩ := hv (0:V3) (by simp)
    refine ⟨r, ?_⟩
    rw [hp]
    show v0 = r • v + v1
    have hr' : (0:V3) = r • v + (v1 - v0) := hr
    linear_combination (norm := module) hr'
  · exact ⟨0, by rw [hp]; simp⟩
  · obtain ⟨r, hr⟩ := hv (v2 - v0) (by simp)
    refine ⟨r, ?_⟩
    rw [hp]
    show v2 = r • v + v1
    have hr' : (v2 - v0 : V3) = r • v + (v1 - v0) := hr
    linear_combination (norm := module) hr'

/-- HOL `DIHV_EQ_DIH_Y` bridge, public 4-point form (2026-09-30; consumer:
PackingAuto21 `GAMMAX_GAMMA2_X`, TSKAJXY3.hl:2070).  At a tetrahedron the
geometric dihedral `dihV v0 v1 v2 v3` equals the analytic `dih_y` of the
squared-length box — both angles have cosine
`deltaX4 x / √(4·x1·deltaX x + deltaX4 x²)`; each `¬Collinear` premise feeds
the matching `0 < ups_x` factor through `p38_upsX_pos_noncollinear`. -/
theorem DIHV_EQ_DIH_Y_4PT_B (v0 v1 v2 v3 : V3)
    (h2 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (h3 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3)) :
    dihV v0 v1 v2 v3 =
      dihY (dist v0 v1) (dist v0 v2) (dist v0 v3) (dist v2 v3)
        (dist v1 v3) (dist v1 v2) := by
  have hnc2 : ¬ Collinear ℝ ({(0:V3), v1 - v0, v2 - v0} : Set V3) :=
    fun hc => h2 (p38_collinear_sub hc)
  have hnc3 : ¬ Collinear ℝ ({(0:V3), v1 - v0, v3 - v0} : Set V3) :=
    fun hc => h3 (p38_collinear_sub hc)
  have hw1 : 0 < ‖v1 - v0‖ := by
    refine norm_pos_iff.mpr fun h0 => h2 ?_
    rw [show v1 = v0 from sub_eq_zero.mp h0]
    exact (by simpa using collinear_pair ℝ v0 v2 :
      Collinear ℝ ({v0, v0, v2} : Set V3))
  rw [p38_dihV_sub v0 v1 v2 v3,
    p38_dihV_eq_dihY (v1 - v0) (v2 - v0) (v3 - v0) hw1
      (by
        have h := p38_deltaY_pos_4 (0:V3) (v1 - v0) (v2 - v0) (v3 - v0)
        rwa [dist_zero_left, dist_zero_left, dist_zero_left] at h)
      (p38_upsX_pos_noncollinear hnc2) (p38_upsX_pos_noncollinear hnc3)]
  rw [show ‖v1 - v0‖ = dist v0 v1 from by rw [dist_eq_norm, norm_sub_rev],
    show ‖v2 - v0‖ = dist v0 v2 from by rw [dist_eq_norm, norm_sub_rev],
    show ‖v3 - v0‖ = dist v0 v3 from by rw [dist_eq_norm, norm_sub_rev],
    show dist (v2 - v0) (v3 - v0) = dist v2 v3 from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right],
    show dist (v1 - v0) (v3 - v0) = dist v1 v3 from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right],
    show dist (v1 - v0) (v2 - v0) = dist v1 v2 from by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]]

/-- The 4-point nonnegativity companion (2026-09-30): the geometric `dihV`
is nonnegative at a proper tetrahedron — the bridge `DIHV_EQ_DIH_Y_4PT`
plus `DIH_Y_NN` over the Cayley–Menger `DELTA_Y_POS_4POINTS`. -/
theorem DIHV_NN_4PT_B (v0 v1 v2 v3 : V3)
    (h2 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (h3 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3)) :
    0 ≤ dihV v0 v1 v2 v3 := by
  rw [DIHV_EQ_DIH_Y_4PT_B v0 v1 v2 v3 h2 h3]
  refine DIH_Y_NN_B _ _ _ _ _ _ (dist_pos.mpr fun h0 => h2 ?_)
    (DELTA_Y_POS_4POINTS_B v0 v1 v2 v3)
  rw [show v0 = v1 from h0]
  exact (by simpa using collinear_pair ℝ v1 v2 :
    Collinear ℝ ({v1, v1, v2} : Set V3))

end Kepler.Text
