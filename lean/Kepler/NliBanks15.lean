/-
Kepler.NliBanks15 — lane `nli-t1-gxsa`.

Closes `Kepler.Assembly.nliTskGXSA` (`bank_TSKAJXYGXSA`, PackingAuto21:268 /
Assembly:913) with **no** new `axiom`/`sorry` and **no** change of statement.

Method (derivative-free interval certificate; the six `HasDerivAt` families of
the `xspace-deriv-kit` turned out to be unnecessary):

* `deltaX` is monotone along each of the six axes on the bank box, with the
  six `ring` factorizations `Δ(xᵢ) - Δ(c) = ±(xᵢ-c)·Sᵢ` and
  `Sᵢ ≥ 57` (each `Sᵢ` is `slot·(linear) + (bounded diff)·(bounded diff)`).
  Hence the **exact rational** box bounds
  `0 ≤ deltaX ≤ 29.52807424 = 11534404/390625`;
* `a = eulerA_x` (`≥ 26.799` on all four `solEuler` slots);
* `deltaX4 ∈ [58.9, 66.57]` on all four `ldih` slots (natural interval);
* `lfun (√x/2) ≥ 0.9807`, `√(4x) ≥ 4` on the `ldih` first coordinates;
* `matan` brackets are `nb10_matan_le_one` (`≤ 1`) and `nb10_matan_ge`
  (`1 - t/3 ≤ ·`), both already in `Kepler.NliBanks10`;
* final: `1/12 - A·Σsol + B·Σldih ≥ 1/12 - 0.6443107122·4/26.799
  + 0.0647174928·4·0.0562256 = 1.7191e-3 > 0`.

`A = 2·mm1/π`, `B = 8·mm2/π` are bracketed by `g4v_AB_bounds`
(`Gamma4ValCornerKit`). No bank is weakened; the disjunction's second branch is
never used.
-/
import Kepler.NliBanks10

namespace Kepler.NliBanks15
open Kepler.Text

set_option maxHeartbeats 4000000

/-! ## 1. `deltaX`: six-axis monotonicity (corner walk) -/

theorem nb15_mul_ge_neg {a b w : ℝ} (ha : a ≤ w) (ha' : -w ≤ a) (hb : b ≤ w) (hb' : -w ≤ b) :
    -(w ^ 2) ≤ a * b := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ w + a) (by linarith : (0:ℝ) ≤ w + b),
    mul_nonneg (by linarith : (0:ℝ) ≤ w - a) (by linarith : (0:ℝ) ≤ w - b), sq_nonneg w]

/-- `a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a*c ≤ b*d` (two-sided product bound). -/
theorem nb15_mulm {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ a) (h4 : 0 ≤ c) :
    a * c ≤ b * d :=
  mul_le_mul h1 h2 h4 (le_trans h3 h1)

/-- `2 ≤ s`, `7.7999 ≤ t` give `7.7999 ≤ s*t/2`. -/
theorem nb15_two_mul_le {s t : ℝ} (hs : 2 ≤ s) (ht : (7.7999:ℝ) ≤ t) :
    (7.7999:ℝ) ≤ s * t / 2 := by
  have h : (2:ℝ) * 7.7999 ≤ s * t :=
    mul_le_mul hs ht (by norm_num) (by linarith : (0:ℝ) ≤ s)
  linarith

theorem nb15_walk_x1 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (hlo : (7.84:ℝ) ≤ x1) (hhi : x1 ≤ c) (hc : c ≤ 8)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401) (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8) (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX c x2 x3 x4 x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX c x2 x3 x4 x5 x6
      = -(x1 - c) * (x4 * (x1 - x2 - x3 + x4 - x5 - x6 + c) + (x2 - x3) * (x6 - x5)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 - x2 - x3 + x4 - x5 - x6 + c := by linarith
  have hP : (-(0.01):ℝ) ≤ (x2 - x3) * (x6 - x5) := by
    have h := nb15_mul_ge_neg (w := 0.1) (by linarith : x2 - x3 ≤ 0.1)
      (by linarith : -(0.1:ℝ) ≤ x2 - x3) (by linarith : x6 - x5 ≤ 0.1)
      (by linarith : -(0.1:ℝ) ≤ x6 - x5)
    norm_num at h ⊢; linarith
  have hS : (0:ℝ) ≤ x4 * (x1 - x2 - x3 + x4 - x5 - x6 + c) + (x2 - x3) * (x6 - x5) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x4) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ -(x1 - c)) hS]

theorem nb15_walk_x4 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401) (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (hlo : (7.84:ℝ) ≤ x4) (hhi : x4 ≤ c) (hc : c ≤ 8)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401) (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 x2 x3 c x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX x1 x2 x3 c x5 x6
      = -(x4 - c) * (x1 * (x1 - x2 - x3 + x4 - x5 - x6 + c) + (x2 - x6) * (x3 - x5)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 - x2 - x3 + x4 - x5 - x6 + c := by linarith
  have hP : (-(0.01):ℝ) ≤ (x2 - x6) * (x3 - x5) := by
    have h := nb15_mul_ge_neg (w := 0.1) (by linarith : x2 - x6 ≤ 0.1)
      (by linarith : -(0.1:ℝ) ≤ x2 - x6) (by linarith : x3 - x5 ≤ 0.1)
      (by linarith : -(0.1:ℝ) ≤ x3 - x5)
    norm_num at h ⊢; linarith
  have hS : (0:ℝ) ≤ x1 * (x1 - x2 - x3 + x4 - x5 - x6 + c) + (x2 - x6) * (x3 - x5) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x1) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ -(x4 - c)) hS]

theorem nb15_walk_x2 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8)
    (hlo : 4 ≤ c) (hhi : c ≤ x2) (h2' : x2 ≤ 4.0401)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8) (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 c x3 x4 x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX x1 c x3 x4 x5 x6
      = (x2 - c) * (x5 * (x1 - x2 + x3 + x4 - x5 + x6 - c) + (x1 - x3) * (x4 - x6)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 - x2 + x3 + x4 - x5 + x6 - c := by linarith
  have hP : (0:ℝ) ≤ (x1 - x3) * (x4 - x6) := mul_nonneg (by linarith) (by linarith)
  have hS : (0:ℝ) ≤ x5 * (x1 - x2 + x3 + x4 - x5 + x6 - c) + (x1 - x3) * (x4 - x6) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x5) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ x2 - c) hS]

theorem nb15_walk_x3 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401)
    (hlo : 4 ≤ c) (hhi : c ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8) (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 x2 c x4 x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX x1 x2 c x4 x5 x6
      = (x3 - c) * (x6 * (x1 + x2 - x3 + x4 + x5 - x6 - c) + (x1 - x2) * (x4 - x5)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 + x2 - x3 + x4 + x5 - x6 - c := by linarith
  have hP : (0:ℝ) ≤ (x1 - x2) * (x4 - x5) := mul_nonneg (by linarith) (by linarith)
  have hS : (0:ℝ) ≤ x6 * (x1 + x2 - x3 + x4 + x5 - x6 - c) + (x1 - x2) * (x4 - x5) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x6) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ x3 - c) hS]

theorem nb15_walk_x5 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401) (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8)
    (hlo : 4 ≤ c) (hhi : c ≤ x5) (h5' : x5 ≤ 4.0401)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 x2 x3 x4 c x6 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX x1 x2 x3 x4 c x6
      = (x5 - c) * (x2 * (x1 - x2 + x3 + x4 - x5 + x6 - c) + (x1 - x6) * (x4 - x3)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 - x2 + x3 + x4 - x5 + x6 - c := by linarith
  have hP : (0:ℝ) ≤ (x1 - x6) * (x4 - x3) := mul_nonneg (by linarith) (by linarith)
  have hS : (0:ℝ) ≤ x2 * (x1 - x2 + x3 + x4 - x5 + x6 - c) + (x1 - x6) * (x4 - x3) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x2) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ x5 - c) hS]

theorem nb15_walk_x6 {x1 x2 x3 x4 x5 x6 c : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8)
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401) (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8) (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401)
    (hlo : 4 ≤ c) (hhi : c ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 x2 x3 x4 x5 c ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : deltaX x1 x2 x3 x4 x5 x6 - deltaX x1 x2 x3 x4 x5 c
      = (x6 - c) * (x3 * (x1 + x2 - x3 + x4 + x5 - x6 - c) + (x4 - x2) * (x1 - x5)) := by
    unfold deltaX; ring
  have hL : (0:ℝ) ≤ x1 + x2 - x3 + x4 + x5 - x6 - c := by linarith
  have hP : (0:ℝ) ≤ (x4 - x2) * (x1 - x5) := mul_nonneg (by linarith) (by linarith)
  have hS : (0:ℝ) ≤ x3 * (x1 + x2 - x3 + x4 + x5 - x6 - c) + (x4 - x2) * (x1 - x5) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x3) hL, hP]
  nlinarith [hid, mul_nonneg (by linarith : (0:ℝ) ≤ x6 - c) hS]

/-! ## 2. `deltaX` box bounds (exact rational corners) -/

theorem nb15_deltaX_corner_lo : deltaX 8 4 4 8 4 4 = 0 := by norm_num [deltaX]

theorem nb15_deltaX_corner_hi :
    deltaX 7.84 4.0401 4.0401 7.84 4.0401 4.0401 = 29.52807424 := by
  norm_num [deltaX]

/-- `0 ≤ deltaX` on the bank box. -/
theorem nb15_deltaX_lo {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8) (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401) (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401) (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    (0:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have hA : deltaX 8 x2 x3 x4 x5 x6 ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    nb15_walk_x1 h1 h1' (by norm_num) h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hB : deltaX 8 x2 x3 8 x5 x6 ≤ deltaX 8 x2 x3 x4 x5 x6 :=
    nb15_walk_x4 (by norm_num) (by norm_num) h2 h2' h3 h3' h4 h4' (by norm_num) h5 h5' h6 h6'
  have hC : deltaX 8 4 x3 8 x5 x6 ≤ deltaX 8 x2 x3 8 x5 x6 :=
    nb15_walk_x2 (by norm_num) (by norm_num) (by norm_num) h2 h2' h3 h3' (by norm_num)
      (by norm_num) h5 h5' h6 h6'
  have hD : deltaX 8 4 4 8 x5 x6 ≤ deltaX 8 4 x3 8 x5 x6 :=
    nb15_walk_x3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h3'
      (by norm_num) (by norm_num) h5 h5' h6 h6'
  have hE : deltaX 8 4 4 8 4 x6 ≤ deltaX 8 4 4 8 x5 x6 :=
    nb15_walk_x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5' h6 h6'
  have hF : deltaX 8 4 4 8 4 4 ≤ deltaX 8 4 4 8 4 x6 :=
    nb15_walk_x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6'
  calc (0:ℝ) = deltaX 8 4 4 8 4 4 := (nb15_deltaX_corner_lo).symm
    _ ≤ deltaX 8 4 4 8 4 x6 := hF
    _ ≤ deltaX 8 4 4 8 x5 x6 := hE
    _ ≤ deltaX 8 4 x3 8 x5 x6 := hD
    _ ≤ deltaX 8 x2 x3 8 x5 x6 := hC
    _ ≤ deltaX 8 x2 x3 x4 x5 x6 := hB
    _ ≤ deltaX x1 x2 x3 x4 x5 x6 := hA

/-- `deltaX ≤ 29.52807424` on the bank box. -/
theorem nb15_deltaX_hi {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8) (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401) (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401) (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    deltaX x1 x2 x3 x4 x5 x6 ≤ 29.52807424 := by
  have hA : deltaX x1 x2 x3 x4 x5 x6 ≤ deltaX 7.84 x2 x3 x4 x5 x6 :=
    nb15_walk_x1 (by norm_num) h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hB : deltaX 7.84 x2 x3 x4 x5 x6 ≤ deltaX 7.84 x2 x3 7.84 x5 x6 :=
    nb15_walk_x4 (by norm_num) (by norm_num) h2 h2' h3 h3' (by norm_num) h4 h4' h5 h5' h6 h6'
  have hC : deltaX 7.84 x2 x3 7.84 x5 x6 ≤ deltaX 7.84 4.0401 x3 7.84 x5 x6 :=
    nb15_walk_x2 (by norm_num) (by norm_num) h2 h2' (by norm_num) h3 h3' (by norm_num)
      (by norm_num) h5 h5' h6 h6'
  have hD : deltaX 7.84 4.0401 x3 7.84 x5 x6 ≤ deltaX 7.84 4.0401 4.0401 7.84 x5 x6 :=
    nb15_walk_x3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h3'
      (by norm_num) (by norm_num) (by norm_num) h5 h5' h6 h6'
  have hE : deltaX 7.84 4.0401 4.0401 7.84 x5 x6 ≤ deltaX 7.84 4.0401 4.0401 7.84 4.0401 x6 :=
    nb15_walk_x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h5 h5' (by norm_num) h6 h6'
  have hF : deltaX 7.84 4.0401 4.0401 7.84 4.0401 x6 ≤
      deltaX 7.84 4.0401 4.0401 7.84 4.0401 4.0401 :=
    nb15_walk_x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6' (by norm_num)
  calc deltaX x1 x2 x3 x4 x5 x6 ≤ deltaX 7.84 x2 x3 x4 x5 x6 := hA
    _ ≤ deltaX 7.84 x2 x3 7.84 x5 x6 := hB
    _ ≤ deltaX 7.84 4.0401 x3 7.84 x5 x6 := hC
    _ ≤ deltaX 7.84 4.0401 4.0401 7.84 x5 x6 := hD
    _ ≤ deltaX 7.84 4.0401 4.0401 7.84 4.0401 x6 := hE
    _ ≤ deltaX 7.84 4.0401 4.0401 7.84 4.0401 4.0401 := hF
    _ = 29.52807424 := nb15_deltaX_corner_hi

/-! ## 3. The Euler denominator `nb15_eulerA` and its lower bounds -/

/-- `eulerA_x` (`sphere.hl:830-833`), the `a` of `solEulerXDivSqrtdelta`. -/
noncomputable def nb15_eulerA (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
    Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2

theorem nb15_solEuler_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 =
      matan (deltaX x1 x2 x3 x4 x5 x6 / (4 * nb15_eulerA x1 x2 x3 x4 x5 x6 ^ 2)) /
        nb15_eulerA x1 x2 x3 x4 x5 x6 := rfl

theorem nb15_sqrt_ge {x c : ℝ} (hx : c ^ 2 ≤ x) (hc : 0 ≤ c) : c ≤ Real.sqrt x := by
  have h := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_sq hc] at h

theorem nb15_sqrt_le {x c : ℝ} (hx : x ≤ c ^ 2) (hc : 0 ≤ c) : Real.sqrt x ≤ c := by
  have h := Real.sqrt_le_sqrt hx
  rwa [Real.sqrt_sq hc] at h

/-- Pattern P1 (wide at 1,4): `26.799 ≤ nb15_eulerA`. -/
theorem nb15_a_p1 {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h2 : 4 ≤ x2) (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401)
    (h4 : 4 ≤ x4) (h4' : x4 ≤ 8) (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    (26.799:ℝ) ≤ nb15_eulerA x1 x2 x3 x4 x5 x6 := by
  have hsx1 : (2.8:ℝ) ≤ Real.sqrt x1 := nb15_sqrt_ge (by linarith) (by norm_num)
  have hsx2 : (2:ℝ) ≤ Real.sqrt x2 := nb15_sqrt_ge (by linarith) (by norm_num)
  have hsx3 : (2:ℝ) ≤ Real.sqrt x3 := nb15_sqrt_ge (by linarith) (by norm_num)
  have h23 : (16:ℝ) ≤ x2 * x3 := by
    have h := nb15_mulm h2 h3 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have ht1 : (11.2:ℝ) ≤ Real.sqrt (x1 * x2 * x3) := nb15_sqrt_ge (by nlinarith) (by norm_num)
  have ht2 : (0:ℝ) ≤ Real.sqrt x1 * (x2 + x3 - x4) / 2 := by
    have h : (0:ℝ) ≤ x2 + x3 - x4 := by linarith
    have h' : (0:ℝ) ≤ Real.sqrt x1 := Real.sqrt_nonneg x1
    positivity
  have ht3 : (7.7999:ℝ) ≤ Real.sqrt x2 * (x1 + x3 - x5) / 2 := by
    have hb : (7.7999:ℝ) ≤ x1 + x3 - x5 := by linarith
    exact nb15_two_mul_le hsx2 hb
  have ht4 : (7.7999:ℝ) ≤ Real.sqrt x3 * (x1 + x2 - x6) / 2 := by
    have hb : (7.7999:ℝ) ≤ x1 + x2 - x6 := by linarith
    exact nb15_two_mul_le hsx3 hb
  unfold nb15_eulerA
  linarith

/-- Pattern P2 (wide at 3,6): `26.799 ≤ nb15_eulerA`. -/
theorem nb15_a_p2 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 4 ≤ y1) (h1' : y1 ≤ 4.0401) (h2 : 4 ≤ y2) (h2' : y2 ≤ 4.0401)
    (h3 : (7.84:ℝ) ≤ y3) (h3' : y3 ≤ 8) (h4 : 4 ≤ y4) (h4' : y4 ≤ 4.0401)
    (h5 : 4 ≤ y5) (h5' : y5 ≤ 4.0401) (h6 : (7.84:ℝ) ≤ y6) (h6' : y6 ≤ 8) :
    (26.799:ℝ) ≤ nb15_eulerA y1 y2 y3 y4 y5 y6 := by
  have hs1 : (2:ℝ) ≤ Real.sqrt y1 := nb15_sqrt_ge (by linarith) (by norm_num)
  have hs2 : (2:ℝ) ≤ Real.sqrt y2 := nb15_sqrt_ge (by linarith) (by norm_num)
  have h13 : (16:ℝ) ≤ y1 * y2 := by
    have h := nb15_mulm h1 h2 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have ht1 : (11.2:ℝ) ≤ Real.sqrt (y1 * y2 * y3) := nb15_sqrt_ge (by nlinarith) (by norm_num)
  have ht2 : (7.7999:ℝ) ≤ Real.sqrt y1 * (y2 + y3 - y4) / 2 := by
    have hb : (7.7999:ℝ) ≤ y2 + y3 - y4 := by linarith
    exact nb15_two_mul_le hs1 hb
  have ht3 : (7.7999:ℝ) ≤ Real.sqrt y2 * (y1 + y3 - y5) / 2 := by
    have hb : (7.7999:ℝ) ≤ y1 + y3 - y5 := by linarith
    exact nb15_two_mul_le hs2 hb
  have ht4 : (0:ℝ) ≤ Real.sqrt y3 * (y1 + y2 - y6) / 2 := by
    have h : (0:ℝ) ≤ y1 + y2 - y6 := by linarith
    have h' : (0:ℝ) ≤ Real.sqrt y3 := Real.sqrt_nonneg y3
    positivity
  unfold nb15_eulerA
  linarith

/-- Pattern P3 (wide at 2,5): `26.799 ≤ nb15_eulerA`. -/
theorem nb15_a_p3 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 4 ≤ y1) (h1' : y1 ≤ 4.0401) (h2 : (7.84:ℝ) ≤ y2) (h2' : y2 ≤ 8)
    (h3 : 4 ≤ y3) (h3' : y3 ≤ 4.0401) (h4 : 4 ≤ y4) (h4' : y4 ≤ 4.0401)
    (h5 : (7.84:ℝ) ≤ y5) (h5' : y5 ≤ 8) (h6 : 4 ≤ y6) (h6' : y6 ≤ 4.0401) :
    (26.799:ℝ) ≤ nb15_eulerA y1 y2 y3 y4 y5 y6 := by
  have hs1 : (2:ℝ) ≤ Real.sqrt y1 := nb15_sqrt_ge (by linarith) (by norm_num)
  have hs3 : (2:ℝ) ≤ Real.sqrt y3 := nb15_sqrt_ge (by linarith) (by norm_num)
  have h13 : (16:ℝ) ≤ y1 * y3 := by
    have h := nb15_mulm h1 h3 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have ht1 : (11.2:ℝ) ≤ Real.sqrt (y1 * y2 * y3) := nb15_sqrt_ge (by nlinarith) (by norm_num)
  have ht2 : (7.7999:ℝ) ≤ Real.sqrt y1 * (y2 + y3 - y4) / 2 := by
    have hb : (7.7999:ℝ) ≤ y2 + y3 - y4 := by linarith
    exact nb15_two_mul_le hs1 hb
  have ht3 : (0:ℝ) ≤ Real.sqrt y2 * (y1 + y3 - y5) / 2 := by
    have h : (0:ℝ) ≤ y1 + y3 - y5 := by linarith
    have h' : (0:ℝ) ≤ Real.sqrt y2 := Real.sqrt_nonneg y2
    positivity
  have ht4 : (7.7999:ℝ) ≤ Real.sqrt y3 * (y1 + y2 - y6) / 2 := by
    have hb : (7.7999:ℝ) ≤ y1 + y2 - y6 := by linarith
    exact nb15_two_mul_le hs3 hb
  unfold nb15_eulerA
  linarith

/-! ## 4. `deltaX4` brackets (`58.9 ≤ · ≤ 66.57`) -/

/-- Pattern P1 (narrow 1,2,4,5; wide 3,6). -/
theorem nb15_d4_p1 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 4 ≤ y1) (h1' : y1 ≤ 4.0401) (h2 : 4 ≤ y2) (h2' : y2 ≤ 4.0401)
    (h3 : (7.84:ℝ) ≤ y3) (h3' : y3 ≤ 8) (h4 : 4 ≤ y4) (h4' : y4 ≤ 4.0401)
    (h5 : 4 ≤ y5) (h5' : y5 ≤ 4.0401) (h6 : (7.84:ℝ) ≤ y6) (h6' : y6 ≤ 8) :
    (58.9:ℝ) ≤ deltaX4 y1 y2 y3 y4 y5 y6 ∧ deltaX4 y1 y2 y3 y4 y5 y6 ≤ 66.57 := by
  have hbr : (15.5998:ℝ) ≤ -y1 + y2 + y3 - y4 + y5 + y6 := by linarith
  have hbr' : -y1 + y2 + y3 - y4 + y5 + y6 ≤ 16.0802 := by linarith
  have hw : (62.3992:ℝ) ≤ y1 * (-y1 + y2 + y3 - y4 + y5 + y6) := by
    have h := nb15_mulm h1 hbr (show (0:ℝ) ≤ 4 by norm_num)
      (show (0:ℝ) ≤ 15.5998 by norm_num)
    linarith
  have hw' : y1 * (-y1 + y2 + y3 - y4 + y5 + y6) ≤ 64.96562002 := by
    have h := nb15_mulm h1' hbr' (show (0:ℝ) ≤ y1 by linarith)
      (show (0:ℝ) ≤ -y1 + y2 + y3 - y4 + y5 + y6 by linarith)
    linarith
  have m1 : (31.36:ℝ) ≤ y2 * y3 := by
    have h := nb15_mulm h2 h3 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 7.84 by norm_num)
    linarith
  have m1' : y2 * y3 ≤ 32.3208 := by
    have h := nb15_mulm h2' h3' (show (0:ℝ) ≤ y2 by linarith)
      (show (0:ℝ) ≤ y3 by linarith)
    linarith
  have m2 : (16:ℝ) ≤ y1 * y4 := by
    have h := nb15_mulm h1 h4 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m2' : y1 * y4 ≤ 16.32241 := by
    have h := nb15_mulm h1' h4' (show (0:ℝ) ≤ y1 by linarith)
      (show (0:ℝ) ≤ y4 by linarith)
    linarith
  have m3 : (16:ℝ) ≤ y2 * y5 := by
    have h := nb15_mulm h2 h5 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m3' : y2 * y5 ≤ 16.32241 := by
    have h := nb15_mulm h2' h5' (show (0:ℝ) ≤ y2 by linarith)
      (show (0:ℝ) ≤ y5 by linarith)
    linarith
  have m4 : (61.4656:ℝ) ≤ y3 * y6 := by
    have h := nb15_mulm h3 h6 (show (0:ℝ) ≤ 7.84 by norm_num)
      (show (0:ℝ) ≤ 7.84 by norm_num)
    linarith
  have m4' : y3 * y6 ≤ 64 := by
    have h := nb15_mulm h3' h6' (show (0:ℝ) ≤ y3 by linarith)
      (show (0:ℝ) ≤ y6 by linarith)
    linarith
  have m5 : (31.36:ℝ) ≤ y5 * y6 := by
    have h := nb15_mulm h5 h6 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 7.84 by norm_num)
    linarith
  have m5' : y5 * y6 ≤ 32.3208 := by
    have h := nb15_mulm h5' h6' (show (0:ℝ) ≤ y5 by linarith)
      (show (0:ℝ) ≤ y6 by linarith)
    linarith
  unfold deltaX4
  constructor <;> nlinarith

/-- Pattern P2 (narrow 1,3,4,6; wide 2,5). -/
theorem nb15_d4_p2 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 4 ≤ y1) (h1' : y1 ≤ 4.0401) (h2 : (7.84:ℝ) ≤ y2) (h2' : y2 ≤ 8)
    (h3 : 4 ≤ y3) (h3' : y3 ≤ 4.0401) (h4 : 4 ≤ y4) (h4' : y4 ≤ 4.0401)
    (h5 : (7.84:ℝ) ≤ y5) (h5' : y5 ≤ 8) (h6 : 4 ≤ y6) (h6' : y6 ≤ 4.0401) :
    (58.9:ℝ) ≤ deltaX4 y1 y2 y3 y4 y5 y6 ∧ deltaX4 y1 y2 y3 y4 y5 y6 ≤ 66.57 := by
  have hbr : (15.5998:ℝ) ≤ -y1 + y2 + y3 - y4 + y5 + y6 := by linarith
  have hbr' : -y1 + y2 + y3 - y4 + y5 + y6 ≤ 16.0802 := by linarith
  have hw : (62.3992:ℝ) ≤ y1 * (-y1 + y2 + y3 - y4 + y5 + y6) := by
    have h := nb15_mulm h1 hbr (show (0:ℝ) ≤ 4 by norm_num)
      (show (0:ℝ) ≤ 15.5998 by norm_num)
    linarith
  have hw' : y1 * (-y1 + y2 + y3 - y4 + y5 + y6) ≤ 64.96562002 := by
    have h := nb15_mulm h1' hbr' (show (0:ℝ) ≤ y1 by linarith)
      (show (0:ℝ) ≤ -y1 + y2 + y3 - y4 + y5 + y6 by linarith)
    linarith
  have m1 : (31.36:ℝ) ≤ y2 * y3 := by
    have h := nb15_mulm h2 h3 (show (0:ℝ) ≤ 7.84 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m1' : y2 * y3 ≤ 32.3208 := by
    have h := nb15_mulm h2' h3' (show (0:ℝ) ≤ y2 by linarith)
      (show (0:ℝ) ≤ y3 by linarith)
    linarith
  have m2 : (16:ℝ) ≤ y1 * y4 := by
    have h := nb15_mulm h1 h4 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m2' : y1 * y4 ≤ 16.32241 := by
    have h := nb15_mulm h1' h4' (show (0:ℝ) ≤ y1 by linarith)
      (show (0:ℝ) ≤ y4 by linarith)
    linarith
  have m3 : (61.4656:ℝ) ≤ y2 * y5 := by
    have h := nb15_mulm h2 h5 (show (0:ℝ) ≤ 7.84 by norm_num)
      (show (0:ℝ) ≤ 7.84 by norm_num)
    linarith
  have m3' : y2 * y5 ≤ 64 := by
    have h := nb15_mulm h2' h5' (show (0:ℝ) ≤ y2 by linarith)
      (show (0:ℝ) ≤ y5 by linarith)
    linarith
  have m4 : (16:ℝ) ≤ y3 * y6 := by
    have h := nb15_mulm h3 h6 (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m4' : y3 * y6 ≤ 16.32241 := by
    have h := nb15_mulm h3' h6' (show (0:ℝ) ≤ y3 by linarith)
      (show (0:ℝ) ≤ y6 by linarith)
    linarith
  have m5 : (31.36:ℝ) ≤ y5 * y6 := by
    have h := nb15_mulm h5 h6 (show (0:ℝ) ≤ 7.84 by norm_num) (show (0:ℝ) ≤ 4 by norm_num)
    linarith
  have m5' : y5 * y6 ≤ 32.3208 := by
    have h := nb15_mulm h5' h6' (show (0:ℝ) ≤ y5 by linarith)
      (show (0:ℝ) ≤ y6 by linarith)
    linarith
  unfold deltaX4
  constructor <;> nlinarith

/-! ## 5. `lfun` lower bound -/

theorem nb15_lfun_ge {x : ℝ} (hx : 4 ≤ x) (hx' : x ≤ 4.0401) :
    (0.9807:ℝ) ≤ lfun (Real.sqrt x / 2) := by
  have h201 : (2.01:ℝ) ^ 2 = 4.0401 := by norm_num
  have hs : Real.sqrt x ≤ 2.01 := nb15_sqrt_le (by linarith) (by norm_num)
  have hs0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  unfold lfun
  rw [show h0 = 1.26 from rfl]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1.26 - 1)]
  nlinarith

end Kepler.NliBanks15
