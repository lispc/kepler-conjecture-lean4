
/-
Kepler.Text.Gamma4Mono0 — shared kit for the `gamma4fgcy` y-partial lower bounds
on the RIBCYXU box `[2,2.001]⁶` (lane `gamma4-w4`, W4-c).

Contents: the box predicate and its fourteen edge permutation preservers, the
`squared box ⊆ [4,4.004001]⁶` transfer, the six `g4dDDihY` slot bounds
(`2·a_k·D_k`), the `lmfun ∈ [0.9979,1]` and `dihY ∈ [0,π/2]` bounds, and two
scalar combination lemmas used to bound `c·S` and `−c·D` by monotone
cross-multiplication.
-/
import Kepler.Text.Gamma4EnvNum

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- The RIBCYXU edge box `[2,2.001]⁶`. -/
def g4dRInBox (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 ≤ y1 ∧ y1 ≤ 2.001 ∧ 2 ≤ y2 ∧ y2 ≤ 2.001 ∧ 2 ≤ y3 ∧ y3 ≤ 2.001 ∧
    2 ≤ y4 ∧ y4 ≤ 2.001 ∧ 2 ≤ y5 ∧ y5 ≤ 2.001 ∧ 2 ≤ y6 ∧ y6 ≤ 2.001

theorem g4dRInBox_corner : g4dRInBox 2 2 2 2 2 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## The fourteen edge permutations preserve the box -/

theorem g4dR_p231564 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a2 a3 a1 a5 a6 a4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h2, h2', h3, h3', h1, h1', h5, h5', h6, h6', h4, h4'⟩

theorem g4dR_p312645 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a3 a1 a2 a6 a4 a5 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h3, h3', h1, h1', h2, h2', h6, h6', h4, h4', h5, h5'⟩

theorem g4dR_p156423 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a1 a5 a6 a4 a2 a3 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h1, h1', h5, h5', h6, h6', h4, h4', h2, h2', h3, h3'⟩

theorem g4dR_p561234 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a5 a6 a1 a2 a3 a4 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h5, h5', h6, h6', h1, h1', h2, h2', h3, h3', h4, h4'⟩

theorem g4dR_p615342 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a6 a1 a5 a3 a4 a2 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h6, h6', h1, h1', h5, h5', h3, h3', h4, h4', h2, h2'⟩

theorem g4dR_p453126 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a4 a5 a3 a1 a2 a6 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h4, h4', h5, h5', h3, h3', h1, h1', h2, h2', h6, h6'⟩

theorem g4dR_p534261 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a5 a3 a4 a2 a6 a1 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h5, h5', h3, h3', h4, h4', h2, h2', h6, h6', h1, h1'⟩

theorem g4dR_p345612 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a3 a4 a5 a6 a1 a2 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h3, h3', h4, h4', h5, h5', h6, h6', h1, h1', h2, h2'⟩

theorem g4dR_p426153 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a4 a2 a6 a1 a5 a3 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h4, h4', h2, h2', h6, h6', h1, h1', h5, h5', h3, h3'⟩

theorem g4dR_p264531 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a2 a6 a4 a5 a3 a1 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h2, h2', h6, h6', h4, h4', h5, h5', h3, h3', h1, h1'⟩

theorem g4dR_p642315 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a6 a4 a2 a3 a1 a5 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h6, h6', h4, h4', h2, h2', h3, h3', h1, h1', h5, h5'⟩

theorem g4dR_p435162 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a4 a3 a5 a1 a6 a2 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h4, h4', h3, h3', h5, h5', h1, h1', h6, h6', h2, h2'⟩

theorem g4dR_p516243 {a1 a2 a3 a4 a5 a6 : ℝ} (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dRInBox a5 a1 a6 a2 a4 a3 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  exact ⟨h5, h5', h1, h1', h6, h6', h2, h2', h4, h4', h3, h3'⟩

/-! ## The squared box -/

theorem g4dInBox_sq {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    g4dInBox (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6) := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-! ## The `g4dDDihY` slot bounds (`2·a_k·D_k`) -/

theorem g4dDDihY_pos_bounds {a D Dl Dh : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2.001)
    (hDl : Dl ≤ D) (hDh : D ≤ Dh) (hDl0 : 0 ≤ Dl) :
    4 * Dl ≤ 2 * a * D ∧ 2 * a * D ≤ 4.002 * Dh := by
  have hapos : (0:ℝ) < 2 * a := by linarith
  constructor
  · have h1 : 4 * Dl ≤ 2 * a * Dl := by nlinarith
    have h2 : 2 * a * Dl ≤ 2 * a * D := mul_le_mul_of_nonneg_left hDl hapos.le
    linarith
  · have h1 : 2 * a * D ≤ 2 * a * Dh := mul_le_mul_of_nonneg_left hDh hapos.le
    have h2 : 2 * a * Dh ≤ 4.002 * Dh := by nlinarith
    linarith

theorem g4dDDihY_neg_bounds {a D Dl Dh : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2.001)
    (hDl : Dl ≤ D) (hDh : D ≤ Dh) (hDh0 : Dh ≤ 0) :
    4.002 * Dl ≤ 2 * a * D ∧ 2 * a * D ≤ 4 * Dh := by
  have hapos : (0:ℝ) < 2 * a := by linarith
  constructor
  · have h1 : 4.002 * Dl ≤ 2 * a * Dl := by nlinarith
    have h2 : 2 * a * Dl ≤ 2 * a * D := mul_le_mul_of_nonneg_left hDl hapos.le
    linarith
  · have h1 : 2 * a * D ≤ 2 * a * Dh := mul_le_mul_of_nonneg_left hDh hapos.le
    have h2 : 2 * a * Dh ≤ 4 * Dh := by nlinarith
    linarith

theorem g4dDDihY1_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4 * 0.0579 ≤ g4dDDihY1 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY1 a1 a2 a3 a4 a5 a6 ≤ 4.002 * 0.0599 := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX1_bounds hbox
  have := g4dDDihY_pos_bounds h1 h1' hl hh (by norm_num)
  simpa only [g4dDDihY1] using this

theorem g4dDDihY2_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4.002 * (-0.0593) ≤ g4dDDihY2 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY2 a1 a2 a3 a4 a5 a6 ≤ 4 * (-0.0585) := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX2_bounds hbox
  have := g4dDDihY_neg_bounds h2 h2' hl hh (by norm_num)
  simpa only [g4dDDihY2] using this

theorem g4dDDihY3_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4.002 * (-0.0593) ≤ g4dDDihY3 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY3 a1 a2 a3 a4 a5 a6 ≤ 4 * (-0.0585) := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX3_bounds hbox
  have := g4dDDihY_neg_bounds h3 h3' hl hh (by norm_num)
  simpa only [g4dDDihY3] using this

theorem g4dDDihY4_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4 * 0.17625 ≤ g4dDDihY4 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY4 a1 a2 a3 a4 a5 a6 ≤ 4.002 * 0.17709 := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX4_bounds hbox
  have := g4dDDihY_pos_bounds h4 h4' hl hh (by norm_num)
  simpa only [g4dDDihY4] using this

theorem g4dDDihY5_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4.002 * (-0.0593) ≤ g4dDDihY5 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY5 a1 a2 a3 a4 a5 a6 ≤ 4 * (-0.0585) := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX5_bounds hbox
  have := g4dDDihY_neg_bounds h5 h5' hl hh (by norm_num)
  simpa only [g4dDDihY5] using this

theorem g4dDDihY6_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    4.002 * (-0.0593) ≤ g4dDDihY6 a1 a2 a3 a4 a5 a6 ∧
      g4dDDihY6 a1 a2 a3 a4 a5 a6 ≤ 4 * (-0.0585) := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hl, hh⟩ := g4dDihX6_bounds hbox
  have := g4dDDihY_neg_bounds h6 h6' hl hh (by norm_num)
  simpa only [g4dDDihY6] using this

/-! ## The `lmfun` weight and the `dihY` range -/

theorem g4d_lmfun_bounds {y : ℝ} (h1 : 2 ≤ y) (h2 : y ≤ 2.001) :
    0.9979 ≤ lmfun (y/2) ∧ lmfun (y/2) ≤ 1 := by
  have hle : y/2 ≤ h0 := by norm_num [h0]; linarith
  have hge : (1:ℝ) ≤ y/2 := by linarith
  rw [lmfun, if_pos hle]
  have hden : (0:ℝ) < h0 - 1 := by norm_num [h0]
  have h0v : h0 = 1.26 := rfl
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [h0v]
  · rw [div_le_one hden]
    nlinarith [h0v]

/-- `0 ≤ dihY ≤ π/2` on the RIBCYXU box: `dihY = π/2 + atn2(A, −Δ₄)` and
`|−Δ₄| < A`, so the `atn2` is `arctan(−Δ₄/A) ∈ (−π/2, 0]`. -/
theorem g4d_dihY_bounds_of_rbox {a1 a2 a3 a4 a5 a6 : ℝ}
    (h : g4dRInBox a1 a2 a3 a4 a5 a6) :
    0 ≤ dihY a1 a2 a3 a4 a5 a6 ∧ dihY a1 a2 a3 a4 a5 a6 ≤ Real.pi / 2 := by
  have hbox := g4dInBox_sq h
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := h
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbox
  obtain ⟨hD4lo, hD4hi⟩ := g4d_deltaX4_bounds hbox
  have hApos : (0:ℝ) < Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6)) := by
    linarith
  have hlt : |-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))| <
      Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6)) := by
    rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  have hv : dihY a1 a2 a3 a4 a5 a6 = Real.pi/2 +
      atn2 (Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6)))
        (-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) := by
    unfold dihY dihXf
    rfl
  have hatn : atn2 (Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6)))
      (-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6)))
      = Real.arctan ((-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) /
          Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) := by
    rw [atn2, if_pos hlt]
  have hnonpos : Real.arctan ((-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) /
      Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) ≤ 0 := by
    apply Real.arctan_le_zero.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hApos.le
  have hgt : -(Real.pi/2) < Real.arctan ((-(deltaX4 (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) /
      Real.sqrt (4 * (a1*a1) * deltaX (a1*a1) (a2*a2) (a3*a3) (a4*a4) (a5*a5) (a6*a6))) :=
    Real.neg_pi_div_two_lt_arctan _
  constructor
  · rw [hv]; rw [hatn]; linarith
  · rw [hv]; rw [hatn]; linarith

/-! ## Scalar combination lemmas -/

theorem g4d_mul_le_upper {c ch S Sh : ℝ} (hc : 0 ≤ c) (hch : c ≤ ch)
    (hS : S ≤ Sh) (hSh : 0 ≤ Sh) : c * S ≤ ch * Sh := by
  rcases le_total 0 S with hs | hs
  · exact mul_le_mul hch hS hs (le_trans hc hch)
  · have h1 : c * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hs
    have h2 : 0 ≤ ch * Sh := mul_nonneg (le_trans hc hch) hSh
    linarith

theorem g4d_neg_mul_le {c ch D Dl : ℝ} (hc : 0 ≤ c) (hch : c ≤ ch)
    (hD : Dl ≤ D) (hDl : Dl ≤ 0) : -(c * D) ≤ -(ch * Dl) := by
  rcases le_total 0 D with hd | hd
  · have h1 : 0 ≤ -(ch * Dl) := by nlinarith [mul_nonneg (le_trans hc hch) (neg_nonneg.mpr hDl)]
    have h2 : c * D ≥ 0 := mul_nonneg hc hd
    linarith
  · have h1 : 0 ≤ -D := by linarith
    have h2 : -D ≤ -Dl := by linarith
    have h3 : c * (-D) ≤ ch * (-Dl) := mul_le_mul hch h2 h1 (le_trans hc hch)
    nlinarith [h3]

/-- Positive weighted term: `w ∈ [0.9979,1]`, `Wl ≤ X`, `0 ≤ Wl` give
`0.9979·Wl ≤ w·X`. -/
theorem g4d_weighted_pos {w X Wl : ℝ} (hw : 0.9979 ≤ w) (hw1 : w ≤ 1)
    (hX : Wl ≤ X) (hWl : 0 ≤ Wl) : 0.9979 * Wl ≤ w * X := by
  have hw0 : 0 ≤ w := by linarith
  exact le_trans (mul_le_mul_of_nonneg_right hw hWl) (mul_le_mul_of_nonneg_left hX hw0)

/-- Negative weighted term: `w ∈ [0.9979,1]`, `Wl ≤ X ≤ 0` give `Wl ≤ w·X`. -/
theorem g4d_weighted_neg {w X Wl : ℝ} (hw : 0.9979 ≤ w) (hw1 : w ≤ 1)
    (hX : Wl ≤ X) (hX0 : X ≤ 0) : Wl ≤ w * X := by
  have hw0 : 0 ≤ w := by linarith
  have h1 : w * Wl ≤ w * X := mul_le_mul_of_nonneg_left hX hw0
  have h2 : Wl ≤ w * Wl := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - w) (by linarith : (0:ℝ) ≤ -Wl)]
  linarith

#print axioms g4dRInBox_corner
#print axioms g4dInBox_sq
#print axioms g4dDDihY_pos_bounds
#print axioms g4dDDihY_neg_bounds
#print axioms g4dDDihY1_of_rbox
#print axioms g4dDDihY2_of_rbox
#print axioms g4dDDihY3_of_rbox
#print axioms g4dDDihY4_of_rbox
#print axioms g4dDDihY5_of_rbox
#print axioms g4dDDihY6_of_rbox
#print axioms g4d_lmfun_bounds
#print axioms g4d_dihY_bounds_of_rbox
#print axioms g4d_mul_le_upper
#print axioms g4d_neg_mul_le
#print axioms g4d_weighted_pos
#print axioms g4d_weighted_neg

end Kepler.Text
