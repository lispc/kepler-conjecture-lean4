/-
Kepler.Text.Gamma4Feed — coordinatewise monotonicity of `gamma4fgcy · lmfun`
on the RIBCYXU box and the machine-checked feed of
`bank_TSKAJXYRIBCYXUsharp_of_mono` (lane `gamma4-w4`, W4-c).

The derivative positivity `∂gamma4fgcy/∂yᵢ > 0` (all six slots, margin 0.0207)
is in `Gamma4VolY`; convexity of the box plus `monotoneOn_of_deriv_nonneg`
gives the six coordinate monotonicities and the bank reduction.
-/
import Kepler.Text.Gamma4VolY

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- Coordinatewise monotonicity in `y1` on the RIBCYXU box. -/
theorem g4d_mono_y1 {a b y2 y3 y4 y5 y6 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h2 : 2 ≤ y2) (h21 : y2 ≤ 2.001)
    (h3 : 2 ≤ y3) (h31 : y3 ≤ 2.001)
    (h4 : 2 ≤ y4) (h41 : y4 ≤ 2.001)
    (h5 : 2 ≤ y5) (h51 : y5 ≤ 2.001)
    (h6 : 2 ≤ y6) (h61 : y6 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy a y2 y3 y4 y5 y6 lmfun ≤ gamma4fgcy b y2 y3 y4 y5 y6 lmfun := by
  have hrA : g4dRInBox a y2 y3 y4 y5 y6 := ⟨ha, ha1, h2, h21, h3, h31, h4, h41, h5, h51, h6, h61⟩
  have hrB : g4dRInBox b y2 y3 y4 y5 y6 := ⟨hb, hb1, h2, h21, h3, h31, h4, h41, h5, h51, h6, h61⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox t y2 y3 y4 y5 y6 := ⟨ht1, ht2, h2, h21, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y1 t y2 y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox t y2 y3 y4 y5 y6 := ⟨ht1, ht2, h2, h21, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y1 t y2 y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox t y2 y3 y4 y5 y6 := ⟨ht1, ht2, h2, h21, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y1 t y2 y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y1_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y2` on the RIBCYXU box. -/
theorem g4d_mono_y2 {a b y1 y3 y4 y5 y6 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h1 : 2 ≤ y1) (h11 : y1 ≤ 2.001)
    (h3 : 2 ≤ y3) (h31 : y3 ≤ 2.001)
    (h4 : 2 ≤ y4) (h41 : y4 ≤ 2.001)
    (h5 : 2 ≤ y5) (h51 : y5 ≤ 2.001)
    (h6 : 2 ≤ y6) (h61 : y6 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy y1 a y3 y4 y5 y6 lmfun ≤ gamma4fgcy y1 b y3 y4 y5 y6 lmfun := by
  have hrA : g4dRInBox y1 a y3 y4 y5 y6 := ⟨h1, h11, ha, ha1, h3, h31, h4, h41, h5, h51, h6, h61⟩
  have hrB : g4dRInBox y1 b y3 y4 y5 y6 := ⟨h1, h11, hb, hb1, h3, h31, h4, h41, h5, h51, h6, h61⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 t y3 y4 y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox y1 t y3 y4 y5 y6 := ⟨h1, h11, ht1, ht2, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 t y3 y4 y5 y6 := ⟨h1, h11, ht1, ht2, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 t y3 y4 y5 y6 := ⟨h1, h11, ht1, ht2, h3, h31, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y2_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y3` on the RIBCYXU box. -/
theorem g4d_mono_y3 {a b y1 y2 y4 y5 y6 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h1 : 2 ≤ y1) (h11 : y1 ≤ 2.001)
    (h2 : 2 ≤ y2) (h21 : y2 ≤ 2.001)
    (h4 : 2 ≤ y4) (h41 : y4 ≤ 2.001)
    (h5 : 2 ≤ y5) (h51 : y5 ≤ 2.001)
    (h6 : 2 ≤ y6) (h61 : y6 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy y1 y2 a y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2 b y4 y5 y6 lmfun := by
  have hrA : g4dRInBox y1 y2 a y4 y5 y6 := ⟨h1, h11, h2, h21, ha, ha1, h4, h41, h5, h51, h6, h61⟩
  have hrB : g4dRInBox y1 y2 b y4 y5 y6 := ⟨h1, h11, h2, h21, hb, hb1, h4, h41, h5, h51, h6, h61⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox y1 y2 t y4 y5 y6 := ⟨h1, h11, h2, h21, ht1, ht2, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 t y4 y5 y6 := ⟨h1, h11, h2, h21, ht1, ht2, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 t y4 y5 y6 := ⟨h1, h11, h2, h21, ht1, ht2, h4, h41, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y3_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y4` on the RIBCYXU box. -/
theorem g4d_mono_y4 {a b y1 y2 y3 y5 y6 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h1 : 2 ≤ y1) (h11 : y1 ≤ 2.001)
    (h2 : 2 ≤ y2) (h21 : y2 ≤ 2.001)
    (h3 : 2 ≤ y3) (h31 : y3 ≤ 2.001)
    (h5 : 2 ≤ y5) (h51 : y5 ≤ 2.001)
    (h6 : 2 ≤ y6) (h61 : y6 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy y1 y2 y3 a y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 b y5 y6 lmfun := by
  have hrA : g4dRInBox y1 y2 y3 a y5 y6 := ⟨h1, h11, h2, h21, h3, h31, ha, ha1, h5, h51, h6, h61⟩
  have hrB : g4dRInBox y1 y2 y3 b y5 y6 := ⟨h1, h11, h2, h21, h3, h31, hb, hb1, h5, h51, h6, h61⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 y3 t y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox y1 y2 y3 t y5 y6 := ⟨h1, h11, h2, h21, h3, h31, ht1, ht2, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y4 y1 y2 y3 t y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 t y5 y6 := ⟨h1, h11, h2, h21, h3, h31, ht1, ht2, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y4 y1 y2 y3 t y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 t y5 y6 := ⟨h1, h11, h2, h21, h3, h31, ht1, ht2, h5, h51, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y4 y1 y2 y3 t y5 y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y4_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y5` on the RIBCYXU box. -/
theorem g4d_mono_y5 {a b y1 y2 y3 y4 y6 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h1 : 2 ≤ y1) (h11 : y1 ≤ 2.001)
    (h2 : 2 ≤ y2) (h21 : y2 ≤ 2.001)
    (h3 : 2 ≤ y3) (h31 : y3 ≤ 2.001)
    (h4 : 2 ≤ y4) (h41 : y4 ≤ 2.001)
    (h6 : 2 ≤ y6) (h61 : y6 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy y1 y2 y3 y4 a y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 b y6 lmfun := by
  have hrA : g4dRInBox y1 y2 y3 y4 a y6 := ⟨h1, h11, h2, h21, h3, h31, h4, h41, ha, ha1, h6, h61⟩
  have hrB : g4dRInBox y1 y2 y3 y4 b y6 := ⟨h1, h11, h2, h21, h3, h31, h4, h41, hb, hb1, h6, h61⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox y1 y2 y3 y4 t y6 := ⟨h1, h11, h2, h21, h3, h31, h4, h41, ht1, ht2, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 y4 t y6 := ⟨h1, h11, h2, h21, h3, h31, h4, h41, ht1, ht2, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 y4 t y6 := ⟨h1, h11, h2, h21, h3, h31, h4, h41, ht1, ht2, h6, h61⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y5_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y6` on the RIBCYXU box. -/
theorem g4d_mono_y6 {a b y1 y2 y3 y4 y5 : ℝ}
    (ha : 2 ≤ a) (ha1 : a ≤ 2.001) (hb : 2 ≤ b) (hb1 : b ≤ 2.001)
    (h1 : 2 ≤ y1) (h11 : y1 ≤ 2.001)
    (h2 : 2 ≤ y2) (h21 : y2 ≤ 2.001)
    (h3 : 2 ≤ y3) (h31 : y3 ≤ 2.001)
    (h4 : 2 ≤ y4) (h41 : y4 ≤ 2.001)
    (h5 : 2 ≤ y5) (h51 : y5 ≤ 2.001)
    (hab : a ≤ b) :
    gamma4fgcy y1 y2 y3 y4 y5 a lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 b lmfun := by
  have hrA : g4dRInBox y1 y2 y3 y4 y5 a := ⟨h1, h11, h2, h21, h3, h31, h4, h41, h5, h51, ha, ha1⟩
  have hrB : g4dRInBox y1 y2 y3 y4 y5 b := ⟨h1, h11, h2, h21, h3, h31, h4, h41, h5, h51, hb, hb1⟩
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 y3 y4 y5 t lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      have ht1 : 2 ≤ t := le_trans ha ht.1
      have ht2 : t ≤ 2.001 := le_trans ht.2 hb1
      have hmem : g4dRInBox y1 y2 y3 y4 y5 t := ⟨h1, h11, h2, h21, h3, h31, h4, h41, h5, h51, ht1, ht2⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 y4 y5 t := ⟨h1, h11, h2, h21, h3, h31, h4, h41, h5, h51, ht1, ht2⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht1 : 2 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2.001 := le_trans ht.2.le hb1
      have hmem : g4dRInBox y1 y2 y3 y4 y5 t := ⟨h1, h11, h2, h21, h3, h31, h4, h41, h5, h51, ht1, ht2⟩
      have h0v : h0 = 1.26 := rfl
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1/(h0-1)) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (g4d_deltaY_pos hmem) (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht2, h0v]))
      rw [hd.deriv]
      have hp := g4d_partial_y6_pos hmem
      linarith
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
/-- **W4-c**: the six-variable monotone slot of `bank_TSKAJXYRIBCYXUsharp`. -/
theorem g4d_bank_RIBCYXU_mono :
    ∀ y1 y2 y3 y4 y5 y6 y1' y2' y3' y4' y5' y6' : ℝ,
      g4dRInBox y1 y2 y3 y4 y5 y6 → g4dRInBox y1' y2' y3' y4' y5' y6' →
      y1 ≤ y1' → y2 ≤ y2' → y3 ≤ y3' → y4 ≤ y4' → y5 ≤ y5' → y6 ≤ y6' →
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ≤
        gamma4fgcy y1' y2' y3' y4' y5' y6' lmfun := by
  intro y1 y2 y3 y4 y5 y6 y1' y2' y3' y4' y5' y6' hb hb' h1 h2 h3 h4 h5 h6
  obtain ⟨h1a, h1a', h2a, h2a', h3a, h3a', h4a, h4a', h5a, h5a', h6a, h6a'⟩ := hb
  obtain ⟨h1b, h1b', h2b, h2b', h3b, h3b', h4b, h4b', h5b, h5b', h6b, h6b'⟩ := hb'
  have s1 := g4d_mono_y1 h1a h1a' h1b h1b' h2a h2a' h3a h3a' h4a h4a' h5a h5a' h6a h6a' h1
  have s2 := g4d_mono_y2 h2a h2a' h2b h2b' h1b h1b' h3a h3a' h4a h4a' h5a h5a' h6a h6a' h2
  have s3 := g4d_mono_y3 h3a h3a' h3b h3b' h1b h1b' h2b h2b' h4a h4a' h5a h5a' h6a h6a' h3
  have s4 := g4d_mono_y4 h4a h4a' h4b h4b' h1b h1b' h2b h2b' h3b h3b' h5a h5a' h6a h6a' h4
  have s5 := g4d_mono_y5 h5a h5a' h5b h5b' h1b h1b' h2b h2b' h3b h3b' h4b h4b' h6a h6a' h5
  have s6 := g4d_mono_y6 h6a h6a' h6b h6b' h1b h1b' h2b h2b' h3b h3b' h4b h4b' h5b h5b' h6
  exact le_trans s1 (le_trans s2 (le_trans s3 (le_trans s4 (le_trans s5 s6))))

/-- **W4-c DONE (RIBCYXU)**: the bank follows from `g4d_bank_RIBCYXU_mono`. -/
theorem g4d_bank_RIBCYXUsharp : bank_TSKAJXYRIBCYXUsharp :=
  bank_TSKAJXYRIBCYXUsharp_of_mono (fun y1 y2 y3 y4 y5 y6 y1' y2' y3' y4' y5' y6'
    hb hb' h1 h2 h3 h4 h5 h6 => by
    have hbR : g4dRInBox y1 y2 y3 y4 y5 y6 := hb
    have hbR' : g4dRInBox y1' y2' y3' y4' y5' y6' := hb'
    exact g4d_bank_RIBCYXU_mono y1 y2 y3 y4 y5 y6 y1' y2' y3' y4' y5' y6'
      hbR hbR' h1 h2 h3 h4 h5 h6)

#print axioms g4dDVolY1_ge
#print axioms g4dDVolY2_ge
#print axioms g4dDVolY3_ge
#print axioms g4dDVolY4_ge
#print axioms g4dDVolY5_ge
#print axioms g4dDVolY6_ge
#print axioms g4d_partial_y1_pos
#print axioms g4d_partial_y2_pos
#print axioms g4d_partial_y3_pos
#print axioms g4d_partial_y4_pos
#print axioms g4d_partial_y5_pos
#print axioms g4d_partial_y6_pos
#print axioms g4d_mono_y1
#print axioms g4d_mono_y2
#print axioms g4d_mono_y3
#print axioms g4d_mono_y4
#print axioms g4d_mono_y5
#print axioms g4d_mono_y6
#print axioms g4d_bank_RIBCYXU_mono
#print axioms g4d_bank_RIBCYXUsharp

end Kepler.Text
