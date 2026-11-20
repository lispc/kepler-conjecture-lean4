import Kepler.Text.ZTGJoint0000DihSecond
import Kepler.Text.ZTGJoint0000Box
import Kepler.Text.Gamma4Concave

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

theorem ztg0000Wide_id {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y1 y2 y3 y4 y5 y6 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩

theorem ztg0000Wide_231564 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y2 y3 y1 y5 y6 y4 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h2, h2', h3, h3', h1, h1', h5, h5', h6, h6', h4, h4'⟩

theorem ztg0000Wide_312645 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y3 y1 y2 y6 y4 y5 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h3, h3', h1, h1', h2, h2', h6, h6', h4, h4', h5, h5'⟩

theorem ztg0000Wide_156423 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y1 y5 y6 y4 y2 y3 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h1, h1', h5, h5', h6, h6', h4, h4', h2, h2', h3, h3'⟩

theorem ztg0000Wide_561234 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y5 y6 y1 y2 y3 y4 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h5, h5', h6, h6', h1, h1', h2, h2', h3, h3', h4, h4'⟩

theorem ztg0000Wide_615342 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y6 y1 y5 y3 y4 y2 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h6, h6', h1, h1', h5, h5', h3, h3', h4, h4', h2, h2'⟩

theorem ztg0000Wide_453126 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y4 y5 y3 y1 y2 y6 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h4, h4', h5, h5', h3, h3', h1, h1', h2, h2', h6, h6'⟩

theorem ztg0000Wide_534261 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y5 y3 y4 y2 y6 y1 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h5, h5', h3, h3', h4, h4', h2, h2', h6, h6', h1, h1'⟩

theorem ztg0000Wide_345612 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y3 y4 y5 y6 y1 y2 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h3, h3', h4, h4', h5, h5', h6, h6', h1, h1', h2, h2'⟩

theorem ztg0000Wide_426153 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y4 y2 y6 y1 y5 y3 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h4, h4', h2, h2', h6, h6', h1, h1', h5, h5', h3, h3'⟩

theorem ztg0000Wide_264531 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y2 y6 y4 y5 y3 y1 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h2, h2', h6, h6', h4, h4', h5, h5', h3, h3', h1, h1'⟩

theorem ztg0000Wide_642315 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y6 y4 y2 y3 y1 y5 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h6, h6', h4, h4', h2, h2', h3, h3', h1, h1', h5, h5'⟩

theorem ztg0000Wide_435162 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y4 y3 y5 y1 y6 y2 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h4, h4', h3, h3', h5, h5', h1, h1', h6, h6', h2, h2'⟩

theorem ztg0000Wide_516243 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) : ztg0000Wide y5 y1 y6 y2 y4 y3 := by
  rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ⟨h5, h5', h1, h1', h6, h6', h2, h2', h4, h4', h3, h3'⟩

theorem ztg_dihY_hasDerivAt2_y1_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY1 t a2 a3 a4 a5 a6) (ztgDihY2_y1 a1 a2 a3 a4 a5 a6) a1 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y1 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

theorem ztg_dihY_hasDerivAt2_y2_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY2 a1 t a3 a4 a5 a6) (ztgDihY2_y2 a1 a2 a3 a4 a5 a6) a2 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y2 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

theorem ztg_dihY_hasDerivAt2_y3_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY3 a1 a2 t a4 a5 a6) (ztgDihY2_y3 a1 a2 a3 a4 a5 a6) a3 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y3 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

theorem ztg_dihY_hasDerivAt2_y4_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY4 a1 a2 a3 t a5 a6) (ztgDihY2_y4 a1 a2 a3 a4 a5 a6) a4 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y4 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

theorem ztg_dihY_hasDerivAt2_y5_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY5 a1 a2 a3 a4 t a6) (ztgDihY2_y5 a1 a2 a3 a4 a5 a6) a5 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y5 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

theorem ztg_dihY_hasDerivAt2_y6_wide (a1 a2 a3 a4 a5 a6 : ℝ)
    (hw : ztg0000Wide a1 a2 a3 a4 a5 a6) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => g4dDDihY6 a1 a2 a3 a4 a5 t) (ztgDihY2_y6 a1 a2 a3 a4 a5 a6) a6 := by
  have ha1 : 0 < a1 := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    linarith
  have hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'
  have hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5) := by
    rcases hw with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
    exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'
  exact ztg_dihY_hasDerivAt2_y6 a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135

noncomputable def ztgDSolY2_1 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y1 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y3 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y2 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY1 t y2 y3 y4 y5 y6) (ztgDSolY2_1 y1 y2 y3 y4 y5 y6) y1 := by
  have h1 : HasDerivAt (fun t => g4dDDihY1 t y2 y3 y4 y5 y6)
      (ztgDihY2_y1 y1 y2 y3 y4 y5 y6) y1 :=
    ztg_dihY_hasDerivAt2_y1_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY3 y2 y3 t y5 y6 y4)
      (ztgDihY2_y3 y2 y3 y1 y5 y6 y4) y1 :=
    ztg_dihY_hasDerivAt2_y3_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY2 y3 t y2 y6 y4 y5)
      (ztgDihY2_y2 y3 y1 y2 y6 y4 y5) y1 :=
    ztg_dihY_hasDerivAt2_y2_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_1]
  convert h using 1 <;> rfl

noncomputable def ztgDSolY2_2 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y2 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y1 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y3 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY2 y1 t y3 y4 y5 y6) (ztgDSolY2_2 y1 y2 y3 y4 y5 y6) y2 := by
  have h1 : HasDerivAt (fun t => g4dDDihY2 y1 t y3 y4 y5 y6)
      (ztgDihY2_y2 y1 y2 y3 y4 y5 y6) y2 :=
    ztg_dihY_hasDerivAt2_y2_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY1 t y3 y1 y5 y6 y4)
      (ztgDihY2_y1 y2 y3 y1 y5 y6 y4) y2 :=
    ztg_dihY_hasDerivAt2_y1_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY3 y3 y1 t y6 y4 y5)
      (ztgDihY2_y3 y3 y1 y2 y6 y4 y5) y2 :=
    ztg_dihY_hasDerivAt2_y3_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_2]
  convert h using 1 <;> rfl

noncomputable def ztgDSolY2_3 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y3 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y2 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y1 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY3 y1 y2 t y4 y5 y6) (ztgDSolY2_3 y1 y2 y3 y4 y5 y6) y3 := by
  have h1 : HasDerivAt (fun t => g4dDDihY3 y1 y2 t y4 y5 y6)
      (ztgDihY2_y3 y1 y2 y3 y4 y5 y6) y3 :=
    ztg_dihY_hasDerivAt2_y3_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY2 y2 t y1 y5 y6 y4)
      (ztgDihY2_y2 y2 y3 y1 y5 y6 y4) y3 :=
    ztg_dihY_hasDerivAt2_y2_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY1 t y1 y2 y6 y4 y5)
      (ztgDihY2_y1 y3 y1 y2 y6 y4 y5) y3 :=
    ztg_dihY_hasDerivAt2_y1_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_3]
  convert h using 1 <;> rfl

noncomputable def ztgDSolY2_4 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y4 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y6 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y5 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY4 y1 y2 y3 t y5 y6) (ztgDSolY2_4 y1 y2 y3 y4 y5 y6) y4 := by
  have h1 : HasDerivAt (fun t => g4dDDihY4 y1 y2 y3 t y5 y6)
      (ztgDihY2_y4 y1 y2 y3 y4 y5 y6) y4 :=
    ztg_dihY_hasDerivAt2_y4_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY6 y2 y3 y1 y5 y6 t)
      (ztgDihY2_y6 y2 y3 y1 y5 y6 y4) y4 :=
    ztg_dihY_hasDerivAt2_y6_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY5 y3 y1 y2 y6 t y5)
      (ztgDihY2_y5 y3 y1 y2 y6 y4 y5) y4 :=
    ztg_dihY_hasDerivAt2_y5_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_4]
  convert h using 1 <;> rfl

noncomputable def ztgDSolY2_5 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y5 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y4 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y6 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY5 y1 y2 y3 y4 t y6) (ztgDSolY2_5 y1 y2 y3 y4 y5 y6) y5 := by
  have h1 : HasDerivAt (fun t => g4dDDihY5 y1 y2 y3 y4 t y6)
      (ztgDihY2_y5 y1 y2 y3 y4 y5 y6) y5 :=
    ztg_dihY_hasDerivAt2_y5_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY4 y2 y3 y1 t y6 y4)
      (ztgDihY2_y4 y2 y3 y1 y5 y6 y4) y5 :=
    ztg_dihY_hasDerivAt2_y4_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY6 y3 y1 y2 y6 y4 t)
      (ztgDihY2_y6 y3 y1 y2 y6 y4 y5) y5 :=
    ztg_dihY_hasDerivAt2_y6_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_5]
  convert h using 1 <;> rfl

noncomputable def ztgDSolY2_6 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  ztgDihY2_y6 y1 y2 y3 y4 y5 y6
    + ztgDihY2_y5 y2 y3 y1 y5 y6 y4
    + ztgDihY2_y4 y3 y1 y2 y6 y4 y5

theorem ztg_solY_hasDerivAt2_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDSolY6 y1 y2 y3 y4 y5 t) (ztgDSolY2_6 y1 y2 y3 y4 y5 y6) y6 := by
  have h1 : HasDerivAt (fun t => g4dDDihY6 y1 y2 y3 y4 y5 t)
      (ztgDihY2_y6 y1 y2 y3 y4 y5 y6) y6 :=
    ztg_dihY_hasDerivAt2_y6_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have h2 : HasDerivAt (fun t => g4dDDihY5 y2 y3 y1 y5 t y4)
      (ztgDihY2_y5 y2 y3 y1 y5 y6 y4) y6 :=
    ztg_dihY_hasDerivAt2_y5_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => g4dDDihY4 y3 y1 y2 t y4 y5)
      (ztgDihY2_y4 y3 y1 y2 y6 y4 y5) y6 :=
    ztg_dihY_hasDerivAt2_y4_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have h := (h1.add h2).add h3
  rw [ztgDSolY2_6]
  convert h using 1 <;> rfl

/-! ## Axiom audit -/

noncomputable def ztgDVol4f2_1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_1 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_1 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_4 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_4 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y1 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y3 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y2 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y4 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y2 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y2 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y1 y2 y3 y4 y5 y6)

theorem ztg_vol4f_hasDerivAt2_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y1 / 2)) :
    HasDerivAt (fun t => g4dDVol4f1 t y2 y3 y4 y5 y6 L) (ztgDVol4f2_1 y1 y2 y3 y4 y5 y6 L) y1 := by
  have s1 := ztg_solY_hasDerivAt2_y1 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y1 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y4 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y4 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y1_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y1) hf
  have d1 := hf2.mul dt1
  have dt2 := ztg_dihY_hasDerivAt2_y3_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := ztg_dihY_hasDerivAt2_y2_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := ztg_dihY_hasDerivAt2_y4_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := ztg_dihY_hasDerivAt2_y2_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := ztg_dihY_hasDerivAt2_y2_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have dt7 := dihY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_1]
  convert h using 1
  all_goals first | rfl | ring

noncomputable def ztgDVol4f2_2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_2 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_5 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_5 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_2 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y2 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y1 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y3 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y6 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y4 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y6 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y2 y3 y1 y5 y6 y4)

theorem ztg_vol4f_hasDerivAt2_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y2 / 2)) :
    HasDerivAt (fun t => g4dDVol4f2 y1 t y3 y4 y5 y6 L) (ztgDVol4f2_2 y1 y2 y3 y4 y5 y6 L) y2 := by
  have s1 := ztg_solY_hasDerivAt2_y2 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y5 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y5 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y2 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y2_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := ztg_dihY_hasDerivAt2_y1_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y2) hf
  have d2 := hf2.mul dt2
  have dt3 := ztg_dihY_hasDerivAt2_y3_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := ztg_dihY_hasDerivAt2_y6_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := ztg_dihY_hasDerivAt2_y4_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := ztg_dihY_hasDerivAt2_y6_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have dt7 := dihY_hasDerivAt_y1 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_2]
  convert h using 1
  all_goals first | rfl | ring

noncomputable def ztgDVol4f2_3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_3 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_6 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_3 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_6 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y3 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y2 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y1 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y2 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y6 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y4 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y3 y1 y2 y6 y4 y5)

theorem ztg_vol4f_hasDerivAt2_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y3 / 2)) :
    HasDerivAt (fun t => g4dDVol4f3 y1 y2 t y4 y5 y6 L) (ztgDVol4f2_3 y1 y2 y3 y4 y5 y6 L) y3 := by
  have s1 := ztg_solY_hasDerivAt2_y3 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y6 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y3 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y6 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y3_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := ztg_dihY_hasDerivAt2_y2_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := ztg_dihY_hasDerivAt2_y1_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y3) hf
  have d3 := hf2.mul dt3
  have dt4 := ztg_dihY_hasDerivAt2_y2_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := ztg_dihY_hasDerivAt2_y6_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := ztg_dihY_hasDerivAt2_y4_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have dt7 := dihY_hasDerivAt_y1 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_3]
  convert h using 1
  all_goals first | rfl | ring

/-! ## Axiom audit -/

noncomputable def ztgDVol4f2_4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_4 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_4 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_1 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_1 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y4 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y6 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y5 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y1 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y5 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y5 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y4 y3 y5 y1 y6 y2)

theorem ztg_vol4f_hasDerivAt2_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y4 / 2)) :
    HasDerivAt (fun t => g4dDVol4f4 y1 y2 y3 t y5 y6 L) (ztgDVol4f2_4 y1 y2 y3 y4 y5 y6 L) y4 := by
  have s1 := ztg_solY_hasDerivAt2_y4 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y4 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y1 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y1 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y4_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := ztg_dihY_hasDerivAt2_y6_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := ztg_dihY_hasDerivAt2_y5_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := ztg_dihY_hasDerivAt2_y1_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y4) hf
  have d4 := hf2.mul dt4
  have dt5 := ztg_dihY_hasDerivAt2_y5_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := ztg_dihY_hasDerivAt2_y5_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have dt7 := dihY_hasDerivAt_y1 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_4]
  convert h using 1
  all_goals first | rfl | ring

noncomputable def ztgDVol4f2_5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_5 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_2 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_2 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_5 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y5 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y4 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y6 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y3 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y1 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y3 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y5 y1 y6 y2 y4 y3)

theorem ztg_vol4f_hasDerivAt2_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y5 / 2)) :
    HasDerivAt (fun t => g4dDVol4f5 y1 y2 y3 y4 t y6 L) (ztgDVol4f2_5 y1 y2 y3 y4 y5 y6 L) y5 := by
  have s1 := ztg_solY_hasDerivAt2_y5 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y2 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y2 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y5 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y5_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := ztg_dihY_hasDerivAt2_y4_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := ztg_dihY_hasDerivAt2_y6_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := ztg_dihY_hasDerivAt2_y3_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := ztg_dihY_hasDerivAt2_y1_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y5) hf
  have d5 := hf2.mul dt5
  have dt6 := ztg_dihY_hasDerivAt2_y3_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have dt7 := dihY_hasDerivAt_y1 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_5]
  convert h using 1
  all_goals first | rfl | ring

noncomputable def ztgDVol4f2_6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (ztgDSolY2_6 y1 y2 y3 y4 y5 y6
     + ztgDSolY2_3 y1 y5 y6 y4 y2 y3
     + ztgDSolY2_6 y4 y5 y3 y1 y2 y6
     + ztgDSolY2_3 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * ztgDihY2_y6 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * ztgDihY2_y5 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * ztgDihY2_y4 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * ztgDihY2_y5 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * ztgDihY2_y3 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * ztgDihY2_y1 y6 y1 y5 y3 y4 y2
     + L * g4dDDihY1 y6 y1 y5 y3 y4 y2)

theorem ztg_vol4f_hasDerivAt2_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y6 / 2)) :
    HasDerivAt (fun t => g4dDVol4f6 y1 y2 y3 y4 y5 t L) (ztgDVol4f2_6 y1 y2 y3 y4 y5 y6 L) y6 := by
  have s1 := ztg_solY_hasDerivAt2_y6 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd (ztg0000Wide_id hw)
  have s2 := ztg_solY_hasDerivAt2_y3 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd) (ztg0000Wide_156423 hw)
  have s3 := ztg_solY_hasDerivAt2_y6 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd) (ztg0000Wide_453126 hw)
  have s4 := ztg_solY_hasDerivAt2_y3 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd) (ztg0000Wide_426153 hw)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := ztg_dihY_hasDerivAt2_y6_wide y1 y2 y3 y4 y5 y6 (ztg0000Wide_id hw) hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := ztg_dihY_hasDerivAt2_y5_wide y2 y3 y1 y5 y6 y4 (ztg0000Wide_231564 hw) (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := ztg_dihY_hasDerivAt2_y4_wide y3 y1 y2 y6 y4 y5 (ztg0000Wide_312645 hw) (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := ztg_dihY_hasDerivAt2_y5_wide y4 y3 y5 y1 y6 y2 (ztg0000Wide_435162 hw) (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := ztg_dihY_hasDerivAt2_y3_wide y5 y1 y6 y2 y4 y3 (ztg0000Wide_516243 hw) (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := ztg_dihY_hasDerivAt2_y1_wide y6 y1 y5 y3 y4 y2 (ztg0000Wide_615342 hw) (by rw [g4d_deltaY_p615342]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y6) hf
  have d6 := hf2.mul dt6
  have dt7 := dihY_hasDerivAt_y1 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d7 := dt7.const_mul (L / 2)
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6).add d7
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [ztgDVol4f2_6]
  convert h using 1
  all_goals first | rfl | ring

/-! ## Axiom audit -/

noncomputable def ztgVolY2_y1 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y1 * y1) * (y4 * y4)) * deltaY y1 y2 y3 y4 y5 y6
        - (y1 * y1) * (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY1 y1 y2 y3 y4 y5 y6 - g4dDVol4f1 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY1 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y1 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_1 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y1 y1 y2 y3 y4 y5 y6

noncomputable def ztgVolY2_y2 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y2 * y2) * (y5 * y5)) * deltaY y1 y2 y3 y4 y5 y6
        - (y2 * y2) * (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY2 y1 y2 y3 y4 y5 y6 - g4dDVol4f2 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY2 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y2 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_2 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y2 y1 y2 y3 y4 y5 y6

noncomputable def ztgVolY2_y3 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y3 * y3) * (y6 * y6)) * deltaY y1 y2 y3 y4 y5 y6
        - (y3 * y3) * (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY3 y1 y2 y3 y4 y5 y6 - g4dDVol4f3 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY3 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y3 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_3 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y3 y1 y2 y3 y4 y5 y6

noncomputable def ztgVolY2_y4 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y4 * y4) * (y1 * y1)) * deltaY y1 y2 y3 y4 y5 y6
        - (y4 * y4) * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY4 y1 y2 y3 y4 y5 y6 - g4dDVol4f4 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY4 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y4 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_4 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y4 y1 y2 y3 y4 y5 y6

noncomputable def ztgVolY2_y5 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y5 * y5) * (y2 * y2)) * deltaY y1 y2 y3 y4 y5 y6
        - (y5 * y5) * (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY5 y1 y2 y3 y4 y5 y6 - g4dDVol4f5 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY5 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y5 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_5 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y5 y1 y2 y3 y4 y5 y6

noncomputable def ztgVolY2_y6 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  (((g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y6 * y6) * (y3 * y3)) * deltaY y1 y2 y3 y4 y5 y6
        - (y6 * y6) * (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))

noncomputable def ztgDMainFirst_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  g4dDVolY6 y1 y2 y3 y4 y5 y6 - g4dDVol4f6 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * g4dDDihY6 y1 y2 y3 y4 y5 y6

noncomputable def ztgDMainSecond_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  ztgVolY2_y6 y1 y2 y3 y4 y5 y6 - ztgDVol4f2_6 y1 y2 y3 y4 y5 y6 L -
    bSpine5 * ztgDihY2_y6 y1 y2 y3 y4 y5 y6

theorem ztg_main_hasDerivAt_y1 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y1 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 t y2 y3 y4 y5 y6) (ztgDMainFirst_y1 y1 y2 y3 y4 y5 y6 L) y1 := by
  have hg := gamma4fgcy_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 t y2 y3 y4 y5 y6) = fun t => gamma4fgcy  t y2 y3 y4 y5 y6 lmfun - bSpine5 * dihY t y2 y3 y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y1]
  exact h

theorem ztg_main_hasDerivAt2_y1 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y1 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y1 t y2 y3 y4 y5 y6 L) (ztgDMainSecond_y1 y1 y2 y3 y4 y5 y6 L) y1 := by
  have hv := volY_hasDerivAt2_y1 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y1 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y1_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

theorem ztg_main_hasDerivAt_y2 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y2 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 y1 t y3 y4 y5 y6) (ztgDMainFirst_y2 y1 y2 y3 y4 y5 y6 L) y2 := by
  have hg := gamma4fgcy_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 y1 t y3 y4 y5 y6) = fun t => gamma4fgcy  y1 t y3 y4 y5 y6 lmfun - bSpine5 * dihY y1 t y3 y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y2]
  exact h

theorem ztg_main_hasDerivAt2_y2 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y2 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y2 y1 t y3 y4 y5 y6 L) (ztgDMainSecond_y2 y1 y2 y3 y4 y5 y6 L) y2 := by
  have hv := volY_hasDerivAt2_y2 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y2 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y2_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

theorem ztg_main_hasDerivAt_y3 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y3 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 y1 y2 t y4 y5 y6) (ztgDMainFirst_y3 y1 y2 y3 y4 y5 y6 L) y3 := by
  have hg := gamma4fgcy_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 t y4 y5 y6) = fun t => gamma4fgcy  y1 y2 t y4 y5 y6 lmfun - bSpine5 * dihY y1 y2 t y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y3]
  exact h

theorem ztg_main_hasDerivAt2_y3 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y3 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y3 y1 y2 t y4 y5 y6 L) (ztgDMainSecond_y3 y1 y2 y3 y4 y5 y6 L) y3 := by
  have hv := volY_hasDerivAt2_y3 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y3 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y3_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

theorem ztg_main_hasDerivAt_y4 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y4 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 t y5 y6) (ztgDMainFirst_y4 y1 y2 y3 y4 y5 y6 L) y4 := by
  have hg := gamma4fgcy_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 t y5 y6) = fun t => gamma4fgcy  y1 y2 y3 t y5 y6 lmfun - bSpine5 * dihY y1 y2 y3 t y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y4]
  exact h

theorem ztg_main_hasDerivAt2_y4 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y4 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y4 y1 y2 y3 t y5 y6 L) (ztgDMainSecond_y4 y1 y2 y3 y4 y5 y6 L) y4 := by
  have hv := volY_hasDerivAt2_y4 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y4 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y4_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

theorem ztg_main_hasDerivAt_y5 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y5 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 t y6) (ztgDMainFirst_y5 y1 y2 y3 y4 y5 y6 L) y5 := by
  have hg := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 t y6) = fun t => gamma4fgcy  y1 y2 y3 y4 t y6 lmfun - bSpine5 * dihY y1 y2 y3 y4 t y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y5]
  exact h

theorem ztg_main_hasDerivAt2_y5 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y5 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y5 y1 y2 y3 y4 t y6 L) (ztgDMainSecond_y5 y1 y2 y3 y4 y5 y6 L) y5 := by
  have hv := volY_hasDerivAt2_y5 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y5 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y5_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

theorem ztg_main_hasDerivAt_y6 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y6 / 2)) :
    HasDerivAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 y5 t) (ztgDMainFirst_y6 y1 y2 y3 y4 y5 y6 L) y6 := by
  have hg := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have hdih := dihY_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have h := (hg.sub (hdih.const_mul bSpine5)).sub_const aSpine5
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 y5 t) = fun t => gamma4fgcy  y1 y2 y3 y4 y5 t lmfun - bSpine5 * dihY y1 y2 y3 y4 y5 t - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun, ztgDMainFirst_y6]
  exact h

theorem ztg_main_hasDerivAt2_y6 (y1 y2 y3 y4 y5 y6 L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) (hf : HasDerivAt lmfun L (y6 / 2))
    (hw : ztg0000Wide y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => ztgDMainFirst_y6 y1 y2 y3 y4 y5 t L) (ztgDMainSecond_y6 y1 y2 y3 y4 y5 y6 L) y6 := by
  have hv := volY_hasDerivAt2_y6 y1 y2 y3 y4 y5 y6 hd
  have hw4 := ztg_vol4f_hasDerivAt2_y6 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hw hf
  have hd2 := ztg_dihY_hasDerivAt2_y6_wide y1 y2 y3 y4 y5 y6 hw hd
  exact (hv.sub hw4).sub (hd2.const_mul bSpine5)

#print axioms ztg_comp2
#print axioms ztg_dihY_hasDerivAt2_y1_wide
#print axioms ztg_main_hasDerivAt_y1
#print axioms ztg_main_hasDerivAt2_y1
#print axioms ztg_dihY_hasDerivAt2_y2_wide
#print axioms ztg_main_hasDerivAt_y2
#print axioms ztg_main_hasDerivAt2_y2
#print axioms ztg_dihY_hasDerivAt2_y3_wide
#print axioms ztg_main_hasDerivAt_y3
#print axioms ztg_main_hasDerivAt2_y3
#print axioms ztg_dihY_hasDerivAt2_y4_wide
#print axioms ztg_main_hasDerivAt_y4
#print axioms ztg_main_hasDerivAt2_y4
#print axioms ztg_dihY_hasDerivAt2_y5_wide
#print axioms ztg_main_hasDerivAt_y5
#print axioms ztg_main_hasDerivAt2_y5
#print axioms ztg_dihY_hasDerivAt2_y6_wide
#print axioms ztg_main_hasDerivAt_y6
#print axioms ztg_main_hasDerivAt2_y6

end Kepler.Text
