/-
LocalAuto23Jotswix — the JOTSWIX.hl Section A twin kit (lane `lflacku-w1`).

WHY THIS MODULE EXISTS.  `LocalAuto23` carries the four `JOTSWIX.hl` Section A
declarations (`taum_attains_inf_p23` / `TAUM_EXTREMAL_p23` / `TAUM_STD_POS_p23`
/ `LFLACKU_p23`) as unproved placeholders, and `LocalAuto16:495` consumes the last one for
the terminal `JEJTVGB` case analysis.  LA23 cannot import LA16/LA22-class
kits (the DAG puts it below them), so the cone-relevant declarations are
re-proved here under primed names with byte-identical statements, and
`LocalAuto16` is rewired to the primed `LFLACKU_p23'`.  Three of the four are
proved here (`TAUM_EXTREMAL_p23'` / `TAUM_STD_POS_p23'` / `LFLACKU_p23'`); see
the note below for `taum_attains_inf_p23`.  The original four stay untouched in
LA23 (they become file-level orphans, the same policy as the `TameLpPerimeter`
twin).

NOTE ON `taum_attains_inf_p23`.  The LA23 statement keeps only `y1 y2 y3 y5 y6`
as parameters and imposes NO box bounds on them, so it is strictly stronger
than HOL `JOTSWIX.hl:9` (which assumes `2 <= yi /\ yi <= 2 * h0` for all six
slots).  Without the box hypotheses `deltaY` is not known positive and
`taum` is *not* continuous in the `y4` slot (`atn2` jumps along `y = 0, x <= 0`,
which `deltaX <= 0` reaches whenever `deltaX4 = 0`), so the HOL
continuity+compactness route does not apply to the unconstrained form.  This
module therefore proves the box-bounded form HOL actually asserts (private
`taum_attains_inf_box_jx`) and feeds it to the remaining three twins; the
unconstrained LA23 statement is left as a documented UNRESOLVED debt.

IMPORTS: LA1 + SphereKit + LA22 (+ LA21 for `taum_dih_y_p16`, LA38 for the
`taum_sym2`/`taustar_taum_dfun`/`FUNLIST_EXPLICIT` bridges).  `LocalAuto16`
is imported NOWHERE here: LA16 imports this module, so the edge would cycle.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.SphereKit
import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto38
import Mathlib

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Kepler.Geom

/-! ## Continuity kit (ported private from `LocalAuto16:1012-1247`) -/

/-- `atn2 x y = Real.arctan (y / x)` on the right half-plane `0 < x`
(all three branches of the `atn2` definition agree there). -/
private theorem atn2_eq_arctan_div_jx {x y : ℝ} (hx : 0 < x) :
    atn2 x y = Real.arctan (y / x) := by
  unfold atn2
  by_cases h : |y| < x
  · rw [if_pos h]
  · rw [if_neg h]
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    by_cases hy : 0 < y
    · rw [if_pos hy]
      have hpos : 0 < y / x := div_pos hy hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_pos hpos]
      ring
    · rw [if_neg hy]
      have hyn : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
      rw [if_pos hyn]
      have hneg : y / x < 0 := div_neg_of_neg_of_pos hyn hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_neg hneg]
      ring

/-- Chain rule for `atn2` at a point where the first argument is positive:
continuity of `q ↦ atn2 (f q) (g q)` from continuity of `f` and `g`. -/
private theorem continuousAt_atn2_comp_jx {f g : ℝ → ℝ} {q0 : ℝ}
    (hf : ContinuousAt f q0) (hg : ContinuousAt g q0) (hpos : 0 < f q0) :
    ContinuousAt (fun q => atn2 (f q) (g q)) q0 := by
  have hcont : ContinuousAt (fun q => Real.arctan (g q / f q)) q0 :=
    Real.continuous_arctan.continuousAt.comp' (hg.div hf hpos.ne')
  refine hcont.congr ?_
  filter_upwards [hf.eventually (isOpen_Ioi.mem_nhds hpos)] with q hq
  exact (atn2_eq_arctan_div_jx hq).symm

/-- `dihXf` is continuous in its fourth slot at points where the `atn2` first
argument `sqrt (4 x1 deltaX)` is positive. -/
private theorem continuousAt_dihXf_wrt4_jx (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 q x5 x6) x4 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 q x5 x6)) x4 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 q x5 x6)) x4 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_jx hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 q x5 x6))
        (-(deltaX4 x1 x2 x3 q x5 x6))) x4 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihXf` is continuous in its fifth slot. -/
private theorem continuousAt_dihXf_wrt5_jx (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 x4 q x6) x5 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6)) x5 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 x4 q x6)) x5 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_jx hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6))
        (-(deltaX4 x1 x2 x3 x4 q x6))) x5 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihXf` is continuous in its sixth slot. -/
private theorem continuousAt_dihXf_wrt6_jx (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ContinuousAt (fun q => dihXf x1 x2 x3 x4 x5 q) x6 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 q)) x6 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 x1 x2 x3 x4 x5 q)) x6 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmain := continuousAt_atn2_comp_jx hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 q))
        (-(deltaX4 x1 x2 x3 x4 x5 q))) x6 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihXf] using hfin

/-- `dihY` is continuous in its fourth slot (`dihXf` at `x4 = y4 * y4`). -/
private theorem continuousAt_dihY_wrt4_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 q y5 y6) y4 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y4 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (q * q)
      (y5 * y5) (y6 * y6)) y4 :=
    (continuousAt_dihXf_wrt4_jx (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `dihY` is continuous in its fifth slot. -/
private theorem continuousAt_dihY_wrt5_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 q y6) y5 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y5 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (q * q) (y6 * y6)) y5 :=
    (continuousAt_dihXf_wrt5_jx (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `dihY` is continuous in its sixth slot. -/
private theorem continuousAt_dihY_wrt6_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 y5 q) y6 := by
  have hx1 : 0 < y1 * y1 := mul_pos hy1 hy1
  have hd' : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    simpa only [deltaY] using hd
  have hsq : ContinuousAt (fun q : ℝ => q * q) y6 := by fun_prop
  have h : ContinuousAt (fun q => dihXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (q * q)) y6 :=
    (continuousAt_dihXf_wrt6_jx (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6) hx1 hd').comp (f := fun q : ℝ => q * q) hsq
  simpa only [dihY] using h

/-- `deltaY` is invariant under the slot permutation `(1 2 3)(4 5 6)` used
by the second term of `taum_dih_y_p16` (a polynomial symmetry of `deltaX`). -/
private theorem deltaY_rot231564_jx (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y2 y3 y1 y5 y6 y4 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

/-- `deltaY` is invariant under the slot permutation `(1 3 2)(4 6 5)` used
by the third term of `taum_dih_y_p16` (the inverse rotation). -/
private theorem deltaY_rot312645_jx (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y3 y1 y2 y6 y4 y5 = deltaY y1 y2 y3 y4 y5 y6 := by
  unfold deltaY deltaX
  ring

/-- `upsX` is symmetric in its first two arguments. -/
private theorem upsX_swap12_jx (a b c : ℝ) : upsX a b c = upsX b a c := by
  unfold upsX
  ring

/-- HOL `real_continuous_dih_y_wrt4` (BKOSSGE.hl:181).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean): `dihY` in the `y4` slot is `dihXf` at
`x4 = y4 * y4`, whose only non-polynomial ingredient is `atn2`, continuous
at a positive first argument via the local `atn2` kit.  No Ocbicby
`derived_form_dih_x_wrt_x4` input (that upstream is still unproved). -/
private theorem real_continuous_dih_y_wrt4_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 q y5 y6) y4 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt4_jx y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_dih_y_wrt5` (BKOSSGE.hl:211).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean), same local `atn2` kit as `wrt4`. -/
private theorem real_continuous_dih_y_wrt5_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 q y6) y5 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt5_jx y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_dih_y_wrt6` (BKOSSGE.hl:241).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean), same local `atn2` kit as `wrt4`. -/
private theorem real_continuous_dih_y_wrt6_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6) (hy1 : 0 < y1)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => dihY y1 y2 y3 y4 y5 q) y6 := by
  have _ := hu1
  have _ := hu2
  exact continuousAt_dihY_wrt6_jx y1 y2 y3 y4 y5 y6 hy1 hdy

/-- HOL `real_continuous_taum` (BKOSSGE.hl:271).  PROVED 2026-11-05
(`la16-cont-w1`, Route B clean): rewrite `taum` by `taum_dih_y_p16` and
apply the `dih_y` slot suite to the three rotated `dihY` terms.  The two
rotations are `deltaY` permutation identities (`ring`) plus one `upsX`
swap; no Ocbicby `derived_form_*` input. -/
private theorem real_continuous_taum_jx (y1 y2 y3 y4 y5 y6 : ℝ)
    (hdy : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hu1 : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hu2 : 0 < upsX (y2 * y2) (y3 * y3) (y4 * y4))
    (hu3 : 0 < upsX (y1 * y1) (y3 * y3) (y5 * y5)) :
    ContinuousAt (fun q => taum y1 y2 y3 q y5 y6) y4 := by
  have hd1 : 0 < deltaY y2 y3 y1 y5 y6 y4 := by
    rw [deltaY_rot231564_jx]
    exact hdy
  have hd2 : 0 < deltaY y3 y1 y2 y6 y4 y5 := by
    rw [deltaY_rot312645_jx]
    exact hdy
  have h1 := real_continuous_dih_y_wrt4_jx y1 y2 y3 y4 y5 y6 hdy hy1 hu1 hu3
  have h2 := real_continuous_dih_y_wrt6_jx y2 y3 y1 y5 y6 y4 hd1 hy2 hu2
    (by rw [upsX_swap12_jx]; exact hu1)
  have h3 := real_continuous_dih_y_wrt5_jx y3 y1 y2 y6 y4 y5 hd2 hy3
    (by rw [upsX_swap12_jx]; exact hu3) (by rw [upsX_swap12_jx]; exact hu2)
  have hsum : ContinuousAt (fun q =>
      rho y1 * dihY y1 y2 y3 q y5 y6 +
        rho y2 * dihY y2 y3 y1 y5 y6 q +
        rho y3 * dihY y3 y1 y2 y6 q y5 - (Real.pi + sol0)) y4 :=
    (((continuousAt_const.mul h1).add (continuousAt_const.mul h2)).add
      (continuousAt_const.mul h3)).sub continuousAt_const
  refine hsum.congr ?_
  filter_upwards with q
  exact (taum_dih_y_p16 y1 y2 y3 q y5 y6).symm

/-- HOL `UPS_X_STD_POS` (BKOSSGE.hl:291); via PackingAuto18's
`TRI_UPS_X_STRICT_POS` with the `h0 = 1.26` box. -/
private theorem UPS_X_STD_POS_jx (y1 y2 y3 : ℝ) (h1 : 2 ≤ y1) (h1' : y1 ≤ 2 * h0)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ 2 * h0) (h3 : 2 ≤ y3) (h3' : y3 ≤ 2 * h0) :
    0 < upsX (y1 * y1) (y2 * y2) (y3 * y3) := by
  have h0v : h0 = 1.26 := rfl
  exact TRI_UPS_X_STRICT_POS y1 y2 y3 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

/-! ## Box-bounded attain-inf (HOL `JOTSWIX.hl:9`, with its six box hypotheses) -/

/-- HOL `taum_attains_inf` (JOTSWIX.hl:9) in its verbatim box-bounded form:
`taum` attains its minimum in the `y4` slot over `[2, 2 * h0]`.  Continuity of
`q => taum y1 y2 y3 q y5 y6` on the box comes from the three `deltaY > 0`
(registry `4717061266`) and the three `upsX > 0` (HOL `UPS_X_STD_POS`) side
conditions, exactly as in the HOL proof. -/
private theorem taum_attains_inf_box_jx (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y5 y6 : ℝ)
    (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0)
    (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    ∃ y4' ∈ Set.Icc (2 : ℝ) (2 * h0), ∀ y4 ∈ Set.Icc (2 : ℝ) (2 * h0),
      taum y1 y2 y3 y4' y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 := by
  have h471 : mainEstimate_4717061266 :=
    h "4717061266" (by simp [mainNonlinearTerminalV11Ids_t11])
  unfold mainEstimate_4717061266 at h471
  have h2h0 : (2 : ℝ) ≤ 2 * h0 := by rw [h0_eq_p22]; norm_num
  refine (isCompact_Icc (a := (2 : ℝ)) (b := 2 * h0)).exists_isMinOn
    (f := fun q => taum y1 y2 y3 q y5 y6) ⟨2, ?_⟩ ?_
  · exact ⟨le_rfl, h2h0⟩
  intro q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hqy : 0 < q := by linarith
  have hdY : 0 < deltaY y1 y2 y3 q y5 y6 :=
    h471 y1 y2 y3 q y5 y6 hy1 hy1' hy2 hy2' hy3 hy3' hq1 hq2 hy5 hy5' hy6 hy6'
  exact (real_continuous_taum_jx y1 y2 y3 q y5 y6 hdY (by linarith)
    (by linarith) (by linarith)
    (UPS_X_STD_POS_jx y1 y2 y6 hy1 hy1' hy2 hy2' hy6 hy6')
    (UPS_X_STD_POS_jx y2 y3 q hy2 hy2' hy3 hy3' hq1 hq2)
    (UPS_X_STD_POS_jx y1 y3 y5 hy1 hy1' hy3 hy3' hy5 hy5')).continuousWithinAt

/-! ## Section B: TAUM_EXTREMAL (HOL JOTSWIX.hl:48) -/

/-- HOL `TAUM_EXTREMAL` (JOTSWIX.hl:48): the attained minimiser of the `y4`
slot is at an endpoint.  HOL route: `taum_attains_inf`, then an interior-point
contradiction through `LEMMA_1834976363` (Ocbicby descent: a strictly better
interior point exists whenever the minimiser is strictly inside the box), with
the `xrr_simple_*` two-sided bounds feeding the lemma's `x4` window. -/
theorem TAUM_EXTREMAL_p23' (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2 * h0) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    ∃ y4' : ℝ, (y4' = 2 * h0 ∨ y4' = 2) ∧
      taum y1 y2 y3 y4' y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 := by
  obtain ⟨y4m, hy4m_mem, hmin⟩ :=
    taum_attains_inf_box_jx h y1 y2 y3 y5 y6 hy1 hy1' hy2 hy2' hy3 hy3'
      hy5 hy5' hy6 hy6'
  obtain ⟨hy4m1, hy4m2⟩ := hy4m_mem
  have hle : taum y1 y2 y3 y4m y5 y6 ≤ taum y1 y2 y3 y4 y5 y6 :=
    hmin y4 ⟨hy4, hy4'⟩
  have h2h0 : (2:ℝ) * h0 = 2.52 := by rw [h0_eq_p22]; norm_num
  by_cases hend : y4m = 2 * h0 ∨ y4m = 2
  · exact ⟨y4m, hend, hle⟩
  · exfalso
    have hne2h0 : y4m ≠ 2 * h0 := fun hc => hend (Or.inl hc)
    have hne2 : y4m ≠ 2 := fun hc => hend (Or.inr hc)
    have hlt2 : 2 < y4m := lt_of_le_of_ne hy4m1 (Ne.symm hne2)
    have hlth : y4m < 2 * h0 := lt_of_le_of_ne hy4m2 hne2h0
    have h471 : mainEstimate_4717061266 :=
      h "4717061266" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4717061266 at h471
    -- the two-sided `xrr y2 y3 y4m` window
    have hx4lo : (2 / h0) ^ 2 ≤ xrr y2 y3 y4m :=
      xrr_simple_lower_bound_p22 y2 y3 y4m 2 hy2 hy2' hy3 hy3' (by norm_num) hy4m1
    have hx4hi : xrr y2 y3 y4m ≤ 15.53 := by
      have hb := xrr_simple_upper_bound_p22 y2 y3 y4m 3.94 hy2 hy2' hy3 hy3'
        (by linarith) (by linarith) (by norm_num)
      calc xrr y2 y3 y4m ≤ (3.94:ℝ) ^ 2 := hb
        _ ≤ 15.53 := by norm_num
    have hx5 : (2 / h0) ^ 2 ≤ xrr y1 y3 y5 :=
      xrr_simple_lower_bound_p22 y1 y3 y5 2 hy1 hy1' hy3 hy3' (by norm_num) hy5
    have hx6 : (2 / h0) ^ 2 ≤ xrr y1 y2 y6 :=
      xrr_simple_lower_bound_p22 y1 y2 y6 2 hy1 hy1' hy2 hy2' (by norm_num) hy6
    -- the interval side-condition of LEMMA_1834976363 at `(2, 2 * h0)`
    have hsub : Set.Ioo (2:ℝ) (2 * h0) ⊆
        {y | 0 < deltaY y1 y2 y3 y y5 y6 ∧ 0 < y ∧
          0 < upsX (y2 * y2) (y3 * y3) (y * y)} := by
      rintro y ⟨hy2lt, hyh0lt⟩
      have hy2le : (2:ℝ) ≤ y := le_of_lt hy2lt
      have hyh0le : y ≤ 2 * h0 := le_of_lt hyh0lt
      exact ⟨h471 y1 y2 y3 y y5 y6 hy1 hy1' hy2 hy2' hy3 hy3' hy2le hyh0le
          hy5 hy5' hy6 hy6', by linarith,
        UPS_X_STD_POS_jx y2 y3 y hy2 hy2' hy3 hy3' hy2le hyh0le⟩
    obtain ⟨z, hz_mem, hz_lt⟩ :=
      LEMMA_1834976363_p22 h y1 y2 y3 y4m y5 y6 2 (2 * h0)
        ⟨hy1, hy1'⟩ ⟨hy2, hy2'⟩ ⟨hy3, hy3'⟩
        ⟨hx4lo, hx4hi⟩ hx5 hx6
        ⟨hlt2, hlth⟩ hsub (by linarith) (by linarith)
        (UPS_X_STD_POS_jx y1 y2 y6 hy1 hy1' hy2 hy2' hy6 hy6')
        (UPS_X_STD_POS_jx y1 y3 y5 hy1 hy1' hy3 hy3' hy5 hy5')
    have hzI : z ∈ Set.Icc (2:ℝ) (2 * h0) :=
      ⟨le_of_lt hz_mem.1, le_of_lt hz_mem.2⟩
    have hzge := hmin z hzI
    linarith


/-! ## Section C: TAUM_STD_POS (HOL JOTSWIX.hl:108) -/

/-- The `(123)(456)` rotation of `taum` (HOL `Terminal.taum_sym2`, used by the
`TAUM_STD_POS` argument to move the registry instantiations onto the rotated
tuples). -/
private theorem taum_rot_jx (a b c d e f : ℝ) :
    taum a b c d e f = taum b c a e f d := by
  rw [(taum_sym2 a b c d e f).1, (taum_sym2 b a c e d f).2]

/-- The `(132)(465)` (inverse) rotation. -/
private theorem taum_rotInv_jx (a b c d e f : ℝ) :
    taum a b c d e f = taum c a b f d e := by
  rw [taum_rot_jx a b c d e f, taum_rot_jx b c a e f d]

/-- HOL `TAUM_STD_POS` (JOTSWIX.hl:108): `taum >= 0` on the box.  HOL route:
three rounds of `TAUM_EXTREMAL` (push `y4`, then `y5`, then `y6` to an
endpoint), each non-`2` endpoint contradicted by registry `5541487347`
(`taum > 0.103`), and the final all-`2` corner by registry
`OMKYNLT 3336871894` (`taum >= 0`). -/
theorem TAUM_STD_POS_p23' (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 2 ≤ y1) (hy1' : y1 ≤ 2 * h0)
    (hy2 : 2 ≤ y2) (hy2' : y2 ≤ 2 * h0) (hy3 : 2 ≤ y3) (hy3' : y3 ≤ 2 * h0)
    (hy4 : 2 ≤ y4) (hy4' : y4 ≤ 2 * h0) (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * h0)
    (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * h0) :
    0 ≤ taum y1 y2 y3 y4 y5 y6 := by
  by_contra hneg
  rw [not_le] at hneg
  have h2h0 : (2:ℝ) * h0 = 2.52 := by rw [h0_eq_p22]; norm_num
  have h2le : (2:ℝ) ≤ 2 * h0 := by linarith
  have hsqrt8 : (2 : ℝ) * h0 ≤ Real.sqrt 8 := by
    have := sqrt8_flyspeck_p22.1
    linarith
  have h554 : mainEstimate_5541487347 :=
    h "5541487347" (by simp [mainNonlinearTerminalV11Ids_t11])
  unfold mainEstimate_5541487347 at h554
  have hOMK : mainEstimate_OMKYNLT_3336871894 :=
    h "OMKYNLT 3336871894" (by simp [mainNonlinearTerminalV11Ids_t11])
  unfold mainEstimate_OMKYNLT_3336871894 at hOMK
  -- ## y4 round
  obtain ⟨y4a, hy4a_end, hmin4⟩ :=
    TAUM_EXTREMAL_p23' h y1 y2 y3 y4 y5 y6 hy1 hy1' hy2 hy2' hy3 hy3'
      hy4 hy4' hy5 hy5' hy6 hy6'
  have h4a_neg : taum y1 y2 y3 y4a y5 y6 < 0 := lt_of_le_of_lt hmin4 hneg
  rcases hy4a_end with h4a | h4a
  · -- y4a = 2 * h0: registry `5541487347` on the rotated tuple
    have hgt : taum y1 y2 y3 y4a y5 y6 > 0.103 := by
      have hreg := h554 y2 y3 y1 y5 y6 y4a
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)
        (by linarith) (h4a ▸ hsqrt8)
      simpa only [taum_rot_jx y1 y2 y3 y4a y5 y6] using hreg
    linarith
  · -- y4a = 2
    have h4a2 : taum y2 y3 y1 y5 y6 2 < 0 := by
      have h0 := h4a_neg
      rw [h4a] at h0
      simpa only [taum_rot_jx y1 y2 y3 2 y5 y6] using h0
    -- ## y5 round: extremal on the rotated tuple `(y2,y3,y1,2,y6,y5)`'s sibling
    obtain ⟨y5a, hy5a_end, hmin5⟩ :=
      TAUM_EXTREMAL_p23' h y2 y3 y1 y5 y6 2 hy2 hy2' hy3 hy3' hy1 hy1'
        hy5 hy5' hy6 hy6' (by norm_num) h2le
    have h5a_neg : taum y2 y3 y1 y5a y6 2 < 0 := lt_of_le_of_lt hmin5 h4a2
    rcases hy5a_end with h5a | h5a
    · -- y5a = 2 * h0
      have hgt : taum y2 y3 y1 y5a y6 2 > 0.103 := by
        have hreg := h554 y3 y1 y2 y6 2 y5a
          (by linarith) (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith)
          (by linarith) (h5a ▸ hsqrt8)
        simpa only [taum_rot_jx y2 y3 y1 y5a y6 2] using hreg
      linarith
    · -- y5a = 2
      have h5a2 : taum y1 y2 y3 2 2 y6 < 0 := by
        have h0 := h5a_neg
        rw [h5a] at h0
        simpa only [taum_rot_jx y1 y2 y3 2 2 y6] using h0
      -- ## y6 round
      obtain ⟨y6a, hy6a_end, hmin6⟩ :=
        TAUM_EXTREMAL_p23' h y3 y1 y2 y6 2 2 hy3 hy3' hy1 hy1' hy2 hy2'
          hy6 hy6' (by norm_num) h2le (by norm_num) h2le
      have hrot6 : taum y1 y2 y3 2 2 y6 = taum y3 y1 y2 y6 2 2 :=
        taum_rotInv_jx y1 y2 y3 2 2 y6
      have h6a_neg : taum y3 y1 y2 y6a 2 2 < 0 := by
        refine lt_of_le_of_lt hmin6 ?_
        rw [← hrot6]; exact h5a2
      rcases hy6a_end with h6a | h6a
      · -- y6a = 2 * h0
        have hgt : taum y3 y1 y2 y6a 2 2 > 0.103 := by
          have hreg := h554 y1 y2 y3 2 2 y6a
            (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith)
            (by linarith) (h6a ▸ hsqrt8)
          have hrot6' : taum y1 y2 y3 2 2 y6a = taum y3 y1 y2 y6a 2 2 :=
            taum_rotInv_jx y1 y2 y3 2 2 y6a
          simpa only [hrot6'] using hreg
        linarith
      · -- y6a = 2: registry `OMKYNLT 3336871894` at the all-`2` corner
        have h6a2 : taum y1 y2 y3 2 2 2 < 0 := by
          have h0 := h6a_neg
          rw [h6a] at h0
          simpa only [taum_rotInv_jx y1 y2 y3 2 2 2] using h0
        have hnonneg : taum y1 y2 y3 2 2 2 ≥ (0.0 : ℝ) :=
          hOMK y1 y2 y3 2 2 2
            (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        linarith


/-! ## Section D: LFLACKU (HOL JOTSWIX.hl:191) -/

/-- HOL `LFLACKU` (JOTSWIX.hl:191): `scs_arrow_v39 {scs_3I1} {}`.  HOL route:
`pos_imp_scs_arrow_empty` + `taustar_taum_dfun` at
`scs_3I1 = mk_unadorned_v39 3 (d_tame 3) (cs_adj 3 2 (2 h0)) (cs_adj 3 (2 h0) 6)`;
`d_tame 3 = 0 != 0.11` fails `is_ear_v39`, the empty `J` kills the
`0.1 * (+-1) * (...)` truncation term, and the residue is exactly
`TAUM_STD_POS`. -/
theorem LFLACKU_p23' (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs3I1} ∅ := by
  refine pos_imp_scs_arrow_empty_p22 scs3I1 ?_
  intro vv hB
  have e_a01 : csAdj 3 2 (2 * h0) 0 1 = 2 := by norm_num [csAdj]
  have e_a12 : csAdj 3 2 (2 * h0) 1 2 = 2 := by norm_num [csAdj]
  have e_a02 : csAdj 3 2 (2 * h0) 0 2 = 2 := by norm_num [csAdj]
  have e_b01 : csAdj 3 (2 * h0) 6 0 1 = 2 * h0 := by norm_num [csAdj]
  have e_b12 : csAdj 3 (2 * h0) 6 1 2 = 2 * h0 := by norm_num [csAdj]
  have e_b02 : csAdj 3 (2 * h0) 6 0 2 = 2 * h0 := by norm_num [csAdj]
  have hd0 : dTame 3 = 0 := by norm_num [dTame]
  have hE : ¬ isEarV39 (ScsV39.mk 3 (dTame 3) (csAdj 3 2 (2 * h0))
      (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) (csAdj 3 (2 * h0) 6)
      (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False)) := by
    intro hear
    have hd11 : (dTame 3) = 0.11 := hear.2.2.2.1
    rw [hd0] at hd11
    norm_num at hd11
  have hB' : BBsV39 (ScsV39.mk 3 (dTame 3) (csAdj 3 2 (2 * h0))
      (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) (csAdj 3 (2 * h0) 6)
      (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False)) vv := by
    simpa only [scs3I1, mkUnadornedV39] using hB
  have hmain : 0 ≤ taustarV39 (ScsV39.mk 3 (dTame 3) (csAdj 3 2 (2 * h0))
      (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) (csAdj 3 (2 * h0) 6)
      (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False)) vv := by
    classical
    refine taustar_taum_dfun (dTame 3) (csAdj 3 2 (2 * h0))
      (csAdj 3 (2 * h0) 6) (fun _ _ => False)
      (by norm_num [csAdj]) (by norm_num [csAdj]) (by norm_num [csAdj])
      (by norm_num [csAdj, h0_eq_p22]) (by norm_num [csAdj, h0_eq_p22])
      (by norm_num [csAdj, h0_eq_p22]) ?_ vv hB'
    intro y1 y2 y3 y4 y5 y6 hy1 hy1' hy2 hy2' hy3 hy3' hy6l hy6u hy4l hy4u hy5l hy5u hdelta
    rw [e_a01] at hy6l
    rw [e_b01] at hy6u
    rw [e_a12] at hy4l
    rw [e_b12] at hy4u
    rw [e_a02] at hy5l
    rw [e_b02] at hy5u
    have hpos := TAUM_STD_POS_p23' h y1 y2 y3 y4 y5 y6 hy1 hy1' hy2 hy2' hy3 hy3'
      hy4l hy4u hy5l hy5u hy6l hy6u
    have hiff : (if isEarV39 (ScsV39.mk 3 (dTame 3) (csAdj 3 2 (2 * h0))
        (csAdj 3 2 (2 * h0)) (csAdj 3 (2 * h0) 6) (csAdj 3 (2 * h0) 6)
        (fun _ _ => False) (fun _ => False) (fun _ => False) (fun _ => False))
        then (1:ℝ) else -1) = -1 := if_neg hE
    rw [hiff, hd0]
    norm_num
    exact hpos
  simpa only [scs3I1, mkUnadornedV39] using hmain


end Kepler.Text
