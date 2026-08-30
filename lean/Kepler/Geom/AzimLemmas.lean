/-
Kepler.Geom.AzimLemmas — AZIM_EQ 引理族（flyspeck.ml:2509–2680，Lean 移植）

源：HOL Light `Multivariate/flyspeck.ml`（AZIM_REFL:2509 / AZIM_EQ:2522 /
AZIM_EQ_ALT:2571 / AZIM_EQ_0:2577 / AZIM_EQ_0_ALT:2586 / AZIM_COMPL_EQ_0:2617 /
AZIM_COMPL:2632 / AZIM_EQ_0_SYM:2661）。

证明路线（替代 HOL 的 GEOM_ORIGIN_TAC / AZIM_ARG）：
- `azim_frame_spec`：把 azim 的 AzimSpec 在给定标架展开为 zOf 坐标的
  极表示（z₁ = r₁ e^{iψ}，z₂ = r₂ e^{i(ψ+θ)}）。
- AZIM_EQ ⇔ 两 z 坐标相差正实数倍 ⇔ 射线表示（affGt_pair_iff）。
- AZIM_COMPL：单位相位乘积为 1 ⟹ θ₁₂ + θ₂₁ ∈ {0, 2π}。
-/

import Kepler.Geom.Azim
import Kepler.Geom.Aff

open Classical
open Complex

namespace Kepler.Geom

/-! ## zOf 的线性性 -/

theorem zOf_add (e1 e2 p q : V3) :
    zOf e1 e2 (p + q) = zOf e1 e2 p + zOf e1 e2 q := by
  show ((p + q : V3) ⬝ᵥ e1) + ((p + q : V3) ⬝ᵥ e2) * I
      = ((p : V3) ⬝ᵥ e1 + (p : V3) ⬝ᵥ e2 * I)
        + ((q : V3) ⬝ᵥ e1 + (q : V3) ⬝ᵥ e2 * I)
  simp only [WithLp.ofLp_add, add_dotProduct]
  push_cast
  ring

theorem zOf_smul (e1 e2 : V3) (c : ℝ) (x : V3) :
    zOf e1 e2 (c • x) = ((c : ℝ) : ℂ) * zOf e1 e2 x := by
  show ((c • x : V3) ⬝ᵥ e1) + ((c • x : V3) ⬝ᵥ e2) * I
      = ((c : ℝ) : ℂ) * ((x : V3) ⬝ᵥ e1 + (x : V3) ⬝ᵥ e2 * I)
  simp only [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

theorem zOf_axis {v w e1 e2 e3 : V3} (hax : (w - v : V3) = dist w v • e3)
    (he : Orthonormal3 e1 e2 e3) : zOf e1 e2 (w - v) = 0 := by
  obtain ⟨hp1, hp2⟩ := axis_perp hax he
  show ((w - v : V3) ⬝ᵥ e1) + ((w - v : V3) ⬝ᵥ e2) * I = 0
  rw [hp1, hp2]
  push_cast
  ring

/-! ## 指数周期工具 -/

theorem exp_unit_norm (t : ℝ) : ‖Complex.exp (t * I)‖ = 1 := by
  rw [Complex.norm_exp,
    show ((t : ℂ) * Complex.I).re = 0 from by simp [Complex.mul_re],
    Real.exp_zero]

/-- 正实数倍的单位相位唯一。 -/
theorem exp_pos_mul_eq {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ((a : ℝ) : ℂ) * Complex.exp (α * I)
      = ((b : ℝ) : ℂ) * Complex.exp (β * I)) :
    Complex.exp (α * I) = Complex.exp (β * I) := by
  have hna : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hnb : ‖((b : ℝ) : ℂ)‖ = b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  rw [Complex.norm_mul, Complex.norm_mul, exp_unit_norm, exp_unit_norm,
    hna, hnb, mul_one, mul_one] at hn
  have hca : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine mul_left_cancel₀ hca ?_
  rw [← hn] at h
  exact h


/-- 区间 [0, 2π) 内由单位相位确定角度。 -/
theorem angle_eq_of_exp_eq {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 2 * Real.pi)
    (hβ0 : 0 ≤ β) (hβ1 : β < 2 * Real.pi)
    (h : Complex.exp (α * I) = Complex.exp (β * I)) : α = β := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hc2 : ((α : ℝ) : ℂ) * Complex.I
      = ((β + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hc3 : ((α : ℝ) : ℂ) = ((β + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hc2
  have hα2 : α = β + (n:ℝ) * (2 * Real.pi) := by exact_mod_cast hc3
  have hn0 : n = 0 := by
    by_contra hne
    rcases Int.lt_trichotomy n 0 with h1 | h1 | h1
    · have hle : ((n:ℤ) : ℝ) ≤ -1 := by
        have := (by omega : (n : ℤ) ≤ -1)
        exact_mod_cast this
      have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle h2pi.le
      linarith
    · exact hne h1
    · have hge : ((n:ℤ) : ℝ) ≥ 1 := by
        have := (by omega : (n : ℤ) ≥ 1)
        exact_mod_cast this
      have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hge h2pi.le
      linarith
  rw [hn0, Int.cast_zero, zero_mul, add_zero] at hα2
  exact hα2

theorem exp_add_I (a b : ℝ) :
    Complex.exp (((a + b : ℝ) : ℂ) * I)
      = Complex.exp (((a : ℝ) : ℂ) * I) * Complex.exp (((b : ℝ) : ℂ) * I) := by
  push_cast
  rw [add_mul, Complex.exp_add]

/-! ## azim 的标架极表示 -/

/-- AzimSpec 在标架处的极坐标展开（z₁ = r₁ e^{iψ}，z₂ = r₂ e^{i(ψ+azim)}）。 -/
theorem azim_frame_spec (h1 : ¬ Collinear3 v w w1) (h2 : ¬ Collinear3 v w w2)
    (he : Orthonormal3 e1 e2 e3) (hax : (w - v : V3) = dist w v • e3)
    (hw : w ≠ v) :
    ∃ psi r1 r2 : ℝ, 0 < r1 ∧ 0 < r2 ∧
      zOf e1 e2 (w1 - v) = ((r1 : ℝ) : ℂ) * Complex.exp (((psi : ℝ) : ℂ) * I) ∧
      zOf e1 e2 (w2 - v) = ((r2 : ℝ) : ℂ) * Complex.exp
        ((((psi + azim v w w1 w2 : ℝ) : ℂ)) * I) := by
  have hspec : AzimSpec v w w1 w2 (azim v w w1 w2) := by
    unfold azim
    rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h])]
    exact Classical.epsilon_spec (azimSpec_exists h1 h2)
  unfold AzimSpec at hspec
  obtain ⟨hz1, hz2, h1v, h2v, hframes⟩ := hspec
  obtain ⟨psi, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframes e1 e2 e3 he hax hw
  exact ⟨psi, r1, r2, hr1, hr2, zOf_of_rep he hax hrep1, zOf_of_rep he hax hrep2⟩

/-- z 坐标成正实数倍 ⟹ 射线表示。 -/
theorem rep_smul_of_zOf (he : Orthonormal3 e1 e2 e3)
    (hax : (w - v : V3) = dist w v • e3) (hw : w ≠ v) (x y : V3) (c : ℝ)
    (hzy : zOf e1 e2 (y - v) = ((c : ℝ) : ℂ) * zOf e1 e2 (x - v)) :
    ∃ h : ℝ, y - v = c • (x - v) + h • (w - v) := by
  have hd : 0 < dist w v := dist_pos.mpr hw
  have hre : (y - v : V3) ⬝ᵥ e1 = c * ((x - v : V3) ⬝ᵥ e1) := by
    have h := congrArg Complex.re hzy
    simpa [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      mul_one, sub_zero] using h
  have him : (y - v : V3) ⬝ᵥ e2 = c * ((x - v : V3) ⬝ᵥ e2) := by
    have h := congrArg Complex.im hzy
    simpa [zOf, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, add_zero,
      zero_add] using h
  set b1 := ((x - v : V3) ⬝ᵥ e1) with hb1
  set b2 := ((x - v : V3) ⬝ᵥ e2) with hb2
  set b3 := ((x - v : V3) ⬝ᵥ e3) with hb3
  have hexpY := on3_expand he (y - v)
  have hexpX := on3_expand he (x - v)
  set a3 := ((y - v : V3) ⬝ᵥ e3) with ha3
  rw [hre, him] at hexpY
  refine ⟨(a3 - c * b3) / dist w v, ?_⟩
  rw [hax, smul_smul, div_mul_cancel₀ _ hd.ne']
  rw [hexpY, hexpX]
  module


/-! ## AZIM_EQ 引理族 -/

theorem collinear3_pair_left {v0 v1 x : V3} (h : x = v0) : Collinear3 v0 v1 x := by
  show Collinear ℝ ({v0, v1, x} : Set V3)
  rw [h]
  have hset : ({v0, v1, v0} : Set V3) = {v0, v1} := by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact collinear_pair ℝ v0 v1

theorem collinear3_pair_right {v0 v1 x : V3} (h : x = v1) : Collinear3 v0 v1 x := by
  show Collinear ℝ ({v0, v1, x} : Set V3)
  rw [h]
  have hset : ({v0, v1, v1} : Set V3) = {v0, v1} := by ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact collinear_pair ℝ v0 v1

/-- 正实数倍消除：`a p = b q → ∃ c > 0, p = c q`。 -/
private theorem z_eq_of_pos_mul {p q : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ((a : ℝ) : ℂ) * p = ((b : ℝ) : ℂ) * q) (hq : q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ p = ((c : ℝ) : ℂ) * q := by
  refine ⟨b / a, by positivity, ?_⟩
  have hca : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have key : ((a : ℝ) : ℂ) * p = ((a : ℝ) : ℂ) * (((b / a : ℝ) : ℂ) * q) := by
    rw [show ((a : ℝ) : ℂ) * (((b / a : ℝ) : ℂ) * q) = ((b : ℝ) : ℂ) * q from by
      push_cast
      field_simp]
    exact h
  exact mul_left_cancel₀ hca key

/-- HOL AZIM_EQ（flyspeck.ml:2522）：
`azim v0 v1 w x = azim v0 v1 w y ↔ y ∈ aff_gt {v0,v1} {x}`。 -/
theorem azim_eq_azim_iff (hw : ¬ Collinear3 v0 v1 w) (hx : ¬ Collinear3 v0 v1 x)
    (hy : ¬ Collinear3 v0 v1 y) :
    azim v0 v1 w x = azim v0 v1 w y ↔ y ∈ affGt {v0, v1} {x} := by
  have hwv : v1 ≠ v0 := fun he => hw (collinear3_of_eq he)
  have hx0 : x ≠ v0 := fun he => hx (collinear3_pair_left he)
  have hx1 : x ≠ v1 := fun he => hx (collinear3_pair_right he)
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v1 - v0)
    (sub_ne_zero.mpr hwv)
  have hax : (v1 - v0 : V3) = dist v1 v0 • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψx, r1, rx, hr1, hrx, hzw1, hzx⟩ := azim_frame_spec hw hx hon hax hwv
  obtain ⟨ψy, r1', ry, hr1', hry, hzw2, hzy⟩ := azim_frame_spec hw hy hon hax hwv
  have hunit : Complex.exp (((ψx : ℝ) : ℂ) * I) = Complex.exp (((ψy : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw2)
  have hzxd : zOf f1 f2 (x - v0)
      = ((rx : ℝ) : ℂ) * (Complex.exp (((ψx : ℝ) : ℂ) * I)
        * Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I)) := by
    rw [← exp_add_I]
    exact hzx
  have hzyd : zOf f1 f2 (y - v0)
      = ((ry : ℝ) : ℂ) * (Complex.exp (((ψy : ℝ) : ℂ) * I)
        * Complex.exp (((azim v0 v1 w y : ℝ) : ℂ) * I)) := by
    rw [← exp_add_I]
    exact hzy
  have hzxne : zOf f1 f2 (x - v0) ≠ 0 := by
    rw [hzxd]
    exact mul_ne_zero (by exact_mod_cast hrx.ne')
      (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
  constructor
  · intro heq
    rw [← heq] at hzyd
    have hkey : ((rx : ℝ) : ℂ) * zOf f1 f2 (y - v0)
        = ((ry : ℝ) : ℂ) * zOf f1 f2 (x - v0) := by
      rw [hzyd, hzxd, hunit]
      ring
    obtain ⟨c, hcpos, hzy2⟩ := z_eq_of_pos_mul hrx hry hkey hzxne
    exact affGt_pair_iff (v0 := v0) (v1 := v1) (x := x) (y := y) (Ne.symm hwv) hx0 hx1 |>.mpr
      ⟨c, hcpos, rep_smul_of_zOf hon hax hwv x y c hzy2⟩
  · intro hmem
    obtain ⟨c, hc, hcoeff⟩ :=
      (affGt_pair_iff (v0 := v0) (v1 := v1) (x := x) (y := y) (Ne.symm hwv) hx0 hx1).mp hmem
    obtain ⟨hh, hcoeq⟩ := hcoeff
    have hzy2 : zOf f1 f2 (y - v0) = ((c : ℝ) : ℂ) * zOf f1 f2 (x - v0) := by
      conv_lhs => rw [hcoeq]
      rw [zOf_add, zOf_smul, zOf_smul, zOf_axis hax hon]
      push_cast
      ring
    have hzyc : zOf f1 f2 (y - v0)
        = ((c * rx : ℝ) : ℂ) * (Complex.exp (((ψx : ℝ) : ℂ) * I)
          * Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I)) := by
      rw [hzy2, hzxd]
      push_cast
      ring
    -- 范数桥：ry = c * rx
    have hnorm : (ry : ℝ) = c * rx := by
      have hny : ‖zOf f1 f2 (y - v0)‖ = ry := by
        rw [hzyd, Complex.norm_mul, Complex.norm_mul, exp_unit_norm, exp_unit_norm,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hry, mul_one]
        norm_num
      have hnx : ‖zOf f1 f2 (x - v0)‖ = rx := by
        rw [hzxd, Complex.norm_mul, Complex.norm_mul, exp_unit_norm, exp_unit_norm,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrx, mul_one]
        norm_num
      rw [hzy2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc, hnx] at hny
      exact hny.symm
    have hzyc' : zOf f1 f2 (y - v0)
        = ((ry : ℝ) : ℂ) * (Complex.exp (((ψx : ℝ) : ℂ) * I)
          * Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I)) := by
      rw [hzyc, show ((c * rx : ℝ) : ℂ) = ((ry : ℝ) : ℂ) from by
        push_cast
        exact_mod_cast hnorm.symm]
    have hpp : Complex.exp (((ψy : ℝ) : ℂ) * I)
          * Complex.exp (((azim v0 v1 w y : ℝ) : ℂ) * I)
        = Complex.exp (((ψx : ℝ) : ℂ) * I)
          * Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I) := by
      have hcry : ((ry : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hry.ne'
      have hkey : ((ry : ℝ) : ℂ) * (Complex.exp (((ψy : ℝ) : ℂ) * I)
            * Complex.exp (((azim v0 v1 w y : ℝ) : ℂ) * I))
          = ((ry : ℝ) : ℂ) * (Complex.exp (((ψx : ℝ) : ℂ) * I)
            * Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I)) :=
        hzyd.symm.trans hzyc'
      exact mul_left_cancel₀ hcry hkey
    have hθeq : Complex.exp (((azim v0 v1 w y : ℝ) : ℂ) * I)
        = Complex.exp (((azim v0 v1 w x : ℝ) : ℂ) * I) := by
      rw [hunit] at hpp
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) hpp
    exact (angle_eq_of_exp_eq (azim_nonneg v0 v1 w y) (azim_lt_two_pi v0 v1 w y)
      (azim_nonneg v0 v1 w x) (azim_lt_two_pi v0 v1 w x) hθeq).symm

/-- HOL AZIM_EQ_ALT（flyspeck.ml:2571）。 -/
theorem azim_eq_azim_iff_alt (hw : ¬ Collinear3 v0 v1 w) (hx : ¬ Collinear3 v0 v1 x)
    (hy : ¬ Collinear3 v0 v1 y) :
    azim v0 v1 w x = azim v0 v1 w y ↔ x ∈ affGt {v0, v1} {y} := by
  have h := azim_eq_azim_iff hw hy hx
  constructor
  · intro he
    exact h.mp he.symm
  · intro hmem
    exact (h.mpr hmem).symm

/-- HOL AZIM_EQ_0（flyspeck.ml:2577）。 -/
theorem azim_eq_zero_iff (hw : ¬ Collinear3 v0 v1 w) (hx : ¬ Collinear3 v0 v1 x) :
    azim v0 v1 w x = 0 ↔ w ∈ affGt {v0, v1} {x} := by
  have h := azim_eq_azim_iff hw hx hw
  rw [azim_self] at h
  constructor
  · intro h0
    exact h.mp h0
  · intro hmem
    exact h.mpr hmem

/-- HOL AZIM_EQ_0_ALT（flyspeck.ml:2586）。 -/
theorem azim_eq_zero_iff_alt (hw : ¬ Collinear3 v0 v1 w) (hx : ¬ Collinear3 v0 v1 x) :
    azim v0 v1 w x = 0 ↔ x ∈ affGt {v0, v1} {w} := by
  have h := azim_eq_azim_iff (v0 := v0) (v1 := v1) (w := w) (x := w) (y := x) hw hw hx
  rw [azim_self] at h
  constructor
  · intro h0
    exact h.mp h0.symm
  · intro hmem
    exact (h.mpr hmem).symm

/-- HOL AZIM_COMPL（flyspeck.ml:2632）。 -/
theorem azim_compl (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2) :
    azim z w w2 w1 = if azim z w w1 w2 = 0 then 0
      else 2 * Real.pi - azim z w w1 w2 := by
  have hwz : w ≠ z := fun he => h1 (collinear3_of_eq he)
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (w - z)
    (sub_ne_zero.mpr hwz)
  have hax : (w - z : V3) = dist w z • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec h1 h2 hon hax hwz
  obtain ⟨ψ', r1', r2', hr1', hr2', hz1', hz2'⟩ := azim_frame_spec h2 h1 hon hax hwz
  -- z2 的两种表示：↑r2 e^{i(ψ+θ12)} 与 ↑r1' e^{iψ'}
  have hz2unit : Complex.exp ((((ψ + azim z w w1 w2 : ℝ) : ℂ)) * I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hr2 hr1' (hz2.symm.trans hz1')
  -- z1 的两种表示：↑r1 e^{iψ} 与 ↑r2' e^{i(ψ'+θ21)}
  have hz1unit : Complex.exp (((ψ : ℝ) : ℂ) * I)
      = Complex.exp ((((ψ' + azim z w w2 w1 : ℝ) : ℂ)) * I) :=
    exp_pos_mul_eq hr1 hr2' (hz1.symm.trans hz2')
  rw [exp_add_I] at hz2unit
  rw [exp_add_I] at hz1unit
  -- 单位相位乘积为 1
  have hsumexp : Complex.exp (((azim z w w1 w2 : ℝ) : ℂ) * I)
      * Complex.exp (((azim z w w2 w1 : ℝ) : ℂ) * I) = 1 := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * I)
        * (Complex.exp (((azim z w w1 w2 : ℝ) : ℂ) * I)
          * Complex.exp (((azim z w w2 w1 : ℝ) : ℂ) * I))
        = Complex.exp (((ψ : ℝ) : ℂ) * I) * 1 := by
      rw [mul_one, ← mul_assoc, hz2unit, ← hz1unit]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hrng : 0 ≤ azim z w w1 w2 + azim z w w2 w1
      ∧ azim z w w1 w2 + azim z w w2 w1 < 4 * Real.pi :=
    ⟨add_nonneg (azim_nonneg z w w1 w2) (azim_nonneg z w w2 w1),
      by linarith [azim_lt_two_pi z w w1 w2, azim_lt_two_pi z w w2 w1]⟩
  have hdisc : azim z w w1 w2 + azim z w w2 w1 = 0 ∨
      azim z w w1 w2 + azim z w w2 w1 = 2 * Real.pi := by
    have he : Complex.exp (((azim z w w1 w2 + azim z w w2 w1 : ℝ) : ℂ) * I)
        = Complex.exp (((0:ℝ) : ℂ) * I) := by
      rw [exp_add_I, hsumexp]
      simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    have hc2 : ((azim z w w1 w2 + azim z w w2 w1 : ℝ) : ℂ) * Complex.I
        = (((n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hn]
      push_cast
      ring
    have hc3 : ((azim z w w1 w2 + azim z w w2 w1 : ℝ) : ℂ)
        = (((n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
      mul_right_cancel₀ Complex.I_ne_zero hc2
    have hsum : azim z w w1 w2 + azim z w w2 w1 = (n:ℝ) * (2 * Real.pi) := by
      exact_mod_cast hc3
    have hn01 : n = 0 ∨ n = 1 := by
      rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
      · exfalso
        have hle : ((n:ℤ) : ℝ) ≤ -1 := by
          have := (by omega : (n : ℤ) ≤ -1)
          exact_mod_cast this
        have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hle h2pi.le
        linarith
      · exact Or.inl hzero
      · by_contra hne2
        have hge : ((n:ℤ) : ℝ) ≥ 2 := by
          have := (by omega : (n : ℤ) ≥ 2)
          exact_mod_cast this
        have hmul : (n:ℝ) * (2 * Real.pi) ≥ (2:ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hge h2pi.le
        linarith
    rcases hn01 with h0 | h1'
    · exact Or.inl (by rw [hsum, h0]; norm_num)
    · have hn1 : ((n:ℝ)) = 1 := by exact_mod_cast h1'
      rw [hsum, hn1]
      norm_num
  by_cases h0 : azim z w w1 w2 = 0
  · rw [if_pos h0]
    rcases hdisc with h1' | h2'
    · linarith
    · exfalso
      linarith [h2', h0, azim_lt_two_pi z w w2 w1]
  · have h0' : (0:ℝ) < azim z w w1 w2 :=
      lt_of_le_of_ne (azim_nonneg z w w1 w2) (fun he => h0 he.symm)
    rw [if_neg h0]
    rcases hdisc with h1' | h2'
    · exfalso
      linarith [h1', azim_nonneg z w w2 w1, h0']
    · linarith

/-- HOL AZIM_COMPL_EQ_0（flyspeck.ml:2617）。 -/
theorem azim_compl_eq_zero (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2)
    (h0 : azim z w w1 w2 = 0) : azim z w w2 w1 = 0 := by
  rw [azim_compl h1 h2, if_pos h0]

/-- HOL AZIM_EQ_0_SYM（flyspeck.ml:2661）。 -/
theorem azim_eq_zero_symm (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2) :
    (azim z w w1 w2 = 0 ↔ azim z w w2 w1 = 0) :=
  ⟨azim_compl_eq_zero h1 h2, azim_compl_eq_zero h2 h1⟩

end Kepler.Geom
