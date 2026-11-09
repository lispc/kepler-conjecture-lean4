/-
LocalAuto7W12A: W12(a) 前置件 —— HOL `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`
(polar_fan.hl:188-226) 的第一个依赖：`AZIM_EQ_PI_ALT` 的**私有移植**
（参照 LocalAuto14:6390 的 public 版与 LocalAuto2:1812 的 private 版；
**不 import LocalAuto14**——实测其 private 名与 LA7 冲突）。

本文件件表（W12(a) 三件的 1、2；件 3 主代数待批）：
* `p12a_affsign_single` / `p12a_smul_mem_affLt`（私）：`t•u ∈ affLt {0} {u}`（t<0）。
* `p12a_affLt_coeffs` / `p12a_affLt_of_coeffs`：`affLt {0,u} {v}` 的三系数
  双向刻画（HOL `AFF_LT_2_1` 的 0 心形）——`p12a_azim_pi_alt` 正反向都要用。
* **`p12a_azim_pi_alt`**（HOL `AZIM_EQ_PI_ALT`）：
  `azim 0 u v w = π ↔ w ∈ affLt {0,u} {v}`（两非共线前提）。
-/
import Kepler.Text.LocalAuto7

namespace Kepler.Text

open Kepler.Geom Set Classical Complex

/-! ## 件 2：`affLt` 的系数刻画（`p12a_` 私/公开引理） -/

/-- Affsign 两点表示（`x` 系数自由、`u` 的系数按 `sgn`；LA14 `w16_affsign_single`
的自足转写）。 -/
private theorem p12a_affsign_single {x u y : V3} (hxu : x ≠ u) {t1 t2 : ℝ}
    (hy : y = t1 • x + t2 • u) (hsum : t1 + t2 = 1) {sgn : ℝ → Prop} (h2 : sgn t2) :
    Affsign sgn ({x} : Set V3) ({u} : Set V3) y := by
  have hfin : (({x} : Set V3) ∪ {u}).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton u)
  have hT : hfin.toFinset = ({x, u} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun w => if w = u then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [hT, Finset.sum_insert (by simp [hxu]), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxu, smul_zero, zero_add]
    exact hy
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simpa using h2
  · rw [hT, Finset.sum_insert (by simp [hxu]), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxu]
    exact hsum

/-- `t • u ∈ affLt {0} {u}`（`t < 0`）。 -/
theorem p12a_smul_mem_affLt {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : t < 0) :
    t • u ∈ affLt ({0} : Set V3) ({u} : Set V3) :=
  p12a_affsign_single (x := 0) (u := u) (y := t • u) (sgn := fun x => x < 0)
    (by simpa using hu.symm) (t1 := 1 - t) (t2 := t) (by simp) (by ring)
    (by simpa using ht)

/-- `affLt {0,u} {v}` 的三系数提取（LA14 `w16_affLt_coeffs` 的自足转写）。 -/
theorem p12a_affLt_coeffs {u v w : V3} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hw : w ∈ affLt ({0, u} : Set V3) ({v} : Set V3)) :
    ∃ t1 t2 t3 : ℝ, t3 < 0 ∧ t1 + t2 + t3 = 1 ∧ w = t1 • (0 : V3) + t2 • u + t3 • v := by
  obtain ⟨f, hfin, hsum, hneg, hone⟩ := hw
  have htf : hfin.toFinset = ({0, u, v} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨f 0, f u, f v, hneg v (by simp), ?_, ?_⟩
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton] at hone
    linarith
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton] at hsum
    rw [hsum]
    abel

/-- 三系数形构造回 `affLt {0,u} {v}`（LA14 `w16_affLt_of_coeffs` 的自足转写）。 -/
theorem p12a_affLt_of_coeffs {u v w : V3} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    {t1 t2 t3 : ℝ} (ht3 : t3 < 0) (hsum : t1 + t2 + t3 = 1)
    (hrep : w = t1 • (0 : V3) + t2 • u + t3 • v) :
    w ∈ affLt ({0, u} : Set V3) ({v} : Set V3) := by
  have hfin : (({0, u} : Set V3) ∪ {v} : Set V3).Finite :=
    ((Set.finite_singleton u).insert 0).union (Set.finite_singleton v)
  have htf : hfin.toFinset = ({0, u, v} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨fun q => if q = v then t3 else if q = u then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
    simp [hu0.symm, hv0.symm, huv]
    simpa using hrep
  · intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst hq
    simp [hu0.symm, hv0.symm, huv]
    exact ht3
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
    simp [hu0.symm, hv0.symm, huv]
    linarith

/-! ## 件 1：`AZIM_EQ_PI_ALT` 私有移植 -/

/-- HOL `AZIM_EQ_PI_ALT`：`azim 0 u v w = π ↔ w ∈ affLt {0,u} {v}`
（LocalAuto14:6390 的逐字移植；前提 = 两处非共线）。 -/
theorem p12a_azim_pi_alt {u v w : V3}
    (huv : ¬ Collinear3 0 u v) (huw : ¬ Collinear3 0 u w) :
    azim 0 u v w = Real.pi ↔ w ∈ affLt ({0, u} : Set V3) ({v} : Set V3) := by
  have hu0 : u ≠ 0 := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) v)
  have hv0 : v ≠ 0 := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) u)
  have huvne : u ≠ v := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) v)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (u - 0) (sub_ne_zero.mpr hu0)
  have hax : (u - 0 : V3) = dist u 0 • e3 := by rw [dist_eq_norm]; exact halign
  constructor
  · intro hpi
    have hvw : v ≠ w := by
      intro he
      rw [he, azim_self] at hpi
      exact Real.pi_pos.ne' hpi.symm
    obtain ⟨h1, h2, hframes⟩ := (azim_master (0 : V3) u v w).2.2
    obtain ⟨ψ, r1, r2, repv, repw, hr1, hr2⟩ := hframes e1 e2 e3 hon hax hu0
    have hr1' : 0 < r1 := hr1 huv
    have hr2' : 0 < r2 := hr2 huw
    rw [hpi, Real.cos_add_pi, Real.sin_add_pi] at repw
    have hkey : w - 0 = (-(r2 / r1)) • (v - 0) + (h2 + (r2 / r1) * h1) • (u - 0) := by
      rw [repv, repw]
      simp only [smul_add, smul_smul]
      have hc1 : (-(r2 / r1)) * (r1 * Real.cos ψ) = -(r2 * Real.cos ψ) := by
        field_simp
      have hc2 : (-(r2 / r1)) * (r1 * Real.sin ψ) = -(r2 * Real.sin ψ) := by
        field_simp
      have hc3 : (-(r2 / r1)) * h1 + (h2 + (r2 / r1) * h1) = h2 := by ring
      rw [hc1, hc2, ← hc3]
      module
    have hwrep : w = (-(r2 / r1)) • v + (h2 + (r2 / r1) * h1) • u := by
      simpa using hkey
    refine p12a_affLt_of_coeffs (u := u) (v := v) (w := w) hu0 hv0 huvne
      (t1 := 1 - (h2 + (r2 / r1) * h1) - (-(r2 / r1)))
      (t2 := h2 + (r2 / r1) * h1) (t3 := -(r2 / r1)) ?_ ?_ ?_
    · have : 0 < r2 / r1 := div_pos hr2' hr1'
      linarith
    · ring
    · rw [hwrep]; simp only [smul_zero, zero_add]; exact add_comm _ _
  · intro hmem
    obtain ⟨t1, t2, t3, ht3, hsum, hrep⟩ := p12a_affLt_coeffs hu0 hv0 huvne hmem
    obtain ⟨ψ, r1, r2, hr1', hr2', hzv, hzw⟩ :=
      azim_frame_spec (v := (0 : V3)) (w := u) (w1 := v) (w2 := w) huv huw hon hax hu0
    have hzu : zOf e1 e2 u = 0 := by
      simpa using zOf_axis (v := (0 : V3)) (w := u) hax hon
    have hz0 : zOf e1 e2 (0 : V3) = 0 := by simp [zOf]
    have hzlin : zOf e1 e2 (w - 0) = ((t3 : ℝ) : ℂ) * zOf e1 e2 (v - 0) := by
      have hw0 : w - 0 = t1 • (0 : V3) + t2 • u + t3 • v := by rw [sub_zero, hrep]
      rw [hw0]
      simp only [zOf_add, zOf_smul, hzu, hz0, mul_zero, add_zero, sub_zero]
      ring
    rw [hzv, hzw] at hzlin
    have hexp : Complex.exp (((ψ + azim 0 u v w : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((azim 0 u v w : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp] at hzlin
    have h2 : (((r2 : ℝ) : ℂ) * Complex.exp (((azim 0 u v w : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        = (((t3 * r1 : ℝ) : ℂ)) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
      push_cast
      linear_combination hzlin
    have hkey := mul_right_cancel₀ (Complex.exp_ne_zero _) h2
    have hsin : Real.sin (azim 0 u v w) = 0 := by
      have hi := congrArg Complex.im hkey
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_mul_I,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        add_zero, zero_add, mul_one, mul_add, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re] at hi
      have h0 : r2 * Real.sin (azim 0 u v w) = 0 := by linarith [hi]
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hr2')
      · exact h
    have hcos : Real.cos (azim 0 u v w) < 0 := by
      have hr := congrArg Complex.re hkey
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_mul_I,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        add_zero, zero_add, mul_one, mul_add, Complex.cos_ofReal_re,
        Complex.sin_ofReal_im] at hr
      have h1 : r2 * Real.cos (azim 0 u v w) = t3 * r1 := by linarith [hr]
      have : t3 * r1 < 0 := mul_neg_of_neg_of_pos ht3 hr1'
      nlinarith [hr1', hr2', h1]
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
    have hθ0 := azim_nonneg 0 u v w
    have hθπ := azim_lt_two_pi 0 u v w
    have hn0 : 0 ≤ n := by
      by_contra hcon
      push_neg at hcon
      have hnle : ((n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega)
      nlinarith
    have hn1 : n ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have hnge : (2 : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith
    interval_cases n
    · rw [← hn] at hcos
      norm_num at hcos
    · rw [← hn]
      push_cast
      ring

/-! ## 件 3：W12(a) 主代数（HOL `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`, polar_fan.hl:188-226） -/

/-- 非共线三点里两个非原点（`¬ Collinear3 0 x y` 的退化排除）。 -/
private theorem p12a_ne_zero_of_ncol {x y : V3} (h : ¬ Collinear3 (0:V3) x y) :
    x ≠ 0 ∧ y ≠ 0 := by
  constructor
  · intro he
    rw [he] at h
    exact h (collinear3_of_eq rfl)
  · intro he
    apply h
    have hset : ({0, x, y} : Set V3) = ({0, x} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    show Collinear ℝ ({0, x, y} : Set V3)
    rw [hset]
    exact collinear_pair ℝ (0:V3) x

/-- HOL `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` (polar_fan.hl:188-226)：
`azim 0 v w u = π` + `affGe {0}{v,w} ∩ affLt {0}{u} = ∅` ⟹ `v ∈ affGe {0}{u,w}`。
（HOL 的 `s ≤ 0` 支：`t3 • u` 同时落在 `affGe {0}{v,w}` 与 `affLt {0}{u}`，
与 `hdis` 冲突；`s > 0` 支：`v = (1/t2) • u − (t3/t2) • w`，两系数为正。） -/
theorem p12a_straight_aff_ge {u v w : V3}
    (hnc1 : ¬ Collinear3 (0:V3) v u) (hnc2 : ¬ Collinear3 (0:V3) v w)
    (haz : azim 0 v w u = Real.pi)
    (hdis : affGe ({0} : Set V3) ({v, w} : Set V3) ∩
      affLt ({0} : Set V3) ({u} : Set V3) = ∅) :
    v ∈ affGe ({0} : Set V3) ({u, w} : Set V3) := by
  obtain ⟨hv0, hu0⟩ := p12a_ne_zero_of_ncol hnc1
  obtain ⟨-, hw0⟩ := p12a_ne_zero_of_ncol hnc2
  have hvw : v ≠ w := by
    intro he
    apply hnc2
    have hset : ({0, v, w} : Set V3) = ({0, v} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    show Collinear ℝ ({0, v, w} : Set V3)
    rw [hset]
    exact collinear_pair ℝ (0:V3) v
  -- `AZIM_EQ_PI_ALT`（`(u,v,w) := (v,w,u)`）给出 `u ∈ affLt {0,v} {w}`
  have hmem : u ∈ affLt ({0, v} : Set V3) ({w} : Set V3) :=
    (p12a_azim_pi_alt (u := v) (v := w) (w := u) hnc2 hnc1).mp haz
  obtain ⟨t1, t2, t3, ht3, hsum, hrep⟩ :=
    p12a_affLt_coeffs (u := v) (v := w) (w := u) hv0 hw0 hvw hmem
  have hrep' : u = t2 • v + t3 • w := by
    have h := hrep
    rw [h]
    simp only [smul_zero, zero_add]
  rw [AFF_GE_1_2_0_p17 u w hu0 hw0]
  simp only [Set.mem_setOf_eq]
  by_cases ht2 : 0 < t2
  · -- 好支：`v = (1/t2) • u + (−t3/t2) • w`，两系数为正
    refine ⟨1 / t2, -(t3 / t2), by positivity, ?_, ?_⟩
    · have : t3 / t2 < 0 := div_neg_of_neg_of_pos ht3 ht2
      linarith
    · rw [hrep', smul_add, smul_smul, smul_smul, add_assoc, ← add_smul,
        show (1 / t2) * t2 = 1 by field_simp,
        show (1 / t2) * t3 + -(t3 / t2) = 0 by field_simp; ring]
      simp
  · -- 坏支：`y = t3 • u` 落在 `affGe {0}{v,w} ∩ affLt {0}{u}`
    exfalso
    have ht2le : t2 ≤ 0 := le_of_not_gt ht2
    have hy_lt : t3 • u ∈ affLt ({0} : Set V3) ({u} : Set V3) :=
      p12a_smul_mem_affLt hu0 ht3
    have hy_ge : t3 • u ∈ affGe ({0} : Set V3) ({v, w} : Set V3) := by
      rw [AFF_GE_1_2_0_p17 v w hv0 hw0]
      simp only [Set.mem_setOf_eq]
      refine ⟨t3 * t2, t3 * t3, ?_, ?_, ?_⟩
      · exact mul_nonneg_of_nonpos_of_nonpos ht3.le ht2le
      · exact mul_self_nonneg t3
      · rw [hrep', smul_add, smul_smul, smul_smul]
    have hbot : t3 • u ∈ affGe ({0} : Set V3) ({v, w} : Set V3) ∩
        affLt ({0} : Set V3) ({u} : Set V3) := ⟨hy_ge, hy_lt⟩
    rw [hdis] at hbot
    exact hbot

end Kepler.Text
