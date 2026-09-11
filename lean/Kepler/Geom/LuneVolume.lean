/-
Kepler.Geom.LuneVolume — HOL Light Flyspeck "lune" 体积结果
（`Multivariate/flyspeck.ml`：`dihV`(:2995)、`AZIM_DIHV_SAME`(:3107)、
`WEDGE_LUNE_GT`(:3805)、`HAS_MEASURE_LUNE`(:5529)、
`HAS_MEASURE_LUNE_SIMPLE`(:5614)）。

本文件只依赖 `Kepler.Geom.*`（`WedgeVolume`、`Aff`、`Coplanar`），
不引入 `Kepler.Text.*`。`dihV` 用本文件局部定义的 `arcV`（与
`Kepler.Text.TopologyFan.arcVFan` 同体，HOL `arcV`）展开。
-/

import Kepler.Geom.WedgeVolume
import Kepler.Geom.Aff
import Kepler.Geom.Coplanar

open Classical
open Complex
open MeasureTheory
open Module

noncomputable section

set_option maxHeartbeats 5000000

namespace Kepler.Geom

/-! ## `arcV` 与 `dihV`（HOL `sphere.hl:375`、`flyspeck.ml:2995`） -/

/-- HOL `arcV u v w = acs ((v-u)·(w-u) / (‖v-u‖ ‖w-u‖))`。 -/
noncomputable def arcV (u v w : V3) : ℝ :=
  Real.arccos (((v - u) ⬝ᵥ (w - u)) / (dist v u * dist w u))

/-- HOL `dihV w0 w1 w2 w3`（`flyspeck.ml:2995`，`sphere.hl:377` 同）：
把 `w2-w0`、`w3-w0` 投影到轴 `w1-w0` 的正交补后取夹角。 -/
noncomputable def dihV (w0 w1 w2 w3 : V3) : ℝ :=
  let va := w2 - w0
  let vb := w3 - w0
  let vc := w1 - w0
  let vap := (vc ⬝ᵥ vc) • va - (va ⬝ᵥ vc) • vc
  let vbp := (vc ⬝ᵥ vc) • vb - (vb ⬝ᵥ vc) • vc
  arcV 0 vap vbp

/-! ## 标架下的投影夹角（`AZIM_DIHV_SAME` 的解析核心）

与 `Kepler/Text/PlanarityAuto16.lean:328` 的私有
`azim_eq_arcVFan_proj` 同证明，此处用局部 `arcV`。 -/

private theorem smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_smul (a : V3) (t : ℝ) (b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem add_dot (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_add (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem coe_add (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem cexp_cos_re (r : ℝ) : (Complex.exp ((r : ℂ) * I)).re = Real.cos r := by
  have h := congrArg Complex.re (Complex.exp_mul_I (r : ℂ))
  simpa using h

private theorem cexp_sin_im (r : ℝ) : (Complex.exp ((r : ℂ) * I)).im = Real.sin r := by
  have h := congrArg Complex.im (Complex.exp_mul_I (r : ℂ))
  simpa using h

/-- 投影夹角恒等式：`dihV a b c d = arccos (cos (azim a b c d))`
（把 `c-a`、`d-a` 投影到轴 `b-a` 的正交补后所得向量的夹角）。 -/
private theorem dihV_eq_arccos_cos_azim {a b c d : V3}
    (h1 : ¬ Collinear3 a b c) (h2 : ¬ Collinear3 a b d) :
    dihV a b c d = Real.arccos (Real.cos (azim a b c d)) := by
  have hab : b ≠ a := fun he => h1 (collinear3_of_eq he)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (b - a) (sub_ne_zero.mpr hab)
  have hax : (b - a : V3) = dist b a • e3 := by
    rw [dist_eq_norm]; exact halign
  have hax' : (b : Fin 3 → ℝ) - (a : Fin 3 → ℝ) = dist b a • (e3 : Fin 3 → ℝ) := by
    have h := congrArg (fun v : V3 => (v : Fin 3 → ℝ)) hax
    simpa only [coe_sub, coe_smul] using h
  obtain ⟨psi, r1, r2, hr1, hr2, hz1, hz2⟩ :=
    azim_frame_spec (v := a) (w := b) (w1 := c) (w2 := d) h1 h2 hon hax hab
  have hon0 := hon
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dot_comm, h12]
  have hva1 : (c - a) ⬝ᵥ e1 = r1 * Real.cos psi := by
    have h := congrArg Complex.re hz1
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      mul_one] at h
    rw [cexp_cos_re] at h
    exact h
  have hva2 : (c - a) ⬝ᵥ e2 = r1 * Real.sin psi := by
    have h := congrArg Complex.im hz1
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] at h
    rw [cexp_sin_im] at h
    exact h
  have hvb1 : (d - a) ⬝ᵥ e1 = r2 * Real.cos (psi + azim a b c d) := by
    have h := congrArg Complex.re hz2
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      mul_one] at h
    rw [cexp_cos_re] at h
    exact h
  have hvb2 : (d - a) ⬝ᵥ e2 = r2 * Real.sin (psi + azim a b c d) := by
    have h := congrArg Complex.im hz2
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] at h
    rw [cexp_sin_im] at h
    exact h
  set s : ℝ := dist b a ^ 2 with hs
  have hs_pos : 0 < s := by rw [hs]; exact pow_pos (dist_pos.mpr hab) 2
  set u1 : V3 := ((c - a) ⬝ᵥ e1) • e1 + ((c - a) ⬝ᵥ e2) • e2 with hu1def
  set u2 : V3 := ((d - a) ⬝ᵥ e1) • e1 + ((d - a) ⬝ᵥ e2) • e2 with hu2def
  have hu1_exp : u1 = (r1 * Real.cos psi) • e1 + (r1 * Real.sin psi) • e2 := by
    rw [hu1def, hva1, hva2]
  have hu2_exp : u2 = (r2 * Real.cos (psi + azim a b c d)) • e1 +
      (r2 * Real.sin (psi + azim a b c d)) • e2 := by
    rw [hu2def, hvb1, hvb2]
  have hvcvc : (b - a) ⬝ᵥ (b - a) = s := by
    rw [coe_sub, hax', smul_dotProduct, dotProduct_smul, h33, smul_eq_mul, hs]
    ring
  have hva_vc : (c - a) ⬝ᵥ (b - a) = dist b a * ((c - a) ⬝ᵥ e3) := by
    rw [coe_sub, hax', dotProduct_smul, smul_eq_mul]
  have hvb_vc : (d - a) ⬝ᵥ (b - a) = dist b a * ((d - a) ⬝ᵥ e3) := by
    rw [coe_sub, hax', dotProduct_smul, smul_eq_mul]
  have hvap : ((b - a) ⬝ᵥ (b - a)) • (c - a) - ((c - a) ⬝ᵥ (b - a)) • (b - a)
      = s • u1 := by
    have hdot3 : ((((c - a) ⬝ᵥ e1) • e1 + ((c - a) ⬝ᵥ e2) • e2 +
        ((c - a) ⬝ᵥ e3) • e3) ⬝ᵥ e3) = (c - a) ⬝ᵥ e3 := by
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct, add_dotProduct,
        smul_dotProduct, smul_dotProduct, smul_dotProduct, h13, h23, h33]
      ring
    rw [hvcvc, hva_vc, hax, on3_expand hon0 (c - a), hdot3, hu1def, hs]
    module
  have hvbp : ((b - a) ⬝ᵥ (b - a)) • (d - a) - ((d - a) ⬝ᵥ (b - a)) • (b - a)
      = s • u2 := by
    have hdot3 : ((((d - a) ⬝ᵥ e1) • e1 + ((d - a) ⬝ᵥ e2) • e2 +
        ((d - a) ⬝ᵥ e3) • e3) ⬝ᵥ e3) = (d - a) ⬝ᵥ e3 := by
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct, add_dotProduct,
        smul_dotProduct, smul_dotProduct, smul_dotProduct, h13, h23, h33]
      ring
    rw [hvcvc, hvb_vc, hax, on3_expand hon0 (d - a), hdot3, hu2def, hs]
    module
  have hu1norm : ‖u1‖ = r1 := by
    have hsq : ‖u1‖ ^ 2 = r1 ^ 2 := by
      rw [norm_sq_eq_dot, hu1_exp]
      simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, h11, h22, h12, h21]
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq psi]
    nlinarith [norm_nonneg u1, hr1.le]
  have hu2norm : ‖u2‖ = r2 := by
    have hsq : ‖u2‖ ^ 2 = r2 ^ 2 := by
      rw [norm_sq_eq_dot, hu2_exp]
      simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, h11, h22, h12, h21]
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq (psi + azim a b c d)]
    nlinarith [norm_nonneg u2, hr2.le]
  have hu1u2 : u1 ⬝ᵥ u2 = r1 * r2 * Real.cos (azim a b c d) := by
    rw [hu1_exp, hu2_exp]
    simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, h11, h22, h12, h21]
    have htrig : Real.cos psi * Real.cos (psi + azim a b c d) +
        Real.sin psi * Real.sin (psi + azim a b c d) = Real.cos (azim a b c d) := by
      rw [← Real.cos_sub]
      rw [show psi - (psi + azim a b c d) = -(azim a b c d) by ring, Real.cos_neg]
    linear_combination (r1 * r2) * htrig
  have hnum : WithLp.ofLp (s • u1) ⬝ᵥ WithLp.ofLp (s • u2) =
      (s * r1) * (s * r2) * Real.cos (azim a b c d) := by
    rw [coe_smul, coe_smul, smul_dotProduct, dotProduct_smul, hu1u2]
    ring
  have hden1 : dist (s • u1) 0 = s * r1 := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hu1norm]
  have hden2 : dist (s • u2) 0 = s * r2 := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hu2norm]
  have hden : dist (s • u1) 0 * dist (s • u2) 0 = (s * r1) * (s * r2) := by
    rw [hden1, hden2]
  have harg : (WithLp.ofLp (s • u1) ⬝ᵥ WithLp.ofLp (s • u2)) /
      (dist (s • u1) 0 * dist (s • u2) 0) = Real.cos (azim a b c d) := by
    rw [hnum, hden]
    have hsne : s ≠ 0 := ne_of_gt hs_pos
    have hr1ne : r1 ≠ 0 := ne_of_gt hr1
    have hr2ne : r2 ≠ 0 := ne_of_gt hr2
    field_simp
  unfold dihV
  dsimp only
  show arcV 0
    (((b - a) ⬝ᵥ (b - a)) • (c - a) - ((c - a) ⬝ᵥ (b - a)) • (b - a))
    (((b - a) ⬝ᵥ (b - a)) • (d - a) - ((d - a) ⬝ᵥ (b - a)) • (b - a))
    = Real.arccos (Real.cos (azim a b c d))
  rw [hvap, hvbp, arcV, coe_zero, sub_zero, sub_zero, harg]

/-- HOL `AZIM_DIHV_SAME`（`flyspeck.ml:3107`）。 -/
theorem azim_dihv_same {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hπ : azim v w v1 v2 < Real.pi) :
    azim v w v1 v2 = dihV v w v1 v2 := by
  rw [dihV_eq_arccos_cos_azim h1 h2,
    Real.arccos_cos (azim_nonneg v w v1 v2) (le_of_lt hπ)]

/-- HOL `AZIM_DIHV_COMPL`（`flyspeck.ml:3115`）：`π ≤ azim` 时
`azim v w v1 v2 = 2π - dihV v w v1 v2`。 -/
theorem azim_dihv_compl {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hge : Real.pi ≤ azim v w v1 v2) :
    azim v w v1 v2 = 2 * Real.pi - dihV v w v1 v2 := by
  have hθ2π : azim v w v1 v2 < 2 * Real.pi := azim_lt_two_pi v w v1 v2
  have hdihv : dihV v w v1 v2 = 2 * Real.pi - azim v w v1 v2 := by
    rw [dihV_eq_arccos_cos_azim h1 h2, ← Real.cos_two_pi_sub,
      Real.arccos_cos (by linarith) (by linarith)]
  linarith

/-! ## `wedge = affGt`（HOL `WEDGE_LUNE_GT`，`flyspeck.ml:3805`）

证明路线（替代 HOL 的二维降维 + `AFF_GT_LEMMA`）：
- `zOf`（到轴正交补的投影，视为 ℂ）把楔形与 `affGt` 都化为
  「`zOf (z-v)` 是 `zOf (w1-v)`、`zOf (w2-v)` 的正实系数组合」。
- `affGt` 侧由 `Affsign` 展开（`mem_affGt_two_pairs_iff`）+ 轴方向判别
  （`zOf_eq_zero_iff_axis`）。
- `azim` 侧由 `azim_frame_spec` 的极坐标表示 + 二维锥分解
  （`exp_pos_combo`）或 `azim_cone_of_combo` 的解析计算。 -/

/-- `zOf` 对减法线性。 -/
private theorem zOf_sub (e1 e2 p q : V3) :
    zOf e1 e2 (p - q) = zOf e1 e2 p - zOf e1 e2 q := by
  rw [sub_eq_add_neg, show -(q : V3) = (-1 : ℝ) • q from by simp, zOf_add, zOf_smul]
  push_cast
  ring

/-- `zOf e1 e2 z = 0` 当且仅当 `z` 平行于轴 `w-v`。 -/
private theorem zOf_eq_zero_iff_axis {v w e1 e2 e3 : V3}
    (he : Orthonormal3 e1 e2 e3) (hax : (w - v : V3) = dist w v • e3) (hw : w ≠ v)
    (z : V3) : zOf e1 e2 z = 0 ↔ ∃ c : ℝ, z = c • (w - v) := by
  constructor
  · intro hz
    have hcol : Collinear3 v w (v + z) := by
      by_contra hnc
      exact (zOf_ne_zero_iff he hax hw (v + z)).mpr hnc (by simpa using hz)
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hw).mp hcol
    exact ⟨c, by simpa using hc⟩
  · rintro ⟨c, rfl⟩
    rw [zOf_smul, zOf_axis hax he, mul_zero]

/-- 四点互异时 `{v,w} ∪ {x,y}` 的 toFinset 求值。 -/
private theorem sum_union_two_pairs {f : V3 → ℝ} {v w x y : V3}
    (hfin : ({v, w} ∪ {x, y} : Set V3).Finite)
    (hvw : v ≠ w) (hvx : v ≠ x) (hvy : v ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    ∑ p ∈ hfin.toFinset, f p = f v + f w + f x + f y := by
  have hfs : hfin.toFinset = ({v, w, x, y} : Finset V3) := by
    apply Finset.ext; intro p
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hfs, Finset.sum_insert (by simp [hvw, hvx, hvy]),
    Finset.sum_insert (by simp [hwx, hwy]), Finset.sum_insert (by simp [hxy]),
    Finset.sum_singleton]
  ring

/-- 四点互异时 `{v,w} ∪ {x,y}` 的向量和求值。 -/
private theorem sum_union_two_pairs_v {f : V3 → ℝ} {v w x y : V3}
    (hfin : ({v, w} ∪ {x, y} : Set V3).Finite)
    (hvw : v ≠ w) (hvx : v ≠ x) (hvy : v ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    ∑ p ∈ hfin.toFinset, f p • p = f v • v + f w • w + f x • x + f y • y := by
  have hfs : hfin.toFinset = ({v, w, x, y} : Finset V3) := by
    apply Finset.ext; intro p
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hfs, Finset.sum_insert (by simp [hvw, hvx, hvy]),
    Finset.sum_insert (by simp [hwx, hwy]), Finset.sum_insert (by simp [hxy]),
    Finset.sum_singleton]
  abel

/-- `affGt {v,w} {x,y}` 的显式组合刻画（四点互异）：
`z - v = β•(x-v) + γ•(y-v) + δ•(w-v)`，`β,γ > 0`。 -/
private theorem mem_affGt_two_pairs_iff {v w x y z : V3}
    (hvw : v ≠ w) (hvx : v ≠ x) (hvy : v ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    z ∈ affGt ({v, w} : Set V3) {x, y} ↔
      ∃ β γ δ : ℝ, 0 < β ∧ 0 < γ ∧
        z - v = β • (x - v) + γ • (y - v) + δ • (w - v) := by
  have hfin : ({v, w} ∪ {x, y} : Set V3).Finite :=
    ((Set.finite_singleton w).insert v).union ((Set.finite_singleton y).insert x)
  constructor
  · rintro ⟨f, hfin', hsum, hpos, hone⟩
    have hfint : hfin'.toFinset = hfin.toFinset := by
      rw [Subsingleton.elim hfin' hfin]
    rw [hfint] at hsum hone
    rw [sum_union_two_pairs_v hfin hvw hvx hvy hwx hwy hxy] at hsum
    rw [sum_union_two_pairs hfin hvw hvx hvy hwx hwy hxy] at hone
    have hfv : f v = 1 - f w - f x - f y := by linarith
    refine ⟨f x, f y, f w, hpos x (by simp), hpos y (by simp), ?_⟩
    rw [hsum, hfv]
    module
  · rintro ⟨β, γ, δ, hβ, hγ, hz⟩
    set f : V3 → ℝ := fun p => if p = x then β else if p = y then γ
      else if p = w then δ else 1 - β - γ - δ with hf
    have hfv : f v = 1 - β - γ - δ := by simp [hf, hvx, hvy, hvw]
    have hfw : f w = δ := by simp [hf, hwx, hwy]
    have hfx : f x = β := by simp [hf]
    have hfy : f y = γ := by simp [hf, hxy, Ne.symm hxy]
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [sum_union_two_pairs_v (f := f) hfin hvw hvx hvy hwx hwy hxy,
        hfv, hfw, hfx, hfy]
      rw [show z = (z - v) + v by abel, hz]
      module
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · rw [hfx]; exact hβ
      · rw [hfy]; exact hγ
    · rw [sum_union_two_pairs (f := f) hfin hvw hvx hvy hwx hwy hxy,
        hfv, hfw, hfx, hfy]
      ring

/-- 二维锥分解（单位圆）：`0 < φ < θ < π` 时
`e^{iφ} = β + γ e^{iθ}`，`β,γ > 0`。 -/
private theorem exp_one_pos_combo {θ φ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ)
    (hθπ : θ < Real.pi) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧
      Complex.exp (((φ : ℝ) : ℂ) * I) = (β : ℂ) + (γ : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * I) := by
  have hθ0 : 0 < θ := lt_trans hφ0 hφθ
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ0, hθπ⟩
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_mem_Ioo ⟨hφ0, by linarith⟩
  have hsinθφ : 0 < Real.sin (θ - φ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  refine ⟨Real.sin (θ - φ) / Real.sin θ, Real.sin φ / Real.sin θ,
    div_pos hsinθφ hsinθ, div_pos hsinφ hsinθ, ?_⟩
  apply Complex.ext
  · rw [cexp_cos_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, cexp_cos_re, cexp_sin_im]
    rw [Real.sin_sub]
    field_simp
    ring
  · rw [cexp_sin_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, cexp_cos_re, cexp_sin_im]
    field_simp
    ring

/-- 二维锥分解（含相位 `ψ`）：`0 < φ < θ < π` 时
`e^{i(ψ+φ)} = β e^{iψ} + γ e^{i(ψ+θ)}`，`β,γ > 0`。 -/
private theorem exp_pos_combo {θ φ ψ : ℝ} (hφ0 : 0 < φ) (hφθ : φ < θ)
    (hθπ : θ < Real.pi) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧
      Complex.exp (((ψ + φ : ℝ) : ℂ) * I) =
        (β : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * I)
          + (γ : ℂ) * Complex.exp ((((ψ + θ : ℝ) : ℂ)) * I) := by
  obtain ⟨β, γ, hβ, hγ, h⟩ := exp_one_pos_combo hφ0 hφθ hθπ
  refine ⟨β, γ, hβ, hγ, ?_⟩
  have hL : Complex.exp (((ψ + φ : ℝ) : ℂ) * I)
      = Complex.exp (((ψ : ℝ) : ℂ) * I) * Complex.exp (((φ : ℝ) : ℂ) * I) := by
    rw [show (((ψ + φ : ℝ)) : ℂ) * I = ((ψ : ℝ) : ℂ) * I + ((φ : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add]
  have hR : Complex.exp ((((ψ + θ : ℝ)) : ℂ) * I)
      = Complex.exp (((ψ : ℝ) : ℂ) * I) * Complex.exp (((θ : ℝ) : ℂ) * I) := by
    rw [show ((((ψ + θ : ℝ)) : ℂ)) * I = ((ψ : ℝ) : ℂ) * I + ((θ : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add]
  rw [hL, h, hR]
  ring

/-! ### 解析锥引理（HOL `WEDGE_LUNE_GT` 的核心）

与 `Kepler/Text/PlanarityNotCut.lean:2069` 的私有 `azim_cone_of_combo` 同证明。 -/

set_option maxHeartbeats 0 in
/-- 锥引理：`0 < azim x u w v < π` 时，`y - x` 是 `v - x`、`w - x`（正系数）
与 `u - x`（任意系数）的组合，则 `y` 不在轴 `xu` 上且
`0 < azim x u w y < azim x u w v`。 -/
private theorem azim_cone_of_combo {x u w v y : V3}
    (hncw : ¬ Collinear3 x u w) (hncv : ¬ Collinear3 x u v)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hy : y - x = a • (v - x) + b • (w - x) + c • (u - x)) :
    ¬ Collinear3 x u y ∧ 0 < azim x u w y ∧ azim x u w y < azim x u w v := by
  have hux : u ≠ x := by
    intro he
    exact hncw (collinear3_of_eq (v := x) (w := u) (w1 := w) he)
  obtain ⟨f1, f2, f3, hon, halign⟩ :=
    exists_on3_eq_smul (u - x) (sub_ne_zero.mpr hux)
  have hax : (u - x : V3) = dist u x • f3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨hp1, hp2⟩ := axis_perp hax hon
  set θv := azim x u w v with hθvdef
  obtain ⟨ψ, rb, ra, hrb, hra, hzw, hzv⟩ := azim_frame_spec hncw hncv hon hax hux
  have hwrep := rep_of_zOf hon hax hux w ψ rb hzw
  have hvrep := rep_of_zOf hon hax hux v (ψ + θv) ra hzv
  have hzline : zOf f1 f2 (y - x)
      = ((a * ra : ℝ) : ℂ) * Complex.exp (((ψ + θv : ℝ) : ℂ) * I)
        + ((b * rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * I) := by
    have h1 : y - x = a • (v - x) + (b • (w - x) + c • (u - x)) := by
      rw [hy]; abel
    rw [h1, zOf_add, zOf_smul, zOf_add, zOf_smul, zOf_smul, zOf_axis hax hon, hzv, hzw]
    push_cast
    ring
  have k1 : (y - x : V3) ⬝ᵥ f1
      = a * (ra * Real.cos (ψ + θv)) + b * (rb * Real.cos ψ) := by
    have h := congrArg Complex.re hzline
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_cos_re, cexp_cos_re] at h
    linarith
  have k2 : (y - x : V3) ⬝ᵥ f2
      = a * (ra * Real.sin (ψ + θv)) + b * (rb * Real.sin ψ) := by
    have h := congrArg Complex.im hzline
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_sin_im, cexp_sin_im] at h
    linarith
  have hsinpos : 0 < Real.sin θv :=
    Real.sin_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hθ0, hθπ⟩)
  have trig1 : ∀ A B α β γ : ℝ, (A * Real.sin α + B * Real.sin β) * Real.cos γ
      - (A * Real.cos α + B * Real.cos β) * Real.sin γ
      = A * Real.sin (α - γ) + B * Real.sin (β - γ) := by
    intro A B α β γ
    rw [Real.sin_sub, Real.sin_sub]
    ring
  have trig2 : ∀ A B α β γ : ℝ, (A * Real.cos α + B * Real.cos β) * Real.sin γ
      - (A * Real.sin α + B * Real.sin β) * Real.cos γ
      = A * Real.sin (γ - α) + B * Real.sin (γ - β) := by
    intro A B α β γ
    rw [Real.sin_sub, Real.sin_sub]
    ring
  by_cases hcy : Collinear3 x u y
  · exfalso
    have hz0 : zOf f1 f2 (y - x) = 0 := by
      by_contra hne
      exact (zOf_ne_zero_iff hon hax hux y).mp hne hcy
    have hz1 : (y - x : V3) ⬝ᵥ f1 = 0 := by
      have h := congrArg Complex.re hz0
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      exact h
    have hz2 : (y - x : V3) ⬝ᵥ f2 = 0 := by
      have h := congrArg Complex.im hz0
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      exact h
    have hK1 : a * (ra * Real.cos (ψ + θv)) + b * (rb * Real.cos ψ) = 0 :=
      k1.symm.trans hz1
    have hK2 : a * (ra * Real.sin (ψ + θv)) + b * (rb * Real.sin ψ) = 0 :=
      k2.symm.trans hz2
    have hkey := trig2 (a * ra) (b * rb) (ψ + θv) ψ ψ
    rw [show (ψ - (ψ + θv) : ℝ) = -θv from by ring, show (ψ - ψ : ℝ) = 0 from by ring,
      Real.sin_zero, mul_zero, add_zero, Real.sin_neg, mul_neg] at hkey
    rw [show ((a * ra) * Real.cos (ψ + θv) : ℝ) = a * (ra * Real.cos (ψ + θv)) from by ring,
      show ((b * rb) * Real.cos ψ : ℝ) = b * (rb * Real.cos ψ) from by ring, hK1,
      show ((a * ra) * Real.sin (ψ + θv) : ℝ) = a * (ra * Real.sin (ψ + θv)) from by ring,
      show ((b * rb) * Real.sin ψ : ℝ) = b * (rb * Real.sin ψ) from by ring, hK2] at hkey
    have hcon : a * (ra * Real.sin θv) = 0 := by
      have hassoc : a * (ra * Real.sin θv) = a * ra * Real.sin θv := by ring
      rw [hassoc]
      linear_combination hkey
    have hposA : 0 < a * (ra * Real.sin θv) := mul_pos ha (mul_pos hra hsinpos)
    linarith
  · obtain ⟨ψ', r1', ry, hr1', hry, hzw2, hzy⟩ :=
      azim_frame_spec hncw hcy hon hax hux
    have heq : Complex.exp (((ψ : ℝ) : ℂ) * I) = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
      exp_pos_mul_eq hrb hr1' (hzw.symm.trans hzw2)
    have hcs : Real.cos ψ = Real.cos ψ' ∧ Real.sin ψ = Real.sin ψ' := by
      constructor
      · have h := congrArg Complex.re heq
        rw [cexp_cos_re, cexp_cos_re] at h
        exact h
      · have h := congrArg Complex.im heq
        rw [cexp_sin_im, cexp_sin_im] at h
        exact h
    have cospv : Real.cos (ψ' + θv) = Real.cos (ψ + θv) := by
      rw [Real.cos_add, Real.cos_add]
      rw [hcs.2, hcs.1]
    have sinpv : Real.sin (ψ' + θv) = Real.sin (ψ + θv) := by
      rw [Real.sin_add, Real.sin_add]
      rw [hcs.2, hcs.1]
    have cosw : Real.cos ψ' = Real.cos ψ := hcs.1.symm
    have sinw : Real.sin ψ' = Real.sin ψ := hcs.2.symm
    set φ := azim x u w y with hφdef
    have hy1' : (y - x : V3) ⬝ᵥ f1 = ry * Real.cos (ψ' + φ) := by
      have h := congrArg Complex.re hzy
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      rw [cexp_cos_re] at h
      linarith
    have hy2' : (y - x : V3) ⬝ᵥ f2 = ry * Real.sin (ψ' + φ) := by
      have h := congrArg Complex.im hzy
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      rw [cexp_sin_im] at h
      linarith
    have e1 : ry * Real.cos (ψ' + φ)
        = a * (ra * Real.cos (ψ' + θv)) + b * (rb * Real.cos ψ') := by
      rw [← hy1', cospv, cosw]
      exact k1
    have e2 : ry * Real.sin (ψ' + φ)
        = a * (ra * Real.sin (ψ' + θv)) + b * (rb * Real.sin ψ') := by
      rw [← hy2', sinpv, sinw]
      exact k2
    have hpos1 : 0 < a * (ra * Real.sin θv) := mul_pos ha (mul_pos hra hsinpos)
    have hE1 : ry * Real.sin φ = a * (ra * Real.sin θv) := by
      have h := trig1 (a * ra) (b * rb) (ψ' + θv) ψ' ψ'
      rw [show ((ψ' + θv) - ψ' : ℝ) = θv from by ring,
        show (ψ' - ψ' : ℝ) = 0 from by ring, Real.sin_zero, mul_zero, add_zero] at h
      calc ry * Real.sin φ
          = ry * (Real.sin (ψ' + φ) * Real.cos ψ'
            - Real.cos (ψ' + φ) * Real.sin ψ') := by
            congr 1
            rw [← Real.sin_sub, show (ψ' + φ - ψ' : ℝ) = φ from by ring]
        _ = (ry * Real.sin (ψ' + φ)) * Real.cos ψ'
            - (ry * Real.cos (ψ' + φ)) * Real.sin ψ' := by ring
        _ = a * (ra * Real.sin θv) := by
            rw [e2, e1]
            linear_combination h
    have hposry : 0 < ry * Real.sin φ := by rw [hE1]; exact hpos1
    have hφ0 : 0 ≤ φ := azim_nonneg x u w y
    have hφnz : φ ≠ 0 := by
      intro h
      rw [h, Real.sin_zero] at hposry
      norm_num at hposry
    have hφpos : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hφnz)
    have hφ2 : φ < 2 * Real.pi := azim_lt_two_pi x u w y
    have hφltπ : φ < Real.pi := by
      by_contra hc
      push_neg at hc
      have hnn : 0 ≤ Real.sin (φ - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hcon := mul_nonneg hry.le hnn
      have hE : ry * Real.sin φ = -(ry * Real.sin (φ - Real.pi)) := by
        have h3 : ry * Real.sin φ = ry * Real.sin ((φ - Real.pi) + Real.pi) := by
          congr 1; ring
        rw [h3, Real.sin_add, Real.cos_pi, Real.sin_pi]
        ring
      rw [hE1] at hE
      linarith
    refine ⟨hcy, hφpos, ?_⟩
    by_contra hc
    push_neg at hc
    have hnn : 0 ≤ Real.sin (φ - θv) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcon := mul_nonneg hry.le hnn
    have hposB : 0 < b * (rb * Real.sin θv) := mul_pos hb (mul_pos hrb hsinpos)
    have hE2 : ry * Real.sin (φ - θv) = -(b * (rb * Real.sin θv)) := by
      have h := trig1 (a * ra) (b * rb) (ψ' + θv) ψ' (ψ' + θv)
      rw [show ((ψ' + θv) - (ψ' + θv) : ℝ) = 0 from by ring,
        show (ψ' - (ψ' + θv) : ℝ) = -θv from by ring, Real.sin_zero, mul_zero,
        zero_add, Real.sin_neg, mul_neg] at h
      calc ry * Real.sin (φ - θv)
          = ry * (Real.sin (ψ' + φ) * Real.cos (ψ' + θv)
            - Real.cos (ψ' + φ) * Real.sin (ψ' + θv)) := by
            congr 1
            rw [← Real.sin_sub, show (ψ' + φ - (ψ' + θv) : ℝ) = φ - θv from by ring]
        _ = (ry * Real.sin (ψ' + φ)) * Real.cos (ψ' + θv)
            - (ry * Real.cos (ψ' + φ)) * Real.sin (ψ' + θv) := by ring
        _ = -(b * (rb * Real.sin θv)) := by
            rw [e2, e1]
            linear_combination h
    rw [hE2] at hcon
    linarith

/-- `WEDGE_LUNE_GT` 的私有一般形式。 -/
private theorem wedge_eq_affGt_aux {v w x y : V3}
    (h1 : ¬ Collinear3 v w x) (h2 : ¬ Collinear3 v w y)
    (h0 : 0 < azim v w x y) (hπ : azim v w x y < Real.pi) :
    wedge v w x y = affGt ({v, w} : Set V3) {x, y} := by
  have hwv : w ≠ v := fun he => h1 (collinear3_of_eq he)
  have hvx : v ≠ x := fun he => h1 (collinear3_pair_left he.symm)
  have hvy : v ≠ y := fun he => h2 (collinear3_pair_left he.symm)
  have hwx : w ≠ x := fun he => h1 (collinear3_pair_right he.symm)
  have hwy : w ≠ y := fun he => h2 (collinear3_pair_right he.symm)
  have hxy : x ≠ y := by
    intro he
    have : azim v w x y = 0 := by rw [he, azim_self]
    linarith
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (w - v) (sub_ne_zero.mpr hwv)
  have hax : (w - v : V3) = dist w v • e3 := by rw [dist_eq_norm]; exact halign
  ext z
  rw [mem_affGt_two_pairs_iff (Ne.symm hwv) hvx hvy hwx hwy hxy]
  constructor
  · rintro ⟨hznc, hφ0, hφθ⟩
    obtain ⟨ψ, rx, ry, hrx, hry, hzx, hzy⟩ := azim_frame_spec h1 h2 hon hax hwv
    obtain ⟨ψ', rx', rz, hrx', hrz, hzx', hzz⟩ := azim_frame_spec h1 hznc hon hax hwv
    have heq : Complex.exp (((ψ : ℝ) : ℂ) * I) = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
      exp_pos_mul_eq hrx hrx' (hzx.symm.trans hzx')
    have hshift : Complex.exp ((((ψ' + azim v w x z : ℝ)) : ℂ) * I)
        = Complex.exp ((((ψ + azim v w x z : ℝ)) : ℂ) * I) := by
      rw [show (((ψ' + azim v w x z : ℝ)) : ℂ) * I
            = ((ψ' : ℝ) : ℂ) * I + ((azim v w x z : ℝ) : ℂ) * I by push_cast; ring,
          show (((ψ + azim v w x z : ℝ)) : ℂ) * I
            = ((ψ : ℝ) : ℂ) * I + ((azim v w x z : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_add, Complex.exp_add, heq]
    have hzz' : zOf e1 e2 (z - v)
        = ((rz : ℝ) : ℂ) * Complex.exp ((((ψ + azim v w x z : ℝ)) : ℂ) * I) := by
      rw [hzz, hshift]
    obtain ⟨β, γ, hβ, hγ, hcomb⟩ :=
      exp_pos_combo (ψ := ψ) (θ := azim v w x y) (φ := azim v w x z) hφ0 hφθ hπ
    have hrxne : ((rx : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrx.ne'
    have hryne : ((ry : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hry.ne'
    have hz1inv : Complex.exp (((ψ : ℝ) : ℂ) * I) = (((rx : ℝ) : ℂ))⁻¹ * zOf e1 e2 (x - v) := by
      rw [hzx]
      field_simp [hrxne]
    have hz2inv : Complex.exp ((((ψ + azim v w x y : ℝ)) : ℂ) * I)
        = (((ry : ℝ) : ℂ))⁻¹ * zOf e1 e2 (y - v) := by
      rw [hzy]
      field_simp [hryne]
    have hzof : zOf e1 e2 (z - v)
        = ((rz * β / rx : ℝ) : ℂ) * zOf e1 e2 (x - v)
          + ((rz * γ / ry : ℝ) : ℂ) * zOf e1 e2 (y - v) := by
      rw [hzz', hcomb, hz1inv, hz2inv]
      push_cast
      ring
    have hzero : zOf e1 e2
        ((z - v) - ((rz * β / rx) • (x - v)) - ((rz * γ / ry) • (y - v))) = 0 := by
      rw [zOf_sub, zOf_sub, zOf_smul, zOf_smul]
      rw [hzof]
      ring
    obtain ⟨δ, hδ⟩ := (zOf_eq_zero_iff_axis hon hax hwv _).mp hzero
    refine ⟨rz * β / rx, rz * γ / ry, δ, div_pos (mul_pos hrz hβ) hrx,
      div_pos (mul_pos hrz hγ) hry, ?_⟩
    rw [← hδ]
    abel
  · rintro ⟨β, γ, δ, hβ, hγ, hz⟩
    have hcone := azim_cone_of_combo (x := v) (u := w) (w := x) (v := y) (y := z)
      h1 h2 h0 hπ γ β δ hγ hβ (by rw [hz]; abel)
    exact ⟨hcone.1, hcone.2.1, hcone.2.2⟩

/-- HOL `WEDGE_LUNE_GT`（`flyspeck.ml:3805`）。 -/
theorem wedge_eq_affGt {v0 v1 w1 w2 : V3} (h1 : ¬ Collinear3 v0 v1 w1)
    (h2 : ¬ Collinear3 v0 v1 w2) (h0 : 0 < azim v0 v1 w1 w2)
    (hπ : azim v0 v1 w1 w2 < Real.pi) :
    wedge v0 v1 w1 w2 = affGt ({v0, v1} : Set V3) {w1, w2} :=
  wedge_eq_affGt_aux h1 h2 h0 hπ

/-! ## 球与 `affGt` 交的体积（HOL `HAS_MEASURE_LUNE`，`flyspeck.ml:5529`） -/

/-- 两个向量张成的子空间维数 ≤ 2。 -/
private theorem finrank_span_pair_le_two (a b : V3) :
    finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h
  have h2 : ({a, b} : Finset V3).card ≤ 2 := by
    calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
      _ = 2 := by simp
  omega

/-- 三点集的仿射包在 `V3`（三维）中真（方向由两个差向量张成）。 -/
private theorem affineSpan_three_ne_top (z w w1 : V3) :
    (affineSpan ℝ ({z, w, w1} : Set V3)) ≠ ⊤ := by
  intro h
  have hdir : (affineSpan ℝ ({z, w, w1} : Set V3)).direction = ⊤ := by
    rw [h]; exact AffineSubspace.direction_top ℝ V3 V3
  have hvs : vectorSpan ℝ ({z, w, w1} : Set V3)
      = Submodule.span ℝ ({w - z, w1 - z} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show z ∈ ({z, w, w1} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simpa using Submodule.zero_mem (Submodule.span ℝ ({w - z, w1 - z} : Set V3))
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨w, by simp, rfl⟩
      · exact Submodule.subset_span ⟨w1, by simp, rfl⟩
  have hle : finrank ℝ (affineSpan ℝ ({z, w, w1} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact finrank_span_pair_le_two (w - z) (w1 - z)
  rw [hdir, finrank_top] at hle
  have h3 : finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  omega

/-- 显式三元仿射组合入三点仿射包。 -/
private theorem mem_affineSpan_triple_of_eq {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (q - x) + h • (p - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : c • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd4 : h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd5 : c • (q - x) + h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval : y = h • (p - x) +ᵥ (c • (q - x) +ᵥ x) := by
    rw [hy, vadd_eq_add, vadd_eq_add]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd4
    (AffineSubspace.vadd_mem_of_mem_direction hd3 hxS)

/-- `affGt {z,w} {w1}` 含于平面 `affineSpan {z,w,w1}`。 -/
private theorem affGt_pair_subset_affineSpan {z w w1 : V3}
    (h1 : ¬ Collinear3 z w w1) :
    affGt ({z, w} : Set V3) {w1} ⊆ affineSpan ℝ ({z, w, w1} : Set V3) := by
  have hzw : z ≠ w := fun he => h1 (collinear3_of_eq he.symm)
  have hw1z : w1 ≠ z := fun he => h1 (collinear3_pair_left he)
  have hw1w : w1 ≠ w := fun he => h1 (collinear3_pair_right he)
  intro p hp
  obtain ⟨c, hc, h, hpeq⟩ :=
    (affGt_pair_iff (v0 := z) (v1 := w) (x := w1) (y := p) hzw hw1z hw1w).mp hp
  refine mem_affineSpan_triple_of_eq (x := z) (p := w) (q := w1) (c := c) (h := h) ?_
  rw [show p = (p - z) + z by abel, hpeq]
  abel

/-- `azim z w w1 w2 = 0` 时 `affGt {z,w}{w1,w2} ⊆ affineSpan {z,w,w1}`。 -/
private theorem affGt_subset_span_of_azim_zero {z w w1 w2 : V3}
    (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2)
    (h0 : azim z w w1 w2 = 0) :
    affGt ({z, w} : Set V3) {w1, w2} ⊆ affineSpan ℝ ({z, w, w1} : Set V3) := by
  by_cases h12 : w1 = w2
  · rw [h12, show ({w2, w2} : Set V3) = {w2} from by ext q; simp]
    exact affGt_pair_subset_affineSpan h2
  · have hzw : z ≠ w := fun he => h1 (collinear3_of_eq he.symm)
    have hw1z : w1 ≠ z := fun he => h1 (collinear3_pair_left he)
    have hw1w : w1 ≠ w := fun he => h1 (collinear3_pair_right he)
    have hw2mem : w2 ∈ affGt ({z, w} : Set V3) {w1} :=
      (azim_eq_zero_iff_alt h1 h2).mp h0
    obtain ⟨c, hc, δ₀, hw2eq⟩ :=
      (affGt_pair_iff (v0 := z) (v1 := w) (x := w1) (y := w2)
        hzw hw1z hw1w).mp hw2mem
    have hz_w1 : z ≠ w1 := Ne.symm hw1z
    have hz_w2 : z ≠ w2 := fun he => h2 (collinear3_pair_left he.symm)
    have hw_w1 : w ≠ w1 := Ne.symm hw1w
    have hw_w2 : w ≠ w2 := fun he => h2 (collinear3_pair_right he.symm)
    intro p hp
    obtain ⟨β, γ, δ, hβ, hγ, hpeq⟩ :=
      (mem_affGt_two_pairs_iff hzw hz_w1 hz_w2 hw_w1 hw_w2 h12).mp hp
    have hpeq' : p - z = (β + γ * c) • (w1 - z) + (δ + γ * δ₀) • (w - z) := by
      rw [hpeq, hw2eq]
      module
    refine mem_affineSpan_triple_of_eq (x := z) (p := w) (q := w1)
      (c := β + γ * c) (h := δ + γ * δ₀) ?_
    rw [show p = (p - z) + z by abel, hpeq']
    abel

/-- HOL `HAS_MEASURE_LUNE`（`flyspeck.ml:5529`）。 -/
theorem volume_ball_affGt {z w w1 w2 : V3} {r : ℝ} (hr : 0 ≤ r)
    (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2) (hne : w ≠ z)
    (hdi : dihV z w w1 w2 ≠ Real.pi) :
    volume (Metric.ball z r ∩ affGt ({z, w} : Set V3) {w1, w2}) =
      ENNReal.ofReal (dihV z w w1 w2 * 2 * r ^ 3 / 3) := by
  rcases lt_or_ge (azim z w w1 w2) Real.pi with hθlt | hθge
  · rcases eq_or_lt_of_le (azim_nonneg z w w1 w2) with hθzero | hθpos
    · have hazim : azim z w w1 w2 = 0 := hθzero.symm
      have hdihv : dihV z w w1 w2 = 0 := by
        have hsame := azim_dihv_same h1 h2 (by rw [hazim]; exact Real.pi_pos)
        rw [← hsame, hazim]
      have hP0 : volume ((affineSpan ℝ ({z, w, w1} : Set V3)) : Set V3) = 0 :=
        MeasureTheory.Measure.addHaar_affineSubspace volume _
          (affineSpan_three_ne_top z w w1)
      have hballP0 : volume (Metric.ball z r ∩
          ((affineSpan ℝ ({z, w, w1} : Set V3)) : Set V3)) = 0 :=
        measure_mono_null Set.inter_subset_right hP0
      have hsubset := affGt_subset_span_of_azim_zero h1 h2 hazim
      have hnull : volume (Metric.ball z r ∩ affGt ({z, w} : Set V3) {w1, w2}) = 0 :=
        measure_mono_null (Set.inter_subset_inter_right (Metric.ball z r) hsubset) hballP0
      rw [hnull, hdihv]
      simp
    · have hwedge := wedge_eq_affGt h1 h2 hθpos hθlt
      have hdihv : dihV z w w1 w2 = azim z w w1 w2 :=
        (azim_dihv_same h1 h2 hθlt).symm
      rw [← hwedge, hdihv]
      exact volume_ball_wedge hr
  · have hθne0 : azim z w w1 w2 ≠ 0 := by linarith [Real.pi_pos]
    have hcompl := azim_dihv_compl h1 h2 hθge
    have hθneπ : azim z w w1 w2 ≠ Real.pi := by
      intro h
      rw [h] at hcompl
      exact hdi (by linarith)
    have hθgtπ : Real.pi < azim z w w1 w2 :=
      lt_of_le_of_ne hθge (Ne.symm hθneπ)
    have hazim21 : azim z w w2 w1 = 2 * Real.pi - azim z w w1 w2 := by
      rw [azim_compl h1 h2, if_neg hθne0]
    have hazim21_pos : 0 < azim z w w2 w1 := by
      rw [hazim21]; linarith [azim_lt_two_pi z w w1 w2]
    have hazim21_ltπ : azim z w w2 w1 < Real.pi := by
      rw [hazim21]; linarith
    have hwedge := wedge_eq_affGt h2 h1 hazim21_pos hazim21_ltπ
    have hdihv : dihV z w w1 w2 = azim z w w2 w1 := by
      rw [hazim21]; linarith
    rw [show ({w1, w2} : Set V3) = {w2, w1} from Set.pair_comm w1 w2,
      ← hwedge, hdihv]
    exact volume_ball_wedge hr

/-! ## 不共面情形（HOL `HAS_MEASURE_LUNE_SIMPLE`，`flyspeck.ml:5614`） -/

/-- 两点 collinear ↔ 仿射包成员（两点互异时）。 -/
private theorem collinear3_iff_mem_affineSpan {v0 v1 y : V3} (hv0v1 : v0 ≠ v1) :
    Collinear3 v0 v1 y ↔
      y ∈ (affineSpan ℝ ({v0, v1} : Set V3) : Set V3) := by
  constructor
  · intro hc
    by_cases hy0 : y = v0
    · rw [hy0]; exact left_mem_affineSpan_pair _ _ _
    by_cases hy1 : y = v1
    · rw [hy1]; exact right_mem_affineSpan_pair _ _ _
    obtain ⟨c, hsmul⟩ := (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mp hc
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (sub_eq_iff_eq_add.mp hsmul).symm
  · intro hy
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    by_cases hy1 : y = v1
    · rw [hy1]; exact collinear3_pair_right (v0 := v0) (v1 := v1) rfl
    have hsmul : y - v0 = r • (v1 - v0) := by
      rw [← hr]
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mpr ⟨r, hsmul⟩

/-- 三点共线 ⟹ 加点后共面（`{z,w,w1,w2}`）。 -/
private theorem coplanar_of_collinear3 {z w w1 w2 : V3}
    (hc : Collinear3 z w w1) : Coplanar ({z, w, w1, w2} : Set V3) := by
  by_cases hzw : z = w
  · subst hzw
    refine ⟨z, w1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact mem_affineSpan ℝ (by simp)
  · have hw1 : w1 ∈ (affineSpan ℝ ({z, w} : Set V3) : Set V3) :=
      (collinear3_iff_mem_affineSpan hzw).mp hc
    refine ⟨z, w, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · refine affineSpan_mono ℝ ?_ hw1
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      tauto
    · exact mem_affineSpan ℝ (by simp)

/-- `e^{i(ψ+π)} = -e^{iψ}`。 -/
private theorem exp_add_pi (ψ : ℝ) :
    Complex.exp (((ψ + Real.pi : ℝ) : ℂ) * I)
      = -Complex.exp (((ψ : ℝ) : ℂ) * I) := by
  rw [show (((ψ + Real.pi : ℝ)) : ℂ) * I
        = ((ψ : ℝ) : ℂ) * I + ((Real.pi : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `azim z w w1 w2 = π` 时四点共面。 -/
private theorem coplanar_of_azim_pi {z w w1 w2 : V3}
    (h1 : ¬ Collinear3 z w w1) (h2 : ¬ Collinear3 z w w2)
    (hpi : azim z w w1 w2 = Real.pi) :
    Coplanar ({z, w, w1, w2} : Set V3) := by
  have hwv : w ≠ z := fun he => h1 (collinear3_of_eq he)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (w - z) (sub_ne_zero.mpr hwv)
  have hax : (w - z : V3) = dist w z • e3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec h1 h2 hon hax hwv
  have hr1ne : ((r1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr1.ne'
  have hz2' : zOf e1 e2 (w2 - z) = -(((r2 / r1 : ℝ) : ℂ) * zOf e1 e2 (w1 - z)) := by
    rw [hz1, hz2, hpi, exp_add_pi]
    push_cast
    field_simp [hr1ne]
  have hzero : zOf e1 e2 (w2 - z + ((r2 / r1 : ℝ) • (w1 - z))) = 0 := by
    rw [zOf_add, zOf_smul, hz2']
    ring
  obtain ⟨c, hc⟩ := (zOf_eq_zero_iff_axis hon hax hwv _).mp hzero
  have hc' : w2 - z = (-(r2 / r1)) • (w1 - z) + c • (w - z) := by
    rw [← hc]; module
  have hw2span : w2 ∈ affineSpan ℝ ({z, w, w1} : Set V3) := by
    refine mem_affineSpan_triple_of_eq (x := z) (p := w) (q := w1)
      (c := -(r2 / r1)) (h := c) ?_
    rw [show w2 = (w2 - z) + z by abel, hc']
    abel
  refine ⟨z, w, w1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact hw2span

/-- `¬ Coplanar {z,w,w1,w2} ⟹ ¬ Collinear3 z w w1`。 -/
private theorem not_coplanar_not_collinear_left {z w w1 w2 : V3}
    (hcop : ¬ Coplanar ({z, w, w1, w2} : Set V3)) : ¬ Collinear3 z w w1 :=
  fun hc => hcop (coplanar_of_collinear3 hc)

/-- `¬ Coplanar {z,w,w1,w2} ⟹ ¬ Collinear3 z w w2`。 -/
private theorem not_coplanar_not_collinear_right {z w w1 w2 : V3}
    (hcop : ¬ Coplanar ({z, w, w1, w2} : Set V3)) : ¬ Collinear3 z w w2 := by
  intro hc
  apply hcop
  have h := coplanar_of_collinear3 (z := z) (w := w) (w1 := w2) (w2 := w1) hc
  rwa [show ({z, w, w2, w1} : Set V3) = {z, w, w1, w2} from by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h

/-- `¬ Coplanar {z,w,w1,w2} ⟹ w ≠ z`。 -/
private theorem not_coplanar_w_ne_z {z w w1 w2 : V3}
    (hcop : ¬ Coplanar ({z, w, w1, w2} : Set V3)) : w ≠ z := by
  intro hwz
  apply hcop
  rw [hwz]
  have hset : ({z, z, w1, w2} : Set V3) = {z, w1, w2} := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact coplanar_triple z w1 w2

/-- `¬ Coplanar {z,w,w1,w2} ⟹ dihV z w w1 w2 ≠ π`。 -/
private theorem not_coplanar_dihv_ne_pi {z w w1 w2 : V3}
    (hcop : ¬ Coplanar ({z, w, w1, w2} : Set V3)) :
    dihV z w w1 w2 ≠ Real.pi := by
  have h1 := not_coplanar_not_collinear_left hcop
  have h2 := not_coplanar_not_collinear_right hcop
  intro hdi
  have hazim : azim z w w1 w2 = Real.pi := by
    rcases lt_or_ge (azim z w w1 w2) Real.pi with hlt | hge
    · rw [azim_dihv_same h1 h2 hlt]; exact hdi
    · rw [azim_dihv_compl h1 h2 hge]; linarith
  exact hcop (coplanar_of_azim_pi h1 h2 hazim)

/-- HOL `HAS_MEASURE_LUNE_SIMPLE`（`flyspeck.ml:5614`）。 -/
theorem volume_ball_affGt_simple {z w w1 w2 : V3} {r : ℝ} (hr : 0 ≤ r)
    (hcop : ¬ Coplanar ({z, w, w1, w2} : Set V3)) :
    volume (Metric.ball z r ∩ affGt ({z, w} : Set V3) {w1, w2}) =
      ENNReal.ofReal (dihV z w w1 w2 * 2 * r ^ 3 / 3) :=
  volume_ball_affGt hr (not_coplanar_not_collinear_left hcop)
    (not_coplanar_not_collinear_right hcop) (not_coplanar_w_ne_z hcop)
    (not_coplanar_dihv_ne_pi hcop)

end Kepler.Geom
