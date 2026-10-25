/-
Kepler.Text.EulerSimplexGeom — Euler 泛型立体角工程 W2 波：几何层。

HOL 正本：
- `trigonometry/delta_x.hl:41-230`（COMPUTE_DELTA_X / DELTA_X_DET_3 /
  DELTA_X_LT_0_COLLINEAR）；
- `nonlinear/merge_ineq.hl:694-840`（vector_of_simplex_dot /
  vector_of_simplex_edge_lemma / simplex_exists / DIHV_EQ_DIH_Y /
  DIHV_DIH_X）；
- `trigonometry/euler_complement.hl:92-113`（DIHV_RESCALE_UNCHANGED）与
  :230-330（COMPUTE_DELTA_X_AFTER_RESCALE / sqrt_delta_x_after_rescale）。

主干四件（public）：
- `ea2_delta_eq_four_det_sq`：Δ = 4·det²（det = 三重积 = Matrix.det 行展开，
  见 `ea2_chi_eq_det`）；
- `ea2_not_collinear_of_delta_pos`：Δ>0 ⇒ 三组非共线；
- `ea2_simplex_exists`（+ `ea2_simplex_exists_y`）：六棱定四面体，
  显式坐标构造（merge:758 的 vector_of_simplex_edge_lemma 坐标）+ 三组
  非共线 + 三重积非零（非共面）；
- `ea2_dihV_eq_dih_y` / `ea2_dihV_dih_x`（dihV 桥，展开角 = LuneVolume.dihV
  投影定义，勿重定义）+ `ea2_dihv_rescale_unchanged` + `ea2_sqrt_delta_rescale`
  （√Δ 重标）。

import 只取既有真证模块（SphereKit canonical defs + Geom.LuneVolume dihV/
azim/Collinear3 kit），不 import PackingAuto18/21/25；PA18 私件
（pa18_deltaP_eq_chi 的标量化）与 W2a atn2 件以 ea2_ 前缀自带。
全部真证，全文无占位缺口词。
-/

import Kepler.Text.SphereKit
import Kepler.Geom.LuneVolume

open Kepler.Geom

noncomputable section

namespace Kepler.Text

/-! ## 私有 kit：V3 / Pi 点积与 coe 运算 -/

private theorem ea2_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem ea2_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem ea2_smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem ea2_dot_smul (a : V3) (t : ℝ) (b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem ea2_sub_dot (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem ea2_dot_sub (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem ea2_dot_smul_pi (x : Fin 3 → ℝ) (t : ℝ) (y : Fin 3 → ℝ) :
    x ⬝ᵥ (t • y) = t * (x ⬝ᵥ y) := dotProduct_smul t x y

private theorem ea2_dot_neg_pi (x y : Fin 3 → ℝ) : x ⬝ᵥ (-y) = -(x ⬝ᵥ y) :=
  dotProduct_neg x y

private theorem ea2_neg_dot_pi (x y : Fin 3 → ℝ) : (-x) ⬝ᵥ y = -(x ⬝ᵥ y) :=
  neg_dotProduct x y

private theorem ea2_smul_cross_left (t : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct (t • x) y = t • (crossProduct x y) := by
  show ((crossProduct (t • x : Fin 3 → ℝ)) y) = _
  rw [map_smul, LinearMap.smul_apply]

private theorem ea2_cross_smul_right (x : Fin 3 → ℝ) (t : ℝ) (y : Fin 3 → ℝ) :
    crossProduct x (t • y) = t • (crossProduct x y) := by
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

private theorem ea2_dot_negneg (x y : V3) : ((-x : V3)) ⬝ᵥ ((-y : V3)) = x ⬝ᵥ y := by
  show ((-x : V3) : Fin 3 → ℝ) ⬝ᵥ ((-y : V3) : Fin 3 → ℝ)
      = ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ)
  rw [WithLp.ofLp_neg, WithLp.ofLp_neg, neg_dotProduct_neg]

private theorem ea2_dist_sq (x y : V3) :
    dist x y ^ 2 = ((y - x : V3)) ⬝ᵥ ((y - x : V3)) := by
  rw [dist_eq_norm]
  have h : ((x : V3) - y) = -((y : V3) - x) := by abel
  rw [h, norm_neg, norm_sq_eq_dot]

private theorem ea2_dist_sq' (x y : V3) :
    dist x y ^ 2 = ((x - y : V3)) ⬝ᵥ ((x - y : V3)) := by
  rw [ea2_dist_sq, show ((x : V3) - y) = -((y : V3) - x) from by abel, ea2_dot_negneg]

/-- `dist` 的平方按分量展开（显式坐标构造用）。 -/
private theorem ea2_dist_sq_components (u v : V3) :
    dist u v ^ 2 = ((WithLp.ofLp u) 0 - (WithLp.ofLp v) 0) ^ 2 +
      ((WithLp.ofLp u) 1 - (WithLp.ofLp v) 1) ^ 2 +
      ((WithLp.ofLp u) 2 - (WithLp.ofLp v) 2) ^ 2 := by
  rw [dist_eq_norm, norm_sq_eq_dot]
  have hcoe : ((u - v : V3) : Fin 3 → ℝ) = (WithLp.ofLp u) - (WithLp.ofLp v) := rfl
  rw [hcoe]
  simp only [sub_dotProduct, dotProduct_sub]
  have hcom : (WithLp.ofLp u : Fin 3 → ℝ) ⬝ᵥ (WithLp.ofLp v : Fin 3 → ℝ)
      = (WithLp.ofLp v : Fin 3 → ℝ) ⬝ᵥ (WithLp.ofLp u : Fin 3 → ℝ) :=
    dotProduct_comm _ _
  rw [hcom]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons]
  ring

private theorem ea2_dmix (f g : Fin 3 → ℝ) :
    (f - g) ⬝ᵥ (f - g) = f ⬝ᵥ f + g ⬝ᵥ g - 2 * (f ⬝ᵥ g) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm f g]
  ring

/-! ## 私有 kit：标量原子恒等式（ups/delta_x 家族的 Gram 形） -/

private theorem ea2_ups_atoms (A B C D : ℝ) :
    upsX C A (A + C - 2 * D) = 4 * (C * A - D * D) := by
  simp only [upsX]
  ring

private theorem ea2_d4_atoms (A B C AB AC BC : ℝ) :
    deltaX4 C A B (A + B - 2 * AB) (B + C - 2 * BC) (A + C - 2 * AC)
      = 4 * (C * AB - AC * BC) := by
  simp only [deltaX4]
  ring

private theorem ea2_delta_atoms (A B C AB AC BC : ℝ) :
    deltaX C A B (A + B - 2 * AB) (B + C - 2 * BC) (A + C - 2 * AC)
      = 4 * (A * B * C + 2 * (AB * AC * BC) - A * (BC * BC) - B * (AC * AC) - C * (AB * AB)) := by
  simp only [deltaX]
  ring

/-- HOL `DELTA_X_AND_DELTA_X4`（merge:770）：`4·x1·Δ = ups1·ups2 − δ4²`
的距离变量形。 -/
private theorem ea2_hkey_atoms (A B C AB AC BC : ℝ) :
    4 * C * deltaX C A B (A + B - 2 * AB) (B + C - 2 * BC) (A + C - 2 * AC)
      = upsX C A (A + C - 2 * AC) * upsX C B (B + C - 2 * BC)
        - deltaX4 C A B (A + B - 2 * AB) (B + C - 2 * BC) (A + C - 2 * AC) ^ 2 := by
  simp only [deltaX, upsX, deltaX4]
  ring

private theorem ea2_chi_sq_atoms (a b c : Fin 3 → ℝ) :
    (crossProduct a b ⬝ᵥ c) ^ 2
      = (a ⬝ᵥ a) * (b ⬝ᵥ b) * (c ⬝ᵥ c) + 2 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c))
        - (a ⬝ᵥ a) * (b ⬝ᵥ c) ^ 2 - (b ⬝ᵥ b) * (a ⬝ᵥ c) ^ 2 - (c ⬝ᵥ c) * (a ⬝ᵥ b) ^ 2 := by
  rw [cross_apply]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

private theorem ea2_norm_cross_sq (a b : Fin 3 → ℝ) :
    (crossProduct a b) ⬝ᵥ (crossProduct a b) = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
  rw [cross_apply]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 私有 kit：共线 ⇔ 叉积为零 -/

private theorem ea2_collinear3_iff_cross (v w w1 : V3) :
    Collinear3 v w w1 ↔ crossProduct ((w - v : V3) : Fin 3 → ℝ) ((w1 - v : V3) : Fin 3 → ℝ) = 0 := by
  constructor
  · intro hcol
    by_cases hw : w = v
    · subst hw
      have h0 : ((w - w : V3) : Fin 3 → ℝ) = 0 := by simp
      rw [h0, LinearMap.map_zero, LinearMap.zero_apply]
    · obtain ⟨c, hc⟩ := (collinear3_iff_smul hw).mp hcol
      have hcoe : ((w1 - v : V3) : Fin 3 → ℝ) = c • ((w - v : V3) : Fin 3 → ℝ) := by
        have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hc
        simpa only [ea2_coe_smul] using h
      rw [hcoe, LinearMap.map_smul, cross_self, smul_zero]
  · intro hcross
    by_cases hw : w = v
    · exact collinear3_of_eq hw
    · rw [collinear3_iff_smul hw]
      have hfne : ((w - v : V3) : Fin 3 → ℝ) ≠ 0 := by
        intro hz
        exact hw (sub_eq_zero.mp
          ((WithLp.ofLp_injective (p := 2)) (by simpa using hz)))
      have hli : ¬ LinearIndependent ℝ ![((w - v : V3) : Fin 3 → ℝ),
          ((w1 - v : V3) : Fin 3 → ℝ)] :=
        (crossProduct_ne_zero_iff_linearIndependent
          (v := ((w - v : V3) : Fin 3 → ℝ)) (w := ((w1 - v : V3) : Fin 3 → ℝ))).not.mp
            (not_not.mpr hcross)
      have hnel' : ¬ (∀ a : ℝ, a • ((w - v : V3) : Fin 3 → ℝ)
          ≠ ((w1 - v : V3) : Fin 3 → ℝ)) :=
        fun hcon => hli ((LinearIndependent.pair_iff' hfne).mpr hcon)
      push_neg at hnel'
      obtain ⟨a, ha⟩ := hnel'
      exact ⟨a, WithLp.ofLp_injective (p := 2) (by simpa only [ea2_coe_smul] using ha.symm)⟩

/-! ## 主干一件：Δ = 4·det² -/

/-- `chi`（有向体积三重积）等于行行列式的循环置换
`Matrix.det ![v3−v0, v1−v0, v2−v0]`（Mathlib `triple_product_eq_det`；
循环置换为偶置换，行列式值与 `det ![v1−v0, v2−v0, v3−v0]` 相同）。 -/
theorem ea2_chi_eq_det (v0 v1 v2 v3 : V3) :
    crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ) ((v2 - v0 : V3) : Fin 3 → ℝ)
        ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
      = Matrix.det ![((v3 - v0 : V3) : Fin 3 → ℝ), ((v1 - v0 : V3) : Fin 3 → ℝ),
          ((v2 - v0 : V3) : Fin 3 → ℝ)] := by
  rw [dotProduct_comm (crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ)
      ((v2 - v0 : V3) : Fin 3 → ℝ)) ((v3 - v0 : V3) : Fin 3 → ℝ)]
  exact triple_product_eq_det
    (u := ((v3 - v0 : V3) : Fin 3 → ℝ)) (v := ((v1 - v0 : V3) : Fin 3 → ℝ))
    (w := ((v2 - v0 : V3) : Fin 3 → ℝ))

/-- **DELTA_X_DET_3 / COMPUTE_DELTA_X**（delta_x.hl:45-139）：四点的
Cayley–Menger 型 Δ 等于 `4·det²`（det = 三重积有向体积）。 -/
theorem ea2_delta_eq_four_det_sq (v0 v1 v2 v3 : V3) :
    deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)
      = 4 * (crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ)
          ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)) ^ 2 := by
  set a : Fin 3 → ℝ := ((v1 - v0 : V3) : Fin 3 → ℝ) with hda
  set b : Fin 3 → ℝ := ((v2 - v0 : V3) : Fin 3 → ℝ) with hdb
  set c : Fin 3 → ℝ := ((v3 - v0 : V3) : Fin 3 → ℝ) with hdc
  have e1 : dist v0 v1 ^ 2 = a ⬝ᵥ a := by rw [ea2_dist_sq, ← hda]
  have e2 : dist v0 v2 ^ 2 = b ⬝ᵥ b := by rw [ea2_dist_sq, ← hdb]
  have e3 : dist v0 v3 ^ 2 = c ⬝ᵥ c := by rw [ea2_dist_sq, ← hdc]
  have h12 : ((v2 - v1 : V3) : Fin 3 → ℝ) = b - a := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ))
      (show (v2 : V3) - v1 = (v2 - v0) - (v1 - v0) from by abel)
    simpa only [ea2_coe_sub, hdb, hda] using h
  have h13 : ((v3 - v1 : V3) : Fin 3 → ℝ) = c - a := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ))
      (show (v3 : V3) - v1 = (v3 - v0) - (v1 - v0) from by abel)
    simpa only [ea2_coe_sub, hdc, hda] using h
  have h23 : ((v2 - v3 : V3) : Fin 3 → ℝ) = b - c := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ))
      (show (v2 : V3) - v3 = (v2 - v0) - (v3 - v0) from by abel)
    simpa only [ea2_coe_sub, hdb, hdc] using h
  have e6 : dist v1 v2 ^ 2 = (b - a) ⬝ᵥ (b - a) := by rw [ea2_dist_sq, h12]
  have e5 : dist v1 v3 ^ 2 = (c - a) ⬝ᵥ (c - a) := by rw [ea2_dist_sq, h13]
  have e4 : dist v2 v3 ^ 2 = (b - c) ⬝ᵥ (b - c) := by rw [ea2_dist_sq', h23]
  rw [e1, e2, e3, e4, e5, e6, ea2_dmix b c, ea2_dmix c a, ea2_dmix b a,
    ea2_delta_atoms (b ⬝ᵥ b) (c ⬝ᵥ c) (a ⬝ᵥ a) (b ⬝ᵥ c) (b ⬝ᵥ a) (c ⬝ᵥ a),
    ea2_chi_sq_atoms a b c, dotProduct_comm c a, dotProduct_comm b a]
  ring

/-! ## 主干二件：Δ > 0 ⇒ 三非共线 -/

/-- **DELTA_X_LT_0_COLLINEAR**（delta_x.hl:141-230）：`Δ > 0` 时三组
`{v0,v1,v2}`、`{v0,v1,v3}`、`{v0,v3,v2}` 全部非共线。 -/
theorem ea2_not_collinear_of_delta_pos (v0 v1 v2 v3 : V3)
    (hd : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)) :
    ¬ Collinear3 v0 v1 v2 ∧ ¬ Collinear3 v0 v1 v3 ∧ ¬ Collinear3 v0 v3 v2 := by
  have h1 := ea2_delta_eq_four_det_sq v0 v1 v2 v3
  have hchi : crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ)
      ((v2 - v0 : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) ≠ 0 := by
    intro hz
    rw [hz] at h1
    rw [h1] at hd
    norm_num at hd
  refine ⟨fun hcol => ?_, fun hcol => ?_, fun hcol => ?_⟩
  · have hc : crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ)
        ((v2 - v0 : V3) : Fin 3 → ℝ) = 0 := (ea2_collinear3_iff_cross v0 v1 v2).mp hcol
    rw [hc] at hchi
    simp at hchi
  · by_cases hv : v1 = v0
    · have hva : ((v1 - v0 : V3) : Fin 3 → ℝ) = 0 := by rw [hv]; simp
      rw [hva] at hchi
      simp at hchi
    · obtain ⟨s, hs⟩ := (collinear3_iff_smul hv).mp hcol
      have hs' : ((v3 - v0 : V3) : Fin 3 → ℝ) = s • ((v1 - v0 : V3) : Fin 3 → ℝ) := by
        have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hs
        simpa only [ea2_coe_smul] using h
      rw [hs'] at hchi
      rw [ea2_dot_smul_pi, ← cross_anticomm, ea2_neg_dot_pi,
        dotProduct_comm (crossProduct ((v2 - v0 : V3) : Fin 3 → ℝ)
          ((v1 - v0 : V3) : Fin 3 → ℝ)) ((v1 - v0 : V3) : Fin 3 → ℝ),
        dot_cross_self, neg_zero, mul_zero] at hchi
      exact hchi rfl
  · by_cases hv : v3 = v0
    · have hvc : ((v3 - v0 : V3) : Fin 3 → ℝ) = 0 := by rw [hv]; simp
      rw [hvc] at hchi
      simp at hchi
    · obtain ⟨s, hs⟩ := (collinear3_iff_smul hv).mp hcol
      have hs' : ((v2 - v0 : V3) : Fin 3 → ℝ) = s • ((v3 - v0 : V3) : Fin 3 → ℝ) := by
        have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hs
        simpa only [ea2_coe_smul] using h
      rw [hs'] at hchi
      rw [ea2_cross_smul_right, smul_dotProduct, smul_eq_mul,
        dotProduct_comm (crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ)
          ((v3 - v0 : V3) : Fin 3 → ℝ)) ((v3 - v0 : V3) : Fin 3 → ℝ),
        dot_cross_self, mul_zero] at hchi
      exact hchi rfl

/-- 非共线 ⇔ 三点距离平方的 ups 正（COL_EQ_UPS_0 的双向形式，
collect_geom2.hl:1420 `NOT_COL_EQ_UPS_X_POS`）。 -/
theorem ea2_upsX_pos_iff (a b c : V3) :
    0 < upsX (dist a b ^ 2) (dist a c ^ 2) (dist b c ^ 2) ↔ ¬ Collinear3 a b c := by
  set f : Fin 3 → ℝ := ((b - a : V3) : Fin 3 → ℝ) with hf
  set g : Fin 3 → ℝ := ((c - a : V3) : Fin 3 → ℝ) with hg
  have e1 : dist a b ^ 2 = f ⬝ᵥ f := by rw [ea2_dist_sq, ← hf]
  have e2 : dist a c ^ 2 = g ⬝ᵥ g := by rw [ea2_dist_sq, ← hg]
  have hcb : ((c - b : V3) : Fin 3 → ℝ) = g - f := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ))
      (show (c : V3) - b = (c - a) - (b - a) from by abel)
    simpa only [ea2_coe_sub, hg, hf] using h
  have e3 : dist b c ^ 2 = (g - f) ⬝ᵥ (g - f) := by rw [ea2_dist_sq, hcb]
  have hups : upsX (dist a b ^ 2) (dist a c ^ 2) (dist b c ^ 2)
      = 4 * ((crossProduct f g) ⬝ᵥ (crossProduct f g)) := by
    rw [e1, e2, e3, ea2_dmix g f, ea2_ups_atoms (g ⬝ᵥ g) (f ⬝ᵥ f) (f ⬝ᵥ f) (g ⬝ᵥ f),
      dotProduct_comm g f, ea2_norm_cross_sq f g]
    ring
  constructor
  · intro hpos hcol
    have hcz : crossProduct f g = 0 := (ea2_collinear3_iff_cross a b c).mp hcol
    rw [hcz] at hups
    simp at hups
    linarith
  · intro hnc
    have hcz : crossProduct f g ≠ 0 := by
      intro hz
      apply hnc
      exact (ea2_collinear3_iff_cross a b c).mpr hz
    rw [hups]
    have hvne : (WithLp.toLp 2 (crossProduct f g) : V3) ≠ 0 := by
      intro hzz
      exact hcz (by simpa using hzz)
    have hpos : 0 < (crossProduct f g) ⬝ᵥ (crossProduct f g) := by
      have h2 : (crossProduct f g) ⬝ᵥ (crossProduct f g)
          = ‖(WithLp.toLp 2 (crossProduct f g) : V3)‖ ^ 2 := (norm_sq_eq_dot _).symm
      rw [h2]
      exact pow_pos (norm_pos_iff.mpr hvne) 2
    exact mul_pos (by norm_num) hpos

/-! ## 私有 kit：atn2 三件（SphereKit.atn2 展开分支）

W2a 的 `mi_p21e_atn2` 族在 PA21 内（勿 import），此处按 8 前提锚的
需要自带泛型版。 -/

private theorem ea2_atn2_pos_compat {x y a : ℝ} (ha : 0 < a) :
    atn2 x y = atn2 (a * x) (a * y) := by
  simp only [atn2]
  by_cases h1 : |y| < x
  · have h1' : |a * y| < a * x := by
      rw [abs_mul, abs_of_pos ha]
      exact mul_lt_mul_of_pos_left h1 ha
    rw [if_pos h1', if_pos h1, mul_div_mul_left _ _ (ne_of_gt ha)]
  · have hcL : ¬(|a * y| < a * x) := by
      intro hcon
      rw [abs_mul, abs_of_pos ha] at hcon
      apply h1
      have hinv : 0 < a⁻¹ := inv_pos.mpr ha
      have h3' := mul_lt_mul_of_pos_left hcon hinv
      rwa [inv_mul_cancel_left₀ (ne_of_gt ha),
        inv_mul_cancel_left₀ (ne_of_gt ha)] at h3'
    by_cases h2 : 0 < y
    · rw [if_neg hcL, if_pos (mul_pos ha h2), if_neg h1, if_pos h2,
        mul_div_mul_left _ _ (ne_of_gt ha)]
    · by_cases h3 : y < 0
      · have hn3 : ¬(0 < a * y) := by
          intro hc
          linarith [mul_neg_of_pos_of_neg ha h3]
        have hp3' : a * y < 0 := mul_neg_of_pos_of_neg ha h3
        rw [if_neg hcL, if_neg hn3, if_pos hp3', if_neg h1, if_neg h2, if_pos h3,
          mul_div_mul_left _ _ (ne_of_gt ha)]
      · have hz : y = 0 := by linarith
        have hn3 : ¬(0 < a * y) := by rw [hz]; simp
        have hp3' : ¬(a * y < 0) := by rw [hz]; simp
        rw [if_neg hcL, if_neg hn3, if_neg hp3', if_neg h1, if_neg h2, if_neg h3]

/-- `atn2` 的正因子除法版。 -/
private theorem ea2_atn2_pos_div {x y c : ℝ} (hc : 0 < c) :
    atn2 (x / c) (y / c) = atn2 x y := by
  have h := ea2_atn2_pos_compat (a := c) (x := x / c) (y := y / c) hc
  rw [show c * (x / c) = x from by field_simp,
    show c * (y / c) = y from by field_simp] at h
  exact h

/-- HOL `ATN2_RNEG`（trig1.hl:420）。 -/
private theorem ea2_atn2_rneg {x y : ℝ} (h : y ≠ 0 ∨ 0 < x) :
    atn2 x (-y) = -(atn2 x y) := by
  simp only [atn2]
  rw [abs_neg]
  by_cases h1 : |y| < x
  · rw [if_pos h1, if_pos h1, neg_div, Real.arctan_neg]
  · rcases h with h0 | hx
    · rcases lt_trichotomy y 0 with hlt | heq | hgt
      · rw [if_neg h1, if_pos (by linarith : (0:ℝ) < -y), if_neg h1,
          if_neg (by linarith : ¬(0:ℝ) < y), if_pos hlt,
          div_neg, Real.arctan_neg]
        ring
      · exact absurd heq h0
      · rw [if_neg h1, if_neg (by linarith : ¬(0:ℝ) < -y),
          if_pos (by linarith : -y < (0:ℝ)), if_neg h1, if_pos hgt,
          div_neg, Real.arctan_neg]
        ring
    · rcases lt_trichotomy y 0 with hlt | heq | hgt
      · rw [if_neg h1, if_pos (by linarith : (0:ℝ) < -y), if_neg h1,
          if_neg (by linarith : ¬(0:ℝ) < y), if_pos hlt,
          div_neg, Real.arctan_neg]
        ring
      · rw [heq] at h1
        exact absurd (by simpa using hx) h1
      · rw [if_neg h1, if_neg (by linarith : ¬(0:ℝ) < -y),
          if_pos (by linarith : -y < (0:ℝ)), if_neg h1, if_pos hgt,
          div_neg, Real.arctan_neg]
        ring

private theorem ea2_atn2_zero {x : ℝ} (hx : 0 < x) : atn2 x 0 = 0 := by
  unfold atn2
  have h0 : |0| < x := by simpa using hx
  rw [if_pos h0, zero_div]
  exact Real.arctan_zero

/-- HOL `acs_atn2`（trig1.hl:435）：`arccos y = π/2 − atn2(√(1−y²), y)`
于 `y ∈ [−1,1]`。 -/
private theorem ea2_arccos_eq_pi2_sub_atn2 {y : ℝ} (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Real.arccos y = Real.pi / 2 - atn2 (Real.sqrt (1 - y * y)) y := by
  have hφle : Real.arccos y ≤ Real.pi := Real.arccos_le_pi y
  have hφge : 0 ≤ Real.arccos y := Real.arccos_nonneg y
  have hcos : Real.cos (Real.arccos y) = y := Real.cos_arccos hy1 hy2
  have hsin2 : Real.sin (Real.arccos y) ^ 2 = 1 - y * y := by
    have hsq := Real.sin_sq_add_cos_sq (Real.arccos y)
    rw [hcos] at hsq
    linarith
  have hsinpos : 0 ≤ Real.sin (Real.arccos y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφge hφle
  have hs : Real.sqrt (1 - y * y) = Real.sin (Real.arccos y) := by
    rw [← hsin2, Real.sqrt_sq hsinpos]
  rw [hs]
  simp only [atn2]
  by_cases h1 : |y| < Real.sin (Real.arccos y)
  · have hφ0 : 0 < Real.arccos y := by
      rcases eq_or_lt_of_le hφge with h0 | h0
      · rw [h0.symm] at h1
        simp only [Real.sin_zero] at h1
        linarith [abs_nonneg y]
      · exact h0
    have hφπ : Real.arccos y < Real.pi := by
      rcases lt_or_ge (Real.arccos y) Real.pi with h0 | h0
      · exact h0
      · have hπ : Real.arccos y = Real.pi := le_antisymm hφle h0
        rw [hπ] at h1
        simp only [Real.sin_pi] at h1
        linarith [abs_nonneg y]
    have htan : Real.tan (Real.pi / 2 - Real.arccos y)
        = y / Real.sin (Real.arccos y) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub, hcos]
    rw [if_pos h1, htan.symm,
      Real.arctan_tan (by linarith : -(Real.pi / 2) < Real.pi / 2 - Real.arccos y)
        (by linarith : Real.pi / 2 - Real.arccos y < Real.pi / 2)]
    ring
  · by_cases h4 : y = 0
    · exfalso
      rw [h4] at h1
      norm_num at h1
    · by_cases h2 : 0 < y
      · have hφlt2 : Real.arccos y < Real.pi / 2 := by
          rcases lt_or_ge (Real.arccos y) (Real.pi / 2) with h | h
          · exact h
          · exfalso
            have ht1 : 0 ≤ Real.arccos y - Real.pi / 2 := by linarith
            have ht2 : Real.arccos y - Real.pi / 2 ≤ Real.pi / 2 := by
              linarith [hφle]
            have hsum := Real.cos_add (Real.pi / 2) (Real.arccos y - Real.pi / 2)
            have hsplit : Real.pi / 2 + (Real.arccos y - Real.pi / 2)
                = Real.arccos y := by ring
            rw [hsplit] at hsum
            simp only [Real.cos_pi_div_two, Real.sin_pi_div_two] at hsum
            have hsinnonneg : 0 ≤ Real.sin (Real.arccos y - Real.pi / 2) :=
              Real.sin_nonneg_of_nonneg_of_le_pi ht1
                (by linarith : Real.arccos y - Real.pi / 2 ≤ Real.pi)
            rw [← hcos] at h2
            rw [hsum] at h2
            linarith
        have hne : Real.cos (Real.arccos y) ≠ 0 := by
          rw [hcos]
          exact h4
        have hswap : Real.sin (Real.arccos y) / y = Real.tan (Real.arccos y) := by
          rw [Real.tan_eq_sin_div_cos, div_eq_div_iff h4 hne, hcos]
        rw [if_neg h1, if_pos h2, hswap,
          Real.arctan_tan (by linarith : -(Real.pi / 2) < Real.arccos y)
            (by linarith : Real.arccos y < Real.pi / 2)]
        ring
      · have h3 : y < 0 := by
          rcases eq_or_lt_of_le (by push_neg at h2; exact h2) with h | h
          · exact absurd h h4
          · exact h
        have hφgt : Real.pi / 2 < Real.arccos y := by
          rcases lt_or_ge (Real.arccos y) (Real.pi / 2) with h | h
          · exfalso
            have ht1 : 0 ≤ Real.pi / 2 - Real.arccos y := by linarith
            have ht2 : Real.pi / 2 - Real.arccos y ≤ Real.pi / 2 := by
              linarith [hφle]
            have hc := Real.cos_pi_div_two_sub (Real.pi / 2 - Real.arccos y)
            have hsplit : Real.pi / 2 - (Real.pi / 2 - Real.arccos y)
                = Real.arccos y := by ring
            rw [hsplit] at hc
            rw [hcos] at hc
            have hsinnonneg : 0 ≤ Real.sin (Real.pi / 2 - Real.arccos y) :=
              Real.sin_nonneg_of_nonneg_of_le_pi ht1
                (by linarith : Real.pi / 2 - Real.arccos y ≤ Real.pi)
            linarith
          · rcases eq_or_lt_of_le h with h0 | h0
            · exfalso
              have hc2 : Real.cos (Real.arccos y) = 0 := by
                rw [← h0]
                exact Real.cos_pi_div_two
              rw [hcos] at hc2
              exact h3.ne hc2
            · exact h0
        have hper : Real.tan (Real.arccos y)
            = Real.tan (Real.arccos y - Real.pi) := by
          have hsplit : Real.arccos y = (Real.arccos y - Real.pi) + Real.pi := by ring
          conv_lhs => rw [hsplit, Real.tan_periodic]
        have hne : Real.cos (Real.arccos y) ≠ 0 := by
          rw [hcos]
          exact h3.ne
        have hswap1 : Real.sin (Real.arccos y) / y
            = Real.tan (Real.arccos y) := by
          rw [Real.tan_eq_sin_div_cos, div_eq_div_iff h3.ne hne, hcos]
        have hswap : Real.sin (Real.arccos y) / y
            = Real.tan (Real.arccos y - Real.pi) := hswap1.trans hper
        rw [if_neg h1, if_neg (by linarith : ¬(0:ℝ) < y), if_pos h3, hswap,
          Real.arctan_tan (by linarith : -(Real.pi / 2) < Real.arccos y - Real.pi)
            (by linarith : Real.arccos y - Real.pi < Real.pi / 2)]
        ring


/-! ## 主干三件：六棱定四面体（simplex_exists） -/

/-- **simplex_exists**（merge_ineq.hl:746-768，显式坐标构造来自
`vector_of_simplex_edge_lemma` :720，强化为严格 `0 < Δ`）：六条棱长平方
`0 < x1`、`0 < upsX x1 x2 x6`、`0 < Δ` 时，存在四点实现全部六条距离，
且三组非共线、有向体积（三重积）非零（非共面）。 -/
theorem ea2_simplex_exists (x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1 : 0 < x1) (hu : 0 < upsX x1 x2 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    ∃ v0 v1 v2 v3 : V3,
      dist v0 v1 ^ 2 = x1 ∧ dist v0 v2 ^ 2 = x2 ∧ dist v0 v3 ^ 2 = x3 ∧
      dist v2 v3 ^ 2 = x4 ∧ dist v1 v3 ^ 2 = x5 ∧ dist v1 v2 ^ 2 = x6 ∧
      ¬ Collinear3 v0 v1 v2 ∧ ¬ Collinear3 v0 v1 v3 ∧ ¬ Collinear3 v0 v3 v2 ∧
      crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ) ((v2 - v0 : V3) : Fin 3 → ℝ)
          ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) ≠ 0 := by
  set y1 : ℝ := Real.sqrt x1 with hy1def
  set u1 : ℝ := Real.sqrt (upsX x1 x2 x6) with hu1def
  set d1 : ℝ := Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) with hd1def
  set Pp : ℝ := x1 * x1 - x1 * x2 - x1 * x3 + x2 * x3 + 2 * x1 * x4 - x1 * x5 -
    x2 * x5 - x1 * x6 - x3 * x6 + x5 * x6 with hpdef
  have hy1sq : y1 * y1 = x1 := by
    rw [hy1def]; exact Real.mul_self_sqrt hx1.le
  have hu1sq : u1 * u1 = upsX x1 x2 x6 := by
    rw [hu1def]; exact Real.mul_self_sqrt hu.le
  have hd1sq : d1 * d1 = deltaX x1 x2 x3 x4 x5 x6 := by
    rw [hd1def]; exact Real.mul_self_sqrt hd.le
  have hy1 : 0 < y1 := Real.sqrt_pos.mpr hx1
  have hu1 : 0 < u1 := Real.sqrt_pos.mpr hu
  have hd1 : 0 < d1 := Real.sqrt_pos.mpr hd
  -- 显式坐标（merge:723-733）
  set v1 : V3 := WithLp.toLp 2 ![y1, 0, 0] with hv1def
  set v2 : V3 := WithLp.toLp 2 ![(x1 + x2 - x6) / (2 * y1), u1 / (2 * y1), 0] with hv2def
  set v3 : V3 := WithLp.toLp 2 ![(x1 + x3 - x5) / (2 * y1),
    -Pp / (2 * y1 * u1), d1 / u1] with hv3def
  have kv10 : (WithLp.ofLp v1) 0 = y1 := by simp [hv1def]
  have kv11 : (WithLp.ofLp v1) 1 = 0 := by simp [hv1def]
  have kv12 : (WithLp.ofLp v1) 2 = 0 := by simp [hv1def]
  have kv20 : (WithLp.ofLp v2) 0 = (x1 + x2 - x6) / (2 * y1) := by simp [hv2def]
  have kv21 : (WithLp.ofLp v2) 1 = u1 / (2 * y1) := by simp [hv2def]
  have kv22 : (WithLp.ofLp v2) 2 = 0 := by simp [hv2def]
  have kv30 : (WithLp.ofLp v3) 0 = (x1 + x3 - x5) / (2 * y1) := by simp [hv3def]
  have kv31 : (WithLp.ofLp v3) 1 = -Pp / (2 * y1 * u1) := by simp [hv3def]
  have kv32 : (WithLp.ofLp v3) 2 = d1 / u1 := by simp [hv3def]
  have kv00 : (WithLp.ofLp (0:V3)) 0 = 0 := by simp
  have kv01 : (WithLp.ofLp (0:V3)) 1 = 0 := by simp
  have kv02 : (WithLp.ofLp (0:V3)) 2 = 0 := by simp
  -- 六条距离方程
  have e1 : dist (0:V3) v1 ^ 2 = x1 := by
    rw [ea2_dist_sq_components, kv00, kv01, kv02, kv10, kv11, kv12]
    simp only [zero_sub, sub_zero]
    ring_nf
    first
      | exact hy1sq
      | (rw [pow_two]; exact hy1sq)
  have e2 : dist (0:V3) v2 ^ 2 = x2 := by
    rw [ea2_dist_sq_components, kv00, kv01, kv02, kv20, kv21, kv22]
    simp only [zero_sub, sub_zero]
    field_simp [hy1.ne']
    simp only [pow_two, hu1sq, upsX, hy1sq]
    ring
  have e3 : dist (0:V3) v3 ^ 2 = x3 := by
    rw [ea2_dist_sq_components, kv00, kv01, kv02, kv30, kv31, kv32]
    simp only [zero_sub, sub_zero]
    field_simp [hy1.ne', hu1.ne']
    simp only [pow_two, hpdef, hu1sq, hd1sq, upsX, deltaX, hy1sq]
    ring
  have e4 : dist v2 v3 ^ 2 = x4 := by
    rw [ea2_dist_sq_components, kv20, kv21, kv22, kv30, kv31, kv32]
    simp only [zero_sub, sub_zero]
    field_simp [hy1.ne', hu1.ne']
    simp only [pow_two, hpdef, hu1sq, hd1sq, upsX, deltaX, hy1sq]
    ring
  have e5 : dist v1 v3 ^ 2 = x5 := by
    rw [ea2_dist_sq_components, kv10, kv11, kv12, kv30, kv31, kv32]
    simp only [zero_sub, sub_zero]
    field_simp [hy1.ne', hu1.ne']
    simp only [pow_two, hpdef, hu1sq, hd1sq, upsX, deltaX, hy1sq]
    ring
  have e6 : dist v1 v2 ^ 2 = x6 := by
    rw [ea2_dist_sq_components, kv10, kv11, kv12, kv20, kv21, kv22]
    simp only [zero_sub, sub_zero]
    field_simp [hy1.ne']
    simp only [pow_two, hu1sq, upsX, hy1sq]
    ring
  refine ⟨(0:V3), v1, v2, v3, e1, e2, e3, e4, e5, e6, ?_, ?_, ?_, ?_⟩
  · have hc : crossProduct ((v1 - (0:V3) : V3) : Fin 3 → ℝ)
        ((v2 - (0:V3) : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      have hz' := congrFun hz 2
      simp only [Pi.zero_apply, cross_apply, sub_zero,
        show ((v1 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v1 : Fin 3 → ℝ) from by rw [sub_zero],
        show ((v2 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v2 : Fin 3 → ℝ) from by rw [sub_zero],
        kv10, kv11, kv12, kv20, kv21, kv22, zero_mul, mul_zero, zero_sub,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.cons_val'] at hz'
      rw [mul_eq_zero] at hz'
      rcases hz' with hz' | hz'
      · exact hy1.ne' hz'
      · rw [div_eq_zero_iff] at hz'
        rcases hz' with hz' | hz'
        · exact hu1.ne' hz'
        · exact hy1.ne' (by
            rcases mul_eq_zero.mp hz' with hc | hc
            · exact absurd hc two_ne_zero
            · exact hc)
    exact fun hcol => hc ((ea2_collinear3_iff_cross (0:V3) v1 v2).mp hcol)
  · have hc : crossProduct ((v1 - (0:V3) : V3) : Fin 3 → ℝ)
        ((v3 - (0:V3) : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      have hz' := congrFun hz 1
      simp only [Pi.zero_apply, cross_apply, sub_zero,
        show ((v1 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v1 : Fin 3 → ℝ) from by rw [sub_zero],
        show ((v3 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v3 : Fin 3 → ℝ) from by rw [sub_zero],
        kv10, kv11, kv12, kv30, kv31, kv32, zero_mul, mul_zero, zero_sub,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.cons_val'] at hz'
      rw [neg_eq_zero, mul_eq_zero] at hz'
      rcases hz' with hz' | hz'
      · exact hy1.ne' hz'
      · rw [div_eq_zero_iff] at hz'
        rcases hz' with hz' | hz'
        · exact hd1.ne' hz'
        · exact hu1.ne' hz'
    exact fun hcol => hc ((ea2_collinear3_iff_cross (0:V3) v1 v3).mp hcol)
  · have hc : crossProduct ((v3 - (0:V3) : V3) : Fin 3 → ℝ)
        ((v2 - (0:V3) : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      have hz' := congrFun hz 0
      simp only [Pi.zero_apply, cross_apply, sub_zero,
        show ((v3 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v3 : Fin 3 → ℝ) from by rw [sub_zero],
        show ((v2 - (0:V3) : V3) : Fin 3 → ℝ)
          = (WithLp.ofLp v2 : Fin 3 → ℝ) from by rw [sub_zero],
        kv30, kv31, kv32, kv20, kv21, kv22, zero_mul, mul_zero, zero_sub,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.cons_val'] at hz'
      rw [neg_eq_zero, mul_eq_zero] at hz'
      rcases hz' with hz' | hz'
      · rw [div_eq_zero_iff] at hz'
        rcases hz' with hz' | hz'
        · exact hd1.ne' hz'
        · exact hu1.ne' hz'
      · rw [div_eq_zero_iff] at hz'
        rcases hz' with hz' | hz'
        · exact hu1.ne' hz'
        · exact hy1.ne' (by
            rcases mul_eq_zero.mp hz' with hc | hc
            · exact absurd hc two_ne_zero
            · exact hc)
    exact fun hcol => hc ((ea2_collinear3_iff_cross (0:V3) v3 v2).mp hcol)
  · have h2 := ea2_delta_eq_four_det_sq (0:V3) v1 v2 v3
    intro hz
    rw [hz] at h2
    rw [e1, e2, e3, e4, e5, e6] at h2
    norm_num at h2
    exact hd.ne' h2

/-- 六棱长形式：六条棱长 `y1..y6` 全正、`0 < upsX (y1²)(y2²)(y6²)`、
`0 < Δ(y1²..y6²)` 时存在四点使 `dist` 逐一对应（+ 三非共线 + 三重积非零）。 -/
theorem ea2_simplex_exists_y (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4) (hy5 : 0 < y5)
    (hy6 : 0 < y6) (hu : 0 < upsX (y1 * y1) (y2 * y2) (y6 * y6))
    (hd : 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) :
    ∃ v0 v1 v2 v3 : V3,
      dist v0 v1 = y1 ∧ dist v0 v2 = y2 ∧ dist v0 v3 = y3 ∧
      dist v2 v3 = y4 ∧ dist v1 v3 = y5 ∧ dist v1 v2 = y6 ∧
      ¬ Collinear3 v0 v1 v2 ∧ ¬ Collinear3 v0 v1 v3 ∧ ¬ Collinear3 v0 v3 v2 ∧
      crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ) ((v2 - v0 : V3) : Fin 3 → ℝ)
          ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ) ≠ 0 := by
  obtain ⟨v0, v1, v2, v3, h1, h2, h3, h4, h5, h6, hn1, hn2, hn3, hchi⟩ :=
    ea2_simplex_exists (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
      (mul_pos hy1 hy1) hu hd
  refine ⟨v0, v1, v2, v3, ?_, ?_, ?_, ?_, ?_, ?_, hn1, hn2, hn3, hchi⟩
  · have hnn : 0 ≤ dist v0 v1 := dist_nonneg
    rw [← pow_two] at h1
    rwa [sq_eq_sq₀ hnn hy1.le] at h1
  · have hnn : 0 ≤ dist v0 v2 := dist_nonneg
    rw [← pow_two] at h2
    rwa [sq_eq_sq₀ hnn hy2.le] at h2
  · have hnn : 0 ≤ dist v0 v3 := dist_nonneg
    rw [← pow_two] at h3
    rwa [sq_eq_sq₀ hnn hy3.le] at h3
  · have hnn : 0 ≤ dist v2 v3 := dist_nonneg
    rw [← pow_two] at h4
    rwa [sq_eq_sq₀ hnn hy4.le] at h4
  · have hnn : 0 ≤ dist v1 v3 := dist_nonneg
    rw [← pow_two] at h5
    rwa [sq_eq_sq₀ hnn hy5.le] at h5
  · have hnn : 0 ≤ dist v1 v2 := dist_nonneg
    rw [← pow_two] at h6
    rwa [sq_eq_sq₀ hnn hy6.le] at h6


/-! ## 私有：dihV 桥的算术核（arccos ↔ atn2） -/

/-- 纯算术核：给定 `ups1 = upsX x01 x02 x12`、`ups2 = upsX x01 x03 x13`、
`d4 = deltaX4 …`、`dl = deltaX …` 全为抽象标量，且 `4·x01·dl = ups1·ups2 − d4²`
（HOL `DELTA_X_AND_DELTA_X4`），则
`arccos (d4/√(ups1·ups2)) = π/2 + atn2(√(4·x01·dl), −d4)`。 -/
private theorem ea2_dihv_arith_core (x01 dl ups1 ups2 d4 : ℝ)
    (hx01 : 0 ≤ x01) (hdl : 0 ≤ dl) (hu1 : 0 < ups1) (hu2 : 0 < ups2)
    (hkey : 4 * x01 * dl = ups1 * ups2 - d4 ^ 2) :
    Real.arccos (d4 / Real.sqrt (ups1 * ups2))
      = Real.pi / 2 + atn2 (Real.sqrt (4 * x01 * dl)) (-d4) := by
  have hdle : 0 ≤ 4 * x01 * dl := by nlinarith
  have hspp : 0 < ups1 * ups2 := mul_pos hu1 hu2
  have hsqd4 : d4 ^ 2 ≤ ups1 * ups2 := by
    have h2 : 0 ≤ ups1 * ups2 - d4 ^ 2 := by rw [← hkey]; exact hdle
    linarith
  have hdenpos : 0 < Real.sqrt (ups1 * ups2) := Real.sqrt_pos.mpr hspp
  have h3 : |d4| ≤ Real.sqrt (ups1 * ups2) := by
    have h2 : |d4| ^ 2 ≤ (Real.sqrt (ups1 * ups2)) ^ 2 := by
      have e1 : d4 ^ 2 = ups1 * ups2 - 4 * x01 * dl := by rw [hkey]; ring
      have e2 : Real.sqrt (ups1 * ups2) ^ 2 = ups1 * ups2 :=
        Real.sq_sqrt (le_of_lt hspp)
      nlinarith [e1, e2, hdle, sq_abs d4]
    rw [← sq_le_sq₀ (abs_nonneg d4) (Real.sqrt_nonneg (ups1 * ups2))]
    exact h2
  have hq1 : -1 ≤ d4 / Real.sqrt (ups1 * ups2) ∧
      d4 / Real.sqrt (ups1 * ups2) ≤ 1 := by
    have habs : |d4 / Real.sqrt (ups1 * ups2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hdenpos, div_le_one hdenpos]
      exact h3
    exact abs_le.mp habs
  rw [ea2_arccos_eq_pi2_sub_atn2 hq1.1 hq1.2]
  have hRs : Real.sqrt (ups1 * ups2) * Real.sqrt (ups1 * ups2) = ups1 * ups2 :=
    Real.mul_self_sqrt (le_of_lt hspp)
  have h1q : 1 - (d4 / Real.sqrt (ups1 * ups2)) * (d4 / Real.sqrt (ups1 * ups2))
      = 4 * x01 * dl / (ups1 * ups2) := by
    calc 1 - (d4 / Real.sqrt (ups1 * ups2)) * (d4 / Real.sqrt (ups1 * ups2))
        = 1 - d4 * d4 / (ups1 * ups2) := by
          have hstep : (d4 / Real.sqrt (ups1 * ups2))
                * (d4 / Real.sqrt (ups1 * ups2))
              = d4 * d4 / (Real.sqrt (ups1 * ups2) * Real.sqrt (ups1 * ups2)) :=
            (mul_div_mul_comm d4 d4 (Real.sqrt (ups1 * ups2))
              (Real.sqrt (ups1 * ups2))).symm
          rw [hstep, hRs]
      _ = (ups1 * ups2 - d4 * d4) / (ups1 * ups2) := by
          field_simp
      _ = 4 * x01 * dl / (ups1 * ups2) := by
          rw [← pow_two, ← hkey]
  have hsq1 : Real.sqrt (1 - (d4 / Real.sqrt (ups1 * ups2)) * (d4 / Real.sqrt (ups1 * ups2)))
      = Real.sqrt (4 * x01 * dl) / Real.sqrt (ups1 * ups2) := by
    rw [h1q, Real.sqrt_div hdle (ups1 * ups2)]
  have hatt : atn2 (Real.sqrt (4 * x01 * dl) / Real.sqrt (ups1 * ups2))
        (d4 / Real.sqrt (ups1 * ups2))
      = atn2 (Real.sqrt (4 * x01 * dl)) d4 := by
    have hinv : 0 < 1 / Real.sqrt (ups1 * ups2) := by positivity
    have h := ea2_atn2_pos_div (x := Real.sqrt (4 * x01 * dl)) (y := d4)
      (c := Real.sqrt (ups1 * ups2)) hdenpos
    exact h
  rw [hsq1, hatt]
  by_cases hd4 : d4 = 0
  · have hx' : 0 < Real.sqrt (4 * x01 * dl) := by
      refine Real.sqrt_pos.mpr ?_
      rw [hkey, hd4]
      linarith
    rw [hd4]
    simp only [neg_zero]
    rw [ea2_atn2_zero hx']
    ring
  · rw [ea2_atn2_rneg (Or.inl hd4)]
    ring

/-! ## 主干四件：dihV 桥（dih_y / dih_x / 重标不变 / √Δ 重标） -/

-- 投影向量点积的代数展开（抽象标量版，避免 ofLp 包裹失配）。
private theorem ea2_dot_subsmul {va vb vc : Fin 3 → ℝ} (X Y Z : ℝ) :
    (X • va - Y • vc) ⬝ᵥ (X • vb - Z • vc)
      = X * X * (va ⬝ᵥ vb) - X * Z * (va ⬝ᵥ vc) - X * Y * (vb ⬝ᵥ vc)
        + Y * Z * (vc ⬝ᵥ vc) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dotProduct_comm vc vb]
  ring

/-- 投影向量点积的代数展开（V3 形）。 -/
private theorem ea2_dot_subsmul_V3 {va vb vc : V3} (X Y Z : ℝ) :
    ((X • va - Y • vc : V3) ⬝ᵥ (X • vb - Z • vc : V3))
      = X * X * (va ⬝ᵥ vb) - X * Z * (va ⬝ᵥ vc) - X * Y * (vb ⬝ᵥ vc)
        + Y * Z * (vc ⬝ᵥ vc) := by
  have h : ((X • va - Y • vc : V3) ⬝ᵥ (X • vb - Z • vc : V3) : ℝ)
      = ((X • va : Fin 3 → ℝ) - (Y • vc : Fin 3 → ℝ)) ⬝ᵥ
        ((X • vb : Fin 3 → ℝ) - (Z • vc : Fin 3 → ℝ)) := rfl
  rw [h, ea2_dot_subsmul]

theorem ea2_dihV_dih_x (v0 v1 v2 v3 : V3)
    (hu1 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v1 v2 ^ 2))
    (hu2 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v3 ^ 2) (dist v1 v3 ^ 2)) :
    dihV v0 v1 v2 v3 = dihXf (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
  set x01 : ℝ := dist v0 v1 ^ 2 with hx01
  set x02 : ℝ := dist v0 v2 ^ 2 with hx02
  set x03 : ℝ := dist v0 v3 ^ 2 with hx03
  set x12 : ℝ := dist v1 v2 ^ 2 with hx12
  set x13 : ℝ := dist v1 v3 ^ 2 with hx13
  set x23 : ℝ := dist v2 v3 ^ 2 with hx23
  set b1 : V3 := (v2 - v0 : V3) with hb1def
  set b2 : V3 := (v3 - v0 : V3) with hb2def
  set b3 : V3 := (v1 - v0 : V3) with hb3def
  set AC : ℝ := b1 ⬝ᵥ b3 with hACdef
  set BC : ℝ := b2 ⬝ᵥ b3 with hBCdef
  set AB : ℝ := b1 ⬝ᵥ b2 with hABdef
  -- 距离 → 原子方程
  have e01 : x01 = b3 ⬝ᵥ b3 := by rw [hx01, ea2_dist_sq, ← hb3def]
  have e02 : x02 = b1 ⬝ᵥ b1 := by rw [hx02, ea2_dist_sq, ← hb1def]
  have e03 : x03 = b2 ⬝ᵥ b2 := by rw [hx03, ea2_dist_sq, ← hb2def]
  have h12c : (v2 - v1 : V3) = b1 - b3 := by
    have h := congrArg (fun z : V3 => z)
      (show (v2 : V3) - v1 = (v2 - v0) - (v1 - v0) from by abel)
    rw [← hb1def, ← hb3def] at h
    exact h
  have h13c : (v3 - v1 : V3) = b2 - b3 := by
    have h := congrArg (fun z : V3 => z)
      (show (v3 : V3) - v1 = (v3 - v0) - (v1 - v0) from by abel)
    rw [← hb2def, ← hb3def] at h
    exact h
  have h23c : (v2 - v3 : V3) = b1 - b2 := by
    have h := congrArg (fun z : V3 => z)
      (show (v2 : V3) - v3 = (v2 - v0) - (v3 - v0) from by abel)
    rw [← hb1def, ← hb2def] at h
    exact h
  have e12 : x12 = (b1 - b3) ⬝ᵥ (b1 - b3) := by
    rw [hx12, ea2_dist_sq, h12c]; rfl
  have e13 : x13 = (b2 - b3) ⬝ᵥ (b2 - b3) := by
    rw [hx13, ea2_dist_sq, h13c]; rfl
  have e23 : x23 = (b1 - b2) ⬝ᵥ (b1 - b2) := by
    rw [hx23, ea2_dist_sq', h23c]; rfl
  -- 标量原子方程
  have hu1eq : upsX x01 x02 x12
      = 4 * (b3 ⬝ᵥ b3 * (b1 ⬝ᵥ b1) - (b1 ⬝ᵥ b3) * (b1 ⬝ᵥ b3)) := by
    rw [e01, e02, e12]
    simp only [WithLp.ofLp_sub, ea2_dmix b1 b3,
      ea2_ups_atoms (b1 ⬝ᵥ b1) 0 (b3 ⬝ᵥ b3) (b1 ⬝ᵥ b3)]
  have hu2eq : upsX x01 x03 x13
      = 4 * (b3 ⬝ᵥ b3 * (b2 ⬝ᵥ b2) - (b2 ⬝ᵥ b3) * (b2 ⬝ᵥ b3)) := by
    rw [e01, e03, e13]
    simp only [WithLp.ofLp_sub, ea2_dmix b2 b3,
      ea2_ups_atoms (b2 ⬝ᵥ b2) 0 (b3 ⬝ᵥ b3) (b2 ⬝ᵥ b3)]
  have hd4eq : deltaX4 x01 x02 x03 x23 x13 x12
      = 4 * (b3 ⬝ᵥ b3 * (b1 ⬝ᵥ b2) - (b1 ⬝ᵥ b3) * (b2 ⬝ᵥ b3)) := by
    rw [e01, e02, e03, e23, e13, e12]
    simp only [WithLp.ofLp_sub, ea2_dmix b1 b2, ea2_dmix b2 b3, ea2_dmix b1 b3,
      ea2_d4_atoms (b1 ⬝ᵥ b1) (b2 ⬝ᵥ b2) (b3 ⬝ᵥ b3) (b1 ⬝ᵥ b2) (b1 ⬝ᵥ b3) (b2 ⬝ᵥ b3)]
  have hdleq : deltaX x01 x02 x03 x23 x13 x12
      = 4 * (b1 ⬝ᵥ b1 * b2 ⬝ᵥ b2 * b3 ⬝ᵥ b3 + 2 * ((b1 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) * (b2 ⬝ᵥ b3))
        - (b1 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) ^ 2 - (b2 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) ^ 2
        - (b3 ⬝ᵥ b3) * (b1 ⬝ᵥ b2) ^ 2) := by
    simp only [e01, e02, e03, e23, e13, e12, WithLp.ofLp_sub, ea2_dmix b1 b2,
      ea2_dmix b2 b3, ea2_dmix b1 b3,
      ea2_delta_atoms (b1 ⬝ᵥ b1) (b2 ⬝ᵥ b2) (b3 ⬝ᵥ b3) (b1 ⬝ᵥ b2) (b1 ⬝ᵥ b3) (b2 ⬝ᵥ b3)]
    ring
  have hkeyeq : 4 * x01 * deltaX x01 x02 x03 x23 x13 x12
      = upsX x01 x02 x12 * upsX x01 x03 x13
        - deltaX4 x01 x02 x03 x23 x13 x12 ^ 2 := by
    simp only [e01, e02, e03, e23, e13, e12, WithLp.ofLp_sub, ea2_dmix b1 b2,
      ea2_dmix b2 b3, ea2_dmix b1 b3,
      ea2_hkey_atoms (b1 ⬝ᵥ b1) (b2 ⬝ᵥ b2) (b3 ⬝ᵥ b3) (b1 ⬝ᵥ b2) (b1 ⬝ᵥ b3) (b2 ⬝ᵥ b3)]
  -- 正性
  have hsqAC : 0 ≤ AC * AC := by
    rw [← pow_two]; exact sq_nonneg AC
  have hx02ge : 0 ≤ x02 := sq_nonneg _
  have hx03ge : 0 ≤ x03 := sq_nonneg _
  have hx01ge : 0 ≤ x01 := sq_nonneg _
  have hu1o : 0 < upsX x01 x02 x12 := hu1
  have hu2o : 0 < upsX x01 x03 x13 := hu2
  rw [hu1eq] at hu1
  rw [hu2eq] at hu2
  have hupsprod : 0 < upsX x01 x02 x12 * upsX x01 x03 x13 := mul_pos hu1o hu2o
  have hK1 : 0 < b3 ⬝ᵥ b3 * (b1 ⬝ᵥ b1) - AC * AC := by linarith
  have hK2 : 0 < b3 ⬝ᵥ b3 * (b2 ⬝ᵥ b2) - BC * BC := by linarith
  have hxp01 : 0 < x01 := by
    rcases eq_or_lt_of_le hx01ge with h | h
    · exfalso
      have hC0 : (b3 ⬝ᵥ b3) = 0 := by rw [← e01, h]
      rw [hC0] at hK1
      simp only [zero_mul, sub_zero] at hK1
      linarith [hK1, hsqAC]
    · exact h
  -- dihV 展开（LuneVolume 定义）
  have hdihv : dihV v0 v1 v2 v3
      = Real.arccos ((x01 • b1 - AC • b3) ⬝ᵥ (x01 • b2 - BC • b3)
          / (dist (x01 • b1 - AC • b3) 0 * dist (x01 • b2 - BC • b3) 0)) := by
    unfold dihV arcV
    dsimp only
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_zero, ← hb1def,
      ← hb2def, ← hb3def, ← hACdef, ← hBCdef, ← e01, ← e02, ← e03, sub_zero]
  -- K1/K2 的原子形（x01·x02 − AC² 正）
  have hK1' : 0 < x01 * x02 - AC * AC := by
    have hk := hK1
    rw [← e01, ← e02] at hk
    exact hk
  have hK2' : 0 < x01 * x03 - BC * BC := by
    have hk := hK2
    rw [← e01, ← e03] at hk
    exact hk
  -- 投影向量的原子方程（V3 显式 ascription 保证 ofLp 包裹确定）
  have hvapsq : ((x01 • b1 - AC • b3 : V3) ⬝ᵥ (x01 • b1 - AC • b3 : V3))
      = x01 * (x01 * x02 - AC * AC) := by
    rw [ea2_dot_subsmul_V3, ← hACdef, ← e01, ← e02]
    ring
  have hvbpdot : ((x01 • b2 - BC • b3 : V3) ⬝ᵥ (x01 • b2 - BC • b3 : V3))
      = x01 * (x01 * x03 - BC * BC) := by
    rw [ea2_dot_subsmul_V3, ← hBCdef, ← e01, ← e03]
    ring
  have hvapn : dist (x01 • b1 - AC • b3) 0
      = Real.sqrt (x01 * (x01 * x02 - AC * AC)) := by
    rw [dist_eq_norm, sub_zero,
      (Real.sqrt_sq (norm_nonneg (x01 • b1 - AC • b3))).symm, norm_sq_eq_dot, hvapsq]
  have hvbpn : dist (x01 • b2 - BC • b3) 0
      = Real.sqrt (x01 * (x01 * x03 - BC * BC)) := by
    rw [dist_eq_norm, sub_zero,
      (Real.sqrt_sq (norm_nonneg (x01 • b2 - BC • b3))).symm, norm_sq_eq_dot, hvbpdot]
  have hsqrtK : Real.sqrt ((x01 * (x01 * x02 - AC * AC)) * (x01 * (x01 * x03 - BC * BC)))
      = x01 * Real.sqrt ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) := by
    rw [show (x01 * (x01 * x02 - AC * AC)) * (x01 * (x01 * x03 - BC * BC))
        = (x01 * x01) * ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) from by ring,
      Real.sqrt_mul (mul_nonneg hx01ge hx01ge)
        ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)),
      Real.sqrt_mul_self hx01ge]
  have hden : dist (x01 • b1 - AC • b3) 0
      * dist (x01 • b2 - BC • b3) 0
      = x01 * Real.sqrt ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) := by
    rw [hvapn, hvbpn,
      ← Real.sqrt_mul (mul_nonneg hx01ge hK1'.le)
        (x01 * (x01 * x03 - BC * BC)), hsqrtK]
  have heq : upsX x01 x02 x12 * upsX x01 x03 x13
      = 16 * ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) := by
    rw [hu1eq, hu2eq, ← e01, ← e02, ← e03, ← hACdef, ← hBCdef]
    ring
  have hsqrtden : Real.sqrt (upsX x01 x02 x12 * upsX x01 x03 x13)
      = 4 * Real.sqrt ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) := by
    rw [heq, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16)
      ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)),
      show (Real.sqrt 16 : ℝ) = 4 from by norm_num]
  have hd4ab : deltaX4 x01 x02 x03 x23 x13 x12 = 4 * (x01 * AB - AC * BC) := by
    rw [hd4eq, ← hABdef, ← hACdef, ← hBCdef, ← e01]
  have hdl : 0 ≤ deltaX x01 x02 x03 x23 x13 x12 := by
    have hd := ea2_delta_eq_four_det_sq v0 v1 v2 v3
    rw [← hx01, ← hx02, ← hx03, ← hx23, ← hx13, ← hx12] at hd
    rw [hd]
    positivity
  have hK'pos : 0 < Real.sqrt ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)) :=
    Real.sqrt_pos.mpr (mul_pos hK1' hK2')
  -- 最终组装：arccos 的辐角化为 d4 / √(ups·ups)，再用 arith core
  have hq : (x01 * x01 * AB - x01 * BC * AC - x01 * AC * BC + AC * BC * x01)
      / (x01 * Real.sqrt ((x01 * x02 - AC * AC) * (x01 * x03 - BC * BC)))
      = deltaX4 x01 x02 x03 x23 x13 x12
        / Real.sqrt (upsX x01 x02 x12 * upsX x01 x03 x13) := by
    rw [hd4ab, hsqrtden]
    field_simp [hxp01.ne', hK'pos.ne']
    ring
  rw [hdihv]
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, ea2_dot_subsmul,
    ← hABdef, ← hACdef, ← hBCdef, ← e01]
  rw [hden, hq]
  exact ea2_dihv_arith_core x01 (deltaX x01 x02 x03 x23 x13 x12)
    (upsX x01 x02 x12) (upsX x01 x03 x13) (deltaX4 x01 x02 x03 x23 x13 x12)
    hx01ge hdl hu1o hu2o hkeyeq

/-- Pi 侧的左 smul 点积。 -/
private theorem ea2_smul_dot_pi (t : ℝ) (x y : Fin 3 → ℝ) :
    (t • x) ⬝ᵥ y = t * (x ⬝ᵥ y) := smul_dotProduct t x y

/-- `vap` 的双缩放恒等式（DIHV_RESCALE_UNCHANGED 的代数核）。 -/
private theorem ea2_vap_scale (A B : V3) (r1 r2 : ℝ) :
    ((r1 • A : V3) ⬝ᵥ (r1 • A : V3)) • (r2 • B : V3)
      - ((r2 • B : V3) ⬝ᵥ (r1 • A : V3)) • (r1 • A : V3)
      = (r1 * r1 * r2) • ((A ⬝ᵥ A) • B - (B ⬝ᵥ A) • A) := by
  set dAA : ℝ := (WithLp.ofLp A) ⬝ᵥ (WithLp.ofLp A) with hdAA
  set dBA : ℝ := (WithLp.ofLp B) ⬝ᵥ (WithLp.ofLp A) with hdBA
  simp only [WithLp.ofLp_smul]
  rw [ea2_smul_dot_pi, ea2_dot_smul_pi, ea2_smul_dot_pi, ea2_dot_smul_pi, ← hdAA, ← hdBA,
    smul_smul, smul_smul, smul_sub, smul_smul, smul_smul,
    show (r1 * (r1 * dAA) * r2 : ℝ) = r1 * r1 * r2 * dAA from by ring,
    show (r2 * (r1 * dBA) * r1 : ℝ) = r1 * r1 * r2 * dBA from by ring]

/-- `arcV` 的正系数缩放不变性（DIHV_RESCALE_UNCHANGED 的核）。 -/
private theorem ea2_arcV_smul_smul (u v : V3) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Kepler.Geom.arcV 0 (s • u) (t • v) = Kepler.Geom.arcV 0 u v := by
  rw [Kepler.Geom.arcV, Kepler.Geom.arcV]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_zero, sub_zero]
  have hdn1 : dist (s • u) (0:V3) = s * ‖u‖ := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hdn2 : dist (t • v) (0:V3) = t * ‖v‖ := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hd1 : dist u (0:V3) = ‖u‖ := by rw [dist_eq_norm, sub_zero]
  have hd2 : dist v (0:V3) = ‖v‖ := by rw [dist_eq_norm, sub_zero]
  have hst : s * t ≠ 0 := ne_of_gt (mul_pos hs ht)
  have hdot : (s • (WithLp.ofLp u)) ⬝ᵥ (t • (WithLp.ofLp v))
      = s * t * ((WithLp.ofLp u) ⬝ᵥ (WithLp.ofLp v)) := by
    rw [dotProduct_smul, smul_dotProduct]
    ring
  rw [hdot, hdn1, hdn2, hd1, hd2,
    show (s * ‖u‖ * (t * ‖v‖)) = (s * t) * (‖u‖ * ‖v‖) from by ring]
  congr 1
  field_simp [hst]

/-- **DIHV_EQ_DIH_Y**（merge_ineq.hl:782-800）：两组非共线时
`dihV = dihY`（六距离形式的解析二面角）。 -/
theorem ea2_dihV_eq_dih_y (v0 v1 v2 v3 : V3)
    (h1 : ¬ Collinear3 v0 v1 v2) (h2 : ¬ Collinear3 v0 v1 v3) :
    dihV v0 v1 v2 v3 = dihY (dist v0 v1) (dist v0 v2) (dist v0 v3)
        (dist v2 v3) (dist v1 v3) (dist v1 v2) := by
  have hu1p : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v1 v2 ^ 2) :=
    (ea2_upsX_pos_iff v0 v1 v2).mpr h1
  have hu2p : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v3 ^ 2) (dist v1 v3 ^ 2) :=
    (ea2_upsX_pos_iff v0 v1 v3).mpr h2
  have hdy : dihY (dist v0 v1) (dist v0 v2) (dist v0 v3)
      (dist v2 v3) (dist v1 v3) (dist v1 v2)
      = dihXf (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [dihY]
    simp only [pow_two]
  rw [hdy]
  exact ea2_dihV_dih_x v0 v1 v2 v3 hu1p hu2p

/-- **DIHV_RESCALE_UNCHANGED**（euler_complement.hl:92-113）：三条棱
沿正系数缩放时 `dihV` 不变。 -/
theorem ea2_dihv_rescale_unchanged (v0 v1 v2 v3 w0 w1 w2 w3 : V3) (m n p : ℝ)
    (hm1 : v1 - v0 = m • (w1 - w0)) (hm2 : v2 - v0 = n • (w2 - w0))
    (hm3 : v3 - v0 = p • (w3 - w0)) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) :
    dihV v0 v1 v2 v3 = dihV w0 w1 w2 w3 := by
  unfold dihV
  dsimp only
  rw [hm1, hm2, hm3,
    ea2_vap_scale (w1 - w0 : V3) (w2 - w0 : V3) m n,
    ea2_vap_scale (w1 - w0 : V3) (w3 - w0 : V3) m p,
    ea2_arcV_smul_smul _ _ (mul_pos (mul_pos hm hm) hn)
    (mul_pos (mul_pos hm hm) hp)]

/-- **√Δ 重标**（euler_complement.hl:230-330，COMPUTE_DELTA_X_AFTER_RESCALE +
sqrt_delta_x_after_rescale）：三条棱自 v0 起沿非负系数缩放时
`√Δ` 乘 `m·n·p`。 -/
theorem ea2_sqrt_delta_rescale (v0 v1 v2 v3 v0' v1' v2' v3' : V3) (m n p : ℝ)
    (hm1 : v1 - v0 = m • (v1' - v0')) (hm2 : v2 - v0 = n • (v2' - v0'))
    (hm3 : v3 - v0 = p • (v3' - v0')) (hm : 0 ≤ m) (hn : 0 ≤ n) (hp : 0 ≤ p) :
    Real.sqrt (deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2))
      = (m * n * p) * Real.sqrt (deltaX (dist v0' v1' ^ 2) (dist v0' v2' ^ 2)
        (dist v0' v3' ^ 2) (dist v2' v3' ^ 2) (dist v1' v3' ^ 2)
        (dist v1' v2' ^ 2)) := by
  have hchi : crossProduct ((v1 - v0 : V3) : Fin 3 → ℝ) ((v2 - v0 : V3) : Fin 3 → ℝ)
      ⬝ᵥ ((v3 - v0 : V3) : Fin 3 → ℝ)
      = (m * n * p) * (crossProduct ((v1' - v0' : V3) : Fin 3 → ℝ)
        ((v2' - v0' : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3' - v0' : V3) : Fin 3 → ℝ)) := by
    rw [hm1, hm2, hm3, WithLp.ofLp_smul, WithLp.ofLp_smul, WithLp.ofLp_smul,
      ea2_smul_cross_left, ea2_cross_smul_right, smul_dotProduct, dotProduct_smul,
      smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have h1 := ea2_delta_eq_four_det_sq v0 v1 v2 v3
  have h2 := ea2_delta_eq_four_det_sq v0' v1' v2' v3'
  rw [hchi] at h1
  have hmnp : 0 ≤ m * n * p := by positivity
  have hsqrt1 : Real.sqrt (4 * ((m * n * p) *
      (crossProduct ((v1' - v0' : V3) : Fin 3 → ℝ) ((v2' - v0' : V3) : Fin 3 → ℝ)
        ⬝ᵥ ((v3' - v0' : V3) : Fin 3 → ℝ))) ^ 2)
      = (m * n * p) * Real.sqrt (4 * (crossProduct ((v1' - v0' : V3) : Fin 3 → ℝ)
        ((v2' - v0' : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3' - v0' : V3) : Fin 3 → ℝ)) ^ 2) := by
    have h4 : (Real.sqrt 4 : ℝ) = 2 := by norm_num
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)
        (((m * n * p) * (crossProduct ((v1' - v0' : V3) : Fin 3 → ℝ)
          ((v2' - v0' : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3' - v0' : V3) : Fin 3 → ℝ))) ^ 2),
      h4, Real.sqrt_sq_eq_abs,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)
        ((crossProduct ((v1' - v0' : V3) : Fin 3 → ℝ)
          ((v2' - v0' : V3) : Fin 3 → ℝ) ⬝ᵥ ((v3' - v0' : V3) : Fin 3 → ℝ)) ^ 2),
      h4, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hmnp]
    ring
  rw [h1, hsqrt1, h2]

end Kepler.Text
