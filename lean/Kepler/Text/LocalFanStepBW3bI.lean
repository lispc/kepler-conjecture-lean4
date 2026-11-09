/-
Kepler/Text/LocalFanStepBW3bI.lean — wave C-W3b-i：W3b 的三个缺口件。

背景：W3b（`azim < π` 支，HOL NKEZBFC.hl:973-1234）的依赖面板里
`JBDNJJB3_p9`（LA9:560）与 `aff_ge_3_1_rep_cross_dot_p9`（LA9:2773）是 `sorry` 桩
（`#print axioms` 实测含 `sorryAx`，见 W3B_PREFLIGHT.md）。本件按 AGENTS §2
「不许消费 sorry」本地重证所需内容，**不改任何既有桩体**：

* §1 `pW3b_jbdnjjb_pos`：JBDNJJB 的严格符号版
  `∃ c > 0, (u × v)·w = c * sin(azim 0 u v w)`（两非共线 + u ≠ 0）；
  推论 `pW3b_crossdot_pos_of_azim_lt_pi`：`0 < azim < π ⇒ 0 < (u×v)·w`。
  路线：公开 `azim_master`（Azim.lean:1000）的标架 spec（自带 `¬Collinear → 0 < r`）
  + `crossProduct` 的 Pi 侧线性桥。
* §2 `pW3b_affGe_3_1_rep`：`affGe {x,v,u}{w}` 的叉积点积半空间表示
  （LA9:2773 桩的本地重证；`AFF_GE_3_1_p9` + 平面分解）。
* §3 `pW3b_not_coplanar_of_azim_between`：扇面实例
  （`azim 0 x.1 x.2 d ∈ (0,π) ⇒ ¬ Coplanar {0,x.1,x.2,d}`，Geom `Coplanar`；
  消费公开 `properties_fully_surrounded`（Planarity:2372，标准三））。

W3b-ii 接线见 DELIVERY.md。
-/
import Kepler.Text.LocalFanStepBW3a

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §0 本地私有桥（V3 → Pi 的 coe / crossProduct 线性；不消费 LA9:560 桩） -/

private theorem pW3b_coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem pW3b_coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem pW3b_coe_add (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem pW3b_coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl

private theorem pW3b_cross_add (p q r : Fin 3 → ℝ) :
    crossProduct (p + q) r = crossProduct p r + crossProduct q r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.add_apply]

private theorem pW3b_cross_smul (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem pW3b_cross_add' (p q r : Fin 3 → ℝ) :
    crossProduct p (q + r) = crossProduct p q + crossProduct p r := by
  rw [← cross_anticomm (q + r) p, ← cross_anticomm q p, ← cross_anticomm r p,
    pW3b_cross_add, neg_add]

private theorem pW3b_cross_smul' (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct p (t • r) = t • crossProduct p r := by
  rw [← cross_anticomm (t • r) p, pW3b_cross_smul, ← cross_anticomm p r, smul_neg,
    neg_neg]

private theorem pW3b_dot_add3 (a : Fin 3 → ℝ) (t1 t2 t3 : ℝ) (p q r : Fin 3 → ℝ) :
    a ⬝ᵥ (t1 • p + t2 • q + t3 • r)
      = t1 * (a ⬝ᵥ p) + t2 * (a ⬝ᵥ q) + t3 * (a ⬝ᵥ r) := by
  rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]

private theorem pW3b_cross_add2' (p s t u : Fin 3 → ℝ) :
    crossProduct p (s + t + u)
      = crossProduct p s + crossProduct p t + crossProduct p u := by
  rw [pW3b_cross_add' p (s + t) u, pW3b_cross_add' p s t]

private theorem pW3b_cross_e3_e1 {f1 f2 f3 : V3} (h : Orthonormal3 f1 f2 f3) :
    crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ) = (f2 : Fin 3 → ℝ) := by
  have hXf1 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f1 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hXf2 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f2 : Fin 3 → ℝ) = 1 := by
    rw [dotProduct_comm, triple_product_permutation, on3_cross h]
    exact h.2.2.1
  have hXf3 : (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) ⬝ᵥ (f3 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hexp := on3_expand h (WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) : V3)
  rw [hXf1, hXf2, hXf3] at hexp
  simp only [zero_smul, one_smul, zero_add, add_zero] at hexp
  have hcoe : ((WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f1 : Fin 3 → ℝ)) : V3) :
      Fin 3 → ℝ) = (f2 : Fin 3 → ℝ) := by rw [hexp]
  rw [coe_toLp] at hcoe
  exact hcoe

private theorem pW3b_cross_e3_e2 {f1 f2 f3 : V3} (h : Orthonormal3 f1 f2 f3) :
    crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ) = -(f1 : Fin 3 → ℝ) := by
  have hXf1 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f1 : Fin 3 → ℝ) = -1 := by
    rw [dotProduct_comm, triple_product_permutation,
      ← cross_anticomm (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ), dotProduct_comm, neg_dotProduct,
      on3_cross h]
    rw [h.2.2.1]
  have hXf2 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f2 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hXf3 : (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) ⬝ᵥ (f3 : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hexp := on3_expand h (WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) : V3)
  rw [hXf1, hXf2, hXf3] at hexp
  simp only [zero_smul, neg_smul, one_smul, add_zero] at hexp
  have hcoe : ((WithLp.toLp 2 (crossProduct (f3 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)) : V3) :
      Fin 3 → ℝ) = -(f1 : Fin 3 → ℝ) := by
    rw [hexp]; rfl
  rw [coe_toLp] at hcoe
  exact hcoe

/-! ## §1 JBDNJJB 严格符号版 -/

/-- **JBDNJJB 严格符号版**：`u ≠ 0`、`v`/`w` 均不与轴 `0-u` 共线时，
`∃ c > 0, (u × v)·w = c * sin(azim 0 u v w)`。
（本地重证；不消费 LA9:560 桩。） -/
theorem pW3b_jbdnjjb_pos (u v w : V3) (hu : u ≠ 0)
    (hncuv : ¬ Collinear3 (0 : V3) u v) (hncuw : ¬ Collinear3 (0 : V3) u w) :
    ∃ c : ℝ, 0 < c ∧
      (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)
        = c * Real.sin (azim 0 u v w) := by
  obtain ⟨g1, g2, g3, hf, halign⟩ := exists_on3_eq_smul u hu
  have huc : (u : Fin 3 → ℝ) = ‖u‖ • (g3 : Fin 3 → ℝ) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) halign
    simpa using h
  have hax : (u - 0 : V3) = dist u 0 • g3 := by
    rw [dist_eq_norm]
    simpa using halign
  obtain ⟨-, -, hmain⟩ := azim_master 0 u v w
  obtain ⟨k1, k2, hframe⟩ := hmain
  obtain ⟨ψ, r1, r2, hv, hw, hr1, hr2⟩ := hframe g1 g2 g3 hf hax hu
  have hr1pos : 0 < r1 := hr1 hncuv
  have hr2pos : 0 < r2 := hr2 hncuw
  have o11 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g1 : Fin 3 → ℝ)) = 1 := hf.1
  have o22 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g2 : Fin 3 → ℝ)) = 1 := hf.2.1
  have o12 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g2 : Fin 3 → ℝ)) = 0 := hf.2.2.2.1
  have o13 : ((g1 : Fin 3 → ℝ)) ⬝ᵥ ((g3 : Fin 3 → ℝ)) = 0 := hf.2.2.2.2.1
  have o23 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g3 : Fin 3 → ℝ)) = 0 := hf.2.2.2.2.2.1
  have o21 : ((g2 : Fin 3 → ℝ)) ⬝ᵥ ((g1 : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm]
    exact o12
  have o1u : ((g1 : Fin 3 → ℝ)) ⬝ᵥ (u : Fin 3 → ℝ) = 0 := by
    rw [huc, dotProduct_smul, o13, smul_zero]
  have o2u : ((g2 : Fin 3 → ℝ)) ⬝ᵥ (u : Fin 3 → ℝ) = 0 := by
    rw [huc, dotProduct_smul, o23, smul_zero]
  have hv' : (v : Fin 3 → ℝ) = (r1 * Real.cos ψ) • (g1 : Fin 3 → ℝ)
      + (r1 * Real.sin ψ) • (g2 : Fin 3 → ℝ) + k1 • (u : Fin 3 → ℝ) := by
    have hcc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hv
    rw [pW3b_coe_add, pW3b_coe_smul, pW3b_coe_add, pW3b_coe_smul, pW3b_coe_smul,
      pW3b_coe_sub, pW3b_coe_zero, sub_zero, pW3b_coe_sub, pW3b_coe_zero, sub_zero] at hcc
    exact hcc
  have hw' : (w : Fin 3 → ℝ) = (r2 * Real.cos (ψ + azim 0 u v w)) • (g1 : Fin 3 → ℝ)
      + (r2 * Real.sin (ψ + azim 0 u v w)) • (g2 : Fin 3 → ℝ)
      + k2 • (u : Fin 3 → ℝ) := by
    have hcc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hw
    rw [pW3b_coe_add, pW3b_coe_smul, pW3b_coe_add, pW3b_coe_smul, pW3b_coe_smul,
      pW3b_coe_sub, pW3b_coe_zero, sub_zero, pW3b_coe_sub, pW3b_coe_zero, sub_zero] at hcc
    exact hcc
  have hd1 : (g1 : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ) = r2 * Real.cos (ψ + azim 0 u v w) := by
    rw [hw', pW3b_dot_add3, o11, o12, o1u]
    ring
  have hd2 : (g2 : Fin 3 → ℝ) ⬝ᵥ (w : Fin 3 → ℝ) = r2 * Real.sin (ψ + azim 0 u v w) := by
    rw [hw', pW3b_dot_add3, o21, o22, o2u]
    ring
  have hcross : crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      = (‖u‖ * (r1 * Real.cos ψ)) • (g2 : Fin 3 → ℝ)
        + (-(‖u‖ * (r1 * Real.sin ψ))) • (g1 : Fin 3 → ℝ) := by
    rw [hv', huc, pW3b_cross_smul, pW3b_cross_add2', pW3b_cross_smul', pW3b_cross_smul',
      pW3b_cross_smul', pW3b_cross_smul', pW3b_cross_e3_e1 hf, pW3b_cross_e3_e2 hf,
      cross_self, smul_zero, smul_zero, add_zero, smul_add, smul_smul, smul_smul, smul_neg,
      neg_smul]
  refine ⟨‖u‖ * r1 * r2,
    mul_pos (mul_pos (norm_pos_iff.mpr hu) hr1pos) hr2pos, ?_⟩
  rw [hcross, add_dotProduct, smul_dotProduct, smul_dotProduct, hd2, hd1]
  simp only [smul_eq_mul]
  have hsub : Real.sin ((ψ + azim 0 u v w) - ψ)
      = Real.sin (ψ + azim 0 u v w) * Real.cos ψ
        - Real.cos (ψ + azim 0 u v w) * Real.sin ψ := Real.sin_sub _ _
  rw [show (ψ + azim 0 u v w) - ψ = azim 0 u v w from by ring] at hsub
  rw [hsub]
  ring

/-- **W3b-ii 消费形**：`0 < azim 0 u v w < π`（两非共线）⇒ `0 < (u × v)·w`。 -/
theorem pW3b_crossdot_pos_of_azim_lt_pi (u v w : V3) (hu : u ≠ 0)
    (hncuv : ¬ Collinear3 (0 : V3) u v) (hncuw : ¬ Collinear3 (0 : V3) u w)
    (h0 : 0 < azim 0 u v w) (hpi : azim 0 u v w < Real.pi) :
    0 < (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ) := by
  obtain ⟨c, hc, hid⟩ := pW3b_jbdnjjb_pos u v w hu hncuv hncuw
  rw [hid]
  exact mul_pos hc (Real.sin_pos_of_pos_of_lt_pi h0 hpi)

/-! ## §2 `affGe {x,v,u}{w}` 的叉积点积半空间表示（LA9:2773 桩的本地重证） -/

/-- 局部分解辅助（HOL `crossProduct` 三重积的平面分解；本地私有）。 -/
private lemma pW3b_plane_decomp_aux (a b z : Fin 3 → ℝ) :
    (crossProduct a b ⬝ᵥ crossProduct a b) • z =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
      ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
  have h1 : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      (crossProduct a b ⬝ᵥ crossProduct a b) • z -
        (z ⬝ᵥ crossProduct a b) • crossProduct a b :=
    cross_cross_eq_smul_sub_smul (crossProduct a b) z (crossProduct a b)
  have h2 : crossProduct (crossProduct a b) z =
      (a ⬝ᵥ z) • b - (b ⬝ᵥ z) • a :=
    cross_cross_eq_smul_sub_smul a b z
  have hb : crossProduct b (crossProduct a b) =
      (b ⬝ᵥ b) • a - (a ⬝ᵥ b) • b :=
    cross_cross_eq_smul_sub_smul' b a b
  have ha : crossProduct a (crossProduct a b) =
      (a ⬝ᵥ b) • a - (a ⬝ᵥ a) • b :=
    cross_cross_eq_smul_sub_smul' a a b
  have h1' : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b := by
    rw [h2, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hb, ha]
    module
  calc (crossProduct a b ⬝ᵥ crossProduct a b) • z =
        crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by
        rw [h1]; abel
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by rw [h1']
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
        rw [dotProduct_comm z (crossProduct a b)]

/-- 平面分解（本地私有）。 -/
private lemma pW3b_plane_decomp {a b z : Fin 3 → ℝ}
    (hn : crossProduct a b ≠ 0) (hz : (crossProduct a b) ⬝ᵥ z = 0) :
    z = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
  have hnn : crossProduct a b ⬝ᵥ crossProduct a b ≠ 0 := by
    intro h0
    apply hn
    funext i
    have hsum : ∑ j, (crossProduct a b) j * (crossProduct a b) j = 0 := by
      simpa only [dotProduct] using h0
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg ((crossProduct a b) j))).mp hsum
    exact mul_self_eq_zero.mp (h3 i (Finset.mem_univ i))
  have hmain := pW3b_plane_decomp_aux a b z
  rw [hz, zero_smul, add_zero] at hmain
  calc z = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        ((crossProduct a b ⬝ᵥ crossProduct a b) • z) :=
        (inv_smul_smul₀ hnn z).symm
    _ = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        (((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
         ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b) := by rw [hmain]
    _ = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
        rw [smul_add, smul_smul, smul_smul]

/-- **`affGe {x,v,u}{w}` 的叉积点积表示**（LA9:2773 桩的本地重证；
`¬ Coplanar ℝ` 与 `0 < (v-x)×(u-x)·(w-x)` 下）。 -/
theorem pW3b_affGe_3_1_rep (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hpos : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ)) :
    affGe ({x, v, u} : Set V3) {w} =
      {y : V3 | 0 ≤ crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} := by
  obtain ⟨hdis, -, -, -, -, -, -, -⟩ := notcoplanar_disjoints x v u w hcop
  rw [AFF_GE_3_1_p9 x v u w hdis]
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨t1, t2, t3, t4, ht4, hsum, hy⟩
    have hz : (y - x : V3) = t2 • (v - x) + t3 • (u - x) + t4 • (w - x) := by
      have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
      rw [hy, ht1]
      module
    have hz' : ((y - x : V3) : Fin 3 → ℝ) =
        t2 • ((v - x : V3) : Fin 3 → ℝ) + t3 • ((u - x : V3) : Fin 3 → ℝ) +
          t4 • ((w - x : V3) : Fin 3 → ℝ) := by
      have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hz
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
    rw [hz']
    have ha : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_self_cross _ _
    have hb : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((u - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_cross_self _ _
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ha, hb, mul_zero,
      zero_add, add_zero]
    exact mul_nonneg ht4 hpos.le
  · intro hy
    let a : Fin 3 → ℝ := ((v - x : V3) : Fin 3 → ℝ)
    let b : Fin 3 → ℝ := ((u - x : V3) : Fin 3 → ℝ)
    let c : Fin 3 → ℝ := ((w - x : V3) : Fin 3 → ℝ)
    let z : Fin 3 → ℝ := ((y - x : V3) : Fin 3 → ℝ)
    let n : Fin 3 → ℝ := crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)
    have hd : 0 < n ⬝ᵥ c := by dsimp only [n, a, b, c]; exact hpos
    have hnz : 0 ≤ n ⬝ᵥ z := by dsimp only [n, a, b, z]; exact hy
    have hn : n ≠ 0 := by
      intro h0
      rw [h0, zero_dotProduct] at hd
      exact lt_irrefl 0 hd
    let t4 : ℝ := (n ⬝ᵥ z) / (n ⬝ᵥ c)
    have ht4 : 0 ≤ t4 := by dsimp only [t4]; exact div_nonneg hnz hd.le
    let z' : Fin 3 → ℝ := z - t4 • c
    have hz' : n ⬝ᵥ z' = 0 := by
      dsimp only [z', t4]
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      field_simp [hd.ne']
      ring
    have hn_ab : crossProduct a b ≠ 0 := by
      dsimp only [a, b]
      dsimp only [n] at hn
      exact hn
    have hz'_ab : crossProduct a b ⬝ᵥ z' = 0 := by
      dsimp only [a, b]
      dsimp only [n] at hz'
      exact hz'
    have hdecomp := pW3b_plane_decomp (a := a) (b := b) (z := z') hn_ab hz'_ab
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℝ, z' = A • a + B • b := ⟨_, _, hdecomp⟩
    refine ⟨1 - A - B - t4, A, B, t4, ht4, by ring, ?_⟩
    have hz_eq : z = A • a + B • b + t4 • c := by
      rw [← hAB]
      dsimp only [z']
      abel
    have hzV : (y - x : V3) = A • (v - x) + B • (u - x) + t4 • (w - x) := by
      have h := congrArg (WithLp.toLp 2) hz_eq
      simpa only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp, a, b, c, z] using h
    calc y = (y - x) + x := by abel
      _ = (A • (v - x) + B • (u - x) + t4 • (w - x)) + x := by rw [hzV]
      _ = (1 - A - B - t4) • x + A • v + B • u + t4 • w := by module

/-! ## §3 W3-4 的 W3b-ii 消费形：扇角 ∈ (0,π) ⇒ 四点不共面（`Geom.Coplanar`） -/

/-- **W3-4 实例（W3b-ii 消费形）**：在凸局部扇中，dart `x` 的扇角
`azim 0 x.1 x.2 (ι x.1) ∈ (0,π)` 时 `{0, x.1, x.2, ι x.1}` 不共面
（`Kepler.Geom.Coplanar`，与公开 `aff_gt_3_1_rep_cross_dot` 同一读法）。
路线：公开 `properties_fully_surrounded`（Planarity:2372，标准三；
其内部已用 `AZIM_EQ_0_PI_EQ_COPLANAR` 的私有替代）。 -/
theorem pW3b_not_coplanar_of_azim_between (hcl : convexLocalFan_p2 V E FF)
    {x : V3 × V3} (hx : x ∈ FF)
    (h0 : 0 < azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1))
    (hpi : azim 0 x.1 x.2 (ivsRhoNode1_p2 FF x.1) < Real.pi) :
    ¬ Coplanar ({0, x.1, x.2, ivsRhoNode1_p2 FF x.1} : Set V3) := by
  have hl : localFan_p2 V E FF := hcl.1
  have hfan : FAN (0 : V3) V E := by
    obtain ⟨-, -, -, -, -, hf, -, -⟩ := hl
    exact hf
  have hEx : ({x.1, x.2} : Set V3) ∈ E := LOCAL_FAN_IN_FF_IN_ORD_PAIRS hl hx
  obtain ⟨hx1V, hx2V, -, -⟩ := LOCAL_FAN_IMP_IN_V hl hx hx
  have hιV : ivsRhoNode1_p2 FF x.1 ∈ V := LOCAL_FAN_IVS_IN_V hl hx1V
  have hρ : rhoNode1_p2 FF (ivsRhoNode1_p2 FF x.1) = x.1 := LOCAL_FAN_RHO_NODE_IVS hl hx1V
  have hEd : ({ivsRhoNode1_p2 FF x.1, x.1} : Set V3) ∈ E := by
    have hdart : (ivsRhoNode1_p2 FF x.1, rhoNode1_p2 FF (ivsRhoNode1_p2 FF x.1)) ∈ FF :=
      (LOCAL_FAN_RHO_NODE_PROS hl).1 _ hιV
    rw [hρ] at hdart
    have h := LOCAL_FAN_IN_FF_IN_ORD_PAIRS hl hdart
    simpa [ordPairs_p2] using h
  have hnc : ¬ Coplanar
      ({0, ivsRhoNode1_p2 FF x.1, x.1, x.2} : Set V3) :=
    properties_fully_surrounded (x := (0 : V3)) (v := ivsRhoNode1_p2 FF x.1)
      (u := x.1) (w := x.2) hfan hEd hEx h0 hpi
  intro hc
  apply hnc
  have hset : ({0, x.1, x.2, ivsRhoNode1_p2 FF x.1} : Set V3)
      = ({0, ivsRhoNode1_p2 FF x.1, x.1, x.2} : Set V3) := by
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [← hset]

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW3b_jbdnjjb_pos
#print axioms Kepler.Text.pW3b_jbdnjjb_pos
#check @Kepler.Text.pW3b_crossdot_pos_of_azim_lt_pi
#print axioms Kepler.Text.pW3b_crossdot_pos_of_azim_lt_pi
#check @Kepler.Text.pW3b_affGe_3_1_rep
#print axioms Kepler.Text.pW3b_affGe_3_1_rep
#check @Kepler.Text.pW3b_not_coplanar_of_azim_between
#print axioms Kepler.Text.pW3b_not_coplanar_of_azim_between
