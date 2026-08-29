/-
Kepler.Geom.Azim — 方位角与正交标架（flyspeck 第 3/4 章几何词汇，Lean 移植）

源：HOL Light `Multivariate/flyspeck.ml`（持久副本
`/home/scroll/hol-light-ref/Multivariate-flyspeck.ml`；fan 章经
`text_formalization/general/sphere.hl` 消费该词汇）。

- `orthonormal`（flyspeck.ml:1864）：三向量标准正交且右手系。
- `azim`（flyspeck.ml:2148 `azim_def`）：方位角。轴 `w - v` 定为 `e3`，
  `w1` 与 `w2` 的水平角差；退化（轴上共线）时为 0。选择算子 `@`
  对应 `Classical.epsilon`（HOL @ 在无见证时给出垃圾值，理论只在
  `azim` 的特征定理 `AZIM_EXISTS`（flyspeck.ml:2200+）非退化情形下消费它）。
- `aff_ge` / `affsign` / `lin_combo`（flyspeck.ml:685–699）：下一块
  （`Kepler/Geom/Aff.lean`）落地；HOL 的集合和 `sum`/`vsum` 语义在
  无限集上为废值，Lean 侧将带 `Set.Finite` 显式化。

Mathlib 对应：`EuclideanSpace ℝ (Fin 3)`（= HOL `real^3`）、
`Matrix.dotProduct`（`dot`）、`Matrix.cross`（`cross`，右手系）、
`Collinear ℝ {v,w,w1}`（`collinear {v,w,w1}`）。
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Classical
open Complex

namespace Kepler.Geom

/-- HOL `real^3`。 -/
abbrev V3 : Type := EuclideanSpace ℝ (Fin 3)

/-- HOL `orthonormal e1 e2 e3`（flyspeck.ml:1864）：
标准正交 + 右手系（`(e1 cross e2) dot e3 > 0`）。 -/
def Orthonormal3 (e1 e2 e3 : V3) : Prop :=
  e1 ⬝ᵥ e1 = 1 ∧ e2 ⬝ᵥ e2 = 1 ∧ e3 ⬝ᵥ e3 = 1 ∧
    e1 ⬝ᵥ e2 = 0 ∧ e1 ⬝ᵥ e3 = 0 ∧ e2 ⬝ᵥ e3 = 0 ∧
    0 < (crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ)) ⬝ᵥ (e3 : Fin 3 → ℝ)

/-- HOL `collinear {v,w,w1}` 的薄封装（geom.ml 的 `collinear`）。 -/
def Collinear3 (v w w1 : V3) : Prop := Collinear ℝ ({v, w, w1} : Set V3)

/-- `azim` 的特征谓词（`azim_def` 中 `@theta` 的身体，非退化情形）。 -/
def AzimSpec (v w w1 w2 : V3) (theta : ℝ) : Prop :=
  0 ≤ theta ∧ theta < 2 * Real.pi ∧
    ∃ h1 h2 : ℝ, ∀ e1 e2 e3 : V3, Orthonormal3 e1 e2 e3 →
      ((w - v : V3) = dist w v • e3) → w ≠ v →
      ∃ psi r1 r2 : ℝ,
        (w1 - v : V3) = (r1 * Real.cos psi) • (e1 : V3) +
            (r1 * Real.sin psi) • (e2 : V3) + h1 • ((w - v : V3)) ∧
        (w2 - v : V3) = (r2 * Real.cos (psi + theta)) • (e1 : V3) +
            (r2 * Real.sin (psi + theta)) • (e2 : V3) + h2 • ((w - v : V3)) ∧
        0 < r1 ∧ 0 < r2

/-- HOL `azim v w w1 w2`（flyspeck.ml:2148 `azim_def`）。 -/
noncomputable def azim (v w w1 w2 : V3) : ℝ :=
  if Collinear3 v w w1 ∨ Collinear3 v w w2 then 0
  else Classical.epsilon (AzimSpec v w w1 w2)

/-- HOL `wedge v0 v1 w1 w2`（flyspeck.ml:3714）：两条方位射线之间的开楔形。 -/
def wedge (v0 v1 w1 w2 : V3) : Set V3 :=
  {y | ¬ Collinear3 v0 v1 y ∧ 0 < azim v0 v1 w1 y ∧ azim v0 v1 w1 y < azim v0 v1 w1 w2}

/-! ## Pi 型桥接（`EuclideanSpace` 与 `Fin 3 → ℝ`）

本节把 V3 上的点积（`⬝ᵥ`，实际定义在 Pi 侧）、内积与 crossProduct 统一起来。 -/

theorem inner_eq_dot (x y : V3) : inner ℝ x y = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

theorem norm_sq_eq_dot (x : V3) : ‖x‖ ^ 2 = x ⬝ᵥ x := by
  rw [show ‖x‖ ^ 2 = inner ℝ x x from by rw [real_inner_self_eq_norm_sq], inner_eq_dot]

theorem coe_toLp (p : Fin 3 → ℝ) : ((WithLp.toLp 2 p : V3) : Fin 3 → ℝ) = p :=
  WithLp.ofLp_toLp 2 p

theorem inner_toLp (p q : Fin 3 → ℝ) :
    inner ℝ (WithLp.toLp 2 p : V3) (WithLp.toLp 2 q : V3) = p ⬝ᵥ q := by
  rw [inner_eq_dot, coe_toLp, coe_toLp]

/-! ## 三点共线特征 -/

theorem collinear3_iff_smul (hw : w ≠ v) :
    Collinear3 v w w1 ↔ ∃ c : ℝ, w1 - v = c • (w - v) := by
  constructor
  · intro h
    obtain ⟨p₀, vec, hall⟩ := (collinear_iff_exists_forall_eq_smul_vadd
      ({v, w, w1} : Set V3)).mp h
    obtain ⟨r1, h1⟩ := hall v (by simp)
    obtain ⟨r2, h2⟩ := hall w (by simp)
    obtain ⟨r3, h3⟩ := hall w1 (by simp)
    have hvw : w - v = (r2 - r1) • vec := by
      rw [h2, h1, vadd_eq_add, vadd_eq_add]; module
    have hw1 : w1 - v = (r3 - r1) • vec := by
      rw [h3, h1, vadd_eq_add, vadd_eq_add]; module
    have hr : r2 - r1 ≠ 0 := by
      intro he
      apply hw
      have hz : w - v = 0 := by rw [hvw, he, zero_smul]
      exact sub_eq_zero.mp hz
    have key : ((r3 - r1) / (r2 - r1)) * (r2 - r1) = r3 - r1 := div_mul_cancel₀ _ hr
    refine ⟨(r3 - r1) / (r2 - r1), ?_⟩
    rw [hw1, hvw, smul_smul, key]
  · intro ⟨c, hc⟩
    refine (collinear_iff_exists_forall_eq_smul_vadd ({v, w, w1} : Set V3)).mpr ⟨v, w - v, ?_⟩
    intro p hp
    rw [Set.mem_insert_iff] at hp
    rcases hp with rfl | hp
    · exact ⟨0, by simp⟩
    rw [Set.mem_insert_iff] at hp
    rcases hp with rfl | hp
    · exact ⟨1, by simp⟩
    rw [Set.mem_singleton_iff] at hp
    refine ⟨c, ?_⟩
    rw [hp, vadd_eq_add, ← hc]
    abel

theorem collinear3_of_eq (he : w = v) : Collinear3 v w w1 := by
  rw [he]
  have hset : ({v, v, w1} : Set V3) = {v, w1} := by ext x; simp
  show Collinear ℝ ({v, v, w1} : Set V3)
  rw [hset]
  exact collinear_pair ℝ v w1

/-- 任一非零向量上存在右手 ON 标架（`exists_on3_eq_smul` 的辅助 dot 事实）。 -/
theorem dot_toLp (p : Fin 3 → ℝ) (y : V3) :
    (WithLp.toLp 2 p : V3) ⬝ᵥ y = p ⬝ᵥ (y : Fin 3 → ℝ) := by
  have hy : y = (WithLp.toLp 2 ((y : Fin 3 → ℝ)) : V3) := (WithLp.toLp_ofLp 2 _).symm
  rw [hy, ← inner_eq_dot, inner_toLp, WithLp.ofLp_toLp]

/-- `v ⬝ᵥ v > 0 ↔ v ≠ 0`（Pi 侧）。 -/
theorem dot_self_pos_iff {m : Type} [Fintype m] (v : m → ℝ) :
    0 < v ⬝ᵥ v ↔ v ≠ 0 := by
  have hnn : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  constructor
  · intro h he
    rw [he, zero_dotProduct] at h
    exact absurd h (by norm_num)
  · intro h
    by_contra hle
    have h0 : v ⬝ᵥ v = 0 := le_antisymm (le_of_not_gt hle) hnn
    have hall : ∀ i ∈ (Finset.univ : Finset m), v i * v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).mp h0
    apply h
    funext i
    have hvi : v i = 0 := mul_self_eq_zero.mp (hall i (Finset.mem_univ i))
    rw [hvi]
    rfl

/-! ## ON 标架基本性质 -/

theorem on3_linearIndependent (h : Orthonormal3 e1 e2 e3) :
    LinearIndependent ℝ (![e1, e2, e3] : Fin 3 → V3) := by
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at hg
  have key : ∀ j : Fin 3, g j = 0 := by
    intro j
    have d0 : (g 0 • e1 + g 1 • e2 + g 2 • e3) ⬝ᵥ e1 = 0 := by rw [hg]; simp
    have d1 : (g 0 • e1 + g 1 • e2 + g 2 • e3) ⬝ᵥ e2 = 0 := by rw [hg]; simp
    have d2 : (g 0 • e1 + g 1 • e2 + g 2 • e3) ⬝ᵥ e3 = 0 := by rw [hg]; simp
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct] at d0 d1 d2
    simp only [dotProduct_comm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ),
      dotProduct_comm (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ),
      dotProduct_comm (e3 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ),
      smul_eq_mul, mul_zero, add_zero, zero_add, mul_one, h11, h12, h13, h22, h23, h33]
      at d0 d1 d2
    fin_cases j
    · exact d0
    · exact d1
    · exact d2
  intro i
  exact key i

noncomputable def on3_basis (h : Orthonormal3 e1 e2 e3) : Module.Basis (Fin 3) ℝ V3 :=
  basisOfLinearIndependentOfCardEqFinrank (on3_linearIndependent h) (by simp)

theorem on3_expand (h : Orthonormal3 e1 e2 e3) (u : V3) :
    u = (u ⬝ᵥ e1) • e1 + (u ⬝ᵥ e2) • e2 + (u ⬝ᵥ e3) • e3 := by
  have hcopy := h
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hcopy
  have hb : ((on3_basis h : Module.Basis (Fin 3) ℝ V3) : Fin 3 → V3) =
      (![e1, e2, e3] : Fin 3 → V3) := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hsum : ∑ i, ((on3_basis h).repr u i) • (![e1, e2, e3] : Fin 3 → V3) i = u := by
    have hs := (on3_basis h).sum_repr u
    rwa [hb] at hs
  have hrep : ∀ j : Fin 3, ((on3_basis h).repr u) j =
      u ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) j := by
    intro j
    fin_cases j
    · show ((on3_basis h).repr u) 0 = u ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 0
      have hcong := congrArg (fun x : V3 => x ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 0) hsum
      simp only [Fin.sum_univ_three, WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct,
        smul_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons,
        dotProduct_comm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ),
        dotProduct_comm (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_add, h11, h12, h13] at hcong ⊢
      exact hcong
    · show ((on3_basis h).repr u) 1 = u ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 1
      have hcong := congrArg (fun x : V3 => x ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 1) hsum
      simp only [Fin.sum_univ_three, WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct,
        smul_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons,
        dotProduct_comm (e3 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ),
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, h11, h12, h22, h23] at hcong ⊢
      exact hcong
    · show ((on3_basis h).repr u) 2 = u ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 2
      have hcong := congrArg (fun x : V3 => x ⬝ᵥ (![e1, e2, e3] : Fin 3 → V3) 2) hsum
      simp only [Fin.sum_univ_three, WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct,
        smul_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons,
        smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, h11, h13, h23, h33] at hcong ⊢
      exact hcong
  conv_lhs => rw [← hsum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [hrep 0, hrep 1, hrep 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]

/-! ## 右手标架的 cross 恒等式 -/

/-- ON 右手标架满足 `e1 × e2 = e3`（Pi 侧）。 -/
theorem on3_cross (h : Orthonormal3 e1 e2 e3) :
    crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ) = (e3 : Fin 3 → ℝ) := by
  have hcopy := h
  obtain ⟨h11, h22, h33, h12, h13, h23, hpos⟩ := hcopy
  set X : V3 := (WithLp.toLp 2 (crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ)) : V3) with hX
  have hx1 : X ⬝ᵥ e1 = 0 := by
    rw [hX, dot_toLp, ← cross_anticomm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), neg_dotProduct,
      dotProduct_comm (crossProduct (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ)) (e1 : Fin 3 → ℝ),
      dot_cross_self, neg_zero]
  have hx2 : X ⬝ᵥ e2 = 0 := by
    rw [hX, dot_toLp,
      dotProduct_comm (crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ)) (e2 : Fin 3 → ℝ),
      dot_cross_self]
  have hrpos : 0 < X ⬝ᵥ e3 := by
    rw [hX, dot_toLp]
    exact hpos
  have he3n : ‖e3‖ ^ 2 = 1 := by
    rw [norm_sq_eq_dot]
    exact h33
  have hnormsq : ‖X‖ ^ 2 = 1 := by
    rw [norm_sq_eq_dot, hX, dot_toLp, coe_toLp, cross_dot_cross,
      dotProduct_comm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), h11, h22, h12]
    norm_num
  have hexp : X = (X ⬝ᵥ e1) • e1 + (X ⬝ᵥ e2) • e2 + (X ⬝ᵥ e3) • e3 := on3_expand h X
  rw [hx1, hx2, zero_smul, zero_smul, zero_add, zero_add] at hexp
  have hcoe : (X ⬝ᵥ e3) ^ 2 = 1 := by
    have h2 : ‖X‖ ^ 2 = ‖(X ⬝ᵥ e3) • e3‖ ^ 2 := by conv_lhs => rw [hexp]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hrpos), mul_pow, he3n] at h2
    rw [hnormsq] at h2
    linarith [sq_nonneg (X ⬝ᵥ e3)]
  have hval : X ⬝ᵥ e3 = 1 := by
    rcases sq_eq_one_iff.mp hcoe with he | he
    · exact he
    · linarith
  have hXe3 : X = e3 := by rw [hexp, hval, one_smul]
  have hcoe' : (X : Fin 3 → ℝ) = (e3 : Fin 3 → ℝ) :=
    congrArg (fun x : V3 => (x : Fin 3 → ℝ)) hXe3
  rwa [coe_toLp] at hcoe'

/-- 任一非零向量上存在右手 ON 标架使其第三轴与该向量同向。 -/
theorem exists_on3_eq_smul (u : V3) (hu : u ≠ 0) :
    ∃ e1 e2 e3 : V3, Orthonormal3 e1 e2 e3 ∧ u = ‖u‖ • e3 := by
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set c : Fin 3 → ℝ :=
    if (u : Fin 3 → ℝ) 1 = 0 ∧ (u : Fin 3 → ℝ) 2 = 0 then
      crossProduct (u : Fin 3 → ℝ) (![0, 1, 0] : Fin 3 → ℝ)
    else crossProduct (u : Fin 3 → ℝ) (![1, 0, 0] : Fin 3 → ℝ) with hc
  have hcz : c ≠ 0 := by
    by_cases hz : (u : Fin 3 → ℝ) 1 = 0 ∧ (u : Fin 3 → ℝ) 2 = 0
    · have hu0 : (u : Fin 3 → ℝ) 0 ≠ 0 := by
        intro h0
        apply hu
        have hall : ∀ i, (u : Fin 3 → ℝ) i = 0 := by
          intro i; fin_cases i
          · exact h0
          · exact hz.1
          · exact hz.2
        have hz2 : u ⬝ᵥ u = 0 := by
          simp only [dotProduct, hall]
          simp
        have h3 : ‖u‖ ^ 2 = 0 := by rw [norm_sq_eq_dot]; exact hz2
        have h4 : ‖u‖ = 0 := by
          exact (pow_eq_zero_iff two_ne_zero).mp h3
        exact (norm_eq_zero).mp h4
      intro he
      rw [hc, if_pos hz, cross_apply] at he
      have h2 := congrFun he 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h2
      norm_num at h2
      exact hu0 h2
    · intro he
      rw [hc, if_neg hz, cross_apply] at he
      have h2 := congrFun he 1
      have h3 := congrFun he 2
      simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.cons_val_zero, Pi.zero_apply] at h2 h3
      norm_num at h2 h3
      exact hz ⟨h3, h2⟩
  have hcu : (u : Fin 3 → ℝ) ⬝ᵥ c = 0 := by
    by_cases hz : (u : Fin 3 → ℝ) 1 = 0 ∧ (u : Fin 3 → ℝ) 2 = 0
    · rw [hc, if_pos hz,
        dotProduct_comm (u : Fin 3 → ℝ) (crossProduct (u : Fin 3 → ℝ)
          (![0, 1, 0] : Fin 3 → ℝ)),
        ← cross_anticomm (![0, 1, 0] : Fin 3 → ℝ) (u : Fin 3 → ℝ),
        neg_dotProduct,
        dotProduct_comm (crossProduct (![0, 1, 0] : Fin 3 → ℝ) (u : Fin 3 → ℝ))
          (u : Fin 3 → ℝ),
        dot_cross_self, neg_zero]
    · rw [hc, if_neg hz,
        dotProduct_comm (u : Fin 3 → ℝ) (crossProduct (u : Fin 3 → ℝ)
          (![1, 0, 0] : Fin 3 → ℝ)),
        ← cross_anticomm (![1, 0, 0] : Fin 3 → ℝ) (u : Fin 3 → ℝ),
        neg_dotProduct,
        dotProduct_comm (crossProduct (![1, 0, 0] : Fin 3 → ℝ) (u : Fin 3 → ℝ))
          (u : Fin 3 → ℝ),
        dot_cross_self, neg_zero]
  -- x1 与 e1
  have hx1u : inner ℝ (WithLp.toLp 2 c : V3) u = 0 := by
    rw [inner_eq_dot, dot_toLp, dotProduct_comm]
    exact hcu
  have hx1n : 0 < ‖(WithLp.toLp 2 c : V3)‖ := by
    have h1 : ‖(WithLp.toLp 2 c : V3)‖ ^ 2 = c ⬝ᵥ c := by
      rw [norm_sq_eq_dot, dot_toLp, coe_toLp]
    have h2 : 0 < c ⬝ᵥ c := (dot_self_pos_iff c).mpr hcz
    have h3 : 0 < ‖(WithLp.toLp 2 c : V3)‖ ^ 2 := by rw [h1]; exact h2
    by_contra hle
    push_neg at hle
    have hz' : ‖(WithLp.toLp 2 c : V3)‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [hz'] at h3
    exact absurd h3 (by norm_num)
  set e1 : V3 := ‖(WithLp.toLp 2 c : V3)‖⁻¹ • (WithLp.toLp 2 c : V3) with he1
  set e3 : V3 := ‖u‖⁻¹ • u with he3
  have he1n : ‖e1‖ = 1 := by
    rw [he1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx1n),
      inv_mul_cancel₀ hx1n.ne']
  have he3n : ‖e3‖ = 1 := by
    rw [he3, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']
  have he11 : e1 ⬝ᵥ e1 = 1 := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq, he1n]; norm_num
  have he33 : e3 ⬝ᵥ e3 = 1 := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq, he3n]; norm_num
  have he13 : e1 ⬝ᵥ e3 = 0 := by
    rw [← inner_eq_dot, real_inner_smul_left, real_inner_smul_right, hx1u]; norm_num
  set e2 : V3 := (WithLp.toLp 2 (crossProduct (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ)) : V3)
    with he2
  have he22 : e2 ⬝ᵥ e2 = 1 := by
    have hd : e2 ⬝ᵥ e2 = (e3 : Fin 3 → ℝ) ⬝ᵥ (e3 : Fin 3 → ℝ) *
        ((e1 : Fin 3 → ℝ) ⬝ᵥ (e1 : Fin 3 → ℝ)) -
      (e3 : Fin 3 → ℝ) ⬝ᵥ (e1 : Fin 3 → ℝ) * ((e1 : Fin 3 → ℝ) ⬝ᵥ (e3 : Fin 3 → ℝ)) := by
      rw [he2, dot_toLp, coe_toLp, cross_dot_cross]
    rw [he33, he11, dotProduct_comm (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), he13] at hd
    rw [hd]; norm_num
  have he12 : e1 ⬝ᵥ e2 = 0 := by
    rw [he2, coe_toLp, dot_cross_self]
  have he23 : e2 ⬝ᵥ e3 = 0 := by
    rw [he2, dot_toLp, ← cross_anticomm (e1 : Fin 3 → ℝ) (e3 : Fin 3 → ℝ),
      neg_dotProduct,
      dotProduct_comm (crossProduct (e1 : Fin 3 → ℝ) (e3 : Fin 3 → ℝ)) (e3 : Fin 3 → ℝ),
      dot_cross_self, neg_zero]
  have hpos : 0 < crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ) ⬝ᵥ (e3 : Fin 3 → ℝ) := by
    have hq : crossProduct (e1 : Fin 3 → ℝ) (crossProduct (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ))
        = ((e1 : Fin 3 → ℝ) ⬝ᵥ (e1 : Fin 3 → ℝ)) • (e3 : Fin 3 → ℝ) -
          ((e3 : Fin 3 → ℝ) ⬝ᵥ (e1 : Fin 3 → ℝ)) • (e1 : Fin 3 → ℝ) :=
      cross_cross_eq_smul_sub_smul' _ _ _
    have he2coe : (e2 : Fin 3 → ℝ) = crossProduct (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ) := by
      rw [he2, coe_toLp]
    rw [he2coe, hq, sub_dotProduct, smul_dotProduct, smul_dotProduct, he11, he33, he13,
      smul_eq_mul, smul_eq_mul, mul_zero, sub_zero, mul_one]
    norm_num
  refine ⟨e1, e2, e3, ⟨he11, he22, he33, he12, he13, he23, hpos⟩, ?_⟩
  rw [he3, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]

/-! ## 标架变换与 ℂ 坐标 -/

private theorem crossAdd (p q r : Fin 3 → ℝ) :
    crossProduct (p + q) r = crossProduct p r + crossProduct q r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.add_apply]

private theorem crossSmul (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem crossAdd' (p q r : Fin 3 → ℝ) :
    crossProduct p (q + r) = crossProduct p q + crossProduct p r := by
  rw [← cross_anticomm (q + r) p, ← cross_anticomm q p, ← cross_anticomm r p, crossAdd,
    neg_add]

private theorem crossSmul' (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct p (t • r) = t • crossProduct p r := by
  rw [← cross_anticomm (t • r) p, crossSmul, ← cross_anticomm p r, smul_neg, neg_neg]

/-- 同轴（e3 = f3）两个右手 ON 标架的平面 ℂ 坐标相差一个单位复数倍。 -/
theorem on3_axis_change (he : Orthonormal3 e1 e2 e3) (hf : Orthonormal3 f1 f2 f3)
    (h3 : e3 = f3) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ x : V3,
      ((x ⬝ᵥ e1) + (x ⬝ᵥ e2) * I = u * ((x ⬝ᵥ f1) + (x ⬝ᵥ f2) * I)) := by
  have heC := he
  have hfC := hf
  obtain ⟨hee11, hee22, hee33, hee12, hee13, hee23, -⟩ := heC
  obtain ⟨hff11, hff22, hff33, hff12, hff13, hff23, -⟩ := hfC
  set a := f1 ⬝ᵥ e1 with ha
  set b := f1 ⬝ᵥ e2 with hb
  set c := f2 ⬝ᵥ e1 with hc
  set d := f2 ⬝ᵥ e2 with hd
  have hf1e3 : f1 ⬝ᵥ e3 = 0 := by rw [h3]; exact hff13
  have hf2e3 : f2 ⬝ᵥ e3 = 0 := by rw [h3]; exact hff23
  have hf1exp : f1 = a • e1 + b • e2 := by
    have hexp := on3_expand he f1
    rw [show f1 ⬝ᵥ e1 = a from rfl, show f1 ⬝ᵥ e2 = b from rfl, hf1e3, zero_smul,
      add_zero] at hexp
    exact hexp
  have hf2exp : f2 = c • e1 + d • e2 := by
    have hexp := on3_expand he f2
    rw [show f2 ⬝ᵥ e1 = c from rfl, show f2 ⬝ᵥ e2 = d from rfl, hf2e3, zero_smul,
      add_zero] at hexp
    exact hexp
  have hbilin : ∀ (p q : V3), (p ⬝ᵥ q = _) := fun _ _ => rfl
  have h1a : f1 ⬝ᵥ f1 = a * a + b * b := by
    have h : (a • e1 + b • e2) ⬝ᵥ (a • e1 + b • e2) = a * a + b * b := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (e2 : Fin 3 → ℝ)
          (e1 : Fin 3 → ℝ), hee11, hee22, hee12, mul_zero, add_zero]
      ring
    rw [hf1exp]
    exact h
  have hab : a * a + b * b = 1 := by rw [← h1a]; exact hff11
  have h1c : f2 ⬝ᵥ f2 = c * c + d * d := by
    have h : (c • e1 + d • e2) ⬝ᵥ (c • e1 + d • e2) = c * c + d * d := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (e2 : Fin 3 → ℝ)
          (e1 : Fin 3 → ℝ), hee11, hee22, hee12, mul_zero, add_zero]
      ring
    rw [hf2exp]
    exact h
  have hcd : c * c + d * d = 1 := by rw [← h1c]; exact hff22
  have h1x : f1 ⬝ᵥ f2 = a * c + b * d := by
    have h : (a • e1 + b • e2) ⬝ᵥ (c • e1 + d • e2) = a * c + b * d := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (e2 : Fin 3 → ℝ)
          (e1 : Fin 3 → ℝ), hee11, hee22, hee12, mul_zero, add_zero]
      ring
    rw [hf1exp, hf2exp]
    exact h
  have hacbd : a * c + b * d = 0 := by rw [← h1x]; exact hff12
  -- 行列式恒等式：ad - bc = 1
  have hE1E2 : crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ) = (e3 : Fin 3 → ℝ) :=
    on3_cross he
  have h3coe : (e3 : Fin 3 → ℝ) = (f3 : Fin 3 → ℝ) := congrArg (fun z : V3 =>
    (z : Fin 3 → ℝ)) h3
  have hf12cross : crossProduct (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ) = (f3 : Fin 3 → ℝ) :=
    on3_cross hf
  have hcoe1 : (f1 : Fin 3 → ℝ) = a • (e1 : Fin 3 → ℝ) + b • (e2 : Fin 3 → ℝ) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hf1exp
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  have hcoe2 : (f2 : Fin 3 → ℝ) = c • (e1 : Fin 3 → ℝ) + d • (e2 : Fin 3 → ℝ) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hf2exp
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  have hexp2 : crossProduct (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ)
      = (a * d - b * c) • (e3 : Fin 3 → ℝ) := by
    rw [hcoe1, hcoe2, crossAdd, crossAdd', crossAdd', crossSmul, crossSmul, crossSmul,
      crossSmul, crossSmul', crossSmul', crossSmul', crossSmul',
      cross_self (e1 : Fin 3 → ℝ), cross_self (e2 : Fin 3 → ℝ), hE1E2,
      ← cross_anticomm (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ), hE1E2]
    module
  have hdet : a * d - b * c = 1 := by
    have w1 : crossProduct (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ) ⬝ᵥ (e3 : Fin 3 → ℝ)
        = 1 := by
      rw [hf12cross, h3coe, hff33]
    have w2 : crossProduct (f1 : Fin 3 → ℝ) (f2 : Fin 3 → ℝ) ⬝ᵥ (e3 : Fin 3 → ℝ)
        = (a * d - b * c) * 1 := by
      rw [hexp2, smul_dotProduct, hee33, smul_eq_mul, mul_one]
    linarith
  have hcd' : c = -b ∧ d = a := by
    constructor
    · calc c = (a * a + b * b) * c := by rw [hab, one_mul]
        _ = a * (a * c + b * d) - b * (a * d - b * c) := by ring
        _ = a * 0 - b * 1 := by rw [hacbd, hdet]
        _ = -b := by ring
    · calc d = (a * a + b * b) * d := by rw [hab, one_mul]
        _ = b * (a * c + b * d) + a * (a * d - b * c) := by ring
        _ = b * 0 + a * 1 := by rw [hacbd, hdet]
        _ = a := by ring
  -- x 的 e-坐标用 f-坐标表出
  have hf3e1 : inner ℝ f3 e1 = 0 := by
    rw [← h3, show inner ℝ e3 e1 = (e3 : V3) ⬝ᵥ e1 from (inner_eq_dot e3 e1),
      dotProduct_comm (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), hee13]
  have hf3e2 : inner ℝ f3 e2 = 0 := by
    rw [← h3, show inner ℝ e3 e2 = (e3 : V3) ⬝ᵥ e2 from (inner_eq_dot e3 e2),
      dotProduct_comm (e3 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ), hee23]
  refine ⟨a + b * I, ?_, ?_⟩
  · have hsq : ‖a + b * I‖ ^ 2 = a * a + b * b := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, add_zero, mul_one, zero_add, sub_self]
    have hnn : 0 ≤ ‖a + b * I‖ := norm_nonneg _
    rcases sq_eq_one_iff.mp (hsq.trans hab) with h' | h'
    · exact h'
    · linarith
  · intro x
    have hxexp := on3_expand hf x
    have hxe1 : x ⬝ᵥ e1 = (x ⬝ᵥ f1) * a + (x ⬝ᵥ f2) * c := by
      have hin : inner ℝ x e1
          = (x ⬝ᵥ f1) * inner ℝ f1 e1 + (x ⬝ᵥ f2) * inner ℝ f2 e1 := by
        conv_lhs => rw [hxexp]
        rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, hf3e1, mul_zero, add_zero]
      rw [inner_eq_dot x e1, inner_eq_dot f1 e1, inner_eq_dot f2 e1] at hin
      exact hin
    have hxe2 : x ⬝ᵥ e2 = (x ⬝ᵥ f1) * b + (x ⬝ᵥ f2) * d := by
      have hin : inner ℝ x e2
          = (x ⬝ᵥ f1) * inner ℝ f1 e2 + (x ⬝ᵥ f2) * inner ℝ f2 e2 := by
        conv_lhs => rw [hxexp]
        rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, hf3e2, mul_zero, add_zero]
      rw [inner_eq_dot x e2, inner_eq_dot f1 e2, inner_eq_dot f2 e2] at hin
      exact hin
    rw [hxe1, hxe2, hcd'.1, hcd'.2]
    rw [Complex.ext_iff]
    constructor
    · simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, add_zero, sub_zero]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, add_zero, sub_zero]
      ring


/-! ## ℂ 角差主值 -/

/-- 标架平面坐标的 ℂ 像。 -/
def zOf (a b x : V3) : ℂ := (x ⬝ᵥ a) + (x ⬝ᵥ b) * I

/-- 相位差主值（AZIM_EXISTS 的 2D 核心）。 -/
theorem exists_angle_diff (a b : ℂ) (ha : a ≠ 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧
      ∀ ψ : ℝ, a = ‖a‖ * Complex.exp (ψ * I) → b = ‖b‖ * Complex.exp ((ψ + θ) * I) := by
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  set θ : ℝ := Complex.arg b - Complex.arg a
      - (Int.floor ((Complex.arg b - Complex.arg a) / (2 * Real.pi)) : ℝ) * (2 * Real.pi)
    with hθdef
  by_cases hb : b = 0
  · refine ⟨0, le_refl 0, by positivity, ?_⟩
    intro ψ _
    rw [hb]
    norm_num
  refine ⟨θ, ?_, ?_, ?_⟩
  · have h1 := Int.floor_le ((Complex.arg b - Complex.arg a) / (2 * Real.pi))
    have hkx := (le_div_iff₀ h2pi).mp h1
    linarith
  · have h2 : (Complex.arg b - Complex.arg a) / (2 * Real.pi)
        < (Int.floor ((Complex.arg b - Complex.arg a) / (2 * Real.pi)) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hxk := (div_lt_iff₀ h2pi).mp h2
    linarith
  · intro ψ hψ
    have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    have hexp : Complex.exp (ψ * I) = Complex.exp (Complex.arg a * I) := by
      have hc : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hna
      exact mul_left_cancel₀ hc (hψ.symm.trans (Complex.norm_mul_exp_arg_mul_I a).symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hpsi : ψ = Complex.arg a + (n:ℝ) * (2 * Real.pi) := by
      have hI2 : ((ψ : ℝ) : ℂ) * Complex.I
          = ((Complex.arg a + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
        rw [hn]
        push_cast
        ring
      have h3 : ((ψ : ℝ) : ℂ)
          = ((Complex.arg a + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
        mul_right_cancel₀ Complex.I_ne_zero hI2
      exact_mod_cast h3
    have hpsic : ((ψ : ℝ) : ℂ)
        = ((Complex.arg a + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      exact_mod_cast hpsi
    have hfin : Complex.exp ((↑ψ + ↑θ) * I) = Complex.exp (Complex.arg b * I) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨n - Int.floor ((Complex.arg b - Complex.arg a) / (2 * Real.pi)), ?_⟩
      rw [hpsic]
      push_cast
      rw [hθdef]
      push_cast
      ring
    rw [hfin, Complex.norm_mul_exp_arg_mul_I b]


/-- 相位乘法：`e^{i arg E} • (n e^{it}) = n e^{i(t + arg E)}`。 -/
private theorem exp_mul_polar (E : ℂ) (t : ℝ) (z : ℂ) (n : ℝ)
    (hp : z = n * Complex.exp (t * I)) :
    Complex.exp (Complex.arg E * I) * z = n * Complex.exp ((t + Complex.arg E) * I) := by
  rw [hp, mul_left_comm, ← Complex.exp_add]
  congr 1
  congr 1
  ring


/-! ## AzimSpec 的满足性 -/

/-- 轴向量的平面分量正交性。 -/
theorem axis_perp (hax : (w - v : V3) = dist w v • e3) (he : Orthonormal3 e1 e2 e3) :
    (w - v : V3) ⬝ᵥ e1 = 0 ∧ (w - v : V3) ⬝ᵥ e2 = 0 := by
  obtain ⟨-, -, -, -, he13, he23, -⟩ := he
  have h1 : inner ℝ (w - v) e1 = (dist w v) * inner ℝ e3 e1 := by
    rw [hax, real_inner_smul_left]
  have h2 : inner ℝ (w - v) e2 = (dist w v) * inner ℝ e3 e2 := by
    rw [hax, real_inner_smul_left]
  rw [inner_eq_dot, inner_eq_dot] at h1 h2
  rw [dotProduct_comm (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), he13, mul_zero] at h1
  rw [dotProduct_comm (e3 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ), he23, mul_zero] at h2
  exact ⟨h1, h2⟩

/-- ℂ 坐标等式 → V3 表示（AzimSpec 身体的构造方向）。 -/
theorem rep_of_zOf {v w : V3} (he : Orthonormal3 e1 e2 e3)
    (hax : (w - v : V3) = dist w v • e3) (hw : w ≠ v)
    (y : V3) (τ ρ : ℝ) (hy : zOf e1 e2 (y - v) = ρ * Complex.exp (τ * I)) :
    y - v = (ρ * Real.cos τ) • e1 + (ρ * Real.sin τ) • e2
      + (((y - v : V3) ⬝ᵥ e3) / dist w v) • (w - v) := by
  have hd : 0 < dist w v := dist_pos.mpr hw
  have hz : (y - v : V3) ⬝ᵥ e1 + (y - v : V3) ⬝ᵥ e2 * I
      = ↑(ρ * Real.cos τ) + ↑(ρ * Real.sin τ) * I := by
    show zOf e1 e2 (y - v) = _
    rw [hy, Complex.exp_mul_I]
    push_cast
    ring
  have h1 : (y - v : V3) ⬝ᵥ e1 = ρ * Real.cos τ := by
    have h := congrArg Complex.re hz
    simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h
  have h2 : (y - v : V3) ⬝ᵥ e2 = ρ * Real.sin τ := by
    have h := congrArg Complex.im hz
    simpa [Complex.cos_ofReal_im, Complex.sin_ofReal_re] using h
  have hexp := on3_expand he (y - v)
  rw [h1, h2] at hexp
  rw [hax, smul_smul, div_mul_cancel₀ _ hd.ne']
  exact hexp

/-- V3 表示 → ℂ 坐标等式。 -/
theorem zOf_of_rep {v w : V3} (he : Orthonormal3 e1 e2 e3)
    (hax : (w - v : V3) = dist w v • e3)
    {y : V3} {τ ρ hY : ℝ}
    (hy : y - v = (ρ * Real.cos τ) • e1 + (ρ * Real.sin τ) • e2 + hY • (w - v)) :
    zOf e1 e2 (y - v) = ρ * Complex.exp (τ * I) := by
  obtain ⟨hp1, hp2⟩ := axis_perp hax he
  have hd1 : (y - v : V3) ⬝ᵥ e1 = ρ * Real.cos τ := by
    have hin : inner ℝ (y - v) e1 = inner ℝ
        ((ρ * Real.cos τ) • e1 + (ρ * Real.sin τ) • e2 + hY • (w - v)) e1 := by
      conv_lhs => rw [hy]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left] at hin
    simp only [inner_eq_dot, show (w - v : V3) ⬝ᵥ e1 = 0 from hp1,
      dotProduct_comm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), he.1, he.2.2.2.1,
      mul_zero, mul_one, add_zero] at hin
    exact hin
  have hd2 : (y - v : V3) ⬝ᵥ e2 = ρ * Real.sin τ := by
    have hin : inner ℝ (y - v) e2 = inner ℝ
        ((ρ * Real.cos τ) • e1 + (ρ * Real.sin τ) • e2 + hY • (w - v)) e2 := by
      conv_lhs => rw [hy]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left] at hin
    simp only [inner_eq_dot, show (w - v : V3) ⬝ᵥ e2 = 0 from hp2, he.2.1,
      he.2.2.2.1, mul_zero, mul_one, zero_add, add_zero] at hin
    exact hin
  show (y - v : V3) ⬝ᵥ e1 + (y - v : V3) ⬝ᵥ e2 * I = _
  rw [hd1, hd2, Complex.exp_mul_I]
  push_cast
  ring

/-- z 坐标非零 ↔ 非共线。 -/
theorem zOf_ne_zero_iff {v w : V3} (he : Orthonormal3 e1 e2 e3)
    (hax : (w - v : V3) = dist w v • e3) (hw : w ≠ v) (y : V3) :
    zOf e1 e2 (y - v) ≠ 0 ↔ ¬ Collinear3 v w y := by
  have hd : 0 < dist w v := dist_pos.mpr hw
  obtain ⟨hp1, hp2⟩ := axis_perp hax he
  constructor
  · intro hz hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hw).mp hcol
    apply hz
    have hd1 : (y - v : V3) ⬝ᵥ e1 = 0 := by
      rw [hc, show ((c : ℝ) • (w - v) : V3) ⬝ᵥ e1 = c * ((w - v : V3) ⬝ᵥ e1) from by
        rw [← inner_eq_dot, ← inner_eq_dot, real_inner_smul_left], hp1, mul_zero]
    have hd2 : (y - v : V3) ⬝ᵥ e2 = 0 := by
      rw [hc, show ((c : ℝ) • (w - v) : V3) ⬝ᵥ e2 = c * ((w - v : V3) ⬝ᵥ e2) from by
        rw [← inner_eq_dot, ← inner_eq_dot, real_inner_smul_left], hp2, mul_zero]
    show (y - v : V3) ⬝ᵥ e1 + (y - v : V3) ⬝ᵥ e2 * I = 0
    rw [hd1, hd2]
    norm_num
  · intro hcol
    intro hz0
    apply hcol
    have hre : (y - v : V3) ⬝ᵥ e1 = 0 := by
      have h := congrArg Complex.re hz0
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        add_zero, mul_one, zero_add, sub_self] at h
      simpa using h
    have him : (y - v : V3) ⬝ᵥ e2 = 0 := by
      have h := congrArg Complex.im hz0
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, add_zero,
        zero_add] at h
      simpa using h
    have hexp := on3_expand he (y - v)
    rw [hre, him, zero_smul, zero_smul, zero_add, zero_add] at hexp
    refine (collinear3_iff_smul hw).mpr ⟨((y - v : V3) ⬝ᵥ e3) / dist w v, ?_⟩
    rw [hax, smul_smul, div_mul_cancel₀ _ hd.ne']
    exact hexp


/-- AzimSpec 在非退化情形可满足（flyspeck.ml AZIM_EXISTS）。 -/
theorem azimSpec_exists (h1 : ¬ Collinear3 v w w1) (h2 : ¬ Collinear3 v w w2) :
    ∃ θ, AzimSpec v w w1 w2 θ := by
  have hwv : w ≠ v := fun he => h1 (collinear3_of_eq he)
  obtain ⟨f1, f2, f3, hf, halign⟩ := exists_on3_eq_smul (w - v) (sub_ne_zero.mpr hwv)
  have haxf : (w - v : V3) = dist w v • f3 := by
    rw [dist_eq_norm]
    exact halign
  have hzf1 : zOf f1 f2 (w1 - v) ≠ 0 := (zOf_ne_zero_iff hf haxf hwv w1).mpr h1
  have hzf2 : zOf f1 f2 (w2 - v) ≠ 0 := (zOf_ne_zero_iff hf haxf hwv w2).mpr h2
  obtain ⟨θ, hθ0, hθ1, hθmain⟩ := exists_angle_diff (zOf f1 f2 (w1 - v))
    (zOf f1 f2 (w2 - v)) hzf1
  refine ⟨θ, hθ0, hθ1, ((w1 - v : V3) ⬝ᵥ f3) / dist w v,
    ((w2 - v : V3) ⬝ᵥ f3) / dist w v, ?_⟩
  intro e1 e2 e3 he hax hw
  have he3f : e3 = f3 := by
    have hc : dist w v ≠ 0 := dist_ne_zero.mpr hwv
    have hsub : dist w v • e3 - dist w v • f3 = 0 := by
      rw [← hax, ← haxf, sub_self]
    rw [← smul_sub] at hsub
    refine sub_eq_zero.mp ?_
    exact smul_eq_zero.mp hsub |>.resolve_left hc
  obtain ⟨u, hu1, hu⟩ := on3_axis_change he hf he3f
  have hue : u = Complex.exp (Complex.arg u * I) := by
    have hp := Complex.norm_mul_exp_arg_mul_I u
    rw [hu1, Complex.ofReal_one, one_mul] at hp
    exact hp.symm
  have hfpol1 : zOf f1 f2 (w1 - v)
      = ‖zOf f1 f2 (w1 - v)‖ * Complex.exp (Complex.arg (zOf f1 f2 (w1 - v)) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hmain' := hθmain _ hfpol1
  have hz1e : zOf e1 e2 (w1 - v)
      = ((‖zOf f1 f2 (w1 - v)‖ : ℝ) : ℂ) * Complex.exp
        ((Complex.arg (zOf f1 f2 (w1 - v)) + Complex.arg u) * I) := by
    show (w1 - v : V3) ⬝ᵥ e1 + (w1 - v : V3) ⬝ᵥ e2 * I = _
    rw [hu (w1 - v),
      show ((w1 - v : V3) ⬝ᵥ f1) + (w1 - v : V3) ⬝ᵥ f2 * I
        = zOf f1 f2 (w1 - v) from rfl]
    conv_lhs => rw [hue, hfpol1]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hz2e : zOf e1 e2 (w2 - v)
      = ((‖zOf f1 f2 (w2 - v)‖ : ℝ) : ℂ) * Complex.exp
        ((Complex.arg (zOf f1 f2 (w1 - v)) + θ + Complex.arg u) * I) := by
    show (w2 - v : V3) ⬝ᵥ e1 + (w2 - v : V3) ⬝ᵥ e2 * I = _
    rw [hu (w2 - v),
      show ((w2 - v : V3) ⬝ᵥ f1) + (w2 - v : V3) ⬝ᵥ f2 * I
        = zOf f1 f2 (w2 - v) from rfl]
    conv_lhs => rw [hue, hmain']
    rw [mul_left_comm, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hr1 : 0 < ‖zOf f1 f2 (w1 - v)‖ := norm_pos_iff.mpr hzf1
  have hr2 : 0 < ‖zOf f1 f2 (w2 - v)‖ := norm_pos_iff.mpr hzf2
  have hz1e' : zOf e1 e2 (w1 - v)
      = ‖zOf f1 f2 (w1 - v)‖ * Complex.exp
        (((Complex.arg (zOf f1 f2 (w1 - v)) + Complex.arg u : ℝ) : ℂ) * I) := by
    rw [hz1e]
    congr 1
    congr 1
    push_cast
    ring
  have hz2e' : zOf e1 e2 (w2 - v)
      = ‖zOf f1 f2 (w2 - v)‖ * Complex.exp
        (((Complex.arg (zOf f1 f2 (w1 - v)) + θ + Complex.arg u : ℝ) : ℂ) * I) := by
    rw [hz2e]
    congr 1
    congr 1
    push_cast
    ring
  have hrep1 := rep_of_zOf he hax hwv w1
    (Complex.arg (zOf f1 f2 (w1 - v)) + Complex.arg u) ‖zOf f1 f2 (w1 - v)‖ hz1e'
  have hrep2 := rep_of_zOf he hax hwv w2
    (Complex.arg (zOf f1 f2 (w1 - v)) + θ + Complex.arg u) ‖zOf f1 f2 (w2 - v)‖ hz2e'
  refine ⟨Complex.arg (zOf f1 f2 (w1 - v)) + Complex.arg u,
    ‖zOf f1 f2 (w1 - v)‖, ‖zOf f1 f2 (w2 - v)‖, ?_, ?_, hr1, hr2⟩
  · rw [show ((w1 - v : V3) ⬝ᵥ f3) = ((w1 - v : V3) ⬝ᵥ e3) from by rw [he3f]]
    exact hrep1
  · rw [show ((w2 - v : V3) ⬝ᵥ f3) = ((w2 - v : V3) ⬝ᵥ e3) from by rw [he3f],
      show Complex.arg (zOf f1 f2 (w1 - v)) + Complex.arg u + θ
        = Complex.arg (zOf f1 f2 (w1 - v)) + θ + Complex.arg u from by ring]
    exact hrep2

/-- AzimSpec 见证唯一（flyspeck.ml AZIM_UNIQUE 的角色）。 -/
theorem azimSpec_unique (hwv : w ≠ v)
    (hθ : AzimSpec v w w1 w2 θ) (hθ' : AzimSpec v w w1 w2 θ') : θ = θ' := by
  unfold AzimSpec at hθ hθ'
  obtain ⟨hb0, hb1, h1v, h2v, hframes⟩ := hθ
  obtain ⟨hb0', hb1', h1v', h2v', hframes'⟩ := hθ'
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (w - v) (sub_ne_zero.mpr hwv)
  have hax : (w - v : V3) = dist w v • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframes f1 f2 f3 hon hax hwv
  obtain ⟨ψ', r1', r2', hrep1', hrep2', hr1', hr2'⟩ := hframes' f1 f2 f3 hon hax hwv
  have hz1 : zOf f1 f2 (w1 - v) = r1 * Complex.exp (ψ * I) := zOf_of_rep hon hax hrep1
  have hz1' : zOf f1 f2 (w1 - v) = r1' * Complex.exp (ψ' * I) := zOf_of_rep hon hax hrep1'
  have hz2 : zOf f1 f2 (w2 - v) = r2 * Complex.exp ((ψ + θ) * I) := by
    have h := zOf_of_rep hon hax hrep2
    rw [h]
    congr 1
    congr 1
    push_cast
    ring
  have hz2' : zOf f1 f2 (w2 - v) = r2' * Complex.exp ((ψ' + θ') * I) := by
    have h := zOf_of_rep hon hax hrep2'
    rw [h]
    congr 1
    congr 1
    push_cast
    ring
  have hnE : ∀ t : ℝ, ‖Complex.exp (t * I)‖ = 1 := by
    intro t
    rw [Complex.norm_exp,
      show ((t : ℂ) * Complex.I).re = 0 from by simp [Complex.mul_re],
      Real.exp_zero]
  have key1 : r1 = r1' := by
    have e1 : ‖zOf f1 f2 (w1 - v)‖ = r1 := by
      rw [hz1, Complex.norm_mul, hnE, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr1, mul_one]
    have e2 : ‖zOf f1 f2 (w1 - v)‖ = r1' := by
      rw [hz1', Complex.norm_mul, hnE, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr1', mul_one]
    rw [← e1, e2]
  have key2 : r2 = r2' := by
    have e1 : ‖zOf f1 f2 (w2 - v)‖ = r2 := by
      rw [hz2, Complex.norm_mul,
        show ((ψ : ℂ) + (θ : ℂ)) * Complex.I = ((ψ + θ : ℝ) : ℂ) * Complex.I from by
          push_cast; ring,
        hnE (ψ + θ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2, mul_one]
    have e2 : ‖zOf f1 f2 (w2 - v)‖ = r2' := by
      rw [hz2', Complex.norm_mul,
        show ((ψ' : ℂ) + (θ' : ℂ)) * Complex.I = ((ψ' + θ' : ℝ) : ℂ) * Complex.I from by
          push_cast; ring,
        hnE (ψ' + θ'), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2', mul_one]
    rw [← e1, e2]
  have hee1 : Complex.exp (ψ * I) = Complex.exp (ψ' * I) := by
    have hc : ((r1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr1.ne'
    refine mul_left_cancel₀ hc ?_
    have := hz1.symm.trans hz1'
    rwa [← key1] at this
  have hee2 : Complex.exp ((ψ + θ) * I) = Complex.exp ((ψ' + θ') * I) := by
    have hc : ((r2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr2.ne'
    refine mul_left_cancel₀ hc ?_
    have := hz2.symm.trans hz2'
    rwa [← key2] at this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hee1
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hee2
  have hpsiI : ψ * I = (ψ' + (n:ℝ) * (2 * Real.pi)) * I := by
    rw [hn]
    push_cast
    ring
  have hpsi : ψ = ψ' + (n:ℝ) * (2 * Real.pi) := by
    have hc2 : ((ψ : ℝ) : ℂ) * Complex.I
        = ((ψ' + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      rw [hpsiI]
      push_cast
      ring
    have hc3 : ((ψ : ℝ) : ℂ) = ((ψ' + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
      mul_right_cancel₀ Complex.I_ne_zero hc2
    exact_mod_cast hc3
  have hsumI : (ψ + θ) * I = (ψ' + θ' + (m:ℝ) * (2 * Real.pi)) * I := by
    rw [hm]
    push_cast
    ring
  have hsum : ψ + θ = ψ' + θ' + (m:ℝ) * (2 * Real.pi) := by
    have hc2 : (((ψ + θ : ℝ) : ℂ)) * Complex.I
        = ((ψ' + θ' + (m:ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      rw [hsumI]
      push_cast
      ring
    have hc3 : ((ψ + θ : ℝ) : ℂ)
        = ((ψ' + θ' + (m:ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
      mul_right_cancel₀ Complex.I_ne_zero hc2
    exact_mod_cast hc3
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hk : θ - θ' = 2 * Real.pi * ((m - n : ℤ) : ℝ) := by
    rw [hpsi] at hsum
    push_cast
    linarith
  have hzero : (m - n : ℤ) = 0 := by
    rcases Int.lt_trichotomy (m - n) 0 with hneg | heq | hpos
    · exfalso
      have h1 : (m - n : ℤ) ≤ -1 := by omega
      have hle : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h1
      have hprod : 2 * Real.pi * ((m - n : ℤ) : ℝ) ≤ -2 * Real.pi := by
        have hmul := mul_le_mul_of_nonneg_right hle h2pi.le
        linarith
      linarith [hk, hprod, hb0, hb1, hb0', hb1']
    · exact heq
    · exfalso
      have h1 : (m - n : ℤ) ≥ 1 := by omega
      have hge : ((m - n : ℤ) : ℝ) ≥ 1 := by exact_mod_cast h1
      have hprod : 2 * Real.pi * ((m - n : ℤ) : ℝ) ≥ 2 * Real.pi := by
        have hmul := mul_le_mul_of_nonneg_right hge h2pi.le
        linarith
      linarith [hk, hprod, hb0, hb1, hb0', hb1']
  rw [hzero] at hk
  norm_num at hk
  linarith

/-- 非退化情形下 azim 由 spec 决定（flyspeck.ml SELECT_CONV 的角色）。 -/
theorem azim_eq_of_spec (h1 : ¬ Collinear3 v w w1) (h2 : ¬ Collinear3 v w w2)
    {θ : ℝ} (hθ : AzimSpec v w w1 w2 θ) : azim v w w1 w2 = θ := by
  have hwv : w ≠ v := fun he => h1 (collinear3_of_eq he)
  show (if Collinear3 v w w1 ∨ Collinear3 v w w2 then (0:ℝ)
      else Classical.epsilon (AzimSpec v w w1 w2)) = θ
  rw [if_neg (by rintro (h | h); exacts [h1 h, h2 h])]
  exact azimSpec_unique hwv (Classical.epsilon_spec (azimSpec_exists h1 h2)) hθ

end Kepler.Geom
