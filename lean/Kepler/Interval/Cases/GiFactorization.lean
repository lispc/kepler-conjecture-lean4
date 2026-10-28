/-
  G_i 符号因式分解私件 (nli-prep-w2 任务件 1)。
  新增独立模块，不被既有文件 import；主仓 tracked 零改动。

  数学内容 (sympy 符号验证 + 本模块 `ring`/`norm_num` 全证, 零 sorry):
  · 单调性核 G_i := rhoX_i·deltaX − rhoX·deltaX_i，其中 rhoX_i = ∂rhoX/∂x_i、
    deltaX_i = ∂deltaX/∂x_i（x_i = y_i²，∂rad2X/∂y_i = 2·y_i·G_i/(4·deltaX²)）。
  · 六式分解——整族由四个齐三次因子 P, Q1, Q2, Q3 生成：
      G1 = -P*Q1    G2 = P*Q2     G3 = P*Q3
      G4 = Q2*Q3    G5 = -Q1*Q3   G6 = -Q1*Q2
    这是「打破 2^40 枚举壁垒」的结构件：盒上 G_i 定号证书化为两个三次因子的
    区间积（P·Q1 形），远紧于六次展开形的直接区间求值（依赖宽度灾难）。
  · 任务书目标「∀ y_i ≥ 2 (x_i ≥ 4): G_i > 0」被精确反例否定：
    x = (4,4,4,13/2,13/2,13/2) 处 deltaX = 1859/8 > 0 而 G1 = -28561/4 < 0
    （`ce_deltaX_pos` / `ce_G1_neg` / `ce_not_forall`）。如实停批，未放宽陈述。
  · 通道存活形态（条件式）：盒上 deltaX ≠ 0 ∧ G_i > 0 ⇒ rad2X 对 y_i 严格递增
    ⇒ 盒上 min/max 在端点。Python 精确有理采样（快照 gi_work/）表明 19 残叶
    全部采样点 G_i > 0（leaf0 的 min G1 ≈ +33492），通道在应用区点态为真。
-/
import Kepler.Text.IneqClosureDefs

namespace Kepler.Interval.Cases

open Kepler.Text

noncomputable section

/-! ## 偏导数定义（真形；与 sympy diff 全核）

注意：nli-prep-w1 `tools/mono.py` 的 `deltaX2..deltaX6` 手写展开缺项
（漏「其余两对 A,B,C 积」），其 G_i 区间数字不可用；本模块按下述真形重建。
repo 正本 `Kepler.Text.deltaX4/deltaX5` 与本文件 `dX4/dX5` 逐项一致（见下
pinning examples），即 w1 的工具 bug 不在 repo。 -/

/-- ∂rhoX/∂x1 = 2·x4·(B+C−A), A=x1x4, B=x2x5, C=x3x6. 与 x4 同形（`rhoX4t`）。 -/
def rhoX1t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x4 * (x2 * x5 + x3 * x6 - x1 * x4)

/-- ∂rhoX/∂x4. -/
def rhoX4t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x1 * (x2 * x5 + x3 * x6 - x1 * x4)

/-- ∂rhoX/∂x2 = 2·x5·(A+C−B). 与 x5 同形（`rhoX5t`）。 -/
def rhoX2t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x5 * (x1 * x4 + x3 * x6 - x2 * x5)

/-- ∂rhoX/∂x5. -/
def rhoX5t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x2 * (x1 * x4 + x3 * x6 - x2 * x5)

/-- ∂rhoX/∂x3 = 2·x6·(A+B−C). 与 x6 同形（`rhoX6t`）。 -/
def rhoX3t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x6 * (x1 * x4 + x2 * x5 - x3 * x6)

/-- ∂rhoX/∂x6. -/
def rhoX6t (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ := 2 * x3 * (x1 * x4 + x2 * x5 - x3 * x6)

/-- ∂deltaX/∂x1. -/
def dX1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x4 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 + x2 * x5 + x3 * x6
    - x3 * x5 - x2 * x6

/-- ∂deltaX/∂x2. -/
def dX2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x5 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x1 * x4 + x3 * x6
    - x3 * x4 - x1 * x6

/-- ∂deltaX/∂x3. -/
def dX3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x3 * x6 + x1 * x4 + x2 * x5
    - x2 * x4 - x1 * x5

/-- ∂deltaX/∂x4. -/
def dX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 + x2 * x5 + x3 * x6
    - x2 * x3 - x5 * x6

/-- ∂deltaX/∂x5. -/
def dX5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x2 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x1 * x4 + x3 * x6
    - x1 * x3 - x4 * x6

/-- ∂deltaX/∂x6. -/
def dX6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x3 * (x1 + x2 - x3 + x4 + x5 - x6) - x3 * x6 + x1 * x4 + x2 * x5
    - x1 * x2 - x4 * x5

/-- 与 repo 正本 `Kepler.Text.deltaX4`（sphere.hl:110 `delta_x4`）逐项一致。 -/
example : dX4 = Kepler.Text.deltaX4 := by
  funext x1 x2 x3 x4 x5 x6; simp only [dX4, deltaX4]; ring

/-- 与 repo 正本 `Kepler.Text.deltaX5`（sphere.hl `delta_x5`, 6-term 修正体）逐项一致。 -/
example : dX5 = Kepler.Text.deltaX5 := by
  funext x1 x2 x3 x4 x5 x6; simp only [dX5, deltaX5]; ring

/-! ## G_i 定义 -/

/-- G1 = ∂rad2X/∂x1 的分子核。 -/
def G1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX1t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX1 x1 x2 x3 x4 x5 x6

/-- G2 = ∂rad2X/∂x2 的分子核。 -/
def G2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX2t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX2 x1 x2 x3 x4 x5 x6

/-- G3 = ∂rad2X/∂x3 的分子核。 -/
def G3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX3t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX3 x1 x2 x3 x4 x5 x6

/-- G4 = ∂rad2X/∂x4 的分子核。 -/
def G4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX4t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX4 x1 x2 x3 x4 x5 x6

/-- G5 = ∂rad2X/∂x5 的分子核。 -/
def G5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX5t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX5 x1 x2 x3 x4 x5 x6

/-- G6 = ∂rad2X/∂x6 的分子核。 -/
def G6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  rhoX6t x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
    - rhoX x1 x2 x3 x4 x5 x6 * dX6 x1 x2 x3 x4 x5 x6

/-! ## 四个齐三次因子（sympy factor 展开形逐字移植） -/

/-- 公共因子 P（G1 的负因子；G2, G3 的正因子）。齐三次。 -/
def Pcub (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 ^ 2 - x1 * x4 * x5 - x1 * x4 * x6 - x2 * x4 * x5 + x2 * x5 ^ 2
    - x2 * x5 * x6 - x3 * x4 * x6 - x3 * x5 * x6 + x3 * x6 ^ 2 + 2 * x4 * x5 * x6

/-- 因子 Q1（G1 的负因子；G5, G6 的正因子）。齐三次。 -/
def Q1cub (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x2 * x4 + x1 * x3 * x4 - x1 * x4 ^ 2 - x2 ^ 2 * x5 - 2 * x2 * x3 * x4
    + x2 * x3 * x5 + x2 * x3 * x6 + x2 * x4 * x5 - x3 ^ 2 * x6 + x3 * x4 * x6

/-- 因子 Q2（G2, G4 的正因子；G6 的负因子）。齐三次。 -/
def Q2cub (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 ^ 2 * x4 - x1 * x2 * x5 - x1 * x3 * x4 + 2 * x1 * x3 * x5 - x1 * x3 * x6
    - x1 * x4 * x5 - x2 * x3 * x5 + x2 * x5 ^ 2 + x3 ^ 2 * x6 - x3 * x5 * x6

/-- 因子 Q3（G3, G4 的正因子；G5 的负因子）。齐三次。 -/
def Q3cub (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 ^ 2 * x4 - x1 * x2 * x4 - x1 * x2 * x5 + 2 * x1 * x2 * x6 - x1 * x3 * x6
    - x1 * x4 * x6 + x2 ^ 2 * x5 - x2 * x3 * x6 - x2 * x5 * x6 + x3 * x6 ^ 2

/-! ## 六式因式分解（本件主定理；`ring` 全证） -/

/-- **G1 = −P·Q1**。 -/
theorem G1_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G1 x1 x2 x3 x4 x5 x6 = -(Pcub x1 x2 x3 x4 x5 x6 * Q1cub x1 x2 x3 x4 x5 x6) := by
  simp only [G1, rhoX1t, dX1, rhoX, deltaX, Pcub, Q1cub]; ring

/-- **G2 = P·Q2**。 -/
theorem G2_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G2 x1 x2 x3 x4 x5 x6 = Pcub x1 x2 x3 x4 x5 x6 * Q2cub x1 x2 x3 x4 x5 x6 := by
  simp only [G2, rhoX2t, dX2, rhoX, deltaX, Pcub, Q2cub]; ring

/-- **G3 = P·Q3**。 -/
theorem G3_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G3 x1 x2 x3 x4 x5 x6 = Pcub x1 x2 x3 x4 x5 x6 * Q3cub x1 x2 x3 x4 x5 x6 := by
  simp only [G3, rhoX3t, dX3, rhoX, deltaX, Pcub, Q3cub]; ring

/-- **G4 = Q2·Q3**。 -/
theorem G4_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G4 x1 x2 x3 x4 x5 x6 = Q2cub x1 x2 x3 x4 x5 x6 * Q3cub x1 x2 x3 x4 x5 x6 := by
  simp only [G4, rhoX4t, dX4, rhoX, deltaX, Q2cub, Q3cub]; ring

/-- **G5 = −Q1·Q3**。 -/
theorem G5_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G5 x1 x2 x3 x4 x5 x6 = -(Q1cub x1 x2 x3 x4 x5 x6 * Q3cub x1 x2 x3 x4 x5 x6) := by
  simp only [G5, rhoX5t, dX5, rhoX, deltaX, Q1cub, Q3cub]; ring

/-- **G6 = −Q1·Q2**。 -/
theorem G6_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    G6 x1 x2 x3 x4 x5 x6 = -(Q1cub x1 x2 x3 x4 x5 x6 * Q2cub x1 x2 x3 x4 x5 x6) := by
  simp only [G6, rhoX6t, dX6, rhoX, deltaX, Q1cub, Q2cub]; ring

/-- 数值锚：正则四面体点 x=(4,…,4) 处 G1 = G4 = 4096。 -/
example : G1 4 4 4 4 4 4 = 4096 := by
  norm_num [G1_eq, Pcub, Q1cub]
example : G4 4 4 4 4 4 4 = 4096 := by
  norm_num [G4_eq, Q2cub, Q3cub]

/-! ## 反例：任务书目标式在给定域上不成立（如实停批件）

x = (4,4,4,13/2,13/2,13/2)（即 y = (2,2,2,√6.5,√6.5,√6.5)）处
deltaX = 1859/8 > 0 而 G1 = -28561/4 < 0。 -/

/-- 反例点上 deltaX > 0（物理域内）。 -/
theorem ce_deltaX_pos : (0:ℝ) < deltaX 4 4 4 ((13:ℝ)/2) ((13:ℝ)/2) ((13:ℝ)/2) := by
  norm_num [deltaX]

/-- 反例点上 G1 < 0。 -/
theorem ce_G1_neg : G1 4 4 4 ((13:ℝ)/2) ((13:ℝ)/2) ((13:ℝ)/2) < 0 := by
  norm_num [G1, rhoX1t, dX1, rhoX, deltaX]

/-- 任务书目标式「x_i ≥ 4 ∧ deltaX > 0 ⇒ G1 > 0」整体不成立。 -/
theorem ce_not_forall :
    ¬ (∀ x1 x2 x3 x4 x5 x6 : ℝ, 4 ≤ x1 → 4 ≤ x2 → 4 ≤ x3 → 4 ≤ x4 → 4 ≤ x5 → 4 ≤ x6 →
        0 < deltaX x1 x2 x3 x4 x5 x6 → 0 < G1 x1 x2 x3 x4 x5 x6) := by
  intro h
  have h4 : (4:ℝ) ≤ (13:ℝ)/2 := by norm_num
  exact absurd (h 4 4 4 ((13:ℝ)/2) ((13:ℝ)/2) ((13:ℝ)/2)
    le_rfl le_rfl le_rfl h4 h4 h4 ce_deltaX_pos)
    (by norm_num [G1, rhoX1t, dX1, rhoX, deltaX])

/-! ## 条件式骨架：「端点即极值」通道（deltaX ≠ 0 ∧ G_i > 0 的盒上单调性） -/

/-- 单项式帮件：`fun t => t * C` 的导数。 -/
theorem hasDerivAt_mulC (C x : ℝ) : HasDerivAt (fun t => t * C) C x :=
  hasDerivAt_mul_const C

/-- 单项式帮件：`fun t => t ^ 2 * C` 的导数。 -/
theorem hasDerivAt_sqC (C x : ℝ) : HasDerivAt (fun t => t ^ 2 * C) (2 * x * C) x := by
  simpa using (((hasDerivAt_id x).pow 2).mul_const C)

theorem deriv_rhoX_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deriv (fun t => rhoX t x2 x3 x4 x5 x6) x1 = rhoX1t x1 x2 x3 x4 x5 x6 := by
  have hshape : (fun t => rhoX t x2 x3 x4 x5 x6)
      = fun t => (t * (x4 * (x2 * (x5 * 2))) + t * (x4 * (x3 * (x6 * 2)))
        - t ^ 2 * (x4 * x4)) + ((x2 * x3) * (x5 * x6) * 2 - x2 ^ 2 * (x5 * x5)
        - x3 ^ 2 * (x6 * x6)) := by
    funext t; simp only [rhoX]; ring
  have h1 : HasDerivAt (fun t => t * (x4 * (x2 * (x5 * 2)))) (x4 * (x2 * (x5 * 2))) x1 :=
    hasDerivAt_mulC _ x1
  have h2 : HasDerivAt (fun t => t * (x4 * (x3 * (x6 * 2)))) (x4 * (x3 * (x6 * 2))) x1 :=
    hasDerivAt_mulC _ x1
  have h3 : HasDerivAt (fun t => t ^ 2 * (x4 * x4)) (2 * x1 * (x4 * x4)) x1 :=
    hasDerivAt_sqC _ x1
  have h4 : HasDerivAt (fun t => (x2 * x3) * (x5 * x6) * 2) 0 x1 :=
    hasDerivAt_const x1 ((x2 * x3) * (x5 * x6) * 2)
  have h5 : HasDerivAt (fun t => x2 ^ 2 * (x5 * x5)) 0 x1 :=
    hasDerivAt_const x1 (x2 ^ 2 * (x5 * x5))
  have h6 : HasDerivAt (fun t => x3 ^ 2 * (x6 * x6)) 0 x1 :=
    hasDerivAt_const x1 (x3 ^ 2 * (x6 * x6))
  rw [hshape]
  have hsum : HasDerivAt (fun t => (t * (x4 * (x2 * (x5 * 2))) + t * (x4 * (x3 * (x6 * 2)))
      - t ^ 2 * (x4 * x4)) + ((x2 * x3) * (x5 * x6) * 2 - x2 ^ 2 * (x5 * x5)
      - x3 ^ 2 * (x6 * x6)))
      ((x4 * (x2 * (x5 * 2))) + (x4 * (x3 * (x6 * 2))) - 2 * x1 * (x4 * x4) + (0 - 0 - 0)) x1 :=
    (h1.add h2).sub h3 |>.add (h4.sub h5 |>.sub h6)
  rw [hsum.deriv]
  simp only [rhoX1t]
  ring

theorem deriv_deltaX_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deriv (fun t => deltaX t x2 x3 x4 x5 x6) x1 = dX1 x1 x2 x3 x4 x5 x6 := by
  have hshape : (fun t => deltaX t x2 x3 x4 x5 x6)
      = fun t => (t ^ 2 * (-x4) + t * ((x4 * (x2 + (x3 + (x5 + x6) - x4)))
        + ((x2 * x5 + x3 * x6) - (x3 * x5 + x2 * x6))))
        + ((x2 * x5) * (-x2 + (x3 + x4 + (x6 - x5)))
        + (x3 * x6) * (-x3 + (x2 + x4 + (x5 - x6)))
        - ((x2 * x3) * x4 + (x4 * x5) * x6)) := by
    funext t; simp only [deltaX]; ring
  have h1 : HasDerivAt (fun t => t ^ 2 * (-x4)) (2 * x1 * (-x4)) x1 := hasDerivAt_sqC _ x1
  have h2 : HasDerivAt (fun t => t * ((x4 * (x2 + (x3 + (x5 + x6) - x4)))
      + ((x2 * x5 + x3 * x6) - (x3 * x5 + x2 * x6))))
      ((x4 * (x2 + (x3 + (x5 + x6) - x4))) + ((x2 * x5 + x3 * x6) - (x3 * x5 + x2 * x6))) x1 :=
    hasDerivAt_mulC _ x1
  have h3 : HasDerivAt (fun t => (x2 * x5) * (-x2 + (x3 + x4 + (x6 - x5)))
      + (x3 * x6) * (-x3 + (x2 + x4 + (x5 - x6)))
      - ((x2 * x3) * x4 + (x4 * x5) * x6)) 0 x1 :=
    hasDerivAt_const x1 (((x2 * x5) * (-x2 + (x3 + x4 + (x6 - x5)))
      + (x3 * x6) * (-x3 + (x2 + x4 + (x5 - x6)))
      - ((x2 * x3) * x4 + (x4 * x5) * x6)))
  rw [hshape]
  have hsum : HasDerivAt (fun t => (t ^ 2 * (-x4) + t * ((x4 * (x2 + (x3 + (x5 + x6) - x4)))
      + ((x2 * x5 + x3 * x6) - (x3 * x5 + x2 * x6))))
      + ((x2 * x5) * (-x2 + (x3 + x4 + (x6 - x5)))
      + (x3 * x6) * (-x3 + (x2 + x4 + (x5 - x6)))
      - ((x2 * x3) * x4 + (x4 * x5) * x6)))
      (2 * x1 * (-x4) + ((x4 * (x2 + (x3 + (x5 + x6) - x4)))
      + ((x2 * x5 + x3 * x6) - (x3 * x5 + x2 * x6))) + 0) x1 := (h1.add h2).add h3
  rw [hsum.deriv]
  simp only [dX1]
  ring

theorem deriv_deltaX4mul_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deriv (fun t => deltaX t x2 x3 x4 x5 x6 * 4) x1 = dX1 x1 x2 x3 x4 x5 x6 * 4 := by
  have hΔ' : DifferentiableAt ℝ (fun t => deltaX t x2 x3 x4 x5 x6) x1 := by
    simp only [deltaX]; fun_prop
  have heq : (fun t => deltaX t x2 x3 x4 x5 x6 * 4)
      = (fun t => (4:ℝ) * deltaX t x2 x3 x4 x5 x6) := funext fun t => by ring
  rw [heq, deriv_const_mul (c := (4:ℝ)) hΔ', deriv_deltaX_x1]
  ring

theorem deriv_rad2X_x1 (x1 x2 x3 x4 x5 x6 : ℝ)
    (hΔ : deltaX x1 x2 x3 x4 x5 x6 ≠ 0) :
    deriv (fun t => rad2X t x2 x3 x4 x5 x6) x1
      = G1 x1 x2 x3 x4 x5 x6 / (4 * deltaX x1 x2 x3 x4 x5 x6 ^ 2) := by
  have hf : DifferentiableAt ℝ (fun t => rhoX t x2 x3 x4 x5 x6) x1 := by
    simp only [rhoX]; fun_prop
  have hg : DifferentiableAt ℝ (fun t => deltaX t x2 x3 x4 x5 x6 * 4) x1 :=
    ((by simp only [deltaX]; fun_prop :
        DifferentiableAt ℝ (fun t => deltaX t x2 x3 x4 x5 x6) x1)).mul
      (differentiableAt_const (c := (4:ℝ)))
  have hne : (deltaX x1 x2 x3 x4 x5 x6 * 4) ≠ 0 := mul_ne_zero hΔ four_ne_zero
  have hrw : (fun t => rad2X t x2 x3 x4 x5 x6)
      = (fun t => rhoX t x2 x3 x4 x5 x6) / (fun t => deltaX t x2 x3 x4 x5 x6 * 4) := rfl
  rw [hrw, deriv_div hf hg hne, deriv_rhoX_x1, deriv_deltaX4mul_x1]
  field_simp [G1, mul_ne_zero hΔ four_ne_zero]
  simp only [G1]

/-- y-链式：∂/∂y1 rad2X(y1²,…,y6²) = y1·G1/(2·deltaX²)（= 2·y1·G1/(4·deltaX²)）。 -/
theorem deriv_rad2Xcomp_y1 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hΔ : deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≠ 0) :
    deriv (fun t => rad2X (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) y1
      = y1 * G1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          / (2 * deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ^ 2) := by
  have hsquare : deriv (fun t => t * t) y1 = 2 * y1 := by
    have h0 : HasDerivAt (fun t => t * t) (1 * y1 + y1 * 1) y1 :=
      (hasDerivAt_id y1).mul (hasDerivAt_id y1)
    rw [h0.deriv]
    ring
  have hcomp : DifferentiableAt ℝ (fun t => t * t) y1 := by fun_prop
  have h1 : DifferentiableAt ℝ
      (fun t => rad2X t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      (y1 * y1) := by
    have hsplit : (fun t => rad2X t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
        = (fun t => rhoX t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
            / (fun t => deltaX t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 4) := rfl
    rw [hsplit]
    exact DifferentiableAt.div
      (by simp only [rhoX]; fun_prop)
      (by simp only [deltaX]; fun_prop)
      (mul_ne_zero hΔ four_ne_zero)
  have hrw : (fun t => rad2X (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      = (fun t => rad2X t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ∘
        (fun t => t * t) := rfl
  rw [hrw, deriv_comp (h₂ := fun t => rad2X t (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    (h := fun t => t * t) y1 h1 hcomp,
    deriv_rad2X_x1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) hΔ, hsquare]
  ring

/-- **端点即极值（y1 通道，条件式）**：盒 [a,b]（a>0）上 deltaX ≠ 0 且 G1 > 0
点态成立时，rad2X(y1²,·) 在盒上严格递增 ⇒ 最小值在 a 端、最大值在 b 端。
（同构引理对 y4 取 G4 = Q2·Q3 > 0 形；y2, y3 取 G2 = P·Q2 / G3 = P·Q3 形；
y5, y6 取 G5 = −Q1·Q3 / G6 = −Q1·Q2 形，六式分解轮换。） -/
theorem strictMonoOn_rad2X_y1 (y2 y3 y4 y5 y6 : ℝ) (a b : ℝ) (ha : 0 < a)
    (hΔ : ∀ t ∈ Set.Icc a b, deltaX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≠ 0)
    (hG : ∀ t ∈ Set.Icc a b, 0 < G1 (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) :
    StrictMonoOn (fun t => rad2X (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      (Set.Icc a b) := by
  have hsplit : (fun t => rad2X (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      = fun t => rhoX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          / (deltaX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * 4) := rfl
  have hc1 : Continuous (fun t => rhoX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) := by
    simp only [rhoX]; fun_prop
  have hc2 : Continuous (fun t => deltaX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) := by
    simp only [deltaX]; fun_prop
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) ?_ ?_
  · rw [hsplit]
    exact ContinuousOn.div hc1.continuousOn (hc2.mul continuous_const).continuousOn
      (fun t ht => mul_ne_zero (hΔ t ht) four_ne_zero)
  · intro z hz
    rw [interior_Icc] at hz
    have hzIcc : z ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hz
    have ht0 : (0:ℝ) < z := lt_of_lt_of_le ha hzIcc.1
    rw [deriv_rad2Xcomp_y1 z y2 y3 y4 y5 y6 (hΔ z hzIcc)]
    exact div_pos (mul_pos ht0 (hG z hzIcc))
      (mul_pos zero_lt_two (sq_pos_of_ne_zero (hΔ z hzIcc)))

end

end Kepler.Interval.Cases

-- 探针：主定理应只依赖标准三公理（propext, Classical.choice, Quot.sound）。
#print axioms Kepler.Interval.Cases.G1_eq
#print axioms Kepler.Interval.Cases.G6_eq
#print axioms Kepler.Interval.Cases.ce_not_forall
#print axioms Kepler.Interval.Cases.strictMonoOn_rad2X_y1
