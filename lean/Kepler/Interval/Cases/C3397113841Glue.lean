/-
  P6-E 粘合引理（量产试点，案例 3397113841；本文件为手工样板，量产时由
  生成器随案例证书一并产出）。

  HOL 侧案例 3397113841
  （reference/flyspeck/text_formalization/nonlinear/ineq.hl:2056）：
  `delta4_y y1 y2 y3 y4 y5 y6 < &0`。生成器把 `<` 严格化为
  `0 - (展开式) > 0`，逐 def 内联进 `IExpr`（`C3397113841Expr`）。本引理把
  `evalReal` 的语义等回 155 定义闭包里的命名定义组合
  `delta4Y = yOfX deltaX4`（SphereKit.lean:126，`delta4_y` 的 Lean 镜像）。

  试点实证记录（2026-09-20，对量产粘合有直接指导意义）：
  - **纯 `rfl` 不成立**：`Dyadic.toReal ⟨0, 0⟩` 不是定义上的 `0`
    （`toReal = Rat.cast ∘ toRat`，经 `zpow`/`Rat.cast`，非定义可约）。
  - `simp only` 展开双侧后，两个多项式**逐节点语法相同**——关键侥幸是
    Lean 解析 `-x2 * x3` 为 `(-x2) * x3`（实证：parse-test），与生成器
    为 RPN `neg; mul` 发出的 `.mul (.neg ..) ..` 同构；唯一残差目标是
    顶层常量 `{m := 0, e := 0}.toReal - P = 0 - P`。
  - 加 `Dyadic.toReal_int, Int.cast_zero` 即闭合（一行 `simp only`）。
-/
import Kepler.Interval.Cases.C3397113841.Base
import Kepler.Text.SphereKit

namespace Kepler.Interval.Cases

open Kepler.Text

/-- **粘合引理**：G4 证书表达式的实数语义 = HOL 不等式
`delta4_y y1 … y6 < &0` 的（严格化）语义展开式 `0 - delta4Y y1 … y6`。 -/
theorem C3397113841_evalReal (ρ : Fin 6 → ℝ) :
    C3397113841Expr.evalReal ρ =
      0 - delta4Y (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  simp only [C3397113841Expr, IExpr.evalReal, delta4Y, yOfX, deltaX4,
    Dyadic.toReal_int, Int.cast_zero]

#print axioms C3397113841_evalReal

end Kepler.Interval.Cases
