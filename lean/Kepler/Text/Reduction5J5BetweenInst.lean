/-
  Kepler.Text.Reduction5J5BetweenInst — BEq 实例桥第 5 例：`between`（Dart 载体）。

  用途：`parts_betwn_final`（HOL betwn_corek_z_x.hl:503）链侧化。链层陈述里裸写的
  `between` 在 Dart 上解析为 `instBEqProd`；而 `eqMemNextElLast`
  （Reduction3CoreSplitNormal:448）/ `nextElBetwnSame`（:491）的 `[DecidableEq α]`
  上下文把 `between` 解析为 `instBEqOfDecidableEq`。本桥把两实例世界缝合：
  `@between Dart instBEqProd = @between Dart instBEqOfDecidableEq`。

  路线：`between` 体只经 `splitAt`（两处）与 `List.contains`（分支条件）作用；
  `splitAtInstEq`（Reduction5J5InstBridges:58）已在库；`contains` 两实例都满足
  `LawfulBEq`，故都等于 `decide (c ∈ as)`（`List.contains_iff_mem` + `Bool.eq_iff_iff`）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5InstBridges

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

/-- `List.contains` 跨实例逐元素等式（两实例都反射成员关系，同归 `decide (c ∈ as)`）。 -/
theorem containsInstEq (c : Dart) (as : List Dart) :
    @List.contains Dart instBEqProd as c
      = @List.contains Dart instBEqOfDecidableEq as c := by
  have h1 : @List.contains Dart instBEqProd as c = decide (c ∈ as) := by
    rw [Bool.eq_iff_iff,
      @List.contains_iff_mem Dart instBEqProd inferInstance c as]
    exact decide_eq_true_iff.symm
  have h2 : @List.contains Dart instBEqOfDecidableEq as c = decide (c ∈ as) := by
    rw [Bool.eq_iff_iff,
      @List.contains_iff_mem Dart instBEqOfDecidableEq inferInstance c as]
    exact decide_eq_true_iff.symm
  rw [h1, h2]

/-- **`between` 跨实例逐点等式**（BEq 世界第 5 例桥）：
`@between Dart instBEqProd r a b = @between Dart instBEqOfDecidableEq r a b`。 -/
theorem betweenInstEq (r : List Dart) (a b : Dart) :
    @Kepler.Graphs.between Dart instBEqProd r a b
      = @Kepler.Graphs.between Dart instBEqOfDecidableEq r a b := by
  unfold Kepler.Graphs.between
  rw [splitAtInstEq a r]
  cases h : @Kepler.Graphs.splitAt Dart instBEqOfDecidableEq a r with
  | mk pre₁ post₁ =>
    dsimp only
    rw [containsInstEq b post₁, splitAtInstEq b post₁, splitAtInstEq b pre₁]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.containsInstEq
#print axioms Kepler.Text.Reduction5.betweenInstEq
