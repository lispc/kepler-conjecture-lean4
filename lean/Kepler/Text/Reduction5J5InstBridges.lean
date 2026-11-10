/-
  Kepler.Text.Reduction5J5InstBridges — J5-2 续段：`splitAt` / `rotateTo` 的
  Prod ↔ DecidableEq 实例桥（Dart 载体）。

  ┌─ 用途 ────────────────────────────────────────────────────────────
  │ 链侧 `indexf` 在定义时烘焙 `instBEqOfDecidableEq`（其定义为
  │ `[DecidableEq α]`，`List.idxOf` 取该实例）；而 Dart 语句里裸写的
  │ `splitAt`/`rotateTo` 默认解析为 `instBEqProd`。J5-1 波已落
  │ `nextElInstEq`/`idxOfInstEq`（Reduction5Kbwpbhq:86/:80）覆盖 `nextEl`/`idxOf`
  │ 两族；本文件补齐 `splitAt`/`rotateTo` 两座，使 `indexf` 相关的四个冻结件
  │ （indexf_indexl_hd / indexf_rotate_to / indexf_rotate_to_indexl /
  │ indexl_y_lt_z）可在同一实例世界内证明。
  └────────────────────────────────────────────────────────────────

  ┌─ 归属 ────────────────────────────────────────────────────────────
  │ 无 HOL 锚：这是实例桥（两实例的 `beq` 逐点相等 ⇒ 递归函数逐点相等），
  │ 仿 `nextElInstEq`（`unfold` + `idxOfInstEq`）/ `beqProdDerivedEq`
  │ （判定值逐点相等，`beq_iff_eq` 两支）的既有形。
  │ `splitAtRec` 对表归纳（HOL/Lean 同递归：首现切分，`bs` 为前缀累加器），
  │ `beqProdDerivedEq` 把 `a == c` 换成 DecEq 侧，再按同一条件分两支。
  │ `splitAt`/`rotateTo` 的定义都是 `splitAtRec c [] as` 的直包裹，
  │ 桥由 `splitAtRecInstEq` 一步得（`rfl` 级）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Graphs.ListAux
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.TameSpine.TameList54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

/-- `splitAtRec` 的跨实例逐点等式（对表归纳，`bs` 泛化）。 -/
theorem splitAtRecInstEq (c : Dart) (bs as : List Dart) :
    @Kepler.Graphs.splitAtRec Dart instBEqProd c bs as
      = @Kepler.Graphs.splitAtRec Dart instBEqOfDecidableEq c bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    show (if @BEq.beq Dart instBEqProd a c then (bs, as)
        else @Kepler.Graphs.splitAtRec Dart instBEqProd c (bs ++ [a]) as)
      = (if @BEq.beq Dart instBEqOfDecidableEq a c then (bs, as)
        else @Kepler.Graphs.splitAtRec Dart instBEqOfDecidableEq c (bs ++ [a]) as)
    rw [beqProdDerivedEq a c]
    by_cases h : @BEq.beq Dart instBEqOfDecidableEq a c = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact ih (bs ++ [a])

/-- `splitAt` 的跨实例逐点等式。 -/
theorem splitAtInstEq (c : Dart) (as : List Dart) :
    @Kepler.Graphs.splitAt Dart instBEqProd c as
      = @Kepler.Graphs.splitAt Dart instBEqOfDecidableEq c as :=
  splitAtRecInstEq c [] as

/-- 链侧 `rotateTo`（`Reduction3.rotateTo`）的跨实例逐点等式。 -/
theorem rotateToInstEq (vs : List Dart) (v : Dart) :
    @Kepler.Text.Reduction3.rotateTo Dart instBEqProd vs v
      = @Kepler.Text.Reduction3.rotateTo Dart instBEqOfDecidableEq vs v := by
  unfold Kepler.Text.Reduction3.rotateTo
  rw [splitAtInstEq]

/-- spine 侧 `rotateTo`（`TameSpine.rotateTo`）的跨实例逐点等式。 -/
theorem rotateToSpineInstEq (vs : List Dart) (v : Dart) :
    @Kepler.Text.TameSpine.rotateTo Dart instBEqProd vs v
      = @Kepler.Text.TameSpine.rotateTo Dart instBEqOfDecidableEq vs v := by
  unfold Kepler.Text.TameSpine.rotateTo
  rw [splitAtInstEq]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.splitAtRecInstEq
#print axioms Kepler.Text.Reduction5.splitAtInstEq
#print axioms Kepler.Text.Reduction5.rotateToInstEq
#print axioms Kepler.Text.Reduction5.rotateToSpineInstEq
