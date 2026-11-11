/-
  Kepler.Text.Reduction3Thm14a — J5-8 W1：`nfgtrans_suc`（reduction3.hl:4735-4770）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ :4735 `nfgtrans_suc` → `nfgtransSuc`（T14 main_induction 的直接上游；
  │   HOL 六前提 ⇒ `nfgtrans' … (SUC i) = subdiv_triple_step (nfgtrans' … i) …`）。
  └────────────────────────────────────────────────────────────────

  **路线（条件槽形两件直拼，零本体重写）**：
  · `nfgtransAdd`（T11，:4373）在 j=1 拆出 `nfgtrans' … (i+1)`；
  · `nfgtrans1`（T11，:4285）展开状态 i 的一步；
  · 两件的 `hfinal` 槽由 `finalListTransformCount`（在库；HOL
    `final_list_transform_count`）在 r 与状态 i 两侧各填一次 ⇒ 无条件形；
  · 状态平移 `ytrans/ztrans (ntrans i) (rtrans i) x 0 = ytrans/ztrans … i`
    由 `transAdd`（T1，`0+i=i` 支）供。
  · HOL 的 `sizel` ↦ `List.length`；`SUC i` ↦ `i + 1`。
  · Lean 惯例 +1 前提 `haq : AqiunppSlot L hL`（供 `finalListTransformCount`；
    装配时由 `aqiunpp` 无条件实例化）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm11
import Kepler.Text.Reduction5J5Termination

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph between)
open Kepler.Assembly (GoodList findFaceDarts)
open Kepler.Text.Reduction5
  (Dart ntrans rtrans ytrans ztrans transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **J5-8 W1：HOL `nfgtrans_suc`**（reduction3.hl:4735-4770）：
`nfgtrans' p … (SUC i) = subdiv_triple_step (nfgtrans' p … i)
 (FST ytrans i, FST ztrans i, |betwn …|)`。 -/
theorem nfgtransSuc (i : ℕ) (n : ℕ) (f : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hi : i + 1 ≤ transformCount L N r x) :
    nfgtrans' (n, f, g) L N r x (i + 1) =
      subdivTripleStep (nfgtrans' (n, f, g) L N r x i)
        ((ytrans L N r x i).1, (ztrans L N r x i).1,
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length) := by
  -- 终态 final（r 侧）
  have hkfinal : finalList L (rtrans L N r x (transformCount L N r x)) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm
      (t := transformCount L N r x) rfl
  have hile : i ≤ transformCount L N r x := by omega
  have hilt : i < transformCount L N r x := by omega
  -- 状态 i 侧 final（供 nfgtrans1 的 hfinal 槽）
  have hm1 : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hfinal1 : finalList L (rtrans L (ntrans L N r x i) (rtrans L N r x i) x
      (transformCount L (ntrans L N r x i) (rtrans L N r x i) x)) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm1
      (t := transformCount L (ntrans L N r x i) (rtrans L N r x i) x) rfl
  have hnf1 : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i hilt
  -- 两槽直拼
  rw [Kepler.Text.Reduction3.nfgtransAdd (n, f, g) L N r x i 1 hkfinal hile,
    Kepler.Text.Reduction3.nfgtrans1 (nfgtrans' (n, f, g) L N r x i)
      L (ntrans L N r x i) (rtrans L N r x i) x hfinal1 hnf1]
  -- 状态平移（transAdd @ (a := i, b := 0)）
  have ht := Kepler.Text.Reduction3.transAdd L N r x i 0
  have hy : ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0
      = ytrans L N r x i := by
    rw [← ht.2.2.1]; simp
  have hz : ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0
      = ztrans L N r x i := by
    rw [← ht.2.2.2]; simp
  rw [hy, hz]

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.nfgtransSuc
