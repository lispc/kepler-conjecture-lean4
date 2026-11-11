/-
  Kepler.Text.TameSpine.Reduction3J5PrevCoreX — tame-corr nb37：J5-6
  `prev_core_x`（HOL more_lemma2.hl:82，body 65 行）。

  陈述（HOL 逐字）：四前提下
  `prev_el (core L r) (FST (next_el (find_face L x) x)) = FST x`。

  路线（比 HOL 的 parts/MAP 中间面短，三条在库件直连）：
  - `(core L r).Nodup` ← `markedListUniqCore`（marked_list 第 5a 槽投影）；
  - 位置对接 `next_el (core L r) (FST x) = FST (next_el r x) = FST w`
    ← `nextCoreFst`（`fList L x = next_el (find_face L x) x` 定义级；
    marked_list 的 successor 槽给 `next_el r x = f_list L x`）；
  - 收口 ← `prevNextId`（`Seq2.prev_next_id`，`uniq s ⇒ prev_el s (next_el s x) = x`，
    对元素类型完全泛型，直接用在 `List ℕ` 的 `core L r` 上）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.Reduction5McCore

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.Reduction5 (Dart)

/-- **HOL `prev_core_x`**（more_lemma2.hl:82）：
`x` 的面后继在 `core L r` 上的前驱 = `x` 的首顶点。 -/
theorem prevCoreX (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ Kepler.Text.Reduction5.finalList L r) :
    Kepler.Assembly.prevEl (Kepler.Text.Reduction5.core L r)
      (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x).1 = x.1 := by
  have hcorend : (Kepler.Text.Reduction5.core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hxr : x ∈ r := hm.2.2.2.1
  -- marked_list successor 槽：`next_el r x = f_list L x`（后者定义级 = `next_el f x`）
  have hnext_eq : Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x
      = Kepler.Assembly.nextEl r x := hm.2.2.2.2.2.1.symm
  -- 位置对接
  have hnc : Kepler.Assembly.nextEl (Kepler.Text.Reduction5.core L r) x.1
      = (Kepler.Assembly.nextEl (Kepler.Assembly.findFaceDarts L x) x).1 := by
    rw [hnext_eq]
    exact Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf hxr hnext_eq
  -- `Seq2.prev_next_id` 收口
  rw [← hnc]
  exact Kepler.Text.Reduction5.prevNextId hcorend x.1

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.prevCoreX
