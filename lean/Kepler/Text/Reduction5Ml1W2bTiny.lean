/-
  Kepler.Text.Reduction5Ml1W2bTiny — W2b 端点件（B5 的前置）：`s` 的首/末元。
  注：本波原计划 B2→B5；B2（s.Nodup）的 take/drop 索引路线与 B3/B4 的
  state-1 normalList 链未在本轮预算内完成，冻结表见 DELIVERY_ml2c。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5Ml1W2b
import Kepler.Text.TameSpine.TameList9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.ChainLists (markedList)

/-- **W2b 端点（HOL `last_cat` 两发）**：`s.getLast! = z1`。 -/
theorem ml1SLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (ml1S L N r x).getLast! = prevEl r (ztrans L N r x 0) := by
  unfold ml1S
  rw [Kepler.Text.TameSpine.lastCat (u := [nextEl r (ly L r x)]) (v := _) (by simp),
    Kepler.Text.TameSpine.lastCat (u := _) (v := [prevEl r (ztrans L N r x 0)])
      (by simp)]
  simp

/-- **W2b 端点（HOL `hd_cat`）**：`s.head! = y1`。 -/
theorem ml1SHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (ml1S L N r x).head! = nextEl r (ly L r x) := by
  unfold ml1S
  rfl

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1SLast
#print axioms Kepler.Text.Reduction5.ml1SHead
