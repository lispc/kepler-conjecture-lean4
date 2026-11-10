/-
  Kepler.Text.TameSpine.Reduction3J5CoreFinal — tame-corr nb25：J5-6
  `betwn_corek_z_x` 头段两件（HOL `core_final_list` :95 / `core_final` :108）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ `core_final_list`：`good_list ∧ all darts f ∧ EdgeNondeg ∧ final f ∧ uniq f
  │   ⇒ core L f = MAP FST f`。证 = 在库 `finalListParts`（Reduction5BetwnBase:833，
  │   `parts L f = f.map (fun x => [x])`）+ `map_map` + 单元素 headD 定义级。
  │ `core_final`：`good_list ∧ marked_list L N r x ∧ final r ⇒ core L r = MAP FST r`。
  │   证 = marked 的 normal_list loopList 给 all-darts；hm.1 给 EdgeNondeg；
  │   `core_final_list` 收口。
  │ 查重：`all_rot` = `allRot`（Reduction4Idx:43）、`mem_core` = `memCore`
  │   （Reduction5McCore:40）——不重落。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList fList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart parts core finalList)

/-- **HOL `core_final_list`**（betwn_corek_z_x.hl:95）：
`good_list ∧ (∀x∈f, x∈darts) ∧ EdgeNondeg ∧ final f ∧ f.Nodup
⇒ core L f = f.map (fun d => d.1)`。 -/
theorem coreFinalList (L : fgraph ℕ) (hL : GoodList L) {f : List Dart}
    (hall : ∀ x ∈ f, x ∈ listOfDarts L)
    (hne : (Kepler.Text.TameLp.hypermapOfList L hL).EdgeNondegenerate)
    (hfin : finalList L f) (hnd : f.Nodup) :
    core L f = f.map (fun d => d.1) := by
  rw [show core L f = (parts L f).map (fun l => (l.headD (0, 0)).1) from rfl,
    Kepler.Text.Reduction5.finalListParts hL hall hne hfin hnd, List.map_map]
  rfl

/-- **HOL `core_final`**（betwn_corek_z_x.hl:108）：
`good_list ∧ marked_list L N r x ∧ final r ⇒ core L r = r.map (fun d => d.1)`。 -/
theorem coreFinal (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hfin : finalList L r) :
    core L r = r.map (fun d => d.1) := by
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hloop := hm.2.1.2.2.2.1 r hm.2.2.1
  exact coreFinalList L hL (fun d hd => (hloop d hd).1)
    hm.1.edgeNondegenerate hfin hnd

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.coreFinalList
#print axioms Kepler.Text.TameSpine.coreFinal
