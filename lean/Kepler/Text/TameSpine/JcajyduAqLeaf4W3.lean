/-
  Kepler.Text.TameSpine.JcajyduAqLeaf4W3 — AQ4 W3a（**引擎片**）：`s1 = new1.reverse ++ f1`
  行的 `loopListSpine` 所需三件。**`aq4_loopS1` 本体未收（§7 止损交边界，见 DELIVERY §3）。**

  `new1 = ((betwn (findFaceDarts L y) y z).map (ndSpine L)).flatten`、
  `f1 = [y1] ++ betwn r y1 z1 ++ [z1]`（`y = lYSpine L r x`、`z = lZSpine L N r x`、
  `y1 = nextEl r y`、`z1 = prevEl r z`）。目标 = 逐点 `d ∈ listOfDarts L ∧ oneStep d (nextEl s1 d)`。

  路线（W2 的规范形/`getLast` 两支照搬 + W1 的块引擎）：
  │ `new1.reverse` 用 `List.reverse_flatten` 写成**反转块**的 flatten
  │ `blocks' = (w.reverse.map (fun d => (ndSpine L d).reverse))`：
  │   · 块内元素（`x ≠ head block d`）：Cat2 + `la7_nextEl_reverse` +
  │     `aq4_prevElNdSpine` ⇒ nextEl = 前一幂，one_step 第二支
  │     （`nodeMap.symm x = nodeMap^(i-1) d`，`aq4_nodeMapSymmPow`）；
  │   · 块边界（`x = head block d = nList d`，且 `d ≠ head w`）：
  │     `aq4_nextElBlockLast` ⇒ nextEl = last block(prevEl w d)，one_step 由
  │     **`aq4_blockBoundaryStep`** 直接给（`prevEl f d = prevEl w d` 由 E1
  │     `aq4_prevElBetwnOfNeHead`）；
  │   · 行边界（`d = head w`，x 是 new1.reverse 末元）：nextEl = head f1 = y1，
  │     one_step 第一支（`x = eList y`、`y1 = fList (eList y)`，`nextRNotEqF`）。
  │ `f1` 段：`y1`（a1 空/非空二分）、a1 内部、a1 末、`z1`（行末）——同 W2 的弧配方，
  │ z1 的 nextEl = `new1.getLast!` = fList z1（`lastNew1EqFList` + `lastWindowEqEListZ1`）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf4W2

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem getD_eq_getElem_of_lt)

/-! ## §1 引擎补件（W3a 专用，公开） -/

/-- **块内后继**：`nextEl (ndSpine L d) ((nList)^[i] d) = (nList)^[i+1] d`
（`1 ≤ i ≤ sz-2`）。由 W1 的 `aq4_prevElNdSpine`（i+1 处）+ `nextEl_prevEl` 立得。 -/
theorem aq4_nextElNdSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts)
    (h2 : 2 ≤ (L.flatten.filter (fun t => decide (t = d.1))).length)
    {i : ℕ} (hi : 1 ≤ i) (hi2 : i ≤ (L.flatten.filter (fun t => decide (t = d.1))).length - 2) :
    nextEl (ndSpine L d) ((nList L)^[i] d) = (nList L)^[i + 1] d := by
  have hnd : (ndSpine L d).Nodup := aq1_ndSpineNodup L hL hgn hd h2
  have hmem : (nList L)^[i] d ∈ ndSpine L d := by
    rw [show ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun j => (nList L)^[j] d) from rfl]
    rw [List.mem_map]
    refine ⟨i, ?_, rfl⟩
    rw [List.mem_range']
    exact ⟨i - 1, by omega, by omega⟩
  have hmem' : (nList L)^[i + 1] d ∈ ndSpine L d := by
    rw [show ndSpine L d = (List.range' 1 ((List.filter (fun t => decide (t = d.1))
        (List.flatten L)).length - 1)).map (fun j => (nList L)^[j] d) from rfl]
    rw [List.mem_map]
    refine ⟨i + 1, ?_, rfl⟩
    rw [List.mem_range']
    exact ⟨i, by omega, by omega⟩
  have hprev := aq4_prevElNdSpine L hL hgn hd h2 (i := i + 1) (by omega) (by omega)
  have hstep := Kepler.Text.TameLp.nextEl_prevEl hnd hmem'
  rw [hprev] at hstep
  rw [show i + 1 - 1 = i from by omega] at hstep
  exact hstep

/-- **幂回绕的 symm 形**：`nodeMap.symm ((nodeMap)^i d) = nodeMap^(i-1) d`（`1 ≤ i`，
载体 `d ∈ darts`）。由 `pow_succ'` + `Equiv.symm_apply_apply` 直达。 -/
theorem aq4_nodeMapSymmPow (L : fgraph ℕ) (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ (hypermapOfList L hL).darts) {i : ℕ} (hi : 1 ≤ i) :
    (hypermapOfList L hL).nodeMap.symm (((hypermapOfList L hL).nodeMap ^ i) d)
      = ((hypermapOfList L hL).nodeMap ^ (i - 1)) d := by
  have hdL : d ∈ listOfDarts L := List.mem_toFinset.mp hd
  have hx : ((hypermapOfList L hL).nodeMap ^ i) d
      = ((hypermapOfList L hL).nodeMap ^ (i - 1 + 1)) d := by
    rw [show i - 1 + 1 = i from by omega]
  rw [hx, pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

/-- **`new1.reverse` 的反转块形**：
`((w.map (ndSpine L)).flatten).reverse = (w.reverse.map (fun d => (ndSpine L d).reverse)).flatten`。 -/
theorem aq4_new1RevForm (L : fgraph ℕ) (w : List (ℕ × ℕ)) :
    (((w.map (ndSpine L)).flatten).reverse)
      = (w.reverse.map (fun d => (ndSpine L d).reverse)).flatten := by
  rw [List.reverse_flatten, List.map_map, List.map_reverse]
  rfl

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq4_nextElNdSpine
#print axioms Kepler.Text.TameSpine.aq4_nodeMapSymmPow
#print axioms Kepler.Text.TameSpine.aq4_new1RevForm
