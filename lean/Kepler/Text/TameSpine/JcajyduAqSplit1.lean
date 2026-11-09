/-
  Kepler.Text.TameSpine.JcajyduAqSplit1 — E4a：split.1 支 f_last 的
  cycle 套件（高置信五件；E4b 交班见 DELIVERY）。

  件目：
  ① `lastRange`（HOL `LAST_UPT` AQ23.hl:242 的 Spine 形）：
     `(List.range' 1 (a - 1)).getLast! = a - 1`（a ≥ 2）——DEF-FIX 后
     nd 的末元指数 = sz-1 的载体；
  ② `nListMemDarts` / `nListPowEqNodeMapPow`（HOL Lebhirj
     `n_list_ext_n_list_power` 的 Spine 形，TameList6 折算 nListExt=nodeMap）：
     `(nList L)^k d = (nodeMap)^k d`（d ∈ darts）；
  ③ `nodeMapSymmEqFList`（HOL `inverse_n_list_ext` 环回）：
     `nodeMap.symm d = fList L (eList d)`（d ∈ darts）；
  ④ `nodeMapPowPredEqFList`（HOL `lemma_node_cycle` +
     `n_list_ext_n_list_power` 的终点合流）：`nodeMap^(node.ncard - 1) d
     = fList L (eList d)`（d ∈ darts，node.ncard ≥ 1）。

  **DEF-FIX 语义**（5628f300）：`nd x` 末元 = `(nList L)^[sz x.1 - 1] x`
  （HOL 对齐）——E4b 的 `LAST new1 = (nList L)^[sz-1] d1` 推导按此写。

  纪律：零 sorry/admit/native_decide/axiom；主仓树零写入（patch 交付）。
-/
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.JcajyduAqTowerBase

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl nextEl_mem_of_mem
  mem_darts_of_mem_findFace nodeMap_hypermapOfList edgeMap_hypermapOfList)

/-! ## §1 lastRange（HOL LAST_UPT 的 Spine 形，AQ23.hl:242） -/

/-- **HOL `LAST_UPT`**（AQ23.hl:242 `2<=a ==> LAST(upt 1 a) = PRE a`）的
DEF-FIX 后语义形：`(range' 1 (a-1)).getLast! = a - 1`（a ≥ 2；range' 的
末元指数即 sz-1）。 -/
theorem lastRange {a : ℕ} (ha : 2 ≤ a) :
    (List.range' 1 (a - 1)).getLast! = a - 1 := by
  have hne : List.range' 1 (a - 1) ≠ [] := by
    intro h0
    have hlen := List.length_range' (s := 1) (n := a - 1) (step := 1)
    rw [h0] at hlen
    simp at hlen
    omega
  have hlen : (List.range' 1 (a - 1)).length = a - 1 := List.length_range'
  rw [getLast!EqGetLast hne, List.getLast_eq_getElem hne]
  rw [List.getElem_range']
  omega

/-! ## §2 E4b 交班（设计已钉死，见 DELIVERY 续）

`nListMemDarts` / `nListPowEqNodeMapPow`（Lebhirj n_list_ext_n_list_power 形）/
`nodeMapSymmEqFList`（inverse_n_list_ext 环回）/ `nodeMapPowPredEqFList`
（lemma_node_cycle 终点合流）——四件的陈述与证词骨架已在 DELIVERY 续中
固定；E4b 一并落 + f_last 核心 + aq3Concl 收口。 -/

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.lastRange
