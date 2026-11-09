/-
  Kepler.Text.TameSpine.JcajyduAqLeaf11 — AQ11 叶（AQ1 兄弟叶）：`aq11Concl` 全式。

  目标（`JcajyduAqTowerBase.lean:300` `aq11Concl`，**陈述冻结**）：
  `∀ N r x, GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
     finalListSpine L (findListSpine (ntransSpine L N r x 1) (eList x))`
  = HOL `AQ11_concl`（AQ11.hl:229-:232）：marked_list 合取项 7
  （`final_list L (find_list N (e_list x))`）的 `ntrans` 迭代形。

  ┌─ 决定性捷径：合取 7 直取 ──────────────────────────────────────
  │ `MarkedListSpine`（TameList7:499；`MarkedListSpineFull` 的第 1 分量）
  │ 的**第 7 合取就是** `finalListSpine L (findListSpine N (eList x))`
  │ = 投影 `hm.1.2.2.2.2.2.2`。于是主证只剩两次改写：
  │   · final 支：`ntransId` 把 `ntrans 1` 折回 `N` ⇒ 目标即合取 7；
  │   · ¬final 支：`findList (ntrans 1) (eList x) = findList N (eList x)`
  │     （本文件 ⑤，吃 `aq1` 的 flatten Nodup）⇒ 目标即合取 7。
  │ HOL 原证（AQ11.hl:234-:277，44 行密排）同构，但未点破这个投影。
  │ 本捷径同时把 helper ③ 从 HOL 的 77 行压到 13 行（见下）。

  ┌─ 件表（HOL 锚 / 行数）─────────────────────────────────────────
  │ ① `aq11_elementInNtransSuc`（AQ9.hl:1031-:1081，50 行）：
  │    `f1 ∈ N → f1 ≠ r → f1 ∈ ntrans L N r x 1`。HOL 证体只实质消费
  │    `Tame_list.MEM3_replace`（tame_list.hl:583）⇒ Lean 10 行。
  │ ② `aq11_eListMemFlatten`（AQ11.hl:116-:188，73 行）：
  │    `eList x ∈ N.flatten`。路线：`w = nextEl (findFaceDarts L x) x ∈ r`
  │    （`aq10_nextMarkMemRTrans`）⇒ `w ∈ N.flatten`（`r ∈ N`）；
  │    `nList L w = eList x`（`findFaceDarts_congr_of_mem` + `prevEl_nextEl`）；
  │    `nList L w ∈ node w`（`nListPowEqNodeMapPow` + `pow_nodeMap_mem_node`，
  │    **不需要 HOL 的 FST/darts 路线**）；`NormalListSpine` 的 node 闭包收口。
  │ ③ `aq11_eListNotMemFinal`（AQ11.hl:39-:115，77 行）：
  │    `¬finalListSpine L r → eList x ∉ r`。HOL 走 FST/find_list/
  │    uniq_sublist 长链；Lean 用合取 7 反证：`eList x ∈ r` ⇒ `findListUniq`
  │    给 `findList N (eList x) = r` ⇒ 合取 7 即 `finalListSpine L r`，撞 ¬final。
  │ ④ `aq11_findListENotR`（AQ11.hl:189-:206，18 行）：
  │    `findListSpine N (eList x) ≠ r`（② 的 hit + ③）。
  │ ⑤ `aq11_findListEListConst`（AQ11.hl:207-:227，22 行）：
  │    `findList (ntrans 1) (eList x) = findList N (eList x)`
  │    （`findListSpineMemN` + `memFindList1` + `findListUniq` + ①，
  │    **吃 `aq1`** ⇒ 本叶是 AQ1 的第一个下游消费者）。
  │ ⑥ `aq11`（AQ11.hl:229-:277，49 行）：主证（合取 7 直取）。

  ┌─ DIFFERS（相对 HOL 的逐条记账）────────────────────────────────
  │ 1. ② 的 Lean 陈述**去掉 `~final_list L r` 前提**（无条件形）：
  │    HOL 两条 helper（77+73 行）的实质内容里该前提未被消费
  │    （node 闭包与 `next_mark_mem_r_trans` 均无条件）；本批只落无条件版，
  │    ③④ 在消费侧按需带 ¬final，结论面不变。
  │ 2. ① 的 Lean 陈述**无 `good_list`/`good_list_nodes`/`marked_list` 前提**
  │    （只留 `f1 ∈ N`、`f1 ≠ r`）：HOL 证体对三前提零消费
  │    （AQ9.hl:1031-:1081 只落 `MEM3_replace`）⇒ 更一般且更短。
  │ 3. ③ 走「合取 7 + `findListUniq`」而非 HOL 的 FST/`list_ext_power_in_darts`/
  │    `uniq_sublist_unique` 链（同结论，13 行 vs 77 行）。
  │ 4. 载体：`hL : GoodList L` / `hgn : GoodListNodesTl L hL` 显式入参
  │    （沿 Spine 约定；`hypermapOfList` 与 node 闭包需之）。**零新增定义、
  │    零陈述改动**（`aq11Concl` 槽冻结不动）。
  │ 5. 签名统一带 `hgn`：仅 ② 直接消费，③ 未消费（HOL 同），④⑤ 经 ②③ 传递。
  │ 6. 公理面：6 件全部 ⊆ `[propext, Classical.choice, Quot.sound]`、零 sorryAx
  │    （`aq1` 与 `aq10_nextMarkMemRTrans` 均标准三，见探针）。

  ┌─ 边界 ────────────────────────────────────────────────────────
  │ 本叶自包含（import 仅 `JcajyduAqLeaf1F` + `JcajyduAqLeaf10`）；
  │ 下游 = `transformAssumptionOfAq`（TowerBase:329）第 11 槽。
  └──────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqLeaf10

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts findFaceDarts GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem)

/-! ## §1 `element_in_ntrans_suc`（AQ9.hl:1031；ntrans 迭代的成员保持） -/

/-- **HOL `element_in_ntrans_suc`**（AQ9.hl:1031-:1081）的 Lean 一般形：
`f1 ∈ N` 且 `f1 ≠ r` ⇒ `f1 ∈ ntrans L N r x 1`。
final 支 `ntransId` 折回 `N`；¬final 支 `ntrans1` + `memReplaceOfNeMem`
（HOL `MEM3_replace` 的换血件，TowerBase:98）。 -/
theorem aq11_elementInNtransSuc (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) {f1 : List (ℕ × ℕ)}
    (hf1N : f1 ∈ N) (hf1r : f1 ≠ r) :
    f1 ∈ ntransSpine L N r x 1 := by
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin]; exact hf1N
  · rw [ntrans1 L N r x hfin]
    exact List.mem_append_left _ (memReplaceOfNeMem hf1r hf1N)

/-! ## §2 `e_list_mem_flatten`（AQ11.hl:116；`eList x` 落 `flatten N`） -/

/-- **HOL `e_list_mem_flatten`**（AQ11.hl:116-:188）的 Lean 无条件形：
`eList x ∈ N.flatten`（HOL 带 `~final_list L r`，证体未消费，见 DIFFERS 1）。
路线：`w = nextEl (findFaceDarts L x) x` 是 `x` 的面后继（`∈ r`，由
`aq10_nextMarkMemRTrans`），故 `w ∈ N.flatten`；`nList L w = eList x`
（面表同面 + `prevEl_nextEl`）；`nList L w ∈ node w`（`nList` 幂桥 +
`pow_nodeMap_mem_node`）；`normal_list` 的 node 闭包收口。 -/
theorem aq11_eListMemFlatten (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    eList x ∈ N.flatten := by
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hfd : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hwfd : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    nextEl_mem_of_mem hfd
  have hwd : nextEl (findFaceDarts L x) x ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hwfd
  have hwr : nextEl (findFaceDarts L x) x ∈ r :=
    aq10_nextMarkMemRTrans L hL hgn hm
  have hwfl : nextEl (findFaceDarts L x) x ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hwr⟩
  have hface : findFaceDarts L (nextEl (findFaceDarts L x) x) = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxd hwfd
  have hprev : prevEl (findFaceDarts L x) (nextEl (findFaceDarts L x) x) = x :=
    Kepler.Text.TameLp.prevEl_nextEl (findFaceDarts_nodup hL.1 x) hfd
  have hnlist : nList L (nextEl (findFaceDarts L x) x) = eList x := by
    rw [nList, hface, hprev]
  have hnode : nList L (nextEl (findFaceDarts L x) x) ∈
      (hypermapOfList L hL).node (nextEl (findFaceDarts L x) x) := by
    have hp : nList L (nextEl (findFaceDarts L x) x)
        = ((hypermapOfList L hL).nodeMap ^ 1) (nextEl (findFaceDarts L x) x) := by
      rw [← Function.iterate_one (nList L), nListPowEqNodeMapPow L hL hwd 1]
    rw [hp]
    exact (hypermapOfList L hL).pow_nodeMap_mem_node _ 1
  have hsub := hm.1.2.1.2.2.2.2 (nextEl (findFaceDarts L x) x) hwfl
  exact hnlist ▸ hsub hnode

/-! ## §3 `e_list_not_mem_final`（AQ11.hl:39；`eList x` 不吃 `r`） -/

/-- **HOL `e_list_not_mem_final`**（AQ11.hl:39-:115）的 Lean 换血形：
`¬finalListSpine L r → eList x ∉ r`。反证：若 `eList x ∈ r`，`findListUniq`
（flatten Nodup + r 成员）给 `findList N (eList x) = r`，而合取 7
正是 `finalListSpine L (findListSpine N (eList x))` ⇒ `finalListSpine L r`，
撞 ¬final。（HOL 的 FST/find_list/uniq_sublist 长链因此整段省掉。） -/
theorem aq11_eListNotMemFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    eList x ∉ r := by
  intro hmem
  have hfind : findListSpine N (eList x) = r :=
    findListUniq hm.1.2.1.1 hmem hm.1.2.2.1
  have h4 : finalListSpine L (findListSpine N (eList x)) := hm.1.2.2.2.2.2.2
  rw [hfind] at h4
  exact hf h4

/-! ## §4 `find_list_e_not_r`（AQ11.hl:189） -/

/-- **HOL `find_list_e_not_r`**（AQ11.hl:189-:206）：
`findListSpine N (eList x) ≠ r`（② 的 hit `eList x ∈ findList` + ③ 的反向假设）。 -/
theorem aq11_findListENotR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    findListSpine N (eList x) ≠ r := by
  intro h
  have hfl : eList x ∈ N.flatten := aq11_eListMemFlatten L hL hgn hm
  have hin : eList x ∈ findListSpine N (eList x) := memFindList1 hfl
  rw [h] at hin
  exact aq11_eListNotMemFinal L hL hgn hm hf hin

/-! ## §5 `find_list_e_list_const`（AQ11.hl:207；`ntrans` 不改变 `findList`） -/

/-- **HOL `find_list_e_list_const`**（AQ11.hl:207-:227）：
`findList (ntrans L N r x 1) (eList x) = findList N (eList x)`。
`findListSpineMemN`（命中行 ∈ N）+ ①（行不改名地进 `ntrans 1`）+
`memFindList1`（`eList x` 在命中行里）+ `findListUniq` 在 `ntrans 1` 的
flatten Nodup 上收口——**该 Nodup 即 `aq1`**（本叶是 AQ1 的首个下游消费者）。 -/
theorem aq11_findListEListConst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    findListSpine (ntransSpine L N r x 1) (eList x)
      = findListSpine N (eList x) := by
  have hfl : eList x ∈ N.flatten := aq11_eListMemFlatten L hL hgn hm
  have hmemN : findListSpine N (eList x) ∈ N := findListSpineMemN hfl
  have himg : findListSpine N (eList x) ∈ ntransSpine L N r x 1 :=
    aq11_elementInNtransSuc L N r x hmemN
      (aq11_findListENotR L hL hgn hm hf)
  have hin : eList x ∈ findListSpine N (eList x) := memFindList1 hfl
  exact findListUniq (aq1 L hL N r x hgn hm) hin himg

/-! ## §6 `AQ11_concl`（AQ11.hl:229；主证） -/

/-- **HOL `AQ11_concl`**（AQ11.hl:229-:232）真证：
`finalListSpine L (findListSpine (ntransSpine L N r x 1) (eList x))`。
final 支 `ntransId`；¬final 支 ⑤ 的 findList 不变式；两支都落到
`marked_list` 合取 7（`hm.1.2.2.2.2.2.2`）。 -/
theorem aq11 (L : fgraph ℕ) (hL : GoodList L) : aq11Concl L hL := by
  intro N r x hgn hm
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin]
    exact hm.1.2.2.2.2.2.2
  · rw [aq11_findListEListConst L hL hgn hm hfin]
    exact hm.1.2.2.2.2.2.2

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq11_elementInNtransSuc
#print axioms Kepler.Text.TameSpine.aq11_eListMemFlatten
#print axioms Kepler.Text.TameSpine.aq11_eListNotMemFinal
#print axioms Kepler.Text.TameSpine.aq11_findListENotR
#print axioms Kepler.Text.TameSpine.aq11_findListEListConst
#print axioms Kepler.Text.TameSpine.aq11
