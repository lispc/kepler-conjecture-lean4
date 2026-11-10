/-
  Kepler.Text.Reduction1W4d — J4 Wave W4 第三波（中）：`HKBGWJI`
  （HOL reduction1.hl:3825-:3934，flag_list ⇒ marked_list 的九合取装配）。

  载体沿 Reduction1W3a 文件头定案（chain）：`markedList`/`flagList`/`sFlagList`
  （ChainListsL2）、`normalList`（ChainListsL1）、`loopChoice2`（Reduction3Thm3）、
  `matchQuotientList`/`fgraphOfGraph`（Reduction3DefsLayer）。

  **陈述对账（逐字对 HOL 原文；零省前提、保 HOL 原序）**：十一前提；
  `good_list L` 本就是首前提。
  `all (\v. sizel (filter (MEM v) (quotient_list L N)) > 1) (flatten …)` ↦
  `∀ v ∈ qs.flatten, 1 < (qs.filter (fun q => decide (v ∈ q))).length`
  （与 `markedList` 第 5 合取同形，直喂）；`(r,x) = loop_choice2 g L N`
  保 HOL 的等式朝向；`~finalGraph g` ↦ `Graph.final g = false`。

  **查重记账（按 HOL 原名搜 docstring；消费件逐个核签名，经本文件编译实证）**：
  前任交接列的十三个小引理按 HOL 原名全部有命中。本文件对它们的处置：
  · **直接消费四件**（签名已核）：`mem_list_of_darts_quotient`（TameList10
    `memListOfDartsQuotient`，iff 形）、`parts_uniq_nonnil`（MoreLemma2Island3，
    chain 形）、`normal_list_parts_next_last`（MoreLemma2QuotientAlt，chain 形）、
    `final_dart_list_final_list`（Reduction1W3a）。
  · **一件 chain 形内联**：`flag_list_s_flag_list`。在库件（TameList58
    `flagListSFlagList`）是 Spine 载体，换到 chain 载体需 `sList = sListSpine`
    的桥等式（ChainBridgeParts `sFlagList_iff_sFlagListSpine` 把它当前提）。
    chain 形本身两行（首合取同形直投 + 尾合取 `List.mem_append_right`），
    证体内联，不引桥。
  · **其余八件不消费**（`mem_minimalVertex`/`minimalFace_nonnil`/
    `nextVertex_next_el`/`prev_el_list_pairs_eq`/`nonFinals_fgraph`/
    `MEM_LIST_DARTS`/`find_list_uniq`/`parts_flatten`；本文件未核其签名，
    亦无需核）：HOL 证体 :3844-:3920 把 `loop_choice` 展开后用它们手工推出
    `MEM r N /\ MEM x r`（经中间量 `MEM d (list_of_darts (fgraph g))`）与
    `x = LAST p /\ MEM p (parts L r)`。前者恰是已在库的 `loopChoiceProps`
    （T4TheoryA，HOL `loop_choice_props` reduction1.hl:3935——HOL 源里它排在
    HKBGWJI 之后，故 HKBGWJI 原证未能引它）的前三个合取，Lean 侧直接消费；
    后者由上列 `mem_list_of_darts_quotient` + `parts_uniq_nonnil` +
    `uniq_sublist_unique`（TameList6）取回。**证体路线偏离，陈述不受影响**。
  · 另消费 `simple_hypermap_all_uniq`（TameList14；HOL 原证用
    `simple_hypermap_uniq` 的 iff 形，同义）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.T4TheoryA
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2QuotientAlt
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts)
open Kepler.Graphs (fgraph Graph)
open Kepler.Text.ChainLists (normalList markedList flagList sFlagList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph loopChoice2)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine quotientListSpine)

/-! ## §0 私件 -/

/-- 非空表 `getLast!` 必是成员（树内多处私件同证；HOL `MEM_LAST`）。 -/
private theorem getLastMemAux {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h,
    Option.getD_some]
  exact List.getLast_mem h

/-! ## §1 `HKBGWJI`（reduction1.hl:3825-:3934） -/

/-- **HOL `HKBGWJI`**（reduction1.hl:3825-:3934）：
`good_list L /\ good_list_nodes L /\ is_restricted (hypermap_of_list L) /\
normal_list L N /\ ~(finalGraph g) /\ ~final_list L r /\
all uniq (quotient_list L N) /\
all (\v. sizel (filter (MEM v) (quotient_list L N)) > 1)
  (flatten (quotient_list L N)) /\
flag_list L N /\ match_quotient_list g L N /\ (r,x) = loop_choice2 g L N ==>
marked_list L N r x`。
九合取：1/2/5/8 = 前提直投；3/4 = `loop_choice_props`；`x = LAST p`、
`p ∈ parts L r`（`mem_list_of_darts_quotient` + `uniq_sublist_unique`）后
6 = `normal_list_parts_next_last`，7 = `flag_list` 尾合取（`~final_list L r`）+
`final_dart_list_final_list`；9 = `flag_list_s_flag_list`（chain 形内联）。 -/
theorem hkbgwji {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart} {x : Dart}
    {g : Graph} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hnl : normalList L hL N)
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hnfin : ¬ finalList L r)
    (hqu : ∀ s ∈ quotientList L N, s.Nodup)
    (hq1 : ∀ v ∈ (quotientList L N).flatten,
      1 < ((quotientList L N).filter (fun q => decide (v ∈ q))).length)
    (hflag : flagList L N)
    (hmq : matchQuotientList g L N)
    (hlc : (r, x) = loopChoice2 g L N) :
    markedList L hL N r x := by
  obtain ⟨hrN, hxr, hxfg, -⟩ :=
    Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hnl g hnf hqu hmq
      r x _ _ rfl rfl hlc.symm
  have hend : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.simpleHypermapAllUniq L hL hgn hres.simple
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  -- x = LAST p，p ∈ parts L r
  have hxq : x ∈ listOfDarts (quotientListSpine L N) := by
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, ← hmq.2]
    exact hxfg
  obtain ⟨p, r', hpS, hr'N, hxlast⟩ :=
    (Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnlS hend hall x).mp hxq
  have hp' : p ∈ parts L r' := by
    rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
    exact hpS
  obtain ⟨-, -, -, hpne, hpsub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hnl hr'N hp'
  have hxr' : x ∈ r' := by
    rw [hxlast]
    exact hpsub _ (getLastMemAux hpne)
  have hrr' : r = r' :=
    Kepler.Text.TameSpine.uniqSublistUnique N hnl.1 r hrN r' hr'N ⟨x, hxr, hxr'⟩
  subst hrr'
  unfold Kepler.Text.ChainLists.markedList
  refine ⟨hres, hnl, hrN, hxr, ⟨hqu, hq1⟩, ?_, ?_, fun _ => hflag, fun _ => ?_⟩
  · rw [hxlast]
    exact Kepler.Text.MoreLemma2QuotientAlt.normalListPartsNextLast L hL hnl hrN hp'
  · refine finalDartListFinalList hnl.1 ?_
    exact hflag.2 r p x
      (hxlast.trans (Kepler.Text.ChainBridge.getLast!_eq_getLastD p)) hp' hrN hnfin
  · unfold Kepler.Text.ChainLists.sFlagList
    exact ⟨hflag.1, fun r' q y hy hq hr' hfin _ =>
      List.mem_append_right _ (hflag.2 r' q y hy hq hr' hfin)⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.hkbgwji
