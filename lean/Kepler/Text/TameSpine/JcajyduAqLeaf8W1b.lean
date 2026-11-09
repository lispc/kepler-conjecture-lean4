/-
  JcajyduAqLeaf8W1b — AQ8 波 1b：`parts_f_betwn_pure` + `uniq_fst_betwn_parts`。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① aqs_partsFBetwnPure      AQ8.hl:399（63 行）
  │    `parts L (betwn (find_face L x) l'y l'z) =
  │     MAP (\x. [x]) (betwn (find_face L x) l'y l'z)`（窗口每 part 单点）
  │ ② aq8w1_uniqFstBetwnParts  AQ8.hl:462（68 行）
  │    `uniq (MAP (FST o HD) (parts L (betwn …)))`
  └────────────────────────────────────────────────────────────────

  ┌─ 命名（编排者规则）───────────────────────────────────────────
  │ `parts_f_betwn_pure` 跨叶消费者实测：AQ13.hl:252（+ AQ8 自身）；
  │ ⇒ 中立名 `aqs_`。`uniq_fst_betwn_parts` 仅 AQ8（8 处）⇒ `aq8w1_`。
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全 2 名；全导入闭包负探针 probe_aq8w1b.log）─────
  │ ① 目标名 2 个全 Unknown（import 到 JcajyduAqLeaf8W1a + 内容面显式
  │    import TameList33/Leaf10/Split1B/TameList6/ZIndexf/ZUnlock/
  │    BetwnBase/TameList7/TameList14/TameCorrCard；AGENTS §7.1 #18）。
  │ ② 两件本身零命中；但**引擎全在库且标准三**（probe_aq8w1b.log）：
  │    - `partsImpure`（TameList33:109）= HOL `parts_impure`（tame_list.hl:11369）
  │      `(∀x∈f, x=LAST f ∨ next_el f x ≠ f_list L (e_list x)) ∧ uniq f
  │       ⇒ parts L f = MAP (\x.[x]) f`；
  │    - `aq10_eqMemNextElLast`（Leaf10:137）= HOL `EQ_MEM_NEXT_EL_LAST`
  │      （AQ4.hl:60）；
  │    - `aq10_nextElBetwnSame`（Leaf10:102）= HOL `next_el_betwn_same`
  │      （NCVIBWU.hl:131）；
  │    - `fListInjDarts`（Split1B:117）= HOL `F_LIST_INJ`（AQ23.hl:210）；
  │    - `isRestrictedEListNondeg`（TameList6:591）edge 非退化；
  │    - `uniqBetwn`/`fListInjDarts`/`faceTableSubset`/`memHypermapOfListNode`/
  │      `simpleHypermapList` 均在册。
  │ ③ 本批**直接消费 IsMarked 解禁后的常态件**（无 condition 槽绕行；
  │    `qrdyxyjList` 未用，本批不需要 IsMarked 证人）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① `betwn` ↦ `between`；`find_face L x` ↦ `findFaceDarts L x`。
  │ ② `LAST f`（HOL）↦ `getLast!`（Lean；窗口非空由 d ∈ 窗口 保证）。
  │ ③ `MAP (\x. [x])` ↦ `List.map (fun d => [d])`（逐字）。
  │ ④ `FST o HD` ↦ `fun q => q.head!.1`（parts 的成员非空；HD ↦ head!）。
  │ ⑤ `good_list`/`good_list_nodes`/`marked_list` ↦ 显式 `hL`/`hgn`/`hm`；
  │    `all uniq L` 由 `hm.1.1` + `isRestrictedAllUniq` 内部导出。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 逐句）─────────────────────────────────────────────
  │ parts_f：窗口 W = betwn f y z。目标形式 = `partsImpure`；辅助件
  │ `∀d∈W, d = LAST W ∨ next_el W d ≠ f_list(e_list d)`：
  │ 反设 `next_el W d = f_list (e_list d)`。d ≠ LAST W ⇒
  │ `EQ_MEM_NEXT_EL_LAST` 给 `next_el f d ∈ W`，`next_el_betwn_same` 给
  │ `next_el W d = next_el f d`，故 `next_el f d = f_list (e_list d)`；
  │ 又 `f_list d = next_el (find_face d) d = next_el f d`（面相等），
  │ 于是 `f_list d = f_list (e_list d)`，`F_LIST_INJ` 给 `d = e_list d`，
  │ 撞 `is_restricted_e_list_nondeg`。
  │ uniq_fst：parts_f 改写后 `MAP (FST o HD) (MAP (\x.[x]) W) = MAP FST W`；
  │ `uniq_map` 化归逐点单射：u,v∈W 同 FST ⇒ 同 node（`MEM_hypermap_of_list_node`）
  │ + 同 face（面相等 + `faceTableSubset`）⇒ Simple 的 `node ∩ face = {u}`
  │ 塌出 u = v。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件前缀见命名节，私件 `aq8w1_`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.TameList33
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList7
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameCorrCard

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl
  mem_darts_of_mem_findFace findFaceDarts_nodup)

/-! ## §0 私件：`getLast! = getLast`（非空） -/

/-- `l ≠ [] ⇒ l.getLast! = l.getLast h`（Leaf10F 同证重推导，
per-file-private 约定零共享）。 -/
private theorem aq8w1_getLast!_eq_getLast {l : List (ℕ × ℕ)} (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast_eq_getElem, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil h; omega)]
  simp

/-! ## §1 `parts_f_betwn_pure`（HOL AQ8.hl:399） -/

/-- HOL `parts_f_betwn_pure`（AQ8.hl:399）：窗口
`betwn (find_face L x) l'y l'z` 的每个 part 都是单点。 -/
theorem aqs_partsFBetwnPure (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    partsSpine L (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
      = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => [d]) := by
  set W := between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hWnd : W.Nodup := uniqBetwn hfnd hyf hzf hyz
  refine partsImpure L W ?_ hWnd
  intro d hd
  by_cases hlast : d = W.getLast!
  · exact Or.inl hlast
  · refine Or.inr ?_
    intro hcon
    have hdf : d ∈ findFaceDarts L x := betwnMem hd
    have hdD : d ∈ listOfDarts L := mem_darts_of_mem_findFace L hdf
    have heD : eList d ∈ listOfDarts L := goodListEList hL hdD
    have hface : findFaceDarts L d = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 hdf
    have hgl := aq8w1_getLast!_eq_getLast (l := W) (List.ne_nil_of_mem hd)
    have hlastne : W.getLast (List.ne_nil_of_mem hd) ≠ d := by
      intro h
      exact hlast (h.symm.trans hgl.symm)
    have hnextW : nextEl (findFaceDarts L x) d ∈ W :=
      (aq10_eqMemNextElLast hyz hyf hzf hd hfnd).mpr hlastne
    have hsame := aq10_nextElBetwnSame hyz hyf hzf hd hnextW hfnd
    have hnextf : nextEl (findFaceDarts L x) d = fList L (eList d) :=
      hsame.symm.trans hcon
    have hfd : fList L d = nextEl (findFaceDarts L x) d :=
      congrArg (fun s => nextEl s d) hface
    have hfEq : fList L d = fList L (eList d) := hfd.trans hnextf
    have hdEq : d = eList d := (fListInjDarts L hL hdD heD).mp hfEq
    exact isRestrictedEListNondeg hL hm.1.1 hdD hdEq.symm

/-! ## §2 `uniq_fst_betwn_parts`（HOL AQ8.hl:462） -/

/-- HOL `uniq_fst_betwn_parts`（AQ8.hl:462）：
`uniq (MAP (FST o HD) (parts L (betwn …)))`。 -/
theorem aq8w1_uniqFstBetwnParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ((partsSpine L (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))).map
      (fun q => q.head!.1)).Nodup := by
  set W := between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hparts : partsSpine L W = W.map (fun d => [d]) :=
    aqs_partsFBetwnPure L hL hgn hm hf
  rw [hparts]
  have hmap : ((W.map (fun d => [d])).map (fun q => q.head!.1)) =
      W.map (fun d => d.1) := by
    simp only [List.map_map]
    rfl
  rw [hmap]
  have hnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hWnd : W.Nodup := uniqBetwn hfnd hpp.1 hpp.2.1 hyz
  refine (List.nodup_map_iff_inj_on hWnd).mpr ?_
  intro u hu v hv heq
  have huF : u ∈ findFaceDarts L x := betwnMem hu
  have hvF : v ∈ findFaceDarts L x := betwnMem hv
  have huD : u ∈ listOfDarts L := mem_darts_of_mem_findFace L huF
  have hvD : v ∈ listOfDarts L := mem_darts_of_mem_findFace L hvF
  have hfv : findFaceDarts L v = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hvF
  have hnode : u ∈ (hypermapOfList L hL).node v :=
    (memHypermapOfListNode hL hgn hvD).mpr ⟨heq.symm, huD⟩
  have huFv : u ∈ findFaceDarts L v := by rw [hfv]; exact huF
  have hface : u ∈ (hypermapOfList L hL).face v :=
    Kepler.Text.TameCorrCard.faceTableSubset hL hvD huFv
  have hsimple := simpleHypermapList L hL hgn hunL
  have hvD' : v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hvD
  have hinter : u ∈ (hypermapOfList L hL).node v ∩ (hypermapOfList L hL).face v :=
    ⟨hnode, hface⟩
  rw [hsimple v hvD'] at hinter
  exact Set.mem_singleton_iff.mp hinter

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aqs_partsFBetwnPure
#print axioms Kepler.Text.TameSpine.aq8w1_uniqFstBetwnParts
