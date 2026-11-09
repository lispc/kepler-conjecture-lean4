/-
  JcajyduAqLeaf8W3c — AQ8 波 3b-ii：snd 巨头 CASE 1 引擎之二
  （`uniq (MAP LAST (parts L s))` + 面内 `(FST∘HD)` 单射）。

  ┌─ 件目（先报后落；本波 2 件，无 W3b-ii-a/b 拆分需要）───────────
  │ ① aq8w3c_uniqLastParts    GSUBGOAL#4（AQ8.hl:1050 附近）：
  │    `uniq (MAP LAST (parts L s))`——`uniqParts` + `partsLastInj`
  │ ② aq8w3c_fstHdInjParts    GSUBGOAL#8（AQ8.hl:1190 附近）：
  │    `∀ u v ∈ parts L s, (HD u).1 = (HD v).1 → u = v`
  └────────────────────────────────────────────────────────────────

  ┌─ 依赖对表（先报；全部在库、标准三）───────────────────────────
  │ `partsLastInj`（TameList11:171）: `normal_list L N → r ∈ N →
  │   p ∈ parts L r → p' ∈ parts L r → p.getLast! = p'.getLast! → p = p'`
  │   —— 与 HOL `parts_last_inj` 逐字同形（只吃 LAST 相等）。
  │ `uniqParts`（TameList10:541）: `r.Nodup → r ≠ [] → (parts L r).Nodup`
  │   （HOL `uniq_parts`）。`List.nodup_map_iff_inj_on`（`uniq_map` 折算）。
  │ ② 侧：`memHypermapOfListNode`（TameList7:243，同 FST + 同 dart 集 ⇒ 同
  │   node）、`aq10_memFindFaceImpFacesEq`（同面）、`faceTableSubset`
  │   （TameCorrCard:137，面表 ⊆ face 轨道）、`simpleHypermapList`
  │   （TameList14:244，`node ∩ face = {d}`）、`uniqSublistUnique`
  │   （HOL `uniq_sublist_unique`，共享元 ⇒ 同 sublist）。
  └────────────────────────────────────────────────────────────────

  ┌─ 与编排者指示的偏差（如实报）─────────────────────────────────
  │ 指示「面内单射一支直接消费 `aqs_partsContiguousRefine`」。实测**不需要**：
  │ `§1` 的 HOL 路线用「同 node（`memHypermapOfListNode`）+ 同面
  │ （`aq10_memFindFaceImpFacesEq` + `faceTableSubset`）+ Simple
  │ （`simpleHypermapList`）塌出 `HD u = HD v`」，再用
  │ `uniqSublistUnique`（两 part 共享 head ⇒ 同一 part）收口；
  │ 「同 node ⇒ 同 part」与连续段细化都被绕开（比 HOL 更省）。
  │ ⇒ `aqs_partsContiguousRefine` 零消费，留给 GSUBGOAL#3 的无条件化。
  │ ② 的唯一载体语境槽：`hsface : ∀ a ∈ s, a ∈ findFaceDarts L x`
  │ （AQ8 应用侧：s ⊆ r，r 是面 x 的块；本波未落其推导，已记 UNRESOLVED）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `uniq` ↦ `Nodup`；`MAP LAST` ↦ `map (fun p => p.getLast!)`；
  │    `MAP (FST o HD)` ↦ `map (fun p => p.head!.1)`；
  │    `HD`/`LAST` ↦ `head!`/`getLast!`（parts 件非空）。
  │ ② `AQ_normal_list` ↦ `aqs_aqNormalList`（五塔接口槽 `h1..h5`，
  │    与 W1a 同口径；塔顶消去）。
  │ ③ `hsface` 为**显式载体语境槽**（非数学前提；AQ8 应用侧可导，推导待落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3c_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3b2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 `uniq (MAP LAST (parts L s))`（GSUBGOAL#4） -/

/-- **HOL GSUBGOAL#4**（AQ8.hl:1050 附近）：`uniq (MAP (LAST) (parts L s))`
——`parts L s` 的末元表无重。

HOL 路：`uniq_map` + `uniq_parts` 化归「末元相等 ⇒ part 相等」，即
`parts_last_inj`。`s ∈ ntrans … 1` 供 `normal_list`（五塔槽）与
`s.Nodup / s ≠ []`。 -/
theorem aq8w3c_uniqLastParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)} (hsN : s ∈ ntransSpine L N r x 1) :
    ((partsSpine L s).map (fun p => p.getLast!)).Nodup := by
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  have hsn : s.Nodup ∧ s ≠ [] := normalListUniqNonnil hnN hsN
  refine (List.nodup_map_iff_inj_on (uniqParts L hsn.1 hsn.2)).mpr ?_
  intro u hu v hv heq
  exact partsLastInj L hL hnN hsN hu hv heq

/-! ## §1 面内 `(FST∘HD)` 单射（GSUBGOAL#8） -/

/-- **HOL GSUBGOAL#8**（AQ8.hl:1190 附近）：`parts L s` 上 `(FST o HD)` 单射。

`u v ∈ parts L s`、`(HD u).1 = (HD v).1` ⇒ `HD v ∈ node (HD u)`
（`memHypermapOfListNode`）；两侧 `HD` 都在面 `findFaceDarts L x` 内
（`hsface` 载体槽）⇒ 同面（`aq10_memFindFaceImpFacesEq`）
⇒ `HD v ∈ face (HD u)`（`faceTableSubset`）⇒ `node ∩ face = {HD u}`
（`simpleHypermapList`）给 `HD v = HD u` ⇒ 两 part 共享 head
⇒ `uniqSublistUnique` 收口 `u = v`。 -/
theorem aq8w3c_fstHdInjParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)} (hsN : s ∈ ntransSpine L N r x 1)
    (hsface : ∀ a ∈ s, a ∈ findFaceDarts L x) :
    ∀ u ∈ partsSpine L s, ∀ v ∈ partsSpine L s,
      (u.head!).1 = (v.head!).1 → u = v := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  have hsn : s.Nodup ∧ s ≠ [] := normalListUniqNonnil hnN hsN
  intro u hu v hv heq
  have hune : u ≠ [] := partsAllNonnil L hsn.1 hsn.2 u hu
  have hvne : v ≠ [] := partsAllNonnil L hsn.1 hsn.2 v hv
  have hup : u.head! ∈ u := List.head!_mem_self hune
  have hvp : v.head! ∈ v := List.head!_mem_self hvne
  have huD : u.head! ∈ listOfDarts L := partsDarts L hnN hsN hu hup
  have hvD : v.head! ∈ listOfDarts L := partsDarts L hnN hsN hv hvp
  -- 同 node
  have hnode : v.head! ∈ (hypermapOfList L hL).node u.head! :=
    (memHypermapOfListNode hL hgn huD).mpr ⟨heq, hvD⟩
  -- 同面（载体槽 → 面相等）
  have huf : u.head! ∈ findFaceDarts L x :=
    hsface _ (memPartsImp L hsn.1 hsn.2 hu _ hup)
  have hvf : v.head! ∈ findFaceDarts L x :=
    hsface _ (memPartsImp L hsn.1 hsn.2 hv _ hvp)
  have hfin : v.head! ∈ findFaceDarts L (u.head!) := by
    rw [aq10_memFindFaceImpFacesEq hL.1 huf]
    exact hvf
  have hface : v.head! ∈ (hypermapOfList L hL).face u.head! :=
    Kepler.Text.TameCorrCard.faceTableSubset hL huD hfin
  -- Simple：node ∩ face = {HD u}
  have hsimple := simpleHypermapList L hL hgn hunL
  have hinter : v.head! ∈ (hypermapOfList L hL).node u.head!
      ∩ (hypermapOfList L hL).face u.head! := ⟨hnode, hface⟩
  rw [hsimple u.head! (List.mem_toFinset.mpr huD)] at hinter
  have hheadEq : v.head! = u.head! := Set.mem_singleton_iff.mp hinter
  -- 两 part 共享 head ⇒ 同一 part
  have hfl : (partsSpine L s).flatten.Nodup := by
    rw [partsFlatten L hsn.1 hsn.2]; exact hsn.1
  exact uniqSublistUnique (partsSpine L s) hfl u hu v hv
    ⟨u.head!, hup, by rw [← hheadEq]; exact hvp⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3c_uniqLastParts
#print axioms Kepler.Text.TameSpine.aq8w3c_fstHdInjParts
