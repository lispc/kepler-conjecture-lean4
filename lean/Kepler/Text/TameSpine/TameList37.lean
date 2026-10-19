/-
  Kepler.Text.TameSpine.TameList37 — B1 Tame_list 地基批 37：quotient 桥面 +
  iso 后续随收（tamespine-port-plan §4 批次表 B1 行；接续批 36 =
  TameList36.lean，批 36 终点 = HOL :11744（iso_list_cons 已落）；本批起点 =
  HOL :11747 `elements_of_list_quotient_list`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测；批 36 预记的 :11764 偏移 +1，
  实测 :11765（见下）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11747-:11944）：

  主件一：`elements_of_list_quotient_list` :11747-:11762
  `!L N. normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
  good_list L /\ all uniq L ==> elements_of_list (quotient_list L N) SUBSET
  elements_of_list L`
  ↦ `elementsOfListQuotientList`（真证，quotient 桥面章）。HOL 证体
  REWRITE[mem_list_of_elements;elements_of_list;SUBSET;IN_SET_OF_LIST] +
  证人 y + MATCH_MP_TAC list_of_darts_quotient_darts（tame_list.hl:9847，
  批 16 listOfDartsQuotientDarts 在库）。Lean 面逐点折算：SUBSET ↦
  Set.Subset intro 逐点；darts↔elements 桥面 = HOL mem_list_of_elements
  （list_hypermap-compiled.vhl:781 `MEM x (list_of_elements L) <=> ?y.
  MEM (x,y) (list_of_darts L)`）双向两私件——⇒ 向 `memElementsSubDarts`
  （证人 y = zip 第二槽 `(l.drop 1 ++ l.take 1)[i]`，即 x 的循环后继：
  x ∈ eraseDups·flatten → 某面 l → getElem 索引 → listPairs = zip l
  (drop 1 ++ take 1) 的 i 槽 pair 逐字取证人，零 rotate 换形）；⇐ 向
  `fstMemListOfElements`（批 16 私件 TameList16.lean:215 同证重推导——
  zip getElem 拆 FST + mem_flatten 回装）。桥链：memElementsSubDarts
  （quotient 面出 y）→ listOfDartsQuotientDarts（darts 降回 L 面，前件
  normal/edge-nondegenerate/good/uniq 四槽全数对位）→
  fstMemListOfElements（L 面 elements 收口）。

  主件二：`inj_on_quotient_list` :11765-:11780（批 36 预记 :11764，偏移
  +1 记档）
  `!phi L N. normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L)
  /\ good_list L /\ all uniq L /\ inj_on phi (elements_of_list L) ==>
  inj_on phi (elements_of_list (quotient_list L N))`
  ↦ `injOnQuotientList`（一行为，inj_on_subset + 前件复用随收形）。
  折算：inj_on ↦ Set.InjOn（批 1 惯例）；inj_on_subset ↦
  Set.InjOn.mono（t ⊆ s 向），子集槽即主件一。

  随收件一：`contour_list_hd_dart` :11831-:11839
  `!L h s. contour_list L (h::s) ==> MEM h (list_of_darts L)`
  ↦ `contourListHdDart`（一行为）。HOL LIST_INDUCT + contour_list_cons +
  MESON；Lean 面 s 两拆（nil/cons）经批 13 `contourListCons`
  （TameList13.lean:105）单元素/cons-cons 支 .mp 直取。

  随收件二：`flatten_eq_nil` :11906-:11920
  `!r. flatten r = [] <=> all (\p. p = []) r`
  ↦ `flattenEqNil`（真证）。HOL EQ_EXPAND 双向；Lean 面 mem_flatten 双向
  拆块（⇒ 向反证以 mem 压 []；⇐ 向逐点 h p hp 消解）。

  随收件三：`last_flatten` :11922-:11944
  `!r. ~(r = []) /\ all (\x. ~(x = [])) r ==> LAST (flatten r) =
  LAST (LAST r)`
  ↦ `lastFlatten`（真证）。HOL flatten_cons 拆 + LAST_cat + flatten_eq_nil
  支；Lean 面 LAST ↦ getLast! 折算免归纳：私件 getLast!_eq_getLast（经
  getLast?_eq_some_getLast 双向转换）+ Mathlib
  getLast_flatten_eq_getLast_getLast（flatten ≠ [] 两侧义务由随收件二 +
  all 非空消解）三发 rw 收口。

  跳过项（非止损，照批 35/36 记档体例）：
  · :11783-:11795 `e_list_map` 系 HOL 源注释块（`(* ... *)` 内被
    e_list_fun 取代的未完成草稿，非定理）。

  终点自然边界：:11765 后 :11797 入 `inj_on_one_step_list`
  （one_step/contour 运输新章——f_list_map（tame_list.hl:3840）载体链：
  findFace_map_injOn（批 1，TameList1.lean:107 = find_face_map 桥形）+
  eListFun（批 5，TameList5.lean:291 = e_list_fun）+ oneStepListSpine
  （批 5）在库，但 fList 的 findFace 连接层 + good_list_e_list
  （tame_list.hl:3883，MEM (SND d,FST d) darts 换面）载体缺口待补，批 38
  开章件）→ :11841 `inj_on_contour_list`（链于 :11797）→ :11879
  `eqseq_cat3`（Seq-index 章：indexl_LAST/index_cat 载体缺口）→ :11946
  `parts_characterize`（parts 章归纳主体，批 38+ 领土）。

  依赖面：批链全批 1-36；本批零新 def，消费面 = 批 16
  listOfDartsQuotientDarts + 批 13 contourListCons + 批 5
  NormalListSpine 面 + 批 7 quotientListSpine + TameLp
  elementsOfList/listOfElements/hypermapOfList + 核心 List.mem_flatten /
  mem_eraseDups / mem_iff_getElem / getElem_zip / length_zip /
  flatten·getLast 族。

  诚实记账：本批五件全部真证，零新 def、零 sorry、零止损件、零记账债
  （两桥面私件系私件不跨文件惯例同证重推导，非新领土）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零
  git 写操作。批 38 接续点：HOL :11797 `inj_on_one_step_list`
  `!phi L h1 h2. good_list L /\ inj_on phi (elements_of_list L) /\
  MEM h1 (list_of_darts L) /\ MEM h2 (list_of_darts L) ==>
  one_step_list (MAP (MAP phi) L) (nphi h1) (nphi h2) =
  one_step_list L h1 h2`（nphi = pair-lift；载体面批次见上「终点自然
  边界」三层处方）→ 其后 :11841 `inj_on_contour_list`（批 13
  contourListCons + map_list_of_darts（tame_list.hl:1051）+ 批 2 memfMap
  面）。
-/

import Kepler.Text.TameSpine.TameList36

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listPairs listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList listOfElements elementsOfList)

/-! ### §0 私件：darts↔elements 桥面（HOL mem_list_of_elements 面，
惯例同证重推导，非新领土） -/

/-- 非空表 `getLast!` 即 `getLast`（getLast? 桥双向转换）。 -/
private theorem getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- 非空表 `getLast!` 必是成员（批 10/11 私件同证重推导）。 -/
private theorem getLastMem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [getLast!_eq_getLast h]
  exact List.getLast_mem h

/-- dart 首分量入 elements（批 16 私件 fstMemListOfElements
TameList16.lean:215 同证重推导）——桥面 ⇐ 向。 -/
private theorem fstMemListOfElements {L : fgraph ℕ} {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : d.1 ∈ listOfElements L := by
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
  simp only [List.mem_map] at hl
  obtain ⟨l₀, hl₀, hEq⟩ := hl
  subst hEq
  obtain ⟨i, hi, hdz⟩ := List.mem_iff_getElem.mp hdl
  have hi2 : i < (l₀.zip (l₀.drop 1 ++ l₀.take 1)).length := hi
  rw [List.length_zip] at hi2
  have hii : i < l₀.length := (Nat.lt_min.mp hi2).1
  have hdz2 : (l₀.zip (l₀.drop 1 ++ l₀.take 1))[i]'hi = d := hdz
  rw [List.getElem_zip] at hdz2
  have h2 : d.1 ∈ l₀ := by
    rw [← congrArg Prod.fst hdz2]
    exact List.getElem_mem hii
  show d.1 ∈ L.flatten.eraseDups
  simp
  exact ⟨l₀, hl₀, h2⟩

/-- 元素 x 的循环后继给 dart 证人（HOL mem_list_of_elements ⇒ 向，
证人 y = zip 第二槽 `(l.drop 1 ++ l.take 1)[i]`）——桥面 ⇒ 向。 -/
private theorem memElementsSubDarts {L : fgraph ℕ} {x : ℕ}
    (hx : x ∈ listOfElements L) : ∃ y : ℕ, (x, y) ∈ listOfDarts L := by
  have hx' : x ∈ L.flatten := List.mem_eraseDups.mp hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx'
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hxl
  have h1 : 0 < l.length := List.length_pos_of_mem hxl
  have hlen : (l.drop 1 ++ l.take 1).length = l.length := by
    rw [List.length_append, List.length_drop, List.length_take,
      Nat.min_eq_left (by omega)]
    omega
  have ihlen : i < (l.drop 1 ++ l.take 1).length := by rw [hlen]; exact hi
  refine ⟨(l.drop 1 ++ l.take 1)[i]'ihlen, List.mem_flatten.mpr
    ⟨listPairs l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩⟩
  show (x, (l.drop 1 ++ l.take 1)[i]'ihlen) ∈ l.zip (l.drop 1 ++ l.take 1)
  have hzi : i < (l.zip (l.drop 1 ++ l.take 1)).length := by
    rw [List.length_zip, hlen]
    omega
  have hpair : (l.zip (l.drop 1 ++ l.take 1))[i]'hzi
      = (x, (l.drop 1 ++ l.take 1)[i]'ihlen) := by
    rw [List.getElem_zip, hxi]
  exact List.mem_iff_getElem.mpr ⟨i, hzi, hpair⟩

/-! ### §1 elements_of_list_quotient_list（tame_list.hl:11747-:11762）——章主体 -/

/-- **HOL `elements_of_list_quotient_list`**（tame_list.hl:11747-:11762）
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
good_list L /\ all uniq L ==> elements_of_list (quotient_list L N) SUBSET
elements_of_list L`——SUBSET 逐点 + 证人 y（桥面 ⇒ 向）+
list_of_darts_quotient_darts（批 16 在库）+ 桥面 ⇐ 向收口。 -/
theorem elementsOfListQuotientList (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) :
    elementsOfList (quotientListSpine L N) ⊆ elementsOfList L := by
  intro x hx
  have hx' : x ∈ listOfElements (quotientListSpine L N) := hx
  obtain ⟨y, hy⟩ := memElementsSubDarts hx'
  exact fstMemListOfElements (listOfDartsQuotientDarts L hL hn hnedg hunL hy)

/-! ### §2 inj_on_quotient_list（tame_list.hl:11765-:11780）——随收形主件 -/

/-- **HOL `inj_on_quotient_list`**（tame_list.hl:11765-:11780；批 36 预记
:11764 偏移 +1 记档）
`normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
good_list L /\ all uniq L /\ inj_on phi (elements_of_list L) ==>
inj_on phi (elements_of_list (quotient_list L N))`——inj_on_subset +
前件复用：Set.InjOn.mono 子集槽即 §1。 -/
theorem injOnQuotientList (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) :
    Set.InjOn phi (elementsOfList (quotientListSpine L N)) :=
  hinj.mono (elementsOfListQuotientList L hL hn hnedg hunL)

/-! ### §3 contour_list_hd_dart（tame_list.hl:11831-:11839）——随收件 -/

/-- **HOL `contour_list_hd_dart`**（tame_list.hl:11831-:11839）
`contour_list L (h::s) ==> MEM h (list_of_darts L)`——s 两拆经批 13
contourListCons 单元素/cons-cons 支 .mp 直取。 -/
theorem contourListHdDart (L : fgraph ℕ) {h : ℕ × ℕ} {s : List (ℕ × ℕ)}
    (hc : ContourListSpine L (h :: s)) : h ∈ listOfDarts L := by
  cases s with
  | nil => exact ((contourListCons L).2.1 h).mp hc
  | cons h₂ s' => exact (((contourListCons L).2.2 h h₂ s').mp hc).1

/-! ### §4 flatten_eq_nil / last_flatten（tame_list.hl:11906-:11944）——随收件 -/

/-- **HOL `flatten_eq_nil`**（tame_list.hl:11906-:11920）
`flatten r = [] <=> all (\p. p = []) r`——mem_flatten 双向拆块。 -/
theorem flattenEqNil (r : List (List ℕ)) :
    r.flatten = [] ↔ ∀ p ∈ r, p = [] := by
  constructor
  · intro h p hp
    by_contra hpne
    obtain ⟨x, hxp⟩ := List.exists_mem_of_ne_nil p hpne
    have hx : x ∈ r.flatten := List.mem_flatten.mpr ⟨p, hp, hxp⟩
    rw [h] at hx
    exact List.not_mem_nil hx
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil r.flatten hne
    obtain ⟨p, hp, hxp⟩ := List.mem_flatten.mp hx
    rw [h p hp] at hxp
    exact absurd hxp (by simp)

/-- **HOL `last_flatten`**（tame_list.hl:11922-:11944）
`~(r = []) /\ all (\x. ~(x = [])) r ==> LAST (flatten r) = LAST (LAST r)`
——LAST ↦ getLast! 折算；§4 flattenEqNil 消解 flatten ≠ [] 义务 +
Mathlib getLast_flatten_eq_getLast_getLast 三发收口。 -/
theorem lastFlatten {r : List (List ℕ)} (hne : r ≠ [])
    (hall : ∀ p ∈ r, p ≠ []) :
    r.flatten.getLast! = r.getLast!.getLast! := by
  have hmem : r.getLast! ∈ r := getLastMem hne
  have hlastNE : r.getLast! ≠ [] := hall _ hmem
  have hflat : r.flatten ≠ [] := by
    intro hc
    exact hlastNE ((flattenEqNil r).mp hc _ hmem)
  have hlastGNE : r.getLast hne ≠ [] := by
    rw [← getLast!_eq_getLast hne]
    exact hlastNE
  rw [getLast!_eq_getLast hflat, getLast!_eq_getLast hne,
    List.getLast_flatten_eq_getLast_getLast hflat hlastGNE,
    getLast!_eq_getLast hlastGNE]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；五件预期零 sorryAx，桥面私件同证重推导
零新领土）：
#print axioms Kepler.Text.TameSpine.elementsOfListQuotientList
#print axioms Kepler.Text.TameSpine.injOnQuotientList
#print axioms Kepler.Text.TameSpine.contourListHdDart
#print axioms Kepler.Text.TameSpine.flattenEqNil
#print axioms Kepler.Text.TameSpine.lastFlatten
-/
