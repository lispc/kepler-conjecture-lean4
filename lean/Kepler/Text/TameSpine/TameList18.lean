/-
  Kepler.Text.TameSpine.TameList18 — B1 Tame_list 地基批 18：marked 几何章
  （tamespine-port-plan §4 批次表 B1 行；接续批 17 = TameList17.lean，批 17
  终点 = HOL :10211（HQYMRTX3_list 已落，marked_lemma_yz_in_face :10214
  起留给本批）；本批起点 = HOL :10214）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10214-:10341）——marked 几何章
  4 枚全量：

  `marked_lemma_yz_in_face` :10214 / `mem_l_z_dart` :10229 /
  `card_atoms_of_loop` :10243 / `QRDYXYJ_list` :10307。:10344 自然边界
  收批（`iso_list_restricted` 起的 iso 章 + :10361-:10579 小工具箱与
  list_pairs 旋转章留批 19）。

  依赖面（全为在案真件，零新增债）：批 16 `lemmaYzInFaceList`（split
  条件版 yz-在面件，本批 marked 版经 marked_list 的 next_el /
  split_condition 两桥直接升格）/ 批 16 `markedConclusion`（在案可引）/
  批 17 `markedTranslate`（hyp↔l' 五桥的桥面）/ 批 12 `memLYDart`（y 侧
  dart 桥）+ `markListSplitConditionList` + hyp 五桥 `hypMLm`/`hypPLp`/
  `hypYL`/`hypZLz` / 批 11 `atomEqLast`+`atomLastInj` / 批 10
  `partsLastInj`+`uniqParts` / 批 9 `partsFlatten`+`partsUniqNonnil` /
  批 7 `partsAllNonnil`+`memHypermapOfListNode` / Hypermap 层
  `parameters`（hypermap.hl:12217，Hypermap.lean:10857 在案）/
  `atomsOfLoop`/`node_eq_of_mem` / TameLp `mem_darts_of_mem_findFace`
  （= List_hypermap.mem_find_face_imp_mem_darts）/ 批 5
  `getLast!EqGetLast`。

  载体折算（沿批 1-17 约定）：`find_face L x` ↦ `findFaceDarts L x`
  （批 16 lemmaYzInFaceList 同款）；`MEM u (list_of_darts L)` 的 face 桥
  = `mem_darts_of_mem_findFace`；`CARD (atoms_of_loop H L)` ↦
  `(H.atomsOfLoop L).ncard`；`sizel (parts L r)` ↦ `(partsSpine L r).length`
  （批 12 sizel 记账）；`BIJ` ↦ `Set.BijOn`（批 11）；`CARD (set_of_list l)
  = sizel l`（uniq l）桥 = `setOfListSpine` = ↑`List.toFinset` +
  `Set.ncard_coe_finset` + `List.toFinset_card_of_nodup`（Seq2.
  card_set_of_list_uniq 折算）；`l'q` 的 Skolem 证明参（hnf/hmk/hl）
  显式入参（批 12 lQSpine 同款折算：HOL 消费点均持 is_marked/¬final
  前提，语义零收窄）；node 不等式 ↦ FST 不等式经批 7
  `memHypermapOfListNode` 双向 + Hypermap `node_eq_of_mem`（node 轨道 =
  同 FST dart 集在案）。

  诚实记账：本批四件全部真证，零新增记账债（零止损件）。公理审计实测
  （#print axioms，2026-10-13）：四件 markedLemmaYzInFace/memLZDart/
  cardAtomsOfLoop/qrdyxyjList 均仅依赖标准三 [propext,
  Classical.choice, Quot.sound]，零记账传入——批 16 在案债件
  （quotient_list_iso_quotient :8223 / marked_list_is_node_nondegenerate
  :9362）不在本章依赖链上（markedLemmaYzInFace 走 lemmaYzInFaceList 的
  Hypermap 直桥，qrdyxyjList 走 Hypermap.parameters + parts 机器，均
  无债面）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 19 接续点：HOL :10344 `iso_list_restricted` 起的 iso 章
  （iso_list_restricted :10344，前提 good_list L' + iso_list (L',[]) (L,[])
  + is_restricted——依 DAKEFCC/GNBEVVU 的 Hypermap 层桥侦察；Lean 侧 iso
  章 TameList15 hypIsoCardComponents 已备）；其后 :10361-:10579 小工具箱
  与 list_pairs 旋转章（INJ_EMPTY :10361 / set_of_list_rev :10369 /
  el_iota :10377 / I_POWER :10389 / hd_iota :10399 / list_pairs_empty_alt
  :10410 / set_of_list_pairs_set_of_list_subset :10418 / .._eq :10432 /
  card_set_of_list_uniq2 :10442 / list_pairs_rot :10454 /
  list_pairs_rot_subset :10495 / e_list_image :10534，需
  next_el_power_rot/rot 载体侦察）。
-/

import Kepler.Text.TameSpine.TameList17

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList listPairs listOfDarts
  findFaceDarts nList)
open Kepler.Graphs (fgraph between)
open Kepler.Text (orbitMap setOfOrbits)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem dart_in_face findFaceDarts_ex_of_self
  findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  mem_darts_of_mem_findFace nextEl_mem_of_mem flatten_nodup_mem
  faceMap_hypermapOfList nodeMap_hypermapOfList GoodListNodesTl)

/-! ### §0 私件引擎 -/

/-- 批 10 私件不跨文件，§0 同证重推导（批 7→18 惯例）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [getLast!EqGetLast h]
  exact List.getLast_mem h

/-! ### §1 marked_lemma_yz_in_face + mem_l_z_dart（tame_list.hl:10214-:10241） -/

/-- **HOL `marked_lemma_yz_in_face`**（tame_list.hl:10214-:10226）
`!L N r x.
      good_list L /\ good_list_nodes L /
     marked_list L N r x /\ ~final_list L r ==>
    MEM (l'y L r x) (find_face L x) /\ MEM (l'z L N r x) (find_face L x)`
——批 16 `lemmaYzInFaceList`（split 条件版）经 marked_list 的两座桥升格：
`next_el r x = f_list L x`（MarkedListSpine 合取）与
`split_condition_list`（批 12 markListSplitConditionList）。
载体记账：`find_face L x` ↦ `findFaceDarts L x`（批 16 同款）。 -/
theorem markedLemmaYzInFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ∈ findFaceDarts L x ∧ lZSpine L N r x ∈ findFaceDarts L x :=
  lemmaYzInFaceList L hL hgn hunL (hm.1.2.2.2.2.2.1)
    (markListSplitConditionList L hL hm.1 hf)

/-- **HOL `mem_l_z_dart`**（tame_list.hl:10229-:10240）
`!L N r x.
      good_list L /\ good_list_nodes L /
     marked_list L N r x /\ ~final_list L r
  ==> MEM (l'z L N r x) (list_of_darts L)`
——marked_lemma_yz_in_face + List_hypermap.mem_find_face_imp_mem_darts
（TameLp `mem_darts_of_mem_findFace`）。 -/
theorem memLZDart (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lZSpine L N r x ∈ listOfDarts L :=
  mem_darts_of_mem_findFace L (markedLemmaYzInFace L hL hgn hunL hm hf).2

/-! ### §2 card_atoms_of_loop（tame_list.hl:10243-:10304） -/

/-- HOL `card_atoms_of_loop` 的 BIJ 内核：`p ↦ atom (LAST p)` 在
parts L r 的成员集（`Set (List (ℕ × ℕ))` 载体，HOL `set_of_list (parts
L r)`；批 11 `setOfListSpine` 是 dart 级载体不适用）与 atoms_of_loop
(loop_of_list r) 之间双射——映入 = atomsOfLoop 定义 + partsUniqNonnil
（LAST p ∈ r ⇒ loop darts）；单射 = atomLastInj（同 r 槽）+
partsLastInj；满射 = atomsOfLoop 拆包 + partsFlatten 定位 p ∋ d +
atomEqLast（HOL BIJ 三支同构）。 -/
private theorem atomsOfLoopBijOnParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) :
    Set.BijOn (fun p : List (ℕ × ℕ) =>
        (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast!)
      {p : List (ℕ × ℕ) | p ∈ partsSpine L r}
      ((hypermapOfList L hL).atomsOfLoop (loopOfListSpine r)) := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  refine ⟨?_, ?_, ?_⟩
  · -- 映入
    intro p hp
    have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
    have hlastR : p.getLast! ∈ r :=
      (partsUniqNonnil L hL hn hr hp).2.2.2.2 p.getLast! (getLastMem hpne)
    exact ⟨p.getLast!, (inDartLoopOfList hr1 hr2 p.getLast!).mpr hlastR, rfl⟩
  · -- 单射
    intro p hp p' hp' hcon
    obtain ⟨-, hlast⟩ := atomLastInj L hL hn hnedg hunL hr hr hp hp' hcon
    exact partsLastInj L hL hn hr hp hp' hlast
  · -- 满射
    intro a ham
    simp only [Hypermap.atomsOfLoop, Set.mem_setOf_eq] at ham
    obtain ⟨d, hd, rfl⟩ := ham
    have hdr : d ∈ r := (inDartLoopOfList hr1 hr2 d).mp hd
    obtain ⟨p, hp, hdp⟩ : ∃ p ∈ partsSpine L r, d ∈ p := by
      have hfl : d ∈ (partsSpine L r).flatten := by
        rw [partsFlatten L hr1 hr2]; exact hdr
      exact List.mem_flatten.mp hfl
    refine ⟨p, hp, (atomEqLast L hL hn hnedg hunL hr hp hdp).symm⟩

/-- **HOL `card_atoms_of_loop`**（tame_list.hl:10243-:10304）
`!L N r.
   good_list L /\ good_list_nodes L /\ normal_list L N /\
         is_edge_nondegenerate (hypermap_of_list L) /\
          all uniq L /\
   MEM r N ==>
   CARD (atoms_of_loop (hypermap_of_list L) (loop_of_list r))  =
	 sizel (parts L r)`
——BIJ 内核（atomsOfLoopBijOnParts）+ InjOn.ncard_image（HOL
CARD_IMAGE_INJ + *_FINITE 同构）+ `CARD (set_of_list l) = sizel l` 桥
（setOfListSpine = ↑toFinset + Set.ncard_coe_finset +
List.toFinset_card_of_nodup；`sizel` ↦ `length`，批 12 记账）。 -/
theorem cardAtomsOfLoop (L : fgraph ℕ) (hL : GoodList L)
    (_hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r : List (ℕ × ℕ)} (hr : r ∈ N) :
    ((hypermapOfList L hL).atomsOfLoop (loopOfListSpine r)).ncard
      = (partsSpine L r).length := by
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hr
  have hbij := atomsOfLoopBijOnParts L hL hn hnedg hunL hr
  have hTeq : (hypermapOfList L hL).atomsOfLoop (loopOfListSpine r)
      = (fun p : List (ℕ × ℕ) =>
          (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast!)
        '' {p : List (ℕ × ℕ) | p ∈ partsSpine L r} := by
    ext a
    constructor
    · intro ham
      obtain ⟨p, hp, hpa⟩ := hbij.surjOn ham
      exact ⟨p, hp, hpa⟩
    · rintro ⟨p, hp, hpa⟩
      have hm2 := hbij.mapsTo hp
      have hm3 : (hypermapOfList L hL).atom (loopOfListSpine r) p.getLast! = a :=
        hpa
      rw [← hm3]
      exact hm2
  have hcardList : ({p : List (ℕ × ℕ) | p ∈ partsSpine L r} :
        Set (List (ℕ × ℕ))).ncard = (partsSpine L r).length := by
    have hfin : ({p : List (ℕ × ℕ) | p ∈ partsSpine L r} :
          Set (List (ℕ × ℕ)))
        = ((partsSpine L r).toFinset : Set (List (ℕ × ℕ))) := by
      ext d
      constructor
      · intro hd; exact List.mem_toFinset.mpr hd
      · intro hd; exact List.mem_toFinset.mp hd
    rw [hfin, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (uniqParts L hr1 hr2)]
  rw [hTeq, Set.InjOn.ncard_image hbij.injOn, hcardList]

/-! ### §3 QRDYXYJ_list（tame_list.hl:10307-:10341） -/

/-- **HOL `QRDYXYJ_list`**（tame_list.hl:10307-:10341）
`!L N r x.
  good_list L /\
  good_list_nodes L /\
  marked_list L N r x /\ ~(final_list L r) ==>
  l'm L r x < l'q L N r x /\
  l'q L N r x < sizel (parts L r) /\
  SUC (l'm L r x) < l'p L N r x + l'q L N r x /\
  ~(FST (l'y L r x) = FST x) /\
  ~(FST (l'y L r x) = FST (l'z L N r x))`
——Hypermap 层 `parameters`（hypermap.hl:12217）+ 批 12 hyp 五桥
（hypMLm/hypPLp/hypYL/hypZLz，marked_list 的 next_el/split_condition
两桥）+ 本批 cardAtomsOfLoop（sizel (parts) 支）+ 本批 memLZDart（z
侧 dart 支）+ 批 12 memLYDart + 批 7 memHypermapOfListNode 双向 +
Hypermap node_eq_of_mem（FST 两支）。`l'q` 的 Skolem 证明参（hnf/hmk/
hl）显式入参（批 12 lQSpine 同款折算，零收窄）。 -/
theorem qrdyxyjList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N)}
    (hmk : (hypermapOfList L hL).IsMarked (loopFamilyOfListSpine N) hnf
      (loopOfListSpine r) x)
    (hl : loopOfListSpine r ∉ (hypermapOfList L hL).finalLoops
      (loopFamilyOfListSpine N)) :
    lMSpine L r x < lQSpine L hL hnf hmk hl ∧
      lQSpine L hL hnf hmk hl < (partsSpine L r).length ∧
      lMSpine L r x + 1 < lPSpine L N r x + lQSpine L hL hnf hmk hl ∧
      (lYSpine L r x).1 ≠ x.1 ∧
      (lYSpine L r x).1 ≠ (lZSpine L N r x).1 := by
  have hnext := hm.1.2.2.2.2.2.1
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hres := hm.1.1
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    Hypermap.parameters (hypermapOfList L hL) hmk hl
  rw [hypMLm L hL hgn hunL hnext hsc] at h1 h3
  rw [hypPLp L hL hgn hunL hnext hsc] at h3
  rw [cardAtomsOfLoop L hL hgn hn hnedg hunL hrN] at h2
  rw [hypYL L hL hgn hunL hnext hsc] at h4 h5
  rw [hypZLz L hL hgn hunL hnext hsc] at h5
  have hxd : x ∈ listOfDarts L := splitConditionListOfDarts hsc
  have hyD : lYSpine L r x ∈ listOfDarts L := memLYDart L hL hsc
  have hzD : lZSpine L N r x ∈ listOfDarts L := memLZDart L hL hgn hunL hm hf
  have eQ : lQSpine L hL hnf hmk hl
      = (hypermapOfList L hL).hypQ hmk hl := rfl
  rw [eQ]
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · -- FST (l'y) ≠ FST x
    intro hcon
    have hny : lYSpine L r x ∈ (hypermapOfList L hL).node x :=
      (memHypermapOfListNode hL hgn hxd).mpr ⟨hcon.symm, hyD⟩
    exact h4 ((hypermapOfList L hL).node_eq_of_mem hny).symm
  · -- FST (l'y) ≠ FST (l'z)
    intro hcon
    have hny : lYSpine L r x ∈ (hypermapOfList L hL).node (lZSpine L N r x) :=
      (memHypermapOfListNode hL hgn hzD).mpr ⟨hcon.symm, hyD⟩
    exact h5 ((hypermapOfList L hL).node_eq_of_mem hny).symm

end Kepler.Text.TameSpine
