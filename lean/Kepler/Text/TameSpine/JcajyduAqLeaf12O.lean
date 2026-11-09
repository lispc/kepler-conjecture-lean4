/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12O — AQ12 叶 W7（F2，decls 47–50）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:2150-:2341（192 HOL 行）
  · decl 47 `last_parts_y_not_s_list`（:2150-:2203，54 行）
  · decl 48 `last_parts_e_list_y_not_s_list`（:2204-:2299，96 行）
  · decl 49 `exist_final_list_e_list`（:2300-:2321，22 行）
  · decl 50 `one_step_e_list_last_y`（:2322-:2341，20 行）

  ┌─ 专项负探针结论（node 族 QUAL，开工先报）──────────────────────
  │ · 四个目标件：Lean 全树 **0 命中**（无同名/camelCase/sorry 桩）⇒ 全部新落。
  │ · HOL 6 个「零命中」名均有**语义等价件**（仅换名）：
  │   `node_refl`→`mem_node_self`；`lemma_node_identity`→`node_eq_of_mem`；
  │   `lemma_inverse_in_node`→`nodeMap_symm_pow_mem_node_self`；
  │   `node_map_and_darts`→`nodeMap_apply_mem`/`nodeMap_permutes`；
  │   `fixed_point_lemma`→`inverseNodeMapQuotient` + `markedListIsNodeNondegenerate`
  │   + `isoIsNodeNondegenerate` + `quotientListIsoQuotient` 组合；
  │   `dart_list_all`→`List.mem_toFinset` 桥。
  │ · 支撑件 20+ 全在库（partsFst/Darts/InNode、fListPowEqNextElPow、
  │   normalListPartsNextLast(Not)、inverseNodeMapList/Quotient、
  │   quotients、simpleHypermapUniq、aqs_lastPartsYNotCat 等）。
  │ · **本波不吃 `h4 : aq4Concl` 槽（DIFFERS：W5b/W6b 吃，W7 不吃）**——
  │   四件都在 parts/sList/face/node 层，不涉及 split 行 loopList。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ─────────────────────────────────────────────────────────
  │ 47：lp ∈ sList ⇒ lp ∈ findFace x；lp,y ∈ p 同 node；Simple（node∩face={y}）
  │     与 face y = face x 给 lp = y，撞 `aqs_lastPartsYNotCat`。
  │ 48：eList lp ∈ sList ⇒ fList(eList lp) ∈ node y（`inverseNodeMapList`）且
  │     ∈ face y ⇒ Simple 给 fList(eList lp) = y；`inverseNodeMapQuotient`
  │     把 `fList(eList lp) ∈ p` 翻成商 nodeMap.symm 不动点，撞商
  │     NodeNondegenerate（`markedListIsNodeNondegenerate` 运输）。
  │ 49：SFlag 次合取（47+48 消去 sList 支）给 eList lp ∈ FinalDartList，
  │     `findListUniq` 把 findList 钉到该 final 行。
  │ 50：`one_step_list` 第二析取 **rfl**。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12N
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList16
import Kepler.Text.TameCorrCard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_mem_of_mem dart_in_face)

/-! ## §0 私件：fList 幂留在面内 -/

/-- `(nextEl s)^[n] y ∈ s`（y ∈ s）。 -/
private theorem aq12o_memNextElIterate {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {y : α} (hy : y ∈ s) : ∀ n : ℕ, (nextEl s)^[n] y ∈ s := by
  intro n
  induction n with
  | zero => exact hy
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- `(fList L)^[k] x ∈ findFaceDarts L x`（x ∈ findFaceDarts L x）。 -/
private theorem aq12o_memFListPowFindFace (L : fgraph ℕ) (hL : GoodList L)
    {x : ℕ × ℕ} (hx : x ∈ findFaceDarts L x) (k : ℕ) :
    (fList L)^[k] x ∈ findFaceDarts L x := by
  rw [fListPowEqNextElPow L hL x hx k]
  exact aq12o_memNextElIterate hx k

/-! ## §1 HOL AQ12.hl:2150 `last_parts_y_not_s_list` -/

/-- **HOL `last_parts_y_not_s_list`**（AQ12.hl:2150-:2203）：
part 末元 `lp` 不在 `sList L r x` 中。 -/
theorem aqs_lastPartsYNotSList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    lp ∉ sListSpine L r x := by
  intro hmem
  -- lp ∈ sList ⇒ lp ∈ findFace x
  obtain ⟨i, hi, hie⟩ := List.mem_map.mp hmem
  rw [List.mem_range] at hi
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hxd : x ∈ listOfDarts L := normalListListOfDarts hm.1.2.1 x
    (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfaceLp : lp ∈ findFaceDarts L x := by
    rw [← hie]
    exact aq12o_memFListPowFindFace L hL hxx _
  -- y ∈ findFace x；lp, y 同 node
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyF : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : lp ∈ p := by
    rw [← hlast, getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpNode : lp ∈ (hypermapOfList L hL).node p.head! :=
    partsInNode L hL hm.1.2.1 hm.1.2.2.1 hp hlpMem
  have hyNode : lYSpine L r x ∈ (hypermapOfList L hL).node p.head! :=
    partsInNode L hL hm.1.2.1 hm.1.2.2.1 hp hyp
  have hnodeEq : (hypermapOfList L hL).node p.head!
      = (hypermapOfList L hL).node (lYSpine L r x) :=
    Kepler.Text.Hypermap.node_eq_of_mem (hypermapOfList L hL) hyNode
  have hlpNodeY : lp ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
    rw [← hnodeEq]
    exact hlpNode
  -- lp ∈ face y（face y = face x）
  have hyd : lYSpine L r x ∈ listOfDarts L :=
    partsDarts L hm.1.2.1 hm.1.2.2.1 hp hyp
  have hfaceEq : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hyF
  have hlpFaceY : lp ∈ (hypermapOfList L hL).face (lYSpine L r x) := by
    rw [Kepler.Text.TameCorrCard.faceOfList hL hyd, Set.mem_setOf_eq, hfaceEq]
    exact hfaceLp
  -- Simple ∩ = {y} ⇒ lp = y
  have hyD : lYSpine L r x ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr hyd
  have hsimple := (simpleHypermapUniq L hL hgn).mpr hunL
  have hinter : lp ∈ (hypermapOfList L hL).node (lYSpine L r x)
      ∩ (hypermapOfList L hL).face (lYSpine L r x) := ⟨hlpNodeY, hlpFaceY⟩
  rw [hsimple (lYSpine L r x) hyD] at hinter
  have hlpEq : lp = lYSpine L r x := Set.mem_singleton_iff.mp hinter
  -- 撞 last_parts_y_not_cat
  exact aqs_lastPartsYNotCat L hL hgn hm hf hp hyp
    (by rw [hlast, hlpEq]
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
          (Or.inr (List.mem_singleton_self _)))))

/-! ## §2 HOL AQ12.hl:2204 `last_parts_e_list_y_not_s_list` -/

/-- **HOL `last_parts_e_list_y_not_s_list`**（AQ12.hl:2204-:2299）：
`eList lp` 不在 `sList L r x` 中（商 node 不动点矛盾）。 -/
theorem aqs_lastPartsEListYNotSList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    eList lp ∉ sListSpine L r x := by
  intro hmem
  obtain ⟨i, hi, hie⟩ := List.mem_map.mp hmem
  rw [List.mem_range] at hi
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hxd : x ∈ listOfDarts L := normalListListOfDarts hm.1.2.1 x
    (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfaceE : eList lp ∈ findFaceDarts L x := by
    rw [← hie]
    exact aq12o_memFListPowFindFace L hL hxx _
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyF : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hfaceEq : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hyF
  have hyd : lYSpine L r x ∈ listOfDarts L :=
    partsDarts L hm.1.2.1 hm.1.2.2.1 hp hyp
  -- fList(eList lp) ∈ face y
  have hEfind : eList lp ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hfaceEq]
    exact hfaceE
  have hffFaceY : fList L (eList lp) ∈ (hypermapOfList L hL).face (lYSpine L r x) := by
    have hcongr : findFaceDarts L (eList lp) = findFaceDarts L (lYSpine L r x) :=
      aq10_memFindFaceImpFacesEq hL.1 hEfind
    have hnextmem : fList L (eList lp) ∈ findFaceDarts L (lYSpine L r x) := by
      rw [fList, hcongr]
      exact nextEl_mem_of_mem hEfind
    rw [Kepler.Text.TameCorrCard.faceOfList hL hyd, Set.mem_setOf_eq]
    exact hnextmem
  -- fList(eList lp) ∈ node y
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : lp ∈ p := by
    rw [← hlast, getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpD : lp ∈ listOfDarts L := partsDarts L hm.1.2.1 hm.1.2.2.1 hp hlpMem
  have hinv : (hypermapOfList L hL).nodeMap.symm lp = fList L (eList lp) :=
    inverseNodeMapList hL hlpD
  have hsymmNode : (hypermapOfList L hL).nodeMap.symm lp
      ∈ (hypermapOfList L hL).node lp := by
    simpa using Kepler.Text.Hypermap.nodeMap_symm_pow_mem_node_self
      (hypermapOfList L hL) lp 1
  have hlpNode : lp ∈ (hypermapOfList L hL).node p.head! :=
    partsInNode L hL hm.1.2.1 hm.1.2.2.1 hp hlpMem
  have hyNode : lYSpine L r x ∈ (hypermapOfList L hL).node p.head! :=
    partsInNode L hL hm.1.2.1 hm.1.2.2.1 hp hyp
  have hnodeEq : (hypermapOfList L hL).node p.head!
      = (hypermapOfList L hL).node (lYSpine L r x) :=
    Kepler.Text.Hypermap.node_eq_of_mem (hypermapOfList L hL) hyNode
  have hlpNodeY : lp ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
    rw [← hnodeEq]; exact hlpNode
  have hnodeYlp : (hypermapOfList L hL).node (lYSpine L r x)
      = (hypermapOfList L hL).node lp :=
    Kepler.Text.Hypermap.node_eq_of_mem (hypermapOfList L hL) hlpNodeY
  have hffNodeY : fList L (eList lp) ∈ (hypermapOfList L hL).node (lYSpine L r x) := by
    rw [← hinv, hnodeYlp]
    exact hsymmNode
  -- Simple ⇒ fList(eList lp) = y
  have hyD : lYSpine L r x ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr hyd
  have hsimple := (simpleHypermapUniq L hL hgn).mpr hunL
  have hinter : fList L (eList lp) ∈ (hypermapOfList L hL).node (lYSpine L r x)
      ∩ (hypermapOfList L hL).face (lYSpine L r x) := ⟨hffNodeY, hffFaceY⟩
  rw [hsimple (lYSpine L r x) hyD] at hinter
  have hffEq : fList L (eList lp) = lYSpine L r x := Set.mem_singleton_iff.mp hinter
  -- 商 nodeMap 不动点矛盾
  have hn := hm.1.2.1
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hm.1.1.edgeNondegenerate
  have hrN : r ∈ N := hm.1.2.2.1
  have hgood : GoodList (quotientListSpine L N) := goodListQuotient L hL hn hnedg hunL
  have hgnq : GoodListNodesTl (quotientListSpine L N) hgood :=
    goodListNodesQuotient L hL hgn hn hnedg hunL
  have hiso := quotientListIsoQuotient L hL hgn hm.1.1 hn hnedg hunL
  have hnnQ := markedListIsNodeNondegenerate L hL hgn hm.1.1 hn hnedg hunL hgnq hm.1
  have hnn := isoIsNodeNondegenerate hiso hnnQ
  have hiff := inverseNodeMapQuotient L hL hn hnedg hunL hrN hrN hp hp
  have hsymmQ : (hypermapOfList (quotientListSpine L N) hgood).nodeMap.symm
      p.getLast! = p.getLast! :=
    hiff.mpr (by rw [hlast, hffEq]; exact hyp)
  have hnodeQ : (hypermapOfList (quotientListSpine L N) hgood).nodeMap
      p.getLast! = p.getLast! := by
    have h := congrArg (fun z => (hypermapOfList (quotientListSpine L N) hgood).nodeMap z) hsymmQ
    simpa using h.symm
  have hlastQ : p.getLast! ∈ (hypermapOfList (quotientListSpine L N) hgood).darts :=
    List.mem_toFinset.mpr
      ((memListOfDartsQuotient L hL hn hnedg hunL (p.getLast!)).mpr
        ⟨p, r, hp, hrN, rfl⟩)
  exact hnn p.getLast! hlastQ hnodeQ

/-! ## §3 HOL AQ12.hl:2300 `exist_final_list_e_list` -/

/-- **HOL `exist_final_list_e_list`**（AQ12.hl:2300-:2321）：
`findList N (eList lp)` 是 final 行。 -/
theorem aqs_existFinalListEList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    finalListSpine L (findListSpine N (eList lp)) := by
  have h47 := aqs_lastPartsYNotSList L hL hgn hm hf hp hyp hlast
  have h48 := aqs_lastPartsEListYNotSList L hL hgn hm hf hp hyp hlast
  have hsf : SFlagListSpine L N r x := hm.2.2 hf
  have hmem := hsf.2 r p lp hlast.symm hp hm.1.2.2.1 hf h47
  rcases List.mem_append.mp hmem with h | h
  · exact absurd h h48
  · obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp h
    obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
    have hlfin' : finalListSpine L l := decide_eq_true_iff.mp hlfin
    rw [findListUniq hm.1.2.1.1 hel hlN]
    exact hlfin'

/-! ## §4 HOL AQ12.hl:2322 `one_step_e_list_last_y` -/

/-- **HOL `one_step_e_list_last_y`**（AQ12.hl:2322-:2341）：
`one_step_list L lp (fList L (eList lp))`——第二析取 rfl。 -/
theorem aqs_oneStepEListLastY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    oneStepListSpine L lp (fList L (eList lp)) :=
  Or.inr rfl

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_lastPartsYNotSList
#print axioms Kepler.Text.TameSpine.aqs_lastPartsEListYNotSList
#print axioms Kepler.Text.TameSpine.aqs_existFinalListEList
#print axioms Kepler.Text.TameSpine.aqs_oneStepEListLastY
