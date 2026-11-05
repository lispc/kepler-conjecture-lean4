/-
  Kepler.Text.TameCorrG4 — `tame_correspondence_iso` 三波施工的 **W3 第六波**：
  G4 首件 `set_of_n_meeting_node`（HOL `WMLNYMD.hl:594`）+ 两个 `list_pairs` 助手。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrNode`（→ TameCorrCard → …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**：
  · `set_of_n_meeting_node`（WMLNYMD.hl:594）：
    `good_list L /\ good_list_nodes L /\ MEM x (list_of_darts L) ==>
      BIJ (set_of_list o list_pairs)
        (set_of_list (FILTER (λf. P(LENGTH f)) (facesAt_list L (FST x))))
        {face (hypermap_of_list L) y | y |
           y IN dart (hypermap_of_list L) /\ P(CARD (face … y)) /\
             y IN node (hypermap_of_list L) x}`
    载体：`P : num -> bool` ↦ `P : ℕ → Prop` + `[DecidablePred P]`（HOL bool =
    命题；filter 侧 `decide (P f.length)`）；`set_of_list ∘ list_pairs` ↦
    `fun f => {d | d ∈ listPairs f}`；`FST x` ↦ `x.1`；`CARD` ↦ `Set.ncard`。
  · 两小助手（W3-W5a 逐下标引擎的收口）：
    - `listPairs_fst`：`(listPairs l).map Prod.fst = l`（HOL `fst_list_pairs` 族）；
    - `mem_list_pairs_exists`：HOL `list_hypermap.mem_list_pairs_exists`（`dartOf` 证人）。

  **证明路线（自证）**：
  BIJ 三合取：maps-to 用 `dartOf f x.1`（`faceOfList` + `cardFaceOfList` +
  `memHypermapOfListNode` 逐槽）；injectivity 用 `findFaceDarts_eq_of_mem` 把
  两个面表合流后 `listPairs_fst` 降回顶点表；surjectivity 用
  `findFaceDarts_ex_of_self` 取面表 `l`，`fst_mem_of_mem_listPairs` 给
  `x.1 ∈ l`，`cardFaceOfList` 搬 `P` 前提。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrNode

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG4

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts nList nextEl GoodList)
open Kepler.Text (Hypermap orbitMap)
open Kepler.Text.TameLp (hypermapOfList faceMap_hypermapOfList nodeMap_hypermapOfList
  dart_in_face findFaceDarts_eq_of_mem findFaceDarts_congr_of_mem findFaceDarts_nodup
  findFaceDarts_ex_of_self mem_darts_of_mem_findFace la7_length_listPairs
  GoodListNodesTl nodesOfListSet)
open Kepler.Text.TameCorrFloor (facesAtList BIJ)
open Kepler.Text.TameCorrNode (memHypermapOfListNode dartOf dartOf_fst
  dartOf_mem_listPairs dartOf_mem_listOfDarts findFaceDarts_dartOf)
open Kepler.Text.TameCorrCard (faceOfList cardFaceOfList memFaceLemma faceTableSubset
  faceOrbitSubset)
open Kepler.Graphs (fgraph)

/-! ## §1 `list_pairs` 两个助手 -/

/-- HOL `fst_list_pairs` 族：`(list_pairs l).map FST = l`。 -/
theorem listPairs_fst (l : List ℕ) : (listPairs l).map Prod.fst = l := by
  have hle : l.length ≤ (l.drop 1 ++ l.take 1).length := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  show (l.zip (l.drop 1 ++ l.take 1)).map Prod.fst = l
  exact List.map_fst_zip hle

/-- HOL `list_hypermap.mem_list_pairs_exists`：`v ∈ f ⇒ ∃y. (v,y) ∈ list_pairs f`。 -/
theorem mem_list_pairs_exists {f : List ℕ} {v : ℕ} (hv : v ∈ f) :
    ∃ y : ℕ, (v, y) ∈ listPairs f :=
  ⟨nextEl f v, by simpa [dartOf] using dartOf_mem_listPairs hv⟩

/-- `list_pairs` 成员的第一个分量必在原表内（`mem_list_pairs_exists` 的对偶消费）。 -/
theorem fst_mem_of_mem_listPairs {l : List ℕ} {d : ℕ × ℕ} (hd : d ∈ listPairs l) :
    d.1 ∈ l := by
  have h : Prod.fst d ∈ (listPairs l).map Prod.fst := List.mem_map.mpr ⟨d, hd, rfl⟩
  rwa [listPairs_fst] at h

/-- `facesAt_list` 的成员刻画：`f ∈ facesAt_list L v ⇔ f ∈ L ∧ v ∈ f`。 -/
theorem mem_facesAtList {L : fgraph ℕ} {v : ℕ} {f : List ℕ} :
    f ∈ facesAtList L v ↔ f ∈ L ∧ v ∈ f := by
  simp [Kepler.Text.TameCorrFloor.facesAtList]

/-! ## §2 G4 首件 `set_of_n_meeting_node`（HOL :594） -/

/-- HOL `set_of_n_meeting_node`（WMLNYMD.hl:594）：
`good_list L ∧ good_list_nodes L ∧ x ∈ list_of_darts L ⇒
 BIJ (set_of_list ∘ list_pairs) (set_of_list (filter (P ∘ length) (facesAt_list L x.1)))
   {face (hypermap_of_list L) y | y ∈ dart ∧ P (CARD (face y)) ∧ y ∈ node x}`。 -/
theorem setOfNMeetingNode {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (x : ℕ × ℕ) (hx : x ∈ listOfDarts L)
    (P : ℕ → Prop) [DecidablePred P] :
    BIJ (fun f : List ℕ => {d : ℕ × ℕ | d ∈ listPairs f})
      {f : List ℕ | f ∈ (facesAtList L x.1).filter (fun f => decide (P f.length))}
      {F : Set (ℕ × ℕ) |
        ∃ y ∈ (hypermapOfList L hL).darts,
          F = (hypermapOfList L hL).face y ∧
            P ((hypermapOfList L hL).face y).ncard ∧
              y ∈ (hypermapOfList L hL).node x} := by
  refine ⟨?_, ?_, ?_⟩
  · -- maps-to
    rintro f hf
    simp only [Set.mem_setOf_eq] at hf
    obtain ⟨hfmem, hP⟩ := List.mem_filter.mp hf
    obtain ⟨hfL, hfx⟩ := mem_facesAtList.mp hfmem
    have hdD : dartOf f x.1 ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfx
    have hdH : dartOf f x.1 ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hdD
    have hfst : (dartOf f x.1).1 = x.1 := dartOf_fst f x.1
    have hfind : findFaceDarts L (dartOf f x.1) = listPairs f :=
      findFaceDarts_dartOf hL hfL hfx
    refine ⟨dartOf f x.1, hdH, ?_, ?_, ?_⟩
    · rw [faceOfList hL hdD, hfind]
    · rw [cardFaceOfList hL hdD, hfind, la7_length_listPairs]
      exact of_decide_eq_true hP
    · rw [memHypermapOfListNode hL hgn hx]
      exact ⟨hfst.symm, hdD⟩
  · -- injectivity
    intro f1 hf1 f2 hf2 heq
    simp only [Set.mem_setOf_eq] at hf1 hf2
    obtain ⟨hf1mem, _⟩ := List.mem_filter.mp hf1
    obtain ⟨hf2mem, _⟩ := List.mem_filter.mp hf2
    obtain ⟨hf1L, hf1x⟩ := mem_facesAtList.mp hf1mem
    obtain ⟨hf2L, _⟩ := mem_facesAtList.mp hf2mem
    have hd1 : dartOf f1 x.1 ∈ listPairs f1 := dartOf_mem_listPairs hf1x
    have hmem1 : dartOf f1 x.1 ∈ {d : ℕ × ℕ | d ∈ listPairs f1} := hd1
    have heq' : {d : ℕ × ℕ | d ∈ listPairs f1} = {d : ℕ × ℕ | d ∈ listPairs f2} := heq
    rw [heq'] at hmem1
    have hmem2 : dartOf f1 x.1 ∈ listPairs f2 := hmem1
    have hfind1 : findFaceDarts L (dartOf f1 x.1) = listPairs f1 :=
      findFaceDarts_dartOf hL hf1L hf1x
    have hfind2 : findFaceDarts L (dartOf f1 x.1) = listPairs f2 :=
      findFaceDarts_eq_of_mem hL.1 hf2L hmem2
    have hpl : listPairs f1 = listPairs f2 := by rw [← hfind1, hfind2]
    have hmap := congrArg (List.map Prod.fst) hpl
    simpa [listPairs_fst] using hmap
  · -- surjectivity
    rintro F ⟨y, hyD, rfl, hP, hyx⟩
    have hyd : y ∈ listOfDarts L := List.mem_toFinset.mp hyD
    have hyx' : x.1 = y.1 ∧ y ∈ listOfDarts L :=
      (memHypermapOfListNode hL hgn hx).mp hyx
    obtain ⟨l, hlL, hfind, hyl⟩ :=
      findFaceDarts_ex_of_self ((dart_in_face L y).mpr hyd)
    have hylmem : y.1 ∈ l := fst_mem_of_mem_listPairs hyl
    have hxl : x.1 ∈ l := by rw [hyx'.1]; exact hylmem
    have hlen : (findFaceDarts L y).length = l.length := by
      rw [hfind, la7_length_listPairs]
    have hPl : P l.length := by
      have := hP
      rw [cardFaceOfList hL hyd, hlen] at this
      exact this
    refine ⟨l, ?_, ?_⟩
    · -- l ∈ filter (P ∘ length) (facesAt_list L x.1)
      simp only [Set.mem_setOf_eq]
      exact List.mem_filter.mpr ⟨mem_facesAtList.mpr ⟨hlL, hxl⟩, decide_eq_true hPl⟩
    · -- ab l = face y
      show {d : ℕ × ℕ | d ∈ listPairs l} = (hypermapOfList L hL).face y
      rw [faceOfList hL hyd, hfind]


/-! ## §3 续件 `card_set_of_n_meeting_node`（HOL :691） -/

/-- HOL `card_set_of_n_meeting_node`（WMLNYMD.hl:691）：
BIJ 的基数形式——`CARD {face (hypermap_of_list L) y | …} =
LENGTH (filter (P ∘ LENGTH) (facesAt_list L (FST x)))`。 -/
theorem cardSetOfNMeetingNode {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (x : ℕ × ℕ) (hx : x ∈ listOfDarts L)
    (P : ℕ → Prop) [DecidablePred P] :
    {F : Set (ℕ × ℕ) |
        ∃ y ∈ (hypermapOfList L hL).darts,
          F = (hypermapOfList L hL).face y ∧
            P ((hypermapOfList L hL).face y).ncard ∧
              y ∈ (hypermapOfList L hL).node x}.ncard
      = ((facesAtList L x.1).filter (fun f => decide (P f.length))).length := by
  let lf : List (List ℕ) := (facesAtList L x.1).filter (fun f => decide (P f.length))
  let S : Set (List ℕ) := {f | f ∈ lf}
  let T : Set (Set (ℕ × ℕ)) :=
    {F | ∃ y ∈ (hypermapOfList L hL).darts,
      F = (hypermapOfList L hL).face y ∧
        P ((hypermapOfList L hL).face y).ncard ∧
          y ∈ (hypermapOfList L hL).node x}
  have hbij : BIJ (fun f : List ℕ => {d : ℕ × ℕ | d ∈ listPairs f}) S T :=
    setOfNMeetingNode hL hgn x hx P
  have hT : T = (fun f : List ℕ => {d : ℕ × ℕ | d ∈ listPairs f}) '' S := by
    ext F
    constructor
    · intro hF
      obtain ⟨f, hfS, hfF⟩ := hbij.2.2 F hF
      exact ⟨f, hfS, hfF⟩
    · rintro ⟨f, hfS, hfF⟩
      rw [← hfF]
      exact hbij.1 f hfS
  have hcard : T.ncard = S.ncard := by
    rw [hT]
    exact Set.InjOn.ncard_image hbij.2.1
  have hSlen : S.ncard = lf.length := by
    have hnod : lf.Nodup :=
      List.Nodup.filter _ (Kepler.Text.TameCorrFloor.uniqFacesAtList hL x.1)
    have hset : S = (lf.toFinset : Set (List ℕ)) := by
      change {f : List ℕ | f ∈ lf} = _
      ext f
      simp
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnod]
  show T.ncard = lf.length
  rw [hcard, hSlen]

end Kepler.Text.TameCorrG4
