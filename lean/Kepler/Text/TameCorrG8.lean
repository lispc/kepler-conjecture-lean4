/-
  Kepler.Text.TameCorrG8 — `tame_correspondence_iso` 三波施工的 **W3 第九波（笔 2）**：
  G8 `tame13a_correspondence`（HOL `WMLNYMD.hl:1360`，本体最大件 113 行 HOL）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrFaceSet`（→ …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**（:1360）：
  `good_list L ∧ good_list_nodes L ∧ all uniq L ∧ tame_9a (hypermap_of_list L) ∧
   tame_13a (hypermap_of_list L) ⇒ tame13a_list L`。
  证体：`tame_13_a_floor` 取 `w`；令 `w' = w ∘ set_of_list ∘ list_pairs`，
  逐槽证 `admissible1/2/3_list w' L`，总量用 `face_set_eq_list` + `sumn_nsum`。

  **Lean 侧与 HOL 的唯一偏差（已论证）**：HOL 的总量槽把
  `sumn_nsum` 用在 `faces_of_list L`（元素是 `Set`）上；Lean 的 `sumnNsum`
  带 `[DecidableEq α]`，而 `Set (ℕ × ℕ)` 无 `DecidableEq`。本文件改走等价路线：
  `sumnNsum` 用在 `L`（`List ℕ`，有 DecidableEq）上，再用
  `BIJ (f ↦ set_of_list (list_pairs f)) : {f | f ∈ L} → faceSet`
  + `BIJNSUM` 换到 `faceSet`（同一条 `sumn` 结论，证明结构等价）。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrFaceSet

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG8

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList Tame9a Tame13a Tame11a Tame11b Tame12o
  setOfFaceMeetingNode setOfTrianglesMeetingNode setOfExceptionalMeetingNode
  typeOfNode GoodListNodesTl flatten_nodup_inj)
open Kepler.Text.TameCorrFloor (facesAtList BIJ BIJNSUM sumnNsum nsum uniqFacesAtList
  Tame13aFloor tame13aFloorTame13a Adm1Floor Adm2Floor Adm3Floor)
open Kepler.Text.TameCorrList (tame13aList admissible1List admissible2List admissible3List
  triList quadList exceptList vertextypeList)
open Kepler.Text.TameCorrNode (dartOf dartOf_fst dartOf_mem_listOfDarts findFaceDarts_dartOf)
open Kepler.Text.TameCorrNodeCard (dartOfCardNode dartOfCardFace)
open Kepler.Text.TameCorrCard (faceOfList)
open Kepler.Text.TameCorrFaceSet (facesOfList faceSetEqList uniqFacesOfList listPairs_ne_nil)
open Kepler.Text.TameCorrG4 (setOfNMeetingNode listPairs_fst)
open Kepler.Text.TameCorrG4b (cardSetOfNMeetingNodePqr typeOfNodeVertextype)
open Kepler.Text.TameCorrG5 (exists_face_of_mem_elements)
open Kepler.Graphs (fgraph squanderFace squanderTarget)

/-- HOL `tame13a_correspondence`（WMLNYMD.hl:1360）：
`good_list L ∧ good_list_nodes L ∧ all uniq L ∧ tame_9a H ∧ tame_13a H ⇒
 tame13a_list L`。 -/
theorem tame13aCorrespondence {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hun : ∀ l ∈ L, l.Nodup)
    (h9 : Tame9a (hypermapOfList L hL))
    (h13 : Tame13a (hypermapOfList L hL)) :
    tame13aList L := by
  have hfloor : Tame13aFloor (hypermapOfList L hL) :=
    tame13aFloorTame13a _ h13 h9
  obtain ⟨w, hadm1, hadm2, hadm3, hweight⟩ := hfloor
  let w' : List ℕ → ℕ := fun f => w {d : ℕ × ℕ | d ∈ listPairs f}
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · -- admissible1_list
    intro f hf
    have hfne : f ≠ [] := hL.2.1 f hf
    have hvmem : f.head hfne ∈ f := List.head_mem hfne
    have hdD : dartOf f (f.head hfne) ∈ listOfDarts L :=
      dartOf_mem_listOfDarts hf hvmem
    have hdH : dartOf f (f.head hfne) ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hdD
    have h1 := hadm1 _ hdH
    have hface : (hypermapOfList L hL).face (dartOf f (f.head hfne))
        = {e : ℕ × ℕ | e ∈ listPairs f} := by
      rw [faceOfList hL hdD, findFaceDarts_dartOf hL hf hvmem]
    have hcard : ((hypermapOfList L hL).face (dartOf f (f.head hfne))).ncard
        = f.length := dartOfCardFace hL hf hvmem
    show squanderFace f.length ≤ w {d : ℕ × ℕ | d ∈ listPairs f}
    rw [← hcard, ← hface]
    exact h1
  · -- admissible2_list
    intro v hv hexc
    obtain ⟨f, hfL, hfv⟩ := exists_face_of_mem_elements hv
    have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfv
    have hdH : dartOf f v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
    have hpqr := cardSetOfNMeetingNodePqr hL hgn (dartOf f v) hdD
    rw [dartOf_fst f v] at hpqr
    have hexc_d : (setOfExceptionalMeetingNode (hypermapOfList L hL) (dartOf f v)).ncard
        = 0 := by
      rw [hpqr.2.2]
      exact hexc
    have h2 := hadm2 _ hdH hexc_d
    rw [hpqr.1, hpqr.2.1] at h2
    have hsum : ((facesAtList L v).map w').sum
        = nsum (setOfFaceMeetingNode (hypermapOfList L hL) (dartOf f v)) w := by
      have hnod : (facesAtList L v).Nodup := uniqFacesAtList hL v
      have hbij : BIJ (fun f : List ℕ => {e : ℕ × ℕ | e ∈ listPairs f})
          {f : List ℕ | f ∈ facesAtList L v}
          (setOfFaceMeetingNode (hypermapOfList L hL) (dartOf f v)) := by
        have h := setOfNMeetingNode hL hgn (dartOf f v) hdD (fun _ => True)
        simpa [dartOf_fst f v, Kepler.Text.TameLp.setOfFaceMeetingNode] using h
      have hbij_sum := BIJNSUM {f : List ℕ | f ∈ facesAtList L v}
        (setOfFaceMeetingNode (hypermapOfList L hL) (dartOf f v)) w
        (fun f : List ℕ => {e : ℕ × ℕ | e ∈ listPairs f}) (List.finite_toSet _) hbij
      rw [sumnNsum (facesAtList L v) w' hnod]
      exact hbij_sum
    rw [hsum]
    exact h2
  · -- admissible3_list
    intro v hv hvt
    obtain ⟨f, hfL, hfv⟩ := exists_face_of_mem_elements hv
    have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfv
    have hdH : dartOf f v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
    have htype : typeOfNode (hypermapOfList L hL) (dartOf f v) = (5, 0, 1) := by
      rw [typeOfNodeVertextype hL hgn (dartOf f v) hdD, dartOf_fst f v]
      exact hvt
    have h3 := hadm3 _ hdH htype
    have hsum : (((facesAtList L v).filter (fun f => f.length == 3)).map w').sum
        = nsum (setOfTrianglesMeetingNode (hypermapOfList L hL) (dartOf f v)) w := by
      have hnod : ((facesAtList L v).filter (fun f => f.length == 3)).Nodup :=
        List.Nodup.filter _ (uniqFacesAtList hL v)
      have hbij : BIJ (fun f : List ℕ => {e : ℕ × ℕ | e ∈ listPairs f})
          {f : List ℕ | f ∈ (facesAtList L v).filter (fun f => f.length == 3)}
          (setOfTrianglesMeetingNode (hypermapOfList L hL) (dartOf f v)) :=
        setOfNMeetingNode hL hgn (dartOf f v) hdD (fun n => n = 3)
      have hbij_sum := BIJNSUM {f : List ℕ |
          f ∈ (facesAtList L v).filter (fun f => f.length == 3)}
        (setOfTrianglesMeetingNode (hypermapOfList L hL) (dartOf f v)) w
        (fun f : List ℕ => {e : ℕ × ℕ | e ∈ listPairs f}) (List.finite_toSet _) hbij
      rw [sumnNsum _ w' hnod]
      exact hbij_sum
    rw [hsum]
    exact h3
  · -- total weight
    have hLn : L.Nodup := List.Nodup.of_map listPairs (uniqFacesOfList hL)
    have hbij : BIJ (fun f : List ℕ => {d : ℕ × ℕ | d ∈ listPairs f})
        {f : List ℕ | f ∈ L} (hypermapOfList L hL).faceSet := by
      refine ⟨?_, ?_, ?_⟩
      · intro f hf
        simp only [Set.mem_setOf_eq] at hf
        rw [faceSetEqList hL]
        change {d : ℕ × ℕ | d ∈ listPairs f}
          ∈ {F : Set (ℕ × ℕ) | F ∈ facesOfList L}
        simp only [Set.mem_setOf_eq]
        unfold facesOfList
        exact List.mem_map.mpr ⟨listPairs f, List.mem_map.mpr ⟨f, hf, rfl⟩, rfl⟩
      · intro f1 hf1 f2 hf2 heq
        simp only [Set.mem_setOf_eq] at hf1 hf2
        have heq' : {d : ℕ × ℕ | d ∈ listPairs f1}
            = {d : ℕ × ℕ | d ∈ listPairs f2} := heq
        have hpl1ne : listPairs f1 ≠ [] := listPairs_ne_nil (hL.2.1 f1 hf1)
        have hd : (listPairs f1).head hpl1ne ∈ listPairs f1 := List.head_mem hpl1ne
        have hd2 : (listPairs f1).head hpl1ne ∈ listPairs f2 := by
          have hdset : (listPairs f1).head hpl1ne
              ∈ {d : ℕ × ℕ | d ∈ listPairs f1} := hd
          rw [heq'] at hdset
          exact hdset
        have hfl : listPairs f1 = listPairs f2 :=
          flatten_nodup_inj hL.1 (List.mem_map.mpr ⟨f1, hf1, rfl⟩)
            (List.mem_map.mpr ⟨f2, hf2, rfl⟩) hd hd2
        have hmap := congrArg (List.map Prod.fst) hfl
        simpa [listPairs_fst] using hmap
      · intro F hF
        rw [faceSetEqList hL] at hF
        simp only [Set.mem_setOf_eq] at hF
        unfold facesOfList at hF
        obtain ⟨g, hg, hgF⟩ := List.mem_map.mp hF
        obtain ⟨l, hlL, rfl⟩ := List.mem_map.mp hg
        refine ⟨l, ?_, ?_⟩
        · simp only [Set.mem_setOf_eq]
          exact hlL
        · simpa using hgF
    have hsumA : (L.map w').sum = nsum {f : List ℕ | f ∈ L} w' :=
      sumnNsum L w' hLn
    have hsumB : nsum {f : List ℕ | f ∈ L} w'
        = nsum (hypermapOfList L hL).faceSet w :=
      BIJNSUM _ _ w _ (List.finite_toSet L) hbij
    rw [hsumA, hsumB]
    exact hweight

end Kepler.Text.TameCorrG8
