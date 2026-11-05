/-
  Kepler.Text.TameCorrG5 — `tame_correspondence_iso` 三波施工的 **W3 第八波 b**：
  G5 两件（HOL `WMLNYMD.hl:757` / `:813`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrNodeCard`（→ …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**（`:757`）：
  `good_list L ∧ good_list_nodes L ∧ all uniq L ∧
   tame_11a (hypermap_of_list L) ∧ tame_11b (hypermap_of_list L) ∧
   tame_12o (hypermap_of_list L) ⇒ tame11a_list L ∧ tame11b_list L`
  （`:813`）：`good_list L ∧ good_list_nodes L ∧ all uniq L ∧
   tame_12o (hypermap_of_list L) ⇒ tame12o_list L`。
  载体：`tame_11a/11b/12o` ↦ `TameLp.Tame11a/11b/12o`；
  `all uniq L` ↦ `∀ l ∈ L, l.Nodup`；`dart_of` ↦ `TameCorrNode.dartOf`；
  `CARD(node …)` ↔ `LENGTH (facesAt_list L v)` 由 W3-W8a `dartOfCardNode` 供。

  **证明路线（自证）**：
  - `tame11a_list`：`v ∈ elements_of_list` ⇒ 取 `f ∈ L ∋ v`，`d = dartOf f v`；
    `tame_11a` 在 `d` 给 `3 ≤ CARD(node d)`，`dartOfCardNode` 换成
    `CARD(node d) = LENGTH (facesAt_list L v)`。
  - `tame11b_list`：`except_list L v = 0` 支用 `tame_11b`（≤7）+ 换卡；
    否则取例外面 `x`（`5 ≤ LENGTH x`），在 `d' = dartOf x v` 上
    `tame_12o` 的 `node_exceptional_face` 给 `CARD(node d') ≤ 6`，
    再用 `dartOfCardNode` 换成 `LENGTH (facesAt_list L v)`。
  - `tame12o_list`：例外面 `x` 的 `d' = dartOf x v` 有 `5 ≤ CARD(face d')` 与
    `CARD(node d') = 6`（第 3 合取），`node_type_exceptional_face` 给
    `type_of_node d' = (5,0,1)`，`typeOfNodeVertextype`（W3-W7）降回
    `vertextype_list L v`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrNodeCard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG5

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList elementsOfList listOfElements
  Tame11a Tame11b Tame12o NodeExceptionalFace NodeTypeExceptionalFace
  ExceptionalFace typeOfNode GoodListNodesTl)
open Kepler.Text.TameCorrFloor (facesAtList)
open Kepler.Text.TameCorrList (tame11aList tame11bList tame12oList exceptList vertextypeList)
open Kepler.Text.TameCorrNode (dartOf dartOf_fst dartOf_mem_listOfDarts)
open Kepler.Text.TameCorrNodeCard (dartOfCardNode dartOfCardFace)
open Kepler.Text.TameCorrG4 (mem_facesAtList)
open Kepler.Text.TameCorrG4b (typeOfNodeVertextype)
open Kepler.Graphs (fgraph)

/-! ## §1 公共助手 -/

/-- `v ∈ elements_of_list L` ⇒ 存在含 `v` 的面 `f ∈ L`。 -/
theorem exists_face_of_mem_elements {L : fgraph ℕ} {v : ℕ}
    (hv : v ∈ elementsOfList L) : ∃ f : List ℕ, f ∈ L ∧ v ∈ f := by
  have hv' : v ∈ L.flatten := by
    have h := hv
    simp only [Kepler.Text.TameLp.elementsOfList, Kepler.Text.TameLp.listOfElements,
      Set.mem_setOf_eq, List.mem_eraseDups] at h
    exact h
  exact List.mem_flatten.mp hv'

/-- `except_list L v ≠ 0` ⇒ 存在面 `f ∈ facesAt_list L v` 且 `5 ≤ LENGTH f`。 -/
theorem exists_exceptional_face {L : fgraph ℕ} {v : ℕ}
    (hexc : exceptList L v ≠ 0) :
    ∃ f : List ℕ, f ∈ facesAtList L v ∧ 5 ≤ f.length := by
  have hlen : ((facesAtList L v).filter (fun f => decide (5 ≤ f.length))).length ≠ 0 := hexc
  have hne : (facesAtList L v).filter (fun f => decide (5 ≤ f.length)) ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hfm, hP⟩ := List.mem_filter.mp hf
  exact ⟨f, hfm, of_decide_eq_true hP⟩

/-! ## §2 G5 两件 -/

/-- HOL `tame11_correspondence`（WMLNYMD.hl:757）：
`… ⇒ tame11a_list L ∧ tame11b_list L`。 -/
theorem tame11Correspondence {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hun : ∀ l ∈ L, l.Nodup)
    (h11a : Tame11a (hypermapOfList L hL))
    (h11b : Tame11b (hypermapOfList L hL))
    (h12o : Tame12o (hypermapOfList L hL)) :
    tame11aList L ∧ tame11bList L := by
  refine ⟨?_, ?_⟩
  · -- tame11a_list
    intro v hv
    obtain ⟨f, hfL, hfv⟩ := exists_face_of_mem_elements hv
    have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfv
    have hdH : dartOf f v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
    have h3 : 3 ≤ ((hypermapOfList L hL).node (dartOf f v)).ncard := h11a _ hdH
    have hcard : ((hypermapOfList L hL).node (dartOf f v)).ncard
        = (facesAtList L v).length :=
      dartOfCardNode hL hgn hun hdD (dartOf_fst f v)
    rwa [hcard] at h3
  · -- tame11b_list
    intro v hv
    by_cases hexc : exceptList L v = 0
    · -- 非例外面：tame_11b 给 ≤ 7
      obtain ⟨f, hfL, hfv⟩ := exists_face_of_mem_elements hv
      have hdD : dartOf f v ∈ listOfDarts L := dartOf_mem_listOfDarts hfL hfv
      have hdH : dartOf f v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
      have h7 : ((hypermapOfList L hL).node (dartOf f v)).ncard ≤ 7 := h11b _ hdH
      have hcard : ((hypermapOfList L hL).node (dartOf f v)).ncard
          = (facesAtList L v).length :=
        dartOfCardNode hL hgn hun hdD (dartOf_fst f v)
      rw [if_pos hexc, ← hcard]
      exact h7
    · -- 有例外面：tame_12o 的 node_exceptional_face 给 ≤ 6
      obtain ⟨g, hgf, hg5⟩ := exists_exceptional_face (L := L) (v := v) hexc
      have hgL : g ∈ L := (mem_facesAtList.mp hgf).1
      have hgv : v ∈ g := (mem_facesAtList.mp hgf).2
      have hdD : dartOf g v ∈ listOfDarts L := dartOf_mem_listOfDarts hgL hgv
      have hdH : dartOf g v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
      have hface5 : ExceptionalFace (hypermapOfList L hL) (dartOf g v) := by
        show 5 ≤ ((hypermapOfList L hL).face (dartOf g v)).ncard
        rw [dartOfCardFace hL hgL hgv]
        exact hg5
      have hnode6 : ((hypermapOfList L hL).node (dartOf g v)).ncard ≤ 6 :=
        (h12o _ hdH).2 hface5
      have hcard : ((hypermapOfList L hL).node (dartOf g v)).ncard
          = (facesAtList L v).length :=
        dartOfCardNode hL hgn hun hdD (dartOf_fst g v)
      rw [if_neg hexc, ← hcard]
      exact hnode6

/-- HOL `tame12o_correspondence`（WMLNYMD.hl:813）：
`… ⇒ tame12o_list L`。 -/
theorem tame12oCorrespondence {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hun : ∀ l ∈ L, l.Nodup)
    (h12o : Tame12o (hypermapOfList L hL)) :
    tame12oList L := by
  intro v hv
  obtain ⟨_hvmem, hexc, hdeg⟩ := hv
  obtain ⟨g, hgf, hg5⟩ := exists_exceptional_face (L := L) (v := v) hexc
  have hgL : g ∈ L := (mem_facesAtList.mp hgf).1
  have hgv : v ∈ g := (mem_facesAtList.mp hgf).2
  have hdD : dartOf g v ∈ listOfDarts L := dartOf_mem_listOfDarts hgL hgv
  have hdH : dartOf g v ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hdD
  have hface5 : ExceptionalFace (hypermapOfList L hL) (dartOf g v) := by
    show 5 ≤ ((hypermapOfList L hL).face (dartOf g v)).ncard
    rw [dartOfCardFace hL hgL hgv]
    exact hg5
  have hnode6 : ((hypermapOfList L hL).node (dartOf g v)).ncard = 6 := by
    rw [dartOfCardNode hL hgn hun hdD (dartOf_fst g v)]
    exact hdeg
  have htype : typeOfNode (hypermapOfList L hL) (dartOf g v) = (5, 0, 1) :=
    (h12o _ hdH).1 ⟨hface5, hnode6⟩
  rw [← dartOf_fst g v, ← typeOfNodeVertextype hL hgn (dartOf g v) hdD]
  exact htype

end Kepler.Text.TameCorrG5
