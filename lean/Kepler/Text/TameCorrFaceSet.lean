/-
  Kepler.Text.TameCorrFaceSet — `tame_correspondence_iso` 三波施工的 **W3 第九波（笔 1）**：
  G8 最后两件 List_hypermap 缺件 + `faces_of_list` 载体
  （HOL `list_hypermap.vhl:1090` 族 / `list_hypermap-compiled.hl:26/:863`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrG5`（→ …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**：
  · `faces_of_list L = MAP set_of_list (list_of_faces L)`（compiled.hl:26）↦ `facesOfList`；
  · `uniq_faces_of_list`（compiled.hl:863 `good_list L ==> uniq (list_of_faces L)`）↦
    `uniqFacesOfList`（`(L.map listPairs).Nodup`）；
  · `face_set_eq_list`（vhl:1090 族
    `good_list L ==> face_set (hypermap_of_list L) = set_of_list (faces_of_list L)`）↦
    `faceSetEqList`。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrG5

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrFaceSet

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList findFaceDarts_ex_of_self dart_in_face
  la7_length_listPairs)
open Kepler.Text.TameCorrNode (dartOf dartOf_mem_listOfDarts findFaceDarts_dartOf)
open Kepler.Text.TameCorrCard (faceOfList)
open Kepler.Graphs (fgraph)

/-- HOL `faces_of_list L = MAP set_of_list (list_of_faces L)`（compiled.hl:26）。 -/
def facesOfList (L : fgraph ℕ) : List (Set (ℕ × ℕ)) :=
  (L.map listPairs).map (fun f => {d : ℕ × ℕ | d ∈ f})

/-! ## §1 `uniq_faces_of_list` -/

/-- `list_pairs` 非空（`list_pairs_empty` 的逆否形）。 -/
theorem listPairs_ne_nil {l : List ℕ} (h : l ≠ []) : listPairs l ≠ [] := by
  intro hc
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  rw [hc] at hlen
  have h0 : l.length = 0 := by simpa using hlen.symm
  exact h (List.length_eq_zero_iff.mp h0)

/-- `flatten` 无重复 + 全非空成员 ⇒ 列表本身无重复。 -/
private theorem uniqFlatten {α : Type*} {L : List (List α)}
    (hun : L.flatten.Nodup) (hn : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.flatten_cons] at hun
    obtain ⟨_, h2, h3⟩ := List.nodup_append.mp hun
    rw [List.nodup_cons]
    refine ⟨?_, ih h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx))⟩
    intro ha
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil a (hn a (List.mem_cons_self ..))
    exact (h3 z hz z (List.mem_flatten.mpr ⟨a, ha, hz⟩)) rfl

/-- HOL `uniq_faces_of_list`（list_hypermap-compiled.hl:863）：
`good_list L ⇒ uniq (list_of_faces L)`（`uniq` ↦ `List.Nodup`）。 -/
theorem uniqFacesOfList {L : fgraph ℕ} (hL : GoodList L) :
    (L.map listPairs).Nodup := by
  refine uniqFlatten hL.1 ?_
  intro q hq
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
  exact listPairs_ne_nil (hL.2.1 l hl)

/-! ## §2 `face_set_eq_list` -/

/-- `faceSet` 的成员表示（HOL `face_set` + `set_of_orbits`）。 -/
private theorem mem_faceSet_iff {α : Type*} [DecidableEq α] {H : Hypermap α}
    {F : Set α} :
    F ∈ H.faceSet ↔ ∃ x ∈ H.darts, H.face x = F := by
  simp only [Kepler.Text.Hypermap.faceSet, Kepler.Text.setOfOrbits,
    Kepler.Text.Hypermap.face, Set.mem_setOf_eq]

/-- HOL `face_set_eq_list`（list_hypermap.vhl:1090 族）：
`good_list L ⇒ face_set (hypermap_of_list L) = set_of_list (faces_of_list L)`。 -/
theorem faceSetEqList {L : fgraph ℕ} (hL : GoodList L) :
    (hypermapOfList L hL).faceSet = {F : Set (ℕ × ℕ) | F ∈ facesOfList L} := by
  ext F
  constructor
  · intro hF
    simp only [Set.mem_setOf_eq]
    obtain ⟨x, hxd, hxF⟩ := (mem_faceSet_iff (H := hypermapOfList L hL)).mp hF
    have hxd' : x ∈ listOfDarts L := List.mem_toFinset.mp hxd
    obtain ⟨l, hlL, hfind, _⟩ := findFaceDarts_ex_of_self ((dart_in_face L x).mpr hxd')
    have hFeq : F = {y : ℕ × ℕ | y ∈ listPairs l} := by
      rw [← hxF, faceOfList hL hxd', hfind]
    rw [hFeq]
    unfold facesOfList
    exact List.mem_map.mpr ⟨listPairs l, List.mem_map.mpr ⟨l, hlL, rfl⟩, rfl⟩
  · intro hF
    simp only [Set.mem_setOf_eq] at hF
    unfold facesOfList at hF
    obtain ⟨g, hg, hgF⟩ := List.mem_map.mp hF
    obtain ⟨l, hlL, rfl⟩ := List.mem_map.mp hg
    have hfne : l ≠ [] := hL.2.1 l hlL
    have hvmem : l.head hfne ∈ l := List.head_mem hfne
    have hdD : dartOf l (l.head hfne) ∈ listOfDarts L :=
      dartOf_mem_listOfDarts hlL hvmem
    have hdH : dartOf l (l.head hfne) ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hdD
    rw [mem_faceSet_iff]
    refine ⟨dartOf l (l.head hfne), hdH, ?_⟩
    rw [faceOfList hL hdD, findFaceDarts_dartOf hL hlL hvmem]
    exact hgF

end Kepler.Text.TameCorrFaceSet
