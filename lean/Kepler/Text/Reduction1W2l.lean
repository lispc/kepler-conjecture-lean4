/-
  Kepler.Text.Reduction1W2l — J4 Wave W2-4 前两件：`final_face_seed`
  （HOL reduction1.hl:2337，defs-chase）+ `face_iota`（:2345，列表级叶件，
  idxOf-枚举重编号 pattern）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Graphs.Plane
import Kepler.Text.TameSpine.TameList1
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (elementsOfList listOfElements)

/-! ## §1 `final_face_seed`（HOL reduction1.hl:2337） -/

/-- **HOL `final_face_seed`**：`filter SND (faces (Seed p)) =
[upt 0 (maxGon p), T]`（`upt 0 n` ↦ `List.range n`；`SND` ↦ `Face.isFinal`）。 -/
theorem finalFaceSeed (p : ℕ) :
    (Kepler.Graphs.Seed p).faces.filter (fun f : Kepler.Graphs.Face => f.isFinal) =
      [⟨List.range (Kepler.Graphs.maxGon p), true⟩] := by
  simp [Kepler.Graphs.Seed, Kepler.Graphs.graph, Kepler.Graphs.maxGon]

/-! ## §2 `face_iota`（HOL reduction1.hl:2345） -/

/-- `?`-形换装：`v ∈ l ⇒ l[l.idxOf v]? = some v`。 -/
private theorem getOptIdxOf {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    l[l.idxOf v]? = some v :=
  List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_iff.mpr hv,
    List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)⟩

/-- **HOL `face_iota`**：`all uniq L ∧ MEM f0 L ⇒ ∃ phi L'.
isop_list phi (L,[]) (L',[]) ∧ MAP phi f0 = iota 0 (sizel f0)`
（`iota 0 n` ↦ `List.range' 0 n`；`phi` = f0 内 `idxOf` 枚举、f0 外元按
`elements_of_list` 续段）。 -/
theorem faceIota {L : Kepler.Graphs.fgraph ℕ} {f0 : List ℕ}
    (hall : ∀ l ∈ L, l.Nodup) (hf0 : f0 ∈ L) :
    ∃ phi : ℕ → ℕ, ∃ L' : Kepler.Graphs.fgraph ℕ,
      Kepler.Text.TameSpine.IsopListSpine phi L L' [] [] ∧
        f0.map phi = List.range' 0 f0.length := by
  have helsEq : listOfElements L = L.flatten.eraseDups := rfl
  have hf0nodup : f0.Nodup := hall f0 hf0
  have hmemE : ∀ v ∈ f0, v ∈ listOfElements L := fun v hv =>
    List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨f0, hf0, hv⟩)
  set phi : ℕ → ℕ := fun v =>
    if v ∈ f0 then f0.idxOf v else f0.length + (listOfElements L).idxOf v with hphidef
  have hinj : Set.InjOn phi (elementsOfList L) := by
    intro a ha b hb hEq
    have hae : a ∈ listOfElements L := Set.mem_setOf.mp ha
    have hbe : b ∈ listOfElements L := Set.mem_setOf.mp hb
    simp only [hphidef] at hEq
    by_cases ha0 : a ∈ f0
    · by_cases hb0 : b ∈ f0
      · rw [if_pos ha0, if_pos hb0] at hEq
        have hia : f0.idxOf a = f0.idxOf b := by omega
        have hga := getOptIdxOf ha0
        have hgb := getOptIdxOf hb0
        rw [hia] at hga
        exact Option.some.inj (hga.symm.trans hgb)
      · rw [if_pos ha0, if_neg hb0] at hEq
        have hlt : f0.idxOf a < f0.length := List.idxOf_lt_length_iff.mpr ha0
        omega
    · by_cases hb0 : b ∈ f0
      · rw [if_neg ha0, if_pos hb0] at hEq
        have hlt : f0.idxOf b < f0.length := List.idxOf_lt_length_iff.mpr hb0
        omega
      · rw [if_neg ha0, if_neg hb0] at hEq
        have hia : (listOfElements L).idxOf a = (listOfElements L).idxOf b := by omega
        have hga := getOptIdxOf hae
        have hgb := getOptIdxOf hbe
        rw [hia] at hga
        exact Option.some.inj (hga.symm.trans hgb)
  refine ⟨phi, L.map (List.map phi), ⟨hinj, rfl, rfl⟩, ?_⟩
  rw [List.map_congr_left (g := fun v => f0.idxOf v)
    (fun v hv => by simp only [hphidef, if_pos hv])]
  refine List.ext_getElem (by rw [List.length_map, List.length_range']) fun i hi1 hi2 => ?_
  rw [List.getElem_map, List.getElem_range']
  have hi1' : i < f0.length := by rw [List.length_map] at hi1; exact hi1
  have hIdx := hf0nodup.idxOf_getElem i hi1'
  simp [hIdx]

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.finalFaceSeed
#print axioms Kepler.Text.Reduction1.faceIota
