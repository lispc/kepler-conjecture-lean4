/-
  Kepler.Text.Reduction1W2b — J4 Wave W2 批 1b（编排者按车道探针结论收口）：
  `generatePolygon_criteria`（HOL reduction1.hl:1385-1420）。

  消费 W1 验收点 `enumeration_vertex_list`（`e5094b9d`）：见证 `e`
  （枚举成员 + `containsDuplicateEdge = false` + `vs = indexToVertexList f v e`），
  再按 `generatePolygon` 的 filter/map 链直投。

  载体判定（编排者核 HOL `tame_defs2.hl:355-390`）：Lean `subdivFace'` 即
  HOL `subdivFace0`（Graph 终点形），Lean `subdivFace` 即 HOL `subdivFace`。
  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W1p
import Kepler.Graphs.Plane

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (listOfDarts listPairs prevEl)
open Kepler.Graphs (Graph Face generatePolygon subdivFace indexToVertexList)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)
open Kepler.Text.TameSpine (indexf)

/-- **HOL `generatePolygon_criteria`**（reduction1.hl:1385）：wrapper 12 前提
⇒ `subdivFace g f vs ∈ generatePolygon vs.length v f g`。 -/
theorem generatePolygonCriteria {g : Graph} {f : Face} {v : Nat}
    {vs : List (Option Nat)} {vs' : List Nat}
    (hvs' : (vs.filter Option.isSome).map Option.get! = vs')
    (h3 : 3 ≤ vs.length)
    (hhd : vs.head! = some v)
    (hlastSome : (vs.getLast!).isSome = true)
    (hprev : prevEl f.vertices v = vs.getLast!.getD 0)
    (hfm : f.vertices ∈ g.fgraph)
    (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g)
    (hvs2 : VerticesSet2Eq g)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices)
    (hmono : ∀ i, i + 1 < vs'.length →
      indexf v vs'[i]! f.vertices < indexf v vs'[i + 1]! f.vertices)
    (hP19 : ∀ (i : Nat) (d : Nat × Nat), i + 1 < vs.length →
      (vs[i]!).isSome = true → (vs[i + 1]!).isSome = true →
      d ∈ listOfDarts g.fgraph → d ∈ listPairs f.vertices) :
    subdivFace g f vs ∈ generatePolygon vs.length v f g := by
  obtain ⟨e, hmem, hcontain, hvsE⟩ :=
    enumerationVertexList hvs' h3 hhd hlastSome hprev hfm hun hgf hvs2 hall hmono hP19
  have hsub : subdivFace g f vs = subdivFace g f (indexToVertexList f v e) := by
    rw [hvsE]
  rw [hsub]
  unfold Kepler.Graphs.generatePolygon
  refine List.mem_map.mpr ⟨indexToVertexList f v e, ?_, rfl⟩
  refine List.mem_map.mpr ⟨e, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hmem, by rw [hcontain]; rfl⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.generatePolygonCriteria
