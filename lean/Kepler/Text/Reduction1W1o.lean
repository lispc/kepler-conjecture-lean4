/-
  Kepler.Text.Reduction1W1o — J4 Wave W1 批 7b：Ob3
  （`reduction1.hl:1163-:1247` 结论③ `vs = indexToVertexList f v e`）。
  纪律：零公理、零占位证明、零反射式判定。全程 `Nat`。
-/
import Kepler.Text.Reduction1W1j
import Kepler.Text.TameSpine.TameList4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (enumOfVertexList indexToVertexListEnum ImageHideDups)

/-- **Ob3**（HOL `enumeration_vertex_list_lemma` 结论③）：`indexToVertexList` 回读。
本体 = `indexToVertexListEnum`（TameList4:431）直投；本件只做「1a 前提形 →
`indexToVertexListEnum` 前提形」的槽对齐（P17 的 `map get!` 形 ⇒ `filter` 形）。 -/
theorem enumerationVertexListIndexToVertex {f : Kepler.Graphs.Face} {v : Nat}
    {vs : List (Option Nat)}
    (hnd : f.vertices.Nodup) (hv : v ∈ f.vertices) (himg : ImageHideDups vs)
    (hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices) :
    Kepler.Graphs.indexToVertexList f v (enumOfVertexList f.vertices v vs) = vs := by
  refine indexToVertexListEnum hnd hv himg ?_
  intro t ht
  exact hall t.get! (List.mem_map.mpr ⟨t, ht, rfl⟩)

end Kepler.Text.Reduction1

#print axioms Kepler.Text.Reduction1.enumerationVertexListIndexToVertex
