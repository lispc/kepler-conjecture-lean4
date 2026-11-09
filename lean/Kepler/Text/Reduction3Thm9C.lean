/-
  Kepler.Text.Reduction3Thm9C — T9C 支撑层（splitFace_props 的前置件）。

  ┌─ 说明（编排者派工：T9C = splitFace_props 专批）───────────────
  │ splitFace_props(:3339) 本体（~20 前提/~20 结论）在单批预算内未收口；
  │ 按 AGENTS §7 止损：本轮先交**可直接编译的支撑层**，本体组装步骤
  │ 逐条写入 DELIVERY §28（每块 have + 修法），供续派直接续写。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目（支撑层；均 splitFace 定义级/一行级）────────────────────
  │   mem_faces_fgraph（T9C 唯一缺件，~5 行级）→ t9c_mem_fgraph_of_mem_face
  │   splitFace 双面顶点分解（rfl）→ t9c_splitFace_fst_vertices / _snd_vertices
  │   splitFace faces 方程（rfl）→ t9c_splitFace_faces
  │   splitFace faceListAt 长度（= 旧长 + news 长）→ t9c_splitFace_faceListAt_length
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm9B
import Kepler.Text.Reduction3Thm8
import Kepler.Graphs.FaceDivisionProps3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between)

/-! ## §A 缺失支撑：`mem_faces_fgraph`（HOL tame_defs/tame_list 面） -/

/-- HOL `mem_faces_fgraph` 的直接形：`oldF ∈ faces g` 且 `v ∈ FST oldF`
⇒ `v ∈ flatten (fgraph g)`（`fgraph g = MAP FST (faces g)` 定义级）。 -/
theorem t9c_mem_fgraph_of_mem_face {g : Graph} {oldF : Face} {v : ℕ}
    (hf : oldF ∈ g.faces) (hv : v ∈ oldF.vertices) :
    v ∈ g.fgraph.flatten :=
  List.mem_flatten.mpr ⟨oldF.vertices, List.mem_map.mpr ⟨oldF, hf, rfl⟩, hv⟩

/-! ## §B splitFace 定义级分解（供 splitFace_props 组装） -/

/-- `splitFace` 第一面的顶点表（`split_face` 定义级）。
`f1.vertices = news.reverse ++ ([ram1] ++ between oldF.vertices ram1 ram2 ++ [ram2])`。 -/
theorem t9c_splitFace_fst_vertices (g : Graph) (ram₁ ram₂ : ℕ) (oldF : Face)
    (news : List ℕ) :
    (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1.vertices
      = news.reverse ++ ([ram₁] ++ between oldF.vertices ram₁ ram₂ ++ [ram₂]) := rfl

/-- `splitFace` 第二面的顶点表（`split_face` 定义级）。
`f2.vertices = ([ram2] ++ between oldF.vertices ram2 ram1 ++ [ram1]) ++ news`。 -/
theorem t9c_splitFace_snd_vertices (g : Graph) (ram₁ ram₂ : ℕ) (oldF : Face)
    (news : List ℕ) :
    (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1.vertices
      = ([ram₂] ++ between oldF.vertices ram₂ ram₁ ++ [ram₁]) ++ news := rfl

/-- `splitFace` 的图面表（splitFace 定义级）：
`g'.faces = replace oldF [f2] (faces g) ++ [f1]`。 -/
theorem t9c_splitFace_faces (g : Graph) (ram₁ ram₂ : ℕ) (oldF : Face)
    (news : List ℕ) :
    (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faces
      = Kepler.Graphs.replace oldF
          [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.1] g.faces
        ++ [(Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).1] := rfl

/-- `splitFace` 的 `faceListAt` 长度：`|g'.faceListAt| = |g.faceListAt| + |news|`
（四次 `replacefacesAt` 保长 + 尾部 `replicate`）。 -/
theorem t9c_splitFace_faceListAt_length (g : Graph) (ram₁ ram₂ : ℕ)
    (oldF : Face) (news : List ℕ) :
    (Kepler.Graphs.splitFace g ram₁ ram₂ oldF news).2.2.faceListAt.length
      = g.faceListAt.length + news.length := by
  simp only [Kepler.Graphs.splitFace, Kepler.Graphs.replacefacesAt,
    t8_size_mapAt, List.length_append, List.length_replicate]

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9c_mem_fgraph_of_mem_face
#print axioms Kepler.Text.Reduction3.t9c_splitFace_fst_vertices
#print axioms Kepler.Text.Reduction3.t9c_splitFace_snd_vertices
#print axioms Kepler.Text.Reduction3.t9c_splitFace_faces
#print axioms Kepler.Text.Reduction3.t9c_splitFace_faceListAt_length
