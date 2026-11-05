/-
  Kepler.Text.TameCorrG3 — `tame_correspondence_iso` 三波施工的 **W3 第三波**：
  `reference/flyspeck/text_formalization/tame/WMLNYMD.hl` 的 **G3（admissible 权重表，
  8 件 prove，HOL :421-:600）**。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrList`（→ TameCorrFloor → TameLp +
  │ Graphs.Tame，另 Graphs.RelativeCompleteness）。闭包零 `Kepler.Assembly`。
  │ 环自检（编排者复跑同款）：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 逐件对照**（载体折算：`sumn` ↦ `List.sum`；`rot n f` ↦ `List.rotate`；
  `perm_eq` ↦ `List.Perm`；`admissible'` ↦ `Kepler.Graphs.admissible`
  （HOL `admissible1∧2∧3` 三合取，与 Lean `admissible` 同体）；
  `(w o FST)` ↦ `fun f => w f.vertices`；`FST f` ↦ `f.vertices`；
  `squanderTarget/excessTCount/squanderVertex` ↦ `Kepler.Graphs.*`。
  `tame13a`（HOL `import_tame_classification.hl:113-114`）↦
  `Kepler.Graphs.tame13a : Graph → Prop`（同一 `∃w` 形）。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG3

open Classical
open Kepler.Graphs
open Kepler.Text.TameLp (elementsOfList)
open Kepler.Text.TameCorrFloor (facesAtList)
open Kepler.Text.TameCorrList

/-! ## §1 求和助手（HOL :435 / :446） -/

/-- HOL `sumn_rot`（WMLNYMD.hl:435）：`sumn (rot n f) = sumn f`。
Lean 载体 `List.rotate`（约定 `splitAt (n % length)`；与 ssreflect `rot` 的
`drop n ++ take n` 在 `n ≤ length` 时同值，且两者都保和）。 -/
theorem sumnRot (f : List ℕ) (n : ℕ) : (f.rotate n).sum = f.sum :=
  (List.rotate_perm f n).sum_eq

/-- HOL `sumn_perm_eq`（WMLNYMD.hl:446）：`perm_eq f g ==> sumn f = sumn g`。
HOL 证体走 `rot_to` 归约到 `sumn_rot`；Lean 直接取 `List.Perm.sum_eq`。 -/
theorem sumnPermEq {f g : List ℕ} (h : f.Perm g) : f.sum = g.sum :=
  h.sum_eq

/-- HOL `sumn_facesAt`（WMLNYMD.hl:474）：
`good_graph_v4 g ∧ v ∈ vertices_set2 g ⇒ sumn (MAP w (facesAt_v2 g v)) = sumn (MAP w (facesAt g v))`。 -/
theorem sumnFacesAt {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) (w : Face → ℕ) :
    ((facesAtV2 g v).map w).sum = ((g.facesAt v).map w).sum :=
  ((goodGraphPermEqFacesAt hgg hv).map w).sum_eq

/-! ## §2 admissible 对应（HOL :421 / :492 / :521） -/

/-- `v ∈ vertices_set2 g` → `v ∈ elements_of_list (fgraph g)`（`good_graph_v4` 第 6 合取）。 -/
private theorem mem_elementsOfList_of_mem_vertices {g : Graph} {v : Vertex}
    (hgg : GoodGraphV4 g) (hv : v ∈ g.vertices) : v ∈ elementsOfList g.fgraph := by
  rw [← hgg.2.2.2.2.2]
  exact hv

/-- HOL `admissible1_list_admissible1`（WMLNYMD.hl:421）：
`admissible1_list w (fgraph g) ==> admissible1 (w o FST) g`。 -/
theorem admissible1ListAdmissible1 {g : Graph} {w : List ℕ → ℕ}
    (h : admissible1List w g.fgraph) : admissible₁ (fun f => w f.vertices) g := by
  intro f hf
  exact h f.vertices (List.mem_map.mpr ⟨f, hf, rfl⟩)

/-- HOL `admissible2_list_admissible2`（WMLNYMD.hl:492）：
`good_graph_v4 g ∧ admissible2_list w (fgraph g) ==> admissible2 (w o FST) g`。 -/
theorem admissible2ListAdmissible2 {g : Graph} {w : List ℕ → ℕ}
    (hgg : GoodGraphV4 g) (h : admissible2List w g.fgraph) :
    admissible₂ (fun f => w f.vertices) g := by
  intro v hv hexc
  have hv' : v ∈ elementsOfList g.fgraph := mem_elementsOfList_of_mem_vertices hgg hv
  have hexc' : exceptList g.fgraph v = 0 := by
    rw [exceptListExcept hgg hv]
    exact hexc
  have h2 := h v hv' hexc'
  rw [triListTri hgg hv, quadListQuad hgg hv] at h2
  rw [← facesAt2List hgg hv, List.map_map] at h2
  rw [sumnFacesAt hgg hv (w ∘ Face.vertices)] at h2
  exact h2

/-- HOL `admissible3_list_admissible3`（WMLNYMD.hl:521）：
`good_graph_v4 g ∧ admissible3_list w (fgraph g) ==> admissible3 (w o FST) g`。 -/
theorem admissible3ListAdmissible3 {g : Graph} {w : List ℕ → ℕ}
    (hgg : GoodGraphV4 g) (h : admissible3List w g.fgraph) :
    admissible₃ (fun f => w f.vertices) g := by
  intro v hv hvt
  have hv' : v ∈ elementsOfList g.fgraph := mem_elementsOfList_of_mem_vertices hgg hv
  have hvt' : vertextypeList g.fgraph v = (5, 0, 1) := by
    rw [vertextypeListVertextype hgg hv]
    exact hvt
  have h3 := h v hv' hvt'
  have hperm : ((facesAtV2 g v).filter triangle).Perm
      ((g.facesAt v).filter triangle) :=
    (goodGraphPermEqFacesAt hgg hv).filter triangle
  have hsum_eq : (((facesAtV2 g v).filter triangle).map (fun f => w f.vertices)).sum =
      (((g.facesAt v).filter triangle).map (fun f => w f.vertices)).sum :=
    (hperm.map (fun f => w f.vertices)).sum_eq
  calc excessTCount
      ≤ (((facesAtList g.fgraph v).filter (fun l => l.length == 3)).map w).sum := h3
    _ = ((((facesAtV2 g v).filter (fun f => f.vertices.length == 3)).map
            Face.vertices).map w).sum := by
          rw [goodTypeFilter hgg hv (fun n => n == 3)]
    _ = (((facesAtV2 g v).filter (fun f => f.vertices.length == 3)).map
            (fun f => w f.vertices)).sum := by
          rw [List.map_map]
          rfl
    _ = (((g.facesAt v).filter triangle).map (fun f => w f.vertices)).sum := hsum_eq

/-! ## §3 tame13a_list ⇒ tame13a（HOL :555 / :574） -/

/-- HOL `tame13a_list_tame13a_lemma`（WMLNYMD.hl:555）。 -/
theorem tame13aListTame13aLemma {g : Graph} (hgg : GoodGraphV4 g)
    (h : tame13aList g.fgraph) :
    ∃ w : List ℕ → ℕ, admissible (fun f => w f.vertices) g ∧
      (g.faces.map (fun f => w f.vertices)).sum < squanderTarget := by
  obtain ⟨w, h1, h2, h3, hsum⟩ := h
  refine ⟨w, ⟨admissible1ListAdmissible1 h1, admissible2ListAdmissible2 hgg h2,
    admissible3ListAdmissible3 hgg h3⟩, ?_⟩
  have hmapeq : (g.faces.map (fun f => w f.vertices)) = g.fgraph.map w := by
    rw [Graph.fgraph, List.map_map]
    rfl
  rw [hmapeq]
  exact hsum

/-- HOL `tame13a_list_tame13a`（WMLNYMD.hl:574）：
`good_graph_v4 g ∧ tame13a_list (fgraph g) ==> tame13a g`。 -/
theorem tame13aListTame13a {g : Graph} (hgg : GoodGraphV4 g)
    (h : tame13aList g.fgraph) : tame13a g := by
  obtain ⟨w, hadm, hsum⟩ := tame13aListTame13aLemma hgg h
  exact ⟨fun f => w f.vertices, hadm, hsum⟩

end Kepler.Text.TameCorrG3
