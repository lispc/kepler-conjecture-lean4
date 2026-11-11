/-
  Kepler.Text.Reduction3Thm14f — J5-8 W2-4：C4 `good_faces_transform_lemma`
  （reduction3.hl:3730-3898）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ C4 :3730 `good_faces_transform_lemma` → `goodFacesTransformLemma`
  │ C2 :3452 `all_uniq_faceListAt`  —— **已在库** `t9c2_all_uniq_faceListAt`（T9C2:301）
  │ C3 :3489 `mem_faceListAt`       —— **已在库** `t9d_mem_faceListAt`（9D2:36）
  └────────────────────────────────────────────────────────────────

  **路线（比 HOL 短，零 uniq 面）**：Lean `GoodFacesV3 g'` =
  `∀ v ∈ verticesSet2 g', (facesAtV2 g' v).Perm (g'.facesAt v)`。
  Perm 由 **`List.Subperm.antisymm`** 双向成员等价给；成员等价 = **C3
  `t9d_mem_faceListAt`**；`v < g'.faceListAt.length` 由
  `v ∈ verticesSet2 g'`（= `v < countVertices`，`Graph.vertices = range`）+ `hc'`。
  HOL 的 `Seq.uniq_perm_eq` + `faces_at_v2_uniq` + `all_uniq_faceListAt`
  三段在本路线**零消费**（Lean `GoodFacesV3` 只要求 Perm，不要求 uniq 合取）。
  `g.faces.Nodup`（C3 前提）由 good_list_quotient/good_list_uniq 链内部供
  （与 A3/A4 同款）；K10 的 10 个事实 + `vertices_set2` 等作显式前提（逐状态槽）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm9D2
import Kepler.Text.Reduction3Thm7D
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph replace splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts prevEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans ly lz
    transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **W2-4 C4：HOL `good_faces_transform_lemma`**（reduction3.hl:3730-3898）：
一次 splitFace 后 `good_faces_v3` 保持。 -/
theorem goodFacesTransformLemma (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g g' : Graph) (newVs : List ℕ) (v : ℕ)
    (f f1 f2 : Face)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hgood : Kepler.Text.TameCorrList.GoodFacesV3 g)
    (hndF : f.vertices.Nodup)
    (hmem : f ∈ g.faces)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hfg' : fgraphOfGraph g' = quotientList L (ntrans L N r x 1))
    (hcore : core L r = f.vertices)
    (hprev : (prevEl f.vertices v, v) = x)
    (hc : g.countVertices = g.faceListAt.length)
    (hc' : g'.countVertices = g'.faceListAt.length)
    (hvs : Kepler.Text.TameCorrList.VerticesSet2Eq g)
    (hvs' : Kepler.Text.TameCorrList.VerticesSet2Eq g')
    (hsplit : splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs
      = (f1, f2, g'))
    (hnf1 : f1 ∉ g.faces) (hnf2 : f2 ∉ g.faces)
    (hnews : ∀ j, j ∈ newVs ↔
      g.faceListAt.length ≤ j ∧ j < g'.faceListAt.length)
    (hmap : (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).map (fun d => d.1) = newVs)
    (hr1 : (ytrans L N r x 0).1 ∈ f.vertices)
    (hr2 : (ztrans L N r x 0).1 ∈ f.vertices)
    (hrne : (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1)
    (hall : ∀ l ∈ g.faceListAt, l.Nodup) :
    Kepler.Text.TameCorrList.GoodFacesV3 g' := by
  intro v hv
  -- g.faces.Nodup（good_list_quotient + good_list_uniq 链）
  have hqnd : (quotientList L N).Nodup := by
    have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
      (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
    have hunL : ∀ l ∈ L, l.Nodup :=
      (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
    have hGL : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
      Kepler.Text.TameSpine.goodListQuotient L hL hnS hm.1.edgeNondegenerate hunL
    have hGL' : GoodList (quotientList L N) := by
      rwa [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine L N]
    exact Kepler.Text.TameSpine.goodListUniq (quotientList L N) hGL'
  have hndFaces : g.faces.Nodup := by
    have h2 : (fgraphOfGraph g).Nodup := by rw [hfg]; exact hqnd
    have h3 : (g.faces.map (fun f : Face => f.vertices)).Nodup := by
      simpa only [fgraphOfGraph] using h2
    exact List.Nodup.of_map (fun f : Face => f.vertices) h3
  -- v < g'.faceListAt.length
  have hvlt : v < g'.faceListAt.length := by
    have h1 : v < g'.countVertices := by
      simpa only [Kepler.Text.TameCorrList.verticesSet2, Set.mem_setOf_eq,
        Kepler.Graphs.Graph.vertices, List.mem_range] using hv
    rwa [hc'] at h1
  -- C3：成员等价
  have hmemEq : ∀ h : Face,
      h ∈ g'.facesAt v ↔ h ∈ Kepler.Text.TameCorrList.facesAtV2 g' v := fun h =>
    Kepler.Text.Reduction3.t9d_mem_faceListAt g (ytrans L N r x 0).1
      (ztrans L N r x 0).1 f newVs h v f1 f2 g' hsplit hgood hc hvs hnf1 hnf2
      hnews hmem hndF hndFaces hr1 hr2 hrne hvlt
  -- facesAt_v2 无重（faces_at_v2_uniq）
  have hndV2 : (Kepler.Text.TameCorrList.facesAtV2 g' v).Nodup :=
    Kepler.Text.Reduction3.facesAtV2Uniq L hL hgn (ntrans L N r x 1)
      (haq hgn N r x hm 1).2.1 hir g' v hfg'
  -- C2：all uniq (faceListAt g')
  have hall' : ∀ l ∈ g'.faceListAt, l.Nodup := by
    have h := Kepler.Text.Reduction3.t9c2_all_uniq_faceListAt g
      (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs
    dsimp only at h
    have h2 := h hndF hr1 hr2 hrne hgood hc hvs hmem
      (by rw [hsplit]; exact hnf1) (by rw [hsplit]; exact hnf2)
      hndFaces (by rw [hsplit]; exact hnews) hall
    simpa only [hsplit] using h2
  -- facesAt g' v 无重
  have hndFacesAt : (g'.facesAt v).Nodup := by
    rw [Kepler.Graphs.Graph.facesAt, List.getD_eq_getElem g'.faceListAt [] hvlt]
    exact hall' _ (List.getElem_mem hvlt)
  -- 双向 Subperm ⇒ Perm
  exact List.Subperm.antisymm
    (List.subperm_of_subset hndV2 (fun h hh => (hmemEq h).mpr hh))
    (List.subperm_of_subset hndFacesAt (fun h hh => (hmemEq h).mp hh))

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.goodFacesTransformLemma
