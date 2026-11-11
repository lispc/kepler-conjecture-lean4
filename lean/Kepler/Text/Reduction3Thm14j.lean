/-
  Kepler.Text.Reduction3Thm14j — J5-8 W5：C4 前提包
  `goodFacesTransformLemmaPremises`（reduction3.hl:3810-3893 内部推导的 8 条）。

  ┌─ 归属对账（HOL Light Flyspeck reduction3.hl）────────────────────
  │ C4 `good_faces_transform_lemma`（:3730-3898）在 HOL 证体内部一次性推完
  │ 8 条事实；Lean 落 `goodFacesTransformLemma`（T14f:47）时把它们提升为
  │ 显式前提。本件把这 8 条包成一个 8 元合取定理，供 `mainInduction` 消费：
  │   hndF  : FST f 无重          （marked_list 的 quotient 无重槽）
  │   hnf1  : f1 ∉ faces g        （K10 的 split_normal_list 非成员 + split_face）
  │   hnf2  : f2 ∉ faces g        （同上）
  │   hnews : newVs = 新顶点段     （K10 range' 等式 + splitFace 计数）
  │   hall  : all uniq (faceListAt g)（good_faces_v3 + faces Nodup + filter）
  │   hr1/hr2/hrne                （K10 直供，本件原样携入）
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14g
import Kepler.Text.Reduction3Thm14e
import Kepler.Text.Reduction3Thm12
import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts prevEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans splitNormalList
    coreSplitNormalList transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **J5-8 W5：C4 的 8 条提升前提**（reduction3.hl:3810-3893 内部推导）。 -/
theorem goodFacesTransformLemmaPremises
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (g g' : Graph) (newVs : List ℕ) (v : ℕ) (f f1 f2 : Face)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hfin : ¬ finalList L r)
    (hgood : Kepler.Text.TameCorrList.GoodFacesV3 g)
    (hmem : f ∈ g.faces)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hcore : core L r = f.vertices)
    (hc : g.countVertices = g.faceListAt.length)
    (hc' : g'.countVertices = g'.faceListAt.length)
    (hvs : Kepler.Text.TameCorrList.VerticesSet2Eq g)
    (hsplit : splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs
      = (f1, f2, g'))
    (hmap : (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).map (fun d => d.1) = newVs)
    (hnewVs : List.range' g.countVertices
      (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).length = newVs)
    (hprevFst : (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1)
    (hcs : coreSplitNormalList L N r x)
    (hsplitNF : core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).1 ∉ quotientList L N ∧
      core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).2 ∉ quotientList L N)
    (hr1 : (ytrans L N r x 0).1 ∈ f.vertices)
    (hr2 : (ztrans L N r x 0).1 ∈ f.vertices)
    (hrne : (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1) :
    f.vertices.Nodup ∧ f1 ∉ g.faces ∧ f2 ∉ g.faces ∧
      (∀ j, j ∈ newVs ↔ g.faceListAt.length ≤ j ∧ j < g'.faceListAt.length) ∧
      (∀ l ∈ g.faceListAt, l.Nodup) ∧
      (ytrans L N r x 0).1 ∈ f.vertices ∧
      (ztrans L N r x 0).1 ∈ f.vertices ∧
      (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 := by
  -- ① f.vertices ∈ quotientList：经 fgraph g
  have hfq : f.vertices ∈ quotientList L N := by
    rw [← hfg]
    exact List.mem_map.mpr ⟨f, hmem, rfl⟩
  -- ② hndF：marked_list 的 all-uniq 槽
  have hndF : f.vertices.Nodup := hm.2.2.2.2.1.1 f.vertices hfq
  -- ③ g.faces.Nodup：fgraph g = quotient_list ⇒ 外层无重 ⇒ of_map
  have hqnd : (quotientList L N).Nodup :=
    Kepler.Text.Reduction3.t12_marked_list_uniq_quotient L hL hgn N r x hm hir
  have hndFaces : g.faces.Nodup := by
    have h2 : (fgraphOfGraph g).Nodup := by rw [hfg]; exact hqnd
    have h3 : (g.faces.map (fun f : Face => f.vertices)).Nodup := by
      simpa only [fgraphOfGraph] using h2
    exact List.Nodup.of_map (fun f : Face => f.vertices) h3
  -- ④ hnf1 / hnf2：K10 的 split_normal_list 非成员 + split_face 定义
  let s := splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
    (prevEl r (ztrans L N r x 0))
  have hface : f = Face.mk (core L r) f.isFinal := by
    cases f with
    | mk vs isFin =>
      rw [hcore]
  have hsp := splitNormalListSplitFace L N r x v s.1 s.2 f.isFinal newVs
    hL hgn hm hir hfin (by rfl) hprevFst hmap hcs
  rw [← hface] at hsp
  -- hsp : split_face f y z newVs = (Face.mk (core L s.1) false, Face.mk (core L s.2) false)
  have hf1eq : f1 = (split_face f (ytrans L N r x 0).1 (ztrans L N r x 0).1 newVs).1 := by
    have h1 : f1 = (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).1 :=
      congrArg Prod.fst hsplit.symm
    rw [h1]
    rfl
  have hf2eq : f2 = (split_face f (ytrans L N r x 0).1 (ztrans L N r x 0).1 newVs).2 := by
    have h1 : f2 = (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2.1 :=
      congrArg (fun p => p.2.1) hsplit.symm
    rw [h1]
    rfl
  have hf1v : f1.vertices = core L s.1 := by
    rw [hf1eq]
    simpa only [Kepler.Graphs.Face.vertices] using
      congrArg (fun p => p.1.vertices) hsp
  have hf2v : f2.vertices = core L s.2 := by
    rw [hf2eq]
    simpa only [Kepler.Graphs.Face.vertices] using
      congrArg (fun p => p.2.vertices) hsp
  have hnf1 : f1 ∉ g.faces := by
    intro hmem1
    have hvq : f1.vertices ∈ quotientList L N := by
      rw [← hfg]
      exact List.mem_map.mpr ⟨f1, hmem1, rfl⟩
    exact hsplitNF.1 (hf1v ▸ hvq)
  have hnf2 : f2 ∉ g.faces := by
    intro hmem2
    have hvq : f2.vertices ∈ quotientList L N := by
      rw [← hfg]
      exact List.mem_map.mpr ⟨f2, hmem2, rfl⟩
    exact hsplitNF.2 (hf2v ▸ hvq)
  -- ⑤ hnews：range' + splitFace 计数
  have hg'cv : g'.countVertices = g.countVertices + newVs.length := by
    rw [show g'.countVertices = (splitFace g (ytrans L N r x 0).1
        (ztrans L N r x 0).1 f newVs).2.2.countVertices from by rw [hsplit]]
    exact splitFaceCountVertices g _ _ f newVs
  have hnewVsLen : newVs.length
      = (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length := by
    rw [← hnewVs, List.length_range']
  have hlen' : g'.faceListAt.length = g.faceListAt.length
      + (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length := by
    rw [← hc', ← hc, hg'cv, hnewVsLen]
  have hnews : ∀ j, j ∈ newVs ↔ g.faceListAt.length ≤ j ∧ j < g'.faceListAt.length := by
    intro j
    have h1 : j ∈ newVs ↔ g.countVertices ≤ j ∧
        j < g.countVertices
          + (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length := by
      rw [← hnewVs, List.mem_range']
      constructor
      · rintro ⟨k, hk, rfl⟩
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨j - g.countVertices, by omega, by omega⟩
    rw [h1, hlen', ← hc]
  -- ⑥ hall：good_faces_v3 + faces Nodup
  have hall : ∀ l ∈ g.faceListAt, l.Nodup := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
    have hiC : i < g.countVertices := by rw [hc]; exact hi
    have hivs : i ∈ Kepler.Text.TameCorrList.verticesSet2 g := by
      show i ∈ g.vertices
      exact List.mem_range.mpr hiC
    have hperm : (Kepler.Text.TameCorrList.facesAtV2 g i).Perm (g.facesAt i) :=
      hgood i hivs
    have hndV2 : (Kepler.Text.TameCorrList.facesAtV2 g i).Nodup := by
      show (g.faces.filter (fun f => i ∈ f.vertices)).Nodup
      exact hndFaces.filter _
    have hndAt : (g.facesAt i).Nodup := hperm.nodup hndV2
    have hget : g.facesAt i = g.faceListAt[i] := by
      show g.faceListAt.getD i [] = g.faceListAt[i]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rwa [hget] at hndAt
  exact ⟨hndF, hnf1, hnf2, hnews, hall, hr1, hr2, hrne⟩

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.goodFacesTransformLemmaPremises
