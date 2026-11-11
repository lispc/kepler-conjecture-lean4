/-
  Kepler.Text.Reduction3Thm14g — J5-8 W3-1：B 簇五件
  （reduction2.hl:1139 / :1273 / :1405 / :1634 / :1336）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction2.hl）──
  │ B1 :1139 `newvertex_prepped_transform_lemma` → `newvertexPreppedTransformLemma`
  │ B2 :1273 `newvertex_prepped_transform`       → `newvertexPreppedTransform`
  │ B3 :1405 `splitFace_countVertices`           → `splitFaceCountVertices`（rfl 级）
  │ B5 :1634 `sizel_faceListAt_splitFace`        → `sizelFaceListAtSplitFace`
  │ B6 :1336 `elements_of_list_vertices_set2`    → `elementsOfListVerticesSet2`
  │ B4 :1432 `splitFace_good_vertices_set2`     → `splitFaceGoodVerticesSet2`
  └────────────────────────────────────────────────────────────────

  **在库供料（#check 清点，零重落）**：
  · B1/B2 的 **spine 形已在库**：`TameSpine.newvertexPreppedTransformLemmaSpine`
    （Reduction3NewvertexPrepTransform:235）/ `newvertexPreppedTransformSpine`
    （Reduction3NewvertexPreppedTransformSpine:384）；本件链形 = 直投 + 桥
    （`ntransEqSpine`/`rtransEqSpine`/`markedSpineFullOfChainAlways`/
    `finalList_iff_finalListSpine`）。
  · B5 = `t9c_splitFace_faceListAt_length`（T9C:71）+ B3。
  · B6 正向未落（T13B 仅有 converse）；本件同证重落。

  **DIFFERS**：B1/B2 链形加 `haq : AqiunppSlot`（桥件需要，本仓惯例 +1）；
  B2 另加 `hrreS : rRtransEqSpine`（树内无 chain→spine 无条件桥，按
  `Reduction5J5NewvertexPrepped` 既有口径显式携入）。B4 的 `elements_of_list`
  等式在本文件以显式前提携入（HOL 由 converse 现推，见下一文件）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm13B
import Kepler.Text.Reduction3Thm9C
import Kepler.Text.TameSpine.Reduction3HbridgeElim
import Kepler.Text.Reduction5J5Red2Pieces
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.TameSpine.Reduction3NewvertexPreppedTransformSpine
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.TameSpine.TameList14

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
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList elementsOfList)

/-- **W3-1 B3：HOL `splitFace_countVertices`**（reduction2.hl:1405-1415）：
`countVertices g' = countVertices g + sizel ws`（`splitFace` 定义级）。 -/
theorem splitFaceCountVertices (g : Graph) (u v : ℕ) (f : Face) (ws : List ℕ) :
    (splitFace g u v f ws).2.2.countVertices = g.countVertices + ws.length := rfl

/-- **W3-1 B5：HOL `sizel_faceListAt_splitFace`**（reduction2.hl:1634-1670）：
`|faceListAt g| = countVertices g ∧ g' = SND (SND (splitFace …)) ⇒
 |faceListAt g'| = countVertices g'`。 -/
theorem sizelFaceListAtSplitFace (g g' : Graph) (h : Face) (newVs : List ℕ)
    (u v : ℕ)
    (hc : g.faceListAt.length = g.countVertices)
    (hstep : (splitFace g u v h newVs).2.2 = g') :
    g'.faceListAt.length = g'.countVertices := by
  rw [show g'.faceListAt.length
        = (splitFace g u v h newVs).2.2.faceListAt.length from by rw [hstep],
    Kepler.Text.Reduction3.t9c_splitFace_faceListAt_length, hc, ← hstep,
    splitFaceCountVertices]

/-- **W3-1 B6：HOL `elements_of_list_vertices_set2`**（reduction2.hl:1336-1359）：
marked + `elements_of_list (quotient L N) = 0..PRE(n)` + `fgraph g = quotient L N`
+ `countVertices g = n` ⇒ `vertices_set2 g = elements_of_list (fgraph g)`。 -/
theorem elementsOfListVerticesSet2 (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g : Graph)
    (hL : GoodList L)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hE : elementsOfList (quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1})
    (hfg : fgraphOfGraph g = quotientList L N)
    (hc : g.countVertices = (N.flatten.map (fun d => d.1)).dedup.length) :
    Kepler.Text.TameCorrList.VerticesSet2Eq g := by
  have hnpos : 1 ≤ (N.flatten.map (fun d => d.1)).dedup.length := by
    by_contra h0
    have h0' : (N.flatten.map (fun d => d.1)).dedup.length = 0 := by omega
    have hd0 : (N.flatten.map (fun d => d.1)).dedup = [] :=
      List.length_eq_zero_iff.mp h0'
    have hfe : N.flatten.map (fun d => d.1) = [] := (List.dedup_eq_nil _).mp hd0
    have hxfn : x.1 ∈ N.flatten.map (fun d => d.1) :=
      List.mem_map.mpr ⟨x, List.mem_flatten.mpr ⟨r, hm.2.2.1, hm.2.2.2.1⟩, rfl⟩
    rw [hfe] at hxfn
    simp at hxfn
  have h1 : Kepler.Text.TameCorrList.verticesSet2 g
      = {v : ℕ | v < (N.flatten.map (fun d => d.1)).dedup.length} := by
    ext v
    show v ∈ g.vertices ↔ v < (N.flatten.map (fun d => d.1)).dedup.length
    rw [Kepler.Graphs.Graph.vertices, List.mem_range, hc]
  have h2 : ({v : ℕ | v < (N.flatten.map (fun d => d.1)).dedup.length} : Set ℕ)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1} := by
    ext i
    constructor
    · intro h; exact Nat.le_sub_one_of_lt h
    · intro h; exact Nat.lt_of_le_pred (by omega) h
  calc Kepler.Text.TameCorrList.verticesSet2 g
      = {v : ℕ | v < (N.flatten.map (fun d => d.1)).dedup.length} := h1
    _ = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1} := h2
    _ = elementsOfList (quotientList L N) := hE.symm
    _ = elementsOfList (fgraphOfGraph g) := by rw [hfg]
    _ = elementsOfList g.fgraph := rfl

/-- **W3-1 B1：HOL `newvertex_prepped_transform_lemma`**（reduction2.hl:1139-1271）：
`|fn'(1)| = |fn| + |MAP FST (filter (∉ r) r')|`。 -/
theorem newvertexPreppedTransformLemma (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hnvp : newvertexPrepped L N r x)
    (hE : elementsOfList (quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1}) :
    ((ntrans L N r x 1).flatten.map (fun d => d.1)).dedup.length
      = (N.flatten.map (fun d => d.1)).dedup.length
        + (((rtrans L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hnfS : ¬ Kepler.Text.TameSpine.finalListSpine L r := fun h =>
    hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have hsp := Kepler.Text.TameSpine.newvertexPreppedTransformLemmaSpine L hL hgn
    hrre hmS hnvp hnfS hE
  have hnt := Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm 1
  have hrt := Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm 1
  simpa only [hnt, hrt] using hsp

/-- **W3-1 B2：HOL `newvertex_prepped_transform`**（reduction2.hl:1273-1345）：
`newvertex_prepped L N r x` ⇒ `newvertex_prepped L (ntrans 1) (rtrans 1) x`。 -/
theorem newvertexPreppedTransform (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hrreS : Kepler.Text.TameSpine.rRtransEqSpine L N r x)
    (hnvp : newvertexPrepped L N r x)
    (hE : elementsOfList (quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1}) :
    newvertexPrepped L (ntrans L N r x 1) (rtrans L N r x 1) x := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hnfS : ¬ Kepler.Text.TameSpine.finalListSpine L r := fun h =>
    hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have hsp := Kepler.Text.TameSpine.newvertexPreppedTransformSpine L hL hgn
    hrre hmS hnvp hnfS hE hrreS
  have hnt := Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm 1
  have hrt := Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm 1
  simpa only [hnt, hrt] using hsp

/-- **W3-2 B4：HOL `splitFace_good_vertices_set2`**（reduction2.hl:1432-1486）：
一次 splitFace 后 `vertices_set2 = elements_of_list (fgraph ·)` 保持。 -/
theorem splitFaceGoodVerticesSet2 (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (N' : List (List Dart))
    (g' g : Graph) (u v : ℕ) (f : Face) (ws : List ℕ)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hnvp : newvertexPrepped L N r x)
    (hfg : fgraphOfGraph g = quotientList L N)
    (hN' : ntrans L N r x 1 = N')
    (hstep : (splitFace g u v f ws).2.2 = g')
    (hfg' : fgraphOfGraph g' = quotientList L N')
    (hws : ws.length
      = (between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
        (Kepler.Text.Reduction5.lz L N r x)).length)
    (hvs : Kepler.Text.TameCorrList.VerticesSet2Eq g) :
    Kepler.Text.TameCorrList.VerticesSet2Eq g' := by
  -- converse：countVertices g = n 与 hold
  have hconv := Kepler.Text.Reduction3.elementsOfListVerticesSet2Converse L hL hm g hfg hvs
  have hcN : g.countVertices = (N.flatten.map (fun d => d.1)).dedup.length := hconv.1
  have hhold : elementsOfList (quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1} := hconv.2
  -- 状态 1 的 hold
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hm.1.simple
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hE1S := Kepler.Text.TameSpine.elementsOfListNtransTop L hL hgn
    hrre hmS hnvp hhold
  have hnt := Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm 1
  have hE1 : elementsOfList (quotientList L (ntrans L N r x 1))
      = {i : ℕ | i ≤ ((ntrans L N r x 1).flatten.map (fun d => d.1)).dedup.length
        - 1} := by
    simpa only [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, hnt]
      using hE1S
  -- countVertices g' = n'
  have hc' : g'.countVertices
      = ((ntrans L N r x 1).flatten.map (fun d => d.1)).dedup.length := by
    have hB1 := newvertexPreppedTransformLemma L N r x hL hgn haq hm hnf hir
      hrre hnvp hhold
    rw [← hstep, splitFaceCountVertices, hcN, hws, hB1]
    congr 1
    rw [Kepler.Text.Reduction5.rtransDiffR L hL hgn hm hnf, List.length_map]
  have hm1 : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
  have hfg1 : fgraphOfGraph g' = quotientList L (ntrans L N r x 1) := by
    rw [hN']
    exact hfg'
  exact elementsOfListVerticesSet2 L (ntrans L N r x 1) (rtrans L N r x 1) x g'
    hL hm1 hE1 hfg1 hc'

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三或更弱，零未证公理） -/
#print axioms Kepler.Text.Reduction3.splitFaceCountVertices
#print axioms Kepler.Text.Reduction3.sizelFaceListAtSplitFace
#print axioms Kepler.Text.Reduction3.elementsOfListVerticesSet2
#print axioms Kepler.Text.Reduction3.newvertexPreppedTransformLemma
#print axioms Kepler.Text.Reduction3.newvertexPreppedTransform
#print axioms Kepler.Text.Reduction3.splitFaceGoodVerticesSet2
