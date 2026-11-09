/-
  Kepler.Text.Reduction3Thm13B — T13 续批：converse + markedListElementPre。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   elements_of_list_vertices_set2_converse
  │       reduction2.hl:1360 → §B elementsOfListVerticesSet2Converse
  │   marked_list_element_pre
  │       reduction3.hl:1797 → §B markedListElementPre（3 行投影）
  │ 目的：闭合 `b_nfgtransk`(:4442) 的最后一个非 subdiv 缺口。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（载体/折算；语义逐字）───────────────────────────────
  │ ① `vertices_set2 g` ↦ `{v : ℕ | v ∈ g.vertices}`——即
  │    `Kepler.Assembly.verticesSet2` 的**定义展开**（`{v | v ∈ g.vertices}`，
  │    Assembly.lean:2248）；写展开形而不用名字只为**不 import Assembly 伞**
  │    （伞模块含接口 sorry；窄闭包核验见 DELIVERY/Evidence）。语义同项。
  │ ② `fgraph g` ↦ `fgraphOfGraph g`（D2 桥，Reduction3DefsLayer:70）。
  │ ③ `good_list L` ↦ 显式参数 `hL : GoodList L`（链侧 `markedList` 吃 hL）；
  │    与 HOL 原子同一命题。
  │ ④ `marked_list L N r x` ↦ `Kepler.Text.ChainLists.markedList L hL N r x`。
  │ ⑤ `undup` ↦ `.dedup`、`sizel` ↦ `.length`、`0..PRE n` ↦ `{i | i ≤ n-1}`。
  │ ⑥ converse 的 HOL 证体用 `CARD`/`set_of_list` 计数；Lean 落 Finset：
  │    `v < countVertices ↔ v ∈ fn` ⇒ `fn.toFinset = Finset.range countVertices`
  │    ⇒ `countVertices = fn.dedup.length`（`List.card_toFinset`）。
  │    非零性由 `markedList` 合取 3（`r ∈ N`）+ 合取 2（各面非空）+
  │    `List.flatten_eq_nil_iff` 供给。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `mle_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.TameList35

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList)
open Kepler.Graphs (Graph fgraph)
open Kepler.Text.Reduction5 (Dart quotientList)
open Kepler.Text.TameLp (elementsOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §A 私有辅助 -/

/-- `setOfListNatSpine` 的成员展开（避免反复 unfold）。 -/
private theorem mle_mem_setOfListNatSpine {l : List ℕ} {x : ℕ} :
    x ∈ Kepler.Text.TameSpine.setOfListNatSpine l ↔ x ∈ l := Iff.rfl

/-! ## §B 两件 -/

/-- HOL `elements_of_list_vertices_set2_converse`（reduction2.hl:1360）：
`good_list L ∧ marked_list L N r x ∧ fgraph g = quotient_list L N ∧
vertices_set2 g = elements_of_list (fgraph g)` ⇒
`countVertices g = sizel (undup (MAP FST (flatten N)))` ∧
`elements_of_list (quotient_list L N) = 0..PRE(该数)`。 -/
theorem elementsOfListVerticesSet2Converse
    (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)} {r : List Dart}
    {x : Dart} (hm : markedList L hL N r x) (g : Graph)
    (hmq : fgraphOfGraph g = quotientList L N)
    (hv2 : {v : ℕ | v ∈ g.vertices} = elementsOfList (fgraphOfGraph g)) :
    g.countVertices = (N.flatten.map (fun d => d.1)).dedup.length ∧
      elementsOfList (quotientList L N) =
        {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1} := by
  set fn : List ℕ := N.flatten.map (fun d => d.1) with hfn
  -- 1. marked_list ⇒ normal_list ⇒ NormalListSpine
  have hnormal : normalList L hL N := hm.2.1
  have hnsp : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnormal
  -- 2. quotient_list_elements（链侧，过桥）
  have hEs : elementsOfList (quotientList L N) =
      Kepler.Text.TameSpine.setOfListNatSpine fn := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact Kepler.Text.TameSpine.quotientListElements L hL hnsp
  -- 3. vertices_set2 g = setOfListNatSpine fn
  have hvfn : {v : ℕ | v ∈ g.vertices} = Kepler.Text.TameSpine.setOfListNatSpine fn := by
    rw [hv2, hmq, hEs]
  -- 4. 点态：v < countVertices ↔ v ∈ fn
  have hpoint : ∀ v : ℕ, v < g.countVertices ↔ v ∈ fn := by
    intro v
    have hmem := congrArg (fun S : Set ℕ => v ∈ S) hvfn
    simpa [Graph.vertices, List.mem_range, Kepler.Text.TameSpine.setOfListNatSpine]
      using hmem
  -- 5. 计数：countVertices = |fn.dedup|
  have hcard : g.countVertices = fn.dedup.length := by
    have htofinset : fn.toFinset = Finset.range g.countVertices := by
      ext v
      simp only [List.mem_toFinset, Finset.mem_range]
      exact (hpoint v).symm
    calc g.countVertices = (Finset.range g.countVertices).card :=
          (Finset.card_range _).symm
      _ = fn.toFinset.card := by rw [htofinset]
      _ = fn.dedup.length := List.card_toFinset fn
  -- 6. fn ≠ []（markedList 合取 3 给 N ≠ []，合取 2 给各面非空）
  have hNne : N ≠ [] := by
    intro h0
    exact List.not_mem_nil (h0 ▸ hm.2.2.1)
  have hfn_ne : fn ≠ [] := by
    intro h0
    have hmap : N.flatten.map (fun d => d.1) = [] := by
      rw [← hfn]
      exact h0
    have hflat : N.flatten = [] := List.map_eq_nil_iff.mp hmap
    have hall : ∀ l ∈ N, l = [] := List.flatten_eq_nil_iff.mp hflat
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil N hNne
    exact hnormal.2.1 s hs (hall s hs)
  have hn_ne : fn.dedup.length ≠ 0 := by
    intro h0
    have hd : fn.dedup = [] := List.length_eq_zero_iff.mp h0
    exact hfn_ne ((List.dedup_eq_nil fn).mp hd)
  constructor
  · exact hcard
  · have hcne : g.countVertices ≠ 0 := by
      rw [hcard]
      exact hn_ne
    rw [hEs]
    ext i
    simp only [Kepler.Text.TameSpine.setOfListNatSpine, Set.mem_setOf_eq]
    rw [← hcard, ← hpoint i]
    omega

/-- HOL `marked_list_element_pre`（reduction3.hl:1797）：
`good_list L ∧ marked_list L N r x ∧ fgraph g = quotient_list L N ∧
vertices_set2 g = elements_of_list (fgraph g)` ⇒ `element_pre L N`
（HOL prove 为 `elements_of_list_vertices_set2_converse` 的第二合取投影）。 -/
theorem markedListElementPre
    (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)} {r : List Dart}
    {x : Dart} (hm : markedList L hL N r x) (g : Graph)
    (hmq : fgraphOfGraph g = quotientList L N)
    (hv2 : {v : ℕ | v ∈ g.vertices} = elementsOfList (fgraphOfGraph g)) :
    elementPre L N := by
  unfold elementPre
  exact (elementsOfListVerticesSet2Converse L hL hm g hmq hv2).2

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.elementsOfListVerticesSet2Converse
#print axioms Kepler.Text.Reduction3.markedListElementPre
