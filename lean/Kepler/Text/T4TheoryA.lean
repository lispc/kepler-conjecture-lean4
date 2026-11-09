/-
  Kepler.Text.Reduction3Thm4TheoryA — T4-theory 前半：
  `minimalFaceNonnil`（reduction1.hl:3728）+ `loopChoiceProps`（reduction1.hl:3935）。

  ┌─ 定位（T4-theory 拆两批的前半；无 J2 依赖）────────────────────
  │ loop_choice_props 是 minimalFace_core / hd_vs_some_v /
  │ last_vs_some_prev 共同的 x ↔ (prev_el f w, w) 关系来源。
  │ 实现路线（照 M0h `AtomChain` 精神：**弱不变量直达，不搬 Spine 大机**）：
  │   · 全程链侧件：normalList/parts/partsUniqNonnil/partsFlatten/
  │     prevElListPairsEq（T4 件）；
  │   · 共享 defs 的 Spine 定理直接调用（findListUniq TameList9、
  │     memListOfDartsQuotient TameList10、simpleHypermapUniq TameList14、
  │     memMinimalVertex TameList58、goodListQuotient TameList10）——
  │     defs 同常量，仅经 ChainBridgeParts 的 iff（normalList/
  │     quotientList/findList）折算；
  │   · PART_LIST 收编：partsUniqNonnil/partsFlatten 用
  │     MoreLemma2Island3/2（M0h 已落 e7a7ddae），不重落。
  │ **单文件闭包核验**（新口径逐文件）：本文件 import 的 6 个模块闭包
  │ 1126-1176 模块，Assembly 条目均仅 `Kepler.Assembly.GoodListDefs`。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide。junk：`LAST` ↦ getLastD(0,0)/
  │ getLast!（非空守卫）；`the` ↦ getD 0（isSome 守卫）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm4
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.ChainBridgeParts
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList14
import Kepler.Text.TameSpine.TameList58

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listOfDarts listPairs prevEl nextEl)
open Kepler.Graphs (Face Graph minimalFace minimalVertex nonFinals fgraph)
open Kepler.Text.Reduction5 (Dart finalList parts quotientList)
open Kepler.Text.ChainLists (findList normalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-! ## §0 junk 辅助 -/

private theorem getLast!_mem_of_ne {α : Type} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

/-! ## §A `minimalFace_nonnil`（reduction1.hl:3728）

`~finalGraph g` ⇒ `minimalFace (nonFinals g)` 非空：其顶点表是
`quotient_list L N` 的成员（`match_quotient_list` + `minimalFace` 在
`fgraph g` 内），而 `quotient_list` 是 `good_list`（`goodListQuotient`），
`good_list` 的 faces 全非空。 -/

/-- HOL `minimalFace_nonnil`（reduction1.hl:3728）。 -/
theorem minimalFaceNonnil (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (N : List (List Dart)) (hn : normalList L hL N)
    (g : Graph) (hmq : matchQuotientList g L N) (hng : g.final = false) :
    (minimalFace (nonFinals g)).vertices ≠ [] := by
  have hne : nonFinals g ≠ [] := by
    intro h
    have hg : g.final = true := by simp [Graph.final, h]
    rw [hg] at hng
    exact Bool.noConfusion hng
  have hfv : (minimalFace (nonFinals g)).vertices
      ∈ fgraphOfGraph g := minimalFaceVerticesMemFgraph hne
  have hq : (minimalFace (nonFinals g)).vertices ∈ quotientList L N := by
    rw [← hmq.2]
    exact hfv
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hn
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hir.simple
  have hgq : GoodList (Kepler.Text.TameSpine.quotientListSpine L N) :=
    Kepler.Text.TameSpine.goodListQuotient L hL hnS hir.edgeNondegenerate hunL
  have hgq' : GoodList (quotientList L N) := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact hgq
  exact hgq'.2.1 _ hq


/-! ## §B `loop_choice_props`（reduction1.hl:3935）

`loop_choice2` 展开后：`r = findList N d`、`x = (findList (parts L r) d).getLastD`，
`d = (prevEl f.vertices w, w)`。四步收口：
1. `d ∈ listPairs f.vertices`（`prevElListPairsEq`）⇒ `d ∈ list_of_darts (fgraph g)`；
2. `match_quotient_list` 转 `quotient_list`，`memListOfDartsQuotient` 给出
   `d = p.getLast!`（`p ∈ parts L r'`，`r' ∈ N`）；
3. `partsUniqNonnil`（Island3）⇒ `r'` 非空且 `d ∈ p ⊆ r'`；
   `findListUniq`（TameList9）⇒ `r = r'`；
4. 再对 `parts L r` 用 `findListUniq` ⇒ `x = d`。 -/

/-- HOL `loop_choice_props`（reduction1.hl:3935）。 -/
theorem loopChoiceProps (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (N : List (List Dart)) (hn : normalList L hL N)
    (g : Graph) (hng : g.final = false)
    (hqu : ∀ s ∈ quotientList L N, s.Nodup)
    (hmq : matchQuotientList g L N)
    (r : List Dart) (x : Dart) (f : Face) (w : ℕ)
    (hf : minimalFace (nonFinals g) = f) (hw : minimalVertex g f = w)
    (hlc : loopChoice2 g L N = (r, x)) :
    r ∈ N ∧ x ∈ r ∧ x ∈ listOfDarts (fgraphOfGraph g) ∧
      (prevEl f.vertices w, w) = x := by
  -- loopChoice2 展开
  simp only [loopChoice2] at hlc
  rw [hf, hw] at hlc
  have hlc' := hlc.symm
  have hr : r = findList N (prevEl f.vertices w, w) := by
    simpa using congrArg Prod.fst hlc'
  have hx : x = (findList (parts L r) (prevEl f.vertices w, w)).getLastD (0, 0) := by
    have h2 : x = (findList (parts L (findList N (prevEl f.vertices w, w)))
        (prevEl f.vertices w, w)).getLastD (0, 0) := by
      simpa using congrArg Prod.snd hlc'
    rwa [← hr] at h2
  -- 结构事实
  have hne : nonFinals g ≠ [] := by
    intro h
    have hg : g.final = true := by simp [Graph.final, h]
    rw [hg] at hng
    exact Bool.noConfusion hng
  have hfv0 : f ∈ g.faces := by
    have hm := minimalFaceMem hne
    rw [hf] at hm
    exact (List.mem_filter.mp hm).1
  have hq : f.vertices ∈ quotientList L N := by
    rw [← hmq.2]
    have h2 := minimalFaceVerticesMemFgraph hne
    rw [hf] at h2
    exact h2
  have hfvnd : f.vertices.Nodup := hqu f.vertices hq
  have hfvne : f.vertices ≠ [] := by
    rw [← hf]
    exact minimalFaceNonnil L hL hgn hir N hn g hmq hng
  have hwmem : w ∈ f.vertices := by
    have := Kepler.Text.TameSpine.memMinimalVertex g f hfvne
    rwa [hw] at this
  have hdp : (prevEl f.vertices w, w) ∈ listPairs f.vertices :=
    prevElListPairsEq hfvnd hwmem
  have hd_fg : (prevEl f.vertices w, w) ∈ listOfDarts (fgraphOfGraph g) := by
    unfold Kepler.Assembly.listOfDarts Kepler.Text.Reduction3.fgraphOfGraph
    rw [List.map_map]
    exact List.mem_flatten.mpr
      ⟨_, List.mem_map.mpr ⟨f, hfv0, rfl⟩, hdp⟩
  have hd_quot : (prevEl f.vertices w, w) ∈ listOfDarts (quotientList L N) := by
    rw [← hmq.2]
    exact hd_fg
  have hd_quotS : (prevEl f.vertices w, w)
      ∈ listOfDarts (Kepler.Text.TameSpine.quotientListSpine L N) := by
    rw [← Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact hd_quot
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hn
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hir.simple
  obtain ⟨p, r', hpS, hr'N, hdlast⟩ :=
    (Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnS
      hir.edgeNondegenerate hunL (prevEl f.vertices w, w)).mp hd_quotS
  have hp : p ∈ parts L r' := by
    rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine L r'] at hpS
    exact hpS
  obtain ⟨hr'nd, hr'ne, _hpnd, hpne, hp_sub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hn hr'N hp
  have hd_mem_p : (prevEl f.vertices w, w) ∈ p := by
    rw [hdlast]
    exact getLast!_mem_of_ne hpne
  have hd_mem_r' : (prevEl f.vertices w, w) ∈ r' := hp_sub _ hd_mem_p
  -- r = r'
  have hfind : findList N (prevEl f.vertices w, w) = r' := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hn.1 hd_mem_r' hr'N
  have hr_eq : r = r' := by
    rw [hr, hfind]
  have hrnd : r.Nodup := by rw [hr_eq]; exact hr'nd
  have hrne : r ≠ [] := by rw [hr_eq]; exact hr'ne
  -- p = findList (parts L r) d
  have hp_r : p ∈ parts L r := by rw [hr_eq]; exact hp
  have hfind2 : findList (parts L r) (prevEl f.vertices w, w) = p := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    apply Kepler.Text.TameSpine.findListUniq
    · rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]; exact hrnd
    · exact hd_mem_p
    · exact hp_r
  -- x = d
  have hxd : x = (prevEl f.vertices w, w) := by
    rw [hx, hfind2, ← Kepler.Text.ChainBridge.getLast!_eq_getLastD]
    exact hdlast.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr_eq]
    exact hr'N
  · rw [hxd, hr_eq]
    exact hd_mem_r'
  · rw [hxd]
    exact hd_fg
  · rw [hxd]

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.minimalFaceNonnil
#print axioms Kepler.Text.Reduction3.loopChoiceProps
