/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12AC — AQ12 叶总装（decl 68 收口）。

  `aq12 : aq12Concl L hL`（TowerBase:307 冻结陈述逐字）：
  `∀ N r x, GoodListNodesTl L hL → MarkedListSpineFull hL N r x →
    finalListSpine L (rtransSpine L N r x 1) → FlagListSpine L (ntransSpine L N r x 1)`。

  装配（HOL AQ12.hl:3643-:4092）：
  · final 支：`ntransId` ⇒ `ntrans 1 = N`；`hm.2.1 hfin : FlagListSpine L N` 直取。
  · ¬final 支：`ntrans1` 展开 `replace r [S] N ++ [F]`（`hsplitS`/`hsplitF` 对齐
    canonical↔f-split）；`FlagListSpine` 两合取：
    1. 合取 1 = `aq12y_flagListConjunctOne`（12Y；`h4 := aq4 L hL` 消槽在其内部）；
    2. 合取 2：`r' ∈ replace r [S] N ++ [F]` 二分——
       `∈ replace` ⇒ **`aq12z_flagConjunctTwoNS`**（12Z：N 段 + S 段，含旧行
       r'∈N 的全部情形；无需在总装另做旧行 quotient 投影）；
       `∈ [F]` ⇒ **`aq12ab_flagConjunctTwoF`**（12AB：F 支完整形）。
  · S 支（r' = S）已由 12Z 内部用 `hfinRtrans ⇒ final S` 反证吸收。

  不吃新的 `h4`（唯一消槽点在 12Y 内部）。纪律：零 sorry/admit/native_decide/
  axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12AB
import Kepler.Text.TameSpine.JcajyduAqLeaf12Y
import Kepler.Text.TameSpine.JcajyduAqLeaf12Z
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **AQ12 叶收口**（HOL `AQ12_concl`，AQ12.hl:3643）：`final_list L r' ==>
flag_list L N'`——`marked_list` 合取 8。 -/
theorem aq12 (L : fgraph ℕ) (hL : GoodList L) : aq12Concl L hL := by
  intro N r x hgn hm hfinR
  by_cases hfin : finalListSpine L r
  · -- final 支：ntrans 1 = N，直取 hm 的 final→Flag 合取
    rw [ntransId L N r x hfin]
    exact hm.2.1 hfin
  · -- ¬final 支：ntrans 1 = replace r [S] N ++ [F]
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    set S := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).2 with hSdef
    set F := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 with hFdef
    have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hfin).1
    have hsplitS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 = S := by
      rw [hSdef, hfaceY]
    have hsplitF : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 = F := by
      rw [hFdef, hfaceY]
    have hn : ntransSpine L N r x 1 = replaceSpine r [S] N ++ [F] := by
      rw [ntrans1 L N r x hfin, hsplitS, hsplitF]
    have hrtrans : rtransSpine L N r x 1 = S := by
      show ((transformListSpine L x)^[1] (N, r)).2 = _
      rw [Function.iterate_one]
      simp only [transformListSpine, if_neg hfin]
      rw [hsplitS]
    have hfinS : finalListSpine L S := by
      rw [← hrtrans]
      exact hfinR
    -- FlagListSpine L (ntrans 1) = 合取 1 ∧ 合取 2
    refine ⟨?_, ?_⟩
    · -- 合取 1：12Y（含 AQ4 消槽）
      exact aq12y_flagListConjunctOne L hL hgn hm
    · -- 合取 2：r' 三分（replace 段 / F 点）
      intro r' p y hy hp hr' hnf'
      have hr'cat : r' ∈ replaceSpine r [S] N ++ [F] := hn ▸ hr'
      rcases List.mem_append.mp hr'cat with hcases | hF
      · -- r' ∈ replace r [S] N：N 段 + S 段（12Z 全包）
        exact aq12z_flagConjunctTwoNS L hL hgn hm hfin hfinR r' p y hy hp hcases hnf'
      · -- r' = F：12AB 组合器
        have hFeq : r' = F := List.mem_singleton.mp hF
        rw [hFeq] at hp
        rw [hy]
        exact aq12ab_flagConjunctTwoF L hL hgn hm hfin hfinR hp

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12
