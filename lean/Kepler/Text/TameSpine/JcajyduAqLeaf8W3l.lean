/-
  JcajyduAqLeaf8W3l — AQ8 波 3l：GSUBGOAL#1 **无条件化**（W3c 最后一件硬件）。

  ┌─ 关键观察（本波最重要的发现）───────────────────────────────────
  │ GSUBGOAL#1 只需 **FST-of-head 的成员性**：
  │   `MEM d (MAP (FST∘HD) (parts L s)) ⇒ MEM d (MAP (FST∘HD) (parts L r))`
  │ 而 W3k 的 `aq8w3k_partRefineFst` 已给：对每个 `u ∈ parts L s`，
  │ 存在 `v ∈ parts L r` 使 `(HD u).1 = (HD v).1` —— **逐点相等即够**，
  │ 不需要 `u ⊆ v`（containment）！故 `partsSubArcRefine` 对 #1 **非必需**。
  └────────────────────────────────────────────────────────────────

  ┌─ 件目（≤180）──────────────────────────────────────────────────
  │ ① aq8w3l_partsFstHdMemSubUncond  GSUBGOAL#1 的**无条件形**（零槽）：
  │    `∀ d, d ∈ MAP (FST∘HD) (parts L (弧 3 段)) → d ∈ MAP (FST∘HD) (parts L r)`
  └────────────────────────────────────────────────────────────────

  ┌─ 与 W3b-i 条件形的关系 ──────────────────────────────────────────
  │ W3b-i `aq8w3b_partsFstHdMemSub`（条件：`hsN : 弧 ∈ ntrans` + `h1..h5`）
  │ 保留不动（其 `hsN` 槽在 CASE-1 由 `sndMemRtran1` 供）；
  │ 本件是它的**零槽强化**——因 W3k 的 FST 半边已不需要 `s` 的 normal_list。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────────
  │ `MAP (FST o HD)` ↦ `List.map (fun p => p.head!.1)`；`MEM` 逐字；
  │ 弧 3 段取 HOL 的 `s = [z] ++ betwn r z y ++ [y]` 具体项。逐字。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3l_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3k

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-- **GSUBGOAL#1 无条件形（零槽）**：环状弧 `[z] ++ between r z y ++ [y]`
的 parts 的「FST-of-head 表」包含于 `parts L r` 的同名表。

由 W3k `aq8w3k_partRefineFst` 逐点代入：`d = (HD u).1 = (HD v).1`（`v ∈ parts L r`）
⇒ `d` 在 r 侧表中。**不需要 containment**，也不需要弧的 normal_list。 -/
theorem aq8w3l_partsFstHdMemSubUncond (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∀ d, d ∈ (partsSpine L ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x])).map (fun p => p.head!.1) →
      d ∈ (partsSpine L r).map (fun p => p.head!.1) := by
  intro d hd
  obtain ⟨u, hu, hud⟩ := List.mem_map.mp hd
  obtain ⟨v, hv, hveq⟩ := aq8w3k_partRefineFst L hL hgn hm hf u hu
  exact List.mem_map.mpr ⟨v, hv, hveq.symm.trans hud⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3l_partsFstHdMemSubUncond
