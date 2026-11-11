/-
  Kepler.Text.Reduction5J7W4 — J5-7 W4 收口：`betwn_core0_z_y` 主件
  （HOL betwn_core0_z_y.hl:1300-1345）——**J5-7 全塔收官件**。

  陈述 = HOL 主件逐字形，结论直接落 **`reductionK5Concl`**
  （`Reduction5K5.lean:60` = `reduction5.hl:71-78` K5CONJ 活段 =
  `betwn_core0_z_y.hl:1300-1309` 结论形）：

  `full premises (good_list/good_list_nodes/is_restricted/marked_list/
   ¬final_list/transform_count = k) ⇒
   reductionK5Concl L N r x k`
  即 `∀ i, SUF i < k → FST zi ≠ FST ys →
    betwn (core L r) (FST zi) (FST ys)
      = betwn (core L (rtrans L N r x (i+1))) (FST zi) (FST ys)`。

  **路线（纯实例化接线，无本体重写）**：
  · `finalBetwnCore0ZY`（W3-4）：`betwn (core L r) … = betwn (core L f) …`，
    f = find_face L x（rfl 代入）；
  · `betwnCore0DY`（W2d）在**下一状态** `(ntrans (i+1), rtrans (i+1))` 实例化：
    `betwn (core L (rtrans (i+1))) … = betwn (core L f) …`；
    其 `ytrans L (ntrans (i+1)) (rtrans (i+1)) x 0` 与 `ytrans L N r x (i+1)`
    是**定义级同一**（`ytrans = ly ∘ rtrans`，`rtrans … 0 = rfl`）；
  · 下一状态入参：`markedList`（AQIUNPP @i+1）、`¬finalList`
    （`transformCount_not (i+1)`）、`indexf` 不等式（**`qcdvkeaChain`** W1-1）、
    `d ∈ f`（`ztranMeFChain`）；k 槽取 `transformCount (ntrans …) (rtrans …) x` rfl。
  · 收口：`calc` 两行（finalBetwn + betwnCore0DY.symm）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1
import Kepler.Text.Reduction5J7W2e
import Kepler.Text.Reduction5J7W3a
import Kepler.Text.Reduction5K5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **W4：HOL `betwn_core0_z_y` 主件**（betwn_core0_z_y.hl:1300-1345）：
六前提合取 ⇒ `reductionK5Concl`（HOL 主件结论形 = K4 ②支）。
`assumptionSetK10Thm` 的 `hbc0` 槽即本件的逐字代入面。 -/
theorem betwnCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    reductionK5Concl L N r x k := by
  intro i hi hne
  -- 下一状态非 final
  have hf2 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; exact hi)
  -- f = find_face L x、w = next_el f x（HOL GABBREV 的 rfl 代入）
  -- QCDVKEA：indexf 不等式（W1-1 在库）
  have hle : indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i)
        (findFaceDarts L x)
      ≤ indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x (i + 1))
        (findFaceDarts L x) :=
    qcdvkeaChain L hL hgn i hm hf2 rfl rfl
  -- W3-4：core r 侧 = core f 侧
  have hfin := finalBetwnCore0ZY L hL hgn hres haq hm hf hk hi
    (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl hne
  -- W2d 在下一状态实例化：core (rtrans (i+1)) 侧 = core f 侧
  have hd := betwnCore0DY L hL hgn hres haq
    (N := ntrans L N r x (i + 1)) (r := rtrans L N r x (i + 1)) (x := x)
    (k := transformCount L (ntrans L N r x (i + 1)) (rtrans L N r x (i + 1)) x)
    (haq hgn N r x hm (i + 1)) hf2 rfl
    (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x)
    (d := ztrans L N r x i) rfl rfl hne hle
    (Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i)
  calc between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1
      = between (core L (findFaceDarts L x)) (ztrans L N r x i).1
          (ytrans L N r x (i + 1)).1 := hfin
    _ = between (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1
          (ytrans L N r x (i + 1)).1 := hd.symm

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.betwnCore0ZY
