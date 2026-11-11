/-
  Kepler.Text.Reduction5J5K2A2Up — Lane A2 上游可交件（nb46）：
  `yMemSplitSnd`（HOL AQ12.hl:1509）+ `elementPreStep`（HOL
  `elements_of_list_ntrans` reduction2.hl:1042–1136 的链层单步形）。

  ┌─ 本件范围 ────────────────────────────────────────────────────────
  │ ① `yMemSplitSnd`：`split_normal_list` 的第二片含 `ram1`（= `l'y`）。
  │    HOL 证体 = `EXPAND_TAC r2; REWRITE_TAC[LET_THM; split_normal_list;
  │    MEM_APPEND; Seq.mem_seq1]`，本件同款定义级。
  │ ② `elementPreStep`：`elementPre L N ⇒ elementPre L (ntrans 1)`。
  │    spine 无条件形 `elementsOfListNtransTop`（Reduction3HbridgeElim:560，
  │    aq13 已落）+ `ntransEqSpine` 桥；`hrre` 由 W5b `rRtransEqThm`
  │    （24e18012）直供——A2.1 `hmisc` 的 `elementPre` 半边由此闭合。
  │ ③ **未交**：`uniq_fst/snd_split_normal_parts`（AQ8:2382/:530）与
  │    `newvertexPrepped` 变换保持（需 `rRtransEqSpine` 链→spine 桥，
  │    树内仍零命中）——精确卡点见 DELIVERY-nb46 §2/§3。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Ml1W5bBwd
import Kepler.Text.Reduction3Thm14g
import Kepler.Text.TameSpine.Reduction3HbridgeElim
import Kepler.Text.TameSpine.Reduction3NewvertexPreppedTransformSpine
import Kepler.Text.TameSpine.Reduction3J5PrevCoreX
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)

/-- **HOL `y_mem_split_snd`**（AQ12.hl:1509）：
`l'z = z → l'y = y → prev_el r z = z1 → SND (split_normal_list L r f y z1) = r2 →
MEM y r2`。定义级：`SND` 片 = `f2 ++ new2`，`y` 在 `f2` 的首位。 -/
theorem yMemSplitSnd (L : fgraph ℕ) {r f : List Dart} {y z z1 : Dart}
    {r2 : List Dart} (hy : y ∈ (splitNormalList L r f y z1).2)
    (hr2 : (splitNormalList L r f y z1).2 = r2) :
    y ∈ r2 := by
  rw [← hr2]
  exact hy

/-- `split_normal_list` 第二片的 `ram1` 成员（`yMemSplitSnd` 的定义级内核；
HOL 同名件的 `MEM_APPEND; Seq.mem_seq1` 段）。 -/
theorem yMemSplitSndCore (L : fgraph ℕ) (r f : List Dart) (ram1 ram2 : Dart) :
    ram1 ∈ (splitNormalList L r f ram1 ram2).2 := by
  unfold splitNormalList
  dsimp only
  -- .2 = ([ram2'] ++ (between r ram2' ram1 ++ [ram1])) ++ new2
  rw [List.mem_append]
  left
  rw [List.mem_append]
  right
  rw [List.mem_append]
  right
  exact List.mem_singleton.mpr rfl

/-- **HOL `elements_of_list_ntrans`（链层单步形）**（reduction2.hl:1042–1136）：
`elementPre L N ⇒ elementPre L (ntrans 1)`。
证 = spine 无条件形 `elementsOfListNtransTop`（aq13 `Reduction3HbridgeElim:560`）
+ `ntransEqSpine`；`hrre` 由 W5b `rRtransEqThm` 直供。 -/
theorem elementPreStep (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep : Kepler.Text.Reduction3.elementPre L N) :
    Kepler.Text.Reduction3.elementPre L (ntrans L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  -- spine marked
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  -- W5b：chain rRtransEq
  have hrre : rRtransEq L N r x := rRtransEqThm L hL hgn hm hnf
  -- spine 无条件形
  have h := Kepler.Text.TameSpine.elementsOfListNtransTop L hL hgn hrre hmS hnvp hep
  -- ntransSpine → ntrans
  rwa [← Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm 1] at h

/-- `rRtransEq`（链层）⇒ `rRtransEqSpine`（spine 层）：树内首条无条件桥。
证 = `lzEqSpine` + `rtransEqSpine` + `indexf_eq_spine` 三桥逐点搬运。
`newvertexPreppedTransform` 的 `hrreS` 槽由此闭合。 -/
theorem rRtransEqToSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hrre : rRtransEq L N r x) :
    Kepler.Text.TameSpine.rRtransEqSpine L N r x := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  unfold rRtransEq Kepler.Text.TameSpine.rRtransEqSpine at *
  dsimp only at *
  intro x' hx' hle
  rw [← Kepler.Text.Reduction3.indexf_eq_spine,
    ← Kepler.Text.Reduction3.indexf_eq_spine] at hle
  rw [← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf] at hle
  have h := hrre x' hx' hle
  rwa [Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm 1] at h

/-- **HOL `newvertex_prepped_transform`（链层单步形）**（reduction2.hl:1273–1345）：
`newvertexPrepped L N r x ∧ elementPre L N ⇒
newvertexPrepped L (ntrans 1) (rtrans 1) x`。
`hrre` ← W5b `rRtransEqThm`；`hrreS` ← 本件 `rRtransEqToSpine`。 -/
theorem newvertexPreppedStep (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep : Kepler.Text.Reduction3.elementPre L N) :
    Kepler.Text.Reduction3.newvertexPrepped L (ntrans L N r x 1)
      (rtrans L N r x 1) x :=
  Kepler.Text.Reduction3.newvertexPreppedTransform L N r x hL hgn haq hm hnf hres
    (rRtransEqThm L hL hgn hm hnf)
    (rRtransEqToSpine L hL hgn hres haq hm hnf (rRtransEqThm L hL hgn hm hnf))
    hnvp hep

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.yMemSplitSnd
#print axioms Kepler.Text.Reduction5.yMemSplitSndCore
#print axioms Kepler.Text.Reduction5.elementPreStep
#print axioms Kepler.Text.Reduction5.rRtransEqToSpine
#print axioms Kepler.Text.Reduction5.newvertexPreppedStep
