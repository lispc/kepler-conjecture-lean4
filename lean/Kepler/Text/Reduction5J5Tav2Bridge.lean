/-
  Kepler.Text.Reduction5J5Tav2Bridge — J5-2 首段（chain 载体）桥文件：
  链侧单槽 `AqiunppSlot` ⇒ spine 塔族单槽 `transformAssumptionSpine`。

  ┌─ 这座桥解决什么 ──────────────────────────────────────────────────
  │ HOL 的 `transform_assumption_v2 L` 在树内有两种载体：链族定理写成
  │ `Reduction4Idx.AqiunppSlot L hL`（Reduction3ChainTower 口径「TAV2 ↦
  │ AqiunppSlot」），spine 塔族定理写成 `hta : TameSpine.transformAssumptionSpine L hL`
  │ （Reduction3QcdvkeaTower 头注「塔族单槽」）。此前两族不互通：链侧要消费带 `hta`
  │ 的 spine 塔层定理（PBFLHET / PNXVWFS / KBWPBHQ 等）没有现成入口。
  │ 本文件的 `transformAssumptionSpineOfAqiunpp` 让任何带 `hta` 的 spine 定理都能在
  │ 链侧用既有的单槽 `haq` 消费——链件的 TAV2 依赖仍只有 `AqiunppSlot` 一处。
  │ 备选做法（未采用，供裁决）：`TameSpine.transformAssumptionSpine_top`（13/13 无条件形，
  │ JcajyduAqTowerTop，标准三）已在链侧 J5 文件的传递 import 闭包里，直接调用它也能供
  │ `hta`；那样链件的证体会绕过槽直接依赖 AQ 塔 13 叶，与「链件 modulo AqiunppSlot」
  │ 的口径不一致，故本文件走桥。
  └────────────────────────────────────────────────────────────────

  ┌─ 证体 ────────────────────────────────────────────────────────────
  │ 任取 spine marked 的 (N, r, x)：
  │ · r 已 final：一步变换是恒等，直接成立。
  │ · r 非 final：spine marked ⇒ chain marked 走公开桥
  │   `markedList_iff_markedListSpineFull`（ChainBridgeParts），其 `sList` 槽由
  │   `lm` 非空桥供（`lmEqLMSpineOfNonempty` + `sListEqOfLm`，ChainTav2Interface；
  │   非空性是该文件私件 `tav2w0_lmSetNonempty` 的同证重推导）；`haq` 给状态 1 的
  │   chain marked；`transformStepEqSpine`（ChainSpineBridge）把链侧一步换成 spine 侧
  │   一步；状态 1 的 chain marked ⇒ spine marked：非 final 支走同一 iff
  │   （`sList` 槽 ← `sListEqSpineOfMarked`），final 支用 core / flag 两条公开 iff
  │   逐块拼（sFlag 块空转）。
  │ 无 HOL 锚：这是两种载体之间的桥，不是 HOL 引理的移植。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.TameSpine.ChainTav2Interface
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.ChainSpineBridge
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction4Subseg9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)
open Kepler.Text.TameSpine (ntransSpine rtransSpine transformListSpine finalListSpine
  MarkedListSpineFull transformAssumptionSpine)

/-- `lm` 极小集非空（`ChainTav2Interface.tav2w0_lmSetNonempty` 私件的同证重推导；
私件不跨文件）。 -/
private theorem lmSetNonemptyOfNotFinal (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hd : d ∈ r) (hr1 : r.Nodup) (hnext : nextEl r d = fList L d)
    (hf : ¬ finalList L r) :
    ({m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty := by
  by_contra hcon
  have hall : ∀ m : ℕ, (nextEl r)^[m + 2] d = fList L ((nextEl r)^[m + 1] d) := by
    intro m
    by_contra hc
    exact hcon ⟨m, hc⟩
  simp only [finalList] at hf
  push Not at hf
  obtain ⟨z, hzr, hz⟩ := hf
  have hz1 : (nextEl r)^[Kepler.Text.TameSpine.indexf d z r] d = z :=
    Kepler.Text.TameSpine.indexfN hd hzr hr1
  rcases Nat.eq_zero_or_pos (Kepler.Text.TameSpine.indexf d z r) with hk | hk
  · rw [hk] at hz1
    simp only [Function.iterate_zero_apply] at hz1
    exact hz (by rw [← hz1, hnext])
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
    have e1 : z = (nextEl r)^[j + 1] d := by rw [← hz1, hj]
    have h2 : (nextEl r)^[j + 2] d = nextEl r ((nextEl r)^[j + 1] d) :=
      Function.iterate_succ_apply' (nextEl r) (j + 1) d
    have hstep := hall j
    rw [h2, ← e1] at hstep
    exact hz hstep.symm

/-- **链侧单槽 ⇒ spine TAV2**：`AqiunppSlot L hL`（chain AQIUNPP 的全称陈述）供出
spine 塔族的单槽 `transformAssumptionSpine L hL`。 -/
theorem transformAssumptionSpineOfAqiunpp (L : fgraph ℕ) (hL : GoodList L)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL) :
    transformAssumptionSpine L hL := by
  intro N r x hgn hmS
  by_cases hfin0 : finalListSpine L r
  · -- final：一步变换是恒等
    have hnS : ntransSpine L N r x 1 = N := by
      simp only [ntransSpine, Function.iterate_one, transformListSpine]
      rw [if_pos hfin0]
    have hrS : rtransSpine L N r x 1 = r := by
      simp only [rtransSpine, Function.iterate_one, transformListSpine]
      rw [if_pos hfin0]
    rw [hnS, hrS]
    exact hmS
  · have hfin : ¬ finalList L r :=
      fun h => hfin0 ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp h)
    -- spine marked ⇒ chain marked（sList 槽由 lm 非空桥供）
    have hr1 : r.Nodup := (List.nodup_flatten.mp hmS.1.2.1.1).1 _ hmS.1.2.2.1
    have hnext : nextEl r x = fList L x := hmS.1.2.2.2.2.2.1
    have hlm := Kepler.Text.TameSpine.lmEqLMSpineOfNonempty L
      (lmSetNonemptyOfNotFinal L hmS.1.2.2.2.1 hr1 hnext hfin)
    have hs0 : Kepler.Text.ChainLists.sList L r x = Kepler.Text.TameSpine.sListSpine L r x :=
      Kepler.Text.TameSpine.sListEqOfLm L hlm
    have hmC : markedList L hL N r x :=
      (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs0).mpr hmS
    have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hmC.1
    -- 链侧 AQIUNPP 一步
    have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hmC 1
    -- 链侧一步 = spine 侧一步
    have hstep := Kepler.Text.ChainSpineBridge.transformStepEqSpine L hL hgn hunL hmC
    have hn1 : ntrans L N r x 1 = ntransSpine L N r x 1 := by
      simp only [ntrans, ntransSpine, Function.iterate_one, hstep]
    have hr1' : rtrans L N r x 1 = rtransSpine L N r x 1 := by
      simp only [rtrans, rtransSpine, Function.iterate_one, hstep]
    -- 状态 1：chain marked ⇒ spine marked
    rw [← hn1, ← hr1']
    by_cases hf1 : finalList L (rtrans L N r x 1)
    · obtain ⟨c1, c2, c3, c4, c5, c6, c7, hfl, hsf⟩ := hm1
      exact ⟨(Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL _ _ _).mp
          ⟨c1, c2, c3, c4, c5, c6, c7⟩,
        fun _ => (Kepler.Text.ChainBridge.flagList_iff_flagListSpine L _).mp (hfl hf1),
        fun hnS => absurd ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mp hf1) hnS⟩
    · have hs1 := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm1 hf1
      exact (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL _ _ _ hs1).mp hm1

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp
