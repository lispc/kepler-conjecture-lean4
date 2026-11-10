/-
  Kepler.Text.TameSpine.Reduction3NcvibwuGateFirst — NCVIBWU 闸首期 + KBWPBHQ2 spine 消费件。

  ┌─ 归属对账 ────────────────────────────────────────────────────
  │ §A KBWPBHQ2 的 transform_count spine 消费面：
  │   `transAddSpine`（HOL `trans_add` 一般形）+ `finalSuccIdSpine`
  │   （终态吸收）+ `transformCountSpine_le`（`sInf_le` 上界半）。
  │ §B NCVIBWU 闸首期·**成员性半（chain 载体）**：
  │   `ncvibwuV0MemChain` = spine i=0 成员性（B1 `ncvibwuSpineV0FPart` +
  │   B2e `ohcgkfuSpineV0`）经桥 `rtransEqSpine` 翻译回 chain `rtrans` 载体。
  │   chain 侧载体换元：`lzEqSpine`（lz→lZSpine）+ `markedList_iff_
  │   markedListSpineFull`（需要生态既有 `hs : sList = sListSpine` 槽）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① `transAddSpine` 用 `Function.iterate_add_apply` 一次收口（不逐项核对）。
  │ ② NCVIBWU 成员性半走「spine 结果 + 桥翻译」而非 chain 重证；chain 侧不新
  │    造变换塔引理（桥已在库 `ChainSpineBridge`）。
  │ ③ **本波不含 index 等式半**（NCVIBWU 原形 i=0 的 `indexf w d r' = j`）：
  │    机器路线分析显示其核心 = r/r' 共享段 B 的「不绕回」对齐（需 B 内
  │    位置-轨道对齐 ~80–100，见 DELIVERY §4 义务表），比 B1 §3 预估 40–60
  │    更重；按止损纪律单列下一波，不硬凑。本波交付 = 成员性半（可独立消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3LnrxInductionSpine
import Kepler.Text.ChainBridgeParts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart)

/-! ## §A KBWPBHQ2：transform_count 的 spine 消费件 -/

/-- HOL `trans_add` 一般形（spine）：`(transform)^[i+j] = (transform)^[i] ∘ (transform)^[j]`。 -/
theorem transAddSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i j : ℕ) :
    (transformListSpine L x)^[i + j] (N, r)
      = (transformListSpine L x)^[i] ((transformListSpine L x)^[j] (N, r)) := by
  rw [Function.iterate_add_apply]

/-- 终态吸收：状态 j final ⇒ 状态 j+1 = 状态 j（transform 的 final 支为恒等）。 -/
theorem finalSuccIdSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (j : ℕ)
    (hf : finalListSpine L (rtransSpine L N r x j)) :
    (ntransSpine L N r x (j + 1), rtransSpine L N r x (j + 1))
      = (ntransSpine L N r x j, rtransSpine L N r x j) := by
  have h1 : transformListSpine L x ((transformListSpine L x)^[j] (N, r))
      = ((transformListSpine L x)^[j] (N, r)) := by
    have hc : finalListSpine L ((transformListSpine L x)^[j] (N, r)).2 := hf
    simp only [transformListSpine, if_pos hc]
  simp only [ntransSpine, rtransSpine, Function.iterate_succ_apply', h1]

/-- `transformCountSpine` 的上界半：状态 j 已 final ⇒ `transformCountSpine ≤ j`。 -/
theorem transformCountSpine_le (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) {j : ℕ}
    (h : finalListSpine L (rtransSpine L N r x j)) :
    transformCountSpine L N r x ≤ j := by
  have hmem : j ∈ {i : ℕ | finalListSpine L (rtransSpine L N r x i)} := h
  simpa only [transformCountSpine, minNumSpine] using Nat.sInf_le hmem

/-! ## §B NCVIBWU 闸首期：成员性半（chain 载体） -/

/-- **NCVIBWU i=0 成员性半（chain 载体）**：`j ≤ indexf w l'z f`
⇒ face 轨道第 j 步 ∈ chain `rtrans … 1`。
证 = spine 侧 `ohcgkfuSpineV0` + 桥 `rtransEqSpine` + `lzEqSpine` +
`markedList_iff_markedListSpineFull`（生态既有 `hs` 槽）。 -/
theorem ncvibwuV0MemChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hs : Kepler.Text.ChainLists.sList L r x = sListSpine L r x)
    (hf : ¬ Kepler.Text.Reduction5.finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (Kepler.Text.Reduction5.lz L N r x) f) :
    (nextEl f)^[j] w ∈ Kepler.Text.Reduction5.rtrans L N r x 1 := by
  have hmS : MarkedListSpineFull hL N r x :=
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
  have hfS : ¬ finalListSpine L r := hf
  have hlz : Kepler.Text.Reduction5.lz L N r x = lZSpine L N r x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hf
  rw [hlz] at hj
  have hspine : (nextEl f)^[j] w ∈ rtransSpine L N r x 1 :=
    ohcgkfuSpineV0 L hL hgn hmS hfS hfind hw hj
  have hbridge : Kepler.Text.Reduction5.rtrans L N r x 1 = rtransSpine L N r x 1 :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm 1
  rw [← hbridge] at hspine
  exact hspine

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.transAddSpine
#print axioms Kepler.Text.TameSpine.finalSuccIdSpine
#print axioms Kepler.Text.TameSpine.transformCountSpine_le
#print axioms Kepler.Text.TameSpine.ncvibwuV0MemChain
