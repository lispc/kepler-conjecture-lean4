/-
  Kepler.Text.TameSpine.JcajyduRed2Tav2 — W2-a patch1②③：TAV2 桥 +
  `AQIUNPP`（`reduction3.hl:4047-4053`）无条件形。

  ┌─ 结构（编排者 2026-11-10 U3 裁决）────────────────────────────
  │ ① `transformAssumptionV2_of_goodList`：塔顶 13/13 真证叶
  │   （JcajyduAqTowerTop 同款 `aq1..aq13 L hL`）经
  │   `ChainTav2Interface.transformAssumptionOfAqChain`（TAV2 Wave 0，
  │   `414ae90b`：Spine↔链变换桥 + 链层 9 合取重装）直投链侧 def
  │   `Reduction5.transformAssumptionV2`。
  │ ② `aqiunpp`：链词汇全称形 `∀ i`（i = 0 走 `ntrans_zero`/`rtrans_zero`，
  │   i+1 步用 ① + 迭代步进引理）。
  │ 环方向：TameSpine → 链侧 defs 是允许向；链侧消费者（reduction_K 链、
  │ betwn_core 塔）以本两件的全称陈述为 Prop 槽，永不 import 本模块。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5Tav2
import Kepler.Text.TameSpine.ChainTav2Interface
import Kepler.Text.TameSpine.JcajyduAqTowerTop

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)

/-- `Prod` 结构 eta 的显式形（`rfl` 直接成立；作步进引理的重写件）。 -/
private theorem tav2ProdEta (p : List (List (ℕ × ℕ)) × List (ℕ × ℕ)) :
    (p.1, p.2) = p := rfl

/-- `ntrans` 的一步迭代分解（`Nat.succ i` 形；`i + 1` 的 `Nat.add` 不折，
须先 `show i + 1 = Nat.succ i`）。 -/
theorem tav2NtransSucc (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (i : ℕ) :
    Kepler.Text.Reduction5.ntrans L N r x (Nat.succ i)
      = Kepler.Text.Reduction5.ntrans L
          (Kepler.Text.Reduction5.ntrans L N r x i)
          (Kepler.Text.Reduction5.rtrans L N r x i) x 1 := by
  show ((Kepler.Text.Reduction5.transformList L x)^[Nat.succ i] (N, r)).1
      = (((Kepler.Text.Reduction5.transformList L x)^[1]
          (((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).1,
            ((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).2))).1
  rw [Function.iterate_succ_apply', Function.iterate_one, tav2ProdEta]

/-- `rtrans` 的一步迭代分解（同上，`.2` 投影）。 -/
theorem tav2RtransSucc (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (i : ℕ) :
    Kepler.Text.Reduction5.rtrans L N r x (Nat.succ i)
      = Kepler.Text.Reduction5.rtrans L
          (Kepler.Text.Reduction5.ntrans L N r x i)
          (Kepler.Text.Reduction5.rtrans L N r x i) x 1 := by
  show ((Kepler.Text.Reduction5.transformList L x)^[Nat.succ i] (N, r)).2
      = (((Kepler.Text.Reduction5.transformList L x)^[1]
          (((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).1,
            ((Kepler.Text.Reduction5.transformList L x)^[i] (N, r)).2))).2
  rw [Function.iterate_succ_apply', Function.iterate_one, tav2ProdEta]

/-- **TAV2 桥**：`Reduction5.transformAssumptionV2 L` 无条件成立
（13 叶全真证，经 Wave 0 桥落到链词汇）。 -/
theorem transformAssumptionV2_of_goodList (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction5.transformAssumptionV2 L := by
  intro _hL hgn N r x hm
  exact transformAssumptionOfAqChain L hL (aq1 L hL) (aq2 L hL) (aq3 L hL)
    (aq4 L hL) (aq5 L hL) (aq6 L hL) (aq7 L hL) (aq8 L hL) (aq9 L hL)
    (aq10 L hL) (aq11 L hL) (aq12 L hL) (aq13 L hL) N r x hgn hm

/-- **HOL `AQIUNPP`**（`reduction3.hl:4047-4053`，逐字）：
`good_list ∧ good_list_nodes ∧ marked_list L N r x ⇒ marked_list L
(ntrans L N r x i) (rtrans L N r x i) x` 全称 `i`。
HOL 证体 = `MESON[Tame_list.AQIUNPP3; Reduction2.transform_assumption_v2_lemma]`；
Lean 路线：`i = 0` 是恒等（`ntrans_zero`/`rtrans_zero`），`i+1` 步是
TAV2（i = 1 处）+ 迭代步进引理 `tav2NtransSucc`/`tav2RtransSucc`。 -/
theorem aqiunpp (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (x : ℕ × ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ) :
    Kepler.Text.ChainLists.markedList L hL
      (Kepler.Text.Reduction5.ntrans L N r x i)
      (Kepler.Text.Reduction5.rtrans L N r x i) x := by
  induction i with
  | zero =>
    rw [Kepler.Text.Reduction5.ntrans_zero, Kepler.Text.Reduction5.rtrans_zero]
    exact hm
  | succ i ih =>
    rw [show i + 1 = Nat.succ i from rfl, tav2NtransSucc, tav2RtransSucc]
    exact transformAssumptionV2_of_goodList L hL hL hgn
      (Kepler.Text.Reduction5.ntrans L N r x i)
      (Kepler.Text.Reduction5.rtrans L N r x i) x ih

end Kepler.Text.TameSpine

/-! 探针（编译即执行；真证件零 sorryAx，目标 ⊆ 标准三） -/
#print axioms Kepler.Text.TameSpine.transformAssumptionV2_of_goodList
#print axioms Kepler.Text.TameSpine.aqiunpp
