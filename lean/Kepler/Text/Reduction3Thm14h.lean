/-
  Kepler.Text.Reduction3Thm14h — J5-8 W2-2：`nfgtrans_fst`（reduction3.hl:4814-4881）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ :4814 `nfgtrans_fst` → `nfgtransFst`（T14 main_induction 直接上游）：
  │   `(nfgtrans' (n,f,g) L N r x i).1 = |undup (MAP FST (flatten (ntrans … i)))|`
  │   （前提含 element_pre / r_trans_eq_assumption / good_list / good_list_nodes /
  │   marked_list / ¬final_list / newvertex_prepped / `|undup N| = n` /
  │   `i ≤ transform_count`）。
  └────────────────────────────────────────────────────────────────

  **路线（对 i 归纳）**：
  · 0 支：`nfgtrans'Zero` + `ntrans … 0 = N` + 前提 `hn`。
  · succ 支：`nfgtransSuc` 展开一步 + `subdivTripleStepPaired` 取第一分量 +
    IH 代入后，缺件为
    `|undup(ntrans … (i+1))| = |undup(ntrans … i)| + |betwn … ytransᵢ ztransᵢ|`；
    该等式由 `newvertexPreppedTransformLemma`（B1）+ `rtransDiffR` 于状态 i
    供给。状态 i 的 `newvertexPrepped`/`elementPre` 由 `lnrxInductionSpine`
    （spine 形）经 `ntransEqSpine`/`rtransEqSpine` 折回链层；
    `lnrxInductionSpine` 又需要 `AqiunppSlot`（状态 marked）+
    `transformCount_not`（状态 ¬final）+ 双世界 `rRtransEq` schema。

  **DIFFERS**：
  ① HOL 的 `r_trans_eq_assumption L` 在本仓直接实例化为
    `hrreAll : ∀ N' r' y, rRtransEq L N' r' y`（与 T14 装配层既有口径一致）；
    额外携带 `hrreSAll : ∀ N' r' y, rRtransEqSpine L N' r' y`，因为树内
    `lnrx_induction` 仅 spine 形可用，且无 `rRtransEq → rRtransEqSpine`
    无条件桥（同 `finalAssumptionNewvertexPrepped` 槽②' 口径）。
  ② HOL 的 `core_split_normal_list_assumption L` 在证体中零消费
    （`lnrxInductionSpine` 已按此口径不显式携入），故不携入。
  ③ Lean 惯例 +1 前提 `haq : AqiunppSlot L hL`（状态 marked 与 transform_count
    桥需要）。
  ④ `sizel`/`undup`/`MAP FST`/`flatten` 分别 ↦ `List.length`/`List.dedup`/
    `List.map (fun d => d.1)`/`List.flatten`；HOL `0..PRE n` 的 `element_pre`
    已在 `elementPre` 定义中折算。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14a
import Kepler.Text.Reduction3Thm5B
import Kepler.Text.Reduction3Thm14g
import Kepler.Text.Reduction5J5Red2Pieces
import Kepler.Text.TameSpine.Reduction3LnrxInductionSpine
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph between)
open Kepler.Assembly (GoodList findFaceDarts)
open Kepler.Text.Reduction5
  (Dart ntrans rtrans ytrans ztrans transformList transformCount finalList rRtransEq rtransDiffR)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **J5-8 W2-2：HOL `nfgtrans_fst`**（reduction3.hl:4814-4881）：
`(nfgtrans' (n,f,g) L N r x i).1 = |undup (MAP FST (flatten (ntrans … i)))|`。 -/
theorem nfgtransFst (i : ℕ) (f : Face) (g : Graph) (n : ℕ) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hnvp : newvertexPrepped L N r x)
    (hpre : elementPre L N)
    (hrreAll : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      rRtransEq L N' r' y)
    (hrreSAll : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
      Kepler.Text.TameSpine.rRtransEqSpine L N' r' y)
    (hn : (N.flatten.map (fun d => d.1)).dedup.length = n)
    (hi : i ≤ transformCount L N r x) :
    (nfgtrans' (n, f, g) L N r x i).1 =
      ((ntrans L N r x i).flatten.map (fun d => d.1)).dedup.length := by
  induction i generalizing f g n with
  | zero =>
    rw [nfgtrans'Zero]
    have hnt0 : ntrans L N r x 0 = N := by simp [ntrans]
    rw [hnt0]
    rw [hn]
  | succ i ih =>
    have hile : i ≤ transformCount L N r x := by omega
    have hilt : i < transformCount L N r x := by omega
    -- 状态 i 的 marked / ¬final
    have hm_i : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
    have hfi : ¬ finalList L (rtrans L N r x i) :=
      Kepler.Text.Reduction4.transformCount_not i hilt
    -- spine 形桥：marked / final / transform_count
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
    have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
      Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
    have htc : Kepler.Text.TameSpine.transformCountSpine L N r x
        = transformCount L N r x := by
      rw [Kepler.Text.TameSpine.transformCountEqSpineOfAq L hL hgn haq hm hnf]
    -- lnrx_induction 于状态 i：newvertex_prepped + element_pre
    obtain ⟨hnvp_i, hpre_i⟩ :=
      Kepler.Text.TameSpine.lnrxInductionSpine L hL hgn hrreAll hrreSAll hmS hnvp hpre
        i (by rw [htc]; exact hilt)
    have hnt_i : ntrans L N r x i = Kepler.Text.TameSpine.ntransSpine L N r x i :=
      Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i
    have hrt_i : rtrans L N r x i = Kepler.Text.TameSpine.rtransSpine L N r x i :=
      Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
    have hnvp_i' : newvertexPrepped L (ntrans L N r x i) (rtrans L N r x i) x := by
      rw [hnt_i, hrt_i]
      exact hnvp_i
    have hpre_i' : elementPre L (ntrans L N r x i) := by
      rw [hnt_i]
      exact hpre_i
    -- nfgtrans' succ 展开
    have hsucc := nfgtransSuc i n f g L N r x hL hgn haq hm hnf hir hi
    rw [hsucc]
    rw [subdivTripleStepPaired]
    dsimp only
    -- IH 代入
    have hIH : (nfgtrans' (n, f, g) L N r x i).1 =
        ((ntrans L N r x i).flatten.map (fun d => d.1)).dedup.length := ih f g n hn hile
    rw [hIH]
    -- 状态 i 的新顶点长度账
    have hB1 := newvertexPreppedTransformLemma L (ntrans L N r x i)
      (rtrans L N r x i) x hL hgn haq hm_i hfi hir
      (hrreAll (ntrans L N r x i) (rtrans L N r x i) x)
      hnvp_i' hpre_i'
    have hrd := rtransDiffR L hL hgn hm_i hfi
    -- 将 ntrans (i+1) 折叠为状态 i 上的一步
    have hnt_succ : ntrans L N r x (i + 1)
        = ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1 := by
      have hpair : (ntrans L N r x i, rtrans L N r x i) = (transformList L x)^[i] (N, r) := by
        simp [ntrans, rtrans]
      rw [show ntrans L N r x (i + 1) = ((transformList L x)^[i + 1] (N, r)).1 by simp [ntrans]]
      rw [show ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1
            = (transformList L x (ntrans L N r x i, rtrans L N r x i)).1 by simp [ntrans]]
      rw [Function.iterate_succ_apply']
      rw [hpair]
    rw [hnt_succ]
    -- 将 rtransDiffR 的右端翻译成 ytrans_i / ztrans_i
    have hA : (((rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1).filter
          (fun d => decide (d ∉ rtrans L N r x i))).map (fun d => d.1)).length =
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length := by
      rw [hrd]
      have hy : ytrans L N r x i = Reduction5.ly L (rtrans L N r x i) x := by
        rw [ytrans]
      have hz : ztrans L N r x i = Reduction5.lz L (ntrans L N r x i) (rtrans L N r x i) x := by
        rw [ztrans]
      rw [hy, hz]
      simp [List.length_map]
    rw [hB1]
    rw [hA]
    omega

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.nfgtransFst
