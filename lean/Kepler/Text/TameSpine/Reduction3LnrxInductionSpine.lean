/-
  Kepler.Text.TameSpine.Reduction3LnrxInductionSpine — W2-件2 Wave D：
  `lnrx_induction`（reduction3.hl:2706-2757）的 spine 形总装。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ HOL `lnrx_induction`：
  │ !j L N r x. core_split_normal_list_assumption L ∧ r_trans_eq_assumption L ∧
  │   good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
  │   newvertex_prepped L N r x ∧ element_pre L N ∧ j < transform_count L N r x
  │   ==> newvertex_prepped L (ntrans … j) (rtrans … j) x ∧
  │       element_pre L (ntrans … j)
  │ 拼装（本文件 §3）：j 归纳。
  │   base：state 0 即前提两原子（ntrans/rtrans 0 = N/r 定义级）。
  │   step：state k → k+1：
  │     ¬final@k   ← `transformCountSpineNot`（§2 = KBWPBHQ transformCount_not
  │                  ∘ chain↔spine 桥；HOL KBWPBHQ.hl:85）
  │     marked@k   ← `aqiunpp3_top`（无条件）
  │     nvp@k+1    ← Wave C `newvertexPreppedTransformSpine`（状态 k 实例）
  │     element@k+1← 件1a `elementsOfListNtransTop`（状态 k 实例）
  │     末步折叠   ← §1 `transSuccSpine`（transform^(k+1) = transform^1 ∘ transform^k）
  └────────────────────────────────────────────────────────────────

  ┌─ ERRATA (SF-106) / DIFFERS ───────────────────────────────────
  │ ① **ERRATA**：本文件曾把 `r_trans_eq_assumption L`（HOL reduction3.hl:64-70，
  │    原文带 `good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list` 四前提）
  │    错移成两个**无条件 schema**。SF-106 已裁决为槽型误植：现 `hrreAll/hrreSAll`
  │    改为前提承载形 `markedList L hL N' r' y → ¬ finalList L r' → …`（槽前提
  │    变弱 ⇒ 定理变强；结论逐字不变）。
  │ ② `core_split_normal_list_assumption L` **不显式携入**：证体零消费
  │    （HOL 同；件1/件1a/2B1 同口径）。
  │ ③ HOL `transform_count L N r x`（链 def）↦ `transformCountSpine`
  │    （本波新 def，`minNumSpine`+`Nat.sInf_le`）：lnrx 的边界用 spine 计数，
  │    `transformCountSpineNot` 直证（`sInf` 极小性一步，免桥、免 chain marked）。
  │ ④ `transAddSpine`（HOL `trans_add`）只落**一步折叠**形（succ 投影），
  │    不落一般 `i+j` 形——本总装不消费一般形。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NewvertexPreppedTransformSpine
import Kepler.Text.TameSpine.Reduction3HbridgeElim
import Kepler.Text.ChainSpineBridge
import Kepler.Text.Reduction4
import Kepler.Text.TameSpine.JcajyduTowerConsumers
import Kepler.Text.TameSpine.ChainTav2Interface
import Kepler.Text.ChainBridgeParts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 一步折叠（trans_add 的 succ 投影形） -/

/-- 状态对的一步折叠（对形）：`(transform)^[j+1] (N,r) = (transform)^[1] (状态 j)`。 -/
theorem transSuccSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (j : ℕ) :
    (transformListSpine L x)^[j + 1] (N, r)
      = (transformListSpine L x)^[1] ((transformListSpine L x)^[j] (N, r)) := by
  rw [Function.iterate_succ_apply', Function.iterate_one]

theorem ntransSuccSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (j : ℕ) :
    ntransSpine L N r x (j + 1)
      = ntransSpine L (ntransSpine L N r x j) (rtransSpine L N r x j) x 1 :=
  congrArg Prod.fst (transSuccSpine L N r x j)

theorem rtransSuccSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (j : ℕ) :
    rtransSpine L N r x (j + 1)
      = rtransSpine L (ntransSpine L N r x j) (rtransSpine L N r x j) x 1 :=
  congrArg Prod.snd (transSuccSpine L N r x j)

/-! ## §2 transformCount 的 spine ¬final 传送（KBWPBHQ.hl:85） -/

/-- spine 自洽的 `transform_count`（HOL tame_defs2 同函数；spine 载体镜像）。 -/
noncomputable def transformCountSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) : ℕ :=
  minNumSpine {i : ℕ | finalListSpine L (rtransSpine L N r x i)}

/-- `j < transformCountSpine` ⇒ 第 j 状态尚未 final（`sInf` 极小性一步）。 -/
theorem transformCountSpineNot (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) {j : ℕ}
    (hj : j < transformCountSpine L N r x) :
    ¬ finalListSpine L (rtransSpine L N r x j) := by
  intro hfin
  have hle : transformCountSpine L N r x ≤ j := by
    have hmem : j ∈ {i : ℕ | finalListSpine L (rtransSpine L N r x i)} := hfin
    simpa only [transformCountSpine, minNumSpine] using Nat.sInf_le hmem
  omega

/-! ## §3 总装：lnrx_induction 的 spine 形 -/


/-- `lm` 极小集非空（`Reduction5J5Tav2Bridge` 同证私件的 TameSpine 侧重落；
SF-106 槽型重构所需：spine marked + ¬final ⇒ chain `lm` 集非空）。 -/
private theorem lmSetNonemptyOfNotFinal (L : fgraph ℕ) {r : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hd : d ∈ r) (hr1 : r.Nodup) (hnext : nextEl r d = fList L d)
    (hf : ¬ Kepler.Text.Reduction5.finalList L r) :
    ({m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty := by
  by_contra hcon
  have hall : ∀ m : ℕ, (nextEl r)^[m + 2] d = fList L ((nextEl r)^[m + 1] d) := by
    intro m
    by_contra hc
    exact hcon ⟨m, hc⟩
  simp only [Kepler.Text.Reduction5.finalList] at hf
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

/-- **spine marked（全量）⇒ chain `markedList`**（`Reduction5J5Tav2Bridge` 内联构造
的公开重落；`lm` 非空桥 + `sListEqOfLm` + `markedList_iff_markedListSpineFull`）。
SF-106 下 `lnrxInductionSpine` 的状态 k 用此把 spine marked 转成槽前提。 -/
private theorem markedListOfSpineFull (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hmS : MarkedListSpineFull hL N r x) (hfin : ¬ finalListSpine L r) :
    Kepler.Text.ChainLists.markedList L hL N r x := by
  have hr1 : r.Nodup := (List.nodup_flatten.mp hmS.1.2.1.1).1 _ hmS.1.2.2.1
  have hnext : nextEl r x = fList L x := hmS.1.2.2.2.2.2.1
  have hfinC : ¬ Kepler.Text.Reduction5.finalList L r := hfin
  have hlm := lmEqLMSpineOfNonempty L
    (lmSetNonemptyOfNotFinal L hmS.1.2.2.2.1 hr1 hnext hfinC)
  have hs0 : Kepler.Text.ChainLists.sList L r x = sListSpine L r x := sListEqOfLm L hlm
  exact (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs0).mpr hmS

/-- **HOL `lnrx_induction`**（reduction3.hl:2706-2757）spine 形：
`j < transform_count` ⇒ 状态 j 同时保持 `newvertex_prepped` 与 `element_pre`。 -/
theorem lnrxInductionSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hrreAll : ∀ (N' : List (List (ℕ × ℕ))) (r' : List (ℕ × ℕ)) (y : ℕ × ℕ),
      Kepler.Text.ChainLists.markedList L hL N' r' y →
      ¬ Kepler.Text.Reduction5.finalList L r' →
      Kepler.Text.Reduction5.rRtransEq L N' r' y)
    (hrreSAll : ∀ (N' : List (List (ℕ × ℕ))) (r' : List (ℕ × ℕ)) (y : ℕ × ℕ),
      Kepler.Text.ChainLists.markedList L hL N' r' y →
      ¬ Kepler.Text.Reduction5.finalList L r' →
      rRtransEqSpine L N' r' y)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hpre : Kepler.Text.Reduction3.elementPre L N) :
    ∀ j : ℕ, j < transformCountSpine L N r x →
      Kepler.Text.Reduction3.newvertexPrepped L (ntransSpine L N r x j)
          (rtransSpine L N r x j) x
        ∧ Kepler.Text.Reduction3.elementPre L (ntransSpine L N r x j) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨hnvp, hpre⟩
  | succ k ih =>
    intro hj
    have hjk : k < transformCountSpine L N r x := by omega
    obtain ⟨ihnvp, ihpre⟩ := ih hjk
    have hmk : MarkedListSpineFull hL (ntransSpine L N r x k)
        (rtransSpine L N r x k) x :=
      aqiunpp3_top L hL k hgn hm
    have hnf : ¬ finalListSpine L (rtransSpine L N r x k) :=
      transformCountSpineNot L N r x hjk
    have hmkC : Kepler.Text.ChainLists.markedList L hL
        (ntransSpine L N r x k) (rtransSpine L N r x k) x :=
      markedListOfSpineFull L hL hmk hnf
    have hnvp' : Kepler.Text.Reduction3.newvertexPrepped L
        (ntransSpine L (ntransSpine L N r x k) (rtransSpine L N r x k) x 1)
        (rtransSpine L (ntransSpine L N r x k) (rtransSpine L N r x k) x 1) x :=
      newvertexPreppedTransformSpine L hL hgn
        (hrreAll (ntransSpine L N r x k) (rtransSpine L N r x k) x hmkC hnf) hmk ihnvp hnf ihpre
        (hrreSAll (ntransSpine L N r x k) (rtransSpine L N r x k) x hmkC hnf)
    have hpre' : Kepler.Text.Reduction3.elementPre L
        (ntransSpine L (ntransSpine L N r x k) (rtransSpine L N r x k) x 1) :=
      elementsOfListNtransTop L hL hgn
        (hrreAll (ntransSpine L N r x k) (rtransSpine L N r x k) x hmkC hnf) hmk ihnvp ihpre
    rw [ntransSuccSpine L N r x k, rtransSuccSpine L N r x k]
    exact ⟨hnvp', hpre'⟩

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.transSuccSpine
#print axioms Kepler.Text.TameSpine.ntransSuccSpine
#print axioms Kepler.Text.TameSpine.rtransSuccSpine
#print axioms Kepler.Text.TameSpine.transformCountSpineNot
#print axioms Kepler.Text.TameSpine.lnrxInductionSpine
