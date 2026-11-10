/-
  Kepler.Text.ChainSpineBridge — chain↔spine 桥（Wave C 后路线①）：
  `Reduction5.ntrans/rtrans =?= ntransSpine/rtransSpine`（marked 前提下全 i）。

  ┌─ 归属对账 / 义务表（DELIVERY_2WaveC §6 实测残差）──────────────────
  │ rfl 探针：i=0 无条件 PASS；i≥1 残差 = 逐字
  │  `(replace [splitC.2] N ++ [splitC.1], splitC.2)` vs Spine 同名形。
  │ 本文件四段闭合：
  │ ① `replaceEqSpine`（`replace`(BEq) ↔ `replaceSpine`(DecidableEq) 孪生）；
  │ ② `splitNormalListEqSpine`（两岛 split 定义级同构：`t == v` vs
  │    `decide (t = v)` 的 filter 等价 + append 结合归正）；
  │ ③ `lyEqSpine`/`lzEqSpine`：链/spine 的 hypY/hypZ 各自等 l'y/l'z
  │    （ChainMarkedTranslate 的 hypYLChain/hypZLzChain × TameList12 的
  │    hypYL/hypZLz 传递——两私件 lmEqLMSpine/lzEqLZSpine 免重推）；
  │ ④ `transformStepEqSpine`/`transformIterEqSpine`：单步 + i 归纳
  │    （中途 marked 由链侧 `AqiunppSlot` 供）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① 常量桥不走 ChainMarkedTranslate 私有 lmEqLMSpine/lyEqLYSpine/
  │    lpEqLPSpine/lzEqLZSpine 重推，而走**双公开 hyp 桥传递**（四个
  │    hypM/hypY/hypP/hypZ 两岛皆公开）——义务表 ① 由 ~70 行降至 6 行。
  │ ② `splitNormalList` 孪生以 `t == v = decide (t = v)`（LawfulBEq）+
  │    `List.append_assoc` 归正一次性收口（无逐段归纳）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.ChainMarkedTranslate
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.Reduction3DefsAssumptionInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainSpineBridge

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList findFaceDarts fList nextEl prevEl)
open Kepler.Text.Reduction5 (Dart)
open Kepler.Text.ChainLists (markedList)
open Kepler.Text.TameSpine (rtransSpine ntransSpine transformListSpine replaceSpine
  splitNormalListSpine lYSpine lZSpine finalListSpine splitConditionListSpine
  hypYL hypZLz)

variable {α : Type}

/-! ## §0 `replace` 孪生（BEq ↔ DecidableEq，路由图 §6 义务 3） -/

theorem replaceEqSpine [BEq α] [LawfulBEq α] [DecidableEq α] (x : α) (ys : List α) :
    ∀ l : List α, Kepler.Graphs.replace x ys l = replaceSpine x ys l := by
  intro l
  induction l with
  | nil => rfl
  | cons z zs ih =>
    have hbeq : (z == x) = decide (z = x) := by
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, decide_eq_true_eq]
    rw [Kepler.Graphs.replace, replaceSpine, hbeq]
    by_cases hzx : z = x
    · rw [if_pos (by simp [hzx]), if_pos hzx]
    · rw [if_neg (by simp [hzx]), if_neg hzx, ih]

/-! ## §1 `splitNormalList` 孪生（义务 2） -/

theorem splitNormalListEqSpine (L : fgraph ℕ) (r f : List Dart) (ram1 ram2 : Dart) :
    Kepler.Text.Reduction5.splitNormalList L r f ram1 ram2
      = splitNormalListSpine L r f ram1 ram2 := by
  have hpred : ∀ v : ℕ,
      List.filter (fun t : ℕ => t == v) (List.flatten L)
        = List.filter (fun t : ℕ => decide (t = v)) (List.flatten L) := by
    intro v
    apply List.filter_congr
    intro t _
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
  simp only [Kepler.Text.Reduction5.splitNormalList, splitNormalListSpine,
    List.append_assoc, hpred]

/-! ## §2 常量桥（义务 1；双公开 hyp 桥传递） -/

theorem lyEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ Kepler.Text.Reduction5.finalList L r) :
    Kepler.Text.Reduction5.ly L r d = lYSpine L r d := by
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hsc : splitConditionListSpine hL N r d :=
    Kepler.Text.ChainMarkedTranslate.markedListSplitOfMarked L hL hm hf
  exact (Kepler.Text.ChainMarkedTranslate.hypYLChain L hL hgn hunL hm hf).symm.trans
    (hypYL L hL hgn hunL hnext hsc)

theorem lzEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ Kepler.Text.Reduction5.finalList L r) :
    Kepler.Text.Reduction5.lz L N r d = lZSpine L N r d := by
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hsc : splitConditionListSpine hL N r d :=
    Kepler.Text.ChainMarkedTranslate.markedListSplitOfMarked L hL hm hf
  exact (Kepler.Text.ChainMarkedTranslate.hypZLzChain L hL hgn hunL hm hf).symm.trans
    (hypZLz L hL hgn hunL hnext hsc)

/-! ## §3 单步与迭代（义务 4） -/

/-- 单步：`transformList = transformListSpine`（同一 `(N, r)`、marked/¬final 分案）。 -/
theorem transformStepEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) :
    Kepler.Text.Reduction5.transformList L x (N, r) = transformListSpine L x (N, r) := by
  by_cases hf : Kepler.Text.Reduction5.finalList L r
  · have hfS : finalListSpine L r :=
      (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp hf
    simp only [Kepler.Text.Reduction5.transformList, transformListSpine,
      if_pos hf, if_pos hfS]
  · have hfS : ¬ finalListSpine L r := fun h =>
      hf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
    have hly : Kepler.Text.Reduction5.ly L r x = lYSpine L r x :=
      lyEqSpine L hL hgn hunL hm hf
    have hlz : Kepler.Text.Reduction5.lz L N r x = lZSpine L N r x :=
      lzEqSpine L hL hgn hunL hm hf
    simp only [Kepler.Text.Reduction5.transformList, transformListSpine,
      if_neg hf, if_neg hfS, hly, hlz, splitNormalListEqSpine, replaceEqSpine]

/-- 全 i：`(transformList x)^[i] (N,r) = (transformListSpine x)^[i] (N,r)`。 -/
theorem transformIterEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) :
    ∀ i : ℕ, (Kepler.Text.Reduction5.transformList L x)^[i] (N, r)
      = (transformListSpine L x)^[i] (N, r) := by
  intro i
  induction i with
  | zero => rfl
  | succ k ih =>
    have hmk : markedList L hL ((Kepler.Text.Reduction5.transformList L x)^[k] (N, r)).1
        ((Kepler.Text.Reduction5.transformList L x)^[k] (N, r)).2 x :=
      haq hgn N r x hm k
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact transformStepEqSpine L hL hgn hunL hmk

/-! ## §4 主桥（消费者面） -/

theorem rtransEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ) :
    Kepler.Text.Reduction5.rtrans L N r x i = rtransSpine L N r x i :=
  congrArg Prod.snd (transformIterEqSpine L hL hgn hunL haq hm i)

theorem ntransEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ) :
    Kepler.Text.Reduction5.ntrans L N r x i = ntransSpine L N r x i :=
  congrArg Prod.fst (transformIterEqSpine L hL hgn hunL haq hm i)

/-- 对偶形：状态对整体相等（`(ntrans, rtrans)` 双分量一次给）。 -/
theorem pairEqSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ) :
    (Kepler.Text.Reduction5.ntrans L N r x i, Kepler.Text.Reduction5.rtrans L N r x i)
      = (ntransSpine L N r x i, rtransSpine L N r x i) :=
  transformIterEqSpine L hL hgn hunL haq hm i

end Kepler.Text.ChainSpineBridge

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.ChainSpineBridge.replaceEqSpine
#print axioms Kepler.Text.ChainSpineBridge.splitNormalListEqSpine
#print axioms Kepler.Text.ChainSpineBridge.lyEqSpine
#print axioms Kepler.Text.ChainSpineBridge.lzEqSpine
#print axioms Kepler.Text.ChainSpineBridge.transformStepEqSpine
#print axioms Kepler.Text.ChainSpineBridge.transformIterEqSpine
#print axioms Kepler.Text.ChainSpineBridge.rtransEqSpine
#print axioms Kepler.Text.ChainSpineBridge.ntransEqSpine
#print axioms Kepler.Text.ChainSpineBridge.pairEqSpine
