/-
  Kepler.Text.TameSpine.JcajyduRed2Trans — jcajydu J2 批 1（w1）：HOL
  `reduction2.hl` 第一口 —— transform 恒等族 + `trans0`（170 处消费的工作马）
  + 单步变换结构（`rtrans_cat` / `ntrans1`）。

  ┌─ 考古锚（AGENTS §8；详见 lane DELIVERY.md）─────────────────────
  │ reduction2.hl（1,671 行/53 定理）自底向上的**最底部自含切片**就是本批
  │ 8 件：它们只消费 transform 定义层（TameList17 载体在册：
  │ splitNormalListSpine/transformListSpine/ntransSpine/rtransSpine/
  │ replaceSpine + TameList7 finalListSpine + TameList12 lYSpine/lZSpine）
  │ 与 next_el/prev_el 反演（TameLp.nextEl_prevEl + junk-value 补形），
  │ 不触 reduction2 上游（AQ 章/Hojodcm/newvertex/SplitFace 桥层）。
  │ 对工单「reduction2 主体零命中」的勘误：定理层确为零命中（逐名 grep
  │ 核实），但**定义层早已全落**（Reduction5Base 256 行 W0 + TameList17
  │ Spine 载体），且 trans0/rtrans_cat/ntrans1 的证词件 next_prev_id、
  │ marked_lemma_yz_in_face（TameList18）、rotate_to（TameList54）均已
  │ 在册或更晚批已落。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体裁定与偏差记档 ────────────────────────────────────────────
  │ 载体 = TameSpine Spine 族（战役既定：JcajyduShell/JcajyduRxBridge/
  │ TameList70-72 DANGEYJ 同域），不用 Text.Reduction5 的 W0 平行载体
  │（后者 import 纪律禁入 TameSpine，见 Reduction5Base 头注）。
  │ **勘误（DEF-FIX 候选，机器证据）**：TameList17:93 的
  │ `splitNormalListSpine.nd` 用 `List.range' 1 (sz x.1)` = [1..sz]，而
  │ HOL `split_normal_list`（tame_defs2.hl:171）是 `upt 1 (sz (FST x))`
  │ = `iota 1 (sz-1)` = [1..sz-1]（tame_defs.hl:383-387 iota/upt 定义 +
  │ tame_list.hl:501 upt_rec + reduction3.hl:206 upt_iota_simple 三处
  │ 互证：upt 上界**互斥**；Reduction5Base.splitNormalList 同件即
  │ `range' 1 (sz-1)` 正确形）。本批 8 件陈述只涉 `split.2`/`new2`
  │（nd/new1 支不进任何结论），对该偏差**不敏感**，照常在现有载体上
  │ 逐字镜像；偏差本体交编排者走 DEF-FIX 裁决，本批不触碰既有文件。
  └────────────────────────────────────────────────────────────────

  ┌─ 债务隔离 ─────────────────────────────────────────────────────
  │ TameList16:1109 `markedListIsNodeNondegenerate` 有在案 sorry（2-strike
  │ 止损债），下游 TameList17 markedListMarked/markedTranslate/hqymrtx1-3List
  │ 携带 sorryAx。本批 8 件证明零消费该链（rtransFinalProp 的
  │ MarkedListSpineFull 只是**未消费的前提槽**，HOL 同形），文件尾
  │ `#print axioms` 探针应全为标准三零 sorryAx。
  └────────────────────────────────────────────────────────────────

  载体折算（沿批 17/70-72 约定）：`betwn` ↦ `Kepler.Graphs.between`、
  `cat` ↦ `List.append`（++，右结合注记见 rtransCat）、`uniq` ↦
  `List.Nodup`、`next_el`/`prev_el` ↦ `Kepler.Assembly.nextEl/prevEl`、
  `find_face L y` ↦ `findFaceDarts L y`、`replace` ↦ `replaceSpine`、
  `POWER n` ↦ `Function.iterate n`、`l'y`/`l'z` ↦ `lYSpine`/`lZSpine`。

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (nextEl_prevEl)

/-! ## §0 next_el/prev_el 的 junk-value 反演（HOL Seq2.next_prev_id 形）-/

/-- `x ∉ s` 时 `nextEl` 退化为默认元 `x`（`s.idxOf x = s.length`：len = 0 走
headD 分支、len ≥ 1 走越界 getD 分支，两者均取 `x`；TameLp
la7_nextEl_of_notMem 的私件孪生，沿 TameList6/9/10 per-file-private
约定零共享）。 -/
private theorem nextElOfNotMem {α : Type*} [BEq α] [LawfulBEq α] {s : List α} {x : α}
    (hx : x ∉ s) : nextEl s x = x := by
  unfold nextEl
  by_cases h0 : s.length = 0
  · have hs : s = [] := List.length_eq_zero_iff.mp h0
    subst hs
    simp
  · have hidx : s.idxOf x = s.length := List.idxOf_eq_length_iff.mpr hx
    have hne1 : ¬(s.idxOf x = s.length - 1) := by rw [hidx]; omega
    rw [if_neg hne1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [hidx]; omega)]
    simp

/-- **HOL `Seq2.next_prev_id`**（seq2-compiled.hl:1784-:1786）的逐句形：
`uniq s ==> next_el s (prev_el s x) = x`——**只需 uniq**（`x ∉ s` 时
prev_el/next_el 均 junk-退化为 `x`，恒等式平凡成立）。Lean 树内
TameLp.nextEl_prevEl 带的是强化前提 `x ∈ s`（tame_list 私有消费形），
reduction2 的 `rtrans_cat`（reduction2.hl:434-439）消费的恰是免 MEM 形，
故补此公开件。雷区记档（本轮实测）：nextEl 族泛型定理沿 TameLp
`[BEq α][LawfulBEq α][DecidableEq α]` 三例随形——BEq 留可合成参，消费点
ℕ×ℕ 处吃 `instBEqProd` 与定义体内烘焙实例一致；只绑 `[DecidableEq α]`
会把 BEq 钉死 `instBEqOfDecidableEq` 而失配（与 rx def 烘焙坑同源反向）。 -/
theorem nextElPrevElUniq {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} (hn : s.Nodup) (x : α) :
    nextEl s (prevEl s x) = x := by
  by_cases hx : x ∈ s
  · exact nextEl_prevEl hn hx
  · rw [prevEl, if_pos hx, nextElOfNotMem hx]

/-! ## §1 transform 恒等族（reduction2.hl:364-:405 + trans0 :778-:785）-/

/-- **HOL `transform_list_final_list_id`**（reduction2.hl:364-:370）
`final_list L r ==> transform_list L x (N,r) = (N,r)`——final 支定义性恒等。 -/
theorem transformListFinalListId (L : fgraph ℕ) (x : ℕ × ℕ)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (hf : finalListSpine L r) :
    transformListSpine L x (N, r) = (N, r) := by
  simp only [transformListSpine, if_pos hf]

/-- **HOL `transform_list_pow_final_list_id`**（reduction2.hl:372-:379）
`final_list L r ==> (transform_list L x POWER i) (N,r) = (N,r)`——
i 归纳，归纳步 `POWER 1` 分解 + 恒等件。 -/
theorem transformListPowFinalListId (L : fgraph ℕ) (x : ℕ × ℕ)
    (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ)) (hf : finalListSpine L r) (i : ℕ) :
    (transformListSpine L x)^[i] (N, r) = (N, r) := by
  induction i with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, transformListFinalListId L x N r hf]

/-- **HOL `rtrans_final_prop`**（reduction2.hl:381-:389）
`marked_list L N r x /\ final_list L r ==> final_list L (rtrans L N r x i)`
——marked_list 前提 HOL 证明未消费，逐字保留形状（MarkedListSpineFull
仅作未消费前提槽，零债务消费）。 -/
theorem rtransFinalProp (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : finalListSpine L r) (i : ℕ) :
    finalListSpine L (rtransSpine L N r x i) := by
  unfold rtransSpine
  rw [transformListPowFinalListId L x N r hf i]
  exact hf

/-- **HOL `ntrans_id`**（reduction2.hl:391-:397）
`final_list L r ==> ntrans L N r x 1 = N`。 -/
theorem ntransId (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (hf : finalListSpine L r) : ntransSpine L N r x 1 = N := by
  show ((transformListSpine L x)^[1] (N, r)).1 = N
  rw [Function.iterate_one, transformListFinalListId L x N r hf]

/-- **HOL `rtrans_id`**（reduction2.hl:399-:405）
`final_list L r ==> rtrans L N r x 1 = r`。 -/
theorem rtransId (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (hf : finalListSpine L r) : rtransSpine L N r x 1 = r := by
  show ((transformListSpine L x)^[1] (N, r)).2 = r
  rw [Function.iterate_one, transformListFinalListId L x N r hf]

/-- **HOL `trans0`**（reduction2.hl:778-:785）——reduction3/4 侧 170 处消费的
工作马：`rtrans L N r x 0 = r /\ ntrans L N r x 0 = N /\
ytrans L N r x 0 = l'y L r x /\ ztrans L N r x 0 = l'z L N r x`。
Spine 载体无 ytrans/ztrans 独立 def（= `ly∘rtrans`/`lz∘ntrans∘rtrans` 复合，
HOL tame_defs2.hl:475-479 定义即复合形），按复合形逐字落，i = 0 四件全
rfl（POWER 0 定义性归约）。 -/
theorem trans0 (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) :
    rtransSpine L N r x 0 = r ∧ ntransSpine L N r x 0 = N ∧
      lYSpine L (rtransSpine L N r x 0) x = lYSpine L r x ∧
      lZSpine L (ntransSpine L N r x 0) (rtransSpine L N r x 0) x = lZSpine L N r x :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §2 单步变换结构（reduction2.hl:407-:441 rtrans_cat + :1487-:1506 ntrans1）-/

/-- **HOL `rtrans_cat`**（reduction2.hl:407-:441）：
`~final_list L r /\ uniq r ==> rtrans L N r x 1 = cat (cat (cat [z]
(betwn r z y)) [y]) (betwn f y z)`，其中 `y = l'y L r x`、`z = l'z L N r x`、
`f = find_face L y`（HOL 的三层 `cat` 左结合 = `(a ++ b ++ c) ++ d`，
Lean 侧括号显式给出）。

HOL 证明（:416-:440）：`rtrans`/`POWER 1`/`transform_list` 展开 → ¬final 支
→ `split_normal_list` 展开 → `Seq.catA` → ram2' = z（`next_prev_id`，只需
`uniq r`，junk-value 形——本文件 §0）→ z' = z。Lean 逐句镜像。 -/
theorem rtransCat (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (hf : ¬finalListSpine L r) (hun : r.Nodup) :
    rtransSpine L N r x 1 =
      (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
          ++ [lYSpine L r x]) ++
        between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x) := by
  have key : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hun _
  have hstep : rtransSpine L N r x 1 =
      (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
  rw [hstep, splitNormalListSpine, key]

/-- **HOL `ntrans1`**（reduction2.hl:1487-:1506）：
`~final_list L r ==> ntrans L N r x 1 = cat (replace r [f2] N) [f1]`，
其中 `(f1,f2) = split_normal_list L r (find_face L y) y (prev_el r z)`
（`y = l'y L r x`、`z = l'z L N r x`）。HOL 证明 = `ntrans`/`POWER 1`/
`transform_list` 展开 → ¬final 支 `LET` 逐个消解（:1498-:1504）；Lean
逐句镜像（split 项在陈述中按 HOL 展开形重复两处，零缩写新 def）。 -/
theorem ntrans1 (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) (hf : ¬finalListSpine L r) :
    ntransSpine L N r x 1 =
      replaceSpine r [(splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2] N ++
        [(splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).1] := by
  show ((transformListSpine L x)^[1] (N, r)).1 = _
  rw [Function.iterate_one]
  simp only [transformListSpine, if_neg hf]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 `[propext, Classical.choice,
Quot.sound]`，零 sorryAx——本批八件证明零消费 TameList16:1109 在案债链。
落库时编排者可整体注释本节，不影响任何声明。） -/
#print axioms Kepler.Text.TameSpine.nextElPrevElUniq
#print axioms Kepler.Text.TameSpine.transformListFinalListId
#print axioms Kepler.Text.TameSpine.transformListPowFinalListId
#print axioms Kepler.Text.TameSpine.rtransFinalProp
#print axioms Kepler.Text.TameSpine.ntransId
#print axioms Kepler.Text.TameSpine.rtransId
#print axioms Kepler.Text.TameSpine.trans0
#print axioms Kepler.Text.TameSpine.rtransCat
#print axioms Kepler.Text.TameSpine.ntrans1
