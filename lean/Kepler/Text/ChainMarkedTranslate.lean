/-
  Kepler.Text.ChainMarkedTranslate — more_lemma2 尾部：HOL `marked_translate`
  （tame_list.hl:10100-:10144）的链层移植；`QRDYXYJ_list` 装配前置 1/3。

  ┌─ HOL 原文（reference/flyspeck/text_formalization/tame/tame_list.hl:10100）──
  │ !L N r d:A#A. good_list L /\ good_list_nodes L /\ marked_list L N r d /\
  │   ~final_list L r ==>
  │   (hyp'm (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d
  │      = l'm L r d /\
  │    hyp'p ... = l'p L N r d /\ hyp'q ... = l'q L N r d /\
  │    hyp'y ... = l'y L r d /\ hyp'z ... = l'z L N r d /\
  │    is_marked (…) /\ ~(loop_of_list r IN final_loops …) /\
  │    is_split_condition (…) (loop_of_list r) d)
  └────────────────────────────────────────────────────────────────

  ┌─ 状态：八合取中 6 条真证落地，合取 3 / 6 判 BLOCKED（上游 sorry）──
  │ HOL 结论八合取逐条对照（链层载体）：
  │   ① hyp'm = l'm              → `hypMLmChain`            ✓ 本文件
  │   ② hyp'p = l'p              → `hypPLpChain`            ✓ 本文件
  │   ③ hyp'q = l'q              → **BLOCKED**（见下）
  │   ④ hyp'y = l'y              → `hypYLChain`             ✓ 本文件
  │   ⑤ hyp'z = l'z              → `hypZLzChain`            ✓ 本文件
  │   ⑥ is_marked (…)            → **BLOCKED**（见下）
  │   ⑦ ¬(loop_of_list r ∈ final_loops) → 复用
  │      `ChainMarkedQ.notFinalList_not_mem_finalLoops`     ✓ 既有
  │   ⑧ is_split_condition …     → `isSplitConditionOfMarkedList` ✓ 本文件
  │ 聚合片（① ② ④ ⑤ ⑦ ⑧）：`markedTranslateCleanPart`。
  │
  │ ③/⑥ 的唯一阻塞点 = `TameSpine.markedListIsNodeNondegenerate`
  │ （TameList16:1095，body :1108-1109 为**在案 sorry**，注释 "NEEDS：ql 侧
  │ node 非退化支"；HOL 原路经 dart_of 选择函数章 :8043-:8221，未移植）。
  │ 机器证据：`#print axioms Kepler.Text.TameSpine.markedListMarked`
  │ = `[propext, sorryAx, Classical.choice, Quot.sound]`（`ChainMarkedQ.lean:15`
  │ 已录同一条）。链层 `l'q` 载体 `markedQ`（ChainMarkedQ 交付
  │ `logs/blocked_markedq_body.lean`）与 ⑥ 同源同锁。
  │ ⇒ 本文件**不写**假 `IsMarked`、**不改**陈述、**不删**合取：③/⑥ 明确挂账，
  │   待该支真证落库后由 `markedTranslateCleanPart` 直接补两合取即得原形。
  └────────────────────────────────────────────────────────────────

  ┌─ 归属对账（HOL Light Flyspeck，commit 1ce0353）─────────────────
  │ `marked_translate` tame_list.hl:10100-10144（proof 消费 `marked_conclusion`
  │ :10071 与 `hyp_m_l_m`/`hyp_p_l_p`/`hyp_q_l_q`/`hyp_y_l_y`/`hyp_z_l_z`
  │ :8624-:8919）。链层对应件：
  │   `l'm`/`l'y`/`l'p`/`l'z` = `Reduction5.lm`/`ly`/`lp`/`lz`
  │     （Reduction5Base:121/125/129/133，minNum/epsilon 口径）
  │   `hyp'm`/`hyp'y`/`hyp'p`/`hyp'z` = `Hypermap.hypM`/`hypY`/`hypP`/`hypZ`
  │   `marked_list` = `ChainLists.markedList`（ChainListsL2:118，9 合取）
  │   `loop_of_list`/`loop_family_of_list` = `ChainMarkedQ.loopOfList`/
  │     `loopFamilyOfList`（:73/:77）
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与 DIFFERS（交编排者知悉）───────────────────────────────
  │ ① `hgn : GoodListNodesTl L hL`（HOL `good_list_nodes L`）与
  │    `hunL : ∀ l ∈ L, l.Nodup`（HOL `all uniq L`，HOL 由 marked_list +
  │    simple_hypermap_all_uniq 内部取得）显式入参——与 Spine
  │    `TameList17.markedTranslate` 同款（`all uniq L` 不可由 `GoodList L`
  │    推出：后者只给 `(L.map listPairs).flatten` Nodup，GoodListDefs:38/:72）。
  │ ② `l'm` 族口径：链层取 `Reduction5.lm`（`minNum` = Classical.epsilon），
  │    非 Spine `lMSpine`（`Nat.sInf`）。二者在**空集上 junk 不同**，故本文件
  │    的 minNum↔minNumSpine 桥（§0）全部以「集非空」为显式前提：
  │    `lm` 侧由 `~final_list L r` 供（§0 `lmSetNonempty`），
  │    `lp` 侧由 `hypP_spec` 的取到支供。
  │ ③ 证明路线：链层谓词 → Spine 装配定理（`markedListCore_iff_markedListSpine`
  │    → `markListSplitConditionList` → `hypMLm`/`hypPLp`/`hypYL`/`hypZLz` →
  │    `splitConditionListSplit`）→ minNum 桥折回链载体。公开陈述**零 Spine
  │    谓词**（结论/前提只用链层名）；Spine 仅出现在证明内部。
  │    若编排者要求纯路线 A（不触 Spine 证明），`hypMLm` 族需就地重证
  │    `minNumPower`/`fListExtFListPower`/`indexfN` 引擎，实测 ≥300 行。
  │ ④ 链层 `split_condition_list`（tame_defs2.hl:673）在案无独立载体，
  │    以 `splitConditionListSpine` + `markedList` 核心桥直取（结论 ⑧ 已折回
  │    链层 `IsSplitCondition`）。不新造重复定义。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；不改任何既有陈述；
  注释正文不含「连字符紧跟斜杠」二字序列；comment-depth 0。
-/

import Kepler.Text.ChainMarkedQ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainMarkedTranslate

open Kepler.Assembly (GoodList eList fList nextEl listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart finalList)
open Kepler.Text.ChainLists (markedList normalList)
open Kepler.Text.ChainMarkedQ (loopOfList loopFamilyOfList notFinalList_not_mem_finalLoops)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine MarkedListSpine MarkedListSpineFull
  finalListSpine lMSpine lPSpine lYSpine lZSpine splitConditionListSpine
  loopOfListSpine loopFamilyOfListSpine
  normalListUniqNonnil markListSplitConditionList splitConditionListSplit
  hypMLm hypPLp hypYL hypZLz memLYDart dartsOfFamilyLoopFamilyOfList
  fListExtFListPower minNumSpine)
open Kepler.Text.ChainBridge (markedListCore_iff_markedListSpine
  finalList_iff_finalListSpine normalList_iff_normalListSpine)
open Kepler.Text (Hypermap Loop)

/-! ## §0 minNum ↔ minNumSpine 桥（junk 支只在集空时分叉，故全部带非空前提）

`Reduction5.minNum` 是 `Classical.epsilon` 选择，`TameSpine.minNumSpine` 是
`Nat.sInf`。两者在非空集上同取最小元；本文件所有桥都以 `S.Nonempty` 为
显式前提——非空性由 `lmSetNonempty`（`lm` 侧）与 `hypP_spec` 取到支
（`lp` 侧）供。 -/

/-- `Reduction5.minNum` 的最小元规格（`Reduction5.lean:65 minNum_spec` 的
同证重推导：该件在 `Kepler.Text.Reduction5` 模块，非本文件 import 闭包）。 -/
private theorem minNumSpec {S : Set ℕ} (hne : S.Nonempty) :
    Reduction5.minNum S ∈ S ∧ ∀ n ∈ S, Reduction5.minNum S ≤ n := by
  classical
  obtain ⟨m₀, hm₀⟩ := hne
  have hex : ∃ m : ℕ, m ∈ S := ⟨m₀, hm₀⟩
  have hmin : Nat.find hex ∈ S ∧ ∀ n ∈ S, Nat.find hex ≤ n :=
    ⟨Nat.find_spec hex, fun n hn => Nat.find_min' hex hn⟩
  exact Classical.epsilon_spec (p := fun m => m ∈ S ∧ ∀ n ∈ S, m ≤ n)
    ⟨Nat.find hex, hmin⟩

/-- `minNum = minNumSpine`（非空集上；`le_antisymm` 两侧互为下界）。 -/
private theorem minNumEqMinNumSpine {S : Set ℕ} (hne : S.Nonempty) :
    Reduction5.minNum S = minNumSpine S :=
  le_antisymm ((minNumSpec hne).2 _ (Nat.sInf_mem hne))
    (Nat.sInf_le (minNumSpec hne).1)

/-- `lm` 的极小集非空：`~final_list L r` + `next_el r d = f_list L d` +
`d ∈ r` + `r` 无重复。反证：若对所有 `m` 等式都成立，沿 `next_el` 轨道
（`indexfN` 定位到反例 `z`）可得 `f_list z = next_el r z`，与 `~final_list` 矛盾。 -/
private theorem lmSetNonempty (L : fgraph ℕ) {r : List Dart} {d : Dart}
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
  have hz1 : (nextEl r)^[TameSpine.indexf d z r] d = z :=
    TameSpine.indexfN hd hzr hr1
  rcases Nat.eq_zero_or_pos (TameSpine.indexf d z r) with hk | hk
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

/-- 链层 `lm = lMSpine`（非空前提由 `lmSetNonempty` 供）。 -/
private theorem lmEqLMSpine (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hne : ({m : ℕ | (nextEl r)^[m + 2] d
      ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty) :
    Reduction5.lm L r d = lMSpine L r d :=
  minNumEqMinNumSpine hne

/-- 链层 `ly = lYSpine`（由 `lm = lMSpine` 直接换元）。 -/
private theorem lyEqLYSpine (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hlm : Reduction5.lm L r d = lMSpine L r d) :
    Reduction5.ly L r d = lYSpine L r d := by
  show (fList L)^[Nat.succ (Reduction5.lm L r d)] d = (fList L)^[lMSpine L r d + 1] d
  rw [hlm]

/-! ## §1 链层 hyp ↔ l' 四桥（HOL `hyp_m_l_m`/`hyp_p_l_p`/`hyp_y_l_y`/`hyp_z_l_z`） -/

/-- `markedList` 核心 7 合取 → Spine 核心（`ChainBridge` 桥，零 `sList` 槽）。 -/
private theorem markedListCoreOfMarked (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) : MarkedListSpine hL N r d :=
  (markedListCore_iff_markedListSpine L hL N r d).mp
    ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
      hm.2.2.2.2.2.2.1⟩

/-- `markedList + ~final_list` → Spine `split_condition_list`（私有支撑）。 -/
private theorem markedListSplitOfMarked (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    splitConditionListSpine hL N r d :=
  markListSplitConditionList L hL (markedListCoreOfMarked L hL hm)
    (fun hc => hf ((finalList_iff_finalListSpine L r).mpr hc))

/-- **HOL `hyp_m_l_m`**（tame_list.hl:8624-:8711）链层形：
`hyp'm = l'm`（`l'm` 取链层 `Reduction5.lm`）。`hypMLm`（Spine）+ 集非空桥。 -/
theorem hypMLmChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).hypM (loopFamilyOfList N) (loopOfList r) d
      = Reduction5.lm L r d := by
  show (hypermapOfList L hL).hypM (loopFamilyOfListSpine N) (loopOfListSpine r) d
    = Reduction5.lm L r d
  have hmS := markedListCoreOfMarked L hL hm
  have hsc : splitConditionListSpine hL N r d := markedListSplitOfMarked L hL hm hf
  obtain ⟨hr1, _⟩ := normalListUniqNonnil hmS.2.1 hmS.2.2.1
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  rw [hypMLm L hL hgn hunL hnext hsc]
  exact (lmEqLMSpine L (lmSetNonempty L hmS.2.2.2.1 hr1 hnext hf)).symm

/-- **HOL `hyp_y_l_y`**（tame_list.hl:8727-:8745）链层形：`hyp'y = l'y`。 -/
theorem hypYLChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).hypY (loopFamilyOfList N) (loopOfList r) d
      = Reduction5.ly L r d := by
  show (hypermapOfList L hL).hypY (loopFamilyOfListSpine N) (loopOfListSpine r) d
    = Reduction5.ly L r d
  have hmS := markedListCoreOfMarked L hL hm
  have hsc : splitConditionListSpine hL N r d := markedListSplitOfMarked L hL hm hf
  obtain ⟨hr1, _⟩ := normalListUniqNonnil hmS.2.1 hmS.2.2.1
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hlm : Reduction5.lm L r d = lMSpine L r d :=
    lmEqLMSpine L (lmSetNonempty L hmS.2.2.2.1 hr1 hnext hf)
  rw [hypYL L hL hgn hunL hnext hsc]
  exact (lyEqLYSpine L hlm).symm

/-- `lp` 侧非空：`hypP` 自身取到（`hypP_spec` 的取到支经 `darts_of_family =
set_of_list (flatten N)` 与 `fList = faceMap` 幂桥折算到 `lp` 的集合）。 -/
private theorem lpSetNonempty (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hnext : nextEl r d = fList L d) (hsc : splitConditionListSpine hL N r d) :
    ({p : ℕ | (fList L)^[p + 1] (lYSpine L r d) ∈ N.flatten}).Nonempty := by
  have hn : NormalListSpine hL N := hsc.2.1
  have hyD : lYSpine L r d ∈ listOfDarts L := memLYDart L hL hsc
  have hsplit : (hypermapOfList L hL).IsSplitCondition
      (loopFamilyOfListSpine N) (loopOfListSpine r) d :=
    splitConditionListSplit L hL hgn hunL hsc
  have hY : lYSpine L r d = (hypermapOfList L hL).hypY
      (loopFamilyOfListSpine N) (loopOfListSpine r) d :=
    (hypYL L hL hgn hunL hnext hsc).symm
  have hpf : ((hypermapOfList L hL).faceMap ^
      ((hypermapOfList L hL).hypP (loopFamilyOfListSpine N)
        (loopOfListSpine r) d + 1))
      ((hypermapOfList L hL).hypY (loopFamilyOfListSpine N)
        (loopOfListSpine r) d) ∈ N.flatten := by
    have h := (Hypermap.hypP_spec (hypermapOfList L hL) hsplit).2
    rw [dartsOfFamilyLoopFamilyOfList L hL hn] at h
    simpa using h
  exact ⟨(hypermapOfList L hL).hypP (loopFamilyOfListSpine N) (loopOfListSpine r) d, by
    show (fList L)^[((hypermapOfList L hL).hypP (loopFamilyOfListSpine N)
      (loopOfListSpine r) d) + 1] (lYSpine L r d) ∈ N.flatten
    rw [← fListExtFListPower L hL hyD ((hypermapOfList L hL).hypP
      (loopFamilyOfListSpine N) (loopOfListSpine r) d + 1), hY]
    exact hpf⟩

/-- 链层 `lp = lPSpine`（`ly = lYSpine` 换元 + 非空前提）。 -/
private theorem lpEqLPSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hnext : nextEl r d = fList L d) (hsc : splitConditionListSpine hL N r d)
    (hly : Reduction5.ly L r d = lYSpine L r d) :
    Reduction5.lp L N r d = lPSpine L N r d := by
  have hne := lpSetNonempty L hL hgn hunL hnext hsc
  have hstep : Reduction5.lp L N r d
      = Reduction5.minNum {p : ℕ | (fList L)^[p + 1] (lYSpine L r d) ∈ N.flatten} := by
    show Reduction5.minNum {p : ℕ | (fList L)^[Nat.succ p] (Reduction5.ly L r d)
      ∈ N.flatten} = _
    rw [hly]
  exact hstep.trans (minNumEqMinNumSpine hne)

/-- **HOL `hyp_p_l_p`**（tame_list.hl:8844-:8882）链层形：`hyp'p = l'p`。 -/
theorem hypPLpChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).hypP (loopFamilyOfList N) (loopOfList r) d
      = Reduction5.lp L N r d := by
  show (hypermapOfList L hL).hypP (loopFamilyOfListSpine N) (loopOfListSpine r) d
    = Reduction5.lp L N r d
  have hmS := markedListCoreOfMarked L hL hm
  have hsc : splitConditionListSpine hL N r d := markedListSplitOfMarked L hL hm hf
  obtain ⟨hr1, _⟩ := normalListUniqNonnil hmS.2.1 hmS.2.2.1
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hlm : Reduction5.lm L r d = lMSpine L r d :=
    lmEqLMSpine L (lmSetNonempty L hmS.2.2.2.1 hr1 hnext hf)
  rw [hypPLp L hL hgn hunL hnext hsc]
  exact (lpEqLPSpine L hL hgn hunL hnext hsc (lyEqLYSpine L hlm)).symm

/-- 链层 `lz = lZSpine`（`lp`/`ly` 两桥换元）。 -/
private theorem lzEqLZSpine (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} {d : Dart}
    (hly : Reduction5.ly L r d = lYSpine L r d)
    (hlp : Reduction5.lp L N r d = lPSpine L N r d) :
    Reduction5.lz L N r d = lZSpine L N r d := by
  show (fList L)^[Nat.succ (Reduction5.lp L N r d)] (Reduction5.ly L r d)
    = (fList L)^[lPSpine L N r d + 1] (lYSpine L r d)
  rw [hlp, hly]

/-- **HOL `hyp_z_l_z`**（tame_list.hl:8884-:8906）链层形：`hyp'z = l'z`。 -/
theorem hypZLzChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).hypZ (loopFamilyOfList N) (loopOfList r) d
      = Reduction5.lz L N r d := by
  show (hypermapOfList L hL).hypZ (loopFamilyOfListSpine N) (loopOfListSpine r) d
    = Reduction5.lz L N r d
  have hmS := markedListCoreOfMarked L hL hm
  have hsc : splitConditionListSpine hL N r d := markedListSplitOfMarked L hL hm hf
  obtain ⟨hr1, _⟩ := normalListUniqNonnil hmS.2.1 hmS.2.2.1
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hlm : Reduction5.lm L r d = lMSpine L r d :=
    lmEqLMSpine L (lmSetNonempty L hmS.2.2.2.1 hr1 hnext hf)
  have hly : Reduction5.ly L r d = lYSpine L r d := lyEqLYSpine L hlm
  have hlp : Reduction5.lp L N r d = lPSpine L N r d :=
    lpEqLPSpine L hL hgn hunL hnext hsc hly
  rw [hypZLz L hL hgn hunL hnext hsc]
  exact (lzEqLZSpine L hly hlp).symm

/-! ## §2 链层 `is_split_condition`（HOL 结论第 8 合取） -/

/-- **HOL `marked_translate` 结论第 8 合取**（tame_list.hl:10140-10143）：
`marked_list L N r d → ~final_list L r →
 is_split_condition (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) d`。
`split_condition_list_split`（TameList12:204）经 `markedList` 核心桥转写。 -/
theorem isSplitConditionOfMarkedList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).IsSplitCondition (loopFamilyOfList N) (loopOfList r) d := by
  simpa only [loopFamilyOfList, loopOfList] using
    splitConditionListSplit L hL hgn hunL (markedListSplitOfMarked L hL hm hf)

/-! ## §3 HOL `marked_translate` 干净片（八合取取 ① ② ④ ⑤ ⑦ ⑧）

合取 ③（`hyp'q = l'q`）与 ⑥（`is_marked`）依赖上游 `TameList16:1109` 在案
sorry，本文件不写假桩；该支落库后把两合取接到本聚合件即得 HOL 原形。 -/

/-- **HOL `marked_translate`（tame_list.hl:10100-10144）6/8 干净片**。
合取映射（HOL 顺序）：① `hyp'm = l'm`、② `hyp'p = l'p`、④ `hyp'y = l'y`、
⑤ `hyp'z = l'z`、⑦ `¬(loop_of_list r ∈ final_loops …)`、⑧ `is_split_condition`。
缺 ③ `hyp'q = l'q` 与 ⑥ `is_marked`（上游 TameList16:1109 sorry，BLOCKED）。 -/
theorem markedTranslateCleanPart (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : markedList L hL N r d) (hf : ¬ finalList L r) :
    (hypermapOfList L hL).hypM (loopFamilyOfList N) (loopOfList r) d
        = Reduction5.lm L r d ∧
      (hypermapOfList L hL).hypP (loopFamilyOfList N) (loopOfList r) d
        = Reduction5.lp L N r d ∧
      (hypermapOfList L hL).hypY (loopFamilyOfList N) (loopOfList r) d
        = Reduction5.ly L r d ∧
      (hypermapOfList L hL).hypZ (loopFamilyOfList N) (loopOfList r) d
        = Reduction5.lz L N r d ∧
      loopOfList r ∉ (hypermapOfList L hL).finalLoops (loopFamilyOfList N) ∧
      (hypermapOfList L hL).IsSplitCondition (loopFamilyOfList N) (loopOfList r) d :=
  ⟨hypMLmChain L hL hgn hunL hm hf, hypPLpChain L hL hgn hunL hm hf,
    hypYLChain L hL hgn hunL hm hf, hypZLzChain L hL hgn hunL hm hf,
    notFinalList_not_mem_finalLoops L hL hm hf,
    isSplitConditionOfMarkedList L hL hgn hunL hm hf⟩

end Kepler.Text.ChainMarkedTranslate

/-! 公理审计锚（本文件编译即执行；预期全部 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.ChainMarkedTranslate.hypMLmChain
#print axioms Kepler.Text.ChainMarkedTranslate.hypYLChain
#print axioms Kepler.Text.ChainMarkedTranslate.hypPLpChain
#print axioms Kepler.Text.ChainMarkedTranslate.hypZLzChain
#print axioms Kepler.Text.ChainMarkedTranslate.isSplitConditionOfMarkedList
#print axioms Kepler.Text.ChainMarkedTranslate.markedTranslateCleanPart
