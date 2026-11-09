/-
  Kepler.Text.TameSpine.ChainTav2Interface — TAV2 Wave 0 接口层。

  ┌─ 范围（编排者 2026-11-10 批准；约 160–310 行）────────────────
  │ 目标：把 `transformAssumptionOfAq`（JcajyduAqTowerBase:329，13 个
  │ `aqNConcl` 前提 ⇒ Spine 无条件形）搬到**链层可消费形**：
  │   ① 链↔Spine 变换桥：`transformList`/`ntrans`/`rtrans` 在 i=1 处相等
  │      （`lm` 走 minNum↔sInf 非空桥；`sList`/`ly`/`lz`/`splitNormalList`/`replace` 同步）；
  │   ② 链层装配 `transformAssumptionOfAqChain`：13 槽 ⇒ 链 `markedList` 在
  │      (ntrans…1, rtrans…1) 处成立。
  │ **不新增 `transformAssumptionV2` def**（Spine 双件 + 桥即可复用；
  │ 若后续 J2 下游确需 def，另报 DEF-FIX 章程）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `l'm` 族：链 `Reduction5.lm`（minNum=epsilon）↔ Spine `lMSpine`（sInf）。
  │    仅在「集非空」时相等（空集 junk 不同）；本文件全部桥以非空为内证：
  │    `~final_list` + `MEM x r` + `uniq r` + `next_el r x = f_list L x`。
  │ ② `replace`（BEq）↔ `replaceSpine`（DecidableEq）：LawfulBEq 下逐点相等。
  │ ③ `split_normal_list` 的 `sz` 谓词 `t == v` ↔ `decide (t = v)`：ℕ 上逐点相等。
  │ ④ `sList`（range' 1 lm）↔ `sListSpine`（range lMSpine，i+1 指数）：
  │    `List.range'_eq_map_range` + `Nat.add_comm`。
  │ ⑤ 结论按「链层 markedList」写，Spine 只出现在证明内部。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `tav2w0_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainMarkedTranslate
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.TameList12
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList lm ly lp lz ntrans rtrans splitNormalList
  transformList)

/-! ## §0 基础桥：replace / splitNormalList / minNum / sList -/

/-- `replace`（BEq 版）与 `replaceSpine`（DecidableEq 版）逐点相等。 -/
theorem replaceEqReplaceSpine {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (x : α) (ys xs : List α) :
    Kepler.Graphs.replace x ys xs = Kepler.Text.TameSpine.replaceSpine x ys xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    rw [Kepler.Graphs.replace, Kepler.Text.TameSpine.replaceSpine]
    by_cases h : z = x
    · rw [if_pos (beq_iff_eq.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (beq_iff_eq.mp hc)), if_neg h, ih]

/-- 链 `splitNormalList` 与 Spine `splitNormalListSpine` 逐点相等
（唯一差异是 `sz` 谓词 `t == v` 与 `decide (t = v)`）。 -/
theorem splitNormalListEq (L : fgraph ℕ) (r f : List Dart) (ram1 ram2 : Dart) :
    Kepler.Text.Reduction5.splitNormalList L r f ram1 ram2
      = Kepler.Text.TameSpine.splitNormalListSpine L r f ram1 ram2 := by
  have hb : ∀ t v : ℕ, (t == v) = decide (t = v) := by
    intro t v
    by_cases h : t = v
    · subst h
      rw [beq_iff_eq.mpr rfl]
      exact (decide_eq_true rfl).symm
    · rw [beq_eq_false_iff_ne.mpr h, decide_eq_false_iff_not.mpr h]
  simp only [Kepler.Text.Reduction5.splitNormalList,
    Kepler.Text.TameSpine.splitNormalListSpine, hb, List.append_assoc]

/-- `Reduction5.minNum` 的最小元规格（非空集）。 -/
private theorem tav2w0_minNumSpec {S : Set ℕ} (hne : S.Nonempty) :
    Kepler.Text.Reduction5.minNum S ∈ S ∧
      ∀ n ∈ S, Kepler.Text.Reduction5.minNum S ≤ n := by
  classical
  obtain ⟨m₀, hm₀⟩ := hne
  have hex : ∃ m : ℕ, m ∈ S := ⟨m₀, hm₀⟩
  have hmin : Nat.find hex ∈ S ∧ ∀ n ∈ S, Nat.find hex ≤ n :=
    ⟨Nat.find_spec hex, fun n hn => Nat.find_min' hex hn⟩
  exact Classical.epsilon_spec (p := fun m => m ∈ S ∧ ∀ n ∈ S, m ≤ n)
    ⟨Nat.find hex, hmin⟩

/-- `minNum = minNumSpine`（非空集上；两侧互为下界）。 -/
theorem minNumEqMinNumSpine {S : Set ℕ} (hne : S.Nonempty) :
    Kepler.Text.Reduction5.minNum S = Kepler.Text.TameSpine.minNumSpine S :=
  le_antisymm ((tav2w0_minNumSpec hne).2 _ (Nat.sInf_mem hne))
    (Nat.sInf_le (tav2w0_minNumSpec hne).1)

/-- `lm` 极小集非空：`~final_list` + `next_el r d = f_list L d` + `d ∈ r` + `uniq r`。
（同证重落 ChainMarkedTranslate 私件 `lmSetNonempty`。） -/
private theorem tav2w0_lmSetNonempty (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hd : d ∈ r) (hr1 : r.Nodup) (hnext : nextEl r d = fList L d)
    (hf : ¬ finalList L r) :
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

/-- 链 `lm = lMSpine`（非空前提外部供给）。 -/
theorem lmEqLMSpineOfNonempty (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hne : ({m : ℕ | (nextEl r)^[m + 2] d
      ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty) :
    Kepler.Text.Reduction5.lm L r d = Kepler.Text.TameSpine.lMSpine L r d :=
  minNumEqMinNumSpine hne

/-- `sList = sListSpine`（由 `lm = lMSpine`；`range'` 换元 + `Nat.add_comm`）。 -/
theorem sListEqOfLm (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hlm : Kepler.Text.Reduction5.lm L r d = Kepler.Text.TameSpine.lMSpine L r d) :
    Kepler.Text.ChainLists.sList L r d = Kepler.Text.TameSpine.sListSpine L r d := by
  unfold Kepler.Text.ChainLists.sList Kepler.Text.TameSpine.sListSpine
  rw [hlm, List.range'_eq_map_range, List.map_map]
  rw [show (fun i => (fList L)^[i] d) ∘ (fun x => 1 + x)
      = (fun i => (fList L)^[i + 1] d) from by
    funext i
    rw [Function.comp_apply, Nat.add_comm]]

/-! ## §1 marked 态下的 ly / lz / transformList / ntrans / rtrans 桥 -/

/-- 链 `ly = lYSpine`（marked 态，经 `hypY` 双侧）。 -/
theorem lyEqLYSpineOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r) :
    Kepler.Text.Reduction5.ly L r x = Kepler.Text.TameSpine.lYSpine L r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hsc : Kepler.Text.TameSpine.splitConditionListSpine hL N r x :=
    Kepler.Text.ChainMarkedTranslate.markedListSplitOfMarked L hL hm hf
  exact (Kepler.Text.ChainMarkedTranslate.hypYLChain L hL hgn hunL hm hf).symm.trans
    (Kepler.Text.TameSpine.hypYL L hL hgn hunL hnext hsc)

/-- 链 `lz = lZSpine`（marked 态，经 `hypZ` 双侧）。 -/
theorem lzEqLZSpineOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r) :
    Kepler.Text.Reduction5.lz L N r x = Kepler.Text.TameSpine.lZSpine L N r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hsc : Kepler.Text.TameSpine.splitConditionListSpine hL N r x :=
    Kepler.Text.ChainMarkedTranslate.markedListSplitOfMarked L hL hm hf
  exact (Kepler.Text.ChainMarkedTranslate.hypZLzChain L hL hgn hunL hm hf).symm.trans
    (Kepler.Text.TameSpine.hypZLz L hL hgn hunL hnext hsc)

/-- 链 `transformList = transformListSpine`（marked 态、非终态，i=1 用）。 -/
theorem transformListOneEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r) :
    Kepler.Text.Reduction5.transformList L x (N, r)
      = Kepler.Text.TameSpine.transformListSpine L x (N, r) := by
  have hly := lyEqLYSpineOfMarked L hL hgn hm hf
  have hlz := lzEqLZSpineOfMarked L hL hgn hm hf
  have hsp := splitNormalListEq L r
    (findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x))
    (Kepler.Text.TameSpine.lYSpine L r x)
    (prevEl r (Kepler.Text.TameSpine.lZSpine L N r x))
  have hrp := replaceEqReplaceSpine r
  dsimp only [Kepler.Text.Reduction5.transformList, Kepler.Text.TameSpine.transformListSpine]
  rw [hly, hlz, hsp, hrp]
  rw [if_neg hf, if_neg (show ¬ Kepler.Text.TameSpine.finalListSpine L r from hf)]

/-- 链 `ntrans … 1 = ntransSpine … 1`（marked 态）。 -/
theorem ntransOneEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    Kepler.Text.Reduction5.ntrans L N r x 1 = Kepler.Text.TameSpine.ntransSpine L N r x 1 := by
  by_cases hf : finalList L r
  · simp only [Kepler.Text.Reduction5.ntrans, Kepler.Text.TameSpine.ntransSpine,
      Function.iterate_one, Kepler.Text.Reduction5.transformList,
      Kepler.Text.TameSpine.transformListSpine]
    rw [if_pos hf, if_pos (show Kepler.Text.TameSpine.finalListSpine L r from hf)]
  · rw [Kepler.Text.Reduction5.ntrans, Kepler.Text.TameSpine.ntransSpine,
      Function.iterate_one, Function.iterate_one,
      transformListOneEq L hL hgn hm hf]

/-- 链 `rtrans … 1 = rtransSpine … 1`（marked 态）。 -/
theorem rtransOneEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    Kepler.Text.Reduction5.rtrans L N r x 1 = Kepler.Text.TameSpine.rtransSpine L N r x 1 := by
  by_cases hf : finalList L r
  · simp only [Kepler.Text.Reduction5.rtrans, Kepler.Text.TameSpine.rtransSpine,
      Function.iterate_one, Kepler.Text.Reduction5.transformList,
      Kepler.Text.TameSpine.transformListSpine]
    rw [if_pos hf, if_pos (show Kepler.Text.TameSpine.finalListSpine L r from hf)]
  · rw [Kepler.Text.Reduction5.rtrans, Kepler.Text.TameSpine.rtransSpine,
      Function.iterate_one, Function.iterate_one,
      transformListOneEq L hL hgn hm hf]

/-! ## §2 链层装配：13 槽 ⇒ 链 markedList -/

/-- **TAV2 Wave 0 主件**：`transformAssumptionOfAq` 的链层可消费形——
13 个 `aqNConcl` 槽 ⇒ 链 `markedList` 在 (ntrans…1, rtrans…1) 处成立。
（链侧 `transformAssumptionV2` def 未新增；J2 下游以本定理的全称陈述
或 13 槽为条件槽前提。） -/
theorem transformAssumptionOfAqChain (L : fgraph ℕ) (hL : GoodList L)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL) (h6 : aq6Concl L hL)
    (h7 : aq7Concl L hL) (h8 : aq8Concl L hL) (h9 : aq9Concl L hL)
    (h10 : aq10Concl L hL) (h11 : aq11Concl L hL) (h12 : aq12Concl L hL)
    (h13 : aq13Concl L hL) :
    ∀ (N : List (List Dart)) (r : List Dart) (x : Dart),
      GoodListNodesTl L hL → Kepler.Text.ChainLists.markedList L hL N r x →
        Kepler.Text.ChainLists.markedList L hL
          (Kepler.Text.Reduction5.ntrans L N r x 1)
          (Kepler.Text.Reduction5.rtrans L N r x 1) x := by
  intro N r x hgn hm
  by_cases hf : finalList L r
  · have hn : Kepler.Text.Reduction5.ntrans L N r x 1 = N := by
      simp only [Kepler.Text.Reduction5.ntrans, Function.iterate_one,
        Kepler.Text.Reduction5.transformList]
      rw [if_pos hf]
    have hr : Kepler.Text.Reduction5.rtrans L N r x 1 = r := by
      simp only [Kepler.Text.Reduction5.rtrans, Function.iterate_one,
        Kepler.Text.Reduction5.transformList]
      rw [if_pos hf]
    rw [hn, hr]
    exact hm
  · -- 初始态：markedList → MarkedListSpineFull（sList 桥由 lm 非空桥供给）
    have hr1 : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
    have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
    have hlm : Kepler.Text.Reduction5.lm L r x = Kepler.Text.TameSpine.lMSpine L r x :=
      lmEqLMSpineOfNonempty L
        (tav2w0_lmSetNonempty L hm.2.2.2.1 hr1 hnext hf)
    have hs0 : Kepler.Text.ChainLists.sList L r x = Kepler.Text.TameSpine.sListSpine L r x :=
      sListEqOfLm L hlm
    have hmS : MarkedListSpineFull hL N r x :=
      (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs0).mp hm
    -- Spine 装配 + i=1 变换桥
    have hsAq : MarkedListSpineFull hL
        (Kepler.Text.TameSpine.ntransSpine L N r x 1)
        (Kepler.Text.TameSpine.rtransSpine L N r x 1) x :=
      transformAssumptionOfAq L hL h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
        N r x hgn hmS
    have hnt := ntransOneEq L hL hgn hm
    have hrt := rtransOneEq L hL hgn hm
    rw [← hnt, ← hrt] at hsAq
    -- 链层重新拼装 9 合取
    obtain ⟨hc, hfl, hsf⟩ := hsAq
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ :=
      (Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL _ _ _).mpr hc
    refine ⟨c1, c2, c3, c4, c5, c6, c7, ?_, ?_⟩
    · intro hfin
      exact (Kepler.Text.ChainBridge.flagList_iff_flagListSpine L _).mpr
        (hfl ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mp hfin))
    · intro hfin
      have hnd' : (Kepler.Text.Reduction5.rtrans L N r x 1).Nodup :=
        (normalListUniqNonnil hc.2.1 hc.2.2.1).1
      have hnext' : nextEl (Kepler.Text.Reduction5.rtrans L N r x 1) x = fList L x :=
        hc.2.2.2.2.2.1
      have hlm' : Kepler.Text.Reduction5.lm L
          (Kepler.Text.Reduction5.rtrans L N r x 1) x
          = Kepler.Text.TameSpine.lMSpine L
            (Kepler.Text.Reduction5.rtrans L N r x 1) x :=
        lmEqLMSpineOfNonempty L
          (tav2w0_lmSetNonempty L hc.2.2.2.1 hnd' hnext' hfin)
      have hs' : Kepler.Text.ChainLists.sList L
          (Kepler.Text.Reduction5.rtrans L N r x 1) x
          = Kepler.Text.TameSpine.sListSpine L
            (Kepler.Text.Reduction5.rtrans L N r x 1) x :=
        sListEqOfLm L hlm'
      exact (Kepler.Text.ChainBridge.sFlagList_iff_sFlagListSpine L _ _ _ hs').mpr
        (hsf (fun hsp => hfin
          ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr hsp)))

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.replaceEqReplaceSpine
#print axioms Kepler.Text.TameSpine.splitNormalListEq
#print axioms Kepler.Text.TameSpine.minNumEqMinNumSpine
#print axioms Kepler.Text.TameSpine.lmEqLMSpineOfNonempty
#print axioms Kepler.Text.TameSpine.sListEqOfLm
#print axioms Kepler.Text.TameSpine.lyEqLYSpineOfMarked
#print axioms Kepler.Text.TameSpine.lzEqLZSpineOfMarked
#print axioms Kepler.Text.TameSpine.transformListOneEq
#print axioms Kepler.Text.TameSpine.ntransOneEq
#print axioms Kepler.Text.TameSpine.rtransOneEq
#print axioms Kepler.Text.TameSpine.transformAssumptionOfAqChain
