/-
  Kepler.Text.Reduction5J5K2A2 — Lane A2.1 收尾（nb47）：
  `finalAssumptionYzInCore`（HOL reduction4.hl:727–794）**条件于强形 `hmisc`**，
  加塔层保持件（`elementPre` + `newvertexPrepped` 沿 `ntrans`/`rtrans` 迭代）。

  ┌─ 本件范围 ────────────────────────────────────────────────────────
  │ ① `elementPreAndNvpIter`：单步保持件（nb46 `elementPreStep` /
  │    `newvertexPreppedStep`）沿塔层迭代到任意 `n < k`；两个投影件
  │    `elementPreIter` / `newvertexPreppedIter` 为一行推论。
  │ ② `finalAssumptionYzInCore`：逐字对 HOL 陈述（含强形 `hmisc` 前提）。
  │    `i ≤ j` 支：`pnxvwfs1/2` 于状态 i（指数 `j-i`）；
  │    `j < i` 支：`ytrans j` 走 `propertiesOfYtrans0Spine` 于状态 j，
  │    `ztrans j` 走强形 `hmisc` 于状态 j。
  │ ③ **未交**：强形 `hmisc` 本体（`∀ N' r' i', K1Asm ∧ i' < tc ⇒ z0 ∈ rtrans i'`）
  │    ——`final_reduction_mem_z0_ri`（HOL 754 行）的推广；`NCVIBWU` i=0 链层件
  │    `ncvibwuV0FullChain` 已落，但塔层归纳 + 索引维护仍缺。卡点见 DELIVERY-nb47 §2。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5J5K2A2Up
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.TameSpine.Reduction3Pbflhet1
import Kepler.Text.ChainSpineBridge
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3Thm1
import Kepler.Text.Reduction3Thm2
import Kepler.Text.Reduction4Subseg4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)
open Kepler.Text.TameSpine (ntransSpine rtransSpine ytransSpine ztransSpine
  finalListSpine MarkedListSpineFull transformAssumptionSpine lYSpine)

/-- 塔层保持束：`n < k` 时 `elementPre L (ntrans n)` 与
`newvertexPrepped L (ntrans n) (rtrans n) x` 同时成立。
单步件 = nb46 `elementPreStep` / `newvertexPreppedStep`（后者吃 W5b `hrre`
+ nb46 `rRtransEqToSpine` 的 `hrreS`）。 -/
theorem elementPreAndNvpIter (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (hnvp0 : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep0 : Kepler.Text.Reduction3.elementPre L N) :
    ∀ n : ℕ, n < k →
      Kepler.Text.Reduction3.elementPre L (ntrans L N r x n) ∧
      Kepler.Text.Reduction3.newvertexPrepped L (ntrans L N r x n) (rtrans L N r x n) x
  | 0, _ => by
    rw [ntrans_zero, rtrans_zero]
    exact ⟨hep0, hnvp0⟩
  | n + 1, hn => by
    have hnk : n < k := by omega
    obtain ⟨hep_n, hnvp_n⟩ :=
      elementPreAndNvpIter L hL hgn hres haq hm hnf hk hnvp0 hep0 n hnk
    have hnf_n : ¬ finalList L (rtrans L N r x n) :=
      Kepler.Text.Reduction4.transformCount_not n (by rw [hk]; exact hnk)
    have hm_n : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x n) (rtrans L N r x n) x := haq hgn N r x hm n
    have hnt : ntrans L N r x (n + 1)
        = ntrans L (ntrans L N r x n) (rtrans L N r x n) x 1 := by
      rw [show n + 1 = 1 + n from by omega]
      exact (Kepler.Text.Reduction3.transAdd L N r x n 1).1
    have hrt : rtrans L N r x (n + 1)
        = rtrans L (ntrans L N r x n) (rtrans L N r x n) x 1 := by
      rw [show n + 1 = 1 + n from by omega]
      exact (Kepler.Text.Reduction3.transAdd L N r x n 1).2.1
    rw [hnt, hrt]
    exact ⟨elementPreStep L hL hgn hres haq hm_n hnf_n hnvp_n hep_n,
      newvertexPreppedStep L hL hgn hres haq hm_n hnf_n hnvp_n hep_n⟩
  termination_by n => n
  decreasing_by omega

/-- `elementPre` 沿塔层保持（`elementPreAndNvpIter` 投影）。 -/
theorem elementPreIter (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (hnvp0 : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep0 : Kepler.Text.Reduction3.elementPre L N) :
    ∀ n : ℕ, n < k → Kepler.Text.Reduction3.elementPre L (ntrans L N r x n) :=
  fun n hn => (elementPreAndNvpIter L hL hgn hres haq hm hnf hk hnvp0 hep0 n hn).1

/-- `newvertexPrepped` 沿塔层保持（`elementPreAndNvpIter` 投影）。 -/
theorem newvertexPreppedIter (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (hnvp0 : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep0 : Kepler.Text.Reduction3.elementPre L N) :
    ∀ n : ℕ, n < k →
      Kepler.Text.Reduction3.newvertexPrepped L (ntrans L N r x n) (rtrans L N r x n) x :=
  fun n hn => (elementPreAndNvpIter L hL hgn hres haq hm hnf hk hnvp0 hep0 n hn).2

/-- **HOL `final_assumption_yz_in_core`**（reduction4.hl:727–794）：
条件于强形 `hmisc`（`∀ N' r' i', K1Asm ∧ i' < transform_count ⇒ z0 ∈ rtrans i'`），
证 `∀ i j, 0 < i → i < k → j < k → ytrans j.1 ∈ core (rtrans i) ∧
ztrans j.1 ∈ core (rtrans i)`。

`i ≤ j` 支 = `pnxvwfs1/2` 于状态 i；`j < i` 支 = `propertiesOfYtrans0Spine`
于状态 j（`ytrans`）+ 强形 `hmisc`（`ztrans`）。 -/
theorem finalAssumptionYzInCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hnvp0 : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hep0 : Kepler.Text.Reduction3.elementPre L N)
    (hmisc : ∀ (N' : List (List Dart)) (r' : List Dart) (i' : ℕ),
      i' < transformCount L N' r' x → Kepler.Text.ChainLists.markedList L hL N' r' x →
      Kepler.Text.Reduction3.newvertexPrepped L N' r' x → ¬ finalList L r' →
      Kepler.Text.Reduction3.elementPre L N' →
      ztrans L N' r' x 0 ∈ rtrans L N' r' x i') :
    ∀ i j : ℕ, 0 < i → i < k → j < k →
      (ytrans L N r x j).1 ∈ core L (rtrans L N r x i) ∧
      (ztrans L N r x j).1 ∈ core L (rtrans L N r x i) := by
  intro i j hi hik hjk
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hm_i : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hcoreI : ∀ u ∈ rtrans L N r x i, u.1 ∈ core L (rtrans L N r x i) :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm_i
  have hnf_i : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  -- `i ≤ j` 支：pnxvwfs1/2 于状态 i（指数 `j-i`）
  have hy_le : i ≤ j → ytrans L N r x j ∈ rtrans L N r x i := by
    intro hij
    have hji : j - i + i = j := by omega
    have hnf' : ¬ finalList L (rtrans L (ntrans L N r x i) (rtrans L N r x i) x (j - i)) := by
      rw [← (Kepler.Text.Reduction3.transAdd L N r x i (j - i)).2.1, hji]
      exact Kepler.Text.Reduction4.transformCount_not j (by rw [hk]; omega)
    have h := pnxvwfs1 L hL hgn haq (N := ntrans L N r x i) (r := rtrans L N r x i)
      (x := x) (j - i) hnf' hm_i
    rwa [← (Kepler.Text.Reduction3.transAdd L N r x i (j - i)).2.2.1, hji] at h
  have hz_le : i ≤ j → ztrans L N r x j ∈ rtrans L N r x i := by
    intro hij
    have hji : j - i + i = j := by omega
    have hnf' : ¬ finalList L (rtrans L (ntrans L N r x i) (rtrans L N r x i) x (j - i)) := by
      rw [← (Kepler.Text.Reduction3.transAdd L N r x i (j - i)).2.1, hji]
      exact Kepler.Text.Reduction4.transformCount_not j (by rw [hk]; omega)
    have h := pnxvwfs2 L hL hgn haq (N := ntrans L N r x i) (r := rtrans L N r x i)
      (x := x) (j - i) hnf' hm_i
    rwa [← (Kepler.Text.Reduction3.transAdd L N r x i (j - i)).2.2.2, hji] at h
  -- `j < i` 支：状态 j
  have hrt_i : j < i → rtrans L N r x i
      = rtrans L (ntrans L N r x j) (rtrans L N r x j) x (i - j) := by
    intro hji
    have h := (Kepler.Text.Reduction3.transAdd L N r x j (i - j)).2.1
    rwa [show i - j + j = i from by omega] at h
  have hy_gt : j < i → ytrans L N r x j ∈ rtrans L N r x i := by
    intro hji
    have hm_j : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x j) (rtrans L N r x j) x := haq hgn N r x hm j
    have hnf_j : ¬ finalList L (rtrans L N r x j) :=
      Kepler.Text.Reduction4.transformCount_not j (by rw [hk]; omega)
    have hmS : MarkedListSpineFull hL (ntrans L N r x j) (rtrans L N r x j) x :=
      Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm_j
    have hrtS : rtransSpine L (ntrans L N r x j) (rtrans L N r x j) x (i - j)
        = rtrans L (ntrans L N r x j) (rtrans L N r x j) x (i - j) :=
      (Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm_j (i - j)).symm
    have hfSp : ¬ finalListSpine L
        (rtransSpine L (ntrans L N r x j) (rtrans L N r x j) x (i - j)) := by
      rw [hrtS, ← hrt_i hji]
      exact fun h => hnf_i ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine
        L (rtrans L N r x i)).mpr h)
    have hYsp := Kepler.Text.TameSpine.propertiesOfYtrans0Spine L hL
      (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq) hgn hunL
      hmS (i - j) rfl rfl hfSp
    have hy_eq : ytrans L N r x j = ytrans L (ntrans L N r x j) (rtrans L N r x j) x 0 := by
      have h := (Kepler.Text.Reduction3.transAdd L N r x j 0).2.2.1
      rwa [Nat.zero_add] at h
    have hyS_eq : ytrans L (ntrans L N r x j) (rtrans L N r x j) x 0
        = ytransSpine L (ntrans L N r x j) (rtrans L N r x j) x 0 := by
      show Kepler.Text.Reduction5.ly L (rtrans L (ntrans L N r x j) (rtrans L N r x j) x 0) x
        = lYSpine L (rtransSpine L (ntrans L N r x j) (rtrans L N r x j) x 0) x
      rw [Kepler.Text.Reduction5.rtrans_zero]
      exact Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm_j hnf_j
    rw [hy_eq, hrt_i hji, hyS_eq, ← hrtS]
    exact hYsp.2.2.2
  have hz_gt : j < i → ztrans L N r x j ∈ rtrans L N r x i := by
    intro hji
    have hm_j : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x j) (rtrans L N r x j) x := haq hgn N r x hm j
    have hnf_j : ¬ finalList L (rtrans L N r x j) :=
      Kepler.Text.Reduction4.transformCount_not j (by rw [hk]; omega)
    have hnvp_j := newvertexPreppedIter L hL hgn hres haq hm hnf hk hnvp0 hep0 j hjk
    have hep_j := elementPreIter L hL hgn hres haq hm hnf hk hnvp0 hep0 j hjk
    have hlt : i - j < transformCount L (ntrans L N r x j) (rtrans L N r x j) x := by
      have htc := transformCountAddOfMarked L hL hgn haq hm j (by rw [hk]; omega)
      rw [htc, hk]
      omega
    have hz_sp := hmisc (ntrans L N r x j) (rtrans L N r x j) (i - j)
      hlt hm_j hnvp_j hnf_j hep_j
    have hz_eq : ztrans L N r x j = ztrans L (ntrans L N r x j) (rtrans L N r x j) x 0 := by
      have h := (Kepler.Text.Reduction3.transAdd L N r x j 0).2.2.2
      rwa [Nat.zero_add] at h
    rw [hz_eq, hrt_i hji]
    exact hz_sp
  by_cases hij : i ≤ j
  · exact ⟨hcoreI _ (hy_le hij), hcoreI _ (hz_le hij)⟩
  · have hji : j < i := by omega
    exact ⟨hcoreI _ (hy_gt hji), hcoreI _ (hz_gt hji)⟩

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.elementPreAndNvpIter
#print axioms Kepler.Text.Reduction5.elementPreIter
#print axioms Kepler.Text.Reduction5.newvertexPreppedIter
#print axioms Kepler.Text.Reduction5.finalAssumptionYzInCore
