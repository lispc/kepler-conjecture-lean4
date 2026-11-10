/-
  Kepler.Text.PwssratTail — 铺装 patch6：Ncvibwu 尾件（链层载体）
  + OHCGKFU 面（见文件尾 §3 状态）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ NCVIBWU.hl:302 `next_mark_mem_r_trans`   → nextMarkMemRTrans
  │ NCVIBWU.hl:204 `indexf_ytrans_eq_l_m1`   → indexfYtransEqLM1
  │   （当前 loop 形 = AQ7.hl:39 `indexf_ytrans_eq_l_m1_v0`
  │    → indexfYtransEqLM1Core）
  │ NCVIBWU.hl:333 `next_mark_case_mem`      → 见 §3 状态（BLOCKED）
  │ OHCGKFU.hl:162 `OHCGKFU`                 → 见 §3 状态（UNRESOLVED）
  │ tame_list.hl:1601 `indexf_antisym`       → 已在库 `Reduction5.indexfCompl`
  │ tame_list.hl:1876 `indexf_n`             → 已在库 `MoreLemma2Island1.indexfN`
  └────────────────────────────────────────────────────────────────

  ┌─ 载体（链层）────────────────────────────────────────────────
  │ `marked_list` ↦ ChainLists.markedList；`find_face` ↦ findFaceDarts；
  │ `next_el` ↦ nextEl；`l'm`/`l'y` ↦ Reduction5.lm/ly；
  │ `rtrans`/`ytrans`/`ntrans` ↦ Reduction5 同名（定义即投影，Reduction5Base）。
  │ `transform_assumption_v2 L` 按 patch4/patch5 同一口径折算为
  │ `AqiunppSlot L hL`（全 i 的变换保持；HOL 证体同用 AQIUNPP3）。
  │ `indexf` = `Kepler.Text.Reduction5.indexf`（链唯一载体；Reduction4 §F
  │ 簇同口径）。
  │ 实例纪律：`Dart = ℕ × ℕ` 的 `nextEl`/`idxOf` 走 `instBEqProd` 世界
  │ （`lm`/`finalList`/`lyNextElPow` 同世界）；Spine 侧 BEq 世界引理经
  │ `Reduction3.indexf_eq_spine`（双常量桥，propext）折回 —— 不复制
  │ Spine 引擎（patch4 实例分歧教训同款）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；零直接 TameSpine import；
  不改既有陈述；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction3Thm6B
import Kepler.Text.PwssratMemberBase
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart lm lz ztrans ytrans ntrans rtrans finalList
  indexf)

/-! ## §1 `next_mark_mem_r_trans`（NCVIBWU.hl:302-:331）

HOL 证体直接展开 `transform_list`；链层载体下 `w = f_list L x =
next_el (rtrans …) x`（变换后 markedList 第 6 槽），轨道成员性一键收口。 -/

/-- **HOL `Ncvibwu.next_mark_mem_r_trans`**（NCVIBWU.hl:302）：
`find_face L x = f`、`next_el f x = w` ⇒ `w ∈ rtrans L N r x i`。 -/
theorem nextMarkMemRTrans (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {f : List Dart} {w : Dart}
    (hfind : findFaceDarts L x = f) (hnext : nextEl f x = w) :
    w ∈ rtrans L N r x i := by
  have hm' := haq hgn N r x hm i
  have hxr : x ∈ rtrans L N r x i := hm'.2.2.2.1
  have h6 : nextEl (rtrans L N r x i) x = fList L x := hm'.2.2.2.2.2.1
  have hw : fList L x = w := by
    show nextEl (findFaceDarts L x) x = w
    rw [hfind]
    exact hnext
  rw [hw] at h6
  rw [← h6]
  exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr

/-! ## §2 `indexf_ytrans_eq_l_m1`（NCVIBWU.hl:204-:296 / AQ7.hl:39 v0）

`indexf w (l'y) r = l'm`：`w = next_el r x = f_list x`，而
`l'y = (f_list)^(l'm+1) x = (next_el r)^(l'm+1) x`（`min_not_eq_imp_eq`），
故 `w` 走 `l'm` 步到 `l'y`，`next_eln_indexf` 收口。界 `l'm < r.length`
由「反例元素 z 的 indexf 定位步 k = indexf x z r < length，偏差在 k-1」证。 -/

/-- `lm` 严格小于表长：`¬final_list L r` + `next_el r x = f_list L x` +
`x ∈ r` + `r.Nodup`。反证：偏差元素 `z` 的定位步 `k = indexf x z r`
（`indexfN`，`k < r.length`）的**前一步**即离开 `f_list`，故 `lm ≤ k-1`。 -/
theorem lmLtLength (L : fgraph ℕ) {r : List Dart} {x : Dart}
    (hx : x ∈ r) (hr : r.Nodup) (hnext : nextEl r x = fList L x)
    (hf : ¬ finalList L r) :
    lm L r x < r.length := by
  simp only [finalList] at hf
  push Not at hf
  obtain ⟨z, hzr, hz⟩ := hf
  have hk : (nextEl r)^[Kepler.Text.TameSpine.indexf x z r] x = z :=
    Kepler.Text.TameSpine.indexfN hx hzr hr
  rw [← Kepler.Text.Reduction3.indexf_eq_spine x z r] at hk
  have hklt : indexf x z r < r.length :=
    Kepler.Text.Reduction4.indexf_lt_length_of_mem hx hzr
  rcases Nat.eq_zero_or_pos (indexf x z r) with h0 | hpos
  · rw [h0] at hk
    simp only [Function.iterate_zero_apply] at hk
    exact (hz (by rw [← hk]; exact hnext.symm)).elim
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
    have hzj : (nextEl r)^[j + 1] x = z := by
      rw [← hk, hj]
    have hmemS : j ∈ {m : ℕ | (nextEl r)^[m + 2] x
        ≠ fList L ((nextEl r)^[m + 1] x)} := by
      simp only [Set.mem_setOf_eq]
      have h1 : (nextEl r)^[j + 2] x = nextEl r z := by
        rw [show j + 2 = (j + 1) + 1 from rfl, Function.iterate_succ_apply', hzj]
      rw [h1, hzj]
      exact Ne.symm hz
    have hle : lm L r x ≤ j :=
      (Kepler.Text.Reduction5.minNum_spec ⟨j, hmemS⟩).2 j hmemS
    omega

/-- **HOL `Aq7.indexf_ytrans_eq_l_m1_v0`**（AQ7.hl:39）当前 loop 形：
`marked_list ∧ ¬final_list ⇒ indexf (next_el (find_face x) x) (l'y) r = l'm`。
patch8 可见性上调（private → public，陈述/证体逐字未动）：`PwssratCase` 的
`indexfConstLe`/`nextMarkCaseMem` 无 haq 形消费（与 Spine `aq10_indexfYtransEqLm1`
公开件同口径）；`lmLtLength` 同款上调（NCVIBWU/Aq7 共同界件）。 -/
theorem indexfYtransEqLM1Core (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    indexf (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x) r
      = lm L r x := by
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hw : nextEl (findFaceDarts L x) x ∈ r := by
    show fList L x ∈ r
    rw [← hnext]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hy : Kepler.Text.Reduction5.ly L r x ∈ r := by
    rw [lyNextElPow L hnext.symm]
    have key : ∀ m : ℕ, (nextEl r)^[m] x ∈ r := by
      intro m
      induction m with
      | zero => simpa using hxr
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
    exact key _
  have hwEq : nextEl (findFaceDarts L x) x = nextEl r x := hnext.symm
  have hyW : Kepler.Text.Reduction5.ly L r x
      = (nextEl r)^[lm L r x] (nextEl (findFaceDarts L x) x) := by
    rw [lyNextElPow L hnext.symm, Function.iterate_succ_apply, ← hwEq]
  have h := Kepler.Text.TameSpine.nextElnIndexf hw hy hrnd hyW.symm
    (lmLtLength L hxr hrnd hnext hf)
  rw [← Kepler.Text.Reduction3.indexf_eq_spine
    (nextEl (findFaceDarts L x) x) (Kepler.Text.Reduction5.ly L r x) r] at h
  exact h

/-- **HOL `Ncvibwu.indexf_ytrans_eq_l_m1`**（NCVIBWU.hl:204）链层形：
`~final_list (rtrans …) ∧ next_el (rtrans …) x = w`
⇒ `indexf w (ytrans …) (rtrans …) = l'm (rtrans …) x`。 -/
theorem indexfYtransEqLM1 (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L (rtrans L N r x i))
    {w : Dart} (hw : nextEl (rtrans L N r x i) x = w) :
    indexf w (ytrans L N r x i) (rtrans L N r x i)
      = lm L (rtrans L N r x i) x := by
  have hm' := haq hgn N r x hm i
  have h6 : nextEl (rtrans L N r x i) x = fList L x := hm'.2.2.2.2.2.1
  have hw' : nextEl (findFaceDarts L x) x = w := by
    show fList L x = w
    rw [← h6]
    exact hw
  have hcore := indexfYtransEqLM1Core L hL hm' hf
  rw [hw'] at hcore
  exact hcore

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.nextMarkMemRTrans
#print axioms Kepler.Text.Reduction4Idx.indexfYtransEqLM1
