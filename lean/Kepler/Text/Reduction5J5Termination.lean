/-
  Kepler.Text.Reduction5J5Termination — J5-2 首段（chain 载体）：变换塔终止性的链层形
  （`KBWPBHQ0` / `final_list_transform_count`）、由它得到的 `transform_count_non0` /
  `transform_count_add` 无条件形，以及 `final_assumption_mem_uniq`（reduction4.hl:171）
  的 HOL 原文形。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ KBWPBHQ.hl:57 `KBWPBHQ0` → `kbwpbhq0`：
  │   transform_assumption_v2 L ∧ good_list ∧ good_list_nodes ∧ marked_list L N r x
  │   ⇒ ∃ i. final_list L (rtrans L N r x i)
  │ KBWPBHQ.hl:352 `final_list_transform_count` → `finalListTransformCount`：
  │   同前件 ∧ transform_count L N r x = t ⇒ final_list L (rtrans L N r x t)
  │ reduction3.hl:796 `transform_count_non0` → `transformCountNon0OfMarked`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list L r ⇒ ¬(transform_count L N r x = 0)
  │ reduction3.hl:515 `transform_count_add` → `transformCountAddOfMarked`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ a ≤ transform_count L N r x ⇒
  │   transform_count L (ntrans L N r x a) (rtrans L N r x a) x = transform_count L N r x − a
  │ reduction4.hl:171 `final_assumption_mem_uniq`（82L）→ `finalAssumptionMemUniq`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list ∧
  │   transform_count L N r x = k ⇒ 11 合取（顺序照原文，见定理陈述）
  │ `transform_assumption_v2 L` ↦ `AqiunppSlot`（同 Reduction3ChainTower 口径）；后三件的
  │ HOL 陈述里没有 TAV2 前提，HOL 证体用 `transform_assumption_v2_lemma` 当场消掉，
  │ Lean 侧同样以 `AqiunppSlot` 承载。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线：与 HOL 同路线（终止定理），不是绕行 ──────────────────────
  │ HOL：`transform_count_non0` / `transform_count_add` ← `final_list_transform_count`
  │ ← `KBWPBHQ0`。Lean 逐层同构：
  │ · `kbwpbhq0`：r 已 final 取 i = 0；否则 = spine `kbwpbhq0Spine`
  │   （TameSpine/Reduction3KbwpbhqNtrans2，在库）+ 桥（`hta` ←
  │   `transformAssumptionSpineOfAqiunpp`；marked ← `markedList_iff_markedListSpineFull`；
  │   `rtransEqSpine` + `finalList_iff_finalListSpine` 折回链层）。
  │ · `finalListTransformCount`：上件供非空 + `minNum_spec` 的成员性（HOL `MIN_LEAST`）。
  │ · 两条计数件：树内条件槽形 `Reduction3.transformCountNon0` / `transformCountAdd`
  │   （Reduction3Thm2:97 / :106）的 `hfinal` 槽由上件填上。条件槽形原件未动。
  │ · `finalAssumptionMemUniq`：与 HOL 证体逐合取同构——第 5、6 合取 = PNXVWFS2 / 1
  │   （Reduction5J5Pnxvwfs）+ `transform_count_not`；第 11 合取 = `transform_count_non0`；
  │   其余 = `marked_list_of_dart` / `dart_in_face` / `mem_next_el` / marked_list 第 6 合取 /
  │   `ytran_me_f` / `ztran_me_f`（`lzMemFindFaceDarts` 于状态 i）/ `marked_list_uniq_core`
  │   于状态 i / `uniq_find_face`。
  └────────────────────────────────────────────────────────────────

  ┌─ 对台账的勘误（机器证据；请编排者复核后改账）─────────────────────
  │ 台账（续837 ②，`docs/priority-queue.md` 的 hnon0 冻结判词）记：`hnon0` 无条件形冻结，
  │ 两条路线均带真闸——链侧终止定理，或 spine TAV2 全量供给。实测：
  │ ① spine 终止定理 `kbwpbhq0Spine` 在库，只吃 `hta`；
  │ ② spine TAV2 的无条件形 `transformAssumptionSpine_top` 在库且公理面为标准三
  │   （JcajyduAqTowerTop，`e49d8c55` 落库，早于该冻结判词）；
  │ ③ 链侧单槽 `AqiunppSlot` 可供出 `hta`（Reduction5J5Tav2Bridge，本波）。
  │ 故链侧终止定理可得，`transform_count_non0` 的原文形即本文件
  │ `transformCountNon0OfMarked`，只带链件惯例的 `AqiunppSlot`。
  │ 九槽顶层的 `hnon0` 槽与 F2 之前绕开的 `transform_count_non0` 消费点随之有了供料。
  └────────────────────────────────────────────────────────────────

  命名：两条计数件的原文名在 `Kepler.Text.Reduction3` 里已被条件槽形占用，本文件用
  `…OfMarked` 后缀区分（陈述是 HOL 原文形）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction3Thm2
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.PwssratFace
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `KBWPBHQ0`**（KBWPBHQ.hl:57）：变换塔必达终态。 -/
theorem kbwpbhq0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) :
    ∃ i : ℕ, finalList L (rtrans L N r x i) := by
  by_cases hf : finalList L r
  · exact ⟨0, hf⟩
  · have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
    have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf
    have hmS := (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
    obtain ⟨i, hi⟩ := Kepler.Text.TameSpine.kbwpbhq0Spine L hL
      (transformAssumptionSpineOfAqiunpp L hL haq) hgn hmS
    refine ⟨i, ?_⟩
    rw [Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]
    exact (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr hi

/-- **HOL `final_list_transform_count`**（KBWPBHQ.hl:352）：第 transform_count 步是 final。 -/
theorem finalListTransformCount (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) {t : ℕ} (ht : transformCount L N r x = t) :
    finalList L (rtrans L N r x t) := by
  obtain ⟨i, hi⟩ := kbwpbhq0 L hL hgn haq hm
  have hmem : minNum {j : ℕ | finalList L (rtrans L N r x j)} ∈
      {j : ℕ | finalList L (rtrans L N r x j)} := (minNum_spec ⟨i, hi⟩).1
  rw [← ht]
  exact hmem

/-- **HOL `transform_count_non0`**（reduction3.hl:796）原文形：非 final 时计数非零。 -/
theorem transformCountNon0OfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    transformCount L N r x ≠ 0 :=
  Kepler.Text.Reduction3.transformCountNon0 L N r x
    (finalListTransformCount L hL hgn haq hm rfl) hnf

/-- **HOL `transform_count_add`**（reduction3.hl:515）原文形：走 a 步后的计数。 -/
theorem transformCountAddOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (a : ℕ) (ha : a ≤ transformCount L N r x) :
    transformCount L (ntrans L N r x a) (rtrans L N r x a) x = transformCount L N r x - a :=
  Kepler.Text.Reduction3.transformCountAdd L N r x a
    (finalListTransformCount L hL hgn haq hm rfl) ha

/-- **HOL `final_assumption_mem_uniq`**（reduction4.hl:171）：11 合取，顺序照原文。 -/
theorem finalAssumptionMemUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    x ∈ listOfDarts L ∧
    x ∈ findFaceDarts L x ∧
    nextEl (findFaceDarts L x) x ∈ findFaceDarts L x ∧
    nextEl (findFaceDarts L x) x ∈ r ∧
    (∀ i, i < k → ztrans L N r x i ∈ r) ∧
    (∀ i, i < k → ytrans L N r x i ∈ r) ∧
    (∀ i, i < k → ytrans L N r x i ∈ findFaceDarts L x) ∧
    (∀ i, i < k → ztrans L N r x i ∈ findFaceDarts L x) ∧
    (∀ i, i ≤ k → (core L (rtrans L N r x i)).Nodup) ∧
    (findFaceDarts L x).Nodup ∧
    k ≠ 0 := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxf : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hnotf : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hik =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  refine ⟨hx, hxf, Kepler.Text.TameLp.nextEl_mem_of_mem hxf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 第 4 合取：next_el (find_face L x) x = f_list L x = next_el r x ∈ r
    have h1 : nextEl (findFaceDarts L x) x = nextEl r x := hm.2.2.2.2.2.1.symm
    rw [h1]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hm.2.2.2.1
  · exact fun i hik => pnxvwfs2 L hL hgn haq i (hnotf i hik) hm
  · exact fun i hik => pnxvwfs1 L hL hgn haq i (hnotf i hik) hm
  · exact fun i _ => Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl i
  · exact fun i _ => Kepler.Text.Reduction4Idx.lzMemFindFaceDarts L hL (haq hgn N r x hm i)
  · exact fun i _ => Kepler.Text.Reduction4Idx.markedListUniqCore L hL (haq hgn N r x hm i)
  · exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  · rw [← hk]
    exact transformCountNon0OfMarked L hL hgn haq hm hnf

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.kbwpbhq0
#print axioms Kepler.Text.Reduction5.finalListTransformCount
#print axioms Kepler.Text.Reduction5.transformCountNon0OfMarked
#print axioms Kepler.Text.Reduction5.transformCountAddOfMarked
#print axioms Kepler.Text.Reduction5.finalAssumptionMemUniq
