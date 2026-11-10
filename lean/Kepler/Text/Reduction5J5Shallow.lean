/-
  Kepler.Text.Reduction5J5Shallow — J5-2 首段（chain 载体）第二文件：
  K1 浅段族中不吃 PNXVWFS / 主机的六件，连同 `Pbflhet.ztrans_in_suc` 的链层形。
  （浅段族其余四件：:587 / :611 吃 PNXVWFS1 / PNXVWFS2，见 Reduction5J5Pnxvwfs，同为原文形；
   :727 / :809 吃主机 `More_lemma1.core_split_normal_list`，按 D2 维持冻结，本波不做。）

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ PBFLHET.hl:512 `ztrans_in_suc` → `ztransInSuc`：
  │   transform_assumption_v2 L ∧ good_list ∧ good_list_nodes ∧ marked_list L N r x ∧
  │   find_face L x = f ∧ next_el f x = w ∧ ¬final_list L (rtrans L N r x i)
  │   ⇒ MEM (ztrans L N r x i) (rtrans L N r x (SUC i))
  │ reduction4.hl:435 `final_assumption_y_ne_z`（20L）→ `finalAssumptionYNeZ`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list ∧
  │   transform_count L N r x = k ⇒ (∀ i. i < k ⇒ ¬(ytrans … i = ztrans … i))
  │ reduction4.hl:455 `final_assumption_size_find_face`（19L）→ `finalAssumptionSizeFindFace`：
  │   … ∧ newvertex_prepped L N r x ∧ … ⇒ 1 ≤ sizel (find_face L x)
  │ reduction4.hl:544 `final_assumption_zpre_core_k`（43L）→ `finalAssumptionZpreCoreK`：
  │   … ∧ newvertex_prepped ∧ … ⇒ MEM (FST (ztrans … (PRE k))) (core L (rtrans … k))
  │ reduction4.hl:635 `final_assumption_fst_z`（20L）→ `finalAssumptionFstZ`：
  │   … ∧ newvertex_prepped ∧ … ⇒ FST (prev_el r (ztrans … 0)) = FST (ztrans … 0)
  │ reduction4.hl:655 `final_assumption_fst_y_neq_fst_z`（35L）→ `finalAssumptionFstYNeqFstZ`：
  │   （无 newvertex_prepped）⇒ ¬(FST (ytrans … 0) = FST (ztrans … 0))
  │ reduction4.hl:690 `final_assumption_size_core`（37L）→ `finalAssumptionSizeCore`：
  │   … ∧ newvertex_prepped ∧ … ⇒ 1 < sizel (core L r)
  │ 七前提件的顺序照原文：good_list / good_list_nodes / is_restricted /
  │ newvertex_prepped / marked_list / ¬final_list / transform_count = k。
  │ `PRE k` ↦ `k - 1`（同 Reduction5K5.reductionK4Concl）；`sizel` ↦ `List.length`。
  │ `transform_assumption_v2 L` ↦ `AqiunppSlot`（同 Reduction3ChainTower 口径）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线差异记账（三件与 HOL 证体路线不同；陈述均为原文逐字，前提不增）──
  │ **:435 y_ne_z**（D1 已批）：HOL 经 `Diowaas.DIOWAAS`（整章未落）+
  │   `transform_count_not`；Lean 由 `fstYiNeFstZi`（Reduction5J5FstNe，
  │   `QRDYXYJ_list` 路线）一行：首顶点相异 ⇒ dart 相异。
  │ **:655 fst_y_neq_fst_z**（D1 已批）：HOL 经 :435 + `transform_count_non0`
  │   （终止定理支）+ `list_pairs_unique`；Lean 直取 `qrdyxyjFstYNeFstZ` 于状态 0。
  │   `transform_count = k` 前提位证体零消费（k 全称）。
  │ **:544 zpre_core_k**（未单独裁决，按 U1 / F2 同款口径做，请确认）：
  │   HOL 取 `¬(k = 0)`（`final_assumption_mem_uniq` ← `transform_count_non0`）后把
  │   `ztrans_in_suc` 用在平移状态 (ntrans (PRE k), rtrans (PRE k)) 的 i = 0 处，其非 final
  │   前提由 `transform_count_add`（终止定理支）供给。Lean 对 k 分两支：
  │   k = 0 时结论是 FST (ztrans 0) ∈ core L r，由 `mem_ztrans_rtrans_v0`（`lzMemR`）
  │   直接成立；k = m + 1 时把 `ztransInSuc` 用在原状态的 i = m 处，非 final 由
  │   `transform_count_not`（m < k）供给。两支都不经 `transform_count_non0` /
  │   `transform_count_add`。（这两条计数件的原文形本波已在 Reduction5J5Termination 落，
  │   所以按 HOL 原路线写也行；现写法不依赖终止定理，陈述相同。）
  │ 其余三件与 HOL 证体同路线：:455 = `sizel_3_concl`（树内 `t10b_sizel_3_concl`）；
  │ :635 = `FST_EQ_PREV_ZTRANS_v0`；:690 = :655 + `final_assumption_mem_fst_core` +
  │ `ytrans_mem_rtrans_v0` + `mem_ztrans_rtrans_v0` 给出 core L r 的两个相异成员。
  │ `ztransInSuc` 由 `trans_add` + `rtrans1` + `next_prev_id` 展开直证
  │ （spine `ztransInSucSpine` 带 spine TAV2 前提，不经它）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线消费面（全部在库或同波落库）────────────────────────────────
  │ 在库：`fstYiNeFstZi` / `qrdyxyjFstYNeFstZ`（Reduction5J5FstNe）、
  │ `fstEqPrevZtransV0`（Reduction5J5SplitNorm）、`lzMemR`（Reduction5Kbwpbhq）、
  │ `ytransMemRtrans`（MoreLemma2Naming）、`finalAssumptionMemFstCore`
  │ （Reduction4Subseg4）、`t10b_sizel_3_concl`（Reduction3Thm10B）、
  │ `transformCount_not`（Reduction4）、`transAdd` / `rtrans1`（Reduction3Thm1）、
  │ `nextPrevId`（Reduction5BetwnBase）、`nextElInstEq`（Reduction5Kbwpbhq）。
  │ 同波落库：`ztransInSuc`（本文件）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5FstNe
import Kepler.Text.Reduction5J5SplitNorm
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction4Subseg4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList markedList)

/-- **HOL `Pbflhet.ztrans_in_suc`**（PBFLHET.hl:512）：非 final 的状态 i 上，
ztrans i 落在下一步的环 rtrans (SUC i) 上。 -/
theorem ztransInSuc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hnfi : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i ∈ rtrans L N r x (i + 1) := by
  have hmI : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hrnd : (rtrans L N r x i).Nodup :=
    (List.nodup_flatten.mp hmI.2.1.1).1 _ hmI.2.2.1
  have hstep : rtrans L N r x (i + 1)
      = rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1 := by
    rw [Nat.add_comm]
    exact (Kepler.Text.Reduction3.transAdd L N r x i 1).2.1
  rw [hstep, Kepler.Text.Reduction3.rtrans1 L _ _ x hnfi]
  show ztrans L N r x i ∈
    (splitNormalList L (rtrans L N r x i) (findFaceDarts L (ytrans L N r x i))
      (ytrans L N r x i) (prevEl (rtrans L N r x i) (ztrans L N r x i))).2
  simp only [splitNormalList]
  rw [nextElInstEq (rtrans L N r x i) (prevEl (rtrans L N r x i) (ztrans L N r x i)),
    nextPrevId hrnd]
  simp

/-- **HOL `final_assumption_y_ne_z`**（reduction4.hl:435）：i < transform_count 时
ytrans i ≠ ztrans i。 -/
theorem finalAssumptionYNeZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i :=
  fun i hik h => fstYiNeFstZi L hL hgn hres haq k i hm hnf hk hik (by rw [h])

/-- **HOL `final_assumption_size_find_face`**（reduction4.hl:455）：x 所在面非空。 -/
theorem finalAssumptionSizeFindFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    1 ≤ (findFaceDarts L x).length :=
  le_trans (by decide) (Kepler.Text.Reduction3.t10b_sizel_3_concl L hL N r x hres hm)

/-- **HOL `final_assumption_zpre_core_k`**（reduction4.hl:544）：FST (ztrans (PRE k))
落在第 k 步环的 core 里。路线差异见文件头。 -/
theorem finalAssumptionZpreCoreK (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    (ztrans L N r x (k - 1)).1 ∈ core L (rtrans L N r x k) := by
  have hmem : ztrans L N r x (k - 1) ∈ rtrans L N r x k := by
    cases k with
    | zero =>
      -- 结论即 l'z L N r x ∈ r（`mem_ztrans_rtrans_v0`）
      have hunL : ∀ l ∈ L, l.Nodup :=
        Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
      exact lzMemR hL hgn hunL haq hm hnf
    | succ m =>
      have hnfm : ¬ finalList L (rtrans L N r x m) :=
        Kepler.Text.Reduction4.transformCount_not m (by rw [hk]; exact Nat.lt_succ_self m)
      exact ztransInSuc L hL hgn haq m hm rfl rfl hnfm
  exact Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL (haq hgn N r x hm k) _ hmem

/-- **HOL `final_assumption_fst_z`**（reduction4.hl:635）：ztrans 0 在 r 上的前驱与它
同首顶点。 -/
theorem finalAssumptionFstZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1 :=
  fstEqPrevZtransV0 L hL hgn hm hnf rfl rfl

/-- **HOL `final_assumption_fst_y_neq_fst_z`**（reduction4.hl:655）：ytrans 0 与
ztrans 0 首顶点相异。路线差异见文件头。 -/
theorem finalAssumptionFstYNeqFstZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 :=
  qrdyxyjFstYNeFstZ L hL hgn hm hnf

/-- 表中有两个相异成员则长度大于 1（`finalAssumptionSizeCore` 的私有支件；
HOL 经 `card_le_size` + `CARD_TWO_ELEMENTS` + `CARD_SUBSET`）。 -/
private theorem lengthGtOneOfTwoMem {α : Type*} {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : 1 < l.length := by
  match l, ha, hb with
  | [], ha, _ => exact absurd ha List.not_mem_nil
  | [c], ha, hb =>
    exact absurd ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm) hab
  | _ :: _ :: _, _, _ => simp

/-- **HOL `final_assumption_size_core`**（reduction4.hl:690）：core L r 至少两个元素。 -/
theorem finalAssumptionSizeCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    1 < (core L r).length := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hne : (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 :=
    finalAssumptionFstYNeqFstZ L hL hgn hres k hm hnf hk
  -- `ytrans_mem_rtrans_v0` / `mem_ztrans_rtrans_v0`
  have hyr : ytrans L N r x 0 ∈ r :=
    Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hnf
  have hzr : ztrans L N r x 0 ∈ r := lzMemR hL hgn hunL haq hm hnf
  -- `final_assumption_mem_fst_core`
  have hmc := Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  exact lengthGtOneOfTwoMem (hmc _ hyr) (hmc _ hzr) hne

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ztransInSuc
#print axioms Kepler.Text.Reduction5.finalAssumptionYNeZ
#print axioms Kepler.Text.Reduction5.finalAssumptionSizeFindFace
#print axioms Kepler.Text.Reduction5.finalAssumptionZpreCoreK
#print axioms Kepler.Text.Reduction5.finalAssumptionFstZ
#print axioms Kepler.Text.Reduction5.finalAssumptionFstYNeqFstZ
#print axioms Kepler.Text.Reduction5.finalAssumptionSizeCore
