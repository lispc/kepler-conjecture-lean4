/-
  Kepler.Text.Reduction4Subseg8 — W2-b（战役 J2/J1 收口并行批）首 patch：
  reduction4.hl「不吃 AQIUNPP/TAV2 子集」可即时交付件（新文件，零 tracked 改动）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :1747 `marked_list_uniq_core`            → markedListUniqCore
  │ :1586 `scroll_flatten_map`               → scrollFlattenMap
  │   （塔 scroll 件的支撑引理；派单点名段 :1763-:1956 的直接前置，同章顺带）
  │ :1847 `initial_prebatch_explicit_scroll` → initialPrebatchExplicitScroll
  └────────────────────────────────────────────────────────────────

  ┌─ W2-b 逐件抽查结论（本文件头记账；详表见 DELIVERY）──────────────
  │ final_assumption_* 家族 :171-:790 范围（除 F 组已落 :474/:506）全部
  │ 吃 TAV2（Reduction2.transform_assumption_v2_lemma）和/或 AQIUNPP：
  │   mem_uniq:171/y_ne_z:435/fsty_core:587/fstz_core:611 吃 TAV2；
  │   mem_x_core:519/zpre_core_k:544/yz_in_core:727 吃 AQIUNPP（+TAV2）；
  │   fst_y_neq_fst_z:655/size_core:690 经 y_ne_z 传递吃 TAV2；
  │   fst_z:635 吃 Aq1.FST_EQ_PREV_ZTRANS_v0（AQ 章）。
  │   唯一非吃件 size_find_face:455 的上游 sizel_3_concl（reduction3:846）
  │   依赖 isRestrictedSizeFace（TameList56，TameSpine 岛）——import 会污
  │   染 J1 板无 Assembly 闭包，随 TAV2 件一并缓交。
  │ 塔 :1763-:1956 三件：explicit:1763/explicit2:1909 归纳步吃 TAV2 +
  │   prebatch_suc_explicit（reduction3:5064 未落）——缓交；scroll:1847
  │   纯列表等式，本批交付。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与导入纪律 ──────────────────────────────────────────────
  │ `core`/`parts`/`rtrans`/`ytrans`/`ztrans`/`ftrans` ↦ Reduction5Base
  │   （7ad388b5 W0 定义基座，本文件经 Reduction5 带入）；
  │ `marked_list` ↦ `ChainLists.markedList`（ChainListsL2:118，`hL :
  │   GoodList L` 载体前提 = DIFFERS-① 章约定，F 组同形）；
  │ `quotient_list_core` ↦ `MoreLemma2Island1.quotientListCore`（:118）；
  │ `betwn` ↦ `Kepler.Graphs.between`（ListAux:27）；`find_face` ↦
  │   `Assembly.findFaceDarts`；`nseq` ↦ `List.replicate`（DIFFERS-②，
  │   无既有 nseq 载体）；`iota i k` ↦ `List.range' i k`；`SOME` ↦
  │   `some`；`rcons l z` ↦ `l ++ [z]`；`cat` ↦ `++`。
  │ 环安全：imports（Reduction5/ChainListsL2/MoreLemma2Island1）全部
  │   Text 层，零 TameSpine、零 Assembly 主模块（Subseg4-7 同款闭包）。
  │ 零 axiom/sorry/admit/native_decide；泛型/具体载体：`Dart = ℕ × ℕ`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList findFaceDarts)
open Kepler.Text.Reduction5 (Dart parts core quotientList ftrans ytrans ztrans
  ftrans_zero)
open Kepler.Text.ChainLists (markedList)
open Kepler.Text.MoreLemma2Island1 (quotientListCore)

/-! ## §0 `range'` 尾接形（Batteries 无 append 引理；iota_add 同型自证件） -/

/-- `iota i (k+1) = iota i k ++ [i+k]`（`Seq.iota_add` 同型；
`List.range' i (k+1)` 的尾接形，`scroll_flatten_map` 归纳底座）。 -/
theorem range'SuccAppend (i k : ℕ) :
    List.range' i (k + 1) = List.range' i k ++ [i + k] := by
  induction k generalizing i with
  | zero => simp [List.range'_succ, List.range'_zero]
  | succ k ih =>
    have htail : i + (k + 1) = i + k + 1 := by omega
    have htail2 : i + 1 + k = i + k + 1 := by omega
    rw [List.range'_succ, ih (i + 1), List.range'_succ, htail, htail2,
      List.cons_append]

/-! ## §1 `scroll_flatten_map`（:1586；纯 nat/list 层，塔 scroll 件支撑）

HOL：`!k i u a. (a i) :: flatten (MAP (λj. rcons (u j) (a (SUC j))) (iota i k))
  = rcons (flatten (MAP (λj. (a j) :: (u j)) (iota i k))) (a (i+k))`。
折算：`iota i k` ↦ `List.range' i k`、`rcons` ↦ `++ [·]`、`MAP` ↦ `List.map`、
`flatten` ↦ `List.flatten`。 -/

theorem scrollFlattenMap {α : Type*} (k : ℕ) : ∀ (i : ℕ) (u : ℕ → List α)
    (a : ℕ → α),
    a i :: ((List.range' i k).map (fun j => u j ++ [a (j + 1)])).flatten
      = ((List.range' i k).map (fun j => a j :: u j)).flatten ++ [a (i + k)] := by
  induction k with
  | zero =>
    intro i _ _
    simp [List.range'_zero]
  | succ k ih =>
    intro i u a
    have htail : i + (k + 1) = i + k + 1 := by omega
    have h1 : List.range' i (k + 1) = List.range' i k ++ [i + k] :=
      range'SuccAppend i k
    rw [h1, List.map_append, List.flatten_append, List.map_append,
      List.flatten_append, List.map_singleton, List.flatten_singleton,
      List.map_singleton, List.flatten_singleton, htail, ← List.cons_append,
      ih i u a]
    simp [List.append_assoc, List.cons_append]

/-! ## §2 `marked_list_uniq_core`（:1747）

HOL：`!L N r x. marked_list L N r x ==> uniq (core L r)`。证明 = marked_list
第 5a 槽（`∀ s ∈ quotient_list L N, uniq s`）+ `quotient_list_core`
（quotient_list = MAP (core L) N）+ `MEMf_MAP`（`r ∈ N` 槽供成员）。
DIFFERS-①：`markedList L hL N r x` 带 `hL : GoodList L` 载体前提（章约定）。 -/

theorem markedListUniqCore (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (h : markedList L hL N r x) :
    (core L r).Nodup := by
  have hrN : r ∈ N := h.2.2.1
  have h5 : ∀ s ∈ quotientList L N, s.Nodup := h.2.2.2.2.1.1
  rw [quotientListCore] at h5
  exact h5 (core L r) (List.mem_map.mpr ⟨r, hrN, rfl⟩)

/-! ## §3 `initial_prebatch_explicit_scroll`（:1847；塔三件之一，纯列表等式）

HOL 原句（:1847-:1877，`(A#A option) list` 层逐字折算）：LHS =
`SOME (SND x) :: flatten (MAP (λj. cat branch_j (cat (nseq len_j NONE)
[SOME (ftrans (SUC j))])) (iota 0 (SUC i)))`，RHS =
`rcons (flatten (MAP (λj. SOME (ftrans j) :: cat branch_j (nseq len_j NONE)))
(iota 0 (SUC i))) (SOME (ftrans (SUC i)))`，其中
`branch_j = if ftrans j = FST (ytrans j) then [] else
cat (MAP SOME (betwn (core L r) (ftrans j) (FST (ytrans j))))
[SOME (FST (ytrans j))]`、`len_j = sizel (betwn (find_face L x) (ytrans j)
(ztrans j))`。
证明 = `scroll_flatten_map` 在 `k := SUC i, i := 0` 的实例 + `ftrans 0 = SND x`
（Reduction5.ftrans_zero）+ `0 + (SUC i)` 归零。零几何前提（HOL 同为
无前提列表等式）。 -/

theorem initialPrebatchExplicitScroll (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (i : ℕ) :
    some x.2 :: ((List.range' 0 (i + 1)).map (fun j =>
        (if ftrans L N r x j = (ytrans L N r x j).1 then [] else
            (between (core L r) (ftrans L N r x j) (ytrans L N r x j).1).map some
              ++ [some (ytrans L N r x j).1])
          ++ (List.replicate
              (between (findFaceDarts L x) (ytrans L N r x j)
                (ztrans L N r x j)).length none
            ++ [some (ftrans L N r x (j + 1))]))).flatten
      = ((List.range' 0 (i + 1)).map (fun j =>
          some (ftrans L N r x j) ::
            ((if ftrans L N r x j = (ytrans L N r x j).1 then [] else
                (between (core L r) (ftrans L N r x j) (ytrans L N r x j).1).map
                  some
                  ++ [some (ytrans L N r x j).1])
              ++ List.replicate
                  (between (findFaceDarts L x) (ytrans L N r x j)
                    (ztrans L N r x j)).length none))).flatten
        ++ [some (ftrans L N r x (i + 1))] := by
  have hs := scrollFlattenMap (i + 1) 0
    (fun j =>
      (if ftrans L N r x j = (ytrans L N r x j).1 then [] else
          (between (core L r) (ftrans L N r x j) (ytrans L N r x j).1).map some
            ++ [some (ytrans L N r x j).1])
        ++ List.replicate
            (between (findFaceDarts L x) (ytrans L N r x j)
              (ztrans L N r x j)).length none)
    (fun j => some (ftrans L N r x j))
  simpa only [Nat.zero_add, ftrans_zero, ← List.append_assoc] using
    scrollFlattenMap (i + 1) 0
      (fun j =>
        (if ftrans L N r x j = (ytrans L N r x j).1 then [] else
            (between (core L r) (ftrans L N r x j) (ytrans L N r x j).1).map some
              ++ [some (ytrans L N r x j).1])
          ++ List.replicate
              (between (findFaceDarts L x) (ytrans L N r x j)
                (ztrans L N r x j)).length none)
      (fun j => some (ftrans L N r x j))

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期 = 标准三或其子集，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.scrollFlattenMap
#print axioms Kepler.Text.Reduction4Idx.markedListUniqCore
#print axioms Kepler.Text.Reduction4Idx.initialPrebatchExplicitScroll
