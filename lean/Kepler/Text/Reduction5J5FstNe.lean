/-
  Kepler.Text.Reduction5J5FstNe — J5-1 主线收口段（chain 载体）第一文件：
  `fst_yi_ne_fst_zi`（reduction4.hl:5075），经 `QRDYXYJ_list` 路线落无槽形
  （编排者 U1 裁决，台账续845 ②）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ tame_list.hl:10307 `QRDYXYJ_list` 第 5 合取 → `qrdyxyjFstYNeFstZ`：
  │   good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r
  │   ⇒ ¬(FST (l'y L r x) = FST (l'z L N r x))
  │   （树内 `ChainQRDYXYJ.qRDYXYJListChain` 的三个显式载体消解后的形；
  │    前提集 = HOL `QRDYXYJ_list` 原文前提集）
  │ reduction4.hl:5075 `fst_yi_ne_fst_zi`（26L）→ `fstYiNeFstZi`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list L N r x ∧
  │   ¬final_list L r ∧ transform_count L N r x = k ∧ i < k
  │   ⇒ ¬(FST (ytrans L N r x i) = FST (ztrans L N r x i))
  └────────────────────────────────────────────────────────────────

  ┌─ 路线差异记账（U1 裁决条件 (c)）──────────────────────────────────
  │ **HOL 原路线**（:5075 证体）：`trans_add` → `final_assumption_fst_y_neq_fst_z`
  │ （:655，取 k' = k − i）→ 其前提 `transform_count … = k − i` 由
  │ `Reduction3.transform_count_add`（reduction3.hl:515，证体消费终止定理
  │ `final_list_transform_count`）供给；而 :655 自身又经
  │ `final_assumption_y_ne_z`（:435）→ `Diowaas.DIOWAAS`（DIOWAAS.hl，整章 220 行）
  │ → `Pnxvwfs.PNXVWFS1/2`（PNXVWFS.hl，整章 182 行），并另吃
  │ `transform_count_non0`（终止定理支）。
  │ 即：HOL 原路线经 transform_count / DIOWAAS / PNXVWFS。
  │ **Lean 路线**：改走 `QRDYXYJ_list`。`FST (l'y) ≠ FST (l'z)` 是 HOL
  │ `QRDYXYJ_list` 自己的第 5 合取，前提只要 marked_list 与 ¬final_list；
  │ 把它用在状态 (ntrans i, rtrans i) 上——该状态的 marked_list 由 AQIUNPP
  │ （`AqiunppSlot` 槽，树内既定惯例）供给，¬final_list 由
  │ `transform_count_not`（i < k）供给——而 `ytrans … i` / `ztrans … i` 按定义
  │ 就是该状态的 l'y / l'z（HOL `l_expand`，定义级）。
  │ 不经 `transform_count_add` / `transform_count_non0` / DIOWAAS / PNXVWFS。
  │ **陈述**：:5075 原文逐字，前提不增不减（另带 `AqiunppSlot` 槽，同
  │ `betEqNilImpNextYZ` / `ncvibwuTowerI` 口径）。`¬final_list L r` 与
  │ `is_restricted` 两前提证体零消费，按原文前提位保留。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线消费面（U1 裁决条件 (b)：全部在库或同波落库）────────────────
  │ 在库（HEAD tracked，逐名实测）：`ChainQRDYXYJ.qRDYXYJListChain`、
  │ `ChainMarkedTranslate.markedTranslate`（供 is_marked 与 ¬final_loops 两载体）、
  │ `ChainMarkedQ.normalListIsNormalFamily`（供 is_normal_family 载体）、
  │ `TameSpine.sListEqSpineOfMarked`（供 markedTranslate 的 sList 槽）、
  │ `TameSpine.isRestrictedAllUniq`、`Reduction4.transformCount_not`、
  │ `Reduction4Idx.AqiunppSlot`。
  │ 同波落库：`qrdyxyjFstYNeFstZ`（本文件）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.ChainQRDYXYJ
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Subseg9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `QRDYXYJ_list` 第 5 合取**（tame_list.hl:10307）的无载体链层形：
`FST (l'y L r x) ≠ FST (l'z L N r x)`。`qRDYXYJListChain` 的三个显式载体由
chain `marked_list` + `¬final_list` 消解：is_normal_family ←
`normalListIsNormalFamily`；is_marked 与 ¬final_loops ← `markedTranslate`
（其 sList 槽 ← `sListEqSpineOfMarked`）。 -/
theorem qrdyxyjFstYNeFstZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (Kepler.Text.Reduction5.ly L r x).1 ≠ (lz L N r x).1 := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  have hnfam := Kepler.Text.ChainMarkedQ.normalListIsNormalFamily L hL hgn hm.1 hm.2.1
  have htr := Kepler.Text.ChainMarkedTranslate.markedTranslate L hL hgn hunL hm hnf hs
  exact (Kepler.Text.ChainQRDYXYJ.qRDYXYJListChain L hL hgn hunL hm hnf
    (htr.2.2.2.2.2.1 hnfam) htr.2.2.2.2.2.2.1).2.2.2.2

/-- **HOL `fst_yi_ne_fst_zi`**（reduction4.hl:5075）：i < transform_count 时
ytrans i 与 ztrans i 首顶点相异。路线见文件头（`QRDYXYJ_list` 于状态 i）。 -/
theorem fstYiNeFstZi (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k i : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) (hik : i < k) :
    (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 := by
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  have hmI : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    haq hgn N r x hm i
  -- ytrans i / ztrans i 即状态 i 的 l'y / l'z（HOL `l_expand`；定义级）
  exact qrdyxyjFstYNeFstZ L hL hgn hmI hnfi

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.qrdyxyjFstYNeFstZ
#print axioms Kepler.Text.Reduction5.fstYiNeFstZi
