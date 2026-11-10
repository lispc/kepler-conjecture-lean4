/-
  Kepler.Text.Reduction5J5Red2Pieces — J5-2 续段（chain 载体）：reduction2 章件移植。
  本文件落 `take_iota`（reduction2.hl:297）与 `rtrans_diff_r`（:489）——
  `final_assumption_newvertex_prepped`（reduction4.hl:809）的前置缺件。

  ┌─ 归属对账（HOL Light Flyspeck reduction2.hl）────────────────────
  │ :297 `take_iota`（13L）→ `takeIota`：i <= j ⇒ take i (iota n j) = iota n i
  │   （`iota m (SUC n) = m :: iota (SUC m) n`，`iota m 0 = []` ⇒ 长度 j 的
  │   连续段；Lean `iota n j` ↦ `List.range' n j`，同 Reduction5Base 的
  │   「`upt i j` = `List.range' i (j - i)`」换算：`iota n j` 恰为
  │   `range' n j`，HOL 里未用 `upt` 口径）。
  │ :489 `rtrans_diff_r`（38L）→ `rtransDiffR`：
  │   good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ⇒
  │   filter (λd. ¬ MEM d r) (rtrans L N r x 1) =
  │     betwn (find_face L x) (l'y L r x) (l'z L N r x)
  └────────────────────────────────────────────────────────────────

  ┌─ `rtransDiffR` 证体（与 HOL 证体各步对照）────────────────────────
  │ ① `rtrans1` 展开 + `splitNormalList` 展开 + `next_prev_id`：
  │    rtrans 1 = ([z] ++ (betwn r z y ++ [y])) ++ betwn f y z，其中
  │    y = l'y L r x、z = l'z L N r x、f = find_face L (l'y L r x)
  │    （HOL `rtrans_cat` + `find_face_x_eq_y` 的对应物）。
  │ ② 过滤分三段：`[z]` / `betwn r z y` / `[y]` 的元素都在 r 里
  │    （`mem_z_r` = `lzMemR`、`betwn_mem` = `betwnMem`、`mem_y_r` =
  │    `ytransMemRtrans`），filter 后为空；`betwn f y z` 的元素都不在 r 里
  │    （HOL `Aq1.betwn_not_in_rtrans`（AQ1.hl:358）= 树内 spine
  │    `betwnNotInRtrans`（JcajyduAqSnd:136），经 chain marked + ¬final 的
  │    公开桥（`sListEqSpineOfMarked` + `markedList_iff_markedListSpineFull` +
  │    `lyEqSpine`/`lzEqSpine`）折到链层），filter 后原样。
  │ ③ 拼接：`[] ++ [] ++ [] ++ betwn f y z = betwn f y z`，再用
  │    `find_face_x_eq_y`（`findFaceXEqY`）把 f 换回 `find_face L x`。
  │ 前提集 = HOL 原文（无 TAV2 槽：桥只走 marked 与 ¬final）。
  └────────────────────────────────────────────────────────────────

  ┌─ 语义查重记档 ────────────────────────────────────────────────────
  │ `take_iota` 按名零命中；`rtrans_diff_r` 按名零命中（j52 冻结表已记）。
  │ `betwn_not_in_rtrans` 语义查重命中 spine `betwnNotInRtrans`
  │ （JcajyduAqSnd:136，AQ1.hl:358 的 spine 形），本文件经公开桥消费，
  │ 不重落。`mem_y_r`/`mem_z_r` 的链形 = 本车道 `ytransMemRtrans`（j51 前
  │ 已落）与 `lzMemR`（Reduction5Kbwpbhq）。
  └────────────────────────────────────────────────────────────────

  ┌─ 本波未做的两件（reduction2 四件中的另两件；冻结带表）────────────
  │ `newvertex_alt`（:620）/ `face_diff_r`（:843）：见 DELIVERY_j54 §6，
  │ 依赖面与估行在表中；其中 `face_diff_r` 另需 `betwn_rotate_to_face`
  │ （:527）/ `indexf_rotate_to_indexl`（:241）/ `rotate_to_uniq`（:195）/
  │ `mem_take_index2`（:254）/ `indexl_y_lt_z`（:556）/ `cat_eq`（:91）
  │ 六件按名零命中，属下一波整段。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5BetwnNil
import Kepler.Text.ChainSpineBridge
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqZUnlock

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- **HOL `Reduction2.take_iota`**（reduction2.hl:297）：`take i (iota n j) = iota n i`
（`i ≤ j` 时）。证：对 i 归纳（`iota n j` 按 j 递归，长度 j 的连续段）。 -/
theorem takeIota : ∀ (i j n : ℕ), i ≤ j → (List.range' n j).take i = List.range' n i
  | 0, _, _, _ => rfl
  | i + 1, 0, _, h => by omega
  | i + 1, j + 1, n, h => by
    show n :: (List.range' (n + 1) j).take i = n :: List.range' (n + 1) i
    rw [takeIota i j (n + 1) (by omega)]

/-- 链 marked + ¬final ⇒ spine marked / spine 非 final / all-uniq（私有打包，桥用）。 -/
private theorem spineOfChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (∀ l ∈ L, l.Nodup) ∧ Kepler.Text.TameSpine.MarkedListSpineFull hL N r x ∧
      ¬ Kepler.Text.TameSpine.finalListSpine L r := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  exact ⟨hunL,
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)⟩

/-- 链层 `betwn (find_face L (l'y)) (l'y) (l'z)` 的元素不在 r 上
（HOL `Aq1.betwn_not_in_rtrans` 的链层形，经公开桥消费 spine `betwnNotInRtrans`；
私有支件）。 -/
private theorem betwnNotInRtransChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) {d : Dart}
    (hd : d ∈ between (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (lz L N r x)) :
    d ∉ r := by
  obtain ⟨hunL, hmS, hfS⟩ := spineOfChain L hL hgn hm hnf
  rw [Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf] at hd
  exact Kepler.Text.TameSpine.betwnNotInRtrans L hL hgn hunL hmS hfS hd

/-- **HOL `Reduction2.rtrans_diff_r`**（reduction2.hl:489）：一步后的环在 r 上的
差（滤掉 r 的成员）恰是 `betwn (find_face L x) (l'y) (l'z)`。 -/
theorem rtransDiffR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (rtrans L N r x 1).filter (fun d => d ∉ r) =
      between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 _ hm.2.2.1
  -- 成员件：y、z ∈ r
  have hyr : Kepler.Text.Reduction5.ly L r x ∈ r :=
    Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hnf
  have hzr : lz L N r x ∈ r := by
    obtain ⟨-, hmS, hfS⟩ := spineOfChain L hL hgn hm hnf
    rw [Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf]
    exact Kepler.Text.TameSpine.zMemRtransClean L hL hgn hunL hmS hfS
  -- 结构件：rtrans 1 的两段分解
  have hstruct : rtrans L N r x 1 =
      ([lz L N r x] ++ (between r (lz L N r x) (Kepler.Text.Reduction5.ly L r x) ++
        [Kepler.Text.Reduction5.ly L r x])) ++
      between (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
        (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
    rw [Kepler.Text.Reduction3.rtrans1 L N r x hnf]
    show (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2 = _
    simp only [splitNormalList]
    rw [nextElInstEq r (prevEl r (lz L N r x)), nextPrevId hrnd]
  rw [hstruct, List.filter_append, List.filter_append, List.filter_append]
  -- `[z]` 段
  have h1 : List.filter (fun d => d ∉ r) [lz L N r x] = [] := by
    simp [hzr]
  -- `betwn r z y` 段
  have h2 : List.filter (fun d => d ∉ r)
      (between r (lz L N r x) (Kepler.Text.Reduction5.ly L r x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd hdr
    exact (of_decide_eq_true hdr) (Kepler.Graphs.inbetween_inset hd)
  -- `[y]` 段
  have h3 : List.filter (fun d => d ∉ r) [Kepler.Text.Reduction5.ly L r x] = [] := by
    simp [hyr]
  -- `betwn f y z` 段：元素都不在 r
  have h4 : List.filter (fun d => d ∉ r)
      (between (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
        (Kepler.Text.Reduction5.ly L r x) (lz L N r x)) =
      between (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
        (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (betwnNotInRtransChain L hL hgn hm hnf hd)
  rw [h1, h2, h3, h4, List.nil_append, List.nil_append, List.nil_append,
    Kepler.Text.Reduction5.findFaceXEqY L hL hgn hm hnf]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.takeIota
#print axioms Kepler.Text.Reduction5.rtransDiffR
