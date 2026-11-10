/-
  Kepler.Text.Reduction5J5SplitNorm — J5-1 余量段（chain 载体）第二文件：
  AQ1 三件的链层形（`uniq_fst_split_norm` AQ1.hl:1373、`FST_EQ_NEXT_YTRANS_v0`
  :851、`FST_EQ_PREV_ZTRANS_v0` :796）与 `bet_eq_nil_imp_next_z_y`
  （reduction4.hl:4970）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ AQ1.hl:1373 `uniq_fst_split_norm` → `uniqFstSplitNorm`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list ⇒
  │   uniq (FST (split_normal_list L r (find_face L (l'y L r x)) (l'y L r x)
  │               (prev_el r (l'z L N r x))))
  │ AQ1.hl:851 `FST_EQ_NEXT_YTRANS_v0` → `fstEqNextYtransV0`：
  │   同前件 ∧ l'y L r x = y ⇒ FST (next_el r y) = FST y
  │ AQ1.hl:796 `FST_EQ_PREV_ZTRANS_v0` → `fstEqPrevZtransV0`：
  │   同前件 ∧ l'z L N r x = z ∧ prev_el r z = z1 ⇒ FST z1 = FST z
  │ reduction4.hl:4970 `bet_eq_nil_imp_next_z_y`（65L）→ `betEqNilImpNextZY`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list ∧
  │   FST (split_normal_list L r (find_face L x) (ytrans … 0)
  │        (prev_el r (ztrans … 0))) = f1 ∧
  │   betwn (find_face L x) (ytrans … 0) (ztrans … 0) = []
  │   ⇒ next_el f1 (prev_el r (ztrans … 0)) = next_el r (ytrans … 0)
  └────────────────────────────────────────────────────────────────

  ┌─ 对表查重结论（工单要求；对交接包的勘误）─────────────────────────
  │ `uniq_fst_split_norm` 的内容**已在 spine 落库**：
  │ `TameSpine.aq1_split1Nodup`（JcajyduAqLeaf1，头注自述「HOL
  │ `uniq_fst_split_norm` 的 Lean 形」）。JcajyduAqSplit1B 文件头的未了清单
  │ （uniqFstSplitNorm 及前置三件）写于该件落库之前，已过期。故 AQ1.hl:1135–
  │ :1475 那条链**无需移植**：链层形 = spine 件 + 公开桥
  │ （`markedList_iff_markedListSpineFull` / `sListEqSpineOfMarked` /
  │ `splitNormalListEqSpine` / `lyEqSpine` / `lzEqSpine`）。两条 FST 件同理
  │ （spine `fstEqNextYtransV0` / `fstEqPrevZtransV0`，JcajyduAqLeaf8W05）。
  │ 公开陈述零 spine 谓词（结论与前提只用链层名），spine 只出现在证体内——
  │ 与 ChainMarkedTranslate / Reduction3ChainTower 同款路线。
  └────────────────────────────────────────────────────────────────

  ┌─ `bet_eq_nil_imp_next_z_y` 证体（与 HOL :4987-:5033 逐步对照）────
  │ split 展开后 FST = rev new1 ++ ([ram1'] ++ (betwn r ram1' ram2 ++ [ram2]))，
  │ ram1' = next_el r y、ram2 = prev_el r z；`next_prev_id` 把 ram2' 折回 z，
  │ betwn 空前提消掉 new2 ⇒ new1 = [] ⇒ f1 = [next_el r y] ++ (… ++ [prev_el r z])；
  │ HD f1 = next_el r y、LAST f1 = prev_el r z；uniq f1 由 `uniqFstSplitNorm`
  │ （经 `findFaceXEqY` 换面）；`next_el_last_hd` 收口。
  │ HOL 证体开头引的 AQIUNPP（状态 1 的 marked_list）在后文零消费，
  │ 故本件**不带** AqiunppSlot 槽（前提集 = HOL 原文前提集）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5BetwnNil
import Kepler.Text.ChainSpineBridge
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.JcajyduAqLeaf1
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList markedList)

/-- chain `markedList` + `¬final_list` ⇒ `all uniq L` 与 spine 全量 marked /
非 final（桥件打包；私有）。 -/
private theorem spineFullOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (∀ l ∈ L, l.Nodup) ∧ Kepler.Text.TameSpine.MarkedListSpineFull hL N r x ∧
      ¬ Kepler.Text.TameSpine.finalListSpine L r := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  exact ⟨hunL,
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)⟩

/-- **HOL `uniq_fst_split_norm`**（AQ1.hl:1373）：split 的 FST 片 uniq。 -/
theorem uniqFstSplitNorm (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1.Nodup := by
  obtain ⟨hunL, hmS, hfS⟩ := spineFullOfMarked L hL hgn hm hnf
  have h := Kepler.Text.TameSpine.aq1_split1Nodup L hL hgn hunL hmS hfS
  rw [Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf]
  exact h

/-- **HOL `FST_EQ_NEXT_YTRANS_v0`**（AQ1.hl:851）：y = l'y 在 r 上的后继与 y
同首顶点。 -/
theorem fstEqNextYtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {y : Dart} (hy : Kepler.Text.Reduction5.ly L r x = y) :
    (nextEl r y).1 = y.1 := by
  obtain ⟨hunL, hmS, hfS⟩ := spineFullOfMarked L hL hgn hm hnf
  have h := Kepler.Text.TameSpine.fstEqNextYtransV0 L hL hgn hmS hfS
  rw [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf, hy] at h
  exact h

/-- **HOL `FST_EQ_PREV_ZTRANS_v0`**（AQ1.hl:796）：z = l'z 在 r 上的前驱与 z
同首顶点。 -/
theorem fstEqPrevZtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {z z1 : Dart} (hz : lz L N r x = z) (hz1 : prevEl r z = z1) :
    z1.1 = z.1 := by
  obtain ⟨hunL, hmS, hfS⟩ := spineFullOfMarked L hL hgn hm hnf
  have h := Kepler.Text.TameSpine.fstEqPrevZtransV0 L hL hgn hmS hfS
  rw [← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf, hz, hz1] at h
  exact h

/-- **HOL `bet_eq_nil_imp_next_z_y`**（reduction4.hl:4970）：同面 betwn 空时，
split 的 FST 片 f1 上 `prev_el r z` 的后继即 `next_el r y`。 -/
theorem betEqNilImpNextZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (f1 : List Dart)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hf1 : (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
      (prevEl r (ztrans L N r x 0))).1 = f1)
    (hbet : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = []) :
    nextEl f1 (prevEl r (ztrans L N r x 0)) = nextEl r (ytrans L N r x 0) := by
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 _ hm.2.2.1
  -- ytrans 0 / ztrans 0 的 l'y / l'z 形（HOL `Reduction2.trans0`；定义级）
  have hf1' : (splitNormalList L r (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
      (prevEl r (lz L N r x))).1 = f1 := hf1
  have hbet' : between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
      (lz L N r x) = [] := hbet
  -- uniq f1（`uniq_fst_split_norm`，经 `find_face_x_eq_y` 换面）
  have hu : f1.Nodup := by
    have h := uniqFstSplitNorm L hL hgn hm hnf
    rw [findFaceXEqY L hL hgn hm hnf, hf1'] at h
    exact h
  -- f1 的显式结构
  have hstruct : f1 = [nextEl r (Kepler.Text.Reduction5.ly L r x)] ++
      (between r (nextEl r (Kepler.Text.Reduction5.ly L r x)) (prevEl r (lz L N r x)) ++
        [prevEl r (lz L N r x)]) := by
    rw [← hf1']
    simp only [splitNormalList]
    rw [nextElInstEq r (prevEl r (lz L N r x)), nextPrevId hrnd, hbet']
    simp only [List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append]
  have hne : f1 ≠ [] := by
    rw [hstruct]
    simp
  have key : ∀ (s : List Dart) (hs : s ≠ []) (a b : Dart) (X : List Dart),
      s = [a] ++ (X ++ [b]) → s.getLast hs = b ∧ s.headD a = a := by
    intro s hs a b X hsx
    subst hsx
    simp
  obtain ⟨hlast, hhd⟩ := key _ hne _ _ _ hstruct
  have h := Kepler.Text.MoreLemma2Naming.nextElLastHd
    (x := nextEl r (Kepler.Text.Reduction5.ly L r x)) hu hne
  rw [hlast, hhd] at h
  rw [nextElInstEq f1]
  exact h

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.uniqFstSplitNorm
#print axioms Kepler.Text.Reduction5.fstEqNextYtransV0
#print axioms Kepler.Text.Reduction5.fstEqPrevZtransV0
#print axioms Kepler.Text.Reduction5.betEqNilImpNextZY
