/-
  Kepler.Text.Reduction5J5FaceDiffR — J5-2 续段：`face_diff_r`（reduction2.hl:843，160L）本体。

  ┌─ 归属对账（HOL Light Flyspeck reduction2.hl）───────────────────
  │ :843 `face_diff_r` → `faceDiffR`：
  │   r_rtrans_eq L N r x ∧ good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
  │   is_restricted (hypermap_of_list L) ∧ next_el (find_face L x) x = w ∧
  │   rotate_to (find_face L x) w = fw ∧ ¬final_list L r ⇒
  │   filter (λd. ¬MEM d r) fw =
  │     cat (filter (λd. ¬MEM d r) (rtrans L N r x 1))
  │         (filter (λd. ¬MEM d (rtrans L N r x 1)) fw)
  └────────────────────────────────────────────────────────────────

  ┌─ 前提集对账 ─────────────────────────────────────────────────────
  │ HOL 八前提逐条对应；另加 `haq : AqiunppSlot L hL`——HOL 证体的
  │ `Ncvibwu.NCVIBWU` 陈述带 `transform_assumption_v2 L`（HOL 由
  │ transform_assumption_v2_lemma 无条件消），链侧按既定口径「TAV2 ↦ AqiunppSlot」
  │ 以槽承载，链形件 `ncvibwuTowerI`（Reduction3ChainTower，fdb02c84）即带 haq。
  │ 这是 +1 前提的链惯例偏离（陈述其余逐字），记档。
  └────────────────────────────────────────────────────────────────

  ┌─ 证体路线（HOL :854-:1000 逐段对照）────────────────────────────
  │ 记 f = find_face L x、y = l'y、z = l'z、n = indexl z fw。
  │ ① `rtrans_diff_r`：filter (∉r) (rtrans 1) = betwn f y z。
  │ ② fw 在 n 处 take/drop；两段目标：
  │   (a) filter (∉r) (take n fw) = betwn f y z：
  │        betwn fw y z = betwn f y z（betwn_rotate_to_face），其元素 ∉ r
  │        （Aq1.betwn_not_in_rtrans 链层形）；betwn_take_drop 展成
  │        (fw.drop (idx y+1)).take (n-(idx y+1))，drop_take_commute 折成
  │        (fw.take n).drop (idx y+1)；cat_take_drop (SUC idx y) 后前段
  │        filter = []（mem_take_index2 + le_y_in_r），后段 filter = 自身。
  │   (b) filter (∉r) (drop n fw) = filter (∉rtrans1) (drop n fw)：
  │        eq_in_filter（= 核心 List.filter_congr）逐点，r_rtrans_eq 在
  │        下标 ≥ n 段给 `x' ∈ r ↔ x' ∈ rtrans 1`；
  │        另 filter (∉rtrans1) (take n fw) = []：元素下标 < n = idx z，
  │        经 indexf_rotate_to_indexl + NCVIBWU（ncvibwuTowerI）落 rtrans 1。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5IndexfUnlock
import Kepler.Text.Reduction5J5RotBridges
import Kepler.Text.Reduction5J5Red2Pieces
import Kepler.Text.Reduction5J5Red2Sub
import Kepler.Text.Reduction1W2a
import Kepler.Text.MoreLemma2a23
import Kepler.Text.PwssratFace
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.Reduction3HbridgeElim
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.TameList18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- 链 marked + ¬final ⇒ spine 全套（私有打包）。 -/
private theorem spineOfChainF (L : fgraph ℕ) (hL : GoodList L)
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

/-- 链层 `betwn (find_face L x) y z` 的元素不在 r 上（私有，HOL `Aq1.betwn_not_in_rtrans`）。 -/
private theorem betwnNotInRtransF (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) {d : Dart}
    (hd : d ∈ between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x)
      (lz L N r x)) :
    d ∉ r := by
  obtain ⟨hunL, hmS, hfS⟩ := spineOfChainF L hL hgn hm hnf
  have hyzf := Kepler.Text.TameSpine.markedLemmaYzInFace L hL hgn hunL hmS hfS
  have hfac : findFaceDarts L x =
      findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x) :=
    (memFindFaceImpFacesEq hL.1 hyzf.1).symm
  have hd' : d ∈ between (findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x))
      (Kepler.Text.TameSpine.lYSpine L r x) (Kepler.Text.TameSpine.lZSpine L N r x) := by
    rw [Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
      Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
      hfac] at hd
    exact hd
  exact Kepler.Text.TameSpine.betwnNotInRtrans L hL hgn hunL hmS hfS hd'

/-- **HOL `face_diff_r`**（reduction2.hl:843）：`fw` 的 `∉r` 过滤按 `rtrans 1` 切两段。 -/
theorem faceDiffR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x w : Dart} {fw : List Dart}
    (hrr : rRtransEq L N r x)
    (hm : markedList L hL N r x)
    (hw : nextEl (findFaceDarts L x) x = w)
    (hfw : Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) w = fw)
    (hnf : ¬ finalList L r) :
    fw.filter (fun d => d ∉ r) =
      (rtrans L N r x 1).filter (fun d => d ∉ r) ++
        fw.filter (fun d => d ∉ rtrans L N r x 1) := by
  -- ── 基本件 ──
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hx : x ∈ findFaceDarts L x :=
    (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwmem : w ∈ findFaceDarts L x := hw ▸ Kepler.Text.TameLp.nextEl_mem_of_mem hx
  have hy : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x :=
    Kepler.Text.Reduction4Idx.lyMemFindFaceDarts L hL hm
  have hz : lz L N r x ∈ findFaceDarts L x :=
    Kepler.Text.Reduction4Idx.lzMemFindFaceDarts L hL hm
  -- fw 侧：无重与成员往返
  have hndfw : fw.Nodup := by
    rw [← hfw, Kepler.Text.Reduction1.rotateToBridge]
    exact rotateToUniq hwmem hnd
  have hmemfw : ∀ u : Dart, (u ∈ fw ↔ u ∈ findFaceDarts L x) := by
    intro u
    rw [← hfw, Kepler.Text.Reduction1.rotateToBridge]
    exact (Kepler.Text.Reduction1.memRotateTo2 hwmem hnd).symm
  have hzfw : lz L N r x ∈ fw := (hmemfw _).mpr hz
  -- 下标序
  have hlt : fw.idxOf (Kepler.Text.Reduction5.ly L r x) < fw.idxOf (lz L N r x) :=
    indexlYLtZ L hL hres hgn hm hw hfw hnf
  set n := fw.idxOf (lz L N r x) with hn
  have hnfw : n ≤ fw.length := by
    rw [hn]
    exact Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hzfw)
  -- ── ① rtrans_diff_r ──
  have hrt := rtransDiffR L hL hgn hm hnf
  -- ── (a) filter (∉r) (take n fw) = betwn f y z ──
  have hbetwf : between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x) =
      between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x) (lz L N r x) :=
    betwnRotateToFace L hL hgn hm hnf hwmem hfw
  have hbetNot : ∀ d ∈ between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x), d ∉ r := by
    intro d hd
    rw [hbetwf] at hd
    exact betwnNotInRtransF L hL hgn hm hnf hd
  have hbtnil : between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x) =
      (fw.drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)).take
        (n - (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)) := by
    have hb := Kepler.Text.TameSpine.betwnTakeDrop (u := Kepler.Text.Reduction5.ly L r x)
      (v := lz L N r x) hndfw hzfw
    rw [if_pos hlt] at hb
    rw [hb, ← hn]
  have hbt' : between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x) =
      (fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1) := by
    rw [hbtnil]
    exact (Kepler.Text.TameSpine.dropTakeCommute
      (s := fw) (n := n) (k := fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)
      (by omega)).symm
  have hbetFilter : (between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x)).filter
        (fun d => d ∉ r) = between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (hbetNot d hd)
  -- 前段 filter (∉r) (fw.take (SUC idx y)) = []
  have htakeSucFilter : (fw.take (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)).filter
        (fun d => d ∉ r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x' hx' hnot
    exact (of_decide_eq_true hnot) (by
      have hx'fw : x' ∈ fw := List.mem_of_mem_take hx'
      have hx'f : x' ∈ findFaceDarts L x := (hmemfw x').mp hx'fw
      have hidx : fw.idxOf x' < fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1 :=
        (memTakeIndex2 hndfw (by omega)).mp hx'
      have hix : indexf w x' (findFaceDarts L x) = fw.idxOf x' := by
        rw [← hfw, rotateToInstEq, idxOfInstEq]
        exact indexfRotateToIndexl hx'f hwmem hnd
      have hiy : indexf w (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x) =
          fw.idxOf (Kepler.Text.Reduction5.ly L r x) := by
        rw [← hfw, rotateToInstEq, idxOfInstEq]
        exact indexfRotateToIndexl hy hwmem hnd
      have hle : indexf w x' (findFaceDarts L x) ≤ Kepler.Text.TameSpine.lMSpine L r x := by
        obtain ⟨-, hmS, hfS⟩ := spineOfChainF L hL hgn hm hnf
        have h1 : Kepler.Text.TameSpine.indexf w (Kepler.Text.Reduction5.ly L r x)
            (findFaceDarts L x) = Kepler.Text.TameSpine.lMSpine L r x := by
          have h0 := Kepler.Text.TameSpine.indexfYtransEqLm L hL hgn hunL hmS hfS
          rw [hw, ← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf] at h0
          exact h0
        calc indexf w x' (findFaceDarts L x) = fw.idxOf x' := hix
          _ ≤ fw.idxOf (Kepler.Text.Reduction5.ly L r x) := by omega
          _ = indexf w (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x) := hiy.symm
          _ = Kepler.Text.TameSpine.indexf w (Kepler.Text.Reduction5.ly L r x)
                (findFaceDarts L x) :=
              Kepler.Text.Reduction3.indexf_eq_spine w (Kepler.Text.Reduction5.ly L r x)
                (findFaceDarts L x)
          _ = Kepler.Text.TameSpine.lMSpine L r x := h1
      obtain ⟨-, hmS0, hfS0⟩ := spineOfChainF L hL hgn hm hnf
      have hle_ts : Kepler.Text.TameSpine.indexf
          (Kepler.Assembly.nextEl (findFaceDarts L x) x) x' (findFaceDarts L x)
          ≤ Kepler.Text.TameSpine.lMSpine L r x := by
        rw [← Kepler.Text.Reduction3.indexf_eq_spine
          (Kepler.Assembly.nextEl (findFaceDarts L x) x) x' (findFaceDarts L x), hw]
        exact hle
      exact Kepler.Text.TameSpine.leYInR L hL hgn hunL hmS0 hfS0 hx'f hle_ts)
  -- 后段 filter = 自身
  have hdropFilter : ((fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)).filter
        (fun d => d ∉ r) =
      (fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1) := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (by rw [← hbt'] at hd; exact hbetNot d hd)
  have htakeFilter : (fw.take n).filter (fun d => d ∉ r) =
      between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
    have hsplit : fw.take n =
        (fw.take n).take (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1) ++
          (fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1) :=
      (List.take_append_drop _ _).symm
    calc (fw.take n).filter (fun d => d ∉ r)
        = ((fw.take n).take (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)).filter
            (fun d => d ∉ r) ++
          ((fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)).filter
            (fun d => d ∉ r) := by
          rw [← List.filter_append, ← hsplit]
      _ = [] ++ ((fw.take n).drop (fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1)) := by
          rw [Kepler.Text.TameSpine.takeTake (s := fw) (i := fw.idxOf (Kepler.Text.Reduction5.ly L r x) + 1) (j := n) (by omega), htakeSucFilter, hdropFilter]
      _ = between fw (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
          rw [List.nil_append, hbt']
      _ = between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := hbetwf
  -- ── (b) filter(∉rtrans1)(take n) = [] 与 drop 段逐点 ──
  have htakeRtrans1 : (fw.take n).filter (fun d => d ∉ rtrans L N r x 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x' hx' hnot
    exact (of_decide_eq_true hnot) (by
      have hx'fw : x' ∈ fw := List.mem_of_mem_take hx'
      have hx'f : x' ∈ findFaceDarts L x := (hmemfw x').mp hx'fw
      have hidx : fw.idxOf x' < n := (memTakeIndex2 hndfw hnfw).mp hx'
      have hx'idx : indexf w x' (findFaceDarts L x) = fw.idxOf x' := by
        rw [← hfw, rotateToInstEq, idxOfInstEq]
        exact indexfRotateToIndexl hx'f hwmem hnd
      have hzidx : indexf w (lz L N r x) (findFaceDarts L x) = n := by
        rw [hn, ← hfw, rotateToInstEq, idxOfInstEq]
        exact indexfRotateToIndexl hz hwmem hnd
      have hj : fw.idxOf x' ≤
          Kepler.Text.TameSpine.indexf w (ztrans L N r x 0) (findFaceDarts L x) := by
        rw [← Kepler.Text.Reduction3.indexf_eq_spine w (ztrans L N r x 0)
            (findFaceDarts L x),
          show ztrans L N r x 0 = lz L N r x from rfl, hzidx]
        exact Nat.le_of_lt hidx
      have hmem := (Kepler.Text.TameSpine.ncvibwuTowerI L hL hgn haq
        (i := 0) hm hnf (f := findFaceDarts L x) (w := w) rfl hw
        (j := fw.idxOf x') hj).1
      have hxj : (Kepler.Assembly.nextEl (findFaceDarts L x))^[fw.idxOf x'] w = x' := by
        rw [← hx'idx, Kepler.Text.Reduction3.indexf_eq_spine w x' (findFaceDarts L x)]
        exact Kepler.Text.TameSpine.indexfN hwmem hx'f hnd
      rw [hxj, Nat.zero_add] at hmem
      exact hmem)
  have hdrop_pt : ∀ x' ∈ fw.drop n, (x' ∉ r ↔ x' ∉ rtrans L N r x 1) := by
    intro x' hx'
    have hx'fw : x' ∈ fw := List.mem_of_mem_drop hx'
    have hx'f : x' ∈ findFaceDarts L x := (hmemfw x').mp hx'fw
    have hidx : n ≤ fw.idxOf x' :=
      (Kepler.Text.TameSpine.memDropIndex hndfw hx'fw).mp hx'
    have hx'idx : indexf w x' (findFaceDarts L x) = fw.idxOf x' := by
      rw [← hfw, rotateToInstEq, idxOfInstEq]
      exact indexfRotateToIndexl hx'f hwmem hnd
    have hzidx : indexf w (lz L N r x) (findFaceDarts L x) = n := by
      rw [hn, ← hfw, rotateToInstEq, idxOfInstEq]
      exact indexfRotateToIndexl hz hwmem hnd
    have hge : indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)
        ≤ indexf (nextEl (findFaceDarts L x) x) x' (findFaceDarts L x) := by
      rw [hw, hzidx, hx'idx]
      exact hidx
    exact not_congr (hrr x' hx'f hge)
  have hdropRtrans : (fw.drop n).filter (fun d => d ∉ r) =
      (fw.drop n).filter (fun d => d ∉ rtrans L N r x 1) := by
    apply List.filter_congr
    intro x' hx'
    exact decide_eq_decide.mpr (hdrop_pt x' hx')
  -- ── 组装 ──
  have hTakeEq : (fw.take n).filter (fun d => d ∉ r) =
      (rtrans L N r x 1).filter (fun d => d ∉ r) :=
    htakeFilter.trans hrt.symm
  calc fw.filter (fun d => d ∉ r)
      = (fw.take n).filter (fun d => d ∉ r) ++ (fw.drop n).filter (fun d => d ∉ r) := by
        rw [← List.filter_append, List.take_append_drop]
    _ = (fw.take n).filter (fun d => d ∉ r) ++ (fw.drop n).filter (fun d => d ∉ rtrans L N r x 1) := by
        rw [hdropRtrans]
    _ = (rtrans L N r x 1).filter (fun d => d ∉ r) ++
          (fw.drop n).filter (fun d => d ∉ rtrans L N r x 1) := by
        rw [hTakeEq]
    _ = (rtrans L N r x 1).filter (fun d => d ∉ r) ++
          ((fw.take n).filter (fun d => d ∉ rtrans L N r x 1) ++
            (fw.drop n).filter (fun d => d ∉ rtrans L N r x 1)) := by
        rw [htakeRtrans1, List.nil_append]
    _ = (rtrans L N r x 1).filter (fun d => d ∉ r) ++
          fw.filter (fun d => d ∉ rtrans L N r x 1) := by
        rw [← List.filter_append, List.take_append_drop]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.faceDiffR
