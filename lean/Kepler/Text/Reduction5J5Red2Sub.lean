/-
  Kepler.Text.Reduction5J5Red2Sub — J5-2 续段：reduction2 章 `face_diff_r`（:843）
  的六件前置中**本波落下的两件**（`cat_eq` 与 `rotate_to_uniq` 在 Reduction5J5RotBridges）：
  `memTakeIndex2`、`betwnRotateToFace`。另四件（indexf 耦合的三件 + `indexl_y_lt_z`）
  与本文件头列的 `face_diff_r` 本体一并冻结，卡点与修法见 DELIVERY_j55 §4。

  ┌─ 归属对账（HOL Light Flyspeck reduction2.hl）────────────────────
  │ ❄（冻结）:233 `indexf_rotate_to`（13L）→ `indexfRotateTo`：
  │    MEM x f ∧ MEM w f ∧ MEM z f ∧ uniq f ⇒ indexf w z (rotate_to f x) = indexf w z f
  │ ❄（冻结）:241 `indexf_rotate_to_indexl`（13L）→ `indexfRotateToIndexl`：
  │    MEM z f ∧ MEM w f ∧ uniq f ⇒ indexf w z f = indexl z (rotate_to f w)
  │ ✅:254 `mem_take_index2`（15L）→ `memTakeIndex2`：
  │    uniq s ∧ k ≤ sizel s ⇒ (MEM v (take k s) ⇔ indexl v s < k)
  │ ✅:527 `betwn_rotate_to_face`（29L）→ `betwnRotateToFace`：
  │    … marked_list ∧ ¬final_list ∧ MEM w (find_face L x) ∧
  │    rotate_to (find_face L x) w = f ⇒
  │    betwn f (l'y L r x) (l'z L N r x) = betwn (find_face L x) (l'y) (l'z)
  │ ❄（冻结）:556 `indexl_y_lt_z`（64L）→ `indexlYLtZ`：
  │    … ∧ next_el (find_face L x) x = w ∧ rotate_to (find_face L x) w = fw ∧ ¬final_list
  │    ⇒ indexl (l'y L r x) fw < indexl (l'z L N r x) fw
  │ ❄（冻结）OHCGKFU.hl:28 `indexf_indexl_hd` → `indexfIndexlHd`：
  │    indexf (HD x) y x = indexl y x（私有支件，前两件的公共步）
  └────────────────────────────────────────────────────────────────

  ┌─ 查重与复用 ──────────────────────────────────────────────────────
  │ `indexf_rotn`（tame_list.hl:1738）= 树内 `TameSpine.indexfRotn`
  │ （TameList3:336，泛型，已诚实省略 `n ≤ sizel` 冗余前提）——`indexf_rotate_to`
  │ 由此 + `rotateToEqRotate` 直拼，不重落。
  │ `betwn_rot`（reduction2.hl:107）= spine `betwnRot`（JcajyduBetwnRot:179）。
  │ `HQYMRTX3_list` = `hqymrtx3List`（TameList17:383）。
  │ `marked_lemma_yz_in_face` = `markedLemmaYzInFace`（TameList18:96）。
  │ `PPLHULJ3_v0` = 链侧 `pplhulj3V0`（PwssratFace:195）。
  │ `hd_rotate_to`/`mem_rotate_to` = spine 同名件；`rot_uniq`/`mem_rot`/
  │ `rot_oversize` = Mathlib `nodup_rotate`/`mem_rotate`/`rotate_mod`。
  └────────────────────────────────────────────────────────────────

  ┌─ 证体（与 HOL 逐件对照）────────────────────────────────────────
  │ · indexfIndexlHd：`indexf` 展开 + `idxOf head = 0` + `Nat.add_mod_right`
  │   （`u ∉ l` 支 `idxOf = length`，`length % length = 0`）。
  │ · indexfRotateTo：`rotateToEqRotate` + `indexfRotn`（n := idxOf x）。
  │ · indexfRotateToIndexl：`indexf w z (rotate_to f w) = idxOf z (rotate_to f w)`
  │   （`indexfIndexlHd` + `hd_rotate_to`）→ 左端换回 `indexf w z f`
  │   （`indexfRotateTo`，x := w）。
  │ · memTakeIndex2：`mem_iff_getElem` + `getElem_take` + `idxOf_getElem`（Nodup）
  │   / `idxOf_eq_length`（不在支）。
  │ · betwnRotateToFace：`betwnRot`（n := idxOf w）+ `rotateToEqRotate`；
  │   y/z ∈ find_face 走 spine `markedLemmaYzInFace` 经 `lyEqSpine`/`lzEqSpine`
  │   折算（y ≠ z 走 `hqymrtx3List`）；`find_face` uniq 走 `findFaceDarts_nodup`。
  │ · indexlYLtZ：`pplhulj3V0`（链侧）+ `indexfRotateToIndexl` 把 idxOf 换成
  │   indexf（`u ∈ f` 两侧同改），`hw` 改写即得。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5RotBridges
import Kepler.Text.TameSpine.JcajyduBetwnRot
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.TameList18
import Kepler.Text.PwssratFace
import Kepler.Text.Reduction5J5Termination

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `mem_take_index2`**（reduction2.hl:254）：`uniq s ∧ k ≤ sizel s ⇒
(MEM v (take k s) ⇔ indexl v s < k)`。 -/
theorem memTakeIndex2 {s : List Dart} {v : Dart} {k : ℕ}
    (hnd : s.Nodup) (hk : k ≤ s.length) : (v ∈ s.take k ↔ s.idxOf v < k) := by
  constructor
  · intro hmem
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have hik : i < k := by have := hi; rw [List.length_take] at this; omega
    have hilt : i < s.length := by have := hi; rw [List.length_take] at this; omega
    have hsv : s[i]'hilt = v := by
      rw [← hget]
      exact (List.getElem_take (xs := s) (j := k) (i := i) (h := hi)).symm
    rw [← hsv, Kepler.Text.TameLp.idxOf_getElem hnd hilt]
    exact hik
  · intro hidx
    have hlt : s.idxOf v < s.length := Nat.lt_of_lt_of_le hidx hk
    have hmem : s[s.idxOf v]'hlt ∈ s.take k := by
      apply List.mem_iff_getElem.mpr
      refine ⟨s.idxOf v, ?_, ?_⟩
      · rw [List.length_take]; omega
      · rw [List.getElem_take, Kepler.Text.TameLp.getElem_idxOf
          (List.idxOf_lt_length_iff.mp hlt)]
    rw [Kepler.Text.TameLp.getElem_idxOf (List.idxOf_lt_length_iff.mp hlt)] at hmem
    exact hmem

/-- 链 marked + ¬final ⇒ spine 全套（私有打包；y/z 面成员与 y≠z 的桥用）。 -/
private theorem spineOfChain2 (L : fgraph ℕ) (hL : GoodList L)
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

/-- **HOL `betwn_rotate_to_face`**（reduction2.hl:527）：把 `rot` 过的面换回原面。 -/
theorem betwnRotateToFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x w : Dart} {f : List Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hw : w ∈ findFaceDarts L x)
    (hf : Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) w = f) :
    between f (Kepler.Text.Reduction5.ly L r x) (lz L N r x) =
      between (findFaceDarts L x) (Kepler.Text.Reduction5.ly L r x) (lz L N r x) := by
  obtain ⟨hunL, hmS, hfS⟩ := spineOfChain2 L hL hgn hm hnf
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hyz := Kepler.Text.TameSpine.markedLemmaYzInFace L hL hgn hunL hmS hfS
  have hy : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x := by
    rw [Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf]
    exact hyz.1
  have hz : lz L N r x ∈ findFaceDarts L x := by
    rw [Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf]
    exact hyz.2
  have hyz' : Kepler.Text.Reduction5.ly L r x ≠ lz L N r x := by
    intro hcon
    apply Kepler.Text.TameSpine.hqymrtx3List L hL hgn hunL hmS hfS
    rw [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
      ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf]
    exact hcon
  rw [← hf, Kepler.Text.Reduction1.rotateToBridge,
    Kepler.Text.Reduction1.rotateToEqRotate hw hnd]
  exact (Kepler.Text.TameSpine.betwnRot (s := findFaceDarts L x)
    (x := Kepler.Text.Reduction5.ly L r x) (y := lz L N r x)
    hnd hy hz hyz' ((findFaceDarts L x).idxOf w)).symm

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.memTakeIndex2
#print axioms Kepler.Text.Reduction5.betwnRotateToFace
