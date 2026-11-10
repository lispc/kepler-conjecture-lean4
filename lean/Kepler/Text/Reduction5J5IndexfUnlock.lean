/-
  Kepler.Text.Reduction5J5IndexfUnlock — J5-2 续段：实例桥解锁的四件。
  · `indexfIndexlHd`（OHCGKFU.hl:28）
  · `indexfRotateTo`（reduction2.hl:233）
  · `indexfRotateToIndexl`（reduction2.hl:241）
  · `indexlYLtZ`（reduction2.hl:556）
  前三件在 **DecidableEq 世界**陈述（`indexf` 定义烘焙该实例，单实例无反例），
  Dart 端点由 `Reduction5J5InstBridges` 的 `rotateToInstEq` 与既有 `idxOfInstEq`
  折算（`indexlYLtZ`）。

  ┌─ 归属对账（HOL Light Flyspeck）─────────────────────────────────
  │ OHCGKFU.hl:28 `indexf_indexl_hd` → `indexfIndexlHd`：
  │   `indexf (HD x) y x = indexl y x`
  │ reduction2.hl:233 `indexf_rotate_to` → `indexfRotateTo`：
  │   `MEM x f ∧ MEM w f ∧ MEM z f ∧ uniq f ⇒ indexf w z (rotate_to f x) = indexf w z f`
  │ reduction2.hl:241 `indexf_rotate_to_indexl` → `indexfRotateToIndexl`：
  │   `MEM z f ∧ MEM w f ∧ uniq f ⇒ indexf w z f = indexl z (rotate_to f w)`
  │ reduction2.hl:556 `indexl_y_lt_z`（64L）→ `indexlYLtZ`（Dart）：
  │   good_list ∧ is_restricted ∧ good_list_nodes ∧ marked_list ∧
  │   next_el (find_face L x) x = w ∧ rotate_to (find_face L x) w = fw ∧ ¬final_list
  │   ⇒ indexl (l'y L r x) fw < indexl (l'z L N r x) fw
  └────────────────────────────────────────────────────────────────

  ┌─ 证体 ───────────────────────────────────────────────────────────
  │ · indexfIndexlHd：`indexf` 展开 + `idxOf head = 0` + `Nat.add_mod_right`
  │   （`u ∉ l` 支 `idxOf = length`）。
  │ · indexfRotateTo：`rotateToEqRotate`（W2d）+ `indexfRotn`（TameList3:336，
  │   = HOL indexf_rotn）反向；经 `indexf_eq_spine`（Thm6B:122）把链 indexf 转
  │   spine 形。
  │ · indexfRotateToIndexl：`indexf w z (rotate_to f w) = idxOf z (rotate_to f w)`
  │   （`indexfIndexlHd` + 头元 rfl）+ `indexfRotateTo`（x := w）折回。
  │ · indexlYLtZ：`pplhulj3V0`（PwssratFace:195，链侧）+ idxOf↔indexf 改写
  │   （前一件）+ `hw` 改写；Dart 端点的实例差用 `rotateToInstEq`/`idxOfInstEq`/
  │   `nextElInstEq` 折算。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5InstBridges
import Kepler.Text.Reduction5J5Red2Sub
import Kepler.Text.PwssratFace
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `Ohcgkfu.indexf_indexl_hd`**（OHCGKFU.hl:28）：`indexf (HD x) y x = indexl y x`。 -/
theorem indexfIndexlHd {α : Type} [DecidableEq α] {l : List α} (h : l ≠ []) (u : α) :
    indexf (l.head h) u l = l.idxOf u := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    show indexf a u (a :: t) = (a :: t).idxOf u
    by_cases hu : u ∈ a :: t
    · unfold indexf
      rw [if_pos ⟨List.mem_cons_self, hu⟩, List.idxOf_cons_self, Nat.sub_zero]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr hu)]
    · unfold indexf
      rw [if_neg (fun hc => hu hc.2), List.idxOf_eq_length hu]

/-- **HOL `indexf_rotate_to`**（reduction2.hl:233）：`indexf` 对 `rotate_to` 不变
（参数都在表上时）。 -/
theorem indexfRotateTo {α : Type} [DecidableEq α] [Inhabited α] {f : List α} {w z x : α}
    (hx : x ∈ f) (hw : w ∈ f) (hz : z ∈ f) (hnd : f.Nodup) :
    indexf w z (Kepler.Text.Reduction3.rotateTo f x) = indexf w z f := by
  rw [Kepler.Text.Reduction1.rotateToBridge,
    Kepler.Text.Reduction1.rotateToEqRotate hx hnd]
  rw [Kepler.Text.Reduction3.indexf_eq_spine w z (f.rotate (f.idxOf x)),
    Kepler.Text.Reduction3.indexf_eq_spine w z f]
  exact (Kepler.Text.TameSpine.indexfRotn hw hz hnd
    (Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hx))).symm

/-- **HOL `indexf_rotate_to_indexl`**（reduction2.hl:241）：
`indexf w z f = indexl z (rotate_to f w)`。 -/
theorem indexfRotateToIndexl {α : Type} [DecidableEq α] [Inhabited α] {f : List α} {w z : α}
    (hz : z ∈ f) (hw : w ∈ f) (hnd : f.Nodup) :
    indexf w z f = (Kepler.Text.Reduction3.rotateTo f w).idxOf z := by
  have hne : Kepler.Text.Reduction3.rotateTo f w ≠ [] := by
    simp [Kepler.Text.Reduction3.rotateTo]
  have hhead : (Kepler.Text.Reduction3.rotateTo f w).head hne = w := rfl
  have h1 : indexf w z (Kepler.Text.Reduction3.rotateTo f w) =
      (Kepler.Text.Reduction3.rotateTo f w).idxOf z := by
    rw [← hhead]
    exact indexfIndexlHd hne z
  rw [← h1]
  exact (indexfRotateTo (x := w) hw hw hz hnd).symm

/-- **HOL `indexl_y_lt_z`**（reduction2.hl:556，Dart 形）：`indexl (l'y) fw < indexl (l'z) fw`。 -/
theorem indexlYLtZ (L : fgraph ℕ) (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x w : Dart} {fw : List Dart}
    (hm : markedList L hL N r x)
    (hw : Kepler.Assembly.nextEl (findFaceDarts L x) x = w)
    (hfw : Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) w = fw)
    (hnf : ¬ finalList L r) :
    fw.idxOf (Kepler.Text.Reduction5.ly L r x) < fw.idxOf (lz L N r x) := by
  have hnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hx : x ∈ findFaceDarts L x :=
    (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hwmem : w ∈ findFaceDarts L x := hw ▸ Kepler.Text.TameLp.nextEl_mem_of_mem hx
  have hy : Kepler.Text.Reduction5.ly L r x ∈ findFaceDarts L x :=
    Kepler.Text.Reduction4Idx.lyMemFindFaceDarts L hL hm
  have hz : lz L N r x ∈ findFaceDarts L x :=
    Kepler.Text.Reduction4Idx.lzMemFindFaceDarts L hL hm
  have hpp := Kepler.Text.Reduction4Idx.pplhulj3V0 L hL hgn
    (Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres) hm hnf
  -- 端点换到 DecidableEq 世界
  rw [idxOfInstEq (Kepler.Text.Reduction5.ly L r x) fw,
    idxOfInstEq (lz L N r x) fw]
  have hfw' : @Kepler.Text.Reduction3.rotateTo Dart instBEqOfDecidableEq
      (findFaceDarts L x) w = fw := by
    rw [← rotateToInstEq]
    exact hfw
  have h1 : @List.idxOf Dart instBEqOfDecidableEq (Kepler.Text.Reduction5.ly L r x) fw =
      indexf w (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x) := by
    rw [← hfw']
    exact (indexfRotateToIndexl hy hwmem hnd).symm
  have h2 : @List.idxOf Dart instBEqOfDecidableEq (lz L N r x) fw =
      indexf w (lz L N r x) (findFaceDarts L x) := by
    rw [← hfw']
    exact (indexfRotateToIndexl hz hwmem hnd).symm
  rw [h1, h2]
  -- `hw`（Prod）换到 DecEq（pplhulj3V0 的 nextEl 世界）
  rw [nextElInstEq (findFaceDarts L x) x] at hw
  rw [nextElInstEq (findFaceDarts L x) x] at hpp
  rw [hw] at hpp
  exact hpp

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.indexfIndexlHd
#print axioms Kepler.Text.Reduction5.indexfRotateTo
#print axioms Kepler.Text.Reduction5.indexfRotateToIndexl
#print axioms Kepler.Text.Reduction5.indexlYLtZ
