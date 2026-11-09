/-
  Kepler.Text.Reduction3Thm7C — reduction_C 的**非 J2 支撑两件**
  （`final_list_pairs` :2571 / `final_list_pairs_core` :2593）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   final_list_pairs       reduction3.hl:2571 → finalListPairs
  │   final_list_pairs_core  reduction3.hl:2593 → finalListPairsCore
  │ 用途：reduction_C（J2 板）证明体直接消费；本批按编排者裁定先落，
  │ J2 收口时少两件。reduction_C/B/A 本体仍 BLOCKED（TAV2）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字）───────────────────────────────────
  │ ① `MAP FST r` ↦ `r.map (fun d => d.1)`；`list_pairs` ↦ `listPairs`。
  │ ② `is_restricted (hypermap_of_list L)` ↦ `(hypermapOfList L hL).IsRestricted`
  │    （链侧 `hypermapOfList` 吃 hL；hL 即前提 `good_list L`）。
  │ ③ `all (\x. MEM x (list_of_darts L)) r` ↦ `∀ d ∈ r, d ∈ listOfDarts L`。
  │ ④ `final_list` ↦ 链侧 `finalList`（Spine 桥
  │    `ChainBridge.finalList_iff_finalListSpine`，Iff.rfl 同体）。
  │ ⑤ `core L r` ↦ 链侧 `core`；证体内经私件 `t7c_coreEqCoreSpine`
  │    （`parts_eq_partsSpine` + headD/head! 点态）转 Spine 形供
  │    `finalListCore`（TameList47）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ────────────────────────────────────────────────────────
  │ final_list_pairs：`finalListRot`（TameList8）给 `r.rotate n = find_face L x`；
  │ `rotSym` 反向给 `find_face.rotate m = r`；`faceRep`（TameList31）+
  │ `memFindFace`（TameList6）给 `listPairs (find_face.map fst) = find_face`；
  │ 再由私件 `t7c_listPairs_rotate`（listPairs/rotate 交换，Assembly 私件
  │ 同证重落）收口。
  │ final_list_pairs_core：`finalListCore`（TameList47）给
  │ `coreSpine = r.map fst`，私件 core 桥 + 上件直投。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t7c_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm5D
import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList31
import Kepler.Text.TameSpine.TameList47

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Graphs (Face Graph between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList)

/-! ## §0 私有辅助（Assembly/TameList50 私件同证重落，不跨模块引用） -/

/-- `List.rotate 1` 的 drop/take 展开（`listPairs` 定义体形态）。 -/
private theorem t7c_rotateOne {α : Type} (l : List α) :
    l.rotate 1 = l.drop 1 ++ l.take 1 := by
  cases l with
  | nil => simp [List.rotate]
  | cons a t =>
    cases t with
    | nil => simp [List.rotate]
    | cons b s =>
      have hmod : 1 % (s.length + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [List.rotate, hmod]

/-- `listPairs` 与 `rotate` 交换：`listPairs (l.rotate n) = (listPairs l).rotate n`
（Assembly `ell_listPairs_rotate` 同证重落，泛型化）。 -/
private theorem t7c_listPairs_rotate {α : Type} (l : List α) (n : ℕ) :
    listPairs (l.rotate n) = (listPairs l).rotate n := by
  have hfold : listPairs l = List.zipWith Prod.mk l (l.drop 1 ++ l.take 1) :=
    List.zip_eq_zipWith
  calc listPairs (l.rotate n)
      = List.zipWith Prod.mk (l.rotate n)
          ((l.rotate n).drop 1 ++ (l.rotate n).take 1) := List.zip_eq_zipWith
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate n).rotate 1) := by
        rw [t7c_rotateOne]
    _ = List.zipWith Prod.mk (l.rotate n) (l.rotate (n + 1)) := by
        rw [List.rotate_rotate]
    _ = List.zipWith Prod.mk (l.rotate n) ((l.rotate 1).rotate n) := by
        rw [List.rotate_rotate, Nat.add_comm]
    _ = (List.zipWith Prod.mk l (l.rotate 1)).rotate n :=
        (List.zipWith_rotate_distrib Prod.mk l (l.rotate 1) n
          (List.length_rotate l 1).symm).symm
    _ = (List.zipWith Prod.mk l (l.drop 1 ++ l.take 1)).rotate n := by
        rw [t7c_rotateOne l]
    _ = (listPairs l).rotate n := by rw [hfold]

/-- `core` 链/Spine 桥（T4TheoryB `coreEqCoreSpine` 同证重落）。 -/
private theorem t7c_coreEqCoreSpine (L : fgraph ℕ) (r : List Dart) :
    core L r = Kepler.Text.TameSpine.coreSpine L r := by
  unfold core Kepler.Text.TameSpine.coreSpine
  rw [Kepler.Text.ChainBridge.parts_eq_partsSpine L r]
  congr 1
  funext p
  cases p with
  | nil => rfl
  | cons x xs => rfl

/-! ## §A 两件 -/

/-- HOL `final_list_pairs`（reduction3.hl:2571）：
`good_list L ∧ uniq r ∧ final_list L r ∧ MEM x r ∧ MEM x (list_of_darts L) ⇒
list_pairs (MAP FST r) = r`。 -/
theorem finalListPairs (L : fgraph ℕ) (r : List Dart) (x : Dart)
    (hL : GoodList L) (hrn : r.Nodup) (hfin : finalList L r) (hxr : x ∈ r)
    (hxD : x ∈ listOfDarts L) :
    listPairs (r.map (fun d => d.1)) = r := by
  have hfsp : Kepler.Text.TameSpine.finalListSpine L r :=
    (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp hfin
  obtain ⟨n, hn⟩ := Kepler.Text.TameSpine.finalListRot hL hfsp hxr hrn hxD
  obtain ⟨m, hm⟩ :=
    (Kepler.Text.TameSpine.rotSym (r := r) (s := findFaceDarts L x)).mp ⟨n, hn⟩
  have hface : listPairs ((findFaceDarts L x).map (fun d => d.1)) = findFaceDarts L x := by
    obtain ⟨f0, h1, h2, h3⟩ := Kepler.Text.TameSpine.faceRep L (findFaceDarts L x)
      (Kepler.Text.TameSpine.memFindFace L hxD)
    rw [h3, h1]
  rw [← hm, List.map_rotate, t7c_listPairs_rotate, hface]

/-- HOL `final_list_pairs_core`（reduction3.hl:2593）：
`is_restricted (hypermap_of_list L) ∧ (∀x∈r, MEM x (list_of_darts L)) ∧
good_list L ∧ uniq r ∧ final_list L r ∧ MEM x r ∧ MEM x (list_of_darts L) ⇒
list_pairs (core L r) = r`。 -/
theorem finalListPairsCore (L : fgraph ℕ) (r : List Dart) (x : Dart)
    (hL : GoodList L) (hir : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (hdarts : ∀ d ∈ r, d ∈ listOfDarts L) (hrn : r.Nodup) (hfin : finalList L r)
    (hxr : x ∈ r) (hxD : x ∈ listOfDarts L) :
    listPairs (core L r) = r := by
  have hfsp : Kepler.Text.TameSpine.finalListSpine L r :=
    (Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mp hfin
  have hcoreSpine : Kepler.Text.TameSpine.coreSpine L r = r.map (fun d => d.1) :=
    Kepler.Text.TameSpine.finalListCore hL hdarts hir.edgeNondegenerate hrn hfsp
  rw [t7c_coreEqCoreSpine, hcoreSpine]
  exact finalListPairs L r x hL hrn hfin hxr hxD

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.finalListPairs
#print axioms Kepler.Text.Reduction3.finalListPairsCore
