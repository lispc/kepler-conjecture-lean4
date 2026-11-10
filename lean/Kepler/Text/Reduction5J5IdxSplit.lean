/-
  Kepler.Text.Reduction5J5IdxSplit — J5-2 首段（chain 载体）第一文件：
  `split_normal_list_index1_lemma`（reduction4.hl:896）与
  `split_normal_list_index2_lemma`（:979），连同它们消费的五条小件的链层形。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ tame_list.hl:583 `MEM3_replace` → `mem3Replace`：
  │   ¬(x = f) ∧ MEM x g ⇒ MEM x (replace f xs g)
  │ reduction2.hl:1487 `ntrans1` → `ntrans1`：
  │   ¬final_list L r ⇒ ntrans L N r x 1 = cat (replace r [f2] N) [f1]，
  │   (f1,f2) = split_normal_list L r (find_face L y) y (prev_el r (l'z L N r x))，y = l'y L r x
  │ AQ8.hl:1357 `fst_mem_rtran1` → `fstMemRtran1`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list ⇒ MEM (FST split) (ntrans L N r x 1)
  │ AQ8.hl:48 `snd_mem_rtran1` → `sndMemRtran1`：同前件 ⇒ MEM (SND split) (ntrans L N r x 1)
  │ AQ9.hl:1031 `element_in_ntrans_suc` → `elementInNtransSuc`：
  │   good_list ∧ good_list_nodes ∧ marked_list ∧ MEM f1 N ∧ ¬(f1 = r) ⇒ MEM f1 (ntrans L N r x 1)
  │ reduction4.hl:896 `split_normal_list_index1_lemma`（83L）→ `splitNormalListIndex1Lemma`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list ∧
  │   transform_count L N r x = k ⇒
  │   let (f1,f2) = split_normal_list L r (find_face L x) (ytrans … 0) (prev_el r (ztrans … 0)) in
  │   (MEM (core L f1) (quotient_list L N) ⇒ core L f1 = core L r)
  │ reduction4.hl:979 `split_normal_list_index2_lemma`（73L）→ `splitNormalListIndex2Lemma`：
  │   同上，f1 换 f2
  └────────────────────────────────────────────────────────────────

  ┌─ 陈述写法 ────────────────────────────────────────────────────────
  │ HOL 的 `let (f1,f2) = split … in P` 按树内既定写法把 split 项内联展开、
  │ 用 `.1` / `.2` 投影（spine `ntrans1`（JcajyduRed2Trans:194）头注明记
  │ 「split 项在陈述中按 HOL 展开形重复」；`aq1_split1Nodup` 同款）。
  └────────────────────────────────────────────────────────────────

  ┌─ 证体（与 HOL :909-:977 / :992-:1050 对照）──────────────────────
  │ 两条 index 引理同构，反证：设 core L f ∈ quotient_list L N 而 core L f ≠ core L r。
  │ 取 r' ∈ N 使 core L r' = core L f，则 r' ≠ r；r' ∈ ntrans 1
  │ （`element_in_ntrans_suc`），f ∈ ntrans 1（`fst/snd_mem_rtran1`）。
  │ 状态 1 的 marked_list（AQIUNPP 槽）经 `marked_list_good_quotient` +
  │ `good_list_uniq` 给 uniq (quotient_list L (ntrans 1))，即 core 在 ntrans 1 上
  │ 单射 ⇒ r' = f。normal_list (ntrans 1) 经 `uniq_flatten` 给 uniq (ntrans 1)，
  │ 而 ntrans 1 = replace r [f2] N ++ [f1]：
  │ · index1：f1 = r' 由 `MEM3_replace` 落进 replace 段，又是尾元 ⇒ 重复；
  │ · index2：f2 = r' ∈ N 且 ≠ r ⇒ `not_uniq_replace` 给 replace 段不 uniq。
  │ HOL 取「core 单射」的方式是 `indexl_core` 两次 + `index_uniq`；Lean 用
  │ `List.inj_on_of_nodup_map`，内容相同（都只吃 uniq (quotient_list (ntrans 1))）。
  │ HOL index1 证体里另算的 LAST / EL / sizel 三条（:912-:929），按我对脚本的阅读
  │ 后文未消费；Lean 证体不需要它们。
  │ 两件的 `transform_count = k` 前提证体零消费，按原文前提位保留。
  └────────────────────────────────────────────────────────────────

  ┌─ 语义查重记档 ────────────────────────────────────────────────────
  │ 五条小件在 chain 世界按名零命中；spine 有 `ntrans1` / `sndMemRtran1` /
  │ `aq8w2b_fstMemRtran1` / `aq11_elementInNtransSuc`（陈述用 spine 载体）。
  │ 本文件的链层形直接由 `transform_list` 展开证，不经 spine 桥（更短）；
  │ 与 spine 件短名相同者命名空间不同（本文件在 `Kepler.Text.Reduction5`）。
  │ `MEM3_replace` 树内只有各文件私件，本文件落公开形。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5BetwnNil
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction3Thm12
import Kepler.Text.TameSpine.TameList50
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

/-- **HOL `Tame_list.MEM3_replace`**（tame_list.hl:583）：被替换元之外的成员在
`replace` 后仍在。 -/
theorem mem3Replace {α : Type*} [BEq α] [LawfulBEq α] {x f : α} (xs : List α)
    {g : List α} (hne : x ≠ f) (hx : x ∈ g) : x ∈ Kepler.Graphs.replace f xs g := by
  induction g with
  | nil => exact absurd hx List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzf : z = f
    · rw [if_pos (by rw [hzf]; exact beq_self_eq_true f)]
      rcases List.mem_cons.mp hx with h | h
      · exact absurd (h.trans hzf) hne
      · exact List.mem_append_right _ h
    · rw [if_neg (by simpa using hzf)]
      rcases List.mem_cons.mp hx with h | h
      · rw [h]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- 被替换元在表中时，替入段的成员都在 `replace` 结果里（`sndMemRtran1` 的私有支件）。 -/
private theorem memReplaceIns {α : Type*} [BEq α] [LawfulBEq α] {f : α} {xs g : List α}
    {y : α} (hf : f ∈ g) (hy : y ∈ xs) : y ∈ Kepler.Graphs.replace f xs g := by
  induction g with
  | nil => exact absurd hf List.not_mem_nil
  | cons z zs ih =>
    rw [Kepler.Graphs.replace]
    by_cases hzf : z = f
    · rw [if_pos (by rw [hzf]; exact beq_self_eq_true f)]
      exact List.mem_append_left _ hy
    · rw [if_neg (by simpa using hzf)]
      rcases List.mem_cons.mp hf with h | h
      · exact absurd h.symm hzf
      · exact List.mem_cons_of_mem _ (ih h)

/-- **HOL `Reduction2.ntrans1`**（reduction2.hl:1487）：非 final 时一步 `ntrans` 的
展开形。 -/
theorem ntrans1 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
    (hnf : ¬ finalList L r) :
    ntrans L N r x 1 =
      Kepler.Graphs.replace r
        [(splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
          (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2] N ++
        [(splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
          (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1] := by
  simp [ntrans, transformList, hnf]

/-- **HOL `Aq8.fst_mem_rtran1`**（AQ8.hl:1357）：split 的 FST 片落 ntrans 1。 -/
theorem fstMemRtran1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1 ∈ ntrans L N r x 1 := by
  rw [ntrans1 L N r x hnf]
  exact List.mem_append_right _ List.mem_cons_self

/-- **HOL `Aq8.snd_mem_rtran1`**（AQ8.hl:48）：split 的 SND 片落 ntrans 1。 -/
theorem sndMemRtran1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2 ∈ ntrans L N r x 1 := by
  rw [ntrans1 L N r x hnf]
  exact List.mem_append_left _ (memReplaceIns hm.2.2.1 List.mem_cons_self)

/-- **HOL `Aq9.element_in_ntrans_suc`**（AQ9.hl:1031）：N 中 r 以外的面一步后仍在。 -/
theorem elementInNtransSuc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) {f1 : List Dart} (hf1 : f1 ∈ N) (hne : f1 ≠ r) :
    f1 ∈ ntrans L N r x 1 := by
  by_cases hnf : finalList L r
  · have h : ntrans L N r x 1 = N := by simp [ntrans, transformList, hnf]
    rw [h]
    exact hf1
  · rw [ntrans1 L N r x hnf]
    exact List.mem_append_left _ (mem3Replace _ hne hf1)

/-- 状态 1 上 `core` 单射与 `ntrans 1` 无重复（两条 index 引理的公共私有支件）：
uniq (quotient_list L (ntrans 1)) 与 uniq (ntrans 1)。 -/
private theorem ntrans1Uniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) :
    ((ntrans L N r x 1).map (core L)).Nodup ∧ (ntrans L N r x 1).Nodup := by
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
  have hq : (quotientList L (ntrans L N r x 1)).Nodup :=
    Kepler.Text.TameSpine.goodListUniq _
      (Kepler.Text.Reduction3.t12_marked_list_good_quotient L hL hgn _ _ x hm1 hres)
  rw [Kepler.Text.MoreLemma2Island1.quotientListCore] at hq
  exact ⟨hq, Kepler.Text.TameSpine.uniqFlatten hm1.2.1.1 hm1.2.1.2.1⟩

/-- **HOL `split_normal_list_index1_lemma`**（reduction4.hl:896）：split 的 FST 片
的 core 若已在 quotient_list L N 中，则只能是 core L r。 -/
theorem splitNormalListIndex1Lemma (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).1 ∈ quotientList L N →
      core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).1 = core L r := by
  intro hmem
  by_contra hcne
  -- l'y / l'z 形（HOL `Reduction2.trans0`；定义级）与换面（`find_face_x_eq_y`）
  have hface : findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
    findFaceXEqY L hL hgn hm hnf
  obtain ⟨f1, hf1⟩ : ∃ f1, (splitNormalList L r (findFaceDarts L x)
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1 = f1 := ⟨_, rfl⟩
  have hmem' : core L f1 ∈ quotientList L N := by rw [← hf1]; exact hmem
  have hcne' : core L f1 ≠ core L r := by rw [← hf1]; exact hcne
  -- r' ∈ N，core L r' = core L f1，r' ≠ r
  rw [Kepler.Text.MoreLemma2Island1.quotientListCore] at hmem'
  obtain ⟨r', hr'N, hr'c⟩ := List.mem_map.mp hmem'
  have hr'ne : r' ≠ r := fun h => hcne' (by rw [← hr'c, h])
  -- 两者都在 ntrans 1，core 单射 ⇒ r' = f1
  have hr'1 : r' ∈ ntrans L N r x 1 := elementInNtransSuc L hL hgn hm hr'N hr'ne
  have hf1mem : f1 ∈ ntrans L N r x 1 := by
    have h := fstMemRtran1 L hL hgn hm hnf
    rw [hface, hf1] at h
    exact h
  obtain ⟨hinj, hnd⟩ := ntrans1Uniq L hL hgn hres haq hm
  have hrf : r' = f1 := List.inj_on_of_nodup_map hinj hr'1 hf1mem hr'c
  -- ntrans 1 = replace r [f2] N ++ [f1]：r' 在 replace 段，f1 是尾元，重复
  rw [ntrans1 L N r x hnf, hface, hf1] at hnd
  have hdisj := (List.nodup_append.mp hnd).2.2
  exact hdisj r' (mem3Replace _ hr'ne hr'N) f1 List.mem_cons_self hrf

/-- **HOL `split_normal_list_index2_lemma`**（reduction4.hl:979）：split 的 SND 片
的 core 若已在 quotient_list L N 中，则只能是 core L r。 -/
theorem splitNormalListIndex2Lemma (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).2 ∈ quotientList L N →
      core L (splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))).2 = core L r := by
  intro hmem
  by_contra hcne
  have hface : findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
    findFaceXEqY L hL hgn hm hnf
  obtain ⟨f2, hf2⟩ : ∃ f2, (splitNormalList L r (findFaceDarts L x)
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2 = f2 := ⟨_, rfl⟩
  have hmem' : core L f2 ∈ quotientList L N := by rw [← hf2]; exact hmem
  have hcne' : core L f2 ≠ core L r := by rw [← hf2]; exact hcne
  rw [Kepler.Text.MoreLemma2Island1.quotientListCore] at hmem'
  obtain ⟨r', hr'N, hr'c⟩ := List.mem_map.mp hmem'
  have hr'ne : r' ≠ r := fun h => hcne' (by rw [← hr'c, h])
  have hr'1 : r' ∈ ntrans L N r x 1 := elementInNtransSuc L hL hgn hm hr'N hr'ne
  have hf2mem : f2 ∈ ntrans L N r x 1 := by
    have h := sndMemRtran1 L hL hgn hm hnf
    rw [hface, hf2] at h
    exact h
  obtain ⟨hinj, hnd⟩ := ntrans1Uniq L hL hgn hres haq hm
  have hrf : r' = f2 := List.inj_on_of_nodup_map hinj hr'1 hf2mem hr'c
  -- ntrans 1 = replace r [f2] N ++ [f1]：f2 = r' ∈ N 且 ≠ r ⇒ replace 段不 uniq
  rw [ntrans1 L N r x hnf, hface, hf2] at hnd
  have hrep := (List.nodup_append.mp hnd).1
  exact Kepler.Text.Reduction3.t10b_not_uniq_replace hm.2.2.1 (hrf ▸ hr'N)
    (fun h => hr'ne (hrf.trans h.symm)) hrep

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.mem3Replace
#print axioms Kepler.Text.Reduction5.ntrans1
#print axioms Kepler.Text.Reduction5.fstMemRtran1
#print axioms Kepler.Text.Reduction5.sndMemRtran1
#print axioms Kepler.Text.Reduction5.elementInNtransSuc
#print axioms Kepler.Text.Reduction5.splitNormalListIndex1Lemma
#print axioms Kepler.Text.Reduction5.splitNormalListIndex2Lemma
