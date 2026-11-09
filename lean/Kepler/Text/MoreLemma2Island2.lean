/-
  Kepler.Text.MoreLemma2Island2 — J 战役 J1（M0e 批第二片）：
  37 件 Island-only 重落清单中 **Tame_list 簇的 parts 组**（链岛重落）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ 本片 4 件（HOL 行号 ↔ Spine 现名 ↔ 本文件 Lean 名）：
  │   :6334 `parts_flatten`      partsFlatten     (TameList9:1063)  → partsFlatten
  │   :6357 `parts_all_nonnil`   partsAllNonnil   (TameList9:1227)  → partsAllNonnil
  │   :6533 `parts_nonnil`       partsNonnil      (TameList9:1267)  → partsNonnil
  │   :6809 `uniq_parts`         uniqParts        (TameList10:541)  → uniqParts
  │ 载体：`parts L r = partitionIntoAtom ((f_list L) o e_list) r`
  │ （Reduction5Base:75/83，定义体逐句对齐 tame_defs2.hl:111-127）。
  └────────────────────────────────────────────────────────────────

  ┌─ 实现路线（与 Spine 岛不同：不用 partsSpine 自定义归纳机）────────
  │ 链世界 `partitionIntoAtom0 n acc r` 是直接结构递归，故三个不变量
  │ （flatten 重建序 / acc 非空保持 / atom 非空保持）都以 `r` 的结构
  │ 归纳直证，Spine 岛 partsPure/sizeInduct/partsCat/partsCases/
  │ partsInductLemma（TameList9:676-1045，≈200-350 行）在本片不需要。
  │ 勘误：HOL `parts_flatten` 带 `uniq r /\ ~(r=[])` 前提，实际证体两条
  │ 前提全程未用（链世界递归定义更强）——hips 逐字保留（陈述不改），
  │ 另记档。
  └────────────────────────────────────────────────────────────────

  ┌─ 本片之外的 parts 件（停报，详见 DELIVERY-M0e）──────────────
  │ :6490 `next_el_parts_unlast`（next_el 跨 atom 邻接机制，需
  │   partsCases/partsCat 级机器，独立片评估）；
  │ :6572 `parts_uniq_nonnil` / :6687 `parts_fst`（normal_list 门槛，
  │   等 L1）；:6522 `quotient_all_uniq`（marked_list，等 L2）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；泛型 binder 零实例
  （本片除 fgraph ℕ 载体外均无类型类）；import 闭包零 TameSpine/Assembly 主模块。
-/

import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2Island2

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts partitionIntoAtom partitionIntoAtom0)
open Kepler.Assembly (fList eList)

/-! ## §1 `partitionIntoAtom0` 三个不变量（私有；对 `r` 结构归纳）

HOL 侧对应 machinery：tame_defs2.hl `partition_into_atom0` 的
`list_RECURSION` 归纳 + Spine 岛 partsInductLemma。链世界定义直接可归纳。 -/

/-- 不变量 ①：扫描重建序 —— `flatten (pia0 n acc r) = r.reverse ++ acc.flatten`。 -/
private theorem flatten_pia0 {n : Dart → Dart} :
    ∀ (r : List Dart) (acc : List (List Dart)),
      (partitionIntoAtom0 n acc r).flatten = r.reverse ++ acc.flatten := by
  intro r
  induction r with
  | nil => intro acc; simp [partitionIntoAtom0]
  | cons r0 rs ih =>
    intro acc
    cases acc with
    | nil =>
      simp only [partitionIntoAtom0]
      rw [ih [[r0]]]
      simp
    | cons a acc' =>
      simp only [partitionIntoAtom0]
      split_ifs with h
      · rw [ih ((r0 :: a) :: acc')]
        simp
      · rw [ih ([r0] :: a :: acc')]
        simp

/-- 不变量 ②：非空保持 —— `acc ≠ [] ⇒ pia0 n acc r ≠ []`。 -/
private theorem pia0_ne_nil {n : Dart → Dart} :
    ∀ (r : List Dart) (acc : List (List Dart)),
      acc ≠ [] → partitionIntoAtom0 n acc r ≠ [] := by
  intro r
  induction r with
  | nil => intro acc hacc; simpa [partitionIntoAtom0] using hacc
  | cons r0 rs ih =>
    intro acc hacc
    cases acc with
    | nil =>
      simp only [partitionIntoAtom0]
      exact ih [[r0]] (List.cons_ne_nil _ _)
    | cons a acc' =>
      simp only [partitionIntoAtom0]
      split_ifs with h
      · exact ih ((r0 :: a) :: acc') (List.cons_ne_nil _ _)
      · exact ih ([r0] :: a :: acc') (List.cons_ne_nil _ _)

/-- 不变量 ② 的导出形：空 acc 从非空输入起扫，结果非空。 -/
private theorem pia0_cons_ne {n : Dart → Dart} (r0 : Dart) (rs : List Dart) :
    partitionIntoAtom0 n [] (r0 :: rs) ≠ [] := by
  simp only [partitionIntoAtom0]
  exact pia0_ne_nil rs [[r0]] (List.cons_ne_nil _ _)

/-- 不变量 ③：atom 非空保持 —— acc 的 atom 都非空 ⇒ 结果的 atom 都非空。 -/
private theorem pia0_all_nonnil {n : Dart → Dart} :
    ∀ (r : List Dart) (acc : List (List Dart)), (∀ a ∈ acc, a ≠ []) →
      ∀ a ∈ partitionIntoAtom0 n acc r, a ≠ [] := by
  intro r
  induction r with
  | nil =>
    intro acc hacc a ha
    rw [partitionIntoAtom0] at ha
    exact hacc a ha
  | cons r0 rs ih =>
    intro acc hacc
    cases acc with
    | nil =>
      simp only [partitionIntoAtom0]
      exact ih [[r0]] (by
        intro a ha
        rw [List.mem_singleton] at ha
        subst ha
        exact List.cons_ne_nil _ _)
    | cons a acc' =>
      simp only [partitionIntoAtom0]
      split_ifs with h
      · exact ih ((r0 :: a) :: acc') (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact List.cons_ne_nil _ _
          · exact hacc x (List.mem_cons_of_mem _ hx'))
      · exact ih ([r0] :: a :: acc') (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact List.cons_ne_nil _ _
          · exact hacc x hx')

/-! ## §2 parts 簇四件 -/

/-- **HOL `parts_flatten`**（tame_list.hl:6334
`uniq r /\ ~(r = []) ==> flatten (parts L r) = r`）。
Spine 现名 `partsFlatten`（TameList9:1063，走 partsInductLemma 机器）。
链岛证体：`parts = pia0 ((f_list L) o e_list) [] r.reverse` +
不变量 ① 一步收口（`(r.reverse).reverse = r`、`[].flatten = []`）。
勘误：`uniq`/非空前提在链世界定义下全程未用，陈述逐字保留。 -/
theorem partsFlatten (L : fgraph ℕ) {r : List Dart} (hnd : r.Nodup) (hne : r ≠ []) :
    (parts L r).flatten = r := by
  unfold parts partitionIntoAtom
  rw [flatten_pia0]
  simp

/-- **HOL `parts_all_nonnil`**（tame_list.hl:6357 `all (\p. ~(p = [])) (parts L r)`）。
Spine 现名 `partsAllNonnil`（TameList9:1227）。
链岛证体：不变量 ③（空 acc 左前提 `simp`）。 -/
theorem partsAllNonnil (L : fgraph ℕ) (r : List Dart) :
    ∀ p ∈ parts L r, p ≠ [] := by
  unfold parts partitionIntoAtom
  exact pia0_all_nonnil (n := fun d => fList L (eList d)) r.reverse []
    (by simp)

/-- **HOL `parts_nonnil`**（tame_list.hl:6533 `~(r = []) ==> ~(parts L r = [])`）。
Spine 现名 `partsNonnil`（TameList9:1267）。
链岛证体：`r.reverse ≠ []` 后按 reverse 的 cons 形走不变量 ②。 -/
theorem partsNonnil (L : fgraph ℕ) {r : List Dart} (hne : r ≠ []) :
    parts L r ≠ [] := by
  unfold parts partitionIntoAtom
  cases hrv : r.reverse with
  | nil => exact absurd hrv (by rw [List.reverse_eq_nil_iff]; exact hne)
  | cons r0 rs => exact pia0_cons_ne r0 rs

/-- **HOL `uniq_parts`**（tame_list.hl:6809
`uniq r /\ ~(r = []) ==> uniq (parts L r)`）。
Spine 现名 `uniqParts`（TameList10:541）。
链岛证体：`parts_flatten` 把 `r.Nodup` 转成 `(parts L r).flatten.Nodup`，
`List.nodup_flatten` 给出 **Pairwise Disjoint**；若两 atom 相同则
`Disjoint a a` 而 `a` 非空（`parts_all_nonnil`），取 `a.headD` 即矛盾；
`nodup_iff_injective_getElem` 收口。 -/
theorem uniqParts (L : fgraph ℕ) {r : List Dart} (hnd : r.Nodup) (hne : r ≠ []) :
    (parts L r).Nodup := by
  have hflat : (parts L r).flatten.Nodup := by
    rw [partsFlatten L hnd hne]
    exact hnd
  have hdisj : (parts L r).Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hflat).2
  have hall : ∀ p ∈ parts L r, p ≠ [] := partsAllNonnil L r
  have hhead : ∀ p ∈ parts L r, p.headD (0, 0) ∈ p := by
    intro p hp
    cases p with
    | nil => exact absurd rfl (hall [] hp)
    | cons b t => simp
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  change (parts L r)[(i : ℕ)] = (parts L r)[(j : ℕ)] at hij
  by_contra hne'
  have hval : (i : ℕ) ≠ (j : ℕ) := fun heq => hne' (Fin.ext heq)
  have hi : (i : ℕ) < (parts L r).length := i.2
  have hj : (j : ℕ) < (parts L r).length := j.2
  have hmem : ((parts L r)[(i : ℕ)]) ≠ [] := hall _ (List.getElem_mem hi)
  have hh : ((parts L r)[(i : ℕ)]).headD (0, 0) ∈ (parts L r)[(i : ℕ)] :=
    hhead _ (List.getElem_mem hi)
  have hd : List.Disjoint ((parts L r)[(i : ℕ)]) ((parts L r)[(i : ℕ)]) := by
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · have h := (List.pairwise_iff_getElem.mp hdisj) (i : ℕ) (j : ℕ) hi hj hlt
      rw [← hij] at h
      exact h
    · have h := (List.pairwise_iff_getElem.mp hdisj) (j : ℕ) (i : ℕ) hj hi hgt
      rw [← hij] at h
      exact h
  exact hd hh hh

end Kepler.Text.MoreLemma2Island2

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2Island2.partsFlatten
#print axioms Kepler.Text.MoreLemma2Island2.partsAllNonnil
#print axioms Kepler.Text.MoreLemma2Island2.partsNonnil
#print axioms Kepler.Text.MoreLemma2Island2.uniqParts
