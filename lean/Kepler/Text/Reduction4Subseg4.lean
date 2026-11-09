/-
  Kepler.Text.Reduction4Subseg4 — J 战役 J1 板 F 组（reduction4.hl core 成员链 2 件）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :474 `final_assumption_mem_fst_core` → finalAssumptionMemFstCore
  │ :506 `mem_fst_core`（前者的一行推论） → memFstCore
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与导入纪律 ──────────────────────────────────────────────
  │ `core` ↦ `Kepler.Text.Reduction5.core`（Reduction5Base:88，
  │   `(parts L r).map (fun l => (l.headD (0,0)).1)`，即 HOL `MAP (FST o HD)`）；
  │ `parts` ↦ `Kepler.Text.Reduction5.parts`；`marked_list` ↦
  │   `Kepler.Text.ChainLists.markedList`（ChainListsL2:118，`(hL : GoodList L)`
  │   为载体前提 = DIFFERS-①，与 normalList/GoodListNodesTl 同形）。
  │ 上游三件全部已落且公开：
  │   `MoreLemma2Island2.partsFlatten`(:143)、`MoreLemma2PartsFst.partsFst`(:381)、
  │   `MoreLemma2Island1.uniqFlattenUniq`(:97)。
  │ 环安全：`MoreLemma2PartsFst` 的 Kepler.* 闭包实测 144 个模块，其中
  │ `Kepler.Assembly.*` **只有 `GoodListDefs` 一个叶**（非 Assembly 主模块），
  │ **零 `Kepler.Text.TameSpine.*`**；本文件新增的 `MoreLemma2Island1`
  │ （import Reduction5Base + Reduction4）与 `ChainListsL2`
  │ （import ChainListsL1）均在该闭包内或同层，不引入新 Assembly 面。
  │ 零 axiom/sorry/admit/native_decide；泛型/具体载体：`Dart = ℕ × ℕ`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.ChainListsL2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.Reduction5 (Dart parts core)
open Kepler.Text.ChainLists (markedList normalList)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil)
open Kepler.Text.MoreLemma2PartsFst (partsFst)
open Kepler.Text.MoreLemma2Island1 (uniqFlattenUniq)

/-! ## §0 私有桥：`headD d ≡ head!`（非空表，任意缺省元）

`head!` 与 `headD` 都按构造子归约；对**变量** `l` 二者都卡住，故 `(l.headD d)`
与 `l.head!` 只在 `l = a :: t` 后 defeq。本件只需这一层。 -/

private theorem headD_eq_head! {α : Type*} [Inhabited α] {l : List α} (h : l ≠ [])
    (d : α) : l.headD d = l.head! := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-! ## §1 `final_assumption_mem_fst_core`（reduction4.hl:474） -/

/-- **HOL `final_assumption_mem_fst_core`**（reduction4.hl:474）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x
 ⇒ ∀ u, MEM u r ⇒ MEM (FST u) (core L r)`。

Lean 侧前提 = `GoodList L`（载体，HOL `good_list ∧ good_list_nodes` 的打包形态，
同 ChainListsL2 的 DIFFERS-①）+ `markedList L hL N r x`。

路线（与 HOL :481-:505 逐段同构）：
1. `markedList` 合取 2 = `normalList` ⇒ `N.flatten.Nodup`（合取 1）与
   `r ≠ []`（合取 2，`r ∈ N` 由 markedList 合取 3 供给）；
2. `N.flatten.Nodup` + `r ∈ N` ⇒ `r.Nodup`（`uniqFlattenUniq`）；
3. `partsFlatten` 把 `u ∈ r` 搬成 `u ∈ (parts L r).flatten`，`List.mem_flatten`
   拆出 `p ∈ parts L r` 且 `u ∈ p`；
4. `partsFst` 给 `u.1 = p.head!.1`，而 `core = (parts L r).map (·.headD (0,0)).1`，
   `List.mem_map` 收口（`head! ≡ headD (0,0)`，`Dart` 的 `Inhabited` 缺省即 `(0,0)`）。 -/
theorem finalAssumptionMemFstCore (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) :
    ∀ u ∈ r, u.1 ∈ core L r := by
  intro u hu
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hnd : r.Nodup := uniqFlattenUniq hN.1 hrN
  have hne : r ≠ [] := hN.2.1 r hrN
  have hfl : u ∈ (parts L r).flatten := by
    rw [partsFlatten L hnd hne]
    exact hu
  obtain ⟨p, hp, hup⟩ := List.mem_flatten.mp hfl
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  refine List.mem_map.mpr ⟨p, hp, ?_⟩
  rw [headD_eq_head! hpne (0, 0)]
  exact (partsFst L hL hN hrN hp hup).symm

/-! ## §2 `mem_fst_core`（reduction4.hl:506） -/

/-- **HOL `mem_fst_core`**（reduction4.hl:506）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ MEM u r
 ⇒ MEM (FST u) (core L r)`。

HOL 证体就是 `ASM_MESON_TAC[final_assumption_mem_fst_core]` 一行；本件取
显式成员形（`(hu : u ∈ r)`，结论直接给成员），证体为上一件的直接调用。 -/
theorem memFstCore (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x u : Dart}
    (hm : markedList L hL N r x) (hu : u ∈ r) : u.1 ∈ core L r :=
  finalAssumptionMemFstCore L hL hm u hu

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore
#print axioms Kepler.Text.Reduction4Idx.memFstCore
