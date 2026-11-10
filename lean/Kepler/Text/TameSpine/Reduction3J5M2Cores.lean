/-
  Kepler.Text.TameSpine.Reduction3J5M2Cores — tame-corr nb11：J5-5 波 1
  的核件（`LAST_FLATTEN_2` / `MEM_LAST` / `next_el_MEM_map` 的 Lean 形）。

  ┌─ 归属对账（HOL → Lean）─────────────────────────────────────
  │ ① `memLastBang`（HOL `Tame_list.MEM_LAST`，tame_list.hl:1364）：
  │    `s ≠ [] ⇒ MEM (LAST s) s`（getLast! 形；结构递归 + 定义级
  │    cons-cons 折叠）。探针仅 [propext]（零 choice/Quot）。
  │ ② `nextElMapOfMem`（HOL `Tame_list.next_el_MEM_map`，tame_list.hl:1011）：
  │    `uniq y ∧ MEM d y ∧ (∀ u v ∈ y, f u = f v → u = v) ⇒
  │    next_el (MAP f y) (f d) = f (next_el y d)`。
  │    **查重命中**：`TameLp.la7_nextEl_map`（:5571，同陈述 cm 形——
  │    免 uniq；实例面 [BEq α][LawfulBEq α][DecidableEq α]）；本件是 HOL
  │    前提逐字形包装（一行）。
  │ ③ **查重命中（不重落）**：`LAST_FLATTEN_2`（AQ23.hl:221）——
  │    `MoreLemma2Naming.lastFlatten2`（:68）与
  │    `JcajyduBetwnBase.lastFlatten2`（:172）双份在库，本笔先行误落、
  │    编译报 already declared 后删件转记账（本文件无此件）。
  │ ④ **未落（预算到点）**：`is_restricted_e_list_nondeg`（tame_list:4371）/
  │    `edge_nondeg_f_xor_ni`（:4933）——两件是 Hypermap 核
  │    （`EdgeNondegenerate` 与 `face_map`/`inverse node_map` 的对应），
  │    需先把 `is_edge_nondegenerate` 的 Lean 形（Hypermap.lean:1070
  │    `EdgeNondegenerate := ∀ x ∈ darts, edgeMap x ≠ x`）与
  │    `eList`/`fList` 的桥（`edgeMap = eList` 面、`face_map_list` 面）
  │    对清；`condition_last_parts` 查重命中
  │    `aqs_conditionLastParts`（JcajyduAqLeaf12T:181，陈述逐字），零新落。
  │ ⑤ **`next_core_FST`（more_lemma2:221）未落**：依赖 ① ②（在库）+ ④
  │    两件（缺）+ 已核对在库 parts 机器——见 DELIVERY §2 的逐件表。
  └────────────────────────────────────────────────────────────────
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameLp

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **HOL `Tame_list.MEM_LAST`**（tame_list.hl:1364）：`s ≠ [] ⇒ MEM (LAST s) s`
（getLast! 形）。 -/
theorem memLastBang {α : Type} [Inhabited α] (s : List α) (hne : s ≠ []) :
    s.getLast! ∈ s := by
  induction s with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => exact List.mem_singleton.mpr rfl
    | cons b u =>
      exact List.mem_cons_of_mem _ (ih (List.cons_ne_nil b u))

/-- **HOL `Tame_list.next_el_MEM_map`**（tame_list.hl:1011，HOL 前提逐字形）：
`uniq y ∧ MEM d y ∧ (∀ u v ∈ y, f u = f v → u = v) ⇒
next_el (MAP f y) (f d) = f (next_el y d)`。
查重命中 `TameLp.la7_nextEl_map`（:5571）直投。 -/
theorem nextElMapOfMem {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] [BEq β]
    [LawfulBEq β] {f : α → β}
    {y : List α} {d : α} (_hy : y.Nodup) (hd : d ∈ y)
    (hinj : ∀ u ∈ y, ∀ v ∈ y, f u = f v → u = v) :
    nextEl (y.map f) (f d) = f (nextEl y d) :=
  Kepler.Text.TameLp.la7_nextEl_map hinj hd

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.memLastBang
#print axioms Kepler.Text.TameSpine.nextElMapOfMem
