/-
  Kepler.Text.Reduction3DefsNewVertex — J 战役 J3 定义层 D3a（newvertex 族）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │   rotate_to        tame_defs.hl:346-347   → §A rotateTo（链岛重落）
  │   newvertex        tame_defs2.hl:702-706  → §B newvertex
  │   newvertex_prepped tame_defs2.hl:708-713 → §B newvertexPrepped
  │ 定义即引理（2 条）：newvertexPreppedOfFinal / rotateToNil。
  │ 消费锚：reduction3.hl assumption_set3:1823 / assumption_setK10:3565
  │ （newvertex_prepped 为合取原子）；reduction2.hl:1042
  │ elements_of_list_ntrans 的 LEBHIRJ 证词链也消费它（J2 批 F）。
  └────────────────────────────────────────────────────────────────

  ┌─ rotate_to 载体裁决（链岛 vs Spine 岛）────────────────────────
  │ `rotate_to` 的树内既有落点 = TameSpine 岛 `TameList54.rotateTo`
  │ （HOL tame_defs.hl:346）。本链岛**不跨岛引用**（Reduction5Base
  │ 头注：TameSpine 经 TameList1→Assembly 传递成环；j1w1-B3 对
  │ rotate 族同判「链岛重落」）。故此处按 tame_defs.hl:346-347 逐字
  │ 重落：`rotate_to vs v = v :: (snd (split_at v vs) ++ fst (split_at
  │ v vs))`，split_at ↦ `Kepler.Graphs.splitAt`（ListAux.lean:22，
  │ 同「首个出现处分割、post 不含 c」约定，语义逐字对齐）。
  │ 与 TameList54 的关系：同源双载体（与 W0/Spine 双 transform 塔
  │ 同制式），J3 装配层择一消费；本岛内以本件为准。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.Reduction3Defs`（D1）。闭包零
  │ `Kepler.Assembly` 主模块、零 TameSpine。零 axiom/sorry/admit/
  │ native_decide。`filter` 的 `~MEM d r` ↦ `decide (d ∉ r)`
  │ （D1/D2 同制式）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (findFaceDarts)
open Kepler.Graphs (splitAt splitAtRec fgraph)
open Kepler.Text.Reduction5 (Dart finalList)

/-! ## §A `rotate_to`（链岛重落，tame_defs.hl:346-347）

HOL：`rotate_to vs v = v :: (APPEND (SND (split_at v vs)) (FST (split_at v vs)))`。
即把 `vs` 在 `v` 处切开后以 `v` 开头重生。`v ∉ vs` 时 split_at 返回
`(vs, [])`（HOL/Lean 同约定），退化为 `v :: vs`——junk 支两库一致。 -/

/-- HOL `rotate_to`（tame_defs.hl:346-347）。 -/
def rotateTo {α : Type} [BEq α] (vs : List α) (v : α) : List α :=
  v :: (splitAt v vs).2 ++ (splitAt v vs).1

/-- 定义即引理①：空表上 `rotate_to` 退化为单元素表（junk 支，
`split_at v [] = ([], [])`；下游 `newvertex` 的空面情形的展开件）。 -/
theorem rotateToNil {α : Type} [BEq α] (v : α) : rotateTo [] v = [v] := by
  simp [rotateTo, splitAt, splitAtRec]

/-! ## §B `newvertex` / `newvertex_prepped`（tame_defs2.hl:702-713）

`newvertex L r x`：`find_face L x` 旋转到 `x` 开头后，滤掉已在 `r` 中
的 dart，投影为顶点表（即「x 处新插入的顶点序列」）。
`newvertex_prepped L N r x`：要么面已 final（无需预备），要么新顶点表
恰为从 `n = #(undup (FST∘flatten N))` 起的连续段 `iota n (sizel news)`
（HOL `iota m (SUC n)` 递归，Lean `List.range' m n`）。 -/

/-- HOL `newvertex`（tame_defs2.hl:702-706）。 -/
def newvertex (L : fgraph ℕ) (r : List Dart) (x : Dart) : List ℕ :=
  let f := findFaceDarts L x
  let f' := rotateTo f x
  (f'.filter (fun d => decide (d ∉ r))).map (fun d => d.1)

/-- HOL `newvertex_prepped`（tame_defs2.hl:708-713）。陈述槽（Prop 形，
零证明义务）。 -/
def newvertexPrepped (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : Prop :=
  finalList L r ∨
    let n := ((N.flatten.map (fun d => d.1)).dedup).length
    let news := newvertex L r x
    news = List.range' n news.length

/-- 定义即引理②：`final_list L r` 支直接给出 `newvertex_prepped`
（HOL :710 第一析取；reduction3 各消费点的 final 分支即用它）。 -/
theorem newvertexPreppedOfFinal (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (h : finalList L r) :
    newvertexPrepped L N r x := Or.inl h

end Kepler.Text.Reduction3

-- 公理探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.rotateToNil
#print axioms Kepler.Text.Reduction3.newvertexPreppedOfFinal
#check @Kepler.Text.Reduction3.rotateTo
#check @Kepler.Text.Reduction3.newvertex
#check @Kepler.Text.Reduction3.newvertexPrepped
