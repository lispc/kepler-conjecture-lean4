/-
  Kepler.Text.Reduction5Ml1W2b — 主机 8b W2b 段（HOL More_lemma1.hl :2300–:2450）。

  ┌─ 本波（B1）与冻结表（B2–B6）────────────────────────────────────
  │ B1 `ml1SMem`（:2205）：`y1 ∈ s ∧ z1 ∈ s`（`ml1S` 定义 + 成员）。
  │ B2 `ml1SUniq`（:2226）：`s.Nodup`——需求 `uniqBetwn`（已核
  │   JcajyduBetwnBase:121，泛 α）+ 端点∉between；替代路线：把 s 写成
  │   r 的 take/drop 连续段（`betwnTakeDrop` + `uniqTake/uniqDrop`）。
  │ B3 `ml1Py1`（:2250–:2280）：侦察结论（机器）：HOL 的 parts_fst /
  │   normal_condition_last_parts 以 **N := ntrans L N r x 1、r := cat g s**
  │   应用（state-1 normal_list = `aqs_aqNormalList`（W1a:113，五槽条件形）
  │   + `parts L split.1` 的 aq12w 分解），故 B3 陈述须带 state-1
  │   normalList 槽；py1/pz1 的 LAST/HD 归属链 4–5 步。
  │ B4 `ml1Pz1`（:2280–:2300）：B3 的 MEM_HD 对称。
  │ B5 `ml1SLastNe`（:2300–:2330）：`lastCat`/`nextElCat1/2`
  │   （TameSpine/TameList9:383/199/248，公开）+ `nextCatBetwnSame`。
  │ B6 `ml1IndexOfS`（:2580，W2c）：`LAST_FLATTEN_2` + `indexf_split_*`。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5Ml1W2
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.ChainLists (markedList)

/-- HOL `s = [y1] ++ (betwn r y1 z1 ++ [z1])`（主件 :2147 的 `GABBREV_TAC s`；
`y1 = next_el r y`、`z1 = prev_el r z`、`z = ztrans L N r x 0`）。 -/
noncomputable def ml1S (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : List Dart :=
  [nextEl r (ly L r x)] ++
    (between r (nextEl r (ly L r x)) (prevEl r (ztrans L N r x 0)) ++
      [prevEl r (ztrans L N r x 0)])

/-- **W2b-B1（HOL :2205）**：`s` 的两端成员：`y1 ∈ s ∧ z1 ∈ s`。 -/
theorem ml1SMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    nextEl r (ly L r x) ∈ ml1S L N r x ∧
      prevEl r (ztrans L N r x 0) ∈ ml1S L N r x := by
  unfold ml1S
  constructor
  · simp
  · simp

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1SMem
