/-
  Kepler.Text.Reduction4Subseg — J 战役 J1 板 B5-A（reduction4.hl 自由件首批）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :1443 `el_cat`        → elCat
  │ :1501 `EL_SUC_CONS`   → elSucCons
  │ :3836 `core_nil`      → coreNil
  │ 后续件（④–⑥）:2746 `mem_ifbetwn` / :2671 `next_el_subseg` / :2138 `indexf_subseg`
  │ 本文件只收 B5-A 六件；依赖全落（`indexf`/`ifbetwn`/`core`/`nextEl` 载体
  │ 在 Reduction5Base/TameLp，成员/代数件在 Reduction4/Reduction4Idx）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；Dart 具体载体。
-/

import Kepler.Text.Reduction4Idx

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart core parts)

/-! ## §1 `EL_SUC_CONS`（reduction4.hl:1501） -/

/-- **HOL `EL_SUC_CONS`**：`EL (SUC i) (h::t) = EL i t`（定义性）。 -/
theorem elSucCons {α : Type*} (i : ℕ) (h : α) (t : List α) (hi : i < t.length) :
    (h :: t)[i + 1]'(by simpa using hi) = t[i]'hi :=
  rfl

/-! ## §2 `el_cat`（reduction4.hl:1443） -/

/-- **HOL `el_cat`**：`EL i (cat a b)` 按 `i < sizel a` 分左右段。 -/
theorem elCat {α : Type*} (i : ℕ) (a b : List α) (hi : i < (a ++ b).length) :
    (a ++ b)[i]'hi = if h : i < a.length then a[i]'h else
      b[i - a.length]'(by rw [List.length_append] at hi; omega) :=
  List.getElem_append (l₁ := a) (l₂ := b) (i := i) hi

/-! ## §3 `core_nil`（reduction4.hl:3836） -/

/-- **HOL `core_nil`**：`core L [] = []`（`parts [] = []` 定义性）。 -/
theorem coreNil (L : fgraph ℕ) : core L [] = [] :=
  rfl

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.elSucCons
#print axioms Kepler.Text.Reduction4Idx.elCat
#print axioms Kepler.Text.Reduction4Idx.coreNil
