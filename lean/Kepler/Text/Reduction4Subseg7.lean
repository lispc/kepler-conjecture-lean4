/-
  Kepler.Text.Reduction4Subseg7 — J 战役 J1 板 F4（reduction4.hl 小件两枚，F 组收尾）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :797 `l_expand`    → l_expand（定义性两合取）
  │ :884 `size_replace1` → size_replace1
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide。
-/

import Kepler.Text.Reduction4Subseg6

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph replace)
open Kepler.Text.Reduction5 (Dart ly lz ntrans rtrans ytrans ztrans)

/-! ## §1 `l_expand`（reduction4.hl:797） -/

/-- **HOL `l_expand`**（reduction4.hl:797）：`l'y L (rtrans … i) x = ytrans … i ∧
l'z L (ntrans … i) (rtrans … i) x = ztrans … i`。

本树 `ytrans`/`ztrans` 的 def body 逐字就是 `ly L (rtrans …) x` /
`lz L (ntrans …) (rtrans …) x`（Reduction5Base:186/191，HOL `l'y`/`l'z` 的直译）
⇒ 两合取都是 **`rfl`**（HOL 证体本身也是空的）。 -/
theorem l_expand (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (i : ℕ) :
    Kepler.Text.Reduction5.ly L (rtrans L N r x i) x = ytrans L N r x i ∧
      Kepler.Text.Reduction5.lz L (ntrans L N r x i) (rtrans L N r x i) x =
        ztrans L N r x i :=
  ⟨rfl, rfl⟩

/-! ## §2 `size_replace1`（reduction4.hl:884） -/

/-- **HOL `size_replace1`**（reduction4.hl:884）：`sizel (replace x [y] s) = sizel s`。

`replace` ↦ `Kepler.Graphs.replace`（ListAux:56，`[BEq α]` 烘焙）；证体对 `s`
归纳，`z == x` 两支分别算长度（命中支替换成 `[y] ++ zs`，长度 1 + |zs|；
未命中支 `z :: replace … zs`，用归纳假设）。 -/
theorem size_replace1 {α : Type*} [BEq α] (s : List α) (x y : α) :
    (replace x [y] s).length = s.length := by
  induction s with
  | nil => rfl
  | cons z zs ih =>
    simp only [replace]
    by_cases h : (z == x) = true
    · rw [if_pos h]
      simp
    · rw [if_neg h, List.length_cons, List.length_cons, ih]

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（本文件编译即执行；预期 ≤ 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4Idx.l_expand
#print axioms Kepler.Text.Reduction4Idx.size_replace1
