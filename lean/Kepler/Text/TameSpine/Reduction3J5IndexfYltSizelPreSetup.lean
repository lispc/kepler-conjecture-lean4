/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreSetup — tame-corr nb19：
  双怪件 `indexf_y_lt_sizel_pre`（more_lemma2:890）的 setup 段（入参/位置事实）。

  ┌─ 归属对账（HOL :890-:928 头部）────────────────────────────────
  │ `transform_count L N r x = k ∧ 0 < k` ⇒
  │ ① 初始状态非 final（`transform_count_not`@0）；
  │ ② zk = ztrans (k-1) ∈ r（`PNXVWFS2`@k-1）；
  │ ③ zk ∈ find_face L x（`ztran_me_f`@k-1，链形 `ztranMeFChain`）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizel
import Kepler.Text.TameSpine.Reduction3J5PowerCoreFace
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList rtrans ntrans ytrans ztrans transformCount)

/-- `transform_count = k > 0` ⇒ 初始状态非 final（HOL `transform_count_not`@0）。 -/
theorem preNotFinal (L : fgraph ℕ) {N : List (List Dart)} {r : List Dart} {x : Dart}
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k) : ¬ finalList L r := by
  have h0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  rw [Kepler.Text.Reduction5.rtrans_zero] at h0
  exact h0

/-- `zk = ztrans (k-1) ∈ r`（HOL `PNXVWFS2`@k-1）。 -/
theorem preZkMemR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k) :
    ztrans L N r x (k - 1) ∈ r :=
  Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq (k - 1)
    (Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)) hm

/-- `zk = ztrans (k-1) ∈ find_face L x`（HOL `ztran_me_f`@k-1，链形）。 -/
theorem preZkMemF (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (_hk : transformCount L N r x = k) (_hk0 : 0 < k) :
    ztrans L N r x (k - 1) ∈ findFaceDarts L x :=
  ztranMeFChain L hL hgn haq hm (k - 1)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.preNotFinal
#print axioms Kepler.Text.TameSpine.preZkMemR
#print axioms Kepler.Text.TameSpine.preZkMemF
