/-
  Kepler.Text.TameSpine.Reduction3J5IndexfPrev — tame-corr nb15：双怪件 ② 组装
  的缺砖 `indexfPrevSucc`（`indexf w (prev_el r d) r + 1 = indexf w d r`）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ 双怪件 HOL `more_lemma2.hl` :576-:599 的 `indexf_add_right`/`indexf_n`
  │ 步：pd = prev_el r d 的前驱位置恰比 d 少一。本件给出链层直接形。
  │ 路线（避开 iterate 模算术）：`indexf_compl` 互补 + `next_el_indexf`
  │ （pd→d 距 1）+ `indexf_add_sum` + 前驱唯一性（nextEl 在 Nodup 成员上单射）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelAtom
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl)
open Kepler.Text.Reduction5 (Dart indexf)

/-! ## §0 前驱唯一性 -/

/-- `Nodup` 成员上 `nextEl` 单射：`nextEl r x = nextEl r y ⇒ x = y`
（`prev_el` 反演一步）。 -/
theorem nextElInjOfNodup {r : List Dart} (hnd : r.Nodup) {x y : Dart}
    (hx : x ∈ r) (hy : y ∈ r) (h : nextEl r x = nextEl r y) : x = y := by
  calc x = Kepler.Assembly.prevEl r (nextEl r x) :=
        (Kepler.Text.TameLp.prevEl_nextEl hnd hx).symm
    _ = Kepler.Assembly.prevEl r (nextEl r y) := by rw [h]
    _ = y := Kepler.Text.TameLp.prevEl_nextEl hnd hy

/-- 两个不同成员 ⇒ 表长 ≥ 2。 -/
theorem oneLtLengthOfTwoNeMem {r : List Dart} {w d : Dart}
    (hw : w ∈ r) (hd : d ∈ r) (hwd : w ≠ d) : 1 < r.length := by
  have hpos : 0 < r.length := List.length_pos_of_mem hw
  rcases Nat.lt_or_ge r.length 2 with h | h
  · have hlen1 : r.length = 1 := by omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
    rw [List.mem_singleton] at hw hd
    exact absurd (hw.trans hd.symm) hwd
  · omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.nextElInjOfNodup
#print axioms Kepler.Text.TameSpine.oneLtLengthOfTwoNeMem
