/-
  Kepler.Text.TameSpine.Reduction3J5IndexfPrevSucc — tame-corr nb16：双怪件 ② 组装
  的缺砖 `indexfPrevSucc`（`Kepler.Text.Reduction5.indexf w (prev_el r d) r + 1 = Kepler.Text.Reduction5.indexf w d r`）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ 双怪件 HOL `more_lemma2.hl` :576-:599 的 `indexf_add_right`/`indexf_n` 步。
  │ nb15 判 BLOCKED 的 BEq 世界分裂由**在库** `Reduction5.nextElInstEq`
  │ （`@nextEl Dart instBEqProd = @nextEl Dart instBEqOfDecidableEq`）解除：
  │ 引擎（`nextElIndexf`/`indexfN`）前先把 `nextEl` 桥到派生世界。
  │ 路线 = `indexf_compl` 互补 + `next_el_indexf`（pd→d 距 1）+
  │ `indexf_add_sum`；f = 1 的退化支用 nb15 绿件 `nextElInjOfNodup`
  │ 得 pd = w（e = 0）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfPrevPartial
import Kepler.Text.Reduction5Kbwpbhq
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

/-- **双怪件缺砖**：`nextEl r pd = d` 时
`Kepler.Text.Reduction5.indexf w pd r + 1 = Kepler.Text.Reduction5.indexf w d r`。 -/
theorem indexfPrevSucc {r : List Dart} {w pd d : Dart}
    (hw : w ∈ r) (hpd : pd ∈ r) (hnd : r.Nodup) (hwd : w ≠ d)
    (hnext : nextEl r pd = d)
    (hlt : Kepler.Text.Reduction5.indexf w d r < r.length) :
    Kepler.Text.Reduction5.indexf w pd r + 1
      = Kepler.Text.Reduction5.indexf w d r := by
  have hd : d ∈ r := by rw [← hnext]; exact Kepler.Text.TameLp.nextEl_mem_of_mem hpd
  have h1len : 1 < r.length := oneLtLengthOfTwoNeMem hw hd hwd
  -- BEq 桥：把 `nextEl` 从 prod 世界桥到派生世界（引擎的世界）
  have hnextD : @nextEl Dart instBEqOfDecidableEq r pd = d := by
    rw [← Kepler.Text.Reduction5.nextElInstEq]
    exact hnext
  have hpd1 : Kepler.Text.Reduction5.indexf pd d r = 1 :=
    Kepler.Text.MoreLemma2Island1.nextElIndexf hpd hd hnd hnextD h1len
  by_cases hf1 : Kepler.Text.Reduction5.indexf w d r = 1
  · -- f = 1：d = nextEl w，前驱唯一性给 pd = w，故 e = 0
    have hidx := Kepler.Text.MoreLemma2Island1.indexfN hw hd hnd
    rw [hf1, Function.iterate_one] at hidx
    have hnextw : @nextEl Dart instBEqProd r w = d := by
      rw [Kepler.Text.Reduction5.nextElInstEq]
      exact hidx
    have hpdw : pd = w :=
      nextElInjOfNodup hnd hpd hw (by rw [hnext, hnextw])
    have he0 : Kepler.Text.Reduction5.indexf w pd r = 0 := by
      rw [hpdw]
      exact Kepler.Text.Reduction4.indexfRefl hw
    omega
  · -- f ≠ 1 且 f ≠ 0 ⇒ f ≥ 2：互补 + 加法
    have hfne : Kepler.Text.Reduction5.indexf w d r ≠ 0 := by
      intro h0
      exact hwd (Kepler.Text.Reduction4.indexf_eq_zero hw hd h0)
    by_cases hwpd : w = pd
    · have hf1' : Kepler.Text.Reduction5.indexf w d r = 1 := by
        rw [hwpd]
        exact hpd1
      exact absurd hf1' hf1
    · have hcompl1 : Kepler.Text.Reduction5.indexf w pd r + Kepler.Text.Reduction5.indexf pd w r = r.length :=
        Kepler.Text.Reduction5.indexfCompl hw hpd hwpd
      have hcompl2 : Kepler.Text.Reduction5.indexf w d r + Kepler.Text.Reduction5.indexf d w r = r.length :=
        Kepler.Text.Reduction5.indexfCompl hw hd hwd
      have hdw : Kepler.Text.Reduction5.indexf d w r = r.length - Kepler.Text.Reduction5.indexf w d r := by omega
      have hpdw : Kepler.Text.Reduction5.indexf pd w r = r.length - Kepler.Text.Reduction5.indexf w pd r := by omega
      have hsum_lt : Kepler.Text.Reduction5.indexf pd d r + Kepler.Text.Reduction5.indexf d w r < r.length := by
        rw [hpd1, hdw]
        omega
      have hsum := Kepler.Text.Reduction4.indexf_add_sum hpd hd hw hsum_lt
      rw [hpd1, hdw, hpdw] at hsum
      omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfPrevSucc
