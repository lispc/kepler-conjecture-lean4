/-
  Kepler.Text.Reduction5J5K2Prefix — Lane A1：K2 包装前置两件
  （HOL `More_lemma2.v_final_lemmas` more_lemma2.hl:195–216 +
   `More_lemma2.indexf1_final_lemmas` more_lemma2.hl:745–776）。

  ┌─ 定位 ─────────────────────────────────────────────────────────
  │ 两件是 `reduction_K2`（HOL reduction4.hl:1276–1442，
  │ K2CONCLUSION → K1CONCLUSION 包装）的直接前置：
  │   · `vFinalLemmas` = K1CONCLUSION 首合取（V）的证明；
  │   · `indexf1FinalLemmas` = K1CONCLUSION INDEX 1 的证明。
  │ K1 本体 `reductionK1`（K1CONCLUSION → assumptionSetK10）已落，
  │ 但上述两合取的证明未落——本件补上，K2 包装才可能开工。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（比 HOL 短，不搬原长证）─────────────────────────────────
  │ · `vFinalLemmas`：`prevCoreX`（nb37，在库）在基态与塔态 i 各实例化一次，
  │   加 `fstNextFaceEqSnd`（nb，J5-1a）+ `nextPrevId`/pair 投影；
  │   HOL 原证的 `MEM_CORE`/`quotient_all_uniq`/`next_prev_id` 三段被
  │   `prevCoreX` 一次吃掉。
  │ · `indexf1FinalLemmas`：HOL 原证 31 行——`indexfYtransEqLm`（PwssratFace，
  │   在库）给 f 侧 = `lm`；`indexfYtransEqLM1`（PwssratTail，在库）在 i=0 给
  │   r 侧 = `lm`；`indexfYltSizel`（双怪件主件，在库）给 `n < |core|`；
  │   `nextPowerCoreW`（J5-5 波，在库）+ `indexfN` + `nextElnIndexf` 收口。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（公理/占位/反射式判定）；不改既有陈述/定义；
  主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.Reduction3J5PrevCoreX
import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizel
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction5McCore
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.PwssratFace
import Kepler.Text.PwssratTail
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2a23
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Idx
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)

/-- **HOL `More_lemma2.v_final_lemmas`**（more_lemma2.hl:195–216）：
六前提 ⇒ `∀ v, prevEl (core L r) v = x.1 ∧ v = x.2 →
(∀ i < k, prevEl (core L (rtrans i)) v = x.1 ∧ v = x.2) ∧
(nextEl (findFaceDarts L x) x).1 = v`。

路线：`prevCoreX` 在基态/塔态各一次 + `fstNextFaceEqSnd`。 -/
theorem vFinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k) :
    ∀ v : ℕ, (prevEl (core L r) v, v) = x →
      (∀ i : ℕ, i < k → (prevEl (core L (rtrans L N r x i)) v, v) = x) ∧
      (nextEl (findFaceDarts L x) x).1 = v := by
  intro v hv
  have hv2 : v = x.2 := congrArg Prod.snd hv
  -- 基态：v = (nextEl f x).1
  have hw : (nextEl (findFaceDarts L x) x).1 = v := by
    rw [hv2]
    exact fstNextFaceEqSnd L hL hgn hm hf
  constructor
  · -- 塔态 i：prevCoreX 于 (ntrans i, rtrans i) 实例化
    intro i hi
    have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
      fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
    have hm' : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
    have hf' : ¬ finalList L (rtrans L N r x i) :=
      Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
    have hprev' : prevEl (core L (rtrans L N r x i))
        (nextEl (findFaceDarts L x) x).1 = x.1 :=
      Kepler.Text.TameSpine.prevCoreX L hL hgn hm' hf'
    have hv' : v = (nextEl (findFaceDarts L x) x).1 := hw.symm
    rw [hv']
    exact Prod.ext hprev' (hw.trans hv2)
  · exact hw

/-- **HOL `More_lemma2.indexf1_final_lemmas`**（more_lemma2.hl:745–776）：
五前提 ⇒ `indexf (nextEl f x).1 (ytrans 0).1 (core L r) =
indexf (nextEl f x) (ytrans 0) f`。

路线：两侧都归约到 `lm L r x`（`indexfYtransEqLm` / `indexfYtransEqLM1`@i=0），
再用 `nextPowerCoreW` + `indexfN` + `nextElnIndexf` 把 core 层下标钉成
`indexf w y r`。 -/
theorem indexf1FinalLemmas (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    indexf (nextEl (findFaceDarts L x) x).1 (ytrans L N r x 0).1 (core L r)
      = indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x 0)
          (findFaceDarts L x) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  set f : List Dart := findFaceDarts L x with hfdef
  set w : Dart := nextEl f x with hwdef
  set y : Dart := ytrans L N r x 0 with hydef
  -- 基本结构件
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hxr : x ∈ r := hm.2.2.2.1
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hwr : w ∈ r := by
    have hwr' : w = nextEl r x := by
      rw [hwdef, hfdef]
      exact hm.2.2.2.2.2.1.symm
    rw [hwr']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hyr : y ∈ r := by
    rw [hydef]
    exact Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hf
  have hcund : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hwcore : w.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hwr hf
  have hycore : y.1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore (L := L) hL hgn hm hyr hf
  -- 两侧都 = lm L r x
  have hfl : indexf w y f = Kepler.Text.Reduction5.lm L r x := by
    have h := Kepler.Text.Reduction4Idx.indexfYtransEqLm L hL hgn hunL hm hf
    rw [hwdef, hfdef, hydef]
    rw [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.rtrans_zero]
    exact h
  have hrl : indexf w y r = Kepler.Text.Reduction5.lm L r x := by
    have h := Kepler.Text.Reduction4Idx.indexfYtransEqLM1 L hL haq hgn 0 hm hf
      (w := w) (by
        rw [Kepler.Text.Reduction5.rtrans_zero, hm.2.2.2.2.2.1]
        show nextEl (findFaceDarts L x) x = w
        rw [← hfdef, ← hwdef])
    rw [Kepler.Text.Reduction5.rtrans_zero] at h
    simpa only [hydef, Kepler.Text.Reduction5.ytrans_def,
      Kepler.Text.Reduction5.rtrans_zero] using h
  have hfr : indexf w y f = indexf w y r := hfl.trans hrl.symm
  -- n = indexf w y r，core 层幂对齐
  set n : ℕ := indexf w y r with hn
  have hpow1 : (nextEl (core L r))^[n] w.1 = ((nextEl r)^[n] w).1 :=
    Kepler.Text.TameSpine.nextPowerCoreW L hL hgn haq hm hf
      (f := f) (w := w) hfdef.symm hwdef.symm
      (n := n) (by rw [hn])
  have hif : (nextEl r)^[n] w = y := by
    rw [hn, Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hwr hyr hrnd
  have hpow : (nextEl (core L r))^[n] w.1 = y.1 :=
    hpow1.trans (congrArg Prod.fst hif)
  have hnlt : n < (core L r).length := by
    rw [hn]
    exact Kepler.Text.TameSpine.indexfYltSizel L hL hgn haq hm hf
      (f := f) (w := w) hfdef.symm hwdef.symm
  have hidx : indexf w.1 y.1 (core L r) = n :=
    Kepler.Text.MoreLemma2Island1.nextElnIndexf hwcore hycore hcund hpow hnlt
  -- 收口：core 层 = n = r 层 = f 层
  rw [hidx, hn, hfr]

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.vFinalLemmas
#print axioms Kepler.Text.Reduction5.indexf1FinalLemmas
