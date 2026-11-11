/-
  Kepler.Text.Reduction5J7W2c — J5-7 W2c 前置件：`dMemROfSetup`（`d ∈ r` 推导复用）。

  **勘误（重要）**：原计划的「成员等价 + 双 Nodup ⇒ 列表相等」**是假命题**
  （反例 `[1,2]` vs `[2,1]`：同成员、同 Nodup、不同序）。W2c `betwn_d_y` 的正确
  收口件是在库 `TameSpine.aqs_eq_last_next`（AQ12.hl:39：同成员 + 逐点
  `nextEl` 相同 + `LAST` 相同 ⇒ 相等），其中逐点 `nextEl` 由
  `Reduction3CoreSplitNormal.nextElBetwnSame` 供、`LAST` 由 **W2b
  `last_betwn_d_y`** 供——故 **W2c 依赖 W2b，顺序应为 W2b → W2c → W2d**。
  本文件先落 W2b/W2d 共用的 `d ∈ r` 推导件。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W2a
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **W2a `d ∈ r` 推导复用件**：在 `memBetwnDY` 的 setup 下 `d ∈ r`
（`indexfYtransEqLm/LM1` 给 `indexf w y0 f = indexf w y0 r`；
`nextElPowerTransEqFv0` 把 f-幂迁到 r；`indexfN` 给终点 d）。 -/
theorem dMemROfSetup (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {f : List Dart} {w d : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hdf : d ∈ f)
    (hidx : indexf w d f ≤ indexf w (ytrans L N r x 0) f) :
    d ∈ r := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hres.simple
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hxr : x ∈ r := hm.2.2.2.1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxf : x ∈ f := by
    rw [← hfind]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hwr : w = nextEl r x := by
    rw [← hw, ← hfind]
    exact hm.2.2.2.2.2.1.symm
  have hw_r : w ∈ r := by
    rw [hwr]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hwf : w ∈ f := by
    rw [← hw]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hy0r : ytrans L N r x 0 ∈ r := pnxvwfs1 L hL hgn haq 0 hf hm
  have hy0f : ytrans L N r x 0 ∈ f :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm 0
  have h_idx_y0 : indexf w (ytrans L N r x 0) f = indexf w (ytrans L N r x 0) r := by
    have hf1 : indexf (nextEl (findFaceDarts L x) x)
        (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x)
        = Kepler.Text.Reduction5.lm L r x :=
      Kepler.Text.Reduction4Idx.indexfYtransEqLm L hL hgn hunL hm hf
    have hr1 : indexf w (ytrans L N r x 0) r = Kepler.Text.Reduction5.lm L r x := by
      have h := Kepler.Text.Reduction4Idx.indexfYtransEqLM1 L hL haq hgn 0 hm hf
        (w := w) (by rw [Kepler.Text.Reduction5.rtrans_zero]; exact hwr.symm)
      rw [Kepler.Text.Reduction5.rtrans_zero] at h
      exact h
    have hf1' : indexf w (ytrans L N r x 0) f = Kepler.Text.Reduction5.lm L r x := by
      rw [← hw, ← hfind]
      exact hf1
    rw [hf1', hr1]
  have hdle : indexf w d f ≤ indexf w (ytrans L N r x 0) r := by
    simpa [h_idx_y0] using hidx
  have hpow : (nextEl r)^[indexf w d f] w = (nextEl f)^[indexf w d f] w := by
    have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
      (by rw [hfind]; exact hw) hdle
    simpa only [← hfind] using h
  have hdFpow : (nextEl f)^[indexf w d f] w = d := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hwf hdf hfnd
  have h : (nextEl r)^[indexf w d f] w = d := hpow.trans hdFpow
  rw [← h]
  exact Kepler.Text.TameSpine.memPowerNextEl hw_r _

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.dMemROfSetup
