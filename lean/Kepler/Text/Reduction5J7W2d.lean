/-
  Kepler.Text.Reduction5J7W2d — J5-7 W2c：`betwn_d_y`（HOL betwn_core0_z_y.hl:961-1111）。

  **路线（比 HOL 的 aqs_eq_last_next 更短）**：逐位外延
  `List.ext_getElem`：`betwnOrbit`（TameSpine B2d:188）给
  `(between s a b)[j] = (nextEl s)^[j+1] a`，两侧同指数 + 幂同步
  `powSyncD`（W2b 私有件同证重推导）⇒ 逐位相等；长度由 `sizeBetwn` 两侧 +
  `indexf d y0 r = indexf d y0 f`。
  **不引入 aqs_eq_last_next 的三段前提**（hnext 末元支、表头等均不需要）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W2b
import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2d

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **从 d 出发的幂同步**（W2b 私有件同证重推导；私件不跨文件）：
`i ≤ indexf d y0 r ⇒ (nextEl r)^i d = (nextEl f)^i d`。 -/
private theorem powSyncD (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r)
    {f : List Dart} {w d : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hdfst : d.1 ≠ (ytrans L N r x 0).1)
    (hidx : indexf w d f ≤ indexf w (ytrans L N r x 0) f)
    (hdf : d ∈ f) :
    ∀ i : ℕ, i ≤ indexf d (ytrans L N r x 0) r →
      (nextEl r)^[i] d = (nextEl f)^[i] d := by
  set y0 := ytrans L N r x 0 with hy0
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
  have hy0r : y0 ∈ r := pnxvwfs1 L hL hgn haq 0 hf hm
  have hy0f : y0 ∈ f := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm 0
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have h_idx_y0 : indexf w y0 f = indexf w y0 r := by
    have hf1 : indexf (nextEl (findFaceDarts L x) x)
        (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x)
        = Kepler.Text.Reduction5.lm L r x :=
      Kepler.Text.Reduction4Idx.indexfYtransEqLm L hL hgn hunL hm hf
    have hr1 : indexf w y0 r = Kepler.Text.Reduction5.lm L r x := by
      have h := Kepler.Text.Reduction4Idx.indexfYtransEqLM1 L hL haq hgn 0 hm hf
        (w := w) (by rw [Kepler.Text.Reduction5.rtrans_zero]; exact hwr.symm)
      rw [Kepler.Text.Reduction5.rtrans_zero] at h
      exact h
    have hf1' : indexf w y0 f = Kepler.Text.Reduction5.lm L r x := by
      rw [← hw, ← hfind]
      exact hf1
    rw [hf1', hr1]
  have hdle_y0r : indexf w d f ≤ indexf w y0 r := by
    simpa [h_idx_y0] using hidx
  have hpow_d : (nextEl r)^[indexf w d f] w = (nextEl f)^[indexf w d f] w := by
    have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
      (by rw [hfind]; exact hw) hdle_y0r
    simpa only [← hfind] using h
  have hdFpow : (nextEl f)^[indexf w d f] w = d := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hwf hdf hfnd
  have hdlt_r : indexf w d f < r.length :=
    lt_of_le_of_lt hdle_y0r (indexfLtSizel hw_r hy0r)
  have hpow_d' : (nextEl r)^[indexf w d f] w = d := hpow_d.trans hdFpow
  have h_idx_d : indexf w d r = indexf w d f := by
    have hp' : (@nextEl Dart instBEqOfDecidableEq r)^[indexf w d f] w = d := by
      rw [← Kepler.Text.Reduction5.iterateInstEq r w (indexf w d f)]
      exact hpow_d'
    exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hw_r
      (dMemROfSetup L hL hgn hres haq hm hf hfind hw hdf hidx) hnd hp' hdlt_r
  have hE1r : indexf w d r + indexf d y0 r = indexf w y0 r :=
    Kepler.Text.Reduction4.indexf_add_left hw_r
      (dMemROfSetup L hL hgn hres haq hm hf hfind hw hdf hidx) hy0r (by
        simpa [h_idx_d, h_idx_y0] using hidx)
  intro i hi
  have hm_le : indexf w d r + i ≤ indexf w y0 r := by omega
  have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
    (by rw [hfind]; exact hw) hm_le
  have h' : (nextEl r)^[indexf w d r + i] w
      = (nextEl f)^[indexf w d r + i] w := by
    simpa only [← hfind] using h
  have hin_r : (nextEl r)^[indexf w d r] w = d := by
    rw [h_idx_d]
    exact hpow_d'
  have hin_f : (nextEl f)^[indexf w d r] w = d := by
    rw [h_idx_d]
    exact hdFpow
  rw [Nat.add_comm (indexf w d r) i] at h'
  rw [Function.iterate_add_apply, Function.iterate_add_apply,
    hin_r, hin_f] at h'
  exact h'

/-- **W2c：HOL `betwn_d_y`**（betwn_core0_z_y.hl:961-1111）链形：
`betwn r d (ytrans 0) = betwn f d (ytrans 0)`。
证 = `betwnOrbit` 两侧逐位 + `powSyncD` + `sizeBetwn` 长度。 -/
theorem betwnDY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {f : List Dart} {w d : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hdfst : d.1 ≠ (ytrans L N r x 0).1)
    (hidx : indexf w d f ≤ indexf w (ytrans L N r x 0) f)
    (hdf : d ∈ f) :
    between r d (ytrans L N r x 0) = between f d (ytrans L N r x 0) := by
  set y0 := ytrans L N r x 0 with hy0
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hy0r : y0 ∈ r := pnxvwfs1 L hL hgn haq 0 hf hm
  have hy0f : y0 ∈ f := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm 0
  have hdy0 : d ≠ y0 := fun h => hdfst (by rw [h])
  have hd_r : d ∈ r := dMemROfSetup L hL hgn hres haq hm hf hfind hw hdf hidx
  -- N_r = N_f（加法等式）
  have hunL : ∀ l ∈ L, l.Nodup :=
    (Kepler.Text.TameSpine.simpleHypermapUniq L hL hgn).mp hres.simple
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
  have h_idx_y0 : indexf w y0 f = indexf w y0 r := by
    have hf1 : indexf (nextEl (findFaceDarts L x) x)
        (Kepler.Text.Reduction5.ly L r x) (findFaceDarts L x)
        = Kepler.Text.Reduction5.lm L r x :=
      Kepler.Text.Reduction4Idx.indexfYtransEqLm L hL hgn hunL hm hf
    have hr1 : indexf w y0 r = Kepler.Text.Reduction5.lm L r x := by
      have h := Kepler.Text.Reduction4Idx.indexfYtransEqLM1 L hL haq hgn 0 hm hf
        (w := w) (by rw [Kepler.Text.Reduction5.rtrans_zero]; exact hwr.symm)
      rw [Kepler.Text.Reduction5.rtrans_zero] at h
      exact h
    have hf1' : indexf w y0 f = Kepler.Text.Reduction5.lm L r x := by
      rw [← hw, ← hfind]
      exact hf1
    rw [hf1', hr1]
  have h_idx_d : indexf w d r = indexf w d f := by
    have hdle_y0r : indexf w d f ≤ indexf w y0 r := by
      simpa [h_idx_y0] using hidx
    have hpow_d : (nextEl r)^[indexf w d f] w = (nextEl f)^[indexf w d f] w := by
      have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
        (by rw [hfind]; exact hw) hdle_y0r
      simpa only [← hfind] using h
    have hdFpow : (nextEl f)^[indexf w d f] w = d := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact Kepler.Text.TameSpine.indexfN hwf hdf hfnd
    have hdlt_r : indexf w d f < r.length :=
      lt_of_le_of_lt hdle_y0r (indexfLtSizel hw_r hy0r)
    have hpow_d' : (nextEl r)^[indexf w d f] w = d := hpow_d.trans hdFpow
    have hp' : (@nextEl Dart instBEqOfDecidableEq r)^[indexf w d f] w = d := by
      rw [← Kepler.Text.Reduction5.iterateInstEq r w (indexf w d f)]
      exact hpow_d'
    exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hw_r hd_r hnd hp' hdlt_r
  have hN : indexf d y0 r = indexf d y0 f := by
    have hE1r : indexf w d r + indexf d y0 r = indexf w y0 r :=
      Kepler.Text.Reduction4.indexf_add_left hw_r hd_r hy0r (by
        simpa [h_idx_d, h_idx_y0] using hidx)
    have hE1f : indexf w d f + indexf d y0 f = indexf w y0 f :=
      Kepler.Text.Reduction4.indexf_add_left hwf hdf hy0f hidx
    have h1 : indexf w d r = indexf w d f := h_idx_d
    have h2 : indexf w y0 r = indexf w y0 f := h_idx_y0.symm
    omega
  -- 长度
  have hlenr : (between r d y0).length = indexf d y0 r - 1 := by
    rw [Kepler.Text.Reduction5.betweenInstEq r d y0]
    exact Kepler.Text.Reduction5.sizeBetwn hnd hd_r hy0r hdy0
  have hlenf : (between f d y0).length = indexf d y0 f - 1 := by
    rw [Kepler.Text.Reduction5.betweenInstEq f d y0]
    exact Kepler.Text.Reduction5.sizeBetwn hfnd hdf hy0f hdy0
  have hlens : (between r d y0).length = (between f d y0).length := by
    rw [hlenr, hlenf, hN]
  refine List.ext_getElem hlens (fun j hj1 hj2 => ?_)
  rw [Kepler.Text.TameSpine.betwnOrbit hdy0 hnd hd_r hy0r hj1,
    Kepler.Text.TameSpine.betwnOrbit hdy0 hfnd hdf hy0f hj2]
  exact powSyncD L hL hgn hres haq hm hf hfind hw hdfst hidx hdf (j + 1) (by
    rw [← hy0]
    rw [hlenr] at hj1
    omega)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.betwnDY
