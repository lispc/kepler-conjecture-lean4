/-
  Kepler.Text.Reduction5J7W2b — J5-7 W2b：`last_betwn_d_y`（HOL betwn_core0_z_y.hl:812-960）。

  **路线（indexf 层直接闭合）**：
  · 非空支：把两侧 betwn 的 **dec 载体冻结为普通列表变量** `Br`/`Bf`
    （`set Br := betwD r d y0`，`betwD` = `instBEqOfDecidableEq` 载体），
    在 `Br`/`Bf` 上做 LAST 幂公式（`indexlBetwn` + `sizeBetwn` + `indexfN`），
    避开 `@between` 的实例 elaboration 元变量；
  · 从 d 出发的幂同步 `(nextEl r)^i d = (nextEl f)^i d`（`nextElPowerTransEqFv0`
    于 m+i + 两处 `indexfN`）；
  · 空支：`betwnNilChain`（W2-0 绿）+ 幂同步 @1；
  · 收口：`Br = between r d y0`（`betweenInstEq` 反向）改写后
    `getLast!EqGetLast` + 两侧幂公式 + `← hN` + `hpowSync (N-1)`。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W2c

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- Dart 的 `instBEqOfDecidableEq` 载体 `between`（显式实例，供 set 冻结用）。 -/
private abbrev betwD (s : List Dart) (a b : Dart) : List Dart :=
  @between Dart (@instBEqOfDecidableEq Dart inferInstance) s a b

/-- **W2b（HOL `last_betwn_d_y`，betwn_core0_z_y.hl:812-960）**：
`LAST (betwn r d (ytrans 0)) = LAST (betwn f d (ytrans 0))`（链形）。 -/
theorem lastBetwnDY (L : fgraph ℕ) (hL : GoodList L)
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
    (between r d (ytrans L N r x 0)).getLast!
      = (between f d (ytrans L N r x 0)).getLast! := by
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
  have hdy0 : d ≠ y0 := fun h => hdfst (by rw [h])
  have hd_r : d ∈ r := dMemROfSetup L hL hgn hres haq hm hf hfind hw hdf hidx
  -- indexf 桥（同 W2a 内部）
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
  -- 从 d 出发的幂同步
  have hpowSync : ∀ i : ℕ, i ≤ indexf d y0 r →
      (nextEl r)^[i] d = (nextEl f)^[i] d := by
    intro i hi
    have hm_le : indexf w d r + i ≤ indexf w y0 r := by
      have hE1r : indexf w d r + indexf d y0 r = indexf w y0 r :=
        Kepler.Text.Reduction4.indexf_add_left hw_r hd_r hy0r (by
          simpa [h_idx_d, h_idx_y0] using hidx)
      omega
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
  -- 空/非空
  by_cases hbr : between r d y0 = []
  · have hNr_ne : indexf d y0 r ≠ 0 := fun h0 =>
      hdy0 (Kepler.Text.Reduction4.indexf_eq_zero hd_r hy0r h0)
    have h1 : y0 = nextEl r d :=
      (betwnNilChain hnd hdy0 hd_r hy0r).mp hbr
    have h2 : nextEl r d = nextEl f d := by
      have hpos : 0 < indexf d y0 r := Nat.pos_of_ne_zero hNr_ne
      simpa using hpowSync 1 (by omega)
    have hbf : between f d y0 = [] :=
      (betwnNilChain hfnd hdy0 hdf hy0f).mpr (h1.trans h2)
    rw [hbr, hbf]
  · have hbf : between f d y0 ≠ [] := by
      intro hb0
      have h1 : y0 = nextEl f d :=
        (betwnNilChain hfnd hdy0 hdf hy0f).mp hb0
      have h2 : nextEl f d = nextEl r d := by
        have hNr_ne : indexf d y0 r ≠ 0 := fun h0 =>
          hdy0 (Kepler.Text.Reduction4.indexf_eq_zero hd_r hy0r h0)
        have hpos : 0 < indexf d y0 r := Nat.pos_of_ne_zero hNr_ne
        simpa using (hpowSync 1 (by omega)).symm
      exact hbr ((betwnNilChain hnd hdy0 hd_r hy0r).mpr (h1.trans h2))
    -- 冻结 dec 载体
    set Br := betwD r d y0 with hBrDef
    set Bf := betwD f d y0 with hBfDef
    have hBr : Br = between r d y0 :=
      (Kepler.Text.Reduction5.betweenInstEq r d y0).symm
    have hBf : Bf = between f d y0 :=
      (Kepler.Text.Reduction5.betweenInstEq f d y0).symm
    have hbrB : Br ≠ [] := by rw [hBr]; exact hbr
    have hbfB : Bf ≠ [] := by rw [hBf]; exact hbf
    have huniqBr : Br.Nodup := by
      rw [hBr]
      exact Kepler.Text.TameSpine.uniqBetwn hnd hd_r hy0r hdy0
    have huniqBf : Bf.Nodup := by
      rw [hBf]
      exact Kepler.Text.TameSpine.uniqBetwn hfnd hdf hy0f hdy0
    -- Br 上 LAST 幂公式
    have hLR : Br.getLast hbrB = (nextEl r)^[indexf d y0 r - 1] d := by
      have hBmem : Br.getLast hbrB ∈ Br := List.getLast_mem hbrB
      have hblen : 0 < Br.length := List.length_pos_of_ne_nil hbrB
      have hBmemD : Br.getLast hbrB ∈ betwD r d y0 := hBmem
      have hidx : indexf d (Br.getLast hbrB) r = indexf d y0 r - 1 := by
        have h1 : List.idxOf (Br.getLast hbrB) Br + 1
            = indexf d (Br.getLast hbrB) r := by
          rw [Kepler.Text.Reduction5.idxOfInstEq]
          exact Kepler.Text.Reduction5.indexlBetwn (s := r) hnd hdy0 hd_r hy0r hBmemD
        have hBidx : List.idxOf (Br.getLast hbrB) Br = Br.length - 1 := by
          rw [List.getLast_eq_getElem hbrB]
          exact Kepler.Text.TameLp.idxOf_getElem (s := Br) huniqBr (by omega)
        have hlen : Br.length = indexf d y0 r - 1 :=
          Kepler.Text.Reduction5.sizeBetwn (s := r) hnd hd_r hy0r hdy0
        omega
      have hp : (nextEl r)^[indexf d (Br.getLast hbrB) r] d = Br.getLast hbrB := by
        rw [Kepler.Text.Reduction3.indexf_eq_spine]
        exact Kepler.Text.TameSpine.indexfN hd_r
          (Kepler.Text.Reduction5.betwnMem hBmemD) hnd
      rw [hidx] at hp
      exact hp.symm
    have hLF : Bf.getLast hbfB = (nextEl f)^[indexf d y0 f - 1] d := by
      have hBmem : Bf.getLast hbfB ∈ Bf := List.getLast_mem hbfB
      have hblen : 0 < Bf.length := List.length_pos_of_ne_nil hbfB
      have hBmemD : Bf.getLast hbfB ∈ betwD f d y0 := hBmem
      have hidx : indexf d (Bf.getLast hbfB) f = indexf d y0 f - 1 := by
        have h1 : List.idxOf (Bf.getLast hbfB) Bf + 1
            = indexf d (Bf.getLast hbfB) f := by
          rw [Kepler.Text.Reduction5.idxOfInstEq]
          exact Kepler.Text.Reduction5.indexlBetwn (s := f) hfnd hdy0 hdf hy0f hBmemD
        have hBidx : List.idxOf (Bf.getLast hbfB) Bf = Bf.length - 1 := by
          rw [List.getLast_eq_getElem hbfB]
          exact Kepler.Text.TameLp.idxOf_getElem (s := Bf) huniqBf (by omega)
        have hlen : Bf.length = indexf d y0 f - 1 :=
          Kepler.Text.Reduction5.sizeBetwn (s := f) hfnd hdf hy0f hdy0
        omega
      have hp : (nextEl f)^[indexf d (Bf.getLast hbfB) f] d = Bf.getLast hbfB := by
        rw [Kepler.Text.Reduction3.indexf_eq_spine]
        exact Kepler.Text.TameSpine.indexfN hdf
          (Kepler.Text.Reduction5.betwnMem hBmemD) hfnd
      rw [hidx] at hp
      exact hp.symm
    rw [← hBr, ← hBf,
      Kepler.Text.TameSpine.getLast!EqGetLast hbrB,
      Kepler.Text.TameSpine.getLast!EqGetLast hbfB,
      hLR, hLF, ← hN]
    exact hpowSync (indexf d y0 r - 1) (by omega)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.lastBetwnDY
