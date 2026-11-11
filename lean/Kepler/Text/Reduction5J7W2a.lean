/-
  Kepler.Text.Reduction5J7W2a — J5-7 W2a：`mem_betwn_d_y`（HOL betwn_core0_z_y.hl:666-811）。

  **路线（与 HOL 同结论、更短的 Lean 路径）**：不经 `parts_betwn`/`MAP FST` 面，
  直接在 `indexf` 层闭合：
  · `indexfBetwnEq` 双向只依赖 indexf 不等式（不要求中间 dart 属于该表）；
  · f-弧与 r-弧在 `indexf w d f ≤ indexf w y0 f` 范围内逐步同步
    （`nextElPowerTransEqFv0`），故对弧上 d1：
    `indexf w d1 r = indexf w d1 f`、`indexf d d1 r = indexf d d1 f`、
    `indexf d y0 r = indexf d y0 f`；
  · 两侧 `indexf_add_left/right` 换算后用 `indexfBetwnEq` 收口。
  HOL 的 `parts_betwn`/`aqs_fstHdMapBetwn`/`uniq_fst_find_face` 在本路线中**不需要**
  （它们服务于 HOL 的 `MAP FST` 中间表述；本文件零消费，不是遗漏）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W2
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.PwssratTail
import Kepler.Text.PwssratFace
import Kepler.Text.Reduction5J5BetweenInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- `indexfN` 的链形指数换词（Spine `indexf` → 链 `indexf`）。 -/
private theorem indexfNChain {s : List Dart} {w d : Dart} (hw : w ∈ s) (hd : d ∈ s)
    (hnd : s.Nodup) :
    (nextEl s)^[indexf w d s] w = d := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine]
  exact Kepler.Text.TameSpine.indexfN hw hd hnd

/-- `nextElnIndexf` 的 Dart 实例桥（prod BEq → `instBEqOfDecidableEq`）。 -/
private theorem nextElnIndexfChain {s : List Dart} {w d : Dart} (hw : w ∈ s)
    (hd : d ∈ s) (hnd : s.Nodup) {m : ℕ}
    (hp : (nextEl s)^[m] w = d) (hlt : m < s.length) :
    indexf w d s = m := by
  have hp' : (@nextEl Dart instBEqOfDecidableEq s)^[m] w = d := by
    rw [← Kepler.Text.Reduction5.iterateInstEq s w m]
    exact hp
  exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hw hd hnd hp' hlt

/-- **W2a（HOL `mem_betwn_d_y`，betwn_core0_z_y.hl:666-811）**：
`betwn r d (ytrans 0)` 与 `betwn f d (ytrans 0)` 成员等价（链形）。 -/
theorem memBetwnDY (L : fgraph ℕ) (hL : GoodList L)
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
    ∀ d1, d1 ∈ between r d (ytrans L N r x 0) ↔
      d1 ∈ between f d (ytrans L N r x 0) := by
  set y0 := ytrans L N r x 0 with hy0
  -- 基础事实
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
  -- (1) indexf w y0 f = indexf w y0 r（lm 双侧）
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
  -- (2) indexf w d r = indexf w d f
  have hdle_y0r : indexf w d f ≤ indexf w y0 r := by
    simpa [h_idx_y0] using hidx
  have hpow_d : (nextEl r)^[indexf w d f] w = (nextEl f)^[indexf w d f] w := by
    have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
      (by rw [hfind]; exact hw) hdle_y0r
    simpa only [← hfind] using h
  have hdFpow : (nextEl f)^[indexf w d f] w = d :=
    indexfNChain hwf hdf hfnd
  have hd_r : d ∈ r := by
    have h : (nextEl r)^[indexf w d f] w = d := hpow_d.trans hdFpow
    rw [← h]
    exact Kepler.Text.TameSpine.memPowerNextEl hw_r _
  have hy0lt_r : indexf w y0 r < r.length := indexfLtSizel hw_r hy0r
  have hdlt_r : indexf w d f < r.length := lt_of_le_of_lt hdle_y0r hy0lt_r
  have hpow_d' : (nextEl r)^[indexf w d f] w = d := hpow_d.trans hdFpow
  have h_idx_d : indexf w d r = indexf w d f :=
    nextElnIndexfChain hw_r hd_r hnd hpow_d' hdlt_r
  -- (3) 弧上同步：对 d1 的两个 indexf 等式
  have hsync : ∀ d1 ∈ r, indexf w d1 r ≤ indexf w y0 r →
      indexf w d1 r = indexf w d1 f ∧ d1 ∈ f := by
    intro d1 hd1r hle
    have hlen : indexf w d1 r < r.length := lt_of_le_of_lt hle hy0lt_r
    have hp_r : (nextEl r)^[indexf w d1 r] w = d1 :=
      indexfNChain hw_r hd1r hnd
    have htrans : (nextEl r)^[indexf w d1 r] w
        = (nextEl f)^[indexf w d1 r] w := by
      have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
        (by rw [hfind]; exact hw) hle
      simpa only [← hfind] using h
    have hp_f : (nextEl f)^[indexf w d1 r] w = d1 := htrans ▸ hp_r
    have hd1f : d1 ∈ f := by
      rw [← hp_f]
      exact Kepler.Text.TameSpine.memPowerNextEl hwf _
    have hlen_f : indexf w d1 r < f.length := by
      have h1 : indexf w d1 r ≤ indexf w y0 f := by
        simpa [h_idx_y0] using hle
      exact lt_of_le_of_lt h1 (indexfLtSizel hwf hy0f)
    have hidx_f : indexf w d1 f = indexf w d1 r :=
      nextElnIndexfChain hwf hd1f hfnd hp_f hlen_f
    exact ⟨hidx_f.symm, hd1f⟩
  -- (4) 主等价
  intro d1
  constructor
  · -- →：d1 ∈ betwn r d y0
    intro hmem
    have hmemD : d1 ∈ @between Dart instBEqOfDecidableEq r d y0 := by
      rwa [Kepler.Text.Reduction5.betweenInstEq r d y0] at hmem
    have hd1r : d1 ∈ r := Kepler.Text.Reduction5.betwnMem hmemD
    obtain ⟨hpos_r, hlt_r⟩ :=
      (indexfBetwnEq hdy0 hnd hd_r hy0r).mp hmemD
    -- 四个加法等式（r 侧）
    have hE1r : indexf w d r + indexf d y0 r = indexf w y0 r :=
      Kepler.Text.Reduction4.indexf_add_left hw_r hd_r hy0r (by
        simpa [h_idx_d, h_idx_y0] using hidx)
    have hE2r : indexf d d1 r + indexf d1 y0 r = indexf d y0 r :=
      Kepler.Text.Reduction4.indexf_add_left hd_r hd1r hy0r (Nat.le_of_lt hlt_r)
    have hE3r : indexf w d1 r + indexf d1 y0 r = indexf w y0 r :=
      Kepler.Text.Reduction4.indexf_add_right hw_r hd1r hy0r (by omega)
    have hwd1 : indexf w d1 r = indexf w d r + indexf d d1 r := by omega
    have hle1 : indexf w d r ≤ indexf w d1 r := by omega
    obtain ⟨hsyn1, hd1f⟩ := hsync d1 hd1r (by omega)
    -- f 侧加法
    have hE1f : indexf w d f + indexf d y0 f = indexf w y0 f :=
      Kepler.Text.Reduction4.indexf_add_left hwf hdf hy0f hidx
    have hE3f : indexf w d f + indexf d d1 f = indexf w d1 f :=
      Kepler.Text.Reduction4.indexf_add_left hwf hdf hd1f (by
        simpa [← h_idx_d, ← hsyn1] using hle1)
    have hdd1f : indexf d d1 f = indexf d d1 r := by
      have h1 : indexf w d f = indexf w d r := h_idx_d.symm
      omega
    have hdy0f : indexf d y0 f = indexf d y0 r := by
      have h1 : indexf w d f = indexf w d r := h_idx_d.symm
      have h2 : indexf w y0 f = indexf w y0 r := h_idx_y0
      omega
    have hgoalD : d1 ∈ @between Dart instBEqOfDecidableEq f d y0 :=
      (indexfBetwnEq hdy0 hfnd hdf hy0f).mpr
        ⟨by rw [hdd1f]; exact hpos_r, by rw [hdd1f, hdy0f]; exact hlt_r⟩
    rwa [← Kepler.Text.Reduction5.betweenInstEq f d y0] at hgoalD
  · -- ←：d1 ∈ betwn f d y0
    intro hmem
    have hmemD : d1 ∈ @between Dart instBEqOfDecidableEq f d y0 := by
      rwa [Kepler.Text.Reduction5.betweenInstEq f d y0] at hmem
    have hd1f : d1 ∈ f := Kepler.Text.Reduction5.betwnMem hmemD
    obtain ⟨hpos_f, hlt_f⟩ :=
      (indexfBetwnEq hdy0 hfnd hdf hy0f).mp hmemD
    -- f 侧加法
    have hE1f : indexf w d f + indexf d y0 f = indexf w y0 f :=
      Kepler.Text.Reduction4.indexf_add_left hwf hdf hy0f hidx
    have hE2f : indexf d d1 f + indexf d1 y0 f = indexf d y0 f :=
      Kepler.Text.Reduction4.indexf_add_left hdf hd1f hy0f (Nat.le_of_lt hlt_f)
    have hE3f : indexf w d1 f + indexf d1 y0 f = indexf w y0 f :=
      Kepler.Text.Reduction4.indexf_add_right hwf hd1f hy0f (by omega)
    have hwd1f : indexf w d1 f = indexf w d f + indexf d d1 f := by omega
    have hle1f : indexf w d f ≤ indexf w d1 f := by omega
    -- 同步回 r：d1 ∈ f 且 indexf w d1 f ≤ indexf w y0 f → r 侧
    have hle1r : indexf w d1 f ≤ indexf w y0 r := by
      have h1 : indexf w d1 f ≤ indexf w y0 f := by omega
      simpa [h_idx_y0] using h1
    have hpow_d1 : (nextEl f)^[indexf w d1 f] w = d1 :=
      indexfNChain hwf hd1f hfnd
    have htrans : (nextEl f)^[indexf w d1 f] w
        = (nextEl r)^[indexf w d1 f] w := by
      have h := nextElPowerTransEqFv0 (L := L) hL hgn haq hm hf (w := w)
        (by rw [hfind]; exact hw) hle1r
      simpa only [← hfind] using h.symm
    have hp_r : (nextEl r)^[indexf w d1 f] w = d1 := htrans ▸ hpow_d1
    have hd1r : d1 ∈ r := by
      rw [← hp_r]
      exact Kepler.Text.TameSpine.memPowerNextEl hw_r _
    have hlen_r : indexf w d1 f < r.length := by
      have h1 : indexf w d1 f ≤ indexf w y0 r := hle1r
      exact lt_of_le_of_lt h1 hy0lt_r
    have hidx_d1r : indexf w d1 r = indexf w d1 f :=
      nextElnIndexfChain hw_r hd1r hnd hp_r hlen_r
    -- r 侧加法
    have hE1r : indexf w d r + indexf d y0 r = indexf w y0 r :=
      Kepler.Text.Reduction4.indexf_add_left hw_r hd_r hy0r (by
        simpa [h_idx_d, h_idx_y0] using hidx)
    have hE3r : indexf w d r + indexf d d1 r = indexf w d1 r :=
      Kepler.Text.Reduction4.indexf_add_left hw_r hd_r hd1r (by
        simpa [← h_idx_d, ← hidx_d1r] using hle1f)
    have hdd1r : indexf d d1 r = indexf d d1 f := by
      have h1 : indexf w d r = indexf w d f := h_idx_d
      have h2 : indexf w d1 r = indexf w d1 f := hidx_d1r
      omega
    have hdy0r : indexf d y0 r = indexf d y0 f := by
      have h1 : indexf w d r = indexf w d f := h_idx_d
      have h2 : indexf w y0 r = indexf w y0 f := h_idx_y0.symm
      omega
    have hgoalD : d1 ∈ @between Dart instBEqOfDecidableEq r d y0 :=
      (indexfBetwnEq hdy0 hnd hd_r hy0r).mpr
        ⟨by rw [hdd1r]; exact hpos_f, by rw [hdd1r, hdy0r]; exact hlt_f⟩
    rwa [← Kepler.Text.Reduction5.betweenInstEq r d y0] at hgoalD

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.memBetwnDY
