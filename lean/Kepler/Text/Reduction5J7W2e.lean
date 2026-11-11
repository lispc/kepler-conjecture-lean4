/-
  Kepler.Text.Reduction5J7W2e — J5-7 W2d：`betwn_core0_z_y`（HOL betwn_core0_z_y.hl:1112-1299）。

  **路线（pointwise，工单指定）**：
  1. **core r 侧归纳**：`nextCoreFst`（J5M2Core:173）逐位给出
     `(nextEl (core L r))^k d.1 = ((nextEl r)^k d).1`（k ≤ indexf d y0 r）；
     弧上前提 `fList = nextEl r` 由 `powSyncD`（W2c 私有件同证重推导）+
     面相容 `findFaceDarts_congr_of_mem` 供；末步 `(nextEl r)^(indexf d y0 r) d = y0`
     由 `indexfN`。
  2. **core f 侧**：setup ⇒ f final（`finalListTransformCount` + `finalListRot` +
     `nextElRotate`）⇒ `core L f = map FST f`（`coreFinalList`）；
     `nextEl (map FST f) a.1 = (nextEl f a).1` 由 `nextElMapApply` 私有件同证重推导。
  3. **长度**：两侧 `indexf d.1 y0.1 = indexf d y0 r`（`nextElnIndexf`）：
     cf 侧长度直取 `f.length`；c 侧由「弧上 indexf+1 个 FST 两两相异」计数
     （`uniqImpInj`（= uniqFstFindFace 的 FST 单射）+ indexf 唯一性）。
  4. **收口**：`betwnOrbit` 两侧 + `sizeBetwn` + `List.ext_getElem`（与 W2c 同款）。

  HOL 尾段四步（condition_last_parts / prev_el_last_hd / aqs_fstHdMapBetwn /
  partsBetwnChain / partsBetwnFinal）作为备选路线留在 DELIVERY，未消费。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W2d
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction4Idx
import Kepler.Text.TameSpine.Reduction3J5CoreFinal
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.Reduction5McCore

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- `uniq (l.map f)` 下，`l.map f` 环上的 next_el 与原环经 f 对接
（J5M2Core 私有件 `nextElMapApply` 同证重推导）。 -/
private theorem nextElMapApplyC {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    (f : α → β) {l : List α} (hnd : (l.map f).Nodup) {a : α} (ha : a ∈ l) :
    nextEl (l.map f) (f a) = f (nextEl l a) := by
  have hfa : f a ∈ l.map f := List.mem_map_of_mem ha
  have hilt : l.idxOf a < l.length := List.idxOf_lt_length_iff.mpr ha
  have hmlt : l.idxOf a < (l.map f).length := by rw [List.length_map]; exact hilt
  have hget : (l.map f)[l.idxOf a] = f a := by
    rw [List.getElem_map]
    exact congrArg f (Kepler.Text.TameLp.getElem_idxOf ha)
  have hidx : (l.map f).idxOf (f a) = l.idxOf a := by
    have h := hnd.idxOf_getElem (l.idxOf a) hmlt
    rw [hget] at h
    exact h
  rw [Kepler.Text.TameLp.nextEl_eq_getD hfa, hidx, List.length_map,
    Kepler.Text.TameLp.nextEl_eq_getD ha, List.getD_map]

/-- **从 d 出发的幂同步**（W2c 私有件同证重推导；私件不跨文件）：
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

/-- **W2d：HOL `betwn_core0_z_y`**（betwn_core0_z_y.hl:1112-1299）链形：
`betwn (core L r) (FST d) (FST y0) = betwn (core L f) (FST d) (FST y0)`
（`y0 = ytrans L N r x 0`），pointwise 路线（见文件头）。 -/
theorem betwnCore0DY (L : fgraph ℕ) (hL : GoodList L)
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
    between (core L r) d.1 (ytrans L N r x 0).1
      = between (core L f) d.1 (ytrans L N r x 0).1 := by
  set y0 := ytrans L N r x 0 with hy0
  -- ===== 基础 setup（与 W2c `betwnDY` 同块）=====
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hy0r : y0 ∈ r := pnxvwfs1 L hL hgn haq 0 hf hm
  have hy0f : y0 ∈ f := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm 0
  have hd_r : d ∈ r := dMemROfSetup L hL hgn hres haq hm hf hfind hw hdf hidx
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
  -- ===== core r：无重 + 端点会员 =====
  have hc_nd : (core L r).Nodup := by
    have hq := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm
    refine hq (core L r) ?_
    rw [Kepler.Text.MoreLemma2Island1.quotientListCore]
    exact List.mem_map.mpr ⟨r, hm.2.2.1, rfl⟩
  have hd1c : d.1 ∈ core L r := memCore (L := L) hL hgn hm hd_r hf
  have hy01c : y0.1 ∈ core L r := memCore (L := L) hL hgn hm hy0r hf
  -- ===== f final（setup）⇒ core f = map FST f =====
  have hfinK : finalList L (rtrans L N r x k) :=
    finalListTransformCount L hL hgn haq hm (t := k) hk
  have hmK : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x k) (rtrans L N r x k) x := haq hgn N r x hm k
  have hrndK : (rtrans L N r x k).Nodup :=
    (List.nodup_flatten.mp hmK.2.1.1).1 (rtrans L N r x k) hmK.2.2.1
  have hxrK : x ∈ rtrans L N r x k := hmK.2.2.2.1
  obtain ⟨nrot, hrot⟩ :=
    Kepler.Text.Reduction5.finalListRot hL hfinK hxrK hrndK hxd
  have hf_rot : f = (rtrans L N r x k).rotate nrot := (hrot.trans hfind).symm
  have hfinF : finalList L f := by
    intro y hy
    have hyK : y ∈ rtrans L N r x k := by
      rw [hf_rot] at hy
      exact List.mem_rotate.mp hy
    rw [hfinK y hyK, hf_rot]
    exact (Kepler.Text.Reduction5.nextElRotate hrndK nrot y).symm
  have hall : ∀ y ∈ f, y ∈ listOfDarts L := by
    intro y hy
    exact Kepler.Text.TameLp.mem_darts_of_mem_findFace L (d := x)
      (by rw [hfind]; exact hy)
  have hcf : core L f = f.map (fun y : Dart => y.1) :=
    Kepler.Text.TameSpine.coreFinalList L hL hall hm.1.edgeNondegenerate hfinF hfnd
  have hmapnd : (f.map (fun y : Dart => y.1)).Nodup := by
    rw [← hfind]
    exact uniqFstFindFace L hL hgn hres hm
  have hd1cf : d.1 ∈ core L f := by
    rw [hcf]
    exact List.mem_map.mpr ⟨d, hdf, rfl⟩
  have hy01cf : y0.1 ∈ core L f := by
    rw [hcf]
    exact List.mem_map.mpr ⟨y0, hy0f, rfl⟩
  have hcf_nd : (core L f).Nodup := by
    rw [hcf]
    exact hmapnd
  -- ===== 幂同步（供两条走步）=====
  have hsync : ∀ i : ℕ, i ≤ indexf d y0 r →
      (nextEl r)^[i] d = (nextEl f)^[i] d :=
    fun i hi => powSyncD (L := L) hL hgn hres haq (N := N) (r := r) (x := x) hm hf
      (f := f) (w := w) (d := d) hfind hw hdfst hidx hdf i hi
  -- ===== core r 走步：nextCoreFst 归纳 =====
  have hwalkR : ∀ i : ℕ, i ≤ indexf d y0 r →
      (nextEl (core L r))^[i] d.1 = ((nextEl r)^[i] d).1 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hile : i ≤ indexf d y0 r := by omega
      rw [Function.iterate_succ_apply', ih hile]
      have hxr_i : (nextEl r)^[i] d ∈ r := Kepler.Text.TameSpine.memPowerNextEl hd_r i
      have hxr_i_f : (nextEl r)^[i] d ∈ f := by
        rw [hsync i hile]
        exact Kepler.Text.TameSpine.memPowerNextEl hdf i
      have hface : findFaceDarts L ((nextEl r)^[i] d) = f :=
        (Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1
          (z := (nextEl r)^[i] d) (d := x) hxd
          (by rw [hfind]; exact hxr_i_f)).trans hfind
      have hfdArc : fList L ((nextEl r)^[i] d) = nextEl r ((nextEl r)^[i] d) := by
        calc fList L ((nextEl r)^[i] d)
            = nextEl (findFaceDarts L ((nextEl r)^[i] d)) ((nextEl r)^[i] d) := rfl
          _ = nextEl f ((nextEl r)^[i] d) := by rw [hface]
          _ = (nextEl f)^[i + 1] d := by
                rw [hsync i hile]
                exact (Function.iterate_succ_apply' (nextEl f) i d).symm
          _ = (nextEl r)^[i + 1] d := (hsync (i + 1) hi).symm
          _ = nextEl r ((nextEl r)^[i] d) := Function.iterate_succ_apply' (nextEl r) i d
      rw [nextCoreFst L hL hgn hm hf hxr_i hfdArc, Function.iterate_succ_apply']
  -- ===== core f 走步：nextElMapApply + map FST =====
  have hnextMap : ∀ a ∈ f,
      nextEl (f.map (fun y : Dart => y.1)) a.1 = (nextEl f a).1 := by
    intro a ha
    simpa using nextElMapApplyC (f := fun y : Dart => y.1) hmapnd ha
  have hwalkF : ∀ i : ℕ, (nextEl (core L f))^[i] d.1 = ((nextEl f)^[i] d).1 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      have hxi_f : (nextEl f)^[i] d ∈ f := Kepler.Text.TameSpine.memPowerNextEl hdf i
      rw [hcf, hnextMap ((nextEl f)^[i] d) hxi_f, Function.iterate_succ_apply']
  -- ===== 计数：弧上 indexf+1 个 FST 两两相异 ⇒ indexf < |core r| =====
  have hnoPeriod : ∀ i j : ℕ, i < j → j ≤ indexf d y0 r →
      (nextEl r)^[i] d = (nextEl r)^[j] d → False := by
    intro i j hij hjM heq
    have hxir : (nextEl r)^[i] d ∈ r := Kepler.Text.TameSpine.memPowerNextEl hd_r i
    have hper : (nextEl r)^[j - i] ((nextEl r)^[i] d) = (nextEl r)^[i] d := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hij)]
      exact heq.symm
    have hltper : j - i < r.length := by
      have := indexfLtSizel hd_r hy0r
      omega
    have hpdec : (@nextEl Dart instBEqOfDecidableEq r)^[j - i] ((nextEl r)^[i] d)
        = (nextEl r)^[i] d := by
      rw [← Kepler.Text.Reduction5.iterateInstEq r ((nextEl r)^[i] d) (j - i)]
      exact hper
    have hEq := Kepler.Text.MoreLemma2Island1.nextElnIndexf hxir hxir hnd hpdec hltper
    have h0 := Kepler.Text.Reduction4.indexfRefl hxir
    omega
  have hMltc : indexf d y0 r < (core L r).length := by
    have hl_nd : ((List.range (indexf d y0 r + 1)).map
        (fun t => ((nextEl r)^[t] d).1)).Nodup := by
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hfst
      rw [List.mem_range] at hi hj
      have hiM : i ≤ indexf d y0 r := by omega
      have hjM : j ≤ indexf d y0 r := by omega
      have hfst' : ((nextEl r)^[i] d).1 = ((nextEl r)^[j] d).1 := hfst
      have hxi_f : (nextEl r)^[i] d ∈ f := by
        rw [hsync i hiM]
        exact Kepler.Text.TameSpine.memPowerNextEl hdf i
      have hxj_f : (nextEl r)^[j] d ∈ f := by
        rw [hsync j hjM]
        exact Kepler.Text.TameSpine.memPowerNextEl hdf j
      have hdarts : (nextEl r)^[i] d = (nextEl r)^[j] d :=
        Kepler.Text.TameSpine.uniqImpInj (f := fun y : Dart => y.1) hmapnd
          hxi_f hxj_f hfst'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnoPeriod i j hlt hjM hdarts
      · exact hnoPeriod j i hgt hiM hdarts.symm
    have hsub : ((List.range (indexf d y0 r + 1)).map
        (fun t => ((nextEl r)^[t] d).1)).toFinset ⊆ (core L r).toFinset := by
      intro v hv
      rw [List.mem_toFinset] at hv ⊢
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      rw [List.mem_range] at ht
      exact memCore (L := L) hL hgn hm (Kepler.Text.TameSpine.memPowerNextEl hd_r t) hf
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hl_nd] at hcard
    have hle := List.toFinset_card_le (core L r)
    have hlen : ((List.range (indexf d y0 r + 1)).map
        (fun t => ((nextEl r)^[t] d).1)).length = indexf d y0 r + 1 := by
      simp
    omega
  -- ===== 两侧 indexf = indexf d y0 r =====
  have hy0_pow_r : (nextEl r)^[indexf d y0 r] d = y0 := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hd_r hy0r hnd
  have hy0_pow_f : (nextEl f)^[indexf d y0 r] d = y0 := by
    have h : (nextEl f)^[indexf d y0 f] d = y0 := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact Kepler.Text.TameSpine.indexfN hdf hy0f hfnd
    rwa [← hN] at h
  have hidxc : indexf d.1 y0.1 (core L r) = indexf d y0 r := by
    have hp : (nextEl (core L r))^[indexf d y0 r] d.1 = y0.1 := by
      rw [hwalkR (indexf d y0 r) le_rfl, hy0_pow_r]
    exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hd1c hy01c hc_nd hp hMltc
  have hidxcf : indexf d.1 y0.1 (core L f) = indexf d y0 r := by
    have hp : (nextEl (core L f))^[indexf d y0 r] d.1 = y0.1 := by
      rw [hwalkF (indexf d y0 r), hy0_pow_f]
    have hlt : indexf d y0 r < (core L f).length := by
      rw [hcf, List.length_map]
      simpa [hN] using indexfLtSizel hdf hy0f
    exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hd1cf hy01cf hcf_nd hp hlt
  -- ===== 长度 + 逐位收口 =====
  have hlenr : (between (core L r) d.1 y0.1).length = indexf d y0 r - 1 := by
    rw [sizeBetwn hc_nd hd1c hy01c hdfst, hidxc]
  have hlenf : (between (core L f) d.1 y0.1).length = indexf d y0 r - 1 := by
    rw [sizeBetwn hcf_nd hd1cf hy01cf hdfst, hidxcf]
  refine List.ext_getElem ?_ (fun j hj1 hj2 => ?_)
  · rw [hlenr, hlenf]
  · rw [Kepler.Text.TameSpine.betwnOrbit hdfst hc_nd hd1c hy01c hj1,
      Kepler.Text.TameSpine.betwnOrbit hdfst hcf_nd hd1cf hy01cf hj2]
    rw [hlenr] at hj1
    have hle : j + 1 ≤ indexf d y0 r := by omega
    rw [hwalkR (j + 1) hle, hwalkF (j + 1)]
    exact congrArg (fun z : Dart => z.1) (hsync (j + 1) hle)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.betwnCore0DY
