/-
  Kepler.Text.TameSpine.Reduction3J5MemBetwnPreFace — tame-corr nb32：J5-6
  `mem_betwn_pre_face`（HOL betwn_corek_z_x.hl:218，body 91 行）。

  陈述（HOL 逐字）：七前提下
  `∀x', x' ∈ betwn (find_face L x) (ztrans (k-1)) x ↔ x' ∈ betwn r (ztrans (k-1)) x`。

  路线（HOL 同构，换成链侧在库引擎）：
  - 成员双向用 `indexfBetwnEq`（TameList3:1209）+ `indexfN` + `nextElnIndexf`；
  - 弧段重合用 `cases2Chain`（PowerCorePublic:68），n 界由
    `indexfSizeZTranPre`（本塔 nb31）+ `indexfTNextEl`（本文件，模移位）给出；
  - 端点 x 在 r 上的 indexf 定位（HOL 前段 CASES2+next_eln_indexf 同构）；
  - 模坍缩支（f-序绕回，`indexf zk w f = 0`）用变换态上的
    `Reduction4Idx.pplhulj3V0` 排除（对应 HOL 的 PPLHULJ3 用法）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfSizeZTranPre
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.PwssratFace
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans transformCount)

/-- `next_el` 步进的 `indexf` 模移位（`TameSpine.indexf` 形；同
`Reduction3CoreSplitNormal:394` 的私件，此处以本塔命名空间重证）。 -/
private theorem indexfTNextEl {f : List Dart} {y d : Dart}
    (hnd : f.Nodup) (hy : y ∈ f) (hd : d ∈ f) :
    Kepler.Text.TameSpine.indexf y (nextEl f d) f
      = (Kepler.Text.TameSpine.indexf y d f + 1) % f.length := by
  have hpos : 0 < f.length := List.length_pos_of_mem hd
  have hnextmem : nextEl f d ∈ f := Kepler.Text.TameLp.nextEl_mem_of_mem hd
  have hi : f.idxOf (nextEl f d) = (f.idxOf d + 1) % f.length := by
    rw [Kepler.Text.TameLp.nextEl_eq_getD hd,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
    exact Kepler.Text.TameLp.idxOf_getElem hnd (Nat.mod_lt _ hpos)
  have hival : Kepler.Text.TameSpine.indexf y d f
      = (f.idxOf d + (f.length - f.idxOf y)) % f.length := by
    unfold Kepler.Text.TameSpine.indexf
    rw [if_pos ⟨hy, hd⟩]
  have hival2 : Kepler.Text.TameSpine.indexf y (nextEl f d) f
      = (f.idxOf (nextEl f d) + (f.length - f.idxOf y)) % f.length := by
    unfold Kepler.Text.TameSpine.indexf
    rw [if_pos ⟨hy, hnextmem⟩]
  rw [hival, hival2, hi, Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

/-- **HOL `mem_betwn_pre_face`**（betwn_corek_z_x.hl:218）：
七前提下 `betwn (find_face L x) (ztrans (k-1)) x` 与 `betwn r (ztrans (k-1)) x`
逐元同成员。 -/
theorem memBetwnPreFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    ∀ x' : Dart, x' ∈ between (findFaceDarts L x) (ztrans L N r x (k - 1)) x
      ↔ x' ∈ between r (ztrans L N r x (k - 1)) x := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  set f : List Dart := findFaceDarts L x with hf
  set w : Dart := nextEl f x with hw
  set zk : Dart := ztrans L N r x (k - 1) with hz
  -- 基本结构件
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxf : x ∈ f := by
    rw [hf]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hx
  have hwf : w ∈ f := by
    rw [hw]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hfnd : f.Nodup := by
    rw [hf]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hzkf : zk ∈ f := by
    rw [hz, hf]
    exact Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm (k - 1)
  have hzkr : zk ∈ r := by
    rw [hz]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq (k - 1)
      (Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)) hm
  have hxr : x ∈ r := hm.2.2.2.1
  have hrnd : r.Nodup := Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hzkx : zk ≠ x := fun h => hne (by rw [h])
  have hnextr : nextEl r x = w := by
    rw [hw, hf]
    exact hm.2.2.2.2.2.1
  have hwr : w ∈ r := hnextr ▸ Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  -- 界
  have hltf : Kepler.Text.TameSpine.indexf zk w f < f.length := by
    have h := Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hwf
    rwa [Kepler.Text.Reduction3.indexf_eq_spine] at h
  have hltr : Kepler.Text.TameSpine.indexf zk w f < r.length := by
    have h := indexfSizeZTranPre L hL hgn hres hm hk hk0 hne
    rwa [Kepler.Text.Reduction3.indexf_eq_spine] at h
  have hm_lt : Kepler.Text.TameSpine.indexf zk x f < f.length := by
    have h := Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hxf
    rwa [Kepler.Text.Reduction3.indexf_eq_spine] at h
  -- (a) `indexf zk w f` 的 +1 模移位
  have hnextIdx : Kepler.Text.TameSpine.indexf zk w f
      = (Kepler.Text.TameSpine.indexf zk x f + 1) % f.length := by
    have h := indexfTNextEl hfnd hzkf hxf
    rwa [← hw] at h
  -- (b) 模坍缩支排除：p = 0 ⇒ w = zk ⇒ 撞 PPLHULJ3
  have hp0 : 0 < Kepler.Text.TameSpine.indexf zk w f := by
    by_contra hle
    have hpzero : Kepler.Text.TameSpine.indexf zk w f = 0 := by omega
    have hwzk : w = zk := by
      have h1 := Kepler.Text.TameSpine.indexfN hzkf hwf hfnd
      rw [hpzero] at h1
      simpa using h1.symm
    have hm' : Kepler.Text.ChainLists.markedList L hL
        (Kepler.Text.Reduction5.ntrans L N r x (k - 1))
        (Kepler.Text.Reduction5.rtrans L N r x (k - 1)) x :=
      haq hgn N r x hm (k - 1)
    have hf' : ¬ Kepler.Text.Reduction5.finalList L (Kepler.Text.Reduction5.rtrans L N r x (k - 1)) :=
      Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
    have hpp := Kepler.Text.Reduction4Idx.pplhulj3V0 L hL hgn hunL hm' hf'
    have hzEq : Kepler.Text.Reduction5.lz L
        (Kepler.Text.Reduction5.ntrans L N r x (k - 1))
        (Kepler.Text.Reduction5.rtrans L N r x (k - 1)) x = zk := by
      rw [hz]
      rfl
    rw [hzEq] at hpp
    have h0 : Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x) zk
        (findFaceDarts L x) = 0 := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      rw [hwzk.symm]
      simpa [hw, hf] using (Kepler.Text.TameSpine.indexfRefl hwf)
    rw [h0] at hpp
    exact absurd hpp (Nat.not_lt_zero _)
  -- m ≤ p
  have hmle : Kepler.Text.TameSpine.indexf zk x f ≤ Kepler.Text.TameSpine.indexf zk w f := by
    by_cases hlt : Kepler.Text.TameSpine.indexf zk x f + 1 < f.length
    · rw [hnextIdx, Nat.mod_eq_of_lt hlt]
      omega
    · have hsucc : Kepler.Text.TameSpine.indexf zk x f + 1 = f.length := by omega
      have hpzero : Kepler.Text.TameSpine.indexf zk w f = 0 := by
        rw [hnextIdx, hsucc, Nat.mod_self]
      omega
  -- 弧段重合（CASES2）
  have hcongr : ∀ n, n ≤ Kepler.Text.TameSpine.indexf zk w f →
      (nextEl r)^[n] zk = (nextEl f)^[n] zk := by
    intro n hn
    have hn' : n ≤ Kepler.Text.Reduction5.indexf zk w f := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact hn
    exact Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm (f := f) (w := w)
      hf.symm hw.symm hk hk0 hn'
  -- 端点 x 在 r 上的 indexf 定位（HOL 前段）
  have hidxXr : Kepler.Text.TameSpine.indexf zk x r = Kepler.Text.TameSpine.indexf zk x f := by
    have hiter_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk x f] zk = x :=
      Kepler.Text.TameSpine.indexfN hzkf hxf hfnd
    have hiter_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk x f] zk = x :=
      (hcongr _ hmle).trans hiter_f
    have hlt : Kepler.Text.TameSpine.indexf zk x f < r.length := by omega
    exact Kepler.Text.TameSpine.nextElnIndexf hzkr hxr hrnd hiter_r hlt
  intro d
  constructor
  · -- 正向：betwn f → betwn r
    intro hd
    have hdf : d ∈ f := Kepler.Graphs.inbetween_inset hd
    obtain ⟨hposd, hltdm⟩ :=
      (Kepler.Text.TameSpine.indexfBetwnEq hzkx hfnd hzkf hxf).mp hd
    have hdle : Kepler.Text.TameSpine.indexf zk d f ≤ Kepler.Text.TameSpine.indexf zk w f := by
      omega
    have hiter_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk d f] zk = d :=
      Kepler.Text.TameSpine.indexfN hzkf hdf hfnd
    have hiter_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk d f] zk = d :=
      (hcongr _ hdle).trans hiter_f
    have hdr : d ∈ r := by
      rw [← hiter_r]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkr _
    have hltrd : Kepler.Text.TameSpine.indexf zk d f < r.length := by omega
    have hidxd : Kepler.Text.TameSpine.indexf zk d r = Kepler.Text.TameSpine.indexf zk d f :=
      Kepler.Text.TameSpine.nextElnIndexf hzkr hdr hrnd hiter_r hltrd
    refine (Kepler.Text.TameSpine.indexfBetwnEq hzkx hrnd hzkr hxr).mpr ?_
    rw [hidxd, hidxXr]
    exact ⟨hposd, hltdm⟩
  · -- 反向：betwn r → betwn f
    intro hd
    have hdr : d ∈ r := Kepler.Graphs.inbetween_inset hd
    obtain ⟨hposd, hltdm⟩ :=
      (Kepler.Text.TameSpine.indexfBetwnEq hzkx hrnd hzkr hxr).mp hd
    have hltdm' : Kepler.Text.TameSpine.indexf zk d r < Kepler.Text.TameSpine.indexf zk x f := by
      rw [hidxXr] at hltdm
      exact hltdm
    have hdle : Kepler.Text.TameSpine.indexf zk d r ≤ Kepler.Text.TameSpine.indexf zk w f := by
      omega
    have hiter_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk d r] zk = d :=
      Kepler.Text.TameSpine.indexfN hzkr hdr hrnd
    have hiter_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk d r] zk = d := by
      rw [← hcongr _ hdle]
      exact hiter_r
    have hdf : d ∈ f := by
      rw [← hiter_f]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkf _
    have hltfd : Kepler.Text.TameSpine.indexf zk d r < f.length := by omega
    have hidxd : Kepler.Text.TameSpine.indexf zk d f = Kepler.Text.TameSpine.indexf zk d r :=
      Kepler.Text.TameSpine.nextElnIndexf hzkf hdf hfnd hiter_f hltfd
    refine (Kepler.Text.TameSpine.indexfBetwnEq hzkx hfnd hzkf hxf).mpr ?_
    rw [hidxd]
    exact ⟨hposd, hltdm'⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.indexfTNextEl
#print axioms Kepler.Text.TameSpine.memBetwnPreFace
