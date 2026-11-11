/-
  Kepler.Text.TameSpine.Reduction3J5PartOfXHead — tame-corr nb42：J5-6 主件 P2 子论证 B
  （`betwn_corek_z_x` HOL betwn_corek_z_x.hl:641–:700 原态侧子论证 B）。

  命题：`x` 所在 atom（`px ∈ parts L r`、`x ∈ px`）的 `HD` 恰为 `x`。

  路线（nb41 短路线判定失效后的修正）：
  - 取 atom 内前驱 `pd := prevEl px x`；
  - 双支：pd = LAST px 支直接得 `nextEl px (LAST px) = px.head! = x`；
  - pd ≠ LAST px 支：
    · `nextPrevId` + `partsNextUnlast` ⇒ `x = fList L (eList pd)`；
    · `partsFst` ⇒ `pd.1 = x.1`；
    · `indexf` 定位 + `cases2Chain` ⇒ `(nextEl r)^[n] zk = pd`（n = PRE(indexf zk x f)）；
    · `nextCoreFst` ⇒ `nextEl (core L r) (x.1) = x.1`；
    · `nextElRefl` + `zk.1 ∈ core L r` 且 `zk.1 ≠ x.1` 得矛盾。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5CorePartsWiring
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3J5IndexfPrevPartial
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4
import Kepler.Text.Reduction3Thm6B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList eList findFaceDarts listOfDarts prevEl)
open Kepler.Text.Reduction5 (Dart ztrans transformCount core finalList parts)

/-- `next_el` 步进的 `indexf` 模移位（`TameSpine.indexf` 形；同款私件第 5 份）。 -/
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

/-- **P2 子论证 B**（HOL `betwn_corek_z_x.hl:641–:700`）：`x` 是其 atom 的头元。 -/
theorem partOfXHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1)
    {px : List Dart} (hpx : px ∈ parts L r)
    (hxpx : x ∈ px) :
    px.head! = x := by
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
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hxr
  have hzkx : zk ≠ x := fun h => hne (by rw [h])
  -- atom 非空 / 无重
  have hpxne : px ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r px hpx
  have hpxnd : px.Nodup := (Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hm.2.1 hm.2.2.1 hpx).2.2.1
  -- atom 内前驱
  set pd : Dart := prevEl px x with hpd
  have hpdmem : pd ∈ px := by
    rw [hpd]
    exact Kepler.Text.Reduction5.memPrevEl hxpx
  have hnextpx : nextEl px pd = x := by
    rw [Kepler.Text.Reduction5.nextElInstEq px pd, hpd]
    exact Kepler.Text.Reduction5.nextPrevId hpxnd x
  -- 双支：pd 是否为 atom 末元
  by_cases hlast : pd = px.getLast!
  · -- 支 B1：pd = LAST px ⇒ 循环 wrap 到头
    have hwrap : nextEl px (px.getLast!) = px.head! := by
      have hpos : 0 < px.length := List.length_pos_of_ne_nil hpxne
      have hmem : px.getLast! ∈ px := by
        rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (by omega)]
        simp
      have hlastidx : px.idxOf (px.getLast!) = px.length - 1 := by
        have hget : px[px.length - 1]'(by omega) = px.getLast! := by
          rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
            List.getElem?_eq_getElem (by omega)]
          rfl
        rw [← hget]
        exact Kepler.Text.TameLp.idxOf_getElem hpxnd (by omega)
      rw [Kepler.Text.TameLp.nextEl_eq_getD hmem]
      rw [hlastidx, show (px.length - 1 + 1) % px.length = 0 by
        rw [Nat.sub_add_cancel (by omega), Nat.mod_self]]
      rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by omega)]
      cases px with
      | nil => exact absurd rfl hpxne
      | cons a t => simp [List.head!_cons]
    rw [hlast] at hnextpx
    exact hwrap.symm.trans hnextpx
  · -- 支 B2：pd ≠ LAST px ⇒ 推导矛盾
    -- `nextEl px pd = fList L (eList pd)`（atom 内相邻 = n 步）
    have hnextpx' : nextEl px pd = fList L (eList pd) :=
      Kepler.Text.MoreLemma2PartsFst.partsNextUnlast L hrnd hrne px hpx pd hpdmem hlast
    have hx_eq : x = fList L (eList pd) := hnextpx.symm.trans hnextpx'
    -- `pd` 与 `x` 同首顶点
    have hpdx1 : pd.1 = x.1 := by
      have h1 := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpx hpdmem
      have h2 := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpx hxpx
      exact h1.trans h2.symm
    -- indexf 非零：zk ≠ x
    have hizkxx_pos : 0 < Kepler.Text.TameSpine.indexf zk x f := by
      by_contra hle
      have h0 : Kepler.Text.TameSpine.indexf zk x f = 0 := by omega
      have hxzk := Kepler.Text.TameSpine.indexfZeroEq hzkf hxf h0
      exact absurd hxzk hzkx
    -- indexf zk w f 非零（排除模坍缩，同 nb40）
    have hizkxw_pos : 0 < Kepler.Text.TameSpine.indexf zk w f := by
      by_contra hle
      have h0 : Kepler.Text.TameSpine.indexf zk w f = 0 := by omega
      have hwzk : w = zk := by
        have h1 := Kepler.Text.TameSpine.indexfN hzkf hwf hfnd
        rw [h0] at h1
        simpa using h1.symm
      have hm' : Kepler.Text.ChainLists.markedList L hL
          (Kepler.Text.Reduction5.ntrans L N r x (k - 1))
          (Kepler.Text.Reduction5.rtrans L N r x (k - 1)) x := haq hgn N r x hm (k - 1)
      have hf' : ¬ finalList L
          (Kepler.Text.Reduction5.rtrans L N r x (k - 1)) :=
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
      have h0' : Kepler.Text.Reduction5.indexf (nextEl (findFaceDarts L x) x) zk
          (findFaceDarts L x) = 0 := by
        rw [Kepler.Text.Reduction3.indexf_eq_spine]
        rw [hwzk.symm]
        simpa [hw, hf] using (Kepler.Text.TameSpine.indexfRefl hwf)
      rw [h0'] at hpp
      exact absurd hpp (Nat.not_lt_zero _)
    -- `indexf zk x f + 1 = indexf zk w f`（无模坍缩）
    have hizkxx_le_w : Kepler.Text.TameSpine.indexf zk x f
        ≤ Kepler.Text.TameSpine.indexf zk w f := by
      have hnext := indexfTNextEl hfnd hzkf hxf
      have hlt : Kepler.Text.TameSpine.indexf zk x f + 1 < f.length := by
        by_contra hge
        have heq : Kepler.Text.TameSpine.indexf zk x f + 1 = f.length := by
          have hle := Kepler.Text.TameSpine.indexfLtSizel hzkf hxf
          omega
        have h0 : Kepler.Text.TameSpine.indexf zk w f = 0 := by
          rw [hnext, heq, Nat.mod_self]
        omega
      rw [hnext, Nat.mod_eq_of_lt hlt]
      omega
    -- 定位 n：PRE(indexf zk x f)
    set n : ℕ := Kepler.Text.TameSpine.indexf zk x f - 1 with hn
    have hn1 : n + 1 = Kepler.Text.TameSpine.indexf zk x f := by
      rw [hn]
      omega
    have hn_bound : n + 1 ≤ Kepler.Text.Reduction5.indexf zk w f := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      omega
    have hn_bound' : n ≤ Kepler.Text.Reduction5.indexf zk w f := by omega
    -- 弧同步：r 侧与 f 侧在 n 及 n+1 处重合
    have hcongr_n : (nextEl r)^[n] zk = (nextEl f)^[n] zk :=
      Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm hf.symm hw.symm hk hk0 hn_bound'
    have hcongr_n1 : (nextEl r)^[n + 1] zk = (nextEl f)^[n + 1] zk :=
      Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm hf.symm hw.symm hk hk0 hn_bound
    -- f 侧 n+1 到达 x
    have hf_n1_x : (nextEl f)^[n + 1] zk = x := by
      rw [hn1]
      exact Kepler.Text.TameSpine.indexfN hzkf hxf hfnd
    -- pd 也是 x 在 r 中的前驱
    have hnextpd : nextEl r pd = x := by
      have h1 : nextEl r pd = nextEl px pd :=
        Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hrnd hrne hpx hpdmem hlast
      exact h1.trans hnextpx
    -- d := (nextEl r)^[n] zk 等于 pd
    set d : Dart := (nextEl r)^[n] zk with hd
    have hdmemr : d ∈ r := by
      rw [hd]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkr n
    have hnextd : nextEl r d = x := by
      rw [hd]
      calc nextEl r ((nextEl r)^[n] zk)
          _ = (nextEl r)^[n + 1] zk := by rw [Function.iterate_succ_apply']
          _ = (nextEl f)^[n + 1] zk := by rw [hcongr_n1]
          _ = x := hf_n1_x
    have hd_eq_pd : d = pd :=
      Kepler.Text.TameSpine.nextElInjOfNodup hrnd hdmemr
        (by
          rw [← Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]
          exact List.mem_flatten.mpr ⟨px, hpx, hpdmem⟩)
        (hnextd.trans hnextpd.symm)
    -- d 与 x 同首顶点
    have hdx1 : d.1 = x.1 := by rw [hd_eq_pd]; exact hpdx1
    -- d 在 face f 中，故 findFaceDarts L d = f
    have hdf : d ∈ f := by
      have h : d = (nextEl f)^[n] zk := hcongr_n
      rw [h]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkf n
    have hffd : findFaceDarts L d = f := by
      rw [hf]
      exact Kepler.Text.TameSpine.aq10_memFindFaceImpFacesEq hL.1 hdf
    -- `fList L d = nextEl r d = x`，满足 nextCoreFst 前提
    have hfd : fList L d = nextEl r d := by
      have hd' : d = (nextEl f)^[n] zk := hcongr_n
      calc fList L d
          _ = nextEl (findFaceDarts L d) d := rfl
          _ = nextEl f d := by rw [hffd]
          _ = nextEl f ((nextEl f)^[n] zk) := by rw [hd']
          _ = (nextEl f)^[n + 1] zk := by rw [Function.iterate_succ_apply']
          _ = x := hf_n1_x
          _ = nextEl r d := hnextd.symm
    have hf0 : ¬ finalList L r := by
      have h := Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
      rwa [Kepler.Text.Reduction5.rtrans_zero] at h
    have hcore := Kepler.Text.Reduction5.nextCoreFst L hL hgn hm hf0 hdmemr hfd
    -- 导出 core L r 在 x.1 处的自环
    have hloop : nextEl (core L r) x.1 = x.1 := by
      rw [hdx1, hnextd] at hcore
      exact hcore
    -- core L r 无重且含 x.1 与 zk.1 两个不同元
    have hcund : (core L r).Nodup :=
      Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
    have hxcore : x.1 ∈ core L r := by
      have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpx hxpx
      have hheadD : px.headD (0, 0) = px.head! := by
        cases px with
        | nil => exact absurd rfl hpxne
        | cons a t => rfl
      have hmem : (px.headD (0, 0)).1 ∈ core L r :=
        List.mem_map_of_mem (f := fun (l : List Dart) => (l.headD (0, 0)).1) hpx
      rw [hheadD] at hmem
      rwa [← h] at hmem
    have hzkcore : zk.1 ∈ core L r := by
      obtain ⟨py, hpy, hzkpy⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hzkr
      have hpynil : py ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r py hpy
      have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hzkpy
      have hheadD : py.headD (0, 0) = py.head! := by
        cases py with
        | nil => exact absurd rfl hpynil
        | cons a t => rfl
      have hmem : (py.headD (0, 0)).1 ∈ core L r :=
        List.mem_map_of_mem (f := fun (l : List Dart) => (l.headD (0, 0)).1) hpy
      rw [hheadD] at hmem
      rwa [← h] at hmem
    have hzkxcore : zk.1 ≠ x.1 := hne
    -- 自环 ⇒ core L r = [x.1]，与含 zk.1 矛盾
    have hsingle : core L r = [x.1] :=
      Kepler.Text.MoreLemma2Island1.nextElRefl hxcore hloop hcund
    rw [hsingle] at hzkcore
    simp at hzkcore
    exact absurd hzkcore hzkxcore

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.partOfXHead
