/-
  Kepler.Text.TameSpine.Reduction3J5LastBetwnPreFace — tame-corr nb34：J5-6
  `last_betwn_pre_face`（HOL betwn_corek_z_x.hl:309，body 96 行）。

  陈述（HOL 逐字）：七前提下
  `LAST (betwn (find_face L x) (ztrans (k-1)) x) = LAST (betwn r (ztrans (k-1)) x)`；
  本仓 LAST 编码 = `List.getLast!`（先例 `betwnGetLastOfIndexfSuccG`）。

  路线（比 nb32 冻结表的 prevEl 路线更短）：
  - `sizeBetwn`（TameList3:1031，prod 世界）给两侧 `length = indexf zk x · - 1`；
    r 侧端点 indexf 由 `hidxXr`（`indexf zk x r = indexf zk x f`）归一；
  - 空支 `m = 1`（`zk ≠ x` ⇒ `m ≠ 0`）⇒ 双空 ⇒ `getLast!` 均 default；
  - 非空支 `m ≥ 2`：`d := (nextEl f)^[m-1] zk`，`nextElnIndexf` 定位
    `indexf zk d f = m-1`，`indexfBetwnEq.mpr` 给 `d ∈ between`，克隆
    `CoreSplitNormal:721 betwnGetLastOfIndexfSuccG` 得 `getLast! = d`；
  - r 侧同法；`cases2Chain` 在 `m-1` 处对齐（`m-1 ≤ m ≤ p`）。

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

/-- `getLast!` 与非空证明版 `getLast` 一致（`Reduction3CoreSplitNormal:128` 私件克隆）。 -/
private theorem getLastBangEqGetLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

/-- `next_el` 步进的 `indexf` 模移位（`TameSpine.indexf` 形）。 -/
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

/-- 「弧内元的 `indexf` 恰为 `indexf a b - 1`」⇒ 它是弧的末元
（`Reduction3CoreSplitNormal:721 betwnGetLastOfIndexfSuccG` 克隆）。 -/
private theorem betwnGetLastOfIndexfSuccG {α : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] [Inhabited α] {f : List α} {a b d : α} (hab : a ≠ b)
    (ha : a ∈ f) (hb : b ∈ f) (hd : d ∈ between f a b) (hnd : f.Nodup)
    (hidx : Kepler.Text.TameSpine.indexf a d f
      = Kepler.Text.TameSpine.indexf a b f - 1) :
    (between f a b).getLast! = d := by
  have hBne : between f a b ≠ [] := fun h => by rw [h] at hd; simp at hd
  have h1 : (between f a b).idxOf d + 1 = Kepler.Text.TameSpine.indexf a d f :=
    Kepler.Text.TameSpine.indexlBetwn hnd ha hb hd
  have h2 : (between f a b).length = Kepler.Text.TameSpine.indexf a b f - 1 :=
    Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
  have h3 : (between f a b).idxOf d = (between f a b).length - 1 := by omega
  have hmemlast : (between f a b).getLast! ∈ between f a b := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_mem hBne
  have hgl : (between f a b).getLast!
      = (between f a b)[(between f a b).length - 1]'(by omega) := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_eq_getElem hBne
  have hidxl : (between f a b).idxOf ((between f a b).getLast!)
      = (between f a b).length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem (Kepler.Graphs.between_distinct hnd)
      (i := (between f a b).length - 1) (by omega)
  exact (List.idxOf_inj hmemlast).mp (by rw [hidxl, h3])

/-- **HOL `last_betwn_pre_face`**（betwn_corek_z_x.hl:309）。 -/
theorem lastBetwnPreFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    (between (findFaceDarts L x) (ztrans L N r x (k - 1)) x).getLast!
      = (between r (ztrans L N r x (k - 1)) x).getLast! := by
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
  -- 界
  have hm_lt : Kepler.Text.TameSpine.indexf zk x f < f.length := by
    have h := Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hxf
    rwa [Kepler.Text.Reduction3.indexf_eq_spine] at h
  have hltr : Kepler.Text.TameSpine.indexf zk w f < r.length := by
    have h := indexfSizeZTranPre L hL hgn hres hm hk hk0 hne
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
    have hf' : ¬ Kepler.Text.Reduction5.finalList L
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
  -- 端点 x 在 r 上的 indexf 定位
  have hidxXr : Kepler.Text.TameSpine.indexf zk x r = Kepler.Text.TameSpine.indexf zk x f := by
    have hiter_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk x f] zk = x :=
      Kepler.Text.TameSpine.indexfN hzkf hxf hfnd
    have hiter_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk x f] zk = x :=
      (hcongr _ hmle).trans hiter_f
    have hlt : Kepler.Text.TameSpine.indexf zk x f < r.length := by omega
    exact Kepler.Text.TameSpine.nextElnIndexf hzkr hxr hrnd hiter_r hlt
  -- m > 0（zk ≠ x）
  have hmpos : 0 < Kepler.Text.TameSpine.indexf zk x f := by
    by_contra hle
    have hz0 : Kepler.Text.TameSpine.indexf zk x f = 0 := by omega
    have h1 := Kepler.Text.TameSpine.indexfN hzkf hxf hfnd
    rw [hz0] at h1
    exact hzkx (by simpa using h1)
  -- 两侧长度 = m - 1
  have hlenF : (between f zk x).length = Kepler.Text.TameSpine.indexf zk x f - 1 :=
    Kepler.Text.TameSpine.sizeBetwn hfnd hzkf hxf hzkx
  have hlenR : (between r zk x).length = Kepler.Text.TameSpine.indexf zk x f - 1 := by
    rw [Kepler.Text.TameSpine.sizeBetwn hrnd hzkr hxr hzkx, hidxXr]
  by_cases hm1 : Kepler.Text.TameSpine.indexf zk x f = 1
  · -- 空支：双空，getLast! 均 default
    have hFn : between f zk x = [] :=
      List.eq_nil_of_length_eq_zero (by rw [hlenF, hm1])
    have hRn : between r zk x = [] :=
      List.eq_nil_of_length_eq_zero (by rw [hlenR, hm1])
    rw [hFn, hRn]
  · -- 非空支：末元 = 弧内位置 m-1 的幂迭代
    have hm2 : 2 ≤ Kepler.Text.TameSpine.indexf zk x f := by omega
    have hdFf : (nextEl f)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk ∈ f :=
      Kepler.Text.TameSpine.memPowerNextEl hzkf _
    have hdFidx : Kepler.Text.TameSpine.indexf zk
        ((nextEl f)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk) f
        = Kepler.Text.TameSpine.indexf zk x f - 1 :=
      Kepler.Text.TameSpine.nextElnIndexf hzkf hdFf hfnd rfl (by omega)
    have hdFmem : (nextEl f)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk
        ∈ between f zk x := by
      refine (Kepler.Text.TameSpine.indexfBetwnEq hzkx hfnd hzkf hxf).mpr ⟨?_, ?_⟩
      · rw [hdFidx]
        omega
      · rw [hdFidx]
        omega
    have hlastF : (between f zk x).getLast!
        = (nextEl f)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk :=
      betwnGetLastOfIndexfSuccG hzkx hzkf hxf hdFmem hfnd hdFidx
    have hdRr : (nextEl r)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk ∈ r :=
      Kepler.Text.TameSpine.memPowerNextEl hzkr _
    have hdRidx : Kepler.Text.TameSpine.indexf zk
        ((nextEl r)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk) r
        = Kepler.Text.TameSpine.indexf zk x r - 1 := by
      rw [hidxXr]
      exact Kepler.Text.TameSpine.nextElnIndexf hzkr hdRr hrnd rfl (by omega)
    have hdRmem : (nextEl r)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk
        ∈ between r zk x := by
      refine (Kepler.Text.TameSpine.indexfBetwnEq hzkx hrnd hzkr hxr).mpr ⟨?_, ?_⟩
      · rw [hdRidx, hidxXr]
        omega
      · rw [hdRidx]
        omega
    have hlastR : (between r zk x).getLast!
        = (nextEl r)^[Kepler.Text.TameSpine.indexf zk x f - 1] zk :=
      betwnGetLastOfIndexfSuccG hzkx hzkr hxr hdRmem hrnd hdRidx
    rw [hlastF, hlastR]
    exact (hcongr _ (by omega)).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.lastBetwnPreFace
