/-
  Kepler.Text.TameSpine.Reduction3J5BetwnPreFace — tame-corr nb36：J5-6
  `betwn_pre_face`（HOL betwn_corek_z_x.hl:405，body 98 行）。

  陈述（HOL 逐字）：七前提下
  `betwn (find_face L x) (ztrans (k-1)) x = betwn r (ztrans (k-1)) x`。

  路线（nb33/nb34 定稿，nb35 修正 hnext 末元缺口）：
  `TameSpine.aqs_eq_last_next`（AQ12.hl:39；**参数序 `{s}{r}`，r 在前**）三料：
  - `hmem` ← `memBetwnPreFace`（在库 a778a176）；
  - `hlast` ← `lastBetwnPreFace`（在库 bbc298e4）；
  - `hnext` 拆两支（`aq10_nextElBetwnSame` 的前提 `nextEl f d ∈ between f zk x`
    在 `d` 为弧末元时不成立，必须分开）：
    支 A（`d` 非 Br 末元）：`aq10_eqMemNextElLast` 反推两侧
    `nextEl · d ∈ between ·`，`aq10_nextElBetwnSame` 把 `nextEl between` 折到
    外层表；`indexfN` 定位 `d = (nextEl f)^[n] zk`（r 侧由 `cases2Chain` 弧同步），
    `cases2Chain` 在 `n + 1` 对齐；
    支 B（`d = LAST Br`，经 `lastBetwnPreFace` 亦 `= LAST Bf`）：
    `nextElLastHd` 把 `nextEl between d` 折成 `head!`，`HD_BETWN2` 折成
    `nextEl · zk`，末对齐由 `cases2Chain` 在 `1` 处给出。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5MemBetwnPreFace
import Kepler.Text.TameSpine.Reduction3J5LastBetwnPreFace
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.JcajyduAqLeaf12A
import Kepler.Text.TameSpine.TameList71
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.Reduction3J5IndexfSizeZTranPre
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.JcajyduRed2Tav2
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

/-- `next_el` 步进的 `indexf` 模移位（`TameSpine.indexf` 形；`Reduction3CoreSplitNormal:394`
私件克隆，本文件自包含第三次重写）。 -/
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

/-- **HOL `betwn_pre_face`**（betwn_corek_z_x.hl:405）：
七前提下两条弧表相等。 -/
theorem betwnPreFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    between (findFaceDarts L x) (ztrans L N r x (k - 1)) x
      = between r (ztrans L N r x (k - 1)) x := by
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
  -- 端点 indexf 的界（`hmle` 的模坍缩支需要 `m < f.length`）
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
  -- 弧段重合（CASES2 迭代形）
  have hcongr : ∀ n, n ≤ Kepler.Text.TameSpine.indexf zk w f →
      (nextEl r)^[n] zk = (nextEl f)^[n] zk := by
    intro n hn
    have hn' : n ≤ Kepler.Text.Reduction5.indexf zk w f := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact hn
    exact Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm (f := f) (w := w)
      hf.symm hw.symm hk hk0 hn'
  -- 三料：成员等价 / LAST 等价（均在库）
  have hmem := Kepler.Text.TameSpine.memBetwnPreFace L hL hgn hres hm hk hk0 hne
  have hlast := Kepler.Text.TameSpine.lastBetwnPreFace L hL hgn hres hm hk hk0 hne
  refine Kepler.Text.TameSpine.aqs_eq_last_next
    (s := between f zk x) (r := between r zk x)
    (Kepler.Graphs.between_distinct hrnd) (Kepler.Graphs.between_distinct hfnd)
    hmem ?_ hlast
  -- hnext：末元/非末元两支（nb35 修正）
  intro d hd
  have hdb : d ∈ between r zk x := (hmem d).mp hd
  have hBfne : between f zk x ≠ [] := List.ne_nil_of_mem hd
  have hBrne : between r zk x ≠ [] := List.ne_nil_of_mem hdb
  have hlastEq : (between f zk x).getLast hBfne
      = (between r zk x).getLast hBrne := by
    rw [← getLastBangEqGetLast hBfne, ← getLastBangEqGetLast hBrne]
    exact hlast
  by_cases hdlast : d = (between r zk x).getLast hBrne
  · -- 支 B：`d` 是弧末元（两侧同）
    have hdlastF : d = (between f zk x).getLast hBfne := by
      rw [hdlast, hlastEq]
    have hbf : nextEl (between f zk x) d = (between f zk x).head! := by
      rw [hdlastF]
      exact Kepler.Text.TameSpine.nextElLastHd
        (Kepler.Graphs.between_distinct hfnd) hBfne
    have hbr : nextEl (between r zk x) d = (between r zk x).head! := by
      rw [hdlast]
      exact Kepler.Text.TameSpine.nextElLastHd
        (Kepler.Graphs.between_distinct hrnd) hBrne
    rw [hbf, hbr,
      Kepler.Text.TameSpine.HD_BETWN2 hzkf hxf hzkx hfnd hBfne,
      Kepler.Text.TameSpine.HD_BETWN2 hzkr hxr hzkx hrnd hBrne]
    have hb : 1 ≤ Kepler.Text.TameSpine.indexf zk w f := by omega
    have hb' : 1 ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) w f := by
      rwa [Kepler.Text.Reduction3.indexf_eq_spine]
    have h1 : (nextEl r)^[1] zk = (nextEl f)^[1] zk :=
      Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm (f := f) (w := w)
        hf.symm hw.symm hk hk0 hb'
    simpa using h1.symm
  · -- 支 A：`d` 非末元，两侧 `nextEl` 都折到外层弧表
    have hdlastF : d ≠ (between f zk x).getLast hBfne := by
      intro h
      exact hdlast (h.trans hlastEq)
    have hnf : nextEl f d ∈ between f zk x :=
      (Kepler.Text.TameSpine.aq10_eqMemNextElLast hzkx hzkf hxf hd hfnd).mpr
        (fun h => hdlastF h.symm)
    have hnr : nextEl r d ∈ between r zk x :=
      (Kepler.Text.TameSpine.aq10_eqMemNextElLast hzkx hzkr hxr hdb hrnd).mpr
        (fun h => hdlast h.symm)
    rw [Kepler.Text.TameSpine.aq10_nextElBetwnSame hzkx hzkf hxf hd hnf hfnd,
      Kepler.Text.TameSpine.aq10_nextElBetwnSame hzkx hzkr hxr hdb hnr hrnd]
    -- 位置定位 + `cases2Chain` 在 `n + 1` 对齐
    obtain ⟨hposd, hltm⟩ :=
      (Kepler.Text.TameSpine.indexfBetwnEq hzkx hfnd hzkf hxf).mp hd
    have hdle : Kepler.Text.TameSpine.indexf zk d f
        ≤ Kepler.Text.TameSpine.indexf zk w f := by omega
    have hdf : d ∈ f := Kepler.Text.TameSpine.betwnMem hd
    have hiter_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk d f] zk = d :=
      Kepler.Text.TameSpine.indexfN hzkf hdf hfnd
    have hiter_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk d f] zk = d :=
      (hcongr _ hdle).trans hiter_f
    have hsucc_f : (nextEl f)^[Kepler.Text.TameSpine.indexf zk d f + 1] zk
        = nextEl f d := by
      rw [Function.iterate_succ_apply', hiter_f]
    have hsucc_r : (nextEl r)^[Kepler.Text.TameSpine.indexf zk d f + 1] zk
        = nextEl r d := by
      rw [Function.iterate_succ_apply', hiter_r]
    rw [← hsucc_f, ← hsucc_r]
    have hb : Kepler.Text.TameSpine.indexf zk d f + 1
        ≤ Kepler.Text.TameSpine.indexf zk w f := by omega
    have hb' : Kepler.Text.TameSpine.indexf zk d f + 1
        ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) w f := by
      rwa [Kepler.Text.Reduction3.indexf_eq_spine]
    exact (Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm (f := f) (w := w)
      hf.symm hw.symm hk hk0 hb').symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.betwnPreFace
