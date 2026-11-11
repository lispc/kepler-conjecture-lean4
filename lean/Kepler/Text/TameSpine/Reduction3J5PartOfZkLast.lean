/-
  Kepler.Text.TameSpine.Reduction3J5PartOfZkLast — tame-corr nb40：J5-6 主件 P2 子论证 A
  （`betwn_corek_z_x` HOL betwn_corek_z_x.hl:535 原态侧子论证 A）。

  命题：`zk := ztrans L N r x (k-1)` 所在 atom（`py ∈ parts L r`、`zk ∈ py`）
  的 `LAST` 恰为 `zk`（HOL 的 GSUBGOAL `LAST pz = zk`，:591–:640）。

  路线（nb39 §4.1 定稿）：
  - 弧引擎（第 4 次自包含重写）：`indexfTNextEl` + `pplhulj3V0` 排除模坍缩 +
    `hmle` + `cases2Chain` 迭代形 `hcongr`；
  - `nextEl r zk = nextEl f zk` ← `hcongr` 在 n = 1；
  - `fList L zk = nextEl f zk` ← `mem_find_face_imp_faces_eq`（`findFaceDarts L zk = f`）；
  - `¬ (nextEl r zk = fList L (eList zk))` ← `loopList` 槽 + `edgeNondegFXorNi`；
  - 双支：`zk = r.getLast` 支（`partsFlatten` + `memLast` + `lastFlatten2` +
    `uniqSublistUnique` ⇒ `py = LAST (parts L r)` ⇒ `py.getLast! = zk`）；
    else 支（`conditionLastParts.mpr` 直给 `zk = py.getLast!`）。

  剩余（下一轮）：子论证 B `px.head! = x` + P3 装配。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5CorePartsWiring
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.Reduction3J5IndexfSizeZTranPre
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.TameLp
import Kepler.Text.Reduction4
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList eList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans transformCount parts)

/-- `getLast!` 与非空证明版 `getLast` 一致（`Reduction3CoreSplitNormal:128` 私件克隆）。 -/
private theorem getLastBangEqGetLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

/-- `next_el` 步进的 `indexf` 模移位（`TameSpine.indexf` 形；同款私件第 4 份）。 -/
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

/-- **P2 子论证 A**（HOL `betwn_corek_z_x.hl:591–:640`）：`zk` 是其 atom 的末元。 -/
theorem partOfZkGetLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1)
    {py : List Dart} (hpy : py ∈ parts L r)
    (hzkpy : ztrans L N r x (k - 1) ∈ py) :
    py.getLast! = ztrans L N r x (k - 1) := by
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
  have hrne : r ≠ [] := List.ne_nil_of_mem hxr
  -- 端点 indexf 的界
  have hm_lt : Kepler.Text.TameSpine.indexf zk x f < f.length := by
    have h := Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hxf
    rwa [Kepler.Text.Reduction3.indexf_eq_spine] at h
  -- (a) `indexf zk w f` 的 +1 模移位
  have hnextIdx : Kepler.Text.TameSpine.indexf zk w f
      = (Kepler.Text.TameSpine.indexf zk x f + 1) % f.length := by
    have h := indexfTNextEl hfnd hzkf hxf
    rwa [← hw] at h
  -- (b) 模坍缩支排除
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
  -- 弧段重合
  have hcongr : ∀ n, n ≤ Kepler.Text.TameSpine.indexf zk w f →
      (nextEl r)^[n] zk = (nextEl f)^[n] zk := by
    intro n hn
    have hn' : n ≤ Kepler.Text.Reduction5.indexf zk w f := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact hn
    exact Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm (f := f) (w := w)
      hf.symm hw.symm hk hk0 hn'
  -- `nextEl r zk = nextEl f zk`
  have hnextRF : nextEl r zk = nextEl f zk := by
    have h := hcongr 1 (by omega)
    simpa using h
  -- `fList L zk = nextEl f zk`（faces 相等 + fList 定义级）
  have hff : findFaceDarts L zk = f := by
    rw [hf]
    exact Kepler.Text.TameSpine.aq10_memFindFaceImpFacesEq hL.1 hzkf
  have hfl : fList L zk = nextEl f zk := by
    show nextEl (findFaceDarts L zk) zk = nextEl f zk
    rw [hff]
  -- `¬ (nextEl r zk = fList L (eList zk))`
  have hloop := hm.2.1.2.2.2.1 r hm.2.2.1
  have hneEL : nextEl r zk ≠ fList L (eList zk) := by
    intro hcon
    exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hres.edgeNondegenerate
      (hloop zk hzkr).1 ((hfl.trans hnextRF.symm).symm ▸ hcon)
  -- 双支
  by_cases hzkLast : zk = r.getLast hrne
  · -- 支 A1：`zk = LAST r` ⇒ `py = LAST (parts L r)`
    have hspne : parts L r ≠ [] := List.ne_nil_of_mem hpy
    have hpynil : py ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r py hpy
    have hlastne : (parts L r).getLast hspne ≠ [] :=
      Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ (List.getLast_mem hspne)
    have hspflat : (parts L r).flatten = r :=
      Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne
    have hspflnd : (parts L r).flatten.Nodup := by rw [hspflat]; exact hrnd
    have hlastFlat : ((parts L r).getLast hspne).getLast hlastne = r.getLast hrne := by
      have hne1 : (parts L r).flatten ≠ [] := by rw [hspflat]; exact hrne
      have h := Kepler.Text.TameSpine.lastFlatten2 (r := parts L r) hspne hlastne hne1
      have h2 : (parts L r).flatten.getLast hne1 = r.getLast hrne :=
        List.getLast_congr hne1 hrne hspflat
      exact h.symm.trans h2
    have hzklp : zk ∈ (parts L r).getLast hspne := by
      have hz : zk = ((parts L r).getLast hspne).getLast hlastne := by
        rw [hzkLast, hlastFlat]
      rw [hz]
      exact List.getLast_mem hlastne
    have hpyEq : py = (parts L r).getLast hspne :=
      Kepler.Text.TameSpine.uniqSublistUnique (parts L r) hspflnd py hpy
        ((parts L r).getLast hspne) (List.getLast_mem hspne)
        ⟨zk, hzkpy, hzklp⟩
    rw [hpyEq, getLastBangEqGetLast hlastne, hlastFlat, ← hzkLast]
  · -- 支 A2：`conditionLastParts.mpr`
    have hzkLastBang : zk ≠ r.getLast! := by
      rw [getLastBangEqGetLast hrne]
      exact hzkLast
    exact ((Kepler.Text.Reduction5.conditionLastParts hpy hzkpy hzkLastBang hrne hrnd).mp
      hneEL).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.partOfZkGetLast
