/-
  Kepler.Text.Reduction5J5IndexfYltSizelPre — J5-5 `indexf_y_lt_sizel_pre` 公开件
  （HOL more_lemma2.hl:890–940）。

  陈述逐字：六前提（good_list / good_list_nodes / is_restricted / marked_list /
  transform_count = k / 0 < k）⇒
  `indexf (ztrans L N r x (k-1)) x (find_face L x) < sizel (core L r)`
  （`sizel ↦ List.length`、`PRE k ↦ k-1`）。

  **证明体来源**：B1（aq13 ml14）在 `Reduction5J5K3Indexf2.lean` 内以 private
  `indexfZkXltCore` 证过同一陈述（弧计数：`pplhulj3Gen'` 排 `zk = w` →
  `preIndexfZkXSucc` 给 `indexf zk w f = m+1` → `cases2Chain` 沿 f 走 →
  弧上 m 个 dart 均单点 atom（`memPartsSingleton`）且 zk 的 part 不在像集 →
  `m+1 ≤ |parts| = |core|`）。私有件跨文件不可见，本文件**平迁证明体**；
  公开陈述按 HOL 六前提形补 `hres`，`haq` 由 `TameSpine.aqiunpp` 内部现拼。
  已落库文件零改动。

  差异记录：私件陈述为 `(hgn) (haq) (hm) (hk) (hk0)`，无 `hres`；本公开件按
  HOL 换为 `(hgn) (hres) (hm) (hk) (hk0)`，`haq` 入证明体。结论逐字一致。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零写入。
-/
import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreSetup
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreCount
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelAtom
import Kepler.Text.TameSpine.Reduction3J5ZTranMeF
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.PwssratFace
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction5McCore
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4
import Kepler.Text.Reduction1W2e

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList findFaceDarts eList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- `AqiunppSlot` 的无条件实例（HOL `AQIUNPP3` 槽；同家族惯例）。 -/
private theorem aqSlotOf (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn N r x hm i => Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i

/-- 一般 `i` 的 PPLHULJ3（f 世界；`pplhulj3V0` 在状态 i 实例化）。 -/
private theorem pplhulj3Gen' (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    indexf (nextEl (findFaceDarts L x) x) (ytrans L N r x i) (findFaceDarts L x)
      < indexf (nextEl (findFaceDarts L x) x) (ztrans L N r x i) (findFaceDarts L x) := by
  have hm_i : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have h := Kepler.Text.Reduction4Idx.pplhulj3V0 L hL hgn hunL hm_i hf
  simpa only [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.ztrans] using h

/-- **HOL `indexf_y_lt_sizel_pre`**（more_lemma2.hl:890–940）：
六前提 + `0 < k` ⇒ `indexf (ztrans (k-1)) x (find_face x) < sizel (core L r)`。 -/
theorem indexfYltSizelPre (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hk : transformCount L N r x = k) (hk0 : 0 < k) :
    indexf (ztrans L N r x (k - 1)) x (findFaceDarts L x) < (core L r).length := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL := aqSlotOf L hL
  have hf : ¬ finalList L r := Kepler.Text.TameSpine.preNotFinal L hk hk0
  set f : List Dart := findFaceDarts L x with hfdef
  set w : Dart := nextEl f x with hwdef
  set zk : Dart := ztrans L N r x (k - 1) with hzkdef
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxf : x ∈ f := by
    rw [hfdef]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hwf : w ∈ f := by
    rw [hwdef]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxf
  have hfnd : f.Nodup := by
    rw [hfdef]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hzkr : zk ∈ r := by
    rw [hzkdef]
    exact Kepler.Text.TameSpine.preZkMemR L hL hgn haq hm hk hk0
  have hzkf : zk ∈ f := by
    rw [hzkdef, hfdef]
    exact Kepler.Text.TameSpine.preZkMemF L hL hgn haq hm hk hk0
  -- zk ≠ w（一般 i 的 PPLHULJ3 在 i = k-1 处）
  have hne : zk ≠ w := by
    intro hzw
    have hnfprev : ¬ finalList L (rtrans L N r x (k - 1)) :=
      Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)
    have hlt3 := pplhulj3Gen' L hL hgn hm (k - 1) hnfprev
    have hzw' : ztrans L N r x (k - 1) = nextEl (findFaceDarts L x) x := by
      rw [← hzkdef, ← hwdef]
      exact hzw
    rw [hzw'] at hlt3
    have h0 : indexf (nextEl (findFaceDarts L x) x) (nextEl (findFaceDarts L x) x)
        (findFaceDarts L x) = 0 :=
      Kepler.Text.Reduction4.indexfRefl (by rw [← hfdef]; exact hwf)
    rw [h0] at hlt3
    omega
  -- indexf zk w f = indexf zk x f + 1
  have hq : indexf zk w f = indexf zk x f + 1 := by
    have hne' : ztrans L N r x (k - 1) ≠ nextEl f x := by
      rw [← hzkdef, ← hwdef]
      exact hne
    have hltw : indexf (ztrans L N r x (k - 1)) (nextEl f x) f < f.length :=
      Kepler.Text.Reduction4.indexf_lt_length_of_mem
        (by rw [← hzkdef]; exact hzkf) (by rw [← hwdef]; exact hwf)
    have h := Kepler.Text.TameSpine.preIndexfZkXSucc L hL hgn haq hm hk hk0
      (f := f) hfdef.symm hne' hltw
    rw [hzkdef, hwdef]
    exact h.symm
  set m : ℕ := indexf zk x f with hmdef
  have hmlt : m < f.length := by
    rw [hmdef]
    exact Kepler.Text.Reduction4.indexf_lt_length_of_mem hzkf hxf
  -- 弧行走：r 沿 f（CASES2 链形）
  have hwalk : ∀ n, n ≤ indexf zk w f → (nextEl r)^[n] zk = (nextEl f)^[n] zk := by
    intro n hn
    have hn' : n ≤ indexf (ztrans L N r x (k - 1)) w f := by
      simpa [hzkdef] using hn
    have h := Kepler.Text.TameSpine.cases2Chain L hL hgn haq hm
      (f := f) (w := w) hfdef.symm hwdef.symm hk hk0 hn'
    rwa [← hzkdef] at h
  -- 每个 j < m：[(nextEl f)^(j+1) zk] ∈ parts
  have hmemφ : ∀ j ∈ Finset.range m,
      [(nextEl f)^[j + 1] zk] ∈ (parts L r).toFinset := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    set d : Dart := (nextEl f)^[j + 1] zk with hddef
    have hdf : d ∈ f := by
      rw [hddef]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkf (j + 1)
    have hdr : d ∈ r := by
      rw [hddef, ← hwalk (j + 1) (by omega)]
      exact Kepler.Text.TameSpine.memPowerNextEl hzkr (j + 1)
    have hdD : d ∈ listOfDarts L := by
      apply Kepler.Text.TameLp.mem_darts_of_mem_findFace L (d := x)
      rw [← hfdef]
      exact hdf
    have hfj : findFaceDarts L ((nextEl f)^[j] zk) = f := by
      have hmemj : (nextEl f)^[j] zk ∈ findFaceDarts L x := by
        rw [← hfdef]
        exact Kepler.Text.TameSpine.memPowerNextEl hzkf j
      have h := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hmemj
      rwa [hfdef] at h
    -- 前驱 = (nextEl r)^j zk
    have hprev : prevEl r d = (nextEl r)^[j] zk := by
      rw [hddef, ← hwalk (j + 1) (by omega), Function.iterate_succ_apply' (nextEl r) j zk]
      exact Kepler.Text.TameLp.prevEl_nextEl hnd (Kepler.Text.TameSpine.memPowerNextEl hzkr j)
    have hprevD : prevEl r d ∈ listOfDarts L := by
      rw [hprev]
      exact (hm.2.1.2.2.2.1 r hm.2.2.1 _ (Kepler.Text.TameSpine.memPowerNextEl hzkr j)).1
    -- 两处 f 步 + 边非退化
    have hstepPrev : nextEl r (prevEl r d) = fList L (prevEl r d) := by
      rw [hprev]
      have huf : (nextEl r)^[j] zk ∈ f := by
        rw [hwalk j (by omega)]
        exact Kepler.Text.TameSpine.memPowerNextEl hzkf j
      have hfindU : findFaceDarts L ((nextEl r)^[j] zk) = f := by
        have hmem : (nextEl r)^[j] zk ∈ findFaceDarts L x := by
          rw [← hfdef]
          exact huf
        have h := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hmem
        rw [hfdef]
        exact h
      rw [show fList L ((nextEl r)^[j] zk) = nextEl f ((nextEl r)^[j] zk) from by
        show nextEl (findFaceDarts L ((nextEl r)^[j] zk)) ((nextEl r)^[j] zk)
          = nextEl f ((nextEl r)^[j] zk)
        rw [hfindU]]
      rw [← Function.iterate_succ_apply' (nextEl r) j zk, hwalk (j + 1) (by omega),
        hwalk j (by omega), Function.iterate_succ_apply']
    have hstepD : nextEl r d = fList L d := by
      rw [hddef]
      have hdf' : (nextEl f)^[j + 1] zk ∈ f :=
        Kepler.Text.TameSpine.memPowerNextEl hzkf (j + 1)
      have hfindD : findFaceDarts L ((nextEl f)^[j + 1] zk) = f := by
        have hmem : (nextEl f)^[j + 1] zk ∈ findFaceDarts L x := by
          rw [← hfdef]
          exact hdf'
        have h := Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hmem
        rw [hfdef]
        exact h
      rw [show fList L ((nextEl f)^[j + 1] zk) = nextEl f ((nextEl f)^[j + 1] zk) from by
        show nextEl (findFaceDarts L ((nextEl f)^[j + 1] zk)) ((nextEl f)^[j + 1] zk)
          = nextEl f ((nextEl f)^[j + 1] zk)
        rw [hfindD]]
      rw [← hwalk (j + 1) (by omega), ← Function.iterate_succ_apply' (nextEl r) (j + 1) zk,
        hwalk (j + 2) (by omega), hwalk (j + 1) (by omega),
        show j + 2 = (j + 1) + 1 from by omega, Function.iterate_succ_apply']
    have hhead : d = r.head! ∨
        nextEl r (prevEl r d) ≠ fList L (eList (prevEl r d)) := by
      right
      rw [hstepPrev]
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL
        hm.1.edgeNondegenerate hprevD
    have hlast : d = r.getLast! ∨ nextEl r d ≠ fList L (eList d) := by
      right
      rw [hstepD]
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL
        hm.1.edgeNondegenerate hdD
    exact List.mem_toFinset.mpr
      (Kepler.Text.TameSpine.memPartsSingleton L hnd hdr hhead hlast)
  -- 单射（r 弧/f 弧上的 power 定位）
  have hinj : ∀ a ∈ Finset.range m, ∀ b ∈ Finset.range m,
      [(nextEl f)^[a + 1] zk] = [(nextEl f)^[b + 1] zk] → a = b := by
    intro a ha b hb heq
    have hal : a < m := Finset.mem_range.mp ha
    have hbl : b < m := Finset.mem_range.mp hb
    have hpow : (nextEl f)^[a + 1] zk = (nextEl f)^[b + 1] zk :=
      List.singleton_inj.mp heq
    have hda : (nextEl f)^[a + 1] zk ∈ f :=
      Kepler.Text.TameSpine.memPowerNextEl hzkf (a + 1)
    have hdb : (nextEl f)^[b + 1] zk ∈ f :=
      Kepler.Text.TameSpine.memPowerNextEl hzkf (b + 1)
    have hlt_a : a + 1 < f.length := by omega
    have hlt_b : b + 1 < f.length := by omega
    have hia : indexf zk ((nextEl f)^[a + 1] zk) f = a + 1 :=
      Kepler.Text.MoreLemma2Island1.nextElnIndexf hzkf hda hfnd
        ((Kepler.Text.Reduction5.iterateInstEq f zk (a + 1)).symm) hlt_a
    have hib : indexf zk ((nextEl f)^[b + 1] zk) f = b + 1 :=
      Kepler.Text.MoreLemma2Island1.nextElnIndexf hzkf hdb hfnd
        ((Kepler.Text.Reduction5.iterateInstEq f zk (b + 1)).symm) hlt_b
    rw [hpow] at hia
    omega
  -- zk 的 part 不在像集
  obtain ⟨pz, hpz, hzkpz⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hnd hzkr
  have hN : Kepler.Text.ChainLists.normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hpzfst : pz.head!.1 = zk.1 := by
    have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hrN hpz hzkpz
    exact h.symm
  have hpzNot : pz ∉ (Finset.range m).image (fun j => [(nextEl f)^[j + 1] zk]) := by
    intro hpzS
    obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hpzS
    have hjlt : j < m := Finset.mem_range.mp hj
    -- pz = [d_j] ⇒ zk = d_j
    have hzkin : zk ∈ pz := hzkpz
    rw [← hpj] at hzkin
    have hzkd : zk = (nextEl f)^[j + 1] zk := by simpa using hzkin
    -- d_j 的 indexf 是 j+1，与 zk 自身 0 相抵
    have hdjf : (nextEl f)^[j + 1] zk ∈ f :=
      Kepler.Text.TameSpine.memPowerNextEl hzkf (j + 1)
    have hltj : j + 1 < f.length := by omega
    have hidxj : indexf zk ((nextEl f)^[j + 1] zk) f = j + 1 :=
      Kepler.Text.MoreLemma2Island1.nextElnIndexf hzkf hdjf hfnd
        ((Kepler.Text.Reduction5.iterateInstEq f zk (j + 1)).symm) hltj
    have h0 : indexf zk zk f = 0 := Kepler.Text.Reduction4.indexfRefl hzkf
    rw [← hzkd] at hidxj
    omega
  -- 计数：m+1 ≤ |parts| = |core|
  have hsub : (insert pz ((Finset.range m).image (fun j => [(nextEl f)^[j + 1] zk])))
      ⊆ (parts L r).toFinset := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact List.mem_toFinset.mpr hpz
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact hmemφ j hj
  have hcardIn : ((Finset.range m).image (fun j => [(nextEl f)^[j + 1] zk])).card = m := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hcardT : (insert pz ((Finset.range m).image (fun j => [(nextEl f)^[j + 1] zk]))).card
      = m + 1 := by
    rw [Finset.card_insert_of_notMem hpzNot, hcardIn]
  have hle := Finset.card_le_card hsub
  rw [hcardT] at hle
  have h1 : (parts L r).toFinset.card ≤ (parts L r).length :=
    Kepler.Text.TameSpine.partsToFinsetCardLe L r
  have h2 : (core L r).length = (parts L r).length :=
    Kepler.Text.TameSpine.coreLengthEqParts L r
  omega

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.indexfYltSizelPre
