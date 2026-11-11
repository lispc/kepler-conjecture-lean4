/-
  Kepler.Text.Reduction5J5K2A2Split — Lane A2.2（nb50）：
  AQ8 两件 uniq 的链层桥 + `zNotEqYtransV0` + `final_assumption_split_normal_list` 本体。

  ┌─ 归属对账（HOL）────────────────────────────────────────────────
  │ ① `z_not_eq_ytrans_v0`（HOJODCM.hl:89）→ `zNotEqYtransV0`
  │ ② `uniq_fst_split_normal_parts`（AQ8.hl:2382）→ `uniqFstSplitNormalParts`
  │ ③ `uniq_snd_split_normal_parts`（AQ8.hl:530）→ `uniqSndSplitNormalParts`
  │ ④ `final_assumption_split_normal_list`（reduction4.hl:1094–1275）
  │    → `finalAssumptionSplitNormalList`
  └────────────────────────────────────────────────────────────────

  ┌─ ④ 的路线（HOL 双支）─────────────────────────────────────────
  │ `bet = between f y0 z0`。
  │ · `bet ≠ []`：`newVs = bet.map FST` 非空，取 `b`；集合差假设 ⇒ `b ∉ N` 的
  │   FST 表；`coreSplitNormalListThm` 的显式 `core s.1/s.2` ⇒ `b` 在两片里；
  │   `quotientListElements` ⇒ 若某片 ∈ quotientList 则 `b` 在 N 的 FST 表，矛盾。
  │ · `bet = []`：`s.2 = [z0] ++ … ++ [y0]`、`s.1 = [y1] ++ … ++ [z1]`；
  │   `nextElLastHd` 给 `nextEl s.2 y0 = z0` / `nextEl s.1 z1 = y1`；
  │   `nextCoreNeFST` 于 `(ntrans 1, s.2)`/`(ntrans 1, s.1)` ⇒
  │   `nextEl (core s.2) y0.1 = z0.1` / `nextEl (core s.1) z1.1 = y1.1`；
  │   `splitNormalListIndex2/1Lemma` 给 `core s.2/s.1 = core r`；
  │   撞 `hny/hnz`（`FST z1 = FST z0`/`FST y1 = FST y0` 由
  │   `fstEqPrevZtransV0`/`fstEqNextYtransV0`）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.TameSpine.JcajyduAqLeaf8W4d
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ae
import Kepler.Text.TameSpine.Reduction3J5CorePartsWiring
import Kepler.Text.Reduction5J5Shallow
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.Reduction5J5SplitNorm
import Kepler.Text.Reduction5Ml1W4
import Kepler.Text.TameSpine.TameList35
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.ChainBridgeParts
import Kepler.Text.ChainSpineBridge
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans ytrans transformCount core finalList parts splitNormalList)
open Kepler.Text.TameLp (elementsOfList)

/-- `getLast!` 与非空证明版 `getLast` 一致（私有克隆）。 -/
private theorem getLastBangEqGetLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

/-- **HOL `HOJODCM.z_not_eq_ytrans_v0`**（HOJODCM.hl:89）：
`ztrans 0 ≠ ytrans 0`。 -/
theorem zNotEqYtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    ztrans L N r x 0 ≠ ytrans L N r x 0 := by
  intro h
  have hk0 : 0 < transformCount L N r x :=
    Nat.pos_of_ne_zero (transformCountNon0OfMarked L hL hgn haq hm hnf)
  exact finalAssumptionYNeZ L hL hgn hres haq (transformCount L N r x) hm hnf rfl
    0 hk0 h.symm

/-- **HOL `AQ8.uniq_fst_split_normal_parts`**（AQ8.hl:2382）。 -/
theorem uniqFstSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    (core L (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have h := Kepler.Text.TameSpine.aq8w4d_uniqFstSplitNormalParts L hL hgn hmS hfS
  simpa only [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine,
    ← Kepler.Text.TameSpine.coreEqPartsHeadFst] using h

/-- **HOL `AQ8.uniq_snd_split_normal_parts`**（AQ8.hl:530）。 -/
theorem uniqSndSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    (core L (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have h := Kepler.Text.TameSpine.aq8w3ae_coreSNDNodup L hL hgn hmS hfS
  simpa only [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine,
    ← Kepler.Text.TameSpine.coreEqPartsHeadFst] using h

/-- **HOL `final_assumption_split_normal_list`**（reduction4.hl:1094–1275）：
`bet ≠ []` 支由 `coreSplitNormalListThm` + 集合差假设排除；`bet = []` 支
由 `splitNormalListIndex1/2Lemma` + 两条 `not_next` 假设排除。 -/
theorem finalAssumptionSplitNormalList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hny : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L (rtrans L N r x 0)) (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1)
    (hnz : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠ (ytrans L N r x 0).1)
    (hdiff : {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
        z ∉ N.flatten.map (fun d => d.1)} =
      {z : ℕ | z ∈ (between (findFaceDarts L x) (ytrans L N r x 0)
        (ztrans L N r x 0)).map (fun d => d.1)}) :
    (let s := splitNormalList L r (findFaceDarts L x) (ytrans L N r x 0)
        (prevEl r (ztrans L N r x 0))
     core L s.1 ∉ quotientList L N ∧ core L s.2 ∉ quotientList L N) := by
  set y : Dart := ytrans L N r x 0 with hy
  set z : Dart := ztrans L N r x 0 with hz
  set z1 : Dart := prevEl r z with hz1
  set s : List Dart × List Dart := splitNormalList L r (findFaceDarts L x) y z1 with hs
  have hrnd : r.Nodup := Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hface : findFaceDarts L (Kepler.Text.Reduction5.ly L r x) = findFaceDarts L x :=
    findFaceXEqY L hL hgn hm hnf
  have hyly : Kepler.Text.Reduction5.ly L r x = ytrans L N r x 0 := rfl
  have hzlz : lz L N r x = ztrans L N r x 0 := rfl
  have hz_next : nextEl r z1 = z := by
    rw [hz1]
    rw [Kepler.Text.Reduction5.nextElInstEq r (prevEl r z)]
    exact Kepler.Text.Reduction5.nextPrevId hrnd z
  by_cases hbet : between (findFaceDarts L x) y z = []
  · -- `bet = []`
    -- 结构件：`bet = []` 时两片的显式形
    have hs2 : s.2 = [z] ++ between r z y ++ [y] := by
      simp [hs, splitNormalList, hz_next, hbet]
    have hs1 : s.1 = [nextEl r y] ++ between r (nextEl r y) z1 ++ [z1] := by
      simp [hs, splitNormalList, hz_next, hbet]
    have hk0 : 0 < k := by
      have h := transformCountNon0OfMarked L hL hgn haq hm hnf
      rw [hk] at h
      exact Nat.pos_of_ne_zero h
    have hyz : y.1 ≠ z.1 := finalAssumptionFstYNeqFstZ L hL hgn hres k hm hnf hk
    have hy1fst : (nextEl r y).1 = y.1 := fstEqNextYtransV0 L hL hgn hm hnf hy.symm
    have hz1fst : z1.1 = z.1 := by
      rw [hz1]
      exact fstEqPrevZtransV0 L hL hgn hm hnf rfl rfl
    have hz1y1 : z1.1 ≠ (nextEl r y).1 := by rw [hz1fst, hy1fst]; exact hyz.symm
    -- F2
    have hf2 : core L s.2 ∉ quotientList L N := by
      intro hmem
      have hEq : core L s.2 = core L r :=
        splitNormalListIndex2Lemma L hL hgn hres haq k hm hnf hk (by simpa [hs, hy, hz, hz1] using hmem)
      have hne2 : s.2 ≠ [] := by rw [hs2]; simp
      have hnd2 : s.2.Nodup := by
        have hm1 : Kepler.Text.ChainLists.markedList L hL
            (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
        exact (List.nodup_flatten.mp hm1.2.1.1).1 _ (by
          simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
            sndMemRtran1 L hL hgn hm hnf)
      have hlast2 : s.2.getLast! = y := by
        rw [hs2]
        have hne : [z] ++ between r z y ++ [y] ≠ [] := by simp
        rw [getLastBangEqGetLast hne, List.getLast_eq_getElem]
        simp
      have hgl2 : s.2.getLast hne2 = y := by
        rw [← getLastBangEqGetLast hne2, hlast2]
      have hhead2 : s.2.head! = z := by
        rw [hs2]
        simp
      have hnext2 : nextEl s.2 y = z := by
        have h := Kepler.Text.TameSpine.nextElLastHd (α := Dart) hnd2 hne2
        rw [hgl2, hhead2] at h
        exact h
      have hy2 : y ∈ s.2 := by rw [hs2]; simp
      have hcu2 : (core L s.2).Nodup := by
        simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
          uniqSndSplitNormalParts L hL hgn hres haq hm hnf
      have hcore2 : nextEl (core L s.2) y.1 = z.1 := by
        have hm1 : Kepler.Text.ChainLists.markedList L hL
            (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
        have hN1 : Kepler.Text.ChainLists.normalList L hL (ntrans L N r x 1) := hm1.2.1
        have hr1 : s.2 ∈ ntrans L N r x 1 := by
          simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
            sndMemRtran1 L hL hgn hm hnf
        exact nextCoreNeFST L hL hgn hres hN1 hr1 hy2 hcu2 hyz hnext2
      rw [hEq] at hcore2
      exact (hny hbet) hcore2
    -- F1
    have hf1 : core L s.1 ∉ quotientList L N := by
      intro hmem
      have hEq : core L s.1 = core L r :=
        splitNormalListIndex1Lemma L hL hgn hres haq k hm hnf hk (by simpa [hs, hy, hz, hz1] using hmem)
      have hne1 : s.1 ≠ [] := by rw [hs1]; simp
      have hnd1 : s.1.Nodup := by
        have hm1 : Kepler.Text.ChainLists.markedList L hL
            (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
        exact (List.nodup_flatten.mp hm1.2.1.1).1 _ (by
          simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
            fstMemRtran1 L hL hgn hm hnf)
      have hlast1 : s.1.getLast! = z1 := by
        rw [hs1]
        have hne : [nextEl r y] ++ between r (nextEl r y) z1 ++ [z1] ≠ [] := by simp
        rw [getLastBangEqGetLast hne, List.getLast_eq_getElem]
        simp
      have hgl1 : s.1.getLast hne1 = z1 := by
        rw [← getLastBangEqGetLast hne1, hlast1]
      have hhead1 : s.1.head! = nextEl r y := by
        rw [hs1]
        simp
      have hnext1 : nextEl s.1 z1 = nextEl r y := by
        have h := Kepler.Text.TameSpine.nextElLastHd (α := Dart) hnd1 hne1
        rw [hgl1, hhead1] at h
        exact h
      have hz1mem : z1 ∈ s.1 := by rw [hs1]; simp
      have hcu1 : (core L s.1).Nodup := by
        simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
          uniqFstSplitNormalParts L hL hgn hres haq hm hnf
      have hcore1 : nextEl (core L s.1) z1.1 = (nextEl r y).1 := by
        have hm1 : Kepler.Text.ChainLists.markedList L hL
            (ntrans L N r x 1) (rtrans L N r x 1) x := haq hgn N r x hm 1
        have hN1 : Kepler.Text.ChainLists.normalList L hL (ntrans L N r x 1) := hm1.2.1
        have hr1 : s.1 ∈ ntrans L N r x 1 := by
          simpa only [hs, ← hface, hy, ← hyly, hz1, hz, ← hzlz] using
            fstMemRtran1 L hL hgn hm hnf
        exact nextCoreNeFST L hL hgn hres hN1 hr1 hz1mem hcu1 hz1y1 hnext1
      rw [hEq] at hcore1
      rw [hz1fst, hy1fst] at hcore1
      exact (hnz hbet) hcore1
    exact ⟨hf1, hf2⟩
  · -- `bet ≠ []`
    have hnewVs_ne : (between (findFaceDarts L x) y z).map (fun d => d.1) ≠ [] := by
      intro h
      exact hbet (List.map_eq_nil_iff.mp h)
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hnewVs_ne
    have hb_diff : b ∈ {z : ℕ | z ∈ (ntrans L N r x 1).flatten.map (fun d => d.1) ∧
        z ∉ N.flatten.map (fun d => d.1)} := by
      rw [hdiff]
      exact hb
    have hbN : b ∉ N.flatten.map (fun d => d.1) := hb_diff.2
    -- coreSplitNormalListThm 的显式形
    have hcs := coreSplitNormalListThm L hL hgn hm hnf
    unfold Kepler.Text.Reduction5.coreSplitNormalList at hcs
    simp only at hcs
    have hb1 : b ∈ core L s.1 := by
      rw [show s = splitNormalList L r (findFaceDarts L x)
        (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x)) from by
        simp only [hs, hy, ← hyly, hz1, hz, ← hzlz]]
      rw [hcs.1]
      exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr hb))
    have hb2 : b ∈ core L s.2 := by
      rw [show s = splitNormalList L r (findFaceDarts L x)
        (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x)) from by
        simp only [hs, hy, ← hyly, hz1, hz, ← hzlz]]
      rw [hcs.2]
      exact List.mem_append.mpr (Or.inr hb)
    -- `quotientList L N` 的元素都在 `N.flatten.map FST` 里
    have hnotMem : ∀ q ∈ quotientList L N, b ∈ q → False := by
      intro q hq hbq
      rw [Kepler.Text.MoreLemma2Island1.quotientListCore] at hq
      obtain ⟨r', hr'N, hr'q⟩ := List.mem_map.mp hq
      have hbq' : b ∈ core L r' := by rw [hr'q]; exact hbq
      rw [Kepler.Text.TameSpine.coreEqPartsHeadFst] at hbq'
      obtain ⟨p, hp, hbp⟩ := List.mem_map.mp hbq'
      have hr'nd : r'.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r' hr'N
      have hr'ne : r' ≠ [] := hm.2.1.2.1 r' hr'N
      have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r' p hp
      have hpr : p.head! ∈ r' := by
        rw [← Kepler.Text.MoreLemma2Island2.partsFlatten L hr'nd hr'ne]
        exact List.mem_flatten.mpr ⟨p, hp, List.head!_mem_self hpne⟩
      have hb_in : b ∈ N.flatten.map (fun d => d.1) := by
        rw [← hbp]
        exact List.mem_map.mpr ⟨p.head!,
          List.mem_flatten.mpr ⟨r', hr'N, hpr⟩, rfl⟩
      exact hbN hb_in
    exact ⟨fun hq => hnotMem _ hq hb1, fun hq => hnotMem _ hq hb2⟩

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.Reduction5.zNotEqYtransV0
#print axioms Kepler.Text.Reduction5.uniqFstSplitNormalParts
#print axioms Kepler.Text.Reduction5.uniqSndSplitNormalParts
#print axioms Kepler.Text.Reduction5.finalAssumptionSplitNormalList
