/-
  Kepler.Text.Reduction5Ml1W2 — J5-2 K2 门控（主机 8b）本体 W2a：setup 与两片 parts 桥。

  ┌─ 归属对账（HOL More_lemma1.hl :2029–:2450）──────────────────────
  │ :2029–:2100 主件展开 + y/z/z1/y1/w/f/g 定义 + 成员事实
  │ :2100–:2200 PPLHULJ_v0 / z≠y / QRDYXYJ / parts 存在与 FST
  │ :2200–:2300 py/pz 定位、parts_betwn 实例、s = [y1]++(betwn r y1 z1)++[z1]
  │ :2300–:2450 f1 半 parts 代数与 LAST/HD 归属（W2b，见下节）
  │ 本文件（W2a 段）落：两片 parts 拆解（f1 = aq12w 链形、f2 = aq13w3 链形）+
  │ 主件 setup 记忆包（y/z/z1/y1 成员、面成员、FST 等式、z≠y）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（DIFFERS，按 GSUBGOAL 语句重推，不逐行转写）────────────────
  │ HOL 的 g = rev(flatten(map nd W)) 与 `uniq_fst_split_norm` 两段在本树已由
  │ tame-corr 铺装为 **parts 层**结论：aq12w（f1 片 = rev(map G W) ++ parts s）/
  │ aq13w3（f2 片 = parts s' ++ map [·] W）。本文件只做链形桥（partsSpine→parts、
  │ splitNormalListSpine→splitNormalList、lYSpine/lZSpine→ly/lz），供 W4 装配。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12W
import Kepler.Text.TameSpine.JcajyduAqLeaf13W3
import Kepler.Text.TameSpine.JcajyduAqSplit1B
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.PwssratFace
import Kepler.Text.PwssratMemberBase
import Kepler.Text.ChainBridgeParts
import Kepler.Text.ChainSpineBridge
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.Reduction5J5SplitNorm
import Kepler.Text.Reduction5Ml1Leaves

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- 链 marked + ¬final ⇒ spine 全套（私有打包；同 Reduction5J5SplitNorm 私件）。 -/
private theorem ml1SpineFull (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (∀ l ∈ L, l.Nodup) ∧ Kepler.Text.TameSpine.MarkedListSpineFull hL N r x ∧
      ¬ Kepler.Text.TameSpine.finalListSpine L r := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  exact ⟨hunL,
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)⟩

/-- `AqiunppSlot` 的无条件链形（`aqiunpp` 逐点；HOL AQIUNPP 由 TAV2 无条件件供）。 -/
private theorem ml1AqSlot (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn N r x hm i => Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i

/-! ### §1 W2a：两片 parts 拆解（aq12w / aq13w3 的链形） -/

/-- **W2a-1（HOL Aq12 `cat_fst_split_normal_parts`，:3236）链形**：
`parts L split.1 = rev(map (nd·).reverse W) ++ parts L s`，
`W = betwn f y z`、`s = [y1] ++ (betwn r y1 z1 ++ [z1])`（y = l'y、z = l'z、
z1 = prev_el r z、y1 = next_el r y）。 -/
theorem ml1SplitFstParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    parts L (splitNormalList L r (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).1
      = ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse
        ++ parts L ([nextEl r (ly L r x)] ++
            (between r (nextEl r (ly L r x)) (prevEl r (lz L N r x)) ++
              [prevEl r (lz L N r x)])) := by
  obtain ⟨hunL, hmS, hfS⟩ := ml1SpineFull L hL hgn hm hnf
  have h := Kepler.Text.TameSpine.aq12w_catFstSplitNormalParts L hL hgn hmS hfS
  simp only [← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine] at h
  exact h

/-- **W2a-2（HOL Aq13 `cat_snd_split_normal_parts`，:180）链形**：
`parts L split.2 = parts L s' ++ map [·] W`，
`s' = [z] ++ (betwn r z y ++ [y])`（f2 半，W3 复用形）。 -/
theorem ml1SplitSndParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    parts L (splitNormalList L r (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).2
      = parts L ([lz L N r x] ++
            (between r (lz L N r x) (ly L r x) ++ [ly L r x]))
        ++ (between (findFaceDarts L x) (ly L r x) (lz L N r x)).map (fun d => [d]) := by
  obtain ⟨hunL, hmS, hfS⟩ := ml1SpineFull L hL hgn hm hnf
  have hpp := Kepler.Text.Reduction4Idx.pplhuljV0 L hL hgn hunL hm hnf
  have hySp : Kepler.Text.TameSpine.lYSpine L r x ∈ findFaceDarts L x := by
    rw [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf]
    exact hpp.1
  have hfy : findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hySp
  have h := Kepler.Text.TameSpine.aq13w3_catSndSplitNormalParts L hL hgn hmS hfS
  rw [hfy] at h
  simp only [← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine] at h
  exact h

/-! ### §2 W2a：主件 setup 记忆包（HOL :2040–:2160） -/

/-- **W2a-3**：主件 setup 的成员与 FST 事实：
`y ∈ r`、`z ∈ r`、`z1 ∈ r`、`y1 ∈ r`；`y,z ∈ f`；`y1.1 = y.1`、`z1.1 = z.1`、`z ≠ y`。
（y = l'y、z = ztrans 0 = l'z、z1 = prev_el r z、y1 = next_el r y、f = find_face。） -/
theorem ml1SetupMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    ly L r x ∈ r ∧ ztrans L N r x 0 ∈ r ∧ prevEl r (ztrans L N r x 0) ∈ r ∧
    nextEl r (ly L r x) ∈ r ∧
    ly L r x ∈ findFaceDarts L x ∧ ztrans L N r x 0 ∈ findFaceDarts L x ∧
    (nextEl r (ly L r x)).1 = (ly L r x).1 ∧
    (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1 ∧
    ztrans L N r x 0 ≠ ly L r x := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have haq := ml1AqSlot L hL
  have hnf0 : ¬ finalList L (rtrans L N r x 0) := by
    rwa [Kepler.Text.Reduction5.rtrans_zero]
  have hyr : ly L r x ∈ r := by
    have h := Kepler.Text.Reduction4Idx.ytransMemRtrans L hL haq hgn 0 hm
    rw [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.rtrans_zero] at h
    exact h
  have hzr : ztrans L N r x 0 ∈ r := by
    have h := Kepler.Text.Reduction4Idx.memZtransRtrans L hL haq hgn hunL 0 hm hnf0
    rw [Kepler.Text.Reduction5.rtrans_zero] at h
    exact h
  have hz1r : prevEl r (ztrans L N r x 0) ∈ r := memPrevEl hzr
  have hy1r : nextEl r (ly L r x) ∈ r := Kepler.Text.TameLp.nextEl_mem_of_mem hyr
  have hpp := Kepler.Text.Reduction4Idx.pplhuljV0 L hL hgn hunL hm hnf
  have hy1fst : (nextEl r (ly L r x)).1 = (ly L r x).1 :=
    fstEqNextYtransV0 L hL hgn hm hnf rfl
  have hz1fst : (prevEl r (ztrans L N r x 0)).1 = (ztrans L N r x 0).1 :=
    fstEqPrevZtransV0 L hL hgn hm hnf rfl rfl
  have hzy : ztrans L N r x 0 ≠ ly L r x := by
    have h := Kepler.Text.Reduction4Idx.zNotEqYtrans L hL haq hgn hunL 0 hm hnf0
    rw [Kepler.Text.Reduction5.ytrans_def, Kepler.Text.Reduction5.rtrans_zero] at h
    exact h
  exact ⟨hyr, hzr, hz1r, hy1r, hpp.1, hpp.2.1, hy1fst, hz1fst, hzy⟩


/-! ### §3 W2a：py/pz 定位与 parts_betwn 实例（HOL :2160–:2300） -/

/-- **W2a-4**：`y.1 ≠ z.1`（HOL QRDYXYJ_list 第 5 合取；setup 的 FST 判别）。 -/
theorem ml1FstNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (ly L r x).1 ≠ (lz L N r x).1 := by
  obtain ⟨hunL, hmS, hfS⟩ := ml1SpineFull L hL hgn hm hnf
  have h := Kepler.Text.TameSpine.aqs_fstYNeFstZ L hL hgn hunL hmS hfS
  rwa [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf] at h

/-- **W2a-5**：`py/pz` 成员定位（HOL :2130–:2200）：
`parts L r` 中含 `y1`/`z1` 的原子 py/pz，其块首 FST 分别 = `y.1`/`z.1`；
py ≠ pz；且 `parts L (betwn r (LAST py) (HD pz)) = betwn (parts L r) py pz`
（`partsBetwnChain` 实例；块首单射由 `quotientList` 的 Nodup 供）。 -/
theorem ml1PartsA (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    ∃ py pz : List Dart, py ∈ parts L r ∧ pz ∈ parts L r ∧
      nextEl r (ly L r x) ∈ py ∧ prevEl r (ztrans L N r x 0) ∈ pz ∧
      py.head!.1 = (ly L r x).1 ∧ pz.head!.1 = (ztrans L N r x 0).1 ∧
      py ≠ pz ∧
      parts L (between r py.getLast! pz.head!) = between (parts L r) py pz := by
  obtain ⟨hunL, hmS, hfS⟩ := ml1SpineFull L hL hgn hm hnf
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, hzf, hy1fst, hz1fst, hzy⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hfstne : (ly L r x).1 ≠ (lz L N r x).1 := ml1FstNe L hL hgn hm hnf
  have hrN : r ∈ N := hm.2.2.1
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hrN
  obtain ⟨py, hpy, hy1py⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hy1r
  obtain ⟨pz, hpz, hz1pz⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hz1r
  have hpyfst : py.head!.1 = (ly L r x).1 := by
    rw [← hy1fst]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hrN hpy hy1py).symm
  have hpzfst : pz.head!.1 = (ztrans L N r x 0).1 := by
    rw [← hz1fst]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hrN hpz hz1pz).symm
  have hpyz : py ≠ pz := by
    intro hcon
    have h1 : (ly L r x).1 = (ztrans L N r x 0).1 := by
      rw [← hpyfst, ← hpzfst, hcon]
    refine hfstne ?_
    show (ly L r x).1 = (lz L N r x).1
    exact h1
  have hy1z1 : (nextEl r (ly L r x)).1 ≠ (prevEl r (ztrans L N r x 0)).1 := by
    rw [hy1fst, hz1fst]
    exact hfstne
  have hcore : ((parts L r).map (fun q => q.head!.1)).Nodup := by
    have hmem : (parts L r).map (fun p => (p.headD (0, 0)).1) ∈ quotientList L N := by
      unfold quotientList coreList
      exact List.mem_map_of_mem (List.mem_map_of_mem hrN)
    have hD := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm _ hmem
    have hcongr : (parts L r).map (fun p => (p.headD (0, 0)).1)
        = (parts L r).map (fun q => q.head!.1) :=
      List.map_congr_left (fun p hp => by
        cases p with
        | nil => exact absurd rfl (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ hp)
        | cons a t => rfl)
    rwa [hcongr] at hD
  have hparts := partsBetwnChain L hL hm.2.1 hm.1.edgeNondegenerate hrN
    (sp := parts L r) rfl hcore hpy hpz hy1py hz1pz hy1z1
  exact ⟨py, pz, hpy, hpz, hy1py, hz1pz, hpyfst, hpzfst, hpyz, hparts⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1SplitFstParts
#print axioms Kepler.Text.Reduction5.ml1SplitSndParts
#print axioms Kepler.Text.Reduction5.ml1SetupMem
#print axioms Kepler.Text.Reduction5.ml1FstNe
#print axioms Kepler.Text.Reduction5.ml1PartsA
