/-
  Kepler.Text.Reduction5Ml1W3b — 主机 8b W3b：f2 半收口（HEAD 归属、块表 HD/LAST、indexf 界）
  （HOL more_lemma1.hl:2851–:3010，含 :3032 的 indexf 界）。

  ┌─ 件目与 HOL 锚 ────────────────────────────────────────────────
  │ `ml1SplitSndEq`（`split.2 = s2 ++ betwn f y z`） | Aq13:180 的 dart 层形 |
  │ `ml1PartEndHead2`（f2 HEAD 侧内核） | :2828–:2940 |
  │ `ml1Py1Head`（f2 的 `HD py1 = HD py`） | :2828 |
  │ `ml1S2HdParts`（`HD(parts L s2) = pz1`） | :2942–:2959 |
  │ `ml1S2LastParts`（`LAST(parts L s2) = py1`） | :2960–:2975 |
  │ `ml1S2PartsNe`（`pz1 ≠ py1`） | :3010–:3020 |
  │ `ml1IndexOfS2`（`indexf (LAST pz) (HD py) s2 ≤ indexf (LAST pz) y s2`） | :3032–:3047 |
  │ f1 侧收口（§3，W4 装配前置）：`ml1S1HdParts`/`ml1S1LastParts`/`ml1S1PartsNe` | :2447–:2546 |
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（DIFFERS）────────────────────────────────────────────────
  │ W2b-B4 内核的镜像：s → s2、split.1 → split.2、nextElCat2 → nextElCat1、
  │ 对端 z1 → y；`ml1S2PartsNe` 的 FST 判别走 state-1 `parts_fst`；
  │ `ml1IndexOfS2` 为 B6 的镜像（two `indexf_split_HD_flatten` + `indexfRefl`）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5Ml1W3a
import Kepler.Text.TameSpine.JcajyduAqLeaf12D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- `split.2 = s2 ++ betwn f y z` 的 dart 层展开式（Aq13:180 的 `f2` 半）。 -/
theorem ml1SplitSndEq (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hrnd : r.Nodup) :
    (splitNormalList L r (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).2
      = ml1S2 L N r x ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0) := by
  have hnextPrev : nextEl r (prevEl r (lz L N r x)) = ztrans L N r x 0 := by
    rw [Kepler.Text.Reduction5.nextElInstEq, Kepler.Text.Reduction5.nextPrevId hrnd]
    rfl
  show (([nextEl r (prevEl r (lz L N r x))] ++
      (between r (nextEl r (prevEl r (lz L N r x))) (ly L r x) ++ [ly L r x]))
    ++ between (findFaceDarts L x) (ly L r x) (nextEl r (prevEl r (lz L N r x))))
    = ml1S2 L N r x ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)
  rw [hnextPrev]
  rfl

/-- **W3b 内核（f2 HEAD 侧）**：`y ∈ p1`、`y ∈ p`、`p ∈ parts L r`、
`p1 ∈ parts L s2` 且 `p1 ∈ parts L split.2` ⇒ `p1.head! = p.head!`。
（W2b `ml1PartEndHead` 的镜像：z1 → y、s → s2、split.1 → split.2、
nextElCat2 → nextElCat1。） -/
theorem ml1PartEndHead2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {p p1 : List Dart} (hp : p ∈ parts L r)
    (hp1 : p1 ∈ parts L (ml1S2 L N r x))
    (hp1s2 : p1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2)
    (hyp1 : ly L r x ∈ p1) (hyp : ly L r x ∈ p) :
    p1.head! = p.head! := by
  obtain ⟨hyr, hzr, -, -, hyf, -, -, -, hzy⟩ := ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hzr
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hp1ne : p1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p1 hp1
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p hp
  have hpnd : p.Nodup := by
    have hflat : (parts L r).flatten.Nodup := by
      rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]
      exact hrnd
    exact (List.nodup_flatten.mp hflat).1 p hp
  -- state-1 normalList 与 split.2 成员/无重
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf2mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.sndMemRtran1 L hL hgn hm hnf
  have hf2nd : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2.Nodup :=
    (List.nodup_flatten.mp hn1.1).1 _ hf2mem
  have hsplit2 := ml1SplitSndEq L (N := N) (r := r) (x := x) hrnd
  -- h := p1.head! 的 FST = y 的 FST
  have hheadmem : p1.head! ∈ p1 := Kepler.Text.TameSpine.aqs_headMem hp1ne
  have hhead_s : p1.head! ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hp1 _ hheadmem
  have hhead_r : p1.head! ∈ r := ml1S2MemImpR L hL hgn hm hnf hhead_s
  have hhfst : p1.head!.1 = (ly L r x).1 :=
    (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hp1s2 hyp1).symm
  -- p.head! 的 FST = y 的 FST
  have hpzfst : (ly L r x).1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hyp
  -- dl := (prevEl (parts L s2) p1).getLast!
  have hspnd : (parts L (ml1S2 L N r x)).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hsnd hsne
  have hpn1mem : prevEl (parts L (ml1S2 L N r x)) p1 ∈ parts L (ml1S2 L N r x) :=
    Kepler.Text.Reduction5.memPrevEl hp1
  have hnextParts : nextEl (parts L (ml1S2 L N r x))
        (prevEl (parts L (ml1S2 L N r x)) p1) = p1 := by
    rw [← nextElListInstEq]
    exact Kepler.Text.Reduction5.nextPrevId hspnd p1
  have hpn1ne : prevEl (parts L (ml1S2 L N r x)) p1 ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ _ hpn1mem
  have hdlmem : (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
      ∈ prevEl (parts L (ml1S2 L N r x)) p1 :=
    Kepler.Text.TameSpine.aqs_getLastMem hpn1ne
  have hdls : (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
      ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hpn1mem _ hdlmem
  have hdlr : (prevEl (parts L (ml1S2 L N r x)) p1).getLast! ∈ r :=
    ml1S2MemImpR L hL hgn hm hnf hdls
  -- nextEl s2 dl = p1.head!
  have hnexts : nextEl (ml1S2 L N r x)
        (prevEl (parts L (ml1S2 L N r x)) p1).getLast! = p1.head! := by
    rw [Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast L hsnd hsne hpn1mem
      hdlmem rfl, hnextParts]
  -- dl ≠ y
  have hdlneY : (prevEl (parts L (ml1S2 L N r x)) p1).getLast! ≠ ly L r x := by
    intro h
    have h2 : nextEl (ml1S2 L N r x) (ly L r x) = p1.head! := by
      rw [← h]
      exact hnexts
    rw [← ml1S2Last (r := r) (N := N) (x := x)] at h2
    rw [Kepler.Text.TameSpine.nextElLast hsnd hsne] at h2
    rw [ml1S2Head] at h2
    have h3 : (ztrans L N r x 0).1 = (ly L r x).1 := by
      rw [h2]
      exact hhfst
    exact ml1FstNe L hL hgn hm hnf h3.symm
  -- 反证 h = p.head!
  by_contra hne
  -- dl.1 ≠ y.1
  have hFstNe : (prevEl (parts L (ml1S2 L N r x)) p1).getLast!.1
      ≠ (ly L r x).1 := by
    intro hfst
    obtain ⟨p', hp', hdlp'⟩ :=
      Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hdlr
    have hdlpzfst : (prevEl (parts L (ml1S2 L N r x)) p1).getLast!.1 = p'.head!.1 :=
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp' hdlp'
    have hp'p : p' = p := by
      have hfst' : p'.head!.1 = p.head!.1 := by
        rw [← hdlpzfst, hfst]
        exact hpzfst
      exact List.inj_on_of_nodup_map
        (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hp' hp hfst'
    have hdlp : (prevEl (parts L (ml1S2 L N r x)) p1).getLast! ∈ p := by
      rw [← hp'p]
      exact hdlp'
    by_cases hlast : (prevEl (parts L (ml1S2 L N r x)) p1).getLast! = p.getLast!
    · -- dl = LAST p：nextEl 链给 h = p.head!，撞反证假设
      have hqmem : nextEl (parts L r) p ∈ parts L r :=
        Kepler.Text.TameLp.nextEl_mem_of_mem hp
      have hnextq : nextEl r (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          = (nextEl (parts L r) p).head! := by
        rw [hlast]
        exact Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast L hrnd hrne hp
          (Kepler.Text.TameSpine.aqs_getLastMem hpne) rfl
      have h2 : (nextEl (parts L r) p).head! = p1.head! := by
        have h3 := hnexts
        rw [Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hyr hzr hzy.symm hdls
          (by unfold ml1S2; rfl) hdlneY] at h3
        rw [hnextq] at h3
        exact h3
      have hqfst : (nextEl (parts L r) p).head!.1 = p.head!.1 := by
        rw [h2]
        exact hhfst.trans hpzfst
      have hqp : nextEl (parts L r) p = p :=
        List.inj_on_of_nodup_map (ml1PartsHeadFstNodup L hL hm hm.2.2.1)
          hqmem hp hqfst
      rw [hqp] at h2
      exact hne h2.symm
    · -- dl ≠ LAST p：parts_next_unlast 与 state-1 normal_condition 矛盾
      have hpzSp : p ∈ Kepler.Text.TameSpine.partsSpine L r := by
        rwa [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
      have hnextr : nextEl r (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          = fList L (eList (prevEl (parts L (ml1S2 L N r x)) p1).getLast!) := by
        rw [Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hrnd hrne hp hdlp hlast]
        exact Kepler.Text.TameSpine.partsNextUnlast L hrnd hrne p hpzSp
          (prevEl (parts L (ml1S2 L N r x)) p1).getLast! hdlp hlast
      have hp1s2' : prevEl (parts L (ml1S2 L N r x)) p1
          ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).2 := by
        rw [ml1SplitSndParts L hL hgn hm hnf]
        exact List.mem_append_left _ hpn1mem
      have hneg1 : ¬(nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).2
              (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          = fList L (eList (prevEl (parts L (ml1S2 L N r x)) p1).getLast!)) :=
        (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hn1
          hm.1.edgeNondegenerate hf2mem hp1s2' hdlmem).mpr rfl
      have hdlneLast : (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          ≠ (ml1S2 L N r x).getLast! := by
        intro h
        exact hdlneY (by rw [h, ml1S2Last (r := r) (N := N) (x := x)])
      have hnextsplit : nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).2 (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          = nextEl (ml1S2 L N r x)
              (prevEl (parts L (ml1S2 L N r x)) p1).getLast! := by
        rw [hsplit2]
        exact Kepler.Text.TameSpine.nextElCat1
          (s := ml1S2 L N r x)
          (t := between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0))
          hsnd hdls hdlneLast
      have hnexts2 : nextEl (ml1S2 L N r x)
            (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
          = nextEl r (prevEl (parts L (ml1S2 L N r x)) p1).getLast! :=
        Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hyr hzr hzy.symm hdls
          (by unfold ml1S2; rfl) hdlneY
      apply hneg1
      rw [hnextsplit, hnexts2]
      exact hnextr
  -- h ∈ p（块首 FST 单射定位）
  have hhead_p : p1.head! ∈ p := by
    obtain ⟨p'', hp'', hhp''⟩ :=
      Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hhead_r
    have h1 : p1.head!.1 = p''.head!.1 :=
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp'' hhp''
    have h2 : p''.head!.1 = p.head!.1 := by
      rw [← h1]
      exact hhfst.trans hpzfst
    have h3 : p'' = p := List.inj_on_of_nodup_map
      (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hp'' hp h2
    rw [← h3]
    exact hhp''
  -- pd := prevEl p h；nextEl 单射 ⇒ pd = dl，撞 dl 的 FST
  have hpdmem : prevEl p p1.head! ∈ p :=
    Kepler.Text.Reduction5.memPrevEl hhead_p
  have hpdmemr : prevEl p p1.head! ∈ r :=
    ml1PartsMemImp L hrnd hrne hp _ hpdmem
  have hnextpd : nextEl p (prevEl p p1.head!) = p1.head! := by
    rw [Kepler.Text.Reduction5.nextElInstEq, Kepler.Text.Reduction5.nextPrevId hpnd]
  have hpdne : prevEl p p1.head! ≠ p.getLast! := by
    intro h
    rw [h, Kepler.Text.TameSpine.nextElLast hpnd hpne] at hnextpd
    exact hne hnextpd.symm
  have hnextpd_r : nextEl r (prevEl p p1.head!) = p1.head! := by
    rw [Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hrnd hrne hp hpdmem hpdne]
    exact hnextpd
  have hdl_next_r : nextEl r (prevEl (parts L (ml1S2 L N r x)) p1).getLast!
      = p1.head! := by
    rw [← Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hyr hzr hzy.symm hdls
      (by unfold ml1S2; rfl) hdlneY]
    exact hnexts
  have hpd_eq : prevEl p p1.head! = (prevEl (parts L (ml1S2 L N r x)) p1).getLast! :=
    Kepler.Text.TameSpine.nextElInjOfNodup hrnd hpdmemr hdlr
      (by rw [hnextpd_r, hdl_next_r])
  have hpdfst : (prevEl p p1.head!).1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hpdmem
  exact hFstNe (by rw [← hpd_eq]; exact hpdfst.trans hpzfst.symm)

/-- **W3b-1（HOL :2828，`HD py1 = HD py`）**：
f2 半列表中含 `y` 的块 `py1` 的首元 = `parts L r` 中含 `y` 的块 `py` 的首元。 -/
theorem ml1Py1Head (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py : List Dart} (hpy : py ∈ parts L r)
    (hypy : ly L r x ∈ py) :
    ∃ py1 : List Dart, py1 ∈ parts L (ml1S2 L N r x) ∧
      ly L r x ∈ py1 ∧ py1.head! = py.head! := by
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hys : ly L r x ∈ ml1S2 L N r x := (ml1S2Mem L N r x).2
  obtain ⟨py1, hpy1, hypy1⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hsnd hys
  have hparts2 := ml1SplitSndParts L hL hgn hm hnf
  have hpy1s2 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2 := by
    rw [hparts2]
    exact List.mem_append_left _ hpy1
  exact ⟨py1, hpy1, hypy1,
    ml1PartEndHead2 L hL hgn hm hnf hpy hpy1 hpy1s2 hypy1 hypy⟩

/-! ## §1 f2 块表的 HD/LAST 定位与 `pz1 ≠ py1` -/

/-- **HOL :2942–:2959**：`HD(parts L s2) = pz1`（含 `z` 的块即块表首元）。 -/
theorem ml1S2HdParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz1 : List Dart} (hpz1 : pz1 ∈ parts L (ml1S2 L N r x))
    (hzpz1 : ztrans L N r x 0 ∈ pz1) :
    (parts L (ml1S2 L N r x)).head! = pz1 := by
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hspflat : (parts L (ml1S2 L N r x)).flatten = ml1S2 L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S2 L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S2 L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hspne : parts L (ml1S2 L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hheadne : (parts L (ml1S2 L N r x)).head! ≠ [] :=
    hall _ (Kepler.Text.TameSpine.aqs_headMem hspne)
  have hdfl : (parts L (ml1S2 L N r x)).flatten.head!
      = (parts L (ml1S2 L N r x)).head!.head! :=
    Kepler.Text.TameSpine.hdFlatten (by rw [hspflat]; exact hsne) hheadne
  have hhh : (parts L (ml1S2 L N r x)).head!.head! = ztrans L N r x 0 := by
    rw [← hdfl, hspflat]
    exact ml1S2Head L N r x
  have hzhead : ztrans L N r x 0 ∈ (parts L (ml1S2 L N r x)).head! := by
    rw [← hhh]
    exact Kepler.Text.TameSpine.aqs_headMem hheadne
  have heq : pz1 = (parts L (ml1S2 L N r x)).head! :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S2 L N r x)) hflat
      pz1 hpz1 _ (Kepler.Text.TameSpine.aqs_headMem hspne) ⟨_, hzpz1, hzhead⟩
  exact heq.symm

/-- **HOL :2960–:2975**：`LAST(parts L s2) = py1`（含 `y` 的块即块表末元）。 -/
theorem ml1S2LastParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py1 : List Dart} (hpy1 : py1 ∈ parts L (ml1S2 L N r x))
    (hypy1 : ly L r x ∈ py1) :
    (parts L (ml1S2 L N r x)).getLast! = py1 := by
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hspflat : (parts L (ml1S2 L N r x)).flatten = ml1S2 L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S2 L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S2 L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hspne : parts L (ml1S2 L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hlastfl : (parts L (ml1S2 L N r x)).flatten.getLast!
      = (parts L (ml1S2 L N r x)).getLast!.getLast! :=
    lastFlatten2Bang hspne (by rw [hspflat]; exact hsne) hall
  have hy_eq_last : ly L r x = (parts L (ml1S2 L N r x)).flatten.getLast! := by
    rw [hspflat]
    exact (ml1S2Last L (r := r) (N := N) (x := x)).symm
  have hy_lastpart : ly L r x ∈ (parts L (ml1S2 L N r x)).getLast! := by
    rw [hy_eq_last, hlastfl]
    exact Kepler.Text.TameSpine.aqs_getLastMem
      (hall _ (Kepler.Text.TameSpine.aqs_getLastMem hspne))
  have heq : py1 = (parts L (ml1S2 L N r x)).getLast! :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S2 L N r x)) hflat
      py1 hpy1 _ (Kepler.Text.TameSpine.aqs_getLastMem hspne) ⟨_, hypy1, hy_lastpart⟩
  exact heq.symm

/-- **HOL :3010–:3020**：`pz1 ≠ py1`（state-1 块首 FST 判别：`z` 与 `y` 的 FST 不同）。 -/
theorem ml1S2PartsNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py1 pz1 : List Dart} (hpy1 : py1 ∈ parts L (ml1S2 L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S2 L N r x))
    (hypy1 : ly L r x ∈ py1) (hzpz1 : ztrans L N r x 0 ∈ pz1) :
    pz1 ≠ py1 := by
  obtain ⟨-, -, -, -, hyf, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf2mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.sndMemRtran1 L hL hgn hm hnf
  have hparts2 := ml1SplitSndParts L hL hgn hm hnf
  have hpz1s2 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2 := by
    rw [hparts2]
    exact List.mem_append_left _ hpz1
  have hpy1s2 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2 := by
    rw [hparts2]
    exact List.mem_append_left _ hpy1
  intro heq
  have hz1 : (ztrans L N r x 0).1 = pz1.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hpz1s2 hzpz1
  have hy1 : (ly L r x).1 = py1.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hpy1s2 hypy1
  rw [← heq] at hy1
  exact ml1FstNe L hL hgn hm hnf (hz1.trans hy1.symm).symm

/-! ## §2 f2 indexf 界（B6 的镜像） -/

/-- **W3b-2（HOL :3032–:3047）**：
`indexf (LAST pz) (HD py) s2 ≤ indexf (LAST pz) y s2`。 -/
theorem ml1IndexOfS2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz py : List Dart} (hpz : pz ∈ parts L r)
    (hzpz : ztrans L N r x 0 ∈ pz)
    (hpy : py ∈ parts L r)
    (hypy : ly L r x ∈ py) :
    Kepler.Text.Reduction5.indexf (pz.getLast!) (py.head!) (ml1S2 L N r x)
      ≤ Kepler.Text.Reduction5.indexf (pz.getLast!) (ly L r x) (ml1S2 L N r x) := by
  obtain ⟨pz1, hpz1, hzpz1, hpz1last⟩ :=
    ml1Pz1Last L hL hgn hm hnf hpz hzpz
  obtain ⟨py1, hpy1, hypy1, hpy1head⟩ :=
    ml1Py1Head L hL hgn hm hnf hpy hypy
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hspflat : (parts L (ml1S2 L N r x)).flatten = ml1S2 L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S2 L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S2 L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hpz1ne : pz1 ≠ [] := hall pz1 hpz1
  have hpy1ne : py1 ≠ [] := hall py1 hpy1
  have hheadmem : py1.head! ∈ py1 := Kepler.Text.TameSpine.aqs_headMem hpy1ne
  -- LAST pz ∈ sp.flatten
  have hy : pz.getLast! ∈ (parts L (ml1S2 L N r x)).flatten := by
    rw [← hpz1last]
    exact List.mem_flatten.mpr ⟨pz1, hpz1,
      Kepler.Text.TameSpine.aqs_getLastMem hpz1ne⟩
  -- LAST pz ∉ py1（PartsNe 一发）
  have hzv : pz.getLast! ∉ py1 := by
    intro hmem
    have hpm : pz.getLast! ∈ pz1 := by
      rw [← hpz1last]
      exact Kepler.Text.TameSpine.aqs_getLastMem hpz1ne
    exact ml1S2PartsNe L hL hgn hm hnf hpy1 hpz1 hypy1 hzpz1
      (Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S2 L N r x))
        hflat pz1 hpz1 py1 hpy1 ⟨_, hpm, hmem⟩)
  have h1 := Kepler.Text.TameSpine.aqs_indexfSplitHdFlatten
    (r := parts L (ml1S2 L N r x)) (v := py1) (y := pz.getLast!)
    (z := ly L r x) hflat hzv hypy1 hpy1 hall hy
  have h2 := Kepler.Text.TameSpine.aqs_indexfSplitHdFlatten
    (r := parts L (ml1S2 L N r x)) (v := py1) (y := pz.getLast!)
    (z := py1.head!) hflat hzv hheadmem hpy1 hall hy
  rw [hspflat] at h1 h2
  have h3 : Kepler.Text.TameSpine.indexf py1.head! py1.head! py1 = 0 :=
    Kepler.Text.TameSpine.indexfRefl hheadmem
  rw [h3] at h2
  rw [Kepler.Text.Reduction3.indexf_eq_spine, Kepler.Text.Reduction3.indexf_eq_spine]
  rw [← hpy1head]
  rw [h2, h1]
  omega


/-! ## §3 f1 侧收口件（HOL :2447–:2546，W4 装配前置；与 §1 对称） -/

/-- **HOL :2447–:2460**：`HD(parts L s1) = py1`（f1 半块表首元；`s1 = ml1S`）。 -/
theorem ml1S1HdParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py1 : List Dart} (hpy1 : py1 ∈ parts L (ml1S L N r x))
    (hy1py1 : nextEl r (ly L r x) ∈ py1) :
    (parts L (ml1S L N r x)).head! = py1 := by
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hspflat : (parts L (ml1S L N r x)).flatten = ml1S L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hspne : parts L (ml1S L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hheadne : (parts L (ml1S L N r x)).head! ≠ [] :=
    hall _ (Kepler.Text.TameSpine.aqs_headMem hspne)
  have hdfl : (parts L (ml1S L N r x)).flatten.head!
      = (parts L (ml1S L N r x)).head!.head! :=
    Kepler.Text.TameSpine.hdFlatten (by rw [hspflat]; exact hsne) hheadne
  have hhh : (parts L (ml1S L N r x)).head!.head! = nextEl r (ly L r x) := by
    rw [← hdfl, hspflat]
    exact ml1SHead L hL hgn hm hnf
  have hy1head : nextEl r (ly L r x) ∈ (parts L (ml1S L N r x)).head! := by
    rw [← hhh]
    exact Kepler.Text.TameSpine.aqs_headMem hheadne
  have heq : py1 = (parts L (ml1S L N r x)).head! :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S L N r x)) hflat
      py1 hpy1 _ (Kepler.Text.TameSpine.aqs_headMem hspne) ⟨_, hy1py1, hy1head⟩
  exact heq.symm

/-- **HOL :2489–:2500**：`LAST(parts L s1) = pz1`（f1 半块表末元）。 -/
theorem ml1S1LastParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz1 : List Dart} (hpz1 : pz1 ∈ parts L (ml1S L N r x))
    (hz1pz1 : prevEl r (ztrans L N r x 0) ∈ pz1) :
    (parts L (ml1S L N r x)).getLast! = pz1 := by
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hspflat : (parts L (ml1S L N r x)).flatten = ml1S L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hspne : parts L (ml1S L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hlastfl : (parts L (ml1S L N r x)).flatten.getLast!
      = (parts L (ml1S L N r x)).getLast!.getLast! :=
    lastFlatten2Bang hspne (by rw [hspflat]; exact hsne) hall
  have hz1_eq_last : prevEl r (ztrans L N r x 0)
      = (parts L (ml1S L N r x)).flatten.getLast! := by
    rw [hspflat]
    exact (ml1SLast L hL hgn hm hnf).symm
  have hz1_lastpart : prevEl r (ztrans L N r x 0)
      ∈ (parts L (ml1S L N r x)).getLast! := by
    rw [hz1_eq_last, hlastfl]
    exact Kepler.Text.TameSpine.aqs_getLastMem
      (hall _ (Kepler.Text.TameSpine.aqs_getLastMem hspne))
  have heq : pz1 = (parts L (ml1S L N r x)).getLast! :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S L N r x)) hflat
      pz1 hpz1 _ (Kepler.Text.TameSpine.aqs_getLastMem hspne) ⟨_, hz1pz1, hz1_lastpart⟩
  exact heq.symm

/-- **HOL :2546**：`py1 ≠ pz1`（f1 侧；state-1 块首 FST 判别 `y1` vs `z1`）。 -/
theorem ml1S1PartsNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py1 pz1 : List Dart} (hpy1 : py1 ∈ parts L (ml1S L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S L N r x))
    (hy1py1 : nextEl r (ly L r x) ∈ py1)
    (hz1pz1 : prevEl r (ztrans L N r x 0) ∈ pz1) :
    py1 ≠ pz1 := by
  obtain ⟨-, -, -, -, hyf, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf1mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.fstMemRtran1 L hL hgn hm hnf
  have hparts1 := ml1SplitFstParts L hL hgn hm hnf
  have hpy1f1 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1 := by
    rw [hparts1]
    exact List.mem_append_right _ hpy1
  have hpz1f1 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1 := by
    rw [hparts1]
    exact List.mem_append_right _ hpz1
  intro heq
  have hy1' : (nextEl r (ly L r x)).1 = py1.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hpy1f1 hy1py1
  have hz1' : (prevEl r (ztrans L N r x 0)).1 = pz1.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hpz1f1 hz1pz1
  rw [← heq] at hz1'
  refine ml1FstNe L hL hgn hm hnf ?_
  show (ly L r x).1 = (ztrans L N r x 0).1
  rw [← hy1fst, ← hz1fst]
  exact hy1'.trans hz1'.symm

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1SplitSndEq
#print axioms Kepler.Text.Reduction5.ml1PartEndHead2
#print axioms Kepler.Text.Reduction5.ml1Py1Head
#print axioms Kepler.Text.Reduction5.ml1S2HdParts
#print axioms Kepler.Text.Reduction5.ml1S2LastParts
#print axioms Kepler.Text.Reduction5.ml1S2PartsNe
#print axioms Kepler.Text.Reduction5.ml1IndexOfS2
#print axioms Kepler.Text.Reduction5.ml1S1HdParts
#print axioms Kepler.Text.Reduction5.ml1S1LastParts
#print axioms Kepler.Text.Reduction5.ml1S1PartsNe
