/-
  Kepler.Text.Reduction5Ml1W2bQ — W2b-B4：`pz1.head! = pz.head!`（HOL more_lemma1.hl:2315–:2440）。

  ┌─ 件目与 HOL 锚 ────────────────────────────────────────────────
  │ B4 `ml1Pz1`（:2315–:2440）：`∃ pz1 ∈ parts L s, z1 ∈ pz1 ∧ pz1.head! = pz.head!`。
  │ B6 `ml1IndexOfS`（:2580）：`indexf (LAST py) (HD pz) s ≤ indexf (LAST py) z1 s`。
  │ 内核 `ml1PartEndHead`：HEAD 侧（`p1.head! = p.head!`），B4 直接实例。
  │ 辅件：`ml1SplitFstEq`（split.1 = g_darts ++ s，P 内核同式的公开复用）、
  │   `nextElListInstEq`（parts 表上 `nextEl` 的 List 实例桥）、
  │   `lastFlatten2Bang`（`LAST_FLATTEN_2` 的 getLast! 形）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（DIFFERS，路线 B：HOL pn/pn1 链的语句级重推）────────────
  │ 记 h := pz1.head!（pz1 = s 中含 z1 的块）、dl := (prevEl (parts L s) pz1).getLast!。
  │ ① `h ∈ pz`：state-1 `parts_fst`（h.1 = z1.1 = z.1 = pz.head!.1）+ 块首 FST 单射。
  │ ② 反证 h ≠ pz.head!：
  │    · dl ≠ z1（若 dl = z1，则 `nextEl s dl = s.head! = y1`，与 h.1 = z.1 撞 FST）；
  │    · 若 dl.1 = z.1，则块首 FST 单射给 dl ∈ pz；再分 dl = pz.last
  │      （`nextEl` 链直接给 h = pz.head!，撞反证假设）与 dl ≠ pz.last
  │      （`partsNextUnlast` 给 nextEl r dl = f_list，state-1 normal_condition 给否定，矛盾）；
  │    · 故 dl.1 ≠ z.1；
  │    · pd := prevEl pz h；`nextPrevId` + `nextElInjOfNodup` 给 pd = dl；
  │      `parts_fst` 给 pd.1 = pz.head!.1 = z.1，撞 dl.1 ≠ z.1。 ⇒ h = pz.head!。
  │ HOL 同段 108 行的 `pn/pn1` 索引链按语句重推；未逐行转写。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5Ml1W2bP
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2QuotientAlt2
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.Reduction3J5IndexfPrevPartial
import Kepler.Text.ChainBridgeParts
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

/-- `nextEl` 在 `List Dart` 上的跨实例桥（`nextPrevId` 的 def-body 用
`instBEqOfDecidableEq`，parts 表上的裸 `nextEl` 用 `List.instBEq`）。 -/
theorem nextElListInstEq (s : List (List Dart)) (x : List Dart) :
    @nextEl (List Dart) (instBEqOfDecidableEq (α := List Dart)) s x
      = @nextEl (List Dart) List.instBEq s x := by
  unfold Kepler.Assembly.nextEl
  rw [Kepler.Text.TameLp.li_idxOf_of_lawful
    (e := instBEqOfDecidableEq (α := List Dart)) (f := List.instBEq)
    inferInstance inferInstance]

/-- `split.1 = g_darts ++ s` 的展开式（`g_darts` = 新原子的逆序铺平；
与 W2b-B3 内核内部同式，本文件公开复用）。 -/
theorem ml1SplitFstEq (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hrnd : r.Nodup) :
    (splitNormalList L r (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).1
      = ((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
          (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse.flatten
        ++ ml1S L N r x := by
  have hnextPrev : nextEl r (prevEl r (lz L N r x)) = ztrans L N r x 0 := by
    rw [Kepler.Text.Reduction5.nextElInstEq, Kepler.Text.Reduction5.nextPrevId hrnd]
    rfl
  show ((between (findFaceDarts L x) (ly L r x)
        (nextEl r (prevEl r (lz L N r x)))).map
          (fun d => Kepler.Text.TameSpine.ndSpine L d)).flatten.reverse
      ++ ([nextEl r (ly L r x)] ++
        (between r (nextEl r (ly L r x)) (prevEl r (lz L N r x)) ++
          [prevEl r (lz L N r x)]))
    = ((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse.flatten
      ++ ml1S L N r x
  rw [hnextPrev, ← Kepler.Text.TameSpine.flattenRev]
  rfl

/-- **W2b-B4 内核（HEAD 侧）**：`p1 ∈ parts L s`（且 `p1 ∈ parts L split.1`）含 `z1`，
`p ∈ parts L r` 也含 `z1`，则 `p1.head! = p.head!`。 -/
theorem ml1PartEndHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {p p1 : List Dart} (hp : p ∈ parts L r)
    (hp1 : p1 ∈ parts L (ml1S L N r x))
    (hp1f1 : p1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1)
    (hz1p1 : prevEl r (ztrans L N r x 0) ∈ p1)
    (hz1p : prevEl r (ztrans L N r x 0) ∈ p) :
    p1.head! = p.head! := by
  obtain ⟨-, hzr, hz1r, hy1r, hyf, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hzr
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hp1ne : p1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p1 hp1
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p hp
  have hpnd : p.Nodup := by
    have hflat : (parts L r).flatten.Nodup := by
      rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]
      exact hrnd
    exact (List.nodup_flatten.mp hflat).1 p hp
  -- state-1 normalList 与 split.1 成员/无重
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf1mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.fstMemRtran1 L hL hgn hm hnf
  have hf1nd : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1.Nodup :=
    (List.nodup_flatten.mp hn1.1).1 _ hf1mem
  have hsplit := ml1SplitFstEq L (N := N) (r := r) (x := x) hrnd
  -- h := p1.head! 的 FST = z 的 FST
  have hheadmem : p1.head! ∈ p1 := Kepler.Text.TameSpine.aqs_headMem hp1ne
  have hhead_s : p1.head! ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hp1 _ hheadmem
  have hhead_r : p1.head! ∈ r := ml1SMemImpR L hL hgn hm hnf hhead_s
  have hhfst : p1.head!.1 = (ztrans L N r x 0).1 := by
    have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hp1f1 hz1p1
    rw [hz1fst] at h
    exact h.symm
  -- p.head! 的 FST = z 的 FST
  have hpzfst : (ztrans L N r x 0).1 = p.head!.1 := by
    have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hz1p
    rwa [hz1fst] at h
  -- dl := (prevEl (parts L s) p1).getLast!
  have hspnd : (parts L (ml1S L N r x)).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hsnd hsne
  have hpn1mem : prevEl (parts L (ml1S L N r x)) p1 ∈ parts L (ml1S L N r x) :=
    Kepler.Text.Reduction5.memPrevEl hp1
  have hnextParts : nextEl (parts L (ml1S L N r x))
        (prevEl (parts L (ml1S L N r x)) p1) = p1 := by
    rw [← nextElListInstEq]
    exact Kepler.Text.Reduction5.nextPrevId hspnd p1
  have hpn1ne : prevEl (parts L (ml1S L N r x)) p1 ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ _ hpn1mem
  have hdlmem : (prevEl (parts L (ml1S L N r x)) p1).getLast!
      ∈ prevEl (parts L (ml1S L N r x)) p1 :=
    Kepler.Text.TameSpine.aqs_getLastMem hpn1ne
  have hdls : (prevEl (parts L (ml1S L N r x)) p1).getLast!
      ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hpn1mem _ hdlmem
  have hdlr : (prevEl (parts L (ml1S L N r x)) p1).getLast! ∈ r :=
    ml1SMemImpR L hL hgn hm hnf hdls
  -- nextEl s dl = p1.head!
  have hnexts : nextEl (ml1S L N r x)
        (prevEl (parts L (ml1S L N r x)) p1).getLast! = p1.head! := by
    rw [Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast L hsnd hsne hpn1mem
      hdlmem rfl, hnextParts]
  -- dl ≠ z1
  have hdlneZ1 : (prevEl (parts L (ml1S L N r x)) p1).getLast!
      ≠ prevEl r (ztrans L N r x 0) := by
    intro h
    have h2 : nextEl (ml1S L N r x) (prevEl r (ztrans L N r x 0)) = p1.head! := by
      rw [← h]
      exact hnexts
    rw [← ml1SLast L hL hgn hm hnf] at h2
    rw [Kepler.Text.TameSpine.nextElLast hsnd hsne] at h2
    rw [ml1SHead L hL hgn hm hnf] at h2
    apply ml1FstNe L hL hgn hm hnf
    rw [← hy1fst, h2]
    exact hhfst
  -- 反证 h = p.head!
  by_contra hne
  -- dl.1 ≠ z.1
  have hFstNe : (prevEl (parts L (ml1S L N r x)) p1).getLast!.1
      ≠ (ztrans L N r x 0).1 := by
    intro hfst
    obtain ⟨p', hp', hdlp'⟩ :=
      Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hdlr
    have hdlpzfst : (prevEl (parts L (ml1S L N r x)) p1).getLast!.1 = p'.head!.1 :=
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp' hdlp'
    have hp'p : p' = p := by
      have hfst' : p'.head!.1 = p.head!.1 := by
        rw [← hdlpzfst, hfst]
        exact hpzfst
      exact List.inj_on_of_nodup_map
        (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hp' hp hfst'
    have hdlp : (prevEl (parts L (ml1S L N r x)) p1).getLast! ∈ p := by
      rw [← hp'p]
      exact hdlp'
    by_cases hlast : (prevEl (parts L (ml1S L N r x)) p1).getLast! = p.getLast!
    · -- dl = LAST p：nextEl 链直接给 h = p.head!，撞反证假设
      have hqmem : nextEl (parts L r) p ∈ parts L r :=
        Kepler.Text.TameLp.nextEl_mem_of_mem hp
      have hnextq : nextEl r (prevEl (parts L (ml1S L N r x)) p1).getLast!
          = (nextEl (parts L r) p).head! := by
        rw [hlast]
        exact Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast L hrnd hrne hp
          (Kepler.Text.TameSpine.aqs_getLastMem hpne) rfl
      have h2 : (nextEl (parts L r) p).head! = p1.head! := by
        have h3 := hnexts
        rw [Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hz1r hy1r hyz.symm
          hdls (by unfold ml1S; rfl) hdlneZ1] at h3
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
      have hnextr : nextEl r (prevEl (parts L (ml1S L N r x)) p1).getLast!
          = fList L (eList (prevEl (parts L (ml1S L N r x)) p1).getLast!) := by
        rw [Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hrnd hrne hp hdlp hlast]
        exact Kepler.Text.TameSpine.partsNextUnlast L hrnd hrne p hpzSp
          (prevEl (parts L (ml1S L N r x)) p1).getLast! hdlp hlast
      have hp1f1' : prevEl (parts L (ml1S L N r x)) p1
          ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).1 := by
        rw [ml1SplitFstParts L hL hgn hm hnf]
        exact List.mem_append_right _ hpn1mem
      have hneg1 : ¬(nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).1
              (prevEl (parts L (ml1S L N r x)) p1).getLast!
          = fList L (eList (prevEl (parts L (ml1S L N r x)) p1).getLast!)) :=
        (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hn1
          hm.1.edgeNondegenerate hf1mem hp1f1' hdlmem).mpr rfl
      have hdlneLast : (prevEl (parts L (ml1S L N r x)) p1).getLast!
          ≠ (ml1S L N r x).getLast! := by
        intro h
        exact hdlneZ1 (by rw [h, ml1SLast L hL hgn hm hnf])
      have hnextsplit : nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).1 (prevEl (parts L (ml1S L N r x)) p1).getLast!
          = nextEl (ml1S L N r x)
              (prevEl (parts L (ml1S L N r x)) p1).getLast! := by
        rw [hsplit] at hf1nd ⊢
        exact Kepler.Text.TameSpine.nextElCat2 hf1nd hdls hdlneLast
      have hnexts2 : nextEl (ml1S L N r x)
            (prevEl (parts L (ml1S L N r x)) p1).getLast!
          = nextEl r (prevEl (parts L (ml1S L N r x)) p1).getLast! :=
        Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hz1r hy1r hyz.symm hdls
          (by unfold ml1S; rfl) hdlneZ1
      apply hneg1
      rw [hnextsplit, hnexts2]
      exact hnextr
  -- h ∈ p（块首 FST 单射定位；HOL :2315–:2321 同法）
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
  have hdl_next_r : nextEl r (prevEl (parts L (ml1S L N r x)) p1).getLast!
      = p1.head! := by
    rw [← Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hz1r hy1r hyz.symm hdls
      (by unfold ml1S; rfl) hdlneZ1]
    exact hnexts
  have hpd_eq : prevEl p p1.head! = (prevEl (parts L (ml1S L N r x)) p1).getLast! :=
    Kepler.Text.TameSpine.nextElInjOfNodup hrnd hpdmemr hdlr
      (by rw [hnextpd_r, hdl_next_r])
  have hpdfst : (prevEl p p1.head!).1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hpdmem
  exact hFstNe (by rw [← hpd_eq]; exact hpdfst.trans hpzfst.symm)

/-- **W2b-B4（HOL :2315–:2440，`HD pz1 = HD pz`）**：
`s` 中含 `z1` 的块 `pz1` 的首元 = `parts L r` 中含 `z1` 的块 `pz` 的首元。 -/
theorem ml1Pz1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz : List Dart} (hpz : pz ∈ parts L r)
    (hz1pz : prevEl r (ztrans L N r x 0) ∈ pz) :
    ∃ pz1 : List Dart, pz1 ∈ parts L (ml1S L N r x) ∧
      prevEl r (ztrans L N r x 0) ∈ pz1 ∧ pz1.head! = pz.head! := by
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hz1s : prevEl r (ztrans L N r x 0) ∈ ml1S L N r x :=
    (ml1SMem L hL hgn hm hnf).2
  obtain ⟨pz1, hpz1, hz1pz1⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hsnd hz1s
  have hparts1 := ml1SplitFstParts L hL hgn hm hnf
  have hpz1f1 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1 := by
    rw [hparts1]
    exact List.mem_append_right _ hpz1
  exact ⟨pz1, hpz1, hz1pz1,
    ml1PartEndHead L hL hgn hm hnf hpz hpz1 hpz1f1 hz1pz1 hz1pz⟩


/-! ## §2 B6：`ml1IndexOfS`（HOL :2580 的 indexf 界） -/

/-- `flatten` 的末元（`getLast!` 形，`LAST_FLATTEN_2` 的 bang 版）。 -/
theorem lastFlatten2Bang {α : Type*} [Inhabited α] {r : List (List α)} (hne : r ≠ [])
    (hflatne : r.flatten ≠ []) (hall : ∀ l ∈ r, l ≠ []) :
    r.flatten.getLast! = r.getLast!.getLast! := by
  have hlne : r.getLast hne ≠ [] := hall _ (List.getLast_mem hne)
  have h1 : r.flatten.getLast! = r.flatten.getLast hflatne := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hflatne,
      Option.getD_some]
  have h2 : r.getLast! = r.getLast hne := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hne,
      Option.getD_some]
  have h3 : r.getLast!.getLast! = (r.getLast hne).getLast hlne := by
    rw [h2, List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hlne,
      Option.getD_some]
  rw [h1, h3, Kepler.Text.MoreLemma2Naming.lastFlatten2 hne hlne hflatne]

/-- **W2b-B6（HOL :2580）**：`indexf (LAST py) (HD pz) s ≤ indexf (LAST py) z1 s`。
（s 的块表 = `parts L s`；`py1`/`pz1` 由 B3/B4 定位；两次
`indexf_split_HD_flatten` 共享前缀，`indexf_refl` 把 `HD pz1` 一侧压成 0。） -/
theorem ml1IndexOfS (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py pz : List Dart} (hpy : py ∈ parts L r)
    (hy1py : nextEl r (ly L r x) ∈ py)
    (hpz : pz ∈ parts L r)
    (hz1pz : prevEl r (ztrans L N r x 0) ∈ pz) :
    Kepler.Text.Reduction5.indexf (py.getLast!) (pz.head!) (ml1S L N r x)
      ≤ Kepler.Text.Reduction5.indexf (py.getLast!)
          (prevEl r (ztrans L N r x 0)) (ml1S L N r x) := by
  obtain ⟨-, hzr, hz1r, hy1r, -, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  obtain ⟨py1, hpy1, hy1py1, hpy1last⟩ :=
    ml1Py1 L hL hgn hm hnf hpy hy1py
  obtain ⟨pz1, hpz1, hz1pz1, hpz1head⟩ :=
    ml1Pz1 L hL hgn hm hnf hpz hz1pz
  have hspflat : (parts L (ml1S L N r x)).flatten = ml1S L N r x :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hsnd hsne
  have hflat : (parts L (ml1S L N r x)).flatten.Nodup := by
    rw [hspflat]
    exact hsnd
  have hall : ∀ l ∈ parts L (ml1S L N r x), l ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsAllNonnil L _
  have hspne : parts L (ml1S L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hpy1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hpz1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  -- LAST py ∈ s
  have hy : py.getLast! ∈ (parts L (ml1S L N r x)).flatten := by
    rw [← hpy1last]
    exact List.mem_flatten.mpr ⟨py1, hpy1, Kepler.Text.TameSpine.aqs_getLastMem hpy1ne⟩
  -- pz1 = sp.getLast! 且 pz1.getLast! = z1
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
    exact Kepler.Text.TameSpine.aqs_getLastMem (hall _ (Kepler.Text.TameSpine.aqs_getLastMem hspne))
  have hlastpart : pz1 = (parts L (ml1S L N r x)).getLast! :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S L N r x)) hflat
      pz1 hpz1 _ (Kepler.Text.TameSpine.aqs_getLastMem hspne) ⟨_, hz1pz1, hz1_lastpart⟩
  have hpz1last : pz1.getLast! = prevEl r (ztrans L N r x 0) := by
    rw [hlastpart, ← hlastfl, hspflat, ml1SLast L hL hgn hm hnf]
  -- py.getLast! ∉ pz1
  have hzv : py.getLast! ∉ pz1 := by
    intro hmem
    have hyy : py.getLast! ∈ py1 := by
      rw [← hpy1last]
      exact Kepler.Text.TameSpine.aqs_getLastMem hpy1ne
    have heq : py1 = pz1 :=
      Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L (ml1S L N r x)) hflat
        py1 hpy1 pz1 hpz1 ⟨_, hyy, hmem⟩
    have hpyz : py.getLast! = prevEl r (ztrans L N r x 0) := by
      rw [← hpy1last, heq, hpz1last]
    have hplastmem : py.getLast! ∈ py :=
      Kepler.Text.TameSpine.aqs_getLastMem (Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py hpy)
    have h1 : py.getLast!.1 = py.head!.1 :=
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hplastmem
    have h2 : (nextEl r (ly L r x)).1 = py.head!.1 :=
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hy1py
    have hfst : py.getLast!.1 = (ztrans L N r x 0).1 := by
      rw [hpyz, hz1fst]
    exact ml1FstNe L hL hgn hm hnf (by
      calc (ly L r x).1 = (nextEl r (ly L r x)).1 := hy1fst.symm
        _ = py.head!.1 := h2
        _ = py.getLast!.1 := h1.symm
        _ = (ztrans L N r x 0).1 := hfst)
  have hheadmem : pz1.head! ∈ pz1 := Kepler.Text.TameSpine.aqs_headMem hpz1ne
  -- 两次 split_HD（列表 := parts L s，v := pz1）
  have h1 := Kepler.Text.TameSpine.aqs_indexfSplitHdFlatten
    (r := parts L (ml1S L N r x)) (v := pz1) (y := py.getLast!)
    (z := prevEl r (ztrans L N r x 0)) hflat hzv hz1pz1 hpz1 hall hy
  have h2 := Kepler.Text.TameSpine.aqs_indexfSplitHdFlatten
    (r := parts L (ml1S L N r x)) (v := pz1) (y := py.getLast!)
    (z := pz1.head!) hflat hzv hheadmem hpz1 hall hy
  rw [hspflat] at h1 h2
  have h3 : Kepler.Text.TameSpine.indexf pz1.head! pz1.head! pz1 = 0 :=
    Kepler.Text.TameSpine.indexfRefl hheadmem
  rw [h3] at h2
  -- 链 indexf → spine indexf
  rw [Kepler.Text.Reduction3.indexf_eq_spine, Kepler.Text.Reduction3.indexf_eq_spine]
  rw [← hpz1head]
  rw [h2, h1]
  omega

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.nextElListInstEq
#print axioms Kepler.Text.Reduction5.ml1SplitFstEq
#print axioms Kepler.Text.Reduction5.ml1PartEndHead
#print axioms Kepler.Text.Reduction5.ml1Pz1
#print axioms Kepler.Text.Reduction5.lastFlatten2Bang
#print axioms Kepler.Text.Reduction5.ml1IndexOfS
