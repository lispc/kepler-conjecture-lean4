/-
  Kepler.Text.Reduction5Ml1W4 — 主机 8b W4 装配：两条 core 方程 + 主件
  （HOL more_lemma1.hl:3011–:3091；主件陈述 = tame_defs2.hl:770–784）。

  ┌─ 件目与 HOL 锚 ────────────────────────────────────────────────
  │ 实例桥包（5 件）：`beqEqOfLawful`/`containsEqOfLawful`/`splitAtRecEqOfLawful`/
  │   `splitAtEqOfLawful`/`betweenEqOfLawful`（任意两个 LawfulBEq 实例逐点相等） |
  │   无 HOL 锚（BEq 世界；nb16/`betweenInstEq`/`nextElListInstEq` 先例的泛化） |
  │ `coreMapHead`（`core L r = (parts L r).map head!.1`） | core 的 head! 形（W2 内联同式） |
  │ `ml1GpartsMapHead`（块表 head! = 窗口 FST 表反序） | :3072 `FST_HD_MAP_betwn` / AQ12:384 |
  │ `ml1PartsBetwnSym`（`parts (betwn r LAST pz HD py) = betwn (parts r) pz py`） | :2674 `parts_betwn` 对称实例 |
  │ `ml1BetwnPartsS1`（f1 parts 的 betwn 折回 r） | :2557–:2615 |
  │ `ml1BetwnPartsS2`（f2 parts 的 betwn 折回 r） | :3005–:3071 |
  │ `ml1CoreS1` / `ml1CoreS2`（两半的 core 方程） | :2557–:2621 / :3011–:3081 |
  │ **`coreSplitNormalListThm`（主件）** | :2028–:3091 / tame_defs2:770 |
  └────────────────────────────────────────────────────────────────

  路线（DIFFERS）：沿用 W1–W3 已落 15 件 + 本文件 14 件装配；`mapBetwn`
  （Reduction5BetwnBase:369）替代 HOL 的 `uniq_imp_inj`+`map_betwn` 两步；
  块表 head 用 `aq8w4a_blockHeadFst`（跨叶复用）；f1 parts 的 betwn 折回用
  「state-1 parts_betwn → betwn_cat → dart betwn_cat → cat_betwn_same →
  state-0 parts_betwn」五段链，f2 同链换 betwnCat0（HOL 同构，语句级重推）；
  parts 表上的 `between` 实例摩擦由 `betweenEqOfLawful` 桥（List 级）与
  `betweenInstEq`（Dart 级）缝合。
-/

import Kepler.Text.Reduction5Ml1W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf12B
import Kepler.Text.TameSpine.JcajyduAqLeaf8W4a
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §0 装配辅件 -/

/-- `core` 的 `head!` 形（parts 原子非空 ⇒ `headD (0,0) = head!`）。 -/
theorem coreMapHead (L : fgraph ℕ) (r : List Dart) :
    core L r = (parts L r).map (fun p => p.head!.1) := by
  unfold core
  exact List.map_congr_left (fun p hp => by
    cases p with
    | nil => exact absurd rfl (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ hp)
    | cons a t => rfl)

/-- 两个 `LawfulBEq` 实例的 `beq` 逐点相等。 -/
theorem beqEqOfLawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (a b : α) :
    @BEq.beq α e a b = @BEq.beq α f a b := by
  by_cases h : a = b
  · subst h
    rw [@beq_self_eq_true α e he.toReflBEq a, @beq_self_eq_true α f hf.toReflBEq a]
  · have h1 : @BEq.beq α e a b = false := by
      cases hb : @BEq.beq α e a b with
      | false => rfl
      | true => exact absurd ((@beq_iff_eq α e he).mp hb) h
    have h2 : @BEq.beq α f a b = false := by
      cases hb : @BEq.beq α f a b with
      | false => rfl
      | true => exact absurd ((@beq_iff_eq α f hf).mp hb) h
    rw [h1, h2]

/-- `List.contains` 跨 `LawfulBEq` 实例逐点相等。 -/
theorem containsEqOfLawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (c : α) (as : List α) :
    @List.contains α e as c = @List.contains α f as c := by
  have h1 : @List.contains α e as c = decide (c ∈ as) := by
    rw [Bool.eq_iff_iff, @List.contains_iff_mem α e he c as]
    exact decide_eq_true_iff.symm
  have h2 : @List.contains α f as c = decide (c ∈ as) := by
    rw [Bool.eq_iff_iff, @List.contains_iff_mem α f hf c as]
    exact decide_eq_true_iff.symm
  rw [h1, h2]

/-- `splitAtRec` 跨 `LawfulBEq` 实例逐点相等（对表归纳，`bs` 泛化）。 -/
theorem splitAtRecEqOfLawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (c : α) (bs as : List α) :
    @Kepler.Graphs.splitAtRec α e c bs as = @Kepler.Graphs.splitAtRec α f c bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    show (if @BEq.beq α e a c then (bs, as)
        else @Kepler.Graphs.splitAtRec α e c (bs ++ [a]) as)
      = (if @BEq.beq α f a c then (bs, as)
        else @Kepler.Graphs.splitAtRec α f c (bs ++ [a]) as)
    rw [beqEqOfLawful he hf a c]
    by_cases h : @BEq.beq α f a c = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact ih (bs ++ [a])

/-- `splitAt` 跨 `LawfulBEq` 实例逐点相等。 -/
theorem splitAtEqOfLawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (c : α) (as : List α) :
    @Kepler.Graphs.splitAt α e c as = @Kepler.Graphs.splitAt α f c as :=
  splitAtRecEqOfLawful he hf c [] as

/-- `between` 跨 `LawfulBEq` 实例逐点相等。 -/
theorem betweenEqOfLawful {α : Type*} {e f : BEq α}
    (he : @LawfulBEq α e) (hf : @LawfulBEq α f) (s : List α) (a b : α) :
    @Kepler.Graphs.between α e s a b = @Kepler.Graphs.between α f s a b := by
  unfold Kepler.Graphs.between
  rw [splitAtEqOfLawful he hf a s]
  cases h : @Kepler.Graphs.splitAt α f a s with
  | mk pre post =>
    dsimp only
    rw [containsEqOfLawful he hf b post, splitAtEqOfLawful he hf b post,
      splitAtEqOfLawful he hf b pre]

/-- 链 marked → spine 对（marked + ¬final）。 -/
theorem ml1SpinePair (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    Kepler.Text.TameSpine.MarkedListSpineFull hL N r x ∧
      ¬ Kepler.Text.TameSpine.finalListSpine L r := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  exact ⟨(Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)⟩

/-- 块表（`((ndSpine d).reverse)`）的 head! FST 表 = 窗口 FST 表反序
（HOL :3072 `FST_HD_MAP_betwn` 的块形；`aq8w4a_blockHeadFst` 跨叶复用）。 -/
theorem ml1GpartsMapHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    ((((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse).map
      (fun p => p.head!.1))
      = ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
          (fun d => d.1)).reverse := by
  obtain ⟨hmS, hfS⟩ := ml1SpinePair L hL hgn hm hnf
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hly : ly L r x = Kepler.Text.TameSpine.lYSpine L r x :=
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf
  have hlz : lz L N r x = Kepler.Text.TameSpine.lZSpine L N r x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf
  rw [List.map_reverse, List.map_map]
  congr 1
  exact List.map_congr_left (fun d hd => by
    apply Kepler.Text.TameSpine.aq8w4a_blockHeadFst L hL hgn hmS hfS
    rwa [hly, hlz] at hd)

/-- `parts_betwn` 的对称实例（y/z 角色互换；HOL :2674 同法）：
`parts L (betwn r LAST pz HD py) = betwn (parts L r) pz py`。 -/
theorem ml1PartsBetwnSym (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz py : List Dart} (hpz : pz ∈ parts L r) (hpy : py ∈ parts L r)
    (hzpz : ztrans L N r x 0 ∈ pz)
    (hypy : ly L r x ∈ py) :
    parts L (between r pz.getLast! py.head!) = between (parts L r) pz py := by
  have hcore : ((parts L r).map (fun q => q.head!.1)).Nodup :=
    ml1PartsHeadFstNodup L hL hm hm.2.2.1
  have hyz' : (ztrans L N r x 0).1 ≠ (ly L r x).1 :=
    fun h => ml1FstNe L hL hgn hm hnf h.symm
  exact Kepler.Text.Reduction5.partsBetwnChain L hL hm.2.1 hm.1.edgeNondegenerate
    hm.2.2.1 (sp := parts L r) rfl hcore hpz hpy hzpz hypy hyz'

/-! ## §1 两半 parts 的 betwn 折回 r -/

/-- **f1 半**（HOL :2557–:2615）：`betwn (parts L s1) py1 pz1 = betwn (parts L r) py pz`。 -/
theorem ml1BetwnPartsS1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py pz py1 pz1 : List Dart}
    (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hy1py : nextEl r (ly L r x) ∈ py)
    (hz1pz : prevEl r (ztrans L N r x 0) ∈ pz)
    (hpy1 : py1 ∈ parts L (ml1S L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S L N r x))
    (hy1py1 : nextEl r (ly L r x) ∈ py1)
    (hz1pz1 : prevEl r (ztrans L N r x 0) ∈ pz1)
    (hpy1last : py1.getLast! = py.getLast!)
    (hpz1head : pz1.head! = pz.head!)
    (hpartsA : parts L (between r py.getLast! pz.head!) = between (parts L r) py pz) :
    between (parts L (ml1S L N r x)) py1 pz1 = between (parts L r) py pz := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, -, hy1fst, hz1fst, -⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hpy1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hpz1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  have hpyne : py ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py hpy
  have hpzne : pz ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz hpz
  -- py1.getLast! / pz1.head! 的 FST 与端点
  have hpl : py1.getLast!.1 = (nextEl r (ly L r x)).1 := by
    rw [hpy1last]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy
        (Kepler.Text.TameSpine.aqs_getLastMem hpyne)).trans
      ((Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hy1py).symm)
  have hph : pz1.head!.1 = (ztrans L N r x 0).1 := by
    rw [hpz1head]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hz1pz).symm.trans
      hz1fst
  have hzy1 : py1.getLast! ≠ pz1.head! := by
    intro h
    have hfst : (nextEl r (ly L r x)).1 = (ztrans L N r x 0).1 :=
      hpl.symm.trans ((congrArg Prod.fst h).trans hph)
    refine ml1FstNe L hL hgn hm hnf ?_
    show (ly L r x).1 = (ztrans L N r x 0).1
    rw [← hy1fst]
    exact hfst
  -- state-1：split.1 的 normalList 与成员
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
  have hf1ne : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 ≠ [] := by
    rw [hsplit]
    exact List.ne_nil_of_mem (List.mem_append_right _ hy1s)
  have hparts1 := ml1SplitFstParts L hL hgn hm hnf
  have hS1eq : ml1S L N r x = [nextEl r (ly L r x)] ++
      (between r (nextEl r (ly L r x)) (prevEl r (lz L N r x)) ++
        [prevEl r (lz L N r x)]) := rfl
  have hparts1' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 = (((between (findFaceDarts L x) (ly L r x)
        (lz L N r x)).map (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
      ++ parts L (ml1S L N r x) := by
    rw [hparts1, ← hS1eq]
  have hpy1f1 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 := by
    rw [hparts1']
    exact List.mem_append_right _ hpy1
  have hpz1f1 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 := by
    rw [hparts1']
    exact List.mem_append_right _ hpz1
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm 1
  have hcore1 : ((parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1).map (fun q => q.head!.1)).Nodup := by
    have hmem : core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).1 ∈ quotientList L (ntrans L N r x 1) := by
      unfold quotientList coreList
      exact List.mem_map_of_mem (List.mem_map_of_mem hf1mem)
    have hD := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm1 _ hmem
    rwa [coreMapHead] at hD
  have hy1z1fst : (nextEl r (ly L r x)).1 ≠ (prevEl r (ztrans L N r x 0)).1 := by
    rw [hz1fst]
    intro h
    exact ml1FstNe L hL hgn hm hnf (by rw [← hy1fst]; exact h)
  -- (a) state-1 parts_betwn
  have hsp := Kepler.Text.Reduction5.partsBetwnChain L hL hn1
    hm.1.edgeNondegenerate hf1mem (sp := parts L (splitNormalList L r
      (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).1) rfl hcore1
    hpy1f1 hpz1f1 hy1py1 hz1pz1 hy1z1fst
  -- (b) parts 上的 betwn_cat（g_parts + parts s1 → parts s1）
  have hparts1nd : (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hf1nd hf1ne
  have hb1raw := Kepler.Text.TameSpine.betwnCat
      (g := (((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse))
      (s := parts L (ml1S L N r x)) (y := py1) (z := pz1)
      (by rw [← hparts1']; exact hparts1nd) hpy1 hpz1
      (by rw [ml1S1LastParts L hL hgn hm hnf hpz1 hz1pz1])
      (ml1S1PartsNe L hL hgn hm hnf hpy1 hpz1 hy1py1 hz1pz1)
  have hb1 : between ((((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
        ++ parts L (ml1S L N r x)) py1 pz1
      = between (parts L (ml1S L N r x)) py1 pz1 := by
    rw [betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
          (he := inferInstance) (hf := inferInstance)
          ((((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
            ++ parts L (ml1S L N r x)) py1 pz1,
        betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
          (he := inferInstance) (hf := inferInstance)
          (parts L (ml1S L N r x)) py1 pz1]
    exact hb1raw
  -- (c) dart 上的 betwn_cat（g_darts + s1 → s1）
  have hpy1lastmem : py1.getLast! ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hpy1 _ (Kepler.Text.TameSpine.aqs_getLastMem hpy1ne)
  have hpz1headmem : pz1.head! ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hpz1 _ (Kepler.Text.TameSpine.aqs_headMem hpz1ne)
  have hindex := ml1IndexOfS L hL hgn hm hnf hpy hy1py hpz hz1pz
  have hb2raw := Kepler.Text.TameSpine.betwnCat
      (g := (((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse).flatten)
      (s := ml1S L N r x) (y := py1.getLast!) (z := pz1.head!)
      (by rw [← hsplit]; exact hf1nd) hpy1lastmem hpz1headmem
      (by
        rw [hpy1last, hpz1head, ml1SLast L hL hgn hm hnf]
        exact hindex)
      hzy1
  have hb2 : between ((((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
        (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse).flatten
        ++ ml1S L N r x) py1.getLast! pz1.head!
      = between (ml1S L N r x) py1.getLast! pz1.head! := by
    rw [Kepler.Text.Reduction5.betweenInstEq
          ((((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
            (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse).flatten
            ++ ml1S L N r x) py1.getLast! pz1.head!,
        Kepler.Text.Reduction5.betweenInstEq
          (ml1S L N r x) py1.getLast! pz1.head!]
    exact hb2raw
  -- (d) cat_betwn_same（s1 → r）
  have hc := Kepler.Text.TameSpine.catBetwnSame (r := r) (s := ml1S L N r x)
    (y := nextEl r (ly L r x)) (z := prevEl r (ztrans L N r x 0))
    (lx := py1.getLast!) (lz := pz1.head!)
    hrnd hy1r hz1r hyz (by unfold ml1S; rfl) hpy1lastmem hpz1headmem hzy1
    (by
      rw [hpy1last, hpz1head]
      exact hindex)
  -- 组装
  calc between (parts L (ml1S L N r x)) py1 pz1
      = between ((((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
          (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
          ++ parts L (ml1S L N r x)) py1 pz1 := hb1.symm
    _ = between (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).1) py1 pz1 := by rw [hparts1']
    _ = parts L (between (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).1 py1.getLast! pz1.head!) := hsp.symm
    _ = parts L (between (ml1S L N r x) py1.getLast! pz1.head!) := by
        rw [hsplit, hb2]
    _ = parts L (between r py1.getLast! pz1.head!) := by rw [hc]
    _ = parts L (between r py.getLast! pz.head!) := by rw [hpy1last, hpz1head]
    _ = between (parts L r) py pz := hpartsA


/-- **f2 半**（HOL :3005–:3071）：`betwn (parts L s2) pz1 py1 = betwn (parts L r) pz py`
（f2 半的 `pz1` 含 `z`、`py1` 含 `y`，与 f1 的 z1/y1 不同）。 -/
theorem ml1BetwnPartsS2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py pz py1 pz1 : List Dart}
    (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hypy : ly L r x ∈ py)
    (hzpz : ztrans L N r x 0 ∈ pz)
    (hpy1 : py1 ∈ parts L (ml1S2 L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S2 L N r x))
    (hypy1 : ly L r x ∈ py1)
    (hzpz1 : ztrans L N r x 0 ∈ pz1)
    (hpy1head : py1.head! = py.head!)
    (hpz1last : pz1.getLast! = pz.getLast!)
    (hpartsA2 : parts L (between r pz.getLast! py.head!) = between (parts L r) pz py) :
    between (parts L (ml1S2 L N r x)) pz1 py1 = between (parts L r) pz py := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, -, -, hz1fst, hzy⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hpy1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hpz1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  have hpyne : py ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py hpy
  have hpzne : pz ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz hpz
  -- pz1.getLast! / py1.head! 的 FST
  have hpl : pz1.getLast!.1 = (prevEl r (ztrans L N r x 0)).1 := by
    rw [hpz1last]
    exact ((Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz
        (Kepler.Text.TameSpine.aqs_getLastMem hpzne)).trans
      ((Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hzpz).symm)).trans
      hz1fst.symm
  have hph : py1.head!.1 = (ly L r x).1 := by
    rw [hpy1head]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hypy).symm
  have hzy1 : pz1.getLast! ≠ py1.head! := by
    intro h
    have hfst : (prevEl r (ztrans L N r x 0)).1 = (ly L r x).1 :=
      hpl.symm.trans ((congrArg Prod.fst h).trans hph)
    exact ml1FstNe L hL hgn hm hnf (hfst.symm.trans hz1fst)
  -- state-1：split.2 的 normalList 与成员
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
  have hf2ne : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 ≠ [] := by
    rw [hsplit2]
    exact List.ne_nil_of_mem (List.mem_append_left _ hzs)
  have hparts2 := ml1SplitSndParts L hL hgn hm hnf
  have hS2eq : ml1S2 L N r x = [ztrans L N r x 0] ++
      (between r (ztrans L N r x 0) (ly L r x) ++ [ly L r x]) := rfl
  have hparts2' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2
      = parts L (ml1S2 L N r x) ++ (between (findFaceDarts L x) (ly L r x)
          (lz L N r x)).map (fun d => [d]) := by
    rw [hparts2, hS2eq]
    rfl
  have hpy1f2 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 := by
    rw [hparts2']
    exact List.mem_append_left _ hpy1
  have hpz1f2 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 := by
    rw [hparts2']
    exact List.mem_append_left _ hpz1
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm 1
  have hcore2 : ((parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2).map (fun q => q.head!.1)).Nodup := by
    have hmem : core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).2 ∈ quotientList L (ntrans L N r x 1) := by
      unfold quotientList coreList
      exact List.mem_map_of_mem (List.mem_map_of_mem hf2mem)
    have hD := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm1 _ hmem
    rwa [coreMapHead] at hD
  have hz1yfst : (ztrans L N r x 0).1 ≠ (ly L r x).1 := by
    exact fun h => ml1FstNe L hL hgn hm hnf h.symm
  -- (a) state-1 parts_betwn（pz1 在前、py1 在后）
  have hsp := Kepler.Text.Reduction5.partsBetwnChain L hL hn1
    hm.1.edgeNondegenerate hf2mem (sp := parts L (splitNormalList L r
      (findFaceDarts L x) (ly L r x) (prevEl r (lz L N r x))).2) rfl hcore2
    hpz1f2 hpy1f2 hzpz1 hypy1 hz1yfst
  -- (b) parts 上的 betwn_cat0（parts s2 + 单点段 → parts s2）
  have hparts2nd : (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hf2nd hf2ne
  have hb1raw := betwnCat0
    (s := parts L (ml1S2 L N r x))
    (g := (between (findFaceDarts L x) (ly L r x) (lz L N r x)).map (fun d => [d]))
    (y := pz1) (z := py1)
    (by rw [← hparts2']; exact hparts2nd) hpz1 hpy1
    (by rw [ml1S2LastParts L hL hgn hm hnf hpy1 hypy1])
    (ml1S2PartsNe L hL hgn hm hnf hpy1 hpz1 hypy1 hzpz1)
  have hb1 : between ((parts L (ml1S2 L N r x))
        ++ (between (findFaceDarts L x) (ly L r x) (lz L N r x)).map (fun d => [d]))
        pz1 py1 = between (parts L (ml1S2 L N r x)) pz1 py1 := by
    rw [betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
          (he := inferInstance) (hf := inferInstance)
          ((parts L (ml1S2 L N r x))
            ++ (between (findFaceDarts L x) (ly L r x) (lz L N r x)).map (fun d => [d]))
          pz1 py1,
        betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
          (he := inferInstance) (hf := inferInstance)
          (parts L (ml1S2 L N r x)) pz1 py1]
    exact hb1raw
  -- (c) dart 上的 betwn_cat0（s2 + 窗口 → s2）
  have hpz1lastmem : pz1.getLast! ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hpz1 _ (Kepler.Text.TameSpine.aqs_getLastMem hpz1ne)
  have hpy1headmem : py1.head! ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hpy1 _ (Kepler.Text.TameSpine.aqs_headMem hpy1ne)
  have hindex := ml1IndexOfS2 L hL hgn hm hnf hpz hzpz hpy hypy
  have hb2raw := betwnCat0
    (s := ml1S2 L N r x)
    (g := between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0))
    (y := pz1.getLast!) (z := py1.head!)
    (by rw [← hsplit2]; exact hf2nd) hpz1lastmem hpy1headmem
    (by
      rw [hpz1last, hpy1head, ml1S2Last L (r := r) (N := N) (x := x)]
      exact hindex)
    hzy1
  have hb2 : between ((ml1S2 L N r x)
        ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0))
        pz1.getLast! py1.head! = between (ml1S2 L N r x) pz1.getLast! py1.head! := by
    rw [Kepler.Text.Reduction5.betweenInstEq
          ((ml1S2 L N r x) ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0))
          pz1.getLast! py1.head!,
        Kepler.Text.Reduction5.betweenInstEq (ml1S2 L N r x) pz1.getLast! py1.head!]
    exact hb2raw
  -- (d) cat_betwn_same（s2 → r）
  have hc := Kepler.Text.TameSpine.catBetwnSame (r := r) (s := ml1S2 L N r x)
    (y := ztrans L N r x 0) (z := ly L r x)
    (lx := pz1.getLast!) (lz := py1.head!)
    hrnd hzr hyr hzy (by unfold ml1S2; rfl) hpz1lastmem hpy1headmem hzy1
    (by
      rw [hpz1last, hpy1head]
      exact hindex)
  -- 组装
  calc between (parts L (ml1S2 L N r x)) pz1 py1
      = between ((parts L (ml1S2 L N r x))
          ++ (between (findFaceDarts L x) (ly L r x) (lz L N r x)).map (fun d => [d]))
          pz1 py1 := hb1.symm
    _ = between (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).2) pz1 py1 := by rw [hparts2']
    _ = parts L (between (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).2 pz1.getLast! py1.head!) := hsp.symm
    _ = parts L (between (ml1S2 L N r x) pz1.getLast! py1.head!) := by
        rw [hsplit2, hb2]
    _ = parts L (between r pz1.getLast! py1.head!) := by rw [hc]
    _ = parts L (between r pz.getLast! py.head!) := by rw [hpz1last, hpy1head]
    _ = between (parts L r) pz py := hpartsA2

/-- **f1 core 方程**（HOL :2557–:2621）：`core L s1 = newVs' ++ ([y.1] ++ betwn(core r) y.1 z1.1 ++ [z1.1])`
的 s1 部分（`newVs'` 由块表在装配处补）。 -/
theorem ml1CoreS1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py pz py1 pz1 : List Dart}
    (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hy1py : nextEl r (ly L r x) ∈ py)
    (hz1pz : prevEl r (ztrans L N r x 0) ∈ pz)
    (hpy1 : py1 ∈ parts L (ml1S L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S L N r x))
    (hy1py1 : nextEl r (ly L r x) ∈ py1)
    (hz1pz1 : prevEl r (ztrans L N r x 0) ∈ pz1)
    (hpy1last : py1.getLast! = py.getLast!)
    (hpz1head : pz1.head! = pz.head!)
    (hpartsA : parts L (between r py.getLast! pz.head!) = between (parts L r) py pz) :
    core L (ml1S L N r x)
      = [(ly L r x).1] ++ (between (core L r) (ly L r x).1
          (prevEl r (lz L N r x)).1 ++ [(prevEl r (lz L N r x)).1]) := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, -, hy1fst, hz1fst, -⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hzr
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hpy1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hpz1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  -- state-1 端点 FST
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf1mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.fstMemRtran1 L hL hgn hm hnf
  have hparts1 := ml1SplitFstParts L hL hgn hm hnf
  have hS1eq : ml1S L N r x = [nextEl r (ly L r x)] ++
      (between r (nextEl r (ly L r x)) (prevEl r (lz L N r x)) ++
        [prevEl r (lz L N r x)]) := rfl
  have hparts1' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 = (((between (findFaceDarts L x) (ly L r x)
        (lz L N r x)).map (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
      ++ parts L (ml1S L N r x) := by
    rw [hparts1, ← hS1eq]
  have hpy1f1 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 := by
    rw [hparts1']
    exact List.mem_append_right _ hpy1
  have hpz1f1 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 := by
    rw [hparts1']
    exact List.mem_append_right _ hpz1
  have hpy1hfst : py1.head!.1 = (ly L r x).1 := by
    have h := Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hpy1f1 hy1py1
    rw [← hy1fst]
    exact h.symm
  have hpz1hfst : pz1.head!.1 = (prevEl r (ztrans L N r x 0)).1 :=
    (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hpz1f1 hz1pz1).symm
  -- parts L s1 的 HD/LAST 分解
  have hspne : parts L (ml1S L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hspnd : (parts L (ml1S L N r x)).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hsnd hsne
  have hheadne2 : (parts L (ml1S L N r x)).head! ≠ (parts L (ml1S L N r x)).getLast! := by
    intro h
    have h1 := ml1S1HdParts L hL hgn hm hnf hpy1 hy1py1
    have h2 := ml1S1LastParts L hL hgn hm hnf hpz1 hz1pz1
    rw [h1, h2] at h
    exact ml1S1PartsNe L hL hgn hm hnf hpy1 hpz1 hy1py1 hz1pz1 h
  have hpartsOrder : parts L (ml1S L N r x)
      = [py1] ++ (between (parts L (ml1S L N r x)) py1 pz1 ++ [pz1]) := by
    have h := Kepler.Text.TameSpine.eqHdLastBetwn (r := parts L (ml1S L N r x))
      hspne hspnd hheadne2
    rw [ml1S1HdParts L hL hgn hm hnf hpy1 hy1py1,
      ml1S1LastParts L hL hgn hm hnf hpz1 hz1pz1] at h
    rw [betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
      (he := inferInstance) (hf := inferInstance) (parts L (ml1S L N r x)) py1 pz1]
    exact h
  -- betwn of parts 折回 r
  have hbp := ml1BetwnPartsS1 L hL hgn hm hnf hpy hpz hy1py hz1pz hpy1 hpz1
    hy1py1 hz1pz1 hpy1last hpz1head hpartsA
  -- mapBetwn：betwn (parts L r) py pz 的 head FST 表
  have hpyz : py ≠ pz := by
    intro h
    have h1 : py.head!.1 = pz.head!.1 := by rw [h]
    rw [← Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hy1py,
      ← Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hz1pz,
      hy1fst, hz1fst] at h1
    exact ml1FstNe L hL hgn hm hnf h1
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
  have hy1z1fst : (nextEl r (ly L r x)).1 ≠ (prevEl r (ztrans L N r x 0)).1 := by
    rw [hz1fst]
    intro h
    exact ml1FstNe L hL hgn hm hnf (by rw [← hy1fst]; exact h)
  have hmap := Kepler.Text.TameSpine.aqs_fstHdMapBetwn L hL hnS hm.2.2.1
    (sp := parts L r) (Kepler.Text.ChainBridge.parts_eq_partsSpine L r).symm
    (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hpy hpz hy1py hz1pz hy1z1fst
  have hmap' : (between (parts L r) py pz).map (fun p => p.head!.1)
      = between (core L r) (ly L r x).1 (prevEl r (ztrans L N r x 0)).1 := by
    rw [hmap, hy1fst, ← coreMapHead]
  have hbp' : (between (parts L (ml1S L N r x)) py1 pz1).map (fun p => p.head!.1)
      = between (core L r) (ly L r x).1 (prevEl r (ztrans L N r x 0)).1 := by
    rw [hbp, hmap']
  -- 组装
  calc core L (ml1S L N r x)
      = (parts L (ml1S L N r x)).map (fun p => p.head!.1) := coreMapHead L _
    _ = ([py1] ++ (between (parts L (ml1S L N r x)) py1 pz1 ++ [pz1])).map
          (fun p => p.head!.1) := by
        conv_lhs => rw [hpartsOrder]
    _ = [py1.head!.1] ++ (((between (parts L (ml1S L N r x)) py1 pz1).map
          (fun p => p.head!.1)) ++ [pz1.head!.1]) := by
        rw [List.map_append, List.map_cons, List.map_nil, List.map_append]
        rfl
    _ = [(ly L r x).1] ++ (between (core L r) (ly L r x).1
          (prevEl r (ztrans L N r x 0)).1 ++
          [(prevEl r (ztrans L N r x 0)).1]) := by
        rw [hpy1hfst, hpz1hfst, hbp']
    _ = [(ly L r x).1] ++ (between (core L r) (ly L r x).1
          (prevEl r (lz L N r x)).1 ++ [(prevEl r (lz L N r x)).1]) := rfl


/-- **f2 core 方程**（HOL :3011–:3081）：`core L s2 = [z'.1] ++ (betwn(core r) z'.1 y.1 ++ [y.1])`
的 s2 部分（`newVs` 由单点段在装配处补）。 -/
theorem ml1CoreS2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py pz py1 pz1 : List Dart}
    (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hypy : ly L r x ∈ py)
    (hzpz : ztrans L N r x 0 ∈ pz)
    (hpy1 : py1 ∈ parts L (ml1S2 L N r x))
    (hpz1 : pz1 ∈ parts L (ml1S2 L N r x))
    (hypy1 : ly L r x ∈ py1)
    (hzpz1 : ztrans L N r x 0 ∈ pz1)
    (hpy1head : py1.head! = py.head!)
    (hpz1last : pz1.getLast! = pz.getLast!)
    (hpartsA2 : parts L (between r pz.getLast! py.head!) = between (parts L r) pz py) :
    core L (ml1S2 L N r x)
      = [(prevEl r (lz L N r x)).1] ++ (between (core L r)
          (prevEl r (lz L N r x)).1 (ly L r x).1 ++ [(ly L r x).1]) := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, -, hy1fst, hz1fst, hzy⟩ :=
    ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hzr
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hpy1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hpz1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  -- state-1 端点 FST
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hf2mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.sndMemRtran1 L hL hgn hm hnf
  have hparts2 := ml1SplitSndParts L hL hgn hm hnf
  have hS2eq : ml1S2 L N r x = [ztrans L N r x 0] ++
      (between r (ztrans L N r x 0) (ly L r x) ++ [ly L r x]) := rfl
  have hparts2' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2
      = parts L (ml1S2 L N r x) ++ (between (findFaceDarts L x) (ly L r x)
          (lz L N r x)).map (fun d => [d]) := by
    rw [hparts2, hS2eq]
    rfl
  have hpy1f2 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 := by
    rw [hparts2']
    exact List.mem_append_left _ hpy1
  have hpz1f2 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 := by
    rw [hparts2']
    exact List.mem_append_left _ hpz1
  have hpz1hfst : pz1.head!.1 = (prevEl r (ztrans L N r x 0)).1 :=
    (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hpz1f2 hzpz1).symm.trans
      hz1fst.symm
  have hpy1hfst : py1.head!.1 = (ly L r x).1 :=
    (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hpy1f2 hypy1).symm
  -- parts L s2 的 HD/LAST 分解
  have hspne : parts L (ml1S2 L N r x) ≠ [] :=
    Kepler.Text.MoreLemma2Island2.partsNonnil L hsne
  have hspnd : (parts L (ml1S2 L N r x)).Nodup :=
    Kepler.Text.MoreLemma2Island2.uniqParts L hsnd hsne
  have hheadne2 : (parts L (ml1S2 L N r x)).head! ≠ (parts L (ml1S2 L N r x)).getLast! := by
    intro h
    have h1 := ml1S2HdParts L hL hgn hm hnf hpz1 hzpz1
    have h2 := ml1S2LastParts L hL hgn hm hnf hpy1 hypy1
    rw [h1, h2] at h
    exact ml1S2PartsNe L hL hgn hm hnf hpy1 hpz1 hypy1 hzpz1 h
  have hpartsOrder : parts L (ml1S2 L N r x)
      = [pz1] ++ (between (parts L (ml1S2 L N r x)) pz1 py1 ++ [py1]) := by
    have h := Kepler.Text.TameSpine.eqHdLastBetwn (r := parts L (ml1S2 L N r x))
      hspne hspnd hheadne2
    rw [ml1S2HdParts L hL hgn hm hnf hpz1 hzpz1,
      ml1S2LastParts L hL hgn hm hnf hpy1 hypy1] at h
    rw [betweenEqOfLawful (e := List.instBEq) (f := instBEqOfDecidableEq)
      (he := inferInstance) (hf := inferInstance) (parts L (ml1S2 L N r x)) pz1 py1]
    exact h
  -- betwn of parts 折回 r
  have hbp := ml1BetwnPartsS2 L hL hgn hm hnf hpy hpz hypy hzpz hpy1 hpz1
    hypy1 hzpz1 hpy1head hpz1last hpartsA2
  -- 端点 FST 表（aqs_fstHdMapBetwn，角色互换）
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
  have hzyfst : (ztrans L N r x 0).1 ≠ (ly L r x).1 :=
    fun h => ml1FstNe L hL hgn hm hnf h.symm
  have hmap := Kepler.Text.TameSpine.aqs_fstHdMapBetwn L hL hnS hm.2.2.1
    (sp := parts L r) (Kepler.Text.ChainBridge.parts_eq_partsSpine L r).symm
    (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hpz hpy hzpz hypy hzyfst
  have hmap' : (between (parts L r) pz py).map (fun p => p.head!.1)
      = between (core L r) (prevEl r (ztrans L N r x 0)).1 (ly L r x).1 := by
    rw [hmap, ← coreMapHead, ← hz1fst]
  have hbp' : (between (parts L (ml1S2 L N r x)) pz1 py1).map (fun p => p.head!.1)
      = between (core L r) (prevEl r (ztrans L N r x 0)).1 (ly L r x).1 := by
    rw [hbp, hmap']
  -- 组装
  calc core L (ml1S2 L N r x)
      = (parts L (ml1S2 L N r x)).map (fun p => p.head!.1) := coreMapHead L _
    _ = ([pz1] ++ (between (parts L (ml1S2 L N r x)) pz1 py1 ++ [py1])).map
          (fun p => p.head!.1) := by
        conv_lhs => rw [hpartsOrder]
    _ = [pz1.head!.1] ++ (((between (parts L (ml1S2 L N r x)) pz1 py1).map
          (fun p => p.head!.1)) ++ [py1.head!.1]) := by
        rw [List.map_append, List.map_cons, List.map_nil, List.map_append]
        rfl
    _ = [(prevEl r (ztrans L N r x 0)).1] ++ (between (core L r)
          (prevEl r (ztrans L N r x 0)).1 (ly L r x).1 ++
          [(ly L r x).1]) := by
        rw [hpz1hfst, hpy1hfst, hbp']
    _ = [(prevEl r (lz L N r x)).1] ++ (between (core L r)
          (prevEl r (lz L N r x)).1 (ly L r x).1 ++ [(ly L r x).1]) := rfl

/-- **主机 8b（HOL `core_split_normal_list`，:2028–:3091）**：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ ¬final_list L r ⇒
coreSplitNormalList L N r x`。 -/
theorem coreSplitNormalListThm (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    coreSplitNormalList L N r x := by
  obtain ⟨hyr, hzr, hz1r, hy1r, hyf, hzf, hy1fst, hz1fst, hzy⟩ :=
    ml1SetupMem L hL hgn hm hnf
  obtain ⟨py, pz, hpy, hpz, hy1py, hz1pz, hpyfst, hpzfst, hpyz, hpartsA⟩ :=
    ml1PartsA L hL hgn hm hnf
  -- f1 半的 py1/pz1（含 y1/z1）
  obtain ⟨py1, hpy1, hy1py1, hpy1last⟩ := ml1Py1 L hL hgn hm hnf hpy hy1py
  obtain ⟨pz1, hpz1, hz1pz1, hpz1head⟩ := ml1Pz1 L hL hgn hm hnf hpz hz1pz
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  -- f2 半的 py2/pz2（含 y/z；与 f1 的 py/pz 可能不同块）
  obtain ⟨py2, hpy2, hypy2⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hyr
  obtain ⟨pz2, hpz2, hzpz2⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hzr
  -- f2 半的 pz1/py1（含 z/y）
  obtain ⟨pz1b, hpz1b, hzpz1b, hpz1blast⟩ := ml1Pz1Last L hL hgn hm hnf hpz2 hzpz2
  obtain ⟨py1b, hpy1b, hypy1b, hpy1bhead⟩ := ml1Py1Head L hL hgn hm hnf hpy2 hypy2
  -- f1 betwn 折回与 core 方程
  have hS1 := ml1CoreS1 L hL hgn hm hnf hpy hpz hy1py hz1pz hpy1 hpz1
    hy1py1 hz1pz1 hpy1last hpz1head hpartsA
  -- f2 betwn 折回（对称 parts_betwn）与 core 方程
  have hpartsA2 := ml1PartsBetwnSym L hL hgn hm hnf hpz2 hpy2 hzpz2 hypy2
  have hS2 := ml1CoreS2 L hL hgn hm hnf hpy2 hpz2 hypy2 hzpz2 hpy1b hpz1b
    hypy1b hzpz1b hpy1bhead hpz1blast hpartsA2
  -- 块表 head! 表
  have hg := ml1GpartsMapHead L hL hgn hm hnf
  -- f1 方程
  have hS1eq : ml1S L N r x = [nextEl r (ly L r x)] ++
      (between r (nextEl r (ly L r x)) (prevEl r (lz L N r x)) ++
        [prevEl r (lz L N r x)]) := rfl
  have hparts1' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 = (((between (findFaceDarts L x) (ly L r x)
        (lz L N r x)).map (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
      ++ parts L (ml1S L N r x) := by
    rw [ml1SplitFstParts L hL hgn hm hnf, ← hS1eq]
  have hf1 : core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).1
      = ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
          (fun d => d.1)).reverse
        ++ ([(ly L r x).1] ++ (between (core L r) (ly L r x).1
            (prevEl r (lz L N r x)).1 ++ [(prevEl r (lz L N r x)).1])) := by
    calc core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).1
        = (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).1).map (fun p => p.head!.1) := coreMapHead L _
      _ = ((((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse)
            ++ parts L (ml1S L N r x)).map (fun p => p.head!.1) := by rw [hparts1']
      _ = (((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse).map
            (fun p => p.head!.1)
          ++ (parts L (ml1S L N r x)).map (fun p => p.head!.1) := List.map_append
      _ = ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => d.1)).reverse ++ core L (ml1S L N r x) := by
          rw [hg, ← coreMapHead]
      _ = ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => d.1)).reverse
          ++ ([(ly L r x).1] ++ (between (core L r) (ly L r x).1
              (prevEl r (lz L N r x)).1 ++ [(prevEl r (lz L N r x)).1])) := by
          rw [hS1]
  -- f2 方程
  have hS2eq : ml1S2 L N r x = [ztrans L N r x 0] ++
      (between r (ztrans L N r x 0) (ly L r x) ++ [ly L r x]) := rfl
  have hparts2' : parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2
      = parts L (ml1S2 L N r x) ++ (between (findFaceDarts L x) (ly L r x)
          (lz L N r x)).map (fun d => [d]) := by
    rw [ml1SplitSndParts L hL hgn hm hnf, hS2eq]
    rfl
  have hf2 : core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).2
      = ([(prevEl r (lz L N r x)).1] ++ (between (core L r)
          (prevEl r (lz L N r x)).1 (ly L r x).1 ++ [(ly L r x).1]))
        ++ ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
            (fun d => d.1)) := by
    calc core L (splitNormalList L r (findFaceDarts L x) (ly L r x)
          (prevEl r (lz L N r x))).2
        = (parts L (splitNormalList L r (findFaceDarts L x) (ly L r x)
            (prevEl r (lz L N r x))).2).map (fun p => p.head!.1) := coreMapHead L _
      _ = (parts L (ml1S2 L N r x) ++ (between (findFaceDarts L x) (ly L r x)
            (lz L N r x)).map (fun d => [d])).map (fun p => p.head!.1) := by
          rw [hparts2']
      _ = (parts L (ml1S2 L N r x)).map (fun p => p.head!.1)
          ++ ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
              (fun d => [d])).map (fun p => p.head!.1) := List.map_append
      _ = core L (ml1S2 L N r x)
          ++ ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
              (fun d => d.1)) := by
          congr 1
          · exact (coreMapHead L _).symm
          · rw [List.map_map]
            exact List.map_congr_left (fun d _ => by rfl)
      _ = ([(prevEl r (lz L N r x)).1] ++ (between (core L r)
            (prevEl r (lz L N r x)).1 (ly L r x).1 ++ [(ly L r x).1]))
          ++ ((between (findFaceDarts L x) (ly L r x) (lz L N r x)).map
              (fun d => d.1)) := by
          rw [hS2]
  unfold coreSplitNormalList
  dsimp only
  exact ⟨hf1, hf2⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.coreMapHead
#print axioms Kepler.Text.Reduction5.beqEqOfLawful
#print axioms Kepler.Text.Reduction5.containsEqOfLawful
#print axioms Kepler.Text.Reduction5.splitAtRecEqOfLawful
#print axioms Kepler.Text.Reduction5.splitAtEqOfLawful
#print axioms Kepler.Text.Reduction5.betweenEqOfLawful
#print axioms Kepler.Text.Reduction5.ml1SpinePair
#print axioms Kepler.Text.Reduction5.ml1GpartsMapHead
#print axioms Kepler.Text.Reduction5.ml1PartsBetwnSym
#print axioms Kepler.Text.Reduction5.ml1BetwnPartsS1
#print axioms Kepler.Text.Reduction5.ml1BetwnPartsS2
#print axioms Kepler.Text.Reduction5.ml1CoreS1
#print axioms Kepler.Text.Reduction5.ml1CoreS2
#print axioms Kepler.Text.Reduction5.coreSplitNormalListThm
