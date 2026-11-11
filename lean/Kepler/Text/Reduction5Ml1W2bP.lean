/-
  Kepler.Text.Reduction5Ml1W2bP — W2b B3/B5：`py1` 的 LAST 归属与 s 端点严格性
  （HOL More_lemma1.hl :2236–:2330）。**B4（`pz1.head! = pz.head!`）本轮冻结**，
  卡点与路线见交付 DELIVERY_ml3 §冻结表。

  ┌─ 件目与 HOL 锚 ────────────────────────────────────────────────
  │ B3 `ml1Py1`（:2248–:2280）：`∃ py1 ∈ parts L s, y1 ∈ py1 ∧ py1.getLast! = py.getLast!`。
  │ B5 `ml1SLastNe`（:2257–:2280）：`py1.getLast! ≠ s.getLast!` 且
  │    `nextEl s py1.getLast! = nextEl r py1.getLast!`。
  │ 内核 `ml1PartEnd`（LAST 侧）：`d ∈ p ∩ p1` ⇒ `p1.getLast! = p.getLast!`，
  │    B3 直接实例（下一轮 B4 的 HD 侧需另一内核）。
  │ 辅件：`ml1NormalNtrans1`（state-1 normalList 链槽）、`ml1Y1NeZ1`、
  │    `ml1PartsHeadFstNodup`、`ml1PartsMemImp`、`ml1SMemImpR`。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（DIFFERS，按 GSUBGOAL 语句重推，不逐行转写）──────────────
  │ state-1 normalList 槽由 `aqs_aqNormalList`（aq1–aq5 无条件件）+ 链/spine
  │ 桥供；`parts L split.1` 的成员由 W2a-1 `ml1SplitFstParts` 供；
  │ `normalConditionLastPartsChain` 在 r 与 state-1 两侧各一发：
  │   · state-1（split.1）给 `¬(nextEl split.1 (LAST p1) = f_list …)`；
  │   · `nextElCat2` + `nextCatBetwnSame` 把 `nextEl split.1` 降回 `nextEl r`；
  │   · 状态 0（r）给 `LAST p1 = LAST p`。
  │ 与 HOL 的差异：HOL 以 `parts_fst` 两次 + `uniq_imp_inj` 定位 `LAST py1 ∈ py`；
  │ 本条相同（块首 FST 表 `Nodup` + `inj_on_of_nodup_map`）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5Ml1W2bU
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2QuotientAlt2
import Kepler.Text.Reduction5Ml1Leaves
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.Reduction5J5BetweenInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §0 共享小件 -/

/-- `AqiunppSlot` 的链形（`aqiunpp` 逐点；同 W2a 私件、本文件自持）。 -/
private theorem ml1bAqSlot (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn N r x hm i => Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i

/-- 状态 1 的 `normal_list`（HOL `AQ_normal_list`，AQ8.hl:39）：
`normalList L hL (ntrans L N r x 1)`——链形。 -/
theorem ml1NormalNtrans1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    normalList L hL (ntrans L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
  have hnSp : Kepler.Text.TameSpine.NormalListSpine hL
      (Kepler.Text.TameSpine.ntransSpine L N r x 1) :=
    Kepler.Text.TameSpine.aqs_aqNormalList L hL
      (Kepler.Text.TameSpine.aq1 L hL) (Kepler.Text.TameSpine.aq2 L hL)
      (Kepler.Text.TameSpine.aq3 L hL) (Kepler.Text.TameSpine.aq4 L hL)
      (Kepler.Text.TameSpine.aq5 L hL) hgn hmS
  rw [Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL
    (ml1bAqSlot L hL) hm 1]
  exact (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL _).mpr hnSp

/-- `y1 ≠ z1`（FST 判别：`y1.1 = y.1 ≠ z.1 = z1.1`）。 -/
theorem ml1Y1NeZ1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) := by
  obtain ⟨-, -, -, -, -, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  intro h
  apply ml1FstNe L hL hgn hm hnf
  have := congrArg Prod.fst h
  rw [hy1fst, hz1fst] at this
  exact this

/-- `(parts L r)` 的块首 FST 表无重（`quotientAllUniq` 换装）。 -/
theorem ml1PartsHeadFstNodup (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hrN : r ∈ N) :
    ((parts L r).map (fun q => q.head!.1)).Nodup := by
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

/-- `parts L r` 的成员回落到 `r`（链形 `MEM_PARTS_IMP`，AQ8.hl:386）。 -/
theorem ml1PartsMemImp (L : fgraph ℕ) {r p : List Dart}
    (hun : r.Nodup) (hne : r ≠ []) (hp : p ∈ parts L r) :
    ∀ a ∈ p, a ∈ r := by
  intro a ha
  have hflat : (parts L r).flatten = r :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hun hne
  have hmem : a ∈ (parts L r).flatten := List.mem_flatten.mpr ⟨p, hp, ha⟩
  rwa [hflat] at hmem

/-- `s` 的成员回落到 `r`（s = [y1] ++ (betwn ++ [z1]) 三段）。 -/
theorem ml1SMemImpR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {a : Dart} (ha : a ∈ ml1S L N r x) : a ∈ r := by
  obtain ⟨hyr, -, hz1r, hy1r, -, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have ha' : a ∈ [nextEl r (ly L r x)] ++
      (between r (nextEl r (ly L r x)) (prevEl r (ztrans L N r x 0)) ++
        [prevEl r (ztrans L N r x 0)]) := ha
  rcases List.mem_append.mp ha' with h | h
  · rw [List.mem_singleton] at h
    subst h
    exact hy1r
  · rcases List.mem_append.mp h with h | h
    · rw [Kepler.Text.Reduction5.betweenInstEq] at h
      exact Kepler.Text.Reduction5.betwnMem h
    · rw [List.mem_singleton] at h
      subst h
      exact hz1r

/-! ## §1 B3：`ml1PartEnd` 内核（端方向：`.getLast!`）与 `ml1Py1` -/

/-- **W2b-B3 内核**：`d ∈ p ∩ p1`（`d` 的 FST 不等于 z 的 FST），
`p ∈ parts L r`、`p1 ∈ parts L s`（且 `p1 ∈ parts L split.1`，供 state-1
`normal_list`），则 `p1.getLast! = p.getLast!`。

证：state-1（`split.1`）的 normal_condition 给 `¬(nextEl split.1 (LAST p1) = f_list …)`；
`nextElCat2`（s 是 split.1 的后缀）+ `nextCatBetwnSame`（s 在弧 [y1,z1] 上）
把 `nextEl` 降回 `nextEl r`；`LAST p1 ∈ p` 由块首 FST 单射（`inj_on_of_nodup_map`）
定位；状态 0（r）的 normal_condition 收口 `LAST p1 = LAST p`。 -/
theorem ml1PartEnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0))
    {p p1 : List Dart} (hp : p ∈ parts L r)
    (hp1 : p1 ∈ parts L (ml1S L N r x))
    (hp1f1 : p1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1)
    {d : Dart} (hd : d ∈ p) (hd1 : d ∈ p1)
    (hdfst : d.1 ≠ (ztrans L N r x 0).1) :
    p1.getLast! = p.getLast! := by
  obtain ⟨-, hzr, hz1r, hy1r, hyf, -, -, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hds : d ∈ ml1S L N r x := ml1PartsMemImp L hsnd hsne hp1 d hd1
  have hp1ne : p1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p1 hp1
  have hlastmem : p1.getLast! ∈ p1 := Kepler.Text.TameSpine.aqs_getLastMem hp1ne
  have hlasts : p1.getLast! ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hp1 _ hlastmem
  have hlastr : p1.getLast! ∈ r := ml1SMemImpR L hL hgn hm hnf hlasts
  -- state-1 normalList 与 split.1 的成员/无重
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hf1mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.fstMemRtran1 L hL hgn hm hnf
  have hf1nd : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).1.Nodup :=
    (List.nodup_flatten.mp hn1.1).1 _ hf1mem
  -- p1 的 LAST 与 d 同 FST
  have hf1 : p1.getLast!.1 = d.1 := by
    rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hp1f1 hlastmem]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf1mem hp1f1 hd1).symm
  -- LAST p1 ≠ LAST s = z1
  have hneLast : p1.getLast! ≠ (ml1S L N r x).getLast! := by
    intro h
    have h1 : p1.getLast!.1 = (ztrans L N r x 0).1 := by
      rw [h, ml1SLast L hL hgn hm hnf, hz1fst]
    exact hdfst (hf1.symm.trans h1)
  have hneZ1 : p1.getLast! ≠ prevEl r (ztrans L N r x 0) := by
    intro h
    exact hneLast (by rw [ml1SLast L hL hgn hm hnf]; exact h)
  -- state-1 normal_condition：¬(nextEl split.1 (LAST p1) = f_list …)
  have hneg1 : ¬(nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).1 p1.getLast!
      = fList L (eList p1.getLast!)) :=
    (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hn1
      hm.1.edgeNondegenerate hf1mem hp1f1 hlastmem).mpr rfl
  -- split.1 = g_darts ++ s（g_darts = new1.reverse）
  have hnextPrev : nextEl r (prevEl r (lz L N r x)) = ztrans L N r x 0 := by
    rw [Kepler.Text.Reduction5.nextElInstEq, Kepler.Text.Reduction5.nextPrevId hrnd]
    rfl
  have hsplit : (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).1
      = ((between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)).map
          (fun d => (Kepler.Text.TameSpine.ndSpine L d).reverse)).reverse.flatten
        ++ ml1S L N r x := by
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
  -- nextEl 从 split.1 降到 s（nextElCat2：s 是 split.1 后缀）
  have hnext1 : nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).1 p1.getLast!
      = nextEl (ml1S L N r x) p1.getLast! := by
    rw [hsplit] at hf1nd ⊢
    exact Kepler.Text.TameSpine.nextElCat2 hf1nd hlasts hneLast
  -- nextEl 再从 s 降到 r（nextCatBetwnSame：LAST p1 ∈ 弧 [y1,z1]）
  have hnext2 : nextEl (ml1S L N r x) p1.getLast! = nextEl r p1.getLast! :=
    Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hz1r hy1r hyz.symm hlasts
      (by unfold ml1S; rfl) hneZ1
  -- LAST p1 ∈ p（块首 FST 单射定位）
  obtain ⟨p', hp', hlastp'⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hlastr
  have hpfst : p1.getLast!.1 = p'.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp' hlastp'
  have hpd : d.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hd
  have hpp : p' = p := by
    have hfst : p'.head!.1 = p.head!.1 := by
      rw [← hpfst, hf1]
      exact hpd
    exact List.inj_on_of_nodup_map
      (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hp' hp hfst
  have hdlp : p1.getLast! ∈ p := by
    rw [← hpp]
    exact hlastp'
  -- 状态 0 normal_condition 收口
  refine (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hm.2.1
    hm.1.edgeNondegenerate hm.2.2.1 hp hdlp).mp ?_
  rw [← hnext2, ← hnext1]
  exact hneg1

/-- **W2b-B3（HOL :2248–:2280，`LAST py1 = LAST py`）**：
`s` 中含 `y1` 的块 `py1` 的末元 = `parts L r` 中含 `y1` 的块 `py` 的末元。 -/
theorem ml1Py1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py : List Dart} (hpy : py ∈ parts L r)
    (hy1py : nextEl r (ly L r x) ∈ py) :
    ∃ py1 : List Dart, py1 ∈ parts L (ml1S L N r x) ∧
      nextEl r (ly L r x) ∈ py1 ∧ py1.getLast! = py.getLast! := by
  obtain ⟨-, -, -, -, -, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hyzFst : (nextEl r (ly L r x)).1 ≠ (ztrans L N r x 0).1 := by
    rw [hy1fst]
    exact fun h => ml1FstNe L hL hgn hm hnf h
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  obtain ⟨py1, hpy1, hy1py1⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hsnd hy1s
  have hparts1 := ml1SplitFstParts L hL hgn hm hnf
  have hpy1f1 : py1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).1 := by
    rw [hparts1]
    exact List.mem_append_right _ hpy1
  exact ⟨py1, hpy1, hy1py1,
    ml1PartEnd L hL hgn hm hnf hyz hpy hpy1 hpy1f1 hy1py hy1py1 hyzFst⟩


/-! ## §2 B5：`s` 端点严格性与 next_el 归约 -/

/-- **W2b-B5（HOL :2257–:2280）**：给定 B3 的 `LAST py1 = LAST py`，
`py1.getLast! ≠ s.getLast!` 且 `nextEl s py1.getLast! = nextEl r py1.getLast!`。
（`LAST py1` 的 FST = `y1` 的 FST ≠ `z1` 的 FST；`next_cat_betwn_same` 在弧
`[y1, z1]` 上降回 r。） -/
theorem ml1SLastNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {py py1 : List Dart} (hpy : py ∈ parts L r)
    (hpy1 : py1 ∈ parts L (ml1S L N r x))
    (hy1py : nextEl r (ly L r x) ∈ py)
    (hlast : py1.getLast! = py.getLast!) :
    py1.getLast! ≠ (ml1S L N r x).getLast! ∧
      nextEl (ml1S L N r x) py1.getLast! = nextEl r py1.getLast! := by
  obtain ⟨-, -, hz1r, hy1r, -, -, hy1fst, hz1fst, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hyz : nextEl r (ly L r x) ≠ prevEl r (ztrans L N r x 0) :=
    ml1Y1NeZ1 L hL hgn hm hnf
  have hsnd : (ml1S L N r x).Nodup := ml1SUniq L hL hgn hm hnf hyz
  have hy1s : nextEl r (ly L r x) ∈ ml1S L N r x := (ml1SMem L hL hgn hm hnf).1
  have hsne : ml1S L N r x ≠ [] := List.ne_nil_of_mem hy1s
  have hpne : py ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py hpy
  have hp1ne : py1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ py1 hpy1
  have hplastmem : py.getLast! ∈ py := Kepler.Text.TameSpine.aqs_getLastMem hpne
  have hp1lastmem : py1.getLast! ∈ py1 := Kepler.Text.TameSpine.aqs_getLastMem hp1ne
  have hlasts : py1.getLast! ∈ ml1S L N r x :=
    ml1PartsMemImp L hsnd hsne hpy1 _ hp1lastmem
  -- LAST py1 的 FST = y1 的 FST
  have hfst1 : py1.getLast!.1 = py.head!.1 := by
    rw [hlast]
    exact Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hplastmem
  have hfst2 : (nextEl r (ly L r x)).1 = py.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpy hy1py
  have hy1ne : (nextEl r (ly L r x)).1 ≠ (ztrans L N r x 0).1 := by
    rw [hy1fst]
    exact fun h => ml1FstNe L hL hgn hm hnf h
  have hneZ1 : py1.getLast! ≠ prevEl r (ztrans L N r x 0) := by
    intro h
    have h1 : py1.getLast!.1 = (ztrans L N r x 0).1 := by
      rw [h]
      exact hz1fst
    exact hy1ne (hfst2.trans (hfst1.symm.trans h1))
  constructor
  · intro h
    exact hneZ1 (by rw [h, ml1SLast L hL hgn hm hnf])
  · exact Kepler.Text.TameSpine.nextCatBetwnSame r
      (Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1)
      hz1r hy1r hyz.symm hlasts (by unfold ml1S; rfl) hneZ1

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1NormalNtrans1
#print axioms Kepler.Text.Reduction5.ml1Y1NeZ1
#print axioms Kepler.Text.Reduction5.ml1PartsHeadFstNodup
#print axioms Kepler.Text.Reduction5.ml1PartsMemImp
#print axioms Kepler.Text.Reduction5.ml1SMemImpR
#print axioms Kepler.Text.Reduction5.ml1PartEnd
#print axioms Kepler.Text.Reduction5.ml1Py1
#print axioms Kepler.Text.Reduction5.ml1SLastNe
