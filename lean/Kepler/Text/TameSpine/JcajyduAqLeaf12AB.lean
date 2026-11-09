/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12AB — AQ12 叶 W-F3e-iii ②
  （F 支 f1 半 + F 支组合器）。

  HOL：AQ12.hl:3870-:4084（215 行）。`p ∈ parts f1`，
  `f1 = [nextEl r l'y] ++ betwn r (nextEl r l'y) (prevEl r l'z) ++ [prevEl r l'z]`。

  件目（接单报价）：3 件 / 1 文件；估 240–330（≤350）。
  · `aq12ab_flagConjunctTwoFF1`：f1 半主定理。
  · `aq12ab_flagConjunctTwoF`：F 支组合器（62 的 mem_append 二分转调
    12AA 窗口块半 + 本件 f1 半）。
  · `aq12ab_getLast!_append`（private）。

  路线（比 HOL 五路 case split 更短的两分）：
  · **F 的 normal_list 面**：F ∈ ntrans 1、ntrans 1 为 NormalListSpine
    （`aqs_aqNormalList` + aq1..aq5 已落库定理）⇒
    `nextEl F y = fList y`（`normalListPartsNextLast`）。
  · y ≠ Z1 支：`nextEl F y = nextEl f1 y = nextEl r y`
    （`nextElCat2` + `nextCatBetwnSame`，f1 是 r 的弧段）⇒ `nextEl r y = fList y`
    ⇒ 取 r-part q ∋ y（`partsMemExists`）；若 y ≠ LAST q 则
    `nextEl r y = nextEl q y = fList(eList y)`（`nextElPartsUnlast` + `partsNextUnlast`）
    ⇒ `fList y = fList(eList y)` ⇒ `y = eList y`（`fListInjDarts`）撞 edge 非退化
    ⇒ **y = LAST q**。再 `y ∉ sList`（61 `aqs_sListNotInFst`：y ∈ f1 ⊆ FST）
    ⇒ SFlag 第二合取（r'=q ∈ N）⇒ `eList y ∈ sList ++ FinalDart N`
    ⇒ sList 支（60 → SND=final 行）或 FinalDart 支（memReplaceOfNeMem 转移）。
  · y = Z1 支：r 的 loop 步 `nextEl r Z1 = Z`（`nextElPrevElUniq`）由
    `loopListSpine` 给 `Z = fList Z1 ∨ Z = fList(eList Z1)`；`prevRNotEqF`
    排除前者 ⇒ `fList(eList Z1) = Z` ⇒ `findFace(eList Z1) = findFace x`
    ⇒ `eList Z1 = prevEl (findFace x) Z`（`prevEl_nextEl`）；该前驱
    在 `betwn f l'y l'z` 为空时为 `l'y`（`betwnNilNextOfNodup`），非空时为其
    `getLast!`（`nextLastBetwn`）——两支都在 SND 内 ⇒ FinalDart。
  不吃 `h4`。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12AA
import Kepler.Text.TameSpine.JcajyduAqLeaf12W
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.JcajyduAqTowerE2
import Kepler.Text.TameSpine.JcajyduAqSplit1H
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b
import Kepler.Text.TameSpine.JcajyduAqLeaf5
import Kepler.Text.TameSpine.JcajyduAqSplit1C
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.TameList53
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_nodup nextEl_mem_of_mem prevEl_mem_of_mem prevEl_nextEl)

/-! ## §0 列表末元私件 -/

/-- `(s ++ t).getLast! = t.getLast!`（`t ≠ []`）。 -/
private theorem aq12ab_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-! ## §1 f1 半主定理（HOL AQ12.hl:3870-:4084） -/

/-- **HOL AQ12.hl:3870-:4084（F 支 · f1 半）**：
`p ∈ parts f1` ⇒ `eList (LAST p) ∈ FinalDartList (ntrans 1)`。 -/
theorem aq12ab_flagConjunctTwoFF1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfinRtrans : finalListSpine L (rtransSpine L N r x 1))
    {p : List (ℕ × ℕ)}
    (hp : p ∈ partsSpine L ([nextEl r (lYSpine L r x)]
      ++ between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
      ++ [prevEl r (lZSpine L N r x)])) :
    eList (p.getLast!) ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hrne : r ≠ [] := hm.1.2.1.2.1 r hm.1.2.2.1
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hY1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hZ1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hY1Z1 : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  -- f1 段
  set f1 := [nextEl r (lYSpine L r x)]
    ++ between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
    ++ [prevEl r (lZSpine L N r x)] with hf1def
  have hf1ne : f1 ≠ [] := by rw [hf1def]; simp
  have hf1nd : f1.Nodup := by
    rw [hf1def]
    exact uniqAppendBetwn hrnd hY1r hZ1r hY1Z1
  have hpf1 : p ∈ partsSpine L f1 := by rw [hf1def]; exact hp
  -- y := LAST p ∈ f1 ⊆ r
  have hyf1 : p.getLast! ∈ f1 := by
    have hpne : p ≠ [] := partsAllNonnil L hf1nd hf1ne p hpf1
    have hmem : p.getLast! ∈ p := by
      rw [getLast!EqGetLast hpne]; exact List.getLast_mem hpne
    exact memPartsImp L hf1nd hf1ne hpf1 _ hmem
  have hyr' : p.getLast! ∈ r := by
    have h := hyf1
    rw [hf1def] at h
    rcases List.mem_append.mp h with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · rw [List.mem_singleton] at h2; rw [h2]; exact hY1r
      · exact betwnMem h2
    · rw [List.mem_singleton] at h1; rw [h1]; exact hZ1r
  have hyD : p.getLast! ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 _ (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hyr'⟩)
  -- S = SND（f-split），final
  set S := (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
    (prevEl r (lZSpine L N r x))).2 with hSdef
  have hfaceY : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hS2 : S = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x) := by
    rw [hSdef]
    simp only [splitNormalListSpine]
    rw [hnextz1]
  have hsplitS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 = S := by
    rw [hSdef, hfaceY]
  have hsplitF : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1
      = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 := by
    rw [hfaceY]
  have hmemS : S ∈ ntransSpine L N r x 1 := by
    rw [← hsplitS]
    exact sndMemRtran1 L hm.1.2.2.1 hf
  have hrtrans : rtransSpine L N r x 1 = S := by
    show ((transformListSpine L x)^[1] (N, r)).2 = _
    rw [Function.iterate_one]
    simp only [transformListSpine, if_neg hf]
    rw [hsplitS]
  have hfinS : finalListSpine L S := by rw [← hrtrans]; exact hfinRtrans
  -- FST 的 g ++ f1 分解 与 F ∈ ntrans 1 / normal_list
  set g := (List.map (ndSpine L) (between (findFaceDarts L x) (lYSpine L r x)
    (lZSpine L N r x))).flatten.reverse with hgdef
  have hFSTeq : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 = g ++ f1 := by
    rw [hgdef, hf1def, split1Unfold, hnextz1]
  have hFmem : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 := by
    rw [← hsplitF]
    exact aq8w2b_fstMemRtran1 L hf
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  have hFnd : (g ++ f1).Nodup := by
    rw [← hFSTeq]
    exact (normalListUniqNonnil hnN hFmem).1
  have hnF : nextEl (g ++ f1) (p.getLast!) = fList L (p.getLast!) := by
    rw [← hFSTeq]
    have h62 := aq12w_catFstSplitNormalParts L hL hgn hm hf
    refine normalListPartsNextLast L hL hnN hFmem ?_
    rw [h62]
    exact List.mem_append.mpr (Or.inr hpf1)
  have hf1last : f1.getLast! = prevEl r (lZSpine L N r x) := by
    rw [hf1def,
      aq12ab_getLast!_append _ (by simp : ([prevEl r (lZSpine L N r x)] : List (ℕ × ℕ)) ≠ [])]
    simp
  by_cases hyZ1 : p.getLast! = prevEl r (lZSpine L N r x)
  · -- ⭐ y = Z1：loop 步 + prevRNotEqF + betwnNil/nextLastBetwn
    rw [hyZ1]
    have hZ1D : prevEl r (lZSpine L N r x) ∈ listOfDarts L :=
      normalListListOfDarts hm.1.2.1 _
        (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hZ1r⟩)
    have heD : eList (prevEl r (lZSpine L N r x)) ∈ listOfDarts L := goodListEList hL hZ1D
    have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
    have hstep := (hloop (prevEl r (lZSpine L N r x)) hZ1r).2
    have hnextZ : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
      nextElPrevElUniq hrnd _
    rw [hnextZ] at hstep
    have hZf : lZSpine L N r x = fList L (eList (prevEl r (lZSpine L N r x))) :=
      hstep.resolve_left (fun h =>
        (prevRNotEqF L hL hgn hunL hm hf) h.symm)
    -- fList(eList Z1) = Z ⇒ findFace(eList Z1) = findFace x
    have hZfE : lZSpine L N r x ∈ findFaceDarts L (eList (prevEl r (lZSpine L N r x))) := by
      have hmem : fList L (eList (prevEl r (lZSpine L N r x))) ∈
          findFaceDarts L (eList (prevEl r (lZSpine L N r x))) := by
        show nextEl (findFaceDarts L (eList (prevEl r (lZSpine L N r x))))
          (eList (prevEl r (lZSpine L N r x))) ∈ _
        exact nextEl_mem_of_mem ((dart_in_face L _).mpr heD)
      exact Eq.mp (congrArg (fun w =>
        w ∈ findFaceDarts L (eList (prevEl r (lZSpine L N r x)))) hZf.symm) hmem
    have hfaceE : findFaceDarts L (eList (prevEl r (lZSpine L N r x)))
        = findFaceDarts L (lZSpine L N r x) :=
      (aq10_memFindFaceImpFacesEq hL.1 hZfE).symm
    have hZx : lZSpine L N r x ∈ findFaceDarts L x := (pplhuljV0 L hL hgn hunL hm hf).2.1
    have hfaceZ : findFaceDarts L (lZSpine L N r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 hZx
    have hfaceEf : findFaceDarts L (eList (prevEl r (lZSpine L N r x)))
        = findFaceDarts L x := hfaceE.trans hfaceZ
    have hnextEf : nextEl (findFaceDarts L x) (eList (prevEl r (lZSpine L N r x)))
        = lZSpine L N r x := by
      rw [← hfaceEf]
      exact hZf.symm
    have heF : eList (prevEl r (lZSpine L N r x)) ∈ findFaceDarts L x := by
      rw [← hfaceEf]
      exact (dart_in_face L _).mpr heD
    have hprevE : prevEl (findFaceDarts L x) (lZSpine L N r x)
        = eList (prevEl r (lZSpine L N r x)) := by
      have h := prevEl_nextEl (findFaceDarts_nodup hL.1 x) heF
      rwa [hnextEf] at h
    have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
    have hYf : lYSpine L r x ∈ findFaceDarts L x := (pplhuljV0 L hL hgn hunL hm hf).1
    by_cases hWnil : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) = []
    · have hnextYZ : nextEl (findFaceDarts L x) (lYSpine L r x) = lZSpine L N r x :=
        betwnNilNextOfNodup hfnd hYf hZx hyz hWnil
      have hprevY : prevEl (findFaceDarts L x) (lZSpine L N r x) = lYSpine L r x := by
        have h := prevEl_nextEl hfnd hYf
        rwa [hnextYZ] at h
      have hEZ1 : eList (prevEl r (lZSpine L N r x)) = lYSpine L r x :=
        hprevE.symm.trans hprevY
      have hYS : lYSpine L r x ∈ S := by
        rw [hS2]
        exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))))
      exact List.mem_flatten.mpr
        ⟨S, List.mem_filter.mpr ⟨hmemS, by simpa using hfinS⟩, by rw [hEZ1]; exact hYS⟩
    · have hWlast : (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).getLast! ∈ between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x) := by
        rw [getLast!EqGetLast hWnil]; exact List.getLast_mem hWnil
      have hnextW : nextEl (findFaceDarts L x) (between (findFaceDarts L x)
          (lYSpine L r x) (lZSpine L N r x)).getLast! = lZSpine L N r x := by
        rw [getLast!EqGetLast hWnil]
        exact nextLastBetwn hYf hZx hfnd hyz hWnil
      have hprevW : prevEl (findFaceDarts L x) (lZSpine L N r x)
          = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).getLast! := by
        have hWmem : (between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x)).getLast! ∈ findFaceDarts L x :=
          betwnMem (f := findFaceDarts L x) (u := lYSpine L r x)
            (v := lZSpine L N r x) hWlast
        have h := prevEl_nextEl hfnd hWmem
        rwa [hnextW] at h
      have hWS : (between (findFaceDarts L x) (lYSpine L r x)
          (lZSpine L N r x)).getLast! ∈ S := by
        rw [hS2]
        exact List.mem_append.mpr (Or.inr hWlast)
      have hEZ1 : eList (prevEl r (lZSpine L N r x))
          = (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).getLast! :=
        hprevE.symm.trans hprevW
      exact List.mem_flatten.mpr
        ⟨S, List.mem_filter.mpr ⟨hmemS, by simpa using hfinS⟩, by rw [hEZ1]; exact hWS⟩
  · -- ⭐ y ≠ Z1：F-normal 步 + r-part 边界 + SFlag
    have hstep1 : nextEl (g ++ f1) (p.getLast!) = nextEl f1 (p.getLast!) :=
      nextElCat2 hFnd hyf1 (by rw [hf1last]; exact hyZ1)
    have hstep2 : nextEl f1 (p.getLast!) = nextEl r (p.getLast!) := by
      exact nextCatBetwnSame (r := r) (y := prevEl r (lZSpine L N r x))
        (z := nextEl r (lYSpine L r x)) (a := p.getLast!) (s := f1)
        hrnd hZ1r hY1r (Ne.symm hY1Z1) hyf1
        (by rw [hf1def]
            exact List.append_assoc [nextEl r (lYSpine L r x)]
              (between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)))
              [prevEl r (lZSpine L N r x)])
        hyZ1
    have hnextr : nextEl r (p.getLast!) = fList L (p.getLast!) :=
      hstep2.symm.trans (hstep1.symm.trans hnF)
    obtain ⟨q, hq, hyq⟩ := partsMemExists L hrnd hyr'
    have hyLastq : p.getLast! = q.getLast! := by
      by_contra hne
      have h1 : nextEl r (p.getLast!) = nextEl q (p.getLast!) :=
        nextElPartsUnlast L hrnd hrne hq hyq hne
      have h2 : nextEl q (p.getLast!) = fList L (eList (p.getLast!)) :=
        partsNextUnlast L hrnd hrne q hq (p.getLast!) hyq hne
      have hfEq : fList L (p.getLast!) = fList L (eList (p.getLast!)) :=
        hnextr.symm.trans (h1.trans h2)
      have hEq : p.getLast! = eList (p.getLast!) :=
        (fListInjDarts L hL hyD (goodListEList hL hyD)).mp hfEq
      exact (isRestrictedEListNondeg hL hm.1.1 hyD) hEq.symm
    have hyNotS : p.getLast! ∉ sListSpine L r x := by
      intro hmem
      have hyFST : p.getLast! ∈ (splitNormalListSpine L r (findFaceDarts L x)
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
        rw [hFSTeq]
        exact List.mem_append.mpr (Or.inr hyf1)
      exact (aqs_sListNotInFst L hL hgn hm hf (findFaceDarts L x) rfl rfl rfl rfl
        hmem) hyFST
    have hSF := (hm.2.2 hf).2 r q (p.getLast!) hyLastq hq hm.1.2.2.1 hf hyNotS
    rcases List.mem_append.mp hSF with hsl | hfin
    · have hSnd : eList (p.getLast!) ∈ S := by
        rw [hSdef]
        exact aqs_sListInRtrans L hL hgn hm hf (findFaceDarts L x) rfl rfl rfl rfl hsl
      exact List.mem_flatten.mpr
        ⟨S, List.mem_filter.mpr ⟨hmemS, by simpa using hfinS⟩, hSnd⟩
    · obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp hfin
      obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
      have hlfinal : finalListSpine L l := decide_eq_true_iff.mp hlfin
      have hlr : l ≠ r := fun h => hf (h ▸ hlfinal)
      have hn' : ntransSpine L N r x 1
          = replaceSpine r [S] N
            ++ [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
              (prevEl r (lZSpine L N r x))).1] := by
        rw [ntrans1 L N r x hf, hsplitS, hsplitF]
      refine List.mem_flatten.mpr ⟨l, List.mem_filter.mpr ⟨?_, by simpa using hlfinal⟩, hel⟩
      rw [hn']
      exact List.mem_append.mpr (Or.inl (memReplaceOfNeMem hlr hlN))

/-! ## §2 F 支组合器（62 二分：窗口块半 + f1 半） -/

/-- **HOL AQ12.hl:3780-:4084（F 支完整形）**：
`p ∈ parts F` ⇒ `eList (LAST p) ∈ FinalDartList (ntrans 1)`。 -/
theorem aq12ab_flagConjunctTwoF (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hfinRtrans : finalListSpine L (rtransSpine L N r x 1))
    {p : List (ℕ × ℕ)}
    (hp : p ∈ partsSpine L ((splitNormalListSpine L r (findFaceDarts L x)
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1)) :
    eList (p.getLast!) ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  have h62 := aq12w_catFstSplitNormalParts L hL hgn hm hf
  rw [h62] at hp
  rcases List.mem_append.mp hp with hb | hf1
  · exact aq12aa_flagConjunctTwoFBlock L hL hgn hm hf hfinRtrans hb
  · exact aq12ab_flagConjunctTwoFF1 L hL hgn hm hf hfinRtrans hf1

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12ab_flagConjunctTwoFF1
#print axioms Kepler.Text.TameSpine.aq12ab_flagConjunctTwoF
