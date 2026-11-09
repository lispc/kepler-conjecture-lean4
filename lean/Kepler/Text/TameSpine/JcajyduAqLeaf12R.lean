/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12R — AQ12 叶 W8b（decls 52–53）。

  HOL：AQ12.hl:2488-:2692（205 行）：decl 52 `one_step_last_y_e_list`（31）、
  decl 53 `exists_contour_fst_not_snd`（174）。

  件目/依赖（开工报价）：2 件 / 1 文件；估 220–280（≤320）。
  · decl 52：第二析取 `nextEl r lp = fList lp`（`normalListPartsNextLast`）。
  · decl 53：角色与 decl 51 对调（`MEM r1 N`、`FST split = r2`）；需要
    `nextEl r lp ∈ FST split`：lp ∈ betwn y z →（lp ≠ prevEl z）nextEl lp ∈ betwn
    → `aq12p_betwnSubF1`；lp = prevEl z 由 FST 链 + `aqs_fstYNeFstZ` 排除。
  · **`h4 : aq4Concl` 槽：吃**（FST 行 loopListSpine；`aq8w2b_fstMemRtran1`
    + 第 4 槽）。DIFFERS：W5b/W6b/W8a-ii/W8b 吃，W7/W8a-i 不吃。
  · 不依赖 decl 51；只复用 W8a-i 的 `aq12p_betwnSubF1` / `aq12p_lastPartsMemFstSplit`。
  · 陈述对表：HOL 前提逐项对应（见定理签名）；唯一附加 = `h4` 条件槽。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf12Q
import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2a
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_mem_of_mem prevEl_mem_of_mem
  dart_in_face prevEl_nextEl findFaceDarts_congr_of_mem findFaceDarts_nodup)

/-! ## §1 HOL AQ12.hl:2488 `one_step_last_y_e_list` -/
/-- **HOL `one_step_last_y_e_list`**（AQ12.hl:2488-:2518）：
`one_step_list L (eList lp) (next_el r lp)`——第二析取
`nextEl r lp = fList lp`（`normalListPartsNextLast`）。 -/
theorem aqs_oneStepLastYEList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    oneStepListSpine L (eList lp) (nextEl r lp) := by
  refine Or.inr ?_
  rw [eList_eList, ← hlast]
  exact normalListPartsNextLast L hL hm.1.2.1 hm.1.2.2.1 hp

/-! ## §2 私件：lp ∈ between r y z（W8a-i 同款四支排除） -/
private theorem aq12r_lpMemBetwn (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp) :
    lp ∈ between r (lYSpine L r x) (lZSpine L N r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : lp ∈ p := by
    rw [← hlast, getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpR : lp ∈ r :=
    memPartsImp L hrnd (List.ne_nil_of_mem hm.1.2.2.2.1) hp lp hlpMem
  rcases betwnCases hyz hrnd hyr hlpR hzr with heq | heq | hb | hb
  · exact absurd (hlast.trans heq)
      (aq8w1_lastPartsYNotY L hL hgn hm hf hp hyp)
  · exact absurd (hlast.trans heq)
      (aq8w1_lastPartsYNotZ L hL hgn hm hf hp hyp)
  · exact hb
  · exact absurd (by
        rw [hlast]
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hb))))
      (aqs_lastPartsYNotCat L hL hgn hm hf hp hyp)

/-! ## §3 私件：`nextEl r lp ∈ FST split` -/
private theorem aq12r_nextElLpMemFstSplit (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p : List (ℕ × ℕ)} (hp : p ∈ partsSpine L r)
    (hyp : lYSpine L r x ∈ p) {lp : ℕ × ℕ} (hlast : p.getLast! = lp)
    (f : List (ℕ × ℕ)) {z y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hr2 : (splitNormalListSpine L r f y z1).1 = r2)
    (hfind : findFaceDarts L x = f) :
    nextEl r lp ∈ r2 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hy1z : nextEl r (lYSpine L r x) ≠ lZSpine L N r x :=
    aq1_nextElYNeZ L hL hgn hunL hm hf
  have hra : nextEl r (lYSpine L r x) ≠ prevEl r (lZSpine L N r x) :=
    aq1_nextElYNePrevElZ L hL hgn hunL hm hf
  have hb := aq12r_lpMemBetwn L hL hgn hm hf hp hyp hlast
  have hBne : between r (lYSpine L r x) (lZSpine L N r x) ≠ [] :=
    List.ne_nil_of_mem hb
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : lp ∈ p := by
    rw [← hlast, getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  by_cases hlpz : lp = prevEl r (lZSpine L N r x)
  · -- 排除 lp = prevEl z：FST 链撞 aqs_fstYNeFstZ
    have hfstLp : lp.1 = p.head!.1 :=
      partsFst L hL hm.1.2.1 hm.1.2.2.1 hp hlpMem
    have hfstY : (lYSpine L r x).1 = p.head!.1 :=
      partsFst L hL hm.1.2.1 hm.1.2.2.1 hp hyp
    have hfstZ1 : (prevEl r (lZSpine L N r x)).1 = (lZSpine L N r x).1 :=
      fstEqPrevZtransV0 L hL hgn hm hf
    exact absurd (by
      calc (lYSpine L r x).1 = p.head!.1 := hfstY
        _ = lp.1 := hfstLp.symm
        _ = (prevEl r (lZSpine L N r x)).1 := by rw [hlpz]
        _ = (lZSpine L N r x).1 := hfstZ1)
      (aqs_fstYNeFstZ L hL hgn hunL hm hf)
  · -- lp ≠ last：nextEl lp ∈ betwn → f1 → FST split
    have hgl : (between r (lYSpine L r x) (lZSpine L N r x)).getLast hBne
        = prevEl r (lZSpine L N r x) := by
      rw [← getLast!EqGetLast hBne]
      exact aqs_lastBetwnEqPrev hrnd hyr hzr hyz hBne
    have hneLast : (between r (lYSpine L r x) (lZSpine L N r x)).getLast hBne
        ≠ lp := fun h => hlpz (h.symm.trans hgl)
    have hnextB : nextEl r lp ∈ between r (lYSpine L r x) (lZSpine L N r x) :=
      (aq10_eqMemNextElLast hyz hyr hzr hb hrnd).mpr hneLast
    have hf1 : nextEl r lp ∈ ([nextEl r (lYSpine L r x)]
        ++ between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)))
        ++ [prevEl r (lZSpine L N r x)] :=
      aq12p_betwnSubF1 hrnd hyr hzr hyz hz1r hnextz1 hy1z hra (nextEl r lp) hnextB
    have hf1r : nextEl r lp ∈ [nextEl r (lYSpine L r x)]
        ++ between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
        ++ [prevEl r (lZSpine L N r x)] := by
      simpa only [List.append_assoc] using hf1
    have hmemCanon : nextEl r lp ∈ (splitNormalListSpine L r
        (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 := by
      rw [split1Unfold L r (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (prevEl r (lZSpine L N r x)), hnextz1]
      exact List.mem_append.mpr (Or.inr hf1r)
    have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
    have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
      (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
    have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x)))
        = splitNormalListSpine L r f y z1 := by
      rw [← hfindcanon, ← hy, ← hz1c]
    have hmemF : nextEl r lp ∈ (splitNormalListSpine L r f y z1).1 := by
      rw [← hsplit_eq]
      exact hmemCanon
    rwa [hr2] at hmemF

/-! ## §4 私件：r2（= FST split）的 Nodup + loopListSpine -/
private theorem aq12r_fstRowFacts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ)) {y z1 : ℕ × ℕ} {r2 : List (ℕ × ℕ)}
    (hy : lYSpine L r x = y) (hz1c : prevEl r (lZSpine L N r x) = z1)
    (hr2 : (splitNormalListSpine L r f y z1).1 = r2)
    (hfindcanon : findFaceDarts L (lYSpine L r x) = f) :
    r2.Nodup ∧ loopListSpine L r2 := by
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  have hmem : (splitNormalListSpine L r f y z1).1 ∈ ntransSpine L N r x 1 := by
    rw [← hsplit_eq]
    exact aq8w2b_fstMemRtran1 L hf
  have hNflat : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hnd : (splitNormalListSpine L r f y z1).1.Nodup :=
    uniqFlattenUniq _ hNflat _ hmem
  have hl : loopListSpine L (splitNormalListSpine L r f y z1).1 :=
    h4 N r x hgn hm _ hmem
  exact ⟨hr2 ▸ hnd, hr2 ▸ hl⟩

/-! ## §5 HOL AQ12.hl:2519 `exists_contour_fst_not_snd` -/
/-- **HOL `exists_contour_fst_not_snd`**（AQ12.hl:2519-:2692）：
`u ∈ r1`（r1 ∈ N、final）、`v ∈ r2`（r2 = FST split、final）⇒ contour u → v。 -/
theorem aqs_existsContourFstNotSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr1N : r1 ∈ N)
    (hr2 : (splitNormalListSpine L r f y z1).1 = r2)
    (hfind : findFaceDarts L x = f)
    (hv : v ∈ r2) (hu : u ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [(splitNormalListSpine L r f y z1).2] N
          ++ [(splitNormalListSpine L r f y z1).1]).filter
            (fun l => decide (finalListSpine L l))).flatten := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  -- p 与 lp
  obtain ⟨p, hp, hyp⟩ := partsMemExists L hrnd hyr
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : p.getLast! ∈ p := by
    rw [getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpD : p.getLast! ∈ listOfDarts L :=
    partsDarts L hm.1.2.1 hm.1.2.2.1 hp hlpMem
  -- nextEl lp ∈ r2
  have hnext2 : nextEl r (p.getLast!) ∈ r2 :=
    aq12r_nextElLpMemFstSplit L hL hgn hm hf hp hyp rfl f hz hy hz1 hr2 hfind
  -- r2 行事实
  obtain ⟨hnd2, hloop2⟩ :=
    aq12r_fstRowFacts L hL hgn h4 hm hf f hy hz1c hr2 hfindcanon
  -- r2 contour：nextEl lp → v
  obtain ⟨s2, hc2, hhd2, hlast2, hsub2, hne2⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r2) (x := nextEl r (p.getLast!)) (y := v)
      hnd2 hloop2 hnext2 hv
  -- SFlag contour：u → eList lp
  have huF : u ∈ FinalDartListSpine L N :=
    List.mem_flatten.mpr
      ⟨r1, List.mem_filter.mpr ⟨hr1N, by simpa using hfin1⟩, hu⟩
  -- e_list_last 内联：eList lp ∈ N.flatten
  have hfdLp : p.getLast! ∈ findFaceDarts L (p.getLast!) := (dart_in_face L _).mpr hlpD
  have hflR : fList L (p.getLast!) ∈ r := by
    rw [← normalListPartsNextLast L hL hm.1.2.1 hm.1.2.2.1 hp]
    exact nextEl_mem_of_mem (memPartsImp L hrnd
      (List.ne_nil_of_mem hm.1.2.2.2.1) hp _ hlpMem)
  have hflFlat : fList L (p.getLast!) ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hflR⟩
  have hflD : fList L (p.getLast!) ∈ listOfDarts L := memFListPower L hL hlpD 1
  have hflfdLp : fList L (p.getLast!) ∈ findFaceDarts L (p.getLast!) := by
    rw [fList]
    exact nextEl_mem_of_mem hfdLp
  have hcongr : findFaceDarts L (fList L (p.getLast!)) = findFaceDarts L (p.getLast!) :=
    findFaceDarts_congr_of_mem hL.1 hlpD hflfdLp
  have hprev : prevEl (findFaceDarts L (fList L (p.getLast!))) (fList L (p.getLast!))
      = p.getLast! := by
    rw [hcongr]
    exact prevEl_nextEl (findFaceDarts_nodup hL.1 _) hfdLp
  have hnlist : nList L (fList L (p.getLast!)) = eList (p.getLast!) := by
    rw [nList, hprev]
  have hnode : nList L (fList L (p.getLast!))
      ∈ (hypermapOfList L hL).node (fList L (p.getLast!)) := by
    have hp1 : nList L (fList L (p.getLast!))
        = ((hypermapOfList L hL).nodeMap ^ 1) (fList L (p.getLast!)) := by
      rw [← Function.iterate_one (nList L), nListPowEqNodeMapPow L hL hflD 1]
    rw [hp1]
    exact (hypermapOfList L hL).pow_nodeMap_mem_node _ 1
  have hfl : eList (p.getLast!) ∈ N.flatten := by
    have hsub := hm.1.2.1.2.2.2.2 (fList L (p.getLast!)) hflFlat
    exact hnlist ▸ hsub hnode
  -- eList lp ∈ FinalDartList
  have hrowfin : finalListSpine L (findListSpine N (eList (p.getLast!))) :=
    aqs_existFinalListEList (x := x) L hL hgn hm hf hp hyp rfl
  have hin : eList (p.getLast!) ∈ findListSpine N (eList (p.getLast!)) := memFindList1 hfl
  have hrowN : findListSpine N (eList (p.getLast!)) ∈ N := findListSpineMemN hfl
  have heF : eList (p.getLast!) ∈ FinalDartListSpine L N :=
    List.mem_flatten.mpr
      ⟨_, List.mem_filter.mpr ⟨hrowN, by simpa using hrowfin⟩, hin⟩
  have hsf : SFlagListSpine L N r x := hm.2.2 hf
  obtain ⟨s, hcs, hne, hhd, hlast, hsF⟩ := hsf.1 u huF (eList (p.getLast!)) heF
  -- 拼接：junction eList lp → nextEl lp
  have hone := aqs_oneStepLastYEList L hL hgn hm hf hp hyp rfl
  have hcat : ContourListSpine L (s ++ s2) := by
    refine (aqs_contourListCat hne hne2).mpr ⟨hcs, hc2, ?_⟩
    rw [hlast, hhd2]
    exact hone
  -- 支撑
  have hr2Subset : ∀ d ∈ r2, d ∈ ((replaceSpine r
      [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
    intro d hd
    have hmem1' : r2 ∈ [(splitNormalListSpine L r f y z1).1] := by
      rw [← hr2]
      exact List.mem_singleton_self _
    exact List.mem_flatten.mpr
      ⟨r2, List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inr hmem1'), by simpa using hfin2⟩, hd⟩
  have hfinalSubset : ∀ d ∈ FinalDartListSpine L N, d ∈ ((replaceSpine r
      [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
    intro d hd
    obtain ⟨l', hl', hdl⟩ := List.mem_flatten.mp hd
    obtain ⟨hl'N, hl'fin⟩ := List.mem_filter.mp hl'
    have hl'fin' : finalListSpine L l' := decide_eq_true_iff.mp hl'fin
    have hl'r : l' ≠ r := fun h => hf (h ▸ hl'fin')
    have hmem : l' ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N :=
      memReplaceOfNeMem hl'r hl'N
    exact List.mem_flatten.mpr
      ⟨l', List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inl hmem), by simpa using hl'fin'⟩, hdl⟩
  refine ⟨s ++ s2, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne))
  · rw [List.head!_append _ hne, hhd]
  · rw [aqs_getLastAppend, if_neg hne2, hlast2]
  · intro d hd
    rcases List.mem_append.mp hd with hdS | hd2
    · exact hfinalSubset d (hsF d hdS)
    · exact hr2Subset d (hsub2 hd2)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_oneStepLastYEList
#print axioms Kepler.Text.TameSpine.aqs_existsContourFstNotSnd
