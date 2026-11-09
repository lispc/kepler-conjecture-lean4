/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12Q — AQ12 叶 W8a-ii（decl 51 装配）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:2342-:2487（146 行）
  `exists_contour_not_snd_fst`：
  `u ∈ r1`（r1 = FST split、final）、`v ∈ r2`（r2 ∈ N、final）⇒ 存在 contour u → v，
  支撑 ⊆ flatten(filter final (replace r [SND split] N ++ [FST split]))。

  ┌─ 依赖与条件槽（编排者 2026-11-10 批准）──────────────────────────
  │ `h4 : aq4Concl L hL` **显式槽**（W5b/W6b 同款；DIFFERS：W5b/W6b/W8a-ii 吃，
  │ W7/W8a-i 不吃）。FST 行 loopListSpine = `aq8w2b_fstMemRtran1` + h4 第 4 槽。
  │ W8a-i 前置 `aq12p_lastPartsMemFstSplit`（lp ∈ r1）已落库（12P）。
  │ 装配：r1 contour(u → lp) + SFlag contour(fList(eList lp) → v) +
  │ `contourListCat`；junction = W7 的 `aqs_oneStepEListLastY`。
  │ 支撑：r1 ⊆ target（final r1 + 右段 [FST split]）；
  │ FinalDartList N ⊆ target（final 行 l ≠ r，`memReplaceOfNeMem`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 陈述对表（HOL → Lean）─────────────────────────────────────────
  │ good_list L                          → (hL : GoodList L)
  │ good_list_nodes L                    → (hgn : GoodListNodesTl L hL)
  │ marked_list L N r x                  → (hm : MarkedListSpineFull hL N r x)
  │ ~final_list L r                      → (hf : ¬finalListSpine L r)
  │ l'z = z / l'y = y / prev_el r z = z1 → hz / hy / hz1
  │ final_list r1 / r2                   → hfin1 / hfin2
  │ MEM r2 N                             → hr2N
  │ FST split = r1                       → hr1
  │ find_face L x = f                    → hfind
  │ MEM v r2 / MEM u r1                  → hv / hu
  │ ?s. contour_list ∧ ~[] ∧ HD=u ∧ LAST=v ∧ support ⊆ target
  │                                      → ∃ s, ContourListSpine L s ∧ s ≠ [] ∧
  │                                        s.head! = u ∧ s.getLast! = v ∧
  │                                        setOfListSpine s ⊆ setOfListSpine target
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12P
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList nextEl_mem_of_mem dart_in_face
  prevEl_nextEl findFaceDarts_congr_of_mem findFaceDarts_nodup)

/-- **HOL `exists_contour_not_snd_fst`**（AQ12.hl:2342-:2487）：
`u ∈ FST split 行 r1`、`v ∈ N 的 final 行 r2` ⇒ contour u → v（支撑见目标）。 -/
theorem aqs_existsContourNotSndFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (h4 : aq4Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} {r1 r2 : List (ℕ × ℕ)} {u v : ℕ × ℕ}
    (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y) (hz1 : prevEl r z = z1)
    (hfin1 : finalListSpine L r1) (hfin2 : finalListSpine L r2)
    (hr2N : r2 ∈ N)
    (hr1 : (splitNormalListSpine L r f y z1).1 = r1)
    (hfind : findFaceDarts L x = f)
    (hv : v ∈ r2) (hu : u ∈ r1) :
    ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
      s.getLast! = v ∧ setOfListSpine s ⊆
        setOfListSpine ((replaceSpine r [(splitNormalListSpine L r f y z1).2] N
          ++ [(splitNormalListSpine L r f y z1).1]).filter
            (fun l => decide (finalListSpine L l))).flatten := by
  -- §0 公共事实
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  -- §1 取含 y 的 part，lp = LAST p，lp ∈ r1（W8a-i）
  obtain ⟨p, hp, hyp⟩ := partsMemExists L hrnd hyr
  have hlpR1 : p.getLast! ∈ r1 :=
    aq12p_lastPartsMemFstSplit L hL hgn hm hf hp hyp rfl f hz hy hz1 hr1 hfind
  -- §2 r1 的 Nodup + loopListSpine（h4 投影）
  have hmem1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 :=
    aq8w2b_fstMemRtran1 L hf
  have hNflat : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hnd1c : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1.Nodup :=
    uniqFlattenUniq _ hNflat _ hmem1
  have hnd1 : r1.Nodup := by rw [← hr1, ← hsplit_eq]; exact hnd1c
  have hloop1c : loopListSpine L (splitNormalListSpine L r
      (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (prevEl r (lZSpine L N r x))).1 :=
    h4 N r x hgn hm _ hmem1
  have hloop1 : loopListSpine L r1 := by rw [← hr1, ← hsplit_eq]; exact hloop1c
  -- §3 r1 contour：u → lp
  obtain ⟨s1, hc1, hhd1, hlast1, hsub1, hne1⟩ :=
    aqs_existsConnectedLoop (L := L) (s := r1) (x := u) (y := p.getLast!)
      hnd1 hloop1 hu hlpR1
  -- §4 SFlag contour：fList(eList lp) → v
  -- e_list_last 路线：eList lp ∈ N.flatten（HOL MEEIXJO.e_list_last 的 Lean 内联）
  have hpne : p ≠ [] := List.ne_nil_of_mem hyp
  have hlpMem : p.getLast! ∈ p := by
    rw [getLast!EqGetLast hpne]
    exact List.getLast_mem hpne
  have hlpR : p.getLast! ∈ r :=
    memPartsImp L hrnd (List.ne_nil_of_mem hm.1.2.2.2.1) hp _ hlpMem
  have hlpD : p.getLast! ∈ listOfDarts L :=
    partsDarts L hm.1.2.1 hm.1.2.2.1 hp hlpMem
  have hfdLp : p.getLast! ∈ findFaceDarts L (p.getLast!) := (dart_in_face L _).mpr hlpD
  have hflR : fList L (p.getLast!) ∈ r := by
    rw [← normalListPartsNextLast L hL hm.1.2.1 hm.1.2.2.1 hp]
    exact nextEl_mem_of_mem hlpR
  have hflFlat : fList L (p.getLast!) ∈ N.flatten :=
    List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hflR⟩
  have hflD : fList L (p.getLast!) ∈ listOfDarts L :=
    memFListPower L hL hlpD 1
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
  have hfF : fList L (eList (p.getLast!)) ∈ FinalDartListSpine L N := by
    have hin : eList (p.getLast!) ∈ findListSpine N (eList (p.getLast!)) := memFindList1 hfl
    have hrowN : findListSpine N (eList (p.getLast!)) ∈ N := findListSpineMemN hfl
    have hrowfin : finalListSpine L (findListSpine N (eList (p.getLast!))) :=
      aqs_existFinalListEList (x := x) L hL hgn hm hf hp hyp rfl
    have hflmem : fList L (eList (p.getLast!)) ∈ findListSpine N (eList (p.getLast!)) := by
      rw [hrowfin (eList (p.getLast!)) hin]
      exact nextEl_mem_of_mem hin
    exact List.mem_flatten.mpr
      ⟨_, List.mem_filter.mpr ⟨hrowN, by simpa using hrowfin⟩, hflmem⟩
  have hvF : v ∈ FinalDartListSpine L N :=
    List.mem_flatten.mpr
      ⟨r2, List.mem_filter.mpr ⟨hr2N, by simpa using hfin2⟩, hv⟩
  have hsf : SFlagListSpine L N r x := hm.2.2 hf
  obtain ⟨s, hcs, hne, hhd, hlast, hsF⟩ :=
    hsf.1 (fList L (eList (p.getLast!))) hfF v hvF
  -- §5 拼接：junction lp → fList(eList lp)
  have hone := aqs_oneStepEListLastY L hL hgn hm hf hp hyp rfl
  have hcat : ContourListSpine L (s1 ++ s) := by
    refine (aqs_contourListCat hne1 hne).mpr ⟨hc1, hcs, ?_⟩
    rw [hlast1, hhd]
    exact hone
  -- §6 支撑
  have hr1Subset : ∀ d ∈ r1, d ∈ ((replaceSpine r
      [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
    intro d hd
    have hmem1' : r1 ∈ [(splitNormalListSpine L r f y z1).1] := by
      rw [hr1]
      exact List.mem_singleton_self _
    exact List.mem_flatten.mpr
      ⟨r1, List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inr hmem1'), by simpa using hfin1⟩, hd⟩
  have hfinalSubset : ∀ d ∈ FinalDartListSpine L N, d ∈ ((replaceSpine r
      [(splitNormalListSpine L r f y z1).2] N
      ++ [(splitNormalListSpine L r f y z1).1]).filter
        (fun l => decide (finalListSpine L l))).flatten := by
    intro d hd
    obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
    obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
    have hlfin' : finalListSpine L l := decide_eq_true_iff.mp hlfin
    have hlr : l ≠ r := fun h => hf (h ▸ hlfin')
    have hmem : l ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N :=
      memReplaceOfNeMem hlr hlN
    exact List.mem_flatten.mpr
      ⟨l, List.mem_filter.mpr
        ⟨List.mem_append.mpr (Or.inl hmem), by simpa using hlfin'⟩, hdl⟩
  -- §7 收口
  refine ⟨s1 ++ s, hcat, ?_, ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_append_left _ (aqs_headMem hne1))
  · rw [List.head!_append _ hne1, hhd1]
  · rw [aqs_getLastAppend, if_neg hne, hlast]
  · intro d hd
    rcases List.mem_append.mp hd with hd1 | hdS
    · exact hr1Subset d (hsub1 hd1)
    · exact hfinalSubset d (hsF d hdS)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_existsContourNotSndFst
