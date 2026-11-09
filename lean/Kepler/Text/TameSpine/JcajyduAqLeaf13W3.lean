/-
  JcajyduAqLeaf13W3 — AQ13 叶 W3：S 支 ④ + F 支 ⑮。
  · ④ `cat_snd_split_normal_parts`（AQ13.hl:180-255，76 行）：
    `parts (SND split) = parts f2 ++ map [·] W`，f2 = [z]++betwn r z y++[y]。
    路线：split SND 展开（f2++W）+ partsCat（切点 y，断口 y≠eList y 经
    F_LIST_INJ + 非退化）+ aqs_partsFBetwnPure（窗口 parts = map 单点）。
  · ⑮ `case_betwn_prev_el`（AQ13.hl:941-960，20 行）：纯列表 indexf 件。
  纪律：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1b
import Kepler.Text.TameSpine.JcajyduAqLeaf12G
import Kepler.Text.TameSpine.JcajyduAqLeaf1F
import Kepler.Text.TameSpine.TameList9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList eList GoodList listOfDarts findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup
  prevEl_mem_of_mem mem_darts_of_mem_findFace)

/-! ## §0 列表私件 -/

private theorem aq13w3_getLast!_append_singleton {α : Type*} [Inhabited α]
    (l : List α) (a : α) : (l ++ [a]).getLast! = a := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append]
  simp

/-! ## §1 HOL ④ `cat_snd_split_normal_parts` -/

/-- **HOL `cat_snd_split_normal_parts`**（AQ13.hl:180-255）：
`parts (SND split) = parts ([z]++betwn r z y++[y]) ++ map [·] (betwn f y z)`。 -/
theorem aq13w3_catSndSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    partsSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 =
      partsSpine L ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x]) ++
        (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).map
          (fun d => [d]) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hnextz : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hfcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 hyf
  -- split.2 = f2 ++ W
  have hsplit : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 =
      ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++
      between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
    dsimp only [splitNormalListSpine]
    rw [hnextz, hfcanon]
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hmemS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
    sndMemRtran1 L hm.1.2.2.1 hf
  have hndS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup :=
    uniqFlattenUniq _ hndNt _ hmemS
  by_cases hW : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) = []
  · -- 窗口空：SND = f2，两边 = parts f2
    rw [hsplit, hW, List.append_nil, List.map_nil, List.append_nil]
  · -- 窗口非空：partsCat + 窗口单点
    have hUlast : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]).getLast! = lYSpine L r x := by
      have h := aq13w3_getLast!_append_singleton
        ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
        (lYSpine L r x)
      simpa only [List.append_assoc] using h
    have hUne : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ≠ [] := by simp
    have hVne : between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x) ≠ [] := hW
    have hnextS : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++
        between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
        (lYSpine L r x) = nextEl (findFaceDarts L x) (lYSpine L r x) := by
      have hndSplit : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x]) ++
          between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
        rw [← hsplit]; exact hndS
      have h1 := nextElCatLast1 hndSplit hUne hVne
      rw [hUlast] at h1
      rw [h1, aqs_hdBetwn2 hfnd hyf hzf hyz hVne]
    have hne : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++
        between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
        (lYSpine L r x) ≠ fList L (eList (lYSpine L r x)) := by
      rw [hnextS]
      intro hcon
      have hfy : nextEl (findFaceDarts L x) (lYSpine L r x)
          = fList L (lYSpine L r x) := by
        simp only [fList, hfcanon]
      have hfe : fList L (lYSpine L r x) = fList L (eList (lYSpine L r x)) :=
        hfy.symm.trans hcon
      have hyd : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
      have hed : eList (lYSpine L r x) ∈ listOfDarts L := goodListEList hL hyd
      have heq : lYSpine L r x = eList (lYSpine L r x) :=
        (fListInjDarts L hL hyd hed).mp hfe
      exact absurd heq.symm (isRestrictedEListNondeg hL hm.1.1 hyd)
    have hcat := partsCat L (u := [lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x])
      (v := between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x))
      (x := lYSpine L r x) hsplit hUlast hUne hVne (by rw [hsplit]; exact hne) hndS
    rw [hcat, aqs_partsFBetwnPure L hL hgn hm hf]

/-! ## §2 HOL ⑮ `case_betwn_prev_el` -/

/-- **HOL `case_betwn_prev_el`**（AQ13.hl:941-960）：
`d ∈ betwn r y z ⇒ prevEl r d = y ∨ prevEl r d ∈ betwn r y z`。 -/
theorem aq13w3_caseBetwnPrevEl {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} {y z d : α} (hyz : y ≠ z) (hy : y ∈ r) (hz : z ∈ r)
    (hnd : r.Nodup) (hd : d ∈ between r y z) :
    prevEl r d = y ∨ prevEl r d ∈ between r y z := by
  have hdmem : d ∈ r := betwnMem hd
  have hemem : prevEl r d ∈ r := prevEl_mem_of_mem hdmem
  have hnext : nextEl r (prevEl r d) = d := nextElPrevElUniq hnd d
  have hbetw := (indexfBetwnEq hyz hnd hy hz).mp hd
  have hlen2 : 1 < r.length := sizelGt1 hy hz hyz
  have hied : indexf (prevEl r d) d r = 1 :=
    nextElIndexf hemem hdmem hnd hnext hlen2
  have hadd : indexf y (prevEl r d) r + indexf (prevEl r d) d r = indexf y d r :=
    indexfAddRight hy hemem hdmem (by rw [hied]; omega)
  have hidx : indexf y (prevEl r d) r = indexf y d r - 1 := by omega
  rcases Nat.eq_zero_or_pos (indexf y (prevEl r d) r) with h0 | hpos
  · left
    exact (indexfZeroEq hy hemem h0).symm
  · right
    exact (indexfBetwnEq hyz hnd hy hz).mpr ⟨hpos, by omega⟩

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.aq13w3_catSndSplitNormalParts
#print axioms Kepler.Text.TameSpine.aq13w3_caseBetwnPrevEl
