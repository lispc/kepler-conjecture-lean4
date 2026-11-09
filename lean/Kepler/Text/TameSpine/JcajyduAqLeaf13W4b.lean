/- JcajyduAqLeaf13W4b — AQ13 主装：theorem aq13（塔 13/13 末件）。0 禁词。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2c3
import Kepler.Text.TameSpine.JcajyduAqLeaf13W3
import Kepler.Text.TameSpine.JcajyduAqLeaf13W2
import Kepler.Text.TameSpine.JcajyduAqLeaf12W
import Kepler.Text.TameSpine.JcajyduAqLeaf8W1a
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup)

private theorem aq13w4b_getLast!_mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- **AQ13 主证**（TowerBase:313-319 逐字）：合取 (i)=12Y 别名；
合取 (ii) 按 `ntrans1 = replace r [S] N ++ [F]` 三支分派。 -/
theorem aq13 (L : fgraph ℕ) (hL : GoodList L) : aq13Concl L hL := by
  intro N r x hgn hm hnf
  refine ⟨aq13w2_flagConjunctOne L hL hgn hm, ?_⟩
  intro r' p y hylast hp hr' hnf' hyNot
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hf : ¬finalListSpine L r := by
    intro hfr
    exact hnf (by rw [rtransId L N r x hfr]; exact hfr)
  have hfindcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))) =
      (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))) := by rw [hfindcanon]
  have hn : ntransSpine L N r x 1 =
      replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).2] N ++
      [(splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1] := by
    rw [ntrans1 L N r x hf, hsplit_eq]
  have hNnd : N.Nodup := uniqFlatten hm.1.2.1.1 hm.1.2.1.2.1
  have hnN' : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL (aq1 L hL) (aq2 L hL) (aq3 L hL) (aq4 L hL) (aq5 L hL) hgn hm
  rw [hn] at hr'
  rcases List.mem_append.mp hr' with hrRep | hrF
  · -- r' ∈ replace r [S] N：N 支 / S 支
    rcases aq13w2_memReplaceCasesNodup hNnd hrRep with ⟨hN, hNne⟩ | ⟨_, hS'⟩
    · exact aq13w2_flagConjunctTwoN L hL hgn hm hf hnf r' p y hN hNne hylast hp hnf' hyNot
    · -- S 支
      have hr'eq : r' = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x))).2 := List.mem_singleton.mp hS'
      subst hr'eq
      rw [← hsplit_eq] at hp
      have hmemS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
        sndMemRtran1 L hm.1.2.2.1 hf
      have hpne : p ≠ [] :=
        (partsUniqNonnil L hL hnN' hmemS hp).2.2.2.1
      have hyp : y ∈ p := by rw [hylast]; exact aq13w4b_getLast!_mem hpne
      rw [aq13w3_catSndSplitNormalParts L hL hgn hm hf] at hp
      rcases List.mem_append.mp hp with hpF2 | hpW
      · by_cases hyLy : y = lYSpine L r x
        · exact absurd (by rw [hyLy]; exact aq13w1_yMemSListRtrans L hL hgn hm hf hnf) hyNot
        · exact aq13w4a2b_sChain L hL hgn hm hf hnf hpF2 hyp hylast hyLy hyNot
      · rcases List.mem_map.mp hpW with ⟨d, hdW, hpd⟩
        rw [← hpd] at hylast
        exact (aq13w4a1_windowContra L hL hgn hm hf hnf hdW hylast hyNot).elim
  · -- F 支
    have hr'eq : r' = (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 := List.mem_singleton.mp hrF
    subst hr'eq
    have hmemF : (splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
        (prevEl r (lZSpine L N r x))).1 ∈ ntransSpine L N r x 1 := by
      rw [hn]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hpne : p ≠ [] :=
      (partsUniqNonnil L hL hnN' hmemF hp).2.2.2.1
    have hyp : y ∈ p := by rw [hylast]; exact aq13w4b_getLast!_mem hpne
    rw [aq12w_catFstSplitNormalParts L hL hgn hm hf] at hp
    rcases List.mem_append.mp hp with hpNode | hpF1
    · rw [List.mem_reverse] at hpNode
      rcases List.mem_map.mp hpNode with ⟨d, hdW, hpd⟩
      rw [← hpd] at hylast
      refine List.mem_append.mpr (Or.inl ?_)
      rw [hylast]
      exact aq13w4a1_nodeBlockMemSList L hL hgn hm hf hnf hdW
    · by_cases hyb : y = prevEl r (lZSpine L N r x)
      · exact aq13w4a2c3_fChainLast L hL hgn hm hf hnf hpF1 hyp hylast hyb hyNot
      · exact aq13w4a2b_fChain L hL hgn hm hf hnf hpF1 hyp hylast hyb hyNot

#print axioms Kepler.Text.TameSpine.aq13
