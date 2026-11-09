/- JcajyduAqLeaf13W4a2b — AQ13 W4a2b：S 链 + F f1（y≠z1）。0 禁词；主仓零改动。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a1
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2
import Kepler.Text.TameSpine.JcajyduAqLeaf13W1b

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup
  nextEl_mem_of_mem prevEl_mem_of_mem)

private theorem aq13w4a2b_getLast!_append_singleton {α : Type*} [Inhabited α]
    (l : List α) (a : α) : (l ++ [a]).getLast! = a := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append]
  simp

/-- FinalDart N → FinalDart N'（W2 §3b 同款）。 -/
theorem aq13w4a2b_finalDartTransfer (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {e : ℕ × ℕ} (he : e ∈ FinalDartListSpine L N) :
    e ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp he
  obtain ⟨hlN, hlfin⟩ := List.mem_filter.mp hl
  have hlF : finalListSpine L l := decide_eq_true_iff.mp hlfin
  have hlr : l ≠ r := fun h => hf (h ▸ hlF)
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
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
  rw [hn]
  refine List.mem_flatten.mpr ⟨l, ?_, hel⟩
  rw [List.mem_filter]
  exact ⟨List.mem_append.mpr (Or.inl (memReplaceOfNeMem hlr hlN)), by simpa using hlF⟩

/-- **S 链段**：`p∈parts f2`、`y=LAST p`、`y≠l'y`、`y∉sList rtr` ⇒ 目标。 -/
theorem aq13w4a2b_sChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {p : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hp : p ∈ partsSpine L ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]))
    (hyp : y ∈ p) (hylast : y = p.getLast!) (hyne : y ≠ lYSpine L r x)
    (hyNot : y ∉ sListSpine L (rtransSpine L N r x 1) x) :
    eList y ∈ sListSpine L (rtransSpine L N r x 1) x ++
      FinalDartListSpine L (ntransSpine L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hnextz : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hfcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hndS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup :=
    uniqFlattenUniq _ hndNt _ (sndMemRtran1 L hm.1.2.2.1 hf)
  have hsplitSND : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 =
      ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ++
      between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
    dsimp only [splitNormalListSpine]
    rw [hnextz, hfcanon]
  have hndF2 : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]).Nodup := by
    have h := hndS
    rw [hsplitSND] at h
    exact (List.nodup_append.mp h).1
  have hgr : ∀ d ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]), d ∈ r := by
    intro d hd
    rcases List.mem_append.mp hd with hdz | hdBy
    · rcases List.mem_append.mp hdz with hdz' | hdB
      · exact (List.mem_singleton.mp hdz') ▸ hz
      · exact betwnMem hdB
    · exact (List.mem_singleton.mp hdBy) ▸ hy
  have hdF2 : y ∈ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) :=
    memPartsImp L hndF2 (by simp) hp y hyp
  have hf2last : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]).getLast! = lYSpine L r x :=
    aq13w4a2b_getLast!_append_singleton _ _
  have hgy : y ≠ ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]).getLast! := by
    rw [hf2last]; exact hyne
  have hnextg : nextEl ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) y = nextEl r y :=
    aq13w4a1_nextEl_f2 L hL hgn hm hf hdF2 hyne
  obtain ⟨p1, hp1, hlastp1⟩ := aq13w4a1_existsPartsLast L hL hm.1.2.1 hm.1.2.2.1
    hp hyp hylast hdF2 hgy hndF2 hgr hnextg
  have hyNotOld : y ∉ sListSpine L r x :=
    fun h => hyNot (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf h)
  have hSF := (hm.2.2 hf).2 r p1 y hlastp1.symm hp1 hm.1.2.2.1 hf hyNotOld
  rcases List.mem_append.mp hSF with hSl | hFin
  · exact List.mem_append.mpr (Or.inl (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf hSl))
  · exact List.mem_append.mpr (Or.inr (aq13w4a2b_finalDartTransfer L hL hgn hm hf hFin))

/-- **F f1（y≠z1 段）**：`p∈parts f1`、`y=LAST p`、`y≠z1`、`y∉sList rtr` ⇒ 目标。 -/
theorem aq13w4a2b_fChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {p : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hp : p ∈ partsSpine L ([nextEl r (lYSpine L r x)] ++
      between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ++
      [prevEl r (lZSpine L N r x)]))
    (hyp : y ∈ p) (hylast : y = p.getLast!)
    (hyb : y ≠ prevEl r (lZSpine L N r x))
    (hyNot : y ∉ sListSpine L (rtransSpine L N r x 1) x) :
    eList y ∈ sListSpine L (rtransSpine L N r x 1) x ++
      FinalDartListSpine L (ntransSpine L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  set a := nextEl r (lYSpine L r x) with hadef
  set b := prevEl r (lZSpine L N r x) with hbdef
  have ha : a ∈ r := nextEl_mem_of_mem hy
  have hb : b ∈ r := prevEl_mem_of_mem hz
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hsplit1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 =
      ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => ndSpine L d)).flatten).reverse) ++
        ([a] ++ between r a b ++ [b]) := by
    dsimp only [splitNormalListSpine]
    simp only [ndSpine]
    rw [hbdef, nextElPrevElUniq hrnd _, ← hadef, ← hbdef]
  have hf1nd : ([a] ++ between r a b ++ [b]).Nodup := by
    have h := uniqFlattenUniq _ hndNt _ (aq8w2b_fstMemRtran1 L hf)
    rw [hsplit1] at h
    exact (List.nodup_append.mp h).2.1
  have hgr : ∀ d ∈ ([a] ++ between r a b ++ [b]), d ∈ r := by
    intro d hd
    rcases List.mem_append.mp hd with hda | hdBy
    · rcases List.mem_append.mp hda with hda' | hdB
      · exact (List.mem_singleton.mp hda') ▸ ha
      · exact betwnMem hdB
    · exact (List.mem_singleton.mp hdBy) ▸ hb
  have hdf1 : y ∈ ([a] ++ between r a b ++ [b]) :=
    memPartsImp L hf1nd (by simp) hp y hyp
  have hf1last : ([a] ++ between r a b ++ [b]).getLast! = b :=
    aq13w4a2b_getLast!_append_singleton _ _
  have hgy : y ≠ ([a] ++ between r a b ++ [b]).getLast! := by
    rw [hf1last]; exact hyb
  have hnextg : nextEl ([a] ++ between r a b ++ [b]) y = nextEl r y :=
    aq13w4a2_nextEl_f1 L hL hgn hm hf (d := y) hdf1 hyb
  obtain ⟨p1, hp1, hlastp1⟩ := aq13w4a1_existsPartsLast L hL hm.1.2.1 hm.1.2.2.1
    hp hyp hylast hdf1 hgy hf1nd hgr hnextg
  have hyNotOld : y ∉ sListSpine L r x :=
    fun h => hyNot (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf h)
  have hSF := (hm.2.2 hf).2 r p1 y hlastp1.symm hp1 hm.1.2.2.1 hf hyNotOld
  rcases List.mem_append.mp hSF with hSl | hFin
  · exact List.mem_append.mpr (Or.inl (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf hSl))
  · exact List.mem_append.mpr (Or.inr (aq13w4a2b_finalDartTransfer L hL hgn hm hf hFin))

#print axioms Kepler.Text.TameSpine.aq13w4a2b_finalDartTransfer
#print axioms Kepler.Text.TameSpine.aq13w4a2b_sChain
#print axioms Kepler.Text.TameSpine.aq13w4a2b_fChain
