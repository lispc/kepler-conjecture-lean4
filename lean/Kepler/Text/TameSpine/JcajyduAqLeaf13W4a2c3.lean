/- JcajyduAqLeaf13W4a2c3 — AQ13 lp=z1 支直证（eList y 为 f 上 z 的前驱）。0 禁词。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2c
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2b
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b
import Kepler.Text.TameSpine.TameList3
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup dart_in_face
  nextEl_mem_of_mem prevEl_mem_of_mem)
/-- y=z1 支直证：p∈parts f1、y=LAST p=z1、y∉sList rtr ⇒ 目标。 -/
theorem aq13w4a2c3_fChainLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {p : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hp : p ∈ partsSpine L ([nextEl r (lYSpine L r x)] ++
      between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ++
      [prevEl r (lZSpine L N r x)]))
    (hyp : y ∈ p) (hylast : y = p.getLast!)
    (hyb : y = prevEl r (lZSpine L N r x))
    (hyNot : y ∉ sListSpine L (rtransSpine L N r x 1) x) :
    eList y ∈ sListSpine L (rtransSpine L N r x 1) x ++
      FinalDartListSpine L (ntransSpine L N r x 1) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf

  have hnextz : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hynext : nextEl r y = lZSpine L N r x := by rw [hyb]; exact hnextz
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  obtain ⟨hyf, hzf, -⟩ := hpp
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  -- f1 Nodup + 子集
  set a := nextEl r (lYSpine L r x) with hadef
  set b := prevEl r (lZSpine L N r x) with hbdef
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
      · exact (List.mem_singleton.mp hda') ▸ nextEl_mem_of_mem hy
      · exact betwnMem hdB
    · exact (List.mem_singleton.mp hdBy) ▸ prevEl_mem_of_mem hz
  have hdf1 : y ∈ ([a] ++ between r a b ++ [b]) :=
    memPartsImp L hf1nd (by simp) hp y hyp
  have hyr : y ∈ r := hgr y hdf1
  have hyd : y ∈ listOfDarts L := normalListListOfDarts hm.1.2.1 y (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hyr⟩)
  have hed : eList y ∈ listOfDarts L := goodListEList hL hyd

  rcases partsMemExists L hrnd hyr with ⟨p1, hp1, hyp1⟩
  by_cases hlast : y = p1.getLast!
  · -- p1 末元 = y：旧 SFlag
    have hyNotOld : y ∉ sListSpine L r x :=
      fun h => hyNot (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf h)
    have hSF := (hm.2.2 hf).2 r p1 y hlast hp1 hm.1.2.2.1 hf hyNotOld
    rcases List.mem_append.mp hSF with hSl | hFin
    · exact List.mem_append.mpr (Or.inl (aq13w1_sListSubsetRtrans L hL hgn hm hf hnf hSl))
    · exact List.mem_append.mpr (Or.inr (aq13w4a2b_finalDartTransfer L hL hgn hm hf hFin))
  · by_cases hyrlast : y = r.getLast!
    · exact absurd (aq13w4a2c_lastOfPartOfLast L hL hm.1.2.1 hm.1.2.2.1 hp1 hyp1 hyrlast)
        (fun h => hlast h.symm)
    · -- r 在 y 处无断口 ⇒ z = fList (eList y)
      have heqNext : nextEl r y = fList L (eList y) := by
        by_contra hb
        exact hlast ((aqs_conditionLastParts L hrnd hrne hp1 hyp1 hyrlast).mp hb)
      have hfListE : fList L (eList y) = lZSpine L N r x := heqNext.symm.trans hynext
      have hmemFaceE : eList y ∈ findFaceDarts L (eList y) :=
        (dart_in_face L (eList y)).mpr hed
      have hzFaceE : lZSpine L N r x ∈ findFaceDarts L (eList y) := by
        rw [← hfListE]
        exact nextEl_mem_of_mem hmemFaceE
      have hzf' : findFaceDarts L (lZSpine L N r x) = findFaceDarts L x :=
        aq10_memFindFaceImpFacesEq hL.1 hzf
      have hfaceE : findFaceDarts L (eList y) = findFaceDarts L x :=
        (aq10_memFindFaceImpFacesEq hL.1 hzFaceE).symm.trans hzf'
      have hnextE : nextEl (findFaceDarts L x) (eList y) = lZSpine L N r x := by
        have h1 : nextEl (findFaceDarts L (eList y)) (eList y) = lZSpine L N r x := by
          rw [← hfListE]; rfl
        rwa [hfaceE] at h1
      have hef : eList y ∈ findFaceDarts L x := by rw [← hfaceE]; exact hmemFaceE
      have hlen2 : 1 < (findFaceDarts L x).length := sizelGt1 hyf hzf hyz
      have hidxEz : indexf (eList y) (lZSpine L N r x) (findFaceDarts L x) = 1 :=
        nextElIndexf hef hzf hfnd hnextE hlen2
      have hposYZ : 0 < indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) := by
        rcases Nat.eq_zero_or_pos (indexf (lYSpine L r x) (lZSpine L N r x)
          (findFaceDarts L x)) with h0 | hpos
        · exact absurd (indexfZeroEq hyf hzf h0) hyz
        · exact hpos
      have hadd : indexf (lYSpine L r x) (eList y) (findFaceDarts L x)
          + indexf (eList y) (lZSpine L N r x) (findFaceDarts L x)
          = indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) :=
        indexfAddRight hyf hef hzf (by rw [hidxEz]; omega)
      by_cases hel : eList y = lYSpine L r x
      · rw [hel]
        exact List.mem_append.mpr (Or.inl (aq13w1_yMemSListRtrans L hL hgn hm hf hnf))
      · have hpos : 0 < indexf (lYSpine L r x) (eList y) (findFaceDarts L x) := by
          rcases Nat.eq_zero_or_pos (indexf (lYSpine L r x) (eList y) (findFaceDarts L x)) with h0 | hpos
          · exact absurd (indexfZeroEq hyf hef h0) (fun h => hel h.symm)
          · exact hpos
        have hmemW : eList y ∈ between (findFaceDarts L x) (lYSpine L r x)
            (lZSpine L N r x) :=
          (indexfBetwnEq hyz hfnd hyf hzf).mpr ⟨hpos, by omega⟩
        exact List.mem_append.mpr (Or.inl (aq13w1b_betwnMemSListRtrans L hL hgn hm hf hnf hmemW))
#print axioms Kepler.Text.TameSpine.aq13w4a2c3_fChainLast