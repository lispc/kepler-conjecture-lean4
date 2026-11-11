/-
  Kepler.Text.Reduction3Thm16 — J5-8 W6c+W6d
  （reduction3.hl:388 generatePolygon_explicit_reduction /
   :623 generateNonfinalPolygon_reduction / :720 reduction_subdivFace）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm15
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction3Thm7C
import Kepler.Text.Reduction3Thm7D
import Kepler.Text.Reduction3Thm7F
import Kepler.Text.Reduction3DefsSubdivAlt
import Kepler.Text.Reduction1W4g
import Kepler.Text.Reduction1Mee2
import Kepler.Text.Reduction1AqtE
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.TameSpine.TameList58

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph nonFinals finals minimalFace minimalVertex
  generatePolygon subdivFace maxGon setFinal)
open Kepler.Assembly (GoodList findFaceDarts listPairs)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §W6c `generatePolygon_explicit_reduction`（reduction3.hl:388） -/

/-- HOL `generatePolygon_explicit_reduction`（reduction3.hl:388-455）：
`(∀ L N N' g p fs f v k r x uvns g' i, 前提 ==> match_quotient_list g' L N' ∧
 good_faces_v3 g' ∧ vertices_set2 g' = … ∧ MEM g' (generatePolygon i v f g))
 ==> restricted_hypermaps_are_planegraphs_v4`。 -/
theorem generatePolygonExplicitReduction
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (uvns : List (ℕ × ℕ × ℕ)) (g' : Graph) (i : ℕ),
      GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted →
      newvertexPrepped L N r x →
      markedList L hL N r x →
      ¬ finalList L r →
      matchQuotientList g L N →
      g.final = false →
      Kepler.Text.TameSpine.PlaneGraphPSpine p g →
      Kepler.Text.TameCorrList.GoodFacesV3 g →
      Kepler.Text.TameCorrList.VerticesSet2Eq g →
      p = (L.map List.length).foldr max 0 - 3 →
      uvns = coreTripleV4 L N r x →
      subdivFaceFinal2 g f uvns = g' →
      nonFinals g = fs →
      minimalFace fs = f →
      minimalVertex g f = v →
      loopChoice2 g L N = (r, x) →
      transformCount L N r x = k →
      ntrans L N r x k = N' →
      (findFaceDarts L x).length = i →
      matchQuotientList g' L N' ∧ Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
        g' ∈ generatePolygon i v f g) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  refine Kepler.Text.Reduction1.restrictedHypermapsArePlanegraphsReduction1OfAuq
    (fun L hL N N' g p fs f v k r x hgn hres hnvp hm hnf hmq hng hpg hgf hvs2 hp
      hfs hf hv hlc hk hN' => ?_)
    (fun L hL _ => Kepler.Text.TameSpine.transformAssumptionV2_of_goodList L hL)
    (fun L hL hgn hres => Kepler.Text.Reduction1.auqtzyzListSlot L hL hgn hres)
  have h := hgen L hL N N' g p fs f v k r x (coreTripleV4 L N r x)
    (subdivFaceFinal2 g f (coreTripleV4 L N r x)) (findFaceDarts L x).length
    hgn hres hnvp hm hnf hmq hng hpg hgf hvs2 hp rfl rfl
    hfs.symm hf.symm hv.symm hlc.symm hk.symm hN'.symm rfl
  obtain ⟨hmq', hgf', hvs2', hgen'⟩ := h
  have h3 : 3 ≤ (findFaceDarts L x).length :=
    t10b_sizel_3_concl L hL N r x hres hm
  have hmem : findFaceDarts L x ∈ Kepler.Text.TameSpine.listOfFaces L :=
    Kepler.Text.TameSpine.memFindFace L
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hle : (findFaceDarts L x).length ≤ (L.map List.length).foldr max 0 := by
    rw [← Kepler.Text.TameSpine.mapSizeListOfFaces L]
    exact Kepler.Text.TameSpine.foldrSizeMax hmem
  have hmax : (findFaceDarts L x).length ≤ maxGon p := by
    rw [maxGon, hp]
    omega
  exact ⟨subdivFaceFinal2 g f (coreTripleV4 L N r x), (findFaceDarts L x).length,
    hmq', h3, hmax, hgf', hvs2', hgen'⟩


/-! ## §W6d-1 `generateNonfinalPolygon_reduction`（reduction3.hl:623） -/

/-- HOL `generateNonfinalPolygon_reduction`（reduction3.hl:623-717）。 -/
theorem generateNonfinalPolygonReduction
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (uvns : List (ℕ × ℕ × ℕ)) (g' : Graph) (i : ℕ),
      GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted →
      newvertexPrepped L N r x →
      markedList L hL N r x →
      ¬ finalList L r →
      matchQuotientList g L N →
      g.final = false →
      Kepler.Text.TameSpine.PlaneGraphPSpine p g →
      Kepler.Text.TameCorrList.GoodFacesV3 g →
      Kepler.Text.TameCorrList.VerticesSet2Eq g →
      p = (L.map List.length).foldr max 0 - 3 →
      uvns = coreTripleV4 L N r x →
      subdivFaceFinal2 g f uvns = g' →
      nonFinals g = fs →
      minimalFace fs = f →
      minimalVertex g f = v →
      loopChoice2 g L N = (r, x) →
      transformCount L N r x = k →
      ntrans L N r x k = N' →
      (findFaceDarts L x).length = i →
      listPairs ((subdivFace0Alt2 g f g.countVertices uvns).1.vertices)
          = rtrans L N r x k ∧
        fgraphOfGraph g' = quotientList L N' ∧
        Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
        g' ∈ generatePolygon i v f g) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply generatePolygonExplicitReduction
  intro L hL N N' g p fs f v k r x uvns g' i hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp huv hg' hfs hf hv hlc hk hN' hi
  have h := hgen L hL N N' g p fs f v k r x uvns g' i hgn hres hnvp hm hnf hmq hng
    hpg hgf hvs2 hp huv hg' hfs hf hv hlc hk hN' hi
  obtain ⟨hpair, hfg', hgf', hvs2', hgenPoly⟩ := h
  -- f ∈ faces g / f.final = false
  have hfmem : f ∈ g.faces := by
    have h := Kepler.Text.TameSpine.minimalFaceFace g hng
    rwa [hfs, hf] at h
  have hffinal : f.final = false := by
    have hne : nonFinals g ≠ [] := by
      intro h0
      have h2 : (nonFinals g).isEmpty = false := hng
      rw [h0] at h2
      simp at h2
    have hmem : f ∈ nonFinals g := by
      rw [← hf, ← hfs]
      exact Kepler.Text.TameSpine.memMinimalFaceNonFinals g hne
    have h := (List.mem_filter.mp hmem).2
    simpa using h
  -- match_quotient_list：第一合取（finals g' ⊆ N'.filter final）
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  refine ⟨⟨?_, hfg'⟩, hgf', hvs2', hgenPoly⟩
  intro d hd
  rw [← hg'] at hd
  obtain ⟨xf, hx, rfl⟩ := List.mem_map.mp hd
  obtain ⟨hxmem, hxfin⟩ := List.mem_filter.mp hx
  have hxfinals : xf ∈ finals (subdivFaceFinal2 g f uvns) :=
    List.mem_filter.mpr ⟨hxmem, hxfin⟩
  have hxcase := subdivFaceFinal2Finals uvns g f hfmem hffinal xf hxfinals
  rw [List.mem_filter]
  rcases hxcase with hxold | hxnew
  · -- 老终面：match_quotient_list 的滤面条款
    have hdinN : listPairs xf.vertices ∈ N.filter (fun r => decide (finalList L r)) :=
      hmq.1 (listPairs xf.vertices) (List.mem_map.mpr ⟨xf, hxold, rfl⟩)
    obtain ⟨hdN, hdfin⟩ := List.mem_filter.mp hdinN
    refine ⟨?_, hdfin⟩
    have hne_r : listPairs xf.vertices ≠ r := by
      intro h
      rw [h] at hdfin
      exact hnf (of_decide_eq_true hdfin)
    rw [← hN']
    exact (ntransFinalList k L N r x (listPairs xf.vertices) hL hgn hm hnf hne_r hdN
      (by rw [hk])).2
  · -- 新终面：rtrans k
    subst hxnew
    rw [show (setFinal (subdivFace0Alt2 g f g.countVertices uvns).1).vertices
        = (subdivFace0Alt2 g f g.countVertices uvns).1.vertices from rfl]
    rw [hpair]
    refine ⟨?_, ?_⟩
    · rw [← hN']
      exact aq6Induct k L N r x hL hgn hm
    · rw [← hk]
      exact decide_eq_true (Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm rfl)

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.generatePolygonExplicitReduction
#print axioms Kepler.Text.Reduction3.generateNonfinalPolygonReduction
