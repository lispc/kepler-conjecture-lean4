/-
  Kepler.Text.Reduction3Thm17 — J5-8 W6d-2 + W6e
  （reduction3.hl:720 reduction_subdivFace / :1379 reduction_subdivFace2）。

  **勘误记档**：上一轮把 `reduction_subdivFace` 判为 BLOCKED，误判原因是漏读
  reduction3.hl:740 的 `vs' = MAP the (filter isSome vs) /\`——它是 HOL 陈述的
  普通前提（20 条中的第 18 条），不是 let、不是待 SF。本件按原前提逐字携入
  `hvs' : (vs.filter Option.isSome).map Option.get! = vs'`（HOL `MAP the (filter …)`
  的 Lean 项序），故无需 SF。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm16
import Kepler.Text.Reduction3Thm15
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction3Thm7D
import Kepler.Text.T4TheoryB
import Kepler.Text.Reduction1W2b

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph nonFinals minimalFace minimalVertex
  generatePolygon subdivFace maxGon)
open Kepler.Assembly (GoodList findFaceDarts prevEl listPairs listOfDarts)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans transformCount finalList indexf)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §W6d-2 `reduction_subdivFace`（reduction3.hl:720-794） -/

/-- HOL `reduction_subdivFace`（reduction3.hl:720-794）。 -/
theorem reductionSubdivFace
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (uvns : List (ℕ × ℕ × ℕ)) (g' : Graph) (i : ℕ)
      (vs : List (Option ℕ)) (vs' : List ℕ),
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
      nonFinals g = fs →
      minimalFace fs = f →
      minimalVertex g f = v →
      loopChoice2 g L N = (r, x) →
      uvns = coreTripleV4 L N r x →
      vs = destTripleFull f.vertices v uvns →
      (vs.filter Option.isSome).map Option.get! = vs' →
      subdivFaceFinal2 g f uvns = g' →
      transformCount L N r x = k →
      ntrans L N r x k = N' →
      (findFaceDarts L x).length = i →
      (fgraphOfGraph g' = quotientList L N' ∧
        Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
        3 ≤ vs.length ∧ vs.head! = some v ∧
        (vs.getLast!).isSome = true ∧
        prevEl f.vertices v = (vs.getLast!).getD 0 ∧
        (∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices) ∧
        (∀ j, j + 1 < vs'.length → indexf v vs'[j]! f.vertices < indexf v vs'[j+1]! f.vertices) ∧
        i = vs.length ∧
        (∀ j, j + 1 < vs.length → (vs[j]!).isSome = true → (vs[j+1]!).isSome = true →
          ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listOfDarts (fgraphOfGraph g) →
          ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listPairs f.vertices) ∧
        subdivFace g f vs = g' ∧
        listPairs ((subdivFace0Alt2 g f g.countVertices uvns).1.vertices)
          = rtrans L N r x k)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply generateNonfinalPolygonReduction
  intro L hL N N' g p fs f v k r x uvns g' i hgn hres hnvp hm hnf hmq hng hpg hgf hvs2 hp
    huv hg' hfs hf hv hlc hk hN' hi
  have h := hgen L hL N N' g p fs f v k r x uvns g' i
    (destTripleFull f.vertices v uvns)
    ((destTripleFull f.vertices v uvns).filter Option.isSome |>.map Option.get!)
    hgn hres hnvp hm hnf hmq hng hpg hgf hvs2 hp hfs hf hv hlc huv rfl rfl hg' hk hN' hi
  obtain ⟨hfg', hgf', hvs2', h3, hhd, hlast, hprev, hall, hmono, hivs, hP19, hsub, hpair⟩ := h
  -- g' ∈ generatePolygon i v f g
  have hfmem : f ∈ g.faces := by
    have h := Kepler.Text.TameSpine.minimalFaceFace g hng
    rwa [hfs, hf] at h
  have hfm : f.vertices ∈ g.fgraph :=
    List.mem_map.mpr ⟨f, hfmem, rfl⟩
  have hun : ∀ l ∈ g.fgraph, l.Nodup := by
    intro l hl
    have hl' : l ∈ fgraphOfGraph g := hl
    rw [hmq.2] at hl'
    exact Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm l hl'
  have hgenPoly : g' ∈ generatePolygon i v f g := by
    rw [← hsub, hivs]
    exact Kepler.Text.Reduction1.generatePolygonCriteria rfl h3 hhd hlast hprev hfm hun
      hgf hvs2 hall hmono hP19
  exact ⟨hpair, hfg', hgf', hvs2', hgenPoly⟩



/-- 私有：`List.filterMap id = (filter isSome) |>.map get!`（junk 访问器转换）。 -/
private theorem filterMapIdEqMapGet (vs : List (Option ℕ)) :
    List.filterMap id vs = (vs.filter Option.isSome).map Option.get! := by
  induction vs with
  | nil => rfl
  | cons o os ih => cases o <;> simpa [List.filterMap] using ih

/-! ## §W6e `reduction_subdivFace2`（reduction3.hl:1379-1448） -/

/-- HOL `reduction_subdivFace2`（reduction3.hl:1379-1448）。 -/
theorem reductionSubdivFace2
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (uvns : List (ℕ × ℕ × ℕ)) (g' : Graph) (i : ℕ)
      (vs : List (Option ℕ)) (vs' : List ℕ),
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
      nonFinals g = fs →
      minimalFace fs = f →
      minimalVertex g f = v →
      loopChoice2 g L N = (r, x) →
      uvns = coreTripleV4 L N r x →
      vs = destTripleFull f.vertices v uvns →
      (vs.filter Option.isSome).map Option.get! = vs' →
      subdivFaceFinal2 g f uvns = g' →
      transformCount L N r x = k →
      ntrans L N r x k = N' →
      (findFaceDarts L x).length = i →
      (fgraphOfGraph g' = quotientList L N' ∧
        Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
        (∀ j, j + 1 < vs'.length → indexf v vs'[j]! f.vertices < indexf v vs'[j+1]! f.vertices) ∧
        i = vs.length ∧
        (∀ j, j + 1 < vs.length → (vs[j]!).isSome = true → (vs[j+1]!).isSome = true →
          ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listOfDarts (fgraphOfGraph g) →
          ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listPairs f.vertices) ∧
        subdivFace g f vs = g' ∧
        listPairs ((subdivFace0Alt2 g f g.countVertices uvns).1.vertices)
          = rtrans L N r x k)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionSubdivFace
  intro L hL N N' g p fs f v k r x uvns g' i vs vs' hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hg' hk hN' hi
  have h := hgen L hL N N' g p fs f v k r x uvns g' i vs vs' hgn hres hnvp hm hnf hmq
    hng hpg hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hg' hk hN' hi
  obtain ⟨hfg', hgf', hvs2', hmono, hivs, hP19, hsub, hpair⟩ := h
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have h0 : transformCount L N r x ≠ 0 :=
    Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
  have h3 : 3 ≤ vs.length := by
    rw [← hivs, ← hi]
    exact t10b_sizel_3_concl L hL N r x hres hm
  have hhd : vs.head! = some v := by
    simpa only [List.head!_eq_head?_getD, List.headD_eq_head?_getD, Option.default_eq_none]
      using hdVsSomeV L N r x g f v uvns vs h0 huv hvs
  have hlast : (vs.getLast!).isSome = true := by
    have h := lastVsSomePrev L N r x g f v uvns vs h0 huv hvs
    have h2 : (vs.getLastD none).isSome = true := by rw [h]; rfl
    simpa only [List.getLast!_eq_getLast?_getD, List.getLastD_eq_getLast?,
      Option.default_eq_none] using h2
  have hprev : prevEl f.vertices v = (vs.getLast!).getD 0 := by
    have h := lastVsSomePrev L N r x g f v uvns vs h0 huv hvs
    have h2 : (vs.getLastD none).getD 0 = prevEl f.vertices v := by rw [h]; rfl
    simpa only [List.getLast!_eq_getLast?_getD, List.getLastD_eq_getLast?,
      Option.default_eq_none] using h2.symm
  have hall : ∀ t ∈ (vs.filter Option.isSome).map Option.get!, t ∈ f.vertices := by
    have h := destTripleFullAllFilter L N r x g fs f v uvns vs hL hgn hres hm hmq hnf hng
      hfs hf hv.symm hlc huv hvs
    rwa [filterMapIdEqMapGet vs] at h
  exact ⟨hfg', hgf', hvs2', h3, hhd, hlast, hprev, hall, hmono, hivs, hP19, hsub, hpair⟩

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.reductionSubdivFace
#print axioms Kepler.Text.Reduction3.reductionSubdivFace2
