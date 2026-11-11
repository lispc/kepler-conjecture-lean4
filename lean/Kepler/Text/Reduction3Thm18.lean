/-
  Kepler.Text.Reduction3Thm18 — J5-8 W6f/g/h：`reduction_A/B/C`
  （reduction3.hl:2278 / :2478 / :2629）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm17
import Kepler.Text.Reduction3Thm6D2
import Kepler.Text.Reduction3Thm7C
import Kepler.Text.Reduction3Thm7D
import Kepler.Text.Reduction3Thm13B
import Kepler.Text.T4TheoryA
import Kepler.Text.T4TheoryB
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction3Thm5B
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.TameSpine.TameList2
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph nonFinals minimalFace minimalVertex
  generatePolygon subdivFace maxGon setFinal makeFaceFinal)
open Kepler.Assembly (GoodList findFaceDarts prevEl nextEl listPairs listOfDarts)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans transformCount finalList indexf)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- 私有：`List.filterMap id = (filter isSome) |>.map get!`（Thm17 私有件跨文件复制）。 -/
private theorem filterMapIdEqMapGet18 (vs : List (Option ℕ)) :
    List.filterMap id vs = (vs.filter Option.isSome).map Option.get! := by
  induction vs with
  | nil => rfl
  | cons o os ih => cases o <;> simpa [List.filterMap] using ih

/-! ## §W6-projection `assumptionSet3` → 26 元合取 -/

/-- `assumptionSet3` 在 `(L,N,r,x,k,uvns,vs,vs',fx,v)` 处的结论（26 合取），
供 `reduction_A` 消费；载体取 `GoodNodesSlot`/`IsRestrictedSlot`/`MarkedSlot`。 -/
theorem assumptionSet3Projection
    (hA3 : assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot)
    (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ)) (vs' : List ℕ)
    (fx : List Dart) (v : ℕ)
    (hnvp : newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hep : elementPre L N)
    (hnf : ¬ finalList L r) (huv : coreTripleV4 L N r x = uvns)
    (hvs : destTripleFull (core L r) v uvns = vs) (hvs' : vs.filterMap id = vs')
    (hk : transformCount L N r x = k) (hfx : findFaceDarts L x = fx)
    (hprev : (prevEl (core L r) v, v) = x) :
    transformCount L N r x ≠ 0 ∧
    0 < transformCount L N r x ∧
    x.1 = prevEl (core L r) v ∧
    x ∈ fx ∧ fx.Nodup ∧
    1 ≤ fx.length ∧
    1 < (core L r).length ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ztrans L N r x i) fx ≤
      indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < k → indexf (ytrans L N r x 0) (ytrans L N r x (i + 1)) fx ≤
      indexf (ytrans L N r x 0) (ztrans L N r x (i + 1)) fx) ∧
    indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ≤ indexf (nextEl fx x) x fx ∧
    indexf (nextEl fx x) (ytrans L N r x 0) fx ≤
      indexf (nextEl fx x) (ztrans L N r x (k - 1)) fx ∧
    nextEl fx x ∈ r ∧
    (∀ i, i < k → ytrans L N r x i ≠ ztrans L N r x i) ∧
    (∀ i, i < k → ztrans L N r x i ∈ r) ∧
    (∀ i, i < k → ytrans L N r x i ∈ r) ∧
    nextEl fx x ∈ fx ∧
    (∀ i, i < k → ytrans L N r x i ∈ fx) ∧
    (∀ i, i < k → ztrans L N r x i ∈ fx) ∧
    (core L r).Nodup ∧
    (nextEl fx x).1 = v ∧
    (∀ u ∈ r, u.1 ∈ core L r) ∧
    indexf v (ytrans L N r x 0).1 (core L r) =
      indexf (nextEl fx x) (ytrans L N r x 0) fx ∧
    indexf (ztrans L N r x (k - 1)).1 x.1 (core L r) =
      indexf (ztrans L N r x (k - 1)) x fx ∧
    (∀ i, i + 1 < k →
      indexf (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 (core L r) =
      indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) fx) ∧
    (∀ i, i + 1 < vs'.length →
      indexf v (vs'.getD i 0) (core L r) <
      indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
    (∀ i, (let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
      ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
        i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
      d ∈ listPairs (core L r))) :=
  hA3 L N r x k uvns vs vs' fx v
    ⟨hL, (fun _ => hgn), (fun _ => hres), hnvp, (fun _ => hm), hep, hnf,
     huv, hvs, hvs', hk, hfx, hprev⟩

/-! ## §W6f `reduction_A`（reduction3.hl:2278） -/

/-- HOL `reduction_A`（reduction3.hl:2278-2360）。 -/
theorem reductionA
    (hA3 : assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot)
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N N' : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (g' : Graph)
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
      v = minimalVertex g f →
      loopChoice2 g L N = (r, x) →
      uvns = coreTripleV4 L N r x →
      vs = destTripleFull f.vertices v uvns →
      (vs.filter Option.isSome).map Option.get! = vs' →
      subdivFaceFinal2 g f uvns = g' →
      transformCount L N r x = k →
      ntrans L N r x k = N' →
      findFaceDarts L x = fx →
      (fgraphOfGraph g' = quotientList L N' ∧
        Kepler.Text.TameCorrList.GoodFacesV3 g' ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq g' ∧
        subdivFace g f vs = g' ∧
        listPairs ((subdivFace0Alt2 g f g.countVertices uvns).1.vertices)
          = rtrans L N r x k)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionSubdivFace2
  intro L hL N N' g p fs f v k r x uvns g' i vs vs' hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hg' hk hN' hi
  -- elementPre / prevEl
  have hep : elementPre L N :=
    Kepler.Text.Reduction3.markedListElementPre L hL hm g hmq.2 hvs2
  have hcore : core L r = f.vertices :=
    Kepler.Text.Reduction3.minimalFaceCore L hL hgn hres N r x g hmq hm hng f v
      (by rw [hfs]; exact hf) hv.symm hlc
  have hqu : ∀ s ∈ quotientList L N, s.Nodup := hm.2.2.2.2.1.1
  have hprev : (prevEl (core L r) v, v) = x := by
    rw [hcore]
    exact (Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hm.2.1 g hng hqu hmq
      r x f v (by rw [hfs]; exact hf) hv hlc).2.2.2
  have hvs0 : destTripleFull (core L r) v uvns = vs := by
    rw [hcore, ← hvs]
  have hvs0' : vs.filterMap id = vs' := by
    rw [filterMapIdEqMapGet18 vs, hvs']
  -- assumptionSet3 投影
  have hproj := assumptionSet3Projection hA3 L hL hgn hres N r x k uvns vs vs'
    (findFaceDarts L x) v hnvp hm hep hnf huv.symm hvs0 hvs0' hk rfl hprev
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26⟩ := hproj
  -- sizeVs
  have hsize : (findFaceDarts L x).length = vs.length :=
    sizeVs GoodNodesSlot IsRestrictedSlot MarkedSlot L N k r x (findFaceDarts L x) v
      uvns vs hL (fun _ => hgn) (fun _ => hres) hnvp (fun _ => hm) hnf huv.symm hvs0 hk rfl
      a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22
      a23 a24
  -- hgen
  have h := hgen L hL N N' g p fs f v k r x (findFaceDarts L x) uvns g' vs vs'
    hgn hres hnvp hm hnf hmq hng hpg hgf hvs2 hp hfs hf hv.symm hlc huv hvs hvs' hg' hk hN' rfl
  obtain ⟨hfg', hgf', hvs2', hsub, hpair⟩ := h
  -- mono / P19 转换
  have hmono : ∀ j, j + 1 < vs'.length →
      indexf v vs'[j]! f.vertices < indexf v vs'[j+1]! f.vertices := by
    intro j hj
    have h := a25 j hj
    rw [hcore] at h
    simpa only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      Nat.default_eq_zero] using h
  have hP19 : ∀ j, j + 1 < vs.length → (vs[j]!).isSome = true → (vs[j+1]!).isSome = true →
      ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listOfDarts (fgraphOfGraph g) →
      ((vs[j]!).getD 0, (vs[j+1]!).getD 0) ∈ listPairs f.vertices := by
    intro j hj h1 h2 hd
    have h := a26 j
    rw [hcore] at h
    have h1' : (vs.getD j none).isSome = true := by
      simpa only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        Option.default_eq_none] using h1
    have h2' : (vs.getD (j + 1) none).isSome = true := by
      simpa only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        Option.default_eq_none] using h2
    have hd' : ((vs.getD j none).getD 0, (vs.getD (j + 1) none).getD 0)
        ∈ listOfDarts (quotientList L N) := by
      simpa only [← hmq.2, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        Option.default_eq_none] using hd
    have hres' : ((vs.getD j none).getD 0, (vs.getD (j + 1) none).getD 0)
        ∈ listPairs f.vertices := h ⟨h1', h2', hj, hd'⟩
    simpa only [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      Option.default_eq_none] using hres'
  exact ⟨hfg', hgf', hvs2', hmono, by rw [← hi]; exact hsize, hP19, hsub, hpair⟩


/-! ## §W6g `reduction_B`（reduction3.hl:2478） -/

/-- HOL `reduction_B`（reduction3.hl:2478-2627）。 -/
theorem reductionB
    (hA3 : assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot)
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N Nk : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (gk : Graph) (fk : Face)
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
      f = minimalFace fs →
      v = minimalVertex g f →
      loopChoice2 g L N = (r, x) →
      uvns = coreTripleV4 L N r x →
      vs = destTripleFull f.vertices v uvns →
      (vs.filter Option.isSome).map Option.get! = vs' →
      gk = (subdivFace0Alt2 g f g.countVertices uvns).2 →
      fk = (subdivFace0Alt2 g f g.countVertices uvns).1 →
      transformCount L N r x = k →
      ntrans L N r x k = Nk →
      findFaceDarts L x = fx →
      (fgraphOfGraph gk = quotientList L Nk ∧
        Kepler.Text.TameCorrList.GoodFacesV3 gk ∧
        gk.faceListAt.length = gk.countVertices ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq gk ∧
        gk = (subdivFace0Beta g f none 0 vs).2.2 ∧
        fk = (subdivFace0Beta g f none 0 vs).2.1 ∧
        listPairs fk.vertices = rtrans L N r x k)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionA hA3
  intro L hL N Nk g p fs f v k r x fx uvns g' vs vs' hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hg' hk hN' hfx
  let gk : Graph := (subdivFace0Alt2 g f g.countVertices uvns).2
  let fk : Face := (subdivFace0Alt2 g f g.countVertices uvns).1
  have hgk : gk = (subdivFace0Alt2 g f g.countVertices uvns).2 := rfl
  have hfk : fk = (subdivFace0Alt2 g f g.countVertices uvns).1 := rfl
  have h := hgen L hL N Nk g p fs f v k r x fx uvns gk fk vs vs' hgn hres hnvp hm hnf
    hmq hng hpg hgf hvs2 hp hfs hf.symm hv hlc huv hvs hvs' hgk hfk hk hN' hfx
  obtain ⟨hfgk, hgfk, hcl, hvs2k, hgk_beta, hfk_beta, hpair⟩ := h
  have hg'eq : g' = makeFaceFinal fk gk := by
    rw [← hg']
    simp only [subdivFaceFinal2, ← hgk, ← hfk]
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hfinal := Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm
    (t := transformCount L N r x) rfl
  have hne : vs ≠ [] := vsNonnil L N r x f.vertices v uvns vs hfinal hnf huv hvs
  have h0 : transformCount L N r x ≠ 0 :=
    Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
  have hhd := hdVsSomeV L N r x g f v uvns vs h0 huv hvs
  have his : (vs.headD none).isSome = true := by rw [hhd]; rfl
  have hm_k : markedList L hL Nk (rtrans L N r x k) x := by
    rw [← hN']
    exact Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm k
  have hnl : normalList L hL Nk := hm_k.2.1
  have huniq : ∀ v ∈ Kepler.Text.TameCorrList.verticesSet2 gk,
      (Kepler.Text.TameCorrList.facesAtV2 gk v).Nodup :=
    fun v _ => facesAtV2Uniq L hL hgn Nk hnl hres gk v hfgk
  have hgf' : Kepler.Text.TameCorrList.GoodFacesV3 (makeFaceFinal fk gk) :=
    goodFacesMakeFaceFinal fk gk huniq hcl hgfk
  have hvs2' : Kepler.Text.TameCorrList.VerticesSet2Eq (makeFaceFinal fk gk) := by
    show Kepler.Text.TameCorrList.verticesSet2 (makeFaceFinal fk gk) =
      Kepler.Text.TameLp.elementsOfList (makeFaceFinal fk gk).fgraph
    rw [show Kepler.Text.TameCorrList.verticesSet2 (makeFaceFinal fk gk)
        = Kepler.Text.TameCorrList.verticesSet2 gk from by
      show {v : ℕ | v ∈ (makeFaceFinal fk gk).vertices} = {v : ℕ | v ∈ gk.vertices}
      rw [Kepler.Text.TameSpine.verticesSet2MakeFaceFinal]]
    rw [show (makeFaceFinal fk gk).fgraph = gk.fgraph from
      Kepler.Text.TameSpine.fgraphMakeFaceFinal fk gk]
    exact hvs2k
  have hfg' : fgraphOfGraph (makeFaceFinal fk gk) = quotientList L Nk := by
    have hb : fgraphOfGraph (makeFaceFinal fk gk)
        = Kepler.Text.TameSpine.facesVertexLists (makeFaceFinal fk gk) := rfl
    have hb2 : Kepler.Text.TameSpine.facesVertexLists gk = fgraphOfGraph gk := rfl
    rw [hb, Kepler.Text.TameSpine.fgraphMakeFaceFinal, hb2]
    exact hfgk
  have hsub_beta : subdivFace g f vs
      = makeFaceFinal (subdivFace0Beta g f none 0 vs).2.1
          (subdivFace0Beta g f none 0 vs).2.2 :=
    subdivFaceSubdivFace0Beta g f vs hne his
  have hsub : subdivFace g f vs = makeFaceFinal fk gk := by
    rw [hsub_beta, ← hfk_beta, ← hgk_beta]
  have hpair' : listPairs ((subdivFace0Alt2 g f g.countVertices uvns).1.vertices)
      = rtrans L N r x k := by
    rw [← hfk]
    exact hpair
  exact ⟨by rwa [← hg'], by rwa [← hg'], by rwa [← hg'], by rwa [← hg'], hpair'⟩

/-! ## §W6h `reduction_C`（reduction3.hl:2629） -/

/-- HOL `reduction_C`（reduction3.hl:2629-2704）。 -/
theorem reductionC
    (hA3 : assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot)
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N Nk : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart)
      (x : Dart) (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (gk : Graph) (fk : Face)
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
      f = minimalFace fs →
      v = minimalVertex g f →
      loopChoice2 g L N = (r, x) →
      uvns = coreTripleV4 L N r x →
      vs = destTripleFull f.vertices v uvns →
      (vs.filter Option.isSome).map Option.get! = vs' →
      gk = (subdivFace0Alt2 g f g.countVertices uvns).2 →
      fk = (subdivFace0Alt2 g f g.countVertices uvns).1 →
      transformCount L N r x = k →
      ntrans L N r x k = Nk →
      findFaceDarts L x = fx →
      (fgraphOfGraph gk = quotientList L Nk ∧
        Kepler.Text.TameCorrList.GoodFacesV3 gk ∧
        gk.faceListAt.length = gk.countVertices ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq gk ∧
        gk = (subdivFace0Beta g f none 0 vs).2.2 ∧
        fk = (subdivFace0Beta g f none 0 vs).2.1 ∧
        core L (rtrans L N r x k) = fk.vertices)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionB hA3
  intro L hL N Nk g p fs f v k r x fx uvns gk fk vs vs' hgn hres hnvp hm hnf hmq hng
    hpg hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hgk hfk hk hN' hfx
  have h := hgen L hL N Nk g p fs f v k r x fx uvns gk fk vs vs' hgn hres hnvp hm hnf
    hmq hng hpg hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hgk hfk hk hN' hfx
  obtain ⟨hfgk, hgfk, hcl, hvs2k, hgk_beta, hfk_beta, hcorek⟩ := h
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hm_k : markedList L hL Nk (rtrans L N r x k) x := by
    rw [← hN']
    exact Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm k
  have hnl : normalList L hL Nk := hm_k.2.1
  have hnlS : Kepler.Text.TameSpine.NormalListSpine hL Nk :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL Nk).mp hnl
  have hrN : rtrans L N r x k ∈ Nk := hm_k.2.2.1
  have hdarts : ∀ d ∈ rtrans L N r x k, d ∈ listOfDarts L := by
    intro d hd
    exact Kepler.Text.TameSpine.normalListListOfDarts hnlS d
      (List.mem_flatten.mpr ⟨rtrans L N r x k, hrN, hd⟩)
  have hrn : (rtrans L N r x k).Nodup :=
    (Kepler.Text.TameSpine.normalListUniqNonnil hnlS hrN).1
  have hfin : finalList L (rtrans L N r x k) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm (t := k) hk
  have hxr : x ∈ rtrans L N r x k := hm_k.2.2.2.1
  have hxD : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hpair : listPairs fk.vertices = rtrans L N r x k := by
    have h := finalListPairsCore L (rtrans L N r x k) x hL hres hdarts hrn hfin hxr hxD
    rwa [hcorek] at h
  exact ⟨hfgk, hgfk, hcl, hvs2k, hgk_beta, hfk_beta, hpair⟩

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.assumptionSet3Projection
#print axioms Kepler.Text.Reduction3.reductionA
#print axioms Kepler.Text.Reduction3.reductionB
#print axioms Kepler.Text.Reduction3.reductionC
