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

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph nonFinals minimalFace minimalVertex
  generatePolygon subdivFace maxGon setFinal)
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

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.assumptionSet3Projection
#print axioms Kepler.Text.Reduction3.reductionA
