/-
  Kepler.Text.Reduction3Thm19 — J5-8 D/E/F：`reduction_D/E/F`
  （reduction3.hl:4578 / :4682 / :5636）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm18
import Kepler.Text.Reduction3Thm5D
import Kepler.Text.Reduction3Thm11
import Kepler.Text.Reduction3Thm10
import Kepler.Text.Reduction3Thm2
import Kepler.Text.Reduction3Thm13B
import Kepler.Text.Reduction3Thm14i
import Kepler.Text.Reduction5J5Termination

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph nonFinals minimalFace minimalVertex between)
open Kepler.Assembly (GoodList findFaceDarts prevEl nextEl listPairs)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans transformCount finalList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- HOL `reduction_D`（reduction3.hl:4578-4678）。 -/
theorem reductionD
    (hK10 : assumptionSetK10Full)
    (hgen : ∀ (L : fgraph ℕ) (hL : GoodList L) (N Nk : List (List Dart)) (g : Graph) (p : ℕ)
      (fs : List Face) (f : Face) (v k : ℕ) (r : List Dart) (x : Dart)
      (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (gk : Graph) (fk : Face),
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
      gk = (nfgtrans' (g.countVertices, f, g) L N r x k).2.2 →
      fk = (nfgtrans' (g.countVertices, f, g) L N r x k).2.1 →
      transformCount L N r x = k →
      ntrans L N r x k = Nk →
      findFaceDarts L x = fx →
      (fgraphOfGraph gk = quotientList L Nk ∧
        Kepler.Text.TameCorrList.GoodFacesV3 gk ∧
        gk.faceListAt.length = gk.countVertices ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq gk ∧
        ((some (ztrans L N r x (k - 1)).1, 0) : Option ℕ × ℕ)
          = (bNfgtrans0 f g L N r x k).1 ∧
        (fk, gk) = (bNfgtrans0 f g L N r x k).2 ∧
        core L (rtrans L N r x k) = fk.vertices)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionC (assumptionSet3_of_assumptionSetK10 GoodNodesSlot IsRestrictedSlot
    MarkedSlot hK10)
  intro L hL N Nk g p fs f v k r x fx uvns gk fk vs vs' hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp hfs hf hv hlc huv hvs hvs' hg_def hf_def hk hN' hfx
  have hntc := nfgtransTransformCount (g.countVertices) f g L N r x k
    IsRestrictedSlot (fun _ => hres) hk
  have hg_def' : gk = (nfgtrans' (g.countVertices, f, g) L N r x k).2.2 := by
    rw [hg_def, huv, ← hntc]
  have hf_def' : fk = (nfgtrans' (g.countVertices, f, g) L N r x k).2.1 := by
    rw [hf_def, huv, ← hntc]
  have h := hgen L hL N Nk g p fs f v k r x fx uvns gk fk hgn hres hnvp hm hnf hmq hng
    hpg hgf hvs2 hp hfs hf hv hlc huv hg_def' hf_def' hk hN' hfx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  -- elementPre / prevEl / core
  have hpre : elementPre L N :=
    Kepler.Text.Reduction3.markedListElementPre L hL hm g hmq.2 hvs2
  have hcore : core L r = f.vertices :=
    Kepler.Text.Reduction3.minimalFaceCore L hL hgn hres N r x g hmq hm hng f v
      (by rw [hfs]; exact hf.symm) hv hlc
  have hqu : ∀ s ∈ quotientList L N, s.Nodup := hm.2.2.2.2.1.1
  have hpx : (prevEl (core L r) v, v) = x := by
    rw [hcore]
    exact (Kepler.Text.Reduction3.loopChoiceProps L hL hgn hres N hm.2.1 g hng hqu hmq
      r x f v (by rw [hfs]; exact hf.symm) hv.symm hlc).2.2.2
  -- K10 结论（k 状态）
  have hK10i := hK10 L N r x k uvns (destTripleFull (core L r) v uvns)
    ((destTripleFull (core L r) v uvns).filterMap id) fx v
    ⟨hL, (fun _ => hgn), (fun _ => hres), hpre, hnvp, (fun _ => hm), hnf,
     huv.symm, rfl, rfl, hk, hfx, hpx⟩
  -- bNfgtransk 的 hobj
  have hobj : ∃ (f0 : Face) (g0 : Graph),
      (let fst_u0 : Option ℕ :=
         if (nextEl fx x).1 = (ytrans L N r x 0).1 then none
         else some (prevEl f.vertices (ytrans L N r x 0).1)
       (((some (ztrans L N r x (k - 1)).1, 0), f0, g0) =
         List.foldl subdivSingleStep ((fst_u0, 0), f, g)
           (destTriple0 f.vertices [] (coreTripleV4 L N r x)))) ∧
      f0.vertices.Nodup ∧
      x.1 ∈ f0.vertices ∧
      (ztrans L N r x (k - 1)).1 ∈ f0.vertices ∧
      ((ztrans L N r x (k - 1)).1 ≠ x.1 →
        between f0.vertices (ztrans L N r x (k - 1)).1 x.1 =
        between f.vertices (ztrans L N r x (k - 1)).1 x.1) := by
    refine ⟨fk, gk, ?_, ?_, ?_, ?_, ?_⟩
    · have hb0 : bNfgtrans0 f g L N r x k =
          List.foldl subdivSingleStep
            ((if (nextEl (findFaceDarts L x) x).1 = (ytrans L N r x 0).1 then none
              else some (prevEl f.vertices (ytrans L N r x 0).1), 0), f, g)
            (batch0 f.vertices L N r x k) := by
        simp [bNfgtrans0]
      rw [hfx, batchK f.vertices L N r x k hk.symm] at hb0
      rw [h5, h6]
      simpa using hb0
    · rw [← h7]; exact hK10i.1
    · rw [← h7]; exact hK10i.2.1
    · rw [← h7]; exact hK10i.2.2.1
    · intro hne
      rw [← h7, ← hcore]
      exact hK10i.2.2.2.1 hne
  have hbk := bNfgtransk L N g fs f v k r x fx uvns vs
    hobj hK10 hL hgn hres hnvp hm hnf hmq hng hvs2 hfs.symm hf.symm hv hlc (by rw [← hcore]; exact hpx) huv hvs hk.symm hfx.symm
  -- C 的 5/6：从 (fk,gk) = SND (bNfgtrans0 …) + bNfgtransk
  have hpair_eq : (fk, gk) = (subdivFace0Beta g f none 0 vs).2 := by
    rw [h6]; exact hbk
  have hgk_beta : gk = (subdivFace0Beta g f none 0 vs).2.2 :=
    (Prod.ext_iff.mp hpair_eq).2
  have hfk_beta : fk = (subdivFace0Beta g f none 0 vs).2.1 :=
    (Prod.ext_iff.mp hpair_eq).1
  exact ⟨h1, h2, h3, h4, hgk_beta, hfk_beta, h7⟩


/-! ## §W-D2 `reduction_E`（reduction3.hl:4682） -/

/-- HOL `reduction_E`（reduction3.hl:4682-4733）。 -/
theorem reductionE
    (hK10 : assumptionSetK10Full)
    (hgen : ∀ (i : ℕ) (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart))
      (g : Graph) (p : ℕ) (fs : List Face) (f : Face) (v : ℕ) (r : List Dart)
      (x : Dart) (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (gi : Graph) (fi : Face),
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
      fx = findFaceDarts L x →
      uvns = coreTripleV4 L N r x →
      gi = (nfgtrans' (g.countVertices, f, g) L N r x i).2.2 →
      fi = (nfgtrans' (g.countVertices, f, g) L N r x i).2.1 →
      i ≤ transformCount L N r x →
      (fgraphOfGraph gi = quotientList L (ntrans L N r x i) ∧
        Kepler.Text.TameCorrList.GoodFacesV3 gi ∧
        gi.faceListAt.length = gi.countVertices ∧
        Kepler.Text.TameCorrList.VerticesSet2Eq gi ∧
        (0 < i → ((some (ztrans L N r x (i - 1)).1, 0) : Option ℕ × ℕ)
          = (bNfgtrans0 f g L N r x i).1) ∧
        (fi, gi) = (bNfgtrans0 f g L N r x i).2 ∧
        core L (rtrans L N r x i) = fi.vertices)) :
    Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  apply reductionD hK10
  intro L hL N Nk g p fs f v k r x fx uvns gk fk hgn hres hnvp hm hnf hmq hng hpg hgf
    hvs2 hp hfs hf hv hlc huv hg_def hf_def hk hN' hfx
  have h := hgen k L hL N g p fs f v r x fx uvns gk fk hgn hres hnvp hm hnf hmq hng hpg
    hgf hvs2 hp hfs hf hv hlc hfx.symm huv hg_def hf_def (by rw [hk])
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hfinal := Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm
    (t := transformCount L N r x) rfl
  have hkpos : 0 < k := by
    rw [← hk]
    exact Nat.pos_of_ne_zero (transformCountNon0 L N r x hfinal hnf)
  exact ⟨by rwa [← hN'], h2, h3, h4, h5 hkpos, h6, h7⟩

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.reductionD
#print axioms Kepler.Text.Reduction3.reductionE
