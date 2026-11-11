/-
  Kepler.Text.Reduction5J5UvnsFinal — U1c 收尾 III：全 vs 装配 `uvnsWalkCons`
  （Cl + mem 合一；mem 半来自 J4 的 `Reduction5J5UvnsMemHalf`）。

  **文件分列原因（ERRATA 记录）**：`MemHalf` 自身 `import
  Kepler.Text.Reduction5J5UvnsChainCl`——在本文件内 import MemHalf 会成环，
  故装配件独立成文件（import 两边），不改 MemHalf、不改 ChainCl。

  纪律：零公理、零占位证明；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5UvnsChainCl
import Kepler.Text.Reduction5J5UvnsMemHalf

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)

/-- **U1c 主干**：`vs = destTripleFull (core L r) v (coreTripleV4)` 的
Cl 分类 + mem。Cl = init/mid/final 三段（`chainClInit`/`chainClMid@k-1`/
`chainClFinal`）经两次 `chainClAppend` 装配；mem = 三段
（`memInit`/`memMid@k-1`/`memFinal`）经两次 `memInAppend` 装配。 -/
theorem uvnsWalkCons
    (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)
    (∀ j, j + 1 < vs.length → (vs.getD j none).isSome → (vs.getD (j + 1) none).isSome →
        nextEl (core L r) ((vs.getD j none).getD 0) = (vs.getD (j + 1) none).getD 0 ∨
        ∃ i, i < k ∧ (vs.getD j none).getD 0 = (ytrans L N r x i).1 ∧
          (vs.getD (j + 1) none).getD 0 = (ztrans L N r x i).1 ∧
          (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = 0) ∧
    (∀ j, j < vs.length → (vs.getD j none).isSome →
        (vs.getD j none).getD 0 ∈ core L r) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hk0 : 0 < k := by
    have h := Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
    rw [hk] at h
    exact Nat.pos_of_ne_zero h
  have hnz : transformCount L N r x ≠ 0 :=
    Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hnf
  have hnfi : ∀ i, i < k → ¬ finalList L (rtrans L N r x i) := fun i hi =>
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  have hcoreof : ∀ u ∈ r, u.1 ∈ core L r :=
    Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm
  have hym : ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs1 L hL hgn haq i (hnfi i hi) hm)
  have hzm : ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := fun i hi =>
    hcoreof _ (pnxvwfs2 L hL hgn haq i (hnfi i hi) hm)
  have hrnd : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hx1 : x.1 = prevEl (core L r) v := (congrArg Prod.fst hprev).symm
  have hvcore : v ∈ core L r := by
    have hpre : prevEl (core L r) v ∈ core L r := by
      rw [← hx1]
      exact hcoreof x hm.2.2.2.1
    have h := Kepler.Text.TameLp.nextEl_mem_of_mem hpre
    rwa [Kepler.Text.Reduction5.nextPrevId hrnd v] at h
  have hprevcore : prevEl (core L r) v ∈ core L r := by
    rw [← hx1]
    exact hcoreof x hm.2.2.2.1
  have hy0 : (ytrans L N r x 0).1 ∈ core L r := hym 0 hk0
  have hzcore : (ztrans L N r x (k - 1)).1 ∈ core L r := hzm (k - 1) (by omega)
  have hlen0 : (Kepler.Text.Reduction3.coreTripleV4 L N r x).length = k := by
    rw [Kepler.Text.Reduction3.coreTripleV4_length]
    exact hk
  have hhead : (Kepler.Text.Reduction3.coreTripleV4 L N r x).headD (0, 0, 0) =
      ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
        (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) := by
    cases huv : Kepler.Text.Reduction3.coreTripleV4 L N r x with
    | nil => rw [huv] at hlen0; simp at hlen0; omega
    | cons a t =>
      have h0 := Kepler.Text.Reduction3.elCoreTriple L N r x 0 (by rw [hk]; exact hk0)
      simpa only [huv, List.headD_cons, List.getElem_cons_zero] using h0
  have hlast : (Kepler.Text.Reduction3.coreTripleV4 L N r x).getLastD (0, 0, 0) =
      ((ytrans L N r x (k - 1)).1, (ztrans L N r x (k - 1)).1,
        (between (findFaceDarts L x) (ytrans L N r x (k - 1))
          (ztrans L N r x (k - 1))).length) := by
    rw [Kepler.Text.Reduction3.lastCoreTriple L N r x (k - 1) hnz (by rw [hk])]
  have hvs : Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)
      = (if v = (ytrans L N r x 0).1 then []
         else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
            (Kepler.Text.Reduction3.coreTripleV4 L N r x)
        ++ (if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
            else (between (core L r) (ztrans L N r x (k - 1)).1
              (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]) := by
    unfold Kepler.Text.Reduction3.destTripleFull
    rw [hhead, hlast]
    rfl
  have hmidtake : (Kepler.Text.Reduction3.coreTripleV4 L N r x).take ((k - 1) + 1)
      = Kepler.Text.Reduction3.coreTripleV4 L N r x := by
    rw [show (k - 1) + 1 = k from by omega, ← hlen0, List.take_length]
  have hClMid : ChainCl (core L r) (UvnsD L N r x k)
      (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)) := by
    have h := (chainClMid L hL hgn hres hm hnf hk (k - 1) (by omega)).1
    rwa [hmidtake] at h
  have hmidlast : (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getLastD none
      = some (ztrans L N r x (k - 1)).1 := by
    have h := (chainClMid L hL hgn hres hm hnf hk (k - 1) (by omega)).2
    rwa [hmidtake] at h
  have hMemMid : MemIn (fun w => w ∈ core L r)
      (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)) := by
    have h := (memMid L hL hgn hres hm hnf hk (k - 1) (by omega)).1
    rwa [hmidtake] at h
  have hmidne : (Kepler.Text.Reduction3.destTriple0 (core L r) []
      (Kepler.Text.Reduction3.coreTripleV4 L N r x)) ≠ [] := by
    intro h
    rw [h] at hmidlast
    simp at hmidlast
  have hClInit := chainClInit L hL hgn hres hm hnf hk hprev
  have hClFinal := chainClFinal L hL hgn hres hm hnf hk hprev
  have hMemInit := memInit L hL hgn hres hm hnf hk v hprev
  have hMemFinal := memFinal L hL hgn hres hm hnf hk v hprev
  have hj1 : ∀ j, j + 1 = (if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).length →
      ((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).getD j none).isSome →
      ((Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD 0 none).isSome →
      nextEl (core L r) (((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).getD j none).getD 0)
        = ((Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD 0 none).getD 0 ∨
      UvnsD L N r x k (((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).getD j none).getD 0)
        (((Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD 0 none).getD 0) := by
    intro j hj _ _
    have hmid0 : (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD 0 none = some (ytrans L N r x 0).1 :=
      getDMidZero L hL hgn hres hm hnf hk
    rw [hmid0]
    by_cases hv0 : v = (ytrans L N r x 0).1
    · rw [if_pos hv0] at hj
      simp at hj
    · rw [if_neg hv0] at hj ⊢
      by_cases harc : (between (core L r) v (ytrans L N r x 0).1) = []
      · rw [harc] at hj ⊢
        have hj0 : j = 0 := by
          have h1 : j + 1 = 1 := by simpa using hj
          omega
        left
        rw [hj0, getDSnocZero]
        exact Kepler.Text.TameSpine.aq10_betwnEqNil harc hvcore hy0 hv0 hrnd
      · left
        have hlenj : ([some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).length
            = (between (core L r) v (ytrans L N r x 0).1).length + 1 := by simp
        have hje : j = (between (core L r) v (ytrans L N r x 0).1).length := by omega
        have hval : (([some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).getD j none).getD 0
            = (between (core L r) v (ytrans L N r x 0).1).getLast harc := by
          rw [hje]
          have hp : 0 < (between (core L r) v (ytrans L N r x 0).1).length :=
            List.length_pos_of_ne_nil harc
          rw [show (between (core L r) v (ytrans L N r x 0).1).length
              = ((between (core L r) v (ytrans L N r x 0).1).length - 1) + 1 from by omega,
            getDSnocSucc, uvnsGetDMapSome (by omega)]
          rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (by omega) 0, ← List.getLast_eq_getElem]
          rfl
        rw [hval]
        exact Kepler.Text.Reduction5.nextLastBetwn hvcore hy0 hrnd hv0 harc
  have hIMlast : ∀ j, j + 1 = ((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length →
      (((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD j none).isSome →
      (((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD j none).getD 0
        = (ztrans L N r x (k - 1)).1 := by
    intro j hj _
    have hlenj : j + 1 = (if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).length
        + (Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length := by
      have := hj; rwa [List.length_append] at this
    have hmidpos : 0 < (Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length :=
      List.length_pos_of_ne_nil hmidne
    rw [uvnsGetDAppend (l := if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
      (m := Kepler.Text.Reduction3.destTriple0 (core L r) []
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)) (j := j),
      dif_neg (by omega)]
    rw [show j - (if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some).length
        = (Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length - 1 from by omega]
    rw [uvnsGetDLastD hmidne]
    rw [hmidlast]
    rfl
  have hj2 : ∀ j, j + 1 = ((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length →
      (((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD j none).isSome →
      ((if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
        else (between (core L r) (ztrans L N r x (k - 1)).1
          (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).getD 0 none).isSome →
      nextEl (core L r) ((((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD j none).getD 0)
        = ((if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
          else (between (core L r) (ztrans L N r x (k - 1)).1
            (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).getD 0 none).getD 0 ∨
      UvnsD L N r x k ((((if v = (ytrans L N r x 0).1 then []
        else [some v] ++ (between (core L r) v (ytrans L N r x 0).1).map some)
        ++ Kepler.Text.Reduction3.destTriple0 (core L r) []
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).getD j none).getD 0)
        (((if (ztrans L N r x (k - 1)).1 = prevEl (core L r) v then []
          else (between (core L r) (ztrans L N r x (k - 1)).1
            (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).getD 0 none).getD 0) := by
    intro j hj hs1 hs2
    have hzval := hIMlast j hj hs1
    rw [hzval]
    by_cases hzf : (ztrans L N r x (k - 1)).1 = prevEl (core L r) v
    · rw [if_pos hzf] at hs2
      simp at hs2
    · rw [if_neg hzf] at hs2 ⊢
      by_cases harc : (between (core L r) (ztrans L N r x (k - 1)).1
          (prevEl (core L r) v)) = []
      · rw [harc] at hs2 ⊢
        have hf0 : ((([] : List ℕ).map some ++ [some (prevEl (core L r) v)]).getD 0 none)
            = some (prevEl (core L r) v) := by simp
        rw [hf0]
        left
        exact Kepler.Text.TameSpine.aq10_betwnEqNil harc hzcore hprevcore hzf hrnd
      · left
        have hpos : 0 < (between (core L r) (ztrans L N r x (k - 1)).1
            (prevEl (core L r) v)).length := by
          cases h : (between (core L r) (ztrans L N r x (k - 1)).1
              (prevEl (core L r) v)).length with
          | zero => exact absurd (List.length_eq_zero_iff.mp h) harc
          | succ n => omega
        have hf0 : (((between (core L r) (ztrans L N r x (k - 1)).1
              (prevEl (core L r) v)).map some ++ [some (prevEl (core L r) v)]).getD 0 none).getD 0
            = (between (core L r) (ztrans L N r x (k - 1)).1
              (prevEl (core L r) v)).getD 0 0 := by
          rw [uvnsGetDAppend (l := (between (core L r) (ztrans L N r x (k - 1)).1
              (prevEl (core L r) v)).map some) (m := [some (prevEl (core L r) v)]) (j := 0),
            dif_pos (by simpa using hpos), uvnsGetDMapSome hpos]
          rfl
        rw [hf0]
        rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos 0,
          Kepler.Text.TameSpine.betwnOrbit hzf hrnd hzcore hprevcore hpos]
        simp
  rw [hvs]
  refine ⟨?_, ?_⟩
  · exact chainClAppend (core L r) (UvnsD L N r x k) _ _
      (chainClAppend (core L r) (UvnsD L N r x k) _ _ hClInit hClMid hj1)
      hClFinal hj2
  · exact memInAppend (fun w => w ∈ core L r) _ _
      (memInAppend (fun w => w ∈ core L r) _ _ hMemInit hMemMid) hMemFinal

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.uvnsWalkCons
