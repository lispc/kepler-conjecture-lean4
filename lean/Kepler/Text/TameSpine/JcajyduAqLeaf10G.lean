/-
  JcajyduAqLeaf10G — AQ10-b2：`theorem aq10` 总装（AQ10 叶收口）。
  终态支 / x=y 的 hgoalY wrapper（S 空·非空）/ x≠y 走 b1 前缀引理 / calc 桥回。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf10F
import Kepler.Text.TameSpine.JcajyduAqLeaf10D
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList71
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl fList findFaceDarts listOfDarts GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **AQ10 主证**（AQ10.hl:102-206）：`next_el (rtrans L N r x 1) x = f_list L x`。 -/
theorem aq10 (L : fgraph ℕ) (hL : GoodList L) : aq10Concl L hL := by
  intro N r x hgn hm
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  by_cases hf : finalListSpine L r
  · have hr1 : rtransSpine L N r x 1 = r := by
      show (Kepler.Text.TameSpine.transformListSpine L x (N, r)).2 = r
      rw [Kepler.Text.TameSpine.transformListFinalListId L x N r hf]
    rw [hr1]
    exact hnext
  · have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    have hnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
    have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
    have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
    have hyz : lYSpine L r x ≠ lZSpine L N r x := hyneSupply L hL hgn hunL hm hf
    have hzy : lZSpine L N r x ≠ lYSpine L r x := hyz.symm
    have hfaceY : lYSpine L r x ∈ findFaceDarts L x := (pplhuljV0 L hL hgn hunL hm hf).1
    have hfaceZ : lZSpine L N r x ∈ findFaceDarts L x := (pplhuljV0 L hL hgn hunL hm hf).2.1
    have hfnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
    have hfaceEq : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 hfaceY
    have hsplit := aq10_rtransOneEqSplit L hL hgn hm hf
    have hxP : x ∈ [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
        [lYSpine L r x] := by
      have h := aq10_pointRemarkMemSplit L hL hgn hm hf
      rwa [← List.append_assoc] at h
    have hPnd : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
        [lYSpine L r x]).Nodup := uniqAppendBetwn hnd hz hy hzy
    have hPlast : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
        [lYSpine L r x]).getLast! = lYSpine L r x := aq10_PLast r _ _
    have hPne : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
        [lYSpine L r x]) ≠ [] := by
      intro hc
      have hlen := congrArg List.length hc
      simp [List.length_append] at hlen
    have hPlen : 0 < ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]).length := List.length_pos_of_ne_nil hPne
    have hyP : lYSpine L r x ∈ [lZSpine L N r x] ++
        between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x] :=
      List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    have hidxP : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
        [lYSpine L r x]).idxOf (lYSpine L r x) =
        ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
          [lYSpine L r x]).length - 1 :=
      (congrArg (fun t => List.idxOf t
        ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
          [lYSpine L r x])) hPlast.symm).trans (idxOfGetLast hPnd hPne)
    have hfl : fList L (lYSpine L r x)
        = nextEl (findFaceDarts L x) (lYSpine L r x) := by
      show nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) = _
      rw [hfaceEq]
    rw [hsplit]
    by_cases hxy : x = lYSpine L r x
    · -- x = y：hgoalY wrapper + 两次 congrArg
      have hgoalY : nextEl
          (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
            [lYSpine L r x]) ++ between (findFaceDarts L x) (lYSpine L r x)
              (lZSpine L N r x)) (lYSpine L r x) = fList L (lYSpine L r x) := by
        by_cases hS : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) = []
        · rw [hS, List.append_nil]
          have hb := (betwnNil hfnd hyz hfaceY hfaceZ).mp hS
          rw [hfl, ← hb]
          unfold Kepler.Assembly.nextEl
          rw [hidxP]
          rw [if_pos rfl]
          show (lZSpine L N r x :: (between r (lZSpine L N r x) (lYSpine L r x) ++
            [lYSpine L r x])).headD (lYSpine L r x) = lZSpine L N r x
          rfl
        · have hyS : lYSpine L r x ∉ between (findFaceDarts L x) (lYSpine L r x)
              (lZSpine L N r x) := notBetwn1 hfnd hfaceZ
          have hidxPS : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
              (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L x)
                (lYSpine L r x) (lZSpine L N r x)).idxOf (lYSpine L r x) =
              ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
                [lYSpine L r x]).length - 1 := by
            rw [List.idxOf_append_of_mem hyP, hidxP]
          unfold Kepler.Assembly.nextEl
          rw [hidxPS]
          rw [if_neg (by
            intro hc
            have hlen : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
                (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L x)
                  (lYSpine L r x) (lZSpine L N r x)).length =
                ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
                  [lYSpine L r x]).length +
                (between (findFaceDarts L x) (lYSpine L r x)
                  (lZSpine L N r x)).length := List.length_append
            have hpos : 0 < (between (findFaceDarts L x) (lYSpine L r x)
                (lZSpine L N r x)).length := List.length_pos_of_ne_nil hS
            omega)]
          rw [show ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
              [lYSpine L r x]).length - 1 + 1 =
              ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
                [lYSpine L r x]).length from by omega]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append]
          simp only [if_neg (by omega : ¬([lZSpine L N r x] ++
            between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]).length <
              ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
                [lYSpine L r x]).length), Nat.sub_self]
          rw [← List.getD_eq_getElem?_getD]
          rw [show (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).getD 0
              (lYSpine L r x) =
              (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).head! from by
            cases hEq : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) with
            | nil => exact absurd hEq hS
            | cons a t => rfl]
          rw [show (between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)).head! =
              nextEl (findFaceDarts L x) (lYSpine L r x) from
            HD_BETWN2 hfaceY hfaceZ hyz hfnd hS]
          rw [← hfl]
      calc nextEl
            (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
              [lYSpine L r x]) ++ between (findFaceDarts L x) (lYSpine L r x)
                (lZSpine L N r x)) x
          = nextEl
            (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
              [lYSpine L r x]) ++ between (findFaceDarts L x) (lYSpine L r x)
                (lZSpine L N r x)) (lYSpine L r x) := congrArg _ hxy
        _ = fList L (lYSpine L r x) := hgoalY
        _ = fList L x := congrArg (fList L) hxy.symm
    · -- x ≠ y：nextElCat1 + b1 前缀引理
      have hxne : x ≠ ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x) ++
          [lYSpine L r x]).getLast! := by
        rw [hPlast]
        exact hxy
      rw [nextElCat1 hPnd hxP hxne]
      exact (aq10_nextElPrefix r hnd hz hy hzy hxP hxy).trans hnext

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10
