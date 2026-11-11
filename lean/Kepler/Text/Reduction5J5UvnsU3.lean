/-
  Kepler.Text.Reduction5J5UvnsU3 — U3（U 段倒数第二件）：`k3UvnsMainSlot` 的
  **pairs 合取**（`k3UvnsSlot` 第二合取逐字）。

  路线：`uvnsWalkCons` 的 Cl 分类二分——
  ① `nextEl (core)` 相邻 ⇒ `memListPairsCoreOfNextEl`（SxC，ac8c6f7b）直接给
     `∈ listPairs (core L r)`（`u ∈ core` 由 `uvnsWalkCons` 的 mem 半）；
  ② `(y_t, z_t)` 且 `|betwn (find_face) y_t z_t| = 0` ⇒ 由 `hnNil` 撞
     `d ∈ listOfDarts (quotientList)`（`|betwn| = 0` 转 `betwn = []` 用
     `List.length_eq_zero_iff`）。
  `d ∈ listOfDarts` 在 ① 支不消费（Cl 已内含邻接）。

  纪律：零公理、零占位证明；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5UvnsFinal
import Kepler.Text.Reduction5J5SxC

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-- **UVNS pairs 支**（`k3UvnsMainSlot` 第二合取逐字）：相邻 Some 项若为 quotient
dart，则必是 `core L r` 的 listPairs 成员。 -/
theorem uvnsPairsOfWalk
    (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x)
    (hnf : ¬ finalList L r) (hk : transformCount L N r x = k)
    (hnNil : ∀ i : ℕ, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉
          listOfDarts (quotientList L N))
    {v : ℕ} (hprev : (prevEl (core L r) v, v) = x) :
    let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v
        (Kepler.Text.Reduction3.coreTripleV4 L N r x)
    ∀ i, (let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
      ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
        i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
      d ∈ listPairs (core L r)) := by
  intro vs i
  dsimp only
  intro h4
  obtain ⟨hs1, hs2, hlt, hd⟩ := h4
  have hlt' : i + 1 < (Kepler.Text.Reduction3.destTripleFull (core L r) v
      (Kepler.Text.Reduction3.coreTripleV4 L N r x)).length := hlt
  have hwalk := uvnsWalkCons L hL hgn hres hm hnf hk hprev
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hcu : (core L r).Nodup := Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  rcases hwalk.1 i hlt hs1 hs2 with hnext | ⟨t, htk, ha, hb, hlen⟩
  · exact memListPairsCoreOfNextEl L hL hgn hunL hnedg hm.2.1 hm.2.2.1 hcu
      (hwalk.2 i (by omega) hs1) hnext
  · exfalso
    apply hnNil t htk (List.length_eq_zero_iff.mp hlen)
    rw [← ha, ← hb]
    exact hd

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.uvnsPairsOfWalk
