/-
  Kepler.Text.TameSpine.Reduction3J5BetwnCoreInitOfLastHead — tame-corr nb41：主件 P2 装配件
  （`betwn_corek_z_x` HOL :535 原态侧，条件于 A/B 两条子论证）。

  本件交付 P2 的**装配层**：在子论证 A（`py.getLast! = zk`，已在库
  `partOfZkGetLast`）与子论证 B（`px.head! = x`）成立的前提下，
  证 `between (core L r) zk.1 x.1 = (between f zk x).map FST`。

  与 nb38 `betwnCoreKZXFinalSide` 合起来，主件只剩 B 一处数学子论证。
  主件陈述零改、无 SF。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5CorePartsWiring
import Kepler.Text.TameSpine.Reduction3J5PartOfZkLast
import Kepler.Text.TameSpine.Reduction3J5BetwnFinalList
import Kepler.Text.TameSpine.Reduction3J5PartsBetwnFinal
import Kepler.Text.TameSpine.Reduction3J5BetwnPreFace
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5Shallow
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans transformCount core parts)

/-- **主件 P2 装配件**（条件于子论证 A/B）：原态侧等式。 -/
theorem betwnCoreInitOfLastHead (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1)
    {py px : List Dart} (hpy : py ∈ parts L r) (hpx : px ∈ parts L r)
    (hzkpy : ztrans L N r x (k - 1) ∈ py) (hxpx : x ∈ px)
    (hlast : py.getLast! = ztrans L N r x (k - 1))
    (hhead : px.head! = x) :
    between (core L r) (ztrans L N r x (k - 1)).1 x.1
      = (between (findFaceDarts L x) (ztrans L N r x (k - 1)) x).map
          (fun d : Dart => d.1) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  set zk : Dart := ztrans L N r x (k - 1) with hz
  have hzkx : zk ≠ x := fun h => hne (by rw [h])
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  -- 第 k 步（final）结构件
  have hmK : Kepler.Text.ChainLists.markedList L hL
      (Kepler.Text.Reduction5.ntrans L N r x k)
      (Kepler.Text.Reduction5.rtrans L N r x k) x := haq hgn N r x hm k
  have hfinK : Kepler.Text.Reduction5.finalList L
      (Kepler.Text.Reduction5.rtrans L N r x k) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm hk
  have hrknd : (Kepler.Text.Reduction5.rtrans L N r x k).Nodup :=
    (List.nodup_flatten.mp hmK.2.1.1).1 _ hmK.2.2.1
  have hxK : x ∈ Kepler.Text.Reduction5.rtrans L N r x k := hmK.2.2.2.1
  have hzkK : zk ∈ Kepler.Text.Reduction5.rtrans L N r x k := by
    rw [hz]
    cases k with
    | zero => exact absurd hk0 (Nat.lt_irrefl 0)
    | succ m =>
      have hnfm : ¬ Kepler.Text.Reduction5.finalList L
          (Kepler.Text.Reduction5.rtrans L N r x m) :=
        Kepler.Text.Reduction4.transformCount_not m (by rw [hk]; omega)
      have h := Kepler.Text.Reduction5.ztransInSuc L hL hgn haq m hm
        (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl hnfm
      simpa using h
  have hall : ∀ d ∈ Kepler.Text.Reduction5.rtrans L N r x k, d ∈ listOfDarts L :=
    fun d hd => (hmK.2.1.2.2.2.1 _ hmK.2.2.1 d hd).1
  -- 终态侧：between f = between rk = between r
  have hbetK : between (findFaceDarts L x) zk x
      = between (Kepler.Text.Reduction5.rtrans L N r x k) zk x :=
    Kepler.Text.TameSpine.betwnFinalList L hL hrknd hfinK hxK hzkK hxK hzkx hxd
  have hbetR : between (Kepler.Text.Reduction5.rtrans L N r x k) zk x
      = between r zk x :=
    hbetK.symm.trans
      (Kepler.Text.TameSpine.betwnPreFace L hL hgn hres hm hk hk0 hne)
  -- 终态 parts 单点化
  have hparts := Kepler.Text.TameSpine.partsBetwnFinal L hL hall
    hres.edgeNondegenerate hrknd hfinK hzkK hxK hzkx
  -- 原态侧（条件于 A/B）
  have h1 := Kepler.Text.TameSpine.coreBetwnPartsBetwnEq L hL hres hm hne hpy hpx hzkpy hxpx
  rw [hlast, hhead] at h1
  -- 投影链
  have h2 : (parts L (between r zk x)).map (fun q : List Dart => q.head!.1)
      = (between (findFaceDarts L x) zk x).map (fun d : Dart => d.1) := by
    rw [← hbetR, hparts, List.map_map]
    rw [← hbetK]
    exact List.map_congr_left (fun d _ => rfl)
  rw [h1]
  exact h2

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.betwnCoreInitOfLastHead
