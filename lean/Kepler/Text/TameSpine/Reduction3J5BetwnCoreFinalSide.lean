/-
  Kepler.Text.TameSpine.Reduction3J5BetwnCoreFinalSide — tame-corr nb38：J5-6 主件 P1
  （`betwn_corek_z_x` HOL betwn_corek_z_x.hl:535 的**终态侧**）。

  本件是主件分段交付的第一段（P0+P1）。主件结论：
  `betwn (core L (rtrans k)) (FST zk) (FST x) = betwn (core L r) (FST zk) (FST x)`；
  本件交付其中**右端化**一步：
  `betwn (core L (rtrans k)) (FST zk) (FST x)
     = (betwn (find_face L x) zk x).map FST`
  ——把终态 `core` 折回原态面弧的投影，供 P2（原态侧 `parts` 展开）与 P3（收口）拼接。

  路线（P1，与冻结表 §4.2 一致）：
  - `rtrans k` 非空/无重 ← marked at k（`aqiunpp`）+ `uniqFlattenUniq`；
  - `zk ∈ rtrans k` ← **`ztransInSuc`**（`transformCount_not (k-1)` 供非 final），
    替代 `final_assumption_zpre_core_k`，**不消费 `newvertexPrepped`**（nb37 判词）；
  - `core L (rtrans k) = (rtrans k).map FST` ← `coreFinal`（final at k ←
    `finalListTransformCount`）；
  - `betwn (find_face L x) zk x = betwn (rtrans k) zk x` ← `betwnFinalList`；
  - `(betwn (rtrans k) zk x).map FST = betwn ((rtrans k).map FST) zk.1 x.1`
    ← `mapBetwn`（FST 在 `rtrans k` 上单射 ← `(core L (rtrans k)).Nodup` 经
    `coreFinal` 搬回 `(rtrans k).map FST`，再 `uniqImpInj`）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5BetwnFinalList
import Kepler.Text.TameSpine.Reduction3J5CoreFinal
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5Shallow
import Kepler.Text.TameSpine.JcajyduBetwnMap
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart ztrans transformCount core finalList)

/-- **HOL `betwn_corek_z_x`（:535）终态侧（P1）**——主件分段交付第一段。 -/
theorem betwnCoreKZXFinalSide (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    between (core L (Kepler.Text.Reduction5.rtrans L N r x k))
        (ztrans L N r x (k - 1)).1 x.1
      = (between (findFaceDarts L x) (ztrans L N r x (k - 1)) x).map
          (fun d : Dart => d.1) := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  set f : List Dart := findFaceDarts L x with hf
  set zk : Dart := ztrans L N r x (k - 1) with hz
  -- 基本结构件
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hzkx : zk ≠ x := fun h => hne (by rw [h])
  -- 第 k 步状态：marked + final + Nodup
  have hmK : Kepler.Text.ChainLists.markedList L hL
      (Kepler.Text.Reduction5.ntrans L N r x k)
      (Kepler.Text.Reduction5.rtrans L N r x k) x := haq hgn N r x hm k
  have hfinK : finalList L (Kepler.Text.Reduction5.rtrans L N r x k) :=
    Kepler.Text.Reduction5.finalListTransformCount L hL hgn haq hm hk
  have hrknd : (Kepler.Text.Reduction5.rtrans L N r x k).Nodup :=
    (List.nodup_flatten.mp hmK.2.1.1).1 _ hmK.2.2.1
  have hxK : x ∈ Kepler.Text.Reduction5.rtrans L N r x k := hmK.2.2.2.1
  -- `zk ∈ rtrans k`（不经 `newvertexPrepped`）
  have hzkK : zk ∈ Kepler.Text.Reduction5.rtrans L N r x k := by
    rw [hz]
    cases k with
    | zero => exact absurd hk0 (Nat.lt_irrefl 0)
    | succ m =>
      have hnfm : ¬ finalList L (Kepler.Text.Reduction5.rtrans L N r x m) :=
        Kepler.Text.Reduction4.transformCount_not m (by rw [hk]; omega)
      have h := Kepler.Text.Reduction5.ztransInSuc L hL hgn haq m hm
        (f := f) (w := nextEl f x) rfl rfl hnfm
      simpa using h
  -- 终态 core 折成 FST 投影
  have hcoreK : core L (Kepler.Text.Reduction5.rtrans L N r x k)
      = (Kepler.Text.Reduction5.rtrans L N r x k).map (fun d : Dart => d.1) :=
    Kepler.Text.TameSpine.coreFinal L hL hmK hfinK
  have hmapnd : ((Kepler.Text.Reduction5.rtrans L N r x k).map
      (fun d : Dart => d.1)).Nodup := by
    rw [← hcoreK]
    exact Kepler.Text.Reduction4Idx.markedListUniqCore L hL hmK
  have hinj : ∀ u ∈ Kepler.Text.Reduction5.rtrans L N r x k,
      ∀ v ∈ Kepler.Text.Reduction5.rtrans L N r x k,
      (fun d : Dart => d.1) u = (fun d : Dart => d.1) v → u = v :=
    fun u hu v hv huv =>
      Kepler.Text.TameSpine.uniqImpInj (f := fun d : Dart => d.1) hmapnd hu hv huv
  -- 两侧弧相等 + 投影换向
  have hbetF : between f zk x = between (Kepler.Text.Reduction5.rtrans L N r x k) zk x :=
    Kepler.Text.TameSpine.betwnFinalList L hL hrknd hfinK hxK hzkK hxK hzkx hx
  have hmap := Kepler.Text.TameSpine.mapBetwn
    (s := Kepler.Text.Reduction5.rtrans L N r x k) (f := fun d : Dart => d.1)
    hrknd hinj hzkK hxK hzkx
  rw [hcoreK, hbetF]
  exact hmap.symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.betwnCoreKZXFinalSide
