/-
  Kepler.Text.TameSpine.Reduction3J5BetwnCorekZX — tame-corr nb42：J5-6 主件收口
  （`betwn_corek_z_x` HOL betwn_corek_z_x.hl:535）。

  本件用 nb38（终态侧 P1）+ nb41（原态侧 P2 装配件）+ 子论证 A/B（nb40/nb42），
  两行 `trans` 收口主等式：
  `betwn (core L (rtrans k)) (FST zk) (FST x)
   = betwn (core L r) (FST zk) (FST x)`。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5BetwnCoreFinalSide
import Kepler.Text.TameSpine.Reduction3J5BetwnCoreInitOfLastHead
import Kepler.Text.TameSpine.Reduction3J5PartOfZkLast
import Kepler.Text.TameSpine.Reduction3J5PartOfXHead
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList)
open Kepler.Text.Reduction5 (Dart ztrans transformCount core rtrans parts)

/-- **HOL `betwn_corek_z_x`**（betwn_corek_z_x.hl:535）：终态 core 与原态 core 的
`between` 在 `FST zk` / `FST x` 处相等。 -/
theorem betwnCorekZX (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hk : transformCount L N r x = k) (hk0 : 0 < k)
    (hne : (ztrans L N r x (k - 1)).1 ≠ x.1) :
    between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1
      = between (core L r) (ztrans L N r x (k - 1)).1 x.1 := by
  set zk : Dart := ztrans L N r x (k - 1) with hz
  -- 子论证 A/B 所需的 atom 存在性与结构件
  have hxr : x ∈ r := hm.2.2.2.1
  have hzkr : zk ∈ r := by
    rw [hz]
    exact Kepler.Text.Reduction5.pnxvwfs2 L hL hgn
      (fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i)
      (k - 1) (Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)) hm
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  obtain ⟨px, hpx, hxpx⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hxr
  obtain ⟨py, hpy, hzkpy⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hzkr
  -- 子论证 A：zk 是其 atom 的末元
  have hlast : py.getLast! = zk :=
    Kepler.Text.TameSpine.partOfZkGetLast L hL hgn hres hm hk hk0 hne hpy hzkpy
  -- 子论证 B：x 是其 atom 的头元
  have hhead : px.head! = x :=
    Kepler.Text.TameSpine.partOfXHead L hL hgn hres hm hk hk0 hne hpx hxpx
  -- P1：终态侧 = 面弧投影
  have hfinal : between (core L (rtrans L N r x k)) zk.1 x.1
      = (between (Kepler.Assembly.findFaceDarts L x) zk x).map (fun d => d.1) :=
    Kepler.Text.TameSpine.betwnCoreKZXFinalSide L hL hgn hres hm hk hk0 hne
  -- P2：原态侧 = 同一面弧投影（条件于 A/B）
  have hinit : between (core L r) zk.1 x.1
      = (between (Kepler.Assembly.findFaceDarts L x) zk x).map (fun d => d.1) :=
    Kepler.Text.TameSpine.betwnCoreInitOfLastHead L hL hgn hres hm hk hk0 hne
      hpy hpx hzkpy hxpx hlast hhead
  -- 两行 trans 收口
  rw [hinit] at *
  exact hfinal

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.betwnCorekZX
