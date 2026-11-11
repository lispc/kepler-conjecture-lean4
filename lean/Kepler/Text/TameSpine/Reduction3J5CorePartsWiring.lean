/-
  Kepler.Text.TameSpine.Reduction3J5CorePartsWiring — tame-corr nb39：J5-6 主件 P2 段 1/4/5
  （`betwn_corek_z_x` HOL betwn_corek_z_x.hl:535 原态侧的 **parts 接线**）。

  本件交付主件 P2 的机械接线层（不含两处数学子论证）：

  1. `coreEqPartsHeadFst`：`core L r = (parts L r).map head!` 的 `headD ↔ head!` 折算
     （`core` 定义用 `headD (0,0)`，`parts` 项非空由 `partsAllNonnil` 保证）；
  2. `coreBetwnPartsEq`：**P2 段 4**——`between (core L r) y z`
     `= (between (parts L r) py pz).map head!`（`aqs_fstHdMapBetwn` 实例化；
     FST 单射 ← `core` 的 Nodup，`parts`/`partsSpine` 同体经 `rfl` 桥，
     `NormalListSpine` ← marked_list 经 `ChainBridge.normalList_iff_normalListSpine`）；
  3. `coreBetwnPartsBetwnEq`：**P2 段 5**——再把 `(between parts)` 换成
     `parts L (between r py.getLast! pz.head!)`（`partsBetwn`）。

  剩余数学子论证（下一轮）：`LAST py = zk` 与 `px.head! = x`（HOL 的 GSUBGOAL 段），
  之后主件 P2 只剩把本件两等式与 `betwnPreFace`/`betwnFinalList`/`partsBetwnFinal`
  串起来。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3CoreSplitNormal
import Kepler.Text.Reduction5Ml1Leaves
import Kepler.Text.TameSpine.JcajyduAqLeaf12B
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList fList eList)
open Kepler.Text.Reduction5 (Dart parts core)

/-- 非空表 `headD (0,0)` = `head!`（private；`Reduction5McCore:30` 同款）。 -/
private theorem headD_eq_headBang {l : List Dart} (hne : l ≠ []) :
    l.headD (0, 0) = l.head! := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- **`core` 的 `head!` 形**：`core L r = (parts L r).map (fun q => q.head!.1)`。 -/
theorem coreEqPartsHeadFst (L : fgraph ℕ) (r : List Dart) :
    core L r = (parts L r).map (fun q : List Dart => q.head!.1) := by
  show (parts L r).map (fun q : List Dart => (q.headD (0, 0)).1) = _
  refine List.map_congr_left ?_
  intro q hq
  have hqne : q ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r q hq
  exact congrArg Prod.fst (headD_eq_headBang hqne)

/-- **P2 段 4**：`between (core L r) y z = (between (parts L r) py pz).map head!`。 -/
theorem coreBetwnPartsEq (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x y z : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hyz : y.1 ≠ z.1)
    {py pz : List Dart} (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hy : y ∈ py) (hz : z ∈ pz) :
    between (core L r) y.1 z.1
      = (between (parts L r) py pz).map (fun q : List Dart => q.head!.1) := by
  have hcoreEq : core L r = (parts L r).map (fun q : List Dart => q.head!.1) :=
    coreEqPartsHeadFst L r
  have huniq : ((parts L r).map (fun q : List Dart => q.head!.1)).Nodup := by
    rw [← hcoreEq]
    exact Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hnSp : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
  have h := Kepler.Text.TameSpine.aqs_fstHdMapBetwn L hL hnSp hm.2.2.1
    (sp := parts L r) (Kepler.Text.ChainBridge.parts_eq_partsSpine L r).symm
    huniq hpy hpz hy hz hyz
  rw [hcoreEq]
  exact h.symm

/-- **P2 段 5**：再经 `partsBetwn` 换成 `parts L (between r py.getLast! pz.head!)`。 -/
theorem coreBetwnPartsBetwnEq (L : fgraph ℕ) (hL : GoodList L)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x y z : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hyz : y.1 ≠ z.1)
    {py pz : List Dart} (hpy : py ∈ parts L r) (hpz : pz ∈ parts L r)
    (hy : y ∈ py) (hz : z ∈ pz) :
    between (core L r) y.1 z.1
      = (parts L (between r py.getLast! pz.head!)).map
          (fun q : List Dart => q.head!.1) := by
  have hcoreEq : core L r = (parts L r).map (fun q : List Dart => q.head!.1) :=
    coreEqPartsHeadFst L r
  have huniq : ((parts L r).map (fun q : List Dart => q.head!.1)).Nodup := by
    rw [← hcoreEq]
    exact Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hnSp : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hm.2.1
  have hpb : parts L (between r py.getLast! pz.head!)
      = between (parts L r) py pz :=
    Kepler.Text.Reduction5.partsBetwnChain L hL hm.2.1 hres.edgeNondegenerate
      hm.2.2.1 rfl huniq hpy hpz hy hz hyz
  rw [hpb]
  exact coreBetwnPartsEq L hL hm hyz hpy hpz hy hz

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.coreEqPartsHeadFst
#print axioms Kepler.Text.TameSpine.coreBetwnPartsEq
#print axioms Kepler.Text.TameSpine.coreBetwnPartsBetwnEq
