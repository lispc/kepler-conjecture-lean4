/-
  Kepler.Text.Reduction3DefsAssumptionInst — J 战役 D3b 三载体实例化
  + 链世界/Spine 世界列表定义逐点桥（DEF-FIX 章程 §4 后半）。

  ┌─ 归属与范围 ──────────────────────────────────────────────────
  │ ① D3b `assumptionSet3`/`assumptionSetK10` 的三载体参数
  │    （GoodNodesL/IsRestrictedL/Marked）按编排者 2026-11-09 批准配方
  │    实例化（**陈述零改**：只提供转发定义 + 展开引理）：
  │      Marked        = fun L N r x => ∀ hL, ChainLists.markedList L hL N r x
  │      GoodNodesL    = fun L => ∀ hL, TameLp.GoodListNodesTl L hL
  │      IsRestrictedL = fun L => ∀ hL, (TameLp.hypermapOfList L hL).IsRestricted
  │ ② 链世界列表定义族（L1+L2）与 Spine 侧同族的**逐点桥**：能证到哪条
  │    给哪条（编排者授权）。§B 全无条件；§C 两处依赖支记 UNRESOLVED
  │    （见文末）。
  └────────────────────────────────────────────────────────────────

  ┌─ 环安全（机器核实，勘误 j1w1 旧禁令的依据）────────────────────
  │ `Kepler.Text.TameSpine.TameList13` 的 import 闭包（1130 模块）
  │ **不含 `Kepler.Assembly`**——只含非环底座 `Kepler.Assembly.
  │ GoodListDefs`（`TameList1.lean:37` 现为 narrowed import）；
  │ 故本文件（import TameList13 + 链岛）闭包同样 Assembly-free，
  │ 桥件可被链岛/J3 定理层自由引用（`deps` 探针见交付报告）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = Reduction3DefsAssumption（D3b）+ ChainListsL2（L2）+
  │ TameSpine.TameList13（Spine 旗塔/Marked 族）。零 axiom/sorry/
  │ admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsAssumption
import Kepler.Text.ChainListsL2
import Kepler.Text.TameSpine.TameList13

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart)

/-! ## §A D3b 三载体实例化（陈述零改，转发定义 + 展开引理） -/

/-- `marked_list` 载体槽（实例化后形态：ChainLists L2 定义，hL 全称化）。 -/
def MarkedSlot (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : Prop :=
  ∀ hL : GoodList L, Kepler.Text.ChainLists.markedList L hL N r x

/-- `good_list_nodes` 载体槽（TameLp 链侧忠实形，hL 全称化）。 -/
def GoodNodesSlot (L : fgraph ℕ) : Prop :=
  ∀ hL : GoodList L, Kepler.Text.TameLp.GoodListNodesTl L hL

/-- `is_restricted (hypermap_of_list L)` 载体槽（hL 全称化）。 -/
def IsRestrictedSlot (L : fgraph ℕ) : Prop :=
  ∀ hL : GoodList L, (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted

/-- `assumption_set3` 实例化形（D3b def 陈述零改，仅填三槽）。 -/
def assumptionSet3Full : Prop :=
  assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot

/-- `assumption_setK10` 实例化形（同上；全树唯一落点仍为 D3b）。 -/
def assumptionSetK10Full : Prop :=
  assumptionSetK10 GoodNodesSlot IsRestrictedSlot MarkedSlot

@[simp] theorem assumptionSet3Full_unfold :
    assumptionSet3Full = assumptionSet3 GoodNodesSlot IsRestrictedSlot MarkedSlot :=
  rfl

@[simp] theorem assumptionSetK10Full_unfold :
    assumptionSetK10Full = assumptionSetK10 GoodNodesSlot IsRestrictedSlot MarkedSlot :=
  rfl

end Kepler.Text.Reduction3

/-! ## §B 链世界 ↔ Spine 世界逐点桥（无条件）

对每对同源定义给出 `↔`/`=` 桥；差异只在 junk 访问器（`getLastD (0,0)`
↔ `getLast!`、`getD i (0,0)` ↔ `[i]!`，ℕ×ℕ 的 Inhabited 缺省同为
`(0,0)`，两形 defeq 经小引理折算）与 `find_list` 的实现形
（递归 ↔ `find?`）。 -/

namespace Kepler.Text.ChainBridge

open Kepler.Assembly (GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart finalList parts quotientList)
open Kepler.Text.ChainLists

/-- junk 访问器折叠：`List.getLast!` 与 `getLastD (0,0)` 在 `ℕ×ℕ` 上同值
（Inhabited 缺省 = `(0,0)`，定义性）。 -/
theorem getLast!_eq_getLastD (l : List Dart) : l.getLast! = l.getLastD (0, 0) := by
  rw [List.getLast!_eq_getLast?_getD, List.getLastD_eq_getLast?]
  rfl

/-- junk 访问器折叠：`l[i]!` 与 `getD i (0,0)` 同值（同上）。 -/
theorem getElem!_eq_getD (l : List Dart) (i : ℕ) : l[i]! = l.getD i (0, 0) := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

/-- `final_list` 两形同体（都是 `∀ d ∈ r, f_list L d = next_el r d`）。 -/
theorem finalList_iff_finalListSpine (L : fgraph ℕ) (r : List Dart) :
    finalList L r ↔ Kepler.Text.TameSpine.finalListSpine L r :=
  Iff.rfl

/-- `find_list` 两形（递归 ↔ `find?`）等值。 -/
theorem findList_eq_findListSpine (N : List (List Dart)) (d : Dart) :
    findList N d = Kepler.Text.TameSpine.findListSpine N d := by
  induction N with
  | nil => rfl
  | cons h t ih =>
    by_cases hd : d ∈ h <;>
      simp [findList, Kepler.Text.TameSpine.findListSpine, hd, ih]

/-- `f_last` 两形（`getLastD (0,0)` ↔ `getLast!`）。 -/
theorem fLast_iff_fLastSpine (L : fgraph ℕ) (s : List Dart) :
    fLast L s ↔ Kepler.Text.TameSpine.fLastSpine L s := by
  unfold fLast Kepler.Text.TameSpine.fLastSpine
  simp only [getLast!_eq_getLastD]

/-- `one_step_list` 两形同体。 -/
theorem oneStepList_iff_oneStepListSpine (L : fgraph ℕ) (x y : Dart) :
    oneStepList L x y ↔ Kepler.Text.TameSpine.oneStepListSpine L x y :=
  Iff.rfl

/-- `loop_list` 两形。 -/
theorem loopList_iff_loopListSpine (L : fgraph ℕ) (s : List Dart) :
    loopList L s ↔ Kepler.Text.TameSpine.loopListSpine L s := by
  unfold loopList Kepler.Text.TameSpine.loopListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  exact Iff.rfl

/-- `normal_list` 两形（5 合取块逐点对齐；node 合取同用
`hypermapOfList L hL`）。 -/
theorem normalList_iff_normalListSpine (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) :
    normalList L hL N ↔ Kepler.Text.TameSpine.NormalListSpine hL N := by
  unfold normalList Kepler.Text.TameSpine.NormalListSpine fLast
    Kepler.Text.TameSpine.fLastSpine loopList
    Kepler.Text.TameSpine.loopListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  simp only [getLast!_eq_getLastD]

/-- `contour_list` 两形（`EL ↦ getD` ↔ `[i]!`）。 -/
theorem contourList_iff_contourListSpine (L : fgraph ℕ) (s : List Dart) :
    contourList L s ↔ Kepler.Text.TameSpine.ContourListSpine L s := by
  unfold contourList Kepler.Text.TameSpine.ContourListSpine oneStepList
    Kepler.Text.TameSpine.oneStepListSpine
  simp only [getElem!_eq_getD]

/-- `final_dart_list` 两形（filter decide 同体）。 -/
theorem finalDartList_eq_finalDartListSpine (L : fgraph ℕ) (N : List (List Dart)) :
    finalDartList L N = Kepler.Text.TameSpine.FinalDartListSpine L N := by
  classical
  have h : (fun r => decide (finalList L r))
      = (fun r => decide (Kepler.Text.TameSpine.finalListSpine L r)) := by
    funext r
    exact decide_eq_decide.mpr (finalList_iff_finalListSpine L r)
  unfold finalDartList Kepler.Text.TameSpine.FinalDartListSpine
  rw [h]

end Kepler.Text.ChainBridge

-- 探针（编译即执行）
#check @Kepler.Text.Reduction3.assumptionSet3Full
#check @Kepler.Text.Reduction3.assumptionSetK10Full
#check @Kepler.Text.Reduction3.MarkedSlot
#print axioms Kepler.Text.Reduction3.assumptionSet3Full_unfold
#print axioms Kepler.Text.ChainBridge.findList_eq_findListSpine
#print axioms Kepler.Text.ChainBridge.normalList_iff_normalListSpine
#print axioms Kepler.Text.ChainBridge.contourList_iff_contourListSpine
#print axioms Kepler.Text.ChainBridge.finalDartList_eq_finalDartListSpine
