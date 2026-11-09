/-
  Kepler.Text.ChainMarkedQ — J 战役 DEF-FIX「链层参数化定义」
  （章程 `docs/def-fix-charters/chain-params-defs/CHARTER.md` §3.1）：`markedQ`。

  ┌─ 状态：BLOCKED（上游 sorryAx）───────────────────────────────
  │ 本文件落**不依赖上游 sorry 的干净部分**：
  │   ① 链层 Loop 族载体 `loopOfList` / `loopFamilyOfList`（零机器，见 DIFFERS-①）；
  │   ② 桥① `normalListIsNormalFamily`（normal_list → is_normal）；
  │   ③ 桥③ `notFinalList_not_mem_finalLoops`（~final_list → ∉ final_loops）。
  │ 桥② `markedListIsMarked` 与 `markedQ` **已写出并机器验证可编译**，但其
  │ `IsMarked` 第 6 合取（商 hypermap `NodeNondegenerate`）只能经
  │ `TameSpine.markedListIsNodeNondegenerate`（TameList16:1095）取得，而该件
  │ **在案 sorry**（TameList16:1108，注释 "NEEDS：ql 侧 node 非退化支"，
  │ 2-strike 记档于 JcajyduAqTowerBase:41 / JcajyduRed2Trans:36）。
  │ 机器证据：`#print axioms Kepler.Text.TameSpine.markedListMarked` =
  │ `[propext, sorryAx, Classical.choice, Quot.sound]`；同链其余 12 件组件
  │ （markListRestricted/MemFamily/MemLoop/LoopEqFaceMap/EdgeMapFinal/
  │ EmptyFlagged/SFlagged、quotientAllUniq、simpleHypermapList、
  │ quotientListIsoQuotient、isoSimple、goodListNodesQuotient）全为干净标准三。
  │ ⇒ 待 TameList16 该支真证落库后，把交付目录 `logs/blocked_markedq_body.lean`
  │   的两段（桥② + markedQ，共 ~40 行）原样并入本文件即可，零改写。
  └────────────────────────────────────────────────────────────────

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_defs2.hl`）──
  │ tame_defs2.hl:455-456 `l'q` = `hyp'q (hypermap_of_list L)
  │   (loop_family_of_list N) (loop_of_list r) d`（`hyp'q` 见 hypermap.hl:12215）
  │ → markedQ（显式证明参数，同 `hL` 口径）：`Hypermap.hypQ`（Hypermap.lean:10842）
  │   收 `hmark : IsMarked` + `hLnot : ¬ mem finalLoops` 两个证明参。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与 DIFFERS（交编排者知悉）───────────────────────────────
  │ ① `Dart` 是 `abbrev ℕ × ℕ`（Reduction5Base:47），故 `Loop Dart` 与
  │    `Loop (ℕ × ℕ)` 同一类型：链层载体直接取 Spine 名，**零桥**。
  │ ② 三桥经 Spine 既有装配定理转写（TameList7:419 `normalListNormal`、
  │    TameList17:152 `markedListMarked`、TameList16:1119 `finalLoopsListIff`）+
  │    `ChainBridge` 的 `normalList↔NormalListSpine` / `markedList↔MarkedListSpineFull`
  │    / `finalList↔finalListSpine` 折叠。
  │ ③ 额外显式前提（HOL 原文同样携带）：`hgn : GoodListNodesTl L hL`
  │    （`good_list_nodes`）、`hunL : ∀ l ∈ L, l.Nodup`（`all uniq L`；不可由
  │    `GoodList L` 推出——后者只给 `(L.map listPairs).flatten` Nodup，
  │    GoodListDefs:38/:72）、`hs : sList L r x = sListSpine L r x`
  │    （纯 Lean 载体差：`lm` 用 minNum/epsilon vs `lMSpine` 用 minNumSpine/sInf，
  │    ChainBridgeParts:13 记档；是既有桥参数，不是新债）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；不改任何既有陈述。
-/

import Kepler.Text.ChainBridgeParts
import Kepler.Text.TameSpine.TameList17

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainMarkedQ

open Kepler.Graphs (fgraph)
open Kepler.Text (Loop)
open Kepler.Text.Reduction5 (Dart finalList)
open Kepler.Text.ChainLists (normalList markedList sList)
open Kepler.Text.TameSpine (NormalListSpine loopOfListSpine loopFamilyOfListSpine
  normalListNormal finalLoopsListIff sListSpine)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Assembly (GoodList)
open Kepler.Text.ChainBridge (normalList_iff_normalListSpine finalList_iff_finalListSpine)

/-! ## §1 链层 Loop 族载体（HOL `loop_of_list` / `loop_family_of_list`） -/

/-- HOL `loop_of_list`（tame_defs2.hl:149）的链层名。载体与
`TameSpine.loopOfListSpine` 同一（`Dart` = `ℕ × ℕ` 的 abbrev，`Loop` 类型同一）。 -/
noncomputable def loopOfList (r : List Dart) : Loop Dart :=
  loopOfListSpine r

/-- HOL `loop_family_of_list`（tame_defs2.hl:152）：`set_of_list (MAP loop_of_list N)`。 -/
def loopFamilyOfList (N : List (List Dart)) : Set (Loop Dart) :=
  loopFamilyOfListSpine N

/-! ## §2 干净桥（章程 §3.1 的 ①/③） -/

/-- **桥①**：`normal_list L N → is_normal (hypermap_of_list L) (loop_family_of_list N)`
（HOL `normal_list_normal` / `EVNAPDQ`，tame_list.hl:4606 的链层折叠）。
`hgn`/`hres` 与 HOL 同（`good_list_nodes` / `is_restricted`）。 -/
theorem normalListIsNormalFamily (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List Dart)}
    (hres : (hypermapOfList L hL).IsRestricted) (hN : normalList L hL N) :
    (hypermapOfList L hL).IsNormalFamily (loopFamilyOfList N) :=
  normalListNormal hL hgn hres ((normalList_iff_normalListSpine L hL N).mp hN)

/-- **桥③**：`~ final_list L r → loop_of_list r ∉ final_loops …`
（`final_loops_list_iff`（TameList16:1119）+ `final_list` 两形折叠）。 -/
theorem notFinalList_not_mem_finalLoops (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hM : markedList L hL N r x) (hNF : ¬ finalList L r) :
    loopOfList r ∉ (hypermapOfList L hL).finalLoops (loopFamilyOfList N) := by
  intro hmem
  have hn : NormalListSpine hL N := (normalList_iff_normalListSpine L hL N).mp hM.2.1
  have hfin : Kepler.Text.TameSpine.finalListSpine L r :=
    (finalLoopsListIff L hL hM.2.2.1 hn).mp hmem
  exact hNF ((finalList_iff_finalListSpine L r).mpr hfin)

end Kepler.Text.ChainMarkedQ

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.ChainMarkedQ.normalListIsNormalFamily
#print axioms Kepler.Text.ChainMarkedQ.notFinalList_not_mem_finalLoops
