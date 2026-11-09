/-
  Kepler.Text.ChainMarkedQ — J 战役 DEF-FIX「链层参数化定义」
  （章程 `docs/def-fix-charters/chain-params-defs/CHARTER.md` §3.1）：`markedQ`。

  ┌─ 状态：已解锁（上游 sorry 于 `967ebbb5` 真证落库）──────────────
  │ 本文件 5 件全落：
  │   ① 链层 Loop 族载体 `loopOfList` / `loopFamilyOfList`（零机器，DIFFERS-①）；
  │   ② 桥① `normalListIsNormalFamily`（normal_list → is_normal）；
  │   ③ 桥③ `notFinalList_not_mem_finalLoops`（~final_list → ∉ final_loops）；
  │   ④ 桥② `markedListIsMarked`（marked_list → is_marked，§3）；
  │   ⑤ `markedQ`（`l'q` 载体 = `Hypermap.hypQ` 的链层显式证明参数形，§3）。
  │ 原阻塞点 `TameSpine.markedListIsNodeNondegenerate`（TameList16:1095，
  │ body :1108-1109 曾为在案 sorry，2-strike 记档于 JcajyduAqTowerBase:41 /
  │ JcajyduRed2Trans:36）已由 `967ebbb5`（+128 行）真证替换。
  │ 机器证据（本文件编译即执行，尾锚）：
  │   `#print axioms markedListIsMarked` = `[propext, Classical.choice, Quot.sound]`
  │   `#print axioms markedQ`             = `[propext, Classical.choice, Quot.sound]`
  │ 历史对照（2026-11-09 `3d015703` 的 BLOCKED 记档）：
  │   `#print axioms TameSpine.markedListMarked` 曾 = `[propext, sorryAx, …]`。
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
  normalListNormal finalLoopsListIff sListSpine MarkedListSpineFull markedListMarked)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Assembly (GoodList)
open Kepler.Text.ChainBridge (normalList_iff_normalListSpine finalList_iff_finalListSpine
  markedList_iff_markedListSpineFull)

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

/-! ## §3 桥② + `markedQ`（原 BLOCKED 段；`967ebbb5` 解锁后按
`logs/blocked_markedq_body.lean` 的零改写稿并入） -/

/-- **桥②**：`marked_list L N r x → is_marked … (loop_of_list r) x`
（Spine 装配 `TameList17:154 markedListMarked` 经 `MarkedListSpineFull` 桥转写）。
`hs` 是 `sList` 槽（`sFlagList` 合取需要，`ChainBridgeParts:13` 已记档）。 -/
theorem markedListIsMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hM : markedList L hL N r x)
    (hs : sList L r x = sListSpine L r x) :
    ∀ hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfList N),
      (hypermapOfList L hL).IsMarked (loopFamilyOfList N) hnf (loopOfList r) x := by
  intro hnf
  simpa only [loopFamilyOfList, loopOfList] using
    markedListMarked L hL hgn hunL
      ((markedList_iff_markedListSpineFull L hL N r x hs).mp hM) hnf

/-- **HOL `l'q`**（tame_defs2.hl:455-456）的链层载体：
`hyp'q (hypermap_of_list L) (loop_family_of_list N) (loop_of_list r) x`。
HOL 的 Skolem 函数无证明参；Lean `Hypermap.hypQ` 带 `IsMarked`/`¬finalLoops`
两参，故按章程 `chain-params-defs` §3.1 口径由 `marked_list + ~final_list`
（+ `sList` 槽）显式供给。 -/
noncomputable def markedQ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hM : markedList L hL N r x) (hNF : ¬ finalList L r)
    (hs : sList L r x = sListSpine L r x) : ℕ :=
  (hypermapOfList L hL).hypQ
    (markedListIsMarked L hL hgn hunL hM hs
      (normalListIsNormalFamily L hL hgn hM.1 hM.2.1))
    (notFinalList_not_mem_finalLoops L hL hM hNF)

end Kepler.Text.ChainMarkedQ

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.ChainMarkedQ.normalListIsNormalFamily
#print axioms Kepler.Text.ChainMarkedQ.notFinalList_not_mem_finalLoops
#print axioms Kepler.Text.ChainMarkedQ.markedListIsMarked
#print axioms Kepler.Text.ChainMarkedQ.markedQ
