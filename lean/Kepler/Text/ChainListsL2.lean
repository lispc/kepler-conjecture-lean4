/-
  Kepler.Text.ChainLists — DEF-FIX「链世界列表定义族」L2 步：
  `flagList` / `sFlagList` / `markedList`（9 合取块）。
  承接 L1（`Kepler.Text.ChainListsL1`：oneStepList/fLast/loopList/
  normalList/findList，落库 220b7b20）。

  ┌─ 章程与范围（docs/def-fix-charters/chain-list-defs/CHARTER.md §4）──
  │ 本项**只落定义**，不证 marked_list 的 9 合取性质（证明归 J3 定理层）；
  │ 零陈述改动、不动 Spine 双家；DF_SORRY_NET = 0。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐件 HOL 锚（reference/flyspeck/text_formalization/tame/）──────
  │   final_dart_list  tame_defs2.hl:146-147 → finalDartList（辅助①）
  │   contour_list     tame_defs2.hl:88-91   → contourList（辅助②）
  │   s_list           tame_defs2.hl:491-493 → sList（辅助③）
  │   s_flag_list      tame_defs2.hl:495-510 → sFlagList
  │   flag_list        tame_defs2.hl:512-526 → flagList
  │   marked_list      tame_defs2.hl:550-564 → markedList（9 合取块逐字）
  │ 辅助定义数 = 3（= 章程门槛，未超）；复用 L1 五件与 Reduction5Base 的
  │ parts/lm/quotientList/finalList。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与 DIFFERS（交编排者知悉；与 L1/批准口径一致）─────────────
  │ ① `marked_list` 的 `is_restricted (hypermap_of_list L)` 与
  │    `normal_list` 的 node 合取均需树内 `hypermapOfList L
  │    (hL : GoodList L)`（TameLp.lean:5188，吃 `Nodup`），故
  │    `markedList` 取显式参数 `(hL : GoodList L)`——编排者 2026-11-09
  │    已批准同形适配（章程澄清：不得复用 Spine 的 BEq 实例 ≠ 不许显式
  │    参数）。
  │ ② `LAST/HD` junk：`y = LAST p` ↦ `p.getLastD (0,0)`、`HD s` ↦
  │    `s.headD (0,0)`（s ≠ [] 前提使非空支忠实；junk 支两库同为任意）。
  │ ③ `EL i s` ↦ `s.getD i (0,0)`（`SUC i < sizel s` 守卫下在界）。
  │ ④ `cat`/`flatten`/`filter`/`iota` 折算同前批；`sizel (filter (MEM v)
  │    qs) > 1` ↦ `1 < (qs.filter (fun q => decide (v ∈ q))).length`。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ imports = `Kepler.Text.ChainListsL1`。闭包零 Kepler.Assembly 主模块、
  │ 零 TameSpine。zero axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.ChainListsL1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainLists

open Kepler.Assembly (GoodList nextEl eList fList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart finalList lm parts quotientList)
open Kepler.Text.TameLp (hypermapOfList)

/-! ## §A 辅助件（tame_defs2.hl:88-91 / :146-147 / :491-493）

`final_dart_list L N`：`N` 的终面之展平。`contour_list L s`：`s` 的每
元素是 dart、相邻对满足一步关系。`s_list L r d`：从 `d` 出发的
`f_list` 迭代 1..`l'm L r d` 次。 -/

/-- HOL `final_dart_list`（tame_defs2.hl:146-147）：
`flatten (filter (final_list L) N)`。 -/
def finalDartList (L : fgraph ℕ) (N : List (List Dart)) : List Dart :=
  (N.filter (fun r => decide (finalList L r))).flatten

/-- HOL `contour_list`（tame_defs2.hl:88-91）：dart 成员 + 相邻一步关系
（`EL` ↦ `getD`，`SUC i < sizel s` 守卫下在界）。 -/
def contourList (L : fgraph ℕ) (s : List Dart) : Prop :=
  (∀ x ∈ s, x ∈ listOfDarts L) ∧
  (∀ i, i + 1 < s.length →
    oneStepList L (s.getD i (0, 0)) (s.getD (i + 1) (0, 0)))

/-- HOL `s_list`（tame_defs2.hl:491-493）：
`MAP (\i. (f_list L POWER i) d) (iota 1 (l'm L r d))`。 -/
noncomputable def sList (L : fgraph ℕ) (r : List Dart) (d : Dart) : List Dart :=
  (List.range' 1 (lm L r d)).map (fun i => (fList L)^[i] d)

/-! ## §B `flag_list` / `s_flag_list`（tame_defs2.hl:512-526 / :495-510）

两件共首合取：终面 dart 两两之间都存在非空 contour 连通段，且段集
落在终面 dart 集内。第二合取：非终面 `r'` 的 parts 末端 `y` 的 `e_list`
落在终面 dart 表（`flag_list`）或 `s_list ++ 终面 dart 表`
（`s_flag_list`，另加 `y ∉ s_list L r x` 前提）。 -/

/-- HOL `flag_list`（tame_defs2.hl:512-526）。 -/
def flagList (L : fgraph ℕ) (N : List (List Dart)) : Prop :=
  (∀ u v, u ∈ finalDartList L N → v ∈ finalDartList L N →
    ∃ s, contourList L s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
      s.getLastD (0, 0) = v ∧
      {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L N}) ∧
  (∀ (r' : List Dart) (p : List Dart) (y : Dart),
    y = p.getLastD (0, 0) → p ∈ parts L r' → r' ∈ N → ¬ finalList L r' →
    eList y ∈ finalDartList L N)

/-- HOL `s_flag_list`（tame_defs2.hl:495-510）。 -/
noncomputable def sFlagList (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) : Prop :=
  (∀ u v, u ∈ finalDartList L N → v ∈ finalDartList L N →
    ∃ s, contourList L s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
      s.getLastD (0, 0) = v ∧
      {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L N}) ∧
  (∀ (r' : List Dart) (p : List Dart) (y : Dart),
    y = p.getLastD (0, 0) → p ∈ parts L r' → r' ∈ N → ¬ finalList L r' →
    y ∉ sList L r x →
    eList y ∈ sList L r x ++ finalDartList L N)

/-! ## §C `marked_list`（tame_defs2.hl:550-564，9 合取块逐字）

1. `is_restricted (hypermap_of_list L)`；2. `normal_list L N`；
3. `r ∈ N`；4. `x ∈ r`；5. quotient_list 各面 simple（uniq）且顶点
非退化（每个顶点在 flatten 中出现 >1 次）；6. `next_el r x = f_list L x`；
7. `find_list N (e_list x)` 是终面；8/9. flag 双分支。 -/

/-- HOL `marked_list`（tame_defs2.hl:550-564）。`hL : GoodList L` 为载体
前提（DIFFERS-①，与 normalList/GoodListNodesTl 同形）。 -/
noncomputable def markedList (L : fgraph ℕ) (hL : GoodList L)
    (N : List (List Dart)) (r : List Dart) (x : Dart) : Prop :=
  (hypermapOfList L hL).IsRestricted ∧
  normalList L hL N ∧
  r ∈ N ∧
  x ∈ r ∧
  (let qs := quotientList L N;
   (∀ s ∈ qs, s.Nodup) ∧
   (∀ v ∈ qs.flatten,
     1 < (qs.filter (fun q => decide (v ∈ q))).length)) ∧
  nextEl r x = fList L x ∧
  (let r' := findList N (eList x); finalList L r') ∧
  (finalList L r → flagList L N) ∧
  (¬ finalList L r → sFlagList L N r x)

end Kepler.Text.ChainLists

-- 探针（编译即执行）：签名打印 + 公理
#check @Kepler.Text.ChainLists.finalDartList
#check @Kepler.Text.ChainLists.contourList
#check @Kepler.Text.ChainLists.sList
#check @Kepler.Text.ChainLists.flagList
#check @Kepler.Text.ChainLists.sFlagList
#check @Kepler.Text.ChainLists.markedList
