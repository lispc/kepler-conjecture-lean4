/-
  Kepler.Text.TameSpine.TameList26 — B1 Tame_list 地基批 26：normal_list 章收口
  （tamespine-port-plan §4 批次表 B1 行；接续批 25 = TameList24.lean→TameList25.lean，
  批 25 终点 = HOL :10830（rev2 已落）；本批起点 = HOL :10832
  `is_normal_loop_list`。行号勘误：任务面所给 :10829 起/:10876 一带为 AFP 版
  参考行号，主仓 reference/flyspeck（commit 1ce0353）实测 +3/+14 偏移——
  is_normal_loop_list 实为 :10832、is_normal_nodal 实为 :10890，本批锚点全按
  主仓记档）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10832-:10929）——normal_list 章两件
  全落，本批零止损：

  主件 1：`is_normal_loop_list` :10832-:10888
  `!L N. is_restricted (hypermap_of_list L) /\ good_list L /\
  good_list_nodes L /\ all (\r. ~(r=[])) N /\ all uniq N /\
  is_normal (hypermap_of_list L) (loop_family_of_list N) ==>
  all (loop_list L) N`。

  主件 2：`is_normal_nodal` :10890-:10929
  `!L N. is_restricted (hypermap_of_list L) /\ good_list L /\
  good_list_nodes L /\ is_normal (hypermap_of_list L)
  (loop_family_of_list N) /\ all (\r. ~(r=[])) N /\ all uniq N ==>
  (!d. MEM d (flatten N) ==> node (hypermap_of_list L) d SUBSET
  set_of_list (flatten N))`。

  定义面侦察定论（本批零新落 def——全部载体在库，逐槽记档）：
  · `loop_list`（tame_defs2.hl:84-86）↦ 批 5 `loopListSpine`
    （TameList5.lean:116）；`one_step_list`（tame_defs2.hl:81-82）↦ 批 5
    `oneStepListSpine`（:110）；
  · `is_normal`（hypermap.hl:8122）↦ 在库 `Hypermap.IsNormalFamily`
    （Hypermap.lean:6808，四合取逐条同形；构造向批 7 `normalListNormal`
    已消费，本批首次消费其假设向合取 1/合取 4）；
  · `is_loop`（hypermap.hl:6726）↦ `Loop.IsLoopOf`（Hypermap.lean:5734）；
    `one_step_contour`（hypermap.hl:1455）↦ `Hypermap.oneStepContour`
    （:1662）；`in_dart_of_loop`（hypermap.hl:6717）↦ `Loop.darts` 成员
    （批 6 载体约定）；
  · `lemma_in_dart`（hypermap.hl:8152）↦ 在库
    `Hypermap.mem_darts_of_isNormalFamily`（:6834）直接复用；
  · `dart_hypermap_of_list`（tame_list.hl:4095）↦ 定义性：`hypermapOfList`
    的 darts 槽 = `(listOfDarts L).toFinset`（TameLp:3993）+
    `List.mem_toFinset` 双向折算；
  · `loop_of_list`/`loop_family_of_list`（tame_defs2.hl:149/:152）↦ 批 6
    `loopOfListSpine`/`loopFamilyOfListSpine`（TameList6.lean:313/:318）。
  消费件全在案（零新增移植）：`loop_map_next_el`（tame_list.hl:4205 ↦ 批 6
  `loopMapNextEl` :348）、`in_dart_loop_of_list`（:4349 ↦ 批 6
  `inDartLoopOfList` :365）、`face_map_list`（:4907 ↦ TameLp
  `faceMap_hypermapOfList`）、`inverse_node_map_list`（:4889 ↦ 批 8
  `inverseNodeMapList`，TameList8.lean:348）。

  证明层侦察定论：
  · 主件 1（:10832）HOL 证体三步：①`lemma_in_dart` 例示经
    dart_hypermap_of_list 改写得「family 成员的 loop darts ⊆
    list_of_darts L」，供 `x ∈ list_of_darts L` 支；②is_normal 合取 1 的
    is_loop 支在 x 点展开 one_step_contour 两支；③loop_map_next_el +
    face_map_list + inverse_node_map_list 三步改写收口。Lean 面：
    ①↦ `mem_darts_of_isNormalFamily` + `inDartLoopOfList`（真分支门槛
    = all uniq/all nonnil 两前提，恰被真实消费）；②↦ hnor.1 例示
    `Loop.IsLoopOf` 逐点化 + oneStepContour delta 展开 rcases 两支；
    ③↦ `←loopMapNextEl` 换元后 faceMap/inverseNodeMap 点态件各一步 rw。
    零 Meson。
  · 主件 2（:10890）HOL 证体：d ∈ flatten N 取证人 l ∈ N → loop_of_list l ∈
    family（MEMf_MAP）→ d ∈ loop darts（in_dart_loop_of_list）→ is_normal
    合取 4 给 L' ∈ family 且 y ∈ L' darts → family 集合形 unravel 出
    r ∈ N → y ∈ r ⊆ flatten N。Lean 面：family 的 Set 形
    （`loopFamilyOfListSpine = {L | ∃ r ∈ N, L = loopOfListSpine r}`）使
    MEMf_MAP/MEM_MAP 两步合一为匿名构造器。HOL 证明头的 `lemma_in_dart`
    例示为死引入（ASM_REWRITE 消费后无后继使用），Lean 镜像不携带
    （头注记档）；is_restricted/good_list_nodes 两前提在两主件证明中均
    未消费——按全前提保留惯例逐字入语句（`_` 前缀），沿批 7
    `markListMemLoop` 先例。
  · 前提折算：`all (\r. ~(r=[])) N ↦ ∀ s ∈ N, s ≠ []`、
    `all uniq N ↦ ∀ s ∈ N, s.Nodup`（即批 6 `loopOfListSpine` 真分支
    门槛形）；结论 `all (loop_list L) N ↦ ∀ s ∈ N, loopListSpine L s`、
    `set_of_list (flatten N) ↦ {d' | d' ∈ N.flatten}`（批 5 载体约定）。

  依赖面（全为在案真件，零新增债）：批 5 loopListSpine/oneStepListSpine +
  批 6 loopOfListSpine/loopFamilyOfListSpine/loopMapNextEl/inDartLoopOfList +
  批 8 inverseNodeMapList + 批 7 链上 GoodListNodesTl（TameLp S11）+
  TameLp hypermapOfList/faceMap_hypermapOfList + 在库 Hypermap
  IsNormalFamily/oneStepContour/mem_darts_of_isNormalFamily +
  Assembly listOfDarts/nextEl/eList/fList + Mathlib List.mem_flatten/
  mem_toFinset。import 边：本模块 import TameList25（链式带全批 1-23 与
  GoodGraph），零新增库依赖。

  诚实记账：本批两主件全部真证，零新 def、零止损件、零记账债。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 27 接续点：HOL :10930 `path_of_loop_of_list` 起 path 章
  （`!r d. d = HD r /\ uniq r /\ ~(r = []) ==> MAP (path_of_loop
  (loop_of_list r) d) (iota 0 (sizel r)) = r`；`path_of_loop`
  （hypermap.hl:6730）在库已备 `Loop.pathOf`（Hypermap.lean:5738），
  证体 MAP_EQ + iota/POWER 面）。
-/

import Kepler.Text.TameSpine.TameList25

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listOfDarts GoodList nextEl eList fList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList faceMap_hypermapOfList GoodListNodesTl)

/-! ### §1 is_normal_loop_list（tame_list.hl:10832-:10888） -/

/-- **HOL `is_normal_loop_list`**（tame_list.hl:10832-:10888）
`is_restricted (hypermap_of_list L) /\ good_list L /\ good_list_nodes L /\
all (\r. ~(r=[])) N /\ all uniq N /\ is_normal (hypermap_of_list L)
(loop_family_of_list N) ==> all (loop_list L) N`——每个环的真分支展开：
`x ∈ list_of_darts L` 支经 `mem_darts_of_isNormalFamily`（HOL
lemma_in_dart :8152）+ `inDartLoopOfList`（HOL in_dart_loop_of_list）；
one_step 支经 is_normal 合取 1 的 `Loop.IsLoopOf` 逐点展开
oneStepContour 两支，`←loopMapNextEl` 换元后交 `faceMap_hypermapOfList`
（HOL face_map_list）/ `inverseNodeMapList`（HOL inverse_node_map_list）。
is_restricted/good_list_nodes 两前提 HOL 证明未消费，全前提保留。 -/
theorem isNormalLoopList {L : fgraph ℕ} (hL : GoodList L)
    (_hgn : GoodListNodesTl L hL) (_hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hne : ∀ s ∈ N, s ≠ []) (hu : ∀ s ∈ N, s.Nodup)
    (hnor : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N)) :
    ∀ s ∈ N, loopListSpine L s := by
  intro s hs
  have hun : s.Nodup := hu s hs
  have hne' : s ≠ [] := hne s hs
  have hfam : loopOfListSpine s ∈ loopFamilyOfListSpine N := ⟨s, hs, rfl⟩
  intro x hx
  have hxL : x ∈ (loopOfListSpine s).darts := (inDartLoopOfList hun hne' x).mpr hx
  have hxd : x ∈ (hypermapOfList L hL).darts :=
    (hypermapOfList L hL).mem_darts_of_isNormalFamily hnor hfam hxL
  refine ⟨List.mem_toFinset.mp hxd, ?_⟩
  have hmap : (loopOfListSpine s).map x = nextEl s x := loopMapNextEl hun hne' x
  have hosc := (hnor.1 (loopOfListSpine s) hfam).1 x hxL
  simp only [Kepler.Text.Hypermap.oneStepContour] at hosc
  rcases hosc with hf | hnv
  · refine Or.inl ?_
    rw [← hmap, hf, faceMap_hypermapOfList L hL hxd]
  · refine Or.inr ?_
    rw [← hmap, hnv, inverseNodeMapList hL (List.mem_toFinset.mp hxd)]

/-! ### §2 is_normal_nodal（tame_list.hl:10890-:10929） -/

/-- **HOL `is_normal_nodal`**（tame_list.hl:10890-:10929）
`...(同 is_normal_loop_list 前提族) ==> !d. MEM d (flatten N) ==>
node (hypermap_of_list L) d SUBSET set_of_list (flatten N)`——is_normal
合取 4 的消费：d 所在环 loop_of_list l 入 family、d 入其 darts，合取 4
给出含 y 的族员 L'，family 的 Set 形 unravel 出 r ∈ N，`inDartLoopOfList`
回 y ∈ r ⊆ flatten N。HOL 证明头的 lemma_in_dart 例示为死引入，不镜像。 -/
theorem isNormalNodal {L : fgraph ℕ} (hL : GoodList L)
    (_hgn : GoodListNodesTl L hL) (_hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List (ℕ × ℕ))} (hne : ∀ s ∈ N, s ≠ []) (hu : ∀ s ∈ N, s.Nodup)
    (hnor : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfListSpine N)) :
    ∀ d ∈ N.flatten, (hypermapOfList L hL).node d ⊆ {d' | d' ∈ N.flatten} := by
  intro d hd y hy
  obtain ⟨l, hlm, hdl⟩ := List.mem_flatten.mp hd
  have hfam : loopOfListSpine l ∈ loopFamilyOfListSpine N := ⟨l, hlm, rfl⟩
  have hdlL : d ∈ (loopOfListSpine l).darts :=
    (inDartLoopOfList (hu l hlm) (hne l hlm) d).mpr hdl
  obtain ⟨L', hL'fam, hyL'⟩ :=
    hnor.2.2.2 (loopOfListSpine l) hfam d y hdlL hy
  obtain ⟨r, hrm, hrEq⟩ := hL'fam
  rw [hrEq] at hyL'
  have hyr : y ∈ r := (inDartLoopOfList (hu r hrm) (hne r hrm) y).mp hyL'
  show y ∈ N.flatten
  exact List.mem_flatten.mpr ⟨r, hrm, hyr⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.isNormalLoopList
#print axioms Kepler.Text.TameSpine.isNormalNodal
-/
