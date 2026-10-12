/-
  Kepler.Text.TameSpine.TameList6 — B1 Tame_list 地基批 6：planegraph 词汇块 +
  loop_of_list 类型层构造 + _ext 置换群 + is_restricted 基础件 + normal_list
  唯一性群前半（tamespine-port-plan §4 批次表 B1 行；接续批 5 = TameList5.lean，
  HOL :3643-:4189，本批从 `planegraph_PlaneGraphs` :4191 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:4191-:4620 前半 + 引擎件）：

  - planegraph 定义词汇块 :4191（`planegraph`/`finalGraph` 定义层在
    tame_defs2.hl:427/tame_defs.hl:419；`PlaneGraphs`/`PlaneGraphsP` 载体 =
    Kepler.Graphs.Plane1 既有件，零重复移植）；
  - loop_of_list 类型层 :4205/:4230/:4350（`loop_of_list`/`loop_family_of_list`
    定义在 tame_defs2.hl:149/:152；Lean `Loop` 载体 = Kepler.Text.Hypermap）；
  - _ext 置换群 :4255/:4275/:4297（`e_list_ext`/`n_list_ext`/`f_list_ext`
    定义在 formal_lp list_hypermap-compiled.hl:57-59；Lean 载体 =
    `hypermapOfList L hL` 的 edgeMap/nodeMap/faceMap——`res` 语义经
    `extendPerm` 内置，见批 1 头注）；
  - `is_loop_of_list` :4317；
  - is_restricted 基础件 :4358/:4370；
  - normal_list 唯一性群前半 :4480/:4500/:4562/:4588（`uniq_sublist_unique`
    引擎 = list_hypermap-compiled.hl:563）。

  批内分工记账（桥引不重移植）：
  - `PlaneGraphs`/`PlaneGraphsP`/`next_plane`/`Seed`/`RTranCl`/`nonFinals`：
    Kepler.Graphs.Plane1/Plane 既有 def（经 Assembly → Graphs 伞已在闭包内），
    零重复移植；
  - `Loop`/`Loop.IsLoopOf`/`Hypermap.IsRestricted`/`oneStepContour`/
    `orbitMap`/`PermutesOn`：Kepler.Text.Hypermap 既有；
  - `extendPerm`/`Kepler.Text.Fan.res`/`bijOn_res`/`extendPerm_permutes`：
    Kepler.Text.Fan 既有（批 1 已桥引惯例）；⚠ `res` 裸名在本命名空间下被
    `Kepler.Text.res`（Hypermap.lean:662 的 Finset 版）遮蔽，本模块一律全限定；
  - `hypermapOfList` 及 edge/node/face-map 点态件、`nList_fList`、
    `prevEl_nextEl`/`nextEl_prevEl`/`nextEl_eq_getD`/`nextEl_mem_of_mem`/
    `prevEl_mem_of_mem`/`getElem_idxOf`/`idxOf_getElem`/`getD_eq_getElem_of_lt`/
    `findFaceDarts_congr_of_mem`/`findFaceDarts_nodup`/`dart_in_face`/
    `mem_darts_of_mem_findFace`/`fList_mem_darts`/`getD_mem`/
    `la7_eList_involutory`：TameLp 既有；
    `uniqFlattenUniq`/`normalListListOfDarts`/`goodListEList`：批 5 既有；
    `List.idxOf_inj`/`List.nodup_append`/`Equiv.symm_apply_eq`：Mathlib。

  载体折算（沿批 1-5 约定）：
  - `loop_of_list r = loop(set_of_list r, next_el r)` ↦ `loopOfListSpine r :
    Loop (ℕ×ℕ)`：`set_of_list` ↦ `r.toFinset`、置换分量 `next_el r` ↦
    `extendPerm r.toFinset (nextEl r)`（dart 外恒等 = HOL `res` 约定）。
    HOL 侧 `loop` 类型包装对非法二元组（uniq 失败/空表）取 choice-junk；Lean
    侧 dite 显式分层：`r.Nodup ∧ r ≠ []` 分支给真构造（私件
    `realLoopOfList`），junk 分支取单位环（私件 `junkLoop`）——HOL 的 junk
    证人不可观测（被 loop 唯一性定理吸收），任一合法 junk 等价；消费侧定理
    全部携带真分支前提，无 junk 语义进入结论；
  - `planegraph g` ↦ `PlanegraphSpine g := ∃ p, RTranCl (next_plane p) (Seed p) g`；
    `finalGraph g = (nonFinals g = [])` ↦ `finalGraphSpine g := nonFinals g = []`
    （HOL bool 等式 ↦ Prop；桥 = `Graph.final`（Bool 形）+ `List.isEmpty`）；
  - `e_list_ext L`/`n_list_ext L`/`f_list_ext L` ↦ `(hypermapOfList L hL).edgeMap/
    nodeMap/faceMap`（`res`-限制的置换载体内置于 Hypermap 结构体；
    `inverse` ↦ `Equiv.Perm.symm`、HOL `o` ↦ Perm 乘法）；
  - `loop_family_of_list N = set_of_list (MAP loop_of_list N)` ↦
    `loopFamilyOfListSpine N := {L | ∃ r ∈ N, L = loopOfListSpine r}`；
  - `is_loop` ↦ `Loop.IsLoopOf`。

  诚实记账（本批跳过件与边界）：
  - **HOL :4387-:4579 的 node 显式刻画链（node_of_element/
    MEM_hypermap_of_list_node/is_restricted_node_f_list/normal_list_nodes_exist/
    normal_list_normal/别名 EVNAPDQ）本批跳过**：该链依赖 list_hypermap 的
    node-list 理论（node_hypermap_of_list_explicit 走 good_list_nodes 侧
    nodes_of_list_eq/uniq_node/set_nodes_of_list 整块）；Lean 侧 TameLp S11
    仅落了 `nodesOfListSet`/`GoodListNodesTl` def、零定理，「node 轨道 =
    同首分量 dart 全类」的反向（⊇）需要面-面在顶点处的链接论证（HOL 由
    node-list 唯一性给出），估 400-700 行独立子块——留批 7 首件。
    normal_list_normal 的 IsNormalFamily 四合取中，本批已落其 3/4 号合取的
    载体件（normalList11/normalListFullNode），conjunct 2 卡上述 node 链，
    整块待批 7；
  - `normal_list_in_dart_of_loop` 的 HOL 前提 `is_restricted (hypermap_of_list
    L)` 在 HOL 证明中未消费（证体只用 good_list + normal_list）；Lean 镜像
    按原文保留前提（下划线命名），结论零收窄；
  - marked_list 群（tame_defs2.hl:550 定义 + quotient_list :134）未进入本批
    （marked_list_restricted/mem_family/mem_loop 三件不卡 node 链，但需
    quotient_list 定义块进场，与 node 链进度一起留给批 7/8 收）；
  - `PlanegraphSpine`/`finalGraphSpine` 为 Graph 层（Isabelle 移植层
    `Kepler.Graphs.Graph`），与 TameSpine 的 `fgraph ℕ` 列表层分属两类型层
    ——与 HOL 原文一致（HOL 的 planegraph 词汇同样在 fgraph 层之外），
    消费侧（Assembly.TameClassification 等）均在 Graph 层取用；
  - `nextElOfNotMem`/`idxOf_nextEl`/`nextElIterateGetD`（TameLp 同域件为
    private 或无对应公开形）私件层重落，待 TameLp 回灌后消解。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList5

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl prevEl listOfDarts GoodList findFaceDarts
  eList fList nList)
open Kepler.Graphs (fgraph PlaneGraphs next_plane nonFinals RTranCl Seed)
open Kepler.Text (PermutesOn orbitMap)
open Kepler.Text.Fan (extendPerm extendPerm_permutes bijOn_res)
open Kepler.Text.TameLp (hypermapOfList elementsOfList nList_fList
  faceMap_hypermapOfList nodeMap_hypermapOfList edgeMap_hypermapOfList
  fList_mem_darts mem_darts_of_mem_findFace dart_in_face
  findFaceDarts_congr_of_mem findFaceDarts_nodup nextEl_eq_getD
  nextEl_mem_of_mem prevEl_mem_of_mem nextEl_prevEl prevEl_nextEl
  getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem getD_mem la7_eList_involutory)

open scoped Classical

variable {α : Type*}

/-! ### §0 定义层（tame_defs2.hl:427/:149/:152；tame_defs.hl:419） -/

/-- HOL `planegraph`（tame_defs2.hl:427
`planegraph g = (?p. (Seed p,g) IN RTranCl (next_plane p))`）逐句镜像
（Graph 层载体；`Kepler.Graphs.RTranCl`/`Seed` 既有）。 -/
def PlanegraphSpine (g : Kepler.Graphs.Graph) : Prop :=
  ∃ p, RTranCl (next_plane p) (Seed p) g

/-- HOL `finalGraph`（tame_defs.hl:419 `finalGraph g = (nonFinals g = [])`）
逐句镜像（Prop 形；与 `Kepler.Graphs.Graph.final`（Bool 形）经
`List.isEmpty` 桥接）。 -/
def finalGraphSpine (g : Kepler.Graphs.Graph) : Prop := nonFinals g = []

/-! ### §1 planegraph 词汇块（tame_list.hl:4191） -/

/-- `Graph.final`（Bool 形）与 `finalGraphSpine`（Prop 形）的桥
（`nonFinals`/`isEmpty` 定义性展开）。 -/
theorem finalBool_finalGraphSpine (g : Kepler.Graphs.Graph) :
    g.final ↔ finalGraphSpine g := by
  show (nonFinals g).isEmpty = true ↔ _
  exact List.isEmpty_iff

/-- **HOL `planegraph_PlaneGraphs`**（tame_list.hl:4191-:4203
`!g. PlaneGraphs g <=> (planegraph g /\ finalGraph g)`）——`∃` 分配律 +
finalGraph bool/prop 桥（HOL 的 UNIONS/IMAGE 展开步在 Lean 载体下定义性）。 -/
theorem planegraphPlaneGraphs (g : Kepler.Graphs.Graph) :
    PlaneGraphs g ↔ (PlanegraphSpine g ∧ finalGraphSpine g) := by
  constructor
  · intro hpg
    obtain ⟨p, hp⟩ := hpg
    have hP : RTranCl (next_plane p) (Seed p) g ∧ g.final := hp
    exact ⟨⟨p, hP.1⟩, (finalBool_finalGraphSpine g).mp hP.2⟩
  · intro ⟨hpg, hf⟩
    obtain ⟨p, hR⟩ := hpg
    exact ⟨p, hR, (finalBool_finalGraphSpine g).mpr hf⟩

/-! ### §2 loop_of_list 类型层构造（tame_defs2.hl:149 + tame_list.hl:4205/:4230/:4350） -/

/-- BEq-only 世界：`x ∉ s` 时 `nextEl` 退化为默认元 `x`（TameLp
`la7_nextEl_of_notMem` 为 private 无法桥引，同体重落）。 -/
private theorem nextElOfNotMem {α : Type*} [BEq α] [LawfulBEq α] {s : List α}
    {x : α} (hx : x ∉ s) : nextEl s x = x := by
  unfold nextEl
  by_cases h0 : s.length = 0
  · have hs : s = [] := List.length_eq_zero_iff.mp h0
    subst hs
    simp
  · have hidx : s.idxOf x = s.length := List.idxOf_eq_length_iff.mpr hx
    have hne1 : ¬(s.idxOf x = s.length - 1) := by rw [hidx]; omega
    rw [if_neg hne1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [hidx]; omega)]
    simp

/-- nodup 表上下标步进：`idxOf (next_el x) = (idxOf x + 1) mod len`
（TameLp `prevEl_nextEl` 证明内的引擎步，公开形不存在，私件重落）。 -/
private theorem idxOf_nextEl {α : Type*} [BEq α] [LawfulBEq α] {s : List α}
    (hn : s.Nodup) {x : α} (hx : x ∈ s) :
    s.idxOf (nextEl s x) = (s.idxOf x + 1) % s.length := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  rw [nextEl_eq_getD hx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  exact idxOf_getElem hn (Nat.mod_lt _ hpos)

/-- next_el 迭代的 getD 形：第 k 次迭代落在模位置 `(idxOf x + k) mod len`
（cyclic 引擎件；getD 无证明分量，rewriting 免疫 motive 崩溃）。 -/
private theorem nextElIterateGetD {α : Type*} [BEq α] [LawfulBEq α] {s : List α}
    (hn : s.Nodup) {x : α} (hx : x ∈ s) (k : ℕ) :
    (nextEl s)^[k] x = s.getD ((s.idxOf x + k) % s.length) x := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  induction k with
  | zero =>
    show x = s.getD (s.idxOf x % s.length) x
    rw [Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr hx),
      getD_eq_getElem_of_lt (List.idxOf_lt_length_iff.mpr hx)]
    exact (getElem_idxOf hx).symm
  | succ k ih =>
    have hj : (s.idxOf x + k) % s.length < s.length := Nat.mod_lt _ hpos
    have hj' : (s.idxOf x + (k + 1)) % s.length < s.length := Nat.mod_lt _ hpos
    have hmem : s.getD ((s.idxOf x + k) % s.length) x ∈ s := by
      rcases getD_mem x with h | h
      · exact h
      · rw [h]; exact hx
    rw [Function.iterate_succ_apply', ih, nextEl_eq_getD hmem]
    have hidxG : s.idxOf (s.getD ((s.idxOf x + k) % s.length) x)
        = (s.idxOf x + k) % s.length := by
      rw [getD_eq_getElem_of_lt hj]
      exact idxOf_getElem hn hj
    rw [hidxG]
    have he : ((s.idxOf x + k) % s.length + 1) % s.length
        = (s.idxOf x + (k + 1)) % s.length := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [he, getD_eq_getElem_of_lt hj', getD_eq_getElem_of_lt hj']

/-- `loop_of_list` 置换分量的 BijOn 引擎：`Kepler.Text.Fan.res` 限制的
next_el 在 `r.toFinset` 上双射（单射经 idxOf 单射 + nodup；满射经
prev_el_nextEl）。 -/
private theorem loopBijOnNextEl (r : List (ℕ × ℕ)) (hn : r.Nodup) :
    Set.BijOn (Kepler.Text.Fan.res (nextEl r) ↑r.toFinset) ↑r.toFinset
      ↑r.toFinset := by
  refine ⟨fun d hd => ?_, fun a ha b hb hfab => ?_, fun y hy => ?_⟩
  · simp only [Kepler.Text.Fan.res, hd]
    have hmem : d ∈ r := List.mem_toFinset.mp hd
    exact List.mem_toFinset.mpr (nextEl_mem_of_mem hmem)
  · simp only [Kepler.Text.Fan.res, ha, hb] at hfab
    calc a = prevEl r (nextEl r a) := (prevEl_nextEl hn (List.mem_toFinset.mp ha)).symm
      _ = prevEl r (nextEl r b) := congrArg (prevEl r) hfab
      _ = b := prevEl_nextEl hn (List.mem_toFinset.mp hb)
  · have hyr : y ∈ r := List.mem_toFinset.mp (Finset.mem_coe.mp hy)
    refine ⟨prevEl r y, Finset.mem_coe.mpr (List.mem_toFinset.mpr
      (prevEl_mem_of_mem hyr)), ?_⟩
    have hp' : prevEl r y ∈ ((r.toFinset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
      List.mem_toFinset.mpr (prevEl_mem_of_mem hyr)
    show Kepler.Text.Fan.res (nextEl r) ↑r.toFinset (prevEl r y) = y
    simp only [Kepler.Text.Fan.res, hp', if_true]
    exact nextEl_prevEl hn hyr

/-- 私件：extendPerm 提升的迭代在起点于表内时逐点等于 next_el 迭代
（`Kepler.Text.Fan.res`-中介的归纳桥；同时给出迭代点全部落表内）。 -/
private theorem loopBijOnNextEl_bridge {r : List (ℕ × ℕ)} (hn : r.Nodup)
    {x : ℕ × ℕ} (hx : x ∈ r) (n : ℕ) :
    ((extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn)) ^ n) x
      = (nextEl r)^[n] x ∧ (nextEl r)^[n] x ∈ r := by
  induction n with
  | zero => exact ⟨rfl, hx⟩
  | succ k ih =>
    obtain ⟨hev, hmem⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [pow_succ', Equiv.Perm.mul_apply, hev, Function.iterate_succ_apply']
      show (extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn))
        ((nextEl r)^[k] x) = nextEl r ((nextEl r)^[k] x)
      have hd' : (nextEl r)^[k] x
          ∈ ((r.toFinset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
        List.mem_toFinset.mpr hmem
      simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd',
        if_true]
    · rw [Function.iterate_succ_apply']
      exact nextEl_mem_of_mem hmem

/-- loop 构造的 cyclic 引擎件：nodup 非空表的 next_el（经 extendPerm 提升）
从任一表内点出发的轨道充满全表（HOL `Seq2.next_el_orbit` 的 Lean 镜像）。 -/
private theorem nextElOrbitCyclic {r : List (ℕ × ℕ)} (hn : r.Nodup) (_hne : r ≠ [])
    (x : ℕ × ℕ) (hx : x ∈ r) :
    orbitMap (extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn)) x
      = ↑r.toFinset := by
  have hpos : 0 < r.length := List.length_pos_of_mem hx
  have hsub : ∀ y ∈ orbitMap (extendPerm r.toFinset (nextEl r)
      (loopBijOnNextEl r hn)) x, y ∈ r := by
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    have hb := loopBijOnNextEl_bridge hn hx n
    rw [hb.1]
    exact hb.2
  have hsup : ∀ y ∈ r, y ∈ orbitMap (extendPerm r.toFinset (nextEl r)
      (loopBijOnNextEl r hn)) x := by
    intro y hy
    have hilt : r.idxOf x < r.length := List.idxOf_lt_length_iff.mpr hx
    have hyilt : r.idxOf y < r.length := List.idxOf_lt_length_iff.mpr hy
    have hshift : (r.idxOf x + (r.idxOf y + r.length - r.idxOf x)) % r.length
        = r.idxOf y := by
      have he1 : r.idxOf x + (r.idxOf y + r.length - r.idxOf x)
          = r.idxOf y + r.length := by omega
      rw [he1, Nat.add_mod_right, Nat.mod_eq_of_lt hyilt]
    refine ⟨r.idxOf y + r.length - r.idxOf x, ?_⟩
    have hb := loopBijOnNextEl_bridge hn hx
      (r.idxOf y + r.length - r.idxOf x)
    have hiter := nextElIterateGetD hn hx
      (r.idxOf y + r.length - r.idxOf x)
    rw [hb.1, hiter, hshift, getD_eq_getElem_of_lt hyilt, getElem_idxOf hy]
  ext y
  simp only [orbitMap, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset]
  exact ⟨fun hmem => hsub y hmem, fun hmem => hsup y hmem⟩

/-- 私件：`loop_of_list` 的真分支构造（nodup 非空表的 `Loop` 打包；
cyclic 证人不定点由表内任取）。 -/
private noncomputable def realLoopOfList (r : List (ℕ × ℕ)) (hn : r.Nodup)
    (hne : r ≠ []) : Loop (ℕ × ℕ) :=
  { darts := r.toFinset
    map := extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn)
    map_permutes := extendPerm_permutes
    cyclic := by
      obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil r hne
      exact ⟨x0, List.mem_toFinset.mpr hx0, nextElOrbitCyclic hn hne x0 hx0⟩ }

/-- 私件：junk 分支的单位环（darts = {(0,0)}、map = 1；HOL choice-junk 的
不可观测替身，见模块头注）。 -/
private noncomputable def junkLoop : Loop (ℕ × ℕ) :=
  { darts := {(0, 0)}
    map := 1
    map_permutes := fun x _ => rfl
    cyclic := ⟨(0, 0), Finset.mem_singleton.mpr rfl, by
      ext y
      simp only [orbitMap, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_singleton]
      constructor
      · rintro ⟨n, hn⟩
        simpa using hn.symm
      · intro hy
        exact ⟨0, by simpa using hy.symm⟩⟩ }

/-- HOL `loop_of_list`（tame_defs2.hl:149
`loop_of_list r = loop(set_of_list r, next_el r)`）的 `Loop` 载体镜像。

载体记账：真分支 = 私件 `realLoopOfList`（`extendPerm` 置换 + cyclic 引擎），
junk 分支 = 私件 `junkLoop`（单位环；HOL choice-junk 的等价替身，不可观测，
见模块头注）。 -/
noncomputable def loopOfListSpine (r : List (ℕ × ℕ)) : Loop (ℕ × ℕ) :=
  if h : r.Nodup ∧ r ≠ [] then realLoopOfList r h.1 h.2 else junkLoop

/-- HOL `loop_family_of_list`（tame_defs2.hl:152
`loop_family_of_list N = set_of_list (MAP loop_of_list N)`）的 Set 形镜像。 -/
def loopFamilyOfListSpine (N : List (List (ℕ × ℕ))) : Set (Loop (ℕ × ℕ)) :=
  {L | ∃ r ∈ N, L = loopOfListSpine r}

/-- 真分支展开桥：nodup 非空时 `loopOfListSpine r = realLoopOfList r`。 -/
theorem loopOfListSpine_real {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ []) :
    loopOfListSpine r = realLoopOfList r hn hne :=
  dif_pos ⟨hn, hne⟩

/-- 私件：realLoopOfList 的置换分量逐点 = `next_el r`
（`Kepler.Text.Fan.res` 语义 + `nextEl` junk 恒等）。 -/
private theorem realLoopMapApply {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ [])
    (x : ℕ × ℕ) :
    (realLoopOfList r hn hne).map x = nextEl r x := by
  by_cases hx : x ∈ r
  · have hd' : x ∈ ((r.toFinset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
      List.mem_toFinset.mpr hx
    show (extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn)) x = nextEl r x
    simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd',
      if_true]
  · have hd' : x ∉ ((r.toFinset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
      fun hmem => hx (List.mem_toFinset.mp hmem)
    show (extendPerm r.toFinset (nextEl r) (loopBijOnNextEl r hn)) x = nextEl r x
    simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd',
      if_false]
    exact (nextElOfNotMem hx).symm

/-- **HOL `loop_map_next_el`**（tame_list.hl:4205-:4228
`!s. uniq s /\ ~(s = []) ==> loop_map (loop_of_list s) = (next_el s)`）——
HOL 的函数等式按逐点形落（`Loop.map` 分量为 `extendPerm`-res 语义，
dart 外由 `nextEl` 的 junk 恒等吸收）。 -/
theorem loopMapNextEl {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ [])
    (x : ℕ × ℕ) :
    (loopOfListSpine r).map x = nextEl r x := by
  rw [loopOfListSpine_real hn hne]
  exact realLoopMapApply hn hne x

/-- **HOL `dart_of_loop_of_list`**（tame_list.hl:4230-:4253
`!s. uniq s /\ ~(s = []) ==> dart_of_loop (loop_of_list s) = set_of_list s`）——
`set_of_list` ↦ 成员集载体。 -/
theorem dartLoopOfList {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ []) :
    (↑(loopOfListSpine r).darts : Set (ℕ × ℕ)) = {x | x ∈ r} := by
  rw [loopOfListSpine_real hn hne]
  ext x
  exact List.mem_toFinset

/-- **HOL `in_dart_loop_of_list`**（tame_list.hl:4350-:4356
`!r x. uniq r /\ ~(r = []) ==> (x IN dart_of_loop (loop_of_list r) <=> MEM x r)`）。 -/
theorem inDartLoopOfList {r : List (ℕ × ℕ)} (hn : r.Nodup) (hne : r ≠ [])
    (x : ℕ × ℕ) :
    x ∈ (loopOfListSpine r).darts ↔ x ∈ r := by
  rw [loopOfListSpine_real hn hne]
  exact List.mem_toFinset

/-! ### §3 is_loop_of_list（tame_list.hl:4317-:4348） -/

/-- **HOL `is_loop_of_list`**（tame_list.hl:4317
`!L r. good_list L /\ uniq r /\ ~(r = []) /\ loop_list L r
==> is_loop (hypermap_of_list L) (loop_of_list r)`）——`loop_list` 的
one_step 两支分别经 faceMap 点态件（左支）与 nodeMap-symm 侧
（右支：`nList_fList` + `la7_eList_involutory`）收口。 -/
theorem isLoopOfList {L : fgraph ℕ} (hL : GoodList L) {r : List (ℕ × ℕ)}
    (hr : r.Nodup) (hne : r ≠ []) (hloop : loopListSpine L r) :
    Loop.IsLoopOf (hypermapOfList L hL) (loopOfListSpine r) := by
  intro x hx
  have hxr : x ∈ r := (inDartLoopOfList hr hne x).mp hx
  have hxL : x ∈ listOfDarts L := (hloop x hxr).1
  have hxD : x ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hxL
  have hstep : nextEl r x = fList L x ∨ nextEl r x = fList L (eList x) :=
    (hloop x hxr).2
  rw [loopMapNextEl hr hne x]
  show nextEl r x = (hypermapOfList L hL).faceMap x
    ∨ nextEl r x = (hypermapOfList L hL).nodeMap.symm x
  rcases hstep with h1 | h1
  · refine Or.inl ?_
    rw [h1, faceMap_hypermapOfList L hL hxD]
  · refine Or.inr ?_
    have hiff : (hypermapOfList L hL).nodeMap.symm x = nextEl r x ↔
        x = (hypermapOfList L hL).nodeMap (nextEl r x) :=
      Equiv.symm_apply_eq _
    have hkey : x = (hypermapOfList L hL).nodeMap (nextEl r x) := by
      rw [h1]
      have hmemE : eList x ∈ listOfDarts L := goodListEList hL hxL
      have hmemZ : fList L (eList x) ∈ listOfDarts L :=
        fList_mem_darts hL.1 hmemE
      have hzD : fList L (eList x) ∈ (hypermapOfList L hL).darts :=
        List.mem_toFinset.mpr hmemZ
      show x = (hypermapOfList L hL).nodeMap (fList L (eList x))
      rw [nodeMap_hypermapOfList L hL hzD, nList_fList hL.1 hmemE,
        la7_eList_involutory]
    exact (hiff.mpr hkey).symm

/-! ### §4 _ext 置换群（tame_list.hl:4255-:4315） -/

/-- 私件：三映射在 dart 外为恒等（PermutesOn 字段的点态形；statement 用
`listOfDarts`-成员形，应用侧免 H.darts 折算）。 -/
private theorem faceMapOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).faceMap d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact (hypermapOfList L hL).faceMap_permutes d hd'

private theorem edgeMapOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).edgeMap d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact (hypermapOfList L hL).edgeMap_permutes d hd'

private theorem nodeMapOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).nodeMap d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact (hypermapOfList L hL).nodeMap_permutes d hd'

private theorem faceMapSymmOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).faceMap.symm d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact PermutesOn.symm (hypermapOfList L hL).faceMap_permutes d hd'

private theorem edgeMapSymmOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).edgeMap.symm d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact PermutesOn.symm (hypermapOfList L hL).edgeMap_permutes d hd'

private theorem nodeMapSymmOfNotMem {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∉ listOfDarts L) :
    (hypermapOfList L hL).nodeMap.symm d = d := by
  have hd' : d ∉ (hypermapOfList L hL).darts :=
    fun hmem => hd (List.mem_toFinset.mp hmem)
  exact PermutesOn.symm (hypermapOfList L hL).nodeMap_permutes d hd'

/-- 私件：`f_list` 在 dart 上的置换逆像 = 面内前驱
（`findFaceDarts_congr_of_mem` + `nextEl_prevEl` 链）。 -/
private theorem faceMapSymmEqPrev {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    (hypermapOfList L hL).faceMap.symm d = prevEl (findFaceDarts L d) d := by
  have hn : (listOfDarts L).Nodup := hL.1
  have hdF : d ∈ findFaceDarts L d := dart_in_face L d |>.mpr hd
  have hmem : prevEl (findFaceDarts L d) d ∈ findFaceDarts L d :=
    prevEl_mem_of_mem hdF
  have hzD : prevEl (findFaceDarts L d) d ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hmem
  have hzDart : prevEl (findFaceDarts L d) d ∈ (hypermapOfList L hL).darts :=
    List.mem_toFinset.mpr hzD
  have hcongr : findFaceDarts L (prevEl (findFaceDarts L d) d)
      = findFaceDarts L d := findFaceDarts_congr_of_mem hn hd hmem
  have hfu : (hypermapOfList L hL).faceMap (prevEl (findFaceDarts L d) d) = d := by
    rw [faceMap_hypermapOfList L hL hzDart]
    show nextEl (findFaceDarts L (prevEl (findFaceDarts L d) d))
      (prevEl (findFaceDarts L d) d) = d
    rw [hcongr]
    exact nextEl_prevEl (findFaceDarts_nodup hn d) hdF
  have hiff : (hypermapOfList L hL).faceMap.symm d
      = prevEl (findFaceDarts L d) d ↔
      d = (hypermapOfList L hL).faceMap (prevEl (findFaceDarts L d) d) :=
    Equiv.symm_apply_eq _
  exact hiff.mpr hfu.symm

/-- **HOL `inverse_e_list_ext`**（tame_list.hl:4255-:4273
`!L. good_list L ==> inverse(e_list_ext L) = e_list_ext L`）——
`e_list_ext` ↦ `edgeMap`；HOL `inverse` 的选择子语义在 res-双射下 =
Perm 逆，involutory 性由 `la7_eList_involutory` 在 dart 上 + PermutesOn
在 dart 外给出。 -/
theorem inverseEListExt {L : fgraph ℕ} (hL : GoodList L) :
    (hypermapOfList L hL).edgeMap.symm = (hypermapOfList L hL).edgeMap := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ listOfDarts L
  · have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
    have hmemE : eList d ∈ listOfDarts L := goodListEList hL hd
    have hmemED : eList d ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hmemE
    have hfu : (hypermapOfList L hL).edgeMap (eList d) = d := by
      rw [edgeMap_hypermapOfList L hL hmemED, la7_eList_involutory]
    have hiff : (hypermapOfList L hL).edgeMap.symm d = eList d ↔
        d = (hypermapOfList L hL).edgeMap (eList d) :=
      Equiv.symm_apply_eq _
    rw [hiff.mpr hfu.symm, edgeMap_hypermapOfList L hL hdD]
  · rw [edgeMapSymmOfNotMem hL hd, edgeMapOfNotMem hL hd]

/-- 私件：nodeMap = edgeMap ∘ faceMap.symm（`n_list` 定义项
`eList (prevEl (findFace d) d)` 的类型层重排；HOL `n_eq_e_fi` 的
res-对称伴，e_list_ext_n_f 与 inverse_n_list_ext 的共同引擎）。 -/
private theorem nodeMapEqEdgeFaceSymm {L : fgraph ℕ} (hL : GoodList L) :
    (hypermapOfList L hL).nodeMap
      = (hypermapOfList L hL).edgeMap * (hypermapOfList L hL).faceMap.symm := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ listOfDarts L
  · have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
    show (hypermapOfList L hL).nodeMap d
      = (hypermapOfList L hL).edgeMap ((hypermapOfList L hL).faceMap.symm d)
    rw [faceMapSymmEqPrev hL hd]
    have hmem : prevEl (findFaceDarts L d) d ∈ listOfDarts L :=
      mem_darts_of_mem_findFace L (prevEl_mem_of_mem (dart_in_face L d |>.mpr hd))
    have hmemD : prevEl (findFaceDarts L d) d ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hmem
    rw [edgeMap_hypermapOfList L hL hmemD, nodeMap_hypermapOfList L hL hdD]
    rfl
  · show (hypermapOfList L hL).nodeMap d
      = (hypermapOfList L hL).edgeMap ((hypermapOfList L hL).faceMap.symm d)
    rw [faceMapSymmOfNotMem hL hd, edgeMapOfNotMem hL hd, nodeMapOfNotMem hL hd]

/-- **HOL `e_list_ext_n_f`**（tame_list.hl:4297-:4315
`!L. good_list L ==> e_list_ext L = n_list_ext L o f_list_ext L`）——
`nodeMapEqEdgeFaceSymm` 右乘 faceMap 消去。 -/
theorem eListExtNF {L : fgraph ℕ} (hL : GoodList L) :
    (hypermapOfList L hL).edgeMap
      = (hypermapOfList L hL).nodeMap * (hypermapOfList L hL).faceMap := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ listOfDarts L
  · have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
    show (hypermapOfList L hL).edgeMap d
      = (hypermapOfList L hL).nodeMap ((hypermapOfList L hL).faceMap d)
    have hfD : fList L d ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr (fList_mem_darts hL.1 hd)
    rw [faceMap_hypermapOfList L hL hdD, nodeMap_hypermapOfList L hL hfD,
      edgeMap_hypermapOfList L hL hdD]
    exact (nList_fList hL.1 hd).symm
  · show (hypermapOfList L hL).edgeMap d
      = (hypermapOfList L hL).nodeMap ((hypermapOfList L hL).faceMap d)
    rw [faceMapOfNotMem hL hd, nodeMapOfNotMem hL hd, edgeMapOfNotMem hL hd]

/-- **HOL `inverse_n_list_ext`**（tame_list.hl:4275-:4295
`!L. good_list L ==> inverse(n_list_ext L) = f_list_ext L o e_list_ext L`）——
nodeMap = edgeMap ∘ faceMap.symm 取逆 + edgeMap involutory。 -/
theorem inverseNListExt {L : fgraph ℕ} (hL : GoodList L) :
    (hypermapOfList L hL).nodeMap.symm
      = (hypermapOfList L hL).faceMap * (hypermapOfList L hL).edgeMap := by
  refine Equiv.Perm.ext fun d => ?_
  by_cases hd : d ∈ listOfDarts L
  · have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
    have hmemE : eList d ∈ listOfDarts L := goodListEList hL hd
    have hz : fList L (eList d) ∈ listOfDarts L := fList_mem_darts hL.1 hmemE
    have hzD : fList L (eList d) ∈ (hypermapOfList L hL).darts :=
      List.mem_toFinset.mpr hz
    have hu : (hypermapOfList L hL).nodeMap (fList L (eList d)) = d := by
      rw [nodeMap_hypermapOfList L hL hzD, nList_fList hL.1 hmemE,
        la7_eList_involutory]
    show (hypermapOfList L hL).nodeMap.symm d
      = (hypermapOfList L hL).faceMap ((hypermapOfList L hL).edgeMap d)
    have hiff : (hypermapOfList L hL).nodeMap.symm d = fList L (eList d) ↔
        d = (hypermapOfList L hL).nodeMap (fList L (eList d)) :=
      Equiv.symm_apply_eq _
    rw [hiff.mpr hu.symm, edgeMap_hypermapOfList L hL hdD,
      faceMap_hypermapOfList L hL (List.mem_toFinset.mpr hmemE)]
  · show (hypermapOfList L hL).nodeMap.symm d
      = (hypermapOfList L hL).faceMap ((hypermapOfList L hL).edgeMap d)
    rw [nodeMapSymmOfNotMem hL hd, edgeMapOfNotMem hL hd, faceMapOfNotMem hL hd]

/-! ### §5 is_restricted 基础件（tame_list.hl:4358-:4385） -/

/-- **HOL `is_restricted_nonnil`**（tame_list.hl:4358-:4368
`!L. good_list L /\ is_restricted (hypermap_of_list L) ==> ~(L=[])`）——
IsRestricted 的 dart 非空支 + darts_hypermapOfList。 -/
theorem isRestrictedNonnil {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted) : L ≠ [] := by
  intro hnil
  have hD : (hypermapOfList L hL).darts ≠ ∅ := hres.1
  apply hD
  show (listOfDarts L).toFinset = ∅
  have hll : listOfDarts L = [] := by rw [hnil]; rfl
  rw [hll]
  simp

/-- **HOL `is_restricted_e_list_nondeg`**（tame_list.hl:4370-:4385
`!L d. good_list L /\ is_restricted (hypermap_of_list L) /\
MEM d (list_of_darts L) ==> ~(e_list d = d)`）——EdgeNondegenerate 支 +
edgeMap 点态件。 -/
theorem isRestrictedEListNondeg {L : fgraph ℕ} (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : eList d ≠ d := by
  have hdD : d ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hd
  have hne := hres.edgeNondegenerate d hdD
  rw [edgeMap_hypermapOfList L hL hdD] at hne
  exact hne

/-! ### §6 normal_list 唯一性群前半（tame_list.hl:4480-:4620 前半） -/

/-- **HOL `uniq_sublist_unique`**（list_hypermap-compiled.hl:563
`uniq (flatten L) /\ MEM s L /\ MEM t L /\ MEM d s /\ MEM d t ==> s = t`）——
cons 分解 + nodup_append 的跨表不交支（normal_list_11 的引擎）。 -/
theorem uniqSublistUnique {α : Type*} :
    ∀ (N : List (List α)), N.flatten.Nodup → ∀ s ∈ N, ∀ t ∈ N,
      (∃ d, d ∈ s ∧ d ∈ t) → s = t := by
  intro N
  induction N with
  | nil => intro _ s hs; exact absurd hs (by simp)
  | cons u N' ih =>
    intro hfl s hs t ht hd
    rw [List.flatten_cons, List.nodup_append] at hfl
    obtain ⟨hu, hN'fl, hdisj⟩ := hfl
    have hdisj' : ∀ x ∈ u, x ∉ N'.flatten := fun x hx hmem =>
      absurd rfl (hdisj x hx x hmem)
    obtain ⟨d, hds, hdt⟩ := hd
    rcases List.mem_cons.mp hs with rfl | hs'
    · rcases List.mem_cons.mp ht with rfl | ht'
      · rfl
      · have hf : d ∈ N'.flatten := List.mem_flatten.mpr ⟨t, ht', hdt⟩
        exact absurd hf (hdisj' d hds)
    · rcases List.mem_cons.mp ht with rfl | ht'
      · have hf : d ∈ N'.flatten := List.mem_flatten.mpr ⟨s, hs', hds⟩
        exact absurd hf (hdisj' d hdt)
      · exact ih hN'fl s hs' t ht' ⟨d, hds, hdt⟩

/-- **HOL `normal_list_uniq_nonnil`**（tame_list.hl:4500-:4508
`!L N r. normal_list L N /\ MEM r N ==> (uniq r /\ ~(r = []))`）——
uniqFlattenUniq（批 5）+ all-nonnil 合取项直取。 -/
theorem normalListUniqNonnil {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) {r : List (ℕ × ℕ)}
    (hr : r ∈ N) : r.Nodup ∧ r ≠ [] :=
  ⟨uniqFlattenUniq N h.1 r hr, h.2.1 r hr⟩

/-- **HOL `normal_list_in_dart_of_loop`**（tame_list.hl:4480-:4498
`!L N r. is_restricted (hypermap_of_list L) /\ good_list L /\
normal_list L N /\ r IN loop_family_of_list N ==> ?x. x IN dart H /\
in_dart_of_loop x r`）——家族成员取面表内点，两向入 dart 集
（载体记账：`in_dart_of_loop x r` 在 Lean `Loop` 载体下定义性为
`x ∈ r.darts`；is_restricted 前提在 HOL 证明中未消费，按原文保留）。 -/
theorem normalListInDartOfLoop {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (_hres : (hypermapOfList L hL).IsRestricted)
    (h : NormalListSpine hL N) {r : Loop (ℕ × ℕ)}
    (hr : r ∈ loopFamilyOfListSpine N) :
    ∃ x ∈ (hypermapOfList L hL).darts, x ∈ r.darts := by
  have hex : ∃ l ∈ N, r = loopOfListSpine l := hr
  obtain ⟨l, hl, rfl⟩ := hex
  have hlne : l ≠ [] := h.2.1 l hl
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hlne
  refine ⟨x, List.mem_toFinset.mpr (normalListListOfDarts h x
    (List.mem_flatten.mpr ⟨l, hl, hx⟩)), ?_⟩
  rw [loopOfListSpine_real (normalListUniqNonnil h hl).1 hlne]
  exact List.mem_toFinset.mpr hx

/-- **HOL `normal_list_11`**（tame_list.hl:4562-:4586
`!L N r r' d. is_restricted H /\ good_list L /\ normal_list L N /\
r IN loop_family_of_list N /\ r' IN loop_family_of_list N /\
in_dart_of_loop d r /\ in_dart_of_loop d r' ==> r = r'`）——两环的面表经
uniq_sublist_unique 相等，环随表相等。 -/
theorem normalList11 {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    {r r' : Loop (ℕ × ℕ)} (hr : r ∈ loopFamilyOfListSpine N)
    (hr' : r' ∈ loopFamilyOfListSpine N) {d : ℕ × ℕ}
    (hd : d ∈ r.darts) (hd' : d ∈ r'.darts) : r = r' := by
  have hexr : ∃ l ∈ N, r = loopOfListSpine l := hr
  have hexr' : ∃ l ∈ N, r' = loopOfListSpine l := hr'
  obtain ⟨l, hl, rfl⟩ := hexr
  obtain ⟨l', hl', rfl⟩ := hexr'
  have hune := normalListUniqNonnil h hl
  have hune' := normalListUniqNonnil h hl'
  have hdl : d ∈ l := (inDartLoopOfList hune.1 hune.2 d).mp hd
  have hdl' : d ∈ l' := (inDartLoopOfList hune'.1 hune'.2 d).mp hd'
  have hleq := uniqSublistUnique N h.1 l hl l' hl' ⟨d, hdl, hdl'⟩
  rw [hleq]

/-- **HOL `normal_list_full_node`**（tame_list.hl:4588-:4606
`!L N r d d'. is_restricted H /\ good_list L /\ normal_list L N /\
r IN loop_family_of_list N /\ in_dart_of_loop d r /\
d' IN node H d ==> ?r'. r' IN loop_family_of_list N /\ in_dart_of_loop d' r'`）
——normal_list 末合取项给 `d' ∈ flatten`，面表 l' 给环。 -/
theorem normalListFullNode {L : fgraph ℕ} (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    {r : Loop (ℕ × ℕ)} (hr : r ∈ loopFamilyOfListSpine N)
    {d d' : ℕ × ℕ} (hd : d ∈ r.darts)
    (hd' : d' ∈ (hypermapOfList L hL).node d) :
    ∃ r' ∈ loopFamilyOfListSpine N, d' ∈ r'.darts := by
  have hexr : ∃ l ∈ N, r = loopOfListSpine l := hr
  obtain ⟨l, hl, rfl⟩ := hexr
  have hne : l ≠ [] := h.2.1 l hl
  have hdl : d ∈ l := (inDartLoopOfList (normalListUniqNonnil h hl).1 hne d).mp hd
  have hdfl : d ∈ N.flatten := List.mem_flatten.mpr ⟨l, hl, hdl⟩
  have hd'fl : d' ∈ N.flatten := h.2.2.2.2 d hdfl hd'
  obtain ⟨l', hl', hd'l'⟩ := List.mem_flatten.mp hd'fl
  refine ⟨loopOfListSpine l', ⟨l', hl', rfl⟩, ?_⟩
  rw [loopOfListSpine_real (normalListUniqNonnil h hl').1 (normalListUniqNonnil h hl').2]
  exact List.mem_toFinset.mpr hd'l'

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.planegraphPlaneGraphs
#print axioms Kepler.Text.TameSpine.loopMapNextEl
#print axioms Kepler.Text.TameSpine.dartLoopOfList
#print axioms Kepler.Text.TameSpine.isLoopOfList
#print axioms Kepler.Text.TameSpine.inverseEListExt
#print axioms Kepler.Text.TameSpine.inverseNListExt
#print axioms Kepler.Text.TameSpine.eListExtNF
#print axioms Kepler.Text.TameSpine.isRestrictedNonnil
#print axioms Kepler.Text.TameSpine.normalList11
#print axioms Kepler.Text.TameSpine.normalListFullNode
-/
