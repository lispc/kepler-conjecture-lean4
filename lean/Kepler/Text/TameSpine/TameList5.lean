/-
  Kepler.Text.TameSpine.TameList5 — B1 Tame_list 地基批 5：normal_list 家族 +
  iso_list 运输收束 + Hypermap 类型层桥
  （tamespine-port-plan §4 批次表 B1 行；接续批 4 = TameList4.lean，HOL
  :2936-:3642，本批从 `normal_list_list_of_darts` :3643 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:3643-:4189——normal_list 基础件、
  iso_list_sym_normal/nil 群、INJ_NUM_EXISTS、inj_on_dart_of_list、
  iso_list 运输五件（uniq_flatten/all_nonnil/all_darts/all_loop_list/f_last）、
  e_list_fun/f_list_map、LAST_MAP、Hypermap 类型层桥块（hyp_iso_hypermap_of_list
  /dart_hypermap_of_list/list_pairs_unique/iso_list_normal_node）、capstone
  iso_list_normal（别名 XKDZKWV）；定义层 f_last/one_step_list/loop_list/
  normal_list 在 tame_defs2.hl:78-100）：

  - 定义层：`f_last` :78、`one_step_list` :81、`loop_list` :84、
    `normal_list` :93（tame_defs2.hl ↦ `fLastSpine`/`oneStepListSpine`/
    `loopListSpine`/`NormalListSpine`）；
  - normal_list 基础件 :3643/:3652/:3663（flatten N ⊆ darts，member/set 两形）；
  - iso_list 对称群 :3673-:3717（iso_list_sym_normal/nil/nil_eq，经批 4
    isoListSpineSym 桥引 + normal_list 前提折算）；
  - `INJ_NUM_EXISTS` :3719（有限集的 ℕ 编码；Fintype.equivFin 路线）；
  - `inj_on_dart_of_list` :3746（Set.InjOn 桥形；点式本体 = 批 2
    injOnLiftListOfDarts）；
  - iso_list 运输家族 :3758-:3972（uniq_flatten/all_nonnil/all_darts/
    all_loop_list，e_list_fun/f_list_map 驱动）；
  - `uniq_flatten_uniq` :3872、`good_list_e_list` :3883；
  - `LAST_MAP` :3975 与 `iso_list_f_last` :3988；
  - Hypermap 类型层块 :4043-:4164：`hyp_iso_hypermap_of_list`（桥引批 1）、
    `dart_hypermap_of_list`（桥引 TameLp）、`list_pairs_unique`、
    `iso_list_normal_node`（node 轨道像运输）；
  - **capstone `iso_list_normal`** :4166（别名 `XKDZKWV` :4189）——normal_list
    沿 iso_list 整体运输，A9 链 consume 形。

  批内分工记账（桥引不重移植）：
  - `JXBJOAB` :3733：批 1 已真证（TameList1.lean:174，ℕ-monomorphic id 证人形），
    跳过；
  - `hyp_iso_hypermap_of_list` :4043：HOL 陈述 = `hyp_iso (pair-lift)
    (hypermap_of_list x) (hypermap_of_list (MAP (MAP phi) x))`，而 HOL
    `hyp_iso f (H,G)` 的 BIJ + 三 map 交换恰好是 Lean `Hypermap.Iso` 的结构体
    字段（证人 f 内置），故本件 = 批 1 `hypermapOfList_iso_map_injOn` 逐字同体，
    以别名 `hypIsoHypermapOfList` 桥引（与批 4 UEYETNI/批 1 PEUTLZH 同惯例）；
  - `dart_hypermap_of_list` :4095：本体 = TameLp `darts_hypermapOfList`
    （TameLp.lean:2579 逐字同陈述），以别名桥引；
  - `normal_list_darts_of_list_mem` :3663：HOL 内与 :3643 逐字重复（同陈述
    双绑定），以别名 `normalListDartsMem` 落账；
  - `iso_list_all_darts` 的 `map_list_of_darts` 步 = TameLp `Kepler.Text.TameLp.la7_listOfDarts_map`；
    `next_el_MEM_map`/`prev_el_map`/`uniq_map`/`find_face_map` 各步分别 =
    Kepler.Text.TameLp.la7_nextEl_map/Kepler.Text.TameLp.la7_prevEl_map/Kepler.Text.TameLp.la7_nodup_map_on/批 1 findFace_map_injOn。

  载体折算（沿批 1-4 约定）：
  - `f_last L s := next_el s (LAST s) = f_list L (LAST s)`：`LAST` ↦
    `List.getLast!`（配 `Inhabited (ℕ×ℕ)` 伪参，空表 junk 按默认值 (0,0) 吸收；
    各定理经 `s ≠ []` 前提折算到 `List.getLast` 形，无 junk 语义损失）；
  - `next_el` ↦ `Kepler.Assembly.nextEl`、`e_list`/`f_list`/`n_list` ↦
    `Kepler.Assembly.eList/fList/nList`、`list_of_darts` ↦ `listOfDarts`、
    `uniq` ↦ `List.Nodup`、`all P l` ↦ 逐点 ∀ ∈ 形、`set_of_list` ↦
    `{x | x ∈ _}`；
  - `node (hypermap_of_list L) d` ↦ `(hypermapOfList L hL).node d`
    （Kepler.Text.Hypermap.node = nodeMap 轨道）。

  诚实记账（载体约定/前提增补）：
  - **NormalListSpine 携带 `hL : GoodList L`**：HOL `normal_list` 的末合取项
    `node (hypermap_of_list L) d SUBSET set_of_list (flatten N)` 引用
    `hypermap_of_list L`——HOL 侧该函数经 `res` 语义对任意 L 有全定义，Lean 侧
    `hypermapOfList` 需 `GoodList L` 才能构造 Hypermap 结构体。故载体把 GoodList
    证人作为显式参数携带（同 `hypermapOfList L hL` 惯例）；代价是
    `normal_list_nil`/`iso_list_sym_nil(_eq)` 比 HOL 原句多一个 `GoodList L`
    前提（纯证人增补，非陈述收窄——全部实际消费者本就假设 good_list L）；
  - `fLastSpine`/`loopListSpine` 不需要 GoodList（fList/nextEl 全定义），
    按 HOL 原句无条件落；
  - `INJ_NUM_EXISTS`：HOL 对任意类型 A 的有限集成立（Counting_spheres.
    INJ_FINITE_EXISTS）；Lean 侧同形 `Set.Finite A → ∃ j, Set.InjOn j A`
    经 `Set.Finite.fintype` + `Fintype.equivFin` 真证，无损；
  - `e_list_fun` 的 HOL `LET_THM` 展开形按 β-归约后陈述落
    （`e_list (nphi x) = nphi (e_list x)` 的 nphi 显式内联），rfl；
  - `iso_list_all_loop_list`/`iso_list_f_last`：HOL 证体为 ~80 行 meson 编排，
    Lean 侧按「next_el MAP 运输 + e_list_fun + f_list_map + normal_list 前提
    逐项代入」重排为直证，内容同构无收窄；
  - `iso_list_normal_node` 的 `components_iso_image`（node 轨道像运输）在
    TameList1 为私有件（iso_node_image），本批以 pair-lift 特形私件
    `nodeLiftImage` 重落（通用形仍留 TameList1 私有层，未回灌）。

  红线遵守：本模块零 sorry、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList4

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl prevEl listOfDarts GoodList findFaceDarts
  eList fList nList)
open Kepler.Graphs (fgraph)
open Kepler.Text (PermutesOn orbitMap)
open Kepler.Text.TameLp (hypermapOfList elementsOfList)

variable {α : Type*}

/-! ### §0 定义层（tame_defs2.hl:78-100） -/

/-- HOL `f_last`（tame_defs2.hl:78-79
`f_last L s <=> next_el s (LAST s) = f_list L (LAST s)`）逐句镜像
（`LAST` ↦ `List.getLast!`，空表 junk 按默认值吸收；消费侧均配 `s ≠ []`
折算到 `List.getLast` 形）。 -/
def fLastSpine (L : fgraph ℕ) (s : List (ℕ × ℕ)) : Prop :=
  nextEl s s.getLast! = fList L s.getLast!

/-- HOL `one_step_list`（tame_defs2.hl:81-82
`one_step_list L x y = (y = f_list L x \/ y = f_list L (e_list x))`）逐句镜像。 -/
def oneStepListSpine (L : fgraph ℕ) (x y : ℕ × ℕ) : Prop :=
  y = fList L x ∨ y = fList L (eList x)

/-- HOL `loop_list`（tame_defs2.hl:84-86
`loop_list L s <=> all (\x. MEM x (list_of_darts L) /\
one_step_list L x (next_el s x)) s`）逐句镜像（HOL `all` ↦ 逐点 ∀ ∈ 形）。 -/
def loopListSpine (L : fgraph ℕ) (s : List (ℕ × ℕ)) : Prop :=
  ∀ x ∈ s, x ∈ listOfDarts L ∧ oneStepListSpine L x (nextEl s x)

/-- HOL `normal_list`（tame_defs2.hl:93-100
`normal_list L N <=> uniq (flatten N) /\ all (\s. ~(s = [])) N /\
all (f_last L) N /\ all (loop_list L) N /\
(!d. MEM d (flatten N) ==> node (hypermap_of_list L) d SUBSET
set_of_list (flatten N))`）逐句镜像。

载体记账：末合取项的 `hypermap_of_list L` 在 Lean 需 `GoodList L` 构造
（见模块头注），故证人 `hL` 显式入参；`set_of_list` ↦ `{x | x ∈ _}`。 -/
def NormalListSpine {L : fgraph ℕ} (hL : GoodList L)
    (N : List (List (ℕ × ℕ))) : Prop :=
  N.flatten.Nodup ∧
  (∀ s ∈ N, s ≠ []) ∧
  (∀ s ∈ N, fLastSpine L s) ∧
  (∀ s ∈ N, loopListSpine L s) ∧
  ∀ d ∈ N.flatten, (hypermapOfList L hL).node d ⊆ {d' | d' ∈ N.flatten}

/-- `List.getLast!` 到 `List.getLast` 的非空折算（f_last 消费侧的 junk 桥）。 -/
theorem getLast!EqGetLast {α : Type*} [Inhabited α] {s : List α} (h : s ≠ []) :
    s.getLast! = s.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-! ### §1 normal_list 基础件（tame_list.hl:3643-:3745） -/

/-- HOL `normal_list_list_of_darts`（tame_list.hl:3643
`normal_list L N ==> all (\x. MEM x (list_of_darts L)) (flatten N)`）——
loop_list 合取项的 flatten 提升。 -/
theorem normalListListOfDarts {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    ∀ x ∈ N.flatten, x ∈ listOfDarts L := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hx
  exact ((h.2.2.2.1 s hs) x hxs).1

/-- HOL `normal_list_darts_of_list`（tame_list.hl:3652
`normal_list L N ==> set_of_list (flatten N) SUBSET darts_of_list L`）的
集合形（`set_of_list`/`darts_of_list` ↦ `{x | x ∈ _}` 成员谓词载体）。 -/
theorem normalListDartsSubset {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    {d | d ∈ N.flatten} ⊆ {d | d ∈ listOfDarts L} := by
  intro d hd
  exact normalListListOfDarts h d hd

/-- HOL `normal_list_darts_of_list_mem`（tame_list.hl:3663）——HOL 内与
:3643 逐字重复（同陈述双绑定），别名落账。 -/
theorem normalListDartsMem {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) :
    ∀ x ∈ N.flatten, x ∈ listOfDarts L :=
  normalListListOfDarts h

/-- HOL `iso_list_sym_normal`（tame_list.hl:3673
`normal_list L N /\ iso_list (L,N) (L',N') ==> iso_list (L',N') (L,N)`）——
经批 4 `isoListSpineSym`（两组 SUBSET 前提由 normal_list_list_of_darts +
mem_list_of_darts_imp_mem_list_of_elements_alt 折算给出）。 -/
theorem isoListSpineSymNormal {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    IsoListSpine L' L N' N := by
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  refine isoListSpineSym hiso (fun p hp => ?_) (fun p hp => ?_)
  · exact (memDartsImpMemElements L (hmem p hp)).1
  · exact (memDartsImpMemElements L (hmem p hp)).2

/-- HOL `normal_list_nil`（tame_list.hl:3692 `normal_list L []`）。
载体记账：GoodList 证人为 Lean 载体的显式参数（见头注），HOL 原句无此前提。 -/
theorem normalListNil (L : fgraph ℕ) (hL : GoodList L) :
    NormalListSpine hL [] := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact absurd hs (by simp)
  · intro s hs
    exact absurd hs (by simp)
  · intro s hs
    exact absurd hs (by simp)
  · intro d hd
    exact absurd hd (by simp)

/-- HOL `iso_list_sym_nil`（tame_list.hl:3701
`iso_list (L,[]) (L',[]) ==> iso_list (L',[]) (L,[])`）。 -/
theorem isoListSpineSymNil {L L' : fgraph ℕ} (hL : GoodList L)
    (hiso : IsoListSpine L L' [] []) :
    IsoListSpine L' L [] [] :=
  isoListSpineSymNormal (normalListNil L hL) hiso

/-- HOL `iso_list_sym_nil_eq`（tame_list.hl:3711
`iso_list (L,[]) (L',[]) <=> iso_list (L',[]) (L,[])`）。 -/
theorem isoListSpineSymNilIff {L L' : fgraph ℕ} (hL : GoodList L)
    (hL' : GoodList L') :
    IsoListSpine L L' [] [] ↔ IsoListSpine L' L [] [] :=
  ⟨isoListSpineSymNil hL, isoListSpineSymNil hL'⟩

/-- **HOL `INJ_NUM_EXISTS`**（tame_list.hl:3719
`!A. FINITE A ==> (?j:A->num. inj_on j A)`）——有限集的 ℕ 编码存在性
（Mathlib `Set.Finite.fintype` + `Fintype.equivFin` 路线；证人 dart 外取 0）。 -/
theorem injNumExists {α : Type*} {A : Set α} (hfin : A.Finite) :
    ∃ j : α → ℕ, Set.InjOn j A := by
  classical
  haveI : Fintype ↥A := hfin.fintype
  refine ⟨fun x => if h : x ∈ A then Fintype.equivFin ↥A ⟨x, h⟩ else 0, ?_⟩
  intro x hx y hy heq
  simp only [dif_pos hx, dif_pos hy] at heq
  exact congrArg Subtype.val
    (Equiv.injective (Fintype.equivFin ↥A) (Fin.val_injective heq))

/-- HOL `inj_on_dart_of_list`（tame_list.hl:3746
`inj_on p (elements_of_list L) ==> inj_on (\t. p (FST t), p (SND t))
(darts_of_list L)`）的 `Set.InjOn` 桥形（点式本体 = 批 2
`injOnLiftListOfDarts`）。 -/
theorem injOnDartOfList (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) :
    Set.InjOn (fun t : ℕ × ℕ => (phi t.1, phi t.2)) {d | d ∈ listOfDarts L} :=
  fun _ hd _ he h => injOnLiftListOfDarts L hinj hd he h

/-! ### §2 iso_list 运输家族（tame_list.hl:3758-:3972） -/

/-- HOL `iso_list_uniq_flatten`（tame_list.hl:3758
`normal_list L N /\ iso_list (L,N) (L',N') ==> uniq (flatten N')`）——
`flatten (MAP (MAP nphi) N) = MAP nphi (flatten N)` 后 `uniq_map`（la7
点式形 + inj_on_dart_of_list 的 flatten 限制）。 -/
theorem isoListUniqFlatten {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    N'.flatten.Nodup := by
  obtain ⟨phi, hinj, -, hN'eq⟩ := hiso
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  have hfm : (N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))).flatten
      = N.flatten.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) :=
    (mapFlattenSpine (f := fun u : ℕ × ℕ => (phi u.1, phi u.2)) N).symm
  rw [hN'eq, hfm]
  exact Kepler.Text.TameLp.la7_nodup_map_on
    (f := fun u : ℕ × ℕ => (phi u.1, phi u.2))
    (fun u hu v hv huv => injOnLiftListOfDarts L hinj (hmem u hu) (hmem v hv) huv)
    h.1

/-- HOL `iso_list_all_nonnil`（tame_list.hl:3780
`normal_list L N /\ iso_list (L,N) (L',N') ==> all (\s. ~(s = [])) N'`）——
MAP 保持非空。 -/
theorem isoListAllNonnil {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    ∀ s' ∈ N', s' ≠ [] := by
  obtain ⟨phi, -, -, hN'eq⟩ := hiso
  intro s' hs'
  rw [hN'eq, List.mem_map] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  intro hnil
  exact h.2.1 s hs (List.map_eq_nil_iff.mp hnil)

/-- HOL `iso_list_all_darts`（tame_list.hl:3804
`normal_list L N /\ iso_list (L,N) (L',N') ==> all (\x. MEM x
(list_of_darts L')) (flatten N')`）——逐点 x = nphi d 与 `map_list_of_darts`
（Kepler.Text.TameLp.la7_listOfDarts_map）。 -/
theorem isoListAllDarts {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    ∀ x ∈ N'.flatten, x ∈ listOfDarts L' := by
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  intro x hx
  rw [hN'eq] at hx
  obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hx
  rw [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [List.mem_map] at hxs
  obtain ⟨d, hd, rfl⟩ := hxs
  have hdD : d ∈ listOfDarts L := hmem d (List.mem_flatten.mpr ⟨t, ht, hd⟩)
  rw [hL'eq, Kepler.Text.TameLp.la7_listOfDarts_map]
  exact List.mem_map.mpr ⟨d, hdD, rfl⟩

/-- HOL `e_list_fun`（tame_list.hl:3827
`e_list (nphi x) = nphi (e_list x)`，`nphi = \u. phi (FST u), phi (SND u)`）——
pair-lift 与 e_list 交换（β-归约后定义性）。 -/
theorem eListFun (phi : ℕ → ℕ) (x : ℕ × ℕ) :
    eList (phi x.1, phi x.2) = (phi (eList x).1, phi (eList x).2) := rfl

/-- HOL `f_list_map`（tame_list.hl:3840
`good_list L /\ inj_on phi (elements_of_list L) /\ MEM x (list_of_darts L) ==>
f_list (MAP (MAP phi) L) (nphi x) = nphi (f_list L x)`）——
`find_face_map`（批 1）+ `next_el_MEM_map`（la7）链。 -/
theorem fListMap {L : fgraph ℕ} {hL : GoodList L} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) :
    fList (L.map (List.map phi)) (phi d.1, phi d.2)
      = (phi (fList L d).1, phi (fList L d).2) := by
  have hmem : d ∈ findFaceDarts L d := Kepler.Text.TameLp.la7_dart_in_findFace L d hd
  have hinj' : ∀ u ∈ findFaceDarts L d, ∀ v ∈ findFaceDarts L d,
      (fun t : ℕ × ℕ => (phi t.1, phi t.2)) u
        = (fun t : ℕ × ℕ => (phi t.1, phi t.2)) v → u = v :=
    fun u hu v hv huv => injOnLiftListOfDarts L hinj
      (Kepler.Text.TameLp.mem_darts_of_mem_findFace L hu) (Kepler.Text.TameLp.mem_darts_of_mem_findFace L hv) huv
  show nextEl (findFaceDarts (L.map (List.map phi)) (phi d.1, phi d.2))
      (phi d.1, phi d.2)
    = (phi (nextEl (findFaceDarts L d) d).1,
       phi (nextEl (findFaceDarts L d) d).2)
  rw [findFace_map_injOn hinj d hd,
    Kepler.Text.TameLp.la7_nextEl_map (f := fun t : ℕ × ℕ => (phi t.1, phi t.2)) hinj' hmem]

/-- HOL `uniq_flatten_uniq`（tame_list.hl:3872
`uniq (flatten L) /\ MEM s L ==> uniq s`）——flatten 的 cons 分解 +
nodup_append 两支。 -/
theorem uniqFlattenUniq {α : Type*} :
    ∀ (L : List (List α)), L.flatten.Nodup → ∀ s ∈ L, s.Nodup := by
  intro L
  induction L with
  | nil => intro _ s hs; exact absurd hs (by simp)
  | cons a t ih =>
    intro hfl s hs
    rw [List.mem_cons] at hs
    rw [List.flatten_cons] at hfl
    obtain ⟨h1, h2, -⟩ := List.nodup_append.mp hfl
    rcases hs with rfl | hst
    · exact h1
    · exact ih h2 s hst

/-- HOL `good_list_e_list`（tame_list.hl:3883
`good_list L /\ MEM d (list_of_darts L) ==> MEM (e_list d) (list_of_darts L)`）
——GoodList 第三合取项（HOL `MEM (SND d, FST d)` 与 `e_list d` 逐字同义）。 -/
theorem goodListEList {L : fgraph ℕ} (hL : GoodList L) {d : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) : eList d ∈ listOfDarts L :=
  hL.2.2 d hd

/-- HOL `iso_list_all_loop_list`（tame_list.hl:3893
`good_list L /\ normal_list L N /\ iso_list (L,N) (L',N') ==> all
(loop_list L') N'`）——逐点：next_el 的 MAP 运输（Kepler.Text.TameLp.la7_nextEl_map）+
one_step 两支分别经 `f_list_map`（d 支 / e_list d 支）+ `e_list_fun` 收口。 -/
theorem isoListAllLoopList {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    ∀ s' ∈ N', loopListSpine L' s' := by
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  intro s' hs'
  rw [hN'eq, List.mem_map] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdD : d ∈ listOfDarts L := hmem d (List.mem_flatten.mpr ⟨s, hs, hd⟩)
  have hstep : nextEl s d = fList L d ∨ nextEl s d = fList L (eList d) :=
    (h.2.2.2.1 s hs d hd).2
  refine ⟨?_, ?_⟩
  · rw [hL'eq, Kepler.Text.TameLp.la7_listOfDarts_map]
    exact List.mem_map.mpr ⟨d, hdD, rfl⟩
  · have hinjL : ∀ u ∈ s, ∀ v ∈ s,
        (fun t : ℕ × ℕ => (phi t.1, phi t.2)) u
          = (fun t : ℕ × ℕ => (phi t.1, phi t.2)) v → u = v :=
      fun u hu v hv huv => injOnLiftListOfDarts L hinj
        (hmem u (List.mem_flatten.mpr ⟨s, hs, hu⟩))
        (hmem v (List.mem_flatten.mpr ⟨s, hs, hv⟩)) huv
    have hnext : nextEl (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2)))
        (phi d.1, phi d.2) = (phi (nextEl s d).1, phi (nextEl s d).2) :=
      Kepler.Text.TameLp.la7_nextEl_map hinjL hd
    show nextEl (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2))) (phi d.1, phi d.2)
        = fList L' (phi d.1, phi d.2)
      ∨ nextEl (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2))) (phi d.1, phi d.2)
        = fList L' (eList (phi d.1, phi d.2))
    rw [hnext]
    rcases hstep with h1 | h1
    · refine Or.inl ?_
      rw [h1, hL'eq, fListMap (hL := hL) hinj hdD]
    · refine Or.inr ?_
      rw [h1, hL'eq, eListFun, fListMap (hL := hL) hinj (goodListEList hL hdD)]

/-! ### §3 LAST_MAP 与 iso_list_f_last（tame_list.hl:3975-:4041） -/

/-- HOL `LAST_MAP`（tame_list.hl:3975
`~(s = []) ==> LAST (MAP f s) = f (LAST s)`）。 -/
theorem lastMapSpine {α β : Type*} (f : α → β) {s : List α} (h : s ≠ []) :
    (s.map f).getLast (show s.map f ≠ [] from fun hm => h (List.map_eq_nil_iff.mp hm))
      = f (s.getLast h) :=
  List.getLast_map (show s.map f ≠ [] from fun hm => h (List.map_eq_nil_iff.mp hm))

/-- HOL `iso_list_f_last`（tame_list.hl:3988
`good_list L /\ normal_list L N /\ iso_list (L,N) (L',N') ==> all (f_last L') N'`）
——LAST_MAP + next_el MAP 运输 + f_last L 前提 + f_list_map 链
（getLast! 的 junk 支经 `s ≠ []` 折算，见载体记账）。 -/
theorem isoListFLast {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    ∀ s' ∈ N', fLastSpine L' s' := by
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  intro s' hs'
  rw [hN'eq, List.mem_map] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  have hsne : s ≠ [] := h.2.1 s hs
  have hmapne : s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2)) ≠ [] := fun hm =>
    hsne (List.map_eq_nil_iff.mp hm)
  have hlastmem : s.getLast hsne ∈ s := List.getLast_mem hsne
  have hdD : s.getLast hsne ∈ listOfDarts L :=
    hmem _ (List.mem_flatten.mpr ⟨s, hs, hlastmem⟩)
  have hinjL : ∀ u ∈ s, ∀ v ∈ s,
      (fun t : ℕ × ℕ => (phi t.1, phi t.2)) u
        = (fun t : ℕ × ℕ => (phi t.1, phi t.2)) v → u = v :=
    fun u hu v hv huv => injOnLiftListOfDarts L hinj
      (hmem u (List.mem_flatten.mpr ⟨s, hs, hu⟩))
      (hmem v (List.mem_flatten.mpr ⟨s, hs, hv⟩)) huv
  show nextEl (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2)))
      (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2))).getLast!
    = fList L' (s.map (fun t : ℕ × ℕ => (phi t.1, phi t.2))).getLast!
  rw [getLast!EqGetLast hmapne, lastMapSpine (fun t : ℕ × ℕ => (phi t.1, phi t.2)) hsne,
    Kepler.Text.TameLp.la7_nextEl_map hinjL hlastmem]
  have hfs : nextEl s s.getLast! = fList L s.getLast! := h.2.2.1 s hs
  rw [getLast!EqGetLast hsne] at hfs
  rw [hfs, hL'eq, fListMap (hL := hL) hinj hdD]

/-! ### §4 Hypermap 类型层桥块（tame_list.hl:4043-:4164） -/

/-- **HOL `hyp_iso_hypermap_of_list`**（tame_list.hl:4043-:4093
`good_list x /\ inj_on phi (elements_of_list x) ==> hyp_iso (\u. phi (FST u),
phi (SND u)) (hypermap_of_list x, hypermap_of_list (MAP (MAP phi) x))`）。

桥引记账：HOL `hyp_iso f (H,G)` 的 BIJ + edge/node/face 三 map 交换合取恰为
Lean `Hypermap.Iso` 的结构体字段（证人 f 内置），故本件与批 1
`hypermapOfList_iso_map_injOn`（= HOL `hypermap_of_list_map` :3486 的
Iso 形）逐字同体，别名桥引不重移植。 -/
theorem hypIsoHypermapOfList {L : fgraph ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) (hgood : GoodList L) :
    Hypermap.Iso (hypermapOfList L hgood)
      (hypermapOfList (L.map (List.map phi)) (mapGoodList_injOn hinj hgood)) :=
  hypermapOfList_iso_map_injOn hinj hgood

/-- HOL `dart_hypermap_of_list`（tame_list.hl:4095-:4107
`good_list L ==> dart (hypermap_of_list L) = set_of_list (list_of_darts L)`）
——本体 = TameLp `darts_hypermapOfList`（TameLp.lean:2579 逐字同陈述），
别名桥引。 -/
theorem dartHypermapOfList (L : fgraph ℕ) (hL : GoodList L) :
    (↑(hypermapOfList L hL).darts : Set (ℕ × ℕ)) = {d | d ∈ listOfDarts L} :=
  Kepler.Text.TameLp.darts_hypermapOfList L hL

/-- 私件：zip 成员的下标刻画（`list_pairs_unique` 的引擎；本版 Mathlib 无
`List.mem_zip` 成员刻画，经 `mem_iff_getElem` + `getElem_zip` 重落）。 -/
private theorem memZipEq {β : Type*} {l₁ : List β} {l₂ : List β} {d : β × β}
    (h : d ∈ l₁.zip l₂) :
    ∃ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      (l₁[i]'h₁, l₂[i]'h₂) = d := by
  obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_zip] at hd
  refine ⟨i, ?_, ?_, hd⟩
  · have hk : i < l₁.length ∧ i < l₂.length := by
      rw [List.length_zip] at hi; omega
    exact hk.1
  · have hk : i < l₁.length ∧ i < l₂.length := by
      rw [List.length_zip] at hi; omega
    exact hk.2

/-- HOL `list_pairs_unique`（tame_list.hl:4110-:4117
`uniq f /\ MEM d1 (list_pairs f) /\ MEM d2 (list_pairs f) /\ FST d1 = FST d2
==> d1 = d2`）——nodup f 下首分量定下标（Nodup.getElem_inj_iff），rotate 1
的位移分量随下标相等。 -/
theorem listPairsUnique {f : List α} (hn : f.Nodup) {d1 d2 : α × α}
    (h1 : d1 ∈ listPairs f) (h2 : d2 ∈ listPairs f) (h : d1.1 = d2.1) :
    d1 = d2 := by
  have e : listPairs f = f.zip (f.rotate 1) := by
    show f.zip (f.drop 1 ++ f.take 1) = f.zip (f.rotate 1)
    rw [rotateSpineOne]
  rw [e] at h1 h2
  obtain ⟨i, hi, hiz, hd1⟩ := memZipEq h1
  obtain ⟨j, hj, hjz, hd2⟩ := memZipEq h2
  have hf1 : f[i]'hi = d1.1 := congrArg Prod.fst hd1
  have hf2 : f[j]'hj = d2.1 := congrArg Prod.fst hd2
  have hij : i = j :=
    (hn.getElem_inj_iff (hi := hi) (hj := hj)).mp (by rw [hf1, hf2, h])
  subst hij
  rw [← hd1, ← hd2]

/-! ### §5 node 轨道运输（iso_list_normal_node 的私有引擎） -/

/-- 私件（批 1 perm_pow_transport 的 pair-lift 特形）：nodeMap 幂经 pair-lift
共轭（归纳步用 PermutesOn 保轨 + 交换律在 dart 集上）。 -/
private theorem nodeMapPowLift {L L' : fgraph ℕ} {hL : GoodList L}
    {hL' : GoodList L'} {phi : ℕ → ℕ}
    (hcomm : ∀ z ∈ listOfDarts L, (hypermapOfList L' hL').nodeMap
        (phi z.1, phi z.2)
      = (phi ((hypermapOfList L hL).nodeMap z).1,
         phi ((hypermapOfList L hL).nodeMap z).2))
    (n : ℕ) :
    ∀ w ∈ listOfDarts L,
      ((hypermapOfList L' hL').nodeMap ^ n) (phi w.1, phi w.2)
        = (phi (((hypermapOfList L hL).nodeMap ^ n) w).1,
           phi (((hypermapOfList L hL).nodeMap ^ n) w).2) := by
  induction n with
  | zero => intro w _; rfl
  | succ k ih =>
    intro w hw
    have hwD : w ∈ (hypermapOfList L hL).darts := List.mem_toFinset.mpr hw
    have hPw : ((hypermapOfList L hL).nodeMap) w
        ∈ (hypermapOfList L hL).darts :=
      (hypermapOfList L hL).nodeMap_permutes.apply_mem hwD
    have hPwL : ((hypermapOfList L hL).nodeMap) w ∈ listOfDarts L :=
      List.mem_toFinset.mp hPw
    show ((hypermapOfList L' hL').nodeMap ^ k)
        ((hypermapOfList L' hL').nodeMap (phi w.1, phi w.2))
      = (phi (((hypermapOfList L hL).nodeMap ^ k)
          ((hypermapOfList L hL).nodeMap w)).1,
         phi (((hypermapOfList L hL).nodeMap ^ k)
          ((hypermapOfList L hL).nodeMap w)).2)
    rw [hcomm w hw, ih _ hPwL]

/-- 私件（批 1 perm_orbitMap_image 的 pair-lift 特形）：node 轨道在 pair-lift
下的像刻画（`components_iso_image` 的 node 分量；通用形留 TameList1 私有层）。 -/
private theorem nodeLiftImage {L L' : fgraph ℕ} {hL : GoodList L}
    {hL' : GoodList L'} {phi : ℕ → ℕ}
    (hcomm : ∀ z ∈ listOfDarts L, (hypermapOfList L' hL').nodeMap
        (phi z.1, phi z.2)
      = (phi ((hypermapOfList L hL).nodeMap z).1,
         phi ((hypermapOfList L hL).nodeMap z).2))
    {d : ℕ × ℕ} (hd : d ∈ listOfDarts L) :
    (hypermapOfList L' hL').node (phi d.1, phi d.2)
      = (fun u : ℕ × ℕ => (phi u.1, phi u.2)) ''
        (hypermapOfList L hL).node d := by
  show orbitMap (hypermapOfList L' hL').nodeMap (phi d.1, phi d.2)
      = (fun u : ℕ × ℕ => (phi u.1, phi u.2)) ''
        orbitMap (hypermapOfList L hL).nodeMap d
  ext y
  simp only [orbitMap, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨((hypermapOfList L hL).nodeMap ^ n) d, ⟨n, rfl⟩,
      (nodeMapPowLift hcomm n d hd).symm⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨n, hn⟩ := hz
    exact ⟨n, (nodeMapPowLift hcomm n d hd).trans
      (congrArg (fun u : ℕ × ℕ => (phi u.1, phi u.2)) hn)⟩

/-- 私件：`n_list` 沿 pair-lift 运输（`find_face_map`（批 1）+
`prev_el_MEM_map`（Kepler.Text.TameLp.la7_prevEl_map）+ `e_list_fun` 链）。 -/
private theorem nListLift {L L' : fgraph ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) (hL'eq : L' = L.map (List.map phi))
    {z : ℕ × ℕ} (hz : z ∈ listOfDarts L) :
    nList L' (phi z.1, phi z.2) = (phi (nList L z).1, phi (nList L z).2) := by
  have hmem : z ∈ findFaceDarts L z := Kepler.Text.TameLp.la7_dart_in_findFace L z hz
  have hinj' : ∀ u ∈ findFaceDarts L z, ∀ v ∈ findFaceDarts L z,
      (fun t : ℕ × ℕ => (phi t.1, phi t.2)) u
        = (fun t : ℕ × ℕ => (phi t.1, phi t.2)) v → u = v :=
    fun u hu v hv huv => injOnLiftListOfDarts L hinj
      (Kepler.Text.TameLp.mem_darts_of_mem_findFace L hu) (Kepler.Text.TameLp.mem_darts_of_mem_findFace L hv) huv
  show eList (prevEl (findFaceDarts L' (phi z.1, phi z.2)) (phi z.1, phi z.2))
      = (phi (eList (prevEl (findFaceDarts L z) z)).1,
         phi (eList (prevEl (findFaceDarts L z) z)).2)
  rw [hL'eq, findFace_map_injOn hinj z hz,
    Kepler.Text.TameLp.la7_prevEl_map (f := fun t : ℕ × ℕ => (phi t.1, phi t.2))
      hinj' hmem]
  rfl

/-- HOL `iso_list_normal_node`（tame_list.hl:4120-:4163
`good_list L /\ normal_list L N /\ MEM d' (flatten N') /\
iso_list (L,N) (L',N') ==> node (hypermap_of_list L') d' SUBSET
set_of_list (flatten N')`）——node 轨道像运输（nodeLiftImage）+
normal_list 末合取项 + flatten-MAP 提升。 -/
theorem isoListNormalNode {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (h : NormalListSpine hL N)
    (hiso : IsoListSpine L L' N N') :
    ∀ d' ∈ N'.flatten,
      (hypermapOfList L' (isoListSpine_goodList hiso hL)).node d'
        ⊆ {d | d ∈ N'.flatten} := by
  obtain ⟨phi, hinj, hL'eq, hN'eq⟩ := hiso
  have hL'g : GoodList L' := isoListSpine_goodList ⟨phi, hinj, hL'eq, hN'eq⟩ hL
  have hmem : ∀ x ∈ N.flatten, x ∈ listOfDarts L := normalListListOfDarts h
  have hcomm : ∀ z ∈ listOfDarts L,
      (hypermapOfList L' hL'g).nodeMap (phi z.1, phi z.2)
        = (phi ((hypermapOfList L hL).nodeMap z).1,
           phi ((hypermapOfList L hL).nodeMap z).2) := by
    intro z hz
    have hzl : (phi z.1, phi z.2) ∈ listOfDarts L' := by
      rw [hL'eq, Kepler.Text.TameLp.la7_listOfDarts_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    have h1 := Kepler.Text.TameLp.nodeMap_hypermapOfList L' hL'g
      (List.mem_toFinset.mpr hzl)
    rw [h1, nListLift hinj hL'eq hz,
      Kepler.Text.TameLp.nodeMap_hypermapOfList L hL (List.mem_toFinset.mpr hz)]
  intro d' hd'
  rw [hN'eq] at hd'
  obtain ⟨s, hs, hd's⟩ := List.mem_flatten.mp hd'
  rw [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [List.mem_map] at hd's
  obtain ⟨d, hd, rfl⟩ := hd's
  have hdD : d ∈ listOfDarts L := hmem d (List.mem_flatten.mpr ⟨t, ht, hd⟩)
  rw [nodeLiftImage hcomm hdD]
  intro y hy
  simp only [Set.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' := h.2.2.2.2 d (List.mem_flatten.mpr ⟨t, ht, hd⟩) hz
  obtain ⟨s', hs'', hz's⟩ := List.mem_flatten.mp hz'
  show (phi z.1, phi z.2) ∈ N'.flatten
  rw [hN'eq, List.mem_flatten]
  refine ⟨s'.map (fun t : ℕ × ℕ => (phi t.1, phi t.2)),
    List.mem_map.mpr ⟨s', hs'', rfl⟩, ?_⟩
  exact List.mem_map.mpr ⟨z, hz's, rfl⟩

/-! ### §6 capstone：iso_list_normal（tame_list.hl:4166-:4189） -/

/-- **HOL `iso_list_normal`**（tame_list.hl:4166-:4186
`good_list L /\ iso_list (L,N) (L',N') /\ normal_list L N ==> normal_list L' N'`，
别名 `XKDZKWV` :4189）——normal_list 五合取沿 iso_list 整体运输：
uniq_flatten / all_nonnil / f_last / loop_list 四支各由本批运输件收口，
末支 node-子集由 iso_list_normal_node 给出。 -/
theorem isoListNormal {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (hiso : IsoListSpine L L' N N')
    (h : NormalListSpine hL N) :
    NormalListSpine (isoListSpine_goodList hiso hL) N' := by
  refine ⟨isoListUniqFlatten h hiso, isoListAllNonnil h hiso,
    isoListFLast h hiso, isoListAllLoopList h hiso, ?_⟩
  exact isoListNormalNode h hiso

/-- HOL 原名 `XKDZKWV` 的别名件（tame_list.hl:4189
`let XKDZKWV = iso_list_normal;;`，逐字同体，供下游按 HOL 名检索）。 -/
theorem XKDZKWV {L L' : fgraph ℕ} {hL : GoodList L}
    {N N' : List (List (ℕ × ℕ))} (hiso : IsoListSpine L L' N N')
    (h : NormalListSpine hL N) :
    NormalListSpine (isoListSpine_goodList hiso hL) N' :=
  isoListNormal hiso h

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.isoListNormal
#print axioms Kepler.Text.TameSpine.isoListNormalNode
#print axioms Kepler.Text.TameSpine.isoListFLast
#print axioms Kepler.Text.TameSpine.isoListAllLoopList
#print axioms Kepler.Text.TameSpine.injNumExists
#print axioms Kepler.Text.TameSpine.listPairsUnique
-/
