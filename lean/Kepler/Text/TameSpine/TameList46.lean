/-
  Kepler.Text.TameSpine.TameList46 — B1 Tame_list 地基批 46：
  connected_hypermap 章开章（tamespine-port-plan §4 批次表 B1 行；
  接续批 45 = TameList45.lean，批 45 终点 = HOL :12656；本批起点 =
  HOL :12658 `connected_induction`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  定义层侦察结论（批 45 尾处方预记对拍面，经主仓全库 grep（含
  LocalAuto 族）+ 工具链 core v4.32.2/mathlib/batteries 三处对拍
  复核）：connected_hypermap 概念面的 Lean 载体 =
  Kepler.Text.Hypermap **全族在册，零新 def，本批纯消费**：
  - `connected_hypermap`（hypermap.hl:1000）↦ `Hypermap.Connected`
    （Hypermap.lean:1633，= numberOfComponents = 1）；
  - `number_of_components`（:175）↦ `Hypermap.numberOfComponents`
    （:1047，= setOfComponents.ncard）；
  - `set_of_components`（:152）↦ `Hypermap.setOfComponents`（:1033）；
  - `comb_component`（:142）↦ `Hypermap.combComponent`（:917）；
  - `is_in_component`（:140）↦ `Hypermap.isInComponent`（:913）；
  - `is_path`（:135）↦ `Hypermap.isPath`（:877）、`go_one_step`
    （:131）↦ `Hypermap.goOneStep`（:873）；
  - `one_step_contour`（:1455）↦ `Hypermap.oneStepContour`（:1661）、
    `is_contour`（:1457）↦ `Hypermap.isContour`（:1665）、
    `lemma_def_contour`（:1468）↦ `Hypermap.isContour_iff`（:1693）、
    `existence_contour`（:1530）↦ `Hypermap.existence_contour`
    （:1767；Hypermap.lean 自证路线与 HOL 不同：edge 步 =
    nodeMap.symm 一步 + faceMap 幂、node 步 = nodeMap.symm 幂，均出
    有限阶——如实记档，消费面零感知）；
  - `lemma_in_components`（:4003）↦
    `Hypermap.mem_darts_iff_combComponent_mem`（:3686）、
    `lemma_partition_by_components`（:1439）↦
    `Hypermap.sUnion_setOfComponents`（:1544）、
    `FINITE_HYPERMAP_COMPONENTS`（:3976）↦
    `Hypermap.setOfComponents_finite`（:1043，本批未被消费——
    HOL set_one_point 的 FINITE 槽由 Mathlib ncard = 1 语义吸收）；
  - HOL 库件 `set_one_point`（+ FINITE 槽单点化）折算 = Mathlib
    `Set.ncard_eq_one`（Data/Set/Card.lean:1252，`s.ncard = 1 ↔
    ∃ a, s = {a}`）；`UNIONS` 单点展开 = Mathlib
    `Set.sUnion_singleton`（Data/Set/Lattice.lean:853）；
  - `lemma_inverse_in_node` 面（件二 MATCH_MP_TAC 槽）↦
    `Hypermap.nodeMap_symm_mem_node`（:8587）+ `mem_node_self`
    （:859）组合（HOL node_refl 槽 = mem_node_self 面）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:12658-:12758）：

  件一：`connected_induction` :12658-:12705（章开章）
  `!H S. connected_hypermap H /\ S SUBSET (dart H) /\ ~(S = {}) /\
  (!x. x IN S ==> face_map H x IN S /\ inverse (node_map H) x IN S)
  ==> (S = dart H)` ↦ `connectedInduction`（真证）。HOL 证体
  EXTENSION 两向 + set_of_components 单点化（set_one_point +
  FINITE_HYPERMAP_COMPONENTS）+ lemma_partition_by_components 收
  dart H = comb_component H x₀ + existence_contour/lemma_def_contour
  沿 contour 逐点走 S 封闭归纳。Lean 面同链：Set.ext 两向 +
  Set.ncard_eq_one 单点化 + sUnion_setOfComponents +
  Set.sUnion_singleton 收 dart 面 + existence_contour + isContour_iff
  逐点 + ∀ i ≤ m 归纳（~(S = {}) 经 EXTENSION + NOT_FORALL 取 ∈S
  证人形 ↦ Set.Nonempty）。

  件二：`normal_list_ivs_node_map` :12707-:12721
  `!L N x. normal_list L N /\ MEM x (flatten N) ==> MEM (inverse
  (node_map (hypermap_of_list L)) x) (flatten N)` ↦
  `normalListIvsNodeMap`（真证）。NormalListSpine 合取项 5（node ⊆
  flatten 集）+ nodeMap_symm_mem_node + mem_node_self 三件项式直投。

  件三（章 capstone）：`normal_list_complete` :12723-:12758
  `!L N. good_list L /\ connected_hypermap (hypermap_of_list L) /\
  ~(N = []) /\ normal_list L N /\
  (!x. MEM x (flatten N) ==> MEM (f_list L x) (flatten N)) ==>
  set_of_list (flatten N) = darts_of_list L` ↦ `normalListComplete`
  （真证）。connected_induction 装配：S = {d | d ∈ flatten N}，
  子集槽 = normalListListOfDarts + dartHypermapOfList、非空槽 =
  N ≠ [] + 合取项 2（all-nonnil）、封闭槽 = faceMap_hypermapOfList
  （f_list 换装）+ normalListIvsNodeMap；收口 dartHypermapOfList。

  载体折算盘点（批 45 尾预记侦察面，经全库 grep（含 LocalAuto 族）
  + 工具链（core v4.32.2/mathlib/batteries 三处）对拍复核）：
  - `normal_list` = 批 5 NormalListSpine（TameList5.lean:127，五
    合取项；本批消费合取项 2（all-nonnil 非空槽）与合取项 5
    （node ⊆ flatten 集，件二直投槽））；
  - `dart_hypermap_of_list`（tame_list.hl:4095）= 批 5
    dartHypermapOfList（TameList5.lean:445）；
  - `normal_list_list_of_darts`（tame_list.hl:3643）= 批 5
    normalListListOfDarts（TameList5.lean:146）；
  - `face_map_list` 面（face_map (hypermap_of_list L) x = f_list L x）
    = TameLp faceMap_hypermapOfList（TameLp.lean:4043）；
  - `hypermap_of_list` ↦ TameLp hypermapOfList（TameLp.lean:3993，
    Hypermap (ℕ × ℕ) 载体；f_list/e_list/n_list ↦ Assembly 件）；
  - connectedInduction 陈述按 hypermap.hl 泛型 α 镜像（Hypermap.lean
    全族同泛型；[DecidableEq α] 槽为消费件 instance 需求，HOL 类型
    层无约束、陈述面不受影响）。
  全库 grep（含 LocalAuto 族 + core/mathlib/batteries 三处）
  connectedInduction/normalListIvsNodeMap/normalListComplete 三件名
  零撞车零现成载体——镜像本体即本批件。

  新落地载体：零（定义层全在 Hypermap.lean 在册，装配槽全在批 5/
  TameLp 既有件——本批纯消费批）。私件：零。

  诚实记账：三件全真证，零新 def、零 sorry、零止损件、零记账债。
  范围决策：批 46 射程收口至 :12758（connected_induction 章开章 +
  connectivity 在 tame_list 侧两应用件，自然边界 = final_list 章
  开章前）；:12760 `final_list_complete`（normal_list_complete 直投
  + final_list 谓词展开）留批 47。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 47 接续点：HOL :12760 `final_list_complete`（连通章收口后
  final_list 运输面开章；消费批 46 normalListComplete 直投，
  final_list = all (final_list L) N 谓词展开 + Seq2.mem_flatten 面
  + batch 既有 finalListSpine 槽对拍）。
-/

import Kepler.Text.TameSpine.TameList45

namespace Kepler.Text.TameSpine

open Kepler.Assembly (GoodList listOfDarts fList)
open Kepler.Graphs (fgraph)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList faceMap_hypermapOfList)

/-! ### §1 connected_induction（tame_list.hl:12658-:12705，章开章） -/

/-- **HOL `connected_induction`**（tame_list.hl:12658-:12705）
`!H S. connected_hypermap H /\ S SUBSET (dart H) /\ ~(S = {}) /\
(!x. x IN S ==> face_map H x IN S /\ inverse (node_map H) x IN S)
==> (S = dart H)`——EXTENSION 两向 + set_of_components 单点化
（HOL set_one_point 槽 ↦ Mathlib Set.ncard_eq_one）+
lemma_partition_by_components（↦ sUnion_setOfComponents）收
dart = comb_component + existence_contour/lemma_def_contour（↦
Hypermap 在册件）沿 contour 逐点 S 封闭归纳。定义层侦察：
connected_hypermap 概念面 Lean 载体 = Hypermap.lean 全族在册
（头注锚点表），零新 def 纯消费。 -/
theorem connectedInduction {α : Type*} [DecidableEq α] {H : Hypermap α}
    (hconn : H.Connected) {S : Set α} (hsub : S ⊆ ↑H.darts)
    (hne : S.Nonempty)
    (hstep : ∀ x ∈ S, H.faceMap x ∈ S ∧ H.nodeMap.symm x ∈ S) :
    S = ↑H.darts := by
  -- 非空证人 x₀ ∈ S + 单点化：set_of_components H = {comb_component H x₀}
  obtain ⟨x₀, hx₀⟩ := hne
  have h1 : H.setOfComponents.ncard = 1 := hconn
  have hmem : H.combComponent x₀ ∈ H.setOfComponents :=
    (H.mem_darts_iff_combComponent_mem x₀).mp (hsub hx₀)
  obtain ⟨C, hC⟩ := Set.ncard_eq_one.mp h1
  have hCx : C = H.combComponent x₀ := by
    rw [hC] at hmem
    exact (Set.mem_singleton_iff.mp hmem).symm
  -- dart H = comb_component H x₀（lemma_partition_by_components + 单点展开）
  have hdart : ↑H.darts = H.combComponent x₀ := by
    rw [H.sUnion_setOfComponents, hC, hCx]
    exact Set.sUnion_singleton _
  -- 主向：dart H 逐点经 contour 走入 S
  refine Set.ext fun y => ⟨fun hyS => hsub hyS, fun hyD => ?_⟩
  have hycomp : y ∈ H.combComponent x₀ := by
    rw [← hdart]
    exact hyD
  obtain ⟨p, n, hp0, hpn, hpath⟩ := hycomp
  obtain ⟨q, m, hq0, hqm, hcont⟩ := H.existence_contour hpath
  have key : ∀ i : ℕ, i ≤ m → q i ∈ S := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hq0, hp0]
      exact hx₀
    | succ k ih =>
      intro hkm
      have hkS : q k ∈ S := ih (Nat.le_of_succ_le hkm)
      rcases (H.isContour_iff q m).mp hcont k (by omega) with h | h
      · rw [h]
        exact (hstep _ hkS).1
      · rw [h]
        exact (hstep _ hkS).2
  rw [← hpn, ← hqm]
  exact key m le_rfl

/-! ### §2 normal_list_ivs_node_map（tame_list.hl:12707-:12721） -/

/-- **HOL `normal_list_ivs_node_map`**（tame_list.hl:12707-:12721）
`!L N x. normal_list L N /\ MEM x (flatten N) ==> MEM (inverse
(node_map (hypermap_of_list L)) x) (flatten N)`——NormalListSpine
合取项 5（node ⊆ flatten 集）+ nodeMap_symm_mem_node + mem_node_self
三件项式直投（HOL node_refl 槽 = mem_node_self 面）。 -/
theorem normalListIvsNodeMap {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (h : NormalListSpine hL N) {x : ℕ × ℕ}
    (hx : x ∈ N.flatten) :
    (hypermapOfList L hL).nodeMap.symm x ∈ N.flatten :=
  h.2.2.2.2 x hx (Hypermap.nodeMap_symm_mem_node (hypermapOfList L hL)
    (Hypermap.mem_node_self (hypermapOfList L hL) x))

/-! ### §3 normal_list_complete（tame_list.hl:12723-:12758，章 capstone） -/

/-- **HOL `normal_list_complete`**（tame_list.hl:12723-:12758）
`!L N. good_list L /\ connected_hypermap (hypermap_of_list L) /\
~(N = []) /\ normal_list L N /\
(!x. MEM x (flatten N) ==> MEM (f_list L x) (flatten N)) ==>
set_of_list (flatten N) = darts_of_list L`——connected_induction
装配件：S = {d | d ∈ flatten N}，子集槽 = normalListListOfDarts +
dartHypermapOfList、非空槽 = N ≠ [] + 合取项 2（all-nonnil）、
封闭槽 = faceMap_hypermapOfList（f_list 换装）+
normalListIvsNodeMap；收口 dartHypermapOfList。 -/
theorem normalListComplete {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List (ℕ × ℕ))} (hconn : (hypermapOfList L hL).Connected)
    (hne : N ≠ []) (hnorm : NormalListSpine hL N)
    (hf : ∀ x ∈ N.flatten, fList L x ∈ N.flatten) :
    {d | d ∈ N.flatten} = {d | d ∈ listOfDarts L} := by
  -- 非空槽：N ≠ [] + all-nonnil 取证人
  have hneS : ({d | d ∈ N.flatten} : Set (ℕ × ℕ)).Nonempty := by
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil N hne
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil s (hnorm.2.1 s hs)
    exact ⟨d, List.mem_flatten.mpr ⟨s, hs, hd⟩⟩
  -- 子集槽：S ⊆ dart（normal_list_list_of_darts + dart_hypermap_of_list）
  have hsub : ({d | d ∈ N.flatten} : Set (ℕ × ℕ)) ⊆
      ↑(hypermapOfList L hL).darts := fun d hd => by
    rw [dartHypermapOfList L hL]
    exact normalListListOfDarts hnorm d hd
  -- 封闭槽：face_map 支（f_list 换装）+ inverse node_map 支（件二）
  have hstep : ∀ x ∈ ({d | d ∈ N.flatten} : Set (ℕ × ℕ)),
      (hypermapOfList L hL).faceMap x ∈ ({d | d ∈ N.flatten} : Set (ℕ × ℕ)) ∧
      (hypermapOfList L hL).nodeMap.symm x ∈ ({d | d ∈ N.flatten} : Set (ℕ × ℕ)) :=
    fun x hx =>
      ⟨by rw [faceMap_hypermapOfList L hL (hsub hx)]; exact hf x hx,
        normalListIvsNodeMap hnorm hx⟩
  -- connected_induction 收口 + dart_hypermap_of_list
  exact (connectedInduction hconn hsub hneS hstep).trans (dartHypermapOfList L hL)

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；三件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.connectedInduction
#print axioms Kepler.Text.TameSpine.normalListIvsNodeMap
#print axioms Kepler.Text.TameSpine.normalListComplete
-/
