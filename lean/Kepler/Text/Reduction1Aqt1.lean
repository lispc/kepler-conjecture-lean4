/-
  Kepler.Text.Reduction1Aqt1 — J4/A 战役 AUQTZYZ 主定理批（① 判词 + ② 陈述定案 +
  EPC 槽形）。**本文件只立陈述（纯缩写 `def : Prop`，零证明义务）**，主定理本体
  （HOL AUQTZYZ.hl:1859-:2624，765 行）留后续波次；冻结表见 DELIVERY_AQT1 §4。

  三件：
  · `ExistsPathComplementSlot` —— 批 ①（aq13 车道）`EXISTS_PATH_COMPLEMENT`
    （AUQTZYZ.hl:574-:1850，1,277 行）结论的逐字槽形（十二合取）。批 ① 落库后
    一行消槽；本批主定理（批 ②）以它为显式假设推进。
  · `AuqtzyzConcl` —— 批 ② 陈述逐字（AUQTZYZ.hl:1851-:1857 的
    `AUQTZYZ_concl`）：`!H x L1. is_restricted H /\ x IN dart H /\
    L1 = loop_of_face H x ==> ?L2. is_normal H {L1,L2} /\
    path_of_loop L2 (complement H x 0) = complement H x /\
    dih2k (quotient H {L1,L2}) (CARD (face H x))`。
  · `auqtzyzConcl_iff_shape` —— 两个陈述的载体形状探针（`#check` 级，见文件尾）。

  **载体折算（逐槽，按 Hypermap.lean 头注 coverage map 实测）**：
  · `Hypermap α`（generic A；本仓 `Hypermap` 结构含 dart Finset + 三置换，
    `H.darts : Finset α`；HOL `dart H` 是集合，`x IN dart H` ↦ `x ∈ H.darts`）。
  · `is_restricted H` ↦ `H.IsRestricted`（Hypermap.lean:9644，HOL hypermap.hl:11174）。
  · `L1 = loop_of_face H x` ↦ `L1 = H.loopOfFace x`（Hypermap.lean:8359，
    HOL :10053）。
  · `is_normal H NF` ↦ `H.IsNormalFamily NF`（Hypermap.lean:6808，HOL :8122，
    `Set (Loop α)` 载体）。
  · `path_of_loop L x` ↦ `Loop.pathOf L x : ℕ → α`（Hypermap.lean:5737，HOL :6730
    `\k. (loop_map L POWER k) x`）——**函数等式**，故写成 `∀ k, … k = … k`。
  · `complement H x 0` ↦ `H.complementPt x 0`；`complement H x`（函数）↦
    `fun k => H.complementPt x k`（Hypermap.lean:9155，HOL :10662 的对角点；HOL
    `complement` 本身即 `\i. complement_aux … i i`，本仓无独立 `complement`
    def，用对角点逐点写）。
  · `in_dart_of_loop y L` ↦ `y ∈ L.darts`；`dart_of_loop L INTER face H x = {}` ↦
    `(↑L.darts : Set α) ∩ H.face x = ∅`；`atoms_of_loop H L` ↦ `H.atomsOfLoop L`
    （Hypermap.lean:7939）；`CARD` ↦ `Set.ncard`；`atom H L x` ↦ `H.atom L x`
    （Hypermap.lean:6566）；`inv_loop_map L` ↦ `L.invMap`（Hypermap.lean:5724）；
    `inverse (node_map H)` ↦ `H.nodeMap.symm`（Perm 的 symm）。
  · `is_loop H L` ↦ `L.IsLoopOf H`（Hypermap.lean:5726，HOL :6726）。
  · `dih2k (quotient H NF) k` ↦ `dih2k_p3 (H.quotientHypermap hnf) k`
    （LocalAuto3.lean:127；`quotientHypermap` 需 `hnf : H.IsNormalFamily NF`
    （Hypermap.lean:7744），故 `is_normal` 合取以 ∃-证人形入结论——
    `∃ L2, is_normal ∧ A` 与 `∃ L2 (hnf : is_normal), A` 定义性等价，
    Prop 证明无关）。
  · `node H y` ↦ `H.node y`；`face H x` ↦ `H.face x`；`face_map H`/`node_map H`
    ↦ `H.faceMap`/`H.nodeMap`（Equiv.Perm，作函数用）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Hypermap
import Kepler.Text.LocalAuto3
import Kepler.Text.TameSpine.TameList60
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap)

/-! ## §1 批 ① 槽：`EXISTS_PATH_COMPLEMENT` 结论逐字 -/

/-- **HOL `EXISTS_PATH_COMPLEMENT`**（AUQTZYZ.hl:574-:1850，批 ① = aq13 车道）
结论的逐字槽形（十二合取）：

`!H x. is_restricted H /\ x IN dart H ==> ?L. is_loop H L /\
 path_of_loop L (complement H x 0) = complement H x /\
 in_dart_of_loop (complement H x 0) L /\
 (?y z. in_dart_of_loop y L /\ in_dart_of_loop z L /\ ~(node H y = node H z)) /\
 dart_of_loop L INTER (face H x) = {} /\
 (!y z. in_dart_of_loop y L /\ z IN node H y ==> in_dart_of_loop z L \/ z IN face H x) /\
 (!y z. y IN face H x /\ z IN node H y ==> in_dart_of_loop z L \/ z IN face H x) /\
 CARD (atoms_of_loop H L) = CARD (face H x) /\
 (atoms_of_loop H L) INTER {y | ?x1. y = atom H (loop_of_face H x) x1 /\
   in_dart_of_loop x1 (loop_of_face H x)} = {} /\
 (!x1. in_dart_of_loop x1 L ==> ?y. y IN atom H L x1 /\ y = face_map H (inv_loop_map L y) /\
   node_map H y IN face H x /\ (node_map H (node_map H y)) IN atom H L x1) /\
 (!x1. x1 IN face H x ==> ?y. y IN atom H L (inverse (node_map H) x1) /\
   y = face_map H (inv_loop_map L y) /\ x1 = node_map H y /\
   inverse (node_map H) x1 IN dart_of_loop L) /\
 (!x1. x1 IN face H x ==> in_dart_of_loop (node_map H x1) L)`。

**纯缩写 `def : Prop`（零证明义务）**：批 ① 落库后主定理（批 ②）一行消槽。
槽的 `?L` 是全称型：本槽形把 `∀ x` 收在同一实例内（每次调用给具体 `x`）。 -/
def ExistsPathComplementSlot {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) : Prop :=
  H.IsRestricted → x ∈ H.darts →
    ∃ L : Loop α,
      L.IsLoopOf H ∧
      (∀ k : ℕ, L.pathOf (H.complementPt x 0) k = H.complementPt x k) ∧
      (H.complementPt x 0) ∈ L.darts ∧
      (∃ y ∈ L.darts, ∃ z ∈ L.darts, H.node y ≠ H.node z) ∧
      ((↑L.darts : Set α) ∩ H.face x = ∅) ∧
      (∀ y ∈ L.darts, ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x) ∧
      (∀ y, y ∈ H.face x → ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x) ∧
      (H.atomsOfLoop L).ncard = (H.face x).ncard ∧
      (H.atomsOfLoop L ∩
        {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
          x1 ∈ (H.loopOfFace x).darts} = ∅) ∧
      (∀ x1, x1 ∈ L.darts →
        ∃ y, y ∈ H.atom L x1 ∧ y = H.faceMap (L.invMap y) ∧
          H.nodeMap y ∈ H.face x ∧ H.nodeMap (H.nodeMap y) ∈ H.atom L x1) ∧
      (∀ x1, x1 ∈ H.face x →
        ∃ y, y ∈ H.atom L (H.nodeMap.symm x1) ∧
          y = H.faceMap (L.invMap y) ∧ x1 = H.nodeMap y ∧
          H.nodeMap.symm x1 ∈ L.darts) ∧
      (∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts)

/-! ## §2 批 ② 陈述：`AUQTZYZ_concl` 逐字 -/

/-- **HOL `AUQTZYZ_concl`**（AUQTZYZ.hl:1851-:1857）逐字：
`!H (x:A) L1. is_restricted H /\ (x IN dart H) /\ (L1 = loop_of_face H x) ==>
(?L2. is_normal H {L1,L2} /\
  (path_of_loop L2 (complement H x 0) = complement H x) /\
  dih2k (quotient H {L1,L2}) (CARD (face H x)))`。
`is_normal` 合取以 ∃-证人 `hnf` 入结论（`quotientHypermap` 在 Lean 侧需它作
显式参数；Prop 证明无关，形状等价）。 -/
def AuqtzyzConcl {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α)
    (L1 : Loop α) : Prop :=
  H.IsRestricted → x ∈ H.darts → L1 = H.loopOfFace x →
    ∃ L2 : Loop α, ∃ hnf : H.IsNormalFamily ({L1, L2} : Set (Loop α)),
      (∀ k : ℕ, L2.pathOf (H.complementPt x 0) k = H.complementPt x k) ∧
      dih2k_p3 (H.quotientHypermap hnf) (H.face x).ncard

/-- `AUQTZYZ_concl` 的全称闭包形（HOL 的 `!H x L1.` 打包；HOL 类型 A 泛化，
Lean 侧对 `Type*` 全称——本仓 Hypermap 层同款泛型）。 -/
def Auqtzyz : Prop :=
  ∀ {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) (L1 : Loop α),
    AuqtzyzConcl H x L1

/-! ## §3 批 ② 的小缺口桥件（HOL 原名零命中 → 按语义在库件 ~40 行重推） -/

-- 注：以下六件是 AUQTZYZ 主证体（:1859-:2624）消费、而按 HOL 原名全树零命中的
-- 「真缺口」——语义全在库（Hypermap 层/ mathlib ncard），只差这层薄桥。

/-- **HOL `Rnsyjxm.in_face_imp_in_dart`**（RNSYJXM-compiled.hl:27）：
`x IN dart H /\ d IN face H x ==> d IN dart H`。 -/
theorem inFaceImpInDart {α : Type*} [DecidableEq α] {H : Hypermap α} {x d : α}
    (hx : x ∈ H.darts) (hd : d ∈ H.face x) : d ∈ H.darts :=
  H.face_subset_darts hx hd

/-- **HOL `Rnsyjxm.face_face_map_eq`**（RNSYJXM-compiled.hl:43）：
`face H (face_map H d) = face H d`（轨道同点同一性）。 -/
theorem faceFaceMapEq {α : Type*} [DecidableEq α] (H : Hypermap α) (d : α) :
    H.face (H.faceMap d) = H.face d :=
  Kepler.Text.orbitMap_eq_of_mem H.faceMap_permutes
    (Kepler.Text.Hypermap.pow_faceMap_mem_face H d 1)

/-- **HOL `Lunar_deform.IN_DART_PRESERVED`**（lunar_deform.hl:2931）：
三映射的 dart 集保持（双向）。 -/
theorem inDartPreserved {α : Type*} [DecidableEq α] (H : Hypermap α) :
    (∀ x : α, H.faceMap x ∈ H.darts ↔ x ∈ H.darts) ∧
    (∀ x : α, H.nodeMap x ∈ H.darts ↔ x ∈ H.darts) ∧
    (∀ x : α, H.edgeMap x ∈ H.darts ↔ x ∈ H.darts) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨fun h => by
      rw [← H.faceMap.symm_apply_apply x]
      exact H.faceMap_symm_apply_mem h, H.faceMap_apply_mem⟩
  · intro x
    exact ⟨fun h => by
      rw [← H.nodeMap.symm_apply_apply x]
      exact H.nodeMap_symm_apply_mem h, H.nodeMap_apply_mem⟩
  · intro x
    exact ⟨fun h => by
      rw [← H.edgeMap.symm_apply_apply x]
      exact H.edgeMap_symm_apply_mem h, H.edgeMap_apply_mem⟩

/-- **HOL `Ysskqoy.CARD_UNION_EQ`**（YSSKQOY.hl:107）：
`FINITE u /\ s INTER t = {} /\ s UNION t = u ==> CARD s + CARD t = CARD u`。
mathlib `Set.ncard_union_eq` + 子集有限性。 -/
theorem cardUnionEq {α : Type*} {s t u : Set α} (hu : u.Finite) (hdisj : s ∩ t = ∅)
    (hunion : s ∪ t = u) : s.ncard + t.ncard = u.ncard := by
  have hs : s.Finite := hu.subset (by rw [← hunion]; exact Set.subset_union_left)
  have ht : t.Finite := hu.subset (by rw [← hunion]; exact Set.subset_union_right)
  rw [← hunion,
    Set.ncard_union_eq (by rw [Set.disjoint_iff_inter_eq_empty]; exact hdisj) hs ht]

/-- **HOL `Lvducxu.FACE_CYCLE_CARD`**（LVDUCXU.hl:1805）：
`y IN face H x ==> (face_map H POWER CARD (face H x)) y = y`——
`pow_card_face_apply_self`（`(faceMap^N) x = x`）沿轨道搬运。 -/
theorem faceCycleCard {α : Type*} [DecidableEq α] (H : Hypermap α) {x y : α}
    (hy : y ∈ H.face x) : (H.faceMap ^ (H.face x).ncard) y = y := by
  obtain ⟨k, hk⟩ := hy
  rw [← hk]
  have hstep : (H.faceMap ^ (H.face x).ncard) ((H.faceMap ^ k) x)
      = (H.faceMap ^ k) ((H.faceMap ^ (H.face x).ncard) x) := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add,
      Nat.add_comm]
  rw [hstep, H.pow_card_face_apply_self]

/-- **HOL `Wrgcvdr_cizmrrh.DIH_IMP_EVERY_NODE_INTER_FACE`**（WRGCVDR.hl:717）：
`dih2k H k ==> (!x y. {x,y} SUBSET dart H ==> ?d. d IN node H x /d IN face H y)`——取 `dih2k` 第二合取（`dart = face y ∪ node_map '' face y`）二分。 -/
theorem dihImpEveryNodeInterFace {α : Type*} [DecidableEq α] {H : Hypermap α} {k : ℕ}
    (hd : Kepler.Text.dih2k_p3 H k) {x y : α} (hx : x ∈ H.darts)
    (hy : y ∈ H.darts) : ∃ d : α, d ∈ H.node x ∧ d ∈ H.face y := by
  have hunion : (↑H.darts : Set α) = H.face y ∪ (H.nodeMap : α → α) '' H.face y :=
    hd.2.1 y hy
  rcases (by rw [← hunion]; exact hx : x ∈ H.face y ∪ (H.nodeMap : α → α) '' H.face y) with
    h1 | ⟨s, hs, hxs⟩
  · exact ⟨x, H.mem_node_self x, h1⟩
  · refine ⟨s, ?_, hs⟩
    have hsx : s = H.nodeMap.symm x := by
      rw [← hxs, H.nodeMap.symm_apply_apply s]
    have hmem : s ∈ Kepler.Text.orbitMap H.nodeMap.symm x := by
      rw [hsx]
      simpa using Kepler.Text.pow_apply_mem_orbitMap H.nodeMap.symm 1 x
    rwa [Kepler.Text.PermutesOn.orbitMap_symm H.nodeMap_permutes] at hmem

end Kepler.Text.Reduction1

/-! 形状探针（编译即执行；本文件无定理，只有陈述缩写） -/
#check @Kepler.Text.Reduction1.ExistsPathComplementSlot
#check @Kepler.Text.Reduction1.AuqtzyzConcl
#check @Kepler.Text.Reduction1.Auqtzyz
#print axioms Kepler.Text.Reduction1.inFaceImpInDart
#print axioms Kepler.Text.Reduction1.faceFaceMapEq
#print axioms Kepler.Text.Reduction1.inDartPreserved
#print axioms Kepler.Text.Reduction1.cardUnionEq
#print axioms Kepler.Text.Reduction1.faceCycleCard
#print axioms Kepler.Text.Reduction1.dihImpEveryNodeInterFace
