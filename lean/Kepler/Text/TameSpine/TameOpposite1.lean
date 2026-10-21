/-
  Kepler.Text.TameSpine.TameOpposite1 — B2 叶件第一批：tame_opposite.hl 结构层
  （:23-:419：opposite_hypermap 四元组 / plain / components / simple /
   结构 eta / 对合 / 路径提升 / 分量集 / 连通 / 非退化 / plain-edge）。

  接续：本批覆盖 HOL :23-:419；批 2 从 `opposite_no_loops`（:395）起，
  含 edge_CARD_dart/edge_CARD/opposite_planar/CARD_faces1/CARD_in_face/
  CARD_nodes/CARD_in_node，批 3 收 the_SAME_orbit_* 家族 → tame_opposite_hypermap
  → PPHEUFG（:598 主定理）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │ 公开件 14（零 sorry 真证）：
  │ ① oppositeHypermap —— HOL `opposite_hypermap`（tame_defs.hl:185）泛型
  │   孪生，与 Assembly 同名件逐字同体（本模块不 import Assembly，接口
  │   sorry 污染纪律）；孪生归一登记待 W0/装配波。
  │ ② tupleOppositeHypermap（:23）四元组投影四等式。
  │ ③ oppositeHypermap_plain（:39，tame_1a）——群论核心：e=(n f)⁻¹ 与
  │   e²=1 推出 (n f)²=1，再共轭到 (f n)²=1。
  │ ④ oppositeComponents（:57）dart/node/face 三不变（orbitMap_symm）。
  │ ⑤ oppositeHypermap_simple（:77，tame_2b）。
  │ ⑥ hypermapEqLemma（:86）结构 eta（Lean 结构投影决定，rfl）。
  │ ⑦ oppositeOpposite（:100）对合（Hypermap.ext' + 群论）。
  │ ⑧ truncatedPathLemma（:117）= isPath_congr 的截断形。
  │ ⑨ oppositePath（:139）——HOL 三支逐步两跳：edge 步走 node→face，
  │   node 步走 edge→face，face 步走 node→edge；Lean 用 `if i ≤ m` 扩表
  │   m→m+2 + isPath_succ 双层展开。
  │ ⑩ oppositePathAlt（:243）反向（oppositeOpposite 折算）。
  │ ⑪ combComponentOpposite（:254 路径核）。
  │ ⑫ oppositeSetsOfComponents（:254）nodeSet/faceSet/setOfComponents 三不变。
  │ ⑬ oppositeHypermap_connected（:284，tame_2a）。
  │ ⑭ oppositeNondegenerate（:291，tame_3）+ plainHypermapEdge（:384）。
  │ 公理探针 14 件 = 标准三内零 sorryAx（hypermapEqLemma/truncatedPathLemma
  │ 仅 [propext, Quot.sound]）；构建纯 lake build 单发串行零旗标。
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测，编号承批 66 的 #167）：
  - **#168 let 绑定 if-函数的 simp 预判**：`have hq2 : q' (m+1) = a := by
    simp only [q']` 会把 `m+1 = m+1` 先判成 True，后续 `rw [if_pos rfl]`
    找不到模式；let 绑定函数取点须 `show (if ... then ... else ...) = ...`
    保持句法形，再两发 if_neg/if_pos。
  - **#169 change 不展开 set-builder 成员**：`t ∈ nodeSet` 的 `change` 目标
    写成 `∃ x, x ∈ darts ∧ t = orbitMap ...` 不 defeq；须先
    `simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq, ...]`。
  - **#170 rw 链尾重复 inv_inv**：`(e*e)⁻¹` 经 `mul_inv_rev` + `he`
    （e=(n f)⁻¹）后一发 `inv_inv` 已同时吃两处，第二发无模式即失败。
  - **#171 两跳模拟的方向敏感**：opposite 的 goOneStep 不能 1:1 提升；
    edge 步 = node 步 + face 步，node 步 = edge 步 + face 步，face 步 =
    node 步 + edge 步（中间点分别 n⁻¹x / f(n x) / n⁻¹x）。
  - **#172 isPath 双层展开的顺序**：`m+2` 先 `show (m+1)+1` 再
    `rw [isPath_succ, isPath_succ]`，否则 succ 匹配错位。
-/
import Kepler.Text.TameLp

namespace Kepler.Text.TameSpine

open Kepler.Text

variable {α : Type*} [DecidableEq α]

/-! ### §0 `opposite_hypermap` 泛型孪生

`Kepler.Assembly.oppositeHypermap` 同体，但本模块不 import Assembly
（接口 sorry 污染纪律）；孪生归一登记待 W0/装配波。 -/

/-- HOL `opposite_hypermap`（`tame_defs.hl:185`）。 -/
def oppositeHypermap (H : Hypermap α) : Hypermap α where
  darts := H.darts
  edgeMap := H.faceMap * H.nodeMap
  nodeMap := H.nodeMap.symm
  faceMap := H.faceMap.symm
  edgeMap_permutes := H.faceMap_permutes.mul H.nodeMap_permutes
  nodeMap_permutes := H.nodeMap_permutes.symm
  faceMap_permutes := H.faceMap_permutes.symm
  comp_eq_one := by
    have hnn : H.nodeMap * H.nodeMap.symm = 1 := mul_inv_cancel H.nodeMap
    have hff : H.faceMap * H.faceMap.symm = 1 := mul_inv_cancel H.faceMap
    rw [mul_assoc H.faceMap H.nodeMap H.nodeMap.symm, hnn, mul_one, hff]

@[simp] theorem oppositeHypermap_darts (H : Hypermap α) :
    (oppositeHypermap H).darts = H.darts := rfl

@[simp] theorem oppositeHypermap_edgeMap (H : Hypermap α) :
    (oppositeHypermap H).edgeMap = H.faceMap * H.nodeMap := rfl

@[simp] theorem oppositeHypermap_nodeMap (H : Hypermap α) :
    (oppositeHypermap H).nodeMap = H.nodeMap.symm := rfl

@[simp] theorem oppositeHypermap_faceMap (H : Hypermap α) :
    (oppositeHypermap H).faceMap = H.faceMap.symm := rfl

/-- HOL `tuple_opposite_hypermap`（`tame_opposite.hl:23`）。 -/
theorem tupleOppositeHypermap (H : Hypermap α) :
    (oppositeHypermap H).darts = H.darts ∧
      (oppositeHypermap H).edgeMap = H.faceMap * H.nodeMap ∧
      (oppositeHypermap H).nodeMap = H.nodeMap.symm ∧
      (oppositeHypermap H).faceMap = H.faceMap.symm :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- HOL `opposite_hypermap_plain`（`tame_opposite.hl:39`，tame_1a）。 -/
theorem oppositeHypermap_plain (H : Hypermap α) (hp : H.Plain) :
    (oppositeHypermap H).Plain := by
  have he : H.edgeMap = (H.nodeMap * H.faceMap)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact H.comp_eq_one)
  have h2 : (H.nodeMap * H.faceMap) * (H.nodeMap * H.faceMap) = 1 := by
    have hinv : (H.edgeMap * H.edgeMap)⁻¹ = 1 := by rw [hp, inv_one]
    rwa [mul_inv_rev, he, inv_inv] at hinv
  show (H.faceMap * H.nodeMap) * (H.faceMap * H.nodeMap) = 1
  calc (H.faceMap * H.nodeMap) * (H.faceMap * H.nodeMap)
      = H.faceMap * ((H.nodeMap * H.faceMap) * (H.nodeMap * H.faceMap)) *
          H.faceMap⁻¹ := by group
    _ = 1 := by rw [h2]; group

/-- HOL `opposite_components`（`tame_opposite.hl:57`）：dart / node / face 不变。 -/
theorem oppositeComponents (H : Hypermap α) (x : α) :
    (oppositeHypermap H).darts = H.darts ∧
      (oppositeHypermap H).node x = H.node x ∧
      (oppositeHypermap H).face x = H.face x := by
  refine ⟨rfl, ?_, ?_⟩
  · show orbitMap H.nodeMap.symm x = orbitMap H.nodeMap x
    exact PermutesOn.orbitMap_symm H.nodeMap_permutes x
  · show orbitMap H.faceMap.symm x = orbitMap H.faceMap x
    exact PermutesOn.orbitMap_symm H.faceMap_permutes x

/-- HOL `opposite_hypermap_simple`（`tame_opposite.hl:77`，tame_2b）。 -/
theorem oppositeHypermap_simple (H : Hypermap α) (hs : H.Simple) :
    (oppositeHypermap H).Simple := by
  intro x hx
  have hx' : x ∈ H.darts := hx
  rw [(oppositeComponents H x).2.1, (oppositeComponents H x).2.2]
  exact hs x hx'

/-- HOL `hypermap_eq_lemma`（`tame_opposite.hl:86`）：四元组投影决定结构（结构 eta）。 -/
theorem hypermapEqLemma (H : Hypermap α) :
    H = ⟨H.darts, H.edgeMap, H.nodeMap, H.faceMap, H.edgeMap_permutes,
      H.nodeMap_permutes, H.faceMap_permutes, H.comp_eq_one⟩ := rfl

/-- HOL `opposite_opposite_hypermap_eq_hypermap`（`tame_opposite.hl:100`）。 -/
theorem oppositeOpposite (H : Hypermap α) :
    oppositeHypermap (oppositeHypermap H) = H := by
  refine Hypermap.ext' rfl ?_ rfl rfl
  show H.faceMap.symm * H.nodeMap.symm = H.edgeMap
  have he : H.edgeMap = (H.nodeMap * H.faceMap)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact H.comp_eq_one)
  rw [he, mul_inv_rev]
  rfl

/-- HOL `truncated_path_lemma`（`tame_opposite.hl:117`）。 -/
theorem truncatedPathLemma (H : Hypermap α) (p q : ℕ → α) (n : ℕ)
    (hp : H.isPath p n) (h : ∀ i ≤ n, q i = p i) : H.isPath q n :=
  (H.isPath_congr (fun i hi => (h i hi).symm)).mp hp


/-- HOL `go_one_step` 的 opposite 两步模拟（`opposite_path` 的三支核心）。 -/
theorem oppositeStepSim (H : Hypermap α) {x y : α} (h : H.goOneStep x y) :
    ∃ a, (oppositeHypermap H).goOneStep x a ∧ (oppositeHypermap H).goOneStep a y := by
  rcases h with h | h | h
  · -- edge 步：x --node--> n⁻¹x --face--> e x
    refine ⟨H.nodeMap.symm x, Or.inr (Or.inl rfl), Or.inr (Or.inr ?_)⟩
    rw [h, H.inverse2_hypermap_maps.1]
    rfl
  · -- node 步：x --edge--> f(n x) --face--> n x
    refine ⟨H.faceMap (H.nodeMap x), Or.inl rfl, Or.inr (Or.inr ?_)⟩
    rw [h]
    simp
  · -- face 步：x --node--> n⁻¹x --edge--> f x
    refine ⟨H.nodeMap.symm x, Or.inr (Or.inl rfl), Or.inl ?_⟩
    rw [h]
    simp

/-- HOL `opposite_path`（`tame_opposite.hl:139`）：H 的路径可提升为
opposite 的路径（每步两跳），端点保持。 -/
theorem oppositePath (H : Hypermap α) (p : ℕ → α) (n : ℕ)
    (hp : H.isPath p n) :
    ∃ q m, (oppositeHypermap H).isPath q m ∧ q 0 = p 0 ∧ q m = p n := by
  induction n with
  | zero => exact ⟨p, 0, trivial, rfl, rfl⟩
  | succ n ih =>
    rw [Hypermap.isPath_succ] at hp
    obtain ⟨hpn, hstep⟩ := hp
    obtain ⟨q, m, hq, hq0, hqm⟩ := ih hpn
    obtain ⟨a, h1, h2⟩ := oppositeStepSim H hstep
    let q' : ℕ → α := fun i => if i ≤ m then q i else if i = m + 1 then a else p (n + 1)
    have hq'm : (oppositeHypermap H).isPath q' m := by
      refine ((oppositeHypermap H).isPath_congr (p := q') (p' := q) ?_).mpr hq
      intro i hi
      simp [q', hi]
    have hq1 : q' m = q m := by simp [q']
    have hq2 : q' (m + 1) = a := by
      show (if m + 1 ≤ m then q (m + 1) else if m + 1 = m + 1 then a else p (n + 1)) = a
      rw [if_neg (by omega), if_pos rfl]
    have hq3 : q' (m + 2) = p (n + 1) := by
      show (if m + 2 ≤ m then q (m + 2) else if m + 2 = m + 1 then a else p (n + 1)) = p (n + 1)
      rw [if_neg (by omega), if_neg (by omega)]
    have hs1 : (oppositeHypermap H).goOneStep (q' m) (q' (m + 1)) := by
      rw [hq1, hq2, hqm]
      exact h1
    have hs2 : (oppositeHypermap H).goOneStep (q' (m + 1)) (q' (m + 2)) := by
      rw [hq2, hq3]
      exact h2
    refine ⟨q', m + 2, ?_, ?_, ?_⟩
    · rw [show m + 2 = (m + 1) + 1 from rfl, Hypermap.isPath_succ, Hypermap.isPath_succ]
      exact ⟨⟨hq'm, hs1⟩, hs2⟩
    · show q' 0 = p 0
      simp [q', hq0]
    · exact hq3

/-- HOL `opposite_path_alt`（`tame_opposite.hl:243`）：反向。 -/
theorem oppositePathAlt (H : Hypermap α) (q : ℕ → α) (m : ℕ)
    (hq : (oppositeHypermap H).isPath q m) :
    ∃ p n, H.isPath p n ∧ p 0 = q 0 ∧ p n = q m := by
  have := oppositePath (oppositeHypermap H) q m hq
  simpa [oppositeOpposite] using this

/-- opposite 的连通分量与 H 相同（`opposite_sets_of_components` 的路径核）。 -/
theorem combComponentOpposite (H : Hypermap α) (x : α) :
    (oppositeHypermap H).combComponent x = H.combComponent x := by
  ext y
  constructor
  · rintro ⟨p, n, hp0, hpn, hp⟩
    obtain ⟨p', n', hp', hp'0, hp'n⟩ := oppositePathAlt H p n hp
    exact ⟨p', n', hp'0.trans hp0, hp'n.trans hpn, hp'⟩
  · rintro ⟨p, n, hp0, hpn, hp⟩
    obtain ⟨q, m, hq, hq0, hqm⟩ := oppositePath H p n hp
    exact ⟨q, m, hq0.trans hp0, hqm.trans hpn, hq⟩

/-- HOL `opposite_sets_of_components`（`tame_opposite.hl:254`）。 -/
theorem oppositeSetsOfComponents (H : Hypermap α) :
    (oppositeHypermap H).nodeSet = H.nodeSet ∧
      (oppositeHypermap H).faceSet = H.faceSet ∧
      (oppositeHypermap H).setOfComponents = H.setOfComponents := by
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq,
      oppositeHypermap_darts, oppositeHypermap_nodeMap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (PermutesOn.orbitMap_symm H.nodeMap_permutes x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, PermutesOn.orbitMap_symm H.nodeMap_permutes x⟩
  · ext t
    simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq,
      oppositeHypermap_darts, oppositeHypermap_faceMap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (PermutesOn.orbitMap_symm H.faceMap_permutes x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, PermutesOn.orbitMap_symm H.faceMap_permutes x⟩
  · ext t
    simp only [Hypermap.setOfComponents, Hypermap.setPartComponents,
      Set.mem_setOf_eq, oppositeHypermap_darts]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (combComponentOpposite H x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, combComponentOpposite H x⟩

/-- HOL `opposite_hypermap_connected`（`tame_opposite.hl:284`，tame_2a）。 -/
theorem oppositeHypermap_connected (H : Hypermap α) (hc : H.Connected) :
    (oppositeHypermap H).Connected := by
  show (oppositeHypermap H).numberOfComponents = 1
  rw [Hypermap.numberOfComponents, (oppositeSetsOfComponents H).2.2]
  exact hc

/-- HOL `opposite_nondegenerate`（`tame_opposite.hl:291`，tame_3）。 -/
theorem oppositeNondegenerate (H : Hypermap α) (hpl : H.Plain)
    (hnd : H.EdgeNondegenerate) : (oppositeHypermap H).EdgeNondegenerate := by
  intro x hx h
  have h' : H.faceMap (H.nodeMap x) = x := h
  have hcyc : ∀ z, H.nodeMap (H.faceMap (H.edgeMap z)) = z := by
    intro z
    have h1 := H.hypermap_cyclic.1
    have h2 := congrFun (congrArg (fun p : Equiv.Perm α => (p : α → α)) h1) z
    simpa [Equiv.Perm.mul_apply] using h2
  have hn1 : H.nodeMap (H.faceMap (H.nodeMap x)) = H.nodeMap x := by rw [h']
  have hc := hcyc (H.nodeMap x)
  have h2 : H.nodeMap (H.faceMap (H.edgeMap (H.nodeMap x))) =
      H.nodeMap (H.faceMap (H.nodeMap x)) := hc.trans hn1.symm
  have h3 : H.faceMap (H.edgeMap (H.nodeMap x)) = H.faceMap (H.nodeMap x) :=
    (H.nodeMap_injective _ _).mp h2
  exact hnd (H.nodeMap x) (H.nodeMap_apply_mem hx) ((H.faceMap_injective _ _).mp h3)

/-- HOL `plain_hypermap_edge`（`tame_opposite.hl:384`）。 -/
theorem plainHypermapEdge (H : Hypermap α) (hp : H.Plain) (x : α) :
    H.edge x = {x, H.edgeMap x} := by
  show orbitMap H.edgeMap x = {x, H.edgeMap x}
  exact orbitMap_of_mul_self_eq_one hp x

end Kepler.Text.TameSpine
