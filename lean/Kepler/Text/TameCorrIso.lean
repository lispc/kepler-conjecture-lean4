/-
  Kepler.Text.TameCorrIso — `tame_correspondence_iso` 三波施工的 **W3 第十波（笔 2）**：
  S4 iso 不变家族 W1（HOL `OXAXUCS.hl:38/:57/:67`）+ `iso_imp_hyp_iso`
  （HOL `fan/hypermap_iso-compiled.hl:438`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ import = `Kepler.Text.TameCorrG9` + `Kepler.Text.TameCorrBase`
  │ （两者闭包零 `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **典范性 rw 判定（W2/W3 排期的关键，本文件实测）**：
  `TameCorrBase.isHypermapOfListTl_iff_eq_hypermapOfList` 是
  `IsHypermapOfListTl L H ↔ H = hypermapOfList L hL`。所以只要手上有
  `hIs : IsHypermapOfListTl L H'`，就能
  `have hEq : H' = hypermapOfList L hL := (…iff… (hL := hL)).mp hIs`
  并在**目标与假设里 `rw [hEq]`**（实测：见 `isHypermapOfListTl_eq_canonical`
  与 `Evidence.md` 的三条 example）。⇒ 六件 `tame*_iso` 的目标可统一取
  `hypermapOfList L hL`，无需对任意 `H'` 维护列表对应；W2/W3 的 iso 迁移
  只需 generic iso 族（本文件）一次付清。

  **HOL 对照**：
  `iso H G = ∃f. hyp_iso f (H,G)`（hypermap.hl:9614）⇒
  `iso_imp_hyp_iso` 是定义展开（Lean 中 `Iso` 体与 `∃f, HypIso f H G` 逐字同体，
  故为 `id`）；`HypIso` 体 = HOL `hyp_iso`（BIJ + 三映射交换）。
  `tame9a_iso`/`tame10_iso`/`tame11a_iso`：iso 保 face/node 轨道基数与
  `numberOfNodes`，逐槽迁移。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrG9
import Kepler.Text.TameCorrBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrIso

open Classical
open Kepler.Assembly (GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList IsHypermapOfListTl Tame9a Tame10 Tame11a)

/-! ## §1 `hyp_iso` 与 `iso_imp_hyp_iso` -/

/-- HOL `hyp_iso f (H,G)`（`fan/hypermap_iso-compiled.hl:6-11`）：
`f` 是 dart 集间双射且与 edge/node/face 三映射交换。 -/
def HypIso {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (H : Hypermap α) (G : Hypermap β) : Prop :=
  Set.BijOn f ↑H.darts ↑G.darts ∧
    ∀ x ∈ H.darts, G.edgeMap (f x) = f (H.edgeMap x) ∧
      G.nodeMap (f x) = f (H.nodeMap x) ∧ G.faceMap (f x) = f (H.faceMap x)

/-- HOL `iso_imp_hyp_iso`（`hypermap_iso-compiled.hl:438`）：
`H iso G ⇒ ∃f. hyp_iso f (H,G)`。Lean 侧 `Hypermap.Iso` 体与
`∃ f, HypIso f H G` 逐字同体（`Iso` 的 def 体 = `∃ f, <HypIso 体>`），故为 `id`。 -/
theorem isoImpHypsIso {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H : Hypermap α} {G : Hypermap β} (h : H.Iso G) :
    ∃ f : α → β, HypIso f H G := h

/-- **典范性桥（判定实证件）**：`IsHypermapOfListTl L H'` 直接给出
`H' = hypermapOfList L hL`（`TameCorrBase` 的 `iff` 的 `.mp`）。
W2/W3 用它把任意显式 `H'` rw 成 canonical 构造。 -/
theorem isHypermapOfListTl_eq_canonical {L : Kepler.Graphs.fgraph ℕ} {hL : GoodList L}
    {H' : Hypermap (ℕ × ℕ)} (hIs : IsHypermapOfListTl L H') :
    H' = hypermapOfList L hL :=
  (Kepler.Text.TameCorrBase.isHypermapOfListTl_iff_eq_hypermapOfList (hL := hL)).mp hIs

/-! ## §2 iso 的轨道/基数不变量 -/

section Engine
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `hyp_iso` 的 maps-to（dart 集成员搬运）。 -/
theorem hypIso_mapsTo {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) : f x ∈ G.darts :=
  hiso.1.mapsTo (by simpa using hx)

/-- `hyp_iso` 的 surjectivity（目标 dart 有原像）。 -/
theorem hypIso_surjOn {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {y : β} (hy : y ∈ G.darts) :
    ∃ x ∈ H.darts, f x = y := by
  obtain ⟨x, hx, hxy⟩ := hiso.1.surjOn (by simpa using hy)
  exact ⟨x, by simpa using hx, hxy⟩

/-- `faceMap` 幂与 `hyp_iso` 交换。 -/
theorem hypIso_faceMap_pow {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (n : ℕ) :
    (G.faceMap ^ n) (f x) = f ((H.faceMap ^ n) x) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hz : (H.faceMap ^ k) x ∈ H.darts :=
      H.faceMap_permutes.pow_apply_mem k hx
    rw [pow_succ', Equiv.Perm.mul_apply, ih, (hiso.2 _ hz).2.2]
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `nodeMap` 幂与 `hyp_iso` 交换。 -/
theorem hypIso_nodeMap_pow {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) (n : ℕ) :
    (G.nodeMap ^ n) (f x) = f ((H.nodeMap ^ n) x) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hz : (H.nodeMap ^ k) x ∈ H.darts :=
      H.nodeMap_permutes.pow_apply_mem k hx
    rw [pow_succ', Equiv.Perm.mul_apply, ih, (hiso.2 _ hz).2.1]
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- `hyp_iso` 把 face 轨道送到 face 轨道：`G.face (f x) = f '' H.face x`。 -/
theorem hypIso_face_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    G.face (f x) = f '' (H.face x) := by
  ext y
  constructor
  · intro hy
    simp only [Kepler.Text.Hypermap.face, Kepler.Text.orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    refine ⟨(H.faceMap ^ n) x, ⟨n, rfl⟩, ?_⟩
    rw [← hypIso_faceMap_pow hiso hx n]
    exact hn
  · rintro ⟨z, hz, rfl⟩
    simp only [Kepler.Text.Hypermap.face, Kepler.Text.orbitMap, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨n, hn⟩ := hz
    exact ⟨n, by rw [hypIso_faceMap_pow hiso hx n, hn]⟩

/-- `hyp_iso` 把 node 轨道送到 node 轨道：`G.node (f x) = f '' H.node x`。 -/
theorem hypIso_node_image {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    G.node (f x) = f '' (H.node x) := by
  ext y
  constructor
  · intro hy
    simp only [Kepler.Text.Hypermap.node, Kepler.Text.orbitMap, Set.mem_setOf_eq] at hy
    obtain ⟨n, hn⟩ := hy
    refine ⟨(H.nodeMap ^ n) x, ⟨n, rfl⟩, ?_⟩
    rw [← hypIso_nodeMap_pow hiso hx n]
    exact hn
  · rintro ⟨z, hz, rfl⟩
    simp only [Kepler.Text.Hypermap.node, Kepler.Text.orbitMap, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨n, hn⟩ := hz
    exact ⟨n, by rw [hypIso_nodeMap_pow hiso hx n, hn]⟩

/-- `hyp_iso` 保 face 轨道基数。 -/
theorem hypIso_face_ncard {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    (G.face (f x)).ncard = (H.face x).ncard := by
  rw [hypIso_face_image hiso hx]
  exact Set.InjOn.ncard_image
    (hiso.1.injOn.mono (Kepler.Text.Hypermap.face_subset_darts H hx))

/-- `hyp_iso` 保 node 轨道基数。 -/
theorem hypIso_node_ncard {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) {x : α} (hx : x ∈ H.darts) :
    (G.node (f x)).ncard = (H.node x).ncard := by
  rw [hypIso_node_image hiso hx]
  exact Set.InjOn.ncard_image
    (hiso.1.injOn.mono (Kepler.Text.Hypermap.node_subset_darts H hx))

/-- `nodeSet` 的成员表示。 -/
private theorem mem_nodeSet_iff {H : Hypermap α} {S : Set α} :
    S ∈ H.nodeSet ↔ ∃ x ∈ H.darts, S = H.node x := by
  rw [Kepler.Text.Hypermap.nodeSet, Kepler.Text.setOfOrbits]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, e.symm⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, e.symm⟩

/-- `hyp_iso` 保 `numberOfNodes`（node 轨道像集 ↔ 轨道集）。 -/
theorem hypIso_numberOfNodes {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (hiso : HypIso f H G) :
    G.numberOfNodes = H.numberOfNodes := by
  have hmaps : ∀ S ∈ H.nodeSet, f '' S ∈ G.nodeSet := by
    intro S hS
    obtain ⟨x, hx, rfl⟩ := mem_nodeSet_iff.mp hS
    rw [← hypIso_node_image hiso hx]
    exact mem_nodeSet_iff.mpr ⟨f x, hypIso_mapsTo hiso hx, rfl⟩
  have hinj : Set.InjOn (fun S : Set α => f '' S) H.nodeSet := by
    intro S1 hS1 S2 hS2 heq
    obtain ⟨x1, hx1, rfl⟩ := mem_nodeSet_iff.mp hS1
    obtain ⟨x2, hx2, rfl⟩ := mem_nodeSet_iff.mp hS2
    have heq' : f '' (H.node x1) = f '' (H.node x2) := heq
    ext z
    constructor
    · intro hz
      have hfz1 : f z ∈ f '' (H.node x1) := ⟨z, hz, rfl⟩
      rw [heq'] at hfz1
      obtain ⟨w, hw, hfw⟩ := hfz1
      have hzD : z ∈ H.darts := Kepler.Text.Hypermap.node_subset_darts H hx1 hz
      have hwD : w ∈ H.darts := Kepler.Text.Hypermap.node_subset_darts H hx2 hw
      have hwz : w = z := hiso.1.injOn hwD hzD hfw
      exact hwz ▸ hw
    · intro hz
      have hfz2 : f z ∈ f '' (H.node x2) := ⟨z, hz, rfl⟩
      rw [← heq'] at hfz2
      obtain ⟨w, hw, hfw⟩ := hfz2
      have hzD : z ∈ H.darts := Kepler.Text.Hypermap.node_subset_darts H hx2 hz
      have hwD : w ∈ H.darts := Kepler.Text.Hypermap.node_subset_darts H hx1 hw
      have hwz : w = z := hiso.1.injOn hwD hzD hfw
      exact hwz ▸ hw
  have hcard : ((fun S : Set α => f '' S) '' H.nodeSet).ncard = H.nodeSet.ncard :=
    Set.InjOn.ncard_image hinj
  have hset : G.nodeSet = (fun S : Set α => f '' S) '' H.nodeSet := by
    ext S
    constructor
    · intro hS
      obtain ⟨y, hy, rfl⟩ := mem_nodeSet_iff.mp hS
      obtain ⟨x, hx, hxy⟩ := hiso.1.surjOn (by simpa using hy)
      have hx' : x ∈ H.darts := by simpa using hx
      refine ⟨H.node x, mem_nodeSet_iff.mpr ⟨x, hx', rfl⟩, ?_⟩
      change f '' (H.node x) = G.node y
      rw [← hxy]
      exact (hypIso_node_image hiso hx').symm
    · rintro ⟨S', hS', rfl⟩
      exact hmaps S' hS'
  unfold Kepler.Text.Hypermap.numberOfNodes
  rw [hset, hcard]

/-! ## §3 `tame*_iso`（HOL OXAXUCS.hl:38/:57/:67） -/

/-- HOL `tame9a_iso`（OXAXUCS.hl:38）：`tame_9a H ∧ hyp_iso f (H,H') ⇒ tame_9a H'`。 -/
theorem tame9aIso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame9a H) (hiso : HypIso f H G) : Tame9a G := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
  rw [← hxy, hypIso_face_ncard hiso hx]
  exact h x hx

/-- HOL `tame10_iso`（OXAXUCS.hl:57）：`tame_10 H ∧ hyp_iso f (H,H') ⇒ tame_10 H'`。 -/
theorem tame10Iso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame10 H) (hiso : HypIso f H G) : Tame10 G := by
  unfold Tame10 at *
  rw [hypIso_numberOfNodes hiso]
  exact h

/-- HOL `tame11a_iso`（OXAXUCS.hl:67）：`tame_11a H ∧ hyp_iso f (H,H') ⇒ tame_11a H'`。 -/
theorem tame11aIso {H : Hypermap α} {G : Hypermap β} {f : α → β}
    (h : Tame11a H) (hiso : HypIso f H G) : Tame11a G := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hypIso_surjOn hiso hy
  rw [← hxy, hypIso_node_ncard hiso hx]
  exact h x hx

end Engine

end Kepler.Text.TameCorrIso
