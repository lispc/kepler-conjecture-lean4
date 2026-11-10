/-
  Kepler.Text.Reduction1AqtA — 互斥的 L 族半（计数归约实做，真证）+ 主定理
  「hEpc + ⑤」收口形。

  本文件三件：
  · `nodeImageL1_eq` —— `nQ '' atomsOfLoop (loop_of_face H x) = atomsOfLoop L`
    （计数归约第一步：L1 半给像 ⊆ 补集 = L 族；nQ 单射 + 两侧 ncard 各 k 收等号）。
  · `disjointOfLFamily` —— 互斥的 **L 族半**：`a = atom L v`（v ∈ L.darts）时
    `Disjoint (face a) (nodeMap '' face a)`。`face a = atomsOfLoop L`
    （`face_quotient_atom`）；`nQ '' atomsOfLoop L = atomsOfLoop L1`
    （由 `nodeImageL1_eq` + nQ 单射 + 族互斥排除 L 支）；与 EPC 9 互斥收口。
  · `auqtzyzConclOfEpcAnd5` —— 主定理收口形：**`hEpc` + ⑤ 两槽** ⇒
    `AuqtzyzConcl`（互斥两侧内置、② 由 Aqt6、④ 由 Aqt8）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt9
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §0 记号 -/

/-- `atomsOfFamily {L1, L} = atomsOfLoop L1 ∪ atomsOfLoop L` 与 EPC 9 互斥的
`Set` 形（`atomsOfLoop L1` 一侧）。 -/
private theorem atomsFamily_decomp {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅)) :
    H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) = ∅ := by
  rw [atomsOfLoopLoopOfFaceEq]
  exact hdisj2

/-! ## §1 `nQ '' atomsOfLoop L1 = atomsOfLoop L`（计数） -/

/-- **计数归约第一步**：`nQ '' atomsOfLoop (loop_of_face H x) = atomsOfLoop L`。
⊆：L1 半（`atomNotMemNodeImageL1`）+ 族分解；等号：`nQ` 单射 + 两侧 ncard 各 k。 -/
theorem nodeImageL1_eq {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅))
    (hdisjL : ((↑L.darts : Set α) ∩ H.face x = ∅))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts) :
    (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop (H.loopOfFace x)
      = H.atomsOfLoop L := by
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hmemq : ∀ z : Set α, z ∈ (H.quotientHypermap hnf).darts ↔
      z ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    fun z => mem_darts_quotient hnf
  -- ⊆：像 ⊆ L 族
  have hsub : (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop (H.loopOfFace x)
      ⊆ H.atomsOfLoop L := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨x1, hx1, rfl⟩ := hw
    have hwfam : H.atom (H.loopOfFace x) x1
        ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
      ⟨H.loopOfFace x, hL1mem, x1, hx1, rfl⟩
    have hwd : H.atom (H.loopOfFace x) x1 ∈ (H.quotientHypermap hnf).darts :=
      (hmemq _).mpr hwfam
    have hnd : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x1)
        ∈ (H.quotientHypermap hnf).darts :=
      (H.quotientHypermap hnf).nodeMap_permutes.apply_mem hwd
    have hnfam : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x1)
        ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) := (hmemq _).mp hnd
    -- 不在 L1 族（L1 半）
    have hnot : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x1)
        ∉ H.atomsOfLoop (H.loopOfFace x) := by
      intro hc
      exact atomNotMemNodeImageL1 hres hnf hdisjL hcl3 _
        hc ⟨_, ⟨x1, hx1, rfl⟩, rfl⟩
    rw [atomsFamilyPair] at hnfam
    rcases hnfam with h1 | h2
    · exact absurd h1 hnot
    · exact h2
  -- 等号（基数）
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (H.atomsOfLoop_finite hnf hLmem)
  have hnc : ((H.quotientHypermap hnf).nodeMap ''
      H.atomsOfLoop (H.loopOfFace x)).ncard
      = (H.atomsOfLoop (H.loopOfFace x)).ncard :=
    Set.ncard_image_of_injective _ (H.quotientHypermap hnf).nodeMap.injective
  have hcard1 : (H.atomsOfLoop (H.loopOfFace x)).ncard = (H.face x).ncard := by
    rw [atomsOfLoopLoopOfFaceEq]
    exact Kepler.Text.TameSpine.cardAtomLoopOfFace H hres hx
  rw [hnc, hcard1, hcard]

/-! ## §2 互斥的 L 族半 -/

/-- **互斥（L 族半）**：`a = atom L v`（`v ∈ L.darts`）时
`Disjoint (face a) (nodeMap '' face a)`。`face a = atomsOfLoop L`；
`nQ '' atomsOfLoop L = atomsOfLoop L1`（§1 + 单射排除 L 支）；
与 EPC 9 互斥收口。 -/
theorem disjointOfLFamily {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅))
    (hdisjL : ((↑L.darts : Set α) ∩ H.face x = ∅))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts)
    {v : α} (hv : v ∈ L.darts) :
    Disjoint ((H.quotientHypermap hnf).face (H.atom L v))
      ((H.quotientHypermap hnf).nodeMap ''
        (H.quotientHypermap hnf).face (H.atom L v)) := by
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hmemq : ∀ z : Set α, z ∈ (H.quotientHypermap hnf).darts ↔
      z ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    fun z => mem_darts_quotient hnf
  have hB := nodeImageL1_eq hres hx hnf hcard hdisj2 hdisjL hcl3
  have hdisjFam : H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) = ∅ :=
    atomsFamily_decomp hdisj2
  -- nQ '' atomsOfLoop L = atomsOfLoop L1
  have hC : (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop L
      = H.atomsOfLoop (H.loopOfFace x) := by
    have hsub : (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop L
        ⊆ H.atomsOfLoop (H.loopOfFace x) := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨w1, hw1, rfl⟩ := hw
      have hwfam : H.atom L w1 ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
        ⟨L, hLmem, w1, hw1, rfl⟩
      have hwd : H.atom L w1 ∈ (H.quotientHypermap hnf).darts := (hmemq _).mpr hwfam
      have hnd : (H.quotientHypermap hnf).nodeMap (H.atom L w1)
          ∈ (H.quotientHypermap hnf).darts :=
        (H.quotientHypermap hnf).nodeMap_permutes.apply_mem hwd
      have hnfam : (H.quotientHypermap hnf).nodeMap (H.atom L w1)
          ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) := (hmemq _).mp hnd
      rw [atomsFamilyPair] at hnfam
      rcases hnfam with h1 | h2
      · exact h1
      · -- 若落在 L 族：由 hB 与单射推出 w1 在 L1 族，撞族互斥
        exfalso
        have hmemImg : (H.quotientHypermap hnf).nodeMap (H.atom L w1)
            ∈ (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop (H.loopOfFace x) := by
          rw [hB]
          exact h2
        obtain ⟨u, hu, hueq⟩ := hmemImg
        have huw : u = H.atom L w1 := (H.quotientHypermap hnf).nodeMap.injective hueq
        rw [huw] at hu
        have hinter : H.atom L w1 ∈ H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) :=
          ⟨⟨w1, hw1, rfl⟩, hu⟩
        rw [hdisjFam] at hinter
        rw [Set.mem_empty_iff_false] at hinter
        exact hinter
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (H.atomsOfLoop_finite hnf hL1mem)
    have hnc : ((H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop L).ncard
        = (H.atomsOfLoop L).ncard :=
      Set.ncard_image_of_injective _ (H.quotientHypermap hnf).nodeMap.injective
    have hcard1 : (H.atomsOfLoop (H.loopOfFace x)).ncard = (H.face x).ncard := by
      rw [atomsOfLoopLoopOfFaceEq]
      exact Kepler.Text.TameSpine.cardAtomLoopOfFace H hres hx
    rw [hnc, hcard, hcard1]
  -- 收口
  rw [H.face_quotient_atom hnf hLmem hv, hC, Set.disjoint_iff_inter_eq_empty,
    atomsOfLoopLoopOfFaceEq]
  exact hdisj2

/-! ## §3 主定理收口形（hEpc + ⑤ 两槽） -/

/-- **AUQTZYZ 主定理收口形（两槽版）**：`hEpc` + ⑤ ⇒ `AuqtzyzConcl H x L1`。
互斥两侧（L1 由 Aqt9、L 由 §2）、② 由 Aqt6、④ 由 Aqt8 全内置。
剩余：批 ① EPC、⑤ 两事。 -/
theorem auqtzyzConclOfEpcAnd5 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (h5 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      Kepler.Text.hasOrders_p3 (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2) :
    AuqtzyzConcl H x L1 := by
  intro hres hx hL1
  obtain ⟨L, hloop, hpath, hmem0, hnodes, hdisjL, hclosL, hclosF, hcard, hdisj2,
    hcl1, hcl2, hcl3⟩ := hEpc H x hres hx
  subst hL1
  have hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    isNormalOfEpcConcl hres hx hloop hmem0 hnodes hdisjL hclosL hclosF
  -- 合成完整互斥
  have hdisjFull : ∀ a ∈ (H.quotientHypermap hnf).darts,
      Disjoint ((H.quotientHypermap hnf).face a)
        ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a) := by
    intro a ha
    have hafam : a ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
      (mem_darts_quotient hnf).mp ha
    obtain ⟨L', hL', v, hv, rfl⟩ := hafam
    rcases Set.mem_insert_iff.mp hL' with h | h
    · rw [h] at hv ⊢
      exact disjointOfL1Family hres hnf hdisjL hcl3 hv
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hv ⊢
      exact disjointOfLFamily hres hx hnf hcard hdisj2 hdisjL hcl3 hv
  refine ⟨L, hnf, hpath, ?_⟩
  exact dih2kOfEpcConcl hres hx hnf hcard hdisj2 ⟨_, hmem0⟩
    (dih2kConj2OfDisjoint hres hx hnf hcard hdisj2 hdisjFull)
    (hasOrdersEdgeQuotient hres hnf hcl3 hdisj2)
    (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.nodeImageL1_eq
#print axioms Kepler.Text.Reduction1.disjointOfLFamily
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAnd5
