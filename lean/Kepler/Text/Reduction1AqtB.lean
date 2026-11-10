/-
  Kepler.Text.Reduction1AqtB — dih2k ⑤ 的非恒等半（真证）+ ⑤ 归约为平方槽 +
  主定理「hEpc + node 平方槽」两槽收口形。

  本文件三件：
  · `nodeQuotient_ne` —— ⑤ 的 **非恒等见证**（HOL AUQTZYZ.hl:2457-:2515 的
    Lean 重写）：证人 `atom (loop_of_face H x) x`；由 `tailOfAtom x = x`
    （`tailOfAtom_eq_self_iff` + `lemmaAtomTail`）得
    `nQ (atom L1 x) = atom L (nodeMap x)`（`nQuotient_via_atomChoice` 第三分量 +
    EPC 12 的 `nodeMap x ∈ L.darts`）；它与 `atom L1 x` 分居两族，撞 EPC 9。
  · `hasOrdersNodeTwoOfHid` —— ⑤ 归约：非恒等见证 + 平方槽
    `∀ a ∈ darts, (nQ²) a = a` ⇒ `hasOrders_p3 nQ 2`（`hasOrdersOfSupport`）。
  · `auqtzyzConclOfEpcAndHid` —— 主定理收口形（`hEpc` + node 平方槽）：
    ⑤ 由 §2 从平方槽提升（非恒等由 §1 供）；互斥/②/④ 全内置。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1AqtA
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §0 私桥：族互斥的 `atomsOfLoop` 形 -/

/-- 族互斥的 `atomsOfLoop L1` 形（EPC 9 的 ∃-次序换装）。 -/
private theorem atomsFamilyDecompB {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅)) :
    H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) = ∅ := by
  rw [atomsOfLoopLoopOfFaceEq]
  exact hdisj2

/-! ## §1 ⑤ 的非恒等见证 -/

/-- **dih2k ⑤ 的非恒等见证**（HOL AUQTZYZ.hl:2457-:2515）：
`nQ (atom (loop_of_face H x) x) ≠ atom (loop_of_face H x) x`。
证体：`tailOfAtom x = x`（`tailOfAtom_eq_self_iff` + `lemmaAtomTail`）；
`nQ (atom L1 x) = atom L (nodeMap x)`（`nQuotient_via_atomChoice` + EPC 12）；
该原子与 `atom L1 x` 分居 L/L1 两族，撞 EPC 9。 -/
theorem nodeQuotient_ne {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts) :
    (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x)
      ≠ H.atom (H.loopOfFace x) x := by
  intro hEq
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hxL1 : x ∈ (H.loopOfFace x).darts :=
    (H.mem_faceFinset x x).mpr (H.mem_face_self x)
  have hfam : x ∈ Kepler.Text.Hypermap.dartsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    ⟨H.loopOfFace x, hL1mem, hxL1⟩
  -- tailOfAtom x = x
  have htail : H.tailOfAtom ({H.loopOfFace x, L}) x = x :=
    (H.tailOfAtom_eq_self_iff hres hnf hL1mem hxL1).mpr
      (Kepler.Text.TameSpine.lemmaAtomTail H x x (H.mem_face_self x))
  -- nQ (atom L1 x) = atom L (nodeMap x)
  have hnQ : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x)
      = H.atom L (H.nodeMap x) := by
    rw [← H.atomChoice_eq_atom hnf hL1mem hxL1,
      (H.quotientHypermap_spec hnf).2.2.1, H.nQuotientPerm_apply,
      (H.nQuotient_via_atomChoice hnf hfam).2.2, htail,
      H.atomChoice_eq_atom hnf hLmem (hcl3 x (H.mem_face_self x))]
  rw [hnQ] at hEq
  -- atom L (nodeMap x) 同时在两族
  have hnmL : H.nodeMap x ∈ L.darts := hcl3 x (H.mem_face_self x)
  have hmemL : H.atom L (H.nodeMap x) ∈ H.atomsOfLoop L :=
    H.atom_mem_atomsOfLoop L hnmL
  have hmemL1 : H.atom L (H.nodeMap x) ∈ H.atomsOfLoop (H.loopOfFace x) := by
    rw [hEq]
    exact H.atom_mem_atomsOfLoop _ hxL1
  have hinter : H.atom L (H.nodeMap x)
      ∈ H.atomsOfLoop L ∩ H.atomsOfLoop (H.loopOfFace x) := ⟨hmemL, hmemL1⟩
  rw [atomsFamilyDecompB hdisj2] at hinter
  rw [Set.mem_empty_iff_false] at hinter
  exact hinter

/-! ## §2 ⑤ 归约为平方槽 -/

/-- **⑤ 归约**：非恒等见证 + `∀ a ∈ darts, (nQ²) a = a` ⇒ `hasOrders_p3 nQ 2`
（`hasOrdersOfSupport`；`0<i<2` 唯一支 i=1）。 -/
theorem hasOrdersNodeTwoOfHid {α : Type*} [DecidableEq α] {H : Hypermap α}
    {x : α} {L : Loop α} (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hne : ∃ a ∈ (H.quotientHypermap hnf).darts,
      (H.quotientHypermap hnf).nodeMap a ≠ a)
    (hhid : ∀ a ∈ (H.quotientHypermap hnf).darts,
      ((H.quotientHypermap hnf).nodeMap ^ 2) a = a) :
    Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2 := by
  refine Kepler.Text.Reduction1.hasOrdersOfSupport _ _ 2
    (H.quotientHypermap hnf).nodeMap_permutes ?_ ?_
  · intro i h0 hk
    have hi : i = 1 := by omega
    subst hi
    simpa [pow_one] using hne
  · exact hhid

/-! ## §3 主定理收口形（hEpc + node 平方槽） -/

/-- **AUQTZYZ 主定理收口形（平方槽版）**：`hEpc` + `∀ L hnf a ∈ darts,
(nQ²) a = a` ⇒ `AuqtzyzConcl H x L1`。⑤ 由 §2 提升（非恒等由 §1 供）；
互斥由 Aqt9/AqtA 内置；② 由 Aqt6、④ 由 Aqt8 内置。
剩余：批 ① EPC + node 平方（每商节点恰二原子的结构事实）两事。 -/
theorem auqtzyzConclOfEpcAndHid {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hhid : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        ((H.quotientHypermap hnf).nodeMap ^ 2) a = a) :
    AuqtzyzConcl H x L1 := by
  intro hres hx hL1
  obtain ⟨L, hloop, hpath, hmem0, hnodes, hdisjL, hclosL, hclosF, hcard, hdisj2,
    hcl1, hcl2, hcl3⟩ := hEpc H x hres hx
  subst hL1
  have hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    isNormalOfEpcConcl hres hx hloop hmem0 hnodes hdisjL hclosL hclosF
  -- ⑤：非恒等（§1）+ 平方（槽）
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hxL1 : x ∈ (H.loopOfFace x).darts :=
    (H.mem_faceFinset x x).mpr (H.mem_face_self x)
  have hmemD : H.atom (H.loopOfFace x) x ∈ (H.quotientHypermap hnf).darts := by
    rw [mem_darts_quotient]
    exact ⟨H.loopOfFace x, hL1mem, x, hxL1, rfl⟩
  have h5 : Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2 :=
    hasOrdersNodeTwoOfHid hnf
      ⟨_, hmemD, nodeQuotient_ne hres hnf hdisj2 hcl3⟩ (hhid L hnf)
  -- 互斥（两侧内置）
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
    h5

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.nodeQuotient_ne
#print axioms Kepler.Text.Reduction1.hasOrdersNodeTwoOfHid
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndHid
