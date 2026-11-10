/-
  Kepler.Text.Reduction1Aqt9 — 互斥的 L1 族半（真证）+ 主定理
  「hEpc + L 族互斥 + ⑤」收口形。

  本文件三件：
  · `atomNotMemNodeImageL1` —— 互斥核的 **L1 族半**：`atom (loop_of_face H x) v`
    （v ∈ face x）不在 `nQ '' atomsOfLoop (loop_of_face H x)` 内。
    反证（复用 Aqt8 的跨族矛盾结构）：设 `nQ (atom L1 u) = atom L1 v`，则
    `nodeMap (tailOfAtom u) ∈ atom L1 v ⊆ face x`（`atomChoice_self_mem` +
    `nQuotient_via_atomChoice` 第三分量），而 `tailOfAtom u ∈ atom L1 u ⊆ face x`，
    **EPC 12** 把 `nodeMap (tailOfAtom u)` 送进 `L.darts` —— 与 **EPC 5** 的
    `L.darts ∩ face x = ∅` 矛盾。
  · `disjointOfL1Family` —— 上式包装为 `Disjoint (face a) (nodeMap '' face a)` 对
    `a = atom L1 v` 成立（互斥的 L1 族半）。
  · `auqtzyzConclOfEpcAndDisjL5` —— 主定理收口形：
    `hEpc` + **L 族互斥槽** + ⑤ ⇒ `AuqtzyzConcl`（L1 族互斥由 §2 内置）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt8
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 互斥核的 L1 族半 -/

/-- **互斥核（L1 族半）**：`atomsOfLoop (loop_of_face H x)` 的任何原子都不属于
`nQ '' atomsOfLoop (loop_of_face H x)`。 -/
theorem atomNotMemNodeImageL1 {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hdisjL : ((↑L.darts : Set α) ∩ H.face x = ∅))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts) :
    ∀ z ∈ H.atomsOfLoop (H.loopOfFace x),
      z ∉ (H.quotientHypermap hnf).nodeMap '' H.atomsOfLoop (H.loopOfFace x) := by
  intro z hz1 hz2
  obtain ⟨v, hv, rfl⟩ := hz1
  obtain ⟨z0, hz0, hz0eq⟩ := hz2
  obtain ⟨u, hu, rfl⟩ := hz0
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have huF : u ∈ Kepler.Text.Hypermap.dartsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    ⟨H.loopOfFace x, hL1mem, hu⟩
  -- nQ (atom L1 u) = atomChoice (nodeMap (tailOfAtom u))
  have hnQ : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) u)
      = H.atomChoice ({H.loopOfFace x, L})
          (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)) := by
    rw [← H.atomChoice_eq_atom hnf hL1mem hu,
      (H.quotientHypermap_spec hnf).2.2.1, H.nQuotientPerm_apply,
      (H.nQuotient_via_atomChoice hnf huF).2.2]
  -- nodeMap (tail u) ∈ atom L1 v ⊆ face x
  have hy : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)
      ∈ H.atom (H.loopOfFace x) v := by
    rw [← hz0eq, hnQ]
    exact H.atomChoice_self_mem hnf _
  have hyface : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u) ∈ H.face x := by
    rw [← H.loopOfFace_darts]
    exact H.mem_darts_of_mem_atom hv hy
  -- tail u ∈ atom L1 u ⊆ face x
  have htailmem : H.tailOfAtom ({H.loopOfFace x, L}) u
      ∈ H.atom (H.loopOfFace x) u :=
    (H.tailOfAtom_mem_atom hnf hL1mem hu).1
  have htailface : H.tailOfAtom ({H.loopOfFace x, L}) u ∈ H.face x := by
    rw [← H.loopOfFace_darts]
    exact H.mem_darts_of_mem_atom hu htailmem
  -- EPC 12：nodeMap (tail u) ∈ L.darts
  have hyL : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u) ∈ L.darts :=
    hcl3 (H.tailOfAtom ({H.loopOfFace x, L}) u) htailface
  -- 撞 EPC 5
  have hinter : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)
      ∈ ((↑L.darts : Set α) ∩ H.face x) := ⟨hyL, hyface⟩
  rw [hdisjL] at hinter
  rw [Set.mem_empty_iff_false] at hinter
  exact hinter

/-! ## §2 互斥的 L1 族半（Disjoint 形） -/

/-- **互斥（L1 族半）**：`a = atom (loop_of_face H x) v`（`v ∈ face x`）时
`Disjoint (face a) (nodeMap '' face a)`。`face a = atomsOfLoop L1`
（`face_quotient_atom`），故即 §1。 -/
theorem disjointOfL1Family {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hdisjL : ((↑L.darts : Set α) ∩ H.face x = ∅))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts)
    {v : α} (hv : v ∈ (H.loopOfFace x).darts) :
    Disjoint ((H.quotientHypermap hnf).face (H.atom (H.loopOfFace x) v))
      ((H.quotientHypermap hnf).nodeMap ''
        (H.quotientHypermap hnf).face (H.atom (H.loopOfFace x) v)) := by
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  rw [H.face_quotient_atom hnf hL1mem hv, Set.disjoint_iff_inter_eq_empty,
    Set.eq_empty_iff_forall_notMem]
  intro z hz
  exact atomNotMemNodeImageL1 hres hnf hdisjL hcl3 z hz.1 hz.2

/-! ## §3 主定理收口形（hEpc + L 族互斥 + ⑤；L1 族互斥内置） -/

/-- **AUQTZYZ 主定理收口形（L 族互斥 + ⑤ 两槽）**：`hEpc` + L 族原子的互斥槽 +
⑤ ⇒ `AuqtzyzConcl H x L1`。L1 族互斥由 §2 内置（EPC 5/12）；
② 由 Aqt6 归约、④ 由 Aqt8 内置。剩余：批 ① EPC、L 族互斥、⑤ 三事。 -/
theorem auqtzyzConclOfEpcAndDisjL5 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hdisjLfam : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts, a ∈ H.atomsOfLoop L →
        Disjoint ((H.quotientHypermap hnf).face a)
          ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a))
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
  -- 合成完整互斥（L 族用槽，L1 族用 §2）
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
      rw [h] at hv ha ⊢
      exact hdisjLfam L hnf (H.atom L v) ha ⟨v, hv, rfl⟩
  refine ⟨L, hnf, hpath, ?_⟩
  exact dih2kOfEpcConcl hres hx hnf hcard hdisj2 ⟨_, hmem0⟩
    (dih2kConj2OfDisjoint hres hx hnf hcard hdisj2 hdisjFull)
    (hasOrdersEdgeQuotient hres hnf hcl3 hdisj2)
    (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.atomNotMemNodeImageL1
#print axioms Kepler.Text.Reduction1.disjointOfL1Family
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndDisjL5
