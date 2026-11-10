/-
  Kepler.Text.Reduction1Aqt8 — dih2k ④ 全证（EPC 语境）+ 主定理「hEpc + 互斥 + ⑤」
  收口形。

  本文件三件：
  · `edgeQuotient_atomNe` —— ④ 的单见证（HOL AUQTZYZ.hl:2273-:2393 的核心）：
    证人 `atom (loop_of_face H x) x`；反证（设 `edge (atom L1 x) = atom L1 x`）：
    `e_quotient (atomChoice x) = atomChoice (edgeMap (head x))` 一发，
    `headOfAtom NF x = x`（`loopOfFace_map_pow_apply` + `headOfAtom_eq_self_iff`），
    `edgeMap x = nodeMap (faceMap x)`（`plain_iff_edgeMap_eq`），
    EPC 12 给 `nodeMap (faceMap x) ∈ L.darts` ⟹ 该 atomChoice 是 **L 族**原子；
    同时由假设它又 = `atom L1 x`（**L1 族**）——两族原子集相交非空，
    与 EPC 9 的互斥矛盾。
  · `hasOrdersEdgeQuotient` —— ④ 在 EPC 语境下的全证：上件供见证 +
    Aqt7 `hasOrdersEdgeTwoOfNe`（`^2 = 1` 由 `edgeQuotient_sq` 供）。
  · `auqtzyzConclOfEpcAndDisj5` —— 主定理收口形（`hEpc` + 互斥 + ⑤ 三槽）：
    ④ 已内置，② 由 Aqt6 基数归约内置。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt7
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 ④ 的单见证（EPC 语境） -/

/-- **dih2k ④ 单见证**（HOL AUQTZYZ.hl:2273-:2393 核心）：EPC 语境下
`edge (atom (loop_of_face H x) x) ≠ atom (loop_of_face H x) x`。
反证链：`e_quotient (atomChoice x) = atomChoice (edgeMap (head x))`；
`head x = x`（L1 的 loopMap = faceMap）；`edgeMap x = nodeMap (faceMap x)`
（Plain）；EPC 12 把 `nodeMap (faceMap x)` 送进 `L.darts`（**L 族**原子），
假设又把它等于 `atom L1 x`（**L1 族**），与 EPC 9 的两族互斥矛盾。 -/
theorem edgeQuotient_atomNe {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅)) :
    (H.quotientHypermap hnf).edgeMap (H.atom (H.loopOfFace x) x)
      ≠ H.atom (H.loopOfFace x) x := by
  intro hEq
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hxL1 : x ∈ (H.loopOfFace x).darts :=
    (H.mem_faceFinset x x).mpr (H.mem_face_self x)
  have hfam : x ∈ Kepler.Text.Hypermap.dartsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    ⟨H.loopOfFace x, hL1mem, hxL1⟩
  -- head x = x（L1 的 loopMap = faceMap，head 判据）
  have hmap1 : (H.loopOfFace x).map x = H.faceMap x := by
    simpa using Kepler.Text.Hypermap.loopOfFace_map_pow_apply H
      (H.mem_face_self x) 1
  have hhead : H.headOfAtom ({H.loopOfFace x, L}) x = x :=
    (H.headOfAtom_eq_self_iff hres hnf hL1mem hxL1).mpr hmap1
  -- atomChoice 与 e_quotient 求值
  have hatom : H.atomChoice ({H.loopOfFace x, L}) x = H.atom (H.loopOfFace x) x :=
    H.atomChoice_eq_atom hnf hL1mem hxL1
  have he := (H.eQuotientPerm_via_atomChoice hnf hfam).2.2
  have hspec := (H.quotientHypermap_spec hnf).2.1
  rw [← hatom] at hEq
  have h1' : (H.quotientHypermap hnf).edgeMap (H.atomChoice ({H.loopOfFace x, L}) x)
      = H.atomChoice ({H.loopOfFace x, L})
          (H.edgeMap (H.headOfAtom ({H.loopOfFace x, L}) x)) := by
    rw [hspec, he]
  rw [h1', hhead] at hEq
  -- hEq : atomChoice (edgeMap x) = atomChoice x，故 = atom L1 x
  have heq' : H.atomChoice ({H.loopOfFace x, L}) (H.edgeMap x)
      = H.atom (H.loopOfFace x) x := hEq.trans hatom
  -- edgeMap x = nodeMap (faceMap x)
  have hedge : H.edgeMap x = H.nodeMap (H.faceMap x) := by
    rw [(H.plain_iff_edgeMap_eq).mp hres.plain]
    rfl
  -- faceMap x ∈ face x ⟹ nodeMap (faceMap x) ∈ L.darts（EPC 12）
  have hfm : H.faceMap x ∈ H.face x := H.pow_faceMap_mem_face x 1
  have hnmL : H.nodeMap (H.faceMap x) ∈ L.darts := hcl3 (H.faceMap x) hfm
  -- 该原子同时在 L 族（EPC 12 侧）与 L1 族（假设侧）
  have hmemL : H.atomChoice ({H.loopOfFace x, L}) (H.nodeMap (H.faceMap x))
      ∈ H.atomsOfLoop L := by
    rw [H.atomChoice_eq_atom hnf hLmem hnmL]
    exact H.atom_mem_atomsOfLoop L hnmL
  have hmemL1 : H.atomChoice ({H.loopOfFace x, L}) (H.nodeMap (H.faceMap x))
      ∈ {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
          x1 ∈ (H.loopOfFace x).darts} := by
    exact ⟨x, by rw [← heq', ← hedge], hxL1⟩
  have hinter : H.atomChoice ({H.loopOfFace x, L}) (H.nodeMap (H.faceMap x))
      ∈ (H.atomsOfLoop L ∩
        {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
          x1 ∈ (H.loopOfFace x).darts}) := ⟨hmemL, hmemL1⟩
  rw [hdisj2] at hinter
  rw [Set.mem_empty_iff_false] at hinter
  exact hinter

/-! ## §2 ④ 全证（EPC 语境） -/

/-- **dih2k 合取 ④（EPC 语境全证）**：`hasOrders_p3 (quotient.edgeMap) 2`。
见证 = §1；`^2 = 1` = Aqt7 `edgeQuotient_sq`（通用）。 -/
theorem hasOrdersEdgeQuotient {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅)) :
    Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).edgeMap : Set α → Set α)) 2 := by
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  have hxL1 : x ∈ (H.loopOfFace x).darts :=
    (H.mem_faceFinset x x).mpr (H.mem_face_self x)
  have hmem : H.atom (H.loopOfFace x) x
      ∈ (H.quotientHypermap hnf).darts := by
    rw [mem_darts_quotient]
    exact ⟨H.loopOfFace x, hL1mem, x, hxL1, rfl⟩
  exact hasOrdersEdgeTwoOfNe hres.plain hnf
    ⟨_, hmem, edgeQuotient_atomNe hres hnf hcl3 hdisj2⟩

/-! ## §3 主定理收口形（hEpc + 互斥 + ⑤ 三槽；④ 内置） -/

/-- **AUQTZYZ 主定理收口形（三槽版）**：`hEpc` + 互斥（② 的等价核）+
⑤ ⇒ `AuqtzyzConcl H x L1`。② 由 Aqt6 基数归约、④ 由 §2 内置。
剩余：批 ① EPC、互斥、⑤ 三事。 -/
theorem auqtzyzConclOfEpcAndDisj5 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hdisj : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
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
  refine ⟨L, hnf, hpath, ?_⟩
  exact dih2kOfEpcConcl hres hx hnf hcard hdisj2 ⟨_, hmem0⟩
    (dih2kConj2OfDisjoint hres hx hnf hcard hdisj2 (hdisj L hnf))
    (hasOrdersEdgeQuotient hres hnf hcl3 hdisj2)
    (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.edgeQuotient_atomNe
#print axioms Kepler.Text.Reduction1.hasOrdersEdgeQuotient
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndDisj5
