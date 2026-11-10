/-
  Kepler.Text.Reduction1Aqt6 — dih2k ② 的基数归约（UNION 分解 ⇐ 互斥）+ 主定理
  「hEpc + 互斥 + ④⑤」收口形。

  本文件两件：
  · `dih2kConj2OfDisjoint` —— dih2k 合取 ②（HOL AUQTZYZ.hl:2047-:2181）经
    **基数归约**：`darts = face a ∪ nodeMap '' face a` 由
    ① `face a ∪ nodeMap '' face a ⊆ darts`（face = 原子族 ⊆ 原子族集合；
    nodeMap 保 darts）、② 两侧 ncard 各为 k（face 侧 = `hcard`/`cardAtomLoopOfFace`，
    像侧 = 置换单射 + 同一 k 值）、③ **互斥** `Disjoint (face a) (nodeMap '' face a)`、
    ④ `darts.ncard = 2k`（Aqt3 `dih2kCard`）经
    `Set.eq_of_subset_of_ncard_le` 收口。即 ② = 互斥 = 唯一剩余内容。
  · `auqtzyzConclOfEpcAndDisj45` —— 主定理收口形（**hEpc + 互斥 + ④ + ⑤** ⇒
    `AuqtzyzConcl`）：EPC 合取 8/9/3/1/4/5/6/7 即时供 conj1/③/is_normal，
    互斥与 ④⑤ 为槽。

  备注：Aqt5 的 `dih2kConj2OfDisjoint` 前身（`dih2kOfEpcConcl` 的 `h2` 槽）即
  此形；本文件把 ② **化简为互斥**并把收口定理更新为「互斥 + ④ + ⑤」三槽。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt5
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-- **dih2k 合取 ② 的基数归约**（HOL AUQTZYZ.hl:2047-:2181 的等价重述）：
在 Aqt3/Aqt5 的 conj1/③ 前提之外，只需**互斥**
`Disjoint (face a) (nodeMap '' face a)` 对 darts 内所有 `a` 成立，则
`darts = face a ∪ nodeMap '' face a`。证明：并 ⊆ darts（face 是原子族 ⊆ 原子族
集合、nodeMap 保 darts）；两侧 ncard 皆 k（face 侧 `hcard`/`cardAtomLoopOfFace`，
像侧 `ncard_image_of_injective`）；故并 ncard = 2k = darts ncard，配合
`Set.eq_of_subset_of_ncard_le` 得等式。 -/
theorem dih2kConj2OfDisjoint {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅))
    (hdisj : ∀ a ∈ (H.quotientHypermap hnf).darts,
      Disjoint ((H.quotientHypermap hnf).face a)
        ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a)) :
    ∀ a ∈ (H.quotientHypermap hnf).darts,
      (↑(H.quotientHypermap hnf).darts : Set (Set α)) =
        (H.quotientHypermap hnf).face a ∪
          (H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a := by
  intro a ha
  set q := H.quotientHypermap hnf with hqdef
  -- a = atom L' y（原子族分解）
  have hafam : a ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) := by
    have h := mem_darts_quotient (H := H) hnf (a := a)
    exact h.mp (by simpa [hqdef] using ha)
  obtain ⟨L', hL', y, hy, rfl⟩ := hafam
  -- q.darts 成员桥（q 为 set 缩写）
  have hmemq : ∀ z : Set α, z ∈ q.darts ↔
      z ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) := by
    intro z
    have h := mem_darts_quotient (H := H) hnf (a := z)
    simpa [hqdef] using h
  -- face a = atomsOfLoop L'
  have hface : q.face (H.atom L' y) = H.atomsOfLoop L' := H.face_quotient_atom hnf hL' hy
  -- ncard（face）= k
  have hkface : (q.face (H.atom L' y)).ncard = (H.face x).ncard := by
    rw [hface]
    rcases Set.mem_insert_iff.mp hL' with h | h
    · rw [h, atomsOfLoopLoopOfFaceEq]
      exact Kepler.Text.TameSpine.cardAtomLoopOfFace H hres hx
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact hcard
  -- ncard（nodeMap 像）= k
  have hkimg : ((q.nodeMap '' q.face (H.atom L' y))).ncard = (H.face x).ncard := by
    rw [Set.ncard_image_of_injective _ q.nodeMap.injective]
    exact hkface
  -- darts 有限性
  have hdartsFin : (↑q.darts : Set (Set α)).Finite := q.darts.finite_toSet
  -- 并 ⊆ darts
  have hsub : q.face (H.atom L' y) ∪ q.nodeMap '' q.face (H.atom L' y)
      ⊆ (↑q.darts : Set (Set α)) := by
    intro z hz
    rcases hz with hz | hz
    · -- face = 原子族 ⊆ 原子族集合
      have hz' : z ∈ H.atomsOfLoop L' := by
        rw [← hface]
        exact hz
      obtain ⟨z1, hz1, hzeq⟩ := hz'
      exact (hmemq z).mpr ⟨L', hL', z1, hz1, hzeq⟩
    · -- nodeMap 保 darts
      obtain ⟨w, hw, rfl⟩ := hz
      have hw' : w ∈ H.atomsOfLoop L' := by
        rw [← hface]
        exact hw
      obtain ⟨w1, hw1, hweq⟩ := hw'
      have hwfam : w ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
        ⟨L', hL', w1, hw1, hweq⟩
      have hwd : w ∈ q.darts := (hmemq w).mpr hwfam
      exact q.nodeMap_permutes.apply_mem hwd
  -- 有限性
  have hfinFace : (q.face (H.atom L' y)).Finite :=
    hdartsFin.subset (fun z hz => hsub (Or.inl hz))
  have hfinImg : (q.nodeMap '' q.face (H.atom L' y)).Finite := hfinFace.image _
  -- ncard（并）= 2k
  have hncUnion : (q.face (H.atom L' y) ∪ q.nodeMap '' q.face (H.atom L' y)).ncard
      = 2 * (H.face x).ncard := by
    rw [Set.ncard_union_eq (hdisj _ ha) hfinFace hfinImg, hkface, hkimg]
    omega
  -- ncard（darts）= 2k
  have hncDarts : (↑q.darts : Set (Set α)).ncard = 2 * (H.face x).ncard := by
    rw [Set.ncard_coe_finset]
    exact dih2kCard hres hx hnf hcard hdisj2
  -- 子集 + ncard 相等 ⇒ 等式
  have hunionEq : q.face (H.atom L' y) ∪ q.nodeMap '' q.face (H.atom L' y)
      = (↑q.darts : Set (Set α)) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hdartsFin
    rw [hncUnion, hncDarts]
  exact hunionEq.symm

/-- **AUQTZYZ 主定理收口形（互斥 + ④ + ⑤ 三槽）**：`hEpc`（批 ① 槽）+
dih2k 的互斥（② 的等价简化，见上件）+ ④⑤ 两 `hasOrders` 槽 ⇒
`AuqtzyzConcl H x L1`（Aqt1 陈述 def）。EPC 合取 8/9/3/1/4/5/6/7 即时供
conj1（Aqt3）、③（Aqt5）、is_normal（Aqt2）。 -/
theorem auqtzyzConclOfEpcAndDisj45 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hdisj : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        Disjoint ((H.quotientHypermap hnf).face a)
          ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a))
    (h4 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      Kepler.Text.hasOrders_p3 (((H.quotientHypermap hnf).edgeMap : Set α → Set α)) 2)
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
    (h4 L hnf) (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.dih2kConj2OfDisjoint
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndDisj45
