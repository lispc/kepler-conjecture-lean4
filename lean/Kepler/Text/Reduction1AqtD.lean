/-
  Kepler.Text.Reduction1AqtD — hhid（node 平方，HOL AUQTZYZ.hl:2515-:2611）全证 +
  **AUQTZYZ 主定理无条件形**（J4 线收官声明）。

  本文件：
  · `hasOrdersNodeSq` —— 商 `nodeMap²` 在 darts 上逐点恒等（HOL :2515-:2611）。
    证体两件几何事实（均由 **EPC 10** + `tailOfAtom_eq_iff_of_mem_atom` 供）：
      F1：`u ∈ L.darts ⇒ nodeMap (tailOfAtom u) ∈ face x`；
      F3：`u ∈ L.darts ⇒ nodeMap (nodeMap (tailOfAtom u)) ∈ atom L u`。
    两支计算：`nQ (atom L u) = atom L1 (nodeMap (tailOfAtom u))`（F1 + `nQuotient_via_atomChoice`）、
    `nQ (atom L1 y) = atom L (nodeMap y)`（tail 在 L1 侧 = 自身，`tailOfAtom_eq_self_iff`
    + `lemmaAtomTail`；EPC 12）。L 支：F3 直接回原子；L1 支：经 nQ 单射 +
    `nodeMap²(tail) ∈ atom L u`（F3）逼回。
  · `auqtzyzConclUncond` —— HEPC 槽由 `TameList63.existsPathComplementSlot` 接线，
    hhid/互斥/②/④/⑤ 全内置 ⇒ `AuqtzyzConcl` **无条件形**。
  · `auqtzyzUncond` —— `Auqtzyz`（全称闭包，逐宇宙）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList63
import Kepler.Text.Reduction1AqtC

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 hhid：node 平方（HOL :2515-:2611） -/

/-- **dih2k ⑤ 的平方半**（HOL AUQTZYZ.hl:2515-:2611）：商 `nodeMap²` 在 darts 上
逐点恒等。两件几何事实（F1/F3）由 EPC 10 + `tailOfAtom_eq_iff_of_mem_atom` 供；
两支各自计算并收口（L1 支经 nQ 单射）。 -/
theorem hasOrdersNodeSq {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcl1 : ∀ x1, x1 ∈ L.darts → ∃ y, y ∈ H.atom L x1 ∧
      y = H.faceMap (L.invMap y) ∧ H.nodeMap y ∈ H.face x ∧
      H.nodeMap (H.nodeMap y) ∈ H.atom L x1)
    (hcl3 : ∀ x1, x1 ∈ H.face x → H.nodeMap x1 ∈ L.darts) :
    ∀ a ∈ (H.quotientHypermap hnf).darts,
      ((H.quotientHypermap hnf).nodeMap ^ 2) a = a := by
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hL1mem : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  -- F1/F3：u ∈ L.darts 的 tail 的 node 性质（EPC 10 + tail 判据）
  have htail10 : ∀ u ∈ L.darts,
      H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u) ∈ H.face x ∧
      H.nodeMap (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)) ∈ H.atom L u := by
    intro u hu
    obtain ⟨y, hyatom, hyfix, hynode, hy2⟩ := hcl1 u hu
    have ht : H.tailOfAtom ({H.loopOfFace x, L}) u = y :=
      (H.tailOfAtom_eq_iff_of_mem_atom hres hnf hLmem hu hyatom).mpr hyfix
    rw [ht]
    exact ⟨hynode, hy2⟩
  -- L1 侧 tail = 自身
  have htailL1 : ∀ y ∈ (H.loopOfFace x).darts,
      H.tailOfAtom ({H.loopOfFace x, L}) y = y := by
    intro y hy
    have hyface : y ∈ H.face x := by
      rw [← H.loopOfFace_darts]
      exact hy
    exact (H.tailOfAtom_eq_self_iff hres hnf hL1mem hy).mpr
      (Kepler.Text.TameSpine.lemmaAtomTail H x y hyface)
  -- nQ 在 L 原子上的求值
  have hnQL : ∀ u ∈ L.darts, (H.quotientHypermap hnf).nodeMap (H.atom L u)
      = H.atom (H.loopOfFace x) (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)) := by
    intro u hu
    have huF : u ∈ Kepler.Text.Hypermap.dartsOfFamily
        ({H.loopOfFace x, L} : Set (Loop α)) := ⟨L, hLmem, hu⟩
    have hw : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) u)
        ∈ (H.loopOfFace x).darts :=
      (H.mem_faceFinset x _).mpr (htail10 u hu).1
    rw [← H.atomChoice_eq_atom hnf hLmem hu, (H.quotientHypermap_spec hnf).2.2.1,
      H.nQuotientPerm_apply, (H.nQuotient_via_atomChoice hnf huF).2.2,
      H.atomChoice_eq_atom hnf hL1mem hw]
  -- nQ 在 L1 原子上的求值
  have hnQL1 : ∀ y ∈ (H.loopOfFace x).darts,
      (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) y)
        = H.atom L (H.nodeMap y) := by
    intro y hy
    have hyface : y ∈ H.face x := by
      rw [← H.loopOfFace_darts]
      exact hy
    have hyF : y ∈ Kepler.Text.Hypermap.dartsOfFamily
        ({H.loopOfFace x, L} : Set (Loop α)) := ⟨_, hL1mem, hy⟩
    have hyd : H.nodeMap y ∈ L.darts := hcl3 y hyface
    rw [← H.atomChoice_eq_atom hnf hL1mem hy, (H.quotientHypermap_spec hnf).2.2.1,
      H.nQuotientPerm_apply, (H.nQuotient_via_atomChoice hnf hyF).2.2,
      htailL1 y hy, H.atomChoice_eq_atom hnf hLmem hyd]
  intro a ha
  have hafam : a ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    (mem_darts_quotient hnf).mp ha
  obtain ⟨L', hL', x'', hx'', rfl⟩ := hafam
  rcases Set.mem_insert_iff.mp hL' with h | h
  · -- L1 支：nQ²(atom L1 x'') = atom L1 x''
    rw [h] at hx'' ⊢
    have hxface : x'' ∈ H.face x := by
      rw [← H.loopOfFace_darts]
      exact hx''
    have hu : H.nodeMap x'' ∈ L.darts := hcl3 x'' hxface
    have hw : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x''))
        ∈ (H.loopOfFace x).darts :=
      (H.mem_faceFinset x _).mpr (htail10 (H.nodeMap x'') hu).1
    have hinner : (H.quotientHypermap hnf).nodeMap (H.atom (H.loopOfFace x) x'')
        = H.atom L (H.nodeMap x'') := hnQL1 x'' hx''
    have houter : (H.quotientHypermap hnf).nodeMap (H.atom L (H.nodeMap x''))
        = H.atom (H.loopOfFace x)
            (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x''))) :=
      hnQL (H.nodeMap x'') hu
    show ((H.quotientHypermap hnf).nodeMap ^ 2) (H.atom (H.loopOfFace x) x'')
      = H.atom (H.loopOfFace x) x''
    rw [pow_two, Equiv.Perm.mul_apply, hinner, houter]
    -- 经 nQ 单射：atom L1 w = atom L1 x''
    refine (H.quotientHypermap hnf).nodeMap.injective ?_
    have heq1 : (H.quotientHypermap hnf).nodeMap
        (H.atom (H.loopOfFace x)
          (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x''))))
        = H.atom L
            (H.nodeMap (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x'')))) :=
      hnQL1 _ hw
    have hmem3 : H.nodeMap (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x'')))
        ∈ H.atom L (H.nodeMap x'') := (htail10 (H.nodeMap x'') hu).2
    have hatomEq : H.atom L
        (H.nodeMap (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) (H.nodeMap x''))))
        = H.atom L (H.nodeMap x'') := (H.atom_eq_of_mem hmem3).symm
    rw [heq1, hinner, hatomEq]
  · -- L 支：nQ²(atom L x'') = atom L x''
    rw [Set.mem_singleton_iff] at h
    rw [h] at hx'' ⊢
    have hw : H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) x'')
        ∈ (H.loopOfFace x).darts :=
      (H.mem_faceFinset x _).mpr (htail10 x'' hx'').1
    have houter : (H.quotientHypermap hnf).nodeMap
        (H.atom (H.loopOfFace x) (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) x'')))
        = H.atom L (H.nodeMap (H.nodeMap (H.tailOfAtom ({H.loopOfFace x, L}) x''))) :=
      hnQL1 _ hw
    show ((H.quotientHypermap hnf).nodeMap ^ 2) (H.atom L x'') = H.atom L x''
    rw [pow_two, Equiv.Perm.mul_apply, hnQL x'' hx'', houter]
    exact (H.atom_eq_of_mem (htail10 x'' hx'').2).symm

/-! ## §2 AUQTZYZ 主定理无条件形 -/

/-- **AUQTZYZ 主定理（无条件形，逐实例）**：HOL `AUQTZYZ_concl`
（AUQTZYZ.hl:1851-:1857）——`AuqtzyzConcl H x L1` 对任意 `H x L1` 成立。
EPC 槽由 `TameList63.existsPathComplementSlot` 接线；hhid（§1）、互斥
（Aqt9/AqtA）、②（Aqt6）、④（Aqt8）、⑤（AqtB + §1）全内置。 -/
theorem auqtzyzConclUncond {α : Type*} [DecidableEq α]
    (H : Hypermap α) (x : α) (L1 : Loop α) : AuqtzyzConcl H x L1 := by
  intro hres hx hL1
  obtain ⟨L, hloop, hpath, hmem0, hnodes, hdisjL, hclosL, hclosF, hcard, hdisj2,
    hcl1, hcl2, hcl3⟩ := Kepler.Text.TameSpine.existsPathComplementSlot H x hres hx
  subst hL1
  have hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    isNormalOfEpcConcl hres hx hloop hmem0 hnodes hdisjL hclosL hclosF
  -- ⑤：非恒等（AqtB）+ 平方（§1）
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
      ⟨_, hmemD, nodeQuotient_ne hres hnf hdisj2 hcl3⟩
      (hasOrdersNodeSq hres hnf hcl1 hcl3)
  -- 互斥（两侧内置）
  have hdisjFull : ∀ a ∈ (H.quotientHypermap hnf).darts,
      Disjoint ((H.quotientHypermap hnf).face a)
        ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a) := by
    intro a ha
    have hafam : a ∈ H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
      (mem_darts_quotient hnf).mp ha
    obtain ⟨L', hL', v, hv, rfl⟩ := hafam
    rcases Set.mem_insert_iff.mp hL' with hh | hh
    · rw [hh] at hv ⊢
      exact disjointOfL1Family hres hnf hdisjL hcl3 hv
    · rw [Set.mem_singleton_iff] at hh
      rw [hh] at hv ⊢
      exact disjointOfLFamily hres hx hnf hcard hdisj2 hdisjL hcl3 hv
  refine ⟨L, hnf, hpath, ?_⟩
  exact dih2kOfEpcConcl hres hx hnf hcard hdisj2 ⟨_, hmem0⟩
    (dih2kConj2OfDisjoint hres hx hnf hcard hdisj2 hdisjFull)
    (hasOrdersEdgeQuotient hres hnf hcl3 hdisj2)
    h5

/-- **HOL `AUQTZYZ`**（AUQTZYZ.hl:1859-:2624）**无条件形**：`Auqtzyz`
（Aqt1 的全称闭包 def）——逐宇宙由 `auqtzyzConclUncond` 给出。 -/
theorem auqtzyzUncond : Auqtzyz :=
  fun {α} _ H x L1 => auqtzyzConclUncond H x L1

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.hasOrdersNodeSq
#print axioms Kepler.Text.Reduction1.auqtzyzConclUncond
#print axioms Kepler.Text.Reduction1.auqtzyzUncond
