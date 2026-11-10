/-
  Kepler.Text.Reduction1Aqt7 — dih2k ④ 的 `^2 = 1` 分量（通用真证）+ ④ 归约为
  单见证 + 主定理「hEpc + 互斥 + edge 非恒等见证 + ⑤」收口形。

  本文件三件：
  · `edgeQuotient_sq` —— 商 hypermap 的 `edgeMap = (fQ)⁻¹ * (nQ)⁻¹` 在 darts
    上平方为恒等（**通用**：任意 normal family + `H.Plain`）。证体用
    `eQuotientPerm_via_atomChoice`（`e_quotient (atomChoice x) =
    atomChoice (edgeMap (headOfAtom x))` 及其 head 余量）两发 + `H.Plain`
    （`edgeMap² = 1`）+ `atomChoice_eq_atom`/`atom_eq_of_mem`。
  · `hasOrdersEdgeTwoOfNe` —— ④（`hasOrders edge 2`）**归约**为单见证
    `∃ a ∈ darts, edge a ≠ a`（`hasOrdersOfSupport` + 上件；`0<i<2` 唯一支 i=1）。
  · `auqtzyzConclOfEpcAndDisjNe5` —— 主定理收口形升级：
    `hEpc` + 互斥 + edge 见证 + ⑤ 四槽 ⇒ `AuqtzyzConcl`。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt6
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 商 edgeMap 的平方 = 恒等（通用真证） -/

/-- **商 hypermap 的 `edgeMap² = 1`（在 darts 上）**：任意正常环族 + `H.Plain`。
`e_quotient (atomChoice x) = atomChoice (edgeMap (headOfAtom x))` 两发
（第二发的 head 余量把 `head(edgeMap(head x))` 消成 `edgeMap(head x)`）+
`H.Plain`（`edgeMap (edgeMap z) = z`）+ `atomChoice` 不变性收口。 -/
theorem edgeQuotient_sq {α : Type*} [DecidableEq α] {H : Hypermap α}
    {NF : Set (Loop α)} (hpf : H.Plain) (hnf : H.IsNormalFamily NF) :
    ∀ a ∈ (H.quotientHypermap hnf).darts,
      ((H.quotientHypermap hnf).edgeMap ^ 2) a = a := by
  intro a ha
  -- a = atomChoice y 表示
  have hafam : a ∈ H.atomsOfFamily NF := (mem_darts_quotient hnf).mp ha
  obtain ⟨L, hL, y, hy, rfl⟩ := hafam
  have hyfam : y ∈ Kepler.Text.Hypermap.dartsOfFamily NF := ⟨L, hL, hy⟩
  have hrep : H.atomChoice NF y = H.atom L y := H.atomChoice_eq_atom hnf hL hy
  rw [← hrep]
  -- 两发 e_quotient 求值
  have hspec := (H.quotientHypermap_spec hnf).2.1
  have he1 := (H.eQuotientPerm_via_atomChoice hnf hyfam).2.2
  have hhead1 : H.edgeMap (H.headOfAtom NF y) ∈ Kepler.Text.Hypermap.dartsOfFamily NF :=
    (H.eQuotientPerm_via_atomChoice hnf hyfam).1
  have hheadEq : H.headOfAtom NF (H.edgeMap (H.headOfAtom NF y))
      = H.edgeMap (H.headOfAtom NF y) :=
    (H.eQuotientPerm_via_atomChoice hnf hyfam).2.1.symm
  have he2 := (H.eQuotientPerm_via_atomChoice hnf hhead1).2.2
  -- Plain ⇒ edgeMap² = id
  have hplain : H.edgeMap (H.edgeMap (H.headOfAtom NF y)) = H.headOfAtom NF y := by
    rw [← Equiv.Perm.mul_apply, hpf, Equiv.Perm.one_apply]
  -- atomChoice(head y) = atomChoice y
  have hheadmem : H.headOfAtom NF y ∈ H.atom L y :=
    (H.headOfAtom_mem_atom hnf hL hy).1
  have hheadd : H.headOfAtom NF y ∈ L.darts :=
    H.mem_darts_of_mem_atom hy hheadmem
  show ((H.quotientHypermap hnf).edgeMap ^ 2) (H.atomChoice NF y) = H.atomChoice NF y
  rw [pow_two, Equiv.Perm.mul_apply, hspec, he1, he2, hheadEq, hplain,
    H.atomChoice_eq_atom hnf hL hheadd, hrep, H.atom_eq_of_mem hheadmem]

/-! ## §2 ④ 归约为单见证 -/

/-- **dih2k 合取 ④ 的归约**：`H.Plain` + 单见证
`∃ a ∈ darts, edge a ≠ a` ⇒ `hasOrders_p3 edge 2`（`0<i<2` 唯一支 i=1；
`^2 = 1` 由 §1）。 -/
theorem hasOrdersEdgeTwoOfNe {α : Type*} [DecidableEq α] {H : Hypermap α}
    {NF : Set (Loop α)} (hpf : H.Plain) (hnf : H.IsNormalFamily NF)
    (hne : ∃ a ∈ (H.quotientHypermap hnf).darts,
      (H.quotientHypermap hnf).edgeMap a ≠ a) :
    Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).edgeMap : Set α → Set α)) 2 := by
  refine Kepler.Text.Reduction1.hasOrdersOfSupport _ _ 2
    (H.quotientHypermap hnf).edgeMap_permutes ?_ ?_
  · intro i h0 hk
    have hi : i = 1 := by omega
    subst hi
    simpa [pow_one] using hne
  · intro a ha
    exact edgeQuotient_sq hpf hnf a ha

/-! ## §3 主定理收口形升级（互斥 + edge 见证 + ⑤） -/

/-- **AUQTZYZ 主定理收口形（四槽版）**：`hEpc` + 互斥 + edge 非恒等见证 + ⑤ ⇒
`AuqtzyzConcl H x L1`。EPC 合取 8/9/3/1/4/5/6/7 供 conj1/③/is_normal；
④ 由 §2 从见证即时提升。剩余：批 ① EPC、互斥、edge 见证、⑤ 四事。 -/
theorem auqtzyzConclOfEpcAndDisjNe5 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hdisj : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        Disjoint ((H.quotientHypermap hnf).face a)
          ((H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a))
    (hne : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∃ a ∈ (H.quotientHypermap hnf).darts,
        (H.quotientHypermap hnf).edgeMap a ≠ a)
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
    (hasOrdersEdgeTwoOfNe hres.plain hnf (hne L hnf))
    (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.edgeQuotient_sq
#print axioms Kepler.Text.Reduction1.hasOrdersEdgeTwoOfNe
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndDisjNe5
