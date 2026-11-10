/-
  Kepler.Text.Reduction1Aqt3 — AUQTZYZ 主定理 dih2k 段（AUQTZYZ.hl:1987-:2613，627 行）
  第一段：`atoms_of_family` 两族分解 + 合取 ①（`darts.card = 2*k`）。

  本文件两件：
  · `atomsFamilyPair` —— 两环正规族的原子族 = 两环原子族之并
    （HOL :1990-:2033 的 EXTENSION 分解，`NF = {L1, L2}` 特化）。
  · `dih2kCard` —— dih2k 合取 ①（HOL :2036-:2062）：
    `(quotient H {L1,L2}).darts.card = 2 * CARD (face H x)`，由
    `quotientHypermap_spec`（darts = atomsOfFamily）+ 两族基数
    （EPC 8 `hcard`、`:441 card_atom_loop_of_face`）+ 互斥（EPC 9 `hdisj2`）+
    `CARD_UNION_EQ`（Aqt1 `cardUnionEq` / mathlib `Set.ncard_union_eq`）合成。

  dih2k 合取 ②–⑤（HOL :2047-:2611）**冻结**，入口表见 DELIVERY_AQT3 §3。

  载体折算：`atoms_of_family` ↦ `H.atomsOfFamily`；`atoms_of_loop` ↦
  `H.atomsOfLoop`；`quotient H NF` ↦ `H.quotientHypermap hnf`（spec 四元组）；
  `CARD` ↦ `Set.ncard`；`dih2k` ↦ `Kepler.Text.dih2k_p3`。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt1
import Kepler.Text.Reduction1Aqt2
import Kepler.Text.TameSpine.TameList60
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 `atoms_of_family` 两族分解（HOL :1990-:2033） -/

/-- **HOL `AUQTZYZ` 证体的子目标**（AUQTZYZ.hl:1990-:2033）：
`atoms_of_family H {L1,L2} = atoms_of_loop H L1 ∪ atoms_of_loop H L2`
（HOL 用 EXTENSION 两面 + `SET_TAC`；Lean `ext` + 逐支构造）。 -/
theorem atomsFamilyPair {α : Type*} [DecidableEq α] (H : Hypermap α)
    (L1 L2 : Loop α) :
    H.atomsOfFamily ({L1, L2} : Set (Loop α)) = H.atomsOfLoop L1 ∪ H.atomsOfLoop L2 := by
  ext a
  constructor
  · rintro ⟨L', hL', y, hy, rfl⟩
    rcases Set.mem_insert_iff.mp hL' with rfl | hL'
    · exact Or.inl ⟨y, hy, rfl⟩
    · rw [Set.mem_singleton_iff] at hL'
      exact Or.inr ⟨y, by rw [hL'] at hy; exact hy, by rw [hL']⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨L1, by simp, y, hy, rfl⟩
    · exact ⟨L2, by simp, y, hy, rfl⟩

/-! ## §2 dih2k 合取 ①：`darts.card = 2*k`（HOL :2036-:2062） -/

/-- **HOL `AUQTZYZ` 的 dih2k 合取 ①**（AUQTZYZ.hl:2036-:2062）：
`(quotient H {L1,L2}).darts.card = 2 * CARD (face H x)`，
`L1 = loop_of_face H x`。供料：`quotientHypermap_spec` 的 darts 槽、
`atomsFamilyPair`、EPC 8（`hcard`）、`cardAtomLoopOfFace`（`:441`）、
EPC 9（`hdisj2`）+ `Set.ncard_union_eq`。 -/
theorem dih2kCard {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α} {L : Loop α}
    (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅)) :
    (H.quotientHypermap hnf).darts.card = 2 * (H.face x).ncard := by
  -- 商 darts = atomsOfFamily（spec 第 1 槽 + Finset 强制转换）
  have hdarts : (H.quotientHypermap hnf).darts.card
      = (H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α))).ncard := by
    rw [← Set.ncard_coe_finset, (H.quotientHypermap_spec hnf).1]
  -- 两族基数
  have hcard1 : (H.atomsOfLoop L).ncard = (H.face x).ncard := hcard
  -- atomsOfLoop (loopOfFace x) 与 EPC 9 的集合形同一
  have hsetEq : H.atomsOfLoop (H.loopOfFace x)
      = {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
          x1 ∈ (H.loopOfFace x).darts} := by
    ext a
    exact ⟨fun ⟨x1, hx1, hEq⟩ => ⟨x1, hEq, hx1⟩,
      fun ⟨x1, hEq, hx1⟩ => ⟨x1, hx1, hEq⟩⟩
  have hcard2 : (H.atomsOfLoop (H.loopOfFace x)).ncard = (H.face x).ncard := by
    rw [hsetEq]
    exact Kepler.Text.TameSpine.cardAtomLoopOfFace H hres hx
  -- 互斥
  have hdisj : Disjoint (H.atomsOfLoop L) (H.atomsOfLoop (H.loopOfFace x)) := by
    rw [Set.disjoint_iff_inter_eq_empty, hsetEq]
    exact hdisj2
  -- 并 = 两族之和
  have hfin1 : (H.atomsOfLoop L).Finite :=
    H.atomsOfLoop_finite hnf (by simp)
  have hfin2 : (H.atomsOfLoop (H.loopOfFace x)).Finite :=
    H.atomsOfLoop_finite hnf (by simp)
  have hunion : (H.atomsOfFamily ({H.loopOfFace x, L} : Set (Loop α))).ncard
      = (H.atomsOfLoop L).ncard + (H.atomsOfLoop (H.loopOfFace x)).ncard := by
    rw [atomsFamilyPair, Set.union_comm, Set.ncard_union_eq hdisj hfin1 hfin2]
  rw [hdarts, hunion, hcard1, hcard2]
  omega

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.atomsFamilyPair
#print axioms Kepler.Text.Reduction1.dih2kCard
