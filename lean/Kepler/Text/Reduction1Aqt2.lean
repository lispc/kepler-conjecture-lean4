/-
  Kepler.Text.Reduction1Aqt2 — AUQTZYZ 主定理本体（hEpc 槽版）：is_normal 段 +
  dih2k 槽包装。

  本文件两件：
  · `isNormalOfEpcConcl` —— HOL AUQTZYZ.hl:1867-:1985（119 行）的 `is_normal`
    验证段：由 EPC 的合取 1/3/4/5/6/7 + `is_restricted` 证
    `H.IsNormalFamily {loop_of_face H x, L}`。**本段已全真证**。
  · `auqtzyzConclOfEpcAndDih` —— HOL AUQTZYZ.hl:1859-:2624 的包装形：给
    EPC 槽（`hEpc`）+ dih2k 段槽（`hdih`）+ `hres`/`hx`/`L1 = loopOfFace`，
    收口 `AuqtzyzConcl`（Aqt1 的陈述 def）。dih2k 段（HOL :1987-:2613，627 行）
    **冻结**，见 DELIVERY_AQT2 §3。

  陈述对账：`isNormalOfEpcConcl` 的前提逐字取自 `ExistsPathComplementSlot`
  （Aqt1）的合取 1/3/4/5/6/7（`is_loop`/`in_dart_of_loop (complement H x 0) L`/
  `∃y z` 异 node/`dart_of_loop L ∩ face H x = {}`/两条 node 闭包）；
  `is_restricted` 与 `x ∈ dart` 是 EPC 前件本身。**零省前提**。

  载体折算：`is_normal H {L1,L2}` ↦ `H.IsNormalFamily ({L1, L2} : Set (Loop α))`
  （Hypermap.lean:6808）；`loop_of_face` ↦ `H.loopOfFace`；`dart_of_loop L` ↦
  `L.darts`；`in_dart_of_loop` ↦ 成员；`complement H x 0 = nodeMap x`
  （`complementPt` 定义面，rfl 级）。dih2k 段槽的 `quotient H {L1,L2}` ↦
  `H.quotientHypermap hnf`（同 Aqt1 `AuqtzyzConcl` 的 ∃-证人形）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt1
import Kepler.Text.TameSpine.TameList60

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 is_normal 验证段（HOL AUQTZYZ.hl:1867-:1985） -/

/-- **HOL `AUQTZYZ` 的 `is_normal` 子目标**（AUQTZYZ.hl:1867-:1968）：
EPC 的合取 1/3/4/5/6/7 + `is_restricted` + `x ∈ dart H` ⇒
`is_normal H {loop_of_face H x, L}`。四公理逐条：
① 两环都是 loops（`loopOfFace_isLoop` / EPC 1）且各有一个 dart 落在 `dart H` 内
（`x` / `complement H x 0 = nodeMap x`）；
② 每环有两个位于不同 node 的 dart（`loopOfFace x` 取 `x` 与 `face_map x`，
由 `Simple` 的 `node ∩ face = {dart}` 与 `CARD_FACE_LE3`（face ≥3 ⇒
`faceMap x ≠ x`）反证；`L` 取 EPC 4）；
③ 两环 dart 不交（`L` 侧由 EPC 5 + `loopOfFace_darts`）；
④ node 闭包（`L` 侧 EPC 6，`loopOfFace x` 侧 EPC 7）。 -/
theorem isNormalOfEpcConcl {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hloop : L.IsLoopOf H)
    (hmem0 : H.complementPt x 0 ∈ L.darts)
    (hnodes : ∃ y ∈ L.darts, ∃ z ∈ L.darts, H.node y ≠ H.node z)
    (hdisj : ((↑L.darts : Set α) ∩ H.face x = ∅))
    (hclosL : ∀ y ∈ L.darts, ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x)
    (hclosF : ∀ y, y ∈ H.face x → ∀ z, z ∈ H.node y → z ∈ L.darts ∨ z ∈ H.face x) :
    H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) := by
  have hcompl : H.complementPt x 0 = H.nodeMap x := rfl
  have hxn : H.nodeMap x ∈ H.darts := H.nodeMap_apply_mem hx
  -- loopOfFace x 的 dart 集 = face x（Finset ↔ Set 桥）
  have hdartsF : ∀ y, y ∈ (H.loopOfFace x).darts ↔ y ∈ H.face x :=
    fun y => H.mem_faceFinset x y
  -- {a, b} 的成员拆条
  have hmem2 : ∀ (L' : Loop α), L' ∈ ({H.loopOfFace x, L} : Set (Loop α)) →
      L' = H.loopOfFace x ∨ L' = L := by
    intro L' hL'
    rcases Set.mem_insert_iff.mp hL' with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  have hmemL : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  have hmemF : H.loopOfFace x ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ① loops 且各有一个 dart
    intro L' hL'
    rcases hmem2 L' hL' with rfl | rfl
    · exact ⟨H.loopOfFace_isLoop x, ⟨x, hx, (hdartsF x).mpr (H.mem_face_self x)⟩⟩
    · exact ⟨hloop, ⟨H.complementPt x 0, by rw [hcompl]; exact hxn, hmem0⟩⟩
  · -- ② 每环两个异 node 的 dart
    intro L' hL'
    rcases hmem2 L' hL' with rfl | rfl
    · -- loop_of_face x：证人 x、faceMap x
      have h3 : 3 ≤ (H.face x).ncard := hres.three_le_ncard_face hx
      have hne : H.faceMap x ≠ x := Kepler.Text.TameSpine.CARD_FACE_LE3 H h3
      have hx' : H.faceMap x ∈ H.darts := H.faceMap_apply_mem hx
      refine ⟨x, (hdartsF x).mpr (H.mem_face_self x),
        H.faceMap x, (hdartsF (H.faceMap x)).mpr (H.pow_faceMap_mem_face x 1), ?_⟩
      -- node x ≠ node (faceMap x)：若相等，x 与 faceMap x 同在 node(faceMap x) ∩ face(faceMap x)
      intro hcon
      have hx1 : x ∈ H.node (H.faceMap x) := by rw [← hcon]; exact H.mem_node_self x
      have hx2 : x ∈ H.face (H.faceMap x) := by
        rw [faceFaceMapEq H x]; exact H.mem_face_self x
      have hfx2 : H.faceMap x ∈ H.face (H.faceMap x) := by
        rw [faceFaceMapEq H x]; exact H.pow_faceMap_mem_face x 1
      have hsimp := hres.simple (H.faceMap x) hx'
      have hxint : x ∈ H.node (H.faceMap x) ∩ H.face (H.faceMap x) := ⟨hx1, hx2⟩
      rw [hsimp] at hxint
      exact hne (Set.mem_singleton_iff.mp hxint).symm
    · exact hnodes
  · -- ③ 两环 dart 不交
    intro L₁ hL₁ L₂ hL₂ y hy1 hy2
    by_cases h1 : L₁ = H.loopOfFace x
    · by_cases h2 : L₂ = H.loopOfFace x
      · rw [h1, h2]
      · have h2' : L₂ = L := by
          rcases hmem2 L₂ hL₂ with h | h
          · exact absurd h h2
          · exact h
        rw [h1] at hy1
        rw [h2'] at hy2
        have hy : y ∈ (↑L.darts : Set α) ∩ H.face x :=
          ⟨hy2, (hdartsF y).mp hy1⟩
        rw [hdisj] at hy
        exact absurd hy (by simp)
    · have h1' : L₁ = L := by
        rcases hmem2 L₁ hL₁ with h | h
        · exact absurd h h1
        · exact h
      by_cases h2 : L₂ = H.loopOfFace x
      · rw [h1', h2]
        rw [h2] at hy2
        rw [h1'] at hy1
        have hy : y ∈ (↑L.darts : Set α) ∩ H.face x :=
          ⟨hy1, (hdartsF y).mp hy2⟩
        rw [hdisj] at hy
        exact absurd hy (by simp)
      · have h2' : L₂ = L := by
          rcases hmem2 L₂ hL₂ with h | h
          · exact absurd h h2
          · exact h
        rw [h1', h2']
  · -- ④ node 闭包
    intro L' hL' u v hu hv
    by_cases h1 : L' = H.loopOfFace x
    · rw [h1] at hu
      rcases hclosF u ((hdartsF u).mp hu) v hv with hv' | hv'
      · exact ⟨L, hmemL, hv'⟩
      · exact ⟨H.loopOfFace x, hmemF, (hdartsF v).mpr hv'⟩
    · have h1' : L' = L := by
        rcases hmem2 L' hL' with h | h
        · exact absurd h h1
        · exact h
      rw [h1'] at hu
      rcases hclosL u hu v hv with hv' | hv'
      · exact ⟨L, hmemL, hv'⟩
      · exact ⟨H.loopOfFace x, hmemF, (hdartsF v).mpr hv'⟩

/-! ## §2 包装形（hEpc + hdih 槽） -/

/-- **AUQTZYZ 主定理的 hEpc + dih2k 槽包装**：
`hEpc`（批 ① 槽）+ `hdih`（dih2k 段槽：对任一 `is_normal` 证人成立 `dih2k_p3`）
⇒ `AuqtzyzConcl H x L1`（Aqt1 陈述 def 逐字）。dih2k 段（HOL :1987-:2613）
冻结，下一波以 `hdih` 槽填。 -/
theorem auqtzyzConclOfEpcAndDih {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hdih : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
        Kepler.Text.dih2k_p3 (H.quotientHypermap hnf) (H.face x).ncard) :
    AuqtzyzConcl H x L1 := by
  intro hres hx hL1
  obtain ⟨L, hloop, hpath, hmem0, hnodes, hdisj, hclosL, hclosF, hcard, hdisj2,
    hcl1, hcl2, hcl3⟩ := hEpc H x hres hx
  subst hL1
  have hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    isNormalOfEpcConcl hres hx hloop hmem0 hnodes hdisj hclosL hclosF
  exact ⟨L, hnf, hpath, hdih L hnf⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.isNormalOfEpcConcl
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndDih
