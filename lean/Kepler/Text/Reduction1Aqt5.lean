/-
  Kepler.Text.Reduction1Aqt5 — dih2k 收口波：合取 ③（`hasOrders faceMap k`）全绿 +
  `dih2k` 组装骨架（conj1/③ 已证，②④⑤ 槽）+ 主定理「hEpc + ②④⑤ 槽」收口形。

  本文件三件：
  · `hasOrdersFaceQuotient` —— dih2k 合取 ③（HOL AUQTZYZ.hl:2183-:2258）：
    商 faceMap（= `fQuotientPerm`）的阶 = `CARD (face H x)`。**全真证**：
    `hasOrdersOfSupport`（Aqt4）+ `face_quotient_atom`（face 轨道 = 原子族）+
    `orbitMap_pow_inj`（i<k 时不动点矛盾）+ `pow_ncard_orbitMap_apply_self`
    （k = 轨道基数 ⇒ 幂回自身）。
  · `dih2kOfEpcConcl` —— dih2k 五合取组装：conj1 = Aqt3 `dih2kCard`，
    conj3 = 上件，conj2/4/5 为槽（② UNION 分解 / ④ edge 阶 2 / ⑤ node 阶 2）。
  · `auqtzyzConclOfEpcAndConj245` —— 主定理收口形：`hEpc` + ②④⑤ 三槽 ⇒
    `AuqtzyzConcl`（Aqt1 陈述 def）。**主定理剩余 = 批① EPC + dih2k 的
    ②④⑤ 三事**，均以显式槽列出。

  载体同 Aqt1–Aqt4（quotientHypermap / fQuotientPerm / atomsOfLoop /
  atomChoice / dih2k_p3 / hasOrders_p3）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt4
import Kepler.Text.TameSpine.TameList60
import Kepler.Text.TameSpine.TameList61

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §0 私桥：`atomsOfLoop (loopOfFace x)` 与 EPC 9/`cardAtomLoopOfFace`
的集合形同一（∃-次序差） -/

/-- `atomsOfLoop (loopOfFace x)` = `{a | ∃ x1, a = atom (loopOfFace x) x1 ∧
x1 ∈ (loopOfFace x).darts}`（HOL 两处集合形的 ∃-次序差桥）。 -/
theorem atomsOfLoopLoopOfFaceEq {α : Type*} [DecidableEq α] (H : Hypermap α) (x : α) :
    H.atomsOfLoop (H.loopOfFace x) =
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} := by
  ext a
  exact ⟨fun ⟨x1, hx1, hEq⟩ => ⟨x1, hEq, hx1⟩,
    fun ⟨x1, hEq, hx1⟩ => ⟨x1, hx1, hEq⟩⟩

/-! ## §1 合取 ③：`hasOrders faceMap k`（HOL AUQTZYZ.hl:2183-:2258） -/

/-- **dih2k 合取 ③**：商 hypermap 的 `faceMap`（= `fQuotientPerm`）在 support
`darts = atomsOfFamily {L1,L}` 上有阶 `k = CARD (face H x)`。
- `hs`：结构字段 `faceMap_permutes`；
- `hne`：`0<i<k` 取证人 `atom L y`（`hdart` 给 `y ∈ L.darts`），其 face 轨道 =
  `atomsOfLoop L`（基数 k），若 `(f^i) a = a` 则 `orbitMap_pow_inj`（a=0,b=i）矛盾；
- `hid`：`a = atom L' y` 的轨道 = `atomsOfLoop L'`（基数 k：L 侧 `hcard`、
  L1 侧 `cardAtomLoopOfFace`），`pow_ncard_orbitMap_apply_self` 收口。 -/
theorem hasOrdersFaceQuotient {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdart : ∃ y, y ∈ L.darts) :
    Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).faceMap : Set α → Set α)) (H.face x).ncard := by
  have hLmem : L ∈ ({H.loopOfFace x, L} : Set (Loop α)) := by
    rw [Set.mem_insert_iff]
    exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  refine Kepler.Text.Reduction1.hasOrdersOfSupport
    ((H.quotientHypermap hnf).faceMap) (H.quotientHypermap hnf).darts
    (H.face x).ncard (H.quotientHypermap hnf).faceMap_permutes ?_ ?_
  · -- hne：i<k 时 atom L y 被移动
    intro i h0 hk
    obtain ⟨y, hy⟩ := hdart
    refine ⟨H.atom L y, ?_, ?_⟩
    · rw [mem_darts_quotient]
      exact H.atom_mem_atomsOfFamily hLmem hy
    · intro hfix
      have hface : Kepler.Text.orbitMap (H.quotientHypermap hnf).faceMap (H.atom L y)
          = H.atomsOfLoop L :=
        H.face_quotient_atom hnf hLmem hy
      have hb : i < (Kepler.Text.orbitMap (H.quotientHypermap hnf).faceMap
          (H.atom L y)).ncard := by
        rw [hface, hcard]
        exact hk
      exact Kepler.Text.orbitMap_pow_inj (H.quotientHypermap hnf).faceMap_permutes
        (x := H.atom L y) (a := 0) (b := i) (by omega) hb
        (by simpa using hfix.symm)
  · -- hid：darts 上 f^k 逐点固定
    intro a ha
    rw [mem_darts_quotient] at ha
    obtain ⟨L', hL', y, hy, rfl⟩ := ha
    have horb : Kepler.Text.orbitMap (H.quotientHypermap hnf).faceMap (H.atom L' y)
        = H.atomsOfLoop L' :=
      H.face_quotient_atom hnf hL' hy
    have hkEq : (Kepler.Text.orbitMap (H.quotientHypermap hnf).faceMap
        (H.atom L' y)).ncard = (H.face x).ncard := by
      rw [horb]
      rcases Set.mem_insert_iff.mp hL' with h | h
      · rw [h, atomsOfLoopLoopOfFaceEq]
        exact Kepler.Text.TameSpine.cardAtomLoopOfFace H hres hx
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hcard
    have hfix := Kepler.Text.PermutesOn.pow_ncard_orbitMap_apply_self
      (H.quotientHypermap hnf).faceMap_permutes (H.atom L' y)
    rwa [hkEq] at hfix

/-! ## §2 dih2k 组装（conj1 = Aqt3，conj3 = §1，②④⑤ 槽） -/

/-- **`dih2kOfEpcConcl`（组装骨架）**：`dih2k_p3 (quotient H {L1,L}) k` 五合取：
① = Aqt3 `dih2kCard`；③ = §1 `hasOrdersFaceQuotient`；②/④/⑤ 为槽。 -/
theorem dih2kOfEpcConcl {α : Type*} [DecidableEq α] {H : Hypermap α} {x : α}
    {L : Loop α} (hres : H.IsRestricted) (hx : x ∈ H.darts)
    (hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)))
    (hcard : (H.atomsOfLoop L).ncard = (H.face x).ncard)
    (hdisj2 : (H.atomsOfLoop L ∩
      {a : Set α | ∃ x1, a = H.atom (H.loopOfFace x) x1 ∧
        x1 ∈ (H.loopOfFace x).darts} = ∅))
    (hdart : ∃ y, y ∈ L.darts)
    (h2 : ∀ a ∈ (H.quotientHypermap hnf).darts,
      (↑(H.quotientHypermap hnf).darts : Set (Set α)) =
        (H.quotientHypermap hnf).face a ∪
          (H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a)
    (h4 : Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).edgeMap : Set α → Set α)) 2)
    (h5 : Kepler.Text.hasOrders_p3
      (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2) :
    Kepler.Text.dih2k_p3 (H.quotientHypermap hnf) (H.face x).ncard :=
  ⟨dih2kCard hres hx hnf hcard hdisj2, h2,
    hasOrdersFaceQuotient hres hx hnf hcard hdart, h4, h5⟩

/-! ## §3 主定理收口形（hEpc + ②④⑤ 三槽 ⇒ `AuqtzyzConcl`） -/

/-- **AUQTZYZ 主定理收口形**：`hEpc`（批 ① 槽）+ dih2k 的 ②④⑤ 三槽（按
`L`/`hnf` 全称）⇒ `AuqtzyzConcl H x L1`（Aqt1 陈述 def）。conj1（Aqt3）与
conj3（§1）在证体内由 EPC 合取 8/9/3 即时供给。主定理剩余 = 批 ① 的 EPC 落库
+ ②/④/⑤ 三事。 -/
theorem auqtzyzConclOfEpcAndConj245 {α : Type*} [DecidableEq α]
    (hEpc : ∀ (H : Hypermap α) (x : α), ExistsPathComplementSlot H x)
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (h2 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        (↑(H.quotientHypermap hnf).darts : Set (Set α)) =
          (H.quotientHypermap hnf).face a ∪
            (H.quotientHypermap hnf).nodeMap '' (H.quotientHypermap hnf).face a)
    (h4 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      Kepler.Text.hasOrders_p3 (((H.quotientHypermap hnf).edgeMap : Set α → Set α)) 2)
    (h5 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      Kepler.Text.hasOrders_p3 (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2) :
    AuqtzyzConcl H x L1 := by
  intro hres hx hL1
  obtain ⟨L, hloop, hpath, hmem0, hnodes, hdisj, hclosL, hclosF, hcard, hdisj2,
    hcl1, hcl2, hcl3⟩ := hEpc H x hres hx
  subst hL1
  have hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)) :=
    isNormalOfEpcConcl hres hx hloop hmem0 hnodes hdisj hclosL hclosF
  refine ⟨L, hnf, hpath, ?_⟩
  exact dih2kOfEpcConcl hres hx hnf hcard hdisj2 ⟨_, hmem0⟩ (h2 L hnf) (h4 L hnf) (h5 L hnf)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.atomsOfLoopLoopOfFaceEq
#print axioms Kepler.Text.Reduction1.hasOrdersFaceQuotient
#print axioms Kepler.Text.Reduction1.dih2kOfEpcConcl
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfEpcAndConj245
