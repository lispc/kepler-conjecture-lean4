/-
  JcajyduAqLeafW22c3a — W22c-iii-a：perimeter 根面消槽件（第三路，按探针裁决）。

  ┌─ 件表 ────────────────────────────────────────────────────────
  │ ① `p22c3_cardFaceGe3_of_degGt1`：`FAN + (∀ v ∈ V, 1 < ncard soe) + d ∈ dart1OfFan`
  │    ⇒ `3 ≤ face 轨道 ncard`（= TameLp:2607 `CARD_FACE_GE_3_TL` 的度前提改弱：
  │    `3 ≤` → `1 <`；末两行只用到 `setOfEdge d.2 V E ≠ {d.1}`，`1 <` 同样给）。
  │ ② `p22c3_cardSetOfEdgeGt1ImpCardFaceGe3`：= HOL
  │    `CARD_SET_OF_EDGE_GT_1_IMP_CARD_FACE_GE_3`（hypermap_and_fan.hl:2275）：
  │    `x ∈ dartOfFan` 的环支由度 > 1 排除（环 ⇒ `setOfEdge = ∅` ⇒ `1 < 0` 矛盾）⇒ ①。
  └───────────────────────────────────────────────────────────────
  ┌─ DIFFERS（相对 HOL）──────────────────────────────────────────
  │ 不移植 HOL `LINEAR_FACE`(1169-1196)/`LINEAR_FACE_2`(1199-1221)/
  │ `IN_DART1_OF_FAN_IMP_CARD_FACE_GT_1`(1324-1359) 三件（87 HOL 行）：
  │ 等价证明已由 TameLp:2607 `CARD_FACE_GE_3_TL` 承载（同构 digon 反证：
  │ face ⊇ {d, f d} ⇒ 2 ≤ ncard；反设 = 2 ⇒ f²d = d ⇒ `inverseSigmaFan` 撞 `SIGMA_FAN`）。
  │ 本件仅前提改弱 + 环排除（W22C3_PROBE_AND_PORT.md §3 的裁决）。
  └───────────────────────────────────────────────────────────────
  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameLp

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **度 > 1 ⇒ face 轨道 ≥ 3**（`CARD_FACE_GE_3_TL` 的度前提改弱版）。
证明 = 逐行复制 TameLp:2607 的 digon 反证；**唯一**吃 `3 ≤ ncard` 处 = 末段
`setOfEdge d.2 V E ≠ {d.1}`（`ncard = 1` 与 `1 < ncard` 矛盾，`omega` 收）。 -/
theorem p22c3_cardFaceGe3_of_degGt1 {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard) :
    3 ≤ ((hypermapOfFanTl V E hfan).face d).ncard := by
  set H := hypermapOfFanTl V E hfan with hHdef
  have hdarts : d ∈ H.darts := mem_dartsTl hd
  have hself : d ∈ H.face d := H.mem_face_self d
  have hfd : H.faceMap d ∈ H.face d := apply_mem_orbitMap H.faceMap d
  have hf_d_eq : H.faceMap d = (d.2, inverseSigmaFan 0 V E d.2 d.1) := by
    rw [faceMapTl_apply hd]; rfl
  have hvw : d.1 ≠ d.2 := edge_ne_of_fan hfan hd
  have hne : H.faceMap d ≠ d := by
    intro he
    rw [hf_d_eq, Prod.mk.injEq] at he
    exact hvw he.1.symm
  have hperm := H.faceMap_permutes
  have hfd1 : H.faceMap d ∈ dart1OfFan V E := by
    rw [← dartsTl_coe]
    exact hperm.apply_mem hdarts
  have hfin : (H.face d).Finite := orbitMap_finite hperm d
  have hpair : ({d, H.faceMap d} : Set (V3 × V3)) ⊆ H.face d := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hself
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hfd
  have h2 : 2 ≤ (H.face d).ncard := by
    have hcard2 : ({d, H.faceMap d} : Set (V3 × V3)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hne)
    calc 2 = ({d, H.faceMap d} : Set (V3 × V3)).ncard := hcard2.symm
      _ ≤ (H.face d).ncard := Set.ncard_le_ncard hpair hfin
  by_contra hcon
  have h2eq : (H.face d).ncard = 2 := by omega
  have hsub_eq : ({d, H.faceMap d} : Set (V3 × V3)) = H.face d := by
    refine Set.eq_of_subset_of_ncard_le hpair ?_ hfin
    rw [h2eq, Set.ncard_pair (Ne.symm hne)]
  have hf2 : H.faceMap (H.faceMap d) ∈ H.face d := by
    have h := pow_apply_mem_orbitMap H.faceMap 2 d
    rwa [show H.faceMap ^ 2 = H.faceMap * H.faceMap from pow_two _,
      Equiv.Perm.mul_apply] at h
  have hne2 : H.faceMap (H.faceMap d) ≠ H.faceMap d := fun h =>
    hne (Equiv.injective H.faceMap h)
  rw [← hsub_eq] at hf2
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hf2
  rcases hf2 with h22 | h22
  · -- f²d = d ⟹ 首分量 inverseSigmaFan d.2 d.1 = d.1
    have hι : inverseSigmaFan 0 V E d.2 d.1 = d.1 := by
      have h : H.faceMap (H.faceMap d) = ((d.1 : V3), (d.2 : V3)) := by
        rw [h22]
      rw [faceMapTl_apply hfd1, hf_d_eq] at h
      simp only [fFanPair, Prod.mk.injEq] at h
      exact h.1
    have he21 : {d.2, d.1} ∈ E := by rw [Set.pair_comm]; exact hd
    have hfan21 := FAN_in_setOfEdge 0 V E d.2 d.1 hfan he21
    obtain ⟨hmem, hsig⟩ := inverseSigmaFan_eq hfan hfan21.2.2.1 hι
    have h1d2 : 1 < (setOfEdge d.2 V E).ncard := hcard d.2 hfan21.1
    have hne1 : setOfEdge d.2 V E ≠ {d.1} := by
      intro he
      rw [he, Set.ncard_singleton] at h1d2
      omega
    exact (SIGMA_FAN hne1 hfan hmem).2.1 hsig
  · exact hne2 h22

/-- **HOL `CARD_SET_OF_EDGE_GT_1_IMP_CARD_FACE_GE_3`**（hypermap_and_fan.hl:2275）：
`FAN` + 一切顶点度 > 1 ⇒ `dartOfFan` 上 face 轨道 ≥ 3。
环支（`dartOfFan` 的 `{d | d.1 = d.2 ∧ … ∧ setOfEdge = ∅}` 部分）由度 > 1 排除
（`1 < 0` 矛盾），余下即 ①。 -/
theorem p22c3_cardSetOfEdgeGt1ImpCardFaceGe3 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard)
    {x : V3 × V3} (hx : x ∈ dartOfFan V E) :
    3 ≤ ((hypermapOfFanTl V E hfan).face x).ncard := by
  have hx1 : x ∈ dart1OfFan V E := by
    unfold dartOfFan at hx
    rcases hx with h | h
    · obtain ⟨-, h1V, hiso⟩ := h
      have h1 := hcard x.1 h1V
      rw [hiso] at h1
      simp at h1
    · exact h
  exact p22c3_cardFaceGe3_of_degGt1 (d := x) hfan hx1 hcard

end Kepler.Text

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.p22c3_cardFaceGe3_of_degGt1
#print axioms Kepler.Text.p22c3_cardSetOfEdgeGt1ImpCardFaceGe3
