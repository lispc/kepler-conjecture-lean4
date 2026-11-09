/-
LocalAuto7W12O: W12(b2b-ii-b3c) — `dih2k` 五合取里最后两块的 straight 支：
face `hasOrders k` 与 `darts = S ∪ node''S`。

* `p12o_nn_image_FF`：`nn '' FF' = FF'rev`（拿 `pre` 作原像）；
* `p12o_nn_image_FFrev`：`nn '' FF'rev = FF'`（`p12j_nn_step_rev` + `pre` 左逆）；
* `p12o_ff_hasOrders`：`hasOrders_p3 ff V'.ncard`（正向 `p12h_ff_period` 见证无小周期，
  反向 `ff^[k] = id` 分 `FF'`/`FF'rev`/darts 外三支，用两条轨道上的周期）；
* `p12o_darts_cover`：`H.darts = H.face x ∪ node '' H.face x`（`x ∈ H.darts`；
  `p12f_darts_eq` + `p12i_face_eq`/`p12j_face_rev` + 两条 node 像等式）。

W12E–N、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12N

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- 基点的周期沿轨道逐点成立：`f^[k] x0 = x0 ⟹ ∀ d ∈ orbitF f x0, f^[k] d = d`。 -/
private theorem p12o_period_on_orbit {α : Type*} {f : α → α} {x0 : α} {k : ℕ}
    (hper : f^[k] x0 = x0) :
    ∀ d ∈ orbitF_p3 f x0, f^[k] d = d := by
  rintro d ⟨a, rfl⟩
  calc f^[k] (f^[a] x0) = f^[k + a] x0 := (Function.iterate_add_apply _ _ _ _).symm
    _ = f^[a + k] x0 := by rw [Nat.add_comm]
    _ = f^[a] (f^[k] x0) := Function.iterate_add_apply _ _ _ _
    _ = f^[a] x0 := by rw [hper]

/-- `nn '' FF' = FF'rev`。 -/
theorem p12o_nn_image_FF {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) '' p12b_FF V FF v
      = p12f_FFrev V FF v := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hd
    have hpre := p12e_pre_spec hcl hedge hv hw
    rw [p12e_nn_fwd hcl hedge hv hw]
    exact ⟨p12e_pre hcl hedge hv w, hpre.1, Prod.ext hpre.2.symm rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(p12b_R FF v w, p12b_R FF v (p12b_R FF v w)),
      ⟨p12b_R FF v w, p12b_R_mem hcl hedge hv hw, rfl⟩, ?_⟩
    rw [p12e_nn_fwd hcl hedge hv (p12b_R_mem hcl hedge hv hw),
      p12m_pre_rho hcl hedge hv hw]

/-- `nn '' FF'rev = FF'`。 -/
theorem p12o_nn_image_FFrev {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) '' p12f_FFrev V FF v
      = p12b_FF V FF v := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hd
    rw [p12j_nn_step_rev hcl hedge hv hw]
    exact ⟨p12b_R FF v w, p12b_R_mem hcl hedge hv hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hpre := p12e_pre_spec hcl hedge hv hw
    refine ⟨(p12b_R FF v (p12e_pre hcl hedge hv w), p12e_pre hcl hedge hv w),
      ⟨p12e_pre hcl hedge hv w, hpre.1, rfl⟩, ?_⟩
    rw [p12j_nn_step_rev hcl hedge hv hpre.1]
    exact Prod.ext hpre.2 (by rw [hpre.2])

/-- **face 的 `HasOrders k`**（`k = V'.ncard`）：无小周期 + `ff^[k] = id`。 -/
theorem p12o_ff_hasOrders {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    hasOrders_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
      (p12b_V V v).ncard := by
  obtain ⟨hperR, -⟩ := p12g_period hcl hedge hv hw0
  obtain ⟨hper, hbefore⟩ := p12h_ff_period hcl hedge hv hw0
  have hpre0 : (p12e_pre hcl hedge hv)^[(p12b_V V v).ncard] w0 = w0 := by
    have h := p12m_pre_rho_iter hcl hedge hv (p12b_V V v).ncard hw0
    rwa [hperR] at h
  have hper_rev : (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[(p12b_V V v).ncard]
      (p12b_R FF v w0, w0) = (p12b_R FF v w0, w0) := by
    rw [p12m_ff_rev_iter hcl hedge hv (p12b_V V v).ncard hw0, hpre0]
  constructor
  · intro i hi0 hik hid
    exact hbefore i hi0 hik (by simpa using congrFun hid (w0, p12b_R FF v w0))
  · funext d
    show (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[(p12b_V V v).ncard] d = d
    by_cases hd : d ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v)
    · rw [p12f_darts_eq hcl hedge hv] at hd
      rcases hd with hd | hd
      · have hdorb : d ∈ orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
            (w0, p12b_R FF v w0) := by
          rw [← p12d_FF_orbit hcl hedge hv hw0]
          exact hd
        exact p12o_period_on_orbit hper d hdorb
      · have hy0 : (p12b_R FF v w0, w0) ∈ p12f_FFrev V FF v := ⟨w0, hw0, rfl⟩
        have hdorb : d ∈ orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
            (p12b_R FF v w0, w0) := by
          rw [p12j_face_rev hcl hedge hv hcard3 (p12b_R FF v w0, w0) hy0]
          exact hd
        exact p12o_period_on_orbit hper_rev d hdorb
    · have hstep : ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) d = d := by
        unfold ffOfHyp_p3
        rw [if_neg hd]
      rw [Function.iterate_fixed hstep (p12b_V V v).ncard]

/-- face 映射的 `HasOrders k`（`H.faceMap = ffOfHyp`，`k = V'.ncard`；
与 `p12l_edge_hasOrders`/`p12l_node_hasOrders` 同形）。 -/
theorem p12o_face_hasOrders {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hfaceM : (H.faceMap : V3 × V3 → V3 × V3)
      = ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    hasOrders_p3 (H.faceMap : V3 × V3 → V3 × V3) (p12b_V V v).ncard := by
  rw [hfaceM]
  exact p12o_ff_hasOrders hcl hedge hv hw0 hcard3

/-- **`darts = face x ∪ node '' face x`**（`x ∈ H.darts`；`dih2k_p3` 第二合取）。 -/
theorem p12o_darts_cover {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hdarts : (↑H.darts : Set (V3 × V3))
      = dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v))
    (hfaceM : (H.faceMap : V3 × V3 → V3 × V3)
      = ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
    (hnodeM : (H.nodeMap : V3 × V3 → V3 × V3)
      = nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    ∀ x ∈ H.darts,
      (↑H.darts : Set (V3 × V3))
        = H.face x ∪ (H.nodeMap : V3 × V3 → V3 × V3) '' H.face x := by
  intro x hx
  have hx' : x ∈ (↑H.darts : Set (V3 × V3)) := Finset.mem_coe.mpr hx
  have hfacex : H.face x
      = orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) x :=
    p12d_face_eq_orbit hfaceM x
  have himg : (H.nodeMap : V3 × V3 → V3 × V3) '' H.face x
      = nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) ''
        orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) x := by
    rw [hfacex, hnodeM]
  rw [hdarts] at hx' ⊢
  rw [p12f_darts_eq hcl hedge hv] at hx' ⊢
  rw [himg, hfacex]
  rcases hx' with hx' | hx'
  · obtain ⟨w, hw, hxw⟩ := hx'
    rw [hxw, p12i_face_eq hcl hedge hv hw0 hcard3 (w, p12b_R FF v w) ⟨w, hw, rfl⟩,
      p12o_nn_image_FF hcl hedge hv]
  · obtain ⟨w, hw, hxw⟩ := hx'
    rw [hxw, p12j_face_rev hcl hedge hv hcard3 (p12b_R FF v w, w) ⟨w, hw, rfl⟩,
      p12o_nn_image_FFrev hcl hedge hv, Set.union_comm]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12o_nn_image_FF
#print axioms Kepler.Text.p12o_nn_image_FFrev
#print axioms Kepler.Text.p12o_ff_hasOrders
#print axioms Kepler.Text.p12o_face_hasOrders
#print axioms Kepler.Text.p12o_darts_cover

end Kepler.Text
