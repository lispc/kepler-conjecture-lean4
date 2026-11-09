/-
LocalAuto7W12P: W12(b2b-ii-c) — straight 支封顶组装（`dih2k_p3` + `localFan_p3` + `LocalFan`）。

* `p12p_dih2k_p3`：`dih2k_p3 H FF'.ncard` 五合取——第一 `p12f_darts_card`，第二
  `p12o_darts_cover`，第三 `p12o_face_hasOrders`（`p12f_FF_card` 把 `k` 换到 `V'.ncard`），
  第四/五 `p12l_edge_hasOrders`/`p12l_node_hasOrders`；
* `p12p_localFan_p3`：`localFan_p3 V' E' FF'` 七合取——`p12c_FAN` 给 `FAN`，
  `exists_hypHyp_of_fan` 给 H 与四条映射等式，`p12d_face_orbit` 给第六合取；
* `p12p_LocalFan`：`LocalFan V' E' FF'`——`LocalFan.of_localFan_p3` 收口，`hno` 由
  `p12f_darts_eq` 与 `p12f_ordPairs_eq` 组装（`dart1OfFan` 与 `ordPairs_p3` 同体）。

W12E–O、LA7、AzimBridge 零改动。
-/
import Kepler.Text.LocalAuto7W12O

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **`dih2k_p3 H FF'.ncard`**（五合取；`H` 的四条映射等式由 `exists_hypHyp_of_fan` 供）。 -/
theorem p12p_dih2k_p3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hdarts : (↑H.darts : Set (V3 × V3))
      = dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v))
    (hedgeM : (H.edgeMap : V3 × V3 → V3 × V3)
      = eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
    (hnodeM : (H.nodeMap : V3 × V3 → V3 × V3)
      = nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
    (hfaceM : (H.faceMap : V3 × V3 → V3 × V3)
      = ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    dih2k_p3 H (p12b_FF V FF v).ncard := by
  refine ⟨p12f_darts_card hcl hedge hv hw0 hcard3 hdarts, ?_, ?_, ?_, ?_⟩
  · exact p12o_darts_cover hcl hedge hv hw0 hcard3 hdarts hfaceM hnodeM
  · rw [p12f_FF_card]
    exact p12o_face_hasOrders hcl hedge hv hw0 hcard3 hfaceM
  · exact p12l_edge_hasOrders hcl hedge hv hw0 hedgeM
  · exact p12l_node_hasOrders hcl hedge hv hw0 hcard3 hnodeM

/-- **`localFan_p3 V' E' FF'`**（七合取；H 取 `exists_hypHyp_of_fan` 的见证）。 -/
theorem p12p_localFan_p3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    {w0 : V3} (hw0 : w0 ∈ p12b_V V v) (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    localFan_p3 (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) := by
  have hfan : FAN (0:V3) (p12b_V V v) (p12b_E V FF v) :=
    p12c_FAN hcl hedge hg hv hpi hcard
  obtain ⟨H, hdarts, hedgeM, hnodeM, hfaceM⟩ := exists_hypHyp_of_fan hfan
  exact ⟨H, hdarts, hedgeM, hnodeM, hfaceM, hfan,
    p12d_face_orbit hcl hedge hv hw0 hdarts hfaceM,
    p12p_dih2k_p3 hcl hedge hv hw0 hcard3 hdarts hedgeM hnodeM hfaceM⟩

/-- **`LocalFan V' E' FF'`**（straight 支的 local-fan 收口；`hno` = 无孤立点）。 -/
theorem p12p_LocalFan {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    {w0 : V3} (hw0 : w0 ∈ p12b_V V v) (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    LocalFan (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) := by
  refine LocalFan.of_localFan_p3
    (p12p_localFan_p3 hcl hedge hg hv hpi hcard hw0 hcard3) ?_
  rw [p12f_darts_eq hcl hedge hv, ← p12f_ordPairs_eq hcl hedge hv]
  rfl

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12p_dih2k_p3
#print axioms Kepler.Text.p12p_localFan_p3
#print axioms Kepler.Text.p12p_LocalFan

end Kepler.Text
