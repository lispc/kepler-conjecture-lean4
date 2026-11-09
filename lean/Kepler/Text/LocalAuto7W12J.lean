/-
LocalAuto7W12J: W12(b2b-ii-b3) — 反向 dart 上的 `nn`/`ee` 单步（三 `HasOrders` 与
`darts = S ∪ node''S` 的前置）：

* `p12j_ee_step_rev`：`eeOfHyp (r w, w) = (w, r w)`；
* `p12j_nn_step_rev`：`nnOfHyp (r w, w) = (r w, r (r w))`（`EE (r w) = {w, r(r w)}` 两点）。

余下（face/edge/node 三 `HasOrders`、`darts = S ∪ node''S`）留 b3 后半。W12E–I、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12I

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `(r w, w) ∈ darts`（反向 dart）。 -/
private theorem p12j_dart_rev_mem {V : Set V3} {FF : Set (V3 × V3)} {v w : V3}
    (hw : w ∈ p12b_V V v) :
    (p12b_R FF v w, w) ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) := by
  refine Set.mem_union_left _ ?_
  show ({p12b_R FF v w, w} : Set V3) ∈ p12b_E V FF v
  rw [Set.pair_comm]
  exact ⟨w, hw, rfl⟩

/-- `eeOfHyp (r w, w) = (w, r w)`（反向 dart 的边映射单步）。 -/
theorem p12j_ee_step_rev {V : Set V3} {FF : Set (V3 × V3)} {v w : V3}
    (hw : w ∈ p12b_V V v) :
    eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) (p12b_R FF v w, w)
      = (w, p12b_R FF v w) := by
  unfold eeOfHyp_p3
  rw [if_pos (p12j_dart_rev_mem hw)]

/-- `nnOfHyp (r w, w) = (r w, r (r w))`（反向 dart 的节点映射单步）。 -/
theorem p12j_nn_step_rev {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) (p12b_R FF v w, w)
      = (p12b_R FF v w, p12b_R FF v (p12b_R FF v w)) := by
  have hEE := p12d_EE_eq (w := w) hcl hedge hv hw
  unfold nnOfHyp_p3
  rw [if_pos (p12j_dart_rev_mem hw), hEE]
  refine Prod.ext rfl ?_
  exact AZIM_CYCLE_TWO_POINT_SET_ALT (x := (0:V3)) (u := p12b_R FF v w)
    (v := w) (w := p12b_R FF v (p12b_R FF v w)) rfl

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12j_ee_step_rev
#print axioms Kepler.Text.p12j_nn_step_rev

end Kepler.Text
