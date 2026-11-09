/-
LocalAuto7W12L: W12(b2b-ii-b3b 后半 a) — `hasOrders_p3` 合成（edge/node `HasOrders 2`）。

`p12l_hasOrders_two`：`f` 对合（`∀ x, f (f x) = x`）+ 某点被移动（`f a ≠ a`）
⟹ `hasOrders_p3 f 2`。两个实例：

* `p12l_edge_hasOrders`：`f = H.edgeMap = eeOfHyp`，见证 `x0 = (w0, r w0)`（`r w0 ≠ w0`）；
* `p12l_node_hasOrders`：`f = H.nodeMap = nnOfHyp`，见证 `x0`（`pre w0 ≠ r w0`，用 no2cycle）。

`p12j_face_rev`（`FF'rev` 侧轨道，~70-90）留 b3b 后半 b。W12E–K、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12K

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `hasOrders_p3 f 2`：对合 + 被移动点。 -/
private theorem p12l_hasOrders_two {α : Type*} {f : α → α} {a : α}
    (hinv : ∀ x, f (f x) = x) (hne : f a ≠ a) :
    hasOrders_p3 f 2 := by
  constructor
  · intro i hi0 hi2 hid
    have hi1 : i = 1 := by omega
    rw [hi1] at hid
    exact hne (by
      have h := congrFun hid a
      simpa using h)
  · funext x
    show (f^[2]) x = id x
    rw [show (2:ℕ) = 1 + 1 by omega, Function.iterate_succ_apply']
    exact hinv x

/-- edge 映射的 `HasOrders 2`。 -/
theorem p12l_edge_hasOrders {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hedgeM : (H.edgeMap : V3 × V3 → V3 × V3)
      = eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    hasOrders_p3 (H.edgeMap : V3 × V3 → V3 × V3) 2 := by
  refine p12l_hasOrders_two (a := (w0, p12b_R FF v w0)) ?_ ?_
  · intro x
    rw [hedgeM]
    exact p12k_ee_invol (E := E) hcl hedge hv x
  · intro hcontra
    have hx : eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (w0, p12b_R FF v w0) = (p12b_R FF v w0, w0) :=
      p12e_ee_step (E := E) hw0
    have h1 : (p12b_R FF v w0, w0) = (w0, p12b_R FF v w0) := by
      rw [← hx, ← hedgeM]
      exact hcontra
    exact (p12b_R_ne hcl hedge hv hw0) (congrArg Prod.fst h1)

/-- node 映射的 `HasOrders 2`。 -/
theorem p12l_node_hasOrders {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hnodeM : (H.nodeMap : V3 × V3 → V3 × V3)
      = nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    hasOrders_p3 (H.nodeMap : V3 × V3 → V3 × V3) 2 := by
  refine p12l_hasOrders_two (a := (w0, p12b_R FF v w0)) ?_ ?_
  · intro x
    rw [hnodeM]
    exact p12k_nn_invol (E := E) hcl hedge hv hw0 x
  · intro hcontra
    have hx : nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (w0, p12b_R FF v w0) = (w0, p12e_pre hcl hedge hv w0) :=
      p12e_nn_fwd hcl hedge hv hw0
    have h1 : (w0, p12e_pre hcl hedge hv w0) = (w0, p12b_R FF v w0) := by
      rw [← hx, ← hnodeM]
      exact hcontra
    have hpre : p12e_pre hcl hedge hv w0 = p12b_R FF v w0 := congrArg Prod.snd h1
    have hs := (p12e_pre_spec hcl hedge hv hw0).2
    rw [hpre] at hs
    exact p12e_no2cycle hcl hedge hv hw0 hcard3 w0 hw0 hs

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12l_edge_hasOrders
#print axioms Kepler.Text.p12l_node_hasOrders

end Kepler.Text
