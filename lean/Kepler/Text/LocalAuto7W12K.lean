/-
LocalAuto7W12K: W12(b2b-ii-b3b) — darts 对称 + `ee`/`nn` 对合（edge/node `HasOrders 2` 的数学内容）。

* `p12k_darts_swap`：`d ∈ darts ⇒ (d.2, d.1) ∈ darts`；
* `p12k_ee_invol`：`eeOfHyp (eeOfHyp d) = d`（darts 上换向、darts 外恒等）；
* `p12k_nn_invol`：`nnOfHyp (nnOfHyp d) = d`（`p12e_nn_fwd`/`p12e_nn_back`/`p12j_nn_step_rev`）。

`hasOrders_p3` 的合成（`f^[2] = id` + `f ≠ id` 的见证形）与 `p12j_face_rev` 留 b3b 后半/下一批。
W12E–J、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12J

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `d ∈ darts ⇒ (d.2, d.1) ∈ darts`（darts 对交换封闭）。 -/
theorem p12k_darts_swap {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ d ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v),
      (d.2, d.1) ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) := by
  intro d hd
  rw [p12f_darts_eq hcl hedge hv] at hd ⊢
  rcases hd with hd | hd
  · obtain ⟨w, hw, rfl⟩ := hd
    exact Or.inr ⟨w, hw, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := hd
    exact Or.inl ⟨w, hw, rfl⟩

/-- `eeOfHyp` 是对合。 -/
theorem p12k_ee_invol {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) (d : V3 × V3) :
    eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) d)
      = d := by
  by_cases hd : d ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v)
  · have hd' : (d.2, d.1) ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) :=
      p12k_darts_swap hcl hedge hv d hd
    unfold eeOfHyp_p3
    rw [if_pos hd, if_pos hd']
  · have hin : eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) d = d := by
      unfold eeOfHyp_p3
      rw [if_neg hd]
    rw [hin]
    exact hin

/-- `nnOfHyp` 是对合（`FF'` 两侧 + darts 外恒等）。 -/
theorem p12k_nn_invol {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) (d : V3 × V3) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) d)
      = d := by
  by_cases hd : d ∈ dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v)
  · rw [p12f_darts_eq hcl hedge hv] at hd
    rcases hd with hd | hd
    · -- 正向 dart `(w, r w)`：`nn → (w, pre)`，再 `nn → (w, r w)`
      obtain ⟨w, hw, rfl⟩ := hd
      rw [p12e_nn_fwd hcl hedge hv hw, p12e_nn_back hcl hedge hv hw]
    · -- 反向 dart `(r w, w)`：`nn → (r w, r(r w))`（正向），再 `nn → (r w, pre(r w)) = (r w, w)`
      obtain ⟨w, hw, rfl⟩ := hd
      rw [p12j_nn_step_rev hcl hedge hv hw]
      -- 目标：nn (r w, r(r w)) = (r w, w)
      have hrw : p12b_R FF v w ∈ p12b_V V v := p12b_R_mem hcl hedge hv hw
      rw [p12e_nn_fwd hcl hedge hv hrw]
      -- 目标：(r w, pre (r w)) = (r w, w)：用 r(pre(r w)) = r w 的单射
      refine Prod.ext rfl ?_
      have hs := (p12e_pre_spec hcl hedge hv hrw).2
      have hpre : p12e_pre hcl hedge hv (p12b_R FF v w) = w :=
        p12b_R_inj hcl hedge hv (p12e_pre_spec hcl hedge hv hrw).1 hw hs
      rw [hpre]
  · have hin : nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) d = d := by
      unfold nnOfHyp_p3
      rw [if_neg hd]
    rw [hin]
    exact hin

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12k_darts_swap
#print axioms Kepler.Text.p12k_ee_invol
#print axioms Kepler.Text.p12k_nn_invol

end Kepler.Text
