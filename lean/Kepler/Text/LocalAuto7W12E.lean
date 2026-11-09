/-
LocalAuto7W12E: W12(b2b-ii-1a) — straight 支新扇的 **dih2k 前置基础设施**（第 1 件的一半）。
按 §42 契约修订，b2b 全件都带 `hcard3 : 3 ≤ V'.ncard`；本文件只交**不依赖 hcard3**
的原像件（后继的无 2-循环/EE 两点/节点步进/darts 计数会消费它）：

* `p12e_R_surj`：`r` 在 `V'` 上满射（像 ⊆ V' + `InjOn.ncard_image` + ncard 相等）；
* `p12e_pre` / `p12e_pre_spec`：`V'` 内的 choice 原像 `q`，满足 `r q = w`。

五合取本体（`dih2k_p3`：darts 计数 / face∪node / face·edge·node 的 hasOrders）
留下半 b2b-ii-1b，规模另报。LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12D

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `r` 在 `V'` 上是满射：像 ⊆ V'、像的 ncard = V'.ncard（单射像）⇒ 像 = V'。 -/
theorem p12e_R_surj {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ w ∈ p12b_V V v, ∃ q ∈ p12b_V V v, p12b_R FF v q = w := by
  have hinj : Set.InjOn (p12b_R FF v) (p12b_V V v) := by
    intro a ha b hb heq
    exact p12b_R_inj hcl hedge hv ha hb heq
  have hsub : p12b_R FF v '' p12b_V V v ⊆ p12b_V V v := by
    rintro _ ⟨a, ha, rfl⟩
    exact p12b_R_mem hcl hedge hv ha
  have himg : (p12b_R FF v '' p12b_V V v).ncard = (p12b_V V v).ncard :=
    hinj.ncard_image
  have heq : p12b_R FF v '' p12b_V V v = p12b_V V v := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (p12b_card hcl hv).1
    rw [himg]
  intro w hw
  have hmem : w ∈ p12b_R FF v '' p12b_V V v := by rw [heq]; exact hw
  obtain ⟨q, hq, hqw⟩ := hmem
  exact ⟨q, hq, hqw⟩

/-- `w` 的 `r`-原像（`V'` 内的 choice 函数；`w ∉ V'` 时取 `w`）。 -/
noncomputable def p12e_pre {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hv : v ∈ V) (w : V3) : V3 :=
  if h : w ∈ p12b_V V v then Classical.choose (p12e_R_surj hcl hedge hv w h) else w

/-- 原像在 `V'` 内且 `r (pre w) = w`。 -/
theorem p12e_pre_spec {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    p12e_pre hcl hedge hv w ∈ p12b_V V v ∧
      p12b_R FF v (p12e_pre hcl hedge hv w) = w := by
  unfold p12e_pre
  rw [dif_pos hw]
  exact Classical.choose_spec (p12e_R_surj hcl hedge hv w hw)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12e_R_surj
#print axioms Kepler.Text.p12e_pre_spec

end Kepler.Text
