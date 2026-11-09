/-
LocalAuto7W12H: W12(b2b-ii-b 续) — `ff` 的周期（`face_eq_FF'` 的钥匙件）：

`p12h_ff_period`：`p12d_ff_iter`（`ff^[n] x0 = (r^[n] w0, r^[n+1] w0)`）+ `p12g_period`
（`r^[k] w0 = w0`、k 前不回）⟹ `ff^[k] x0 = x0` 且 `0 < i < k` 时 `ff^[i] x0 ≠ x0`，
`k = V'.ncard`、`x0 = (w0, r w0)`。

余下件（`face_eq_FF'`、三条 `HasOrders`、`darts = S ∪ node''S`）需要 `ff` 在
**反向 dart** `(r w, w)` 上的单步公式（`ff (r w, w) = (w, pre w)`）与在 dart 上的
单射性（`faceMap` 为置换），规模另报。W12E/F/G 与 LA7 均零改动。
-/
import Kepler.Text.LocalAuto7W12G

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `r^[n] w ∈ V'`（W12D 私件 `p12d_R_iter_mem` 的本地副本）。 -/
private theorem p12h_R_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => simpa using hw0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p12b_R_mem hcl hedge hv ih

/-- `ff` 的迭代公式（W12D 私件 `p12d_ff_iter` 的本地副本）：
`ff^[n] (w0, r w0) = (r^[n] w0, r^[n+1] w0)`。 -/
private theorem p12h_ff_iter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ,
      (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n]
          (w0, p12b_R FF v w0)
        = ((p12b_R FF v)^[n] w0, (p12b_R FF v)^[n + 1] w0) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk : (p12b_R FF v)^[k] w0 ∈ p12b_V V v :=
      p12h_R_iter_mem hcl hedge hv hw0 k
    have hsucc : (p12b_R FF v)^[k + 1] w0
        = p12b_R FF v ((p12b_R FF v)^[k] w0) :=
      Function.iterate_succ_apply' (p12b_R FF v) k w0
    have hexp : (p12b_R FF v)^[k + 1 + 1] w0
        = p12b_R FF v (p12b_R FF v ((p12b_R FF v)^[k] w0)) := by
      rw [Function.iterate_succ_apply' (p12b_R FF v) (k + 1) w0, hsucc]
    rw [hsucc, hexp]
    exact p12d_ff_step hcl hedge hv hk

/-- **`ff` 的周期**：`ff^[k] x0 = x0`，且 `k` 之前不回 `x0`（`k = V'.ncard`）。 -/
theorem p12h_ff_period {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[(p12b_V V v).ncard]
        (w0, p12b_R FF v w0) = (w0, p12b_R FF v w0) ∧
      ∀ i : ℕ, 0 < i → i < (p12b_V V v).ncard →
        (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[i]
            (w0, p12b_R FF v w0) ≠ (w0, p12b_R FF v w0) := by
  obtain ⟨hper, hbefore⟩ := p12g_period hcl hedge hv hw0
  constructor
  · rw [p12h_ff_iter hcl hedge hv hw0, hper]
    show (w0, (p12b_R FF v)^[(p12b_V V v).ncard + 1] w0)
      = (w0, p12b_R FF v w0)
    rw [Function.iterate_succ_apply', hper]
  · intro i hi0 hik hcontra
    have h1 := p12h_ff_iter hcl hedge hv hw0 i
    rw [h1] at hcontra
    exact hbefore i hi0 hik (congrArg Prod.fst hcontra)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12h_ff_period

end Kepler.Text
