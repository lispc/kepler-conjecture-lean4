/-
LocalAuto7W12I: W12(b2b-ii-b2) — `ff` 反向单步 + `face_eq_FF'`（FF' 侧）。

* `p12i_ff_step_rev`：`ff (r w, w) = (w, pre w)`（两点 EE 上 ivs 另一侧）。
* `p12i_ff_iter_mod`：`ff^[n] x0 = ff^[n % k] x0`（k = V'.ncard，`ff^[k] x0 = x0`）。
* `p12i_face_eq`：`x ∈ FF' ⇒ orbitF_p3 ff x = FF'`（双向；`FF'` = orbit x0，周期 k）。

`FF'rev` 侧与三条 `HasOrders`/`darts = S ∪ node''S` 留 b3。W12E–H、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12H

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `ff (r w, w) = (w, pre w)`（反向 dart 的单步；ivs 在 `{r w, pre w}` 上取另一侧）。 -/
theorem p12i_ff_step_rev {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (p12b_R FF v w, w)
      = (w, p12e_pre hcl hedge hv w) := by
  have hdart : (p12b_R FF v w, w) ∈
      dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) := by
    refine Set.mem_union_left _ ?_
    show ({p12b_R FF v w, w} : Set V3) ∈ p12b_E V FF v
    rw [Set.pair_comm]
    exact ⟨w, hw, rfl⟩
  have hEE := p12e_EE_w hcl hedge hv hw
  unfold ffOfHyp_p3
  rw [if_pos hdart, hEE]
  refine Prod.ext rfl ?_
  exact IVS_AZIM_CYCLE_TWO_POINT_SET (p12b_R FF v w)
    (p12e_pre hcl hedge hv w) (0:V3) w

/-- `ff^[k * q] x0 = x0`（`k = V'.ncard`）。 -/
private theorem p12i_ff_pow_mul {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ q : ℕ,
      (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[(p12b_V V v).ncard * q]
          (w0, p12b_R FF v w0) = (w0, p12b_R FF v w0) := by
  obtain ⟨hper, -⟩ := p12h_ff_period hcl hedge hv hw0
  intro q
  induction q with
  | zero => simp
  | succ m ihm =>
    rw [Nat.mul_succ, Function.iterate_add_apply, hper, ihm]

/-- `ff^[n] x0 = ff^[n % k] x0`（k = V'.ncard）。 -/
private theorem p12i_ff_iter_mod {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) (n : ℕ) :
    (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n]
        (w0, p12b_R FF v w0)
      = (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n % (p12b_V V v).ncard]
          (w0, p12b_R FF v w0) := by
  have h1 : n = n % (p12b_V V v).ncard + (p12b_V V v).ncard * (n / (p12b_V V v).ncard) :=
    (Nat.mod_add_div n (p12b_V V v).ncard).symm
  calc (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n] (w0, p12b_R FF v w0)
      = (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[
          n % (p12b_V V v).ncard + (p12b_V V v).ncard * (n / (p12b_V V v).ncard)]
          (w0, p12b_R FF v w0) := by conv_lhs => rw [h1]
    _ = (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n % (p12b_V V v).ncard]
          ((ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[
            (p12b_V V v).ncard * (n / (p12b_V V v).ncard)] (w0, p12b_R FF v w0)) :=
        Function.iterate_add_apply _ _ _ _
    _ = (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n % (p12b_V V v).ncard]
          (w0, p12b_R FF v w0) := by
        rw [p12i_ff_pow_mul hcl hedge hv hw0 (n / (p12b_V V v).ncard)]

/-- **`face_eq_FF'`（FF' 侧）**：`x ∈ FF' ⇒ orbitF_p3 ff x = FF'`。 -/
theorem p12i_face_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ∀ x ∈ p12b_FF V FF v,
      orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) x
        = p12b_FF V FF v := by
  obtain ⟨hper, hbefore⟩ := p12h_ff_period hcl hedge hv hw0
  set ff := ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) with hff
  set x0 : V3 × V3 := (w0, p12b_R FF v w0) with hx0
  have hFF : p12b_FF V FF v = orbitF_p3 ff x0 := p12d_FF_orbit hcl hedge hv hw0
  intro x hx
  have hxorb : x ∈ orbitF_p3 ff x0 := by rw [← hFF]; exact hx
  obtain ⟨n, hn⟩ := hxorb
  -- x = ff^[n%k] x0，且 x0 = ff^[k - n%k] x
  have hxn : ff^[n % (p12b_V V v).ncard] x0 = x := by
    rw [← hn, p12i_ff_iter_mod hcl hedge hv hw0 hcard3 n]
  have hk_pos : 0 < (p12b_V V v).ncard := by omega
  have hx0x : ff^[(p12b_V V v).ncard - n % (p12b_V V v).ncard] x = x0 := by
    rw [← hxn]
    have h1 : (p12b_V V v).ncard - n % (p12b_V V v).ncard
        + n % (p12b_V V v).ncard = (p12b_V V v).ncard :=
      Nat.sub_add_cancel (le_of_lt (Nat.mod_lt n hk_pos))
    calc ff^[(p12b_V V v).ncard - n % (p12b_V V v).ncard]
          (ff^[n % (p12b_V V v).ncard] x0)
        = ff^[(p12b_V V v).ncard - n % (p12b_V V v).ncard
            + n % (p12b_V V v).ncard] x0 :=
            (Function.iterate_add_apply _ _ _ _).symm
      _ = ff^[(p12b_V V v).ncard] x0 := by rw [h1]
      _ = x0 := hper
  ext y
  constructor
  · intro hy
    rw [hFF]
    obtain ⟨m, hm⟩ := hy
    exact ⟨m + n, by rw [Function.iterate_add_apply, hn]; exact hm⟩
  · intro hy
    rw [hFF] at hy
    obtain ⟨m, hm⟩ := hy
    refine ⟨m + ((p12b_V V v).ncard - n % (p12b_V V v).ncard), ?_⟩
    rw [Function.iterate_add_apply, hx0x]
    exact hm

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12i_ff_step_rev
#print axioms Kepler.Text.p12i_face_eq

end Kepler.Text
