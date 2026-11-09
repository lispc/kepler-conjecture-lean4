/-
LocalAuto7W12M: W12(b2b-ii-b3b 尾) — `FF'rev` 侧轨道的基座件：

* `p12m_pre_rho`：`pre (r x) = x`（`pre` 是 `r` 在 `V'` 上的左逆）；
* `p12m_r_iter_mod`：`r^[n] w0 = r^[n % k] w0`（`k = V'.ncard`，`r^[k] w0 = w0`）。

`p12j_face_rev`（`x ∈ FF'rev ⇒ orbitF ff x = FF'rev`）还需三件：
`pre`-迭代左逆（`pre^[n] (r^[n] w) = w`）、`pre`-轨道覆盖（`∃ n, pre^[n] w0 = w`，
经 `r`-轨道 + mod 归约 + 左逆）、反向 `ff` 迭代（`ff^[n] (r w, w) = (r (pre^[n] w), pre^[n] w)`）——
规模另报。W12E–L、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12L

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `pre (r x) = x`（`pre` 是 `r` 在 `V'` 上的左逆）。 -/
theorem p12m_pre_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {x : V3} (hx : x ∈ p12b_V V v) :
    p12e_pre hcl hedge hv (p12b_R FF v x) = x := by
  have hrx : p12b_R FF v x ∈ p12b_V V v := p12b_R_mem hcl hedge hv hx
  exact p12b_R_inj hcl hedge hv (p12e_pre_spec hcl hedge hv hrx).1 hx
    (p12e_pre_spec hcl hedge hv hrx).2

/-- `r^[n] w0 = r^[n % k] w0`（`k = V'.ncard`）。 -/
theorem p12m_r_iter_mod {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) (n : ℕ) :
    (p12b_R FF v)^[n] w0 = (p12b_R FF v)^[n % (p12b_V V v).ncard] w0 := by
  obtain ⟨hper, -⟩ := p12g_period hcl hedge hv hw0
  have hk_pos : 0 < (p12b_V V v).ncard := by omega
  have hdq : ∀ q : ℕ, (p12b_R FF v)^[(p12b_V V v).ncard * q] w0 = w0 := by
    intro q
    induction q with
    | zero => simp
    | succ m ihm =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hper, ihm]
  have h1 : n = n % (p12b_V V v).ncard
      + (p12b_V V v).ncard * (n / (p12b_V V v).ncard) :=
    (Nat.mod_add_div n (p12b_V V v).ncard).symm
  calc (p12b_R FF v)^[n] w0
      = (p12b_R FF v)^[n % (p12b_V V v).ncard
          + (p12b_V V v).ncard * (n / (p12b_V V v).ncard)] w0 := by
        conv_lhs => rw [h1]
    _ = (p12b_R FF v)^[n % (p12b_V V v).ncard]
          ((p12b_R FF v)^[(p12b_V V v).ncard * (n / (p12b_V V v).ncard)] w0) :=
        Function.iterate_add_apply _ _ _ _
    _ = (p12b_R FF v)^[n % (p12b_V V v).ncard] w0 := by
        rw [hdq (n / (p12b_V V v).ncard)]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12m_pre_rho
#print axioms Kepler.Text.p12m_r_iter_mod

end Kepler.Text
