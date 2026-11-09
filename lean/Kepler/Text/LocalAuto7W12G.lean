/-
LocalAuto7W12G: W12(b2b-ii-b) — straight 支 `r` 周期的**钥匙件**：

`p12g_period`：`orbitF r w0 = V'`（`p12d_orbit_splice_V`）+ 基数 `k = V'.ncard`
⟹ `r^[k] w0 = w0` 且 `0 < i < k` 时 `r^[i] w0 ≠ w0`（前 k 个值互异且穷尽）。

后续（1b-ii-b2）：`face_eq_FF'`、face/edge/node 三条 `HasOrders`、`darts = S ∪ node''S`；
再后（1b-ii-c）：`dih2k_p3` 组装 + `localFan_p3` + `LocalFan.of_localFan_p3`。
LA7 / W12E / W12F 均零改动。
-/
import Kepler.Text.LocalAuto7W12F

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `r^[n] w ∈ V'`（W12E 私件的本地副本）。 -/
private theorem p12g_R_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => simpa using hw0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p12b_R_mem hcl hedge hv ih

/-- `r^[n]` 在 `V'` 上可消（W12E 私件的本地副本）。 -/
private theorem p12g_R_iter_inj {V : Set V3} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ n : ℕ, ∀ a ∈ p12b_V V v, ∀ b ∈ p12b_V V v,
      (p12b_R FF v)^[n] a = (p12b_R FF v)^[n] b → a = b := by
  intro n
  induction n with
  | zero =>
    intro a ha b hb h
    simpa using h
  | succ k ih =>
    intro a ha b hb h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
    exact ih a ha b hb (p12b_R_inj hcl hedge hv
      (p12g_R_iter_mem hcl hedge hv ha k) (p12g_R_iter_mem hcl hedge hv hb k) h)


/-- **`r` 的周期**（`k = V'.ncard`）：`r^[k] w0 = w0`，且 `k` 之前不回 `w0`。
证明：早返 `r^[d] w0 = w0`（`0<d<k`）⟹ 轨道 ⊆ 前 `d` 个值 ⟹ `ncard ≤ d < k` 矛盾；
再由"前 k 个值互异"+"都在 V'（ncard = k）"得穷尽，`r^[k] w0` 落在其中，
非零位移即早返矛盾。 -/
theorem p12g_period {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    (p12b_R FF v)^[(p12b_V V v).ncard] w0 = w0 ∧
      ∀ i : ℕ, 0 < i → i < (p12b_V V v).ncard → (p12b_R FF v)^[i] w0 ≠ w0 := by
  have hV' : orbitF_p2 (p12b_R FF v) w0 = p12b_V V v :=
    p12d_orbit_splice_V hcl hedge hv hw0
  have hfinV : (p12b_V V v).Finite := (p12b_card hcl hv).1
  -- (1) 早返不可能
  have hnoearly : ∀ d : ℕ, 0 < d → d < (p12b_V V v).ncard →
      (p12b_R FF v)^[d] w0 ≠ w0 := by
    intro d hd0 hdk hd
    have hdq : ∀ q : ℕ, (p12b_R FF v)^[d * q] w0 = w0 := by
      intro q
      induction q with
      | zero => simp
      | succ m ihm =>
        rw [Nat.mul_succ, Function.iterate_add_apply, hd, ihm]
    -- 轨道 ⊆ 前 d 个值
    have hsub : orbitF_p2 (p12b_R FF v) w0
        ⊆ ((fun t : ℕ => (p12b_R FF v)^[t] w0) '' {t : ℕ | t < d}) := by
      rintro y ⟨n, rfl⟩
      refine ⟨n % d, Nat.mod_lt n hd0, ?_⟩
      have h1 : n = n % d + d * (n / d) := (Nat.mod_add_div n d).symm
      calc (p12b_R FF v)^[n % d] w0
          = (p12b_R FF v)^[n % d] ((p12b_R FF v)^[d * (n / d)] w0) := by
            rw [hdq (n / d)]
        _ = (p12b_R FF v)^[n % d + d * (n / d)] w0 :=
            (Function.iterate_add_apply (p12b_R FF v) (n % d) (d * (n / d)) w0).symm
        _ = (p12b_R FF v)^[n] w0 := by
            conv_rhs => rw [h1]
    have hTcard : ((fun t : ℕ => (p12b_R FF v)^[t] w0) '' {t : ℕ | t < d}).ncard ≤ d := by
      have h1 := Set.ncard_image_le (s := {t : ℕ | t < d})
        (f := fun t : ℕ => (p12b_R FF v)^[t] w0)
      have h2 : ({t : ℕ | t < d}).ncard = d := by
        rw [show {t : ℕ | t < d} = (↑(Finset.range d) : Set ℕ) from by
          ext t; simp, Set.ncard_coe_finset, Finset.card_range]
      omega
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hV'] at hle
    omega
  -- (2) 前 k 个值互异
  have hdistinct : ∀ i j : ℕ, i < j → j < (p12b_V V v).ncard →
      (p12b_R FF v)^[i] w0 ≠ (p12b_R FF v)^[j] w0 := by
    intro i j hij hjk heq
    have hj : (p12b_R FF v)^[j] w0
        = (p12b_R FF v)^[i] ((p12b_R FF v)^[j - i] w0) := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt hij)]
    rw [hj] at heq
    have hc := p12g_R_iter_inj hcl hedge hv i w0 hw0
      ((p12b_R FF v)^[j - i] w0) (p12g_R_iter_mem hcl hedge hv hw0 (j - i)) heq
    exact hnoearly (j - i) (by omega) (by omega) hc.symm
  -- (3) 前 k 个值穷尽 V'
  have hcover : ((fun i : ℕ => (p12b_R FF v)^[i] w0) '' {i : ℕ | i < (p12b_V V v).ncard})
      = p12b_V V v := by
    have hinjOn : Set.InjOn (fun i : ℕ => (p12b_R FF v)^[i] w0)
        {i : ℕ | i < (p12b_V V v).ncard} := by
      intro i hi j hj h
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact absurd h (hdistinct i j hlt hj)
      · exact heq
      · exact absurd h.symm (hdistinct j i hgt hi)
    have himgcard : ((fun i : ℕ => (p12b_R FF v)^[i] w0)
        '' {i : ℕ | i < (p12b_V V v).ncard}).ncard = (p12b_V V v).ncard := by
      rw [hinjOn.ncard_image,
        show {i : ℕ | i < (p12b_V V v).ncard}
          = (↑(Finset.range (p12b_V V v).ncard) : Set ℕ) from by
          ext t; simp,
        Set.ncard_coe_finset, Finset.card_range]
    have hsubV : ((fun i : ℕ => (p12b_R FF v)^[i] w0)
        '' {i : ℕ | i < (p12b_V V v).ncard}) ⊆ p12b_V V v := by
      rintro _ ⟨i, -, rfl⟩
      exact p12g_R_iter_mem hcl hedge hv hw0 i
    refine Set.eq_of_subset_of_ncard_le hsubV ?_ hfinV
    rw [himgcard]
  -- (4) `r^[k] w0` 落在前 k 个里 ⇒ 非零位移即早返矛盾
  have hper : (p12b_R FF v)^[(p12b_V V v).ncard] w0 = w0 := by
    have hmem : (p12b_R FF v)^[(p12b_V V v).ncard] w0
        ∈ ((fun i : ℕ => (p12b_R FF v)^[i] w0) '' {i : ℕ | i < (p12b_V V v).ncard}) := by
      rw [hcover]
      exact p12g_R_iter_mem hcl hedge hv hw0 _
    obtain ⟨i, hi, hik⟩ := hmem
    by_cases hi0 : i = 0
    · rw [hi0] at hik
      exact hik.symm
    · exfalso
      have hk : (p12b_R FF v)^[(p12b_V V v).ncard] w0
          = (p12b_R FF v)^[i] ((p12b_R FF v)^[(p12b_V V v).ncard - i] w0) := by
        rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt hi)]
      rw [hk] at hik
      have hc := p12g_R_iter_inj hcl hedge hv i w0 hw0
        ((p12b_R FF v)^[(p12b_V V v).ncard - i] w0)
        (p12g_R_iter_mem hcl hedge hv hw0 _) hik
      have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have hk_pos : 0 < (p12b_V V v).ncard := lt_of_lt_of_le hi_pos (le_of_lt hi)
      exact hnoearly ((p12b_V V v).ncard - i)
        (Nat.sub_pos_of_lt hi) (by omega) hc.symm
  exact ⟨hper, hnoearly⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12g_period

end Kepler.Text
