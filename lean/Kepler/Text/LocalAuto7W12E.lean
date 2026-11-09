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


/-! ## 1b-i：`hcard3` 下的无 2-循环 / EE 两点 / 节点·边步进 -/

/-- `r^[n] w ∈ V'`（W12D 私件 `p12d_R_iter_mem` 的本地副本）。 -/
private theorem p12e_R_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => simpa using hw0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p12b_R_mem hcl hedge hv ih

/-- `r^[n]` 在 `V'` 上可消（单射的迭代）。 -/
private theorem p12e_R_iter_inj {V : Set V3} {FF : Set (V3 × V3)}
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
      (p12e_R_iter_mem hcl hedge hv ha k) (p12e_R_iter_mem hcl hedge hv hb k) h)

/-- `r (r w0) = w0` ⟹ 轨道 ⊆ `{w0, r w0}`（奇偶性）。 -/
private theorem p12e_orbit_two {FF : Set (V3 × V3)}
    {v w0 : V3} (h2 : p12b_R FF v (p12b_R FF v w0) = w0) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 = w0 ∨ (p12b_R FF v)^[n] w0 = p12b_R FF v w0 := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; exact h2)

/-- **无 2-循环**（`hcard3` 下）：`r (r w) ≠ w`。反证：`r²w = w` ⟹ 轨道 ⊆ `{w0, r w0}`
（ncard ≤ 2），与 `orbitF r w0 = V'` 的 `ncard ≥ 3` 冲突。 -/
theorem p12e_no2cycle {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ∀ w ∈ p12b_V V v, p12b_R FF v (p12b_R FF v w) ≠ w := by
  intro w hw h2
  have hV' : orbitF_p2 (p12b_R FF v) w0 = p12b_V V v :=
    p12d_orbit_splice_V hcl hedge hv hw0
  have hworb : w ∈ orbitF_p2 (p12b_R FF v) w0 := by rw [hV']; exact hw
  obtain ⟨n, hn⟩ := hworb
  -- `r² w = w` 传到 `w0`：`r^[n] (r (r w0)) = r^[n] w0` ⇒ `r² w0 = w0`
  have h2gen : ∀ x : V3, (p12b_R FF v)^[2] x
      = p12b_R FF v (p12b_R FF v x) := by
    intro x
    rw [show (2:ℕ) = 1 + 1 by omega, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    rfl
  have h2w0 : p12b_R FF v (p12b_R FF v w0) = w0 := by
    apply p12e_R_iter_inj hcl hedge hv n
      (p12b_R FF v (p12b_R FF v w0))
      (p12b_R_mem hcl hedge hv (p12b_R_mem hcl hedge hv hw0)) w0 hw0
    have hsplit : (p12b_R FF v)^[n + 2] w0
        = (p12b_R FF v)^[n] ((p12b_R FF v)^[2] w0) :=
      Function.iterate_add_apply (p12b_R FF v) n 2 w0
    have h3 : (p12b_R FF v)^[n + 2] w0
        = p12b_R FF v (p12b_R FF v ((p12b_R FF v)^[n] w0)) := by
      rw [show n + 2 = 2 + n by omega,
        Function.iterate_add_apply (p12b_R FF v) 2 n w0]
      exact h2gen ((p12b_R FF v)^[n] w0)
    have heq : (p12b_R FF v)^[n + 2] w0 = (p12b_R FF v)^[n] w0 := by
      rw [h3]
      rw [← hn] at h2
      exact h2
    rw [← h2gen w0, ← hsplit]
    exact heq
  -- 轨道 ⊆ {w0, r w0}
  have hsmall := p12e_orbit_two (v := v) h2w0
  have hsub : p12b_V V v ⊆ ({w0, p12b_R FF v w0} : Set V3) := by
    intro y hy
    rw [← hV'] at hy
    obtain ⟨m, hm⟩ := hy
    rcases hsmall m with h | h
    · rw [← hm, h]; exact Set.mem_insert _ _
    · rw [← hm, h]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hle : (p12b_V V v).ncard ≤ 2 := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : ({w0, p12b_R FF v w0} : Set V3).ncard ≤ 2 := by
      by_cases heq2 : w0 = p12b_R FF v w0
      · have hset : ({w0, p12b_R FF v w0} : Set V3) = {w0} := by
          rw [← heq2]
          exact Set.insert_eq_of_mem (Set.mem_singleton _)
        rw [hset, Set.ncard_singleton]
        norm_num
      · rw [Set.ncard_pair heq2]
    omega
  omega

/-- `EE_p3 w E' = {r w, pre w}`（两点集：复用 `p12d_EE_eq` 于 `pre w`）。 -/
theorem p12e_EE_w {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    EE_p3 w (p12b_E V FF v)
      = ({p12b_R FF v w, p12e_pre hcl hedge hv w} : Set V3) := by
  obtain ⟨hqV, hrq⟩ := p12e_pre_spec hcl hedge hv hw
  have h := p12d_EE_eq (w := p12e_pre hcl hedge hv w) hcl hedge hv hqV
  rw [hrq] at h
  rw [h, Set.pair_comm]

/-- 两点 EE 上 `azimCycle` 正向：`σ_w (r w) = pre w`。 -/
theorem p12e_azim_fwd {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    azimCycle_p3 (EE_p3 w (p12b_E V FF v)) (0:V3) w (p12b_R FF v w)
      = p12e_pre hcl hedge hv w := by
  rw [p12e_EE_w hcl hedge hv hw]
  exact AZIM_CYCLE_TWO_POINT_SET_ALT (x := (0:V3)) (u := w)
    (v := p12b_R FF v w) (w := p12e_pre hcl hedge hv w) rfl

/-- 两点 EE 上 `azimCycle` 反向：`σ_w (pre w) = r w`。 -/
theorem p12e_azim_back {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    azimCycle_p3 (EE_p3 w (p12b_E V FF v)) (0:V3) w (p12e_pre hcl hedge hv w)
      = p12b_R FF v w := by
  rw [p12e_EE_w hcl hedge hv hw]
  exact AZIM_CYCLE_TWO_POINT_SET_ALT (x := (0:V3)) (u := w)
    (v := p12e_pre hcl hedge hv w) (w := p12b_R FF v w) (Set.pair_comm _ _)

/-- 边映射单步：`eeOfHyp (w, r w) = (r w, w)`。 -/
theorem p12e_ee_step {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v : V3} {w : V3} (hw : w ∈ p12b_V V v) :
    eeOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) (w, p12b_R FF v w)
      = (p12b_R FF v w, w) := by
  have hdart : (w, p12b_R FF v w) ∈
      dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) :=
    Set.mem_union_left _
      (show ({w, p12b_R FF v w} : Set V3) ∈ p12b_E V FF v from ⟨w, hw, rfl⟩)
  unfold eeOfHyp_p3
  rw [if_pos hdart]

/-- 节点映射单步：`nnOfHyp (w, r w) = (w, pre w)`。 -/
theorem p12e_nn_fwd {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) (w, p12b_R FF v w)
      = (w, p12e_pre hcl hedge hv w) := by
  have hdart : (w, p12b_R FF v w) ∈
      dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) :=
    Set.mem_union_left _
      (show ({w, p12b_R FF v w} : Set V3) ∈ p12b_E V FF v from ⟨w, hw, rfl⟩)
  unfold nnOfHyp_p3
  rw [if_pos hdart, p12e_azim_fwd hcl hedge hv hw]

/-- 节点映射单步（回）：`nnOfHyp (w, pre w) = (w, r w)`。 -/
theorem p12e_nn_back {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    nnOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (w, p12e_pre hcl hedge hv w)
      = (w, p12b_R FF v w) := by
  obtain ⟨hqV, hrq⟩ := p12e_pre_spec hcl hedge hv hw
  have hdart : (w, p12e_pre hcl hedge hv w) ∈
      dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) :=
    Set.mem_union_left _
      (show ({w, p12e_pre hcl hedge hv w} : Set V3) ∈ p12b_E V FF v from
        ⟨p12e_pre hcl hedge hv w, hqV, by rw [hrq, Set.pair_comm]⟩)
  unfold nnOfHyp_p3
  rw [if_pos hdart, p12e_azim_back hcl hedge hv hw]

/-- **`FF' ∩ FF'rev = ∅`**（`FF'rev = {(r w, w) | w ∈ V'}`；由 `p12e_no2cycle`）。 -/
theorem p12e_FFrev_disj {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    p12b_FF V FF v ∩ {d : V3 × V3 | ∃ w ∈ p12b_V V v, d = (p12b_R FF v w, w)}
      = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbd⟩⟩ := hd
  have h1 : a = p12b_R FF v b := congrArg Prod.fst hbd
  have h2 : p12b_R FF v a = b := congrArg Prod.snd hbd
  exact p12e_no2cycle hcl hedge hv hw0 hcard3 b hb (by rw [← h1]; exact h2)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12e_R_surj
#print axioms Kepler.Text.p12e_pre_spec
#print axioms Kepler.Text.p12e_no2cycle
#print axioms Kepler.Text.p12e_EE_w
#print axioms Kepler.Text.p12e_azim_fwd
#print axioms Kepler.Text.p12e_azim_back
#print axioms Kepler.Text.p12e_ee_step
#print axioms Kepler.Text.p12e_nn_fwd
#print axioms Kepler.Text.p12e_nn_back
#print axioms Kepler.Text.p12e_FFrev_disj

end Kepler.Text
