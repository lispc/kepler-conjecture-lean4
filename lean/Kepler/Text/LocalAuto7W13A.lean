/-
LocalAuto7W13A: W13a — straight 支 `ConvexLocalFan V' E' FF'` 的分解基座（第一批）。

本文件只交 convex 半两合取**共用的分解件**（LA1 词汇，零 p2/p3 词汇桥）：

* `p13a_ivs_FF'`：`ivsRhoNode1 FF' w = pre w`（`FF'` 的前驱 = `pre`，`r` 在 `V'` 上单射）；
* `p13a_r_ne_pre`：`r w ≠ pre w`（否则 `r (r w) = w`，撞 `p12e_no2cycle`）；
* `p13a_EE_card`：`(ee w E').ncard = 2`；
* `p13a_azimInFan_FF'`：`azimInFan (w, r w) E' = azim 0 w (r w) (pre w)`。

convex 半本体（W13a-ii，路线见 DELIVERY）：
`azimInFan x E' ≤ π`（`IN_V_IMP_AZIM_LESS_PI` + `p13w_convexLocalFan_p2_of_clf` 桥）、
`V' ⊆ wedgeInFanGe x E'`（`WEDGE_IN_FAN_RHOND_IVS_RHOND` + 旧凸性 + `ρv = u` 两例拆分）、
`ConvexLocalFan` 装配（`p12p_LocalFan` + 两合取）。W12E–P、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12P

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- epsilon 唯一性坍塌（W12B 私件的本地副本）。 -/
private theorem p13a_epsilon_fixed {α : Type*} [Nonempty α] {p : α → Prop} {a : α}
    (hpa : p a) (huniq : ∀ y, p y → y = a) : Classical.epsilon p = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- `FF'` 的前驱就是 `pre w`：`ivsRhoNode1 FF' w = pre w`。 -/
theorem p13a_ivs_FF' {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v) :
    ivsRhoNode1 (p12b_FF V FF v) w = p12e_pre hcl hedge hv w := by
  unfold ivsRhoNode1
  refine p13a_epsilon_fixed ?_ ?_
  · exact ⟨p12e_pre hcl hedge hv w, (p12e_pre_spec hcl hedge hv hw).1,
      Prod.ext rfl (p12e_pre_spec hcl hedge hv hw).2.symm⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hy1 : y = z := congrArg Prod.fst hzy
    have hy2 : w = p12b_R FF v z := congrArg Prod.snd hzy
    have hrz : p12b_R FF v (p12e_pre hcl hedge hv w) = p12b_R FF v z := by
      rw [(p12e_pre_spec hcl hedge hv hw).2, hy2]
    have hpre_eq : p12e_pre hcl hedge hv w = z :=
      p12b_R_inj hcl hedge hv (p12e_pre_spec hcl hedge hv hw).1 hz hrz
    rw [hy1, ← hpre_eq]

/-- `r w ≠ pre w`（否则 `r (r w) = w`，与无 2-循环冲突）。 -/
theorem p13a_r_ne_pre {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) {w : V3} (hw : w ∈ p12b_V V v) :
    p12b_R FF v w ≠ p12e_pre hcl hedge hv w := by
  intro h
  have h2 : p12b_R FF v (p12b_R FF v w) = w := by
    rw [h]
    exact (p12e_pre_spec hcl hedge hv hw).2
  exact p12e_no2cycle hcl hedge hv hw0 hcard3 w hw h2

/-- `(ee w E').ncard = 2`（邻边集 = `{r w, pre w}` 两点）。 -/
theorem p13a_EE_card {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) {w : V3} (hw : w ∈ p12b_V V v) :
    (ee w (p12b_E V FF v)).ncard = 2 := by
  have hne := p13a_r_ne_pre hcl hedge hv hw0 hcard3 hw
  have hEE : ee w (p12b_E V FF v)
      = ({p12b_R FF v w, p12e_pre hcl hedge hv w} : Set V3) :=
    p12e_EE_w hcl hedge hv hw
  rw [hEE, Set.ncard_pair hne]

/-- **`azimInFan (w, r w) E' = azim 0 w (r w) (pre w)`**（`sigmaFan` 在两点邻边集上取 `pre`）。 -/
theorem p13a_azimInFan_FF' {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) {w : V3} (hw : w ∈ p12b_V V v) :
    azimInFan (w, p12b_R FF v w) (p12b_E V FF v)
      = azim 0 w (p12b_R FF v w) (p12e_pre hcl hedge hv w) := by
  have hne := p13a_r_ne_pre hcl hedge hv hw0 hcard3 hw
  have hcard := p13a_EE_card hcl hedge hv hw0 hcard3 hw
  have hset : setOfEdge w Set.univ (p12b_E V FF v)
      = ({p12b_R FF v w, p12e_pre hcl hedge hv w} : Set V3) := by
    rw [show setOfEdge w Set.univ (p12b_E V FF v) = ee w (p12b_E V FF v) from by
      ext z
      simp only [setOfEdge, ee, Set.mem_setOf_eq, Set.mem_univ, and_true]]
    exact p12e_EE_w hcl hedge hv hw
  have hnotsing : setOfEdge w Set.univ (p12b_E V FF v) ≠ {p12b_R FF v w} := by
    intro h
    have hmem : p12e_pre hcl hedge hv w ∈ setOfEdge w Set.univ (p12b_E V FF v) := by
      rw [hset]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [h] at hmem
    exact hne (Set.mem_singleton_iff.mp hmem).symm
  have hsig : sigmaFan 0 Set.univ (p12b_E V FF v) w (p12b_R FF v w)
      = p12e_pre hcl hedge hv w := by
    unfold sigmaFan
    rw [if_neg hnotsing]
    refine p13a_epsilon_fixed ?_ ?_
    · refine ⟨?_, hne.symm, ?_⟩
      · rw [hset]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · intro w1 hw1 hw1ne
        rw [hset, Set.mem_insert_iff, Set.mem_singleton_iff] at hw1
        rcases hw1 with h1 | h1
        · exact absurd h1 hw1ne
        · rw [h1]
    · intro y hy
      obtain ⟨hym, hyne, -⟩ := hy
      rw [hset, Set.mem_insert_iff, Set.mem_singleton_iff] at hym
      rcases hym with h1 | h1
      · exact absurd h1 hyne
      · exact h1
  unfold azimInFan
  rw [if_pos (by rw [hcard]; norm_num), hsig]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p13a_ivs_FF'
#print axioms Kepler.Text.p13a_r_ne_pre
#print axioms Kepler.Text.p13a_EE_card
#print axioms Kepler.Text.p13a_azimInFan_FF'

end Kepler.Text
