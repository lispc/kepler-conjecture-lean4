/-
LocalAuto7W12D: W12(b2b-i) 前半 — straight 支新扇的**邻边集两点集**与 **ff 单步**：
`EE_p3 (r w) E' = {w, r (r w)}` 与 `ffOfHyp_p3 0 V' E' (w, r w) = (r w, r (r w))`。
（b2b-i 后半：`FF' = face orbit` 需要 r 的 cycle-splice 归纳与 orbit 双向包含，
规模另报；本文件先交其中**安全、可独立审计**的件 + `hedge'`。）

契约：本文件只出 b2b 的**部件**，不改 `ConvexLocalFan` 目标形；LA7 零改动。

件表：
* `p12d_hedge`：`∀ w ∈ V', ∃ z, {w, z} ∈ E'`（z := r w；供 b2b-ii 的 `hno_of_no_isolated`）；
* `p12d_ivsTwo_p3` / `p12d_ivsSing_p3`（私）：公开 p7 件的 p3 逐字转写
  （`IVS_AZIM_CYCLE_TWO_POINT_SET` / `IVS_AZIM_CYCLE_SING`，p7/p3 同体）；
* **`p12d_EE_eq`**：`EE_p3 (r w) E' = {w, r (r w)}`（风险②：p3/plain + image 词形）；
* **`p12d_ff_step`**：`ffOfHyp_p3 0 V' E' (w, r w) = (r w, r (r w))`（退化支 `w = r (r w)`
  走单点 ivs）。
-/
import Kepler.Text.LocalAuto7W12C

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 邻边存在性（b2b-ii 的 hno 前提） -/

/-- `∀ w ∈ V', ∃ z, {w, z} ∈ E'`（取 `z := r w`）。 -/
theorem p12d_hedge {V : Set V3} {FF : Set (V3 × V3)} (v : V3) :
    ∀ w ∈ p12b_V V v, ∃ z, {w, z} ∈ p12b_E V FF v :=
  fun w hw => ⟨p12b_R FF v w, w, hw, rfl⟩

/-! ## p7 → p3 的 ivs 逐字转写（p7/p3 定义同体） -/

/-- `ivsAzimCycle_p3 {a,b} v0 c a = b`（公开 p7 件 `IVS_AZIM_CYCLE_TWO_POINT_SET`
的 p3 转写；`a = b` 时由下面的单点件兜底）。 -/
private theorem p12d_ivsTwo_p3 (a b v0 c : V3) :
    ivsAzimCycle_p3 ({a, b} : Set V3) v0 c a = b :=
  IVS_AZIM_CYCLE_TWO_POINT_SET a b v0 c

/-- `ivsAzimCycle_p3 {v} x u v = v`（公开 `IVS_AZIM_CYCLE_SING` 的 p3 转写）。 -/
private theorem p12d_ivsSing_p3 (x u v : V3) :
    ivsAzimCycle_p3 ({v} : Set V3) x u v = v :=
  IVS_AZIM_CYCLE_SING x u v

/-! ## `EE_p3 (r w) E' = {w, r (r w)}`（风险②） -/

/-- 新扇在 `r w` 处的邻边集恰为 `{w, r (r w)}`。两条来路：
`{r w, a} = {z, r z}` 分解为 `z = r w`（得 `a = r (r w)`）或 `r z = r w`（`r` 在 `V'` 上
单射 ⇒ `z = w`，得 `a = w`）。 -/
theorem p12d_EE_eq {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ p12b_V V v) :
    EE_p3 (p12b_R FF v w) (p12b_E V FF v)
      = ({w, p12b_R FF v (p12b_R FF v w)} : Set V3) := by
  have hrw : p12b_R FF v w ∈ p12b_V V v := p12b_R_mem hcl hedge hv hw
  have hrrw : p12b_R FF v (p12b_R FF v w) ∈ p12b_V V v := p12b_R_mem hcl hedge hv hrw
  ext a
  simp only [EE_p3, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ha
    -- `{r w, a} ∈ E'` 分解为 `{r w, a} = {z, r z}`
    obtain ⟨z, hz, hze⟩ := ha
    have hrw_mem : p12b_R FF v w ∈ ({z, p12b_R FF v z} : Set V3) :=
      hze ▸ (Set.mem_insert _ _)
    have ha_mem : a ∈ ({z, p12b_R FF v z} : Set V3) :=
      hze ▸ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hrw_mem ha_mem
    -- `a = r w` 不可能：否则边退化为单点集，与 `r z ≠ z` 矛盾
    have hcontr : a ≠ p12b_R FF v w := by
      intro haeq
      have hsingle : ({z, p12b_R FF v z} : Set V3) = {p12b_R FF v w} := by
        rw [← hze, haeq]
        simp
      have hzmem : z ∈ ({p12b_R FF v w} : Set V3) := hsingle ▸ Set.mem_insert _ _
      have hrzmem : p12b_R FF v z ∈ ({p12b_R FF v w} : Set V3) :=
        hsingle ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
      rw [Set.mem_singleton_iff] at hzmem hrzmem
      exact p12b_R_ne hcl hedge hv hz (by rw [hrzmem, hzmem])
    rcases hrw_mem with h1 | h1
    · rcases ha_mem with h2 | h2
      · exact absurd (h2.trans h1.symm) hcontr
      · exact Or.inr (by rw [h2, ← h1])
    · rcases ha_mem with h2 | h2
      · have hzw : z = w := p12b_R_inj hcl hedge hv hz hw h1.symm
        exact Or.inl (by rw [h2, hzw])
      · exact absurd (h2.trans h1.symm) hcontr
  · rintro (h | h)
    · -- `w ∈ EE (r w)`：边 `{r w, w} = {w, r w}`
      rw [h]
      exact ⟨w, hw, by rw [Set.pair_comm]⟩
    · -- `r (r w) ∈ EE (r w)`：边 `{r w, r (r w)}`
      rw [h]
      exact ⟨p12b_R FF v w, hrw, rfl⟩

/-! ## `ffOfHyp_p3` 的单步公式 -/

/-- `ffOfHyp_p3 0 V' E' (w, r w) = (r w, r (r w))`（退化支 `w = r (r w)` 时
`EE = {w}` 为单点集，走 `p12d_ivsSing_p3`）。 -/
theorem p12d_ff_step {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w : V3} (hv : v ∈ V) (hw : w ∈ p12b_V V v) :
    ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)
        (w, p12b_R FF v w)
      = (p12b_R FF v w, p12b_R FF v (p12b_R FF v w)) := by
  have hrw : p12b_R FF v w ∈ p12b_V V v := p12b_R_mem hcl hedge hv hw
  have hdart : (w, p12b_R FF v w) ∈
      dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v) :=
    Set.mem_union_left _ (show ({w, p12b_R FF v w} : Set V3) ∈ p12b_E V FF v from
      ⟨w, hw, rfl⟩)
  have hEE := p12d_EE_eq hcl hedge hv hw
  unfold ffOfHyp_p3
  rw [if_pos hdart, hEE]
  by_cases hdeg : w = p12b_R FF v (p12b_R FF v w)
  · -- 退化：`{w, r(r w)} = {w}`，ivs 单点件
    have hset : ({w, p12b_R FF v (p12b_R FF v w)} : Set V3) = {w} := by
      rw [← hdeg]
      exact Set.insert_eq_of_mem (Set.mem_singleton _)
    rw [hset, p12d_ivsSing_p3]
    exact Prod.ext rfl hdeg
  · rw [p12d_ivsTwo_p3 w (p12b_R FF v (p12b_R FF v w)) 0 (p12b_R FF v w)]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12d_hedge
#print axioms Kepler.Text.p12d_EE_eq
#print axioms Kepler.Text.p12d_ff_step

end Kepler.Text
