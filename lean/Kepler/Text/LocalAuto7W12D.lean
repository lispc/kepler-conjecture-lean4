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


/-! ## r 的 cycle-splice：`orbitF r w0 = orbitF ρ w0 \ {v}` 与 `= V'` -/

/-- `r` 把 `V'` 送到 `V'`（迭代形）。 -/
private theorem p12d_R_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => simpa using hw0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p12b_R_mem hcl hedge hv ih

/-- r-轨道 ⊆ ρ-轨道（`r x = ρx` 或 `r x = ρ(ρx)`）。 -/
private theorem p12d_r_sub_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, ∃ m : ℕ,
      (rhoNode1 FF)^[m] w0 = (p12b_R FF v)^[n] w0 := by
  intro n
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    set x : V3 := (p12b_R FF v)^[k] w0 with hx
    rw [show (p12b_R FF v)^[k + 1] w0 = p12b_R FF v x from
      Function.iterate_succ_apply' (p12b_R FF v) k w0]
    by_cases hcase : rhoNode1 FF x = v
    · -- `r x = ρv = ρ(ρx)`：多走两步
      have hrx : p12b_R FF v x = rhoNode1 FF v := by
        show (if rhoNode1 FF x = v then rhoNode1 FF v else rhoNode1 FF x) = rhoNode1 FF v
        rw [if_pos hcase]
      rw [hrx]
      refine ⟨m + 2, ?_⟩
      have hsteps : (rhoNode1 FF)^[m + 2] w0 = rhoNode1 FF (rhoNode1 FF x) := by
        rw [show m + 2 = m + 1 + 1 by omega,
          Function.iterate_succ_apply' (rhoNode1 FF) (m + 1) w0,
          Function.iterate_succ_apply' (rhoNode1 FF) m w0, hm]
      rw [hsteps, hcase]
    · have hrx : p12b_R FF v x = rhoNode1 FF x := by
        show (if rhoNode1 FF x = v then rhoNode1 FF v else rhoNode1 FF x) = rhoNode1 FF x
        rw [if_neg hcase]
      rw [hrx]
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm]⟩

/-- ρ-轨道 ⊆ r-轨道 ∪ {v}：双子句归纳
（`ρ^n w0 ≠ v → r^[m] = ρ^n w0` / `ρ^n w0 = v → r^[m] = ρv`）。 -/
private theorem p12d_rho_sub_r {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ,
      (((rhoNode1 FF)^[n] w0 ≠ v →
          ∃ m : ℕ, (p12b_R FF v)^[m] w0 = (rhoNode1 FF)^[n] w0) ∧
        ((rhoNode1 FF)^[n] w0 = v →
          ∃ m : ℕ, (p12b_R FF v)^[m] w0 = rhoNode1 FF v)) := by
  intro n
  induction n with
  | zero => exact ⟨fun hne => ⟨0, rfl⟩, fun heq => absurd heq hw0.2⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set x : V3 := (rhoNode1 FF)^[k] w0 with hx
    have hstep : (rhoNode1 FF)^[k + 1] w0 = rhoNode1 FF x := by
      rw [Function.iterate_succ_apply']
    constructor
    · intro hne
      by_cases hcase : rhoNode1 FF x = v
      · exact absurd (by rw [hstep]; exact hcase) hne
      · by_cases hxv : x = v
        · obtain ⟨m, hm⟩ := ih2 hxv
          refine ⟨m, ?_⟩
          rw [hstep, hxv]
          exact hm
        · obtain ⟨m, hm⟩ := ih1 hxv
          have hrx : p12b_R FF v x = rhoNode1 FF x := by
            show (if rhoNode1 FF x = v then rhoNode1 FF v else rhoNode1 FF x) = rhoNode1 FF x
            rw [if_neg hcase]
          refine ⟨m + 1, ?_⟩
          show (p12b_R FF v)^[m + 1] w0 = (rhoNode1 FF)^[k + 1] w0
          rw [hstep, Function.iterate_succ_apply' (p12b_R FF v) m w0, hm, hrx]
    · intro heq
      have hcase : rhoNode1 FF x = v := by rw [← hstep]; exact heq
      by_cases hxv : x = v
      · exact ih2 hxv
      · obtain ⟨m, hm⟩ := ih1 hxv
        have hrx : p12b_R FF v x = rhoNode1 FF v := by
          show (if rhoNode1 FF x = v then rhoNode1 FF v else rhoNode1 FF x) = rhoNode1 FF v
          rw [if_pos hcase]
        refine ⟨m + 1, ?_⟩
        show (p12b_R FF v)^[m + 1] w0 = rhoNode1 FF v
        rw [Function.iterate_succ_apply' (p12b_R FF v) m w0, hm, hrx]

/-- **cycle-splice**：`orbitF r w0 = orbitF ρ w0 \ {v}`（`w0 ∈ V'`）。 -/
theorem p12d_orbit_splice {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    orbitF_p2 (p12b_R FF v) w0 = orbitF_p2 (rhoNode1 FF) w0 \ {v} := by
  ext y
  constructor
  · rintro ⟨n, hn⟩
    have hmemV : (p12b_R FF v)^[n] w0 ∈ p12b_V V v :=
      p12d_R_iter_mem hcl hedge hv hw0 n
    constructor
    · obtain ⟨m, hm⟩ := p12d_r_sub_rho hcl hedge hv hw0 n
      exact ⟨m, by rw [hm, hn]⟩
    · rw [Set.mem_singleton_iff]
      intro hyv
      exact hmemV.2 (by rw [hn, hyv]; exact Set.mem_singleton v)
  · rintro ⟨⟨n, hn⟩, hyv⟩
    have hne : (rhoNode1 FF)^[n] w0 ≠ v := by rw [hn]; exact hyv
    obtain ⟨m, hm⟩ := (p12d_rho_sub_r hcl hedge hv hw0 n).1 hne
    exact ⟨m, by rw [hm, hn]⟩

/-- `orbitF r w0 = V'`（配 `LOCAL_FAN_ORBIT_MAP_V`：`orbitF ρ w0 = V`）。 -/
theorem p12d_orbit_splice_V {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    orbitF_p2 (p12b_R FF v) w0 = p12b_V V v := by
  rw [p12d_orbit_splice hcl hedge hv hw0]
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hρ : orbitF_p2 (rhoNode1 FF) w0 = V := LOCAL_FAN_ORBIT_MAP_V h2 hw0.1
  rw [hρ]
  rfl

/-! ## `FF' = orbitF (ffOfHyp)` -/

/-- `ffOfHyp_p3 0 V' E'` 的迭代公式：`ff^[n] (w0, r w0) = (r^[n] w0, r^[n+1] w0)`。 -/
private theorem p12d_ff_iter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
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
      p12d_R_iter_mem hcl hedge hv hw0 k
    have hsucc : (p12b_R FF v)^[k + 1] w0
        = p12b_R FF v ((p12b_R FF v)^[k] w0) :=
      Function.iterate_succ_apply' (p12b_R FF v) k w0
    have hexp : (p12b_R FF v)^[k + 1 + 1] w0
        = p12b_R FF v (p12b_R FF v ((p12b_R FF v)^[k] w0)) := by
      rw [Function.iterate_succ_apply' (p12b_R FF v) (k + 1) w0, hsucc]
    rw [hsucc, hexp]
    exact p12d_ff_step hcl hedge hv hk

/-- **`FF' = orbitF_p3 (ffOfHyp_p3 0 V' E') (w0, r w0)`**：正向用
`p12d_orbit_splice_V` 把每个 `w` 写成 `r^[n] w0`，反向用迭代公式。 -/
theorem p12d_FF_orbit {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    p12b_FF V FF v = orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))
      (w0, p12b_R FF v w0) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hV : orbitF_p2 (p12b_R FF v) w0 = p12b_V V v :=
      p12d_orbit_splice_V hcl hedge hv hw0
    obtain ⟨n, hn⟩ : w ∈ orbitF_p2 (p12b_R FF v) w0 := by rw [hV]; exact hw
    refine ⟨n, ?_⟩
    rw [p12d_ff_iter hcl hedge hv hw0 n, Function.iterate_succ_apply', hn]
  · rintro ⟨n, hn⟩
    rw [p12d_ff_iter hcl hedge hv hw0 n, Function.iterate_succ_apply'] at hn
    exact ⟨(p12b_R FF v)^[n] w0, p12d_R_iter_mem hcl hedge hv hw0 n, hn.symm⟩

/-! ## `H.face` 桥（配 `exists_hypHyp_of_fan` 的第四分量，b2b-ii 直接消费） -/

/-- `H.face d = orbitF_p3 (ffOfHyp_p3 0 V' E') d`，只要 `H.faceMap` 与 `ffOfHyp` 同函数
（`exists_hypHyp_of_fan` 的 face 分量即是）。不碰 LA7 私件：`Hypermap.face = orbitMap` +
`Equiv.Perm.coe_pow`。 -/
theorem p12d_face_eq_orbit {V : Set V3} {FF : Set (V3 × V3)}
    {v : V3} {H : @Hypermap (V3 × V3) dartDecEq3}
    (hface : (H.faceMap : V3 × V3 → V3 × V3)
      = ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    ∀ d : V3 × V3, H.face d
      = orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) d := by
  intro d
  unfold Hypermap.face orbitMap orbitF_p3
  ext y
  simp only [Equiv.Perm.coe_pow, hface]

/-- **`FF' = H.face x`（`x ∈ H.darts`）**：b2b-ii 的 `localFan_p3` 第 6 分量。 -/
theorem p12d_face_orbit {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    {H : @Hypermap (V3 × V3) dartDecEq3}
    (hdarts : (↑H.darts : Set (V3 × V3))
      = dartsOfHyp_p3 (p12b_E V FF v) (p12b_V V v))
    (hface : (H.faceMap : V3 × V3 → V3 × V3)
      = ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) :
    ∃ x ∈ H.darts, p12b_FF V FF v = H.face x := by
  refine ⟨(w0, p12b_R FF v w0), ?_, ?_⟩
  · exact Finset.mem_coe.mp (by
      rw [hdarts]
      exact Set.mem_union_left _
        (show ({w0, p12b_R FF v w0} : Set V3) ∈ p12b_E V FF v from ⟨w0, hw0, rfl⟩))
  · rw [p12d_FF_orbit hcl hedge hv hw0, p12d_face_eq_orbit hface]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12d_hedge
#print axioms Kepler.Text.p12d_EE_eq
#print axioms Kepler.Text.p12d_ff_step
#print axioms Kepler.Text.p12d_orbit_splice
#print axioms Kepler.Text.p12d_orbit_splice_V
#print axioms Kepler.Text.p12d_FF_orbit
#print axioms Kepler.Text.p12d_face_eq_orbit
#print axioms Kepler.Text.p12d_face_orbit

end Kepler.Text
