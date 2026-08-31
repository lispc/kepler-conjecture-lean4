/-
Port of the HOL Light Flyspeck topology theory (Fan chapter).

Source: `reference/flyspeck/text_formalization/fan/topology.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (block 1, orbit counting & azim monotonicity, lines 1–~350):
- `CARD_SIGMA_FAN` (17): the σ-map preserves the cardinality of the
  edge set (image under an injective map).
- (further items appended per batch; see the coverage table below)

Coverage / skip table (updated per batch):
- 17 `CARD_SIGMA_FAN` ↦ `card_sigmaFan_image` (block 1).
- Mathlib-subsumed: `CARD_IMAGE_INJ` ↦ `Set.InjOn.ncard_image`.

Conventions: HOL line numbers in the head comment of each item; zero
`sorry`/`native_decide`/new axioms; `lake build Kepler` green before
each commit.
-/
import Kepler.Text.Fan
import Mathlib.Order.Interval.Set.Nat

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan

variable {x v u w : V3} {V : Set V3} {E : Set (Set V3)}

/-- HOL topology.hl:17 `CARD_SIGMA_FAN`：σ-像保持边集基数
（σ 在 setOfEdge 上单射）。 -/
theorem card_sigmaFan_image (hfan : FAN x V E) (v : V3) :
    ((sigmaFan x V E v) '' (setOfEdge v V E)).ncard = (setOfEdge v V E).ncard :=
  Set.InjOn.ncard_image (fun _ ha _ hb heq => mono_sigma_fan hfan ha hb heq)

/-- HOL topology.hl:35 `MONO_AZIM_SIGMA_FAN`：azim 单调性（基准 u 视角）。
证明重构：不走 HOL 的 cyclic_set 机制（约 800 行，未移植），改用
SIGMA_FAN 第三条件（基准 w）+ sum2_azim_fan 角加法 + azim_compl
补角换算；退化情形（u = w；σ 对径唯一）由 azim_self /
unique_azim0_point_fan 排除。 -/
theorem mono_azim_sigmaFan (hfan : FAN x V E) (hu : {v, u} ∈ E)
    (hw : {v, w} ∈ E) (hne : sigmaFan x V E v w ≠ u) :
    azim x v u w ≤ azim x v u (sigmaFan x V E v w) := by
  have hu1 : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hu
  have hw1 : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hw
  have hσedge : {v, sigmaFan x V E v w} ∈ E := by
    have hm := sigma_fan_in_setOfEdge hfan hw1
    simp only [setOfEdge, Set.mem_setOf_eq] at hm
    exact hm.1
  by_cases huw : u = w
  · rw [huw, azim_self]
    exact azim_nonneg _ _ _ _
  · have hne1 : setOfEdge v V E ≠ {w} := fun h =>
      huw (Set.mem_singleton_iff.mp (h ▸ hu1))
    obtain ⟨-, -, hσ3⟩ := SIGMA_FAN hne1 hfan hw1
    have hσ3u : azim x v w (sigmaFan x V E v w) ≤ azim x v w u := hσ3 u hu1 huw
    have hsum : azim x v w u =
        azim x v w (sigmaFan x V E v w) + azim x v (sigmaFan x V E v w) u :=
      sum2_azim_fan hfan hw hσedge hu hσ3u
    have hσu_ne : azim x v (sigmaFan x V E v w) u ≠ 0 := fun h0 =>
      hne (unique_azim0_point_fan hfan hσedge hu h0)
    have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hu
    have hncw : ¬ Collinear3 x v w := fan_not_collinear hfan hw
    have hncσ : ¬ Collinear3 x v (sigmaFan x V E v w) := fan_not_collinear hfan hσedge
    rw [azim_compl hncw hncu, azim_compl hncσ hncu, if_neg hσu_ne]
    by_cases hA : azim x v w u = 0
    · rw [if_pos hA]
      linarith [azim_lt_two_pi x v (sigmaFan x V E v w) u]
    · rw [if_neg hA]
      linarith [azim_nonneg x v w (sigmaFan x V E v w)]

/-! ## 仿射补集与 if_azims（topology.hl:239–285） -/

/-- HOL topology.hl:239 `complement_set`（HOL `aff` ↔ Mathlib
`affineSpan ℝ`）。 -/
def complementSet (x v : V3) : Set V3 :=
  {y | y ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3)}

/-- HOL topology.hl:241 `subset_aff`。 -/
theorem subset_aff (x v : V3) :
    (affineSpan ℝ ({x, v} : Set V3) : Set V3) ⊆ (Set.univ : Set V3) :=
  Set.subset_univ _

/-- HOL topology.hl:243 `union_aff`。 -/
theorem union_aff (x v : V3) :
    (Set.univ : Set V3) =
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∪ complementSet x v :=
  (Set.eq_univ_of_forall (fun y => by
    by_cases h : y ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3)
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h)).symm

/-- HOL topology.hl:256 `if_azims_fan`（HOL `CARD` ↔ ncard；FAN 下
setOfEdge 有限，语义一致；σ-迭代 ↔ power_map_points）。 -/
noncomputable def ifAzimsFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) : ℝ :=
  if i = (setOfEdge v V E).ncard then 2 * Real.pi
    else azim x v u ((sigmaFan x V E v)^[i] u)

/-- HOL topology.hl:265 `if_azims_works_fan`：if_azims 值域 [0, 2π]。 -/
theorem ifAzimsFan_mem (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3) (i : ℕ) :
    0 ≤ ifAzimsFan x V E v u i ∧ ifAzimsFan x V E v u i ≤ 2 * Real.pi := by
  unfold ifAzimsFan
  by_cases h : i = (setOfEdge v V E).ncard
  · rw [if_pos h]
    exact ⟨by positivity, le_refl _⟩
  · rw [if_neg h]
    exact ⟨azim_nonneg x v u _, le_of_lt (azim_lt_two_pi x v u _)⟩

/-- HOL topology.hl:275 `set_of_orbits_points_fan`（σ-轨道集）。 -/
def setOfOrbitsPointsFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3) : Set V3 :=
  {y | ∃ i : ℕ, (sigmaFan x V E v)^[i] u = y}

/-- HOL topology.hl:277 `number_of_orbits_points_fan`。 -/
noncomputable def numberOfOrbitsFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : ℕ :=
  (setOfOrbitsPointsFan x V E v u).ncard

/-- HOL topology.hl:280 `addition_sigma_fan`（iterate 加法，Mathlib 原生
`Function.iterate_add_apply`）。 -/
theorem addition_sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (m n : ℕ) :
    (sigmaFan x V E v)^[m + n] u = (sigmaFan x V E v)^[m] ((sigmaFan x V E v)^[n] u) :=
  Function.iterate_add_apply _ m n u

/-- HOL fan.hl（`image_power_map_points` 角色）：σ-迭代保持
`setOfEdge v` 成员性。 -/
theorem image_power_map_points (hfan : FAN x V E) (hvu : {v, u} ∈ E) (i : ℕ) :
    (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E := by
  induction i with
  | zero => exact (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  | succ i ih =>
    rw [Function.iterate_succ']
    exact sigma_fan_in_setOfEdge hfan ih

/-! ## 轨道基本性质（topology.hl:295–360） -/

/-- HOL topology.hl:295 `fix_point_sigma_fan`：轨道回到 u 则周期倍数
亦回。 -/
theorem fix_point_sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (q i : ℕ) (h : (sigmaFan x V E v)^[i] u = u) :
    (sigmaFan x V E v)^[q * i] u = u := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, Function.iterate_add_apply, h, ih]

/-- HOL topology.hl:305 `i_IN_ORBITS_FAN`。 -/
theorem iterates_mem_orbits (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) :
    (sigmaFan x V E v)^[i] u ∈ setOfOrbitsPointsFan x V E v u :=
  ⟨i, rfl⟩

/-- HOL topology.hl:309 `u_IN_ORBITS_FAN`。 -/
theorem mem_orbits_self (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3) :
    u ∈ setOfOrbitsPointsFan x V E v u :=
  ⟨0, rfl⟩

/-- HOL topology.hl:314 `IN_ORBITS_FAN`：轨道对 σ 封闭。 -/
theorem sigma_mem_orbits (x : V3) (V : Set V3) (E : Set (Set V3)) (v u w : V3)
    (hw : w ∈ setOfOrbitsPointsFan x V E v u) :
    sigmaFan x V E v w ∈ setOfOrbitsPointsFan x V E v u := by
  obtain ⟨i, hi⟩ := hw
  refine ⟨i + 1, ?_⟩
  rw [Function.iterate_succ_apply', hi]

/-- HOL topology.hl:321 `ORBITS_SUBSET_EDGE_FAN`：轨道 ⊆ setOfEdge。 -/
theorem orbits_subset_setOfEdge (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    setOfOrbitsPointsFan x V E v u ⊆ setOfEdge v V E := by
  intro w hw
  obtain ⟨i, hi⟩ := hw
  have h := image_power_map_points hfan hvu i
  rwa [hi] at h

/-- HOL topology.hl:331 `CARD_ORBITS_EDGE_FAN_LE`。 -/
theorem card_orbits_le_setOfEdge (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (setOfOrbitsPointsFan x V E v u).ncard ≤ (setOfEdge v V E).ncard :=
  Set.ncard_le_ncard (orbits_subset_setOfEdge hfan hvu)
    (remark_finite_fan1 v V E hfan.2.2.1.1)

/-- HOL topology.hl:346 `FINITE_ORBITS_SIGMA_FAN`。 -/
theorem finite_orbits_sigmaFan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (setOfOrbitsPointsFan x V E v u).Finite :=
  (remark_finite_fan1 v V E hfan.2.2.1.1).subset
    (orbits_subset_setOfEdge hfan hvu)

/-- HOL topology.hl:360 `ORBITS_SIGMA_FAN`：轨道回到 u（周期 i）时，
轨道 = 前 i 步截段。 -/
theorem orbits_eq_series (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) (h : (sigmaFan x V E v)^[i] u = u) (hi : i ≠ 0) :
    setOfOrbitsPointsFan x V E v u =
      {y | ∃ j : ℕ, j < i ∧ (sigmaFan x V E v)^[j] u = y} := by
  ext y
  constructor
  · rintro ⟨i', hi'⟩
    have h2 : i' % i + i * (i' / i) = i' := Nat.mod_add_div i' i
    have hlt : i' % i < i := Nat.mod_lt _ (Nat.pos_of_ne_zero hi)
    have hfm : (sigmaFan x V E v)^[i' / i * i] u = u :=
      fix_point_sigmaFan x V E v u _ i h
    have key : (sigmaFan x V E v)^[i' % i + i * (i' / i)] u =
        (sigmaFan x V E v)^[i' % i] u := by
      rw [Function.iterate_add_apply, Nat.mul_comm i (i' / i), hfm]
    refine ⟨i' % i, hlt, ?_⟩
    rw [← h2] at hi'
    rw [← key]
    exact hi'
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj⟩

/-- HOL topology.hl:423 `CARD_ORBITS_SIGMA_FAN_LE`：周期轨道基数
≤ 周期。 -/
theorem card_orbits_le_period (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) (i : ℕ) (h : (sigmaFan x V E v)^[i] u = u) (hi : i ≠ 0) :
    (setOfOrbitsPointsFan x V E v u).ncard ≤ i := by
  have himg : setOfOrbitsPointsFan x V E v u
      = (fun j : ℕ => (sigmaFan x V E v)^[j] u) '' (Set.Iio i) := by
    rw [orbits_eq_series x V E v u i h hi]
    ext y
    simp [Set.mem_image, Set.mem_Iio]
  rw [himg]
  calc ((fun j : ℕ => (sigmaFan x V E v)^[j] u) '' (Set.Iio i)).ncard
      ≤ (Set.Iio i).ncard := Set.ncard_image_le
    _ = i := Set.ncard_Iio_nat i

/-- HOL fan.hl:503 `azim1`：反向方位角（`2π - azim`）。 -/
noncomputable def azim1 (x v u w : V3) : ℝ :=
  2 * Real.pi - azim x v u w

/-- HOL topology.hl:427 `exists_inverse_in_orbits_sigma_fan`：轨道上
azim1-最小元存在（y ∉ 轨道；有限非空集取最小）。 -/
theorem exists_inverse_in_orbits (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (y : V3) (hy : y ∉ setOfOrbitsPointsFan x V E v u) :
    ∃ w ∈ setOfOrbitsPointsFan x V E v u, w ≠ y ∧
      ∀ w1 ∈ setOfOrbitsPointsFan x V E v u, w1 ≠ y →
        azim1 x v y w ≤ azim1 x v y w1 := by
  have hfin := finite_orbits_sigmaFan hfan hvu
  have hne : (setOfOrbitsPointsFan x V E v u).Nonempty :=
    ⟨u, mem_orbits_self x V E v u⟩
  obtain ⟨w, hw, hmin⟩ :=
    Set.exists_min_image (setOfOrbitsPointsFan x V E v u) (azim1 x v y) hfin hne
  exact ⟨w, hw, fun hwy => hy (hwy ▸ hw), fun w1 hw1 _ => hmin w1 hw1⟩

end Kepler.Text
