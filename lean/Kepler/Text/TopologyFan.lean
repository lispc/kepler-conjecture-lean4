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

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex

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

/-! ## 单循环性（topology.hl:490–700 重构：key_lemma_cyclic_fan 基础） -/

/-- σ 的迭代保持 setOfEdge 成员。 -/
theorem iterates_mem_setOfEdge (hfan : FAN x V E) (v w : V3)
    (hw : w ∈ setOfEdge v V E) (m : ℕ) :
    (sigmaFan x V E v)^[m] w ∈ setOfEdge v V E := by
  induction m with
  | zero => exact hw
  | succ m ih =>
    rw [Function.iterate_succ']
    exact sigma_fan_in_setOfEdge hfan ih

/-- σ 的迭代在 setOfEdge 上单射。 -/
theorem iterates_injOn_setOfEdge (hfan : FAN x V E) (v : V3) (m : ℕ) :
    Set.InjOn (sigmaFan x V E v)^[m] (setOfEdge v V E) := by
  induction m with
  | zero => intro x _ y _ h; simpa using h
  | succ m ih =>
    intro x hx y hy heq
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
    refine ih hx hy (mono_sigma_fan hfan (iterates_mem_setOfEdge hfan v x hx m)
      (iterates_mem_setOfEdge hfan v y hy m) heq)

/-- HOL topology.hl:490 区域（`key_lemma_cyclic_fan` 的重构基础）：
**σ-轨道 = setOfEdge**（单循环性）。重构证明：反设 a ∈ soe \ orbit。
(a) 轨道在 σ 下不变（封闭 + ncard + 单射 ⟹ 满），故 σ-迭代永不回 u；
(b) 于是 mono_azim_sigmaFan 沿迭代链严格递增（等号情形由
unique_azim_point_fan + SIGMA_FAN 第二条件排除）；
(c) soe 有限迫使迭代序列重复，与严格递增矛盾。 -/
theorem orbit_eq_setOfEdge (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    setOfOrbitsPointsFan x V E v u = setOfEdge v V E := by
  refine Set.Subset.antisymm (orbits_subset_setOfEdge hfan hvu) ?_
  intro a ha_soe
  by_contra ha_not
  have h_a_soe : a ∈ setOfEdge v V E := ha_soe
  have h_a_edge : {v, a} ∈ E := (properties_of_setOfEdge_fan x V E v a hfan).mpr ha_soe
  have hu_soe : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  -- (a) σ(orbit) = orbit
  have hcl : (sigmaFan x V E v) '' setOfOrbitsPointsFan x V E v u ⊆
      setOfOrbitsPointsFan x V E v u := by
    rintro w ⟨b, hb, rfl⟩
    exact sigma_mem_orbits x V E v u b hb
  have hinj_o : Set.InjOn (sigmaFan x V E v) (setOfOrbitsPointsFan x V E v u) :=
    fun b hb c hc heq => mono_sigma_fan hfan
      (orbits_subset_setOfEdge hfan hvu hb) (orbits_subset_setOfEdge hfan hvu hc) heq
  have hncard : ((sigmaFan x V E v) '' setOfOrbitsPointsFan x V E v u).ncard =
      (setOfOrbitsPointsFan x V E v u).ncard := Set.InjOn.ncard_image hinj_o
  have hfin := finite_orbits_sigmaFan hfan hvu
  have himg_eq : (sigmaFan x V E v) '' setOfOrbitsPointsFan x V E v u =
      setOfOrbitsPointsFan x V E v u := by
    by_contra hne2
    have hss := Set.ncard_lt_ncard (lt_of_le_of_ne hcl hne2) hfin
    rw [hncard] at hss
    omega
  -- σ^k a ∉ orbit ∀k（归纳：σ(orbit) = orbit ⟹ σ⁻¹(orbit) = orbit）
  have hnot_orbit : ∀ k : ℕ, (sigmaFan x V E v)^[k] a ∉
      setOfOrbitsPointsFan x V E v u := by
    intro k
    induction k with
    | zero => exact ha_not
    | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply'] at hk
      have hmem : (sigmaFan x V E v) ((sigmaFan x V E v)^[k] a) ∈
          (sigmaFan x V E v) '' setOfOrbitsPointsFan x V E v u := by
        rw [himg_eq]; exact hk
      obtain ⟨b, hb, hb_eq⟩ := hmem
      have hkey : b = (sigmaFan x V E v)^[k] a :=
        mono_sigma_fan hfan (orbits_subset_setOfEdge hfan hvu hb)
          (iterates_mem_setOfEdge hfan v a ha_soe k) hb_eq
      exact ih (by rw [← hkey]; exact hb)
  have hnot_u : ∀ k : ℕ, (sigmaFan x V E v)^[k] a ≠ u := by
    intro k he
    apply hnot_orbit k
    rw [he]
    exact mem_orbits_self x V E v u
  -- (b) 严格递增链
  have hstrict : ∀ k : ℕ,
      azim x v u ((sigmaFan x V E v)^[k] a) <
        azim x v u ((sigmaFan x V E v)^[k + 1] a) := by
    intro k
    have h1 : (sigmaFan x V E v)^[k] a ∈ setOfEdge v V E :=
      iterates_mem_setOfEdge hfan v a ha_soe k
    have h2 : (sigmaFan x V E v)^[k + 1] a ∈ setOfEdge v V E :=
      iterates_mem_setOfEdge hfan v a ha_soe (k + 1)
    have h1e : {v, (sigmaFan x V E v)^[k] a} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr h1
    have h2e : {v, (sigmaFan x V E v)^[k + 1] a} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr h2
    have hne1 : sigmaFan x V E v ((sigmaFan x V E v)^[k] a) ≠ u := fun he =>
      hnot_u (k + 1) (by rwa [Function.iterate_succ_apply'])
    have hle := mono_azim_sigmaFan hfan hvu h1e hne1
    by_contra hge
    push_neg at hge
    rw [Function.iterate_succ_apply'] at hge
    have heq := le_antisymm hge hle
    have heq' : azim x v u ((sigmaFan x V E v)^[k] a) =
        azim x v u ((sigmaFan x V E v)^[k + 1] a) := by
      rw [Function.iterate_succ_apply']; exact heq.symm
    have hpt := unique_azim_point_fan hfan hvu h1e h2e heq'
    rw [Function.iterate_succ_apply'] at hpt
    have hne_soe : setOfEdge v V E ≠ {(sigmaFan x V E v)^[k] a} := by
      intro h
      rw [h] at hu_soe
      exact hnot_u k (Set.mem_singleton_iff.mp hu_soe).symm
    exact (SIGMA_FAN hne_soe hfan h1).2.1 hpt.symm
  -- 严格链的传递
  have hchain : ∀ i j : ℕ, i < j →
      azim x v u ((sigmaFan x V E v)^[i] a) <
        azim x v u ((sigmaFan x V E v)^[j] a) := by
    intro i j hij
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero i)
    | succ j ihj =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ihj h) (hstrict j)
      · exact h ▸ hstrict j
  -- (c) soe 有限 ⟹ 迭代序列必有重复 ⟹ 与严格链矛盾
  have hfin_a : (setOfOrbitsPointsFan x V E v a).Finite :=
    finite_orbits_sigmaFan hfan h_a_edge
  have hrep : ∃ i j : ℕ, i < j ∧
      (sigmaFan x V E v)^[i] a = (sigmaFan x V E v)^[j] a := by
    by_contra hno
    push_neg at hno
    have hinj_seq : Function.Injective fun k : ℕ => (sigmaFan x V E v)^[k] a := by
      intro i j hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (hno i j h)
      · exact h
      · exact absurd hij.symm (hno j i h)
    have hinf : (Set.range fun k : ℕ => (sigmaFan x V E v)^[k] a).Infinite :=
      (Set.infinite_range_iff hinj_seq).mpr (by infer_instance)
    have hreq : (Set.range fun k : ℕ => (sigmaFan x V E v)^[k] a) =
        setOfOrbitsPointsFan x V E v a := rfl
    exact hinf.not_finite (by rw [hreq]; exact hfin_a)
  obtain ⟨i, j, hij, heq⟩ := hrep
  have hfinal := hchain i j hij
  rw [← heq] at hfinal
  exact lt_irrefl _ hfinal

/-- HOL topology.hl:656 `CARD_SET_OF_ORBITS_POINTS_FAN`：轨道基数 =
边集基数（σ 单循环的核心结论）。 -/
theorem card_orbits_eq_setOfEdge (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (setOfOrbitsPointsFan x V E v u).ncard = (setOfEdge v V E).ncard := by
  rw [orbit_eq_setOfEdge hfan hvu]

/-- HOL topology.hl:490 `key_lemma_cyclic_fan`：`0 < i < CARD(soe)` ⟹
σ 的第 i 次迭代不回原点（周期 = 全循环长）。 -/
theorem key_lemma_cyclic (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) {v u : V3} (hvu : {v, u} ∈ E)
    (i : ℕ) (hi : 0 < i) (hin : i < (setOfEdge v V E).ncard) :
    (sigmaFan x V E v)^[i] u ≠ u := by
  intro h0
  have hcard := card_orbits_le_period x V E v u i h0 (Nat.ne_of_gt hi)
  rw [orbit_eq_setOfEdge hfan hvu] at hcard
  omega

/-- HOL topology.hl:620 `cyclic_power_sigma_fan`：`j < i < CARD(soe)` ⟹
前 i 次迭代两两不同。 -/
theorem cyclic_power_sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) {v u : V3} (hvu : {v, u} ∈ E)
    (i j : ℕ) (hin : i < (setOfEdge v V E).ncard) (hij : j < i) :
    (sigmaFan x V E v)^[i] u ≠ (sigmaFan x V E v)^[j] u := by
  intro heq
  have hu_soe : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hstep : (sigmaFan x V E v)^[j] ((sigmaFan x V E v)^[i - j] u)
      = (sigmaFan x V E v)^[j] u := by
    have hadd : j + (i - j) = i := by omega
    rw [← Function.iterate_add_apply, hadd]
    exact heq
  have hfix : (sigmaFan x V E v)^[i - j] u = u :=
    iterates_injOn_setOfEdge hfan v j
      (iterates_mem_setOfEdge hfan v u hu_soe (i - j)) hu_soe hstep
  exact key_lemma_cyclic x V E hfan hvu (i - j) (by omega) (by omega) hfix

/-- HOL topology.hl:701 `ORDER_POWER_SIGMA_FAN`：σ 的第 n = CARD(soe)
次迭代回原点（全循环闭合）。证明重构：前 n 个迭代两两不同
（cyclic_power_sigmaFan）⟹ 截段像集是 soe 的 n 元子集 ⟹ 相等；
σ^[n]u ∈ soe = 截段 ⟹ 有重复 ⟹ 更短周期，与 key_lemma 矛盾。 -/
theorem order_power_sigmaFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) {v u : V3} (hvu : {v, u} ∈ E)
    (hn : n = (setOfEdge v V E).ncard) :
    (sigmaFan x V E v)^[n] u = u := by
  have hu_soe : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  -- 前 n 个迭代像集 ⊆ soe 且基数 n
  have hseg : (fun k : ℕ => (sigmaFan x V E v)^[k] u) '' (Set.Iio n)
      ⊆ setOfEdge v V E := by
    rintro w ⟨k, _, rfl⟩
    exact iterates_mem_setOfEdge hfan v u hu_soe k
  have hinj_seg : Set.InjOn (fun k : ℕ => (sigmaFan x V E v)^[k] u) (Set.Iio n) := by
    intro k hk_mem l hl_mem heq
    have hk : k < n := Set.mem_Iio.mp hk_mem
    have hl : l < n := Set.mem_Iio.mp hl_mem
    rcases lt_trichotomy k l with h | h | h
    · exact absurd heq.symm (cyclic_power_sigmaFan x V E hfan hvu l k
        (by rw [← hn]; omega) h)
    · exact h
    · exact absurd heq (cyclic_power_sigmaFan x V E hfan hvu k l
        (by rw [← hn]; omega) h)
  have hcard_seg : ((fun k : ℕ => (sigmaFan x V E v)^[k] u) '' (Set.Iio n)).ncard =
      n := by
    rw [Set.InjOn.ncard_image hinj_seg, Set.ncard_Iio_nat]
  -- 截段像集 = soe（n 元子集含于 n 元 soe）
  have hseg_eq : (fun k : ℕ => (sigmaFan x V E v)^[k] u) '' (Set.Iio n)
      = setOfEdge v V E := by
    by_contra hne
    have hss := Set.ncard_lt_ncard (lt_of_le_of_ne hseg hne)
      (remark_finite_fan1 v V E hfan.2.2.1.1)
    rw [hcard_seg] at hss
    omega
  -- σ^[n] u ∈ soe = 截段 → 与某 σ^[k] u (k < n) 重合 → 更短周期矛盾
  have hmem_seg : (sigmaFan x V E v)^[n] u ∈
      (fun k : ℕ => (sigmaFan x V E v)^[k] u) '' (Set.Iio n) := by
    rw [hseg_eq]
    exact iterates_mem_setOfEdge hfan v u hu_soe n
  obtain ⟨k, hk, hk_eq⟩ := hmem_seg
  have hk' : k < n := Set.mem_Iio.mp hk
  have hk_eq' : (sigmaFan x V E v)^[k] u = (sigmaFan x V E v)^[n] u := hk_eq
  rcases Nat.eq_zero_or_pos k with h0k | h0k
  · rw [h0k, Function.iterate_zero] at hk_eq'
    exact hk_eq'.symm
  have hsplit : (sigmaFan x V E v)^[n] u =
      (sigmaFan x V E v)^[k] ((sigmaFan x V E v)^[n - k] u) := by
    have hadd : k + (n - k) = n := by omega
    rw [← Function.iterate_add_apply, hadd]
  have hrep : (sigmaFan x V E v)^[n - k] u = u := by
    have heq2 : (sigmaFan x V E v)^[k] u =
        (sigmaFan x V E v)^[k] ((sigmaFan x V E v)^[n - k] u) := by
      rw [← hsplit]; exact hk_eq'
    exact (iterates_injOn_setOfEdge hfan v k hu_soe
      (iterates_mem_setOfEdge hfan v u hu_soe (n - k)) heq2).symm
  exact absurd hrep (key_lemma_cyclic x V E hfan hvu (n - k)
    (by omega) (by omega))

/-- Every `w ∈ setOfEdge v V E` is `(sigmaFan x V E v)^[j] u` for some
`j < ncard`.  Proof: orbit = setOfEdge (by `orbit_eq_setOfEdge`),
`σ^[ncard] u = u` (by `order_power_sigmaFan`), so `σ^[i] u = σ^[i mod ncard] u`
and `i mod ncard < ncard`. -/
theorem iterates_mem_sigmaFan (hfan : FAN x V E) {v u : V3} (hvu : {v, u} ∈ E)
    {w : V3} (hw : w ∈ setOfEdge v V E) :
    ∃ j, j < (setOfEdge v V E).ncard ∧ (sigmaFan x V E v)^[j] u = w := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hmem : w ∈ setOfOrbitsPointsFan x V E v u :=
    (orbit_eq_setOfEdge hfan hvu).symm ▸ hw
  obtain ⟨i, hi⟩ := hmem
  set n := (setOfEdge v V E).ncard
  have hn_pos : 0 < n := by
    show 0 < (setOfEdge v V E).ncard
    exact Nat.pos_of_ne_zero (fun h =>
      Set.nonempty_iff_ne_empty.mp ⟨u, hu_soe⟩
        ((Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)).mp h))
  have hperiod : (sigmaFan x V E v)^[n] u = u :=
    order_power_sigmaFan x V E hfan hvu rfl
  have hmod_eq : (sigmaFan x V E v)^[i] u =
      (sigmaFan x V E v)^[i % n] u := by
    conv_lhs => rw [show i = i % n + n * (i / n) from (Nat.mod_add_div i n).symm]
    rw [Function.iterate_add_apply, Nat.mul_comm n (i / n),
      show (sigmaFan x V E v)^[i / n * n] u = u from
        fix_point_sigmaFan x V E v u (i / n) n hperiod]
  exact ⟨i % n, Nat.mod_lt _ hn_pos, hmod_eq ▸ hi⟩

/-! ## 绕圈角和（topology.hl:793–850 重构） -/

/-- HOL topology.hl:793 `azim_i_fan`：第 i 步的角增量。 -/
noncomputable def azimIfan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) : ℝ :=
  azim x v ((sigmaFan x V E v)^[i] u) ((sigmaFan x V E v)^[i + 1] u)

/-- HOL topology.hl:205 `MONO_AZIM_POWER_SIGMA_FAN`：azim 沿迭代不减
（前提 `pm (i+1) ≠ u`，即 HOL 原版前提；无前提版数学上不成立）。 -/
theorem mono_azim_power_sigmaFan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hne : (sigmaFan x V E v)^[i + 1] u ≠ u) :
    azim x v u ((sigmaFan x V E v)^[i] u) ≤
      azim x v u ((sigmaFan x V E v)^[i + 1] u) := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have h1 : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr
      (iterates_mem_setOfEdge hfan v u hu_soe i)
  have hs : (sigmaFan x V E v)^[i + 1] u =
      sigmaFan x V E v ((sigmaFan x V E v)^[i] u) :=
    Function.iterate_succ_apply' (sigmaFan x V E v) i u
  have hne' : sigmaFan x V E v ((sigmaFan x V E v)^[i] u) ≠ u := by
    intro hc
    apply hne
    rw [hs]
    exact hc
  rw [hs]
  exact mono_azim_sigmaFan hfan hvu h1 hne'

/-- HOL topology.hl:851 `AZIM_LE_POWER_SIGMA_FAN`（严格版）：`j < i <
CARD(soe)` ⟹ azim 沿迭代严格递增。单步严格性：等号给
unique_azim_point_fan 的不动点，违反 SIGMA_FAN 第二条件（`soe ≠
{pm k}`：k = 0 时由 `soe ≠ {u}`，0 < k 时由 key_lemma）。 -/
theorem azim_lt_power_sigmaFan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u})
    (i j : ℕ) (hji : j < i) (hin : i < (setOfEdge v V E).ncard) :
    azim x v u ((sigmaFan x V E v)^[j] u) <
      azim x v u ((sigmaFan x V E v)^[i] u) := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  -- 单步严格（k+1 在循环长内：mono 前提与 key_lemma 都需要）
  have hstrict1 : ∀ k : ℕ, k + 1 < (setOfEdge v V E).ncard →
      azim x v u ((sigmaFan x V E v)^[k] u) <
        azim x v u ((sigmaFan x V E v)^[k + 1] u) := by
    intro k hk
    by_contra hge
    push_neg at hge
    have hne1 := key_lemma_cyclic x V E hfan hvu (k + 1) (by omega) hk
    have heq := le_antisymm hge (mono_azim_power_sigmaFan hfan hvu k hne1)
    have h1e : {v, (sigmaFan x V E v)^[k] u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr
        (iterates_mem_setOfEdge hfan v u hu_soe k)
    have h2e : {v, (sigmaFan x V E v)^[k + 1] u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr
        (iterates_mem_setOfEdge hfan v u hu_soe (k + 1))
    have hpt := unique_azim_point_fan hfan hvu h1e h2e heq.symm
    -- soe ≠ {pm k}
    have hne_soe : setOfEdge v V E ≠ {(sigmaFan x V E v)^[k] u} := by
      intro h
      rcases Nat.eq_zero_or_pos k with h0k | h0k
      · rw [h0k, Function.iterate_zero_apply] at h
        exact hne_u h
      · rw [h] at hu_soe
        exact key_lemma_cyclic x V E hfan hvu k h0k
          (by omega) (Set.mem_singleton_iff.mp hu_soe).symm
    have hs2 : (sigmaFan x V E v)^[k + 1] u =
        sigmaFan x V E v ((sigmaFan x V E v)^[k] u) :=
      Function.iterate_succ_apply' _ k u
    rw [hs2] at hpt
    exact (SIGMA_FAN hne_soe hfan
      (iterates_mem_setOfEdge hfan v u hu_soe k)).2.1 hpt.symm
  -- 链传播（所有步 k+1 ≤ i < n）
  have hchain : ∀ p q : ℕ, p < q → q ≤ i →
      azim x v u ((sigmaFan x V E v)^[p] u) <
        azim x v u ((sigmaFan x V E v)^[q] u) := by
    intro p q hpq hqi
    induction q with
    | zero => exact absurd hpq (Nat.not_lt_zero p)
    | succ q ihq =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hpq with h | h
      · exact lt_trans (ihq h (Nat.le_of_succ_le_succ (by omega)))
          (hstrict1 q (by omega))
      · rw [h]; exact hstrict1 q (by omega)
  exact hchain j i hji (Nat.le_refl i)

/-- HOL topology.hl:735 前置：`soe ≠ {u}` ⟹ `2 ≤ CARD(soe)`
（u 与某 w ≠ u 同在 soe，{u,w} 嵌入 + ncard_pair）。 -/
theorem two_le_ncard_of_ne (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u}) :
    (2:ℕ) ≤ (setOfEdge v V E).ncard := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  obtain ⟨w, hw_soe, hwu⟩ : ∃ w ∈ setOfEdge v V E, w ≠ u := by
    by_contra hall
    push_neg at hall
    exact hne_u
      (Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨u, hu_soe⟩, fun x hx => hall x hx⟩)
  have hsub : ({u, w} : Set V3) ⊆ setOfEdge v V E := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hu_soe
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hw_soe
  have hnc2 : ({u, w} : Set V3).ncard = 2 := Set.ncard_pair (Ne.symm hwu)
  have hle := Set.ncard_le_ncard hsub (remark_finite_fan1 v V E hfan.2.2.1.1)
  omega

/-- HOL topology.hl:735 `SUM_IF_AZIMS_FAN`：if_azims 的递推
（`ifAzims (i+1) = ifAzims i + azimIfan i`）。终局分支由
azim_compl 补角 + unique_azim0 + key_lemma 拼合；中间分支由
sum2_azim_fan 直接给出。 -/
theorem sum_if_azims (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hi1 : 0 < i) (hin : i < (setOfEdge v V E).ncard) :
    ifAzimsFan x V E v u (i + 1) =
      ifAzimsFan x V E v u i + azimIfan x V E v u i := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hpmi_soe : (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E :=
    iterates_mem_setOfEdge hfan v u hu_soe i
  have hpmi_edge : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr hpmi_soe
  have hncpm : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) :=
    fan_not_collinear hfan hpmi_edge
  have hi_ne : i ≠ (setOfEdge v V E).ncard := Nat.ne_of_lt hin
  rw [ifAzimsFan, ifAzimsFan, if_neg hi_ne]
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hin) with h1n | h1n
  · -- i + 1 = n：终局分支，if_azims(i+1) = 2π，azimIfan i = azim (pm i) u
    rw [Nat.succ_eq_add_one] at h1n
    have hpm : (sigmaFan x V E v)^[i + 1] u = u :=
      order_power_sigmaFan x V E hfan hvu h1n
    have h0 : azim x v u ((sigmaFan x V E v)^[i] u) ≠ 0 := by
      intro h0
      have huw : u = (sigmaFan x V E v)^[i] u :=
        unique_azim0_point_fan hfan hvu hpmi_edge h0
      exact key_lemma_cyclic x V E hfan hvu i hi1 hin huw.symm
    rw [h1n, if_pos rfl, azimIfan, hpm, azim_compl hncu hncpm, if_neg h0]
    ring
  · -- i + 1 < n：中间分支，sum2_azim_fan 直接给出
    have hpm1_soe : (sigmaFan x V E v)^[i + 1] u ∈ setOfEdge v V E :=
      iterates_mem_setOfEdge hfan v u hu_soe (i + 1)
    have hpm1_edge : {v, (sigmaFan x V E v)^[i + 1] u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr hpm1_soe
    have hne1 := key_lemma_cyclic x V E hfan hvu (i + 1) (by omega) (by omega)
    have hle := mono_azim_power_sigmaFan hfan hvu i hne1
    rw [if_neg (by omega : ¬(i + 1 = (setOfEdge v V E).ncard)), azimIfan]
    exact sum2_azim_fan hfan hvu hpmi_edge hpm1_edge hle

/-- HOL topology.hl:795 `SUM_EQ_IF_AZIMS_FAN`：前 i+1 步角增量之和 =
if_azims (i+1)（对 i 归纳）。 -/
theorem sum_eq_if_azims (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u})
    (i : ℕ) (hin : i < (setOfEdge v V E).ncard) :
    ∑ k ∈ Finset.range (i + 1), azimIfan x V E v u k =
      ifAzimsFan x V E v u (i + 1) := by
  induction i with
  | zero =>
    have h1n : (1:ℕ) ≠ (setOfEdge v V E).ncard := by
      have := two_le_ncard_of_ne hfan hvu hne_u
      omega
    rw [show Finset.range (0 + 1) = {0} from rfl, Finset.sum_singleton, azimIfan,
      ifAzimsFan, if_neg h1n, Function.iterate_zero_apply, Nat.zero_add]
  | succ i ih =>
    have hin' : i < (setOfEdge v V E).ncard := by omega
    rw [Finset.range_add_one, Finset.sum_insert (Finset.notMem_range_self), ih hin',
      add_comm (azimIfan x V E v u (i + 1)) (ifAzimsFan x V E v u (i + 1)),
      sum_if_azims hfan hvu (i + 1) (by omega) (by omega)]

/-- HOL topology.hl:833 `SUM_AZIMS_EQ_2PI_FAN`：**绕一圈角和 = 2π**
（σ 循环的几何本质）。 -/
theorem sum_azims_eq_2pi (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u}) :
    ∑ k ∈ Finset.range (setOfEdge v V E).ncard, azimIfan x V E v u k
      = 2 * Real.pi := by
  have h1n : (1:ℕ) < (setOfEdge v V E).ncard := by
    have := two_le_ncard_of_ne hfan hvu hne_u
    omega
  have h := sum_eq_if_azims hfan hvu hne_u
    ((setOfEdge v V E).ncard - 1)
    (by omega)
  have hrange : Finset.range ((setOfEdge v V E).ncard - 1 + 1)
      = Finset.range (setOfEdge v V E).ncard := by
    congr 1; omega
  rw [hrange] at h
  rw [h, ifAzimsFan,
    if_pos (show (setOfEdge v V E).ncard - 1 + 1 =
      (setOfEdge v V E).ncard by omega)]

/-- HOL topology.hl:908 `SUM_AZIM_POWER_SIGMA_FAN`：第 j 步到第 i 步的
角增量 = azim（链式分解）。即 `azim (pm j) (pm i)` 型三点角恒等式。 -/
theorem sum_azim_power_sigmaFan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u})
    (i j : ℕ) (hji : j < i) (hin : i < (setOfEdge v V E).ncard) :
    azim x v u ((sigmaFan x V E v)^[i] u) =
      azim x v u ((sigmaFan x V E v)^[j] u) +
        azim x v ((sigmaFan x V E v)^[j] u) ((sigmaFan x V E v)^[i] u) := by
  have hle : azim x v u ((sigmaFan x V E v)^[j] u) ≤
      azim x v u ((sigmaFan x V E v)^[i] u) :=
    le_of_lt (azim_lt_power_sigmaFan hfan hvu hne_u i j hji hin)
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hw_j : {v, (sigmaFan x V E v)^[j] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr
      (iterates_mem_setOfEdge hfan v u hu_soe j)
  have hw_i : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr
      (iterates_mem_setOfEdge hfan v u hu_soe i)
  exact sum2_azim_fan hfan hvu hw_j hw_i hle

/-- HOL topology.hl:954 `SUM1_IFAZIMS_FAN`：if_azims 差异 = 三点角增量
（j < i < ncard 时 if_azims 未到终局分支，直接退化为
sum_azim_power_sigmaFan）。 -/
theorem sum1_ifAzimsFan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u})
    (i j : ℕ) (hji : j < i) (hin : i < (setOfEdge v V E).ncard) :
    ifAzimsFan x V E v u i =
      ifAzimsFan x V E v u j +
        azim x v ((sigmaFan x V E v)^[j] u) ((sigmaFan x V E v)^[i] u) := by
  have hni : i ≠ (setOfEdge v V E).ncard := by omega
  have hnj : j ≠ (setOfEdge v V E).ncard := by omega
  rw [ifAzimsFan, ifAzimsFan, if_neg hni, if_neg hnj]
  exact sum_azim_power_sigmaFan hfan hvu hne_u i j hji hin

/-- HOL topology.hl:973 `ULEKUUB`：if_azims 差异恒等式 与 绕一圈角和
= 2π 的合取打包（后者取 `1 < CARD(soe)` 前提形）。 -/
theorem ulekuub (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u})
    (h1n : (1:ℕ) < (setOfEdge v V E).ncard) :
    (∀ i j : ℕ, j < i → i < (setOfEdge v V E).ncard →
      ifAzimsFan x V E v u i =
        ifAzimsFan x V E v u j +
          azim x v ((sigmaFan x V E v)^[j] u) ((sigmaFan x V E v)^[i] u)) ∧
    (∑ k ∈ Finset.range (setOfEdge v V E).ncard, azimIfan x V E v u k
      = 2 * Real.pi) := by
  constructor
  · intro i j hji hin
    exact sum1_ifAzimsFan hfan hvu hne_u i j hji hin
  · exact sum_azims_eq_2pi hfan hvu hne_u

/-! ## 楔形分解（topology.hl:996–1234 重构）

wedge2_fan = aff_gt 的关键是 `azim_eq_azim_iff`（AZIM_EQ，已在
AzimLemmas 落地）：`azim x v u w = azim x v u y ↔ y ∈ aff_gt {x,v} {w}`。
HOL 此块的 aff_gt 组合不变性（th1）、补集判定（th2/COMPLEMENT_SET_FAN）
与两向包含（aff_gt_subset_wedge_fan2 / wedge_fan2_subset_aff_gt）都从此
出发重述。 -/

/-- HOL topology.hl:996 `wedge2_fan`：if_azims 等值面 ∩ 仿射补集。 -/
noncomputable def wedge2Fan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) : Set V3 :=
  {y | ifAzimsFan x V E v u i = azim x v u y ∧ y ∈ complementSet x v}

/-- HOL topology.hl:1002 `affine_hull_2_fan`：两点仿射包的凸组合刻画
（HOL `aff {x,v}` ↔ Mathlib `affineSpan ℝ {x,v}`）。 -/
theorem affine_hull_2_fan (x v : V3) :
    (affineSpan ℝ ({x, v} : Set V3) : Set V3) =
      {y | ∃ t1 t2 : ℝ, t1 + t2 = 1 ∧ y = t1 • x + t2 • v} := by
  ext y
  constructor
  · intro hy
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    refine ⟨1 - r, r, by ring, ?_⟩
    have hlm : y = r • (v - x) + x := by
      rw [← hr]
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    rw [hlm]
    module
  · rintro ⟨t1, t2, ht, hy⟩
    rw [hy]
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t2, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    have ht' : 1 - t2 = t1 := by linarith
    rw [← ht']
    module

/-- 两点 collinear ↔ 仿射包成员（两点互异时）。 -/
theorem collinear3_iff_mem_affineSpan {v0 v1 y : V3} (hv0v1 : v0 ≠ v1) :
    Collinear3 v0 v1 y ↔
      y ∈ (affineSpan ℝ ({v0, v1} : Set V3) : Set V3) := by
  constructor
  · intro hc
    by_cases hy0 : y = v0
    · rw [hy0]
      exact left_mem_affineSpan_pair _ _ _
    by_cases hy1 : y = v1
    · rw [hy1]
      exact right_mem_affineSpan_pair _ _ _
    obtain ⟨c, hsmul⟩ := (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mp hc
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (sub_eq_iff_eq_add.mp hsmul).symm
  · intro hy
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    by_cases hy1 : y = v1
    · rw [hy1]
      exact collinear3_pair_right (v0 := v0) (v1 := v1) rfl
    have hsmul : y - v0 = r • (v1 - v0) := by
      rw [← hr]
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mpr ⟨r, hsmul⟩

/-- affGt 三点组合：`y = t1•x + t2•v + t3•w`（t3 > 0, t1+t2+t3 = 1）
落在 `aff_gt {x,v} {w}` 中。 -/
theorem affGt_of_triple {x v w y : V3} (t1 t2 t3 : ℝ) (ht3 : 0 < t3)
    (ht : t1 + t2 + t3 = 1) (hy : y = t1 • x + t2 • v + t3 • w)
    (hxv : x ≠ v) (hxw : x ≠ w) (hvw : v ≠ w) :
    y ∈ affGt {x, v} {w} := by
  refine (affGt_pair_iff (v0 := x) (v1 := v) (x := w) (y := y)
    hxv (Ne.symm hxw) (Ne.symm hvw)).mpr ⟨t3, ht3, t2, ?_⟩
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  rw [hy, ht1]
  module

/-- HOL topology.hl:1080 `th1`：aff_gt 组合保持 azim（组合点与 w 同向，
因 y - x = t3•(w - x) + t2•(v - x)，投影平面内成正倍数）。 -/
theorem azim_of_affGt_combo (hu : ¬ Collinear3 x v u) (hw : ¬ Collinear3 x v w)
    (t1 t2 t3 : ℝ) (ht3 : 0 < t3) (ht : t1 + t2 + t3 = 1)
    (hy : y = t1 • x + t2 • v + t3 • w) :
    azim x v u w = azim x v u y := by
  have hxv : x ≠ v := fun he => hw (collinear3_of_eq (v := x) (w := v) (w1 := w) he.symm)
  have hxw : x ≠ w := fun he => hw
    (collinear3_pair_left (v0 := x) (v1 := v) (x := w) he.symm)
  have hvw : v ≠ w := by
    intro he
    rw [he] at hw
    exact hw (collinear3_pair_right (v0 := x) (v1 := w) rfl)
  have hygt : y ∈ affGt {x, v} {w} := affGt_of_triple t1 t2 t3 ht3 ht hy hxv hxw hvw
  have hyncol : ¬ Collinear3 x v y := by
    intro hc
    have hline : y ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
      (collinear3_iff_mem_affineSpan hxv).mp hc
    rw [affine_hull_2_fan] at hline
    obtain ⟨s1, s2, hs, hcombo⟩ := hline
    have hsum : (s1 - t1) / t3 + (s2 - t2) / t3 = 1 := by
      field_simp [ht3.ne']
      linarith
    have hcombo' : t1 • x + t2 • v + t3 • w = s1 • x + s2 • v := by
      rw [hy] at hcombo
      exact hcombo
    have hq : t3 • w = (s1 - t1) • x + (s2 - t2) • v := by
      have hh1 : t3 • w = s1 • x + s2 • v - t1 • x - t2 • v := by
        rw [← hcombo']
        module
      rw [hh1]
      module
    have hsub : ((s1 - t1) / t3) • x + ((s2 - t2) / t3) • v = w := by
      have hq' : ((s1 - t1) / t3) • x + ((s2 - t2) / t3) • v = (t3⁻¹ : ℝ) • (t3 • w) := by
        rw [hq]
        rw [smul_add, smul_smul, smul_smul]
        congr 1 <;> congr 1
        · field_simp [ht3.ne']
        · field_simp [ht3.ne']
      rw [hq']
      exact inv_smul_smul₀ ht3.ne' w
    have hwsp : w ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
      rw [affine_hull_2_fan]
      exact ⟨(s1 - t1) / t3, (s2 - t2) / t3, hsum, hsub.symm⟩
    exact hw ((collinear3_iff_mem_affineSpan hxv).mpr hwsp)
  exact (azim_eq_azim_iff (v0 := x) (v1 := v) (w := u) (x := w) (y := y) hu hw hyncol).mpr hygt

/-- HOL topology.hl:1099 `th2`：`x ≠ v` 时补集中的点不与 x,v 共线
（共线 ⟹ 在仿射包中，与补集定义矛盾）。 -/
theorem complementSet_noncollinear {x v y : V3} (hxv : x ≠ v)
    (hy : y ∈ complementSet x v) : ¬ Collinear3 x v y := by
  intro hc
  have hline : y ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
    (collinear3_iff_mem_affineSpan hxv).mp hc
  exact hy hline

/-- HOL topology.hl:1110 `COMPLEMENT_SET_FAN`：aff_gt 组合点的补集判定
（t3 ≠ 0 保证组合方向偏离仿射包）。 -/
theorem complementSet_of_combo {x v w y : V3} (t1 t2 t3 : ℝ)
    (hw : w ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3))
    (ht3 : t3 ≠ 0) (ht : t1 + t2 + t3 = 1)
    (hy : y = t1 • x + t2 • v + t3 • w) :
    y ∈ complementSet x v := by
  intro hyaff
  rw [affine_hull_2_fan] at hyaff
  obtain ⟨s1, s2, hs, hcombo⟩ := hyaff
  have hcombo' : t1 • x + t2 • v + t3 • w = s1 • x + s2 • v := by
    rw [hy] at hcombo
    exact hcombo
  have hsum : (s1 - t1) / t3 + (s2 - t2) / t3 = 1 := by
    field_simp [ht3]
    linarith
  have hq : t3 • w = (s1 - t1) • x + (s2 - t2) • v := by
    have hh1 : t3 • w = s1 • x + s2 • v - t1 • x - t2 • v := by
      rw [← hcombo']
      module
    rw [hh1]
    module
  have hsub : ((s1 - t1) / t3) • x + ((s2 - t2) / t3) • v = w := by
    have hq' : ((s1 - t1) / t3) • x + ((s2 - t2) / t3) • v = (t3⁻¹ : ℝ) • (t3 • w) := by
      rw [hq]
      rw [smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1
      · field_simp [ht3]
      · field_simp [ht3]
    rw [hq']
    exact inv_smul_smul₀ ht3 w
  apply hw
  rw [affine_hull_2_fan]
  exact ⟨(s1 - t1) / t3, (s2 - t2) / t3, hsum, hsub.symm⟩

/-- HOL topology.hl:1141 `aff_gt_subset_wedge_fan2`：`i ≠ CARD` 且非共线
时 aff_gt 的楔形位于 wedge2_fan 中（azim 相等由 azim_of_affGt_combo，
补集由 complementSet_of_combo）。 -/
theorem affGt_subset_wedge2Fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hin : i ≠ (setOfEdge v V E).ncard)
    (hncu : ¬ Collinear3 x v u)
    (hncw : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u)) :
    affGt {x, v} {(sigmaFan x V E v)^[i] u} ⊆ wedge2Fan x V E v u i := by
  set w := (sigmaFan x V E v)^[i] u
  intro y hy
  rw [wedge2Fan]
  have hxv : x ≠ v := fun he => hncw
    (collinear3_of_eq (v := x) (w := v) (w1 := (sigmaFan x V E v)^[i] u) he.symm)
  have hxw : x ≠ (sigmaFan x V E v)^[i] u :=
    fun he => hncw (collinear3_pair_left (v0 := x) (v1 := v)
      (x := (sigmaFan x V E v)^[i] u) he.symm)
  have hvw : v ≠ (sigmaFan x V E v)^[i] u :=
    fun he => hncw (collinear3_pair_right (v0 := x) (v1 := v)
      (x := (sigmaFan x V E v)^[i] u) he.symm)
  obtain ⟨c, hc, hh, hcoeff⟩ :=
    (affGt_pair_iff (v0 := x) (v1 := v) (x := (sigmaFan x V E v)^[i] u)
      (y := y) hxv (Ne.symm hxw) (Ne.symm hvw)).mp hy
  have hcombo : y = (1 - c - hh) • x + hh • v + c • (sigmaFan x V E v)^[i] u := by
    rw [sub_eq_iff_eq_add] at hcoeff
    rw [hcoeff]
    module
  constructor
  · rw [ifAzimsFan, if_neg hin]
    symm
    exact (azim_of_affGt_combo hncu hncw (t1 := 1 - c - hh) (t2 := hh) (t3 := c)
      hc (by ring) hcombo).symm
  · rw [complementSet]
    intro hyaff
    have hwsp : (sigmaFan x V E v)^[i] u ∉
        (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
      fun hwa => hncw ((collinear3_iff_mem_affineSpan hxv).mpr hwa)
    exact (complementSet_of_combo (x := x) (v := v)
      (w := (sigmaFan x V E v)^[i] u)
      (t1 := 1 - c - hh) (t2 := hh) (t3 := c) hwsp hc.ne' (by ring) hcombo) hyaff

/-- HOL topology.hl:1171 `wedge_fan2_subset_aff_gt`：wedge2_fan 的成员
（非共线、不在仿射包）落在 aff_gt 中。 -/
theorem wedge2Fan_subset_affGt (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hin : i ≠ (setOfEdge v V E).ncard)
    (hncu : ¬ Collinear3 x v u)
    (hncw : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u)) :
    wedge2Fan x V E v u i ⊆ affGt {x, v} {(sigmaFan x V E v)^[i] u} := by
  intro y hy
  rw [wedge2Fan] at hy
  obtain ⟨haz, hcomp⟩ := hy
  have hxv : x ≠ v := fun he => hncu
    (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  have hxw : x ≠ (sigmaFan x V E v)^[i] u :=
    fun he => hncw (collinear3_pair_left (v0 := x) (v1 := v)
      (x := (sigmaFan x V E v)^[i] u) he.symm)
  have hvw : v ≠ (sigmaFan x V E v)^[i] u :=
    fun he => hncw (collinear3_pair_right (v0 := x) (v1 := v)
      (x := (sigmaFan x V E v)^[i] u) he.symm)
  have hyncol : ¬ Collinear3 x v y := complementSet_noncollinear hxv hcomp
  rw [ifAzimsFan, if_neg hin] at haz
  exact (azim_eq_azim_iff (v0 := x) (v1 := v) (w := u) (x := (sigmaFan x V E v)^[i] u)
    (y := y) hncu hncw hyncol).mp haz

/-- HOL topology.hl:1196 `wedge_fan2_equal_aff_gt`：双包含。 -/
theorem wedge2Fan_eq_affGt (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hin : i ≠ (setOfEdge v V E).ncard)
    (hncu : ¬ Collinear3 x v u)
    (hncw : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u)) :
    wedge2Fan x V E v u i = affGt {x, v} {(sigmaFan x V E v)^[i] u} :=
  Set.Subset.antisymm
    (wedge2Fan_subset_affGt hfan hvu i hin hncu hncw)
    (affGt_subset_wedge2Fan hfan hvu i hin hncu hncw)

/-- HOL topology.hl:1212 `wedge_fan2_equal_aff_gt_fan`：FAN 前提下
`i ≠ CARD` ⟹ wedge2_fan = aff_gt（fan6 保证非共线）。 -/
theorem wedge2Fan_eq_affGt_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) (hin : i ≠ (setOfEdge v V E).ncard) :
    wedge2Fan x V E v u i = affGt {x, v} {(sigmaFan x V E v)^[i] u} := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hw_soe : (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E :=
    iterates_mem_setOfEdge hfan v u hu_soe i
  have hw_edge : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr hw_soe
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hncw : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) :=
    fan_not_collinear hfan hw_edge
  exact wedge2Fan_eq_affGt hfan hvu i hin hncu hncw

/-! ## wedge3 与轨道楔形（topology.hl:1237–1343 重构）

前置引理（fan.hl）：IN2_ORBITS_FAN（迭代仍为边）、
remark_power_map_points（迭代点全体性质）、sum3/sum4_azim_fan
（无 E 前提的三点角加法）。wedge3_fan 在 wedge2 基础上加严格上下界。
w_dart_eq_wedge3_fan 重构：楔形成员 ⟺ azim 落在 [if_azims i, if_azims
(SUC i)) 开区间——上界由 SUM_AZIM_POWER_SIGMA_FAN + sum_if_azims
展开，下界由 azim_lt_power_sigmaFan + sum1_ifAzimsFan 得。 -/

/-- HOL fan.hl:1056 `IN2_ORBITS_FAN`：σ-迭代保持边。 -/
theorem in2_orbits_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) (i : ℕ) :
    {v, (sigmaFan x V E v)^[i] u} ∈ E := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  exact (properties_of_setOfEdge_fan x V E v _ hfan).mpr
    (iterates_mem_setOfEdge hfan v u hu_soe i)

/-- HOL fan.hl `remark_power_map_points`：迭代点全体性质
（边、共线、互异、仿射包外）。 -/
theorem remark_power_map_points (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i : ℕ) :
    (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E ∧
    {v, (sigmaFan x V E v)^[i] u} ∈ E ∧
    ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) ∧
    x ≠ (sigmaFan x V E v)^[i] u ∧
    v ≠ (sigmaFan x V E v)^[i] u ∧
    (sigmaFan x V E v)^[i] u ∉
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hw_soe : (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E :=
    iterates_mem_setOfEdge hfan v u hu_soe i
  have hw_edge : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v _ hfan).mpr hw_soe
  have hncw : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) :=
    fan_not_collinear hfan hw_edge
  have hxv : x ≠ v := by
    intro he
    exact fan_not_collinear hfan hvu
      (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  constructor
  · exact hw_soe
  constructor
  · exact hw_edge
  constructor
  · exact hncw
  constructor
  · intro he
    exact hncw (collinear3_pair_left (v0 := x) (v1 := v) (x := (sigmaFan x V E v)^[i] u) he.symm)
  constructor
  · intro he
    exact hncw (collinear3_pair_right (v0 := x) (v1 := v) (x := (sigmaFan x V E v)^[i] u) he.symm)
  · intro hwa
    exact hncw ((collinear3_iff_mem_affineSpan hxv).mpr hwa)

/-- 三点角加法的标架核心：给定非共线，`azim x v u w2` 与
`azim x v u w1 + azim x v w1 w2` 相差 `n·2π`。 -/
private theorem azim_sum_core (hxv : v ≠ x) (hncu : ¬ Collinear3 x v u)
    (hnc1 : ¬ Collinear3 x v w1) (hnc2 : ¬ Collinear3 x v w2) :
    ∃ n : ℤ, azim x v u w2 =
      azim x v u w1 + azim x v w1 w2 + (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr (fun he => hxv he))
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hncu hnc1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hncu hnc2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec hnc1 hnc2 hon hax hxv
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * I)
      = Complex.exp (((ψ : ℝ) : ℂ) * I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  refine ⟨n, ?_⟩
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2

/-- HOL fan.hl:1698 `sum4_azim_fan`：三点角加法（`azim x v u w1 ≤
azim x v u w2` 版本，无 E 前提）。 -/
theorem sum4_azim_fan (hxv : v ≠ x) (hncu : ¬ Collinear3 x v u)
    (hnc1 : ¬ Collinear3 x v w1) (hnc2 : ¬ Collinear3 x v w2)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨n, hc3⟩ := azim_sum_core hxv hncu hnc1 hnc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-- HOL fan.hl:1597 `sum3_azim_fan`：三点角加法（`azim x v u w1 +
azim x v w1 w2 < 2π` 版本）。 -/
theorem sum3_azim_fan (hxv : v ≠ x) (hncu : ¬ Collinear3 x v u)
    (hnc1 : ¬ Collinear3 x v w1) (hnc2 : ¬ Collinear3 x v w2)
    (hlt : azim x v u w1 + azim x v w1 w2 < 2 * Real.pi) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨n, hc3⟩ := azim_sum_core hxv hncu hnc1 hnc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-- HOL topology.hl:1237 `wedge3_fan`：if_azims 严格上/下界间的楔形
（开区间版 wedge2）。 -/
noncomputable def wedge3Fan (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) : Set V3 :=
  {y | ifAzimsFan x V E v u i < azim x v u y ∧
    azim x v u y < ifAzimsFan x V E v u (i + 1) ∧ y ∈ complementSet x v}

/-- HOL fan.hl:1755 `sum5_azim_fan`：三点角加法（`azim x v w1 w2 ≤
azim x v u w2` 版本，无 E 前提）。 -/
theorem sum5_azim_fan (hxv : v ≠ x) (hncu : ¬ Collinear3 x v u)
    (hnc1 : ¬ Collinear3 x v w1) (hnc2 : ¬ Collinear3 x v w2)
    (hle : azim x v w1 w2 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨n, hc3⟩ := azim_sum_core hxv hncu hnc1 hnc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr1'1 : azim x v u w1 < 2 * Real.pi := azim_lt_two_pi x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : (n : ℤ) ≤ -1)
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith [hle, hc3, hr1'1, hmul]
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by exact_mod_cast (by omega : (n : ℤ) ≥ 1)
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith [hr1'0, hr2'0, hr3'1, hmul, hc3]

/-- `i < CARD(soe)` 时 `ifAzims i = azim x v u (σ^i u)`（定义直接）。 -/
theorem ifAzimsFan_eq_azim (x : V3) (V : Set V3) (E : Set (Set V3)) (v u : V3)
    (i : ℕ) (hin : i < (setOfEdge v V E).ncard) :
    ifAzimsFan x V E v u i = azim x v u ((sigmaFan x V E v)^[i] u) := by
  rw [ifAzimsFan, if_neg (by omega)]

/-- `w_dart_fan x V E (x,v,pm i,pm(SUC i))`（CARD > 1 时）展开为
`wedge x v (pm i) (pm(SUC i))`。 -/
theorem wDartFan_of_ncard_gt_one (hfan : FAN x V E) {v u : V3} (hvu : {v, u} ∈ E)
    (hcard : 1 < (setOfEdge v V E).ncard) (i : ℕ) :
    wDartFan x V E (x, v, (sigmaFan x V E v)^[i] u, (sigmaFan x V E v)^[i + 1] u)
      = wedge x v ((sigmaFan x V E v)^[i] u) ((sigmaFan x V E v)^[i + 1] u) := by
  rw [wDartFan, if_pos hcard]
  congr 2
  rw [Function.iterate_succ_apply']

/-- `i < CARD` 时 pm i 与 pm(SUC i) 的非共线（remark_power_map_points）。 -/
private theorem pm_noncollinear (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hin : i < (setOfEdge v V E).ncard) :
    ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) :=
  (remark_power_map_points hfan hvu i).2.2.1

/-- `x ≠ v`（FAN 下的非退化，fan_not_collinear 的分量）。 -/
private theorem fan_x_ne_v (hfan : FAN x V E) (hvu : {v, u} ∈ E) : x ≠ v := by
  intro he
  exact fan_not_collinear hfan hvu
    (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)

/-- 非共线点与补集的互化（x ≠ v 时）。 -/
private theorem mem_complementSet_iff_noncollinear (hfan : FAN x V E)
    (hvu : {v, u} ∈ E) (y : V3) :
    y ∈ complementSet x v ↔ ¬ Collinear3 x v y := by
  have hxv : x ≠ v := fan_x_ne_v hfan hvu
  constructor
  · exact complementSet_noncollinear hxv
  · intro hnc
    intro hyaff
    exact hnc ((collinear3_iff_mem_affineSpan hxv).mpr hyaff)

/-- `azim_compl` when the azim is known nonzero: avoids the `ite` wrapper
and the expensive `rw [if_neg h]` tactic. -/
private theorem azim_compl_ne_zero {z w w1 w2 : V3}
    (hnc1 : ¬ Collinear3 z w w1) (hnc2 : ¬ Collinear3 z w w2)
    (h : azim z w w1 w2 ≠ 0) :
    azim z w w2 w1 = 2 * Real.pi - azim z w w1 w2 := by
  rw [azim_compl hnc1 hnc2, if_neg h]

/-- 三点角分解的换底引理（sum4）：`azim x v u y = azim x v u (pm i) + azim x v (pm i) y`
（给定 `azim x v u (pm i) ≤ azim x v u y`）。 -/
private theorem azim_translate_le (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hin : i < (setOfEdge v V E).ncard) (y : V3)
    (hyncol : ¬ Collinear3 x v y)
    (hle : azim x v u ((sigmaFan x V E v)^[i] u) ≤ azim x v u y) :
    azim x v u y =
      azim x v u ((sigmaFan x V E v)^[i] u) +
        azim x v ((sigmaFan x V E v)^[i] u) y := by
  have hnc_pm : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) := pm_noncollinear hfan hvu hin
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hvx : v ≠ x := (fan_x_ne_v hfan hvu).symm
  exact sum4_azim_fan hvx hncu hnc_pm hyncol hle

/-- 三点角分解（`azim x v u (pm i) + azim x v (pm i) y < 2π` 时，即 sum3
应用；用于方向 `0 < azim x v (pm i) y ⟹ ifAzims i < azim x v u y`）。 -/
private theorem azim_translate_lt (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hin : i < (setOfEdge v V E).ncard) (y : V3)
    (hyncol : ¬ Collinear3 x v y)
    (hlt : azim x v u ((sigmaFan x V E v)^[i] u) +
        azim x v ((sigmaFan x V E v)^[i] u) y < 2 * Real.pi) :
    azim x v u y =
      azim x v u ((sigmaFan x V E v)^[i] u) +
        azim x v ((sigmaFan x V E v)^[i] u) y := by
  have hnc_pm : ¬ Collinear3 x v ((sigmaFan x V E v)^[i] u) := pm_noncollinear hfan hvu hin
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hvx : v ≠ x := (fan_x_ne_v hfan hvu).symm
  exact sum3_azim_fan hvx hncu hnc_pm hyncol hlt

/-- 上界换底（⟹）：`azim x v u y < ifAzims (SUC i)`（配合下界
`ifAzims i < azim x v u y`）⟹ `azim x v (pm i) y < azim x v (pm i) (pm(SUC i))`。
下界保证 sum4 分解适用。 -/
private theorem azim_upper_translate_mp (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u}) (hcard : 1 < (setOfEdge v V E).ncard)
    (hin : i < (setOfEdge v V E).ncard) (y : V3)
    (hyncol : ¬ Collinear3 x v y)
    (hlo : ifAzimsFan x V E v u i < azim x v u y)
    (hhi : azim x v u y < ifAzimsFan x V E v u (i + 1)) :
    azim x v ((sigmaFan x V E v)^[i] u) y <
      azim x v ((sigmaFan x V E v)^[i] u) ((sigmaFan x V E v)^[i + 1] u) := by
  have hle_pm : azim x v u ((sigmaFan x V E v)^[i] u) ≤ azim x v u y := by
    rw [← ifAzimsFan_eq_azim x V E v u i hin]
    exact le_of_lt hlo
  have htrans := azim_translate_le hfan hvu hin y hyncol hle_pm
  by_cases hne_i : i + 1 = (setOfEdge v V E).ncard
  · -- SUC i = CARD：pm(SUC i) = u，ifAzims (SUC i) = 2π
    have hpm : (sigmaFan x V E v)^[i + 1] u = u :=
      order_power_sigmaFan x V E hfan hvu hne_i
    have hθ0 : azim x v u ((sigmaFan x V E v)^[i] u) ≠ 0 := by
      intro hθ
      exact key_lemma_cyclic x V E hfan hvu i (by omega : 0 < i)
        (by omega : i < (setOfEdge v V E).ncard)
        (unique_azim0_point_fan hfan hvu (in2_orbits_fan hfan hvu i) hθ).symm
    have hcomp1 : azim x v ((sigmaFan x V E v)^[i] u) u =
        2 * Real.pi - azim x v u ((sigmaFan x V E v)^[i] u) :=
      azim_compl_ne_zero (z := x) (w := v) (w1 := u)
        (w2 := (sigmaFan x V E v)^[i] u) (fan_not_collinear hfan hvu)
        (pm_noncollinear hfan hvu hin) hθ0
    rw [ifAzimsFan, if_pos hne_i] at hhi
    rw [hpm]
    linarith [htrans, hcomp1, hhi]
  · -- SUC i < CARD：常规链式分解
    have hsuc : i + 1 < (setOfEdge v V E).ncard := by omega
    have hstep := sum_azim_power_sigmaFan hfan hvu hne_u (i + 1) i (by omega) hsuc
    rw [ifAzimsFan_eq_azim x V E v u (i + 1) hsuc] at hhi
    linarith

/-- 无回绕前提：`azim x v u (pm i) + azim x v (pm i) y < 2π`
（由 `azim x v (pm i) y < azim x v (pm i) (pm(SUC i))` 与步长关系给出）。 -/
private theorem azim_no_wrap (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u}) (hcard : 1 < (setOfEdge v V E).ncard)
    (hin : i < (setOfEdge v V E).ncard) (y : V3)
    (hyncol : ¬ Collinear3 x v y)
    (hne : azim x v ((sigmaFan x V E v)^[i] u) y <
      azim x v ((sigmaFan x V E v)^[i] u) ((sigmaFan x V E v)^[i + 1] u)) :
    azim x v u ((sigmaFan x V E v)^[i] u) +
        azim x v ((sigmaFan x V E v)^[i] u) y < 2 * Real.pi := by
  by_cases hne_i : i + 1 = (setOfEdge v V E).ncard
  · -- SUC i = CARD：pm(SUC i) = u，补角给出 ≤ 2π
    have hpm : (sigmaFan x V E v)^[i + 1] u = u :=
      order_power_sigmaFan x V E hfan hvu hne_i
    have hθ0 : azim x v u ((sigmaFan x V E v)^[i] u) ≠ 0 := by
      intro hθ
      exact key_lemma_cyclic x V E hfan hvu i (by omega : 0 < i)
        (by omega : i < (setOfEdge v V E).ncard)
        (unique_azim0_point_fan hfan hvu (in2_orbits_fan hfan hvu i) hθ).symm
    have hcomp1 : azim x v ((sigmaFan x V E v)^[i] u) u =
        2 * Real.pi - azim x v u ((sigmaFan x V E v)^[i] u) :=
      azim_compl_ne_zero (z := x) (w := v) (w1 := u)
        (w2 := (sigmaFan x V E v)^[i] u) (fan_not_collinear hfan hvu)
        (pm_noncollinear hfan hvu hin) hθ0
    rw [hpm] at hne
    linarith [hcomp1, hne]
  · -- SUC i < CARD：步长 = 差，且 pm(SUC i) 的 azim < 2π
    have hsuc : i + 1 < (setOfEdge v V E).ncard := by omega
    have hstep := sum_azim_power_sigmaFan hfan hvu hne_u (i + 1) i (by omega) hsuc
    have hlt2 : azim x v u ((sigmaFan x V E v)^[i + 1] u) < 2 * Real.pi :=
      azim_lt_two_pi x v u ((sigmaFan x V E v)^[i + 1] u)
    linarith [hstep, hlt2, hne]

/-- 上界换底（⟸）：`azim x v (pm i) y < azim x v (pm i) (pm(SUC i))`
⟹ `azim x v u y < ifAzims (SUC i)`。用 sum3 分解（无回绕由
azim_no_wrap 保证）。 -/
private theorem azim_upper_translate_mpr (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hne_u : setOfEdge v V E ≠ {u}) (hcard : 1 < (setOfEdge v V E).ncard)
    (hin : i < (setOfEdge v V E).ncard) (y : V3)
    (hyncol : ¬ Collinear3 x v y)
    (hne : azim x v ((sigmaFan x V E v)^[i] u) y <
      azim x v ((sigmaFan x V E v)^[i] u) ((sigmaFan x V E v)^[i + 1] u)) :
    azim x v u y < ifAzimsFan x V E v u (i + 1) := by
  have hlt_sum := azim_no_wrap hfan hvu hne_u hcard hin y hyncol hne
  have htrans := azim_translate_lt hfan hvu hin y hyncol hlt_sum
  by_cases hne_i : i + 1 = (setOfEdge v V E).ncard
  · -- SUC i = CARD：ifAzims (SUC i) = 2π
    rw [ifAzimsFan, if_pos hne_i]
    linarith [htrans, hlt_sum]
  · -- SUC i < CARD：链式分解
    have hsuc : i + 1 < (setOfEdge v V E).ncard := by omega
    have hstep := sum_azim_power_sigmaFan hfan hvu hne_u (i + 1) i (by omega) hsuc
    rw [ifAzimsFan_eq_azim x V E v u (i + 1) hsuc]
    linarith [htrans, hstep, hne]

/-- HOL topology.hl:1248 `w_dart_eq_wedge3_fan`：w_dart（从 pm i 到
pm(SUC i) 的楔形）= wedge3（if_azims 区间楔形）。核心：两个换底
（下界 `0 < azim (pm i) y ⟺ ifAzims i < azim u y`、上界
`azim (pm i) y < azim (pm i) (pm(SUC i)) ⟺ azim u y < ifAzims (SUC i)`）
由 sum3/sum4/sum_azim_power + ifAzims 定义拼合。 -/
theorem wDart_eq_wedge3_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hin : i < (setOfEdge v V E).ncard)
    (hcard : 1 < (setOfEdge v V E).ncard) :
    wDartFan x V E (x, v, (sigmaFan x V E v)^[i] u, (sigmaFan x V E v)^[i + 1] u)
      = wedge3Fan x V E v u i := by
  have hne_u : setOfEdge v V E ≠ {u} := by
    intro he
    have h1n : (1:ℕ) < (setOfEdge v V E).ncard := hcard
    rw [he] at h1n
    simp at h1n
  rw [wDartFan_of_ncard_gt_one hfan hvu hcard i]
  ext y
  rw [wedge, wedge3Fan]
  constructor
  · -- y ∈ wedge ⟹ y ∈ wedge3
    rintro ⟨hnc, hlo, hhi⟩
    have hyncol : ¬ Collinear3 x v y := hnc
    -- 下界：无回绕（由 hhi 步长保证）⟹ sum3 分解 ⟹ ifAzims i < azim u y
    have hlt_sum := azim_no_wrap hfan hvu hne_u hcard hin y hyncol hhi
    have htrans := azim_translate_lt hfan hvu hin y hyncol hlt_sum
    constructor
    · rw [ifAzimsFan_eq_azim x V E v u i hin]
      linarith [htrans, hlo]
    constructor
    · exact azim_upper_translate_mpr hfan hvu hne_u hcard hin y hyncol hhi
    · exact (mem_complementSet_iff_noncollinear hfan hvu y).mpr hnc
  · -- y ∈ wedge3 ⟹ y ∈ wedge
    rintro ⟨hlo, hhi, hcomp⟩
    have hyncol : ¬ Collinear3 x v y :=
      (mem_complementSet_iff_noncollinear hfan hvu y).mp hcomp
    -- 下界反向：ifAzims i < azim u y ⟹ sum4 分解（hle 前提）
    have hle_pm : azim x v u ((sigmaFan x V E v)^[i] u) ≤ azim x v u y := by
      rw [← ifAzimsFan_eq_azim x V E v u i hin]
      exact le_of_lt hlo
    have htrans := azim_translate_le hfan hvu hin y hyncol hle_pm
    constructor
    · exact hyncol
    constructor
    · rw [ifAzimsFan_eq_azim x V E v u i hin] at hlo
      linarith [htrans, hlo]
    · exact azim_upper_translate_mp hfan hvu hne_u hcard hin y hyncol hlo hhi

/-- HOL topology.hl:1654 `aff_subset_aff_ge`：DISJOINT {x,v} {w} ⟹
aff {x,v} ⊆ aff_ge {x,v} {w}。 -/
theorem aff_subset_aff_ge {x v w : V3} (hdisj : Disjoint ({x, v} : Set V3) {w}) :
    (affineSpan ℝ ({x, v} : Set V3) : Set V3) ⊆ affGe {x, v} {w} := by
  intro y hy
  rw [affine_hull_2_fan] at hy
  obtain ⟨a, b, hab, rfl⟩ := hy
  have hfin : ({x, v} ∪ {w} : Set V3).Finite :=
    ((Set.finite_singleton v).insert x).union (Set.finite_singleton w)
  by_cases hvx : v = x
  · -- 退化情形 v = x：subst 消去 x（全替换为 v），取系数 v↦1、其余↦0
    subst hvx
    have hxw : v ≠ w := Set.disjoint_iff_forall_ne.mp hdisj (Or.inl rfl) rfl
    have h2 : hfin.toFinset = ({v, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    refine ⟨fun z => if z = v then 1 else 0, hfin, ?_, ?_, ?_⟩
    · rw [h2, Finset.sum_insert (Finset.notMem_singleton.mpr hxw), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg (Ne.symm hxw),
        one_smul, zero_smul, add_zero]
      rw [← add_smul, hab, one_smul]
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      simp only [if_neg (Ne.symm hxw), le_refl]
    · rw [h2, Finset.sum_insert (Finset.notMem_singleton.mpr hxw), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg (Ne.symm hxw), add_zero]
  · -- 非退化：取系数 x↦a, v↦b, w↦0
    have hxw : x ≠ w := Set.disjoint_iff_forall_ne.mp hdisj (Or.inl rfl) rfl
    have hvw : v ≠ w := Set.disjoint_iff_forall_ne.mp hdisj (Or.inr rfl) rfl
    have h3 : hfin.toFinset = ({x, v, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hxnotmem : x ∉ ({v, w} : Finset V3) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hvx, hxw⟩
    refine ⟨fun z => if z = x then a else if z = v then b else 0, hfin, ?_, ?_, ?_⟩
    · rw [h3, Finset.sum_insert hxnotmem,
        Finset.sum_insert (Finset.notMem_singleton.mpr hvw), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg hvx, if_neg (Ne.symm hxw),
        if_neg (Ne.symm hvw), zero_smul, add_zero]
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      simp only [if_neg (Ne.symm hxw), if_neg (Ne.symm hvw), le_refl]
    · rw [h3, Finset.sum_insert hxnotmem,
        Finset.sum_insert (Finset.notMem_singleton.mpr hvw), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg hvx, if_neg (Ne.symm hxw),
        if_neg (Ne.symm hvw), add_zero]
      exact hab

/-- 非零 azim 的下界：azim ≥ 0 且 ≠ 0 则 > 0。 -/
private theorem azim_pos_of_ne_zero {x v u w : V3}
    (h : azim x v u w ≠ 0) : 0 < azim x v u w :=
  lt_of_le_of_ne (azim_nonneg x v u w) (Ne.symm h)

/-- HOL topology.hl:1344 `UNION_FAN`：UNIV = aff ∪ ⋃wedge3 ∪ ⋃wedge2。
核心思路：任一点 y，要么在 aff{x,v} 中（共线），要么在某个 wedge3 或 wedge2 中
（非共线时按 azim 角度确定区间）。 -/
theorem UNION_FAN (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (Set.univ : Set V3) =
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∪
      (⋃ i ∈ {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard}, wedge3Fan x V E v u i) ∪
      (⋃ i ∈ {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard}, wedge2Fan x V E v u i) := by
  ext y; simp only [Set.mem_union, Set.mem_iUnion, Set.mem_univ, true_iff]
  have hn_pos : 0 < (setOfEdge v V E).ncard := by
    have hu_soe : u ∈ setOfEdge v V E :=
      (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
    exact Nat.pos_of_ne_zero (fun h =>
      Set.nonempty_iff_ne_empty.mp ⟨u, hu_soe⟩
        ((Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)).mp h))
  by_cases hcoll : Collinear3 x v y
  · exact Or.inl (Or.inl ((collinear3_iff_mem_affineSpan (fan_x_ne_v hfan hvu)).mp hcoll))
  · have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
    -- ifAzims 值在 [0,2π) 中：ifAzims 0 = 0，ifAzims n = 2π
    -- y 的 azim 角落入某个区间
    have hθ0 : 0 ≤ azim x v u y := azim_nonneg x v u y
    have hθ1 : azim x v u y < 2 * Real.pi := azim_lt_two_pi x v u y
    by_cases hθ : azim x v u y = 0
    · -- azim = 0：y 在 ifAzims 0 = 0 的等值面上，属于 wedge2Fan 0
      have hcomp : y ∈ complementSet x v :=
        (mem_complementSet_iff_noncollinear hfan hvu y).mpr hcoll
      -- ifAzimsFan 0 = azim x v u u = 0（因 0 ≠ ncard）
      have hif0 : ifAzimsFan x V E v u 0 = 0 := by
        rw [ifAzimsFan_eq_azim x V E v u 0 hn_pos]
        exact azim_self x v u
      right
      exact ⟨0, ⟨Nat.zero_le _, hn_pos⟩, hif0.trans hθ.symm, hcomp⟩
    · -- azim > 0：找区间
      have hθpos : 0 < azim x v u y := azim_pos_of_ne_zero hθ
      -- Nat.find 找到第一个 ifAzims > azim y 的索引
      have h_exists : ∃ i, i ≤ (setOfEdge v V E).ncard ∧
          ifAzimsFan x V E v u i > azim x v u y := by
        exact ⟨(setOfEdge v V E).ncard, le_refl _,
          by rw [ifAzimsFan, if_pos rfl]; exact hθ1⟩
      let i := Nat.find h_exists
      have hi_bound : i ≤ (setOfEdge v V E).ncard := (Nat.find_spec h_exists).1
      have hi_gt : ifAzimsFan x V E v u i > azim x v u y := (Nat.find_spec h_exists).2
      -- i > 0 因为 ifAzims 0 = 0 ≤ azim
      have hi0 : 0 < i := by
        by_contra hi0
        have h0 := Nat.eq_zero_of_not_pos hi0
        rw [h0] at hi_gt
        have haz0 : azim x v u ((sigmaFan x V E v)^[0] u) = 0 := azim_self x v u
        rw [ifAzimsFan_eq_azim x V E v u 0 hn_pos, haz0] at hi_gt
        exact absurd hi_gt (not_lt_of_ge hθ0)
      have hin : i - 1 < (setOfEdge v V E).ncard := by omega
      -- ifAzims (i-1) ≤ azim < ifAzims i
      have hle_prev : ifAzimsFan x V E v u (i - 1) ≤ azim x v u y := by
        by_contra hgt
        have hlt : azim x v u y < ifAzimsFan x V E v u (i - 1) := lt_of_not_ge hgt
        -- i-1 也满足条件，与 i 的最小性矛盾
        exact absurd ⟨by omega, hlt⟩ (Nat.find_min h_exists (by omega : i - 1 < i))
      -- y 在 complementSet 中（非共线）
      have hcomp : y ∈ complementSet x v :=
        (mem_complementSet_iff_noncollinear hfan hvu y).mpr hcoll
      -- 分情况：azim 恰好等于某个 ifAzims（边界）或在区间内（内部）
      by_cases heq : azim x v u y = ifAzimsFan x V E v u (i - 1)
      · -- 边界情况：azim = ifAzims (i-1)，y 在 wedge2Fan (i-1) 中
        right
        exact ⟨i - 1, ⟨by omega, by omega⟩, heq.symm, hcomp⟩
      · -- 内部情况：ifAzims (i-1) < azim < ifAzims i，y 在 wedge3Fan (i-1) 中
        left; right
        have hhi : azim x v u y < ifAzimsFan x V E v u (i - 1 + 1) := by
          rw [show i - 1 + 1 = i from by omega]
          exact hi_gt
        exact ⟨i - 1, ⟨by omega, by omega⟩,
          lt_of_le_of_ne hle_prev (Ne.symm heq), hhi, hcomp⟩

/-- HOL topology.hl:1670 `eq_set_wdart_fan` 证明内的 CARD = 1 分支
（HOL 第二 DISJ_CASES：ncard = 1 ⟹ soe = {u}、i = 0）：wDartFan 展开到
`UNIV \ aff_ge {x,v} {u}` 分支，wedge3Fan 0 因 ifAzims 0 = 0、ifAzims 1 = 2π
化为 `{y ∈ complementSet | azim ≠ 0}`；两者相等由 AZIM_EQ_0_GE_ALT
（`azim x v u y = 0 ⟺ y ∈ affGe {x,v} {u}`，非共线下）+ aff ⊆ aff_ge 给出。 -/
theorem wDart_eq_wedge3_of_ncard_eq_one (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hcard : (setOfEdge v V E).ncard = 1) :
    wDartFan x V E (x, v, u, sigmaFan x V E v u) = wedge3Fan x V E v u 0 := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hsoe : setOfEdge v V E = {u} := by
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard
    rw [ha, Set.mem_singleton_iff] at hu_soe
    rw [ha, hu_soe]
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hxv : x ≠ v := fan_x_ne_v hfan hvu
  have hif0 : ifAzimsFan x V E v u 0 = 0 := by
    rw [ifAzimsFan, if_neg (by omega : ¬ 0 = (setOfEdge v V E).ncard)]
    exact azim_self x v u
  have hif1 : ifAzimsFan x V E v u (0 + 1) = 2 * Real.pi := by
    rw [ifAzimsFan, if_pos (by omega : 0 + 1 = (setOfEdge v V E).ncard)]
  have hunfold : wDartFan x V E (x, v, u, sigmaFan x V E v u) =
      Set.univ \ affGe {x, v} {u} := by
    rw [wDartFan, if_neg (by omega : ¬ (setOfEdge v V E).ncard > 1), if_pos hsoe]
  have hdisj : Disjoint ({x, v} : Set V3) {u} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he => hncu (collinear3_pair_left he),
      fun he => hncu (collinear3_pair_right he)⟩
  -- AZIM_EQ_0_GE_ALT：非共线下 azim = 0 ⟺ y ∈ affGe
  have key : ∀ y : V3, ¬ Collinear3 x v y →
      (y ∈ affGe {x, v} {u} ↔ azim x v u y = 0) := by
    intro y hyncol
    constructor
    · rintro ⟨f, hfin, hsum, hpos, hone⟩
      have hxu : x ≠ u := fun he => hncu (collinear3_pair_left he.symm)
      have hvu' : v ≠ u := fun he => hncu (collinear3_pair_right he.symm)
      have h3 : hfin.toFinset = ({x, v, u} : Finset V3) := by
        ext z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hxnotmem : x ∉ ({v, u} : Finset V3) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxv, hxu⟩
      rw [h3, Finset.sum_insert hxnotmem,
        Finset.sum_insert (Finset.notMem_singleton.mpr hvu'),
        Finset.sum_singleton] at hsum hone
      -- f u = 0 时 y ∈ aff{x,v}，与非共线矛盾；故 f u > 0，y ∈ affGt
      have hfu0 : f u ≠ 0 := by
        intro h0
        apply hyncol
        rw [collinear3_iff_mem_affineSpan hxv, affine_hull_2_fan]
        exact ⟨f x, f v, by linarith, by rw [hsum, h0, zero_smul, add_zero]⟩
      have hfu : 0 < f u := lt_of_le_of_ne (hpos u (Set.mem_singleton u)) (Ne.symm hfu0)
      have hfx : f x = 1 - f v - f u := by linarith
      have hGt : y ∈ affGt {x, v} {u} :=
        (affGt_pair_iff hxv hxu.symm hvu'.symm).mpr ⟨f u, hfu, f v, by rw [hsum, hfx]; module⟩
      exact (azim_eq_zero_iff_alt hncu hyncol).mpr hGt
    · -- affGt ⊆ affGe（同一组系数，严格正 ⟹ 非负）
      intro h0
      obtain ⟨f, hfin, hsum, hpos, hone⟩ := (azim_eq_zero_iff_alt hncu hyncol).mp h0
      exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩
  rw [hunfold, wedge3Fan, hif0, hif1]
  ext y
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · intro hy
    have hyaff : y ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
      fun hya => hy (aff_subset_aff_ge hdisj hya)
    have hyncol : ¬ Collinear3 x v y :=
      fun hc => hyaff ((collinear3_iff_mem_affineSpan hxv).mp hc)
    have haz : azim x v u y ≠ 0 := fun h0 => hy ((key y hyncol).mpr h0)
    exact ⟨lt_of_le_of_ne (azim_nonneg x v u y) (Ne.symm haz),
      azim_lt_two_pi x v u y, hyaff⟩
  · rintro ⟨hlo, _hhi, hycomp⟩
    have hyncol : ¬ Collinear3 x v y :=
      fun hc => hycomp ((collinear3_iff_mem_affineSpan hxv).mp hc)
    intro hyge
    exact absurd ((key y hyncol).mp hyge) (ne_of_gt hlo)

/-- HOL topology.hl:1670 `eq_set_wdart_fan`：w_dart 集 = wedge3 集。
CARD > 1 时用 wDart_eq_wedge3_fan；CARD = 1（FAN 不排除一度顶点，
HOL 同定理的第二 DISJ_CASES 分支）时用 wDart_eq_wedge3_of_ncard_eq_one。 -/
theorem eq_set_wdart_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (fun w : V3 => wDartFan x V E (x, v, w, sigmaFan x V E v w)) '' {w | {v, w} ∈ E} =
      (fun i : ℕ => wedge3Fan x V E v u i) '' {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard} := by
  have hn_pos : 0 < (setOfEdge v V E).ncard := by
    have hu_soe : u ∈ setOfEdge v V E :=
      (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
    exact Nat.pos_of_ne_zero (fun h =>
      Set.nonempty_iff_ne_empty.mp ⟨u, hu_soe⟩
        ((Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)).mp h))
  by_cases hcard : 1 < (setOfEdge v V E).ncard
  · -- CARD > 1（HOL 第一分支）
    ext y; constructor
    · rintro ⟨w, hwE, rfl⟩
      have hwc : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hwE
      obtain ⟨j, hj, rfl⟩ := iterates_mem_sigmaFan hfan hvu hwc
      refine ⟨j, ⟨Nat.zero_le j, hj⟩, ?_⟩
      show wedge3Fan x V E v u j = wDartFan x V E (x, v, (sigmaFan x V E v)^[j] u,
        sigmaFan x V E v ((sigmaFan x V E v)^[j] u))
      have h := wDart_eq_wedge3_fan hfan hvu hj hcard
      rw [Function.iterate_succ_apply'] at h
      exact h.symm
    · rintro ⟨i, ⟨hi0, hi⟩, rfl⟩
      have hi_mem : (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E :=
        iterates_mem_setOfEdge hfan v u
          ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu) i
      have hwE : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
        (properties_of_setOfEdge_fan x V E v _ hfan).mpr hi_mem
      refine ⟨(sigmaFan x V E v)^[i] u, hwE, ?_⟩
      show wDartFan x V E (x, v, (sigmaFan x V E v)^[i] u,
        sigmaFan x V E v ((sigmaFan x V E v)^[i] u)) = wedge3Fan x V E v u i
      have h := wDart_eq_wedge3_fan hfan hvu hi hcard
      rw [Function.iterate_succ_apply'] at h
      exact h
  · -- CARD = 1（HOL 第二分支：soe = {u}，i = j = 0，w = u）
    have hcard1 : (setOfEdge v V E).ncard = 1 := by omega
    ext y; constructor
    · rintro ⟨w, hwE, rfl⟩
      have hwc : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hwE
      have hu_soe : u ∈ setOfEdge v V E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
      have hsoe : setOfEdge v V E = {u} := by
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard1
        rw [ha, Set.mem_singleton_iff] at hu_soe
        rw [ha, hu_soe]
      rw [hsoe, Set.mem_singleton_iff] at hwc
      subst w
      refine ⟨0, ⟨Nat.zero_le 0, by omega⟩, ?_⟩
      show wedge3Fan x V E v u 0 = wDartFan x V E (x, v, u, sigmaFan x V E v u)
      exact (wDart_eq_wedge3_of_ncard_eq_one hfan hvu hcard1).symm
    · rintro ⟨i, ⟨hi0, hi⟩, rfl⟩
      have hi0' : i = 0 := by omega
      subst hi0'
      refine ⟨u, hvu, ?_⟩
      show wDartFan x V E (x, v, u, sigmaFan x V E v u) = wedge3Fan x V E v u 0
      exact wDart_eq_wedge3_of_ncard_eq_one hfan hvu hcard1

/-- HOL topology.hl:1774 `eq_set_aff_gt`：aff_gt 集 = wedge2 集。
利用 wedge2Fan_eq_affGt_fan（block 9）双包含。 -/
theorem eq_set_aff_gt (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (fun w : V3 => affGt {x, v} {w}) '' {w | {v, w} ∈ E} =
      (fun i : ℕ => wedge2Fan x V E v u i) '' {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard} := by
  ext y; constructor
  · rintro ⟨w, hwE, rfl⟩
    have hwc : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v w hfan).mp hwE
    obtain ⟨j, hj, rfl⟩ := iterates_mem_sigmaFan hfan hvu hwc
    refine ⟨j, ⟨Nat.zero_le j, hj⟩, ?_⟩
    show wedge2Fan x V E v u j = affGt {x, v} {(sigmaFan x V E v)^[j] u}
    exact wedge2Fan_eq_affGt_fan hfan hvu j (Nat.ne_of_lt hj)
  · rintro ⟨i, ⟨hi0, hi⟩, rfl⟩
    have hi_mem : (sigmaFan x V E v)^[i] u ∈ setOfEdge v V E :=
      iterates_mem_setOfEdge hfan v u
        ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu) i
    have hwE : {v, (sigmaFan x V E v)^[i] u} ∈ E :=
      (properties_of_setOfEdge_fan x V E v _ hfan).mpr hi_mem
    refine ⟨(sigmaFan x V E v)^[i] u, hwE, ?_⟩
    show affGt {x, v} {(sigmaFan x V E v)^[i] u} = wedge2Fan x V E v u i
    exact (wedge2Fan_eq_affGt_fan hfan hvu i (Nat.ne_of_lt hi)).symm

/-- HOL topology.hl:1814 `UNION1_FAN`：UNIV = aff ∪ ⋃wDart ∪ ⋃aff_gt。
由 UNION_FAN + eq_set_wdart_fan + eq_set_aff_gt 直接替换。 -/
theorem UNION1_FAN (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (Set.univ : Set V3) =
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∪
      (⋃ w ∈ {w | {v, w} ∈ E},
        wDartFan x V E (x, v, w, sigmaFan x V E v w)) ∪
      (⋃ w ∈ {w | {v, w} ∈ E}, affGt {x, v} {w}) := by
  have h1 := UNION_FAN hfan hvu
  have h2 := eq_set_wdart_fan hfan hvu
  have h3 := eq_set_aff_gt hfan hvu
  have key3 : (⋃ w ∈ {w | {v, w} ∈ E},
        wDartFan x V E (x, v, w, sigmaFan x V E v w)) =
      ⋃ i ∈ {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard}, wedge3Fan x V E v u i := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hy⟩
      have hmem : wDartFan x V E (x, v, w, sigmaFan x V E v w) ∈
          (fun w : V3 => wDartFan x V E (x, v, w, sigmaFan x V E v w)) ''
            {w | {v, w} ∈ E} := ⟨w, hw, rfl⟩
      rw [h2] at hmem
      simp only [Set.mem_image, Set.mem_setOf_eq] at hmem
      obtain ⟨i, hi, hiy⟩ := hmem
      exact ⟨i, hi, hiy ▸ hy⟩
    · rintro ⟨i, hi, hy⟩
      have hmem : wedge3Fan x V E v u i ∈
          (fun i : ℕ => wedge3Fan x V E v u i) ''
            {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard} := ⟨i, hi, rfl⟩
      rw [← h2] at hmem
      simp only [Set.mem_image, Set.mem_setOf_eq] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      exact ⟨w, hw, hwy ▸ hy⟩
  have key2 : (⋃ w ∈ {w | {v, w} ∈ E}, affGt {x, v} {w}) =
      ⋃ i ∈ {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard}, wedge2Fan x V E v u i := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hy⟩
      have hmem : affGt {x, v} {w} ∈ (fun w : V3 => affGt {x, v} {w}) ''
          {w | {v, w} ∈ E} := ⟨w, hw, rfl⟩
      rw [h3] at hmem
      simp only [Set.mem_image, Set.mem_setOf_eq] at hmem
      obtain ⟨i, hi, hiy⟩ := hmem
      exact ⟨i, hi, hiy ▸ hy⟩
    · rintro ⟨i, hi, hy⟩
      have hmem : wedge2Fan x V E v u i ∈
          (fun i : ℕ => wedge2Fan x V E v u i) ''
            {i | 0 ≤ i ∧ i < (setOfEdge v V E).ncard} := ⟨i, hi, rfl⟩
      rw [← h3] at hmem
      simp only [Set.mem_image, Set.mem_setOf_eq] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      exact ⟨w, hw, hwy ▸ hy⟩
  rw [h1, key3, key2]

/-- HOL topology.hl:1944 `disjiont1_cor6dot1`：wedge3 ∩ aff = ∅
（complementSet 与 affineSpan 不交的直接推论）。 -/
theorem disjoint_wedge3_aff (x v u : V3) (V : Set V3) (E : Set (Set V3))
    (i : ℕ) :
    wedge3Fan x V E v u i ∩ affineSpan ℝ {x, v} = ∅ := by
  ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, _, hcomp⟩, _⟩
  exact hcomp ‹y ∈ affineSpan ℝ {x, v}›

/-- HOL topology.hl:1952 `disjoint_fan1`：w_dart ∩ aff = ∅。
按 wDartFan 定义分四支：CARD > 1 时 wedge 含非共线条件；soe = {w} 时
UNIV \ aff_ge 与 aff 不交（aff ⊆ aff_ge）；soe = ∅ 与 ∅ 两支平凡。 -/
theorem disjoint_fan1 (hfan : FAN x V E) (hvw : {v, w} ∈ E) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) = ∅ := by
  have hncw : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  rw [wDartFan]
  by_cases hcard : 1 < (setOfEdge v V E).ncard
  · -- wedge x v w (σw)：成员非共线，与 aff{x,v} 不交
    rw [if_pos hcard]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hy hyaff
    exact (mem_complementSet_iff_noncollinear hfan hvw y).mpr hy.1 hyaff
  · rw [if_neg hcard]
    by_cases hsoe : setOfEdge v V E = {w}
    · -- UNIV \ aff_ge {x,v} {w}：aff{x,v} ⊆ aff_ge，故不交
      rw [if_pos hsoe]
      have hdisj : Disjoint ({x, v} : Set V3) {w} := by
        rw [Set.disjoint_singleton_right]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun he => hncw (collinear3_pair_left he),
          fun he => hncw (collinear3_pair_right he)⟩
      ext y
      simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_inter_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hyge hyaff
      exact hyge (aff_subset_aff_ge hdisj hyaff)
    · rw [if_neg hsoe]
      by_cases hsoe0 : setOfEdge v V E = ∅
      · -- UNIV \ aff：自身不交
        rw [if_pos hsoe0]
        ext y
        simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_inter_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact h1 h2
      · rw [if_neg hsoe0, Set.empty_inter]

/-- aff_gt ⊆ aff_ge：同一组系数，严格正 ⟹ 非负。 -/
private theorem affGt_subset_affGe (s t : Set V3) : affGt s t ⊆ affGe s t := by
  rintro y ⟨f, hfin, hsum, hpos, hone⟩
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- `disjoint_set_fan` 的 w = w1 自交情形：w_dart(x,v,w,σw) 与
aff_gt {x,v} {w} 不交（CARD > 1 时 wedge3 0 与 wedge2 0 的 azim 下界
严格分离；CARD = 1 时 w_dart = UNIV \ aff_ge 而 aff_gt ⊆ aff_ge）。 -/
private theorem wDart_self_inter_affGt (hfan : FAN x V E) (hvw : {v, w} ∈ E) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩ affGt {x, v} {w} = ∅ := by
  have hEw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hvw
  have hn_pos : 0 < (setOfEdge v V E).ncard :=
    Nat.pos_of_ne_zero (fun h =>
      Set.nonempty_iff_ne_empty.mp ⟨w, hEw⟩
        ((Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)).mp h))
  by_cases hcard : 1 < (setOfEdge v V E).ncard
  · have hwDart0 := wDart_eq_wedge3_fan hfan hvw hn_pos hcard
    rw [Function.iterate_succ_apply', Function.iterate_zero_apply] at hwDart0
    have hgt0 : affGt {x, v} {w} = wedge2Fan x V E v w 0 := by
      have h := (wedge2Fan_eq_affGt_fan hfan hvw 0
        (by omega : 0 ≠ (setOfEdge v V E).ncard)).symm
      rwa [Function.iterate_zero_apply] at h
    rw [hwDart0, hgt0]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hlo, -, -⟩ ⟨hz, -⟩
    linarith
  · -- CARD = 1：soe = {w}，wDart = UNIV \ aff_ge
    have hcard1 : (setOfEdge v V E).ncard = 1 := by omega
    have hsoe : setOfEdge v V E = {w} := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard1
      rw [ha, Set.mem_singleton_iff] at hEw
      rw [ha, hEw]
    have hunfold : wDartFan x V E (x, v, w, sigmaFan x V E v w) =
        Set.univ \ affGe {x, v} {w} := by
      rw [wDartFan, if_neg (by omega : ¬ (setOfEdge v V E).ncard > 1), if_pos hsoe]
    rw [hunfold]
    ext y
    simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_inter_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hyge hygt
    exact hyge (affGt_subset_affGe _ _ hygt)

/-- HOL topology.hl:1853 `disjoint_set_fan` 的 w ≠ w1 情形（block 13 原
`disjoint_set_fan`）：wedge3 与 wedge2 的 azim 区间严格分离。 -/
private theorem disjoint_set_fan_of_ne (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hvw1 : {v, w1} ∈ E) (hw1ne : w ≠ w1) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩ affGt {x, v} {w1} = ∅ := by
  have hEw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hvw
  have hEw1 : w1 ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w1 hfan).mp hvw1
  obtain ⟨j, hj, rfl⟩ := iterates_mem_sigmaFan hfan hvw hEw1
  have hne_j0 : j ≠ 0 := fun he => hw1ne (by simp [he])
  have hcard : 1 < (setOfEdge v V E).ncard := by
    by_contra hle
    push_neg at hle
    have h01 : (setOfEdge v V E).ncard = 0 ∨ (setOfEdge v V E).ncard = 1 := by omega
    rcases h01 with h0 | h1
    · rw [Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)] at h0
      rw [h0] at hEw
      exact (Set.mem_empty_iff_false w).mp hEw
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      rw [ha, Set.mem_singleton_iff] at hEw hEw1
      exact hw1ne (hEw.trans hEw1.symm)
  have hne_u : setOfEdge v V E ≠ {w} := by
    intro he; rw [he] at hcard; simp at hcard
  have h0lt : (0 : ℕ) < (setOfEdge v V E).ncard := by omega
  have hwDart0 := wDart_eq_wedge3_fan hfan hvw h0lt hcard
  rw [Function.iterate_succ_apply', Function.iterate_zero_apply] at hwDart0
  have haffgtj : affGt {x, v} {(sigmaFan x V E v)^[j] w} = wedge2Fan x V E v w j :=
    (wedge2Fan_eq_affGt_fan hfan hvw j (by omega : j ≠ (setOfEdge v V E).ncard)).symm
  rw [hwDart0, haffgtj]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_hlo, hhi, -⟩, hweq, -⟩
  have hhi1 : azim x v w y < ifAzimsFan x V E v w 1 := hhi
  by_cases hj1 : j = 1
  · subst hj1; linarith
  · have h1j : 1 < j := by omega
    have hstr := azim_lt_power_sigmaFan hfan hvw hne_u j 1 h1j hj
    rw [← ifAzimsFan_eq_azim x V E v w 1 (by omega : 1 < (setOfEdge v V E).ncard),
      ← ifAzimsFan_eq_azim x V E v w j hj] at hstr
    linarith

/-- HOL topology.hl:1853 `disjoint_set_fan`：w_dart ∩ aff_gt = ∅。
HOL 原文无 `w ≠ w1` 前提：w ≠ w1 时由 disjoint_set_fan_of_ne（azim 区间
严格分离），w = w1 时由 wDart_self_inter_affGt 给出。 -/
theorem disjoint_set_fan (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hvw1 : {v, w1} ∈ E) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩ affGt {x, v} {w1} = ∅ := by
  by_cases hww1 : w = w1
  · subst hww1
    exact wDart_self_inter_affGt hfan hvw
  · exact disjoint_set_fan_of_ne hfan hvw hvw1 hww1

/-- HOL topology.hl:1977 `disjoint_fan2`：不同边的 w_dart 互不相交。
（wedge3Fan 的 azim 区间严格分离）。 -/
theorem disjoint_fan2 (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hvw1 : {v, w1} ∈ E) (hw1ne : w ≠ w1) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩
    wDartFan x V E (x, v, w1, sigmaFan x V E v w1) = ∅ := by
  have hEw : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hvw
  have hEw1 : w1 ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w1 hfan).mp hvw1
  obtain ⟨j, hj, rfl⟩ := iterates_mem_sigmaFan hfan hvw hEw1
  have hne_j0 : j ≠ 0 := fun he => hw1ne (by simp [he])
  have hcard : 1 < (setOfEdge v V E).ncard := by
    by_contra hle
    push_neg at hle
    have h01 : (setOfEdge v V E).ncard = 0 ∨ (setOfEdge v V E).ncard = 1 := by omega
    rcases h01 with h0 | h1
    · rw [Set.ncard_eq_zero (remark_finite_fan1 v V E hfan.2.2.1.1)] at h0
      rw [h0] at hEw
      exact (Set.mem_empty_iff_false w).mp hEw
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      rw [ha, Set.mem_singleton_iff] at hEw hEw1
      exact hw1ne (hEw.trans hEw1.symm)
  have hne_u : setOfEdge v V E ≠ {w} := by
    intro he; rw [he] at hcard; simp at hcard
  have h0lt : (0 : ℕ) < (setOfEdge v V E).ncard := by omega
  have hwDart0 := wDart_eq_wedge3_fan hfan hvw h0lt hcard
  rw [Function.iterate_succ_apply', Function.iterate_zero_apply] at hwDart0
  have hwDartj := wDart_eq_wedge3_fan hfan hvw hj hcard
  rw [Function.iterate_succ_apply'] at hwDartj
  rw [hwDart0, hwDartj]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_hlo, hhi, -⟩, ⟨hloj, -, -⟩⟩
  have hhi1 : azim x v w y < ifAzimsFan x V E v w 1 := hhi
  have h1j : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hne_j0
  have hle1j : ifAzimsFan x V E v w 1 ≤ ifAzimsFan x V E v w j := by
    rcases Nat.eq_or_lt_of_le h1j with h1 | h1
    · rw [h1]
    · have hstr := azim_lt_power_sigmaFan hfan hvw hne_u j 1 h1 hj
      rw [← ifAzimsFan_eq_azim x V E v w 1 (by omega : 1 < (setOfEdge v V E).ncard),
        ← ifAzimsFan_eq_azim x V E v w j hj] at hstr
      exact le_of_lt hstr
  linarith

/-! ## disjoint 系列余部与 VBTIKLP（topology.hl:2033–2288）

disjoint_fan3（aff ∩ aff_gt 不交）、remark3_fan（aff_gt 两两不交）、
VBTIKLP（UNION1 + 不交性打包）、disjiont_union_fan、
aff_ge_subset_aff_gt_union_aff、IBZWFFH（w_dart ∩ aff_ge = ∅）与
aff_ge_inter_aff_ge（扇形 = 两个半平面之交）。前置：AFF_GE_2_1 /
AFF_GE_1_2 的三点组合刻画（成员形式）。 -/

/-- HOL fan.hl:580 `AFF_GE_2_1`（成员形式）：y ∈ aff_ge {x,v} {w} ⟺
三点组合（仅 w 系数非负）。HOL 前提仅 DISJOINT {x,v} {w}（给出
x≠w、v≠w），此处另取 x ≠ v 以展开三点和（HOL 由 AFF_TAC 内部处理
x = v 退化）。 -/
theorem mem_affGe_pair {x v w : V3} (hdisj : Disjoint ({x, v} : Set V3) {w})
    (hxv : x ≠ v) {y : V3} :
    y ∈ affGe {x, v} {w} ↔
      ∃ t1 t2 t3 : ℝ, 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • w := by
  have hxw : x ≠ w := Set.disjoint_iff_forall_ne.mp hdisj (Or.inl rfl) rfl
  have hvw' : v ≠ w := Set.disjoint_iff_forall_ne.mp hdisj (Or.inr rfl) rfl
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    have h3 : hfin.toFinset = ({x, v, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hxnotmem : x ∉ ({v, w} : Finset V3) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxv, hxw⟩
    rw [h3, Finset.sum_insert hxnotmem,
      Finset.sum_insert (Finset.notMem_singleton.mpr hvw'),
      Finset.sum_singleton] at hsum hone
    exact ⟨f x, f v, f w, hpos w (Set.mem_singleton w), by linarith,
      by rw [hsum]; module⟩
  · rintro ⟨t1, t2, t3, ht3, hsum, hy⟩
    have hfin : ({x, v} ∪ {w} : Set V3).Finite :=
      ((Set.finite_singleton v).insert x).union (Set.finite_singleton w)
    have h3 : hfin.toFinset = ({x, v, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hxnotmem : x ∉ ({v, w} : Finset V3) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxv, hxw⟩
    rw [show t1 = 1 - t2 - t3 from by linarith] at hy
    refine ⟨fun z => if z = w then t3 else if z = v then t2 else 1 - t2 - t3,
      hfin, ?_, ?_, ?_⟩
    · rw [h3, Finset.sum_insert hxnotmem,
        Finset.sum_insert (Finset.notMem_singleton.mpr hvw'), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg hxv, if_neg hxw, if_neg hvw']
      rw [hy]; module
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      simp only [eq_self_iff_true, if_true]
      exact ht3
    · rw [h3, Finset.sum_insert hxnotmem,
        Finset.sum_insert (Finset.notMem_singleton.mpr hvw'), Finset.sum_singleton]
      simp only [eq_self_iff_true, if_true, if_neg hxv, if_neg hxw, if_neg hvw']
      ring

/-- HOL fan.hl:590 `AFF_GE_1_2`（成员形式）：y ∈ aff_ge {x} {v,w} ⟺
三点组合（v、w 系数非负）。HOL 前提仅 DISJOINT {x} {v,w}，此处另取
v ≠ w（HOL 由 AFF_TAC 内部处理 v = w 退化）。 -/
theorem mem_affGe_singleton_pair {x v w : V3}
    (hdisj : Disjoint ({x} : Set V3) {v, w}) (hvw' : v ≠ w) {y : V3} :
    y ∈ affGe {x} {v, w} ↔
      ∃ t1 t2 t3 : ℝ, 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • w := by
  have hxv : x ≠ v := Set.disjoint_iff_forall_ne.mp hdisj rfl (Or.inl rfl)
  have hxw : x ≠ w := Set.disjoint_iff_forall_ne.mp hdisj rfl (Or.inr rfl)
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    have h3 : hfin.toFinset = ({x, v, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      try tauto
    have hxnotmem : x ∉ ({v, w} : Finset V3) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxv, hxw⟩
    rw [h3, Finset.sum_insert hxnotmem,
      Finset.sum_insert (Finset.notMem_singleton.mpr hvw'),
      Finset.sum_singleton] at hsum hone
    exact ⟨f x, f v, f w, hpos v (Set.mem_insert v {w}),
      hpos w (Set.mem_insert_of_mem v (Set.mem_singleton w)), by linarith,
      by rw [hsum]; module⟩
  · rintro ⟨t1, t2, t3, ht2, ht3, hsum, hy⟩
    rw [show t1 = 1 - t2 - t3 from by linarith] at hy
    exact Affsign.of_triple t2 t3 ht2 ht3 hy hxv hxw hvw'

/-- HOL topology.hl:2033 `disjoint_fan3`：aff{x,v} ∩ aff_gt {x,v} {w} = ∅。
aff 与 AFF_GT_2_1 两式相减得 t3•w = 仿射组合，t3 > 0 缩放后
w ∈ aff{x,v}，与 ¬collinear 矛盾。 -/
theorem disjoint_fan3 (hfan : FAN x V E) (hvw : {v, w} ∈ E) :
    (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∩ affGt {x, v} {w} = ∅ := by
  have hncw : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hxv : x ≠ v := fan_x_ne_v hfan hvw
  have hxw : x ≠ w := fun he => hncw (collinear3_pair_left he.symm)
  have hvw' : v ≠ w := fun he => hncw (collinear3_pair_right he.symm)
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hyaff hygt
  rw [affine_hull_2_fan] at hyaff
  obtain ⟨t1, t2, ht, rfl⟩ := hyaff
  rw [affGt_pair_iff hxv hxw.symm hvw'.symm] at hygt
  obtain ⟨c, hc, h, hy⟩ := hygt
  -- c • (w - x) = (t1 - 1 + h) • x + (t2 - h) • v
  have h1 : c • (w - x) = (t1 - 1 + h) • x + (t2 - h) • v := by
    have h2 : c • (w - x) = t1 • x + t2 • v - x - h • (v - x) := by
      rw [hy]; module
    rw [h2]; module
  have hmem : w ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
    rw [affine_hull_2_fan]
    have hc' : c ≠ 0 := ne_of_gt hc
    refine ⟨1 + c⁻¹ * (t1 - 1 + h), c⁻¹ * (t2 - h), ?_, ?_⟩
    · have hsum : t1 - 1 + h + (t2 - h) = 0 := by linarith
      linear_combination c⁻¹ * hsum
    · have h3 : w = x + c⁻¹ • (c • (w - x)) := by
        rw [inv_smul_smul₀ hc']; module
      rw [h3, h1]; module
  exact hncw ((collinear3_iff_mem_affineSpan hxv).mpr hmem)

/-- HOL topology.hl:2072 `remark3_fan`：不同边的 aff_gt 互不相交
（w1 = σ^i w，i > 0 时两侧化为 wedge2Fan 0 与 wedge2Fan i，交成员给
azim x v w w1 = 0，UNIQUE_AZIM_0_POINT_FAN 得 w = w1，矛盾）。 -/
theorem remark3_fan (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hvw1 : {v, w1} ∈ E) (hww1 : w ≠ w1) :
    affGt {x, v} {w} ∩ affGt {x, v} {w1} = ∅ := by
  have hEw1 : w1 ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w1 hfan).mp hvw1
  obtain ⟨i, hi, rfl⟩ := iterates_mem_sigmaFan hfan hvw hEw1
  have hne_i0 : i ≠ 0 := fun he => hww1 (by simp [he])
  have hn_pos : 0 < (setOfEdge v V E).ncard := by omega
  have hgt0 : affGt {x, v} {w} = wedge2Fan x V E v w 0 := by
    have h := (wedge2Fan_eq_affGt_fan hfan hvw 0
      (by omega : 0 ≠ (setOfEdge v V E).ncard)).symm
    rwa [Function.iterate_zero_apply] at h
  have hgti : affGt {x, v} {(sigmaFan x V E v)^[i] w} = wedge2Fan x V E v w i :=
    (wedge2Fan_eq_affGt_fan hfan hvw i (Nat.ne_of_lt hi)).symm
  rw [hgt0, hgti]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hz0, -⟩ ⟨hzi, -⟩
  have haz0 : azim x v w ((sigmaFan x V E v)^[0] w) = 0 := azim_self x v w
  rw [ifAzimsFan_eq_azim x V E v w 0 hn_pos, haz0] at hz0
  rw [ifAzimsFan_eq_azim x V E v w i hi] at hzi
  have hazim : azim x v w ((sigmaFan x V E v)^[i] w) = 0 := hzi.trans hz0.symm
  exact hww1 (unique_azim0_point_fan hfan hvw hvw1 hazim)

/-- HOL topology.hl:2113 `VBTIKLP`：UNION1_FAN 与全部不交性的合取打包。 -/
theorem VBTIKLP (hfan : FAN x V E) :
    (∀ v u : V3, {v, u} ∈ E →
      (Set.univ : Set V3) =
        (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∪
        (⋃ w ∈ {w | {v, w} ∈ E},
          wDartFan x V E (x, v, w, sigmaFan x V E v w)) ∪
        (⋃ w ∈ {w | {v, w} ∈ E}, affGt {x, v} {w})) ∧
    (∀ v w : V3, {v, w} ∈ E →
      wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩
        (affineSpan ℝ ({x, v} : Set V3) : Set V3) = ∅) ∧
    (∀ v w w1 : V3, {v, w} ∈ E → {v, w1} ∈ E →
      wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩ affGt {x, v} {w1} = ∅) ∧
    (∀ v w w1 : V3, {v, w} ∈ E → {v, w1} ∈ E → w ≠ w1 →
      wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩
      wDartFan x V E (x, v, w1, sigmaFan x V E v w1) = ∅) ∧
    (∀ v w w1 : V3, {v, w} ∈ E → {v, w1} ∈ E → w ≠ w1 →
      affGt {x, v} {w} ∩ affGt {x, v} {w1} = ∅) ∧
    (∀ v w : V3, {v, w} ∈ E →
      (affineSpan ℝ ({x, v} : Set V3) : Set V3) ∩ affGt {x, v} {w} = ∅) :=
  ⟨fun v u h => UNION1_FAN hfan h,
   fun v w h => disjoint_fan1 hfan h,
   fun v w w1 h h1 => disjoint_set_fan hfan h h1,
   fun v w w1 h h1 hne => disjoint_fan2 hfan h h1 hne,
   fun v w w1 h h1 hne => remark3_fan hfan h h1 hne,
   fun v w h => disjoint_fan3 hfan h⟩

/-- HOL topology.hl:2155 `disjiont_union_fan`：w_dart ∩ (aff ∪ aff_gt) = ∅
（UNION_OVER_INTER + disjoint_set_fan + disjoint_fan1）。 -/
theorem disjiont_union_fan (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hvw1 : {v, w1} ∈ E) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩
      ((affineSpan ℝ ({x, v} : Set V3) : Set V3) ∪ affGt {x, v} {w1}) = ∅ := by
  rw [Set.inter_union_distrib_left, disjoint_set_fan hfan hvw hvw1,
    disjoint_fan1 hfan hvw, Set.union_empty]

/-- HOL topology.hl:2167 `aff_ge_subset_aff_gt_union_aff`：
aff_ge {x} {v,w} ⊆ aff_gt {x,v} {w} ∪ aff{x,v}
（t3 = 0 时落入 aff，0 < t3 时落入 aff_gt）。 -/
theorem aff_ge_subset_aff_gt_union_aff (hfan : FAN x V E) (hvw : {v, w} ∈ E) :
    affGe {x} {v, w} ⊆
      affGt {x, v} {w} ∪ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
  have hncw : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hxv : x ≠ v := fan_x_ne_v hfan hvw
  have hxw : x ≠ w := fun he => hncw (collinear3_pair_left he.symm)
  have hvw' : v ≠ w := fun he => hncw (collinear3_pair_right he.symm)
  have hdisj : Disjoint ({x} : Set V3) {v, w} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  intro y hy
  rw [mem_affGe_singleton_pair hdisj hvw'] at hy
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hy⟩ := hy
  by_cases ht3' : t3 = 0
  · -- t3 = 0：y ∈ aff{x,v}
    right
    rw [affine_hull_2_fan]
    exact ⟨t1, t2, by linarith, by rw [hy, ht3', zero_smul, add_zero]⟩
  · -- 0 < t3：y ∈ aff_gt {x,v} {w}
    left
    have ht3pos : 0 < t3 := lt_of_le_of_ne ht3 (Ne.symm ht3')
    rw [affGt_pair_iff hxv hxw.symm hvw'.symm]
    exact ⟨t3, ht3pos, t2, by
      rw [hy, show t1 = 1 - t2 - t3 from by linarith]; module⟩

/-- HOL topology.hl:2205 `IBZWFFH`：w_dart ∩ aff_ge {x} {v,w1} = ∅
（aff_ge ⊆ aff_gt ∪ aff 与 disjiont_union_fan 的推论）。 -/
theorem IBZWFFH (hfan : FAN x V E) (hvw : {v, w} ∈ E) (hvw1 : {v, w1} ∈ E) :
    wDartFan x V E (x, v, w, sigmaFan x V E v w) ∩ affGe {x} {v, w1} = ∅ := by
  have hsub := aff_ge_subset_aff_gt_union_aff hfan hvw1
  have hdis := disjiont_union_fan hfan hvw hvw1
  rw [Set.union_comm] at hsub
  exact Set.eq_empty_of_subset_empty
    ((Set.inter_subset_inter_right _ hsub).trans hdis.subset)

/-- HOL topology.hl:2227 `aff_ge_inter_aff_ge`：¬collinear {x,v,w} 时
aff_ge {x} {v,w} = aff_ge {x,v} {w} ∩ aff_ge {x,w} {v}。
反向：两式相减得 (t3 - t2')•w = 仿射组合；t3 ≠ t2' 时缩放给出
w ∈ aff{x,v}，与 ¬collinear 矛盾，故 t3 = t2'，直接读出三点组合。 -/
theorem aff_ge_inter_aff_ge {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    affGe {x} {v, w} = affGe {x, v} {w} ∩ affGe {x, w} {v} := by
  have hxv : x ≠ v := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w)
    he.symm)
  have hxw : x ≠ w := fun he => hnc (collinear3_pair_left he.symm)
  have hvw' : v ≠ w := fun he => hnc (collinear3_pair_right he.symm)
  have hdisj1 : Disjoint ({x} : Set V3) {v, w} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  have hdisj2 : Disjoint ({x, v} : Set V3) {w} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he => hnc (collinear3_pair_left he),
      fun he => hnc (collinear3_pair_right he)⟩
  have hdisj3 : Disjoint ({x, w} : Set V3) {v} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) he),
      fun he => hnc (collinear3_pair_right he.symm)⟩
  ext y
  constructor
  · intro hy
    rw [mem_affGe_singleton_pair hdisj1 hvw'] at hy
    obtain ⟨t1, t2, t3, ht2, ht3, hsum, hy⟩ := hy
    constructor
    · rw [mem_affGe_pair hdisj2 hxv]
      exact ⟨t1, t2, t3, ht3, hsum, hy⟩
    · rw [mem_affGe_pair hdisj3 hxw]
      exact ⟨t1, t3, t2, ht2, by linarith, by rw [hy]; module⟩
  · rintro ⟨hy1, hy2⟩
    rw [mem_affGe_pair hdisj2 hxv] at hy1
    rw [mem_affGe_pair hdisj3 hxw] at hy2
    obtain ⟨t1, t2, t3, ht3, hsum1, hy1⟩ := hy1
    obtain ⟨t1', t2', t3', ht3', hsum2, hy2⟩ := hy2
    -- 两式相减：(t3 - t2')•w = (t1' - t1)•x + (t3' - t2)•v
    have hsub : (t3 - t2') • w = (t1' - t1) • x + (t3' - t2) • v := by
      have h12 : t1 • x + t2 • v + t3 • w = t1' • x + t2' • w + t3' • v := by
        rw [← hy1, ← hy2]
      calc (t3 - t2') • w
          = (t1 • x + t2 • v + t3 • w) - (t1 • x + t2 • v + t2' • w) := by module
        _ = (t1' • x + t2' • w + t3' • v) - (t1 • x + t2 • v + t2' • w) := by
          rw [h12]
        _ = (t1' - t1) • x + (t3' - t2) • v := by module
    by_cases hz : t3 - t2' = 0
    · -- t3 = t2'：y 的三点组合由第二式系数读出
      -- （0 ≤ t3' 来自第二式，0 ≤ t2' = t3 来自第一式）
      rw [mem_affGe_singleton_pair hdisj1 hvw']
      have ht3eq : t3 = t2' := sub_eq_zero.mp hz
      exact ⟨t1', t3', t2', ht3', by linarith, by linarith, by rw [hy2]; module⟩
    · -- t3 ≠ t2'：w ∈ aff{x,v}，与 ¬collinear 矛盾
      exfalso
      have hwmem : w ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
        rw [affine_hull_2_fan]
        refine ⟨(t3 - t2')⁻¹ * (t1' - t1), (t3 - t2')⁻¹ * (t3' - t2), ?_, ?_⟩
        · have hsum3 : (t1' - t1) + (t3' - t2) = t3 - t2' := by linarith
          rw [← mul_add, hsum3, inv_mul_cancel₀ hz]
        · have h4 : w = (t3 - t2')⁻¹ • ((t3 - t2') • w) :=
            (inv_smul_smul₀ hz w).symm
          rw [h4, hsub]; module
      exact hnc ((collinear3_iff_mem_affineSpan hxv).mpr hwmem)

/-! ## rcone 与 e-标架（topology.hl:2289–2534；fan.hl:1133–1260）

rcone_fan 定义；e1/e2/e3_fan 标架（fan.hl，exp_aff_ge_by_dot 的载体）；
aff_ge 的点积刻画（exp_aff_ge_by_dot / exp_aff_ge_by_dot_1_1）与闭性
（closed_aff_ge_2_1 / closed_aff_ge_1_2 / closed_halfline_fan）。 -/

/-- HOL topology.hl:2289 `rcone_fan`。 -/
def rconeFan (x v : V3) (h : ℝ) : Set V3 :=
  {y | (y - x) ⬝ᵥ (v - x) > dist y x * dist v x * h}

/-- V3 上的叉积（Pi 侧 `crossProduct` 的提升；HOL `cross`）。 -/
private noncomputable def cross3 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))

/-- HOL fan.hl:1133 `e3_fan`：v - x 方向的单位向量。 -/
noncomputable def e3Fan (x v u : V3) : V3 := (‖v - x‖⁻¹ : ℝ) • (v - x)

/-- HOL fan.hl:1138 `e2_fan`：(u-x) 垂直于 e3 的分量方向的单位向量。 -/
noncomputable def e2Fan (x v u : V3) : V3 :=
  (‖cross3 (e3Fan x v u) (u - x)‖⁻¹ : ℝ) • cross3 (e3Fan x v u) (u - x)

/-- HOL fan.hl:1140 `e1_fan`。 -/
noncomputable def e1Fan (x v u : V3) : V3 := cross3 (e2Fan x v u) (e3Fan x v u)

private theorem coe_cross3 (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) :=
  coe_toLp _

private theorem dot_coe (a b : V3) :
    (a : Fin 3 → ℝ) ⬝ᵥ (b : Fin 3 → ℝ) = a ⬝ᵥ b := by
  rw [← dot_toLp, WithLp.toLp_ofLp]

private theorem coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem crossProduct_smul_left (t : ℝ) (p r : Fin 3 → ℝ) :
    crossProduct (t • p) r = t • crossProduct p r := by
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply]

private theorem coe_add (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem toLp_smul (t : ℝ) (p : Fin 3 → ℝ) :
    (WithLp.toLp 2 (t • p) : V3) = t • (WithLp.toLp 2 p : V3) := by
  rw [show t • (WithLp.toLp 2 p : V3) =
      WithLp.toLp 2 ((t • (WithLp.toLp 2 p : V3) : Fin 3 → ℝ)) from
    (WithLp.toLp_ofLp 2 _).symm]

private theorem toLp_sub (p q : Fin 3 → ℝ) :
    (WithLp.toLp 2 (p - q) : V3) =
      (WithLp.toLp 2 p : V3) - (WithLp.toLp 2 q : V3) := by
  rw [show (WithLp.toLp 2 p : V3) - (WithLp.toLp 2 q : V3) =
      WithLp.toLp 2 (((WithLp.toLp 2 p : V3) - (WithLp.toLp 2 q : V3) : Fin 3 → ℝ)) from
    (WithLp.toLp_ofLp 2 _).symm]

/-- V3 侧 dot 代数（Pi 侧 dotProduct 引理的 term-mode 转接；V3 的 `⬝ᵥ`
实例与 Pi 实例对 rw 而言形式不同，右侧带 • 的场合需先用 coe_smul 归一）。 -/
private theorem smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem add_dot (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem sub_dot (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_sub (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem zero_dot (a : V3) : (0 : V3) ⬝ᵥ a = 0 :=
  zero_dotProduct (a : Fin 3 → ℝ)

private theorem dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem cross3_smul_left (t : ℝ) (a b : V3) :
    cross3 (t • a) b = t • cross3 a b := by
  rw [cross3, cross3, coe_smul, crossProduct_smul_left, toLp_smul]

private theorem cross3_dot_left (a b : V3) : a ⬝ᵥ cross3 a b = 0 := by
  rw [cross3, dotProduct_comm, dot_toLp, dotProduct_comm, triple_product_permutation]
  exact dot_cross_self _ _

private theorem cross3_dot_right (a b : V3) : b ⬝ᵥ cross3 a b = 0 := by
  rw [cross3, dotProduct_comm, dot_toLp, dotProduct_comm]
  exact dot_cross_self _ _

private theorem cross3_cross3 (a b c : V3) :
    cross3 (cross3 a b) c = ((a : Fin 3 → ℝ) ⬝ᵥ (c : Fin 3 → ℝ)) • b -
      ((b : Fin 3 → ℝ) ⬝ᵥ (c : Fin 3 → ℝ)) • a := by
  rw [cross3, cross3, coe_toLp, cross_cross_eq_smul_sub_smul, toLp_sub, toLp_smul,
    toLp_smul, WithLp.toLp_ofLp, WithLp.toLp_ofLp]

/-- HOL fan.hl:1152 `e3_is_normal_fan`。 -/
theorem e3Fan_dot_self (hvx : v ≠ x) (u : V3) : e3Fan x v u ⬝ᵥ e3Fan x v u = 1 := by
  have h1 : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  rw [e3Fan, coe_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← norm_sq_eq_dot, smul_eq_mul]
  have h2 : ‖v - x‖⁻¹ * (‖v - x‖⁻¹ * ‖v - x‖ ^ 2) = 1 := by field_simp [h1]
  exact h2

/-- e3 × (u-x) ≠ 0（非共线 ⟹ (u-x) 有垂直于 (v-x) 的分量）。 -/
theorem e3Fan_cross_ux_ne_zero (hnc : ¬ Collinear3 x v u) :
    cross3 (e3Fan x v u) (u - x) ≠ 0 := by
  intro hzero
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  -- |cross|² = |ux|² - (e3·ux)² = 0 ⟹ ux = t•e3 ⟹ 共线
  have hsq : (u - x) ⬝ᵥ (u - x) =
      ((u - x) ⬝ᵥ e3Fan x v u) * ((u - x) ⬝ᵥ e3Fan x v u) := by
    have h1 : cross3 (e3Fan x v u) (u - x) ⬝ᵥ cross3 (e3Fan x v u) (u - x) = 0 := by
      rw [hzero, coe_zero, zero_dotProduct]
    rw [cross3, dot_toLp, coe_toLp, cross_dot_cross, dot_coe, dot_coe, dot_coe, dot_coe,
      e3Fan_dot_self hvx u,
      dotProduct_comm ((u - x : V3) : Fin 3 → ℝ) ((e3Fan x v u : V3) : Fin 3 → ℝ)] at h1
    rw [← coe_sub]
    rw [dot_comm (u - x) (e3Fan x v u)]
    linarith [h1]
  have hp : ((u - x) - ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u) ⬝ᵥ
      ((u - x) - ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u) = 0 := by
    have he3 : e3Fan x v u ⬝ᵥ e3Fan x v u = 1 := e3Fan_dot_self hvx u
    rw [← coe_sub] at hsq
    -- set 变量化：(u-x)、e3Fan 变为原子变量，绕开复合 coercion 的混合形态
    set ux : V3 := u - x with hux
    set e3 : V3 := e3Fan x v u with he3s
    have hcomm : e3 ⬝ᵥ ux = ux ⬝ᵥ e3 := dot_comm _ _
    have hp' : (ux - (ux ⬝ᵥ e3) • e3) ⬝ᵥ (ux - (ux ⬝ᵥ e3) • e3) = 0 := by
      rw [sub_dot, dot_sub, dot_sub, coe_smul, coe_toLp, coe_toLp, smul_dotProduct,
        dotProduct_smul, smul_dotProduct, dotProduct_smul, he3, hcomm]
      simp only [smul_eq_mul] at hsq ⊢
      nlinarith [hsq]
    -- hp' 经 let 展开与目标 defeq
    exact hp'
  have hp0 : (u - x) - ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u = 0 := by
    have h3 : ‖(u - x) - ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u‖ ^ 2 = 0 := by
      rw [norm_sq_eq_dot]; exact hp
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h3)
  have hux : u - x = ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u := sub_eq_zero.mp hp0
  have h2 : ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u =
      (((u - x) ⬝ᵥ e3Fan x v u) * ‖v - x‖⁻¹) • (v - x) := by
    rw [e3Fan, smul_smul]
  exact hnc ((collinear3_iff_smul hvx).mpr
    ⟨((u - x) ⬝ᵥ e3Fan x v u) * ‖v - x‖⁻¹, by rw [← h2]; exact hux⟩)

/-- HOL fan.hl:1158 `e2_is_normal_fan`。 -/
theorem e2Fan_dot_self (hnc : ¬ Collinear3 x v u) : e2Fan x v u ⬝ᵥ e2Fan x v u = 1 := by
  have hn : ‖cross3 (e3Fan x v u) (u - x)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (e3Fan_cross_ux_ne_zero hnc)
  rw [e2Fan, coe_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← norm_sq_eq_dot, smul_eq_mul]
  have h2 : ‖cross3 (e3Fan x v u) (u - x)‖⁻¹ *
      (‖cross3 (e3Fan x v u) (u - x)‖⁻¹ * ‖cross3 (e3Fan x v u) (u - x)‖ ^ 2) = 1 := by
    field_simp [hn]
  exact h2

/-- HOL fan.hl:1170 `e2_orthogonal_e3_fan`。 -/
theorem e2Fan_dot_e3 (hnc : ¬ Collinear3 x v u) : e2Fan x v u ⬝ᵥ e3Fan x v u = 0 := by
  rw [e2Fan, coe_smul, smul_dotProduct,
    dotProduct_comm ((cross3 (e3Fan x v u) (u - x) : V3) : Fin 3 → ℝ)
      ((e3Fan x v u : V3) : Fin 3 → ℝ),
    cross3_dot_left, smul_zero]

/-- HOL fan.hl:1176 `e1_is_normal_fan`。 -/
theorem e1Fan_dot_self (hnc : ¬ Collinear3 x v u) : e1Fan x v u ⬝ᵥ e1Fan x v u = 1 := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  rw [e1Fan, cross3, dot_toLp, coe_toLp, cross_dot_cross, dot_coe, dot_coe, dot_coe,
    dot_coe, e2Fan_dot_self hnc, e3Fan_dot_self hvx u,
    dotProduct_comm ((e3Fan x v u : V3) : Fin 3 → ℝ) ((e2Fan x v u : V3) : Fin 3 → ℝ),
    e2Fan_dot_e3 hnc]
  ring

/-- HOL fan.hl:1192 `e1_orthogonal_e2_fan`。 -/
theorem e1Fan_dot_e2 (hnc : ¬ Collinear3 x v u) : e1Fan x v u ⬝ᵥ e2Fan x v u = 0 := by
  rw [e1Fan,
    dotProduct_comm ((cross3 (e2Fan x v u) (e3Fan x v u) : V3) : Fin 3 → ℝ)
      ((e2Fan x v u : V3) : Fin 3 → ℝ)]
  exact cross3_dot_left _ _

/-- HOL fan.hl:1187 `e1_orthogonal_e3_fan`。 -/
theorem e1Fan_dot_e3 (hnc : ¬ Collinear3 x v u) : e1Fan x v u ⬝ᵥ e3Fan x v u = 0 := by
  rw [e1Fan,
    dotProduct_comm ((cross3 (e2Fan x v u) (e3Fan x v u) : V3) : Fin 3 → ℝ)
      ((e3Fan x v u : V3) : Fin 3 → ℝ)]
  exact cross3_dot_right _ _

/-- HOL fan.hl:1211 `dot_e2_fan`。 -/
theorem dot_e2Fan (hnc : ¬ Collinear3 x v u) : (u - x) ⬝ᵥ e2Fan x v u = 0 := by
  rw [e2Fan, coe_smul, dotProduct_smul, cross3_dot_right, smul_zero]

/-- HOL fan.hl:1216 `vdot_e2_fan`。 -/
theorem vdot_e2Fan (hnc : ¬ Collinear3 x v u) : (v - x) ⬝ᵥ e2Fan x v u = 0 := by
  rw [e2Fan, coe_smul, dotProduct_smul, e3Fan, cross3_smul_left, coe_smul,
    dotProduct_smul, cross3_dot_left, smul_zero, smul_zero]

/-- e1 = n⁻¹ • ((u-x) - ((u-x)·e3)•e3)（Lagrange 展开；取点积前的中间形）。 -/
private theorem e1Fan_eq (hnc : ¬ Collinear3 x v u) :
    e1Fan x v u = ‖cross3 (e3Fan x v u) (u - x)‖⁻¹ •
      ((u - x) - ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u) := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  rw [e1Fan, e2Fan, cross3_smul_left, cross3_cross3, dot_coe, dot_coe,
    e3Fan_dot_self hvx u, one_smul]

/-- HOL fan.hl:1222 `udot_e1_fan`。 -/
theorem udot_e1Fan (hnc : ¬ Collinear3 x v u) : 0 < (u - x) ⬝ᵥ e1Fan x v u := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hn : 0 < ‖cross3 (e3Fan x v u) (u - x)‖ :=
    norm_pos_iff.mpr (e3Fan_cross_ux_ne_zero hnc)
  have h1 : (u - x) ⬝ᵥ e1Fan x v u = ‖cross3 (e3Fan x v u) (u - x)‖ := by
    rw [e1Fan_eq hnc, coe_smul, dotProduct_smul,
      coe_sub (u - x) (((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u), coe_smul,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hsq : (u - x) ⬝ᵥ (u - x) - ((u - x) ⬝ᵥ e3Fan x v u) *
        ((u - x) ⬝ᵥ e3Fan x v u) =
        cross3 (e3Fan x v u) (u - x) ⬝ᵥ cross3 (e3Fan x v u) (u - x) := by
      rw [cross3, dot_toLp, coe_toLp, cross_dot_cross, dot_coe, dot_coe, dot_coe,
        dot_coe, e3Fan_dot_self hvx u,
        dotProduct_comm ((u - x : V3) : Fin 3 → ℝ) ((e3Fan x v u : V3) : Fin 3 → ℝ)]
      simp only [coe_sub]
      ring
    simp only [coe_sub, smul_eq_mul] at hsq ⊢
    rw [hsq, ← norm_sq_eq_dot]
    have h2 : ‖cross3 (e3Fan x v u) (u - x)‖⁻¹ * ‖cross3 (e3Fan x v u) (u - x)‖ ^ 2 =
        ‖cross3 (e3Fan x v u) (u - x)‖ := by
      field_simp [ne_of_gt hn]
    exact h2
  rw [h1]
  exact hn

/-- HOL fan.hl:1247 `vdot_e1_fan`。 -/
theorem vdot_e1Fan (hnc : ¬ Collinear3 x v u) : (v - x) ⬝ᵥ e1Fan x v u = 0 := by
  rw [e1Fan, cross3, dotProduct_comm, dot_toLp, dotProduct_comm,
    triple_product_permutation, e3Fan, coe_smul, crossProduct_smul_left, cross_self,
    smul_zero, dotProduct_zero]

/-- 标准正交三向量的坐标展开（HOL `ORTHONORMAL_IMP_SPANNING` + `SPAN_3`
的角色：w = Σ (w·ei)•ei）。 -/
private theorem coord_eq_sum {e1 e2 e3 : V3} (h1 : e1 ⬝ᵥ e1 = 1) (h2 : e2 ⬝ᵥ e2 = 1)
    (h3 : e3 ⬝ᵥ e3 = 1) (h12 : e1 ⬝ᵥ e2 = 0) (h13 : e1 ⬝ᵥ e3 = 0)
    (h23 : e2 ⬝ᵥ e3 = 0) (w : V3) :
    w = (w ⬝ᵥ e1) • e1 + (w ⬝ᵥ e2) • e2 + (w ⬝ᵥ e3) • e3 := by
  have hli : LinearIndependent ℝ ![e1, e2, e3] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hd : ∀ e : V3, (g 0 • e1 + g 1 • e2 + g 2 • e3) ⬝ᵥ e = 0 := by
      intro e
      have hsum3 : g 0 • e1 + g 1 • e2 + g 2 • e3 =
          ∑ j : Fin 3, g j • ![e1, e2, e3] j := by
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      rw [hsum3, hg, zero_dot]
    fin_cases i
    · have h0 := hd e1
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
        add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct, h1,
        dotProduct_comm ((e2 : V3) : Fin 3 → ℝ) ((e1 : V3) : Fin 3 → ℝ), h12,
        dotProduct_comm ((e3 : V3) : Fin 3 → ℝ) ((e1 : V3) : Fin 3 → ℝ), h13] at h0
      simpa using h0
    · have h0 := hd e2
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
        add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct, h12, h2,
        dotProduct_comm ((e3 : V3) : Fin 3 → ℝ) ((e2 : V3) : Fin 3 → ℝ), h23] at h0
      simpa using h0
    · have h0 := hd e3
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
        add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
        h13, h23, h3] at h0
      simpa using h0
  have hspan : Submodule.span ℝ (Set.range ![e1, e2, e3]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  have hmem : w ∈ Submodule.span ℝ (Set.range ![e1, e2, e3]) :=
    hspan.symm ▸ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hw : w = c 0 • e1 + c 1 • e2 + c 2 • e3 := by
    rw [← hc, Finsupp.sum,
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_smul])]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have hc0 : c 0 = w ⬝ᵥ e1 := by
    rw [hw, coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
      add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct, h1,
      dotProduct_comm ((e2 : V3) : Fin 3 → ℝ) ((e1 : V3) : Fin 3 → ℝ), h12,
      dotProduct_comm ((e3 : V3) : Fin 3 → ℝ) ((e1 : V3) : Fin 3 → ℝ), h13]
    ring
  have hc1 : c 1 = w ⬝ᵥ e2 := by
    rw [hw, coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
      add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct, h12, h2,
      dotProduct_comm ((e3 : V3) : Fin 3 → ℝ) ((e2 : V3) : Fin 3 → ℝ), h23]
    ring
  have hc2 : c 2 = w ⬝ᵥ e3 := by
    rw [hw, coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct,
      add_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
      h13, h23, h3]
    ring
  rw [hc0, hc1, hc2] at hw
  exact hw

/-- HOL topology.hl:2302 `exp_aff_ge_by_dot`：¬collinear {x,v,u} 时
aff_ge {x,v} {u} 的点积刻画。 -/
theorem exp_aff_ge_by_dot {x v u : V3} (hnc : ¬ Collinear3 x v u) :
    affGe {x, v} {u} =
      {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0 ∧ 0 ≤ (w - x) ⬝ᵥ e1Fan x v u} := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hxv : x ≠ v := hvx.symm
  have hdisj : Disjoint ({x, v} : Set V3) {u} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he => hnc (collinear3_pair_left he),
      fun he => hnc (collinear3_pair_right he)⟩
  ext w
  constructor
  · intro hy
    rw [mem_affGe_pair hdisj hxv] at hy
    obtain ⟨t1, t2, t3, ht3, hsum, hy⟩ := hy
    have hwx : w - x = t2 • (v - x) + t3 • (u - x) := by
      rw [hy, show t1 = 1 - t2 - t3 from by linarith]
      module
    constructor
    · rw [hwx, coe_add, coe_smul, coe_smul, add_dotProduct, smul_dotProduct,
        smul_dotProduct, vdot_e2Fan hnc, dot_e2Fan hnc]
      ring
    · rw [hwx, coe_add, coe_smul, coe_smul, add_dotProduct, smul_dotProduct,
        smul_dotProduct, vdot_e1Fan hnc, smul_zero, zero_add, smul_eq_mul]
      have hu1 := udot_e1Fan hnc
      exact mul_nonneg ht3 (le_of_lt hu1)
  · rintro ⟨he2, he1⟩
    have hcoord := coord_eq_sum (e1Fan_dot_self hnc) (e2Fan_dot_self hnc)
      (e3Fan_dot_self hvx u) (e1Fan_dot_e2 hnc) (e1Fan_dot_e3 hnc) (e2Fan_dot_e3 hnc)
      (w - x)
    rw [he2, zero_smul, add_zero] at hcoord
    -- (u-x) = T1•e1 + T3•e3（dot_e2Fan 消去 e2 分量），T1 > 0，反解 e1；
    -- set 使标量原子不透明，避免 rw 回归
    have hux_coord := coord_eq_sum (e1Fan_dot_self hnc) (e2Fan_dot_self hnc)
      (e3Fan_dot_self hvx u) (e1Fan_dot_e2 hnc) (e1Fan_dot_e3 hnc) (e2Fan_dot_e3 hnc)
      (u - x)
    rw [dot_e2Fan hnc, zero_smul, add_zero] at hux_coord
    set A := (w - x) ⬝ᵥ e1Fan x v u with hA
    set T1 := (u - x) ⬝ᵥ e1Fan x v u with hT1s
    set T3 := (u - x) ⬝ᵥ e3Fan x v u with hT3s
    set C := (w - x) ⬝ᵥ e3Fan x v u with hC
    have hT1 : T1 ≠ 0 := by
      rw [hT1s]; exact ne_of_gt (udot_e1Fan hnc)
    have he1eq : e1Fan x v u = T1⁻¹ • ((u - x) - T3 • e3Fan x v u) := by
      have h : T1 • e1Fan x v u = (u - x) - T3 • e3Fan x v u := by
        conv_rhs => rw [hux_coord]
        module
      rw [← h, inv_smul_smul₀ hT1]
    have hcoord2 : w - x = (A * T1⁻¹) • (u - x) +
        ((C - A * T1⁻¹ * T3) * ‖v - x‖⁻¹) • (v - x) := by
      conv_lhs => rw [hcoord]
      rw [he1eq, e3Fan]; module
    rw [mem_affGe_pair hdisj hxv]
    refine ⟨1 - ((C - A * T1⁻¹ * T3) * ‖v - x‖⁻¹) - A * T1⁻¹,
      (C - A * T1⁻¹ * T3) * ‖v - x‖⁻¹, A * T1⁻¹, ?_, by ring, ?_⟩
    · rw [hA, hT1s]
      exact mul_nonneg he1 (inv_nonneg.mpr (le_of_lt (udot_e1Fan hnc)))
    · have : w = x + (w - x) := by module
      conv_lhs => rw [this, hcoord2]
      module

/-- CLOSED_HYPERPLANE 的点积形式：{w | (w - x) ⬝ᵥ e = 0} 闭。 -/
private theorem isClosed_dot_eq_zero (x e : V3) :
    IsClosed {w : V3 | (w - x) ⬝ᵥ e = 0} := by
  have hcont : Continuous fun w : V3 => (w - x) ⬝ᵥ e := by
    have h : Continuous fun w : V3 => inner ℝ (w - x) e :=
      (continuous_id.sub continuous_const).inner continuous_const
    simp only [inner_eq_dot] at h
    exact h
  exact isClosed_singleton.preimage hcont

/-- CLOSED_HALFSPACE_GE 的点积形式：{w | 0 ≤ (w - x) ⬝ᵥ e} 闭。 -/
private theorem isClosed_dot_ge_zero (x e : V3) :
    IsClosed {w : V3 | 0 ≤ (w - x) ⬝ᵥ e} := by
  have hcont : Continuous fun w : V3 => (w - x) ⬝ᵥ e := by
    have h : Continuous fun w : V3 => inner ℝ (w - x) e :=
      (continuous_id.sub continuous_const).inner continuous_const
    simp only [inner_eq_dot] at h
    exact h
  exact isClosed_Ici.preimage hcont

/-- HOL topology.hl:2377 `closed_aff_ge_2_1`：¬collinear {x,v,u} 时
aff_ge {x,v} {u} 闭。 -/
theorem closed_aff_ge_2_1 {x v u : V3} (hnc : ¬ Collinear3 x v u) :
    IsClosed (affGe {x, v} {u}) := by
  rw [exp_aff_ge_by_dot hnc]
  have h1 : {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0 ∧ 0 ≤ (w - x) ⬝ᵥ e1Fan x v u} =
      {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0} ∩
        {w : V3 | 0 ≤ (w - x) ⬝ᵥ e1Fan x v u} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h1]
  exact (isClosed_dot_eq_zero x _).inter (isClosed_dot_ge_zero x _)

/-- HOL topology.hl:2405 `closed_aff_ge_1_2`：¬collinear {x,v,w} 时
aff_ge {x} {v,w} 闭。 -/
theorem closed_aff_ge_1_2 {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    IsClosed (affGe {x} {v, w}) := by
  have hnc' : ¬ Collinear3 x w v := by
    intro hc
    have hset : ({x, w, v} : Set V3) = {x, v, w} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hc' : Collinear ℝ ({x, w, v} : Set V3) := hc
    have hc'' : Collinear ℝ ({x, v, w} : Set V3) := hset ▸ hc'
    exact hnc hc''
  rw [aff_ge_inter_aff_ge hnc]
  exact (closed_aff_ge_2_1 hnc).inter (closed_aff_ge_2_1 hnc')

/-- HOL topology.hl:2421 `AFF_GE_1_1`（成员形式）：y ∈ aff_ge {x} {v} ⟺
两点组合（v 系数非负）。 -/
theorem mem_affGe_singleton {x v : V3} (hxv : x ≠ v) {y : V3} :
    y ∈ affGe {x} {v} ↔
      ∃ t1 t2 : ℝ, 0 ≤ t2 ∧ t1 + t2 = 1 ∧ y = t1 • x + t2 • v := by
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    rw [sum_insert_single_s hfin hxv] at hone
    rw [sum_insert_single_v hfin hxv] at hsum
    exact ⟨f x, f v, hpos v (Set.mem_singleton v), hone, hsum⟩
  · rintro ⟨t1, t2, ht2, hsum, hy⟩
    have hfin : ({x} ∪ {v} : Set V3).Finite :=
      (Set.finite_singleton x).union (Set.finite_singleton v)
    refine ⟨fun z => if z = v then t2 else 1 - t2, hfin, ?_, ?_, ?_⟩
    · rw [sum_insert_single_v hfin hxv]
      simp only [eq_self_iff_true, if_true, if_neg hxv]
      rw [show t1 = 1 - t2 from by linarith] at hy
      exact hy
    · intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      simp only [eq_self_iff_true, if_true]
      exact ht2
    · rw [sum_insert_single_s hfin hxv]
      simp only [eq_self_iff_true, if_true, if_neg hxv]
      ring

/-- HOL topology.hl:2431 `exp_aff_ge_by_dot_1_1`：¬collinear {x,v,u} 时
aff_ge {x} {v} 的点积刻画。 -/
theorem exp_aff_ge_by_dot_1_1 {x v u : V3} (hnc : ¬ Collinear3 x v u) :
    affGe {x} {v} =
      {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0 ∧ 0 ≤ (w - x) ⬝ᵥ e3Fan x v u ∧
        (w - x) ⬝ᵥ e1Fan x v u = 0} := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hxv : x ≠ v := hvx.symm
  have hdote3 : (v - x) ⬝ᵥ e3Fan x v u = ‖v - x‖ := by
    have hn : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
    rw [e3Fan, coe_smul, dotProduct_smul, smul_eq_mul, ← norm_sq_eq_dot]
    have h2 : ‖v - x‖⁻¹ * ‖v - x‖ ^ 2 = ‖v - x‖ := by field_simp [hn]
    exact h2
  ext w
  constructor
  · intro hy
    rw [mem_affGe_singleton hxv] at hy
    obtain ⟨t1, t2, ht2, hsum, hy⟩ := hy
    have hwx : w - x = t2 • (v - x) := by
      rw [hy, show t1 = 1 - t2 from by linarith]
      module
    refine ⟨?_, ?_, ?_⟩
    · rw [hwx, coe_smul, smul_dotProduct, vdot_e2Fan hnc, smul_zero]
    · rw [hwx, coe_smul, smul_dotProduct, hdote3, smul_eq_mul]
      exact mul_nonneg ht2 (norm_nonneg _)
    · rw [hwx, coe_smul, smul_dotProduct, vdot_e1Fan hnc, smul_zero]
  · rintro ⟨he2, he3, he1⟩
    have hcoord := coord_eq_sum (e1Fan_dot_self hnc) (e2Fan_dot_self hnc)
      (e3Fan_dot_self hvx u) (e1Fan_dot_e2 hnc) (e1Fan_dot_e3 hnc) (e2Fan_dot_e3 hnc)
      (w - x)
    rw [he1, he2, zero_smul, zero_smul, add_zero, zero_add] at hcoord
    set C := (w - x) ⬝ᵥ e3Fan x v u with hC
    rw [mem_affGe_singleton hxv]
    refine ⟨1 - C * ‖v - x‖⁻¹, C * ‖v - x‖⁻¹, ?_, by ring, ?_⟩
    · rw [hC]; exact mul_nonneg he3 (inv_nonneg.mpr (norm_nonneg _))
    · have : w = x + (w - x) := by module
      conv_lhs => rw [this, hcoord, e3Fan]
      module

/-- HOL topology.hl:2486 `closed_halfline_fan`：¬collinear {x,v,u} 时
aff_ge {x} {v} 闭。 -/
theorem closed_halfline_fan {x v u : V3} (hnc : ¬ Collinear3 x v u) :
    IsClosed (affGe {x} {v}) := by
  rw [exp_aff_ge_by_dot_1_1 hnc]
  have h1 : {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0 ∧ 0 ≤ (w - x) ⬝ᵥ e3Fan x v u ∧
      (w - x) ⬝ᵥ e1Fan x v u = 0} =
      {w : V3 | (w - x) ⬝ᵥ e2Fan x v u = 0} ∩
        ({w : V3 | (w - x) ⬝ᵥ e1Fan x v u = 0} ∩
          {w : V3 | 0 ≤ (w - x) ⬝ᵥ e3Fan x v u}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [h1]
  exact (isClosed_dot_eq_zero x _).inter
    ((isClosed_dot_eq_zero x _).inter (isClosed_dot_ge_zero x _))

/-! ## 单位球面与分离（topology.hl:2535–2698）

ballnorm_fan（单位球面）的闭/有界/紧性质，exist_fan（无交闭集与紧集的
正分离，SEPARATE_CLOSED_COMPACT 的角色由 infDist 在紧集上的最小值给出），
ballsets_fan 与 exists_ballsets_fan，cone_ge_fan 定义。 -/

/-- HOL topology.hl:2535 `ballnorm_fan`：单位球面。 -/
def ballnormFan (x : V3) : Set V3 := {y | dist x y = 1}

private theorem ballnormFan_eq_sphere (x : V3) :
    ballnormFan x = Metric.sphere x 1 := by
  ext y
  simp only [ballnormFan, Metric.sphere, Set.mem_setOf_eq, dist_comm]

/-- HOL topology.hl:2538 `closed_ballnorm_fan`。 -/
theorem closed_ballnorm_fan (x : V3) : IsClosed (ballnormFan x) := by
  rw [ballnormFan_eq_sphere]
  exact Metric.isClosed_sphere

/-- HOL topology.hl:2548 `bounded_ballnorm_fan`。 -/
theorem bounded_ballnorm_fan (x : V3) : Bornology.IsBounded (ballnormFan x) := by
  rw [ballnormFan_eq_sphere]
  exact Metric.isBounded_sphere

/-- HOL topology.hl:2555 `bounded_ballnorm_fans`（有界子集的有界性）。 -/
theorem bounded_ballnorm_fans (x v w : V3) :
    Bornology.IsBounded (affGe {x} {v, w} ∩ ballnormFan x) :=
  (bounded_ballnorm_fan x).subset Set.inter_subset_right

/-- HOL topology.hl:2571 `closed_aff_ge_ballnorm_fan`。 -/
theorem closed_aff_ge_ballnorm_fan {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    IsClosed (affGe {x} {v, w} ∩ ballnormFan x) :=
  (closed_aff_ge_1_2 hnc).inter (closed_ballnorm_fan x)

/-- HOL topology.hl:2581 `compact_aff_ge_ballnorm_fan`
（BOUNDED_CLOSED_IMP_COMPACT）。 -/
theorem compact_aff_ge_ballnorm_fan {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    IsCompact (affGe {x} {v, w} ∩ ballnormFan x) :=
  Metric.isCompact_of_isClosed_isBounded (closed_aff_ge_ballnorm_fan hnc)
    (bounded_ballnorm_fans x v w)

/-- HOL topology.hl:2601 `closed_point_fan`。 -/
theorem closed_point_fan {x v u : V3} (hnc : ¬ Collinear3 x v u) :
    IsClosed (affGe {x} {v} ∩ ballnormFan x) :=
  (closed_halfline_fan hnc).inter (closed_ballnorm_fan x)

/-- aff_ge {x} ∅ = {x}（HOL `AFF_GE_EQ_AFFINE_HULL` + `AFFINE_SING`
的退化情形）。 -/
private theorem affGe_singleton_empty (x : V3) : affGe {x} ∅ = {x} := by
  ext y
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have h2 : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, Finset.mem_singleton]
    rw [h2, Finset.sum_singleton] at hsum hone
    have : y = x := by rw [hsum, hone, one_smul]
    rw [this]
    exact Set.mem_singleton x
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    have hfin : ({x} ∪ ∅ : Set V3).Finite :=
      (Set.finite_singleton x).union Set.finite_empty
    have h2 : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, Finset.mem_singleton]
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [hy]
      simp only [h2, Finset.sum_singleton, one_smul]
    · intro z hz
      exact ((Set.mem_empty_iff_false z).mp hz).elim
    · simp only [h2, Finset.sum_singleton]

/-- HOL topology.hl:2615 `exist_fan`：不相交的闭集 A = aff_ge{x}{v}∩S 与
紧集 B = aff_ge{x}{v1,w1}∩S 正分离（SEPARATE_CLOSED_COMPACT 的角色由
infDist 在紧集上的最小值给出；无交由 fan7 + dist x x = 0 ≠ 1 给出）。 -/
theorem exist_fan (hfan : FAN x V E) (hv : v ∉ ({v1, w1} : Set V3))
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 0 < h ∧
      ∀ y1 y2 : V3, y1 ∈ affGe {x} {v} ∩ ballnormFan x →
        y2 ∈ affGe {x} {v1, w1} ∩ ballnormFan x → h ≤ dist y1 y2 := by
  have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan he
  have hnc1 : ¬ Collinear3 x v1 w1 := fan_not_collinear hfan he1
  have hvx : v ≠ x := fun he2 => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) he2)
  have hv1x : v1 ≠ x := fun he2 => hnc1 (collinear3_of_eq (v := x) (w := v1) (w1 := w1) he2)
  have hVv : v ∈ V := hfan.1 (Set.mem_sUnion.mpr ⟨{v, w}, he, Set.mem_insert v {w}⟩)
  -- A ∩ B = ∅：fan7 + affGe {x} ∅ = {x} + dist x x = 0 ≠ 1
  have h77 : affGe {x} {v} ∩ affGe {x} {v1, w1} = affGe {x} ({v} ∩ {v1, w1}) :=
    hfan.2.2.2.2.2 {v} (Or.inr ⟨v, hVv, rfl⟩) {v1, w1} (Or.inl he1)
  have hinter : ({v} : Set V3) ∩ {v1, w1} = ∅ := Set.singleton_inter_eq_empty.mpr hv
  have hAB : (affGe {x} {v} ∩ ballnormFan x) ∩ (affGe {x} {v1, w1} ∩ ballnormFan x)
      = ∅ := by
    have h1 : (affGe {x} {v} ∩ ballnormFan x) ∩ (affGe {x} {v1, w1} ∩ ballnormFan x) =
        (affGe {x} {v} ∩ affGe {x} {v1, w1}) ∩ ballnormFan x := by
      ext y
      simp only [Set.mem_inter_iff]
      tauto
    rw [h1, h77, hinter, affGe_singleton_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, ballnormFan, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hyx
    rw [hyx, dist_self]
    norm_num
  have hB : IsCompact (affGe {x} {v1, w1} ∩ ballnormFan x) :=
    compact_aff_ge_ballnorm_fan hnc1
  have hA : IsClosed (affGe {x} {v} ∩ ballnormFan x) := closed_point_fan hnc
  have hAne : (affGe {x} {v} ∩ ballnormFan x).Nonempty := by
    have hn : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
    refine ⟨x + ‖v - x‖⁻¹ • (v - x), ?_, ?_⟩
    · rw [mem_affGe_singleton hvx.symm]
      exact ⟨1 - ‖v - x‖⁻¹, ‖v - x‖⁻¹, inv_nonneg.mpr (norm_nonneg _), by ring,
        by module⟩
    · rw [ballnormFan]
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm,
        show x - (x + ‖v - x‖⁻¹ • (v - x)) = -(‖v - x‖⁻¹ • (v - x)) from by module,
        norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]
  obtain ⟨h, hh0, hh⟩ := IsCompact.exists_forall_le' hB
    (Metric.continuous_infDist_pt _).continuousOn
    (fun y2 hy2 => by
      have hy2not : y2 ∉ closure (affGe {x} {v} ∩ ballnormFan x) := by
        rw [hA.closure_eq]
        intro hmem
        exact (Set.mem_empty_iff_false y2).mp (hAB ▸ ⟨hmem, hy2⟩)
      exact (Metric.infDist_pos_iff_notMem_closure hAne).mp hy2not)
  exact ⟨h, hh0, fun y1 y2 hy1 hy2 =>
    (hh y2 hy2).trans (by rw [dist_comm]; exact Metric.infDist_le_dist_of_mem hy1)⟩

/-- HOL topology.hl:2665 `ballsets_fan`：s 的开 h-邻域。 -/
def ballsetsFan (s : Set V3) (h : ℝ) : Set V3 := {y | ∃ x, dist x y < h ∧ x ∈ s}

/-- HOL topology.hl:2668 `exists_ballsets_fan`：exist_fan 的邻域形式。 -/
theorem exists_ballsets_fan (hfan : FAN x V E) (hv : v ∉ ({v1, w1} : Set V3))
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 0 < h ∧
      ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩
        (affGe {x} {v1, w1} ∩ ballnormFan x) = ∅ := by
  obtain ⟨h, hh0, hh⟩ := exist_fan hfan hv he1 he
  refine ⟨h, hh0, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, ballsetsFan, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro ⟨z, hzd, hzA⟩ hyA2 hyB2
  have hle := hh z y hzA ⟨hyA2, hyB2⟩
  linarith

/-- HOL topology.hl:2698 `cone_ge_fan`：以 x 为顶点的锥。 -/
def coneGeFan (x : V3) (s : Set V3) : Set V3 :=
  {y | ∃ a : ℝ, ∃ z : V3, 0 ≤ a ∧ z ∈ s ∧ y = a • (z - x) + x}

/-! ## cone 区域：交为空与 rcone 控制（topology.hl:2704–3296）

cone_ge_fan_inter_aff_ge_is_empty（核心：归一化点 y1 = ‖y-x‖⁻¹•(y-x)+x
同时落在球面、aff_ge 与 ballsets 中，与 exists_ballsets_fan 矛盾）、
rcone_subset_cone（rcone 条件经 Cauchy 控制归一化点距离）、
rw_dart_fan 与 avoids 系列、CTVTAQA（FAN 对边集子集封闭）。 -/

/-- HOL topology.hl:2704 `cone_ge_fan_inter_aff_ge_is_empty`：
∃ h>0, cone(ballsets(A,h)∩S) ∩ aff_ge{x}{v1,w1} = {x}。 -/
theorem cone_ge_fan_inter_aff_ge_is_empty (hfan : FAN x V E)
    (hv : v ∉ ({v1, w1} : Set V3)) (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 0 < h ∧
      coneGeFan x (ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩ ballnormFan x) ∩
        affGe {x} {v1, w1} = {x} := by
  have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan he
  have hnc1 : ¬ Collinear3 x v1 w1 := fan_not_collinear hfan he1
  have hvx : v ≠ x := fun he2 => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) he2)
  have hdisj1 : Disjoint ({x} : Set V3) {v1, w1} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he2 => hnc1 (collinear3_of_eq (v := x) (w := v1) (w1 := w1) he2.symm),
      fun he2 => hnc1 (collinear3_pair_left he2.symm)⟩
  have hv1w1 : v1 ≠ w1 := fun he2 => hnc1
    (collinear3_pair_right (v0 := x) (v1 := v1) (x := w1) he2.symm)
  obtain ⟨h, hh0, hh⟩ := exists_ballsets_fan hfan hv he1 he
  refine ⟨h, hh0, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨a, z, ha, hz, hy⟩, hyB⟩
    by_cases hyx : y = x
    · rw [Set.mem_singleton_iff]
      exact hyx
    · exfalso
      -- 归一化点 y1 = ‖y-x‖⁻¹•(y-x)+x：球面 + aff_ge + ballsets 三属，矛盾
      have hyne : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyx)
      rw [mem_affGe_singleton_pair hdisj1 hv1w1] at hyB
      obtain ⟨t1, t2, t3, ht2, ht3, hsum, hyaff⟩ := hyB
      -- y - x = a • (z - x)，‖y - x‖ = a（z 在球面上），a > 0
      have ha0 : a ≠ 0 := by
        intro h0
        apply hyx
        rw [hy, h0]
        module
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hnorm : ‖y - x‖ = a := by
        have h1 : y - x = a • (z - x) := by rw [hy]; module
        have hzn : ‖z - x‖ = 1 := by
          have h2 : dist x z = 1 := hz.2
          rw [dist_eq_norm] at h2
          rw [← h2, norm_sub_rev]
        rw [h1, norm_smul, Real.norm_of_nonneg (le_of_lt hapos), hzn, mul_one]
      -- y1 = z
      have hy1z : ‖y - x‖⁻¹ • (y - x) + x = z := by
        rw [hnorm, show y - x = a • (z - x) from by rw [hy]; module,
          inv_smul_smul₀ (ne_of_gt hapos)]
        module
      -- y1 ∈ ballnorm
      have hy1norm : ‖y - x‖⁻¹ • (y - x) + x ∈ ballnormFan x := by
        rw [ballnormFan]
        simp only [Set.mem_setOf_eq]
        rw [dist_eq_norm,
          show x - (‖y - x‖⁻¹ • (y - x) + x) = -(‖y - x‖⁻¹ • (y - x)) from by module,
          norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ hyne]
      -- y1 ∈ aff_ge {x} {v1, w1}（系数按 d = ‖y-x‖⁻¹ 缩放）
      have hy1aff : ‖y - x‖⁻¹ • (y - x) + x ∈ affGe {x} {v1, w1} := by
        rw [mem_affGe_singleton_pair hdisj1 hv1w1]
        refine ⟨1 - ‖y - x‖⁻¹ + ‖y - x‖⁻¹ * t1, ‖y - x‖⁻¹ * t2, ‖y - x‖⁻¹ * t3,
          mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ht2,
          mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ht3,
          by linear_combination ‖y - x‖⁻¹ * hsum, ?_⟩
        rw [hyaff]
        module
      -- y1 ∈ ballsets A h（y1 = z）
      have hy1A : ‖y - x‖⁻¹ • (y - x) + x ∈
          ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h := hy1z ▸ hz.1
      have hy1mem : ‖y - x‖⁻¹ • (y - x) + x ∈
          ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩
            (affGe {x} {v1, w1} ∩ ballnormFan x) := ⟨hy1A, hy1aff, hy1norm⟩
      exact (Set.mem_empty_iff_false _).mp (hh ▸ hy1mem)
  · -- x ∈ LHS：a = 0，z0 = ‖v-x‖⁻¹•(v-x)+x ∈ ballsets A h ∩ S
    intro hyx
    rw [Set.mem_singleton_iff] at hyx
    subst y
    have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
    have hz0norm : ‖v - x‖⁻¹ • (v - x) + x ∈ ballnormFan x := by
      rw [ballnormFan]
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm,
        show x - (‖v - x‖⁻¹ • (v - x) + x) = -(‖v - x‖⁻¹ • (v - x)) from by module,
        norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hnv]
    have hz0A : ‖v - x‖⁻¹ • (v - x) + x ∈ affGe {x} {v} ∩ ballnormFan x := by
      refine ⟨?_, hz0norm⟩
      rw [mem_affGe_singleton hvx.symm]
      exact ⟨1 - ‖v - x‖⁻¹, ‖v - x‖⁻¹, inv_nonneg.mpr (norm_nonneg _), by ring,
        by module⟩
    refine ⟨⟨0, ‖v - x‖⁻¹ • (v - x) + x, le_refl 0, ⟨?_, hz0norm⟩, by module⟩, ?_⟩
    · exact ⟨‖v - x‖⁻¹ • (v - x) + x, by rw [dist_self]; exact hh0, hz0A⟩
    · -- x ∈ aff_ge {x} {v1, w1}：系数 (1, 0, 0)
      rw [mem_affGe_singleton_pair hdisj1 hv1w1]
      exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by module⟩

/-- HOL topology.hl:2874 `subset_by_inequality_fan`：h < h1 时 cone 交
随 ballsets 半径单调。 -/
theorem subset_by_inequality_fan (hfan : FAN x V E) (hv : v ∉ ({v1, w1} : Set V3))
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) (h h1 : ℝ) (hh : h < h1) :
    coneGeFan x (ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩ ballnormFan x) ∩
      affGe {x} {v1, w1} ⊆
    coneGeFan x (ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h1 ∩ ballnormFan x) ∩
      affGe {x} {v1, w1} := by
  have hsub : ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ⊆
      ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h1 := by
    intro y hy
    obtain ⟨p, hpd, hp⟩ := hy
    exact ⟨p, hpd.trans hh, hp⟩
  intro y ⟨⟨a, z, ha, hz, hy⟩, hyB⟩
  exact ⟨⟨a, z, ha, ⟨hsub hz.1, hz.2⟩, hy⟩, hyB⟩

/-- HOL topology.hl:2900 `cone_ge_fan_inter_aff_ge_is_empty_fan`：
∃ h, 1 > h > 0，cone 交 ⊆ {x}（h ≥ 1 时用 1/2 缩减）。 -/
theorem cone_ge_fan_inter_aff_ge_is_empty_fan (hfan : FAN x V E)
    (hv : v ∉ ({v1, w1} : Set V3)) (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      coneGeFan x (ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩ ballnormFan x) ∩
        affGe {x} {v1, w1} ⊆ {x} := by
  obtain ⟨h, hh0, hh⟩ := cone_ge_fan_inter_aff_ge_is_empty hfan hv he1 he
  by_cases h1 : 1 ≤ h
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    exact (subset_by_inequality_fan hfan hv he1 he (1 / 2) h (by linarith)).trans
      hh.subset
  · push_neg at h1
    exact ⟨h, h1, hh0, hh.subset⟩

/-- HOL topology.hl:2936 `rcone_subset_cone`：h1 = (2 - h²)/2 时
rcone x v h1 ⊆ cone(ballsets(A,h)∩S)（归一化点距离经点积条件控制）。 -/
theorem rcone_subset_cone (hfan : FAN x V E) (he : {v, w} ∈ E) (h0 : 0 < h)
    (h1 : h < 1) :
    ∃ h1 : ℝ, 1 > h1 ∧ h1 > 0 ∧
      rconeFan x v h1 ⊆
        coneGeFan x
          (ballsetsFan (affGe {x} {v} ∩ ballnormFan x) h ∩ ballnormFan x) := by
  have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan he
  have hvx : v ≠ x := fun he2 => hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) he2)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hnvp : 0 < ‖v - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvx)
  have hsq0 : 0 < h ^ 2 := sq_pos_of_pos h0
  have hsq1 : h ^ 2 < 1 := by nlinarith [h0, h1, mul_lt_mul_of_pos_left h1 h0]
  refine ⟨(2 - h ^ 2) / 2, by linarith, by linarith, ?_⟩
  intro y hy
  rw [rconeFan] at hy
  simp only [Set.mem_setOf_eq] at hy
  by_cases hyx : y = x
  · -- y = x：rcone 条件给出 0 > 0，矛盾
    subst hyx
    have hz : (y - y : V3) ⬝ᵥ (v - y) = 0 := by
      rw [sub_self]
      exact zero_dot _
    rw [hz] at hy
    simp at hy
  · have hyne : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyx)
    have hnyp : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    refine ⟨‖y - x‖, ‖y - x‖⁻¹ • (y - x) + x, norm_nonneg _, ⟨?_, ?_⟩, ?_⟩
    · -- z ∈ ballsets A h：证人 z1 = ‖v-x‖⁻¹•(v-x)+x，dist z1 z < h
      refine ⟨‖v - x‖⁻¹ • (v - x) + x, ?_, ⟨?_, ?_⟩⟩
      · -- dist z1 z < h：平方比较（点积条件控制 ⟪v1', z'⟫ > (2-h²)/2）
        have hz1z : (‖v - x‖⁻¹ • (v - x) + x) - (‖y - x‖⁻¹ • (y - x) + x) =
            ‖v - x‖⁻¹ • (v - x) - ‖y - x‖⁻¹ • (y - x) := by module
        rw [dist_eq_norm, hz1z]
        have hv1 : inner ℝ (‖v - x‖⁻¹ • (v - x)) (‖v - x‖⁻¹ • (v - x)) = 1 := by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp [hnv]
        have hz1 : inner ℝ (‖y - x‖⁻¹ • (y - x)) (‖y - x‖⁻¹ • (y - x)) = 1 := by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp [hyne]
        have hD : (v - x) ⬝ᵥ (y - x) > ‖y - x‖ * ‖v - x‖ * ((2 - h ^ 2) / 2) := by
          rw [dist_eq_norm, dist_eq_norm] at hy
          simp only [coe_sub] at hy ⊢
          rw [dotProduct_comm (((y : V3) : Fin 3 → ℝ) - ((x : V3) : Fin 3 → ℝ))
            (((v : V3) : Fin 3 → ℝ) - ((x : V3) : Fin 3 → ℝ))] at hy
          exact hy
        have hdot : (2 - h ^ 2) / 2 <
            inner ℝ (‖v - x‖⁻¹ • (v - x)) (‖y - x‖⁻¹ • (y - x)) := by
          rw [real_inner_smul_left, real_inner_smul_right, inner_eq_dot]
          calc (2 - h ^ 2) / 2
              = ‖v - x‖⁻¹ * (‖y - x‖⁻¹ * (‖y - x‖ * ‖v - x‖ * ((2 - h ^ 2) / 2))) := by
                field_simp [hnv, hyne]
            _ < ‖v - x‖⁻¹ * (‖y - x‖⁻¹ * ((v - x) ⬝ᵥ (y - x))) :=
                mul_lt_mul_of_pos_left
                  (mul_lt_mul_of_pos_left hD (inv_pos.mpr hnyp)) (inv_pos.mpr hnvp)
        have hsq : ‖‖v - x‖⁻¹ • (v - x) - ‖y - x‖⁻¹ • (y - x)‖ ^ 2 < h ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
            inner_sub_right, hv1, hz1]
          nlinarith [hdot, real_inner_comm (‖y - x‖⁻¹ • (y - x)) (‖v - x‖⁻¹ • (v - x))]
        exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (le_of_lt h0)
          (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
      · -- z1 ∈ aff_ge {x} {v}
        rw [mem_affGe_singleton hvx.symm]
        exact ⟨1 - ‖v - x‖⁻¹, ‖v - x‖⁻¹, inv_nonneg.mpr (norm_nonneg _), by ring,
          by module⟩
      · -- z1 ∈ ballnormFan x
        rw [ballnormFan]
        simp only [Set.mem_setOf_eq]
        rw [dist_eq_norm,
          show x - (‖v - x‖⁻¹ • (v - x) + x) = -(‖v - x‖⁻¹ • (v - x)) from by module,
          norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ hnv]
    · -- z ∈ ballnormFan x
      rw [ballnormFan]
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm,
        show x - (‖y - x‖⁻¹ • (y - x) + x) = -(‖y - x‖⁻¹ • (y - x)) from by module,
        norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hyne]
    · -- y = ‖y-x‖ • (z - x) + x
      rw [show ‖y - x‖⁻¹ • (y - x) + x - x = ‖y - x‖⁻¹ • (y - x) from by module]
      rw [smul_inv_smul₀ hyne]
      module

/-- HOL topology.hl:3110 `origin_not_in_rcone_fan`。 -/
theorem origin_not_in_rcone_fan (x v : V3) (h : ℝ) : x ∉ rconeFan x v h := by
  intro hy
  rw [rconeFan] at hy
  simp only [Set.mem_setOf_eq] at hy
  have hz : (x - x : V3) ⬝ᵥ (v - x) = 0 := by
    rw [sub_self]
    exact zero_dot _
  rw [hz] at hy
  simp at hy

/-- HOL topology.hl:3118 `inter_is_empty`：∃ h1, 1 > h1 > 0，
rcone x v h1 ∩ aff_ge {x} {v1,w1} = ∅。 -/
theorem inter_is_empty (hfan : FAN x V E) (hv : v ∉ ({v1, w1} : Set V3))
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h1 : ℝ, 1 > h1 ∧ h1 > 0 ∧ rconeFan x v h1 ∩ affGe {x} {v1, w1} = ∅ := by
  obtain ⟨h, hh1, hh0, hh⟩ := cone_ge_fan_inter_aff_ge_is_empty_fan hfan hv he1 he
  obtain ⟨h1, hh1', hh0', hsub⟩ := rcone_subset_cone hfan he hh0 hh1
  refine ⟨h1, hh1', hh0', ?_⟩
  have hsub2 : rconeFan x v h1 ∩ affGe {x} {v1, w1} ⊆ {x} :=
    (Set.inter_subset_inter_left _ hsub).trans hh
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hyx : y = x := Set.mem_singleton_iff.mp (hsub2 hy)
  exact origin_not_in_rcone_fan x v h1 (hyx ▸ hy.1)

/-- HOL topology.hl:3174 `rw_dart_fan`：w_dart ∩ rcone。 -/
def rwDartFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (p : V3 × V3 × V3 × V3) (h : ℝ) : Set V3 :=
  wDartFan x V E p ∩ rconeFan x p.2.1 h

/-- HOL topology.hl:3178 `avoids_fan`：v ∉ {v1,w1} 时 rw_dart 避开
aff_ge {x} {v1,w1}（inter_is_empty 的推論）。 -/
theorem avoids_fan (hfan : FAN x V E) (hv : v ∉ ({v1, w1} : Set V3))
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) (w2 : V3) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, w, w2) h ∩ affGe {x} {v1, w1} = ∅ := by
  obtain ⟨h1, hh1, hh0, hh⟩ := inter_is_empty hfan hv he1 he
  exact ⟨h1, hh1, hh0, by
    rw [rwDartFan]
    show wDartFan x V E (x, v, w, w2) ∩ rconeFan x v h1 ∩ affGe {x} {v1, w1} = ∅
    rw [Set.inter_assoc, hh, Set.inter_empty]⟩

/-- HOL topology.hl:3197 `avoids1_fan`：同顶点情形（IBZWFFH 的推论）。 -/
theorem avoids1_fan (hfan : FAN x V E) (he : {v, w} ∈ E) (he1 : {v, w1} ∈ E) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ∩ affGe {x} {v, w1} = ∅ := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  rw [rwDartFan]
  exact Set.eq_empty_of_subset_empty
    ((Set.inter_subset_inter Set.inter_subset_left (Set.Subset.refl _)).trans
      (IBZWFFH hfan he he1).subset)

/-- HOL topology.hl:3214 `finish_avoids_fan`：v ∈ {v1,w1} 与否统一。 -/
theorem finish_avoids_fan (hfan : FAN x V E) (he : {v, w} ∈ E) (he1 : {v1, w1} ∈ E) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ∩ affGe {x} {v1, w1} = ∅ := by
  by_cases hv : v ∈ ({v1, w1} : Set V3)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hveq | hveq
    · -- v = v1：消去 v1
      subst hveq
      exact avoids1_fan hfan he he1
    · -- v = w1：消去 w1，换序后用 avoids1_fan
      subst hveq
      have he1' : ({v, v1} : Set V3) ∈ E := Set.pair_comm v1 v ▸ he1
      obtain ⟨h, hh1, hh0, hh⟩ := avoids1_fan hfan he he1'
      exact ⟨h, hh1, hh0, by rw [Set.pair_comm v1 v]; exact hh⟩
  · exact avoids_fan hfan hv he1 he (sigmaFan x V E v w)

/-- HOL topology.hl:3253 `continuous_set_fan`：rw_dart 随半径单调
（h1 ≤ h 时缩小）。 -/
theorem continuous_set_fan (hfan : FAN x V E) (he : {v, w} ∈ E) (h h1 : ℝ)
    (hle : h1 ≤ h) :
    rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ⊆
      rwDartFan x V E (x, v, w, sigmaFan x V E v w) h1 := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨hy1, ?_⟩
  rw [rconeFan] at hy2 ⊢
  simp only [Set.mem_setOf_eq] at hy2 ⊢
  have hmul : dist y x * dist v x * h1 ≤ dist y x * dist v x * h :=
    mul_le_mul_of_nonneg_left hle (mul_nonneg dist_nonneg dist_nonneg)
  linarith

/-- HOL topology.hl:3282 `CTVTAQA`：FAN 对边集子集封闭。 -/
theorem CTVTAQA (hfan : FAN x V E) (hE1 : E1 ⊆ E) : FAN x V E1 := by
  obtain ⟨hsub, hgraph, hfan1, hfan2, hfan6, hfan7⟩ := hfan
  refine ⟨(Set.sUnion_subset_sUnion hE1).trans hsub, fun e he => hgraph e (hE1 he),
    hfan1, hfan2, fun e he => hfan6 e (hE1 he), fun e1 he1 e2 he2 =>
      hfan7 e1 (he1.elim (fun h => Or.inl (hE1 h)) Or.inr) e2
        (he2.elim (fun h => Or.inl (hE1 h)) Or.inr)⟩

/-- HOL topology.hl:3291 `expand_edge_graph_fan`：边 = 二元素集。 -/
theorem expand_edge_graph_fan (hfan : FAN x V E) (he : e ∈ E) :
    ∃ v w : V3, e = {v, w} := by
  obtain ⟨hfin, hcard⟩ := hfan.2.1 e he
  obtain ⟨v, w, hvw, hfin'⟩ := Finset.card_eq_two.mp hcard
  refine ⟨v, w, ?_⟩
  have h2 : e = hfin.toFinset := (Set.Finite.coe_toFinset hfin).symm
  rw [h2, hfin']
  simp

/-! ## finish_avoids1 与 rw_dart_avoids（topology.hl:3396–3578）

finish_avoids1_fan：rw_dart 避开 E' 全体边的 aff_ge 并（对 E'.toFinset
作 Finset.induction，插入步用 finish_avoids_fan + continuous_set_fan 取
max）。rw_dart_avoids_fan：rw_dart ⊆ yfan（= UNIV \ xfan）。 -/

/-- HOL topology.hl:3396 `finish_avoids1_fan`。 -/
theorem finish_avoids1_fan (hfan : FAN x V E) (he : {v, w} ∈ E)
    (hE' : E' ⊆ E) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ∩
        {y | ∃ e ∈ E', y ∈ affGe {x} e} = ∅ := by
  have hE'fin : E'.Finite := (setEdgesFiniteFan hfan).subset hE'
  -- 对边集作 Finset 归纳（HOL 的 CARD 归纳的 insert 形）
  have key : ∀ s : Finset (Set V3), (↑s : Set (Set V3)) ⊆ E →
      ∃ h : ℝ, 1 > h ∧ h > 0 ∧
        rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ∩
          {y | ∃ e ∈ (↑s : Set (Set V3)), y ∈ affGe {x} e} = ∅ := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro hsub
      refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [show {y : V3 | ∃ e ∈ (↑(∅ : Finset (Set V3)) : Set (Set V3)),
          y ∈ affGe {x} e} = ∅ from by
        ext y
        simp only [Finset.coe_empty, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨e, he, -⟩
        exact he]
      exact Set.inter_empty _
    | @insert e t ht ih =>
      intro hsub
      -- e ∈ E 且 t ⊆ E
      have heE : e ∈ E := hsub (Finset.mem_coe.mpr (Finset.mem_insert_self e t))
      have htE : (↑t : Set (Set V3)) ⊆ E := fun e2 he2 =>
        hsub (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp he2)))
      -- 单边 e = {v', w'} 由 finish_avoids_fan，t 由 IH；取 h1 = max
      obtain ⟨v', w', he'⟩ := expand_edge_graph_fan hfan heE
      obtain ⟨h', hh1', hh0', hh'⟩ := finish_avoids_fan hfan he (he' ▸ heE)
      obtain ⟨ht', hht1, hht0, hht⟩ := ih htE
      refine ⟨max h' ht', by simp [hh1', hht1], by simp [hh0', hht0], ?_⟩
      -- 目标集合分解为 affGe {x} e ∪ （t 上的并）
      have hunion : {y : V3 | ∃ e2 ∈ (↑(insert e t) : Set (Set V3)),
          y ∈ affGe {x} e2} =
          affGe {x} e ∪ {y | ∃ e2 ∈ (↑t : Set (Set V3)), y ∈ affGe {x} e2} := by
        ext y
        simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_setOf_eq,
          Set.mem_union]
        constructor
        · rintro ⟨e2, rfl | he2t, hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨e2, he2t, hy⟩
        · rintro (hy | ⟨e2, he2t, hy⟩)
          · exact ⟨e, Or.inl rfl, hy⟩
          · exact ⟨e2, Or.inr he2t, hy⟩
      rw [hunion, Set.inter_union_distrib_left]
      have hdart1 : rwDartFan x V E (x, v, w, sigmaFan x V E v w) (max h' ht') ∩
          affGe {x} e = ∅ := by
        rw [he']
        exact Set.eq_empty_of_subset_empty
          ((Set.inter_subset_inter_left _
            (continuous_set_fan hfan he (max h' ht') h' (le_max_left _ _))).trans
            hh'.subset)
      have hdartt : rwDartFan x V E (x, v, w, sigmaFan x V E v w) (max h' ht') ∩
          {y | ∃ e2 ∈ (↑t : Set (Set V3)), y ∈ affGe {x} e2} = ∅ := by
        exact Set.eq_empty_of_subset_empty
          ((Set.inter_subset_inter_left _
            (continuous_set_fan hfan he (max h' ht') ht' (le_max_right _ _))).trans
            hht.subset)
      rw [hdart1, hdartt, Set.union_empty]
  obtain ⟨h, hh1, hh0, hh⟩ := key hE'fin.toFinset (by
    intro e he2
    exact hE' (hE'fin.mem_toFinset.mp he2))
  refine ⟨h, hh1, hh0, ?_⟩
  rw [show {y : V3 | ∃ e ∈ E', y ∈ affGe {x} e} =
      {y : V3 | ∃ e ∈ (↑hE'fin.toFinset : Set (Set V3)), y ∈ affGe {x} e} from by
    ext y
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Set.Finite.mem_toFinset]]
  exact hh

/-- HOL topology.hl:3553 `rw_dart_avoids_fan`：rw_dart ⊆ yfan。 -/
theorem rw_dart_avoids_fan (hfan : FAN x V E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, w, sigmaFan x V E v w) h ⊆ yfan x V E := by
  obtain ⟨h, hh1, hh0, hh⟩ := finish_avoids1_fan hfan he (Set.Subset.refl E)
  refine ⟨h, hh1, hh0, ?_⟩
  rw [yfan]
  exact Set.subset_diff.mpr ⟨Set.subset_univ _,
    Set.disjoint_iff_inter_eq_empty.mpr hh⟩

/-! ## r_fan 坐标半空间（topology.hl:3580–3650）

r_fan 及六个半空间定义、r_fan_is_inter_halfspace、凸性与开性
（CONVEX/OPEN_HALFSPACE_COMPONENT_LT/GT 由分量映射的连续性 +
直接组合论证给出）、r_is_connected_fan（CONVEX_CONNECTED）。 -/

/-- HOL topology.hl:3580 `r_fan`（HOL `y$1` 1-指标 ↔ `y 0` Fin 3 0-指标）。 -/
def rFan (a b c : ℝ) : Set V3 :=
  {y | y (0 : Fin 3) > 0 ∧ y (1 : Fin 3) > a ∧ y (1 : Fin 3) < b ∧
    y (2 : Fin 3) > 0 ∧ y (2 : Fin 3) < c}

/-- HOL topology.hl:3584 `r1_le_fan`。 -/
def r1LeFan (a : ℝ) : Set V3 := {y | y (0 : Fin 3) > a}

/-- HOL topology.hl:3587 `r2_le_fan`。 -/
def r2LeFan (a : ℝ) : Set V3 := {y | y (1 : Fin 3) > a}

/-- HOL topology.hl:3591 `r3_le_fan`。 -/
def r3LeFan (a : ℝ) : Set V3 := {y | y (2 : Fin 3) > a}

/-- HOL topology.hl:3595 `r1_ge_fan`。 -/
def r1GeFan (a : ℝ) : Set V3 := {y | y (0 : Fin 3) < a}

/-- HOL topology.hl:3598 `r2_ge_fan`。 -/
def r2GeFan (a : ℝ) : Set V3 := {y | y (1 : Fin 3) < a}

/-- HOL topology.hl:3600 `r3_ge_fan`。 -/
def r3GeFan (a : ℝ) : Set V3 := {y | y (2 : Fin 3) < a}

/-- HOL topology.hl:3605 `r_fan_is_inter_halfspace`。 -/
theorem r_fan_is_inter_halfspace (a b c : ℝ) :
    rFan a b c = r1LeFan 0 ∩ r2LeFan a ∩ r2GeFan b ∩ r3LeFan 0 ∩ r3GeFan c := by
  ext y
  simp only [rFan, r1LeFan, r2LeFan, r2GeFan, r3LeFan, r3GeFan, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  tauto

/-- 分量半空间的凸性与开性（HOL CONVEX/OPEN_HALFSPACE_COMPONENT_LT 的
角色：{y | y i < a}）。 -/
private theorem convex_isOpen_component_lt (i : Fin 3) (a : ℝ) :
    Convex ℝ {y : V3 | y i < a} ∧ IsOpen {y : V3 | y i < a} := by
  refine ⟨?_, ?_⟩
  · intro y hy z hz p q hp hq hpq
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    have h1 : ((p • y + q • z : V3) i) = p * (y i) + q * (z i) := by
      simp [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    rw [h1]
    have hpa : p * (y i) ≤ p * a := mul_le_mul_of_nonneg_left hy.le hp
    have hqa : q * (z i) ≤ q * a := mul_le_mul_of_nonneg_left hz.le hq
    have hsum : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
    by_cases hp0 : p = 0
    · subst hp0
      have hq1 : q = 1 := by linarith
      subst hq1
      linarith [hz]
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hpa' : p * (y i) < p * a := mul_lt_mul_of_pos_left hy hp'
      linarith [hpa', hqa, hsum]
  · have hcont : Continuous (fun y : V3 => y.ofLp i) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) i
    exact isOpen_Iio.preimage hcont

/-- 分量半空间的凸性与开性（HOL CONVEX/OPEN_HALFSPACE_COMPONENT_GT 的
角色：{y | y i > a}）。 -/
private theorem convex_isOpen_component_gt (i : Fin 3) (a : ℝ) :
    Convex ℝ {y : V3 | y i > a} ∧ IsOpen {y : V3 | y i > a} := by
  refine ⟨?_, ?_⟩
  · intro y hy z hz p q hp hq hpq
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    have h1 : ((p • y + q • z : V3) i) = p * (y i) + q * (z i) := by
      simp [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    rw [h1]
    have hpa : p * (y i) ≥ p * a := mul_le_mul_of_nonneg_left hy.le hp
    have hqa : q * (z i) ≥ q * a := mul_le_mul_of_nonneg_left hz.le hq
    have hsum : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
    by_cases hp0 : p = 0
    · subst hp0
      have hq1 : q = 1 := by linarith
      subst hq1
      linarith [hz]
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hpa' : p * (y i) > p * a := mul_lt_mul_of_pos_left hy hp'
      linarith [hpa', hqa, hsum]
  · have hcont : Continuous (fun y : V3 => y.ofLp i) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) i
    exact isOpen_Ioi.preimage hcont

/-- HOL topology.hl:3613 `r1_ge_is_convex_fan`。 -/
theorem r1_ge_is_convex_fan (a : ℝ) :
    Convex ℝ (r1GeFan a) ∧ IsOpen (r1GeFan a) :=
  convex_isOpen_component_lt 0 a

/-- HOL topology.hl:3616 `r2_ge_is_convex_fan`。 -/
theorem r2_ge_is_convex_fan (a : ℝ) :
    Convex ℝ (r2GeFan a) ∧ IsOpen (r2GeFan a) :=
  convex_isOpen_component_lt 1 a

/-- HOL topology.hl:3619 `r3_ge_is_convex_fan`。 -/
theorem r3_ge_is_convex_fan (a : ℝ) :
    Convex ℝ (r3GeFan a) ∧ IsOpen (r3GeFan a) :=
  convex_isOpen_component_lt 2 a

/-- HOL topology.hl:3622 `r1_le_is_convex_fan`。 -/
theorem r1_le_is_convex_fan (a : ℝ) :
    Convex ℝ (r1LeFan a) ∧ IsOpen (r1LeFan a) :=
  convex_isOpen_component_gt 0 a

/-- HOL topology.hl:3625 `r2_le_is_convex_fan`。 -/
theorem r2_le_is_convex_fan (a : ℝ) :
    Convex ℝ (r2LeFan a) ∧ IsOpen (r2LeFan a) :=
  convex_isOpen_component_gt 1 a

/-- HOL topology.hl:3628 `r3_le_is_convex_fan`。 -/
theorem r3_le_is_convex_fan (a : ℝ) :
    Convex ℝ (r3LeFan a) ∧ IsOpen (r3LeFan a) :=
  convex_isOpen_component_gt 2 a

/-- HOL topology.hl:3631 `r_is_connected_fan`。注意：HOL `connected` 在
空集上为真，Mathlib `IsConnected` 要求 Nonempty（rFan 在 a ≥ b 或 c ≤ 0
时为空）——故此处用无 Nonempty 前提的 `IsPreconnected`（HOL
`CONVEX_CONNECTED` ↔ Mathlib `Convex.isPreconnected`）。 -/
theorem r_is_connected_fan (a b c : ℝ) :
    IsPreconnected (rFan a b c) ∧ Convex ℝ (rFan a b c) ∧ IsOpen (rFan a b c) := by
  have hconv : Convex ℝ (rFan a b c) := by
    rw [r_fan_is_inter_halfspace]
    exact ((((convex_isOpen_component_gt 0 0).1.inter
      (convex_isOpen_component_gt 1 a).1).inter
      (convex_isOpen_component_lt 1 b).1).inter
      (convex_isOpen_component_gt 2 0).1).inter
      (convex_isOpen_component_lt 2 c).1
  exact ⟨hconv.isPreconnected, hconv, by
    rw [r_fan_is_inter_halfspace]
    exact ((((convex_isOpen_component_gt 0 0).2.inter
      (convex_isOpen_component_gt 1 a).2).inter
      (convex_isOpen_component_lt 1 b).2).inter
      (convex_isOpen_component_gt 2 0).2).inter
      (convex_isOpen_component_lt 2 c).2⟩

/-- HOL topology.hl:3652 `change_spherical_coordinate_fan`（HOL `t$1`=r、
`t$2`=θ、`t$3`=φ，1-指标 ↔ Fin 3 的 0/1/2）。 -/
noncomputable def changeSphericalCoordinateFan (x v u : V3) : V3 → V3 :=
  fun t => x + (t (0 : Fin 3) * Real.cos (t (1 : Fin 3)) * Real.sin (t (2 : Fin 3))) •
      e1Fan x v u +
    (t (0 : Fin 3) * Real.sin (t (1 : Fin 3)) * Real.sin (t (2 : Fin 3))) •
      e2Fan x v u +
    (t (0 : Fin 3) * Real.cos (t (2 : Fin 3))) • e3Fan x v u

/-! ## 球坐标下的 azim 展开（topology.hl:3666–3814）

REAL_CONTINUOUS_AT_COMPONENT（3666）：Mathlib 已由
`PiLp.continuous_apply` 覆盖，跳过。
one_edge_fan（3692）：CARD ≤ 1 时 soe = {u}。
azim_fan（3724）：定义。
expand_elements_by_azim_fan（3729）：球坐标点的 azim = θ，
经 azim_eq_of_spec（AZIM_UNIQUE 的角色）+ e-标架基准 +
on3_axis_change 的单位复数旋转传递。 -/

/-- HOL topology.hl:3692 `one_edge_fan`：CARD ≤ 1 时 set_of_edge = {u}。 -/
theorem one_edge_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hcard : ¬ (1 < (setOfEdge v V E).ncard)) :
    setOfEdge v V E = {u} := by
  have hu_soe : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hle : (setOfEdge v V E).ncard ≤ 1 := by
    by_contra h; push_neg at h; exact hcard h
  have hsub : ({u} : Set V3) ⊆ setOfEdge v V E := Set.singleton_subset_iff.mpr hu_soe
  have h1 : (setOfEdge v V E).ncard ≤ ({u} : Set V3).ncard := by
    rw [Set.ncard_singleton]; exact hle
  exact (Set.eq_of_subset_of_ncard_le hsub h1
    (remark_finite_fan1 v V E hfan.2.2.1.1)).symm

/-- HOL topology.hl:3724 `azim_fan`。 -/
noncomputable def azimFan (x : V3) (V : Set V3) (E : Set (Set V3)) (v w : V3) : ℝ :=
  if 1 < (setOfEdge v V E).ncard then azim x v w (sigmaFan x V E v w) else 2 * Real.pi

/-- HOL fan.hl:1197 `e1_cross_e2_dot_e3_fan`：e-标架右手系。 -/
theorem e1Fan_cross_e2Fan_dot (hnc : ¬ Collinear3 x v u) :
    0 < (cross3 (e1Fan x v u) (e2Fan x v u)) ⬝ᵥ (e3Fan x v u) := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have h : cross3 (e1Fan x v u) (e2Fan x v u) = e3Fan x v u := by
    rw [e1Fan, cross3_cross3, dot_coe, dot_coe, e2Fan_dot_self hnc,
      dot_comm (e3Fan x v u) (e2Fan x v u), e2Fan_dot_e3 hnc]
    module
  rw [h, e3Fan_dot_self hvx u]
  norm_num

/-- HOL fan.hl:1205 `orthonormal_e1_e2_e3_fan`。 -/
theorem orthonormal_e1Fan_e2Fan_e3Fan (hnc : ¬ Collinear3 x v u) :
    Orthonormal3 (e1Fan x v u) (e2Fan x v u) (e3Fan x v u) := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  exact ⟨e1Fan_dot_self hnc, e2Fan_dot_self hnc, e3Fan_dot_self hvx u,
    e1Fan_dot_e2 hnc, e1Fan_dot_e3 hnc, e2Fan_dot_e3 hnc, by
      rw [← coe_cross3, dot_coe]
      exact e1Fan_cross_e2Fan_dot hnc⟩

/-- HOL topology.hl:3729 `expand_elements_by_azim_fan`：球坐标点的 azim。
经 azim_eq_of_spec（AZIM_UNIQUE 的角色）：e-标架为基准，任意 aligned
标架由 on3_axis_change 的单位复数旋转传递（同 azimSpec_exists 的
桥接模式）。 -/
theorem expand_elements_by_azim_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx2' : x2 < 2 * Real.pi)
    (hx3 : 0 < x3) (hx3' : x3 < Real.pi / 2) :
    azim x v u (x + (x1 * Real.cos x2 * Real.sin x3) • e1Fan x v u +
      (x1 * Real.sin x2 * Real.sin x3) • e2Fan x v u +
      (x1 * Real.cos x3) • e3Fan x v u) = x2 := by
  have hnc : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hframe : Orthonormal3 (e1Fan x v u) (e2Fan x v u) (e3Fan x v u) :=
    orthonormal_e1Fan_e2Fan_e3Fan hnc
  have haxf : (v - x : V3) = dist v x • e3Fan x v u := by
    rw [e3Fan, dist_eq_norm, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  -- (v-x) ⬝ᵥ e3 = ‖v - x‖
  have hvxe3 : (v - x) ⬝ᵥ e3Fan x v u = ‖v - x‖ := by
    rw [e3Fan, coe_smul, dotProduct_smul, smul_eq_mul, ← norm_sq_eq_dot]
    have h2 : ‖v - x‖⁻¹ * ‖v - x‖ ^ 2 = ‖v - x‖ := by field_simp [hnv]
    exact h2
  -- 记 y 与标架点积分量
  set y : V3 := x + (x1 * Real.cos x2 * Real.sin x3) • e1Fan x v u +
    (x1 * Real.sin x2 * Real.sin x3) • e2Fan x v u +
    (x1 * Real.cos x3) • e3Fan x v u with hy
  -- y 的 rep（zOf_of_rep 的输入形）
  have hyrep : y - x = ((x1 * Real.sin x3) * Real.cos x2) • e1Fan x v u +
      ((x1 * Real.sin x3) * Real.sin x2) • e2Fan x v u +
      ((x1 * Real.cos x3) * ‖v - x‖⁻¹) • (v - x) := by
    have h3 : (x1 * Real.cos x3) • e3Fan x v u =
        ((x1 * Real.cos x3) * ‖v - x‖⁻¹) • (v - x) := by
      rw [e3Fan, smul_smul]
    rw [show y - x = (x1 * Real.cos x2 * Real.sin x3) • e1Fan x v u +
        (x1 * Real.sin x2 * Real.sin x3) • e2Fan x v u +
        (x1 * Real.cos x3) • e3Fan x v u from by rw [hy]; module, h3]
    module
  -- u 的 rep：u - x = T1•e1 + T3•e3（e2 分量为 0），ρ = T1，τ = 0
  have hurep : u - x = (((u - x) ⬝ᵥ e1Fan x v u) * Real.cos 0) • e1Fan x v u +
      (((u - x) ⬝ᵥ e1Fan x v u) * Real.sin 0) • e2Fan x v u +
      (((u - x) ⬝ᵥ e3Fan x v u) * ‖v - x‖⁻¹) • (v - x) := by
    have hcoord := coord_eq_sum (e1Fan_dot_self hnc) (e2Fan_dot_self hnc)
      (e3Fan_dot_self hvx u) (e1Fan_dot_e2 hnc) (e1Fan_dot_e3 hnc) (e2Fan_dot_e3 hnc)
      (u - x)
    rw [dot_e2Fan hnc, zero_smul, add_zero] at hcoord
    rw [Real.cos_zero, Real.sin_zero, mul_zero, zero_smul, add_zero, mul_one]
    conv_lhs => rw [hcoord]
    rw [show (((u - x) ⬝ᵥ e3Fan x v u) * ‖v - x‖⁻¹) • (v - x) =
        ((u - x) ⬝ᵥ e3Fan x v u) • e3Fan x v u from by
      rw [e3Fan, smul_smul]]
  -- zOf 计算
  have hzy_f : zOf (e1Fan x v u) (e2Fan x v u) (y - x) =
      ((x1 * Real.sin x3 : ℝ) : ℂ) * Complex.exp (x2 * I) :=
    zOf_of_rep hframe haxf hyrep
  have hzu_f : zOf (e1Fan x v u) (e2Fan x v u) (u - x) =
      (((u - x) ⬝ᵥ e1Fan x v u : ℝ) : ℂ) * Complex.exp ((0 : ℝ) * I) :=
    zOf_of_rep hframe haxf hurep
  -- 非共线（azim_eq_of_spec 的前提）
  have h2 : ¬ Collinear3 x v y := by
    have h := (zOf_ne_zero_iff hframe haxf hvx y).mp ?_
    · exact h
    · rw [hzy_f]
      exact mul_ne_zero (by
        exact_mod_cast (mul_ne_zero hx1.ne'
          (Real.sin_pos_of_pos_of_lt_pi hx3 (by linarith [hx3', Real.pi_pos])).ne'))
        (Complex.exp_ne_zero _)
  -- 主目标经 azim_eq_of_spec
  apply azim_eq_of_spec (fan_not_collinear hfan hvu) h2
  refine ⟨hx2, hx2', ((u - x) ⬝ᵥ e3Fan x v u) / dist v x,
    (x1 * Real.cos x3) / dist v x, ?_⟩
  intro e1 e2 e3 he hax hw
  -- 同轴：e3 = e3Fan
  have he3f : e3 = e3Fan x v u := by
    have hc : dist v x ≠ 0 := dist_ne_zero.mpr hvx
    have hsub : dist v x • e3 - dist v x • e3Fan x v u = 0 := by
      rw [← hax, ← haxf, sub_self]
    rw [← smul_sub] at hsub
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left hc)
  obtain ⟨urot, hurot1, hurot⟩ := on3_axis_change he hframe he3f
  set ψ := Complex.arg urot with hψ
  have hue : urot = Complex.exp (ψ * I) := by
    have hp := Complex.norm_mul_exp_arg_mul_I urot
    rw [hurot1, Complex.ofReal_one, one_mul] at hp
    rw [hψ]
    exact hp.symm
  -- u 侧 zOf
  have hz1e : zOf e1 e2 (u - x) =
      (((u - x) ⬝ᵥ e1Fan x v u : ℝ) : ℂ) * Complex.exp ((ψ : ℂ) * I) := by
    show (u - x : V3) ⬝ᵥ e1 + (u - x : V3) ⬝ᵥ e2 * I = _
    rw [hurot (u - x),
      show (u - x : V3) ⬝ᵥ e1Fan x v u + (u - x : V3) ⬝ᵥ e2Fan x v u * I
        = zOf (e1Fan x v u) (e2Fan x v u) (u - x) from rfl]
    rw [hzu_f, hue]
    rw [show ((0 : ℝ) : ℂ) * I = (0 : ℂ) from by simp]
    rw [Complex.exp_zero, mul_one]
    ring
  -- y 侧 zOf
  have hz2e : zOf e1 e2 (y - x) =
      ((x1 * Real.sin x3 : ℝ) : ℂ) * Complex.exp (((ψ + x2 : ℝ) : ℂ) * I) := by
    show (y - x : V3) ⬝ᵥ e1 + (y - x : V3) ⬝ᵥ e2 * I = _
    rw [hurot (y - x),
      show (y - x : V3) ⬝ᵥ e1Fan x v u + (y - x : V3) ⬝ᵥ e2Fan x v u * I
        = zOf (e1Fan x v u) (e2Fan x v u) (y - x) from rfl]
    rw [hzy_f, hue, mul_left_comm, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  -- rep 回填
  have hT1 : 0 < (u - x) ⬝ᵥ e1Fan x v u := udot_e1Fan hnc
  have hr2 : 0 < x1 * Real.sin x3 :=
    mul_pos hx1 (Real.sin_pos_of_pos_of_lt_pi hx3 (by linarith [hx3', Real.pi_pos]))
  refine ⟨ψ, (u - x) ⬝ᵥ e1Fan x v u, x1 * Real.sin x3, ?_, ?_, hT1, hr2⟩
  · have hrep := rep_of_zOf he hax hw u ψ ((u - x) ⬝ᵥ e1Fan x v u) hz1e
    rw [he3f] at hrep
    exact hrep
  · have hrep := rep_of_zOf he hax hw y (ψ + x2) (x1 * Real.sin x3) hz2e
    have hye3 : (y - x) ⬝ᵥ e3Fan x v u = x1 * Real.cos x3 := by
      rw [hyrep]
      rw [← inner_eq_dot, inner_add_left, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left]
      rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, e1Fan_dot_e3 hnc,
        e2Fan_dot_e3 hnc, hvxe3]
      simp only [mul_zero, add_zero, zero_add]
      rw [mul_assoc, inv_mul_cancel₀ hnv, mul_one]
    rw [he3f, hye3] at hrep
    exact hrep

/-- azimFan ≤ 2π（两个分支：azim_lt_two_pi / 平凡）。 -/
private theorem azimFan_le_two_pi (x : V3) (V : Set V3) (E : Set (Set V3))
    (v w : V3) : azimFan x V E v w ≤ 2 * Real.pi := by
  rw [azimFan]
  by_cases hcard : 1 < (setOfEdge v V E).ncard
  · rw [if_pos hcard]
    exact le_of_lt (azim_lt_two_pi x v w _)
  · rw [if_neg hcard]

/-! ## 球坐标重建与 rw_dart 的像刻画（topology.hl:3815–4436）

arcVFan（sphere.hl:375 `arcV`）、spherical_coordinates_eFan
（Multivariate-flyspeck.ml:3572 `SPHERICAL_COORDINATES` 的 e-标架特化：
HOL 的 `(v + e1) IN aff_gt` 条件在 e1Fan 上由 (u-x)·e2Fan = 0 与
(u-x)·e1Fan > 0 自动钉住 ψ = 0）、rw_dart_is_image_set_spherical_coordinate
（本块主体）。 -/

/-- HOL sphere.hl:375 `arcV`（HOL `acs` ↔ Mathlib `Real.arccos`；
HOL 用 norm，此处用 dist——dist v u = ‖v - u‖）。 -/
noncomputable def arcVFan (u v w : V3) : ℝ :=
  Real.arccos (((v - u) ⬝ᵥ (w - u)) / (dist v u * dist w u))

/-- 标准正交组合的范数平方（Parseval）。 -/
private theorem norm_sq_combo {e1 e2 e3 : V3} (he : Orthonormal3 e1 e2 e3)
    (a b c : ℝ) : ‖a • e1 + b • e2 + c • e3‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨h1, h2, h3, h12, h13, h23, -⟩ := he
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot,
    inner_eq_dot, inner_eq_dot, inner_eq_dot, inner_eq_dot]
  rw [h1, h2, h3, h12, h13, h23, dot_comm e2 e1, h12, dot_comm e3 e1, h13,
    dot_comm e3 e2, h23]
  ring

/-- HOL Multivariate-flyspeck.ml:3572 `SPHERICAL_COORDINATES` 的 e-标架
特化：y = x + dist•(cos θ sin φ e1 + sin θ sin φ e2 + cos φ e3)，
θ = azim x v u y，φ = arcVFan x y v。 -/
private theorem spherical_coordinates_eFan (hnc1 : ¬ Collinear3 x v u)
    (hnc2 : ¬ Collinear3 x v y) :
    y = x + (dist y x * Real.cos (azim x v u y) * Real.sin (arcVFan x y v)) •
        e1Fan x v u +
      (dist y x * Real.sin (azim x v u y) * Real.sin (arcVFan x y v)) •
        e2Fan x v u +
      (dist y x * Real.cos (arcVFan x y v)) • e3Fan x v u := by
  have hvx : v ≠ x := fun he => hnc1 (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hyx0 : y ≠ x := fun he => hnc2 (collinear3_pair_left he)
  have hny : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyx0)
  have hframe := orthonormal_e1Fan_e2Fan_e3Fan hnc1
  have haxf : (v - x : V3) = ‖v - x‖ • e3Fan x v u := by
    rw [e3Fan, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have haxf' : (v - x : V3) = dist v x • e3Fan x v u := by
    rw [dist_eq_norm]; exact haxf
  -- azim_master 在 e 标架取值：u 的 rep 角度为 ψ，y 的为 ψ + azim
  obtain ⟨-, -, h1, h2, hspec⟩ := azim_master x v u y
  obtain ⟨ψ, r1, r2, hu_rep, hy_rep, hr1, hr2⟩ :=
    hspec (e1Fan x v u) (e2Fan x v u) (e3Fan x v u) hframe haxf' hvx
  -- ψ = 0：u 的 rep 的 e2 分量 = 0（dot_e2Fan）、e1 分量 > 0（udot_e1Fan）
  have hue2 : inner ℝ (u - x) (e2Fan x v u) = 0 := by
    rw [inner_eq_dot]
    exact dot_e2Fan hnc1
  have hue2' : inner ℝ (u - x) (e2Fan x v u) = r1 * Real.sin ψ := by
    conv_lhs => rw [hu_rep]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
      e1Fan_dot_e2 hnc1, e2Fan_dot_self hnc1, vdot_e2Fan hnc1]
    ring
  have hue1' : inner ℝ (u - x) (e1Fan x v u) = r1 * Real.cos ψ := by
    conv_lhs => rw [hu_rep]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
      e1Fan_dot_self hnc1, dot_comm (e2Fan x v u) (e1Fan x v u),
      e1Fan_dot_e2 hnc1, vdot_e1Fan hnc1]
    ring
  have hT1 : 0 < inner ℝ (u - x) (e1Fan x v u) := by
    rw [inner_eq_dot]
    exact udot_e1Fan hnc1
  rw [hue1'] at hT1
  have hψ0 : Real.sin ψ = 0 := by
    have h : r1 * Real.sin ψ = 0 := hue2'.symm.trans hue2
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (hr1 hnc1))
  have hψ1 : Real.cos ψ = 1 := by
    have hsc := Real.sin_sq_add_cos_sq ψ
    rw [hψ0] at hsc
    have hcos2 : Real.cos ψ ^ 2 = 1 := by linarith [hsc]
    have hcos0 : 0 < Real.cos ψ :=
      pos_of_mul_pos_right hT1 (le_of_lt (hr1 hnc1))
    rcases (sq_eq_one_iff.mp hcos2) with h | h
    · exact h
    · linarith
  have hcos : Real.cos (ψ + azim x v u y) = Real.cos (azim x v u y) := by
    rw [Real.cos_add, hψ0, hψ1]; ring
  have hsin : Real.sin (ψ + azim x v u y) = Real.sin (azim x v u y) := by
    rw [Real.sin_add, hψ0, hψ1]; ring
  rw [hcos, hsin] at hy_rep
  -- 轴分量：(y-x)·e3Fan = h2 * ‖v-x‖
  have hvxe3 : (v - x) ⬝ᵥ e3Fan x v u = ‖v - x‖ := by
    rw [e3Fan, coe_smul, dotProduct_smul, smul_eq_mul, ← norm_sq_eq_dot]
    have h2 : ‖v - x‖⁻¹ * ‖v - x‖ ^ 2 = ‖v - x‖ := by field_simp [hnv]
    exact h2
  have hye3 : inner ℝ (y - x) (e3Fan x v u) = h2 * ‖v - x‖ := by
    conv_lhs => rw [hy_rep]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
      e1Fan_dot_e3 hnc1, e2Fan_dot_e3 hnc1, hvxe3]
    ring
  -- (y-x)·(v-x) = h2·‖v-x‖²
  have hyvx : (y - x) ⬝ᵥ (v - x) = h2 * ‖v - x‖ * ‖v - x‖ := by
    have haxf2 : (WithLp.toLp 2 (v.ofLp - x.ofLp) : V3) = ‖v - x‖ • e3Fan x v u :=
      haxf
    rw [← inner_eq_dot, haxf2, real_inner_smul_right, hye3]
    ring
  -- cos φ 与 Cauchy-Schwarz 界
  have hcb : |((y - x) ⬝ᵥ (v - x)) / (dist y x * dist v x)| ≤ 1 := by
    have hdpos : (0:ℝ) < dist y x * dist v x :=
      mul_pos (dist_pos.mpr hyx0) (dist_pos.mpr hvx)
    rw [abs_div, abs_of_pos hdpos, div_le_one hdpos,
      show dist y x * dist v x = ‖y - x‖ * ‖v - x‖ from by
        rw [dist_eq_norm, dist_eq_norm], ← inner_eq_dot]
    exact abs_real_inner_le_norm _ _
  obtain ⟨hcb1, hcb2⟩ := abs_le.mp hcb
  have hcosφ : Real.cos (arcVFan x y v) =
      ((y - x) ⬝ᵥ (v - x)) / (dist y x * dist v x) := by
    rw [arcVFan]
    exact Real.cos_arccos hcb1 hcb2
  -- dist y x · cos φ = h2·‖v-x‖
  have hrcos : dist y x * Real.cos (arcVFan x y v) = h2 * ‖v - x‖ := by
    rw [hcosφ, hyvx]
    rw [show dist y x * dist v x = ‖y - x‖ * ‖v - x‖ from by
      rw [dist_eq_norm, dist_eq_norm]]
    rw [show dist y x = ‖y - x‖ from by rw [dist_eq_norm]]
    field_simp [hny, hnv]
  -- ‖y-x‖² = r2² + (h2·‖v-x‖)²（Parseval）
  have haxial : h2 • (v - x) = (h2 * ‖v - x‖) • e3Fan x v u := by
    conv_lhs => rw [haxf]
    module
  have hnorm2 : ‖y - x‖ ^ 2 = r2 ^ 2 + (h2 * ‖v - x‖) ^ 2 := by
    have hrep : y - x = (r2 * Real.cos (azim x v u y)) • e1Fan x v u +
        (r2 * Real.sin (azim x v u y)) • e2Fan x v u +
        (h2 * ‖v - x‖) • e3Fan x v u := by
      rw [hy_rep, haxial]
    have h := norm_sq_combo hframe (r2 * Real.cos (azim x v u y))
      (r2 * Real.sin (azim x v u y)) (h2 * ‖v - x‖)
    rw [← hrep] at h
    rw [h, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  -- r2 = dist y x · sin φ
  have hr2 : r2 = dist y x * Real.sin (arcVFan x y v) := by
    have h1 : (h2 * ‖v - x‖) ^ 2 = (dist y x * Real.cos (arcVFan x y v)) ^ 2 := by
      rw [hrcos]
    have hsin2 : Real.sin (arcVFan x y v) ^ 2 = 1 - Real.cos (arcVFan x y v) ^ 2 :=
      Real.sin_sq _
    have hpos : 0 ≤ dist y x * Real.sin (arcVFan x y v) :=
      mul_nonneg dist_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _)
          (Real.arccos_le_pi _))
    have hrc : dist y x = ‖y - x‖ := by rw [dist_eq_norm]
    rw [← hrc] at hnorm2
    have hsq : r2 ^ 2 = (dist y x * Real.sin (arcVFan x y v)) ^ 2 := by
      have e2 : (dist y x * Real.sin (arcVFan x y v)) ^ 2 =
          dist y x ^ 2 - (dist y x * Real.cos (arcVFan x y v)) ^ 2 := by
        rw [mul_pow, mul_pow, hsin2]; ring
      rw [e2, ← h1]
      linarith [hnorm2]
    exact (sq_eq_sq₀ (le_of_lt (hr2 hnc2)) hpos).mp hsq
  -- 终组装
  have hyfinal : y - x =
      (dist y x * Real.cos (azim x v u y) * Real.sin (arcVFan x y v)) •
        e1Fan x v u +
      (dist y x * Real.sin (azim x v u y) * Real.sin (arcVFan x y v)) •
        e2Fan x v u +
      (dist y x * Real.cos (arcVFan x y v)) • e3Fan x v u := by
    rw [hy_rep, haxial, hr2, hrcos]
    module
  conv_lhs => rw [show y = x + (y - x) from by module]
  rw [hyfinal]
  module

/-- HOL topology.hl:3815 `rw_dart_is_image_set_spherical_coordinate`：
球坐标映射在 r_fan 上的像 = rw_dart（CARD > 1 时为 wedge ∩ rcone(cos h)，
CARD ≤ 1 时为 `univ \ aff_ge {x,v} {u}` ∩ rcone(cos h)）。
证明重构：正向用 expand_elements_by_azim_fan（azim = t 1）、
norm_sq_combo（dist = t 0）与 cos 在 [0,π] 严格递减（rcone 成员）；
CARD ≤ 1 分支用 AZIM_EQ_0_GE_ALT（azim_eq_zero_iff_alt）排除 affGe。
反向取证人 t = (dist y x, azim x v u y, arcVFan x y v)：arcV ∈ (0, h) 由
rcone 条件 + 严格 Cauchy–Schwarz（inner_lt_norm_mul_iff_real，非共线
给出严格性）+ arccos 在 [-1,1] 严格递减；重建等式即
spherical_coordinates_eFan。 -/
theorem rw_dart_is_image_set_spherical_coordinate (hfan : FAN x V E)
    (hvu : {v, u} ∈ E) (h0 : 0 < h) (h1 : h < Real.pi / 2) :
    changeSphericalCoordinateFan x v u ''
        rFan (azim x v u u) (azimFan x V E v u) h =
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos h) := by
  have hnc : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hxv : x ≠ v := fan_x_ne_v hfan hvu
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hnvpos : 0 < ‖v - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvx)
  have hframe := orthonormal_e1Fan_e2Fan_e3Fan hnc
  have haxf : (v - x : V3) = ‖v - x‖ • e3Fan x v u := by
    rw [e3Fan, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have hazu : azim x v u u = 0 := azim_self x v u
  have hdisj : Disjoint ({x, v} : Set V3) {u} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun he => hnc (collinear3_pair_left he),
      fun he => hnc (collinear3_pair_right he)⟩
  ext y
  constructor
  · -- 正向：像 ⊆ rwDart
    rintro ⟨t, ht, rfl⟩
    simp only [rFan, Set.mem_setOf_eq] at ht
    obtain ⟨ht0, ht1lo, ht1hi, ht2lo, ht2hi⟩ := ht
    rw [hazu] at ht1lo
    have ht1lt : t 1 < 2 * Real.pi :=
      lt_of_lt_of_le ht1hi (azimFan_le_two_pi x V E v u)
    have ht2lt : t 2 < Real.pi / 2 := lt_trans ht2hi h1
    have hs2 : 0 < Real.sin (t 2) :=
      Real.sin_pos_of_pos_of_lt_pi ht2lo (by have := Real.pi_pos; linarith)
    -- y - x 的分量展开
    have hyrep : changeSphericalCoordinateFan x v u t - x =
        (t 0 * Real.cos (t 1) * Real.sin (t 2)) • e1Fan x v u +
        (t 0 * Real.sin (t 1) * Real.sin (t 2)) • e2Fan x v u +
        (t 0 * Real.cos (t 2)) • e3Fan x v u := by
      rw [show changeSphericalCoordinateFan x v u t = x +
          (t 0 * Real.cos (t 1) * Real.sin (t 2)) • e1Fan x v u +
          (t 0 * Real.sin (t 1) * Real.sin (t 2)) • e2Fan x v u +
          (t 0 * Real.cos (t 2)) • e3Fan x v u from rfl]
      module
    -- azim y = t 1
    have hyaz : azim x v u (changeSphericalCoordinateFan x v u t) = t 1 :=
      expand_elements_by_azim_fan hfan hvu (t 0) (t 1) (t 2) ht0 (le_of_lt ht1lo)
        ht1lt ht2lo ht2lt
    -- 非共线：共线 ⟹ y - x 平行 v - x ⟹ e1/e2 分量同零，与 sin²+cos²=1 矛盾
    have hncy : ¬ Collinear3 x v (changeSphericalCoordinateFan x v u t) := by
      intro hc
      obtain ⟨c, hc⟩ := (collinear3_iff_smul (w := v) (v := x) hvx).mp hc
      have hd1 : inner ℝ (changeSphericalCoordinateFan x v u t - x) (e1Fan x v u) =
          t 0 * Real.cos (t 1) * Real.sin (t 2) := by
        conv_lhs => rw [hyrep]
        rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
          e1Fan_dot_self hnc, dot_comm (e2Fan x v u) (e1Fan x v u), e1Fan_dot_e2 hnc,
          dot_comm (e3Fan x v u) (e1Fan x v u), e1Fan_dot_e3 hnc]
        ring
      have hd1' : inner ℝ (changeSphericalCoordinateFan x v u t - x) (e1Fan x v u) =
          0 := by
        conv_lhs => rw [hc]
        rw [real_inner_smul_left, inner_eq_dot, vdot_e1Fan hnc, mul_zero]
      have hcos0 : Real.cos (t 1) = 0 := by
        have hh := hd1.symm.trans hd1'
        rcases mul_eq_zero.mp hh with hh | hh
        · rcases mul_eq_zero.mp hh with hh | hh
          · exact absurd hh (ne_of_gt ht0)
          · exact hh
        · exact absurd hh (ne_of_gt hs2)
      have hd2 : inner ℝ (changeSphericalCoordinateFan x v u t - x) (e2Fan x v u) =
          t 0 * Real.sin (t 1) * Real.sin (t 2) := by
        conv_lhs => rw [hyrep]
        rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
          e1Fan_dot_e2 hnc, e2Fan_dot_self hnc,
          dot_comm (e3Fan x v u) (e2Fan x v u), e2Fan_dot_e3 hnc]
        ring
      have hd2' : inner ℝ (changeSphericalCoordinateFan x v u t - x) (e2Fan x v u) =
          0 := by
        conv_lhs => rw [hc]
        rw [real_inner_smul_left, inner_eq_dot, vdot_e2Fan hnc, mul_zero]
      have hsin0 : Real.sin (t 1) = 0 := by
        have hh := hd2.symm.trans hd2'
        rcases mul_eq_zero.mp hh with hh | hh
        · rcases mul_eq_zero.mp hh with hh | hh
          · exact absurd hh (ne_of_gt ht0)
          · exact hh
        · exact absurd hh (ne_of_gt hs2)
      have hsc := Real.sin_sq_add_cos_sq (t 1)
      rw [hsin0, hcos0] at hsc
      norm_num at hsc
    -- dist y x = t 0（Parseval + 三角恒等式）
    have hdist : dist (changeSphericalCoordinateFan x v u t) x = t 0 := by
      have h2 := norm_sq_combo hframe (t 0 * Real.cos (t 1) * Real.sin (t 2))
        (t 0 * Real.sin (t 1) * Real.sin (t 2)) (t 0 * Real.cos (t 2))
      rw [← hyrep] at h2
      have htrig : (t 0 * Real.cos (t 1) * Real.sin (t 2)) ^ 2 +
          (t 0 * Real.sin (t 1) * Real.sin (t 2)) ^ 2 + (t 0 * Real.cos (t 2)) ^ 2 =
          t 0 ^ 2 := by
        have e1 : (t 0 * Real.cos (t 1) * Real.sin (t 2)) ^ 2 +
            (t 0 * Real.sin (t 1) * Real.sin (t 2)) ^ 2 =
            t 0 ^ 2 * Real.sin (t 2) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, ← add_mul, ← mul_add,
            Real.cos_sq_add_sin_sq, mul_one]
        rw [e1, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
      rw [dist_eq_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) (le_of_lt ht0)).mp (h2.trans htrig)
    -- e3 分量与 rcone 点积
    have hye3 : inner ℝ (changeSphericalCoordinateFan x v u t - x) (e3Fan x v u) =
        t 0 * Real.cos (t 2) := by
      conv_lhs => rw [hyrep]
      rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, inner_eq_dot, inner_eq_dot, inner_eq_dot,
        e1Fan_dot_e3 hnc, e2Fan_dot_e3 hnc, e3Fan_dot_self hvx u]
      ring
    have hyvx : (changeSphericalCoordinateFan x v u t - x) ⬝ᵥ (v - x) =
        ‖v - x‖ * (t 0 * Real.cos (t 2)) := by
      have haxf2 : (WithLp.toLp 2 (v.ofLp - x.ofLp) : V3) = ‖v - x‖ • e3Fan x v u :=
        haxf
      rw [← inner_eq_dot, haxf2, real_inner_smul_right, hye3]
    -- 组装 wDart ∩ rcone
    rw [rwDartFan]
    refine ⟨?_, ?_⟩
    · rw [wDartFan]
      by_cases hcard : 1 < (setOfEdge v V E).ncard
      · rw [if_pos (show (setOfEdge v V E).ncard > 1 from hcard)]
        rw [wedge, Set.mem_setOf_eq]
        show ¬ Collinear3 x v (changeSphericalCoordinateFan x v u t) ∧
          0 < azim x v u (changeSphericalCoordinateFan x v u t) ∧
          azim x v u (changeSphericalCoordinateFan x v u t) <
            azim x v u (sigmaFan x V E v u)
        refine ⟨hncy, by rw [hyaz]; exact ht1lo, ?_⟩
        rw [hyaz]
        rw [azimFan, if_pos hcard] at ht1hi
        exact ht1hi
      · have hsoe := one_edge_fan hfan hvu hcard
        rw [if_neg (show ¬ (setOfEdge v V E).ncard > 1 from hcard), if_pos hsoe]
        rw [Set.mem_sdiff]
        refine ⟨Set.mem_univ _, fun hge => ?_⟩
        obtain ⟨t1, t2, t3, ht3, hsum, hycombo⟩ := (mem_affGe_pair hdisj hxv).mp hge
        rcases eq_or_lt_of_le ht3 with ht3 | ht3
        · subst ht3
          apply hncy
          rw [collinear3_iff_mem_affineSpan hxv, affine_hull_2_fan]
          refine ⟨t1, t2, by linarith, ?_⟩
          rw [hycombo, zero_smul, add_zero]
        · have hxu : x ≠ u := fun he => hnc (collinear3_pair_left he.symm)
          have hvu' : v ≠ u := fun he => hnc (collinear3_pair_right he.symm)
          have hgt := affGt_of_triple t1 t2 t3 ht3 hsum hycombo hxv hxu hvu'
          have haz0 := (azim_eq_zero_iff_alt hnc hncy).mpr hgt
          rw [hyaz] at haz0
          linarith
    · show (changeSphericalCoordinateFan x v u t - x) ⬝ᵥ (v - x) >
        dist (changeSphericalCoordinateFan x v u t) x * dist v x * Real.cos h
      rw [hyvx, hdist, show dist v x = ‖v - x‖ from by rw [dist_eq_norm]]
      have hcos : Real.cos h < Real.cos (t 2) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt ht2lo)
          (by have := Real.pi_pos; linarith) ht2hi
      calc t 0 * ‖v - x‖ * Real.cos h < t 0 * ‖v - x‖ * Real.cos (t 2) :=
            mul_lt_mul_of_pos_left hcos (mul_pos ht0 hnvpos)
        _ = ‖v - x‖ * (t 0 * Real.cos (t 2)) := by ring
  · -- 反向：rwDart ⊆ 像
    intro hy
    rw [rwDartFan, Set.mem_inter_iff] at hy
    obtain ⟨hyw, hyr⟩ := hy
    have hyr' : (y - x) ⬝ᵥ (v - x) > dist y x * dist v x * Real.cos h := hyr
    have hyx : y ≠ x := by
      intro he
      rw [he, sub_self, zero_dot, dist_self, zero_mul, zero_mul] at hyr'
      exact lt_irrefl 0 hyr'
    have hdy : 0 < dist y x := dist_pos.mpr hyx
    have hdpos : (0:ℝ) < dist y x * dist v x := mul_pos hdy (dist_pos.mpr hvx)
    rw [wDartFan] at hyw
    -- 公共尾段：给定非共线与 azim 界，构造证人
    have tail : ¬ Collinear3 x v y → azim x v u u < azim x v u y →
        azim x v u y < azimFan x V E v u →
        y ∈ changeSphericalCoordinateFan x v u ''
          rFan (azim x v u u) (azimFan x V E v u) h := by
      intro hncy hazlo hazhi
      -- Cauchy–Schwarz 界：比值 ∈ [-1, 1]
      have hzabs : |(y - x) ⬝ᵥ (v - x) / (dist y x * dist v x)| ≤ 1 := by
        rw [abs_div, abs_of_pos hdpos, div_le_one hdpos,
          show dist y x * dist v x = ‖y - x‖ * ‖v - x‖ from by
            rw [dist_eq_norm, dist_eq_norm], ← inner_eq_dot]
        exact abs_real_inner_le_norm _ _
      have hzmem : (y - x) ⬝ᵥ (v - x) / (dist y x * dist v x) ∈ Set.Icc (-1) 1 :=
        Set.mem_Icc.mpr (abs_le.mp hzabs)
      -- 严格 < 1（非共线 ⟹ 严格 Cauchy–Schwarz）
      have hzlt : (y - x) ⬝ᵥ (v - x) / (dist y x * dist v x) < 1 := by
        rw [div_lt_one hdpos,
          show dist y x * dist v x = ‖y - x‖ * ‖v - x‖ from by
            rw [dist_eq_norm, dist_eq_norm], ← inner_eq_dot,
          show (WithLp.toLp 2 (v.ofLp - x.ofLp) : V3) = v - x from rfl,
          inner_lt_norm_mul_iff_real]
        intro heq
        apply hncy
        refine (collinear3_iff_smul (w := v) (v := x) hvx).mpr ⟨‖y - x‖ / ‖v - x‖, ?_⟩
        have e2 : y - x = (‖y - x‖ / ‖v - x‖) • (v - x) := by
          have e3 : (‖y - x‖ / ‖v - x‖) • (v - x) = ‖v - x‖⁻¹ • (‖y - x‖ • (v - x)) := by
            rw [div_eq_mul_inv, mul_comm ‖y - x‖ ‖v - x‖⁻¹, ← smul_smul]
          rw [e3, ← heq, smul_smul, inv_mul_cancel₀ hnv, one_smul]
        exact e2
      -- arcV ∈ (0, h)
      have hpos_arc : 0 < arcVFan x y v := by
        show 0 < Real.arccos (((y - x) ⬝ᵥ (v - x)) / (dist y x * dist v x))
        have hanti := Real.strictAntiOn_arccos hzmem
          (show (1:ℝ) ∈ Set.Icc (-1) 1 from ⟨by norm_num, le_refl 1⟩) hzlt
        rw [Real.arccos_one] at hanti
        exact hanti
      have harclt : arcVFan x y v < h := by
        have hcoslt : Real.cos h < (y - x) ⬝ᵥ (v - x) / (dist y x * dist v x) := by
          rw [lt_div_iff₀ hdpos]
          calc Real.cos h * (dist y x * dist v x) = dist y x * dist v x * Real.cos h :=
                by ring
            _ < (y - x) ⬝ᵥ (v - x) := hyr'
        have hanti := Real.strictAntiOn_arccos
          (show Real.cos h ∈ Set.Icc (-1) 1 from ⟨Real.neg_one_le_cos h, Real.cos_le_one h⟩)
          hzmem hcoslt
        rw [Real.arccos_cos (le_of_lt h0) (by have := Real.pi_pos; linarith)] at hanti
        show Real.arccos (((y - x) ⬝ᵥ (v - x)) / (dist y x * dist v x)) < h
        exact hanti
      -- 证人与重建等式
      refine ⟨WithLp.toLp 2 ![dist y x, azim x v u y, arcVFan x y v], ?_, ?_⟩
      · simp only [rFan, Set.mem_setOf_eq]
        exact ⟨hdy, hazlo, hazhi, hpos_arc, harclt⟩
      · show x + (dist y x * Real.cos (azim x v u y) * Real.sin (arcVFan x y v)) •
            e1Fan x v u +
          (dist y x * Real.sin (azim x v u y) * Real.sin (arcVFan x y v)) •
            e2Fan x v u +
          (dist y x * Real.cos (arcVFan x y v)) • e3Fan x v u = y
        exact (spherical_coordinates_eFan hnc hncy).symm
    by_cases hcard : 1 < (setOfEdge v V E).ncard
    · rw [if_pos (show (setOfEdge v V E).ncard > 1 from hcard)] at hyw
      rw [wedge, Set.mem_setOf_eq] at hyw
      obtain ⟨hncy, hazlo, hazhi⟩ := hyw
      refine tail hncy (by rw [hazu]; exact hazlo) ?_
      rw [azimFan, if_pos hcard]
      exact hazhi
    · have hsoe := one_edge_fan hfan hvu hcard
      rw [if_neg (show ¬ (setOfEdge v V E).ncard > 1 from hcard), if_pos hsoe] at hyw
      rw [Set.mem_sdiff] at hyw
      obtain ⟨-, hyw⟩ := hyw
      have hncy : ¬ Collinear3 x v y := fun hc =>
        hyw (aff_subset_aff_ge hdisj ((collinear3_iff_mem_affineSpan hxv).mp hc))
      refine tail hncy ?_ ?_
      · rw [hazu]
        rcases eq_or_lt_of_le (azim_nonneg x v u y) with h0' | h0'
        · exfalso
          exact hyw (affGt_subset_affGe _ _ ((azim_eq_zero_iff_alt hnc hncy).mp h0'.symm))
        · exact h0'
      · rw [azimFan, if_neg hcard]
        exact azim_lt_two_pi x v u y

/-! ## rw_dart 的连通性、非空与 dart_leads_into（topology.hl:4436–4718，收尾）

continuous_changeSphericalCoordinateFan（3673，block 18 跳过的前置，
connected_rw_dart_fan 需要）；connected_rw_dart_fan（4436）；
not_empty_rw_dart_fan（4477）；JGIYDLE（4526，四件打包）；
dartLeadsInto（4555 定义，ε-算子）；exists_leads_into_fan（4565）；
dartLeadsInto_spec（4619 `DART_LEADS_INTO`）；
unique_dart_leads_into（4632）；
dart_leads_into_mem_topologicalComponentYfan（4670）；
isPreconnected_of_mem_topologicalComponentYfan（4704）；
connected_dart_leads_into_fan（4711）。
约定：HOL `connected` ↔ Mathlib `IsPreconnected`（沿用
r_is_connected_fan 的注释；HOL 空集连通，Mathlib `IsConnected` 额外要求
Nonempty）；HOL `connected_component s y` ↔ `connectedComponentIn s y`。 -/

/-- HOL topology.hl:3673 `continuous_change_spherical_coordinate_fan`
（HOL 逐点 `continuous at x`，此处取全局连续形；连通像论证只需
ContinuousOn）。分量映射连续（PiLp.continuous_apply）+ 三角/乘法/
数乘/加法封闭性。 -/
theorem continuous_changeSphericalCoordinateFan (x v u : V3) :
    Continuous (changeSphericalCoordinateFan x v u) := by
  have hc : ∀ i : Fin 3, Continuous fun t : V3 => t i :=
    fun i => PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) i
  show Continuous fun t : V3 => x + (t (0 : Fin 3) * Real.cos (t (1 : Fin 3)) *
      Real.sin (t (2 : Fin 3))) • e1Fan x v u +
    (t (0 : Fin 3) * Real.sin (t (1 : Fin 3)) * Real.sin (t (2 : Fin 3))) •
      e2Fan x v u +
    (t (0 : Fin 3) * Real.cos (t (2 : Fin 3))) • e3Fan x v u
  refine ((continuous_const.add ?_).add ?_).add ?_
  · exact (((hc 0).mul (Real.continuous_cos.comp (hc 1))).mul
      (Real.continuous_sin.comp (hc 2))).smul continuous_const
  · exact (((hc 0).mul (Real.continuous_sin.comp (hc 1))).mul
      (Real.continuous_sin.comp (hc 2))).smul continuous_const
  · exact ((hc 0).mul (Real.continuous_cos.comp (hc 2))).smul continuous_const

/-- HOL topology.hl:4436 `connected_rw_dart_fan`：0 < h < π/2 时
rw_dart(cos h) 预连通。经 rw_dart_is_image_set_spherical_coordinate 化为
rFan 的连续像；rFan 凸 ⟹ 预连通（r_is_connected_fan）。 -/
theorem connected_rw_dart_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (h0 : 0 < h) (h1 : h < Real.pi / 2) :
    IsPreconnected (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos h)) := by
  rw [← rw_dart_is_image_set_spherical_coordinate hfan hvu h0 h1]
  exact (r_is_connected_fan _ _ _).1.image _
    (continuous_changeSphericalCoordinateFan x v u).continuousOn

/-- HOL topology.hl:4477 `not_empty_rw_dart_fan`：0 < h < π/2 时
rw_dart(cos h) 非空（HOL `~(... = {})` ↔ `Set.Nonempty`）。经像刻画化为
rFan 非空：CARD > 1 时 azimFan = azim x v u (σu) > 0（azim = 0 会导致
u = σu，与 key_lemma_cyclic 矛盾），证人 (1, azim/2, h/2)；CARD ≤ 1 时
azimFan = 2π，证人 (1, π, h/2)。 -/
theorem not_empty_rw_dart_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (h0 : 0 < h) (h1 : h < Real.pi / 2) :
    (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos h)).Nonempty := by
  rw [← rw_dart_is_image_set_spherical_coordinate hfan hvu h0 h1]
  apply Set.Nonempty.image
  by_cases hcard : 1 < (setOfEdge v V E).ncard
  · -- CARD > 1：azimFan = azim x v u (σu)
    have hσedge : {v, sigmaFan x V E v u} ∈ E := by
      have hm := sigma_fan_in_setOfEdge hfan
        ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu)
      simp only [setOfEdge, Set.mem_setOf_eq] at hm
      exact hm.1
    have hazim_pos : 0 < azim x v u (sigmaFan x V E v u) := by
      rcases eq_or_lt_of_le (azim_nonneg x v u (sigmaFan x V E v u)) with h0' | h0'
      · exfalso
        have hσu : u = sigmaFan x V E v u :=
          unique_azim0_point_fan hfan hvu hσedge h0'.symm
        have h1ne := key_lemma_cyclic x V E hfan hvu 1 (by norm_num) hcard
        apply h1ne
        show sigmaFan x V E v u = u
        exact hσu.symm
      · exact h0'
    refine ⟨WithLp.toLp 2 ![1, azim x v u (sigmaFan x V E v u) / 2, h / 2], ?_⟩
    rw [rFan, azimFan, if_pos hcard, azim_self]
    simp only [Set.mem_setOf_eq]
    exact ⟨zero_lt_one, half_pos hazim_pos, half_lt_self hazim_pos,
      half_pos h0, half_lt_self h0⟩
  · -- CARD ≤ 1：azimFan = 2π
    refine ⟨WithLp.toLp 2 ![1, Real.pi, h / 2], ?_⟩
    rw [rFan, azimFan, if_neg hcard, azim_self]
    simp only [Set.mem_setOf_eq]
    exact ⟨zero_lt_one, Real.pi_pos, lt_two_mul_self Real.pi_pos,
      half_pos h0, half_lt_self h0⟩

/-- HOL topology.hl:4526 `JGIYDLE`：rw_dart 的四项性质打包（非空、
随半径单调缩小、某半径避开 yfan、预连通）。 -/
theorem jgiydle (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    (∀ h : ℝ, 0 < h → h < Real.pi / 2 →
      (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos h)).Nonempty) ∧
    (∀ h h1 : ℝ, h1 ≤ h →
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) h ⊆
        rwDartFan x V E (x, v, u, sigmaFan x V E v u) h1) ∧
    (∃ h : ℝ, 1 > h ∧ h > 0 ∧
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) h ⊆ yfan x V E) ∧
    (∀ h : ℝ, 0 < h → h < Real.pi / 2 →
      IsPreconnected (rwDartFan x V E (x, v, u, sigmaFan x V E v u)
        (Real.cos h))) :=
  ⟨fun h h0 h1 => not_empty_rw_dart_fan hfan hvu h0 h1,
   fun h h1 hle => continuous_set_fan hfan hvu h h1 hle,
   rw_dart_avoids_fan hfan hvu,
   fun h h0 h1 => connected_rw_dart_fan hfan hvu h0 h1⟩

/-- HOL topology.hl:4555 `dart_leads_into`（HOL `@U` 选择算子 ↔
`Classical.epsilon`）：dart (x,v,u) 引导进入的 yfan 连通分量。 -/
noncomputable def dartLeadsInto (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u : V3) : Set V3 :=
  Classical.epsilon (fun U : Set V3 => ∃ h : ℝ, 0 < h ∧ ∀ (s : ℝ) (y : V3),
    0 < s → s < h →
      y ∈ rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) →
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆ U ∧
        connectedComponentIn (yfan x V E) y = U)

/-- HOL topology.hl:4565 `exists_leads_into_fan`：dart_leads_into 的
刻画性质可满足。取 h'（rw_dart_avoids_fan 的半径）的 arccos 作为阈值：
s < arccos h' ⟹ cos s > h' ⟹ rwDart(cos s) ⊆ rwDart(h') ⊆ yfan；
rwDart(cos s) 预连通 ⟹ 落在 y 的连通分量里。 -/
theorem exists_leads_into_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    ∃ U : Set V3, ∃ h : ℝ, 0 < h ∧ ∀ (s : ℝ) (y : V3),
      0 < s → s < h →
        y ∈ rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) →
        rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆ U ∧
          connectedComponentIn (yfan x V E) y = U := by
  obtain ⟨hEM, hmono, ⟨h, hh1, hh0, hsuby⟩, hconn⟩ := jgiydle hfan hvu
  have hb1 : -1 ≤ h := by linarith [hh0]
  have hb2 : h ≤ 1 := le_of_lt hh1
  have hac0 : 0 < Real.arccos h := Real.arccos_pos.mpr hh1
  have haclt : Real.arccos h < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hh0
  have hcosac : Real.cos (Real.arccos h) = h := Real.cos_arccos hb1 hb2
  obtain ⟨x', hx'⟩ := hEM (Real.arccos h) hac0 haclt
  rw [hcosac] at hx'
  refine ⟨connectedComponentIn (yfan x V E) x', Real.arccos h, hac0, ?_⟩
  intro s y hs0 hslt hy
  -- h < cos s（cos 在 [0,π] 严格递减）
  have hcos : h < Real.cos s := by
    have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hs0)
      (Real.arccos_le_pi h) hslt
    rw [hcosac] at h2
    exact h2
  have hsub1 : rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) h :=
    hmono _ _ (le_of_lt hcos)
  -- rwDart(h) ⊆ component x'
  have hxg : rwDartFan x V E (x, v, u, sigmaFan x V E v u) h ⊆
      connectedComponentIn (yfan x V E) x' := by
    have hpre : IsPreconnected (rwDartFan x V E (x, v, u, sigmaFan x V E v u) h) := by
      have hh := hconn (Real.arccos h) hac0 haclt
      rwa [hcosac] at hh
    exact hpre.subset_connectedComponentIn hx' hsuby
  have hymem : y ∈ connectedComponentIn (yfan x V E) x' := hxg (hsub1 hy)
  refine ⟨?_, (connectedComponentIn_eq hymem).symm⟩
  have hpre2 := hconn s hs0 (lt_trans hslt haclt)
  have hsub2 : rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆
      yfan x V E := fun z hz => hsuby (hsub1 hz)
  have hthis := hpre2.subset_connectedComponentIn hy hsub2
  rwa [← connectedComponentIn_eq hymem] at hthis

/-- HOL topology.hl:4619 `DART_LEADS_INTO`：dartLeadsInto 满足其
刻画性质（ε-算子规范）。 -/
theorem dartLeadsInto_spec (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    ∃ h : ℝ, 0 < h ∧ ∀ (s : ℝ) (y : V3), 0 < s → s < h →
      y ∈ rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) →
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆
        dartLeadsInto x V E v u ∧
        connectedComponentIn (yfan x V E) y = dartLeadsInto x V E v u :=
  Classical.epsilon_spec (exists_leads_into_fan hfan hvu)

/-- HOL topology.hl:4632 `unique_dart_leads_into`：满足刻画性质的集合
唯一（取 s = min (min h h'/2) (π/3)，落在两个阈值之内，用非空公共点
的连通分量传递相等）。 -/
theorem unique_dart_leads_into (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (U : Set V3)
    (hU : ∃ h : ℝ, 0 < h ∧ ∀ (s : ℝ) (y : V3), 0 < s → s < h →
      y ∈ rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) →
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ⊆ U ∧
        connectedComponentIn (yfan x V E) y = U) :
    dartLeadsInto x V E v u = U := by
  obtain ⟨h', hh'0, hU'⟩ := hU
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec hfan hvu
  have hEM := (jgiydle hfan hvu).1
  have hpi : 0 < Real.pi := Real.pi_pos
  set s := min (min h h' / 2) (Real.pi / 3) with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact lt_min (div_pos (lt_min hh0 hh'0) two_pos) (by positivity)
  have hslt_h : s < h := by
    rw [hsdef]
    exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le (half_lt_self (lt_min hh0 hh'0)) (min_le_left _ _))
  have hslt_h' : s < h' := by
    rw [hsdef]
    exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le (half_lt_self (lt_min hh0 hh'0)) (min_le_right _ _))
  have hslt_pi2 : s < Real.pi / 2 := by
    rw [hsdef]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  obtain ⟨x', hx'⟩ := hEM s hs0 hslt_pi2
  obtain ⟨-, heq1⟩ := hspec s x' hs0 hslt_h hx'
  obtain ⟨-, heq2⟩ := hU' s x' hs0 hslt_h' hx'
  exact heq1.symm.trans heq2

/-- HOL topology.hl:4670
`dart_leads_into_fan_in_topological_component_yfan`：dartLeadsInto 是
yfan 的一个拓扑分量（取 h1 = min h (arccos h')/2 使 cos h1 > h'，
rwDart(cos h1) ⊆ rwDart(h') ⊆ yfan，其中的点 y 落在 yfan 且其分量
正是 dartLeadsInto）。 -/
theorem dart_leads_into_mem_topologicalComponentYfan (hfan : FAN x V E)
    (hvu : {v, u} ∈ E) :
    dartLeadsInto x V E v u ∈ topologicalComponentYfan x V E := by
  obtain ⟨h', hh'1, hh'0, hsub'⟩ := rw_dart_avoids_fan hfan hvu
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec hfan hvu
  have hEM := (jgiydle hfan hvu).1
  have hb'1 : -1 ≤ h' := by linarith [hh'0]
  have hb'2 : h' ≤ 1 := le_of_lt hh'1
  have hac0 : 0 < Real.arccos h' := Real.arccos_pos.mpr hh'1
  have haclt : Real.arccos h' < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hh'0
  have hcosac : Real.cos (Real.arccos h') = h' := Real.cos_arccos hb'1 hb'2
  -- h1 := min h (arccos h') / 2
  have hh10 : 0 < min h (Real.arccos h') / 2 :=
    div_pos (lt_min hh0 hac0) two_pos
  have hh1lt : min h (Real.arccos h') / 2 < h :=
    lt_of_lt_of_le (half_lt_self (lt_min hh0 hac0)) (min_le_left _ _)
  have hh1ac : min h (Real.arccos h') / 2 < Real.arccos h' :=
    lt_of_lt_of_le (half_lt_self (lt_min hh0 hac0)) (min_le_right _ _)
  have hh1pi : min h (Real.arccos h') / 2 < Real.pi / 2 := lt_trans hh1ac haclt
  -- h' ≤ cos h1
  have hle : h' ≤ Real.cos (min h (Real.arccos h') / 2) := by
    have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hh10)
      (Real.arccos_le_pi h') hh1ac
    rw [hcosac] at h2
    exact le_of_lt h2
  obtain ⟨y, hy⟩ := hEM _ hh10 hh1pi
  have hsub1 : rwDartFan x V E (x, v, u, sigmaFan x V E v u)
        (Real.cos (min h (Real.arccos h') / 2)) ⊆
      rwDartFan x V E (x, v, u, sigmaFan x V E v u) h' :=
    (jgiydle hfan hvu).2.1 _ _ hle
  obtain ⟨-, heq⟩ := hspec _ y hh10 hh1lt hy
  have hyg : y ∈ yfan x V E := hsub' (hsub1 hy)
  exact ⟨y, hyg, heq⟩

/-- HOL topology.hl:4704 `in_topological_component_yfan_is_connected`。 -/
theorem isPreconnected_of_mem_topologicalComponentYfan {U : Set V3}
    (h : U ∈ topologicalComponentYfan x V E) : IsPreconnected U := by
  obtain ⟨b, -, rfl⟩ := h
  exact isPreconnected_connectedComponentIn

/-- HOL topology.hl:4711 `connected_dart_leads_into_fan`。 -/
theorem connected_dart_leads_into_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    IsPreconnected (dartLeadsInto x V E v u) :=
  isPreconnected_of_mem_topologicalComponentYfan
    (dart_leads_into_mem_topologicalComponentYfan hfan hvu)

end Kepler.Text
