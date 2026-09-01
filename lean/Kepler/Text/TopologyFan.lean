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

set_option maxHeartbeats 3000000

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

end Kepler.Text
