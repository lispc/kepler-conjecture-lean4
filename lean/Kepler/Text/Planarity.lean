/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter).

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (block 1, continuity/openness preliminaries, lines 35–122):
- `collinear_continuous_fan` (35): continuity of a combination path.
- `collinear1_continuous_fan` (54): pointwise continuity of a path.
- `CONTINUOUS_CLOSED_PREIMAGE_CONSTANT` (71): level set in a closed set.
- `vector_angle` (Multivariate-geom.ml:24, HOL library) ↦ `vectorAngle`;
  `REAL_CONTINUOUS_AT_VECTOR_ANGLE` (Multivariate-geom.ml:293) ↦
  `continuousAt_vectorAngle`.
- `open_vector_angle_fan` (83): openness of a non-level set of angles.

Conventions: HOL line numbers in the head comment of each item; zero
`sorry`/`native_decide`/new axioms; `lake build Kepler` green before
each commit.
-/
import Kepler.Text.TopologyFan

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open scoped Topology

variable {x v u w : V3} {V : Set V3} {E : Set (Set V3)}

/-- HOL planarity.hl:35 `collinear_continuous_fan`（HOL `real^1`/`drop`
↔ 此处取 `ℝ` 参数；`continuous_on univ` ↔ `ContinuousOn _ Set.univ`）。 -/
theorem collinear_continuous_fan (x v u w : V3) (c : ℝ) :
    ContinuousOn (fun t : ℝ => (1 - t) • u + t • w - (1 - c) • x - c • v)
      Set.univ := by
  continuity

/-- HOL planarity.hl:54 `collinear1_continuous_fan`（`continuous at t`
↔ `ContinuousAt`）。 -/
theorem collinear1_continuous_fan (u w : V3) (t : ℝ) :
    ContinuousAt (fun s : ℝ => (1 - s) • u + s • w) t :=
  (by continuity : Continuous fun s : ℝ => (1 - s) • u + s • w).continuousAt

/-- HOL planarity.hl:71 `CONTINUOUS_CLOSED_PREIMAGE_CONSTANT`：闭集上的
连续函数的水平集闭（Mathlib `ContinuousOn.preimage_isClosed_of_isClosed`
+ `isClosed_singleton`）。 -/
theorem continuous_closed_preimage_constant {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [T1Space N] {f : M → N} {s : Set M} {a : N}
    (hf : ContinuousOn f s) (hs : IsClosed s) :
    IsClosed {y ∈ s | f y = a} := by
  have : {y ∈ s | f y = a} = s ∩ f ⁻¹' {a} := by
    ext y
    simp [Set.mem_preimage, Set.mem_singleton_iff, and_comm]
  rw [this]
  exact hf.preimage_isClosed_of_isClosed hs isClosed_singleton

/-- HOL `vector_angle`（Multivariate-geom.ml:24，HOL 库级定义；
planarity.hl 自 83 行起大量使用）。非零向量夹角，退化时取 π/2。 -/
noncomputable def vectorAngle (x y : V3) : ℝ :=
  if x = 0 ∨ y = 0 then Real.pi / 2
  else Real.arccos ((x ⬝ᵥ y) / (‖x‖ * ‖y‖))

/-- HOL `REAL_CONTINUOUS_AT_VECTOR_ANGLE`（Multivariate-geom.ml:293）：
vector_angle 第二分量在非零处连续。c = 0 时为常值 π/2；c ≠ 0 且
x ≠ 0 时局部等于 arccos 商形式，由连续函数复合给出。 -/
theorem continuousAt_vectorAngle (c : V3) {x : V3} (hx : x ≠ 0) :
    ContinuousAt (vectorAngle c) x := by
  by_cases hc : c = 0
  · have hconst : vectorAngle c = fun _ => Real.pi / 2 := by
      funext y
      rw [vectorAngle, if_pos (Or.inl hc)]
    rw [hconst]
    exact continuousAt_const
  · have hne : ∀ᶠ y in 𝓝 x, y ≠ 0 := by
      have hop : IsOpen {y : V3 | y ≠ 0} := isOpen_compl_singleton
      exact hop.mem_nhds hx
    have hev : (fun y => Real.arccos ((c ⬝ᵥ y) / (‖c‖ * ‖y‖))) =ᶠ[𝓝 x]
        vectorAngle c := by
      filter_upwards [hne] with y hy
      rw [vectorAngle, if_neg (not_or.mpr ⟨hc, hy⟩)]
    refine ContinuousAt.congr ?_ hev
    have harg : ContinuousAt (fun y : V3 => (c ⬝ᵥ y) / (‖c‖ * ‖y‖)) x := by
      apply ContinuousAt.div
      · have hdot : Continuous fun y : V3 => c ⬝ᵥ y := by
          have hi : Continuous fun y : V3 => inner ℝ c y :=
            continuous_const.inner continuous_id
          simpa [inner_eq_dot] using hi
        exact hdot.continuousAt
      · exact (continuous_const.mul continuous_norm).continuousAt
      · exact mul_ne_zero (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hx)
    exact Real.continuous_arccos.continuousAt.comp harg

/-- HOL planarity.hl:83 `open_vector_angle_fan`：路径恒不经过 x 时，
角度 ≠ a 的参数集开。 -/
theorem open_vector_angle_fan (x v u w : V3) (a : ℝ)
    (h : ∀ t : ℝ, (1 - t) • u + t • w ≠ x) :
    IsOpen {t : ℝ | vectorAngle (v - x) ((1 - t) • u + t • w - x) ≠ a} := by
  have hcont : Continuous fun t : ℝ =>
      vectorAngle (v - x) ((1 - t) • u + t • w - x) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 - t) • u + t • w - x ≠ 0 := sub_ne_zero.mpr (h t)
    have hpath : ContinuousAt (fun s : ℝ => (1 - s) • u + s • w - x) t :=
      (by continuity : Continuous fun s : ℝ => (1 - s) • u + s • w - x).continuousAt
    have hcomp : ContinuousAt ((vectorAngle (v - x)) ∘
        (fun s : ℝ => (1 - s) • u + s • w - x)) t :=
      ContinuousAt.comp (continuousAt_vectorAngle (v - x) hne) hpath
    exact hcomp
  have hset : {t : ℝ | vectorAngle (v - x) ((1 - t) • u + t • w - x) ≠ a} =
      (fun t : ℝ => vectorAngle (v - x) ((1 - t) • u + t • w - x)) ⁻¹' {a}ᶜ := by
    ext t
    simp [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset]
  exact isOpen_compl_singleton.preimage hcont

/-- HOL planarity.hl:122 `exists_open_not_collinear`（证明重构：不走
HOL 的 vector_angle 开集路线，改用 —— 共线 ⟺ 落在闭仿射包
`affineSpan {x,v}` 中，而路径连续且 t=0 处不在其中，故一小段都避开）。 -/
theorem exists_open_not_collinear (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ t1 → ¬ Collinear3 x v ((1 - t) • u + t • w) := by
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hxv : x ≠ v := by
    intro he
    apply hncu
    rw [he]
    exact collinear3_of_eq rfl
  have hclosed : IsClosed (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
    AffineSubspace.closed_of_finiteDimensional _
  have hcont : Continuous fun t : ℝ => (1 - t) • u + t • w := by continuity
  have hopen : IsOpen ((fun t : ℝ => (1 - t) • u + t • w) ⁻¹'
      (affineSpan ℝ ({x, v} : Set V3) : Set V3)ᶜ) :=
    hclosed.isOpen_compl.preimage hcont
  have hmem0 : (0 : ℝ) ∈ (fun t : ℝ => (1 - t) • u + t • w) ⁻¹'
      (affineSpan ℝ ({x, v} : Set V3) : Set V3)ᶜ := by
    rw [Set.mem_preimage, Set.mem_compl_iff]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact fun hu => hncu ((collinear3_iff_mem_affineSpan hxv).mpr hu)
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen 0 hmem0
  refine ⟨min (ε / 2) 1, by positivity, min_le_right _ _, ?_⟩
  intro t ht0 ht1
  have ht : t ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact lt_of_le_of_lt (ht1.trans (min_le_left _ _)) (by linarith)
  have hthis := hε ht
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hthis
  intro hcol
  apply hthis
  rwa [collinear3_iff_mem_affineSpan hxv] at hcol
