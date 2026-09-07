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
import Kepler.Geom.Coplanar

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
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

/-! ## 第二块：convex hull 分离与 aff_gt 显式刻画（planarity.hl:260–480）

约定：HOL `DISJOINT {x} {v,w}` ↔ `x ∉ {v,w}`；HOL `convex hull` ↔
`convexHull ℝ`；HOL `coplanar` ↔ `Coplanar`（含于某三点仿射包）。 -/

/-- HOL planarity.hl:260 `AFF_GT_1_2`：`aff_gt {x} {v,w}` 的显式组合刻画。
有限和按去重集合求和，故 `v = w`（此时并集只有两点）需单独处理。 -/
theorem aff_gt_1_2 (hdis : Disjoint ({x} : Set V3) {v, w}) :
    affGt {x} {v, w} =
      {y | ∃ t1 t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • w} := by
  have hdis' := Set.disjoint_left.mp hdis
  have hxv : x ≠ v := by
    intro he
    exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  have hxw : x ≠ w := by
    intro he
    exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  ext y
  simp only [affGt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    by_cases hvw : v = w
    · -- 退化情形 v = w：求和集合为 {x, v}，把正系数 f v 对半拆成 t2 = t3。
      have hfv : 0 < f v := hpos v (by simp)
      have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, hvw, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hTeq] at hsum hone
      rw [Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hone
      rw [Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hsum
      have hsplit : ∀ c : ℝ, ∀ p : V3, (c / 2) • p + (c / 2) • p = c • p := by
        intro c p
        rw [← add_smul]
        congr 1
        ring
      refine ⟨f x, f v / 2, f v / 2, by linarith, by linarith, by linarith, ?_⟩
      rw [hsum, ← hvw, add_assoc, hsplit]
    · have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      rw [hTeq] at hsum hone
      rw [Finset.sum_insert (by simp [hxv, hxw]), Finset.sum_insert (by simp [hvw]),
        Finset.sum_singleton] at hone
      rw [Finset.sum_insert (by simp [hxv, hxw]), Finset.sum_insert (by simp [hvw]),
        Finset.sum_singleton] at hsum
      exact ⟨f x, f v, f w, hpos v (by simp), hpos w (by simp), by linarith,
        by rw [hsum]; abel⟩
  · rintro ⟨t1, t2, t3, ht2, ht3, hone, hy⟩
    have hfin : ({x} ∪ {v, w} : Set V3).Finite :=
      (Set.finite_singleton x).union ((Set.finite_singleton w).insert v)
    by_cases hvw : v = w
    · -- 退化情形 v = w：t2 + t3 合并到 v 的系数上。
      refine ⟨fun z => if z = v then t2 + t3 else t1, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
        show y = (if x = v then t2 + t3 else t1) • x +
          (if v = v then t2 + t3 else t1) • v
        rw [if_neg hxv, if_pos (rfl : v = v), hy, ← hvw, add_assoc, ← add_smul]
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzv | hzw
        · rw [hzv]
          show 0 < (if v = v then t2 + t3 else t1)
          rw [if_pos (rfl : v = v)]
          linarith
        · rw [hzw]
          show 0 < (if w = v then t2 + t3 else t1)
          rw [if_pos hvw.symm]
          linarith
      · have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
        show (if x = v then t2 + t3 else t1) + (if v = v then t2 + t3 else t1) = 1
        rw [if_neg hxv, if_pos (rfl : v = v)]
        linarith
    · refine ⟨fun z => if z = v then t2 else if z = w then t3 else t1, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
          Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
        show y = (if x = v then t2 else if x = w then t3 else t1) • x +
          ((if v = v then t2 else if v = w then t3 else t1) • v +
            (if w = v then t2 else if w = w then t3 else t1) • w)
        rw [if_neg hxv, if_neg hxw, if_pos (rfl : v = v),
          if_neg (Ne.symm hvw), if_pos (rfl : w = w), hy]
        abel
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzv | hzw
        · rw [hzv]
          show 0 < (if v = v then t2 else if v = w then t3 else t1)
          rw [if_pos (rfl : v = v)]
          exact ht2
        · rw [hzw]
          show 0 < (if w = v then t2 else if w = w then t3 else t1)
          rw [if_neg (Ne.symm hvw), if_pos (rfl : w = w)]
          exact ht3
      · have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
          Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
        show (if x = v then t2 else if x = w then t3 else t1) +
          ((if v = v then t2 else if v = w then t3 else t1) +
            (if w = v then t2 else if w = w then t3 else t1)) = 1
        rw [if_neg hxv, if_neg hxw, if_pos (rfl : v = v),
          if_neg (Ne.symm hvw), if_pos (rfl : w = w)]
        linarith

/-- HOL planarity.hl:273 `linear_aff_fan`：`ℝ² → V³` 的线性映射
`t ↦ t₁•(v-x) + t₂•(u-x)`（打包为 `LinearMap`）。 -/
def linearAffFan (x v u : V3) : (ℝ × ℝ) →ₗ[ℝ] V3 where
  toFun p := p.1 • (v - x) + p.2 • (u - x)
  map_add' p q := by
    show (p.1 + q.1) • (v - x) + (p.2 + q.2) • (u - x) =
      (p.1 • (v - x) + p.2 • (u - x)) + (q.1 • (v - x) + q.2 • (u - x))
    rw [add_smul, add_smul]
    abel
  map_smul' c p := by
    show (c * p.1) • (v - x) + (c * p.2) • (u - x) =
      (c : ℝ) • (p.1 • (v - x) + p.2 • (u - x))
    rw [smul_add, smul_smul, smul_smul]

/-- HOL planarity.hl:273 `linear_aff_fan`（`IsLinearMap` 形式）。 -/
theorem linear_aff_fan (x v u : V3) :
    IsLinearMap ℝ (fun p : ℝ × ℝ => p.1 • (v - x) + p.2 • (u - x)) :=
  ⟨fun a b => by
    show (a.1 + b.1) • (v - x) + (a.2 + b.2) • (u - x) =
      (a.1 • (v - x) + a.2 • (u - x)) + (b.1 • (v - x) + b.2 • (u - x))
    rw [add_smul, add_smul]
    abel,
   fun c p => by
    show (c * p.1) • (v - x) + (c * p.2) • (u - x) =
      (c : ℝ) • (p.1 • (v - x) + p.2 • (u - x))
    rw [smul_add, smul_smul, smul_smul]⟩

/-- HOL planarity.hl:285 `origin_point_not_in_convex_fan`。核心只是纯几何：
`x ∈ convexHull {v,u,w}` 给出 `x ∈ affineSpan {v,u,w}`，从而四点组共面。
（HOL 中的 FAN 假设在此引理内并未实质使用，按原样保留。） -/
theorem origin_point_not_in_convex_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    x ∉ convexHull ℝ ({v, u, w} : Set V3) := by
  intro hx
  apply hcop
  refine ⟨v, u, w, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hv : v ∈ (affineSpan ℝ ({v, u, w} : Set V3) : Set V3) :=
    SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  have hu : u ∈ (affineSpan ℝ ({v, u, w} : Set V3) : Set V3) :=
    SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  have hw : w ∈ (affineSpan ℝ ({v, u, w} : Set V3) : Set V3) :=
    SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  rcases hp with hp1 | hp
  · rw [hp1]
    exact convexHull_subset_affineSpan ({v, u, w} : Set V3) hx
  rcases hp with hp2 | hp
  · rw [hp2]
    exact hv
  rcases hp with hp3 | hp4
  · rw [hp3]
    exact hu
  · rw [hp4]
    exact hw

/-- HOL planarity.hl:337 `separate_point_convex_fan`：不共面条件下，原点与
三角形凸包正分离（有限集凸包闭 ⟹ 距离水平集开）。 -/
theorem separate_point_convex_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∃ h : ℝ, 0 < h ∧ ∀ y ∈ convexHull ℝ ({v, u, w} : Set V3), h < ‖y - x‖ := by
  have hnc := origin_point_not_in_convex_fan hfan hvu huw hcop
  have hfin : ({v, u, w} : Set V3).Finite := by simp
  have hclosed : IsClosed (convexHull ℝ ({v, u, w} : Set V3)) :=
    Set.Finite.isClosed_convexHull (𝕜 := ℝ) hfin
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp (isOpen_compl_iff.mpr hclosed) x hnc
  refine ⟨ε / 2, by positivity, ?_⟩
  intro y hy
  have hnb : y ∉ Metric.ball x ε := fun hb => (hε hb) hy
  rw [Metric.mem_ball] at hnb
  exact lt_of_lt_of_le (by linarith) ((le_of_not_gt hnb).trans_eq (dist_eq_norm y x))

/-- HOL planarity.hl:393 `expansion_convex_fan`：`s`、`t ∈ [0,1]` 的两步凸组合
仍落在三点凸包内（凸包的凸性 + 线段的双系数刻画）。 -/
theorem expansion_convex_fan (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    (1 - s) • v + s • ((1 - t) • u + t • w) ∈ convexHull ℝ ({v, u, w} : Set V3) := by
  have hconv := convex_iff_segment_subset.mp (convex_convexHull ℝ ({v, u, w} : Set V3))
  have hv : v ∈ convexHull ℝ ({v, u, w} : Set V3) := subset_convexHull ℝ _ (by simp)
  have hu : u ∈ convexHull ℝ ({v, u, w} : Set V3) := subset_convexHull ℝ _ (by simp)
  have hw : w ∈ convexHull ℝ ({v, u, w} : Set V3) := subset_convexHull ℝ _ (by simp)
  have hq : (1 - t) • u + t • w ∈ convexHull ℝ ({v, u, w} : Set V3) :=
    hconv hu hw ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  exact hconv hv hq ⟨1 - s, s, by linarith, hs0, by ring, rfl⟩

/-- HOL planarity.hl:416 `expansion1_convex_fan`。 -/
theorem expansion1_convex_fan (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • v + s • u ∈ convexHull ℝ ({v, u} : Set V3) := by
  rw [convexHull_pair]
  exact ⟨1 - s, s, by linarith, hs0, by ring, rfl⟩

/-- HOL planarity.hl:428 `norm_origin_fan`：`y ↦ ‖y - x‖` 连续。 -/
theorem norm_origin_fan (x : V3) : Continuous fun y : V3 => ‖y - x‖ :=
  (continuous_id.sub continuous_const).norm

/-- HOL planarity.hl:441 `origin_point_not1_in_convex_fan`：原点不在
两邻居的凸包内，即 x、v、u 不共线（fan6 的重述）。 -/
theorem origin_point_not1_in_convex_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    x ∉ convexHull ℝ ({v, u} : Set V3) := by
  intro hx
  have hncu := fan_not_collinear hfan hvu
  have hvx : v ≠ x := by
    intro he
    apply hncu
    rw [he]
    exact collinear3_of_eq rfl
  rw [convexHull_pair] at hx
  simp only [segment, Set.mem_setOf_eq] at hx
  obtain ⟨a, b, ha0, hb0, hab, hcoef⟩ := hx
  by_cases hb : b = 0
  · rw [hb, zero_smul, add_zero] at hcoef
    have ha1 : a = 1 := by linarith
    rw [ha1, one_smul] at hcoef
    exact hncu (by rw [hcoef]; exact collinear3_of_eq rfl)
  · apply hncu
    refine (collinear3_iff_smul hvx).mpr ⟨-(a / b), ?_⟩
    have h1 : u - x = a • (u - v) := by
      rw [sub_eq_iff_eq_add, smul_sub, ← hcoef]
      have hex : a • u - a • v + (a • v + b • u) = a • u + b • u := by abel
      rw [hex, ← add_smul, hab, one_smul]
    have h2 : v - x = -b • (u - v) := by
      rw [sub_eq_iff_eq_add, neg_smul, smul_sub, ← hcoef]
      have hex : -(b • u - b • v) + (a • v + b • u) = a • v + b • v := by abel
      rw [hex, ← add_smul, hab, one_smul]
    rw [h1, h2, smul_smul]
    have hkey : -(a / b) * -b = a := by
      rw [neg_mul, mul_neg, neg_neg]
      exact div_mul_cancel₀ a hb
    rw [hkey]

/-! ## 第三块：距离估计（planarity.hl:573、644） -/

/-- HOL planarity.hl:644 `real_abs_sub_norm`（Mathlib
`abs_norm_sub_norm_le` 的一行转述）。 -/
theorem real_abs_sub_norm (x y : V3) : |‖x‖ - ‖y‖| ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

/-- HOL planarity.hl:573 `bounded_convex_fan`：两点凸包紧致，连续映射
`y ↦ ‖y - x‖` 在其上有界，取界加 1 即得严格上界。 -/
theorem bounded_convex_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    ∃ h : ℝ, 0 < h ∧ ∀ y ∈ convexHull ℝ ({v, u} : Set V3), ‖y - x‖ < h := by
  have hfin : ({v, u} : Set V3).Finite := by simp
  obtain ⟨C, hC⟩ := (Set.Finite.isCompact_convexHull (𝕜 := ℝ) hfin).exists_bound_of_continuousOn
    (norm_origin_fan x).continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC v (subset_convexHull ℝ _ (by simp))
    rw [norm_norm] at h
    exact le_trans (norm_nonneg _) h
  refine ⟨C + 1, by linarith, ?_⟩
  intro y hy
  have h2 := hC y hy
  rw [norm_norm] at h2
  exact lt_of_le_of_lt h2 (by linarith)

/-! ## 第四块：小边附近的范数估计（planarity.hl:487、651、872）

记 `a := (1-s)•v + s•u - x`（指向边 `vu` 上动点的向量）与
`b := (1-s)•v + s •((1-t)•u + t•w) - x`（`u→w` 扰动后的对应向量）。
两插值点都落在 `convexHull {v,u,w}` 内（`expansion_convex_fan`），由
`separate_point_convex_fan` 与 x 的距离以 `h0 > 0` 为下界，故
`‖a‖, ‖b‖ ≥ h0`：倒数有界，`‖a - b‖ = s*t*‖u-w‖` 随 t → 0。 -/

/-- 实数辅助：正实数倒数之差的绝对值乘回分子
（HOL 中 `inv_sub_inv` + 分式化简的封装）。 -/
theorem abs_inv_sub_mul_self_eq {r1 r2 : ℝ} (h1 : 0 < r1) (h2 : 0 < r2) :
    |r1⁻¹ - r2⁻¹| * r1 = |r2 - r1| / r2 := by
  rw [inv_sub_inv h1.ne' h2.ne', abs_div, abs_mul, abs_of_pos h1, abs_of_pos h2]
  field_simp

/-- 恒等式 `u - ((1-t)•u + t•w) = t•(u-w)`（HOL 证明中反复出现的
`VECTOR_ARITH` 步骤）。 -/
theorem sub_interp_fan (t : ℝ) (u w : V3) :
    u - ((1 - t) • u + t • w) = t • (u - w) := by
  have e : (1 - t) • u = u - t • u := by rw [sub_smul, one_smul]
  rw [e, sub_add_eq_sub_sub, sub_sub_cancel, smul_sub]

/-- 恒等式：两个插值点（相对 x）之差。 -/
theorem sub_interps_fan (s t : ℝ) (x v u w : V3) :
    ((1 - s) • v + s • u - x) - ((1 - s) • v + s • ((1 - t) • u + t • w) - x) =
      s • (u - ((1 - t) • u + t • w)) := by
  have e : ((1 - s) • v + s • u - x) -
      ((1 - s) • v + s • ((1 - t) • u + t • w) - x) =
      s • u - s • ((1 - t) • u + t • w) := by abel
  rw [e, smul_sub]

/-- HOL planarity.hl:487 `inequality1_fan`：取 `h := min 1 (d*h0/‖u-w‖)`；
`‖u - ((1-t)•u+t•w)‖ = t*‖u-w‖`，`‖b‖⁻¹ ≤ h0⁻¹`（b 点在凸包内）。 -/
theorem inequality1_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (d : ℝ) (hd : 0 < d) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ t : ℝ, 0 ≤ t → t < h → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        s * ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ *
            ‖u - ((1 - t) • u + t • w)‖ < d := by
  obtain ⟨h0, h0pos, h0b⟩ := separate_point_convex_fan hfan hvu huw hcop
  have huwne : u ≠ w := edge_ne_of_fan hfan huw
  have hnw : 0 < ‖u - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huwne)
  refine ⟨min 1 (d * h0 / ‖u - w‖),
    lt_min zero_lt_one (div_pos (mul_pos hd h0pos) hnw), min_le_left _ _, ?_⟩
  intro t ht0 hlt s hs0 hs1
  have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
  have hbn : h0 < ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ :=
    h0b _ (expansion_convex_fan t s ht0 ht1 hs0 hs1)
  have hsplit : t * ‖u - w‖ < d * h0 :=
    (lt_div_iff₀ hnw).mp (lt_of_lt_of_le hlt (min_le_right _ _))
  have hinv : ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ ≤ h0⁻¹ :=
    inv_anti₀ h0pos (le_of_lt hbn)
  have hle : s * ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ *
      (t * ‖u - w‖) ≤ h0⁻¹ * (t * ‖u - w‖) := by
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg ht0 (norm_nonneg _))
    have h1 : s * ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ ≤ 1 * h0⁻¹ :=
      mul_le_mul hs1 hinv (inv_nonneg.mpr (norm_nonneg _)) zero_le_one
    simpa using h1
  have hfin : h0⁻¹ * (t * ‖u - w‖) < d := by
    have hdiv : (t * ‖u - w‖) / h0 < d := (div_lt_iff₀ h0pos).mpr hsplit
    rwa [div_eq_inv_mul] at hdiv
  rw [sub_interp_fan, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  exact lt_of_le_of_lt hle hfin

/-- HOL planarity.hl:651 `inequaility2_fan`（沿用 HOL 原拼写）。注意按 HOL
原文，两个被数乘的向量都是 `a = (1-s)•v + s•u - x`（第二个的标度才是
`‖b‖⁻¹`）。核心约化：`‖ ‖a‖⁻¹•a - ‖b‖⁻¹•a ‖ = |‖b‖ - ‖a‖|/‖b‖ ≤
‖a - b‖/h0 = s*t*‖u-w‖/h0 < d`。 -/
theorem inequaility2_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (d : ℝ) (hd : 0 < d) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ t : ℝ, 0 ≤ t → t < h → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ‖(‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
            (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
              ((1 - s) • v + s • u - x)‖ < d := by
  obtain ⟨h0, h0pos, h0b⟩ := separate_point_convex_fan hfan hvu huw hcop
  have huwne : u ≠ w := edge_ne_of_fan hfan huw
  have hnw : 0 < ‖u - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huwne)
  refine ⟨min 1 (d * h0 / ‖u - w‖),
    lt_min zero_lt_one (div_pos (mul_pos hd h0pos) hnw), min_le_left _ _, ?_⟩
  intro t ht0 hlt s hs0 hs1
  have ht1 : t ≤ 1 := le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
  have hpu : (1 - s) • v + s • u ∈ convexHull ℝ ({v, u, w} : Set V3) := by
    have hmem : (1 - s) • v + s • ((1 - (0 : ℝ)) • u + (0 : ℝ) • w) ∈
        convexHull ℝ ({v, u, w} : Set V3) :=
      expansion_convex_fan 0 s (by norm_num) (by norm_num) hs0 hs1
    simpa using hmem
  have han : h0 < ‖(1 - s) • v + s • u - x‖ := h0b _ hpu
  have hbn : h0 < ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ :=
    h0b _ (expansion_convex_fan t s ht0 ht1 hs0 hs1)
  have hapos : 0 < ‖(1 - s) • v + s • u - x‖ := lt_trans h0pos han
  have hbpos : 0 < ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ :=
    lt_trans h0pos hbn
  have hkey : ‖(‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
        (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
          ((1 - s) • v + s • u - x)‖ =
      |‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ -
          ‖(1 - s) • v + s • u - x‖| /
        ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs,
      abs_inv_sub_mul_self_eq hapos hbpos]
  have h1 : |‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖ -
      ‖(1 - s) • v + s • u - x‖| ≤
      ‖((1 - s) • v + s • u - x) -
        ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ := by
    have h11 := real_abs_sub_norm
      ((1 - s) • v + s • ((1 - t) • u + t • w) - x) ((1 - s) • v + s • u - x)
    rwa [norm_sub_rev ((1 - s) • v + s • ((1 - t) • u + t • w) - x)
      ((1 - s) • v + s • u - x)] at h11
  have h2 : ‖((1 - s) • v + s • u - x) -
      ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ = s * t * ‖u - w‖ := by
    rw [sub_interps_fan s t x v u w, sub_interp_fan t u w, smul_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 ht0)]
  have hsplit : t * ‖u - w‖ < d * h0 :=
    (lt_div_iff₀ hnw).mp (lt_of_lt_of_le hlt (min_le_right _ _))
  have hinvb : ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ ≤ h0⁻¹ :=
    inv_anti₀ h0pos (le_of_lt hbn)
  rw [hkey, div_eq_mul_inv]
  refine lt_of_le_of_lt (mul_le_mul h1 hinvb (inv_nonneg.mpr (norm_nonneg _))
    (norm_nonneg _)) ?_
  rw [h2]
  have h3 : s * t ≤ 1 * t := mul_le_mul hs1 le_rfl ht0 zero_le_one
  have hfin : (t * ‖u - w‖) * h0⁻¹ < d := by
    have hdiv : (t * ‖u - w‖) / h0 < d := (div_lt_iff₀ h0pos).mpr hsplit
    rw [div_eq_inv_mul] at hdiv
    rw [mul_comm]
    exact hdiv
  calc s * t * ‖u - w‖ * h0⁻¹ ≤ (t * ‖u - w‖) * h0⁻¹ :=
        mul_le_mul_of_nonneg_right (by
          calc s * t * ‖u - w‖ ≤ (1 * t) * ‖u - w‖ :=
                mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
            _ = t * ‖u - w‖ := by ring) (inv_nonneg.mpr h0pos.le)
    _ < d := hfin

/-- HOL planarity.hl:872 `exists_point_small_edges_fan`：单位化 a 与单位化 b
之差小于 d。把差拆成 `‖a/‖a‖ - a/‖b‖‖ + ‖a/‖b‖ - b/‖b‖‖`，前者由
`inequaility2_fan`（d/2）控制，后者 `= ‖‖b‖⁻¹•(a-b)‖ = s*‖b‖⁻¹*‖u-...‖`
由 `inequality1_fan`（d/2）控制，三角不等式相加。 -/
theorem exists_point_small_edges_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (d : ℝ)
    (hd : 0 < d) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ t : ℝ, 0 ≤ t → t < h → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ‖(‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
            (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
              ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ < d := by
  have hd2 : 0 < d / 2 := by linarith
  obtain ⟨h2, h2pos, h2le, h2b⟩ := inequaility2_fan hfan hvu huw hcop (d / 2) hd2
  obtain ⟨h1, h1pos, _, h1b⟩ := inequality1_fan hfan hvu huw hcop (d / 2) hd2
  refine ⟨min h1 h2, lt_min h1pos h2pos,
    (min_le_right _ _).trans h2le, ?_⟩
  intro t ht0 hlt s hs0 hs1
  have B1 := h2b t ht0 (lt_of_lt_of_le hlt (min_le_right _ _)) s hs0 hs1
  have B2 := h1b t ht0 (lt_of_lt_of_le hlt (min_le_left _ _)) s hs0 hs1
  have B3 : ‖(‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
        ((1 - s) • v + s • u - x) -
      (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
        ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ =
      s * ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ *
        ‖u - ((1 - t) • u + t • w)‖ := by
    rw [← smul_sub, sub_interps_fan s t x v u w, smul_smul, norm_smul,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hs0)]
    ring
  have hsplit : ‖(‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
        (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
          ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ =
      ‖((‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
          (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
            ((1 - s) • v + s • u - x)) +
        ((‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
            ((1 - s) • v + s • u - x) -
          (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
            ((1 - s) • v + s • ((1 - t) • u + t • w) - x))‖ := by
    rw [sub_add_sub_cancel]
  rw [hsplit]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

/-! ## 第五块：aff_ge 显式刻画与锥的数乘封闭 -/

/-- HOL `AFF_GE_1_2`：`aff_ge {x} {v,u}` 的显式组合刻画（`aff_gt_1_2`
的非严格对偶：`0 <` 全部换成 `0 ≤`，证明逐行对应）。 -/
theorem aff_ge_1_2 (hdis : Disjoint ({x} : Set V3) {v, u}) :
    affGe {x} {v, u} =
      {y | ∃ t1 t2 t3 : ℝ, 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • u} := by
  have hdis' := Set.disjoint_left.mp hdis
  have hxv : x ≠ v := by
    intro he
    exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  have hxu : x ≠ u := by
    intro he
    exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  ext y
  simp only [affGe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    by_cases hvu : v = u
    · -- 退化情形 v = u：求和集合为 {x, v}，把系数 f v 对半拆成 t2 = t3。
      have hfv : 0 ≤ f v := hpos v (by simp)
      have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, hvu, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hTeq] at hsum hone
      rw [Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hone
      rw [Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hsum
      have hsplit : ∀ c : ℝ, ∀ p : V3, (c / 2) • p + (c / 2) • p = c • p := by
        intro c p
        rw [← add_smul]
        congr 1
        ring
      refine ⟨f x, f v / 2, f v / 2, by linarith, by linarith, by linarith, ?_⟩
      rw [hsum, ← hvu, add_assoc, hsplit]
    · have hTeq : hfin.toFinset = ({x, v, u} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      rw [hTeq] at hsum hone
      rw [Finset.sum_insert (by simp [hxv, hxu]), Finset.sum_insert (by simp [hvu]),
        Finset.sum_singleton] at hone
      rw [Finset.sum_insert (by simp [hxv, hxu]), Finset.sum_insert (by simp [hvu]),
        Finset.sum_singleton] at hsum
      exact ⟨f x, f v, f u, hpos v (by simp), hpos u (by simp), by linarith,
        by rw [hsum]; abel⟩
  · rintro ⟨t1, t2, t3, ht2, ht3, hone, hy⟩
    have hfin : ({x} ∪ {v, u} : Set V3).Finite :=
      (Set.finite_singleton x).union ((Set.finite_singleton u).insert v)
    by_cases hvu : v = u
    · -- 退化情形 v = u：t2 + t3 合并到 v 的系数上。
      refine ⟨fun z => if z = v then t2 + t3 else t1, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvu, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
        show y = (if x = v then t2 + t3 else t1) • x +
          (if v = v then t2 + t3 else t1) • v
        rw [if_neg hxv, if_pos (rfl : v = v), hy, ← hvu, add_assoc, ← add_smul]
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzv | hzu
        · rw [hzv]
          show 0 ≤ (if v = v then t2 + t3 else t1)
          rw [if_pos (rfl : v = v)]
          linarith
        · rw [hzu]
          show 0 ≤ (if u = v then t2 + t3 else t1)
          rw [if_pos hvu.symm]
          linarith
      · have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvu, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
        show (if x = v then t2 + t3 else t1) + (if v = v then t2 + t3 else t1) = 1
        rw [if_neg hxv, if_pos (rfl : v = v)]
        linarith
    · refine ⟨fun z => if z = v then t2 else if z = u then t3 else t1, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, v, u} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxu]),
          Finset.sum_insert (by simp [hvu]), Finset.sum_singleton]
        show y = (if x = v then t2 else if x = u then t3 else t1) • x +
          ((if v = v then t2 else if v = u then t3 else t1) • v +
            (if u = v then t2 else if u = u then t3 else t1) • u)
        rw [if_neg hxv, if_neg hxu, if_pos (rfl : v = v),
          if_neg (Ne.symm hvu), if_pos (rfl : u = u), hy]
        abel
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzv | hzu
        · rw [hzv]
          show 0 ≤ (if v = v then t2 else if v = u then t3 else t1)
          rw [if_pos (rfl : v = v)]
          exact ht2
        · rw [hzu]
          show 0 ≤ (if u = v then t2 else if u = u then t3 else t1)
          rw [if_neg (Ne.symm hvu), if_pos (rfl : u = u)]
          exact ht3
      · have hTeq : hfin.toFinset = ({x, v, u} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxu]),
          Finset.sum_insert (by simp [hvu]), Finset.sum_singleton]
        show (if x = v then t2 else if x = u then t3 else t1) +
          ((if v = v then t2 else if v = u then t3 else t1) +
            (if u = v then t2 else if u = u then t3 else t1)) = 1
        rw [if_neg hxv, if_neg hxu, if_pos (rfl : v = v),
          if_neg (Ne.symm hvu), if_pos (rfl : u = u)]
        linarith

/-- `aff_ge {x} {v,u}` 对从 x 出发的非负数乘封闭：`a•(y-x)+x` 仍为
非负组合，新系数 `⟨1-a*t2-a*t3, a*t2, a*t3⟩`。 -/
theorem scale_aff_ge_fan (hdis : Disjoint ({x} : Set V3) {v, u}) (y : V3) (a : ℝ)
    (hy : y ∈ affGe {x} {v, u}) (ha : 0 ≤ a) :
    a • (y - x) + x ∈ affGe {x} {v, u} := by
  rw [aff_ge_1_2 hdis] at hy ⊢
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hyeq⟩ := hy
  refine ⟨1 - a * t2 - a * t3, a * t2, a * t3, mul_nonneg ha ht2, mul_nonneg ha ht3,
    by ring, ?_⟩
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  rw [hyeq, ht1]
  module

/-- `aff_gt {x} {v,u}` 对从 x 出发的正数乘封闭（严格性由 `mul_pos` 保持）。 -/
theorem scale_aff_gt_fan (hdis : Disjoint ({x} : Set V3) {v, u}) (y : V3) (a : ℝ)
    (hy : y ∈ affGt {x} {v, u}) (ha : 0 < a) :
    a • (y - x) + x ∈ affGt {x} {v, u} := by
  rw [aff_gt_1_2 hdis] at hy ⊢
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hyeq⟩ := hy
  refine ⟨1 - a * t2 - a * t3, a * t2, a * t3, mul_pos ha ht2, mul_pos ha ht3,
    by ring, ?_⟩
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  rw [hyeq, ht1]
  module

/-! ## 第六块：闭扇区的分离（planarity.hl:223、1228、965、1045）

HOL `exist_close_fan`（223）：两条不相交边的闭扇区与单位球面之交是
不相交紧集，`dist` 在紧集乘积上取到正的最小值。
HOL `origin_is_not_aff_gt_fan`（1228）：`aff_gt` 的严格正系数把 x 拉出
意味着 u 落在直线 `aff {x,v}` 上。
HOL `same_projective_sphere_gt_fan`（965）：球面上的 `aff_gt` 点可写成
凸组合 `(1-s)•v + s•p` 的径向单位化。
HOL `separate1_sphere_fan`（1045）：小 t 时扰动扇区与另一边的闭扇区
在球面上无交（前三者的组合，HOL 证明结构照搬）。 -/

/-- HOL `th3` 的角色：`¬ Collinear3 x v w → x ∉ {v, w}`。 -/
private theorem disjoint_of_not_collinear3 {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    Disjoint ({x} : Set V3) {v, w} := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.singleton_inter_eq_empty]
  intro hmem
  rcases Set.mem_insert_iff.mp hmem with he | he
  · exact hnc (by rw [he]; exact collinear3_of_eq rfl)
  · exact hnc (by rw [Set.mem_singleton_iff.mp he]; exact collinear3_pair_left rfl)

/-- `aff_ge {x} ∅ = {x}`（TopologyFan 中同名私有引理的本地复制）。 -/
private theorem affGe_empty_eq_singleton (x : V3) : affGe {x} ∅ = {x} := by
  ext y
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have h2 : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, Finset.mem_singleton]
    rw [h2, Finset.sum_singleton] at hsum hone
    have h : y = x := by rw [hsum, hone, one_smul]
    rw [h]
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

/-- `affGe {x} {v,w} ∩ ballnormFan x` 非空：取 v 方向的单位化点
（`exist_fan`（TopologyFan）中同一构造的一般边版本）。 -/
private theorem affGe_ballnorm_nonempty {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    (affGe {x} {v, w} ∩ ballnormFan x).Nonempty := by
  have hvx : v ≠ x := by
    intro he
    apply hnc
    rw [← he]
    exact collinear3_of_eq rfl
  have hn : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  refine ⟨x + ‖v - x‖⁻¹ • (v - x), ?_, ?_⟩
  · rw [aff_ge_1_2 (disjoint_of_not_collinear3 hnc)]
    simp only [Set.mem_setOf_eq]
    refine ⟨1 - ‖v - x‖⁻¹, ‖v - x‖⁻¹, 0, inv_nonneg.mpr (norm_nonneg _), by norm_num,
      by ring, ?_⟩
    module
  · rw [ballnormFan]
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm,
      show x - (x + ‖v - x‖⁻¹ • (v - x)) = -(‖v - x‖⁻¹ • (v - x)) from by module,
      norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]

/-- HOL planarity.hl:223 `exist_close_fan`：FAN 下两条不相交边的闭扇区
（与单位球面之交）正分离。B 紧、A 闭无交（fan7 + `affGe {x} ∅ = {x}` +
`dist x x = 0 ≠ 1`），`infDist` 在 B 上取正的最小值（`SEPARATE_CLOSED_COMPACT`
的角色，同 TopologyFan `exist_fan` 的收尾）。 -/
theorem exist_close_fan (hfan : FAN x V E) (hdis : Disjoint ({v, w} : Set V3) {v1, w1})
    (he1 : {v1, w1} ∈ E) (he : {v, w} ∈ E) :
    ∃ h : ℝ, 0 < h ∧
      ∀ y1 : V3, y1 ∈ affGe {x} {v, w} ∩ ballnormFan x →
        ∀ y2 : V3, y2 ∈ affGe {x} {v1, w1} ∩ ballnormFan x → h ≤ dist y1 y2 := by
  have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan he
  have hnc1 : ¬ Collinear3 x v1 w1 := fan_not_collinear hfan he1
  have hAclosed : IsClosed (affGe {x} {v, w} ∩ ballnormFan x) :=
    closed_aff_ge_ballnorm_fan hnc
  have hBc : IsCompact (affGe {x} {v1, w1} ∩ ballnormFan x) :=
    compact_aff_ge_ballnorm_fan hnc1
  have hAne := affGe_ballnorm_nonempty hnc
  have h77 : affGe {x} {v, w} ∩ affGe {x} {v1, w1} = affGe {x} ({v, w} ∩ {v1, w1}) :=
    hfan.2.2.2.2.2 {v, w} (Or.inl he) {v1, w1} (Or.inl he1)
  have hinter : {v, w} ∩ {v1, w1} = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdis
  have hint : (affGe {x} {v, w} ∩ ballnormFan x) ∩
      (affGe {x} {v1, w1} ∩ ballnormFan x) = ∅ := by
    have h1 : (affGe {x} {v, w} ∩ ballnormFan x) ∩
        (affGe {x} {v1, w1} ∩ ballnormFan x) =
        (affGe {x} {v, w} ∩ affGe {x} {v1, w1}) ∩ ballnormFan x := by
      ext y
      simp only [Set.mem_inter_iff]
      tauto
    rw [h1, h77, hinter, affGe_empty_eq_singleton]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, ballnormFan, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hyx
    rw [hyx, dist_self]
    norm_num
  obtain ⟨h, hh0, hh⟩ := IsCompact.exists_forall_le' hBc
    (Metric.continuous_infDist_pt _).continuousOn
    (fun y2 hy2 => by
      have hy2not : y2 ∉ closure (affGe {x} {v, w} ∩ ballnormFan x) := by
        rw [hAclosed.closure_eq]
        intro hmem
        exact (Set.mem_empty_iff_false y2).mp (hint ▸ ⟨hmem, hy2⟩)
      exact (Metric.infDist_pos_iff_notMem_closure hAne).mp hy2not)
  exact ⟨h, hh0, fun y1 hy1 y2 hy2 =>
    (hh y2 hy2).trans (by rw [dist_comm]; exact Metric.infDist_le_dist_of_mem hy1)⟩

/-- HOL planarity.hl:1228 `origin_is_not_aff_gt_fan`：u 不在直线
`aff {x,v}` 上时 x ∉ aff_gt {x} {v,u}（`aff_gt_1_2` 的 t3 > 0 系数可解出
u 为 x, v 的仿射组合）。 -/
theorem origin_is_not_aff_gt_fan
    (hu : u ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3))
    (hdis : Disjoint ({x} : Set V3) {v, u}) : x ∉ affGt {x} {v, u} := by
  intro hx
  rw [aff_gt_1_2 hdis] at hx
  simp only [Set.mem_setOf_eq] at hx
  obtain ⟨t1, t2, t3, -, ht3, hone, hyeq⟩ := hx
  refine hu ?_
  have ht3ne : t3 ≠ 0 := ne_of_gt ht3
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  rw [ht1] at hyeq
  have hx' : (1 - t2 - t3) • x + t2 • v + t3 • u - x = 0 := sub_eq_zero.mpr hyeq.symm
  have hexp : (1 - t2 - t3) • x + t2 • v + t3 • u - x =
      t2 • (v - x) + t3 • (u - x) := by
    module
  rw [hexp] at hx'
  have hd : u - x = (-(t2 / t3)) • (v - x) := by
    have h2 : t3⁻¹ • (t2 • (v - x) + t3 • (u - x)) = (0 : V3) := by
      rw [hx', smul_zero]
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht3ne, one_smul] at h2
    rw [show t3⁻¹ * t2 = t2 / t3 from by field_simp] at h2
    have h3 : u - x = -((t2 / t3) • (v - x)) :=
      (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h2))
    rw [h3, neg_smul]
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨-(t2 / t3), ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hd]
  module

/-- HOL planarity.hl:965 `same_projective_sphere_gt_fan`：球面上的
`aff_gt` 点是凸组合 `(1-s)•v + s•p`（p 为 u→w 插值）的径向单位化。
s := t3/(1-t1) 由 `aff_gt_1_2` 的系数齐次化而来。 -/
theorem same_projective_sphere_gt_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (t : ℝ)
    (hnc : ¬ Collinear3 x v ((1 - t) • u + t • w))
    {y1 : V3} (hy1 : y1 ∈ affGt {x} {v, (1 - t) • u + t • w} ∩ ballnormFan x) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      y1 = ‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹ •
        ((1 - s) • v + s • ((1 - t) • u + t • w) - x) + x := by
  have hdis : Disjoint ({x} : Set V3) {v, (1 - t) • u + t • w} :=
    disjoint_of_not_collinear3 hnc
  have hball : dist x y1 = 1 := hy1.2
  have hy1' := hy1.1
  rw [aff_gt_1_2 hdis] at hy1'
  simp only [Set.mem_setOf_eq] at hy1'
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hyeq⟩ := hy1'
  have hc : 0 < 1 - t1 := by linarith
  have hcn : 1 - t1 ≠ 0 := ne_of_gt hc
  refine ⟨t3 / (1 - t1), div_nonneg ht3.le hc.le,
    by rw [div_le_one hc]; linarith, ?_⟩
  have e2 : (1 - t1) * (t3 / (1 - t1)) = t3 := mul_div_cancel₀ t3 hcn
  have e1 : (1 - t1) * (1 - t3 / (1 - t1)) = t2 := by
    rw [mul_sub, mul_one, mul_div_cancel₀ t3 hcn]
    linarith
  have hyx : y1 - x = t2 • (v - x) + t3 • ((1 - t) • u + t • w - x) := by
    rw [hyeq, show t1 = 1 - t2 - t3 from by linarith]
    module
  have hsplit : (1 - t1) • ((1 - t3 / (1 - t1)) • v +
      (t3 / (1 - t1)) • ((1 - t) • u + t • w) - x) =
      t2 • (v - x) + t3 • ((1 - t) • u + t • w - x) := by
    have step : (1 - t1) • ((1 - t3 / (1 - t1)) • v +
        (t3 / (1 - t1)) • ((1 - t) • u + t • w) - x) =
        ((1 - t1) * (1 - t3 / (1 - t1))) • v +
        ((1 - t1) * (t3 / (1 - t1))) • ((1 - t) • u + t • w) - (1 - t1) • x := by
      rw [smul_sub, smul_add, smul_smul, smul_smul]
    rw [step, e1, e2, show (1 - t1) = t2 + t3 from by linarith]
    module
  have hn1 : ‖y1 - x‖ = 1 := by
    rw [dist_eq_norm] at hball
    rwa [norm_sub_rev] at hball
  have h2 : ∀ z : V3, (1 - t1) * ‖z‖ = ‖(1 - t1) • z‖ := by
    intro z
    rw [norm_smul, Real.norm_of_nonneg hc.le]
  have hmul : (1 - t1) * ‖(1 - t3 / (1 - t1)) • v +
      (t3 / (1 - t1)) • ((1 - t) • u + t • w) - x‖ = 1 := by
    rw [h2, hsplit, ← hyx]
    exact hn1
  have hAnorm : ‖(1 - t3 / (1 - t1)) • v +
      (t3 / (1 - t1)) • ((1 - t) • u + t • w) - x‖ = (1 - t1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  have hinv : ‖(1 - t3 / (1 - t1)) • v +
      (t3 / (1 - t1)) • ((1 - t) • u + t • w) - x‖⁻¹ = 1 - t1 := by
    rw [hAnorm, inv_inv]
  rw [hinv, hsplit, ← hyx, sub_add_cancel]

/-- HOL planarity.hl:1045 `separate1_sphere_fan`：存在 h ∈ (0,1] 使得
小 t 时扰动扇区 `aff_gt {x} {v,(1-t)•u+t•w}` 与另一边的闭扇区
`aff_ge {x} {v1,u1}` 在单位球面上无交。HOL 证明：`exist_close_fan`
分离 `{v,u}`/`{v1,u1}` 扇区，`exists_point_small_edges_fan` 保证扰动点
的单位化贴近 `{v,u}` 扇区，`same_projective_sphere_gt_fan` 把交点改写为
该单位化形式，矛盾。 -/
theorem separate1_sphere_fan (hfan : FAN x V E)
    (hdis : Disjoint ({v, u} : Set V3) {v1, u1}) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hv1u1 : {v1, u1} ∈ E) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < h →
      affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v1, u1} ∩ ballnormFan x = ∅ := by
  obtain ⟨hc, hc0, hcsep⟩ := exist_close_fan hfan hdis hv1u1 hvu
  obtain ⟨t1, t1pos, t1le, hnc⟩ := exists_open_not_collinear hfan hvu huw
  obtain ⟨he, hepos, hele, hesm⟩ := exists_point_small_edges_fan hfan hvu huw hcop hc hc0
  refine ⟨min (he / 2) t1, lt_min (by linarith) t1pos,
    (min_le_right _ _).trans t1le, ?_⟩
  intro t ht0 hth
  refine Set.eq_empty_of_forall_notMem (fun z hz => ?_)
  have ht1le' : t ≤ t1 := le_of_lt (lt_of_lt_of_le hth (min_le_right _ _))
  have hthe : t < he := by
    have h1 : t < he / 2 := lt_of_lt_of_le hth (min_le_left _ _)
    linarith
  have hnc' : ¬ Collinear3 x v ((1 - t) • u + t • w) := hnc t ht0.le ht1le'
  obtain ⟨s, hs0, hs1, hzs⟩ := same_projective_sphere_gt_fan hfan hvu huw t hnc'
    ⟨hz.1.1, hz.2⟩
  have hconv : (1 - s) • v + s • u ∈ convexHull ℝ ({v, u} : Set V3) :=
    expansion1_convex_fan s hs0 hs1
  have hxconv : x ∉ convexHull ℝ ({v, u} : Set V3) :=
    origin_point_not1_in_convex_fan hfan hvu
  have hne : (1 - s) • v + s • u - x ≠ 0 := by
    intro h0
    exact hxconv ((sub_eq_zero.mp h0) ▸ hconv)
  have hn : ‖(1 - s) • v + s • u - x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  obtain ⟨y2, hy2def⟩ : ∃ y2 : V3, y2 = ‖(1 - s) • v + s • u - x‖⁻¹ •
      ((1 - s) • v + s • u - x) + x := ⟨_, rfl⟩
  have hy2ball : y2 ∈ ballnormFan x := by
    rw [hy2def, ballnormFan]
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm,
      show x - (‖(1 - s) • v + s • u - x‖⁻¹ • ((1 - s) • v + s • u - x) + x) =
        -(‖(1 - s) • v + s • u - x‖⁻¹ • ((1 - s) • v + s • u - x)) from by module,
      norm_neg, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have hvune : Disjoint ({x} : Set V3) {v, u} :=
    disjoint_of_not_collinear3 (fan_not_collinear hfan hvu)
  have hy2aff : y2 ∈ affGe {x} {v, u} := by
    rw [hy2def, aff_ge_1_2 hvune]
    simp only [Set.mem_setOf_eq]
    refine ⟨1 - ‖(1 - s) • v + s • u - x‖⁻¹,
      ‖(1 - s) • v + s • u - x‖⁻¹ * (1 - s), ‖(1 - s) • v + s • u - x‖⁻¹ * s,
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by linarith : 0 ≤ 1 - s),
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hs0,
      by ring, by module⟩
  have hsm := hesm t ht0.le hthe s hs0 hs1
  have hdzy2 : dist z y2 =
      ‖(‖(1 - s) • v + s • u - x‖⁻¹) • ((1 - s) • v + s • u - x) -
        (‖(1 - s) • v + s • ((1 - t) • u + t • w) - x‖⁻¹) •
          ((1 - s) • v + s • ((1 - t) • u + t • w) - x)‖ := by
    rw [dist_eq_norm, hzs, hy2def, add_sub_add_right_eq_sub, norm_sub_rev]
  have hfinal : hc ≤ dist y2 z := hcsep y2 ⟨hy2aff, hy2ball⟩ z ⟨hz.1.2, hz.2⟩
  rw [dist_comm y2 z, hdzy2] at hfinal
  linarith
