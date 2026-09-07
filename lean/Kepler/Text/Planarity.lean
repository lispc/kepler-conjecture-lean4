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

/-! ## 第七块：fully surrounded 预备（planarity.hl:1336–1463）

约定：HOL `{v,u} IN E` ↔ `{v, u} ∈ E`；`azim_fan`/`sigma_fan` 取
Kepler/Text/Fan.lean 的 `Fan.azimFan`/`Fan.sigmaFan`；`coplanar` ↔
`Coplanar`（含于某三点仿射包）。共面性的总体策略走仿射包闭性：把第四点
写成已有点的仿射组合（lineMap），再对仿射包做单调性传递，避免维数论证。 -/

/-- 组合辅助：子空间载合集的仿射包仍是子空间本身（点式传递）。 -/
private theorem mem_affineSpan_carrier {S : AffineSubspace ℝ V3} {z : V3}
    (hz : z ∈ (affineSpan ℝ (↑S : Set V3) : Set V3)) : z ∈ (S : Set V3) :=
  affineSpan_le.mpr (Set.Subset.rfl) hz

private theorem subset_pair3 {a b c : V3} : ({a, b} : Set V3) ⊆ ({a, b, c} : Set V3) := by
  intro p hp
  rcases Set.mem_insert_iff.mp hp with h1 | hp
  · rw [h1]
    exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff.mp hp]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

private theorem subset_pair4 {a b c d : V3} : ({c, d} : Set V3) ⊆ ({a, b, c, d} : Set V3) := by
  intro p hp
  rcases Set.mem_insert_iff.mp hp with h1 | hp
  · rw [h1]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [Set.mem_singleton_iff.mp hp]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl)))

/-- 组合辅助：仿射组合入三点仿射包
（`y = x + c•(q-x) + h•(p-x)` 时 `y ∈ affineSpan {x,p,q}`）。 -/
private theorem mem_affineSpan_triple_of_eq {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (q - x) + h • (p - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : c • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd4 : h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd5 : c • (q - x) + h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval : y = h • (p - x) +ᵥ (c • (q - x) +ᵥ x) := by
    rw [hy, vadd_eq_add, vadd_eq_add]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd4
    (AffineSubspace.vadd_mem_of_mem_direction hd3 hxS)

/-- 组合辅助：`p` 落在直线 `aff {x,v}` 上时四点 `{x,v,p,q}` 共面
（见证取 `{x,v,q}`，`p` 由仿射包单调性传入）。 -/
private theorem coplanar_of_mem_line {x v p q : V3}
    (hp : p ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3)) :
    Coplanar ({x, v, p, q} : Set V3) := by
  refine ⟨x, v, q, fun z hz => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h1 | hz
  · rw [h1]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  rcases hz with h1 | hz
  · rw [h1]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  rcases hz with h1 | hz
  · rw [h1]
    exact affineSpan_mono ℝ subset_pair3 (SetLike.mem_coe.mp hp)
  · rw [hz]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))

/-- 组合辅助：`q` 落在直线 `aff {x,v}` 上时四点 `{x,v,p,q}` 共面
（`coplanar_of_mem_line` 的末位变体）。 -/
private theorem coplanar_of_mem_line' {x v p q : V3}
    (hq : q ∈ (affineSpan ℝ ({x, v} : Set V3) : Set V3)) :
    Coplanar ({x, v, p, q} : Set V3) := by
  refine ⟨x, v, p, fun z hz => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h1 | hz
  · rw [h1]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  rcases hz with h1 | hz
  · rw [h1]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  rcases hz with h1 | hz
  · rw [h1]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  · rw [hz]
    exact affineSpan_mono ℝ subset_pair3 (SetLike.mem_coe.mp hq)

/-- HOL planarity.hl:1336 `fan81`：每条边张开的扇形角小于 π。 -/
def fan81 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E → Fan.azimFan x V E v u < Real.pi

/-- HOL planarity.hl:1338 `fan80`：每条边对后继的方位角严格在 (0, π) 内。 -/
def fan80 (x : V3) (V : Set V3) (E : Set (Set V3)) : Prop :=
  ∀ v u : V3, {v, u} ∈ E →
    0 < azim x v u (Fan.sigmaFan x V E v u) ∧
      azim x v u (Fan.sigmaFan x V E v u) < Real.pi

/-- HOL planarity.hl:1349 `continuous_coplanar_fan`：不共面四点中把 `w`
换成线段 `u→w` 上的内点 `p_t = (1-t)•u + t•w`（t ≠ 0）仍不共面。
重构证明（不走 HOL 的行列式展开）：`p_t = lineMap u w t` 落在
`aff {u,p_t}` 中，而 `w = p_t + t⁻¹•(u - p_t)` 是 `u, p_t` 的仿射组合
（系数和 1），故 `{x,v,u,w}` 整体落在 `{x,v,u,p_t}` 的仿射包内，再由
Coplanar 的三点见证 `{a,b,c}` 单调传递。 -/
theorem continuous_coplanar_fan (x v u w : V3) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (t : ℝ) (ht : t ≠ 0) :
    ¬ Coplanar ({x, v, u, (1 - t) • u + t • w} : Set V3) := by
  intro hc
  apply hcop
  obtain ⟨a, b, c, hsub⟩ := hc
  have hwS : w ∈ (affineSpan ℝ ({x, v, u, (1 - t) • u + t • w} : Set V3) : Set V3) := by
    have hw2 : w ∈ (affineSpan ℝ ({u, (1 - t) • u + t • w} : Set V3) : Set V3) := by
      refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t⁻¹, ?_⟩
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
        show (1 - t) • u + t • w - u = t • (w - u) from by module, smul_smul,
        show t⁻¹ * t = 1 from by field_simp, one_smul]
      abel
    exact affineSpan_mono ℝ (subset_pair4 (a := x) (b := v))
      (SetLike.mem_coe.mp hw2)
  refine ⟨a, b, c, fun z hz => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h1 | hz
  · rw [h1]
    exact hsub (by simp)
  rcases hz with h1 | hz
  · rw [h1]
    exact hsub (by simp)
  rcases hz with h1 | hz
  · rw [h1]
    exact hsub (by simp)
  · rw [hz]
    exact mem_affineSpan_carrier (affineSpan_mono ℝ hsub (SetLike.mem_coe.mp hwS))

/-- HOL planarity.hl:1404 `injective_azim_coplanar`：沿弦 `u→w` 的参数化
`t ↦ azim x v u ((1-t)•u + t•w)` 在不共面四点下是单射（a, b 均非零）。
重构证明（避开 HOL 的行列式计算）：
1. 由 `continuous_coplanar_fan` + 三点共线 ⇒ 共面，得 `¬Collinear3 x v u`、
   `¬Collinear3 x v p_a`、`¬Collinear3 x v p_b`；
2. HOL `AZIM_EQ`（`azim_eq_azim_iff`）：方位角相等给出
   `p_a ∈ aff_gt {x,v} {p_b}`，其射线刻画（`affGt_pair_iff`）给出
   `p_a - x = c•(p_b - x) + h•(v - x)`，故 `p_a ∈ aff {x,v,p_b}`，即
   `{x,v,p_a,p_b}` 共面于某三点包 `{r,s,q}`；
3. 若 `a ≠ b`，则 `u, w` 都是 `p_a, p_b` 的仿射组合
   （`u = lineMap p_a p_b (a/(a-b))`、`w = lineMap p_a p_b ((a-1)/(a-b))`），
   于是 `{x,v,u,w}` 也含于该三点包，与假设矛盾。故 `a = b`。 -/
theorem injective_azim_coplanar (x v u w : V3) (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hazim : azim x v u ((1 - a) • u + a • w) = azim x v u ((1 - b) • u + b • w)) :
    a = b := by
  rcases eq_or_ne a b with hab | hab
  · exact hab
  exfalso
  have hxv : x ≠ v := by
    intro he
    apply hcop
    have h : ({x, v, u, w} : Set V3) = ({v, u, w} : Set V3) := by
      rw [← he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h]
    exact coplanar_triple v u w
  have huw : u ≠ w := by
    intro he
    apply hcop
    have h : ({x, v, u, w} : Set V3) = ({x, v, u} : Set V3) := by
      rw [← he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h]
    exact coplanar_triple x v u
  have hncu : ¬ Collinear3 x v u := fun hcol =>
    hcop (coplanar_of_mem_line ((collinear3_iff_mem_affineSpan hxv).mp hcol))
  have hncpa : ¬ Collinear3 x v ((1 - a) • u + a • w) := fun hcol =>
    continuous_coplanar_fan x v u w hcop a ha
      (coplanar_of_mem_line' ((collinear3_iff_mem_affineSpan hxv).mp hcol))
  have hncpb : ¬ Collinear3 x v ((1 - b) • u + b • w) := fun hcol =>
    continuous_coplanar_fan x v u w hcop b hb
      (coplanar_of_mem_line' ((collinear3_iff_mem_affineSpan hxv).mp hcol))
  have hkey : (1 - a) • u + a • w ∈ affGt ({x, v} : Set V3)
      {(1 - b) • u + b • w} :=
    (azim_eq_azim_iff hncu hncpb hncpa).mp hazim.symm
  have hpbx : (1 - b) • u + b • w ≠ x := fun he =>
    hncpb (collinear3_pair_left he)
  have hpbv : (1 - b) • u + b • w ≠ v := fun he =>
    hncpb (collinear3_pair_right he)
  obtain ⟨c, hc0, h, hline⟩ :=
    (affGt_pair_iff (v0 := x) (v1 := v) (x := (1 - b) • u + b • w)
      (y := (1 - a) • u + a • w) hxv hpbx hpbv).mp hkey
  -- p_a ∈ aff {x, v, p_b}
  have hxS : x ∈ affineSpan ℝ ({x, v, (1 - b) • u + b • w} : Set V3) :=
    mem_affineSpan ℝ (by simp)
  have hvS : v ∈ affineSpan ℝ ({x, v, (1 - b) • u + b • w} : Set V3) :=
    mem_affineSpan ℝ (by simp)
  have hpbS : (1 - b) • u + b • w ∈
      affineSpan ℝ ({x, v, (1 - b) • u + b • w} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpaS : (1 - a) • u + a • w ∈
      (affineSpan ℝ ({x, v, (1 - b) • u + b • w} : Set V3) : Set V3) :=
    mem_affineSpan_triple_of_eq
      (show (1 - a) • u + a • w = x + c • ((1 - b) • u + b • w - x) + h • (v - x) from by
        rw [show (1 - a) • u + a • w = x + ((1 - a) • u + a • w - x) from by abel, hline]
        abel)
  have hcoppa : Coplanar ({x, v, (1 - a) • u + a • w, (1 - b) • u + b • w} : Set V3) :=
    ⟨x, v, (1 - b) • u + b • w, by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h1 | hz
      · rw [h1]
        exact SetLike.mem_coe.mpr hxS
      rcases hz with h1 | hz
      · rw [h1]
        exact SetLike.mem_coe.mpr hvS
      rcases hz with h1 | hz
      · rw [h1]
        exact hpaS
      · rw [hz]
        exact SetLike.mem_coe.mpr hpbS⟩
  obtain ⟨r, s, q, hsub⟩ := hcoppa
  have hsubpa : ({(1 - a) • u + a • w, (1 - b) • u + b • w} : Set V3) ⊆
      (affineSpan ℝ ({r, s, q} : Set V3) : Set V3) := by
    intro z hz
    refine hsub ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  -- u 与 w 都是 p_a, p_b 的仿射组合（a ≠ b）
  have hdiff : (1 - b) • u + b • w - ((1 - a) • u + a • w) = (a - b) • (u - w) := by
    module
  have hupa : u ∈ (affineSpan ℝ ({(1 - a) • u + a • w, (1 - b) • u + b • w} : Set V3) :
      Set V3) := by
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨a / (a - b), ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hdiff, smul_smul,
      show a / (a - b) * (a - b) = a from by field_simp]
    module
  have hwpb : w ∈ (affineSpan ℝ ({(1 - a) • u + a • w, (1 - b) • u + b • w} : Set V3) :
      Set V3) := by
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨(a - 1) / (a - b), ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hdiff, smul_smul,
      show (a - 1) / (a - b) * (a - b) = a - 1 from by field_simp]
    module
  refine hcop ⟨r, s, q, fun z hz => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h1 | hz
  · rw [h1]
    exact hsub (by simp)
  rcases hz with h1 | hz
  · rw [h1]
    exact hsub (by simp)
  rcases hz with h1 | hz
  · rw [h1]
    exact mem_affineSpan_carrier (affineSpan_mono ℝ hsubpa
      (SetLike.mem_coe.mp hupa))
  · rw [hz]
    exact mem_affineSpan_carrier (affineSpan_mono ℝ hsubpa
      (SetLike.mem_coe.mp hwpb))

/-! ## 第八块：fan_run_in_small（planarity.hl:1266–1627）

HOL `fan_run_in_small1_is_fan`（1266）：`separate1_sphere_fan` + 球面单
位化数乘（`scale_aff_gt_fan`/`scale_aff_ge_fan` + `imp_norm_not_zero_fan`）
把交点拉回 `ballnormFan`，与球面分离矛盾。
HOL `fan_run_in_small21_is_fan`（1464）：按「是否存在 h 使方位角在弦上
取到 w1 的方位角」分情形；核心推导（HOL 的 AFF_GT_1_2/AFF_GE_1_2 系数
比较 + AZIM_EQ_0_GE/AZIM_EQ_ALT）由私有辅助 `azim_eq_of_mem_inter` 完成，
两种情形分别用 `injective_azim_coplanar` 与原假设收尾。
HOL `fan_run_in_small2_is_fan`（1627）：small21 的 t < t1 直接推论。 -/

/-- HOL `imp_norm_not_zero_fan`：两点互异给出差向量范数非零。 -/
private theorem imp_norm_not_zero_fan {a b : V3} (h : a ≠ b) : ‖b - a‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))

/-- HOL fan_run_in_small21_is_fan（planarity.hl:1464–1627）的核心推导：
若 `y` 同时落在 `aff_gt {x} {v,(1-t)•u+t•w}` 与 `aff_ge {x} {v,w1}`
（t > 0，且 u、w1、(1-t)•u+t•w 均与 x,v 不共线），则 w1 落在
`aff_gt {x,v} {(1-t)•u+t•w}` 中，即 `azim x v u w1 = azim x v u z(t)`。
HOL 路线：`aff_gt_1_2`/`aff_ge_1_2` 系数比较得 w1 与 z(t) 沿 v 方向的
正倍数关系（`affGt_pair_iff`），再用 `azim_eq_azim_iff_alt`。 -/
private theorem azim_eq_of_mem_inter {x v u w w1 : V3} (y : V3) (t : ℝ)
    (hncu : ¬ Collinear3 x v u) (hncw1 : ¬ Collinear3 x v w1)
    (hncz : ¬ Collinear3 x v ((1 - t) • u + t • w))
    (hy1 : y ∈ affGt {x} {v, (1 - t) • u + t • w})
    (hy2 : y ∈ affGe {x} {v, w1}) :
    azim x v u w1 = azim x v u ((1 - t) • u + t • w) := by
  have hxv : x ≠ v := fun he => hncu (collinear3_of_eq he.symm)
  have hdisx : Disjoint ({x} : Set V3) {v, (1 - t) • u + t • w} :=
    disjoint_of_not_collinear3 hncz
  have hdisw1 : Disjoint ({x} : Set V3) {v, w1} :=
    disjoint_of_not_collinear3 hncw1
  rw [aff_gt_1_2 hdisx] at hy1
  simp only [Set.mem_setOf_eq] at hy1
  obtain ⟨a, b, g, -, hg, hsum, hyeq1⟩ := hy1
  rw [aff_ge_1_2 hdisw1] at hy2
  simp only [Set.mem_setOf_eq] at hy2
  obtain ⟨a', b', d, -, hd, hsum', hyeq2⟩ := hy2
  have ha : a = 1 - b - g := by linarith
  have ha' : a' = 1 - b' - d := by linarith
  have e1 : y - x = b • (v - x) + g • ((1 - t) • u + t • w - x) := by
    rw [hyeq1, ha]; module
  have e2 : y - x = b' • (v - x) + d • (w1 - x) := by
    rw [hyeq2, ha']; module
  have master : g • ((1 - t) • u + t • w - x) =
      (b' - b) • (v - x) + d • (w1 - x) := by
    have h12 : b • (v - x) + g • ((1 - t) • u + t • w - x) =
        b' • (v - x) + d • (w1 - x) := e1.symm.trans e2
    calc g • ((1 - t) • u + t • w - x)
        = (b • (v - x) + g • ((1 - t) • u + t • w - x)) - b • (v - x) := by module
      _ = (b' • (v - x) + d • (w1 - x)) - b • (v - x) := by rw [h12]
      _ = (b' - b) • (v - x) + d • (w1 - x) := by module
  by_cases hdz : d = 0
  · -- 退化：z(t) - x 平行 v - x，与 ¬Collinear3 x v z(t) 矛盾
    exfalso
    apply hncz
    have h1 : g • ((1 - t) • u + t • w - x) = (b' - b) • (v - x) := by
      rw [master, hdz, zero_smul, add_zero]
    have h2 : (1 - t) • u + t • w - x = (g⁻¹ * (b' - b)) • (v - x) := by
      have h3 := congrArg (fun p : V3 => g⁻¹ • p) h1
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hg), one_smul, smul_smul] at h3
      exact h3
    have hvx : v ≠ x := fun he => hncu (collinear3_of_eq he)
    exact (collinear3_iff_smul (v := x) (w := v) (w1 := (1 - t) • u + t • w) hvx).mpr
      ⟨g⁻¹ * (b' - b), h2⟩
  · -- d > 0：w1 - x 是 z(t) - x 的正倍数（沿 v - x 方向修正）
    have hdpos : 0 < d := hd.lt_of_ne (Ne.symm hdz)
    have hdd : d ≠ 0 := ne_of_gt hdpos
    have h1 : d • (w1 - x) = g • ((1 - t) • u + t • w - x) - (b' - b) • (v - x) := by
      have h0' : g • ((1 - t) • u + t • w - x) - (b' - b) • (v - x)
          = (b' - b) • (v - x) + d • (w1 - x) - (b' - b) • (v - x) := by
        rw [master]
      rw [h0']; module
    have h2 : w1 - x = (d⁻¹ * g) • ((1 - t) • u + t • w - x) +
        (d⁻¹ * -(b' - b)) • (v - x) := by
      have h3 := congrArg (fun p : V3 => d⁻¹ • p) h1
      rw [smul_smul, inv_mul_cancel₀ hdd, one_smul, smul_sub, smul_smul, smul_smul] at h3
      rw [h3]; module
    have hxz : (1 - t) • u + t • w ≠ x := fun he => hncz (collinear3_pair_left he)
    have hvz : (1 - t) • u + t • w ≠ v := fun he => hncz (collinear3_pair_right he)
    have hmem : w1 ∈ affGt ({x, v} : Set V3) {((1 - t) • u + t • w : V3)} := by
      refine (affGt_pair_iff (v0 := x) (v1 := v)
        (x := (1 - t) • u + t • w) (y := w1) hxv hxz hvz).mpr ⟨d⁻¹ * g, ?_, _, h2⟩
      exact mul_pos (inv_pos.mpr hdpos) hg
    exact (azim_eq_azim_iff_alt hncu hncw1 hncz).mpr hmem

/-- HOL planarity.hl:1464 `fan_run_in_small21_is_fan`：存在 t1 ∈ (0,1]
使得 t ∈ (0,t1] 时扰动扇区与 `aff_ge {x} {v,w1}` 无交。按 HOL 分两情形：
(A) 存在 h ∈ (0,1] 使 `azim x v u w1 = azim x v u ((1-h)•u+h•w)`：取
t1 = min ta (h/2)，`injective_azim_coplanar` 给出 h = t 与 t ≤ h/2 矛盾；
(B) 不存在：取 t1 = ta，直接与核心推导的方位角等式矛盾。 -/
theorem fan_run_in_small21_is_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hvw1 : {v, w1} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 < t → t ≤ t1 →
        affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v, w1} = ∅ := by
  obtain ⟨ta, ta0, ta1, hnc⟩ := exists_open_not_collinear hfan hvu huw
  have hncu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hncw1 : ¬ Collinear3 x v w1 := fan_not_collinear hfan hvw1
  by_cases hex : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      azim x v u w1 = azim x v u ((1 - h) • u + h • w)
  · -- 情形 A：方位角在弦上取到 w1 的方位角
    obtain ⟨h, h0, h1, haz⟩ := hex
    refine ⟨min ta (h / 2), lt_min ta0 (by linarith),
      (min_le_left _ _).trans ta1, ?_⟩
    intro t ht0 htle
    refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => ?_)
    have hle2 : t ≤ h / 2 := htle.trans (min_le_right _ _)
    have hncz : ¬ Collinear3 x v ((1 - t) • u + t • w) :=
      hnc t ht0.le (htle.trans (min_le_left _ _))
    have hazt : azim x v u w1 = azim x v u ((1 - t) • u + t • w) :=
      azim_eq_of_mem_inter y t hncu hncw1 hncz hy.1 hy.2
    have hht : h = t := injective_azim_coplanar x v u w hcop h t (ne_of_gt h0)
      (ne_of_gt ht0) (haz.symm.trans hazt)
    linarith
  · -- 情形 B：方位角在弦上取不到 w1 的方位角，直接矛盾
    refine ⟨ta, ta0, ta1, ?_⟩
    intro t ht0 htt
    refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => ?_)
    have hncz : ¬ Collinear3 x v ((1 - t) • u + t • w) := hnc t ht0.le htt
    have hazt : azim x v u w1 = azim x v u ((1 - t) • u + t • w) :=
      azim_eq_of_mem_inter y t hncu hncw1 hncz hy.1 hy.2
    exact hex ⟨t, ht0, htt.trans ta1, hazt⟩

/-- HOL planarity.hl:1627 `fan_run_in_small2_is_fan`：small21 的直接推论
（同一 t1，`t < t1` 蕴含 `t ≤ t1`）。 -/
theorem fan_run_in_small2_is_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hvw1 : {v, w1} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 < t → t < t1 →
        affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v, w1} = ∅ := by
  obtain ⟨t1, h0, h1, hb⟩ := fan_run_in_small21_is_fan hfan hvu huw hvw1 hcop
  exact ⟨t1, h0, h1, fun t ht0 htt1 => hb t ht0 (le_of_lt htt1)⟩

/-- HOL planarity.hl:1266 `fan_run_in_small1_is_fan`：小 t 时扰动扇区
`aff_gt {x} {v,(1-t)•u+t•w}` 与不相交边 {v1,u1} 的闭扇区无交。HOL 路线：
`separate1_sphere_fan`（球面分离）+ `th3`（= `disjoint_of_not_collinear3`）
+ `origin_is_not_aff_gt_fan`（x 不是交点）+ `imp_norm_not_zero_fan` 后
单位化数乘（`scale_aff_gt_fan`/`scale_aff_ge_fan`）把交点拉回
`ballnormFan x`，与球面分离矛盾。 -/
theorem fan_run_in_small1_is_fan (hfan : FAN x V E)
    (hdis : Disjoint ({v, u} : Set V3) {v1, u1}) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hv1u1 : {v1, u1} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 < t → t < t1 →
        affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v1, u1} = ∅ := by
  obtain ⟨ta, ta0, ta1, hnc⟩ := exists_open_not_collinear hfan hvu huw
  obtain ⟨h, h0, h1, hsep⟩ := separate1_sphere_fan hfan hdis hvu huw hv1u1 hcop
  refine ⟨min h ta, lt_min h0 ta0, (min_le_left _ _).trans h1, ?_⟩
  intro t ht0 hth
  have htta : t ≤ ta := le_of_lt (lt_of_lt_of_le hth (min_le_right _ _))
  have hzcol : ¬ Collinear3 x v ((1 - t) • u + t • w) := hnc t ht0.le htta
  have hxv : x ≠ v := fun he => hzcol (collinear3_of_eq he.symm)
  have hdisx : Disjoint ({x} : Set V3) {v, (1 - t) • u + t • w} :=
    disjoint_of_not_collinear3 hzcol
  have hdis1 : Disjoint ({x} : Set V3) {v1, u1} :=
    disjoint_of_not_collinear3 (fan_not_collinear hfan hv1u1)
  have hz1 : (1 - t) • u + t • w ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := fun hm =>
    hzcol ((collinear3_iff_mem_affineSpan hxv).mpr hm)
  have hxnotin : x ∉ affGt {x} {v, (1 - t) • u + t • w} :=
    origin_is_not_aff_gt_fan hz1 hdisx
  refine Set.eq_empty_iff_forall_notMem.mpr (fun z hz => ?_)
  have hxz : x ≠ z := by
    intro he
    subst he
    exact hxnotin hz.1
  have hn : ‖z - x‖ ≠ 0 := imp_norm_not_zero_fan hxz
  have hpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxz))
  have hs1 : ‖z - x‖⁻¹ • (z - x) + x ∈ affGt {x} {v, (1 - t) • u + t • w} :=
    scale_aff_gt_fan hdisx z _ hz.1 (inv_pos.mpr hpos)
  have hs2 : ‖z - x‖⁻¹ • (z - x) + x ∈ affGe {x} {v1, u1} :=
    scale_aff_ge_fan hdis1 z _ hz.2 (inv_nonneg.mpr (norm_nonneg _))
  have hs3 : ‖z - x‖⁻¹ • (z - x) + x ∈ ballnormFan x := by
    rw [ballnormFan]
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm,
      show x - (‖z - x‖⁻¹ • (z - x) + x) = -(‖z - x‖⁻¹ • (z - x)) from by module,
      norm_neg, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have hcontr : ‖z - x‖⁻¹ • (z - x) + x ∈
      (affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v1, u1} ∩ ballnormFan x : Set V3) :=
    ⟨⟨hs1, hs2⟩, hs3⟩
  rw [hsep t ht0 (lt_of_lt_of_le hth (min_le_left _ _)), Set.mem_empty_iff_false] at hcontr
  exact hcontr

/-! ## 第九块：AFF_GT_2_2 与 convex fan（planarity.hl:1646–1950）

本块移植 planarity.hl 的 `AFF_GT_2_2`（1646）、`extension_in_aff_2_2_fan`
（1658）、`inequality3_aim_in_convex_fan`（1688）、`fan_run_in_small3_is_fan`
（1714）、`properties_fully_surrounded`（1872）、`fan_run_in_small_is_fan`
（1897）。HOL 证明所用的 `WEDGE_LUNE_GT` 与 `AZIM_EQ_0_PI_EQ_COPLANAR`
（Multivariate-flyspeck.ml:3805/3161，未在库中移植）由两个解析型私有引理
`azim_cone_of_combo`、`azim_eq_0_or_pi_of_coplanar` 替代：都在轴向标准正交
标架下把方位角化为极坐标相位，再用 sin/cos 恒等式收尾。 -/

/-- HOL planarity.hl:1646 `AFF_GT_2_2`：`aff_gt {x,u} {v,w}` 的显式组合刻画。
`Disjoint {x,u} {v,w}` 仅排除跨集合重合（`x ≠ v`、`u ≠ w` 等）；`x = u` 或
`v = w` 时求和集按集合去重，正系数用对半拆分吸收（镜像 `aff_gt_1_2`）。 -/
theorem affGt2_2 (hdis : Disjoint ({x, u} : Set V3) {v, w}) :
    affGt {x, u} {v, w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 < t3 ∧ 0 < t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • u + t3 • v + t4 • w} := by
  have hdis' := Set.disjoint_left.mp hdis
  have hxv : x ≠ v := fun he => hdis' (Set.mem_insert _ _) (by rw [he]; simp)
  have hxw : x ≠ w := fun he => hdis' (Set.mem_insert _ _) (by rw [he]; simp)
  have huv : u ≠ v := fun he =>
    hdis' (Set.mem_insert_of_mem _ (Set.mem_singleton u)) (by rw [he]; simp)
  have huw : u ≠ w := fun he =>
    hdis' (Set.mem_insert_of_mem _ (Set.mem_singleton u)) (by rw [he]; simp)
  ext y
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    have hfv : 0 < f v := hpos v (by simp)
    have hfw : 0 < f w := hpos w (by simp)
    by_cases hux : x = u
    · by_cases hvw : v = w
      · -- x = u，v = w：求和集为 {x, v}，两系数对半拆分
        have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hux, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq] at hsum hone
        rw [Finset.sum_insert (by simp [hxv]), Finset.sum_singleton] at hsum hone
        refine ⟨f x / 2, f x / 2, f v / 2, f v / 2, by linarith, by linarith,
          by linarith, ?_⟩
        rw [hsum, ← hux, ← hvw]
        module
      · -- x = u：求和集为 {x, v, w}
        have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hux, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq] at hsum hone
        rw [Finset.sum_insert (by simp [hxv, hxw]), Finset.sum_insert (by simp [hvw]),
          Finset.sum_singleton] at hsum hone
        refine ⟨f x / 2, f x / 2, f v, f w, by linarith, by linarith,
          by linarith, ?_⟩
        rw [hsum, ← hux]
        module
    · by_cases hvw : v = w
      · -- v = w：求和集为 {x, u, v}
        have hTeq : hfin.toFinset = ({x, u, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq] at hsum hone
        rw [Finset.sum_insert (by simp [hux, hxv]), Finset.sum_insert (by simp [huv]),
          Finset.sum_singleton] at hsum hone
        refine ⟨f x, f u, f v / 2, f v / 2, by linarith, by linarith, by linarith, ?_⟩
        rw [hsum, ← hvw]
        module
      · -- 四点互异：直接取系数
        have hTeq : hfin.toFinset = ({x, u, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq] at hsum hone
        rw [Finset.sum_insert (by simp [hux, hxv, hxw]),
          Finset.sum_insert (by simp [huv, huw]), Finset.sum_insert (by simp [hvw]),
          Finset.sum_singleton] at hsum hone
        exact ⟨f x, f u, f v, f w, hfv, hfw, by linarith, by rw [hsum]; abel⟩
  · rintro ⟨t1, t2, t3, t4, ht3, ht4, hone, hy⟩
    have hfin0 : ({u, x} ∪ {w, v} : Set V3).Finite :=
      ((Set.finite_singleton x).insert u).union ((Set.finite_singleton v).insert w)
    have hfin : ({x, u} ∪ {v, w} : Set V3).Finite := hfin0.subset (by
      intro z hz
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto)
    by_cases hux : x = u
    · by_cases hvw : v = w
      · -- x = u，v = w：u、w 折到 x、v 上，正系数合并
        have hTeq : hfin.toFinset = ({x, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hux, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [← hux, ← hvw, ← add_smul] at hy
        refine ⟨fun z => if z = x then t1 + t2 else t3 + t4, hfin, ?_, ?_, ?_⟩
        · rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
          show y = (if x = x then t1 + t2 else t3 + t4) • x
            + (if v = x then t1 + t2 else t3 + t4) • v
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm), hy]
          module
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzv | hzw
          · rw [hzv]
            show 0 < (if v = x then t1 + t2 else t3 + t4)
            rw [if_neg (fun he => hxv he.symm)]
            linarith
          · rw [hzw]
            show 0 < (if w = x then t1 + t2 else t3 + t4)
            rw [if_neg (fun he => hxw he.symm)]
            linarith
        · rw [hTeq, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]
          show (if x = x then t1 + t2 else t3 + t4)
            + (if v = x then t1 + t2 else t3 + t4) = 1
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm)]
          linarith
      · -- x = u：函数在 {x, v, w} 上取值
        have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hux, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [← hux, ← add_smul] at hy
        refine ⟨fun z => if z = x then t1 + t2 else if z = v then t3 else t4, hfin, ?_, ?_, ?_⟩
        · rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
            Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
          show y = (if x = x then t1 + t2 else if x = v then t3 else t4) • x
            + ((if v = x then t1 + t2 else if v = v then t3 else t4) • v
              + (if w = x then t1 + t2 else if w = v then t3 else t4) • w)
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_pos (show (v : V3) = v from rfl),
            if_neg (show (w : V3) ≠ x from fun he => hxw he.symm),
            if_neg (show (w : V3) ≠ v from fun he => hvw he.symm), hy]
          module
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzv | hz
          · rw [hzv]
            show 0 < (if v = x then t1 + t2 else if v = v then t3 else t4)
            rw [if_neg (fun he => hxv he.symm), if_pos (rfl : v = v)]
            exact ht3
          · rw [hz]
            show 0 < (if w = x then t1 + t2 else if w = v then t3 else t4)
            rw [if_neg (fun he => hxw he.symm), if_neg (fun he => hvw he.symm)]
            exact ht4
        · rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
            Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
          show (if x = x then t1 + t2 else if x = v then t3 else t4)
            + ((if v = x then t1 + t2 else if v = v then t3 else t4)
              + (if w = x then t1 + t2 else if w = v then t3 else t4)) = 1
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_pos (show (v : V3) = v from rfl),
            if_neg (show (w : V3) ≠ x from fun he => hxw he.symm),
            if_neg (show (w : V3) ≠ v from fun he => hvw he.symm)]
          linarith
    · by_cases hvw : v = w
      · -- v = w：函数在 {x, u, v} 上取值，t3 + t4 合并
        have hTeq : hfin.toFinset = ({x, u, v} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hvw, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [← hvw] at hy
        refine ⟨fun z => if z = x then t1 else if z = u then t2 else t3 + t4, hfin, ?_, ?_, ?_⟩
        · rw [hTeq, Finset.sum_insert (by simp [hux, hxv]),
            Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
          show y = (if x = x then t1 else if x = u then t2 else t3 + t4) • x
            + ((if u = x then t1 else if u = u then t2 else t3 + t4) • u
              + (if v = x then t1 else if v = u then t2 else t3 + t4) • v)
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (u : V3) ≠ x from fun he => hux he.symm),
            if_pos (show (u : V3) = u from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_neg (show (v : V3) ≠ u from fun he => huv he.symm), hy]
          module
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzv | hz
          · rw [hzv]
            show 0 < (if v = x then t1 else if v = u then t2 else t3 + t4)
            rw [if_neg (fun he => hxv he.symm), if_neg (fun he => huv he.symm)]
            linarith
          · rw [Set.mem_singleton_iff.mp hz]
            show 0 < (if w = x then t1 else if w = u then t2 else t3 + t4)
            rw [if_neg (fun he => hxw he.symm), if_neg (fun he => huw he.symm)]
            linarith
        · rw [hTeq, Finset.sum_insert (by simp [hux, hxv]),
            Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
          show (if x = x then t1 else if x = u then t2 else t3 + t4)
            + ((if u = x then t1 else if u = u then t2 else t3 + t4)
              + (if v = x then t1 else if v = u then t2 else t3 + t4)) = 1
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (u : V3) ≠ x from fun he => hux he.symm),
            if_pos (show (u : V3) = u from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_neg (show (v : V3) ≠ u from fun he => huv he.symm)]
          linarith
      · -- 四点互异
        have hTeq : hfin.toFinset = ({x, u, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        refine ⟨fun z => if z = x then t1 else if z = u then t2 else if z = v then t3
          else t4, hfin, ?_, ?_, ?_⟩
        · rw [hTeq, Finset.sum_insert (by simp [hux, hxv, hxw]),
            Finset.sum_insert (by simp [huv, huw]), Finset.sum_insert (by simp [hvw]),
            Finset.sum_singleton]
          show y = (if x = x then t1 else if x = u then t2 else if x = v then t3 else t4) • x
            + ((if u = x then t1 else if u = u then t2 else if u = v then t3 else t4) • u
              + ((if v = x then t1 else if v = u then t2 else if v = v then t3 else t4) • v
                + (if w = x then t1 else if w = u then t2 else if w = v then t3
                  else t4) • w))
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (u : V3) ≠ x from fun he => hux he.symm),
            if_pos (show (u : V3) = u from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_neg (show (v : V3) ≠ u from fun he => huv he.symm),
            if_pos (show (v : V3) = v from rfl),
            if_neg (show (w : V3) ≠ x from fun he => hxw he.symm),
            if_neg (show (w : V3) ≠ u from fun he => huw he.symm),
            if_neg (show (w : V3) ≠ v from fun he => hvw he.symm), hy]
          module
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzv | hz
          · rw [hzv]
            show 0 < (if v = x then t1 else if v = u then t2 else if v = v then t3 else t4)
            rw [if_neg (fun he => hxv he.symm), if_neg (fun he => huv he.symm),
              if_pos (rfl : v = v)]
            exact ht3
          · rw [Set.mem_singleton_iff.mp hz]
            show 0 < (if w = x then t1 else if w = u then t2 else if w = v then t3
              else t4)
            rw [if_neg (fun he => hxw he.symm), if_neg (fun he => huw he.symm),
              if_neg (fun he => hvw he.symm)]
            exact ht4
        · rw [hTeq, Finset.sum_insert (by simp [hux, hxv, hxw]),
            Finset.sum_insert (by simp [huv, huw]), Finset.sum_insert (by simp [hvw]),
            Finset.sum_singleton]
          show (if x = x then t1 else if x = u then t2 else if x = v then t3 else t4)
            + ((if u = x then t1 else if u = u then t2 else if u = v then t3 else t4)
              + ((if v = x then t1 else if v = u then t2 else if v = v then t3 else t4)
                + (if w = x then t1 else if w = u then t2 else if w = v then t3
                  else t4))) = 1
          rw [if_pos (show (x : V3) = x from rfl),
            if_neg (show (u : V3) ≠ x from fun he => hux he.symm),
            if_pos (show (u : V3) = u from rfl),
            if_neg (show (v : V3) ≠ x from fun he => hxv he.symm),
            if_neg (show (v : V3) ≠ u from fun he => huv he.symm),
            if_pos (show (v : V3) = v from rfl),
            if_neg (show (w : V3) ≠ x from fun he => hxw he.symm),
            if_neg (show (w : V3) ≠ u from fun he => huw he.symm),
            if_neg (show (w : V3) ≠ v from fun he => hvw he.symm)]
          linarith

/-- HOL planarity.hl:1658 `extension_in_aff_2_2_fan`：弦 `v→w` 上的内点
组合仍落在 `aff_gt {x,u} {w,v}` 中（`affGt2_2` 的系数代入）。 -/
theorem extension_in_aff_2_2_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (t1 t2 t3 : ℝ) (ht3 : 0 < t3) (ht2 : 0 < t2) (hsum : t1 + t2 + t3 = 1) :
    t1 • x + t2 • v + t3 • ((1 - t) • u + t • w) ∈ affGt {x, u} {w, v} := by
  have huv : ({u, v} : Set V3) ∈ E := by
    have h : ({u, v} : Set V3) = ({v, u} : Set V3) := by
      ext z
      simp [Set.mem_insert_iff]
      tauto
    rw [h]; exact hvu
  have hncu : ¬ Collinear3 x u v := fan_not_collinear hfan huv
  have hncw : ¬ Collinear3 x u w := fan_not_collinear hfan huw
  have hxv : x ≠ v := by
    intro he
    exact hncu (collinear3_pair_left (v0 := x) (v1 := u) (x := v) he.symm)
  have hxw : x ≠ w := by
    intro he
    exact hncw (collinear3_pair_left (v0 := x) (v1 := u) (x := w) he.symm)
  have huvw : u ≠ w := by
    intro he
    exact hncw (collinear3_pair_right (v0 := x) (v1 := u) (x := w) he.symm)
  have huvne : u ≠ v := by
    intro he
    exact hncu (collinear3_pair_right (v0 := x) (v1 := u) (x := v) he.symm)
  have hdis : Disjoint ({x, u} : Set V3) {w, v} :=
    Set.disjoint_left.mpr (by
      intro a ha hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact hxw rfl
      · exact hxv rfl
      · exact huvw rfl
      · exact huvne rfl)
  rw [affGt2_2 hdis]
  refine ⟨t1, t3 * (1 - t), t3 * t, t2, mul_pos ht3 ht0, ht2, ?_, ?_⟩
  · linarith
  · rw [smul_add, smul_smul, smul_smul]
    module

/-- 实数纯虚指数的实部/虚部（cos/sin 提取的受控重写形式）。 -/
private theorem cexp_cos_re (r : ℝ) : (Complex.exp ((r : ℂ) * I)).re = Real.cos r := by
  have h := congrArg Complex.re (Complex.exp_mul_I (r : ℂ))
  simpa using h

private theorem cexp_sin_im (r : ℝ) : (Complex.exp ((r : ℂ) * I)).im = Real.sin r := by
  have h := congrArg Complex.im (Complex.exp_mul_I (r : ℂ))
  simpa using h

/-- 锥引理（`WEDGE_LUNE_GT`（Multivariate-flyspeck.ml:3805）在轴向标架下的
解析核心）：`0 < azim x u w v < π` 时，`y - x` 是 `v - x`、`w - x`（正系数）
与 `u - x`（任意系数）的组合，给出 `y` 不在轴 `xu` 上且
`0 < azim x u w y < azim x u w v`。证明：取轴 `u - x` 的标准正交标架，
`w`、`v` 的平面坐标写成极坐标 `e^{iψ}`、`e^{i(ψ+θv)}`，`y` 的平面坐标由
线性性与 `zOf_axis` 化为 `e^{iψ}(A cosθv·i + …)`，比较与 `azim x u w y`
的极坐标相位，用 `sin(ψ'+φ)`、`sin(φ-θv)` 的符号定出相位区间。 -/
private theorem azim_cone_of_combo {x u w v y : V3}
    (hncw : ¬ Collinear3 x u w) (hncv : ¬ Collinear3 x u v)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hy : y - x = a • (v - x) + b • (w - x) + c • (u - x)) :
    ¬ Collinear3 x u y ∧ 0 < azim x u w y ∧ azim x u w y < azim x u w v := by
  have hux : u ≠ x := by
    intro he
    exact hncw (collinear3_of_eq (v := x) (w := u) (w1 := w) he)
  obtain ⟨f1, f2, f3, hon, halign⟩ :=
    exists_on3_eq_smul (u - x) (sub_ne_zero.mpr hux)
  have hax : (u - x : V3) = dist u x • f3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨hp1, hp2⟩ := axis_perp hax hon
  set θv := azim x u w v with hθvdef
  obtain ⟨ψ, rb, ra, hrb, hra, hzw, hzv⟩ := azim_frame_spec hncw hncv hon hax hux
  have hwrep := rep_of_zOf hon hax hux w ψ rb hzw
  have hvrep := rep_of_zOf hon hax hux v (ψ + θv) ra hzv
  -- y 的平面坐标：线性性 + 轴向分量归零
  have hzline : zOf f1 f2 (y - x)
      = ((a * ra : ℝ) : ℂ) * Complex.exp (((ψ + θv : ℝ) : ℂ) * I)
        + ((b * rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * I) := by
    have h1 : y - x = a • (v - x) + (b • (w - x) + c • (u - x)) := by
      rw [hy]; abel
    rw [h1, zOf_add, zOf_smul, zOf_add, zOf_smul, zOf_smul, zOf_axis hax hon, hzv, hzw]
    push_cast
    ring
  have k1 : (y - x : V3) ⬝ᵥ f1
      = a * (ra * Real.cos (ψ + θv)) + b * (rb * Real.cos ψ) := by
    have h := congrArg Complex.re hzline
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_cos_re, cexp_cos_re] at h
    linarith
  have k2 : (y - x : V3) ⬝ᵥ f2
      = a * (ra * Real.sin (ψ + θv)) + b * (rb * Real.sin ψ) := by
    have h := congrArg Complex.im hzline
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_sin_im, cexp_sin_im] at h
    linarith
  have hsinpos : 0 < Real.sin θv :=
    Real.sin_pos_of_mem_Ioo (Set.mem_Ioo.mpr ⟨hθ0, hθπ⟩)
  have trig1 : ∀ A B α β γ : ℝ, (A * Real.sin α + B * Real.sin β) * Real.cos γ
      - (A * Real.cos α + B * Real.cos β) * Real.sin γ
      = A * Real.sin (α - γ) + B * Real.sin (β - γ) := by
    intro A B α β γ
    rw [Real.sin_sub, Real.sin_sub]
    ring
  have trig2 : ∀ A B α β γ : ℝ, (A * Real.cos α + B * Real.cos β) * Real.sin γ
      - (A * Real.sin α + B * Real.sin β) * Real.cos γ
      = A * Real.sin (γ - α) + B * Real.sin (γ - β) := by
    intro A B α β γ
    rw [Real.sin_sub, Real.sin_sub]
    ring
  by_cases hcy : Collinear3 x u y
  · -- y 在轴上：平面坐标为 0，与 v、w 正系数组合的虚部矛盾
    exfalso
    have hz0 : zOf f1 f2 (y - x) = 0 := by
      by_contra hne
      exact (zOf_ne_zero_iff hon hax hux y).mp hne hcy
    have hz1 : (y - x : V3) ⬝ᵥ f1 = 0 := by
      have h := congrArg Complex.re hz0
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      exact h
    have hz2 : (y - x : V3) ⬝ᵥ f2 = 0 := by
      have h := congrArg Complex.im hz0
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      exact h
    have hK1 : a * (ra * Real.cos (ψ + θv)) + b * (rb * Real.cos ψ) = 0 :=
      k1.symm.trans hz1
    have hK2 : a * (ra * Real.sin (ψ + θv)) + b * (rb * Real.sin ψ) = 0 :=
      k2.symm.trans hz2
    have hkey := trig2 (a * ra) (b * rb) (ψ + θv) ψ ψ
    rw [show (ψ - (ψ + θv) : ℝ) = -θv from by ring, show (ψ - ψ : ℝ) = 0 from by ring,
      Real.sin_zero, mul_zero, add_zero, Real.sin_neg, mul_neg] at hkey
    rw [show ((a * ra) * Real.cos (ψ + θv) : ℝ) = a * (ra * Real.cos (ψ + θv)) from by ring,
      show ((b * rb) * Real.cos ψ : ℝ) = b * (rb * Real.cos ψ) from by ring, hK1,
      show ((a * ra) * Real.sin (ψ + θv) : ℝ) = a * (ra * Real.sin (ψ + θv)) from by ring,
      show ((b * rb) * Real.sin ψ : ℝ) = b * (rb * Real.sin ψ) from by ring, hK2] at hkey
    have hcon : a * (ra * Real.sin θv) = 0 := by
      have hassoc : a * (ra * Real.sin θv) = a * ra * Real.sin θv := by ring
      rw [hassoc]
      linear_combination hkey
    have hposA : 0 < a * (ra * Real.sin θv) := mul_pos ha (mul_pos hra hsinpos)
    linarith
  · obtain ⟨ψ', r1', ry, hr1', hry, hzw2, hzy⟩ :=
      azim_frame_spec hncw hcy hon hax hux
    have heq : Complex.exp (((ψ : ℝ) : ℂ) * I) = Complex.exp (((ψ' : ℝ) : ℂ) * I) :=
      exp_pos_mul_eq hrb hr1' (hzw.symm.trans hzw2)
    have hcs : Real.cos ψ = Real.cos ψ' ∧ Real.sin ψ = Real.sin ψ' := by
      constructor
      · have h := congrArg Complex.re heq
        rw [cexp_cos_re, cexp_cos_re] at h
        exact h
      · have h := congrArg Complex.im heq
        rw [cexp_sin_im, cexp_sin_im] at h
        exact h
    have cospv : Real.cos (ψ' + θv) = Real.cos (ψ + θv) := by
      rw [Real.cos_add, Real.cos_add]
      rw [hcs.2, hcs.1]
    have sinpv : Real.sin (ψ' + θv) = Real.sin (ψ + θv) := by
      rw [Real.sin_add, Real.sin_add]
      rw [hcs.2, hcs.1]
    have cosw : Real.cos ψ' = Real.cos ψ := hcs.1.symm
    have sinw : Real.sin ψ' = Real.sin ψ := hcs.2.symm
    set φ := azim x u w y with hφdef
    have hy1' : (y - x : V3) ⬝ᵥ f1 = ry * Real.cos (ψ' + φ) := by
      have h := congrArg Complex.re hzy
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      rw [cexp_cos_re] at h
      linarith
    have hy2' : (y - x : V3) ⬝ᵥ f2 = ry * Real.sin (ψ' + φ) := by
      have h := congrArg Complex.im hzy
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, mul_one, one_mul] at h
      rw [cexp_sin_im] at h
      linarith
    have e1 : ry * Real.cos (ψ' + φ)
        = a * (ra * Real.cos (ψ' + θv)) + b * (rb * Real.cos ψ') := by
      rw [← hy1', cospv, cosw]
      exact k1
    have e2 : ry * Real.sin (ψ' + φ)
        = a * (ra * Real.sin (ψ' + θv)) + b * (rb * Real.sin ψ') := by
      rw [← hy2', sinpv, sinw]
      exact k2
    -- φ 的界：E1 给 sin φ > 0，故 0 < φ < π；E2 给 sin(φ - θv) < 0，故 φ < θv
    have hpos1 : 0 < a * (ra * Real.sin θv) := mul_pos ha (mul_pos hra hsinpos)
    have hE1 : ry * Real.sin φ = a * (ra * Real.sin θv) := by
      have h := trig1 (a * ra) (b * rb) (ψ' + θv) ψ' ψ'
      rw [show ((ψ' + θv) - ψ' : ℝ) = θv from by ring,
        show (ψ' - ψ' : ℝ) = 0 from by ring, Real.sin_zero, mul_zero, add_zero] at h
      calc ry * Real.sin φ
          = ry * (Real.sin (ψ' + φ) * Real.cos ψ'
            - Real.cos (ψ' + φ) * Real.sin ψ') := by
            congr 1
            rw [← Real.sin_sub, show (ψ' + φ - ψ' : ℝ) = φ from by ring]
        _ = (ry * Real.sin (ψ' + φ)) * Real.cos ψ'
            - (ry * Real.cos (ψ' + φ)) * Real.sin ψ' := by ring
        _ = a * (ra * Real.sin θv) := by
            rw [e2, e1]
            linear_combination h
    have hposry : 0 < ry * Real.sin φ := by rw [hE1]; exact hpos1
    have hφ0 : 0 ≤ φ := azim_nonneg x u w y
    have hφnz : φ ≠ 0 := by
      intro h
      rw [h, Real.sin_zero] at hposry
      norm_num at hposry
    have hφpos : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hφnz)
    have hφ2 : φ < 2 * Real.pi := azim_lt_two_pi x u w y
    have hφltπ : φ < Real.pi := by
      by_contra hc
      push_neg at hc
      have hnn : 0 ≤ Real.sin (φ - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hcon := mul_nonneg hry.le hnn
      have hE : ry * Real.sin φ = -(ry * Real.sin (φ - Real.pi)) := by
        have h3 : ry * Real.sin φ = ry * Real.sin ((φ - Real.pi) + Real.pi) := by
          congr 1; ring
        rw [h3, Real.sin_add, Real.cos_pi, Real.sin_pi]
        ring
      rw [hE1] at hE
      linarith
    refine ⟨hcy, hφpos, ?_⟩
    by_contra hc
    push_neg at hc
    have hnn : 0 ≤ Real.sin (φ - θv) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcon := mul_nonneg hry.le hnn
    have hposB : 0 < b * (rb * Real.sin θv) := mul_pos hb (mul_pos hrb hsinpos)
    have hE2 : ry * Real.sin (φ - θv) = -(b * (rb * Real.sin θv)) := by
      have h := trig1 (a * ra) (b * rb) (ψ' + θv) ψ' (ψ' + θv)
      rw [show ((ψ' + θv) - (ψ' + θv) : ℝ) = 0 from by ring,
        show (ψ' - (ψ' + θv) : ℝ) = -θv from by ring, Real.sin_zero, mul_zero,
        zero_add, Real.sin_neg, mul_neg] at h
      calc ry * Real.sin (φ - θv)
          = ry * (Real.sin (ψ' + φ) * Real.cos (ψ' + θv)
            - Real.cos (ψ' + φ) * Real.sin (ψ' + θv)) := by
            congr 1
            rw [← Real.sin_sub, show (ψ' + φ - (ψ' + θv) : ℝ) = φ - θv from by ring]
        _ = (ry * Real.sin (ψ' + φ)) * Real.cos (ψ' + θv)
            - (ry * Real.cos (ψ' + φ)) * Real.sin (ψ' + θv) := by ring
        _ = -(b * (rb * Real.sin θv)) := by
            rw [e2, e1]
            linear_combination h
    rw [hE2] at hcon
    linarith

/-- HOL planarity.hl:1688 `inequality3_aim_in_convex_fan`：弦 `v→w` 内点的
正组合的方位角严格落在 `0` 与 `azim x u w v` 之间（锥引理推论）。 -/
theorem inequality3_aim_in_convex_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (t1 t2 t3 : ℝ) (ht3 : 0 < t3) (ht2 : 0 < t2) (hsum : t1 + t2 + t3 = 1) :
    0 < azim x u w (t1 • x + t2 • v + t3 • ((1 - t) • u + t • w)) ∧
      azim x u w (t1 • x + t2 • v + t3 • ((1 - t) • u + t • w)) < azim x u w v := by
  have hncw : ¬ Collinear3 x u w := fan_not_collinear hfan huw
  have hncv : ¬ Collinear3 x u v := fan_not_collinear hfan (by
    have h : ({u, v} : Set V3) = ({v, u} : Set V3) := by
      ext z
      simp [Set.mem_insert_iff]
      tauto
    rw [h]; exact hvu)
  have hyc : t1 • x + t2 • v + t3 • ((1 - t) • u + t • w) - x
      = t2 • (v - x) + (t3 * t) • (w - x) + (t3 * (1 - t)) • (u - x) := by
    have h1 : t1 = 1 - t2 - t3 := by linarith
    rw [h1]
    module
  exact (azim_cone_of_combo hncw hncv hθ0 hθπ t2 (t3 * t) (t3 * (1 - t)) ht2
    (mul_pos ht3 ht0) hyc).2

/-- 仿射组合入三点仿射包（系数和为 1 的显式三元组合；
`mem_affineSpan_triple_of_eq` 的对称版本）。 -/
private theorem mem_affineSpan_of_combo {p q r z : V3} {c1 c2 c3 : ℝ}
    (hsum : c1 + c2 + c3 = 1) (hcomb : z = c1 • p + c2 • q + c3 • r) :
    z ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := by
  have hc1 : c1 = 1 - c2 - c3 := by linarith
  have hset : ({p, r, q} : Set V3) = ({p, q, r} : Set V3) := by
    ext a; simp; tauto
  rw [hcomb, hc1, ← hset]
  exact mem_affineSpan_triple_of_eq (x := p) (p := r) (q := q) (c := c2) (h := c3)
    (by module)

/-- HOL planarity.hl:1714 `fan_run_in_small3_is_fan`：w1 与 u 相邻
（`{u,w1} ∈ E`）时，小扰动扇区 `aff_gt {x} {v,(1-t)•u+t•w}` 与闭扇区
`aff_ge {x} {u,w1}` 无交。重构证明：交点 y 的两组系数
（`aff_gt_1_2`/`aff_ge_1_2`）给出
(1) y 不在轴 xu 上（否则弦点 z(t) ∈ aff{x,v,u}，四点共面，与
`continuous_coplanar_fan` 矛盾）；
(2) w1 系数 t3' > 0（否则 y ∈ aff{x,u}），于是 y - x = t2'•(u-x) + t3'•(w1-x)
给出 w1 ∈ aff_gt {x,u} {y}，`azim_eq_azim_iff_alt` 给
azim x u w w1 = azim x u w y；
(3) `inequality3_aim_in_convex_fan` 给 0 < azim x u w y < azim x u w v；
(4) w1 = w 时 azim x u w w = 0 与 (3) 矛盾；否则 `SIGMA_FAN` 最小性
azim x u w v ≤ azim x u w w1 = azim x u w y < azim x u w v 矛盾。 -/
theorem fan_run_in_small3_is_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (huw1 : {u, w1} ∈ E)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (hsigma : sigmaFan x V E u w = v)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 < t → t < t1 →
        affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {u, w1} = ∅ := by
  obtain ⟨ta, ta0, ta1, hnc⟩ := exists_open_not_collinear hfan hvu huw
  refine ⟨ta, ta0, ta1, ?_⟩
  intro t ht0 htt1
  have ht1 : t < 1 := lt_of_lt_of_le htt1 ta1
  have hncz : ¬ Collinear3 x v ((1 - t) • u + t • w) := hnc t ht0.le (le_of_lt htt1)
  have hncuv : ¬ Collinear3 x u v := by
    refine fan_not_collinear hfan ?_
    have h : ({u, v} : Set V3) = ({v, u} : Set V3) := by
      ext a; simp; tauto
    rw [h]; exact hvu
  have hncw : ¬ Collinear3 x u w := fan_not_collinear hfan huw
  have hncw1 : ¬ Collinear3 x u w1 := fan_not_collinear hfan huw1
  have hxu : x ≠ u := fun he => hncw (collinear3_of_eq he.symm)
  refine Set.eq_empty_iff_forall_notMem.mpr (fun y hy => ?_)
  obtain ⟨hy1, hy2⟩ := hy
  have hdisx : Disjoint ({x} : Set V3) ({v, (1 - t) • u + t • w} : Set V3) :=
    disjoint_of_not_collinear3 hncz
  rw [aff_gt_1_2 hdisx] at hy1
  simp only [Set.mem_setOf_eq] at hy1
  obtain ⟨t1', t2, t3, ht2, ht3, hsum, hyeq⟩ := hy1
  -- (1) y 不在轴 xu 上
  have hncy : ¬ Collinear3 x u y := by
    intro hcol
    obtain ⟨s, hsline⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
      ((collinear3_iff_mem_affineSpan hxu).mp hcol)
    have hycombo : y = (1 - s) • x + s • u := by
      rw [← hsline, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]; module
    have hne : t3 ≠ 0 := ne_of_gt ht3
    have heqy : t1' • x + t2 • v + t3 • ((1 - t) • u + t • w)
        = (1 - s) • x + s • u := hyeq.symm.trans hycombo
    have hzexpr : t3 • ((1 - t) • u + t • w)
        = (1 - s) • x + s • u - (t1' • x + t2 • v) := by
      calc t3 • ((1 - t) • u + t • w)
          = (t1' • x + t2 • v + t3 • ((1 - t) • u + t • w))
            - (t1' • x + t2 • v) := by module
        _ = (1 - s) • x + s • u - (t1' • x + t2 • v) := by rw [heqy]
    have hzmem : (1 - t) • u + t • w ∈
        (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) := by
      refine mem_affineSpan_of_combo (p := x) (q := v) (r := u)
        (c1 := t3⁻¹ * (1 - s) - t3⁻¹ * t1') (c2 := -(t3⁻¹ * t2))
        (c3 := t3⁻¹ * s) ?_ ?_
      · calc t3⁻¹ * (1 - s) - t3⁻¹ * t1' + -(t3⁻¹ * t2) + t3⁻¹ * s
            = t3⁻¹ * ((1 - s) - t1' - t2 + s) := by ring
          _ = t3⁻¹ * t3 := by congr 1; linarith
          _ = 1 := inv_mul_cancel₀ hne
      · show (1 - t) • u + t • w = (t3⁻¹ * (1 - s) - t3⁻¹ * t1') • x
          + -(t3⁻¹ * t2) • v + (t3⁻¹ * s) • u
        calc (1 - t) • u + t • w
            = t3⁻¹ • (t3 • ((1 - t) • u + t • w)) := by
              rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = t3⁻¹ • ((1 - s) • x + s • u - (t1' • x + t2 • v)) := by rw [hzexpr]
          _ = _ := by module
    refine continuous_coplanar_fan x v u w hcop t (ne_of_gt ht0)
      ⟨x, v, u, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | hzmem'
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · rw [hzmem']
      exact SetLike.mem_coe.mpr hzmem
  -- aff_ge 侧系数
  have hdisw1 : Disjoint ({x} : Set V3) ({u, w1} : Set V3) :=
    disjoint_of_not_collinear3 hncw1
  rw [aff_ge_1_2 hdisw1] at hy2
  simp only [Set.mem_setOf_eq] at hy2
  obtain ⟨t1'', t2', t3', ht2', ht3', hsum', hyeq2⟩ := hy2
  -- (2) t3' > 0，否则 y 落在轴上
  have ht3'0 : 0 < t3' := by
    by_contra hcon
    push_neg at hcon
    have h0 : t3' = 0 := le_antisymm hcon ht3'
    refine hncy ((collinear3_iff_mem_affineSpan hxu).mpr
      (mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t2', ?_⟩))
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hyeq2, h0, zero_smul,
      add_zero]
    have ht : t1'' = 1 - t2' := by linarith
    rw [ht]
    module
  -- w1 ∈ aff_gt {x,u} {y}
  have hyxc : y - x = t2' • (u - x) + t3' • (w1 - x) := by
    have h1 : t1'' = 1 - t2' - t3' := by linarith
    rw [hyeq2, h1]
    module
  have hyx : y ≠ x := fun he => hncy (collinear3_pair_left he)
  have hyu : y ≠ u := fun he => hncy (collinear3_pair_right he)
  have hne3 : t3' ≠ 0 := ne_of_gt ht3'0
  have hmem : w1 ∈ affGt ({x, u} : Set V3) {y} := by
    refine (affGt_pair_iff (v0 := x) (v1 := u) (x := y) (y := w1) hxu hyx hyu).mpr
      ⟨t3'⁻¹, inv_pos.mpr ht3'0, -(t2' * t3'⁻¹), ?_⟩
    show w1 - x = t3'⁻¹ • (y - x) + -(t2' * t3'⁻¹) • (u - x)
    rw [hyxc, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne3, one_smul]
    module
  have hazim : azim x u w w1 = azim x u w y :=
    (azim_eq_azim_iff_alt hncw hncw1 hncy).mpr hmem
  -- (3) 锥引理
  obtain ⟨hBE, hYEU⟩ := inequality3_aim_in_convex_fan hfan hvu huw hθ0 hθπ
    t ht0 ht1 t1' t2 t3 ht3 ht2 hsum
  rw [← hyeq] at hBE hYEU
  -- (4) 终局矛盾
  rcases eq_or_ne w1 w with rfl | hw1w
  · rw [azim_self] at hazim
    linarith
  · have hw1edge : w1 ∈ setOfEdge u V E :=
      (properties_of_setOfEdge_fan x V E u w1 hfan).mp huw1
    have hwedge : w ∈ setOfEdge u V E :=
      (properties_of_setOfEdge_fan x V E u w hfan).mp huw
    by_cases hsingle : setOfEdge u V E = {w}
    · exact hw1w (by
        rw [hsingle] at hw1edge
        exact Set.mem_singleton_iff.mp hw1edge)
    · obtain ⟨-, -, hmin⟩ := SIGMA_FAN hsingle hfan hwedge
      have hle := hmin w1 hw1edge hw1w
      rw [hsigma] at hle
      linarith

/-- 三点仿射包 membership 的双系数刻画（差落在 `span {b-a, c-a}`）。 -/
private theorem exists_combo_of_mem_affineSpan3 {a b c z : V3}
    (hz : z ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3)) :
    ∃ d1 d2 : ℝ, z = a + d1 • (b - a) + d2 • (c - a) := by
  have h1 : z -ᵥ a ∈ vectorSpan ℝ ({a, b, c} : Set V3) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (SetLike.mem_coe.mp hz)
      (mem_affineSpan ℝ (by simp))
  rw [vectorSpan_eq_span_vsub_set_right ℝ
    (by simp : a ∈ ({a, b, c} : Set V3))] at h1
  have hle : Submodule.span ℝ ((· -ᵥ a) '' ({a, b, c} : Set V3)) ≤
      Submodule.span ℝ ({b - a, c - a} : Set V3) := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨z', hz'set, hp⟩
    dsimp only at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'set
    rcases hz'set with hz' | hz' | hz'
    · rw [← hp, hz', vsub_self]
      exact Submodule.zero_mem _
    · rw [← hp, hz', vsub_eq_sub]
      exact Submodule.subset_span (by simp)
    · rw [← hp, hz', vsub_eq_sub]
      exact Submodule.subset_span (by simp)
  obtain ⟨d1, d2, hd⟩ := Submodule.mem_span_pair.mp (hle h1)
  have hd' : d1 • (b - a) + d2 • (c - a) = z - a := by
    rw [hd, vsub_eq_sub]
  refine ⟨d1, d2, ?_⟩
  calc z = a + (z - a) := by abel
    _ = a + (d1 • (b - a) + d2 • (c - a)) := by rw [hd']
    _ = a + d1 • (b - a) + d2 • (c - a) := by abel

/-- 共面提取的抽象 ℂ 核心：两组实系数组合共用一对复数 P、Q，且轴向组合
为零、w 侧组合非零时，v 侧组合是 w 侧组合的实倍数。 -/
private theorem complex_mul_of_span_two {P Q zv zw : ℂ}
    {β1 β2 α1 α2 γ1 γ2 : ℝ}
    (hzu : ((β1 : ℝ) : ℂ) * P + ((β2 : ℝ) : ℂ) * Q = 0)
    (hzv : zv = ((α1 : ℝ) : ℂ) * P + ((α2 : ℝ) : ℂ) * Q)
    (hzw : zw = ((γ1 : ℝ) : ℂ) * P + ((γ2 : ℝ) : ℂ) * Q)
    (hβ : β1 ≠ 0 ∨ β2 ≠ 0) (hzw0 : zw ≠ 0) :
    ∃ μ : ℝ, zv = ((μ : ℝ) : ℂ) * zw := by
  by_cases hβ1 : β1 = 0
  · have hβ2 : β2 ≠ 0 := by
      rcases hβ with h | h
      · exact absurd hβ1 h
      · exact h
    have hβ2' : ((β2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ2
    have h1 : ((β2 : ℝ) : ℂ) * Q = 0 := by
      have h1' := hzu
      rw [hβ1, Complex.ofReal_zero, zero_mul, zero_add] at h1'
      exact h1'
    have hQ : Q = 0 := by
      have h2 : Q = (((β2 : ℝ) : ℂ)⁻¹ * ((β2 : ℝ) : ℂ)) * Q := by
        rw [inv_mul_cancel₀ hβ2', one_mul]
      calc Q = (((β2 : ℝ) : ℂ)⁻¹ * ((β2 : ℝ) : ℂ)) * Q := h2
        _ = ((β2 : ℝ) : ℂ)⁻¹ * (((β2 : ℝ) : ℂ) * Q) := by ring
        _ = ((β2 : ℝ) : ℂ)⁻¹ * 0 := by rw [h1]
        _ = 0 := by rw [mul_zero]
    have hγ1 : γ1 ≠ 0 := by
      intro h0
      rw [hzw, h0, hQ] at hzw0
      simp at hzw0
    have hd1 : ((α1 / γ1 : ℝ) : ℂ) * ((γ1 : ℝ) : ℂ) = ((α1 : ℝ) : ℂ) := by
      exact_mod_cast div_mul_cancel₀ α1 hγ1
    refine ⟨α1 / γ1, ?_⟩
    rw [hzv, hzw, hQ, mul_add, ← mul_assoc, hd1]
    simp [mul_zero]
  · have hβ1' : ((β1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ1
    have hP : P = ((-(β2 / β1) : ℝ) : ℂ) * Q := by
      have h1 : ((β1 : ℝ) : ℂ) * P = -((β2 : ℝ) : ℂ) * Q := by
        linear_combination hzu
      have h2 : P = (((β1 : ℝ) : ℂ)⁻¹ * ((β1 : ℝ) : ℂ)) * P := by
        rw [inv_mul_cancel₀ hβ1', one_mul]
      calc P = (((β1 : ℝ) : ℂ)⁻¹ * ((β1 : ℝ) : ℂ)) * P := h2
        _ = ((β1 : ℝ) : ℂ)⁻¹ * (((β1 : ℝ) : ℂ) * P) := by ring
        _ = ((β1 : ℝ) : ℂ)⁻¹ * (-((β2 : ℝ) : ℂ) * Q) := by rw [h1]
        _ = ((-(β2 / β1) : ℝ) : ℂ) * Q := by
            push_cast
            field_simp [hβ1']
    have hzvQ : zv = ((α2 - α1 * β2 / β1 : ℝ) : ℂ) * Q := by
      rw [hzv, hP]; push_cast; ring
    have hzwQ : zw = ((γ2 - γ1 * β2 / β1 : ℝ) : ℂ) * Q := by
      rw [hzw, hP]; push_cast; ring
    have hκ : γ2 - γ1 * β2 / β1 ≠ 0 := by
      intro h0
      rw [hzwQ, h0] at hzw0
      simp at hzw0
    have hd2 : (((α2 - α1 * β2 / β1 : ℝ) / (γ2 - γ1 * β2 / β1 : ℝ) : ℝ) : ℂ)
        * ((γ2 - γ1 * β2 / β1 : ℝ) : ℂ) = ((α2 - α1 * β2 / β1 : ℝ) : ℂ) := by
      exact_mod_cast div_mul_cancel₀ _ hκ
    refine ⟨(α2 - α1 * β2 / β1) / (γ2 - γ1 * β2 / β1), ?_⟩
    rw [hzvQ, hzwQ, ← mul_assoc, hd2]

/-- HOL `AZIM_EQ_0_PI_EQ_COPLANAR`（Multivariate-flyspeck.ml:3161）的解析
替代：四点 {x,u,v,w} 共面且 v、w 都不在轴 xu 上时，v-x 与 w-x 在轴向
正交标架下的 ℂ 平面坐标成实倍数，故 θ = azim x u w v 的相位 e^{iθ} 为
实数，即 sin θ = 0，结合 0 ≤ θ < 2π 得 θ ∈ {0, π}。 -/
private theorem azim_eq_0_or_pi_of_coplanar {x u v w : V3}
    (hncv : ¬ Collinear3 x u v) (hncw : ¬ Collinear3 x u w)
    (hcop : Coplanar ({x, u, v, w} : Set V3)) :
    azim x u w v = 0 ∨ azim x u w v = Real.pi := by
  have hux : u ≠ x := fun he => hncw (collinear3_of_eq he)
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (u - x) (sub_ne_zero.mpr hux)
  have hax : (u - x : V3) = dist u x • f3 := by rw [dist_eq_norm]; exact halign
  have hzwne : zOf f1 f2 (w - x) ≠ 0 := (zOf_ne_zero_iff hon hax hux w).mpr hncw
  obtain ⟨ψ, rb, ra, hrb, hra, hzwrep, hzvrep⟩ := azim_frame_spec hncw hncv hon hax hux
  -- 共面性 → 公共平面表示 → ℂ 坐标实相关
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, zOf f1 f2 (v - x) = ((μ : ℝ) : ℂ) * zOf f1 f2 (w - x) := by
    obtain ⟨a, b, c, hsub⟩ := hcop
    have hxS : x ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have huS : u ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have hvS : v ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have hwS : w ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    obtain ⟨ξ1, ξ2, hξ⟩ := exists_combo_of_mem_affineSpan3 hxS
    obtain ⟨β1, β2, hβ⟩ := exists_combo_of_mem_affineSpan3 huS
    obtain ⟨α1, α2, hα⟩ := exists_combo_of_mem_affineSpan3 hvS
    obtain ⟨γ1, γ2, hγ⟩ := exists_combo_of_mem_affineSpan3 hwS
    have hvx : v - x = (α1 - ξ1) • (b - a) + (α2 - ξ2) • (c - a) := by
      rw [hα, hξ]; module
    have hwx : w - x = (γ1 - ξ1) • (b - a) + (γ2 - ξ2) • (c - a) := by
      rw [hγ, hξ]; module
    have huxc : u - x = (β1 - ξ1) • (b - a) + (β2 - ξ2) • (c - a) := by
      rw [hβ, hξ]; module
    have hzlin : ∀ p q : V3, ∀ d1 d2 : ℝ, p - q = d1 • (b - a) + d2 • (c - a) →
        zOf f1 f2 (p - q) = ((d1 : ℝ) : ℂ) * zOf f1 f2 (b - a)
          + ((d2 : ℝ) : ℂ) * zOf f1 f2 (c - a) := by
      intro p q d1 d2 hd
      rw [hd, zOf_add, zOf_smul, zOf_smul]
    have hzc := hzlin v x (α1 - ξ1) (α2 - ξ2) hvx
    have hzd := hzlin w x (γ1 - ξ1) (γ2 - ξ2) hwx
    have hzu0 := hzlin u x (β1 - ξ1) (β2 - ξ2) huxc
    have hf3z : zOf f1 f2 f3 = 0 := by
      obtain ⟨-, -, -, -, h13, h23, -⟩ := hon
      unfold zOf
      rw [dotProduct_comm f3 f1, dotProduct_comm f3 f2, h13, h23]
      norm_num
    rw [hax, zOf_smul, hf3z, mul_zero] at hzu0
    have hne2 : β1 - ξ1 ≠ 0 ∨ β2 - ξ2 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hux
      have hzero : u - x = 0 := by
        rw [huxc, hcon.1, hcon.2]
        module
      exact sub_eq_zero.mp hzero
    exact complex_mul_of_span_two hzu0.symm hzc hzd hne2 hzwne
  -- 相位：ra • e^{i(ψ+θ)} = μ • rb • e^{iψ} ⟹ ra • e^{iθ} = μ • rb ∈ ℝ
  have hkey : ((ra : ℝ) : ℂ) * Complex.exp (((azim x u w v : ℝ) : ℂ) * I)
      = ((μ * rb : ℝ) : ℂ) := by
    have h1 : ((ra : ℝ) : ℂ)
          * Complex.exp ((((ψ + azim x u w v : ℝ) : ℂ)) * I)
        = ((μ : ℝ) : ℂ) * (((rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * I)) := by
      rw [← hzvrep, ← hzwrep]
      exact hμ
    have hexp : Complex.exp ((((ψ + azim x u w v : ℝ) : ℂ)) * I)
        = Complex.exp (((ψ : ℝ) : ℂ) * I)
          * Complex.exp (((azim x u w v : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp] at h1
    have h2 : ((ra : ℝ) : ℂ) * Complex.exp (((azim x u w v : ℝ) : ℂ) * I)
          * Complex.exp (((ψ : ℝ) : ℂ) * I)
        = ((μ * rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * I) := by
      push_cast
      linear_combination h1
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) h2
  have hsin : Real.sin (azim x u w v) = 0 := by
    have h := congrArg Complex.im hkey
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, cexp_sin_im,
      mul_zero, add_zero, zero_mul] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by exact_mod_cast (ne_of_gt hra))
    · exact h'
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hn0 : (0:ℤ) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hnle : ((n:ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega)
    have hθn : azim x u w v < 0 := by rw [← hn]; nlinarith [hnle, hpi]
    exact absurd (azim_nonneg x u w v) (not_le.mpr hθn)
  have hn2 : n < 2 := by
    by_contra hcon
    push_neg at hcon
    have hnge : (2:ℝ) ≤ ((n:ℤ) : ℝ) := by exact_mod_cast (by omega)
    have hθbig : 2 * Real.pi ≤ azim x u w v := by rw [← hn]; nlinarith [hnge, hpi]
    exact absurd hθbig (not_le.mpr (azim_lt_two_pi x u w v))
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · exact Or.inl (by rw [← hn]; push_cast; norm_num)
  · exact Or.inr (by rw [← hn]; push_cast; norm_num)

/-- HOL planarity.hl:1872 `properties_fully_surrounded`：扇区角严格介于
0 与 π 之间时四点不共面（`AZIM_EQ_0_PI_EQ_COPLANAR` 的逆否形式）。 -/
theorem properties_fully_surrounded (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi) :
    ¬ Coplanar ({x, v, u, w} : Set V3) := by
  intro hcop
  have hncv : ¬ Collinear3 x u v := by
    refine fan_not_collinear hfan ?_
    have h : ({u, v} : Set V3) = ({v, u} : Set V3) := by ext a; simp; tauto
    rw [h]; exact hvu
  have hncw : ¬ Collinear3 x u w := fan_not_collinear hfan huw
  have hset : ({x, u, v, w} : Set V3) = ({x, v, u, w} : Set V3) := by
    ext a; simp; tauto
  rw [← hset] at hcop
  rcases azim_eq_0_or_pi_of_coplanar hncv hncw hcop with h | h
  · linarith
  · linarith

/-- HOL planarity.hl:1897 证明内嵌引理 `lem`：`aff_ge {x} {v1,v} = aff_ge {x} {v,v1}`
（集合参数的对称性）。 -/
private theorem affGe_pair_comm {x a b : V3} :
    affGe {x} {a, b} = affGe {x} {b, a} := by
  have h : ({a, b} : Set V3) = ({b, a} : Set V3) := by
    ext p; simp; tauto
  rw [h]

/-- HOL planarity.hl:1897 `fan_run_in_small_is_fan`：任意相邻边 {v1,w1} ∈ E
的闭扇区都与小扰动扇区无交。按 HOL 分四情形：
v1 = v 用 small2；v1 = u 用 small3（轴交换）；w1 = v 用 small2（换 v）；
w1 = u 用 small3（换轴）；其余 {v,u} ∩ {v1,w1} = ∅ 用 small1。 -/
theorem fan_run_in_small_is_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hv1w1 : {v1, w1} ∈ E)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (hsigma : sigmaFan x V E u w = v) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 ≤ 1 ∧
      ∀ t : ℝ, 0 < t → t < t1 →
        affGt {x} {v, (1 - t) • u + t • w} ∩ affGe {x} {v1, w1} = ∅ := by
  have hcop := properties_fully_surrounded hfan hvu huw hθ0 hθπ
  rcases eq_or_ne v1 v with rfl | hv1v
  · exact fan_run_in_small2_is_fan hfan hvu huw hv1w1 hcop
  rcases eq_or_ne v1 u with rfl | hv1u
  · exact fan_run_in_small3_is_fan hfan hvu huw hv1w1 hcop hsigma hθ0 hθπ
  rcases eq_or_ne w1 v with rfl | hw1v
  · rw [affGe_pair_comm]
    refine fan_run_in_small2_is_fan hfan hvu huw ?_ hcop
    rw [show ({w1, v1} : Set V3) = ({v1, w1} : Set V3) from by
      ext a; simp; tauto]
    exact hv1w1
  rcases eq_or_ne w1 u with rfl | hw1u
  · rw [affGe_pair_comm]
    refine fan_run_in_small3_is_fan hfan hvu huw ?_ hcop hsigma hθ0 hθπ
    rw [show ({w1, v1} : Set V3) = ({v1, w1} : Set V3) from by
      ext a; simp; tauto]
    exact hv1w1
  refine fan_run_in_small1_is_fan hfan ?_ hvu huw hv1w1 hcop
  refine Set.disjoint_left.mpr ?_
  intro a ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with hva | hua <;> rcases hb with hvb | hwb
  · exact hv1v (hva.symm.trans hvb).symm
  · exact hw1v (hva.symm.trans hwb).symm
  · exact hv1u (hua.symm.trans hvb).symm
  · exact hw1u (hua.symm.trans hwb).symm

/-! ## 第十块：`fan_run1_in_small_is_fan` 与不共线推论
（planarity.hl:1948/2126/2224）

HOL 的 `fan_run1_in_small_is_fan` 对 `CARD E'` 做归纳：先对任意有限边族
（此处用 `Finset (Set V3)` 表示）给出 `h`；基例空集取 `h = 1/2`，归纳步把
单条边的 `fan_run_in_small_is_fan` 与归纳假设的最小 `h` 合并（`min`），
并集的无交性由 `Disjoint s (t ∪ u)` 分配到两侧。最后经
`Set.Finite.toFinset` 换回子集 `E' ⊆ E`。 -/

/-- `Graph E` 的展开：每条边都是两点集 `{v1, w1}`。 -/
private theorem exists_pair_of_graphEdge {e : Set V3} (hgraph : Graph E) (he : e ∈ E) :
    ∃ v1 w1 : V3, e = ({v1, w1} : Set V3) := by
  obtain ⟨hfin, hcard⟩ := hgraph e he
  have hcoe : (↑hfin.toFinset : Set V3) = e := hfin.coe_toFinset
  obtain ⟨a, b, -, heq⟩ := Finset.card_eq_two.mp hcard
  exact ⟨a, b, by rw [← hcoe, heq]; simp⟩

/-- HOL planarity.hl:1948 `fan_run1_in_small_is_fan` 的有限归纳核：
有限边族 `T ⊆ E` 时存在 `h ∈ (0,1]`，使小扰动扇区与
`⋃ e ∈ T, aff_ge {x} e` 无交。 -/
private theorem fan_run1_in_small_is_fan_finset (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (hsigma : sigmaFan x V E u w = v) (T : Finset (Set V3))
    (hT : ∀ e ∈ T, e ∈ E) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ s : ℝ, 0 < s → s < h →
        affGt {x} {v, (1 - s) • u + s • w} ∩ (⋃ e ∈ T, affGe {x} e) = ∅ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro s _ _
    simp
  | insert e T heT ih =>
    have heE : e ∈ E := hT e (Finset.mem_insert_self e T)
    obtain ⟨v1, w1, hpair⟩ := exists_pair_of_graphEdge hfan.2.1 heE
    have hepair : ({v1, w1} : Set V3) ∈ E := by rw [← hpair]; exact heE
    obtain ⟨he, he0, he1, he2⟩ :=
      fan_run_in_small_is_fan hfan hvu huw hepair hθ0 hθπ hsigma
    rw [← hpair] at he2
    obtain ⟨ht, ht0, ht1, ht2⟩ := ih (fun a ha => hT a (Finset.mem_insert_of_mem ha))
    refine ⟨min he ht, lt_min he0 ht0, min_le_iff.mpr (Or.inl he1), ?_⟩
    intro s hs0 hsm
    rw [Finset.set_biUnion_insert, ← Set.disjoint_iff_inter_eq_empty,
      Set.disjoint_union_right]
    refine
      ⟨Set.disjoint_iff_inter_eq_empty.mpr (he2 s hs0 (lt_of_lt_of_le hsm (min_le_left _ _))),
        Set.disjoint_iff_inter_eq_empty.mpr (ht2 s hs0 (lt_of_lt_of_le hsm (min_le_right _ _)))⟩

/-- HOL planarity.hl:1948 `fan_run1_in_small_is_fan`：`E' ⊆ E` 的
任意（有限）边子集的闭扇区之并，都与充分小的扰动扇区无交。 -/
theorem fan_run1_in_small_is_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hE' : E' ⊆ E)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (hsigma : sigmaFan x V E u w = v) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ s : ℝ, 0 < s → s < h →
        affGt {x} {v, (1 - s) • u + s • w} ∩ {z | ∃ e ∈ E', z ∈ affGe {x} e} = ∅ := by
  have hfin : E'.Finite := (setEdgesFiniteFan hfan).subset hE'
  obtain ⟨h, hp0, hp1, hp2⟩ :=
    fan_run1_in_small_is_fan_finset hfan hvu huw hθ0 hθπ hsigma hfin.toFinset
      (fun e he => hE' (hfin.mem_toFinset.mp he))
  refine ⟨h, hp0, hp1, ?_⟩
  intro s hs0 hsh
  have hset : {z : V3 | ∃ e ∈ E', z ∈ affGe {x} e} =
      ⋃ e ∈ hfin.toFinset, affGe {x} e := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact exists_congr fun e => and_congr (hfin.mem_toFinset (a := e)).symm Iff.rfl
  rw [hset]
  exact hp2 s hs0 hsh

/-- HOL planarity.hl:2126 `not_collinear_is_properties_fully_surrounded1`：
`0 ≤ t ≤ 1` 时弦点 `(1-t)•u + t•w` 不与 `x, v` 共线。
`t = 0`/`t = 1` 端点即 `u`/`w`；中间情形由 `x, v, 弦点` 共线推出
`w ∈ aff{x,v,u}`，于是四点共面，与 `properties_fully_surrounded` 矛盾。 -/
theorem not_collinear_is_properties_fully_surrounded1 (hfan : FAN x V E)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ¬ Collinear3 x v ((1 - t) • u + t • w) := by
  have hxv : x ≠ v := fun he =>
    fan_not_collinear hfan hvu (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  rcases eq_or_lt_of_le ht0 with rfl | htmid
  · intro hcol
    simp only [sub_zero, one_smul, zero_smul, add_zero] at hcol
    exact fan_not_collinear hfan hvu hcol
  rcases eq_or_lt_of_le ht1 with rfl | htmid1
  · intro hcol
    simp only [sub_self, one_smul, zero_smul, zero_add] at hcol
    exact properties_fully_surrounded hfan hvu huw hθ0 hθπ
      (coplanar_of_mem_line' (p := u) ((collinear3_iff_mem_affineSpan hxv).mp hcol))
  · intro hcol
    have hne : t ≠ 0 := ne_of_gt htmid
    have hmem : ((1 - t) • u + t • w : V3) ∈
        (affineSpan ℝ ({x, v} : Set V3) : Set V3) :=
      (collinear3_iff_mem_affineSpan hxv).mp hcol
    have hmem3 : ((1 - t) • u + t • w : V3) ∈
        affineSpan ℝ ({x, v, u} : Set V3) :=
      affineSpan_mono ℝ subset_pair3 (SetLike.mem_coe.mp hmem)
    have hu3 : (u : V3) ∈ affineSpan ℝ ({x, v, u} : Set V3) :=
      mem_affineSpan ℝ (by simp)
    have hdir : (t⁻¹ : ℝ) • ((1 - t) • u + t • w - u) ∈
        (affineSpan ℝ ({x, v, u} : Set V3)).direction :=
      Submodule.smul_mem _ _ (AffineSubspace.vsub_mem_direction hmem3 hu3)
    have hw3 : (w : V3) ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) := by
      have hsplit : ((1 - t) • u + t • w - u : V3) = t • (w - u) := by module
      have hadd : w = (t⁻¹ : ℝ) • ((1 - t) • u + t • w - u) +ᵥ u := by
        rw [vadd_eq_add, hsplit, smul_smul, inv_mul_cancel₀ hne, one_smul, sub_add_cancel]
      rw [hadd]
      exact AffineSubspace.vadd_mem_of_mem_direction hdir hu3
    refine properties_fully_surrounded hfan hvu huw hθ0 hθπ ⟨x, v, u, fun z hz => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h1 | hz
    · rw [h1]
      exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    rcases hz with h1 | hz
    · rw [h1]
      exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    rcases hz with h1 | hz
    · rw [h1]
      exact SetLike.mem_coe.mpr hu3
    · rw [hz]
      exact hw3

/-- HOL planarity.hl:2224 `not_collinear_is_properties_fully_surrounded`：
开弦版本（`0 < t < 1`），直接引用 `…_surrounded1`。 -/
theorem not_collinear_is_properties_fully_surrounded (hfan : FAN x V E)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ¬ Collinear3 x v ((1 - t) • u + t • w) :=
  not_collinear_is_properties_fully_surrounded1 hfan hvu huw hθ0 hθπ t
    (le_of_lt ht0) (le_of_lt ht1)

/-! ## 第十一块：小扰动扇区与 `xfan`/`yfan`（planarity.hl:2089/2107）

HOL `fan_run_in_small_is_not_meet_xfan`（2089）对 `E' = E` 用
`fan_run1_in_small_is_fan`：其中 `{v | ∃ e ∈ E, v ∈ aff_ge {x} e}` 即
`Fan.lean:154` 定义的 `xfan x V E`（定义相等）。
`fan_run_in_small_is_subset_yfan`（2107）由 `yfan = univ \ xfan`
（Fan.lean:158）与上述无交性直接得到。 -/

/-- HOL planarity.hl:2089 `fan_run_in_small_is_not_meet_xfan`：充分小的
扰动扇区与边锥之并 `xfan x V E` 无交（取 `E' = E` 的
`fan_run1_in_small_is_fan`）。 -/
theorem fan_run_in_small_is_not_meet_xfan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (hsigma : sigmaFan x V E u w = v) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ s : ℝ, 0 < s → s < h →
        affGt {x} {v, (1 - s) • u + s • w} ∩ xfan x V E = ∅ :=
  fan_run1_in_small_is_fan hfan hvu huw Set.Subset.rfl hθ0 hθπ hsigma

/-- HOL planarity.hl:2107 `fan_run_in_small_is_subset_yfan`：充分小的
扰动扇区含于 `yfan x V E = univ \ xfan x V E`。 -/
theorem fan_run_in_small_is_subset_yfan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (hsigma : sigmaFan x V E u w = v) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ s : ℝ, 0 < s → s < h →
        affGt {x} {v, (1 - s) • u + s • w} ⊆ yfan x V E := by
  obtain ⟨h, hp0, hp1, hp2⟩ :=
    fan_run_in_small_is_not_meet_xfan hfan hvu huw hθ0 hθπ hsigma
  refine ⟨h, hp0, hp1, fun s hs0 hsh z hz => ⟨Set.mem_univ z, fun hmem => ?_⟩⟩
  have hmem2 : z ∈ (∅ : Set V3) := by
    rw [← hp2 s hs0 hsh]
    exact ⟨hz, hmem⟩
  simp at hmem2

/-! ## 第十二块：邻居集方位角最小元、半空间边元素与混合积符号
（planarity.hl:2238/2273/2339） -/

/-- HOL planarity.hl:2238 `exists_inf_element_fix_fan`：邻居集多于一点时，
存在相对固定基准 `u1` 方位角最小的邻居（有限非空实数集取最小元，
`Set.exists_min_image`；有限性由 `remark_finite_fan1`）。 -/
theorem exists_inf_element_fix_fan (x v u1 : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hv : v ∈ V) (hcard : 1 < (setOfEdge v V E).ncard) :
    ∃ u ∈ setOfEdge v V E, ∀ w ∈ setOfEdge v V E, azim x v u1 u ≤ azim x v u1 w := by
  have hfin : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hfan.2.2.1.1
  have hne : (setOfEdge v V E).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty.mp h0, Set.ncard_empty] at hcard
    linarith
  obtain ⟨a, ha, hmin⟩ :=
    Set.exists_min_image (setOfEdge v V E) (fun z => azim x v u1 z) hfin hne
  exact ⟨a, ha, fun z hz => hmin z hz⟩

/-- HOL fan.hl:1802 `SUR_SIGMA_FAN`：σ 在邻居集上满射（有限集上的单射
自映射必满；单射性即 `mono_sigma_fan`）。 -/
private theorem sur_sigmaFan (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    ∃ w : V3, {v, w} ∈ E ∧ sigmaFan x V E v w = u := by
  have hu : u ∈ setOfEdge v V E := (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hfin : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hfan.2.2.1.1
  haveI : Finite ↥(setOfEdge v V E) := hfin
  have hinj : Function.Injective
      (fun p : { z // z ∈ setOfEdge v V E } =>
        (⟨sigmaFan x V E v p.1, sigma_fan_in_setOfEdge hfan p.2⟩ :
          { z // z ∈ setOfEdge v V E })) := by
    intro p q hpq
    have hval : sigmaFan x V E v p.1 = sigmaFan x V E v q.1 :=
      congrArg Subtype.val hpq
    exact Subtype.ext (mono_sigma_fan hfan p.2 q.2 hval)
  obtain ⟨p, hp⟩ :=
    Finite.surjective_of_injective hinj (⟨u, hu⟩ : { z // z ∈ setOfEdge v V E })
  have hval : sigmaFan x V E v p.1 = u := congrArg Subtype.val hp
  exact ⟨p.1, (properties_of_setOfEdge_fan x V E v p.1 hfan).mpr p.2, hval⟩

/-- HOL planarity.hl:2273 `exists_element_in_half_sapace_fan`：`fan80` 扇形下
存在边 `{v,u}` 使 `azim x v u1 u ∈ (0, π)`。若最小元方位角已达 (0, π) 取
最小元本身；`azim = 0` 时取 `σ`（`fan80` 给出 `azim x v u σ ∈ (0, π)`，由
`sum4_azim_fan` 换算基准）；`π ≤ azim` 时由 `SUR_SIGMA_FAN` 的前驱 `w`
（`azim x v w u ∈ (0, π)`）与 `sum5_azim_fan`、极小性矛盾。 -/
theorem exists_element_in_half_sapace_fan (x v u1 w1 : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) (hv : v ∈ V) (hcop : ¬ Coplanar ({x, v, u1, w1} : Set V3))
    (hcard : 1 < (setOfEdge v V E).ncard) (h80 : fan80 x V E) :
    ∃ u : V3, {v, u} ∈ E ∧ 0 < azim x v u1 u ∧ azim x v u1 u < Real.pi := by
  have hxn : x ≠ v := by
    intro he
    apply hcop
    have hset : ({x, v, u1, w1} : Set V3) = ({v, u1, w1} : Set V3) := by
      rw [← he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple v u1 w1
  have hvx : v ≠ x := hxn.symm
  have hncu1 : ¬ Collinear3 x v u1 := fun hcol =>
    hcop (coplanar_of_mem_line ((collinear3_iff_mem_affineSpan hxn).mp hcol))
  obtain ⟨umin, hminE, hmin⟩ :=
    exists_inf_element_fix_fan x v u1 V E hfan hv hcard
  have huE : {v, umin} ∈ E := (properties_of_setOfEdge_fan x V E v umin hfan).mpr hminE
  have hncu : ¬ Collinear3 x v umin := fan_not_collinear hfan huE
  obtain ⟨w, hwE, hwsig⟩ := sur_sigmaFan hfan huE
  have hncw : ¬ Collinear3 x v w := fan_not_collinear hfan hwE
  obtain ⟨h80w0, h80w1⟩ := h80 v w hwE
  rw [hwsig] at h80w0 h80w1
  rcases lt_or_ge (azim x v u1 umin) Real.pi with hlt | hge
  · rcases lt_or_eq_of_le (azim_nonneg x v u1 umin) with hpos | hzero
    · exact ⟨umin, huE, hpos, hlt⟩
    · -- azim x v u1 umin = 0：取 σ umin，`sum4_azim_fan` 换算基准角
      have hne : setOfEdge v V E ≠ {umin} := by
        intro he
        rw [he, Set.ncard_singleton] at hcard
        linarith
      obtain ⟨hsE, -, -⟩ := SIGMA_FAN hne hfan hminE
      have hsE' : {v, sigmaFan x V E v umin} ∈ E :=
        (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v umin) hfan).mpr hsE
      have h80u0 : 0 < azim x v umin (sigmaFan x V E v umin) := (h80 v umin huE).1
      have h80u1 : azim x v umin (sigmaFan x V E v umin) < Real.pi := (h80 v umin huE).2
      have hle : azim x v u1 umin ≤ azim x v u1 (sigmaFan x V E v umin) := hmin _ hsE
      have hsum := sum4_azim_fan hvx hncu1 hncu (fan_not_collinear hfan hsE') hle
      refine ⟨sigmaFan x V E v umin, hsE', ?_, ?_⟩
      · rw [hsum]; linarith
      · rw [hsum]; linarith
  · -- π ≤ azim x v u1 umin：前驱 w 的角落在 (0, π) 内，与极小性矛盾
    exfalso
    have hle : azim x v w umin ≤ azim x v u1 umin := h80w1.le.trans hge
    have hsum := sum5_azim_fan hvx hncu1 hncw hncu hle
    have hminw : azim x v u1 umin ≤ azim x v u1 w :=
      hmin w ((properties_of_setOfEdge_fan x V E v w hfan).mp hwE)
    linarith

/-- HOL planarity.hl:2339 `JBDNJJB`：`sin(azim 0 u v w)` 是混合积
`(u × v) ⬝ w`（HOL `cross` 即 `crossProduct`）的正常数倍。证明：取 `u`
方向的右手正交标架（`exists_on3_eq_smul`，`u = ‖u‖•e3`），`azim_frame_spec`
给出 `v`、`w` 的平面极坐标 `z_v = r1 e^{iψ}`、`z_w = r2 e^{i(ψ+θ)}`（
θ = azim 0 u v w）；由 `e3×e1 = e2`、`e3×e2 = -e1` 得
`u × v = ‖u‖ r1 (cos ψ e2 - sin ψ e1)`，与 `w` 点乘得 `‖u‖ r1 r2 sin θ`。 -/
theorem JBDNJJB {u v w : V3} (h1 : ¬ Collinear3 0 u v) (h2 : ¬ Collinear3 0 u w) :
    ∃ t : ℝ, 0 < t ∧ Real.sin (azim 0 u v w) =
      t * (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ) := by
  have hu0 : u ≠ 0 := by
    intro he
    exact h1 (by rw [he]; exact collinear3_of_eq rfl)
  obtain ⟨e1, e2, e3, hon, hue⟩ := exists_on3_eq_smul u hu0
  have hax : (u - 0 : V3) = dist u 0 • e3 := by
    rw [sub_zero, dist_eq_norm, sub_zero]
    exact hue
  obtain ⟨psi, r1, r2, hr1, hr2, hzv, hzw⟩ :=
    azim_frame_spec (v := 0) (w := u) (w1 := v) (w2 := w) h1 h2 hon hax hu0
  -- 平面坐标的实虚部
  have hv1 : (v : V3) ⬝ᵥ e1 = r1 * Real.cos psi := by
    have h := congrArg Complex.re hzv
    simp only [zOf, sub_zero, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_cos_re] at h
    exact h
  have hv2 : (v : V3) ⬝ᵥ e2 = r1 * Real.sin psi := by
    have h := congrArg Complex.im hzv
    simp only [zOf, sub_zero, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_sin_im] at h
    exact h
  have hw1 : (w : V3) ⬝ᵥ e1 = r2 * Real.cos (psi + azim 0 u v w) := by
    have h := congrArg Complex.re hzw
    simp only [zOf, sub_zero, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_cos_re] at h
    exact h
  have hw2 : (w : V3) ⬝ᵥ e2 = r2 * Real.sin (psi + azim 0 u v w) := by
    have h := congrArg Complex.im hzw
    simp only [zOf, sub_zero, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, mul_one, one_mul] at h
    rw [cexp_sin_im] at h
    exact h
  -- 标架的叉积值
  have hO := hon
  obtain ⟨h11, h22, h33, h12, h13, h23, hpos⟩ := hO
  have hc1 : crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ) = (e3 : Fin 3 → ℝ) :=
    on3_cross hon
  have hc2 : crossProduct (e3 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ) = (e2 : Fin 3 → ℝ) := by
    rw [← hc1, cross_cross_eq_smul_sub_smul, h11,
      dotProduct_comm (e2 : Fin 3 → ℝ) (e1 : Fin 3 → ℝ), h12]
    simp
  have hc3 : crossProduct (e3 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ) = -(e1 : Fin 3 → ℝ) := by
    rw [← hc1, cross_cross_eq_smul_sub_smul, h12, h22]
    simp
  -- 叉积线性性（Azim.lean 中同名引理为 private，此处按同法重证）
  have cr_add : ∀ p q s : Fin 3 → ℝ,
      crossProduct p (q + s) = crossProduct p q + crossProduct p s := by
    intro p q s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.add_apply] <;>
      ring
  have cr_smul : ∀ (c : ℝ) (p s : Fin 3 → ℝ),
      crossProduct p (c • s) = c • crossProduct p s := by
    intro c p s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply] <;>
      ring
  have cl_smul : ∀ (c : ℝ) (p s : Fin 3 → ℝ),
      crossProduct (c • p) s = c • crossProduct p s := by
    intro c p s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply] <;>
      ring
  -- 坐标在 Pi 侧的展开
  have hucoe : (u : Fin 3 → ℝ) = ‖u‖ • ((e3 : Fin 3 → ℝ)) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hue
    simpa only [WithLp.ofLp_smul] using h
  have vrep := rep_of_zOf hon hax hu0 v psi r1 hzv
  have hvcoe : (v : Fin 3 → ℝ)
      = (r1 * Real.cos psi) • ((e1 : Fin 3 → ℝ))
        + (r1 * Real.sin psi) • ((e2 : Fin 3 → ℝ))
        + ((v ⬝ᵥ e3) / dist u 0) • (‖u‖ • ((e3 : Fin 3 → ℝ))) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) vrep
    simpa only [sub_zero, WithLp.ofLp_add, WithLp.ofLp_smul, hucoe] using h
  -- 主计算：混合积 = ‖u‖ r1 r2 sin θ
  have htrig : ∀ X Y : ℝ, Real.cos Y * Real.sin X - Real.sin Y * Real.cos X
      = Real.sin (X - Y) := by
    intro X Y
    rw [Real.sin_sub]
    ring
  have htrig' : Real.cos psi * Real.sin (psi + azim 0 u v w)
      - Real.sin psi * Real.cos (psi + azim 0 u v w) = Real.sin (azim 0 u v w) := by
    rw [htrig, add_sub_cancel_left]
  have hX : (crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)) ⬝ᵥ (w : Fin 3 → ℝ)
      = ‖u‖ * r1 * r2 * Real.sin (azim 0 u v w) := by
    rw [hucoe, hvcoe, cl_smul, smul_dotProduct, cr_add, cr_add, cr_smul, cr_smul,
      cr_smul, cr_smul, hc2, hc3, cross_self (e3 : Fin 3 → ℝ), smul_zero, smul_zero,
      add_zero, add_dotProduct, smul_dotProduct, smul_dotProduct, neg_dotProduct,
      dotProduct_comm (e2 : Fin 3 → ℝ) (w : Fin 3 → ℝ),
      dotProduct_comm (e1 : Fin 3 → ℝ) (w : Fin 3 → ℝ), hw2, hw1]
    simp only [smul_eq_mul]
    linear_combination ‖u‖ * r1 * r2 * htrig'
  have huN : ‖u‖ ≠ 0 := (norm_pos_iff.mpr hu0).ne'
  have hM : ‖u‖ * r1 * r2 ≠ 0 := mul_ne_zero (mul_ne_zero huN hr1.ne') hr2.ne'
  refine ⟨(‖u‖ * r1 * r2)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  rw [hX, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-! ## 第十二块：azim 平移桥与 cross_dot 族（planarity.hl:2419–2493）

`azim x a b c = azim 0 (a-x) (b-x) (c-x)`（azim 定义中所有量都以
`w - v` 形式出现，平移不变）打通 `JBDNJJB`（原点形式）到一般顶点的
混合积刻画。本块由主 agent 手写（两个 GLM 模型均在此卡住：flash 探索
瘫痪，glm-5.3 超时未落码）。 -/

/-- 平移保持三点共线。 -/
private theorem collinear3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases ha : a = x
  · subst ha
    rw [sub_self]
    constructor <;> · intro _; exact collinear3_of_eq rfl
  · rw [collinear3_iff_smul ha, collinear3_iff_smul (sub_ne_zero.mpr ha)]
    simp only [sub_zero]

/-- `AzimSpec` 的平移不变性（所有量以差形式出现）。 -/
private theorem azimSpec_sub {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

/-- azim 平移桥：顶点移到原点（planarity.hl 全库反复使用的隐含事实）。 -/
theorem azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [collinear3_zero_sub (x := x) (a := a) (b := b),
    collinear3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext azimSpec_sub
  rw [hpred]

/-- HOL planarity.hl:2453 `IMP_NORM_FAN`：互异点的范数事实包。 -/
theorem IMP_NORM_FAN {va vb : V3} (h : va ≠ vb) :
    ‖va - vb‖ ≠ 0 ∧ 0 ≤ ‖va - vb‖ ∧ 0 < ‖va - vb‖ ∧ 0 ≤ ‖va - vb‖⁻¹ ∧
      0 < ‖va - vb‖⁻¹ ∧ ‖va - vb‖⁻¹ * ‖va - vb‖ = 1 := by
  have h0 : ‖va - vb‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hpos : 0 < ‖va - vb‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  exact ⟨h0, norm_nonneg _, hpos, inv_nonneg.mpr (norm_nonneg _),
    inv_pos.mpr hpos, inv_mul_cancel₀ h0⟩

/-- HOL planarity.hl:2470 `cross_dot_fully_surrounded_fan`：`azim ∈ (0,π)`
给出混合积严格为正（`JBDNJJB` 的 sin 桥 + sin 在开区间为正）。 -/
theorem cross_dot_fully_surrounded_fan {x v1 v u1 : V3}
    (h1 : ¬ Collinear3 x v1 u1) (h2 : ¬ Collinear3 x v1 v)
    (h0 : 0 < azim x v1 v u1) (hpi : azim x v1 v u1 < Real.pi) :
    0 < (crossProduct ((v1 - x : V3) : Fin 3 → ℝ) ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((u1 - x : V3) : Fin 3 → ℝ) := by
  rw [azim_sub_self] at h0 hpi
  have h1' : ¬ Collinear3 0 (v1 - x) (u1 - x) :=
    fun h => h1 (collinear3_zero_sub.mpr h)
  have h2' : ¬ Collinear3 0 (v1 - x) (v - x) :=
    fun h => h2 (collinear3_zero_sub.mpr h)
  obtain ⟨t, ht, hsin⟩ := JBDNJJB h2' h1'
  have hsp := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  rw [hsin] at hsp
  exact (mul_pos_iff_of_pos_left ht).mp hsp

/-- HOL planarity.hl:2493 `cross_dot_fully_surrounded_ge_fan`：闭区间版。 -/
theorem cross_dot_fully_surrounded_ge_fan {x v1 v u1 : V3}
    (h1 : ¬ Collinear3 x v1 u1) (h2 : ¬ Collinear3 x v1 v)
    (h0 : 0 ≤ azim x v1 v u1) (hpi : azim x v1 v u1 ≤ Real.pi) :
    0 ≤ (crossProduct ((v1 - x : V3) : Fin 3 → ℝ) ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((u1 - x : V3) : Fin 3 → ℝ) := by
  rw [azim_sub_self] at h0 hpi
  have h1' : ¬ Collinear3 0 (v1 - x) (u1 - x) :=
    fun h => h1 (collinear3_zero_sub.mpr h)
  have h2' : ¬ Collinear3 0 (v1 - x) (v - x) :=
    fun h => h2 (collinear3_zero_sub.mpr h)
  obtain ⟨t, ht, hsin⟩ := JBDNJJB h2' h1'
  have hsp := Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi
  rw [hsin] at hsp
  exact nonneg_of_mul_nonneg_right hsp ht

/-- HOL planarity.hl:2419 `independent_run_edges_fan`：内插边保持
`{v-x, u-x, p-x}` 线性无关。直证（不走 HOL 的 NOT_COPLANAR_0_4 引理）：
若相关，则或 `p-x ∈ span{v-x,u-x}`（四点共面，与
`continuous_coplanar_fan` 矛盾），或 `v-x,u-x` 相关（`fan_not_collinear`
矛盾）。 -/
theorem independent_run_edges_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {a : ℝ} (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (h80 : fan80 x V E) (hsigma : sigmaFan x V E u w = v)
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    LinearIndependent ℝ ![v - x, u - x, ((1 - a) • u + a • w) - x] := by
  have hθ := h80 u w huw
  rw [hsigma] at hθ
  have hcop := properties_fully_surrounded hfan hvu huw hθ.1 hθ.2
  have hcop2 := continuous_coplanar_fan x v u w hcop a (ne_of_gt ha0)
  have hvx : v ≠ x := by
    intro h
    have hc : Collinear3 x v u := by rw [h]; exact collinear3_of_eq rfl
    exact fan_not_collinear hfan hvu hc
  have hux : u ≠ x := by
    intro h
    have hc : Collinear3 x v u := by rw [← h]; exact collinear3_pair_left rfl
    exact fan_not_collinear hfan hvu hc
  by_contra hdep
  rw [Fintype.linearIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hg
  by_cases h2 : g 2 = 0
  · rw [h2, zero_smul, add_zero] at hg
    have h01 : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
      · exact False.elim (hi (by simpa using h2))
    have hcol_of : g 1 ≠ 0 → Collinear3 x v u := by
      intro h1
      refine (collinear3_iff_smul hvx).mpr ⟨-(g 0 * (g 1)⁻¹), ?_⟩
      have hg1 : g 1 • (u - x) = -(g 0 • (v - x)) := by
        linear_combination (norm := module) hg
      calc u - x = (g 1)⁻¹ • (g 1 • (u - x)) := (inv_smul_smul₀ h1 _).symm
        _ = (g 1)⁻¹ • (-(g 0 • (v - x))) := by rw [hg1]
        _ = -(g 0 * (g 1)⁻¹) • (v - x) := by
          rw [smul_neg, smul_smul, neg_smul, mul_comm]
    rcases h01 with h0 | h1
    · by_cases h1' : g 1 = 0
      · rw [h1', zero_smul, add_zero] at hg
        rcases smul_eq_zero.mp hg with hh | hh
        · exact absurd hh h0
        · exact absurd (sub_eq_zero.mp hh) hvx
      · exact absurd (hcol_of h1') (fan_not_collinear hfan hvu)
    · exact absurd (hcol_of h1) (fan_not_collinear hfan hvu)
  · have hp : ((1 - a) • u + a • w) - x =
        (-(g 0 * (g 2)⁻¹)) • (v - x) + (-(g 1 * (g 2)⁻¹)) • (u - x) := by
      have hz : g 2 • ((((1 - a) • u + a • w) - x) -
          ((-(g 0 * (g 2)⁻¹)) • (v - x) + (-(g 1 * (g 2)⁻¹)) • (u - x))) = 0 := by
        rw [smul_sub, smul_add, smul_smul, smul_smul]
        have e1 : g 2 * -(g 0 * (g 2)⁻¹) = -(g 0) := by field_simp
        have e2 : g 2 * -(g 1 * (g 2)⁻¹) = -(g 1) := by field_simp
        rw [e1, e2, neg_smul, neg_smul]
        linear_combination (norm := module) hg
      rcases smul_eq_zero.mp hz with h | h
      · exact absurd h h2
      · exact eq_of_sub_eq_zero h
    apply hcop2
    refine ⟨x, v, u, fun z hz => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · refine mem_affineSpan_of_combo (c1 := 1 - -(g 0 * (g 2)⁻¹) - -(g 1 * (g 2)⁻¹))
        (c2 := -(g 0 * (g 2)⁻¹)) (c3 := -(g 1 * (g 2)⁻¹)) (by ring) ?_
      calc (1 - a) • u + a • w = (((1 - a) • u + a • w) - x) + x := by module
        _ = (1 - -(g 0 * (g 2)⁻¹) - -(g 1 * (g 2)⁻¹)) • x +
            -(g 0 * (g 2)⁻¹) • v + -(g 1 * (g 2)⁻¹) • u := by rw [hp]; module

/-! ## aff_lt 的显式刻画与 fan 非退化四点性质（planarity.hl:2515–2527）

约定：HOL `DISJOINT {x,v} {w}` ↔ `x ∉ {w} ∧ v ∉ {w}`。 -/

/-- HOL planarity.hl:2515 `AFF_LT_2_1`：`aff_lt {x,v} {w}` 的显式组合刻画。
符号条件只落在 `w` 的系数上（`t3 < 0`）；`x = v`（并集去重为两点）单独处理。 -/
theorem AFF_LT_2_1 (hdis : Disjoint ({x, v} : Set V3) {w}) :
    affLt {x, v} {w} =
      {y | ∃ t1 t2 t3 : ℝ, t3 < 0 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • w} := by
  have hdis' := Set.disjoint_left.mp hdis
  have hxw : x ≠ w := by
    intro he
    exact hdis' (Set.mem_insert x {v}) (by rw [he]; simp)
  have hvw : v ≠ w := by
    intro he
    exact hdis' (Set.mem_insert_of_mem x (Set.mem_singleton v)) (by rw [he]; simp)
  ext y
  simp only [affLt, Affsign, Set.mem_setOf_eq]
  by_cases hxv : x = v
  · -- 退化情形 x = v：并集去重后为 {x, w}。
    constructor
    · rintro ⟨f, hfin, hsum, hneg, hone⟩
      have ht3 : f w < 0 := hneg w (by simp)
      have hTeq : hfin.toFinset = ({x, w} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, hxv, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hTeq, Finset.sum_insert (by simp [hxw]), Finset.sum_singleton] at hsum hone
      refine ⟨f x, 0, f w, ht3, by linarith, ?_⟩
      rw [hsum]
      module
    · rintro ⟨t1, t2, t3, ht3, hone, hy⟩
      have hfin : ({x, v} ∪ {w} : Set V3).Finite :=
        ((Set.finite_singleton v).insert x).union (Set.finite_singleton w)
      refine ⟨fun z => if z = x then t1 + t2 else t3, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hxv, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxw]), Finset.sum_singleton]
        show y = (if x = x then t1 + t2 else t3) • x +
          (if w = x then t1 + t2 else t3) • w
        rw [if_pos (rfl : x = x), if_neg (Ne.symm hxw), hy, ← hxv, add_smul]
      · intro z hz
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        show (if w = x then t1 + t2 else t3) < 0
        rw [if_neg (Ne.symm hxw)]
        exact ht3
      · have hTeq : hfin.toFinset = ({x, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, hxv, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxw]), Finset.sum_singleton]
        show (if x = x then t1 + t2 else t3) + (if w = x then t1 + t2 else t3) = 1
        rw [if_pos (rfl : x = x), if_neg (Ne.symm hxw)]
        linarith
  · -- 一般情形 x ≠ v。
    constructor
    · rintro ⟨f, hfin, hsum, hneg, hone⟩
      have ht3 : f w < 0 := hneg w (by simp)
      have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
        apply Finset.ext
        intro z
        simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]), Finset.sum_insert (by simp [hvw]),
        Finset.sum_singleton] at hsum hone
      exact ⟨f x, f v, f w, ht3, by linarith, by rw [hsum]; abel⟩
    · rintro ⟨t1, t2, t3, ht3, hone, hy⟩
      have hfin : ({x, v} ∪ {w} : Set V3).Finite :=
        ((Set.finite_singleton v).insert x).union (Set.finite_singleton w)
      refine ⟨fun z => if z = v then t2 else if z = w then t3 else t1, hfin, ?_, ?_, ?_⟩
      · have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
          Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
        show y = (if x = v then t2 else if x = w then t3 else t1) • x +
          ((if v = v then t2 else if v = w then t3 else t1) • v +
            (if w = v then t2 else if w = w then t3 else t1) • w)
        rw [if_neg hxv, if_neg hxw, if_pos (rfl : v = v),
          if_neg (Ne.symm hvw), if_pos (rfl : w = w), hy]
        abel
      · intro z hz
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        show (if w = v then t2 else if w = w then t3 else t1) < 0
        rw [if_neg (Ne.symm hvw), if_pos (rfl : w = w)]
        exact ht3
      · have hTeq : hfin.toFinset = ({x, v, w} : Finset V3) := by
          apply Finset.ext
          intro z
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hTeq, Finset.sum_insert (by simp [hxv, hxw]),
          Finset.sum_insert (by simp [hvw]), Finset.sum_singleton]
        show (if x = v then t2 else if x = w then t3 else t1) +
          ((if v = v then t2 else if v = w then t3 else t1) +
            (if w = v then t2 else if w = w then t3 else t1)) = 1
        rw [if_neg hxv, if_neg hxw, if_pos (rfl : v = v),
          if_neg (Ne.symm hvw), if_pos (rfl : w = w)]
        linarith

/-- HOL planarity.hl:2527 `properties_of_collinear4_points_fan`：
`x,v,u` 不共线且 `v1 ∈ aff_gt {x} {v,u}` 时，`x,v1,v` 亦不共线。 -/
theorem properties_of_collinear4_points_fan {v1 : V3} (hnc : ¬ Collinear3 x v u)
    (hv1 : v1 ∈ affGt {x} {v, u}) : ¬ Collinear3 x v1 v := by
  have hvx : x ≠ v := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({v, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hxu : x ≠ u := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({u, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h' | h'
    · exact hvx h'
    · exact hxu h'
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hv1
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hv1c⟩ := hv1
  intro hc
  have ht3n : t3 ≠ 0 := ne_of_gt ht3
  have hset : ({x, v1, v} : Set V3) = ({x, v, v1} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hc' : Collinear ℝ ({x, v, v1} : Set V3) := by
    rw [← hset]
    exact hc
  obtain ⟨c, hcsmul⟩ := (collinear3_iff_smul (w := v) (v := x) hvx.symm).mp hc'
  have step1 : v1 - x = t1 • x + t2 • v + t3 • u - (t1 + t2 + t3) • x := by
    rw [hv1c, hone, one_smul]
  have hv1x : v1 - x = t2 • (v - x) + t3 • (u - x) := by
    rw [step1]
    module
  have hcc : c • (v - x) = t2 • (v - x) + t3 • (u - x) := by
    rw [← hcsmul]
    exact hv1x
  have hkey : t3 • (u - x) = (c - t2) • (v - x) := by
    calc t3 • (u - x) = c • (v - x) - t2 • (v - x) := by rw [hcc]; abel
      _ = (c - t2) • (v - x) := by rw [sub_smul]
  have hux : u - x = ((c - t2) / t3) • (v - x) := by
    rw [div_eq_inv_mul, ← smul_smul, ← hkey, inv_smul_smul₀ ht3n]
  exact hnc
    ((collinear3_iff_smul (w := v) (v := x) hvx.symm).mpr ⟨(c - t2) / t3, hux⟩)

/-! ## 第十五块：cross_dot_fully_surrounded1 族（planarity.hl:2561/2677） -/

/-- 纯 `(Fin 3 → ℝ)` 侧的混合积代数引理：`X = t₂•W + t₃•Q`
（`t₂, t₃ > 0`）且 `det[X, W, Z] > 0` 时 `det[X, Z, Q] > 0`
（`cr_add_l`/`cr_smul_l` 为 `crossProduct` 左线性，仿 `JBDNJJB`
内的同名局部引理）。 -/
private theorem cross_dot_combo_pos {X W Z Q : Fin 3 → ℝ} {t2 t3 : ℝ}
    (ht2 : 0 < t2) (ht3 : 0 < t3)
    (hX : X = t2 • W + t3 • Q) (hA : 0 < (crossProduct X W) ⬝ᵥ Z) :
    0 < (crossProduct X Z) ⬝ᵥ Q := by
  have cr_add_l : ∀ p q s : Fin 3 → ℝ,
      crossProduct (p + q) s = crossProduct p s + crossProduct q s := by
    intro p q s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.add_apply] <;>
      ring
  have cr_smul_l : ∀ (c : ℝ) (p s : Fin 3 → ℝ),
      crossProduct (c • p) s = c • crossProduct p s := by
    intro c p s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply] <;>
      ring
  have hexp : (crossProduct X Z) ⬝ᵥ Q = t2 * ((crossProduct W Z) ⬝ᵥ Q) := by
    rw [hX, cr_add_l, cr_smul_l, cr_smul_l, add_dotProduct, smul_dotProduct,
      smul_dotProduct, dotProduct_comm (crossProduct Q Z) Q, dot_self_cross, smul_zero,
      add_zero, smul_eq_mul]
  have hA' : (crossProduct X W) ⬝ᵥ Z = t3 * ((crossProduct Q W) ⬝ᵥ Z) := by
    rw [hX, cr_add_l, cr_smul_l, cr_smul_l, add_dotProduct, cross_self W, smul_zero,
      zero_dotProduct, zero_add, smul_dotProduct, smul_eq_mul]
  have hperm : (crossProduct W Z) ⬝ᵥ Q = (crossProduct Q W) ⬝ᵥ Z := by
    calc (crossProduct W Z) ⬝ᵥ Q = Q ⬝ᵥ crossProduct W Z := dotProduct_comm _ _
      _ = Z ⬝ᵥ crossProduct Q W := (triple_product_permutation Z Q W).symm
      _ = (crossProduct Q W) ⬝ᵥ Z := dotProduct_comm _ _
  have hQW : 0 < (crossProduct Q W) ⬝ᵥ Z :=
    (mul_pos_iff_of_pos_left ht3).mp (by rwa [hA'] at hA)
  rw [hexp, hperm]
  exact mul_pos ht2 hQW

/-- HOL planarity.hl:2561 `cross_dot_fully_surrounded1_fan`：
`aff_gt` 平面侧点的混合积严格为正。重构证明（不走 HOL 的
`sum4_azim_fan`/`AZIM_EQ_PI_ALT` 路线）：把已有的
`cross_dot_fully_surrounded_fan` 直接用于假设 `azim x v1 v u1` 得
`det[v1-x, v-x, u1-x] > 0`，再由 `aff_gt_1_2` 展开仿射组合
`v1 - x = t2•(v-x) + t3•(p-x)`（`t2, t3 > 0`）与混合积的
多重线性（`cross_dot_combo_pos`）直接换算。 -/
theorem cross_dot_fully_surrounded1_fan {v1 u1 : V3} {a : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (h80 : fan80 x V E) (hnc : ¬ Collinear3 x v1 u1)
    (hv1 : v1 ∈ affGt {x} {v, (1 - a) • u + a • w})
    (h0 : 0 < azim x v1 v u1) (hpi : azim x v1 v u1 < Real.pi) :
    0 < (crossProduct ((v1 - x : V3) : Fin 3 → ℝ) ((u1 - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((((1 - a) • u + a • w - x : V3) : Fin 3 → ℝ)) := by
  obtain ⟨hθ0, hθπ⟩ := h80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hncvp : ¬ Collinear3 x v ((1 - a) • u + a • w) :=
    not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ a ha0 ha1
  have hv1v : ¬ Collinear3 x v1 v :=
    properties_of_collinear4_points_fan hncvp hv1
  have hA := cross_dot_fully_surrounded_fan hnc hv1v h0 hpi
  have hxv : x ≠ v := fun he => hncvp (by rw [he]; exact collinear3_of_eq rfl)
  have hxp : x ≠ (1 - a) • u + a • w :=
    fun he => hncvp (by rw [he]; exact collinear3_pair_left rfl)
  have hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w} := by
    rw [Set.disjoint_singleton_left]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h' | h'
    · exact hxv h'
    · exact hxp h'
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hv1
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hv1c⟩ := hv1
  have step1 : v1 - x = t1 • x + t2 • v + t3 • ((1 - a) • u + a • w)
      - (t1 + t2 + t3) • x := by
    rw [hv1c, hone, one_smul]
  have hvsub : v1 - x
      = t2 • (v - x : V3) + t3 • (((1 - a) • u + a • w) - x : V3) := by
    rw [step1]
    module
  have hv1coe : ((v1 - x : V3) : Fin 3 → ℝ)
      = t2 • (((v - x : V3) : Fin 3 → ℝ))
        + t3 • ((((1 - a) • u + a • w - x : V3) : Fin 3 → ℝ)) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hvsub
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  exact cross_dot_combo_pos ht2 ht3 hv1coe hA

/-- HOL planarity.hl:2677 `exists_cross_dot_fully_surrounded1_fan`：
第 1 款的正性沿 `p ↦ (1-h)•p + h•u` 延拓一段正长度。展开
`(1-h)•p + h•u - x = (p - x) - (h*a)•(w-u)` 后混合积是
`A - h*a*B`（`A > 0` 为第 1 款）；`B ≤ 0` 时任意 `h > 0` 均可，
`B > 0` 时取 `t` 为 `A/(a*B)/2` 与 `1/2` 的较小者。 -/
theorem exists_cross_dot_fully_surrounded1_fan {v1 u1 : V3} {a : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (h80 : fan80 x V E) (hnc : ¬ Collinear3 x v1 u1)
    (hv1 : v1 ∈ affGt {x} {v, (1 - a) • u + a • w})
    (h0 : 0 < azim x v1 v u1) (hpi : azim x v1 v u1 < Real.pi) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ h : ℝ, 0 < h → h < t →
      0 < (crossProduct ((v1 - x : V3) : Fin 3 → ℝ) ((u1 - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
        ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3) : Fin 3 → ℝ)) := by
  have hA := cross_dot_fully_surrounded1_fan hfan hvu huw hsigma ha0 ha1 h80 hnc hv1 h0 hpi
  set C := (crossProduct ((v1 - x : V3) : Fin 3 → ℝ) ((u1 - x : V3) : Fin 3 → ℝ)) with hCdef
  set D := C ⬝ᵥ ((((1 - a) • u + a • w) - x : V3) : Fin 3 → ℝ) with hDdef
  set B := C ⬝ᵥ (((w - u : V3) : Fin 3 → ℝ)) with hBdef
  have hvid : ∀ h : ℝ, ((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3)
      = (((1 - a) • u + a • w) - x : V3) - (h * a) • (w - u : V3) := by
    intro h
    module
  have hcoe : ∀ h : ℝ,
      ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3)) : Fin 3 → ℝ)
      = ((((1 - a) • u + a • w) - x : V3) : Fin 3 → ℝ)
        - (h * a) • (((w - u : V3) : Fin 3 → ℝ)) := by
    intro h
    have hc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) (hvid h)
    simpa only [WithLp.ofLp_sub, WithLp.ofLp_smul] using hc
  have hkey : ∀ h : ℝ,
      C ⬝ᵥ ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3) : Fin 3 → ℝ))
        = D - h * a * B := by
    intro h
    rw [hcoe h, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rcases le_or_gt B 0 with hB | hB
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro h hh0 _
    rw [hkey h]
    have hha : 0 ≤ h * a := mul_nonneg (le_of_lt hh0) (le_of_lt ha0)
    have hnn : h * a * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hha hB
    linarith
  · have hBpos : 0 < a * B := mul_pos ha0 hB
    have hDpos : 0 < D / (a * B) := div_pos hA hBpos
    refine ⟨min (D / (a * B) / 2) (1 / 2), lt_min (half_pos hDpos) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro h hh0 hht
    rw [hkey h]
    have hlt : h < D / (a * B) :=
      lt_of_lt_of_le hht
        (le_trans (min_le_left _ _) (le_of_lt (half_lt_self hDpos)))
    have hmul : h * (a * B) < D := (lt_div_iff₀ hBpos).mp hlt
    have hs : h * a * B = h * (a * B) := by ring
    rw [hs]
    linarith

/-! ## 第十六块：cross_dot_fully_surrounded2 族与共面（planarity.hl:2742/2794/2864/2911） -/

/-- 纯 `(Fin 3 → ℝ)` 侧的混合积代数引理（`cross_dot_combo_pos` 的镜像）：
`X = t₂•W + t₃•Q`（`t₃ > 0`）且 `det[X, W, Z] > 0` 时 `det[Q, W, Z] > 0`
（`t₂` 项经 `cross_self` 消失）。 -/
private theorem cross_dot_combo_pos2 {X W Z Q : Fin 3 → ℝ} {t2 t3 : ℝ}
    (ht3 : 0 < t3) (hX : X = t2 • W + t3 • Q)
    (hA : 0 < (crossProduct X W) ⬝ᵥ Z) :
    0 < (crossProduct Q W) ⬝ᵥ Z := by
  have cr_add_l : ∀ p q s : Fin 3 → ℝ,
      crossProduct (p + q) s = crossProduct p s + crossProduct q s := by
    intro p q s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.add_apply] <;>
      ring
  have cr_smul_l : ∀ (c : ℝ) (p s : Fin 3 → ℝ),
      crossProduct (c • p) s = c • crossProduct p s := by
    intro c p s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply] <;>
      ring
  have hA' : (crossProduct X W) ⬝ᵥ Z = t3 * ((crossProduct Q W) ⬝ᵥ Z) := by
    rw [hX, cr_add_l, cr_smul_l, cr_smul_l, add_dotProduct, cross_self W, smul_zero,
      zero_dotProduct, zero_add, smul_dotProduct, smul_eq_mul]
  exact (mul_pos_iff_of_pos_left ht3).mp (by rwa [hA'] at hA)

/-- HOL planarity.hl:2742 `cross_dot_fully_surrounded2_fan`：
`cross_dot_fully_surrounded1_fan` 的镜像（混合积第 1/第 3 槽位互换）。
路线与第 1 款相同：`cross_dot_fully_surrounded_fan` 给
`det[v1-x, v-x, u1-x] > 0`，`aff_gt_1_2` 展开
`v1 - x = t2•(v-x) + t3•(p-x)`（`p = (1-a)•u + a•w`），再由多重线性
（`cross_dot_combo_pos2`）换算成 `det[p-x, v-x, u1-x] > 0`。 -/
theorem cross_dot_fully_surrounded2_fan {v1 u1 : V3} {a : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (h80 : fan80 x V E) (hnc : ¬ Collinear3 x v1 u1)
    (hv1 : v1 ∈ affGt {x} {v, (1 - a) • u + a • w})
    (h0 : 0 < azim x v1 v u1) (hpi : azim x v1 v u1 < Real.pi) :
    0 < (crossProduct ((((1 - a) • u + a • w - x : V3) : Fin 3 → ℝ))
        ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (((u1 - x : V3) : Fin 3 → ℝ)) := by
  obtain ⟨hθ0, hθπ⟩ := h80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hncvp : ¬ Collinear3 x v ((1 - a) • u + a • w) :=
    not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ a ha0 ha1
  have hv1v : ¬ Collinear3 x v1 v :=
    properties_of_collinear4_points_fan hncvp hv1
  have hA := cross_dot_fully_surrounded_fan hnc hv1v h0 hpi
  have hxv : x ≠ v := fun he => hncvp (by rw [he]; exact collinear3_of_eq rfl)
  have hxp : x ≠ (1 - a) • u + a • w :=
    fun he => hncvp (by rw [he]; exact collinear3_pair_left rfl)
  have hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w} := by
    rw [Set.disjoint_singleton_left]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h' | h'
    · exact hxv h'
    · exact hxp h'
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hv1
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hv1c⟩ := hv1
  have step1 : v1 - x = t1 • x + t2 • v + t3 • ((1 - a) • u + a • w)
      - (t1 + t2 + t3) • x := by
    rw [hv1c, hone, one_smul]
  have hvsub : v1 - x
      = t2 • (v - x : V3) + t3 • (((1 - a) • u + a • w) - x : V3) := by
    rw [step1]
    module
  have hv1coe : ((v1 - x : V3) : Fin 3 → ℝ)
      = t2 • (((v - x : V3) : Fin 3 → ℝ))
        + t3 • ((((1 - a) • u + a • w - x : V3) : Fin 3 → ℝ)) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hvsub
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  exact cross_dot_combo_pos2 ht3 hv1coe hA

/-- HOL planarity.hl:2794 `exists_cross_dot_fully_surrounded2_fan`：
第 2 款的正性沿 `p ↦ (1-h)•p + h•u` 延拓一段正长度，与
`exists_cross_dot_fully_surrounded1_fan` 同构：展开
`(1-h)•p + h•u - x = (p - x) - (h*a)•(w-u)` 后混合积是 `D - h*a*B`
（`D > 0` 为第 2 款）；`B ≤ 0` 时任意 `h > 0` 均可，`B > 0` 时取
`t` 为 `D/(a*B)/2` 与 `1/2` 的较小者。 -/
theorem exists_cross_dot_fully_surrounded2_fan {v1 u1 : V3} {a : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (h80 : fan80 x V E) (hnc : ¬ Collinear3 x v1 u1)
    (hv1 : v1 ∈ affGt {x} {v, (1 - a) • u + a • w})
    (h0 : 0 < azim x v1 v u1) (hpi : azim x v1 v u1 < Real.pi) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ h : ℝ, 0 < h → h < t →
      0 < (crossProduct ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3) : Fin 3 → ℝ))
          ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
        (((u1 - x : V3) : Fin 3 → ℝ)) := by
  have hA := cross_dot_fully_surrounded2_fan hfan hvu huw hsigma ha0 ha1 h80 hnc hv1 h0 hpi
  set D := (crossProduct ((((1 - a) • u + a • w - x : V3) : Fin 3 → ℝ))
      ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ (((u1 - x : V3) : Fin 3 → ℝ)) with hDdef
  set B := (crossProduct (((w - u : V3) : Fin 3 → ℝ))
      ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ (((u1 - x : V3) : Fin 3 → ℝ)) with hBdef
  have hvid : ∀ h : ℝ, ((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3)
      = (((1 - a) • u + a • w) - x : V3) - (h * a) • (w - u : V3) := by
    intro h
    module
  have hcoe : ∀ h : ℝ,
      ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3)) : Fin 3 → ℝ)
      = ((((1 - a) • u + a • w) - x : V3) : Fin 3 → ℝ)
        - (h * a) • (((w - u : V3) : Fin 3 → ℝ)) := by
    intro h
    have hc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) (hvid h)
    simpa only [WithLp.ofLp_sub, WithLp.ofLp_smul] using hc
  have cr_sub_l : ∀ p q s : Fin 3 → ℝ,
      crossProduct (p - q) s = crossProduct p s - crossProduct q s := by
    intro p q s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.sub_apply] <;>
      ring
  have cr_smul_l : ∀ (c : ℝ) (p s : Fin 3 → ℝ),
      crossProduct (c • p) s = c • crossProduct p s := by
    intro c p s
    funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply] <;>
      ring
  have hkey : ∀ h : ℝ,
      (crossProduct ((((1 - h) • ((1 - a) • u + a • w) + h • u - x : V3) : Fin 3 → ℝ))
          ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ (((u1 - x : V3) : Fin 3 → ℝ))
      = D - h * a * B := by
    intro h
    rw [hcoe h, cr_sub_l, cr_smul_l, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rcases le_or_gt B 0 with hB | hB
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro h hh0 _
    rw [hkey h]
    have hha : 0 ≤ h * a := mul_nonneg (le_of_lt hh0) (le_of_lt ha0)
    have hnn : h * a * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hha hB
    linarith
  · have hBpos : 0 < a * B := mul_pos ha0 hB
    have hDpos : 0 < D / (a * B) := div_pos hA hBpos
    refine ⟨min (D / (a * B) / 2) (1 / 2), lt_min (half_pos hDpos) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro h hh0 hht
    rw [hkey h]
    have hlt : h < D / (a * B) :=
      lt_of_lt_of_le hht
        (le_trans (min_le_left _ _) (le_of_lt (half_lt_self hDpos)))
    have hmul : h * (a * B) < D := (lt_div_iff₀ hBpos).mp hlt
    have hs : h * a * B = h * (a * B) := by ring
    rw [hs]
    linarith

/-- HOL planarity.hl:2864 `properties_of_coplanar`：`aff_gt {x} {v,u}` 中的
点 `v1` 与 `{x, v, u}` 共面（直接版：`aff_gt_1_2` 给出 `v1` 的仿射组合，
`affineCombination_mem_affineSpan` 放进 `affineSpan {x,v,u}`，四点皆入）。 -/
theorem properties_of_coplanar {v1 : V3} (hnc : ¬ Collinear3 x v u)
    (hv1 : v1 ∈ affGt {x} {v, u}) :
    Coplanar ({x, v1, v, u} : Set V3) := by
  have hvx : x ≠ v := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({v, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hxu : x ≠ u := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({u, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h' | h'
    · exact hvx h'
    · exact hxu h'
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hv1
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hv1c⟩ := hv1
  have hw : ∑ i, (![t1, t2, t3] : Fin 3 → ℝ) i = 1 := by
    simp [Fin.sum_univ_three, hone]
  have hrange : (Set.range (![x, v, u] : Fin 3 → V3)) = ({x, v, u} : Set V3) := by
    ext q
    simp
    tauto
  have hv1span : v1 ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) := by
    have hac := affineCombination_mem_affineSpan hw (![x, v, u] : Fin 3 → V3)
    rw [hrange] at hac
    have hv1ac : v1 = (Finset.univ : Finset (Fin 3)).affineCombination ℝ
        (![x, v, u] : Fin 3 → V3) (![t1, t2, t3] : Fin 3 → ℝ) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
      simp [Fin.sum_univ_three, hv1c]
    rw [← hv1ac] at hac
    exact SetLike.mem_coe.mpr hac
  refine ⟨x, v, u, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  · exact hv1span
  · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))

/-- HOL planarity.hl:2911 `coplanar_is_cross_fan`：`aff_gt {x} {v,u}` 中的点
满足 `(v-x) ×₃ (u-x)` 与 `v1-x` 垂直（混合积为零）。直接由 `aff_gt_1_2`
的仿射展开 `v1 - x = t2•(v-x) + t3•(u-x)` 加 `dot_self_cross`/
`dot_cross_self`（叉积与两个因子正交）得出。 -/
theorem coplanar_is_cross_fan {v1 : V3} (hnc : ¬ Collinear3 x v u)
    (hv1 : v1 ∈ affGt {x} {v, u}) :
    (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (((v1 - x : V3) : Fin 3 → ℝ)) = 0 := by
  have hvx : x ≠ v := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({v, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hxu : x ≠ u := by
    intro he
    apply hnc
    show Collinear ℝ ({x, v, u} : Set V3)
    rw [he]
    have hset : ({u, v, u} : Set V3) = {v, u} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v u
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h' | h'
    · exact hvx h'
    · exact hxu h'
  rw [aff_gt_1_2 hdis, Set.mem_setOf_eq] at hv1
  obtain ⟨t1, t2, t3, ht2, ht3, hone, hv1c⟩ := hv1
  have step1 : v1 - x = t1 • x + t2 • v + t3 • u - (t1 + t2 + t3) • x := by
    rw [hv1c, hone, one_smul]
  have hvsub : v1 - x = t2 • (v - x : V3) + t3 • (u - x : V3) := by
    rw [step1]
    module
  have hv1coe : ((v1 - x : V3) : Fin 3 → ℝ)
      = t2 • (((v - x : V3) : Fin 3 → ℝ))
        + t3 • (((u - x : V3) : Fin 3 → ℝ)) := by
    have h := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hvsub
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  have h1 : (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (((v - x : V3) : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm, dot_self_cross]
  have h2 : (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (((u - x : V3) : Fin 3 → ℝ)) = 0 := by
    rw [dotProduct_comm, dot_cross_self]
  simp only [hv1coe, dotProduct_add, dotProduct_smul, smul_eq_mul, h1, h2]
  ring
