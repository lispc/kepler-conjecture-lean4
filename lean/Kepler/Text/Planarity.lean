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
