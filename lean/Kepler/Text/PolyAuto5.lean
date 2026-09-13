/-
Port of the HOL Light Flyspeck polyhedron theory (Packing chapter), slice 5:
skeleton pass of `scripts/polyhedron.hl` :745-:1314 (batch 5 of 8+).

Source: `lean/scripts/polyhedron.hl` (persistent copy of Flyspeck book
formalization `text_formalization/packing/polyhedron.hl`, John Harrison +
Hoang Le Truong, 2010-2011).

Coverage (batch 5, theorems whose `let ... = prove` starts in :745-:1314,
exactly 10):
- `CONTINUOUS_ON_LIFT_DOT` (:745)
- `AFFINITE_HULL_BALL_EQ_UNIV` (:752)
- `INTERIOR_AFFINIE_HUL_EQ_UNIV` (:815)
- `AFF_DIM_INTERIOR_EQ_3` (:828)
- `INTERIOR_IMP_RELATIVE_INTERIOR` (:840)
- `IN_RELATIVE_INTERIOR1` (:858)
- `FCHANGED_OPEN` (:891-:1127, batch centerpiece: openness of the
  "fchanged" region away from the origin)
- `FCHANGED_ONE_TO_ONE` (:1132)
- `CARD_EXISTS_2` (:1184)
- `EXISTS_EDGE_POLYTOPE` (:1278)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs are `by sorry`, to be filled by the auto_loop harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  `t % v` ↔ `t • v`; `vec 0` ↔ `(0 : V3)`; `a dot x` ↔ `a ⬝ᵥ x`.
- HOL `relative_interior s` ↔ `intrinsicInterior ℝ s` (Mathlib
  Analysis/Convex/Intrinsic.lean:61; no `relative_interior` in Mathlib
  v4.32.2). HOL `interior` ↔ Mathlib `interior`.
- HOL `affine hull s` ↔ `(affineSpan ℝ s : Set V3)` (carrier coercion, since
  HOL compares hulls as sets, e.g. `affine hull p = (:real^3)`).
- HOL `bounded s` ↔ `Bornology.IsBounded s`; CONTINUOUS_ON ↔ Mathlib
  `ContinuousOn`.
- HOL `lift o (λy. a dot y)` (real-valued dot composed with the embedding
  `ℝ → ℝ^1`) is encoded as the plain ℝ-valued `fun y : V3 => a ⬝ᵥ y`:
  `lift` is a linear homeomorphism onto its image, so openness/continuity
  content is unchanged.
- DEFS: the canonical ports of `fchanged` (polyhedron.hl:512),
  `polyhedron` (HOL polytope.ml:4385 / flyspeck Def 4.8), `face_of`,
  `facet_of` (Def 4.7), `aff_dim` and (for the `edges` of
  EXISTS_EDGE_POLYTOPE) `edge_of` (`e face_of s ∧ aff_dim e = 1`,
  polytope.ml:2847) / `edges s = {{v,w} | segment[v,w] edge_of s}`
  (flyspeck_multivariate.ml:6887) live in / will live in the concurrent
  batch Kepler/Text/PolyAuto4.lean (`fchanged`, `polyhedron`, `FaceOf`,
  `FacetOf`, `affDim`). Since PolyAuto4 must NOT be imported here
  (concurrent lane; batch plan forbids PolyAuto imports), the statements
  below reference faithful `private` copies suffixed `_p5`
  (`fchanged`, `polyhedron`, `FaceOf`, `FacetOf`, `affDim`,
  `edgeOf`, `edges`), byte-for-byte the PolyAuto4 bodies
  (`edgeOf`/`edges` are new ports, quoted verbatim from
  polytope.ml:2847 / flyspeck_multivariate.ml:6887; `edges` uses the CLOSED
  segment `segment[v,w]`, unlike the open-segment `face_of` quantifier).
  MERGE PLAN: at assembly, delete the `_p5` copies and re-point every
  occurrence to PolyAuto4's `fchanged`/`polyhedron`/`FaceOf`/`FacetOf`/
  `affDim` (identical bodies); `edgeOf`/`edges` should move next to
  them (or be inlined at call sites) — propose `edgeOf`/`edges` defs in the
  PolyAuto4 lane.
- Imports: `PlanarityAuto16` + `ConformingDefs` per batch plan (the cited
  ConformingAuto-chain rides in transitively through PlanarityAuto16);
  `Mathlib` is imported explicitly for `intrinsicInterior`, `affineSpan`,
  `Metric.ball`, `Set.ncard`. NO other PolyAuto files are imported
  (batches 1-4 are concurrent lanes).

Difficulty scale (for the fill-in pass): zuzhuang = assembly of already
ported lemmas; liangou = coefficient/rewriting bookkeeping; fenxi =
geometric content.
-/

import Kepler.Text.Polytope
import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Classical

/-! ## polyhedron.hl :745-:890（连续性、仿射包与内部） -/

/-- HOL polyhedron.hl :745-:747 `CONTINUOUS_ON_LIFT_DOT`

HOL 原文：
```
!s a. (lift o (\y. a dot y)) continuous_on s
```

编码说明：HOL `lift : real -> real^1` 为线性同胚，去掉后等价于 ℝ 值函数
`fun y => a ⬝ᵥ y` 的连续性（见文件头编码说明）；`!s a` 保持原序。

证明思路：点态连续（`dotProduct` 关于第二个变元连续）+ `continuousOn_iff`。

候选已有引理：
- `ContinuousOn`、`continuousOn_iff`（Mathlib Topology/ContinuousOn.lean）
- `Matrix.dotProduct` 连续性 / `(innerSL ℝ a).continuous`（EuclideanSpace 内积） -/
theorem CONTINUOUS_ON_LIFT_DOT (s : Set V3) (a : V3) :
    ContinuousOn (fun y : V3 => a ⬝ᵥ y) s := by
  exact (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _)).continuousOn

/-- HOL polyhedron.hl :752-:812 `AFFINITE_HULL_BALL_EQ_UNIV`

HOL 原文：
```
!x e. &0< e ==> affine hull ball (x,e) =(:real^3)
```

编码说明：`(:real^3)` ↦ `(univ : Set V3)`；`affine hull` 的等式按集合相等
编码为 `(affineSpan ℝ (Metric.ball x e) : Set V3) = univ`。

证明思路：HOL 用两点 delta 扰动显式写出凸组合系数（`func1`）；Lean 可改走
泛化路线：取 `v = x + c • (x' - x)`（小 `c > 0`）入球，则 `x' ∈ affineSpan {x, v} ⊆
affineSpan (ball x e)`，再由 `x'` 任意得 `= univ`。

候选已有引理：
- `affineSpan_mono`、`subset_affineSpan`、`affineSpan_insert`、`mem_ball`
- `Submodule.eq_top_of_finrank_eq` / `eq_top_iff`（经 `finrank` 判满）
- 缺口：Mathlib 似无 `affineSpan_ball_eq_univ` 一等引理 -/
theorem AFFINITE_HULL_BALL_EQ_UNIV (x : V3) (e : ℝ) (he : 0 < e) :
    (affineSpan ℝ (Metric.ball x e) : Set V3) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y = x
  · subst hy
    exact subset_affineSpan ℝ _ (Metric.mem_ball_self he)
  · have hyn : 0 < ‖(y - x : V3)‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    set c := e / 2 / ‖y - x‖ with hc
    have hc0 : 0 < c := by rw [hc]; exact div_pos (div_pos he zero_lt_two) hyn
    have hz : x + c • (y - x) ∈ Metric.ball x e := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc0, hc]
      field_simp
      linarith
    have hcne : c ≠ 0 := ne_of_gt hc0
    have key : AffineMap.lineMap x (x + c • (y - x)) c⁻¹ = y := by
      simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hcne, one_smul, sub_add_cancel]
    rw [← key]
    exact AffineMap.lineMap_mem _ (subset_affineSpan ℝ _ (Metric.mem_ball_self he))
      (subset_affineSpan ℝ _ hz)

/-- HOL polyhedron.hl :815-:824 `INTERIOR_AFFINIE_HUL_EQ_UNIV`

HOL 原文：
```
!x p:(real^3->bool). x IN interior p ==> affine hull p= (:real^3)
```

编码说明：结论同上按集合相等编码。

证明思路：`interior p` 非空 → 存在球 `ball (x, e) ⊆ p` →
`affineSpan (ball x e) = univ ⊇ affineSpan p` 反向单调得 `affineSpan p = univ`。

候选已有引理：
- `Metric.isOpen_iff`、`interior` 的开球刻画
- 本批 `AFFINITE_HULL_BALL_EQ_UNIV`、`affineSpan_mono` -/
theorem INTERIOR_AFFINIE_HUL_EQ_UNIV (x : V3) (p : Set V3) (hx : x ∈ interior p) :
    (affineSpan ℝ p : Set V3) = Set.univ := by
  obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have h1 := AFFINITE_HULL_BALL_EQ_UNIV x e he
  have h2 : (affineSpan ℝ (Metric.ball x e) : Set V3) ⊆ (affineSpan ℝ p : Set V3) :=
    affineSpan_mono ℝ (hsub.trans interior_subset)
  rw [h1] at h2
  exact Set.eq_univ_of_univ_subset h2

/-- HOL polyhedron.hl :828-:836 `AFF_DIM_INTERIOR_EQ_3`

HOL 原文：
```
!x p:(real^3->bool). x IN interior p ==> aff_dim p= &3
```

编码说明：HOL `aff_dim` ↦ 本批私有 `affDim`（= PolyAuto4 的 `affDim`；
∅ ↦ -1，否则 `Module.finrank ℝ (vectorSpan ℝ s)`）。

证明思路：`INTERIOR_AFFINIE_HUL_EQ_UNIV` 得 `affineSpan p = univ`；
`vectorSpan ℝ univ = ⊤`，`finrank ℝ (⊤ : Submodule ℝ V3) = 3`
（`EuclideanSpace` 维数 3），空集分支被 `x ∈ interior p → p ≠ ∅` 排除。

候选已有引理：
- 本批 `INTERIOR_AFFINIE_HUL_EQ_UNIV`
- `vectorSpan_univ`（Mathlib LinearAlgebra/AffineSpace）、`Module.finrank_top`
- `SetLike`/`Submodule.finrank` 维数 API -/
theorem AFF_DIM_INTERIOR_EQ_3 (x : V3) (p : Set V3) (hx : x ∈ interior p) :
    affDim p = 3 := by
  have hne : p ≠ ∅ := by
    rintro rfl
    simp at hx
  have hspan := INTERIOR_AFFINIE_HUL_EQ_UNIV x p hx
  have htop : affineSpan ℝ p = ⊤ := by
    refine SetLike.coe_injective ?_
    rw [AffineSubspace.top_coe, hspan]
  have hv : vectorSpan ℝ p = ⊤ :=
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 htop
  have h3 : affDim p = ((Module.finrank ℝ (vectorSpan ℝ p) : ℕ) : ℤ) := if_neg hne
  rw [h3, hv, finrank_top, finrank_euclideanSpace_fin]
  norm_num

/-- HOL polyhedron.hl :840-:853 `INTERIOR_IMP_RELATIVE_INTERIOR`

HOL 原文：
```
!x p:(real^3->bool). x IN interior p ==> x IN relative_interior p
```

编码说明：`relative_interior` ↦ `intrinsicInterior ℝ`（见文件头）。

证明思路：`interior p ⊆ p`；HOL 证 `interior p` 中任一点的邻域与
`affine hull p = univ` 之交仍在 `p`，即 `intrinsicInterior` 的成员条件
（`affineSpan ℝ p = univ` 时 `intrinsicInterior ℝ p = interior p`）。

候选已有引理：
- `mem_intrinsicInterior`（Mathlib Analysis/Convex/Intrinsic.lean:87）
- `intrinsicInterior_eq_interior`（全维数情形，若存在）/ `Metric.isOpen_iff`
- 本批 `INTERIOR_AFFINIE_HUL_EQ_UNIV`、`interior_subset` -/
theorem INTERIOR_IMP_RELATIVE_INTERIOR (x : V3) (p : Set V3) (hx : x ∈ interior p) :
    x ∈ intrinsicInterior ℝ p := by
  exact interior_subset_intrinsicInterior hx

/-- HOL polyhedron.hl :858-:886 `IN_RELATIVE_INTERIOR1`

HOL 原文：
```
!x:real^N s. x IN relative_interior s ==>
 ?e. &0 < e /\ (ball(x,e) INTER (affine hull s)) SUBSET relative_interior s
```

编码说明：交与包含按集合编码；`affine hull s` 以载体集合出现。

证明思路：相对内部在 `affineSpan s` 的子空间拓扑中是开的：由成员条件取
`e'` 使 `ball (x, e') ∩ affineSpan s ⊆ relative_interior s`，再取
`e = min e' e₀` 处理两条件的交。

候选已有引理：
- `mem_intrinsicInterior`、`intrinsicInterior` 的开性
  （`Intrinsic` 模块的 `isOpen` 系）
- `Metric.isOpen_iff`、`Set.subset_inter` -/
theorem IN_RELATIVE_INTERIOR1 (x : V3) (s : Set V3) (hx : x ∈ intrinsicInterior ℝ s) :
    ∃ e : ℝ, 0 < e ∧ (Metric.ball x e ∩ (affineSpan ℝ s : Set V3)) ⊆
      intrinsicInterior ℝ s := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx
  have hopen : IsOpen (interior ((↑) ⁻¹' s : Set (affineSpan ℝ s))) := isOpen_interior
  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp hopen
  have hxy : y ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact hy
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp ht (y : V3) hxy
  refine ⟨e, he, ?_⟩
  rintro z ⟨hzb, hzs⟩
  have hex : ∃ w : (affineSpan ℝ s), (w : V3) = z := ⟨⟨z, hzs⟩, rfl⟩
  obtain ⟨w, rfl⟩ := hex
  refine mem_intrinsicInterior.mpr ⟨w, ?_, rfl⟩
  rw [← hteq]
  exact hball hzb

/-! ## polyhedron.hl :891-:1180（fchanged 区域的开性与单射性） -/

/-! ### 批 5 内联辅助引理（Polytope.lean 尚无对应公开版本；内联实现） -/

/-- 点积的 ℝ-线性性（`dotRight` 的内联副本，供超平面方向计算使用）。 -/
private def dotLin5 (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    rw [dotProduct_add]
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

/-- 点积加法（Polytope.lean 私有 `dot_add` 的内联副本）。 -/
private theorem dot_add5 (a x y : V3) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y := by
  show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
  rw [dotProduct_add]

/-- 点积数乘（Polytope.lean 私有 `dot_smul` 的内联副本）。 -/
private theorem dot_smul5 (a x : V3) (r : ℝ) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  show a.ofLp ⬝ᵥ (r • x.ofLp) = r * (a.ofLp ⬝ᵥ x.ofLp)
  rw [dotProduct_smul]
  simp

/-- 点积左数乘。 -/
private theorem dot_smul_left5 (a b : V3) (r : ℝ) : (r • a) ⬝ᵥ b = r * (a ⬝ᵥ b) := by
  show (r • a).ofLp ⬝ᵥ b.ofLp = r * (a.ofLp ⬝ᵥ b.ofLp)
  rw [WithLp.ofLp_smul, dotProduct_comm, dotProduct_smul, dotProduct_comm, smul_eq_mul]

/-- 点积左减法。 -/
private theorem dot_sub_left5 (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  show (a - b).ofLp ⬝ᵥ c.ofLp = a.ofLp ⬝ᵥ c.ofLp - b.ofLp ⬝ᵥ c.ofLp
  rw [WithLp.ofLp_sub, dotProduct_comm, dotProduct_sub, dotProduct_comm, dotProduct_comm,
    dotProduct_comm c.ofLp a.ofLp, dotProduct_comm c.ofLp b.ofLp]

/-- Skolem 化的最小半空间表示（= Polytope.lean 私有 `minrep_skolem` 的公开
重述；`minrep_skolem` 为 private，无法跨文件使用）。 -/
private theorem exists_minrep {s : Set V3} (hsp : polyhedron s) :
    ∃ (F : Set (Set V3)) (a : Set V3 → V3) (b : Set V3 → ℝ), F.Finite ∧
      s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F ∧
      (∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h}) ∧
      ∀ F' : Set (Set V3), F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F' := by
  obtain ⟨F, hF, hs, hFprop, hmin⟩ := POLYHEDRON_INTER_AFFINE_MINIMAL.1 hsp
  have hex : ∀ h : Set V3, ∃ c : V3 × ℝ, h ∈ F → c.1 ≠ 0 ∧ h = {x : V3 | c.1 ⬝ᵥ x ≤ c.2} := by
    intro h
    by_cases hh : h ∈ F
    · obtain ⟨u, r, hu, hr⟩ := hFprop h hh
      exact ⟨(u, r), fun _ => ⟨hu, hr⟩⟩
    · exact ⟨(0, 0), fun hf => absurd hf hh⟩
  choose c hc using hex
  exact ⟨F, fun h => (c h).1, fun h => (c h).2, hF, hs, fun h hh => hc h hh, hmin⟩

/-- 有界非空、维数 ≥ 1 的多面体有真面（facet 存在性，= HOL
`POLYTOPE_FACET_EXISTS` 的多面体版本）：取最小表示的任一约束切一刀。 -/
private theorem exists_facet {s : Set V3} (hsp : polyhedron s) (hb : Bornology.IsBounded s)
    (hne : s.Nonempty) (hdim : 1 ≤ affDim s) :
    ∃ g : Set V3, FacetOf g s := by
  obtain ⟨F, a, b, hF, hs, hFprop, hmin⟩ := exists_minrep hsp
  have hFne : F.Nonempty := by
    by_contra hcon
    push_neg at hcon
    have hsaff : s = (affineSpan ℝ s : Set V3) := by
      rw [hcon, Set.sInter_empty, Set.inter_univ] at hs
      exact hs
    have hdir0 : (affineSpan ℝ s).direction = ⊥ := by
      rw [direction_affineSpan]
      refine Submodule.eq_bot_iff _ |>.2 fun u hu => ?_
      by_contra hune
      obtain ⟨x, hx⟩ := hne
      have hum : u ∈ (affineSpan ℝ s).direction := by
        rw [direction_affineSpan]; exact hu
      have hstep : ∀ n : ℕ, x + (n : ℝ) • u ∈ s := by
        intro n
        have hmem : ((n : ℝ) • u) ∈ (affineSpan ℝ s).direction :=
          Submodule.smul_mem _ (n : ℝ) hum
        have hvadd : ((n : ℝ) • u) +ᵥ x = x + (n : ℝ) • u := by
          rw [vadd_eq_add]; module
        rw [← hvadd, hsaff]
        exact AffineSubspace.vadd_mem_of_mem_direction hmem (subset_affineSpan ℝ s hx)
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hb
      have hkey : ∀ n : ℕ, (n : ℝ) * ‖u‖ ≤ C := by
        intro n
        have h1 := hC hx (hstep n)
        rw [dist_eq_norm] at h1
        have h2 : x - (x + (n : ℝ) • u) = -((n : ℝ) • u) := by module
        rw [h2, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
        exact h1
      have hpos : 0 < ‖u‖ := norm_pos_iff.2 hune
      obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖u‖ + 1)
      have h1 := mul_lt_mul_of_pos_right hn hpos
      have h2 : (C / ‖u‖ + 1) * ‖u‖ = C + ‖u‖ := by field_simp
      have h3 := hkey n
      linarith
    have h0 : affDim s = 0 := by
      rw [affDim, if_neg (Set.nonempty_iff_ne_empty.1 hne), ← direction_affineSpan, hdir0,
        finrank_bot]
      norm_num
    linarith [hdim, h0]
  obtain ⟨h0, h0mem⟩ := hFne
  exact ⟨s ∩ {x : V3 | a h0 ⬝ᵥ x = b h0},
    (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin _).2 ⟨h0, h0mem, rfl⟩⟩

/-- 点积加法备用与超平面仿射包（HOL `AFF_DIM_HYPERPLANE` 用法的内联版本）：
非空、二维且含于超平面 `{a ⬝ᵥ x = b}` 的集合的仿射包等于该超平面。 -/
private theorem affineSpan_eq_hyperplane {f : Set V3} {a : V3} {b : ℝ} (ha : a ≠ 0)
    (hne : f.Nonempty) (hsub : f ⊆ {x : V3 | a ⬝ᵥ x = b}) (hdim : affDim f = 2) :
    (affineSpan ℝ f : Set V3) = {x : V3 | a ⬝ᵥ x = b} := by
  obtain ⟨p0, hp0f⟩ := hne
  have hp0 : a ⬝ᵥ p0 = b := hsub hp0f
  have hmap : ∀ w : V3, dotLin5 a w = a ⬝ᵥ w := fun _ => rfl
  have hneH : ({x : V3 | a ⬝ᵥ x = b} : Set V3) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.1 ⟨p0, hp0⟩
  have hvK : vectorSpan ℝ ({x : V3 | a ⬝ᵥ x = b} : Set V3)
      = LinearMap.ker (dotLin5 a) := by
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      intro z hz
      obtain ⟨x, hx, y, hy, hz'⟩ := Set.mem_vsub.1 hz
      have hx1 : a ⬝ᵥ x = b := hx
      have hy1 : a ⬝ᵥ y = b := hy
      rw [← hz', SetLike.mem_coe, LinearMap.mem_ker]
      show dotLin5 a (x - y) = 0
      rw [LinearMap.map_sub, hmap, hmap, hx1, hy1, sub_self]
    · intro z hz
      rw [vectorSpan_def]
      have hz0 : a ⬝ᵥ z = 0 := by
        have h0' := LinearMap.mem_ker.1 hz
        rw [hmap] at h0'
        exact h0'
      refine Submodule.subset_span ?_
      refine Set.mem_vsub.2
        ⟨p0 + z, ?_, p0, (show p0 ∈ ({x : V3 | a ⬝ᵥ x = b} : Set V3) from hp0), ?_⟩
      · show a ⬝ᵥ (p0 + z) = b
        rw [dot_add5, hp0, hz0, add_zero]
      · show (p0 + z) -ᵥ p0 = z
        rw [vsub_eq_sub, add_sub_cancel_left]
  have hK2 : Module.finrank ℝ (LinearMap.ker (dotLin5 a)) = 2 := by
    have h1 := affDim_hyperplane ha b
    simp only [affDim, if_neg hneH] at h1
    rw [hvK] at h1
    exact_mod_cast h1
  have hSle : affineSpan ℝ f ≤ AffineSubspace.mk' p0 (LinearMap.ker (dotLin5 a)) := by
    refine affineSpan_le.2 fun z hz => ?_
    refine (AffineSubspace.mem_mk').2 ?_
    show dotLin5 a (z -ᵥ p0) = 0
    rw [vsub_eq_sub, LinearMap.map_sub, hmap, hmap, hsub hz, hp0, sub_self]
  have hdirEq : (affineSpan ℝ f).direction
      = (AffineSubspace.mk' p0 (LinearMap.ker (dotLin5 a))).direction := by
    refine Submodule.eq_of_le_of_finrank_le (AffineSubspace.direction_le hSle) ?_
    rw [AffineSubspace.direction_mk', direction_affineSpan]
    have hdim' : (Module.finrank ℝ (vectorSpan ℝ f) : ℤ) = 2 := by
      have h2' := hdim
      simp only [affDim, if_neg (Set.nonempty_iff_ne_empty.1 ⟨p0, hp0f⟩)] at h2'
      exact h2'
    rw [hK2]
    exact_mod_cast hdim'.symm.le
  have heq : affineSpan ℝ f = AffineSubspace.mk' p0 (LinearMap.ker (dotLin5 a)) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirEq
      ⟨p0, subset_affineSpan ℝ f hp0f⟩ hSle
  rw [heq]
  ext z
  constructor
  · intro hz
    have hz' : z -ᵥ p0 ∈ LinearMap.ker (dotLin5 a) := (AffineSubspace.mem_mk').1 hz
    show a ⬝ᵥ z = b
    have e1 : a ⬝ᵥ z = a ⬝ᵥ p0 := by
      have h2' : dotLin5 a (z -ᵥ p0) = 0 := hz'
      rw [vsub_eq_sub, LinearMap.map_sub, hmap, hmap, sub_eq_zero] at h2'
      exact h2'
    rw [e1, hp0]
  · intro hz
    have hz' : a ⬝ᵥ z = b := hz
    refine (AffineSubspace.mem_mk').2 ?_
    show dotLin5 a (z -ᵥ p0) = 0
    rw [vsub_eq_sub, LinearMap.map_sub, hmap, hmap, hz', hp0, sub_self]

/-- 直线上的坐标：`{v, w}` 仿射包中的点形如 `v + μ • (w - v)`。 -/
private theorem line_coord {v w y : V3} (hy : y ∈ (affineSpan ℝ {v, w} : Set V3)) :
    ∃ μ : ℝ, y - v = μ • (w - v) := by
  have hle : affineSpan ℝ {v, w} ≤ AffineSubspace.mk' v (ℝ ∙ (w - v)) := by
    refine affineSpan_le.2 fun p hp => ?_
    obtain hp' : p = v ∨ p = w := by
      rcases Set.mem_insert_iff.1 hp with h | h
      · exact Or.inl h
      · rw [Set.mem_singleton_iff] at h
        exact Or.inr h
    rcases hp' with hpe | hpe
    · rw [hpe]
      exact (AffineSubspace.mem_mk').2 (by
        simp only [vsub_eq_sub, sub_self]; exact Submodule.zero_mem _)
    · rw [hpe]
      exact (AffineSubspace.mem_mk').2
        (Submodule.mem_span_singleton.2 ⟨1, one_smul ℝ (w - v)⟩)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (AffineSubspace.mem_mk'.1 (hle hy))
  exact ⟨r, hr.symm⟩

/-- 两点集的方向：`vectorSpan {v, w} = ℝ ∙ (w - v)`。 -/
private theorem vectorSpan_pair5 (v w : V3) : vectorSpan ℝ {v, w} = ℝ ∙ (w - v) := by
  rw [vectorSpan_def]
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · intro z hz
    obtain ⟨p, hp, q, hq, hz⟩ := Set.mem_vsub.1 hz
    have hp' : p = v ∨ p = w := by
      rcases Set.mem_insert_iff.1 hp with h | h
      · exact Or.inl h
      · rw [Set.mem_singleton_iff] at h
        exact Or.inr h
    have hq' : q = v ∨ q = w := by
      rcases Set.mem_insert_iff.1 hq with h | h
      · exact Or.inl h
      · rw [Set.mem_singleton_iff] at h
        exact Or.inr h
    rcases hp' with hpe | hpe <;> rcases hq' with hqe | hqe
    · rw [← hz, hpe, hqe, vsub_eq_sub, sub_self]; exact Submodule.zero_mem _
    · rw [← hz, hpe, hqe, vsub_eq_sub]
      rw [(neg_sub w v).symm]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton.2 ⟨1, one_smul ℝ (w - v)⟩)
    · rw [← hz, hpe, hqe, vsub_eq_sub]
      exact Submodule.mem_span_singleton.2 ⟨1, one_smul ℝ (w - v)⟩
    · rw [← hz, hpe, hqe, vsub_eq_sub, sub_self]; exact Submodule.zero_mem _
  · have hmem : (w - v : V3) ∈ ({v, w} : Set V3) -ᵥ ({v, w} : Set V3) :=
      Set.mem_vsub.2 ⟨w, Set.mem_insert_of_mem v (by simp), v,
        Set.mem_insert v {w}, rfl⟩
    refine Submodule.span_le.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.subset_span hmem

/-! ## polyhedron.hl :891-:1180（fchanged 区域的开性与单射性） -/

/-- HOL polyhedron.hl :891-:1127 `FCHANGED_OPEN`（批 5 主打，HOL 证明约 240 行）

HOL 原文：
```
!p f:(real^3->bool).
  bounded p /\ polyhedron p /\ vec 0 IN interior p
/\ f facet_of p
==> open (fchanged f)
```

编码说明：`fchanged`、`facet_of` 经私有副本 `fchanged`、`FacetOf`
引用（= PolyAuto4 的 `fchanged`/`FacetOf`，见文件头合并计划）；
`open` ↦ `IsOpen`；`bounded` ↦ `Bornology.IsBounded`。

证明思路（HOL 结构）：(1) `POLYHEDRON_INTER_AFFINE_MINIMAL` + 选择公理把
polyhedron 写成有限交 `p = affine hull p ∩ ⋂ h {x | a h dot x = b h}`；(2)
`FACET_OF_POLYHEDRON_EXPLICIT`：`f = p ∩ {x | a h dot x = b h}` 且
`affine hull f = {x | a h dot x = b h}`（由 `AFF_DIM_HYPERPLANE` + 维数比较
`affDim f = affDim p - 1 = 2`）；(3) 任取 `v = t • v1 ∈ fchanged f`
（`v1 ∈ relative interior f`），用 `CONTINUOUS_ON_LIFT_DOT` 与
`IN_RELATIVE_INTERIOR1` 取半径，令 `r1 = min (‖v1‖⁻¹ e /6) 1 /2`、
`r2 = |b h| r1 /2`、`r3 = min (e/12) (d/2)`，证明 `v1` 的 `r3`-球内点的
正射线可调参 `t1` 仍打在超平面 `{a h dot x = b h}` 上且停在
`ball (v1, e)` 内；(4) 由 `t > 0` 缩放回 `v`，得 `fchanged f` 含
`v` 的开球，`open_def` 收尾。关键不等式大量使用 `REAL_ABS_BETWEEN`、
`REAL_LT_MUL2`、三角不等式（`NORM_TRIANGLE`）。

候选已有引理：
- 本批 `CONTINUOUS_ON_LIFT_DOT`、`IN_RELATIVE_INTERIOR1`、
  `INTERIOR_IMP_RELATIVE_INTERIOR`、`AFF_DIM_INTERIOR_EQ_3`
- `POLYHEDRON_INTER_AFFINE_MINIMAL`、`FACET_OF_POLYHEDRON_EXPLICIT`、
  `AFF_DIM_HYPERPLANE`、`RELATIVE_INTERIOR_OF_POLYHEDRON`：HOL :745 之前的
  `polyhedron.hl` 段（批 3/4 或后续批次），repo 尚未移植 → 需内联或补批
- `IsOpen`、`Metric.isOpen_iff`、`mem_intrinsicInterior`（Mathlib）
- 缺口：`POLYHEDRON_COLLINEAR_FACES` 等上游引理未移植 -/
theorem FCHANGED_OPEN (p f : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hz : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    IsOpen (fchanged f) := by
  -- supporting-hyperplane data for the facet f
  obtain ⟨a, b, ha0, hpsub, hfeq⟩ := FACET_OF_POLYHEDRON hp hf
  have h0p : (0 : V3) ∈ intrinsicInterior ℝ p := interior_subset_intrinsicInterior hz
  have hfne : f ≠ ∅ := hf.2.1
  have h0f : (0 : V3) ∉ f := by
    intro h0
    have hfp : p ⊆ f := subset_of_faceOf hf.1 (Set.Subset.refl p)
      (Set.not_disjoint_iff.2 ⟨(0 : V3), h0, h0p⟩)
    have hfpeq : f = p := Set.Subset.antisymm hf.1.1 hfp
    rw [hfpeq] at hf
    have h2 := hf.2.2
    linarith
  have h0in : (0 : V3) ∈ p := interior_subset hz
  have hdot0 : a ⬝ᵥ (0 : V3) = 0 := (dotLin5 a).map_zero

  have hb_ge : 0 ≤ b := by
    have h1 : (0 : V3) ∈ {x : V3 | a ⬝ᵥ x ≤ b} := hpsub h0in
    rw [Set.mem_setOf_eq, hdot0] at h1
    linarith
  have hbpos : 0 < b := by
    rcases lt_or_eq_of_le hb_ge with h | h
    · exact h
    · exfalso
      apply h0f
      rw [hfeq]
      refine ⟨h0in, ?_⟩
      rw [Set.mem_setOf_eq, hdot0, h]
  have hdim3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
  have hdimf : affDim f = 2 := by rw [hf.2.2, hdim3]; norm_num
  have hsf : f ⊆ {x : V3 | a ⬝ᵥ x = b} := by rw [hfeq]; exact Set.inter_subset_right
  have hspanfeq : (affineSpan ℝ f : Set V3) = {x : V3 | a ⬝ᵥ x = b} :=
    affineSpan_eq_hyperplane ha0 (Set.nonempty_iff_ne_empty.2 hfne) hsf hdimf
  have hdot : Continuous fun y : V3 => a ⬝ᵥ y :=
    continuous_const.dotProduct (PiLp.continuous_ofLp 2 _)
  -- pointwise: every v ∈ fchanged f has the open neighbourhood
  -- {y | a ⬝ᵥ y > 0} ∩ ψ ⁻¹' (ball v1 e) inside fchanged f, where ψ y = (b/(a⬝ᵥy)) • y
  refine Metric.isOpen_iff.2 fun v hv => ?_
  obtain ⟨v1, t, rfl, hv1, ht⟩ := hv
  have hv1f : v1 ∈ f := (mem_rint_iff.1 hv1).1
  have hv1b : a ⬝ᵥ v1 = b := hsf hv1f
  have hav : a ⬝ᵥ (t • v1) = t * b := by rw [dot_smul5, hv1b]
  have hav0 : 0 < a ⬝ᵥ (t • v1) := by rw [hav]; exact mul_pos ht hbpos
  obtain ⟨e, he0, hball⟩ := IN_RELATIVE_INTERIOR1 v1 f hv1
  have hPopen : IsOpen {y : V3 | a ⬝ᵥ y > 0} := isOpen_lt continuous_const hdot
  have hψcont : ContinuousOn (fun y : V3 => (b / (a ⬝ᵥ y)) • y) {y : V3 | a ⬝ᵥ y > 0} := by
    have hc : ContinuousOn (fun y : V3 => b / (a ⬝ᵥ y)) {y : V3 | a ⬝ᵥ y > 0} :=
      ContinuousOn.div continuousOn_const hdot.continuousOn fun y hy => ne_of_gt hy
    exact ContinuousOn.smul (f := fun y : V3 => b / (a ⬝ᵥ y)) (g := id) hc continuousOn_id
  -- the open neighbourhood U of v inside fchanged f
  have hUopen : IsOpen ({y : V3 | a ⬝ᵥ y > 0} ∩
      (fun y : V3 => (b / (a ⬝ᵥ y)) • y) ⁻¹' Metric.ball v1 e) :=
    ContinuousOn.isOpen_inter_preimage hψcont hPopen Metric.isOpen_ball
  have hψvmem : (b / (a ⬝ᵥ (t • v1))) • (t • v1) ∈ Metric.ball v1 e := by
    have hψv : (b / (a ⬝ᵥ (t • v1))) • (t • v1) = v1 := by
      rw [hav]
      rw [show (b / (t * b)) • (t • v1) = ((b / (t * b)) * t) • v1 from
        by rw [smul_smul]]
      rw [show (b / (t * b)) * t = 1 from by field_simp, one_smul]
    rw [hψv]
    exact Metric.mem_ball_self he0
  have hvmem : t • v1 ∈ ({y : V3 | a ⬝ᵥ y > 0} ∩
      (fun y : V3 => (b / (a ⬝ᵥ y)) • y) ⁻¹' Metric.ball v1 e) := ⟨hav0, hψvmem⟩
  have hUsub : ({y : V3 | a ⬝ᵥ y > 0} ∩
      (fun y : V3 => (b / (a ⬝ᵥ y)) • y) ⁻¹' Metric.ball v1 e) ⊆ fchanged f := by
    rintro y ⟨hyP, hyball⟩
    have hay0 : 0 < a ⬝ᵥ y := hyP
    have hx0 : a ⬝ᵥ y ≠ 0 := ne_of_gt hay0
    have hb0 : b ≠ 0 := ne_of_gt hbpos
    have hEq : y = (a ⬝ᵥ y / b) • ((b / (a ⬝ᵥ y)) • y) := by
      rw [smul_smul]
      have hprodc : (a ⬝ᵥ y / b) * (b / (a ⬝ᵥ y)) = 1 := by field_simp
      rw [hprodc, one_smul]
    refine ⟨(b / (a ⬝ᵥ y)) • y, a ⬝ᵥ y / b, hEq, ?_, div_pos hay0 hbpos⟩
    · have hψyH : (b / (a ⬝ᵥ y)) • y ∈ {x : V3 | a ⬝ᵥ x = b} := by
        show a ⬝ᵥ ((b / (a ⬝ᵥ y)) • y) = b
        rw [dot_smul5, div_mul_cancel₀ b hx0]
      rw [hspanfeq] at hball
      exact hball ⟨hyball, hψyH⟩
  obtain ⟨ε, hε0, hballε⟩ := Metric.isOpen_iff.1 hUopen (t • v1) hvmem
  exact ⟨ε, hε0, fun z hz => hUsub (hballε hz)⟩

/-- HOL polyhedron.hl :1132-:1179 `FCHANGED_ONE_TO_ONE`

HOL 原文：
```
!p f1 f2:real^3->bool.
     bounded p /\ polyhedron p /\ vec 0 IN interior p /\ f1 facet_of p
/\ f2 facet_of p /\  ~(fchanged f1 INTER fchanged f2= {})
==> f1=f2
```

编码说明：同上，`fchanged`/`facet_of` 经私有副本引用；
`~(A INTER B = {})` ↦ `fchanged f1 ∩ fchanged f2 ≠ ∅`。

证明思路（HOL 结构）：取公共点 `v = t•v1 = t'•v1'`（`v1, v1'` 分别在
`f1, f2` 的相对内部）；`facet_of` 展开排除 `f1 = p` / `f2 = p`（与
`vec 0 ∉ ⋃ {f | f facet_of p}` 矛盾，用 `AFF_DIM_INTERIOR_EQ_3`）；然后
`POLYHEDRON_COLLINEAR_FACES`（`s • p = t • q ∧ s,t > 0 → s = t`）得
`t' = t`，故 `v1 = v1'`，最后 `FACE_OF_EQ`（相对内部相交的两个 face 相等）。

候选已有引理：
- 本批 `AFF_DIM_INTERIOR_EQ_3`、`INTERIOR_IMP_RELATIVE_INTERIOR`
- `FACE_OF_EQ`：polytope.ml（repo 未移植，需补批）；`POLYHEDRON_COLLINEAR_FACES`
  （flyspeck_multivariate.ml:6881，repo 未移植）
- `Set.extremePoints`、`mem_intrinsicInterior`（Mathlib） -/
theorem FCHANGED_ONE_TO_ONE (p f1 f2 : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hz : (0 : V3) ∈ interior p)
    (hf1 : FacetOf f1 p) (hf2 : FacetOf f2 p)
    (hinter : fchanged f1 ∩ fchanged f2 ≠ ∅) : f1 = f2 := by
  obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.2 hinter
  obtain ⟨hvm1, hvm2⟩ := hv
  obtain ⟨v1, t, hveq1, hv1, ht⟩ := hvm1
  obtain ⟨v1', t', hveq2, hv1', ht'⟩ := hvm2
  have hray : t • v1 = t' • v1' := hveq1.symm.trans hveq2
  have h0p : (0 : V3) ∈ intrinsicInterior ℝ p := interior_subset_intrinsicInterior hz
  -- properness: fᵢ ≠ p, whence 0 ∉ fᵢ (0 ∈ relative interior of p)
  have hf1ne : f1 ≠ p := by
    intro hcon
    rw [hcon] at hf1
    have h2 := hf1.2.2
    linarith
  have hf2ne : f2 ≠ p := by
    intro hcon
    rw [hcon] at hf2
    have h2 := hf2.2.2
    linarith
  have h0f1 : (0 : V3) ∉ f1 := fun h0 => hf1ne
    (Set.Subset.antisymm hf1.1.1 (subset_of_faceOf hf1.1 (Set.Subset.refl p)
      (Set.not_disjoint_iff.2 ⟨(0 : V3), h0, h0p⟩)))
  have h0f2 : (0 : V3) ∉ f2 := fun h0 => hf2ne
    (Set.Subset.antisymm hf2.1.1 (subset_of_faceOf hf2.1 (Set.Subset.refl p)
      (Set.not_disjoint_iff.2 ⟨(0 : V3), h0, h0p⟩)))
  have hv1f1 : v1 ∈ p := hf1.1.1 (mem_rint_iff.1 hv1).1
  have hv1'f2 : v1' ∈ p := hf2.1.1 (mem_rint_iff.1 hv1').1
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · -- t < t': the ray from 0 through v1' enters f2 via v1' ∈ openSegment 0 v1
    exfalso
    have hcoef : v1' = (t / t') • v1 := by
      have h1 : (1 / t') • (t • v1) = (1 / t') • (t' • v1') := by rw [hray]
      rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ ht'.ne', one_smul,
        ← div_eq_inv_mul] at h1
      exact h1.symm
    refine h0f2 ((hf2.1.2.2 (0 : V3) v1 v1' (interior_subset hz) hv1f1
      (mem_rint_iff.1 hv1').1 ?_).1)
    have hlt1 : t / t' < 1 := (div_lt_one ht').2 hlt
    refine ⟨1 - t / t', t / t', by linarith, div_pos ht ht', by ring, ?_⟩
    rw [smul_zero, zero_add, hcoef]
  · -- t = t': v1 = v1' lies in both relative interiors
    have h1 : t • v1 = t • v1' := by
      rw [← heq] at hray
      exact hray
    have hvv : v1 = v1' := by
      have h2 := congrArg (fun x => (1 / t) • x) h1
      rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ ht.ne', one_smul] at h2
      rw [one_smul] at h2
      exact h2
    exact faceOf_eq hf1.1 hf2.1 (Set.not_disjoint_iff.2 ⟨v1, hv1, hvv ▸ hv1'⟩)
  · -- t' < t: symmetric, using the face f1
    exfalso
    have hcoef : v1 = (t' / t) • v1' := by
      have h1 : (1 / t) • (t' • v1') = (1 / t) • (t • v1) := by rw [← hray]
      rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ ht.ne', one_smul,
        ← div_eq_inv_mul] at h1
      exact h1.symm
    refine h0f1 ((hf1.1.2.2 (0 : V3) v1' v1 (interior_subset hz) hv1'f2
      (mem_rint_iff.1 hv1).1 ?_).1)
    have hlt1 : t' / t < 1 := (div_lt_one ht).2 hgt
    refine ⟨1 - t' / t, t' / t, by linarith, div_pos ht' ht, by ring, ?_⟩
    rw [smul_zero, zero_add, hcoef]


/-! ## polyhedron.hl :1184-:1311（基数与边的存在性） -/

/-- HOL polyhedron.hl :1184-:1275 `CARD_EXISTS_2`

HOL 原文：
```
!e:A->bool. FINITE e /\ CARD e=2 ==> ?v:A w:A. e={v,w}
```

编码说明：HOL `CARD`（自然数）↦ `Set.ncard`（不有限时为 0，这里显式带
`e.Finite` 前提，与 HOL 一致）。

证明思路：Mathlib 有现成刻画 `Set.ncard_eq_two : s.ncard = 2 ↔ ∃ a b,
a ≠ b ∧ s = {a, b}`，一步完成（zuzhuang）。

候选已有引理：
- `Set.ncard_eq_two`（Mathlib Mathlib/Data/Set/Card.lean）
- `Set.Finite`、`Set.ncard` -/
theorem CARD_EXISTS_2 {α : Type*} (e : Set α) (he : e.Finite) (hc : e.ncard = 2) :
    ∃ v w : α, e = {v, w} := by
  obtain ⟨v, w, -, rfl⟩ := Set.ncard_eq_two.mp hc
  exact ⟨v, w, rfl⟩

/-- HOL polyhedron.hl :1278-:1311 `EXISTS_EDGE_POLYTOPE`

HOL 原文：
```
!p:real^3->bool.
     bounded p /\ polyhedron p /\ vec 0 IN interior p
==> ?e. e IN edges p
```

编码说明：`edges p = {{v,w} | segment[v,w] edge_of p}`（flyspeck_multivariate.ml:6887）
经私有 `edges` 引用，`edge_of`（polytope.ml:2847：`e face_of s ∧
aff_dim e = &1`）经私有 `edgeOf` 引用；成员关系 `e ∈ edges p` 已按
集合论展开为 `∃ v w, e = {v,w} ∧ edgeOf (segment ℝ v w) p` 语义。

证明思路（HOL 结构）：(1) `POLYTOPE_EQ_BOUNDED_POLYHEDRON`：p 是多胞形；
(2) `AFF_DIM_INTERIOR_EQ_3` 得满维；(3) `POLYTOPE_FACET_EXISTS` 两连击：
p 有余维 1 面 `f`（`affDim f = 2`），f 又有余维 1 面 `f'`（`affDim f' = 1`），
且 `f'` 非空；(4) `affDim f' = 1` ⇒ 仿射无关基 `b` 满足 `CARD b = 2`，经
`CARD_EXISTS_2` 写成 `{v, w}`；(5) `FACE_OF_TRANS` 得 `f' face_of p`，故
`e = {v,w}` 见证 `edges p`。

候选已有引理：
- 本批 `AFF_DIM_INTERIOR_EQ_3`、`CARD_EXISTS_2`
- `POLYTOPE_EQ_BOUNDED_POLYHEDRON`、`POLYTOPE_FACET_EXISTS`、
  `FACE_OF_POLYTOPE_POLYTOPE`、`FACE_OF_TRANS`：HOL polytope.ml /
  flyspeck 库引理，repo 均未移植 → 需补批（fenxi）
- `segment`、`affineSpan`、`Set.ncard`（Mathlib） -/
theorem EXISTS_EDGE_POLYTOPE (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hz : (0 : V3) ∈ interior p) :
    ∃ e : Set V3, e ∈ edges p := by
  have hdim3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p hz
  have hpne : p.Nonempty := ⟨0, interior_subset hz⟩
  -- facet g1 of p, made explicit and polyhedral
  obtain ⟨g1, hg1f⟩ := exists_facet hp hb hpne (by rw [hdim3]; norm_num)
  obtain ⟨a₁, b₁, ha₁, -, hg1eq⟩ := FACET_OF_POLYHEDRON hp hg1f
  have hg1ne : g1.Nonempty := Set.nonempty_iff_ne_empty.2 hg1f.2.1
  have hg1b : Bornology.IsBounded g1 := Bornology.IsBounded.subset hb hg1f.1.1
  have hg1p : polyhedron g1 := by
    rw [hg1eq]
    exact POLYHEDRON_INTER hp (POLYHEDRON_HYPERPLANE ha₁ b₁)
  have hdim2 : affDim g1 = 2 := by rw [hg1f.2.2, hdim3]; norm_num
  -- facet g2 of g1
  obtain ⟨g2, hg2f⟩ := exists_facet hg1p hg1b hg1ne (by rw [hdim2]; norm_num)
  have hg2b : Bornology.IsBounded g2 :=
    Bornology.IsBounded.subset hb (Set.Subset.trans hg2f.1.1 hg1f.1.1)
  have hg2ne : g2.Nonempty := Set.nonempty_iff_ne_empty.2 hg2f.2.1
  have hdim1 : affDim g2 = 1 := by rw [hg2f.2.2, hdim2]; norm_num
  -- two distinct points of g2
  obtain ⟨v, w, hvw, hv, hw⟩ : ∃ v w : V3, v ≠ w ∧ v ∈ g2 ∧ w ∈ g2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v0, hv0⟩ := hg2ne
    have hsingle : g2 = {v0} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hv0, fun y hy => by
        by_contra hne
        exact hcon v0 y (fun h => hne h.symm) hv0 hy⟩
    rw [hsingle, affDim_singleton] at hdim1
    norm_num at hdim1
  -- g2 lies on the line through v, w
  have hmem : ∀ z ∈ ({v, w} : Set V3), z ∈ g2 := by
    intro z hz
    rcases Set.mem_insert_iff.1 hz with rfl | hz
    · exact hv
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hw
  have hvspan : vectorSpan ℝ {v, w} = vectorSpan ℝ g2 := by
    refine Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hmem) ?_
    have h1 : vectorSpan ℝ {v, w} = ℝ ∙ (w - v) := vectorSpan_pair5 v w
    have h2 : Module.finrank ℝ (ℝ ∙ (w - v)) = 1 :=
      finrank_span_singleton (sub_ne_zero.2 (Ne.symm hvw))
    have h3 : (Module.finrank ℝ (vectorSpan ℝ g2) : ℤ) = 1 := by
      have h3' : affDim g2 = (Module.finrank ℝ (vectorSpan ℝ g2) : ℤ) := by
        simp only [affDim, if_neg (Set.nonempty_iff_ne_empty.1 hg2ne)]
      rw [h3'] at hdim1
      exact hdim1
    rw [h1, h2]
    exact_mod_cast h3.le
  have hspang : (affineSpan ℝ {v, w} : Set V3) = (affineSpan ℝ g2 : Set V3) := by
    have hsp' : affineSpan ℝ {v, w} = affineSpan ℝ g2 :=
      AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
        (by rw [direction_affineSpan, direction_affineSpan, hvspan])
        ⟨v, subset_affineSpan ℝ {v, w} (Set.mem_insert v {w})⟩ (affineSpan_mono ℝ hmem)
    rw [hsp']
  have hg2sub : g2 ⊆ (affineSpan ℝ {v, w} : Set V3) := by
    rw [hspang]
    exact subset_affineSpan ℝ g2
  -- closedness of g1, g2 and compactness of g2
  have hcont : ∀ a : V3, Continuous fun y : V3 => a ⬝ᵥ y := fun a =>
    continuous_const.dotProduct (PiLp.continuous_ofLp 2 _)
  have hg1c : IsClosed g1 := by
    rw [hg1eq]
    exact (POLYHEDRON_IMP_CLOSED hp).inter (isClosed_eq (hcont a₁) continuous_const)
  have hg2c : IsClosed g2 := by
    obtain ⟨a₂, b₂, -, -, hg2eq⟩ := FACET_OF_POLYHEDRON hg1p hg2f
    rw [hg2eq]
    exact hg1c.inter (isClosed_eq (hcont a₂) continuous_const)
  have hgcpt : IsCompact g2 := Metric.isCompact_of_isClosed_isBounded hg2c hg2b
  -- coordinate on the line, endpoints of g2 as min/max of the coordinate
  set d : V3 := w - v with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hvw)
  have hdd : d ⬝ᵥ d ≠ 0 := fun h => hd0 (by simpa using dotProduct_self_eq_zero.1 h)
  have hddpos : 0 < d ⬝ᵥ d := by
    have hnn : 0 ≤ d.ofLp ⬝ᵥ d.ofLp := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact lt_of_le_of_ne hnn (Ne.symm hdd)
  have hcoord : ∀ y ∈ g2, ∃ μ : ℝ, y - v = μ • d ∧ (y - v) ⬝ᵥ d = μ * (d ⬝ᵥ d) := by
    intro y hy
    obtain ⟨μ, hμ⟩ := line_coord (hg2sub hy)
    exact ⟨μ, hμ, by rw [hμ, dot_smul_left5]⟩
  have hcc : Continuous fun y : V3 => (y - v) ⬝ᵥ d / (d ⬝ᵥ d) := by
    refine Continuous.div ?_ continuous_const fun _ => hdd
    have hA : Continuous fun y : V3 => y ⬝ᵥ d :=
      Continuous.dotProduct (PiLp.continuous_ofLp 2 _) continuous_const
    have hB : Continuous fun y : V3 => v ⬝ᵥ d := continuous_const
    refine Continuous.congr (hA.sub hB) fun y => (dot_sub_left5 y v d).symm
  obtain ⟨ymin, hymin, hmin⟩ := hgcpt.exists_isMinOn hg2ne hcc.continuousOn
  obtain ⟨ymax, hymax, hmax⟩ := hgcpt.exists_isMaxOn hg2ne hcc.continuousOn
  obtain ⟨α, hα, hcα⟩ := hcoord ymin hymin
  obtain ⟨β, hβ, hcβ⟩ := hcoord ymax hymax
  have hmin' : ∀ y ∈ g2, α * (d ⬝ᵥ d) ≤ (y - v) ⬝ᵥ d := fun y hy => by
    have h0 : ((ymin - v) ⬝ᵥ d) / (d ⬝ᵥ d) ≤ ((y - v) ⬝ᵥ d) / (d ⬝ᵥ d) := hmin hy
    rw [hcα] at h0
    rw [le_div_iff₀ hddpos, div_mul_cancel₀ _ (ne_of_gt hddpos)] at h0
    exact h0
  have hmax' : ∀ y ∈ g2, (y - v) ⬝ᵥ d ≤ β * (d ⬝ᵥ d) := fun y hy => by
    have h0 : ((ymin - v) ⬝ᵥ d) / (d ⬝ᵥ d) ≤ ((y - v) ⬝ᵥ d) / (d ⬝ᵥ d) := hmin hy
    have h1 : ((y - v) ⬝ᵥ d) / (d ⬝ᵥ d) ≤ ((ymax - v) ⬝ᵥ d) / (d ⬝ᵥ d) := hmax hy
    rw [hcβ, div_le_iff₀ hddpos, div_mul_cancel₀ _ (ne_of_gt hddpos)] at h1
    exact h1
  have hαβ : α < β := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ y ∈ g2, y = ymin := by
      intro y hy
      obtain ⟨μ, hμ, hcμ⟩ := hcoord y hy
      have h1 : α * (d ⬝ᵥ d) ≤ μ * (d ⬝ᵥ d) := (hmin' y hy).trans hcμ.le
      have h2 : μ * (d ⬝ᵥ d) ≤ β * (d ⬝ᵥ d) := by rw [← hcμ]; exact hmax' y hy
      have hαle : α ≤ μ := le_of_mul_le_mul_right h1 hddpos
      have hμle : μ ≤ β := le_of_mul_le_mul_right h2 hddpos
      have hcyeq : μ = α := le_antisymm (le_trans hμle hcon) hαle
      have hμeq : y - v = α • d := by rw [← hcyeq]; exact hμ
      have heq2 : ymin - v = y - v := by rw [hα, ← hμeq]
      calc y = v + (y - v) := by module
        _ = v + (ymin - v) := by rw [← heq2]
        _ = ymin := by module
    rw [Set.eq_singleton_iff_unique_mem.2 ⟨hymin, hall⟩, affDim_singleton] at hdim1
    norm_num at hdim1
  have hminmax : ymin ≠ ymax := by
    intro hcon
    have h1 : α = β := by
      rw [hcon] at hα
      have h2' : (α • d) ⬝ᵥ d = (β • d) ⬝ᵥ d := by rw [hα.symm, hβ]
      rw [dot_smul_left5, dot_smul_left5] at h2'
      exact mul_left_injective₀ (ne_of_gt hddpos) h2'
    linarith [hαβ]
  -- g2 = segment ℝ ymin ymax
  have hseg : g2 = segment ℝ ymin ymax := by
    refine Set.ext fun y => ?_
    constructor
    · intro hy
      obtain ⟨μ, hμ, hcμ⟩ := hcoord y hy
      have h1 : α ≤ μ := le_of_mul_le_mul_right ((hmin' y hy).trans hcμ.le) hddpos
      have h2 : μ ≤ β := le_of_mul_le_mul_right
        (by rw [← hcμ]; exact hmax' y hy) hddpos
      have hβ0 : β - α ≠ 0 := ne_of_gt (sub_pos.2 hαβ)
      have hβpos : 0 < β - α := sub_pos.2 hαβ
      set t : ℝ := (β - μ) / (β - α) with htdef
      obtain ⟨ht01a, ht01b⟩ : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith) hβpos.le, (div_le_one hβpos).2 (by linarith)⟩
      have htmul : t * α + (1 - t) * β = μ := by
        rw [htdef]
        field_simp
        linarith
      have hy' : y = v + μ • d := by rw [← hμ]; module
      have hy1 : ymin = v + α • d := by rw [← hα]; module
      have hy2 : ymax = v + β • d := by rw [← hβ]; module
      have hkey : t • ymin + (1 - t) • ymax = v + μ • d := by
        rw [hy1, hy2]
        have e1 : t • (v + α • d) + (1 - t) • (v + β • d)
            = (t + (1 - t)) • v + (t * α + (1 - t) * β) • d := by
          rw [smul_add, smul_add, smul_smul, smul_smul]
          module
        rw [e1, show t + (1 - t) = 1 from by ring, one_smul, htmul]
      rw [hy']
      exact ⟨t, 1 - t, ht01a, by linarith, by ring, hkey⟩
    · intro hy
      exact Convex.segment_subset hg2f.1.2.1 hymin hymax hy
  refine ⟨{ymin, ymax}, Set.mem_setOf.2 ⟨ymin, ymax, rfl, ?_, ?_⟩⟩
  · rw [← hseg]
    exact FaceOf.trans hg2f.1 hg1f.1
  · exact (affDim_segment ymin ymax).2 hminmax