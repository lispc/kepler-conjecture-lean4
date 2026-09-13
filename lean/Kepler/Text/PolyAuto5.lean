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
  (`fchanged_p5`, `polyhedron_p5`, `faceOf_p5`, `facetOf_p5`, `affDim_p5`,
  `edgeOf_p5`, `edges_p5`), byte-for-byte the PolyAuto4 bodies
  (`edgeOf_p5`/`edges_p5` are new ports, quoted verbatim from
  polytope.ml:2847 / flyspeck_multivariate.ml:6887; `edges` uses the CLOSED
  segment `segment[v,w]`, unlike the open-segment `face_of` quantifier).
  MERGE PLAN: at assembly, delete the `_p5` copies and re-point every
  occurrence to PolyAuto4's `fchanged`/`polyhedron`/`FaceOf`/`FacetOf`/
  `affDim` (identical bodies); `edgeOf_p5`/`edges_p5` should move next to
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

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Classical

/-! ## 批 5 需要的上游定义（PolyAuto4 同体私有副本；见文件头「合并去重」说明） -/

/-- PolyAuto4.lean `affDim` 的私有副本（HOL `aff_dim`，polytope.ml；
∅ ↦ -1，否则仿射包方向 `vectorSpan` 的维数）。 -/
private noncomputable def affDim_p5 (s : Set V3) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- PolyAuto4.lean `FaceOf` 的私有副本（HOL `t face_of s`，polytope.ml，
flyspeck Definition 4.7 QLITJET）：
```
t SUBSET s /\ convex t /\
!a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t
```
-/
private def faceOf_p5 (t s : Set V3) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : V3, a ∈ s → b ∈ s → x ∈ t → x ∈ segment ℝ a b → a ∈ t ∧ b ∈ t

/-- PolyAuto4.lean `FacetOf` 的私有副本（HOL `f facet_of s`，polytope.ml:2620）：
```
f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1
```
-/
private def facetOf_p5 (f s : Set V3) : Prop :=
  faceOf_p5 f s ∧ f ≠ ∅ ∧ affDim_p5 f = affDim_p5 s - 1

/-- PolyAuto4.lean `polyhedron` 的私有副本（HOL `polyhedron s`，flyspeck
Definition 4.8 QSRHLXB，polytope.ml:4385）：
```
polyhedron s <=> ?f. FINITE f /\ s = INTERS f /\
  (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})
```
-/
private def polyhedron_p5 (s : Set V3) : Prop :=
  ∃ F : Set (Set V3), F.Finite ∧ s = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}

/-- PolyAuto4.lean `fchanged` 的私有副本（HOL `fchanged`，polyhedron.hl:512
`new_definition`，逐字移植）：
```
fchanged f={v| ?v1 t. v=t% v1 /\ v1 IN (relative_interior f)/\ t> &0}
```
即 `f` 相对内部各点出发的正射线之并。 -/
private def fchanged_p5 (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-- HOL `e edge_of s`（polytope.ml:2847，逐字移植；批 5 新增）：
```
e edge_of s <=> e face_of s /\ aff_dim e = &1
```
-/
private def edgeOf_p5 (e s : Set V3) : Prop :=
  faceOf_p5 e s ∧ affDim_p5 e = 1

/-- HOL `edges s = {{v,w} | segment[v,w] edge_of s}`（flyspeck_multivariate.ml:6887，
逐字移植；注意此处是**闭**段 `segment[v,w]`） -/
private def edges_p5 (s : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ edgeOf_p5 (segment ℝ v w) s}

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
  sorry

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
    (affineSpan ℝ (Metric.ball x e) : Set V3) = univ := by
  sorry

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
    (affineSpan ℝ p : Set V3) = univ := by
  sorry

/-- HOL polyhedron.hl :828-:836 `AFF_DIM_INTERIOR_EQ_3`

HOL 原文：
```
!x p:(real^3->bool). x IN interior p ==> aff_dim p= &3
```

编码说明：HOL `aff_dim` ↦ 本批私有 `affDim_p5`（= PolyAuto4 的 `affDim`；
∅ ↦ -1，否则 `Module.finrank ℝ (vectorSpan ℝ s)`）。

证明思路：`INTERIOR_AFFINIE_HUL_EQ_UNIV` 得 `affineSpan p = univ`；
`vectorSpan ℝ univ = ⊤`，`finrank ℝ (⊤ : Submodule ℝ V3) = 3`
（`EuclideanSpace` 维数 3），空集分支被 `x ∈ interior p → p ≠ ∅` 排除。

候选已有引理：
- 本批 `INTERIOR_AFFINIE_HUL_EQ_UNIV`
- `vectorSpan_univ`（Mathlib LinearAlgebra/AffineSpace）、`Module.finrank_top`
- `SetLike`/`Submodule.finrank` 维数 API -/
theorem AFF_DIM_INTERIOR_EQ_3 (x : V3) (p : Set V3) (hx : x ∈ interior p) :
    affDim_p5 p = 3 := by
  sorry

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
  sorry

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
  sorry

/-! ## polyhedron.hl :891-:1180（fchanged 区域的开性与单射性） -/

/-- HOL polyhedron.hl :891-:1127 `FCHANGED_OPEN`（批 5 主打，HOL 证明约 240 行）

HOL 原文：
```
!p f:(real^3->bool).
  bounded p /\ polyhedron p /\ vec 0 IN interior p
/\ f facet_of p
==> open (fchanged f)
```

编码说明：`fchanged`、`facet_of` 经私有副本 `fchanged_p5`、`facetOf_p5`
引用（= PolyAuto4 的 `fchanged`/`FacetOf`，见文件头合并计划）；
`open` ↦ `IsOpen`；`bounded` ↦ `Bornology.IsBounded`。

证明思路（HOL 结构）：(1) `POLYHEDRON_INTER_AFFINE_MINIMAL` + 选择公理把
polyhedron 写成有限交 `p = affine hull p ∩ ⋂ h {x | a h dot x = b h}`；(2)
`FACET_OF_POLYHEDRON_EXPLICIT`：`f = p ∩ {x | a h dot x = b h}` 且
`affine hull f = {x | a h dot x = b h}`（由 `AFF_DIM_HYPERPLANE` + 维数比较
`affDim f = affDim p - 1 = 2`）；(3) 任取 `v = t • v1 ∈ fchanged_p5 f`
（`v1 ∈ relative interior f`），用 `CONTINUOUS_ON_LIFT_DOT` 与
`IN_RELATIVE_INTERIOR1` 取半径，令 `r1 = min (‖v1‖⁻¹ e /6) 1 /2`、
`r2 = |b h| r1 /2`、`r3 = min (e/12) (d/2)`，证明 `v1` 的 `r3`-球内点的
正射线可调参 `t1` 仍打在超平面 `{a h dot x = b h}` 上且停在
`ball (v1, e)` 内；(4) 由 `t > 0` 缩放回 `v`，得 `fchanged_p5 f` 含
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
    (hp : polyhedron_p5 p) (hz : (0 : V3) ∈ interior p) (hf : facetOf_p5 f p) :
    IsOpen (fchanged_p5 f) := by
  sorry

/-- HOL polyhedron.hl :1132-:1179 `FCHANGED_ONE_TO_ONE`

HOL 原文：
```
!p f1 f2:real^3->bool.
     bounded p /\ polyhedron p /\ vec 0 IN interior p /\ f1 facet_of p
/\ f2 facet_of p /\  ~(fchanged f1 INTER fchanged f2= {})
==> f1=f2
```

编码说明：同上，`fchanged`/`facet_of` 经私有副本引用；
`~(A INTER B = {})` ↦ `fchanged_p5 f1 ∩ fchanged_p5 f2 ≠ ∅`。

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
    (hp : polyhedron_p5 p) (hz : (0 : V3) ∈ interior p)
    (hf1 : facetOf_p5 f1 p) (hf2 : facetOf_p5 f2 p)
    (hinter : fchanged_p5 f1 ∩ fchanged_p5 f2 ≠ ∅) : f1 = f2 := by
  sorry

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
  sorry

/-- HOL polyhedron.hl :1278-:1311 `EXISTS_EDGE_POLYTOPE`

HOL 原文：
```
!p:real^3->bool.
     bounded p /\ polyhedron p /\ vec 0 IN interior p
==> ?e. e IN edges p
```

编码说明：`edges p = {{v,w} | segment[v,w] edge_of p}`（flyspeck_multivariate.ml:6887）
经私有 `edges_p5` 引用，`edge_of`（polytope.ml:2847：`e face_of s ∧
aff_dim e = &1`）经私有 `edgeOf_p5` 引用；成员关系 `e ∈ edges_p5 p` 已按
集合论展开为 `∃ v w, e = {v,w} ∧ edgeOf_p5 (segment ℝ v w) p` 语义。

证明思路（HOL 结构）：(1) `POLYTOPE_EQ_BOUNDED_POLYHEDRON`：p 是多胞形；
(2) `AFF_DIM_INTERIOR_EQ_3` 得满维；(3) `POLYTOPE_FACET_EXISTS` 两连击：
p 有余维 1 面 `f`（`affDim f = 2`），f 又有余维 1 面 `f'`（`affDim f' = 1`），
且 `f'` 非空；(4) `affDim f' = 1` ⇒ 仿射无关基 `b` 满足 `CARD b = 2`，经
`CARD_EXISTS_2` 写成 `{v, w}`；(5) `FACE_OF_TRANS` 得 `f' face_of p`，故
`e = {v,w}` 见证 `edges_p5 p`。

候选已有引理：
- 本批 `AFF_DIM_INTERIOR_EQ_3`、`CARD_EXISTS_2`
- `POLYTOPE_EQ_BOUNDED_POLYHEDRON`、`POLYTOPE_FACET_EXISTS`、
  `FACE_OF_POLYTOPE_POLYTOPE`、`FACE_OF_TRANS`：HOL polytope.ml /
  flyspeck 库引理，repo 均未移植 → 需补批（fenxi）
- `segment`、`affineSpan`、`Set.ncard`（Mathlib） -/
theorem EXISTS_EDGE_POLYTOPE (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron_p5 p) (hz : (0 : V3) ∈ interior p) :
    ∃ e : Set V3, e ∈ edges_p5 p := by
  sorry

end Kepler.Text
