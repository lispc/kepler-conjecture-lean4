/-
Port of the HOL Light Flyspeck `polyhedron.hl` top-level theorems, batch 3
(polyhedron.hl:283-569).

Source: `reference/flyspeck/text_formalization/fan/polyhedron.hl`
(Flyspeck book formalization; persistent copy `lean/scripts/polyhedron.hl`).

Coverage (batch 3 of polyhedron.hl, theorems whose `let = prove` starts in
:283-:569, exactly 10):
- `FAN_TRANSLATION_EQ` (:283)
- `FAN_LINEAR_IMAGE_EQ` (:289)
- `BASE_POINT_FAN_TRANSLATION_EQ` (:298)
- `BASE_POINT_FAN_LINEAR_IMAGE_EQ` (:304)
- `SET_OF_EDGE_TRANSLATION_EQ` (:311)
- `SET_OF_EDGE_LINEAR_IMAGE_EQ` (:318)
- `POLYHEDRON_FAN` (:342)
- `CONVEX_RELATIVE_INTERIOR` (:514)
- `LEMMA` (:517)  [note: this batch OWNS the HOL name `LEMMA`; a later
  batch's `LEMMA` (polyhedron.hl:858) is to be renamed, not this one]
- `CONVEX_RELATIVE_INTERIOR_FACE` (:561)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL `((real^3->bool)->bool)` ↔
  `Set (Set V3)`.
- HOL `FAN` ↔ `FAN` (Kepler/Text/Fan.lean:56); HOL `set_of_edge` ↔
  `setOfEdge` (Kepler/Text/Fan.lean:62).
- HOL `IMAGE (IMAGE (\x. a + x)) E` ↔
  `(fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E`; HOL
  `IMAGE f E` (E a set of sets) ↔ `(fun s : Set V3 => f '' s) '' E`.
- HOL `linear f /\ (!x y. f x = f y ==> x = y)` for `f : real^3 -> real^3`
  is encoded by taking `f : V3 →ₗ[ℝ] V3` (the linearity hypothesis is
  absorbed into the type) plus `Function.Injective f`.
- HOL `base_point_fan (x,V,E) = x` (fan/fan.hl:67) is NOT ported as a
  definition; it is inlined by its defining formula on both sides of the
  two `BASE_POINT_FAN_*` statements (which therefore degenerate to point
  identities; the unused `V`/`E` arguments are kept for signature
  fidelity).
- HOL `polyhedron s` (hol-light Multivariate/polytope.ml:4385:
  `?f. FINITE f /\ s = INTERS f /\ (!h. h IN f ==> ?a b. ~(a = vec 0) /\
  h = {x | a dot x <= b})`) has no Lean counterpart in the repo; it is
  INLINED verbatim as
  `∃ f : Set (Set V3), f.Finite ∧ s = ⋂₀ f ∧ ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ,
  a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b}` in the three polyhedron theorems.
- HOL `relative_interior s` (IN_RELATIVE_INTERIOR, flyspeck.ml) maps to
  Mathlib's intrinsic interior `intrinsicInterior ℝ s`
  (Mathlib/Analysis/Convex/Intrinsic.lean:61, the `affineSpan`-based
  relative interior); no new definition is introduced.
- HOL `vertices s = {x | x extreme_point_of s}` (flyspeck_multivariate.ml
  :6884) is inlined as `Set.extremePoints ℝ p`
  (Mathlib/Analysis/Convex/Extreme.lean:68; `mem_extremePoints` matches
  the HOL open-segment formulation).
- HOL `face_of` (polytope.ml:13, `t SUBSET s /\ convex t /\ !a b x.
  a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t`,
  with HOL `segment(a,b)` the OPEN segment) and HOL `edge_of`
  (polytope.ml:2847, `e face_of s /\ aff_dim e = &1`) are inlined; the
  affine-dimension condition `aff_dim (segment[v,w]) = &1` is encoded by
  its segment-equivalent `v ≠ w` (this Mathlib v4.32.2 has no affine
  dimension API); HOL open `segment(a,b)` ↔ `openSegment ℝ a b`, HOL
  closed `segment[v,w]` ↔ `segment ℝ v w`.
- HOL `bounded p` ↔ `Bornology.IsBounded p`；HOL `interior p` ↔ `interior p`
  (Mathlib topology); HOL `convex` ↔ `Convex ℝ`; HOL `dot` ↔ `⬝ᵥ`
  (Kepler/Geom/Azim.lean:40); HOL `INTERS {g y | y IN f}` ↔ `⋂ y ∈ f, g y`
  (`Set.iInter`, repo convention cf. ConformingDefs.lean header).
- This file imports `Mathlib` (in addition to the PlanarityAuto16 +
  ConformingDefs chain) because `intrinsicInterior`, `Set.extremePoints`,
  `segment`/`openSegment` and `interior` are not reachable from those
  Kepler imports alone.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 平移与线性像不变性（polyhedron.hl:283-339） -/

/-- HOL polyhedron.hl :283-288 `FAN_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
     FAN(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
     FAN(x,V,E)
```

编码说明：HOL `FAN` ↔ `FAN`（Kepler/Text/Fan.lean:56）；`IMAGE (IMAGE
(\x. a + x)) E` 编码为 `(fun s => (fun y : V3 => a + y) '' s) '' E`。

证明思路：按 `FAN` 的六个合取项（`⋃₀ E ⊆ V`、`Graph E`、`fan1`、`fan2`、
`fan6`、`fan7`）逐一化简；平移不改变 `Collinear`、`affGe` 与集合基数，
用 `Set.image_pair`-型恒等式与 `collinear`/`affGe` 的平移不变性收口。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `affGe`（Kepler/Geom/Aff.lean:42）、`Collinear3`（Kepler/Geom/Azim.lean:43）
- 缺口：`fan7` 平移不变性（`affGe` 的平移等变）repo 无现成引理 -/
theorem FAN_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN (a + x) ((fun y : V3 => a + y) '' V)
        ((fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E) ↔
      FAN x V E := by
  sorry

/-- HOL polyhedron.hl :289-297 `FAN_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
 linear f /\ (!x y. f x = f y ==> x = y)
 ==> (FAN(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> FAN(x,V,E))
```

编码说明：`linear f ∧ injective` 编码为 `f : V3 →ₗ[ℝ] V3` +
`Function.Injective f`（线性假设吸收进类型）；`IMAGE (IMAGE f) E` 编码为
`(fun s => f '' s) '' E`。

证明思路：同 `FAN_TRANSLATION_EQ`，逐合取项化简；线性双射保持
`Collinear`、`affGe`（`affGe` 对线性像的等变性）与有限性/非空性。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `Set.image_pair`、`Function.Injective`（Mathlib）
- 缺口：`affGe`/`Collinear` 在可逆线性像下的等变引理 repo 无现成陈述 -/
theorem FAN_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (hf : Function.Injective f) :
    FAN (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) ↔ FAN x V E := by
  sorry

/-- HOL polyhedron.hl :298-303 `BASE_POINT_FAN_TRANSLATION_EQ`

HOL 原文：
```
!a x V E.
  base_point_fan(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) =
  a + base_point_fan(x,V,E)
```

编码说明（缺口）：HOL `base_point_fan (x,V,E) = x`（fan/fan.hl:67）未
移植，按定义式在两边就地展开：左边展开为 `a + x`，右边为 `a + x`，陈述
退化为点的恒等式；`V`、`E` 仅为保持 HOL 签名（无实际约束）。

证明思路：定义式展开后即 `a + x = a + x`（`rfl` 量级的平凡恒等式）。

候选已有引理：
- `base_point_fan` 定义 fan/fan.hl:67（未移植，就地展开）
- `add_self`/`rfl`（Lean 核心） -/
theorem BASE_POINT_FAN_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    a + x = a + x := by
  sorry

/-- HOL polyhedron.hl :304-310 `BASE_POINT_FAN_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
      linear f
      ==> base_point_fan(f x,IMAGE f V,IMAGE (IMAGE f) E) =
          f(base_point_fan(x,V,E))
```

编码说明（缺口）：HOL `base_point_fan (x,V,E) = x`（fan/fan.hl:67）未
移植，按定义式在两边就地展开：左边展开为 `f x`，右边为 `f x`；HOL
`linear f` 由 `f : V3 →ₗ[ℝ] V3` 的类型吸收，陈述退化为点的恒等式；
`V`、`E` 仅为保持 HOL 签名。

证明思路：定义式展开后即 `f x = f x`（`rfl` 量级）。

候选已有引理：
- `base_point_fan` 定义 fan/fan.hl:67（未移植，就地展开）
- `rfl`（Lean 核心） -/
theorem BASE_POINT_FAN_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) : f x = f x := by
  sorry

/-- HOL polyhedron.hl :311-317 `SET_OF_EDGE_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
      set_of_edge (a + x) (IMAGE (\x. a + x) V)
                  (IMAGE (IMAGE (\x. a + x)) E) =
      IMAGE (\x. a + x) (set_of_edge x V E)
```

编码说明：HOL `set_of_edge` ↔ `setOfEdge`（Kepler/Text/Fan.lean:62：
`{w | {v, w} ∈ E ∧ w ∈ V}`）。

证明思路：`setOfEdge` 按定义展开后，两边均为
`{w | w ∈ (a + ·) '' V ∧ {a + x, a + w} ∈ (a + ·) '' (a + ·) '' E}`-型
集合；用 `Set.mem_image`、`Set.image_image` 与加法消去
（`(a + u = a + v) ↔ u = v`）收口。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_image`、`Set.image_image`、`Set.ext_iff`（Mathlib）
- `V3` 的 `add_right_cancel`（Mathlib） -/
theorem SET_OF_EDGE_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    setOfEdge (a + x) ((fun y : V3 => a + y) '' V)
        ((fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E) =
      (fun y : V3 => a + y) '' (setOfEdge x V E) := by
  sorry

/-- HOL polyhedron.hl :318-339 `SET_OF_EDGE_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> set_of_edge (f x) (IMAGE f V) (IMAGE (IMAGE f) E) =
          IMAGE f (set_of_edge x V E)
```

编码说明：`linear f ∧ injective` 编码为 `f : V3 →ₗ[ℝ] V3` +
`Function.Injective f`；`set_of_edge` ↔ `setOfEdge`
（Kepler/Text/Fan.lean:62）。

证明思路：`setOfEdge` 展开后用 `Set.mem_image` 拆两边；`f` 单射给出
`{f v, f w} ∈ ...` 与 `{v, w} ∈ ...` 的相互转移（`Set.mem_image` +
`map_le_map_iff`-型单射参数），其余为集合演算。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_image`、`Set.image_image`、`Set.image_congr`（Mathlib）
- `LinearMap.injective` 应用场景 `Set.injOn_of_injective`-族（Mathlib） -/
theorem SET_OF_EDGE_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (hf : Function.Injective f) :
    setOfEdge (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) =
      f '' (setOfEdge x V E) := by
  sorry

/-! ## 多面体导出扇（polyhedron.hl:342-513） -/

/-- HOL polyhedron.hl :342-513 `POLYHEDRON_FAN`

HOL 原文：
```
!p z:real^3.
    bounded p /\ polyhedron p /\ z IN interior p
    ==> FAN(z,vertices p,edges p)
```

编码说明（缺口）：HOL `polyhedron p`（polytope.ml:4385）、`vertices p`
（flyspeck_multivariate.ml:6884）、`edges p`（:6887）、`face_of`
（polytope.ml:13，开 `segment(a,b)`）均未移植，全部按定义式就地展开；
`aff_dim (segment[v,w]) = &1`（`edge_of` 条件）以段上等价条件 `v ≠ w`
编码（本 Mathlib 无仿射维数 API）；`relative_interior` 见批头说明。
因此结论为 `FAN z (Set.extremePoints ℝ p) {e | ∃ v w, e = {v, w} ∧
v ≠ w ∧ face_of 条件(内联)}`。

证明思路（HOL 六合取项）：(1) `⋃₀ E ⊆ vertices p`：`edge_of ⊆ vertices`
经 `face_of` 传递性与 `EXTREME_POINT_OF_SEGMENT`；(2) `Graph E`：边由
`v ≠ w` 保证基数 2；(3) `fan1`：`FINITE_POLYHEDRON_EXTREME_POINTS` +
`EXTREME_POINT_EXISTS_CONVEX`（紧凸集有极值点）；(4) `fan2`：
`EXTREME_POINT_NOT_IN_INTERIOR`；(5) `fan6`：设 `{x,v,w}` 共线导出
`t % v` 型内点矛盾（`FACE_OF_DISJOINT_INTERIOR` +
`POLYHEDRON_COLLINEAR_FACES`）；(6) `fan7`：内联引理（两条 `face_of` 段
要么重合要么交于端点并）+ `AFF_GE_0_CONVEX_HULL_ALT` 与
`POLYHEDRON_COLLINEAR_FACES`。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `Set.extremePoints`、`mem_extremePoints`（Mathlib Analysis/Convex/Extreme.lean:68,133）
- `segment`、`openSegment`、`convex_segment`（Mathlib Analysis/Convex/Segment.lean）
- `IsBounded`（Mathlib Topology/Bornology/Basic.lean:99；HOL `bounded`）、
  `interior`、`interior_subset`（Mathlib）
- 缺口：`POLYHEDRON_COLLINEAR_FACES`、`EXTREME_POINT_EXISTS_CONVEX`、
  `FACE_OF_DISJOINT_INTERIOR` 等上游引理 repo 均未移植 -/
theorem POLYHEDRON_FAN {p : Set V3} {z : V3} (hb : Bornology.IsBounded p)
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hz : z ∈ interior p) :
    FAN z (Set.extremePoints ℝ p)
      {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
        segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
        ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
          y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w} := by
  sorry

/-! ## 相对内部的凸性（polyhedron.hl:514-569，Truong 添加部分） -/

/-- HOL polyhedron.hl :514-516 `CONVEX_RELATIVE_INTERIOR`

HOL 原文：
```
!p:real^3->bool. polyhedron p ==> convex (relative_interior p)
```

编码说明（缺口）：HOL `polyhedron p` 就地展开（见批头）；HOL
`relative_interior p` ↔ `intrinsicInterior ℝ p`
（Mathlib Analysis/Convex/Intrinsic.lean:61）。

证明思路（HOL）：由 `POLYHEDRON_INTER_AFFINE_MINIMAL` 取 `p =
affine hull p ∩ ⋂ f`，用 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT` 得
`relative_interior p = p ∩ {x | ∀ h ∈ f, a h ⬝ x < b h}`，再
`CONVEX_INTER`（`p` 凸：`POLYHEDRON_EQ_FINITE_FACES`）+ `CONVEX_INTERS`
+ `LEMMA`（本文件）+ `CONVEX_HALFSPACE_LT`。

候选已有引理：
- `intrinsicInterior ℝ`（Mathlib Analysis/Convex/Intrinsic.lean:61）
- `Convex.inter`、`convex_iInter`-型、`Convex.halfspace_lt`（Mathlib：
  `convex_halfspace_lt`）
- `LEMMA`（本文件 PolyAuto3.lean）
- 缺口：`RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`、
  `POLYHEDRON_INTER_AFFINE_MINIMAL` 未移植 -/
theorem CONVEX_RELATIVE_INTERIOR {p : Set V3}
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b}) :
    Convex ℝ (intrinsicInterior ℝ p) := by
  sorry

/-- HOL polyhedron.hl :517-560 `LEMMA`

HOL 原文：
```
!f:(real^3->bool)->bool (a:(real^3->bool)->real^3) (b:(real^3->bool)->real).
{x | !h. h IN f ==> a h dot x < b h} = INTERS{{x | a h dot x < b h}| h IN f}
```

（本批独占 HOL 名 `LEMMA`；后一批的同名 `LEMMA`（polyhedron.hl:858）
届时改名，非本批职责。）

编码说明：纯集合论恒等式；`INTERS {g h | h ∈ f}` ↔ `⋂ h ∈ f, g h`
（repo 约定）；`dot` ↔ `⬝ᵥ`。

证明思路：`Set.ext_iff` + `mem_iInter`：左边逐点语句
`x ∈ {x | ∀ h ∈ f, ...}` 与右边逐 h 交成员互推（每步取 `h` 作见证，
`⟨h, hf, rfl⟩` 型收口）。

候选已有引理：
- `Set.ext_iff`、`Set.mem_iInter`、`Set.mem_setOf_eq`（Mathlib） -/
theorem LEMMA (f : Set (Set V3)) (a : Set V3 → V3) (b : Set V3 → ℝ) :
    {x : V3 | ∀ h : Set V3, h ∈ f → a h ⬝ᵥ x < b h} =
      ⋂ h ∈ f, {x : V3 | a h ⬝ᵥ x < b h} := by
  sorry

/-- HOL polyhedron.hl :561-566 `CONVEX_RELATIVE_INTERIOR_FACE`

HOL 原文：
```
!p f:(real^3->bool). polyhedron p /\ f face_of p
==> convex (relative_interior f)
```

编码说明（缺口）：HOL `polyhedron p` 与 `face_of`（polytope.ml:13，
开 `segment(a,b)`）均未移植，按定义式就地展开；`relative_interior` ↔
`intrinsicInterior ℝ p`。

证明思路（HOL）：`FACE_OF_POLYHEDRON_POLYHEDRON`（面的多项式性，HOL
polytope.ml:5278）把 `face_of p` 转成 `polyhedron f`，再用本文件
`CONVEX_RELATIVE_INTERIOR`。

候选已有引理：
- `CONVEX_RELATIVE_INTERIOR`（本文件 PolyAuto3.lean）
- `intrinsicInterior ℝ`（Mathlib Analysis/Convex/Intrinsic.lean:61）
- 缺口：`FACE_OF_POLYHEDRON_POLYHEDRON` 未移植 -/
theorem CONVEX_RELATIVE_INTERIOR_FACE {p f : Set V3}
    (hp : ∃ g : Set (Set V3), g.Finite ∧ p = ⋂₀ g ∧
      ∀ h ∈ g, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hf : f ⊆ p ∧ Convex ℝ f ∧
      ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ f →
        y ∈ openSegment ℝ c d → c ∈ f ∧ d ∈ f) :
    Convex ℝ (intrinsicInterior ℝ f) := by
  sorry

end Kepler.Text
