/-
Port of the HOL Light Flyspeck polyhedron theory (Packing chapter), slice 7
(FINAL batch): skeleton pass of `scripts/polyhedron.hl` :1823-:3200 — the
theorems whose `let ... = prove` starts in :1823-:3200, exactly 10.

Source: `lean/scripts/polyhedron.hl` (persistent copy of Flyspeck book
formalization `text_formalization/packing/polyhedron.hl`, John Harrison +
Hoang Le Truong, 2010-2011).

Coverage (batch 7, FINAL):
- `SUR_FCHANGED` (:1823)
- `AMHFNXP` (:1855)
- `AMHFNXP_BIJ` (:1875)
- `EXPAND_EDGE_POLYTOPE` (:1893)
- `EXISTS_EDGE_AT_VERTICES` (:1932)
- `FLVNSME` (:2005-:2995, batch centerpiece — the file's ~1000-line giant:
  every vertex lies on an edge reaching into the open halfspace opposite
  the facet normal)
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON` (:2996)
- `BSXAQBQ` (:3028)
- `POLYTOPE_FAN80` (:3090)
- `WBLARHH` (:3158)
Not assigned: `WBLARHH_BIJ` (:3189-:3200) is a `prove_by_refinement`
corollary of WBLARHH + `PIIJBJK` (ConformingAuto21.lean:903); it does not
start a `let = prove` in the assigned window and is left to the fill-in
pass of whichever batch owns the WBLARHH proof.

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs are `by sorry`, to be filled by the auto_loop harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  `t % v` ↔ `t • v`; `vec 0` ↔ `(0 : V3)`; `dot` ↔ `⬝ᵥ` (Kepler/Geom/
  Azim.lean:40).
- HOL `relative_interior s` ↔ `intrinsicInterior ℝ s`
  (Mathlib/Analysis/Convex/Intrinsic.lean:61; precedent: PolyAuto4 header).
- HOL `bounded s` ↔ `Bornology.IsBounded s`; HOL `interior` ↔ Mathlib
  `interior`.
- `fchanged` (:512), `polyhedron` (polytope1.ml:2546), `face_of`
  (polytope1.ml:22), `facet_of` (polytope1.ml:1506) and `aff_dim` are
  ported here VERBATIM as private `_p7` copies `fchanged_p7`/
  `polyhedron_p7`/`FaceOf_p7`/`FacetOf_p7`/`affDim_p7` because the
  concurrent batch 3/4 lanes own the public names (PolyAuto3/PolyAuto4 are
  NOT imported: batches are parallel lanes; the bodies are token-identical
  to the polytope1.ml originals). Merge note: when the public copies land,
  delete these `_p7` copies and re-point; nothing else in this file needs
  to change.
- `vertices s = {x | x extreme_point_of s}` (flyspeck_multivariate.ml:6884)
  is INLINED as `Set.extremePoints ℝ p` (Mathlib Analysis/Convex/
  Extreme.lean:68), following the PolyAuto3 POLYHEDRON_FAN precedent —
  this file's statements share V/E with PolyAuto3.POLYHEDRON_FAN verbatim,
  so the fill-in proofs can instantiate it without bridging.
- `edges s = {{v,w} | segment[v,w] edge_of s}` (flyspeck_multivariate.ml
  :6887) is ported as `edges_p7`: `edge_of` (polytope.ml:2847:
  `e face_of s /\ aff_dim e = &1`) is inlined, the face_of body verbatim
  (PolyAuto3 precedent) and the affine-dimension condition `aff_dim
  (segment[v,w]) = &1` encoded by its segment-equivalent `v ≠ w` (this
  Mathlib has no affine-dimension API on segments; PolyAuto3 made the same
  call inside POLYHEDRON_FAN).
- HOL `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); `set_of_edge` ↔ `setOfEdge` (Fan.lean:62);
  `azim_fan` ↔ `azimFan` (Fan.lean:177); `fan80` ↔ `fan80` (Fan.lean:227);
  `FAN` ↔ `FAN` (Fan.lean:56); `CARD s > 1` ↔ `1 < s.ncard`.
- HOL `d_fan (x,V,E) = d1_fan ∪ d20_fan` (fan.hl:2302) ↦ `dartOfFan V E`
  (Fan.lean:90; apex dropped, pair darts — ConformingDefs.lean header
  precedent); `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`.
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `hypermap1_of_fanx
  (x,V,E)` is NOT ported: `face_set (hypermap1_of_fanx ...)` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts, carrying an
  explicit `hfan : FAN x V E` witness (ConformingDefs.lean header
  precedent; the only signature deviation from HOL, affecting WBLARHH).
- HOL `BIJ f s t` (INJ + SURJ) ↔ `Set.BijOn f s t`.
- HOL `?!x. P x` ↔ `∃! x, P x`.
- Imports: `PlanarityAuto16` + `ConformingDefs` per batch plan (the cited
  PlanarityComponent/PlanarityConnect/Fan/ConformingAuto chain rides in
  transitively) plus `Mathlib` for `intrinsicInterior`, `Set.extremePoints`,
  `segment`, `interior`. NO PolyAuto imports (batches 1-6 are concurrent
  lanes; cross-batch dependencies are recorded per theorem below).

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
open Kepler.Text.Fan
open Classical

/-! ## 上游定义私有副本（HOL 原文逐字移植；见文件头「合并去重」说明） -/

/-- HOL `aff_dim`（polytope1.ml，逐字；∅ ↦ -1，否则仿射包方向的维数）。
私有副本：公开名 `affDim` 在并发批 4 lane（PolyAuto4.lean:90），本 lane
不导入 PolyAuto*。 -/
noncomputable def affDim_p7 (s : Set V3) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- HOL `t face_of s`（polytope1.ml:22，flyspeck Definition 4.7 QLITJET）：
```
t SUBSET s /\ convex t /\
!a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t
```
（HOL `segment(a,b)` 为开段 ↦ `openSegment ℝ a b`。）私有副本：公开名
`FaceOf` 在并发批 4 lane（PolyAuto4.lean:99）。 -/
def FaceOf_p7 (t s : Set V3) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : V3, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

/-- HOL `f facet_of s`（polytope1.ml:1506）：
```
f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1
```
私有副本：公开名 `FacetOf` 在并发批 4 lane（PolyAuto4.lean:108）。 -/
def FacetOf_p7 (f s : Set V3) : Prop :=
  FaceOf_p7 f s ∧ f ≠ ∅ ∧ affDim_p7 f = affDim_p7 s - 1

/-- HOL `polyhedron s`（polytope1.ml:2546，flyspeck Definition 4.8 QSRHLXB）：
```
polyhedron s <=> ?f. FINITE f /\ s = INTERS f /\
  (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})
```
私有副本：公开名 `polyhedron` 在并发批 4 lane（PolyAuto4.lean:117）。 -/
def polyhedron_p7 (s : Set V3) : Prop :=
  ∃ F : Set (Set V3), F.Finite ∧ s = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}

/-- HOL `fchanged`（polyhedron.hl:512，`new_definition`，逐字移植）：
```
fchanged f={v| ?v1 t. v=t% v1 /\ v1 IN (relative_interior f)/\ t> &0}
```
即 `f` 相对内部各点出发的正射线之并。私有副本：公开名 `fchanged` 在并发
批 4 lane（PolyAuto4.lean:126，同样逐字移植自 :512）；合并时删一份并
重指。 -/
def fchanged_p7 (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-- HOL `edges s`（flyspeck_multivariate.ml:6887）：
```
edges s = {{v,w} | segment[v,w] edge_of s}
```
`edge_of`（polytope.ml:2847：`e face_of s /\ aff_dim e = &1`）就地内联：
face_of 条件按 `polytope1.ml:22` 逐字展开（PolyAuto3 POLYHEDRON_FAN 的
E-编码），`aff_dim (segment[v,w]) = &1` 以段上等价 `v ≠ w` 编码（本
Mathlib 无仿射维数 API；与 POLYHEDRON_FAN 完全一致，填充证明可直接
实例化之）。`vertices s`（flyspeck_multivariate.ml:6884）就地内联为
`Set.extremePoints ℝ p`。 -/
def edges_p7 (p : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
    segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
    ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
      y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w}

/-! ## polyhedron.hl :1823-:2004（面的 fchanged-参数化） -/

/-- HOL polyhedron.hl :1823-:1839 `SUR_FCHANGED`

HOL 原文：
```
!s p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p /\
 s IN topological_component_yfan(vec 0:real^3,vertices (p:real^3->bool),edges (p:real^3->bool))
==> ?f. f facet_of p /\ s= fchanged f
```

编码说明：`topological_component_yfan` ↦ `topologicalComponentYfan`
（Kepler/Text/Fan.lean:199）；`vertices`/`edges` 见 `edges_p7` 与批头
（`Set.extremePoints ℝ p`）；`facet_of`/`fchanged` ↦ 本文件私有副本。

证明思路（HOL）：`FCHANGED_EQ_YFAN`（批 6）把 `fchanged` 侧化入
yfan-分量语言；`topological_component_subset_yfan`
（Kepler/Text/PlanarityConnect.lean:189）与
`exists_point_in_component_yfan`（PlanarityConnect.lean:76）取
`z ∈ s ⊆ yfan`；`FCHANGED_IN_COMPONENT`（批 6：每个 facet 的 fchanged
是含 yfan 点的 yfan-连通分量）取 facet `f` 与点 `z ∈ fchanged f`；两个
yfan-连通分量共享 `z`，`CONNECTED_COMPONENT_OVERLAP` 迫使其相等。

候选已有引理：
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `exists_point_in_component_yfan`（Kepler/Text/PlanarityConnect.lean:76）
- `connectedComponentIn_eq`（Mathlib Topology/Connected/Basic.lean:585；
  共享一点的两分量相等，HOL `CONNECTED_COMPONENT_OVERLAP` 的对应物）
- 跨批依赖：`FCHANGED_EQ_YFAN`、`FCHANGED_IN_COMPONENT`（批 6 lane，
  polyhedron.hl :1718-:1822；本 lane 未移植） -/
theorem SUR_FCHANGED {s p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    (hs : s ∈ topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) :
    ∃ f : Set V3, FacetOf_p7 f p ∧ s = fchanged_p7 f := by
  sorry

/-- HOL polyhedron.hl :1855-:1873 `AMHFNXP`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>
(!s. s IN topological_component_yfan (vec 0,vertices (p:real^3->bool),edges (p:real^3->bool)) ==> (?!f. f facet_of p /\
							 s = fchanged f))
```

编码说明：`?!f. P f` ↦ `∃! f, P f`（ConformingDefs.lean 先例）。

证明思路（HOL）：存在性即 `SUR_FCHANGED`；唯一性：设 `s = fchanged f =
fchanged y`，`FCHANGED_ONE_TO_ONE`（批 5，polyhedron.hl :1132：fchanged
单射性）化归为 `fchanged f ∩ fchanged y ≠ ∅`，而
`EXISTS_POINT_IN_FCHANGED`（批 5/6：非空 facet 的 fchanged 含 yfan 点）
+ `SET_TAC` 给出交非空，故 `f = y`。

候选已有引理：
- `SUR_FCHANGED`（本文件上文）
- `Set.BijOn`-侧工具（Mathlib）
- 跨批依赖：`FCHANGED_ONE_TO_ONE`（批 5，polyhedron.hl :1132）、
  `EXISTS_POINT_IN_FCHANGED`（批 5/6 lane；本 lane 未移植） -/
theorem AMHFNXP {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    ∀ s ∈ topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p),
      ∃! f : Set V3, FacetOf_p7 f p ∧ s = fchanged_p7 f := by
  sorry

/-- HOL polyhedron.hl :1875-:1891 `AMHFNXP_BIJ`

HOL 原文：
```
!p:real^3->bool. bounded p /\ polyhedron p /\ vec 0 IN interior p ==>
  (BIJ fchanged (\f. f facet_of p) (topological_component_yfan (vec 0,vertices p,edges p)))
```

编码说明：HOL `BIJ f s t`（INJ + SURJ）↦ `Set.BijOn f s t`；像函数
`\f. f facet_of p` 编码为集合 `{f : Set V3 | FacetOf_p7 f p}`。

证明思路（HOL，prove_by_refinement 原文仅 7 步）：展开 `BIJ/INJ/SURJ`；
`FCHANGED_IN_COMPONENT`（批 6，REWRITE_RULE[IN] 后 SIMP）给出
MapsTo；`AMHFNXP` 的唯一存在性（`EXISTS_UNIQUE` 展开 + ASM_MESON）
同时给出 InjOn 与 SurjOn。

候选已有引理：
- `AMHFNXP`（本文件上文）
- `Set.BijOn`（Mathlib Order/Basic；按 `MapsTo ∧ InjOn ∧ SurjOn` 展开）
- 跨批依赖：`FCHANGED_IN_COMPONENT`（批 6 lane；本 lane 未移植） -/
theorem AMHFNXP_BIJ {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    Set.BijOn (fun f : Set V3 => fchanged_p7 f) {f : Set V3 | FacetOf_p7 f p}
      (topologicalComponentYfan 0 (Set.extremePoints ℝ p) (edges_p7 p)) := by
  sorry

/-! ## polyhedron.hl :1893-:2004（边上的顶点） -/

/-- HOL polyhedron.hl :1893-:1930 `EXPAND_EDGE_POLYTOPE`

HOL 原文（对 `real^N` 一般陈述；本 lane 按仓库惯例特化到 `V3`）：
```
!f p:real^N->bool.
polytope p /\ f face_of p /\ aff_dim f= &1
==> ?a b. f= segment[a,b]
```

编码说明：HOL `polytope p`（`?t. FINITE t /\ p = convex hull t`，见
flyspeck_multivariate.ml:1579 `REWRITE_TAC[polytope]` 的用法）内联为
`∃ t : Set V3, t.Finite ∧ p = convexHull ℝ t`；`face_of`/`aff_dim` ↦
本文件 `FaceOf_p7`/`affDim_p7`；闭段 `segment[a,b]` ↦ `segment ℝ a b`。

证明思路（HOL）：`AFF_DIM f = &1` 给仿射基 `b` 且 `CARD b = 2`
（`AFF_DIM` 展开 + `INT_OF_NUM_EQ`）；`AFFINE_INDEPENDENT_IMP_FINITE` +
`CARD_EXISTS_2` 得 `b = {v,w}`；`FACE_OF_POLYTOPE_POLYTOPE`（面的多胞体
性）+ `POLYTOPE_IMP_COMPACT`/`POLYTOPE_IMP_CONVEX` 后
`f ⊆ affine hull {v,w}`（`HULL_SUBSET`），即 f 共线；最后
`COMPACT_CONVEX_COLLINEAR_SEGMENT`（polytope.ml）给
`f = segment[v,w]`（退化情形 `b = {v}` 由维数算术排除）。

候选已有引理：
- `FaceOf_p7`（本文件，展开即 `f ⊆ p`、`Convex ℝ f`）
- `convexHull`（Mathlib Analysis/Convex/Basic）
- 缺口：`AFF_DIM`-类展开、`COMPACT_CONVEX_COLLINEAR_SEGMENT`
  （「紧凸共线集是（可退化）段」）repo/Mathlib 均无现成引理；
  Mathlib 侧可由 `vectorSpan` 维数分类 + `segment` 的凸包刻画
  `convexHull_two` 重建 -/
theorem EXPAND_EDGE_POLYTOPE {f p : Set V3}
    (hp : ∃ t : Set V3, t.Finite ∧ p = convexHull ℝ t)
    (hf : FaceOf_p7 f p) (hdim : affDim_p7 f = 1) :
    ∃ a b : V3, f = segment ℝ a b := by
  sorry

/-- HOL polyhedron.hl :1932-:2003 `EXISTS_EDGE_AT_VERTICES`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>  (!v. v IN vertices p ==> ~(set_of_edge v (vertices p) (edges p) ={}) )
```

编码说明：`vertices p` ↦ `Set.extremePoints ℝ p`；
`~(s = {})` ↦ `s ≠ ∅`；`set_of_edge` ↦ `setOfEdge`
（Kepler/Text/Fan.lean:62）；`edges p` ↦ `edges_p7`（本文件）。

证明思路（HOL）：`vertices` 展开 + `GSYM FACE_OF_SING` 把 `v ∈ vertices p`
写成 `{v} face_of p`；`AFF_DIM_SING` + `AFF_DIM_INTERIOR_EQ_3`（含内点的
有界多面体维数 3，未移植）排除 `p = {v}`；`FACE_OF_POLYHEDRON_SUBSET_FACET`
（未移植）把 `{v}` 嵌入 facet `f`；`EXTREME_POINT_OF_FACE` 传递极点性，
`FACE_OF_POLYHEDRON_POLYHEDRON` 保持多面体性；再降一维取 `f` 的过 `v`
facet `f'`（`AFF_DIM f = 2`），`EXPAND_EDGE_POLYTOPE` 给
`f' = segment[a,b]`，`EXTREME_POINT_OF_SEGMENT` 得 `v ∈ {a,b}`；
`SEGMENT_EDGE_OF`（segment[a,b] edge_of p）把 `{a,b}` 送入 `edges p`，
取异于 `v` 的端点为 `w`，`setOfEdge` 展开收口。

候选已有引理：
- `Set.extremePoints`、`mem_extremePoints`（Mathlib Analysis/Convex/Extreme.lean:68,133）
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `EXPAND_EDGE_POLYTOPE`（本文件上文）
- 缺口：`AFF_DIM_INTERIOR_EQ_3`、`FACE_OF_POLYHEDRON_SUBSET_FACET`、
  `EXTREME_POINT_OF_FACE`、`EXTREME_POINT_OF_SEGMENT`、`SEGMENT_EDGE_OF`
  等上游面论引理 repo 未移植（Mathlib 有 `Set.extremePoints` 的段刻画
  与 `IsExtremePoint` 传递性可部分重建） -/
theorem EXISTS_EDGE_AT_VERTICES {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    ∀ v ∈ Set.extremePoints ℝ p,
      setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p) ≠ ∅ := by
  sorry

/-! ## polyhedron.hl :2005-:2995（FLVNSME，本批主菜） -/

/-- HOL polyhedron.hl :2005-:2995 `FLVNSME`（HOL 文件最大证明块，约
1000 行）

HOL 原文：
```
!v A a b p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
 /\ A={x| a dot x < b } /\ ~(a= vec 0)
/\ v IN {x| a dot x = b } /\ vec 0 IN {x| a dot x = b }
/\ v IN vertices p
==> ?w. w IN vertices p /\ w IN A/\ {v,w} IN edges p
```

几何含义：过顶点 `v` 的支撑超平面 `{a·x = b}`（原点也在其上）是某个
facet 的所在平面；从 `v` 出发必有一条（真）边 `≥v,w≥` 深入开半空间
`A = {a·x < b}`。

编码说明：`vertices p` ↦ `Set.extremePoints ℝ p`、`edges p` ↦
`edges_p7`（本文件）；`A`/`v`/`a`/`b`/`p` 保持显式参数（HOL 全称；
`A` 的定义式作为假设 `hA` 冻结）。

证明思路（HOL 原证按本 lane 采样复述——窗口 :2005-:2104 全读、
:2104-:2136 / :2215-:2330 / :2400-:2520 / :2560-:2680 采样、
:2890-:2995 全读；六个阶段）：

1. **setup（:2005-:2104）**：`vertices` 展开 + `GSYM FACE_OF_SING` 得
   `{v} face_of p`；`AFF_DIM_SING` + `AFF_DIM_INTERIOR_EQ_3` 排除
   `p = {v}`；`FACE_OF_POLYHEDRON_SUBSET_FACET` + `EXPOSED_FACE_OF_
   POLYHEDRON` 取过 `v` 的暴露 facet `f = p ∩ {a'·x = b'}`；令
   `s = {--a'·w | w ∈ vertices p, w ≠ v}`，由 `EXISTS_EDGE_AT_VERTICES`
   于 `v` 知其非空，`FINITE_IMAGE` 知其有限；内引理（`INF_FINITE`）取
   最小元 `--a''`；若 `--a'' ≥ b'` 则 `a'·w = b'`，由 facet 等式
   `{v} = p ∩ {a'·x = b'}` 迫 `w = v`，矛盾，故 `--a'' < b'`；
   `INTERIOR_SUBSET` 给 `0 ≤ b'`。
2. **归一化（:2104-:2136）**：`b' = 0` 迫 `v = vec 0`，与
   `EXTREME_POINT_NOT_IN_INTERIOR` 矛盾，故 `0 < b'`；取
   `b1 = max(--a'',0) + (b'-max(--a'',0))/2`，有 `--a'' < b1 < b'`、
   `0 < b1`；证明 `vertices p ∩ {a'·x ≥ b1} = {v}`；令
   `p' = p ∩ {a'·x = b1}`；`OPEN_HALFSPACE_LT` + `IN_INTERIOR` +
   `CLOSURE_HALFSPACE_LT` + `CLOSURE_APPROACHABLE` 在
   `ball(0, min e e'/2)` 内取 `y ∈ interior p ∩ A`（`0 < a·y < b`）。
3. **截线（:2215-:2330）**：显式参数
   `t = inv(a'·v - a'·y)·(b1 - a'·y) ∈ (0,1)` 给
   `z ∈ segment[y,v] ∩ {a'·x = b1} ∧ z ≠ v`；`POLYHEDRON_IMP_CONVEX` +
   `SUBSET_HULL` + `SEGMENT_CONVEX_HULL` 给 `segment[y,v] ⊆ p`；
   `CONVEX_HALFSPACE_LE` 给 `segment[v,y] ⊆ {a·x ≤ b}`，由 `z ≠ v` 分支
   得 `a·z < b`，即 `z ∈ A`。
4. **暴露面下潜（:2330-:2560，采样 :2400-:2520）**：`p1 :=
   p ∩ {a'·x ≥ b1}`（凸紧），`FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
   + `EXPOSED_FACE_OF_POLYHEDRON` 两次下潜取 `{w} = p' ∩ {a'''·x =
   b''}`；令 `a2 = (v-w) × (a''' × a')`、`b2 = a2·w`，
   `CROSS_LADD`/`CROSS_LAGRANGE`/`DOT_*` 系数簿记证明
   `{a'·x = b1} ∩ {a'''·x ≤ b''} = {a'·x = b1} ∩ {a2·x ≤ b2}`（= 变体
   同理），关键用 `0 < b'-b1` 乘开 `REAL_LE_MUL`。
5. **重心迁移（:2560-:2890，采样 :2560-:2680）**：`KREIN_MILMAN_
   MINKOWSKI`（`GSYM vertices`）把 `v` 写成有限 `s' ⊆ vertices p` 上的
   凸组合 `Σ u(x)%x`；`s1 = s' \ {v}`，`SUM_DELETE_CASES`/
   `VSUM_DELETE_CASES` + `SUM_POS_EQ_0`/`VSUM_EQ_0` 处理 `t12 = 0` 分支；
   重权 `inv t12 % v12 ∈ p`（凸组合系数非负）、
   `a'·(inv t12 % v12) ≤ b1`（逐点 `a'·x < b1` 求和）、
   `inv t12 % v12 ≠ v`；`AFF_GE_1_1` + 显式系数（`t1 - t2·inv t12·u v`
   等）证 `aff_ge {v}{inv t12 % v12} = aff_ge {v}{w}`。
6. **收口（:2890-:2995）**：`aff_ge {v}{w} ⊆ {a2·x = b2}`（AFF_GE_1_1 +
   点积线性）；由 4 的等式得 `p ∩ {a2·x = b2} ⊆ aff_ge {v}{w}`；
   `POLYTOPE_IMP_COMPACT` + `HALFLINE_INTER_COMPACT_SEGMENT` 给
   `p ∩ {a2·x = b2} = segment[v,c]`；`FACE_OF_INTER_SUPPORTING_
   HYPERPLANE_LE_STRONG` + `SEGMENT_FACE_OF` 使其为 `p` 的面；
   `w ∈ segment[v,c]`、`w ≠ v` ⇒ `v ≠ c`（`SEGMENT_EQ_SING`）；取见证
   `w ∈ A`（`t2 > 0` 时 `REAL_LT_LMUL`），最后 `{v,c} IN edges p` 由
   `edge_of` 内联 + `AFFINE_HULL_SEGMENT` + `AFF_DIM_2` 收口。

候选已有引理：
- `EXISTS_EDGE_AT_VERTICES`（本文件上文；阶段 1 非空性）
- `segment`/`openSegment`/`convex_segment`（Mathlib Analysis/Convex/Segment）
- `isOpen_halfspace_lt`、`closure_halfspace_lt`-类（Mathlib
  Analysis/Convex/ Halfspace；对应 `OPEN/CLOSURE_HALFSPACE_LT`）、
  `Metric.ball`、`interior`（Mathlib）
- `Convex ℝ`、`convexHull`（Mathlib；对应 `SUBSET_HULL`/
  `SEGMENT_CONVEX_HULL`、`KREIN_MILMAN_MINKOWSKI`）
- 缺口（上游未移植，填充时需先建）：`AFF_DIM_INTERIOR_EQ_3`、
  `FACE_OF_POLYHEDRON_SUBSET_FACET`、`EXPOSED_FACE_OF_POLYHEDRON`、
  `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE/LE_STRONG`、
  `HALFLINE_INTER_COMPACT_SEGMENT`、`SEGMENT_FACE_OF`、
  `SEGMENT_EQ_SING`、`EXTREME_POINT_NOT_IN_INTERIOR`、
  `KREIN_MILMAN_MINKOWSKI`、`SUM_DELETE_CASES`/`VSUM_DELETE_CASES` -/
theorem FLVNSME {v : V3} {A : Set V3} {a : V3} {b : ℝ} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p)
    (hz : (0 : V3) ∈ interior p) (hA : A = {x : V3 | a ⬝ᵥ x < b})
    (ha : a ≠ 0) (hv : v ∈ {x : V3 | a ⬝ᵥ x = b})
    (h0 : (0 : V3) ∈ {x : V3 | a ⬝ᵥ x = b})
    (hv' : v ∈ Set.extremePoints ℝ p) :
    ∃ w : V3, w ∈ Set.extremePoints ℝ p ∧ w ∈ A ∧ {v, w} ∈ edges_p7 p := by
  sorry

/-! ## polyhedron.hl :2996-:3200（fan 性质与 conforming 桥） -/

/-- HOL polyhedron.hl :2996-:3026 `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>  (!v. v IN vertices p ==>CARD (set_of_edge v (vertices p) (edges p)) >1)
```

编码说明：`CARD s > 1` ↔ `1 < s.ncard`（ConformingDefs.lean 头先例，
无限集 ncard = 0 约定与 HOL 有限性前提相容）。

证明思路（HOL）：`EXISTS_EDGE_AT_VERTICES` 给一个邻居 `w`；
`POLYHEDRON_FAN`（Kepler/Text/PolyAuto3.lean:279，签名与本文件 V/E 编码
逐字一致）得 fan 结构；`remark1_fan`（fan.hl，未移植）+ `properties_
coordinate`（fan.hl，未移植）取 `v,w` 处标准正交基
`e1_fan/e2_fan/e3_fan`（↦ `e1Fan/e2Fan/e3Fan`，Kepler/Text/TopologyFan
.lean:2268-2272，`orthonormal_e1Fan_e2Fan_e3Fan` :3499）并以
`a = e2_fan 0 v w` 实例化 `FLVNSME`（`A = {x | a·x < 0}`，
`DOT_RZERO`）；得 `w'` 顶点、`a·w' < 0`、`{v,w'} ∈ edges p`；
`w' ≠ w`（否则 `0 < a·w` 与 `< 0` 矛盾，`ONCE_REWRITE_TAC[DOT_SYM]`）；
`{w,w'} ⊆ setOfEdge v V E` + `CARD_SUBSET` + `CARD_2_FAN`
（Kepler/Text/Planarity.lean:4975）给 `CARD ≥ 2 > 1`。

候选已有引理：
- `EXISTS_EDGE_AT_VERTICES`、`FLVNSME`（本文件上文）
- `POLYHEDRON_FAN`（Kepler/Text/PolyAuto3.lean:279；跨批依赖，签名兼容）
- `e1Fan`/`e2Fan`/`e3Fan`、`orthonormal_e1Fan_e2Fan_e3Fan`、
  `ORTHONORMAL`-非零（Kepler/Text/TopologyFan.lean:2268-2272,3499）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975）、`Set.ncard_le`/
  `ncard_mono`（Mathlib；对应 `CARD_SUBSET`）
- 缺口：`remark1_fan`、`properties_coordinate`（fan.hl）未移植 -/
theorem CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron_p7 p)
    (hz : (0 : V3) ∈ interior p) :
    ∀ v ∈ Set.extremePoints ℝ p,
      1 < (setOfEdge v (Set.extremePoints ℝ p) (edges_p7 p)).ncard := by
  sorry

/-- HOL polyhedron.hl :3028-:3088 `BSXAQBQ`

HOL 原文：
```
!p:real^3->bool x.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
/\ x IN d_fan((vec 0),(vertices p),(edges p))
==> azim_fan (vec 0) (vertices p) (edges p) (pr2 x) (pr3 x) < pi
```

编码说明：`d_fan` ↦ `dartOfFan V E`（Fan.lean:90，apex 丢弃、二元组
dart，ConformingDefs.lean 头先例）；`pr2 x`/`pr3 x` ↦ `x.1`/`x.2`；
`azim_fan` ↦ `azimFan`（Fan.lean:177）。

证明思路（HOL）：`CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`（LABEL_TAC "LINH"）
+ `POLYHEDRON_FAN` + `dartset_fully_surrounded_is_non_isolated_fan`
（↦ `dartOfFan_eq_dart1_of_surrounded`，Kepler/Text/Fan.lean:1084，把
`d_fan` 化为 `d1_fan`，即 `x = (v,w)`、`{v,w} ∈ E`）；`remark1_fan` +
`FLVNSME`（`a = v × w` 的反向、`b = 0`）取 `w'`：
`--(v×w)·w' < 0` 即 `(v×w)·w' > 0`；`w' = w` 时 `DOT_CROSS_SELF`
（`CROSS_EQ_0`）矛盾；否则 `SIGMA_FAN`（Fan.lean:317）取
`σ_fan v w`-邻域内 `azim` 极小者，`JBDNJJB`（Kepler/Text/Planarity
.lean:2702）给 `t·(a·w') > 0` 型正性，`azim < 2π` 分支用
`SIN_POS_PI_LE`（`SIN_SUB`/`SIN_PI`/`COS_PI` 簿记）排除
`azim - π ≥ 0`。

候选已有引理：
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`（本文件上文）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`azimFan`（Fan.lean:177）
- `JBDNJJB`（Kepler/Text/Planarity.lean:2702）
- `Real.sin_sub`、`Real.sin_pi`、`Real.cos_pi`（Mathlib）
- 缺口：`remark1_fan`（fan.hl）未移植 -/
theorem BSXAQBQ {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) {x : V3 × V3}
    (hx : x ∈ dartOfFan (Set.extremePoints ℝ p) (edges_p7 p)) :
    azimFan 0 (Set.extremePoints ℝ p) (edges_p7 p) x.1 x.2 < Real.pi := by
  sorry

/-- HOL polyhedron.hl :3090-:3156 `POLYTOPE_FAN80`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==> fan80 (vec 0,vertices p,edges p)
```

编码说明：`fan80` ↦ `fan80`（Kepler/Text/Fan.lean:227）。

证明思路（HOL）：与 `BSXAQBQ` 孪生（差异仅在方向 `a = v × u` 与收口多
一层 σ-传递）：展开 `fan80` 后对 `{v,u} ∈ E`；`CARD_SET_OF_EDGE_INEQ_1_
POLYHEDRON` + `POLYHEDRON_FAN` + `remark1_fan`；`FLVNSME`（`a = --(v×u)`、
`b = 0`）给 `w`：`(v×u)·w > 0` 且 `{v,w} ∈ E`；`u = w` 由
`DOT_CROSS_SELF` 排除；`SIGMA_FAN` + `JBDNJJB` + `REAL_LT_MUL` 得
`azim 0 v u w < 2π` 的上界，`SIN_POS_PI_LE` 分支排除 `azim ≥ π`；
再由 `azim 0 v u σ ≤ azim 0 v u w < π`（σ 的极小性）与
`UNIQUE_AZIM_0_POINT_FAN`（↦ `unique_azim0_point_fan`，
Kepler/Text/Fan.lean:456）收口 `0 < azim 0 v u σ < π`。

候选已有引理：
- `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`、`FLVNSME`（本文件上文）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`sigmaFan`（Fan.lean:66）
- `unique_azim0_point_fan`（Kepler/Text/Fan.lean:456）
- `JBDNJJB`（Kepler/Text/Planarity.lean:2702）
- `azim` 基础（Kepler/Geom/Azim.lean）
- 缺口：`remark1_fan`（fan.hl）未移植 -/
theorem POLYTOPE_FAN80 {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p) :
    fan80 0 (Set.extremePoints ℝ p) (edges_p7 p) := by
  sorry

/-- HOL polyhedron.hl :3158-:3187 `WBLARHH`

HOL 原文：
```
!p:real^3->bool.
         bounded p /\ polyhedron p /\ vec 0 IN interior p
==>
 (!f. f IN face_set (hypermap1_of_fanx  (vec 0,vertices p,edges p)) ==> (?!f1. f1 facet_of p /\
							 dartset_leads_into_fan (vec 0) (vertices p) (edges p) f = fchanged f1))
```

编码说明：`hypermap1_of_fanx` 未移植——`face_set` 编码为
`(hypermapOfFan 0 V E hfan).faceSet`（pair darts），按 ConformingDefs
头先例携带显式 `hfan : FAN 0 V E` 见证（唯一签名偏差）；`f` 类型为
`Set (V3 × V3)`；`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`
（Kepler/Text/PlanarityComponent.lean:348）。

证明思路（HOL）：`POLYHEDRON_FAN` + `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`
（LINH）+ `POLYTOPE_FAN80`（本文件上文）凑齐 conforming 三前提；
`dartset_leads_into_is_topological_component_yfan`
（Kepler/Text/PlanarityComponent.lean:535）把
`s = dartsetLeadsIntoFan ... f` 送入 `topologicalComponentYfan`；
`PIIJBJK`（Kepler/Text/ConformingAuto21.lean:903，需 conforming_fan/
conforming_bijection_fan 展开）保证每个 yfan-分量恰为某面的
dartsetLeadsInto 像；最后 `AMHFNXP`（本文件上文）给出唯一 facet
`f1` 使 `s = fchanged_p7 f1`。

候选已有引理：
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535；签名即按本文件 hfan 约定）
- `PIIJBJK`（Kepler/Text/ConformingAuto21.lean:903）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）、`Hypermap.faceSet`
  （Kepler/Text/Hypermap.lean:1008）
- `AMHFNXP`（本文件上文）
- 跨批依赖：`PIIJBJK` 需 ConformingAuto 链（经 PlanarityAuto16 传递可
  用）；HOL 证明中的 `REMOVE_ASSUM_TAC`-清理不进陈述 -/
theorem WBLARHH {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron_p7 p) (hz : (0 : V3) ∈ interior p)
    (hfan : FAN 0 (Set.extremePoints ℝ p) (edges_p7 p))
    {f : Set (V3 × V3)}
    (hf : f ∈ (hypermapOfFan 0 (Set.extremePoints ℝ p) (edges_p7 p) hfan).faceSet) :
    ∃! f1 : Set V3, FacetOf_p7 f1 p ∧
      dartsetLeadsIntoFan 0 (Set.extremePoints ℝ p) (edges_p7 p) f = fchanged_p7 f1 := by
  sorry

end Kepler.Text
