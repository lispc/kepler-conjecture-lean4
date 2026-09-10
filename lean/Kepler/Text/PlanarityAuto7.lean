/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18k.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18k of block 18, planarity.hl:11787-12005): the
yfan-component interior / boundary / aff_gt-separation layer
- `zpoint_in_yfan` (11787)
- `segment_in_segment` (11802)
- `connect_insidepoint_to_bound_yfan` (11820)
- `in_topological_component_yfan_is_connected` (11882)
- `expand_element_in_topological_component_yfan` (11891)
- `segmentsubset_aff_gt` (11905)
- `point_in_aff_gt_in_yfan` (11927)
- `segment_subset_yfan` (11938)
- `exists_in_aff_gt_disjoint` (11956)
- `aff_gt_subset_component_y_fan` (11969)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `connected` ↔ Mathlib `IsPreconnected` (repo convention; HOL 空集连通,
  Mathlib `IsConnected` 额外要求 `Nonempty`, cf.
  Kepler/Text/TopologyFan.lean:4086).
- HOL `connected_component s y` ↔ `connectedComponentIn s y`
  (Kepler/Text/PlanarityComponent.lean:31).
- HOL `segment [x,y]` ↔ `segment ℝ x y` (Mathlib closed segment).
- HOL `DISJOINT {x} {y,z}` ↔ `Disjoint ({x} : Set V3) {y, z}`.
- `segment_in_segment` 与 `segmentsubset_aff_gt` 的 HOL 版对 `real^N` 陈述；
  `segment_in_segment` 以任意实向量空间 `E` 表达（更强，仿射/凸组合结论不
  依赖欧氏结构），`segmentsubset_aff_gt` 受仓库 `affGt` 的 `V3` 专有定义
  限制只能对 `V3` 陈述（保真度缺口，已在该定理 docstring 标注）。
- HOL `closest_point s x`（11831-11849 使用）在 Mathlib/本仓库均未移植；
  本批 10 条定理的陈述均不出现 `closest_point`（仅 `connect_insidepoint_to_
  bound_yfan` 的证明内部使用），故骨架不受影响；该定理 docstring 给出最接近
  的替代 `exists_norm_eq_iInf_of_complete_convex` 并标注缺口。
- `in_topological_component_yfan_is_connected` 已在本仓库以
  `isPreconnected_of_mem_topologicalComponentYfan`
  (Kepler/Text/TopologyFan.lean:4315，源 topology.hl:4704) 移植；为保持
  planarity.hl 的 HOL 名称仍单独列出（docstring 已注明等价引理）。
-/

import Kepler.Text.PlanarityAuto6

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 分量中的点落在 yfan（planarity.hl:11787-11801） -/

/-- HOL planarity.hl :11787-11801 `zpoint_in_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool z:real^3.
FAN(x,V,E) /\ ~(E={})
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
==> z IN yfan(x,V,E)
```

证明思路：由 `topological_component_subset_yfan` 得 `U ⊆ yfan x V E`，再用
`z ∈ U` 传递即得。HOL 即 `MRESA_TAC topological_component_subset_yfan`
后 `SET_TAC[]`。`FAN`/`E ≠ ∅` 两条假设在结论中未使用，仅为与 HOL 保真而保留。

候选已有引理：
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `yfan`（Kepler/Text/Fan.lean:158） -/
theorem zpoint_in_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (z : V3)
    (hfan : FAN x V E) (hne : E ≠ ∅)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U) :
    z ∈ yfan x V E := by
  exact topological_component_subset_yfan hU hz

/-! ## 线段上的凸组合（planarity.hl:11802-11819） -/

/-- HOL planarity.hl :11802-11819 `segment_in_segment`

HOL 原文：
```
!x y z:real^N. z IN segment [x,y]==>  (!t. &0<= t /\ t<= &1 ==> (&1-t) %z +t %y IN segment[x,y])
```

证明思路：`segment ℝ x y` 凸（`convex_segment`），且 `y ∈ segment ℝ x y`
（`right_mem_segment`）。把 `(1-t)•z + t•y` 写成 `segment ℝ z y` 的内点
（`segment_subset_iff`/`left_mem_segment`+`right_mem_segment`），再由
`Convex.segment_subset` 沿 `z, y ∈ segment ℝ x y` 传递即得。HOL 即展开
`segment` 的系数存在性并做 `REAL_LE_ADD`/`REAL_LE_MUL`。

编码说明：HOL `real^N` 以任意实向量空间 `E` 表达（更强；结论只用凸性）。
Mathlib 无与 HOL 同名/同形的整句引理，故保留（最接近者为 `convex_segment`）。

候选已有引理：
- `convex_segment`（Mathlib/Analysis/Convex/Basic.lean:164）
- `Convex.segment_subset`（Mathlib/Analysis/Convex/Basic.lean:63）
- `left_mem_segment`（Mathlib/Analysis/Convex/Segment.lean:105）
- `right_mem_segment`（Mathlib/Analysis/Convex/Segment.lean:108）
- `segment_subset_iff`（Mathlib/Analysis/Convex/Segment.lean:86） -/
theorem segment_in_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y z : E) (hz : z ∈ segment ℝ x y) :
    ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → (1 - t) • z + t • y ∈ segment ℝ x y := by
  intro t ht
  exact convex_iff_add_mem.mp (convex_segment x y) hz (right_mem_segment ℝ x y)
    (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-! ## 内点与 xfan 边界点的连线（planarity.hl:11820-11881） -/

/-- HOL planarity.hl :11820-11881 `connect_insidepoint_to_bound_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool z:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
==> ?y. ~(y=x)/\  y IN xfan(x,V,E) /\(!t. &0<t /\ t<&1==>   (&1-t)%y+t%z IN yfan(x,V,E))
```

证明思路：由 `exists_point_notxin_convex_in_xfan` 取 `v ∈ xfan` 且
`x ∉ convexHull {v,z}`；令 `y` 为紧非空集 `xfan x V E ∩ segment[v,z]`
（`xfan_inter_segment_closed_fan`+`notempty_xfan_inter_segment_fan`）中距 `z`
最近点（HOL `closest_point`）。由 `point_in_yfan_not_x_fan` 得 `z ≠ x`，故
`y ≠ x`；再证 `(1-t)•y + t•z` 对 `t∈(0,1)` 距 `z` 更近（严格凸）从而必须落在
`yfan`（否则与 `y` 最近性矛盾），并用 `segment_in_segment` 保持线段隶属。

编码缺口：HOL `closest_point s x` 未移植；最接近的替代是
`exists_norm_eq_iInf_of_complete_convex`（Mathlib，对完备凸集）或
`Metric.exists_dist_eq_iInf` 型最近点存在性；本定理陈述不含 `closest_point`。

候选已有引理：
- `exists_point_notxin_convex_in_xfan`（Kepler/Text/PlanarityAuto6.lean:276）
- `xfan_inter_segment_closed_fan`（Kepler/Text/PlanarityAuto6.lean:355）
- `notempty_xfan_inter_segment_fan`（Kepler/Text/PlanarityAuto6.lean:327）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `segment_in_segment`（本文件上文）
- `exists_norm_eq_iInf_of_complete_convex`
  （Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean:34）
- `xfan`（Kepler/Text/Fan.lean:154）、`yfan`（Kepler/Text/Fan.lean:158） -/
private lemma dist_smul_segment_lt {y z : V3} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hyz : y ≠ z) :
    dist z ((1 - t) • y + t • z) < dist z y := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have h1t1 : 1 - t < 1 := by linarith
  have hz_pos : 0 < dist z y := dist_pos.mpr (Ne.symm hyz)
  have hsub : z - ((1 - t) • y + t • z) = (1 - t) • (z - y) := by module
  calc
    dist z ((1 - t) • y + t • z)
        = ‖(1 - t) • (z - y)‖ := by rw [dist_eq_norm, hsub]
      _ = (1 - t) * ‖z - y‖ := norm_smul_of_nonneg (le_of_lt h1t) _
      _ = (1 - t) * dist z y := by rw [dist_eq_norm]
      _ < 1 * dist z y := mul_lt_mul_of_pos_right h1t1 hz_pos
      _ = dist z y := one_mul _

theorem connect_insidepoint_to_bound_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (z : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U) :
    ∃ y : V3, y ≠ x ∧ y ∈ xfan x V E ∧
      ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E := by
  have hne : E ≠ ∅ := nonsetedge_fully_surround_fan hcard hfan
  have hxz : x ≠ z := point_in_yfan_not_x_fan x V E U z hfan hne hU hz
  obtain ⟨v, hv_xfan, hx_not_conv⟩ :=
    exists_point_notxin_convex_in_xfan x V E z hfan hxz hne
  have hne_inter : (xfan x V E ∩ segment ℝ v z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr
      (notempty_xfan_inter_segment_fan x V E z v hfan hv_xfan)
  have hcompact_seg : IsCompact (segment ℝ v z) := by
    rw [← convexHull_pair v z]
    exact (Set.toFinite ({v, z} : Set V3)).isCompact_convexHull ℝ
  have hcompact : IsCompact (xfan x V E ∩ segment ℝ v z) :=
    hcompact_seg.inter_left (xfan_closed_fan hfan)
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hne_inter
    (continuous_const.dist continuous_id).continuousOn
  have hy_xfan : y ∈ xfan x V E := hy.1
  have hy_seg : y ∈ segment ℝ v z := hy.2
  have hy_conv : y ∈ convexHull ℝ ({v, z} : Set V3) := by
    rw [convexHull_pair]
    exact hy_seg
  have hyx : y ≠ x := by
    intro h
    exact hx_not_conv (h ▸ hy_conv)
  have hz_yfan : z ∈ yfan x V E := topological_component_subset_yfan hU hz
  have hyz : y ≠ z := by
    intro h
    exact hz_yfan.2 (h ▸ hy_xfan)
  refine ⟨y, hyx, hy_xfan, ?_⟩
  intro t ht0 ht1
  by_contra hp_not
  have hp_xfan : (1 - t) • y + t • z ∈ xfan x V E := by
    by_contra hpx
    exact hp_not (by simp [yfan, hpx])
  have hp_seg : (1 - t) • y + t • z ∈ segment ℝ v z :=
    segment_in_segment v z y hy_seg t ⟨le_of_lt ht0, le_of_lt ht1⟩
  have hle : dist z y ≤ dist z ((1 - t) • y + t • z) :=
    isMinOn_iff.mp hmin _ ⟨hp_xfan, hp_seg⟩
  exact (not_lt_of_ge hle) (dist_smul_segment_lt ht0 ht1 hyz)

/-! ## yfan 分量的连通性与刻画（planarity.hl:11882-11904） -/

/-- HOL planarity.hl :11882-11890 `in_topological_component_yfan_is_connected`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool.
U IN topological_component_yfan (x,V,E)
==> connected U
```

证明思路：展开 `topologicalComponentYfan`，`U = connectedComponentIn (yfan x V E) b`，
连通分量预连通（`isPreconnected_connectedComponentIn`）即得。HOL 即
`REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT]`。

编码说明：HOL `connected` 取 Mathlib `IsPreconnected`（仓库约定）。

候选已有引理：
- `isPreconnected_connectedComponentIn`（Mathlib/Topology/Connected/Basic.lean:536）
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- 等价已移植引理：`isPreconnected_of_mem_topologicalComponentYfan`
  （Kepler/Text/TopologyFan.lean:4315，源 topology.hl:4704；本仓库已存在，
  此处保留 planarity.hl 的 HOL 名称） -/
theorem in_topological_component_yfan_is_connected (x : V3) (V : Set V3)
    (E : Set (Set V3)) (U : Set V3)
    (hU : U ∈ topologicalComponentYfan x V E) :
    IsPreconnected U := by
  exact isPreconnected_of_mem_topologicalComponentYfan hU

/-- HOL planarity.hl :11891-11904 `expand_element_in_topological_component_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool z:real^3.
FAN(x,V,E) 
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
==> U=connected_component (yfan(x,V,E)) z
```

证明思路：展开 `topologicalComponentYfan` 得 `U = connectedComponentIn (yfan x V E) b`
（`b ∈ yfan`）；由 `z ∈ U` 与 `connectedComponentIn_subset` 得 `z ∈ yfan`，
再用 `connectedComponentIn_eq`（HOL `CONNECTED_COMPONENT_EQ`）把
`connectedComponentIn (yfan x V E) z` 与 `U` 对齐。HOL 即
`MRESA_TAC CONNECTED_COMPONENT_EQ`。

编码说明：HOL `connected_component s z` ↔ `connectedComponentIn s z`。

候选已有引理：
- `connectedComponentIn_eq`（Mathlib/Topology/Connected/Basic.lean:585）
- `connectedComponentIn_subset`（Mathlib/Topology/Connected/Basic.lean:529）
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `yfan`（Kepler/Text/Fan.lean:158） -/
theorem expand_element_in_topological_component_yfan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (U : Set V3) (z : V3)
    (hfan : FAN x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U) :
    U = connectedComponentIn (yfan x V E) z := by
  rcases hU with ⟨b, _hb, rfl⟩
  exact connectedComponentIn_eq hz

/-! ## aff_gt 上的凸组合与 yfan 分离（planarity.hl:11905-11968） -/

/-- HOL planarity.hl :11905-11926 `segmentsubset_aff_gt`

HOL 原文：
```
!x y z w:real^N.
DISJOINT {x} {y,z}/\ w IN aff_gt {x} {y,z}
==> !t. &0<= t /\ t< &1 ==> (&1-t) %w+t%z IN aff_gt {x} {y,z}
```

证明思路：用 `aff_gt_1_2`（HOL `AFF_GT_1_2`）把 `w = t1•x + t2•y + t3•z`
（`t2,t3>0`、`t1+t2+t3=1`）展开；目标点系数取
`((1-t)t1, (1-t)t2, (1-t)t3 + t)`，由 `0 ≤ t < 1` 得后两系数仍严格正、系数和
仍为 1，再用 `aff_gt_1_2` 反向打包即得。

编码说明（保真度缺口）：HOL 对 `real^N` 陈述，但仓库 `affGt` 是 `V3` 专有
定义（Kepler/Geom/Aff.lean:39），故只能对 `V3` 陈述。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `affGt`（Kepler/Geom/Aff.lean:39） -/
theorem segmentsubset_aff_gt (x y z w : V3)
    (hdis : Disjoint ({x} : Set V3) {y, z}) (hw : w ∈ affGt {x} {y, z}) :
    ∀ t : ℝ, 0 ≤ t ∧ t < 1 → (1 - t) • w + t • z ∈ affGt {x} {y, z} := by
  sorry

/-- HOL planarity.hl :11927-11937 `point_in_aff_gt_in_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y:real^3 z:real^3 w:real^3.
FAN(x,V,E) /\ DISJOINT {x} {y,z} /\ w IN aff_gt {x} {y,z}
/\ (!t. &0 < t /\ t < &1 ==> (&1 - t) % y + t % z IN yfan (x,V,E))
==> w IN yfan(x,V,E)
```

证明思路：直接由 `aff_gt_connect_bound_subset_yfan`（由 `FAN`、`DISJOINT` 与
`hconn` 给出 `affGt {x} {y,z} ⊆ yfan x V E`）与 `w ∈ affGt {x} {y,z}` 传递。
HOL 即 `MRESA_TAC aff_gt_connect_bound_subset_yfan` 后 `SET_TAC[]`。

候选已有引理：
- `aff_gt_connect_bound_subset_yfan`（Kepler/Text/PlanarityConnect.lean:276）
- `yfan`（Kepler/Text/Fan.lean:158） -/
theorem point_in_aff_gt_in_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (y z w : V3)
    (hfan : FAN x V E) (hdis : Disjoint ({x} : Set V3) {y, z})
    (hw : w ∈ affGt {x} {y, z})
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    w ∈ yfan x V E := by
  sorry

/-- HOL planarity.hl :11938-11955 `segment_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y:real^3 z:real^3 w:real^3.
FAN(x,V,E) /\ DISJOINT {x} {y,z} /\ z IN yfan(x,V,E) /\ w IN aff_gt {x} {y,z}
/\ (!t. &0 < t /\ t < &1 ==> (&1 - t) % y + t % z IN yfan (x,V,E))
==> segment[w,z] SUBSET yfan(x,V,E)
```

证明思路：展开 `segment ℝ w z`，取内点 `(1-u)•w + u•z`（`0≤u≤1`）。当
`u<1` 时由 `segmentsubset_aff_gt` 该点在 `affGt {x} {y,z}`，再用
`point_in_aff_gt_in_yfan` 得在 `yfan`；当 `u=1` 时点即 `z`，由假设
`z ∈ yfan` 得。HOL 即 `segmentsubset_aff_gt` + `aff_gt_connect_bound_subset_yfan`
后对 `u<1 ∨ u=1` 分情形 `SET_TAC[]`。

候选已有引理：
- `segmentsubset_aff_gt`（本文件上文）
- `point_in_aff_gt_in_yfan`（本文件上文）
- `aff_gt_connect_bound_subset_yfan`（Kepler/Text/PlanarityConnect.lean:276）
- `yfan`（Kepler/Text/Fan.lean:158）、`segment`（Mathlib） -/
theorem segment_subset_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (y z w : V3)
    (hfan : FAN x V E) (hdis : Disjoint ({x} : Set V3) {y, z})
    (hz : z ∈ yfan x V E) (hw : w ∈ affGt {x} {y, z})
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    segment ℝ w z ⊆ yfan x V E := by
  sorry

/-- HOL planarity.hl :11956-11968 `exists_in_aff_gt_disjoint`

HOL 原文：
```
!x:real^3  v:real^3 u:real^3.
DISJOINT {x} {v,u} ==> ?y:real^3. y IN aff_gt {x} {v, u}
```

证明思路：用 `aff_gt_1_2`（HOL `AFF_GT_1_2`）展开，取见证
`y = (1/2)•v + (1/2)•u`（系数 `t1=0, t2=t3=1/2` 严格正且和为 1），
`DISJOINT {x} {v,u}` 保证 `x` 不在 `{v,u}` 从而 `aff_gt_1_2` 的假设成立。
HOL 即 `EXISTS_TAC` 后 `REAL_ARITH_TAC`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `affGt`（Kepler/Geom/Aff.lean:39） -/
theorem exists_in_aff_gt_disjoint (x v u : V3)
    (hdis : Disjoint ({x} : Set V3) {v, u}) :
    ∃ y : V3, y ∈ affGt {x} {v, u} := by
  sorry

/-- HOL planarity.hl :11969-12005 `aff_gt_subset_component_y_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ DISJOINT {x} {y,z}
/\ (!t. &0 < t /\ t < &1 ==> (&1 - t) % y + t % z IN yfan (x,V,E))
==> aff_gt {x} {y,z} SUBSET U
```

证明思路：由 `expand_element_in_topological_component_yfan` 把目标化为
`affGt {x} {y,z} ⊆ connectedComponentIn (yfan x V E) z`。由
`exists_in_aff_gt_disjoint` 取 `y' ∈ affGt {x} {y,z}`；`affGt` 凸
（HOL `CONVEX_AFF_GT`）故预连通，且由 `aff_gt_connect_bound_subset_yfan` /
`point_in_aff_gt_in_yfan` 含于 `yfan`，于是
`affGt {x} {y,z} ⊆ connectedComponentIn (yfan x V E) y'`
（`IsPreconnected.subset_connectedComponentIn`，HOL `CONNECTED_COMPONENT_MAXIMAL`）。
再用 `zpoint_in_yfan` 得 `z ∈ yfan`，由 `segment_subset_yfan`（取 `w=y'`）得
`segment[y',z] ⊆ yfan`，故 `y', z` 同属一个分量
（`CONNECTED_COMPONENT_OF_SUBSET`/`connectedComponentIn_eq`），最终
`connectedComponentIn (yfan x V E) y' = connectedComponentIn (yfan x V E) z`。

编码说明：HOL `CONVEX_AFF_GT` 在仓库中以 `convex_affGt_single_pair`
（`private`，Kepler/Text/PlanarityComponent.lean:89）实现，公开层面可经
`aff_gt_1_2` 或 `Affsign` 重新论证；`DISJOINT` 用 `Disjoint`。

候选已有引理：
- `expand_element_in_topological_component_yfan`（本文件上文）
- `exists_in_aff_gt_disjoint`（本文件上文）
- `point_in_aff_gt_in_yfan`（本文件上文）
- `segment_subset_yfan`（本文件上文）
- `zpoint_in_yfan`（本文件上文）
- `aff_gt_connect_bound_subset_yfan`（Kepler/Text/PlanarityConnect.lean:276）
- `IsPreconnected.subset_connectedComponentIn`
  （Mathlib/Topology/Connected/Basic.lean:553）
- `connectedComponentIn_eq`（Mathlib/Topology/Connected/Basic.lean:585）
- `connectedComponentIn_mono`（Mathlib/Topology/Connected/Basic.lean:635）
- `convex_affGt_single_pair`（private，Kepler/Text/PlanarityComponent.lean:89）
- `convex_segment`（Mathlib/Analysis/Convex/Basic.lean:164） -/
theorem aff_gt_subset_component_y_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (y z : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hdis : Disjoint ({x} : Set V3) {y, z})
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    affGt {x} {y, z} ⊆ U := by
  sorry

end Kepler.Text
