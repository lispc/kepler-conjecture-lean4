/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18f.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18f of block 18, planarity.hl:9297-10095): the eight
angle/cone theorems
- `condition_to_in_aff_gt_by_angle` (9297)
- `condition1_to_in_aff_gt_by_angle` (9396)
- `angle_is_small_fan` (9479)
- `angle_is_smallpi_fan` (9639)
- `exists_rw_dart_inter_aff_gt_fan` (9680, ~300 HOL lines, hardest)
- `scale_in_edges_fan` (9981)
- `aff_gt_imp_not_collinear` (10020)
- `conditions_in_rcone_fan` (10051)

SKELETON ONLY: every proof below is `sorry`; a worker pool fills them
mechanically from the per-theorem HOL proof sketch in the docstring
(the verbatim HOL statement is included so the worker never needs to
open the .hl file). `lake env lean` green with all sorries.

Encoding notes (gaps / closest existing encodings):
- HOL `e1_fan`/`e2_fan`/`e3_fan` ↔ `e1Fan`/`e2Fan`/`e3Fan`
  (Kepler/Text/TopologyFan.lean:2261-2268).
- HOL `rcone_fan x v h` ↔ `rconeFan x v h` (Kepler/Text/TopologyFan.lean:2253;
  an identical `Kepler.Text.Fan.rconeFan` also exists, Kepler/Text/Fan.lean:186).
- HOL `rw_dart_fan x V E (y,v,w,w1) h` ↔ `rwDartFan x V E (y,v,w,w1) h`
  (Kepler/Text/TopologyFan.lean:3145; identical `Kepler.Text.Fan.rwDartFan`
  at Kepler/Text/Fan.lean:192).
- HOL `norm ((v - x) cross (u - x))`: there is no public V3-level cross in
  the repo (`cross3` in TopologyFan is private), so the statement uses the
  established `WithLp.toLp 2 (crossProduct …)` idiom (as in
  Kepler/Text/Planarity.lean:3792) under the V3 Euclidean norm `‖·‖`.
- HOL `aff_gt_2_1` is not ported under that name; its ray characterization
  is `affGt_pair_iff` (Kepler/Geom/Aff.lean:82).
- HOL `remark1_fan` (fan.hl:423) and `inequality4_aim_in_convex_fan`
  (planarity.hl:7933) are not yet ported; the fragments needed are noted
  per-theorem below.
-/
import Kepler.Text.PlanarityNotCut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 角度条件给出的 aff_gt 成员（planarity.hl:9297-9478） -/

/-- HOL planarity.hl:9297-9395 `condition_to_in_aff_gt_by_angle`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 s1:real.
~collinear {x,v,u} /\  &0< (v - x) dot (u - x) /\ &0< s1
/\ s1< atn ((norm ((v - x) cross (u - x))) * inv((v - x) dot (u - x)))
==>
sin s1 % e1_fan x v u + cos s1 % e3_fan x v u + x IN aff_gt {x} {v, u}
```

证明思路：`atn_bounds` 给出 `s1 < pi/2`；`aff_gt_1_2` 把目标化为找
`t1+t2+t3=1`、`t2,t3>0` 的组合。取
`t3 = sin s1 * |v-x| * |(v-x) cross (u-x)|⁻¹`，
`t2 = |v-x|⁻¹*(cos s1 - sin s1*|(v-x) cross (u-x)|⁻¹*((v-x) dot (u-x))`，
`t1 = 1 - t3 - t2`；向量恒等式经 CROSS_LAGRANGE 展开 `e1_fan`/`e3_fan`
后 `module` 可验证；`t2 > 0` 由 `tan s1 < |cross| * (dot)⁻¹`（TAN_MONO_LT
+ ATN_TAN）两端乘正数得到，`t3 > 0` 由 `0 < sin s1`（SIN_POS_PI2）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499，即
  HOL `properties_coordinate` 的角色）
- `e3Fan_cross_ux_ne_zero`（Kepler/Text/TopologyFan.lean:2355）
- `e1Fan_dot_self`/`e2Fan_dot_self`/`e3Fan_dot_self`/`e1Fan_dot_e3`
  （Kepler/Text/TopologyFan.lean:2415/2397/2347/2431）
- `fan_not_collinear`（Kepler/Text/Fan.lean:342） -/
theorem condition_to_in_aff_gt_by_angle {x v u : V3} {s1 : ℝ}
    (hnc : ¬ Collinear3 x v u) (hdot : 0 < (v - x) ⬝ᵥ (u - x)) (hs1 : 0 < s1)
    (hs : s1 < Real.arctan
      (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (u - x))⁻¹)) :
    Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x ∈
      affGt {x} {v, u} := by
  sorry

/-- HOL planarity.hl:9396-9478 `condition1_to_in_aff_gt_by_angle`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 s1:real.
~collinear {x,v,u} /\ &0< s1 /\ s1< pi/ &2
/\ (v - x) dot (u - x:real^3) <= &0
==>
sin s1 % e1_fan x v u + cos s1 % e3_fan x v u + x IN aff_gt {x} {v, u}`
```

证明思路：与 `condition_to_in_aff_gt_by_angle` 完全相同的见证系数
`t1, t2, t3`；区别只在 `t2 > 0`：此处 `cos s1 > 0`（COS_POS_PI2）而
`(v-x) dot (u-x) <= 0`，故减去的项 `sin s1 * |cross|⁻¹ * dot <= 0`，
`t2 >= |v-x|⁻¹ * cos s1 > 0`（REAL_LE_MUL 连锁）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499）
- `e3Fan_cross_ux_ne_zero`（Kepler/Text/TopologyFan.lean:2355） -/
theorem condition1_to_in_aff_gt_by_angle {x v u : V3} {s1 : ℝ}
    (hnc : ¬ Collinear3 x v u) (hs1 : 0 < s1) (hs : s1 < Real.pi / 2)
    (hle : (v - x) ⬝ᵥ (u - x) ≤ 0) :
    Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x ∈
      affGt {x} {v, u} := by
  sorry

/-! ## 方位角与 sigma 后继（planarity.hl:9479-9679） -/

/-- HOL planarity.hl:9479-9638 `angle_is_small_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
 azim x v u w <= azim x v u (sigma_fan x V E v u)
```

证明思路：若 `set_of_edge v V E = {u}` 则 CARD=1 与 `hcard` 矛盾。否则
令 `w1 = sigma_fan x V E v u`；`fan80`（u,w 与 v,u 两次）+ `hsigma` 给
`0 < azim x u w v < pi`，`properties_fully_surrounded` 得四点不共面，
`notcoplanar_imp_notcollinear_fan`/`properties_of_fully_surrounded1_fan`
给 `0 < azim x v u w < pi`。若 `azim x v u w <= azim x v u w1` 即结论；
若 `azim x v u w1 < azim x v u w`，`sum4_azim_fan` 分解 + 
`exists_cut_in_edge_fan` 取弦点 `va`，`decomposition_planar_by_angle_fan`
二分：一支与 `not_cut_in_edges_fan`（边内部不相交）矛盾，另一支把
`w`（或 `u`）逼进 `aff {x,u}`（或 `aff {x,w}`）与非共线矛盾。
注意：HOL 用的 `remark1_fan`（fan.hl:423）未移植，需用
`fan_not_collinear` + sigmaFan 性质现场替代。

候选已有引理：
- `fan_not_collinear`（Kepler/Text/Fan.lean:342）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_of_fully_surrounded1_fan`（Kepler/Text/PlanarityNotCut.lean:2330）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `exists_cut_in_edge_fan`（Kepler/Text/PlanarityNotCut.lean:1974）
- `decomposition_planar_by_angle_fan`（Kepler/Text/Planarity.lean:4203）
- `not_cut_in_edges_fan`（Kepler/Text/PlanarityNotCut.lean:1224）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）、
  `pos_in_aff_ge_fan`（Kepler/Text/Planarity.lean:4366）、
  `aff_gt1_subset_aff_ge`（Kepler/Text/Planarity.lean:3888） -/
theorem angle_is_small_fan {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    azim x v u w ≤ azim x v u (sigmaFan x V E v u) := by
  sorry

/-- HOL planarity.hl:9639-9679 `angle_is_smallpi_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
&0< azim x v u w /\ azim x v u w <pi
```

证明思路：`0 <`：`azim_nonneg`，若 `= 0` 则 AZIM_EQ_0_PI_EQ_COPLANAR
给出共面，与 `properties_fully_surrounded`（由 fan80 + hsigma 得
`0 < azim x u w v < pi`）矛盾（Lean 侧可用 `azim_eq_zero_iff` +
`affGt_pair_iff` 走 PlanarityNotCut.lean:2330 的同款论证）。
`< pi`：`angle_is_small_fan` 给 `azim x v u w <= azim x v u w1`，
而 fan80(v,u) 给 `azim x v u w1 < pi`（`w1 = sigma_fan x V E v u`）。

候选已有引理：
- `azim_nonneg`（Kepler/Geom/Azim.lean:947）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `angle_is_small_fan`（本文件上文） -/
theorem angle_is_smallpi_fan {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    0 < azim x v u w ∧ azim x v u w < Real.pi := by
  sorry

/-! ## rw_dart 与 aff_gt 相交（planarity.hl:9680-9980，最难一块） -/

/-- HOL planarity.hl:9680-9980 `exists_rw_dart_inter_aff_gt_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 .
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
(?h:real. &0< h /\
(!t:real. &0< t /\ t< h==>
(!s:real. &0<s /\ s< pi/ &2
==>
~(rw_dart_fan x V E ((x:real^3),(v:real^3),(u:real^3),(sigma_fan x V E v (u:real^3))) (cos(s)) INTER aff_gt {x} {v, (&1-t)%u+t%w}={})
)))
```

证明思路：取 `h = 1`。前半与 `angle_is_small_fan` 同一巨型分情况
（set_of_edge v = {u} 矛盾；`w1 = sigma_fan x V E v u`；azim 大小二分；
`exists_cut_in_edge_fan` + `decomposition_planar_by_angle_fan` +
`not_cut_in_edges_fan` 排除 `azim x v u w1 < azim x v u w`），得到
`aff_gt {x} {v, va} ⊆ wedge x v u w1`（HOL 由 aff_gt_inter_aff_gt +
properties_of_collinear4_points_fan + AZIM_EQ_ALT 得出）。于是
`rw_dart ∩ aff_gt {x} {v, va}` 化为 `rcone_fan x v (cos s) ∩ aff_gt {x} {v, va}`。
对每个 `t` 记 `va = (1-t)•u + t•w`，按 `(v-x) dot (va-x)` 符号二分取
`s1 = s/2`（dot<=0 支，用 `condition1_to_in_aff_gt_by_angle`）或
`s1 = min s (atn(|cross|/(dot))/2`（dot>0 支，用
`condition_to_in_aff_gt_by_angle`），见证点
`y = x + sin s1 • e1_fan x v va + cos s1 • e3_fan x v va`：
`y ∈ aff_gt` 即上述二引理；`y ∈ rcone` 由正交标架
（`orthonormal_e1Fan_e2Fan_e3Fan`）算出
`(y-x) dot (v-x) = |v-x| * cos s1 > |v-x| * cos s = |y-x| * |v-x| * cos s`
（SIN_CIRCLE 给 `|y-x| = 1`，COS_MONO_LT 给严格不等）。
注意：HOL 的 `inequality4_aim_in_convex_fan`（planarity.hl:7933）与
`remark1_fan` 未移植，需现场替代（弦点非共线用
`not_collinear_is_properties_fully_surrounded`
Kepler/Text/Planarity.lean:2559）。

候选已有引理：
- `angle_is_small_fan`（本文件上文）
- `condition_to_in_aff_gt_by_angle` / `condition1_to_in_aff_gt_by_angle`（本文件上文）
- `rwDartFan` / `rconeFan` 定义（Kepler/Text/TopologyFan.lean:3145/2253）
- `wedge`（Kepler/Geom/Azim.lean:63）、`azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `not_collinear_is_properties_fully_surrounded`（Kepler/Text/Planarity.lean:2559）
- `not_cut_in_edges_fan`（Kepler/Text/PlanarityNotCut.lean:1224）
- `exists_cut_in_edge_fan`（Kepler/Text/PlanarityNotCut.lean:1974）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499） -/
theorem exists_rw_dart_inter_aff_gt_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    ∃ h : ℝ, 0 < h ∧
      ∀ t : ℝ, 0 < t → t < h →
        ∀ s : ℝ, 0 < s → s < Real.pi / 2 →
          (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ∩
            affGt {x} {v, (1 - t) • u + t • w}) ≠ ∅ := by
  sorry

/-! ## 缩放、非共线与锥条件（planarity.hl:9981-10095） -/

/-- HOL planarity.hl:9981-10019 `scale_in_edges_fan`

HOL 原文：
```
!(x:real^3) (v:real^3) (u:real^3) (w:real^3).
DISJOINT {x} {v,u}
/\ w IN aff_gt {x} {v,u}
==>
(?a t:real. &0<a /\ &0<t /\ t< &1
/\ a%(w-x) = (&1-t)% v+ t%u-x)
```

证明思路：`aff_gt_1_2` 展开给 `w = t1•x + t2•v + t3•u`（`t2,t3>0`、
和为 1）；于是 `w - x = t2•(v-x) + t3•(u-x)`。令 `a = (1-t1)⁻¹`、
`t = t3/(1-t1)`：`0 < 1 - t1`（因 `t1 = 1 - t2 - t3 < 1`），
`a • (w - x) = (1-t)•(v-x) + t•(u-x) = (1-t)•v + t•u - x`，
正性由 `REAL_LT_MUL`/`inv_pos`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165） -/
theorem scale_in_edges_fan {x v u w : V3}
    (hdis : Disjoint ({x} : Set V3) {v, u}) (hw : w ∈ affGt {x} {v, u}) :
    ∃ a t : ℝ, 0 < a ∧ 0 < t ∧ t < 1 ∧
      a • (w - x) = (1 - t) • v + t • u - x := by
  sorry

/-- HOL planarity.hl:10020-10050 `aff_gt_imp_not_collinear`

HOL 原文：
```
!x u v w:real^3.
~collinear{x,v,u}/\ w IN aff_gt{x,v} {u}==> ~collinear{x,v,w}
```

证明思路：HOL 用 AFF_GT_2_1 展开 `w = t1•x + t2•v + t3•u`（`t3>0`、
和 1）。若 `collinear {x,v,w}`，即 `w ∈ affineSpan {x,v}`：
`w = u'•x + v'•v`，则 `t3•u = (u'-t1)•x + (v'-t2)•v`，除以 `t3` 得
`u ∈ aff {x,v}`，与 `~collinear {x,v,u}` 矛盾。
Lean 侧 `aff_gt_2_1` 未移植：用 `affGt_pair_iff`（AFF_GT_2_1 的射线
刻画，`w - x = c•(u-x) + h•(v-x)`，`c>0`）+ `Collinear` 的
affineSpan characterization（Mathlib `collinear_iff`/
`mem_affineSpan_pair`）完成同一归约。

候选已有引理：
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `collinear3_of_eq` / `collinear3_pair_left` / `collinear3_pair_right`
  （Kepler/Geom/Azim.lean:121、Kepler/Geom/AzimLemmas.lean:164-171） -/
theorem aff_gt_imp_not_collinear {x v u w : V3}
    (hnc : ¬ Collinear3 x v u) (hw : w ∈ affGt {x, v} {u}) :
    ¬ Collinear3 x v w := by
  sorry

/-- HOL planarity.hl:10051-10095 `conditions_in_rcone_fan`

HOL 原文：
```
!x v u w:real^3 s:real.
~collinear {x,v,u}/\ w IN aff_gt {x} {v,u} /\ &0<s /\ s< pi/ &2 /\u IN rcone_fan x v (cos s)==> w IN rcone_fan x v (cos s)
```

证明思路：`rcone_fan` 展开为目标
`(w-x) dot (v-x) > |w-x| * |v-x| * cos s`。`aff_gt_1_2` 给
`w - x = t2•(v-x) + t3•(u-x)`（`t2,t3>0`）。LHS =
`t2*|v-x|² + t3*((u-x) dot (v-x))`；由 `u ∈ rcone` 与 Cauchy-Schwarz
`((u-x) dot (v-x)) > |u-x|*|v-x|*cos s`；RHS 由三角不等式
`|w-x| <= t2*|v-x| + t3*|u-x|` 与 `cos s >= 0`（COS_POS_PI2）放大
合并即得（HOL 的 NORM_TRIANGLE + REAL_LE_RMUL 链）。

候选已有引理：
- `rconeFan` 定义（Kepler/Text/TopologyFan.lean:2253）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- Mathlib `norm_add_le`（三角不等式）、`abs_inner_le_norm`/
  Cauchy–Schwarz（dot 与范数乘积） -/
theorem conditions_in_rcone_fan {x v u w : V3} {s : ℝ}
    (hnc : ¬ Collinear3 x v u) (hw : w ∈ affGt {x} {v, u})
    (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hu : u ∈ rconeFan x v (Real.cos s)) :
    w ∈ rconeFan x v (Real.cos s) := by
  sorry

end Kepler.Text
