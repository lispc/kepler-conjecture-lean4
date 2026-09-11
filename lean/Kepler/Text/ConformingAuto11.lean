/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 11
(Conforming.hl:2638-3689).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 11, Conforming.hl:2638-3689):
- `XFAN_INTER_SET` (2638)
- `condition_azim_imp_edge_fan` (2668)
- `condition_azim_le_pi` (2758)
- `azim_trangle_le_azim_face_fan` (2820)
- `SIGMA_FAN_OF_FANADD_AT_POINT3` (2932)
- `SIGMA_FAN_OF_FANADD_AT_POINT4` (3073)
- `SIGMA_FAN_OF_FANADD_AT_POINT5` (3275)
- `SIGMA_FAN_OF_FANADD_AT_POINT6` (3476)
- `f1_fan_of_f10_eq_f20` (3603)
- `f1_fan_of_f20_eq_f30` (3642)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62);
  HOL `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `FAN(x,V,E)`
  ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL `fan80` ↔ `fan80`
  (Kepler/Text/Fan.lean:227); HOL `xfan` ↔ `xfan` (Kepler/Text/Fan.lean:154);
  HOL `aff_ge`/`aff_gt` ↔ `affGe`/`affGt` (Kepler/Geom/Aff.lean:42/39).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94). HOL `CARD ds >3`
  ↔ `3 < ds.ncard`.
- HOL `E UNION {{v,w}}` ↔ `E ∪ {({v, w} : Set V3)}`.
- HOL `UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e INTER s}` is the indexed
  union `⋃ e ∈ E, (affGe ({x} : Set V3) e ∩ s)` (cf. the identical convention
  in `XFAN_EQ_UNIONS_AFF_GE_1_2`, Kepler/Text/ConformingAuto3.lean:306).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `f10=(x,w,v,u)`,
  `f20=(x,v,u,w)`, `f30=(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`,
  `(u,w)`; `f1_fan` is `f1Fan` (Kepler/Text/ConformingDefs.lean:87).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and ConformingAuto8.lean:34-40,
  `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` and
  `face (hypermap1_of_fanx (x,V,E)) f` as
  `(hypermapOfFan x V E hfan).face f`, with pair darts. Because
  `hypermapOfFan` (Kepler/Text/Fan.lean:1169) needs an explicit
  `hfan : FAN x V E`, every theorem that mentions it carries an extra
  explicit `(hfan : FAN x V E)` argument. This is the only deviation from
  the HOL signatures (HOL's `hypermap_of_fan` is total).
- The last two theorems additionally mention
  `face (hypermap1_of_fanx (x,V,E1))`, for which the HOL statement supplies
  no `FAN(x,V,E1)` hypothesis (it is derivable in HOL via
  `STEP3_REDUCE_FAN`, ConformingAuto9.lean:298). Since `hypermapOfFan` needs
  a witness, those two statements carry one extra explicit argument
  `(hfan1 : FAN x V E1)`; this is the second and only other deviation.
- `SIGMA_FAN_OF_FANADD_AT_POINT2` (ConformingAuto10.lean:510) and
  `SIGMA_FAN_OF_FANADD1` (ConformingAuto10.lean:197), used by the HOL proofs
  of the last two theorems, live in ConformingAuto10, which is NOT imported
  here (the batch imports only `PlanarityAuto16` and `ConformingDefs`, per
  the porting convention); the proof sketches note them as candidates to be
  restated or imported by the worker pool.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `xfan`/`FAN`/`sigmaFan`/`azim`/`hypermapOfFan` vocabulary,
  so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.AffGtCut

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 边锥与半空间的交（Conforming.hl:2638-2667） -/

/-- HOL Conforming.hl :2638-2667 `XFAN_INTER_SET`

HOL 原文：
```
!x:real^N V E s:real^N->bool.
xfan(x,V,E) INTER s = UNIONS {y | ?e. e IN E /\ y = (aff_ge {x} e) INTER s}
```

编码说明：`xfan`（Fan.lean:154）与 `aff_ge`（Aff.lean:42）在仓库中固定为
`V3`，故 HOL 的多态点类型 `real^N` 特化到 `V3`；右端的存在量词
`UNIONS {y | ?e. e IN E /\ y = ...}` 编码为索引并
`⋃ e ∈ E, (affGe {x} e ∩ s)`（与 `XFAN_EQ_UNIONS_AFF_GE_1_2` 同一约定）。

证明思路：先用 `XFAN_EQ_UNIONS_AFF_GE_1_2` 把 `xfan x V E` 写成
`⋃ e ∈ E, affGe {x} e`，再对 `v` 外延：`v ∈ (⋃ e ∈ E, affGe {x} e) ∩ s`
当且仅当存在 `e ∈ E` 使 `v ∈ affGe {x} e ∧ v ∈ s`，即
`v ∈ ⋃ e ∈ E, (affGe {x} e ∩ s)`；`Set.mem_iUnion₂`/`Set.mem_inter_iff`
直接改写。

候选已有引理：
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306）
- `xfan`（Kepler/Text/Fan.lean:154）、`affGe`（Kepler/Geom/Aff.lean:42）
- `Set.mem_iUnion`、`Set.mem_iUnion₂`、`Set.mem_inter_iff`（Mathlib） -/
theorem XFAN_INTER_SET (x : V3) (V : Set V3) (E : Set (Set V3)) (s : Set V3) :
    xfan x V E ∩ s = ⋃ e ∈ E, (affGe ({x} : Set V3) e ∩ s) := by
  ext v
  simp only [Set.mem_inter_iff, xfan, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨e, he, hv⟩, hs⟩
    exact ⟨e, he, hv, hs⟩
  · rintro ⟨e, he, hv, hs⟩
    exact ⟨⟨e, he, hv⟩, hs⟩

/-! ## 方位角条件对 σ 与边的影响（Conforming.hl:2668-2931） -/

/-- 非共线给出 `Disjoint {x} {p,q}`（本文件私有副本）。 -/
private theorem disjoint_singleton_of_nc_ca11 {x p q : V3}
    (hnc : ¬ Collinear3 x p q) : Disjoint ({x} : Set V3) {p, q} := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.singleton_inter_eq_empty]
  intro hmem
  rcases Set.mem_insert_iff.mp hmem with he | he
  · exact hnc (by rw [he]; exact collinear3_of_eq rfl)
  · exact hnc (by rw [Set.mem_singleton_iff.mp he]; exact collinear3_pair_left rfl)

/-- `Collinear3` 后两点交换（本文件私有副本）。 -/
private theorem collinear3_swap_ca11 {a b c : V3} (h : ¬ Collinear3 a b c) :
    ¬ Collinear3 a c b := by
  intro hc
  apply h
  change Collinear ℝ ({a, b, c} : Set V3)
  rw [show ({a, b, c} : Set V3) = {a, c, b} from by ext z; simp; tauto]
  exact hc

/-- `affGt ⊆ affGe`（同一组合，严格正系数放宽为非负）。 -/
private theorem affGt_subset_affGe_ca11 (s t : Set V3) : affGt s t ⊆ affGe s t := by
  intro y hy
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hy
  exact ⟨f, hfin, hsum, fun z hz => (hpos z hz).le, hone⟩

/-- HOL Conforming.hl :2668-2757 `condition_azim_imp_edge_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w w1.
FAN(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E /\  {w,w1} IN E
/\ sigma_fan x V E u w = v
/\ sigma_fan x V E w w1 = u
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\  azim x w v u = azim x w w1 u
==> {v,w} IN E
```

编码说明：`sigma_fan` ↔ `sigmaFan`（Fan.lean:67）；`fan80` ↔ `fan80`
（Fan.lean:227）；`CARD (set_of_edge v V E) > 1` ↔
`1 < (setOfEdge v V E).ncard`；HOL 内层 `!v` 与外层参数 `v` 同名（遮蔽），
Lean 侧改名为 `v'`（alpha 等价）。`azim`（Azim.lean:58）参数顺序不变。

证明思路：由 `fan80` 与两条 σ 等式得 `x,w,u,v` 与 `x,u,w,w1` 各自不共面
（`properties_fully_surrounded`），进而用 `notcoplanar_imp_notcollinear_fan`
排除共线；由假设 `azim x w v u = azim x w w1 u` 与 `AZIM_COMPL`
（`azim_compl`）得 `azim x w u v = azim x w u w1`，再用
`AZIM_EQ_ALT`（`azim_eq_azim_iff_alt`）得 `v ∈ affGt {x,w} {w1}`；
最后 `AFF_GT_CUT_XFAN_IMP_EDGE_FAN`（配合 `XFAN_INTER_SET`）把
`affGt {x} {v,w} ∩ xfan` 的非空性转成 `{v,w} ∈ E`。

候选已有引理：
- `XFAN_INTER_SET`（本文件上文）
- `AFF_GT_CUT_XFAN_IMP_EDGE_FAN`（Kepler/Text/AffGtCut.lean:669）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_azim_iff_alt`（Kepler/Geom/AzimLemmas.lean:284，AZIM_EQ_ALT）
- `decomposition_planar_by_angle_fan`（Kepler/Text/Planarity.lean:4203）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `aff_gt12_subset_aff_ge`（Kepler/Text/Planarity.lean:3906）
- `exists_in_aff_gt`（Kepler/Text/PlanarityNotCut.lean:1847）
- 缺口：HOL `AZIM_EQ_0_PI_EQ_COPLANAR` 未以该名移植，用 `azim_eq_zero_iff`
  （Kepler/Geom/AzimLemmas.lean:296）替代 -/
theorem condition_azim_imp_edge_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w w1 : V3) :
    FAN x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, w1} : Set V3) ∈ E ∧
    sigmaFan x V E u w = v ∧
    sigmaFan x V E w w1 = u ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    azim x w v u = azim x w w1 u →
      ({v, w} : Set V3) ∈ E := by
  rintro ⟨hfan, hvu, huw, hww1, hsigma1, hsigma2, h80, hcard, hazim⟩
  -- `fan80` 给出的两组方位角界
  obtain ⟨h_uw0, h_uwpi⟩ := h80 u w huw
  rw [hsigma1] at h_uw0 h_uwpi
  obtain ⟨h_ww10, h_ww1pi⟩ := h80 w w1 hww1
  rw [hsigma2] at h_ww10 h_ww1pi
  -- 两组四点不共面
  have hcop1 : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw h_uw0 h_uwpi
  have hcop2 : ¬ Coplanar ({x, u, w, w1} : Set V3) :=
    properties_fully_surrounded hfan huw hww1 h_ww10 h_ww1pi
  -- 拆出不共线事实
  obtain ⟨hncuw, hncvu, hncvw⟩ := notcoplanar_imp_notcollinear_fan hcop1
  obtain ⟨hncww1, -, hncuw1⟩ := notcoplanar_imp_notcollinear_fan hcop2
  have hncuw' : ¬ Collinear3 x w u := collinear3_swap_ca11 hncuw
  have hncwv' : ¬ Collinear3 x w v := collinear3_swap_ca11 hncvw
  -- 由 `azim_compl` 把方位角等式翻转为 `azim x w u v = azim x w u w1`
  have hazim' : azim x w u v = azim x w u w1 := by
    by_cases h0 : azim x w u v = 0
    · have hv0 : azim x w v u = 0 := azim_compl_eq_zero hncuw' hncwv' h0
      have hw1u0 : azim x w w1 u = 0 := by rw [← hazim]; exact hv0
      have huw10 : azim x w u w1 = 0 := (azim_eq_zero_symm hncuw' hncww1).mpr hw1u0
      rw [h0, huw10]
    · have hne2 : azim x w u w1 ≠ 0 := by
        intro h
        have hw1u0 : azim x w w1 u = 0 := (azim_eq_zero_symm hncuw' hncww1).mp h
        have hvu0 : azim x w v u = 0 := by rw [hazim]; exact hw1u0
        exact h0 ((azim_eq_zero_symm hncuw' hncwv').mpr hvu0)
      have hc1 : azim x w v u = 2 * Real.pi - azim x w u v := by
        rw [azim_compl hncuw' hncwv', if_neg h0]
      have hc2 : azim x w w1 u = 2 * Real.pi - azim x w u w1 := by
        rw [azim_compl hncuw' hncww1, if_neg hne2]
      have h := hazim
      rw [hc1, hc2] at h
      linarith
  -- `AZIM_EQ_ALT`：`v` 落在 `aff_gt {x,w} {w1}`
  have hv : v ∈ affGt ({x, w} : Set V3) {w1} :=
    (azim_eq_azim_iff_alt hncuw' hncwv' hncww1).mp hazim'
  have hdisww1 : Disjoint ({x} : Set V3) {w, w1} :=
    disjoint_singleton_of_nc_ca11 hncww1
  have hv_ge : v ∈ affGe ({x, w} : Set V3) {w1} :=
    affGt_subset_affGe_ca11 _ _ hv
  -- 平面分解：要么 `w1 ∈ aff_gt {x}{v,w}`，要么 `v ∈ aff_ge {x}{w,w1}`
  have hdecomp : w1 ∈ affGt ({x} : Set V3) {v, w} ∨
      v ∈ affGe ({x} : Set V3) {w, w1} := by
    have h := decomposition_planar_by_angle_fan (x := x) (v := w) (u := w1) (w := v)
      hncww1 hncwv' hv_ge
    rw [show ({w, v} : Set V3) = {v, w} from by ext z; simp; tauto] at h
    exact h
  -- 取出 `aff_gt {x}{v,w} ∩ xfan` 中的见证点
  have hne : (affGt ({x} : Set V3) {v, w} ∩ xfan x V E).Nonempty := by
    rcases hdecomp with hcase | hcase
    · exact ⟨w1, hcase, ({w, w1} : Set V3), hww1, (point_in_aff_ge hncww1).2.2⟩
    · obtain ⟨y, hy⟩ := exists_in_aff_gt (x := x) (v := v) (u := w) hncvw
      have hsub : affGt ({x} : Set V3) {v, w} ⊆ affGe ({x} : Set V3) {w, w1} :=
        aff_gt12_subset_aff_ge (x := x) (v := w) (u := w1) (v1 := v) hdisww1 hncvw hcase
      exact ⟨y, hy, ({w, w1} : Set V3), hww1, hsub hy⟩
  exact AFF_GT_CUT_XFAN_IMP_EDGE_FAN hfan hvu huw hsigma1 hcard h80 hne.ne_empty

/-- HOL Conforming.hl :2758-2819 `condition_azim_le_pi`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w.
FAN(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
==> &0< azim x w v u/\ azim x w v u < pi
```

编码说明：`&0< ...` ↔ `0 < ...`；`pi` ↔ `Real.pi`；其余同
`condition_azim_imp_edge_fan`（内层 `!v` 改名 `v'`）。

证明思路：由 `fan80` 与 `sigma_fan x V E u w = v` 得
`0 < azim x u w v ∧ azim x u w v < π`（`properties_fully_surrounded`）；
`cross_dot_fully_surrounded_fan` 给出叉积-点积的符号条件，配合
`AZIM_COMPL`（`azim_compl`）与 `azim` 的值域 `0 ≤ azim < 2π` 把
`azim x w v u` 夹到 `(0, π)`：先用 `azim_eq_zero_iff` 排除 `= 0`，
再分 `π ≤ azim x w v u` 与 `< π` 两支，前者由 `azim_compl` 转化为
`azim x w u v` 的符号矛盾。

候选已有引理：
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim`（Kepler/Geom/Azim.lean:58）
- 缺口：HOL `AZIM_EQ_0_PI_EQ_COPLANAR` 未移植，用 `azim_eq_zero_iff`
  （Kepler/Geom/AzimLemmas.lean:296）替代 -/
theorem condition_azim_le_pi (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w : V3) :
    FAN x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧
    sigmaFan x V E u w = v ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) →
      0 < azim x w v u ∧ azim x w v u < Real.pi := by
  rintro ⟨hfan, hvu, huw, hsigma, h80, hcard⟩
  have hθ : 0 < azim x u w v ∧ azim x u w v < Real.pi := by
    have h := h80 u w huw
    rw [hsigma] at h
    exact h
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ.1 hθ.2
  have h1 : 0 < azim x v u w ∧ azim x v u w < Real.pi :=
    properties_of_fully_surrounded1_fan (x := x) (v := v) (u := u) (w := w)
      hcop hθ.1 hθ.2
  have hset : ({x, w, v, u} : Set V3) = ({x, v, u, w} : Set V3) := by
    ext z; simp; tauto
  exact properties_of_fully_surrounded1_fan (x := x) (v := w) (u := v) (w := u)
    (by rwa [hset]) h1.1 h1.2

/-- HOL Conforming.hl :2820-2931 `azim_trangle_le_azim_face_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w w1.
FAN(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E /\  {w,w1} IN E  /\ ~({v,w} IN E)
/\ sigma_fan x V E u w = v
/\ sigma_fan x V E w w1 = u
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
==> azim x w v u < azim x w w1 u
```

编码说明：`~({v,w} IN E)` ↔ `({v, w} : Set V3) ∉ E`；其余同
`condition_azim_imp_edge_fan`（内层 `!v` 改名 `v'`）。

证明思路：由 `condition_azim_imp_edge_fan` 与 `{v,w} ∉ E` 反设
`azim x w w1 u ≤ azim x w v u`；`sum5_azim_fan` 给出
`azim x w v u = azim x w v w1 + azim x w w1 u`，结合 `condition_azim_le_pi`
（`azim x w w1 u > 0`）把问题化为比较 `w1` 与 `aff_gt {x,w} {v,u}`
（`WEDGE_LUNE_GT`，未移植）；用 `inter_aff_gt_3_1_is_aff_gt_2_2`、
`aff_gt_3_1_rep_cross_dot`、`invariant_crossr_dot_esilon_3piont` 取
`w1` 附近的点落入 `affGt {x} {v,u,w}`，再由
`aff_gt_1_3_subset_dart_leads_into_fan` 与 `topological_component_subset_yfan`
得该点属于 `yfan`，与 `w1` 的定义域矛盾。

候选已有引理：
- `condition_azim_imp_edge_fan`、`condition_azim_le_pi`（本文件上文）
- `sum5_azim_fan`（Kepler/Text/TopologyFan.lean:1175）
- `inter_aff_gt_3_1_is_aff_gt_2_2`（Kepler/Text/PlanarityAuto14.lean:468）
- `invariant_crossr_dot_esilon_3piont`（Kepler/Text/PlanarityAuto10.lean:737）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `aff_gt_1_3_subset_dart_leads_into_fan`（Kepler/Text/PlanarityAuto12.lean:270）
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- 缺口：HOL `WEDGE_LUNE_GT` 未移植 -/
theorem azim_trangle_le_azim_face_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w w1 : V3) :
    FAN x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧
    ({w, w1} : Set V3) ∈ E ∧ ({v, w} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    sigmaFan x V E w w1 = u ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) →
      azim x w v u < azim x w w1 u := by
  rintro ⟨hfan, hvu, huw, hww1, hvw_not, hsigma1, hsigma2, h80, hcard⟩
  by_contra hnot
  have hle : azim x w w1 u ≤ azim x w v u := not_lt.mp hnot
  -- fan80 给出的两组方位角界
  have hθw1 : 0 < azim x w w1 u ∧ azim x w w1 u < Real.pi := by
    have := h80 w w1 hww1
    rwa [hsigma2] at this
  have hθuw : 0 < azim x u w v ∧ azim x u w v < Real.pi := by
    have := h80 u w huw
    rwa [hsigma1] at this
  -- 两组四点不共面
  have hcop1 : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθuw.1 hθuw.2
  have hcop2 : ¬ Coplanar ({x, u, w, w1} : Set V3) :=
    properties_fully_surrounded hfan huw hww1 hθw1.1 hθw1.2
  -- 拆出不共线事实
  obtain ⟨hnc_uw, hnc_vu, hnc_vw⟩ := notcoplanar_imp_notcollinear_fan hcop1
  obtain ⟨hnc_ww1, -, -⟩ := notcoplanar_imp_notcollinear_fan hcop2
  have hnc_wv : ¬ Collinear3 x w v := collinear3_swap_ca11 hnc_vw
  have hnc_wu : ¬ Collinear3 x w u := collinear3_swap_ca11 hnc_uw
  have hxw : x ≠ w := fun h =>
    hnc_wv (collinear3_of_eq (v := x) (w := w) (w1 := v) h.symm)
  have hxw1 : x ≠ w1 := fun h =>
    hnc_ww1 (collinear3_pair_left (v0 := x) (v1 := w) (x := w1) h.symm)
  have hww1ne : w ≠ w1 := fun h =>
    hnc_ww1 (collinear3_pair_right (v0 := x) (v1 := w) (x := w1) h.symm)
  -- `{v,w} ∉ E` 把方位角等式排除
  have hne : azim x w v u ≠ azim x w w1 u := by
    intro heq
    exact hvw_not (condition_azim_imp_edge_fan x V E v u w w1
      ⟨hfan, hvu, huw, hww1, hsigma1, hsigma2, h80, hcard, heq⟩)
  -- 角分解
  have hsum : azim x w v u = azim x w v w1 + azim x w w1 u :=
    sum5_azim_fan (v := w) (u := v) (w1 := w1) (w2 := u)
      hxw.symm hnc_wv hnc_ww1 hnc_wu hle
  have hApos : 0 < azim x w v w1 := by
    have hA0 : 0 ≤ azim x w v w1 := by linarith [hsum, hle]
    have hAne : azim x w v w1 ≠ 0 := by
      intro h0
      exact hne (by rw [hsum, h0]; ring)
    exact lt_of_le_of_ne hA0 (Ne.symm hAne)
  have hAlt : azim x w v w1 < azim x w v u := by linarith [hsum, hθw1.1]
  have hθvu : 0 < azim x w v u ∧ azim x w v u < Real.pi :=
    condition_azim_le_pi x V E v u w ⟨hfan, hvu, huw, hsigma1, h80, hcard⟩
  -- `w1` 落在楔形，进而落在 `affGt {x,w} {v,u}`
  have hw1_wedge : w1 ∈ wedge x w v u := by
    simp only [wedge, Set.mem_setOf_eq]
    exact ⟨hnc_ww1, hApos, hAlt⟩
  have hwedge_eq := wedge_eq_affGt (v0 := x) (v1 := w) (w1 := v) (w2 := u)
    hnc_wv hnc_wu hθvu.1 hθvu.2
  have hw1_affGt : w1 ∈ affGt ({x, w} : Set V3) {v, u} := by
    rw [hwedge_eq] at hw1_wedge
    exact hw1_wedge
  -- 不交性，用于 `affGt2_2` 系数分解
  obtain ⟨hxv, hxu, -, -, hvw, huw_ne⟩ := notcoplanar_disjoint x v u w hcop1
  have hdis_xw_vu : Disjoint ({x, w} : Set V3) {v, u} := by
    rw [Set.disjoint_left]
    intro a ha ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
    rcases ha with rfl | rfl
    · rcases ha' with rfl | rfl
      · exact hxv rfl
      · exact hxu rfl
    · rcases ha' with rfl | rfl
      · exact hvw rfl
      · exact huw_ne rfl
  rw [affGt2_2 (x := x) (u := w) (v := v) (w := u) hdis_xw_vu,
    Set.mem_setOf_eq] at hw1_affGt
  obtain ⟨t1, t2, t3, t4, ht3, ht4, htsum, hw1eq⟩ := hw1_affGt
  -- 选取小参数 `h`
  set M : ℝ := |t2| + 1 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  set h : ℝ := min (1 / 2) (1 / (2 * M)) with hh
  have hpos : 0 < h := by
    rw [hh]
    exact lt_min (by norm_num) (by positivity)
  have hle_half : h ≤ 1 / 2 := by rw [hh]; exact min_le_left _ _
  have hlt1 : h < 1 := lt_of_le_of_lt hle_half (by norm_num)
  have hcoef : 0 < (1 - h) + h * t2 := by
    have hleM : h * M ≤ 1 / 2 := by
      have hle : h ≤ 1 / (2 * M) := by rw [hh]; exact min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hMpos)
      have heq : (1 / (2 * M)) * M = 1 / 2 := by
        field_simp [hMpos.ne']
      rw [heq] at hmul
      exact hmul
    have h1mt2 : 1 - t2 ≤ M := by
      rw [hM]
      linarith [neg_le_abs t2]
    have hmul2 := mul_le_mul_of_nonneg_left h1mt2 (le_of_lt hpos)
    have hle3 : h * (1 - t2) ≤ 1 / 2 := le_trans hmul2 hleM
    have hrw : (1 - h) + h * t2 = 1 - h * (1 - t2) := by ring
    rw [hrw]
    linarith
  -- 见证点
  set y : V3 := (1 - h) • w + h • w1 with hydef
  obtain ⟨-, -, -, hdis_x_vuw, -, -, -, -⟩ := notcoplanar_disjoints x v u w hcop1
  have hy_affGt : y ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
    rw [AFF_GT_1_3 x v u w hdis_x_vuw, Set.mem_setOf_eq]
    refine ⟨h * t1, h * t3, h * t4, (1 - h) + h * t2,
      mul_pos hpos ht3, mul_pos hpos ht4, hcoef, ?_, ?_⟩
    · nlinarith [htsum]
    · rw [hydef, hw1eq]; module
  have hy_yfan : y ∈ yfan x V E :=
    aff_gt_1_3_subset_yfan x V E v u w hfan hvu huw hsigma1 hcard h80 hy_affGt
  have hy_affGe : y ∈ affGe ({x} : Set V3) ({w, w1} : Set V3) := by
    refine Affsign.of_triple (sgn := fun r => 0 ≤ r) (x := x) (v := w) (u := w1)
      (y := y) (1 - h) h ?_ ?_ ?_ hxw hxw1 hww1ne
    · linarith
    · exact le_of_lt hpos
    · rw [hydef]; module
  have hy_xfan : y ∈ xfan x V E := AFF_GE_SUBSET_XFAN x V E w w1 hww1 hy_affGe
  obtain ⟨-, hy_notxfan⟩ := hy_yfan
  exact hy_notxfan hy_xfan

/-! ## 加边后 σ 的取值（Conforming.hl:2932-3602） -/

/-- HOL Conforming.hl :2932-3072 `SIGMA_FAN_OF_FANADD_AT_POINT3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 v u w.
FAN(x,V,E)/\ FAN(x,V,E1)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 w v = u
```

编码说明：`E UNION {{v,w}} = E1` ↔ `E ∪ {({v, w} : Set V3)} = E1`；内层
`!v` 改名 `v'`；其余同 `condition_azim_imp_edge_fan`。

证明思路：由 `add_edge_graph` 得 `{v,w} ∈ E1`，由
`add_edge_imp_card_set_edge_ge1_fan` 得 `E1` 上最小度条件，故
`setOfEdge w V E1 ≠ {v}`；对 `E1` 用 `UNIQUE_SIGMA_FAN`
（`unique_sigma_fan`）把结论化为 `u ∈ setOfEdge w V E1` 且 `u` 使方位角
最小；`{u,w} ∈ E ⊆ E1` 给成员性，最小性由 `SIGMA_FAN` 在 `E` 上的最小性
经 `SET_OF_EDGE_UNION_GRAPH`、`set_of_only_edge1` 与
`azim_trangle_le_azim_face_fan`、`sum5_azim_fan` 的角度比较搬过去。

候选已有引理：
- `azim_trangle_le_azim_face_fan`（本文件上文）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`、`SIGMA_FAN_OF_FANADD_AT_POINT2`
  （Kepler/Text/ConformingAuto10.lean:399/510）
- `unique_sigma_fan`（Kepler/Text/ConformingAuto10.lean:336，private）
- `add_edge_graph_of_fanadd`（Kepler/Text/ConformingAuto10.lean:230）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `SET_OF_EDGE_UNION_GRAPH`（Kepler/Text/ConformingAuto9.lean:344）
- `set_of_only_edge1`（Kepler/Text/ConformingAuto10.lean:312）
- `sum5_azim_fan`、`sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1175/1105）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- 缺口：HOL `remark1_fan`（fan.hl:423）未以该名移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT3 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      sigmaFan x V E1 w v = u := by
  sorry

/-- HOL Conforming.hl :3073-3274 `SIGMA_FAN_OF_FANADD_AT_POINT4`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w w1.

FAN(x,V,E)/\ FAN(x,V,E1)
/\ fan80(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E) /\ ~(u=w1)
/\ {v,w1} IN E
/\ sigma_fan x V E u w = v
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 v w1 = sigma_fan x V E v w1
```

编码说明：`~(u=w1)` ↔ `u ≠ w1`；内层 `!v` 改名 `v'`；其余同
`SIGMA_FAN_OF_FANADD_AT_POINT3`。

证明思路：由 `add_edge_imp_card_set_edge_ge1_fan` 得
`setOfEdge v V E1 ≠ {w1}`；对 `E1` 用 `UNIQUE_SIGMA_FAN` 把结论化为
`sigma_fan x V E v w1` 是 `v` 在 `E1` 中的最小方位角邻居；由
`add_edge_graph` 与 `SET_OF_EDGE_UNION_GRAPH` 把 `setOfEdge v V E1`
写成 `setOfEdge v V E ∪ {w}`，于是只需比较 `w` 与 `w1` 的方位角：
用 `angle_is_small_fan`、`sum3_azim_fan`/`sum4_azim_fan`、
`azim_compl`、`AZIM_EQ_0_*`（`azim_eq_zero_iff`/`azim_eq_zero_iff_alt`）
与 `condition_aff_gt_subset_yfan` 排除边界情形。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `angle_is_small_fan`（Kepler/Text/PlanarityAngle.lean:490）
- `sum3_azim_fan`、`sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1137/1105）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_zero_iff`、`azim_eq_zero_iff_alt`（Kepler/Geom/AzimLemmas.lean:296/307）
- `unique_azim_point_fan`（Kepler/Text/Fan.lean:463）
- `condition_aff_gt_subset_yfan`（Kepler/Text/ConformingAuto8.lean:629）
- `AFF_GT_CUT_XFAN_IMP_EDGE_FAN`（Kepler/Text/AffGtCut.lean:669）
- 缺口：HOL `MONO_AZIM_SIGMA_FAN`（fan.hl）、`remark1_fan`（fan.hl:423）
  未以该名移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT4 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w w1 : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    fan80 x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    u ≠ w1 ∧
    ({v, w1} : Set V3) ∈ E ∧
    sigmaFan x V E u w = v ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      sigmaFan x V E1 v w1 = sigmaFan x V E v w1 := by
  sorry

/-- HOL Conforming.hl :3275-3475 `SIGMA_FAN_OF_FANADD_AT_POINT5`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w w1.

FAN(x,V,E)/\ FAN(x,V,E1)
/\ fan80(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E) /\ ~(w1=inverse1_sigma_fan x V E w u )
/\ {w,w1} IN E
/\ sigma_fan x V E u w = v
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 w w1 = sigma_fan x V E w w1
```

编码说明：`inverse1_sigma_fan` ↔ `inverse1SigmaFan`（Fan.lean:240）；
`~(w1=...)` ↔ `w1 ≠ ...`；内层 `!v` 改名 `v'`；其余同
`SIGMA_FAN_OF_FANADD_AT_POINT3`。

证明思路：由 `add_edge_imp_card_set_edge_ge1_fan` 得
`setOfEdge w V E1 ≠ {w1}`；对 `E1` 用 `UNIQUE_SIGMA_FAN` 化为证明
`sigma_fan x V E w w1` 是 `w` 在 `E1` 中的最小方位角邻居；由
`add_edge_graph` 与 `SET_OF_EDGE_UNION_GRAPH` 知新增邻居仅可能为 `v`；
设 `w2 = inverse1_sigma_fan x V E w u`，由 `INVERSE1_SIGMA_FAN` 与
`SIGMA_FAN` 的最小性、`MONO_AZIM_SIGMA_FAN`（未移植）、
`azim_trangle_le_azim_face_fan`、`sum3/4/5_azim_fan` 与 `azim_compl`
比较 `v`、`w2`、`w1` 的角度。

候选已有引理：
- `azim_trangle_le_azim_face_fan`（本文件上文）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `sum3_azim_fan`、`sum4_azim_fan`、`sum5_azim_fan`
  （Kepler/Text/TopologyFan.lean:1137/1105/1175）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296）
- `unique_azim_point_fan`（Kepler/Text/Fan.lean:463）
- 缺口：HOL `MONO_AZIM_SIGMA_FAN`（fan.hl）、`remark1_fan`（fan.hl:423）
  未以该名移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT5 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w w1 : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    fan80 x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    w1 ≠ inverse1SigmaFan x V E w u ∧
    ({w, w1} : Set V3) ∈ E ∧
    sigmaFan x V E u w = v ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      sigmaFan x V E1 w w1 = sigmaFan x V E w w1 := by
  sorry

/-- HOL Conforming.hl :3476-3602 `SIGMA_FAN_OF_FANADD_AT_POINT6`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w w1.
FAN(x,V,E)/\ FAN(x,V,E1)
/\ fan80(x,V,E)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E) /\ w1=inverse1_sigma_fan x V E w u
/\ {w,w1} IN E
/\ sigma_fan x V E u w = v
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 w w1 = v
```

编码说明：`inverse1_sigma_fan` ↔ `inverse1SigmaFan`（Fan.lean:240）；内层
`!v` 改名 `v'`；其余同 `SIGMA_FAN_OF_FANADD_AT_POINT3`。

证明思路：由 `add_edge_imp_card_set_edge_ge1_fan` 得
`setOfEdge w V E1 ≠ {w1}`；对 `E1` 用 `UNIQUE_SIGMA_FAN` 化为证明
`v` 是 `w` 在 `E1` 中的最小方位角邻居。由 `add_edge_graph` 得
`{v,w} ∈ E1` 故 `v ∈ setOfEdge w V E1`；设
`w1 = inverse1_sigma_fan x V E w u`，由 `INVERSE1_SIGMA_FAN`、
`SIGMA_FAN`、`sum5_azim_fan` 与 `azim_trangle_le_azim_face_fan` 比较
`v` 与任一邻居 `w1'` 的角度；边界情形用 `azim_eq_zero_iff`/
`azim_eq_zero_iff_alt` 与 `set_of_only_edge1` 排除。

候选已有引理：
- `azim_trangle_le_azim_face_fan`（本文件上文）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `sum5_azim_fan`（Kepler/Text/TopologyFan.lean:1175）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_zero_iff`、`azim_eq_zero_iff_alt`（Kepler/Geom/AzimLemmas.lean:296/307）
- `set_of_only_edge1`（Kepler/Text/ConformingAuto10.lean:312）
- `unique_azim_point_fan`（Kepler/Text/Fan.lean:463）
- 缺口：HOL `remark1_fan`（fan.hl:423）未以该名移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT6 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w w1 : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    fan80 x V E ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    w1 = inverse1SigmaFan x V E w u ∧
    ({w, w1} : Set V3) ∈ E ∧
    sigmaFan x V E u w = v ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      sigmaFan x V E1 w w1 = v := by
  sorry

/-! ## 加边后 f1_fan 的作用（Conforming.hl:3603-3689） -/

/-- HOL Conforming.hl :3603-3641 `f1_fan_of_f10_eq_f20`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ f10=(x,w,v,u)
/\ f20=(x,v,u,w)
/\ E UNION {{v,w}}= E1
==> f20=f1_fan x V E1 f10
```

编码说明：四元组 dart 用点对 `V3 × V3` 表示（PlanarityComponent.lean:37），
故 `f1,f2,f3 : V3 × V3`；`pr2 f1 = v` ↔ `f1.1 = v` 等；
`f1_fan` ↔ `f1Fan`（ConformingDefs.lean:87）；`face_set(hypermap1_of_fanx
(x,V,E))` ↔ `(hypermapOfFan x V E hfan).faceSet`，
`face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan ...)` 的收缩 dart 为
`(v,w)`，故编码为 `(hypermapOfFan x V E1 hfan1).face (v, w)`；`f10=(x,w,v,u)`
收缩为 `(w,v)`，`f20=(x,v,u,w)` 收缩为 `(v,u)`；`CARD ds >3` ↔
`3 < ds.ncard`；`E UNION {{v,w}}=E1` ↔ `E ∪ {({v, w} : Set V3)} = E1`。
偏差：HOL 未给 `FAN(x,V,E1)`（在 HOL 中由 `STEP3_REDUCE_FAN` 导出），
Lean 的 `hypermapOfFan` 需要见证，故增加显式参数 `(hfan1 : FAN x V E1)`
（与 ConformingDefs.lean:30-33 的约定一致）。

证明思路：由 `STEP3_REDUCE_FAN` 得 `FAN x V E1`；由
`hypermap_of_fan_rep`（未移植，可用 `hypermapOfFan_faceMap_eq` 的二元组
版本替代）把两幅 hypermap 的 face 映射化为 `f1Fan`；
`SIGMA_FAN_OF_FANADD_AT_POINT2` 给 `sigma_fan x V E1 v w`，再用
`INVERSE1_SIGMA_FAN` 对齐 `f1Fan` 的第二分量，最后 `f1Fan` 展开与
`EQ_PAIR`（`Prod.ext`）收尾。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `f1Fan`（Kepler/Text/ConformingDefs.lean:87）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `hypermapOfFan_faceMap_eq`（Kepler/Text/PlanarityComponent.lean:242，private；
  另有 ConformingAuto8.lean:432 / PlanarityAuto14.lean:732 的同型副本）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- 缺口：HOL `hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未以该名移植 -/
theorem f1_fan_of_f10_eq_f20 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      f20 = f1Fan x V E1 f10 := by
  sorry

/-- HOL Conforming.hl :3642-3689 `f1_fan_of_f20_eq_f30`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ f20=(x,v,u,w)
/\ f30=(x,u,w,v)
/\ E UNION {{v,w}}= E1
==> f30=f1_fan x V E1 f20
```

编码说明：同 `f1_fan_of_f10_eq_f20`；此处 `f20=(x,v,u,w)` 收缩为 `(v,u)`，
`f30=(x,u,w,v)` 收缩为 `(u,w)`。偏差同为增加显式参数
`(hfan1 : FAN x V E1)`。

证明思路：由 `STEP3_REDUCE_FAN` 得 `FAN x V E1`；由
`hypermap_of_fan_rep`（未移植，可用 `hypermapOfFan_faceMap_eq` 替代）与
`SIGMA_FAN_OF_FANADD1` 把 `sigma_fan x V E1 v u` 化为
`sigma_fan x V E v u` 再化为 `w`；用 `INVERSE1_SIGMA_FAN` 对齐
`f1Fan` 的第二分量（对 `u` 处取逆），最后展开 `f1Fan` 并用 `Prod.ext`
对齐两分量。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `f1Fan`（Kepler/Text/ConformingDefs.lean:87）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `hypermapOfFan_faceMap_eq`（Kepler/Text/PlanarityComponent.lean:242，private）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- 缺口：HOL `hypermap_of_fan_rep`（fan.hl:2780）、
  `dartset_fully_surrounded_is_non_isolated_fan` 未以该名移植 -/
theorem f1_fan_of_f20_eq_f30 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      f30 = f1Fan x V E1 f20 := by
  sorry

end Kepler.Text
