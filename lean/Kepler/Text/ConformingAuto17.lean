/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 17
(Conforming.hl:8259-9065).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 17, Conforming.hl:8259-9065):
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14` (8259)
- `lemmaINTERS_HALF_SPACE_DS_FANADD3` (8303)
- `aff_3_rep_cross_dot` (8401)
- `SPACE3_EQ_UNION_3SET` (8522)
- `lemmaU1_subset_U` (8622)
- `open_subsetU` (8684)
- `eq_aff_gt_3_fanadd_edge` (8812)
- `aff_gt_add_subset_U1` (8902)
- `lemma_rep_U_fanadd` (8958)
- `dartset_leads_into_ds_open_fanadd` (9008)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`; HOL `CARD ds > 3` ↔ `3 < ds.ncard`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, and `face (hypermap1_of_fanx
  (x,V,E)) f` as `(hypermapOfFan x V E hfan).face f`. Since
  `hypermapOfFan` (Kepler/Text/Fan.lean:1169) needs an explicit
  `hfan : FAN x V E`, every theorem that mentions it carries an extra
  explicit `(hfan : FAN x V E)` argument; theorems that also mention
  `hypermapOfFan x V E1` carry a second extra explicit argument
  `(hfan1 : FAN x V E1)`. These are the only deviations from the HOL
  signatures (HOL's `hypermap_of_fan` is total).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `aff s` (affine
  hull) ↔ `(affineSpan ℝ s : Set V3)`; HOL `open` ↔ `IsOpen`; HOL
  `(:real^3)` ↔ `Set.univ`; HOL `collinear` ↔ `Collinear3`
  (Kepler/Geom/Azim.lean:43); HOL `coplanar` ↔ `Coplanar`
  (Kepler/Geom/Coplanar.lean:23).
- HOL `(v - x) cross (u - x)` ↔ `crossProduct ((v - x : V3) : Fin 3 → ℝ)
  ((u - x : V3) : Fin 3 → ℝ)`; HOL `dot` ↔ `⬝ᵥ` (`dotProduct`).
- The inner quantifier `(!E1. ... ==> conforming_fan (x,V,E1))` shadows the
  outer `E1`; as in `minimallyNonconformingFan`
  (Kepler/Text/ConformingDefs.lean:226) the inner variable is renamed `E2`
  and, because `conformingFan`/`nFan` need a `FAN` witness, encoded as
  `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
  conformingFan x V E2 hfan2` (the `FAN x V E2` conjunct is kept to align
  with the HOL antecedent).
- None of the ten statements is a verbatim Mathlib theorem. The two
  geometric ones (`aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`,
  `aff_3_rep_cross_dot`) use repo-specific `affGt`/`Collinear3`/`Coplanar`
  (and the second has no Mathlib counterpart for the cross-dot
  characterisation of `affineSpan`), so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 几何表示引理（Conforming.hl:8259-8450） -/

/-- HOL Conforming.hl :8259-8302 `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`

HOL 原文：
```
!a x y z:real^3.
~coplanar {a, x, y, z}
==> aff_gt {a,x,y}{z} INTER aff{a,x,z} SUBSET aff_gt {a,x} {z}
```

编码说明：`coplanar` ↦ `Coplanar`；`aff_gt` ↦ `affGt`；`aff` ↦
`affineSpan ℝ`；`INTER`/`SUBSET` ↦ `∩`/`⊆`。结论
`affGt ({a, x, y} : Set V3) {z} ∩
(affineSpan ℝ ({a, x, z} : Set V3) : Set V3) ⊆ affGt ({a, x} : Set V3) {z}`。

证明思路：由 `~coplanar {a,x,y,z}` 得 `~collinear {a,x,z}` 与
`~collinear {a,x,y}`（`notcoplanar_imp_notcollinear_fan`）；用
`cross_dot_fully_surrounded_fan` 建立 `n = (x-a)⨯(y-a)` 对 `z` 的定向
符号；`aff_gt_3_1_rep_cross_dot` 把 `affGt {a,x,y}{z}` 化为
`0 < n·(p-a)`，`aff{a,x,z}` 展开为 `a + c•(x-a) + h•(z-a)`，代入后由
`n·(x-a)=0` 得 `n·(p-a)=h·(n·(z-a))` 且 `h>0`；再对 `affGt {a,x}{z}` 用
一次叉积表示即得。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `affGt`（Kepler/Geom/Aff.lean:39）
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- 缺口：`AFF_GT_2_1`/`AFF_GT_3_1` 的系数展开需手工桥接 `affineSpan` -/
theorem aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14 (a x y z : V3) :
    ¬ Coplanar ({a, x, y, z} : Set V3) →
      affGt ({a, x, y} : Set V3) {z} ∩
        (affineSpan ℝ ({a, x, z} : Set V3) : Set V3) ⊆
          affGt ({a, x} : Set V3) {z} := by
  sorry

/-- HOL Conforming.hl :8303-8400 `lemmaINTERS_HALF_SPACE_DS_FANADD3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}

==> U1 INTER aff {x,v,w} SUBSET  aff_gt {x} {v, w}
```

编码说明：内层 `!E1` 改名为 `E2`（携带 `hfan2`）；`INTER`/`SUBSET` ↦
`∩`/`⊆`；`aff` ↦ `affineSpan ℝ`；`U1` 定义为四个 `affGt` 之交。
结论 `U1 ∩ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ⊆
affGt ({x} : Set V3) {v, w}`。

证明思路：由 `fan80` 对 `(u,w)`、`(v,u)`、`(v,sigma_fan x V E v u)` 用
`properties_fully_surrounded` 得三组四点非共面；对 `U1` 的四个
`affGt` 分别用 `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1` 与
`aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14` 把半空间交约化为
`aff {x,v,w} ∩ …`，再用 `aff_gt_inter_aff_gt` 与 `SET_TAC` 收口。

候选已有引理：
- `lemmaINTERS_HALF_SPACE_DS_FANADD1`（Kepler/Text/ConformingAuto16.lean:1304）
- `lemmaINTERS_HALF_SPACE_DS_FANADD2`（Kepler/Text/ConformingAuto16.lean:1515）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`（Kepler/Text/ConformingAuto16.lean:1673）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`（本文件上文）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- 缺口：`AFF_GT_MONO_LEFT`、`remark1_fan` 未以该名移植 -/
theorem lemmaINTERS_HALF_SPACE_DS_FANADD3 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      U1 ∩ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ⊆
        affGt ({x} : Set V3) {v, w} := by
  sorry

/-- HOL Conforming.hl :8401-8521 `aff_3_rep_cross_dot`

HOL 原文：
```
!x:real^3  v:real^3 u:real^3.
~collinear {x,v,u}

==> aff {x,v,u} ={y:real^3|   (((v-x) cross (u-x)) dot (y-x)) = &0}
```

编码说明：`collinear` ↦ `Collinear3`；`aff` ↦ `affineSpan ℝ`；
`cross`/`dot` ↦ `crossProduct`/`⬝ᵥ`。结论
`(affineSpan ℝ ({x, v, u} : Set V3) : Set V3) =
{y : V3 | crossProduct ((v-x):Fin 3→ℝ) ((u-x):Fin 3→ℝ) ⬝ᵥ ((y-x):Fin 3→ℝ) = 0}`。
这是纯几何（Mathlib 通用词汇）的命题，但 Mathlib 没有把 `affineSpan`
等同于「位移与叉积正交」的现成定理，故仍按 HOL 移植。

证明思路：`⊆` 方向把 `y = u'•x + v'•v + w•u`（系数和 1）代入
`(v-x)⨯(u-x) · (y-x)`，用叉积/点积双线性、`cross_refl`、
`dot_cross_self` 化简为 0。`⊇` 方向由 `~collinear` 取标准正交标架
`e1,e2,e3`（`e1Fan`/`e2Fan`/`e3Fan`）展开坐标，解线性方程组给出
`affineSpan` 的系数。

候选已有引理：
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `crossProduct`（Mathlib/LinearAlgebra/CrossProduct.lean）
- `dot_self_cross` / `dot_cross_self`（Mathlib）
- `affineSpan`（Mathlib）
- `e1Fan`/`e2Fan`/`e3Fan`（Kepler/Text/TopologyFan.lean:2486 附近）
- 缺口：HOL `properties_coordinate`/`ORTHONORMAL_IMP_SPANNING`/
  `ORTHONORMAL_CROSS` 未以该名移植 -/
theorem aff_3_rep_cross_dot (x v u : V3) :
    ¬ Collinear3 x v u →
      (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) =
        {y : V3 | crossProduct ((v - x : V3) : Fin 3 → ℝ)
            ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) = 0} := by
  sorry

/-! ## 空间分解与 U1/U 的包含关系（Conforming.hl:8522-9065） -/

/-- HOL Conforming.hl :8522-8621 `SPACE3_EQ_UNION_3SET`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> aff {x,v,w} UNION aff_gt {x, v, w} {sigma_fan x V E v u} UNION aff_gt {x, v, w} {u}= (:real^3)
```

编码说明：注意本定理的假设块没有内层 `!E1` conforming 子句；`aff` ↦
`affineSpan ℝ`；`aff_gt` ↦ `affGt`；`(:real^3)` ↦ `Set.univ`。结论
`(affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ∪
affGt ({x, v, w} : Set V3) {u} = Set.univ`。

证明思路：由 `fan80` 与 `properties_fully_surrounded` 得
`~collinear {x,w,v}`、`~collinear {x,v,sigma_fan x V E v u}` 等；用
`aff_3_rep_cross_dot` 把 `aff {x,v,w}` 化为叉积正交条件，用
`aff_gt_3_1_rep_cross_dot` 把两个开半空间化为叉积定向条件
（`cross_dot_fully_surrounded_fan` 定符号），对任意 `y` 按
`(w-x)⨯(v-x)·(y-x)` 与 `(v-x)⨯(sigma_fan …-x)·(y-x)` 的符号分类
（`REAL_ARITH`）即得三集之并覆盖全空间。

候选已有引理：
- `aff_3_rep_cross_dot`（本文件上文）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- 缺口：`AFF_GT_3_1` 的系数展开与 `AFF_GT_3_1_REP_CROSS_DOT` 的
  定向重排需手工桥接 -/
theorem SPACE3_EQ_UNION_3SET (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
        affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ∪
        affGt ({x, v, w} : Set V3) {u} = Set.univ := by
  sorry

/-- HOL Conforming.hl :8622-8683 `lemmaU1_subset_U`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
==> U1 SUBSET U
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；`UNION` ↦
`∪`；`U1` 为四 `affGt` 之交，`U` 为两个 `dartsetLeadsIntoFan` 与
`affGt {x}{v,w}` 之并。结论 `U1 ⊆ U`。

证明思路：由 `lemmaINTERS_HALF_SPACE_DS_FANADD1/2/3` 把 `U1` 的三个
分量分别包含进 `dartsetLeadsIntoFan x V E1 ds1`/`ds2`；由
`SPACE3_EQ_UNION_3SET` 得 `aff {x,v,w} ∪ affGt {x,v,w}{…} ∪ affGt {x,v,w}{u}
= univ`，配合 `lemmaINTERS_HALF_SPACE_DS_FANADD3` 的
`U1 ∩ aff {x,v,w} ⊆ affGt {x}{v,w}` 与集合运算（`SET_TAC`）收口。

候选已有引理：
- `lemmaINTERS_HALF_SPACE_DS_FANADD1/2/3`
  （Kepler/Text/ConformingAuto16.lean:1304/1515、本文件上文）
- `SPACE3_EQ_UNION_3SET`（本文件上文）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- 缺口：`FAN80_FANADD` 之外的 fanadd 引理按名引用，未逐一桥接 -/
theorem lemmaU1_subset_U (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} ∧
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} →
      U1 ⊆ U := by
  sorry

/-- HOL Conforming.hl :8684-8811 `open_subsetU`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\  U=aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> open U
```

编码说明：`open` ↦ `IsOpen`；`U` 为四 `affGt` 之交。结论 `IsOpen U`。

证明思路：`U` 是四个 `affGt` 之交，逐个用 `OPEN_AFF_GT_3_1` 证开
（每个 `affGt {x,·,·}{·}` 需要对应三点非共线，由 `fan80` 与
`properties_fully_surrounded` 提供；`sigma_fan` 的第三点用
`SIGMA_FAN_OF_FANADD_AT_POINT1` 换到 `E1`），再三次 `IsOpen.inter`
收口。

候选已有引理：
- `OPEN_AFF_GT_3_1`（Kepler/Text/ConformingAuto5.lean:433）
- `IsOpen.inter`（Mathlib/Topology/Defs/Basic.lean）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `sigma_fan_in_setOfEdge`（Kepler/Text/Fan.lean:326）
- 缺口：`remark1_fan` 未以该名移植 -/
theorem open_subsetU (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      IsOpen U := by
  sorry

/-- HOL Conforming.hl :8812-8901 `eq_aff_gt_3_fanadd_edge`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
==> aff_gt {x, v, u} {sigma_fan x V E v u}= aff_gt {x, v, u} {w}
```

编码说明：`aff_gt` ↦ `affGt`；结论
`affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} =
affGt ({x, v, u} : Set V3) {w}`。

证明思路：由 `fan80` 对 `(v,u)` 与 `(v,sigma_fan x V E v u)` 用
`properties_fully_surrounded` 得两组四点非共面；用
`cross_dot_fully_surrounded_fan` 定两个叉积定向符号，
`aff_gt_3_1_rep_cross_dot` 把左右两个 `affGt` 都化为同一叉积正条件
（`SIGMA_FAN_OF_FANADD_AT_POINT2` 把 `sigma_fan` 换到 `E1` 侧）。

候选已有引理：
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `aff_gt_eq_fanadd`（Kepler/Text/ConformingAuto16.lean:597）
- 缺口：`remark1_fan` 未以该名移植 -/
theorem eq_aff_gt_3_fanadd_edge (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) →
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} =
        affGt ({x, v, u} : Set V3) {w} := by
  sorry

/-- HOL Conforming.hl :8902-8957 `aff_gt_add_subset_U1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> aff_gt {x} {v,w} SUBSET U1
```

编码说明：`aff_gt` ↦ `affGt`；`SUBSET` ↦ `⊆`；`U1` 为四 `affGt`
之交。结论 `affGt ({x} : Set V3) {v, w} ⊆ U1`。

证明思路：`eq_aff_gt_3_fanadd_edge` 把 `affGt {x,v,u}{sigma_fan …}` 换成
`affGt {x,v,u}{w}`；`aff_gt_inter_aff_gt` 把 `affGt {x}{v,w}` 化为
`affGt {x,v}{w} ∩ affGt {x,w}{v}`；再用 `AFF_GT_MONO_LEFT`（各分量对
左端集合单调）把 `affGt {x,v}{w}`、`affGt {x,w}{v}` 分别塞进 `U1`
的四个 `affGt` 分量（`SET_TAC` 收口）。

候选已有引理：
- `eq_aff_gt_3_fanadd_edge`（本文件上文）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`（Kepler/Text/ConformingAuto16.lean:1673）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- 缺口：`AFF_GT_MONO_LEFT`、`remark1_fan` 未以该名移植 -/
theorem aff_gt_add_subset_U1 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      affGt ({x} : Set V3) {v, w} ⊆ U1 := by
  sorry

/-- HOL Conforming.hl :8958-9007 `lemma_rep_U_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\  U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> U= U1 UNION dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；`UNION` ↦
`∪`。结论 `U = U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪
dartsetLeadsIntoFan x V E1 ds2`。

证明思路：`U` 定义中已有两个 `dartsetLeadsIntoFan` 分量，只需把
`affGt {x}{v,w}` 并入 `U1`：`aff_gt_add_subset_U1` 给
`affGt {x}{v,w} ⊆ U1`，`lemmaU1_subset_U` 给 `U1 ⊆ U`，再用集合运算
（`SET_TAC`）证两边互含。

候选已有引理：
- `aff_gt_add_subset_U1`（本文件上文）
- `lemmaU1_subset_U`（本文件上文）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- 缺口：`FANADD_CONFORMING` 的展开按名引用，未逐一桥接 -/
theorem lemma_rep_U_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      U = U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪
        dartsetLeadsIntoFan x V E1 ds2 := by
  sorry

/-- HOL Conforming.hl :9008-9065 `dartset_leads_into_ds_open_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}=U
==> open U
```

编码说明：`open` ↦ `IsOpen`；`U` 为两个 `dartsetLeadsIntoFan` 与
`affGt {x}{v,w}` 之并。结论 `IsOpen U`。

证明思路：`lemma_rep_U_fanadd` 把 `U` 重写为
`U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2`；
`open_subsetU` 给 `IsOpen U1`；`FANADD_CONFORMING` 与
`ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd` 使两个
`dartsetLeadsIntoFan` 是 `topologicalComponentYfan`，再由
`OPEN_TOPOLOGICAL_COMPONENT_YFAN` 得开；最后两次 `IsOpen.union` 收口。

候选已有引理：
- `lemma_rep_U_fanadd`（本文件上文）
- `open_subsetU`（本文件上文）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `dartset_leads_into_is_topological_component_yfan`（Kepler/Text/PlanarityComponent.lean:535）
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN`（Kepler/Text/ConformingAuto6.lean:317）
- `IsOpen.union`（Mathlib/Topology/Defs/Basic.lean）
- 缺口：`OPEN_TOPOLOGICAL_COMPONENT_YFAN` 的 `E1` 版本按名引用 -/
theorem dartset_leads_into_ds_open_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} = U →
      IsOpen U := by
  sorry

end Kepler.Text
