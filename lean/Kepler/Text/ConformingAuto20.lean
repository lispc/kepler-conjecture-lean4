/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 20
(Conforming.hl:12512-13673).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 20, Conforming.hl:12512-13673):
- `TXFBALB_VERSION` (12512)
- `conforming_bijection_fanadd_verrion` (12539)  [HOL's own typo "verrion",
  kept verbatim]
- `inverse1_sigma_fan_FANADD4` (12569)
- `conforming_diagonal_fanadd1` (12682)
- `INDUCTION_FANADD` (13011)
- `conforming_diagonal_fan_ds_fanadd` (13204)
- `GGZWYRM` (13253)
- `INTERS_HALF_SPACE_DS_FANADD3` (13309)  [HOL line reads "let  INTERS_..."
  with two spaces; the name has no leading space]
- `lemma_HYUAZSE` (13460)
- `DART_FANADD_SUBSET_HALFSPACE` (13518)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL darts
  `real^3#real^3#real^3#real^3` ↔ pair darts `V3 × V3`
  (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`;
  the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`, `(x,u,w,v)` contract to the
  pairs `(w,v)`, `(v,u)`, `(u,w)`, and `(x,v,w,sigma_fan x V E1 v w)` /
  `(x,w,v,sigma_fan x V E1 w v)` to the pairs `(v,w)` / `(w,v)` (same
  conventions as batches 16-19).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); `set_of_edge` ↦
  `setOfEdge` (Kepler/Text/Fan.lean:62); `sigma_fan` ↦ `sigmaFan`
  (Kepler/Text/Fan.lean:67); `fan80` ↦ `fan80` (Kepler/Text/Fan.lean:227);
  `inverse1_sigma_fan` ↦ `inverse1SigmaFan` (Kepler/Text/Fan.lean:240);
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`; HOL
  `CARD ds >3` ↔ `3 < ds.ncard`.
- FAN-witness arguments: `hypermapOfFan` (Kepler/Text/Fan.lean:1169) and the
  ConformingDefs predicates `conformingFan`/`conformingSolidAngleFan`/
  `conformingDiagonalFan`/`nFan` need an explicit `FAN` witness, so each
  theorem mentioning them carries an extra explicit `(hfan : FAN x V E)`
  (and `(hfan1 : FAN x V E1)` when `face (hypermap1_of_fanx (x,V,E1)) ...`
  occurs). These are the only deviations from the HOL signatures.
- HOL `face_set(hypermap1_of_fanx (x,V,E))` ↦
  `(hypermapOfFan x V E hfan).faceSet`; `face (hypermap1_of_fanx (x,V,E)) d`
  ↦ `(hypermapOfFan x V E hfan).face d`; `dartset_leads_into_fan` ↦
  `dartsetLeadsIntoFan` (Kepler/Text/PlanarityComponent.lean:348);
  `topological_component_yfan` ↦ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); `f1_fan` ↦ `f1Fan`
  (Kepler/Text/ConformingDefs.lean:87).
- HOL `?!f. P f` (unique existence) ↦ `∃! f, P f`.
- `INDUCTION_FANADD`'s conclusion `?f1 f2 f3. ...` binds fresh variables
  shadowing the outer parameters `f1 f2 f3`; per the batch-18 shadowing
  convention the inner binders are renamed `f1' f2' f3'` (the final conjunct
  `y=f3` refers to the inner binder and is written `y = f3'`).
- HOL `INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y)} | y IN ds}`
  ↦ `⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}` (same
  encoding as `conformingHalfSpaceFan`, Kepler/Text/ConformingDefs.lean:121,
  and `INTERS_HALF_SPACE_DS_FANADD1/2`, Kepler/Text/ConformingAuto16.lean).
- HOL `aff s` (affine hull) ↦ `(affineSpan ℝ s : Set V3)` (same encoding as
  batch 17, Kepler/Text/ConformingAuto17.lean:56-57); `collinear` ↦
  `Collinear3` (Kepler/Geom/Azim.lean:43); `aff_gt` ↦ `affGt`
  (Kepler/Geom/Aff.lean:39); `INTER`/`SUBSET`/`UNION`/`DELETE` ↦
  `∩`/`⊆`/`∪`/`\`.
- Dependencies on earlier batches are imported: this file imports
  `Kepler.Text.ConformingAuto19` (which transitively pulls
  `ConformingAuto18`, hence 17/16/15/14/12/... and `TXFBALB`
  (Kepler/Text/ConformingAuto19.lean:1487) and `conforming_bijection_fanadd`
  (Kepler/Text/ConformingAuto18.lean:1166)) plus `ConformingDefs` and
  `PlanarityAuto16` directly. NOTE: `TXFBALB`'s proof is still `sorry` in
  batch 19 (proof in progress in the other lane); `TXFBALB_VERSION` below is
  stated so that the pool can prove it from `TXFBALB` once that proof lands.
- HOL notions NOT ported that the HOL proofs use (the pool proofs must work
  around them): `dartset_fully_surrounded_is_non_isolated_fan`, `remark1_fan`,
  `MONO_SIGMA_FAN`, `properties_of_f1_fan`, `f_fan_no_fix_point`,
  `into_domain_power_efn_fan`/`into_domain1_power_efn_fan`,
  `lemma_face_identity`/`lemma_face_cycle`, `sigma_fan_in_set_of_edge`,
  `NOT_COPLANAR_NOT_COLLINEAR` (closest existing:
  `notcoplanar_imp_notcollinear_fan`, Kepler/Text/PlanarityNotCut.lean:2298),
  `face_subset_dart_fan` (closest existing: `face_subset_darts`,
  Kepler/Text/Hypermap.lean:854, and `faceSet_subset_dartOfFan_auto2`,
  Kepler/Text/ConformingAuto2.lean:220), `CARD_SING`/`INSERT1_CARD1`
  (Mathlib). No new definition is introduced for any of them.
- None of the ten statements is Mathlib-general: each mentions the
  repo-specific `FAN`/`sigmaFan`/`f1Fan`/`affGt`/`dartsetLeadsIntoFan`/
  `conforming*Fan` vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto19

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical
open MeasureTheory

/-! ## 极小非 conforming 扇的两个直接推论（Conforming.hl:12512-12568） -/

/-- HOL Conforming.hl :12512-12538 `TXFBALB_VERSION`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~(conforming_fan (x,V,E))
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
==> conforming_solid_angle_fan(x,V,E)
```

编码说明：`conforming_fan`/`conforming_solid_angle_fan`/`N_FAN` ↦
`conformingFan`/`conformingSolidAngleFan`/`nFan`（均需显式 `FAN` 见证，
见文件头）。依赖 batch-19 的 `TXFBALB`（Kepler/Text/ConformingAuto19.lean:1487，
其证明目前仍是 `sorry`）；本定理声明保持原样，待 batch-19 证明落地后由
pool 按 HOL 原证明补齐。

证明思路：由 `nonconformin_fan_imp_exist_face_gt_3` 取卡片数 `>3` 的面
`ds`，`nonconformin_fan_imp_exist_3point_in_face` 取其中三点
`f1,f2,f3`，缩写 `v,u,w,E1,ds1,ds2,f10,f20,f30` 与 HOL 一致，最后把
`TXFBALB` 实例化即得 `conformingSolidAngleFan x V E hfan`。

候选已有引理：
- `nonconformin_fan_imp_exist_face_gt_3`（Kepler/Text/ConformingAuto8.lean:304）
- `nonconformin_fan_imp_exist_3point_in_face`
  （Kepler/Text/ConformingAuto8.lean:483）
- `TXFBALB`（Kepler/Text/ConformingAuto19.lean:1487；batch-19 证明尚为
  `sorry`，本定理的证明依赖它）
- `conformingSolidAngleFan`（Kepler/Text/ConformingDefs.lean:141） -/
theorem TXFBALB_VERSION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ¬ conformingFan x V E hfan ∧
    (∀ (E1 : Set (Set V3)) (hfan1 : FAN x V E1),
      FAN x V E1 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard) ∧
      fan80 x V E1 ∧
      nFan x V E1 hfan1 < nFan x V E hfan →
        conformingFan x V E1 hfan1) →
      conformingSolidAngleFan x V E hfan := by
  sorry

/-- HOL Conforming.hl :12539-12568 `conforming_bijection_fanadd_verrion`
（HOL 自身拼写 "verrion"，名字照抄）

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~(conforming_fan (x,V,E))
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
==>
!s. s IN topological_component_yfan (x,V,E) ==>
    (?!f. f IN face_set (hypermap1_of_fanx (x,V,E)) /\
           s = dartset_leads_into_fan x V E f)
```

编码说明：`?!f. P f` ↦ `∃! f, P f`；`face_set (hypermap1_of_fanx (x,V,E))`
↦ `(hypermapOfFan x V E hfan).faceSet`；`topological_component_yfan` ↦
`topologicalComponentYfan`；`dartset_leads_into_fan` ↦
`dartsetLeadsIntoFan`。与 `TXFBALB_VERSION` 同样依赖 batch-19 的
`TXFBALB`（经 `conforming_bijection_fanadd` 的实例化）。

证明思路：同上取 `ds, f1, f2, f3` 并缩写 `v,u,w,E1,ds1,ds2,f10,f20,f30`，
把 batch-18 的 `conforming_bijection_fanadd` 实例化，其结论恰为
`∀ s ∈ topologicalComponentYfan x V E, ∃! f, ...`。

候选已有引理：
- `nonconformin_fan_imp_exist_face_gt_3`（Kepler/Text/ConformingAuto8.lean:304）
- `nonconformin_fan_imp_exist_3point_in_face`
  （Kepler/Text/ConformingAuto8.lean:483）
- `conforming_bijection_fanadd`（Kepler/Text/ConformingAuto18.lean:1166）
- `TXFBALB`（Kepler/Text/ConformingAuto19.lean:1487；其证明尚为 `sorry`） -/
theorem conforming_bijection_fanadd_verrion (x : V3) (V : Set V3)
    (E : Set (Set V3)) (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ¬ conformingFan x V E hfan ∧
    (∀ (E1 : Set (Set V3)) (hfan1 : FAN x V E1),
      FAN x V E1 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard) ∧
      fan80 x V E1 ∧
      nFan x V E1 hfan1 < nFan x V E hfan →
        conformingFan x V E1 hfan1) →
      ∀ s ∈ topologicalComponentYfan x V E,
        ∃! f : Set (V3 × V3),
          f ∈ (hypermapOfFan x V E hfan).faceSet ∧
            s = dartsetLeadsIntoFan x V E f := by
  sorry

/-! ## fanadd 结构下的逆 σ 恒等式（Conforming.hl:12569-12681） -/

/-- HOL Conforming.hl :12569-12681 `inverse1_sigma_fan_FANADD4`

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
==> inverse1_sigma_fan x V E1 (inverse1_sigma_fan x V E w u) w = inverse1_sigma_fan x V E (inverse1_sigma_fan x V E w u) w
```

编码说明：`inverse1_sigma_fan` ↦ `inverse1SigmaFan`
（Kepler/Text/Fan.lean:240，无 `FAN` 参数）；假设块无内层 `!E1`
conforming 子句。

证明思路：`STEP3_REDUCE_FAN`/`FAN80_FANADD`/`YFANADD_AFF_GT` 建立
fanadd 结构；`INVERSE1_SIGMA_FAN` 给出 `{w, i w u}`、`{i w u, i (i w u) w}`
等在 `E`/`E1` 中（注意 `E ⊆ E1`），于是两边都落在 `E1` 的 σ-逆框架内；
再用 `SIGMA_FAN_OF_FANADD1` 与边关系逐点收缩为同一顶点。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- 缺口：`remark1_fan`、`MONO_SIGMA_FAN` 未移植（见文件头），pool 需用
  `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）等替代 -/
theorem inverse1_sigma_fan_FANADD4 (x : V3) (V : Set V3)
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
      inverse1SigmaFan x V E1 (inverse1SigmaFan x V E w u) w =
        inverse1SigmaFan x V E (inverse1SigmaFan x V E w u) w := by
  sorry

/-! ## 面内对角线的分类（Conforming.hl:12682-13252） -/

/-- HOL Conforming.hl :12682-13010 `conforming_diagonal_fanadd1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 z.
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
/\ z IN ds
/\ ~(f3=z)
==> ~collinear {x, pr2 f3, pr2 z} /\
                  (f3 = f1_fan x V E z \/
                   z = f1_fan x V E f3 \/
                   aff_gt {x} {pr2 f3, pr2 z} SUBSET
                   dartset_leads_into_fan x V E ds)
```

编码说明：内层 `!E1` 与外层 `E1` 同名，按 batch-18 约定改名 `E2`/`hfan2`；
`~collinear {x, pr2 f3, pr2 z}` ↦ `¬ Collinear3 x f3.1 z.1`；`f1_fan` ↦
`f1Fan`；`aff_gt {x} {pr2 f3, pr2 z}` ↦ `affGt ({x} : Set V3) {f3.1, z.1}`。

证明思路：`STEP3_REDUCE_FAN` + `FANADD_CONFORMING` 得
`conformingFan x V E1 hfan1`，其 `conformingDiagonalFan` 分量对
`z ∈ ds`（`ds` 是 `E1`-面，`DS1_DS2_EQ_DS_FANADD`）给出分类；按
`z = f1 / z = f2 / 其他` 分情况，用 `remark1_fan` 类的边交换与
`INJ_TRAN_D1_FAN`/`f2_EQ_F30_FANADD` 收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `conformingDiagonalFan`（Kepler/Text/ConformingDefs.lean:163）
- `DS1_DS2_EQ_DS_FANADD`（Kepler/Text/ConformingAuto19.lean:1256）
- `INJ_TRAN_D1_FAN`（Kepler/Text/ConformingAuto14.lean:314）
- `STEP2_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:235）
- `f2_EQ_F30_FANADD`（Kepler/Text/ConformingAuto16.lean:719）
- `rep_dartset_leads_into_fan_ds`（Kepler/Text/ConformingAuto18.lean:597）
- 缺口：`remark1_fan`、`properties_of_f1_fan`、`EQ_PAIR_IMP_EQ_4_FAN` 的
  替代需 pool 处理（`EQ_PAIR_IMP_EQ_4_FAN` 已有：
  Kepler/Text/PlanarityAuto15.lean:546） -/
theorem conforming_diagonal_fanadd1 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (z : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    z ∈ ds ∧
    ¬ (f3 = z) →
      ¬ Collinear3 x f3.1 z.1 ∧
        (f3 = f1Fan x V E z ∨ z = f1Fan x V E f3 ∨
          affGt ({x} : Set V3) {f3.1, z.1} ⊆ dartsetLeadsIntoFan x V E ds) := by
  sorry

/-- HOL Conforming.hl :13011-13203 `INDUCTION_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y.
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
/\ y IN ds
==> ?f1 f2 f3. {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\ {pr2 f2, pr2 f3} IN E
/\ ~({pr2 f3, pr2 f1 } IN E)
/\ {pr2 f1, pr2 f2 } IN E
/\ sigma_fan x V E (pr2 f2) (pr2 f3)=pr2 f1
/\ pr2 f3= pr3 f2
/\ pr2 f2= pr3 f1
/\ y=f3
```

编码说明：结论的存在量词 `?f1 f2 f3` 与外层参数同名遮蔽，按约定改名
`f1' f2' f3'`（尾合取 `y=f3` 指内层约束，写作 `y = f3'`）；`pr2/pr3` ↦
`.1/.2`，如 `{pr2 f2, pr2 f3} IN E` ↦ `({f2'.1, f3'.1} : Set V3) ∈ E`。

证明思路：`y` 在 `E`-面 `ds` 内，沿 `f1Fan` 的轨道回退
`CARD ds - 1`/`CARD ds - 2` 步取 `f2'`/`f1'`（`into_domain*_power_efn_fan`
的角色；`Hypermap.orbit`/`card_orbit_le`，Kepler/Text/Hypermap.lean:1115，
可替代）；`properties_of_f1_fan`/`PROPERTIES_TRIANGLE_FAN`/`condition_f1_eq_fan`
给出三角形关系与边条件；`f_fan_no_fix_point` 排除不动点。

候选已有引理：
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854）
- `identity_face_in_face_set`（Kepler/Text/ConformingAuto8.lean:380）
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（Kepler/Text/ConformingAuto1.lean:271）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `card_orbit_le`（Kepler/Text/Hypermap.lean:1115）
- `PROPERTIES_TRIANGLE_FAN`（Kepler/Text/PlanarityAuto14.lean:368）
- `condition_f1_eq_fan`（Kepler/Text/ConformingAuto8.lean:412）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：`into_domain_power_efn_fan`/`into_domain1_power_efn_fan`、
  `properties_of_f1_fan`、`f_fan_no_fix_point`、`lemma_face_identity`/
  `lemma_face_cycle`、`MONO_SIGMA_FAN` 未移植（见文件头） -/
theorem INDUCTION_FANADD (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (y : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    y ∈ ds →
      ∃ f1' f2' f3' : V3 × V3,
        ({f1', f2', f3'} : Set (V3 × V3)) ⊆ ds ∧
        f1Fan x V E f1' = f2' ∧ f1Fan x V E f2' = f3' ∧
        ¬ (f1Fan x V E f3' = f1') ∧
        ({f2'.1, f3'.1} : Set V3) ∈ E ∧
        ({f3'.1, f1'.1} : Set V3) ∉ E ∧
        ({f1'.1, f2'.1} : Set V3) ∈ E ∧
        sigmaFan x V E f2'.1 f3'.1 = f1'.1 ∧
        f3'.1 = f2'.2 ∧
        f2'.1 = f1'.2 ∧
        y = f3' := by
  sorry

/-- HOL Conforming.hl :13204-13252 `conforming_diagonal_fan_ds_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y z.
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
/\ y IN ds
/\ z IN ds
/\ ~(y=z)
==> ~collinear {x, pr2 y, pr2 z} /\
                  (y = f1_fan x V E z \/
                   z = f1_fan x V E y \/
                   aff_gt {x} {pr2 y, pr2 z} SUBSET
                   dartset_leads_into_fan x V E ds)
```

编码说明：内层 `!E1` 改名 `E2`/`hfan2`；`~collinear {x, pr2 y, pr2 z}` ↦
`¬ Collinear3 x y.1 z.1`。

证明思路：对 `y ∈ ds` 用 `INDUCTION_FANADD`（本文件上文）取
`f1',f2',f3'`，缩写 `v',u',w',E1',ds1',ds2',f10',f20',f30'` 后把
`conforming_diagonal_fanadd1`（本文件上文）实例化于 `(f1',f2',f3')` 与
`z`，再回代 `y = f3'` 即得。

候选已有引理：
- `INDUCTION_FANADD`（本文件上文）
- `conforming_diagonal_fanadd1`（本文件上文）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `conformingDiagonalFan`（Kepler/Text/ConformingDefs.lean:163） -/
theorem conforming_diagonal_fan_ds_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (y z : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    y ∈ ds ∧
    z ∈ ds ∧
    ¬ (y = z) →
      ¬ Collinear3 x y.1 z.1 ∧
        (y = f1Fan x V E z ∨ z = f1Fan x V E y ∨
          affGt ({x} : Set V3) {y.1, z.1} ⊆ dartsetLeadsIntoFan x V E ds) := by
  sorry

/-! ## GGZWYRM 与半空间交的三个引理（Conforming.hl:13253-13673） -/

/-- HOL Conforming.hl :13253-13308 `GGZWYRM`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
==> conforming_diagonal_fan(x,V,E)
```

编码说明：`conforming_diagonal_fan` ↦ `conformingDiagonalFan x V E hfan`
（Kepler/Text/ConformingDefs.lean:163）。

证明思路：展开 `conformingDiagonalFan`；任取 `f ∈ faceSet` 与
`y ≠ z ∈ f`。`CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN` 给 `3 ≤ CARD f`：
若 `CARD f = 3`，由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 与三点
枚举（`SET_TAC`）逐对验证；否则用
`nonconformin_fan_imp_exist_3point_in_face` 取三点并把
`conforming_diagonal_fan_ds_fanadd`（本文件上文）实例化于 `f`。

候选已有引理：
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`
  （Kepler/Text/PlanarityAuto15.lean:139）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371）
- `nonconformin_fan_imp_exist_3point_in_face`
  （Kepler/Text/ConformingAuto8.lean:483）
- `conforming_diagonal_fan_ds_fanadd`（本文件上文）
- `conformingDiagonalFan`（Kepler/Text/ConformingDefs.lean:163） -/
theorem GGZWYRM (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    (∀ (E1 : Set (Set V3)) (hfan1 : FAN x V E1),
      FAN x V E1 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard) ∧
      fan80 x V E1 ∧
      nFan x V E1 hfan1 < nFan x V E hfan →
        conformingFan x V E1 hfan1) →
      conformingDiagonalFan x V E hfan := by
  sorry

/-- HOL Conforming.hl :13309-13459 `INTERS_HALF_SPACE_DS_FANADD3`
（HOL 源行为 "let  INTERS_..." 双空格；名字无前导空格）

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
/\ U1=INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds}
==> U1 INTER aff {x, v, w} SUBSET aff_gt {x} {v, w}
```

编码说明：`INTERS {g y | y IN ds}` ↦ `⋂ y ∈ ds, g y`（同 batch-16 的
`INTERS_HALF_SPACE_DS_FANADD1/2`）；`aff` ↦ `(affineSpan ℝ _ : Set V3)`
（同 batch-17）；内层 `!E1` 改名 `E2`/`hfan2`。

证明思路：`STEP3_REDUCE_FAN`/`FAN80_FANADD`/`YFANADD_AFF_GT` 建立
fanadd 结构；`SIGMA_FAN_OF_FANADD_AT_POINT2/3` 与
`properties_fully_surrounded` 得两组 `fully surrounded` 四点组，再用
`aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1/..._2_14` 与
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（以 `f1`、`f2` 为见证
把两个半空间写成 `aff_gt {x, y.1, y.2}` 形式）与 `aff_gt_inter_aff_gt`
收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`
  （Kepler/Text/ConformingAuto16.lean:1673）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`（Kepler/Text/ConformingAuto17.lean:120）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- 缺口：`sigma_fan_in_set_of_edge` 未移植（见文件头） -/
theorem INTERS_HALF_SPACE_DS_FANADD3 (x : V3) (V : Set V3)
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
    U1 = ⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} →
      U1 ∩ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ⊆
        affGt ({x} : Set V3) {v, w} := by
  sorry

/-- HOL Conforming.hl :13460-13517 `lemma_HYUAZSE`

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
/\ INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds} = U1
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
==> U1 SUBSET U
```

编码说明：`INTERS {...}` ↦ `⋂ y ∈ ds, ...`（同 batch-16）；内层 `!E1`
改名 `E2`/`hfan2`。

证明思路：与 `INTERS_HALF_SPACE_DS_FANADD3` 相同的 fanadd 前置；再用
batch-16 的 `INTERS_HALF_SPACE_DS_FANADD1/2`（`U1 ∩ aff {x,v,w}` 的两个
半空间）、本文件 `INTERS_HALF_SPACE_DS_FANADD3` 与 batch-17 的
`SPACE3_EQ_UNION_3SET`（`aff {x,v,w}` 与两个开半空间之并覆盖全空间），
`SET_TAC` 收口得 `U1 ⊆ U`。

候选已有引理：
- `INTERS_HALF_SPACE_DS_FANADD1`（Kepler/Text/ConformingAuto16.lean:320）
- `INTERS_HALF_SPACE_DS_FANADD2`（Kepler/Text/ConformingAuto16.lean:850）
- `INTERS_HALF_SPACE_DS_FANADD3`（本文件上文）
- `SPACE3_EQ_UNION_3SET`（Kepler/Text/ConformingAuto17.lean:706）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014） -/
theorem lemma_HYUAZSE (x : V3) (V : Set V3)
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
    (⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}) = U1 ∧
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} →
      U1 ⊆ U := by
  sorry

/-- HOL Conforming.hl :13518-13673 `DART_FANADD_SUBSET_HALFSPACE`

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
==> dartset_leads_into_fan x V E1 ds1 SUBSET aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3) }
```

编码说明：`aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3)}` ↦
`affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2}`；内层 `!E1` 改名
`E2`/`hfan2`。

证明思路：`YFANADD_AFF_GT` 与 `FANADD_CONFORMING` 给
`conformingFan x V E1 hfan1`；其 `conformingHalfSpaceFan` 分量把
`dartsetLeadsIntoFan x V E1 ds1` 写成半空间之交，于是只需对 `ds1` 中任一
dart 验证；取 `(v,w)`（及其 `f1Fan`-像 `(w, inverse1SigmaFan x V E1 w v)`）
为见证，`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan` +
`inverse1_sigma_fan_FANADD` + `cross_dot_fully_surrounded_fan`/
`aff_gt_3_1_rep_cross_dot` 定向收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `inverse1_sigma_fan_FANADD`（Kepler/Text/ConformingAuto16.lean:521）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298；
  替代未移植的 `NOT_COPLANAR_NOT_COLLINEAR`）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- 缺口：`dartset_fully_surrounded_is_non_isolated_fan`、`remark1_fan`、
  `face_subset_dart_fan` 未移植（替代见文件头） -/
theorem DART_FANADD_SUBSET_HALFSPACE (x : V3) (V : Set V3)
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
      dartsetLeadsIntoFan x V E1 ds1 ⊆
        affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2} := by
  sorry

end Kepler.Text
