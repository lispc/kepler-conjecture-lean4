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
  rintro ⟨-, hcard, hfan80, -, -, -, -, -, -, -, -, -, hvu, huw, hwv, hsigma,
    -, -, -, -, -, -, -, hE1⟩
  have hwu : ({w, u} : Set V3) ∈ E := by rw [Set.pair_comm]; exact huw
  set p : V3 := inverse1SigmaFan x V E w u with hp
  have hpE : ({w, p} : Set V3) ∈ E := (INVERSE1_SIGMA_FAN (v := w) hfan).1 u hwu
  have hpw : ({p, w} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hpE
  have htE : ({p, inverse1SigmaFan x V E p w} : Set V3) ∈ E :=
    (INVERSE1_SIGMA_FAN (v := p) hfan).1 w hpw
  have htσ : sigmaFan x V E p (inverse1SigmaFan x V E p w) = w :=
    (INVERSE1_SIGMA_FAN (v := p) hfan).2.1 w hpw
  have hnotvw : ({v, w} : Set V3) ∉ E := fun hh => hwv (by rw [Set.pair_comm]; exact hh)
  have hp_ne_mem : p ∉ ({v, w} : Set V3) := by
    intro hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact hwv (h ▸ hpE)
    · exact edge_ne_of_fan hfan hpw h
  have hEsub : E ⊆ E1 := fun e he => by rw [← hE1]; exact Set.mem_union_left _ he
  have hσd : sigmaFan x V E1 p (inverse1SigmaFan x V E p w) = w := by
    rw [SIGMA_FAN_OF_FANADD1 x V E E1 v w ⟨hfan, hfan1, hcard, hnotvw, hE1⟩ p
      (inverse1SigmaFan x V E p w) ⟨htE, hp_ne_mem⟩, htσ]
  have hin := (INVERSE1_SIGMA_FAN (v := p) hfan1).2.2 _ (hEsub htE)
  rw [hσd] at hin
  exact hin

/-- `Collinear3` 后两点交换（ConformingAuto11.lean:131 的私有副本）。 -/
private theorem collinear3_swap20 {a b c : V3} (h : ¬ Collinear3 a b c) :
    ¬ Collinear3 a c b := by
  intro hc
  apply h
  change Collinear ℝ ({a, b, c} : Set V3)
  rw [show ({a, b, c} : Set V3) = {a, c, b} from by ext z; simp; tauto]
  exact hc

/-- 加边 `{v,w}` 处 `f1Fan` 的相容性（ConformingAuto19.lean:688-733、793-877
的 σ-稳定性技术打包）：真 dart `c`（`c ≠ (u,w)`）处 `f1Fan x V E1 c` 要么与
`f1Fan x V E c` 一致，要么落到新 dart `(v,w)`。 -/
private theorem f1Fan_E1_eq_of_edge {x : V3} {V : Set V3} {E E1 : Set (Set V3)}
    {v u w : V3} (hfan : FAN x V E) (hfan1 : FAN x V E1)
    (hfan80 : fan80 x V E)
    (hcard : ∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard)
    (hvu : ({v, u} : Set V3) ∈ E) (huw : ({u, w} : Set V3) ∈ E)
    (hwv : ({w, v} : Set V3) ∉ E) (hsigma : sigmaFan x V E u w = v)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1)
    (c : V3 × V3) (hcE : ({c.1, c.2} : Set V3) ∈ E) (hc : c ≠ (u, w)) :
    f1Fan x V E1 c = f1Fan x V E c ∨ f1Fan x V E1 c = (v, w) := by
  have hEsub : E ⊆ E1 := fun e he => by rw [← hE1]; exact Set.mem_union_left _ he
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by rw [← hE1]; exact Or.inr rfl
  have hθ := hfan80 v u hvu
  have hsnu : sigmaFan x V E v u ≠ u := by
    intro hsu
    rw [hsu, azim_self] at hθ
    norm_num at hθ
  have hwuE : ({w, u} : Set V3) ∈ E := by rw [Set.pair_comm]; exact huw
  have hσ1 : sigmaFan x V E1 v w = sigmaFan x V E v u :=
    SIGMA_FAN_OF_FANADD_AT_POINT1 x V E E1 v u w
      ⟨hfan, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hescinv : inverse1SigmaFan x V E1 v (sigmaFan x V E v u) = w := by
    have hin := (INVERSE1_SIGMA_FAN (v := v) hfan1).2.2 w hvwE1
    rwa [hσ1] at hin
  have hnotvw : ({v, w} : Set V3) ∉ E := fun hh => hwv (by rw [Set.pair_comm]; exact hh)
  -- 新边之外 inverse1SigmaFan 的不变性
  have hinv_off : ∀ b a : V3, b ∉ ({v, w} : Set V3) → ({b, a} : Set V3) ∈ E →
      inverse1SigmaFan x V E1 b a = inverse1SigmaFan x V E b a := by
    intro b a hb hba
    have htE : ({b, inverse1SigmaFan x V E b a} : Set V3) ∈ E :=
      (INVERSE1_SIGMA_FAN (v := b) hfan).1 a hba
    have htσ : sigmaFan x V E b (inverse1SigmaFan x V E b a) = a :=
      (INVERSE1_SIGMA_FAN (v := b) hfan).2.1 a hba
    have hσd : sigmaFan x V E1 b (inverse1SigmaFan x V E b a) = a := by
      rw [SIGMA_FAN_OF_FANADD1 x V E E1 v w ⟨hfan, hfan1, hcard, hnotvw, hE1⟩ b
        (inverse1SigmaFan x V E b a) ⟨htE, hb⟩, htσ]
    have hin := (INVERSE1_SIGMA_FAN (v := b) hfan1).2.2 _ (hEsub htE)
    rwa [hσd] at hin
  have hinv_v : ∀ a : V3, a ≠ sigmaFan x V E v u → ({v, a} : Set V3) ∈ E →
      inverse1SigmaFan x V E1 v a = inverse1SigmaFan x V E v a := by
    intro a ha hva
    have htE : ({v, inverse1SigmaFan x V E v a} : Set V3) ∈ E :=
      (INVERSE1_SIGMA_FAN (v := v) hfan).1 a hva
    have htσ : sigmaFan x V E v (inverse1SigmaFan x V E v a) = a :=
      (INVERSE1_SIGMA_FAN (v := v) hfan).2.1 a hva
    have htne : u ≠ inverse1SigmaFan x V E v a := by
      intro hte
      apply ha
      rw [← htσ, hte]
    have hσd : sigmaFan x V E1 v (inverse1SigmaFan x V E v a) = a := by
      rw [SIGMA_FAN_OF_FANADD_AT_POINT4 x V E E1 v u w (inverse1SigmaFan x V E v a)
        ⟨hfan, hfan1, hfan80, hvu, huw, hwv, htne, htE, hsigma, hcard, hE1⟩, htσ]
    have hin := (INVERSE1_SIGMA_FAN (v := v) hfan1).2.2 _ (hEsub htE)
    rwa [hσd] at hin
  have hinv_w : ∀ a : V3, a ≠ u → ({w, a} : Set V3) ∈ E →
      inverse1SigmaFan x V E1 w a = inverse1SigmaFan x V E w a := by
    intro a ha hwa
    have htE : ({w, inverse1SigmaFan x V E w a} : Set V3) ∈ E :=
      (INVERSE1_SIGMA_FAN (v := w) hfan).1 a hwa
    have htσ : sigmaFan x V E w (inverse1SigmaFan x V E w a) = a :=
      (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 a hwa
    have htne : inverse1SigmaFan x V E w a ≠ inverse1SigmaFan x V E w u := by
      intro hte
      apply ha
      rw [← htσ, hte]
      exact (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 u hwuE
    have hσd : sigmaFan x V E1 w (inverse1SigmaFan x V E w a) = a := by
      rw [SIGMA_FAN_OF_FANADD_AT_POINT5 x V E E1 v u w (inverse1SigmaFan x V E w a)
        ⟨hfan, hfan1, hfan80, hvu, huw, hwv, htne, htE, hsigma, hcard, hE1⟩, htσ]
    have hin := (INVERSE1_SIGMA_FAN (v := w) hfan1).2.2 _ (hEsub htE)
    rwa [hσd] at hin
  by_cases hc2v : c.2 = v
  · by_cases hc1s : c.1 = sigmaFan x V E v u
    · -- 逃逸回新 dart (v, w)
      right
      simp only [f1Fan, hc2v, hc1s]
      rw [hescinv]
    · left
      have hve : ({v, c.1} : Set V3) ∈ E := by
        rw [Set.pair_comm, ← hc2v]; exact hcE
      simp only [f1Fan, hc2v]
      rw [hinv_v c.1 hc1s hve]
  · by_cases hc2w : c.2 = w
    · by_cases hc1u : c.1 = u
      · exact absurd (Prod.ext_iff.mpr ⟨hc1u, hc2w⟩) hc
      · left
        have hwa : ({w, c.1} : Set V3) ∈ E := by
          rw [Set.pair_comm, ← hc2w]; exact hcE
        simp only [f1Fan, hc2w]
        rw [hinv_w c.1 hc1u hwa]
    · left
      have hnv : c.2 ∉ ({v, w} : Set V3) := by
        intro hmem
        rcases Set.mem_insert_iff.mp hmem with h | h
        · exact hc2v h
        · exact hc2w (Set.mem_singleton_iff.mp h)
      have hba : ({c.2, c.1} : Set V3) ∈ E := by rw [Set.pair_comm]; exact hcE
      simp only [f1Fan]
      rw [hinv_off c.2 c.1 hnv hba]

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
  intro h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    a17, a18, a19, a20, a21, a22, a23, a24, a25, hz, hf3z⟩ := h
  -- E ⊆ E1 与三支 dart 的形状
  have hEsub : E ⊆ E1 := fun e he => by rw [← a24]; exact Set.mem_union_left _ he
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by rw [← a24]; exact Or.inr rfl
  have hf1val : f1 = (v, u) := Prod.ext_iff.mpr ⟨a10, a17⟩
  have hf2val : f2 = (u, w) := Prod.ext_iff.mpr ⟨a11, a18⟩
  have hwuE : ({w, u} : Set V3) ∈ E := by rw [Set.pair_comm]; exact a14
  have hpE : ({w, inverse1SigmaFan x V E w u} : Set V3) ∈ E :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).1 u hwuE
  have hf3val : f3 = (w, inverse1SigmaFan x V E w u) := by
    rw [← a8, hf2val]
    simp [f1Fan]
  have hunw : u ≠ w := edge_ne_of_fan hfan a14
  have hθ := a3 u w a14
  rw [a16] at hθ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan a13 a14 hθ.1 hθ.2
  have hvnw : v ≠ w := by
    intro hveq
    rw [hveq, azim_self] at hθ
    norm_num at hθ
  -- z 是 E-dart
  have hdartscoe : ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E := by
    change ((finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hzE : ({z.1, z.2} : Set V3) ∈ E := by
    obtain ⟨d0, hd0, hd0f⟩ := (hypermapOfFan x V E hfan).face_representation a4
    have hzface : z ∈ (hypermapOfFan x V E hfan).face d0 := by rw [← hd0f]; exact hz
    have hzdart := (hypermapOfFan x V E hfan).face_subset_darts hd0 hzface
    rw [hdartscoe] at hzdart
    exact hzdart
  -- E1 中加边处的 σ 值与 f3 = f1Fan x V E1 (v,w) ∈ ds1
  have hσ6 : sigmaFan x V E1 w (inverse1SigmaFan x V E w u) = v :=
    SIGMA_FAN_OF_FANADD_AT_POINT6 x V E E1 v u w (inverse1SigmaFan x V E w u)
      ⟨hfan, hfan1, a3, a13, a14, a15, rfl, hpE, a16, a2, a24⟩
  have hinvF1 : inverse1SigmaFan x V E1 w v = inverse1SigmaFan x V E w u := by
    have hin := (INVERSE1_SIGMA_FAN (v := w) hfan1).2.2 _ (hEsub hpE)
    rwa [hσ6] at hin
  have hvwD1 : (v, w) ∈ dart1OfFan V E1 := hvwE1
  have hfm : (hypermapOfFan x V E1 hfan1).faceMap (v, w) = f1Fan x V E1 (v, w) := by
    have hba : ({w, v} : Set V3) ∈ E1 := by rw [Set.pair_comm]; exact hvwE1
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [if_pos (by
      simpa [(finite_dart1_fan hfan1).coe_toFinset] using hvwD1)]
    simp only [f1Fan, fFanPair]
    rw [inverse_sigma_fan_eq_inverse1 hfan1 hba]
  have hf3f : f3 = f1Fan x V E1 (v, w) := by
    show f3 = (w, inverse1SigmaFan x V E1 w v)
    rw [hinvF1]
    exact hf3val
  have hf3d1 : f3 ∈ ds1 := by
    have h0 := pow_apply_mem_orbitMap (hypermapOfFan x V E1 hfan1).faceMap 1 (v, w)
    rw [Equiv.Perm.coe_pow, Function.iterate_one, hfm] at h0
    rw [← a19, hf3f]
    exact h0
  -- FANADD_CONFORMING（用到归纳假设 a25）给出 E1 上的 conforming_diagonal_fan
  have hconf1 := FANADD_CONFORMING x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    hfan hfan1 ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25⟩
  -- ds2 的三元表示、ds 的差集表示、leads-into 的并集表示
  have hds2rep : ds2 = ({f10, f20, f30} : Set (V3 × V3)) :=
    reperentation_of_ds2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
        a19.symm, a20.symm, a21, a22, a23, a24⟩
  have hdsrep : (fun y : V3 × V3 => y) '' ds =
      ((ds1 ∪ ds2) \ {(v, w)}) \ {(w, v)} :=
    DS1_DS2_EQ_DS_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 (v, w) (w, v)
      hfan hfan1
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
        a17, a18, a19.symm, a20.symm, a21, a22, a23, a24, rfl, rfl⟩
  have hU := rep_dartset_leads_into_fan_ds x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    (dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w}) hfan hfan1
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, rfl⟩
  have hds1fs : ds1 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds1_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
        a17, a18, a19.symm, a20.symm, a21, a22, a23, a24⟩
  -- 情形一：z = f1
  by_cases hz1 : z = f1
  · rw [hz1]
    refine ⟨?_, Or.inr (Or.inr ?_)⟩
    · rw [a12, a10]
      exact collinear3_swap20 (notcoplanar_imp_notcollinear_fan hcop).2.2
    · rw [a12, a10, Set.pair_comm]
      exact STEP2_REDUCE_FAN hfan a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  -- 情形二：z = f2
  by_cases hz2 : z = f2
  · rw [hz2]
    refine ⟨?_, Or.inl ?_⟩
    · rw [a12, a11]
      exact fan_not_collinear hfan hwuE
    · rw [a8]
  -- 情形三：z ≠ f1 且 z ≠ f2，则 z ∈ ds1，套用 E1 上的 conforming_diagonal_fan
  · have hzimg : z ∈ (fun y : V3 × V3 => y) '' ds := ⟨z, hz, rfl⟩
    rw [hdsrep] at hzimg
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hzimg
    obtain ⟨⟨hzunion, hznvw⟩, hznwv⟩ := hzimg
    have hz1m : z ∈ ds1 := by
      rcases hzunion with hmem | hmem
      · exact hmem
      · rw [hds2rep] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with hm | hm | hm
        · rw [a21] at hm
          exact absurd hm hznwv
        · rw [a22] at hm
          rw [← hf1val] at hm
          exact absurd hm hz1
        · rw [a23] at hm
          rw [← hf2val] at hm
          exact absurd hm hz2
    obtain ⟨hcol, dor⟩ :=
      hconf1.2.2.2.2.2 ds1 hds1fs f3 hf3d1 z hz1m hf3z
    refine ⟨hcol, ?_⟩
    rcases dor with d1 | d2 | d3
    · -- f3 = f1Fan x V E1 z
      rcases f1Fan_E1_eq_of_edge hfan hfan1 a3 a2 a13 a14 a15 a16 a24 z hzE
        (fun hc => hz2 (by rw [hf2val]; exact hc)) with heq | hesc
      · exact Or.inl (d1.trans heq)
      · have hf3vw : f3 = (v, w) := d1.trans hesc
        have hcf : f3.1 = v := by rw [hf3vw]
        exact absurd (hcf.symm.trans a12) hvnw
    · -- z = f1Fan x V E1 f3
      have hf3ne : f3 ≠ (u, w) := by
        intro hcon
        rw [hf3val] at hcon
        exact hunw (congrArg Prod.fst hcon).symm
      rcases f1Fan_E1_eq_of_edge hfan hfan1 a3 a2 a13 a14 a15 a16 a24 f3
        (by rw [hf3val]; exact hpE) hf3ne with heq | hesc
      · exact Or.inr (Or.inl (d2.trans heq))
      · rw [hf3val] at hesc
        have h5 : f1Fan x V E1 (w, inverse1SigmaFan x V E w u) =
            (inverse1SigmaFan x V E w u,
              inverse1SigmaFan x V E1 (inverse1SigmaFan x V E w u) w) := rfl
        rw [h5] at hesc
        have hpv : inverse1SigmaFan x V E w u ≠ v := fun h6 => a15 (h6 ▸ hpE)
        exact absurd (congrArg Prod.fst hesc).symm hpv.symm
    · -- affGt {x} {f3.1, z.1} ⊆ dartsetLeadsIntoFan x V E1 ds1
      refine Or.inr (Or.inr ?_)
      rw [hU]
      exact Set.Subset.trans d3 (Set.subset_union_left.trans Set.subset_union_left)

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
/- `faceMap` 与 `f1Fan` 在真 dart 上一致（`hypermapOfFan_faceMap_eq_ca1`
（Kepler/Text/ConformingAuto1.lean）与 `inverse_sigma_fan_eq_inverse1` 的合并）。 -/
private theorem hypermapOfFan_faceMap_eq_f1Fan20 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = f1Fan x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]
  have hba : {d.2, d.1} ∈ E := by
    have h : {d.1, d.2} ∈ E := hd
    rwa [Set.pair_comm] at h
  simp only [f1Fan, fFanPair]
  rw [inverse_sigma_fan_eq_inverse1 hfan hba]

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
  intro h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, hy⟩ := h
  -- dart 集、置换、以及 y ∈ ds 的 dart 属性
  have hdartscoe : ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E := by
    change ((finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  obtain ⟨d0, hd0, hd0f⟩ := (hypermapOfFan x V E hfan).face_representation a4
  have hyface0 : y ∈ (hypermapOfFan x V E hfan).face d0 := by rw [← hd0f]; exact hy
  have hydart1 : y ∈ dart1OfFan V E := by
    have hysub := (hypermapOfFan x V E hfan).face_subset_darts hd0 hyface0
    rwa [hdartscoe] at hysub
  have hdsy : ds = (hypermapOfFan x V E hfan).face y := identity_face_in_face_set hfan a4 hy
  have hfinMem : ∀ d : V3 × V3, d ∈ dart1OfFan V E →
      d ∈ (hypermapOfFan x V E hfan).darts := by
    intro d hd
    rw [← hdartscoe] at hd
    exact Finset.mem_coe.mp hd
  have hfinMem' : ∀ d : V3 × V3, d ∈ (hypermapOfFan x V E hfan).darts →
      d ∈ dart1OfFan V E := by
    intro d hd
    have h2 : d ∈ ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) :=
      Finset.mem_coe.mpr hd
    rwa [hdartscoe] at h2
  -- 轨道回退的显式见证：f3' = y，f2' = σ_{y.1}(y.2) 方向的前一 dart，
  -- f1' = σ_{f2'.1}(y.1) 方向的再前一 dart
  set u' : V3 := sigmaFan x V E y.1 y.2 with hu'def
  set w' : V3 := sigmaFan x V E u' y.1 with hw'def
  have hyE : {y.1, y.2} ∈ E := hydart1
  have hy1V : y.1 ∈ V := a1.1 (Set.mem_sUnion.mpr ⟨{y.1, y.2}, hyE, by simp⟩)
  have hy2V : y.2 ∈ V := a1.1 (Set.mem_sUnion.mpr ⟨{y.1, y.2}, hyE, by simp⟩)
  have hy1s : y.2 ∈ setOfEdge y.1 V E := ⟨hyE, hy2V⟩
  have hsu' : u' ∈ setOfEdge y.1 V E := sigma_fan_in_setOfEdge hfan hy1s
  have hG5 : {u', y.1} ∈ E := by
    have hw : {y.1, u'} ∈ E := (properties_of_setOfEdge_fan x V E y.1 u' hfan).mpr hsu'
    rwa [Set.pair_comm] at hw
  have hu'V : u' ∈ V := a1.1 (Set.mem_sUnion.mpr ⟨{u', y.1}, hG5, by simp⟩)
  have hu1s : y.1 ∈ setOfEdge u' V E := ⟨hG5, hy1V⟩
  have hsw' : w' ∈ setOfEdge u' V E := sigma_fan_in_setOfEdge hfan hu1s
  have hG7 : {w', u'} ∈ E := by
    have hw : {u', w'} ∈ E := (properties_of_setOfEdge_fan x V E u' w' hfan).mpr hsw'
    rwa [Set.pair_comm] at hw
  have hG7u : {u', w'} ∈ E := by
    have hw := hG7
    rwa [Set.pair_comm w' u'] at hw
  have hw'V : w' ∈ V := a1.1 (Set.mem_sUnion.mpr ⟨{u', w'}, hG7u, by simp⟩)
  -- f1Fan 沿轨道回退两步
  have hF23 : f1Fan x V E (u', y.1) = y := by
    show (y.1, inverse1SigmaFan x V E y.1 u') = y
    rw [hu'def, (INVERSE1_SIGMA_FAN hfan).2.2 y.2 hyE]
  have hF12 : f1Fan x V E (w', u') = (u', y.1) := by
    show (u', inverse1SigmaFan x V E u' w') = (u', y.1)
    rw [hw'def, (INVERSE1_SIGMA_FAN hfan).2.2 y.1 hG5]
  -- 排除不动点情形：f1Fan y ≠ f1'，否则 ds 是长度 ≤ 3 的轨道
  have hne : f1Fan x V E y ≠ (w', u') := by
    intro h4
    have h3 : (f1Fan x V E)^[3] y = y := by
      show (f1Fan x V E) ((f1Fan x V E) ((f1Fan x V E) y)) = y
      rw [h4, hF12, hF23]
    have hlink : ∀ (n : ℕ) (d : V3 × V3), d ∈ dart1OfFan V E →
        ((hypermapOfFan x V E hfan).faceMap ^ n) d = (f1Fan x V E)^[n] d := by
      intro n
      induction n with
      | zero => intro d _; simp
      | succ k ih =>
        intro d hd
        have hd' : (hypermapOfFan x V E hfan).faceMap d ∈ dart1OfFan V E :=
          hfinMem' _ ((hypermapOfFan x V E hfan).faceMap_permutes.apply_mem (hfinMem d hd))
        rw [pow_succ, Equiv.Perm.mul_apply,
          ih ((hypermapOfFan x V E hfan).faceMap d) hd',
          hypermapOfFan_faceMap_eq_f1Fan20 hfan hd,
          Function.iterate_succ_apply]
    have hy3 : ((hypermapOfFan x V E hfan).faceMap ^ 3) y = y := by
      rw [hlink 3 y hydart1]; exact h3
    have hcard := card_orbit_le (hypermapOfFan x V E hfan).faceMap
      (by norm_num : (3:ℕ) ≠ 0) hy3
    rw [hdsy] at a5
    simp only [Hypermap.face] at a5
    omega
  -- f2'、f1' 都是 dart
  have hdof : dartOfFan V E = dart1OfFan V E := dartOfFan_eq_dart1_of_surrounded hfan a2
  have hf2dart : (u', y.1) ∈ dartOfFan V E := by rw [hdof]; exact hG5
  have hf1dart : (w', u') ∈ dartOfFan V E := by rw [hdof]; exact hG7
  refine ⟨(w', u'), (u', y.1), y, ?_, hF12, hF23, hne, hG5, ?_, hG7, hw'def.symm,
    rfl, rfl, rfl⟩
  · intro z hz
    have hm1 : (u', y.1) ∈ ds := IMAGE_F1_IN_FACE_IMP_IN_FACE hfan a2 a4 hy hf2dart hF23
    have hm2 : (w', u') ∈ ds := IMAGE_F1_IN_FACE_IMP_IN_FACE hfan a2 a4 hm1 hf1dart hF12
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hm2
    · exact hm1
    · exact hy
  · intro hcontra
    obtain ⟨hσ1, hσ2⟩ := PROPERTIES_TRIANGLE_FAN (v := w') (u := u') (w := y.1)
      hfan hG7 hG5 hcontra hw'def.symm a2 a3
    have hw's : w' ∈ setOfEdge y.1 V E := ⟨hcontra, hw'V⟩
    have hσeq : sigmaFan x V E y.1 y.2 = sigmaFan x V E y.1 w' := by
      rw [← hu'def, hσ2]
    have h22 : y.2 = w' := mono_sigma_fan hfan hy1s hw's hσeq
    have hfeq : y = (y.1, w') := Prod.ext rfl h22
    rw [hfeq] at hne
    exact hne (condition_f1_eq_fan (v := y.1) (u := w') (w := u') hfan hG7 hcontra hσ1)

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
  intro h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
      a17, a18, a19, a20, a21, a22, a23, a24, a25, hy, hz, hyz⟩ := h
  obtain ⟨g1, g2, g3, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, hyg3⟩ :=
    INDUCTION_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y hfan hfan1
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
        a18, a19, a20, a21, a22, a23, a24, a25, hy⟩
  have hfan1' : FAN x V (E ∪ {({g1.1, g3.1} : Set V3)}) :=
    STEP3_REDUCE_FAN hfan a2 a3 a4 a5 k1 k2 k3 k4 rfl rfl rfl k7 k5 k6 k8 rfl
  rw [hyg3]
  exact conforming_diagonal_fanadd1 x V E (E ∪ {({g1.1, g3.1} : Set V3)}) ds g1 g2 g3
    g1.1 g2.1 g3.1
    ((hypermapOfFan x V (E ∪ {({g1.1, g3.1} : Set V3)}) hfan1').face (g1.1, g3.1))
    ((hypermapOfFan x V (E ∪ {({g1.1, g3.1} : Set V3)}) hfan1').face (g3.1, g1.1))
    (g3.1, g1.1) (g1.1, g2.1) (g2.1, g3.1) z hfan hfan1'
    ⟨a1, a2, a3, a4, a5, k1, k2, k3, k4, rfl, rfl, rfl, k7, k5, k6, k8, k10.symm,
      k9.symm, rfl, rfl, rfl, rfl, rfl, rfl, a25, hz, fun hc => hyz (hyg3.trans hc)⟩

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
