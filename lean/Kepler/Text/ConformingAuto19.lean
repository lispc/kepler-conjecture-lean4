/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 19
(Conforming.hl:10304-12511).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 19, Conforming.hl:10304-12511):
- `eventally_measurable_fanadd` (10304)
- `SOL_AFF_GT_2_1` (10455)
- `inverse1_sigma_fan_FANADD1` (10467)
- `inverse1_sigma_fan_FANADD2` (10530)
- `inverse1_sigma_fan_FANADD3` (10587)
- `DS1_DS2_EQ_DS_FANADD1` (10663)
- `DS1_DS2_EQ_DS_FANADD2` (11344)
- `DS1_DS2_EQ_DS_FANADD` (11882)
- `azim_fanadd_eq_ds` (11909)
- `TXFBALB` (12056)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`; HOL
  `CARD ds > 3` ↔ `3 < ds.ncard`.
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
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`,
  `(x,v,u,w)`, `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`,
  and `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to
  the pairs `(v,w)` / `(w,v)` (also used for `ed1`/`ed2` below).
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- The inner quantifier `(!E1. ... ==> conforming_fan (x,V,E1))` shadows the
  outer `E1`; as in `minimallyNonconformingFan`
  (Kepler/Text/ConformingDefs.lean:226) the inner variable is renamed `E2`
  and, because `conformingFan`/`nFan` need a `FAN` witness, encoded as
  `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
  conformingFan x V E2 hfan2` (the `FAN x V E2` conjunct is kept to align
  with the HOL antecedent). The binder `!v. v IN V ==> ...` inside that
  block is renamed `v'` to avoid shadowing the outer parameter `v`.
- HOL `tran` (Conforming.hl:4097) is NOT ported. It is
  `(\(x,y,z,w). (x,y,z,sigma_fan x V E1 y z))`: it only rewrites the 4th
  component of a dart. Since the repo's pair-dart encoding keeps
  `(pr2,pr3)` and drops the 4th component, `tran x V E1` is the IDENTITY on
  pair darts (same convention as Kepler/Text/ConformingAuto13.lean:55-68,
  Kepler/Text/ConformingAuto14.lean:59-72 and
  Kepler/Text/ConformingAuto18.lean:63-71). Hence `IMAGE (tran x V E1) ds`
  is kept in the `DS1_DS2_*` statements as the identity image
  `(fun y : V3 × V3 => y) '' ds` (so that the statements stay structurally
  parallel to HOL), and in `azim_fanadd_eq_ds` the arguments
  `pr2 (tran x V E1 y)`, `pr3 (tran x V E1 y)` collapse to `y.1`, `y.2`.
- HOL `measurable` ↔ `MeasurableSet`; HOL `ball (x,r)` ↔ `Metric.ball x r`;
  HOL `eventually_radial` ↔ `EventuallyRadial` (Kepler/Geom/Volume.lean:32);
  HOL `sol` ↔ `sol` (Kepler/Geom/Volume.lean:36); HOL `&0`/`&2 * pi` ↦
  `0`/`2 * Real.pi` (same encoding as `conformingSolidAngleFan`,
  Kepler/Text/ConformingDefs.lean:139-150).
- HOL `collinear` ↔ `Collinear3` (Kepler/Geom/Azim.lean:43); HOL `aff_gt`
  ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `DELETE` ↔ `\`; HOL
  `INTER`/`SUBSET`/`UNION`/`IMAGE` ↔ `∩`/`⊆`/`∪`/`Set.image`.
- Proof dependencies living in earlier conforming batches are NOT imported
  here (per the porting convention this batch imports only
  `PlanarityAuto16` and `ConformingDefs`); the proof sketches name them as
  candidates to be restated or imported by the worker pool.
- `SOL_AFF_GT_2_1` mentions only Mathlib-plus-`sol`/`affGt`/`Collinear3`
  vocabulary; `sol`/`affGt`/`Collinear3` are repo-specific, so it is not
  Mathlib-general and nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical
open MeasureTheory

/-! ## 实心角的可测性与径向性（Conforming.hl:10304-10465） -/

/-- HOL Conforming.hl :10304-10451 `eventally_measurable_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 f.
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
/\ f IN face_set (hypermap1_of_fanx (x,V,E))
 ==> let U = dartset_leads_into_fan x V E f in
               ((!r. measurable (ball (x,r) INTER U)) /\
               eventually_radial x U)
```

编码说明：结论中的 HOL `let U = ... in` 保留为 Lean 结论级 `let`（与
`conformingSolidAngleFan`，Kepler/Text/ConformingDefs.lean:144-150 一致）；
`measurable` ↦ `MeasurableSet`；`ball (x,r)` ↦ `Metric.ball x r`；
`eventually_radial` ↦ `EventuallyRadial`（Kepler/Geom/Volume.lean:32，
不再就地展开）。内层 `!E1` 改名 `E2` 并携带 `hfan2`（见文件头）。
额外携带 `hfan`、`hfan1`。

证明思路：对任意 `f ∈ faceSet`，由 `dartset_leads_into_fan_eq_fanadd`
把 `dartsetLeadsIntoFan x V E f` 拆成 `ds1`/`ds2`（新增边两侧的两片）之
并（`tranf_eq_image_of_tran` + `DOMAIN_TRANF_FACE_DELETE_DS` + `rep_...`），
其中 `f = ds` 或 `f ∈ faceSet \ {ds}`：前者直接对 `ds1`/`ds2` 用
`ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd` + `measurable_dartset_leads_into30_fan` 型
参数 + `dartset_leads_into_fan_eventually_radial_norm`；后者用
`YFANADD_AFF_GT` 得 `dartsetLeadsIntoFan f = affGt {x}{v,w}` 的径向片，
再以 `RADIAL_AFF_GT_1_2`/`MEASURABLE_AFF_GT_2_1_INTER_BALL` 收口；
两片相并用 `MEASURABLE_UNION`（Mathlib `MeasurableSet.union`）与
`RADIAL_UNION`、`RADIAL_NORM_CO`（半径上调）。

候选已有引理：
- `dartset_leads_into_fan_eq_fanadd`（Kepler/Text/ConformingAuto18.lean:763）
- `rep_dartset_leads_into_fan_ds`（Kepler/Text/ConformingAuto18.lean:597）
- `ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd`
  （Kepler/Text/ConformingAuto14.lean:555/623）
- `measurable_dartset_leads_into30_fan`（Kepler/Text/ConformingAuto2.lean:165）
- `dartset_leads_into_fan_eventually_radial_norm`
  （Kepler/Text/PlanarityAuto16.lean:142）
- `RADIAL_UNION`（Kepler/Text/ConformingAuto3.lean:588）、
  `RADIAL_NORM_CO`（Kepler/Text/ConformingAuto18.lean:1434）
- `MeasurableSet.union`（Mathlib；HOL `MEASURABLE_UNION`）
- `DOMAIN_TRANF_FACE_DELETE_DS`（Kepler/Text/ConformingAuto14.lean:1033） -/
theorem eventally_measurable_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (f : Set (V3 × V3)) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    f ∈ (hypermapOfFan x V E hfan).faceSet →
      let U := dartsetLeadsIntoFan x V E f
      (∀ r : ℝ, MeasurableSet (Metric.ball x r ∩ U)) ∧
        EventuallyRadial x U := by
  sorry

/-- HOL Conforming.hl :10455-10463 `SOL_AFF_GT_2_1`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
~collinear {x,v,u}==>   sol x (aff_gt {x} {v,u})= &0
```

编码说明：`~collinear {x,v,u}` ↦ `¬ Collinear3 x v u`
（Kepler/Geom/Azim.lean:43）；`aff_gt {x} {v,u}` ↦
`affGt ({x} : Set V3) {v, u}`（Kepler/Geom/Aff.lean:39）；`sol` ↦
`sol`（Kepler/Geom/Volume.lean:36）；`&0` ↦ `(0 : ℝ)`。

证明思路：用 `sol_spec`（Kepler/Geom/Volume.lean:171）在 `r = 1` 处：
`MeasurableSet (affGt {x} {v,u} ∩ ball x 1)` 由
`MEASURABLE_AFF_GT_2_1_INTER_BALL` 给出；`radialNorm 1 x (affGt ∩ ball)`
由 `RADIAL_AFF_GT_1_2` 给出（其 `Disjoint {x} {v,u}` 前件由不共线性与
`x ≠ v`/`x ≠ u` 推出）；于是 `sol = 3 * volume.real (affGt ∩ ball x 1) / 1 = 0`，
体积为零由 `MEASURE_AFF_GT_2_1_INTER_BALL` 给出。

候选已有引理：
- `MEASURABLE_AFF_GT_2_1_INTER_BALL`（Kepler/Text/ConformingAuto3.lean:279）
- `RADIAL_AFF_GT_1_2`（Kepler/Text/ConformingAuto18.lean:1383）
- `MEASURE_AFF_GT_2_1_INTER_BALL`（Kepler/Text/ConformingAuto2.lean:656）
- `sol_spec`（Kepler/Geom/Volume.lean:171） -/
theorem SOL_AFF_GT_2_1 (x v u : V3) (h : ¬ Collinear3 x v u) :
    sol x (affGt ({x} : Set V3) {v, u}) = 0 := by
  sorry

/-! ## 加边后 `inverse1_sigma_fan` 的三个转移式（Conforming.hl:10467-10657） -/

/-- HOL Conforming.hl :10467-10526 `inverse1_sigma_fan_FANADD1`

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
==> inverse1_sigma_fan x V E1 v (sigma_fan x V E v u) =  w
```

编码说明：`inverse1_sigma_fan` ↦ `inverse1SigmaFan`
（Kepler/Text/Fan.lean:240）。额外携带 `hfan`、`hfan1`。

证明思路：`SIGMA_FAN_OF_FANADD_AT_POINT1` 给出
`sigmaFan x V E1 v w = sigmaFan x V E v u`；又在 `E1` 中
`{v, sigmaFan x V E v u} ∈ E1`（`{v,u} ∈ E ⊆ E1`，`{v,w} ∈ E1` 由
`add_edge_graph_of_fanadd`），故对 `INVERSE1_SIGMA_FAN`（以 `FAN x V E1`
为见证）取 `w := w` 得 `inverse1SigmaFan x V E1 v (sigmaFan x V E1 v w) = w`，
两式改写即得。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `add_edge_graph_of_fanadd`（Kepler/Text/ConformingAuto10.lean:230） -/
theorem inverse1_sigma_fan_FANADD1 (x : V3) (V : Set V3)
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
      inverse1SigmaFan x V E1 v (sigmaFan x V E v u) = w := by
  sorry

/-- HOL Conforming.hl :10530-10583 `inverse1_sigma_fan_FANADD2`

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
==> inverse1_sigma_fan x V E1 v w=u
```

编码说明：`inverse1_sigma_fan` ↦ `inverse1SigmaFan`
（Kepler/Text/Fan.lean:240）。额外携带 `hfan`、`hfan1`。

证明思路：`SIGMA_FAN_OF_FANADD_AT_POINT2` 直接给出
`sigmaFan x V E1 v u = w`；`{v,u} ∈ E ⊆ E1`，故对
`INVERSE1_SIGMA_FAN`（以 `FAN x V E1` 为见证）在 `w := u` 处取第三支
`inverse1SigmaFan x V E1 v (sigmaFan x V E1 v u) = u`，改写即得。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `add_edge_graph_of_fanadd`（Kepler/Text/ConformingAuto10.lean:230） -/
theorem inverse1_sigma_fan_FANADD2 (x : V3) (V : Set V3)
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
      inverse1SigmaFan x V E1 v w = u := by
  sorry

/-- HOL Conforming.hl :10587-10657 `inverse1_sigma_fan_FANADD3`

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
==> inverse1_sigma_fan x V E1 u v=w
```

编码说明：`inverse1_sigma_fan` ↦ `inverse1SigmaFan`
（Kepler/Text/Fan.lean:240）。额外携带 `hfan`、`hfan1`。

证明思路：`{u,v} ∈ E1`（`Set.pair_comm` + `{v,u} ∈ E ⊆ E1`）；由
`SIGMA_FAN_OF_FANADD1`（在 `v1 = u, w1 = v`，需 `u ∉ {v,w}`，由
`v ≠ u`、`u ≠ w` 推出）得 `sigmaFan x V E1 u v = sigmaFan x V E u v`；
而 `sigmaFan x V E u v = w`（`sigmaFan x V E u w = v` 加
`INVERSE1_SIGMA_FAN` 在 `FAN x V E`、边 `{u,w} ∈ E` 处的 σ-置换性）；
最后对 `INVERSE1_SIGMA_FAN`（以 `FAN x V E1` 为见证）在 `w := v` 处取
第二支 `sigmaFan x V E1 u (inverse1SigmaFan x V E1 u v) = v` 并用 σ 在
`setOfEdge u V E1` 上的单射性（`sigmaFan` 为双射，见
`INVERSE1_SIGMA_FAN` 三条件）把 `inverse1SigmaFan x V E1 u v` 与 `w`
对齐。

候选已有引理：
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `sigma_fan_in_setOfEdge`（Kepler/Text/Fan.lean:326）
- `add_edge_graph_of_fanadd`（Kepler/Text/ConformingAuto10.lean:230）
- `Set.pair_comm`（Mathlib） -/
theorem inverse1_sigma_fan_FANADD3 (x : V3) (V : Set V3)
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
      inverse1SigmaFan x V E1 u v = w := by
  sorry

/-! ## 加边面的 darts 交换（Conforming.hl:10663-11907） -/

/-- HOL Conforming.hl :10663-11338 `DS1_DS2_EQ_DS_FANADD1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ed1 ed2.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1=face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2=face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ed1=(x,v,w,sigma_fan x V E1 v w)
/\ ed2=(x,w,v,sigma_fan x V E1 w v)
==> (ds1 UNION ds2) DELETE ed1 DELETE ed2 SUBSET IMAGE (tran x V E1) ds
```

编码说明：`tran x V E1` 在点对编码下为恒等（见文件头），右端
`IMAGE (tran x V E1) ds` 保留为 `(fun y : V3 × V3 => y) '' ds`；
`ed1 = (v, w)`、`ed2 = (w, v)`（四元组收缩为点对，见文件头）；
`DELETE` ↦ `\`。额外携带 `hfan`、`hfan1`。

证明思路：任取 `z ∈ ((ds1 ∪ ds2) \ {ed1}) \ {ed2}`；`z` 落在
`ds1` 或 `ds2` 中且异于 `(v,w)`/`(w,v)`，由 `ds1_in_face_set_fanadd`/
`ds2_in_face_set_fanadd` 得 `ds1 ∪ ds2 ⊆ dart1OfFan V E1`，再用
`STEP3_REDUCE_FAN`/`FAN80_FANADD`/`YFANADD_AFF_GT` 把 `E1`-面
`ds1`、`ds2` 与 `E`-面 `ds` 的 `tran`（恒等）轨道联系起来：面内 dart
沿 `f1Fan` 轨道走，删去 `ed1`/`ed2` 后轨道不跨新增边，故
`z` 的 `f1Fan x V E`-轨道仍在 `ds` 中，即 `z ∈ ds`。

候选已有引理：
- `ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd`
  （Kepler/Text/ConformingAuto14.lean:555/623）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `disjoint_ds1_and_ds2`（Kepler/Text/ConformingAuto12.lean:819）
- `Set.mem_diff`、`Set.image_id'`（Mathlib） -/
theorem DS1_DS2_EQ_DS_FANADD1 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ed1 ed2 : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ed1 = (v, w) ∧ ed2 = (w, v) →
      ((ds1 ∪ ds2) \ {ed1}) \ {ed2} ⊆ (fun y : V3 × V3 => y) '' ds := by
  sorry

/-- HOL Conforming.hl :11344-11877 `DS1_DS2_EQ_DS_FANADD2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ed1 ed2.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1=face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2=face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ed1=(x,v,w,sigma_fan x V E1 v w)
/\ ed2=(x,w,v,sigma_fan x V E1 w v)
==> IMAGE (tran x V E1) ds SUBSET (ds1 UNION ds2) DELETE ed1 DELETE ed2
```

编码说明：同 `DS1_DS2_EQ_DS_FANADD1`（`tran` 恒等、`ed1 = (v, w)`、
`ed2 = (w, v)`、`DELETE` ↦ `\`）。额外携带 `hfan`、`hfan1`。

证明思路：对 `z ∈ ds` 分类讨论：`z = f1` 时 `tran z`（恒等）在 `E1`-面
`(v,w)` 中但 `z = ed1` 被删（需证 `f1 = (v,w)`，由 `f1.1 = v` 与
`f1Fan` 的点对形状）；`z = f3` 类似落入 `ed2`；其余 `z`（含 `f2`）的
`tran` 像落在 `ds1` 或 `ds2` 中——由 `hypermapOfFan` 面的轨道表示与
`SIGMA_FAN_OF_FANADD_AT_POINT1/2`（新增边两侧 σ-值的变化）确定
`z` 属于哪一侧，再以 `tranf_eq_image_of_tran` 与
`DOMAIN_TRANF_FACE_DELETE_DS` 收口。

候选已有引理：
- `ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd`
  （Kepler/Text/ConformingAuto14.lean:555/623）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`/`_AT_POINT2`
  （Kepler/Text/ConformingAuto10.lean:399/510）
- `tranf_eq_image_of_tran`（Kepler/Text/ConformingAuto18.lean:1492）
- `DOMAIN_TRANF_FACE_DELETE_DS`（Kepler/Text/ConformingAuto14.lean:1033）
- `disjoint_ds1_and_ds2`（Kepler/Text/ConformingAuto12.lean:819） -/
theorem DS1_DS2_EQ_DS_FANADD2 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ed1 ed2 : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ed1 = (v, w) ∧ ed2 = (w, v) →
      (fun y : V3 × V3 => y) '' ds ⊆ ((ds1 ∪ ds2) \ {ed1}) \ {ed2} := by
  sorry

/-- HOL Conforming.hl :11882-11907 `DS1_DS2_EQ_DS_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ed1 ed2.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ ds1=face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2=face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ed1=(x,v,w,sigma_fan x V E1 v w)
/\ ed2=(x,w,v,sigma_fan x V E1 w v)
==> IMAGE (tran x V E1) ds = (ds1 UNION ds2) DELETE ed1 DELETE ed2
```

编码说明：同 `DS1_DS2_EQ_DS_FANADD1`（`tran` 恒等、`ed1 = (v, w)`、
`ed2 = (w, v)`、`DELETE` ↦ `\`）。额外携带 `hfan`、`hfan1`。

证明思路：直接由 `DS1_DS2_EQ_DS_FANADD1` 与 `DS1_DS2_EQ_DS_FANADD2`
（本文件上文）两个包含方向用 `Set.Subset.antisymm` 拼接。

候选已有引理：
- `DS1_DS2_EQ_DS_FANADD1`/`DS1_DS2_EQ_DS_FANADD2`（本文件上文）
- `Set.Subset.antisymm`（Mathlib） -/
theorem DS1_DS2_EQ_DS_FANADD (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ed1 ed2 : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    ed1 = (v, w) ∧ ed2 = (w, v) →
      (fun y : V3 × V3 => y) '' ds = ((ds1 ∪ ds2) \ {ed1}) \ {ed2} := by
  sorry

/-! ## 方位角不变性与实心角 conforming（Conforming.hl:11909-12507） -/

/-- HOL Conforming.hl :11909-12047 `azim_fanadd_eq_ds`

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
/\ y IN ds
/\ ~(y=f1)
/\ ~(y=f3)
==> azim_fan x V E1 (pr2 (tran x V E1 y)) (pr3 (tran x V E1 y))
= azim_fan x V E (pr2 y) (pr3 y)
```

编码说明：`tran x V E1` 在点对编码下为恒等（见文件头），故左端
`pr2 (tran x V E1 y)`/`pr3 (tran x V E1 y)` 收缩为 `y.1`/`y.2`；
`azim_fan` ↦ `azimFan`（Kepler/Text/Fan.lean:177）。额外携带
`hfan`、`hfan1`。

证明思路：由 `y ∈ ds ⊆ dart1OfFan V E` 得 `{y.1, y.2} ∈ E`；对 `y.1`
分类（= `v`、= `w`、其余）：分别用
`SIGMA_FAN_OF_FANADD_AT_POINT1`/`_AT_POINT2`/`SIGMA_FAN_OF_FANADD1`
得 `sigmaFan x V E1 y.1 y.2 = sigmaFan x V E y.1 y.2`，再由
`azimFan_eq_of_sigmaFan_eq`（σ 相同则 azim 相同）收口；
`~(y = f1)`/`~(y = f3)` 用于排除 `y.2 = u`（当 `y.1 = v`）与
`y.2 = inverse1SigmaFan x V E w u`（当 `y.1 = w`）的退化情形——那里
`sigmaFan` 变了、结论对 `E1` 不再成立。

候选已有引理：
- `SIGMA_FAN_OF_FANADD_AT_POINT1`/`_AT_POINT2`
  （Kepler/Text/ConformingAuto10.lean:399/510）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `azimFan_eq_of_sigmaFan_eq`（Kepler/Text/ConformingAuto18.lean:1689 处使用）
- `azim_fanadd_eq`（Kepler/Text/ConformingAuto18.lean:1633，同型命题的
  `faceSet \ {ds}` 版本）
- `dart1OfFan`（Kepler/Text/Fan.lean:86） -/
theorem azim_fanadd_eq_ds (x : V3) (V : Set V3)
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
    y ∈ ds ∧ ¬ (y = f1) ∧ ¬ (y = f3) →
      azimFan x V E1 y.1 y.2 = azimFan x V E y.1 y.2 := by
  sorry

/-- HOL Conforming.hl :12056-12507 `TXFBALB`

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
==> conforming_solid_angle_fan(x,V,E)
```

编码说明：`conforming_solid_angle_fan (x,V,E)` ↦
`conformingSolidAngleFan x V E hfan`
（Kepler/Text/ConformingDefs.lean:139-150，携带 `hfan` 见文件头）；
内层 `!E1` 改名 `E2` 并携带 `hfan2`（见文件头）。额外携带
`hfan`、`hfan1`。

证明思路：`FANADD_CONFORMING` 给出 `conformingFan x V E1 hfan1`，其
第三支为 `conformingSolidAngleFan x V E1 hfan1`；再把 `E1`-面的
`sol`/径向/可测条件沿 `dartset_leads_into_fan_eq_fanadd`（每个
`E`-面 `f` 的引导集等于 `E1`-面对应面 `tranf f` 的引导集，`tran` 恒等，
即 `ds1 ∪ ds2` 删两端）转移回 `E`：`sol` 用 `SOL_DISJOINT_UNION` 拆并、
`azim` 项用 `azim_fanadd_eq_ds`/`azim_fanadd_eq` 逐点改写，可测与径向
用 `eventally_measurable_fanadd`（本文件上文）+ `MEASURABLE_UNION` +
`RADIAL_UNION` + `RADIAL_NORM_CO`。

候选已有引理：
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `conformingSolidAngleFan`（Kepler/Text/ConformingDefs.lean:139）
- `eventally_measurable_fanadd`（本文件上文）
- `azim_fanadd_eq_ds`（本文件上文）、
  `azim_fanadd_eq`（Kepler/Text/ConformingAuto18.lean:1633）
- `dartset_leads_into_fan_eq_fanadd`（Kepler/Text/ConformingAuto18.lean:763）
- `DS1_DS2_EQ_DS_FANADD`（本文件上文）、
  `disjoint_ds1_and_ds2`（Kepler/Text/ConformingAuto12.lean:819）
- `SOL_DISJOINT_UNION`（Kepler/Text/ConformingAuto5.lean:212）、
  `RADIAL_UNION`（Kepler/Text/ConformingAuto3.lean:588）、
  `RADIAL_NORM_CO`（Kepler/Text/ConformingAuto18.lean:1434）
- `MeasurableSet.union`（Mathlib；HOL `MEASURABLE_UNION`） -/
theorem TXFBALB (x : V3) (V : Set V3)
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
      conformingSolidAngleFan x V E hfan := by
  sorry

end Kepler.Text
