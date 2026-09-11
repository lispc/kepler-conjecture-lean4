/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 15
(Conforming.hl:6178-7118).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 15, Conforming.hl:6178-7118):
- `CARD_DART_FANADD` (6178)
- `ZSZIUQE_LEMMA` (6237)  [listed only as ":6237" in the task]
- `FAN80_FANADD` (6338)
- `FANADD_CONFORMING` (6522)
- `INVARANT_SIGMA_FAN_ADD` (6567)
- `lemma_yfanadd_aff_ge` (6693)
- `lemma_yfanadd_aff_gt` (6743)
- `lemma_yfanadd_aff_gt1` (6844)
- `YFANADD_AFF_GT` (6869)
- `dartset_leads_into_fanadd1` (6901)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`; HOL `CARD ds > 3` ↔ `3 < ds.ncard`; HOL
  `CARD s` ↔ `s.ncard` (`s` a set).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx (x,V,E)) f`
  as `(hypermapOfFan x V E hfan).face f`, and `dart (hypermap1_of_fanx
  (x,V,E))` (the dart set) as `(hypermapOfFan x V E hfan).darts` (a
  `Finset`, so HOL `CARD (dart ...)` ↔ `.darts.card`, cf.
  Kepler/Text/ConformingAuto8.lean:51). Since `hypermapOfFan`
  (Kepler/Text/Fan.lean:1169) needs an explicit `hfan : FAN x V E`, every
  theorem that mentions it carries an extra explicit `(hfan : FAN x V E)`
  argument; theorems that also mention `hypermapOfFan x V E1` carry a second
  extra explicit argument `(hfan1 : FAN x V E1)`. These are the only
  deviations from the HOL signatures (HOL's `hypermap_of_fan` is total).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87).
- HOL `d1_fan (x,V,E)` ↔ `dart1OfFan V E` (Kepler/Text/Fan.lean:86); HOL
  `d_fan (x,V,E)` ↔ `dartOfFan V E` (Kepler/Text/Fan.lean:90).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `yfan`/`xfan` ↔ `yfan`/`xfan` (Kepler/Text/Fan.lean:158/154); HOL
  `aff_ge`/`aff_gt` ↔ `affGe`/`affGt` (Kepler/Geom/Aff.lean:42/39).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `dart_leads_into` ↔
  `dartLeadsInto` (Kepler/Text/TopologyFan.lean:4179).
- `FANADD_CONFORMING` binds `!E1` (an inner quantifier that shadows the outer
  `E1`). Because `conformingFan`/`nFan` need a `FAN` witness, the inner
  quantifier is encoded as `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), ...`,
  keeping the HOL `FAN x V E2` conjunct (cf. the same convention in
  `minimallyNonconformingFan`, Kepler/Text/ConformingDefs.lean:226).
- `ZSZIUQE_LEMMA` (HOL :6237) is the anonymous `:6237` entry of the task; its
  name is read from the HOL source.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`hypermapOfFan`/`sigmaFan`/`nFan`/`yfan` vocabulary, so
  nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto9

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## dart 计数与 `N_FAN` 严格下降（Conforming.hl:6178-6337） -/

/-- HOL Conforming.hl :6178-6236 `CARD_DART_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ~(v=w)
/\ E UNION {{v,w}}=E1
==>
CARD (dart (hypermap1_of_fanx (x,V,E1)))
= CARD (dart (hypermap1_of_fanx (x,V,E))) +2
```

编码说明：`CARD (dart ...)` ↦ `.darts.card`（见文件头）；`E UNION {{v,w}}=E1`
↦ `E ∪ {({v, w} : Set V3)} = E1`；额外携带 `hfan`、`hfan1`。

证明思路：`STEP3_REDUCE_FAN` 给出 `E1 = E ∪ {{v,w}}` 的结构，配合
`dartset_fully_surrounded_is_non_isolated_fan`（`dartOfFan = dart1OfFan`）；
`card_eq_image_in_d_fan` 把 `CARD (dart ...)` 化为 `dart1OfFan` 的像计数，
再用 `DART_FANADD_EQ_DART_FAN_ADD_2DART` 说明新增恰为两条 dart `(v,w)`、
`(w,v)`，最后 `CARD_UNION`/`FINITE_IMAGE` 完成。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084，HOL
  `dartset_fully_surrounded_is_non_isolated_fan`）
- `finite_dart1_fan`（Kepler/Text/Fan.lean，HOL `finite_d1_fan`）
- `Finset.card_union_of_disjoint`/`Set.ncard_union`（Mathlib，HOL `CARD_UNION`）
- 缺口：`card_eq_image_in_d_fan`、`DART_FANADD_EQ_DART_FAN_ADD_2DART`、
  `hypermap_of_fan_rep` 未移植 -/
private theorem darts_card_hypermapOfFan_eq_ncard {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) :
    (hypermapOfFan x V E hfan).darts.card = (dart1OfFan V E).ncard := by
  rw [hypermapOfFan]
  exact (Set.ncard_eq_toFinset_card (dart1OfFan V E) (finite_dart1_fan hfan)).symm

theorem CARD_DART_FANADD (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ v ≠ w ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      (hypermapOfFan x V E1 hfan1).darts.card =
        (hypermapOfFan x V E hfan).darts.card + 2 := by
  intro h
  rcases h with ⟨hfan, hcard, hfan80, hds, hds3, hfsub, hf1, hf2, hf3,
    hv, hu, hw, hvu, huw, hwv, hsigma, hvw, hE1⟩
  have hdarts : dartOfFan V E1 =
      dartOfFan V E ∪ ({(v, w), (w, v)} : Set (V3 × V3)) := by
    have h := DART_FANADD_EQ_DART_FAN_ADD_2DART hfan hcard hfan80 hds hds3 hfsub
      hf1 hf2 hf3 hv hu hw hvu huw hwv hsigma hvw hE1
    rw [show (fun p : V3 × V3 => (p.1, p.2)) = id from
      funext (fun _ => rfl)] at h
    simpa only [Set.image_id] using h
  have hcardE1 : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan hfan hcard hE1.symm
  have hdE : dartOfFan V E = dart1OfFan V E :=
    dartOfFan_eq_dart1_of_surrounded hfan hcard
  have hdE1 : dartOfFan V E1 = dart1OfFan V E1 :=
    dartOfFan_eq_dart1_of_surrounded hfan1 hcardE1
  have hset : dart1OfFan V E1 =
      dart1OfFan V E ∪ ({(v, w), (w, v)} : Set (V3 × V3)) := by
    rw [← hdE1, hdarts, hdE]
  have hdisj : Disjoint (dart1OfFan V E) ({(v, w), (w, v)} : Set (V3 × V3)) := by
    rw [Set.disjoint_left]
    intro d hd1 hd2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd2
    rcases hd2 with h | h
    · rw [h] at hd1
      exact hwv (by simpa only [dart1OfFan, Set.mem_setOf_eq, Set.pair_comm] using hd1)
    · rw [h] at hd1
      exact hwv (by simpa only [dart1OfFan, Set.mem_setOf_eq] using hd1)
  have hpair : (v, w) ≠ (w, v) := fun h => hvw (congrArg Prod.fst h)
  rw [darts_card_hypermapOfFan_eq_ncard hfan1,
    darts_card_hypermapOfFan_eq_ncard hfan, hset,
    Set.ncard_union_eq hdisj (finite_dart1_fan hfan), Set.ncard_pair hpair]

/-- HOL Conforming.hl :6237-6337 `ZSZIUQE_LEMMA`（任务中仅标 ":6237"）

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
==> N_FAN (x,V,E1)< N_FAN(x,V,E)
```

编码说明：`N_FAN` ↦ `nFan`（额外 `hfan` 见证）；`face (...) (x,v,w,...)= ds1`
↦ `(hypermapOfFan x V E1 hfan1).face (v, w) = ds1`（四元组收缩为点对，
见文件头）；`(x,w,v,u)=f10` 等 ↦ `f10 = (w, v)` 等。

证明思路：对 `E`、`E1` 分别展开 `nFan`，用
`FINITE_HYPERMAP_ORBITS`（`Hypermap.faceSet_finite`）与
`CARD_DART_FANADD` 比较 dart 总数；`EQ_CARD_FACE_FAN_AND_FANADD` 给出
两个 face_set 删除 `ds` 与 `{ds1,ds2}` 后的基数相等，`ds1`/`ds2` 的
面基数均为 3（`CARD_FACE_SET_GE_3`/`CARD_MINUS_ONE`），从而 `N_FAN` 下降。

候选已有引理：
- `CARD_DART_FANADD`（本文件上文）
- `EQ_CARD_FACE_FAN_AND_FANADD`（Kepler/Text/ConformingAuto14.lean:1185）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `nFan`（Kepler/Text/ConformingDefs.lean:204）
- `Hypermap.faceSet_finite`（Kepler/Text/Hypermap.lean:1016）
- 缺口：`NSUM_CONST`、`NSUM_EQ`、`NSUM_ADD`、`card_partition_formula`、
  `CARD_MINUS_ONE`、`disjoint_ds1_and_ds2`、`AAUHTVE` 未移植 -/
theorem ZSZIUQE_LEMMA (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      nFan x V E1 hfan1 < nFan x V E hfan := by
  sorry

/-! ## `fan80` 在加边后保持（Conforming.hl:6338-6521） -/

/-- HOL Conforming.hl :6338-6521 `FAN80_FANADD`

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
==> fan80(x,V,E1)
```

编码说明：与 `ZSZIUQE_LEMMA` 同假设块；结论 `fan80 x V E1`。

证明思路：展开 `fan80`，对任意 `{v',u'} ∈ E1` 分情况：`{v',u'}` 不是新增
边时由 `fan80 x V E` 直接继承；等于 `{v,w}`（或 `{w,v}`）时用
`SIGMA_FAN_OF_FANADD_AT_POINT1`/`..._AT_POINT3` 计算
`sigma_fan x V E1`，并用 `properties_fully_surrounded`、`azim` 的角度
不等式（`azim_trangle_le_azim_face_fan`、`sum4_azim_fan`、`sum5_azim_fan`）
把新角控制在 `(0, pi)`。

候选已有引理：
- `fan80`（Kepler/Text/Fan.lean:227）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `SIGMA_FAN_OF_FANADD_AT_POINT3-6`（Kepler/Text/ConformingAuto11.lean:554/681/830/987）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：`azim_trangle_le_azim_face_fan`、`sum4_azim_fan`、`sum5_azim_fan`、
  `condition_azim_le_pi`、`inverse1_sigma_fan`（`inverse1SigmaFan`）相关引理 -/
theorem FAN80_FANADD (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      fan80 x V E1 := by
  sorry

/-! ## 加边保持 conforming（Conforming.hl:6522-6566） -/

/-- HOL Conforming.hl :6522-6566 `FANADD_CONFORMING`

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
==>
conforming_fan (x,V,E1)
```

编码说明：HOL 内层 `!E1` 遮蔽外层 `E1`，编码为
`∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
conformingFan x V E2 hfan2`（保留 HOL 的 `FAN x V E2` 合取项，见文件头）；
外层结论为 `conformingFan x V E1 hfan1`。额外携带 `hfan`、`hfan1`。

证明思路：把极小性假设 `(!E1. ...)` 应用到外层 `E1`，只需证
`FAN x V E1`（`hfan1`）、`∀ v ∈ V, 1 < (setOfEdge v V E1).ncard`
（`add_edge_imp_card_set_edge_ge1_fan`）、`fan80 x V E1`（`FAN80_FANADD`）
与 `nFan x V E1 hfan1 < nFan x V E hfan`（`ZSZIUQE_LEMMA`）。

候选已有引理：
- `conformingFan`（Kepler/Text/ConformingDefs.lean:184）
- `FAN80_FANADD`（本文件上文）
- `ZSZIUQE_LEMMA`（本文件上文）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376） -/
theorem FANADD_CONFORMING (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      conformingFan x V E1 hfan1 := by
  sorry

/-! ## σ 在面外 dart 上的不变性（Conforming.hl:6567-6692） -/

/-- HOL Conforming.hl :6567-6692 `INVARANT_SIGMA_FAN_ADD`

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
/\ ds1 = face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)
/\ ds2 = face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ ~(y IN ds)
/\ y IN d_fan(x,V,E)
==>
sigma_fan x V E1 (pr2(y)) (pr3(y))= sigma_fan x V E (pr2(y)) (pr3(y))
```

编码说明：`y : V3 × V3`，`pr2(y)`/`pr3(y)` ↦ `y.1`/`y.2`；`ds1 = face ...`
↦ `ds1 = (hypermapOfFan x V E1 hfan1).face (v, w)`；`d_fan` ↦ `dartOfFan`。
额外携带 `hfan`、`hfan1`。

证明思路：`y ∈ dartOfFan V E` 且 `y ∉ ds`，由
`STEP3_REDUCE_FAN`/`d1_fan` 展开 `y = (v',w')`；分情况 `v' ∉ {v,w}`、
`v' = v`、`v' = w`，分别用 `SIGMA_FAN_OF_FANADD1`、
`SIGMA_FAN_OF_FANADD_AT_POINT4`/`..._AT_POINT5` 证明新旧 `sigma_fan` 相等
（`y = f1`/`y = f3` 的情形用 `EQ_PAIR_IMP_EQ_4_FAN` 导出与 `y ∉ ds` 矛盾）。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `SIGMA_FAN_OF_FANADD_AT_POINT4`（Kepler/Text/ConformingAuto11.lean:681）
- `SIGMA_FAN_OF_FANADD_AT_POINT5`（Kepler/Text/ConformingAuto11.lean:830）
- `EQ_PAIR_IMP_EQ_4_FAN`（Kepler/Text/PlanarityAuto15.lean:638）
- `dartOfFan`（Kepler/Text/Fan.lean:90）
- 缺口：`hypermap_of_fan_rep`、`f1_fan` 四元组表示与点对表示的桥接引理 -/
theorem INVARANT_SIGMA_FAN_ADD (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (y : V3 × V3)
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
    ds1 = (hypermapOfFan x V E1 hfan1).face (v, w) ∧
    ds2 = (hypermapOfFan x V E1 hfan1).face (w, v) ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    y ∉ ds ∧ y ∈ dartOfFan V E →
      sigmaFan x V E1 y.1 y.2 = sigmaFan x V E y.1 y.2 := by
  sorry

/-! ## `yfan` 在加边下的包含/等式（Conforming.hl:6693-6900） -/

/-- HOL Conforming.hl :6693-6742 `lemma_yfanadd_aff_ge`

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
==> yfan(x,V,E) SUBSET yfan(x,V,E1) UNION aff_ge {x} {v, w}
```

编码说明：`SUBSET`/`UNION` ↦ `⊆`/`∪`；`aff_ge {x} {v,w}` ↦
`affGe ({x} : Set V3) ({v, w} : Set V3)`。

证明思路：展开 `yfan = univ \ xfan` 与 `xfan`，用
`XFAN_EQ_UNIONS_AFF_GE_1_2` 把 `xfan` 写成 `aff_ge` 的并；对
`x' ∉ yfan(x,V,E1) ∪ aff_ge {x} {v,w}` 分情况，唯一的新增半空间
`aff_ge {x} {v,w}` 已被并项吸收，其余由 `E ⊆ E1` 直接继承。

候选已有引理：
- `yfan`（Kepler/Text/Fan.lean:158）、`xfan`（Kepler/Text/Fan.lean:154）
- `affGe`（Kepler/Geom/Aff.lean:42）
- 缺口：`XFAN_EQ_UNIONS_AFF_GE_1_2` 未移植 -/
theorem lemma_yfanadd_aff_ge (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      yfan x V E ⊆ yfan x V E1 ∪ affGe ({x} : Set V3) ({v, w} : Set V3) := by
  sorry

/-- HOL Conforming.hl :6743-6843 `lemma_yfanadd_aff_gt`

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
==> yfan(x,V,E) SUBSET yfan(x,V,E1) UNION aff_gt {x} {v, w}
```

编码说明：`aff_gt {x} {v,w}` ↦ `affGt ({x} : Set V3) ({v, w} : Set V3)`。

证明思路：由 `remark1_fan` 得 `{x,v,w}` 不共线，用
`aff_ge_eq_aff_gt_union_aff_ge` 把 `aff_ge {x} {v,w}` 分解为
`aff_gt {x} {v,w} ∪ aff_ge {x} {v} ∪ aff_ge {x} {w}`；再用
`lemma_yfanadd_aff_ge`，并证 `aff_ge {x} {v}`、`aff_ge {x} {w}` 包含在
`xfan(x,V,E)` 中（由 `exists_edge_fully_surround_fan` 找过 `v`、`w` 的边），
故它们对 `yfan` 无贡献。

候选已有引理：
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `lemma_yfanadd_aff_ge`（本文件上文）
- `exists_edge_fully_surround_fan`（Kepler/Text/PlanarityDarts.lean:480）
- `yfan`/`xfan`（Kepler/Text/Fan.lean:158/154）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异分量）
- 缺口：`remark1_fan` 的非共线分量未单列移植 -/
theorem lemma_yfanadd_aff_gt (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      yfan x V E ⊆ yfan x V E1 ∪ affGt ({x} : Set V3) ({v, w} : Set V3) := by
  sorry

/-- HOL Conforming.hl :6844-6868 `lemma_yfanadd_aff_gt1`

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
==>  yfan(x,V,E1) SUBSET yfan(x,V,E)
```

编码说明：结论 `yfan x V E1 ⊆ yfan x V E`（加边只会缩小 `yfan`）。

证明思路：展开 `yfan = univ \ xfan`，用 `XFAN_EQ_UNIONS_AFF_GE_1_2` 把
`xfan` 写成半空间并；由 `E ⊆ E1` 知 `xfan(x,V,E) ⊆ xfan(x,V,E1)`，
取补即得反向包含，最后 `SET_TAC`。

候选已有引理：
- `yfan`/`xfan`（Kepler/Text/Fan.lean:158/154）
- 缺口：`XFAN_EQ_UNIONS_AFF_GE_1_2` 未移植 -/
theorem lemma_yfanadd_aff_gt1 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      yfan x V E1 ⊆ yfan x V E := by
  sorry

/-- HOL Conforming.hl :6869-6900 `YFANADD_AFF_GT`

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
==> yfan(x,V,E) = yfan(x,V,E1) UNION aff_gt {x} {v, w}
```

编码说明：结论 `yfan x V E = yfan x V E1 ∪ affGt ({x}) ({v,w})`。

证明思路：双向包含。`⊆` 由 `lemma_yfanadd_aff_gt` 给出；`⊇` 由
`lemma_yfanadd_aff_gt1`（`yfan(x,V,E1) ⊆ yfan(x,V,E)`）与
`condition_aff_gt_subset_yfan`（`aff_gt {x} {v,w} ⊆ yfan(x,V,E)`）合并，
最后 `SET_TAC`。

候选已有引理：
- `lemma_yfanadd_aff_gt`（本文件上文）
- `lemma_yfanadd_aff_gt1`（本文件上文）
- `condition_aff_gt_subset_yfan`（Kepler/Text/ConformingAuto8.lean:629）
- `yfan`（Kepler/Text/Fan.lean:158）
- 缺口：`condition_aff_gt_subset_yfan` 需 `E1`/`FAN` 参数适配 -/
theorem YFANADD_AFF_GT (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      yfan x V E = yfan x V E1 ∪ affGt ({x} : Set V3) ({v, w} : Set V3) := by
  sorry

/-! ## `dartset_leads_into_fan` 的包含（Conforming.hl:6901-7118） -/

/-- HOL Conforming.hl :6901-7118 `dartset_leads_into_fanadd1`

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
==> dartset_leads_into_fan x V E1 ds1 SUBSET  dartset_leads_into_fan x V E ds
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；结论
`dartsetLeadsIntoFan x V E1 ds1 ⊆ dartsetLeadsIntoFan x V E ds`。

证明思路：`FAN80_FANADD` 得 `fan80 x V E1`；`DARTSET_LEADS_INTO_FAN`
把 `dartsetLeadsIntoFan` 化为对应 `dartLeadsInto`；取
`y = (sigma_fan x V E v u, v, ...)` 的公共 dart，用
`YFANADD_AFF_GT` 与 `CONNECTED_COMPONENT_MONO`
（`connectedComponentIn_mono`）证明两拓扑分量相等，从而包含成立。

候选已有引理：
- `FAN80_FANADD`（本文件上文）
- `DARTSET_LEADS_INTO_FAN`（Kepler/Text/PlanarityComponent.lean:375）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `dartLeadsInto`（Kepler/Text/TopologyFan.lean:4179）
- `YFANADD_AFF_GT`（本文件上文）
- `connectedComponentIn_mono`（Mathlib/Topology/Connected/Basic.lean:635，
  HOL `CONNECTED_COMPONENT_MONO`）
- 缺口：`IMAGE_F1_IN_FACE_IMP_IN_FACE`、`rw_dart_fan`/`rwDartFan`、
  `not_empty_rw_dart_fan` 未移植 -/
theorem dartset_leads_into_fanadd1 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
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
      dartsetLeadsIntoFan x V E1 ds1 ⊆ dartsetLeadsIntoFan x V E ds := by
  sorry

end Kepler.Text
