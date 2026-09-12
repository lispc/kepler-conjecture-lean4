/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 21
(Conforming.hl:13674-14522).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 21, Conforming.hl:13674-14522):
- `DART_FANADD_SUBSET_HALFSPACE1` (13674)
- `DART_FANADD_SUBSET_HALFSPACE2` (13870)
- `DART_FANADD_SUBSET_HALFSPACE3` (13997)  [HOL line reads "= prove" with a
  space after `let`; name as in HOL]
- `DART_FANADD_SUBSET_HALFSPACE4` (14053)
- `DART_FANADD_EQ_HALFSPACE` (14093)
- `HYUAZSE` (14143)
- `PIIJBJK` (14195)
- `expand_xfan_eq_aff_gt_aff_ge` (14258)
- `properties12_fan7` (14355)
- `yfan_union_aff_gt_fan` (14506)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings; same conventions as
batches 16-20):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL darts
  `real^3#real^3#real^3#real^3` ↔ pair darts `V3 × V3`
  (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`;
  the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`, `(x,u,w,v)` contract to the
  pairs `(w,v)`, `(v,u)`, `(u,w)`, and `(x,v,w,sigma_fan x V E1 v w)` /
  `(x,w,v,sigma_fan x V E1 w v)` to the pairs `(v,w)` / `(w,v)`.
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); `set_of_edge` ↦
  `setOfEdge` (Kepler/Text/Fan.lean:62); `sigma_fan` ↦ `sigmaFan`
  (Kepler/Text/Fan.lean:67); `fan80` ↦ `fan80` (Kepler/Text/Fan.lean:227);
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`; HOL
  `CARD ds >3` ↔ `3 < ds.ncard`; `N_FAN` ↦ `nFan`
  (Kepler/Text/ConformingDefs.lean:204).
- FAN-witness arguments: `hypermapOfFan` (Kepler/Text/Fan.lean:1169) and the
  ConformingDefs predicates `conformingFan`/`conformingHalfSpaceFan`/`nFan`
  need an explicit `FAN` witness, so theorems mentioning them carry an extra
  explicit `(hfan : FAN x V E)` (and `(hfan1 : FAN x V E1)` when
  `face (hypermap1_of_fanx (x,V,E1)) ...` occurs); the inner `!E1` conjunct
  is quantified `∀ E2 hfan2, ...` with `E2` renamed per the batch-16+
  convention. These are the only deviations from the HOL signatures.
- HOL `face_set(hypermap1_of_fanx (x,V,E))` ↦
  `(hypermapOfFan x V E hfan).faceSet`; `face (hypermap1_of_fanx (x,V,E)) d`
  ↦ `(hypermapOfFan x V E hfan).face d`; `dartset_leads_into_fan` ↦
  `dartsetLeadsIntoFan` (Kepler/Text/PlanarityComponent.lean:348);
  `f1_fan` ↦ `f1Fan` (Kepler/Text/ConformingDefs.lean:87).
- HOL `INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y)} | y IN ds}` ↦
  `⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}` (same
  encoding as `conformingHalfSpaceFan`, Kepler/Text/ConformingDefs.lean:121);
  `aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3)}` ↦
  `affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2}`.
- HOL `UNIONS {g y | y IN s}` ↦ `⋃ y ∈ s, g y`; `aff_gt` ↦ `affGt`
  (Kepler/Geom/Aff.lean:39); `aff_ge` ↦ `affGe` (Kepler/Geom/Aff.lean:42);
  `yfan` ↦ `yfan` (Kepler/Text/Fan.lean:158, = `Set.univ \ xfan x V E`);
  `(:real^3)` ↦ `(Set.univ : Set V3)`.
- Dependencies on earlier batches are imported: this file imports
  `Kepler.Text.ConformingAuto20` (which transitively pulls ConformingAuto19
  hence 18/17/16/15/14/12/...), plus `ConformingDefs` and
  `PlanarityAuto16` directly.
- HOL notions NOT ported that the HOL proofs use (the pool proofs must work
  around them): `dartset_fully_surrounded_is_non_isolated_fan`, `remark1_fan`,
  `face_subset_dart_fan` (closest existing: `face_subset_darts`,
  Kepler/Text/Hypermap.lean:854), `WEDGE_LUNE_GT`, `hypermap_of_fan_rep`
  (dart-membership characterization of `hypermapOfFan`), `AFF_GT_2_1` /
  `AFF_GT_1_1` / `AFF_GE_1_1` (definition-unfolding steps; closest existing:
  `aff_gt_1_2`, Kepler/Text/Planarity.lean:165, `aff_ge_1_2`,
  Kepler/Text/Planarity.lean:622), HOL `minimal` on `num->bool` (Mathlib
  `IsLeast`). No new definition is introduced for any of them.
- None of the ten statements is Mathlib-general: each mentions the
  repo-specific `FAN`/`sigmaFan`/`f1Fan`/`affGt`/`affGe`/`yfan`/
  `dartsetLeadsIntoFan`/`conforming*Fan` vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto20

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical
open MeasureTheory

/-! ## fanadd 增边后 ds2 / 三 partition 块落入开半空间（Conforming.hl:13674-14092） -/

/-- 三角锥 `affGt {x} {w,v,u}` 落入半空间 `affGt {x,w,z} {u}`（`z` 满足
`azim x w v u < azim x w z u < π`，即 `u` 在 `w` 处介于 `v` 与 `z` 之间）。

证明思路：`sum5_azim_fan` 由角序得 `azim x w z v ∈ (0,π)`；两次
`cross_dot_fully_surrounded_fan` 给 `crossProduct (w-x) (z-x)` 与 `v-x`、
`u-x` 的混合积均为正；`coplanar_cross_dot` 的逆否给四点不共面，从而
`aff_gt_3_1_rep_cross_dot` 把目标半空间写成混合积符号条件；对
`AFF_GT_1_3` 展开的锥系数 `t2,t3,t4 > 0` 直接计算混合积为正。 -/
private theorem cone_subset_halfspace_aux (x w z v u : V3)
    (hxw : x ≠ w) (hxu : x ≠ u) (hxv : x ≠ v)
    (hncwz : ¬ Collinear3 x w z) (hncwu : ¬ Collinear3 x w u)
    (hncwv : ¬ Collinear3 x w v)
    (hθ0 : 0 < azim x w z u) (hθπ : azim x w z u < Real.pi)
    (hlt : azim x w v u < azim x w z u)
    (hncop : ¬ Coplanar ({x, w, z, u} : Set V3)) :
    affGt ({x} : Set V3) ({w, v, u} : Set V3) ⊆
      affGt ({x, w, z} : Set V3) {u} := by
  have hsum := sum5_azim_fan (Ne.symm hxw) hncwz hncwv hncwu hlt.le
  have hnv : 0 ≤ azim x w v u := azim_nonneg x w v u
  have hθv0 : 0 < azim x w z v := by linarith
  have hθvπ : azim x w z v < Real.pi := by linarith
  have hposV := cross_dot_fully_surrounded_fan (v1 := w) (v := z) (u1 := v)
    hncwv hncwz hθv0 hθvπ
  have hposU := cross_dot_fully_surrounded_fan (v1 := w) (v := z) (u1 := u)
    hncwu hncwz hθ0 hθπ
  rw [aff_gt_3_1_rep_cross_dot x w z u hncop hposU]
  rw [AFF_GT_1_3 x w v u (Set.disjoint_singleton_left.mpr (by simp [hxw, hxu, hxv]))]
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum1, hyeq⟩ := hy
  have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
  have hzV : (y - x : V3) = t2 • (w - x) + t3 • (v - x) + t4 • (u - x) := by
    rw [hyeq, ht1]; module
  have hzV' : ((y - x : V3) : Fin 3 → ℝ) =
      t2 • ((w - x : V3) : Fin 3 → ℝ) + t3 • ((v - x : V3) : Fin 3 → ℝ) +
        t4 • ((u - x : V3) : Fin 3 → ℝ) := by
    have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hzV
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  rw [hzV']
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hz0 : crossProduct ((w - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((w - x : V3) : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]; exact dot_self_cross _ _
  rw [hz0, mul_zero, zero_add]
  exact add_pos (mul_pos ht3 hposV) (mul_pos ht4 hposU)

/-- HOL Conforming.hl :13674-13869 `DART_FANADD_SUBSET_HALFSPACE1`

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
==> dartset_leads_into_fan x V E1 ds2 SUBSET aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3) }
```

编码说明：同 `DART_FANADD_SUBSET_HALFSPACE`（batch 20），仅结论中 `ds1`
换成 `ds2`；内层 `!E1` 改名 `E2`/`hfan2`。

证明思路：batch-20 前置（`STEP3_REDUCE_FAN`、`YFANADD_AFF_GT`、
`EQ_PAIR_IMP_EQ_4_FAN` 把 `f2` 写成 `(u, sigmaFan x V E u w)`）；`f3` 的
`f1Fan`-像为 `(w, inverse1SigmaFan x V E w u)`，由
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan` 把
`affGt {x, w, inverse1SigmaFan ...} {u}` 表成含 `affGt {x,u,w} {v}` 的
交集；`FAN80_FANADD` + `SIGMA_FAN_OF_FANADD_AT_POINT3` + wedge/azim 链
（`sum4_azim_fan`/`sum5_azim_fan`/`azim_trangle_le_azim_face_fan`）与
`inter_aff_gt_3_1_is_aff_gt_2_2` 把 `ds2` 的代表元（`reperentation_of_ds2`
+ `KVQWYDL_lemma10` + `card_ds2_fanadd_eq3` + `ds2_in_face_set_fanadd`）
逐一送进该半空间，`SET_TAC` 收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `EQ_PAIR_IMP_EQ_4_FAN`（Kepler/Text/PlanarityAuto15.lean:546）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `card_ds2_fanadd_eq3`（Kepler/Text/ConformingAuto12.lean:455）
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）
- `reperentation_of_ds2`（Kepler/Text/ConformingAuto12.lean:596）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- `inter_aff_gt_3_1_is_aff_gt_2_2`（Kepler/Text/PlanarityAuto14.lean:468）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `sum5_azim_fan`（Kepler/Text/TopologyFan.lean:1175）
- `azim_trangle_le_azim_face_fan`（Kepler/Text/ConformingAuto11.lean:347）
- 缺口：`dartset_fully_surrounded_is_non_isolated_fan`、`remark1_fan`、
  `face_subset_dart_fan`、`WEDGE_LUNE_GT`、`hypermap_of_fan_rep` 未移植
  （替代见文件头） -/
theorem DART_FANADD_SUBSET_HALFSPACE1 (x : V3) (V : Set V3)
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
      dartsetLeadsIntoFan x V E1 ds2 ⊆
        affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2} := by
  intro h
  obtain ⟨-, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw,
    hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, -⟩ := h
  have pc : ∀ (a b : V3), ({a, b} : Set V3) = ({b, a} : Set V3) := by
    intro a b
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  -- `f3` 的第二分量：由 `f1_fan f2 = f3` 读出 `f3 = (w, inverse1SigmaFan x V E w u)`
  have hf3s : f3.2 = inverse1SigmaFan x V E w u := by
    have h6 : (f1Fan x V E f2).2 = f3.2 := congrArg Prod.snd hf23
    rw [← h6]
    simp only [f1Fan]
    rw [hpw, hu]
  -- E 侧：`{w, z} ∈ E` 与 `sigmaFan x V E w z = u`（`z = inverse1SigmaFan x V E w u`）
  have hwuE : ({w, u} : Set V3) ∈ E := by rw [pc]; exact huw
  have hwz : ({w, inverse1SigmaFan x V E w u} : Set V3) ∈ E :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).1 u hwuE
  have hsigwz : sigmaFan x V E w (inverse1SigmaFan x V E w u) = u :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 u hwuE
  -- E1 侧前置：基数条件、fan80、`ds2` 是 3 元面且 `ds2 = {f10, f20, f30}`
  have hcard1 : ∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan hfan hcard hE1.symm
  have h801 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
        hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1⟩
  have hds2fs : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds2_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
        hsig, hpu, hpw, hface1, hface2.symm, hf10, hf20, hf30, hE1⟩
  have hds2card : ds2.ncard = 3 :=
    card_ds2_fanadd_eq3 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
        hsig, hface1.symm, hface2.symm, hf10, hf20, hf30, hE1⟩
  have hds2rep : ds2 = ({f10, f20, f30} : Set (V3 × V3)) :=
    reperentation_of_ds2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
        hsig, hface1.symm, hface2.symm, hf10, hf20, hf30, hE1⟩
  -- 半空间侧角序：`azim x w z u ∈ (0,π)`（fan80）与 `azim x w v u < azim x w z u`
  have hθz : 0 < azim x w (inverse1SigmaFan x V E w u) u ∧
      azim x w (inverse1SigmaFan x V E w u) u < Real.pi := by
    have hh := h80 w (inverse1SigmaFan x V E w u) hwz
    rwa [hsigwz] at hh
  have hlt : azim x w v u < azim x w (inverse1SigmaFan x V E w u) u :=
    azim_trangle_le_azim_face_fan x V E v u w (inverse1SigmaFan x V E w u)
      ⟨hfan, hvu, huw, hwz, by rw [pc]; exact hwv, hsig, hsigwz, h80, hcard⟩
  -- 不共面：`properties_fully_surrounded` 于公共顶点 `w`、夹角 `azim x w z u`
  have hncop : ¬ Coplanar ({x, w, inverse1SigmaFan x V E w u, u} : Set V3) := by
    have hh : ¬ Coplanar ({x, u, w, inverse1SigmaFan x V E w u} : Set V3) :=
      properties_fully_surrounded (v := u) (u := w) (w := inverse1SigmaFan x V E w u)
        hfan huw hwz hθz.1 hθz.2
    have he : ({x, u, w, inverse1SigmaFan x V E w u} : Set V3) =
        ({x, w, inverse1SigmaFan x V E w u, u} : Set V3) := by
      ext p; simp; tauto
    rwa [he] at hh
  -- 互异性与不共线性
  obtain ⟨hvV, huV⟩ := fan_mem_of_edge hfan hvu
  obtain ⟨_, hwV⟩ := fan_mem_of_edge hfan huw
  have hxV : x ∉ V := hfan.2.2.2.1
  have hxw : x ≠ w := fun he => hxV (by rw [he]; exact hwV)
  have hxu : x ≠ u := fun he => hxV (by rw [he]; exact huV)
  have hxv : x ≠ v := fun he => hxV (by rw [he]; exact hvV)
  have hncwz : ¬ Collinear3 x w (inverse1SigmaFan x V E w u) :=
    fan_not_collinear hfan hwz
  have hncwu : ¬ Collinear3 x w u := fan_not_collinear hfan hwuE
  have hncop1 : ¬ Coplanar ({x, v, u, w} : Set V3) := by
    have hh := h80 u w huw
    rw [hsig] at hh
    exact properties_fully_surrounded hfan hvu huw hh.1 hh.2
  have hncvw : ¬ Collinear3 x v w := (notcoplanar_imp_notcollinear_fan hncop1).2.2
  have hncwv : ¬ Collinear3 x w v := by
    intro hc
    apply hncvw
    have h2 : Collinear ℝ ({x, w, v} : Set V3) := hc
    rw [show ({x, w, v} : Set V3) = ({x, v, w} : Set V3) from by ext p; simp; tauto] at h2
    exact h2
  -- 目标改写：半空间点第三坐标换成 `u`，锥写成 `affGt {x} {w, v, u}`
  have htk : (f1Fan x V E f3).2 = inverse1SigmaFan x V E f3.2 f3.1 := rfl
  have htfan := fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (v := w)
    (w := inverse1SigmaFan x V E w u) hfan hwz hcard h80
  rw [hsigwz] at htfan
  rw [htk, hw, hf3s, ← htfan, ← KVQWYDL_lemma10 hfan1 hcard1 h801 hds2fs hds2card,
    hds2rep, hf10, hf20, hf30]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact cone_subset_halfspace_aux x w (inverse1SigmaFan x V E w u) v u hxw hxu hxv
    hncwz hncwu hncwv hθz.1 hθz.2 hlt hncop

/-- HOL Conforming.hl :13870-13996 `DART_FANADD_SUBSET_HALFSPACE2`

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
==> aff_gt {x} {v,w} SUBSET aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3) }
```

编码说明：`aff_gt {x} {v,w}` ↦ `affGt ({x} : Set V3) {v, w}`；其余同
`DART_FANADD_SUBSET_HALFSPACE1`；内层 `!E1` 改名 `E2`/`hfan2`。

证明思路：同 HALFSPACE1 的 fanadd 前置；`f3` 的 `f1Fan`-像给出
`(w, inverse1SigmaFan x V E w u)`，`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
与 `aff_ge_eq_aff_gt_union_aff_ge`（配合 `aff_gt_inter_aff_gt`、
`aff_gt_1_2` 展开 `affGt {x,w,v} ∩ affGt {x,w,u}`）+ `fan80` 的
`properties_fully_surrounded` + `cross_dot_fully_surrounded_fan` /
`aff_gt_3_1_rep_cross_dot` 逐点比较系数即得子集关系；
`inverse1_sigma_fan_FANADD` + `FAN80_FANADD` 处理 E1 一侧。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `EQ_PAIR_IMP_EQ_4_FAN`（Kepler/Text/PlanarityAuto15.lean:546）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `inverse1_sigma_fan_FANADD`（Kepler/Text/ConformingAuto16.lean:521）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- 缺口：`remark1_fan`、`AFF_GT_2_1` 未移植（替代见文件头） -/
theorem DART_FANADD_SUBSET_HALFSPACE2 (x : V3) (V : Set V3)
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
      affGt ({x} : Set V3) {v, w} ⊆
        affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2} := by
  intro h
  obtain ⟨-, hcard, h80, -, -, -, -, hf23, -, hv, hu, hw, hvu, huw,
    hwv, hsig, -, hpw, -, -, -, -, -, -, -⟩ := h
  have pc : ∀ (a b : V3), ({a, b} : Set V3) = ({b, a} : Set V3) := by
    intro a b
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  -- `f3` 的第二分量：由 `f1_fan f2 = f3` 读出 `f3 = (w, inverse1SigmaFan x V E w u)`
  have hf3s : f3.2 = inverse1SigmaFan x V E w u := by
    have h6 : (f1Fan x V E f2).2 = f3.2 := congrArg Prod.snd hf23
    rw [← h6]
    simp only [f1Fan]
    rw [hpw, hu]
  have hwuE : ({w, u} : Set V3) ∈ E := by rw [pc]; exact huw
  have hwz : ({w, inverse1SigmaFan x V E w u} : Set V3) ∈ E :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).1 u hwuE
  have hsigwz : sigmaFan x V E w (inverse1SigmaFan x V E w u) = u :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 u hwuE
  -- 半空间侧角序：`azim x w z u ∈ (0,π)`（fan80）与 `azim x w v u < azim x w z u`
  have hθz : 0 < azim x w (inverse1SigmaFan x V E w u) u ∧
      azim x w (inverse1SigmaFan x V E w u) u < Real.pi := by
    have hh := h80 w (inverse1SigmaFan x V E w u) hwz
    rwa [hsigwz] at hh
  have hlt : azim x w v u < azim x w (inverse1SigmaFan x V E w u) u :=
    azim_trangle_le_azim_face_fan x V E v u w (inverse1SigmaFan x V E w u)
      ⟨hfan, hvu, huw, hwz, by rw [pc]; exact hwv, hsig, hsigwz, h80, hcard⟩
  -- 互异性与不共线性
  obtain ⟨hvV, huV⟩ := fan_mem_of_edge hfan hvu
  obtain ⟨_, hwV⟩ := fan_mem_of_edge hfan huw
  have hxV : x ∉ V := hfan.2.2.2.1
  have hxw : x ≠ w := fun he => hxV (by rw [he]; exact hwV)
  have hxu : x ≠ u := fun he => hxV (by rw [he]; exact huV)
  have hxv : x ≠ v := fun he => hxV (by rw [he]; exact hvV)
  have hncwz : ¬ Collinear3 x w (inverse1SigmaFan x V E w u) :=
    fan_not_collinear hfan hwz
  have hncwu : ¬ Collinear3 x w u := fan_not_collinear hfan hwuE
  have hncop1 : ¬ Coplanar ({x, v, u, w} : Set V3) := by
    have hh := h80 u w huw
    rw [hsig] at hh
    exact properties_fully_surrounded hfan hvu huw hh.1 hh.2
  have hncvw : ¬ Collinear3 x v w := (notcoplanar_imp_notcollinear_fan hncop1).2.2
  have hncwv : ¬ Collinear3 x w v := by
    intro hc
    apply hncvw
    have h2 : Collinear ℝ ({x, w, v} : Set V3) := hc
    rw [show ({x, w, v} : Set V3) = ({x, v, w} : Set V3) from by ext p; simp; tauto] at h2
    exact h2
  have hncop : ¬ Coplanar ({x, w, inverse1SigmaFan x V E w u, u} : Set V3) := by
    have hh : ¬ Coplanar ({x, u, w, inverse1SigmaFan x V E w u} : Set V3) :=
      properties_fully_surrounded (v := u) (u := w) (w := inverse1SigmaFan x V E w u)
        hfan huw hwz hθz.1 hθz.2
    have he : ({x, u, w, inverse1SigmaFan x V E w u} : Set V3) =
        ({x, w, inverse1SigmaFan x V E w u, u} : Set V3) := by
      ext p; simp; tauto
    rwa [he] at hh
  -- 角序传递：`azim x w z v ∈ (0,π)`
  have hsum := sum5_azim_fan (Ne.symm hxw) hncwz hncwv hncwu hlt.le
  have hnv : 0 ≤ azim x w v u := azim_nonneg x w v u
  have hθv0 : 0 < azim x w (inverse1SigmaFan x V E w u) v := by linarith
  have hθvπ : azim x w (inverse1SigmaFan x V E w u) v < Real.pi := by linarith
  have hposV := cross_dot_fully_surrounded_fan (v1 := w) (v := inverse1SigmaFan x V E w u)
    (u1 := v) hncwv hncwz hθv0 hθvπ
  have hposU := cross_dot_fully_surrounded_fan (v1 := w) (v := inverse1SigmaFan x V E w u)
    (u1 := u) hncwu hncwz hθz.1 hθz.2
  -- 目标改写：半空间点第三坐标换成 `u`，锥 `affGt {x} {v,w}` 按 `aff_gt_1_2` 展开
  have htk : (f1Fan x V E f3).2 = inverse1SigmaFan x V E f3.2 f3.1 := rfl
  have htfan := fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (v := w)
    (w := inverse1SigmaFan x V E w u) hfan hwz hcard h80
  rw [hsigwz] at htfan
  rw [htk, hw, hf3s, ← htfan,
    aff_gt_1_2 (Set.disjoint_singleton_left.mpr (by simp [hxv, hxw])),
    aff_gt_3_1_rep_cross_dot x w (inverse1SigmaFan x V E w u) u hncop hposU]
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨t1, t2, t3, ht2, ht3, hsum1, hyeq⟩ := hy
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  have hzV : (y - x : V3) = t2 • (v - x) + t3 • (w - x) := by
    rw [hyeq, ht1]; module
  have hzV' : ((y - x : V3) : Fin 3 → ℝ) =
      t2 • ((v - x : V3) : Fin 3 → ℝ) + t3 • ((w - x : V3) : Fin 3 → ℝ) := by
    have hh := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hzV
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using hh
  rw [hzV']
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hz0 : crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((inverse1SigmaFan x V E w u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((w - x : V3) : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]; exact dot_self_cross _ _
  rw [hz0, mul_zero, add_zero]
  exact mul_pos ht2 hposV

/-- HOL Conforming.hl :13997-14052 `DART_FANADD_SUBSET_HALFSPACE3`
（HOL 该行 `let` 后多一空格 "= prove"，名字照抄）

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
==> dartset_leads_into_fan x V E ds SUBSET aff_gt {x, pr2 f3, pr3 f3} {pr3 (f1_fan x V E f3) }
```

编码说明：结论中 `dartset_leads_into_fan x V E ds` 用的是原扇 E（非
E1）；内层 `!E1` 改名 `E2`/`hfan2`。

证明思路：batch-20 前置（`STEP3_REDUCE_FAN`、`YFANADD_AFF_GT`）；
`rep_dartset_leads_into_fan_ds`（batch 18）把
`dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
affGt {x} {v,w}` 写成 `dartsetLeadsIntoFan x V E ds` 的重 representation；
再对三个块分别用 batch-20 的 `DART_FANADD_SUBSET_HALFSPACE`（ds1 块）与
本文件的 `DART_FANADD_SUBSET_HALFSPACE1`（ds2 块）、
`DART_FANADD_SUBSET_HALFSPACE2`（aff_gt 块），三并集即含于半空间，
`SET_TAC` 收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `rep_dartset_leads_into_fan_ds`（Kepler/Text/ConformingAuto18.lean:597）
- `DART_FANADD_SUBSET_HALFSPACE`（Kepler/Text/ConformingAuto20.lean:930）
- `DART_FANADD_SUBSET_HALFSPACE1`（本文件上文）
- `DART_FANADD_SUBSET_HALFSPACE2`（本文件上文）
- 缺口：`dartset_fully_surrounded_is_non_isolated_fan`、`face_subset_dart_fan`
  未移植（替代见文件头） -/
theorem DART_FANADD_SUBSET_HALFSPACE3 (x : V3) (V : Set V3)
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
      dartsetLeadsIntoFan x V E ds ⊆
        affGt ({x, f3.1, f3.2} : Set V3) {(f1Fan x V E f3).2} := by
  intro h
  obtain ⟨hfan0, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw,
    hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩ := h
  have hrep := rep_dartset_leads_into_fan_ds x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    (dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w}) hfan hfan1
    ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
      hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH, rfl⟩
  have h1 := DART_FANADD_SUBSET_HALFSPACE x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    hfan hfan1 ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu,
      huw, hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩
  have h2 := DART_FANADD_SUBSET_HALFSPACE1 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    hfan hfan1 ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu,
      huw, hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩
  have h3 := DART_FANADD_SUBSET_HALFSPACE2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    hfan hfan1 ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu,
      huw, hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩
  rw [hrep]
  intro z hz
  simp only [Set.mem_union] at hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · exact h1 hz
    · exact h2 hz
  · exact h3 hz

/-- HOL Conforming.hl :14053-14092 `DART_FANADD_SUBSET_HALFSPACE4`

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
==> dartset_leads_into_fan x V E ds SUBSET INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds}
```

编码说明：`INTERS {g y | y IN ds}` ↦ `⋂ y ∈ ds, g y`（同
`conformingHalfSpaceFan` 的编码，Kepler/Text/ConformingDefs.lean:121）；
内层 `!E1` 改名 `E2`/`hfan2`。

证明思路：把结论按 `Set.iInter₂` 展开（对任意 `y ∈ ds`）；用 batch-20 的
`INDUCTION_FANADD` 沿面转移，把 `y` 换成 `f3'`（其 `pr2`/`pr3` 记 `v'`/
`w'`，`E1'`、`ds1'`/`ds2'`、`f10'`/`f20'`/`f30'` 为对应 abbreviations），
对换后的数据用本文件 `DART_FANADD_SUBSET_HALFSPACE3` 即得。

候选已有引理：
- `INDUCTION_FANADD`（Kepler/Text/ConformingAuto20.lean:435）
- `DART_FANADD_SUBSET_HALFSPACE3`（本文件上文） -/
theorem DART_FANADD_SUBSET_HALFSPACE4 (x : V3) (V : Set V3)
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
      dartsetLeadsIntoFan x V E ds ⊆
        ⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} := by
  intro h
  obtain ⟨hfan0, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw,
    hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩ := h
  intro z hz
  simp only [Set.mem_iInter]
  intro y hy
  obtain ⟨f1', f2', f3', hsub', h12', h23', h31', he23', he31', he12', hsig', hc23',
    hc12', hy3⟩ :=
    INDUCTION_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y hfan hfan1
      ⟨hfan0, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
        hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH, hy⟩
  have hfanE1' : FAN x V (E ∪ {({f1'.1, f3'.1} : Set V3)}) :=
    STEP3_REDUCE_FAN hfan hcard h80 hds h3lt hsub' h12' h23' h31' rfl rfl rfl he12'
      he23' he31' hsig' rfl
  rw [hy3]
  exact DART_FANADD_SUBSET_HALFSPACE3 x V E (E ∪ {({f1'.1, f3'.1} : Set V3)}) ds f1' f2'
    f3' f1'.1 f2'.1 f3'.1
    ((hypermapOfFan x V (E ∪ {({f1'.1, f3'.1} : Set V3)}) hfanE1').face (f1'.1, f3'.1))
    ((hypermapOfFan x V (E ∪ {({f1'.1, f3'.1} : Set V3)}) hfanE1').face (f3'.1, f1'.1))
    (f3'.1, f1'.1) (f1'.1, f2'.1) (f2'.1, f3'.1) hfan hfanE1'
    ⟨hfan0, hcard, h80, hds, h3lt, hsub', h12', h23', h31', rfl, rfl, rfl, he12', he23',
      he31', hsig', hc12'.symm, hc23'.symm, rfl, rfl, rfl, rfl, rfl, rfl, IH⟩ hz

/-- HOL Conforming.hl :14093-14142 `DART_FANADD_EQ_HALFSPACE`

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
==> dartset_leads_into_fan x V E ds = INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds}
```

编码说明：同 `DART_FANADD_SUBSET_HALFSPACE4` 的编码，结论为等式；内层
`!E1` 改名 `E2`/`hfan2`。

证明思路：与 HALFSPACE3 同样的 batch-20 前置 +
`rep_dartset_leads_into_fan_ds`；⊇ 方向由 batch-20 `lemma_HYUAZSE`
（`U1 = ⋂ ...`、`U = ds1 ∪ ds2 ∪ affGt {x} {v,w}` 时 `U1 ⊆ U`）给出，
⊆ 方向由本文件 `DART_FANADD_SUBSET_HALFSPACE4` 给出，`SET_TAC` 收口。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `rep_dartset_leads_into_fan_ds`（Kepler/Text/ConformingAuto18.lean:597）
- `DART_FANADD_SUBSET_HALFSPACE4`（本文件上文）
- `lemma_HYUAZSE`（Kepler/Text/ConformingAuto20.lean:845）
- 缺口：`dartset_fully_surrounded_is_non_isolated_fan`、`face_subset_dart_fan`
  未移植（替代见文件头） -/
theorem DART_FANADD_EQ_HALFSPACE (x : V3) (V : Set V3)
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
      dartsetLeadsIntoFan x V E ds =
        ⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} := by
  intro h
  obtain ⟨hfan0, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw,
    hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩ := h
  have hrep := rep_dartset_leads_into_fan_ds x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20
    f30 (dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w}) hfan hfan1
    ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
      hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH, rfl⟩
  have hsub4 := DART_FANADD_SUBSET_HALFSPACE4 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20
    f30 hfan hfan1 ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw,
      hvu, huw, hwv, hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH⟩
  have hyz := lemma_HYUAZSE x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
    (dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w})
    (⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}) hfan hfan1
    ⟨hfan, hcard, h80, hds, h3lt, hsub, hf12, hf23, hf31, hv, hu, hw, hvu, huw, hwv,
      hsig, hpu, hpw, hface1, hface2, hf10, hf20, hf30, hE1, IH, rfl, rfl⟩
  rw [hrep] at hsub4 ⊢
  exact Set.Subset.antisymm hsub4 hyz

/-! ## conforming_half_space_fan 与 conforming_fan 的归纳证明（Conforming.hl:14143-14257） -/

/-- HOL Conforming.hl :14143-14194 `HYUAZSE`

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
==> conforming_half_space_fan(x,V,E)
```

编码说明：`conforming_half_space_fan` ↦ `conformingHalfSpaceFan`
（Kepler/Text/ConformingDefs.lean:121，需 `hfan` 见证）；内层 `!E1` 量化为
`∀ E1 hfan1, ...`。

证明思路：按定义展开后对任意面 `f` 分 `CARD f = 3` 与 `CARD f > 3`
两情形：`CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN` 给出 `3 ≤ CARD f`；
=3 时用 `KVQWYDL_lemma10` + `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
把 `f` 写成 `{f1,f2,f3}`，三半空间之交由
`inter_aff_gt_3_1_is_aff_gt_1_3` 收成单个 `aff_gt`，等于
`dartsetLeadsIntoFan x V E f`；>3 时用
`nonconformin_fan_imp_exist_3point_in_face` 取三元组，按 batch-21 的
abbreviations（E1 = E ∪ {{v,w}} 等）套 `DART_FANADD_EQ_HALFSPACE`。

候选已有引理：
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`
  （Kepler/Text/PlanarityAuto15.lean:139）
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- `nonconformin_fan_imp_exist_3point_in_face`
  （Kepler/Text/ConformingAuto8.lean:483）
- `DART_FANADD_EQ_HALFSPACE`（本文件上文） -/
theorem HYUAZSE (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    (∀ (E1 : Set (Set V3)) (hfan1 : FAN x V E1),
      FAN x V E1 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard) ∧
      fan80 x V E1 ∧
      nFan x V E1 hfan1 < nFan x V E hfan →
        conformingFan x V E1 hfan1) →
      conformingHalfSpaceFan x V E hfan := by
  intro h
  obtain ⟨-, hcard, h80, IH⟩ := h
  show ∀ ds ∈ (hypermapOfFan x V E hfan).faceSet,
    dartsetLeadsIntoFan x V E ds =
      ⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}
  intro ds hds
  have hge := CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN hfan hcard hds
  rcases Nat.lt_or_ge ds.ncard 3 with h3 | h3
  · exact absurd h3 (Nat.not_lt.mpr hge)
  rcases Nat.eq_or_lt_of_le h3 with h3eq | h3lt
  · -- CARD ds = 3
    obtain ⟨g1, g2, g3, hset, hk12, hk23, hk31, he23, he31, he12, hsig, hc31, hc12,
      hc23⟩ := CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1 hfan hcard hds h3eq.symm
    have hσinv : ∀ {a b : V3}, {a, b} ∈ E →
        inverse1SigmaFan x V E a b = inverseSigmaFan x V E a b :=
      fun hb => inverse_sigma_fan_eq_inverse1 hfan hb
    have ht22 : g2.2 = inverseSigmaFan x V E g1.2 g1.1 := by rw [← hk12]; rfl
    have ht32 : g3.2 = inverseSigmaFan x V E g2.2 g2.1 := by rw [← hk23]; rfl
    have ht12 : g1.2 = inverseSigmaFan x V E g3.2 g3.1 := by rw [← hk31]; rfl
    have hapk1 : (f1Fan x V E g1).2 = g3.1 := by
      show inverse1SigmaFan x V E g1.2 g1.1 = g3.1
      rw [hσinv (show ({g1.2, g1.1} : Set V3) ∈ E by rw [← hc12, Set.pair_comm]; exact he12),
        ← ht22, hc31]
    have hapk2 : (f1Fan x V E g2).2 = g1.1 := by
      show inverse1SigmaFan x V E g2.2 g2.1 = g1.1
      rw [hσinv (show ({g2.2, g2.1} : Set V3) ∈ E by rw [← hc31, Set.pair_comm]; exact he23),
        ← ht32, hc23]
    have hapk3 : (f1Fan x V E g3).2 = g2.1 := by
      show inverse1SigmaFan x V E g3.2 g3.1 = g2.1
      rw [hσinv (show ({g3.2, g3.1} : Set V3) ∈ E by rw [← hc23, Set.pair_comm]; exact he31),
        ← ht12, hc12]
    have hcop : ¬ Coplanar ({x, g1.1, g2.1, g3.1} : Set V3) := by
      have h80bc := h80 g2.1 g3.1 he23
      rw [hsig] at h80bc
      exact properties_fully_surrounded hfan he12 he23 h80bc.1 h80bc.2
    rw [← KVQWYDL_lemma10 hfan hcard h80 hds h3eq.symm, hset]
    simp only [Set.image_insert_eq, Set.image_singleton, Set.biInter_insert,
      Set.biInter_singleton]
    rw [hapk1, hapk2, hapk3, ← hc12, ← hc31, ← hc23,
      ← inter_aff_gt_3_1_is_aff_gt_1_3 x g1.1 g2.1 g3.1 hcop, Set.inter_assoc]
  · -- 3 < CARD ds
    obtain ⟨k1, k2, k3, hksub, hk12, hk23, hk3ne, he23, he31ne, he12, hsig, hc31,
      hc12⟩ := nonconformin_fan_imp_exist_3point_in_face hfan hcard h80 hds h3lt
    have hfanE1 : FAN x V (E ∪ {({k1.1, k3.1} : Set V3)}) :=
      STEP3_REDUCE_FAN hfan hcard h80 hds h3lt hksub hk12 hk23 hk3ne rfl rfl rfl
        he12 he23 he31ne hsig rfl
    exact DART_FANADD_EQ_HALFSPACE x V E (E ∪ {({k1.1, k3.1} : Set V3)}) ds k1 k2 k3
      k1.1 k2.1 k3.1
      ((hypermapOfFan x V (E ∪ {({k1.1, k3.1} : Set V3)}) hfanE1).face (k1.1, k3.1))
      ((hypermapOfFan x V (E ∪ {({k1.1, k3.1} : Set V3)}) hfanE1).face (k3.1, k1.1))
      (k3.1, k1.1) (k1.1, k2.1) (k2.1, k3.1) hfan hfanE1
      ⟨hfan, hcard, h80, hds, h3lt, hksub, hk12, hk23, hk3ne, rfl, rfl, rfl,
        he12, he23, he31ne, hsig, hc12.symm, hc31.symm, rfl, rfl, rfl, rfl, rfl, rfl,
        IH⟩

/-- HOL Conforming.hl :14195-14257 `PIIJBJK`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
==> conforming_fan(x,V,E)
```

编码说明：`conforming_fan` ↦ `conformingFan`
（Kepler/Text/ConformingDefs.lean:184，需 `hfan` 见证）；HOL 证明中的
`minimal (S:num->bool)` 极小反例构造是证明内部内容（Mathlib 对应
`IsLeast`），不进陈述。

证明思路：反证，设 `¬conformingFan x V E hfan`；HOL 取
`S = {n | ∃ x' V' E1, x' = x ∧ V' = V ∧ FAN ∧ fan80 ∧ ¬conforming ∧
N_FAN = n}` 的极小元 `n`；`n = 0` 由 `nonconformin_fan_imp_n_fan_ge0`
排除；否则对 `N_FAN x V E1 < n` 的 E1 用极小性得归纳前提，`HYUAZSE` +
`TXFBALB_VERSION` + `GGZWYRM` + `conforming_bijection_fanadd_verrion`
拼出 `conformingFan x V E1 hfan1`，与 `¬conformingFan` 矛盾。

候选已有引理：
- `conformingFan`（Kepler/Text/ConformingDefs.lean:184）
- `nonconformin_fan_imp_n_fan_ge0`（Kepler/Text/ConformingAuto8.lean:267）
- `HYUAZSE`（本文件上文）
- `TXFBALB_VERSION`（Kepler/Text/ConformingAuto20.lean:143）
- `GGZWYRM`（Kepler/Text/ConformingAuto20.lean:703）
- `conforming_bijection_fanadd_verrion`
  （Kepler/Text/ConformingAuto20.lean:194）
- `conformingBijectionFan`（Kepler/Text/ConformingDefs.lean:104） -/
theorem PIIJBJK (x : V3) (V : Set V3) (E : Set (Set V3)) (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E →
      conformingFan x V E hfan := by
  rintro ⟨_, hcard, h80⟩
  by_cases hconf : conformingFan x V E hfan
  · exact hconf
  set S : Set ℕ := {n | ∃ (E1 : Set (Set V3)) (h1 : FAN x V E1),
      FAN x V E1 ∧ (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard) ∧
        fan80 x V E1 ∧ ¬ conformingFan x V E1 h1 ∧ nFan x V E1 h1 = n} with hSdef
  have hne : S.Nonempty := ⟨nFan x V E hfan, E, hfan, hfan, hcard, h80, hconf, rfl⟩
  obtain ⟨n, hnS, hnmin⟩ :
      ∃ n, n ∈ S ∧ ∀ m ∈ S, n ≤ m :=
    ⟨sInf S, Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
  rw [hSdef, Set.mem_setOf_eq] at hnS
  obtain ⟨E1, h1, h1E, h1card, h180, h1conf, hn1⟩ := hnS
  have IH : ∀ (E2 : Set (Set V3)) (h2 : FAN x V E2),
      FAN x V E2 ∧ (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
        fan80 x V E2 ∧ nFan x V E2 h2 < nFan x V E1 h1 →
        conformingFan x V E2 h2 := by
    intro E2 h2 ⟨h2E, h2card, h280, hlt⟩
    by_contra h2conf
    have hle : n ≤ nFan x V E2 h2 :=
      hnmin _ ⟨E2, h2, h2E, h2card, h280, h2conf, rfl⟩
    rw [← hn1] at hle
    omega
  have hbij : conformingBijectionFan x V E1 h1 :=
    conforming_bijection_fanadd_verrion x V E1 h1 ⟨h1E, h1card, h180, h1conf, IH⟩
  have hhalf : conformingHalfSpaceFan x V E1 h1 :=
    HYUAZSE x V E1 h1 ⟨h1E, h1card, h180, IH⟩
  have hsol : conformingSolidAngleFan x V E1 h1 :=
    TXFBALB_VERSION x V E1 h1 ⟨h1E, h1card, h180, h1conf, IH⟩
  have hdiag : conformingDiagonalFan x V E1 h1 :=
    GGZWYRM x V E1 h1 ⟨h1E, h1card, h180, IH⟩
  exact absurd ⟨h1card, h180, hbij, hhalf, hsol, hdiag⟩ h1conf

/-! ## 边锥的展开与两并集不交（Conforming.hl:14258-14522） -/

/-- HOL Conforming.hl :14258-14354 `expand_xfan_eq_aff_gt_aff_ge`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
==> UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e}= (UNIONS {aff_gt {x} e | e IN E}) UNION (UNIONS {aff_ge {x} {v}| v IN V})
```

编码说明：HOL `UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e}` 即
`⋃ e ∈ E, affGe ({x} : Set V3) e`（= `xfan x V E`，见
`XFAN_EQ_UNIONS_AFF_GE_1_2`，Kepler/Text/ConformingAuto3.lean:306）；按
HOL 字面以 `⋃`/`∪` 编码，不引入 `xfan` 记号。

证明思路：外延性 + 双向。⊆：`expand_edge_graph_fan` 把边 `e` 写成
`{v,w}`，`aff_ge_eq_aff_gt_union_aff_ge` 展开
`affGe {x} {v,w} = affGt {x} {v,w} ∪ affGe {x} {v} ∪ affGe {x} {w}`，
分三种归属；⊇：`aff_gt_subset_aff_ge` 处理第一支；第二支中 `v` 有邻居
（`set_of_edge` 基数 > 1），`exists_inf_element_fix_fan` 取 `u1` 使
`{v,u1} ∈ E`，再用 `aff_ge_eq_aff_gt_union_aff_ge` 把 `v` 归入
`affGe {x} {v,u1}`。

候选已有引理：
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `aff_gt_subset_aff_ge`（Kepler/Text/Planarity.lean:3878）
- `exists_inf_element_fix_fan`（Kepler/Text/Planarity.lean:2608）
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306）
- `xfan`（Kepler/Text/Fan.lean:154）
- 缺口：`remark1_fan` 未移植（替代见文件头） -/
theorem expand_xfan_eq_aff_gt_aff_ge (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E →
      (⋃ e ∈ E, affGe ({x} : Set V3) e) =
        (⋃ e ∈ E, affGt ({x} : Set V3) e) ∪
          ⋃ v ∈ V, affGe ({x} : Set V3) {v} := by
  rintro ⟨hfan, hcard, h80⟩
  have hxV : x ∉ V := hfan.2.2.2.1
  ext y
  constructor
  · intro hy
    obtain ⟨e, he, hy⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨v, w, hevw⟩ := expand_edge_graph_fan hfan he
    have hvwE : ({v, w} : Set V3) ∈ E := by rw [← hevw]; exact he
    obtain ⟨hv, hw⟩ := fan_mem_of_edge hfan hvwE
    have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan hvwE
    rw [hevw, aff_ge_eq_aff_gt_union_aff_ge hnc] at hy
    simp only [Set.mem_union] at hy
    rcases hy with (hy | hy) | hy
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨{v, w}, hvwE, hy⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, hy⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩)
  · intro hy
    rcases (Set.mem_union y _ _).1 hy with hy | hy
    · obtain ⟨e, he, hy⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨v, w, hevw⟩ := expand_edge_graph_fan hfan he
      have hvwE : ({v, w} : Set V3) ∈ E := by rw [← hevw]; exact he
      obtain ⟨hv, hw⟩ := fan_mem_of_edge hfan hvwE
      have hxv : x ≠ v := fun hh => hxV (by rw [hh]; exact hv)
      have hxw : x ≠ w := fun hh => hxV (by rw [hh]; exact hw)
      have hdis : Disjoint ({x} : Set V3) {v, w} :=
        Set.disjoint_singleton_left.mpr (by simp [hxv, hxw])
      rw [hevw] at hy
      have hy' : y ∈ affGe ({x} : Set V3) {v, w} := aff_gt_subset_aff_ge hdis hy
      exact Set.mem_iUnion₂.mpr ⟨{v, w}, hvwE, hy'⟩
    · obtain ⟨v, hv, hy⟩ := Set.mem_iUnion₂.mp hy
      have hcardv : 1 < (setOfEdge v V E).ncard := hcard v hv
      have hne : (setOfEdge v V E).Nonempty := by
        by_contra h0
        rw [Set.not_nonempty_iff_eq_empty.mp h0, Set.ncard_empty] at hcardv
        linarith
      obtain ⟨u, hu⟩ := hne
      have huE : ({v, u} : Set V3) ∈ E :=
        (properties_of_setOfEdge_fan x V E v u hfan).mpr hu
      have hnc : ¬ Collinear3 x v u := fan_not_collinear hfan huE
      have hy' : y ∈ affGe ({x} : Set V3) {v, u} := by
        rw [aff_ge_eq_aff_gt_union_aff_ge hnc]
        exact Or.inl (Or.inr hy)
      exact Set.mem_iUnion₂.mpr ⟨{v, u}, huE, hy'⟩

/-- HOL Conforming.hl :14355-14505 `properties12_fan7`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
==> (UNIONS {aff_gt {x} e | e IN E}) INTER (UNIONS {aff_ge {x} {v}| v IN V})={}
```

编码说明：`UNIONS {...}` ↦ `⋃ ... ∈ ..., ...`；`{}` ↦ `∅`。

证明思路：反证，取 `y` 属于两并集之交；`expand_edge_graph_fan` 写
`e = {v',w}`，`aff_ge_eq_aff_gt_union_aff_ge` 展开；`v`（属第二并集）
在 `E` 中有邻居，`exists_inf_element_fix_fan` 取 `u''`；再由
`aff_gt_1_2`/`aff_ge_1_2` 的表示分解系数，`properties_of_fan7`
（Kepler/Text/Planarity.lean:4243）判定 `v` 只能是 `v'` 或 `w`，两种情形
都推出 `w ∈ aff {x,v'}`（或对称情形），与 `remark1_fan` 的不共线性质
（最近替代 `fan_not_collinear`/`notcoplanar_imp_notcollinear_fan`）矛盾。

候选已有引理：
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `exists_inf_element_fix_fan`（Kepler/Text/Planarity.lean:2608）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `properties_of_fan7`（Kepler/Text/Planarity.lean:4243）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- 缺口：`remark1_fan`、`AFF_GT_1_2`/`AFF_GE_1_1`（展开型）未移植
  （替代见文件头） -/
theorem properties12_fan7 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E →
      (⋃ e ∈ E, affGt ({x} : Set V3) e) ∩
          ⋃ v ∈ V, affGe ({x} : Set V3) {v} = ∅ := by
  sorry

/-- HOL Conforming.hl :14506-14522 `yfan_union_aff_gt_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
==> yfan(x,V,E) UNION (UNIONS {aff_gt {x} e | e IN E}) = (:real^3) DIFF (UNIONS {aff_ge {x} {v}| v IN V})
```

编码说明：`yfan` ↦ `yfan`（Kepler/Text/Fan.lean:158，
`Set.univ \ xfan x V E`）；`(:real^3)` ↦ `(Set.univ : Set V3)`；`DIFF` ↦
`\`。

证明思路：`XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306）
把 `yfan x V E` 写成 `Set.univ \ ⋃ e ∈ E, affGe {x} e`，再由本文件的
`expand_xfan_eq_aff_gt_aff_ge`（把 `⋃ affGe` 换成 `⋃ affGt ∪ ⋃ 单点
affGe`）与 `properties12_fan7`（两 ⋃ 不交），集合等式
`A ∪ (B ∪ C) = UNIV \ C`（当 `B ∩ C = ∅` 且 `A = UNIV \ (B ∪ C)`）由
`SET_TAC`/`Set` 引理收口。

候选已有引理：
- `yfan`（Kepler/Text/Fan.lean:158）
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306）
- `expand_xfan_eq_aff_gt_aff_ge`（本文件上文）
- `properties12_fan7`（本文件上文） -/
theorem yfan_union_aff_gt_fan (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E →
      yfan x V E ∪ (⋃ e ∈ E, affGt ({x} : Set V3) e) =
        (Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v} := by
  rintro ⟨hfan, hcard, h80⟩
  have hxp := expand_xfan_eq_aff_gt_aff_ge x V E ⟨hfan, hcard, h80⟩
  have hdis := properties12_fan7 x V E ⟨hfan, hcard, h80⟩
  have hBC : ∀ y : V3, y ∈ (⋃ e ∈ E, affGt ({x} : Set V3) e) →
      y ∉ ⋃ v ∈ V, affGe ({x} : Set V3) {v} := by
    intro y hy hc
    have hmem : y ∈ (⋃ e ∈ E, affGt ({x} : Set V3) e) ∩
        (⋃ v ∈ V, affGe ({x} : Set V3) {v}) := Set.mem_inter hy hc
    rw [hdis] at hmem
    exact hmem
  unfold yfan
  rw [XFAN_EQ_UNIONS_AFF_GE_1_2, hxp]
  ext y
  constructor
  · intro hy
    rcases (Set.mem_union y _ _).1 hy with hy | hy
    · rcases (Set.mem_sdiff y).1 hy with ⟨_, hne⟩
      exact Set.mem_sdiff_of_mem (Set.mem_univ y) (fun hc => hne (Or.inr hc))
    · exact Set.mem_sdiff_of_mem (Set.mem_univ y) (hBC y hy)
  · intro hy
    by_cases hB : y ∈ (⋃ e ∈ E, affGt ({x} : Set V3) e)
    · exact Or.inr hB
    · refine Or.inl ?_
      refine Set.mem_sdiff_of_mem (Set.mem_univ y) (fun hc => ?_)
      rcases (Set.mem_union y _ _).1 hc with hc | hc
      · exact hB hc
      · exact ((Set.mem_sdiff y).1 hy).2 hc

end Kepler.Text
