/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 1
(Conforming.hl:64-483).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 1, Conforming.hl:64-483):
- `GINGUAP` (64)
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan` (88)
- `IMAGE_F1_IN_FACE_IMP_IN_FACE` (155)
- `IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE` (211)
- `REP_OF_INVERSE1_SIGMA_FAN` (247)
- `DARTSET_LEADS_INTO_SUBSET_WDART_FAN` (268)
- `power_map_points_edge_fan` (354)
- `SRPRNPL` (371; HOL spells the binder `let     SRPRNPL`, the extra
  blanks defeat the pipeline's `let `-name extraction, which is why the
  batch listing showed an empty name at :371)
- `NSUM_EQ_0_IFF` (458)
- `N_FAN_EQ_0_IMP_CARD_FACE_EQ_3` (465)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityAuto15.lean:26).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`, `d_fan` ↦ `dartOfFan` (Fan.lean:90), `f1_fan` ↦
  `f1Fan` (ConformingDefs.lean:87). A face element `y = (v,w)` extends to
  the quadruple `(x, v, w, sigmaFan x V E v w)` (the first and fourth
  components are unused by `wDartFan`, cf. Fan.lean:162).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts
  (Kepler/Text/Fan.lean:1169); `hfan : FAN x V E` is passed explicitly.
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `w_dart_fan` ↔
  `wDartFan` (Kepler/Text/Fan.lean:162); HOL `convex` ↔ Mathlib `Convex ℝ`;
  HOL `simple_hypermap` ↔ `Hypermap.Simple` (Kepler/Text/Hypermap.lean:1058).
- HOL `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (ConformingDefs.lean:184), which already carries the
  `CARD (set_of_edge …) > 1` and `fan80` conjuncts.
- HOL `power_map_points sigma_fan x V E v w n` ↔ `(sigmaFan x V E v)^[n] w`
  (HOL recursive definition fan.hl:988; repo encoding
  Kepler/Text/TopologyFan.lean:132/1021).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL
  `inverse1_sigma_fan` ↔ `inverse1SigmaFan` (Kepler/Text/Fan.lean:240).
- HOL `nsum S g` ↔ finsum `∑ᶠ f ∈ S, g f` (ConformingDefs.lean:50);
  `CARD ds` ↔ `ds.ncard`.
- `NSUM_EQ_0_IFF` is a HOL-general `nsum` fact; Mathlib has only the
  one-directional `finsum_eq_zero_of_forall_eq_zero` and the Finset
  version `Finset.sum_eq_zero_iff`, NOT the exact set-finsum `↔`, so the
  statement is kept (not skipped).
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology
open scoped BigOperators

/-! ## conforming fan 的凸性与半空间（Conforming.hl:64-153） -/

/-- HOL `CONVEX_AFF_GT`：`affGt s t` 对任意 `s t` 都是凸集。
`Affsign` 的系数在凸组合下保持 `t` 上的严格正性与系数和为 1。 -/
private theorem convex_affGt (s t : Set V3) : Convex ℝ (affGt s t) := by
  rw [convex_iff_forall_pos]
  intro y hy z hz a b ha hb hab
  obtain ⟨f, hfin, hyeq, hfpos, hfsum⟩ := hy
  obtain ⟨g, hfin', hzeq, hgpos, hgsum⟩ := hz
  have hfs : hfin'.toFinset = hfin.toFinset := by
    rw [Subsingleton.elim hfin' hfin]
  rw [hfs] at hzeq hgsum
  refine ⟨fun w => a * f w + b * g w, hfin, ?_, ?_, ?_⟩
  · rw [hyeq, hzeq, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [smul_smul, smul_smul, ← add_smul]
  · intro w hw
    exact add_pos (mul_pos ha (hfpos w hw)) (mul_pos hb (hgpos w hw))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hfsum, hgsum, mul_one, mul_one, hab]

/-- HOL Conforming.hl :64-87 `GINGUAP`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
/\ conforming_fan (x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>   convex(dartset_leads_into_fan x V E ds)
```

证明思路：展开 `conformingFan` 取出 `conformingHalfSpaceFan`，把
`dartsetLeadsIntoFan x V E ds` 重写为半空间族的交
`⋂ y ∈ ds, affGt {x, y.1, y.2} {(f1Fan x V E y).2}`；HOL
`CONVEX_INTERS` ↔ Mathlib `convex_iInter`，每个 `affGt` 是凸集（由
`conformingDiagonalFan` 给出三点不共线）。

候选已有引理：
- `conformingFan`（Kepler/Text/ConformingDefs.lean:184）
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `convex_iInter`（Mathlib/Analysis/Convex/Basic.lean:96）
- 缺口：HOL `CONVEX_AFF_GT` 在仓库无公开具名引理；最近的是 private
  `convex_affGt_single_pair`（Kepler/Text/PlanarityComponent.lean:89）与
  `convex_affGt_triple`（Kepler/Text/PlanarityAuto12.lean:220） -/
theorem GINGUAP {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    Convex ℝ (dartsetLeadsIntoFan x V E ds) := by
  obtain ⟨-, -, -, hhalf, -, -⟩ := hconf
  rw [hhalf ds hds]
  exact convex_iInter₂ fun y _ => convex_affGt _ _

/-- 混合积轮换：`(a × b) · c = (b × c) · a`。 -/
private theorem cross_dot_cyclic_conf {a b c : Fin 3 → ℝ} :
    (crossProduct a b) ⬝ᵥ c = (crossProduct b c) ⬝ᵥ a := by
  calc (crossProduct a b) ⬝ᵥ c = c ⬝ᵥ crossProduct a b := dotProduct_comm _ _
    _ = a ⬝ᵥ crossProduct b c := triple_product_permutation c a b
    _ = (crossProduct b c) ⬝ᵥ a := dotProduct_comm _ _

/-- HOL Conforming.hl :88-154 `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v w.
FAN(x,V,E) /\ {v,w} IN E
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>  aff_gt {x, v,w} {sigma_fan x V E v w} =
 aff_gt {x, v, w} {inverse1_sigma_fan x V E w v}
```

证明思路：由 `INVERSE1_SIGMA_FAN` 得 `sigmaFan x V E v (inverse1SigmaFan
x V E v w) = w` 且 `inverse1SigmaFan x V E w v` 与 `w` 相邻；用
`properties_fully_surrounded`/`cross_dot_fully_surrounded_fan` 比较两侧
`affGt` 的 cross-dot 表示，`aff_gt_3_1_rep_cross_dot` 把
`affGt {x,v,w} {p}` 化为 `(v-x) × (w-x) · (p-x)` 的符号条件，两侧等价。

候选已有引理：
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `sigma_fan_in_setOfEdge`（Kepler/Text/Fan.lean:326） -/

theorem fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {v w : V3}
    (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x, v, w} : Set V3) {sigmaFan x V E v w} =
      affGt ({x, v, w} : Set V3) {inverse1SigmaFan x V E w v} := by
  have hwv : {w, v} ∈ E := by
    rw [show ({w, v} : Set V3) = {v, w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hvw
  have hwS : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hvw
  have hsS : sigmaFan x V E v w ∈ setOfEdge v V E :=
    sigma_fan_in_setOfEdge hfan hwS
  have hvs : {v, sigmaFan x V E v w} ∈ E :=
    (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v w) hfan).mpr hsS
  have hsv : {sigmaFan x V E v w, v} ∈ E := by
    rw [show ({sigmaFan x V E v w, v} : Set V3) = {v, sigmaFan x V E v w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hvs
  have hwt : {w, inverse1SigmaFan x V E w v} ∈ E :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).1 v hwv
  have hsig_t : sigmaFan x V E w (inverse1SigmaFan x V E w v) = v :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 v hwv
  have h80_vw := hfan80 v w hvw
  have h80_wt := hfan80 w (inverse1SigmaFan x V E w v) hwt
  rw [hsig_t] at h80_wt
  have hcop_inv : ¬ Coplanar ({x, v, w, inverse1SigmaFan x V E w v} : Set V3) :=
    properties_fully_surrounded hfan hvw hwt h80_wt.1 h80_wt.2
  have hcop_sig' : ¬ Coplanar ({x, sigmaFan x V E v w, v, w} : Set V3) :=
    properties_fully_surrounded (v := sigmaFan x V E v w) (u := v) (w := w)
      hfan hsv hvw h80_vw.1 h80_vw.2
  have hcop_sig : ¬ Coplanar ({x, v, w, sigmaFan x V E v w} : Set V3) := by
    rw [show ({x, v, w, sigmaFan x V E v w} : Set V3) =
        {x, sigmaFan x V E v w, v, w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop_sig'
  have hncv_s : ¬ Collinear3 x v (sigmaFan x V E v w) := fan_not_collinear hfan hvs
  have hncvw : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hncwv : ¬ Collinear3 x w v := fan_not_collinear hfan hwv
  have hncwt : ¬ Collinear3 x w (inverse1SigmaFan x V E w v) :=
    fan_not_collinear hfan hwt
  have hpos_sig : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((sigmaFan x V E v w - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v) (v := w)
      (u1 := sigmaFan x V E v w) hncv_s hncvw h80_vw.1 h80_vw.2
  have hpos_inv_raw : 0 < crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((v - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := w)
      (v := inverse1SigmaFan x V E w v) (u1 := v) hncwv hncwt h80_wt.1 h80_wt.2
  have hpos_inv : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ) := by
    rw [cross_dot_cyclic_conf (a := ((v - x : V3) : Fin 3 → ℝ))
      (b := ((w - x : V3) : Fin 3 → ℝ))
      (c := ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ))]
    exact hpos_inv_raw
  calc affGt ({x, v, w} : Set V3) {sigmaFan x V E v w}
      = {y : V3 | 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} :=
        aff_gt_3_1_rep_cross_dot x v w (sigmaFan x V E v w) hcop_sig hpos_sig
    _ = affGt ({x, v, w} : Set V3) {inverse1SigmaFan x V E w v} :=
        (aff_gt_3_1_rep_cross_dot x v w (inverse1SigmaFan x V E w v) hcop_inv
          hpos_inv).symm

/-! ## `f1_fan` 的像仍在面内（Conforming.hl:155-246） -/

/-- HOL Conforming.hl :155-210 `IMAGE_F1_IN_FACE_IMP_IN_FACE`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y y1.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN ds
/\ y1 IN d_fan(x,V,E)
/\ f1_fan x V E y1= y
==>   y1 IN ds
```

证明思路：由 `dartOfFan_eq_dart1_of_surrounded` 把 `y1 ∈ d_fan` 化为
`y1 ∈ d1_fan`，再展开 `(hypermapOfFan …).faceSet` 为 `f1Fan`-轨道；
`condition_f1_fan_in_face_set` 给出 `f1Fan` 封闭性，结合面的循环性
（`face_representation`）从 `f1Fan y1 = y ∈ ds` 反推 `y1 ∈ ds`。

候选已有引理：
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `FINITE_FACE_FAN`（Kepler/Text/PlanarityAuto14.lean:693）
- 缺口：HOL `hypermap_of_fan_rep`（fan.hl:2780）、
  `into_domain_power_efn_fan`（fan.hl:2694）未以该名移植 -/
private theorem hypermapOfFan_faceMap_eq_ca1 (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

theorem IMAGE_F1_IN_FACE_IMP_IN_FACE {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {y y1 : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds)
    (hy1 : y1 ∈ dartOfFan V E)
    (hf1 : f1Fan x V E y1 = y) :
    y1 ∈ ds := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdart : dartOfFan V E = dart1OfFan V E :=
    dartOfFan_eq_dart1_of_surrounded hfan hcard
  have hy1d : y1 ∈ dart1OfFan V E := by rw [← hdart]; exact hy1
  have hf1pair : f1Fan x V E y1 = fFanPair x V E y1 := by
    have hba : {y1.2, y1.1} ∈ E := by
      have h : {y1.1, y1.2} ∈ E := hy1d
      rwa [Set.pair_comm] at h
    simp only [f1Fan, fFanPair]
    rw [inverse_sigma_fan_eq_inverse1 hfan hba]
  have hfm : H.faceMap y1 = y := by
    change (hypermapOfFan x V E hfan).faceMap y1 = y
    rw [hypermapOfFan_faceMap_eq_ca1 hfan hy1d, ← hf1pair]
    exact hf1
  obtain ⟨d, _hdH, hface⟩ := Hypermap.face_representation H hds
  have hyface : y ∈ H.face d := by rw [← hface]; exact hy
  have hsymm : H.faceMap.symm y = y1 := by
    rw [← hfm, Equiv.symm_apply_apply]
  have hy1face : y1 ∈ H.face d := by
    have h := Hypermap.faceMap_symm_mem_face H hyface
    rwa [hsymm] at h
  rw [hface]
  exact hy1face

/-- HOL Conforming.hl :211-246 `IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE`

HOL 原文：
```
!m x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y y1.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN ds
/\ y1 IN d_fan(x,V,E)
/\ (f1_fan x V E POWER m) y1= y
==>   y1 IN ds
```

证明思路：对 `m` 归纳。`m=0` 时假设即 `y1 = y ∈ ds`；`m+1` 时由
`y' = f1Fan x V E y1` 落在 `d_fan`（`fFanPair_mem_dart1` /
`dartOfFan_eq_dart1_of_surrounded`），先用归纳假设把 `y1` 的像拉回
`ds`，再用 `IMAGE_F1_IN_FACE_IMP_IN_FACE`。

候选已有引理：
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（本文件上文，HOL :155）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Function.iterate_succ_apply'`（Mathlib/Logic/Function/Iterate.lean） -/
private theorem f1Fan_iterate_mem_face_aux {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∀ (m : ℕ) (y1 y : V3 × V3), y1 ∈ dartOfFan V E →
      y ∈ ds → (f1Fan x V E)^[m] y1 = y → y1 ∈ ds := by
  intro m
  induction m with
  | zero =>
      intro y1 y hy1 hy hpow
      simp only [Function.iterate_zero, id_eq] at hpow
      rw [hpow]
      exact hy
  | succ m ih =>
      intro y1 y hy1 hy hpow
      rw [Function.iterate_succ_apply] at hpow
      have hy1d : y1 ∈ dart1OfFan V E := by
        rw [← dartOfFan_eq_dart1_of_surrounded hfan hcard]
        exact hy1
      have hf1pair : f1Fan x V E y1 = fFanPair x V E y1 := by
        have hba : {y1.2, y1.1} ∈ E := by
          have h : {y1.1, y1.2} ∈ E := hy1d
          rwa [Set.pair_comm] at h
        simp only [f1Fan, fFanPair]
        rw [inverse_sigma_fan_eq_inverse1 hfan hba]
      have hclos1 : f1Fan x V E y1 ∈ dart1OfFan V E := by
        rw [hf1pair]
        exact fFanPair_mem_dart1 hfan hy1d
      have hclos : f1Fan x V E y1 ∈ dartOfFan V E := by
        rw [dartOfFan_eq_dart1_of_surrounded hfan hcard]
        exact hclos1
      exact IMAGE_F1_IN_FACE_IMP_IN_FACE hfan hcard hds
        (ih (f1Fan x V E y1) y hclos hy hpow) hy1 rfl

theorem IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE (m : ℕ) {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y y1 : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds)
    (hy1 : y1 ∈ dartOfFan V E)
    (hpow : (f1Fan x V E)^[m] y1 = y) :
    y1 ∈ ds := by
  exact f1Fan_iterate_mem_face_aux hfan hcard hds m y1 y hy1 hy hpow

/-! ## 面的 `f1_fan` 代表元（Conforming.hl:247-353） -/

/-- HOL Conforming.hl :247-267 `REP_OF_INVERSE1_SIGMA_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN ds
==>  f1_fan x V E  (x,sigma_fan x V E (pr2 y) (pr3 y),(pr2 y),sigma_fan x V E (sigma_fan x V E (pr2 y) (pr3 y)) (pr2 y))=y
```

编码说明：HOL 的 4 元组实参 `(x, sigma_fan x V E v w, v, …)`（其中
`v = pr2 y`、`w = pr3 y`）在二元组编码下为
`(sigmaFan x V E y.1 y.2, y.1)`；`f1Fan (a,b) = (b, inverse1SigmaFan
x V E b a)`。

证明思路：由 `hy` 与 `dartOfFan_eq_dart1_of_surrounded` 得
`{y.1,y.2} ∈ E`；`f1Fan` 展开后用 `INVERSE1_SIGMA_FAN` 的第三条件
`inverse1SigmaFan x V E y.1 (sigmaFan x V E y.1 y.2) = y.2`，即得
`(y.1,y.2) = y`。

候选已有引理：
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `dartset_fully_surrounded_is_non_isolated_fan` 的二元组对应
  （Kepler/Text/Fan.lean:1084） -/
theorem REP_OF_INVERSE1_SIGMA_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) :
    f1Fan x V E (sigmaFan x V E y.1 y.2, y.1) = y := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hy_dart : y ∈ dart1OfFan V E := by
    simp only [Hypermap.faceSet, setOfOrbits] at hds
    obtain ⟨d, hd, rfl⟩ := hds
    have hsub : orbitMap H.faceMap d ⊆ (↑H.darts : Set (V3 × V3)) :=
      H.face_subset_darts hd
    exact hdarts ▸ hsub hy
  have hyE : {y.1, y.2} ∈ E := by
    simpa [dart1OfFan] using hy_dart
  have hinv : inverse1SigmaFan x V E y.1 (sigmaFan x V E y.1 y.2) = y.2 :=
    (INVERSE1_SIGMA_FAN hfan).2.2 y.2 hyE
  simp only [f1Fan]
  rw [hinv]

/-- HOL Conforming.hl :268-353 `DARTSET_LEADS_INTO_SUBSET_WDART_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y.
FAN(x,V,E)
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN ds
/\ conforming_fan (x,V,E)
==>   (dartset_leads_into_fan x V E ds) SUBSET (w_dart_fan x V E y)
```

编码说明：面元素 `y = (v,w)` 对应 4 元组
`(x, y.1, y.2, sigmaFan x V E y.1 y.2)`（`wDartFan` 仅用第 2、3 分量）。

证明思路：展开 `conformingFan` 得 `conformingHalfSpaceFan`，把
`dartsetLeadsIntoFan ds` 写成半空间交，用
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan` 与
`WEDGE_LUNE_GT`（仓库对应 `wedge` 与 `inter_aff_gt_3_1_is_aff_gt_2_2`）
说明该交含于 `wDartFan`；`properties_of_f1_fan` 给出代表 dart 在面内。

候选已有引理：
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（本文件上文，HOL :88）
- `REP_OF_INVERSE1_SIGMA_FAN`（本文件上文，HOL :247）
- `IMAGE_F1_IN_FACE_IMP_IN_FACE`（本文件上文，HOL :155）
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `wDartFan`（Kepler/Text/Fan.lean:162）
- 缺口：HOL `WEDGE_LUNE_GT`（fan.hl）、`inter_aff_gt_3_1_is_aff_gt_2_2`
  （fan.hl）、`properties_of_f1_fan`（fan.hl:2797）未以该名移植 -/

/-
`WEDGE_LUNE_GT` 的 2-2 方向（本文件私有）：四点不共面且
`0 < azim x v w s < π` 时，`affGt {x,v} {w,s} ⊆ wedge x v w s`。

证明：`affGt2_2` 给出 `p = t1•x + t2•v + t3•w + t4•s`（`t3,t4>0`）。
令 `c = t3+t4`、`a = t4/c`、`q = (1-a)•w + a•s`，则 `p = t1•x + t2•v + c•q`
且 `q` 是弦 `w→s` 的内点。先用 `properties_of_fully_surrounded1_fan`
两次把方位角反射到 `azim x w s v ∈ (0,π)`，再以
`inequality4_aim_in_convex_fan` 得 `0 < azim x v w q < azim x v w s`。
最后 `azim_of_affGt_combo` 说明 `p` 与 `q` 同方位角，`p` 非共线由
`aff_gt_imp_not_collinear`。 -/
private theorem affGt_subset_wedge_ca1 {x v w s : V3}
    (hcop : ¬ Coplanar ({x, v, w, s} : Set V3))
    (hθ0 : 0 < azim x v w s) (hθπ : azim x v w s < Real.pi)
    (hdis : Disjoint ({x, v} : Set V3) {w, s}) :
    affGt ({x, v} : Set V3) {w, s} ⊆ wedge x v w s := by
  intro p hp
  rw [affGt2_2 hdis] at hp
  obtain ⟨t1, t2, t3, t4, ht3, ht4, hsum, hp_eq⟩ := hp
  set c : ℝ := t3 + t4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set a : ℝ := t4 / c with ha
  have ha0 : 0 < a := by rw [ha]; exact div_pos ht4 hcpos
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hcpos]
    linarith [ht3]
  set q : V3 := (1 - a) • w + a • s with hq
  have hcq : c • q = t3 • w + t4 • s := by
    rw [hq, ha, hc, smul_add, smul_smul, smul_smul]
    have hcne : t3 + t4 ≠ 0 := ne_of_gt (by linarith)
    rw [show (t3 + t4) * (1 - t4 / (t3 + t4)) = t3 by
          field_simp [hcne] <;> ring,
        show (t3 + t4) * (t4 / (t3 + t4)) = t4 by
          field_simp [hcne] <;> ring]
  have hp_q : p = t1 • x + t2 • v + c • q := by
    rw [hp_eq, hcq]
    module
  -- 反射方位角
  have hcop_sw : ¬ Coplanar ({x, s, v, w} : Set V3) := by
    rwa [show ({x, s, v, w} : Set V3) = {x, v, w, s} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hsvw : 0 < azim x s v w ∧ azim x s v w < Real.pi :=
    properties_of_fully_surrounded1_fan hcop_sw hθ0 hθπ
  have hcop_ws : ¬ Coplanar ({x, w, s, v} : Set V3) := by
    rwa [show ({x, w, s, v} : Set V3) = {x, v, w, s} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hwsv : 0 < azim x w s v ∧ azim x w s v < Real.pi :=
    properties_of_fully_surrounded1_fan hcop_ws hsvw.1 hsvw.2
  have hq_bounds : 0 < azim x v w q ∧ azim x v w q < azim x v w s := by
    have h := inequality4_aim_in_convex_fan (x := x) (v := v) (u := w) (w := s)
      (a := a) hcop hwsv.1 hwsv.2 ha0 ha1
    rw [hq]
    exact h
  -- p 与 q 同方位角
  obtain ⟨-, hnc_vw, -⟩ := notcoplanar_imp_notcollinear_fan hcop
  have hnc_q : ¬ Collinear3 x v q := by
    intro hc
    have h0 : azim x v w q = 0 := by
      unfold azim
      rw [if_pos (Or.inr hc)]
    linarith [hq_bounds.1, h0]
  have hsum' : t1 + t2 + c = 1 := by rw [hc]; linarith
  have haz : azim x v w p = azim x v w q :=
    (azim_of_affGt_combo hnc_vw hnc_q t1 t2 c hcpos hsum' hp_q).symm
  have hxv : x ≠ v := fun h => hnc_vw
    (collinear3_of_eq (v := x) (w := v) (w1 := w) h.symm)
  have hxq : x ≠ q := fun h => hnc_q
    (collinear3_pair_left (v0 := x) (v1 := v) (x := q) h.symm)
  have hvq : v ≠ q := fun h => hnc_q
    (collinear3_pair_right (v0 := x) (v1 := v) (x := q) h.symm)
  have hpq : p ∈ affGt ({x, v} : Set V3) {q} :=
    affGt_of_triple t1 t2 c hcpos hsum' hp_q hxv hxq hvq
  have hnc_p : ¬ Collinear3 x v p := aff_gt_imp_not_collinear hnc_q hpq
  exact ⟨hnc_p, by rw [haz]; exact hq_bounds.1, by rw [haz]; exact hq_bounds.2⟩

theorem DARTSET_LEADS_INTO_SUBSET_WDART_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds)
    (hconf : conformingFan x V E hfan) :
    dartsetLeadsIntoFan x V E ds ⊆
      wDartFan x V E (x, y.1, y.2, sigmaFan x V E y.1 y.2) := by
  obtain ⟨hcard, hfan80, -, hhalf, -, -⟩ := hconf
  set sigma : V3 := sigmaFan x V E y.1 y.2 with hsigma
  -- y ∈ d1_fan，从而 {y.1,y.2} ∈ E
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  obtain ⟨d, hdH, hface⟩ := Hypermap.face_representation H hds
  have hy_dart1 : y ∈ dart1OfFan V E := by
    have hyface : y ∈ H.face d := by simpa [hface] using hy
    have hymem : y ∈ H.darts := H.face_subset_darts hdH hyface
    change y ∈ (↑H.darts : Set (V3 × V3)) at hymem
    simpa [hdarts] using hymem
  have hvw : {y.1, y.2} ∈ E := hy_dart1
  have hnc_vw : ¬ Collinear3 x y.1 y.2 := fan_not_collinear hfan hvw
  have hy1V : y.1 ∈ V := (fan_mem_of_edge hfan hvw).1
  have hcardv : 1 < (setOfEdge y.1 V E).ncard := hcard y.1 hy1V
  obtain ⟨hθ0, hθπ⟩ := hfan80 y.1 y.2 hvw
  have hσ_soe : sigma ∈ setOfEdge y.1 V E := by
    rw [hsigma]
    exact sigma_fan_in_setOfEdge hfan
      ((properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hvw)
  have h_vσ : {y.1, sigma} ∈ E :=
    (properties_of_setOfEdge_fan x V E y.1 sigma hfan).mpr hσ_soe
  have h_σv : {sigma, y.1} ∈ E := by
    rw [Set.pair_comm]; exact h_vσ
  have hnc_vσ : ¬ Collinear3 x y.1 sigma := fan_not_collinear hfan h_vσ
  -- (sigma, y.1) 也在 ds 中（f1Fan 的前像）
  have hy1_dart : (sigma, y.1) ∈ dartOfFan V E := by
    rw [dartOfFan_eq_dart1_of_surrounded hfan hcard]
    change {(sigma, y.1).1, (sigma, y.1).2} ∈ E
    simpa using h_σv
  have hf1_y1 : f1Fan x V E (sigma, y.1) = y := by
    have h2 : inverse1SigmaFan x V E y.1 sigma = y.2 := by
      rw [hsigma]
      exact (INVERSE1_SIGMA_FAN (v := y.1) hfan).2.2 y.2 hvw
    simp only [f1Fan]
    rw [h2]
  have hy1_ds : (sigma, y.1) ∈ ds :=
    IMAGE_F1_IN_FACE_IMP_IN_FACE hfan hcard hds hy hy1_dart hf1_y1
  -- 用 conformingHalfSpaceFan 展开为半空间交
  rw [hhalf ds hds]
  intro p hp
  have hp_y : p ∈ affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} :=
    (Set.mem_iInter.mp (Set.mem_iInter.mp hp y)) hy
  have hp_y1 : p ∈ affGt ({x, (sigma, y.1).1, (sigma, y.1).2} : Set V3)
      {(f1Fan x V E (sigma, y.1)).2} :=
    (Set.mem_iInter.mp (Set.mem_iInter.mp hp (sigma, y.1))) hy1_ds
  -- 两个 3-1 半空间
  have hp_y_inv : p ∈ affGt ({x, y.1, y.2} : Set V3)
      {inverse1SigmaFan x V E y.2 y.1} := by
    simpa only [f1Fan] using hp_y
  have hp_y_σ : p ∈ affGt ({x, y.1, y.2} : Set V3) {sigma} := by
    have h := fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan hfan hvw hcard hfan80
    rw [← h] at hp_y_inv
    rw [← hsigma] at hp_y_inv
    exact hp_y_inv
  have hp_y1_w : p ∈ affGt ({x, sigma, y.1} : Set V3) {y.2} := by
    have h2 : (f1Fan x V E (sigma, y.1)).2 = y.2 := by
      simp only [f1Fan, hsigma]
      exact (INVERSE1_SIGMA_FAN (v := y.1) hfan).2.2 y.2 hvw
    simpa only [h2] using hp_y1
  -- 非共面性（四种点序）
  have hcop_σvw : ¬ Coplanar ({x, sigma, y.1, y.2} : Set V3) :=
    properties_fully_surrounded hfan h_σv hvw
      (by rw [hsigma]; exact hθ0) (by rw [hsigma]; exact hθπ)
  have hcop_wvσ : ¬ Coplanar ({x, y.2, y.1, sigma} : Set V3) := by
    rwa [show ({x, y.2, y.1, sigma} : Set V3) = {x, sigma, y.1, y.2} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hcop_vwσ : ¬ Coplanar ({x, y.1, y.2, sigma} : Set V3) := by
    rwa [show ({x, y.1, y.2, sigma} : Set V3) = {x, sigma, y.1, y.2} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  -- 交到 2-2
  have hp2 : p ∈ affGt ({x, y.1} : Set V3) {y.2, sigma} := by
    have hsetA : ({x, y.2, y.1} : Set V3) = {x, y.1, y.2} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have hsetB : ({x, y.1, sigma} : Set V3) = {x, sigma, y.1} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have hmem : p ∈ affGt ({x, y.2, y.1} : Set V3) {sigma} ∩
        affGt ({x, y.1, sigma} : Set V3) {y.2} := by
      refine ⟨?_, ?_⟩
      · rwa [hsetA]
      · rwa [hsetB]
    have heq := inter_aff_gt_3_1_is_aff_gt_2_2 x y.2 y.1 sigma hcop_wvσ
    rw [heq] at hmem
    exact hmem
  -- 互异性
  have hxv : x ≠ y.1 := fun h => hnc_vw
    (collinear3_of_eq (v := x) (w := y.1) (w1 := y.2) h.symm)
  have hxw : x ≠ y.2 := fun h => hnc_vw
    (collinear3_pair_left (v0 := x) (v1 := y.1) (x := y.2) h.symm)
  have hxs : x ≠ sigma := fun h => hnc_vσ
    (collinear3_pair_left (v0 := x) (v1 := y.1) (x := sigma) h.symm)
  have hvw' : y.1 ≠ y.2 := edge_ne_of_fan hfan hvw
  have hvs : y.1 ≠ sigma := fun h => hnc_vσ
    (collinear3_pair_right (v0 := x) (v1 := y.1) (x := sigma) h.symm)
  have hdis : Disjoint ({x, y.1} : Set V3) {y.2, sigma} := by
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact hxw (ha.symm.trans hb)
      · exact hxs (ha.symm.trans hb)
    · rcases hb with hb | hb
      · exact hvw' (ha.symm.trans hb)
      · exact hvs (ha.symm.trans hb)
  have hpwedge : p ∈ wedge x y.1 y.2 sigma :=
    affGt_subset_wedge_ca1 hcop_vwσ
      (by rw [hsigma]; exact hθ0) (by rw [hsigma]; exact hθπ) hdis hp2
  rw [wDartFan, if_pos hcardv]
  exact hpwedge

/-! ## 迭代点与简单超映射（Conforming.hl:354-457） -/

/-- HOL Conforming.hl :354-370 `power_map_points_edge_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 n:num.
FAN(x,V,E)
/\ {v,w} IN E
==> {v,power_map_points sigma_fan x V E v w n} IN E
```

编码说明：HOL `power_map_points sigma_fan x V E v w n` ↔
`(sigmaFan x V E v)^[n] w`（fan.hl:988 的递归定义；仓库编码见
Kepler/Text/TopologyFan.lean:132/1021）。

证明思路：`image_power_map_points`（HOL `image_power_map_points`）给出
迭代点属于 `setOfEdge v V E`，再用
`properties_of_setOfEdge_fan` 把成员性翻译成边 `{v, ·} ∈ E`。

候选已有引理：
- `image_power_map_points`（Kepler/Text/TopologyFan.lean:132）
- `properties_of_setOfEdge_fan`（Kepler/Text/Fan.lean:334）
- `orbits_subset_setOfEdge`（Kepler/Text/TopologyFan.lean:171） -/
theorem power_map_points_edge_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {v w : V3} (n : ℕ)
    (hfan : FAN x V E) (hvw : {v, w} ∈ E) :
    {v, (sigmaFan x V E v)^[n] w} ∈ E := by
  exact (properties_of_setOfEdge_fan x V E v ((sigmaFan x V E v)^[n] w) hfan).mpr
    (image_power_map_points hfan hvw n)

/-- `hypermapOfFan` 的 `nodeMap` 在 `dart1OfFan` 上就是 `nFanPair`。 -/
private theorem hypermapOfFan_nodeMap_eq_ca1 (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).nodeMap d = nFanPair x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- `nodeMap` 的迭代在 `dart1OfFan` 上保持首分量并沿 `sigmaFan` 递推。 -/
private theorem hypermapOfFan_nodeMap_iterate_ca1 (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (n : ℕ) :
    ((hypermapOfFan x V E hfan).nodeMap^[n]) d =
      (d.1, (sigmaFan x V E d.1)^[n] d.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hdE : {d.1, d.2} ∈ E := hd
    have hmem : (d.1, (sigmaFan x V E d.1)^[n] d.2) ∈ dart1OfFan V E := by
      simp only [dart1OfFan, Set.mem_setOf_eq]
      exact power_map_points_edge_fan n hfan hdE
    rw [hypermapOfFan_nodeMap_eq_ca1 hfan hmem]
    simp only [nFanPair, Function.iterate_succ_apply']

/-- HOL Conforming.hl :371-457 `SRPRNPL`

HOL 原文（HOL 中 `let     SRPRNPL=prove(...)`，多空格使批次名提取为空）：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
/\ conforming_fan (x,V,E)
==>   simple_hypermap(hypermap1_of_fanx (x,V,E))
```

证明思路：展开 `conformingFan` 得 `fan80` 与半空间性；对
`x' ∈ dart`，证 `(hypermapOfFan …).node x' ∩ (hypermapOfFan …).face x'
= {x'}`。用 `DARTSET_LEADS_INTO_SUBSET_WDART_FAN` 说明相邻 dart 的
`wDartFan` 与 `dartsetLeadsInto` 分量互不相交（`disjoint_fan2`），
结合 `dartset_leads_into_is_topological_component_yfan` 与
`exists_point_in_component_yfan` 收口。

候选已有引理：
- `Simple`（Kepler/Text/Hypermap.lean:1058）
- `DARTSET_LEADS_INTO_SUBSET_WDART_FAN`（本文件上文，HOL :268）
- `power_map_points_edge_fan`（本文件上文，HOL :354）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `exists_point_in_component_yfan`（Kepler/Text/PlanarityConnect.lean:76）
- `disjoint_fan2`（Kepler/Text/TopologyFan.lean:1912）
- 缺口：HOL `power_n_fan`（fan.hl:1005）、`i_IN_ORBITS_FAN` 的
  `power_map_points` 版本（仓库 `iterates_mem_orbits`，
  Kepler/Text/TopologyFan.lean:152） -/
theorem SRPRNPL {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan) :
    (hypermapOfFan x V E hfan).Simple := by
  have hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard := hconf.1
  have hfan80 : fan80 x V E := hconf.2.1
  intro x' hx'darts
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hx'dart1 : x' ∈ dart1OfFan V E := by
    have : x' ∈ (↑H.darts : Set (V3 × V3)) := hx'darts
    rwa [hdarts] at this
  have hx'E : {x'.1, x'.2} ∈ E := hx'dart1
  apply Set.Subset.antisymm
  · intro z hz
    rw [Set.mem_singleton_iff]
    obtain ⟨hz_node, hz_face⟩ := hz
    have hz_darts : z ∈ H.darts := H.node_subset_darts hx'darts hz_node
    have hz_dart1 : z ∈ dart1OfFan V E := by
      have : z ∈ (↑H.darts : Set (V3 × V3)) := hz_darts
      rwa [hdarts] at this
    have hz_E : {z.1, z.2} ∈ E := hz_dart1
    have hz_fst : z.1 = x'.1 := by
      obtain ⟨n, hn⟩ := hz_node
      rw [← hn]
      rw [Equiv.Perm.coe_pow, hypermapOfFan_nodeMap_iterate_ca1 hfan hx'dart1 n]
    have hds_mem : H.face x' ∈ H.faceSet := ⟨x', hx'darts, rfl⟩
    have hx'_ds : x' ∈ H.face x' := H.mem_face_self x'
    have hcomp :=
      dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds_mem
    obtain ⟨p, hp⟩ := exists_point_in_component_yfan hcomp
    have hp_z : p ∈ wDartFan x V E (x, z.1, z.2, sigmaFan x V E z.1 z.2) :=
      DARTSET_LEADS_INTO_SUBSET_WDART_FAN hfan hds_mem hz_face hconf hp
    have hp_x' : p ∈ wDartFan x V E (x, x'.1, x'.2, sigmaFan x V E x'.1 x'.2) :=
      DARTSET_LEADS_INTO_SUBSET_WDART_FAN hfan hds_mem hx'_ds hconf hp
    by_contra hne
    have hz2ne : x'.2 ≠ z.2 := fun h => hne (Prod.ext hz_fst h.symm)
    have hzE' : {x'.1, z.2} ∈ E := by
      rw [← hz_fst]
      exact hz_E
    have hdisj :=
      disjoint_fan2 (v := x'.1) (w := x'.2) (w1 := z.2) hfan hx'E hzE' hz2ne
    have hmem : p ∈ wDartFan x V E (x, x'.1, x'.2, sigmaFan x V E x'.1 x'.2) ∩
        wDartFan x V E (x, x'.1, z.2, sigmaFan x V E x'.1 z.2) := by
      refine ⟨hp_x', ?_⟩
      rwa [hz_fst] at hp_z
    rw [hdisj] at hmem
    exact hmem
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨H.mem_node_self x', H.mem_face_self x'⟩

/-! ## `nsum` 与 `N_FAN` 的计数引理（Conforming.hl:458-483） -/

/-- HOL Conforming.hl :458-464 `NSUM_EQ_0_IFF`

HOL 原文：
```
!s f. FINITE s ==> (nsum s f = 0 <=> !x. x IN s ==> f x = 0)
```

编码说明：HOL `nsum s f` ↔ finsum `∑ᶠ x ∈ s, f x`（ConformingDefs.lean:50）。
该命题是 HOL 一般的 `nsum` 事实；Mathlib 只有单向
`finsum_eq_zero_of_forall_eq_zero` 与 Finset 版 `Finset.sum_eq_zero_iff`，
没有集合 finsum 的精确 `↔`，故保留此陈述。

证明思路：`s.Finite` 时把 `∑ᶠ x ∈ s, f x` 转为 Finset 和（`s.toFinite`
上的 `Finset.sum`），再用 `Finset.sum_eq_zero_iff`（`ℕ` 的 `AddUnits`
是 Subsingleton）；反向用 `finsum_eq_zero_of_forall_eq_zero`。

候选已有引理：
- `finsum_eq_zero_of_forall_eq_zero`
  （Mathlib/Algebra/BigOperators/Finprod.lean:579，`finprod_eq_one_of_forall_eq_one`
  的 to_additive）
- `Finset.sum_eq_zero_iff`
  （Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:115，
  `prod_eq_one_iff` 的 to_additive，对 `ℕ` 适用因 `AddUnits ℕ` 是 Subsingleton）
- `Set.Finite.toFinset`（Mathlib/Data/Set/Finite.lean） -/
theorem NSUM_EQ_0_IFF {α : Type*} {s : Set α} {f : α → ℕ}
    (hs : s.Finite) :
    (∑ᶠ x ∈ s, f x) = 0 ↔ ∀ x, x ∈ s → f x = 0 := by
  rw [finsum_mem_eq_finite_toFinset_sum f hs, Finset.sum_eq_zero_iff]
  exact ⟨fun h x hx => h x (hs.mem_toFinset.mpr hx),
    fun h x hx => h x (hs.mem_toFinset.mp hx)⟩

/-- HOL Conforming.hl :465-483 `N_FAN_EQ_0_IMP_CARD_FACE_EQ_3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ N_FAN(x,V,E)=0
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> CARD ds=3
```

编码说明：HOL `N_FAN(x,V,E)` ↔ `nFan x V E hfan`
（ConformingDefs.lean:204）；`CARD ds` ↔ `ds.ncard`。

证明思路：展开 `nFan` 为 `∑ᶠ f ∈ faceSet, (f.ncard - 3)`；由
`NSUM_EQ_0_IFF`（`FINITE_FACE_FAN` 给出每个面有限，face_set 的有限性
用 `Set.Finite` 的像）与 `hn` 得 `ds.ncard - 3 = 0`；再由
`CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN` 得 `3 ≤ ds.ncard`，算术即得
`ds.ncard = 3`。

候选已有引理：
- `nFan`（Kepler/Text/ConformingDefs.lean:204）
- `NSUM_EQ_0_IFF`（本文件上文，HOL :458）
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`（Kepler/Text/PlanarityAuto15.lean:139）
- `FINITE_FACE_FAN`（Kepler/Text/PlanarityAuto14.lean:693） -/
theorem N_FAN_EQ_0_IMP_CARD_FACE_EQ_3 {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hn : nFan x V E hfan = 0)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ds.ncard = 3 := by
  have hzero : ∀ f, f ∈ (hypermapOfFan x V E hfan).faceSet → f.ncard - 3 = 0 := by
    refine (NSUM_EQ_0_IFF (Hypermap.faceSet_finite (hypermapOfFan x V E hfan))).mp ?_
    simpa [nFan] using hn
  have hds0 : ds.ncard - 3 = 0 := hzero ds hds
  have hge : 3 ≤ ds.ncard := CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN hfan hcard hds
  omega
