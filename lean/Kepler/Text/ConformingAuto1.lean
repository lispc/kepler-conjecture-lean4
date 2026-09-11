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
theorem IMAGE_F1_POWER_IN_FACE_IMP_IN_FACE (m : ℕ) {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y y1 : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds)
    (hy1 : y1 ∈ dartOfFan V E)
    (hpow : (f1Fan x V E)^[m] y1 = y) :
    y1 ∈ ds := by
  sorry

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
  sorry

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
theorem DARTSET_LEADS_INTO_SUBSET_WDART_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds)
    (hconf : conformingFan x V E hfan) :
    dartsetLeadsIntoFan x V E ds ⊆
      wDartFan x V E (x, y.1, y.2, sigmaFan x V E y.1 y.2) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry
