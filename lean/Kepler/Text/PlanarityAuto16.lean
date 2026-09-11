/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18t.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18t of block 18, planarity.hl:15281-15463):
- `ball_eq_normball` (15281)            [SKIPPED: Mathlib-general, see below]
- `dartset_leads_into_fan_eventually_radial_norm` (15286)
- `measurable_dartset_leads_into3_fan` (15301)
- `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM` (15318)
- `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV` (15333)
- `solid_of_dartset_leads_into_fan_triangle_fan` (15370)
- `MOZNWEH` (15443)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- `FAN` ↔ `FAN` (Kepler/Text/Fan.lean:56); `CARD (set_of_edge v V E) > 1`
  ↔ `1 < (setOfEdge v V E).ncard` (repo convention, cf.
  Kepler/Text/PlanarityDarts.lean:94); `fan80` ↔ `fan80`
  (Kepler/Text/Fan.lean:227); `sigma_fan` ↔ `sigmaFan`
  (Kepler/Text/Fan.lean:67).
- Quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y`
  ↦ `y.1`/`y.2`, `d_fan` ↦ `dartOfFan` (Fan.lean:90).
- `hypermap1_of_fanx (x,V,E)` is NOT ported; the face-set hypothesis
  `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with `ds : Set (V3 × V3)`
  (cf. Kepler/Text/PlanarityComponent.lean:37-48, PlanarityAuto15.lean:33).
- `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); `dart_leads_into` ↔
  `dartLeadsInto` (Kepler/Text/TopologyFan.lean:4179).
- HOL `ball (x,r)` and `normball x r` both map to Mathlib
  `Metric.ball x r` (cf. PlanarityAuto15.lean:46). Consequently
  `ball_eq_normball` (`!x r. ball (x,r) = normball x r`) is a
  Mathlib-general statement already provided by Mathlib as
  `ball_eq` (the additive `to_additive` of
  `ball_eq'`, Mathlib/Analysis/Normed/Group/Basic.lean:864-865:
  `ball y ε = {x | ‖x - y‖ < ε}`). Per task instructions it is SKIPPED.
- HOL `eventually_radial` (sphere.hl:452) is NOT ported; it is inlined as
  `∃ r, 0 < r ∧ radial_norm r x (C ∩ Metric.ball x r)` with `radial_norm`
  (vol1.hl:18-23) inlined as `C' ⊆ Metric.ball x r ∧ ∀ u, x + u ∈ C' →
  ∀ t, 0 < t → t * ‖u‖ < r → x + t • u ∈ C'` (same convention as
  PlanarityAuto15.lean:673-700 for `radial_norm`).
- HOL `sol` (volume/vol1.hl:651, introduced by `new_specification` from
  `pre_def_4_3b_alt`) is NOT ported (module-map: Volume layer not started).
  It is encoded inline by its HOL specification using `Classical.epsilon`
  (the Lean analogue of HOL's `@`/`new_specification` choice): for fixed
  `x` and `C`, `sol x C` is the `s` with
  `∀ r, 0 < r → measurable (C ∩ ball x r) → radial_norm r x (C ∩ ball x r)
   → s = 3 * vol (C ∩ ball x r) / r^3`. No new named definition is added.
- HOL `dihV` (sphere.hl:377) is NOT ported; it is inlined via the ported
  `arcVFan` (Kepler/Text/TopologyFan.lean:3654, HOL `arcV`) and the HOL
  defining formula `let va = w2-w0; vb = w3-w0; vc = w1-w0;
  vap = (vc·vc)•va - (va·vc)•vc; vbp = (vc·vc)•vb - (vb·vc)•vc;
  arcV 0 vap vbp`.
- HOL `measurable` ↔ `MeasurableSet` (Mathlib); HOL `vol` ↔ `volume`.
- HOL `sum (ds) f` (set sum, HOL `sum`/`iterate`) is encoded as the
  Mathlib finite sum over a set, `∑ᶠ y ∈ ds, f y` (finsum); under
  `CARD ds = 3` the set is finite so this coincides with HOL's sum.
- `AZIM_DIVH` (used by the HOL proof of `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV`)
  is NOT ported anywhere in the repo; noted per-theorem.
- This file imports `Mathlib` (in addition to the planarity chain) because
  `MeasurableSet`, `volume`, `∑ᶠ` and the Euclidean `MeasureSpace`
  instance are not reachable from `Kepler.Text.PlanarityAuto15`.
-/

import Kepler.Text.PlanarityAuto15
import Kepler.Geom.Volume
import Kepler.Geom.SolidAngle
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open MeasureTheory
open scoped Topology
open scoped BigOperators

/-! ## 径向性、可测性与方位角/二面角恒等式（planarity.hl:15281-15369） -/

/- HOL planarity.hl :15281-15285 `ball_eq_normball`

HOL 原文：
```
!x r.ball (x,r)= normball x r
```

编码说明（缺口）：本陈述是 Mathlib-general 的度量球刻画，Mathlib 已有
`ball_eq : ball y ε = {x | ‖x - y‖ < ε}`
（`ball_eq'` 的 `to_additive`，Mathlib/Analysis/Normed/Group/Basic.lean:864-865）。
按任务规则「Mathlib 已有则跳过」，本文件不重复陈述。

证明思路：`Set.ext` + `Metric.mem_ball` + `dist_eq_norm`（即 Mathlib
`ball_eq` 的证明）。

候选已有引理：
- `ball_eq`（Mathlib/Analysis/Normed/Group/Basic.lean:864）
- `Metric.mem_ball`、`dist_eq_norm`（Mathlib） -/

/-- HOL planarity.hl :15286-15300 `dartset_leads_into_fan_eventually_radial_norm`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>   eventually_radial  x ((dartset_leads_into_fan x V E ds))
```

编码说明（缺口）：HOL `eventually_radial x C`（sphere.hl:452）未移植，
就地展开为 `∃ r, 0 < r ∧ radial_norm r x (C ∩ Metric.ball x r)`，
其中 `radial_norm r x C'`（vol1.hl:18-23）展开为
`C' ⊆ Metric.ball x r ∧ ∀ u, x + u ∈ C' → ∀ t, 0 < t → t * ‖u‖ < r →
x + t • u ∈ C'`，取 `C = dartsetLeadsIntoFan x V E ds`、
`C' = C ∩ Metric.ball x r`。与 PlanarityAuto15.lean:673-700 的
`radial_norm` 内联方式一致。

证明思路：由 `dartset_leads_into_fan_radial`（本批上游，HOL :15260）
在 `r = 1` 处取 `radial_norm 1 x (C ∩ Metric.ball x 1)`，再取见证
`r = 1` 即得 `eventually_radial`；`0 < 1` 由 `norm_num` 收口。

候选已有引理：
- `dartset_leads_into_fan_radial`（Kepler/Text/PlanarityAuto15.lean:691，
  HOL `dartset_leads_into_fan_radial` :15260）
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）
- 缺口：`eventually_radial`（sphere.hl:452）、`radial_norm`（vol1.hl:18）
  未移植（本陈述就地展开） -/
theorem dartset_leads_into_fan_eventually_radial_norm
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    ∃ r : ℝ, 0 < r ∧
      (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
        ∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
          ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
            x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r := by
  exact ⟨1, by norm_num,
    dartset_leads_into_fan_radial hfan hcard hfan80 hds hds3 (by norm_num)⟩

/-- HOL planarity.hl :15301-15317 `measurable_dartset_leads_into3_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds e:real.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
/\ e> &0
==>   measurable((dartset_leads_into_fan x V E ds) INTER ball (x,e))
```

编码说明：HOL `measurable` ↔ `MeasurableSet`；HOL `ball (x,e)` 用
`Metric.ball x e`（见 PlanarityAuto15.lean:46）。`INTER` ↔ `∩`。

证明思路：HOL 用 `KVQWYDL_lemma10`（HOL :15163）把 `dartsetLeadsIntoFan`
换成 `aff_gt {x} {pr2 f1, pr2 f2, pr2 f3}`，再交换 `INTER` 后用
`MEASURABLE_BALL_AFF_GT`（未移植）得可测。Lean 侧对应先用
`KVQWYDL_lemma10` + `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 归约，
再证 `affGt` 与球的交可测。

候选已有引理：
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466，HOL :15163）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371，HOL :15114）
- `MeasurableSet`、`measurableSet_ball`（Mathlib）
- 缺口：`MEASURABLE_BALL_AFF_GT`（HOL 未在仓库移植） -/
theorem measurable_dartset_leads_into3_fan
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)} {e : ℝ}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (he : 0 < e) :
    MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x e) := by
  rw [← KVQWYDL_lemma10 hfan hcard hfan80 hds hds3]
  have hmeas : MeasurableSet
      (affGt ({x} : Set V3) ((fun y : V3 × V3 => y.1) '' ds)) := by
    obtain ⟨f1, f2, f3, hdsf, _hf12, _hf23, _hf31, he23, he31, he12, hsig,
      _hf3fst, _hf2fst, _hf1fst⟩ :=
      CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1 hfan hcard hds hds3
    have himg : (fun y : V3 × V3 => y.1) '' ds = ({f1.1, f2.1, f3.1} : Set V3) := by
      rw [hdsf]
      ext z
      simp
      tauto
    obtain ⟨hθ0, hθπ⟩ := hfan80 f2.1 f3.1 he23
    rw [hsig] at hθ0 hθπ
    have hcop : ¬ Coplanar ({x, f1.1, f2.1, f3.1} : Set V3) :=
      properties_fully_surrounded hfan he12 he23 hθ0 hθπ
    rw [himg]
    exact (OPEN_AFF_GT_1_3 x f1.1 f2.1 f3.1 hcop).measurableSet
  exact hmeas.inter Metric.isOpen_ball.measurableSet

/-- HOL planarity.hl :15318-15332 `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y.
FAN(x,V,E)
/\ y IN d_fan(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
azim_fan x V E (pr2 y) (pr3 y)= azim x (pr2 y) (pr3 y) (sigma_fan x V E (pr2 y) (pr3 y))
```

编码说明：`d_fan` ↦ `dartOfFan V E`（Fan.lean:90）；二元组 dart 下
`pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；`azim_fan` ↦ `azimFan`
（Kepler/Text/TopologyFan.lean:3484，亦见 Fan.lean:177）；HOL `azim`
↦ `Kepler.Geom.azim`（Azim.lean:58）。注意 HOL `azim_fan` 的定义是
`if CARD (set_of_edge v V E) > 1 then azim x v w (sigma_fan ...) else 2π`，
在 `CARD > 1` 假设下化为 `azim ...`。

证明思路：`azimFan` 在 `1 < (setOfEdge y.1 V E).ncard` 上按定义展开，
由 `IN_D1_FAN_IMP_EDGE_FAN`（HOL :15179）得 `{y.1,y.2} ∈ E`，再经
`remark1_fan` 的分量（`edge_ne_of_fan` + `point_in_aff_ge`）与
`hcard y.1 (…)` 把条件 `1 < ncard` 消去，最后 `rfl`/`if_pos` 收口。

候选已有引理：
- `IN_D1_FAN_IMP_EDGE_FAN`（Kepler/Text/PlanarityAuto15.lean:513，
  HOL :15179）
- `dartOfFan`（Kepler/Text/Fan.lean:90）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异分量）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334，
  HOL `remark1_fan` 成员分量）
- 缺口：`remark1_fan`（fan.hl:423）未以原名移植（分量见上） -/
theorem CARD_GT1_IMP_AZIM_FAN_EQ_AZIM
    {x : V3} {V : Set V3} {E : Set (Set V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hy : y ∈ dartOfFan V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    azimFan x V E y.1 y.2 = azim x y.1 y.2 (sigmaFan x V E y.1 y.2) := by
  have he : {y.1, y.2} ∈ E := IN_D1_FAN_IMP_EDGE_FAN hfan hcard hy
  have hyV : y.1 ∈ V := (FAN_in_setOfEdge x V E y.1 y.2 hfan he).1
  have h : 1 < (setOfEdge y.1 V E).ncard := hcard y.1 hyV
  unfold azimFan
  rw [if_pos h]

/-- HOL planarity.hl :15333-15369 `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ y IN d_fan(x,V,E)
==>
azim_fan x V E (pr2 y) (pr3 y)= dihV x (pr2 y) (pr3 y) (sigma_fan x V E (pr2 y) (pr3 y))
```

编码说明（缺口）：HOL `dihV w0 w1 w2 w3`（sphere.hl:377）未移植，就地
展开为 `let va = w2-w0; vb = w3-w0; vc = w1-w0;
vap = (vc·vc)•va - (va·vc)•vc; vbp = (vc·vc)•vb - (vb·vc)•vc;
arcV 0 vap vbp`，其中 `arcV` 用已移植的 `arcVFan`
（Kepler/Text/TopologyFan.lean:3654）。取 `w0 = x`、`w1 = y.1`、
`w2 = y.2`、`w3 = sigmaFan x V E y.1 y.2`。

证明思路：先用 `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`（本文件上文）把
`azimFan` 换成 `azim x (pr2 y) (pr3 y) (sigma_fan …)`；由
`IN_D1_FAN_IMP_EDGE_FAN` 与 `remark1_fan` 分量得非退化，再用
`sigma_fan_in_set_of_edge` 与 `fan80` 的三点非共线条件，最后以
`AZIM_DIVH`（HOL，未移植）把 `azim` 与 `dihV` 等同。

候选已有引理：
- `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`（本文件上文，HOL :15318）
- `IN_D1_FAN_IMP_EDGE_FAN`（Kepler/Text/PlanarityAuto15.lean:513）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `arcVFan`（Kepler/Text/TopologyFan.lean:3654，HOL `arcV`）
- 缺口：`dihV`（sphere.hl:377）未移植（本陈述就地展开）；
  `AZIM_DIVH`（HOL 证明所用）未移植；`sigma_fan_in_set_of_edge`
  （HOL fan.hl）未以原名移植 -/
private theorem smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_smul (a : V3) (t : ℝ) (b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem add_dot (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_add (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem coe_sub (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

private theorem coe_add (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

private theorem coe_smul (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem coe_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem cexp_cos_re (r : ℝ) : (Complex.exp ((r : ℂ) * I)).re = Real.cos r := by
  have h := congrArg Complex.re (Complex.exp_mul_I (r : ℂ))
  simpa using h

private theorem cexp_sin_im (r : ℝ) : (Complex.exp ((r : ℂ) * I)).im = Real.sin r := by
  have h := congrArg Complex.im (Complex.exp_mul_I (r : ℂ))
  simpa using h

/-- `AZIM_DIVH`（sphere.hl）的轴向标架证明：`azim a b c d` 与把 `c-a`、`d-a`
投影到轴 `b-a` 的正交补后所得向量的夹角（即 `dihV`）相等，前提是
`azim a b c d ≤ π`。 -/
private theorem azim_eq_arcVFan_proj {a b c d : V3}
    (h1 : ¬ Collinear3 a b c) (h2 : ¬ Collinear3 a b d)
    (hπ : azim a b c d ≤ Real.pi) :
    azim a b c d =
      let va := c - a
      let vb := d - a
      let vc := b - a
      arcVFan 0 ((vc ⬝ᵥ vc) • va - (va ⬝ᵥ vc) • vc)
                ((vc ⬝ᵥ vc) • vb - (vb ⬝ᵥ vc) • vc) := by
  have hab : b ≠ a := fun he => h1 (collinear3_of_eq he)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (b - a) (sub_ne_zero.mpr hab)
  have hax : (b - a : V3) = dist b a • e3 := by
    rw [dist_eq_norm]; exact halign
  have hax' : (b : Fin 3 → ℝ) - (a : Fin 3 → ℝ) = dist b a • (e3 : Fin 3 → ℝ) := by
    have h := congrArg (fun v : V3 => (v : Fin 3 → ℝ)) hax
    simpa only [coe_sub, coe_smul] using h
  obtain ⟨psi, r1, r2, hr1, hr2, hz1, hz2⟩ :=
    azim_frame_spec (v := a) (w := b) (w1 := c) (w2 := d) h1 h2 hon hax hab
  have hon0 := hon
  obtain ⟨h11, h22, h33, h12, h13, h23, -⟩ := hon
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dot_comm, h12]
  have hva1 : (c - a) ⬝ᵥ e1 = r1 * Real.cos psi := by
    have h := congrArg Complex.re hz1
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      mul_one] at h
    rw [cexp_cos_re] at h
    exact h
  have hva2 : (c - a) ⬝ᵥ e2 = r1 * Real.sin psi := by
    have h := congrArg Complex.im hz1
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] at h
    rw [cexp_sin_im] at h
    exact h
  have hvb1 : (d - a) ⬝ᵥ e1 = r2 * Real.cos (psi + azim a b c d) := by
    have h := congrArg Complex.re hz2
    simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      mul_one] at h
    rw [cexp_cos_re] at h
    exact h
  have hvb2 : (d - a) ⬝ᵥ e2 = r2 * Real.sin (psi + azim a b c d) := by
    have h := congrArg Complex.im hz2
    simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
      zero_add, mul_one] at h
    rw [cexp_sin_im] at h
    exact h
  set s : ℝ := dist b a ^ 2 with hs
  have hs_pos : 0 < s := by rw [hs]; exact pow_pos (dist_pos.mpr hab) 2
  set u1 : V3 := ((c - a) ⬝ᵥ e1) • e1 + ((c - a) ⬝ᵥ e2) • e2 with hu1def
  set u2 : V3 := ((d - a) ⬝ᵥ e1) • e1 + ((d - a) ⬝ᵥ e2) • e2 with hu2def
  have hu1_exp : u1 = (r1 * Real.cos psi) • e1 + (r1 * Real.sin psi) • e2 := by
    rw [hu1def, hva1, hva2]
  have hu2_exp : u2 = (r2 * Real.cos (psi + azim a b c d)) • e1 +
      (r2 * Real.sin (psi + azim a b c d)) • e2 := by
    rw [hu2def, hvb1, hvb2]
  have hvcvc : (b - a) ⬝ᵥ (b - a) = s := by
    rw [coe_sub, hax', smul_dotProduct, dotProduct_smul, h33, smul_eq_mul, hs]
    ring
  have hva_vc : (c - a) ⬝ᵥ (b - a) = dist b a * ((c - a) ⬝ᵥ e3) := by
    rw [coe_sub, hax', dotProduct_smul, smul_eq_mul]
  have hvb_vc : (d - a) ⬝ᵥ (b - a) = dist b a * ((d - a) ⬝ᵥ e3) := by
    rw [coe_sub, hax', dotProduct_smul, smul_eq_mul]
  have hvap : ((b - a) ⬝ᵥ (b - a)) • (c - a) - ((c - a) ⬝ᵥ (b - a)) • (b - a)
      = s • u1 := by
    have hdot3 : ((((c - a) ⬝ᵥ e1) • e1 + ((c - a) ⬝ᵥ e2) • e2 +
        ((c - a) ⬝ᵥ e3) • e3) ⬝ᵥ e3) = (c - a) ⬝ᵥ e3 := by
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct, add_dotProduct,
        smul_dotProduct, smul_dotProduct, smul_dotProduct, h13, h23, h33]
      ring
    rw [hvcvc, hva_vc, hax, on3_expand hon0 (c - a), hdot3, hu1def, hs]
    module
  have hvbp : ((b - a) ⬝ᵥ (b - a)) • (d - a) - ((d - a) ⬝ᵥ (b - a)) • (b - a)
      = s • u2 := by
    have hdot3 : ((((d - a) ⬝ᵥ e1) • e1 + ((d - a) ⬝ᵥ e2) • e2 +
        ((d - a) ⬝ᵥ e3) • e3) ⬝ᵥ e3) = (d - a) ⬝ᵥ e3 := by
      rw [coe_add, coe_add, coe_smul, coe_smul, coe_smul, add_dotProduct, add_dotProduct,
        smul_dotProduct, smul_dotProduct, smul_dotProduct, h13, h23, h33]
      ring
    rw [hvcvc, hvb_vc, hax, on3_expand hon0 (d - a), hdot3, hu2def, hs]
    module
  have hu1norm : ‖u1‖ = r1 := by
    have hsq : ‖u1‖ ^ 2 = r1 ^ 2 := by
      rw [norm_sq_eq_dot, hu1_exp]
      simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, h11, h22, h12, h21]
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq psi]
    nlinarith [norm_nonneg u1, hr1.le]
  have hu2norm : ‖u2‖ = r2 := by
    have hsq : ‖u2‖ ^ 2 = r2 ^ 2 := by
      rw [norm_sq_eq_dot, hu2_exp]
      simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, h11, h22, h12, h21]
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq (psi + azim a b c d)]
    nlinarith [norm_nonneg u2, hr2.le]
  have hu1u2 : u1 ⬝ᵥ u2 = r1 * r2 * Real.cos (azim a b c d) := by
    rw [hu1_exp, hu2_exp]
    simp only [coe_add, coe_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, h11, h22, h12, h21]
    have htrig : Real.cos psi * Real.cos (psi + azim a b c d) +
        Real.sin psi * Real.sin (psi + azim a b c d) = Real.cos (azim a b c d) := by
      rw [← Real.cos_sub]
      rw [show psi - (psi + azim a b c d) = -(azim a b c d) by ring, Real.cos_neg]
    linear_combination (r1 * r2) * htrig
  have hnum : WithLp.ofLp (s • u1) ⬝ᵥ WithLp.ofLp (s • u2) =
      (s * r1) * (s * r2) * Real.cos (azim a b c d) := by
    rw [coe_smul, coe_smul, smul_dotProduct, dotProduct_smul, hu1u2]
    ring
  have hden1 : dist (s • u1) 0 = s * r1 := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hu1norm]
  have hden2 : dist (s • u2) 0 = s * r2 := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hu2norm]
  have hden : dist (s • u1) 0 * dist (s • u2) 0 = (s * r1) * (s * r2) := by
    rw [hden1, hden2]
  have harg : (WithLp.ofLp (s • u1) ⬝ᵥ WithLp.ofLp (s • u2)) /
      (dist (s • u1) 0 * dist (s • u2) 0) = Real.cos (azim a b c d) := by
    rw [hnum, hden]
    have hsne : s ≠ 0 := ne_of_gt hs_pos
    have hr1ne : r1 ≠ 0 := ne_of_gt hr1
    have hr2ne : r2 ≠ 0 := ne_of_gt hr2
    field_simp
  dsimp only
  show azim a b c d = arcVFan 0
    (((b - a) ⬝ᵥ (b - a)) • (c - a) - ((c - a) ⬝ᵥ (b - a)) • (b - a))
    (((b - a) ⬝ᵥ (b - a)) • (d - a) - ((d - a) ⬝ᵥ (b - a)) • (b - a))
  rw [hvap, hvbp, arcVFan, coe_zero, sub_zero, sub_zero, harg,
    Real.arccos_cos (azim_nonneg a b c d) hπ]

theorem CARD_GT1_IMP_AZIM_FAN_EQ_DIHV
    {x : V3} {V : Set V3} {E : Set (Set V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hy : y ∈ dartOfFan V E) :
    azimFan x V E y.1 y.2 =
      let va := y.2 - x
      let vb := sigmaFan x V E y.1 y.2 - x
      let vc := y.1 - x
      arcVFan 0 ((vc ⬝ᵥ vc) • va - (va ⬝ᵥ vc) • vc)
                ((vc ⬝ᵥ vc) • vb - (vb ⬝ᵥ vc) • vc) := by
  have he : {y.1, y.2} ∈ E := IN_D1_FAN_IMP_EDGE_FAN hfan hcard hy
  have hnc1 : ¬ Collinear3 x y.1 y.2 := fan_not_collinear hfan he
  have hy2soe : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp he
  have hsigsoe : sigmaFan x V E y.1 y.2 ∈ setOfEdge y.1 V E :=
    sigma_fan_in_setOfEdge hfan hy2soe
  have hsigE : {y.1, sigmaFan x V E y.1 y.2} ∈ E :=
    (properties_of_setOfEdge_fan x V E y.1 (sigmaFan x V E y.1 y.2) hfan).mpr hsigsoe
  have hnc2 : ¬ Collinear3 x y.1 (sigmaFan x V E y.1 y.2) :=
    fan_not_collinear hfan hsigE
  have h80 := hfan80 y.1 y.2 he
  rw [CARD_GT1_IMP_AZIM_FAN_EQ_AZIM hfan hy hcard]
  exact azim_eq_arcVFan_proj hnc1 hnc2 h80.2.le

/-- `affGt {x} {v1,v2,v3}`（`¬ Coplanar {x,v1,v2,v3}`）与单位球的交非空。
用于从 `VOLUME_SOLID_TRIANGLE` 的 `ENNReal.ofReal` 值提取立体角的非负性：
交为开集且非空，故体积为正，从而 `ofReal` 的自变量为正。 -/
private theorem solid_triangle_inter_ball_nonempty {x v1 v2 v3 : V3}
    (hcop : ¬ Coplanar ({x, v1, v2, v3} : Set V3)) :
    (Metric.ball x 1 ∩ affGt ({x} : Set V3) {v1, v2, v3}).Nonempty := by
  have hx1 : x ≠ v1 := by
    intro h; apply hcop
    have he : ({x, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; exact coplanar_triple v1 v2 v3
  have hx2 : x ≠ v2 := by
    intro h; apply hcop
    have he : ({x, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; exact coplanar_triple v1 v2 v3
  have hx3 : x ≠ v3 := by
    intro h; apply hcop
    have he : ({x, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [he]; exact coplanar_triple v1 v2 v3
  have hdis : Disjoint ({x} : Set V3) {v1, v2, v3} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1, hx2, hx3⟩
  set c : ℝ := 1 / (4 + ‖v1 + v2 + v3 - 3 • x‖) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcn : c * (4 + ‖v1 + v2 + v3 - 3 • x‖) = 1 := by
    rw [hcdef]; field_simp
  have hn0 : 0 ≤ ‖v1 + v2 + v3 - 3 • x‖ := norm_nonneg _
  have hc3 : 3 * c < 1 := by nlinarith [hcn, hcpos, hn0]
  have hcw : c * ‖v1 + v2 + v3 - 3 • x‖ < 1 := by nlinarith [hcn, hcpos]
  refine ⟨(1 - 3 * c) • x + c • v1 + c • v2 + c • v3, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (1 - 3 * c) • x + c • v1 + c • v2 + c • v3 - x =
        c • (v1 + v2 + v3 - 3 • x) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    exact hcw
  · rw [AFF_GT_1_3 x v1 v2 v3 hdis]
    exact ⟨1 - 3 * c, c, c, c, hcpos, hcpos, hcpos, by ring, rfl⟩

/-! ## 立体角恒等式与 MOZNWEH（planarity.hl:15370-15463） -/

/-- HOL planarity.hl :15370-15442 `solid_of_dartset_leads_into_fan_triangle_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
	FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>    
sol  x (dartset_leads_into_fan x V E ds)= &2 * pi + sum (ds) (\y. (azim_fan x V E (pr2 y) (pr3 y))  - pi)
```

编码说明（缺口）：HOL `sol`（volume/vol1.hl:651，经 `new_specification`
由 `pre_def_4_3b_alt` 引入）未移植（module-map：Volume 层未开始）。
此处按 HOL 规格用 `Classical.epsilon` 就地编码（HOL `@`/规格选择算子的
Lean 对应）：固定 `x, C` 时 `sol x C` 取满足
`∀ r, 0 < r → MeasurableSet (C ∩ ball x r) → radial_norm r x (C ∩ ball x r)
 → s = 3 * vol (C ∩ ball x r) / r^3` 的 `s`（其中 `radial_norm` 按
vol1.hl:18-23 展开，`vol` ↔ `volume`）。不引入新的具名定义。
HOL `sum (ds) f` 用 Mathlib 集合有限和 `∑ᶠ y ∈ ds, f y`（`CARD ds = 3`
保证有限）；`&2 * pi` ↔ `2 * Real.pi`。

证明思路：HOL 由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 取
`ds = {f1,f2,f3}`，用 `SUM_UNION`/`SUM_SING` 拆成三项；由
`measurable_dartset_leads_into3_fan`、`dartset_leads_into_fan_radial`
（本批上文）与 `ball_eq_normball` 得 `sol` 规格的可测/径向前提，再用
`UNIQUE_DARTSET_LEADS_INTO1_FAN` + `KVQWYDL_lemma1` 定位
`dartsetLeadsIntoFan = aff_gt {x} {pr2 f1, pr2 f2, pr2 f3}`，接着
`CARD_GT1_IMP_AZIM_FAN_EQ_DIHV` 把每项 `azim_fan` 化为 `dihV`，最后
`VOLUME_SOLID_TRIANGLE` + `PROPERTIES_TRIANGLE_FAN` 与 `sol` 规格相减收口。

候选已有引理：
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371，HOL :15114）
- `measurable_dartset_leads_into3_fan`、`dartset_leads_into_fan_radial`
  （本文件上文 / PlanarityAuto15.lean:691）
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`
  （Kepler/Text/PlanarityComponent.lean:468）
- `KVQWYDL_lemma1`（Kepler/Text/PlanarityAuto13.lean:368）
- `PROPERTIES_TRIANGLE_FAN`（Kepler/Text/PlanarityAuto14.lean:368）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：`sol`（vol1.hl:651）、`VOLUME_SOLID_TRIANGLE`（vol1.hl）、
  `AZIM_DIVH`、`dihV`（sphere.hl:377）未移植 -/
theorem solid_of_dartset_leads_into_fan_triangle_fan
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    sol x (dartsetLeadsIntoFan x V E ds)
      = 2 * Real.pi + ∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi) := by
  obtain ⟨f1, f2, f3, hdsf, hf12, hf23, hf31, he23, he31, he12, hsig,
    hf3fst, hf2fst, hf1fst⟩ :=
    CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1 hfan hcard hds hds3
  have hf1d1 : f1 ∈ dart1OfFan V E := by
    show {f1.1, f1.2} ∈ E
    rw [← hf2fst]; exact he12
  have hf2d1 : f2 ∈ dart1OfFan V E := by
    show {f2.1, f2.2} ∈ E
    rw [← hf3fst]; exact he23
  have hf3d1 : f3 ∈ dart1OfFan V E := by
    show {f3.1, f3.2} ∈ E
    rw [← hf1fst]; exact he31
  have hf1dart : f1 ∈ dartOfFan V E := by
    rw [dartOfFan_eq_dart1_of_surrounded hfan hcard]; exact hf1d1
  have hf2dart : f2 ∈ dartOfFan V E := by
    rw [dartOfFan_eq_dart1_of_surrounded hfan hcard]; exact hf2d1
  have hf3dart : f3 ∈ dartOfFan V E := by
    rw [dartOfFan_eq_dart1_of_surrounded hfan hcard]; exact hf3d1
  have hf12ne : f1 ≠ f2 := by
    intro h; exact f_fan_no_fix hfan f1 hf1d1 (hf12.trans h.symm)
  have hf23ne : f2 ≠ f3 := by
    intro h; exact f_fan_no_fix hfan f2 hf2d1 (hf23.trans h.symm)
  have hf31ne : f3 ≠ f1 := by
    intro h; exact f_fan_no_fix hfan f3 hf3d1 (hf31.trans h.symm)
  have hf13ne : f1 ≠ f3 := hf31ne.symm
  have himg : (fun y : V3 × V3 => y.1) '' ds = ({f1.1, f2.1, f3.1} : Set V3) := by
    rw [hdsf]; ext z; simp; tauto
  have hleads : dartsetLeadsIntoFan x V E ds =
      affGt ({x} : Set V3) {f1.1, f2.1, f3.1} := by
    rw [← KVQWYDL_lemma10 hfan hcard hfan80 hds hds3, himg]
  have hmeas : MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x 1) :=
    measurable_dartset_leads_into3_fan hfan hcard hfan80 hds hds3 (by norm_num)
  have hrad : radialNorm 1 x (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x 1) :=
    dartset_leads_into_fan_radial hfan hcard hfan80 hds hds3 (by norm_num)
  have hsol := sol_spec (x := x) (C := dartsetLeadsIntoFan x V E ds) (r := 1)
    (by norm_num) hmeas hrad
  obtain ⟨hθ0, hθπ⟩ := hfan80 f2.1 f3.1 he23
  rw [hsig] at hθ0 hθπ
  have hcop : ¬ Coplanar ({x, f1.1, f2.1, f3.1} : Set V3) :=
    properties_fully_surrounded hfan he12 he23 hθ0 hθπ
  have hne : (Metric.ball x 1 ∩ affGt ({x} : Set V3) {f1.1, f2.1, f3.1}).Nonempty :=
    solid_triangle_inter_ball_nonempty hcop
  have hvolpos : 0 < volume (Metric.ball x 1 ∩
      affGt ({x} : Set V3) {f1.1, f2.1, f3.1}) :=
    (Metric.isOpen_ball.inter (OPEN_AFF_GT_1_3 x f1.1 f2.1 f3.1 hcop)).measure_pos
      volume hne
  have hvol := volume_solid_triangle (v0 := x) (v1 := f1.1) (v2 := f2.1) (v3 := f3.1)
    (r := 1) (by norm_num) hcop
  rw [hvol] at hvolpos
  rw [ENNReal.ofReal_pos] at hvolpos
  have hTpos : 0 < (dihV x f1.1 f2.1 f3.1 + dihV x f2.1 f3.1 f1.1 +
      dihV x f3.1 f1.1 f2.1 - Real.pi) := by nlinarith [hvolpos]
  have hvolreal : volume.real (Metric.ball x 1 ∩
      affGt ({x} : Set V3) {f1.1, f2.1, f3.1}) =
      (dihV x f1.1 f2.1 f3.1 + dihV x f2.1 f3.1 f1.1 +
        dihV x f3.1 f1.1 f2.1 - Real.pi) * 1 ^ 3 / 3 := by
    rw [Measure.real_def, hvol, ENNReal.toReal_ofReal (by nlinarith [hTpos])]
  have hPTF := PROPERTIES_TRIANGLE_FAN hfan he12 he23 he31 hsig hcard hfan80
  have hf1azim : azimFan x V E f1.1 f1.2 =
      dihV x f1.1 f1.2 (sigmaFan x V E f1.1 f1.2) :=
    CARD_GT1_IMP_AZIM_FAN_EQ_DIHV hfan hcard hfan80 hf1dart
  have hf2azim : azimFan x V E f2.1 f2.2 =
      dihV x f2.1 f2.2 (sigmaFan x V E f2.1 f2.2) :=
    CARD_GT1_IMP_AZIM_FAN_EQ_DIHV hfan hcard hfan80 hf2dart
  have hf3azim : azimFan x V E f3.1 f3.2 =
      dihV x f3.1 f3.2 (sigmaFan x V E f3.1 f3.2) :=
    CARD_GT1_IMP_AZIM_FAN_EQ_DIHV hfan hcard hfan80 hf3dart
  have hsum : (∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi)) =
      (azimFan x V E f1.1 f1.2 - Real.pi) + (azimFan x V E f2.1 f2.2 - Real.pi) +
        (azimFan x V E f3.1 f3.2 - Real.pi) := by
    rw [hdsf]
    rw [finsum_mem_insert (fun y : V3 × V3 => azimFan x V E y.1 y.2 - Real.pi)
      (by simp [hf12ne, hf13ne]) ((Set.finite_singleton f3).insert f2)]
    rw [finsum_mem_pair hf23ne]
    ring
  have hLHS : sol x (dartsetLeadsIntoFan x V E ds) =
      (dihV x f1.1 f2.1 f3.1 + dihV x f2.1 f3.1 f1.1 +
        dihV x f3.1 f1.1 f2.1) - Real.pi := by
    rw [hsol, hleads, Set.inter_comm, hvolreal]
    ring
  have hRHS : 2 * Real.pi + (∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi)) =
      (dihV x f1.1 f2.1 f3.1 + dihV x f2.1 f3.1 f1.1 +
        dihV x f3.1 f1.1 f2.1) - Real.pi := by
    rw [hsum, hf1azim, hf2azim, hf3azim]
    rw [← hf2fst, ← hf3fst, ← hf1fst, hPTF.1, hsig, hPTF.2]
    ring
  rw [hLHS, hRHS]

/-- HOL planarity.hl :15443-15463 `MOZNWEH`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds e.
	FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
/\ e> &0
==>    measurable((dartset_leads_into_fan x V E ds) INTER ball (x,e))
/\ eventually_radial  x ((dartset_leads_into_fan x V E ds))
/\ sol  x (dartset_leads_into_fan x V E ds)= &2 * pi + sum (ds) (\y. (azim_fan x V E (pr2 y) (pr3 y))  - pi)
```

编码说明（缺口）：三个合取项分别内联
`measurable_dartset_leads_into3_fan`、
`dartset_leads_into_fan_eventually_radial_norm`、
`solid_of_dartset_leads_into_fan_triangle_fan`（本文件上文）的结论；
`eventually_radial`、`sol`、`sum` 的内联方式见上两条 docstring。
HOL `e` 为可测项半径，`eventually_radial` 自带存在半径。

证明思路：HOL 直接 `MESON_TAC` 三条上游定理
（`solid_of_dartset_leads_into_fan_triangle_fan`、
`measurable_dartset_leads_into3_fan`、
`dartset_leads_into_fan_eventually_radial_norm`）。Lean 侧即
`⟨measurable_dartset_leads_into3_fan … he, ‹eventually_radial›,
 ‹sol 等式›⟩` 三项组装。

候选已有引理：
- `solid_of_dartset_leads_into_fan_triangle_fan`（本文件上文）
- `measurable_dartset_leads_into3_fan`（本文件上文）
- `dartset_leads_into_fan_eventually_radial_norm`（本文件上文） -/
theorem MOZNWEH
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)} {e : ℝ}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (he : 0 < e) :
    MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x e) ∧
      (∃ r : ℝ, 0 < r ∧
        (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
          ∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
            ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
              x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ∧
      sol x (dartsetLeadsIntoFan x V E ds)
        = 2 * Real.pi + ∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi) :=
  ⟨measurable_dartset_leads_into3_fan hfan hcard hfan80 hds hds3 he,
    dartset_leads_into_fan_eventually_radial_norm hfan hcard hfan80 hds hds3,
    solid_of_dartset_leads_into_fan_triangle_fan hfan hcard hfan80 hds hds3⟩

end Kepler.Text
