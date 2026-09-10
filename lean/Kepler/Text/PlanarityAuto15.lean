/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18s.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18s of block 18, planarity.hl:14910-15279):
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN` (14910)
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN` (14986)
- `lemma_CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN` (15064)
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` (15114)
- `KVQWYDL_lemma10` (15163)
- `IN_D1_FAN_IMP_EDGE_FAN` (15179)
- `EQ_PAIR_IMP_EQ_4_FAN` (15192)
- `KVQWYDL_lemma30` (15212)
- `KVQWYDL` (15243)
- `dartset_leads_into_fan_radial` (15260)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, the face-set hypothesis
  `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with pair darts
  `ds : Set (V3 × V3)`.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`, `f1_fan x V E` ↦ `fFanPair x V E` (Fan.lean:118),
  `d_fan` ↦ `dartOfFan` (Fan.lean:90), `d1_fan` ↦ `dart1OfFan`
  (Fan.lean:86). The HOL proofs rewrite `d_fan` to `d1_fan` via
  `dartset_fully_surrounded_is_non_isolated_fan`; the ported form is
  `dartOfFan_eq_dart1_of_surrounded` (Fan.lean:1084).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `dart_leads_into` ↔
  `dartLeadsInto` (Kepler/Text/TopologyFan.lean:4179).
- HOL `normball x r` ↔ Mathlib `Metric.ball x r` (both are
  `{y | dist y x < r}`; cf. `NORMBALL_BALL`, sphere.hl). HOL
  `radial_norm` is NOT ported anywhere in the repo; the final theorem
  inlines its defining formula from vol1.hl:18-23,
  `radial_norm r x C ⇔ C ⊆ ball x r ∧
     ∀ u, x + u ∈ C → ∀ t, 0 < t → t * ‖u‖ < r → x + t • u ∈ C`,
  since the repo has no `radial_norm`/`radial` definition and no new
  definitions may be introduced.
- `aff_gt_radial` (vol1.hl:686) and `radial_normball` (vol1.hl:569),
  used by the HOL proof of `dartset_leads_into_fan_radial`, are NOT
  ported; noted per-theorem.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`affGt`/`dartLeadsInto`/`hypermapOfFan` vocabulary,
  so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto14

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 3 元面集的基本基数性质（planarity.hl:14910-15162） -/

/-- `f1_fan` 在真 dart 上没有 2-循环（HOL `properties_of_f1_fan` +
`SIGMA_FAN` 的核心互异性步骤）：`fFanPair (fFanPair d) ≠ d`。

证明：写 `d = (a,b)`，设 `c = inverseSigmaFan b a`。若
`fFanPair (fFanPair d) = d`，则第一分量给 `c = a`，即
`inverseSigmaFan b a = a`；由 `inverse_sigma_fan_comp` 得
`extensionSigmaFan b a = a`，即 `sigmaFan b a = a`。另一方面 `a` 是 `b`
的邻居，且由 `hcard` 知 `setOfEdge b ≠ {a}`，故 `SIGMA_FAN` 给出
`sigmaFan b a ≠ a`，矛盾。 -/
private theorem fFanPair_fFanPair_ne_of_surrounded {x : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    fFanPair x V E (fFanPair x V E d) ≠ d := by
  obtain ⟨a, b⟩ := d
  simp only [dart1OfFan, Set.mem_setOf_eq] at hd
  intro heq
  have hba : {b, a} ∈ E := by rwa [Set.pair_comm]
  have ha_mem : a ∈ setOfEdge b V E :=
    (properties_of_setOfEdge_fan x V E b a hfan).mp hba
  have hc : inverseSigmaFan x V E b a = a := by
    have h1 := congrArg Prod.fst heq
    simpa only [fFanPair] using h1
  have hbV : b ∈ V := hfan.1 (Set.mem_sUnion.mpr ⟨{a, b}, hd, by simp⟩)
  have hne : setOfEdge b V E ≠ {a} := by
    intro h
    have h1 := hcard b hbV
    rw [h] at h1
    simp at h1
  have hsa : sigmaFan x V E b a = a := by
    have hcomp : extensionSigmaFan x V E b a = a := by
      have h2 := congrFun (inverse_sigma_fan_comp hfan ha_mem).2 a
      simpa [Function.comp, hc] using h2
    rwa [extensionSigmaFan, if_neg (by simpa using ha_mem)] at hcomp
  exact (SIGMA_FAN hne hfan ha_mem).2.1 hsa

/-- HOL planarity.hl :14910-14985 `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> 3<= CARD ds
```

证明思路：由 `dartOfFan_eq_dart1_of_surrounded` 消去孤立点；取 face 元素
`ds` 中的 `x'`，迭代 `fFanPair` 得 `y = f1 x'`、`y1 = f1 y`，用
`properties_of_f1_fan`、`SIGMA_FAN`、`remark1_fan` 证 `x',y,y1` 互异且
均在 `ds` 中（`condition_f1_fan_in_face_set`），故 `{x',y,y1} ⊆ ds`，
由 `ds` 有限（`FINITE_FACE_FAN`）与 `Set.ncard_mono` 得 `3 ≤ ds.ncard`。

候选已有引理：
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `fFanPair`（Kepler/Text/Fan.lean:118）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084，HOL `dartset_fully_surrounded_is_non_isolated_fan`）
- `face_representation`（Kepler/Text/Hypermap.lean:2794，HOL `lemma_face_representation`）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `FINITE_FACE_FAN`（Kepler/Text/PlanarityAuto14.lean:693）
- 缺口：`hypermap_of_fan_rep`（fan.hl:2780）、`properties_of_f1_fan`（fan.hl:2797）未以该名移植 -/
theorem CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    3 ≤ ds.ncard := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdf : dartOfFan V E = dart1OfFan V E :=
    dartOfFan_eq_dart1_of_surrounded hfan hcard
  have hfin : ds.Finite := FINITE_FACE_FAN hfan hds
  obtain ⟨d, hdH, hface⟩ := Hypermap.face_representation H hds
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hd_dart1 : d ∈ dart1OfFan V E := by
    change d ∈ (↑H.darts : Set (V3 × V3)) at hdH
    simpa [hdarts] using hdH
  have hd_mem : d ∈ ds := by
    rw [hface]
    exact Hypermap.mem_face_self H d
  let y : V3 × V3 := fFanPair x V E d
  have hy_dart1 : y ∈ dart1OfFan V E := fFanPair_mem_dart1 hfan hd_dart1
  have hy_mem : y ∈ ds :=
    condition_f1_fan_in_face_set (y := y) (y1 := d) hfan rfl hds hdf hd_mem
  let y1 : V3 × V3 := fFanPair x V E y
  have hy1_mem : y1 ∈ ds :=
    condition_f1_fan_in_face_set (y := y1) (y1 := y) hfan rfl hds hdf hy_mem
  have hdy : d ≠ y := fun h => f_fan_no_fix hfan d hd_dart1 h.symm
  have hyy1 : y ≠ y1 := fun h => f_fan_no_fix hfan y hy_dart1 h.symm
  have hdy1 : d ≠ y1 := fun h =>
    fFanPair_fFanPair_ne_of_surrounded hfan hcard hd_dart1 h.symm
  have hsub : ({d, y, y1} : Set (V3 × V3)) ⊆ ds := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact hd_mem
    · exact hy_mem
    · exact hy1_mem
  have hcard3 : ({d, y, y1} : Set (V3 × V3)).ncard = 3 := by
    rw [show ({d, y, y1} : Set (V3 × V3)) = insert d (insert y {y1}) by rfl,
      Set.ncard_insert_of_notMem (by simp [hdy, hdy1]),
      Set.ncard_insert_of_notMem (by simpa using hyy1)]
    simp
  have hle := Set.ncard_le_ncard hsub hfin
  rwa [hcard3] at hle

/-- HOL planarity.hl :14986-15063 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds =3
==> ?f1 f2 f3. ds={f1,f2,f3}/\ f2=f1_fan x V E f1 /\ f3=f1_fan x V E f2
```

证明思路：同 `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN` 构造
`x', y = f1 x', y1 = f1 y`，得 `{x',y,y1} ⊆ ds` 且基数为 3；由
`CARD ds = 3` 与 `Set.eq_of_subset_of_ncard_le`（`CARD_SUBSET_EQ`）得
`ds = {x',y,y1}`，再取 `f1 := x'`、`f2 := y`、`f3 := y1` 即得。

候选已有引理：
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`（本文件上文，HOL :14910）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `FINITE_FACE_FAN`（Kepler/Text/PlanarityAuto14.lean:693）
- `Set.eq_of_subset_of_ncard_le`（Mathlib/Data/Set/Card.lean，HOL `CARD_SUBSET_EQ`） -/
theorem CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    ∃ f1 f2 f3 : V3 × V3, ds = {f1, f2, f3} ∧
      f2 = fFanPair x V E f1 ∧ f3 = fFanPair x V E f2 := by
  sorry

/-- HOL planarity.hl :15064-15113 `lemma_CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds f1 f2 f3.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds =3
/\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ds={f1,f2,f3}
==> f1=f1_fan x V E f3
```

证明思路：`ds = {f1,f2,f3} ⊆ dartOfFan`（`face_subset_darts` +
`dartOfFan_eq_dart1_of_surrounded`）。令 `y1 = f1 f3`；若 `y1 = f2` 用
`properties_of_f1_fan`、`SIGMA_FAN`、`remark1_fan` 与 `hcard` 导出矛盾
（同 3 点轨道论证）；否则 `y1` 与 `f1,f2,f3` 都在 face 中，由
`condition_f1_fan_in_face_set` 与 `CARD ds = 3` 得 `y1 ∈ {f1,f2,f3}`，
只能是 `f1`。

候选已有引理：
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854，HOL `face_subset_dart_fan`）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 的互异部分）
- `fFanPair`（Kepler/Text/Fan.lean:118） -/
theorem lemma_CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {f1 f2 f3 : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (hf12 : fFanPair x V E f1 = f2) (hf23 : fFanPair x V E f2 = f3)
    (hdsf : ds = {f1, f2, f3}) :
    f1 = fFanPair x V E f3 := by
  sorry

/-- HOL planarity.hl :15114-15162 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds =3
==> ?f1 f2 f3. ds={f1,f2,f3}/\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ f1_fan x V E f3 =f1
/\ {pr2 f2, pr2 f3} IN E
/\ {pr2 f3, pr2 f1 } IN E
/\ {pr2 f1, pr2 f2 } IN E
/\ sigma_fan x V E (pr2 f2) (pr2 f3)=pr2 f1
/\ pr2 f3= pr3 f2
/\ pr2 f2= pr3 f1
/\ pr2 f1= pr3 f3
```

证明思路：由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN` 取 `f1,f2,f3`，
由 `lemma_CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN` 补上 `f1 = f1 f3`。
对 `f2 = f1 f1`、`f3 = f1 f2` 用 `properties_of_f1_fan`（未移植，二元组
版由 `fFanPair` 展开）读出 `fFanPair` 的第二分量：`{pr2 f2,pr2 f3} ∈ E`、
`sigma_fan`、`pr2 f3 = pr3 f2` 等，再循环轮换得全部结论。

候选已有引理：
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN`（本文件上文，HOL :14986）
- `lemma_CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN`（本文件上文，HOL :15064）
- `properties_of_setOfEdge`（Kepler/Text/Fan.lean:282）
- `fFanPair`（Kepler/Text/Fan.lean:118）
- 缺口：`properties_of_f1_fan`（fan.hl:2797）未以该名移植 -/
theorem CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1 {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    ∃ f1 f2 f3 : V3 × V3, ds = {f1, f2, f3} ∧
      fFanPair x V E f1 = f2 ∧ fFanPair x V E f2 = f3 ∧ fFanPair x V E f3 = f1 ∧
      {f2.1, f3.1} ∈ E ∧ {f3.1, f1.1} ∈ E ∧ {f1.1, f2.1} ∈ E ∧
      sigmaFan x V E f2.1 f3.1 = f1.1 ∧
      f3.1 = f2.2 ∧ f2.1 = f1.2 ∧ f1.1 = f3.2 := by
  sorry

/-! ## KVQWYDL 系列：3 元面的 aff_gt 与引导集（planarity.hl:15163-15259） -/

/-- HOL planarity.hl :15163-15178 `KVQWYDL_lemma10`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>  aff_gt {x} ({pr2(y)| y IN ds}) = dartset_leads_into_fan x V E ds
```

证明思路：由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 把
`{pr2 y | y ∈ ds}` 写成 `{pr2 f1, pr2 f2, pr2 f3}`，用 `KVQWYDL_lemma1`
得 `aff_gt {x} {pr2 f1,pr2 f2,pr2 f3} = dartLeadsInto ...`；再由
`UNIQUE_DARTSET_LEADS_INTO1_FAN`（在 `f2` 处）把 `dartLeadsInto` 与
`dartsetLeadsIntoFan ds` 等同。

候选已有引理：
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`（本文件上文，HOL :15114）
- `KVQWYDL_lemma1`（Kepler/Text/PlanarityAuto13.lean:368）
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`（Kepler/Text/PlanarityComponent.lean:468）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348） -/
theorem KVQWYDL_lemma10 {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    affGt ({x} : Set V3) ((fun y : V3 × V3 => y.1) '' ds) =
      dartsetLeadsIntoFan x V E ds := by
  sorry

/-- HOL planarity.hl :15179-15191 `IN_D1_FAN_IMP_EDGE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ y IN d_fan(x,V,E) 
==> {pr2 y, pr3 y} IN E
```

编码说明（缺口）：HOL 陈述用 `d_fan`（四元组 dart）；本仓库二元组编码
下 `d_fan` ↦ `dartOfFan`，证明中用 `dartset_fully_surrounded_is_non_isolated_fan`
把 `d_fan` 化为 `d1_fan`，对应 `dartOfFan_eq_dart1_of_surrounded`。

证明思路：`dartOfFan_eq_dart1_of_surrounded` 给 `dartOfFan = dart1OfFan`，
展开 `dart1OfFan` 即得 `{y.1,y.2} ∈ E`（`y.1 = pr2 y`，`y.2 = pr3 y`）。

候选已有引理：
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084，HOL `dartset_fully_surrounded_is_non_isolated_fan`）
- `dart1OfFan`（Kepler/Text/Fan.lean:86） -/
theorem IN_D1_FAN_IMP_EDGE_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hy : y ∈ dartOfFan V E) :
    {y.1, y.2} ∈ E := by
  sorry

/-- HOL planarity.hl :15192-15211 `EQ_PAIR_IMP_EQ_4_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y y1.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ y IN d_fan(x,V,E) 
/\ y1 IN d_fan(x,V,E) 
/\ (pr2 y,pr3 y)= (pr2 y1,pr3 y1)
==> y=y1
```

编码说明（缺口）：HOL `y` 为四元组，结论 `y=y1` 由 `pr2`/`pr3` 相等
加上 `d_fan` 上的约束得到；二元组编码下 `y` 就是 `(pr2 y, pr3 y)`，故
`(y.1,y.2) = (y1.1,y1.2)` 已直接给出 `y = y1`。

证明思路：`dartOfFan_eq_dart1_of_surrounded` 展开 `d_fan`，由
`Prod.ext_iff` 把假设 `(y.1,y.2) = (y1.1,y1.2)` 化为 `y.1 = y1.1 ∧
y.2 = y1.2`，`Prod.ext` 即得。

候选已有引理：
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `Prod.ext`（Mathlib/Data/Prod/Basic.lean） -/
theorem EQ_PAIR_IMP_EQ_4_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y y1 : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hy : y ∈ dartOfFan V E)
    (hy1 : y1 ∈ dartOfFan V E)
    (hp : (y.1, y.2) = (y1.1, y1.2)) :
    y = y1 := by
  sorry

/-- HOL planarity.hl :15212-15242 `KVQWYDL_lemma30`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3

==>  (!y. y IN d_fan(x,V,E) /\ dartset_leads_into_fan x V E ds = dart_leads_into x V E (pr2 y) (pr3 y) 
==> y IN ds)
```

证明思路：由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 取
`ds = {f1,f2,f3}`；`IN_D1_FAN_IMP_EDGE_FAN` 给 `y` 是边
`{pr2 y, pr3 y}`。由 `KVQWYDL_lemma10` 与
`UNIQUE_DARTSET_LEADS_INTO1_FAN` 得 `dart_leads_into (pr2 y) (pr3 y)`
等于 `aff_gt {x} {pr2 f1,pr2 f2,pr2 f3}`，再由 `KVQWYDL_lemma3` 把
`(pr2 y,pr3 y)` 定位到 `(pr2 f1,pr2 f2)`、`(pr2 f2,pr3 f2)`、
`(pr3 f2,pr2 f1)` 之一，最后用 `EQ_PAIR_IMP_EQ_4_FAN` 与 `SET_TAC` 收口。

候选已有引理：
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`（本文件上文，HOL :15114）
- `IN_D1_FAN_IMP_EDGE_FAN`（本文件上文，HOL :15179）
- `KVQWYDL_lemma1`（Kepler/Text/PlanarityAuto13.lean:368）
- `KVQWYDL_lemma3`（Kepler/Text/PlanarityAuto14.lean:629）
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`（Kepler/Text/PlanarityComponent.lean:468）
- `EQ_PAIR_IMP_EQ_4_FAN`（本文件上文，HOL :15192）
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854） -/
theorem KVQWYDL_lemma30 {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    ∀ y : V3 × V3, y ∈ dartOfFan V E →
      dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 → y ∈ ds := by
  sorry

/-- HOL planarity.hl :15243-15259 `KVQWYDL`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3

==>   aff_gt {x} ({pr2(y)| y IN ds}) = dartset_leads_into_fan x V E ds
/\  (!y. y IN d_fan(x,V,E) /\ dartset_leads_into_fan x V E ds = dart_leads_into x V E (pr2 y) (pr3 y) 
==> y IN ds)
```

证明思路：HOL 为 `MESON_TAC[KVQWYDL_lemma30;KVQWYDL_lemma10]`，即两个
合取项分别是 `KVQWYDL_lemma10`（第一项）与 `KVQWYDL_lemma30`（第二项），
直接 `⟨KVQWYDL_lemma10 ..., KVQWYDL_lemma30 ...⟩` 组装。

候选已有引理：
- `KVQWYDL_lemma10`（本文件上文，HOL :15163）
- `KVQWYDL_lemma30`（本文件上文，HOL :15212） -/
theorem KVQWYDL {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    affGt ({x} : Set V3) ((fun y : V3 × V3 => y.1) '' ds) =
        dartsetLeadsIntoFan x V E ds ∧
      ∀ y : V3 × V3, y ∈ dartOfFan V E →
        dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 → y ∈ ds := by
  sorry

/-! ## 3 元面引导集的径向性（planarity.hl:15260-15279） -/

/-- HOL planarity.hl :15260-15279 `dartset_leads_into_fan_radial`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds r.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
/\ r> &0
==>   radial_norm r x ((dartset_leads_into_fan x V E ds) INTER normball  x r) 
```

编码说明（缺口）：`normball x r` 用 Mathlib `Metric.ball x r`；
`radial_norm` 未移植，按 vol1.hl:18-23 就地展开为
`C ⊆ Metric.ball x r ∧ ∀ u, x + u ∈ C → ∀ t, 0 < t → t * ‖u‖ < r →
x + t • u ∈ C`，其中 `C = dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r`。

证明思路：由 `KVQWYDL_lemma10` 把 `dartsetLeadsIntoFan ds` 换为
`aff_gt {x} {pr2 f1,pr2 f2,pr2 f3}`（`CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
给出 `f1,f2,f3`），再用 `aff_gt_radial`（vol1.hl:686，未移植）与
`remark1_fan` 得径向性；`hr : 0 < r` 用于满足 `aff_gt_radial` 的半径条件。

候选已有引理：
- `KVQWYDL_lemma10`（本文件上文，HOL :15163）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`（本文件上文，HOL :15114）
- `Metric.ball`（Mathlib/Topology/MetricSpace/Basic.lean，HOL `normball`）
- 缺口：`aff_gt_radial`（vol1.hl:686）、`radial_norm`（vol1.hl:18）未移植 -/
theorem dartset_leads_into_fan_radial {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {r : ℝ}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (hr : 0 < r) :
    (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
      ∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
        ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
          x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r := by
  sorry

end Kepler.Text
