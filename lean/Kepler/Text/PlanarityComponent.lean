/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18g.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18g of block 18, planarity.hl:10807-11106): the
connected-component / dartset-leads-into layer
- `CONNECTED_COMPONENT_OF_SUBSET` (10807) — SKIPPED, see below
- `connected_component_of_faces_fan` (10812)
- `dart_leads_into1` / `dartset_leads_into` defs (10915/10921) — already
  ported as `dartLeadsInto1` / `dartsetLeadsInto`
  (Kepler/Text/Fan.lean:204/210)
- `dartset_leads_into_fan` def (10978) — ported below as
  `dartsetLeadsIntoFan` (required by 7 of the statements)
- `exists_dartset_leads_into_fan` (10927)
- `DARTSET_LEADS_INTO_FAN` (10984)
- `UNIQUE_DARTSET_LEADS_INTO_FAN` (11006)
- `equality_dart_leads_into` (11028)
- `UNIQUE_DARTSET_LEADS_INTO1_FAN` (11043)
- `exists_point_dart_leads_into_fan` (11059)
- `dartset_leads_into_is_topological_component_yfan` (11081)
- `dartset_leads_into_subset_yfan` (11094)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings)
designed by glm-5.3, proofs filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `CONNECTED_COMPONENT_OF_SUBSET` (10807) is Mathlib-general and SKIPPED:
  HOL `connected_component s x y` ↔ `x ∈ connectedComponentIn s y`
  (Kepler/Text/TopologyFan.lean:4088 convention), and the statement is
  exactly `connectedComponentIn_mono`
  (Mathlib/Topology/Connected/Basic.lean:635). Similarly HOL
  `CONNECTED_COMPONENT_SUBSET` ↔ `connectedComponentIn_subset`
  (Mathlib/Topology/Connected/Basic.lean:529).
- HOL `hypermap1_of_fanx (x,V,E)` (quadruple-dart hypermap on `d1_fan`) is
  NOT ported. Closest encoding: the pair-dart fan hypermap
  `hypermapOfFan x V E hfan : Hypermap (V3 × V3)`
  (Kepler/Text/Fan.lean:1169, darts = `dart1OfFan V E`). The two hypermaps
  are canonically isomorphic via contraction
  `contractedDart (y0,v,u,w1) = (v,u)` (Kepler/Text/Fan.lean:104, HOL
  `contracted_dart`) / `extendedDart` (Kepler/Text/Fan.lean:99), and face
  sets correspond under it; every theorem in this slice only uses the
  contracted dart of each element. Hence `ds IN face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with `ds : Set (V3 × V3)`,
  and `pr2 y, pr3 y` as `y.1, y.2`.
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, e.g. Kepler/Text/PlanarityAngle.lean:821).
- HOL `dart_leads_into x V E v u` ↔ `dartLeadsInto x V E v u`
  (Kepler/Text/TopologyFan.lean:4179, ε-选择算子 via `Classical.epsilon`).
- Not yet ported proof dependencies (needed by the worker pool; pair-dart
  analogues must be developed): `FACE_FAN_NOT_EMPTY` (fan.hl:2376),
  `properties_of_elements_in_face_fully_surroundedfan` (fan.hl:2857),
  `hypermap_of_fan_rep` (fan.hl:2780), `id_power_enf_fan` (fan.hl:2651),
  `into_domain_power_efn_fan` (fan.hl:2694),
  `into_domain1_power_efn_fan` (fan.hl:2726),
  `properties_of_f1_fan` (fan.hl:2797).
-/

import Kepler.Text.PlanarityAngle

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 面上 dart_leads_into 的一致性（planarity.hl:10812-10976） -/

/-- 不共线 ⇒ `x` 不属于 `{v,w}`（`Disjoint {x} {v,w}`）。 -/
private theorem disjoint_of_not_collinear3_component {x v w : V3}
    (hnc : ¬ Collinear3 x v w) :
    Disjoint ({x} : Set V3) {v, w} := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.singleton_inter_eq_empty]
  intro hmem
  rcases Set.mem_insert_iff.mp hmem with he | he
  · exact hnc (by rw [he]; exact collinear3_of_eq rfl)
  · exact hnc (by rw [Set.mem_singleton_iff.mp he]; exact collinear3_pair_left rfl)

/-- 三点不共线时 `affGt {x} {v,w}` 是凸集（HOL `CONVEX_AFF_GT`）：由
`aff_gt_1_2` 写成开三角形的显式组合，凸组合的系数仍严格正。 -/
private theorem convex_affGt_single_pair {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    Convex ℝ (affGt {x} {v, w}) := by
  rw [aff_gt_1_2 (disjoint_of_not_collinear3_component hnc), convex_iff_forall_pos]
  intro y hy z hz a b ha hb hab
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hyeq⟩ := hy
  obtain ⟨s1, s2, s3, hs2, hs3, hssum, hzeq⟩ := hz
  refine ⟨a * t1 + b * s1, a * t2 + b * s2, a * t3 + b * s3,
    add_pos (mul_pos ha ht2) (mul_pos hb hs2),
    add_pos (mul_pos ha ht3) (mul_pos hb hs3), ?_, ?_⟩
  · nlinarith [hsum, hssum, hab]
  · rw [hyeq, hzeq]
    module

/-- HOL planarity.hl :10812-10913 `connected_component_of_faces_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>
dart_leads_into x V E v u = dart_leads_into x V E u w
```

证明思路：对 (v,u) 与 (u,w) 各用 `exists_leads_into_fan` 得阈值刻画；
取 h00 = min h' (π/2)/2、h1 = min (min h'' h''') h'''' /2、h2 = min h (π/2)/2，
由 `exists_rw_dart_inter_aff_gt1_fan`（dart (v,u) 侧）与
`exists_rw_dart_inter_aff_gt_fan`（dart (u,w) 侧）取公共弦带
`aff_gt {x} {v, (1-h1)•u + h1•w}` 内的交点 y、y'；
`aff_gt` 凸（HOL CONVEX_AFF_GT）故连通，y、y' 同属其一个连通分量，
又 `fan_run_in_small_is_subset_yfan` 保证该 aff_gt（小 h1 时）⊆ yfan，
经 `connectedComponentIn_mono`（= HOL CONNECTED_COMPONENT_OF_SUBSET，
10807，Mathlib 已有故本批不重复移植）把分量粘合，得刻画集相等 U = U'；
最后两次 `unique_dart_leads_into` 收口。

候选已有引理：
- `exists_leads_into_fan`（Kepler/Text/TopologyFan.lean:4191）
- `unique_dart_leads_into`（Kepler/Text/TopologyFan.lean:4244）
- `exists_rw_dart_inter_aff_gt_fan`（Kepler/Text/PlanarityAngle.lean:817）
- `exists_rw_dart_inter_aff_gt1_fan`（Kepler/Text/PlanarityAngle.lean:2173）
- `fan_run_in_small_is_subset_yfan`（Kepler/Text/Planarity.lean:2588）
- `connectedComponentIn_mono`（Mathlib/Topology/Connected/Basic.lean:635） -/

theorem connected_component_of_faces_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    dartLeadsInto x V E v u = dartLeadsInto x V E u w := by
  obtain ⟨U, h, hh0, hspec⟩ := exists_leads_into_fan hfan hvu
  obtain ⟨U', h', hh'0, hspec'⟩ := exists_leads_into_fan hfan huw
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  -- 公共小角度 s0：同时小于两侧阈值与 π/2
  set s0 : ℝ := min (min h h') (Real.pi / 2) / 2 with hs0def
  have hXpos : 0 < min (min h h') (Real.pi / 2) :=
    lt_min (lt_min hh0 hh'0) (by positivity)
  have hs0pos : 0 < s0 := by rw [hs0def]; exact div_pos hXpos two_pos
  have hs0lt_h : s0 < h := by
    rw [hs0def]
    exact lt_of_lt_of_le (half_lt_self hXpos)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hs0lt_h' : s0 < h' := by
    rw [hs0def]
    exact lt_of_lt_of_le (half_lt_self hXpos)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hs0lt_pi2 : s0 < Real.pi / 2 := by
    rw [hs0def]
    exact lt_of_lt_of_le (half_lt_self hXpos) (min_le_right _ _)
  -- 两侧弦带阈值与 yfan 阈值
  obtain ⟨H1, hH10, hH1⟩ :=
    exists_rw_dart_inter_aff_gt1_fan hfan hvu huw hsigma hs0pos hs0lt_pi2 hfan80 hcard
  obtain ⟨H2, hH20, hH2⟩ :=
    exists_rw_dart_inter_aff_gt_fan hfan hvu huw hsigma hfan80 hcard
  obtain ⟨H3, hH30, hH3le1, hH3⟩ :=
    fan_run_in_small_is_subset_yfan hfan hvu huw hθ0 hθπ hsigma
  -- 公共弦参数 h1：同时小于三个阈值
  set h1 : ℝ := min (min H1 H2) H3 / 2 with hh1def
  have hYpos : 0 < min (min H1 H2) H3 :=
    lt_min (lt_min hH10 hH20) hH30
  have hh1pos : 0 < h1 := by rw [hh1def]; exact div_pos hYpos two_pos
  have hh1lt_H1 : h1 < H1 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hYpos)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hh1lt_H2 : h1 < H2 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hYpos)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh1lt_H3 : h1 < H3 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hYpos) (min_le_right _ _)
  have hh1lt_one : h1 < 1 := lt_of_lt_of_le hh1lt_H3 hH3le1
  -- 公共凸区域 A = aff_gt {x} {v, (1-h1)u + h1 w}
  set A : Set V3 := affGt {x} {v, (1 - h1) • u + h1 • w} with hA
  have hncA : ¬ Collinear3 x v ((1 - h1) • u + h1 • w) :=
    not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ h1 hh1pos hh1lt_one
  have hconvA : Convex ℝ A := by
    rw [hA]
    exact convex_affGt_single_pair hncA
  have hpreA : IsPreconnected A := hconvA.isPreconnected
  -- 两侧各取 A 内的交点
  have hne_y : (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s0) ∩ A) ≠ ∅ := by
    rw [hA]
    exact hH2 h1 hh1pos hh1lt_H2 s0 hs0pos hs0lt_pi2
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne_y
  have hyrw : y ∈ rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s0) := hy.1
  have hyA : y ∈ A := hy.2
  have hne_y' : (rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos s0) ∩ A) ≠ ∅ := by
    rw [hA]
    exact hH1 h1 hh1pos hh1lt_H1
  obtain ⟨y', hy'⟩ := Set.nonempty_iff_ne_empty.mpr hne_y'
  have hy'rw : y' ∈ rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos s0) := hy'.1
  have hy'A : y' ∈ A := hy'.2
  have hAyfan : A ⊆ yfan x V E := by
    rw [hA]
    exact hH3 h1 hh1pos hh1lt_H3
  -- A 预连通且含于 yfan ⇒ y 与 y' 落在 yfan 的同一连通分量
  have hy'comp : y' ∈ connectedComponentIn (yfan x V E) y :=
    (hpreA.subset_connectedComponentIn hyA hAyfan) hy'A
  have hcomp : connectedComponentIn (yfan x V E) y =
      connectedComponentIn (yfan x V E) y' :=
    connectedComponentIn_eq hy'comp
  obtain ⟨-, hUy⟩ := hspec s0 y hs0pos hs0lt_h hyrw
  obtain ⟨-, hU'y'⟩ := hspec' s0 y' hs0pos hs0lt_h' hy'rw
  have hUU' : U = U' := by rw [← hUy, hcomp, hU'y']
  exact (unique_dart_leads_into hfan hvu U ⟨h, hh0, hspec⟩).trans
    (hUU'.trans (unique_dart_leads_into hfan huw U' ⟨h', hh'0, hspec'⟩).symm)

/-- `connected_component_of_faces_fan` 的 `fFanPair` 步进版：同面上相邻
dart `d`、`fFanPair d` 的 `dartLeadsInto` 相等。 -/
private theorem dartLeadsInto_fFanPair {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    dartLeadsInto x V E (fFanPair x V E d).1 (fFanPair x V E d).2 =
      dartLeadsInto x V E d.1 d.2 := by
  rcases d with ⟨v, u⟩
  have hvu : {v, u} ∈ E := hd
  have hba : {u, v} ∈ E := by
    rwa [Set.pair_comm]
  have hσ1 : sigmaFan x V E u (inverse1SigmaFan x V E u v) = v :=
    (INVERSE1_SIGMA_FAN hfan).2.1 v hba
  have hσ : sigmaFan x V E u (inverseSigmaFan x V E u v) = v := by
    rwa [inverse_sigma_fan_eq_inverse1 hfan hba] at hσ1
  have huw : {u, inverseSigmaFan x V E u v} ∈ E := by
    simpa [dart1OfFan, fFanPair] using (fFanPair_mem_dart1 hfan hd)
  simpa [fFanPair] using
    (connected_component_of_faces_fan hfan hvu huw hσ hcard hfan80).symm

/-- `hypermapOfFan` 的 faceMap 在 dart1OfFan 上即 `fFanPair`。 -/
private theorem hypermapOfFan_faceMap_eq (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- HOL planarity.hl :10927-10976 `exists_dartset_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
?s:real^3->bool. !y. y IN ds==> s= dart_leads_into x V E (pr2 y) (pr3 y)
```

编码说明：`ds IN face_set(hypermap1_of_fanx (x,V,E))` 用二元组 dart 超图
编码为 `ds ∈ (hypermapOfFan x V E hfan).faceSet`（见文件头）；`pr2 y`/`pr3 y`
↦ `y.1`/`y.2`（收缩 `contractedDart`，Kepler/Text/Fan.lean:104）。

证明思路：由 `face_representation` 取 dart x' 使 ds 为 faceMap 轨道
（二元组版即 `fFanPair` 迭代轨道）；见证取
`s := dartLeadsInto x V E x'.1 x'.2`，沿轨道归纳：每步
d ↦ fFanPair d = (d.2, inverseSigmaFan x V E d.2 d.1)，边链与 σ 关系
（HOL 的 `properties_of_f1_fan` / `into_domain_power_efn_fan` 的二元组
替代品）使 `connected_component_of_faces_fan` 把 dart_leads_into 相等性
从 x' 传递到轨道上每个 y。

候选已有引理：
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `connected_component_of_faces_fan`（本文件上文）
- `fFanPair`（Kepler/Text/Fan.lean:118）、`inverseSigmaFan`
  （Kepler/Text/Fan.lean:79）、`sigma_fan_in_setOfEdge`
  （Kepler/Text/Fan.lean:326）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169） -/
theorem exists_dartset_leads_into_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ s : Set V3, ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2 := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  obtain ⟨d, hd, hds⟩ := Hypermap.face_representation H hds
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hmem : ∀ p : V3 × V3, p ∈ H.darts → p ∈ dart1OfFan V E := by
    intro p hp
    change p ∈ (↑H.darts : Set (V3 × V3)) at hp
    simpa [hdarts] using hp
  have hfm : ∀ p : V3 × V3, p ∈ dart1OfFan V E →
      H.faceMap p = fFanPair x V E p := by
    intro p hp
    change (hypermapOfFan x V E hfan).faceMap p = fFanPair x V E p
    exact hypermapOfFan_faceMap_eq hfan hp
  have hstep : ∀ p : V3 × V3, p ∈ dart1OfFan V E →
      dartLeadsInto x V E (H.faceMap p).1 (H.faceMap p).2 =
        dartLeadsInto x V E p.1 p.2 := by
    intro p hp
    rw [hfm p hp]
    exact dartLeadsInto_fFanPair hfan hcard hfan80 hp
  refine ⟨dartLeadsInto x V E d.1 d.2, ?_⟩
  intro y hy
  have hc : y ∈ H.face d := by
    simpa [hds] using hy
  rcases (by simpa [Hypermap.face, orbitMap] using hc :
    ∃ n : ℕ, (H.faceMap ^ n) d = y) with ⟨n, hn⟩
  have hmain : ∀ n : ℕ,
      dartLeadsInto x V E ((H.faceMap ^ n) d).1 ((H.faceMap ^ n) d).2 =
        dartLeadsInto x V E d.1 d.2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hp : (H.faceMap ^ k) d ∈ H.darts := by
          exact H.faceMap_permutes.pow_apply_mem k hd
        have hp1 : (H.faceMap ^ k) d ∈ dart1OfFan V E := hmem _ hp
        have hs : dartLeadsInto x V E (H.faceMap ((H.faceMap ^ k) d)).1
            (H.faceMap ((H.faceMap ^ k) d)).2 =
            dartLeadsInto x V E ((H.faceMap ^ k) d).1 ((H.faceMap ^ k) d).2 :=
          hstep _ hp1
        rw [pow_succ', Equiv.Perm.mul_apply, hs, ih]
  have hkey := hmain n
  rw [hn] at hkey
  exact hkey.symm

/-! ## dartset_leads_into_fan 的 ε-定义与其刻画（planarity.hl:10978-11106） -/

/-- HOL planarity.hl :10978-10981 定义 `dartset_leads_into_fan`（原样移植，
非新发明；HOL `@s` 选择算子 ↔ `Classical.epsilon`，同
Kepler/Text/Fan.lean:210 的 `dartsetLeadsInto` 风格）。

HOL 原文：
```
dartset_leads_into_fan x V E ds =
    @s. (!y. (y IN ds) ==> (s = dart_leads_into x V E (pr2 y) (pr3 y)))
```

编码说明：dart 采用二元组（见文件头），故 `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；
`dart_leads_into` ↦ `dartLeadsInto`（Kepler/Text/TopologyFan.lean:4179）。 -/
noncomputable def dartsetLeadsIntoFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) : Set V3 :=
  Classical.epsilon (fun s => ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2)

/-- HOL planarity.hl :10984-11004 `DARTSET_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
(!y. y IN ds==> dartset_leads_into_fan x V E ds= dart_leads_into x V E (pr2 y) (pr3 y))
```

证明思路：`dartsetLeadsIntoFan` 是性质
`P s := ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2` 的 ε-选择；
`exists_dartset_leads_into_fan` 给出满足者 s，用
`Classical.epsilon_spec` 直接把刻画搬到 ε-值上（对应 HOL 的
ONCE_REWRITE + SELECT_ELIM）。

候选已有引理：
- `exists_dartset_leads_into_fan`（本文件上文）
- `Classical.epsilon_spec`（Mathlib/Classical.lean）
- `dartLeadsInto_spec` 的同型用法（Kepler/Text/TopologyFan.lean:4233） -/
theorem DARTSET_LEADS_INTO_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∀ y ∈ ds, dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 := by
  have h := exists_dartset_leads_into_fan hfan hcard hfan80 hds
  simpa [dartsetLeadsIntoFan] using (Classical.epsilon_spec h)

/-- HOL planarity.hl :11006-11026 `UNIQUE_DARTSET_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds s.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ (!y. y IN ds==> s= dart_leads_into x V E (pr2 y) (pr3 y))
==> dartset_leads_into_fan x V E ds= s
```

证明思路：面非空（HOL `FACE_FAN_NOT_EMPTY` fan.hl:2376 未移植；二元组
编码下用 `face_representation` + `mem_orbitMap_self` 即得 ds ≠ ∅），
取 y ∈ ds，由 `DARTSET_LEADS_INTO_FAN` 得
dartsetLeadsIntoFan ds = dartLeadsInto y，再与假设 hs 在 y 处相等。

候选已有引理：
- `DARTSET_LEADS_INTO_FAN`（本文件上文）
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `mem_orbitMap_self`（Kepler/Text/Hypermap.lean:713） -/
theorem UNIQUE_DARTSET_LEADS_INTO_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} (s : Set V3)
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hs : ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2) :
    dartsetLeadsIntoFan x V E ds = s := by
  obtain ⟨y, hy, hds_eq⟩ := Hypermap.face_representation (hypermapOfFan x V E hfan) hds
  have hyds : y ∈ ds := by rw [hds_eq]; exact Hypermap.mem_face_self _ y
  have h1 := DARTSET_LEADS_INTO_FAN hfan hcard hfan80 hds y hyds
  have h2 := hs y hyds
  rw [h2, h1]

/-- HOL planarity.hl :11028-11041 `equality_dart_leads_into`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y y1.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ y IN ds /\ y1 IN ds

==>dart_leads_into x V E (pr2 y) (pr3 y)= dart_leads_into x V E (pr2 y1) (pr3 y1)
```

证明思路：`exists_dartset_leads_into_fan` 给出公共 s，
在 y 与 y1 两处实例化即得两端都等于 s。

候选已有引理：
- `exists_dartset_leads_into_fan`（本文件上文） -/
theorem equality_dart_leads_into {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {y y1 : V3 × V3}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) (hy1 : y1 ∈ ds) :
    dartLeadsInto x V E y.1 y.2 = dartLeadsInto x V E y1.1 y1.2 := by
  rcases exists_dartset_leads_into_fan hfan hcard hfan80 hds with ⟨s, hs⟩
  rw [← hs y hy, ← hs y1 hy1]

/-- HOL planarity.hl :11043-11057 `UNIQUE_DARTSET_LEADS_INTO1_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds s y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ y IN ds /\ s= dart_leads_into x V E (pr2 y) (pr3 y)
==> dartset_leads_into_fan x V E ds= s
```

证明思路：先用 `equality_dart_leads_into` 把假设强化为
`∀ y' ∈ ds, s = dartLeadsInto y'`，再套
`UNIQUE_DARTSET_LEADS_INTO_FAN`。

候选已有引理：
- `equality_dart_leads_into`、`UNIQUE_DARTSET_LEADS_INTO_FAN`
  （本文件上文） -/
theorem UNIQUE_DARTSET_LEADS_INTO1_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y : V3 × V3} (s : Set V3)
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) (hs : s = dartLeadsInto x V E y.1 y.2) :
    dartsetLeadsIntoFan x V E ds = s := by
  refine UNIQUE_DARTSET_LEADS_INTO_FAN s hfan hcard hfan80 hds ?_
  intro y' hy'
  rw [hs]
  exact equality_dart_leads_into hfan hcard hfan80 hds hy hy'

/-- HOL planarity.hl :11059-11079 `exists_point_dart_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> ?y. y IN ds /\ dartset_leads_into_fan x V E ds =dart_leads_into x V E (pr2 y) (pr3 y)
```

证明思路：面非空取 y ∈ ds（同上，`face_representation` +
`mem_orbitMap_self` 替代未移植的 `FACE_FAN_NOT_EMPTY`），对
s := dartLeadsInto x V E y.1 y.2 用 `UNIQUE_DARTSET_LEADS_INTO1_FAN`。

候选已有引理：
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`（本文件上文）
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `mem_orbitMap_self`（Kepler/Text/Hypermap.lean:713） -/
theorem exists_point_dart_leads_into_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ y ∈ ds, dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 := by
  obtain ⟨d, _hd, hd_eq⟩ := Hypermap.face_representation (hypermapOfFan x V E hfan) hds
  have hd_mem : d ∈ ds := by rw [hd_eq]; exact Hypermap.mem_face_self _ d
  exact ⟨d, hd_mem, UNIQUE_DARTSET_LEADS_INTO1_FAN _ hfan hcard hfan80 hds hd_mem rfl⟩

/-- HOL planarity.hl :11081-11092 `dartset_leads_into_is_topological_component_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> dartset_leads_into_fan x V E ds IN topological_component_yfan (x,V,E)
```

证明思路：`exists_point_dart_leads_into_fan` 取 y ∈ ds 使
dartsetLeadsIntoFan ds = dartLeadsInto y；y ∈ 轨道 ⊆ darts =
dart1OfFan 给 {y.1, y.2} ∈ E（替代未移植的
`properties_of_elements_in_face_fully_surroundedfan` fan.hl:2857），
再用 `dart_leads_into_mem_topologicalComponentYfan`
（HOL 名 `dart_leads_into_fan_in_topological_component_yfan`）。

候选已有引理：
- `exists_point_dart_leads_into_fan`（本文件上文）
- `dart_leads_into_mem_topologicalComponentYfan`
  （Kepler/Text/TopologyFan.lean:4280）
- `orbitMap_subset_of_permutesOn`（Kepler/Text/Hypermap.lean:721）、
  `dart1OfFan`（Kepler/Text/Fan.lean:86） -/
theorem dartset_leads_into_is_topological_component_yfan {x : V3}
    {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E := by
  obtain ⟨y, hy, heq⟩ := exists_point_dart_leads_into_fan hfan hcard hfan80 hds
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hy_darts : y ∈ H.darts := by
    have hyU : y ∈ ⋃₀ H.faceSet := Set.mem_sUnion.mpr ⟨ds, hds, hy⟩
    have hsu := sUnion_setOfOrbits H.faceMap_permutes
    change y ∈ (↑H.darts : Set (V3 × V3))
    rw [hsu]
    simpa [Hypermap.faceSet] using hyU
  have hy_dart1 : y ∈ dart1OfFan V E := by
    have : y ∈ (↑H.darts : Set (V3 × V3)) := hy_darts
    rwa [hdarts] at this
  have hE : {y.1, y.2} ∈ E := by
    simpa [dart1OfFan] using hy_dart1
  rw [heq]
  exact dart_leads_into_mem_topologicalComponentYfan (v := y.1) (u := y.2) hfan hE

/-- HOL planarity.hl :11094-11106 `dartset_leads_into_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds:real^3#real^3#real^3#real^3->bool.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
dartset_leads_into_fan x V E ds SUBSET yfan (x,V,E)
```

证明思路：展开 `topologicalComponentYfan`（Fan.lean:199），由
`dartset_leads_into_is_topological_component_yfan` 得
dartsetLeadsIntoFan ds = connectedComponentIn (yfan x V E) b（b ∈ yfan），
再用 `connectedComponentIn_subset`（= HOL CONNECTED_COMPONENT_SUBSET）
得 ⊆ yfan x V E。

候选已有引理：
- `dartset_leads_into_is_topological_component_yfan`（本文件上文）
- `connectedComponentIn_subset`
  （Mathlib/Topology/Connected/Basic.lean:529） -/
theorem dartset_leads_into_subset_yfan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    dartsetLeadsIntoFan x V E ds ⊆ yfan x V E := by
  have hmem := dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds
  rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
  obtain ⟨b, _hb, heq⟩ := hmem
  rw [← heq]
  exact connectedComponentIn_subset (yfan x V E) b

end Kepler.Text
