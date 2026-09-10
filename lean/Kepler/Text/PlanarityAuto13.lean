/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18q.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18q of block 18, planarity.hl:14125-14504):
- `aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3` (14125)
- `cut_aff_gt_1_3_connected` (14252)
- `AFF_GE_SUBSET_XFAN` (14298)
- `notcoplanar_4point_aff_gt_3_1_not_empty` (14309)
- `notcoplanar_4point_aff_gt_1_3_not_empty` (14350)
- `KVQWYDL_lemma1` (14360)
- `point_in_yfan_is_not_inv_fan` (14401)
- `point_in_aff_ge_1_1` (14418)
- `POINT_IN_AFF_GE_IMP_IN_EDGE` (14441)
- `POINT_IN_CLOSURE_AFF_GT_1_2` (14473)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42).
- HOL `coplanar` ↔ `Coplanar` (Kepler/Geom/Coplanar.lean:23).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `yfan`/`xfan` ↔ `yfan`/`xfan`
  (Kepler/Text/Fan.lean:158/154); HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179); HOL
  `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199).
- HOL `connected s` ↔ Mathlib `IsPreconnected s` (repo convention: HOL
  空集连通，Mathlib `IsConnected` 额外要求 `Nonempty`, cf.
  Kepler/Text/PlanarityAuto7.lean:29 与 Kepler/Text/TopologyFan.lean:4086).
- HOL `closure s` ↔ `closure s` (Mathlib `TopologicalSpace`，`open scoped
  Topology`)；HOL `CLOSURE_APPROACHABLE` 的对应是 Mathlib
  `Metric.mem_closure_iff`。
- HOL `AFF_GE_EQ_AFFINE_HULL`（POINT_IN_AFF_GE_IMP_IN_EDGE 的证明内部使用）
  未以该名移植；最接近的是 `affGe {x} ∅ = {x}` 相关引理
  （Kepler/Text/TopologyFan.lean:2790 注释）与 `AFFINE_HULL_1`
  （Kepler/Text/Planarity.lean:4459）。本批定理陈述不含该引理。
- 本批 10 条定理均依赖仓库自定义的 `affGe`/`xfan`/`FAN`/`dartLeadsInto`
  等概念，非 Mathlib 通用命题，故无跳过项。
-/

import Kepler.Text.PlanarityAuto12

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## aff_ge 1-3 的边并分解与切割连通性（planarity.hl:14125-14297） -/

/-- HOL planarity.hl :14125-14251
`aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3`

HOL 原文：
```
!x  v u w:real^3.
~coplanar {x,v,u,w}
==>
aff_ge {x} {v,u,w}= aff_ge {x} {v,u} UNION aff_ge {x} {u,w} UNION aff_ge {x} {w,v} UNION  aff_gt {x} {v,u,w}
```

证明思路：由 `notcoplanar_disjoints` 得三组 `Disjoint {x} {·,·}`，用
`AFF_GE_1_3` 把左侧展开为非负组合 `t1•x+t2•v+t3•u+t4•w`。按 `t2,t3,t4`
中哪些为零分类：恰有一个为零时落入对应的 `aff_ge {x} {·,·}`
（`AFF_GE_1_2`），全为正时落入 `aff_gt {x} {v,u,w}`（`AFF_GT_1_3`）；
反方向由各 `aff_ge`/`aff_gt` 的系数直接嵌入。HOL 即对
`EXTENSION;IN_ELIM_THM;UNION` 展开后 `REAL_ARITH`。

候选已有引理：
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `notcoplanar_disjoint`（Kepler/Text/PlanarityAuto11.lean:1220）
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `AFF_GE_1_3`（Kepler/Text/PlanarityAuto11.lean:1136）
- `AFF_GT_1_3`（Kepler/Text/PlanarityAuto11.lean:1029） -/
theorem aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGe ({x} : Set V3) ({v, u, w} : Set V3) =
      affGe ({x} : Set V3) ({v, u} : Set V3) ∪
        affGe ({x} : Set V3) ({u, w} : Set V3) ∪
        affGe ({x} : Set V3) ({w, v} : Set V3) ∪
        affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩ :=
    notcoplanar_disjoints x v u w hcop
  apply le_antisymm
  · intro y hy
    rw [AFF_GE_1_3 x v u w hd4] at hy
    simp only [Set.mem_setOf_eq] at hy
    obtain ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, hy⟩ := hy
    by_cases h2 : t2 = 0
    · have hmem : y ∈ affGe ({x} : Set V3) ({u, w} : Set V3) := by
        rw [aff_ge_1_2 (x := x) (v := u) (u := w) hd7]
        exact ⟨t1, t3, t4, ht3, ht4, by linarith, by rw [hy, h2]; module⟩
      simp only [Set.mem_union]
      tauto
    · by_cases h3 : t3 = 0
      · have hmem : y ∈ affGe ({x} : Set V3) ({w, v} : Set V3) := by
          rw [aff_ge_1_2 (x := x) (v := w) (u := v) hd8]
          exact ⟨t1, t4, t2, ht4, ht2, by linarith, by rw [hy, h3]; module⟩
        simp only [Set.mem_union]
        tauto
      · by_cases h4 : t4 = 0
        · have hmem : y ∈ affGe ({x} : Set V3) ({v, u} : Set V3) := by
            rw [aff_ge_1_2 (x := x) (v := v) (u := u) hd6]
            exact ⟨t1, t2, t3, ht2, ht3, by linarith, by rw [hy, h4]; module⟩
          simp only [Set.mem_union]
          tauto
        · have hmem : y ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
            rw [AFF_GT_1_3 x v u w hd4]
            exact ⟨t1, t2, t3, t4, lt_of_le_of_ne ht2 (Ne.symm h2),
              lt_of_le_of_ne ht3 (Ne.symm h3), lt_of_le_of_ne ht4 (Ne.symm h4),
              hsum, hy⟩
          simp only [Set.mem_union]
          tauto
  · apply Set.union_subset
    · apply Set.union_subset
      · apply Set.union_subset
        · intro y hy
          rw [aff_ge_1_2 (x := x) (v := v) (u := u) hd6] at hy
          simp only [Set.mem_setOf_eq] at hy
          obtain ⟨a1, a2, a3, ha2, ha3, hsum, hy⟩ := hy
          rw [AFF_GE_1_3 x v u w hd4]
          simp only [Set.mem_setOf_eq]
          exact ⟨a1, a2, a3, 0, ha2, ha3, le_refl 0, by linarith, by rw [hy]; module⟩
        · intro y hy
          rw [aff_ge_1_2 (x := x) (v := u) (u := w) hd7] at hy
          simp only [Set.mem_setOf_eq] at hy
          obtain ⟨b1, b2, b3, hb2, hb3, hsum, hy⟩ := hy
          rw [AFF_GE_1_3 x v u w hd4]
          simp only [Set.mem_setOf_eq]
          exact ⟨b1, 0, b2, b3, le_refl 0, hb2, hb3, by linarith, by rw [hy]; module⟩
      · intro y hy
        rw [aff_ge_1_2 (x := x) (v := w) (u := v) hd8] at hy
        simp only [Set.mem_setOf_eq] at hy
        obtain ⟨c1, c2, c3, hc2, hc3, hsum, hy⟩ := hy
        rw [AFF_GE_1_3 x v u w hd4]
        simp only [Set.mem_setOf_eq]
        exact ⟨c1, c3, 0, c2, hc3, le_refl 0, hc2, by linarith, by rw [hy]; module⟩
    · intro y hy
      rw [AFF_GT_1_3 x v u w hd4] at hy
      simp only [Set.mem_setOf_eq] at hy
      obtain ⟨d1, d2, d3, d4, hd2, hd3, hd4', hsum, hy⟩ := hy
      rw [AFF_GE_1_3 x v u w hd4]
      simp only [Set.mem_setOf_eq]
      exact ⟨d1, d2, d3, d4, le_of_lt hd2, le_of_lt hd3, le_of_lt hd4', hsum, hy⟩

/-- `affGt s t ⊆ affGe s t`：严格正系数组合是非负组合。 -/
private theorem affGt_subset_affGe_cut {s t : Set V3} : affGt s t ⊆ affGe s t := by
  intro z hz
  simp only [affGt, affGe, Set.mem_setOf_eq, Affsign] at hz ⊢
  obtain ⟨f, h, hv, ht, hsum⟩ := hz
  exact ⟨f, h, hv, fun w hw => le_of_lt (ht w hw), hsum⟩

/-- HOL planarity.hl :14252-14297 `cut_aff_gt_1_3_connected`

HOL 原文：
```
!x y z v u w:real^3 s:real^3->bool.
        connected s /\ ~coplanar {x,v,u,w} 
        /\  y IN s /\ z IN s /\ y IN aff_gt {x} {v,u,w} /\ ~(z IN aff_gt {x} {v,u,w})
        ==> ?t. t IN s /\ t IN aff_ge {x} {v,u} UNION aff_ge {x} {u,w} UNION aff_ge {x} {w,v}
```

证明思路：反设 `s` 与边并 `aff_ge {x}{v,u} ∪ aff_ge {x}{u,w} ∪
aff_ge {x}{w,v}` 不交，则 `s` 被两个相对开集
`aff_gt {x}{v,u,w}`（`OPEN_AFF_GT_1_3`）与其补
`univ \ aff_ge {x}{v,u,w}`（`OPEN_DIFF_AFF_GE`）分离，与
`connected s` 矛盾。关键是 `aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3`
把 `aff_ge {x}{v,u,w}` 写成边并与 `aff_gt` 之并，从而使
`z ∉ aff_gt` 且 `z ∈ s` 落进边并的补，与 `y` 分离。HOL 即对
`connected` 取 `{aff_gt {x}{v,u,w}, univ \ aff_ge {x}{v,u,w}}` 后
`SET_TAC`。

候选已有引理：
- `aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3`（本文件上文，HOL :14125）
- `OPEN_AFF_GT_1_3`（Kepler/Text/PlanarityAuto12.lean:877）
- `OPEN_DIFF_AFF_GE`（Kepler/Text/PlanarityAuto12.lean:1216）
- `IsPreconnected`（Mathlib/Topology/Connected/Basic.lean；HOL `connected`
  按仓库约定编码为 `IsPreconnected`） -/
theorem cut_aff_gt_1_3_connected (x y z v u w : V3) (s : Set V3)
    (hs : IsPreconnected s)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hy : y ∈ s) (hz : z ∈ s)
    (hygt : y ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3))
    (hzgt : z ∉ affGt ({x} : Set V3) ({v, u, w} : Set V3)) :
    ∃ t : V3, t ∈ s ∧
      t ∈ affGe ({x} : Set V3) ({v, u} : Set V3) ∪
        affGe ({x} : Set V3) ({u, w} : Set V3) ∪
        affGe ({x} : Set V3) ({w, v} : Set V3) := by
  by_contra h
  push Not at h
  have hAopen : IsOpen (affGt ({x} : Set V3) ({v, u, w} : Set V3)) :=
    OPEN_AFF_GT_1_3 x v u w hcop
  have hBopen : IsOpen ((Set.univ : Set V3) \
      affGe ({x} : Set V3) ({v, u, w} : Set V3)) := OPEN_DIFF_AFF_GE x v u w
  have hdisj : Disjoint (affGt ({x} : Set V3) ({v, u, w} : Set V3))
      ((Set.univ : Set V3) \ affGe ({x} : Set V3) ({v, u, w} : Set V3)) := by
    rw [Set.disjoint_left]
    intro a haA haB
    exact haB.2 (affGt_subset_affGe_cut haA)
  have hsub : s ⊆ affGt ({x} : Set V3) ({v, u, w} : Set V3) ∪
      ((Set.univ : Set V3) \ affGe ({x} : Set V3) ({v, u, w} : Set V3)) := by
    intro a ha
    by_cases haA : a ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3)
    · exact Or.inl haA
    · refine Or.inr ⟨Set.mem_univ a, ?_⟩
      intro haB
      have hdecomp := aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3 x v u w hcop
      have hmem : a ∈ affGe ({x} : Set V3) ({v, u} : Set V3) ∪
          affGe ({x} : Set V3) ({u, w} : Set V3) ∪
          affGe ({x} : Set V3) ({w, v} : Set V3) ∪
          affGt ({x} : Set V3) ({v, u, w} : Set V3) := hdecomp ▸ haB
      rcases (by simpa only [Set.mem_union] using hmem) with ((h1 | h2) | h3) | h4
      · exact h a ha (Or.inl (Or.inl h1))
      · exact h a ha (Or.inl (Or.inr h2))
      · exact h a ha (Or.inr h3)
      · exact haA h4
  rcases hs.subset_or_subset hAopen hBopen hdisj hsub with hsu | hsv
  · exact hzgt (hsu hz)
  · exact (hsv hy).2 (affGt_subset_affGe_cut hygt)

/-! ## 边锥含于 xfan（planarity.hl:14298-14308） -/

/-- HOL planarity.hl :14298-14308 `AFF_GE_SUBSET_XFAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) u:real^3 w:real^3.
 {u,w} IN E
==> 
aff_ge {x} {u,w} SUBSET xfan(x:real^3,V:real^3->bool,E)
```

证明思路：展开 `xfan x V E = {y | ∃ e ∈ E, y ∈ aff_ge {x} e}`，对
`y ∈ aff_ge {x} {u,w}` 取 `e = {u,w}` 为见证，`huw` 给出 `e ∈ E`，
`y ∈ aff_ge {x} e` 即假设。HOL 即 `EXISTS_TAC {u,w}` 后
`ASM_REWRITE_TAC[]`。

候选已有引理：
- `xfan`（Kepler/Text/Fan.lean:154）
- `affGe`（Kepler/Geom/Aff.lean:42） -/
theorem AFF_GE_SUBSET_XFAN (x : V3) (V : Set V3) (E : Set (Set V3)) (u w : V3)
    (huw : {u, w} ∈ E) :
    affGe ({x} : Set V3) ({u, w} : Set V3) ⊆ xfan x V E := by
  intro y hy
  exact ⟨{u, w}, huw, hy⟩

/-! ## 不共面四点与 aff_gt 的非空性（planarity.hl:14309-14359） -/

/-- HOL planarity.hl :14309-14349 `notcoplanar_4point_aff_gt_3_1_not_empty`

HOL 原文：
```
!x v u w:real^3.
~coplanar {x,v,u,w}
==> ~(aff_gt {x,v,u} {w} INTER aff_gt {x,u,w} {v} INTER aff_gt {x,w,v} {u} = {})
```

证明思路：由 `coplanar_cross_dot` 得
`n = (v-x)⨯(u-x)` 满足 `n·(w-x) ≠ 0`，分正负两种情形。对三个 `3-1`
半空间分别用 `aff_gt_3_1_rep_cross_dot`（含相应的叉积重排/取反）化为
严格半空间，显式取 `y = (1/3)•v+(1/3)•u+(1/3)•w`（重心）作为交的
见证，代入 `DOT_RADD/DOT_RMUL/DOT_CROSS_SELF` 后由 `REAL_LT_MUL` 收尾。
HOL 即 `SET_RULE ~(A={}) <=> ?y. y∈A` 后构造重心点。

候选已有引理：
- `coplanar_cross_dot`（Kepler/Text/PlanarityAuto12.lean:573）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `AFF_GT_3_1`（Kepler/Text/PlanarityAuto11.lean:957）
- `crossProduct`（Mathlib/LinearAlgebra/CrossProduct.lean）
- `dotProduct`（Mathlib，`⬝ᵥ`） -/
theorem notcoplanar_4point_aff_gt_3_1_not_empty (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGt ({x, v, u} : Set V3) {w} ∩ affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, w, v} : Set V3) {u} ≠ ∅ := by
  obtain ⟨hd1, hd2, hd3, -⟩ := notcoplanar_disjoints x v u w hcop
  have h1 : (1 / 3 : ℝ) • v + (1 / 3 : ℝ) • u + (1 / 3 : ℝ) • w ∈
      affGt ({x, v, u} : Set V3) {w} := by
    rw [AFF_GT_3_1 x v u w hd1]
    exact ⟨0, 1 / 3, 1 / 3, 1 / 3, by norm_num, by norm_num, by module⟩
  have h2 : (1 / 3 : ℝ) • v + (1 / 3 : ℝ) • u + (1 / 3 : ℝ) • w ∈
      affGt ({x, u, w} : Set V3) {v} := by
    rw [AFF_GT_3_1 x u w v hd2]
    exact ⟨0, 1 / 3, 1 / 3, 1 / 3, by norm_num, by norm_num, by module⟩
  have h3 : (1 / 3 : ℝ) • v + (1 / 3 : ℝ) • u + (1 / 3 : ℝ) • w ∈
      affGt ({x, w, v} : Set V3) {u} := by
    rw [AFF_GT_3_1 x w v u hd3]
    exact ⟨0, 1 / 3, 1 / 3, 1 / 3, by norm_num, by norm_num, by module⟩
  rw [← Set.nonempty_iff_ne_empty]
  exact ⟨_, ⟨⟨h1, h2⟩, h3⟩⟩

/-- HOL planarity.hl :14350-14359 `notcoplanar_4point_aff_gt_1_3_not_empty`

HOL 原文：
```
!x v u w:real^3.
~coplanar {x,v,u,w}
==> ~(aff_gt {x} {v,u,w}  = {})
```

证明思路：由 `inter_aff_gt_3_1_is_aff_gt_1_3` 把 `aff_gt {x}{v,u,w}`
重写为三个 `3-1` `aff_gt` 之交，再对
`notcoplanar_4point_aff_gt_3_1_not_empty` 取反即得非空。HOL 即
`MRESA_TAC inter_aff_gt_3_1_is_aff_gt_1_3` 后
`REWRITE_TAC[SYM th]` 再 `SET_TAC`。

候选已有引理：
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- `notcoplanar_4point_aff_gt_3_1_not_empty`（本文件上文，HOL :14309） -/
theorem notcoplanar_4point_aff_gt_1_3_not_empty (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGt ({x} : Set V3) ({v, u, w} : Set V3) ≠ ∅ := by
  have h := inter_aff_gt_3_1_is_aff_gt_1_3 x v u w hcop
  rw [← h]
  exact notcoplanar_4point_aff_gt_3_1_not_empty x v u w hcop

/-! ## dart_leads_into 与 aff_gt 的相等（planarity.hl:14360-14400） -/

/-- HOL planarity.hl :14360-14400 `KVQWYDL_lemma1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>  aff_gt{x} {v,u,w} = dart_leads_into x V E u w
```

证明思路：用集合双向包含 `A ⊆ B ∧ B ⊆ A → A = B`。
`aff_gt {x}{v,u,w} ⊆ dartLeadsInto` 由
`aff_gt_1_3_subset_dart_leads_into_fan`。反向用
`cut_aff_gt_1_3_connected`（`s := dartLeadsInto`，其 `IsPreconnected`
来自 `connected_dart_leads_into_fan`）：若存在
`z ∈ dartLeadsInto \ aff_gt`，由 `notcoplanar_4point_aff_gt_1_3_not_empty`
取 `y ∈ aff_gt` 得割点 `t`；再用
`dart_leads_into_mem_topologicalComponentYfan` 与
`topological_component_subset_yfan` 把 `t ∈ dartLeadsInto` 落到 `yfan`，
而 `AFF_GE_SUBSET_XFAN` 说明 `t` 落在某条边的 `aff_ge ⊆ xfan`，与
`yfan = univ \ xfan` 矛盾。不共面性由 `fan80` 与
`properties_fully_surrounded` 给出。

候选已有引理：
- `fan80`（Kepler/Text/Fan.lean:227）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `aff_gt_1_3_subset_dart_leads_into_fan`（Kepler/Text/PlanarityAuto12.lean:270）
- `connected_dart_leads_into_fan`（Kepler/Text/TopologyFan.lean:4321）
- `notcoplanar_4point_aff_gt_1_3_not_empty`（本文件上文，HOL :14350）
- `cut_aff_gt_1_3_connected`（本文件上文，HOL :14252）
- `dart_leads_into_mem_topologicalComponentYfan`（Kepler/Text/TopologyFan.lean:4280）
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `AFF_GE_SUBSET_XFAN`（本文件上文，HOL :14298）
- `yfan`（Kepler/Text/Fan.lean:158） -/
theorem KVQWYDL_lemma1 (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w : V3) (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x} : Set V3) ({v, u, w} : Set V3) = dartLeadsInto x V E u w := by
  apply Set.Subset.antisymm
  · exact aff_gt_1_3_subset_dart_leads_into_fan x V E v u w hfan hvu huw hsigma
      hcard hfan80
  · intro z hz
    by_contra hzgt
    obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
    rw [hsigma] at hθ0 hθπ
    have hcop := properties_fully_surrounded hfan hvu huw hθ0 hθπ
    have hne := notcoplanar_4point_aff_gt_1_3_not_empty x v u w hcop
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hys : y ∈ dartLeadsInto x V E u w :=
      aff_gt_1_3_subset_dart_leads_into_fan x V E v u w hfan hvu huw hsigma
        hcard hfan80 hy
    have hconn : IsPreconnected (dartLeadsInto x V E u w) :=
      connected_dart_leads_into_fan hfan huw
    obtain ⟨t, hts, htun⟩ :=
      cut_aff_gt_1_3_connected x y z v u w (dartLeadsInto x V E u w)
        hconn hcop hys hz hy hzgt
    have hyfan : dartLeadsInto x V E u w ⊆ yfan x V E :=
      topological_component_subset_yfan
        (dart_leads_into_mem_topologicalComponentYfan hfan huw)
    have htxfan : t ∈ xfan x V E := by
      rcases htun with (h1 | h2) | h3
      · exact AFF_GE_SUBSET_XFAN x V E v u hvu h1
      · exact AFF_GE_SUBSET_XFAN x V E u w huw h2
      · exact AFF_GE_SUBSET_XFAN x V E w v hwv h3
    have hty : t ∈ yfan x V E := hyfan hts
    rw [yfan, Set.mem_sdiff] at hty
    exact hty.2 htxfan

/-! ## yfan 分量内的点不等于顶点（planarity.hl:14401-14417） -/

/-- HOL planarity.hl :14401-14417 `point_in_yfan_is_not_inv_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool z:real^3 u:real^3.
FAN(x,V,E) /\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
==> ~(u=z)
```

证明思路：由 `nonsetedge_fully_surround_fan` 与 `zpoint_in_yfan` 得
`z ∈ yfan x V E`，由 `v_subset_xfan` 得 `u ∈ xfan x V E`。展开
`yfan = univ \ xfan` 知 `z ∉ xfan`，故 `u ≠ z`。HOL 即
`MRESA_TAC` 三条引理后 `REWRITE_TAC[yfan] THEN SET_TAC[]`。

候选已有引理：
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `zpoint_in_yfan`（Kepler/Text/PlanarityAuto7.lean:83）
- `v_subset_xfan`（Kepler/Text/PlanarityAuto8.lean:501）
- `yfan`（Kepler/Text/Fan.lean:158）
- `xfan`（Kepler/Text/Fan.lean:154） -/
theorem point_in_yfan_is_not_inv_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (z u : V3) (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U) (hu : u ∈ V) :
    u ≠ z := by
  have hne : E ≠ ∅ := nonsetedge_fully_surround_fan hcard hfan
  have hzY : z ∈ yfan x V E := zpoint_in_yfan x V E U z hfan hne hU hz
  have huX : u ∈ xfan x V E := v_subset_xfan x V E hfan hcard hu
  intro huz
  rw [yfan, Set.mem_sdiff] at hzY
  exact hzY.2 (huz ▸ huX)

/-! ## 端点落在 aff_ge 1-1 中（planarity.hl:14418-14440） -/

/-- HOL planarity.hl :14418-14440 `point_in_aff_ge_1_1`

HOL 原文：
```
!(x:real^3) (v:real^3).
~(x=v)
==>
x IN aff_ge {x} {v}
/\ v IN aff_ge {x} {v}
```

证明思路：用 `AFF_GE_1_1` 的成员刻画（`mem_affGe_singleton`）：
`x` 取系数 `(1,0)`，`v` 取系数 `(0,1)`，两者均满足 `0 ≤ t2`、
`t1 + t2 = 1`，向量等式由 `module` 化简。HOL 即对 `AFF_GE_1_1` 展开后
`EXISTS_TAC &1/&0` 与 `&0/&1` 再 `REAL_ARITH`。

候选已有引理：
- `mem_affGe_singleton`（Kepler/Text/TopologyFan.lean:2664）
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `affGe`（Kepler/Geom/Aff.lean:42） -/
theorem point_in_aff_ge_1_1 (x v : V3) (hxv : x ≠ v) :
    x ∈ affGe ({x} : Set V3) ({v} : Set V3) ∧
      v ∈ affGe ({x} : Set V3) ({v} : Set V3) := by
  constructor
  · rw [mem_affGe_singleton hxv]
    exact ⟨1, 0, le_refl 0, by norm_num, by module⟩
  · rw [mem_affGe_singleton hxv]
    exact ⟨0, 1, by norm_num, by norm_num, by module⟩

/-! ## aff_ge {x}{v,u} 中的顶点必为端点（planarity.hl:14441-14472） -/

/-- `affGe {x} ∅ = {x}`（AFF_GE_EQ_AFFINE_HULL/AFFINE_HULL_1 的现场替代：
`{x} ∪ ∅` 的求和塌缩到单点，故 `f x = 1` 且 `y = x`）。 -/
private theorem affGe_empty_auto13 (x : V3) : affGe {x} (∅ : Set V3) = {x} := by
  ext y
  simp only [affGe, Set.mem_setOf_eq, Affsign, Set.mem_singleton_iff]
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have hTeq : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp
    rw [hTeq, Finset.sum_singleton] at hsum hone
    rw [hsum, hone, one_smul]
  · intro heq
    rw [heq]
    have hfin : ({x} ∪ (∅ : Set V3)).Finite :=
      (Set.finite_singleton x).union Set.finite_empty
    have hTeq : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [hTeq]; simp
    · intro z hz; simp at hz
    · rw [hTeq]; simp

/-- HOL planarity.hl :14441-14472 `POINT_IN_AFF_GE_IMP_IN_EDGE`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 u1:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ u1 IN V /\ ~(x=u1)
/\ u1 IN aff_ge {x} {v,u}
==> u1 IN {v,u}
```

证明思路：由 `remark1_fan`（互异性 `edge_ne_of_fan` 与
`aff_ge` 成员 `point_in_aff_ge`）与
`aff_ge_1_1_subset_aff_ge_fan` 得 `aff_ge {x}{u1} ⊆ aff_ge {x}{v,u}`，
从而两者之交即 `aff_ge {x}{u1}`。由 `FAN` 的 `fan7` 分量，把
`aff_ge {x}{u1} ∩ aff_ge {x}{v,u}` 分配为 `aff_ge {x} ({u1}∩{v,u})`；
若 `u1 ∉ {v,u}` 则交为空，此时用 `point_in_aff_ge_1_1`（`x ≠ u1`）得
`u1 ∈ aff_ge {x}{u1}` 与空集矛盾。HOL 即 `fan7` 后
`DISJ_CASES_TAC` 与 `point_in_aff_ge_1_1` 收尾。

编码缺口：HOL 证明内部用 `AFF_GE_EQ_AFFINE_HULL;AFFINE_HULL_1`，仓库
未以 `AFF_GE_EQ_AFFINE_HULL` 移植（最接近的为单点仿射包引理
`AFFINE_HULL_1`，Kepler/Text/Planarity.lean:4459，及
`affGe {x} ∅ = {x}` 的注释 Kepler/Text/TopologyFan.lean:2790）；本定理
陈述不含该引理，填充证明时需现场替代。

候选已有引理：
- `aff_ge_1_1_subset_aff_ge_fan`（Kepler/Text/Planarity.lean:4059）
- `point_in_aff_ge_1_1`（本文件上文，HOL :14418）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异性分量）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334，HOL `remark1_fan` 成员分量）
- `FAN`（Kepler/Text/Fan.lean:56）、`fan7`（Kepler/Text/Fan.lean:49） -/
theorem POINT_IN_AFF_GE_IMP_IN_EDGE (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u u1 : V3) (hfan : FAN x V E) (hvu : {v, u} ∈ E) (hu1V : u1 ∈ V)
    (hxu1 : x ≠ u1)
    (hu1 : u1 ∈ affGe ({x} : Set V3) ({v, u} : Set V3)) :
    u1 ∈ ({v, u} : Set V3) := by
  rcases hfan with ⟨-, -, -, -, -, hfan7⟩
  have h7 := hfan7 ({u1} : Set V3) (Or.inr ⟨u1, hu1V, rfl⟩)
    ({v, u} : Set V3) (Or.inl hvu)
  have hpt : u1 ∈ affGe ({x} : Set V3) ({u1} : Set V3) :=
    (point_in_aff_ge_1_1 x u1 hxu1).2
  have hmem : u1 ∈ affGe ({x} : Set V3) (({u1} : Set V3) ∩ ({v, u} : Set V3)) := by
    rw [← h7]
    exact ⟨hpt, hu1⟩
  by_cases hcase : u1 ∈ ({v, u} : Set V3)
  · exact hcase
  · exfalso
    have hdisj : Disjoint ({u1} : Set V3) ({v, u} : Set V3) := by
      rw [Set.disjoint_left]
      intro a ha hb
      rw [Set.mem_singleton_iff] at ha
      rw [ha] at hb
      exact hcase hb
    have hinter : ({u1} : Set V3) ∩ ({v, u} : Set V3) = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hdisj
    rw [hinter, affGe_empty_auto13] at hmem
    rw [Set.mem_singleton_iff] at hmem
    exact hxu1 hmem.symm

/-! ## aff_gt 1-2 的端点落在闭包中（planarity.hl:14473-14504） -/

/-- HOL planarity.hl :14473-14504 `POINT_IN_CLOSURE_AFF_GT_1_2`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
~(x=v) /\ ~(x=u) /\ ~(v=u) 
==> v IN closure(aff_gt {x} {v,u})
```

证明思路：`GEOM_ORIGIN_TAC x` 归约到原点。用
`AFF_GT_1_2` 展开 `aff_gt {0}{v,u}`，再用闭包的度量刻画
`CLOSURE_APPROACHABLE`（Mathlib `Metric.mem_closure_iff`）：给定 `e > 0`，
取 `t3 = min (‖u-v‖⁻¹ * e) 1 / 2`、`t2 = 1 - t3`，则
`t2,t3 > 0` 且 `‖(t2•v + t3•u) - v‖ = t3 * ‖u-v‖ < e`（由
`IMP_NORM_FAN` 与 `REAL_LT_LMUL`），故 `t2•v + t3•u ∈ aff_gt` 且逼近
`v`。HOL 即 `EXISTS_TAC (t2 % v + t3 % u)` 后 `NORM_MUL` 与
`REAL_ARITH` 收尾。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `Metric.mem_closure_iff`（Mathlib/Topology/MetricSpace/Basic.lean；HOL
  `CLOSURE_APPROACHABLE` 的度量形式）
- `IMP_NORM_FAN`（Kepler/Text/Planarity.lean:2850）
- `disjoint_of_not_collinear3`（Kepler/Text/Planarity.lean:783）
- `closure`（Mathlib `TopologicalSpace`，`open scoped Topology`） -/
theorem POINT_IN_CLOSURE_AFF_GT_1_2 (x v u : V3)
    (hxv : x ≠ v) (hxu : x ≠ u) (hvu : v ≠ u) :
    v ∈ closure (affGt ({x} : Set V3) ({v, u} : Set V3)) := by
  sorry

end Kepler.Text
