/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 17
(Conforming.hl:8259-9065).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 17, Conforming.hl:8259-9065):
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14` (8259)
- `lemmaINTERS_HALF_SPACE_DS_FANADD3` (8303)
- `aff_3_rep_cross_dot` (8401)
- `SPACE3_EQ_UNION_3SET` (8522)
- `lemmaU1_subset_U` (8622)
- `open_subsetU` (8684)
- `eq_aff_gt_3_fanadd_edge` (8812)
- `aff_gt_add_subset_U1` (8902)
- `lemma_rep_U_fanadd` (8958)
- `dartset_leads_into_ds_open_fanadd` (9008)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`; HOL `CARD ds > 3` ↔ `3 < ds.ncard`.
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
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `aff s` (affine
  hull) ↔ `(affineSpan ℝ s : Set V3)`; HOL `open` ↔ `IsOpen`; HOL
  `(:real^3)` ↔ `Set.univ`; HOL `collinear` ↔ `Collinear3`
  (Kepler/Geom/Azim.lean:43); HOL `coplanar` ↔ `Coplanar`
  (Kepler/Geom/Coplanar.lean:23).
- HOL `(v - x) cross (u - x)` ↔ `crossProduct ((v - x : V3) : Fin 3 → ℝ)
  ((u - x : V3) : Fin 3 → ℝ)`; HOL `dot` ↔ `⬝ᵥ` (`dotProduct`).
- The inner quantifier `(!E1. ... ==> conforming_fan (x,V,E1))` shadows the
  outer `E1`; as in `minimallyNonconformingFan`
  (Kepler/Text/ConformingDefs.lean:226) the inner variable is renamed `E2`
  and, because `conformingFan`/`nFan` need a `FAN` witness, encoded as
  `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
  conformingFan x V E2 hfan2` (the `FAN x V E2` conjunct is kept to align
  with the HOL antecedent).
- None of the ten statements is a verbatim Mathlib theorem. The two
  geometric ones (`aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`,
  `aff_3_rep_cross_dot`) use repo-specific `affGt`/`Collinear3`/`Coplanar`
  (and the second has no Mathlib counterpart for the cross-dot
  characterisation of `affineSpan`), so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto16

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 几何表示引理（Conforming.hl:8259-8450） -/

/-- HOL Conforming.hl :8259-8302 `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`

HOL 原文：
```
!a x y z:real^3.
~coplanar {a, x, y, z}
==> aff_gt {a,x,y}{z} INTER aff{a,x,z} SUBSET aff_gt {a,x} {z}
```

编码说明：`coplanar` ↦ `Coplanar`；`aff_gt` ↦ `affGt`；`aff` ↦
`affineSpan ℝ`；`INTER`/`SUBSET` ↦ `∩`/`⊆`。结论
`affGt ({a, x, y} : Set V3) {z} ∩
(affineSpan ℝ ({a, x, z} : Set V3) : Set V3) ⊆ affGt ({a, x} : Set V3) {z}`。

证明思路：由 `~coplanar {a,x,y,z}` 得 `~collinear {a,x,z}` 与
`~collinear {a,x,y}`（`notcoplanar_imp_notcollinear_fan`）；用
`cross_dot_fully_surrounded_fan` 建立 `n = (x-a)⨯(y-a)` 对 `z` 的定向
符号；`aff_gt_3_1_rep_cross_dot` 把 `affGt {a,x,y}{z}` 化为
`0 < n·(p-a)`，`aff{a,x,z}` 展开为 `a + c•(x-a) + h•(z-a)`，代入后由
`n·(x-a)=0` 得 `n·(p-a)=h·(n·(z-a))` 且 `h>0`；再对 `affGt {a,x}{z}` 用
一次叉积表示即得。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `affGt`（Kepler/Geom/Aff.lean:39）
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- 缺口：`AFF_GT_2_1`/`AFF_GT_3_1` 的系数展开需手工桥接 `affineSpan` -/
theorem aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14 (a x y z : V3) :
    ¬ Coplanar ({a, x, y, z} : Set V3) →
      affGt ({a, x, y} : Set V3) {z} ∩
        (affineSpan ℝ ({a, x, z} : Set V3) : Set V3) ⊆
          affGt ({a, x} : Set V3) {z} := by
  intro hcop p hp
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hax, -, haz, -, hxz, -⟩ := notcoplanar_disjoint a x y z hcop
  have hza : z ≠ a := fun h => haz h.symm
  have hzx : z ≠ x := fun h => hxz h.symm
  have hdis : Disjoint ({a, x, y} : Set V3) {z} :=
    (notcoplanar_disjoints a x y z hcop).1
  rw [AFF_GT_3_1 a x y z hdis] at hp1
  obtain ⟨t1, t2, t3, t4, ht4, hsum, hp_eq⟩ := hp1
  have hp_sub : p - a = t2 • (x - a) + t3 • (y - a) + t4 • (z - a) := by
    have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
    rw [hp_eq, ht1]
    module
  have hcoord : ∃ c h : ℝ, p - a = c • (x - a) + h • (z - a) := by
    have hpS : p ∈ spanPoints ℝ ({a, x, z} : Set V3) := hp2
    have haS : a ∈ spanPoints ℝ ({a, x, z} : Set V3) :=
      mem_spanPoints ℝ a ({a, x, z} : Set V3) (by simp)
    have hv : p - a ∈ vectorSpan ℝ ({a, x, z} : Set V3) :=
      vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints ℝ hpS haS
    rw [vectorSpan_eq_span_vsub_set_right ℝ
        (show a ∈ ({a, x, z} : Set V3) by simp)] at hv
    have hle : Submodule.span ℝ ((fun q : V3 => q - a) '' ({a, x, z} : Set V3)) ≤
        Submodule.span ℝ ({x - a, z - a} : Set V3) := by
      rw [Submodule.span_le]
      rintro v ⟨q, hq, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    have hv' : p - a ∈ Submodule.span ℝ ({x - a, z - a} : Set V3) := hle hv
    rw [Submodule.mem_span_pair] at hv'
    obtain ⟨c, h, hch⟩ := hv'
    exact ⟨c, h, hch.symm⟩
  obtain ⟨c, h, hcp⟩ := hcoord
  have hcoe_sub : ((p - a : V3) : Fin 3 → ℝ) =
      t2 • ((x - a : V3) : Fin 3 → ℝ) + t3 • ((y - a : V3) : Fin 3 → ℝ) +
        t4 • ((z - a : V3) : Fin 3 → ℝ) := by
    have := congrArg (fun q : V3 => (q : Fin 3 → ℝ)) hp_sub
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using this
  have hcoe_coord : ((p - a : V3) : Fin 3 → ℝ) =
      c • ((x - a : V3) : Fin 3 → ℝ) + h • ((z - a : V3) : Fin 3 → ℝ) := by
    have := congrArg (fun q : V3 => (q : Fin 3 → ℝ)) hcp
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using this
  let n : Fin 3 → ℝ :=
    crossProduct ((x - a : V3) : Fin 3 → ℝ) ((y - a : V3) : Fin 3 → ℝ)
  have hx0 : n ⬝ᵥ ((x - a : V3) : Fin 3 → ℝ) = 0 := by
    dsimp only [n]
    rw [dotProduct_comm]
    exact dot_self_cross _ _
  have hy0 : n ⬝ᵥ ((y - a : V3) : Fin 3 → ℝ) = 0 := by
    dsimp only [n]
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  have hnz : n ⬝ᵥ ((z - a : V3) : Fin 3 → ℝ) ≠ 0 := by
    dsimp only [n]
    exact coplanar_cross_dot a x y z hcop
  have hdot1 : n ⬝ᵥ ((p - a : V3) : Fin 3 → ℝ) =
      t4 * (n ⬝ᵥ ((z - a : V3) : Fin 3 → ℝ)) := by
    rw [hcoe_sub, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul, hx0, hy0]
    simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
  have hdot2 : n ⬝ᵥ ((p - a : V3) : Fin 3 → ℝ) =
      h * (n ⬝ᵥ ((z - a : V3) : Fin 3 → ℝ)) := by
    rw [hcoe_coord, dotProduct_add, dotProduct_smul, dotProduct_smul, hx0]
    simp only [smul_eq_mul, mul_zero]
    ring
  have ht4h : t4 = h := by
    have hz : (t4 - h) * (n ⬝ᵥ ((z - a : V3) : Fin 3 → ℝ)) = 0 := by
      rw [sub_mul, ← hdot1, ← hdot2, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hnz)
  rw [affGt_pair_iff (v0 := a) (v1 := x) (x := z) (y := p) hax hza hzx]
  exact ⟨t4, ht4, c, by rw [hcp, ht4h, add_comm]⟩

/-- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1` 的叉积正定版本（不依赖 `azim`
条件，只用 `0 < (x-a)⨯(y-a)·z` 与 `0 < (x-a)⨯(y-a)·w`）。 -/
private theorem aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1_hpos
    (a x y z w : V3)
    (hcop : ¬ Coplanar ({a, x, y, z} : Set V3))
    (hax : a ≠ x) (hwa : w ≠ a) (hwx : w ≠ x)
    (hpos_z : 0 < crossProduct ((x - a : V3) : Fin 3 → ℝ)
        ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ ((z - a : V3) : Fin 3 → ℝ))
    (hpos_w : 0 < crossProduct ((x - a : V3) : Fin 3 → ℝ)
        ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - a : V3) : Fin 3 → ℝ)) :
    affGt ({a, x, y} : Set V3) {z} ∩
      (affineSpan ℝ ({a, x, w} : Set V3) : Set V3) ⊆
        affGt ({a, x} : Set V3) {w} := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  rw [aff_gt_3_1_rep_cross_dot a x y z hcop hpos_z, Set.mem_setOf_eq] at hp1
  have hcoord : ∃ c h : ℝ, p - a = c • (x - a) + h • (w - a) := by
    have hpS : p ∈ spanPoints ℝ ({a, x, w} : Set V3) := hp2
    have haS : a ∈ spanPoints ℝ ({a, x, w} : Set V3) :=
      mem_spanPoints ℝ a ({a, x, w} : Set V3) (by simp)
    have hv : p - a ∈ vectorSpan ℝ ({a, x, w} : Set V3) :=
      vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints ℝ hpS haS
    rw [vectorSpan_eq_span_vsub_set_right ℝ
        (show a ∈ ({a, x, w} : Set V3) by simp)] at hv
    have hle : Submodule.span ℝ ((fun q : V3 => q - a) '' ({a, x, w} : Set V3)) ≤
        Submodule.span ℝ ({x - a, w - a} : Set V3) := by
      rw [Submodule.span_le]
      rintro v ⟨q, hq, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    have hv' : p - a ∈ Submodule.span ℝ ({x - a, w - a} : Set V3) := hle hv
    rw [Submodule.mem_span_pair] at hv'
    obtain ⟨c, h, hch⟩ := hv'
    exact ⟨c, h, hch.symm⟩
  obtain ⟨c, h, hcp⟩ := hcoord
  have hcoe : ((p - a : V3) : Fin 3 → ℝ) =
      c • ((x - a : V3) : Fin 3 → ℝ) + h • ((w - a : V3) : Fin 3 → ℝ) := by
    have := congrArg (fun q : V3 => (q : Fin 3 → ℝ)) hcp
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using this
  have hdot : crossProduct ((x - a : V3) : Fin 3 → ℝ) ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((p - a : V3) : Fin 3 → ℝ) =
      h * (crossProduct ((x - a : V3) : Fin 3 → ℝ) ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((w - a : V3) : Fin 3 → ℝ)) := by
    rw [hcoe, dotProduct_add, dotProduct_smul, dotProduct_smul]
    have hx0 : crossProduct ((x - a : V3) : Fin 3 → ℝ) ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((x - a : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]
      exact dot_self_cross _ _
    rw [hx0, smul_zero, zero_add, smul_eq_mul]
  have hhpos : 0 < h := by
    have hlt : 0 < h * (crossProduct ((x - a : V3) : Fin 3 → ℝ)
        ((y - a : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - a : V3) : Fin 3 → ℝ)) := by
      rw [← hdot]
      exact hp1
    exact (mul_pos_iff_of_pos_right hpos_w).mp hlt
  rw [affGt_pair_iff (v0 := a) (v1 := x) (x := w) (y := p) hax hwa hwx]
  exact ⟨h, hhpos, c, by rw [hcp, add_comm]⟩

/-- HOL Conforming.hl :8303-8400 `lemmaINTERS_HALF_SPACE_DS_FANADD3`

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
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}

==> U1 INTER aff {x,v,w} SUBSET  aff_gt {x} {v, w}
```

编码说明：内层 `!E1` 改名为 `E2`（携带 `hfan2`）；`INTER`/`SUBSET` ↦
`∩`/`⊆`；`aff` ↦ `affineSpan ℝ`；`U1` 定义为四个 `affGt` 之交。
结论 `U1 ∩ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ⊆
affGt ({x} : Set V3) {v, w}`。

证明思路：由 `fan80` 对 `(u,w)`、`(v,u)`、`(v,sigma_fan x V E v u)` 用
`properties_fully_surrounded` 得三组四点非共面；对 `U1` 的四个
`affGt` 分别用 `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1` 与
`aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14` 把半空间交约化为
`aff {x,v,w} ∩ …`，再用 `aff_gt_inter_aff_gt` 与 `SET_TAC` 收口。

候选已有引理：
- `lemmaINTERS_HALF_SPACE_DS_FANADD1`（Kepler/Text/ConformingAuto16.lean:1304）
- `lemmaINTERS_HALF_SPACE_DS_FANADD2`（Kepler/Text/ConformingAuto16.lean:1515）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`（Kepler/Text/ConformingAuto16.lean:1673）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14`（本文件上文）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- 缺口：`AFF_GT_MONO_LEFT`、`remark1_fan` 未以该名移植 -/
theorem lemmaINTERS_HALF_SPACE_DS_FANADD3 (x : V3) (V : Set V3)
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
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      U1 ∩ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ⊆
        affGt ({x} : Set V3) {v, w} := by
  intro h
  obtain ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hmin, hU1⟩ := h
  have hθuw : 0 < azim x u w v ∧ azim x u w v < Real.pi := by
    have := hfan80 u w huw
    rwa [hsigma] at this
  have hcop_xvuw : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθuw.1 hθuw.2
  have hnc_vw : ¬ Collinear3 x v w := (notcoplanar_imp_notcollinear_fan hcop_xvuw).2.2
  have hnc_uv : ¬ Collinear3 x u v := by
    have hcop' : ¬ Coplanar ({x, u, v, w} : Set V3) := by
      rwa [show ({x, u, v, w} : Set V3) = ({x, v, u, w} : Set V3) by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact (notcoplanar_imp_notcollinear_fan hcop').2.1
  obtain ⟨hxv, hxu, hxw, hvu_ne, hvw_ne, huw_ne⟩ :=
    notcoplanar_disjoint x v u w hcop_xvuw
  have hσ_soe : sigmaFan x V E v u ∈ setOfEdge v V E :=
    sigma_fan_in_setOfEdge hfan
      ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu)
  have hσvE : ({v, sigmaFan x V E v u} : Set V3) ∈ E :=
    (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfan).mpr hσ_soe
  have hθs : 0 < azim x v u (sigmaFan x V E v u) ∧
      azim x v u (sigmaFan x V E v u) < Real.pi := hfan80 v u hvu
  have hcop_vus : ¬ Coplanar ({x, v, u, sigmaFan x V E v u} : Set V3) := by
    have h := properties_fully_surrounded (x := x) (V := V) (E := E)
      (v := sigmaFan x V E v u) (u := v) (w := u)
      hfan (by rwa [Set.pair_comm]) hvu hθs.1 hθs.2
    have hset : ({x, sigmaFan x V E v u, v, u} : Set V3) =
        ({x, v, u, sigmaFan x V E v u} : Set V3) := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset] at h
  have hcop_xwuv : ¬ Coplanar ({x, w, u, v} : Set V3) := by
    rwa [show ({x, w, u, v} : Set V3) = ({x, v, u, w} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hpos_s : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((sigmaFan x V E v u - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v) (v := u)
      (u1 := sigmaFan x V E v u)
      (fan_not_collinear hfan hσvE) (fan_not_collinear hfan hvu) hθs.1 hθs.2
  have hpos_w : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) := by
    have h := cross_dot_fully_surrounded_fan (x := x) (v1 := u) (v := w) (u1 := v)
      hnc_uv (notcoplanar_imp_notcollinear_fan hcop_xvuw).1 hθuw.1 hθuw.2
    have heq : crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) =
        crossProduct ((u - x : V3) : Fin 3 → ℝ)
          ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) := by
      calc crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
            ((w - x : V3) : Fin 3 → ℝ)
          = ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
              crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) := by
            rw [dotProduct_comm]
        _ = ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ
              crossProduct ((u - x : V3) : Fin 3 → ℝ) ((w - x : V3) : Fin 3 → ℝ) := by
            rw [triple_product_permutation]
        _ = crossProduct ((u - x : V3) : Fin 3 → ℝ) ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
              ((v - x : V3) : Fin 3 → ℝ) := by
            rw [dotProduct_comm]
    rwa [heq]
  have hB := aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1_hpos x v u
      (sigmaFan x V E v u) w hcop_vus hxv hxw.symm hvw_ne.symm hpos_s hpos_w
  have hA := aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_14 x w u v hcop_xwuv
  have haff : affGt ({x} : Set V3) {v, w} =
      affGt ({x, v} : Set V3) {w} ∩ affGt ({x, w} : Set V3) {v} :=
    aff_gt_inter_aff_gt hnc_vw
  intro z hz
  obtain ⟨hzU, hzspan⟩ := hz
  rw [hU1] at hzU
  obtain ⟨⟨⟨hzA, hzB⟩, _⟩, _⟩ := hzU
  have hBmem : z ∈ affGt ({x, v} : Set V3) {w} := hB ⟨hzB, hzspan⟩
  have hzA' : z ∈ affGt ({x, w, u} : Set V3) {v} := by
    rw [show ({x, w, u} : Set V3) = ({x, u, w} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hzA
  have hzspan' : z ∈ (affineSpan ℝ ({x, w, v} : Set V3) : Set V3) := by
    rw [show ({x, w, v} : Set V3) = ({x, v, w} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hzspan
  have hAmem : z ∈ affGt ({x, w} : Set V3) {v} := hA ⟨hzA', hzspan'⟩
  rw [haff]
  exact ⟨hBmem, hAmem⟩

/-- 叉积平面分解辅助恒等式（本地副本）。 -/
private lemma crossProduct_plane_decomp_aux_17 (a b z : Fin 3 → ℝ) :
    (crossProduct a b ⬝ᵥ crossProduct a b) • z =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
      ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
  have h1 : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      (crossProduct a b ⬝ᵥ crossProduct a b) • z -
        (z ⬝ᵥ crossProduct a b) • crossProduct a b :=
    cross_cross_eq_smul_sub_smul (crossProduct a b) z (crossProduct a b)
  have h2 : crossProduct (crossProduct a b) z =
      (a ⬝ᵥ z) • b - (b ⬝ᵥ z) • a :=
    cross_cross_eq_smul_sub_smul a b z
  have hb : crossProduct b (crossProduct a b) =
      (b ⬝ᵥ b) • a - (a ⬝ᵥ b) • b :=
    cross_cross_eq_smul_sub_smul' b a b
  have ha : crossProduct a (crossProduct a b) =
      (a ⬝ᵥ b) • a - (a ⬝ᵥ a) • b :=
    cross_cross_eq_smul_sub_smul' a a b
  have h1' : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b := by
    rw [h2, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hb, ha]
    module
  calc (crossProduct a b ⬝ᵥ crossProduct a b) • z =
        crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by
        rw [h1]; abel
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by rw [h1']
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
        rw [dotProduct_comm z (crossProduct a b)]

/-- 平面分解（本地副本）：`n = a ⨯ b ≠ 0` 且 `n·z = 0` 时 `z` 是 `a,b` 的线性组合。 -/
private lemma crossProduct_plane_decomp_17 {a b z : Fin 3 → ℝ}
    (hn : crossProduct a b ≠ 0) (hz : (crossProduct a b) ⬝ᵥ z = 0) :
    z = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
  have hnn : crossProduct a b ⬝ᵥ crossProduct a b ≠ 0 := by
    intro h0
    apply hn
    funext i
    have hsum : ∑ j, (crossProduct a b) j * (crossProduct a b) j = 0 := by
      simpa only [dotProduct] using h0
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg ((crossProduct a b) j))).mp hsum
    exact mul_self_eq_zero.mp (h3 i (Finset.mem_univ i))
  have hmain := crossProduct_plane_decomp_aux_17 a b z
  rw [hz, zero_smul, add_zero] at hmain
  calc z = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        ((crossProduct a b ⬝ᵥ crossProduct a b) • z) :=
        (inv_smul_smul₀ hnn z).symm
    _ = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        (((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
         ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b) := by rw [hmain]
    _ = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
        rw [smul_add, smul_smul, smul_smul]

/-- HOL Conforming.hl :8401-8521 `aff_3_rep_cross_dot`

HOL 原文：
```
!x:real^3  v:real^3 u:real^3.
~collinear {x,v,u}

==> aff {x,v,u} ={y:real^3|   (((v-x) cross (u-x)) dot (y-x)) = &0}
```

编码说明：`collinear` ↦ `Collinear3`；`aff` ↦ `affineSpan ℝ`；
`cross`/`dot` ↦ `crossProduct`/`⬝ᵥ`。结论
`(affineSpan ℝ ({x, v, u} : Set V3) : Set V3) =
{y : V3 | crossProduct ((v-x):Fin 3→ℝ) ((u-x):Fin 3→ℝ) ⬝ᵥ ((y-x):Fin 3→ℝ) = 0}`。
这是纯几何（Mathlib 通用词汇）的命题，但 Mathlib 没有把 `affineSpan`
等同于「位移与叉积正交」的现成定理，故仍按 HOL 移植。

证明思路：`⊆` 方向把 `y = u'•x + v'•v + w•u`（系数和 1）代入
`(v-x)⨯(u-x) · (y-x)`，用叉积/点积双线性、`cross_refl`、
`dot_cross_self` 化简为 0。`⊇` 方向由 `~collinear` 取标准正交标架
`e1,e2,e3`（`e1Fan`/`e2Fan`/`e3Fan`）展开坐标，解线性方程组给出
`affineSpan` 的系数。

候选已有引理：
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `crossProduct`（Mathlib/LinearAlgebra/CrossProduct.lean）
- `dot_self_cross` / `dot_cross_self`（Mathlib）
- `affineSpan`（Mathlib）
- `e1Fan`/`e2Fan`/`e3Fan`（Kepler/Text/TopologyFan.lean:2486 附近）
- 缺口：HOL `properties_coordinate`/`ORTHONORMAL_IMP_SPANNING`/
  `ORTHONORMAL_CROSS` 未以该名移植 -/
theorem aff_3_rep_cross_dot (x v u : V3) :
    ¬ Collinear3 x v u →
      (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) =
        {y : V3 | crossProduct ((v - x : V3) : Fin 3 → ℝ)
            ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) = 0} := by
  intro hnc
  have hvx : v ≠ x := by
    intro h
    exact hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) h)
  have ha0 : ((v - x : V3) : Fin 3 → ℝ) ≠ 0 := by
    intro h
    apply hvx
    exact sub_eq_zero.mp ((WithLp.ofLp_eq_zero 2).mp h)
  have hn : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ≠ 0 := by
    rw [crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' ha0]
    intro c hc
    apply hnc
    refine (collinear3_iff_smul hvx).mpr ⟨c, ?_⟩
    have h := congrArg (WithLp.toLp 2) hc.symm
    simpa only [WithLp.toLp_smul, WithLp.toLp_ofLp] using h
  have himg : (fun q : V3 => q -ᵥ x) '' ({x, v, u} : Set V3) =
      insert (0 : V3) ({v - x, u - x} : Set V3) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> simp [vsub_eq_sub]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨x, by simp, by simp⟩
      · exact ⟨v, by simp, by simp [vsub_eq_sub]⟩
      · exact ⟨u, by simp, by simp [vsub_eq_sub]⟩
  have hspan : vectorSpan ℝ ({x, v, u} : Set V3) =
      Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (by simp : x ∈ ({x, v, u} : Set V3)),
      himg, Submodule.span_insert_zero]
  have hxmem : x ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) :=
    mem_affineSpan ℝ (by simp)
  ext y
  constructor
  · intro hy
    simp only [Set.mem_setOf_eq]
    have hmem : y - x ∈ Submodule.span ℝ ({v - x, u - x} : Set V3) := by
      have h := (AffineSubspace.vsub_right_mem_direction_iff_mem hxmem y).mpr hy
      rw [direction_affineSpan, hspan] at h
      simpa [vsub_eq_sub] using h
    obtain ⟨c1, c2, hc⟩ := Submodule.mem_span_pair.mp hmem
    have hc' : ((y - x : V3) : Fin 3 → ℝ) =
        c1 • ((v - x : V3) : Fin 3 → ℝ) + c2 • ((u - x : V3) : Fin 3 → ℝ) := by
      have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hc
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h.symm
    rw [hc']
    have ha : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_self_cross _ _
    have hb : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((u - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_cross_self _ _
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ha, hb, mul_zero, add_zero]
  · intro hy
    simp only [Set.mem_setOf_eq] at hy
    let a : Fin 3 → ℝ := ((v - x : V3) : Fin 3 → ℝ)
    let b : Fin 3 → ℝ := ((u - x : V3) : Fin 3 → ℝ)
    let z : Fin 3 → ℝ := ((y - x : V3) : Fin 3 → ℝ)
    let A : ℝ := ((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))
    let B : ℝ := ((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))
    have hn_ab : crossProduct a b ≠ 0 := by simpa only [a, b] using hn
    have hz : crossProduct a b ⬝ᵥ z = 0 := by simpa only [a, b, z] using hy
    have hdec := crossProduct_plane_decomp_17 (a := a) (b := b) (z := z) hn_ab hz
    have hdecV : (y - x : V3) = A • (v - x) + B • (u - x) := by
      have h := congrArg (WithLp.toLp 2) hdec
      simpa only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp, A, B, a, b, z] using h
    have hmem : y - x ∈ Submodule.span ℝ ({v - x, u - x} : Set V3) := by
      rw [hdecV]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hdir : y - x ∈ (affineSpan ℝ ({x, v, u} : Set V3)).direction := by
      rw [direction_affineSpan, hspan]
      exact hmem
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hxmem y).mp (by
      simpa [vsub_eq_sub] using hdir)

/-- 混合积轮换：`(a × b) · c = (b × c) · a`。 -/
private theorem cross_dot_cyclic17 {a b c : Fin 3 → ℝ} :
    crossProduct a b ⬝ᵥ c = crossProduct b c ⬝ᵥ a := by
  calc crossProduct a b ⬝ᵥ c = c ⬝ᵥ crossProduct a b := dotProduct_comm _ _
    _ = a ⬝ᵥ crossProduct b c := triple_product_permutation c a b
    _ = crossProduct b c ⬝ᵥ a := dotProduct_comm _ _

/-- 空间分解的纯几何核：平面 `{x,v,w}` 与分别由 `s`、`u` 定向的两个开半空间
之并覆盖全空间（`s` 与 `u` 位于平面两侧时）。 -/
private theorem space3_eq_union_3set_geom (x v w u s : V3)
    (hcop_u : ¬ Coplanar ({x, w, v, u} : Set V3))
    (hcop_s : ¬ Coplanar ({x, v, w, s} : Set V3))
    (hposB : 0 < crossProduct ((w - x : V3) : Fin 3 → ℝ)
        ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ))
    (hposA : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((s - x : V3) : Fin 3 → ℝ)) :
    (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
      affGt ({x, v, w} : Set V3) {s} ∪
      affGt ({x, v, w} : Set V3) {u} = Set.univ := by
  have hnc_vw : ¬ Collinear3 x v w :=
    (notcoplanar_imp_notcollinear_fan hcop_s).2.1
  have hP := aff_3_rep_cross_dot x v w hnc_vw
  have hA := aff_gt_3_1_rep_cross_dot x v w s hcop_s hposA
  have hB0 := aff_gt_3_1_rep_cross_dot x w v u hcop_u hposB
  have hB1 : affGt ({x, v, w} : Set V3) {u} =
      {y : V3 | 0 < crossProduct ((w - x : V3) : Fin 3 → ℝ)
          ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} := by
    rw [show ({x, v, w} : Set V3) = ({x, w, v} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hB0
  ext y
  constructor
  · intro _; exact Set.mem_univ y
  · intro _
    rcases lt_trichotomy (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) 0 with
      hneg | hzero | hpos
    · right
      rw [hB1]
      simp only [Set.mem_setOf_eq]
      have hcross : crossProduct ((w - x : V3) : Fin 3 → ℝ)
          ((v - x : V3) : Fin 3 → ℝ) =
          - crossProduct ((v - x : V3) : Fin 3 → ℝ)
            ((w - x : V3) : Fin 3 → ℝ) := (cross_anticomm _ _).symm
      rw [hcross, neg_dotProduct]
      linarith
    · left; left
      rw [hP]
      simpa only [Set.mem_setOf_eq] using hzero
    · left; right
      rw [hA]
      simpa only [Set.mem_setOf_eq] using hpos

/-! ## 空间分解与 U1/U 的包含关系（Conforming.hl:8522-9065） -/

/-- HOL Conforming.hl :8522-8621 `SPACE3_EQ_UNION_3SET`

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
==> aff {x,v,w} UNION aff_gt {x, v, w} {sigma_fan x V E v u} UNION aff_gt {x, v, w} {u}= (:real^3)
```

编码说明：注意本定理的假设块没有内层 `!E1` conforming 子句；`aff` ↦
`affineSpan ℝ`；`aff_gt` ↦ `affGt`；`(:real^3)` ↦ `Set.univ`。结论
`(affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ∪
affGt ({x, v, w} : Set V3) {u} = Set.univ`。

证明思路：由 `fan80` 与 `properties_fully_surrounded` 得
`~collinear {x,w,v}`、`~collinear {x,v,sigma_fan x V E v u}` 等；用
`aff_3_rep_cross_dot` 把 `aff {x,v,w}` 化为叉积正交条件，用
`aff_gt_3_1_rep_cross_dot` 把两个开半空间化为叉积定向条件
（`cross_dot_fully_surrounded_fan` 定符号），对任意 `y` 按
`(w-x)⨯(v-x)·(y-x)` 与 `(v-x)⨯(sigma_fan …-x)·(y-x)` 的符号分类
（`REAL_ARITH`）即得三集之并覆盖全空间。

候选已有引理：
- `aff_3_rep_cross_dot`（本文件上文）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- 缺口：`AFF_GT_3_1` 的系数展开与 `AFF_GT_3_1_REP_CROSS_DOT` 的
  定向重排需手工桥接 -/
theorem SPACE3_EQ_UNION_3SET (x : V3) (V : Set V3)
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
      (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
        affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ∪
        affGt ({x, v, w} : Set V3) {u} = Set.univ := by
  intro h
  obtain ⟨_hfanE, hcard, hfan80, _hds, _hds3, _hfsub, _hf1f2, _hf2f3, _hf3ne,
    _hf1v, _hf2u, _hf3w, hvu, huw, hwv, hsigma, _hf1u, _hf2w, _hds1, _hds2,
    _hf10, _hf20, _hf30, hE1⟩ := h
  have hθuw : 0 < azim x u w v ∧ azim x u w v < Real.pi := by
    have := hfan80 u w huw
    rwa [hsigma] at this
  have hcop_xvuw : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθuw.1 hθuw.2
  have hnc_vw : ¬ Collinear3 x v w :=
    (notcoplanar_imp_notcollinear_fan hcop_xvuw).2.2
  have hnc_vu : ¬ Collinear3 x v u :=
    (notcoplanar_imp_notcollinear_fan hcop_xvuw).2.1
  have hnc_uw : ¬ Collinear3 x u w :=
    (notcoplanar_imp_notcollinear_fan hcop_xvuw).1
  have hnc_uv : ¬ Collinear3 x u v := by
    have hcop' : ¬ Coplanar ({x, u, v, w} : Set V3) := by
      rwa [show ({x, u, v, w} : Set V3) = ({x, v, u, w} : Set V3) by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact (notcoplanar_imp_notcollinear_fan hcop').2.1
  have hcop_u : ¬ Coplanar ({x, w, v, u} : Set V3) := by
    rwa [show ({x, w, v, u} : Set V3) = ({x, v, u, w} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hpos_w0 : 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := u) (v := w) (u1 := v)
      hnc_uv hnc_uw hθuw.1 hθuw.2
  have hposB : 0 < crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ) := by
    rw [← cross_dot_cyclic17 (a := ((u - x : V3) : Fin 3 → ℝ))
      (b := ((w - x : V3) : Fin 3 → ℝ)) (c := ((v - x : V3) : Fin 3 → ℝ))]
    exact hpos_w0
  have hσ_edge : ({v, sigmaFan x V E v u} : Set V3) ∈ E :=
    (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfan).mpr
      (sigma_fan_in_setOfEdge hfan
        ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu))
  have hnc_vσ : ¬ Collinear3 x v (sigmaFan x V E v u) :=
    fan_not_collinear hfan hσ_edge
  have hxv : v ≠ x := fun hh =>
    hnc_vu (collinear3_of_eq (v := x) (w := v) (w1 := u) hh)
  have hsmall : azim x v u w ≤ azim x v u (sigmaFan x V E v u) :=
    angle_is_small_fan hfan hvu huw hsigma hfan80 hcard
  have hsum : azim x v u (sigmaFan x V E v u) =
      azim x v u w + azim x v w (sigmaFan x V E v u) :=
    sum4_azim_fan hxv hnc_vu hnc_vw hnc_vσ hsmall
  have h80vu : 0 < azim x v u (sigmaFan x V E v u) ∧
      azim x v u (sigmaFan x V E v u) < Real.pi := hfan80 v u hvu
  have hlt : azim x v w (sigmaFan x V E v u) < Real.pi := by
    linarith [hsum, h80vu.2, azim_nonneg x v u w]
  have hpos_azim : 0 < azim x v w (sigmaFan x V E v u) := by
    rcases lt_or_eq_of_le (azim_nonneg x v w (sigmaFan x V E v u)) with hh | hh
    · exact hh
    · exfalso
      have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
        rw [← hE1]; exact Set.mem_union_right E (by simp)
      have hσvE1 : ({v, sigmaFan x V E v u} : Set V3) ∈ E1 := by
        rw [← hE1]; exact Set.mem_union_left _ hσ_edge
      have hweq : w = sigmaFan x V E v u :=
        unique_azim0_point_fan hfan1 hvwE1 hσvE1 hh.symm
      have hvwE : ({v, w} : Set V3) ∈ E := by
        rw [hweq]; exact hσ_edge
      exact hwv (Set.pair_comm v w ▸ hvwE)
  have hθs : 0 < azim x v w (sigmaFan x V E v u) ∧
      azim x v w (sigmaFan x V E v u) < Real.pi := ⟨hpos_azim, hlt⟩
  have hposA : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((sigmaFan x V E v u - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v) (v := w)
      (u1 := sigmaFan x V E v u) hnc_vσ hnc_vw hθs.1 hθs.2
  have hcop_s : ¬ Coplanar ({x, v, w, sigmaFan x V E v u} : Set V3) := by
    have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
      rw [← hE1]; exact Set.mem_union_right E (by simp)
    have hσvE1 : ({v, sigmaFan x V E v u} : Set V3) ∈ E1 := by
      rw [← hE1]; exact Set.mem_union_left _ hσ_edge
    have h := properties_fully_surrounded (x := x) (V := V) (E := E1)
      (v := sigmaFan x V E v u) (u := v) (w := w)
      hfan1 (Set.pair_comm v (sigmaFan x V E v u) ▸ hσvE1) hvwE1 hθs.1 hθs.2
    rwa [show ({x, sigmaFan x V E v u, v, w} : Set V3) =
        ({x, v, w, sigmaFan x V E v u} : Set V3) by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  exact space3_eq_union_3set_geom x v w u (sigmaFan x V E v u)
    hcop_u hcop_s hposB hposA

/-- HOL Conforming.hl :8622-8683 `lemmaU1_subset_U`

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
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
==> U1 SUBSET U
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；`UNION` ↦
`∪`；`U1` 为四 `affGt` 之交，`U` 为两个 `dartsetLeadsIntoFan` 与
`affGt {x}{v,w}` 之并。结论 `U1 ⊆ U`。

证明思路：由 `lemmaINTERS_HALF_SPACE_DS_FANADD1/2/3` 把 `U1` 的三个
分量分别包含进 `dartsetLeadsIntoFan x V E1 ds1`/`ds2`；由
`SPACE3_EQ_UNION_3SET` 得 `aff {x,v,w} ∪ affGt {x,v,w}{…} ∪ affGt {x,v,w}{u}
= univ`，配合 `lemmaINTERS_HALF_SPACE_DS_FANADD3` 的
`U1 ∩ aff {x,v,w} ⊆ affGt {x}{v,w}` 与集合运算（`SET_TAC`）收口。

候选已有引理：
- `lemmaINTERS_HALF_SPACE_DS_FANADD1/2/3`
  （Kepler/Text/ConformingAuto16.lean:1304/1515、本文件上文）
- `SPACE3_EQ_UNION_3SET`（本文件上文）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- 缺口：`FAN80_FANADD` 之外的 fanadd 引理按名引用，未逐一桥接 -/
theorem lemmaU1_subset_U (x : V3) (V : Set V3)
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
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} ∧
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} →
      U1 ⊆ U := by
  intro h
  obtain ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hmin, hU1, hU⟩ := h
  have hbase : FAN x V E ∧
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
      E ∪ {({v, w} : Set V3)} = E1 :=
    ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
      hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20,
      hf30, hE1⟩
  have hds1sub := lemmaINTERS_HALF_SPACE_DS_FANADD2 x V E E1 ds f1 f2 f3 v u w
    ds1 ds2 f10 f20 f30 U1 hfan hfan1
    ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
      hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20,
      hf30, hE1, hmin, hU1.symm⟩
  have hds2sub := lemmaINTERS_HALF_SPACE_DS_FANADD1 x V E E1 ds f1 f2 f3 v u w
    ds1 ds2 f10 f20 f30 U1 hfan hfan1
    ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
      hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20,
      hf30, hE1, hmin, hU1.symm⟩
  have hhalf := lemmaINTERS_HALF_SPACE_DS_FANADD3 x V E E1 ds f1 f2 f3 v u w
    ds1 ds2 f10 f20 f30 U1 hfan hfan1
    ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
      hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20,
      hf30, hE1, hmin, hU1⟩
  have hcover := SPACE3_EQ_UNION_3SET x V E E1 ds f1 f2 f3 v u w
    ds1 ds2 f10 f20 f30 hfan hfan1 hbase
  intro z hz
  rw [hU]
  have hzcov : z ∈ (affineSpan ℝ ({x, v, w} : Set V3) : Set V3) ∪
      affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ∪
      affGt ({x, v, w} : Set V3) {u} := by
    rw [hcover]; exact Set.mem_univ z
  rw [Set.mem_union, Set.mem_union] at hzcov
  rcases hzcov with (hzaff | hzσ) | hzu
  · exact Or.inr (hhalf ⟨hz, hzaff⟩)
  · exact Or.inl (Or.inl (hds1sub ⟨hz, hzσ⟩))
  · exact Or.inl (Or.inr (hds2sub ⟨hz, hzu⟩))

/-- HOL Conforming.hl :8684-8811 `open_subsetU`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
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
/\  U=aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> open U
```

编码说明：`open` ↦ `IsOpen`；`U` 为四 `affGt` 之交。结论 `IsOpen U`。

证明思路：`U` 是四个 `affGt` 之交，逐个用 `OPEN_AFF_GT_3_1` 证开
（每个 `affGt {x,·,·}{·}` 需要对应三点非共线，由 `fan80` 与
`properties_fully_surrounded` 提供；`sigma_fan` 的第三点用
`SIGMA_FAN_OF_FANADD_AT_POINT1` 换到 `E1`），再三次 `IsOpen.inter`
收口。

候选已有引理：
- `OPEN_AFF_GT_3_1`（Kepler/Text/ConformingAuto5.lean:433）
- `IsOpen.inter`（Mathlib/Topology/Defs/Basic.lean）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `sigma_fan_in_setOfEdge`（Kepler/Text/Fan.lean:326）
- 缺口：`remark1_fan` 未以该名移植 -/
theorem open_subsetU (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    U = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      IsOpen U := by
  rintro ⟨hfanE, hcard, h80, hds, hds3, hfsub, hf12, hf23, hf31, hpr1, hpr2,
    hpr3, hvu, huw, hwv, hsigma, hf1u, hf2w, hface1, hface2, hf10, hf20,
    hf30, hE1, hconf, hU⟩
  have h80E1 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfanE, hcard, h80, hds, hds3, hfsub, hf12, hf23, hf31, hpr1, hpr2,
       hpr3, hvu, huw, hwv, hsigma, hf1u, hf2w, hface1, hface2, hf10, hf20,
       hf30, hE1⟩
  have hθuw : 0 < azim x u w v ∧ azim x u w v < Real.pi := by
    have := h80 u w huw
    rwa [hsigma] at this
  have hcop1 : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθuw.1 hθuw.2
  have hσ_soe : sigmaFan x V E v u ∈ setOfEdge v V E :=
    sigma_fan_in_setOfEdge hfan
      ((properties_of_setOfEdge_fan x V E v u hfan).mp hvu)
  have hσvE : ({sigmaFan x V E v u, v} : Set V3) ∈ E := by
    have h1 : ({v, sigmaFan x V E v u} : Set V3) ∈ E :=
      (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfan).mpr hσ_soe
    rwa [Set.pair_comm] at h1
  have hθs : 0 < azim x v u (sigmaFan x V E v u) ∧
      azim x v u (sigmaFan x V E v u) < Real.pi := h80 v u hvu
  have hcop2 : ¬ Coplanar ({x, sigmaFan x V E v u, v, u} : Set V3) :=
    properties_fully_surrounded (v := sigmaFan x V E v u) (u := v) (w := u)
      hfan hσvE hvu hθs.1 hθs.2
  have hσeq : sigmaFan x V E1 v w = sigmaFan x V E v u :=
    SIGMA_FAN_OF_FANADD_AT_POINT1 x V E E1 v u w
      ⟨hfan, hfan1, hvu, huw, hwv, hsigma, h80, hcard, hE1⟩
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Or.inr (by simp)
  have hσvE1 : ({sigmaFan x V E v u, v} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Or.inl hσvE
  have hθvw : 0 < azim x v w (sigmaFan x V E v u) ∧
      azim x v w (sigmaFan x V E v u) < Real.pi := by
    have := h80E1 v w hvwE1
    rwa [hσeq] at this
  have hcop3 : ¬ Coplanar ({x, sigmaFan x V E v u, v, w} : Set V3) :=
    properties_fully_surrounded (v := sigmaFan x V E v u) (u := v) (w := w)
      hfan1 hσvE1 hvwE1 hθvw.1 hθvw.2
  have hA1 : IsOpen (affGt ({x, u, w} : Set V3) {v}) := by
    apply OPEN_AFF_GT_3_1
    rw [show ({x, u, w, v} : Set V3) = {x, v, u, w} by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop1
  have hA2 : IsOpen (affGt ({x, v, u} : Set V3) {sigmaFan x V E v u}) := by
    apply OPEN_AFF_GT_3_1
    rw [show ({x, v, u, sigmaFan x V E v u} : Set V3) =
        {x, sigmaFan x V E v u, v, u} by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop2
  have hA3 : IsOpen (affGt ({x, v, sigmaFan x V E v u} : Set V3) {w}) := by
    apply OPEN_AFF_GT_3_1
    rw [show ({x, v, sigmaFan x V E v u, w} : Set V3) =
        {x, sigmaFan x V E v u, v, w} by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop3
  have hA4 : IsOpen (affGt ({x, sigmaFan x V E v u, w} : Set V3) {v}) := by
    apply OPEN_AFF_GT_3_1
    rw [show ({x, sigmaFan x V E v u, w, v} : Set V3) =
        {x, sigmaFan x V E v u, v, w} by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop3
  rw [hU]
  exact IsOpen.inter (IsOpen.inter (IsOpen.inter hA1 hA2) hA3) hA4

/-- HOL Conforming.hl :8812-8901 `eq_aff_gt_3_fanadd_edge`

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
==> aff_gt {x, v, u} {sigma_fan x V E v u}= aff_gt {x, v, u} {w}
```

编码说明：`aff_gt` ↦ `affGt`；结论
`affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} =
affGt ({x, v, u} : Set V3) {w}`。

证明思路：由 `fan80` 对 `(v,u)` 与 `(v,sigma_fan x V E v u)` 用
`properties_fully_surrounded` 得两组四点非共面；用
`cross_dot_fully_surrounded_fan` 定两个叉积定向符号，
`aff_gt_3_1_rep_cross_dot` 把左右两个 `affGt` 都化为同一叉积正条件
（`SIGMA_FAN_OF_FANADD_AT_POINT2` 把 `sigma_fan` 换到 `E1` 侧）。

候选已有引理：
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `aff_gt_eq_fanadd`（Kepler/Text/ConformingAuto16.lean:597）
- 缺口：`remark1_fan` 未以该名移植 -/
theorem eq_aff_gt_3_fanadd_edge (x : V3) (V : Set V3)
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
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} =
        affGt ({x, v, u} : Set V3) {w} := by
  sorry

/-- HOL Conforming.hl :8902-8957 `aff_gt_add_subset_U1`

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
/\ U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> aff_gt {x} {v,w} SUBSET U1
```

编码说明：`aff_gt` ↦ `affGt`；`SUBSET` ↦ `⊆`；`U1` 为四 `affGt`
之交。结论 `affGt ({x} : Set V3) {v, w} ⊆ U1`。

证明思路：`eq_aff_gt_3_fanadd_edge` 把 `affGt {x,v,u}{sigma_fan …}` 换成
`affGt {x,v,u}{w}`；`aff_gt_inter_aff_gt` 把 `affGt {x}{v,w}` 化为
`affGt {x,v}{w} ∩ affGt {x,w}{v}`；再用 `AFF_GT_MONO_LEFT`（各分量对
左端集合单调）把 `affGt {x,v}{w}`、`affGt {x,w}{v}` 分别塞进 `U1`
的四个 `affGt` 分量（`SET_TAC` 收口）。

候选已有引理：
- `eq_aff_gt_3_fanadd_edge`（本文件上文）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`（Kepler/Text/ConformingAuto16.lean:1673）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- 缺口：`AFF_GT_MONO_LEFT`、`remark1_fan` 未以该名移植 -/
theorem aff_gt_add_subset_U1 (x : V3) (V : Set V3)
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
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      affGt ({x} : Set V3) {v, w} ⊆ U1 := by
  sorry

/-- HOL Conforming.hl :8958-9007 `lemma_rep_U_fanadd`

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
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\  U1= aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}
==> U= U1 UNION dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；`UNION` ↦
`∪`。结论 `U = U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪
dartsetLeadsIntoFan x V E1 ds2`。

证明思路：`U` 定义中已有两个 `dartsetLeadsIntoFan` 分量，只需把
`affGt {x}{v,w}` 并入 `U1`：`aff_gt_add_subset_U1` 给
`affGt {x}{v,w} ⊆ U1`，`lemmaU1_subset_U` 给 `U1 ⊆ U`，再用集合运算
（`SET_TAC`）证两边互含。

候选已有引理：
- `aff_gt_add_subset_U1`（本文件上文）
- `lemmaU1_subset_U`（本文件上文）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- 缺口：`FANADD_CONFORMING` 的展开按名引用，未逐一桥接 -/
theorem lemma_rep_U_fanadd (x : V3) (V : Set V3)
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
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    U1 = affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} →
      U = U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪
        dartsetLeadsIntoFan x V E1 ds2 := by
  sorry

/-- HOL Conforming.hl :9008-9065 `dartset_leads_into_ds_open_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
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
/\ dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}=U
==> open U
```

编码说明：`open` ↦ `IsOpen`；`U` 为两个 `dartsetLeadsIntoFan` 与
`affGt {x}{v,w}` 之并。结论 `IsOpen U`。

证明思路：`lemma_rep_U_fanadd` 把 `U` 重写为
`U1 ∪ dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2`；
`open_subsetU` 给 `IsOpen U1`；`FANADD_CONFORMING` 与
`ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd` 使两个
`dartsetLeadsIntoFan` 是 `topologicalComponentYfan`，再由
`OPEN_TOPOLOGICAL_COMPONENT_YFAN` 得开；最后两次 `IsOpen.union` 收口。

候选已有引理：
- `lemma_rep_U_fanadd`（本文件上文）
- `open_subsetU`（本文件上文）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `dartset_leads_into_is_topological_component_yfan`（Kepler/Text/PlanarityComponent.lean:535）
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN`（Kepler/Text/ConformingAuto6.lean:317）
- `IsOpen.union`（Mathlib/Topology/Defs/Basic.lean）
- 缺口：`OPEN_TOPOLOGICAL_COMPONENT_YFAN` 的 `E1` 版本按名引用 -/
theorem dartset_leads_into_ds_open_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} = U →
      IsOpen U := by
  sorry

end Kepler.Text
