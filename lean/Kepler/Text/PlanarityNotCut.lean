/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18a.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18a of block 18, planarity.hl:3667-5182):
- `not_cut_inside_fan` (3667): statement setup plus the first small
  branch `t3' = 0 /\ t2' = 0` (HOL :3730-3776) fully proved.
- `[BLOCK18B] planarity.hl:3777-3893` (`t3' = 0`, `t2' <> 0`) and the
  `t2' = 0` sub-branch of `[BLOCK18C]` (planarity.hl:3894-4043,
  `t3' <> 0`; mirror of 18b with `v' <-> w'`, `t2' <-> t3'`) are fully
  proved.
- `[BLOCK18D]` first portion (planarity.hl:4044-4224, the generic case
  `t3' <> 0`, `t2' <> 0`: aff_gt/aff_ge combinations plus the
  non-collinearity chain `~collinear {x,x',w'}`, `~collinear {x,x',v'}`,
  `~collinear {x,x',va}`, `~collinear {x,x',v}`) is fully proved.
- `[BLOCK18D2]` (planarity.hl:4225-4291, the azim case split of the
  generic case: the `0 < azim x x' v w' < pi` branch and the
  `pi < azim x x' v w'` branch, via `exists_cut_small_edges_fan`,
  `aff_gt2_subset_aff_ge`, `sum5_azim_fan` and `aff_gt1_subset_aff_ge`)
  is fully proved.
- `[BLOCK18D3]` (planarity.hl:4289-4810, the `azim x y v w' = 0` sub-case,
  handled in HOL via AZIM_EQ_0/AZIM_EQ_0_ALT followed by the `w' ∈
  aff_gt {x} {v,va}` / `v' ∈ aff_gt {x} {v,va}` splits — coplanar chain +
  `exists_cut_small_edges_fan` endings, then `decomposition_planar_by_
  angle_fan` + `properties_of_fan7`/`properties1_of_fan7` + the fan7
  intersection / singleton-intersection analysis) is fully proved.
- The `azim = pi` sub-case is proved as the private lemma
  `not_cut_inside_fan_azim_pi` (`[BLOCK18D4] planarity.hl:4812-5182`):
  the sum5_azim_fan reduction at HOL :4812-4817 yields
  `azim x y v v' = 0`, after which the case is the azim = 0 branch with
  `v'`/`w'` swapped (HOL :4818-5181 replays :4289-4810 inline), so it
  delegates to `not_cut_inside_fan_azim0`.
- HOL `remark1_fan`/`th3` (fan.hl:388,423) are not yet ported; the
  specific fragments needed here live below as private helpers.

Conventions: HOL line numbers in the head comment of each item; zero
`sorry` outside the marked block-18 markers; `lake env lean` green.
-/
import Kepler.Text.Planarity
import Kepler.Geom.Coplanar

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

variable {x v u w : V3} {V : Set V3} {E : Set (Set V3)} {a : ℝ}

/-! ## `th3`/`remark1_fan` 片段（fan.hl:388,423 未移植，此处只证所需） -/

/-- HOL fan.hl:371 `th3b` 片段：`¬Collinear3 x p q → x ≠ p`。 -/
private theorem not_collinear3_left {x p q : V3} (h : ¬ Collinear3 x p q) :
    x ≠ p := by
  intro he
  subst he
  exact h (collinear3_of_eq rfl)

/-- 首尾同点时三点共线（`Collinear3 x p x`，两点集去重情形）。 -/
private theorem collinear3_first_third (x p : V3) : Collinear3 x p x := by
  show Collinear ℝ ({x, p, x} : Set V3)
  have h2 : ({x, p, x} : Set V3) = {x, p} := by ext z; simp; tauto
  rw [h2]
  exact collinear_pair ℝ x p

/-- HOL fan.hl:373 `th3b1` 片段：`¬Collinear3 x p q → x ≠ q`。 -/
private theorem not_collinear3_right {x p q : V3} (h : ¬ Collinear3 x p q) :
    x ≠ q := by
  intro he
  subst he
  exact h (collinear3_first_third x p)

/-- HOL fan.hl:388 `th3` 片段：`¬Collinear3 x p q → DISJOINT {x} {p,q}`。 -/
private theorem disjoint_singleton_of_not_collinear3 {x p q : V3}
    (h : ¬ Collinear3 x p q) : Disjoint ({x} : Set V3) {p, q} := by
  rw [Set.disjoint_singleton_left]
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with he | he
  · subst he
    exact h (collinear3_of_eq rfl)
  · subst he
    exact h (collinear3_first_third x p)

/-- 三点共线对换后两点（`Collinear3 x p q → Collinear3 x q p`）。 -/
private theorem collinear3_swap {x p q : V3} (h : Collinear3 x p q) :
    Collinear3 x q p := by
  show Collinear ℝ ({x, q, p} : Set V3)
  have h' : Collinear ℝ ({x, p, q} : Set V3) := h
  rw [show ({x, p, q} : Set V3) = ({x, q, p} : Set V3) from by ext z; simp; tauto] at h'
  exact h'

/-- HOL planarity.hl:4099-4224 各非共线子目标的公共模式：若 `y` 与 `x`、`r`
共线（`x ≠ r`），且 `y = c1•x + c2•q + c3•r`（`c1+c2+c3 = 1`，`c2 ≠ 0`），
则 `q ∈ affineSpan {x, r}`（两点表示消去 `y`，孤立 `c2•q` 后除以 `c2`）。 -/
private theorem mem_affineSpan_pair_of_collinear3 {x y q r : V3}
    (hxr : x ≠ r) (hcol : Collinear3 x y r)
    {c1 c2 c3 : ℝ} (hc2 : c2 ≠ 0) (hsum : c1 + c2 + c3 = 1)
    (hyeq : y = c1 • x + c2 • q + c3 • r) :
    q ∈ (affineSpan ℝ ({x, r} : Set V3) : Set V3) := by
  -- 共线给出两点表示：y = (1-s)•x + s•r
  obtain ⟨s, hys⟩ : ∃ s : ℝ, y = (1 - s) • x + s • r := by
    obtain ⟨c, hc⟩ :=
      (collinear3_iff_smul (v := x) (w := r) (w1 := y) (Ne.symm hxr)).mp
        (collinear3_swap hcol)
    exact ⟨c, by rw [sub_eq_iff_eq_add.mp hc]; module⟩
  -- 与三点组合比较，孤立出 c2•q
  have hkey : c2 • q = (1 - s - c1) • x + (s - c3) • r := by
    have e : c1 • x + c2 • q + c3 • r = (1 - s) • x + s • r := by
      rw [← hyeq, hys]
    calc c2 • q
        = (1 - s) • x + s • r - (c1 • x + c3 • r) := by
          rw [← e]
          module
      _ = (1 - s - c1) • x + (s - c3) • r := by
          module
  -- 除以 c2，得到 q 的两点组合（系数和为 1）
  have hq : q = ((1 - s - c1) / c2) • x + ((s - c3) / c2) • r := by
    rw [← inv_smul_smul₀ hc2 q, hkey, smul_add, smul_smul, smul_smul]
    module
  rw [affine_hull_2_fan]
  refine ⟨_, _, ?_, hq⟩
  field_simp
  linarith

/-! ## 主定理（切片 18a） -/

/-- `aff_gt s t ⊆ aff_ge s t`（任意点集版本：sgn `0 < x` 蕴含 `0 ≤ x`）。
HOL 中由 affsign 定义直接可得，用于 AZIM_EQ_0_GE 的成员式弱化。 -/
private theorem affGt_subset_affGe' {s t : Set V3} : affGt s t ⊆ affGe s t := by
  intro z hz
  simp only [affGt, affGe, Set.mem_setOf_eq, Affsign] at hz ⊢
  obtain ⟨f, hfin, hv, hpos, hone⟩ := hz
  exact ⟨f, hfin, hv, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- `aff_ge {x} ∅ = {x}`（HOL planarity.hl 私有引理 `aff_ge_empty_singleton`
的同型复制，planarity_not_cut 自用）。 -/
private theorem affGe_empty' (x : V3) : affGe {x} (∅ : Set V3) = {x} := by
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
    · rw [hTeq]
      simp
    · intro z hz
      simp at hz
    · rw [hTeq]
      simp

set_option maxHeartbeats 20000000 in
/-- `[BLOCK18D3]` 内层 `v = w'` 整链（HOL :4487-4645 与 :4648-4810 两处
共用），从 not_cut_inside_fan_azim0 二次抽出以控制心跳预算。 -/
private theorem not_cut_inside_fan_azim0_veq {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {a : ℝ} {y v' w' : V3}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E) (ha0 : 0 < a) (ha1 : a < 1)
    (he' : {v', w'} ∈ E) (hnc' : ¬ Collinear3 x v' w')
    (hdis' : Disjoint ({x} : Set V3) {v', w'})
    (hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w})
    (hygt' : y ∈ affGt {x} {v', w'}) (hyge' : y ∈ affGe {x} {v', w'})
    (hygt : y ∈ affGt {x} {v, (1 - a) • u + a • w})
    (hncw' : ¬ Collinear3 x y w') (hncv' : ¬ Collinear3 x y v')
    (hncz : ¬ Collinear3 x y ((1 - a) • u + a • w))
    (hncv : ¬ Collinear3 x y v)
    (hxy : x ≠ y) (hncvy : ¬ Collinear3 x v y)
    (hPFS : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hv'gt : ¬ (v' ∈ affGt {x} {v, (1 - a) • u + a • w}))
    (hwveq : v = w') : False := by
  have hπ1 : azim x y v' w' = Real.pi :=
    aff_gt2_subset_aff_ge hdis' hncw' hncv' hygt'
  rw [← hwveq] at hπ1
  have hπ3 : azim x y v v' = Real.pi := by
    rw [azim_compl hncv' hncv,
      if_neg (by rw [hπ1]; exact Real.pi_ne_zero), hπ1]
    ring
  have hπ4 : azim x y v ((1 - a) • u + a • w) = Real.pi :=
    aff_gt2_subset_aff_ge hdis hncz hncv hygt
  have hsum4 := sum4_azim_fan (Ne.symm hxy) hncv hncz hncv'
    (by rw [hπ3, hπ4])
  have hzv'0 : azim x y ((1 - a) • u + a • w) v' = 0 := by linarith
  have hzge : (1 - a) • u + a • w ∈ affGe ({x, y} : Set V3) {v'} :=
    affGt_subset_affGe'
      ((azim_eq_zero_iff hncz hncv').mp hzv'0)
  -- HOL :4484/:4668 第二次 decomposition_planar_by_angle_fan
  rcases decomposition_planar_by_angle_fan hncv' hncz hzge with h19a | h19b
  · -- 块 19a（:4487-4491）：v' ∈ aff_gt {x} {y,z} 传回 aff_gt 矛盾
    -- 修正（非纯代码移动）：aff_gt1 此处需 ¬Collinear3 x y z（hncz），
    -- 原文误传 hncvy（该项从未通过编译，40M 心跳亦未到达此行）
    exact absurd (aff_gt1_subset_aff_gt hdis hncz hygt h19a) hv'gt
  · -- 块 19b + 20 + 21 + 22（:4492-4555 与 :4687-4810）
    have hsetwv : ({v', w'} : Set V3) = ({w', v'} : Set V3) := by
      ext q; simp; tauto
    have hdis2 : Disjoint ({x} : Set V3) {w', v'} := by
      rw [← hsetwv]; exact hdis'
    have hyge2 : y ∈ affGe {x} {w', v'} := by
      rw [← hsetwv]; exact hyge'
    have hz19 : (1 - a) • u + a • w ∈ affGe {x} {w', v'} :=
      aff_ge1_subset_aff_ge hdis2 hncv' hyge2 h19b
    -- 块 20（:4501-4525）：va ∈ aff_ge {x} {u,w}（见证 0,1-a,a）
    have hdisuw : Disjoint ({x} : Set V3) {u, w} :=
      disjoint_singleton_of_not_collinear3 (fan_not_collinear hfan huw)
    have hz20 : (1 - a) • u + a • w ∈ affGe {x} {u, w} := by
      rw [aff_ge_1_2 hdisuw]
      exact ⟨0, 1 - a, a, by linarith, by linarith, by ring, by module⟩
    -- fan7 相交（HOL :4528-4534）
    have h77 : affGe {x} ({u, w} : Set V3) ∩ affGe {x} {v', w'}
        = affGe {x} (({u, w} ∩ {v', w'} : Set V3)) :=
      hfan.2.2.2.2.2 {u, w} (Or.inl huw) {v', w'} (Or.inl he')
    have hzS : (1 - a) • u + a • w
        ∈ affGe {x} (({u, w} ∩ {v', w'} : Set V3)) := by
      rw [← h77]
      exact (Set.mem_inter_iff _ _ _).mpr ⟨hz20, by rw [hsetwv]; exact hz19⟩
    by_cases hI : ({u, w} ∩ {v', w'} : Set V3) = {u, w}
    · -- 块 21a（:4527-4556）：{v',w'} = {u,w}，v ∈ 交的
      -- aff_ge {x} {u,w}，与 fully_surrounded 不共面矛盾
      have hu'vw : u ∈ ({v', w'} : Set V3) := by
        have huS : u ∈ ({u, w} ∩ {v', w'} : Set V3) := by
          rw [hI]; simp
        exact ((Set.mem_inter_iff _ _ _).mp huS).2
      have hw'vw : w ∈ ({v', w'} : Set V3) := by
        have hwS : w ∈ ({u, w} ∩ {v', w'} : Set V3) := by
          rw [hI]; simp
        exact ((Set.mem_inter_iff _ _ _).mp hwS).2
      have huwne : u ≠ w := fun he =>
        fan_not_collinear hfan huw (collinear3_pair_right he.symm)
      have hv'w'ne : v' ≠ w' := fun he =>
        hnc' (collinear3_pair_right he.symm)
      -- {v',w'} = {u,w}（两种对位之一）
      have hkey : (v' = u ∧ w' = w) ∨ (v' = w ∧ w' = u) := by
        have h1 : u = v' ∨ u = w' := by
          simpa using hu'vw
        have h2 : w = v' ∨ w = w' := by
          simpa using hw'vw
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) huwne
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
        · exact absurd (h1.trans h2.symm) huwne
      -- v ∈ aff_ge {x} {v',w'}：由 w' ∈ 该集（point_in_aff_ge）
      -- 与 v = w' 换点（集合不参与改写）
      have hw'aff : w' ∈ affGe {x} {v', w'} := (point_in_aff_ge hnc').2.2
      have hvwaff : ∀ S : Set V3, w' ∈ S → v ∈ S := by
        intro S hS
        rw [hwveq]
        exact hS
      have hvmem : v ∈ affGe {x} {v', w'} := hvwaff _ hw'aff
      have hset_eq : ({v', w'} : Set V3) = {u, w} := by
        rcases hkey with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2]; ext q; simp; tauto
      rw [hset_eq] at hvmem
      -- v ∈ aff_ge {x} {u,w} 的系数分解 + 共面矛盾
      rw [aff_ge_1_2 hdisuw] at hvmem
      obtain ⟨c1, c2, c3, hc2, hc3, hcsum, hveq2⟩ := hvmem
      refine hPFS ⟨x, u, w, ?_⟩
      intro q hq2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq2
      rcases hq2 with rfl | hqv | rfl | rfl
      · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
      · -- q = v：两次 lineMap 组合出三点仿射包成员
        rw [hqv]
        rcases eq_or_lt_of_le (add_nonneg hc2 hc3) with hcc | hcc
        · have hcc0 : c2 + c3 = 0 := hcc.symm
          rw [show c2 = 0 by linarith, show c3 = 0 by linarith] at hveq2
          rw [hveq2, show c1 = 1 by linarith, one_smul]
          exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
        · have hqm : AffineMap.lineMap u w (c3 / (c2 + c3))
              ∈ (affineSpan ℝ ({x, u, w} : Set V3) : Set V3) :=
            AffineMap.lineMap_mem (c3 / (c2 + c3))
              (SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp)))
              (SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp)))
          have hvm : AffineMap.lineMap
              x (AffineMap.lineMap u w (c3 / (c2 + c3))) (c2 + c3)
              ∈ (affineSpan ℝ ({x, u, w} : Set V3) : Set V3) :=
            AffineMap.lineMap_mem (c2 + c3)
              (SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))) hqm
          have hvleq : v = AffineMap.lineMap
              x (AffineMap.lineMap u w (c3 / (c2 + c3))) (c2 + c3) := by
            have hs23 : (c2 + c3 : ℝ) ≠ 0 := ne_of_gt hcc
            have hkey : (c2 + c3) * (c3 / (c2 + c3)) = c3 := by field_simp
            have hrw : (c2 + c3) • ((c3 / (c2 + c3)) • (w - u) + u - x) + x
                = (1 - c2 - c3) • x + c2 • u + c3 • w := by
              rw [smul_sub, smul_add, smul_smul, hkey]
              module
            rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply,
              vsub_eq_sub, vadd_eq_add, vsub_eq_sub, vadd_eq_add, hveq2,
              show c1 = 1 - c2 - c3 by linarith, hrw]
          rw [hvleq]
          exact hvm
      · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
      · exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
    · -- 块 21b + 22（:4557-4645 与 :4740-4810）：交集为真子集
      by_cases huS : u ∈ ({u, w} ∩ {v', w'} : Set V3)
      · -- w ∉ 交集，故交集 = {u}（块 22b 镜像）：
        -- va ∈ aff_ge {x} {u} ⟹ u ∈ aff {x,w} 矛盾
        have hwS : w ∉ ({u, w} ∩ {v', w'} : Set V3) := by
          intro hwS
          refine hI ?_
          ext q
          simp only [Set.mem_inter_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩
            rcases h1 with h3 | h3
            · exact Or.inl h3
            · exact Or.inr h3
          · rintro (rfl | rfl)
            · exact ⟨by simp, ((Set.mem_inter_iff _ _ _).mp huS).2⟩
            · exact ⟨by simp, ((Set.mem_inter_iff _ _ _).mp hwS).2⟩
        have hSu : ({u, w} ∩ {v', w'} : Set V3) = {u} := by
          apply Set.eq_singleton_iff_unique_mem.mpr
          refine ⟨huS, ?_⟩
          intro q hq
          rcases Set.mem_insert_iff.mp ((Set.mem_inter_iff _ _ _).mp hq).1 with
            hq2 | hq2
          · exact hq2
          · exact absurd (hq2 ▸ hq) hwS
        rw [hSu] at hzS
        obtain ⟨d1, d2, hd2, hdsum, hzeq⟩ :=
          (mem_affGe_singleton
            (not_collinear3_left (fan_not_collinear hfan huw))).mp hzS
        -- (1-a)•u + a•w = d1•x + d2•u ⟹ w ∈ aff {x,u} 矛盾
        have haw : a • w = d1 • x + (d2 - 1 + a) • u := by
          calc a • w = ((1 - a) • u + a • w) - (1 - a) • u := by module
            _ = (d1 • x + d2 • u) - (1 - a) • u := by rw [hzeq]
            _ = d1 • x + (d2 - 1 + a) • u := by module
        have hww : w = (a⁻¹ * d1) • x
            + (a⁻¹ * (d2 - 1 + a)) • u := by
          calc w = a⁻¹ • (a • w) := (inv_smul_smul₀ (ne_of_gt ha0) _).symm
            _ = a⁻¹ • (d1 • x + (d2 - 1 + a) • u) := by rw [haw]
            _ = (a⁻¹ * d1) • x + (a⁻¹ * (d2 - 1 + a)) • u := by
              rw [smul_add, smul_smul, smul_smul]
        have hwwmem : w ∈ (affineSpan ℝ ({x, u} : Set V3) : Set V3) := by
          rw [affine_hull_2_fan]
          refine ⟨_, _, ?_, hww⟩
          field_simp
          linarith
        exact fan_not_collinear hfan huw
          ((collinear3_iff_mem_affineSpan
            (not_collinear3_left (fan_not_collinear hfan huw))).mpr hwwmem)
      · by_cases hwS : w ∈ ({u, w} ∩ {v', w'} : Set V3)
        · -- 交集 = {w}（块 22b）：va ∈ aff_ge {x} {w} ⟹
          -- u ∈ aff {x,w} 矛盾
          have hSw : ({u, w} ∩ {v', w'} : Set V3) = {w} := by
            apply Set.eq_singleton_iff_unique_mem.mpr
            refine ⟨hwS, ?_⟩
            intro q hq
            rcases Set.mem_insert_iff.mp ((Set.mem_inter_iff _ _ _).mp hq).1 with
              hq2 | hq2
            · exact absurd (hq2 ▸ hq) huS
            · exact hq2
          rw [hSw] at hzS
          obtain ⟨d1, d2, hd2, hdsum, hzeq⟩ :=
            (mem_affGe_singleton
              (not_collinear3_right (fan_not_collinear hfan huw))).mp hzS
          have hxune : 1 - a ≠ 0 := by linarith
          have hukey : (1 - a) • u = d1 • x + (d2 - a) • w := by
            calc (1 - a) • u = ((1 - a) • u + a • w) - a • w := by module
              _ = (d1 • x + d2 • w) - a • w := by rw [hzeq]
              _ = d1 • x + (d2 - a) • w := by module
          have huum : u = ((1 - a)⁻¹ * d1) • x
              + ((1 - a)⁻¹ * (d2 - a)) • w := by
            calc u = (1 - a)⁻¹ • ((1 - a) • u) :=
                (inv_smul_smul₀ hxune _).symm
              _ = (1 - a)⁻¹ • (d1 • x + (d2 - a) • w) := by rw [hukey]
              _ = ((1 - a)⁻¹ * d1) • x + ((1 - a)⁻¹ * (d2 - a)) • w := by
                rw [smul_add, smul_smul, smul_smul]
          have huumem : u ∈ (affineSpan ℝ ({x, w} : Set V3) : Set V3) := by
            rw [affine_hull_2_fan]
            exact ⟨_, _, by field_simp; linarith, huum⟩
          exact fan_not_collinear hfan huw
            (collinear3_swap ((collinear3_iff_mem_affineSpan
              (not_collinear3_right (fan_not_collinear hfan huw))).mpr huumem))
        · -- 交集 = ∅：va = x 与 ¬Collinear3 x y va 矛盾
          have hSe : ({u, w} ∩ {v', w'} : Set V3) = ∅ := by
            by_contra hne
            obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hne
            rcases Set.mem_insert_iff.mp ((Set.mem_inter_iff _ _ _).mp hq).1 with
              hq2 | hq2
            · exact huS (hq2 ▸ hq)
            · exact hwS (hq2 ▸ hq)
          rw [hSe, affGe_empty' x] at hzS
          have hzx : (1 - a) • u + a • w = x :=
            Set.mem_singleton_iff.mp hzS
          exact hncz (by rw [hzx]; exact collinear3_first_third x y)

set_option maxHeartbeats 12000000 in
/-- `[BLOCK18D3]`（planarity.hl:4289-4810）`azim x y v w' = 0` 支，从
not_cut_inside_fan 抽出（心跳预算独立控制）。假设即主定理分支处的全部
局部事实；结论为该支的目标 False。 -/
private theorem not_cut_inside_fan_azim0 {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {a : ℝ} {y v' w' : V3}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hEM : ∀ h : ℝ, 0 < h → h < a →
      affGt {x} {v, (1 - h) • u + h • w} ∩
        {z | ∃ e, e ∈ E ∧ z ∈ affGe {x} e} = ∅)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (he' : {v', w'} ∈ E) (hnc' : ¬ Collinear3 x v' w')
    (hdis' : Disjoint ({x} : Set V3) {v', w'})
    (hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w})
    (hygt' : y ∈ affGt {x} {v', w'}) (hyge' : y ∈ affGe {x} {v', w'})
    (hygt : y ∈ affGt {x} {v, (1 - a) • u + a • w})
    (hncw' : ¬ Collinear3 x y w') (hncv' : ¬ Collinear3 x y v')
    (hncz : ¬ Collinear3 x y ((1 - a) • u + a • w))
    (hncv : ¬ Collinear3 x y v)
    (h0 : azim x y v w' = 0) : False := by
  · -- HOL :4289-4810（azim x y v w' = 0）
    -- :4289-4292 AZIM_EQ_0 / AZIM_EQ_0_ALT 的成员式结论
    -- （AZIM_EQ_0_GE 即其 aff_ge 弱化）
    have hvw' : v ∈ affGt {x, y} {w'} := (azim_eq_zero_iff hncv hncw').mp h0
    have hw'v : w' ∈ affGt {x, y} {v} := (azim_eq_zero_iff_alt hncv hncw').mp h0
    have hw'v' : w' ∈ affGe ({x, y} : Set V3) {v} := affGt_subset_affGe' hw'v
    -- 公共事实（各块反复使用）
    have hxy : x ≠ y := fun he => hncv (collinear3_of_eq he.symm)
    have hncvy : ¬ Collinear3 x v y := fun h => hncv (collinear3_swap h)
    have hPFS : ¬ Coplanar ({x, v, u, w} : Set V3) :=
      properties_fully_surrounded hfan hvu huw hθ0 hθπ
    have hncop1 : ¬ Coplanar ({x, v, u, (1 - a) • u + a • w} : Set V3) :=
      continuous_coplanar_fan x v u w hPFS a (ne_of_gt ha0)
    have hncop2 : ¬ Coplanar ({x, u, v, (1 - a) • u + a • w} : Set V3) := by
      intro hc
      apply hncop1
      have hset : ({x, u, v, (1 - a) • u + a • w} : Set V3)
          = ({x, v, u, (1 - a) • u + a • w} : Set V3) := by ext q; simp; tauto
      rw [← hset]
      exact hc
    -- HOL :4293：按 w' ∈ aff_gt {x} {v,va} 分情况
    by_cases hw'gt : w' ∈ affGt {x} {v, (1 - a) • u + a • w}
    · -- HOL :4294-4367（块 14：w' ∈ aff_gt {x} {v,va}）
      -- AFF_GT_1_2 分解（"DICH CHUYEN"）
      have hw'gt2 := hw'gt
      rw [aff_gt_1_2 hdis] at hw'gt2
      obtain ⟨s1, s2, s3, hs2, hs3, hssum, hw'eq⟩ := hw'gt2
      have hsm : 0 < s2 + s3 := add_pos hs2 hs3
      -- 不共面链：VA 点换内点后经 x—w' 直线传入平面（HOL 的
      -- COPLANAR_TRANSLATION_EQ + COPLANAR_SCALE_ALL）
      have hc0 : 0 < s3 / (s2 + s3) := div_pos hs3 hsm
      have hncop3 : ¬ Coplanar ({x, u, v,
          (1 - s3 / (s2 + s3)) • v + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)} :
          Set V3) :=
        continuous_coplanar_fan x u v ((1 - a) • u + a • w) hncop2
          (s3 / (s2 + s3)) (ne_of_gt hc0)
      have hw'x : w' - x = s2 • (v - x)
          + s3 • (((1 - a) • u + a • w) - x) := by
        have hs1 : s1 = 1 - s2 - s3 := by linarith
        rw [hw'eq, hs1]; module
      have hq : (1 - s3 / (s2 + s3)) • v
          + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)
          = x + (s2 + s3)⁻¹ • (w' - x) := by
        rw [hw'x]
        rw [show s2 • (v - x) + s3 • (((1 - a) • u + a • w) - x)
            = s2 • v + s3 • ((1 - a) • u + a • w) - (s2 + s3) • x from by module]
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hsm), one_smul]
        rw [show x + ((s2 + s3)⁻¹ • (s2 • v + s3 • ((1 - a) • u + a • w)) - x)
            = (s2 + s3)⁻¹ • (s2 • v + s3 • ((1 - a) • u + a • w)) from by abel]
        rw [smul_add, smul_smul, smul_smul]
        have hc2 : 1 - s3 / (s2 + s3) = (s2 + s3)⁻¹ * s2 := by
          field_simp
          ring
        have hc3 : s3 / (s2 + s3) = (s2 + s3)⁻¹ * s3 := by
          rw [div_eq_inv_mul, mul_comm]
        rw [hc2, hc3]; module
      have hncvxu : ¬ Coplanar ({x, u, v, w'} : Set V3) := by
        intro hc4
        obtain ⟨o1, o2, o3, hsub⟩ := hc4
        have hxo : x ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
          hsub (by simp)
        have huo : u ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
          hsub (by simp)
        have hvo : v ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
          hsub (by simp)
        have hw'o : w' ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
          hsub (by simp)
        have hqo : (1 - s3 / (s2 + s3)) • v
            + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)
            ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := by
          have hL := AffineMap.lineMap_mem ((s2 + s3)⁻¹ * (1 : ℝ)) hxo hw'o
          rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mul_one, add_comm] at hL
          rw [hq]
          exact hL
        refine hncop3 ⟨o1, o2, o3, ?_⟩
        intro q hq2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq2
        rcases hq2 with rfl | rfl | rfl | rfl
        · exact hxo
        · exact huo
        · exact hvo
        · exact hqo
      -- HOL :4348-4367：半空间元素 + 切边引理 + EM 收尾
      obtain ⟨-, hw'V⟩ := fan_mem_of_edge hfan he'
      have hncop4 : ¬ Coplanar ({x, w', v, u} : Set V3) := by
        intro hc
        apply hncvxu
        have hset : ({x, w', v, u} : Set V3) = ({x, u, v, w'} : Set V3) := by
          ext q; simp; tauto
        rw [← hset]
        exact hc
      obtain ⟨u', hu'E, hu'0, hu'π⟩ :=
        exists_element_in_half_sapace_fan x w' v u V E hfan hw'V hncop4
          (hcard w' hw'V) hfan80
      have hncwu' : ¬ Collinear3 x w' u' := fan_not_collinear hfan hu'E
      obtain ⟨t, ht0, htlt1, hpm⟩ :=
        exists_cut_small_edges_fan (v1 := w') (u1 := u') hfan hvu huw hsigma ha0
          ha1 hfan80 hncwu' hw'gt hu'0 hu'π
      obtain ⟨p, hp⟩ := hpm
      rw [Set.mem_inter_iff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have h1t : 0 < 1 - t := by linarith
      have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
      have h'1 : (1 - t) * a < a := by
        have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
        rwa [one_mul] at hm
      -- 向量恒等式（HOL "YEU" 处的 VECTOR_ARITH）
      have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
          = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
      have hp1' : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} :=
        by
        rw [hid]
        exact hp1
      have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} :=
        ⟨{w', u'}, hu'E,
          aff_gt_subset_aff_ge (disjoint_singleton_of_not_collinear3 hncwu') hp2⟩
      have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
          ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
      rw [hEM ((1 - t) * a) h'0 h'1] at hfin
      simp at hfin
    · by_cases hv'gt : v' ∈ affGt {x} {v, (1 - a) • u + a • w}
      · -- HOL :4369-4443（块 15：v' ∈ aff_gt {x} {v,va}，块 14 的镜像）
        have hv'gt2 := hv'gt
        rw [aff_gt_1_2 hdis] at hv'gt2
        obtain ⟨s1, s2, s3, hs2, hs3, hssum, hv'eq⟩ := hv'gt2
        have hsm : 0 < s2 + s3 := add_pos hs2 hs3
        have hc0 : 0 < s3 / (s2 + s3) := div_pos hs3 hsm
        have hncop3 : ¬ Coplanar ({x, u, v,
            (1 - s3 / (s2 + s3)) • v + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)}:
            Set V3) :=
          continuous_coplanar_fan x u v ((1 - a) • u + a • w) hncop2
            (s3 / (s2 + s3)) (ne_of_gt hc0)
        have hv'x : v' - x = s2 • (v - x)
            + s3 • (((1 - a) • u + a • w) - x) := by
          have hs1 : s1 = 1 - s2 - s3 := by linarith
          rw [hv'eq, hs1]; module
        have hq : (1 - s3 / (s2 + s3)) • v
            + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)
            = x + (s2 + s3)⁻¹ • (v' - x) := by
          rw [hv'x]
          rw [show s2 • (v - x) + s3 • (((1 - a) • u + a • w) - x)
              = s2 • v + s3 • ((1 - a) • u + a • w) - (s2 + s3) • x from by module]
          rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hsm), one_smul]
          rw [show x + ((s2 + s3)⁻¹ • (s2 • v + s3 • ((1 - a) • u + a • w)) - x)
              = (s2 + s3)⁻¹ • (s2 • v + s3 • ((1 - a) • u + a • w)) from by abel]
          rw [smul_add, smul_smul, smul_smul]
          have hc2 : 1 - s3 / (s2 + s3) = (s2 + s3)⁻¹ * s2 := by
            field_simp
            ring
          have hc3 : s3 / (s2 + s3) = (s2 + s3)⁻¹ * s3 := by
            rw [div_eq_inv_mul, mul_comm]
          rw [hc2, hc3]; module
        have hncvxu : ¬ Coplanar ({x, u, v, v'} : Set V3) := by
          intro hc4
          obtain ⟨o1, o2, o3, hsub⟩ := hc4
          have hxo : x ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
            hsub (by simp)
          have huo : u ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
            hsub (by simp)
          have hvo : v ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
            hsub (by simp)
          have hv'o : v' ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) :=
            hsub (by simp)
          have hqo : (1 - s3 / (s2 + s3)) • v
              + (s3 / (s2 + s3)) • ((1 - a) • u + a • w)
              ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := by
            have hL := AffineMap.lineMap_mem ((s2 + s3)⁻¹ * (1 : ℝ)) hxo hv'o
            rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mul_one, add_comm] at hL
            rw [hq]
            exact hL
          refine hncop3 ⟨o1, o2, o3, ?_⟩
          intro q hq2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq2
          rcases hq2 with rfl | rfl | rfl | rfl
          · exact hxo
          · exact huo
          · exact hvo
          · exact hqo
        -- HOL :4424-4443：半空间元素 + 切边引理 + EM 收尾
        obtain ⟨hv'V, -⟩ := fan_mem_of_edge hfan he'
        have hncop4 : ¬ Coplanar ({x, v', v, u} : Set V3) := by
          intro hc
          apply hncvxu
          have hset : ({x, v', v, u} : Set V3) = ({x, u, v, v'} : Set V3) := by
            ext q; simp; tauto
          rw [← hset]
          exact hc
        obtain ⟨u', hu'E, hu'0, hu'π⟩ :=
          exists_element_in_half_sapace_fan x v' v u V E hfan hv'V hncop4
            (hcard v' hv'V) hfan80
        have hncvu' : ¬ Collinear3 x v' u' := fan_not_collinear hfan hu'E
        obtain ⟨t, ht0, htlt1, hpm⟩ :=
          exists_cut_small_edges_fan (v1 := v') (u1 := u') hfan hvu huw hsigma
            ha0 ha1 hfan80 hncvu' hv'gt hu'0 hu'π
        obtain ⟨p, hp⟩ := hpm
        rw [Set.mem_inter_iff] at hp
        obtain ⟨hp1, hp2⟩ := hp
        have h1t : 0 < 1 - t := by linarith
        have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
        have h'1 : (1 - t) * a < a := by
          have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
          rwa [one_mul] at hm
        have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
            = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
        have hp1' : p ∈
            affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} := by
          rw [hid]
          exact hp1
        have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} :=
          ⟨{v', u'}, hu'E,
            aff_gt_subset_aff_ge (disjoint_singleton_of_not_collinear3 hncvu') hp2⟩
        have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
            ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
        rw [hEM ((1 - t) * a) h'0 h'1] at hfin
        simp at hfin
      · -- HOL :4444-4645（块 16-22：w'、v' 均不在 aff_gt {x} {v,va}）
        -- 块 16（:4444-4453）：¬(w' ∈ aff_gt {x} {y,v})，经
        -- aff_gt3_subset_aff_gt 与 hygt 传回 aff_gt {x} {v,va}
        have h16 : ¬ (w' ∈ affGt {x} {y, v}) := by
          intro hmem
          have hset : ({y, v} : Set V3) = ({v, y} : Set V3) := by
            ext q; simp; tauto
          rw [hset] at hmem
          exact hw'gt (aff_gt3_subset_aff_gt hdis hncvy hygt hmem)
        -- v = w' 情形整链（HOL :4487-4645 与 :4648-4810 两处共用）：
        -- π 角追逐 + decomposition_planar_by_angle_fan + fan7 相交
        have hveq_case : v = w' → False :=
          not_cut_inside_fan_azim0_veq hfan hvu huw ha0 ha1 he' hnc' hdis' hdis
            hygt' hyge' hygt hncw' hncv' hncz hncv hxy hncvy hPFS hv'gt
        -- 块 17（:4454-4457）：decomposition_planar_by_angle_fan
        rcases decomposition_planar_by_angle_fan hncv hncw' hw'v' with h17a | h17b
        · -- 块 17a/18（:4458-4486）：v ∈ aff_gt {x} {y,w'}
          have hvge : v ∈ affGe {x} {v', w'} :=
            aff_gt1_subset_aff_ge hdis' hncw' hyge' h17a
          rcases properties_of_fan7 hfan hvu he' hvge with hvv' | hvw'2
          · -- 块 18a（:4465-4476）：v = v' 与 azim = 0/π 矛盾
            have hπ2 : azim x y v' w' = Real.pi :=
              aff_gt2_subset_aff_ge hdis' hncw' hncv' hygt'
            rw [← hvv'] at hπ2
            linarith [Real.pi_pos, hπ2]
          · -- 块 18b（:4477-4645）：v = w'
            exact hveq_case hvw'2
        · -- 块 17b（:4641-4810）：w' ∈ aff_ge {x} {v,y} 拆开
          have h17b' : w' ∈ affGe {x} {v, y} := by
            rw [show ({v, y} : Set V3) = ({y, v} : Set V3) from by
              ext q; simp; tauto]
            exact h17b
          rcases (Set.mem_union _ _ _).mp
            (aff_ge_subset_aff_gt_union_aff_ge hncvy h17b') with hB1 | hB2
          · -- B1：w' ∈ aff_gt {x,v} {y} 与 w' ∈ aff_gt {x,y} {v}
            -- 合成 aff_gt {x} {y,v}，抵触块 16
            exact h16 (by
              rw [aff_gt_inter_aff_gt hncv]
              exact ⟨hw'v, hB1⟩)
          · -- B2（:4636-4647）：w' ∈ aff_ge {x} {v}，经
            -- properties1_of_fan7 得 w' = v，归入 hveq_case
            have he2 : ({w', v'} : Set V3) ∈ E := by
              rw [show ({w', v'} : Set V3) = ({v', w'} : Set V3) from by
                ext q; simp; tauto]
              exact he'
            exact hveq_case (properties1_of_fan7 hfan he2 hvu hB2).symm

/-- `[BLOCK18D4]`（planarity.hl:4812-5182）`azim x y v w' = π` 支
（v 与 w' 角色对换的镜像），假设同 not_cut_inside_fan_azim0。 -/
private theorem not_cut_inside_fan_azim_pi {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {a : ℝ} {y v' w' : V3}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a) (ha1 : a < 1)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hEM : ∀ h : ℝ, 0 < h → h < a →
      affGt {x} {v, (1 - h) • u + h • w} ∩
        {z | ∃ e, e ∈ E ∧ z ∈ affGe {x} e} = ∅)
    (hθ0 : 0 < azim x u w v) (hθπ : azim x u w v < Real.pi)
    (he' : {v', w'} ∈ E) (hnc' : ¬ Collinear3 x v' w')
    (hdis' : Disjoint ({x} : Set V3) {v', w'})
    (hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w})
    (hygt' : y ∈ affGt {x} {v', w'}) (hyge' : y ∈ affGe {x} {v', w'})
    (hygt : y ∈ affGt {x} {v, (1 - a) • u + a • w})
    (hncw' : ¬ Collinear3 x y w') (hncv' : ¬ Collinear3 x y v')
    (hncz : ¬ Collinear3 x y ((1 - a) • u + a • w))
    (hncv : ¬ Collinear3 x y v)
    (hπ : azim x y v w' = Real.pi) : False := by
  -- HOL :4812-4817（π 支的归约，"CUOI"+sum5_azim_fan）：由
  -- y ∈ aff_gt {x} {v',w'} 得 azim x y v' w' = π（aff_gt2_subset_aff_ge，
  -- 即 HOL 的 AZIM_EQ_PI 路线），与 hπ 经 sum5_azim_fan 相加得
  -- azim x y v v' = 0。此后 :4818-5181 是 azim = 0 支（:4289-4810）在
  -- v' 与 w' 角色对换下的逐行重放（HOL 未抽引理故整段复制），此处直接
  -- 调用已抽出的 not_cut_inside_fan_azim0（v' ↦ w'，w' ↦ v'）。
  have hxy : x ≠ y := fun he => hncv (by rw [he]; exact collinear3_of_eq rfl)
  have hπ' : azim x y v' w' = Real.pi :=
    aff_gt2_subset_aff_ge hdis' hncw' hncv' hygt'
  have hsum := sum5_azim_fan hxy.symm hncv hncv' hncw' (by rw [hπ', hπ])
  -- hsum : azim x y v w' = azim x y v v' + azim x y v' w'
  have h0' : azim x y v v' = 0 := by
    rw [hπ, hπ'] at hsum
    linarith
  -- 共用集合对换 {w', v'} = {v', w'}
  have hswap : ({w', v'} : Set V3) = ({v', w'} : Set V3) := by
    ext q; simp; tauto
  exact not_cut_inside_fan_azim0 (v' := w') (w' := v') hfan hvu huw hsigma ha0 ha1
    hcard hfan80 hEM hθ0 hθπ
    (by rw [hswap]; exact he')
    (fun h => hnc' (collinear3_swap h))
    (by rw [hswap]; exact hdis')
    hdis
    (by rw [hswap]; exact hygt')
    (by rw [hswap]; exact hyge')
    hygt hncv' hncw' hncz hncv h0'

/-- HOL planarity.hl:3667 `not_cut_inside_fan`（`t3' = t2' = 0`
（:3730-3776）、`[BLOCK18B]`（`t3' = 0`，`t2' ≠ 0`，:3777-3893）、
`[BLOCK18C]` 的 `t2' = 0` 子分支（`t3' ≠ 0`，:3894-4043，18b 的镜像）
以及 `[BLOCK18D]` 首段（一般情形 `t2' ≠ 0` 且 `t3' ≠ 0` 的 aff 组合与
非共线链，:4044-4224）均完整证明；`[BLOCK18D2]`（azim 分情况之
`0 < azim < π` 与 `π < azim` 两支，:4225-4291）亦完整证明；
`[BLOCK18D3]`（`azim x y v w' = 0` 支，:4289-4810：w'/v' ∈ aff_gt 两半
的不共面链 + 切边收尾，与双否半支的 decomposition_planar_by_angle_fan +
fan7 相交分析）完整证明（抽出为私有引理 not_cut_inside_fan_azim0）；
`[BLOCK18D4]`（`azim x y v w' = π` 支，:4812-5182）完整证明（私有引理
not_cut_inside_fan_azim_pi：sum5_azim_fan 归约得 `azim x y v v' = 0` 后
调用 not_cut_inside_fan_azim0，v'/w' 对换）。零 sorry。 -/
theorem not_cut_inside_fan (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hsigma : sigmaFan x V E u w = v) (ha0 : 0 < a)
    (ha1 : a < 1) (hcard : ∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard)
    (hfan80 : fan80 x V E)
    (hEM : ∀ h : ℝ, 0 < h → h < a →
      affGt {x} {v, (1 - h) • u + h • w} ∩
        {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} = ∅) :
    affGt {x} {v, (1 - a) • u + a • w} ∩
      {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} = ∅ := by
  -- fan80 + sigma_fan 给出 azim 界（HOL :3702 REWRITE_TAC[fan80] 后取 u,w）
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  -- HOL :3707 not_collinear_is_properties_fully_surrounded
  have hnc : ¬ Collinear3 x v ((1 - a) • u + a • w) :=
    not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ a ha0 ha1
  have hxv : x ≠ v := not_collinear3_left hnc
  -- HOL :3691 INTER/EXTENSION/IN_ELIM_THM + EQ_TAC：化为逐点矛盾
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  obtain ⟨hy, e, he, hye⟩ := hy
  -- HOL :3694 expand_edge_graph_fan：e = {v', w'}
  obtain ⟨v', w', hve⟩ := expand_edge_graph_fan hfan he
  rw [hve] at hye
  have he' : {v', w'} ∈ E := by rw [← hve]; exact he
  -- HOL :3708 remark1_fan 片段（fan6 的直接推论）
  have hnc' : ¬ Collinear3 x v' w' := fan_not_collinear hfan he'
  have hdis' : Disjoint ({x} : Set V3) {v', w'} :=
    disjoint_singleton_of_not_collinear3 hnc'
  -- HOL :3713 AFF_GE_1_2
  rw [aff_ge_1_2 hdis'] at hye
  obtain ⟨t1', t2', t3', ht2'0, ht3'0, hsum', hyeq'⟩ := hye
  -- HOL :3715 AFF_GT_1_2（Disjoint {x} {v,z} 由 :3707 非共线得出）
  have hdis : Disjoint ({x} : Set V3) {v, (1 - a) • u + a • w} :=
    disjoint_singleton_of_not_collinear3 hnc
  rw [aff_gt_1_2 hdis] at hy
  obtain ⟨t1, t2, t3, ht20, ht30, hsum, hyeq⟩ := hy
  -- HOL :3723 分情况：t3' = 0
  by_cases ht3z : t3' = 0
  · subst ht3z
    -- HOL :3728 再分：t2' = 0
    by_cases ht2z : t2' = 0
    · -- HOL :3730-3776：本切片完整证明
      subst ht2z
      have ht1'1 : t1' = 1 := by linarith
      have hyx : y = x := by rw [hyeq', ht1'1]; simp
      -- 两个分解合并：t3 • (z - x) = (-t2) • (v - x)，z = (1-a)•u + a•w
      have e1 : t3 • ((1 - a) • u + a • w) + t2 • v = y - t1 • x := by
        rw [hyeq]; module
      have hlt : 1 - t1 = t2 + t3 := by linarith
      have e2 : y - t1 • x = (t2 + t3) • x := by rw [hyx, ← hlt]; module
      have hcomb : t3 • ((1 - a) • u + a • w) + t2 • v = t2 • x + t3 • x := by
        rw [e1, e2, add_smul]
      have h0 : t3 • ((1 - a) • u + a • w - x) + t2 • (v - x) = 0 := by
        have hexp : t3 • ((1 - a) • u + a • w - x) + t2 • (v - x)
            = (t3 • ((1 - a) • u + a • w) + t2 • v) - (t2 • x + t3 • x) := by
          rw [smul_sub, smul_sub]; abel
        rw [hexp, hcomb, sub_self]
      have ht3ne : t3 ≠ 0 := ne_of_gt ht30
      -- t3 ≠ 0 除过去：z - x = (t3⁻¹ * (-t2)) • (v - x)
      have hz : (1 - a) • u + a • w - x = (t3⁻¹ * (-t2)) • (v - x) := by
        have hkey : t3 • ((1 - a) • u + a • w - x) = -(t2 • (v - x)) :=
          eq_neg_of_add_eq_zero_left h0
        calc (1 - a) • u + a • w - x
            = t3⁻¹ • (t3 • ((1 - a) • u + a • w - x)) :=
              (inv_smul_smul₀ ht3ne _).symm
          _ = t3⁻¹ • (-(t2 • (v - x))) := by rw [hkey]
          _ = (t3⁻¹ * (-t2)) • (v - x) := by module
      -- 与 :3707 的非共线矛盾（HOL 用 AFFINE_HULL_2 显式见证，此处直接
      -- 用 collinear3_iff_smul 的组合刻画）
      exact hnc ((collinear3_iff_smul (Ne.symm hxv)).mpr ⟨_, hz⟩)
    · -- HOL :3777-3893（t3' = 0，t2' ≠ 0）
      -- 基本正性与系数关系
      have ht2'pos : 0 < t2' := lt_of_le_of_ne ht2'0 (fun h => ht2z h.symm)
      have ht2'ne : t2' ≠ 0 := ne_of_gt ht2'pos
      have ht1 : t1 = 1 - t2 - t3 := by linarith
      have ht1' : t1' = 1 - t2' := by linarith
      -- 两个仿射组合分解合并（HOL :3780-3795 的系数方程）
      have hA : t1' • x + t2' • v' + (0 : ℝ) • w'
          = t1 • x + t2 • v + t3 • ((1 - a) • u + a • w) := hyeq'.symm.trans hyeq
      have h2 : t2' • v' = (t2' - t2 - t3) • x + t2 • v + t3 • ((1 - a) • u + a • w) := by
        have hz : t2' • v' - ((t2' - t2 - t3) • x + t2 • v + t3 • ((1 - a) • u + a • w)) = 0 := by
          have e1 : (t2' - t2 - t3) • x = t1 • x - t1' • x := by rw [ht1, ht1']; module
          rw [e1]
          rw [show t2' • v' - ((t1 • x - t1' • x) + t2 • v + t3 • ((1 - a) • u + a • w))
              = (t1' • x + t2' • v' + (0 : ℝ) • w')
                - (t1 • x + t2 • v + t3 • ((1 - a) • u + a • w)) from by module]
          exact sub_eq_zero_of_eq hA
        exact sub_eq_zero.mp hz
      have hvx : t2' • (v' - x) = t2 • (v - x) + t3 • ((1 - a) • u + a • w - x) := by
        rw [smul_sub, h2]
        module
      -- 第 2 部分（:3856-3866）：v' ∈ aff_gt {x} {v,z}，显式见证系数
      have hv' : v' = (1 - t2'⁻¹ * t2 - t2'⁻¹ * t3) • x + (t2'⁻¹ * t2) • v
          + (t2'⁻¹ * t3) • ((1 - a) • u + a • w) := by
        rw [← inv_smul_smul₀ ht2'ne v', h2, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        have hc : t2'⁻¹ * (t2' - t2 - t3) = 1 - t2'⁻¹ * t2 - t2'⁻¹ * t3 := by
          rw [mul_sub, mul_sub, inv_mul_cancel₀ ht2'ne]
        rw [hc]
      have hv'aff : v' ∈ affGt {x} {v, (1 - a) • u + a • w} := by
        rw [aff_gt_1_2 hdis]
        exact ⟨1 - t2'⁻¹ * t2 - t2'⁻¹ * t3, t2'⁻¹ * t2, t2'⁻¹ * t3,
          mul_pos (inv_pos.mpr ht2'pos) ht20, mul_pos (inv_pos.mpr ht2'pos) ht30, by ring, hv'⟩
      -- 第 1 部分（:3777-3844）：~coplanar {x,v',v,u}
      have hDne : (t2 + t3 : ℝ) ≠ 0 := by linarith
      have hPFS : ¬ Coplanar ({x, v, u, w} : Set V3) :=
        properties_fully_surrounded hfan hvu huw hθ0 hθπ
      have hncop1 : ¬ Coplanar ({x, v, u, (1 - a) • u + a • w} : Set V3) :=
        continuous_coplanar_fan x v u w hPFS a (by linarith)
      have hncop2 : ¬ Coplanar ({x, u, v, (1 - a) • u + a • w} : Set V3) := by
        intro hc
        apply hncop1
        have hset : ({x, u, v, (1 - a) • u + a • w} : Set V3)
            = ({x, v, u, (1 - a) • u + a • w} : Set V3) := by ext p; simp; tauto
        rw [← hset]
        exact hc
      have htne : t3 * (t2 + t3)⁻¹ ≠ 0 :=
        mul_ne_zero (ne_of_gt ht30) (inv_ne_zero hDne)
      have hncop3 : ¬ Coplanar ({x, u, v,
          (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)} : Set V3) :=
        continuous_coplanar_fan x u v ((1 - a) • u + a • w) hncop2 (t3 * (t2 + t3)⁻¹) htne
      have hncvxu : ¬ Coplanar ({x, v', v, u} : Set V3) := by
        intro hcop4
        obtain ⟨o1, o2, o3, hsub⟩ := hcop4
        have hxo : x ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have hv'o : v' ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have hvo : v ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have huo : u ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        -- 关键组合点：q = (1-c)•v + c•z = x + (t2'/(t2+t3)) • (v' - x)（HOL :3796-3812）
        have hqm : (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)
            = x + (t2 + t3)⁻¹ • (t2' • (v' - x)) := by
          rw [hvx]
          rw [show t2 • (v - x) + t3 • ((1 - a) • u + a • w - x)
              = t2 • v + t3 • ((1 - a) • u + a • w) - (t2 + t3) • x from by module]
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hDne, one_smul]
          rw [show x + ((t2 + t3)⁻¹ • (t2 • v + t3 • ((1 - a) • u + a • w)) - x)
              = (t2 + t3)⁻¹ • (t2 • v + t3 • ((1 - a) • u + a • w)) from by abel]
          rw [smul_add, smul_smul, smul_smul]
          have hc2 : 1 - t3 * (t2 + t3)⁻¹ = (t2 + t3)⁻¹ * t2 := by
            field_simp
            linarith
          rw [hc2]
          module
        -- q 落在过 x, v' 的直线上，故落在同一平面内
        have hqo : (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)
            ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := by
          have hL := AffineMap.lineMap_mem ((t2 + t3)⁻¹ * t2') hxo hv'o
          rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hL
          rw [hqm, smul_smul, add_comm]
          exact hL
        refine hncop3 ⟨o1, o2, o3, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hxo
        · exact huo
        · exact hvo
        · exact hqo
      -- 第 3 部分（:3867-3893）：借助半空间元素与切边引理收尾
      obtain ⟨hv'V, -⟩ := fan_mem_of_edge hfan he'
      obtain ⟨u', hu'E, hu'0, hu'π⟩ :=
        exists_element_in_half_sapace_fan x v' v u V E hfan hv'V hncvxu (hcard v' hv'V) hfan80
      have hncvu' : ¬ Collinear3 x v' u' := fan_not_collinear hfan hu'E
      obtain ⟨t, ht0, htlt1, hpm⟩ :=
        exists_cut_small_edges_fan (v1 := v') (u1 := u') hfan hvu huw hsigma ha0 ha1 hfan80
          hncvu' hv'aff hu'0 hu'π
      obtain ⟨p, hp⟩ := hpm
      rw [Set.mem_inter_iff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have h1t : 0 < 1 - t := by linarith
      have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
      have h'1 : (1 - t) * a < a := by
        have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
        rwa [one_mul] at hm
      -- 向量恒等式（HOL "YEU" 处的 VECTOR_ARITH）
      have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
          = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
      have hp1' : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} := by
        rw [hid]
        exact hp1
      have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} :=
        ⟨{v', u'}, hu'E, aff_gt_subset_aff_ge (disjoint_singleton_of_not_collinear3 hncvu') hp2⟩
      have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
          ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
      rw [hEM ((1 - t) * a) h'0 h'1] at hfin
      simp at hfin
  · -- HOL :3894-4043（t3' ≠ 0）：再分 t2' = 0 / t2' ≠ 0
    by_cases ht2z : t2' = 0
    · -- HOL :3894-4043（t3' ≠ 0，t2' = 0）：BLOCK18B 的镜像（v' ↔ w'，t2' ↔ t3'）
      subst ht2z
      -- 基本正性与系数关系
      have ht3'pos : 0 < t3' := lt_of_le_of_ne ht3'0 (fun h => ht3z h.symm)
      have ht3'ne : t3' ≠ 0 := ne_of_gt ht3'pos
      have ht1 : t1 = 1 - t2 - t3 := by linarith
      have ht1' : t1' = 1 - t3' := by linarith
      -- 两个仿射组合分解合并（HOL :3894-3913 的系数方程）
      have hA : t1' • x + (0 : ℝ) • v' + t3' • w'
          = t1 • x + t2 • v + t3 • ((1 - a) • u + a • w) := hyeq'.symm.trans hyeq
      have h2 : t3' • w' = (t3' - t2 - t3) • x + t2 • v + t3 • ((1 - a) • u + a • w) := by
        have hz : t3' • w'
            - ((t3' - t2 - t3) • x + t2 • v + t3 • ((1 - a) • u + a • w)) = 0 := by
          have e1 : (t3' - t2 - t3) • x = t1 • x - t1' • x := by rw [ht1, ht1']; module
          rw [e1]
          rw [show t3' • w' - ((t1 • x - t1' • x) + t2 • v + t3 • ((1 - a) • u + a • w))
              = (t1' • x + (0 : ℝ) • v' + t3' • w')
                - (t1 • x + t2 • v + t3 • ((1 - a) • u + a • w)) from by module]
          exact sub_eq_zero_of_eq hA
        exact sub_eq_zero.mp hz
      have hwx : t3' • (w' - x) = t2 • (v - x) + t3 • ((1 - a) • u + a • w - x) := by
        rw [smul_sub, h2]
        module
      -- 第 2 部分（HOL :3994-4004）：w' ∈ aff_gt {x} {v,z}，显式见证系数
      have hw' : w' = (1 - t3'⁻¹ * t2 - t3'⁻¹ * t3) • x + (t3'⁻¹ * t2) • v
          + (t3'⁻¹ * t3) • ((1 - a) • u + a • w) := by
        rw [← inv_smul_smul₀ ht3'ne w', h2, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        have hc : t3'⁻¹ * (t3' - t2 - t3) = 1 - t3'⁻¹ * t2 - t3'⁻¹ * t3 := by
          rw [mul_sub, mul_sub, inv_mul_cancel₀ ht3'ne]
        rw [hc]
      have hw'aff : w' ∈ affGt {x} {v, (1 - a) • u + a • w} := by
        rw [aff_gt_1_2 hdis]
        exact ⟨1 - t3'⁻¹ * t2 - t3'⁻¹ * t3, t3'⁻¹ * t2, t3'⁻¹ * t3,
          mul_pos (inv_pos.mpr ht3'pos) ht20, mul_pos (inv_pos.mpr ht3'pos) ht30, by ring, hw'⟩
      -- 第 1 部分（HOL :3914-3993）：~coplanar {x,w',v,u}
      have hDne : (t2 + t3 : ℝ) ≠ 0 := by linarith
      have hPFS : ¬ Coplanar ({x, v, u, w} : Set V3) :=
        properties_fully_surrounded hfan hvu huw hθ0 hθπ
      have hncop1 : ¬ Coplanar ({x, v, u, (1 - a) • u + a • w} : Set V3) :=
        continuous_coplanar_fan x v u w hPFS a (by linarith)
      have hncop2 : ¬ Coplanar ({x, u, v, (1 - a) • u + a • w} : Set V3) := by
        intro hc
        apply hncop1
        have hset : ({x, u, v, (1 - a) • u + a • w} : Set V3)
            = ({x, v, u, (1 - a) • u + a • w} : Set V3) := by ext p; simp; tauto
        rw [← hset]
        exact hc
      have htne : t3 * (t2 + t3)⁻¹ ≠ 0 :=
        mul_ne_zero (ne_of_gt ht30) (inv_ne_zero hDne)
      have hncop3 : ¬ Coplanar ({x, u, v,
          (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)} : Set V3) :=
        continuous_coplanar_fan x u v ((1 - a) • u + a • w) hncop2 (t3 * (t2 + t3)⁻¹) htne
      have hncwxu : ¬ Coplanar ({x, w', v, u} : Set V3) := by
        intro hcop4
        obtain ⟨o1, o2, o3, hsub⟩ := hcop4
        have hxo : x ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have hw'o : w' ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have hvo : v ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        have huo : u ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := hsub (by simp)
        -- 关键组合点：q = (1-c)•v + c•z = x + (t2+t3)⁻¹ • (t3' • (w' - x))（HOL :3946 附近）
        have hqm : (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)
            = x + (t2 + t3)⁻¹ • (t3' • (w' - x)) := by
          rw [hwx]
          rw [show t2 • (v - x) + t3 • ((1 - a) • u + a • w - x)
              = t2 • v + t3 • ((1 - a) • u + a • w) - (t2 + t3) • x from by module]
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hDne, one_smul]
          rw [show x + ((t2 + t3)⁻¹ • (t2 • v + t3 • ((1 - a) • u + a • w)) - x)
              = (t2 + t3)⁻¹ • (t2 • v + t3 • ((1 - a) • u + a • w)) from by abel]
          rw [smul_add, smul_smul, smul_smul]
          have hc2 : 1 - t3 * (t2 + t3)⁻¹ = (t2 + t3)⁻¹ * t2 := by
            field_simp
            linarith
          rw [hc2]
          module
        -- q 落在过 x, w' 的直线上，故落在同一平面内
        have hqo : (1 - t3 * (t2 + t3)⁻¹) • v + (t3 * (t2 + t3)⁻¹) • ((1 - a) • u + a • w)
            ∈ (affineSpan ℝ ({o1, o2, o3} : Set V3) : Set V3) := by
          have hL := AffineMap.lineMap_mem ((t2 + t3)⁻¹ * t3') hxo hw'o
          rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hL
          rw [hqm, smul_smul, add_comm]
          exact hL
        refine hncop3 ⟨o1, o2, o3, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hxo
        · exact huo
        · exact hvo
        · exact hqo
      -- 第 3 部分（HOL :4005-4043）：借助半空间元素与切边引理收尾
      obtain ⟨-, hw'V⟩ := fan_mem_of_edge hfan he'
      obtain ⟨u', hu'E, hu'0, hu'π⟩ :=
        exists_element_in_half_sapace_fan x w' v u V E hfan hw'V hncwxu (hcard w' hw'V) hfan80
      have hncwu' : ¬ Collinear3 x w' u' := fan_not_collinear hfan hu'E
      obtain ⟨t, ht0, htlt1, hpm⟩ :=
        exists_cut_small_edges_fan (v1 := w') (u1 := u') hfan hvu huw hsigma ha0 ha1 hfan80
          hncwu' hw'aff hu'0 hu'π
      obtain ⟨p, hp⟩ := hpm
      rw [Set.mem_inter_iff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have h1t : 0 < 1 - t := by linarith
      have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
      have h'1 : (1 - t) * a < a := by
        have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
        rwa [one_mul] at hm
      -- 向量恒等式（HOL "YEU" 处的 VECTOR_ARITH）
      have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
          = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
      have hp1' : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} := by
        rw [hid]
        exact hp1
      have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} :=
        ⟨{w', u'}, hu'E, aff_gt_subset_aff_ge (disjoint_singleton_of_not_collinear3 hncwu') hp2⟩
      have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
          ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
      rw [hEM ((1 - t) * a) h'0 h'1] at hfin
      simp at hfin
    · -- HOL :4044-4224（t2' ≠ 0 且 t3' ≠ 0，结合 0 ≤ 得均正）
      -- 基本正性
      have ht2'pos : 0 < t2' := lt_of_le_of_ne ht2'0 (Ne.symm ht2z)
      have ht3'pos : 0 < t3' := lt_of_le_of_ne ht3'0 (Ne.symm ht3z)
      have ht2'ne : t2' ≠ 0 := ne_of_gt ht2'pos
      have ht3'ne : t3' ≠ 0 := ne_of_gt ht3'pos
      have ht3ne : t3 ≠ 0 := ne_of_gt ht30
      -- 第 1 部分（HOL :4053-4062）：y ∈ aff_gt {x} {v',w'}，见证 t1',t2',t3'
      have hygt' : y ∈ affGt {x} {v', w'} := by
        rw [aff_gt_1_2 hdis']
        exact ⟨t1', t2', t3', ht2'pos, ht3'pos, hsum', hyeq'⟩
      -- 第 2 部分（HOL :4063-4071）：y ∈ aff_ge {x} {v',w'}，同见证
      have hyge' : y ∈ affGe {x} {v', w'} := by
        rw [aff_ge_1_2 hdis']
        exact ⟨t1', t2', t3', ht2'0, ht3'0, hsum', hyeq'⟩
      -- 第 3 部分（HOL :4072-4093）：y ∈ aff_gt/aff_ge {x} {v,z}，见证 t1,t2,t3
      have hygt : y ∈ affGt {x} {v, (1 - a) • u + a • w} := by
        rw [aff_gt_1_2 hdis]
        exact ⟨t1, t2, t3, ht20, ht30, hsum, hyeq⟩
      have hyge : y ∈ affGe {x} {v, (1 - a) • u + a • w} := by
        rw [aff_ge_1_2 hdis]
        exact ⟨t1, t2, t3, le_of_lt ht20, le_of_lt ht30, hsum, hyeq⟩
      -- 第 4 部分（HOL :4099-4224）：非共线链，均经两点表示 + 系数分解矛盾
      have hxv' : x ≠ v' := not_collinear3_left hnc'
      have hxw' : x ≠ w' := not_collinear3_right hnc'
      have hxz : x ≠ (1 - a) • u + a • w := not_collinear3_right hnc
      -- 4a（HOL :4099-4125）：¬ Collinear3 x y w'
      have hncw' : ¬ Collinear3 x y w' := by
        intro hcol
        have hmem := mem_affineSpan_pair_of_collinear3 hxw' hcol ht2'ne hsum' hyeq'
        refine hnc' ?_
        show Collinear ℝ ({x, v', w'} : Set V3)
        have hcol2 : Collinear3 x w' v' := (collinear3_iff_mem_affineSpan hxw').mpr hmem
        have hset : ({x, v', w'} : Set V3) = ({x, w', v'} : Set V3) := by
          ext p; simp; tauto
        rw [hset]
        exact hcol2
      -- 4b（HOL :4126-4151）：¬ Collinear3 x y v'
      have hncv' : ¬ Collinear3 x y v' := by
        intro hcol
        have hyeq'' : y = t1' • x + t3' • w' + t2' • v' := by rw [hyeq']; module
        have hmem := mem_affineSpan_pair_of_collinear3 hxv' hcol ht3'ne
          (by linarith : t1' + t3' + t2' = 1) hyeq''
        exact hnc' ((collinear3_iff_mem_affineSpan hxv').mpr hmem)
      -- 4c（HOL :4152-4188）：¬ Collinear3 x y z
      have hncz : ¬ Collinear3 x y ((1 - a) • u + a • w) := by
        intro hcol
        have hmem := mem_affineSpan_pair_of_collinear3 hxz hcol (ne_of_gt ht20) hsum hyeq
        refine hnc ?_
        show Collinear ℝ ({x, v, (1 - a) • u + a • w} : Set V3)
        have hcol2 : Collinear3 x ((1 - a) • u + a • w) v :=
          (collinear3_iff_mem_affineSpan hxz).mpr hmem
        have hset : ({x, v, (1 - a) • u + a • w} : Set V3)
            = ({x, (1 - a) • u + a • w, v} : Set V3) := by
          ext p; simp; tauto
        rw [hset]
        exact hcol2
      -- 4d（HOL :4189-4224）：¬ Collinear3 x y v
      have hncv : ¬ Collinear3 x y v := by
        intro hcol
        have hyeq'v : y = t1 • x + t3 • ((1 - a) • u + a • w) + t2 • v := by
          rw [hyeq]; module
        have hmem := mem_affineSpan_pair_of_collinear3 hxv hcol ht3ne
          (by linarith : t1 + t3 + t2 = 1) hyeq'v
        exact hnc ((collinear3_iff_mem_affineSpan hxv).mpr hmem)
      -- HOL :4225：按 azim x y v w' 是否落在 (0,π) 分情况
      by_cases haz : 0 < azim x y v w' ∧ azim x y v w' < Real.pi
      · -- HOL :4229-4247（Case A：azim x y v w' ∈ (0,π)）
        obtain ⟨t, ht0, htlt1, hpm⟩ :=
          exists_cut_small_edges_fan (v1 := y) (u1 := w') hfan hvu huw hsigma ha0 ha1 hfan80
            hncw' hygt haz.1 haz.2
        obtain ⟨p, hp⟩ := hpm
        rw [Set.mem_inter_iff] at hp
        obtain ⟨hp1, hp2⟩ := hp
        have h1t : 0 < 1 - t := by linarith
        have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
        have h'1 : (1 - t) * a < a := by
          have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
          rwa [one_mul] at hm
        -- 向量恒等式（HOL "YEU" 处的 VECTOR_ARITH）
        have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
            = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
        have hp1' : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} := by
          rw [hid]
          exact hp1
        -- HOL :4238 aff_gt1_subset_aff_ge：aff_gt {x} {y,w'} ⊆ aff_ge {x} {v',w'}
        have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} :=
          ⟨{v', w'}, he', aff_gt1_subset_aff_ge hdis' hncw' hyge' hp2⟩
        have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
            ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
        rw [hEM ((1 - t) * a) h'0 h'1] at hfin
        simp at hfin
      · -- HOL :4248-4252：azim 非负（azim spec）+ 上界（< 2π）拆成
        -- π < azim ∨ (azim = 0 ∨ azim = π)
        have h0le : 0 ≤ azim x y v w' := azim_nonneg x y v w'
        have hlt2π : azim x y v w' < 2 * Real.pi := azim_lt_two_pi x y v w'
        have hB : Real.pi < azim x y v w' ∨
            (azim x y v w' = 0 ∨ azim x y v w' = Real.pi) := by
          rcases eq_or_lt_of_le h0le with hz | hpos
          · exact Or.inr (Or.inl hz.symm)
          · rcases eq_or_lt_of_le
              (not_lt.mp (fun hcc => haz ⟨hpos, hcc⟩)) with heq | hgt
            · exact Or.inr (Or.inr heq.symm)
            · exact Or.inl hgt
        rcases hB with hgt | hzπ
        · -- HOL :4254-4291（π < azim x y v w'）
          -- HOL :4255 aff_gt2_subset_aff_ge：azim x y v' w' = π
          have hπ2 : azim x y v' w' = Real.pi :=
            aff_gt2_subset_aff_ge hdis' hncw' hncv' hygt'
          have hle : azim x y v' w' ≤ azim x y v w' := by
            rw [hπ2]
            exact le_of_lt hgt
          -- HOL :4262 sum5_azim_fan：azim x y v w' = azim x y v v' + azim x y v' w'
          have hsum5 := sum5_azim_fan (not_collinear3_left hncv).symm hncv hncv' hncw' hle
          have hvv'0 : 0 < azim x y v v' := by linarith
          have hvv'π : azim x y v v' < Real.pi := by linarith
          obtain ⟨t, ht0, htlt1, hpm⟩ :=
            exists_cut_small_edges_fan (v1 := y) (u1 := v') hfan hvu huw hsigma ha0 ha1 hfan80
              hncv' hygt hvv'0 hvv'π
          obtain ⟨p, hp⟩ := hpm
          rw [Set.mem_inter_iff] at hp
          obtain ⟨hp1, hp2⟩ := hp
          have h1t : 0 < 1 - t := by linarith
          have h'0 : 0 < (1 - t) * a := mul_pos h1t ha0
          have h'1 : (1 - t) * a < a := by
            have hm := mul_lt_mul_of_pos_right (show (1 - t : ℝ) < 1 by linarith) ha0
            rwa [one_mul] at hm
          -- 向量恒等式（HOL "YEU" 处的 VECTOR_ARITH）
          have hid : (1 - (1 - t) * a) • u + ((1 - t) * a) • w
              = (1 - t) • ((1 - a) • u + a • w) + t • u := by module
          have hp1' : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w} := by
            rw [hid]
            exact hp1
          -- HOL :4276-4278：集合对换 aff_ge {x} {w',v'} = aff_ge {x} {v',w'}
          have hsetw : ({w', v'} : Set V3) = ({v', w'} : Set V3) := by
            ext q; simp; tauto
          have hdisw : Disjoint ({x} : Set V3) {w', v'} := by
            rw [hsetw]
            exact hdis'
          have hygew : y ∈ affGe {x} {w', v'} := by
            rw [hsetw]
            exact hyge'
          -- HOL :4282 aff_gt1_subset_aff_ge（作用于换序对 w',v'）
          have hp2' : p ∈ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := by
            refine ⟨{v', w'}, he', ?_⟩
            rw [← hsetw]
            exact aff_gt1_subset_aff_ge hdisw hncv' hygew hp2
          have hfin : p ∈ affGt {x} {v, (1 - (1 - t) * a) • u + ((1 - t) * a) • w}
              ∩ {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} := ⟨hp1', hp2'⟩
          rw [hEM ((1 - t) * a) h'0 h'1] at hfin
          simp at hfin
        · -- HOL :4289-4810 / :4812-5182（azim x y v w' = 0 或 = π）。
          -- HOL 将三重析取展开为三支：π < azim（已证）、= 0（:4289-4810）、
          -- = π（:4812-5182，[BLOCK18D4]）
          rcases hzπ with h0 | hπ
          · -- HOL :4289-4810（azim x y v w' = 0）：抽出为私有引理
            exact not_cut_inside_fan_azim0 hfan hvu huw hsigma ha0 ha1 hcard hfan80
              hEM hθ0 hθπ he' hnc' hdis' hdis hygt' hyge' hygt hncw' hncv' hncz hncv h0
          · -- HOL :4812-5182（azim x y v w' = π：v 与 w' 角色对换的镜像）
            exact not_cut_inside_fan_azim_pi hfan hvu huw hsigma ha0 ha1 hcard hfan80
              hEM hθ0 hθπ he' hnc' hdis' hdis hygt' hyge' hygt hncw' hncv' hncz hncv hπ

/-! ## `cut_in_edges_fan` / `not_cut_in_edges_fan`（planarity.hl:7038–7301）

`not_cut_in_edges_fan`：若扰动点 `(1-a)•u + a•w`（`0 < a < 1`）不在被边锥
之并 `xfan` 中（用 infimum 论证：`s1` 的下确界 `b` 处交集为空，
`not_cut_inside_fan` 给出闭性输入，`fan_run1_in_small_not0_is_fan` 把空性
延拓到 `(0,h')`，与 `b` 的最大下界性冲突）。`cut_in_edges_fan` 是其
`a ≠ 1` 情形的一行归约。零 sorry。 -/
theorem not_cut_in_edges_fan {a : ℝ} (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E = ∅ := by
  by_contra hnot
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  let s1 : Set ℝ := {h | 0 < h ∧ h < 1 ∧
    ¬(affGt {x} {v, (1 - h) • u + h • w} ∩ xfan x V E = ∅)}
  have ha_s1 : a ∈ s1 := by
    simp [s1, ha0, ha1, hnot]
  have hs1_ne : s1.Nonempty := ⟨a, ha_s1⟩
  have hBddBelow_s1 : BddBelow s1 := by
    refine ⟨0, ?_⟩
    intro h hh
    have hh' : 0 < h ∧ h < 1 ∧ ¬(affGt {x} {v, (1 - h) • u + h • w} ∩ xfan x V E = ∅) := by
      simpa [s1] using hh
    exact le_of_lt hh'.1
  let b : ℝ := sInf s1
  have hb_le_a : b ≤ a := by
    dsimp [b]
    exact csInf_le hBddBelow_s1 ha_s1
  have hb1 : b < 1 := lt_of_le_of_lt hb_le_a ha1
  have he1 : ∀ s : ℝ, 0 < s → s < b →
      affGt {x} {v, (1 - s) • u + s • w} ∩
        {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} = ∅ := by
    intro s hs0 hsb
    by_contra hneq
    have hs1 : s ∈ s1 := by
      simp [s1, hs0]
      exact ⟨lt_trans hsb hb1, hneq⟩
    have hb_le_s : b ≤ s := by
      dsimp [b]
      exact csInf_le hBddBelow_s1 hs1
    linarith
  obtain ⟨h0, h1_0, h1_le, h1_prop⟩ :=
    fan_run_in_small_is_not_meet_xfan hfan hvu huw hθ0 hθπ hsigma
  have hb0 : 0 < b := by
    have hh0_le_b : h0 ≤ b := by
      dsimp [b]
      refine le_csInf hs1_ne ?_
      intro t ht
      have ht' : 0 < t ∧ t < 1 ∧ ¬(affGt {x} {v, (1 - t) • u + t • w} ∩ xfan x V E = ∅) := by
        simpa [s1] using ht
      have ht0 : 0 < t := ht'.1
      have htneq : ¬(affGt {x} {v, (1 - t) • u + t • w} ∩ xfan x V E = ∅) := ht'.2.2
      by_contra hnot0
      have hlt : t < h0 := lt_of_not_ge hnot0
      exact htneq (h1_prop t ht0 hlt)
    exact lt_of_lt_of_le h1_0 hh0_le_b
  have hncb : affGt {x} {v, (1 - b) • u + b • w} ∩
      {y | ∃ e, e ∈ E ∧ y ∈ affGe {x} e} = ∅ :=
    not_cut_inside_fan hfan hvu huw hsigma hb0 hb1 hcard hfan80 he1
  obtain ⟨h', hb_lt_h', _h'_le, h'_prop⟩ :=
    fan_run1_in_small_not0_is_fan hfan hvu huw Set.Subset.rfl hθ0 hθπ hsigma hb0 hb1
      hncb he1
  have h'_le_b : h' ≤ b := by
    dsimp [b]
    refine le_csInf hs1_ne ?_
    intro t ht
    by_contra hnot0
    have hlt : t < h' := lt_of_not_ge hnot0
    have ht' : 0 < t ∧ t < 1 ∧ ¬(affGt {x} {v, (1 - t) • u + t • w} ∩ xfan x V E = ∅) := by
      simpa [s1] using ht
    have ht0 : 0 < t := ht'.1
    have htneq : ¬(affGt {x} {v, (1 - t) • u + t • w} ∩ xfan x V E = ∅) := ht'.2.2
    have hempt : affGt {x} {v, (1 - t) • u + t • w} ∩ xfan x V E = ∅ := by
      change (affGt {x} {v, (1 - t) • u + t • w} ∩
        {z | ∃ e ∈ E, z ∈ affGe {x} e} = ∅)
      exact h'_prop t ht0 hlt
    exact htneq hempt
  linarith

/-- HOL planarity.hl:7038 `cut_in_edges_fan`：由 `not_cut_in_edges_fan`
一行归约（`a ≠ 1` 与 `a ≤ 1`、`0 < a` 合得 `a < 1`）。 -/
theorem cut_in_edges_fan {a : ℝ} (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (huw : {u, w} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hEM : ¬ (affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E = ∅)) :
    a = 1 := by
  by_contra h1
  have haLt : a < 1 := lt_of_le_of_ne ha1 h1
  have hem : affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E = ∅ :=
    not_cut_in_edges_fan hfan hvu huw hsigma ha0 haLt hcard hfan80
  exact hEM hem
