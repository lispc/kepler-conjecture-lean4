/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18a.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18a of block 18, planarity.hl:3667-5182):
- `not_cut_inside_fan` (3667): statement setup plus the first small
  branch `t3' = 0 /\ t2' = 0` (HOL :3730-3776) fully proved.
- Remaining branches are left as marked sorries:
  `[BLOCK18B] planarity.hl:3777-3893` (`t3' = 0`, `t2' <> 0`),
  `[BLOCK18C] planarity.hl:3894-5182` (`t3' <> 0`).
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

/-! ## 主定理（切片 18a） -/

/-- HOL planarity.hl:3667 `not_cut_inside_fan`（切片 18a：陈述与第一个
小分支 `t3' = t2' = 0`（:3730-3776）完整证明；`t2' ≠ 0` 与 `t3' ≠ 0`
分支分别留待 `[BLOCK18B]`/`[BLOCK18C]`）。 -/
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
    · sorry -- [BLOCK18B] planarity.hl:3777-3893
  · sorry -- [BLOCK18C] planarity.hl:3894-5182
