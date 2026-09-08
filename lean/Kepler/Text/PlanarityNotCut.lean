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
- Remaining `azim = 0` / `azim = pi` sub-cases (handled together in HOL
  via AZIM_EQ_0/AZIM_EQ_0_ALT) left as a marked sorry:
  `[BLOCK18D3] planarity.hl:4292-5182`.
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

/-- HOL planarity.hl:3667 `not_cut_inside_fan`（`t3' = t2' = 0`
（:3730-3776）、`[BLOCK18B]`（`t3' = 0`，`t2' ≠ 0`，:3777-3893）、
`[BLOCK18C]` 的 `t2' = 0` 子分支（`t3' ≠ 0`，:3894-4043，18b 的镜像）
以及 `[BLOCK18D]` 首段（一般情形 `t2' ≠ 0` 且 `t3' ≠ 0` 的 aff 组合与
非共线链，:4044-4224）均完整证明；`[BLOCK18D2]`（azim 分情况之
`0 < azim < π` 与 `π < azim` 两支，:4225-4291）亦完整证明；剩余
`azim = 0 / π` 分情况（HOL 中合并处理）留待 `[BLOCK18D3]`（:4292-5182）。 -/
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
        · -- HOL :4292-4645（azim = 0 或 azim = π：AZIM_EQ_0 / AZIM_EQ_0_ALT
          -- 合并为单支，再按 w' ∈ aff_gt 分情况）
          sorry -- [BLOCK18D3] planarity.hl:4292-4645 (azim = 0 or pi; w' IN aff_gt case split)
