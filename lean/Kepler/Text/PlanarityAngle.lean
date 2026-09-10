/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18f.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18f of block 18, planarity.hl:9297-10095): the eight
angle/cone theorems
- `condition_to_in_aff_gt_by_angle` (9297)
- `condition1_to_in_aff_gt_by_angle` (9396)
- `angle_is_small_fan` (9479)
- `angle_is_smallpi_fan` (9639)
- `exists_rw_dart_inter_aff_gt_fan` (9680, ~300 HOL lines, hardest)
- `scale_in_edges_fan` (9981)
- `aff_gt_imp_not_collinear` (10020)
- `conditions_in_rcone_fan` (10051)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings)
designed by glm-5.3, proofs filled by the auto_loop/big-pickle harness,
each commit gated on build+axioms+signature-freeze, batch-audited by the
main agent. All 8 theorems fully proved, zero sorry.

Encoding notes (gaps / closest existing encodings):
- HOL `e1_fan`/`e2_fan`/`e3_fan` ↔ `e1Fan`/`e2Fan`/`e3Fan`
  (Kepler/Text/TopologyFan.lean:2261-2268).
- HOL `rcone_fan x v h` ↔ `rconeFan x v h` (Kepler/Text/TopologyFan.lean:2253;
  an identical `Kepler.Text.Fan.rconeFan` also exists, Kepler/Text/Fan.lean:186).
- HOL `rw_dart_fan x V E (y,v,w,w1) h` ↔ `rwDartFan x V E (y,v,w,w1) h`
  (Kepler/Text/TopologyFan.lean:3145; identical `Kepler.Text.Fan.rwDartFan`
  at Kepler/Text/Fan.lean:192).
- HOL `norm ((v - x) cross (u - x))`: there is no public V3-level cross in
  the repo (`cross3` in TopologyFan is private), so the statement uses the
  established `WithLp.toLp 2 (crossProduct …)` idiom (as in
  Kepler/Text/Planarity.lean:3792) under the V3 Euclidean norm `‖·‖`.
- HOL `aff_gt_2_1` is not ported under that name; its ray characterization
  is `affGt_pair_iff` (Kepler/Geom/Aff.lean:82).
- HOL `remark1_fan` (fan.hl:423) and `inequality4_aim_in_convex_fan`
  (planarity.hl:7933) are not yet ported; the fragments needed are noted
  per-theorem below.
-/
import Kepler.Text.PlanarityNotCut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 角度条件给出的 aff_gt 成员（planarity.hl:9297-9478） -/

/-- V3 点积的左标量引理（TopologyFan 私有引理 `smul_dot` 的复制）。 -/
private theorem smul_dot_aux (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- V3 点积交换（TopologyFan 私有引理 `dot_comm` 的复制）。 -/
private theorem dot_comm_aux (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- Pi 侧点积回到 V3 点积（TopologyFan 私有引理 `dot_coe` 的复制）。 -/
private theorem dot_coe_aux (a b : V3) :
    (a : Fin 3 → ℝ) ⬝ᵥ (b : Fin 3 → ℝ) = a ⬝ᵥ b := by
  rw [← dot_toLp, WithLp.toLp_ofLp]

/-- V3 取分量的减法桥（TopologyFan 私有引理 `coe_sub` 的复制）。 -/
private theorem coe_sub_aux (a b : V3) :
    ((a - b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) - (b : Fin 3 → ℝ) := rfl

/-- V3 点积的右标量引理。 -/
private theorem dot_smul_right_aux (t : ℝ) (a b : V3) :
    a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) := by
  rw [show (a : V3) ⬝ᵥ (t • b) = ((a : Fin 3 → ℝ) ⬝ᵥ (t • (b : Fin 3 → ℝ))) from rfl,
    dotProduct_smul, smul_eq_mul]

/-- V3 取分量的标量乘桥。 -/
private theorem coe_smul_aux (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

/-- HOL planarity.hl:9297-9395 `condition_to_in_aff_gt_by_angle`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 s1:real.
~collinear {x,v,u} /\  &0< (v - x) dot (u - x) /\ &0< s1
/\ s1< atn ((norm ((v - x) cross (u - x))) * inv((v - x) dot (u - x)))
==>
sin s1 % e1_fan x v u + cos s1 % e3_fan x v u + x IN aff_gt {x} {v, u}
```

证明思路：`atn_bounds` 给出 `s1 < pi/2`；`aff_gt_1_2` 把目标化为找
`t1+t2+t3=1`、`t2,t3>0` 的组合。取
`t3 = sin s1 * |v-x| * |(v-x) cross (u-x)|⁻¹`，
`t2 = |v-x|⁻¹*(cos s1 - sin s1*|(v-x) cross (u-x)|⁻¹*((v-x) dot (u-x))`，
`t1 = 1 - t3 - t2`；向量恒等式经 CROSS_LAGRANGE 展开 `e1_fan`/`e3_fan`
后 `module` 可验证；`t2 > 0` 由 `tan s1 < |cross| * (dot)⁻¹`（TAN_MONO_LT
+ ATN_TAN）两端乘正数得到，`t3 > 0` 由 `0 < sin s1`（SIN_POS_PI2）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499，即
  HOL `properties_coordinate` 的角色）
- `e3Fan_cross_ux_ne_zero`（Kepler/Text/TopologyFan.lean:2355）
- `e1Fan_dot_self`/`e2Fan_dot_self`/`e3Fan_dot_self`/`e1Fan_dot_e3`
  （Kepler/Text/TopologyFan.lean:2415/2397/2347/2431）
- `fan_not_collinear`（Kepler/Text/Fan.lean:342） -/
theorem condition_to_in_aff_gt_by_angle {x v u : V3} {s1 : ℝ}
    (hnc : ¬ Collinear3 x v u) (hdot : 0 < (v - x) ⬝ᵥ (u - x)) (hs1 : 0 < s1)
    (hs : s1 < Real.arctan
      (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (u - x))⁻¹)) :
    Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x ∈
      affGt {x} {v, u} := by
  -- 基本非退化事实
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hnvpos : 0 < ‖v - x‖ := lt_of_le_of_ne (norm_nonneg _) fun h => hnv h.symm
  set nv : ℝ := ‖v - x‖ with hnvdef
  set d : ℝ := (v - x) ⬝ᵥ (u - x) with hddef
  rw [← coe_sub_aux] at hddef
  set C : ℝ := ‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ with hCdef
  have hnv' : nv ≠ 0 := by rw [hnvdef]; exact hnv
  have hdne : d ≠ 0 := ne_of_gt hdot
  replace hs : s1 < Real.arctan (C * d⁻¹) := hs
  -- 角度范围：0 < s1 < π/2
  have hs1pi : s1 < Real.pi / 2 :=
    lt_trans hs (Real.arctan_mem_Ioo (C * d⁻¹)).2
  have hsin : 0 < Real.sin s1 :=
    Real.sin_pos_of_pos_of_lt_pi hs1 (by linarith)
  have hcos : 0 < Real.cos s1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hs1pi⟩
  -- C > 0（否则 arctan (C * d⁻¹) ≤ 0 < s1）
  have hnC : 0 < C := by
    by_contra hcon
    have hcon' : C ≤ 0 := le_of_not_gt hcon
    have hle : C * d⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon' (inv_nonneg.mpr (le_of_lt hdot))
    have hle2 : Real.arctan (C * d⁻¹) ≤ Real.arctan 0 :=
      Real.arctan_mono hle
    rw [Real.arctan_zero] at hle2
    linarith
  -- e-标架与 (u - x) 的坐标分解
  have hframe : Orthonormal3 (e1Fan x v u) (e2Fan x v u) (e3Fan x v u) :=
    orthonormal_e1Fan_e2Fan_e3Fan hnc
  have haxf : (v - x : V3) = nv • e3Fan x v u := by
    rw [e3Fan, smul_smul, ← hnvdef, mul_inv_cancel₀ hnv, one_smul]
  have h0 := on3_expand hframe (u - x)
  rw [dot_e2Fan hnc, zero_smul, add_zero] at h0
  set T1 : ℝ := (u - x) ⬝ᵥ e1Fan x v u with hT1def
  set T3 : ℝ := (u - x) ⬝ᵥ e3Fan x v u with hT3def
  have hnT1 : 0 < T1 := udot_e1Fan hnc
  have hT1ne : T1 ≠ 0 := ne_of_gt hnT1
  have hdecomp : (u - x : V3) = T1 • e1Fan x v u + T3 • e3Fan x v u := h0
  have hT3val : T3 = nv⁻¹ * d := by
    rw [hT3def, e3Fan, coe_smul_aux ‖v - x‖⁻¹ (v - x),
      dot_smul_right_aux ‖v - x‖⁻¹ (u - x) (v - x), dot_comm_aux (u - x) (v - x),
      ← hnvdef, ← hddef]
  have hT3d : nv * T3 = d := by
    rw [hT3val, ← mul_assoc, mul_inv_cancel₀ hnv', one_mul]
  have hT3pos : 0 < T3 := by rw [hT3val]; exact mul_pos (inv_pos.mpr hnvpos) hdot
  -- 勾股：T1² + T3² = ‖u - x‖²
  have he1n : ‖e1Fan x v u‖ = 1 := by
    have h : ‖e1Fan x v u‖ ^ 2 = 1 := by
      rw [norm_sq_eq_dot]; exact e1Fan_dot_self hnc
    nlinarith [h, norm_nonneg (e1Fan x v u),
      sq_nonneg (‖e1Fan x v u‖ - 1)]
  have he3n : ‖e3Fan x v u‖ = 1 := by
    have h : ‖e3Fan x v u‖ ^ 2 = 1 := by
      rw [norm_sq_eq_dot]; exact e3Fan_dot_self hvx u
    nlinarith [h, norm_nonneg (e3Fan x v u),
      sq_nonneg (‖e3Fan x v u‖ - 1)]
  have hpyth : T1 * T1 + T3 * T3 = ‖u - x‖ ^ 2 := by
    conv_rhs => rw [hdecomp, norm_add_sq_real, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnT1, abs_of_pos hT3pos,
      he1n, he3n, real_inner_smul_left, real_inner_smul_right, inner_eq_dot,
      e1Fan_dot_e3 hnc]
    ring
  -- Lagrange：C² = nv² * ‖u - x‖² − d²
  have hC2 : C ^ 2 = nv ^ 2 * ‖u - x‖ ^ 2 - d ^ 2 := by
    rw [hCdef, ← real_inner_self_eq_norm_sq, inner_toLp, cross_dot_cross,
      dot_coe_aux, ← norm_sq_eq_dot, ← norm_sq_eq_dot, ← hnvdef,
      dot_comm_aux (u - x) (v - x), ← hddef]
    ring
  -- nv * T1 = C
  have hnT : nv * T1 = C := by
    have h4 : d ^ 2 = (nv * T3) ^ 2 := by rw [← hT3d]
    have h3 : (nv * T1) ^ 2 + (nv * T3) ^ 2 = nv ^ 2 * (T1 * T1 + T3 * T3) := by
      ring
    have h1 : (nv * T1) ^ 2 + d ^ 2 = C ^ 2 + d ^ 2 := by
      rw [h4, h3, hpyth, ← h4]
      linarith [hC2]
    have hsq : (nv * T1) ^ 2 = C ^ 2 := by linarith [h1]
    have hmul0 : (nv * T1 - C) * (nv * T1 + C) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hmul0 with h | h
    · linarith
    · exfalso
      have hp : 0 ≤ nv * T1 := mul_nonneg (le_of_lt hnvpos) (le_of_lt hnT1)
      linarith
  -- tan 单调性给出关键标量不等式
  have htan : Real.tan s1 < C * d⁻¹ := by
    have hs1mem : s1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, hs1pi⟩
    have hAmem : Real.arctan (C * d⁻¹) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      Real.arctan_mem_Ioo _
    have hlt := Real.strictMonoOn_tan hs1mem hAmem hs
    rwa [Real.tan_arctan] at hlt
  have hkey : Real.sin s1 * C⁻¹ * d < Real.cos s1 := by
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at htan
    have hstep : Real.sin s1 * d < Real.cos s1 * C := by
      have h1 : Real.sin s1 * d < (C * d⁻¹ * Real.cos s1) * d :=
        mul_lt_mul_of_pos_right htan hdot
      have h2 : (C * d⁻¹ * Real.cos s1) * d = Real.cos s1 * C := by
        field_simp [hdne]
      linarith
    have h3 : Real.sin s1 * d / C < Real.cos s1 := (div_lt_iff₀ hnC).mpr hstep
    rw [div_eq_inv_mul] at h3
    have h4 : Real.sin s1 * C⁻¹ * d = C⁻¹ * (Real.sin s1 * d) := by ring
    rw [h4]; exact h3
  have hrel : Real.sin s1 * T1⁻¹ * T3 = Real.sin s1 * C⁻¹ * d := by
    rw [← hnT, ← hT3d]
    field_simp [hnv', hT1ne]
  have ht2inner : 0 < Real.cos s1 - Real.sin s1 * T1⁻¹ * T3 := by
    rw [hrel]; linarith
  have ht3T1 : Real.sin s1 * T1⁻¹ * T1 = Real.sin s1 := by
    rw [mul_assoc, inv_mul_cancel₀ hT1ne, mul_one]
  -- 见证系数
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro hxmem
    rcases Set.mem_insert_iff.mp hxmem with he | he
    · exact hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
    · exact hnc (collinear3_pair_left (Set.mem_singleton_iff.mp he).symm)
  obtain ⟨t2, t3, ht2def', ht3def'⟩ :
      ∃ t2 t3 : ℝ, t2 = nv⁻¹ * (Real.cos s1 - Real.sin s1 * T1⁻¹ * T3) ∧
        t3 = Real.sin s1 * T1⁻¹ := ⟨_, _, rfl, rfl⟩
  have hc1 : t3 * T1 = Real.sin s1 := by rw [ht3def']; exact ht3T1
  have hc2 : t2 * nv + t3 * T3 = Real.cos s1 := by
    rw [ht2def', ht3def']
    have hA : (nv⁻¹ * (Real.cos s1 - Real.sin s1 * T1⁻¹ * T3)) * nv
        = Real.cos s1 - Real.sin s1 * T1⁻¹ * T3 := by
      field_simp [hnv']
    rw [hA]; ring
  rw [aff_gt_1_2 hdis]
  refine ⟨1 - t2 - t3, t2, t3, ?_, ?_, by ring, ?_⟩
  · rw [ht2def']; exact mul_pos (inv_pos.mpr hnvpos) ht2inner
  · rw [ht3def']; exact mul_pos hsin (inv_pos.mpr hnT1)
  · have e1 : (1 - t2 - t3) • x + t2 • v + t3 • u
        = x + t2 • ((v - x : V3)) + t3 • ((u - x : V3)) := by module
    have e2 : x + t2 • ((v - x : V3)) + t3 • ((u - x : V3))
        = x + (t3 * T1) • e1Fan x v u + (t2 * nv + t3 * T3) • e3Fan x v u := by
      rw [haxf, hdecomp]; module
    rw [e1, e2, hc1, hc2]
    module

/-- HOL planarity.hl:9396-9478 `condition1_to_in_aff_gt_by_angle`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 s1:real.
~collinear {x,v,u} /\ &0< s1 /\ s1< pi/ &2
/\ (v - x) dot (u - x:real^3) <= &0
==>
sin s1 % e1_fan x v u + cos s1 % e3_fan x v u + x IN aff_gt {x} {v, u}`
```

证明思路：与 `condition_to_in_aff_gt_by_angle` 完全相同的见证系数
`t1, t2, t3`；区别只在 `t2 > 0`：此处 `cos s1 > 0`（COS_POS_PI2）而
`(v-x) dot (u-x) <= 0`，故减去的项 `sin s1 * |cross|⁻¹ * dot <= 0`，
`t2 >= |v-x|⁻¹ * cos s1 > 0`（REAL_LE_MUL 连锁）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499）
- `e3Fan_cross_ux_ne_zero`（Kepler/Text/TopologyFan.lean:2355） -/
theorem condition1_to_in_aff_gt_by_angle {x v u : V3} {s1 : ℝ}
    (hnc : ¬ Collinear3 x v u) (hs1 : 0 < s1) (hs : s1 < Real.pi / 2)
    (hle : (v - x) ⬝ᵥ (u - x) ≤ 0) :
    Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x ∈
      affGt {x} {v, u} := by
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hnvpos : 0 < ‖v - x‖ := lt_of_le_of_ne (norm_nonneg _) fun h => hnv h.symm
  set nv : ℝ := ‖v - x‖ with hnvdef
  set d : ℝ := (v - x) ⬝ᵥ (u - x) with hddef
  rw [← coe_sub_aux] at hddef
  set C : ℝ := ‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ with hCdef
  have hnv' : nv ≠ 0 := by rw [hnvdef]; exact hnv
  have hs1pi : s1 < Real.pi / 2 := hs
  have hsin : 0 < Real.sin s1 :=
    Real.sin_pos_of_pos_of_lt_pi hs1 (by linarith)
  have hcos : 0 < Real.cos s1 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hs1pi⟩
  have hframe : Orthonormal3 (e1Fan x v u) (e2Fan x v u) (e3Fan x v u) :=
    orthonormal_e1Fan_e2Fan_e3Fan hnc
  have haxf : (v - x : V3) = nv • e3Fan x v u := by
    rw [e3Fan, smul_smul, ← hnvdef, mul_inv_cancel₀ hnv, one_smul]
  have h0 := on3_expand hframe (u - x)
  rw [dot_e2Fan hnc, zero_smul, add_zero] at h0
  set T1 : ℝ := (u - x) ⬝ᵥ e1Fan x v u with hT1def
  set T3 : ℝ := (u - x) ⬝ᵥ e3Fan x v u with hT3def
  have hnT1 : 0 < T1 := udot_e1Fan hnc
  have hT1ne : T1 ≠ 0 := ne_of_gt hnT1
  have hdecomp : (u - x : V3) = T1 • e1Fan x v u + T3 • e3Fan x v u := h0
  have hT3val : T3 = nv⁻¹ * d := by
    rw [hT3def, e3Fan, coe_smul_aux ‖v - x‖⁻¹ (v - x),
      dot_smul_right_aux ‖v - x‖⁻¹ (u - x) (v - x), dot_comm_aux (u - x) (v - x),
      ← hnvdef, ← hddef]
  have hT3d : nv * T3 = d := by
    rw [hT3val, ← mul_assoc, mul_inv_cancel₀ hnv', one_mul]
  have hT3neg : T3 ≤ 0 := by
    rw [hT3val]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hnvpos)) hle
  have he1n : ‖e1Fan x v u‖ = 1 := by
    have h : ‖e1Fan x v u‖ ^ 2 = 1 := by
      rw [norm_sq_eq_dot]; exact e1Fan_dot_self hnc
    nlinarith [h, norm_nonneg (e1Fan x v u),
      sq_nonneg (‖e1Fan x v u‖ - 1)]
  have he3n : ‖e3Fan x v u‖ = 1 := by
    have h : ‖e3Fan x v u‖ ^ 2 = 1 := by
      rw [norm_sq_eq_dot]; exact e3Fan_dot_self hvx u
    nlinarith [h, norm_nonneg (e3Fan x v u),
      sq_nonneg (‖e3Fan x v u‖ - 1)]
  have hpyth : T1 * T1 + T3 * T3 = ‖u - x‖ ^ 2 := by
    conv_rhs => rw [hdecomp, norm_add_sq_real, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hnT1, abs_of_nonpos hT3neg,
      he1n, he3n, real_inner_smul_left, real_inner_smul_right, inner_eq_dot,
      e1Fan_dot_e3 hnc]
    ring
  have hC2 : C ^ 2 = nv ^ 2 * ‖u - x‖ ^ 2 - d ^ 2 := by
    rw [hCdef, ← real_inner_self_eq_norm_sq, inner_toLp, cross_dot_cross,
      dot_coe_aux, ← norm_sq_eq_dot, ← norm_sq_eq_dot, ← hnvdef,
      dot_comm_aux (u - x) (v - x), ← hddef]
    ring
  have hnT : nv * T1 = C := by
    have h4 : d ^ 2 = (nv * T3) ^ 2 := by rw [← hT3d]
    have h3 : (nv * T1) ^ 2 + (nv * T3) ^ 2 = nv ^ 2 * (T1 * T1 + T3 * T3) := by
      ring
    have h1 : (nv * T1) ^ 2 + d ^ 2 = C ^ 2 + d ^ 2 := by
      rw [h4, h3, hpyth, ← h4]
      linarith [hC2]
    have hsq : (nv * T1) ^ 2 = C ^ 2 := by linarith [h1]
    have hmul0 : (nv * T1 - C) * (nv * T1 + C) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hmul0 with h | h
    · linarith
    · exfalso
      have hp : 0 < nv * T1 := mul_pos hnvpos hnT1
      have hCnn : 0 ≤ C := by rw [hCdef]; exact norm_nonneg _
      linarith
  have ht2inner : 0 < Real.cos s1 - Real.sin s1 * T1⁻¹ * T3 := by
    have hpos : 0 ≤ Real.sin s1 * T1⁻¹ := le_of_lt (mul_pos hsin (inv_pos.mpr hnT1))
    have hmul : Real.sin s1 * T1⁻¹ * T3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos hT3neg
    linarith
  have ht3T1 : Real.sin s1 * T1⁻¹ * T1 = Real.sin s1 := by
    rw [mul_assoc, inv_mul_cancel₀ hT1ne, mul_one]
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro hxmem
    rcases Set.mem_insert_iff.mp hxmem with he | he
    · exact hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
    · exact hnc (collinear3_pair_left (Set.mem_singleton_iff.mp he).symm)
  obtain ⟨t2, t3, ht2def', ht3def'⟩ :
      ∃ t2 t3 : ℝ, t2 = nv⁻¹ * (Real.cos s1 - Real.sin s1 * T1⁻¹ * T3) ∧
        t3 = Real.sin s1 * T1⁻¹ := ⟨_, _, rfl, rfl⟩
  have hc1 : t3 * T1 = Real.sin s1 := by rw [ht3def']; exact ht3T1
  have hc2 : t2 * nv + t3 * T3 = Real.cos s1 := by
    rw [ht2def', ht3def']
    have hA : (nv⁻¹ * (Real.cos s1 - Real.sin s1 * T1⁻¹ * T3)) * nv
        = Real.cos s1 - Real.sin s1 * T1⁻¹ * T3 := by
      field_simp [hnv']
    rw [hA]; ring
  rw [aff_gt_1_2 hdis]
  refine ⟨1 - t2 - t3, t2, t3, ?_, ?_, by ring, ?_⟩
  · rw [ht2def']; exact mul_pos (inv_pos.mpr hnvpos) ht2inner
  · rw [ht3def']; exact mul_pos hsin (inv_pos.mpr hnT1)
  · have e1 : (1 - t2 - t3) • x + t2 • v + t3 • u
        = x + t2 • ((v - x : V3)) + t3 • ((u - x : V3)) := by module
    have e2 : x + t2 • ((v - x : V3)) + t3 • ((u - x : V3))
        = x + (t3 * T1) • e1Fan x v u + (t2 * nv + t3 * T3) • e3Fan x v u := by
      rw [haxf, hdecomp]; module
    rw [e1, e2, hc1, hc2]
    module

/-! ## 方位角与 sigma 后继（planarity.hl:9479-9679） -/

/-- HOL planarity.hl:9479-9638 `angle_is_small_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
 azim x v u w <= azim x v u (sigma_fan x V E v u)
```

证明思路：若 `set_of_edge v V E = {u}` 则 CARD=1 与 `hcard` 矛盾。否则
令 `w1 = sigma_fan x V E v u`；`fan80`（u,w 与 v,u 两次）+ `hsigma` 给
`0 < azim x u w v < pi`，`properties_fully_surrounded` 得四点不共面，
`notcoplanar_imp_notcollinear_fan`/`properties_of_fully_surrounded1_fan`
给 `0 < azim x v u w < pi`。若 `azim x v u w <= azim x v u w1` 即结论；
若 `azim x v u w1 < azim x v u w`，`sum4_azim_fan` 分解 + 
`exists_cut_in_edge_fan` 取弦点 `va`，`decomposition_planar_by_angle_fan`
二分：一支与 `not_cut_in_edges_fan`（边内部不相交）矛盾，另一支把
`w`（或 `u`）逼进 `aff {x,u}`（或 `aff {x,w}`）与非共线矛盾。
注意：HOL 用的 `remark1_fan`（fan.hl:423）未移植，需用
`fan_not_collinear` + sigmaFan 性质现场替代。

候选已有引理：
- `fan_not_collinear`（Kepler/Text/Fan.lean:342）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `properties_of_fully_surrounded1_fan`（Kepler/Text/PlanarityNotCut.lean:2330）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `exists_cut_in_edge_fan`（Kepler/Text/PlanarityNotCut.lean:1974）
- `decomposition_planar_by_angle_fan`（Kepler/Text/Planarity.lean:4203）
- `not_cut_in_edges_fan`（Kepler/Text/PlanarityNotCut.lean:1224）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）、
  `pos_in_aff_ge_fan`（Kepler/Text/Planarity.lean:4366）、
  `aff_gt1_subset_aff_ge`（Kepler/Text/Planarity.lean:3888） -/

private theorem collinear3_swap_anc {x p q : V3} (h : Collinear3 x p q) :
    Collinear3 x q p := by
  show Collinear ℝ ({x, q, p} : Set V3)
  have h' : Collinear ℝ ({x, p, q} : Set V3) := h
  rw [show ({x, p, q} : Set V3) = ({x, q, p} : Set V3) from by ext z; simp; tauto] at h'
  exact h'

private theorem collinear3_first_third_anc (x p : V3) : Collinear3 x p x := by
  show Collinear ℝ ({x, p, x} : Set V3)
  have h2 : ({x, p, x} : Set V3) = {x, p} := by ext z; simp; tauto
  rw [h2]
  exact collinear_pair ℝ x p

private theorem not_collinear3_left_anc {x p q : V3} (h : ¬ Collinear3 x p q) :
    x ≠ p := by
  intro he
  subst he
  exact h (collinear3_of_eq rfl)

private theorem not_collinear3_right_anc {x p q : V3} (h : ¬ Collinear3 x p q) :
    x ≠ q := by
  intro he
  subst he
  exact h (collinear3_first_third_anc x p)

private theorem disjoint_singleton_of_not_collinear3_anc {x p q : V3}
    (h : ¬ Collinear3 x p q) : Disjoint ({x} : Set V3) {p, q} := by
  rw [Set.disjoint_singleton_left]
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with he | he
  · subst he
    exact h (collinear3_of_eq rfl)
  · subst he
    exact h (collinear3_first_third_anc x p)

private theorem affGe_empty_anc (x : V3) : affGe {x} (∅ : Set V3) = {x} := by
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

theorem angle_is_small_fan {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    azim x v u w ≤ azim x v u (sigmaFan x V E v u) := by
  have hvV : v ∈ V := (fan_mem_of_edge hfan hvu).1
  have huV : u ∈ V := (fan_mem_of_edge hfan hvu).2
  have hnc_vu : ¬ Collinear3 x v u := fan_not_collinear hfan hvu
  have hxnv : x ≠ v := not_collinear3_left_anc hnc_vu
  have hxv : v ≠ x := hxnv.symm
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hu_edge : u ∈ setOfEdge v V E := by
    simp [setOfEdge, huV, hvu]
  by_cases hne : setOfEdge v V E = {u}
  · exfalso
    have hgt : 1 < (setOfEdge v V E).ncard := hcard v hvV
    rw [hne, Set.ncard_singleton] at hgt
    norm_num at hgt
  · have hσ := SIGMA_FAN hne hfan hu_edge
    let w1 : V3 := sigmaFan x V E v u
    have hσmem : w1 ∈ setOfEdge v V E := by dsimp [w1]; exact hσ.1
    have hσne : w1 ≠ u := by dsimp [w1]; exact hσ.2.1
    have hσmin : ∀ w1 ∈ setOfEdge v V E, w1 ≠ u →
        azim x v u (sigmaFan x V E v u) ≤ azim x v u w1 := hσ.2.2
    have hσpair : ({v, w1} ∈ E) ∧ w1 ∈ V := by
      simpa [setOfEdge] using hσmem
    have hv_w1 : {v, w1} ∈ E := hσpair.1
    have hnc_vw1 : ¬ Collinear3 x v w1 := fan_not_collinear hfan hv_w1
    obtain ⟨h0w1, hpiw1⟩ := hfan80 v u hvu
    have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
      properties_fully_surrounded hfan hvu huw hθ0 hθπ
    have hnc_pairs := notcoplanar_imp_notcollinear_fan hcop
    have hnc_uw : ¬ Collinear3 x u w := hnc_pairs.1
    have hnc_vw : ¬ Collinear3 x v w := hnc_pairs.2.2
    have hfs1 := properties_of_fully_surrounded1_fan hcop hθ0 hθπ
    have h0w : 0 < azim x v u w := hfs1.1
    have hpiw : azim x v u w < Real.pi := hfs1.2
    by_cases hle : azim x v u w ≤ azim x v u w1
    · exact hle
    · exfalso
      have hlt : azim x v u w1 < azim x v u w := not_le.mp hle
      have hle' : azim x v u w1 ≤ azim x v u w := le_of_lt hlt
      have hsum := sum4_azim_fan hxv hnc_vu hnc_vw1 hnc_vw hle'
      have h0w1w : 0 < azim x v w1 w := by
        have hz : azim x v w1 w ≠ 0 := by
          intro heq
          have hrel : azim x v u w = azim x v u w1 := by rw [hsum, heq, add_zero]
          linarith
        exact lt_of_le_of_ne (azim_nonneg x v w1 w) (Ne.symm hz)
      have hltw1w : azim x v w1 w < Real.pi := by
        have hlepart : azim x v w1 w ≤ azim x v u w := by
          have hz : 0 ≤ azim x v u w1 := azim_nonneg x v u w1
          rw [hsum]
          linarith
        exact lt_of_le_of_lt hlepart hpiw
      obtain ⟨a, ha0, ha1, hva_w1⟩ :=
        exists_cut_in_edge_fan hnc_vw1 hnc_uw hnc_vu hnc_vw hθ0 hθπ h0w1 hpiw1 h0w1w hltw1w
      have hnc_va : ¬ Collinear3 x v ((1 - a) • u + a • w) :=
        not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ a ha0 ha1
      rcases decomposition_planar_by_angle_fan hnc_vw1 hnc_va hva_w1 with hA | hB
      · -- 支 A：w1 ∈ aff_gt {x} {v,va}，与 not_cut_in_edges_fan 矛盾
        have hpt := point_in_aff_ge hnc_vw1
        have hw1_ge : w1 ∈ affGe {x} {v, w1} := hpt.2.2
        have hw1_xfan : w1 ∈ xfan x V E := ⟨{v, w1}, hv_w1, hw1_ge⟩
        have hempty := not_cut_in_edges_fan hfan hvu huw hsigma ha0 ha1 hcard hfan80
        have hcontra : w1 ∈ affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E :=
          ⟨hA, hw1_xfan⟩
        have hnotmem : w1 ∉ affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E := by
          rw [hempty]
          simp
        exact hnotmem hcontra
      · -- 支 B：va ∈ aff_ge {x} {v,w1}，fan7 交到 {u,w}∩{v,w1}，再分类
        let S : Set V3 := ({u, w} : Set V3) ∩ {v, w1}
        have hdis_uw : Disjoint ({x} : Set V3) {u, w} :=
          disjoint_singleton_of_not_collinear3_anc hnc_uw
        have hva_uw : (1 - a) • u + a • w ∈ affGe {x} {u, w} :=
          pos_in_aff_ge_fan hdis_uw ha0 ha1
        have hinter_va : (1 - a) • u + a • w ∈
            affGe {x} {u, w} ∩ affGe {x} {v, w1} := ⟨hva_uw, hB⟩
        have hf7 : fan7 x V E := hfan.2.2.2.2.2
        have hin1 : ({u, w} : Set V3) ∈ E ∪ {s | ∃ v ∈ V, s = {v}} := Or.inl huw
        have hin2 : ({v, w1} : Set V3) ∈ E ∪ {s | ∃ v ∈ V, s = {v}} := Or.inl hv_w1
        have hfan7eq : affGe {x} {u, w} ∩ affGe {x} {v, w1} =
            affGe {x} (S : Set V3) := by
          dsimp [S]
          exact hf7 {u, w} hin1 {v, w1} hin2
        have hvaS : (1 - a) • u + a • w ∈ affGe {x} (S : Set V3) :=
          hfan7eq ▸ hinter_va
        have hu_vw1 : u ∉ ({v, w1} : Set V3) := by
          intro hu
          rcases Set.mem_insert_iff.mp hu with h | h
          · exact edge_ne_of_fan hfan hvu h.symm
          · exact hσne h.symm
        have huS : u ∉ S := by
          intro hus
          exact hu_vw1 ((Set.mem_inter_iff _ _ _).mp hus).2
        by_cases hwS : w ∈ S
        · -- S = {w} ⟹ va ∈ aff_ge {x} {w} ⟹ u ∈ aff {x,w} 矛盾
          have hSw : S = ({w} : Set V3) := by
            apply Set.eq_singleton_iff_unique_mem.mpr
            refine ⟨hwS, ?_⟩
            intro q hq
            rcases Set.mem_insert_iff.mp ((Set.mem_inter_iff _ _ _).mp hq).1 with
              hq2 | hq2
            · exact absurd (hq2 ▸ hq) huS
            · exact hq2
          have hvaW : (1 - a) • u + a • w ∈ affGe {x} ({w} : Set V3) := by
            rw [← hSw]
            exact hvaS
          have hxw : x ≠ w := not_collinear3_right_anc hnc_uw
          obtain ⟨d1, d2, hd2, hdsum, hzeq⟩ :=
            (mem_affGe_singleton hxw).mp hvaW
          have hxune : 1 - a ≠ 0 := by linarith
          have hukey : (1 - a) • u = d1 • x + (d2 - a) • w := by
            calc (1 - a) • u = ((1 - a) • u + a • w) - a • w := by module
              _ = (d1 • x + d2 • w) - a • w := by rw [hzeq]
              _ = d1 • x + (d2 - a) • w := by module
          have huum : u = ((1 - a)⁻¹ * d1) • x + ((1 - a)⁻¹ * (d2 - a)) • w := by
            calc u = (1 - a)⁻¹ • ((1 - a) • u) := (inv_smul_smul₀ hxune _).symm
              _ = (1 - a)⁻¹ • (d1 • x + (d2 - a) • w) := by rw [hukey]
              _ = ((1 - a)⁻¹ * d1) • x + ((1 - a)⁻¹ * (d2 - a)) • w := by
                rw [smul_add, smul_smul, smul_smul]
          have huumem : u ∈ (affineSpan ℝ ({x, w} : Set V3) : Set V3) := by
            rw [affine_hull_2_fan]
            exact ⟨_, _, by field_simp; linarith, huum⟩
          exact hnc_uw (collinear3_swap_anc ((collinear3_iff_mem_affineSpan hxw).mpr huumem))
        · -- S = ∅ ⟹ va = x 与 ¬Collinear3 x v va 矛盾
          have hSe : S = (∅ : Set V3) := by
            by_contra hneS
            obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hneS
            rcases Set.mem_insert_iff.mp ((Set.mem_inter_iff _ _ _).mp hq).1 with
              hq2 | hq2
            · exact huS (hq2 ▸ hq)
            · exact hwS (hq2 ▸ hq)
          have hvaE : (1 - a) • u + a • w ∈ affGe {x} (∅ : Set V3) := by
            rw [← hSe]
            exact hvaS
          rw [affGe_empty_anc] at hvaE
          have hzx : (1 - a) • u + a • w = x := Set.mem_singleton_iff.mp hvaE
          exact hnc_va (by rw [hzx]; exact collinear3_first_third_anc x v)

/-- HOL planarity.hl:9639-9679 `angle_is_smallpi_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
&0< azim x v u w /\ azim x v u w <pi
```

证明思路：`0 <`：`azim_nonneg`，若 `= 0` 则 AZIM_EQ_0_PI_EQ_COPLANAR
给出共面，与 `properties_fully_surrounded`（由 fan80 + hsigma 得
`0 < azim x u w v < pi`）矛盾（Lean 侧可用 `azim_eq_zero_iff` +
`affGt_pair_iff` 走 PlanarityNotCut.lean:2330 的同款论证）。
`< pi`：`angle_is_small_fan` 给 `azim x v u w <= azim x v u w1`，
而 fan80(v,u) 给 `azim x v u w1 < pi`（`w1 = sigma_fan x V E v u`）。

候选已有引理：
- `azim_nonneg`（Kepler/Geom/Azim.lean:947）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `angle_is_small_fan`（本文件上文） -/
theorem angle_is_smallpi_fan {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    0 < azim x v u w ∧ azim x v u w < Real.pi := by
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  exact properties_of_fully_surrounded1_fan hcop hθ0 hθπ

/-! ## `exists_rw_dart_inter_aff_gt_fan` 的私有辅助（V3 点积加法、叉积桥接） -/

/-- V3 点积的加法左分配（TopologyFan 私有引理 `add_dot` 的复制）。 -/
private theorem dot_add_left_anc (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c :=
  add_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

/-- V3 点积的加法右分配。 -/
private theorem dot_add_right_anc (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c :=
  dotProduct_add (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

/-- Pi 侧点积的加法左分配（rw 用的 Pi 变量版）。 -/
private theorem dot_add_left_pi {a b c : Fin 3 → ℝ} :
    (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := add_dotProduct a b c

/-- Pi 侧点积的左标量分配（rw 用的 Pi 变量版）。 -/
private theorem smul_dot_pi (t : ℝ) (a b : Fin 3 → ℝ) :
    (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := by
  rw [smul_dotProduct, smul_eq_mul]

/-- 叉积为零推出共线（HOL CROSS_EQ_0 + COLLINEAR_3 的 V3 桥接）。 -/
private theorem collinear3_of_cross_eq_zero {x v u : V3}
    (h : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) = 0) :
    Collinear3 x v u := by
  by_cases hvx : v = x
  · rw [hvx]
    exact collinear3_of_eq rfl
  · have hp : ((v - x : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro h0
      apply hvx
      exact sub_eq_zero.mp ((WithLp.ofLp_eq_zero 2).mp h0)
    have h0 : crossProduct ((v - x : V3) : Fin 3 → ℝ)
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) = 0 := by
      rw [h]
      exact map_zero _
    have h1 := cross_cross_eq_smul_sub_smul' ((v - x : V3) : Fin 3 → ℝ)
      ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)
    rw [h0] at h1
    have h2 : (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) •
        ((v - x : V3) : Fin 3 → ℝ) =
        (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) •
          ((u - x : V3) : Fin 3 → ℝ) :=
      sub_eq_zero.mp h1.symm
    have hpp : ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro h1'
      apply hp
      funext i
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (((v - x : V3) : Fin 3 → ℝ) j))).mp h1'
      exact mul_self_eq_zero.mp (h3 i (Finset.mem_univ i))
    have hqe : ((u - x : V3) : Fin 3 → ℝ)
        = ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
          (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))) •
          ((v - x : V3) : Fin 3 → ℝ) := by
      calc ((u - x : V3) : Fin 3 → ℝ)
          = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))⁻¹ •
              ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) •
                ((u - x : V3) : Fin 3 → ℝ)) := by
            rw [smul_smul, inv_mul_cancel₀ hpp, one_smul]
        _ = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))⁻¹ •
              ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) •
                ((v - x : V3) : Fin 3 → ℝ)) := by rw [h2]
        _ = ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
              (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))) •
              ((v - x : V3) : Fin 3 → ℝ) := by
            rw [smul_smul, div_eq_inv_mul, mul_comm]
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
        c = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
          (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) := ⟨_, rfl⟩
    have hqec : ((u - x : V3) : Fin 3 → ℝ) = c • ((v - x : V3) : Fin 3 → ℝ) := by
      rw [hcdef]
      exact hqe
    have hqV : (u - x : V3) = c • (v - x : V3) := by
      have hc := congrArg (WithLp.toLp 2) hqec
      rwa [WithLp.toLp_ofLp, WithLp.toLp_smul, WithLp.toLp_ofLp] at hc
    rw [collinear3_iff_mem_affineSpan (Ne.symm hvx), affine_hull_2_fan]
    refine ⟨1 - c, c, by ring, ?_⟩
    calc u = (u - x) + x := by module
      _ = c • (v - x) + x := by rw [hqV]
      _ = (1 - c) • x + c • v := by module

/-- 非共线 ⇒ 叉积范数为正（HOL NORM_CROSS 的替代，
用 CROSS_EQ_0 + COLLINEAR_3 桥接）。 -/
private theorem cross_pos_of_not_collinear3_anc {x v u : V3}
    (hnc : ¬ Collinear3 x v u) :
    0 < ‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ := by
  have hzne : (WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3) ≠ 0 := by
    intro h0
    apply hnc
    have hcoe := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) h0
    simp only [WithLp.ofLp_zero] at hcoe
    exact collinear3_of_cross_eq_zero hcoe
  exact norm_pos_iff.mpr hzne

/-! ## rw_dart 与 aff_gt 相交（planarity.hl:9680-9980，最难一块） -/

/-- HOL planarity.hl:9680-9980 `exists_rw_dart_inter_aff_gt_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 .
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
(?h:real. &0< h /\
(!t:real. &0< t /\ t< h==>
(!s:real. &0<s /\ s< pi/ &2
==>
~(rw_dart_fan x V E ((x:real^3),(v:real^3),(u:real^3),(sigma_fan x V E v (u:real^3))) (cos(s)) INTER aff_gt {x} {v, (&1-t)%u+t%w}={})
)))
```

证明思路：取 `h = 1`。前半与 `angle_is_small_fan` 同一巨型分情况
（set_of_edge v = {u} 矛盾；`w1 = sigma_fan x V E v u`；azim 大小二分；
`exists_cut_in_edge_fan` + `decomposition_planar_by_angle_fan` +
`not_cut_in_edges_fan` 排除 `azim x v u w1 < azim x v u w`），得到
`aff_gt {x} {v, va} ⊆ wedge x v u w1`（HOL 由 aff_gt_inter_aff_gt +
properties_of_collinear4_points_fan + AZIM_EQ_ALT 得出）。于是
`rw_dart ∩ aff_gt {x} {v, va}` 化为 `rcone_fan x v (cos s) ∩ aff_gt {x} {v, va}`。
对每个 `t` 记 `va = (1-t)•u + t•w`，按 `(v-x) dot (va-x)` 符号二分取
`s1 = s/2`（dot<=0 支，用 `condition1_to_in_aff_gt_by_angle`）或
`s1 = min s (atn(|cross|/(dot))/2`（dot>0 支，用
`condition_to_in_aff_gt_by_angle`），见证点
`y = x + sin s1 • e1_fan x v va + cos s1 • e3_fan x v va`：
`y ∈ aff_gt` 即上述二引理；`y ∈ rcone` 由正交标架
（`orthonormal_e1Fan_e2Fan_e3Fan`）算出
`(y-x) dot (v-x) = |v-x| * cos s1 > |v-x| * cos s = |y-x| * |v-x| * cos s`
（SIN_CIRCLE 给 `|y-x| = 1`，COS_MONO_LT 给严格不等）。
注意：HOL 的 `inequality4_aim_in_convex_fan`（planarity.hl:7933）与
`remark1_fan` 未移植，需现场替代（弦点非共线用
`not_collinear_is_properties_fully_surrounded`
Kepler/Text/Planarity.lean:2559）。

候选已有引理：
- `angle_is_small_fan`（本文件上文）
- `condition_to_in_aff_gt_by_angle` / `condition1_to_in_aff_gt_by_angle`（本文件上文）
- `rwDartFan` / `rconeFan` 定义（Kepler/Text/TopologyFan.lean:3145/2253）
- `wedge`（Kepler/Geom/Azim.lean:63）、`azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `not_collinear_is_properties_fully_surrounded`（Kepler/Text/Planarity.lean:2559）
- `not_cut_in_edges_fan`（Kepler/Text/PlanarityNotCut.lean:1224）
- `exists_cut_in_edge_fan`（Kepler/Text/PlanarityNotCut.lean:1974）
- `orthonormal_e1Fan_e2Fan_e3Fan`（Kepler/Text/TopologyFan.lean:3499） -/


theorem exists_rw_dart_inter_aff_gt_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    ∃ h : ℝ, 0 < h ∧
      ∀ t : ℝ, 0 < t → t < h →
        ∀ s : ℝ, 0 < s → s < Real.pi / 2 →
          (rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos s) ∩
            affGt {x} {v, (1 - t) • u + t • w}) ≠ ∅ := by
  -- HOL 大分情况已由 `angle_is_small_fan` 给出（azim x v u w ≤ azim x v u w1）
  have hvV : v ∈ V := (fan_mem_of_edge hfan hvu).1
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  obtain ⟨hnc_uw, hnc_vu, hnc_vw⟩ := notcoplanar_imp_notcollinear_fan hcop
  have hle : azim x v u w ≤ azim x v u (sigmaFan x V E v u) :=
    angle_is_small_fan hfan hvu huw hsigma hfan80 hcard
  have hcardv : 1 < (setOfEdge v V E).ncard := hcard v hvV
  refine ⟨1, by norm_num, ?_⟩
  intro t ht0 ht1 s hs0 hsπ
  obtain ⟨va, hvadef⟩ : ∃ va : V3, va = (1 - t) • u + t • w := ⟨_, rfl⟩
  rw [← hvadef]
  -- 弦点 va 的方位角事实（HOL inequality4_aim_in_convex_fan，已移植）
  obtain ⟨h0va, hpiva⟩ := inequality4_aim_in_convex_fan hcop hθ0 hθπ ht0 ht1
  rw [← hvadef] at h0va hpiva
  have hnc_va : ¬ Collinear3 x v va := by
    rw [hvadef]
    exact not_collinear_is_properties_fully_surrounded hfan hvu huw hθ0 hθπ t ht0 ht1
  have hpiva' : azim x v u va < azim x v u (sigmaFan x V E v u) :=
    lt_of_lt_of_le hpiva hle
  have hvxne : v ≠ x := (not_collinear3_left_anc hnc_va).symm
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvxne)
  have hnvpos : 0 < ‖v - x‖ := lt_of_le_of_ne (norm_nonneg _) fun h => hnv h.symm
  -- 标架基本量（x, v, va）
  have haxf : (v - x : V3) = ‖v - x‖ • e3Fan x v va := by
    rw [e3Fan, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have he1s : e1Fan x v va ⬝ᵥ e1Fan x v va = 1 := e1Fan_dot_self hnc_va
  have he3s : e3Fan x v va ⬝ᵥ e3Fan x v va = 1 := e3Fan_dot_self hvxne va
  have he1d3 : e1Fan x v va ⬝ᵥ e3Fan x v va = 0 := e1Fan_dot_e3 hnc_va
  have haxfc : (v : Fin 3 → ℝ) - (x : Fin 3 → ℝ)
      = ‖v - x‖ • ((e3Fan x v va : V3) : Fin 3 → ℝ) := by
    rw [← coe_sub_aux, ← coe_smul_aux]
    exact congrArg (fun z : V3 => (z : Fin 3 → ℝ)) haxf
  have he1vx : ((e1Fan x v va : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((v : Fin 3 → ℝ) - (x : Fin 3 → ℝ)) = 0 := by
    rw [haxfc, dot_smul_right_aux, he1d3, mul_zero]
  have he3vx : ((e3Fan x v va : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((v : Fin 3 → ℝ) - (x : Fin 3 → ℝ)) = ‖v - x‖ := by
    rw [haxfc, dot_smul_right_aux, he3s, mul_one]
  -- aff_gt {x} {v, va} ⊆ wedge x v u w1（HOL：aff_gt_inter_aff_gt +
  -- properties_of_collinear4_points_fan + AZIM_EQ_ALT）
  have hwedge : ∀ y : V3, y ∈ affGt {x} {v, va} →
      y ∈ wedge x v u (sigmaFan x V E v u) := by
    intro y hy
    have hsplit : y ∈ affGt {x, v} {va} ∩ affGt {x, va} {v} := by
      rw [← aff_gt_inter_aff_gt hnc_va]
      exact hy
    have hncy : ¬ Collinear3 x y v := properties_of_collinear4_points_fan hnc_va hy
    have hncy' : ¬ Collinear3 x v y := fun hc => hncy (collinear3_swap_anc hc)
    have heqy : azim x v u y = azim x v u va :=
      (azim_eq_azim_iff_alt hnc_vu hncy' hnc_va).mpr hsplit.1
    exact ⟨hncy', by rw [heqy]; exact h0va, by rw [heqy]; exact hpiva'⟩
  -- rcone 成员（HOL：正交标架 + SIN_CIRCLE + COS_MONO_LT）
  have hrcone : ∀ s1 : ℝ, 0 < s1 → s1 < s →
      Real.sin s1 • e1Fan x v va + Real.cos s1 • e3Fan x v va + x ∈
        rconeFan x v (Real.cos s) := by
    intro s1 hs1pos hs1s
    have hs1pi : s1 < Real.pi / 2 := lt_trans hs1s hsπ
    have hsin : 0 < Real.sin s1 :=
      Real.sin_pos_of_pos_of_lt_pi hs1pos (by linarith)
    have hcos1 : 0 < Real.cos s1 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hs1pi⟩
    have hcoslt : Real.cos s < Real.cos s1 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hs1pos)
        (by linarith [Real.pi_pos]) hs1s
    set w : V3 := Real.sin s1 • e1Fan x v va + Real.cos s1 • e3Fan x v va + x with hwdef
    have hwxs : w - x = Real.sin s1 • e1Fan x v va + Real.cos s1 • e3Fan x v va := by
      rw [hwdef]; module
    have he1n : ‖e1Fan x v va‖ = 1 := by
      have h : ‖e1Fan x v va‖ ^ 2 = 1 := by
        rw [norm_sq_eq_dot]; exact e1Fan_dot_self hnc_va
      nlinarith [h, norm_nonneg (e1Fan x v va), sq_nonneg (‖e1Fan x v va‖ - 1)]
    have he3n : ‖e3Fan x v va‖ = 1 := by
      have h : ‖e3Fan x v va‖ ^ 2 = 1 := by
        rw [norm_sq_eq_dot]; exact e3Fan_dot_self hvxne va
      nlinarith [h, norm_nonneg (e3Fan x v va), sq_nonneg (‖e3Fan x v va‖ - 1)]
    have hnw : ‖w - x‖ = 1 := by
      have h2 : ‖w - x‖ ^ 2 = 1 := by
        conv_lhs => rw [hwxs, norm_add_sq_real, norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsin, abs_of_pos hcos1,
          he1n, he3n, real_inner_smul_left, real_inner_smul_right, inner_eq_dot,
          e1Fan_dot_e3 hnc_va]
        have hsc := Real.sin_sq_add_cos_sq s1
        rw [sq, sq] at hsc
        linarith
      nlinarith [h2, norm_nonneg (w - x), sq_nonneg (‖w - x‖ - 1)]
    have hwdot : ((w - x : V3) : Fin 3 → ℝ)
        = Real.sin s1 • ((e1Fan x v va : V3) : Fin 3 → ℝ)
          + Real.cos s1 • ((e3Fan x v va : V3) : Fin 3 → ℝ) := by
      have hc := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hwxs
      rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul] at hc
      exact hc
    have hdot : ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v : Fin 3 → ℝ) - (x : Fin 3 → ℝ)) = Real.cos s1 * ‖v - x‖ := by
      rw [hwdot, dot_add_left_pi, smul_dot_pi, smul_dot_pi, he1vx, he3vx, mul_zero,
        zero_add]
    show ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) >
      dist w x * dist v x * Real.cos s
    rw [coe_sub_aux v x, hdot, dist_eq_norm, dist_eq_norm, hnw, one_mul]
    have hstep : (Real.cos s1 - Real.cos s) * ‖v - x‖ > 0 :=
      mul_pos (sub_pos.mpr hcoslt) hnvpos
    have hstep2 : Real.cos s1 * ‖v - x‖ - ‖v - x‖ * Real.cos s
        = (Real.cos s1 - Real.cos s) * ‖v - x‖ := by ring
    linarith
  -- 共用收尾
  rw [rwDartFan, wDartFan, if_pos hcardv]
  have finish : ∀ s1 : ℝ, 0 < s1 → s1 < s →
      (Real.sin s1 • e1Fan x v va + Real.cos s1 • e3Fan x v va + x ∈
        affGt {x} {v, va}) →
      (wedge x v u (sigmaFan x V E v u) ∩ rconeFan x v (Real.cos s)) ∩
        affGt {x} {v, va} ≠ ∅ := by
    intro s1 hs1pos hs1s hyaff
    exact Set.Nonempty.ne_empty
      ⟨_, ⟨⟨hwedge _ hyaff, hrcone _ hs1pos hs1s⟩, hyaff⟩⟩
  -- 按 (v - x) dot (va - x) 的符号二分（HOL 两支）
  rcases lt_or_ge 0 ((v - x) ⬝ᵥ (va - x)) with hd | hle'
  · -- 正支：s1 = min s (atn (|cross| / dot)) / 2
    have hCpos := cross_pos_of_not_collinear3_anc hnc_va
    have hApos : 0 < Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹) :=
      Real.arctan_pos.mpr (mul_pos hCpos (inv_pos.mpr hd))
    refine finish (min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) :
        Fin 3 → ℝ) ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹)) / 2)
      (div_pos (lt_min hs0 hApos) two_pos) ?_ ?_
    · have h1 : min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹)) ≤ s :=
        min_le_left _ _
      have h2 : min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹)) / 2
            ≤ s / 2 := by
        calc min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
              ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹)) / 2
              = min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
              ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (va - x))⁻¹)) * 2⁻¹ := by ring
          _ ≤ s * 2⁻¹ := mul_le_mul_of_nonneg_right h1 (by norm_num)
          _ = s / 2 := by ring
      linarith
    · exact condition_to_in_aff_gt_by_angle hnc_va hd
        (div_pos (lt_min hs0 hApos) two_pos)
        (by
          have h1 : min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) :
              Fin 3 → ℝ) ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ *
              ((v - x) ⬝ᵥ (va - x))⁻¹)) ≤ Real.arctan (‖(WithLp.toLp 2 (crossProduct
              ((v - x : V3) : Fin 3 → ℝ) ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ *
              ((v - x) ⬝ᵥ (va - x))⁻¹) := min_le_right _ _
          have h2 : 2 * (min s (Real.arctan (‖(WithLp.toLp 2 (crossProduct
              ((v - x : V3) : Fin 3 → ℝ) ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ *
              ((v - x) ⬝ᵥ (va - x))⁻¹)) / 2) = min s (Real.arctan (‖(WithLp.toLp 2
              (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((va - x : V3) : Fin 3 → ℝ)) : V3)‖ *
              ((v - x) ⬝ᵥ (va - x))⁻¹)) := by ring
          linarith)
  · -- 非正支：s1 = s / 2
    refine finish (s / 2) (div_pos hs0 two_pos) (by linarith) ?_
    exact condition1_to_in_aff_gt_by_angle hnc_va (div_pos hs0 two_pos) (by linarith) hle'

/-! ## 缩放、非共线与锥条件（planarity.hl:9981-10095） -/

/-- HOL planarity.hl:9981-10019 `scale_in_edges_fan`

HOL 原文：
```
!(x:real^3) (v:real^3) (u:real^3) (w:real^3).
DISJOINT {x} {v,u}
/\ w IN aff_gt {x} {v,u}
==>
(?a t:real. &0<a /\ &0<t /\ t< &1
/\ a%(w-x) = (&1-t)% v+ t%u-x)
```

证明思路：`aff_gt_1_2` 展开给 `w = t1•x + t2•v + t3•u`（`t2,t3>0`、
和为 1）；于是 `w - x = t2•(v-x) + t3•(u-x)`。令 `a = (1-t1)⁻¹`、
`t = t3/(1-t1)`：`0 < 1 - t1`（因 `t1 = 1 - t2 - t3 < 1`），
`a • (w - x) = (1-t)•(v-x) + t•(u-x) = (1-t)•v + t•u - x`，
正性由 `REAL_LT_MUL`/`inv_pos`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165） -/
theorem scale_in_edges_fan {x v u w : V3}
    (hdis : Disjoint ({x} : Set V3) {v, u}) (hw : w ∈ affGt {x} {v, u}) :
    ∃ a t : ℝ, 0 < a ∧ 0 < t ∧ t < 1 ∧
      a • (w - x) = (1 - t) • v + t • u - x := by
  rw [aff_gt_1_2 hdis] at hw
  simp only [Set.mem_setOf_eq] at hw
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hw_eq⟩ := hw
  have hs : 0 < t2 + t3 := add_pos ht2 ht3
  have hA : (t2 + t3)⁻¹ * (t2 + t3) = 1 := inv_mul_cancel₀ (ne_of_gt hs)
  have ht : t3 / (t2 + t3) = (t2 + t3)⁻¹ * t3 := by
    rw [div_eq_inv_mul, mul_comm]
  have hx' : (t2 + t3)⁻¹ * t1 - (t2 + t3)⁻¹ = -1 := by
    have h1 : t1 - 1 = -(t2 + t3) := by linarith
    have hstep : (t2 + t3)⁻¹ * t1 - (t2 + t3)⁻¹
        = (t2 + t3)⁻¹ * (t1 - 1) := by ring
    rw [hstep, h1, mul_neg, hA]
  have hv' : (t2 + t3)⁻¹ * t2 = 1 - (t2 + t3)⁻¹ * t3 := by
    rw [eq_sub_iff_add_eq, ← mul_add, hA]
  refine ⟨(t2 + t3)⁻¹, t3 / (t2 + t3), inv_pos.2 hs, div_pos ht3 hs, ?_, ?_⟩
  · rw [div_lt_iff₀ hs]
    linarith
  · have hnx : (-1 : ℝ) • x = -x := by simp
    calc (t2 + t3)⁻¹ • (w - x)
        = ((t2 + t3)⁻¹ * t1 - (t2 + t3)⁻¹) • x + ((t2 + t3)⁻¹ * t2) • v
            + ((t2 + t3)⁻¹ * t3) • u := by
          rw [hw_eq, smul_sub, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
          have e2 : ((t2 + t3)⁻¹ * t1) • x + ((t2 + t3)⁻¹ * t2) • v
                  + ((t2 + t3)⁻¹ * t3) • u - (t2 + t3)⁻¹ • x
              = (((t2 + t3)⁻¹ * t1) • x - (t2 + t3)⁻¹ • x)
                + ((t2 + t3)⁻¹ * t2) • v + ((t2 + t3)⁻¹ * t3) • u := by abel
          rw [e2, sub_smul]
      _ = (-1 : ℝ) • x + ((t2 + t3)⁻¹ * t2) • v + ((t2 + t3)⁻¹ * t3) • u := by
          rw [hx']
      _ = -x + ((t2 + t3)⁻¹ * t2) • v + ((t2 + t3)⁻¹ * t3) • u := by
          rw [hnx]
      _ = -x + (1 - (t2 + t3)⁻¹ * t3) • v + ((t2 + t3)⁻¹ * t3) • u := by
          rw [hv']
      _ = (1 - (t2 + t3)⁻¹ * t3) • v + ((t2 + t3)⁻¹ * t3) • u - x := by
          abel
      _ = (1 - t3 / (t2 + t3)) • v + (t3 / (t2 + t3)) • u - x := by
          rw [← ht]

/-- HOL planarity.hl:10020-10050 `aff_gt_imp_not_collinear`

HOL 原文：
```
!x u v w:real^3.
~collinear{x,v,u}/\ w IN aff_gt{x,v} {u}==> ~collinear{x,v,w}
```

证明思路：HOL 用 AFF_GT_2_1 展开 `w = t1•x + t2•v + t3•u`（`t3>0`、
和 1）。若 `collinear {x,v,w}`，即 `w ∈ affineSpan {x,v}`：
`w = u'•x + v'•v`，则 `t3•u = (u'-t1)•x + (v'-t2)•v`，除以 `t3` 得
`u ∈ aff {x,v}`，与 `~collinear {x,v,u}` 矛盾。
Lean 侧 `aff_gt_2_1` 未移植：用 `affGt_pair_iff`（AFF_GT_2_1 的射线
刻画，`w - x = c•(u-x) + h•(v-x)`，`c>0`）+ `Collinear` 的
affineSpan characterization（Mathlib `collinear_iff`/
`mem_affineSpan_pair`）完成同一归约。

候选已有引理：
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `collinear3_of_eq` / `collinear3_pair_left` / `collinear3_pair_right`
  （Kepler/Geom/Azim.lean:121、Kepler/Geom/AzimLemmas.lean:164-171） -/
theorem aff_gt_imp_not_collinear {x v u w : V3}
    (hnc : ¬ Collinear3 x v u) (hw : w ∈ affGt {x, v} {u}) :
    ¬ Collinear3 x v w := by
  -- 基本非退化：x ≠ v、u ≠ x、u ≠ v（否则 hnc 直接矛盾）
  have hxv : x ≠ v := fun he =>
    hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  have hux : u ≠ x := fun he =>
    hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := u) he)
  have huv : u ≠ v := fun he =>
    hnc (collinear3_pair_right (v0 := x) (v1 := v) (x := u) he)
  -- AFF_GT_2_1 的射线刻画：w - x = c•(u - x) + k•(v - x)，c > 0
  obtain ⟨c, hc0, k, hw_eq⟩ := (affGt_pair_iff hxv hux huv).mp hw
  -- 若 collinear {x,v,w}：w - x = c'•(v - x)
  intro hcol
  obtain ⟨c', hw_eq2⟩ := (collinear3_iff_smul (Ne.symm hxv)).mp hcol
  have h1 : c • (u - x) + k • (v - x) = c' • (v - x) := by
    rw [← hw_eq2, hw_eq]
  have h3 : c • (u - x) = (c' - k) • (v - x) := by
    rw [sub_smul, eq_sub_iff_add_eq]
    exact h1
  -- 除以 c > 0 得 u ∈ aff {x,v}，即 Collinear3 x v u，矛盾
  have hcne : c ≠ 0 := hc0.ne'
  exact hnc ((collinear3_iff_smul (Ne.symm hxv)).mpr ⟨c⁻¹ * (c' - k), by
    calc u - x = (c⁻¹ * c) • (u - x) := by rw [inv_mul_cancel₀ hcne, one_smul]
      _ = c⁻¹ • (c • (u - x)) := by rw [smul_smul]
      _ = c⁻¹ • ((c' - k) • (v - x)) := by rw [h3]
      _ = (c⁻¹ * (c' - k)) • (v - x) := by rw [smul_smul]⟩)

/-- HOL planarity.hl:10051-10095 `conditions_in_rcone_fan`

HOL 原文：
```
!x v u w:real^3 s:real.
~collinear {x,v,u}/\ w IN aff_gt {x} {v,u} /\ &0<s /\ s< pi/ &2 /\u IN rcone_fan x v (cos s)==> w IN rcone_fan x v (cos s)
```

证明思路：`rcone_fan` 展开为目标
`(w-x) dot (v-x) > |w-x| * |v-x| * cos s`。`aff_gt_1_2` 给
`w - x = t2•(v-x) + t3•(u-x)`（`t2,t3>0`）。LHS =
`t2*|v-x|² + t3*((u-x) dot (v-x))`；由 `u ∈ rcone` 与 Cauchy-Schwarz
`((u-x) dot (v-x)) > |u-x|*|v-x|*cos s`；RHS 由三角不等式
`|w-x| <= t2*|v-x| + t3*|u-x|` 与 `cos s >= 0`（COS_POS_PI2）放大
合并即得（HOL 的 NORM_TRIANGLE + REAL_LE_RMUL 链）。

候选已有引理：
- `rconeFan` 定义（Kepler/Text/TopologyFan.lean:2253）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- Mathlib `norm_add_le`（三角不等式）、`abs_inner_le_norm`/
  Cauchy–Schwarz（dot 与范数乘积） -/
theorem conditions_in_rcone_fan {x v u w : V3} {s : ℝ}
    (hnc : ¬ Collinear3 x v u) (hw : w ∈ affGt {x} {v, u})
    (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hu : u ∈ rconeFan x v (Real.cos s)) :
    w ∈ rconeFan x v (Real.cos s) := by
  -- 非退化：x ∉ {v, u}（否则与 hnc 矛盾），故 {x} 与 {v,u} 不交
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_singleton_left]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) h.symm)
    · exact hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := u) h.symm)
  -- 展开目标与假设，dist 全部换为范数
  rw [rconeFan]
  simp only [Set.mem_setOf_eq, dist_eq_norm]
  rw [rconeFan] at hu
  simp only [Set.mem_setOf_eq, dist_eq_norm] at hu
  -- cos 的符号事实
  have hcos_nn : 0 ≤ Real.cos s :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hsπ⟩)
  have hcos_le : Real.cos s ≤ 1 := Real.cos_le_one s
  have hnp : 0 ≤ ‖v - x‖ := norm_nonneg _
  -- aff_gt_1_2 分解：w = t1•x + t2•v + t3•u，t2,t3 > 0
  have hw' : w ∈ {y : V3 | ∃ t1 t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t1 + t2 + t3 = 1 ∧
      y = t1 • x + t2 • v + t3 • u} := by
    rw [← aff_gt_1_2 hdis]
    exact hw
  obtain ⟨t1, t2, t3, ht2, ht3, htsum, hw_eq⟩ := hw'
  -- w - x = t2•(v - x) + t3•(u - x)
  have hwsub : w - x = t2 • (v - x) + t3 • (u - x) := by
    have hxe : (t1 + t2 + t3) • x = x := by rw [htsum, one_smul]
    have expand : t1 • x + t2 • v + t3 • u - x
        = t2 • (v - x) + t3 • (u - x) + ((t1 + t2 + t3) • x - x) := by module
    rw [hxe, sub_self, add_zero] at expand
    rw [hw_eq]
    exact expand
  -- 点积展开
  have hdot : (w - x) ⬝ᵥ (v - x)
      = t2 * ((v - x) ⬝ᵥ (v - x)) + t3 * ((u - x) ⬝ᵥ (v - x)) := by
    rw [hwsub, dot_add_left_anc, smul_dot_aux, smul_dot_aux]
  have hself : (v - x) ⬝ᵥ (v - x) = ‖v - x‖ * ‖v - x‖ :=
    (norm_sq_eq_dot (v - x)).symm.trans (pow_two _)
  -- 三角不等式：|w-x| ≤ t2*|v-x| + t3*|u-x|
  have htri : ‖w - x‖ ≤ t2 * ‖v - x‖ + t3 * ‖u - x‖ := by
    rw [hwsub]
    calc ‖t2 • (v - x) + t3 • (u - x)‖ ≤ ‖t2 • (v - x)‖ + ‖t3 • (u - x)‖ :=
        norm_add_le _ _
      _ = t2 * ‖v - x‖ + t3 * ‖u - x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ht2, abs_of_pos ht3]
  -- 逐项估计并合并
  rw [hdot, hself]
  have s1 : t3 * ((u - x) ⬝ᵥ (v - x))
      > t3 * (‖u - x‖ * ‖v - x‖ * Real.cos s) :=
    mul_lt_mul_of_pos_left hu ht3
  have hc1 : 0 ≤ 1 - Real.cos s := sub_nonneg.mpr hcos_le
  have s2 : t2 * (‖v - x‖ * ‖v - x‖ * Real.cos s) ≤ t2 * (‖v - x‖ * ‖v - x‖) := by
    have hppc : ‖v - x‖ * ‖v - x‖ * Real.cos s ≤ ‖v - x‖ * ‖v - x‖ := by
      nlinarith [mul_nonneg (mul_nonneg hnp hnp) hc1]
    exact mul_le_mul_of_nonneg_left hppc (le_of_lt ht2)
  have e3 : (t2 * ‖v - x‖ + t3 * ‖u - x‖) * ‖v - x‖ * Real.cos s
      ≥ ‖w - x‖ * ‖v - x‖ * Real.cos s := by
    have h5 : ‖w - x‖ * Real.cos s ≤ (t2 * ‖v - x‖ + t3 * ‖u - x‖) * Real.cos s :=
      mul_le_mul_of_nonneg_right htri hcos_nn
    have h6 : ‖w - x‖ * Real.cos s * ‖v - x‖
        ≤ (t2 * ‖v - x‖ + t3 * ‖u - x‖) * Real.cos s * ‖v - x‖ :=
      mul_le_mul_of_nonneg_right h5 hnp
    nlinarith [h6]
  calc t2 * (‖v - x‖ * ‖v - x‖) + t3 * ((u - x) ⬝ᵥ (v - x))
      > t2 * (‖v - x‖ * ‖v - x‖) + t3 * (‖u - x‖ * ‖v - x‖ * Real.cos s) :=
        by linarith
    _ ≥ t2 * (‖v - x‖ * ‖v - x‖ * Real.cos s) + t3 * (‖u - x‖ * ‖v - x‖ * Real.cos s) :=
        by linarith
    _ = (t2 * ‖v - x‖ + t3 * ‖u - x‖) * ‖v - x‖ * Real.cos s := by ring
    _ ≥ ‖w - x‖ * ‖v - x‖ * Real.cos s := e3

/-! ## 锥内取点与弦切割（planarity.hl:10096-10806，batch 2 skeleton） -/

/-- 三点仿射包成员（Planarity 私有引理 `mem_affineSpan_triple_of_eq` 的复制）。 -/
private theorem mem_affineSpan_triple_of_eq_pa {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (q - x) + h • (p - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : c • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd4 : h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd5 : c • (q - x) + h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval : y = h • (p - x) +ᵥ (c • (q - x) +ᵥ x) := by
    rw [hy, vadd_eq_add, vadd_eq_add]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd4
    (AffineSubspace.vadd_mem_of_mem_direction hd3 hxS)

/-- 混合积轮换（Planarity 私有引理 `cross_dot_cycle` 的复制）。 -/
private theorem cross_dot_cycle_pa {X Y Z : Fin 3 → ℝ} :
    crossProduct X Y ⬝ᵥ Z = crossProduct Y Z ⬝ᵥ X := by
  rw [dotProduct_comm, triple_product_permutation, dotProduct_comm]

/-- 叉积第二变元的标量分配（Planarity 私有引理的复制）。 -/
private theorem crossProduct_smul_right_pa (c : ℝ) (p q : Fin 3 → ℝ) :
    crossProduct p (c • q) = c • crossProduct p q :=
  (crossProduct p).map_smul c q

/-- HOL planarity.hl:10096-10328 `exists_point_inside_domain_cone_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 s:real.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ &0<s /\ s<pi/ &2
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
(?y:real^3. y IN rw_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(w2:real^3)) (cos(s)) /\
azim x v u y< azim x v u w)
```

证明思路：fan80(u,w) + hsigma 给 `0 < azim x u w v < π`，
`properties_fully_surrounded` 给 ¬Coplanar {x,v,u,w}；分支
`CARD(set_of_edge u) = 1` 与 hcard u 矛盾，故 CARD > 1，
`not_empty_rw_dart_fan` 给 y ∈ rw_dart(cos s)（wedge 侧
`azim x u w y < azim x u w v`，配合 `sum4_azim_fan` 与
`azim_compl`、`azim_eq_zero_iff`（AZIM_EQ_0_PI_EQ_COPLANAR 的替代）
排除 azim = 0/π 退化）。主构造 `v3 = ((y-x)×(u-x))×((v-x)×(w-x)) + x`
与 `v4 = ½•v3 + ½•u`：`aff_gt_1_2` 展开系数
（t1 = 1 - va⬝a2 + va⬝a3 等），正性由
`cross_dot_fully_surrounded_fan` / `_ge_fan`（CROSS_LAGRANGE =
Mathlib `cross_dot_cross` 展开），最后
`inequality4_aim_in_convex_fan` + `conditions_in_rcone_fan` 收尾。
注意：HOL 原文结论里的 `w2` 是自由变量（Flyspeck 笔误）；
`rwDartFan` 不依赖四元组第 4 分量（wedge 用 sigmaFan，
见 `wDartFan` 定义），故按全称量化绑定为定理参数（HOL 侧
MATCH 时自由变量即被实例化，语义一致）。

候选已有引理：
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `properties_of_fully_surrounded1_fan`（Kepler/Text/PlanarityNotCut.lean:2330）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318，AZIM_COMPL）
- `azim_eq_zero_iff` / `azim_eq_zero_iff_alt`（Kepler/Geom/AzimLemmas.lean:296/307，
  AZIM_EQ_0_PI_EQ_COPLANAR 的替代）
- `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193，AZIM_EQ_ALT）
- `cross_dot_fully_surrounded_fan` / `_ge_fan`
  （Kepler/Text/Planarity.lean:2860/2876）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `inequality4_aim_in_convex_fan`（Kepler/Text/PlanarityNotCut.lean:2474）
- `conditions_in_rcone_fan` / `aff_gt_imp_not_collinear`（本文件 batch 1） -/
theorem exists_point_inside_domain_cone_fan {x v u w w2 : V3} {V : Set V3}
    {E : Set (Set V3)} {s : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    ∃ y : V3, y ∈ rwDartFan x V E (x, u, w, w2) (Real.cos s) ∧
      azim x v u y < azim x v u w := by
  -- 基本成员与 fan80 角度（HOL：fan80 + remark1_fan）
  have huV : u ∈ V := (fan_mem_of_edge hfan huw).1
  have hcardu : 1 < (setOfEdge u V E).ncard := hcard u huV
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  -- 非共面/非共线基本盘
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  obtain ⟨hncuw, hncvu, hncvw⟩ := notcoplanar_imp_notcollinear_fan hcop
  have hncuv : ¬ Collinear3 x u v := fun hc => hncvu (collinear3_swap_anc hc)
  have hux : u ≠ x := fun he => hncuw (collinear3_of_eq he)
  -- 取 y ∈ rwDart（not_empty_rw_dart_fan；rwDartFan 不依赖四元组第 4 分量）
  obtain ⟨y, hyr⟩ := not_empty_rw_dart_fan (v := u) (u := w) hfan huw hs hsπ
  rw [hsigma] at hyr
  have hyr2 : y ∈ rwDartFan x V E (x, u, w, w2) (Real.cos s) := by
    have heq : rwDartFan x V E (x, u, w, w2) (Real.cos s)
        = rwDartFan x V E (x, u, w, v) (Real.cos s) := by
      simp only [rwDartFan, wDartFan]
    rw [heq]
    exact hyr
  -- 拆分 rwDart：wedge + rcone
  have hycone : y ∈ rconeFan x u (Real.cos s) := by
    have h1 : y ∈ rwDartFan x V E (x, u, w, v) (Real.cos s) := hyr
    rw [rwDartFan] at h1
    exact h1.2
  have hywedge : y ∈ wedge x u w v := by
    have h1 : y ∈ rwDartFan x V E (x, u, w, v) (Real.cos s) := hyr
    rw [rwDartFan] at h1
    have h2 := h1.1
    rw [wDartFan, if_pos hcardu, hsigma] at h2
    exact h2
  rw [wedge, Set.mem_setOf_eq] at hywedge
  obtain ⟨hncuy, h0y, hyv⟩ := hywedge
  -- 三点角加法（HOL sum4_azim_fan）→ azim x u y v ∈ (0, π)
  have hsum : azim x u w v = azim x u w y + azim x u y v :=
    sum4_azim_fan hux hncuw hncuy hncuv (le_of_lt hyv)
  have h0yv : 0 < azim x u y v := by linarith
  have hyvpi : azim x u y v < Real.pi := by linarith
  -- 混合积正性（HOL cross_dot_fully_surrounded_fan[x;u;y;v] 侧）：
  -- 0 < (u-x)×(y-x)⬝(v-x)
  have hD1 : 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((v - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (v1 := u) (v := y) (u1 := v) hncuv hncuy h0yv hyvpi
  -- ¬Collinear3 x v y：y = x 时 azim x u w y = 0 矛盾；y - x ∥ v - x 时混合积为 0 矛盾
  have hncvy : ¬ Collinear3 x v y := by
    intro hcol
    rcases eq_or_ne y x with hyx | hyx
    · exfalso
      have h0 : azim x u w y = 0 := by
        rw [hyx]
        show (if Collinear3 x u w ∨ Collinear3 x u x then (0 : ℝ)
            else Classical.epsilon _) = 0
        rw [if_pos (Or.inr (collinear3_pair_left rfl))]
      linarith
    · exfalso
      have hxv : x ≠ v := fun he => hncvu (by rw [he]; exact collinear3_of_eq rfl)
      obtain ⟨μ, hμ⟩ := (collinear3_iff_smul (Ne.symm hxv)).mp hcol
      have hcoe : ((y - x : V3) : Fin 3 → ℝ) = μ • ((v - x : V3) : Fin 3 → ℝ) := by
        rw [← coe_smul_aux]
        exact congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hμ
      have hzero : crossProduct ((u - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ
          ((v - x : V3) : Fin 3 → ℝ) = 0 := by
        rw [hcoe, crossProduct_smul_right_pa, smul_dotProduct, smul_eq_mul,
          dotProduct_comm (crossProduct ((u - x : V3) : Fin 3 → ℝ)
            ((v - x : V3) : Fin 3 → ℝ)) ((v - x : V3) : Fin 3 → ℝ),
          dot_cross_self, mul_zero]
      linarith
  -- 主分支：azim x v u y 与 π 的比较（HOL 分支 4 的矛盾，含 = π 情形）
  rcases lt_or_ge (azim x v u y) Real.pi with hvyπ | hvypi
  · -- azim x v u y < π
    rcases (lt_or_ge (azim x v u y) (azim x v u w)).symm with hlewy | hlty
    · -- 大支：azim x v u w ≤ azim x v u y，构造 v3 / v4（HOL 分支 5a）
      -- 记号（HOL ABBREV）：a1 = v-x, a2 = y-x, a3 = u-x, a4 = w-x
      obtain ⟨a1, ha1⟩ : ∃ f : Fin 3 → ℝ, f = ((v - x : V3) : Fin 3 → ℝ) := ⟨_, rfl⟩
      obtain ⟨a2, ha2⟩ : ∃ f : Fin 3 → ℝ, f = ((y - x : V3) : Fin 3 → ℝ) := ⟨_, rfl⟩
      obtain ⟨a3, ha3⟩ : ∃ f : Fin 3 → ℝ, f = ((u - x : V3) : Fin 3 → ℝ) := ⟨_, rfl⟩
      obtain ⟨a4, ha4⟩ : ∃ f : Fin 3 → ℝ, f = ((w - x : V3) : Fin 3 → ℝ) := ⟨_, rfl⟩
      -- 混合积正性（HOL cross_dot_fully_surrounded_fan[x;u;v;w] 侧）：
      -- 0 < (u-x)×(w-x)⬝(v-x)
      have hP1 : 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ) ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
          ((v - x : V3) : Fin 3 → ℝ) :=
        cross_dot_fully_surrounded_fan (v1 := u) (v := w) (u1 := v) hncuv hncuw hθ0 hθπ
      rw [← ha3, ← ha4, ← ha1] at hP1
      rw [← ha3, ← ha2, ← ha1] at hD1
      -- 系数正性（HOL 子目标 6/8 的 t3 / t3' > 0）
      have ht3 : 0 < -(crossProduct a1 a4 ⬝ᵥ a3) := by
        rw [cross_dot_cycle_pa, ← cross_anticomm, neg_dotProduct, neg_neg]
        exact hP1
      have ht3' : 0 < -(crossProduct a2 a3 ⬝ᵥ a1) := by
        rw [← cross_anticomm, neg_dotProduct, neg_neg]
        exact hD1
      -- v3 := (a2×a3)×(a1×a4) + x（HOL ABBREV v3）
      obtain ⟨v3, hv3⟩ : ∃ z : V3,
          z = (WithLp.toLp 2 (crossProduct (crossProduct a2 a3)
            (crossProduct a1 a4)) : V3) + x := ⟨_, rfl⟩
      have hv3x : v3 - x = (WithLp.toLp 2 (crossProduct (crossProduct a2 a3)
          (crossProduct a1 a4)) : V3) := by
        rw [hv3]; module
      -- CROSS_LAGRANGE 两种展开
      have hE1 : v3 - x = (crossProduct a2 a3 ⬝ᵥ a4) • (v - x)
          - (crossProduct a2 a3 ⬝ᵥ a1) • (w - x) := by
        have hc := cross_cross_eq_smul_sub_smul' (crossProduct a2 a3) a1 a4
        rw [dotProduct_comm a1 (crossProduct a2 a3)] at hc
        rw [hv3x]
        have hx1 : (v - x : V3) = (WithLp.toLp 2 a1 : V3) := by
          rw [ha1]
        have hx4 : (w - x : V3) = (WithLp.toLp 2 a4 : V3) := by
          rw [ha4]
        rw [hx1, hx4, ← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_sub, hc]
      have hE2 : v3 - x = (crossProduct a1 a4 ⬝ᵥ a2) • (u - x)
          - (crossProduct a1 a4 ⬝ᵥ a3) • (y - x) := by
        have hc2 := cross_cross_eq_smul_sub_smul' (crossProduct a1 a4) a2 a3
        rw [dotProduct_comm a2 (crossProduct a1 a4)] at hc2
        have hanti : crossProduct (crossProduct a2 a3) (crossProduct a1 a4)
            = -crossProduct (crossProduct a1 a4) (crossProduct a2 a3) :=
          (cross_anticomm (crossProduct a1 a4) (crossProduct a2 a3)).symm
        rw [hv3x]
        have hx3 : (u - x : V3) = (WithLp.toLp 2 a3 : V3) := by
          rw [ha3]
        have hxy : (y - x : V3) = (WithLp.toLp 2 a2 : V3) := by
          rw [ha2]
        rw [hx3, hxy, ← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
          hanti, hc2, neg_sub]
      -- 非退化（th3 的角色）
      have hxv : x ≠ v := fun he => hncvu (by rw [he]; exact collinear3_of_eq rfl)
      have hwx : w ≠ x := fun he => hncvw (by rw [he]; exact collinear3_pair_left rfl)
      have hwv : w ≠ v := fun he => hncvw (by rw [he]; exact collinear3_pair_right rfl)
      have hyx : y ≠ x := fun he => hncuy (by rw [he]; exact collinear3_pair_left rfl)
      have hyu : y ≠ u := fun he => hncuy (by rw [he]; exact collinear3_pair_right rfl)
      have hxu : x ≠ u := fun he => hncuw (by rw [he]; exact collinear3_of_eq rfl)
      -- aff_gt 成员（HOL AFF_GT_2_1 的射线刻画 affGt_pair_iff）
      have hv3vw : v3 ∈ affGt {x, v} {w} :=
        (affGt_pair_iff hxv hwx hwv).mpr ⟨-(crossProduct a2 a3 ⬝ᵥ a1), ht3',
          crossProduct a2 a3 ⬝ᵥ a4, by rw [hE1]; module⟩
      have hv3uy : v3 ∈ affGt {x, u} {y} :=
        (affGt_pair_iff hxu hyx hyu).mpr ⟨-(crossProduct a1 a4 ⬝ᵥ a3), ht3,
          crossProduct a1 a4 ⬝ᵥ a2, by rw [hE2]; module⟩
      have hncv3 : ¬ Collinear3 x v v3 := aff_gt_imp_not_collinear hncvw hv3vw
      have hncuv3 : ¬ Collinear3 x u v3 := aff_gt_imp_not_collinear hncuy hv3uy
      -- 方位角传递（HOL AZIM_EQ_ALT 两次）
      have hzvs : azim x v u v3 = azim x v u w :=
        (azim_eq_azim_iff_alt hncvu hncv3 hncvw).mpr hv3vw
      have hzu : azim x u v v3 = azim x u v y :=
        (azim_eq_azim_iff_alt hncuv hncuv3 hncuy).mpr hv3uy
      -- azim x u v3 v = azim x u y v ∈ (0, π)（HOL 子目标 10 的消除 + AZIM_COMPL 双侧）
      have hv3vne : azim x u v3 v ≠ 0 := by
        intro h0
        have hc : azim x u v v3 = 0 := by
          rw [azim_compl hncuv3 hncuv, if_pos h0]
        have hcompl1 : azim x u v y = 2 * Real.pi - azim x u y v := by
          rw [azim_compl hncuy hncuv, if_neg (ne_of_gt h0yv)]
        rw [hzu, hcompl1] at hc
        have h2pi := azim_lt_two_pi x u y v
        linarith
      have hkey : azim x u v3 v = azim x u y v := by
        have hc : azim x u v v3 = 2 * Real.pi - azim x u v3 v := by
          rw [azim_compl hncuv3 hncuv, if_neg hv3vne]
        have hcompl1 : azim x u v y = 2 * Real.pi - azim x u y v := by
          rw [azim_compl hncuy hncuv, if_neg (ne_of_gt h0yv)]
        rw [hzu, hcompl1] at hc
        have h2pi := azim_lt_two_pi x u y v
        linarith
      have hv3v0 : 0 < azim x u v3 v := by rw [hkey]; exact h0yv
      have hv3vpi : azim x u v3 v < Real.pi := by rw [hkey]; exact hyvpi
      -- w ∈ aff{x,v,v3}（由 t3' > 0 反解；HOL 子目标 9 的准备）
      have hwspan : w ∈ (affineSpan ℝ ({x, v, v3} : Set V3) : Set V3) := by
        have hCne : crossProduct a2 a3 ⬝ᵥ a1 ≠ 0 := by
          intro h0
          rw [h0] at ht3'
          norm_num at ht3'
        have hmul : (crossProduct a2 a3 ⬝ᵥ a1)⁻¹ * (crossProduct a2 a3 ⬝ᵥ a1) = 1 :=
          inv_mul_cancel₀ hCne
        have hstep : (crossProduct a2 a3 ⬝ᵥ a1)⁻¹ • (v3 - x)
            = ((crossProduct a2 a3 ⬝ᵥ a1)⁻¹ * (crossProduct a2 a3 ⬝ᵥ a4)) • (v - x)
              - (w - x) := by
          rw [hE1, smul_sub, smul_smul, smul_smul, hmul, one_smul]
        refine mem_affineSpan_triple_of_eq_pa (x := x) (p := v) (q := v3)
          (c := -((crossProduct a2 a3 ⬝ᵥ a1)⁻¹))
          (h := ((crossProduct a2 a3 ⬝ᵥ a1)⁻¹) * (crossProduct a2 a3 ⬝ᵥ a4)) ?_
        rw [neg_smul, hstep, neg_sub]
        module
      -- ¬Coplanar {x,v,u,v3}（HOL 子目标 9）
      have hcop3 : ¬ Coplanar ({x, v, u, v3} : Set V3) := by
        intro hcpl
        obtain ⟨p, q, r, hsub⟩ := hcpl
        apply hcop
        refine ⟨p, q, r, ?_⟩
        have hxS : x ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := hsub (by simp)
        have hvS : v ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := hsub (by simp)
        have huS : u ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := hsub (by simp)
        have hv3S : v3 ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := hsub (by simp)
        have hle : affineSpan ℝ ({x, v, v3} : Set V3) ≤ affineSpan ℝ ({p, q, r} : Set V3) :=
          affineSpan_le.mpr (by
            intro z hz'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
            rcases hz' with rfl | rfl | rfl
            · exact hxS
            · exact hvS
            · exact hv3S)
        have hwS : w ∈ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := hle hwspan
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hxS
        · exact hvS
        · exact huS
        · exact hwS
      -- azim x v w y ∈ [0, π] → va⬝a2 ≥ 0（HOL 末段 cross_dot_fully_surrounded_ge_fan）
      have hsum2 : azim x v u y = azim x v u w + azim x v w y :=
        sum4_azim_fan (Ne.symm hxv) hncvu hncvw hncvy hlewy
      have hge2 : 0 ≤ crossProduct ((v - x : V3) : Fin 3 → ℝ) ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
          ((y - x : V3) : Fin 3 → ℝ) := by
        refine cross_dot_fully_surrounded_ge_fan (v1 := v) (v := w) (u1 := y) hncvy hncvw ?_ ?_
        · exact azim_nonneg x v w y
        · have h1 := azim_nonneg x v u w
          have h2 : azim x v w y = azim x v u y - azim x v u w := by
            rw [hsum2]; ring
          rw [h2]
          linarith
      rw [← ha1, ← ha4, ← ha2] at hge2
      -- v4 := ½•u + ½•v3（HOL ABBREV v4）
      obtain ⟨v4, hv4⟩ : ∃ z : V3,
          z = (1 - 1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v3 := ⟨_, rfl⟩
      have hv4x : v4 - x = (1 / 2 : ℝ) • (u - x) + (1 / 2 : ℝ) • (v3 - x) := by
        rw [hv4]; module
      -- v4 的两组 aff_gt 成员
      have hv4uy : v4 ∈ affGt {x, u} {y} :=
        (affGt_pair_iff hxu hyx hyu).mpr ⟨(1 / 2 : ℝ) * (-(crossProduct a1 a4 ⬝ᵥ a3)),
          mul_pos (by norm_num) ht3,
          (1 / 2 : ℝ) * (crossProduct a1 a4 ⬝ᵥ a2) + 1 / 2, by
            rw [hv4x, hE2]
            module⟩
      have hv4uy' : v4 ∈ affGt {x} {u, y} := by
        rw [aff_gt_1_2 (disjoint_singleton_of_not_collinear3_anc hncuy)]
        refine ⟨(1 / 2 : ℝ) * (1 - (crossProduct a1 a4 ⬝ᵥ a2)
            + (crossProduct a1 a4 ⬝ᵥ a3)),
          (1 / 2 : ℝ) * (crossProduct a1 a4 ⬝ᵥ a2) + 1 / 2,
          (1 / 2 : ℝ) * (-(crossProduct a1 a4 ⬝ᵥ a3)), ?_, ?_, ?_, ?_⟩
        · linarith
        · exact mul_pos (by norm_num) ht3
        · ring
        · have h1 : v4 - x = ((1 / 2 : ℝ) * (crossProduct a1 a4 ⬝ᵥ a2) + 1 / 2) • (u - x)
              + ((1 / 2 : ℝ) * (-(crossProduct a1 a4 ⬝ᵥ a3))) • (y - x) := by
            rw [hv4x, hE2]
            module
          rw [← sub_add_cancel v4 x, h1]
          module
      -- v4 ∈ rwDart：wedge + rcone
      have hncv4 : ¬ Collinear3 x u v4 := aff_gt_imp_not_collinear hncuy hv4uy
      have hzv4 : azim x u w v4 = azim x u w y :=
        (azim_eq_azim_iff_alt hncuw hncv4 hncuy).mpr hv4uy
      have hv4cone : v4 ∈ rconeFan x u (Real.cos s) :=
        conditions_in_rcone_fan hncuy hv4uy' hs hsπ hycone
      have hv4wedge : v4 ∈ wedge x u w v := by
        rw [wedge, Set.mem_setOf_eq]
        refine ⟨hncv4, ?_, ?_⟩
        · rw [hzv4]; exact h0y
        · rw [hzv4]; exact hyv
      -- 弦角夹逼（HOL inequality4_aim_in_convex_fan）
      obtain ⟨-, hv4b⟩ := inequality4_aim_in_convex_fan (v := v) (u := u) (w := v3)
        (a := 1 / 2) hcop3 hv3v0 hv3vpi (by norm_num) (by norm_num)
      rw [← hv4] at hv4b
      exact ⟨v4, by
        rw [rwDartFan, wDartFan, if_pos hcardu, hsigma]
        exact ⟨hv4wedge, hv4cone⟩, by
        rw [← hzvs]
        exact hv4b⟩
    · -- 小支：azim x v u y < azim x v u w，直接取 y
      exact ⟨y, hyr2, hlty⟩
  · -- Real.pi ≤ azim x v u y：矛盾（HOL 分支 4）
    exfalso
    have hne0 : azim x v u y ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le Real.pi_pos hvypi)
    have hcompl : azim x v y u = 2 * Real.pi - azim x v u y := by
      rw [azim_compl hncvu hncvy, if_neg hne0]
    have hge1 : 0 ≤ azim x v y u := azim_nonneg x v y u
    have hle1 : azim x v y u ≤ Real.pi := by
      rw [hcompl]
      linarith [azim_lt_two_pi x v u y]
    have hge : 0 ≤ crossProduct ((v - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((u - x : V3) : Fin 3 → ℝ) :=
      cross_dot_fully_surrounded_ge_fan (v1 := v) (v := y) (u1 := u) hncvu hncvy hge1 hle1
    have hrel : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((u - x : V3) : Fin 3 → ℝ)
        = -(crossProduct ((u - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) ⬝ᵥ
          ((v - x : V3) : Fin 3 → ℝ)) := by
      rw [cross_dot_cycle_pa, ← cross_anticomm, neg_dotProduct]
    linarith

/-- HOL planarity.hl:10329-10384 `cut_in_angle_fan`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 w:real^3 y:real^3.
 ~coplanar {x,v,u,w} /\ ~collinear {x,u,y}
/\ &0< azim x u w v /\ azim x u w v< pi
/\ azim x u w y< azim x u w v /\ &0< azim x u w y
==> let a1=(v-x):real^3 in
    let a2=w-x:real^3 in
    let a3=(y-x):real^3 in
    let a4=(u-x) :real^3 in
        let va=a1 cross a2:real^3 in
    let vb=a3 cross a4:real^3 in
    let v3= (vb:real^3) cross (va:real^3)+(x:real^3)
in v3 IN aff_gt {x} {v,w:real^3}
```

证明思路：`notcoplanar_imp_notcollinear_fan` 给 ¬Collinear3 x v w 等；
`aff_gt_1_2` 展开目标，取系数 t1 = 1 - vb⬝a4 + vb⬝a1、
t2 = vb⬝a4、t3 = -(vb⬝a1)（a1 = v-x、a2 = w-x、a3 = y-x、
a4 = u-x、va = a1×a2、vb = a3×a4）。t3 > 0 由
`cross_dot_fully_surrounded_fan`（h2/h1 先给 azim x u w y < π，
`sum4_azim_fan` 转成 0 < azim x u y v < π）；向量恒等式经
CROSS_LAGRANGE（Mathlib `cross_dot_cross`）展开验证。
编码注记：HOL 的 let 绑定按定义内联为嵌套叉积表达式；
仓库无公开 V3 级叉积，沿用 Pi 侧 `crossProduct` + `WithLp.toLp 2`
习惯写法（同本文件 `condition_to_in_aff_gt_by_angle` 与
`cross_dot_fully_surrounded_fan`）。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- Mathlib `cross_dot_cross`（Mathlib/LinearAlgebra/CrossProduct.lean:111，
  CROSS_LAGRANGE）、`cross_cross_eq_smul_sub_smul'`（CROSS_TRIPLE 侧） -/
theorem cut_in_angle_fan {x v u w y : V3}
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) (hnc : ¬ Collinear3 x u y)
    (h0 : 0 < azim x u w v) (h1 : azim x u w v < Real.pi)
    (h2 : azim x u w y < azim x u w v) (h3 : 0 < azim x u w y) :
    ((WithLp.toLp 2 (crossProduct
        (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ))
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((w - x : V3) : Fin 3 → ℝ))) : V3) + x) ∈
      affGt {x} {v, w} := by
  sorry

/-- HOL planarity.hl:10385-10426 `aff_gt_1_2_scale_fan`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 w:real^3 a:real.
&0< a /\ a % (u-x)= w-x /\ ~collinear {x,w,v}
==> aff_gt {x} {u,v} =aff_gt {x} {w,v}
```

证明思路：由 a • (u - x) = w - x 得 u - x = a⁻¹ • (w - x)。
两侧各用 `aff_gt_1_2`（Disjoint 由 ¬Collinear3 x w v 导出，
做法同本文件 `conditions_in_rcone_fan`；HOL 的 `th3` 未移植）
展开为系数组合后双向映射系数：t1' = 1 - a*t2 - t3、
t2' = a*t2、t3' = t3（反向用 a⁻¹），正性由 a > 0 与 a⁻¹ > 0
（HOL COLLINEAR_SPECIAL_SCALE 对应 `collinear3_iff_smul` 型
缩放论证）。HOL 的 GEOM_ORIGIN_TAC（平移原点）不必要：
`aff_gt_1_2` 组合式已带 t1 系数。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `collinear3_iff_smul`（Kepler/Geom/Azim.lean:86，COLLINEAR_SPECIAL_SCALE 角色）
- `conditions_in_rcone_fan`（本文件 batch 1，Disjoint 内联推导模板） -/
theorem aff_gt_1_2_scale_fan {x v u w : V3} {a : ℝ}
    (ha : 0 < a) (hscale : a • (u - x) = w - x)
    (hnc : ¬ Collinear3 x w v) :
    affGt {x} {u, v} = affGt {x} {w, v} := by
  sorry

/-- HOL planarity.hl:10427-10570 `exists_cut_rcone_fan_with_edge_run_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 s:real.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ &0<s /\ s<pi/ &2
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
(?t:real. &0< t /\ t< &1 /\
~(rw_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(sigma_fan x V E u w:real^3)) (cos(s)) INTER aff_gt {x} {v, (&1-t)%u+t%w}={}))
```

证明思路：与 `exists_point_inside_domain_cone_fan` 相同的 fan80 /
fully-surrounded 前奏；`CARD = 1` 分支与 hcard u 矛盾。CARD > 1 时
`inequality3_aim_in_convex_fan` 给弦内点方位角严格介于 0 与
azim x u w v；`exists_point_inside_domain_cone_fan`（本批上文）给
y ∈ rw_dart(cos s) 且 azim x v u y < azim x v u w。再以
`cut_in_angle_fan`（实例 [x;w;v;u;y]，四元组换序 + let_CONV）得
v3 ∈ aff_gt {x,w} {v,u}；`scale_in_edges_fan`（本文件 batch 1）
给 a、t 使 a • (v3 - x) = (1-t) • u + t • w - x，EXISTS_TAC t；
成员资格经 `aff_gt_1_2_scale_fan`（本批上文）、
`continuous_coplanar_fan`、`notcoplanar_imp_notcollinear_fan`、
`azim_compl` / `azim_eq_azim_iff`（AZIM_EQ_ALT）、
`inequality4_aim_in_convex_fan`、`angle_is_smallpi_fan`（batch 1）
与 `conditions_in_rcone_fan`（batch 1）合并（witness 为 y）。

候选已有引理：
- `exists_point_inside_domain_cone_fan` / `cut_in_angle_fan` /
  `aff_gt_1_2_scale_fan`（本批上文）
- `inequality3_aim_in_convex_fan`（Kepler/Text/Planarity.lean:2009）
- `inequality4_aim_in_convex_fan`（Kepler/Text/PlanarityNotCut.lean:2474）
- `scale_in_edges_fan` / `conditions_in_rcone_fan` /
  `angle_is_smallpi_fan`（本文件 batch 1）
- `continuous_coplanar_fan`（Kepler/Text/Planarity.lean:1142）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）、
  `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193） -/
theorem exists_cut_rcone_fan_with_edge_run_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {s : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      (rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos s) ∩
        affGt {x} {v, (1 - t) • u + t • w}) ≠ ∅ := by
  sorry

/-- HOL planarity.hl:10571-10612 `aff_gt_in_rw_dart_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 y:real^3 s:real.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ &0<s /\ s<pi/ &2
/\ y IN rw_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(v:real^3)) (cos(s))
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==> aff_gt {x} {u,y} SUBSET rw_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(sigma_fan x V E u w:real^3)) (cos(s))
```

证明思路：`CARD = 1` 分支与 hcard u 矛盾。CARD > 1 时
`rwDartFan` 展开为 `wedge x u w (sigmaFan …) ∩ rconeFan x u (cos s)`
（wedge 用 sigmaFan 而非四元组第 4 分量）。取 x' ∈ aff_gt {x} {u,y}：
`aff_gt_inter_aff_gt` 分解出 x' ∈ aff_gt {x,u} {y}；
`aff_gt_imp_not_collinear`（batch 1）+ `azim_eq_azim_iff`（AZIM_EQ_ALT）
把 wedge 界 `azim x u w y < azim x u w (sigmaFan …)` 转移到 x'；
rcone 侧由 `conditions_in_rcone_fan`（batch 1，EXISTS_TAC y，
锥轴为 u）转移到 x'。

候选已有引理：
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `aff_gt_imp_not_collinear` / `conditions_in_rcone_fan`（本文件 batch 1）
- `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193，AZIM_EQ_ALT）
- `fan_not_collinear` / `edge_ne_of_fan`（Kepler/Text/Fan.lean:342/1038，
  HOL remark1_fan 的互异性分量） -/
theorem aff_gt_in_rw_dart_fan {x v u w y : V3} {V : Set V3} {E : Set (Set V3)}
    {s : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hy : y ∈ rwDartFan x V E (x, u, w, v) (Real.cos s))
    (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    affGt {x} {u, y} ⊆ rwDartFan x V E (x, u, w, sigmaFan x V E u w)
      (Real.cos s) := by
  sorry

/-- HOL planarity.hl:10613-10623 `in_aff_gt_1_2`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 t:real.
DISJOINT {x} {v,u} /\ &0< t /\ t< &1==>  (&1-t)% v+ t% u IN aff_gt {x} {v,u}
```

证明思路：`aff_gt_1_2` 展开后取系数 (0, 1-t, t)：三系数和为 1、
1 - t > 0 与 t > 0 由 ht/ht1，向量恒等式 `module` 即得
（HOL 用 VECTOR_ARITH）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165） -/
theorem in_aff_gt_1_2 {x v u : V3} {t : ℝ}
    (hdis : Disjoint ({x} : Set V3) {v, u}) (ht : 0 < t) (ht1 : t < 1) :
    (1 - t) • v + t • u ∈ affGt {x} {v, u} := by
  sorry

/-- HOL planarity.hl:10624-10806 `exists_rw_dart_inter_aff_gt1_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 s:real.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ &0<s /\ s<pi/ &2
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
(?h:real. &0< h /\
(!t:real. &0< t /\ t< h==>
~(rw_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(sigma_fan x V E u w:real^3)) (cos(s)) INTER aff_gt {x} {v, (&1-t)%u+t%w}={})
))
```

证明思路：`CARD = 1` 分支与 hcard u 矛盾。CARD > 1 时
`exists_cut_rcone_fan_with_edge_run_fan`（本批上文）给 t0 ∈ (0,1)
使交集非空，取 h := t0。对每个 t' < t0 记 vt = (1-t')•u + t'•w：
`in_aff_gt_1_2`（本批上文）+ `aff_gt_inter_aff_gt` +
`continuous_coplanar_fan` 维持非退化；两次 `cut_in_angle_fan`
（[x;v;u;vt;y] 给 v3 ∈ aff_gt {x} {v,vt} 侧、[x;y;v;u;vt] 经
叉积反对称归一给 v3 ∈ aff_gt {x} {u,y} 侧），
`aff_gt_in_rw_dart_fan`（本批上文）把 aff_gt {x} {u,y} 整体纳入
rw_dart；楔形严格性经 `azim_eq_azim_iff`（AZIM_EQ_ALT）、
`azim_compl`、`inequality4_aim_in_convex_fan`（比例 t⁻¹*t'）、
`angle_is_smallpi_fan`（batch 1）与 `azim_eq_zero_iff` 合成。

候选已有引理：
- `exists_cut_rcone_fan_with_edge_run_fan` / `cut_in_angle_fan` /
  `in_aff_gt_1_2` / `aff_gt_in_rw_dart_fan`（本批上文）
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `continuous_coplanar_fan`（Kepler/Text/Planarity.lean:1142）
- `inequality4_aim_in_convex_fan`（Kepler/Text/PlanarityNotCut.lean:2474）
- `angle_is_smallpi_fan`（本文件 batch 1）
- `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193）、
  `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）、
  `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296） -/
theorem exists_rw_dart_inter_aff_gt1_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)} {s : ℝ}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v) (hs : 0 < s) (hsπ : s < Real.pi / 2)
    (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    ∃ h : ℝ, 0 < h ∧
      ∀ t : ℝ, 0 < t → t < h →
        (rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos s) ∩
          affGt {x} {v, (1 - t) • u + t • w}) ≠ ∅ := by
  sorry

end Kepler.Text

