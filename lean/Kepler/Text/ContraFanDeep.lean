/-
  Kepler/Text/ContraFanDeep — CKQOWSA 章深几何核 `LEMMA_4_POINTS_FINAL`（CF-4）的
  独立移植模块（GIANT，切三波：CF-4a kit / CF-4b 主装配 / CF-4c 接线）。

  HOL 参照（reference/flyspeck/text_formalization/tame/）：
  - `tame/CKQOWSA_4.hl`（module Ckqowsa_4_points）：目标陈述 `LEMMA_4_POINTS_FINAL`
    （:4093-4096）；分离平面 `separation_plane_4_points`（:2870-3003）；旋转族
    `rotation_lemma_special`（:1012）、`rotation_about_axis`（:1676）；穿越不变量
    `continuous_lemma_aff_ge`（:2204）、`continuous_intersection_point`（:1785）、
    `aff_ge_inter_segments`（:1238）、`in_aff_ge_cases_lemma`（:1928）、
    `segment_intersects_aff_ge_lemma`（:2138）；终局 `lemma_4_points_circumcenter`
    （:3866）。
  - `tame/CKQOWSA_3.hl`：`LEMMA_3_POINTS_FINAL`（:1350）——分离步 4 次调用的 twin，
    本模块自带路线 B 私有副本（ContraFanDeep 不得 import ContraFan：接线方向是
    ContraFan → ContraFanDeep）。

  模块策略（scout 报告 docs/contrafan-scout.md §4.0/§4.2）：只 import
  {Kepler.Geom.Aff, Kepler.Text.PackingAuto2}（ballAnnulus/h0 均在此，无环：
  二者均不 import 本模块）；全部公开件 `cf4_*` 前缀或 private；ContraFan.lean
  的接线（2 行转发）属 CF-4c，本模块不回头依赖它。

  移植状态（CF-4a，2026-09-28 工位）：
  - 真证明：twin 前奏（§0-1）、`cf4_cone_inter_imp_segment_conv`（件 1）、
    `cf4_separation_plane_4_points`（件 2）、旋转族机器（件 3）、
    穿越不变量易侧（件 4 的 `cf4_aff_ge_inter_segments` 等）、外心预备（件 5）；
  - NEEDS 脚手架（带账）：`cf4_continuous_intersection_point`、
    `cf4_continuous_lemma_aff_ge`（穿越不变量在连续旋转族下的传递，
    HOL continuous_lemma_aff_ge :2204-2869 共 665 行——CF-4b 主件）。
-/
import Kepler.Geom.Aff
import Kepler.Text.PackingAuto2

set_option maxHeartbeats 800000

open Kepler.Geom
open Kepler.Text
open Set Metric Classical

namespace Kepler.Text.ContraFanDeep

/-! ## 0. 基础孪生（ContraFan.lean 同体私有副本——本模块不得 import ContraFan）-/

/-- HOL `in_ball_annulus`（CKQOWSA_3.hl:33-34）。 -/
private theorem inBallAnnulus {v : V3} (hv : v ∈ ballAnnulus) :
    2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  simp only [ballAnnulus, Set.mem_diff, Set.mem_singleton_iff, mem_closedBall, mem_ball,
    dist_zero_right, not_lt] at hv
  exact ⟨hv.2, hv.1⟩

/-- HOL `h0`（pack_defs.hl:147）的数值。 -/
private theorem two_h0 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]

/-- `y ∈ affGe {0} {v}` 的显式刻画（HOL `HALFLINE`/`AFF_GE_1_1` 在 `x = 0`
的组合形式；无条件版：v = 0 时两侧同为 `y = 0`）。 -/
private theorem affGe_0_1_char (v y : V3) :
    y ∈ affGe {0} ({v} : Set V3) ↔ ∃ t : ℝ, 0 ≤ t ∧ y = t • v := by
  simp only [affGe, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    by_cases h0v : (0:V3) = v
    · subst h0v
      have hS : hfin.toFinset = ({0} : Finset V3) := by
        ext z
        simp [Set.Finite.mem_toFinset] <;> tauto
      rw [hS, Finset.sum_singleton] at hsum
      exact ⟨0, le_refl 0, by rw [hsum]; simp⟩
    · have hS : hfin.toFinset = ({0, v} : Finset V3) := by
        ext z
        simp [Set.Finite.mem_toFinset] <;> tauto
      rw [hS, Finset.sum_insert (by simpa using h0v), Finset.sum_singleton] at hsum
      refine ⟨f v, hpos v (by simp), ?_⟩
      rw [hsum]
      simp
  · rintro ⟨t, ht, rfl⟩
    by_cases h0v : (0:V3) = v
    · subst h0v
      have hfin0 : (({0} : Set V3) ∪ {0} : Set V3).Finite := Set.toFinite _
      have hS : hfin0.toFinset = ({0} : Finset V3) := by
        ext z
        simp [Set.Finite.mem_toFinset] <;> tauto
      refine ⟨fun _ => 1, hfin0, ?_, ?_, ?_⟩
      · rw [hS]
        simp
      · intro z _
        simp
      · rw [hS]
        simp
    · have hfin0 : (({0} : Set V3) ∪ {v} : Set V3).Finite := Set.toFinite _
      have hS : hfin0.toFinset = ({0, v} : Finset V3) := by
        ext z
        simp [Set.Finite.mem_toFinset] <;> tauto
      refine ⟨fun z => if z = v then t else 1 - t, hfin0, ?_, ?_, ?_⟩
      · rw [hS, Finset.sum_insert (by simpa using h0v), Finset.sum_singleton]
        simp [h0v]
      · intro z hz
        have hzv : z = v := by simpa using hz
        simp [hzv, ht]
      · rw [hS, Finset.sum_insert (by simpa using h0v), Finset.sum_singleton]
        simp [h0v]

private theorem fin_sum_two {M : Type*} [AddCommMonoid M] {g : V3 → M} {a b : V3}
    (hne : a ≠ b) :
    ∑ z ∈ ({a, b} : Finset V3), g z = g a + g b := by
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]

private theorem fin_sum_three {M : Type*} [AddCommMonoid M] {g : V3 → M} {a b c : V3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ z ∈ ({a, b, c} : Finset V3), g z = g a + g b + g c := by
  rw [Finset.sum_insert (by simp [hab, hac] : (a : V3) ∉ ({b, c} : Finset V3)),
    fin_sum_two hbc, add_assoc]

/-- `y ∈ affGe {0} {v1, v2}` 的显式二系数刻画（HOL `aff_ge_0_2`
CKQOWSA_3.hl:115-142 的组合形式；非退化假设与 HOL 一致）。 -/
private theorem affGe_0_2_char {v1 v2 : V3} (h01 : v1 ≠ 0) (h02 : v2 ≠ 0) (h12 : v1 ≠ v2)
    (y : V3) :
    y ∈ affGe {0} ({v1, v2} : Set V3) ↔
      ∃ t1 t2 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ y = t1 • v1 + t2 • v2 := by
  simp only [affGe, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    have hS : hfin.toFinset = ({0, v1, v2} : Finset V3) := by
      ext z
      simp [Set.Finite.mem_toFinset] <;> tauto
    rw [hS, fin_sum_three (g := fun z => f z • z) (fun h => h01 h.symm)
      (fun h => h02 h.symm) h12] at hsum
    simp only [smul_zero, zero_add] at hsum
    exact ⟨f v1, f v2, hpos v1 (by simp), hpos v2 (by simp), by rw [hsum]⟩
  · rintro ⟨t1, t2, ht1, ht2, rfl⟩
    have hv01 : (0:V3) ≠ v1 := fun h => h01 h.symm
    have hv02 : (0:V3) ≠ v2 := fun h => h02 h.symm
    have hfin0 : (({0} : Set V3) ∪ {v1, v2} : Set V3).Finite := Set.toFinite _
    have hS : hfin0.toFinset = ({0, v1, v2} : Finset V3) := by
      ext z
      simp [Set.Finite.mem_toFinset] <;> tauto
    refine ⟨fun z => if z = v2 then t2 else if z = v1 then t1 else 1 - t1 - t2,
      hfin0, ?_, ?_, ?_⟩
    · rw [hS, fin_sum_three (g := fun z => (if z = v2 then t2 else if z = v1 then t1
          else 1 - t1 - t2) • z) (fun h => h01 h.symm) (fun h => h02 h.symm) h12]
      simp [hv01, hv02, h12]
    · intro z hz
      by_cases hz2 : z = v2
      · simp [hz2, ht2]
      · by_cases hz1 : z = v1
        · rw [hz1]
          simp [h12, ht1]
        · exact absurd hz (by simp [hz1, hz2])
    · rw [hS, fin_sum_three (g := fun z => if z = v2 then t2 else if z = v1 then t1
          else 1 - t1 - t2) (fun h => h01 h.symm) (fun h => h02 h.symm) h12]
      simp [hv01, hv02, h12] <;> ring

/-- fan7_2 与 estd_non_collinear 共用的算术核：annulus 中两点若沿同一射线
（`v = c • w`，c ≥ 0）则违反距离约束。对应 CKQOWSA.hl:131-169 的
`REAL_LE_ADD2` 论证。 -/
private theorem annulus_ray_absurd {v w : V3} (hv2 : 2 ≤ ‖v‖) (hw2 : 2 ≤ ‖w‖)
    (hvw2 : 2 ≤ dist v w) (hvup : ‖v‖ ≤ 2 * h0) (hwup : ‖w‖ ≤ 2 * h0)
    {c : ℝ} (hc : 0 ≤ c) (hvc : v = c • w) : False := by
  have hn_v : ‖v‖ = c * ‖w‖ := by
    rw [hvc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hd_vw : dist v w = |c - 1| * ‖w‖ := by
    rw [hvc, dist_eq_norm]
    have hse : c • w - w = (c - 1) • w := by module
    rw [hse, norm_smul, Real.norm_eq_abs]
  rcases le_or_gt c 1 with h1 | h1
  · have hab : |c - 1| = 1 - c := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c)]
    have hsum : ‖v‖ + dist v w = ‖w‖ := by rw [hn_v, hd_vw, hab]; ring
    have h4 : (4:ℝ) ≤ ‖v‖ + dist v w := by linarith
    have h252 : (2:ℝ) * h0 = 2.52 := two_h0
    linarith
  · have hab : |c - 1| = c - 1 := abs_of_nonneg (by linarith)
    have hsum : ‖w‖ + dist v w = ‖v‖ := by rw [hn_v, hd_vw, hab]; ring
    have h4 : (4:ℝ) ≤ ‖w‖ + dist v w := by linarith
    have h252 : (2:ℝ) * h0 = 2.52 := two_h0
    linarith

/-! ## 1. LEMMA_3_POINTS_FINAL 路线 B 孪生（分离步的 4 次调用件）

`ContraFan.lean`（CF-3, commit e9ee264a）同名定理的私有副本：ContraFanDeep
不得 import ContraFan（接线方向 ContraFan → ContraFanDeep，见模块头），故复制。
HOL 锚点：`LEMMA_3_POINTS_FINAL`（CKQOWSA_3.hl:1350-1356）；路线 B 数值件
（quad_corner / cos_ge_1031 / cos_le_2719 / two_arccos_gt）见 ContraFan.lean §3.0。 -/

/-- 角点二次型引理：a, b ∈ [2, 2h0]（= [2, 63/25]）⟹
a² + b² − (5438/3969)·a·b ≤ 4。 -/
private theorem quad_corner (a b : ℝ) (ha1 : (2:ℝ) ≤ a) (ha2 : a ≤ 2 * h0)
    (hb1 : (2:ℝ) ≤ b) (hb2 : b ≤ 2 * h0) :
    a * a + b * b - (5438:ℝ) / 3969 * a * b ≤ 4 := by
  rw [two_h0] at ha2 hb2
  have hkey : a * a + b * b - (5438:ℝ) / 3969 * a * b - 4
      = (63/25 - a) * (63/25 - a) + (63/25 - b) * (63/25 - b)
        - (5438:ℝ) / 3969 * (63/25 - a) * (63/25 - b)
        - (100:ℝ) / 63 * ((63/25 - a) + (63/25 - b)) := by
    field_simp
    ring
  have hx1 : (0:ℝ) ≤ 63/25 - a := by linarith
  have hx2 : 63/25 - a ≤ 13/25 := by linarith
  have hy1 : (0:ℝ) ≤ 63/25 - b := by linarith
  have hy2 : 63/25 - b ≤ 13/25 := by linarith
  have hp1 : (63/25 - a) * (63/25 - a) ≤ (13/25) * (63/25 - a) := by nlinarith
  have hp2 : (63/25 - b) * (63/25 - b) ≤ (13/25) * (63/25 - b) := by nlinarith
  have hp3 : (0:ℝ) ≤ (63/25 - a) * (63/25 - b) := by nlinarith
  have hp4 : (0:ℝ) ≤ (5438:ℝ) / 3969 * ((63/25 - a) * (63/25 - b)) :=
    mul_nonneg (by norm_num) hp3
  linarith [hkey, hp1, hp2, hp3, hp4]

/-- 短边角的下界：annulus 中 dist v w ≤ 2h0 ⟹ cos ∠(v,w) ≥ 1031/7938。 -/
private theorem cos_ge_1031 {v w : V3} (hv2 : (2:ℝ) ≤ ‖v‖) (hvup : ‖v‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwup : ‖w‖ ≤ 2 * h0) (hd : dist v w ≤ 2 * h0) :
    (1031:ℝ) / 7938 ≤ Real.cos (InnerProductGeometry.angle v w) := by
  rw [two_h0] at hvup hwup hd
  have hvpos : (0:ℝ) < ‖v‖ := by linarith
  have hwpos : (0:ℝ) < ‖w‖ := by linarith
  have hv4 : (4:ℝ) ≤ ‖v‖ ^ 2 := by nlinarith
  have hw4 : (4:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
  have hsq : (2.52:ℝ) ^ 2 = 6.3504 := by norm_num
  have e1 : (0:ℝ) ≤ (2.52 - ‖w‖) * ‖v‖ :=
    mul_nonneg (sub_nonneg.2 hwup) hvpos.le
  have e2 : (0:ℝ) ≤ (2.52 - ‖v‖) * 2.52 :=
    mul_nonneg (sub_nonneg.2 hvup) (by norm_num)
  have hab : ‖v‖ * ‖w‖ ≤ 2.52 * 2.52 := by linarith
  have hd2 : dist v w ^ 2 ≤ 6.3504 := le_trans (pow_le_pow_left₀ dist_nonneg hd 2)
    (le_of_eq hsq)
  have hkey : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 - 2 * inner ℝ v w := by
    have h1 : ‖v - w‖ ^ 2 = inner ℝ (v - w) (v - w) := (real_inner_self_eq_norm_sq _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v w,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hdist : dist v w = ‖v - w‖ := dist_eq_norm v w
  have h2A : (8:ℝ) - 6.3504 ≤ 2 * inner ℝ v w := by
    have h1 : ‖v - w‖ ^ 2 = dist v w ^ 2 := by rw [hdist]
    linarith
  rw [InnerProductGeometry.cos_angle, le_div_iff₀ (mul_pos hvpos hwpos)]
  linarith

/-- 长距离角的上界：annulus 中 2 ≤ dist v w ⟹ cos ∠(v,w) ≤ 2719/3969。 -/
private theorem cos_le_2719 {v w : V3} (hv2 : (2:ℝ) ≤ ‖v‖) (hvup : ‖v‖ ≤ 2 * h0)
    (hw2 : (2:ℝ) ≤ ‖w‖) (hwup : ‖w‖ ≤ 2 * h0) (hd : (2:ℝ) ≤ dist v w) :
    Real.cos (InnerProductGeometry.angle v w) ≤ (2719:ℝ) / 3969 := by
  have hvpos : (0:ℝ) < ‖v‖ := by linarith
  have hwpos : (0:ℝ) < ‖w‖ := by linarith
  have hkey : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 - 2 * inner ℝ v w := by
    have h1 : ‖v - w‖ ^ 2 = inner ℝ (v - w) (v - w) := (real_inner_self_eq_norm_sq _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v w,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hdist : dist v w = ‖v - w‖ := dist_eq_norm v w
  have hd4 : (4:ℝ) ≤ dist v w ^ 2 := by nlinarith
  have hqc := quad_corner ‖v‖ ‖w‖ hv2 hvup hw2 hwup
  have h2A : 2 * inner ℝ v w ≤ (5438:ℝ) / 3969 * (‖v‖ * ‖w‖) := by
    have h1 : ‖v - w‖ ^ 2 = dist v w ^ 2 := by rw [hdist]
    linarith
  rw [InnerProductGeometry.cos_angle, div_le_iff₀ (mul_pos hvpos hwpos)]
  linarith

/-- 纯有理数角隙：2·arccos(2719/3969) > arccos(1031/7938)。 -/
private theorem two_arccos_gt :
    Real.arccos ((1031:ℝ) / 7938) < 2 * Real.arccos ((2719:ℝ) / 3969) := by
  have hc1 : (2719:ℝ) / 3969 ≤ 1 := by norm_num
  have hc1m : -1 ≤ (2719:ℝ) / 3969 := by norm_num
  have hpos : (0:ℝ) ≤ 2719 / 3969 := by norm_num
  have hle : 2 * Real.arccos ((2719:ℝ) / 3969) ≤ Real.pi := by
    have h := Real.arccos_le_pi_div_two.2 hpos
    linarith
  have hge : (0:ℝ) ≤ 2 * Real.arccos ((2719:ℝ) / 3969) := by
    have h := Real.arccos_nonneg ((2719:ℝ) / 3969)
    linarith
  have hcos : Real.cos (2 * Real.arccos ((2719:ℝ) / 3969))
      = 2 * ((2719:ℝ) / 3969) ^ 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos hc1m hc1]
  have hval : 2 * ((2719:ℝ) / 3969) ^ 2 - 1 < (1031:ℝ) / 7938 := by norm_num
  have hkey := Real.arccos_lt_arccos (x := 2 * ((2719:ℝ) / 3969) ^ 2 - 1)
    (y := (1031:ℝ) / 7938)
    (by linarith [sq_nonneg ((2719:ℝ) / 3969)]) hval (by norm_num)
  rwa [← hcos, Real.arccos_cos hge hle] at hkey

/-- HOL `LEMMA_3_POINTS_FINAL`（CKQOWSA_3.hl:1350-1356）的私有孪生（路线 B，
与 ContraFan.lean 同体证明）。 -/
private theorem cf4_LEMMA_3_POINTS_FINAL {v1 v2 v3 : V3}
    (hcone : v3 ∈ affGe {0} ({v1, v2} : Set V3))
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hd : dist v1 v2 ≤ 2 * h0) (hd13 : 2 ≤ dist v1 v3) (hd23 : 2 ≤ dist v2 v3) :
    False := by
  obtain ⟨ha1, hau1⟩ := inBallAnnulus hb1
  obtain ⟨ha2, hau2⟩ := inBallAnnulus hb2
  obtain ⟨ha3, hau3⟩ := inBallAnnulus hb3
  have hv1n : v1 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha1; norm_num at ha1
  have hv2n : v2 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha2; norm_num at ha2
  have hv3n : v3 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha3; norm_num at ha3
  rcases eq_or_ne v1 v2 with hv12 | hv12
  · -- v1 = v2：v3 落在射线 v1 上，1D 算术反证
    subst hv12
    rw [Set.pair_eq_singleton] at hcone
    obtain ⟨t, ht0, hv3t⟩ := (affGe_0_1_char v1 v3).1 hcone
    have htp : (0:ℝ) < t := by
      rcases lt_or_eq_of_le ht0 with h | h
      · exact h
      · rw [← h, zero_smul] at hv3t
        exact absurd hv3t hv3n
    exact annulus_ray_absurd ha1 ha3 hd13 hau1 hau3 (le_of_lt (inv_pos.2 htp))
      (by rw [hv3t, inv_smul_smul₀ htp.ne'])
  · -- v1 ≠ v2：锥内二系数显式化
    obtain ⟨t1, t2, ht1, ht2, hv3t⟩ := (affGe_0_2_char hv1n hv2n hv12 v3).1 hcone
    rcases lt_or_eq_of_le ht1 with ht1p | ht10
    · rcases lt_or_eq_of_le ht2 with ht2p | ht20
      · -- 主分支：t1, t2 > 0，锥内角加法 + 纯有理数余弦界
        have hmem : v3 ∈ Submodule.span NNReal ({v1, v2} : Set V3) := by
          rw [Submodule.mem_span_pair]
          refine ⟨⟨t1, ht1p.le⟩, ⟨t2, ht2p.le⟩, ?_⟩
          show t1 • v1 + t2 • v2 = v3
          exact hv3t.symm
        have hsplit : InnerProductGeometry.angle v1 v2
            = InnerProductGeometry.angle v1 v3 + InnerProductGeometry.angle v3 v2 :=
          InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hv3n hmem
        have hBge : Real.arccos ((2719:ℝ) / 3969)
            ≤ InnerProductGeometry.angle v1 v3 := by
          have h1 : Real.arccos ((2719:ℝ) / 3969)
              ≤ Real.arccos (Real.cos (InnerProductGeometry.angle v1 v3)) :=
            Real.antitone_arccos (cos_le_2719 ha1 hau1 ha3 hau3 hd13)
          rwa [Real.arccos_cos (InnerProductGeometry.angle_nonneg v1 v3)
            (InnerProductGeometry.angle_le_pi v1 v3)] at h1
        have hCge : Real.arccos ((2719:ℝ) / 3969)
            ≤ InnerProductGeometry.angle v3 v2 := by
          have h1 : Real.arccos ((2719:ℝ) / 3969)
              ≤ Real.arccos (Real.cos (InnerProductGeometry.angle v2 v3)) :=
            Real.antitone_arccos (cos_le_2719 ha2 hau2 ha3 hau3 hd23)
          rw [Real.arccos_cos (InnerProductGeometry.angle_nonneg v2 v3)
            (InnerProductGeometry.angle_le_pi v2 v3), InnerProductGeometry.angle_comm
            v2 v3] at h1
          exact h1
        have hAge : InnerProductGeometry.angle v1 v2
            ≤ Real.arccos ((1031:ℝ) / 7938) := by
          have h1 : Real.arccos (Real.cos (InnerProductGeometry.angle v1 v2))
              ≤ Real.arccos ((1031:ℝ) / 7938) :=
            Real.antitone_arccos (cos_ge_1031 ha1 hau1 ha2 hau2 hd)
          rwa [Real.arccos_cos (InnerProductGeometry.angle_nonneg v1 v2)
            (InnerProductGeometry.angle_le_pi v1 v2)] at h1
        have hsum : 2 * Real.arccos ((2719:ℝ) / 3969)
            ≤ InnerProductGeometry.angle v1 v3 + InnerProductGeometry.angle v3 v2 := by
          linarith
        linarith [hsum, hsplit, hAge, two_arccos_gt]
      · -- t2 = 0：v3 在射线 v1 上
        have ht20' : t2 = 0 := ht20.symm
        simp only [ht20', zero_smul, add_zero] at hv3t
        exact annulus_ray_absurd ha1 ha3 hd13 hau1 hau3 (le_of_lt (inv_pos.2 ht1p))
          (by rw [hv3t, inv_smul_smul₀ ht1p.ne'])
    · -- t1 = 0：v3 在射线 v2 上
      have ht10' : t1 = 0 := ht10.symm
      simp only [ht10', zero_smul, zero_add] at hv3t
      have ht2p : (0:ℝ) < t2 := by
        rcases lt_or_eq_of_le ht2 with h | h
        · exact h
        · rw [← h, zero_smul] at hv3t
          exact absurd hv3t hv3n
      exact annulus_ray_absurd ha2 ha3 hd23 hau2 hau3 (le_of_lt (inv_pos.2 ht2p))
        (by rw [hv3t, inv_smul_smul₀ ht2p.ne'])

/-- HOL `dot_pos_lemma`（CKQOWSA_3.hl:1071-1105）：annulus 中距离 ≤ 2h0 的
两点内积为正。 -/
private theorem dot_pos_lemma {v w : V3} (hv : v ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
    (hd : dist v w ≤ 2 * h0) : 0 < inner ℝ v w := by
  obtain ⟨hv2, -⟩ := inBallAnnulus hv
  obtain ⟨hw2, -⟩ := inBallAnnulus hw
  by_contra hcon
  push_neg at hcon
  have hsqv : (4:ℝ) ≤ ‖v‖ ^ 2 := by nlinarith [hv2]
  have hsqw : (4:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith [hw2]
  have hkey : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 - 2 * inner ℝ v w := by
    have h1 : ‖v - w‖ ^ 2 = inner ℝ (v - w) (v - w) := (real_inner_self_eq_norm_sq _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v w,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hdist : dist v w = ‖v - w‖ := dist_eq_norm v w
  have h1 : (8:ℝ) ≤ ‖v - w‖ ^ 2 := by rw [hkey]; linarith
  have h2 : dist v w ^ 2 ≤ (2 * h0) ^ 2 := pow_le_pow_left₀ dist_nonneg hd 2
  rw [two_h0] at h2
  rw [← hdist] at h1
  linarith

/-- HOL `estd_non_collinear_lemma`（CKQOWSA_4.hl:45-53）：annulus 中距离
约束 [2, 2h0] 的两点与原点不共线。 -/
private theorem estd_non_collinear_lemma {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (hd1 : 2 ≤ dist v w) (hd2 : dist v w ≤ 2 * h0) :
    ¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3)) := by
  obtain ⟨hv2, hvup⟩ := inBallAnnulus hv
  obtain ⟨hw2, hwup⟩ := inBallAnnulus hw
  intro hcol
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨p₀, u, hall⟩ := hcol
  obtain ⟨r0, hr0⟩ := hall (0:V3) (by simp)
  obtain ⟨r1, hr1⟩ := hall v (by simp)
  obtain ⟨r2, hr2⟩ := hall w (by simp)
  simp only [vadd_eq_add] at hr0 hr1 hr2
  have hr0' : r0 • u + p₀ = 0 := by rw [hr0]
  have hvne0 : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv2
    norm_num at hv2
  have hva : v = (r1 - r0) • u := by
    have h4 : p₀ = -(r0 • u) := eq_neg_of_add_eq_zero_right hr0'
    rw [hr1, h4]
    module
  have ha0 : r1 - r0 ≠ 0 := by
    intro he
    rw [he, zero_smul] at hva
    exact hvne0 hva
  have huv : u = (r1 - r0)⁻¹ • v := by rw [hva, inv_smul_smul₀ ha0]
  have hwt : w = ((r2 - r0) * (r1 - r0)⁻¹) • v := by
    have h4 : p₀ = -(r0 • u) := eq_neg_of_add_eq_zero_right hr0'
    rw [hr2, h4, hva, smul_smul]
    have hk : (r2 - r0) * (r1 - r0)⁻¹ * (r1 - r0) = r2 - r0 := by
      field_simp
    rw [hk, sub_smul]
    abel
  have hn_w : ‖w‖ = |(r2 - r0) * (r1 - r0)⁻¹| * ‖v‖ := by
    rw [hwt, norm_smul, Real.norm_eq_abs]
  have hd : dist v w = |1 - (r2 - r0) * (r1 - r0)⁻¹| * ‖v‖ := by
    rw [hwt, dist_eq_norm]
    have hse : v - ((r2 - r0) * (r1 - r0)⁻¹) • v =
        (1 - (r2 - r0) * (r1 - r0)⁻¹) • v := by module
    rw [hse, norm_smul, Real.norm_eq_abs]
  rcases lt_trichotomy ((r2 - r0) * (r1 - r0)⁻¹ : ℝ) 0 with ht | ht | ht
  · have h1 : |(r2 - r0) * (r1 - r0)⁻¹| = -((r2 - r0) * (r1 - r0)⁻¹) := abs_of_neg ht
    have h2 : |1 - (r2 - r0) * (r1 - r0)⁻¹| = 1 - (r2 - r0) * (r1 - r0)⁻¹ :=
      abs_of_pos (by linarith)
    have hdn : dist v w = ‖v‖ + ‖w‖ := by rw [hd, hn_w, h1, h2]; ring
    have h4 : (4:ℝ) ≤ ‖v‖ + ‖w‖ := by linarith
    have h252 : (2:ℝ) * h0 = 2.52 := two_h0
    linarith
  · -- t = 0：w = 0，与 annulus 下界矛盾
    rw [ht, zero_smul] at hwt
    rw [hwt, norm_zero] at hw2
    norm_num at hw2
  · -- 0 < t：分 0 < t ≤ 1 与 1 < t 两段
    rcases le_or_gt ((r2 - r0) * (r1 - r0)⁻¹) 1 with hle | hgt
    · have h1 : |(r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (le_of_lt ht)
      have h2 : |1 - (r2 - r0) * (r1 - r0)⁻¹| = 1 - (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (by linarith)
      have hwn : ‖w‖ = (r2 - r0) * (r1 - r0)⁻¹ * ‖v‖ := by rw [hn_w, h1]
      have hdn : dist v w = ‖v‖ - ‖w‖ := by rw [hd, h2, hwn]; ring
      have h252 : (2:ℝ) * h0 = 2.52 := two_h0
      linarith
    · have h1 : |(r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (r2 - r0) * (r1 - r0)⁻¹)
      have h2 : |1 - (r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ - 1 := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ (r2 - r0) * (r1 - r0)⁻¹ - 1)]
      have hwn : ‖w‖ = (r2 - r0) * (r1 - r0)⁻¹ * ‖v‖ := by rw [hn_w, h1]
      have hdn : dist v w = ‖w‖ - ‖v‖ := by rw [hd, h2, hwn]; ring
      have h252 : (2:ℝ) * h0 = 2.52 := two_h0
      linarith

/-! ## 2. 件 1：双锥交非零 ⟹ segment ∩ conv{0,v2,v4} 非空（穿越不变量的起点）

HOL 锚点：`LEMMA_4_POINTS_FINAL`（CKQOWSA_4.hl:4093）证明体的第一个 SUBGOAL
（:4135-4185，`CONVEX_HULL_3_ALT` 部分 + `inv (t1+t2) % v` 显式见证 + WLOG
系数和对换 :4186-4210）。系数归一经 `affGe_0_2_char`（= HOL `aff_ge_0_2`）。 -/

/-- `CONVEX_HULL_3_ALT` 的易侧（显式凸组合属于凸包）：非负系数组
(a, b) 满足 a + b ≤ 1 时 `a•v2 + b•v4 ∈ convex hull {0, v2, v4}`。
两次 segment 嵌套：`z ∈ [0, (a/s)•v2 + (b/s)•v4]` 且中间点 ∈ `[v2,v4]` ⊆ hull
（`segment_subset_convexHull` + `convexHull_mono`；HOL 的方向是集合等式
`CONVEX_HULL_3_ALT`，CF-4a 只消费组合 ⟹ 成员一侧）。 -/
private theorem cf4_smul_mem_convexHull3 {v2 v4 z : V3} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b ≤ 1) (hz : a • v2 + b • v4 = z) :
    z ∈ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3)) := by
  have h0 : (0:V3) ∈ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    subset_convexHull _ _ (Set.mem_insert _ _)
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hab0 | habp
  · -- a = b = 0：z = 0
    have hab : a = 0 ∧ b = 0 := by
      have hab0' : a + b = 0 := hab0.symm
      rw [add_eq_zero_iff_of_nonneg ha hb] at hab0'
      exact hab0'
    rw [← hz, hab.1, hab.2, zero_smul, zero_smul, zero_add]
    exact h0
  · -- 一般情形：z ∈ [0, y]，y ∈ [v2,v4] ⊆ hull，hull 凸
    set s := a + b with hsd
    have hsp : s ≠ 0 := ne_of_gt habp
    have key : ∀ (x : V3) (c : ℝ), s • ((s⁻¹ * c) • x) = c • x := by
      intro x c
      rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hsp, one_mul]
    have hy : (s⁻¹ * a) • v2 + (s⁻¹ * b) • v4 ∈ segment ℝ v2 v4 := by
      refine ⟨s⁻¹ * a, s⁻¹ * b, mul_nonneg (inv_nonneg.2 habp.le) ha,
        mul_nonneg (inv_nonneg.2 habp.le) hb, ?_, rfl⟩
      rw [← mul_add, inv_mul_cancel₀ hsp]
    have hyH : (s⁻¹ * a) • v2 + (s⁻¹ * b) • v4
        ∈ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
      segment_subset_convexHull (s := insert (0:V3) ({v2, v4} : Set V3))
        (by simp) (by simp) hy
    have hzseg : z ∈ segment ℝ (0:V3) ((s⁻¹ * a) • v2 + (s⁻¹ * b) • v4) := by
      refine ⟨1 - s, s, by linarith, habp.le, by ring, ?_⟩
      rw [smul_zero, zero_add, smul_add, key, key]
      exact hz
    exact Convex.segment_subset (convex_convexHull ℝ
      (insert (0:V3) ({v2, v4} : Set V3))) h0 hyH hzseg

/-- HOL `LEMMA_4_POINTS_FINAL` 第一个 SUBGOAL 的系数形（CKQOWSA_4.hl:4135-4185）：
p ≠ 0 的两锥表示 p = t1•v1 + t2•v3 = t1'•v2 + t2'•v4（系数全 ≥ 0）且
t1' + t2' ≤ t1 + t2 ⟹ segment[v1,v3] ∩ convex hull {0,v2,v4} ≠ ∅，
显式见证 `inv (t1+t2) • p`。 -/
private theorem cf4_segment_conv_aux {v1 v2 v3 v4 p : V3} (hp : p ≠ 0)
    {t1 t2 t1' t2' : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h1' : 0 ≤ t1') (h2' : 0 ≤ t2')
    (he1 : t1 • v1 + t2 • v3 = p) (he2 : t1' • v2 + t2' • v4 = p)
    (hle : t1' + t2' ≤ t1 + t2) :
    (segment ℝ v1 v3 ∩ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))).Nonempty := by
  have hs : 0 < t1 + t2 := by
    rcases lt_or_eq_of_le (add_nonneg h1 h2) with h | h
    · exact h
    · exfalso
      have hz : t1 + t2 = 0 := h.symm
      rw [add_eq_zero_iff_of_nonneg h1 h2] at hz
      rw [hz.1, hz.2, zero_smul, zero_smul, zero_add] at he1
      exact hp he1.symm
  have hsn : (0:ℝ) ≤ (t1 + t2)⁻¹ := inv_nonneg.2 hs.le
  have hsp : (t1 + t2)⁻¹ * (t1 + t2) = 1 := inv_mul_cancel₀ hs.ne'
  refine ⟨(t1 + t2)⁻¹ • p, ⟨(t1 + t2)⁻¹ * t1, (t1 + t2)⁻¹ * t2,
    mul_nonneg hsn h1, mul_nonneg hsn h2, by rw [← mul_add]; exact hsp, ?_⟩, ?_⟩
  · rw [← smul_smul, ← smul_smul, ← smul_add, he1]
  · refine cf4_smul_mem_convexHull3 (mul_nonneg hsn h1') (mul_nonneg hsn h2') ?_ ?_
    · have h1s : (t1 + t2)⁻¹ * (t1' + t2') ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hle hsn) (le_of_eq hsp)
      rw [← mul_add]
      exact h1s
    · rw [← smul_smul, ← smul_smul, ← smul_add, he2]

/-- 件 1（CF-4a）：四点约束下，双锥 `affGe {0} {v1,v3} ∩ affGe {0} {v2,v4}`
含非零点 ⟹ 存在（可能整体对换 (v1,v3)↔(v2,v4) 的）四元组使
`segment [w1,w3] ∩ convex hull {0,w2,w4} ≠ ∅`。
HOL 锚点：CKQOWSA_4.hl:4116-4210（含 `ASM_CASES_TAC t1'+t2' <= t1+t2` 的
WLOG 对换，对换后由 `DIST_SYM` 复核各距离）。所有下游件（rotation2_full 等）
的假设清单在 (v1,v3)↔(v2,v4) 对换下不变，故此 ∃ 形即 HOL :4185 的 MP 形。 -/
theorem cf4_cone_inter_imp_segment_conv {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus)
    (hb3 : v3 ∈ ballAnnulus) (hb4 : v4 ∈ ballAnnulus)
    (h13 : v1 ≠ v3) (h24 : v2 ≠ v4)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd13 : 2 ≤ dist v1 v3) (hd24 : 2 ≤ dist v2 v4)
    (hp : ∃ p, p ≠ 0 ∧ p ∈ affGe {0} ({v1, v3} : Set V3) ∩ affGe {0} ({v2, v4} : Set V3)) :
    ∃ w1 w2 w3 w4 : V3,
      w1 ∈ ballAnnulus ∧ w2 ∈ ballAnnulus ∧ w3 ∈ ballAnnulus ∧ w4 ∈ ballAnnulus ∧
      dist w1 w3 ≤ 2 * h0 ∧ dist w2 w4 ≤ 2 * h0 ∧
      2 ≤ dist w1 w2 ∧ 2 ≤ dist w1 w4 ∧ 2 ≤ dist w2 w3 ∧ 2 ≤ dist w3 w4 ∧ 2 ≤ dist w2 w4 ∧
      (segment ℝ w1 w3 ∩ convexHull ℝ (insert (0:V3) ({w2, w4} : Set V3))).Nonempty := by
  obtain ⟨p, hpn, hp⟩ := hp
  obtain ⟨ha1, -⟩ := inBallAnnulus hb1
  obtain ⟨ha2, -⟩ := inBallAnnulus hb2
  obtain ⟨ha3, -⟩ := inBallAnnulus hb3
  obtain ⟨ha4, -⟩ := inBallAnnulus hb4
  have hv1n : v1 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha1; norm_num at ha1
  have hv2n : v2 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha2; norm_num at ha2
  have hv3n : v3 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha3; norm_num at ha3
  have hv4n : v4 ≠ 0 := by
    intro h; rw [h, norm_zero] at ha4; norm_num at ha4
  obtain ⟨t1, t2, ht1, ht2, he1⟩ := (affGe_0_2_char hv1n hv3n h13 p).1 hp.1
  obtain ⟨t1', t2', ht1', ht2', he2⟩ := (affGe_0_2_char hv2n hv4n h24 p).1 hp.2
  rcases le_or_gt (t1' + t2') (t1 + t2) with hle | hlt
  · refine ⟨v1, v2, v3, v4, hb1, hb2, hb3, hb4, hd13l, hd24l, hd12, hd14, hd23, hd34,
      hd24, ?_⟩
    · exact cf4_segment_conv_aux hpn ht1 ht2 ht1' ht2' he1.symm he2.symm hle
  · -- WLOG 对换：(w1,w2,w3,w4) := (v2,v1,v4,v3)
    refine ⟨v2, v1, v4, v3, hb2, hb1, hb4, hb3, hd24l, hd13l, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dist_comm v2 v1]; exact hd12
    · exact hd23
    · exact hd14
    · rw [dist_comm v4 v3]; exact hd34
    · exact hd13
    · exact cf4_segment_conv_aux hpn ht1' ht2' ht1 ht2 he2.symm he1.symm hlt.le

/-! ## 3. 件 2：分离平面（separation_plane_4_points, CKQOWSA_4.hl:2870-3003）

结构（对应 HOL 逐段）：`zero_not_between_estd`（:117）+ cross 积法向
n := ±(v2 ×₃ v4)（:2905-2914）+ 4 次调用 L3F 孪生排除四点入锥（:2924-2942）+
`segment_inter_aff_ge_ends`（:373，v1·n = 0 分支）+ 平面参数化
（`affine_hull_3_plane` :445 的显式化 = `cf4_plane_repr`）+ 双零分支的
`segment_intersects_aff_ge_lemma`（:2138，内含 `in_aff_ge_cases_lemma` :1928 的
Cramer–符号情形分析）。 -/

/-- HOL `zero_not_between_estd`（CKQOWSA_4.hl:117-119）：annulus 中距离 ≤ 2h0
的两点，原点不落在线段上（HOL `between (vec 0) (v,w)` ⟿ 0 ∈ segment）。 -/
private theorem cf4_not_between_estd {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (hd : dist v w ≤ 2 * h0) : (0:V3) ∉ segment ℝ v w := by
  obtain ⟨hv2, -⟩ := inBallAnnulus hv
  obtain ⟨hw2, hwup⟩ := inBallAnnulus hw
  intro h0
  obtain ⟨a, b, ha, hb, hab, hvw⟩ := h0
  -- a • v + b • w = 0，a + b = 1：两端 > 0（否则端点为零），v = −(b/a)•w 反向
  have ha0 : 0 < a := by
    rcases lt_or_eq_of_le ha with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, zero_add] at hvw
      rcases smul_eq_zero.1 hvw with h' | h'
      · rw [← h, zero_add, h'] at hab
        norm_num at hab
      · rw [h', norm_zero] at hw2
        norm_num at hw2
  have hb0 : 0 < b := by
    rcases lt_or_eq_of_le hb with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero] at hvw
      rcases smul_eq_zero.1 hvw with h' | h'
      · rw [← h, add_zero, h'] at hab
        norm_num at hab
      · rw [h', norm_zero] at hv2
        norm_num at hv2
  have h1 : a • v = -(b • w) := eq_neg_iff_add_eq_zero.mpr hvw
  have hvw' : v = (-(b / a)) • w := by
    have h2 := congrArg (fun t : V3 => (a⁻¹) • t) h1
    rw [inv_smul_smul₀ ha0.ne', smul_neg, smul_smul] at h2
    have h3 : (a⁻¹ * b) = (b / a) := by field_simp
    rw [h2, h3, neg_smul]
  have hba : 0 < b / a := div_pos hb0 ha0
  have hnv : ‖v‖ = (b / a) * ‖w‖ := by
    rw [hvw', norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : (-(b / a)) < 0)]
    ring
  have hd1 : dist v w = (b / a) * ‖w‖ + ‖w‖ := by
    have h1' : dist v w = dist ((-(b / a)) • w) w := by rw [hvw']
    have h2' : dist ((-(b / a)) • w) w = ‖((-(b / a)) • w - w)‖ := dist_eq_norm _ _
    have h3' : (-(b / a)) • w - w = ((-(b / a) - 1)) • w := by module
    have h4' : ‖((-(b / a) - 1)) • w‖ = (b / a + 1) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : (-(b / a) - 1) < 0)]
      ring
    have h5' : ‖((-(b / a)) • w)‖ = (b / a) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : (-(b / a)) < 0)]
      ring
    rw [h1', h2', h3', h4']
    ring
  have h4 : (4:ℝ) ≤ dist v w := by rw [hd1, ← hnv]; linarith
  have h252 : (2:ℝ) * h0 = 2.52 := two_h0
  linarith

/-- HOL `zero_not_between`（CKQOWSA_4.hl:55-116）的结论形：0 ∉ segment[v,w]
⟹ 两端非零且异侧射线不相交（a < 0 < b ⟹ a•w ≠ b•v）。 -/
private theorem cf4_zero_not_between {v w : V3} (h0 : (0:V3) ∉ segment ℝ v w) :
    v ≠ 0 ∧ w ≠ 0 ∧ ∀ a b : ℝ, a < 0 → 0 < b → a • w ≠ b • v := by
  refine ⟨fun he => h0 ?_, fun he => h0 ?_, ?_⟩
  · exact ⟨(1:ℝ), 0, by norm_num, by norm_num, by norm_num, by simp [he]⟩
  · exact ⟨0, (1:ℝ), by norm_num, by norm_num, by norm_num, by simp [he]⟩
  · intro a b ha hb hab
    -- hab : a • w = b • v（Ne 展开后的等式）；c := a/b < 0，v = c•w
    have hc : v = (a / b) • w := by
      have hb1 := congrArg (fun t : V3 => (b⁻¹) • t) hab
      rw [inv_smul_smul₀ hb.ne', smul_smul] at hb1
      rw [← hb1]
      field_simp
    apply h0
    have hnab : a / b < 0 := by rwa [div_lt_iff₀ hb, zero_mul]
    have hcpos : 0 < 1 - a / b := by linarith
    refine ⟨1 / (1 - a / b), -(a / b) / (1 - a / b),
      div_nonneg (by norm_num) (le_of_lt hcpos),
      div_nonneg (by linarith) (le_of_lt hcpos), ?_, ?_⟩
    · have hne : (1:ℝ) - a / b ≠ 0 := ne_of_gt hcpos
      have hkey : (1:ℝ) / (1 - a / b) + -(a / b) / (1 - a / b)
          = (1 - a / b) / (1 - a / b) := by
        rw [← add_div]
        ring
      rw [hkey, div_self hne]
    · rw [hc, smul_smul, ← add_smul]
      have hsc : (1 / (1 - a / b)) * (a / b) + (-(a / b) / (1 - a / b)) = 0 := by
        rw [div_mul_eq_mul_div, one_mul, neg_div, add_neg_cancel]
      rw [hsc, zero_smul]

/-- HOL `segment_inter_aff_ge_ends`（CKQOWSA_4.hl:373-407）：v 在平面 {x·n = 0}
内、w 不在、线段 [v,w] 穿锥 ⟹ v 在锥内（交点参数 u = 0）。 -/
private theorem cf4_segment_inter_aff_ge_ends {v1 v2 v w n : V3}
    (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h12 : v1 ≠ v2)
    (h1n : inner ℝ v1 n = 0) (h2n : inner ℝ v2 n = 0)
    (hvn : inner ℝ v n = 0) (hwn : inner ℝ w n ≠ 0)
    (hcross : (segment ℝ v w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) :
    v ∈ affGe {0} ({v1, v2} : Set V3) := by
  obtain ⟨x, hxseg, hxcone⟩ := hcross
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨t1, t2, ht1, ht2, hxc⟩ := (affGe_0_2_char h1 h2 h12 x).1 hxcone
  have hxin : inner ℝ x n = 0 := by
    rw [hxc, inner_add_left, real_inner_smul_left, real_inner_smul_left, h1n, h2n]
    ring
  have hbin : inner ℝ x n = b * inner ℝ w n := by
    rw [← hx, inner_add_left, real_inner_smul_left, real_inner_smul_left, hvn, mul_zero,
      zero_add]
  rw [hxin] at hbin
  have hb0 : b = 0 := by
    rcases mul_eq_zero.1 hbin.symm with h | h
    · exact h
    · exact absurd h hwn
  have ha1 : a = 1 := by rw [hb0, add_zero] at hab; exact hab
  have hxv : x = v := by
    rw [← hx, hb0, ha1, zero_smul, add_zero, one_smul]
  rw [← hxv]
  exact (affGe_0_2_char h1 h2 h12 x).2 ⟨t1, t2, ht1, ht2, hxc⟩

/-- `¬collinear {0,v,w}` 的展开：两端非零且 w 不在 v 的实倍数射线上
（HOL `COLLINEAR_LEMMA` 的组合形，CKQOWSA_4.hl:2916 处用法；
端点为零时三点集缩为两点集，用 `collinear_pair`）。 -/
private theorem cf4_not_collinear_smul {v w : V3}
    (h : ¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3))) :
    v ≠ 0 ∧ w ≠ 0 ∧ ∀ c : ℝ, w ≠ c • v := by
  have hv0 : v ≠ 0 := by
    intro he
    refine h ?_
    have hset : (insert (0:V3) ({v, w} : Set V3)) = ({0, w} : Set V3) := by
      rw [he]
      ext z
      simp
    rw [hset]
    exact collinear_pair ℝ (0:V3) w
  have hw0 : w ≠ 0 := by
    intro he
    refine h ?_
    have hset : (insert (0:V3) ({v, w} : Set V3)) = ({0, v} : Set V3) := by
      rw [he]
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ (0:V3) v
  refine ⟨hv0, hw0, ?_⟩
  intro c hc
  refine h ?_
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0:V3), v, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | hx
  · exact ⟨0, by rw [zero_smul, vadd_eq_add, add_zero]⟩
  rcases hx with rfl | hx
  · exact ⟨1, by rw [one_smul, vadd_eq_add, add_zero]⟩
  · exact ⟨c, by rw [hx, hc, vadd_eq_add, add_zero]⟩

/-- 线性无关二元组（`¬collinear {0,v,w}` ⟹ `LinearIndependent ![v,w]`，
经 `LinearIndependent.pair_iff'`）。 -/
private theorem cf4_linearIndependent_pair {v w : V3}
    (h : ¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3))) : LinearIndependent ℝ ![v, w] := by
  obtain ⟨hv0, -, hc⟩ := cf4_not_collinear_smul h
  exact (LinearIndependent.pair_iff' hv0).2 fun a ha => hc a ha.symm

/-- 线性无关二元组下表示唯一（`LinearIndependent.pair_iff` 的直接推论）。 -/
private theorem cf4_repr_unique {v w x : V3} (hindep : LinearIndependent ℝ ![v, w])
    {a b a' b' : ℝ} (h1 : a • v + b • w = x) (h2 : a' • v + b' • w = x) :
    a = a' ∧ b = b' := by
  have h3 : (a - a') • v + (b - b') • w = 0 := by
    have hstep : (a - a') • v + (b - b') • w
        = (a • v + b • w) - (a' • v + b' • w) := by module
    rw [hstep, h1, h2, sub_self]
  have h4 := LinearIndependent.pair_iff.1 hindep (a - a') (b - b') h3
  exact ⟨sub_eq_zero.mp h4.1, sub_eq_zero.mp h4.2⟩

/-- HOL `aff_ge_0_2_SUBSET`（CKQOWSA_4.hl:338-372）：锥 {a,b} 的两个成员生成的
锥含于原锥（系数双线性）。 -/
private theorem cf4_cone_mono {a b v w : V3} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hv : v ∈ affGe {0} ({a, b} : Set V3)) (hw : w ∈ affGe {0} ({a, b} : Set V3)) :
    affGe {0} ({v, w} : Set V3) ⊆ affGe {0} ({a, b} : Set V3) := by
  obtain ⟨t1, t2, ht1, ht2, hv'⟩ := (affGe_0_2_char ha hb hab v).1 hv
  obtain ⟨t3, t4, ht3, ht4, hw'⟩ := (affGe_0_2_char ha hb hab w).1 hw
  intro y hy
  obtain ⟨s1, s2, hs1, hs2, hy'⟩ := (affGe_0_2_char hv0 hw0 hvw y).1 hy
  refine (affGe_0_2_char ha hb hab y).2 ⟨s1 * t1 + s2 * t3, s1 * t2 + s2 * t4,
    by nlinarith, by nlinarith, ?_⟩
  rw [hy', hv', hw']
  module

/-- 线段中的点落在端点锥内（HOL 消费件 `in_segment_imp_in_aff_ge_0_2` 的形）。 -/
private theorem cf4_segment_mem_cone {v w x : V3} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w)
    (hx : x ∈ segment ℝ v w) : x ∈ affGe {0} ({v, w} : Set V3) := by
  obtain ⟨a, b, ha, hb, hab, hx'⟩ := hx
  exact (affGe_0_2_char hv hw hvw x).2 ⟨a, b, ha, hb, hx'.symm⟩

/-- V3 的 Pi 分量映射的注入性与数乘相容（WithLp 桥，供 cross 积件使用）。 -/
private theorem cf4_coe_inj {x y : V3} (h : (x : Fin 3 → ℝ) = (y : Fin 3 → ℝ)) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, h]

private theorem cf4_coe_smul (r : ℝ) (x : V3) :
    ((r • x : V3) : Fin 3 → ℝ) = r • ((x : V3) : Fin 3 → ℝ) :=
  WithLp.ofLp_smul (p := 2) r x

/-- V3 上的 cross 积（Pi 侧 `crossProduct` 经 WithLp 提升；HOL `CROSS`）。 -/
private def cf4Cross (v w : V3) : V3 :=
  (WithLp.toLp 2 (crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)) : V3)

private theorem cf4Cross_dot_left (v w : V3) : inner ℝ v (cf4Cross v w) = 0 := by
  rw [cf4Cross, inner_eq_dot, dot_toLp]
  exact dot_self_cross (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)

private theorem cf4Cross_dot_right (v w : V3) : inner ℝ w (cf4Cross v w) = 0 := by
  rw [cf4Cross, inner_eq_dot, dot_toLp]
  exact dot_cross_self (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)

/-- HOL `CROSS_EQ_0` 的反向：非共线 ⟹ cross 积非零
（经 `crossProduct_ne_zero_iff_linearIndependent`，Pi 侧线性无关由
`LinearIndependent.pair_iff` + `cf4_not_collinear_smul` 的射线性直接验证）。 -/
private theorem cf4Cross_ne_zero {v w : V3}
    (h : ¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3))) : cf4Cross v w ≠ 0 := by
  obtain ⟨hv0, hw0, hc⟩ := cf4_not_collinear_smul h
  have hindep : LinearIndependent ℝ ![(v : Fin 3 → ℝ), (w : Fin 3 → ℝ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    -- hst 是 Pi 侧方程；先转回 V3 侧
    have hv3 : (s • v + t • w : V3) = 0 := by
      apply cf4_coe_inj
      rw [WithLp.ofLp_add, cf4_coe_smul, cf4_coe_smul]
      simpa using hst
    rcases eq_or_ne s 0 with hs0 | hs0
    · -- s = 0：t • w = 0 ⟹ t = 0（t = 0 与本分支 t ≠ 0 矛盾）
      rw [hs0, zero_smul, zero_add, smul_eq_zero] at hv3
      rcases hv3 with h | h
      · exact ⟨hs0, h⟩
      · exact absurd h hw0
    · -- s ≠ 0：t = 0 时 v = 0 矛盾；t ≠ 0 时 w = −(s/t)•v 与 hc 矛盾
      rcases eq_or_ne t 0 with ht0 | ht0
      · rw [ht0, zero_smul, add_zero, smul_eq_zero] at hv3
        rcases hv3 with h | h
        · exact absurd h hs0
        · exact absurd h hv0
      · have hyw : w = (-(s / t)) • v := by
          have hst' : t • w = -(s • v) := eq_neg_iff_add_eq_zero.mpr
            (by rw [add_comm]; exact hv3)
          have h2 := congrArg (fun z : V3 => (t⁻¹) • z) hst'
          rw [inv_smul_smul₀ ht0, smul_neg, smul_smul] at h2
          have hsc : (t:ℝ)⁻¹ * s = s / t := by field_simp
          rw [h2, hsc, neg_smul]
        exact (hc (-(s / t)) hyw).elim
  intro hzero
  have hcne : crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ) ≠ 0 :=
    (crossProduct_ne_zero_iff_linearIndependent (v := (v : Fin 3 → ℝ))
      (w := (w : Fin 3 → ℝ))).mpr hindep
  have hcoe : ((cf4Cross v w : V3) : Fin 3 → ℝ)
      = crossProduct (v : Fin 3 → ℝ) (w : Fin 3 → ℝ) := coe_toLp _
  rw [← hcoe, hzero] at hcne
  simpa using hcne

/-- 平面参数化（HOL `affine_hull_3_plane` :445-500 的显式化）：v2, v4 线性无关、
n ≠ 0、n ⊥ v2 ⊥ v4 时，x·n = 0 ⟹ x 可表为 v2, v4 的实系数组合。
途径：K := span{v2,v4}（finrank 2），n ∈ Kᗮ ⟹ Kᗮ = span{n}（finrank 计数），
x·n = 0 ⟹ x ∈ Kᗮᗮ = K（`Submodule.orthogonal_orthogonal`）。 -/
private theorem cf4_plane_repr {v2 v4 n x : V3}
    (hindep : LinearIndependent ℝ ![v2, v4]) (hn : n ≠ 0)
    (h2n : inner ℝ v2 n = 0) (h4n : inner ℝ v4 n = 0)
    (hxn : inner ℝ x n = 0) : ∃ a b : ℝ, x = a • v2 + b • v4 := by
  have hKrank : Module.finrank ℝ (Submodule.span ℝ ({v2, v4} : Set V3)) = 2 := by
    have h1 : Submodule.span ℝ (Set.range ![v2, v4])
        = Submodule.span ℝ ({v2, v4} : Set V3) := by
      congr 1
      simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    rw [← h1, finrank_span_eq_card hindep]
    norm_num
  have hnK : n ∈ (Submodule.span ℝ ({v2, v4} : Set V3))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, hy'⟩ := hy
    rw [← hy', inner_add_left, real_inner_smul_left, real_inner_smul_left, h2n, h4n]
    ring
  have hOrank : Module.finrank ℝ
      (Submodule.span ℝ ({v2, v4} : Set V3))ᗮ = 1 := by
    have hdim := Submodule.finrank_add_finrank_orthogonal
      (𝕜 := ℝ) (E := V3) (Submodule.span ℝ ({v2, v4} : Set V3))
    rw [hKrank] at hdim
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    linarith
  have hle : Submodule.span ℝ {n} ≤ (Submodule.span ℝ ({v2, v4} : Set V3))ᗮ := by
    intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, hy'⟩ := hy
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← hy', real_inner_smul_right,
      (Submodule.mem_orthogonal _ _).1 hnK z hz, mul_zero]
  have hKsp := Submodule.eq_of_le_of_finrank_le hle (by
    rw [hOrank, finrank_span_singleton hn])
  have hxJ : x ∈ ((Submodule.span ℝ ({v2, v4} : Set V3))ᗮ)ᗮ := by
    rw [← hKsp]
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, hy'⟩ := hy
    rw [← hy', real_inner_smul_left, real_inner_comm x n, hxn, mul_zero]
  rw [Submodule.orthogonal_orthogonal, Submodule.mem_span_pair] at hxJ
  obtain ⟨a, b, hab⟩ := hxJ
  exact ⟨a, b, hab.symm⟩

/-- 范数平方差的展开。 -/
private theorem cf4_norm_sq_sub (x y : V3) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (x - y), inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_comm y x, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

/-- 旋转不增对锥点的距离（HOL `rotation_dist_decrease_lemma` CKQOWSA_4.hl:624）：
u ∈ cone{v,w}、‖u‖ = ‖v‖ ⟹ dist(u,w) ≤ dist(v,w)。记 c := v·w、
g := u·w = t1c + t2‖w‖²，由模长约束 t2(t2‖w‖² + 2t1c) = ‖v‖²(1 − t1²) 得
g² − c² = (1 − t1²)(‖v‖²‖w‖² − c²)：t1 ≤ 1 时 c ≥ 0 ⟹ g ≥ 0 且 g² ≥ c²、
c < 0 ⟹ g ≥ t1c ≥ c；t1 > 1 时 c ≥ 0 ⟹ g ≥ t1c ≥ c、c < 0 ⟹ 若 g < c 则
g² > c² 矛盾。 -/
private theorem cf4_rotation_dist_decrease {v w u : V3} (hv : v ≠ 0) (hw : w ≠ 0)
    (hcone : u ∈ affGe {0} ({v, w} : Set V3)) (hnorm : ‖u‖ = ‖v‖) :
    dist u w ≤ dist v w := by
  -- 证明骨架：u = t1•v + t2•w（t ≥ 0），模长约束给出
  --   t2(t2‖w‖² + 2t1c) = ‖v‖²(1 − t1²)（c := v·w），
  --   g² − c² = (1 − t1²)(‖v‖²‖w‖² − c²)（g := u·w = t1c + t2‖w‖²），
  --   ed(1−t1²) = d(t2²‖w‖² + 2t1t2c)（e := ‖v‖²，C–S 给 ed ≥ c²）。
  -- t1 ≤ 1：g² ≥ c² 且 (c ≥ 0 ⟹ g ≥ 0 ⟹ g ≥ c；c < 0 ⟹ g ≥ t1c ≥ c)；
  -- t1 > 1：g² ≤ c² 且 (c ≥ 0 ⟹ g ≥ t1c ≥ c；c ≤ 0 且 g < c ⟹ g² > c² 矛盾)。
  -- 最后 dist²(u,w) − dist²(v,w) = 2(c − g) ≤ 0。
  rcases eq_or_ne v w with hwv | hwv
  · -- v = w：{v,w} = {v}，u = t•v（t ≥ 0）且 ‖t•v‖ = ‖v‖ ⟹ t = 1 ⟹ u = v
    subst hwv
    rw [Set.pair_eq_singleton] at hcone
    obtain ⟨t, ht0, hu'⟩ := (affGe_0_1_char v u).1 hcone
    have hv2 : (0:ℝ) < ‖v‖ := norm_pos_iff.2 hv
    rw [hu', norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hnorm
    have ht1 : t = 1 := mul_right_cancel₀ hv2.ne' (by rw [one_mul]; exact hnorm)
    rw [hu', ht1, one_smul]
  · -- 主分支：二系数显式化 + 模长恒等式 + g²−c² 恒等式 + t1/c 符号四分
    obtain ⟨t1, t2, ht1, ht2, hu⟩ := (affGe_0_2_char hv hw hwv u).1 hcone
    set c := inner ℝ v w with hcd
    set d := ‖w‖ ^ 2 with hdd
    set e := ‖v‖ ^ 2 with hed
    have hd0 : (0:ℝ) ≤ d := by positivity
    have hun : ‖u‖ ^ 2 = e := by rw [hnorm, hed]
    have hunsq : inner ℝ u u = e := by rw [real_inner_self_eq_norm_sq, hun]
    have hg : inner ℝ u w = t1 * c + t2 * d := by
      rw [hu, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, ← hcd, ← hdd]
    have hA : t2 * t2 * d + 2 * t1 * t2 * c + t1 * t1 * e = e := by
      have h4 : inner ℝ u u = t2 * t2 * d + 2 * t1 * t2 * c + t1 * t1 * e := by
        rw [hu, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
          real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          real_inner_comm v w, ← hcd, ← hdd, ← hed]
        ring
      rw [hunsq] at h4
      exact h4.symm
    have hAd : t2 * t2 * (d * d) + 2 * t1 * t2 * c * d = e * (1 - t1 * t1) * d := by
      linear_combination d * hA
    have hid : inner ℝ u w * inner ℝ u w - c * c = (1 - t1 * t1) * (e * d - c * c) := by
      rw [hg]
      linear_combination hAd
    have habs : |c| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
    have h1 : (0:ℝ) ≤ ‖v‖ * ‖w‖ - |c| := by linarith
    have h2 : (0:ℝ) ≤ ‖v‖ * ‖w‖ + |c| := by
      linarith [norm_nonneg v, norm_nonneg w, abs_nonneg c]
    have h3 : (0:ℝ) ≤ (‖v‖ * ‖w‖ - |c|) * (‖v‖ * ‖w‖ + |c|) := mul_nonneg h1 h2
    have h4' : (0:ℝ) ≤ |c| * |c| - c * c := by
      have h5 : (0:ℝ) ≤ |c| - c := by
        rcases le_or_gt 0 c with hc | hc
        · rw [abs_of_nonneg hc]; linarith
        · rw [abs_of_neg hc]; linarith
      have h6 : (0:ℝ) ≤ |c| + c := by
        rcases le_or_gt 0 c with hc | hc
        · rw [abs_of_nonneg hc]; linarith
        · rw [abs_of_neg hc]; linarith
      nlinarith [mul_nonneg h5 h6]
    have hcs : (0:ℝ) ≤ e * d - c * c := by nlinarith [h3, h4']
    have hge : c ≤ inner ℝ u w := by
      rcases le_or_gt t1 1 with hle1 | hgt1
      · -- t1 ≤ 1：g² ≥ c²；(c < 0 ⟹ g ≥ t1c ≥ c；c ≥ 0 ⟹ g ≥ 0 且 g² ≥ c² ⟹ g ≥ c)
        have hsq1 : t1 * t1 ≤ 1 := by nlinarith [ht1, hle1]
        have hgd : (0:ℝ) ≤ inner ℝ u w * inner ℝ u w - c * c := by
          rw [hid]; exact mul_nonneg (by linarith) hcs
        rcases le_or_gt c 0 with hc0 | hc0
        · have hstep : c ≤ t1 * c := by nlinarith [hc0, hle1]
          have hg1 : t1 * c ≤ inner ℝ u w := by rw [hg]; nlinarith [ht2, hd0]
          linarith
        · have hg0 : (0:ℝ) ≤ inner ℝ u w := by rw [hg]; nlinarith [ht1, ht2, hc0, hd0]
          exact nonneg_le_nonneg_of_sq_le_sq hg0 (by linarith)
      · -- t1 > 1：g² ≤ c²；(c ≥ 0 ⟹ g ≥ t1c ≥ c；c ≤ 0 且 g < c ⟹ g² > c² 矛盾)
        have hge1 : (1:ℝ) ≤ t1 * t1 := by nlinarith
        have hgd2 : inner ℝ u w * inner ℝ u w - c * c ≤ 0 := by
          have h2' : (0:ℝ) ≤ (t1 * t1 - 1) * (e * d - c * c) :=
            mul_nonneg (by linarith) hcs
          rw [hid]
          nlinarith [h2']
        rcases le_or_gt c 0 with hc0 | hc0
        · by_contra hcon
          push_neg at hcon
          have hgc : inner ℝ u w + c < 0 := by linarith
          have hp1 : (0:ℝ) < c - inner ℝ u w := by linarith
          have hp2 : (c - inner ℝ u w) * (c + inner ℝ u w) < 0 := by nlinarith [hp1, hgc]
          have hp3 : (c - inner ℝ u w) * (c + inner ℝ u w)
              = c * c - inner ℝ u w * inner ℝ u w := by ring
          linarith
        · have hstep : c ≤ t1 * c := by nlinarith [hc0, hgt1]
          have hg1 : t1 * c ≤ inner ℝ u w := by rw [hg]; nlinarith [ht2, hd0]
          linarith
    -- g ≥ c ⟹ dist²(u,w) = e − 2g + d ≤ e − 2c + d = dist²(v,w)
    have hd1 : dist u w = ‖u - w‖ := dist_eq_norm u w
    have hd2 : dist v w = ‖v - w‖ := dist_eq_norm v w
    have e1 : ‖u - w‖ ^ 2 = e - 2 * inner ℝ u w + d := by rw [cf4_norm_sq_sub, hun, hdd]
    have e2 : ‖v - w‖ ^ 2 = e - 2 * c + d := by rw [cf4_norm_sq_sub, hed, ← hcd, hdd]
    have hsq : ‖u - w‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by rw [e1, e2]; linarith
    refine nonneg_le_nonneg_of_sq_le_sq dist_nonneg ?_
    rw [hd1, hd2, ← pow_two, ← pow_two]
    exact hsq

/-- 系数换元：c > 0 时 cone{v,w} = cone{v, c•w}（HOL `aff_ge_eq_lemma`
CKQOWSA_3.hl:244，rotation_lemma_special 的末端归一化步骤）。 -/
private theorem cf4_aff_ge_eq_smul {v w : V3} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w)
    {c : ℝ} (hvcw : v ≠ c • w) (hc : 0 < c) :
    affGe {0} ({v, c • w} : Set V3) = affGe {0} ({v, w} : Set V3) := by
  have hne : c • w ≠ 0 := by
    intro h
    have hw0 : w = 0 := by
      rw [← inv_smul_smul₀ (a := c) (x := w) (Ne.symm hc.ne), h, smul_zero]
    exact hw hw0
  ext y
  rw [affGe_0_2_char hv hw hvw y,
    affGe_0_2_char hv hne hvcw y]
  constructor
  · rintro ⟨t1, t2, ht1, ht2, rfl⟩
    exact ⟨t1, t2 * c, ht1, mul_nonneg ht2 hc.le, by rw [smul_smul]⟩
  · rintro ⟨t1, t2, ht1, ht2, rfl⟩
    exact ⟨t1, t2 / c, ht1, div_nonneg ht2 hc.le, by rw [smul_smul]; field_simp⟩

/-- HOL `rotation_lemma`（CKQOWSA_3.hl:828-1010）：非共线同范数对 (v, u) 的
连续圆弧。显式构造：φ := ∠(v,u) ∈ (0, π)（非共线 ⟹ sin φ > 0），
e := (sin φ)⁻¹•(u − cos φ•v)（⊥ v、‖e‖ = ‖v‖），
f t := cos(φ•t)•v + sin(φ•t)•e（2×2 旋转嵌入 span{v,e}）。
性质：f 0 = v、f 1 = u（sin φ•e = u − cos φ•v）、‖f t‖ = ‖v‖
（cos² + sin² = 1）、f t ∈ cone{v,u}（系数 sin(φ(1−t))/sinφ ≥ 0 与
sin(φt)/sinφ ≥ 0，φ(1−t) ∈ [0,π]）、连续。
NEEDS: CF-4b 移植（Mathlib 侧 InnerProductGeometry.angle/cos_angle/sin_angle
已核可；约 120 行）。 -/
theorem cf4_rotation_lemma
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v, u} : Set V3))) (hnorm : ‖v‖ = ‖u‖) :
    ∃ f : ℝ → V3, f 0 = v ∧ f 1 = u ∧ (∀ t, ‖f t‖ = ‖v‖) ∧
      (∀ t ∈ Set.Icc 0 1, f t ∈ affGe {0} ({v, u} : Set V3)) ∧ Continuous f := by
  obtain ⟨hv0, hu0, hnc⟩ := cf4_not_collinear_smul hcol
  have hvu : v ≠ u := fun he => hnc 1 (by rw [he, one_smul])
  have hun : ‖u‖ ≠ 0 := ne_of_gt (norm_pos_iff.2 hu0)
  set φ : ℝ := InnerProductGeometry.angle v u with hφdef
  have hφ0 : 0 ≤ φ := InnerProductGeometry.angle_nonneg v u
  have hφpi : φ ≤ Real.pi := InnerProductGeometry.angle_le_pi v u
  have hφpos : 0 < φ := by
    rcases le_iff_eq_or_lt.mp hφ0 with h | h
    · exfalso
      have hz : φ = 0 := h.symm
      rw [hφdef, InnerProductGeometry.angle_eq_zero_iff] at hz
      exact hnc _ hz.2.choose_spec.2
    · exact h
  have hφlt : φ < Real.pi := by
    rcases le_iff_eq_or_lt.mp hφpi with h | h
    · exfalso
      have hz : φ = Real.pi := h
      rw [hφdef, InnerProductGeometry.angle_eq_pi_iff] at hz
      exact hnc _ hz.2.choose_spec.2
    · linarith
  have hsin : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφpos hφlt
  have hinn : inner ℝ v u = Real.cos φ * (‖v‖ * ‖v‖) := by
    have hcos : Real.cos φ = inner ℝ v u / (‖v‖ * ‖u‖) := by
      rw [hφdef, InnerProductGeometry.cos_angle]
    rw [hcos, hnorm]
    field_simp
  -- 圆弧的正交补方向 e：⊥ v、‖e‖ = ‖v‖、sin φ•e = u − cos φ•v
  obtain ⟨e, hev, hen, hsfe⟩ :
      ∃ e : V3, inner ℝ e v = 0 ∧ ‖e‖ = ‖v‖ ∧ Real.sin φ • e = u - Real.cos φ • v := by
    refine ⟨(Real.sin φ)⁻¹ • (u - Real.cos φ • v), ?_, ?_, ?_⟩
    · rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left,
        real_inner_comm v u, hinn, real_inner_self_eq_norm_sq]
      ring
    · have h2 : ‖u - Real.cos φ • v‖ ^ 2 = (Real.sin φ * ‖v‖) ^ 2 := by
        have hsq : ‖u - Real.cos φ • v‖ ^ 2
            = inner ℝ (u - Real.cos φ • v) (u - Real.cos φ • v) :=
          (real_inner_self_eq_norm_sq _).symm
        rw [hsq, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_right,
          real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
          real_inner_comm v u, hinn, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          ← hnorm]
        linear_combination -(‖v‖ * ‖v‖) * Real.sin_sq φ
      have h3 : ‖u - Real.cos φ • v‖ = Real.sin φ * ‖v‖ :=
        sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hsin.le (norm_nonneg _)) |>.1 h2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsin), h3, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hsin), one_mul]
    · rw [smul_inv_smul₀ (ne_of_gt hsin)]
  refine ⟨fun t => Real.cos (φ * t) • v + Real.sin (φ * t) • e, ?_, ?_, ?_, ?_, ?_⟩
  · show Real.cos (φ * 0) • v + Real.sin (φ * 0) • e = v
    rw [mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
  · show Real.cos (φ * 1) • v + Real.sin (φ * 1) • e = u
    rw [mul_one, hsfe]
    module
  · intro t
    have hcs : Real.sin (φ * t) ^ 2 + Real.cos (φ * t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have hftt : inner ℝ (Real.cos (φ * t) • v + Real.sin (φ * t) • e)
        (Real.cos (φ * t) • v + Real.sin (φ * t) • e) = inner ℝ v v := by
      rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right]
      simp only [real_inner_comm e v, hev, mul_zero, add_zero, zero_add,
        real_inner_self_eq_norm_sq, hen]
      linear_combination (‖v‖ * ‖v‖) * hcs
    have hsq : ‖Real.cos (φ * t) • v + Real.sin (φ * t) • e‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact hftt
    exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.1 hsq
  · intro t ht
    have hφt0 : 0 ≤ φ * t := by nlinarith [hφpos, ht.1]
    have hφtφ : φ * t ≤ φ := by nlinarith [ht.2, hφ0]
    have hsinφt : 0 ≤ Real.sin (φ * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hφt0 (le_trans hφtφ hφpi)
    have hsub0 : 0 ≤ φ - φ * t := by linarith
    have hsub1 : φ - φ * t ≤ Real.pi := by linarith
    have hsin2 : 0 ≤ Real.sin (φ - φ * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hsub0 hsub1
    have hsplit : Real.sin (φ * t) • e
        = ((Real.sin φ)⁻¹ * Real.sin (φ * t)) • (u - Real.cos φ • v) := by
      have h1 : ((Real.sin φ)⁻¹ * Real.sin (φ * t)) • (u - Real.cos φ • v)
          = ((Real.sin φ)⁻¹ * Real.sin (φ * t)) • (Real.sin φ • e) := by
        rw [← hsfe]
      rw [h1, smul_smul, mul_assoc, mul_comm (Real.sin (φ * t)) (Real.sin φ),
        ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsin), one_mul]
    refine (affGe_0_2_char hv0 hu0 hvu _).2
      ⟨((Real.sin φ)⁻¹ * Real.sin (φ - φ * t)), ((Real.sin φ)⁻¹ * Real.sin (φ * t)),
        mul_nonneg (inv_nonneg.2 hsin.le) hsin2,
        mul_nonneg (inv_nonneg.2 hsin.le) hsinφt, ?_⟩
    show Real.cos (φ * t) • v + Real.sin (φ * t) • e
        = ((Real.sin φ)⁻¹ * Real.sin (φ - φ * t)) • v
          + ((Real.sin φ)⁻¹ * Real.sin (φ * t)) • u
    rw [hsplit, smul_sub, smul_smul, Real.sin_sub, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hsin), one_mul]
    module
  · fun_prop

/-- HOL `rotation_lemma_special`（CKQOWSA_4.hl:1012-1240）：v·n = w·n = 0 时
v 绕轴 n 转向 (‖v‖/‖w‖)•w 的连续族（保范、保轴正交性、不增距、保锥）。
非共线 {0,v,u} 情形由 `cf4_rotation_lemma` + `cf4_aff_ge_eq_smul`（cone 换元
u = (‖v‖/‖w‖)•w）+ `cf4_rotation_dist_decrease` 组装（经 min/max 夹逼延拓到全轴，
区间外取端点——端点亦 ⊥ n）；共线情形 v ∥ w（含 u = −v）经叉积取 ⊥ 补方向 e
作 π 旋转族，锥条件在该分支空缺。 -/
private theorem cf4_collinear_smul {a b : V3} (ha : a ≠ 0)
    (h : Collinear ℝ (insert (0:V3) ({a, b} : Set V3))) : ∃ c : ℝ, b = c • a := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, z, hall⟩ := h
  obtain ⟨r₀, hr₀⟩ := hall (0:V3) (by simp)
  obtain ⟨r₁, hr₁⟩ := hall a (by simp)
  obtain ⟨r₂, hr₂⟩ := hall b (by simp)
  simp only [vadd_eq_add] at hr₀ hr₁ hr₂
  have hna : a = (r₁ - r₀) • z := by
    have h4 : p₀ = -(r₀ • z) := eq_neg_of_add_eq_zero_right hr₀.symm
    rw [hr₁, h4]
    module
  have hz0 : r₁ - r₀ ≠ 0 := by
    intro he
    rw [he, zero_smul] at hna
    exact ha hna
  refine ⟨(r₂ - r₀) * (r₁ - r₀)⁻¹, ?_⟩
  have h4 : p₀ = -(r₀ • z) := eq_neg_of_add_eq_zero_right hr₀.symm
  rw [hr₂, h4, hna, smul_smul]
  have hk : (r₂ - r₀) * (r₁ - r₀)⁻¹ * (r₁ - r₀) = r₂ - r₀ := by field_simp
  rw [hk, sub_smul]
  abel

/-- 非共线的显式充分条件：两端非零且 b 不是 a 的实倍数。 -/
private theorem cf4_not_collinear_mk {a b : V3} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ c : ℝ, b ≠ c • a) : ¬ Collinear ℝ (insert (0:V3) ({a, b} : Set V3)) := by
  intro h
  obtain ⟨c, hbc⟩ := cf4_collinear_smul ha h
  exact hc c hbc

/-- 正交对上的一般旋转范数式：a ⊥ b、‖b‖ = ‖a‖ 时
‖c•a + s•b‖² = (c² + s²)·‖a‖²。 -/
private theorem cf4_orth_pair_norm_sq {a b : V3} (hab : inner ℝ a b = 0) (hn : ‖b‖ = ‖a‖)
    (c s : ℝ) : ‖c • a + s • b‖ ^ 2 = (c * c + s * s) * ‖a‖ ^ 2 := by
  have h1 : ‖c • a + s • b‖ ^ 2
      = inner ℝ (c • a + s • b) (c • a + s • b) := (real_inner_self_eq_norm_sq _).symm
  rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right]
  simp only [real_inner_comm a b, hab, mul_zero, add_zero, zero_add,
    real_inner_self_eq_norm_sq, hn]
  ring

/-- 正交对上的单位旋转：c² + s² = 1 时 ‖c•a + s•b‖ = ‖a‖。 -/
private theorem cf4_orth_pair_norm {a b : V3} (hab : inner ℝ a b = 0) (hn : ‖b‖ = ‖a‖)
    (c s : ℝ) (hpy : s * s + c * c = 1) : ‖c • a + s • b‖ = ‖a‖ :=
  sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.1 (by
    rw [cf4_orth_pair_norm_sq hab hn c s]
    linear_combination (‖a‖ * ‖a‖) * hpy)

/-- HOL `rotation_lemma_special`（CKQOWSA_4.hl:1012-1240）：v·n = w·n = 0 时
v 绕轴 n 转向 (‖v‖/‖w‖)•w 的连续族（保范、保轴正交性、不增距、保锥）。
NEEDS: 组装路线已试写至逐行（CF-4b 未完，卡点见下）：
1. 非共线分支：`cf4_rotation_lemma`（v, u := (‖v‖/‖w‖)•w）给出 f 0 = v、f 1 = u、
   保范、cone{v,u}、连续；cone{v,u} → cone{v,w} 经 `cf4_aff_ge_eq_smul`；
   ⟪f t,n⟫ = 0 用 cone 二系数展开 + hvn/hunn2；dist 不增用
   `cf4_rotation_dist_decrease`。注意 rotation_lemma 的锥成员只在 [0,1] 上成立，
   而本陈述的保范+⊥n 是 ∀ t——需 min/max 夹逼延拓 g t = f (min (max t 0) 1)
   （连续性 hfcont.comp (by fun_prop)；三段 g t = 0 / g t = t / g t = 1 分别取
   f 0 = v（⟨rfl, hvn⟩）/ 中段 / f 1 = u（⟨hunn, hunn2⟩）。
   ⚠ 夹逼段的 goal 是 β 未约简形 `(fun t => f (g t)) t`，先 `show f (g t) …`
   再 rw，否则 rw [hg_*] 全部失配。
   ⚠ hg_* 三件的证法：`show min (max t 0) 1 = 0` 后
   `rw [max_eq_right ht, min_eq_left (by norm_num)]`（hg_le0，ht : t ≤ 0）；
   hg_ge1 用 max_eq_left (0 ≤ t) + min_eq_right ht；hg_mid 用
   max_eq_left ht.1.le + min_eq_left ht.2.le（Ioo 严格对 0 端）。
2. 共线分支：`cf4_collinear_smul` 给 w = c•v；|c| = ‖w‖/‖v‖ 且 c < 0
   （c > 0 给 u = v 矛盾）⟹ w = -(‖w‖/‖v‖)•v。⊥ 补方向 e 由叉积构造：
   ∃ p ≠ 0、p ∦ v、⟪n, cf4Cross v p⟫ = 0（n ≠ 0 取 p = n 用
   cf4Cross_dot_right v n；n = 0 取 x ∉ span{v}——span{v} ≠ ⊤ 经
   finrank_span_singleton hv 与 finrank_top 矛盾——此时 ⟪n,·⟫ = 0 平凡），
   e := (‖v‖/‖cf4Cross v p‖)•cf4Cross v p，f t = cos(πt)•v + sin(πt)•e；
   范数与 dist 用 `cf4_orth_pair_norm(_sq)`（⊥ 对双线性恒等式），
   dist² 差 = 2k(cos πt − 1)·‖v‖² ≤ 0（nlinarith [sin_sq_add_cos_sq, h1p]）。
   锥条件在共线分支空缺（前提 ¬Collinear 直接矛盾）。
3. 通用雷区：`rw [hcw]`（hcw : w = c•v）会同时改写目标里的 ‖w‖——目标含
   ‖w‖ 时改用 congrArg 迁移等式；`set u with hu` 后 hunn2 的 smul 在左
   （real_inner_smul_left）；∃! 的匿名构造子须 ⟨w, ?_, ?_⟩ + show β 约简
   （ExistsUnique 在此版本是 ∃ x, P x ∧ ∀ y, P y → y = x 的 def）；
   div_eq_zero_iff 无参数形式给三岐 Or；LT.lt.ne/ne' 在本 toolchain 都是
   a ≠ b 方向（用 ne_of_gt）。 -/
theorem cf4_rotation_family_special {v w n : V3} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvn : inner ℝ v n = 0) (hwn : inner ℝ w n = 0) :
    ∃ f : ℝ → V3, Continuous f ∧ f 0 = v ∧ f 1 = (‖v‖ / ‖w‖) • w ∧
      (∀ t, ‖f t‖ = ‖v‖ ∧ inner ℝ (f t) n = 0) ∧
      (∀ t ∈ Set.Icc 0 1, dist (f t) w ≤ dist v w) ∧
      (¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3)) →
        ∀ t ∈ Set.Icc 0 1, f t ∈ affGe {0} ({v, w} : Set V3)) :=
  -- NEEDS: rotation_lemma_special CKQOWSA_4.hl:1012（CF-4b/4c；逐行试写记录见上 docstring）
  sorry

/-- HOL `rotation_about_axis`（CKQOWSA_4.hl:1676-1758）：绕轴直线 ℝd 转动 v 到
a•w + b•d（a > 0 为正交分量的比例、b 由 d 分量决定），轴上点距离不变、
对 w 距离不增。构造：⊥ 分量 pv := v − (⟪v,d⟫/‖d‖²)•d 经
`cf4_rotation_family_special`（n := d）旋转至 (‖pv‖/‖pw‖)•pw，f t := g t +
(⟪v,d⟫/‖d‖²)•d；轴距不变由 ‖f t‖ = ‖pv‖ 与 ∥-分量不变合成。
NEEDS: CF-4c（上游 cf4_rotation_family_special 未闭合，见其 docstring 卡点）。 -/
theorem cf4_rotation_about_axis {d v w : V3} (hd : d ≠ 0)
    (hvw : v - (inner ℝ v d / ‖d‖ ^ 2) • d ≠ 0)
    (hww : w - (inner ℝ w d / ‖d‖ ^ 2) • d ≠ 0) :
    ∃ f : ℝ → V3, ∃ a b : ℝ, 0 < a ∧ Continuous f ∧ f 0 = v ∧
      f 1 = a • w + b • d ∧
      (∀ t c : ℝ, dist (f t) (c • d) = dist v (c • d)) ∧
      (∀ t ∈ Set.Icc 0 1, dist (f t) w ≤ dist v w) :=
  -- NEEDS: rotation_about_axis CKQOWSA_4.hl:1676（CF-4c）
  sorry

/-! ## 6. 件 4：穿越不变量的起始端（aff_ge_inter_segments :1238 + 连续性陈述）

完整传递机器（HOL continuous_lemma_aff_ge :2204-2869，约 665 行）属 CF-4b；
本节交付起始端：换端点传递（HOL :1238）+ 连续性/打靶两陈述（带账脚手架）。 -/

/-- HOL `aff_ge_inter_segments`（CKQOWSA_4.hl:1238-1395）：换端点传递——
p ∈ cone{v,u} 且 segment[v,w] 穿过射线 cone{u} ⟹ segment[p,w] 亦穿过。
代数核：交点 x = y•u = (1−s)v + s•w 与 p = a•v + b•u 联立得
(1−σ)p + σw = τ•u（σ = as/(1−s+as)、τ ≥ 0）。 -/
theorem cf4_aff_ge_inter_segments {v w u p : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v, u} : Set V3)))
    (hp : p ∈ affGe {0} ({v, u} : Set V3))
    (hcross : (segment ℝ v w ∩ affGe {0} ({u} : Set V3)).Nonempty) :
    (segment ℝ p w ∩ affGe {0} ({u} : Set V3)).Nonempty := by
  obtain ⟨hv0, hu0, hnc⟩ := cf4_not_collinear_smul hcol
  have hvu : v ≠ u := fun he => hnc 1 (by rw [he, one_smul])
  obtain ⟨x, hxseg, hxu⟩ := hcross
  obtain ⟨c1, c2, hc1, hc2, hc12, hx⟩ := hxseg
  obtain ⟨t, ht, hxt⟩ := (affGe_0_1_char u x).1 hxu
  obtain ⟨a, b, ha, hb, hpab⟩ := (affGe_0_2_char hv0 hu0 hvu p).1 hp
  rcases lt_or_eq_of_le (by linarith : c2 ≤ 1) with hc21 | hc21
  · -- 主分支：c2 < 1。交点 = D⁻¹•((1-c2)•p + (a·c2)•w)，D := 1-c2+a·c2 > 0
    have hm0 : (0:ℝ) ≤ 1 - c2 := by linarith
    have hn0 : (0:ℝ) ≤ a * c2 := mul_nonneg ha hc2
    have hd0 : (0:ℝ) < (1 - c2) + a * c2 := by linarith
    have hc1m : c1 = 1 - c2 := by linarith
    have hkey : (1 - c2) • p + (a * c2) • w = (a * t + b * (1 - c2)) • u := by
      have e1 : (1 - c2) • v + c2 • w = x := by rw [← hx, hc1m]
      have hva : ((1 - c2) * a) • v + (a * c2) • w = (a * t) • u := by
        have hgrp : ((1 - c2) * a) • v + (a * c2) • w
            = a • ((1 - c2) • v + c2 • w) := by module
        rw [hgrp, e1, hxt, smul_smul]
      rw [hpab, smul_add, smul_smul, smul_smul, add_right_comm, hva]
      module
    refine ⟨(1 - c2 + a * c2)⁻¹ • ((1 - c2) • p + (a * c2) • w),
      ⟨(1 - c2) * (1 - c2 + a * c2)⁻¹, (a * c2) * (1 - c2 + a * c2)⁻¹,
        mul_nonneg hm0 (inv_nonneg.2 hd0.le), mul_nonneg hn0 (inv_nonneg.2 hd0.le), ?_, ?_⟩,
      (affGe_0_1_char u ((1 - c2 + a * c2)⁻¹ • ((1 - c2) • p + (a * c2) • w))).2
        ⟨(1 - c2 + a * c2)⁻¹ * (a * t + b * (1 - c2)),
          mul_nonneg (inv_nonneg.2 hd0.le)
            (add_nonneg (mul_nonneg ha ht) (mul_nonneg hb hm0)),
          by rw [hkey, smul_smul]⟩⟩
    · rw [← add_mul, mul_inv_cancel₀ (ne_of_gt hd0)]
    · module
  · -- c2 = 1：x = w = t•u，w 自身即 [p,w] ∩ cone{u} 的交点
    have hc1m : c1 = 1 - c2 := by linarith
    have hc10 : c1 = 0 := by rw [hc1m, hc21]; norm_num
    rw [hc21, one_smul, hc10, zero_smul, zero_add] at hx
    exact ⟨w, ⟨(0:ℝ), 1, by norm_num, by norm_num, by norm_num,
      by rw [zero_smul, zero_add, one_smul]⟩, (affGe_0_1_char u w).2 ⟨t, ht,
      by rw [hx.trans hxt]⟩⟩

/-- HOL `continuous_intersection_point`（CKQOWSA_4.hl:1785-1928）：交点对参数的
连续依赖（2×2 线性组的 Cramer 解连续，continuous_solution_aux :1748）。
NEEDS: CF-4b。路线：s t := -⟪f t,n⟫/(⟪w,n⟫-⟪f t,n⟫) ∈ [0,1]（分母 > 0 严格），
交点 x t = (1-s t)•f t + s t•w；{v1,v2} 线性无关（cf4_linearIndependent_pair）
⟹ Gram 行列式 G = ⟪v1,v1⟫⟪v2,v2⟫-⟪v1,v2⟫² > 0（严格 Cauchy–Schwarz 反证），
α β 取显式 Cramer 公式（⟪x,vᵢ⟫ 的线性组合除以 G），连续性全部落在
ContinuousOn.inner + 四则运算封闭；交唯一性由 s 的方程 (1-s)A+sW=0 的唯一解。
辅助路线（可复用）：span{v1,v2} = {x : ⟪x,n⟫ = 0} 的成员表示经
`cf4_plane_repr`（本文件已备）。 -/
theorem cf4_continuous_intersection_point {v1 v2 w n : V3} (f : ℝ → V3) (t1 : ℝ)
    (ht1 : 0 ≤ t1)
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hf : ContinuousOn f (Set.Icc 0 t1))
    (h1n : inner ℝ v1 n = 0) (h2n : inner ℝ v2 n = 0) (hwn : 0 < inner ℝ w n)
    (hfn : ∀ t ∈ Set.Icc 0 t1, inner ℝ (f t) n ≤ 0) :
    ∃ α β : ℝ → ℝ, (ContinuousOn α (Set.Icc 0 t1) ∧ ContinuousOn β (Set.Icc 0 t1)) ∧
      ∀ t ∈ Set.Icc 0 t1,
        segment ℝ (f t) w ∩ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3))
          = {α t • v1 + β t • v2} :=
  -- NEEDS: continuous_intersection_point CKQOWSA_4.hl:1785（CF-4b）
  sorry

/-- HOL `continuous_lemma_aff_ge`（CKQOWSA_4.hl:2204-2869，全章最大单件 665 行）：
穿越不变量在连续旋转族下的传递。NEEDS: CF-4b 主件（保留 sorry）。
卡点诊断（CF-4b 试写后）：HOL 的证明依赖
①in_aff_ge_cases_lemma :1928 + segment_intersects_aff_ge_lemma :2138（穿锥判别
两分支，未移植）②continuous_intersection_point（α β 连续参数化，见上件）③
aff_ge_inter_segments（本文件已闭合）④IVT 打靶（dist_decreasing_ivt 家族，未移植）。
Lean 路线建议：记 S := {t ∈ [0,h] | segment[f t,w] ∩ cone{v1,v2} ≠ ∅}，用
f 的连续性 + 分离超平面 {x : ⟪x,n⟫ = 0}（v1 v2 n 的正交关系）证 S 同时开闭，
再由 [0,h] 连通得 S = [0,h] 或给出 x 分界点（结论的二支）。上游依赖：
cf4_rotation_family_special（本文件 NEEDS，试写记录见其 docstring）与
cf4_continuous_intersection_point（见上件）。 -/
theorem cf4_continuous_lemma_aff_ge {v1 v2 w : V3} (f : ℝ → V3) (h : ℝ) (hh : 0 ≤ h)
    (hf : ContinuousOn f (Set.Icc 0 h))
    (hstart : (segment ℝ (f 0) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty)
    (hnb : ∀ t ∈ Set.Icc 0 h, (0:V3) ∉ segment ℝ (f t) w)
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v1, v2} : Set V3))) :
    (∀ t ∈ Set.Icc 0 h, (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) ∨
      (∃ x, 0 ≤ x ∧ x ≤ h ∧
        (∀ t ∈ Set.Icc 0 x, (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) ∧
        (f x ∈ affGe {0} ({v1, v2} : Set V3) ∨
          v1 ∈ affGe {0} ({f x, w} : Set V3) ∨
          v2 ∈ affGe {0} ({f x, w} : Set V3))) :=
  -- NEEDS: continuous_lemma_aff_ge CKQOWSA_4.hl:2204（CF-4b，600-1000 行）
  sorry

/-! ## 7. 件 5：外心终端预备（lemma_4_points_circumcenter :3866 的前置件）

仓库无 PA18 `cc_uh_exists`（grep 实测），自带构造：Mathlib simplex 外心
（`EuclideanGeometry.circumcenter`，AffineIndependent ![0,v2,v4] 经
`collinear_iff_not_affineIndependent_set`）。R² 记号展开 =
等距点的内积刻画 `cf4_dot_of_dist2`（终局 parallelogram + ETA_Y 的输入）。 -/

/-- 非共线 {0, v2, v4} ⟹ ![0, v2, v4] 仿射独立。 -/
private theorem cf4_affineIndependent3 {v2 v4 : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3))) :
    AffineIndependent ℝ ![0, v2, v4] :=
  not_not.mp ((collinear_iff_not_affineIndependent_set (p₁ := (0:V3)) (p₂ := v2)
    (p₃ := v4)).not.mp hcol)

/-- 外心存在：非共线 {0, v2, v4} 的 affineSpan 内存在到三点等距的点
（即外心；Mathlib `AffineIndependent.existsUnique_dist_eq` 的外接球见证，
range/insert 换算经 ext+simp，点值换算走定义性展开免 rw）。 -/
theorem cf4_circumcenter3_exists {v2 v4 : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3))) :
    ∃ c : V3, c ∈ affineSpan ℝ (insert (0:V3) ({v2, v4} : Set V3)) ∧
      dist c (0:V3) = dist c v2 ∧ dist c v2 = dist c v4 := by
  have hAI := cf4_affineIndependent3 hcol
  have hrange : Set.range (![(0:V3), v2, v4] : Fin 3 → V3)
      = insert (0:V3) ({v2, v4} : Set V3) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    tauto
  obtain ⟨cs, ⟨hcmem, hcrange⟩, -⟩ := hAI.existsUnique_dist_eq
  -- hcrange 的成员形经定义性展开直取（球成员 = dist z cs.center = cs.radius）
  have h0' : dist (0:V3) cs.center = cs.radius := hcrange (Set.mem_range_self 0)
  have h1' : dist v2 cs.center = cs.radius := hcrange (Set.mem_range_self 1)
  have h2' : dist v4 cs.center = cs.radius := hcrange (Set.mem_range_self 2)
  have h0 : dist cs.center (0:V3) = cs.radius := (dist_comm cs.center 0).trans h0'
  have h1 : dist cs.center v2 = cs.radius := (dist_comm cs.center v2).trans h1'
  have h2 : dist cs.center v4 = cs.radius := (dist_comm cs.center v4).trans h2'
  refine ⟨cs.center, ?_, h0.trans h1.symm, h1.trans h2.symm⟩
  rw [← hrange]
  exact hcmem

/-- 外心唯一：affineSpan 内到三点等距的点即外心（同一外接球唯一性：
候选 y 连同半径 dist y 0 构成第二外接球，由 existsUnique 收敛到球等式再取心）。 -/
theorem cf4_circumcenter3_existsUnique {v2 v4 : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3))) :
    ∃! c : V3, c ∈ affineSpan ℝ (insert (0:V3) ({v2, v4} : Set V3)) ∧
      dist c (0:V3) = dist c v2 ∧ dist c v2 = dist c v4 := by
  have hAI := cf4_affineIndependent3 hcol
  have hrange : Set.range (![(0:V3), v2, v4] : Fin 3 → V3)
      = insert (0:V3) ({v2, v4} : Set V3) := by
    ext z
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    tauto
  obtain ⟨cs, ⟨hcmem, hcrange⟩, hcuniq⟩ := hAI.existsUnique_dist_eq
  have h0' : dist (0:V3) cs.center = cs.radius := hcrange (Set.mem_range_self 0)
  have h1' : dist v2 cs.center = cs.radius := hcrange (Set.mem_range_self 1)
  have h2' : dist v4 cs.center = cs.radius := hcrange (Set.mem_range_self 2)
  have h0 : dist cs.center (0:V3) = cs.radius := (dist_comm cs.center 0).trans h0'
  have h1 : dist cs.center v2 = cs.radius := (dist_comm cs.center v2).trans h1'
  have h2 : dist cs.center v4 = cs.radius := (dist_comm cs.center v4).trans h2'
  refine ⟨cs.center, ?_, ?_⟩
  · show cs.center ∈ affineSpan ℝ (insert (0:V3) ({v2, v4} : Set V3)) ∧
      dist cs.center (0:V3) = dist cs.center v2 ∧ dist cs.center v2 = dist cs.center v4
    rw [← hrange]
    exact ⟨hcmem, h0.trans h1.symm, h1.trans h2.symm⟩
  rintro y ⟨hymem, hy01, hy12⟩
  have hspan : y ∈ affineSpan ℝ (Set.range (![(0:V3), v2, v4] : Fin 3 → V3)) := by
    rw [hrange]; exact hymem
  have hp : ∀ z ∈ Set.range (![(0:V3), v2, v4] : Fin 3 → V3), dist z y = dist y (0:V3) := by
    intro z hz
    have hz' : z = (0:V3) ∨ z = v2 ∨ z = v4 := by
      rw [hrange, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      tauto
    rcases hz' with rfl | rfl | rfl
    · exact dist_comm 0 y
    · rw [dist_comm]; exact hy01.symm
    · rw [dist_comm]; exact hy12.symm.trans hy01.symm
  exact congrArg EuclideanGeometry.Sphere.center
    (hcuniq (EuclideanGeometry.Sphere.mk y (dist y (0:V3))) (And.intro hspan hp))

end Kepler.Text.ContraFanDeep
