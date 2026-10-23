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
  - CF-4c 后（2026-09-28）：旋转族机器全净（rotation_lemma/family_special/
    rotation_about_axis）+ `cf4_continuous_intersection_point`（Cramer 连续参数化）
    均闭合。
  - CF-4d 后（2026-09-28）：主件上游四件（affineSpan 刻画 / IVT 打靶
    cf4_ivt_first_hit·dec / 穿锥判别 cf4_in_aff_ge_cases +
    cf4_segment_intersects_aff_ge，HOL :1928/:2138/:785/:967）全部移植闭合，
    主件 `cf4_continuous_lemma_aff_ge`（HOL :2204-2869）按 HOL 逐段闭合——
    本模块 sorry 归零。
-/
import Kepler.Geom.Aff
import Kepler.Text.PackingAuto2
import Kepler.Text.IneqClosureDefs  -- W3a：etaY/etaX 真体（upsX 经 SphereKit 传递可见；无环已核）

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
sin(φt)/sinφ ≥ 0，φ(1−t) ∈ [0,π]）、连续。已闭合（Mathlib 侧
InnerProductGeometry.angle/cos_angle/sin_angle）。 -/
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
CF-4c 已闭合。B1 非共线：`cf4_rotation_lemma`（v, u := (‖v‖/‖w‖)•w）+
min/max 夹逼延拓 g t = f (min (max t 0) 1)（⟪g t,n⟫ = 0 与 dist/锥三件全由
夹逼段 ∈ [0,1] 的锥表示经 `cf4_aff_ge_eq_smul`（cone{v,c•w} = cone{v,w}）
统一给出，无需三段分析；dist 用 `cf4_rotation_dist_decrease`）。
B2 共线（w = c•v）：c > 0 时 (‖v‖/‖w‖)•w = v 取常数族；c < 0 时 ⊥ 补方向
e := (‖v‖/‖cf4Cross v p‖)•cf4Cross v p（n ≠ 0 取 p = n：⟪v,n⟫ = 0 ⟹ v,n
不共线；n = 0 取 x ∉ span{v}），π 旋转族 f t = cos(πt)•v + sin(πt)•e，
范数/内积用 `cf4_orth_pair_norm(_sq)`，dist² 差 = ((cosπt−c)²+sin²−(1−c)²)·‖v‖² ≤ 0。 -/
theorem cf4_rotation_family_special {v w n : V3} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvn : inner ℝ v n = 0) (hwn : inner ℝ w n = 0) :
    ∃ f : ℝ → V3, Continuous f ∧ f 0 = v ∧ f 1 = (‖v‖ / ‖w‖) • w ∧
      (∀ t, ‖f t‖ = ‖v‖ ∧ inner ℝ (f t) n = 0) ∧
      (∀ t ∈ Set.Icc 0 1, dist (f t) w ≤ dist v w) ∧
      (¬ Collinear ℝ (insert (0:V3) ({v, w} : Set V3)) →
        ∀ t ∈ Set.Icc 0 1, f t ∈ affGe {0} ({v, w} : Set V3)) := by
  by_cases hcol : Collinear ℝ (insert (0:V3) ({v, w} : Set V3))
  · -- B2 共线分支：w = c•v
    obtain ⟨c, hwc⟩ := cf4_collinear_smul hv hcol
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_smul] at hwc
      exact hw hwc
    rcases lt_or_gt_of_ne hc0 with hc | hc
    · -- c < 0：w = -(‖w‖/‖v‖)•v，π 旋转族（⊥ 补方向 e 由叉积构造）
      obtain ⟨p, hpcol, hpinn⟩ : ∃ p : V3,
          ¬ Collinear ℝ (insert (0:V3) ({v, p} : Set V3)) ∧ inner ℝ n (cf4Cross v p) = 0 := by
        by_cases hn0 : n = 0
        · -- n = 0：任取 x ∉ span{v}，此时 ⟪n,·⟫ = 0 平凡
          have hsp : (Submodule.span ℝ ({v} : Set V3)) ≠ (⊤ : Submodule ℝ V3) := by
            intro htop
            have h1 : Module.finrank ℝ (Submodule.span ℝ ({v} : Set V3)) = 1 :=
              finrank_span_singleton hv
            rw [htop, finrank_top, finrank_euclideanSpace_fin] at h1
            norm_num at h1
          obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top _ hsp
          refine ⟨x, cf4_not_collinear_mk hv ?_ ?_, ?_⟩
          · intro hx0
            rw [hx0] at hx
            exact hx (Submodule.zero_mem _)
          · intro k hk
            exact hx (Submodule.mem_span_singleton.2 ⟨k, hk.symm⟩)
          · rw [hn0]
            exact inner_zero_left _
        · -- n ≠ 0：⟪v,n⟫ = 0 ⟹ v, n 不共线，p := n
          refine ⟨n, cf4_not_collinear_mk hv hn0 ?_, cf4Cross_dot_right v n⟩
          intro k hk
          have hvn' := hvn
          rw [hk, real_inner_smul_right, real_inner_self_eq_norm_sq] at hvn'
          have hv2 : (0:ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
          rcases mul_eq_zero.1 hvn' with hk0 | hk0
          · rw [hk0, zero_smul] at hk
            exact hn0 hk
          · exact absurd hk0 hv2.ne'
      obtain ⟨e, hev, hen, heinn⟩ :
          ∃ e : V3, inner ℝ v e = 0 ∧ ‖e‖ = ‖v‖ ∧ inner ℝ e n = 0 := by
        have hcz : cf4Cross v p ≠ 0 := cf4Cross_ne_zero hpcol
        refine ⟨(‖v‖ / ‖cf4Cross v p‖) • cf4Cross v p, ?_, ?_, ?_⟩
        · rw [real_inner_smul_right, cf4Cross_dot_left]
          ring
        · rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hcz))]
          field_simp
        · rw [real_inner_smul_left, real_inner_comm n (cf4Cross v p), hpinn]
          ring
      refine ⟨fun t => Real.cos (Real.pi * t) • v + Real.sin (Real.pi * t) • e,
        by fun_prop, ?_, ?_, ?_, ?_, fun hfalse => (hfalse hcol).elim⟩
      · show Real.cos (Real.pi * 0) • v + Real.sin (Real.pi * 0) • e = v
        rw [mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
      · show Real.cos (Real.pi * 1) • v + Real.sin (Real.pi * 1) • e = (‖v‖ / ‖w‖) • w
        have hwn2 : ‖w‖ = -(c) * ‖v‖ := by
          rw [hwc, norm_smul, Real.norm_eq_abs, abs_of_neg hc]
        rw [mul_one, Real.cos_pi, neg_one_smul, Real.sin_pi, zero_smul, add_zero, hwn2,
          hwc, smul_smul]
        have h2 : (‖v‖ / (-(c) * ‖v‖)) * c = -1 := by field_simp
        rw [h2, neg_one_smul]
      · intro t
        show ‖Real.cos (Real.pi * t) • v + Real.sin (Real.pi * t) • e‖ = ‖v‖ ∧
          inner ℝ (Real.cos (Real.pi * t) • v + Real.sin (Real.pi * t) • e) n = 0
        refine ⟨cf4_orth_pair_norm hev hen _ _
          (by rw [← pow_two, ← pow_two]; exact Real.sin_sq_add_cos_sq _), ?_⟩
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hvn, heinn]
        ring
      · intro t _
        have hcos : Real.cos (Real.pi * t) ≤ 1 := Real.cos_le_one _
        have hineq : (Real.cos (Real.pi * t) - c) ^ 2 + Real.sin (Real.pi * t) ^ 2
            ≤ (1 - c) ^ 2 := by
          have h1 : Real.sin (Real.pi * t) ^ 2 + Real.cos (Real.pi * t) ^ 2 = 1 :=
            Real.sin_sq_add_cos_sq _
          nlinarith [hcos, h1, le_of_lt hc]
        have h5 : v - c • v = (1 - c) • v := by module
        have hfw : Real.cos (Real.pi * t) • v + Real.sin (Real.pi * t) • e - w
            = (Real.cos (Real.pi * t) - c) • v + Real.sin (Real.pi * t) • e := by
          rw [hwc]
          module
        have hd1 : dist (Real.cos (Real.pi * t) • v + Real.sin (Real.pi * t) • e) w ^ 2
            = ((Real.cos (Real.pi * t) - c) ^ 2 + Real.sin (Real.pi * t) ^ 2) * ‖v‖ ^ 2 := by
          rw [dist_eq_norm, hfw, cf4_orth_pair_norm_sq hev hen]
          ring
        have hd2 : dist v w ^ 2 = (1 - c) ^ 2 * ‖v‖ ^ 2 := by
          rw [dist_eq_norm, hwc, h5, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by linarith : (0:ℝ) < 1 - c)]
          ring
        refine nonneg_le_nonneg_of_sq_le_sq dist_nonneg ?_
        rw [← pow_two, ← pow_two, hd1, hd2]
        exact mul_le_mul_of_nonneg_right hineq (sq_nonneg ‖v‖)
    · -- c > 0：(‖v‖/‖w‖)•w = v，常数族 f t = v
      have hwn2 : ‖w‖ = c * ‖v‖ := by
        rw [hwc, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      refine ⟨fun _ => v, continuous_const, rfl, ?_, ?_, ?_, fun hfalse => (hfalse hcol).elim⟩
      · show v = (‖v‖ / ‖w‖) • w
        rw [hwn2, hwc, smul_smul]
        have h2 : (‖v‖ / (c * ‖v‖)) * c = 1 := by field_simp
        rw [h2, one_smul]
      · intro t
        exact ⟨rfl, hvn⟩
      · intro t _
        exact le_refl _
  · -- B1 非共线分支：rotation_lemma + min/max 夹逼延拓
    obtain ⟨-, hw0, hnc⟩ := cf4_not_collinear_smul hcol
    have hcpos : (0:ℝ) < ‖v‖ / ‖w‖ := div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hw)
    have hvw : v ≠ w := by
      intro he
      refine hcol ?_
      rw [he, Set.pair_eq_singleton]
      exact collinear_pair ℝ (0:V3) w
    have hncu : ¬ Collinear ℝ (insert (0:V3) ({v, (‖v‖ / ‖w‖) • w} : Set V3)) := by
      refine cf4_not_collinear_mk hv (smul_ne_zero hcpos.ne' hw0) ?_
      intro k hk
      refine hnc (k / (‖v‖ / ‖w‖)) ?_
      have h2 := congrArg (fun z : V3 => ((‖v‖ / ‖w‖)⁻¹ : ℝ) • z) hk
      rw [inv_smul_smul₀ hcpos.ne', smul_smul] at h2
      have h3 : (‖v‖ / ‖w‖)⁻¹ * k = k / (‖v‖ / ‖w‖) := by field_simp
      rw [h3] at h2
      exact h2
    have hwnz : ‖w‖ ≠ 0 := ne_of_gt (norm_pos_iff.2 hw)
    have hnormu : ‖v‖ = ‖(‖v‖ / ‖w‖) • w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      field_simp
    obtain ⟨f, hf0, hf1, hfnorm, hfcone, hfcont⟩ := cf4_rotation_lemma hncu hnormu
    have hvcw : v ≠ (‖v‖ / ‖w‖) • w := by
      intro he
      refine hnc ((‖v‖ / ‖w‖)⁻¹) ?_
      have h2 := congrArg (fun z : V3 => ((‖v‖ / ‖w‖)⁻¹ : ℝ) • z) he
      rw [inv_smul_smul₀ hcpos.ne'] at h2
      exact h2.symm
    have hconeeq : affGe {0} ({v, (‖v‖ / ‖w‖) • w} : Set V3)
        = affGe {0} ({v, w} : Set V3) :=
      cf4_aff_ge_eq_smul hv hw hvw hvcw hcpos
    refine ⟨fun t => f (min (max t 0) 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hcl : Continuous fun t : ℝ => min (max t 0) (1:ℝ) :=
        Continuous.min (Continuous.max continuous_id continuous_const) continuous_const
      exact hfcont.comp hcl
    · show f (min (max 0 0) 1) = v
      rw [max_self, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
      exact hf0
    · show f (min (max 1 0) 1) = (‖v‖ / ‖w‖) • w
      rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1), min_self]
      exact hf1
    · intro t
      show ‖f (min (max t 0) 1)‖ = ‖v‖ ∧ inner ℝ (f (min (max t 0) 1)) n = 0
      have hcl01 : min (max t 0) (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · have hle : min (0:ℝ) 1 ≤ min (max t 0) (1:ℝ) :=
            min_le_min (le_max_right t 0) (le_refl (1:ℝ))
          rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1)] at hle
          exact hle
        · exact min_le_right _ _
      have hm : f (min (max t 0) 1) ∈ affGe {0} ({v, w} : Set V3) := by
        have h1 := hfcone _ hcl01
        rwa [hconeeq] at h1
      obtain ⟨a, b, -, -, hfab⟩ := (affGe_0_2_char hv hw hvw _).1 hm
      exact ⟨hfnorm _, by
        rw [hfab, inner_add_left, real_inner_smul_left, real_inner_smul_left, hvn, hwn]
        ring⟩
    · intro t ht
      show dist (f (min (max t 0) 1)) w ≤ dist v w
      have heq : min (max t 0) (1:ℝ) = t := by
        rw [max_eq_left ht.1, min_eq_left ht.2]
      rw [heq]
      have h1 := hfcone t ht
      rw [hconeeq] at h1
      exact cf4_rotation_dist_decrease hv hw h1 (hfnorm t)
    · intro _ t ht
      have heq : min (max t 0) (1:ℝ) = t := by
        rw [max_eq_left ht.1, min_eq_left ht.2]
      show f (min (max t 0) 1) ∈ affGe {0} ({v, w} : Set V3)
      rw [heq]
      have h1 := hfcone t ht
      rwa [hconeeq] at h1

/-- HOL `rotation_about_axis`（CKQOWSA_4.hl:1676-1758）：绕轴直线 ℝd 转动 v 到
a•w + b•d（a > 0 为正交分量的比例、b 由 d 分量决定），轴上点距离不变、
对 w 距离不增。构造：⊥ 分量 pv := v − (⟪v,d⟫/‖d‖²)•d 经
`cf4_rotation_family_special`（n := d）旋转至 (‖pv‖/‖pw‖)•pw，f t := g t +
(⟪v,d⟫/‖d‖²)•d；轴距不变由 ‖f t‖ = ‖pv‖ 与 ∥-分量不变合成。 -/
theorem cf4_rotation_about_axis {d v w : V3} (hd : d ≠ 0)
    (hvw : v - (inner ℝ v d / ‖d‖ ^ 2) • d ≠ 0)
    (hww : w - (inner ℝ w d / ‖d‖ ^ 2) • d ≠ 0) :
    ∃ f : ℝ → V3, ∃ a b : ℝ, 0 < a ∧ Continuous f ∧ f 0 = v ∧
      f 1 = a • w + b • d ∧
      (∀ t c : ℝ, dist (f t) (c • d) = dist v (c • d)) ∧
      (∀ t ∈ Set.Icc 0 1, dist (f t) w ≤ dist v w) := by
  have hd2 : (0:ℝ) < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hd) 2
  -- ⊥ 分量 + ∥ 分量系数的抽象化（lam/mu 不透明，绕开 rw 连带改写 inner ℝ v d）
  obtain ⟨pv, lam, hpvadd, hpvne, hpvd⟩ :
      ∃ pv : V3, ∃ lam : ℝ, pv + lam • d = v ∧ pv ≠ 0 ∧ inner ℝ pv d = 0 :=
    ⟨v - (inner ℝ v d / ‖d‖ ^ 2) • d, inner ℝ v d / ‖d‖ ^ 2, by module, hvw, by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
      ring⟩
  obtain ⟨pw, mu, hpwadd, hpwne, hpwd⟩ :
      ∃ pw : V3, ∃ mu : ℝ, pw + mu • d = w ∧ pw ≠ 0 ∧ inner ℝ pw d = 0 :=
    ⟨w - (inner ℝ w d / ‖d‖ ^ 2) • d, inner ℝ w d / ‖d‖ ^ 2, by module, hww, by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
      ring⟩
  obtain ⟨g, hgcont, hg0, hg1, hgprop, hgdist, -⟩ :=
    cf4_rotation_family_special (v := pv) (w := pw) (n := d) hpvne hpwne hpvd hpwd
  refine ⟨fun t => g t + lam • d, ‖pv‖ / ‖pw‖, lam - (‖pv‖ / ‖pw‖) * mu,
    div_pos (norm_pos_iff.2 hpvne) (norm_pos_iff.2 hpwne), by fun_prop, ?_, ?_, ?_, ?_⟩
  · show g 0 + lam • d = v
    rw [hg0, hpvadd]
  · show g 1 + lam • d =
      (‖pv‖ / ‖pw‖) • w + (lam - (‖pv‖ / ‖pw‖) * mu) • d
    have h2 : (‖pv‖ / ‖pw‖) * mu + (lam - (‖pv‖ / ‖pw‖) * mu) = lam := by ring
    rw [hg1, ← hpwadd, smul_add, smul_smul, add_assoc, ← add_smul, h2]
  · intro t c
    show dist (g t + lam • d) ((c:ℝ) • d) = dist v ((c:ℝ) • d)
    refine sq_eq_sq₀ dist_nonneg dist_nonneg |>.1 ?_
    have e1 : dist (g t + lam • d) ((c:ℝ) • d) = ‖g t + (lam - c) • d‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      module
    have e2 : dist v ((c:ℝ) • d) = ‖pv + (lam - c) • d‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      rw [← hpvadd]
      module
    have hgn : ‖g t‖ = ‖pv‖ := (hgprop t).1
    have hgd : inner ℝ (g t) d = 0 := (hgprop t).2
    have s1 : ‖g t + (lam - c) • d‖ ^ 2 = ‖g t‖ ^ 2 + (lam - c) ^ 2 * ‖d‖ ^ 2 := by
      have h1 : ‖g t + (lam - c) • d‖ ^ 2
          = inner ℝ (g t + (lam - c) • d) (g t + (lam - c) • d) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm (g t) d, hgd, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      ring
    have s2 : ‖pv + (lam - c) • d‖ ^ 2 = ‖pv‖ ^ 2 + (lam - c) ^ 2 * ‖d‖ ^ 2 := by
      have h1 : ‖pv + (lam - c) • d‖ ^ 2
          = inner ℝ (pv + (lam - c) • d) (pv + (lam - c) • d) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm pv d, hpvd, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      ring
    rw [e1, s1, hgn, ← s2, ← e2]
  · intro t ht
    show dist (g t + lam • d) w ≤ dist v w
    refine nonneg_le_nonneg_of_sq_le_sq dist_nonneg ?_
    have e1 : dist (g t + lam • d) w = ‖(g t - pw) + (lam - mu) • d‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      rw [← hpwadd]
      module
    have e2 : dist v w = ‖(pv - pw) + (lam - mu) • d‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      rw [← hpvadd, ← hpwadd]
      module
    have hgd : inner ℝ (g t) d = 0 := (hgprop t).2
    have s1 : ‖(g t - pw) + (lam - mu) • d‖ ^ 2
        = ‖g t - pw‖ ^ 2 + (lam - mu) ^ 2 * ‖d‖ ^ 2 := by
      have h1 : ‖(g t - pw) + (lam - mu) • d‖ ^ 2
          = inner ℝ ((g t - pw) + (lam - mu) • d) ((g t - pw) + (lam - mu) • d) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm (g t - pw) d, inner_sub_left (g t) pw d,
        (hgprop t).2, hpwd, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have s2 : ‖(pv - pw) + (lam - mu) • d‖ ^ 2
        = ‖pv - pw‖ ^ 2 + (lam - mu) ^ 2 * ‖d‖ ^ 2 := by
      have h1 : ‖(pv - pw) + (lam - mu) • d‖ ^ 2
          = inner ℝ ((pv - pw) + (lam - mu) • d) ((pv - pw) + (lam - mu) • d) :=
        (real_inner_self_eq_norm_sq _).symm
      rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm (pv - pw) d, inner_sub_left pv pw d,
        hpvd, hpwd, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    have hle : ‖g t - pw‖ ^ 2 ≤ ‖pv - pw‖ ^ 2 := by
      have h := hgdist t ht
      rw [dist_eq_norm, dist_eq_norm] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [← pow_two, ← pow_two, e1, e2, s1, s2]
    linarith

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
CF-4c 已闭合。路线：s t := -⟪f t,n⟫/(⟪w,n⟫-⟪f t,n⟫) ∈ [0,1]（分母 > 0 严格），
交点 x t = (1-s t)•f t + s t•w 落在平面 ⟪·,n⟫ = 0 内；{v1,v2} 线性无关
（cf4_linearIndependent_pair）⟹ Gram 行列式 G > 0（严格 Cauchy–Schwarz，
等号情形经 inner_eq_norm_mul_iff_real 归结到共线矛盾），α β 取显式 Cramer 公式
（⟪x,vᵢ⟫ 的线性组合除以 G），连续性全部落在 ContinuousOn.inner + 四则封闭；
平面表示核 = `cf4_plane_repr` + affineSpan {0,v1,v2} = span{v1,v2}
（mem_affineSpan_iff_exists + vectorSpan_eq_span_vsub_set_left 双向）；
交唯一性由 σ + τ = 1 与 ⟪z,n⟫ = 0 联立的 s 唯一解。 -/
theorem cf4_continuous_intersection_point {v1 v2 w n : V3} (f : ℝ → V3) (t1 : ℝ)
    (ht1 : 0 ≤ t1)
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hf : ContinuousOn f (Set.Icc 0 t1))
    (h1n : inner ℝ v1 n = 0) (h2n : inner ℝ v2 n = 0) (hwn : 0 < inner ℝ w n)
    (hfn : ∀ t ∈ Set.Icc 0 t1, inner ℝ (f t) n ≤ 0) :
    ∃ α β : ℝ → ℝ, (ContinuousOn α (Set.Icc 0 t1) ∧ ContinuousOn β (Set.Icc 0 t1)) ∧
      ∀ t ∈ Set.Icc 0 t1,
        segment ℝ (f t) w ∩ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3))
          = {α t • v1 + β t • v2} := by
  obtain ⟨hv10, hv20, hnc⟩ := cf4_not_collinear_smul hcol
  have hindep : LinearIndependent ℝ ![v1, v2] := cf4_linearIndependent_pair hcol
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hwn
    norm_num at hwn
  -- 严格 Cauchy–Schwarz：|⟪v1,v2⟫| < ‖v1‖‖v2‖（线性无关 ⟹ 等号情形共线矛盾）
  have habs : |inner ℝ v1 v2| < ‖v1‖ * ‖v2‖ := by
    by_contra hcon
    push_neg at hcon
    have heq : |inner ℝ v1 v2| = ‖v1‖ * ‖v2‖ :=
      le_antisymm (abs_real_inner_le_norm v1 v2) hcon
    rcases (abs_eq (show (0:ℝ) ≤ ‖v1‖ * ‖v2‖ by positivity)).1 heq with hsgn | hsgn
    · have h2 : ‖v2‖ • v1 = ‖v1‖ • v2 :=
        (inner_eq_norm_mul_iff_real (x := v1) (y := v2)).1 hsgn
      have h3 := congrArg (fun z : V3 => (‖v1‖⁻¹ : ℝ) • z) h2
      rw [inv_smul_smul₀ (ne_of_gt (norm_pos_iff.2 hv10)), smul_smul] at h3
      exact hnc (‖v1‖⁻¹ * ‖v2‖) h3.symm
    · have h2' : ‖-v2‖ • v1 = ‖v1‖ • (-v2) :=
        (inner_eq_norm_mul_iff_real (x := v1) (y := -v2)).1 (by
          rw [inner_neg_right, norm_neg, hsgn]
          ring)
      rw [norm_neg] at h2'
      have h3 := congrArg (fun z : V3 => (‖v1‖⁻¹ : ℝ) • z) h2'
      rw [inv_smul_smul₀ (ne_of_gt (norm_pos_iff.2 hv10)), smul_smul] at h3
      exact hnc (-(‖v1‖⁻¹ * ‖v2‖)) (by rw [neg_smul, h3, neg_neg])
  -- Gram 行列式 hG > 0
  obtain ⟨hG, hGpos, hGdef⟩ : ∃ hG : ℝ, 0 < hG ∧
      hG = inner ℝ v1 v1 * inner ℝ v2 v2 - inner ℝ v1 v2 * inner ℝ v1 v2 := by
    refine ⟨inner ℝ v1 v1 * inner ℝ v2 v2 - inner ℝ v1 v2 * inner ℝ v1 v2, ?_, rfl⟩
    have hsq : inner ℝ v1 v2 ^ 2 < ‖v1‖ ^ 2 * ‖v2‖ ^ 2 := by
      have hA : (0:ℝ) < ‖v1‖ * ‖v2‖ := by positivity
      have hnn : (0:ℝ) ≤ |inner ℝ v1 v2| := abs_nonneg _
      calc inner ℝ v1 v2 ^ 2
          = |inner ℝ v1 v2| ^ 2 := (sq_abs _).symm
        _ = |inner ℝ v1 v2| * |inner ℝ v1 v2| := by rw [sq]
        _ ≤ (‖v1‖ * ‖v2‖) * |inner ℝ v1 v2| :=
              mul_le_mul_of_nonneg_right (le_of_lt habs) hnn
        _ < (‖v1‖ * ‖v2‖) * (‖v1‖ * ‖v2‖) := mul_lt_mul_of_pos_left habs hA
        _ = ‖v1‖ ^ 2 * ‖v2‖ ^ 2 := by ring
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    linarith
  have hGne : hG ≠ 0 := ne_of_gt hGpos
  -- 平面 {⟪x,n⟫ = 0} 内点的显式 Cramer 表示
  have hrepr : ∀ x : V3, inner ℝ x n = 0 →
      ∃ α₀ β₀ : ℝ, x = α₀ • v1 + β₀ • v2 ∧
        α₀ * hG = inner ℝ x v1 * inner ℝ v2 v2 - inner ℝ x v2 * inner ℝ v1 v2 ∧
        β₀ * hG = inner ℝ v1 v1 * inner ℝ x v2 - inner ℝ v1 v2 * inner ℝ x v1 := by
    intro x hxn
    obtain ⟨a, b, hx⟩ := cf4_plane_repr (v2 := v1) (v4 := v2) hindep hn0 h1n h2n hxn
    have hd1 : inner ℝ x v1 = a * inner ℝ v1 v1 + b * inner ℝ v1 v2 := by
      rw [hx, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm v1 v2]
    have hd2 : inner ℝ x v2 = a * inner ℝ v1 v2 + b * inner ℝ v2 v2 := by
      rw [hx, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    refine ⟨a, b, hx, ?_, ?_⟩
    · rw [hGdef, hd1, hd2]
      ring
    · rw [hGdef, hd1, hd2]
      ring
  -- affineSpan {0,v1,v2} = span{v1,v2} 的双向刻画
  have hv1mem : v1 ∈ insert (0:V3) ({v1, v2} : Set V3) :=
    Set.mem_insert_of_mem _ (Set.mem_insert v1 ({v2} : Set V3))
  have hvspeq : vectorSpan ℝ (insert (0:V3) ({v1, v2} : Set V3))
      = Submodule.span ℝ ((fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3))) :=
    vectorSpan_eq_span_vsub_set_left ℝ hv1mem
  have hspan_le : Submodule.span ℝ ({v1, v2} : Set V3) ≤ Submodule.span ℝ
      ((fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3))) := by
    rw [Submodule.span_le]
    intro w2 hw2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw2
    rcases hw2 with hw2' | hw2'
    · rw [hw2']
      exact Submodule.subset_span ⟨(0:V3), by simp,
        by show v1 - 0 = v1; rw [sub_zero]⟩
    · rw [hw2']
      have hv2eq : (v2:V3) = (v1 -ᵥ (0:V3)) - (v1 -ᵥ v2) := by
        show v2 = v1 - 0 - (v1 - v2)
        rw [sub_zero, sub_sub_cancel]
      rw [hv2eq]
      exact Submodule.sub_mem _
        (Submodule.subset_span ⟨(0:V3), by simp, rfl⟩)
        (Submodule.subset_span ⟨v2, by simp, rfl⟩)
  have himg_sub : ∀ w2 ∈ (fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3)),
      w2 ∈ Submodule.span ℝ ({v1, v2} : Set V3) := by
    rintro w2 ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy' | hy' | hy'
    · rw [hy']
      show v1 - (0:V3) ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      rw [sub_zero]
      exact Submodule.subset_span (by simp)
    · rw [hy']
      show v1 - v1 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      rw [sub_self]
      exact Submodule.zero_mem _
    · rw [hy']
      show v1 - v2 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      exact Submodule.mem_span_pair.2 ⟨1, -1, by module⟩
  have haff_sub : ∀ z : V3, z ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) →
      z ∈ Submodule.span ℝ ({v1, v2} : Set V3) := by
    intro z hz
    rw [mem_affineSpan_iff_exists] at hz
    obtain ⟨p₁, hp₁, v2', hv2', rfl⟩ := hz
    rw [hvspeq] at hv2'
    have hv' : v2' ∈ Submodule.span ℝ ({v1, v2} : Set V3) := by
      have hle : Submodule.span ℝ
          ((fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3)))
          ≤ Submodule.span ℝ ({v1, v2} : Set V3) := Submodule.span_le.2 himg_sub
      exact hle hv2'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp₁
    rcases hp₁ with hp₁' | hp₁' | hp₁'
    · rw [hp₁']
      show v2' + (0:V3) ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      rw [add_zero]
      exact hv'
    · rw [hp₁']
      show v2' + v1 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      exact Submodule.add_mem _ hv' (Submodule.subset_span (by simp))
    · rw [hp₁']
      show v2' + v2 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      exact Submodule.add_mem _ hv' (Submodule.subset_span (by simp))
  have haff_sup : ∀ z : V3, z ∈ Submodule.span ℝ ({v1, v2} : Set V3) →
      z ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) := by
    intro z hz
    rw [mem_affineSpan_iff_exists]
    refine ⟨(0:V3), by simp, z, ?_, ?_⟩
    · rw [hvspeq]
      exact hspan_le hz
    · show z = z + (0:V3)
      rw [add_zero]
  -- α β 的显式 Cramer 公式（连续性归约到 ContinuousOn 四则）
  have hfc : ContinuousOn (fun t => inner ℝ (f t) n) (Set.Icc 0 t1) :=
    hf.inner continuous_const.continuousOn
  have hfv1 : ContinuousOn (fun t => inner ℝ (f t) v1) (Set.Icc 0 t1) :=
    hf.inner continuous_const.continuousOn
  have hfv2 : ContinuousOn (fun t => inner ℝ (f t) v2) (Set.Icc 0 t1) :=
    hf.inner continuous_const.continuousOn
  have hs : ContinuousOn (fun t => -inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
      (Set.Icc 0 t1) :=
    ContinuousOn.div hfc.neg (continuous_const.continuousOn.sub hfc) (fun t ht =>
      ne_of_gt (by linarith [hfn t ht]))
  have hA1 : ContinuousOn (fun t => inner ℝ (f t) v1
      + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
        * (inner ℝ w v1 - inner ℝ (f t) v1)) (Set.Icc 0 t1) :=
    hfv1.add (hs.mul (continuous_const.continuousOn.sub hfv1))
  have hA2 : ContinuousOn (fun t => inner ℝ (f t) v2
      + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
        * (inner ℝ w v2 - inner ℝ (f t) v2)) (Set.Icc 0 t1) :=
    hfv2.add (hs.mul (continuous_const.continuousOn.sub hfv2))
  refine ⟨fun t => ((inner ℝ (f t) v1
        + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
          * (inner ℝ w v1 - inner ℝ (f t) v1)) * inner ℝ v2 v2
      - (inner ℝ (f t) v2
        + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
          * (inner ℝ w v2 - inner ℝ (f t) v2)) * inner ℝ v1 v2) / hG,
    fun t => (inner ℝ v1 v1
        * (inner ℝ (f t) v2 + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v2 - inner ℝ (f t) v2))
      - inner ℝ v1 v2 * (inner ℝ (f t) v1
        + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
          * (inner ℝ w v1 - inner ℝ (f t) v1))) / hG,
    ⟨ContinuousOn.div ((hA1.mul continuous_const.continuousOn).sub
        (hA2.mul continuous_const.continuousOn)) continuous_const.continuousOn
        (fun _ _ => hGne),
      ContinuousOn.div ((continuous_const.continuousOn.mul hA2).sub
        (continuous_const.continuousOn.mul hA1)) continuous_const.continuousOn
        (fun _ _ => hGne)⟩,
    ?_⟩
  intro t ht
  have hD : (0:ℝ) < inner ℝ w n - inner ℝ (f t) n := by linarith [hfn t ht]
  have hDne : inner ℝ w n - inner ℝ (f t) n ≠ 0 := ne_of_gt hD
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = -inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n) := ⟨_, rfl⟩
  have hs01 : 0 ≤ s ∧ s ≤ 1 := by
    rw [hs]
    constructor
    · have h0 := hfn t ht
      exact div_nonneg (by linarith) hD.le
    · rw [div_le_iff₀ hD]
      linarith
  -- 交点 x = (1-s)•f t + s•w 落在平面 ⟪·,n⟫ = 0 内
  have hxn : inner ℝ ((1 - s) • f t + s • w) n = 0 := by
    rw [hs, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    field_simp
    all_goals { ring }
  obtain ⟨α₀, β₀, hxpt, hα, hβ⟩ := hrepr ((1 - s) • f t + s • w) hxn
  -- ⟪x,vᵢ⟫ 的展开与 α₀ β₀ = 显式 Cramer 公式的衔接
  have hv1x : inner ℝ ((1 - s) • f t + s • w) v1
      = inner ℝ (f t) v1 + s * (inner ℝ w v1 - inner ℝ (f t) v1) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hv2x : inner ℝ ((1 - s) • f t + s • w) v2
      = inner ℝ (f t) v2 + s * (inner ℝ w v2 - inner ℝ (f t) v2) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hxat : (1 - s) • f t + s • w
      = (((inner ℝ (f t) v1
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v1 - inner ℝ (f t) v1)) * inner ℝ v2 v2
        - (inner ℝ (f t) v2
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v2 - inner ℝ (f t) v2)) * inner ℝ v1 v2) / hG) • v1
        + ((inner ℝ v1 v1
          * (inner ℝ (f t) v2 + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
              * (inner ℝ w v2 - inner ℝ (f t) v2))
        - inner ℝ v1 v2 * (inner ℝ (f t) v1
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v1 - inner ℝ (f t) v1))) / hG) • v2 := by
    rw [hxpt]
    have e1 : ((inner ℝ (f t) v1
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v1 - inner ℝ (f t) v1)) * inner ℝ v2 v2
        - (inner ℝ (f t) v2
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v2 - inner ℝ (f t) v2)) * inner ℝ v1 v2) / hG = α₀ := by
      rw [← hs, ← hv1x, ← hv2x, ← hα]
      field_simp
    have e2 : (inner ℝ v1 v1
          * (inner ℝ (f t) v2 + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
              * (inner ℝ w v2 - inner ℝ (f t) v2))
        - inner ℝ v1 v2 * (inner ℝ (f t) v1
          + (-inner ℝ (f t) n / (inner ℝ w n - inner ℝ (f t) n))
            * (inner ℝ w v1 - inner ℝ (f t) v1))) / hG = β₀ := by
      rw [← hs, ← hv1x, ← hv2x, ← hβ]
      field_simp
    rw [e1, e2]
  -- 交唯一性：z ∈ segment ∩ 平面 ⟹ z = 交点
  ext z
  constructor
  · rintro ⟨hseg, haff⟩
    obtain ⟨σ, τ, hσ, hτ, hστ, hz⟩ := hseg
    have hzn : inner ℝ z n = 0 := by
      have hzsp := haff_sub z haff
      obtain ⟨a, b, hzab⟩ := Submodule.mem_span_pair.1 hzsp
      rw [← hzab, inner_add_left, real_inner_smul_left, real_inner_smul_left, h1n, h2n]
      ring
    have hzinn : inner ℝ z n
        = inner ℝ (f t) n + τ * (inner ℝ w n - inner ℝ (f t) n) := by
      rw [← hz, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have hsc : σ = 1 - τ := by linarith
      rw [hsc]
      ring
    have hτs : τ = s := by
      rw [hs, eq_div_iff hDne]
      have h2 : τ * (inner ℝ w n - inner ℝ (f t) n)
          = -inner ℝ (f t) n := by linarith [hzinn, hzn]
      exact h2
    have hσs : σ = 1 - s := by linarith
    rw [← hz, hτs, hσs]
    exact hxat
  · rintro hz
    refine ⟨⟨1 - s, s, by linarith, hs01.1, by ring, ?_⟩, ?_⟩
    · rw [hz]
      exact hxat
    · rw [hz]
      exact haff_sup _ (Submodule.mem_span_pair.2 ⟨_, _, rfl⟩)

/-! ### 6.5 主石上游四件（CF-4d）：affineSpan 刻画 / IVT 打靶 / 穿锥判别两件

HOL 锚点：`in_aff_ge_cases_lemma`（CKQOWSA_4.hl:1928-2134）、
`segment_intersects_aff_ge_lemma`（:2138-2197）、IVT 打靶族
`continuous_lemma_inc`（:785）/`continuous_lemma_dec`（:967，经取负归约到 inc）。 -/

/-- `affineSpan ℝ {0,v1,v2}` 的显式二系数刻画（含退化情形；HOL `AFFINE_HULL_3`
的组合形。提取自 cf4_continuous_intersection_point 内联论证，正向 = haff_sub
路线（mem_affineSpan_iff_exists + vectorSpan 换 span），反向 = haff_sup 路线）。 -/
private theorem cf4_affSpan3_char (v1 v2 z : V3) :
    z ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) ↔
      ∃ a b : ℝ, z = a • v1 + b • v2 := by
  have hv1mem : v1 ∈ insert (0:V3) ({v1, v2} : Set V3) :=
    Set.mem_insert_of_mem _ (Set.mem_insert v1 ({v2} : Set V3))
  have hvspeq : vectorSpan ℝ (insert (0:V3) ({v1, v2} : Set V3))
      = Submodule.span ℝ ((fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3))) :=
    vectorSpan_eq_span_vsub_set_left ℝ hv1mem
  have hsp_le : Submodule.span ℝ ({v1, v2} : Set V3) ≤ Submodule.span ℝ
      ((fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3))) := by
    rw [Submodule.span_le]
    intro w2 hw2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw2
    rcases hw2 with hw2' | hw2'
    · rw [hw2']
      exact Submodule.subset_span ⟨(0:V3), by simp,
        by show v1 - 0 = v1; rw [sub_zero]⟩
    · rw [hw2']
      have hv2eq : (v2:V3) = (v1 -ᵥ (0:V3)) - (v1 -ᵥ v2) := by
        show v2 = v1 - 0 - (v1 - v2)
        rw [sub_zero, sub_sub_cancel]
      rw [hv2eq]
      exact Submodule.sub_mem _
        (Submodule.subset_span ⟨(0:V3), by simp, rfl⟩)
        (Submodule.subset_span ⟨v2, by simp, rfl⟩)
  have himg_le : ∀ w2 ∈ (fun y : V3 => v1 -ᵥ y) '' (insert (0:V3) ({v1, v2} : Set V3)),
      w2 ∈ Submodule.span ℝ ({v1, v2} : Set V3) := by
    rintro w2 ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy' | hy' | hy'
    · rw [hy']
      show v1 - (0:V3) ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      rw [sub_zero]
      exact Submodule.subset_span (by simp)
    · rw [hy']
      show v1 - v1 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      rw [sub_self]
      exact Submodule.zero_mem _
    · rw [hy']
      show v1 - v2 ∈ Submodule.span ℝ ({v1, v2} : Set V3)
      exact Submodule.mem_span_pair.2 ⟨1, -1, by module⟩
  constructor
  · intro hz
    rw [mem_affineSpan_iff_exists] at hz
    obtain ⟨p₁, hp₁, z', hz'mem, hz4⟩ := hz
    rw [hvspeq] at hz'mem
    have hz'span : z' ∈ Submodule.span ℝ ({v1, v2} : Set V3) :=
      Submodule.span_le.2 himg_le hz'mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp₁
    obtain ⟨a, b, hz'eq⟩ := Submodule.mem_span_pair.1 hz'span
    rw [hz4]
    rcases hp₁ with rfl | rfl | rfl
    · exact ⟨a, b, by rw [vadd_eq_add, add_zero, hz'eq]⟩
    · refine ⟨a + 1, b, ?_⟩
      rw [vadd_eq_add, ← hz'eq]
      module
    · refine ⟨a, b + 1, ?_⟩
      rw [vadd_eq_add, ← hz'eq]
      module
  · rintro ⟨a, b, rfl⟩
    rw [mem_affineSpan_iff_exists]
    refine ⟨(0:V3), by simp, a • v1 + b • v2, ?_, by rw [vadd_eq_add, add_zero]⟩
    rw [hvspeq]
    exact hsp_le (Submodule.mem_span_pair.2 ⟨a, b, rfl⟩)

/-- 平面 {⟪x,n⟫ = 0} 中的点落在 affineSpan {0,v1,v2} 内
（`cf4_plane_repr` + `cf4_affSpan3_char` 反向；HOL `affine_hull_3_plane`
的 ⊇ 单侧，主石 f 0 / w 入平面刻画用）。 -/
private theorem cf4_mem_affSpan3_of_inner_eq {v1 v2 n x : V3}
    (hindep : LinearIndependent ℝ ![v1, v2]) (hn : n ≠ 0)
    (h1n : inner ℝ v1 n = 0) (h2n : inner ℝ v2 n = 0)
    (hxn : inner ℝ x n = 0) :
    x ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) := by
  obtain ⟨a, b, hx⟩ := cf4_plane_repr (v2 := v1) (v4 := v2) hindep hn h1n h2n hxn
  exact (cf4_affSpan3_char v1 v2 x).2 ⟨a, b, hx⟩

/-- HOL `continuous_lemma_inc`（CKQOWSA_4.hl:785-965）：首次达位——g 连续于 [0,t1]、
g 0 ≤ c ≤ g t1 ⟹ 存在首个 x：g x = c 且 [0,x) 上严格小于 c。
途径：S := [0,t1] ∩ g⁻¹[c,∞)（闭，`ContinuousOn.preimage_isClosed_of_isClosed`），
x := sInf S（`IsClosed.isLeast_csInf` 给 ∈ S + 下界）；g x > c 由左侧连续点
（邻域取 Ioi((g x+c)/2)）与 sInf 邻近点矛盾，g x < c 由右侧 Iio c 邻域 +
`csInf_lt_iff` 取 S 邻近点矛盾。 -/
private theorem cf4_ivt_first_hit (g : ℝ → ℝ) (c t1 : ℝ) (ht1 : 0 ≤ t1)
    (hgc : ContinuousOn g (Set.Icc 0 t1)) (h0 : g 0 ≤ c) (h1 : c ≤ g t1) :
    ∃ x, 0 ≤ x ∧ x ≤ t1 ∧ g x = c ∧ ∀ t ∈ Set.Ico 0 x, g t < c := by
  obtain ⟨S, hScc, hSmem⟩ : ∃ S : Set ℝ, IsClosed S ∧
      ∀ t, t ∈ S ↔ 0 ≤ t ∧ t ≤ t1 ∧ c ≤ g t :=
    ⟨Set.Icc 0 t1 ∩ g ⁻¹' (Set.Ici c),
      hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici,
      fun t => by
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_Ici]
        tauto⟩
  have ht1mem : t1 ∈ S := (hSmem t1).2 ⟨ht1, le_refl t1, h1⟩
  have hne : S.Nonempty := ⟨t1, ht1mem⟩
  have hbd : BddBelow S := ⟨0, fun y hy => ((hSmem y).1 hy).1⟩
  obtain ⟨xmem, xlb⟩ := hScc.isLeast_csInf hne hbd
  have hxlb : ∀ y ∈ S, sInf S ≤ y := fun y hy => mem_lowerBounds.1 xlb y hy
  have h3 := (hSmem _).1 xmem
  refine ⟨sInf S, h3.1, h3.2.1, ?_, ?_⟩
  · -- g (sInf S) = c：∈ S 给 c ≤ g x（下侧），左邻域点夹逼给 g x ≤ c
    rcases eq_or_lt_of_le h3.2.2 with heq | hgt
    · exact heq.symm
    · -- g x > c：x = 0 与 h0 矛盾；x > 0 取左侧点 y ∈ S 且 g y > c，与下界矛盾
      exfalso
      rcases eq_or_lt_of_le h3.1 with hx0 | hx0p
      · rw [← hx0] at hgt
        exact absurd hgt (not_lt.2 h0)
      · obtain ⟨U, hUmem, hU⟩ := Filter.eventually_iff_exists_mem.1
          (Filter.tendsto_iff_eventually.1 (hgc (sInf S) (Set.mem_Icc.2 ⟨h3.1, h3.2.1⟩))
            ((Ioi_mem_nhds (by linarith : (g (sInf S) + c) / 2 < g (sInf S)) :
              ∀ᶠ y in nhds (g (sInf S)),
                y ∈ Set.Ioi ((g (sInf S) + c) / 2))))
        obtain ⟨W, hWx, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hUmem
        obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hWx
        have hmine : (0:ℝ) < min (δ / 2) (sInf S / 2) :=
          lt_min (by linarith) (by linarith)
        have hminle : min (δ / 2) (sInf S / 2) ≤ sInf S :=
          le_trans (min_le_right _ _) (by linarith)
        have hy0 : (0:ℝ) ≤ sInf S - min (δ / 2) (sInf S / 2) := by linarith
        have hyx : sInf S - min (δ / 2) (sInf S / 2) < sInf S := by linarith
        have hydist : dist (sInf S - min (δ / 2) (sInf S / 2)) (sInf S) < δ := by
          rw [Real.dist_eq, show sInf S - min (δ / 2) (sInf S / 2) - sInf S
            = -(min (δ / 2) (sInf S / 2)) by ring, abs_neg, abs_of_nonneg (le_of_lt hmine)]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hyI : sInf S - min (δ / 2) (sInf S / 2) ∈ Set.Icc 0 t1 :=
          ⟨hy0, le_trans (le_of_lt hyx) h3.2.1⟩
        have hyc : c < g (sInf S - min (δ / 2) (sInf S / 2)) := by
          have h1' := hU _ (hWsub ⟨hball hydist, hyI⟩)
          linarith
        have hyS : sInf S - min (δ / 2) (sInf S / 2) ∈ S :=
          (hSmem _).2 ⟨hy0, le_trans (le_of_lt hyx) h3.2.1, le_of_lt hyc⟩
        exact absurd hyx (not_lt.2 (hxlb (sInf S - min (δ / 2) (sInf S / 2)) hyS))
  · intro t ht
    by_contra hcon
    push_neg at hcon
    exact absurd ht.2 (not_lt.2 (hxlb t ((hSmem t).2 ⟨ht.1, le_trans (le_of_lt ht.2) h3.2.1,
      hcon⟩)))

/-- HOL `continuous_lemma_dec`（CKQOWSA_4.hl:967-1010）：反向首次达位
（HOL 由 `\t. --f t` 归约到 inc，本处同法）。 -/
private theorem cf4_ivt_first_dec (g : ℝ → ℝ) (c t1 : ℝ) (ht1 : 0 ≤ t1)
    (hgc : ContinuousOn g (Set.Icc 0 t1)) (h0 : c ≤ g 0) (h1 : g t1 ≤ c) :
    ∃ x, 0 ≤ x ∧ x ≤ t1 ∧ g x = c ∧ ∀ t ∈ Set.Ico 0 x, c < g t := by
  obtain ⟨x, hx0, hxt, hxc, hlt⟩ :=
    cf4_ivt_first_hit (fun t => -g t) (-c) t1 ht1 (hgc.neg)
      (neg_le_neg h0) (neg_le_neg h1)
  have hxc' : -g x = -c := hxc
  have hlt' : ∀ t ∈ Set.Ico 0 x, -g t < -c := hlt
  refine ⟨x, hx0, hxt, by linarith, fun t ht => by linarith [hlt' t ht]⟩

/-- HOL `in_aff_ge_cases_lemma`（CKQOWSA_4.hl:1928-2134）：穿锥判别之一。
v ∈ affineSpan{0,v1,v2}、w ∈ cone{v1,v2}、0 ∉ segment[v,w]、非共线
⟹ v ∈ cone ∨ v1 ∈ cone{v,w} ∨ v2 ∈ cone{v,w}。
路线（同 HOL）：v 的二系数分解含负系数 + w 的非负系数分解；t3 = 0 / t4 = 0
退化分支直取端点；主分支 Cramer 消元
v2 = (t3·v − t1·w)/d、v1 = (t4·v − t2·w)/(−d)（d := t2·t3 − t1·t4 ≠ 0，
d = 0 时退到 zero_not_between 的异侧射线不相交），按 t1 t2 d 符号四分。 -/
private theorem cf4_in_aff_ge_cases {v1 v2 v w : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hnb : (0:V3) ∉ segment ℝ v w)
    (hv : v ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hw : w ∈ affGe {0} ({v1, v2} : Set V3)) :
    v ∈ affGe {0} ({v1, v2} : Set V3) ∨
      v1 ∈ affGe {0} ({v, w} : Set V3) ∨
      v2 ∈ affGe {0} ({v, w} : Set V3) := by
  obtain ⟨hv10, hv20, hnc⟩ := cf4_not_collinear_smul hcol
  have hv12 : v1 ≠ v2 := fun he => hnc 1 (by rw [he, one_smul])
  obtain ⟨hv0, hw0, hznb⟩ := cf4_zero_not_between hnb
  by_cases hvcone : v ∈ affGe {0} ({v1, v2} : Set V3)
  · exact Or.inl hvcone
  · obtain ⟨t1, t2, hveq⟩ := (cf4_affSpan3_char v1 v2 v).1 hv
    have hneg : t1 < 0 ∨ t2 < 0 := by
      by_contra hcon
      push_neg at hcon
      exact hvcone ((affGe_0_2_char hv10 hv20 hv12 _).2 ⟨t1, t2, hcon.1, hcon.2, hveq⟩)
    obtain ⟨t3, t4, ht3, ht4, hw'⟩ := (affGe_0_2_char hv10 hv20 hv12 w).1 hw
    have hvne : v ≠ 0 := by
      intro he
      refine hvcone ?_
      rw [he]
      exact (affGe_0_2_char hv10 hv20 hv12 (0:V3)).2 ⟨0, 0, le_refl _, le_refl _, by simp⟩
    have hvw : v ≠ w := by
      intro he
      refine hvcone ?_
      rw [he]
      exact hw
    rcases eq_or_lt_of_le ht3 with ht30 | ht3p
    · -- t3 = 0：w = t4•v2，v2 = t4⁻¹•w ∈ cone{v,w}（第三支）
      subst ht30
      have ht4p : 0 < t4 := by
        rcases lt_or_eq_of_le ht4 with h | h
        · exact h
        · exfalso
          refine hw0 ?_
          rw [hw', zero_smul, zero_add, ← h, zero_smul]
      refine Or.inr (Or.inr ((affGe_0_2_char hvne hw0 hvw v2).2
        ⟨0, t4⁻¹, by norm_num, by positivity, ?_⟩))
      rw [zero_smul, zero_add]
      have hwt : t4 • v2 = w := by rw [hw', zero_smul, zero_add]
      rw [← hwt, inv_smul_smul₀ ht4p.ne']
    rcases eq_or_lt_of_le ht4 with ht40 | ht4p
    · -- t4 = 0：w = t3•v1，v1 = t3⁻¹•w ∈ cone{v,w}（第二支）
      subst ht40
      refine Or.inr (Or.inl ((affGe_0_2_char hvne hw0 hvw v1).2
        ⟨0, t3⁻¹, by norm_num, by positivity, ?_⟩))
      rw [zero_smul, zero_add]
      have hwt : t3 • v1 = w := by rw [hw', zero_smul, add_zero]
      rw [← hwt, inv_smul_smul₀ ht3p.ne']
    -- 主分支：t3, t4 > 0
    have key1 : t3 • v - t1 • w = (t2 * t3 - t1 * t4) • v2 := by
      rw [hveq, hw']
      module
    have key2 : t2 • w - t4 • v = (t2 * t3 - t1 * t4) • v1 := by
      rw [hveq, hw']
      module
    have key3 : t4 • v - t2 • w = (t1 * t4 - t2 * t3) • v1 := by
      rw [hveq, hw']
      module
    have hdne : t2 * t3 - t1 * t4 ≠ 0 := by
      intro hh0
      rcases hneg with h1n | h2n
      · exact hznb t1 t3 h1n ht3p (sub_eq_zero.mp (by rw [key1, hh0, zero_smul])).symm
      · exact hznb t2 t4 h2n ht4p (sub_eq_zero.mp (by rw [key2, hh0, zero_smul]))
    -- 主分支按 d := t2t3 − t1t4 的符号三分：d = 0 已排除；d > 0 强制 t1 ≤ 0（v2 支），
    -- d < 0 强制 t2 ≤ 0（v1 支）（若反向符号则 hneg 矛盾）。
    rcases lt_trichotomy 0 (t2 * t3 - t1 * t4) with hdp | hdpz | hdpn
    · -- d > 0：t1 ≤ 0：v2 = (t3/d)•v + (−t1/d)•w ∈ cone{v,w}
      have h1n0 : t1 ≤ 0 := by
        rcases hneg with h1n | h2n
        · exact le_of_lt h1n
        · have h2' : t2 * t3 < 0 := mul_neg_of_neg_of_pos h2n ht3p
          have hd0 : t2 * t3 - t1 * t4 = t2 * t3 + -(t1 * t4) := by ring
          have h4' : t1 * t4 < 0 := by linarith
          rcases lt_trichotomy 0 t1 with k1 | k2 | k3
          · exfalso
            linarith [mul_pos k1 ht4p]
          · exfalso
            rw [← k2, zero_mul] at h4'
            linarith
          · exact le_of_lt k3
      refine Or.inr (Or.inr ((affGe_0_2_char hvne hw0 hvw v2).2
        ⟨(t2 * t3 - t1 * t4)⁻¹ * t3, (t2 * t3 - t1 * t4)⁻¹ * -t1,
          mul_nonneg (inv_nonneg.2 (le_of_lt hdp)) ht3,
          mul_nonneg (inv_nonneg.2 (le_of_lt hdp)) (neg_nonneg.2 h1n0), ?_⟩))
      have hinv : (t2 * t3 - t1 * t4)⁻¹ • (t3 • v - t1 • w) = v2 := by
        rw [key1, inv_smul_smul₀ hdne]
      rw [← hinv, smul_sub, smul_smul, smul_smul]
      module
    · -- d = 0：已排除
      exact absurd hdpz.symm hdne
    · -- d < 0：t2 ≤ 0：v1 = (t4/(−d))•v + (t2/(−d))•w ∈ cone{v,w}
      have h2n0 : t2 ≤ 0 := by
        rcases hneg with h1n | h2n
        · have h2' : (0:ℝ) < -t1 * t4 := mul_pos (neg_pos.2 h1n) ht4p
          have hb4 : -t1 * t4 = -(t1 * t4) := by ring
          have h3' : t2 * t3 < 0 := by linarith
          rcases lt_trichotomy 0 t2 with k1 | k2 | k3
          · exfalso
            linarith [mul_pos k1 ht3p]
          · exfalso
            rw [← k2, zero_mul] at h3'
            linarith
          · exact le_of_lt k3
        · exact le_of_lt h2n
      have hd2p : 0 < t1 * t4 - t2 * t3 := by
        have hh : t1 * t4 - t2 * t3 ≠ 0 := by
          intro hh0
          apply hdne
          linarith
        linarith [le_of_lt hdpn, hh]
      refine Or.inr (Or.inl ((affGe_0_2_char hvne hw0 hvw v1).2
        ⟨(t1 * t4 - t2 * t3)⁻¹ * t4, (t1 * t4 - t2 * t3)⁻¹ * -t2,
          mul_nonneg (inv_nonneg.2 (le_of_lt hd2p)) ht4,
          mul_nonneg (inv_nonneg.2 (le_of_lt hd2p)) (neg_nonneg.2 h2n0), ?_⟩))
      have hinv : (t1 * t4 - t2 * t3)⁻¹ • (t4 • v - t2 • w) = v1 := by
        rw [key3, inv_smul_smul₀ hd2p.ne']
      rw [← hinv, smul_sub, smul_smul, smul_smul]
      module

/-- HOL `segment_intersects_aff_ge_lemma`（CKQOWSA_4.hl:2138-2197）：穿锥判别之二。
v, w ∈ affineSpan{0,v1,v2}、0 ∉ segment[v,w]、segment[v,w] 穿锥
⟹ v ∈ cone ∨ v1 ∈ cone{v,w} ∨ v2 ∈ cone{v,w}。
路线（同 HOL）：取穿点 p ∈ segment[v,w] ∩ cone；v = w 或 u'（w 系数）= 0 时
p = v ∈ cone 直取第一支；否则对 (v,p) 用 `cf4_in_aff_ge_cases`
（segment[v,p] ⊆ segment[v,w] 保 0 ∉），锥单调 cone{v,p} ⊆ cone{v,w}
（p ∈ segment[v,w] ⊆ cone{v,w}，`cf4_cone_mono`）把两支迁到 {v,w}。 -/
private theorem cf4_segment_intersects_aff_ge {v1 v2 v w : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hnb : (0:V3) ∉ segment ℝ v w)
    (hv : v ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hw : w ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)))
    (hcross : (segment ℝ v w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) :
    v ∈ affGe {0} ({v1, v2} : Set V3) ∨
      v1 ∈ affGe {0} ({v, w} : Set V3) ∨
      v2 ∈ affGe {0} ({v, w} : Set V3) := by
  obtain ⟨hv0, hw0, -⟩ := cf4_zero_not_between hnb
  obtain ⟨p, hpsegm, hpcone⟩ := hcross
  obtain ⟨u, u', hu, hu', huu, hpeq⟩ := hpsegm
  rcases eq_or_ne v w with hvw0 | hvw
  · -- v = w：p = v ∈ cone
    refine Or.inl ?_
    have hvp : v = p := by rw [← hpeq, hvw0, ← add_smul, huu, one_smul]
    rw [hvp]
    exact hpcone
  · have hsub : segment ℝ v p ⊆ segment ℝ v w := by
      intro q hq
      obtain ⟨s, s', hs, hs', hss, hqeq⟩ := hq
      have hsum : s + s' * u + s' * u' = 1 := by
        rw [add_assoc, ← mul_add, huu, mul_one]
        exact hss
      refine ⟨s + s' * u, s' * u', by nlinarith, by nlinarith, hsum, ?_⟩
      rw [← hqeq, ← hpeq]
      module
    have hb0 : (0:V3) ∉ segment ℝ v p := fun h0 => hnb (hsub h0)
    obtain hd := cf4_in_aff_ge_cases hcol hb0 hv hpcone
    rcases eq_or_lt_of_le hu' with hu'0 | hu'p
    · -- u' = 0：p = v ∈ cone
      refine Or.inl ?_
      have hvp : v = p := by
        rw [← hpeq, ← hu'0, zero_smul, add_zero, (show u = 1 from by linarith), one_smul]
      rw [hvp]
      exact hpcone
    · -- 0 < u'：主分支
      have hpne : p ≠ 0 := by
        intro he
        refine hnb ?_
        rw [← he]
        exact ⟨u, u', hu, hu', huu, hpeq⟩
      have hvvp : v ≠ p := by
        intro he
        refine hvw ?_
        rw [he] at hpeq
        have h2 : u' • w = v - u • v := by
          rw [he]
          have h3 : u' • w + u • p = p := by
            rw [add_comm]
            exact hpeq
          exact eq_sub_of_add_eq h3
        have h5 : v - u • v = (1 - u) • v := by
          rw [sub_smul, one_smul]
        rw [h5, (show 1 - u = u' from by linarith)] at h2
        have h3 : u' • (w - v) = 0 := by
          rw [smul_sub, h2, sub_self]
        rcases smul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 hu'p.ne'
        · exact (sub_eq_zero.mp h4).symm
      have hvcone' : v ∈ affGe {0} ({v, w} : Set V3) :=
        (affGe_0_2_char hv0 hw0 hvw v).2 ⟨1, 0, by norm_num, by norm_num,
          by rw [one_smul, zero_smul, add_zero]⟩
      have hpcone' : p ∈ affGe {0} ({v, w} : Set V3) :=
        cf4_segment_mem_cone hv0 hw0 hvw ⟨u, u', hu, hu', huu, hpeq⟩
      have hmono : affGe {0} ({v, p} : Set V3) ⊆ affGe {0} ({v, w} : Set V3) :=
        cf4_cone_mono hv0 hw0 hvw hv0 hpne hvvp hvcone' hpcone'
      rcases hd with hd1 | hd2 | hd3
      · exact Or.inl hd1
      · exact Or.inr (Or.inl (hmono hd2))
      · exact Or.inr (Or.inr (hmono hd3))

/-- HOL `continuous_lemma_aff_ge`（CKQOWSA_4.hl:2204-2869，全章最大单件 665 行）：
穿越不变量在连续旋转族下的传递。CF-4d 闭合。
移植结构（同 HOL 逐段）：①全通则左支直接收；②法向量 n := ±(v1×v2) 取
f 0·n ≤ 0（HOL :2277）；③起点内积方程 (HOL :2301)；④三分类 w·n < 0 / = 0 / > 0
（HOL :2312/:2346/:2395）：< 0 时 f 0 = 交点 x := 0；= 0 时
`cf4_segment_intersects_aff_ge` 给 x := 0 的三支；> 0 时 IVT 打靶 r
（`cf4_ivt_first_hit` 作用于 ⟪f t,n⟫，HOL :2398-2482），再经
`cf4_continuous_intersection_point` 的 α β（HOL :2499-2605）+ `cf4_ivt_first_dec`
对 α/β 的首穿点 x（HOL :2609-2762），终局 a x = 0 ∨ b x = 0 给 v1/v2 入
cone{f x,w}（HOL :2800-2862）。 -/
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
          v2 ∈ affGe {0} ({f x, w} : Set V3))) := by
  -- §A 基本事实：v1 v2 非零异线；hfw 展开 0 ∉ segment[f t,w]
  obtain ⟨hv10, hv20, hnc⟩ := cf4_not_collinear_smul hcol
  have hv12 : v1 ≠ v2 := fun he => hnc 1 (by rw [he, one_smul])
  have hindep : LinearIndependent ℝ ![v1, v2] := cf4_linearIndependent_pair hcol
  obtain ⟨hf00, hw0, -⟩ := cf4_zero_not_between (hnb 0 (Set.mem_Icc.2 ⟨le_refl 0, hh⟩))
  have hfw : ∀ t ∈ Set.Icc 0 h, f t ≠ 0 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1 - u) • f t + u • w ≠ (0:V3) := by
    intro t ht
    obtain ⟨hft0, -, hznb⟩ := cf4_zero_not_between (hnb t ht)
    refine ⟨hft0, fun u hu1 hu2 heq => ?_⟩
    rcases eq_or_lt_of_le hu1 with hu0 | hu0p
    · rw [← hu0, sub_zero, one_smul, zero_smul, add_zero] at heq
      exact hft0 heq
    rcases eq_or_lt_of_le hu2 with hu10 | hu1p
    · rw [hu10, sub_self, zero_smul, one_smul, zero_add] at heq
      exact hw0 heq
    · exact hznb (-u) (1 - u) (by linarith) (by linarith)
        (((eq_neg_of_add_eq_zero_left heq).trans (neg_smul u w).symm).symm :
          (-u) • w = (1 - u) • f t)
  -- §B 主分叉
  by_cases hall : ∀ t ∈ Set.Icc 0 h,
      (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty
  · exact Or.inl hall
  · rw [not_forall] at hall
    obtain ⟨t1, ht1e⟩ := hall
    push_neg at ht1e
    obtain ⟨ht1I, ht1ne⟩ := ht1e
    -- 统一空交形态为 Nonempty 的否定
    have ht1nen : ¬ (segment ℝ (f t1) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty := by
      rintro ⟨x, hx⟩
      rw [ht1ne] at hx
      exact absurd hx (Set.mem_empty_iff_false x).mp
    -- §C 法向量 n := ±(v1 × v2)（f 0·n ≤ 0）
    have hcne : cf4Cross v1 v2 ≠ 0 := cf4Cross_ne_zero hcol
    have hv1c : inner ℝ v1 (cf4Cross v1 v2) = 0 := cf4Cross_dot_left v1 v2
    have hv2c : inner ℝ v2 (cf4Cross v1 v2) = 0 := cf4Cross_dot_right v1 v2
    obtain ⟨n, hn0, hv1n, hv2n, hf0n⟩ :
        ∃ n : V3, n ≠ 0 ∧ inner ℝ v1 n = 0 ∧ inner ℝ v2 n = 0 ∧ inner ℝ (f 0) n ≤ 0 := by
      rcases le_or_gt (inner ℝ (f 0) (cf4Cross v1 v2)) 0 with hsign | hsign
      · exact ⟨cf4Cross v1 v2, hcne, hv1c, hv2c, hsign⟩
      · refine ⟨-cf4Cross v1 v2, by simpa using hcne, by simp [hv1c], by simp [hv2c],
          by rw [inner_neg_right]; linarith⟩
    -- §D 锥 ⟹ 内积零；§E 起点内积方程
    have hcone_n : ∀ p ∈ affGe {0} ({v1, v2} : Set V3), inner ℝ p n = 0 := by
      intro p hp
      obtain ⟨a, b, ha, hb, hpab⟩ := (affGe_0_2_char hv10 hv20 hv12 p).1 hp
      rw [hpab, inner_add_left, real_inner_smul_left, real_inner_smul_left, hv1n, hv2n]
      ring
    obtain ⟨p0, hp0seg, hp0cone⟩ := hstart
    obtain ⟨u0, u0', hu00, hu00', hu001, hp0eq⟩ := hp0seg
    have hDu0 : u0 * inner ℝ (f 0) n + u0' * inner ℝ w n = 0 := by
      have h1 : inner ℝ p0 n = 0 := hcone_n p0 hp0cone
      rw [← hp0eq, inner_add_left, real_inner_smul_left, real_inner_smul_left] at h1
      exact h1
    -- §F/G/H 按 w·n 三分类
    rcases lt_trichotomy (inner ℝ w n) 0 with hwn | hwn | hwn
    · -- w·n < 0：u0' = 0 ⟹ p0 = f 0 ∈ cone，x := 0
      have hu0z : u0' = 0 := by
        rcases eq_or_lt_of_le hu00' with h | h
        · exact h.symm
        · exfalso
          have h1 : u0 * inner ℝ (f 0) n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu00 hf0n
          have h2 : u0' * inner ℝ w n < 0 := mul_neg_of_pos_of_neg h hwn
          linarith
      have hp0f0 : p0 = f 0 := by
        rw [← hp0eq, hu0z, zero_smul, add_zero, (show u0 = 1 from by linarith), one_smul]
      refine Or.inr ⟨0, le_refl 0, hh, ?_, Or.inl ?_⟩
      · intro t ht
        rw [le_antisymm ht.2 ht.1]
        exact ⟨p0, ⟨u0, u0', hu00, hu00', hu001, hp0eq⟩, hp0cone⟩
      · rw [← hp0f0]
        exact hp0cone
    · -- w·n = 0：f 0·n = 0，两件入平面，cf4_segment_intersects_aff_ge 收
      by_cases hwcone : w ∈ affGe {0} ({v1, v2} : Set V3)
      · exact absurd (⟨w, ⟨⟨(0:ℝ), 1, by norm_num, by norm_num, by norm_num,
          by rw [zero_smul, zero_add, one_smul]⟩, hwcone⟩⟩ :
          (segment ℝ (f t1) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) ht1nen
      have hu0ne : u0 ≠ 0 := by
        intro hz
        refine hwcone ?_
        have hpw : p0 = w := by
          rw [← hp0eq, hz, zero_smul, zero_add, (show u0' = 1 from by linarith),
            one_smul]
        rw [← hpw]
        exact hp0cone
      have hf0n0 : inner ℝ (f 0) n = 0 := by
        have h2 := hDu0
        rw [hwn, mul_zero, add_zero] at h2
        exact (mul_eq_zero.1 h2).resolve_left hu0ne
      have hf0aff : f 0 ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) :=
        cf4_mem_affSpan3_of_inner_eq hindep hn0 hv1n hv2n hf0n0
      have hwaff : w ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) :=
        cf4_mem_affSpan3_of_inner_eq hindep hn0 hv1n hv2n hwn
      have hdisj := cf4_segment_intersects_aff_ge hcol
        (hnb 0 (Set.mem_Icc.2 ⟨le_refl 0, hh⟩)) hf0aff hwaff
        ⟨p0, ⟨u0, u0', hu00, hu00', hu001, hp0eq⟩, hp0cone⟩
      refine Or.inr ⟨0, le_refl 0, hh, ?_, hdisj⟩
      · intro t ht
        rw [le_antisymm ht.2 ht.1]
        exact ⟨p0, ⟨u0, u0', hu00, hu00', hu001, hp0eq⟩, hp0cone⟩
    · -- w·n > 0：IVT 打靶 r（HOL :2398 SUBGOAL）
      have hgfun : ContinuousOn (fun t => inner ℝ (f t) n) (Set.Icc 0 h) :=
        hf.inner continuous_const.continuousOn
      obtain ⟨r, hr0, hrh, hrle, hrdisj⟩ :
          ∃ r, 0 ≤ r ∧ r ≤ h ∧ (∀ t ∈ Set.Icc 0 r, inner ℝ (f t) n ≤ 0) ∧
            (((∀ t ∈ Set.Icc 0 r,
                  (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty) ∧
                f r ∈ affGe {0} ({v1, v2} : Set V3)) ∨
              (∃ t1 ∈ Set.Icc 0 r,
                segment ℝ (f t1) w ∩ affGe {0} ({v1, v2} : Set V3) = ∅)) := by
        by_cases hle : ∀ t ∈ Set.Icc 0 h, inner ℝ (f t) n ≤ 0
        · exact ⟨h, hh, le_refl h, hle, Or.inr ⟨t1, ht1I, ht1ne⟩⟩
        · push_neg at hle
          obtain ⟨tt, httI, htt⟩ := hle
          obtain ⟨x, hx0, hxt, hxc, hlt⟩ :=
            cf4_ivt_first_hit (fun t => inner ℝ (f t) n) 0 tt httI.1
              (hgfun.mono (Set.Icc_subset_Icc le_rfl httI.2)) hf0n htt.le
          have hxc' : inner ℝ (f x) n = 0 := hxc
          have hlt' : ∀ t ∈ Set.Ico 0 x, inner ℝ (f t) n < 0 := hlt
          refine ⟨x, hx0, le_trans hxt httI.2, ?_, ?_⟩
          · intro t ht
            rcases eq_or_lt_of_le ht.2 with htx | htx
            · rw [htx]
              exact hxc'.le
            · exact le_of_lt (hlt' t ⟨ht.1, htx⟩)
          · by_cases hx1 : ∀ t ∈ Set.Icc 0 x,
                (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty
            · -- f x ∈ cone：x 处交点参数 ub = 0
              refine Or.inl ⟨hx1, ?_⟩
              obtain ⟨p', hp'seg, hp'cone⟩ := hx1 x ⟨hx0, le_refl x⟩
              obtain ⟨ua, ub, hua, hub, huab, hp'eq⟩ := hp'seg
              have hub0 : ub = 0 := by
                have h1 : inner ℝ p' n = 0 := hcone_n p' hp'cone
                rw [← hp'eq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
                  hxc', mul_zero, zero_add] at h1
                rcases mul_eq_zero.1 h1 with h | h
                · exact h
                · exact absurd h (ne_of_gt hwn)
              have hp'x : p' = f x := by
                rw [← hp'eq, hub0, zero_smul, add_zero, (show ua = 1 from by linarith),
                  one_smul]
              rw [← hp'x]
              exact hp'cone
            · push_neg at hx1
              obtain ⟨t1', ht1'I, ht1'e⟩ := hx1
              exact Or.inr ⟨t1', ht1'I, ht1'e⟩
      -- §I 终局装配（HOL :2486-2862）
      rcases hrdisj with ⟨hrempty, hrcone⟩ | ⟨t1', ht1'I, ht1ne'⟩
      · exact Or.inr ⟨r, hr0, hrh, hrempty, Or.inl hrcone⟩
      · -- 主案例：continuous_intersection_point 的 α β + IVT 首穿
        obtain ⟨α, β, habcont, habpoint⟩ :=
          cf4_continuous_intersection_point f r hr0 hcol
            (hf.mono (Set.Icc_subset_Icc le_rfl hrh)) hv1n hv2n hwn hrle
        have ha1 : ∀ t ∈ Set.Icc 0 r,
            α t • v1 + β t • v2 ∈ segment ℝ (f t) w ∩
              affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) := by
          intro t ht
          rw [habpoint t ht]
          exact Set.mem_singleton _
        have ha2 : ∀ t ∈ Set.Icc 0 r, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
            α t • v1 + β t • v2 = (1 - u) • f t + u • w := by
          intro t ht
          obtain ⟨c1, c2, hc1, hc2, hc12, hceq⟩ := (ha1 t ht).1
          refine ⟨c2, hc2, by linarith, ?_⟩
          rw [← hceq, (show c1 = 1 - c2 from by linarith)]
        have ha3 : ∀ t ∈ Set.Icc 0 r, 0 ≤ α t → 0 ≤ β t →
            (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty := by
          intro t ht' ha hb
          exact ⟨α t • v1 + β t • v2, (ha1 t ht').1,
            (affGe_0_2_char hv10 hv20 hv12 _).2 ⟨α t, β t, ha, hb, rfl⟩⟩
        have ha4 : ∀ t ∈ Set.Icc 0 r,
            (segment ℝ (f t) w ∩ affGe {0} ({v1, v2} : Set V3)).Nonempty →
            0 ≤ α t ∧ 0 ≤ β t := by
          intro t ht ⟨x, hxseg, hxcone⟩
          have hxaff : x ∈ affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) := by
            obtain ⟨s, u, hs, hu, hxeq⟩ := (affGe_0_2_char hv10 hv20 hv12 x).1 hxcone
            exact (cf4_affSpan3_char v1 v2 x).2 ⟨s, u, hxeq⟩
          have hx2 : x ∈ segment ℝ (f t) w ∩
              affineSpan ℝ (insert (0:V3) ({v1, v2} : Set V3)) := ⟨hxseg, hxaff⟩
          rw [habpoint t ht] at hx2
          have hxeq : x = α t • v1 + β t • v2 := Set.mem_singleton_iff.1 hx2
          obtain ⟨s, u, hs, hu, hxrepr⟩ := (affGe_0_2_char hv10 hv20 hv12 x).1 hxcone
          obtain ⟨e1, e2⟩ := cf4_repr_unique hindep hxeq.symm hxrepr.symm
          refine ⟨?_, ?_⟩
          · rw [e1]
            exact hs
          · rw [e2]
            exact hu
        have ha5 : 0 ≤ α 0 ∧ 0 ≤ β 0 :=
          ha4 0 (Set.mem_Icc.2 ⟨le_refl 0, hr0⟩) ⟨p0, ⟨u0, u0', hu00, hu00', hu001, hp0eq⟩,
            hp0cone⟩
        have hconta : ∀ s : ℝ, 0 ≤ s → s ≤ r → ContinuousOn α (Set.Icc 0 s) := fun s _ hs2 =>
          habcont.1.mono (Set.Icc_subset_Icc le_rfl hs2)
        have hcontb : ∀ s : ℝ, 0 ≤ s → s ≤ r → ContinuousOn β (Set.Icc 0 s) := fun s _ hs2 =>
          habcont.2.mono (Set.Icc_subset_Icc le_rfl hs2)
        -- α/β 的 IVT 首穿点 x
        obtain ⟨x, hx0, hxr, hxA, hxAB⟩ :
            ∃ x, 0 ≤ x ∧ x ≤ r ∧ (∀ t ∈ Set.Icc 0 x, 0 ≤ α t ∧ 0 ≤ β t) ∧
              (α x = 0 ∨ β x = 0) := by
          by_cases hA : ∀ t ∈ Set.Icc 0 r, 0 ≤ α t
          · -- α 全 ≥ 0：β 在 [0,t1'] 首穿 0
            have hb1 : β t1' < 0 := by
              by_contra hcon
              push_neg at hcon
              obtain ⟨x, hx⟩ := ha3 t1' ht1'I (hA t1' ht1'I) hcon
              rw [ht1ne'] at hx
              exact absurd hx (Set.mem_empty_iff_false x).mp
            obtain ⟨xb, hxb0, hxb1, hbxc, hblt⟩ :=
              cf4_ivt_first_dec β 0 t1' ht1'I.1 (hcontb t1' ht1'I.1 ht1'I.2) ha5.2 hb1.le
            refine ⟨xb, hxb0, le_trans hxb1 ht1'I.2, ?_, Or.inr hbxc⟩
            intro t ht
            have hbR : t ≤ r := le_trans ht.2 (le_trans hxb1 ht1'I.2)
            rcases eq_or_lt_of_le ht.2 with htx | htx
            · rw [htx]
              exact ⟨hA xb (Set.mem_Icc.2 ⟨hxb0, le_trans hxb1 ht1'I.2⟩),
                hbxc.symm.le⟩
            · exact ⟨hA t (Set.mem_Icc.2 ⟨ht.1, hbR⟩),
                le_of_lt (hblt t ⟨ht.1, htx⟩)⟩
          · push_neg at hA
            obtain ⟨ta, htaI, hta⟩ := hA
            obtain ⟨xa, hxa0, hxta, hxac, halt⟩ :=
              cf4_ivt_first_dec α 0 ta htaI.1 (hconta ta htaI.1 htaI.2) ha5.1 hta.le
            have hαxa : ∀ t ∈ Set.Icc 0 xa, 0 ≤ α t := by
              intro t ht
              rcases eq_or_lt_of_le ht.2 with htx | htx
              · rw [htx]
                exact hxac.symm.le
              · exact le_of_lt (halt t ⟨ht.1, htx⟩)
            by_cases hB : ∀ t ∈ Set.Icc 0 r, 0 ≤ β t
            · -- β 全 ≥ 0：x := xa
              refine ⟨xa, hxa0, le_trans hxta htaI.2, ?_, Or.inl hxac⟩
              intro t ht
              exact ⟨hαxa t ⟨ht.1, ht.2⟩,
                hB t (Set.mem_Icc.2 ⟨ht.1,
                  le_trans (le_trans ht.2 hxta) htaI.2⟩)⟩
            · push_neg at hB
              obtain ⟨tb, htbI, htb⟩ := hB
              obtain ⟨xb, hxb0, hxtb, hbxc, hblt⟩ :=
                cf4_ivt_first_dec β 0 tb htbI.1 (hcontb tb htbI.1 htbI.2) ha5.2 htb.le
              have hβxb : ∀ t ∈ Set.Icc 0 xb, 0 ≤ β t := by
                intro t ht
                rcases eq_or_lt_of_le ht.2 with htx | htx
                · rw [htx]
                  exact hbxc.symm.le
                · exact le_of_lt (hblt t ⟨ht.1, htx⟩)
              refine ⟨min xa xb, by positivity,
                le_trans (min_le_left xa xb) (le_trans hxta htaI.2), ?_, ?_⟩
              · intro t ht
                exact ⟨hαxa t ⟨ht.1, le_trans ht.2 (min_le_left xa xb)⟩,
                  hβxb t ⟨ht.1, le_trans ht.2 (min_le_right xa xb)⟩⟩
              · rcases le_total xa xb with hle | hle
                · rw [min_eq_left hle]
                  exact Or.inl hxac
                · rw [min_eq_right hle]
                  exact Or.inr hbxc
        have hxIr : x ∈ Set.Icc 0 r := ⟨hx0, hxr⟩
        have hxInH : x ∈ Set.Icc 0 h := ⟨hx0, le_trans hxr hrh⟩
        have hxAx : 0 ≤ α x ∧ 0 ≤ β x := hxA x ⟨hx0, le_refl x⟩
        refine Or.inr ⟨x, hx0, le_trans hxr hrh, ?_, ?_⟩
        · intro t ht
          exact ha3 t (Set.mem_Icc.2 ⟨ht.1, le_trans ht.2 hxr⟩)
            (hxA t ht).1 (hxA t ht).2
        · rcases hxAB with hxaz | hxbz
          · -- α x = 0：v2 ∈ cone{f x,w}（第三支）
            right
            right
            obtain ⟨u, hu1, hu2, hueq⟩ := ha2 x hxIr
            rw [hxaz, zero_smul, zero_add] at hueq
            have hbx : β x ≠ 0 := by
              intro hz
              rw [hz, zero_smul] at hueq
              exact (hfw x hxInH).2 u hu1 hu2 hueq.symm
            have hvfxw : f x ≠ w := by
              intro he
              have hle := hrle x hxIr
              rw [he] at hle
              linarith
            have heq : v2 = ((β x)⁻¹ * (1 - u)) • f x + ((β x)⁻¹ * u) • w := by
              have h2 := congrArg (fun z : V3 => (β x)⁻¹ • z) hueq
              rw [inv_smul_smul₀ hbx, smul_add, smul_smul, smul_smul] at h2
              exact h2
            exact (affGe_0_2_char (hfw x hxInH).1 hw0 hvfxw v2).2
              ⟨(β x)⁻¹ * (1 - u), (β x)⁻¹ * u,
                mul_nonneg (inv_nonneg.2 hxAx.2) (sub_nonneg.2 hu2),
                mul_nonneg (inv_nonneg.2 hxAx.2) hu1, heq⟩
          · -- β x = 0：v1 ∈ cone{f x,w}（第二支）
            right
            left
            obtain ⟨u, hu1, hu2, hueq⟩ := ha2 x hxIr
            rw [hxbz, zero_smul, add_zero] at hueq
            have hax : α x ≠ 0 := by
              intro hz
              rw [hz, zero_smul] at hueq
              exact (hfw x hxInH).2 u hu1 hu2 hueq.symm
            have hvfxw : f x ≠ w := by
              intro he
              have hle := hrle x hxIr
              rw [he] at hle
              linarith
            have heq : v1 = ((α x)⁻¹ * (1 - u)) • f x + ((α x)⁻¹ * u) • w := by
              have h2 := congrArg (fun z : V3 => (α x)⁻¹ • z) hueq
              rw [inv_smul_smul₀ hax, smul_add, smul_smul, smul_smul] at h2
              exact h2
            exact (affGe_0_2_char (hfw x hxInH).1 hw0 hvfxw v1).2
              ⟨(α x)⁻¹ * (1 - u), (α x)⁻¹ * u,
                mul_nonneg (inv_nonneg.2 hxAx.1) (sub_nonneg.2 hu2),
                mul_nonneg (inv_nonneg.2 hxAx.1) hu1, heq⟩

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


/-! ## W1（四点链 Wave-1）：分离平面重装 + dot_of_dist2 + rotation1 家族

HOL 参照（CKQOWSA_4.hl:2870-3265 及 :3870-3882）：`separation_plane_4_points`
（CF-4b 重构时溶散成私件群，此处按原陈述重装配）、`dot_of_dist2`（终局外心件
首子目标，本波先备）、`lemma_4_points_rotation1`、`lemma_4_points_rotation1_full`。
全部为自身完全证明的私件，供 W2/W3/W4 装配消费；不改 ContraFan.lean（W4 接线）。 -/

/-- 环带成员的构造方向（`inBallAnnulus` 之逆）：`‖z‖ ≤ 2h0 ∧ 2 ≤ ‖z‖`。 -/
private theorem cf4_ballAnnulus_mk {z : V3} (h1 : ‖z‖ ≤ 2 * h0) (h2 : 2 ≤ ‖z‖) :
    z ∈ ballAnnulus := by
  simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right]
  exact ⟨h1, fun hcon => lt_irrefl (2:ℝ) (lt_of_le_of_lt h2 hcon)⟩

/-- HOL `dot_of_dist2` 场景特形（CKQOWSA_4.hl:3870-3882，终局外心件首子目标）：
两"单位配置"（‖v‖ = 2、dist v w = 2）下距离平方展开直接给出内积值。 -/
private theorem cf4_dot_of_dist2 {v w : V3} (hv : ‖v‖ = 2) (hd : dist v w = 2) :
    inner ℝ v w = ‖w‖ ^ 2 / 2 := by
  have h2 : dist v w ^ 2 = ‖v - w‖ ^ 2 := by rw [dist_eq_norm]
  rw [hd, norm_sub_sq_real, hv] at h2
  linarith

/-- HOL `separation_plane_4_points`（CKQOWSA_4.hl:2870-3002）重装：环带四点、
两条对边 ≤ 2h0、四条连接边与长对角 ≥ 2、segment[v1,v3] 穿锥 {v2,v4} ⟹
存在分离法向 n（v2, v4 ⊥ n，v1·n 与 v3·n 反号）。途径：n := ±(v2 × v4)
（`cf4Cross` kit）；`cf4_LEMMA_3_POINTS_FINAL` 四次反用排四点入对面锥；
v1·n = 0 的余支用 `cf4_segment_intersects_aff_ge` / `cf4_segment_inter_aff_ge_ends`
（经 `cf4_mem_affSpan3_of_inner_eq` 把 v1、v3 拉进平面）排空。 -/
private theorem cf4_separation_plane_4_points {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd24 : 2 ≤ dist v2 v4) (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hcross : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty) :
    ∃ n : V3, n ≠ 0 ∧ inner ℝ v2 n = 0 ∧ inner ℝ v4 n = 0 ∧
      inner ℝ v1 n < 0 ∧ 0 < inner ℝ v3 n := by
  have hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    estd_non_collinear_lemma hb2 hb4 hd24 hd24l
  obtain ⟨hv20, hv40, hv24ne⟩ := cf4_not_collinear_smul hcol
  have hv24 : v2 ≠ v4 := fun he => hv24ne 1 (by rw [he, one_smul])
  have hnb : (0:V3) ∉ segment ℝ v1 v3 := cf4_not_between_estd hb1 hb3 hd13l
  -- n := ±(v2 × v4)：正交 v2、v4，取号使 v1·n ≤ 0
  obtain ⟨n, hn0, h2n, h4n, h1n0⟩ :
      ∃ n : V3, n ≠ 0 ∧ inner ℝ v2 n = 0 ∧ inner ℝ v4 n = 0 ∧ inner ℝ v1 n ≤ 0 := by
    rcases le_or_gt (inner ℝ v1 (cf4Cross v2 v4)) 0 with hle | hgt
    · exact ⟨cf4Cross v2 v4, cf4Cross_ne_zero hcol, cf4Cross_dot_left v2 v4,
        cf4Cross_dot_right v2 v4, hle⟩
    · refine ⟨-cf4Cross v2 v4, neg_ne_zero.2 (cf4Cross_ne_zero hcol), ?_, ?_, ?_⟩
      · rw [inner_neg_right, cf4Cross_dot_left, neg_zero]
      · rw [inner_neg_right, cf4Cross_dot_right, neg_zero]
      · rw [inner_neg_right]; linarith
  -- LEMMA_3_POINTS_FINAL 反用：四点均不落对面锥
  have hv1ncone : v1 ∉ affGe {0} ({v2, v4} : Set V3) := fun hmem =>
    cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4) (v3 := v1) hmem hb2 hb4 hb1 hd24l
      (by rw [dist_comm]; exact hd12) (by rw [dist_comm]; exact hd14)
  have hv3ncone : v3 ∉ affGe {0} ({v2, v4} : Set V3) := fun hmem =>
    cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4) (v3 := v3) hmem hb2 hb4 hb3 hd24l hd23
      (by rw [dist_comm]; exact hd34)
  have hv2ncone : v2 ∉ affGe {0} ({v1, v3} : Set V3) := fun hmem =>
    cf4_LEMMA_3_POINTS_FINAL (v1 := v1) (v2 := v3) (v3 := v2) hmem hb1 hb3 hb2 hd13l hd12
      (by rw [dist_comm]; exact hd23)
  have hv4ncone : v4 ∉ affGe {0} ({v1, v3} : Set V3) := fun hmem =>
    cf4_LEMMA_3_POINTS_FINAL (v1 := v1) (v2 := v3) (v3 := v4) hmem hb1 hb3 hb4 hd13l hd14 hd34
  -- v1·n = 0 与穿锥假设矛盾（两支分别排空）
  rcases eq_or_ne (inner ℝ v1 n) 0 with hz | hv1nne
  · exfalso
    have hindep : LinearIndependent ℝ ![v2, v4] := cf4_linearIndependent_pair hcol
    have hv1span : v1 ∈ affineSpan ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
      cf4_mem_affSpan3_of_inner_eq hindep hn0 h2n h4n hz
    rcases eq_or_ne (inner ℝ v3 n) 0 with hz3 | hne3
    · have hv3span : v3 ∈ affineSpan ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
        cf4_mem_affSpan3_of_inner_eq hindep hn0 h2n h4n hz3
      have hdisj := cf4_segment_intersects_aff_ge hcol hnb hv1span hv3span hcross
      exact Or.elim hdisj (fun hc1 => hv1ncone hc1)
        (fun hc23 => Or.elim hc23 (fun hc2 => hv2ncone hc2) (fun hc3 => hv4ncone hc3))
    · exact hv1ncone
        (cf4_segment_inter_aff_ge_ends (v1 := v2) (v2 := v4) hv20 hv40 hv24 h2n h4n hz hne3
          hcross)
  refine ⟨n, hn0, h2n, h4n, lt_of_le_of_ne h1n0 hv1nne, ?_⟩
  have hv1nlt : inner ℝ v1 n < 0 := lt_of_le_of_ne h1n0 hv1nne
  rcases lt_trichotomy (inner ℝ v3 n) 0 with h3l | h3e | h3g
  · -- v3·n < 0：交点 dot 同时为零（锥侧）与负（段侧），矛盾
    exfalso
    obtain ⟨x, hxseg, hxcone⟩ := hcross
    obtain ⟨u, u', hu, hu', huu, hxueq⟩ := hxseg
    obtain ⟨t1, t2, ht1, ht2, hxceq⟩ := (affGe_0_2_char hv20 hv40 hv24 x).1 hxcone
    have kcone : inner ℝ x n = 0 := by
      rw [hxceq, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2n, h4n]
      ring
    have kseg : inner ℝ x n = u * inner ℝ v1 n + u' * inner ℝ v3 n := by
      rw [← hxueq, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rcases eq_or_lt_of_le hu with hu0 | hup
    · subst hu0
      have hu'1 : u' = 1 := by linarith
      rw [kseg] at kcone
      rw [zero_mul, zero_add, hu'1] at kcone
      linarith
    · have e1 : u * inner ℝ v1 n < 0 := mul_neg_of_pos_of_neg hup hv1nlt
      have e2 : u' * inner ℝ v3 n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu' (le_of_lt h3l)
      rw [kseg] at kcone
      linarith
  · exfalso
    -- v3·n = 0：换端点引理把 v3 拉进对面锥
    refine hv3ncone
      (cf4_segment_inter_aff_ge_ends (v1 := v2) (v2 := v4) hv20 hv40 hv24 h2n h4n h3e hv1nne ?_)
    rw [segment_symm]
    exact hcross
  · exact h3g

/-- HOL `lemma_4_points_rotation1`（CKQOWSA_4.hl:3003-3202）：绕轴 ℝ•v2 转动 v1
（保 ‖·‖、保到轴上点距离），落点 v1' 与 v4 距离恰为 2，且 segment[v1',v3] 仍穿锥
{v2,v4}。途径：分离法向 n（W1a）+ `cf4_rotation_about_axis`（轴上点距全保）
+ `cf4_continuous_lemma_aff_ge` 交不变量传递 + `cf4_ivt_first_dec` 打靶
dist(·,v4) = 2 + `cf4_LEMMA_3_POINTS_FINAL` 排掉首穿点三支与全程有交支。 -/
private theorem cf4_rotation_1 {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd24 : 2 ≤ dist v2 v4)
    (hcross : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty) :
    ∃ v1' : V3, v1' ∈ ballAnnulus ∧ ‖v1'‖ = ‖v1‖ ∧ dist v1' v3 ≤ 2 * h0 ∧
      dist v1' v2 = dist v1 v2 ∧ dist v1' v4 = 2 ∧
      (segment ℝ v1' v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty := by
  have hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    estd_non_collinear_lemma hb2 hb4 hd24 hd24l
  obtain ⟨hv20, hv40, hv24ne⟩ := cf4_not_collinear_smul hcol
  have hv24 : v2 ≠ v4 := fun he => hv24ne 1 (by rw [he, one_smul])
  obtain ⟨n, hn0, h2n, h4n, h1n, h3n⟩ :=
    cf4_separation_plane_4_points hb1 hb2 hb3 hb4 hd13l hd24l hd24 hd12 hd14 hd23 hd34 hcross
  -- 轴投影差非零：v1−proj·v2、v3−proj·v2 的 dot n 分别 < 0 / > 0
  have hvw0 : v1 - (inner ℝ v1 v2 / ‖v2‖ ^ 2) • v2 ≠ 0 := by
    intro hzero
    have hz : inner ℝ (v1 - (inner ℝ v1 v2 / ‖v2‖ ^ 2) • v2) n = 0 := by
      rw [hzero]; simp
    rw [inner_sub_left, real_inner_smul_left, h2n, mul_zero, sub_zero] at hz
    linarith
  have hww0 : v3 - (inner ℝ v3 v2 / ‖v2‖ ^ 2) • v2 ≠ 0 := by
    intro hzero
    have hz : inner ℝ (v3 - (inner ℝ v3 v2 / ‖v2‖ ^ 2) • v2) n = 0 := by
      rw [hzero]; simp
    rw [inner_sub_left, real_inner_smul_left, h2n, mul_zero, sub_zero] at hz
    linarith
  obtain ⟨f, a, b, hap, hfcont, hf0, hf1, hfdist, hfdec⟩ :=
    cf4_rotation_about_axis (d := v2) (v := v1) (w := v3) hv20 hvw0 hww0
  have hnormft : ∀ t : ℝ, ‖f t‖ = ‖v1‖ := by
    intro t
    have h5 := hfdist t 0
    rw [zero_smul, dist_zero_right, dist_zero_right] at h5
    exact h5
  have hba : ∀ t : ℝ, f t ∈ ballAnnulus := by
    intro t
    obtain ⟨hz1, hz2⟩ := inBallAnnulus hb1
    exact cf4_ballAnnulus_mk (by rw [hnormft t]; exact hz2) (by rw [hnormft t]; exact hz1)
  have hfub : ∀ t ∈ Set.Icc 0 1, dist (f t) v3 ≤ 2 * h0 := fun t ht =>
    le_trans (hfdec t ht) hd13l
  rcases cf4_continuous_lemma_aff_ge (v1 := v2) (v2 := v4) (w := v3) f 1 (by norm_num)
      hfcont.continuousOn (by rw [hf0]; exact hcross)
      (fun t ht => cf4_not_between_estd (hba t) hb3 (hfub t ht)) hcol with
    hall | ⟨x, hx0, hx1, hallx, hdisj⟩
  · -- 全程有交支：f 1 = a•v3 + b•v2（a > 0）在分离面正侧，交点 dot 矛盾
    exfalso
    obtain ⟨x0, hx0seg, hx0cone⟩ := hall 1 (Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩)
    obtain ⟨t1, t2, ht1, ht2, hxceq⟩ := (affGe_0_2_char hv20 hv40 hv24 x0).1 hx0cone
    obtain ⟨u, u', hu, hu', huu, hxueq⟩ := hx0seg
    have kcone : inner ℝ x0 n = 0 := by
      rw [hxceq, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2n, h4n]
      ring
    have kf1 : 0 < inner ℝ (f 1) n := by
      rw [hf1, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2n, mul_zero,
        add_zero]
      exact mul_pos hap h3n
    have kseg : inner ℝ x0 n = u * inner ℝ (f 1) n + u' * inner ℝ v3 n := by
      rw [← hxueq, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rcases eq_or_lt_of_le hu with hu0 | hup
    · subst hu0
      have hu'1 : u' = 1 := by linarith
      rw [kseg] at kcone
      rw [zero_mul, zero_add, hu'1] at kcone
      linarith
    · have e1 : 0 < u * inner ℝ (f 1) n := mul_pos hup kf1
      have e2 : 0 ≤ u' * inner ℝ v3 n := mul_nonneg hu' (le_of_lt h3n)
      rw [kseg] at kcone
      linarith
  · -- 首穿支：dist(f x, v4) < 2 经三支排空，IVT 打靶恰等 2
    have hxd2 : dist (f x) v2 = dist v1 v2 := by
      have h5 := hfdist x 1
      rw [one_smul] at h5
      exact h5
    have hfx2 : dist (f x) v4 < 2 := by
      by_contra hge
      push_neg at hge
      rcases hdisj with hd1 | hd2 | hd3
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4) (v3 := f x) hd1 hb2 hb4 (hba x)
          hd24l (by rw [dist_comm]; linarith) (by rw [dist_comm]; exact hge)
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := f x) (v2 := v3) (v3 := v2) hd2 (hba x) hb3 hb2
          (le_trans (hfdec x (Set.mem_Icc.2 ⟨hx0, hx1⟩)) hd13l) (by linarith)
          (by rw [dist_comm]; exact hd23)
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := f x) (v2 := v3) (v3 := v4) hd3 (hba x) hb3 hb4
          (le_trans (hfdec x (Set.mem_Icc.2 ⟨hx0, hx1⟩)) hd13l) hge hd34
    obtain ⟨s, hs0, hsx, hsd, -⟩ :=
      cf4_ivt_first_dec (fun t => dist (f t) v4) 2 x hx0
        ((hfcont.dist continuous_const).continuousOn)
        (by show (2:ℝ) ≤ dist (f 0) v4; rw [hf0]; exact hd14)
        (by show dist (f x) v4 ≤ 2; exact le_of_lt hfx2)
    refine ⟨f s, hba s, hnormft s,
      le_trans (hfdec s (Set.mem_Icc.2 ⟨hs0, le_trans hsx hx1⟩)) hd13l, ?_, hsd,
      hallx s (Set.mem_Icc.2 ⟨hs0, hsx⟩)⟩
    have h5 := hfdist s 1
    rw [one_smul] at h5
    exact h5

/-- HOL `lemma_4_points_rotation1_full`（CKQOWSA_4.hl:3203-3265）：rotation1 四次
（v1 绕 v2、v1' 绕 v4；v3 绕 v2、v3' 绕 v4），四条交叉距离全部打成恰 2，范数保持，
穿锥交不变量保持。 -/
private theorem cf4_rotation_1_full {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd24 : 2 ≤ dist v2 v4)
    (hcross : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty) :
    ∃ v1' v3' : V3, v1' ∈ ballAnnulus ∧ v3' ∈ ballAnnulus ∧
      ‖v1'‖ = ‖v1‖ ∧ ‖v3'‖ = ‖v3‖ ∧ dist v1' v3' ≤ 2 * h0 ∧
      dist v1' v2 = 2 ∧ dist v1' v4 = 2 ∧ dist v2 v3' = 2 ∧ dist v3' v4 = 2 ∧
      (segment ℝ v1' v3' ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty := by
  -- 第 1 次：v1 绕 v2 转
  obtain ⟨w1, hw1b, hw1n, hw1d13, hw1d2, hw1d4, hw1cross⟩ :=
    cf4_rotation_1 hb1 hb2 hb3 hb4 hd13l hd24l hd12 hd14 hd23 hd34 hd24 hcross
  -- 第 2 次：w1 绕 v4 转
  obtain ⟨w2, hw2b, hw2n, hw2d13, hw2d4, hw2d2, hw2cross⟩ :=
    cf4_rotation_1 hw1b hb4 hb3 hb2 hw1d13 (by rw [dist_comm]; exact hd24l)
      (by linarith [hw1d4]) (by linarith [hw1d2, hd12])
      (by rw [dist_comm]; exact hd34) (by rw [dist_comm]; exact hd23)
      (by rw [dist_comm]; exact hd24)
      (by rw [Set.pair_comm]; exact hw1cross)
  -- 第 3 次：v3 绕 v2 转
  obtain ⟨w3, hw3b, hw3n, hw3d13, hw3d2, hw3d4, hw3cross⟩ :=
    cf4_rotation_1 hb3 hb2 hw2b hb4 (by rw [dist_comm]; exact hw2d13) hd24l
      (by rw [dist_comm]; exact hd23) hd34
      (by rw [dist_comm]; linarith [hw2d2]) (by linarith [hw2d4, hw1d4]) hd24
      (by rw [segment_symm, Set.pair_comm]; exact hw2cross)
  -- 第 4 次：w3 绕 v4 转
  obtain ⟨w4, hw4b, hw4n, hw4d13, hw4d4, hw4d2, hw4cross⟩ :=
    cf4_rotation_1 hw3b hb4 hw2b hb2 hw3d13 (by rw [dist_comm]; exact hd24l)
      (by linarith [hw3d4]) (by linarith [hw3d2, hd23, dist_comm v2 v3])
      (by rw [dist_comm]; linarith [hw2d4, hw1d4]) (by linarith [hw2d2])
      (by rw [dist_comm]; exact hd24)
      (by rw [Set.pair_comm]; exact hw3cross)
  refine ⟨w2, w4, hw2b, hw4b, hw2n.trans hw1n, hw4n.trans hw3n,
    ?_, hw2d2, ?_, ?_, ?_, ?_⟩
  · rw [dist_comm]; exact hw4d13
  · linarith [hw2d4, hw1d4]
  · rw [dist_comm]; exact hw4d2
  · linarith [hw4d4, hw3d4]
  · rw [segment_symm, Set.pair_comm]; exact hw4cross


/-! ## W2（四点链 Wave-2）：投影 helper + segment_inter_conv + rotation2 家族

HOL 参照（CKQOWSA_4.hl）：`PROJECTION_DIST_SPECIAL_LE`（:267-283）、
`segment_inter_conv`（:3266-3378）、`lemma_4_points_rotation2`（:3379-3813）、
`lemma_4_points_rotation2_full`（:3814-3865）以及 checkpoint 中转件
`rotation_lemma_segments`（:1395-1675，非退化支）的吸收移植。
全部为自身完全证明的私件，供 W3/W4 装配消费；不改 ContraFan.lean。 -/

/-- 轴向正交投影残差（HOL `projection d w`，CKQOWSA_4.hl:135 附近定义）：
`y` 去掉沿 `d` 的影子后的 ⊥ 分量。 -/
private noncomputable def cf4Proj (d y : V3) : V3 := y - (inner ℝ y d / ‖d‖ ^ 2) • d

private theorem cf4Proj_orth {d y : V3} : inner ℝ (cf4Proj d y) d = 0 := by
  rcases eq_or_ne d 0 with h0 | hne
  · subst h0
    simp [cf4Proj]
  · have hd2 : (0:ℝ) < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hne) 2
    rw [cf4Proj, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring

private theorem cf4Proj_self {d : V3} (hd : d ≠ 0) : cf4Proj d d = 0 := by
  have hd2 : (0:ℝ) < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hd) 2
  have h1 : inner ℝ d d / ‖d‖ ^ 2 = 1 := by
    rw [real_inner_self_eq_norm_sq, pow_two]
    field_simp
  rw [cf4Proj, h1, one_smul, sub_self]

private theorem cf4Proj_id_of_orth {d y : V3} (h : inner ℝ y d = 0) : cf4Proj d y = y := by
  rw [cf4Proj, h, zero_div, zero_smul, sub_zero]

private theorem cf4Proj_add {d y z : V3} :
    cf4Proj d (y + z) = cf4Proj d y + cf4Proj d z := by
  rw [cf4Proj, cf4Proj, cf4Proj, inner_add_left]
  module

private theorem cf4Proj_smul {d y : V3} (c : ℝ) :
    cf4Proj d (c • y) = c • cf4Proj d y := by
  rw [cf4Proj, cf4Proj, real_inner_smul_left]
  module

private theorem cf4Proj_dot_n {d n y : V3} (h : inner ℝ d n = 0) :
    inner ℝ (cf4Proj d y) n = inner ℝ y n := by
  rw [cf4Proj, inner_sub_left, real_inner_smul_left, h, mul_zero, sub_zero]

/-- HOL `PROJECTION_DIST_SPECIAL_LE`（CKQOWSA_4.hl:267-283）：`x ⊥ d` 且
`x` 到 `w` 的残差不大于 `v` 到 `w` 的残差 ⟹ 把 `v` 平移到 `d` 的影子（`v1+ 影子`）
后到 `w` 的距离不增。证法：残差-影子正交分解 + 勾股恒等式（同
`cf4_rotation_about_axis` 的 s1/s2 模式）。 -/
private theorem cf4_projection_dist_le {d x v w : V3} (hd : d ≠ 0) (hxd : inner ℝ x d = 0)
    (hle : dist x (cf4Proj d w) ≤ dist (cf4Proj d v) (cf4Proj d w)) :
    dist (x + (inner ℝ v d / ‖d‖ ^ 2) • d) w ≤ dist v w := by
  have hd2 : (0:ℝ) < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.2 hd) 2
  -- 残差抽象化：qv + lam•d = v、qw + mu•d = w（残差 ⊥ d；lam/mu 即影子系数）
  obtain ⟨qv, lam, hlam, hqvadd, hqvd⟩ :
      ∃ q : V3, ∃ lam : ℝ, lam = inner ℝ v d / ‖d‖ ^ 2 ∧
        q + lam • d = v ∧ inner ℝ q d = 0 :=
    ⟨cf4Proj d v, inner ℝ v d / ‖d‖ ^ 2, rfl, by
      rw [cf4Proj]; module, cf4Proj_orth⟩
  obtain ⟨qw, mu, hmu, hqwadd, hqwd⟩ :
      ∃ q : V3, ∃ mu : ℝ, mu = inner ℝ w d / ‖d‖ ^ 2 ∧
        q + mu • d = w ∧ inner ℝ q d = 0 :=
    ⟨cf4Proj d w, inner ℝ w d / ‖d‖ ^ 2, rfl, by
      rw [cf4Proj]; module, cf4Proj_orth⟩
  rw [← hlam]
  simp only [cf4Proj] at hle
  rw [← hlam, ← hmu] at hle
  have eqw : w - mu • d = qw := by rw [← hqwadd]; module
  have eqv : v - lam • d = qv := by rw [← hqvadd]; module
  rw [eqw, eqv] at hle
  -- 勾股恒等式
  have pyth : ∀ (y z : V3) (a b : ℝ), inner ℝ y d = 0 → inner ℝ z d = 0 →
      ‖(y - z) + (a - b) • d‖ ^ 2 = ‖y - z‖ ^ 2 + (a - b) ^ 2 * ‖d‖ ^ 2 := by
    intro y z a b hyd hzd
    have h1 : ‖(y - z) + (a - b) • d‖ ^ 2
        = inner ℝ ((y - z) + (a - b) • d) ((y - z) + (a - b) • d) :=
      (real_inner_self_eq_norm_sq _).symm
    rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm (y - z) d, inner_sub_left y z d, hyd, hzd,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have e1 : dist (x + lam • d) w = ‖(x - qw) + (lam - mu) • d‖ := by
    rw [dist_eq_norm]
    refine congrArg norm ?_
    rw [← hqwadd]
    module
  have e2 : dist v w = ‖(qv - qw) + (lam - mu) • d‖ := by
    rw [dist_eq_norm]
    refine congrArg norm ?_
    rw [← hqvadd, ← hqwadd]
    module
  refine nonneg_le_nonneg_of_sq_le_sq dist_nonneg ?_
  rw [← pow_two, ← pow_two]
  rw [e1, pyth x qw lam mu hxd hqwd, e2, pyth qv qw lam mu hqvd hqwd]
  have hsq : ‖x - qw‖ ^ 2 ≤ ‖qv - qw‖ ^ 2 := by
    rw [← dist_eq_norm x qw, ← dist_eq_norm qv qw]
    exact pow_le_pow_left₀ dist_nonneg hle 2
  linarith

/-- 三点凸包成员的系数提取（`Finset.mem_convexHull'` + `fin_sum_three`）：
`z ∈ convex hull {0, v2, v4}` ⟹ `z = t2•v2 + t4•v4`、t2 t4 ≥ 0、t2+t4 ≤ 1。 -/
private theorem cf4_mem_convexHull3 {v2 v4 z : V3} (hv2 : v2 ≠ 0) (hv4 : v4 ≠ 0)
    (h24 : v2 ≠ v4)
    (hz : z ∈ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))) :
    ∃ t2 t4 : ℝ, 0 ≤ t2 ∧ 0 ≤ t4 ∧ t2 + t4 ≤ 1 ∧ z = t2 • v2 + t4 • v4 := by
  have hS : (insert (0:V3) ({v2, v4} : Set V3))
      = (({0, v2, v4} : Finset V3) : Set V3) := by
    ext y
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hS] at hz
  rw [Finset.mem_convexHull'] at hz
  obtain ⟨w, hw0, hw1, hwx⟩ := hz
  have hsum : ∑ y ∈ ({0, v2, v4} : Finset V3), w y = w (0:V3) + w v2 + w v4 := by
    rw [fin_sum_three (g := fun y => w y) (fun h => hv2 h.symm) (fun h => hv4 h.symm) h24]
  have hx : ∑ y ∈ ({0, v2, v4} : Finset V3), w y • y
      = w v2 • v2 + w v4 • v4 := by
    rw [fin_sum_three (g := fun y => w y • y) (fun h => hv2 h.symm) (fun h => hv4 h.symm) h24]
    simp
  have hw00 : 0 ≤ w (0:V3) := hw0 (0:V3) (by simp)
  have hw02 : 0 ≤ w v2 := hw0 v2 (by simp)
  have hw04 : 0 ≤ w v4 := hw0 v4 (by simp)
  refine ⟨w v2, w v4, hw02, hw04, ?_, ?_⟩
  · have h1 : w (0:V3) + w v2 + w v4 = 1 := by
      rw [← hsum]; exact hw1
    linarith
  · rw [← hx, hwx]

/-- `b = c•a` 时 `{0, a, b}` 共线（`cf4_not_collinear_smul` 的反向构造）。 -/
private theorem cf4_collinear_mk_smul {a b : V3} (c : ℝ) (h : b = c • a) :
    Collinear ℝ (insert (0:V3) ({a, b} : Set V3)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0:V3), a, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | hz
  · exact ⟨0, by rw [zero_smul, vadd_eq_add, add_zero]⟩
  rcases hz with rfl | hz
  · exact ⟨1, by rw [one_smul, vadd_eq_add, add_zero]⟩
  · rw [hz, h]
    exact ⟨c, by rw [vadd_eq_add, add_zero]⟩

/-- W2 checkpoint（HOL `rotation_lemma_segments` CKQOWSA_4.hl:1395-1675 的非退化支，
「任意连续族不变量」范式的投影平面实例）：`d⊥` 平面内旋转族——保范、保轴正交、
到两投影点距离不增、segment[g t, qw] 恒穿射线 cone{pu}。途经
`cf4_rotation_family_special`（族 + dist-to-pu + 锥成员）+ `cf4_rotation_dist_decrease`
（dist-to-qw；τ=0 退化支 qw = κ•qv、κ ≤ 0 走 C–S 直接界）+
`cf4_aff_ge_inter_segments`（穿越不变量传递）。 -/
private theorem cf4_rotation_2_family {d qv qw pu : V3} (hd : d ≠ 0)
    (hqv : qv ≠ 0) (hqw : qw ≠ 0) (hpu : pu ≠ 0)
    (hqvd : inner ℝ qv d = 0) (hpwd : inner ℝ qw d = 0) (hpud : inner ℝ pu d = 0)
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({qv, pu} : Set V3)))
    (hcr : ∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ (1 - σ) • qv + σ • qw = τ • pu) :
    ∃ g : ℝ → V3, Continuous g ∧ g 0 = qv ∧ g 1 = (‖qv‖ / ‖pu‖) • pu ∧
      (∀ t, ‖g t‖ = ‖qv‖ ∧ inner ℝ (g t) d = 0) ∧
      (∀ t ∈ Set.Icc 0 1, dist (g t) pu ≤ dist qv pu) ∧
      (∀ t ∈ Set.Icc 0 1, dist (g t) qw ≤ dist qv qw) ∧
      (∀ t ∈ Set.Icc 0 1,
        (segment ℝ (g t) qw ∩ affGe {0} ({pu} : Set V3)).Nonempty) := by
  obtain ⟨g, hgcont, hg0, hg1, hgprop, hgdist, hgcone⟩ :=
    cf4_rotation_family_special (v := qv) (w := pu) (n := d) hqv hpu hqvd hpud
  obtain ⟨σ, τ, hσ0, hσ1, hτ0, hcr⟩ := hcr
  have hqvp : qv ≠ pu := by
    intro he
    refine hcol ?_
    have hset : (insert (0:V3) ({qv, pu} : Set V3)) = ({0, pu} : Set V3) := by
      rw [he]
      ext z
      simp
    rw [hset]
    exact collinear_pair ℝ (0:V3) pu
  have hcrossray : (segment ℝ qv qw ∩ affGe {0} ({pu} : Set V3)).Nonempty :=
    ⟨(1 - σ) • qv + σ • qw, ⟨1 - σ, σ, by linarith, hσ0, by ring, rfl⟩,
      (affGe_0_1_char pu _).2 ⟨τ, hτ0, hcr⟩⟩
  refine ⟨g, hgcont, hg0, hg1, hgprop, fun t ht => hgdist t ht, ?_, ?_⟩
  · -- dist(g t, qw) ≤ dist(qv, qw)
    intro t ht
    rcases eq_or_lt_of_le hτ0 with hτ | hτp
    · -- τ = 0 退化支：qw = κ•qv、κ ≤ 0，C–S 直接界
      have hcr0 : (1 - σ) • qv + σ • qw = (0:V3) := by
        rw [← hτ, zero_smul] at hcr
        exact hcr
      have hσpos : 0 < σ := by
        rcases eq_or_lt_of_le hσ0 with h | h
        · exfalso
          rw [← h, sub_zero, zero_smul, add_zero, one_smul] at hcr0
          exact hqv hcr0
        · exact h
      have hσlt : σ < 1 := by
        rcases eq_or_lt_of_le hσ1 with h | h
        · exfalso
          rw [h, sub_self, zero_smul, zero_add, one_smul] at hcr0
          exact hqw hcr0
        · exact h
      have hκ : qw = ((σ - 1) / σ) • qv := by
        have h2 : σ • qw = (σ - 1) • qv := by
          linear_combination (norm := module) hcr0
        have h3 := congrArg (fun z : V3 => (σ:ℝ)⁻¹ • z) h2
        rw [inv_smul_smul₀ hσpos.ne', smul_smul] at h3
        field_simp at h3
        exact h3
      have hκle : (σ - 1) / σ ≤ 0 := by
        rw [div_le_iff₀ hσpos]
        linarith
      have hR : dist qv qw = (1 - (σ - 1) / σ) * ‖qv‖ := by
        rw [hκ, dist_eq_norm]
        have h5 : qv - ((σ - 1) / σ) • qv = (1 - (σ - 1) / σ) • qv := by module
        rw [h5, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith :
          (0:ℝ) ≤ 1 - (σ - 1) / σ)]
      have hcs : inner ℝ (g t) qv ≤ ‖qv‖ ^ 2 := by
        have h3 := abs_real_inner_le_norm (g t) qv
        have h4 : inner ℝ (g t) qv ≤ |inner ℝ (g t) qv| := le_abs_self _
        rw [(hgprop t).1, ← pow_two] at h3
        linarith
      have hkey : ‖g t - ((σ - 1) / σ) • qv‖ ^ 2
          ≤ ((1 - (σ - 1) / σ) * ‖qv‖) ^ 2 := by
        have h6 : ‖g t - ((σ - 1) / σ) • qv‖ ^ 2
            = ‖qv‖ ^ 2 - 2 * ((σ - 1) / σ) * inner ℝ (g t) qv
              + ((σ - 1) / σ) ^ 2 * ‖qv‖ ^ 2 := by
          rw [cf4_norm_sq_sub, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
            abs_of_nonpos hκle, (hgprop t).1]
          ring
        have h7 : ((1 - (σ - 1) / σ) * ‖qv‖) ^ 2
            = (1 - (σ - 1) / σ) ^ 2 * ‖qv‖ ^ 2 := by
          rw [mul_pow]
        have h8 : inner ℝ (g t) qv - ‖qv‖ ^ 2 ≤ 0 := by linarith
        have h9 : (2:ℝ) * ((σ - 1) / σ) ≤ 0 := by linarith
        have hprod : (2:ℝ) * ((σ - 1) / σ) * (inner ℝ (g t) qv - ‖qv‖ ^ 2) ≥ 0 := by
          nlinarith [h8, h9]
        rw [h6, h7]
        nlinarith [hprod]
      rw [hR, hκ, dist_eq_norm]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).1 hkey
    · -- 主支：pu ∈ cone{qv,qw} ⟹ g t ∈ cone{qv,qw} ⟹ 距离不增
      have hqvw : qv ≠ qw := by
        intro he
        have h1 : (1 - σ) • qv + σ • qv = τ • pu := by rw [← he] at hcr; exact hcr
        have h2 : qv = τ • pu := by
          rw [← add_smul] at h1
          have h5 : (1:ℝ) - σ + σ = 1 := by ring
          rw [h5, one_smul] at h1
          exact h1
        have h3 : pu = (τ:ℝ)⁻¹ • qv := by
          have h4 := congrArg (fun z : V3 => (τ:ℝ)⁻¹ • z) h2
          rw [inv_smul_smul₀ hτp.ne'] at h4
          exact h4.symm
        exact hcol (cf4_collinear_mk_smul (τ:ℝ)⁻¹ h3)
      have hpuexp : pu = ((1 - σ) / τ) • qv + (σ / τ) • qw := by
        have h2 := congrArg (fun z : V3 => (τ:ℝ)⁻¹ • z) hcr
        rw [inv_smul_smul₀ hτp.ne', smul_add, smul_smul, smul_smul] at h2
        field_simp at h2
        exact h2.symm
      obtain ⟨a, b, ha, hb2, hgp⟩ :=
        (affGe_0_2_char hqv hpu hqvp (g t)).1 (hgcone hcol t ht)
      have hd1p : 0 ≤ (1 - σ) / τ := div_nonneg (by linarith : 0 ≤ 1 - σ) hτp.le
      have hd2p : 0 ≤ σ / τ := div_nonneg hσ0 hτp.le
      have hmem : g t ∈ affGe {0} ({qv, qw} : Set V3) :=
        (affGe_0_2_char hqv hqw hqvw (g t)).2 ⟨a + b * ((1 - σ) / τ), b * (σ / τ),
          by nlinarith [ha, hb2, hd1p], by nlinarith [hb2, hd2p],
          by rw [hgp, hpuexp]; module⟩
      exact cf4_rotation_dist_decrease hqv hqw hmem (hgprop t).1
  · -- 穿越不变量：aff_ge_inter_segments 传递
    intro t ht
    exact cf4_aff_ge_inter_segments hcol (hgcone hcol t ht) hcrossray

/-- HOL `segment_inter_conv`（CKQOWSA_4.hl:3266-3378）：锥交 + 投影段-射线穿越 ⟹
凸包交。证法：交点 x 的双表示给恒等式 u•(v1−v2) + u'•(v3−v2) = t4•d + (1−t2−t4)(−v2)，
投影到 d⊥ 后与投影段穿越点的 dot 方程联立（两侧参数同为 v1·n/(v1·n−v3·n)），
再由 pu ≠ 0 得 tp = 1−t2−t4 ≥ 0，x 以 (t2, t4) 入凸包。 -/
private theorem cf4_segment_inter_conv {v1 v2 v3 v4 n : V3}
    (hv2 : v2 ≠ 0) (hv4 : v4 ≠ 0) (h24 : v2 ≠ v4)
    (hpu : cf4Proj (v4 - v2) (-v2) ≠ 0)
    (hcross : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty)
    (h1n : inner ℝ v1 n < 0) (h3n : 0 < inner ℝ v3 n)
    (h2n : inner ℝ v2 n = 0) (h4n : inner ℝ v4 n = 0)
    (hproj : (segment ℝ (cf4Proj (v4 - v2) (v1 - v2)) (cf4Proj (v4 - v2) (v3 - v2)) ∩
        affGe {0} ({cf4Proj (v4 - v2) (-v2)} : Set V3)).Nonempty) :
    (segment ℝ v1 v3 ∩ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))).Nonempty := by
  have hd : v4 - v2 ≠ 0 := fun hcon => h24 (eq_of_sub_eq_zero hcon).symm
  have hdnn : inner ℝ (v4 - v2) n = 0 := by rw [inner_sub_left, h4n, h2n, sub_zero]
  have e1n : inner ℝ (v1 - v2) n = inner ℝ v1 n := by rw [inner_sub_left, h2n, sub_zero]
  have e3n : inner ℝ (v3 - v2) n = inner ℝ v3 n := by rw [inner_sub_left, h2n, sub_zero]
  have eun : inner ℝ (-v2) n = 0 := by rw [inner_neg_left, h2n, neg_zero]
  obtain ⟨x, hxseg, hxcone⟩ := hcross
  obtain ⟨u, u', hu, hu', huu, hxueq⟩ := hxseg
  obtain ⟨t2, t4, ht2, ht4, hxeq⟩ := (affGe_0_2_char hv2 hv4 h24 x).1 hxcone
  -- 恒等式 (A) 与其投影
  have iA : u • (v1 - v2) + u' • (v3 - v2)
      = t4 • (v4 - v2) + (1 - t2 - t4) • (-v2) := by
    have h1 : u • (v1 - v2) + u' • (v3 - v2)
        = (u • v1 + u' • v3) - (u + u') • v2 := by module
    rw [h1, huu, hxueq, hxeq]
    module
  have iProj : u • cf4Proj (v4 - v2) (v1 - v2) + u' • cf4Proj (v4 - v2) (v3 - v2)
      = (1 - t2 - t4) • cf4Proj (v4 - v2) (-v2) := by
    have h0 : cf4Proj (v4 - v2) (v4 - v2) = 0 := cf4Proj_self hd
    have h := congrArg (cf4Proj (v4 - v2)) iA
    rw [cf4Proj_add, cf4Proj_smul, cf4Proj_smul, cf4Proj_add, cf4Proj_smul,
      cf4Proj_smul, h0, smul_zero, zero_add] at h
    exact h
  have keyA : u * inner ℝ v1 n + u' * inner ℝ v3 n = 0 := by
    have h := congrArg (fun z : V3 => inner ℝ z n) iProj
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      cf4Proj_dot_n hdnn, cf4Proj_dot_n hdnn, cf4Proj_dot_n hdnn, e1n, e3n, eun,
      mul_zero] at h
    linarith
  -- 投影段穿越点的 dot 方程
  obtain ⟨px, hpxseg, hpxray⟩ := hproj
  obtain ⟨up, up', hup, hup', hupu, hpxueq⟩ := hpxseg
  obtain ⟨tp, htp, hpxeq⟩ := (affGe_0_1_char _ _).1 hpxray
  have keyB : up * inner ℝ v1 n + up' * inner ℝ v3 n = 0 := by
    have h := congrArg (fun z : V3 => inner ℝ z n) hpxueq
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      cf4Proj_dot_n hdnn, cf4Proj_dot_n hdnn, e1n, e3n, hpxeq, real_inner_smul_left,
      cf4Proj_dot_n hdnn, eun, mul_zero] at h
    linarith
  -- 两侧参数一致（同解 v1·n/(v1·n − v3·n)）
  have hu_eq : u = up := by
    have h3 : (u - up) * (inner ℝ v1 n - inner ℝ v3 n) = 0 := by
      have h9 : (u - up) * (inner ℝ v1 n - inner ℝ v3 n)
          = (u * inner ℝ v1 n + u' * inner ℝ v3 n)
            - (up * inner ℝ v1 n + up' * inner ℝ v3 n) := by
        have h10 : (1:ℝ) - u = u' := by linarith
        have h11 : (1:ℝ) - up = up' := by linarith
        rw [← h10, ← h11]
        ring
      rw [h9, keyA, keyB]
      ring
    have hne : inner ℝ v1 n - inner ℝ v3 n ≠ 0 :=
      ne_of_lt (show inner ℝ v1 n - inner ℝ v3 n < 0 by linarith)
    have h4 : u - up = 0 := by
      rcases mul_eq_zero.1 h3 with h5 | h5
      · exact h5
      · exact absurd h5 hne
    linarith
  -- tp = 1 − t2 − t4 ≥ 0
  have hpxproj : px = (1 - t2 - t4) • cf4Proj (v4 - v2) (-v2) := by
    have h2 : up' = u' := by linarith
    rw [← hpxueq, h2, hu_eq.symm, iProj]
  have htp_eq : tp = 1 - t2 - t4 := by
    have h6 : (1 - t2 - t4) • cf4Proj (v4 - v2) (-v2)
        = tp • cf4Proj (v4 - v2) (-v2) := by
      rw [← hpxeq, hpxproj]
    have h7 : (1 - t2 - t4 - tp) • cf4Proj (v4 - v2) (-v2) = 0 := by
      have h8 : (1 - t2 - t4 - tp) • cf4Proj (v4 - v2) (-v2)
          = (1 - t2 - t4) • cf4Proj (v4 - v2) (-v2)
            - tp • cf4Proj (v4 - v2) (-v2) := by module
      rw [h8, h6, sub_self]
    rcases smul_eq_zero.1 h7 with h9 | h9
    · linarith
    · exact absurd h9 hpu
  refine ⟨x, ⟨u, u', hu, hu', huu, hxueq⟩, cf4_smul_mem_convexHull3 ht2 ht4 ?_ hxeq.symm⟩
  linarith

/-- 勾股恒等式（⊥ d 的 y 与沿 d 的平移）：`‖y + a•d‖² = ‖y‖² + a²‖d‖²`。 -/
private theorem cf4_pyth_axis {d y : V3} (a : ℝ) (hyd : inner ℝ y d = 0) :
    ‖y + a • d‖ ^ 2 = ‖y‖ ^ 2 + a ^ 2 * ‖d‖ ^ 2 := by
  have h1 : ‖y + a • d‖ ^ 2 = inner ℝ (y + a • d) (y + a • d) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [h1, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm y d, hyd, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- HOL `lemma_4_points_rotation2`（CKQOWSA_4.hl:3379-3813）：绕平移轴 v2 + ℝ(v4−v2)
转动 v1（保到 v2、v4 两点距离），把 ‖v1‖ 打到恰 2，交不变量换成凸包形。途经：
凸包分解（u, t2, t4）+ 分离法向（早应用于 v1）+ 残差正交分解（cf4Proj）+
checkpoint 旋转族（cf4_rotation_2_family）+ 平移距离双保（`cf4_pyth_axis`）+
`cf4_projection_dist_le`（‖f t‖ ≤ ‖v1‖ 与 dist(f t,v3) ≤ dist(v1,v3)）+
`cf4_ivt_first_dec`（‖·‖ 下穿 2 打靶）+ `cf4_continuous_lemma_aff_ge`
（交不变量传递，s 处存续）+ 分离法向（再应用于 f s）+ `cf4_segment_inter_conv` 收尾。 -/
private theorem cf4_rotation_2 {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd24 : 2 ≤ dist v2 v4)
    (hcross : (segment ℝ v1 v3 ∩ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))).Nonempty) :
    ∃ v1' : V3, v1' ∈ ballAnnulus ∧ ‖v1'‖ = 2 ∧ dist v1' v3 ≤ 2 * h0 ∧
      dist v1' v2 = dist v1 v2 ∧ dist v1' v4 = dist v1 v4 ∧
      (segment ℝ v1' v3 ∩ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))).Nonempty := by
  -- §0 基本非退化
  have hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    estd_non_collinear_lemma hb2 hb4 hd24 hd24l
  obtain ⟨hv20, hv40, hv24ne⟩ := cf4_not_collinear_smul hcol
  have hv24 : v2 ≠ v4 := fun he => hv24ne 1 (by rw [he, one_smul])
  have hd : v4 - v2 ≠ 0 := fun hcon => hv24 (eq_of_sub_eq_zero hcon).symm
  -- §1 凸包分解
  obtain ⟨x, hxseg, hxhull⟩ := hcross
  obtain ⟨u, u', hu, hu', huu, hxueq⟩ := id hxseg
  obtain ⟨t2, t4, ht2, ht4, hsum, hxeq⟩ :=
    cf4_mem_convexHull3 hv20 hv40 hv24 hxhull
  -- §2 锥形式 + 分离法向（早应用于 v1）
  have hxcone : x ∈ affGe {0} ({v2, v4} : Set V3) :=
    (affGe_0_2_char hv20 hv40 hv24 x).2 ⟨t2, t4, ht2, ht4, hxeq⟩
  obtain ⟨n, hn0, h2n, h4n, h1n, h3n⟩ :=
    cf4_separation_plane_4_points hb1 hb2 hb3 hb4 hd13l hd24l hd24 hd12 hd14 hd23 hd34
      ⟨x, hxseg, hxcone⟩
  -- §3 残差与 dot 事实
  have hdnn : inner ℝ (v4 - v2) n = 0 := by rw [inner_sub_left, h4n, h2n, sub_zero]
  have e1n : inner ℝ (v1 - v2) n = inner ℝ v1 n := by rw [inner_sub_left, h2n, sub_zero]
  have e3n : inner ℝ (v3 - v2) n = inner ℝ v3 n := by rw [inner_sub_left, h2n, sub_zero]
  have eun : inner ℝ (-v2) n = 0 := by rw [inner_neg_left, h2n, neg_zero]
  have hqv0 : cf4Proj (v4 - v2) (v1 - v2) ≠ 0 := by
    intro hzero
    have h1 : inner ℝ (cf4Proj (v4 - v2) (v1 - v2)) n = 0 := by
      rw [hzero, inner_zero_left]
    rw [cf4Proj_dot_n hdnn, e1n] at h1
    rw [h1] at h1n
    norm_num at h1n
  have hqw0 : cf4Proj (v4 - v2) (v3 - v2) ≠ 0 := by
    intro hzero
    have h1 : inner ℝ (cf4Proj (v4 - v2) (v3 - v2)) n = 0 := by
      rw [hzero, inner_zero_left]
    rw [cf4Proj_dot_n hdnn, e3n] at h1
    rw [h1] at h3n
    norm_num at h3n
  have hpu0 : cf4Proj (v4 - v2) (-v2) ≠ 0 := by
    intro hzero
    rw [cf4Proj] at hzero
    have hneg2 : -v2 = (inner ℝ (-v2) (v4 - v2) / ‖v4 - v2‖ ^ 2) • (v4 - v2) :=
      eq_of_sub_eq_zero hzero
    have h5 := congrArg (fun z : V3 => -z) hneg2
    rw [neg_neg, ← neg_smul] at h5
    obtain ⟨k, hk⟩ : ∃ k : ℝ, v2 = k • (v4 - v2) :=
      ⟨-(inner ℝ (-v2) (v4 - v2) / ‖v4 - v2‖ ^ 2), h5⟩
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk0, zero_smul] at hk
      exact hv20 hk
    · have h6 : (k:ℝ)⁻¹ • v2 = v4 - v2 := by
        have h6' := congrArg (fun z : V3 => (k:ℝ)⁻¹ • z) hk
        rw [inv_smul_smul₀ hk0] at h6'
        exact h6'
      apply hv24ne ((k:ℝ)⁻¹ + 1)
      have h8 : (k:ℝ)⁻¹ • v2 + v2 = v4 := by rw [h6]; module
      calc v4 = (k:ℝ)⁻¹ • v2 + v2 := h8.symm
        _ = ((k:ℝ)⁻¹ + 1) • v2 := by module
  have hcolqp : ¬ Collinear ℝ (insert (0:V3)
      ({cf4Proj (v4 - v2) (v1 - v2), cf4Proj (v4 - v2) (-v2)} : Set V3)) := by
    intro hcoll
    obtain ⟨c, hc⟩ := cf4_collinear_smul hqv0 hcoll
    have h1 : inner ℝ (cf4Proj (v4 - v2) (-v2)) n
        = c * inner ℝ (cf4Proj (v4 - v2) (v1 - v2)) n := by
      rw [hc, real_inner_smul_left]
    rw [cf4Proj_dot_n hdnn, cf4Proj_dot_n hdnn, eun, e1n] at h1
    rcases mul_eq_zero.1 h1.symm with h3 | h3
    · rw [h3, zero_smul] at hc
      exact hpu0 hc
    · rw [h3] at h1n
      norm_num at h1n
  -- §4 恒等式 (A) 与其投影（checkpoint 的 segment 穿越）
  have iA : u • (v1 - v2) + u' • (v3 - v2)
      = t4 • (v4 - v2) + (1 - t2 - t4) • (-v2) := by
    have h1 : u • (v1 - v2) + u' • (v3 - v2)
        = (u • v1 + u' • v3) - (u + u') • v2 := by module
    rw [h1, huu, hxueq, hxeq]
    module
  have iProj : u • cf4Proj (v4 - v2) (v1 - v2) + u' • cf4Proj (v4 - v2) (v3 - v2)
      = (1 - t2 - t4) • cf4Proj (v4 - v2) (-v2) := by
    have h0 : cf4Proj (v4 - v2) (v4 - v2) = 0 := cf4Proj_self hd
    have h := congrArg (cf4Proj (v4 - v2)) iA
    rw [cf4Proj_add, cf4Proj_smul, cf4Proj_smul, cf4Proj_add, cf4Proj_smul,
      cf4Proj_smul, h0, smul_zero, zero_add] at h
    exact h
  -- §5 checkpoint 旋转族
  obtain ⟨g, hgcont, hg0, hg1, hgprop, hgdistp, hgdistq, hgcross⟩ :=
    cf4_rotation_2_family (d := v4 - v2) hd hqv0 hqw0 hpu0 cf4Proj_orth cf4Proj_orth
      cf4Proj_orth hcolqp
      ⟨u', 1 - t2 - t4, hu', by linarith, by linarith, by
        rw [show (1:ℝ) - u' = u from by linarith]
        exact iProj⟩
  -- §6 f 的定义与基本性质（平移 + 距离双保 + W2a 两界）
  obtain ⟨lam, hlamv, hlamlam⟩ : ∃ lam : ℝ,
      lam • (v4 - v2) + cf4Proj (v4 - v2) (v1 - v2) = v1 - v2 ∧
      lam = inner ℝ (v1 - v2) (v4 - v2) / ‖v4 - v2‖ ^ 2 :=
    ⟨inner ℝ (v1 - v2) (v4 - v2) / ‖v4 - v2‖ ^ 2, by rw [cf4Proj]; module, rfl⟩
  have hfcont : Continuous (fun t => g t + lam • (v4 - v2) + v2) := by fun_prop
  have hf0 : g 0 + lam • (v4 - v2) + v2 = v1 := by
    rw [hg0]
    have h2 : cf4Proj (v4 - v2) (v1 - v2) + lam • (v4 - v2)
        = lam • (v4 - v2) + cf4Proj (v4 - v2) (v1 - v2) := add_comm _ _
    have h3 : lam • (v4 - v2) + cf4Proj (v4 - v2) (v1 - v2) + v2 = v1 := by
      rw [hlamv]
      module
    rw [h2, h3]
  have hf1n : inner ℝ (g 1 + lam • (v4 - v2) + v2) n = 0 := by
    rw [hg1, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      cf4Proj_dot_n hdnn, eun, hdnn, h2n]
    ring
  have hdist2 : ∀ t, dist (g t + lam • (v4 - v2) + v2) v2 = dist v1 v2 := by
    intro t
    refine sq_eq_sq₀ dist_nonneg dist_nonneg |>.1 ?_
    have e1 : dist (g t + lam • (v4 - v2) + v2) v2 = ‖g t + lam • (v4 - v2)‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      module
    have e2 : dist v1 v2 = ‖cf4Proj (v4 - v2) (v1 - v2) + lam • (v4 - v2)‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      nth_rewrite 1 [← hlamv]
      module
    rw [e1, e2, cf4_pyth_axis lam ((hgprop t).2), cf4_pyth_axis lam cf4Proj_orth,
      (hgprop t).1]
  have hdist4 : ∀ t, dist (g t + lam • (v4 - v2) + v2) v4 = dist v1 v4 := by
    intro t
    refine sq_eq_sq₀ dist_nonneg dist_nonneg |>.1 ?_
    have e1 : dist (g t + lam • (v4 - v2) + v2) v4 = ‖g t + (lam - 1) • (v4 - v2)‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      module
    have e2 : dist v1 v4 = ‖cf4Proj (v4 - v2) (v1 - v2) + (lam - 1) • (v4 - v2)‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      have h9 : v1 - v4
          = lam • (v4 - v2) + cf4Proj (v4 - v2) (v1 - v2) - (v4 - v2) := by
        rw [hlamv]
        module
      rw [h9]
      module
    rw [e1, e2, cf4_pyth_axis (lam - 1) ((hgprop t).2),
      cf4_pyth_axis (lam - 1) cf4Proj_orth, (hgprop t).1]
  have hnormub : ∀ t ∈ Set.Icc 0 1,
      ‖g t + lam • (v4 - v2) + v2‖ ≤ ‖v1‖ := by
    intro t ht
    have h3 := cf4_projection_dist_le hd (hgprop t).2 (hgdistp t ht)
    rw [← hlamlam] at h3
    have h4 : ‖g t + lam • (v4 - v2) + v2‖
        = dist (g t + lam • (v4 - v2)) (-v2) := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      module
    have h5 : dist (v1 - v2) (-v2) = ‖v1‖ := by
      rw [dist_eq_norm]
      refine congrArg norm ?_
      module
    rw [h4]
    exact le_trans h3 h5.le
  have hdist3 : ∀ t ∈ Set.Icc 0 1,
      dist (g t + lam • (v4 - v2) + v2) v3 ≤ 2 * h0 := by
    intro t ht
    have h3 := cf4_projection_dist_le hd (hgprop t).2 (hgdistq t ht)
    rw [← hlamlam] at h3
    have h4 : dist (g t + lam • (v4 - v2) + v2) v3
        = dist (g t + lam • (v4 - v2)) (v3 - v2) := by
      rw [dist_eq_norm, dist_eq_norm]
      refine congrArg norm ?_
      module
    have h5 : dist (v1 - v2) (v3 - v2) = dist v1 v3 := by
      rw [dist_eq_norm, dist_eq_norm]
      refine congrArg norm ?_
      module
    rw [h4]
    exact le_trans h3 (le_trans h5.le hd13l)
  -- §7 情形 A（全程 ‖f t‖ ≥ 2）反证
  have hba : ∀ t ∈ Set.Icc 0 1, 2 ≤ ‖g t + lam • (v4 - v2) + v2‖ →
      g t + lam • (v4 - v2) + v2 ∈ ballAnnulus := by
    intro t ht h2
    obtain ⟨hz1, hz2⟩ := inBallAnnulus hb1
    exact cf4_ballAnnulus_mk (le_trans (hnormub t ht) hz2) h2
  have hnb_gen : ∀ t ∈ Set.Icc 0 1, 2 ≤ ‖g t + lam • (v4 - v2) + v2‖ →
      (0:V3) ∉ segment ℝ (g t + lam • (v4 - v2) + v2) v3 := fun t ht h2 =>
    cf4_not_between_estd (hba t ht h2) hb3 (hdist3 t ht)
  have hstart : (segment ℝ (g 0 + lam • (v4 - v2) + v2) v3
      ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty := by
    rw [hf0]
    exact ⟨x, hxseg, hxcone⟩
  by_cases hall2 : ∀ t ∈ Set.Icc 0 1, 2 ≤ ‖g t + lam • (v4 - v2) + v2‖
  · exfalso
    rcases cf4_continuous_lemma_aff_ge (v1 := v2) (v2 := v4) (w := v3)
        (fun t => g t + lam • (v4 - v2) + v2) 1 (by norm_num) hfcont.continuousOn
        hstart (fun t ht => hnb_gen t ht (hall2 t ht)) hcol with
      hall | ⟨x0, hx00, hx01, hallx, hdisj⟩
    · -- 全程有交：f 1 · n = 0 ⟹ f 1 ∈ 锥（cf4_segment_inter_aff_ge_ends）⟹ L3PF
      obtain ⟨x1, hx1seg, hx1cone⟩ := hall 1 (Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩)
      exact cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4)
        (v3 := g 1 + lam • (v4 - v2) + v2)
        (cf4_segment_inter_aff_ge_ends (v1 := v2) (v2 := v4) hv20 hv40 hv24 h2n h4n
          hf1n (ne_of_gt h3n) ⟨x1, hx1seg, hx1cone⟩)
        hb2 hb4
        (hba 1 (Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩)
          (hall2 1 (Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩))) hd24l
        (by rw [dist_comm, hdist2]; exact hd12)
        (by rw [dist_comm, hdist4]; exact hd14)
    · -- 首穿支三支 L3PF 排空
      have hfx0 : 2 ≤ ‖g x0 + lam • (v4 - v2) + v2‖ :=
        hall2 x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩)
      rcases hdisj with hd1 | hd2 | hd3
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4)
          (v3 := g x0 + lam • (v4 - v2) + v2) hd1 hb2 hb4
          (hba x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩) hfx0) hd24l
          (by rw [dist_comm, hdist2]; exact hd12)
          (by rw [dist_comm, hdist4]; exact hd14)
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := g x0 + lam • (v4 - v2) + v2) (v2 := v3)
          (v3 := v2) hd2 (hba x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩) hfx0) hb3 hb2
          (hdist3 x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩))
          (by rw [hdist2]; exact hd12) (by rw [dist_comm]; exact hd23)
      · exact cf4_LEMMA_3_POINTS_FINAL (v1 := g x0 + lam • (v4 - v2) + v2) (v2 := v3)
          (v3 := v4) hd3 (hba x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩) hfx0) hb3 hb4
          (hdist3 x0 (Set.mem_Icc.2 ⟨hx00, hx01⟩))
          (by rw [hdist4]; exact hd14) hd34
  -- §8 IVT：‖f·‖ 下穿 2 打靶 s
  push_neg at hall2
  obtain ⟨h, hhI, hhl⟩ := hall2
  obtain ⟨s, hs0, hsh, hsn, hsl⟩ :=
    cf4_ivt_first_dec (fun t => ‖g t + lam • (v4 - v2) + v2‖) 2 h hhI.1
      ((hfcont.norm).continuousOn) (by rw [hf0]; exact (inBallAnnulus hb1).1)
      (le_of_lt hhl)
  have hs1 : s ≤ 1 := le_trans hsh hhI.2
  -- §9 continuous_lemma 在 h := s：好分支存续、首穿支排空
  have hge2 : ∀ t ∈ Set.Icc 0 s, 2 ≤ ‖g t + lam • (v4 - v2) + v2‖ := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · rw [heq]
      exact le_of_eq hsn.symm
    · exact le_of_lt (hsl t ⟨ht.1, hlt⟩)
  have hbas : ∀ t ∈ Set.Icc 0 s, g t + lam • (v4 - v2) + v2 ∈ ballAnnulus := by
    intro t ht
    exact hba t (Set.mem_Icc.2 ⟨ht.1, le_trans ht.2 hs1⟩) (hge2 t ht)
  rcases cf4_continuous_lemma_aff_ge (v1 := v2) (v2 := v4) (w := v3)
      (fun t => g t + lam • (v4 - v2) + v2) s hs0
      (hfcont.continuousOn.mono (fun z hz => Set.mem_Icc.2 ⟨hz.1, le_trans hz.2 hs1⟩))
      hstart
      (fun t ht => hnb_gen t (Set.mem_Icc.2 ⟨ht.1, le_trans ht.2 hs1⟩) (hge2 t ht))
      hcol with
    hall | ⟨x0, hx00, hx01, hallx, hdisj⟩
  · -- 好分支：s 处存续交不变量
    obtain ⟨x1, hx1seg, hx1cone⟩ := hall s ⟨hs0, le_refl s⟩
    obtain ⟨n', hn0', h2n', h4n', hfsn, h3n'⟩ :=
      cf4_separation_plane_4_points (hbas s ⟨hs0, le_refl s⟩) hb2 hb3 hb4
        (hdist3 s (Set.mem_Icc.2 ⟨hs0, le_trans (le_refl s) hs1⟩)) hd24l hd24
        (by rw [hdist2]; exact hd12) (by rw [hdist4]; exact hd14) hd23 hd34
        ⟨x1, hx1seg, hx1cone⟩
    have hprojcross : (segment ℝ (cf4Proj (v4 - v2)
          (g s + lam • (v4 - v2) + v2 - v2)) (cf4Proj (v4 - v2) (v3 - v2))
        ∩ affGe {0} ({cf4Proj (v4 - v2) (-v2)} : Set V3)).Nonempty := by
      have h1 : cf4Proj (v4 - v2) (g s + lam • (v4 - v2) + v2 - v2) = g s := by
        have h0 : g s + lam • (v4 - v2) + v2 - v2 = g s + lam • (v4 - v2) := by module
        rw [h0, cf4Proj]
        have hd2p : (0:ℝ) < ‖v4 - v2‖ ^ 2 := pow_pos (norm_pos_iff.2 hd) 2
        have hd2n : ‖v4 - v2‖ ^ 2 ≠ 0 := ne_of_gt hd2p
        have h2 : inner ℝ (g s + lam • (v4 - v2)) (v4 - v2)
            = inner ℝ (g s) (v4 - v2) + lam * ‖v4 - v2‖ ^ 2 := by
          rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        rw [h2, (hgprop s).2, zero_add]
        have hexp : (lam * ‖v4 - v2‖ ^ 2) / ‖v4 - v2‖ ^ 2 = lam := by field_simp
        rw [hexp]
        module
      rw [h1]
      exact hgcross s (Set.mem_Icc.2 ⟨hs0, le_trans hsh hhI.2⟩)
    refine ⟨g s + lam • (v4 - v2) + v2, hbas s ⟨hs0, le_refl s⟩, hsn,
      hdist3 s (Set.mem_Icc.2 ⟨hs0, le_trans (le_refl s) hs1⟩), hdist2 s, hdist4 s, ?_⟩
    exact cf4_segment_inter_conv hv20 hv40 hv24 hpu0 ⟨x1, hx1seg, hx1cone⟩ hfsn h3n'
      h2n' h4n' hprojcross
  · exfalso
    -- 首穿支三支 L3PF 排空
    have hx01' : x0 ∈ Set.Icc 0 1 := ⟨hx00, le_trans hx01 hs1⟩
    have hfx0 : 2 ≤ ‖g x0 + lam • (v4 - v2) + v2‖ := hge2 x0 ⟨hx00, hx01⟩
    rcases hdisj with hd1 | hd2 | hd3
    · exact cf4_LEMMA_3_POINTS_FINAL (v1 := v2) (v2 := v4)
        (v3 := g x0 + lam • (v4 - v2) + v2) hd1 hb2 hb4 (hba x0 hx01' hfx0) hd24l
        (by rw [dist_comm, hdist2]; exact hd12)
        (by rw [dist_comm, hdist4]; exact hd14)
    · exact cf4_LEMMA_3_POINTS_FINAL (v1 := g x0 + lam • (v4 - v2) + v2) (v2 := v3)
        (v3 := v2) hd2 (hba x0 hx01' hfx0) hb3 hb2 (hdist3 x0 hx01')
        (by rw [hdist2]; exact hd12) (by rw [dist_comm]; exact hd23)
    · exact cf4_LEMMA_3_POINTS_FINAL (v1 := g x0 + lam • (v4 - v2) + v2) (v2 := v3)
        (v3 := v4) hd3 (hba x0 hx01' hfx0) hb3 hb4
        (hdist3 x0 hx01')
        (by rw [hdist4]; exact hd14) hd34


/-- HOL `lemma_4_points_rotation2_full`（CKQOWSA_4.hl:3814-3865）：rotation2 两次
（v1 绕平移轴打 ‖·‖ 恰 2、v3 绕同一轴打 ‖·‖ 恰 2），四条到 v2/v4 的距离全部原值保持，
交不变量换成锥形（凸包交点以 (s2, s4) 系数入锥）。 -/
private theorem cf4_rotation_2_full {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd24 : 2 ≤ dist v2 v4)
    (hcross : (segment ℝ v1 v3 ∩ convexHull ℝ (insert (0:V3) ({v2, v4} : Set V3))).Nonempty) :
    ∃ v1' v3' : V3, v1' ∈ ballAnnulus ∧ v3' ∈ ballAnnulus ∧ ‖v1'‖ = 2 ∧ ‖v3'‖ = 2 ∧
      dist v1' v3' ≤ 2 * h0 ∧
      dist v1' v2 = dist v1 v2 ∧ dist v1' v4 = dist v1 v4 ∧
      dist v2 v3' = dist v2 v3 ∧ dist v3' v4 = dist v3 v4 ∧
      (segment ℝ v1' v3' ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty := by
  have hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    estd_non_collinear_lemma hb2 hb4 hd24 hd24l
  obtain ⟨hv20, hv40, hv24ne⟩ := cf4_not_collinear_smul hcol
  have hv24 : v2 ≠ v4 := fun he => hv24ne 1 (by rw [he, one_smul])
  -- 第 1 次：v1 绕平移轴
  obtain ⟨w1, hw1b, hw1n2, hw1d13, hw1d2, hw1d4, hw1cross⟩ :=
    cf4_rotation_2 hb1 hb2 hb3 hb4 hd13l hd24l hd12 hd14 hd23 hd34 hd24 hcross
  -- 第 2 次：v3 绕同一平移轴（w1 作对侧点）
  obtain ⟨w3, hw3b, hw3n2, hw3d13, hw3d2, hw3d4, hw3cross⟩ :=
    cf4_rotation_2 hb3 hb2 hw1b hb4
      (by rw [dist_comm]; exact hw1d13) hd24l (by rw [dist_comm]; exact hd23) hd34
      (by rw [dist_comm, hw1d2]; exact hd12)
      (by rw [hw1d4]; exact hd14)
      hd24
      (by rw [segment_symm]; exact hw1cross)
  refine ⟨w1, w3, hw1b, hw3b, hw1n2, hw3n2, ?_, hw1d2, hw1d4, ?_, hw3d4, ?_⟩
  · rw [dist_comm]
    exact hw3d13
  · rw [dist_comm v2 w3, hw3d2, dist_comm v3 v2]
  · -- 锥交：凸包交点提取系数入锥
    obtain ⟨y, hyseg, hyhull⟩ := hw3cross
    obtain ⟨s2, s4, hs2, hs4, hsum, hyeq2⟩ := cf4_mem_convexHull3 hv20 hv40 hv24 hyhull
    refine ⟨y, ?_, (affGe_0_2_char hv20 hv40 hv24 y).2 ⟨s2, s4, hs2, hs4, hyeq2⟩⟩
    rw [segment_symm]
    exact hyseg


/-! ## W3（四点链 Wave-3）：etaY 盒界 + 外心恒等 + 终局矛盾

HOL 参照（CKQOWSA_4.hl:3866-4092、tame/Inequalities.hl:356-372）：
`lemma_4_points_circumcenter`（:3866-4027）、`PARALLELOGRAM_LAW`（:4028-4034）、
`lemma_4_points_contradiction`（:4035-4092）、外部锚 `ETA_Y_4_POINTS_INEQ`
（Inequalities.hl:356-372，HOL 侧即纯有理数盒式论证——此处以「凹二次逐变量归结
到 8 角点」的单体插值恒等式替代移植，数值 margin 人工预验：角 (4,4,4) 富余 41.6、
最紧角 (6.3504³) 富余 ≈10.07、终局 4·(11/5) + 6.3504 = 15.1504 < 16）。
etaY/etaX 用 IneqClosureDefs 真体、upsX 用 SphereKit 真体（scout 注记：
勿用 PackingAuto21 的 `eta_y` 同名件）。W3a/W3b 为私件；顶件
`cf4_4_points_contradiction` 公开（W4 终件装配消费 + axiom 审计锚）。 -/

/-- **W3a 核心**（HOL `ETA_Y_4_POINTS_INEQ` 的盒式内核，Inequalities.hl:356-372）：
`P a b c := (11/5)·upsX a b c − a·b·c` 在盒 `[4, 6.3504]³` 上非负
（`6.3504 = (2·h0)²`）。`P` 全对称且对每个变元是首项 −11/5 的凹二次，
凹函数最小值在端点 ⟹ 逐变量归结到 8 角点。单体重排恒等式（记 `D := 6.3504 − 4`）：
`D³·P(a,b,c) = Σ_角点 权重·P(角点) + (11/5)·D³·Σ_{u∈{a,b,c}} (u−4)(R−u)`
（由一维恒等式 `p(x) = 弦(x) + q(x−l)(r−x)` 三级迭代而得；ring 验证）。
权重与修正项全部非负、8 个角点值 `norm_num` 收口。 -/
private theorem cf4_etaP_box (a b c : ℝ) (ha : a ∈ Icc (4:ℝ) 6.3504)
    (hb : b ∈ Icc (4:ℝ) 6.3504) (hc : c ∈ Icc (4:ℝ) 6.3504) :
    0 ≤ (11 / 5) * upsX a b c - a * b * c := by
  have wa : 0 ≤ 6.3504 - a := by linarith [ha.2]
  have wap : 0 ≤ a - 4 := by linarith [ha.1]
  have wb : 0 ≤ 6.3504 - b := by linarith [hb.2]
  have wbp : 0 ≤ b - 4 := by linarith [hb.1]
  have wc : 0 ≤ 6.3504 - c := by linarith [hc.2]
  have wcp : 0 ≤ c - 4 := by linarith [hc.1]
  -- 8 个角点值（纯数值）
  have k1 : 0 ≤ (11 / 5) * upsX (4:ℝ) 4 4 - 4 * 4 * 4 := by norm_num [upsX]
  have k2 : 0 ≤ (11 / 5) * upsX (4:ℝ) 4 6.3504 - 4 * 4 * 6.3504 := by norm_num [upsX]
  have k3 : 0 ≤ (11 / 5) * upsX (4:ℝ) 6.3504 4 - 4 * 6.3504 * 4 := by norm_num [upsX]
  have k4 : 0 ≤ (11 / 5) * upsX (6.3504:ℝ) 4 4 - 6.3504 * 4 * 4 := by norm_num [upsX]
  have k5 : 0 ≤ (11 / 5) * upsX (4:ℝ) 6.3504 6.3504 - 4 * 6.3504 * 6.3504 := by
    norm_num [upsX]
  have k6 : 0 ≤ (11 / 5) * upsX (6.3504:ℝ) 4 6.3504 - 6.3504 * 4 * 6.3504 := by
    norm_num [upsX]
  have k7 : 0 ≤ (11 / 5) * upsX (6.3504:ℝ) 6.3504 4 - 6.3504 * 6.3504 * 4 := by
    norm_num [upsX]
  have k8 : 0 ≤ (11 / 5) * upsX (6.3504:ℝ) 6.3504 6.3504 - 6.3504 * 6.3504 * 6.3504 := by
    norm_num [upsX]
  -- 单体插值恒等式（角点值在 simp only [upsX] 后全部折叠为数值系数）
  have key : (6.3504 - 4) ^ 3 * ((11 / 5) * upsX a b c - a * b * c)
      = (6.3504 - a) * (6.3504 - b) * (6.3504 - c)
          * ((11 / 5) * upsX (4:ℝ) 4 4 - 4 * 4 * 4)
      + (a - 4) * (6.3504 - b) * (6.3504 - c)
          * ((11 / 5) * upsX (6.3504:ℝ) 4 4 - 6.3504 * 4 * 4)
      + (6.3504 - a) * (b - 4) * (6.3504 - c)
          * ((11 / 5) * upsX (4:ℝ) 6.3504 4 - 4 * 6.3504 * 4)
      + (6.3504 - a) * (6.3504 - b) * (c - 4)
          * ((11 / 5) * upsX (4:ℝ) 4 6.3504 - 4 * 4 * 6.3504)
      + (a - 4) * (b - 4) * (6.3504 - c)
          * ((11 / 5) * upsX (6.3504:ℝ) 6.3504 4 - 6.3504 * 6.3504 * 4)
      + (a - 4) * (6.3504 - b) * (c - 4)
          * ((11 / 5) * upsX (6.3504:ℝ) 4 6.3504 - 6.3504 * 4 * 6.3504)
      + (6.3504 - a) * (b - 4) * (c - 4)
          * ((11 / 5) * upsX (4:ℝ) 6.3504 6.3504 - 4 * 6.3504 * 6.3504)
      + (a - 4) * (b - 4) * (c - 4)
          * ((11 / 5) * upsX (6.3504:ℝ) 6.3504 6.3504
            - 6.3504 * 6.3504 * 6.3504)
      + (11 / 5) * (6.3504 - 4) ^ 3
          * ((a - 4) * (6.3504 - a) + (b - 4) * (6.3504 - b)
            + (c - 4) * (6.3504 - c)) := by
    simp only [upsX]
    ring
  -- 角点项（权重 × 角点值，双双非负）
  have p1 : 0 ≤ (6.3504 - a) * (6.3504 - b) * (6.3504 - c)
      * ((11 / 5) * upsX (4:ℝ) 4 4 - 4 * 4 * 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg wa wb) wc) k1
  have p2 : 0 ≤ (a - 4) * (6.3504 - b) * (6.3504 - c)
      * ((11 / 5) * upsX (6.3504:ℝ) 4 4 - 6.3504 * 4 * 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg wap wb) wc) k4
  have p3 : 0 ≤ (6.3504 - a) * (b - 4) * (6.3504 - c)
      * ((11 / 5) * upsX (4:ℝ) 6.3504 4 - 4 * 6.3504 * 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg wa wbp) wc) k3
  have p4 : 0 ≤ (6.3504 - a) * (6.3504 - b) * (c - 4)
      * ((11 / 5) * upsX (4:ℝ) 4 6.3504 - 4 * 4 * 6.3504) :=
    mul_nonneg (mul_nonneg (mul_nonneg wa wb) wcp) k2
  have p5 : 0 ≤ (a - 4) * (b - 4) * (6.3504 - c)
      * ((11 / 5) * upsX (6.3504:ℝ) 6.3504 4 - 6.3504 * 6.3504 * 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg wap wbp) wc) k7
  have p6 : 0 ≤ (a - 4) * (6.3504 - b) * (c - 4)
      * ((11 / 5) * upsX (6.3504:ℝ) 4 6.3504 - 6.3504 * 4 * 6.3504) :=
    mul_nonneg (mul_nonneg (mul_nonneg wap wb) wcp) k6
  have p7 : 0 ≤ (6.3504 - a) * (b - 4) * (c - 4)
      * ((11 / 5) * upsX (4:ℝ) 6.3504 6.3504 - 4 * 6.3504 * 6.3504) :=
    mul_nonneg (mul_nonneg (mul_nonneg wa wbp) wcp) k5
  have p8 : 0 ≤ (a - 4) * (b - 4) * (c - 4)
      * ((11 / 5) * upsX (6.3504:ℝ) 6.3504 6.3504
        - 6.3504 * 6.3504 * 6.3504) :=
    mul_nonneg (mul_nonneg (mul_nonneg wap wbp) wcp) k8
  have corr : 0 ≤ (11 / 5) * (6.3504 - 4) ^ 3
      * ((a - 4) * (6.3504 - a) + (b - 4) * (6.3504 - b)
        + (c - 4) * (6.3504 - c)) := by
    have h1c : (0:ℝ) ≤ (11:ℝ) / 5 * ((6.3504:ℝ) - 4) ^ 3 := by norm_num
    have h2c : 0 ≤ (a - 4) * (6.3504 - a) := mul_nonneg wap wa
    have h3c : 0 ≤ (b - 4) * (6.3504 - b) := mul_nonneg wbp wb
    have h4c : 0 ≤ (c - 4) * (6.3504 - c) := mul_nonneg wcp wc
    exact mul_nonneg h1c (add_nonneg (add_nonneg h2c h3c) h4c)
  -- 收口：D³ > 0 消去因子
  have hd3 : (0:ℝ) < ((6.3504:ℝ) - 4) ^ 3 := by norm_num
  have hzero : 0 ≤ (6.3504 - 4) ^ 3 * ((11 / 5) * upsX a b c - a * b * c) := by
    linarith [key, p1, p2, p3, p4, p5, p6, p7, p8, corr]
  rcases lt_or_ge ((11 / 5) * upsX a b c - a * b * c) 0 with hneg | hge
  · exfalso
    have hmul : (6.3504 - 4) ^ 3 * ((11 / 5) * upsX a b c - a * b * c) < 0 := by
      have h1 := mul_lt_mul_of_pos_left hneg hd3
      rwa [mul_zero] at h1
    linarith
  · exact hge

/-- **W3a**（HOL `ETA_Y_4_POINTS_INEQ`，Inequalities.hl:356-372）：
`y₁, y₂, y₃ ∈ [2, 2·h0]` ⟹ `etaY y₁ y₂ y₃ ^ 2 ≤ 11 / 5`（= 2.2）。
x_i := y_i² ∈ [4, 6.3504]（mul_le_mul 两侧平方 + `2·h0 = 2.52`），盒不等式
x₁x₂x₃ ≤ (11/5)·upsX x₁x₂x₃（`cf4_etaP_box`），etaY² = x₁x₂x₃/upsX
（etaX/etaY 定义展开 + `Real.sqrt_sq`）。 -/
private theorem cf4_etaY_box (y1 y2 y3 : ℝ) (hy1 : y1 ∈ Icc (2:ℝ) (2 * h0))
    (hy2 : y2 ∈ Icc (2:ℝ) (2 * h0)) (hy3 : y3 ∈ Icc (2:ℝ) (2 * h0)) :
    etaY y1 y2 y3 ^ 2 ≤ 11 / 5 := by
  have hsq : (2:ℝ) * h0 * (2 * h0) = 6.3504 := by rw [two_h0]; norm_num
  have h1m : y1 * y1 ∈ Icc (4:ℝ) 6.3504 := by
    constructor
    · have h := le_trans (mul_le_mul_of_nonneg_left hy1.1 (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_right hy1.1 (le_trans (by norm_num : (0:ℝ) ≤ 2) hy1.1))
      norm_num at h
      exact h
    · have h := le_trans (mul_le_mul_of_nonneg_right hy1.2
          (le_trans (by norm_num : (0:ℝ) ≤ 2) hy1.1))
        (mul_le_mul_of_nonneg_left hy1.2 (by norm_num [h0]))
      rwa [hsq] at h
  have h2m : y2 * y2 ∈ Icc (4:ℝ) 6.3504 := by
    constructor
    · have h := le_trans (mul_le_mul_of_nonneg_left hy2.1 (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_right hy2.1 (le_trans (by norm_num : (0:ℝ) ≤ 2) hy2.1))
      norm_num at h
      exact h
    · have h := le_trans (mul_le_mul_of_nonneg_right hy2.2
          (le_trans (by norm_num : (0:ℝ) ≤ 2) hy2.1))
        (mul_le_mul_of_nonneg_left hy2.2 (by norm_num [h0]))
      rwa [hsq] at h
  have h3m : y3 * y3 ∈ Icc (4:ℝ) 6.3504 := by
    constructor
    · have h := le_trans (mul_le_mul_of_nonneg_left hy3.1 (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_right hy3.1 (le_trans (by norm_num : (0:ℝ) ≤ 2) hy3.1))
      norm_num at h
      exact h
    · have h := le_trans (mul_le_mul_of_nonneg_right hy3.2
          (le_trans (by norm_num : (0:ℝ) ≤ 2) hy3.1))
        (mul_le_mul_of_nonneg_left hy3.2 (by norm_num [h0]))
      rwa [hsq] at h
  have hPpos : 0 < y1 * y1 * (y2 * y2) * (y3 * y3) :=
    mul_pos (mul_pos (mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy1.1)
        (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy1.1))
      (mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy2.1)
        (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy2.1)))
      (mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy3.1)
        (lt_of_lt_of_le (by norm_num : (0:ℝ) < (2:ℝ)) hy3.1))
  have hbox : 0 ≤ (11 / 5) * upsX (y1 * y1) (y2 * y2) (y3 * y3)
      - y1 * y1 * (y2 * y2) * (y3 * y3) :=
    cf4_etaP_box (y1 * y1) (y2 * y2) (y3 * y3) h1m h2m h3m
  have hQpos : 0 < upsX (y1 * y1) (y2 * y2) (y3 * y3) := by
    by_contra hcon
    push_neg at hcon
    have h2 : (11 / 5) * upsX (y1 * y1) (y2 * y2) (y3 * y3) ≤ 0 := by
      calc (11 / 5) * upsX (y1 * y1) (y2 * y2) (y3 * y3)
          ≤ (11 / 5) * 0 := mul_le_mul_of_nonneg_left hcon (by norm_num)
        _ = 0 := by ring
    linarith
  have hdiv : y1 * y1 * (y2 * y2) * (y3 * y3)
      / upsX (y1 * y1) (y2 * y2) (y3 * y3) ≤ 11 / 5 := by
    rw [div_le_iff₀ hQpos]
    linarith
  have hetasq : etaY y1 y2 y3 ^ 2
      = y1 * y1 * (y2 * y2) * (y3 * y3)
        / upsX (y1 * y1) (y2 * y2) (y3 * y3) := by
    simp only [etaY, etaX]
    exact Real.sq_sqrt (div_nonneg hPpos.le hQpos.le)
  rwa [hetasq]

/-- **W3b**（HOL `lemma_4_points_circumcenter`，CKQOWSA_4.hl:3866-4027）：
`{0, v2, v4}` 非共线、segment[v1,v3] 穿锥 {v2,v4}、‖v1‖ = ‖v3‖ = 2、四条交叉
距离恰 2 ⟹ `‖v1 + v3‖ = 2·etaY ‖v2‖ ‖v4‖ (dist v2 v4)`（中点
`m := (v1+v3)/2` 为三角形 {0,v2,v4} 的外心，‖m‖ 即外接圆半径 = etaY 式）。

途径（对 HOL 的显式重排）：cf4_dot_of_dist2 ×4 ⟹ `m·v2 = ‖v2‖²/2`、
`m·v4 = ‖v4‖²/2`；交点 `x` 两种表示的内积比较给 `(4 − ⟨v1,v3⟩)·(u − u′) = 0`：
`u = u′` 主支 `m = x` 入锥；`⟨v1,v3⟩ = 4` 退化支经 cf4_norm_sq_sub 归零得
`v1 = v3` 仍 `m = x`。半径式：`m = s₂•v2 + s₄•v4` 与两条 dot 方程线性组合解出
`s₂·2g = b(a−cv)`、`s₄·2g = a(b−cv)`（`g := a·b − cv² > 0`，平行性由非共线
排除），得 `‖m‖²·4g = a·b·(a+b−2cv)`；`upsX a b (a+b−2cv) = 4g` 收口。 -/
private theorem cf4_4pts_circumcenter {v1 v2 v3 v4 : V3}
    (hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)))
    (hseg : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty)
    (hn1 : ‖v1‖ = 2) (hn3 : ‖v3‖ = 2)
    (hd12 : dist v1 v2 = 2) (hd14 : dist v1 v4 = 2)
    (hd32 : dist v3 v2 = 2) (hd34 : dist v3 v4 = 2) :
    ‖v1 + v3‖ = 2 * etaY ‖v2‖ ‖v4‖ (dist v2 v4) := by
  obtain ⟨hv20, hv40, hpar⟩ := cf4_not_collinear_smul hcol
  have hv24 : v2 ≠ v4 := fun he => hpar 1 (by rw [he, one_smul])
  -- 四条交叉距离的 dot 事实（HOL :3870-3882 首子目标，cf4_dot_of_dist2 ×4）
  have d12 := cf4_dot_of_dist2 hn1 hd12
  have d14 := cf4_dot_of_dist2 hn1 hd14
  have d32 := cf4_dot_of_dist2 hn3 hd32
  have d34 := cf4_dot_of_dist2 hn3 hd34
  -- 中点 m 与两条 dot 恒等式
  obtain ⟨m, hm⟩ : ∃ z : V3, z = ((1:ℝ) / 2) • (v1 + v3) := ⟨_, rfl⟩
  have hA2 : inner ℝ m v2 = ‖v2‖ ^ 2 / 2 := by
    rw [hm, real_inner_smul_left, inner_add_left, d12, d32]
    ring
  have hA4 : inner ℝ m v4 = ‖v4‖ ^ 2 / 2 := by
    rw [hm, real_inner_smul_left, inner_add_left, d14, d34]
    ring
  -- m 落锥：交点 x 的 segment 表示与锥表示的内积比较（HOL :3940-3990）
  obtain ⟨x, hxseg, hxcone⟩ := hseg
  obtain ⟨u, u', hu, hu', huu, hxeq⟩ := hxseg
  obtain ⟨t2, t4, ht2, ht4, hxc⟩ := (affGe_0_2_char hv20 hv40 hv24 x).1 hxcone
  have eX1 : inner ℝ x v1 = u * 4 + u' * inner ℝ v1 v3 := by
    rw [← hxeq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hn1, real_inner_comm v3 v1]
    ring
  have eX3 : inner ℝ x v3 = u * inner ℝ v1 v3 + u' * 4 := by
    rw [← hxeq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hn3]
    ring
  have eC1 : inner ℝ x v1 = t2 * inner ℝ v2 v1 + t4 * inner ℝ v4 v1 := by
    rw [hxc, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have eC3 : inner ℝ x v3 = t2 * inner ℝ v2 v3 + t4 * inner ℝ v4 v3 := by
    rw [hxc, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hXX : inner ℝ x v1 = inner ℝ x v3 := by
    rw [eC1, eC3, real_inner_comm v1 v2, d12, real_inner_comm v1 v4, d14,
      real_inner_comm v3 v2, d32, real_inner_comm v3 v4, d34]
  have hkey : (4 - inner ℝ v1 v3) * (u - u') = 0 := by
    have h1 : inner ℝ x v1 - inner ℝ x v3 = (4 - inner ℝ v1 v3) * (u - u') := by
      rw [eX1, eX3]
      ring
    rw [← h1, hXX, sub_self]
  have hmcone : m ∈ affGe {0} ({v2, v4} : Set V3) := by
    rcases mul_eq_zero.1 hkey with hca | hcb
    · -- ⟨v1,v3⟩ = 4 退化支：v1 = v3（C–S 等号），仍 m = x
      have hAeq : inner ℝ v1 v3 = 4 := by linarith
      have hv13 : v1 = v3 := by
        have hzero : ‖v1 - v3‖ ^ 2 = 0 := by
          rw [cf4_norm_sq_sub, hn1, hn3, hAeq]
          ring
        exact eq_of_sub_eq_zero (norm_eq_zero.1 (sq_eq_zero_iff.1 hzero))
      have hxv1 : x = v1 := by
        rw [← hxeq, hv13, ← add_smul, huu, one_smul]
      have hmv1 : m = v1 := by
        rw [hm, hv13, smul_add, ← add_smul,
          show ((1:ℝ) / 2 + (1:ℝ) / 2) = 1 from by norm_num, one_smul]
      exact (affGe_0_2_char hv20 hv40 hv24 m).2
        ⟨t2, t4, ht2, ht4, by rw [hmv1, ← hxc, hxv1]⟩
    · -- u = u′ 主支：m = x = (1/2)•(v1+v3)
      have hcb' : u = u' := sub_eq_zero.1 hcb
      have hmx : m = x := by
        rw [hm, ← hxeq, ← hcb', ← smul_add,
          show u = (1:ℝ) / 2 from by linarith]
      exact (affGe_0_2_char hv20 hv40 hv24 m).2
        ⟨t2, t4, ht2, ht4, by rw [hmx]; exact hxc⟩
  -- 半径式：a := ‖v2‖², b := ‖v4‖², cv := ⟨v2,v4⟩, x3 := dist v2 v4²
  obtain ⟨a, ha⟩ : ∃ z, z = ‖v2‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ z, z = ‖v4‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ z, z = inner ℝ v2 v4 := ⟨_, rfl⟩
  obtain ⟨x3, hx3def⟩ : ∃ z, z = dist v2 v4 ^ 2 := ⟨_, rfl⟩
  have hn20 : ‖v2‖ ≠ 0 := fun he => hv20 (norm_eq_zero.1 he)
  have hn40 : ‖v4‖ ≠ 0 := fun he => hv40 (norm_eq_zero.1 he)
  have hap : 0 < a := by
    rw [ha, pow_two]
    exact mul_pos (lt_of_le_of_ne (norm_nonneg v2) (Ne.symm hn20))
      (lt_of_le_of_ne (norm_nonneg v2) (Ne.symm hn20))
  have hbp : 0 < b := by
    rw [hb, pow_two]
    exact mul_pos (lt_of_le_of_ne (norm_nonneg v4) (Ne.symm hn40))
      (lt_of_le_of_ne (norm_nonneg v4) (Ne.symm hn40))
  have hane : (a:ℝ) ≠ 0 := ne_of_gt hap
  -- x3 = a + b − 2·cv
  have hx3 : x3 = a + b - 2 * cv := by
    rw [hx3def, dist_eq_norm, cf4_norm_sq_sub, ← hcv, ← ha, ← hb]
    ring
  -- Gram 行列式 g := a·b − cv² > 0（缩放差向量恒等式，平行性由 hpar 排除）
  have hcomp3 : ‖(a:ℝ) • v4 - cv • v2‖ ^ 2 = a * (a * b - cv * cv) := by
    rw [cf4_norm_sq_sub]
    have e1 : ‖(a:ℝ) • v4‖ ^ 2 = a ^ 2 * b := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← hb]
    have e2 : ‖cv • v2‖ ^ 2 = cv ^ 2 * a := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← ha]
    have e3 : inner ℝ ((a:ℝ) • v4) (cv • v2) = a * cv * cv := by
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm v2 v4,
        ← hcv, mul_assoc]
    rw [e1, e3, e2]
    ring
  have hgg : 0 < a * b - cv * cv := by
    have hge : 0 ≤ a * b - cv * cv := by
      rcases lt_or_ge (a * b - cv * cv) 0 with hneg | hge0
      · exfalso
        have hsq : 0 ≤ ‖(a:ℝ) • v4 - cv • v2‖ ^ 2 := sq_nonneg _
        rw [hcomp3] at hsq
        have hneg' := mul_lt_mul_of_pos_left hneg hap
        rw [mul_zero] at hneg'
        linarith
      · exact hge0
    have hgne : a * b - cv * cv ≠ 0 := by
      intro h0
      have h2 : ‖(a:ℝ) • v4 - cv • v2‖ ^ 2 = 0 := by rw [hcomp3, h0, mul_zero]
      have h4 : (a:ℝ) • v4 - cv • v2 = 0 := norm_eq_zero.1 (sq_eq_zero_iff.1 h2)
      have h6 : (a:ℝ) • v4 = cv • v2 := eq_of_sub_eq_zero h4
      -- v2 与 v4 平行 ⟹ 与线性无关矛盾（cf4_repr_unique 给 cv = 0 ∧ a = 0）
      have hlin : LinearIndependent ℝ ![v2, v4] := cf4_linearIndependent_pair hcol
      have hpair1 : (0:ℝ) • v2 + (a:ℝ) • v4 = cv • v2 := by
        rw [zero_smul, zero_add, h6]
      have hpair2 : cv • v2 + (0:ℝ) • v4 = cv • v2 := by
        rw [zero_smul, add_zero]
      exact hane (cf4_repr_unique hlin hpair1 hpair2).2
    exact lt_of_le_of_ne hge (Ne.symm hgne)
  -- m 的锥表示与两条 dot 方程
  obtain ⟨s2, s4, hs2, hs4, hme⟩ := (affGe_0_2_char hv20 hv40 hv24 m).1 hmcone
  have eq2 : s2 * a + s4 * cv = a / 2 := by
    have h1 : inner ℝ m v2 = s2 * inner ℝ v2 v2 + s4 * inner ℝ v4 v2 := by
      rw [hme, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hA2] at h1
    rw [real_inner_self_eq_norm_sq, ← ha] at h1
    rw [real_inner_comm v2 v4, ← hcv] at h1
    linarith
  have eq4 : s2 * cv + s4 * b = b / 2 := by
    have h1 : inner ℝ m v4 = s2 * inner ℝ v2 v4 + s4 * inner ℝ v4 v4 := by
      rw [hme, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hA4] at h1
    rw [real_inner_self_eq_norm_sq, ← hb] at h1
    rw [← hcv] at h1
    linarith
  have eqm : ‖m‖ ^ 2 = s2 * (a / 2) + s4 * (b / 2) := by
    have h1 : inner ℝ m (s2 • v2 + s4 • v4) = s2 * (a / 2) + s4 * (b / 2) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hA2, ← ha, hA4, ← hb]
    rw [← hme] at h1
    rw [← real_inner_self_eq_norm_sq]
    exact h1
  -- 线性组合求解 s2、s4（2b·eq2 − 2cv·eq4 / 2a·eq4 − 2cv·eq2）
  have key1 : s2 * (2 * (a * b - cv * cv)) = b * (a - cv) := by
    linear_combination (2 * b) * eq2 - (2 * cv) * eq4
  have key2 : s4 * (2 * (a * b - cv * cv)) = a * (b - cv) := by
    linear_combination (2 * a) * eq4 - (2 * cv) * eq2
  have key3 : ‖m‖ ^ 2 * (4 * (a * b - cv * cv)) = a * b * x3 := by
    rw [eqm, hx3]
    linear_combination a * key1 + b * key2
  -- 收口：upsX a b x3 = 4g ⟹ ‖m‖² = a·b·x3 / upsX（= etaY²）
  have hups : upsX a b x3 = 4 * (a * b - cv * cv) := by
    rw [hx3]
    simp only [upsX]
    ring
  have hupspos : upsX a b x3 ≠ 0 := by
    rw [hups]
    exact ne_of_gt (mul_pos (by norm_num) hgg)
  have hsqm : ‖m‖ ^ 2 * upsX a b x3 = a * b * x3 := by
    rw [hups, key3]
  have hdiv : a * b * x3 / upsX a b x3 = ‖m‖ ^ 2 := by
    rw [div_eq_iff hupspos, hsqm]
  have hetasq : etaY ‖v2‖ ‖v4‖ (dist v2 v4) = ‖m‖ := by
    simp only [etaY, etaX]
    rw [show ‖v2‖ * ‖v2‖ = ‖v2‖ ^ 2 from (pow_two ‖v2‖).symm,
        show ‖v4‖ * ‖v4‖ = ‖v4‖ ^ 2 from (pow_two ‖v4‖).symm,
        show dist v2 v4 * dist v2 v4 = dist v2 v4 ^ 2 from (pow_two (dist v2 v4)).symm,
        ← ha, ← hb, ← hx3def, hdiv, Real.sqrt_sq (norm_nonneg m)]
  -- 终目标：‖v1+v3‖ = 2·‖m‖ = 2·etaY …
  have h2m : v1 + v3 = (2:ℝ) • m := by
    rw [hm, smul_smul, show (2:ℝ) * ((1:ℝ) / 2) = 1 from by norm_num, one_smul]
  rw [h2m, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 2), hetasq]

/-- **W3c**（HOL `lemma_4_points_contradiction`，CKQOWSA_4.hl:4035-4092；
`PARALLELOGRAM_LAW` :4028-4034）：环带 v2、v4、`2 ≤ dist v2 v4 ≤ 2·h0`、
segment[v1,v3] 穿锥、‖v1‖ = ‖v3‖ = 2、四条交叉距离恰 2、dist v1 v3 ≤ 2·h0
⟹ False。平行四边形恒等式 `‖v1+v3‖² + ‖v1−v3‖² = 2(‖v1‖²+‖v3‖²) = 16`，
W3b 给 `‖v1+v3‖² = 4·etaY²`、W3a 给 `etaY² ≤ 11/5`、dist² ≤ (2·h0)² = 6.3504：
`4·(11/5) + 6.3504 = 15.1504 < 16` 矛盾。 -/
theorem cf4_4_points_contradiction {v1 v2 v3 v4 : V3}
    (hb2 : v2 ∈ ballAnnulus) (hb4 : v4 ∈ ballAnnulus)
    (hd24l : dist v2 v4 ≤ 2 * h0) (hd24 : 2 ≤ dist v2 v4)
    (hseg : (segment ℝ v1 v3 ∩ affGe {0} ({v2, v4} : Set V3)).Nonempty)
    (hn1 : ‖v1‖ = 2) (hn3 : ‖v3‖ = 2)
    (hd12 : dist v1 v2 = 2) (hd14 : dist v1 v4 = 2)
    (hd32 : dist v3 v2 = 2) (hd34 : dist v3 v4 = 2)
    (hd13l : dist v1 v3 ≤ 2 * h0) : False := by
  have hcol : ¬ Collinear ℝ (insert (0:V3) ({v2, v4} : Set V3)) :=
    estd_non_collinear_lemma hb2 hb4 hd24 hd24l
  have hcc := cf4_4pts_circumcenter hcol hseg hn1 hn3 hd12 hd14 hd32 hd34
  obtain ⟨hv2, hv2u⟩ := inBallAnnulus hb2
  obtain ⟨hv4, hv4u⟩ := inBallAnnulus hb4
  have hbox := cf4_etaY_box ‖v2‖ ‖v4‖ (dist v2 v4) ⟨hv2, hv2u⟩ ⟨hv4, hv4u⟩
    ⟨hd24, hd24l⟩
  have h1 : ‖v1 + v3‖ ^ 2 ≤ 4 * (11 / 5) := by
    rw [hcc, show (2 * etaY ‖v2‖ ‖v4‖ (dist v2 v4)) ^ 2
      = 4 * (etaY ‖v2‖ ‖v4‖ (dist v2 v4)) ^ 2 from by ring]
    exact mul_le_mul_of_nonneg_left hbox (by norm_num)
  have hdn : dist v1 v3 = ‖v1 - v3‖ := dist_eq_norm v1 v3
  have h2 : ‖v1 - v3‖ ^ 2 ≤ 6.3504 := by
    have hd : ‖v1 - v3‖ ≤ 2 * h0 := by rw [← hdn]; exact hd13l
    have hs : ‖v1 - v3‖ * ‖v1 - v3‖ ≤ (2:ℝ) * h0 * (2 * h0) :=
      le_trans (mul_le_mul_of_nonneg_right hd (norm_nonneg (v1 - v3)))
        (mul_le_mul_of_nonneg_left hd (by norm_num [h0]))
    rw [← pow_two (‖v1 - v3‖), ← pow_two ((2:ℝ) * h0), two_h0] at hs
    norm_num at hs
    linarith
  have hpara : ‖v1 + v3‖ ^ 2 + ‖v1 - v3‖ ^ 2 = 16 := by
    have e1 : ‖v1 + v3‖ ^ 2 = ‖v1‖ ^ 2 + ‖v3‖ ^ 2 + 2 * inner ℝ v1 v3 := by
      rw [← real_inner_self_eq_norm_sq (v1 + v3), inner_add_left, inner_add_right,
        inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm v1 v3]
      ring
    have e2 := cf4_norm_sq_sub v1 v3
    have n1 : ‖v1‖ ^ 2 = 4 := by rw [hn1]; norm_num
    have n3 : ‖v3‖ ^ 2 = 4 := by rw [hn3]; norm_num
    linarith [e1, e2, n1, n3]
  have hle : ‖v1 + v3‖ ^ 2 + ‖v1 - v3‖ ^ 2 ≤ 4 * (11 / 5) + 6.3504 :=
    add_le_add h1 h2
  rw [hpara] at hle
  exact absurd hle (by norm_num)


end Kepler.Text.ContraFanDeep
