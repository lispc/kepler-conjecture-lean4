/-
  Kepler/Text/ContraFan — CKQOWSA 章移植：`(V, ESTD V)` 是 fan。

  HOL 参照（/dev/shm/kepler-ref/flyspeck/text_formalization/）：
  - `tame/CKQOWSA.hl`（module Ckqowsa，:1-580）：主章
    （ESTD_fan0/fan1/fan2/fan6、fan7_2/fan7_3/fan7_4_0/fan7_4_1_one_case/
    fan7_4_1_cases/fan7_4_1/fan7_4_2、ESTD_fan7、CKQOWSA）；
  - `tame/CKQOWSA_3.hl`（module Ckqowsa_3_points）：aff_ge_0_2 显式锥、
    dot_pos_lemma、LEMMA_3_POINTS(_FINAL) 链；
  - `tame/CKQOWSA_4.hl`（module Ckqowsa_4_points）：estd_non_collinear_lemma、
    points_in_aff_ge_0_2、LEMMA_4_POINTS_FINAL 链。

  用途：`Kepler.Text.TameLp.contravening_fanTl`（CONTRAVENING_FAN twin，
  contravening→lp_fan 桥链唯一缺口）的证明内核；下轮中央接线时
  TameLp 反向 import 本模块，故本模块不得 import TameLp。

  接口注记：本模块 `ESTD` 与 `Kepler.Text.TameLp.ESTD`（TameLp.lean:308）、
  `Kepler.Assembly.ESTD`（Assembly.lean:41）同体（`exact` 级 definitional
  unfolding 可互换）。`contraveningFanTl` 的三前提由 `Contravening V` 直接
  给出：`hpack = hc.1`、`hann = hc.2.1`、`hne` 由 `V.ncard = 13 ∨ 14 ∨ 15`
  （或 `scriptL V > 12` 加 scriptL 空集取 0）得到。

  移植状态（2026-09-21 工位）：
  - 真证明：inBallAnnulus、affGe_0_1_char / affGe_0_2_char / affGe_0_empty /
    affGe_0_subset（aff_ge_0_2 与 HALFLINE 的 twin）、annulus_ray_absurd、
    dot_pos_lemma（CKQOWSA_3:1071）、estd_non_collinear_lemma（CKQOWSA_4:45）、
    ESTD_fan0/fan1/fan2/fan6、fan7_2、fan7_3、fan7_4_0、fan7_4_1_cases、
    fan7_4_1_one_case、fan7_4_1、fan7_4_2、ESTD_fan7、CKQOWSA、
    contraveningFanTl；
  - sorry（深几何核，仅陈述 + DISCHARGES 注记）：`LEMMA_3_POINTS_FINAL`
    （CKQOWSA_3.hl:1350-1356）、`LEMMA_4_POINTS_FINAL`
    （CKQOWSA_4.hl:4093-4096）。二者的 HOL 依赖链（LEMMA_3_POINTS:1306 ←
    lemma_3_points:1147（IVT :1106）← rotation_lemma:828 ← 投影/三角链；
    LEMMA_4_POINTS_FINAL ← lemma_4_points_contradiction:4035 ←
    lemma_4_points_circumcenter:3866 ← 旋转段相交链 + ETA_Y_4_POINTS_INEQ）
    约 4700 行，属后续轮次。
-/
import Kepler.Text.Fan
import Kepler.Text.PackingAuto2
import Kepler.Geom.Aff

open Kepler.Geom
open Kepler.Text.Fan
open Kepler.Text
open Kepler
open Set Metric
open Classical

namespace Kepler.Text.ContraFan

/-! ## 0. 基础孪生定义 -/

/-- HOL `ESTD`（`tame/tame_defs.hl:191-192`）。与 `Kepler.Text.TameLp.ESTD`、
`Kepler.Assembly.ESTD` 同体（definitional unfolding 可互换）。 -/
def ESTD (V : Set V3) : Set (Set V3) :=
  {e | ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w ≤ 2 * h0}

theorem mem_ESTD {V : Set V3} {e : Set V3} :
    e ∈ ESTD V ↔ ∃ v w : V3, e = {v, w} ∧ v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ dist v w ≤ 2 * h0 :=
  Iff.rfl

/-- HOL `in_ball_annulus`（CKQOWSA_3.hl:33-34）。 -/
theorem inBallAnnulus {v : V3} (hv : v ∈ ballAnnulus) : 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  simp only [ballAnnulus, Set.mem_diff, Set.mem_singleton_iff, mem_closedBall, mem_ball,
    dist_zero_right, not_lt] at hv
  exact ⟨hv.2, hv.1⟩

/-- HOL `h0`（pack_defs.hl:147）的数值。 -/
theorem two_h0 : (2 : ℝ) * h0 = 2.52 := by norm_num [h0]

/-! ## 1. affGe {0} 的显式刻画（aff_ge_0_2 / HALFLINE 的 twin）

HOL：`aff_ge_0_2`（CKQOWSA_3.hl:115-142）、`HALFLINE`、`points_in_aff_ge_0_2`
（CKQOWSA_4.hl:313-336）。单点情形无条件成立（v = 0 时两侧同为 {0}）；两点
情形需端点非零（v1 = 0 时 `affGe {0} {0,v2}` 是线段而非射线，恰为 HOL 加
非零假设的原因）。 -/

private theorem finset_union_pair {a b c : V3}
    (hfin : (({a} : Set V3) ∪ {b, c}).Finite) :
    hfin.toFinset = ({a, b, c} : Finset V3) := by
  ext z
  simp [Set.Finite.mem_toFinset] <;> tauto

private theorem fin_sum_two {M : Type*} [AddCommMonoid M] {g : V3 → M} {a b : V3}
    (hne : a ≠ b) :
    ∑ z ∈ ({a, b} : Finset V3), g z = g a + g b := by
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]

private theorem fin_sum_three {M : Type*} [AddCommMonoid M] {g : V3 → M} {a b c : V3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ z ∈ ({a, b, c} : Finset V3), g z = g a + g b + g c := by
  rw [Finset.sum_insert (by simp [hab, hac] : (a : V3) ∉ ({b, c} : Finset V3)),
    fin_sum_two hbc, add_assoc]

/-- `y ∈ affGe {0} {v}` 的显式刻画（HOL `HALFLINE`/`AFF_GE_1_1` 在 `x = 0`
的组合形式；无条件版：v = 0 时两侧同为 `y = 0`）。 -/
theorem affGe_0_1_char (v y : V3) :
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

/-- `y ∈ affGe {0} {v1, v2}` 的显式二系数刻画（HOL `aff_ge_0_2`
CKQOWSA_3.hl:115-142 的组合形式；非退化假设与 HOL 一致）。 -/
theorem affGe_0_2_char {v1 v2 : V3} (h01 : v1 ≠ 0) (h02 : v2 ≠ 0) (h12 : v1 ≠ v2)
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

/-- `affGe {0} ∅ = {0}`（CKQOWSA.hl:115 的 `AFF_GE_EQ_AFFINE_HULL` +
`AFFINE_HULL_SING` 改写在 `x = 0` 的形式）。 -/
theorem affGe_0_empty : affGe {0} (∅ : Set V3) = {0} := by
  ext y
  simp only [affGe, Set.mem_setOf_eq, Affsign, Set.mem_singleton_iff]
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have hS : hfin.toFinset = ({0} : Finset V3) := by
      ext z
      simp [Set.Finite.mem_toFinset] <;> tauto
    rw [hS, Finset.sum_singleton] at hsum
    rw [hsum]
    simp
  · intro hy
    have hfin0 : (({0} : Set V3) ∪ (∅ : Set V3)).Finite := Set.toFinite _
    have hS : hfin0.toFinset = ({0} : Finset V3) := by
      ext z
      simp [Set.Finite.mem_toFinset] <;> tauto
    refine ⟨fun _ => 1, hfin0, ?_, ?_, ?_⟩
    · rw [hS]
      simp [hy]
    · intro z hz
      simp at hz
    · rw [hS]
      simp

/-- `affGe {0}` 对第二参数的单调性（CKQOWSA.hl:205 `SUBSET_INTER_ABSORPTION`
分支所需；前提 `0 ∉ t'` 与用途匹配：t' 为 ESTD 边，端点在 annulus 中非零；
`hfin'` 为并集有限性——本仓库 `Affsign` 的显式有限化要求）。 -/
theorem affGe_0_subset {t t' : Set V3} (hsub : t ⊆ t') (h0t' : (0:V3) ∉ t')
    (hfin' : (({0} : Set V3) ∪ t').Finite) :
    affGe {0} t ⊆ affGe {0} t' := by
  rintro y ⟨f, hfin, hsum, hpos, hone⟩
  set g : V3 → ℝ := fun z => if z ∈ ({0} : Set V3) ∪ t then f z else 0 with hgdef
  have hSsub : hfin.toFinset ⊆ hfin'.toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset, Set.mem_union] at hz ⊢
    tauto
  have h1 : ∀ z ∈ hfin.toFinset, g z = f z := by
    intro z hz
    have hzt : z ∈ ({0} : Set V3) ∪ t := by
      simpa only [Set.Finite.mem_toFinset] using hz
    show (if z ∈ ({0} : Set V3) ∪ t then f z else 0) = f z
    rw [if_pos hzt]
  have hside : ∀ z ∈ hfin'.toFinset, z ∉ hfin.toFinset → g z • z = 0 := by
    intro z hz' hz
    have hzn : z ∉ ({0} : Set V3) ∪ t := by
      intro hcontra
      exact hz (by simpa only [Set.Finite.mem_toFinset] using hcontra)
    show (if z ∈ ({0} : Set V3) ∪ t then f z else 0) • z = 0
    rw [if_neg hzn, zero_smul]
  have hvec : ∑ w ∈ hfin.toFinset, g w • w = ∑ w ∈ hfin'.toFinset, g w • w :=
    Finset.sum_subset hSsub hside
  have hscal : ∑ w ∈ hfin.toFinset, g w = ∑ w ∈ hfin'.toFinset, g w :=
    Finset.sum_subset hSsub (fun z hz' hz => by
      have hzn : z ∉ ({0} : Set V3) ∪ t := fun h =>
        hz (by simpa only [Set.Finite.mem_toFinset] using h)
      show (if z ∈ ({0} : Set V3) ∪ t then f z else 0) = 0
      rw [if_neg hzn])
  refine ⟨g, hfin', ?_, ?_, ?_⟩
  · calc y = ∑ w ∈ hfin.toFinset, f w • w := hsum
      _ = ∑ w ∈ hfin.toFinset, g w • w :=
          Finset.sum_congr rfl fun z hz => by rw [← h1 z hz]
      _ = ∑ w ∈ hfin'.toFinset, g w • w := hvec
  · intro z hz
    by_cases hzt : z ∈ t
    · have hpz := hpos z hzt
      have hzt' : z ∈ ({0} : Set V3) ∪ t := Set.mem_union_right _ hzt
      show 0 ≤ (if z ∈ ({0} : Set V3) ∪ t then f z else 0)
      rw [if_pos hzt']
      exact hpz
    · have hz0 : z ≠ 0 := fun h => h0t' (h ▸ hz)
      have hzn : z ∉ ({0} : Set V3) ∪ t := fun h => by
        rcases Set.mem_union _ _ _ |>.1 h with h1 | h1
        · exact hz0 h1
        · exact hzt h1
      show 0 ≤ (if z ∈ ({0} : Set V3) ∪ t then f z else 0)
      rw [if_neg hzn]
  · calc ∑ w ∈ hfin'.toFinset, g w = ∑ w ∈ hfin.toFinset, g w := hscal.symm
      _ = ∑ w ∈ hfin.toFinset, f w := Finset.sum_congr rfl fun z hz => h1 z hz
      _ = 1 := hone

/-! ## 2. annulus 的算术核与非共线性 -/

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

/-- HOL `dot_pos_lemma`（CKQOWSA_3.hl:1071-1105）：annulus 中距离 ≤ 2h0 的
两点内积为正。 -/
theorem dot_pos_lemma {v w : V3} (hv : v ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
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

/-- HOL `estd_non_collinear_lemma`（CKQOWSA_4.hl:45-53）：ESTD 边两端与原点
不共线（HOL 经 `COLLINEAR_BETWEEN_CASES` 归为 `REAL_ARITH`；此处经
`collinear_iff_exists_forall_eq_smul_vadd` 提取共线参数后归为三分支算术，
与 HOL 的 between 三分支逐一对应）。 -/
theorem estd_non_collinear_lemma {v w : V3} (hv : v ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
    (hd1 : 2 ≤ dist v w) (hd2 : dist v w ≤ 2 * h0) :
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
    · -- 0 < t ≤ 1：dist = ‖v‖ - ‖w‖ ≤ 2h0 - 2 < 2
      have h1 : |(r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (le_of_lt ht)
      have h2 : |1 - (r2 - r0) * (r1 - r0)⁻¹| = 1 - (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (by linarith)
      have hwn : ‖w‖ = (r2 - r0) * (r1 - r0)⁻¹ * ‖v‖ := by rw [hn_w, h1]
      have hdn : dist v w = ‖v‖ - ‖w‖ := by rw [hd, h2, hwn]; ring
      have h252 : (2:ℝ) * h0 = 2.52 := two_h0
      linarith
    · -- 1 < t：dist = ‖w‖ - ‖v‖ ≤ 2h0 - 2 < 2
      have h1 : |(r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ :=
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (r2 - r0) * (r1 - r0)⁻¹)
      have h2 : |1 - (r2 - r0) * (r1 - r0)⁻¹| = (r2 - r0) * (r1 - r0)⁻¹ - 1 := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ (r2 - r0) * (r1 - r0)⁻¹ - 1)]
      have hwn : ‖w‖ = (r2 - r0) * (r1 - r0)⁻¹ * ‖v‖ := by rw [hn_w, h1]
      have hdn : dist v w = ‖w‖ - ‖v‖ := by rw [hd, h2, hwn]; ring
      have h252 : (2:ℝ) * h0 = 2.52 := two_h0
      linarith

/-! ## 3. 深几何核（骨架：陈述移植，DISCHARGES 记欠） -/

/-- HOL `LEMMA_3_POINTS_FINAL`（CKQOWSA_3.hl:1350-1356）：annulus 中三点，
第三点在锥内、两两距离约束 ⟹ 矛盾。
DISCHARGES：骨架占位（sorry）。HOL 依赖链：`LEMMA_3_POINTS`（:1306）←
`lemma_3_points`（:1147，经 `dist_decreasing_ivt_lemma` :1106 的 IVT 论证）←
`rotation_lemma`（:828，连续旋转归约）← `triangle_height_lemma`（:283）、
`in_aff_ge_dist_lemma`（:327）、`in_aff_ge_dist_lower_bound`（:436）、
`rotation_dist_decrease`（:673）、`projection_lemma`（:42）等，约 1300 行。
后续轮次移植。 -/
theorem LEMMA_3_POINTS_FINAL {v1 v2 v3 : V3}
    (hcone : v3 ∈ affGe {0} ({v1, v2} : Set V3))
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus) (hb3 : v3 ∈ ballAnnulus)
    (hd : dist v1 v2 ≤ 2 * h0) (hd13 : 2 ≤ dist v1 v3) (hd23 : 2 ≤ dist v2 v3) :
    False := by
  sorry

/-- HOL `LEMMA_4_POINTS_FINAL`（CKQOWSA_4.hl:4093-4096）：annulus 中四点、
两组对边距离 ≤ 2h0、六对距离 ≥ 2 ⟹ 两锥恰交于原点。
DISCHARGES：骨架占位（sorry）。HOL 依赖链：`lemma_4_points_contradiction`
（:4035，经 `PARALLELOGRAM_LAW` :4028 + `ETA_Y_4_POINTS_INEQ` +
`lemma_4_points_circumcenter` :3866）← `lemma_4_points_rotation2(_full)`
（:3379/:3814）、`separation_plane_4_points`（:2870）、`aff_ge_inter_segments`
（:1238）、`rotation_lemma_segments`（:1395）等，约 3800 行。后续轮次移植。 -/
theorem LEMMA_4_POINTS_FINAL {v1 v2 v3 v4 : V3}
    (hb1 : v1 ∈ ballAnnulus) (hb2 : v2 ∈ ballAnnulus)
    (hb3 : v3 ∈ ballAnnulus) (hb4 : v4 ∈ ballAnnulus)
    (hd13l : dist v1 v3 ≤ 2 * h0) (hd24l : dist v2 v4 ≤ 2 * h0)
    (hd12 : 2 ≤ dist v1 v2) (hd14 : 2 ≤ dist v1 v4)
    (hd23 : 2 ≤ dist v2 v3) (hd34 : 2 ≤ dist v3 v4)
    (hd13 : 2 ≤ dist v1 v3) (hd24 : 2 ≤ dist v2 v4) :
    affGe {0} ({v1, v3} : Set V3) ∩ affGe {0} ({v2, v4} : Set V3) = {(0:V3)} := by
  sorry

/-! ## 4. fan7 的两点/三点块（CKQOWSA.hl:95/178） -/

/-- HOL `fan7_2`（CKQOWSA.hl:95-173）：两点情形的 aff_ge 交分配律。 -/
theorem fan7_2 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    affGe {0} ({v} : Set V3) ∩ affGe {0} ({w} : Set V3)
      = affGe {0} (({v} : Set V3) ∩ {w}) := by
  obtain ⟨hv2, hvup⟩ := inBallAnnulus (hann hv)
  obtain ⟨hw2, hwup⟩ := inBallAnnulus (hann hw)
  by_cases hvw : v = w
  · subst hvw
    simp only [Set.inter_self]
  · have hd : 2 ≤ dist v w := hpack.dist_ge_two hv hw hvw
    have hempty : ({v} : Set V3) ∩ {w} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      exact ⟨fun h => hvw (h.1.symm.trans h.2), fun hf => hf.elim⟩
    rw [hempty, affGe_0_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy1, hy2⟩
      by_contra hy0
      obtain ⟨a, ha0, hay⟩ := (affGe_0_1_char v y).1 hy1
      obtain ⟨b, hb0, hby⟩ := (affGe_0_1_char w y).1 hy2
      have ha : a ≠ 0 := by
        intro he
        rw [he, zero_smul] at hay
        exact hy0 hay
      have h1 : a • v = b • w := by rw [← hay, ← hby]
      have hvc : v = (b / a) • w := by
        have h2 : v = a⁻¹ • (a • v) := by rw [inv_smul_smul₀ ha]
        rw [h2, h1, smul_smul]
        have hba : a⁻¹ * b = b / a := by field_simp
        rw [hba]
      exact annulus_ray_absurd hv2 hw2 hd hvup hwup (div_nonneg hb0 ha0) hvc
    · rintro rfl
      exact ⟨(affGe_0_1_char v 0).2 ⟨0, le_refl 0, by simp⟩,
        (affGe_0_1_char w 0).2 ⟨0, le_refl 0, by simp⟩⟩

/-- HOL `fan7_3`（CKQOWSA.hl:178-276）：三点（边×单点）情形的 aff_ge 交分配律。
模 `LEMMA_3_POINTS_FINAL` 为真证明，与 HOL 结构逐行对应：u ∈ e 的
`SUBSET_INTER_ABSORPTION` 分支（:190-216）+ u ∉ e 的锥归约（:227-270）+
三点核（:271-276）。 -/
theorem fan7_3 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    (u : V3) (hu : u ∈ V) (e : Set V3) (he : e ∈ ESTD V) :
    affGe {0} ({u} : Set V3) ∩ affGe {0} e = affGe {0} (({u} : Set V3) ∩ e) := by
  obtain ⟨v, w, rfl, hv, hw, hvw, hd⟩ := mem_ESTD.1 he
  obtain ⟨hvb, -⟩ := inBallAnnulus (hann hv)
  obtain ⟨hwb, -⟩ := inBallAnnulus (hann hw)
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvb
    norm_num at hvb
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwb
    norm_num at hwb
  rcases Classical.em (u ∈ ({v, w} : Set V3)) with hue | hue
  · have hint : ({u} : Set V3) ∩ {v, w} = {u} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨h1, -⟩
        exact h1
      · intro h
        rw [h]
        simpa using hue
    rw [hint]
    have hfinE : (({0} : Set V3) ∪ {v, w} : Set V3).Finite := Set.toFinite _
    have h0t : (0:V3) ∉ ({v, w} : Set V3) := by
      intro h0
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
      rcases h0 with h | h
      · exact hvne h.symm
      · exact hwne h.symm
    refine Set.inter_eq_left.mpr (affGe_0_subset (Set.singleton_subset_iff.mpr hue)
      h0t hfinE)
  · have hint : ({u} : Set V3) ∩ {v, w} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
        Set.mem_empty_iff_false]
      constructor
      · rintro ⟨h1, h2⟩
        subst h1
        exact hue h2
      · rintro hz
        exact hz.elim
    rw [hint, affGe_0_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy1, hy2⟩
      by_contra hy0
      obtain ⟨t, ht0, hyt⟩ := (affGe_0_1_char u y).1 hy1
      have ht : 0 < t := by
        rcases lt_or_eq_of_le ht0 with h | h
        · exact h
        · rw [← h, zero_smul] at hyt
          exact absurd hyt hy0
      obtain ⟨t1, t2, ht1, ht2, hyt2⟩ := (affGe_0_2_char hvne hwne hvw y).1 hy2
      have hEq : t • u = t1 • v + t2 • w := by rw [← hyt2, ← hyt]
      have hcone : u ∈ affGe {0} ({v, w} : Set V3) := by
        refine (affGe_0_2_char hvne hwne hvw u).2 ⟨t1 / t, t2 / t,
          div_nonneg ht1 ht0, div_nonneg ht2 ht0, ?_⟩
        have hEq2 : u = t⁻¹ • (t1 • v + t2 • w) := by
          rw [← hEq, inv_smul_smul₀ ht.ne']
        rw [hEq2, smul_add, smul_smul, smul_smul]
        have hc1 : t⁻¹ * t1 = t1 / t := by field_simp
        have hc2 : t⁻¹ * t2 = t2 / t := by field_simp
        rw [hc1, hc2]
      exact LEMMA_3_POINTS_FINAL hcone (hann hv) (hann hw) (hann hu) hd
        (hpack.dist_ge_two hv hu fun h => hue (by rw [← h]; simp))
        (hpack.dist_ge_two hw hu fun h => hue (by rw [← h]; simp))
    · rintro rfl
      exact ⟨(affGe_0_1_char u 0).2 ⟨0, le_refl 0, by simp⟩,
        (affGe_0_2_char hvne hwne hvw 0).2 ⟨0, 0, le_refl 0, le_refl 0, by simp⟩⟩

/-! ## 5. ESTD_fan0/1/2/6（CKQOWSA.hl:29/47/68/79） -/

/-- HOL `ESTD_fan0`（CKQOWSA.hl:29-42）：`⋃₀ (ESTD V) ⊆ V` 且 `ESTD V` 是图
（每条边恰两点）。 -/
theorem ESTD_fan0 (V : Set V3) : (⋃₀ ESTD V) ⊆ V ∧ Graph (ESTD V) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, hxe⟩ := hx
    obtain ⟨v, w, rfl, hv, hw, -, -⟩ := mem_ESTD.1 he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxe
    rcases hxe with rfl | rfl
    · exact hv
    · exact hw
  · intro e he
    obtain ⟨v, w, rfl, -, -, hvw, -⟩ := mem_ESTD.1 he
    have hfin : ({v, w} : Set V3).Finite := Set.toFinite _
    refine ⟨hfin, ?_⟩
    have hE : hfin.toFinset = ({v, w} : Finset V3) := by
      ext z
      simp [Set.Finite.mem_toFinset]
    rw [hE]
    simp [hvw]

/-- HOL `ESTD_fan1`（CKQOWSA.hl:47-62）：annulus + packing + 非空 ⟹ `fan1`。
HOL 经 `Pack2.KIUMVTC`（packing 与球交有限）；此处复用
`Kepler.Packing.finite_inter_ball`（Statement.lean:46-47，同一事实的体积计数
证明；`Pack2.KIUMVTC` twin 所在的 PackingAuto1 与 PackingAuto2 的
`Kepler.Text.saturated` 声明冲突，无法同闭包 import）。 -/
theorem ESTD_fan1 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    (hne : V ≠ ∅) : fan1 0 V (ESTD V) := by
  have hsub : V ⊆ Metric.ball (0:V3) 4 := by
    intro v hv
    obtain ⟨-, hup⟩ := inBallAnnulus (hann hv)
    rw [Metric.mem_ball, dist_zero_right]
    have h252 := two_h0
    linarith
  have hfin0 : (V ∩ Metric.ball (0:V3) 4).Finite := hpack.finite_inter_ball 4
  have hveq : V ∩ Metric.ball (0:V3) 4 = V := by
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, hsub h⟩⟩
  have hfin : V.Finite := by rw [← hveq]; exact hfin0
  exact ⟨hfin, hne⟩

/-- HOL `ESTD_fan2`（CKQOWSA.hl:68-74）：`0 ∉ V`（annulus 下界）。 -/
theorem ESTD_fan2 (V : Set V3) (hann : V ⊆ ballAnnulus) : fan2 0 V (ESTD V) := by
  intro h0
  obtain ⟨h2, -⟩ := inBallAnnulus (hann h0)
  norm_num at h2

/-- HOL `ESTD_fan6`（CKQOWSA.hl:79-88）：每条 ESTD 边与原点不共线（fan6）。
归消引理 `estd_non_collinear_lemma`（§2，CKQOWSA_4.hl:45）。 -/
theorem ESTD_fan6 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V) :
    fan6 0 V (ESTD V) := by
  intro e he
  obtain ⟨v, w, rfl, hv, hw, hvw, hd⟩ := mem_ESTD.1 he
  exact estd_non_collinear_lemma (hann hv) (hann hw) (hpack.dist_ge_two hv hw hvw) hd

/-! ## 6. fan7 的四点块（CKQOWSA.hl:282-506） -/

/-- HOL `fan7_4_1_cases`（CKQOWSA.hl:404-434）：交恰一点的纯集合分类。 -/
theorem fan7_4_1_cases {v w v' w' : V3} (hvw : v ≠ w) (hv'w' : v' ≠ w')
    (hp : ∃ p, ({v, w} : Set V3) ∩ {v', w'} = {p}) :
    (v = v' ∧ w ≠ w') ∨ (v = w' ∧ w ≠ v') ∨ (w = v' ∧ v ≠ w') ∨ (w = w' ∧ v ≠ v') := by
  obtain ⟨p, hp⟩ := hp
  have key : ∀ z : V3, z ∈ ({v, w} : Set V3) → z ∈ ({v', w'} : Set V3) → z = p := by
    intro z hz1 hz2
    have hz : z ∈ ({v, w} : Set V3) ∩ {v', w'} := ⟨hz1, hz2⟩
    rw [hp] at hz
    simpa using hz
  have hpv : p = v ∨ p = w := by
    have h : p ∈ ({v, w} : Set V3) ∩ {v', w'} := by rw [hp]; simp
    simpa using h.1
  have hpv' : p = v' ∨ p = w' := by
    have h : p ∈ ({v, w} : Set V3) ∩ {v', w'} := by rw [hp]; simp
    simpa using h.2
  rcases hpv with rfl | rfl <;> rcases hpv' with rfl | rfl
  · exact Or.inl ⟨rfl, fun hww => hvw (key w (by simp) (by simp [hww])).symm⟩
  · exact Or.inr (Or.inl ⟨rfl, fun hwv' => hvw (key w (by simp) (by simp [hwv'])).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, fun hvw' => hvw (key v (by simp) (by simp [hvw']))⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, fun hvv' => hvw (key v (by simp) (by simp [hvv']))⟩))

/-- HOL `fan7_4_1_one_case`（CKQOWSA.hl:297-400）：共点两边（`v1 = v2`）的
交分配律，假设与 HOL 逐条对应（`~(v1 = v3)`、`~(v2 = v4)`、`~(v3 = v4)` 为
两边端点互异 + 交点约束）。模 `LEMMA_3_POINTS_FINAL` 为真证明：t2 = 0 /
t2' = 0 退化（:332-338/:367-372）+ 系数比较归约到三点核（:340-363/:375-396）。 -/
theorem fan7_4_1_one_case (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    {v1 v2 v3 v4 : V3} (hv1 : v1 ∈ V) (hv2 : v2 ∈ V) (hv3 : v3 ∈ V) (hv4 : v4 ∈ V)
    (h13 : v1 ≠ v3) (h24 : v2 ≠ v4) (h12 : v1 = v2) (h34 : v3 ≠ v4)
    (hd13 : dist v1 v3 ≤ 2 * h0) (hd24 : dist v2 v4 ≤ 2 * h0) :
    affGe {0} ({v1, v3} : Set V3) ∩ affGe {0} ({v2, v4} : Set V3)
      = affGe {0} (({v1, v3} : Set V3) ∩ {v2, v4}) := by
  rcases h12 with rfl
  obtain ⟨ha1, -⟩ := inBallAnnulus (hann hv1)
  obtain ⟨ha3, -⟩ := inBallAnnulus (hann hv3)
  obtain ⟨ha4, -⟩ := inBallAnnulus (hann hv4)
  have hv1n : v1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha1
    norm_num at ha1
  have hv3n : v3 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha3
    norm_num at ha3
  have hv4n : v4 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha4
    norm_num at ha4
  have hint : ({v1, v3} : Set V3) ∩ {v1, v4} = {v1} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨(h1 | h1), (h2 | h2)⟩
      · exact h1
      · exact h1
      · exact h2
      · exact absurd (h1.symm.trans h2) h34
    · intro hz
      rw [hz]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  rw [hint]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy1, hy2⟩
    obtain ⟨t1, t2, ht1, ht2, hyt1⟩ := (affGe_0_2_char hv1n hv3n h13 y).1 hy1
    obtain ⟨t1', t2', ht1', ht2', hyt2⟩ := (affGe_0_2_char hv1n hv4n h24 y).1 hy2
    have hEq : t1 • v1 + t2 • v3 = t1' • v1 + t2' • v4 := by rw [← hyt1, ← hyt2]
    by_cases ht20 : t2 = 0
    · exact (affGe_0_1_char v1 y).2 ⟨t1, ht1, by rw [hyt1, ht20]; simp⟩
    · rcases le_or_gt t1 t1' with hle | hlt
      · exfalso
        have ht2p : (0:ℝ) < t2 := lt_of_le_of_ne ht2 (Ne.symm ht20)
        have h3cone : v3 ∈ affGe {0} ({v1, v4} : Set V3) := by
          refine (affGe_0_2_char hv1n hv4n h24 v3).2 ⟨t2⁻¹ * (t1' - t1), t2⁻¹ * t2',
            mul_nonneg (le_of_lt (inv_pos.2 ht2p)) (by linarith),
            mul_nonneg (le_of_lt (inv_pos.2 ht2p)) ht2', ?_⟩
          have h5 : t2 • v3 = (t1' - t1) • v1 + t2' • v4 := by
            calc t2 • v3 = -(t1 • v1) + (t1' • v1 + t2' • v4) := by rw [← hEq]; abel
              _ = (t1' • v1 - t1 • v1) + t2' • v4 := by abel
              _ = (t1' - t1) • v1 + t2' • v4 := by rw [sub_smul]
          have hEq2 : v3 = t2⁻¹ • ((t1' - t1) • v1 + t2' • v4) := by
            rw [← h5, inv_smul_smul₀ ht20]
          rw [hEq2, smul_add, smul_smul, smul_smul]
        exact LEMMA_3_POINTS_FINAL h3cone (hann hv1) (hann hv4) (hann hv3) hd24
          (hpack.dist_ge_two hv1 hv3 h13)
          (hpack.dist_ge_two hv4 hv3 (fun h => h34 h.symm))
      · by_cases ht20' : t2' = 0
        · exact (affGe_0_1_char v1 y).2 ⟨t1', ht1', by rw [hyt2, ht20']; simp⟩
        · exfalso
          have ht2p' : (0:ℝ) < t2' := lt_of_le_of_ne ht2' (Ne.symm ht20')
          have h4cone : v4 ∈ affGe {0} ({v1, v3} : Set V3) := by
            refine (affGe_0_2_char hv1n hv3n h13 v4).2 ⟨t2'⁻¹ * (t1 - t1'), t2'⁻¹ * t2,
              mul_nonneg (le_of_lt (inv_pos.2 ht2p')) (by linarith),
              mul_nonneg (le_of_lt (inv_pos.2 ht2p')) ht2, ?_⟩
            have h5 : t2' • v4 = (t1 - t1') • v1 + t2 • v3 := by
              calc t2' • v4 = -(t1' • v1) + (t1 • v1 + t2 • v3) := by rw [hEq]; abel
                _ = (t1 • v1 - t1' • v1) + t2 • v3 := by abel
                _ = (t1 - t1') • v1 + t2 • v3 := by rw [sub_smul]
            have hEq2 : v4 = t2'⁻¹ • ((t1 - t1') • v1 + t2 • v3) := by
              rw [← h5, inv_smul_smul₀ ht20']
            rw [hEq2, smul_add, smul_smul, smul_smul]
          exact LEMMA_3_POINTS_FINAL h4cone (hann hv1) (hann hv3) (hann hv4) hd13
            (hpack.dist_ge_two hv1 hv4 h24)
            (hpack.dist_ge_two hv3 hv4 h34)
  · intro hy
    obtain ⟨t, ht, hyt⟩ := (affGe_0_1_char v1 y).1 hy
    exact ⟨(affGe_0_2_char hv1n hv3n h13 y).2 ⟨t, 0, ht, le_refl 0, by rw [hyt]; simp⟩,
      (affGe_0_2_char hv1n hv4n h24 y).2 ⟨t, 0, ht, le_refl 0, by rw [hyt]; simp⟩⟩

/-- HOL `fan7_4_1`（CKQOWSA.hl:439-473）：交恰一点的两边。按
`fan7_4_1_cases` 的四向分类套用 `fan7_4_1_one_case`（`PER_SET2` 对换由
`Set.pair_comm` 承担）。 -/
theorem fan7_4_1 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    {e1 e2 : Set V3} (he1 : e1 ∈ ESTD V) (he2 : e2 ∈ ESTD V)
    (hp : ∃ p, e1 ∩ e2 = {p}) :
    affGe {0} e1 ∩ affGe {0} e2 = affGe {0} (e1 ∩ e2) := by
  obtain ⟨v, w, rfl, hv, hw, hvw, hd⟩ := mem_ESTD.1 he1
  obtain ⟨v', w', rfl, hv', hw', hv'w', hd'⟩ := mem_ESTD.1 he2
  obtain ⟨p, hp⟩ := hp
  rcases fan7_4_1_cases hvw hv'w' ⟨p, hp⟩ with
    (⟨hvv', hww'⟩ | ⟨hvw', hwv'⟩ | ⟨hwv', hvw'⟩ | ⟨hww', hvv'⟩)
  · exact fan7_4_1_one_case V hann hpack (v1 := v) (v2 := v') (v3 := w) (v4 := w')
      hv hv' hw hw' hvw hv'w' hvv' hww' hd hd'
  · have h := fan7_4_1_one_case V hann hpack (v1 := v) (v2 := w') (v3 := w) (v4 := v')
      hv hw' hw hv' hvw hv'w'.symm hvw' hwv' hd
      (by rw [dist_comm w' v']; exact hd')
    rw [Set.pair_comm v' w']
    exact h
  · have h := fan7_4_1_one_case V hann hpack (v1 := w) (v2 := v') (v3 := v) (v4 := w')
      hw hv' hv hw' hvw.symm hv'w' hwv' hvw'
      (by rw [dist_comm w v]; exact hd) hd'
    rw [Set.pair_comm v w]
    exact h
  · have h := fan7_4_1_one_case V hann hpack (v1 := w) (v2 := w') (v3 := v) (v4 := v')
      hw hw' hv hv' hvw.symm hv'w'.symm hww' hvv'
      (by rw [dist_comm w v]; exact hd) (by rw [dist_comm w' v']; exact hd')
    rw [Set.pair_comm v w, Set.pair_comm v' w']
    exact h

/-- HOL `fan7_4_0`（CKQOWSA.hl:282-293）：不相交两边的交分配律（交为 ∅）。
直接套用 `LEMMA_4_POINTS_FINAL`（HOL :289 同）。 -/
theorem fan7_4_0 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    {e1 e2 : Set V3} (he1 : e1 ∈ ESTD V) (he2 : e2 ∈ ESTD V) (hdisj : e1 ∩ e2 = ∅) :
    affGe {0} e1 ∩ affGe {0} e2 = affGe {0} (e1 ∩ e2) := by
  rw [hdisj, affGe_0_empty]
  obtain ⟨v1, v3, rfl, hv1, hv3, h13, hd13l⟩ := mem_ESTD.1 he1
  obtain ⟨v2, v4, rfl, hv2, hv4, h24, hd24l⟩ := mem_ESTD.1 he2
  have hmem : ∀ z : V3, z ∈ ({v1, v3} : Set V3) → z ∈ ({v2, v4} : Set V3) → False := by
    intro z hz1 hz2
    have hz : z ∈ ({v1, v3} : Set V3) ∩ {v2, v4} := ⟨hz1, hz2⟩
    rw [hdisj] at hz
    exact hz
  exact LEMMA_4_POINTS_FINAL (hann hv1) (hann hv2) (hann hv3) (hann hv4) hd13l hd24l
    (hpack.dist_ge_two hv1 hv2 fun h => hmem v1 (by simp) (by simp [h]))
    (hpack.dist_ge_two hv1 hv4 fun h => hmem v1 (by simp) (by simp [h]))
    (hpack.dist_ge_two hv2 hv3 fun h => hmem v3 (by simp) (by simp [h.symm]))
    (hpack.dist_ge_two hv3 hv4 fun h => hmem v3 (by simp) (by simp [h]))
    (hpack.dist_ge_two hv1 hv3 h13)
    (hpack.dist_ge_two hv2 hv4 h24)

/-- HOL `fan7_4_2`（CKQOWSA.hl:477-506）：两边相等的情形（HOL 由
`(e1 ∩ e2) HAS_SIZE 2` 推 `e1 = e2`；该基数论证归入 `ESTD_fan7` 的三分支）。 -/
theorem fan7_4_2 {e1 e2 : Set V3} (heq : e1 = e2) :
    affGe {0} e1 ∩ affGe {0} e2 = affGe {0} (e1 ∩ e2) := by
  rw [heq]
  simp only [Set.inter_self]

/-! ## 7. 汇总：ESTD_fan7 与 CKQOWSA（CKQOWSA.hl:511-569/574-577） -/

/-- HOL `ESTD_fan7`（CKQOWSA.hl:511-569）：`fan7 (vec 0, V, ESTD V)`。边×边
情形按交的空/单点/相等三分支分流（HOL 用 `HAS_SIZE n, n ≤ 2`）。 -/
theorem ESTD_fan7 (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V) :
    fan7 0 V (ESTD V) := by
  intro e1 he1 e2 he2
  rcases (Set.mem_union _ _ _).1 he1 with he1 | ⟨u, hu, rfl⟩
  · rcases (Set.mem_union _ _ _).1 he2 with he2 | ⟨u', hu', rfl⟩
    · -- 边 × 边
      obtain ⟨v, w, rfl, hv, hw, hvw, hd⟩ := mem_ESTD.1 he1
      obtain ⟨v', w', rfl, hv', hw', hv'w', hd'⟩ := mem_ESTD.1 he2
      have hvin : v ∈ ({v', w'} : Set V3) ∨ v ∉ ({v', w'} : Set V3) := Classical.em _
      have hwin : w ∈ ({v', w'} : Set V3) ∨ w ∉ ({v', w'} : Set V3) := Classical.em _
      rcases hvin with hvin | hvin
      · rcases hwin with hwin | hwin
        · -- v, w 均在 e2 中 ⟹ e1 = e2
          have hv2e : v = v' ∨ v = w' := by simpa using hvin
          have hw2e : w = v' ∨ w = w' := by simpa using hwin
          have hsub : ({v, w} : Set V3) ⊆ {v', w'} := by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
            rcases hz with h | h
            · rw [h]; exact hv2e
            · rw [h]; exact hw2e
          have hc1 : ({v, w} : Set V3).ncard = 2 := Set.ncard_pair hvw
          have hc2 : ({v', w'} : Set V3).ncard = 2 := Set.ncard_pair hv'w'
          have heq : ({v, w} : Set V3) = {v', w'} :=
            Set.eq_of_subset_of_ncard_le hsub (hc2.trans hc1.symm).le
              (Set.toFinite ({v', w'} : Set V3))
          rw [heq]
          simp only [Set.inter_self]
        · -- 交 = {v}
          have hw2n : ¬ (w = v' ∨ w = w') := fun h => hwin (by simpa using h)
          have hint : ({v, w} : Set V3) ∩ {v', w'} = {v} := by
            ext z
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨(h1 | h1), (h2 | h2)⟩
              · exact h1
              · exact h1
              · exact absurd (Or.inl (h1.symm.trans h2)) hw2n
              · exact absurd (Or.inr (h1.symm.trans h2)) hw2n
            · rintro hz
              have hzv : z = v := hz
              rw [hzv]
              exact ⟨Or.inl rfl, by simpa using hvin⟩
          exact fan7_4_1 V hann hpack he1 he2 ⟨v, hint⟩
      · rcases hwin with hwin | hwin
        · -- 交 = {w}
          have hv2n : ¬ (v = v' ∨ v = w') := fun h => hvin (by simpa using h)
          have hw2e : w = v' ∨ w = w' := by simpa using hwin
          have hint : ({v, w} : Set V3) ∩ {v', w'} = {w} := by
            ext z
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨(h1 | h1), (h2 | h2)⟩
              · exact absurd (Or.inl (h1.symm.trans h2)) hv2n
              · exact absurd (Or.inr (h1.symm.trans h2)) hv2n
              · exact h1
              · exact h1
            · rintro hz
              have hzw : z = w := hz
              rw [hzw]
              exact ⟨Or.inr rfl, hw2e⟩
          exact fan7_4_1 V hann hpack he1 he2 ⟨w, hint⟩
        · -- 交 = ∅
          have hv2n : ¬ (v = v' ∨ v = w') := fun h => hvin (by simpa using h)
          have hw2n : ¬ (w = v' ∨ w = w') := fun h => hwin (by simpa using h)
          have hint : ({v, w} : Set V3) ∩ {v', w'} = ∅ := by
            ext z
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
              Set.mem_empty_iff_false]
            constructor
            · rintro ⟨(h1 | h1), (h2 | h2)⟩
              · exact absurd (Or.inl (h1.symm.trans h2)) hv2n
              · exact absurd (Or.inr (h1.symm.trans h2)) hv2n
              · exact absurd (Or.inl (h1.symm.trans h2)) hw2n
              · exact absurd (Or.inr (h1.symm.trans h2)) hw2n
            · rintro hz
              exact hz.elim
          exact fan7_4_0 V hann hpack he1 he2 hint
    · -- 边 × 单点：fan7_3 换序（HOL :557-560 的 INTER_ACI）
      have h := fan7_3 V hann hpack u' hu' e1 he1
      rw [Set.inter_comm (affGe {0} e1) (affGe {0} ({u'} : Set V3)),
        Set.inter_comm e1 ({u'} : Set V3)]
      exact h
  · rcases (Set.mem_union _ _ _).1 he2 with he2 | ⟨u', hu', rfl⟩
    · -- 单点 × 边：fan7_3（HOL :562-564）
      exact fan7_3 V hann hpack u hu e2 he2
    · -- 单点 × 单点：fan7_2（HOL :566-568）
      exact fan7_2 V hann hpack u u' hu hu'

/-- HOL `CKQOWSA`（CKQOWSA.hl:574-577）：`(V, ESTD V)` 是 fan。 -/
theorem CKQOWSA (V : Set V3) (hann : V ⊆ ballAnnulus) (hpack : Packing V)
    (hne : V ≠ ∅) : FAN 0 V (ESTD V) :=
  ⟨(ESTD_fan0 V).1, (ESTD_fan0 V).2, ESTD_fan1 V hann hpack hne, ESTD_fan2 V hann,
    ESTD_fan6 V hann hpack, ESTD_fan7 V hann hpack⟩

/-- HOL `CONTRAVENING_FAN` 的 FAN 合取项内核（= `Kepler.Text.TameLp
.contravening_fanTl` 的债务承接点，CKQOWSA 的 contravening 接口形）。
接线注记：由 `Contravening V`（TameLp.lean:324）取 `hpack = hc.1`、
`hann = hc.2.1`；`hne` 由 `V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15`
（合取项 5；ncard 13 > 0 排除空集）或 `scriptL V > 12` 得到。 -/
theorem contraveningFanTl (V : Set V3) (hpack : Packing V) (hann : V ⊆ ballAnnulus)
    (hne : V ≠ ∅) : FAN 0 V (ESTD V) :=
  CKQOWSA V hann hpack hne

end Kepler.Text.ContraFan
