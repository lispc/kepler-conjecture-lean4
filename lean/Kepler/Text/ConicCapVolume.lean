/-
Kepler.Text.ConicCapVolume — 锥帽体积套件（GT-1 三链共享银行：
GRUTOTI §D/§F/§I + PA24 REUHADY `volumeConicCapWedgeGeVsConicCap` +
TSKAJXY3 STRONG 版）。

HOL 源：`scripts/flyspeck_multivariate.ml`（本仓副本！非 reference 树）：
- `conic_cap`（:4832）/ `wedge`（:3714）/ `MEASURABLE_CONIC_CAP`（:4847）/
  `BOUNDED_CONIC_CAP`（:4842）/ `CONIC_CAP_DEGENERATE`（:4836）/
  `VOLUME_CONIC_CAP`（:5057）/ `VOLUME_CONIC_CAP_WEDGE_WEAK`（:6147）/
  `AZIM_EQ_0_PI_IMP_COPLANAR`（:2771）。

**依赖隔离说明（重要）**：本模块只 import `Kepler.Geom.*`（Azim/AzimLemmas/
SectorArea/Volume/WedgeVolume/Coplanar 全零 sorry 子树），**不 import 任何
Kepler.Text 文件**。原因：PA15 正本 `conicCap` 经 PA15←PA6 传递依赖，而
PackingAuto6.lean 正被并行 lane 在制（工作副本暂不编译），build 会连带失败。
故 `conic_cap` 以 `ccvConicCap` 私拷落地——与 PA15:109 `conicCap`、
PA24:93 `conicCapP24`、PA23:65 `grutotiConicCap` 逐字节同体
（`Metric.closedBall v0 r ∩ rconeGt v0 v1 a`，rconeGt 按 PA2:258 展开），
桥接在任何消费 lane 里是一行：
`example : conicCapP24 v0 v1 r a = ccvConicCap v0 v1 r a := rfl`（或
`conicCap`/`grutotiConicCap` 同理）。合并时按 playbook §5.3 以 PA15 正本
改名收敛，删除 `ccvConicCap`。

公开件与使用点形状对齐：
- `volumeConicCap` / `volumeConicCapPos`：HOL `VOLUME_CONIC_CAP`（:5057，
  前提 `0 < a`；`measurable(conic_cap) ∧ measure = if v1 = v0 ∨ 1 ≤ a ∨
  r < 0 then 0 else 2/3·π·(1−a)·r³`）。使用点：GRUTOTI.hl:3356-3358/7983-7985
  （§I 正性；PA23:315 `grutoti_volD_pos` 按 PA23:307-314 注记补 `hne`）、
  PA24:422-433（REUHADY）、TSKAJXY3.hl:1959（STRONG 版另配 bounded/convex；
  bounded 见 `boundedConicCap`，凸性未做）。
- `volumeConicCapWedge`（vol·azim/2π 形）/ `volumeConicCapWedgeFormula`
  （azim/3·(1−a)·r³ 形）：HOL `VOLUME_CONIC_CAP_WEDGE_WEAK`（:6147）。
  使用点：GRUTOTI §D/§F（HL:3208/3516/4767/5154/6544/6928）、PA24:428。
- `measurableConicCapWedge`：HOL `MEASURABLE_CONIC_CAP_WEDGE`（:6365）。
- `AZIM_EQ_0_PI_IMP_COPLANAR`：同名片（:2771），GRUTOTI §F AZIM_COMPL 前提。

范围注记（诚实边界）：本波给 `0 < a` 的 WEAK 版（GRUTOTI/PA24 使用点均为
0 < a ∈ (0,1)）。HOL :6511 全量版（a < 0 经 VOLUME_CONIC_CAP_COMPL 反射
配账、`max a (--1)` 分支）与 STRONG 的 convex 分量留给后续波。

路线（Geom/WedgeVolume.lean 零 sorry 先例的柱坐标改造）：
1. 平移到原点（`volume_real_add_left` + 私拷 `ccv_azim_sub_self`）；
2. 轴上右手 ON 标架（`exists_on3_eq_smul`）+ 保测投影
   `x ↦ (x⬝e3, zOf e1 e2 x)`（`measurePreserving_proj`）把锥帽变成 ℝ×ℂ
   模型集 `{p | p.1²+‖p.2‖² ≤ r² ∧ a·√(p.1²+‖p.2‖²) < p.1}`；
3. Fubini 轴高切片：`0 < a < 1` 时切片是两圆盘取小（lens disc），
   体积 = π·min(r²−t², s²t²)（s² = (1−a²)/a²）；楔形切片再乘扇形角 θ/2
   （复用 `volume_sector_rot` + ℂ 球面零测）；
4. 两段多项式积分 ∫₀^{ar} s²t² + ∫_{ar}^r (r²−t²) = 2(1−a)r³/3。
-/

import Mathlib
import Kepler.Geom.Azim
import Kepler.Geom.AzimLemmas
import Kepler.Geom.SectorArea
import Kepler.Geom.Volume
import Kepler.Geom.WedgeVolume
import Kepler.Geom.Coplanar

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## §0 定义私拷与平移私件（`ccv_` 前缀）-/

/-- HOL `conic_cap`（flyspeck_multivariate.ml:4832）私拷；与 PA15:109
`conicCap` / PA24:93 `conicCapP24` / PA23:65 `grutotiConicCap` 同体
（PA2:258 `rconeGt v0 v1 a` 按定义展开）。 -/
def ccvConicCap (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩
    {x : V3 | (x - v0) ⬝ᵥ (v1 - v0) > dist x v0 * dist v1 v0 * a}

private theorem ccv_mem_cone {v0 v1 : V3} (a : ℝ) (x : V3) :
    x ∈ {y : V3 | (y - v0) ⬝ᵥ (v1 - v0) > dist y v0 * dist v1 v0 * a} ↔
      (x - v0) ⬝ᵥ (v1 - v0) > dist x v0 * dist v1 v0 * a :=
  Iff.rfl

private theorem ccv_collinear3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases h : a = x
  · rw [h]
    simp only [sub_self]
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
    rw [collinear3_iff_smul h, collinear3_iff_smul h']
    simp only [sub_zero]

private theorem ccv_azimSubSpec {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

private theorem ccv_azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [ccv_collinear3_zero_sub (x := x) (a := a) (b := b),
    ccv_collinear3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext ccv_azimSubSpec
  rw [hpred]

private theorem ccv_wedge_sub_self (x a b c : V3) :
    Kepler.Geom.wedge x a b c =
      (fun y => x + y) '' Kepler.Geom.wedge 0 (a - x) (b - x) (c - x) := by
  ext y
  rw [Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - x, ?_, by abel⟩
    simp only [Kepler.Geom.wedge, Set.mem_setOf_eq] at hy ⊢
    exact ⟨fun h => hy.1 ((ccv_collinear3_zero_sub (x := x) (a := a) (b := y)).mpr h),
      by rw [← ccv_azim_sub_self x a b y]; exact hy.2.1,
      by rw [← ccv_azim_sub_self x a b y, ← ccv_azim_sub_self x a b c]; exact hy.2.2⟩
  · rintro ⟨u, hu, rfl⟩
    simp only [Kepler.Geom.wedge, Set.mem_setOf_eq] at hu ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [ccv_collinear3_zero_sub (x := x) (a := a) (b := x + u),
        show (x + u) - x = u by abel]
      exact hu.1
    · rw [ccv_azim_sub_self x a b (x + u), show (x + u) - x = u by abel]
      exact hu.2.1
    · rw [ccv_azim_sub_self x a b (x + u), show (x + u) - x = u by abel,
        ccv_azim_sub_self x a b c]
      exact hu.2.2

/-- HOL `AZIM_DEGENERATE`（PA24:100 私件拷贝）。 -/
private theorem ccv_azim_eq_zero_of_collinearY (v0 v1 w y : V3) (h : Collinear3 v0 v1 y) :
    azim v0 v1 w y = 0 := by
  unfold azim
  exact if_pos (Or.inr h)

/-- HOL `WEDGE_SIMPLE`（REUHADY.hl:68；PA24:111 公开件在禁 import 的 PA24，
私拷）。开楔形是严格方位角区间。 -/
private theorem ccv_wedge_simple (v0 v1 w1 w2 : V3) :
    Kepler.Geom.wedge v0 v1 w1 w2 =
      {y | 0 < azim v0 v1 w1 y ∧ azim v0 v1 w1 y < azim v0 v1 w1 w2} := by
  ext y
  simp only [Kepler.Geom.wedge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    intro hc
    rw [ccv_azim_eq_zero_of_collinearY v0 v1 w1 y hc] at h1
    exact absurd h1 (by linarith)

/-- HOL `CONIC_CAP_DEGENERATE`（flyspeck_multivariate.ml:4836）。 -/
private theorem ccv_conicCap_empty {v0 : V3} (r a : ℝ) : ccvConicCap v0 v0 r a = ∅ := by
  ext x
  simp only [ccvConicCap, Metric.mem_closedBall, ccv_mem_cone, Set.mem_inter_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, hcone⟩
  have h1 : ((x - v0 : V3) ⬝ᵥ (v0 - v0)) = 0 := by
    rw [sub_self]
    simp
  have h2 : dist x v0 * dist v0 v0 * a = 0 := by
    rw [dist_self]
    ring
  rw [h1, h2] at hcone
  linarith

/-- 锥参数 ≥ 1 时径向锥为空（柯西–施瓦茨）。 -/
private theorem ccv_cone_empty_of_ge (v0 w : V3) (a : ℝ) (ha : 1 ≤ a) :
    {x : V3 | (x - v0) ⬝ᵥ (w - v0) > dist x v0 * dist w v0 * a} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hcs : |((x - v0 : V3) ⬝ᵥ (w - v0))| ≤ ‖x - v0‖ * ‖w - v0‖ := by
    rw [← inner_eq_dot]
    exact abs_real_inner_le_norm (x - v0) (w - v0)
  have h1 : ((x - v0 : V3) ⬝ᵥ (w - v0)) ≤ |((x - v0 : V3) ⬝ᵥ (w - v0))| := le_abs_self _
  have h3 : ‖w - v0‖ ≤ ‖w - v0‖ * a := by
    have h := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ ‖w - v0‖)
    rwa [mul_one] at h
  have h6 : ‖x - v0‖ * ‖w - v0‖ ≤ ‖x - v0‖ * ‖w - v0‖ * a := by
    have h7 : ‖x - v0‖ * ‖w - v0‖ ≤ ‖x - v0‖ * (‖w - v0‖ * a) := by
      apply mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have h8 : ‖x - v0‖ * (‖w - v0‖ * a) = ‖x - v0‖ * ‖w - v0‖ * a := by ring
    rwa [h8] at h7
  have h4 : dist x v0 = ‖x - v0‖ := dist_eq_norm _ _
  have h5 : dist w v0 = ‖w - v0‖ := dist_eq_norm _ _
  rw [h4, h5] at hx
  linarith

/-! ## §1 可测性与有界性 -/

/-- HOL `MEASURABLE_CONIC_CAP`（flyspeck_multivariate.ml:4847）。 -/
theorem measurableConicCap (v0 v1 : V3) (r a : ℝ) :
    MeasurableSet (ccvConicCap v0 v1 r a) := by
  have h1 : Continuous fun x : V3 => (x - v0) ⬝ᵥ (v1 - v0) := by fun_prop
  have h2 : Continuous fun x : V3 => dist x v0 * dist v1 v0 * a :=
    Continuous.mul (Continuous.mul (continuous_id.dist continuous_const)
      continuous_const) continuous_const
  have hf : Continuous fun x : V3 =>
      (x - v0) ⬝ᵥ (v1 - v0) - dist x v0 * dist v1 v0 * a := h1.sub h2
  have hc : MeasurableSet
      {x : V3 | (x - v0) ⬝ᵥ (v1 - v0) > dist x v0 * dist v1 v0 * a} := by
    have hset : {x : V3 | (x - v0) ⬝ᵥ (v1 - v0) > dist x v0 * dist v1 v0 * a}
        = (fun x : V3 => (x - v0) ⬝ᵥ (v1 - v0) - dist x v0 * dist v1 v0 * a) ⁻¹'
            Set.Ioi 0 := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, sub_pos]
    rw [hset]
    exact hf.measurable measurableSet_Ioi
  exact Metric.isClosed_closedBall.measurableSet.inter hc

/-- HOL `BOUNDED_CONIC_CAP`（flyspeck_multivariate.ml:4842）。 -/
theorem boundedConicCap (v0 v1 : V3) (r a : ℝ) :
    Bornology.IsBounded (ccvConicCap v0 v1 r a) :=
  Bornology.IsBounded.subset Metric.isBounded_closedBall Set.inter_subset_left

/-! ## §2 平移归约与标架投影模型 -/

/-- 锥帽平移到原点。 -/
private theorem ccv_conicCap_add_left (v0 v1 : V3) (r a : ℝ) :
    ccvConicCap v0 v1 r a = (fun y : V3 => v0 + y) '' ccvConicCap 0 (v1 - v0) r a := by
  ext x
  rw [Set.mem_image]
  constructor
  · rintro ⟨hball, hcone⟩
    refine ⟨x - v0, ⟨?_, ?_⟩, by abel⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    · simpa [Set.mem_setOf_eq, sub_zero, dist_eq_norm] using hcone
  · rintro ⟨y, ⟨hball, hcone⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : dist (v0 + y) v0 = dist y 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      simpa [Metric.mem_closedBall, h1] using hball
    · have h1 : dist (v0 + y) v0 = dist y 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      have h2 : dist v1 v0 = dist (v1 - v0) 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        simp
      have h3 : ((v0 + y - v0 : V3) ⬝ᵥ (v1 - v0)) = ((y : V3) ⬝ᵥ (v1 - v0)) := by
        rw [show v0 + y - v0 = (y : V3) from by abel]
      simp only [ccvConicCap, Metric.mem_closedBall, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [h1, h2, h3]
      simpa [ccv_mem_cone, sub_zero] using hcone

/-- 标架下 ‖x‖² 的分量分解（WedgeVolume `on3_norm_sq` 私拷）。 -/
private theorem ccv_on3_norm_sq (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (x : V3) :
    ‖x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 + (x ⬝ᵥ e3) ^ 2 := by
  have h12 : e1 ⬝ᵥ e2 = 0 := he.2.2.2.1
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.1
  have h13 : e1 ⬝ᵥ e3 = 0 := he.2.2.2.2.1
  have h31 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.1
  have h23 : e2 ⬝ᵥ e3 = 0 := he.2.2.2.2.2.1
  have h32 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.2.1
  rw [norm_sq_eq_dot, on3_expand he x]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [he.1, he.2.1, he.2.2.1, h12, h21, h13, h31, h23, h32]
  ring

/-- WedgeVolume `zOf_norm_sq` 私拷。 -/
private theorem ccv_zOf_norm_sq (e1 e2 : V3) (x : V3) :
    ‖zOf e1 e2 x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [zOf, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero, zero_add, mul_one, sub_self]
  ring

/-- 锥帽的标架投影刻画（轴 `w = b • e3`，`0 < b`）。 -/
private theorem ccv_mem_capProj_iff {w : V3} (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3)
    {b : ℝ} (hb : 0 < b) (hax : (w : V3) = b • e3) (r a : ℝ) (hr : 0 ≤ r) (x : V3) :
    x ∈ ccvConicCap 0 w r a ↔
      (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 ≤ r ^ 2 ∧
        a * Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) < x ⬝ᵥ e3 := by
  have he31 : ‖(e3 : V3)‖ = 1 := by
    have h := norm_sq_eq_dot (x := e3)
    rw [he.2.2.1] at h
    have h0 : 0 ≤ ‖(e3 : V3)‖ := norm_nonneg e3
    nlinarith
  have hwnorm : ‖w‖ = b := by
    rw [hax, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.le, he31, mul_one]
  have hdot : (x ⬝ᵥ w) = b * (x ⬝ᵥ e3) := by
    rw [hax]
    simp only [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]
  have hnorm : ‖x‖ ^ 2 = (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 := by
    rw [ccv_on3_norm_sq e1 e2 e3 he x, ccv_zOf_norm_sq]
    ring
  have hsqrt : Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) = ‖x‖ := by
    rw [← hnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hmem : x ∈ ccvConicCap 0 w r a ↔ ‖x‖ ≤ r ∧ x ⬝ᵥ w > ‖x‖ * ‖w‖ * a := by
    simp [ccvConicCap]
  rw [hmem, hwnorm, hdot]
  constructor
  · rintro ⟨hball, hcone⟩
    have hball2 : (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 ≤ r ^ 2 := by
      rw [← hnorm]
      exact (sq_le_sq₀ (norm_nonneg x) hr).mpr hball
    refine ⟨hball2, ?_⟩
    have hkey : a * ‖x‖ < x ⬝ᵥ e3 := by
      have h2 : b * (a * ‖x‖) < b * (x ⬝ᵥ e3) := by
        have hrw : b * (a * ‖x‖) = ‖x‖ * b * a := by ring
        rw [hrw]
        linarith
      exact lt_of_mul_lt_mul_left h2 hb.le
    rw [hsqrt]
    exact hkey
  · rintro ⟨hball, hcone⟩
    have hball2 : ‖x‖ ≤ r := by
      have h2 : ‖x‖ ^ 2 ≤ r ^ 2 := by rw [hnorm]; exact hball
      exact (sq_le_sq₀ (norm_nonneg x) hr).mp h2
    refine ⟨hball2, ?_⟩
    have hkey : a * ‖x‖ < x ⬝ᵥ e3 := by rw [hsqrt] at hcone; exact hcone
    have h2 : b * (a * ‖x‖) < b * (x ⬝ᵥ e3) := mul_lt_mul_of_pos_left hkey hb
    have hrw : ‖x‖ * b * a = b * (a * ‖x‖) := by ring
    rw [hrw]
    exact h2

/-- 柱坐标模型集（原点锥帽的标架投影像）。 -/
private def ccvCapProj (r a : ℝ) : Set (ℝ × ℂ) :=
  {p | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) < p.1}

private theorem ccv_capProj_meas (r a : ℝ) : MeasurableSet (ccvCapProj r a) := by
  have hqc : Continuous fun p : ℝ × ℂ => p.1 ^ 2 + ‖p.2‖ ^ 2 :=
    (continuous_fst.pow 2).add (continuous_snd.norm.pow 2)
  have hqm : Measurable fun p : ℝ × ℂ => p.1 ^ 2 + ‖p.2‖ ^ 2 :=
    (measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)
  have hsq : Measurable fun p : ℝ × ℂ => Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) :=
    hqc.sqrt.measurable
  have h1 : MeasurableSet {p : ℝ × ℂ | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ r ^ 2} :=
    measurableSet_le hqm measurable_const
  have h2 : MeasurableSet {p : ℝ × ℂ | a * Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) < p.1} :=
    measurableSet_lt (measurable_const.mul hsq) measurable_fst
  exact h1.inter h2

private theorem ccv_preimage_capProj (r a : ℝ) (t : ℝ) :
    Prod.mk t ⁻¹' ccvCapProj r a =
      {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t} := by
  ext ζ
  simp only [Set.mem_preimage, ccvCapProj, Set.mem_setOf_eq]

/-! ## §3 切片体积：两圆盘取小（lens disc）-/

private theorem ccv_cone_sq_lt {t a ζ2 : ℝ} (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (h : a * Real.sqrt (t ^ 2 + ζ2) < t) :
    ζ2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
  rcases le_or_gt 0 (t ^ 2 + ζ2) with hX0 | hXneg
  · have hsq : (a * Real.sqrt (t ^ 2 + ζ2)) ^ 2 < t ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by linarith)).mpr h
    have hexp : (a * Real.sqrt (t ^ 2 + ζ2)) ^ 2 = a ^ 2 * (t ^ 2 + ζ2) := by
      rw [mul_pow, Real.sq_sqrt hX0]
    rw [hexp] at hsq
    have hnorm : a ^ 2 * t ^ 2 + a ^ 2 * ζ2 < t ^ 2 := by nlinarith
    have hz2 : ζ2 * a ^ 2 < (1 - a ^ 2) * t ^ 2 := by linarith
    rw [show (1 - a ^ 2) / a ^ 2 * t ^ 2 = (1 - a ^ 2) * t ^ 2 / a ^ 2 from by ring]
    exact (lt_div_iff₀ (by positivity : (0:ℝ) < a ^ 2)).mpr hz2
  · have hsa : 0 < (1 - a ^ 2) / a ^ 2 := by
      have h3 : 0 < 1 - a ^ 2 := by nlinarith [sq_nonneg a, ha.le, ha1]
      have h4 : 0 < a ^ 2 := by positivity
      exact div_pos h3 h4
    have h1 : t ^ 2 + ζ2 < 0 := hXneg
    nlinarith [sq_nonneg t, hsa, h1]

private theorem ccv_cone_sq_lt' {t a ζ2 : ℝ} (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (h : ζ2 < (1 - a ^ 2) / a ^ 2 * t ^ 2) :
    a * Real.sqrt (t ^ 2 + ζ2) < t := by
  rcases le_or_gt 0 (t ^ 2 + ζ2) with hX0 | hXneg
  · have hz2 : a ^ 2 * ζ2 < (1 - a ^ 2) * t ^ 2 := by
      have h2 := mul_lt_mul_of_pos_right h (by positivity : (0:ℝ) < a ^ 2)
      have h4 : a ^ 2 * ((1 - a ^ 2) / a ^ 2 * t ^ 2) = (1 - a ^ 2) * t ^ 2 := by
        field_simp
      nlinarith [h2, h4]
    have hsq : a ^ 2 * t ^ 2 + a ^ 2 * ζ2 < t ^ 2 := by nlinarith
    have hexp : (a * Real.sqrt (t ^ 2 + ζ2)) ^ 2 = a ^ 2 * (t ^ 2 + ζ2) := by
      rw [mul_pow, Real.sq_sqrt hX0]
    have h4 : (a * Real.sqrt (t ^ 2 + ζ2)) ^ 2 < t ^ 2 := by rw [hexp]; nlinarith
    exact (sq_lt_sq₀ (by positivity) (by linarith)).mp h4
  · have h0 : Real.sqrt (t ^ 2 + ζ2) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [h0, mul_zero]
    exact ht

private theorem ccv_ofReal_sq_pi (R : ℝ) (hR : 0 ≤ R) :
    ENNReal.ofReal R ^ 2 * ((NNReal.pi : NNReal) : ENNReal) =
      ENNReal.ofReal (Real.pi * R ^ 2) := by
  have hcoe : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal Real.pi :=
    ENNReal.coe_nnreal_eq NNReal.pi
  rw [hcoe, sq, ← ENNReal.ofReal_mul hR,
    ← ENNReal.ofReal_mul (by nlinarith : 0 ≤ R * R)]
  congr 1
  ring

private theorem ccv_volume_ball_complex (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.ball (0 : ℂ) R) = ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [Complex.volume_ball, ccv_ofReal_sq_pi R hR]

private theorem ccv_volume_closedBall_complex (R : ℝ) (hR : 0 ≤ R) :
    volume (Metric.closedBall (0 : ℂ) R) = ENNReal.ofReal (Real.pi * R ^ 2) := by
  rw [Complex.volume_closedBall, ccv_ofReal_sq_pi R hR]

/-- 双条件圆片 `{‖ζ‖² ≤ X ∧ ‖ζ‖² < Y}` 的面积 = π·min(X, Y)。 -/
private theorem ccv_volume_lensDisc (X Y : ℝ) :
    volume {ζ : ℂ | ‖ζ‖ ^ 2 ≤ X ∧ ‖ζ‖ ^ 2 < Y} =
      ENNReal.ofReal (Real.pi * min X Y) := by
  rcases lt_or_ge X 0 with hXneg | hX0
  · -- X < 0：第一条件不可能
    have hempty : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ X ∧ ‖ζ‖ ^ 2 < Y} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, -⟩
      have hnz := sq_nonneg ‖(ζ : ℂ)‖
      exact absurd h1 (by nlinarith)
    rw [hempty, measure_empty]
    rcases le_or_gt X Y with hle | hgt
    · rw [min_eq_left hle, eq_comm, ENNReal.ofReal_eq_zero]
      nlinarith [Real.pi_pos, hXneg]
    · rw [min_eq_right hgt.le, eq_comm, ENNReal.ofReal_eq_zero]
      nlinarith [Real.pi_pos, hXneg]
  · rcases lt_or_ge Y 0 with hYneg | hY0
    · -- Y < 0（而 0 ≤ X）：第二条件不可能
      have hempty : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ X ∧ ‖ζ‖ ^ 2 < Y} = ∅ := by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2⟩
        have hnz := sq_nonneg ‖(ζ : ℂ)‖
        exact absurd h2 (by nlinarith)
      rw [hempty, measure_empty, min_eq_right (by linarith : Y ≤ X),
        eq_comm, ENNReal.ofReal_eq_zero]
      nlinarith [Real.pi_pos, hYneg]
    · -- 0 ≤ X, 0 ≤ Y：开/闭圆盘正常计算
      rcases le_or_gt Y X with hYX | hXY
      · have hset : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ X ∧ ‖ζ‖ ^ 2 < Y}
            = Metric.ball (0 : ℂ) (Real.sqrt Y) := by
          ext ζ
          simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
          constructor
          · rintro ⟨-, h2⟩
            have h3 : ‖ζ‖ ^ 2 < (Real.sqrt Y) ^ 2 := by
              rw [Real.sq_sqrt hY0]
              exact h2
            exact (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg Y)).mp h3
          · intro h
            have h3 : ‖ζ‖ ^ 2 < (Real.sqrt Y) ^ 2 :=
              (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg Y)).mpr h
            rw [Real.sq_sqrt hY0] at h3
            exact ⟨by linarith, h3⟩
        rw [hset, ccv_volume_ball_complex (Real.sqrt Y) (Real.sqrt_nonneg Y),
          Real.sq_sqrt hY0, min_eq_right hYX]
      · have hset : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ X ∧ ‖ζ‖ ^ 2 < Y}
            = Metric.closedBall (0 : ℂ) (Real.sqrt X) := by
          ext ζ
          simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, -⟩
            have h3 : ‖ζ‖ ^ 2 ≤ (Real.sqrt X) ^ 2 := by
              rw [Real.sq_sqrt hX0]
              exact h1
            exact (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg X)).mp h3
          · intro h
            have h3 : ‖ζ‖ ^ 2 ≤ (Real.sqrt X) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg X)).mpr h
            rw [Real.sq_sqrt hX0] at h3
            exact ⟨h3, by linarith⟩
        rw [hset, ccv_volume_closedBall_complex (Real.sqrt X) (Real.sqrt_nonneg X),
          Real.sq_sqrt hX0, min_eq_left hXY.le]

/-- ℂ 上非零半径球面零测。 -/
private theorem ccv_volume_sphere_complex {R : ℝ} (hR0 : R ≠ 0) :
    volume (Metric.sphere (0 : ℂ) R) = 0 := by
  rcases lt_or_ge R 0 with hneg | hnonneg
  · rw [Metric.sphere_eq_empty_of_neg hneg]
    exact measure_empty
  · have hf : Metric.sphere (0 : ℂ) R = frontier (Metric.ball (0 : ℂ) R) :=
      (frontier_ball (0 : ℂ) hR0).symm
    rw [hf]
    exact (convex_ball (0 : ℂ) R).addHaar_frontier volume

/-- ℂ 上闭圆盘扇形面积（闭/开差 ∪ 球面，零测收账）。 -/
private theorem ccv_volume_sectorClosed {u : ℂ} (hu : u ≠ 0) (R θ : ℝ) (hR : 0 ≤ R)
    (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) :
    volume {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
      = ENNReal.ofReal (R ^ 2 * θ / 2) := by
  rcases eq_or_lt_of_le hR with h0 | hpos
  · subst h0
    have hempty : {ζ : ℂ | ‖ζ‖ ≤ 0 ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      have hz0 : ‖ζ‖ = 0 := le_antisymm h1 (norm_nonneg ζ)
      have hz : ζ = 0 := norm_eq_zero.mp hz0
      rw [hz, mul_zero] at h2
      simp [ang, angArg] at h2
    rw [hempty, measure_empty]
    simp
  · have hopen := volume_sector_rot hu hR hθ0 hθ2π
    have hsub : {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} ⊆
        {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
          ∪ Metric.sphere (0 : ℂ) R := by
      intro z hz
      by_cases h1 : ‖z‖ < R
      · exact Or.inl ⟨h1, hz.2.1, hz.2.2⟩
      · refine Or.inr ?_
        rw [Metric.mem_sphere, dist_zero_right]
        have h2 := not_lt.mp h1
        have hz1 := hz.1
        linarith
    have hsub2 : {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} ⊆
        {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} :=
      fun z hz => ⟨le_of_lt hz.1, hz.2.1, hz.2.2⟩
    have hle : volume {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
        ≤ volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
      calc volume {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
          ≤ volume ({ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
              ∪ Metric.sphere (0 : ℂ) R) := measure_mono hsub
        _ ≤ volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
              + volume (Metric.sphere (0 : ℂ) R) :=
            measure_union_le _ _
        _ = volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} + 0 := by
            rw [ccv_volume_sphere_complex (ne_of_gt hpos)]
        _ = volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := add_zero _
    have heq : volume {ζ : ℂ | ‖ζ‖ ≤ R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
        = volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} :=
      le_antisymm hle (measure_mono hsub2)
    rw [heq]
    exact hopen

/-! ## §4 核心积分：两段多项式 = 2(1−a)r³/3 -/

/-- ∫⁻ in Ioo x y, ofReal(C·(s·t²)) = ofReal(C·(s·(y³−x³)/3))。 -/
private theorem ccv_lintegral_sq_Ioo (C s x y : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hxy : x ≤ y) :
    ∫⁻ t in Set.Ioo x y, ENNReal.ofReal (C * (s * t ^ 2))
      = ENNReal.ofReal (C * (s * (y ^ 3 - x ^ 3) / 3)) := by
  have hint : IntegrableOn (fun t : ℝ => C * (s * t ^ 2)) (Set.Ioo x y) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hxy).mp
      (Continuous.intervalIntegrable
        (continuous_const.mul (continuous_const.mul (continuous_id.pow 2))) x y)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo x y)] (fun t : ℝ => C * (s * t ^ 2)) := by
    filter_upwards [self_mem_ae_restrict (by exact measurableSet_Ioo)] with t ht
    exact mul_nonneg hC (mul_nonneg hs (sq_nonneg t))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hxy, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow]
  congr 1
  ring

/-- ∫⁻ in Ioc x y, ofReal(C·(r²−t²)) = ofReal(C·(r²(y−x)−(y³−x³)/3))，
要求区间落在 `[0, r]` 内（保证被积函数非负）。 -/
private theorem ccv_lintegral_parabola_Ioc (C r x y : ℝ) (hC : 0 ≤ C) (hxy : x ≤ y)
    (hx0 : 0 ≤ x) (hyr : y ≤ r) :
    ∫⁻ t in Set.Ioc x y, ENNReal.ofReal (C * (r ^ 2 - t ^ 2))
      = ENNReal.ofReal (C * (r ^ 2 * (y - x) - (y ^ 3 - x ^ 3) / 3)) := by
  have hcont : Continuous fun t : ℝ => C * (r ^ 2 - t ^ 2) :=
    continuous_const.mul (continuous_const.sub (continuous_id.pow 2))
  have hint : IntegrableOn (fun t : ℝ => C * (r ^ 2 - t ^ 2)) (Set.Ioc x y) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mp
      (Continuous.intervalIntegrable hcont x y)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc x y)] (fun t : ℝ => C * (r ^ 2 - t ^ 2)) := by
    filter_upwards [self_mem_ae_restrict (by exact measurableSet_Ioc)] with t ht
    have htx : 0 ≤ t := by linarith [hx0, ht.1]
    have htr : t ≤ r := ht.2.trans hyr
    have hsq : t ^ 2 ≤ r ^ 2 := (sq_le_sq₀ (by linarith) (by linarith)).mpr htr
    exact mul_nonneg hC (sub_nonneg.mpr hsq)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hxy]
  have hsplit : ∫ t in x..y, (C * (r ^ 2 - t ^ 2))
      = C * (r ^ 2 * (y - x) - (y ^ 3 - x ^ 3) / 3) := by
    have h1 : ∀ t : ℝ, (C * (r ^ 2 - t ^ 2) : ℝ) = C * r ^ 2 - C * t ^ 2 := fun _ => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_pow]
      ring
    · exact Continuous.intervalIntegrable continuous_const x y
    · exact Continuous.intervalIntegrable
        (continuous_const.mul (continuous_id.pow 2)) x y
  rw [hsplit]

/-- ∫⁻ in Ico x y, ofReal(C·(r²−t²)) = ofReal(C·(r²(y−x)−(y³−x³)/3))，
要求区间落在 `[0, r]` 内。 -/
private theorem ccv_lintegral_parabola_Ico (C r x y : ℝ) (hC : 0 ≤ C) (hxy : x ≤ y)
    (hx0 : 0 ≤ x) (hyr : y ≤ r) :
    ∫⁻ t in Set.Ico x y, ENNReal.ofReal (C * (r ^ 2 - t ^ 2))
      = ENNReal.ofReal (C * (r ^ 2 * (y - x) - (y ^ 3 - x ^ 3) / 3)) := by
  have hcont : Continuous fun t : ℝ => C * (r ^ 2 - t ^ 2) :=
    continuous_const.mul (continuous_const.sub (continuous_id.pow 2))
  have hint : IntegrableOn (fun t : ℝ => C * (r ^ 2 - t ^ 2)) (Set.Ico x y) := by
    rw [integrableOn_Ico_iff_integrableOn_Ioo]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hxy).mp
      (Continuous.intervalIntegrable hcont x y)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ico x y)] (fun t : ℝ => C * (r ^ 2 - t ^ 2)) := by
    filter_upwards [self_mem_ae_restrict (by exact measurableSet_Ico)] with t ht
    rw [Set.mem_Ico] at ht
    have htx : 0 ≤ t := by linarith [hx0, ht.1]
    have htr : t ≤ r := (ht.2.trans_le hyr).le
    have hsq : t ^ 2 ≤ r ^ 2 := (sq_le_sq₀ (by linarith) (by linarith)).mpr htr
    exact mul_nonneg hC (sub_nonneg.mpr hsq)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hxy]
  have hsplit : ∫ t in x..y, (C * (r ^ 2 - t ^ 2))
      = C * (r ^ 2 * (y - x) - (y ^ 3 - x ^ 3) / 3) := by
    have h1 : ∀ t : ℝ, (C * (r ^ 2 - t ^ 2) : ℝ) = C * r ^ 2 - C * t ^ 2 := fun _ => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_pow]
      ring
    · exact Continuous.intervalIntegrable continuous_const x y
    · exact Continuous.intervalIntegrable
        (continuous_const.mul (continuous_id.pow 2)) x y
  rw [hsplit]

/-- GT-1 解析内核：切片体积 ly 积分（两段多项式）。 -/
private theorem ccv_lintegral_core (r a C : ℝ) (hr : 0 < r) (ha : 0 < a) (ha1 : a < 1)
    (hC : 0 ≤ C) :
    ∫⁻ t : ℝ,
        (if 0 < t then
          ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
      = ENNReal.ofReal (C * (2 * (1 - a) * r ^ 3 / 3)) := by
  have hsa : 0 < (1 - a ^ 2) / a ^ 2 := by
    have h1 : 0 < 1 - a ^ 2 := by nlinarith [sq_nonneg a, ha.le, ha1]
    have h2 : 0 < a ^ 2 := by positivity
    exact div_pos h1 h2
  have hsa2 : (1 - a ^ 2) / a ^ 2 * a ^ 2 = 1 - a ^ 2 := by field_simp
  have hskey1 : (1 + (1 - a ^ 2) / a ^ 2) * a ^ 2 = 1 := by
    field_simp
    ring
  have hmin1 : ∀ t : ℝ, 0 < t → t ≤ a * r →
      min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)
        = (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
    intro t ht0 hle
    have hle2 : t ^ 2 ≤ a ^ 2 * r ^ 2 := by
      have h := (sq_le_sq₀ (by nlinarith) (by nlinarith)).mpr hle
      rwa [mul_pow] at h
    have h1 : (1 - a ^ 2) / a ^ 2 * t ^ 2 ≤ (1 - a ^ 2) * r ^ 2 := by
      calc (1 - a ^ 2) / a ^ 2 * t ^ 2
          ≤ (1 - a ^ 2) / a ^ 2 * (a ^ 2 * r ^ 2) :=
            by apply mul_le_mul_of_nonneg_left hle2 (by positivity)
        _ = ((1 - a ^ 2) / a ^ 2 * a ^ 2) * r ^ 2 := by ring
        _ = (1 - a ^ 2) * r ^ 2 := by rw [hsa2]
    have h2 : (1 - a ^ 2) * r ^ 2 ≤ r ^ 2 - t ^ 2 := by nlinarith
    exact min_eq_right (h1.trans h2)
  have hmin2 : ∀ t : ℝ, 0 < t → a * r < t →
      min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2) = r ^ 2 - t ^ 2 := by
    intro t ht0 hgt
    have h1 : r ^ 2 - t ^ 2 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
      by_contra hc
      push_neg at hc
      have h2 : (1 + (1 - a ^ 2) / a ^ 2) * t ^ 2 < r ^ 2 := by
        have h2a : t ^ 2 + (1 - a ^ 2) / a ^ 2 * t ^ 2 < t ^ 2 + (r ^ 2 - t ^ 2) := by
          linarith
        nlinarith
      have h3 : a ^ 2 * ((1 + (1 - a ^ 2) / a ^ 2) * t ^ 2) = t ^ 2 := by
        field_simp
        ring
      have h6 : a ^ 2 * ((1 + (1 - a ^ 2) / a ^ 2) * t ^ 2) < a ^ 2 * r ^ 2 :=
        mul_lt_mul_of_pos_left h2 (show 0 < (a:ℝ) ^ 2 from by positivity)
      rw [h3] at h6
      have h8 : (a * r) ^ 2 < t ^ 2 :=
        (sq_lt_sq₀ (mul_nonneg ha.le hr.le) ht0.le).mpr hgt
      linarith
    exact min_eq_left h1
  -- 拆分一：ℝ = Iic 0 ⊔ Ioi 0
  have hcompl : (Set.Iic 0)ᶜ = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ioi, not_le]
  have hzero1 : ∫⁻ t in Set.Iic 0,
      (if 0 < t then
        ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0) = 0 := by
    refine setLIntegral_eq_zero measurableSet_Iic ?_
    intro t ht
    simp only [Set.mem_Iic] at ht
    show (if 0 < t then
      ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0) = 0
    rw [if_neg (by linarith)]
  have hI1 : ∫⁻ t : ℝ,
      (if 0 < t then
        ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
      = ∫⁻ t in Set.Ioi 0,
          (if 0 < t then
            ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0) := by
    have h := lintegral_add_compl
      (f := fun t =>
        if 0 < t then
          ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
      (μ := volume) (A := Set.Ioi (0:ℝ)) measurableSet_Ioi
    rw [← h]
    have hz2 : ∫⁻ x in (Set.Ioi (0:ℝ))ᶜ,
        (if 0 < x then
          ENNReal.ofReal (C * min (r ^ 2 - x ^ 2) ((1 - a ^ 2) / a ^ 2 * x ^ 2)) else 0)
      = ∫⁻ x in Set.Iic 0,
          (if 0 < x then
            ENNReal.ofReal (C * min (r ^ 2 - x ^ 2) ((1 - a ^ 2) / a ^ 2 * x ^ 2)) else 0) := by
      rw [Set.compl_Ioi]
    rw [hz2]
    simp only [hzero1, zero_add]
    exact add_zero _
  -- 拆分二：Ioi 0 = Ioo 0 (a*r) ⊔ Ici (a*r)
  have har : 0 < a * r := by positivity
  have hIoiSet : Set.Ioo 0 (a * r) ∪ Set.Ici (a * r) = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, -⟩ | h)
      · exact h1
      · exact har.trans_le h
    · intro h
      rcases lt_or_ge t (a * r) with hlt | hle
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr hle
  have hdisj : Disjoint (Set.Ioo 0 (a * r)) (Set.Ici (a * r)) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    simp only [Set.mem_Ioo, Set.mem_Ici] at h1 h2
    linarith
  -- 第二段所需的集合重写与零测件
  have hAB : Set.Ici (a * r) ∩ Set.Ici r = Set.Ici r := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici]
    constructor
    · rintro ⟨-, h2⟩
      exact h2
    · intro h
      exact ⟨by nlinarith, h⟩
  have hAD : Set.Ici (a * r) \ Set.Ici r = Set.Ico (a * r) r := by
    ext t
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Ico, not_le, not_lt]
  have hz : ∫⁻ t in Set.Ici r,
      ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ici ?_
    intro t ht
    simp only [Set.mem_Ici] at ht
    have ht0 : 0 < t := by linarith
    have htr : a * r < t := by
      have h2 := mul_lt_mul_of_pos_right ha1 hr
      rw [one_mul] at h2
      linarith
    show ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) = 0
    rw [hmin2 t ht0 htr, ENNReal.ofReal_eq_zero,
      show r ^ 2 - t ^ 2 = -(t ^ 2 - r ^ 2) from by ring, mul_neg]
    exact neg_nonpos.mpr (mul_nonneg hC (sub_nonneg.mpr ((sq_le_sq₀ hr.le ht0.le).mpr ht)))
  have hI2 : ∫⁻ t in Set.Ioi 0,
      (if 0 < t then
        ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
      = ENNReal.ofReal (C * (2 * (1 - a) * r ^ 3 / 3)) := by
    have hEq := setLIntegral_congr_fun
      (f := fun t =>
        if 0 < t then
          ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
      (g := fun t => ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)))
      (μ := volume) measurableSet_Ioi (fun t ht => by
        simp only [Set.mem_Ioi] at ht
        show (if 0 < t then
          ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)) else 0)
            = ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
        rw [if_pos ht])
    have hEq1 : ∫⁻ t in Set.Ioo 0 (a * r),
        ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
      = ∫⁻ t in Set.Ioo 0 (a * r), ENNReal.ofReal (C * ((1 - a ^ 2) / a ^ 2 * t ^ 2)) := by
      refine setLIntegral_congr_fun
        (f := fun t => ENNReal.ofReal
          (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)))
        (g := fun t => ENNReal.ofReal (C * ((1 - a ^ 2) / a ^ 2 * t ^ 2)))
        (by exact measurableSet_Ioo) (fun t ht => by
          obtain ⟨ht1, ht2⟩ := ht
          show ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
              = ENNReal.ofReal (C * ((1 - a ^ 2) / a ^ 2 * t ^ 2))
          rw [hmin1 t ht1 ht2.le])
    have hEq2 : ∫⁻ t in Set.Ico (a * r) r,
        ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
      = ∫⁻ t in Set.Ico (a * r) r, ENNReal.ofReal (C * (r ^ 2 - t ^ 2)) := by
      refine setLIntegral_congr_fun
        (f := fun t => ENNReal.ofReal
          (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)))
        (g := fun t => ENNReal.ofReal (C * (r ^ 2 - t ^ 2)))
        (by exact measurableSet_Ico) (fun t ht => by
          rw [Set.mem_Ico] at ht
          show ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
              = ENNReal.ofReal (C * (r ^ 2 - t ^ 2))
          rcases eq_or_lt_of_le ht.1 with heq | hlt
          · subst heq
            have he2 : (1 - a ^ 2) / a ^ 2 * (a * r) ^ 2 = r ^ 2 - (a * r) ^ 2 := by
              field_simp
            rw [he2, min_self]
          · rw [hmin2 t (by linarith [har, hlt]) hlt])
    have hsplit := lintegral_inter_add_sdiff
      (f := fun t => ENNReal.ofReal (C * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2)))
      (Set.Ici (a * r)) (B := Set.Ici r) (μ := volume) measurableSet_Ici
    rw [hAB, hAD] at hsplit
    rw [hEq, ← hIoiSet]
    simp only [lintegral_union measurableSet_Ici hdisj, ← hsplit, hz, add_zero, hEq1,
      hEq2, zero_add]
    rw [ccv_lintegral_sq_Ioo C ((1 - a ^ 2) / a ^ 2) 0 (a * r) hC hsa.le
      (by nlinarith)]
    rw [ccv_lintegral_parabola_Ico C r (a * r) r hC (by nlinarith)
      (mul_nonneg ha.le hr.le) (le_refl r)]
    have hpow : (a * r) ^ 3 = a ^ 3 * r ^ 3 := by ring
    have hp1' : 0 ≤ C * ((1 - a ^ 2) / a ^ 2 * ((a * r) ^ 3 - 0 ^ 3) / 3) := by
      have h3 : 0 ≤ (a * r) ^ 3 := pow_nonneg (mul_nonneg ha.le hr.le) 3
      have h5 : (0:ℝ) ^ 3 = 0 := by norm_num
      refine mul_nonneg hC (div_nonneg (mul_nonneg hsa.le ?_) (by norm_num))
      rw [h5, sub_zero]
      exact h3
    have hp2 : 0 ≤ C * (r ^ 2 * (r - a * r) - ((r ^ 3 - (a * r) ^ 3) / 3)) := by
      have hinner : r ^ 2 * (r - a * r) - ((r ^ 3 - (a * r) ^ 3) / 3)
          = (1 - a) ^ 2 * (2 + a) * r ^ 3 / 3 := by
        rw [hpow]
        ring
      rw [hinner]
      exact mul_nonneg hC (by positivity)
    have hfin : ENNReal.ofReal
        (C * ((1 - a ^ 2) / a ^ 2 * ((a * r) ^ 3 - 0 ^ 3) / 3)) +
        ENNReal.ofReal
          (C * (r ^ 2 * (r - a * r) - ((r ^ 3 - (a * r) ^ 3) / 3))) =
      ENNReal.ofReal (C * (2 * (1 - a) * r ^ 3 / 3)) := by
      rw [← ENNReal.ofReal_add hp1' hp2, ← mul_add]
      have hkey0 : (1 - a ^ 2) / a ^ 2 * ((a * r) ^ 3 - 0 ^ 3) / 3
          + (r ^ 2 * (r - a * r) - ((r ^ 3 - (a * r) ^ 3) / 3))
          = 2 * (1 - a) * r ^ 3 / 3 := by
        have hpow2 : (a * r) ^ 3 - 0 ^ 3 = a ^ 3 * r ^ 3 := by
          rw [hpow]
          ring
        rw [hpow2]
        field_simp
        ring
      rw [hkey0]
    exact hfin
  rw [hI1, hI2]

/-! ## §5 原点锥帽体积与公开件 -/

/-- 原点锥帽体积主 kernel（`0 < a < 1`、`0 < r`、轴非退化）。 -/
private theorem ccv_volume_conicCap_zero {w : V3} (r a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hr : 0 < r) (hw : w ≠ 0) :
    volume (ccvConicCap 0 w r a) = ENNReal.ofReal (2 / 3 * Real.pi * (1 - a) * r ^ 3) := by
  obtain ⟨e1, e2, e3, he, halign⟩ := exists_on3_eq_smul w hw
  have hax : (w : V3) = dist w 0 • e3 := by
    rw [dist_eq_norm, sub_zero]; exact halign
  have hbw : 0 < dist w 0 := by
    rw [dist_zero_right]
    exact norm_pos_iff.mpr hw
  have hproj := measurePreserving_proj e1 e2 e3 he
  have hpre : ccvConicCap 0 w r a =
      (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹' ccvCapProj r a := by
    ext x
    rw [Set.mem_preimage, ccvCapProj, Set.mem_setOf_eq]
    exact ccv_mem_capProj_iff e1 e2 e3 he hbw hax r a (le_of_lt hr) x
  have hvol : volume (ccvConicCap 0 w r a) = (volume.prod volume) (ccvCapProj r a) := by
    rw [hpre]
    exact hproj.measure_preimage (ccv_capProj_meas r a).nullMeasurableSet
  rw [hvol, Measure.prod_apply (ccv_capProj_meas r a)]
  have hslice : ∀ t : ℝ,
      volume (Prod.mk t ⁻¹' ccvCapProj r a) =
        (if 0 < t then
          ENNReal.ofReal (Real.pi * min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
        else 0) := by
    intro t
    rw [ccv_preimage_capProj]
    by_cases ht : 0 < t
    · rw [if_pos ht]
      have hkey : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t}
          = {ζ : ℂ | ‖ζ‖ ^ 2 ≤ r ^ 2 - t ^ 2 ∧
              ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2} := by
        ext ζ
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          have hcone := ccv_cone_sq_lt ha ha1 ht h2
          refine ⟨?_, hcone⟩
          have hnz := sq_nonneg ‖(ζ : ℂ)‖
          have h6 : t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 := h1
          nlinarith
        · rintro ⟨h1, h2⟩
          have hcone := ccv_cone_sq_lt' ha ha1 ht h2
          refine ⟨?_, hcone⟩
          have hnz := sq_nonneg ‖(ζ : ℂ)‖
          have h6 : ‖ζ‖ ^ 2 ≤ r ^ 2 - t ^ 2 := h1
          nlinarith
      rw [hkey, ccv_volume_lensDisc]
    · rw [if_neg ht]
      have hempty : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧
          a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t} = ∅ := by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2⟩
        have h1 : 0 ≤ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) := by positivity
        linarith
      rw [hempty, measure_empty]
  simp_rw [hslice]
  rw [ccv_lintegral_core r a Real.pi hr ha ha1 Real.pi_pos.le]
  congr 1
  ring

/-- HOL `VOLUME_CONIC_CAP`（flyspeck_multivariate.ml:5057，GT-1 交付件 1）：
锥帽可测 + 体积公式。使用点锚：GRUTOTI.hl:3356-3358/7983-7985（§I 正性）、
PA24:422-433（REUHADY）、TSKAJXY3.hl:1959（STRONG 版另配 bounded/convex）。
集合常数为 `ccvConicCap` 私拷（文件头桥接说明；与 PA15/PA24/PA23 各 conicCap
同体，消费 lane 一行 `rfl` 转移）。 -/
theorem volumeConicCap (v0 v1 : V3) (r a : ℝ) (ha : 0 < a) :
    MeasurableSet (ccvConicCap v0 v1 r a) ∧
      volume.real (ccvConicCap v0 v1 r a) =
        if v1 = v0 ∨ 1 ≤ a ∨ r < 0 then 0
        else 2 / 3 * Real.pi * (1 - a) * r ^ 3 := by
  refine ⟨measurableConicCap v0 v1 r a, ?_⟩
  rcases eq_or_ne v1 v0 with heq | hne
  · rw [heq, ccv_conicCap_empty]
    rw [Measure.real_def, measure_empty, ENNReal.toReal_zero]
    rw [if_pos (by simp)]
  · by_cases hage : 1 ≤ a
    · have hE : ccvConicCap 0 (v1 - v0) r a = ∅ := by
        rw [ccvConicCap, ccv_cone_empty_of_ge 0 (v1 - v0) a hage, Set.inter_empty]
      rw [ccv_conicCap_add_left, hE, Set.image_empty]
      rw [Measure.real_def, measure_empty, ENNReal.toReal_zero]
      rw [if_pos (by exact Or.inr (Or.inl hage))]
    · by_cases hrneg : r < 0
      · have hempty : ccvConicCap v0 v1 r a = ∅ := by
          ext x
          simp only [ccvConicCap, Metric.mem_closedBall, Set.mem_inter_iff,
            Set.mem_empty_iff_false, iff_false]
          intro h
          have hd := dist_nonneg (x := x) (y := v0)
          linarith
        rw [hempty, Measure.real_def, measure_empty, ENNReal.toReal_zero]
        rw [if_pos (by exact Or.inr (Or.inr hrneg))]
      · have hnc : ¬(v1 = v0 ∨ 1 ≤ a ∨ r < 0) := by
          rintro (h | h | h)
          · exact hne h
          · exact hage h
          · exact hrneg h
        have ha1 : a < 1 := lt_of_not_ge hage
        have hr0 : 0 ≤ r := not_lt.mp hrneg
        rw [if_neg hnc]
        rcases eq_or_lt_of_le hr0 with hreq | hrpos
        · have hempty : ccvConicCap v0 v1 r a = ∅ := by
            subst hreq
            ext x
            simp only [ccvConicCap, Metric.mem_closedBall, ccv_mem_cone,
              Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hball, hcone⟩
            have hx0 : x = v0 := by
              have h2 : dist x v0 ≤ 0 := hball
              have h3 : 0 ≤ dist x v0 := dist_nonneg
              have h4 : dist x v0 = 0 := by linarith
              exact dist_eq_zero.mp h4
            rw [hx0] at hcone
            simp only [sub_self, WithLp.ofLp_zero, zero_dotProduct, dist_self,
              zero_mul] at hcone
            linarith
          rw [hempty, ← hreq, Measure.real_def, measure_empty, ENNReal.toReal_zero]
          ring
        · rw [ccv_conicCap_add_left, volume_real_add_left]
          have hvol := ccv_volume_conicCap_zero r a ha ha1 hrpos
            (sub_ne_zero.mpr hne)
          rw [Measure.real_def, hvol, ENNReal.toReal_ofReal (by positivity)]

/-- GT-1 交付件 1 之正性（GRUTOTI §I 锚：GRUTOTI.hl:7983-7985；
PA23:315 `grutoti_volD_pos` 的共享版，按 PA23:307-314 诚实注记补 `hne`）。 -/
theorem volumeConicCapPos {v0 v1 : V3} {r d : ℝ} (hr : 0 < r) (hd : 0 < d) (hd1 : d < 1)
    (hne : v0 ≠ v1) : 0 < volume.real (ccvConicCap v0 v1 r d) := by
  have h := volumeConicCap v0 v1 r d hd
  have hnc : ¬(v1 = v0 ∨ 1 ≤ d ∨ r < 0) := by
    rintro (h0 | h0 | h0)
    · exact hne h0.symm
    · exact absurd h0 (by linarith)
    · exact absurd h0 (by linarith)
  rw [h.2, if_neg hnc]
  positivity

/-! ## §6 楔形（HOL `VOLUME_CONIC_CAP_WEDGE_WEAK`，flyspeck_multivariate.ml:6147）-/

/-- 楔形投影模型集（原点锥帽 ∩ 楔的标架投影像）。 -/
private def ccvWedgeProj (r a θ : ℝ) (u : ℂ) : Set (ℝ × ℂ) :=
  ccvCapProj r a ∩ {p | 0 < ang (u⁻¹ * p.2) ∧ ang (u⁻¹ * p.2) < θ}

/-- HOL `AZIM_DEGENERATE`-类：`wedge`-成员的投影刻画。 -/
private theorem ccv_mem_capWedgeProj_iff {w w1 : V3} (e1 e2 e3 : V3)
    (he : Orthonormal3 e1 e2 e3) {b : ℝ} (hb : 0 < b) (hax : (w : V3) = b • e3)
    (hw : w ≠ 0) (h1 : ¬ Collinear3 0 w w1) (r a : ℝ) (hr : 0 ≤ r) (x : V3) :
    x ∈ ccvConicCap 0 w r a ∩ Kepler.Geom.wedge 0 w w1 w2 ↔
      (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 ≤ r ^ 2 ∧
        a * Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) < x ⬝ᵥ e3 ∧
        0 < ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 x) ∧
        ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 x) < azim 0 w w1 w2 := by
  have hmem : x ∈ ccvConicCap 0 w r a ↔
      (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 ≤ r ^ 2 ∧
        a * Real.sqrt ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2) < x ⬝ᵥ e3 :=
    ccv_mem_capProj_iff e1 e2 e3 he hb hax r a hr x
  have he31 : ‖(e3 : V3)‖ = 1 := by
    have h := norm_sq_eq_dot (x := e3)
    rw [he.2.2.1] at h
    nlinarith [norm_nonneg e3]
  have hbw2 : dist w 0 = b := by
    rw [dist_eq_norm, sub_zero, hax, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.le,
      he31, mul_one]
  have haxD : (w : V3) = dist w 0 • e3 := by
    conv_rhs => rw [hbw2]
    exact hax
  have hcolzx : ∀ z : V3, Collinear3 0 w z → zOf e1 e2 z = 0 := by
    intro z hz
    by_contra hne
    have hax2 : (w - 0 : V3) = dist w 0 • e3 := by
      rw [sub_zero]; exact haxD
    have hnc : ¬ Collinear3 0 w z :=
      (zOf_ne_zero_iff he hax2 hw z).mp
        (by rw [sub_zero]; exact hne)
    exact hnc.elim hz
  have hw1u : zOf e1 e2 w1 ≠ 0 := by
    have hax2 : (w - 0 : V3) = dist w 0 • e3 := by
      rw [sub_zero]; exact haxD
    rw [show zOf e1 e2 w1 = zOf e1 e2 (w1 - 0) from by rw [sub_zero]]
    exact (zOf_ne_zero_iff he hax2 hw w1).mpr h1
  have hang0 : ∀ v : ℂ, v ≠ 0 → ang (v⁻¹ * 0) = 0 := by
    intro v hv
    have h1 : v⁻¹ * 0 = 0 := mul_zero _
    have h2 : ang (0:ℂ) = 0 := by simp [ang, angArg]
    rw [h1, h2]
  rw [Set.mem_inter_iff, hmem, ccv_wedge_simple, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcap, hwedge⟩
    obtain ⟨ha1, ha2⟩ := hwedge
    have hxnc : ¬ Collinear3 0 w x := by
      intro hcol
      rw [ccv_azim_eq_zero_of_collinearY 0 w w1 x hcol] at ha1
      linarith
    rw [azim_eq_ang_of_frame e1 e2 e3 he haxD hw h1 hxnc] at ha1
    rw [azim_eq_ang_of_frame e1 e2 e3 he haxD hw h1 hxnc] at ha2
    exact ⟨hcap.1, hcap.2, ha1, ha2⟩
  · rintro ⟨hcap1, hcap2, ha1, ha2⟩
    have hxnc : ¬ Collinear3 0 w x := by
      intro hcol
      rw [hcolzx x hcol, hang0 (zOf e1 e2 w1) hw1u] at ha1
      linarith
    have hab : azim 0 w w1 x = ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 x) :=
      azim_eq_ang_of_frame e1 e2 e3 he haxD hw h1 hxnc
    rw [← hab] at ha1
    rw [← hab] at ha2
    exact ⟨⟨hcap1, hcap2⟩, ha1, ha2⟩

private theorem ccv_capWedgeProj_meas (r a θ : ℝ) (u : ℂ) :
    MeasurableSet (ccvWedgeProj r a θ u) := by
  have h2 : MeasurableSet {p : ℝ × ℂ | 0 < ang (u⁻¹ * p.2) ∧ ang (u⁻¹ * p.2) < θ} :=
    (measurableSet_lt measurable_const
      (measurable_ang.comp (measurable_const.mul measurable_snd))).inter
      (measurableSet_lt (measurable_ang.comp (measurable_const.mul measurable_snd))
        measurable_const)
  exact (ccv_capProj_meas r a).inter h2

private theorem ccv_preimage_capWedgeProj (r a θ : ℝ) (u : ℂ) (t : ℝ) :
    Prod.mk t ⁻¹' ccvWedgeProj r a θ u =
      {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
        0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
  ext ζ
  simp only [Set.mem_preimage, ccvWedgeProj, Set.mem_inter_iff, ccvCapProj,
    Set.mem_setOf_eq]
  tauto

/-- ℂ 上闭圆盘扇形切片（t 固定）：锥帽楔切片体积。前提 `hYX`：球侧半径不小于
锥侧（`min(r²−t², s·t²) = s·t²`，GLUTOTI/GLUKOTI 使用点均为该情形）。
证法：锥侧集等价（`ccv_cone_sq_lt/'`）+ 闭球条件在 `hYX` 下冗余，集合即开扇形
`{‖ζ‖ < √(s·t²) ∧ 角 ∈ (0, θ)}`，`volume_sector_rot` 收账（hkey 两向以
`sq_lt_sq₀`/`Real.sq_sqrt` 显式转换 order 结构体）。 -/
private theorem ccv_volume_sliceWedge (r a t θ : ℝ) {u : ℂ} (hu : u ≠ 0)
    (ha : 0 < a) (ha1 : a < 1) (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi)
    (ht : 0 < t) (hYX : (1 - a ^ 2) / a ^ 2 * t ^ 2 ≤ r ^ 2 - t ^ 2) :
    volume {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
        0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
      = ENNReal.ofReal (((1 - a ^ 2) / a ^ 2 * t ^ 2) * θ / 2) := by
  have hsq1 : a ^ 2 < 1 := by nlinarith
  have hsX : 0 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
    have h1 : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
      refine div_nonneg (by linarith) (by positivity)
    exact mul_nonneg h1 (sq_nonneg t)
  have hkey : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
      0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
      = {ζ : ℂ | ‖ζ‖ < Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2) ∧
          0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
    ext ζ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hz2 := ccv_cone_sq_lt ha ha1 ht h2
      refine ⟨?_, h3, h4⟩
      have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt hsX]
        exact hz2
      exact (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mp h5
    · rintro ⟨hnorm, h3, h4⟩
      have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mpr hnorm
      have hz2 : ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 := by
        rwa [Real.sq_sqrt hsX] at h5
      refine ⟨?_, ccv_cone_sq_lt' ha ha1 ht hz2, h3, h4⟩
      have h6 : ‖ζ‖ ^ 2 < r ^ 2 - t ^ 2 := lt_of_lt_of_le hz2 hYX
      linarith
  rw [hkey, volume_sector_rot hu (Real.sqrt_nonneg _) hθ0 hθ2π]
  congr 1
  rw [Real.sq_sqrt hsX]

/-- 楔切片 min 版（任意 `0 < t`）：切片体积 = `min(r²−t², s·t²)·θ/2`。
锥侧分支开扇形（`volume_sector_rot`）、球侧分支闭扇形
（`ccv_volume_sectorClosed`，含 `r < t` 空集退化）。 -/
private theorem ccv_volume_sliceWedgeMin (r a t θ : ℝ) {u : ℂ} (hu : u ≠ 0)
    (ha : 0 < a) (ha1 : a < 1) (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) (ht : 0 < t) :
    volume {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
        0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
      = ENNReal.ofReal (min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2) * θ / 2) := by
  have hsa : 0 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 :=
    mul_nonneg (div_nonneg (by nlinarith [sq_nonneg a, ha.le, ha1]) (by positivity))
      (sq_nonneg t)
  -- 圆片双条件等价（ccv_cone_sq_lt/' 两向）
  have hkey : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
      0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
      = {ζ : ℂ | ‖ζ‖ ^ 2 ≤ r ^ 2 - t ^ 2 ∧ ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 ∧
          0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
    ext ζ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ccv_cone_sq_lt ha ha1 ht h2, h3, h4⟩
      nlinarith [sq_nonneg ‖(ζ : ℂ)‖]
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ccv_cone_sq_lt' ha ha1 ht h2, h3, h4⟩
      nlinarith [sq_nonneg ‖(ζ : ℂ)‖]
  rcases le_or_gt (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2) with hXY | hYX
  · -- 球侧限半径：min = r²−t²，闭扇形
    rw [hkey, min_eq_left hXY]
    rcases lt_or_ge (r ^ 2 - t ^ 2) 0 with hneg | hX0
    · -- r² < t²：切片为空（t² + ‖ζ‖² ≥ t² > r²）
      have hempty : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧
          a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
          0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} = ∅ := by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, -, -⟩
        nlinarith [sq_nonneg ‖(ζ : ℂ)‖, hneg]
      rw [← hkey, hempty, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
      nlinarith [mul_nonneg hθ0 (by linarith : (0:ℝ) ≤ -(r ^ 2 - t ^ 2))]
    · -- 0 ≤ r²−t²：临界相等走开扇形、严格走闭扇形
      rcases eq_or_lt_of_le hXY with heq | hlt
      · -- 临界情形 r²−t² = s·t²：集合即开扇形
        rw [heq]
        have hset : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ (1 - a ^ 2) / a ^ 2 * t ^ 2 ∧
            ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 ∧
            0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
            = {ζ : ℂ | ‖ζ‖ < Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2) ∧
                0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
          ext ζ
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨?_, h3, h4⟩
            have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 := by
              rw [Real.sq_sqrt hsa]
              exact h2
            exact (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mp h5
          · rintro ⟨h1, h3, h4⟩
            have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 :=
              (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mpr h1
            rw [Real.sq_sqrt hsa] at h5
            exact ⟨by linarith, h5, h3, h4⟩
        rw [hset, volume_sector_rot hu (Real.sqrt_nonneg _) hθ0 hθ2π]
        congr 1
        rw [Real.sq_sqrt hsa]
      · have hset : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ r ^ 2 - t ^ 2 ∧
              ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 ∧
              0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
            = {ζ : ℂ | ‖ζ‖ ≤ Real.sqrt (r ^ 2 - t ^ 2) ∧
                0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
          ext ζ
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨?_, h3, h4⟩
            have h5 : ‖ζ‖ ^ 2 ≤ (Real.sqrt (r ^ 2 - t ^ 2)) ^ 2 := by
              rw [Real.sq_sqrt hX0]
              exact h1
            exact (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mp h5
          · rintro ⟨h1, h3, h4⟩
            have h5 : ‖ζ‖ ^ 2 ≤ (Real.sqrt (r ^ 2 - t ^ 2)) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mpr h1
            rw [Real.sq_sqrt hX0] at h5
            exact ⟨h5, lt_of_le_of_lt h5 hlt, h3, h4⟩
        rw [hset, ccv_volume_sectorClosed hu (Real.sqrt (r ^ 2 - t ^ 2)) θ
          (Real.sqrt_nonneg _) hθ0 hθ2π]
        congr 1
        rw [Real.sq_sqrt hX0]
  · -- 锥侧限半径：min = s·t²，开扇形
    rw [hkey, min_eq_right hYX.le]
    have hset : {ζ : ℂ | ‖ζ‖ ^ 2 ≤ r ^ 2 - t ^ 2 ∧
            ‖ζ‖ ^ 2 < (1 - a ^ 2) / a ^ 2 * t ^ 2 ∧
            0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ}
        = {ζ : ℂ | ‖ζ‖ < Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2) ∧
            0 < ang (u⁻¹ * ζ) ∧ ang (u⁻¹ * ζ) < θ} := by
      ext ζ
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨?_, h3, h4⟩
        have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt hsa]
          exact h2
        exact (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mp h5
      · rintro ⟨h1, h3, h4⟩
        have h5 : ‖ζ‖ ^ 2 < (Real.sqrt ((1 - a ^ 2) / a ^ 2 * t ^ 2)) ^ 2 :=
          (sq_lt_sq₀ (norm_nonneg ζ) (Real.sqrt_nonneg _)).mpr h1
        rw [Real.sq_sqrt hsa] at h5
        exact ⟨by linarith [h5, hYX], h5, h3, h4⟩
    rw [hset, volume_sector_rot hu (Real.sqrt_nonneg _) hθ0 hθ2π]
    congr 1
    rw [Real.sq_sqrt hsa]

/-- 楔形体积主 kernel（HOL `VOLUME_CONIC_CAP_WEDGE_WEAK` 的 Lean 体）。
证法：照 `ccv_volume_conicCap_zero` 的 Fubini 骨架（hproj/hvol/hslice），
标架投影把楔形变成扇形切片，切片体积 = `min(r²−t², s·t²)·θ/2`
（`ccv_volume_sliceWedgeMin`，θ = azim），核心积分 `ccv_lintegral_core`
以 `C := azim 0 w w1 w2 / 2` 收账。 -/
private theorem ccv_volume_conicCapWedge_zero {w w1 w2 : V3} (r a : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hr : 0 < r) (h1 : ¬ Collinear3 0 w w1) (h2 : ¬ Collinear3 0 w w2) :
    volume (ccvConicCap 0 w r a ∩ Kepler.Geom.wedge 0 w w1 w2)
      = ENNReal.ofReal (azim 0 w w1 w2 * ((1 - a) * r ^ 3) / 3) := by
  have hw : w ≠ 0 := by
    rintro rfl
    exact h1 (collinear3_of_eq rfl)
  obtain ⟨e1, e2, e3, he, halign⟩ := exists_on3_eq_smul w hw
  have hax : (w : V3) = dist w 0 • e3 := by
    rw [dist_eq_norm, sub_zero]; exact halign
  have hbw : 0 < dist w 0 := by
    rw [dist_zero_right]
    exact norm_pos_iff.mpr hw
  have hproj := measurePreserving_proj e1 e2 e3 he
  have hax2 : (w - 0 : V3) = dist w 0 • e3 := by
    rw [sub_zero]; exact hax
  have hw1u : zOf e1 e2 w1 ≠ 0 := by
    rw [show zOf e1 e2 w1 = zOf e1 e2 (w1 - 0) from by rw [sub_zero]]
    exact (zOf_ne_zero_iff he hax2 hw w1).mpr h1
  have hθ0 : 0 ≤ azim 0 w w1 w2 := azim_nonneg 0 w w1 w2
  have hθ2π : azim 0 w w1 w2 < 2 * Real.pi := azim_lt_two_pi 0 w w1 w2
  have hpre : ccvConicCap 0 w r a ∩ Kepler.Geom.wedge 0 w w1 w2 =
      (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹'
        ccvWedgeProj r a (azim 0 w w1 w2) (zOf e1 e2 w1) := by
    ext x
    rw [Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨hb, hc, ha1', ha2'⟩ :=
        (ccv_mem_capWedgeProj_iff e1 e2 e3 he hbw hax hw h1 r a (le_of_lt hr) x).mp hx
      rw [ccvWedgeProj, Set.mem_inter_iff, ccvCapProj, Set.mem_setOf_eq,
        Set.mem_setOf_eq]
      exact ⟨⟨hb, hc⟩, ha1', ha2'⟩
    · intro hx
      rw [ccvWedgeProj, Set.mem_inter_iff, ccvCapProj, Set.mem_setOf_eq,
        Set.mem_setOf_eq] at hx
      exact (ccv_mem_capWedgeProj_iff e1 e2 e3 he hbw hax hw h1 r a (le_of_lt hr) x).mpr
        ⟨hx.1.1, hx.1.2, hx.2.1, hx.2.2⟩
  have hvol : volume (ccvConicCap 0 w r a ∩ Kepler.Geom.wedge 0 w w1 w2)
      = (volume.prod volume) (ccvWedgeProj r a (azim 0 w w1 w2) (zOf e1 e2 w1)) := by
    rw [hpre]
    exact hproj.measure_preimage (ccv_capWedgeProj_meas r a _ _).nullMeasurableSet
  rw [hvol, Measure.prod_apply (ccv_capWedgeProj_meas r a _ _)]
  have hslice : ∀ t : ℝ,
      volume (Prod.mk t ⁻¹' ccvWedgeProj r a (azim 0 w w1 w2) (zOf e1 e2 w1)) =
        (if 0 < t then
          ENNReal.ofReal ((azim 0 w w1 w2 / 2) *
            min (r ^ 2 - t ^ 2) ((1 - a ^ 2) / a ^ 2 * t ^ 2))
        else 0) := by
    intro t
    rw [ccv_preimage_capWedgeProj]
    by_cases ht : 0 < t
    · rw [if_pos ht, ccv_volume_sliceWedgeMin r a t (azim 0 w w1 w2) hw1u ha ha1
        hθ0 hθ2π ht]
      congr 1
      ring
    · rw [if_neg ht]
      have hempty : {ζ : ℂ | t ^ 2 + ‖ζ‖ ^ 2 ≤ r ^ 2 ∧
          a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) < t ∧
          0 < ang ((zOf e1 e2 w1)⁻¹ * ζ) ∧
          ang ((zOf e1 e2 w1)⁻¹ * ζ) < azim 0 w w1 w2} = ∅ := by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2', -, -⟩
        have h1' : 0 ≤ a * Real.sqrt (t ^ 2 + ‖ζ‖ ^ 2) := by positivity
        linarith
      rw [hempty, measure_empty]
  simp_rw [hslice]
  rw [ccv_lintegral_core r a (azim 0 w w1 w2 / 2) hr ha ha1
    (div_nonneg hθ0 (by norm_num : (0:ℝ) ≤ 2))]
  congr 1
  ring

/-- 帽半径非正时为空（`r ≤ 0`：球点只剩 `v0`，被锥条件排除）。 -/
private theorem ccv_conicCap_rle0 {v0 v1 : V3} (r a : ℝ) (hr : r ≤ 0) :
    ccvConicCap v0 v1 r a = ∅ := by
  ext x
  simp only [ccvConicCap, Metric.mem_closedBall, ccv_mem_cone, Set.mem_inter_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨hball, hcone⟩
  have hd := dist_nonneg (x := x) (y := v0)
  have h0 : dist x v0 = 0 := le_antisymm (by linarith) hd
  have hx : x = v0 := dist_eq_zero.mp h0
  rw [hx] at hcone
  simp only [sub_self, WithLp.ofLp_zero, zero_dotProduct, dist_self, zero_mul] at hcone
  linarith

/-- w1 与轴共线时 `azim v0 v1 w1 · ≡ 0`，开楔为空（azim 定义 if 正分支）。 -/
private theorem ccv_wedge_empty_of_collinearW1 {v0 v1 w1 w2 : V3}
    (hc1 : Collinear3 v0 v1 w1) : Kepler.Geom.wedge v0 v1 w1 w2 = ∅ := by
  ext y
  simp only [Kepler.Geom.wedge, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, ha1, -⟩
  have h0 : azim v0 v1 w1 y = 0 := by
    rw [azim, if_pos (Or.inl hc1)]
  rw [h0] at ha1
  linarith

/-- 楔可测（无需退化前提）：主情形经轴向标架把楔 transport 成连续映射
`y ↦ zOf e1 e2 (y − v0)` 的原像（`zOf ≠ 0` 恰为离轴 + `azim_eq_ang_of_frame`
桥接），像集为 Borel 扇形；w1 共线/轴退化时楔空。 -/
private theorem ccv_measSet_wedge (v0 v1 w1 w2 : V3) :
    MeasurableSet (Kepler.Geom.wedge v0 v1 w1 w2) := by
  by_cases hv : v1 = v0
  · rw [hv, ccv_wedge_empty_of_collinearW1 (by
      exact collinear3_of_eq rfl : Collinear3 v0 v0 w1)]
    exact MeasurableSet.empty
  · by_cases hc1 : Collinear3 v0 v1 w1
    · rw [ccv_wedge_empty_of_collinearW1 hc1]
      exact MeasurableSet.empty
    · obtain ⟨e1, e2, e3, he, halign⟩ :=
        exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hv)
      have hax : (v1 - v0 : V3) = dist (v1 - v0) 0 • e3 := by
        rw [dist_eq_norm, sub_zero]; exact halign
      have hax2 : (v1 - v0 : V3) = dist v1 v0 • e3 := by
        rw [dist_eq_norm]; exact halign
      have hcont : Continuous fun y : V3 => zOf e1 e2 (y - v0) := by
        simp only [zOf]
        fun_prop
      have hset : Kepler.Geom.wedge v0 v1 w1 w2
          = (fun y : V3 => zOf e1 e2 (y - v0)) ⁻¹'
              {ζ : ℂ | ζ ≠ 0 ∧ 0 < ang ((zOf e1 e2 (w1 - v0))⁻¹ * ζ) ∧
                ang ((zOf e1 e2 (w1 - v0))⁻¹ * ζ) < azim v0 v1 w1 w2} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Kepler.Geom.wedge]
        constructor
        · rintro ⟨hnc, ha1, ha2⟩
          have hframe := azim_eq_ang_of_frame e1 e2 e3 he hax (sub_ne_zero.mpr hv)
            (ccv_collinear3_zero_sub.not.mp hc1)
            (ccv_collinear3_zero_sub.not.mp hnc)
          refine ⟨(zOf_ne_zero_iff he hax2 hv y).mpr hnc, ?_, ?_⟩
          · rw [ccv_azim_sub_self v0 v1 w1 y, hframe] at ha1
            exact ha1
          · rw [ccv_azim_sub_self v0 v1 w1 y, hframe] at ha2
            exact ha2
        · rintro ⟨hne0, ha1, ha2⟩
          have hframe := azim_eq_ang_of_frame e1 e2 e3 he hax (sub_ne_zero.mpr hv)
            (ccv_collinear3_zero_sub.not.mp hc1)
            (ccv_collinear3_zero_sub.not.mp
              ((zOf_ne_zero_iff he hax2 hv y).mp hne0))
          refine ⟨(zOf_ne_zero_iff he hax2 hv y).mp hne0, ?_, ?_⟩
          · rw [← hframe] at ha1
            rw [ccv_azim_sub_self v0 v1 w1 y]
            exact ha1
          · rw [← hframe] at ha2
            rw [ccv_azim_sub_self v0 v1 w1 y]
            exact ha2
      rw [hset]
      refine hcont.measurable
        (((measurableSet_singleton (0:ℂ)).compl).inter ?_)
      exact (measurableSet_lt measurable_const
          (measurable_ang.comp (measurable_const.mul measurable_id))).inter
        (measurableSet_lt (measurable_ang.comp (measurable_const.mul measurable_id))
          measurable_const)

/-- HOL `MEASURABLE_CONIC_CAP_WEDGE`（flyspeck_multivariate.ml:6365，
GT-1 wedge 交付件之可测性）：锥帽楔交集 Borel，无退化前提。 -/
theorem measurableConicCapWedge (v0 v1 w1 w2 : V3) (r a : ℝ) :
    MeasurableSet (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2) :=
  (measurableConicCap v0 v1 r a).inter (ccv_measSet_wedge v0 v1 w1 w2)

/-- HOL `VOLUME_CONIC_CAP_WEDGE_WEAK`（flyspeck_multivariate.ml:6147，
GT-1 wedge 交付件主形）：`0 < a` 双非共线下楔帽交集有界可测，
体积 = `azim/3·(1−a)·r³`（`1 ≤ a` 或 `r < 0` 时为 0）。
使用点：GRUTOTI §D/§F（HL:3208/3516/4767/5154/6544/6928）。 -/
theorem volumeConicCapWedgeFormula (v0 v1 w1 w2 : V3) (r a : ℝ) (ha : 0 < a)
    (h1 : ¬ Collinear3 v0 v1 w1) (h2 : ¬ Collinear3 v0 v1 w2) :
    Bornology.IsBounded (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2) ∧
      MeasurableSet (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2) ∧
      volume.real (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2) =
        if 1 ≤ a ∨ r < 0 then 0
        else azim v0 v1 w1 w2 / 3 * (1 - a) * r ^ 3 := by
  refine ⟨(boundedConicCap v0 v1 r a).subset Set.inter_subset_left,
    measurableConicCapWedge v0 v1 w1 w2 r a, ?_⟩
  rcases eq_or_ne v1 v0 with he | hne
  · rw [he, ccv_conicCap_empty, Set.empty_inter, Measure.real_def, measure_empty,
      ENNReal.toReal_zero]
    split
    · rfl
    · rw [show azim v0 v0 w1 w2 = 0 by
        rw [azim, if_pos (Or.inl (collinear3_of_eq rfl : Collinear3 v0 v0 w1))]]
      ring
  · rcases lt_or_ge r 0 with hrneg | hr0
    · rw [ccv_conicCap_rle0 r a (le_of_lt hrneg), Set.empty_inter, Measure.real_def,
        measure_empty, ENNReal.toReal_zero, if_pos (Or.inr hrneg)]
    · rcases eq_or_lt_of_le hr0 with hreq | hrpos
      · rw [ccv_conicCap_rle0 r a hreq.symm.le, Set.empty_inter, Measure.real_def,
          measure_empty, ENNReal.toReal_zero]
        split
        · rfl
        · rw [← hreq]
          ring
      · by_cases hge : 1 ≤ a
        · -- 1 ≤ a：帽空
          have hE : ccvConicCap v0 v1 r a = ∅ := by
            rw [ccv_conicCap_add_left, show ccvConicCap 0 (v1 - v0) r a = ∅ from by
              rw [ccvConicCap, ccv_cone_empty_of_ge 0 (v1 - v0) a hge, Set.inter_empty],
              Set.image_empty]
          rw [hE, Set.empty_inter, Measure.real_def, measure_empty,
            ENNReal.toReal_zero, if_pos (Or.inl hge)]
        · -- 主情形：0 < a < 1，0 < r，双非共线，平移 + kernel
          have ha1 : a < 1 := lt_of_not_ge hge
          have hage : ¬ (1 ≤ a ∨ r < 0) := by
            rintro (h | h)
            · exact hge h
            · linarith
          have hkey : volume.real
                (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2)
              = volume.real (ccvConicCap 0 (v1 - v0) r a
                  ∩ Kepler.Geom.wedge 0 (v1 - v0) (w1 - v0) (w2 - v0)) := by
            rw [ccv_conicCap_add_left, ccv_wedge_sub_self,
              ← Set.image_inter (f := fun y : V3 => v0 + y)
                (fun a' b' h => add_left_cancel h), volume_real_add_left]
          rw [if_neg hage, hkey, Measure.real_def,
            ccv_volume_conicCapWedge_zero r a ha ha1 hrpos
              (ccv_collinear3_zero_sub.not.mp h1)
              (ccv_collinear3_zero_sub.not.mp h2),
            ENNReal.toReal_ofReal (div_nonneg
              (mul_nonneg (azim_nonneg 0 (v1 - v0) (w1 - v0) (w2 - v0))
                (mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg hrpos.le 3)))
              (by norm_num)),
            ← ccv_azim_sub_self]
          ring

/-- HOL `VOLUME_CONIC_CAP_WEDGE`-WEAK 的 vol·azim/2π 形（GRUTOTI §D/§F、
PA24:428 `volumeConicCapWedgeGeVsConicCap` 对接形状）：楔帽体积 =
锥帽体积 × `azim/2π`。 -/
theorem volumeConicCapWedge (v0 v1 w1 w2 : V3) (r a : ℝ) (ha : 0 < a)
    (h1 : ¬ Collinear3 v0 v1 w1) (h2 : ¬ Collinear3 v0 v1 w2) :
    volume.real (ccvConicCap v0 v1 r a ∩ Kepler.Geom.wedge v0 v1 w1 w2)
      = volume.real (ccvConicCap v0 v1 r a) * azim v0 v1 w1 w2 / (2 * Real.pi) := by
  obtain ⟨-, -, hvol⟩ := volumeConicCapWedgeFormula v0 v1 w1 w2 r a ha h1 h2
  obtain ⟨-, hcap⟩ := volumeConicCap v0 v1 r a ha
  rw [hvol, hcap]
  by_cases hc : 1 ≤ a ∨ r < 0
  · rw [if_pos hc]
    rcases hc with h | h
    · rw [if_pos (Or.inr (Or.inl h))]; ring
    · rw [if_pos (Or.inr (Or.inr h))]; ring
  · rw [if_neg hc]
    have hvne : ¬ (v1 = v0 ∨ 1 ≤ a ∨ r < 0) := by
      rintro (h | h | h)
      · exact h1 (by rw [h]; exact collinear3_of_eq rfl)
      · exact hc (Or.inl h)
      · exact hc (Or.inr h)
    rw [if_neg hvne, eq_div_iff (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    ring

/-- 三元仿射组合入三点仿射包（LuneVolume `mem_affineSpan_triple_of_eq` 私拷）。 -/
private theorem ccv_mem_affineSpan_triple {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (p - x) + h • (q - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd1 : c • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd2 : h • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd3 : c • (p - x) + h • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd1 hd2
  have hval : y = (c • (p - x) + h • (q - x)) +ᵥ x := by
    rw [vadd_eq_add, hy]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd3 hxS

/-- HOL `AZIM_EQ_0_PI_IMP_COPLANAR`（flyspeck_multivariate.ml:2771）：
方位角为 0 或 π ⟹ 四点共面。
证法：退化情形（`Collinear3 v0 v1 w1/w2`）经 `collinear3_iff_smul` +
`coplanar_triple`+`Coplanar.subset` 直接收；主情形 azim = 0 经
`azim_eq_zero_iff_alt`+`affGt_pair_iff` 的射线分解，azim = π 经
`azim_frame_spec` 的 ψ+π 极角展开（`rep_of_zOf`+`Real.cos/sin_add_pi`）得
`w2 − v0 = −(r2/r1)•(w1−v0) + t•(v1−v0)`；两向都以
`ccv_mem_affineSpan_triple` 收进 `affineSpan {v0,w1,v1}`。 -/
theorem AZIM_EQ_0_PI_IMP_COPLANAR (v0 v1 w1 w2 : V3)
    (h : azim v0 v1 w1 w2 = 0 ∨ azim v0 v1 w1 w2 = Real.pi) :
    Coplanar ({v0, v1, w1, w2} : Set V3) := by
  by_cases hv01 : v0 = v1
  · -- 退化一：v0 = v1，直接丢 v1
    rw [← hv01]
    refine ⟨v0, w1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hp
    · exact mem_affineSpan ℝ (by simp)
    · rcases hp with rfl | hp
      · exact mem_affineSpan ℝ (by simp)
      · rcases hp with rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
  have hv10 : v1 ≠ v0 := fun he => hv01 he.symm
  by_cases hc1 : Collinear3 v0 v1 w1
  · -- 退化二：w1 在 v0v1 线上，w1 ∈ affineSpan {v0,v1}
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hv10).mp hc1
    refine ⟨v0, v1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hp
    · exact mem_affineSpan ℝ (by simp)
    · rcases hp with rfl | hp
      · exact mem_affineSpan ℝ (by simp)
      · rcases hp with rfl | rfl
        · exact ccv_mem_affineSpan_triple (c := c) (h := 0)
            (by rw [zero_smul, add_zero, ← hc]; abel)
        · exact mem_affineSpan ℝ (by simp)
  by_cases hc2 : Collinear3 v0 v1 w2
  · -- 退化三：w2 在 v0v1 线上
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hv10).mp hc2
    refine ⟨v0, v1, w1, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hp
    · exact mem_affineSpan ℝ (by simp)
    · rcases hp with rfl | hp
      · exact mem_affineSpan ℝ (by simp)
      · rcases hp with rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact ccv_mem_affineSpan_triple (c := c) (h := 0)
            (by rw [zero_smul, add_zero, ← hc]; abel)
  -- 主情形
  rcases h with h0 | hpi
  · -- azim = 0：affGt 射线分解
    have hw2gt : w2 ∈ affGt ({v0, v1} : Set V3) ({w1} : Set V3) :=
      (azim_eq_zero_iff_alt hc1 hc2).mp h0
    obtain ⟨c, hcpos, t, hdec⟩ :=
      (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w1) (y := w2)
        hv01
        (fun he => hc1 (collinear3_pair_left he))
        (fun he => hc1 (collinear3_pair_right he))).mp hw2gt
    refine ⟨v0, w1, v1, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hp
    · exact mem_affineSpan ℝ (by simp)
    · rcases hp with rfl | hp
      · exact mem_affineSpan ℝ (by simp)
      · rcases hp with rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact ccv_mem_affineSpan_triple (c := c) (h := t)
            (by rw [show p = v0 + (p - v0) from by abel, hdec]; abel)
  · -- azim = π：标架极坐标，ψ+π 展开
    obtain ⟨e1, e2, e3, he, halign⟩ := exists_on3_eq_smul (v1 - v0 : V3)
      (sub_ne_zero.mpr hv10)
    have hax : (v1 - v0 : V3) = dist v1 v0 • e3 := by
      rw [dist_eq_norm]
      exact halign
    obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec hc1 hc2 he hax hv10
    rw [hpi] at hz2
    have href1 := rep_of_zOf he hax hv10 w1 ψ r1 hz1
    have href2 := rep_of_zOf he hax hv10 w2 (ψ + Real.pi) r2 hz2
    set t1 := ((w1 - v0 : V3) ⬝ᵥ e3) / dist v1 v0 with ht1def
    set t2 := ((w2 - v0 : V3) ⬝ᵥ e3) / dist v1 v0 with ht2def
    have hrc : (r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2
        = (w1 - v0 : V3) - t1 • (v1 - v0) := by
      rw [href1]
      abel
    have hr10 : r1 ≠ 0 := hr1.ne'
    have hscal1 : (-(r2 / r1)) * (r1 * Real.cos ψ) = r2 * -(Real.cos ψ) := by
      field_simp
    have hscal2 : (-(r2 / r1)) * (r1 * Real.sin ψ) = r2 * -(Real.sin ψ) := by
      field_simp
    have hA2 : (r2 * Real.cos (ψ + Real.pi)) • e1 + (r2 * Real.sin (ψ + Real.pi)) • e2
        = (-(r2 / r1)) • ((r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2) := by
      rw [Real.cos_add_pi, Real.sin_add_pi, smul_add, smul_smul, smul_smul, hscal1, hscal2]
    have hkey : (w2 - v0 : V3)
        = (-(r2 / r1)) • (w1 - v0 : V3) + ((r2 / r1) * t1 + t2) • (v1 - v0) := by
      rw [href2, hA2, hrc]
      module
    refine ⟨v0, w1, v1, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | hp
    · exact mem_affineSpan ℝ (by simp)
    · rcases hp with rfl | hp
      · exact mem_affineSpan ℝ (by simp)
      · rcases hp with rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact ccv_mem_affineSpan_triple (c := -(r2 / r1)) (h := (r2 / r1) * t1 + t2)
            (by rw [show p = v0 + (p - v0) from by abel, hkey]; abel)

end Kepler.Text
/-! ## §7 公开件公理体检 -/

#print axioms Kepler.Text.volumeConicCap
#print axioms Kepler.Text.volumeConicCapPos
#print axioms Kepler.Text.measurableConicCap
#print axioms Kepler.Text.boundedConicCap
#print axioms Kepler.Text.measurableConicCapWedge
#print axioms Kepler.Text.volumeConicCapWedgeFormula
#print axioms Kepler.Text.volumeConicCapWedge
