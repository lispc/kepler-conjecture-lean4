/-
Kepler.Text.FanBaseKit — F0-a 首发车道（fanbase-f0a-w1）：fan 基座总根
`EE_EXPAND_BB_VV` 与 azim-neg 六件，在 LA1 世界 `ScsV39` 型成件。

为什么是新模块：LA13 §6/§4 的 `_p13` 件全部定义在平行记录 `ScsV39P13` 上，
与 LA1 `ScsV39` 字段同构但**不 defeq**（fanbase-scout-w1 §3 类型墙）；真实
消费者（LA33 `MM_SCS_OPP_p33`/`YXIONXL2_p33`、LA32 opp-支柱、LA1 三 `_concl`）
全部在 `ScsV39` 世界，故在 LA13 原位填 `_p13` 无法被消费。本模块以 LA1
`ScsV39`/`isScsV39`/`BBsV39`/`ee` 成件，root import = {LocalAuto1,
Kepler.Geom.AzimLemmas, Mathlib}，零环（LA1/LA13/LA33 均不 import 本模块的
任何目标）。

HOL 锚与 LA13 `_p13` 孪生（逐槽对照见 PLAN.md）：
- `EE_EXPAND_BB_VV`      HOL YXIONXL2.hl:714-748；LA13 :1555（`_p13` sorry）
- `AZIM_EQ_PI_POINT_SYM_0` HOL :1350；LA13 :1503
- `SUM_AZIM_SYM_0`         HOL :1361（:1371 verbatim 重复）；LA13 :1510
- `AZIM_NEG_FIRST_PI`      HOL :1883；LA13 :1518
- `AZIM_COMPL_NEG`         HOL :1932；LA13 :1526
- `REMOVE_NEG_AZIM1_SYM_0` HOL :1961；LA13 :1533
- `AZIM_NEG`               HOL :2014；LA13 :1540

证法说明（陈述逐槽同 `_p13` 孪生，证体比 HOL 短，零新数学）：
- EE_EXPAND_BB_VV：HOL 走 local_fan σ-轨道（LOFA_IMP_EE_TWO_ELMS_INS_ND +
  CARD_V_EQ_SCS_K1 + VV_SUC_EQ_RHO_NODE_PRIME + ITER_CARD_MINUS1_EQ_IVS_RN1）。
  本证走纯组合路线：isScsV39 的 `2 ≤ s.a i j`（i j < k, i ≠ j）+ BBsV39 的
  dist 下界给出「模 k 单射」（即 HOL CARD_V_EQ_SCS_K1 内部引用的 VV_INJ 内容），
  与周期性合起来直接展开邻域集。fan 侧假设（hV/hFF/hbb 的 fan 合取）按孪生
  保留在陈述里，证体不需要。
- azim-neg 六件：HOL 走 AZIM_UNIQUE 显式正交标架见证；本证走 AzimSpec 组装 +
  `azim_eq_of_spec`（Assembly.lean §2c.6 `azimSpecNeg`/`azimMirror` 的同款
  路线与病理对策）。`AZIM_NEG` 在 Assembly 已有同形已证件但是 private 不可
  import，本模块按其证明私有大段移植（mirrorRep/on3Mirror 同源拷贝）。
  `SUM_AZIM_SYM_0` 的 HOL `Fan.sum4_azim_fan` 亦以显式 spec 组装替代。
-/

import Kepler.Text.LocalAuto1
import Kepler.Geom.AzimLemmas
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace Kepler.Text

open Kepler.Geom Set

/-! ## 私有机械件：mod / 周期 / pair（LA13 `_p13` 孪生同名加 `Fb`） -/

/-- LA13 `periodicAddP13`（LocalAuto13.lean:352）孪生。 -/
private theorem periodicAddFb {α : Sort*} {f : ℕ → α} {k : ℕ}
    (hper : Periodic f k) : ∀ q j, f (j + q * k) = f j := by
  intro q
  induction q with
  | zero => intro j; simp
  | succ n ih =>
      intro j
      have hsplit : j + Nat.succ n * k = j + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      rw [hsplit, hper, ih j]

/-- LA13 `periodicModP13`（LocalAuto13.lean:363）孪生。 -/
private theorem periodicModFb {α : Sort*} {f : ℕ → α} {k : ℕ}
    (hper : Periodic f k) (j : ℕ) : f (j % k) = f j := by
  have h := periodicAddFb hper (j / k) (j % k)
  rw [Nat.mul_comm] at h
  rw [Nat.mod_add_div j k] at h
  exact h.symm

/-- `i ≡ j (mod k) → i+1 ≡ j+1 (mod k)`。 -/
private theorem modSuccFb {k i j : ℕ} (h : i % k = j % k) : (i + 1) % k = (j + 1) % k := by
  have e1 : (i + 1) % k = (i % k + 1 % k) % k := Nat.add_mod i 1 k
  have e2 : (j + 1) % k = (j % k + 1 % k) % k := Nat.add_mod j 1 k
  rw [e1, e2, h]

/-- `2 ≤ k` 时 `j` 与 `j+1` 模 k 不同余。 -/
private theorem modNeSuccFb {k j : ℕ} (hk : 2 ≤ k) : j % k ≠ (j + 1) % k := by
  intro heq
  have hkpos : 0 < k := by omega
  have hr : j % k < k := Nat.mod_lt j hkpos
  have h1mod : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hsplit : (j + 1) % k = (j % k + 1) % k := by rw [Nat.add_mod, h1mod]
  rw [hsplit] at heq
  rcases Nat.lt_or_ge (j % k + 1) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have heq2 : j % k + 1 = k := by omega
    rw [heq2, Nat.mod_self] at heq
    omega

/-- `(j+1) ≡ i (mod k) → j ≡ i + k - 1 (mod k)`。 -/
private theorem modPredFb {k i j : ℕ} (hk1 : 1 ≤ k) (h : (j + 1) % k = i % k) :
    j % k = (i + (k - 1)) % k := by
  have hk0 : k ≠ 0 := by omega
  have e1 : (j + k) % k = j % k := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have hsplit : j + k = (j + 1) + (k - 1) := by omega
  calc j % k = (j + k) % k := e1.symm
  _ = ((j + 1) + (k - 1)) % k := by rw [hsplit]
  _ = ((j + 1) % k + (k - 1) % k) % k := Nat.add_mod _ _ _
  _ = (i % k + (k - 1) % k) % k := by rw [h]
  _ = (i + (k - 1)) % k := (Nat.add_mod i (k - 1) k).symm

/-- 二元集交换（Assembly `pairSetComm` 孪生）。 -/
private theorem pairSetCommFb (p q : V3) : ({p, q} : Set V3) = {q, p} := by
  ext r
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-! ## 私有机械件：原点固定三点共线的取反传输 -/

/-- 共线三点集非退化读法：`¬Collinear3 0 a b` 给出三个互异。 -/
private theorem collinear3_zero_neFb {a b : V3} (h : ¬ Collinear3 0 a b) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  refine ⟨fun he => h ?_, fun he => h ?_, fun he => h ?_⟩
  · show Collinear ℝ ({0, a, b} : Set V3)
    rw [he]
    have hset : ({0, 0, b} : Set V3) = ({0, b} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ 0 b
  · show Collinear ℝ ({0, a, b} : Set V3)
    rw [he]
    have hset : ({0, a, 0} : Set V3) = ({0, a} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ 0 a
  · show Collinear ℝ ({0, a, b} : Set V3)
    rw [he]
    have hset : ({0, b, b} : Set V3) = ({0, b} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ 0 b

/-- Assembly `collinear3_zero_neg`（Assembly.lean:2517，private）孪生：
`{0,a,b}` ↔ `{0,-a,-b}`。 -/
private theorem collinear3_zero_negFb {a b : V3} :
    Collinear3 0 a b ↔ Collinear3 0 (-a) (-b) := by
  by_cases ha : a = 0
  · subst ha
    simp only [neg_zero]
    exact ⟨fun _ => collinear3_of_eq rfl, fun _ => collinear3_of_eq rfl⟩
  · rw [collinear3_iff_smul ha, collinear3_iff_smul (by simpa using ha)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hc' : (b : V3) = c • a := by simpa using hc
      rw [sub_zero, sub_zero, smul_neg, hc']
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hc' : (-b : V3) = c • (-a) := by simpa using hc
      rw [smul_neg] at hc'
      have h2 := congrArg Neg.neg hc'
      simpa using h2

/-- 仅翻转第二点：`{0,a,b}` ↔ `{0,a,-b}`。 -/
private theorem collinear3_zero_negRFb {a b : V3} :
    Collinear3 0 a b ↔ Collinear3 0 a (-b) := by
  by_cases ha : a = 0
  · subst ha
    exact ⟨fun _ => collinear3_of_eq rfl, fun _ => collinear3_of_eq rfl⟩
  · rw [collinear3_iff_smul ha, collinear3_iff_smul ha]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      simpa [sub_zero, neg_smul] using congrArg Neg.neg hc
    · rintro ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      simpa [sub_zero, neg_smul] using congrArg Neg.neg hc

/-- 仅翻转轴点：`{0,-a,b}` ↔ `{0,a,b}`。 -/
private theorem collinear3_zero_negLFb {a b : V3} :
    Collinear3 0 (-a) b ↔ Collinear3 0 a b := by
  constructor
  · intro hc
    exact collinear3_zero_negFb.mpr ((collinear3_zero_negRFb (a := -a) (b := b)).mp hc)
  · intro hc
    exact collinear3_zero_negRFb.mpr (collinear3_zero_negFb.mp hc)

/-! ## 私有机械件：镜像标架 kit（Assembly §2c.6 同源拷贝，彼处 private） -/

private theorem dotPi_neg_leftFb (f g : Fin 3 → ℝ) : (-f) ⬝ᵥ g = -(f ⬝ᵥ g) := by
  simp [dotProduct, Pi.neg_apply, Finset.sum_neg_distrib]

private theorem dotPi_neg_rightFb (f g : Fin 3 → ℝ) : f ⬝ᵥ (-g) = -(f ⬝ᵥ g) := by
  simp [dotProduct, Pi.neg_apply, Finset.sum_neg_distrib]

private theorem dotPi_neg_negFb (f g : Fin 3 → ℝ) : (-f) ⬝ᵥ (-g) = f ⬝ᵥ g := by
  simp [dotProduct, Pi.neg_apply, neg_mul, mul_neg]

private theorem cross_neg_leftFb (f g : Fin 3 → ℝ) :
    crossProduct (-f) g = -(crossProduct f g) := by
  funext i
  fin_cases i <;> simp [cross_apply, Pi.neg_apply]

/-- Assembly `on3Mirror`（Assembly.lean:2497，private）孪生：
镜像标架 `(-e1, e2, -e3)` 保持标准正交 + 右手性。 -/
private theorem on3MirrorFb {e1 e2 e3 : V3} (he : Orthonormal3 e1 e2 e3) :
    Orthonormal3 (-e1) e2 (-e3) := by
  obtain ⟨h11, h22, h33, h12, h13, h23, hc⟩ := he
  refine ⟨?_, h22, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_negFb, h11]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_negFb, h33]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_leftFb, h12, neg_zero]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_negFb, h13]
  · simp only [WithLp.ofLp_neg]
    rw [dotPi_neg_rightFb, h23, neg_zero]
  · have h1 : (((-e1 : V3) : Fin 3 → ℝ)) = -(e1 : Fin 3 → ℝ) := by simp
    have h2 : (((-e3 : V3) : Fin 3 → ℝ)) = -(e3 : Fin 3 → ℝ) := by simp
    rw [h1, cross_neg_leftFb, h2, dotPi_neg_leftFb, dotPi_neg_rightFb, neg_neg]
    exact hc

/-- Assembly `mirrorRep`（Assembly.lean:2537，private）孪生：
镜像坐标传输（neg 取反把 `(cos β, sin β)` 分量变为 `(cos (-β), sin (-β))`）。 -/
private theorem mirrorRepFb (e1 e2 u t : V3) (α β h : ℝ)
    (hrep : u - 0 = (α * Real.cos β) • (-e1) + (α * Real.sin β) • e2 + h • (t - 0)) :
    -u - 0 = (α * Real.cos (-β)) • e1 + (α * Real.sin (-β)) • e2 + h • (-t - 0) := by
  have hsub : (-u : V3) - 0 = -(u - 0) := by simp
  have key : (-u : V3) - 0
      = -((α * Real.cos β) • (-e1) + (α * Real.sin β) • e2 + h • (t - 0)) := by
    rw [hsub, hrep]
  rw [Real.cos_neg, Real.sin_neg, key]
  simp [neg_smul, smul_neg, mul_neg]
  abel

/-! ## azim-neg 六件之一：AZIM_EQ_PI_POINT_SYM_0（HOL :1350；LA13 :1503） -/

/-- AzimSpec 组装：`AzimSpec 0 v w (-w) π`（对径点角为 π）。 -/
private theorem azimSpecOppPiFb {v w : V3} (h : ¬ Collinear3 0 v w) :
    AzimSpec 0 v w (-w) Real.pi := by
  obtain ⟨θ0, hspec⟩ := azimSpec_exists h h
  obtain ⟨hh1, hh2, hbody⟩ := hspec.2.2
  refine ⟨Real.pi_pos.le, by linarith [Real.pi_pos], hh1, -hh1, ?_⟩
  intro e1 e2 e3 he hax hvn
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hbody e1 e2 e3 he hax hvn
  refine ⟨ψ, r1, r1, hrep1, ?_, hr1, hr1⟩
  have hsub : (-w - 0 : V3) = -(w - 0) := by simp
  have key : (-w - 0 : V3)
      = -((r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2 + hh1 • (v - 0)) := by
    rw [hsub, hrep1]
  have hcp : Real.cos (ψ + Real.pi) = -Real.cos ψ := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
  have hsp : Real.sin (ψ + Real.pi) = -Real.sin ψ := by
    rw [Real.sin_add, Real.cos_pi, Real.sin_pi]; ring
  rw [key, hcp, hsp]
  module

/-- HOL `AZIM_EQ_PI_POINT_SYM_0`（YXIONXL2.hl:1350）；LA13 孪生
`AZIM_EQ_PI_POINT_SYM_0_p13`（LocalAuto13.lean:1503）。 -/
theorem AZIM_EQ_PI_POINT_SYM_0_fb {v1 w1 : V3}
    (h : ¬Collinear ℝ ({0, v1, w1} : Set V3)) :
    azim 0 v1 w1 (-w1) = Real.pi := by
  have hc : ¬ Collinear3 0 v1 w1 := h
  have hnegw : ¬ Collinear3 0 v1 (-w1) := by
    intro hc'
    refine hc ?_
    have h2' := collinear3_zero_negRFb.mp hc'
    simpa using h2'
  exact azim_eq_of_spec hc hnegw (azimSpecOppPiFb hc)

/-! ## azim-neg 六件之二：SUM_AZIM_SYM_0（HOL :1361；LA13 :1510） -/

/-- AzimSpec 组装：以 `w2` 为参考向、`-w1` 为目标向，角为 `π - θ12`。 -/
private theorem azimSpecSumFb {v w1 w2 : V3} {θ12 : ℝ}
    (hsp : AzimSpec 0 v w1 w2 θ12) (hle : θ12 ≤ Real.pi) :
    AzimSpec 0 v w2 (-w1) (Real.pi - θ12) := by
  have hb1 := hsp.1
  have hb2 := hsp.2.1
  obtain ⟨hh1, hh2, hbody⟩ := hsp.2.2
  refine ⟨by linarith [hb1, hle], by linarith [hb1, hle, Real.pi_pos], hh2, -hh1, ?_⟩
  intro e1 e2 e3 he hax hvn
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hbody e1 e2 e3 he hax hvn
  refine ⟨ψ + θ12, r2, r1, hrep2, ?_, hr2, hr1⟩
  have hang : ψ + θ12 + (Real.pi - θ12) = ψ + Real.pi := by ring
  have hsub : (-w1 - 0 : V3) = -(w1 - 0) := by simp
  have key : (-w1 - 0 : V3)
      = -((r1 * Real.cos ψ) • e1 + (r1 * Real.sin ψ) • e2 + hh1 • (v - 0)) := by
    rw [hsub, hrep1]
  have hcp : Real.cos (ψ + Real.pi) = -Real.cos ψ := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
  have hsp : Real.sin (ψ + Real.pi) = -Real.sin ψ := by
    rw [Real.sin_add, Real.cos_pi, Real.sin_pi]; ring
  rw [hang, key, hcp, hsp]
  module

/-- HOL `SUM_AZIM_SYM_0`（YXIONXL2.hl:1361，:1371 verbatim 重复）；LA13 孪生
`SUM_AZIM_SYM_0_p13`（LocalAuto13.lean:1510）。HOL 的 `Fan.sum4_azim_fan` 以
显式 AzimSpec 组装替代。 -/
theorem SUM_AZIM_SYM_0_fb {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3))
    (h3 : azim 0 v1 w1 w2 ≤ Real.pi) :
    azim 0 v1 w1 w2 + azim 0 v1 w2 (-w1) = Real.pi := by
  have hc1 : ¬ Collinear3 0 v1 w1 := h1
  have hc2 : ¬ Collinear3 0 v1 w2 := h2
  obtain ⟨θ12, hspec⟩ := azimSpec_exists hc1 hc2
  have hθ : azim 0 v1 w1 w2 = θ12 := azim_eq_of_spec hc1 hc2 hspec
  rw [hθ]
  have hnegw : ¬ Collinear3 0 v1 (-w1) := by
    intro hc'
    refine hc1 ?_
    have h2' := collinear3_zero_negRFb.mp hc'
    simpa using h2'
  have hval : azim 0 v1 w2 (-w1) = Real.pi - θ12 :=
    azim_eq_of_spec hc2 hnegw (azimSpecSumFb hspec (by rw [← hθ]; exact h3))
  rw [hval]; ring

/-! ## azim-neg 六件之三：AZIM_NEG_FIRST_PI（HOL :1883；LA13 :1518） -/

/-- AzimSpec 组装：轴取反 `-v`，角补为 `2π - θ`（需 `0 < θ` 保证角在 [0, 2π)）。 -/
private theorem azimSpecNegFirstPiFb {v w1 w2 : V3} {θ : ℝ}
    (hsp : AzimSpec 0 v w1 w2 θ) (hpos : 0 < θ) :
    AzimSpec 0 (-v) w1 w2 (2 * Real.pi - θ) := by
  have hb1 := hsp.1
  have hb2 := hsp.2.1
  obtain ⟨hh1, hh2, hbody⟩ := hsp.2.2
  refine ⟨by linarith [hb2, hpos], by linarith [hpos], -hh1, -hh2, ?_⟩
  intro e1 e2 e3 he hax hvn
  -- 镜像给定标架后喂给源 spec（轴条件转回 v；Assembly azimSpecNeg 同款）
  have hdd : dist (-v) 0 = dist v 0 := by
    rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero, norm_neg]
  have h2v : (-v - 0 : V3) = dist v 0 • e3 := hax.trans (congrArg (fun d : ℝ => d • e3) hdd)
  have h3v : (-((-v) - 0 : V3)) = -(dist v 0 • e3) := congrArg Neg.neg h2v
  have h1v : (v - 0 : V3) = -((-v) - 0) := by simp
  have haxv : (v - 0 : V3) = dist v 0 • (-e3) :=
    h1v.trans (h3v.trans (smul_neg (dist v 0) e3).symm)
  have hv0 : v ≠ 0 := fun he => hvn (by simpa using he)
  obtain ⟨ψ, rA, rB, hw1rep, hw2rep, hposA, hposB⟩ :=
    hbody (-e1) e2 (-e3) (on3MirrorFb he) haxv hv0
  refine ⟨Real.pi - ψ, rA, rB, ?_, ?_, hposA, hposB⟩
  · -- w1：镜像标架角 ψ → 直接标架角 π - ψ，高度 -hh1
    have hcp : Real.cos (Real.pi - ψ) = -Real.cos ψ := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    have hsp : Real.sin (Real.pi - ψ) = Real.sin ψ := by
      rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]; ring
    have hvax : (v - 0 : V3) = -((-v) - 0) := by simp
    rw [hvax] at hw1rep
    rw [hw1rep, hcp, hsp]
    module
  · -- w2：镜像标架角 ψ+θ → 直接标架角 π-(ψ+θ)，再由 2π 周期补成 (π-ψ)+(2π-θ)
    have hang : Real.pi - ψ + (2 * Real.pi - θ) = Real.pi - (ψ + θ) + 2 * Real.pi := by ring
    have hper : ∀ x : ℝ, Real.cos (x + 2 * Real.pi) = Real.cos x ∧
        Real.sin (x + 2 * Real.pi) = Real.sin x := fun x =>
      ⟨by rw [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]; ring,
       by rw [Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]; ring⟩
    have hcp2 : Real.cos (Real.pi - (ψ + θ)) = -Real.cos (ψ + θ) := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    have hsp2 : Real.sin (Real.pi - (ψ + θ)) = Real.sin (ψ + θ) := by
      rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]; ring
    have hvax : (v - 0 : V3) = -((-v) - 0) := by simp
    rw [hvax] at hw2rep
    rw [hang, (hper _).1, (hper _).2, hcp2, hsp2, hw2rep]
    module

/-- HOL `AZIM_NEG_FIRST_PI`（YXIONXL2.hl:1883）；LA13 孪生
`AZIM_NEG_FIRST_PI_p13`（LocalAuto13.lean:1518）。 -/
theorem AZIM_NEG_FIRST_PI_fb {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3))
    (h3 : 0 < azim 0 v1 w1 w2) :
    azim 0 (-v1) w1 w2 = 2 * Real.pi - azim 0 v1 w1 w2 := by
  have hc1 : ¬ Collinear3 0 v1 w1 := h1
  have hc2 : ¬ Collinear3 0 v1 w2 := h2
  obtain ⟨θ0, hspec⟩ := azimSpec_exists hc1 hc2
  have hθ : azim 0 v1 w1 w2 = θ0 := azim_eq_of_spec hc1 hc2 hspec
  have hpos : 0 < θ0 := by rw [← hθ]; exact h3
  rw [hθ]
  exact azim_eq_of_spec (fun hc => hc1 (collinear3_zero_negLFb.mp hc))
    (fun hc => hc2 (collinear3_zero_negLFb.mp hc)) (azimSpecNegFirstPiFb hspec hpos)

/-! ## azim-neg 六件之四：AZIM_COMPL_NEG（HOL :1932；LA13 :1526） -/

/-- HOL `AZIM_COMPL_NEG`（YXIONXL2.hl:1932）；LA13 孪生
`AZIM_COMPL_NEG_p13`（LocalAuto13.lean:1526）。证体 = HOL 同款二分：
θ = 0 时两侧归零（`azim_compl_eq_zero` + affGt 换轴传输），θ > 0 时
`AZIM_NEG_FIRST_PI` + `azim_compl`。 -/
theorem AZIM_COMPL_NEG_fb {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 (-v1) w1 w2 = azim 0 v1 w2 w1 := by
  have hc1 : ¬ Collinear3 0 v1 w1 := h1
  have hc2 : ¬ Collinear3 0 v1 w2 := h2
  have hn1 : ¬ Collinear3 0 (-v1) w1 := fun hc => hc1 (collinear3_zero_negLFb.mp hc)
  have hn2 : ¬ Collinear3 0 (-v1) w2 := fun hc => hc2 (collinear3_zero_negLFb.mp hc)
  rcases Classical.em (azim 0 v1 w1 w2 = 0) with h0 | h0
  · have hrhs : azim 0 v1 w2 w1 = 0 := azim_compl_eq_zero hc1 hc2 h0
    have hlhs : azim 0 (-v1) w1 w2 = 0 := by
      rw [azim_eq_zero_iff hn1 hn2]
      -- w1 ∈ affGt {0,-v1} {w2}，由 h0 的 affGt {0,v1} {w2} 换轴传输
      have hmem0 := (azim_eq_zero_iff hc1 hc2).mp h0
      obtain ⟨hv10, hw20, hne12⟩ := collinear3_zero_neFb hc2
      have hv01 : (0 : V3) ≠ v1 := Ne.symm hv10
      have hneg1 : (0 : V3) ≠ -v1 := by
        intro he
        exact hv10 (by simpa using he.symm)
      have hneg12 : w2 ≠ -v1 := by
        intro he
        refine hc2 ?_
        show Collinear ℝ ({0, v1, w2} : Set V3)
        rw [he]
        refine (collinear3_iff_smul hv10).mpr ⟨-1, ?_⟩
        simp
      obtain ⟨c, hcpos, h, hrep⟩ :=
        (affGt_pair_iff (v0 := 0) (v1 := v1) (x := w2) (y := w1)
          hv01 hw20 (Ne.symm hne12)).mp hmem0
      have hvax : (v1 - 0 : V3) = -((-v1) - 0) := by simp
      refine (affGt_pair_iff (v0 := 0) (v1 := -v1) (x := w2) (y := w1)
        hneg1 hw20 hneg12).mpr ⟨c, hcpos, -h, ?_⟩
      rw [hrep, hvax]
      module
    rw [hlhs, hrhs]
  · have hpos : 0 < azim 0 v1 w1 w2 :=
      lt_of_le_of_ne (azim_nonneg 0 v1 w1 w2) (fun he => h0 he.symm)
    rw [azim_compl hc1 hc2, if_neg h0, ← AZIM_NEG_FIRST_PI_fb h1 h2 hpos]

/-! ## azim-neg 六件之五：REMOVE_NEG_AZIM1_SYM_0（HOL :1961；LA13 :1533） -/

/-- AzimSpec 组装：参考/目标同时取反，角不变。 -/
private theorem azimSpecNegNegFb {v w1 w2 : V3} {θ : ℝ} (hsp : AzimSpec 0 v w1 w2 θ) :
    AzimSpec 0 v (-w1) (-w2) θ := by
  have hb1 := hsp.1
  have hb2 := hsp.2.1
  obtain ⟨hh1, hh2, hbody⟩ := hsp.2.2
  refine ⟨hb1, hb2, -hh1, -hh2, ?_⟩
  intro e1 e2 e3 he hax hvn
  obtain ⟨ψ, rA, rB, hw1rep, hw2rep, hposA, hposB⟩ := hbody e1 e2 e3 he hax hvn
  refine ⟨Real.pi + ψ, rA, rB, ?_, ?_, hposA, hposB⟩
  · have hcp : Real.cos (Real.pi + ψ) = -Real.cos ψ := by
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
    have hsp : Real.sin (Real.pi + ψ) = -Real.sin ψ := by
      rw [Real.sin_add, Real.cos_pi, Real.sin_pi]; ring
    have hsub : (-w1 - 0 : V3) = -(w1 - 0) := by simp
    rw [hsub, hw1rep, hcp, hsp]
    module
  · have hang : Real.pi + ψ + θ = Real.pi + (ψ + θ) := by ring
    have hcp : Real.cos (Real.pi + (ψ + θ)) = -Real.cos (ψ + θ) := by
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
    have hsp : Real.sin (Real.pi + (ψ + θ)) = -Real.sin (ψ + θ) := by
      rw [Real.sin_add, Real.cos_pi, Real.sin_pi]; ring
    have hsub : (-w2 - 0 : V3) = -(w2 - 0) := by simp
    rw [hang, hsub, hw2rep, hcp, hsp]
    module

/-- HOL `REMOVE_NEG_AZIM1_SYM_0`（YXIONXL2.hl:1961）；LA13 孪生
`REMOVE_NEG_AZIM1_SYM_0_p13`（LocalAuto13.lean:1533）。 -/
theorem REMOVE_NEG_AZIM1_SYM_0_fb {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 v1 (-w1) (-w2) = azim 0 v1 w1 w2 := by
  have hc1 : ¬ Collinear3 0 v1 w1 := h1
  have hc2 : ¬ Collinear3 0 v1 w2 := h2
  have hnegw1 : ¬ Collinear3 0 v1 (-w1) := by
    intro hc'
    refine hc1 ?_
    have h2' := collinear3_zero_negRFb.mp hc'
    simpa using h2'
  have hnegw2 : ¬ Collinear3 0 v1 (-w2) := by
    intro hc'
    refine hc2 ?_
    have h2' := collinear3_zero_negRFb.mp hc'
    simpa using h2'
  obtain ⟨θ0, hspec⟩ := azimSpec_exists hc1 hc2
  rw [azim_eq_of_spec hnegw1 hnegw2 (azimSpecNegNegFb hspec),
    azim_eq_of_spec hc1 hc2 hspec]

/-! ## azim-neg 六件之六：AZIM_NEG（HOL :2014；LA13 :1540） -/

/-- Assembly `azimSpecNeg`（Assembly.lean:2578，private 不可 import）同证移植：
`AzimSpec 0 v w2 w1 θ → AzimSpec 0 (-v) (-w1) (-w2) θ`。 -/
private theorem azimSpecNegFb {v w1 w2 : V3} {θ : ℝ}
    (h1 : ¬ Collinear3 0 v w1) (h2 : ¬ Collinear3 0 v w2)
    (hsp : AzimSpec 0 v w2 w1 θ) : AzimSpec 0 (-v) (-w1) (-w2) θ := by
  have hb1 := hsp.1
  have hb2 := hsp.2.1
  obtain ⟨hh1, hh2, hbody⟩ := hsp.2.2
  refine ⟨hb1, hb2, hh2, hh1, fun e1 e2 e3 he hax hvn => ?_⟩
  have hdd : dist (-v) 0 = dist v 0 := by
    rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero, norm_neg]
  have h2v : (-v - 0 : V3) = dist v 0 • e3 := hax.trans (congrArg (fun d : ℝ => d • e3) hdd)
  have h3v : (-((-v) - 0 : V3)) = -(dist v 0 • e3) := congrArg Neg.neg h2v
  have h1v : (v - 0 : V3) = -((-v) - 0) := by simp
  have haxv : (v - 0 : V3) = dist v 0 • (-e3) :=
    h1v.trans (h3v.trans (smul_neg (dist v 0) e3).symm)
  have hv0 : v ≠ 0 := fun he => hvn (by simpa using he)
  obtain ⟨ψ, rA, rB, hw2rep, hw1rep, hposA', hposB'⟩ :=
    hbody (-e1) e2 (-e3) (on3MirrorFb he) haxv hv0
  have key1 : (-w1 - 0 : V3) = (rB * Real.cos (-(ψ + θ))) • e1
      + (rB * Real.sin (-(ψ + θ))) • e2 + hh2 • ((-v) - 0) :=
    mirrorRepFb e1 e2 w1 v rB (ψ + θ) hh2 hw1rep
  have key2 : (-w2 - 0 : V3) = (rA * Real.cos (-(ψ + θ) + θ)) • e1
      + (rA * Real.sin (-(ψ + θ) + θ)) • e2 + hh1 • ((-v) - 0) := by
    have hring : (-(ψ + θ) + θ : ℝ) = -ψ := by ring
    have eqA : (rA * Real.cos (-(ψ + θ) + θ) : ℝ) = rA * Real.cos (-ψ) :=
      congrArg (fun x : ℝ => rA * Real.cos x) hring
    have eqB : (rA * Real.sin (-(ψ + θ) + θ) : ℝ) = rA * Real.sin (-ψ) :=
      congrArg (fun x : ℝ => rA * Real.sin x) hring
    have hb : (-w2 - 0 : V3) = (rA * Real.cos (-ψ)) • e1
        + (rA * Real.sin (-ψ)) • e2 + hh1 • ((-v) - 0) :=
      mirrorRepFb e1 e2 w2 v rA ψ hh1 hw2rep
    rw [eqA, eqB]
    exact hb
  exact ⟨-(ψ + θ), rB, rA, key1, key2, hposB', hposA'⟩

/-- HOL `AZIM_NEG`（YXIONXL2.hl:2014）；LA13 孪生 `AZIM_NEG_p13`
（LocalAuto13.lean:1540）。Assembly.lean:2619 `azimMirror` 同形件为 private，
本件按其证明移植（病理对策保留：Collinear3 侧条件 intro+simpa 传输、θ 槽先
`obtain` 换不透明变元）。 -/
theorem AZIM_NEG_fb {v1 w1 w2 : V3}
    (h1 : ¬Collinear ℝ ({0, v1, w1} : Set V3))
    (h2 : ¬Collinear ℝ ({0, v1, w2} : Set V3)) :
    azim 0 (-v1) (-w1) (-w2) = azim 0 v1 w2 w1 := by
  have hc1 : ¬ Collinear3 0 v1 w1 := h1
  have hc2 : ¬ Collinear3 0 v1 w2 := h2
  have hn1 : ¬ Collinear3 0 (-v1) (-w1) := by
    intro hc
    refine hc1 ?_
    have h2' := collinear3_zero_negFb.mp hc
    simpa using h2'
  have hn2 : ¬ Collinear3 0 (-v1) (-w2) := by
    intro hc
    refine hc2 ?_
    have h2' := collinear3_zero_negFb.mp hc
    simpa using h2'
  obtain ⟨θ₀, hθ₀spec⟩ := azimSpec_exists hc2 hc1
  have hθ₀eq : azim 0 v1 w2 w1 = θ₀ := azim_eq_of_spec hc2 hc1 hθ₀spec
  rw [hθ₀eq]
  exact azim_eq_of_spec hn1 hn2 (azimSpecNegFb hc1 hc2 hθ₀spec)

/-! ## 家族总根：EE_EXPAND_BB_VV（HOL :714-748；LA13 :1555） -/

/-- 模 k 单射：`vv i = vv j → i ≡ j (mod k)`。来源 = isScsV39 的
`2 ≤ s.a i j`（i j < k, i ≠ j）+ BBsV39 的 dist 下界（HOL `VV_INJ` 内容，
CARD_V_EQ_SCS_K1 证明内部引用的同款事实）。 -/
private theorem vvInjModFb {s : ScsV39} {vv : ℕ → V3} {k : ℕ} (hk : s.k = k)
    (hkpos : 0 < k)
    (hge : ∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j)
    (hdist : ∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j)
    (hper : Periodic vv k) {i j : ℕ} (hvv : vv i = vv j) : i % k = j % k := by
  have hmod : ∀ n, vv (n % k) = vv n := fun n => periodicModFb hper n
  have hlt1 : i % k < k := Nat.mod_lt i hkpos
  have hlt2 : j % k < k := Nat.mod_lt j hkpos
  by_contra hne
  have h2a : (2 : ℝ) ≤ s.a (i % k) (j % k) :=
    hge (i % k) (j % k) ⟨by rw [hk]; exact hlt1, by rw [hk]; exact hlt2, hne⟩
  have hd2 : (2 : ℝ) ≤ dist (vv (i % k)) (vv (j % k)) := h2a.trans (hdist _ _).1
  have hne0 : vv (i % k) ≠ vv (j % k) := by
    intro h0
    rw [h0, dist_self] at hd2
    linarith
  rw [hmod i, hmod j] at hne0
  exact hne0 hvv

/-- 循环无自环：`vv j ≠ vv (j + 1)`。 -/
private theorem vvSuccNeFb {s : ScsV39} {vv : ℕ → V3} {k : ℕ} (hk : s.k = k) (hk2 : 2 ≤ k)
    (hge : ∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j)
    (hdist : ∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j)
    (hper : Periodic vv k) (j : ℕ) : vv j ≠ vv (j + 1) := by
  have hkpos : 0 < k := by omega
  have hmod : ∀ n, vv (n % k) = vv n := fun n => periodicModFb hper n
  have hlt1 : j % k < k := Nat.mod_lt j hkpos
  have hlt2 : (j + 1) % k < k := Nat.mod_lt (j + 1) hkpos
  have hne : j % k ≠ (j + 1) % k := modNeSuccFb hk2
  have hd2 : (2 : ℝ) ≤ dist (vv (j % k)) (vv ((j + 1) % k)) :=
    (hge (j % k) ((j + 1) % k)
      ⟨by rw [hk]; exact hlt1, by rw [hk]; exact hlt2, hne⟩).trans (hdist _ _).1
  intro h0
  have hEq : vv (j % k) = vv ((j + 1) % k) := by
    rw [hmod j, hmod (j + 1)]
    exact h0
  rw [hEq, dist_self] at hd2
  linarith

/-- HOL `EE_EXPAND_BB_VV`（YXIONXL2.hl:714-748）；LA13 孪生
`EE_EXPAND_BB_VV_p13`（LocalAuto13.lean:1555，`ScsV39P13` 型）。本件为
LA1 `ScsV39` 型 —— 家族总根，HOL 内被 IVS/SYM_AZIM/FF_ITER/CONVEX/TAUSTAR
五处直接引用。证体走纯组合路线（周期性 + 模 k 单射 + 无自环），不经 HOL 的
local_fan σ-轨道；hV/hFF 与 fan 合取按孪生保留、证体不需。 -/
theorem EE_EXPAND_BB_VV_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (i : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3) := by
  obtain ⟨-, hper0, hdist, -⟩ := hbb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hge, -, -, -, -, -⟩ := hiscs
  have hper : Periodic vv k := by rw [← hk]; exact hper0
  have hmod : ∀ n, vv (n % k) = vv n := fun n => periodicModFb hper n
  have hk4 : 4 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  ext w
  constructor
  · -- ⊆：每个循环邻居都是这两个
    intro hw
    simp only [ee, Set.mem_setOf_eq] at hw
    rw [← hE] at hw
    obtain ⟨j, -, hj⟩ := hw
    have hj' : ({vv j, vv (j + 1)} : Set V3) = {vv i, w} := hj
    have hvi : vv i ∈ ({vv j, vv (j + 1)} : Set V3) := by
      rw [hj']
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    have hwm : w ∈ ({vv j, vv (j + 1)} : Set V3) := by
      rw [hj']
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
    rcases Set.mem_insert_iff.mp hvi with hvij | hvij
    · -- vv i = vv j
      rcases Set.mem_insert_iff.mp hwm with hwj | hwj
      · -- w = vv j：退化为自环边，矛盾
        exfalso
        have hset : ({vv i, w} : Set V3) = ({vv j} : Set V3) := by
          rw [hvij, hwj]
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        have h2 : vv (j + 1) ∈ ({vv j, vv (j + 1)} : Set V3) :=
          Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
        rw [hj', hset, Set.mem_singleton_iff] at h2
        exact vvSuccNeFb hk hk2 hge hdist hper j h2.symm
      · -- w = vv (j+1)：模 k 单射给出 w = vv (i+1)
        have hjmod : j % k = i % k := vvInjModFb hk hkpos hge hdist hper hvij.symm
        have hweq : vv (j + 1) = vv (i + 1) := by
          rw [← hmod (j + 1), ← hmod (i + 1), modSuccFb hjmod]
        rw [hwj, hweq]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · -- vv i = vv (j+1)
      rw [Set.mem_singleton_iff] at hvij
      rcases Set.mem_insert_iff.mp hwm with hwj | hwj
      · -- w = vv j：模 k 单射给出 w = vv (i+k-1)
        have hjmod : (j + 1) % k = i % k := vvInjModFb hk hkpos hge hdist hper hvij.symm
        have hjeq : j % k = (i + (k - 1)) % k := modPredFb (by omega) hjmod
        have hsk : i + (k - 1) = i + k - 1 := by omega
        rw [hsk] at hjeq
        have hweq : vv j = vv (i + k - 1) := by
          rw [← hmod j, ← hmod (i + k - 1), hjeq]
        rw [hwj, hweq]
        exact Set.mem_insert_of_mem _ rfl
      · -- w = vv (j+1) = vv i：退化为自环边，矛盾
        exfalso
        have hset : ({vv j, vv (j + 1)} : Set V3) = ({vv (j + 1)} : Set V3) := by
          rw [hj', hvij, hwj]
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        have h2 : vv j ∈ ({vv j, vv (j + 1)} : Set V3) :=
          Set.mem_insert_iff.mpr (Or.inl rfl)
        rw [hset, Set.mem_singleton_iff] at h2
        exact vvSuccNeFb hk hk2 hge hdist hper j h2
  · -- ⊇：边 i 与边 i+k-1 都是 E 的成员
    intro hw
    rcases Set.mem_insert_iff.mp hw with hw | hw
    · rw [hw]
      show ({vv i, vv (i + 1)} : Set V3) ∈ E
      rw [← hE]
      exact ⟨i, Set.mem_univ i, rfl⟩
    · rw [hw]
      show ({vv i, vv (i + k - 1)} : Set V3) ∈ E
      have hstep : (i + k - 1) + 1 = i + k := by omega
      have hmem : ({vv (i + k - 1), vv ((i + k - 1) + 1)} : Set V3) ∈ E := by
        rw [← hE]
        exact ⟨i + k - 1, Set.mem_univ _, rfl⟩
      rw [hstep] at hmem
      rw [← hper i, pairSetCommFb]
      exact hmem

end Kepler.Text
