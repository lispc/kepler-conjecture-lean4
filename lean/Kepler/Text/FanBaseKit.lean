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

F1 增补（fanbase-f1-w1，FAN-free 机械五件，同世界 ScsV39 + LA3 `_p3` def）：
- `IVS_AZIM_CYCLE_SYM_0`   HOL :749；P13 孪生 LA13-f0b-draft :2169（LHS 缺负像集，按 HOL 落槽）
- `SYM_AZIM_CYCLE_SYM_0`   HOL :1104；P13 孪生 :2237（3 参 azim 不合型，按 HOL 落槽 azimCycle 形）
- `ff_FUN_COMMUTATIVE_SYM_0` HOL :787；P13 孪生 :2181
- `ff_POWER_COMMUTATIVE_SYM_0` HOL :823；P13 孪生 :2195
- `FF_OF_HYP_ITER_VV`      HOL :1417；P13 孪生 :2320
根输入 = `EE_EXPAND_BB_VV`（证体内核化为 `eeExpandCoreFb`，负向系统同喂）；
二元 azimCycle/ivsAzimCycle 显式值 = 私有微件（epsilon 唯一性，零 azim 计算）。

F2 增补（fanbase-f2-w1，hypermap 对称/记账七件，同世界 ScsV39 + LA3 `_p3` def）：
- `FACE_SYM_0`             HOL :846-880；P13 孪生 LA13-f0b-draft :2220
- `FACE_ALL_SYM_0`         HOL :1056-1090；P13 孪生 :2234
- `NODE_MAP_SYM_0`         HOL :1143-1184；P13 孪生 :2260
- `IMAGE_NODE_SYM_0`       HOL :1188-1229；P13 孪生 :2275
- `EDGE_MAP_SYM_0`         HOL :1242-1281；P13 孪生 :2289
- `EDGE_POWER_MAP_SYM_0`   HOL :1285-1300；P13 孪生 :2303
- `NODE_POWER_MAP_SYM_0`   HOL :1303-1318；P13 孪生 :2317
根输入 = F1 五件（dart 负像桥自 `ff_FUN_COMMUTATIVE_SYM_0_fb` 证体提为
`dartNegMemFb`/`dartNegNotFb`）；face = canonical def `hypFaceFb`（ff-轨道集，
`hypFaceP13` 的 ScsV39 世界孪生；LA3 无 face def）。FAN-free：HOL 七件的
`FAN_SYM_0` 输入只经 ELMS_OF_HYPERMAP_HYP / DART_OF_HYP_VV（hypermap 型编码的
face/dart 刻画）进入，本编码 face/dart 资格皆 defining，刻画步消失；F0-b 依赖
裁定 = 跳过（不 import LocalAuto13），详见快照 PLAN.md。

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
import Kepler.Text.LocalAuto3
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

/-- F0-a `EE_EXPAND_BB_VV_fb` 的内核化证体（fanbase-f1-w1 抽取）：只吃
周期性 + isScsV39 的 `a`-下界 + BBsV39 的 dist 界，不含 fan 合取——使 F1 的
负向系统（`vv := fun i => -(vv i)`）可以绕开 `BBsV39` 第 4 合取支的
`ConvexLocalFan`（LA1:411）直接复用同一展开。 -/
private theorem eeExpandCoreFb {s : ScsV39} {vv : ℕ → V3} {k : ℕ} {E : Set (Set V3)}
    (hk : s.k = k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hper : Periodic vv k)
    (hge : ∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j)
    (hdist : ∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j)
    (hk3 : ¬(k ≤ 3)) (i : ℕ) :
    ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3) := by
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

/-! ## F1（fanbase-f1-w1）：FAN-free 机械五件 + 二元 azimCycle 微件

HOL 锚（YXIONXL2.hl）：`IVS_AZIM_CYCLE_SYM_0` :749、`ff_FUN_COMMUTATIVE_SYM_0`
:787、`ff_POWER_COMMUTATIVE_SYM_0` :823、`SYM_AZIM_CYCLE_SYM_0` :1104、
`FF_OF_HYP_ITER_VV` :1417。P13 孪生 = /tmp/LA13_f0b_aff_azn.lean
:2169/:2237/:2320/:2181/:2195。路线：EE_EXPAND 二元邻域 + azimCycle/ivs
二元显式值（epsilon 唯一性，fprime `azimCycle2_p35` 同内容）+ dart 资格
取负桥。 -/

/-- fprime-bridge `epsFixed_p35`（LA35_stack12.lean:976，private）孪生：
epsilon 的唯一见证固定。 -/
private theorem epsFixedFb {α : Sort*} [Nonempty α] {pr : α → Prop} {a : α}
    (hpa : pr a) (huniq : ∀ y, pr y → y = a) : Classical.epsilon pr = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

/-- dist 在两端同时取负下不变。 -/
private theorem distNegNegFb (a b : V3) : dist (-a) (-b) = dist a b := by
  have h : ((-a) - (-b) : V3) = -(a - b) := by abel
  rw [dist_eq_norm, h, norm_neg, ← dist_eq_norm]

/-- `c ∈ (0, k)` 时 `a` 与 `a + c` 模 `k` 不同余。 -/
private theorem modNeAddltFb {k a c : ℕ} (hk0 : 0 < k) (hck : c < k) (hc0 : 0 < c) :
    a % k ≠ (a + c) % k := by
  intro h
  have hd : k ∣ a + c - a := Nat.modEq_iff_dvd' (by omega) |>.mp h
  rw [Nat.add_sub_cancel_left] at hd
  have hd2 : c % k = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [Nat.mod_eq_of_lt hck] at hd2
  omega

/-- 二元 azimCycle（fprime-bridge `azimCycle2_p35`（LA35_stack12.lean:2314，
private）同内容）：邻域集 `{p, q}`（`p ≠ q`）上从 `p` 出发的 cycle 后继 =
「另」元素 `q`；纯 epsilon 唯一性，零 azim 计算。 -/
private theorem azimCycleTwoFb {p q v : V3} (hne : p ≠ q) :
    azimCycle_p3 ({p, q} : Set V3) 0 v p = q := by
  have hsub : ¬(({p, q} : Set V3) ⊆ ({p} : Set V3)) := by
    intro hc
    exact hne (Set.mem_singleton_iff.mp
      (hc (Set.mem_insert_iff.mpr (Or.inr rfl)))).symm
  unfold azimCycle_p3
  rw [if_neg hsub]
  refine epsFixedFb ⟨Ne.symm hne, Set.mem_insert_iff.mpr (Or.inr rfl), ?_⟩ ?_
  · intro r hr hrp
    rcases Set.mem_insert_iff.mp hr with hrr | hrr
    · exact absurd hrr hrp
    · rw [hrr]
      exact Or.inr ⟨rfl, le_refl _⟩
  · intro y hy
    rcases Set.mem_insert_iff.mp hy.2.1 with hy2 | hy2
    · exact absurd hy2 hy.1
    · exact hy2

private theorem azimCycleTwoSwapFb {p q v : V3} (hne : p ≠ q) :
    azimCycle_p3 ({p, q} : Set V3) 0 v q = p := by
  rw [pairSetCommFb]
  exact azimCycleTwoFb hne.symm

/-- 二元 ivs_azim_cycle：`{p, q}`（`p ≠ q`）上从 `q` 出发的一步 = `p`。 -/
private theorem ivsTwoNeFb {p q v : V3} (hne : p ≠ q) :
    ivsAzimCycle_p3 ({p, q} : Set V3) 0 v q = p := by
  have hne0 : ¬(({p, q} : Set V3) = ∅) := by
    intro hc
    have hp : p ∈ ({p, q} : Set V3) := Set.mem_insert_iff.mpr (Or.inl rfl)
    rw [hc] at hp
    simp at hp
  unfold ivsAzimCycle_p3
  rw [if_neg hne0]
  refine epsFixedFb ⟨Set.mem_insert_iff.mpr (Or.inl rfl), azimCycleTwoFb hne⟩ ?_
  intro y hy
  rcases Set.mem_insert_iff.mp hy.1 with hy1 | hy1
  · exact hy1
  · have hy1' : y = q := Set.mem_singleton_iff.mp hy1
    rw [hy1'] at hy
    rw [azimCycleTwoSwapFb hne] at hy
    exact absurd hy.2 hne

private theorem ivsTwoSwapFb {p q v : V3} (hne : p ≠ q) :
    ivsAzimCycle_p3 ({p, q} : Set V3) 0 v p = q := by
  rw [pairSetCommFb]
  exact ivsTwoNeFb hne.symm

/-- HOL `EE_EXPAND_BB_VV`（YXIONXL2.hl:714-748）；LA13 孪生
`EE_EXPAND_BB_VV_p13`（LocalAuto13.lean:1555，`ScsV39P13` 型）。f0a 七件之一，
签名逐字不动；本车道把其证体抽取为 `eeExpandCoreFb` 供负向系统复用。 -/
theorem EE_EXPAND_BB_VV_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (i : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3) := by
  obtain ⟨-, hper0, hdist, -⟩ := hbb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hge, -, -, -, -, -⟩ := hiscs
  exact eeExpandCoreFb hk hE (by rw [← hk]; exact hper0) hge hdist hk3 i

/-- 正向：循环序对是 dart（ordPairs 成员，与 V 无关）。 -/
private theorem ordMemDartsFb {vv : ℕ → V3} {V : Set V3} {E : Set (Set V3)} {u w : V3}
    (h : ({u, w} : Set V3) ∈ E) : (u, w) ∈ dartsOfHyp_p3 E V := by
  simp only [dartsOfHyp_p3, ordPairs_p3, selfPairs_p3, Set.mem_union, Set.mem_setOf_eq]
  exact Or.inl h

/-- `z ∈ V` 的 vv-原像（正向族）。 -/
private theorem vvmemFb {vv : ℕ → V3} {V : Set V3} (hV : Set.image vv Set.univ = V) {z : V3}
    (hz : z ∈ V) : ∃ m, z = vv m := by
  rw [← hV] at hz
  obtain ⟨m, -, hm⟩ := hz
  exact ⟨m, hm.symm⟩

/-- 第 `m` 条边属于 `E`（正向族）。 -/
private theorem edgeMemFb {vv : ℕ → V3} {E : Set (Set V3)}
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E) (m : ℕ) :
    ({vv m, vv (m + 1)} : Set V3) ∈ E := by
  rw [← hE]
  exact ⟨m, Set.mem_univ _, rfl⟩

/-- `z ∈ V'` 的负向 vv-原像（负向族）。 -/
private theorem negVmemFb (vv : ℕ → V3) {z : V3}
    (hz : z ∈ Set.image (fun i : ℕ => -(vv i)) Set.univ) : ∃ m, z = -(vv m) := by
  rw [Set.mem_image] at hz
  obtain ⟨m, -, hm⟩ := hz
  exact ⟨m, hm.symm⟩

/-- 第 `m` 条负向边属于 `NEGE`。 -/
private theorem negEdgeMemFb (vv : ℕ → V3) (m : ℕ) :
    ({-(vv m), -(vv (m + 1))} : Set V3) ∈
      Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ :=
  ⟨m, Set.mem_univ _, rfl⟩

/-- dart 拆解（世界无关形）：无自环 dart 的无序对必在 `E` 中（selfPairs 一侧
因邻域非空被排除）。 -/
private theorem dartInvFb {vv : ℕ → V3} {V : Set V3} {E : Set (Set V3)}
    (hVmem : ∀ z : V3, z ∈ V → ∃ m, z = vv m)
    (hEw : ∀ m, ({vv m, vv (m + 1)} : Set V3) ∈ E)
    (hne : ∀ j, vv j ≠ vv (j + 1)) {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) :
    ({x.1, x.2} : Set V3) ∈ E := by
  simp only [dartsOfHyp_p3, ordPairs_p3, selfPairs_p3, Set.mem_union, Set.mem_setOf_eq] at hx
  rcases hx with h | hs
  · exact h
  · exfalso
    obtain ⟨-, hVin, hEEempty⟩ := hs
    obtain ⟨m, hm⟩ := hVmem x.1 hVin
    rw [hm] at hEEempty
    have hineE : vv (m + 1) ∈ EE_p3 (vv m) E := by
      show ({vv m, vv (m + 1)} : Set V3) ∈ E
      exact hEw m
    rw [hEEempty] at hineE
    exact absurd hineE (by simp)

/-- 无序对朝向：`{x.1, x.2} = {p, q}`（`p ≠ q`）给出两个朝向之一。 -/
private theorem dartOrientFb {p q : V3} {x : V3 × V3} (hne : p ≠ q)
    (hjeq : ({x.1, x.2} : Set V3) = ({p, q} : Set V3)) :
    (x.1 = p ∧ x.2 = q) ∨ (x.1 = q ∧ x.2 = p) := by
  have h1 : x.1 = p ∨ x.1 = q := by
    have hx1 : x.1 ∈ ({x.1, x.2} : Set V3) := Set.mem_insert_iff.mpr (Or.inl rfl)
    rw [hjeq] at hx1
    simpa using hx1
  have h2 : x.2 = p ∨ x.2 = q := by
    have hx2 : x.2 ∈ ({x.1, x.2} : Set V3) := Set.mem_insert_iff.mpr (Or.inr rfl)
    rw [hjeq] at hx2
    simpa using hx2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso
    have hq : q ∈ ({x.1, x.2} : Set V3) := by rw [hjeq]; simp
    rw [h1, h2] at hq
    simp at hq
    exact hne hq.symm
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exfalso
    have hp : p ∈ ({x.1, x.2} : Set V3) := by rw [hjeq]; simp
    rw [h1, h2] at hp
    simp at hp
    exact hne hp

/-- 边集取负桥：`{u, w} ∈ E ↔ {-u, -w} ∈ NEGE`（双向都走 image 成员展开 +
`neg_neg`）。 -/
private theorem memNegEFb {vv : ℕ → V3} {E : Set (Set V3)}
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    {u w : V3} :
    ({u, w} : Set V3) ∈ E ↔
      ({-u, -w} : Set V3) ∈
        Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ := by
  constructor
  · intro h
    rw [← hE] at h
    obtain ⟨j, -, hj⟩ := h
    refine ⟨j, Set.mem_univ _, ?_⟩
    have himg : Set.image (fun z : V3 => -z) ({u, w} : Set V3) = ({-u, -w} : Set V3) := by
      simp
    rw [← himg, ← hj]
    simp
  · intro h
    rw [← hE]
    obtain ⟨j, -, hj⟩ := h
    refine ⟨j, Set.mem_univ _, ?_⟩
    have hj' : ({-vv j, -vv (j + 1)} : Set V3) = {-u, -w} := hj
    have h2 : Set.image (fun z : V3 => -z) ({-vv j, -vv (j + 1)} : Set V3)
        = Set.image (fun z : V3 => -z) ({-u, -w} : Set V3) := by
      rw [hj']
    simp at h2
    exact h2

/-- HOL `FUN_COMMUTATIVE`（YXIONXL2.hl:833-843）孪生：逐点交换的 n 步迭代。 -/
private theorem iterCommFb {α : Type*} {f g h : α → α} (hcomm : ∀ x, f (g x) = g (h x)) :
    ∀ n x, f^[n] (g x) = g (h^[n] x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, hcomm, ih (h x), Function.iterate_succ_apply]

/-- `ff_of_hyp` 在 dart 上的显式值。 -/
private theorem ffMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∈ dartsOfHyp_p3 E V) :
    ffOfHyp_p3 x V E d = (d.2, ivsAzimCycle_p3 (EE_p3 d.2 E) x d.2 d.1) := by
  unfold ffOfHyp_p3
  rw [if_pos hmem]

/-- `ff_of_hyp` 在非 dart 上恒等。 -/
private theorem ffNotMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∉ dartsOfHyp_p3 E V) : ffOfHyp_p3 x V E d = d := by
  unfold ffOfHyp_p3
  rw [if_neg hmem]

/-- F1 块共享语境：从 scs 七槽假设块读出 hge/hdist/周期性/邻域展开（正向 +
负向；负向走 `eeExpandCoreFb`，绕开 fan 合取）+ 三条模 k 不等。 -/
private theorem fanbaseCtxFb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    (∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j) ∧
      (∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j) ∧
      Periodic vv k ∧
      (∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3)) ∧
      (∀ i, ee (-(vv i))
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          = ({-(vv (i + 1)), -(vv (i + k - 1))} : Set V3)) ∧
      (∀ j, vv j ≠ vv (j + 1)) ∧
      (∀ j, vv (j + 1) ≠ vv (j + k - 1)) ∧
      (∀ j, vv (j + 2) ≠ vv (j + k)) := by
  obtain ⟨-, hper0, hdist, -⟩ := hbb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hge, -, -, -, -, -⟩ := hiscs
  have hper : Periodic vv k := by rw [← hk]; exact hper0
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hperN : Periodic (fun i : ℕ => -(vv i)) k := fun t => by simpa using hper t
  have hdistN : ∀ i j, s.a i j ≤ dist (-(vv i)) (-(vv j)) ∧ dist (-(vv i)) (-(vv j)) ≤ s.b i j := by
    intro i j
    constructor
    · rw [distNegNegFb]; exact (hdist i j).1
    · rw [distNegNegFb]; exact (hdist i j).2
  refine ⟨hge, hdist, hper, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => eeExpandCoreFb hk hE hper hge hdist hk3 i
  · exact fun i => eeExpandCoreFb hk rfl hperN hge hdistN hk3 i
  · exact fun j => vvSuccNeFb hk hk2 hge hdist hper j
  · intro j hcon
    have hm : (j + 1) % k = (j + k - 1) % k := vvInjModFb hk hkpos hge hdist hper hcon
    rw [show (j + k - 1 : ℕ) = (j + 1) + (k - 2) from by omega] at hm
    exact modNeAddltFb hkpos (by omega) (by omega) hm
  · intro j hcon
    have hm : (j + 2) % k = (j + k) % k := vvInjModFb hk hkpos hge hdist hper hcon
    rw [show (j + k : ℕ) = (j + 2) + (k - 2) from by omega] at hm
    exact modNeAddltFb hkpos (by omega) (by omega) hm

/-- backward dart 上 ff 的一步：`(vv (m+1), vv m) ↦ (vv m, vv (m + (k-1)))`。 -/
private theorem ffStepFb {s : ScsV39} {vv : ℕ → V3} {k : ℕ} {V : Set V3} {E : Set (Set V3)}
    (hk : s.k = k) (hk4 : 4 ≤ k)
    (hge : ∀ i j, i < s.k ∧ j < s.k ∧ i ≠ j → 2 ≤ s.a i j)
    (hdist : ∀ i j, s.a i j ≤ dist (vv i) (vv j) ∧ dist (vv i) (vv j) ≤ s.b i j)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hper : Periodic vv k) (m : ℕ) :
    ffOfHyp_p3 0 V E (vv (m + 1), vv m) = (vv m, vv (m + (k - 1))) := by
  have hkpos : 0 < k := by omega
  have hneSuccPred : vv (m + 1) ≠ vv (m + k - 1) := by
    intro hcon
    have hm : (m + 1) % k = (m + k - 1) % k := vvInjModFb hk hkpos hge hdist hper hcon
    rw [show (m + k - 1 : ℕ) = (m + 1) + (k - 2) from by omega] at hm
    exact modNeAddltFb hkpos (by omega) (by omega) hm
  have hmem : ((vv (m + 1), vv m) : V3 × V3) ∈ dartsOfHyp_p3 E V :=
    ordMemDartsFb (vv := vv) (by rw [← hE]; exact ⟨m, Set.mem_univ _, by rw [pairSetCommFb]⟩)
  rw [ffMemEqFb hmem, show EE_p3 ((vv (m + 1), vv m)).2 E = ee (vv m) E from rfl, hEE m,
    ivsTwoSwapFb (p := vv (m + 1)) (q := vv (m + k - 1)) hneSuccPred,
    show (m + k - 1 : ℕ) = m + (k - 1) from by omega]

/-- HOL `IVS_AZIM_CYCLE_SYM_0`（YXIONXL2.hl:749-786）；LA13 孪生
`IVS_AZIM_CYCLE_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2169；其 LHS 首参误写
`eeP13 (-(x.2)) E` 丢了负像边集——本件按 HOL 正本落槽为
`EE (--SND x) (IMAGE …{--vv i,--vv (SUC i)}…)`）。 -/
theorem IVS_AZIM_CYCLE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv)
    (hx : x ∈ dartsOfHyp_p3 E V) :
    ivsAzimCycle_p3
        (ee (-(x.2))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
        0 (-(x.2)) (-(x.1))
      = -(ivsAzimCycle_p3 (ee (x.2) E) 0 (x.2) (x.1)) := by
  obtain ⟨hge, hdist, hper, hEE, hEEN, hne, hneE, hneD⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hkpos : 0 < k := by omega
  have hord := dartInvFb (fun z hz => vvmemFb hV hz) (edgeMemFb hE) hne hx
  rw [← hE] at hord
  obtain ⟨j, -, hjeq⟩ := hord
  rcases dartOrientFb (hne j) hjeq.symm with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · rw [hj2, hj1]
    have hsetR : ee (vv (j + 1)) E = ({vv (j + 2), vv (j + k)} : Set V3) := by
      rw [hEE (j + 1)]
      have e1 : (j + 1 + 1 : ℕ) = j + 2 := by omega
      have e2 : (j + 1 + k - 1 : ℕ) = j + k := by omega
      rw [e1, e2]
    have hsetL : ee (-(vv (j + 1)))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        = ({-(vv (j + 2)), -(vv (j + k))} : Set V3) := by
      rw [hEEN (j + 1)]
      have e1 : (j + 1 + 1 : ℕ) = j + 2 := by omega
      have e2 : (j + 1 + k - 1 : ℕ) = j + k := by omega
      rw [e1, e2]
    rw [hsetL, hsetR, ← hper j,
      ivsTwoNeFb (p := -(vv (j + 2))) (q := -(vv (j + k))) (v := -(vv (j + 1)))
        (fun hc => hneD j (by simpa using hc)),
      ivsTwoNeFb (p := vv (j + 2)) (q := vv (j + k)) (v := vv (j + 1)) (hneD j)]
  · rw [hj2, hj1, hEEN j, hEE j,
      ivsTwoSwapFb (p := -(vv (j + 1))) (q := -(vv (j + k - 1))) (v := -(vv j))
        (fun hc => hneE j (by simpa using hc)),
      ivsTwoSwapFb (p := vv (j + 1)) (q := vv (j + k - 1)) (v := vv j) (hneE j)]

/-- HOL `SYM_AZIM_CYCLE_SYM_0`（YXIONXL2.hl:1104-1142）；LA13 孪生
`SYM_AZIM_CYCLE_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2237；其结论槽误把
`azim_cycle` 摊平成 3 参 `azim`（不完全应用，不合型）——本件按 HOL 正本落槽：
`azim_cycle (EE (--FST x) NEGE) 0 (--FST x) (--SND x)
 = -- azim_cycle (EE (FST x) E) 0 (FST x) (SND x)`）。 -/
theorem SYM_AZIM_CYCLE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv)
    (hx : x ∈ dartsOfHyp_p3 E V) :
    azimCycle_p3
        (ee (-(x.1))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
        0 (-(x.1)) (-(x.2))
      = -(azimCycle_p3 (ee (x.1) E) 0 (x.1) (x.2)) := by
  obtain ⟨hge, hdist, hper, hEE, hEEN, hne, hneE, hneD⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hkpos : 0 < k := by omega
  have hord := dartInvFb (fun z hz => vvmemFb hV hz) (edgeMemFb hE) hne hx
  rw [← hE] at hord
  obtain ⟨j, -, hjeq⟩ := hord
  rcases dartOrientFb (hne j) hjeq.symm with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
  · rw [hj1, hj2, hEEN j, hEE j,
      azimCycleTwoFb (p := -(vv (j + 1))) (q := -(vv (j + k - 1))) (v := -(vv j))
        (fun hc => hneE j (by simpa using hc)),
      azimCycleTwoFb (p := vv (j + 1)) (q := vv (j + k - 1)) (v := vv j) (hneE j)]
  · rw [hj1, hj2]
    have hsetR : ee (vv (j + 1)) E = ({vv (j + 2), vv (j + k)} : Set V3) := by
      rw [hEE (j + 1)]
      have e1 : (j + 1 + 1 : ℕ) = j + 2 := by omega
      have e2 : (j + 1 + k - 1 : ℕ) = j + k := by omega
      rw [e1, e2]
    have hsetL : ee (-(vv (j + 1)))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        = ({-(vv (j + 2)), -(vv (j + k))} : Set V3) := by
      rw [hEEN (j + 1)]
      have e1 : (j + 1 + 1 : ℕ) = j + 2 := by omega
      have e2 : (j + 1 + k - 1 : ℕ) = j + k := by omega
      rw [e1, e2]
    rw [hsetL, hsetR, ← hper j,
      azimCycleTwoSwapFb (p := -(vv (j + 2))) (q := -(vv (j + k))) (v := -(vv (j + 1)))
        (fun hc => hneD j (by simpa using hc)),
      azimCycleTwoSwapFb (p := vv (j + 2)) (q := vv (j + k)) (v := vv (j + 1)) (hneD j)]

/-- HOL `ff_FUN_COMMUTATIVE_SYM_0`（YXIONXL2.hl:787-822）；LA13 孪生
`ff_FUN_COMMUTATIVE_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2181）。证体 = HOL
同款：dart 资格取负桥 + `IVS_AZIM_CYCLE_SYM_0_fb` 逐点代入。 -/
theorem ff_FUN_COMMUTATIVE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ x : V3 × V3,
      ffOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (ffOfHyp_p3 0 V E x) := by
  obtain ⟨hge, hdist, hper, hEE, -, hne, -, -⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hneN : ∀ j, -(vv j) ≠ -(vv (j + 1)) := fun j hc => hne j (by simpa using hc)
  intro x
  by_cases hx : x ∈ dartsOfHyp_p3 E V
  · have hneg : ((-x.1, -x.2) : V3 × V3) ∈
        dartsOfHyp_p3
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          (Set.image (fun i : ℕ => -(vv i)) Set.univ) := by
      have hord := dartInvFb (fun z hz => vvmemFb hV hz) (edgeMemFb hE) hne hx
      exact ordMemDartsFb (vv := fun i : ℕ => -(vv i)) ((memNegEFb hE).mp hord)
    rw [ffMemEqFb hneg, ffMemEqFb hx]
    show (-(x.2),
            ivsAzimCycle_p3
              (EE_p3 (-(x.2))
                (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
              0 (-(x.2)) (-(x.1)))
        = (-(x.2),
            -(ivsAzimCycle_p3 (EE_p3 (x.2) E) 0 (x.2) (x.1)))
    rw [show EE_p3 (-(x.2))
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          = ee (-(x.2))
              (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) from rfl,
      show EE_p3 (x.2) E = ee (x.2) E from rfl,
      IVS_AZIM_CYCLE_SYM_0_fb s vv k V E FF x hk hV hE hFF hiscs hk3 hbb hx]
  · have hnegout : ((-x.1, -x.2) : V3 × V3) ∉
        dartsOfHyp_p3
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          (Set.image (fun i : ℕ => -(vv i)) Set.univ) := by
      intro hmem
      refine hx ?_
      have hord := dartInvFb (fun z hz => negVmemFb vv hz) (negEdgeMemFb vv) hneN hmem
      exact ordMemDartsFb (vv := fun i : ℕ => -(vv i)) ((memNegEFb hE).mpr hord)
    rw [ffNotMemEqFb hnegout, ffNotMemEqFb hx]

/-- HOL `ff_POWER_COMMUTATIVE_SYM_0`（YXIONXL2.hl:823-845）；LA13 孪生
`ff_POWER_COMMUTATIVE_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2195）。证体 =
HOL 同款 `FUN_COMMUTATIVE` 迭代转移（`iterCommFb`）。 -/
theorem ff_POWER_COMMUTATIVE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (ffOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2))
            ((ffOfHyp_p3 0 V E)^[n] x) := by
  intro n x
  exact iterCommFb (ff_FUN_COMMUTATIVE_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb) n x

/-- HOL `FF_OF_HYP_ITER_VV`（YXIONXL2.hl:1417-1452）；LA13 孪生
`FF_OF_HYP_ITER_VV_p13`（/tmp/LA13_f0b_aff_azn.lean:2320）。证体 = `ffStepFb`
（backward dart 一步闭式）+ 归纳 + 周期性，替代 HOL 的
ITER_CARD_MINUS1_EQ_IVS_RN1 σ-轨道四件套。 -/
theorem FF_OF_HYP_ITER_VV_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (i : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ n : ℕ,
      (ffOfHyp_p3 0 V E)^[n] (vv (i + 1), vv i)
        = (vv (n * (k - 1) + i + 1), vv (n * (k - 1) + i)) := by
  obtain ⟨hge, hdist, hper, hEE, -, -, -, -⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hk4 : 4 ≤ k := by omega
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        ffStepFb hk hk4 hge hdist hE hEE hper (n * (k - 1) + i)]
      have h1 : n.succ * (k - 1) + i + 1 = n * (k - 1) + i + k := by
        have hke : k - 1 + 1 = k := by omega
        have hr : n * (k - 1) + (k - 1) + i + 1 = n * (k - 1) + i + ((k - 1) + 1) := by
          ring
        rw [Nat.succ_mul, hr, hke]
      have h2 : n.succ * (k - 1) + i = n * (k - 1) + i + (k - 1) := by
        rw [Nat.succ_mul]; ring
      rw [h1, h2, hper]


/-! ## F2（fanbase-f2-w1）：hypermap 对称/记账七件

HOL 锚（YXIONXL2.hl）：`FACE_SYM_0` :846-880、`FACE_ALL_SYM_0` :1056-1090、
`NODE_MAP_SYM_0` :1143-1184、`IMAGE_NODE_SYM_0` :1188-1229、`EDGE_MAP_SYM_0`
:1242-1281、`EDGE_POWER_MAP_SYM_0` :1285-1300、`NODE_POWER_MAP_SYM_0`
:1303-1318。P13 孪生 = /tmp/LA13_f0b_aff_azn.lean
:2220/:2234/:2260/:2275/:2289/:2303/:2317（结论槽逐字对照 HOL 无转录缺陷；
`hypFaceP13` 之外的三个 map 直接用 LA3 canonical def `nnOfHyp_p3`/`eeOfHyp_p3`
/`ffOfHyp_p3`）。face 用本文件 canonical def `hypFaceFb`（LA13 草案 :151
`hypFaceP13` 的 ScsV39 世界孪生）。

证法（陈述逐槽同 HOL/孪生，证体零新数学，FAN-free）：HOL 七件的 `FAN_SYM_0`
输入只经 `ELMS_OF_HYPERMAP_HYP` / `DART_OF_HYP_VV`（hypermap 型编码下的
face/dart 刻画）进入；本编码 face = ff-轨道集（defining）、dart 资格 = if-
判据（defining），刻画步消失，七件归约为 F1 机械：
- FACE_SYM_0 / FACE_ALL_SYM_0 = `ff_POWER_COMMUTATIVE_SYM_0_fb` + 轨道集
  extensionality（迭代次数 n 双向搬运）；
- NODE_MAP / EDGE_MAP = dart 负像桥（`dartNegMemFb`/`dartNegNotFb`，F1
  `ff_FUN_COMMUTATIVE_SYM_0_fb` 证体内同一构造提为私件）+ dart 点值 +
  `SYM_AZIM_CYCLE_SYM_0_fb`（仅 nn 有 azim 内容）；EDGE_POWER / NODE_POWER =
  `iterCommFb`（HOL 同款 FUN_COMMUTATIVE，EDGE/NODE_MAP 逐点版）；
- IMAGE_NODE = NODE_MAP 逐点 funext + `Set.image_image`。
故 F0-b 依赖裁定 = 跳过（不 import LocalAuto13、不重刻 `fanNegCoreP13`），
详见快照 PLAN.md。 -/

/-- HOL `face (hypermap (HYP (x,V,E))) d`：`ff_of_hyp` 的轨道集（Hypermap
`orbit_map` 约定；LA13 草案 `hypFaceP13`（/tmp/LA13_f0b_aff_azn.lean:151）的
ScsV39 世界孪生，组装自 LA3 canonical def `ffOfHyp_p3`）。 -/
def hypFaceFb (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    Set (V3 × V3) := {y | ∃ n : ℕ, (ffOfHyp_p3 x V E)^[n] d = y}

/-- `ee_of_hyp` 在 dart 上的显式值。 -/
private theorem eeMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∈ dartsOfHyp_p3 E V) : eeOfHyp_p3 x V E d = (d.2, d.1) := by
  unfold eeOfHyp_p3
  rw [if_pos hmem]

/-- `ee_of_hyp` 在非 dart 上恒等。 -/
private theorem eeNotMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∉ dartsOfHyp_p3 E V) : eeOfHyp_p3 x V E d = d := by
  unfold eeOfHyp_p3
  rw [if_neg hmem]

/-- `nn_of_hyp` 在 dart 上的显式值。 -/
private theorem nnMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∈ dartsOfHyp_p3 E V) :
    nnOfHyp_p3 x V E d = (d.1, azimCycle_p3 (EE_p3 d.1 E) x d.1 d.2) := by
  unfold nnOfHyp_p3
  rw [if_pos hmem]

/-- `nn_of_hyp` 在非 dart 上恒等。 -/
private theorem nnNotMemEqFb {x : V3} {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hmem : d ∉ dartsOfHyp_p3 E V) : nnOfHyp_p3 x V E d = d := by
  unfold nnOfHyp_p3
  rw [if_neg hmem]

/-- dart 负像桥（正向）：`x` 是 `(V,E)`-dart ⇒ 负像是负向族 dart（F1
`ff_FUN_COMMUTATIVE_SYM_0_fb` 证体内同一构造提为私件）。 -/
private theorem dartNegMemFb {vv : ℕ → V3} {V : Set V3} {E : Set (Set V3)}
    (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hne : ∀ j, vv j ≠ vv (j + 1)) {x : V3 × V3}
    (hx : x ∈ dartsOfHyp_p3 E V) :
    ((fun p : V3 × V3 => (-p.1, -p.2)) x) ∈
      dartsOfHyp_p3
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        (Set.image (fun i : ℕ => -(vv i)) Set.univ) := by
  have hord := dartInvFb (fun z hz => vvmemFb hV hz) (edgeMemFb hE) hne hx
  exact ordMemDartsFb (vv := fun i : ℕ => -(vv i)) ((memNegEFb hE).mp hord)

/-- dart 负像桥（反向）：`x` 非 `(V,E)`-dart ⇒ 负像非负向族 dart。 -/
private theorem dartNegNotFb {vv : ℕ → V3} {V : Set V3} {E : Set (Set V3)}
    (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hne : ∀ j, vv j ≠ vv (j + 1)) {x : V3 × V3}
    (hx : x ∉ dartsOfHyp_p3 E V) :
    ((fun p : V3 × V3 => (-p.1, -p.2)) x) ∉
      dartsOfHyp_p3
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        (Set.image (fun i : ℕ => -(vv i)) Set.univ) := by
  have hneN : ∀ j, -(vv j) ≠ -(vv (j + 1)) := fun j hc => hne j (by simpa using hc)
  intro hmem
  refine hx ?_
  have hord := dartInvFb (fun z hz => negVmemFb vv hz) (negEdgeMemFb vv) hneN hmem
  exact ordMemDartsFb (vv := fun i : ℕ => -(vv i)) ((memNegEFb hE).mpr hord)

/-- HOL `FACE_SYM_0`（YXIONXL2.hl:846-880）；LA13 孪生 `FACE_SYM_0_p13`
（/tmp/LA13_f0b_aff_azn.lean:2220）。证体 = `ff_POWER_COMMUTATIVE_SYM_0_fb`
+ 轨道集 extensionality（替代 HOL 的 ELMS_OF_HYPERMAP_HYP 刻画步）。 -/
theorem FACE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    hypFaceFb 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        ((fun p : V3 × V3 => (-p.1, -p.2)) x)
      = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) (hypFaceFb 0 V E x) := by
  have hpc := ff_POWER_COMMUTATIVE_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  unfold hypFaceFb
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨(ffOfHyp_p3 0 V E)^[n] x, ⟨n, rfl⟩, ?_⟩
    exact (hpc n x).symm.trans hn
  · rintro ⟨z, ⟨n, hz⟩, hy⟩
    refine ⟨n, ?_⟩
    rw [hpc n x, hz]
    exact hy

/-- HOL `FACE_ALL_SYM_0`（YXIONXL2.hl:1056-1090，族根）；LA13 孪生
`FACE_ALL_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2234）。 -/
theorem FACE_ALL_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ x : V3 × V3,
      hypFaceFb 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = Set.image (fun p : V3 × V3 => (-p.1, -p.2)) (hypFaceFb 0 V E x) := by
  intro x
  exact FACE_SYM_0_fb s vv k V E FF x hk hV hE hFF hiscs hk3 hbb

/-- HOL `NODE_MAP_SYM_0`（YXIONXL2.hl:1143-1184）；LA13 孪生
`NODE_MAP_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2260）。证体 = dart 负像桥 +
dart 点值 + `SYM_AZIM_CYCLE_SYM_0_fb`（替代 HOL 的 ELMS_OF_HYPERMAP_HYP +
DART_OF_HYP_VV + SYM_AZIM_CYCLE_SYM_0 链）。 -/
theorem NODE_MAP_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ x : V3 × V3,
      nnOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (nnOfHyp_p3 0 V E x) := by
  obtain ⟨-, -, -, -, -, hne, -, -⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  intro x
  by_cases hx : x ∈ dartsOfHyp_p3 E V
  · rw [nnMemEqFb (dartNegMemFb hV hE hne hx), nnMemEqFb hx]
    show (-(x.1),
            azimCycle_p3
              (EE_p3 (-(x.1))
                (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
              0 (-(x.1)) (-(x.2)))
        = (-(x.1),
            -(azimCycle_p3 (EE_p3 (x.1) E) 0 (x.1) (x.2)))
    rw [show EE_p3 (-(x.1))
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          = ee (-(x.1))
              (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) from rfl,
      show EE_p3 (x.1) E = ee (x.1) E from rfl,
      SYM_AZIM_CYCLE_SYM_0_fb s vv k V E FF x hk hV hE hFF hiscs hk3 hbb hx]
  · rw [nnNotMemEqFb (dartNegNotFb hV hE hne hx), nnNotMemEqFb hx]

/-- HOL `IMAGE_NODE_SYM_0`（YXIONXL2.hl:1188-1229）；LA13 孪生
`IMAGE_NODE_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2275）。证体 = NODE_MAP
逐点 funext + `Set.image_image`（替代 HOL 的 IMAGE/IN_ELIM 展开）。 -/
theorem IMAGE_NODE_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ A : Set (V3 × V3),
      Set.image (nnOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
          (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A)
        = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
            (Set.image (nnOfHyp_p3 0 V E) A) := by
  have hfun : (fun y : V3 × V3 =>
        nnOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) y))
      = (fun y : V3 × V3 =>
        (fun p : V3 × V3 => (-p.1, -p.2)) (nnOfHyp_p3 0 V E y)) :=
    funext (NODE_MAP_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb)
  intro A
  have h1 : Set.image
        (nnOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
        (Set.image (fun p : V3 × V3 => (-p.1, -p.2)) A)
      = Set.image (fun y : V3 × V3 =>
          (fun p : V3 × V3 => (-p.1, -p.2)) (nnOfHyp_p3 0 V E y)) A := by
    rw [Set.image_image, hfun]
  rw [h1, Set.image_image]

/-- HOL `EDGE_MAP_SYM_0`（YXIONXL2.hl:1242-1281）；LA13 孪生
`EDGE_MAP_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2289）。证体 = dart 负像桥 +
dart 点值（ee 是换位，无 azim 内容）。 -/
theorem EDGE_MAP_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ x : V3 × V3,
      eeOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) (eeOfHyp_p3 0 V E x) := by
  obtain ⟨-, -, -, -, -, hne, -, -⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  intro x
  by_cases hx : x ∈ dartsOfHyp_p3 E V
  · rw [eeMemEqFb (dartNegMemFb hV hE hne hx), eeMemEqFb hx]
  · rw [eeNotMemEqFb (dartNegNotFb hV hE hne hx), eeNotMemEqFb hx]

/-- HOL `EDGE_POWER_MAP_SYM_0`（YXIONXL2.hl:1285-1300）；LA13 孪生
`EDGE_POWER_MAP_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2303）。证体 = HOL 同款
`FUN_COMMUTATIVE` 迭代转移（`iterCommFb`，EDGE_MAP 逐点版）。 -/
theorem EDGE_POWER_MAP_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (eeOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) ((eeOfHyp_p3 0 V E)^[n] x) := by
  intro n x
  exact iterCommFb (EDGE_MAP_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb) n x

/-- HOL `NODE_POWER_MAP_SYM_0`（YXIONXL2.hl:1303-1318）；LA13 孪生
`NODE_POWER_MAP_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2317）。证体 = HOL 同款
`FUN_COMMUTATIVE` 迭代转移（`iterCommFb`，NODE_MAP 逐点版）。 -/
theorem NODE_POWER_MAP_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    ∀ (n : ℕ) (x : V3 × V3),
      (nnOfHyp_p3 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))^[n]
          ((fun p : V3 × V3 => (-p.1, -p.2)) x)
        = (fun p : V3 × V3 => (-p.1, -p.2)) ((nnOfHyp_p3 0 V E)^[n] x) := by
  intro n x
  exact iterCommFb (NODE_MAP_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb) n x


/-! ## F3（fanbase-f3-w1）：FACE_DUAL → LOCAL_FAN_DUAL → CONVEX_LOCAL_FAN

HOL 锚（YXIONXL2.hl）：`FACE_DUAL_SYM_0` :1505-1556、`LOCAL_FAN_DUAL_SYM_0`
:1558-1882、`CONVEX_LOCAL_FAN_SYM_0` :2029-2182。P13 孪生 =
/tmp/LA13_f0b_aff_azn.lean :2332/:2343/:2357。

陈述槽照 HOL 正本（P13 孪生转录缺陷注记：`FACE_DUAL_SYM_0_p13` 的 face 槽写
`hypFaceP13 0 V E x`，而 HOL 正本（:1505 假设块 `SND x,FST x = v1`，结论
`face … v1`）取的是 backward dart `(SND x, FST x)`；forward dart 的 ff-轨道
含 forward dart 本身（n=0）而 backward dart 像集不含它（`vv i ≠ vv (i+1)` 且
`2 < k` 时无指标回绕），故孪生形在 k ≥ 4 下不成立，本件按 HOL 取 `(x.2, x.1)`。

证法（FAN-free，同 F2 口径）：FACE_DUAL = `FF_OF_HYP_ITER_VV_fb` 闭式 + 轨道
extensionality；迭代次数取 `n = i * (k - 1) + m`（免减法消去：`A = n*(k-1)+m`
满足 `A + n = n*k + m`、`i + n = i*k + m`，两侧同加 `n` 后模 `k` 相消）。-/

/-- `Periodic vv k` 下同余指标的点值相等（FACE_DUAL 消用）。 -/
private theorem vvModEqFb {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k) {a b : ℕ}
    (h : a % k = b % k) : vv a = vv b := by
  rw [← periodicModFb hper a, ← periodicModFb hper b, h]

/-- 有界消去：`(a + c) ≡ (b + c) (mod k) → a ≡ b (mod k)`。 -/
private theorem modAddCancelFb {k a b c : ℕ} (_hkpos : 0 < k)
    (h : (a + c) % k = (b + c) % k) : a % k = b % k := by
  have hz : ((a:ℤ) + c) % (k:ℤ) = ((b:ℤ) + c) % (k:ℤ) := by exact_mod_cast h
  have h1 : (((a:ℤ) + c) - ((b:ℤ) + c)) % (k:ℤ) = 0 :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hz
  have h2 : ((a:ℤ) - (b:ℤ)) % (k:ℤ) = 0 := by
    rw [show ((a:ℤ) - (b:ℤ)) = ((a:ℤ) + c - ((b:ℤ) + c)) from by ring]
    exact h1
  have h3 := (Int.emod_eq_emod_iff_emod_sub_eq_zero (m := (a:ℤ)) (k := (b:ℤ))
    (n := (k:ℤ))).mpr h2
  exact_mod_cast h3

/-- 轨道命中模核（无减法形；`t + 1` 为模）：迭代次数 `n = i * t + m` 时
`n * t + m ≡ i (mod t + 1)`。 -/
private theorem orbitHitModCoreFb (i m : ℕ) {t : ℕ} :
    ((i * t + m) * t + m) % (t + 1) = i % (t + 1) := by
  have hB1 : (i * t + m) * t + (i * t + m) = (i * t + m) * (t + 1) := by ring
  have hB2 : i + (i * t + m) = i * (t + 1) + m := by ring
  have e1 : ((i * t + m) * t + m + (i * t + m)) % (t + 1)
      = (i + (i * t + m)) % (t + 1) := by
    rw [Nat.add_assoc, Nat.add_comm m (i * t + m), ← Nat.add_assoc, hB1, hB2]
    simp [Nat.add_mod, Nat.mul_mod]
  exact modAddCancelFb (by omega) e1

/-- `k > 0` 时迭代次数 `n = i * (k - 1) + m` 给出 backward 轨道命中：模 `k` 有
`n * (k - 1) + m ≡ i`。 -/
private theorem orbitHitModFb {k : ℕ} (hkpos : 0 < k) (i m : ℕ) :
    ((i * (k - 1) + m) * (k - 1) + m) % k = i % k := by
  have h := orbitHitModCoreFb i m (t := k - 1)
  rwa [show (k - 1) + 1 = k from by omega] at h

/-- FACE_DUAL 内核：任一 backward dart 的 ff-轨道 = 全体 backward dart 集。 -/
private theorem faceBackwardFb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (m : ℕ)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    hypFaceFb 0 V E (vv (m + 1), vv m)
      = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  have hiter := FF_OF_HYP_ITER_VV_fb s vv k V E FF m hk hV hE hFF hiscs hk3 hbb
  obtain ⟨hge, -, hper, -, -, -, -, -⟩ :=
    fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hkpos : 0 < k := by omega
  unfold hypFaceFb
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, hn⟩
    rw [hiter n] at hn
    exact ⟨n * (k - 1) + m, Set.mem_univ _, hn⟩
  · rintro ⟨i, -, hi⟩
    refine ⟨i * (k - 1) + m, ?_⟩
    rw [hiter (i * (k - 1) + m)]
    have hmod := orbitHitModFb hkpos i m
    rw [vvModEqFb hper hmod, vvModEqFb hper (modSuccFb hmod), hi]

/-- HOL `FACE_DUAL_SYM_0`（YXIONXL2.hl:1505-1556）；LA13 孪生
`FACE_DUAL_SYM_0_p13`（/tmp/LA13_f0b_aff_azn.lean:2332，face 槽转录缺陷见块注）。
证体 = `x ∈ FF` 的 vv-原像 + `faceBackwardFb` 闭式收口（替代 HOL 的
ELMS_OF_HYPERMAP_HYP 刻画 + FF_OF_HYP_ITER_VV + DUAL_EXISTS_MOD +
PERIODIC_PROPERTY + MOD_LT/MOD_ADD_MOD 链）。 -/
theorem FACE_DUAL_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (x : V3 × V3)
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv)
    (hxFF : x ∈ FF) :
    Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
      = hypFaceFb 0 V E (x.2, x.1) := by
  rw [← hFF, Set.mem_image] at hxFF
  obtain ⟨j, -, hj⟩ := hxFF
  have hx2 : (x.2, x.1) = (vv (j + 1), vv j) := by rw [← hj]
  rw [hx2]
  exact (faceBackwardFb s vv k V E FF j hk hV hE hFF hiscs hk3 hbb).symm


/-! ## F3 支撑层 A：取反传输链（f0b 草案 §0-§3 同证移植，P13→Fb 改名）

供 `LOCAL_FAN_DUAL_SYM_0_fb` 消费：FAN 六合取在点取反下的逐条传输
（HOL `FAN_SYM_0` src:336 内容）+ aff_ge 取反传输（HOL `AFF_GE_VEC0_SYM_0`
src:315 内容）。全部 private。 -/

private theorem negInjFb : Function.Injective (fun x : V3 => -x) :=
  fun _ _ h => by simpa using h

private theorem imageUnivCongrFb {α β} {f g : α → β} (h : ∀ i, f i = g i) :
    Set.image f Set.univ = Set.image g Set.univ :=
  congrArg (Set.image · Set.univ) (funext h)

private theorem inSymFb {a : V3} {A : Set V3} (h : a ∈ A) :
    -a ∈ Set.image (fun x : V3 => -x) A :=
  ⟨a, h, rfl⟩

private theorem subsetSymFb {A B : Set V3} (h : A ⊆ B) :
    Set.image (fun x : V3 => -x) A ⊆ Set.image (fun x : V3 => -x) B :=
  fun x hx => let ⟨y, hy, hyx⟩ := hx; ⟨y, h hy, hyx⟩

private theorem imageVSymFb (vv : ℕ → V3) :
    Set.image (fun i : ℕ => -(vv i)) Set.univ
      = Set.image (fun x : V3 => -x) (Set.image vv Set.univ) := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨vv i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

private theorem unionsImageFanFb (vv : ℕ → V3) :
    ⋃₀ (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ)
      = Set.image (fun x : V3 => -x)
          (⋃₀ (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ)) := by
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨i, -, rfl⟩ := ht
    rcases Set.mem_insert_iff.mp hx with rfl | rfl
    · exact ⟨vv i, ⟨{vv i, vv (i + 1)}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert _ _⟩, rfl⟩
    · exact ⟨vv (i + 1), ⟨{vv i, vv (i + 1)}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨t', ht', hy'⟩ := hy
    obtain ⟨i, -, rfl⟩ := ht'
    subst hyx
    rcases Set.mem_insert_iff.mp hy' with rfl | rfl
    · exact ⟨{-(vv i), -(vv (i + 1))}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert _ _⟩
    · exact ⟨{-(vv i), -(vv (i + 1))}, ⟨i, Set.mem_univ _, rfl⟩,
        Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

private theorem finiteSymFb {A : Set V3} (h : A.Finite) :
    (Set.image (fun x : V3 => -x) A).Finite := h.image _

private theorem element2SymFb (a b : V3) :
    ({-a, -b} : Set V3) = Set.image (fun x : V3 => -x) ({a, b} : Set V3) := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem graphSymFb (vv : ℕ → V3)
    (h : Fan.Graph (Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ)) :
    Fan.Graph (Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ) := by
  intro e he
  obtain ⟨x, -, rfl⟩ := he
  obtain ⟨hf, hc⟩ := h {vv x, vv (x + 1)} ⟨x, Set.mem_univ _, rfl⟩
  have hne : vv x ≠ vv (x + 1) := by
    intro hcon
    have h1 : hf.toFinset.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      have ha' : a ∈ ({vv x, vv (x + 1)} : Set V3) := by simpa using ha
      have hb' : b ∈ ({vv x, vv (x + 1)} : Set V3) := by simpa using hb
      rw [hcon] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp
    omega
  have hne' : -(vv x) ≠ -(vv (x + 1)) := fun hcc => hne (by simpa using hcc)
  have hset : ({-(vv x), -(vv (x + 1))} : Set V3)
      = Set.image (fun y : V3 => -y) ({vv x, vv (x + 1)} : Set V3) := by
    rw [← element2SymFb]
  have hf2 : (Set.image (fun y : V3 => -y) ({vv x, vv (x + 1)} : Set V3)).Finite :=
    hf.image _
  have hfin : ({-(vv x), -(vv (x + 1))} : Set V3).Finite := by
    rw [hset]
    exact hf2
  have hcard : hfin.toFinset.card = 2 := by
    have h2 : ({vv x, vv (x + 1)} : Set V3).ncard = 2 :=
      (Set.ncard_eq_toFinset_card _ hf).trans hc
    have h3 : ({-(vv x), -(vv (x + 1))} : Set V3).ncard = 2 := by
      rw [hset, Set.ncard_image_of_injective _ negInjFb]
      exact h2
    exact (Set.ncard_eq_toFinset_card _ hfin).symm.trans h3
  exact ⟨hfin, hcard⟩

private theorem reflSymFb (A : Set V3) :
    Set.image (fun x : V3 => -x) (Set.image (fun x : V3 => -x) A) = A := by
  simp

private theorem imageESymFb (vv : ℕ → V3) {e : Set V3}
    (h : e ∈ Set.image (fun i : ℕ => {-(vv i), -(vv (i + 1))}) Set.univ) :
    Set.image (fun x : V3 => -x) e
      ∈ Set.image (fun i : ℕ => {vv i, vv (i + 1)}) Set.univ := by
  obtain ⟨x, -, rfl⟩ := h
  have himg : Set.image (fun x : V3 => -x) {-(vv x), -(vv (x + 1))}
      = {vv x, vv (x + 1)} := by
    rw [← element2SymFb (-(vv x)) (-(vv (x + 1)))]
    simp
  rw [himg]
  exact ⟨x, Set.mem_univ _, rfl⟩

private theorem collinearSymFb {e : Set V3} (h : Collinear ℝ e) :
    Collinear ℝ (Set.image (fun x : V3 => -x) e) := by
  by_cases he : e = ∅
  · rw [he, Set.image_empty]
    exact @collinear_empty ℝ V3 V3 _ _ _ _
  · obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr he
    rw [collinear_iff_of_mem (Set.mem_image_of_mem _ hp₀)]
    obtain ⟨v, hv⟩ := (collinear_iff_of_mem hp₀).mp h
    refine ⟨v, ?_⟩
    rintro p ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hv x hx
    refine ⟨-r, ?_⟩
    have hx2 : (-x : V3) = -(r • v +ᵥ p₀) := by rw [hr]
    show (-x : V3) = (-r) • v +ᵥ (-p₀)
    rw [hx2, vadd_eq_add, vadd_eq_add, neg_add, neg_smul]

private theorem unionSymFb (s e : Set V3) :
    Set.image (fun x : V3 => -x) (s ∪ e)
      = Set.image (fun x : V3 => -x) s ∪ Set.image (fun x : V3 => -x) e :=
  Set.image_union _ _ _

private theorem vec0SymFb :
    Set.image (fun x : V3 => -x) ({0} : Set V3) = ({0} : Set V3) := by
  ext x
  simp

private theorem vec0UnionSymFb (e : Set V3) :
    Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
      = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e := by
  rw [unionSymFb, vec0SymFb]

private theorem notCollinearSymFb {e : Set V3} (h : ¬Collinear ℝ e) :
    ¬Collinear ℝ (Set.image (fun x : V3 => -x) e) := fun hc =>
  h (by rw [← reflSymFb e]; exact collinearSymFb hc)

private theorem vec0NotCollinearSymFb {e : Set V3}
    (h : ¬Collinear ℝ (({0} : Set V3) ∪ e)) :
    ¬Collinear ℝ (({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e) := fun hc =>
  h (by
    have h1 := collinearSymFb hc
    rw [unionSymFb, vec0SymFb, reflSymFb e] at h1
    exact h1)

private theorem interSymFb (e1 e2 : Set V3) :
    Set.image (fun x : V3 => -x) (e1 ∩ e2)
      = Set.image (fun x : V3 => -x) e1 ∩ Set.image (fun x : V3 => -x) e2 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨⟨y, hy1, rfl⟩, ⟨y, hy2, rfl⟩⟩
  · rintro ⟨⟨y1, hy1, rfl⟩, ⟨y2, hy2, hy12⟩⟩
    have hyy : y1 = y2 := neg_inj.mp hy12.symm
    exact ⟨y1, ⟨hy1, hyy ▸ hy2⟩, rfl⟩

private theorem insertUnionFb (a : V3) (s : Set V3) :
    insert a s = ({a} : Set V3) ∪ s := by
  ext z
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]

private theorem affGeNegPtFb {e : Set V3} {w : V3}
    (hw : w ∈ affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)) :
    -w ∈ affGe ({0} : Set V3) e := by
  obtain ⟨f, hfin, hwv, hfp, hfsum⟩ := hw
  have hU : Set.image (fun x : V3 => -x) (({0} : Set V3) ∪ e)
      = ({0} : Set V3) ∪ Set.image (fun x : V3 => -x) e := by
    rw [Set.image_union, vec0SymFb]
  have hfinA : ((({0} : Set V3) ∪ e : Set V3)).Finite :=
    (Set.finite_image_iff negInjFb.injOn).mp (by rw [hU]; exact hfin)
  have heq : hfin.toFinset = hfinA.toFinset.image (fun x : V3 => -x) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_image,
      Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨0, Or.inl rfl, by simp⟩
      · exact ⟨y, Or.inr hy, rfl⟩
    · rintro ⟨a, (rfl | hy), rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inr ⟨a, hy, rfl⟩
  refine ⟨fun y => f (-y), hfinA, ?_, ?_, ?_⟩
  · calc -w = ∑ x ∈ hfin.toFinset, f x • (-x) := by
          rw [hwv]
          simp only [Finset.sum_neg_distrib, smul_neg]
      _ = ∑ x ∈ hfinA.toFinset.image (fun x : V3 => -x), f x • (-x) := by rw [heq]
      _ = ∑ y ∈ hfinA.toFinset, f (-y) • y := by
          simp only [Finset.sum_image (f := fun z : V3 => f z • (-z))
            (g := fun x : V3 => -x) negInjFb.injOn, neg_neg]
  · intro z hz
    exact hfp (-z) ⟨z, hz, rfl⟩
  · show (∑ y ∈ hfinA.toFinset, f (-y)) = 1
    rw [← Finset.sum_image (f := f) (g := fun x : V3 => -x) negInjFb.injOn, ← heq]
    exact hfsum

private theorem affGeNegFb (e : Set V3) :
    affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)
      = Set.image (fun x : V3 => -x) (affGe ({0} : Set V3) e) := by
  ext v
  constructor
  · intro hv
    exact ⟨-v, affGeNegPtFb hv, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    refine affGeNegPtFb (e := Set.image (fun x : V3 => -x) e) ?_
    rw [reflSymFb e]
    exact hu

private theorem affGeNeg2Fb (e : Set V3) :
    affGe ({0} : Set V3) e
      = Set.image (fun x : V3 => -x)
          (affGe ({0} : Set V3) (Set.image (fun x : V3 => -x) e)) := by
  have h := affGeNegFb (Set.image (fun x : V3 => -x) e)
  rw [reflSymFb e] at h
  exact h

/-- FAN 六合取的逐条取反传输（HOL `FAN_SYM_0` src:336 证体内容；
f0b 草案 `fanNegCoreP13` 的 ScsV39 世界同证移植）。 -/
private theorem fanNegCoreFb (vv : ℕ → V3)
    (hf : Fan.FAN 0 (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)) :
    Fan.FAN 0 (Set.image (fun i : ℕ => -(vv i)) Set.univ)
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) := by
  have hV : Set.image (fun i : ℕ => -(vv i)) Set.univ
      = Set.image (fun x : V3 => -x) (Set.image vv Set.univ) := imageVSymFb vv
  refine ⟨?_, graphSymFb vv hf.2.1, ?_, ?_, ?_, ?_⟩
  · rw [unionsImageFanFb vv, hV]
    exact subsetSymFb hf.1
  · rw [hV]
    refine ⟨finiteSymFb hf.2.2.1.1, fun hempty => ?_⟩
    rw [Set.image_eq_empty] at hempty
    exact hf.2.2.1.2 hempty
  · intro h0
    rw [hV, Set.mem_image] at h0
    obtain ⟨y, hy, hneg⟩ := h0
    have hy0 : y = 0 := by simpa using hneg
    rw [hy0] at hy
    exact hf.2.2.2.1 hy
  · intro e he
    obtain ⟨i, -, rfl⟩ := he
    show ¬Collinear ℝ (insert 0 ({-(vv i), -(vv (i + 1))} : Set V3))
    rw [element2SymFb (vv i) (vv (i + 1)), insertUnionFb]
    exact vec0NotCollinearSymFb
      (hf.2.2.2.2.1 ({vv i, vv (i + 1)} : Set V3) ⟨i, Set.mem_univ _, rfl⟩)
  · intro e1 he1 e2 he2
    have hmem : ∀ e : Set V3,
        e ∈ Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ
          ∪ {s : Set V3 | ∃ v ∈ Set.image (fun i : ℕ => -(vv i)) Set.univ, s = {v}} →
        Set.image (fun x : V3 => -x) e
          ∈ Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ
            ∪ {s : Set V3 | ∃ v ∈ Set.image vv Set.univ, s = {v}} := by
      intro e he
      rcases (Set.mem_union _ _ _).mp he with he | he
      · exact Or.inl (imageESymFb vv he)
      · obtain ⟨v, hv, rfl⟩ := he
        obtain ⟨i, -, rfl⟩ := hv
        refine Or.inr ⟨vv i, ⟨i, Set.mem_univ _, rfl⟩, ?_⟩
        rw [Set.image_singleton, neg_neg]
    have key := hf.2.2.2.2.2 (Set.image (fun x : V3 => -x) e1) (hmem e1 he1)
      (Set.image (fun x : V3 => -x) e2) (hmem e2 he2)
    rw [affGeNeg2Fb e1, affGeNeg2Fb e2, ← interSymFb, key, ← interSymFb,
      ← affGeNeg2Fb (e1 ∩ e2)]

/-! ## F3 支撑层 B：重指标像桥（f0b 草案 §2 同证移植）

`k - (i % k + 1)` 重指标像 = 平取负像的桥（HOL `OPP_IMAGE_V/E/F2_EQ_NEG`
src:885/:902/:991）。 -/

private theorem oppSucModFb {k x : ℕ} (hk : k ≠ 0) :
    k - ((k - (x % k + 1)) % k + 1) = x % k := by
  have h1 : x % k < k := Nat.mod_lt x (Nat.pos_of_ne_zero hk)
  have h2 : (k - (x % k + 1)) % k = k - (x % k + 1) := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  omega

private theorem modSucModFb {k x : ℕ} (hk : 1 < k) :
    (x % k + 1) % k = (x + 1) % k := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [show (x + 1) % k = (x % k + 1 % k) % k from Nat.add_mod x 1 k, h1]

private theorem sucModEqModSucFb {k x : ℕ} (hk : 1 < k) :
    (k - (x % k + 1)) % k = (k - ((x + 1) % k)) % k := by
  have h1 : x % k < k := Nat.mod_lt x (by omega)
  by_cases hlt : x % k + 1 < k
  · rw [(modSucModFb (x := x) hk).symm, Nat.mod_eq_of_lt hlt]
  · have heq : x % k + 1 = k := by omega
    have h0 : (x + 1) % k = 0 := by
      rw [(modSucModFb (x := x) hk).symm, heq, Nat.mod_self]
    rw [heq, Nat.sub_self, Nat.zero_mod, h0, Nat.sub_zero, Nat.mod_self]

private theorem pairSetEqFb {a b c d : V3} :
    ({a, b} : Set V3) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 : a ∈ ({c, d} : Set V3) := by rw [← h]; simp
    have h2 : b ∈ ({c, d} : Set V3) := by rw [← h]; simp
    have h3 : d ∈ ({a, b} : Set V3) := by rw [h]; simp
    have h4 : c ∈ ({a, b} : Set V3) := by rw [h]; simp
    rcases Set.mem_insert_iff.mp h1 with hac | had
    · rcases Set.mem_insert_iff.mp h2 with hbc | hbd
      · rcases Set.mem_insert_iff.mp h3 with hda | hdb
        · exact Or.inr ⟨hda.symm, hbc⟩
        · exact Or.inl ⟨hac, hdb.symm⟩
      · exact Or.inl ⟨hac, hbd⟩
    · rcases Set.mem_insert_iff.mp h2 with hbc | hbd
      · exact Or.inr ⟨had, hbc⟩
      · rcases Set.mem_insert_iff.mp h4 with hca | hcb
        · exact Or.inl ⟨hca.symm, hbd⟩
        · exact Or.inr ⟨had, hcb.symm⟩
  · rintro (h | h)
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

private theorem dartEqFb {a b c d : V3} (h1 : a = c) (h2 : b = d) :
    ((a, b) : V3 × V3) = (c, d) := by rw [h1, h2]

private theorem oppImageVEqFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : k ≠ 0) :
    Set.image (fun i : ℕ => vv (k - (i % k + 1))) Set.univ
      = Set.image vv Set.univ := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨k - (i % k + 1), rfl⟩
  · rintro ⟨j, rfl⟩
    have hjk : j % k < k := Nat.mod_lt j (Nat.pos_of_ne_zero hk)
    have h1 : (k - (j % k + 1)) % k = k - (j % k + 1) := Nat.mod_eq_of_lt (by omega)
    have h2 : k - ((k - (j % k + 1)) % k + 1) = j % k := oppSucModFb hk
    rw [h1] at h2
    exact ⟨k - (j % k + 1), by rw [h1, h2, periodicModFb hper j]⟩

private theorem oppImageEEqFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ => ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
        Set.univ
      = Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ := by
  have hk0 : (0:ℕ) < k := by omega
  have hv0 : vv k = vv 0 := by
    have h := hper 0
    rwa [Nat.zero_add] at h
  have key : ∀ j, j < k → ({vv j, vv (j + 1)} : Set V3)
      ∈ Set.image
          (fun i : ℕ => ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
          Set.univ := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) k with hlt | heq
    · refine ⟨k - (j + 2), Set.mem_univ _, ?_⟩
      show ({vv (k - ((k - (j + 2)) % k + 1)),
             vv (k - ((k - (j + 2) + 1) % k + 1))} : Set V3)
          = {vv j, vv (j + 1)}
      rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) < k),
          Nat.mod_eq_of_lt (by omega : k - (j + 2) + 1 < k),
          show k - (k - (j + 2) + 1 + 1) = j from by omega,
          show k - (k - (j + 2) + 1) = j + 1 from by omega,
          pairSetCommFb]
    · have heq' : j + 1 = k := by omega
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      show ({vv (k - ((k - 1) % k + 1)),
             vv (k - ((k - 1 + 1) % k + 1))} : Set V3)
          = {vv j, vv (j + 1)}
      rw [Nat.mod_eq_of_lt (by omega : k - 1 < k),
        show k - 1 + 1 = k from by omega, Nat.mod_self, heq', hv0,
        show j = k - 1 from by omega,
        show k - (0 + 1) = k - 1 from by omega, Nat.sub_self, pairSetCommFb]
  ext e
  constructor
  · intro he
    obtain ⟨i, -, hFe⟩ := he
    subst hFe
    have hu : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    have hk1 : i % k < k := Nat.mod_lt i hk0
    by_cases hlt : i % k + 1 < k
    · rw [Set.mem_image]
      show ∃ x ∈ Set.univ, ({vv x, vv (x + 1)} : Set V3)
          = {vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))}
      rw [hu, Nat.mod_eq_of_lt hlt]
      refine ⟨k - (i % k + 2), Set.mem_univ _, ?_⟩
      rw [pairSetCommFb,
        show k - (i % k + 2) + 1 = k - (i % k + 1) from by omega,
        show k - (i % k + 2) = k - (i % k + 1 + 1) from by omega]
    · rw [Set.mem_image]
      show ∃ x ∈ Set.univ, ({vv x, vv (x + 1)} : Set V3)
          = {vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))}
      have heq : i % k + 1 = k := by omega
      rw [hu, heq, Nat.mod_self, Nat.sub_self]
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      rw [show k - 1 + 1 = k from by omega, hv0,
        show k - (0 + 1) = k - 1 from by omega, pairSetCommFb]
  · intro he
    obtain ⟨j, -, hjF⟩ := he
    subst hjF
    rw [Set.mem_image]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact key j hjk
    · show ({vv j, vv (j + 1)} : Set V3)
          ∈ Set.image
              (fun i : ℕ =>
                ({vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))} : Set V3))
              Set.univ
      have h1 : vv (j % k + 1) = vv (j + 1) := by
        rw [← periodicModFb hper (j % k + 1), Nat.mod_add_mod j k 1,
          ← periodicModFb hper (j + 1)]
      have heqset : (({vv j, vv (j + 1)} : Set V3) =
          {vv (j % k), vv (j % k + 1)}) := by
        rw [← periodicModFb hper j, ← h1]
      rw [heqset]
      exact key (j % k) (Nat.mod_lt j hk0)

private theorem oppImageFEq2Fb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : 1 < k) :
    Set.image
        (fun i : ℕ => (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))) Set.univ
      = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  have hk0 : (0:ℕ) < k := by omega
  have hv0 : vv k = vv 0 := by
    have h := hper 0
    rwa [Nat.zero_add] at h
  have key : ∀ j, j < k → (vv (j + 1), vv j)
      ∈ Set.image
          (fun i : ℕ => (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1))))
          Set.univ := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) k with hlt | heq
    · refine ⟨k - (j + 2), Set.mem_univ _, ?_⟩
      have hA : k - ((k - (j + 2)) % k + 1) = j + 1 := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) < k)]
        omega
      have hB : k - ((k - (j + 2) + 1) % k + 1) = j := by
        rw [Nat.mod_eq_of_lt (by omega : k - (j + 2) + 1 < k)]
        omega
      exact dartEqFb (congrArg vv hA) (congrArg vv hB)
    · have heq' : j + 1 = k := by omega
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      show ((vv (k - ((k - 1) % k + 1)), vv (k - ((k - 1 + 1) % k + 1))) : V3 × V3)
          = (vv (j + 1), vv j)
      rw [Nat.mod_eq_of_lt (by omega : k - 1 < k), show k - 1 + 1 = k from by omega,
        Nat.mod_self, Nat.sub_self, heq', hv0, show j = k - 1 from by omega]
  ext d
  constructor
  · intro hd
    obtain ⟨i, -, hdi⟩ := hd
    subst hdi
    rw [Set.mem_image]
    have hu : (i + 1) % k = (i % k + 1) % k := (Nat.mod_add_mod i k 1).symm
    have hk1 : i % k < k := Nat.mod_lt i hk0
    by_cases hlt : i % k + 1 < k
    · show ∃ x ∈ Set.univ, (vv (x + 1), vv x)
          = (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))
      rw [hu, Nat.mod_eq_of_lt hlt]
      refine ⟨k - (i % k + 2), Set.mem_univ _, ?_⟩
      exact dartEqFb (congrArg vv (by omega)) (congrArg vv (by omega))
    · show ∃ x ∈ Set.univ, (vv (x + 1), vv x)
          = (vv (k - (i % k + 1)), vv (k - ((i + 1) % k + 1)))
      have heq : i % k + 1 = k := by omega
      rw [hu, heq, Nat.mod_self]
      refine ⟨k - 1, Set.mem_univ _, ?_⟩
      exact dartEqFb
        (by rw [show k - 1 + 1 = k from by omega, hv0, Nat.sub_self])
        (by rw [show k - (0 + 1) = k - 1 from by omega])
  · intro hd
    obtain ⟨j, -, hjd⟩ := hd
    subst hjd
    rw [Set.mem_image]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact key j hjk
    · show ∃ x ∈ Set.univ, (vv (k - (x % k + 1)), vv (k - ((x + 1) % k + 1)))
          = (vv (j + 1), vv j)
      have h1 : vv (j % k + 1) = vv (j + 1) := by
        rw [← periodicModFb hper (j % k + 1), Nat.mod_add_mod j k 1,
          ← periodicModFb hper (j + 1)]
      have h0 : ((vv (j + 1), vv j) : V3 × V3) = (vv (j % k + 1), vv (j % k)) :=
        dartEqFb h1.symm (periodicModFb hper j).symm
      rw [h0]
      exact key (j % k) (Nat.mod_lt j hk0)

private theorem imageNegCompUnivFb {f : ℕ → V3} :
    Set.image (fun i : ℕ => -(f i)) Set.univ
      = Set.image (fun x : V3 => -x) (Set.image f Set.univ) := by
  rw [Set.image_image, imageUnivCongrFb (fun _ => rfl)]

private theorem imageNegDartCompUnivFb {f g : ℕ → V3} :
    Set.image (fun i : ℕ => (-(f i), -(g i))) Set.univ
      = Set.image (fun p : V3 × V3 => (-p.1, -p.2))
          (Set.image (fun i : ℕ => (f i, g i)) Set.univ) := by
  rw [Set.image_image, imageUnivCongrFb (fun _ => rfl)]

private theorem imageNegPairCompUnivFb {f g : ℕ → V3} :
    Set.image (fun i : ℕ => ({-(f i), -(g i)} : Set V3)) Set.univ
      = Set.image (fun S : Set V3 => Set.image (fun x : V3 => -x) S)
          (Set.image (fun i : ℕ => ({f i, g i} : Set V3)) Set.univ) := by
  ext S
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨{f i, g i}, ⟨i, rfl⟩, by rw [← element2SymFb (f i) (g i)]⟩
  · rintro ⟨T, ⟨i, rfl⟩, hT⟩
    have h2 : Set.image (fun x : V3 => -x) ({f i, g i} : Set V3)
        = {-(f i), -(g i)} := by
      rw [← element2SymFb (f i) (g i)]
    rw [h2] at hT
    exact ⟨i, hT⟩

private theorem oppImageVEqNegFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : k ≠ 0) :
    Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ
      = Set.image (fun i : ℕ => -(vv i)) Set.univ := by
  rw [imageNegCompUnivFb (f := fun i => vv (k - (i % k + 1))),
    oppImageVEqFb vv hper hk, imageNegCompUnivFb (f := vv)]

private theorem oppImageEEqNegFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3))
        Set.univ
      = Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ := by
  rw [imageNegPairCompUnivFb
      (f := fun i => vv (k - (i % k + 1)))
      (g := fun i => vv (k - ((i + 1) % k + 1))),
    oppImageEEqFb vv hper hk, imageNegPairCompUnivFb]

private theorem oppImageFEq2NegFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k)
    (hk : 1 < k) :
    Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ
      = Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ := by
  have hfun : ((fun p : V3 × V3 => (-p.1, -p.2)) ∘
      fun i : ℕ => (vv (i + 1), vv i))
      = (fun i : ℕ => (-(vv (i + 1)), -(vv i))) := funext fun i => by simp [Function.comp]
  rw [imageNegDartCompUnivFb
      (f := fun i => vv (k - (i % k + 1)))
      (g := fun i => vv (k - ((i + 1) % k + 1))),
    oppImageFEq2Fb vv hper hk, ← Set.image_comp, hfun]


/-! ## F3 支撑层 C1：canonical 族的 dart 层闭式（localFan_p3 主装配前置）

对任意满足七槽像形 + 二元邻域展开 + 三个不退化条件的族 `vv`：ff/nn/ee 在
forward/backward dart 上的一步与 n 步闭式、dart 集两分、轨道集两分。
全部 private；替代 HOL 的 ELMS_OF_HYPERMAP_HYP / DART_OF_HYP_VV 刻画链。 -/

section FanDartLayer

variable {vv : ℕ → V3} {k : ℕ} {V : Set V3} {E : Set (Set V3)}

/-- backward dart 上 ff 一步：`(vv (m+1), vv m) ↦ (vv m, vv (m + (k-1)))`。 -/
private theorem fdffValBFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hne2 : ∀ j, vv (j + 1) ≠ vv (j + k - 1)) (m : ℕ) :
    ffOfHyp_p3 0 V E (vv (m + 1), vv m) = (vv (m + (k - 1) + 1), vv (m + (k - 1))) := by
  have hd : (vv (m + 1), vv m) ∈ dartsOfHyp_p3 E V := by
    refine ordMemDartsFb (vv := vv) ?_
    rw [pairSetCommFb]
    exact edgeMemFb hE m
  rw [ffMemEqFb hd]
  show (vv m, ivsAzimCycle_p3 (EE_p3 (vv m) E) 0 (vv m) (vv (m + 1)))
      = (vv (m + (k - 1) + 1), vv (m + (k - 1)))
  have hE2 : EE_p3 (vv m) E = ({vv (m + 1), vv (m + k - 1)} : Set V3) := hEE m
  rw [hE2, pairSetCommFb, ivsTwoNeFb (hne2 m).symm,
    show vv m = vv (m + (k - 1) + 1) from by
      rw [show m + (k - 1) + 1 = m + k from by omega]; exact (hper m).symm,
    show (m:Nat) + k - 1 = m + (k - 1) from by omega]

/-- forward dart 上 ff 一步：`(vv m, vv (m+1)) ↦ (vv (m+1), vv (m+2))`。 -/
private theorem fdffValFFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hshift2 : ∀ j, vv (j + 2) ≠ vv j) (m : ℕ) :
    ffOfHyp_p3 0 V E (vv m, vv (m + 1)) = (vv (m + 1), vv (m + 2)) := by
  have hd : (vv m, vv (m + 1)) ∈ dartsOfHyp_p3 E V :=
    ordMemDartsFb (vv := vv) (edgeMemFb hE m)
  rw [ffMemEqFb hd]
  show (vv (m + 1), ivsAzimCycle_p3 (EE_p3 (vv (m + 1)) E) 0 (vv (m + 1)) (vv m))
      = (vv (m + 1), vv (m + 2))
  have hE2 : EE_p3 (vv (m + 1)) E = ({vv (m + 2), vv m} : Set V3) := by
    have h := hEE (m + 1)
    rw [show (vv (m + 1 + k - 1) : V3) = vv m from by
      rw [show (m + 1 + k - 1) = m + k from by omega, hper m]] at h
    exact h
  rw [hE2, ivsTwoNeFb (hshift2 m)]

/-- forward dart 上 nn 一步：`(vv m, vv (m+1)) ↦ (vv m, vv (m + (k-1)))`。 -/
private theorem fdnnValFFb (hper : Periodic vv k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hne2 : ∀ j, vv (j + 1) ≠ vv (j + k - 1)) (hk1 : 1 ≤ k) (m : ℕ) :
    nnOfHyp_p3 0 V E (vv m, vv (m + 1)) = (vv m, vv (m + (k - 1))) := by
  have hd : (vv m, vv (m + 1)) ∈ dartsOfHyp_p3 E V :=
    ordMemDartsFb (vv := vv) (edgeMemFb hE m)
  rw [nnMemEqFb hd]
  show (vv m, azimCycle_p3 (EE_p3 (vv m) E) 0 (vv m) (vv (m + 1)))
      = (vv m, vv (m + (k - 1)))
  have hE2 : EE_p3 (vv m) E = ({vv (m + 1), vv (m + k - 1)} : Set V3) := hEE m
  rw [hE2, pairSetCommFb, azimCycleTwoSwapFb (hne2 m).symm,
    show (m:Nat) + k - 1 = m + (k - 1) from by omega]

/-- backward dart 上 nn 一步：`(vv (m+1), vv m) ↦ (vv (m+1), vv (m+2))`。 -/
private theorem fdnnValBFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hshift2 : ∀ j, vv (j + 2) ≠ vv j) (m : ℕ) :
    nnOfHyp_p3 0 V E (vv (m + 1), vv m) = (vv (m + 1), vv (m + 2)) := by
  have hd : (vv (m + 1), vv m) ∈ dartsOfHyp_p3 E V := by
    refine ordMemDartsFb (vv := vv) ?_
    rw [pairSetCommFb]
    exact edgeMemFb hE m
  rw [nnMemEqFb hd]
  show (vv (m + 1), azimCycle_p3 (EE_p3 (vv (m + 1)) E) 0 (vv (m + 1)) (vv m))
      = (vv (m + 1), vv (m + 2))
  have hE2 : EE_p3 (vv (m + 1)) E = ({vv (m + 2), vv m} : Set V3) := by
    have h := hEE (m + 1)
    rw [show (vv (m + 1 + k - 1) : V3) = vv m from by
      rw [show (m + 1 + k - 1) = m + k from by omega, hper m]] at h
    exact h
  rw [hE2, azimCycleTwoSwapFb (hshift2 m)]

/-- backward dart 的 ff n 步闭式。 -/
private theorem fdffIterBFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hne2 : ∀ j, vv (j + 1) ≠ vv (j + k - 1)) (m : ℕ) :
    ∀ n : ℕ, (ffOfHyp_p3 0 V E)^[n] (vv (m + 1), vv m)
      = (vv (m + n * (k - 1) + 1), vv (m + n * (k - 1))) := by
  intro n
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        fdffValBFb hper hk1 hE hEE hne2 (m + n * (k - 1)),
        show m + Nat.succ n * (k - 1) = m + n * (k - 1) + (k - 1) from by
          rw [Nat.succ_mul]; ring]

/-- forward dart 的 ff n 步闭式。 -/
private theorem fdffIterFFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hshift2 : ∀ j, vv (j + 2) ≠ vv j) (m : ℕ) :
    ∀ n : ℕ, (ffOfHyp_p3 0 V E)^[n] (vv m, vv (m + 1))
      = (vv (m + n), vv (m + n + 1)) := by
  intro n
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, fdffValFFb hper hk1 hE hEE hshift2 (m + n),
        show m + Nat.succ n = m + n + 1 from by omega,
        show m + n + 2 = m + n + 1 + 1 from rfl]

/-- self_pairs 为空（每点邻域非空）。 -/
private theorem fdselfPairsEmptyFb
    (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E) :
    selfPairs_p3 E V = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨h12, hv, hev⟩ := hp
  rw [← hV, Set.mem_image] at hv
  obtain ⟨i, -, hi⟩ := hv
  have hmemb : vv (i + 1) ∈ EE_p3 p.1 E := by
    show ({p.1, vv (i + 1)} : Set V3) ∈ E
    rw [show ({p.1, vv (i + 1)} : Set V3) = ({vv i, vv (i + 1)} : Set V3) from by rw [hi]]
    exact edgeMemFb hE i
  rw [hev] at hmemb
  exact Set.notMem_empty _ hmemb

/-- ord_pairs 两分：forward ∪ backward。 -/
private theorem fdordPairsFb (hne : ∀ j, vv j ≠ vv (j + 1))
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E) :
    ordPairs_p3 E
        = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
          ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  ext p
  simp only [ordPairs_p3, Set.mem_setOf_eq]
  constructor
  · intro hp
    rw [← hE, Set.mem_image] at hp
    obtain ⟨i, -, he⟩ := hp
    rw [pairSetEqFb] at he
    rcases he with (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Set.mem_union_left _ ⟨i, Set.mem_univ _, by show (vv i, vv (i + 1)) = p; rw [h1, h2]⟩
    · exact Set.mem_union_right _ ⟨i, Set.mem_univ _, by show (vv (i + 1), vv i) = p; rw [h1, h2]⟩
  · intro he
    rcases (Set.mem_union _ _ _).mp he with he | he
    · obtain ⟨i, -, hie⟩ := he
      rw [← hie]
      exact Set.mem_setOf_eq.mpr (edgeMemFb hE i)
    · obtain ⟨i, -, hie⟩ := he
      rw [← hie]
      exact Set.mem_setOf_eq.mpr (by
        show ({vv (i + 1), vv i} : Set V3) ∈ E
        rw [pairSetCommFb]
        exact edgeMemFb hE i)

/-- dart 集两分。 -/
private theorem fddartsEqFb (hV : Set.image vv Set.univ = V)
    (hne : ∀ j, vv j ≠ vv (j + 1))
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E) :
    dartsOfHyp_p3 E V
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
        ∪ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  simp only [dartsOfHyp_p3, fdselfPairsEmptyFb hV hE, Set.union_empty,
    fdordPairsFb hne hE]

/-- dart 两分到朝向。 -/
private theorem fddartCasesFb (hV : Set.image vv Set.univ = V)
    (hne : ∀ j, vv j ≠ vv (j + 1))
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) :
    (∃ m : ℕ, x = (vv m, vv (m + 1))) ∨ (∃ m : ℕ, x = (vv (m + 1), vv m)) := by
  have hord := dartInvFb (fun z hz => vvmemFb hV hz) (edgeMemFb hE) hne hx
  rw [← hE, Set.mem_image] at hord
  obtain ⟨j, -, hj'⟩ := hord
  have hjeq : ({x.1, x.2} : Set V3) = {vv j, vv (j + 1)} := hj'.symm
  rcases dartOrientFb (hne j) hjeq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨j, Prod.ext h1 h2⟩
  · exact Or.inr ⟨j, Prod.ext h1 h2⟩

/-- 周期族的「下标平移一」像不变。 -/
private theorem fdimageShiftFb {F : ℕ → V3 × V3} (hk0 : 0 < k) (hper : Periodic F k) :
    Set.image (fun i : ℕ => F (i + 1)) Set.univ = Set.image F Set.univ := by
  ext z
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + 1, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i + k - 1, ?_⟩
    show F ((i + k - 1) + 1) = F i
    rw [show (i + k - 1) + 1 = i + k from by omega, hper]

end FanDartLayer


/-! ## F3 支撑层 C2：轨道集 / nn 像 / 卡片 / 全局对合（localFan_p3 主装配前置） -/

section FanOrbitLayer

variable {vv : ℕ → V3} {k : ℕ} {V : Set V3} {E : Set (Set V3)}

/-- 周期族的 forward 像有限。 -/
private theorem foimgFiniteFb (hk0 : 0 < k) (hper : Periodic vv k) :
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.univ.image
    (fun i : Fin k => (vv (i : ℕ), vv ((i : ℕ) + 1))))) ?_
  rintro x ⟨i, -, rfl⟩
  refine Finset.mem_image.mpr ⟨⟨i % k, Nat.mod_lt _ hk0⟩, Finset.mem_univ _, ?_⟩
  show (vv (i % k), vv (i % k + 1)) = (vv i, vv (i + 1))
  rw [periodicModFb hper i, vvModEqFb hper
    (modSuccFb (Nat.mod_mod_of_dvd i (dvd_refl k)))]

/-- backward 像基数 = k（forward 形参数化）。 -/
private theorem fdbwdCardFb (hk0 : 0 < k) (hper : Periodic vv k)
    (hinjv : ∀ i j, vv i = vv j → i % k = j % k)
    (F : ℕ → V3 × V3) (hF : ∀ t, F t = (vv t, vv (t + 1))) :
    (Set.image F Set.univ).ncard = k := by
  have hperF : Periodic F k := by
    intro t
    rw [hF t, hF (t + k), hper t,
      show (t:Nat) + k + 1 = t + 1 + k from by omega, hper (t + 1)]
  have hfin : (Set.image F Set.univ).Finite := by
    have h0 : Set.image F Set.univ
        = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ :=
      imageUnivCongrFb (fun i => by rw [hF i])
    rw [h0]
    exact foimgFiniteFb hk0 hper
  have hcoeeq : Set.image F Set.univ
      = ((Finset.univ.image (fun i : Fin k => F (i : ℕ))) : Set (V3 × V3)) := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i % k, Nat.mod_lt _ hk0⟩, Finset.mem_univ _, by
        show F (i % k) = F i
        rw [periodicModFb hperF i]⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  have hSfin : ((Finset.univ.image (fun i : Fin k => F (i : ℕ))) : Set (V3 × V3)).Finite := by
    rw [← hcoeeq]
    exact hfin
  have hinj : Function.Injective (fun i : Fin k => F (i : ℕ)) := by
    intro i j hij
    have hF1 : (F ↑i).1 = vv ↑i := by rw [hF ↑i]
    have hF2 : (F ↑j).1 = vv ↑j := by rw [hF ↑j]
    have h1 : vv ↑i = vv ↑j := by
      rw [← hF1, ← hF2]
      exact congrArg Prod.fst hij
    have hik : (i : ℕ) % k = (j : ℕ) % k := hinjv _ _ h1
    rw [Fin.ext ((Nat.mod_eq_of_lt i.isLt).symm.trans
      (hik.trans (Nat.mod_eq_of_lt j.isLt)))]
  have hT : hSfin.toFinset = Finset.univ.image (fun i : Fin k => F (i : ℕ)) := by
    ext x
    simp only [Set.Finite.mem_toFinset hSfin, Finset.mem_coe, Finset.mem_image, Set.mem_univ,
      true_and, exists_prop]
  rw [hcoeeq, Set.ncard_eq_toFinset_card _ hSfin, hT,
    Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ, Fintype.card_fin]

/-- forward ∩ backward = ∅。 -/
private theorem fddisjFb (hk3 : 3 ≤ k) (hper : Periodic vv k)
    (hinjv : ∀ i j, vv i = vv j → i % k = j % k) :
    Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ
      ∩ Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  rw [Set.mem_inter_iff, Set.mem_image, Set.mem_image] at hp
  obtain ⟨⟨i, -, hi⟩, ⟨j, -, hj⟩⟩ := hp
  have hpe : (vv i, vv (i + 1)) = (vv (j + 1), vv j) := hi.trans hj.symm
  have h1 : i % k = (j + 1) % k := hinjv i (j + 1) (congrArg Prod.fst hpe)
  have h2 : (i + 1) % k = j % k := hinjv (i + 1) j (congrArg Prod.snd hpe)
  have hj2 : (j + 1 + 1) % k = j % k := by
    rw [← modSuccFb h1, h2]
  exact modNeAddltFb (a := j) (c := 2) (by omega) (by omega) (by omega) hj2.symm

/-- 像 c 平移（c := k - 1 特化）：F 周期 k 时 +（k-1） 平移像不变。 -/
private theorem fdimageShiftK1Fb {F : ℕ → V3 × V3} (hk1 : 1 ≤ k) (hperF : Periodic F k) :
    Set.image (fun i : ℕ => F (i + (k - 1))) Set.univ = Set.image F Set.univ := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + (k - 1), rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i + 1, ?_⟩
    show F (i + 1 + (k - 1)) = F i
    rw [show (i:Nat) + 1 + (k - 1) = i + k from by omega]
    exact hperF i

/-- 周期族的 forward 像基数 = k。 -/
private theorem fdfwdCardFb (hk0 : 0 < k) (hper : Periodic vv k)
    (hinjv : ∀ i j, vv i = vv j → i % k = j % k) :
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).ncard = k :=
  fdbwdCardFb hk0 hper hinjv (fun i => (vv i, vv (i + 1))) (fun _ => rfl)

/-- backward 像基数 = k。 -/
private theorem fdbwdNcardFb (hk0 : 0 < k) (hper : Periodic vv k)
    (hinjv : ∀ i j, vv i = vv j → i % k = j % k) :
    (Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ).ncard = k := by
  have hfin : (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).Finite :=
    foimgFiniteFb hk0 hper
  have hs : Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ
      = Prod.swap '' (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rw [← Set.image_comp, imageUnivCongrFb (f := Prod.swap ∘ fun i : ℕ => (vv i, vv (i + 1))) (g := fun i : ℕ => (vv (i + 1), vv i)) (fun i : ℕ => by show Prod.swap (vv i, vv (i + 1)) = (vv (i + 1), vv i); rfl)]
  have hswap : Function.Injective (Prod.swap : V3 × V3 → V3 × V3) := by
    intro a b h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  rw [hs, Set.ncard_image_of_injective
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) hswap]
  exact fdfwdCardFb hk0 hper hinjv

/-- nn 像：backward 像 ↦ forward 像。 -/
private theorem fdnnImageBFb (hper : Periodic vv k) (hk0 : 0 < k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hshift2 : ∀ j, vv (j + 2) ≠ vv j) :
    Set.image (nnOfHyp_p3 0 V E) (Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ)
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ := by
  rw [← Set.image_comp, imageUnivCongrFb (f := nnOfHyp_p3 0 V E ∘ fun i : ℕ => (vv (i + 1), vv i))
      (g := fun i : ℕ => (vv (i + 1), vv (i + 2)))
      (fun i : ℕ => by show nnOfHyp_p3 0 V E (vv (i + 1), vv i) = (vv (i + 1), vv (i + 2)); exact fdnnValBFb hper hk1 hE hEE hshift2 i)]
  exact fdimageShiftFb hk0
    (F := fun i : ℕ => (vv i, vv (i + 1)))
    (fun t => by show (vv (t + k), vv (t + k + 1)) = (vv t, vv (t + 1)); rw [hper t, show (t:Nat) + k + 1 = t + 1 + k from by omega, hper (t + 1)])

/-- nn 像：forward 像 ↦ backward 像。 -/
private theorem fdnnImageFFb (hper : Periodic vv k) (hk0 : 0 < k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hne2 : ∀ j, vv (j + 1) ≠ vv (j + k - 1)) :
    Set.image (nnOfHyp_p3 0 V E) (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ)
      = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  have hval : ∀ i : ℕ, (nnOfHyp_p3 0 V E ∘ fun i : ℕ => (vv i, vv (i + 1))) i
      = (vv i, vv (i + (k - 1))) := fun i => fdnnValFFb hper hE hEE hne2 hk1 i
  have hval2 : Set.image (fun i : ℕ => (vv i, vv (i + (k - 1)))) Set.univ
      = Set.image (fun i : ℕ => (vv (i + (k - 1) + 1), vv (i + (k - 1)))) Set.univ := by
    have hG : ∀ i : ℕ, (vv i, vv (i + (k - 1))) = (vv (i + (k - 1) + 1), vv (i + (k - 1))) := by
      intro i
      rw [show (i:Nat) + (k - 1) + 1 = i + k from by omega, hper i]
    rw [imageUnivCongrFb (f := fun i : ℕ => (vv i, vv (i + (k - 1)))) (g := fun i : ℕ => (vv (i + (k - 1) + 1), vv (i + (k - 1)))) hG]
  rw [← Set.image_comp, imageUnivCongrFb (f := nnOfHyp_p3 0 V E ∘ fun i : ℕ => (vv i, vv (i + 1)))
      (g := fun i : ℕ => (vv i, vv (i + (k - 1)))) hval, hval2]
  exact fdimageShiftK1Fb (hk1 := hk1) (F := fun i : ℕ => (vv (i + 1), vv i)) (fun t : ℕ => by show (vv (t + k + 1), vv (t + k)) = (vv (t + 1), vv t); rw [show (t:Nat) + k + 1 = t + 1 + k from by omega, hper (t + 1), hper t])

/-- backward dart 的 ff 轨道集 = backward 像。 -/
private theorem fdorbitBFb (hper : Periodic vv k) (hk0 : 0 < k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hne2 : ∀ j, vv (j + 1) ≠ vv (j + k - 1)) (m : ℕ) :
    {y | ∃ n : ℕ, (ffOfHyp_p3 0 V E)^[n] (vv (m + 1), vv m) = y}
      = Set.image (fun i : ℕ => (vv (i + 1), vv i)) Set.univ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, hn⟩
    rw [fdffIterBFb hper hk1 hE hEE hne2 m n] at hn
    exact ⟨m + n * (k - 1), Set.mem_univ _, hn⟩
  · rintro ⟨i, ⟨-, hi⟩⟩
    refine ⟨i * (k - 1) + m, ?_⟩
    have hb := orbitHitModFb hk0 i m
    rw [fdffIterBFb hper hk1 hE hEE hne2 m (i * (k - 1) + m),
        show m + (i * (k - 1) + m) * (k - 1) + 1 = (i * (k - 1) + m) * (k - 1) + m + 1 from by ring,
        show m + (i * (k - 1) + m) * (k - 1) = (i * (k - 1) + m) * (k - 1) + m from by ring,
        vvModEqFb hper (modSuccFb hb), vvModEqFb hper hb]
    exact hi

/-- forward dart 的 ff 轨道集 = forward 像。 -/
private theorem fdorbitFFb (hper : Periodic vv k) (hk1 : 1 ≤ k)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hEE : ∀ i, ee (vv i) E = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hshift2 : ∀ j, vv (j + 2) ≠ vv j) (m : ℕ) :
    {y | ∃ n : ℕ, (ffOfHyp_p3 0 V E)^[n] (vv m, vv (m + 1)) = y}
      = Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨n, hn⟩
    rw [fdffIterFFb hper hk1 hE hEE hshift2 m n] at hn
    exact ⟨m + n, Set.mem_univ _, hn⟩
  · rintro ⟨i, ⟨-, hi⟩⟩
    refine ⟨m * (k - 1) + i, ?_⟩
    have hmk : (m:Nat) + m * (k - 1) = m * k := by
      have h1 : (1:ℕ) + (k - 1) = k := by omega
      rw [show (m:Nat) * k = m * (1 + (k - 1)) from by rw [h1]]
      have h2 := Nat.mul_add m 1 (k - 1)
      rw [Nat.mul_one] at h2
      exact h2.symm
    have hE1 : (m:Nat) + (m * (k - 1) + i) = i + m * k := by
      rw [← Nat.add_assoc m (m * (k - 1)) i, hmk]; ring
    rw [fdffIterFFb hper hk1 hE hEE hshift2 m (m * (k - 1) + i), hE1,
        vvModEqFb hper (show (i + m * k) % k = i % k from by simp [Nat.add_mod, Nat.mul_mod]),
        vvModEqFb hper (show (i + m * k + 1) % k = (i + 1) % k from by
          simp [Nat.add_mod, Nat.mul_mod])]
    exact hi

end FanOrbitLayer


/-! ## D（fanbase-f3b-w1）：LOCAL_FAN_DUAL_SYM_0 与 CONVEX_LOCAL_FAN_SYM_0 收口

前车道交付的装配 DAG（DELIVERY ③）落地：① FAN 提取（BBsV39 末合取 → hfan）；
② Hypermap 证人（darts Finset + 三张 Perm + comp_eq_one）；③ dih2k_p3 五合取；
④ master `localFan_p3` 装配 + `LOCAL_FAN_DUAL_SYM_0_fb`；⑤ `CONVEX_LOCAL_FAN_SYM_0_fb`
（azim/wedge 内容经 `AZIM_NEG_fb` 对换传输 + `sum4_azim_fan`，绕开 LA3 三处
FAN 门 sorry）。全部新件 private `…Fb` 新名。 -/

section FanMasterLayer

variable {w : ℕ → V3} {k : ℕ} {V' : Set V3} {E' : Set (Set V3)}

/-- 模 k 单射 ⇒ 三条不退化（无自环 / 无跨 k-1 环 / 无 +2 环）。 -/
private theorem fanNeFb (hk3 : 3 ≤ k) (hper : Periodic w k)
    (hinj : ∀ i j, w i = w j → i % k = j % k) :
    (∀ j, w j ≠ w (j + 1)) ∧ (∀ j, w (j + 1) ≠ w (j + k - 1)) ∧ (∀ j, w (j + 2) ≠ w j) := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact modNeSuccFb hk2 (hinj j (j + 1) hj)
  · intro j hcon
    have hm : (j + 1) % k = (j + k - 1) % k := hinj (j + 1) (j + k - 1) hcon
    rw [show (j + k - 1 : ℕ) = (j + 1) + (k - 2) from by omega] at hm
    exact modNeAddltFb hk0 (by omega) (by omega) hm
  · intro j hcon
    have hm : (j + 2) % k = (j + k) % k := hinj (j + 2) (j + k) (hcon.trans (hper j).symm)
    rw [show (j + k : ℕ) = (j + 2) + (k - 2) from by omega] at hm
    exact modNeAddltFb hk0 (by omega) (by omega) hm

/-- 周期族像 = 有限下标像（Finset 像的 coe）。 -/
private theorem coeiImageFb {F : ℕ → V3 × V3} (hk0 : 0 < k) (hperF : Periodic F k) :
    Set.image F Set.univ
      = ((Finset.univ.image (fun i : Fin k => F (i : ℕ))) : Set (V3 × V3)) := by
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i % k, Nat.mod_lt _ hk0⟩, Finset.mem_univ _, by
      show F (i % k) = F i
      rw [periodicModFb hperF i]⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

/-- `f^[n] = id` 逐点（n > 0）⇒ 双射。 -/
private theorem bijOfIterIdFb {α : Type*} {f : α → α} {n : ℕ} (hn : 0 < n)
    (h : ∀ x, f^[n] x = x) :
    Function.Bijective f := by
  cases n with
  | zero => omega
  | succ m =>
    constructor
    · intro a b hab
      have ha : f^[m] (f a) = a := by
        rw [← Function.iterate_succ_apply f m a]
        exact h a
      have hb : f^[m] (f b) = b := by
        rw [← Function.iterate_succ_apply f m b]
        exact h b
      exact ha.symm.trans ((congrArg (f^[m]) hab).trans hb)
    · intro y
      refine ⟨f^[m] y, ?_⟩
      rw [← Function.iterate_succ_apply' f m y]
      exact h y

/-- Hypermap 证人组装：dart 集 + 三个 plain 函数（对合×2 + 双射 ff）+
off-dart 恒等 + 三元复合 ⇒ Hypermap，且各分量逐字等于 plain 函数、face 轨道
= plain iterate 轨道。 -/
private theorem hypermapOfDartsFb (D : Finset (V3 × V3))
    (eeF nnF ffF : V3 × V3 → V3 × V3)
    (hee : ∀ x, eeF (eeF x) = x) (hnn : ∀ x, nnF (nnF x) = x)
    (hbij : Function.Bijective ffF)
    (hoffE : ∀ x ∉ D, eeF x = x) (hoffN : ∀ x ∉ D, nnF x = x) (hoffF : ∀ x ∉ D, ffF x = x)
    (hcomp : ∀ x, eeF (nnF (ffF x)) = x) :
    ∃ H : Hypermap (V3 × V3), H.darts = D ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeF ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnF ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffF ∧
      ∀ d : V3 × V3, H.face d = {y | ∃ n : ℕ, ffF^[n] d = y} := by
  refine ⟨Hypermap.mk D (Equiv.mk eeF eeF hee hee) (Equiv.mk nnF nnF hnn hnn)
      (Equiv.ofBijective ffF hbij) ?_ ?_ ?_ ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro x hx
    show eeF x = x
    exact hoffE x hx
  · intro x hx
    show nnF x = x
    exact hoffN x hx
  · intro x hx
    show ffF x = x
    exact hoffF x hx
  · exact Equiv.ext fun x => by
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact hcomp x
  · intro d
    rw [Hypermap.face]
    simp only [orbitMap, Equiv.Perm.coe_pow]
    rfl

/-- plain 世界全套组合件：darts Finset（coe / 基数 / 覆盖）+ 对合×2 +
ff 的 k 阶 + 三元复合 + off-dart 恒等。 -/
private theorem plainKitFb (hk3 : 3 ≤ k) (hper : Periodic w k)
    (hV : Set.image w Set.univ = V')
    (hE : Set.image (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) Set.univ = E')
    (hEE : ∀ i, ee (w i) E' = ({w (i + 1), w (i + k - 1)} : Set V3))
    (hinj : ∀ i j, w i = w j → i % k = j % k) :
    ∃ D : Finset (V3 × V3),
      (↑D : Set (V3 × V3)) = dartsOfHyp_p3 E' V' ∧ D.card = 2 * k ∧
      (∀ d ∈ D, (↑D : Set (V3 × V3))
          = {y | ∃ n : ℕ, (ffOfHyp_p3 0 V' E')^[n] d = y}
            ∪ (nnOfHyp_p3 0 V' E') '' {y | ∃ n : ℕ, (ffOfHyp_p3 0 V' E')^[n] d = y}) ∧
      (∀ x : V3 × V3, eeOfHyp_p3 0 V' E' (eeOfHyp_p3 0 V' E' x) = x) ∧
      (∀ x : V3 × V3, nnOfHyp_p3 0 V' E' (nnOfHyp_p3 0 V' E' x) = x) ∧
      (∀ x : V3 × V3, (ffOfHyp_p3 0 V' E')^[k] x = x) ∧
      (∀ i : ℕ, 0 < i → i < k → ¬((ffOfHyp_p3 0 V' E')^[i] = id)) ∧
      (∀ x : V3 × V3,
        eeOfHyp_p3 0 V' E' (nnOfHyp_p3 0 V' E' (ffOfHyp_p3 0 V' E' x)) = x) ∧
      hasOrders_p3 (eeOfHyp_p3 0 V' E') 2 ∧
      hasOrders_p3 (nnOfHyp_p3 0 V' E') 2 ∧
      (∀ x ∉ D, eeOfHyp_p3 0 V' E' x = x) ∧
      (∀ x ∉ D, nnOfHyp_p3 0 V' E' x = x) ∧
      (∀ x ∉ D, ffOfHyp_p3 0 V' E' x = x) ∧
      (w (0 + 1), w 0) ∈ D := by
  have hk0 : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hne, hne2, hshift2⟩ := fanNeFb hk3 hper hinj
  have hperF : Periodic (fun i : ℕ => (w i, w (i + 1))) k := by
    intro t
    show (w (t + k), w (t + k + 1)) = (w t, w (t + 1))
    rw [hper t, show (t:Nat) + k + 1 = t + 1 + k from by omega, hper (t + 1)]
  have hperB : Periodic (fun i : ℕ => (w (i + 1), w i)) k := by
    intro t
    show (w (t + k + 1), w (t + k)) = (w (t + 1), w t)
    rw [show (t:Nat) + k + 1 = t + 1 + k from by omega, hper (t + 1), hper t]
  have hswapMem : ∀ x : V3 × V3, x ∈ dartsOfHyp_p3 E' V' →
      ((x.2, x.1) : V3 × V3) ∈ dartsOfHyp_p3 E' V' := by
    intro x hx
    have hself : selfPairs_p3 E' V' = ∅ := fdselfPairsEmptyFb hV hE
    simp only [dartsOfHyp_p3, Set.mem_union] at hx
    rcases hx with h | hs
    · refine Set.mem_union_left _ ?_
      show ({x.2, x.1} : Set V3) ∈ E'
      rw [pairSetCommFb]
      exact h
    · exfalso
      rw [hself] at hs
      exact Set.notMem_empty _ hs
  have heeAll : ∀ x : V3 × V3, eeOfHyp_p3 0 V' E' (eeOfHyp_p3 0 V' E' x) = x := by
    intro x
    by_cases hd : x ∈ dartsOfHyp_p3 E' V'
    · rw [eeMemEqFb hd, eeMemEqFb (hswapMem x hd)]
    · rw [eeNotMemEqFb hd, eeNotMemEqFb hd]
  have hnnAll : ∀ x : V3 × V3, nnOfHyp_p3 0 V' E' (nnOfHyp_p3 0 V' E' x) = x := by
    intro x
    by_cases hd : x ∈ dartsOfHyp_p3 E' V'
    · rcases fddartCasesFb hV hne hE hd with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have h1 : nnOfHyp_p3 0 V' E' (w m, w (m + 1))
            = (w (m + (k - 1) + 1), w (m + (k - 1))) := by
          rw [fdnnValFFb hper hE hEE hne2 hk1 m]
          rw [show (w m : V3) = w (m + (k - 1) + 1) from by
            rw [show (m:Nat) + (k - 1) + 1 = m + k from by omega]; exact (hper m).symm]
        have h2 : nnOfHyp_p3 0 V' E' (w (m + (k - 1) + 1), w (m + (k - 1)))
            = (w m, w (m + 1)) := by
          rw [fdnnValBFb hper hk1 hE hEE hshift2 (m + (k - 1)),
            show ((m:Nat) + (k - 1) + 1) = m + k from by omega, hper m,
            show ((m:Nat) + (k - 1) + 2) = m + 1 + k from by omega, hper (m + 1)]
        rw [h1, h2]
      · have h1 : nnOfHyp_p3 0 V' E' (w (m + 1), w m) = (w (m + 1), w (m + 2)) :=
          fdnnValBFb hper hk1 hE hEE hshift2 m
        have h2 : nnOfHyp_p3 0 V' E' (w (m + 1), w (m + 2)) = (w (m + 1), w m) := by
          rw [fdnnValFFb hper hE hEE hne2 hk1 (m + 1),
            show ((m:Nat) + 1 + (k - 1)) = m + k from by omega, hper m]
        rw [h1, h2]
    · rw [nnNotMemEqFb hd, nnNotMemEqFb hd]
  have hcoeD : (((Finset.univ.image (fun i : Fin k => (w (i + 1), w i))
      ∪ Finset.univ.image (fun i : Fin k => (w i, w (i + 1))) : Finset (V3 × V3)) :
      Set (V3 × V3))) = dartsOfHyp_p3 E' V' := by
    rw [Finset.coe_union, ← coeiImageFb (F := fun i : ℕ => (w (i + 1), w i)) hk0 hperB,
      ← coeiImageFb (F := fun i : ℕ => (w i, w (i + 1))) hk0 hperF,
      fddartsEqFb hV hne hE, Set.union_comm]
  have hcardD : (Finset.univ.image (fun i : Fin k => (w (i + 1), w i))
      ∪ Finset.univ.image (fun i : Fin k => (w i, w (i + 1)))).card = 2 * k := by
    have hdisjF : Disjoint
        (Set.image (fun i : ℕ => (w i, w (i + 1))) Set.univ)
        (Set.image (fun i : ℕ => (w (i + 1), w i)) Set.univ) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact fddisjFb hk3 hper hinj
    have hfinF : (Set.image (fun i : ℕ => (w i, w (i + 1))) Set.univ).Finite := by
      rw [coeiImageFb (F := fun i : ℕ => (w i, w (i + 1))) hk0 hperF]
      exact Finset.finite_toSet _
    have hfinB : (Set.image (fun i : ℕ => (w (i + 1), w i)) Set.univ).Finite := by
      rw [coeiImageFb (F := fun i : ℕ => (w (i + 1), w i)) hk0 hperB]
      exact Finset.finite_toSet _
    have h1 : (((Finset.univ.image (fun i : Fin k => (w (i + 1), w i))
        ∪ Finset.univ.image (fun i : Fin k => (w i, w (i + 1))) : Finset (V3 × V3)) :
        Set (V3 × V3))).ncard = 2 * k := by
      rw [hcoeD, fddartsEqFb hV hne hE, ncard_union_eq hdisjF hfinF hfinB,
        fdfwdCardFb hk0 hper hinj, fdbwdNcardFb hk0 hper hinj]
      ring
    rw [← h1, Set.ncard_coe_finset]
  refine ⟨Finset.univ.image (fun i : Fin k => (w (i + 1), w i))
      ∪ Finset.univ.image (fun i : Fin k => (w i, w (i + 1))), hcoeD, hcardD, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hdmem
    simp only [Finset.mem_union, Finset.mem_image] at hdmem
    rcases hdmem with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩)
    · rw [fdorbitBFb hper hk0 hk1 hE hEE hne2 (i : ℕ),
        fdnnImageBFb hper hk0 hk1 hE hEE hshift2, hcoeD, fddartsEqFb hV hne hE,
        Set.union_comm]
    · rw [fdorbitFFb hper hk1 hE hEE hshift2 (i : ℕ), fdnnImageFFb hper hk0 hk1 hE hEE hne2,
        hcoeD, fddartsEqFb hV hne hE]
  · exact heeAll
  exact hnnAll
  · intro x
    by_cases hd : x ∈ dartsOfHyp_p3 E' V'
    · rcases fddartCasesFb hV hne hE hd with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [fdffIterFFb hper hk1 hE hEE hshift2 m k, hper m,
          show (m:Nat) + k + 1 = m + 1 + k from by omega, hper (m + 1)]
      · rw [fdffIterBFb hper hk1 hE hEE hne2 m k]
        have hmul : ((m:Nat) + k * (k - 1)) % k = m % k := by
          rw [Nat.add_mul_mod_self_left]
        rw [vvModEqFb hper (modSuccFb hmul), vvModEqFb hper hmul]
    · exact Function.iterate_fixed (ffNotMemEqFb hd) k
  · intro i hi0 hik hid
    have h1 := congrFun hid (w 0, w 1)
    rw [fdffIterFFb hper hk1 hE hEE hshift2 0 i] at h1
    have h2 : i % k = 0 % k := hinj i 0 (by simpa using congrArg Prod.fst h1)
    rw [Nat.mod_eq_of_lt hik, Nat.zero_mod] at h2
    omega
  · intro x
    by_cases hd : x ∈ dartsOfHyp_p3 E' V'
    · rcases fddartCasesFb hV hne hE hd with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have h1 : ffOfHyp_p3 0 V' E' (w m, w (m + 1)) = (w (m + 1), w (m + 2)) :=
          fdffValFFb hper hk1 hE hEE hshift2 m
        have h2 : nnOfHyp_p3 0 V' E' (w (m + 1), w (m + 2)) = (w (m + 1), w m) := by
          rw [fdnnValFFb hper hE hEE hne2 hk1 (m + 1),
            show ((m:Nat) + 1 + (k - 1)) = m + k from by omega, hper m]
        have h3 : eeOfHyp_p3 0 V' E' (w (m + 1), w m) = (w m, w (m + 1)) :=
          eeMemEqFb (ordMemDartsFb (vv := w)
            (by rw [pairSetCommFb]; exact edgeMemFb hE m))
        rw [h1, h2, h3]
      · have h1 : ffOfHyp_p3 0 V' E' (w (m + 1), w m)
            = (w (m + (k - 1) + 1), w (m + (k - 1))) :=
          fdffValBFb hper hk1 hE hEE hne2 m
        have h2 : nnOfHyp_p3 0 V' E' (w (m + (k - 1) + 1), w (m + (k - 1)))
            = (w m, w (m + 1)) := by
          rw [fdnnValBFb hper hk1 hE hEE hshift2 (m + (k - 1)),
            show ((m:Nat) + (k - 1) + 1) = m + k from by omega, hper m,
            show ((m:Nat) + (k - 1) + 2) = m + 1 + k from by omega, hper (m + 1)]
        have h3 : eeOfHyp_p3 0 V' E' (w m, w (m + 1)) = (w (m + 1), w m) :=
          eeMemEqFb (ordMemDartsFb (vv := w) (edgeMemFb hE m))
        rw [h1, h2, h3]
    · rw [ffNotMemEqFb hd, nnNotMemEqFb hd, eeNotMemEqFb hd]
  · have heeOrd : hasOrders_p3 (eeOfHyp_p3 0 V' E') 2 := by
      constructor
      · intro i hi0 _hik hid
        have hi1 : i = 1 := by omega
        subst hi1
        have h1 : eeOfHyp_p3 0 V' E' (w 0, w 1) = (w 0, w 1) := congrFun hid (w 0, w 1)
        rw [eeMemEqFb (ordMemDartsFb (vv := w) (edgeMemFb hE 0))] at h1
        exact hne 0 (congrArg Prod.fst h1.symm)
      · funext x
        show eeOfHyp_p3 0 V' E' (eeOfHyp_p3 0 V' E' x) = x
        exact heeAll x
    exact heeOrd
  · have hnnOrd : hasOrders_p3 (nnOfHyp_p3 0 V' E') 2 := by
      constructor
      · intro i hi0 _hik hid
        have hi1 : i = 1 := by omega
        subst hi1
        have h1 : nnOfHyp_p3 0 V' E' (w 0, w 1) = (w 0, w 1) := congrFun hid (w 0, w 1)
        rw [fdnnValFFb hper hE hEE hne2 hk1 0] at h1
        have h2 : w 1 = w (k - 1) := by
          have hc2 := congrArg Prod.snd h1.symm
          rw [Nat.zero_add] at hc2
          exact hc2
        have h3 : w (0 + 1) = w (0 + k - 1) := by
          rw [show ((0:Nat) + 1) = 1 from by simp, show ((0:Nat) + k) = k from by simp]
          exact h2
        exact hne2 0 h3
      · funext x
        show nnOfHyp_p3 0 V' E' (nnOfHyp_p3 0 V' E' x) = x
        exact hnnAll x
    exact hnnOrd
  · intro x hx
    rw [eeNotMemEqFb (fun hc => hx (by rw [← hcoeD] at hc; exact hc))]
  · intro x hx
    rw [nnNotMemEqFb (fun hc => hx (by rw [← hcoeD] at hc; exact hc))]
  · intro x hx
    rw [ffNotMemEqFb (fun hc => hx (by rw [← hcoeD] at hc; exact hc))]
  refine Finset.mem_union_left
    (t := Finset.univ.image (fun i : Fin k => (w i, w (i + 1)))) ?_
  exact Finset.mem_image.mpr ⟨⟨0, hk0⟩, Finset.mem_univ _, rfl⟩

/-- master：七槽像形 + 周期 + 模 k 单射 + FAN ⇒ `localFan_p3`（backward 像为
face 轨道）。LA3 `HYP_LEMMA`/`ELMS_OF_HYPERMAP_HYP`（sorry 门）的自建绕法。 -/
private theorem localFanMasterFb (hk3 : 3 ≤ k) (hper : Periodic w k)
    (hV : Set.image w Set.univ = V')
    (hE : Set.image (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) Set.univ = E')
    (hEE : ∀ i, ee (w i) E' = ({w (i + 1), w (i + k - 1)} : Set V3))
    (hinj : ∀ i j, w i = w j → i % k = j % k)
    (hfan : Fan.FAN 0 V' E') :
    localFan_p3 V' E' (Set.image (fun i : ℕ => (w (i + 1), w i)) Set.univ) := by
  have hk0 : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hne, hne2, hshift2⟩ := fanNeFb hk3 hper hinj
  obtain ⟨D, hcoeD, hcardD, hcov, heeInv, hnnInv, hffIterId, hffNotId, hcomp,
    heeOrd, hnnOrd, hoffE, hoffN, hoffF, hmemD0⟩ := plainKitFb hk3 hper hV hE hEE hinj
  obtain ⟨H, hHd, hHe, hHn, hHf, hHF⟩ :=
    hypermapOfDartsFb D (eeOfHyp_p3 0 V' E') (nnOfHyp_p3 0 V' E') (ffOfHyp_p3 0 V' E')
      heeInv hnnInv (bijOfIterIdFb hk0 hffIterId) hoffE hoffN hoffF hcomp
  refine ⟨H, ?_, hHe, hHn, hHf, hfan, ?_, ?_⟩
  · rw [hHd]
    exact hcoeD
  · refine ⟨(w (0 + 1), w 0), ?_, ?_⟩
    · rw [hHd]
      exact hmemD0
    · rw [hHF (w (0 + 1), w 0), fdorbitBFb hper hk0 hk1 hE hEE hne2 0]
  · rw [fdbwdNcardFb hk0 hper hinj]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hHd, hcardD]
    · intro d hdmem
      rw [hHd] at hdmem ⊢
      rw [hHF d, hHn]
      exact hcov d hdmem
    · rw [hHf]
      exact ⟨hffNotId, funext hffIterId⟩
    · rw [hHe]
      exact heeOrd
    · rw [hHn]
      exact hnnOrd

/-- `sigmaFan 0 univ E' (w i) (w (i+1)) = w (i+k-1)`（ε 唯一性；原族 wedge
内容提取用）。 -/
private theorem sigmaFanUnivFb (hk3 : 3 ≤ k) (hper : Periodic w k)
    (hE : Set.image (fun i : ℕ => ({w i, w (i + 1)} : Set V3)) Set.univ = E')
    (hEE : ∀ i, ee (w i) E' = ({w (i + 1), w (i + k - 1)} : Set V3))
    (hne2 : ∀ j, w (j + 1) ≠ w (j + k - 1))
    (hinj : ∀ i j, w i = w j → i % k = j % k)
    (i : ℕ) :
    Fan.sigmaFan 0 Set.univ E' (w i) (w (i + 1)) = w (i + k - 1) := by
  have hsoe : Fan.setOfEdge (w i) Set.univ E' = ({w (i + 1), w (i + k - 1)} : Set V3) := by
    ext z
    simp only [Fan.setOfEdge, Set.mem_setOf_eq, Set.mem_univ, true_and]
    constructor
    · intro h
      have hm : ({w i, z} : Set V3) ∈ E' := h.1
      rw [← hE, Set.mem_image] at hm
      obtain ⟨j, -, hj⟩ := hm
      rw [pairSetEqFb] at hj
      rcases hj with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        show z = w (i + 1)
        rw [← h2]
        exact vvModEqFb hper (modSuccFb (hinj j i h1))
      · right
        show z = w (i + k - 1)
        rw [← h1, show ((i:Nat) + k - 1) = i + (k - 1) from by omega]
        exact vvModEqFb hper (modPredFb (by omega) (hinj (j + 1) i h2))
    · intro h
      rcases Set.mem_insert_iff.mp h with hz | hz
      · rw [hz]
        refine ⟨?_, trivial⟩
        rw [← hE]
        exact ⟨i, Set.mem_univ _, rfl⟩
      · rw [Set.mem_singleton_iff.mp hz]
        refine ⟨?_, trivial⟩
        rw [← hE, Set.mem_image]
        refine ⟨i + k - 1, Set.mem_univ _, ?_⟩
        rw [pairSetCommFb, show ((i:Nat) + k - 1 + 1) = i + k from by omega, hper i]
  have hne1 : Fan.setOfEdge (w i) Set.univ E' ≠ ({w (i + 1)} : Set V3) := by
    intro hc
    rw [hsoe] at hc
    have hm : w (i + k - 1) ∈ ({w (i + 1)} : Set V3) := by
      rw [← hc]
      exact Set.mem_insert_iff.mpr (Or.inr rfl)
    exact hne2 i (Set.mem_singleton_iff.mp hm).symm
  rw [Fan.sigmaFan, if_neg hne1]
  refine epsFixedFb ?_ ?_
  · refine ⟨?_, (hne2 i).symm, ?_⟩
    · rw [hsoe]
      exact Set.mem_insert_iff.mpr (Or.inr rfl)
    · intro u hu1 hu2
      rw [hsoe] at hu1
      rcases Set.mem_insert_iff.mp hu1 with hu | hu
      · exact absurd hu hu2
      · rw [hu]
  · intro y hy
    rw [hsoe] at hy
    rcases Set.mem_insert_iff.mp hy.1 with hy1 | hy1
    · exact absurd hy1 hy.2.1
    · exact hy1

end FanMasterLayer

/-- HOL `LOCAL_FAN_DUAL_SYM_0`（YXIONXL2.hl:1558-1882）；LA13 孪生
`localFanP13`（LA13-f0b 草案 :2343，True 占位，不可沿袭）。目标谓词 = LA3
canonical `localFan_p3`；三槽 = HOL 重指标形，经 `oppImageV/E/FEq2NegFb`
改写为平取负像形后套 master。 -/
theorem LOCAL_FAN_DUAL_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    localFan_p3
      (Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ)
      (Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ) := by
  have hconv : ConvexLocalFan (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rcases hbb.2.2.2 with h3 | hcf
    · exact absurd (by rw [hk] at h3; exact h3) hk3
    · simpa only [Set.image_univ] using hcf
  obtain ⟨hlf0, -⟩ := hconv
  obtain ⟨hfan0, -, -⟩ := hlf0
  have hctx := fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hper0 : Periodic vv k := hctx.2.2.1
  have hperN : Periodic (fun i : ℕ => -(vv i)) k := fun t => by simpa using hper0 t
  have hinjN : ∀ i j, -(vv i) = -(vv j) → i % k = j % k := by
    intro i j hc
    exact vvInjModFb hk (by omega) hctx.1 hctx.2.1 hper0 (by simpa using congrArg Neg.neg hc)
  rw [oppImageVEqNegFb vv hper0 (by omega), oppImageEEqNegFb vv hper0 (by omega),
    oppImageFEq2NegFb vv hper0 (by omega)]
  refine localFanMasterFb (by omega) hperN rfl rfl hctx.2.2.2.2.1 hinjN ?_
  exact fanNegCoreFb vv hfan0

/-- HOL `CONVEX_LOCAL_FAN_SYM_0`（YXIONXL2.hl:2029-2182）；LA13 孪生 :2357。
azim ≤ π 与 V ⊆ wedge 经 `AZIM_NEG_fb` 对换传输到原族 forward dart 的
ConvexLocalFan 内容 (A)/(B)（sigmaFan 值由 `sigmaFanUnivFb` 收口）；wedge
上界由 (B) 上界 + `sum4_azim_fan` 收口；共线简并分支由 `azim` 定义的 0
分支收口。 -/
theorem CONVEX_LOCAL_FAN_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3))
    (hk : s.k = k) (hV : Set.image vv Set.univ = V)
    (hE : Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ = E)
    (hFF : Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ = FF)
    (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    convexLocalFan_p3
      (Set.image (fun i : ℕ => -(vv (k - (i % k + 1)))) Set.univ)
      (Set.image (fun i : ℕ =>
        ({-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1)))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ =>
        (-(vv (k - (i % k + 1))), -(vv (k - ((i + 1) % k + 1))))) Set.univ) := by
  have hconv : ConvexLocalFan (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rcases hbb.2.2.2 with h3 | hcf
    · exact absurd (by rw [hk] at h3; exact h3) hk3
    · simpa only [Set.image_univ] using hcf
  obtain ⟨hlf0, hpts⟩ := hconv
  obtain ⟨hfan0, -, -⟩ := hlf0
  have hctx := fanbaseCtxFb s vv k V E FF hk hV hE hFF hiscs hk3 hbb
  have hper0 : Periodic vv k := hctx.2.2.1
  have hperN : Periodic (fun i : ℕ => -(vv i)) k := fun t => by simpa using hper0 t
  have hne0 : ∀ j, vv j ≠ 0 := by
    intro j hc
    exact hfan0.2.2.2.1 ⟨j, Set.mem_univ _, hc⟩
  have hsig : ∀ i : ℕ, Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1)) = vv (i + k - 1) :=
    fun i => sigmaFanUnivFb (by omega) hper0 hE hctx.2.2.2.1 hctx.2.2.2.2.2.2.1
      (fun i j hc => vvInjModFb hk (by omega) hctx.1 hctx.2.1 hper0 hc) i
  -- 原族 ConvexLocalFan 的方位内容：(A_i) azim ≤ π；(B_i) wedge 覆盖
  have hAB : ∀ i : ℕ,
      azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi ∧
      ∀ z : V3, z ∈ V → 0 ≤ azim 0 (vv i) (vv (i + 1)) z ∧
        azim 0 (vv i) (vv (i + 1)) z ≤ azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
    intro i
    have hdart : (vv i, vv (i + 1)) ∈ Set.image (fun j : ℕ => (vv j, vv (j + 1))) Set.univ :=
      ⟨i, Set.mem_univ _, rfl⟩
    obtain ⟨hA, hB⟩ := hpts (vv i, vv (i + 1)) hdart
    rw [hE] at hA
    rw [hE, hV] at hB
    have hcard : 1 < (ee (vv i) E).ncard := by
      rw [hctx.2.2.2.1 i, Set.ncard_pair (hctx.2.2.2.2.2.2.1 i)]
      norm_num
    constructor
    · have hA' : azim 0 (vv i) (vv (i + 1))
          (Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1))) ≤ Real.pi := by
        have h1 : azimInFan (vv i, vv (i + 1)) E
            = azim 0 (vv i) (vv (i + 1))
              (Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1))) := by
          simp only [azimInFan, if_pos hcard]
        rw [h1] at hA
        exact hA
      rwa [hsig i] at hA'
    · have hB' : V ⊆ wedgeGe 0 (vv i) (vv (i + 1))
          (Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1))) := by
        have h1 : wedgeInFanGe (vv i, vv (i + 1)) E
            = wedgeGe 0 (vv i) (vv (i + 1))
              (Fan.sigmaFan 0 Set.univ E (vv i) (vv (i + 1))) := by
          simp only [wedgeInFanGe, if_pos hcard]
        rw [h1] at hB
        exact hB
      intro z hz
      have hBm : z ∈ wedgeGe 0 (vv i) (vv (i + 1))
          (Fan.sigmaFan 0 univ E (vv i) (vv (i + 1))) := hB' hz
      simp only [wedgeGe, Set.mem_setOf_eq] at hBm
      rw [hsig i] at hBm
      exact hBm
  rw [convexLocalFan_p3]
  refine ⟨LOCAL_FAN_DUAL_SYM_0_fb s vv k V E FF hk hV hE hFF hiscs hk3 hbb, ?_⟩
  rw [oppImageVEqNegFb vv hper0 (by omega), oppImageEEqNegFb vv hper0 (by omega),
    oppImageFEq2NegFb vv hper0 (by omega)]
  rintro x ⟨j, -, rfl⟩
  -- fan6 给出的两条不共线（边 {vv j, vv (j+1)} / {vv (j+1), vv (j+2)}）
  have hcol1 : ¬Collinear ℝ ({0, vv (j + 1), vv j} : Set V3) := by
    have h := hfan0.2.2.2.2.1 ({vv j, vv (j + 1)} : Set V3) ⟨j, Set.mem_univ _, rfl⟩
    show ¬Collinear ℝ (insert 0 (insert (vv (j + 1)) ({vv j} : Set V3)))
    rw [pairSetCommFb]
    exact h
  have hcol2 : ¬Collinear ℝ ({0, vv (j + 1), vv (j + 2)} : Set V3) :=
    hfan0.2.2.2.2.1 ({vv (j + 1), vv (j + 2)} : Set V3) ⟨j + 1, Set.mem_univ _, rfl⟩
  have hne2j : -(vv (j + 2)) ≠ -(vv j) := by
    intro hc
    have hc2 : vv (j + 2) = vv j := by simpa using congrArg Neg.neg hc
    exact hctx.2.2.2.2.2.2.2 j (hc2.trans (hper0 j).symm)
  have hneigh : ee (-(vv (j + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      = ({-(vv (j + 2)), -(vv j)} : Set V3) := by
    have h := hctx.2.2.2.2.1 (j + 1)
    rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
      show (-(vv (j + k)) : V3) = -(vv j) from by
        simpa using congrArg Neg.neg (hper0 j)] at h
    exact h
  have hcardN : 1 < (EE_p3 (-(vv (j + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)).ncard := by
    show 1 < (ee (-(vv (j + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)).ncard
    rw [hneigh, Set.ncard_pair hne2j]
    norm_num
  have hcyc : azimCycle_p3 (EE_p3 (-(vv (j + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
        0 (-(vv (j + 1))) (-(vv j))
      = -(vv (j + 2)) := by
    show azimCycle_p3 (ee (-(vv (j + 1)))
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ))
      0 (-(vv (j + 1))) (-(vv j)) = -(vv (j + 2))
    rw [hneigh, azimCycleTwoSwapFb hne2j]
  constructor
  · -- azimInFan_p3 x E'' ≤ π：对换传输 = (A_{j+1})
    have hA := (hAB (j + 1)).1
    rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
      show (vv (j + k) : V3) = vv j from hper0 j] at hA
    simp only [azimInFan_p3]
    rw [if_pos hcardN, hcyc, AZIM_NEG_fb hcol1 hcol2]
    exact hA
  · -- V'' ⊆ wedgeInFanGe_p3 x E''：下界 azim_nonneg；上界对换传输 + sum4
    simp only [wedgeInFanGe_p3]
    rw [if_pos hcardN, hcyc]
    rintro z ⟨i, -, rfl⟩
    simp only [wedgeGe_p3, Set.mem_setOf_eq]
    refine ⟨azim_nonneg 0 (-(vv (j + 1))) (-(vv j)) (-(vv i)), ?_⟩
    by_cases hcol : Collinear ℝ ({0, vv (j + 1), vv i} : Set V3)
    · have hdeg : azim 0 (-(vv (j + 1))) (-(vv j)) (-(vv i)) = 0 := by
        have hc : Collinear3 0 (-(vv (j + 1))) (-(vv i)) := collinear3_zero_negFb.mp hcol
        unfold azim
        exact if_pos (Or.inr hc)
      rw [hdeg, AZIM_NEG_fb hcol1 hcol2]
      exact azim_nonneg 0 (vv (j + 1)) (vv (j + 2)) (vv j)
    · rw [AZIM_NEG_fb hcol1 hcol, AZIM_NEG_fb hcol1 hcol2]
      have hB := (hAB (j + 1)).2 (vv i) (by rw [← hV]; exact ⟨i, Set.mem_univ _, rfl⟩)
      rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
        show (vv (j + k) : V3) = vv j from hper0 j] at hB
      have hsum := sum4_azim_fan (x := 0) (v := vv (j + 1)) (u := vv (j + 2))
        (w1 := vv i) (w2 := vv j) (hne0 (j + 1)) hcol2 hcol hcol1 hB.2
      rw [hsum]
      linarith [azim_nonneg 0 (vv (j + 1)) (vv (j + 2)) (vv i)]
/-! ## S 链首波三件（fanbase-s1-w1）：`SCS_OPP_REFL_fb` + `DSV_EQ_SYM_0_fb` +
`PEROPP_IN_BB_SYM_0_fb`

ScsV39 世界的 scs_opp 对偶链首波。HOL 锚（YXIONXL2.hl）：`SCS_OPP_REFL` :3095、
`DSV_EQ_SYM_0` :2236、`PEROPP_IN_BB_SYM_0` :2183；LA13 P13 孪生 =
LA13_f0b 草案 :2396 / :2378 / :2372（`ScsV39P13→ScsV39`、`peroppP13→peropp`
（LA1 canonical def）、`dsvV39P13→dsvV39` 逐槽改型）。

- `SCS_OPP_REFL_fb`：链首新小件，全库缺失。路线 = HOL 同型：peropp/peropp2
  对合（DUAL_PEROPP/DUAL_PEROPP2 孪生，吃 `oppSucModFb` + 周期传输），k ≠ 0
  由 isScsV39 的 3 ≤ k 收口。
- `DSV_EQ_SYM_0_fb`：HOL SUM_EQ_GENERAL 重指标和的 Lean 形 = Finset 和经对合
  重指标 `dsvReidxFb`（`i ↦ ((k-1-i)+k-1) % k`，[0,k) 对合）的
  `Finset.sum_nbij`；J 条件双向传输只吃 isScsV39 的 J 对称 + Periodic2；
  距离端吃 `distNegNegFb` + dist 对换 + Periodic vv k；isEar 两侧皆假
  （k ≥ 4，NO_IS_EAR/NO_IS_EAR_SCS_OPP 同型）。
- `PEROPP_IN_BB_SYM_0_fb`：BBsV39 四合取逐条——前三条纯记录（ballAnnulus
  取负对称、Periodic、peropp2 槽 dist 界）；第四条 = LA1 `ConvexLocalFan`
  （BBsV39 的 fan 槽是 LA1 canonical 形，非 LA3 `_p3` 形）于取负族：
  LocalFan 部分经 `localFanLA1ofP3Fb`（AzimBridge `LocalFan.of_localFan_p3`
  的 kit 内私有重铸；hno 前提由负族无孤立点收口）消费本 kit 的
  `LOCAL_FAN_DUAL_SYM_0_fb`；azim 部分重走 F3 的 (A)/(B) 对换传输
  （`AZIM_NEG_fb` + `sum4_azim_fan`），wedge/azimInFan 槽在 LA1 `Fan.sigmaFan`
  渲染下由 `sigmaFanUnivFb` + `sigmaFanTwoFb` 收口。三槽经
  `oppImageV/E/FEq2NegFb` 改写为平取负像形。

新增 helper 全部 private `…Fb` 新名；既有件签名逐字不动。 -/

section SOppChain

-- 本节 helper 需要 dart1OfFan/dartsOfHyp_p3 隶属的古典可判定（fan 层 def 的
-- if 形）；仅 local 作用域，不改文件既有 setup。
attribute [local instance] Classical.propDecidable

/-! ### S.1 peropp 对合算术（HOL DUAL_PEROPP / DUAL_PEROPP2，LA13 :1447/:1470 孪生） -/

/-- 2 元周期的整倍数传输（LA13 `periodicAdd2P13` 孪生）。 -/
private theorem periodicAdd2Fb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) : ∀ q i j, a (i + q * k) j = a i j ∧ a i (j + q * k) = a i j := by
  intro q
  induction q with
  | zero => intro i j; simp
  | succ n ih =>
      intro i j
      have hsplit : i + Nat.succ n * k = i + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      have hsplitJ : j + Nat.succ n * k = j + n * k + k := by
        rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (n * k) k]
      rw [hsplit, hsplitJ]
      exact ⟨(hper (i + n * k) j).1.trans (ih i j).1,
        (hper i (j + n * k)).2.trans (ih i j).2⟩

/-- 2 元周期的取模传输。 -/
private theorem periodicMod2Fb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) (i j : ℕ) : a i (j % k) = a i j := by
  have h := (periodicAdd2Fb hper (j / k) i (j % k)).2
  rw [Nat.mul_comm, Nat.mod_add_div] at h
  exact h.symm

/-- HOL `DUAL_PEROPP`（YXIONXL2.hl:3084）。 -/
private theorem peroppDualFb {α : Sort*} {a : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic a k) : peropp (peropp a k) k = a := by
  funext i
  show a (k - ((k - (i % k + 1)) % k + 1)) = a i
  rw [oppSucModFb hk]
  exact periodicModFb hper i

/-- HOL `DUAL_PEROPP2`（YXIONXL2.hl:3089）。 -/
private theorem peropp2DualFb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hper : Periodic2 a k) : peropp2 (peropp2 a k) k = a := by
  funext i j
  show a (k - ((k - (i % k + 1)) % k + 1)) (k - ((k - (j % k + 1)) % k + 1)) = a i j
  rw [oppSucModFb hk, oppSucModFb hk]
  have hA : a (i % k) (j % k) = a i (j % k) := by
    have h := (periodicAdd2Fb hper (i / k) (i % k) (j % k)).1.symm
    rw [Nat.mul_comm, Nat.mod_add_div i k] at h
    exact h
  rw [hA, periodicMod2Fb hper i j]

/-- `ballAnnulus` 取负对称（HOL `BALL_ANNULUS_SYM_0` 点态形）。 -/
private theorem ballAnnulusNegFb (x : V3) (h : x ∈ ballAnnulus) : -x ∈ ballAnnulus := by
  have hd : dist (-x) (0:V3) = dist x (0:V3) := by simp [dist_eq_norm]
  obtain ⟨hm, hn⟩ := h
  refine ⟨Metric.mem_closedBall.mpr ?_, ?_⟩
  · rw [hd]
    exact Metric.mem_closedBall.mp hm
  · intro hc
    have hc' : dist (-x) (0:V3) < 2 := hc
    rw [hd] at hc'
    exact hn (show x ∈ Metric.ball (0:V3) 2 from hc')

/-- HOL `SCS_OPP_REFL`（YXIONXL2.hl:3095；LA13 孪生 `SCS_OPP_REFL_p13`
= LA13_f0b:2396）。`scs_opp_v39` 对合：逐字段 DUAL_PEROPP/2。 -/
theorem SCS_OPP_REFL_fb (s : ScsV39) (hiscs : isScsV39 s) :
    scsOppV39 (scsOppV39 s) = s := by
  cases s with
  | mk k d a am bm b J lo hi str =>
    obtain ⟨-, hk3, -, hlo, hhi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, -, -, -, -, -, -, -, -, -⟩ :=
      hiscs
    have hk3' : 3 ≤ k := hk3
    have hk0 : k ≠ 0 := by omega
    show ScsV39.mk k d (peropp2 (peropp2 a k) k) (peropp2 (peropp2 am k) k)
      (peropp2 (peropp2 bm k) k) (peropp2 (peropp2 b k) k) (peropp2 (peropp2 J k) k)
      (peropp (peropp lo k) k) (peropp (peropp hi k) k) (peropp (peropp str k) k)
      = ScsV39.mk k d a am bm b J lo hi str
    rw [ScsV39.mk.injEq k d (peropp2 (peropp2 a k) k) (peropp2 (peropp2 am k) k)
      (peropp2 (peropp2 bm k) k) (peropp2 (peropp2 b k) k) (peropp2 (peropp2 J k) k)
      (peropp (peropp lo k) k) (peropp (peropp hi k) k) (peropp (peropp str k) k)
      k d a am bm b J lo hi str]
    exact ⟨rfl, rfl, peropp2DualFb hk0 hpa, peropp2DualFb hk0 hpam, peropp2DualFb hk0 hpbm,
      peropp2DualFb hk0 hpb, peropp2DualFb hk0 hpJ, peroppDualFb hk0 hlo,
      peroppDualFb hk0 hhi, peroppDualFb hk0 hstr⟩

/-! ### S.2 DSV 记录件（HOL DSV_EQ_SYM_0 :2236） -/

/-- DSV 重指标对合：`i ↦ ((k-1-i)+(k-1)) % k`，[0,k) 上的对合
（i ≤ k-2 时 = k-2-i；i = k-1 时 = k-1）。职能同 HOL SUM_EQ_GENERAL 的
重指标 `(\j. k - SUC(SUC(j MOD k) MOD k))`。 -/
private def dsvReidxFb (k i : ℕ) : ℕ := ((k - 1 - i) + (k - 1)) % k

private theorem dsvReidxSqFb {k i : ℕ} (hik : i < k) (hik2 : i ≤ k - 2) (hk2 : 2 ≤ k) :
    dsvReidxFb k i = k - 2 - i := by
  unfold dsvReidxFb
  have hsplit : (k - 1 - i) + (k - 1) = (k - 2 - i) + k * 1 := by omega
  rw [hsplit, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

private theorem dsvReidxLastFb {k : ℕ} (hk1 : 1 ≤ k) : dsvReidxFb k (k - 1) = k - 1 := by
  unfold dsvReidxFb
  rw [Nat.sub_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

private theorem dsvReidxLtFb {k i : ℕ} (hik : i < k) (hk2 : 2 ≤ k) : dsvReidxFb k i < k := by
  by_cases hlast : i = k - 1
  · subst hlast
    rw [dsvReidxLastFb (k := k) (by omega)]
    omega
  · rw [dsvReidxSqFb hik (by omega) hk2]
    omega

private theorem dsvReidxInvFb {k i : ℕ} (hik : i < k) (hk2 : 2 ≤ k) :
    dsvReidxFb k (dsvReidxFb k i) = i := by
  by_cases hlast : i = k - 1
  · subst hlast
    have hL := dsvReidxLastFb (k := k) (by omega)
    rw [hL, hL]
  · rw [dsvReidxSqFb hik (by omega) hk2, dsvReidxSqFb (by omega) (by omega) hk2]
    omega

private theorem dsvReidxInjFb {k a b : ℕ} (hab : dsvReidxFb k a = dsvReidxFb k b)
    (ha : a < k) (hb : b < k) (hk2 : 2 ≤ k) : a = b := by
  have h := dsvReidxInvFb ha hk2
  rw [← h, hab, dsvReidxInvFb hb hk2]

/-- J 条件的重指标传输：对 i < k，
`s.J (k-(i%k+1)) (k-((i+1)%k+1)) ↔ s.J (σ i) (σ i + 1)`。只吃 J 对称 +
Periodic2（isScsV39 两合取），零几何。 -/
private theorem dsvKeyFb (s : ScsV39) (hpJ : Periodic2 s.J s.k)
    (hJsym : ∀ i j, s.J i j = s.J j i) {k : ℕ} (hk : s.k = k) {i : ℕ}
    (hik : i < k) (hk2 : 2 ≤ k) :
    s.J (k - (i % k + 1)) (k - ((i + 1) % k + 1)) ↔
      s.J (dsvReidxFb k i) (dsvReidxFb k i + 1) := by
  rw [Nat.mod_eq_of_lt hik]
  by_cases hlast : i = k - 1
  · subst hlast
    have hL := dsvReidxLastFb (k := k) (by omega)
    have hpJk : Periodic2 s.J k := by
      have h := hpJ
      rw [hk] at h
      exact h
    have hm := periodicMod2Fb hpJk (k - 1) k
    rw [Nat.mod_self] at hm
    have hE1 : k - ((k - 1) + 1) = 0 := by omega
    have hE2 : k - ((k - 1 + 1) % k + 1) = k - 1 := by
      rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
    rw [hE1, hE2, hL, show k - 1 + 1 = k from by omega]
    rw [← hm]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hJsym] at h; exact h
    · rw [hJsym] at h; exact h
  · have hb : k - ((i + 1) % k + 1) = k - 2 - i := by
      rw [Nat.mod_eq_of_lt (by omega : i + 1 < k)]
      omega
    rw [show k - (i + 1) = k - 1 - i from by omega, hb,
      dsvReidxSqFb hik (by omega) hk2,
      show (k - 2 - i) + 1 = k - 1 - i from by omega]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hJsym] at h; exact h
    · rw [hJsym] at h; exact h

/-- `setSum` 的有限集展开。 -/
private theorem setSumFiniteFb {α : Type*} (s : Set α) (f : α → ℝ) (h : Set.Finite s) :
    setSum s f = ∑ w ∈ h.toFinset, f w := by
  rw [setSum, dif_pos h]

/-- HOL `DSV_EQ_SYM_0`（YXIONXL2.hl:2236；LA13 孪生 `DSV_EQ_SYM_0_p13`
= LA13_f0b:2378）。`dsv_v39 (scs_opp_v39 s) (\i. --peropp vv k i)
= dsv_v39 s vv`。 -/
theorem DSV_EQ_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    dsvV39 (scsOppV39 s) (fun i => -(peropp vv k i)) = dsvV39 s vv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpJ, hsym5, -, -, -, -, -, -, -, -⟩ := hiscs
  have hJsym : ∀ i j, s.J i j = s.J j i := fun i j => (hsym5 i j).2.2.2.2
  have hper : Periodic vv k := by
    have h := hbb.2.1
    rw [hk] at h
    exact h
  have hk2 : 2 ≤ k := by omega
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hdop : (scsOppV39 s).d = s.d := rfl
  have hJop : ∀ i j : ℕ, (scsOppV39 s).J i j
      = s.J (k - (i % k + 1)) (k - (j % k + 1)) := by
    intro i j
    show peropp2 s.J s.k i j = _
    rw [hk]
    rfl
  have hS1set : {i | i < k ∧ (scsOppV39 s).J i (i + 1)}
      = {i | i < k ∧ s.J (k - (i % k + 1)) (k - ((i + 1) % k + 1))} := by
    ext i
    exact ⟨fun h => ⟨h.1, hJop i (i + 1) ▸ h.2⟩,
      fun h => ⟨h.1, (hJop i (i + 1)).symm ▸ h.2⟩⟩
  -- isEar 两侧皆假（k ≥ 4；NO_IS_EAR / NO_IS_EAR_SCS_OPP 同型）
  have hnearL : ¬isEarV39 (scsOppV39 s) := by
    intro hc
    have hk3e := hc.2.2.1
    rw [hK] at hk3e
    omega
  have hnearR : ¬isEarV39 s := by
    intro hc
    have hk3e := hc.2.2.1
    rw [hk] at hk3e
    omega
  unfold dsvV39
  rw [if_neg hnearL, if_neg hnearR, hdop, hK, hk, hS1set]
  simp only [peropp, distNegNegFb]
  have hfin1 : {i | i < k ∧ s.J (k - (i % k + 1)) (k - ((i + 1) % k + 1))}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
  have hfin2 : {i | i < k ∧ s.J i (i + 1)}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
  rw [setSumFiniteFb _ _ hfin1, setSumFiniteFb _ _ hfin2]
  refine congrArg (fun r : ℝ => s.d + (0.1:ℝ) * (-1:ℝ) * r) ?_
  refine Finset.sum_nbij (fun (i : ℕ) => dsvReidxFb k i) ?_ ?_ ?_ ?_
  · -- 落点 ∈ 右侧集
    intro a ha
    have ha2 : a < k ∧ s.J (k - (a % k + 1)) (k - ((a + 1) % k + 1)) :=
      hfin1.mem_toFinset.mp ha
    have hlt := dsvReidxLtFb ha2.1 hk2
    refine hfin2.mem_toFinset.mpr ⟨hlt, ?_⟩
    exact dsvKeyFb s hpJ hJsym hk ha2.1 hk2 |>.mp ha2.2
  · -- 单射
    intro a ha b hb hab
    exact dsvReidxInjFb hab (hfin1.mem_toFinset.mp ha).1
      (hfin1.mem_toFinset.mp hb).1 hk2
  · -- 满射（逆 = 自身）
    intro m hm
    have hm2 : m < k ∧ s.J m (m + 1) := hfin2.mem_toFinset.mp hm
    have hlt := dsvReidxLtFb hm2.1 hk2
    have hkey := dsvKeyFb s hpJ hJsym hk hlt hk2
    rw [dsvReidxInvFb hm2.1 hk2] at hkey
    refine ⟨dsvReidxFb k m, hfin1.mem_toFinset.mpr ⟨hlt, hkey.mpr hm2.2⟩, ?_⟩
    show dsvReidxFb k (dsvReidxFb k m) = m
    rw [dsvReidxInvFb hm2.1 hk2]
  · -- 逐点：σ 对合下距离端闭合
    intro a ha
    have ha2 : a < k := (hfin1.mem_toFinset.mp ha).1
    show cstab - dist (vv (k - (a % k + 1))) (vv (k - ((a + 1) % k + 1)))
      = cstab - dist (vv (dsvReidxFb k a)) (vv (dsvReidxFb k a + 1))
    rw [Nat.mod_eq_of_lt ha2]
    by_cases hlast : a = k - 1
    · subst hlast
      have hL := dsvReidxLastFb (k := k) (by omega)
      have hE2 : k - ((k - 1 + 1) % k + 1) = k - 1 := by
        rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
      have hE4 : k - 1 + 1 = k := by omega
      have hE5 : (vv k : V3) = vv 0 := by simpa using hper 0
      rw [show k - ((k - 1) + 1) = 0 from by omega, hE2, hL, hE4, hE5, dist_comm]
    · have hb2 : k - ((a + 1) % k + 1) = k - 2 - a := by
        rw [Nat.mod_eq_of_lt (by omega : a + 1 < k)]
        omega
      rw [show k - (a + 1) = k - 1 - a from by omega, hb2,
        dsvReidxSqFb ha2 (by omega) hk2,
        show (k - 2 - a) + 1 = k - 1 - a from by omega, dist_comm]

/-! ### S.3 LA1 桥（`localFan_p3 → LocalFan`）+ `Fan.sigmaFan` 二元闭式 -/

/-- `Fan.sigmaFan` 在二元邻域集上的闭式：`ee v E = {p, q}`（`p ≠ q`）时
`Fan.sigmaFan 0 univ E v q = p`（epsilon 唯一性，同 `azimCycleTwoFb` 手法）。 -/
private theorem sigmaFanTwoFb {p q v u : V3} {E : Set (Set V3)}
    (hee : ee v E = ({p, q} : Set V3)) (hne : p ≠ q) (huq : u = q) :
    Fan.sigmaFan 0 Set.univ E v u = p := by
  have hso : Fan.setOfEdge v Set.univ E = ({p, q} : Set V3) := by
    have h0 : Fan.setOfEdge v Set.univ E = ee v E := by
      ext w
      simp only [Fan.setOfEdge, ee, Set.mem_setOf_eq, Set.mem_univ, true_and, and_true]
    rw [h0, hee]
  have hneU : ¬(Fan.setOfEdge v Set.univ E = {u}) := by
    rw [hso, huq]
    intro hc
    have hc' := Set.eq_singleton_iff_unique_mem.mp hc
    exact hne (hc'.2 p (Set.mem_insert_iff.mpr (Or.inl rfl)))
  unfold Fan.sigmaFan
  rw [if_neg hneU, hso, huq]
  refine epsFixedFb ⟨Set.mem_insert_iff.mpr (Or.inl rfl), hne, ?_⟩ ?_
  · intro w1 hw1 hw1ne
    rcases Set.mem_insert_iff.mp hw1 with h | h
    · exact h ▸ le_refl _
    · exact absurd h hw1ne
  · intro y hy
    rcases Set.mem_insert_iff.mp hy.1 with h | h
    · exact h
    · exact absurd h hy.2.1

/-- 逐点函数相等下 iterate 逐点相等。 -/
private theorem iterateCongrFb {α : Type*} {f g : α → α} (h : ∀ y, f y = g y) :
    ∀ (n : ℕ) (y : α), f^[n] y = g^[n] y := by
  intro n
  induction n with
  | zero => intro y; rfl
  | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih y, h]

/-- **LA1 桥**：LA3 `localFan_p3` + 孤立自对 dart 缺失
（`dartsOfHyp_p3 E V = Fan.dart1OfFan V E`）⇒ LA1 `LocalFan`。AzimBridge
`LocalFan.of_localFan_p3`（:740）的 kit 内私有重铸；hno 前提消去
self-pair 分支后组件桥为纯 funext 链。 -/
private theorem localFanLA1ofP3Fb {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hp3 : localFan_p3 V E FF) (hno : dartsOfHyp_p3 E V = Fan.dart1OfFan V E) :
    LocalFan V E FF := by
  obtain ⟨H, hdarts, hedge, hnode, hface, hfan, ⟨x, hx, hFF⟩, hdih⟩ := hp3
  have c1 := hdih.1
  have c2 := hdih.2.1
  have c3 := hdih.2.2.1
  have c4 := hdih.2.2.2.1
  have c5 := hdih.2.2.2.2
  -- Fan.hypermapOfFan 组件在 dart1OfFan 内外的 if 形（AzimBridge apply_* 私有件重铸）
  have hme : ∀ d : V3 × V3, (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = if d ∈ Fan.dart1OfFan V E then Fan.eFanPair V E d
      else d := by
    intro d
    show (@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = _
    unfold Fan.hypermapOfFan Kepler.Text.Fan.extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(Fan.finite_dart1_fan hfan).coe_toFinset]
  have hmn : ∀ d : V3 × V3, (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = if d ∈ Fan.dart1OfFan V E then Fan.nFanPair 0 V E d
      else d := by
    intro d
    show (@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = _
    unfold Fan.hypermapOfFan Kepler.Text.Fan.extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(Fan.finite_dart1_fan hfan).coe_toFinset]
  have hmf : ∀ d : V3 × V3, (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = if d ∈ Fan.dart1OfFan V E then Fan.fFanPair 0 V E d
      else d := by
    intro d
    show (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) d = _
    unfold Fan.hypermapOfFan Kepler.Text.Fan.extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [(Fan.finite_dart1_fan hfan).coe_toFinset]
  -- ofHyp 组元的 if 形（定义性）
  have hifE : ∀ d : V3 × V3, eeOfHyp_p3 0 V E d =
      if d ∈ dartsOfHyp_p3 E V then (d.2, d.1) else d := fun _ => rfl
  have hifN : ∀ d : V3 × V3, nnOfHyp_p3 0 V E d =
      if d ∈ dartsOfHyp_p3 E V then (d.1, azimCycle_p3 (EE_p3 d.1 E) 0 d.1 d.2) else d :=
    fun _ => rfl
  have hifF : ∀ d : V3 × V3, ffOfHyp_p3 0 V E d =
      if d ∈ dartsOfHyp_p3 E V then (d.2, ivsAzimCycle_p3 (EE_p3 d.2 E) 0 d.2 d.1) else d :=
    fun _ => rfl
  -- 三张点式桥（hno 消去 self-pair 分支）
  have hptE : ∀ d : V3 × V3, ⇑H.edgeMap d =
      ⇑(@Hypermap.edgeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) d := by
    intro d
    by_cases hd : d ∈ Fan.dart1OfFan V E
    · have hDD : d ∈ dartsOfHyp_p3 E V := by rw [hno]; exact hd
      rw [hedge]
      simp only [hifE d, hme d, if_pos hd, if_pos hDD]
      rfl
    · have hNN : ¬(d ∈ dartsOfHyp_p3 E V) := by rw [hno]; exact hd
      rw [hedge]
      simp only [hifE d, hme d, if_neg hd, if_neg hNN]
  have hptN : ∀ d : V3 × V3, ⇑H.nodeMap d =
      ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) d := by
    intro d
    by_cases hd : d ∈ Fan.dart1OfFan V E
    · have hDD : d ∈ dartsOfHyp_p3 E V := by rw [hno]; exact hd
      rw [hnode]
      rw [hifN d, hmn d]
      simp only [if_pos hd, if_pos hDD,
        AZIM_CYCLE_EQ_SIGMA_FAN hfan
          ((Fan.properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hd)]
      rfl
    · have hNN : ¬(d ∈ dartsOfHyp_p3 E V) := by rw [hno]; exact hd
      rw [hnode]
      rw [hifN d, hmn d, if_neg hd, if_neg hNN]
  have hptF : ∀ d : V3 × V3, ⇑H.faceMap d =
      ⇑(@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) d := by
    intro d
    by_cases hd : d ∈ Fan.dart1OfFan V E
    · have hDD : d ∈ dartsOfHyp_p3 E V := by rw [hno]; exact hd
      have hpE : ({d.2, d.1} : Set V3) ∈ E :=
        Set.pair_comm _ _ ▸ (hd : ({d.1, d.2} : Set V3) ∈ E)
      rw [hface]
      rw [hifF d, hmf d]
      simp only [if_pos hd, if_pos hDD,
        IVS_AZIM_EQ_INVERSE_SIGMA_FAN hfan hpE,
        Fan.inverse_sigma_fan_eq_inverse1 hfan hpE]
      rfl
    · have hNN : ¬(d ∈ dartsOfHyp_p3 E V) := by rw [hno]; exact hd
      rw [hface]
      rw [hifF d, hmf d, if_neg hd, if_neg hNN]
  -- dart Finset 一致
  have hcoeD : ((@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan) : Set (V3 × V3))) = Fan.dart1OfFan V E := by
    -- toFinset 的 [DecidableEq] 实例钉为 instProd 形（与 Fan.lean 定义时烘焙一致；
    -- 仅此 have 块内生效，避免 dartDecEq3 抢占 synth）。
    haveI : DecidableEq (V3 × V3) := fun a b => instDecidableEqProd a b
    exact (Fan.finite_dart1_fan hfan).coe_toFinset
  have hDart' : (@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
      (Fan.hypermapOfFan 0 V E hfan)) = H.darts :=
    Finset.coe_injective (hcoeD.trans (hno.symm.trans hdarts.symm))
  -- iterate / 轨道传输
  have hitF := iterateCongrFb hptF
  have hNF : ⇑H.nodeMap =
      ⇑(@Hypermap.nodeMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) :=
    funext hptN
  have horb : ∀ y : V3 × V3, orbitMap (H.faceMap : Equiv.Perm (V3 × V3)) y =
      orbitMap (@Hypermap.faceMap (V3 × V3) (fun a b => instDecidableEqProd a b)
        (Fan.hypermapOfFan 0 V E hfan)) y := by
    intro y
    ext z
    simp only [orbitMap, Set.mem_setOf_eq, Equiv.Perm.coe_pow]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hitF n y).symm ▸ hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hitF n y ▸ hn⟩
  refine ⟨hfan, x, ?_, ?_, ?_⟩
  · rw [hDart']
    exact hx
  · rw [hFF]
    ext z
    simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq, Equiv.Perm.coe_pow]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hitF n x).symm ▸ hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, hitF n x ▸ hn⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hDart']
      exact c1
    · intro dmem hdmem
      have hd2 : dmem ∈ (↑H.darts : Set (V3 × V3)) := by
        have h3 : dmem ∈ (↑(@Hypermap.darts (V3 × V3) (fun a b => instDecidableEqProd a b)
          (Fan.hypermapOfFan 0 V E hfan)) : Set (V3 × V3)) := Finset.mem_coe.mpr hdmem
        rwa [hDart'] at h3
      rw [hDart', c2 dmem hd2,
        show H.face dmem = orbitMap (H.faceMap : Equiv.Perm (V3 × V3)) dmem from rfl,
        ← horb dmem, ← hNF]
    · refine ⟨?_, ?_⟩
      · intro i hi0 hik h1
        have hEq : (H.faceMap : V3 × V3 → V3 × V3)^[i] = id := by
          funext y
          rw [hitF i y, ← Equiv.Perm.coe_pow, h1]
          rfl
        exact c3.1 i hi0 hik hEq
      · refine Equiv.Perm.ext fun y => ?_
        rw [Equiv.Perm.coe_pow, ← hitF (FF.ncard) y, c3.2]
        rfl
    · refine ⟨?_, ?_⟩
      · intro i hi0 hik h1
        have hEq : (H.edgeMap : V3 × V3 → V3 × V3)^[i] = id := by
          funext y
          rw [iterateCongrFb hptE i y, ← Equiv.Perm.coe_pow, h1]
          rfl
        exact c4.1 i hi0 hik hEq
      · refine Equiv.Perm.ext fun y => ?_
        rw [Equiv.Perm.coe_pow, ← iterateCongrFb hptE (2 : ℕ) y, c4.2]
        rfl
    · refine ⟨?_, ?_⟩
      · intro i hi0 hik h1
        have hEq : (H.nodeMap : V3 × V3 → V3 × V3)^[i] = id := by
          funext y
          rw [iterateCongrFb hptN i y, ← Equiv.Perm.coe_pow, h1]
          rfl
        exact c5.1 i hi0 hik hEq
      · refine Equiv.Perm.ext fun y => ?_
        rw [Equiv.Perm.coe_pow, ← iterateCongrFb hptN (2 : ℕ) y, c5.2]
        rfl

/-! ### S.4 PEROPP_IN_BB_SYM_0（HOL :2183） -/

/-- HOL `PEROPP_IN_BB_SYM_0`（YXIONXL2.hl:2183；LA13 孪生
`PEROPP_IN_BB_SYM_0_p13` = LA13_f0b:2372）。
`BBs_v39 (scs_opp_v39 s) (\i. -- peropp vv k i)`；fan 槽消费本 kit 的
`CONVEX_LOCAL_FAN_SYM_0_fb` 层（经 `LOCAL_FAN_DUAL_SYM_0_fb` + LA1 桥 +
azim 对换传输）。 -/
theorem PEROPP_IN_BB_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    BBsV39 (scsOppV39 s) (fun i => -(peropp vv k i)) := by
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hAop : ∀ i j : ℕ, (scsOppV39 s).a i j
      = s.a (k - (i % k + 1)) (k - (j % k + 1)) := by
    intro i j
    show peropp2 s.a s.k i j = _
    rw [hk]
    rfl
  have hBop : ∀ i j : ℕ, (scsOppV39 s).b i j
      = s.b (k - (i % k + 1)) (k - (j % k + 1)) := by
    intro i j
    show peropp2 s.b s.k i j = _
    rw [hk]
    rfl
  have hw : ∀ i : ℕ, (-(peropp vv k i) : V3) = -(vv (k - (i % k + 1))) := fun _ => rfl
  -- 上下文
  have hctx := fanbaseCtxFb s vv k (Set.image vv Set.univ)
    (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ)
    hk rfl rfl rfl hiscs hk3 hbb
  have hper0 : Periodic vv k := hctx.2.2.1
  -- 原族 ConvexLocalFan（azim (A)/(B) 内容提取用）
  have hconv0 : ConvexLocalFan (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rcases hbb.2.2.2 with h3 | hcf
    · rw [hk] at h3
      exact absurd h3 hk3
    · simpa only [Set.image_univ] using hcf
  obtain ⟨hlf0, hpts⟩ := hconv0
  obtain ⟨hfan0, -, -⟩ := hlf0
  have hne0 : ∀ j, vv j ≠ 0 := by
    intro j hc
    exact hfan0.2.2.2.1 ⟨j, Set.mem_univ _, hc⟩
  -- 原族方位内容 (A)/(B)（F3 CONVEX 同块）
  have hsig : ∀ i : ℕ,
      Fan.sigmaFan 0 Set.univ (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
        (vv i) (vv (i + 1)) = vv (i + k - 1) :=
    fun i => sigmaFanUnivFb (by omega) hper0 rfl (hctx.2.2.2.1)
      (hctx.2.2.2.2.2.2.1)
      (fun i j hc => vvInjModFb hk (by omega) hctx.1 hctx.2.1 hper0 hc) i
  have hAB : ∀ i : ℕ,
      azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) ≤ Real.pi ∧
      ∀ z : V3, z ∈ Set.image vv Set.univ → 0 ≤ azim 0 (vv i) (vv (i + 1)) z ∧
        azim 0 (vv i) (vv (i + 1)) z ≤ azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
    intro i
    have hdart : (vv i, vv (i + 1)) ∈
        Set.image (fun j : ℕ => (vv j, vv (j + 1))) Set.univ :=
      ⟨i, Set.mem_univ _, rfl⟩
    obtain ⟨hA, hB⟩ := hpts (vv i, vv (i + 1)) hdart
    have hcard : 1 < (ee (vv i)
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)).ncard := by
      rw [hctx.2.2.2.1 i, Set.ncard_pair (hctx.2.2.2.2.2.2.1 i)]
      norm_num
    constructor
    · have hA' : azim 0 (vv i) (vv (i + 1))
          (Fan.sigmaFan 0 Set.univ
            (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            (vv i) (vv (i + 1))) ≤ Real.pi := by
        have h1 : azimInFan (vv i, vv (i + 1))
            (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            = azim 0 (vv i) (vv (i + 1))
              (Fan.sigmaFan 0 Set.univ
                (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
                (vv i) (vv (i + 1))) := by
          simp only [azimInFan, if_pos hcard]
        rw [h1] at hA
        exact hA
      rwa [hsig i] at hA'
    · intro z hz
      have hB' : z ∈ wedgeGe 0 (vv i) (vv (i + 1))
          (Fan.sigmaFan 0 Set.univ
            (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            (vv i) (vv (i + 1))) := by
        have h1 : wedgeInFanGe (vv i, vv (i + 1))
            (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
            = wedgeGe 0 (vv i) (vv (i + 1))
              (Fan.sigmaFan 0 Set.univ
                (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
                (vv i) (vv (i + 1))) := by
          simp only [wedgeInFanGe, if_pos hcard]
        rw [h1] at hB
        exact hB hz
      simp only [wedgeGe, Set.mem_setOf_eq] at hB'
      rw [hsig i] at hB'
      exact hB'
  -- LA3 形 localFan（本 kit F3 件）→ 平取负像形
  have hlf3 := LOCAL_FAN_DUAL_SYM_0_fb s vv k (Set.image vv Set.univ)
    (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ)
    hk rfl rfl rfl hiscs hk3 hbb
  rw [oppImageVEqNegFb vv hper0 (by omega), oppImageEEqNegFb vv hper0 (by omega),
    oppImageFEq2NegFb vv hper0 (by omega)] at hlf3
  -- 负族无孤立点 ⇒ hno
  have hspEmpty : selfPairs_p3
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => -(vv i)) Set.univ) = (∅ : Set (V3 × V3)) := by
    ext p
    constructor
    · rintro ⟨hp12, hpV, hpEE⟩
      obtain ⟨i, -, hi⟩ := hpV
      rw [← hi] at hpEE
      have hmem : (-(vv (i + 1)) : V3) ∈ EE_p3 (-(vv i))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) := by
        show -(vv (i + 1)) ∈ ee (-(vv i))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        rw [hctx.2.2.2.2.1 i]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact absurd hmem (by rw [hpEE]; simp)
    · exact fun h => h.elim
  have hno : dartsOfHyp_p3
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => -(vv i)) Set.univ)
      = Fan.dart1OfFan (Set.image (fun i : ℕ => -(vv i)) Set.univ)
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ) := by
    have hunfold : dartsOfHyp_p3
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        (Set.image (fun i : ℕ => -(vv i)) Set.univ)
        = ordPairs_p3 (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
          ∪ selfPairs_p3
            (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
            (Set.image (fun i : ℕ => -(vv i)) Set.univ) := rfl
    rw [hunfold, hspEmpty, Set.union_empty]
    rfl
  have hlf1 : LocalFan (Set.image (fun i : ℕ => -(vv i)) Set.univ)
      (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ) :=
    localFanLA1ofP3Fb hlf3 hno
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. ballAnnulus
    simp only [← Set.image_univ, peropp]
    rw [oppImageVEqNegFb vv hper0 (by omega)]
    rintro x ⟨i, -, rfl⟩
    exact ballAnnulusNegFb _ (hbb.1 ⟨i, rfl⟩)
  · -- 2. Periodic
    intro i
    show -(peropp vv k (i + (scsOppV39 s).k)) = -(peropp vv k i)
    rw [hK]
    simp only [peropp, Nat.add_mod_right]
  · -- 3. dist 界（peropp2 槽）
    intro i j
    rw [hAop i j, hBop i j]
    show s.a (k - (i % k + 1)) (k - (j % k + 1))
      ≤ dist (-(vv (k - (i % k + 1)))) (-(vv (k - (j % k + 1)))) ∧
      dist (-(vv (k - (i % k + 1)))) (-(vv (k - (j % k + 1)))) ≤
        s.b (k - (i % k + 1)) (k - (j % k + 1))
    rw [distNegNegFb]
    exact hbb.2.2.1 (k - (i % k + 1)) (k - (j % k + 1))
  · -- 4. fan 槽（LA1 ConvexLocalFan 于负族）
    rw [hK]
    right
    simp only [← Set.image_univ, peropp]
    rw [oppImageVEqNegFb vv hper0 (by omega), oppImageEEqNegFb vv hper0 (by omega),
      oppImageFEq2NegFb vv hper0 (by omega)]
    refine ⟨hlf1, ?_⟩
    rintro x ⟨j, -, rfl⟩
    have hcol1 : ¬Collinear ℝ ({0, vv (j + 1), vv j} : Set V3) := by
      have h := hfan0.2.2.2.2.1 ({vv j, vv (j + 1)} : Set V3) ⟨j, Set.mem_univ _, rfl⟩
      show ¬Collinear ℝ (insert 0 (insert (vv (j + 1)) ({vv j} : Set V3)))
      rw [pairSetCommFb]
      exact h
    have hcol2 : ¬Collinear ℝ ({0, vv (j + 1), vv (j + 2)} : Set V3) :=
      hfan0.2.2.2.2.1 ({vv (j + 1), vv (j + 2)} : Set V3) ⟨j + 1, Set.mem_univ _, rfl⟩
    have hne2j : -(vv (j + 2)) ≠ -(vv j) := by
      intro hc
      have hc2 : vv (j + 2) = vv j := by simpa using congrArg Neg.neg hc
      exact hctx.2.2.2.2.2.2.2 j (hc2.trans (hper0 j).symm)
    have hneigh : ee (-(vv (j + 1)))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      = ({-(vv (j + 2)), -(vv j)} : Set V3) := by
      have h := hctx.2.2.2.2.1 (j + 1)
      rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
        show (-(vv (j + k)) : V3) = -(vv j) from by
          simpa using congrArg Neg.neg (hper0 j)] at h
      exact h
    have hcardN : 1 < (ee (-(vv (j + 1)))
          (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)).ncard := by
      rw [hneigh, Set.ncard_pair hne2j]
      norm_num
    constructor
    · -- azimInFan ≤ π：(A) 对换传输
      have hA := (hAB (j + 1)).1
      rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
        show (vv (j + k) : V3) = vv j from hper0 j] at hA
      simp only [azimInFan]
      rw [if_pos hcardN, sigmaFanTwoFb hneigh hne2j rfl, AZIM_NEG_fb hcol1 hcol2]
      exact hA
    · -- V'' ⊆ wedgeInFanGe：下界 azim_nonneg；上界对换传输 + sum4
      simp only [wedgeInFanGe]
      rw [if_pos hcardN, sigmaFanTwoFb hneigh hne2j rfl]
      rintro z ⟨i, -, rfl⟩
      simp only [wedgeGe, Set.mem_setOf_eq]
      refine ⟨azim_nonneg 0 (-(vv (j + 1))) (-(vv j)) (-(vv i)), ?_⟩
      by_cases hcol : Collinear ℝ ({0, vv (j + 1), vv i} : Set V3)
      · have hdeg : azim 0 (-(vv (j + 1))) (-(vv j)) (-(vv i)) = 0 := by
          have hc : Collinear3 0 (-(vv (j + 1))) (-(vv i)) := collinear3_zero_negFb.mp hcol
          unfold azim
          exact if_pos (Or.inr hc)
        rw [hdeg, AZIM_NEG_fb hcol1 hcol2]
        exact azim_nonneg 0 (vv (j + 1)) (vv (j + 2)) (vv j)
      · rw [AZIM_NEG_fb hcol1 hcol, AZIM_NEG_fb hcol1 hcol2]
        have hB := (hAB (j + 1)).2 (vv i) (by
          refine ⟨i, Set.mem_univ _, rfl⟩)
        rw [show ((j:Nat) + 1 + k - 1) = j + k from by omega,
          show (vv (j + k) : V3) = vv j from hper0 j] at hB
        have hsum := sum4_azim_fan (x := 0) (v := vv (j + 1)) (u := vv (j + 2))
          (w1 := vv i) (w2 := vv j) (hne0 (j + 1)) hcol2 hcol hcol1 hB.2
        rw [hsum]
        linarith [azim_nonneg 0 (vv (j + 1)) (vv (j + 2)) (vv i)]

end SOppChain


/-! ### S.5 W2：TAUSTAR_EQ_SYM_0 / BBPRIME_EQ_OPP_SYM_0（HOL :2374 / :3154）-/

-- 本节 helper 同样需要古典可判定（fan 层 if 形 + toFinset）；仅 local 作用域。
attribute [local instance] Classical.propDecidable

/-- `(i+1) % k = (j+1) % k` 且 `i, j < k` 蕴含 `i = j`。 -/
private theorem succModInjFb {k i j : ℕ} (h : (i + 1) % k = (j + 1) % k)
    (hi : i < k) (hj : j < k) : i = j := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · exfalso
    have h1 : (i + 1) % k = i + 1 := Nat.mod_eq_of_lt (by omega)
    rcases Nat.lt_or_ge (j + 1) k with h2 | h2
    · have h3 : (j + 1) % k = j + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    · have h3 : (j + 1) % k = 0 := by
        rw [show j + 1 = k from by omega, Nat.mod_self]
      omega
  · rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · exact heq.symm
    · exfalso
      have h1 : (j + 1) % k = j + 1 := Nat.mod_eq_of_lt (by omega)
      rcases Nat.lt_or_ge (i + 1) k with h2 | h2
      · have h3 : (i + 1) % k = i + 1 := Nat.mod_eq_of_lt (by omega)
        omega
      · have h3 : (i + 1) % k = 0 := by
          rw [show i + 1 = k from by omega, Nat.mod_self]
        omega

/-- `peropp2` 保 Periodic2。 -/
private theorem peropp2PeriodicFb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) : Periodic2 (peropp2 a k) k := by
  intro i j
  show a (k - ((i + k) % k + 1)) (k - (j % k + 1))
      = a (k - (i % k + 1)) (k - (j % k + 1)) ∧
    a (k - (i % k + 1)) (k - ((j + k) % k + 1))
      = a (k - (i % k + 1)) (k - (j % k + 1))
  rw [Nat.add_mod_right, Nat.add_mod_right]
  exact ⟨rfl, rfl⟩

/-- 边端相邻关系：`flip(m) = k-(m%k+1)` 与 `flip(m+1)` 满足 `q+1 = p` 或 `q+1 = p+k`。 -/
private theorem flipAdjFb {k m : ℕ} (hk1 : 1 ≤ k) :
    (k - ((m + 1) % k + 1)) + 1 = k - (m % k + 1) ∨
      (k - ((m + 1) % k + 1)) + 1 = k - (m % k + 1) + k := by
  have hmlt : m % k < k := Nat.mod_lt m (by omega)
  rcases Nat.lt_or_ge (m % k) (k - 1) with h | h
  · left
    have h1 : (m + 1) % k = (m % k + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq m k))
    rw [h1, Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    have hmk : m % k = k - 1 := by omega
    have h1 : (m + 1) % k = (m % k + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq m k))
    rw [h1, hmk, show k - 1 + 1 = k from by omega, Nat.mod_self]
    omega

/-- 边端传输：`q + 1 = p` 或 `q + 1 = p + k` 时 `a p q = a q (q + 1)`
（对称 + Periodic2 传输）。 -/
private theorem oppEdgeAdjFb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) (hsym : ∀ i j, a i j = a j i) {p q : ℕ} (hqk : q < k)
    (hq : q + 1 = p ∨ q + 1 = p + k) : a p q = a q (q + 1) := by
  rcases hq with h | h
  · rw [← h, hsym]
  · have hp0 : p = 0 := by omega
    have hstep : a (k - 1) k = a (k - 1) 0 := by
      have h2 := (periodicAdd2Fb hper 1 (k - 1) 0).2
      rw [Nat.zero_add, Nat.one_mul] at h2
      exact h2
    show a p q = a q (q + 1)
    rw [hp0, show q + 1 = k from by omega, show q = k - 1 from by omega, hsym 0 (k - 1)]
    exact hstep.symm

/-- `flip (m+1) = dsvReidxFb k m`（m < k）。 -/
private theorem flipDsvFb {k m : ℕ} (hik : m < k) (hk2 : 2 ≤ k) :
    k - ((m + 1) % k + 1) = dsvReidxFb k m := by
  by_cases hlast : m = k - 1
  · subst hlast
    rw [dsvReidxLastFb (by omega)]
    rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
  · rw [dsvReidxSqFb hik (by omega) hk2, Nat.mod_eq_of_lt (by omega : m + 1 < k)]
    omega

/-- 边端重指标（i 形）：`peropp2 a k i (i+1) = a (σ i) (σ i + 1)`。 -/
private theorem oppEdgeAtFb' {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) (hsym : ∀ i j, a i j = a j i) (hk2 : 2 ≤ k) (i : ℕ)
    (hik : i < k) : peropp2 a k i (i + 1) = a (dsvReidxFb k i) (dsvReidxFb k i + 1) := by
  show a (k - (i % k + 1)) (k - ((i + 1) % k + 1))
      = a (dsvReidxFb k i) (dsvReidxFb k i + 1)
  have hf := flipAdjFb (k := k) (m := i) (by omega)
  rw [flipDsvFb hik hk2] at hf ⊢
  exact oppEdgeAdjFb hper hsym (dsvReidxLtFb hik hk2) hf

/-- 边端重指标（σ 形）：`peropp2 a k (σ i) (σ i + 1) = a i (i+1)`。 -/
private theorem oppEdgeAtFb {α : Sort*} {a : ℕ → ℕ → α} {k : ℕ}
    (hper : Periodic2 a k) (hsym : ∀ i j, a i j = a j i) (hk2 : 2 ≤ k) (i : ℕ)
    (hik : i < k) :
    peropp2 a k (dsvReidxFb k i) (dsvReidxFb k i + 1) = a i (i + 1) := by
  have hik2 : dsvReidxFb k i < k := dsvReidxLtFb hik hk2
  have h := oppEdgeAtFb' hper hsym hk2 _ hik2
  rwa [dsvReidxInvFb hik hk2] at h

/-- HOL `OPP_IS_SCS`（YXIONXL2.hl:2536）：`scs_opp_v39` 保 is_scs_v39。 -/
private theorem isScsOppFb (s : ScsV39) (hiscs : isScsV39 s) : isScsV39 (scsOppV39 s) := by
  cases s with
  | mk k d a am bm b J lo hi str =>
    obtain ⟨hd, hk3, hk6, hlo, hhi, hstr, -, hpa, hpam, hpbm, hpb, hpJ, hsym5, hch, hdiag0,
      hdiag, hb3, hbc, hjn, hjab, hcard⟩ := hiscs
    have hk3' : 3 ≤ k := hk3
    have hk6' : k ≤ 6 := hk6
    have hpa' : Periodic2 a k := hpa
    have hpb' : Periodic2 b k := hpb
    have hsymA : ∀ i j, a i j = a j i := fun i j => (hsym5 i j).1
    have hsymB : ∀ i j, b i j = b j i := fun i j => (hsym5 i j).2.2.2.1
    have hjn' : ∀ i j, J i j → j % k = (i + 1) % k ∨ i % k = (j + 1) % k := hjn
    have hjab' : ∀ i j, J i j → a i j = Real.sqrt 8 ∧ b i j = cstab := hjab
    have hcard' : {i | i < k ∧ (2 * h0 < b i (i + 1) ∨ 2 < a i (i + 1))}.ncard + k ≤ 6 := hcard
    have hk0 : k ≠ 0 := by omega
    have hmodlt : ∀ i : ℕ, i % k < k := fun i => Nat.mod_lt i (by omega)
    have hlt : ∀ i, k - (i % k + 1) < k := by
      intro i
      have := hmodlt i
      omega
    have hflipinj : ∀ i j, i < k → j < k → k - (i % k + 1) = k - (j % k + 1) → i = j := by
      intro i j hi hj hc
      have h4 : i % k = j % k := by
        have h2 := hmodlt i
        have h3 := hmodlt j
        omega
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h4
      exact h4
    have key : ∀ y x : ℕ, y < k → x < k → k - (x + 1) = (k - y) % k → y = (x + 1) % k := by
      intro y x hy hx hc
      have hs : (x + 1) % k = (x % k + 1) % k :=
        Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq x k))
      rw [hs, Nat.mod_eq_of_lt hx]
      -- （y = (x + 1) % k）
      rcases Nat.eq_zero_or_pos y with h0 | h0
      · subst h0
        rw [Nat.sub_zero, Nat.mod_self] at hc
        have hxy : x + 1 = k := by omega
        rw [hxy, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)] at hc
        have hxy : x + 1 = y := by omega
        rw [hxy, Nat.mod_eq_of_lt hy]
    show isScsV39 (ScsV39.mk k d (peropp2 a k) (peropp2 am k) (peropp2 bm k) (peropp2 b k)
      (peropp2 J k) (peropp lo k) (peropp hi k) (peropp str k))
    refine ⟨hd, hk3, hk6, peropp_periodic lo k, peropp_periodic hi k, peropp_periodic str k,
      peropp_periodic str k, peropp2PeriodicFb hpa, peropp2PeriodicFb hpam,
      peropp2PeriodicFb hpbm, peropp2PeriodicFb hpb, peropp2PeriodicFb hpJ, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      exact ⟨(hsym5 _ _).1, (hsym5 _ _).2.1, (hsym5 _ _).2.2.1, (hsym5 _ _).2.2.2.1,
        (hsym5 _ _).2.2.2.2⟩
    · intro i j
      exact ⟨(hch _ _).1, (hch _ _).2.1, (hch _ _).2.2⟩
    · intro i
      exact hdiag0 _
    · intro i j hi
      refine hdiag _ _ ⟨hlt i, hlt j, ?_⟩
      intro hc
      exact hi.2.2 (hflipinj i j hi.1 hi.2.1 hc)
    · intro i hi3
      have hf := flipAdjFb (k := k) (m := i) (by omega)
      show b (k - (i % k + 1)) (k - ((i + 1) % k + 1)) < 4
      rw [oppEdgeAdjFb hpb' hsymB (by have := hmodlt (i + 1); omega) hf]
      exact hb3 _ hi3
    · intro i hik4
      have hf := flipAdjFb (k := k) (m := i) (by omega)
      show b (k - (i % k + 1)) (k - ((i + 1) % k + 1)) ≤ cstab
      rw [oppEdgeAdjFb hpb' hsymB (by have := hmodlt (i + 1); omega) hf]
      exact hbc _ hik4
    · intro i j hJ
      have hJ' : J (k - (i % k + 1)) (k - (j % k + 1)) := hJ
      have hjm : (j + 1) % k = (j % k + 1) % k :=
        Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq j k))
      have him : (i + 1) % k = (i % k + 1) % k :=
        Nat.ModEq.add_right 1 (Nat.ModEq.symm (Nat.mod_modEq i k))
      rcases hjn' _ _ hJ' with h | h
      · rw [Nat.mod_eq_of_lt (hlt j), show k - (i % k + 1) + 1 = k - i % k from by
          have := hmodlt i; omega] at h
        refine Or.inr ?_
        rw [hjm]
        exact key (i % k) (j % k) (hmodlt i) (hmodlt j) h
      · rw [Nat.mod_eq_of_lt (hlt i), show k - (j % k + 1) + 1 = k - j % k from by
          have := hmodlt j; omega] at h
        refine Or.inl ?_
        rw [him]
        exact key (j % k) (i % k) (hmodlt j) (hmodlt i) h
    · intro i j hJ
      have hJ' : J (k - (i % k + 1)) (k - (j % k + 1)) := hJ
      exact ⟨(hjab' _ _ hJ').1, (hjab' _ _ hJ').2⟩
    · -- 第 21 槽：σ 重指标 + ncard 传输
      have hk2' : 2 ≤ k := by omega
      have hfin : {i | i < k ∧ (2 * h0 < b i (i + 1) ∨ 2 < a i (i + 1))}.Finite :=
        Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
      have hsetEq : {i | i < k ∧ (2 * h0 < peropp2 b k i (i + 1) ∨ 2 < peropp2 a k i (i + 1))}
          = dsvReidxFb k '' {i | i < k ∧ (2 * h0 < b i (i + 1) ∨ 2 < a i (i + 1))} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨hik, hP⟩
          rw [oppEdgeAtFb' hpa' hsymA hk2' i hik,
            oppEdgeAtFb' hpb' hsymB hk2' i hik] at hP
          exact ⟨dsvReidxFb k i, ⟨dsvReidxLtFb hik hk2', hP⟩, dsvReidxInvFb hik hk2'⟩
        · rintro ⟨m, ⟨hmik, hmP⟩, hmi⟩
          have hikm : dsvReidxFb k m < k := dsvReidxLtFb hmik hk2'
          refine ⟨by rw [← hmi]; exact hikm, ?_⟩
          rw [← hmi, oppEdgeAtFb hpa' hsymA hk2' m hmik,
            oppEdgeAtFb hpb' hsymB hk2' m hmik]
          exact hmP
      have hN : (dsvReidxFb k ''
          {i | i < k ∧ (2 * h0 < b i (i + 1) ∨ 2 < a i (i + 1))}).ncard
          = {i | i < k ∧ (2 * h0 < b i (i + 1) ∨ 2 < a i (i + 1))}.ncard := by
        rw [Set.ncard_image_iff hfin]
        intro x hx y hy hxy
        exact dsvReidxInjFb hxy hx.1 hy.1 hk2'
      show {i | i < k ∧ (2 * h0 < peropp2 b k i (i + 1) ∨ 2 < peropp2 a k i (i + 1))}.ncard
        + k ≤ 6
      rw [hsetEq, hN]
      exact hcard'

/-- HOL `DSV_EQ_SYM_0` 的全分支形（去 `¬ k ≤ 3`，耳记号以 IFF 假设显式给出）。 -/
private theorem dsvOppEqAllFb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hbb : BBsV39 s vv)
    (he : isEarV39 s ↔ isEarV39 (scsOppV39 s)) :
    dsvV39 (scsOppV39 s) (fun i => -(peropp vv k i)) = dsvV39 s vv := by
  obtain ⟨-, hk3s, -, -, -, -, -, -, -, -, -, hpJ, hsym5, -, -, -, -, -, -, -, -⟩ := hiscs
  have hJsym : ∀ i j, s.J i j = s.J j i := fun i j => (hsym5 i j).2.2.2.2
  have hper : Periodic vv k := by
    have h := hbb.2.1
    rw [hk] at h
    exact h
  have hk2 : 2 ≤ k := by omega
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hdop : (scsOppV39 s).d = s.d := rfl
  have hJop : ∀ i j : ℕ, (scsOppV39 s).J i j
      = s.J (k - (i % k + 1)) (k - (j % k + 1)) := by
    intro i j
    have hJd : (scsOppV39 s).J i j
        = s.J (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1)) := rfl
    rw [hJd, hk]
  have hS1set : {i | i < k ∧ (scsOppV39 s).J i (i + 1)}
      = {i | i < k ∧ s.J (k - (i % k + 1)) (k - ((i + 1) % k + 1))} := by
    ext i
    exact ⟨fun h => ⟨h.1, hJop i (i + 1) ▸ h.2⟩,
      fun h => ⟨h.1, (hJop i (i + 1)).symm ▸ h.2⟩⟩
  unfold dsvV39
  rw [← he, hdop, hK, hk, hS1set]
  simp only [peropp, distNegNegFb]
  have hfin1 : {i | i < k ∧ s.J (k - (i % k + 1)) (k - ((i + 1) % k + 1))}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
  have hfin2 : {i | i < k ∧ s.J i (i + 1)}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
  rw [setSumFiniteFb _ _ hfin1, setSumFiniteFb _ _ hfin2]
  refine congrArg
    (fun r : ℝ => s.d + (0.1:ℝ) * (if isEarV39 s then (1:ℝ) else -1) * r) ?_
  refine Finset.sum_nbij (fun (i : ℕ) => dsvReidxFb k i) ?_ ?_ ?_ ?_
  · intro a ha
    have ha2 : a < k ∧ s.J (k - (a % k + 1)) (k - ((a + 1) % k + 1)) :=
      hfin1.mem_toFinset.mp ha
    have hlt := dsvReidxLtFb ha2.1 hk2
    refine hfin2.mem_toFinset.mpr ⟨hlt, ?_⟩
    exact (dsvKeyFb s hpJ hJsym hk ha2.1 hk2).mp ha2.2
  · intro a ha b hb hab
    exact dsvReidxInjFb hab (hfin1.mem_toFinset.mp ha).1
      (hfin1.mem_toFinset.mp hb).1 hk2
  · intro m hm
    have hm2 : m < k ∧ s.J m (m + 1) := hfin2.mem_toFinset.mp hm
    have hlt := dsvReidxLtFb hm2.1 hk2
    have hkey := dsvKeyFb s hpJ hJsym hk hlt hk2
    rw [dsvReidxInvFb hm2.1 hk2] at hkey
    refine ⟨dsvReidxFb k m, hfin1.mem_toFinset.mpr ⟨hlt, hkey.mpr hm2.2⟩, ?_⟩
    show dsvReidxFb k (dsvReidxFb k m) = m
    rw [dsvReidxInvFb hm2.1 hk2]
  · intro a ha
    have ha2 : a < k := (hfin1.mem_toFinset.mp ha).1
    show cstab - dist (vv (k - (a % k + 1))) (vv (k - ((a + 1) % k + 1)))
      = cstab - dist (vv (dsvReidxFb k a)) (vv (dsvReidxFb k a + 1))
    rw [Nat.mod_eq_of_lt ha2]
    by_cases hlast : a = k - 1
    · subst hlast
      have hL := dsvReidxLastFb (k := k) (by omega)
      have hE2 : k - ((k - 1 + 1) % k + 1) = k - 1 := by
        rw [show k - 1 + 1 = k from by omega, Nat.mod_self]
      have hE4 : k - 1 + 1 = k := by omega
      have hE5 : (vv k : V3) = vv 0 := by simpa using hper 0
      rw [show k - ((k - 1) + 1) = 0 from by omega, hE2, hL, hE4, hE5, dist_comm]
    · have hb2 : k - ((a + 1) % k + 1) = k - 2 - a := by
        rw [Nat.mod_eq_of_lt (by omega : a + 1 < k)]
        omega
      rw [show k - (a + 1) = k - 1 - a from by omega, hb2,
        dsvReidxSqFb ha2 (by omega) hk2,
        show (k - 2 - a) + 1 = k - 1 - a from by omega, dist_comm]

/-- HOL `is_ear_v39 (scs_opp_v39 t)` ↔ `is_ear_v39 t`（耳记号经 σ 重指标传输）。 -/
private theorem isEarOppIffFb (s : ScsV39) (hiscs : isScsV39 s) :
    isEarV39 s ↔ isEarV39 (scsOppV39 s) := by
  have hfwd : ∀ t : ScsV39, isScsV39 t → isEarV39 t → isEarV39 (scsOppV39 t) := by
    intro t hT hE
    have hTfull := hT
    obtain ⟨-, -, -, -, -, -, -, hpaT, -, -, hpbT, hpJT, hsym5T, -, -, -, -, -, -, -, -⟩ := hT
    obtain ⟨-, hunadT, hk3, hd011, hbii, j0, hset, haj0, hbj0, hother⟩ := hE
    have hk2T : 2 ≤ t.k := by omega
    have hJsym : ∀ i j, t.J i j = t.J j i := fun i j => (hsym5T i j).2.2.2.2
    have hasymA : ∀ i j, t.a i j = t.a j i := fun i j => (hsym5T i j).1
    have hasymB : ∀ i j, t.b i j = t.b j i := fun i j => (hsym5T i j).2.2.2.1
    have hlt3 : ∀ i, i < 3 → i < t.k := by
      intro i hi
      rw [hk3]
      exact hi
    have hj03 : j0 < 3 ∧ t.J j0 (j0 + 1) := by
      have hm : j0 ∈ ({j0} : Set ℕ) := Set.mem_singleton j0
      rw [← hset] at hm
      exact hm
    unfold isEarV39
    refine ⟨isScsOppFb t hTfull, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hlo, hhi, hstr, haa, hbbm⟩ := hunadT
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · funext i
        show t.lo (t.k - (i % t.k + 1)) = False
        rw [hlo]
      · funext i
        show t.hi (t.k - (i % t.k + 1)) = False
        rw [hhi]
      · funext i
        show t.str (t.k - (i % t.k + 1)) = False
        rw [hstr]
      · show peropp2 t.a t.k = peropp2 t.am t.k
        rw [haa]
      · show peropp2 t.b t.k = peropp2 t.bm t.k
        rw [hbbm]
    · exact hk3
    · exact hd011
    · intro i
      show t.b (t.k - (i % t.k + 1)) (t.k - (i % t.k + 1)) = 0
      exact hbii _
    · have hjlt : dsvReidxFb t.k j0 < t.k := dsvReidxLtFb (hlt3 j0 hj03.1) hk2T
      have hjlt3 : dsvReidxFb t.k j0 < 3 := by
        have hh : dsvReidxFb t.k j0 < t.k := hjlt
        rw [hk3] at hh ⊢
        exact hh
      refine ⟨dsvReidxFb t.k j0, ?_, ?_, ?_, ?_⟩
      · ext j
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hj3, hJopp⟩
          have hjk : j < t.k := hlt3 j hj3
          have hmem : t.J (dsvReidxFb t.k j) (dsvReidxFb t.k j + 1) :=
            (dsvKeyFb t hpJT hJsym rfl hjk hk2T).mp hJopp
          have hjl : dsvReidxFb t.k j < 3 := by
            have hh := dsvReidxLtFb hjk hk2T
            rw [hk3] at hh ⊢
            exact hh
          have hval : dsvReidxFb t.k j ∈ ({j | j < 3 ∧ t.J j (j + 1)} : Set ℕ) :=
            ⟨hjl, hmem⟩
          rw [hset, Set.mem_singleton_iff] at hval
          rw [Set.mem_singleton_iff]
          have hinv := dsvReidxInvFb hjk hk2T
          rw [← hinv, hval]
        · rintro rfl
          refine ⟨hjlt3, ?_⟩
          show t.J (t.k - (dsvReidxFb t.k j0 % t.k + 1))
            (t.k - ((dsvReidxFb t.k j0 + 1) % t.k + 1))
          have hj := dsvKeyFb t hpJT hJsym rfl hjlt hk2T
          rw [dsvReidxInvFb (hlt3 j0 hj03.1) hk2T] at hj
          exact hj.mpr hj03.2
      · show peropp2 t.a t.k (dsvReidxFb t.k j0) (dsvReidxFb t.k j0 + 1) = Real.sqrt 8
        rw [oppEdgeAtFb hpaT hasymA hk2T j0 (hlt3 j0 hj03.1)]
        exact haj0
      · show peropp2 t.b t.k (dsvReidxFb t.k j0) (dsvReidxFb t.k j0 + 1) = cstab
        rw [oppEdgeAtFb hpbT hasymB hk2T j0 (hlt3 j0 hj03.1)]
        exact hbj0
      · intro j hj
        obtain ⟨hj3, hjne⟩ := hj
        have hjk : j < t.k := hlt3 j hj3
        have hjne0 : dsvReidxFb t.k j ≠ j0 := by
          intro hc
          apply hjne
          have hinv := dsvReidxInvFb hjk hk2T
          rw [← hinv, hc]
        have hjlt3j : dsvReidxFb t.k j < 3 := by
          have hh := dsvReidxLtFb hjk hk2T
          rw [hk3] at hh ⊢
          exact hh
        refine ⟨?_, ?_⟩
        · show peropp2 t.a t.k j (j + 1) = 2
          rw [oppEdgeAtFb' hpaT hasymA hk2T j hjk]
          exact (hother (dsvReidxFb t.k j) ⟨hjlt3j, hjne0⟩).1
        · show peropp2 t.b t.k j (j + 1) = 2 * h0
          rw [oppEdgeAtFb' hpbT hasymB hk2T j hjk]
          exact (hother (dsvReidxFb t.k j) ⟨hjlt3j, hjne0⟩).2
  refine ⟨fun hE => hfwd s hiscs hE, fun hEopp => ?_⟩
  have h := hfwd (scsOppV39 s) (isScsOppFb s hiscs) hEopp
  rwa [SCS_OPP_REFL_fb s hiscs] at h

/-- `Finset` 余集上的 setSum。 -/
private theorem setSumCoeFb {β : Type*} (S : Finset β) (g : β → ℝ) :
    setSum (↑S : Set β) g = ∑ x ∈ S, g x := by
  have hfin : (↑S : Set β).Finite := S.finite_toSet
  rw [setSumFiniteFb _ _ hfin]
  have hT : hfin.toFinset = S := Finset.ext fun x => by
    simp [Set.Finite.mem_toFinset]
  rw [hT]

/-- `Iio k` 像上的 setSum 折叠为 range-k 和（InjOn 下）。 -/
private theorem setSumImageIioFb {β : Type*} [DecidableEq β] {f : ℕ → β} {g : β → ℝ}
    {k : ℕ} (hinj : ∀ i j, i < k → j < k → f i = f j → i = j) :
    setSum (Set.image f (Set.Iio k)) g = ∑ i ∈ Finset.range k, g (f i) := by
  have hcoe : Set.image f (Set.Iio k) = ↑(Finset.image f (Finset.range k)) := by
    ext x
    simp [Set.mem_image, Set.mem_Iio, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  rw [hcoe]
  refine (setSumCoeFb _ g).trans ?_
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- 周期像展开到 `Iio k`。 -/
private theorem imageUnivEqIioFb {α : Type*} {f : ℕ → α} {k : ℕ} (hk0 : 0 < k)
    (hper : Periodic f k) : Set.image f Set.univ = Set.image f (Set.Iio k) := by
  ext x
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i % k, Nat.mod_lt _ hk0, periodicModFb hper i⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, Set.mem_univ _, rfl⟩

/-- range-k 和的循环移位。 -/
private theorem sumSuccModFb (φ : ℕ → ℝ) (k : ℕ) (hk0 : 0 < k) :
    ∑ i ∈ Finset.range k, φ ((i + 1) % k) = ∑ i ∈ Finset.range k, φ i := by
  refine Finset.sum_nbij (fun i => (i + 1) % k) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hk0)
  · intro a ha b hb hab
    exact succModInjFb hab (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)
  · intro m hm
    refine ⟨(m + k - 1) % k, Finset.mem_range.mpr (Nat.mod_lt _ hk0), ?_⟩
    show ((m + k - 1) % k + 1) % k = m
    have h1 : ((m + k - 1) % k + 1) % k = (m + k - 1 + 1) % k :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq (m + k - 1) k)
    rw [h1, show m + k - 1 + 1 = m + k from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_coe.mp hm))]
  · intro i _
    rfl

/-- `tauFun` 对平取负像三件套（V/E/FF）的不变性（k>3 taustar 槽的几何核心）。 -/
private theorem tauFunNegImageFb (vv : ℕ → V3) {k : ℕ} (hper : Periodic vv k) (hk3 : 3 ≤ k)
    (hEE : ∀ i, ee (vv i) (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
        = ({vv (i + 1), vv (i + k - 1)} : Set V3))
    (hEEN : ∀ i, ee (-(vv i))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        = ({-(vv (i + 1)), -(vv (i + k - 1))} : Set V3))
    (hcol : ∀ i, ¬ Collinear ℝ (insert 0 ({vv i, vv (i + 1)} : Set V3)))
    (hne2 : ∀ j, vv (j + 2) ≠ vv (j + k))
    (hinj : ∀ i j, vv i = vv j → i % k = j % k) :
    tauFun (Set.image (fun i : ℕ => -(vv i)) Set.univ)
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
        (Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ)
      = tauFun (Set.image vv Set.univ)
          (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
          (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
  have hfk0 : 0 < k := by omega
  have hperF : Periodic (fun i : ℕ => (vv i, vv (i + 1))) k := fun i => by
    show (vv (i + k), vv (i + k + 1)) = (vv i, vv (i + 1))
    rw [show vv (i + k + 1) = vv (i + 1 + k) from by congr 1; omega, hper (i + 1), hper i]
  have hperFN : Periodic (fun i : ℕ => (-(vv (i + 1)), -(vv i))) k := fun i => by
    show (-(vv (i + k + 1)), -(vv (i + k))) = (-(vv (i + 1)), -(vv i))
    rw [show vv (i + k + 1) = vv (i + 1 + k) from by congr 1; omega, hper (i + 1), hper i]
  have hinjF : ∀ i j, i < k → j < k →
      (fun i : ℕ => (vv i, vv (i + 1))) i = (fun i : ℕ => (vv i, vv (i + 1))) j → i = j := by
    intro i j hi hj hc
    have hc' := hc
    simp only [Prod.mk.injEq] at hc'
    have h2 := hinj i j hc'.1
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
    exact h2
  have hinjFN : ∀ i j, i < k → j < k →
      (fun i : ℕ => (-(vv (i + 1)), -(vv i))) i
        = (fun i : ℕ => (-(vv (i + 1)), -(vv i))) j → i = j := by
    intro i j hi hj hc
    have hc' := hc
    simp only [Prod.mk.injEq] at hc'
    have h1 : vv (i + 1) = vv (j + 1) := by
      simpa using congrArg Neg.neg hc'.1
    exact succModInjFb (hinj (i + 1) (j + 1) h1) hi hj
  unfold tauFun
  have hcardN : (Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) Set.univ).ncard
      = (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).ncard := by
    rw [imageUnivEqIioFb hfk0 hperFN, imageUnivEqIioFb hfk0 hperF]
    have hcoN : Set.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) (Set.Iio k)
        = ↑(Finset.image (fun i : ℕ => (-(vv (i + 1)), -(vv i))) (Finset.range k)) := by
      ext x
      simp [Set.mem_image, Set.mem_Iio, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    have hcoP : Set.image (fun i : ℕ => (vv i, vv (i + 1))) (Set.Iio k)
        = ↑(Finset.image (fun i : ℕ => (vv i, vv (i + 1))) (Finset.range k)) := by
      ext x
      simp [Set.mem_image, Set.mem_Iio, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    have hinj1 : Set.InjOn (fun i : ℕ => (-(vv (i + 1)), -(vv i)))
        ((Finset.range k : Finset ℕ) : Set ℕ) := by
      intro a ha b hb hab
      exact hinjFN a b (Finset.mem_range.mp (Finset.mem_coe.mp ha))
        (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
    have hinj2 : Set.InjOn (fun i : ℕ => (vv i, vv (i + 1)))
        ((Finset.range k : Finset ℕ) : Set ℕ) := by
      intro a ha b hb hab
      exact hinjF a b (Finset.mem_range.mp (Finset.mem_coe.mp ha))
        (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab
    rw [hcoN, hcoP, Set.ncard_coe_finset, Set.ncard_coe_finset,
      Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2, Finset.card_range]
  rw [hcardN]
  refine congrArg (fun r : ℝ => r - (Real.pi + sol0) *
    (((Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ).ncard - 2 : ℕ) : ℝ)) ?_
  rw [imageUnivEqIioFb hfk0 hperFN, setSumImageIioFb hinjFN,
    imageUnivEqIioFb hfk0 hperF, setSumImageIioFb hinjF]
  rw [← sumSuccModFb
    (fun j : ℕ => rhoFun (norm (vv j, vv (j + 1)).1) *
      azimInFan (vv j, vv (j + 1))
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)) k hfk0]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hterm : rhoFun (norm (-(vv (i + 1)))) *
      azimInFan (-(vv (i + 1)), -(vv i))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
    = rhoFun (norm (vv (i + 1))) *
      azimInFan (vv (i + 1), vv (i + 2))
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ) := by
    have hEi : ee (-(vv (i + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)
      = ({-(vv (i + 2)), -(vv (i + k))} : Set V3) := by
      have h := hEEN (i + 1)
      rw [show ((i:Nat) + 1 + k - 1) = i + k from by omega] at h
      exact h
    have hne : -(vv (i + 2)) ≠ -(vv (i + k)) := fun hc => hne2 i (negInjFb hc)
    have hneP : vv (i + 2) ≠ vv (i + k) := fun hc => hne2 i hc
    have hneR : vv (i + k) ≠ vv (i + 2) := fun hc => hne2 i hc.symm
    have hcard : 1 < (ee (-(vv (i + 1)))
        (Set.image (fun i : ℕ => ({-(vv i), -(vv (i + 1))} : Set V3)) Set.univ)).ncard := by
      rw [hEi, Set.ncard_pair hne]
      norm_num
    have hcol1 : ¬ Collinear ℝ ({0, vv (i + 1), vv i} : Set V3) := by
      show ¬ Collinear ℝ (insert 0 (insert (vv (i + 1)) ({vv i} : Set V3)))
      have h := hcol i
      rw [pairSetCommFb] at h
      exact h
    have hcol2 : ¬ Collinear ℝ ({0, vv (i + 1), vv (i + 2)} : Set V3) :=
      hcol (i + 1)
    have hEr : ee (vv (i + 1))
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      = ({vv (i + 2), vv (i + k)} : Set V3) := by
      have h := hEE (i + 1)
      rw [show ((i:Nat) + 1 + k - 1) = i + k from by omega] at h
      exact h
    have hcardr : 1 < (ee (vv (i + 1))
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)).ncard := by
      rw [hEr, Set.ncard_pair hneP]
      norm_num
    have hEr' : ee (vv (i + 1))
        (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      = ({vv (i + k), vv (i + 2)} : Set V3) := by
      rw [hEr]
      exact pairSetCommFb _ _
    simp only [azimInFan, norm_neg]
    rw [if_pos hcard, sigmaFanTwoFb hEi hne (congrArg Neg.neg (hper i).symm),
      AZIM_NEG_fb hcol1 hcol2, if_pos hcardr, sigmaFanTwoFb hEr' hneR rfl, hper i]
  exact hterm.trans (congrArg (fun e : V3 × V3 => rhoFun (norm e.1) *
    azimInFan e (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ))
    (periodicModFb hperF (i + 1))).symm

/-- 全 k 形的 `PEROPP_IN_BB`（k ≤ 3 时 fan 槽走左支，纯算术槽）。 -/
private theorem peroppInBbAllFb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hbb : BBsV39 s vv) :
    BBsV39 (scsOppV39 s) (fun i => -(peropp vv k i)) := by
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · have hk33 : k = 3 := by have := hiscs.2.1; omega
    subst hk33
    have hK : (scsOppV39 s).k = 3 := by show s.k = 3; exact hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      exact ballAnnulusNegFb _ (hbb.1 ⟨3 - (i % 3 + 1), rfl⟩)
    · intro i
      show -(peropp vv 3 (i + (scsOppV39 s).k)) = -(peropp vv 3 i)
      rw [hK]
      simp only [peropp, Nat.add_mod_right]
    · intro i j
      have h3 : (scsOppV39 s).a i j
          = s.a (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1)) := rfl
      have h4 : (scsOppV39 s).b i j
          = s.b (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1)) := rfl
      rw [h3, h4, hk]
      show s.a (3 - (i % 3 + 1)) (3 - (j % 3 + 1))
        ≤ dist (-(peropp vv 3 i)) (-(peropp vv 3 j)) ∧
        dist (-(peropp vv 3 i)) (-(peropp vv 3 j)) ≤ s.b (3 - (i % 3 + 1)) (3 - (j % 3 + 1))
      rw [distNegNegFb]
      exact hbb.2.2.1 _ _
    · rw [hK]
      exact Or.inl (by omega)
  · exact PEROPP_IN_BB_SYM_0_fb s vv k hk hiscs (by have := hiscs.2.1; omega) hbb

/-- HOL `TAUSTAR_EQ_SYM_0`（YXIONXL2.hl:2374）。 -/
theorem TAUSTAR_EQ_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbb : BBsV39 s vv) :
    taustarV39 (scsOppV39 s) (fun i => -(peropp vv k i)) = taustarV39 s vv := by
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hper : Periodic vv k := by
    have h := hbb.2.1
    rw [hk] at h
    exact h
  have hctx := fanbaseCtxFb s vv k (Set.image vv Set.univ)
    (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
    (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ)
    hk rfl rfl rfl hiscs hk3 hbb
  have hconv0 : ConvexLocalFan (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rcases hbb.2.2.2 with h3 | hcf
    · rw [hk] at h3
      exact absurd h3 hk3
    · simpa only [Set.image_univ] using hcf
  obtain ⟨hlf0, -⟩ := hconv0
  obtain ⟨hfan0, -, -⟩ := hlf0
  have hcol : ∀ i, ¬ Collinear ℝ (insert 0 ({vv i, vv (i + 1)} : Set V3)) := fun i =>
    hfan0.2.2.2.2.1 _ ⟨i, Set.mem_univ _, rfl⟩
  simp only [taustarV39]
  rw [if_neg (by rw [hK]; exact hk3), if_neg (by rw [hk]; exact hk3)]
  rw [DSV_EQ_SYM_0_fb s vv k hk hiscs hk3 hbb]
  simp only [← Set.image_univ, peropp]
  rw [oppImageVEqNegFb vv hper (by omega), oppImageEEqNegFb vv hper (by omega),
    oppImageFEq2NegFb vv hper (by omega)]
  exact congrArg (fun r : ℝ => r - dsvV39 s vv) (tauFunNegImageFb vv hper (by omega)
    hctx.2.2.2.1 hctx.2.2.2.2.1 hcol hctx.2.2.2.2.2.2.2
    (fun i j hc => vvInjModFb hk (by omega) hctx.1 hctx.2.1 hctx.2.2.1 hc))

/-- HOL `BBPRIME_EQ_OPP_SYM_0`（YXIONXL2.hl:3154）。 -/
theorem BBPRIME_EQ_OPP_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbp : BBprimeV39 s vv) :
    BBprimeV39 (scsOppV39 s) (fun i => -(peropp vv k i)) := by
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hiscsO : isScsV39 (scsOppV39 s) := isScsOppFb s hiscs
  have hbbO : BBsV39 (scsOppV39 s) (fun i => -(peropp vv k i)) :=
    PEROPP_IN_BB_SYM_0_fb s vv k hk hiscs hk3 hbp.1
  simp only [BBprimeV39, Set.mem_setOf_eq]
  refine ⟨hbbO, ?_, ?_⟩
  · intro ww hww
    have hBBs : BBsV39 s (fun i => -(peropp ww k i)) := by
      have h := PEROPP_IN_BB_SYM_0_fb (scsOppV39 s) ww k hK hiscsO hk3 hww
      rwa [SCS_OPP_REFL_fb s hiscs] at h
    have htw : taustarV39 (scsOppV39 s) ww
        = taustarV39 s (fun i => -(peropp ww k i)) := by
      have h := TAUSTAR_EQ_SYM_0_fb (scsOppV39 s) ww k hK hiscsO hk3 hww
      rw [SCS_OPP_REFL_fb s hiscs] at h
      exact h.symm
    rw [htw, TAUSTAR_EQ_SYM_0_fb s vv k hk hiscs hk3 hbp.1]
    exact hbp.2.1 _ hBBs
  · rw [TAUSTAR_EQ_SYM_0_fb s vv k hk hiscs hk3 hbp.1]
    exact hbp.2.2

/-! ### S.6 W3（fanbase-s3-w1）：BBindex 计数对称 + `BBPRIME2_SYM_0_fb` +
`MM_SCS_OPP_fb`（HOL YXIONXL2.hl :3182 / :3343 / :3355 / :3370）。 -/

attribute [local instance] Classical.propDecidable

/-- flip（`σ i = k - (i % k + 1)`）在 `[0,k)` 上的对合性：`σ (σ i) = i`。 -/
private theorem flipInvIioFb {k i : ℕ} (hik : i < k) :
    k - ((k - (i % k + 1)) % k + 1) = i := by
  rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt (show k - (i + 1) < k by omega)]
  omega

/-- flip 在 `[0,k)` 上单射。 -/
private theorem flipInjIioFb {k i j : ℕ} (hik : i < k) (hjk : j < k)
    (h : k - (i % k + 1) = k - (j % k + 1)) : i = j := by
  rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at h
  omega

/-- flip 的后继重指标：`σ (i+1) = (σ i + k - 1) % k`（边端 `σ i ↦ σ i - 1`）。 -/
private theorem flipSuccModFb {k i : ℕ} (hk1 : 0 < k) :
    k - ((i + 1) % k + 1) = (k - (i % k + 1) + k - 1) % k := by
  have hm : i % k < k := Nat.mod_lt i hk1
  have h1 : (i + 1) % k = (i % k + 1) % k :=
    Nat.ModEq.symm (Nat.ModEq.add_right 1 (Nat.mod_modEq i k))
  rcases Nat.lt_or_ge (i % k) (k - 1) with h | h
  · rw [h1, Nat.mod_eq_of_lt (show i % k + 1 < k by omega)]
    rw [show k - (i % k + 1) + k - 1 = k - (i % k + 1 + 1) + k from by omega,
      Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show k - (i % k + 1 + 1) < k by omega)]
  · have hmk : i % k = k - 1 := by omega
    rw [hmk] at h1 ⊢
    rw [show k - 1 + 1 = k from by omega, Nat.mod_self] at h1
    rw [h1, Nat.zero_add,
      show k - (k - 1 + 1) + k - 1 = k - 1 from by omega,
      Nat.mod_eq_of_lt (show k - 1 < k by omega)]

/-- flip 的前驱重指标：`σ (i+k-1) = (σ i + 1) % k`。 -/
private theorem flipPredModFb {k i : ℕ} (hk1 : 0 < k) :
    k - ((i + k - 1) % k + 1) = (k - (i % k + 1) + 1) % k := by
  have hm : i % k < k := Nat.mod_lt i hk1
  have h1 : (i + k - 1) % k = (i % k + k - 1) % k := by
    have hh : (i % k + (k - 1)) % k = (i + (k - 1)) % k :=
      Nat.ModEq.add_right (k - 1) (Nat.mod_modEq i k)
    rw [show i + k - 1 = i + (k - 1) from by omega,
      show i % k + k - 1 = i % k + (k - 1) from by omega]
    exact hh.symm
  rw [h1]
  rcases Nat.eq_zero_or_pos (i % k) with hzero | hzero
  · rw [hzero, Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega),
      show k - (k - 1 + 1) = 0 from by omega]
    rw [show k - (0 + 1) + 1 = k from by omega, Nat.mod_self]
  · rw [show i % k + k - 1 = i % k - 1 + k from by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega),
      show k - (i % k - 1 + 1) = k - i % k from by omega,
      show k - (i % k + 1) + 1 = k - i % k from by omega,
      Nat.mod_eq_of_lt (show k - i % k < k by omega)]

/-- rot 退一位 `j ↦ (j + k - 1) % k` 在 `[0,k)` 上单射。 -/
private theorem rotInjIioFb {k i j : ℕ} (hik : i < k) (hjk : j < k)
    (h : (i + k - 1) % k = (j + k - 1) % k) : i = j := by
  have h4 : (i + k) % k = (j + k) % k := by
    have hi1 : (i + k) % k = ((i + k - 1) % k + 1) % k := by
      have hh : (i + k - 1 + 1) % k = ((i + k - 1) % k + 1) % k :=
        (Nat.ModEq.add_right 1 (Nat.mod_modEq (i + k - 1) k)).symm
      have e1 : i + k = i + k - 1 + 1 := by omega
      rw [e1]
      exact hh
    have hj1 : (j + k) % k = ((j + k - 1) % k + 1) % k := by
      have hh : (j + k - 1 + 1) % k = ((j + k - 1) % k + 1) % k :=
        (Nat.ModEq.add_right 1 (Nat.mod_modEq (j + k - 1) k)).symm
      have e2 : j + k = j + k - 1 + 1 := by omega
      rw [e2]
      exact hh
    rw [hi1, hj1, h]
  rw [Nat.add_mod_right, Nat.add_mod_right] at h4
  rw [Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hjk] at h4
  exact h4

/-- HOL `BBINDEX_EQ_SYM_0`（YXIONXL2.hl:3182）：BBindex 紧边计数在 flip 重指标
下不变（σ 后继/对合 + rot 单射 + a/dist 对称；HOL 的 CARD_IMAGE_INJ_EQ 同型），
支撑 `BBPRIME2_SYM_0_fb` 的 min 槽。 -/
theorem BBINDEX_EQ_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbp : BBprimeV39 s vv) :
    BBindexV39 (scsOppV39 s) (fun i => -(peropp vv k i)) = BBindexV39 s vv := by
  have hk1 : 0 < k := by have := hiscs.2.1; omega
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  obtain ⟨-, -, -, -, -, -, -, hpa, -, -, -, -, hsym5, -, -, -, -, -, -, -, -⟩ := hiscs
  have hasymA : ∀ i j, s.a i j = s.a j i := fun i j => (hsym5 i j).1
  have hpa' : Periodic2 s.a k := by
    rw [← hk]
    exact hpa
  have hper : Periodic vv k := by
    have h := hbp.1.2.1
    rw [hk] at h
    exact h
  show {i | i < (scsOppV39 s).k ∧ (scsOppV39 s).a i (i + 1)
      = dist (-(peropp vv k i)) (-(peropp vv k (i + 1)))}.ncard
    = {i | i < s.k ∧ s.a i (i + 1) = dist (vv i) (vv (i + 1))}.ncard
  rw [hK, hk]
  -- B（flip 形紧边集）= flip '' A'（j → j-1 形紧边集），ncard 经单射传输；
  -- A' = rot '' A（rot 退一位 + 对称传输），两步计数相等。
  have hBset : {i | i < k ∧ (scsOppV39 s).a i (i + 1)
        = dist (-(peropp vv k i)) (-(peropp vv k (i + 1)))}
      = {i | i < k ∧ s.a (k - (i % k + 1)) ((k - (i % k + 1) + k - 1) % k)
          = dist (vv (k - (i % k + 1))) (vv ((k - (i % k + 1) + k - 1) % k))} := by
    ext i
    simp only [Set.mem_setOf_eq, peropp]
    have hAop : (scsOppV39 s).a i (i + 1)
        = s.a (k - (i % k + 1)) (k - ((i + 1) % k + 1)) := by
      have h0 : (scsOppV39 s).a i (i + 1) = peropp2 s.a s.k i (i + 1) := rfl
      rw [h0, hk]
      rfl
    rw [hAop, flipSuccModFb hk1, distNegNegFb]
  have hA'fin : {j | j < k ∧ s.a j ((j + k - 1) % k)
        = dist (vv j) (vv ((j + k - 1) % k))}.Finite :=
    Set.Finite.subset (Set.finite_Iio k) (fun i hi => hi.1)
  have hInj : Set.InjOn (fun j => k - (j % k + 1)) {j | j < k ∧ s.a j ((j + k - 1) % k)
        = dist (vv j) (vv ((j + k - 1) % k))} := fun a ha b hb hab =>
    flipInjIioFb ha.1 hb.1 hab
  have hBimg : {i | i < k ∧ s.a (k - (i % k + 1)) ((k - (i % k + 1) + k - 1) % k)
        = dist (vv (k - (i % k + 1))) (vv ((k - (i % k + 1) + k - 1) % k))}
      = (fun j => k - (j % k + 1)) '' {j | j < k ∧ s.a j ((j + k - 1) % k)
          = dist (vv j) (vv ((j + k - 1) % k))} := by
    ext i
    constructor
    · rintro ⟨hik, hcond⟩
      refine ⟨k - (i % k + 1), ⟨by omega, hcond⟩, ?_⟩
      show k - ((k - (i % k + 1)) % k + 1) = i
      exact flipInvIioFb hik
    · rintro ⟨j, hj, hje⟩
      have hje' : k - (j % k + 1) = i := hje
      subst hje'
      refine ⟨by omega, ?_⟩
      rw [flipInvIioFb hj.1]
      exact hj.2
  have hInjR : Set.InjOn (fun j => (j + k - 1) % k) {j | j < k ∧ s.a j ((j + k - 1) % k)
        = dist (vv j) (vv ((j + k - 1) % k))} := fun a ha b hb hab =>
    rotInjIioFb ha.1 hb.1 hab
  have hA'iff : ∀ j : ℕ, j < k →
      (j ∈ {j2 | j2 < k ∧ s.a j2 ((j2 + k - 1) % k)
            = dist (vv j2) (vv ((j2 + k - 1) % k))} ↔
        (j + k - 1) % k ∈ {i2 | i2 < k ∧ s.a i2 (i2 + 1)
            = dist (vv i2) (vv (i2 + 1))}) := by
    intro j hjk
    rcases Nat.eq_zero_or_pos j with hzero | hzero
    · subst hzero
      constructor
      · rintro ⟨-, hcond⟩
        refine ⟨Nat.mod_lt _ hk1, ?_⟩
        rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega)] at hcond
        rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega),
          show k - 1 + 1 = k from by omega]
        have hv0 : (vv k : V3) = vv 0 := by simpa using hper 0
        have hpa2 := (hpa' (k - 1) 0).2
        rw [Nat.zero_add] at hpa2
        rw [hpa2, hasymA (k - 1) 0, hv0, dist_comm]
        exact hcond
      · rintro ⟨-, hcondA⟩
        refine ⟨hjk, ?_⟩
        rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega)]
        have hv0 : (vv k : V3) = vv 0 := by simpa using hper 0
        have hpa2 := (hpa' (k - 1) 0).2
        rw [Nat.zero_add] at hpa2
        rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega),
          show k - 1 + 1 = k from by omega, hpa2, hasymA (k - 1) 0, hv0, dist_comm] at hcondA
        exact hcondA
    · have hrj : (j + k - 1) % k = j - 1 := by
        rw [show j + k - 1 = j - 1 + k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      constructor
      · rintro ⟨-, hcond⟩
        refine ⟨Nat.mod_lt _ hk1, ?_⟩
        rw [hrj] at hcond ⊢
        rw [show j - 1 + 1 = j from by omega]
        rw [hasymA j (j - 1), dist_comm] at hcond
        exact hcond
      · rintro ⟨-, hcondA⟩
        refine ⟨hjk, ?_⟩
        rw [hrj]
        rw [hrj, show j - 1 + 1 = j from by omega, hasymA (j - 1) j, dist_comm] at hcondA
        exact hcondA
  have hA'img : {i | i < k ∧ s.a i (i + 1) = dist (vv i) (vv (i + 1))}
      = (fun j => (j + k - 1) % k) '' {j | j < k ∧ s.a j ((j + k - 1) % k)
          = dist (vv j) (vv ((j + k - 1) % k))} := by
    ext i
    constructor
    · rintro ⟨hik, hcond⟩
      have hj : (i + 1) % k < k := Nat.mod_lt _ hk1
      have hr : ((i + 1) % k + k - 1) % k = i := by
        have e1 : ((i + 1) % k + (k - 1)) % k = (i + 1 + (k - 1)) % k :=
          Nat.ModEq.add_right (k - 1) (Nat.mod_modEq (i + 1) k)
        rw [show (i + 1) % k + k - 1 = (i + 1) % k + (k - 1) from by omega, e1,
          show i + 1 + (k - 1) = i + k from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hik]
      refine ⟨(i + 1) % k, (hA'iff ((i + 1) % k) hj).mpr ?_, hr⟩
      rw [hr]
      exact ⟨hik, hcond⟩
    · rintro ⟨j, hj, hje⟩
      have hje' : (j + k - 1) % k = i := hje
      subst hje'
      exact (hA'iff j hj.1).mp hj
  rw [hBset, hBimg, (Set.ncard_image_iff hA'fin).mpr hInj, hA'img,
    (Set.ncard_image_iff hA'fin).mpr hInjR]

/-- HOL `BBINDEX_MIN_SYM_0`（YXIONXL2.hl:3343）：BBindex_min 在 `scs_opp_v39`
下不变（像集相等 + `BBINDEX_EQ_SYM_0_fb` + `BBPRIME_EQ_OPP_SYM_0_fb` 于对合侧）。 -/
theorem BBINDEX_MIN_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbp : BBprimeV39 s vv) :
    BBindexMinV39 (scsOppV39 s) = BBindexMinV39 s := by
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hiscsO : isScsV39 (scsOppV39 s) := isScsOppFb s hiscs
  have himg : BBindexV39 (scsOppV39 s) '' BBprimeV39 (scsOppV39 s)
      = BBindexV39 s '' BBprimeV39 s := by
    ext n
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : BBprimeV39 s (fun i => -(peropp w k i)) := by
        have h := BBPRIME_EQ_OPP_SYM_0_fb (scsOppV39 s) w k hK hiscsO hk3 hw
        rwa [SCS_OPP_REFL_fb s hiscs] at h
      refine ⟨fun i => -(peropp w k i), hw', ?_⟩
      have h := BBINDEX_EQ_SYM_0_fb (scsOppV39 s) w k hK hiscsO hk3 hw
      rwa [SCS_OPP_REFL_fb s hiscs] at h
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => -(peropp v k i), BBPRIME_EQ_OPP_SYM_0_fb s v k hk hiscs hk3 hv,
        BBINDEX_EQ_SYM_0_fb s v k hk hiscs hk3 hv⟩
  show minNum (BBindexV39 (scsOppV39 s) '' BBprimeV39 (scsOppV39 s))
    = minNum (BBindexV39 s '' BBprimeV39 s)
  rw [himg]

/-- HOL `BBPRIME2_SYM_0`（YXIONXL2.hl:3355）：BBprime2 对 `scs_opp_v39` +
负 peropp 实现的对称（BBprime 槽 = BBPRIME_EQ_OPP_SYM_0_fb；min 槽 =
BBINDEX_MIN_SYM_0_fb + BBINDEX_EQ_SYM_0_fb）。 -/
theorem BBPRIME2_SYM_0_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hbp2 : BBprime2V39 s vv) :
    BBprime2V39 (scsOppV39 s) (fun i => -(peropp vv k i)) := by
  simp only [BBprime2V39, Set.mem_setOf_eq]
  refine ⟨BBPRIME_EQ_OPP_SYM_0_fb s vv k hk hiscs hk3 hbp2.1, ?_⟩
  rw [BBINDEX_MIN_SYM_0_fb s vv k hk hiscs hk3 hbp2.1,
    BBINDEX_EQ_SYM_0_fb s vv k hk hiscs hk3 hbp2.1]
  exact hbp2.2

/-- HOL `MM_SCS_OPP`（YXIONXL2.hl:3370）：MMs 对 `scs_opp_v39` + 负 peropp
实现的对称（BBprime2 槽 = BBPRIME2_SYM_0_fb；str 槽 = 原族 fan 非共线 +
AZIM_NEG_fb + flip 后继/前驱重指标 + 周期传输；lo/hi/am/bm 四槽纯传输）。 -/
theorem MM_SCS_OPP_fb (s : ScsV39) (vv : ℕ → V3) (k : ℕ)
    (hk : s.k = k) (hiscs : isScsV39 s) (hk3 : ¬(k ≤ 3)) (hmm : MMsV39 s vv) :
    MMsV39 (scsOppV39 s) (fun i => -(peropp vv k i)) := by
  have hK : (scsOppV39 s).k = k := by show s.k = k; exact hk
  have hk1 : 0 < k := by have := hiscs.2.1; omega
  obtain ⟨hbp2, hstr0, hlo0, hhi0, ham0, hbm0⟩ := hmm
  have hbb : BBsV39 s vv := hbp2.1.1
  have hper : Periodic vv k := by
    have h := hbb.2.1
    rw [hk] at h
    exact h
  -- 原族 convex local fan（str 槽非共线的来源）
  have hconv0 : ConvexLocalFan (Set.image vv Set.univ)
      (Set.image (fun i : ℕ => ({vv i, vv (i + 1)} : Set V3)) Set.univ)
      (Set.image (fun i : ℕ => (vv i, vv (i + 1))) Set.univ) := by
    rcases hbb.2.2.2 with h3 | hcf
    · rw [hk] at h3
      exact absurd h3 hk3
    · simpa only [Set.image_univ] using hcf
  obtain ⟨hlf0, -⟩ := hconv0
  obtain ⟨hfan0, -, -⟩ := hlf0
  have hEcol : ∀ m : ℕ, ¬ Collinear ℝ (insert 0 ({vv m, vv (m + 1)} : Set V3)) :=
    fun m => hfan0.2.2.2.2.1 _ ⟨m, Set.mem_univ _, rfl⟩
  simp only [MMsV39, Set.mem_setOf_eq]
  refine ⟨BBPRIME2_SYM_0_fb s vv k hk hiscs hk3 hbp2, ?_, ?_, ?_, ?_, ?_⟩
  · -- str 槽：flip 后继/前驱重指标 + AZIM_NEG_fb + 周期传输
    intro i hi
    rw [hK]
    simp only [peropp]
    rw [show i + (k - 1) = i + k - 1 from by omega, flipSuccModFb hk1,
      flipPredModFb hk1]
    have hj : k - (i % k + 1) < k := by omega
    have hstrj : s.str (k - (i % k + 1)) := by
      rw [← hk]
      exact hi
    have hstr1 := hstr0 (k - (i % k + 1)) hstrj
    rw [hk, show k - (i % k + 1) + (k - 1) = k - (i % k + 1) + k - 1 from by omega] at hstr1
    rw [← periodicModFb hper (k - (i % k + 1) + 1),
      ← periodicModFb hper (k - (i % k + 1) + k - 1)] at hstr1
    have hcol2 : ¬ Collinear ℝ ({0, vv (k - (i % k + 1)),
        vv ((k - (i % k + 1) + 1) % k)} : Set V3) := by
      rcases Nat.lt_or_ge (k - (i % k + 1)) (k - 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt (show k - (i % k + 1) + 1 < k by omega)]
        exact hEcol (k - (i % k + 1))
      · have hlast : k - (i % k + 1) = k - 1 := by omega
        rw [hlast, show k - 1 + 1 = k from by omega, Nat.mod_self]
        have hv0 : (vv k : V3) = vv 0 := by simpa using hper 0
        have hE := hEcol (k - 1)
        rw [show (vv (k - 1 + 1) : V3) = vv 0 from by
          rw [show k - 1 + 1 = k from by omega]; exact hv0] at hE
        exact hE
    have hcol1 : ¬ Collinear ℝ ({0, vv (k - (i % k + 1)),
        vv ((k - (i % k + 1) + k - 1) % k)} : Set V3) := by
      rcases Nat.eq_zero_or_pos (k - (i % k + 1)) with hz | hz
      · rw [hz, Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega)]
        have hv0 : (vv k : V3) = vv 0 := by simpa using hper 0
        have hE := hEcol (k - 1)
        rw [show (vv (k - 1 + 1) : V3) = vv 0 from by
          rw [show k - 1 + 1 = k from by omega]; exact hv0] at hE
        rw [pairSetCommFb]
        exact hE
      · rw [show (k - (i % k + 1) + k - 1) % k = k - (i % k + 1) - 1 from by
          rw [show k - (i % k + 1) + k - 1 = k - (i % k + 1) - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
        rw [pairSetCommFb]
        have hE' := hEcol (k - (i % k + 1) - 1)
        rw [show k - (i % k + 1) - 1 + 1 = k - (i % k + 1) from by omega] at hE'
        exact hE'
    rw [AZIM_NEG_fb hcol1 hcol2]
    exact hstr1
  · -- lo 槽
    intro i hi
    show norm (-(peropp vv k i)) = 2
    rw [norm_neg]
    exact hlo0 (k - (i % k + 1)) (by rw [← hk]; exact hi)
  · -- hi 槽
    intro i hi
    show norm (-(peropp vv k i)) = 2 * h0
    rw [norm_neg]
    exact hhi0 (k - (i % k + 1)) (by rw [← hk]; exact hi)
  · -- am 槽
    intro i j
    show s.am (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))
      ≤ dist (-(peropp vv k i)) (-(peropp vv k j))
    rw [hk, distNegNegFb]
    exact ham0 (k - (i % k + 1)) (k - (j % k + 1))
  · -- bm 槽
    intro i j
    show dist (-(peropp vv k i)) (-(peropp vv k j))
      ≤ s.bm (s.k - (i % s.k + 1)) (s.k - (j % s.k + 1))
    rw [hk, distNegNegFb]
    exact hbm0 (k - (i % k + 1)) (k - (j % k + 1))

end Kepler.Text
