/-
Kepler/Text/LocalFanPerimeterGeneric.lean — WSEWPCH generic 支（wave 1，先补桩）。

## 定位

本件是 HOL `Polar_fan.WSEWPCH`（reference/flyspeck/text_formalization/local/
polar_fan.hl:2213）generic 支（:2553-2623，`!v. v IN V ==> interior_angle1
(vec 0) FF v < pi` 的 TRUE 支）的 Lean 装配，把 NKEZBFC 留成显式参数槽：

  `hNKE : 0 ≤ solLocal_p2 E' FF'`  （E', FF' 是 `polarFan V E FF` 的后两分量）

目标式为 `fanPerimeter V E FF ≤ 2 * Real.pi`。NKEZBFC 本体
（HOL `localization.hl:1502`；树内 `LocalAuto2.lean:1606-1607` 的未完成声明）
不在本波范围，由后续波 B/C/D 产出。

## 与 LA7 `WSEWPCH` 的关系 / 将来接线

`LocalAuto7.lean:7335-7337` 的 `WSEWPCH` 是 HOL 五分支归纳的总装（当前未完成）。
本件的 `p13w_generic_perimeter` 就是它 generic（`hia` 真）分支的完整证明，只差一个
具名槽。将来总装车道在 LA14 与 LA7 的共同下游新文件里：

* 用 `hNKE := NKEZBFC_final …`（波 B/C/D 产出）实例化本件；
* 与 `FAN_PERIMETER_LE_2PI_OF_CIRCULAR`（LA7:7134）、`…_OF_LUNAR`（LA7:4838）、
  `…_OF_CARD_LE`（LA7:4014）、straight 支（W12）按 CIZMRRH 三分 + `hia` 分叉
  拼成 `WSEWPCH_final`（新名；LA7 的 `WSEWPCH` 不能原位补——LA7 不能 import LA14，
  见 `SCOUT.md` §0 第 5 条）。

本件**不 import LA14**（EGHNAVX 只在 stepB 需要，不在 generic 支）。

## import 闭包（实测，最小单条）

`Kepler.Text.LocalAuto7`：它直接 import `LocalAuto9`（`SOL_LOFA_EQ_SUM_INANGLE_p9`、
`solLocal_p2/p9`、`convexLocalFan_p2`）、`AzimBridge`（`localFan_data`、
`localFan_p2.of_localFan_p3`、`azimInFan_eq_azimInFan_p3`、
`wedgeInFanGe_eq_wedgeInFanGe_p3`）、`LocalAuto1`（`ConvexLocalFan`）、`Fan`；
`LocalAuto7` 自身提供 `BGMIFTE`、`polarFan`、`fanPerimeter`、`FAN_PERIMETER`、
`P11W_PRIME_INJ`、`LOCAL_FAN_IMP_HEDGE`。传递闭包不含 `LocalAuto14`。
-/
import Kepler.Text.LocalAuto7

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## Local 桥：LA1 `ConvexLocalFan` → LA2 `convexLocalFan_p2` -/

/-- LA1 `ConvexLocalFan` → LA2 `convexLocalFan_p2` 的本地公开桥（不 import LA14）。
证明模式与 LA37 的私有 `la37g5_clf2` 相同：`localFan_p2.of_LocalFan_noIso`
（AzimBridge）+ `azimInFan`/`wedgeInFanGe` 的 p1↔p3 桥（AzimBridge）+
`_p2`/`_p3` 定义相等（rfl）。 -/
theorem p13w_convexLocalFan_p2_of_clf (h : ConvexLocalFan V E FF) :
    convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hfan : FAN 0 V E := (localFan_data hlf).1
  have hsub : FF ⊆ dart1OfFan V E := by
    obtain ⟨-, -, -, -, -, hsub, -⟩ := localFan_data hlf
    exact hsub
  have hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E := LOCAL_FAN_IMP_HEDGE hlf
  refine ⟨localFan_p2.of_LocalFan_noIso hlf hedge, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · have hb : azimInFan d E = azimInFan_p3 d E :=
      azimInFan_eq_azimInFan_p3 hfan (hsub hd)
    show azimInFan_p2 d E ≤ Real.pi
    rw [show azimInFan_p2 d E = azimInFan_p3 d E from rfl, ← hb]
    exact (hcvx d hd).1
  · show V ⊆ wedgeInFanGe_p2 d E
    rw [show wedgeInFanGe_p2 d E = wedgeInFanGe_p3 d E from rfl,
      ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfan (hsub hd)]
    exact (hcvx d hd).2

/-! ## `setSum` 小工具 -/

private theorem p13w_setSum_congr {s : Set V3} {f g : V3 → ℝ}
    (h : ∀ v ∈ s, f v = g v) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : s.Finite
  · simp only [dif_pos hs]
    exact Finset.sum_congr rfl fun v hv =>
      h v ((Set.Finite.mem_toFinset hs).mp hv)
  · simp only [dif_neg hs]

private theorem p13w_setSum_neg (s : Set V3) (f : V3 → ℝ) :
    setSum s (fun v => -f v) = -setSum s f := by
  unfold setSum
  by_cases hs : s.Finite
  · simp only [dif_pos hs, Finset.sum_neg_distrib]
  · simp only [dif_neg hs, neg_zero]

private theorem p13w_setSum_image {s : Set V3} (hs : s.Finite) {p : V3 → V3}
    (hinj : Set.InjOn p s) (f : V3 → ℝ) :
    setSum s (fun v => f (p v)) = setSum (p '' s) f := by
  rw [setSum, setSum, dif_pos hs, dif_pos (hs.image p)]
  refine Finset.sum_nbij (fun v => p v) ?_ ?_ ?_ ?_
  · intro v hv
    exact (Set.Finite.mem_toFinset (hs.image p)).mpr
      ⟨v, (Set.Finite.mem_toFinset hs).mp hv, rfl⟩
  · intro a ha b hb hab
    exact hinj ((Set.Finite.mem_toFinset hs).mp ha)
      ((Set.Finite.mem_toFinset hs).mp hb) hab
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := (Set.Finite.mem_toFinset (hs.image p)).mp hy
    exact ⟨v, (Set.Finite.mem_toFinset hs).mpr hv, rfl⟩
  · intro v hv
    rfl

/-! ## generic 支（HOL polar_fan.hl:2553-2623） -/

/-- **WSEWPCH generic 支（先补桩）**：HOL `Polar_fan.WSEWPCH` 在
`!v. v IN V ==> interior_angle1 (vec 0) FF v < pi` 的 TRUE 支的完整装配。

`hNKE` 是唯一缺口（NKEZBFC 结论 `0 ≤ sol_local E' FF'` 的 p2 渲染；后续波产出）。
其余全部来自 BGMIFTE（五合取）+ `SOL_LOFA_EQ_SUM_INANGLE_p9` + `FAN_PERIMETER`
+ `P11W_PRIME_INJ`。 -/
theorem p13w_generic_perimeter
    {V' : Set V3} {E' : Set (Set V3)} {FF' : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF)
    (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (hp : polarFan V E FF = (V', E', FF'))
    (hNKE : 0 ≤ solLocal_p2 E' FF') :
    fanPerimeter V E FF ≤ 2 * Real.pi := by
  -- BGMIFTE 五合取：polar fan 仍是凸局部扇 + generic + 两弧半
  obtain ⟨hcl', -, -, -, harc2⟩ := BGMIFTE hcl hedge hg hia hp
  -- LA1 → LA2 桥，供 SOL_LOFA 使用（不 import LA14）
  have hcl2 : convexLocalFan_p2 V' E' FF' := p13w_convexLocalFan_p2_of_clf hcl'
  -- SOL_LOFA：solLocal 展开为 2π + Σ(interiorAngle1 − π)
  have hsol := SOL_LOFA_EQ_SUM_INANGLE_p9 (V := V') (E := E') (FF := FF') hcl2
  have hNKE9 : 0 ≤ solLocal_p9 E' FF' := hNKE
  rw [hsol] at hNKE9
  -- 记 S = Σ_{V'}(interiorAngle1 − π)
  set S : ℝ := setSum V' (fun v => interiorAngle1_p2 0 FF' v - Real.pi) with hS
  have hNKE' : 0 ≤ 2 * Real.pi + S := by simpa [hS] using hNKE9
  -- 极映射 p v = v × ρv，V' = p '' V，p 在 V 上单射
  set p : V3 → V3 := fun v => cross3 v (rhoNode1 FF v) with hpdef
  have hV' : V' = p '' V := by
    have h1 : (polarFan V E FF).1 = V' := congrArg (fun t => t.1) hp
    have h2 : (polarFan V E FF).1 = p '' V := rfl
    rw [h2] at h1
    exact h1.symm
  have hVfin : V.Finite := by
    have hfan : FAN 0 V E := (localFan_data hcl.1).1
    exact hfan.2.2.1.1
  have hinj : Set.InjOn p V := by
    intro a ha b hb hab
    exact P11W_PRIME_INJ hcl hedge hg hia a ha b hb hab
  -- S = −Σ_V (π − interiorAngle1 (p v))
  have hSimg : setSum V' (fun v => interiorAngle1_p2 0 FF' v - Real.pi)
      = setSum V (fun v => interiorAngle1_p2 0 FF' (p v) - Real.pi) := by
    rw [hV']
    exact (p13w_setSum_image hVfin hinj _).symm
  have hSneg : setSum V (fun v => interiorAngle1_p2 0 FF' (p v) - Real.pi)
      = -setSum V (fun v => Real.pi - interiorAngle1_p2 0 FF' (p v)) := by
    rw [← p13w_setSum_neg]
    exact p13w_setSum_congr (fun v _ => by ring)
  have hSeq : S = -setSum V (fun v => Real.pi - interiorAngle1_p2 0 FF' (p v)) := by
    rw [hS, hSimg, hSneg]
  -- fanPerimeter = Σ_V arcV 0 v (ρv) = Σ_V (π − interiorAngle1 FF' (p v))
  have hper : fanPerimeter V E FF
      = setSum V (fun v => Real.pi - interiorAngle1_p2 0 FF' (p v)) := by
    rw [FAN_PERIMETER hcl.1 hedge]
    refine p13w_setSum_congr (fun v hv => ?_)
    exact (harc2 v hv).1
  -- 收口：perimeter = −S，0 ≤ 2π + S ⇒ perimeter ≤ 2π
  have hperS : fanPerimeter V E FF = -S := by
    rw [hper]
    linarith [hSeq]
  linarith

end Kepler.Text

/-- 接线探针：`hNKE` 直接写在 `polarFan` 的三元组投影上（W11 总装最省事的调用形）。 -/
example {V : Set Kepler.Geom.V3} {E : Set (Set Kepler.Geom.V3)}
    {FF : Set (Kepler.Geom.V3 × Kepler.Geom.V3)}
    (hcl : Kepler.Text.ConvexLocalFan V E FF)
    (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Kepler.Text.Generic V E)
    (hia : ∀ v ∈ V, Kepler.Text.interiorAngle1 (0 : Kepler.Geom.V3) FF v < Real.pi)
    (hNKE : 0 ≤ Kepler.Text.solLocal_p2 (Kepler.Text.polarFan V E FF).2.1
      (Kepler.Text.polarFan V E FF).2.2) :
    Kepler.Text.fanPerimeter V E FF ≤ 2 * Real.pi :=
  Kepler.Text.p13w_generic_perimeter hcl hedge hg hia rfl hNKE

/-! ## 探针（岛编译时随文件执行） -/
#print axioms Kepler.Text.p13w_convexLocalFan_p2_of_clf
#print axioms Kepler.Text.p13w_generic_perimeter
