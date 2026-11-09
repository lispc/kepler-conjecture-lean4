/-
LocalAuto7W13B: W13a-ii — straight 支 `ConvexLocalFan V' E' FF'` 的 convex 半收口。

HOL `Polar_fan.WSEWPCH` straight 支（`scripts/local/polar_fan.hl:3255-3390`）逐段移植：

* `p13a_ncol_ivs_rho`：`¬ Collinear3 0 ιv ρv`（`COLLINEAR_WITHIN_AFF_GE_COLLINEAR`
  配 `p12b_straight_mem`，撞 `LOCAL_FAN_CHARACTER_OF_RHO_NODE2`）；
* `p13a_azim_same`：`azim 0 w (r w) z = azim 0 w (ρw) z`（HOL 3281-3305；`ρw ≠ v`
  时 rfl，`w = ιv` 时 `AZIM_SAME_WITHIN_AFF_GE` 把参考方向 `ρv` 换成 `v`）；
* `p13a_azim_le_pi`：`azimInFan (w, r w) E' ≤ π`（HOL 3306-3313；`pre w ∈ V' ⊆ V`，
  `IN_V_IMP_AZIM_LESS_PI` 在原扇上直接给界——两支统一，无需 `pre w` 拆分）；
* `p13a_wedgeInFanGe_FF'`：`wedgeInFanGe (w, r w) E' = wedgeGe 0 w (r w) (pre w)`
  （新扇 `localFan_p2` + `DETERMINE_WEDGE_IN_FAN` + `p12e_azim_fwd`）；
* `p13a_wedge`：`V' ⊆ wedgeInFanGe (w, r w) E'`（HOL 3314-3390；旧凸性 + `w = ρv`
  支的 `AZIM_SAME_WITHIN_AFF_GE_ALT` 同向改写）；
* `p13a_convex`：`ConvexLocalFan V' E' FF'` 装配（`p12p_LocalFan` + 两合取）。

W12E–P、W13A、LA7 零改动；唯一新增 import 是 `LocalFanPerimeterGeneric`
（`p13w_convexLocalFan_p2_of_clf`，只 import `LocalAuto7`，与 W12P 无环）。
-/
import Kepler.Text.LocalAuto7W13A
import Kepler.Text.LocalFanPerimeterGeneric

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 共线三点重排（`Collinear3` 是集合，需交换第二、三点） -/

/-- `Collinear3 a c b → Collinear3 a b c`。 -/
private theorem p13b_collinear3_comm {a b c : V3} (h : Collinear3 a c b) :
    Collinear3 a b c := by
  unfold Collinear3 at h ⊢
  rwa [show ({a, b, c} : Set V3) = {a, c, b} from by rw [Set.pair_comm b c]]

/-- 否命题版。 -/
private theorem p13b_ncollinear3_comm {a b c : V3} (h : ¬ Collinear3 a c b) :
    ¬ Collinear3 a b c :=
  fun hbc => h (p13b_collinear3_comm hbc)

/-! ## 支 2 的非共线前提（HOL 3299-3305 第三合取） -/

/-- **`¬ Collinear3 0 ιv ρv`**：若 `0, ιv, ρv` 共线，`COLLINEAR_WITHIN_AFF_GE_COLLINEAR`
配 `p12b_straight_mem`（`v ∈ affGe {0}{ιv,ρv}`）把 `v` 拉进同一直线，撞
`LOCAL_FAN_CHARACTER_OF_RHO_NODE2`。 -/
theorem p13a_ncol_ivs_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    ¬ Collinear3 (0 : V3) (ivsRhoNode1 FF v) (rhoNode1 FF v) := by
  intro hcol
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  exact LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv
    (COLLINEAR_WITHIN_AFF_GE_COLLINEAR 0 (ivsRhoNode1 FF v) v (rhoNode1 FF v)
      (p12b_straight_mem hcl hedge hg hv hpi) hcol)

/-! ## 参考方向改写：`r w` ↔ `ρw`（HOL 3281-3305） -/

/-- **`azim 0 w (r w) z = azim 0 w (ρw) z`**。`ρw ≠ v` 时 `r w = ρw`（rfl）；
`ρw = v`（此时 `w = ιv`）时 `AZIM_SAME_WITHIN_AFF_GE` 把参考方向从 `ρv` 换成 `v`
（`v ∈ affGe {0}{ιv,ρv}` 由 `p12b_straight_mem` 供，两非共线前提见上）。 -/
theorem p13a_azim_same {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi)
    {w : V3} (hw : w ∈ p12b_V V v) :
    ∀ z : V3, azim 0 w (p12b_R FF v w) z = azim 0 w (rhoNode1 FF w) z := by
  intro z
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  unfold p12b_R
  by_cases hc : rhoNode1 FF w = v
  · rw [if_pos hc, hc]
    have hwivs : w = ivsRhoNode1 FF v := by
      have hid : ivsRhoNode1 FF (rhoNode1 FF w) = w := IVS_RHO_IDD h2 hw.1
      rw [hc] at hid
      exact hid.symm
    rw [hwivs]
    exact (AZIM_SAME_WITHIN_AFF_GE 0 (ivsRhoNode1 FF v) v (rhoNode1 FF v) z
      (p12b_straight_mem hcl hedge hg hv hpi)
      (p13b_ncollinear3_comm (LOFA_IMP_NOT_COLL_IVS h2 hv))
      (p13a_ncol_ivs_rho hcl hedge hg hv hpi)).symm
  · rw [if_neg hc]

/-! ## azim 半（HOL 3306-3313） -/

/-- **`azimInFan (w, r w) E' ≤ π`**：`p13a_azimInFan_FF'` → `p13a_azim_same` →
`IN_V_IMP_AZIM_LESS_PI`。关键是 `pre w ∈ V' ⊆ V`，故原扇 `IN_V_IMP_AZIM_LESS_PI`
在顶点 `w` 上对 `pre w` 直接给界——`pre w = ιw` 与 `pre w = ιv` 两支**无需拆分**。 -/
theorem p13a_azim_le_pi {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) {w : V3} (hw : w ∈ p12b_V V v) :
    azimInFan (w, p12b_R FF v w) (p12b_E V FF v) ≤ Real.pi := by
  rw [p13a_azimInFan_FF' hcl hedge hv hw0 hcard3 hw]
  rw [p13a_azim_same hcl hedge hg hv hpi hw]
  exact IN_V_IMP_AZIM_LESS_PI (p13w_convexLocalFan_p2_of_clf hcl) w hw.1
    (p12e_pre hcl hedge hv w) (p12e_pre_spec hcl hedge hv hw).1.1

/-! ## 支 A 的同向改写：从 `ρv` 看 `ιv` 与 `v`（HOL 3336-3355） -/

/-- **`azim 0 (ρv) (ρ(ρv)) ιv = azim 0 (ρv) (ρ(ρv)) v`**：
`AZIM_SAME_WITHIN_AFF_GE_ALT` 配 `p12b_straight_mem`（`v ∈ affGe {0}{ρv,ιv}`），
把「`v` 在 `ιv` 与 `ρv` 之间 ⇒ 从 `ρv` 看二者同向」落成 azim 等式。 -/
private theorem p13b_azim_rho_ivs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v : V3} (hv : v ∈ V)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) :
    azim 0 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)) (ivsRhoNode1 FF v)
      = azim 0 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)) v := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hmem : v ∈ affGe ({0} : Set V3)
      ({rhoNode1 FF v, ivsRhoNode1 FF v} : Set V3) := by
    rw [Set.pair_comm]
    exact p12b_straight_mem hcl hedge hg hv hpi
  have h1 : ¬ Collinear3 (0 : V3) (rhoNode1 FF v) v :=
    p13b_ncollinear3_comm (LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 hv)
  have h2' : ¬ Collinear3 (0 : V3) (rhoNode1 FF v) (ivsRhoNode1 FF v) := by
    intro hcol
    exact LOFA_IMP_NOT_COLL_IVS h2 hv
      (COLLINEAR_WITHIN_AFF_GE_COLLINEAR 0 (rhoNode1 FF v) v (ivsRhoNode1 FF v)
        hmem hcol)
  exact (AZIM_SAME_WITHIN_AFF_GE_ALT 0 (rhoNode1 FF v) v (ivsRhoNode1 FF v)
    (rhoNode1 FF (rhoNode1 FF v)) hmem h1 h2').symm

/-! ## `pre w` 的两种识别 -/

/-- `w ≠ ρv` 时 `pre w = ιw`（`r (pre w) = w`；若 `ρ(pre w) = v` 则 `w = ρv`）。 -/
theorem p13b_pre_eq_ivs {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v)
    (hne : w ≠ rhoNode1 FF v) :
    p12e_pre hcl hedge hv w = ivsRhoNode1 FF w := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  obtain ⟨hqV, hrq⟩ := p12e_pre_spec hcl hedge hv hw
  have hqV' : p12e_pre hcl hedge hv w ∈ V := hqV.1
  unfold p12b_R at hrq
  by_cases hc : rhoNode1 FF (p12e_pre hcl hedge hv w) = v
  · rw [if_pos hc] at hrq
    exact absurd hrq.symm hne
  · rw [if_neg hc] at hrq
    have hid : ivsRhoNode1 FF (rhoNode1 FF (p12e_pre hcl hedge hv w))
        = p12e_pre hcl hedge hv w := IVS_RHO_IDD h2 hqV'
    rw [hrq] at hid
    exact hid.symm

/-- `w = ρv` 时 `pre w = ιv`（`r ιv = ρv` 且 `r` 在 `V'` 上单射）。 -/
theorem p13b_pre_of_eq_rho {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) {w : V3} (hw : w ∈ p12b_V V v)
    (heq : w = rhoNode1 FF v) :
    p12e_pre hcl hedge hv w = ivsRhoNode1 FF v := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hivsV : ivsRhoNode1 FF v ∈ p12b_V V v :=
    ⟨IVS_RHO_NODE1_IN_V hcl.1 hedge v hv, IVS_RHO_NODE_DIFF_ID h2 hv⟩
  have hpre : p12b_R FF v (ivsRhoNode1 FF v) = rhoNode1 FF v := by
    unfold p12b_R
    rw [if_pos (show rhoNode1 FF (ivsRhoNode1 FF v) = v from
      LOCAL_FAN_RHO_NODE_IVS h2 hv)]
  obtain ⟨hqV, hrq⟩ := p12e_pre_spec hcl hedge hv hw
  exact p12b_R_inj hcl hedge hv hqV hivsV (by rw [hrq, heq, hpre])

/-! ## 旧扇 wedge 界 -/

/-- 旧扇在 dart `(w, ρw)` 的 wedge 界（`hcl.2` 的 wedge 半 + `WEDGE_IN_FAN_RHOND_IVS_RHOND`）。 -/
private theorem p13b_old_wedge_le {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {w u : V3} (hw : w ∈ V) (hu : u ∈ V) :
    azim 0 w (rhoNode1 FF w) u ≤ azim 0 w (rhoNode1 FF w) (ivsRhoNode1 FF w) := by
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  have hcvx2 : convexLocalFan_p2 V E FF := p13w_convexLocalFan_p2_of_clf hcl
  have hdart : (w, rhoNode1_p2 FF w) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS h2).1 w hw
  have hmem : u ∈ wedgeInFanGe_p2 (w, rhoNode1_p2 FF w) E := (hcvx2.2 _ hdart).2 hu
  rw [WEDGE_IN_FAN_RHOND_IVS_RHOND h2 hw] at hmem
  exact hmem.2

/-! ## 新扇 wedge 的集合形（`sigmaFan` → `pre w`） -/

/-- **`wedgeInFanGe (w, r w) E' = wedgeGe 0 w (r w) (pre w)`**：新扇的
`localFan_p2` + `DETERMINE_WEDGE_IN_FAN` 把 `wedgeInFanGe_p2` 展开成
`azimCycle_p2`，再由 `p12e_azim_fwd`（`azimCycle_p3 (EE_p3 w E') 0 w (r w) = pre w`）
收成 `pre w`；LA1↔p3 的换算由 `wedgeInFanGe_eq_wedgeInFanGe_p3`（配 `p12c_FAN`）供。 -/
theorem p13a_wedgeInFanGe_FF' {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) {w : V3} (hw : w ∈ p12b_V V v) :
    wedgeInFanGe (w, p12b_R FF v w) (p12b_E V FF v)
      = wedgeGe 0 w (p12b_R FF v w) (p12e_pre hcl hedge hv w) := by
  have hfan' : FAN (0:V3) (p12b_V V v) (p12b_E V FF v) :=
    p12c_FAN hcl hedge hg hv hpi hcard
  have hd1 : (w, p12b_R FF v w) ∈ dart1OfFan (p12b_V V v) (p12b_E V FF v) :=
    ⟨w, hw, rfl⟩
  rw [wedgeInFanGe_eq_wedgeInFanGe_p3 hfan' hd1]
  have hlf2' : localFan_p2 (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) :=
    localFan_p2.of_localFan_p3 (p12p_localFan_p3 hcl hedge hg hv hpi hcard hw0 hcard3)
  have hdFF' : (w, p12b_R FF v w) ∈ p12b_FF V FF v := ⟨w, hw, rfl⟩
  rw [show wedgeInFanGe_p3 (w, p12b_R FF v w) (p12b_E V FF v)
      = wedgeInFanGe_p2 (w, p12b_R FF v w) (p12b_E V FF v) from rfl]
  rw [DETERMINE_WEDGE_IN_FAN hlf2' hdFF']
  rw [show azimCycle_p2 (EE_p2 w (p12b_E V FF v)) 0 w (p12b_R FF v w)
      = azimCycle_p3 (EE_p3 w (p12b_E V FF v)) 0 w (p12b_R FF v w) from rfl]
  rw [p12e_azim_fwd hcl hedge hv hw]
  rfl

/-! ## wedge 半（HOL 3314-3390） -/

/-- **`V' ⊆ wedgeInFanGe (w, r w) E'`**。`p13a_wedgeInFanGe_FF'` 换成
`wedgeGe 0 w (r w) (pre w)`，再用 `p13a_azim_same` 把参考方向与界都换成 `ρw`：

* `w ≠ ρv`：`pre w = ιw`，目标即旧扇 `(w, ρw)` 的 wedge 界（`u ∈ V' ⊆ V`）；
* `w = ρv`：`pre w = ιv`，旧扇 `(ρv, ρ(ρv))` 的界给到 `ι(ρv) = v`，再由
  `p13b_azim_rho_ivs`（从 `ρv` 看 `ιv` 与 `v` 同向）换成 `ιv`。 -/
theorem p13a_wedge {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) {w : V3} (hw : w ∈ p12b_V V v) :
    ∀ u ∈ p12b_V V v, u ∈ wedgeInFanGe (w, p12b_R FF v w) (p12b_E V FF v) := by
  intro u hu
  have h2 : localFan_p2 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
  rw [p13a_wedgeInFanGe_FF' hcl hedge hg hv hw0 hpi hcard hcard3 hw]
  refine ⟨azim_nonneg _ _ _ _, ?_⟩
  rw [p13a_azim_same hcl hedge hg hv hpi hw u,
    p13a_azim_same hcl hedge hg hv hpi hw (p12e_pre hcl hedge hv w)]
  by_cases hcase : w = rhoNode1 FF v
  · have hpre := p13b_pre_of_eq_rho hcl hedge hv hw hcase
    have hρV : rhoNode1 FF v ∈ V := by rw [← hcase]; exact hw.1
    rw [hpre, hcase]
    refine (p13b_old_wedge_le hcl hedge hρV hu.1).trans ?_
    rw [show ivsRhoNode1 FF (rhoNode1 FF v) = v from IVS_RHO_IDD h2 hv]
    exact le_of_eq (p13b_azim_rho_ivs hcl hedge hg hv hpi).symm
  · rw [p13b_pre_eq_ivs hcl hedge hv hw hcase]
    exact p13b_old_wedge_le hcl hedge hw.1 hu.1

/-! ## 装配（A1 形） -/

/-- **`ConvexLocalFan V' E' FF'`**：`p12p_LocalFan`（L 块）+ azim 半 + wedge 半。 -/
theorem p13a_convex {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (hg : Generic V E) {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hpi : interiorAngle1 (0 : V3) FF v = Real.pi) (hcard : 3 ≤ V.ncard)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ConvexLocalFan (p12b_V V v) (p12b_E V FF v) (p12b_FF V FF v) := by
  refine ⟨p12p_LocalFan hcl hedge hg hv hpi hcard hw0 hcard3, ?_⟩
  rintro ⟨x1, x2⟩ hx
  obtain ⟨w, hw, hd⟩ := hx
  rw [hd]
  exact ⟨p13a_azim_le_pi hcl hedge hg hv hw0 hcard3 hpi hw,
    p13a_wedge hcl hedge hg hv hw0 hpi hcard hcard3 hw⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p13a_ncol_ivs_rho
#print axioms Kepler.Text.p13a_azim_same
#print axioms Kepler.Text.p13a_azim_le_pi
#print axioms Kepler.Text.p13a_wedgeInFanGe_FF'
#print axioms Kepler.Text.p13a_wedge
#print axioms Kepler.Text.p13a_convex

end Kepler.Text
