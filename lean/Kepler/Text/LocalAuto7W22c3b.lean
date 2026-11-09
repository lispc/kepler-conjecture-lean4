/-
LocalAuto7W22c3b: W22c-iii-a 的 ③④（环境性延后件的编排者补完）。

* ③ `p22c3_fullySurrounded_cardFaceGe3`：`FullySurrounded` + FAN ⇒ 度 > 1
  （`p22a_fs_ncard_gt1`）⇒ ② 直接给 `3 ≤ face.ncard`。
* ④ `p22c3_hcard_bridge`：把 `3 ≤ (hypermapOfFanTl …).face x).ncard` 桥到
  W22c-ii 条件形的槽形 `2 < FF.ncard`（`FF = H1.face x`，`H1 : IsHypOn_p10`）。
  桥 = 面映射等式：`IsHypOn_p10` 给 `⇑H1.faceMap = ffOfHyp_p3`，
  `ffOfHyp_p3_eq_faceMap_fun`（AzimBridge:353）给 `= ⇑(fanHyp hfan).faceMap`，
  `fanHyp`/`hypermapOfFanTl` 都是 `hypermapOfFan` 的实例包装（faceMap `rfl` 级）。

对照：`aq1-fin` 车道原 ③④ 因「岛池缺 olean」延后；编排者核池后确认
`LocalAuto7W21/W22a/W22b/W22c` olean 均在 `.lake/build/lib/lean/Kepler/Text/`，
此事为环境误判（ERRATA 记 `续702`），故就地补完。
-/
import Kepler.Text.JcajyduAqLeafW22c3a
import Kepler.Text.LocalAuto7W22a
import Kepler.Text.LocalAuto7W22ciib
import Kepler.Text.AzimBridge

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **③ `FullySurrounded ⇒ face ≥ 3`**：`FullySurrounded` + FAN 给度 > 1
（`p22a_fs_ncard_gt1`），再走 ② 的环排除。 -/
theorem p22c3_fullySurrounded_cardFaceGe3 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E)
    {x : V3 × V3} (hx : x ∈ dartOfFan V E) :
    3 ≤ ((hypermapOfFanTl V E hfan).face x).ncard :=
  p22c3_cardSetOfEdgeGt1ImpCardFaceGe3 hfan (p22a_fs_ncard_gt1 hfan hfs) hx

/-- **④ `hcard` 槽桥**：`IsHypOn_p10 0 V E H1` 的 `H1.face x` 与
`hypermapOfFanTl V E hfan` 的 `face x` 相同（面映射 `rfl` 级一致），
故 `3 ≤` 给出条件形所需的 `2 < FF.ncard`。 -/
theorem p22c3_hcard_bridge {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)}
    (h1 : IsHypOn_p10 0 V E H1) {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V)
    {FF : Set (V3 × V3)} (hFF : FF = H1.face x) (hfs : FullySurrounded V E) :
    2 < FF.ncard := by
  have hxE : {x.1, x.2} ∈ E := p22c2_dartsOfHyp_subset hfs hx
  have hxDF : x ∈ dartOfFan V E := Or.inr hxE
  have h3 := p22c3_fullySurrounded_cardFaceGe3 hfan hfs hxDF
  have hface : H1.face x = (hypermapOfFanTl V E hfan).face x := by
    have hperm : H1.faceMap = (hypermapOfFanTl V E hfan).faceMap := by
      apply Equiv.ext
      intro d
      have h1f : H1.faceMap d = ffOfHyp_p3 0 V E d := congrFun h1.2.2.2 d
      rw [h1f, ffOfHyp_p3_eq_faceMap hfan d]
      rfl
    show orbitMap H1.faceMap x = orbitMap (hypermapOfFanTl V E hfan).faceMap x
    rw [hperm]
  rw [hFF, hface]
  omega

/-- **条件形的 `hcard` 消槽形**：`p22c3_hcard_bridge` 填掉 `hcard`，只剩 `hfs`/`hsimple`/`hno`。 -/
theorem p22c2_f_surr_localization_cond_noHcard {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hfs : FullySurrounded V E) (hsimple : H2.Simple)
    (hno : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF)) :
    LocalFan (vPrime_p3 V FF) (ePrime_p3 E FF) FF ∧
    FF = H2.face x ∧
    (∀ y ∈ FF, azimDart V E y = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y) ∧
    (∀ y ∈ FF, wedgeInFanGt_p2 y E = wedgeInFanGt_p2 y (ePrime_p3 E FF)) ∧
    (∀ y ∈ FF, wedgeInFanGe_p2 y E = wedgeInFanGe_p2 y (ePrime_p3 E FF)) :=
  p22c2_f_surr_localization_cond hfan h1 hx hFF h2 hfs
    (p22c3_hcard_bridge hfan h1 hx hFF hfs) hsimple hno

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22c3_fullySurrounded_cardFaceGe3
#print axioms Kepler.Text.p22c3_hcard_bridge
#print axioms Kepler.Text.p22c2_f_surr_localization_cond_noHcard

end Kepler.Text
