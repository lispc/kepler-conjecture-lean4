/-
LocalAuto7W22ciib: W22c-ii-b — `f_surr_localization` 的**条件形**（5 合取）。

`LVDUCXU`（`LocalAuto10:1708`，std3）已给全部 5 条（p3 词汇 + `azimInFan`）；本波按 §7 止损只交面⊆darts 的边成员性件；条件形本体剩余步骤见 DELIVERY §M2。

## 槽

* `hfs : FullySurrounded V E` —— HOL RNSYJXM 整节假设；用于排除 `selfPairs_p3`（孤立点自环）。
* `hcard : 2 < FF.ncard` / `hsimple : H2.Simple` —— HOL `FULLY_SURROUNDED_IMP_CARD_FACE_GE_3` /
  `fully_surrounded_simple_hypermap`（**未移植**，W22c-iii 的 a/b）。
* `hno` —— `LocalFan.of_localFan_p3` 的 `dartsOfHyp_p3 = dart1OfFan` 槽（切片扇无孤立点，
  需 `FullySurrounded (vPrime_p3 V FF) (ePrime_p3 E FF)` 或直接给等式）。

W22c / W22c-ii / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22cii

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-! ## 1. `dartsOfHyp_p3` 的边成员性（`FullySurrounded` 下无自环） -/

/-- **`FullySurrounded V E → dartsOfHyp_p3 E V ⊆ {d | {d.1,d.2} ∈ E}`**：
`dartsOfHyp_p3 = ordPairs_p3 ∪ selfPairs_p3`，前者定义即边，后者在 `FullySurrounded`
（无孤立点，`p22a_fs_has_edge`）下为空。 -/
theorem p22c2_dartsOfHyp_subset {V : Set V3} {E : Set (Set V3)} (hfs : FullySurrounded V E) :
    dartsOfHyp_p3 E V ⊆ {d : V3 × V3 | {d.1, d.2} ∈ E} := by
  intro d hd
  unfold dartsOfHyp_p3 at hd
  rcases hd with hord | hself
  · exact hord
  · -- 自环支：`EE_p3 d.1 E = ∅`，而 `FullySurrounded` 给 `d.1` 有邻居
    obtain ⟨w, hw⟩ := p22a_fs_has_edge hfs d.1 hself.2.1
    have hmem : w ∈ EE_p3 d.1 E := hw
    rw [hself.2.2] at hmem
    exact absurd hmem (Set.notMem_empty w)

/-- **`f_surr_localization` 条件形**（HOL RNSYJXM.vhl:245）：
`LVDUCXU` 的 5 合取 + azim 的 `azimDart` 双向折算 + `LocalFan.of_localFan_p3` 桥。
槽：`hfs`（边成员性）、`hcard`/`hsimple`（W22c-iii a/b 消）、`hno`（切片扇 darts 等式）。 -/
theorem p22c2_f_surr_localization_cond {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hfs : FullySurrounded V E) (hcard : 2 < FF.ncard) (hsimple : H2.Simple)
    (hno : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF)) :
    LocalFan (vPrime_p3 V FF) (ePrime_p3 E FF) FF ∧
    FF = H2.face x ∧
    (∀ y ∈ FF, azimDart V E y = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y) ∧
    (∀ y ∈ FF, wedgeInFanGt_p2 y E = wedgeInFanGt_p2 y (ePrime_p3 E FF)) ∧
    (∀ y ∈ FF, wedgeInFanGe_p2 y E = wedgeInFanGe_p2 y (ePrime_p3 E FF)) := by
  obtain ⟨hface2, hazimWedge, hlocal⟩ := LVDUCXU hfan h1 hx hFF h2
  have hxH1 : x ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  have hFFH1 : FF ⊆ (↑H1.darts : Set (V3 × V3)) := by
    rw [hFF]; exact p22c2_face_subset_darts H1 hxH1
  have hxFF : x ∈ FF := by rw [hFF]; exact H1.mem_face_self x
  have hxDarts2 : x ∈ dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF) :=
    IN_DARTS_FF_IMP_DARTS_E_PRIME_V_PRIME hx hxFF
  have hxD2 : x ∈ (↑H2.darts : Set (V3 × V3)) := h2.1.symm ▸ hxDarts2
  have hFFH2 : FF ⊆ (↑H2.darts : Set (V3 × V3)) := by
    rw [hface2]; exact p22c2_face_subset_darts H2 hxD2
  have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    IMP_FAN_V_PRIME_E_PRIME hfan
      ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, hxH1, hFF⟩
  refine ⟨?_, hface2, ?_, ?_, ?_⟩
  · exact LocalFan.of_localFan_p3 (hlocal ⟨hcard, hsimple⟩) hno
  · intro y hy
    have hyDarts : y ∈ dartsOfHyp_p3 E V := h1.1 ▸ hFFH1 hy
    have hyE : {y.1, y.2} ∈ E := p22c2_dartsOfHyp_subset hfs hyDarts
    have hyE2 : {y.1, y.2} ∈ ePrime_p3 E FF := ⟨y.1, y.2, rfl, hyE, hy⟩
    calc azimDart V E y = azimInFan_p3 y E := p22c_azimDart_eq_azimInFan hfan hyE
      _ = azimInFan_p3 y (ePrime_p3 E FF) := (hazimWedge y hy).1
      _ = azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y :=
          (p22c_azimDart_eq_azimInFan hfan' hyE2).symm
  · intro y hy
    exact (hazimWedge y hy).2.2
  · intro y hy
    exact (hazimWedge y hy).2.1

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/
#print axioms Kepler.Text.p22c2_f_surr_localization_cond
#print axioms Kepler.Text.p22c2_dartsOfHyp_subset

end Kepler.Text
