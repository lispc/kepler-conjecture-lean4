/-
LocalAuto7W22dE: W22d azim 半 — `p22d_slice_azimDart_lt_pi`。

目标：`y ∈ FF` ⇒ `azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y < Real.pi`。
路线（机器已核）：
1. `p22c2_f_surr_localization_cond` 第 3 合取：`∀ y ∈ FF, azimDart V E y = azimDart 切片 y`；
2. `FullySurrounded V E := ∀ x ∈ dartOfFan V E, azimDart V E x < Real.pi`（TameLp:339）；
   `y ∈ dart1OfFan V E`（`{y.1,y.2} ∈ E`，由 `p22c2_dartsOfHyp_subset hfs` +
   `FF ⊆ H1.darts = dartsOfHyp_p3 E V`）⇒ `y ∈ dartOfFan V E`（右并支）。
3. 合流：`rw [← haz]; exact hfs y (Or.inr hyE)`。

W22d / W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciino

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **W22d azim 半**：`y ∈ FF` ⇒ 切片扇上的 `azimDart` 严格小于 `π`。 -/
theorem p22d_slice_azimDart_lt_pi {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    {H2 : Hypermap (V3 × V3)}
    (h2 : IsHypOn_p10 0 (vPrime_p3 V FF) (ePrime_p3 E FF) H2)
    (hfs : FullySurrounded V E) (hcard : 2 < FF.ncard) (hsimple : H2.Simple)
    (hno : dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF))
    {y : V3 × V3} (hy : y ∈ FF) :
    azimDart (vPrime_p3 V FF) (ePrime_p3 E FF) y < Real.pi := by
  have haz := (p22c2_f_surr_localization_cond hfan h1 hx hFF h2 hfs hcard hsimple
    hno).2.2.1 y hy
  rw [← haz]
  have hxH1 : x ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  have hFFH1 : FF ⊆ (↑H1.darts : Set (V3 × V3)) := by
    rw [hFF]; exact p22c2_face_subset_darts H1 hxH1
  have hyDarts : y ∈ dartsOfHyp_p3 E V := h1.1 ▸ hFFH1 hy
  have hyE : {y.1, y.2} ∈ E := p22c2_dartsOfHyp_subset hfs hyDarts
  exact hfs y (Or.inr hyE)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_slice_azimDart_lt_pi

end Kepler.Text
