/-
LocalAuto7W22ciino: W22c-ii-b 消槽 — `hno` 的显式证明（切片扇无孤立点）。

`vPrime_p3 V FF` 的每个点由 FF-dart `(y,w)` 的端点供给；`FF ⊆ H1.darts`
（面⊆darts）+ `H1.darts = dartsOfHyp_p3 E V` ⇒ `(y,w) ∈ dartsOfHyp_p3 E V`
⇒ `FullySurrounded` 给 `{y,w} ∈ E` ⇒ `{y,w} ∈ ePrime_p3 E FF`（端点 dart 在 FF）
⇒ `y ∈ ⋃₀ ePrime_p3 E FF`。再 `noIsolated_of_hsub_p36`（LocalAuto36:633）
⇒ `∀ v ∈ vPrime, ∃ w, {v,w} ∈ ePrime` ⇒ `hno_of_no_isolated`（AzimBridge:1157）。

W22c-ii-b / W22c-ii / W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciib
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto36

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- 切片扇无孤立点：`vPrime_p3 V FF ⊆ ⋃₀ ePrime_p3 E FF`。 -/
theorem p22c2_vPrime_subset_sUnion {V : Set V3} {E : Set (Set V3)}
    {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    (hfs : FullySurrounded V E) :
    vPrime_p3 V FF ⊆ ⋃₀ ePrime_p3 E FF := by
  have hxH1 : x ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  have hFFH1 : FF ⊆ (↑H1.darts : Set (V3 × V3)) := by
    rw [hFF]; exact p22c2_face_subset_darts H1 hxH1
  intro y hy
  have hy' : y ∈ V ∧ ∃ w, (y, w) ∈ FF := hy
  obtain ⟨-, w, hyw⟩ := hy'
  have hywDarts : (y, w) ∈ dartsOfHyp_p3 E V := h1.1 ▸ hFFH1 hyw
  have hyE : {y, w} ∈ E := p22c2_dartsOfHyp_subset hfs hywDarts
  exact Set.mem_sUnion.mpr
    ⟨{y, w}, ⟨y, w, rfl, hyE, hyw⟩, Set.mem_insert_iff.mpr (Or.inl rfl)⟩

/-- **消 `hno` 槽**：切片扇的 `dartsOfHyp_p3 (ePrime) (vPrime) = dart1OfFan`。 -/
theorem p22c2_noSlot_slice {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {H1 : Hypermap (V3 × V3)} (h1 : IsHypOn_p10 0 V E H1)
    {FF : Set (V3 × V3)} {x : V3 × V3} (hx : x ∈ dartsOfHyp_p3 E V) (hFF : FF = H1.face x)
    (hfs : FullySurrounded V E) :
    dartsOfHyp_p3 (ePrime_p3 E FF) (vPrime_p3 V FF)
      = dart1OfFan (vPrime_p3 V FF) (ePrime_p3 E FF) := by
  have hxH1 : x ∈ (↑H1.darts : Set (V3 × V3)) := h1.1.symm ▸ hx
  have hfan' : FAN 0 (vPrime_p3 V FF) (ePrime_p3 E FF) :=
    IMP_FAN_V_PRIME_E_PRIME hfan
      ⟨H1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, x, hxH1, hFF⟩
  exact hno_of_no_isolated
    (noIsolated_of_hsub_p36 hfan' (p22c2_vPrime_subset_sUnion h1 hx hFF hfs))

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22c2_vPrime_subset_sUnion
#print axioms Kepler.Text.p22c2_noSlot_slice

end Kepler.Text
