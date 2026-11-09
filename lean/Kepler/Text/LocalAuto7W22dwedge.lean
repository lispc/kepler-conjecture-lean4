/-
LocalAuto7W22dwedge: W22d wedge 路线第 2 件 — `wedge_in_fan_gt_eq_w_dart_fan`。

HOL 锚：`RNSYJXM.vhl:74`
`Lemma wedge_in_fan_gt_eq_w_dart_fan d:
  d IN dart1_of_fan (V,E) ==>
  wedge_in_fan_gt d E = w_dart_fan (vec 0) V E (ext_dart (V,E) d)`。

Lean 词汇（探针已核）：`wedge_in_fan_gt` ↦ `wedgeInFanGt_p2`；
`w_dart_fan 0 V E (ext_dart (V,E) d)` ↦ `wDartFan 0 V E (0, d.1, d.2,
extensionSigmaFan 0 V E d.1 d.2)`（`ext_dart (V,E) (v,w) = (0,v,w,extension_sigma_fan 0 V E v w)`，
`hypermap_iso.vhl:847`；Lean 无 `extDart` 名，按定义式展开）。

证明（HOL 逐支，`CARD (set_of_edge v V E)` 两分）：
* `1 < ncard`：两边首支 = `wedge 0 v w`（azimCycle vs sigmaFan），
  `AZIM_CYCLE_EQ_SIGMA_FAN_ALT` 收口；
* 否则：`w ∈ setOfEdge` ⇒ ncard ≠ 0 ⇒ ncard = 1 ⇒ `setOfEdge = {w}`
  （`Set.ncard_eq_one`），两边次支 = `affGe` 补集，`Set.ext` + `simp` 收口。
  （`wedgeInFanGt_p2` 的 else 支与 `wDartFan` 的 empty 支在此不可达。）

W22d / W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciino

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **HOL `wedge_in_fan_gt_eq_w_dart_fan`**（RNSYJXM.vhl:74）：
`d ∈ dart1_of_fan` ⇒ `wedge_in_fan_gt d E = w_dart_fan 0 V E (ext_dart (V,E) d)`。 -/
theorem p22d_wedgeInFanGt_eq_wDartFan {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    wedgeInFanGt_p2 d E
      = wDartFan 0 V E (0, d.1, d.2, extensionSigmaFan 0 V E d.1 d.2) := by
  have hdm : d.2 ∈ setOfEdge d.1 V E :=
    (FAN_in_setOfEdge 0 V E d.1 d.2 hfan hd).2.2.1
  have hfin : (setOfEdge d.1 V E).Finite :=
    remark_finite_fan1 d.1 V E hfan.2.2.1.1
  simp only [wedgeInFanGt_p2, wDartFan, gt_iff_lt]
  rw [EE_elim hfan d.1]
  by_cases hgt : 1 < (setOfEdge d.1 V E).ncard
  · simp only [hgt, if_true]
    rw [AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hdm]
    rfl
  · have hpos : 0 < (setOfEdge d.1 V E).ncard :=
      (Set.ncard_pos (hs := hfin)).mpr ⟨d.2, hdm⟩
    have hcard1 : (setOfEdge d.1 V E).ncard = 1 := by omega
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard1
    have hxu : x = d.2 := by
      have h2 : d.2 ∈ setOfEdge d.1 V E := hdm
      rw [hx] at h2
      exact (Set.mem_singleton_iff.mp h2).symm
    have hsoe : setOfEdge d.1 V E = {d.2} := by rw [hx, hxu]
    simp only [hsoe, if_true]
    ext y
    simp [Set.mem_sdiff]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_wedgeInFanGt_eq_wDartFan

end Kepler.Text
