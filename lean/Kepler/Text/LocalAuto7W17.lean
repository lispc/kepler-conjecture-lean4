/-
LocalAuto7W17: W18 — NKEZBFC 链的四个桩**下游重证**（材料齐，纯装配）。

## 件表（全部 = 已证内容的重述，无新数学）

| # | 件 | = 哪个桩 | 证明 |
|---|---|---|---|
| 1 | `p17_EJRCFJD_ALT2` | `LocalAuto2.lean:1589`（`EJRCFJD_ALT2`） | `exact pB_EJRCFJD_ALT2 …`（`LocalFanNkezbfcAlt2:575`，std3） |
| 2 | `p17_compatible_p9` | `LocalAuto9.lean:3200`（`COMPATIBLE_BW_TWO_LEMMAS_p9`） | `exact p16b_compatible_p9 …`（W16b，std3） |
| 3 | `p17_compatible2_alt` | `LocalAuto2.lean:1434`（`COMPATIBLE_BW_TWO_LEMMAS2_ALT`） | `p16b_compatible2` + `hcol`（`PROVE_THE_SLICE_ASSUMPTION`）+ 扁平重结合 |
| 4 | `p17_EJRCFJD_concl_p9` | `LocalAuto9.lean:3080`（`EJRCFJD_concl_p9 : Prop`） | `p16_concl_p9_of_ALT2 (fun … => pB_EJRCFJD_ALT2 …)` |

`EJRCFJD_concl_p9` 是 `NKEZBFC_PREP_p9` 的前提；件 4 使其**不再需要外部供给**。

## 同批 LA9 可见性（2 行，陈述零改）

`p9_chord_case`（`:3106`）/ `p9_main_induction`（`:3163`）`private theorem` → `theorem`，
供 W19 的 `p17_NKEZBFC_PREP_p9`（骨架 + `stepB` 参数）跨模块复用（先例 W13B/W15）。

LA2/LA9 的 5 个原位桩**不动**（LA2/LA9 在 `LocalAuto6` 上游，不能 import 下游 ⇒ 只能保留孤儿桩，
内容以本文件新名固化）。W16 / W16b / W13A–F 零改动。
-/
import Kepler.Text.LocalAuto7W16b
import Kepler.Text.LocalFanNkezbfcAlt2

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## 1. `EJRCFJD_ALT2`（LA2:1589 桩）的下游重证 -/

/-- **`EJRCFJD_ALT2`**（LA2:1589 的陈述，逐字）：两切片仍凸局部扇、`tauFun` 不减、
`solLocal` 可加、顶点数严格下降、`generic` 保持。证明 = `pB_EJRCFJD_ALT2`（std3）。 -/
theorem p17_EJRCFJD_ALT2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3}
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
    (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) :
    convexLocalFan_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) ∧
      convexLocalFan_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      tauFun_p2 V E FF ≥
        tauFun_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          tauFun_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      solLocal_p2 E FF =
        solLocal_p2 (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
          solLocal_p2 (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
      (slicev_p2 E FF v w).ncard < V.ncard ∧
      (slicev_p2 E FF w v).ncard < V.ncard ∧
      (generic_p2 V E →
        generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) ∧
          generic_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v)) :=
  pB_EJRCFJD_ALT2 hcl hv hw hcol hsub

/-! ## 2. `COMPATIBLE_BW_TWO_LEMMAS_p9`（LA9:3200 桩）的下游重证 -/

/-- **`COMPATIBLE_BW_TWO_LEMMAS_p9`**（LA9:3200 的陈述，逐字：`_p9` 切片名、反序 `hfv`、
无 `hcol`）。证明 = `p16b_compatible_p9`（W16b，std3）。 -/
theorem p17_compatible_p9 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {fv : Set (V3 × V3)}
    (h : convexLocalFan_p2 V E FF) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : HS.face (v, rhoNode1_p2 FF v) = fv) :
    (vPrime_p2 V fv = slicev_p9 E FF v w) ∧
      (ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p9 E FF v w) ∧
      (fv = slicef_p9 E FF v w) :=
  p16b_compatible_p9 h hv hw hvw hsub HS hHS hfv

/-! ## 3. `COMPATIBLE_BW_TWO_LEMMAS2_ALT`（LA2:1434 桩）的下游重证 -/

/-- **`COMPATIBLE_BW_TWO_LEMMAS2_ALT`**（LA2:1434 的陈述，逐字：三垃圾槽
`_hV`/`_hE`/`_hFF`、**无 `hcol`**、结论**扁平 6 元**）。`hcol` 由
`PROVE_THE_SLICE_ASSUMPTION`（LA6，std3）补，结论由 `p16b_compatible2` 的嵌套形扁平重结合。 -/
theorem p17_compatible2_alt {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (_hV : V) (_hE : E) (_hFF : FF)
    (HS : Hypermap (V3 × V3)) (fv fw : Set (V3 × V3)) (v w : V3)
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    (vPrime_p2 V fv = slicev_p2 E FF v w ∧
        ePrime_p2 (E ∪ {{v, w}}) fv = slicee_p2 E FF v w ∧
        fv = slicef_p2 E FF v w) ∧
      vPrime_p2 V fw = slicev_p2 E FF w v ∧
      ePrime_p2 (E ∪ {{w, v}}) fw = slicee_p2 E FF w v ∧
      fw = slicef_p2 E FF w v := by
  have hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) :=
    fun z t hz ht => PROVE_THE_SLICE_ASSUMPTION hcl hv hw hvw hsub z t hz ht
  obtain ⟨h1, h2⟩ := p16b_compatible2 (CVX_LO_IMP_LO hcl) hv hw hvw hcol hsub HS hHS hfv hfw
  exact ⟨h1, h2.1, h2.2.1, h2.2.2⟩

/-! ## 4. `EJRCFJD_concl_p9`（`NKEZBFC_PREP_p9` 的前提） -/

/-- **`EJRCFJD_concl_p9` 已证**：由 `p16_concl_p9_of_ALT2`（W16，`_p2`/`_p9` rfl 级桥）
喂 `pB_EJRCFJD_ALT2` 即得 ⇒ `NKEZBFC_PREP_p9` 的前提**不再需要外部供给**。 -/
theorem p17_EJRCFJD_concl_p9 : EJRCFJD_concl_p9 :=
  p16_concl_p9_of_ALT2
    (fun {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {v w : V3}
      (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
      (hcol : ∀ u u1 : V3, u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
        ¬ Collinear ℝ ({0, u, u1} : Set V3))
      (hsub : ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) =>
      pB_EJRCFJD_ALT2 hcl hv hw hcol hsub)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p17_EJRCFJD_ALT2
#print axioms Kepler.Text.p17_compatible_p9
#print axioms Kepler.Text.p17_compatible2_alt
#print axioms Kepler.Text.p17_EJRCFJD_concl_p9

end Kepler.Text
