/-
Kepler/Text/LocalFanPerimeterFinalV5.lean — 父件 v5 条件形（纯追加）：
`pW42_perimeter_hia_v5`（无 w 侧槽）+ ② 的 `p21_hL_of_fullySurrounded` ⇒
`PerimeterBound`。

与 `LocalFanPerimeterFinal.lean` 的差别**只有**一行：hNKE 参数从
`pW42_perimeter_hia_v4 hB1` 换成 `pW42_perimeter_hia_v5`（hB1 槽已被
`LocalFanStepW44` 的 run 内 1_2 取代；父件陈述不动）。
-/
import Kepler.Text.LocalFanStepW42V5
import Kepler.Text.LocalFanPerimeterFinal

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **父件条件形 v5（hL 显式）**：每面弧和 ≤ 2π（无任何 w 侧槽）。 -/
theorem pW43_parent_perimeterBound_v5
    (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hL : ∀ d, d ∈ (hypermapOfFanTl V E hfan).darts →
      ConvexLocalFan (vPrime_p2 V ((hypermapOfFanTl V E hfan).face d))
        (ePrime_p2 E ((hypermapOfFanTl V E hfan).face d))
        ((hypermapOfFanTl V E hfan).face d)) :
    PerimeterBound V E hfan := by
  intro f hf
  obtain ⟨d, hd, rfl⟩ := p20_face_representation (hypermapOfFanTl V E hfan) hf
  have hcl := hL d hd
  have hhedge : ∀ v ∈ vPrime_p2 V ((hypermapOfFanTl V E hfan).face d),
      ∃ w, {v, w} ∈ ePrime_p2 E ((hypermapOfFanTl V E hfan).face d) :=
    LOCAL_FAN_IMP_HEDGE hcl.1
  have hfin : ((hypermapOfFanTl V E hfan).face d).Finite :=
    orbitMap_finite (hypermapOfFanTl V E hfan).faceMap_permutes d
  rw [perimSumFaceArc V E _ hcl.1 hhedge hfin]
  rw [← FAN_PERIMETER hcl.1 hhedge]
  exact pW42_perimeter_hia_v5 hcl hhedge

/-- **`fully_surrounded_perimeter_bound` 的 v5 形（零槽）**：② 由
`p21_hL_of_fullySurrounded` 自动供给。 -/
theorem pW43_parent_perimeterBound_of_fullySurrounded_v5
    (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) :
    PerimeterBound V E hfan :=
  pW43_parent_perimeterBound_v5 V E hfan (p21_hL_of_fullySurrounded hfan hfs)

end Kepler.Text

/-! ## 探针 -/

#print axioms Kepler.Text.pW43_parent_perimeterBound_v5
#print axioms Kepler.Text.pW43_parent_perimeterBound_of_fullySurrounded_v5
