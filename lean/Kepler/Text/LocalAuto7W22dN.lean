/-
LocalAuto7W22dN: perimeter ② 收口——`p21_fully_surrounded_perimeter_bound` 的 `hL` 槽
已由 `p21_hL_of_fullySurrounded`（`67190185`）自动供给，本件把装配写成一行。

剩余唯一槽 = `hNKE`（NKEZBFC 链，stepB 车道在收）；其余全在库。
-/
import Kepler.Text.LocalAuto7W21
import Kepler.Text.LocalAuto7W22dM

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **`fully_surrounded_perimeter_bound` 的 ② 已闭形**：HOL `f_surr_localization_convex_local`
的全部内容由 `p21_hL_of_fullySurrounded` 自动供给；只剩 `hNKE`（NKEZBFC）。 -/
theorem p21_fully_surrounded_perimeter_bound' 
    (hNKE : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      ConvexLocalFan U E' g → Generic U E' →
        0 ≤ solLocal_p2 (polarFan U E' g).2.1 (polarFan U E' g).2.2)
    (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E) (hfs : FullySurrounded V E) :
    PerimeterBound V E hfan :=
  p21_fully_surrounded_perimeter_bound hNKE V E hfan
    (p21_hL_of_fullySurrounded hfan hfs)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p21_fully_surrounded_perimeter_bound'

end Kepler.Text
