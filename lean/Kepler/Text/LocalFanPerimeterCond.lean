/-
Kepler/Text/LocalFanPerimeterCond.lean — TameLp 便宜门：父件条件形的 p21 族收口形。

`TameLp.fully_surrounded_perimeter_bound`（TameLp:925）的条件形资产：唯一显式
前提 = B1（w 侧 1_2 族；NKEZBFC 结案报告 §2 唯一真几何边界；形 = `pW42_prep_v4`
的 hslots.2 逐字）。无条件形仍等 B1 真证（用户未拍）。

装配链（全部在库、落库时公理面 = 标准三）：

* W19/W24 v4 链顶 `pW42_prep_v4`（hstep 已由 `pW30_hstepEG` 定理放电）；
* `pW42_hNKE_hia`：hNKE provider（hia 形；极扇凸性/generic 公开件全部需 hia，
  HOL polar_fan.hl:2552-2568 在 hia 分支内实例化 NKEZBFC 同形）；
* `pW42_WSEWPCH_hia_aux`（W13F aux 的 hia 并行孪生；generic 支
  `p13w_generic_perimeter` 的 hNKE 槽由 provider 直投）；
* `pW42_perimeter_hia_v4`：`hB1 ⇒ fanPerimeter ≤ 2π`；
* `pW43_parent_perimeterBound_of_fullySurrounded`：面装配（③a
  `p20_face_representation` + ③b `perimSumFaceArc` + `FAN_PERIMETER`）+
  ② 由 `p21_hL_of_fullySurrounded` 自动供给。

hia 说明：W13F/W21 的 hNKE 槽为 hia 自由形，与 provider 的 hia 形**类型不可配**
（W42B DELIVERY §3.1 机核）——hia 是 WSEWPCH generic 支的语境前提，故链的
装配走 hia 并行 aux；本件是该路线的 p21 族命名收口（与 W22dN
`p21_fully_surrounded_perimeter_bound'` 同族：其唯一显式槽 hNKE 由本件的
B1 条件形供给）。

**TameLp:925 未证槽零删除**（本文件纯新增，删除面 = 0；条件形资产非还债）。
-/
import Kepler.Text.LocalFanPerimeterFinal
import Kepler.Text.LocalAuto7W22dN

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **`fully_surrounded_perimeter_bound` 的条件形（便宜门收口形；W22dN 命名先例）**：
唯一显式前提 `hB1` = B1（w 侧 1_2 族，形 = `pW42_prep_v4` 的 hslots.2 逐字）。
② 由 `p21_hL_of_fullySurrounded` 自动供给；hNKE 由 `pW42_hNKE_hia`
（W19/W24 v4 链，hstep 已定理放电）经 hia 并行 aux 供给。

与 `pW43_parent_perimeterBound_of_fullySurrounded` 同装配同内容，按 p21 族
命名，以便 B1 真证后一行退无条件形。 -/
theorem p21_fully_surrounded_perimeter_bound''
    (hB1 : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})
    (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) :
    PerimeterBound V E hfan :=
  pW43_parent_perimeterBound_of_fullySurrounded hB1 V E hfan hfs

end Kepler.Text

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p21_fully_surrounded_perimeter_bound''
