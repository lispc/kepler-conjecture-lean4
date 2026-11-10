/-
Kepler/Text/LocalFanPerimeterFinal.lean — 父件条件形接线（编排者亲作）：
**B1（w 侧 1_2 族）⇒ `PerimeterBound V E hfan`**。

链路（全在库，本件只做面级装配）：
* `pW42_perimeter_hia_v4 (hB1) (hcl) (hedge) : fanPerimeter ≤ 2π`
  （W42b：hNKE provider(hia 形) + WSEWPCH 并行 aux；hia 由 aux 的 generic
  分支在语境提供——HOL polar_fan.hl:2552–2568 同形）；
* `p20_face_representation`（③a）+ `perimSumFaceArc`（③b）；
* `FAN_PERIMETER`（周长 = 面弧和）；
* `p21_hL_of_fullySurrounded`（② 自动供给面切片凸性）。

**父件 `TameLp.fully_surrounded_perimeter_bound` 的无条件陈述不动**（其未证槽
只能在 B1 真证或 SF 之后关闭）；本件给出其**条件形**，唯一显式前提 = B1。
-/
import Kepler.Text.LocalFanStepW42B
import Kepler.Text.LocalAuto7W22dN

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **父件条件形（hL 显式）**：B1 ⇒ 每面弧和 ≤ 2π。与
`p21_fully_surrounded_perimeter_bound` 同装配，唯一替换 = hNKE 槽换成
B1 条件形的 `pW42_perimeter_hia_v4`。 -/
theorem pW43_parent_perimeterBound
    (hB1 : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})
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
  exact pW42_perimeter_hia_v4 hB1 hcl hhedge

/-- **`fully_surrounded_perimeter_bound` 的条件形（唯一前提 B1）**：
② 由 `p21_hL_of_fullySurrounded` 自动供给。 -/
theorem pW43_parent_perimeterBound_of_fullySurrounded
    (hB1 : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})
    (V : Set V3) (E : Set (Set V3)) (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) :
    PerimeterBound V E hfan :=
  pW43_parent_perimeterBound hB1 V E hfan (p21_hL_of_fullySurrounded hfan hfs)

end Kepler.Text

/-! ## `#print axioms` 探针 -/

#print axioms Kepler.Text.pW43_parent_perimeterBound
#print axioms Kepler.Text.pW43_parent_perimeterBound_of_fullySurrounded
