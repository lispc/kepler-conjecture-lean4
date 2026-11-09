/-
LocalAuto7W22dC: W22d wave 2 件 1 — `fan_hypermaps_iso` 的 Lean 折算（**坍缩版**）。

## HOL 原形与 Lean 判定

HOL `fan_hypermaps_iso`（`fan/hypermap_iso-compiled.hl:1092`）：

```
(hypermap1_of_fanx (vec 0,V,E)) iso (hypermap_of_fan (V,E))
```

**Lean 判定：该件在 Lean 下坍缩为「映射相等」**——
`hypermap1OfFanx` / `hypermap1OfFan` **全树零命中**（本批 `grep` 核实），Lean 只有**一个**
扇超映射 `hypermapOfFan`（`Fan.lean:1189`）⇒ HOL 的「两个扇超映射同构」在 Lean 侧没有对象，
其**实质内容**退化为：任何两个 `IsHypOn_p10 0 V E` 的超映射**四条映射相等**。

## 件（本波只交件 1）

`p22d_isHypOn_maps_eq`：`IsHypOn_p10 0 V E H1 → IsHypOn_p10 0 V E H2 →
H1.darts = H2.darts ∧ H1.edgeMap = H2.edgeMap ∧ H1.nodeMap = H2.nodeMap ∧ H1.faceMap = H2.faceMap`

（`IsHypOn_p10 x V E HS = ↑HS.darts = dartsOfHyp_p3 E V ∧ edgeMap = eeOfHyp_p3 x V E ∧
nodeMap = nnOfHyp_p3 x V E ∧ faceMap = ffOfHyp_p3 x V E`，两条相消即得。）

W22dA/B / W22c* / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciib

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **`fan_hypermaps_iso` 的 Lean 坍缩形**：同一 `(V,E)` 上两个 `IsHypOn_p10` 超映射的
四条映射相等（HOL 的「两扇超映射同构」在 Lean 侧无对象，退化为映射相等）。 -/
theorem p22d_isHypOn_maps_eq {V : Set V3} {E : Set (Set V3)}
    {H1 H2 : Hypermap (V3 × V3)}
    (h1 : IsHypOn_p10 0 V E H1) (h2 : IsHypOn_p10 0 V E H2) :
    H1.darts = H2.darts ∧ (H1.edgeMap : V3 × V3 → V3 × V3) = H2.edgeMap ∧
      (H1.nodeMap : V3 × V3 → V3 × V3) = H2.nodeMap ∧
      (H1.faceMap : V3 × V3 → V3 × V3) = H2.faceMap :=
  ⟨Finset.coe_injective (h1.1.trans h2.1.symm), h1.2.1.trans h2.2.1.symm,
    h1.2.2.1.trans h2.2.2.1.symm, h1.2.2.2.trans h2.2.2.2.symm⟩




/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_isHypOn_maps_eq

end Kepler.Text
