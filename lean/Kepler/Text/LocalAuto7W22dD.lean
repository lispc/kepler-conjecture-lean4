/-
LocalAuto7W22dD: W22d wave 2 件 2 — `iso_simple` 的 Lean 坍缩形（`Simple` 传输）。

## HOL 原形

`hypermap_iso-compiled.hl:699` `iso_simple_imp`：
`simple_hypermap G ==> simple_hypermap H`（iso 传输）。

## Lean 判定（坍缩）

`Simple H := ∀ x ∈ H.darts, H.node x ∩ H.face x = {x}`（`Hypermap.lean:1058`）只依赖
`nodeMap`/`faceMap` 与 `darts`；同 `(V,E)` 上两个 `IsHypOn_p10` 超映射的四条映射相等
由 `p22d_isHypOn_maps_eq`（`5f1ef193`）供给 ⇒ `Simple` 沿映射相等传输。

**边界（如实报）**：本件不消 `hsimple`——切片扇 `(vPrime_p3 V FF, ePrime_p3 E FF)` 与原扇
`(V,E)` 不同，映射不等；切片扇 `Simple` 仍需 HOL `localization_simple_hypermap`（全树零命中）。
-/
import Kepler.Text.LocalAuto7W22dC

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **`Simple` 沿映射相等传输**（`iso_simple_imp` 的 Lean 坍缩形）：
`nodeMap`/`faceMap` 相等 + `darts` 相等 ⇒ `Simple` 传输。 -/
theorem p22d_simple_congr {α : Type*} {H1 H2 : Hypermap α}
    (hn : H1.nodeMap = H2.nodeMap) (hf : H1.faceMap = H2.faceMap)
    (hd : H1.darts = H2.darts) (hs : H1.Simple) : H2.Simple := by
  intro x hx
  rw [← hd] at hx
  have h := hs x hx
  rw [Hypermap.node, Hypermap.face] at h ⊢
  rw [hn] at h
  rw [hf] at h
  exact h

/-- **同 `(V,E)` 上 `IsHypOn_p10` 超映射的 `Simple` 传输**：`p22d_isHypOn_maps_eq` + 坍缩。 -/
theorem p22d_simple_of_isHypOn {V : Set V3} {E : Set (Set V3)}
    {H1 H2 : Hypermap (V3 × V3)}
    (h1 : IsHypOn_p10 0 V E H1) (h2 : IsHypOn_p10 0 V E H2)
    (hs : H1.Simple) : H2.Simple := by
  obtain ⟨hd, -, hn, hf⟩ := p22d_isHypOn_maps_eq h1 h2
  have hn' : H1.nodeMap = H2.nodeMap := Equiv.ext (fun x => congrFun hn x)
  have hf' : H1.faceMap = H2.faceMap := Equiv.ext (fun x => congrFun hf x)
  exact p22d_simple_congr hn' hf' hd hs

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_simple_congr
#print axioms Kepler.Text.p22d_simple_of_isHypOn

end Kepler.Text
