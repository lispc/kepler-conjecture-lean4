/-
LocalAuto7W22dB: W22d 战役 wave 1 件 2 — HOL Light `CLOSURE_MINIMAL_EQ`
（`Multivariate/topology1.ml:1758`，**通用拓扑件**，非 Flyspeck 专属）。

## 陈述（HOL 原文）

```
!s t:real^N->bool. closed t ==> (closure s SUBSET t <=> s SUBSET t)
```

## Lean 翻译对照

| HOL | Lean |
|---|---|
| `closed t` | `IsClosed t` |
| `closure s SUBSET t` | `closure s ⊆ t` |
| `s SUBSET t` | `s ⊆ t` |

证明：`→` `subset_closure` + `Subset.trans`；`←` `closure_minimal`（`s ⊆ t` + `IsClosed t`）。

W22c-ii-b / W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciib

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **HOL Light `CLOSURE_MINIMAL_EQ`**（通用拓扑）：`IsClosed t` 时
`closure s ⊆ t ↔ s ⊆ t`。 -/
theorem p22d_closureMinimalEq {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsClosed t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨fun h => Set.Subset.trans subset_closure h, fun h => closure_minimal h ht⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_closureMinimalEq

end Kepler.Text
