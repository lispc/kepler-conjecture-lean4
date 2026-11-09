/-
LocalAuto7W22dA: W22d 战役 wave 1 件 1 — HOL `DART1_NOT_COLLINEAR_2`
（`fan/hypermap_and_fan.hl:2693`）。

## 陈述（HOL 原文）

```
FAN (vec 0,V,E) /\ (v,w) IN dart1_of_fan (V,E)
  ==> ~collinear {vec 0,v,w} /\ ~collinear {vec 0,v,sigma_fan (vec 0) V E v w}
```

## Lean 翻译对照

| HOL | Lean |
|---|---|
| `~collinear {vec 0,v,w}` | `¬ Collinear3 0 v w` |
| `sigma_fan (vec 0) V E v w` | `sigmaFan 0 V E v w` |
| `(v,w) IN dart1_of_fan` | `(v,w) ∈ dart1OfFan V E`（`= {d | {d.1,d.2} ∈ E}`） |

**两半都走 `fan6`**（`FAN` 的第五合取：`∀ e ∈ E, ¬Collinear ℝ (insert 0 e)`），
第二半需先证 `sigmaFan … ∈ setOfEdge v V E`（`SIGMA_FAN` 的 `if_neg` 支 +
`sigmaFan` 单点支 `if_pos`）。

W22c-ii-b / W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22ciib

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **HOL `DART1_NOT_COLLINEAR_2`**：`(v,w) ∈ dart1OfFan` 时 `{0,v,w}` 与
`{0,v,sigmaFan 0 V E v w}` 都非共线。 -/
theorem p22d_dart1NotCollinear2 {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {v w : V3} (hvw : (v, w) ∈ dart1OfFan V E) :
    ¬ Collinear3 (0 : V3) v w ∧ ¬ Collinear3 (0 : V3) v (sigmaFan 0 V E v w) := by
  have hE : {v, w} ∈ E := hvw
  refine ⟨hfan.2.2.2.2.1 {v, w} hE, ?_⟩
  have hw : w ∈ setOfEdge v V E := (properties_of_setOfEdge_fan 0 V E v w hfan).mp hE
  have hσ : sigmaFan 0 V E v w ∈ setOfEdge v V E := by
    by_cases hne : setOfEdge v V E = {w}
    · unfold sigmaFan
      rw [if_pos hne]
      exact hne ▸ Set.mem_singleton w
    · exact (SIGMA_FAN hne hfan hw).1
  have hEσ : {v, sigmaFan 0 V E v w} ∈ E :=
    (properties_of_setOfEdge_fan 0 V E v (sigmaFan 0 V E v w) hfan).mpr hσ
  exact hfan.2.2.2.2.1 {v, sigmaFan 0 V E v w} hEσ

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_dart1NotCollinear2

end Kepler.Text
