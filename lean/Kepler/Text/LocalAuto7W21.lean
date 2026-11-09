/-
LocalAuto7W21: W21 — ③ 固化 + `fully_surrounded_perimeter_bound` 的**条件形**
（② `f_surr_localization_convex_local` 作显式前提）。

## 件表

| # | 件 | = 哪个 HOL 件 | 行 |
|---|---|---|---|
| 1 | `p20_face_representation` | `hypermap.hl:2737` `lemma_face_representation` | ~5 |
| 2 | **`p21_fully_surrounded_perimeter_bound`** | `lp_main_estimate-compiled.hl:1530-1543` 的**条件形** | ~25 |

`perimFaceEqImageRhoNode1` / `perimSumFaceArc`（TameLp:871/903，③b）本批**只改可见性**
（`private theorem` → `theorem`，陈述零改），TameLp **不加新证明**。

## 条件形的 ② 槽

HOL ② 的陈述：`d ∈ dart_of_fan (V,E) → convex_local_fan (v_prime V f, e_prime E f, f)`
（`f = face (hypermap_of_fan (V,E)) d`）。本件取**更易供给**的 `H.darts` 索引形：

```
hL : ∀ d, d ∈ (hypermapOfFanTl V E hfan).darts →
     ConvexLocalFan (vPrime_p2 V (H.face d)) (ePrime_p2 E (H.face d)) (H.face d)
```

`dart1OfFan V E ⊆ dartOfFan V E`（`Fan.lean:90` 定义即 `… ∪ dart1OfFan`）⇒ HOL 形的 ②
可直接实例化本槽（孤立点自环 `(v,v)` 对 `face` 无影响）。

## 接线（HOL 九步 → Lean）

`PerimeterBound` 定义 → ③a（本件件 1）→ ③b（`perimSumFaceArc`）→ `FAN_PERIMETER`
→ `WSEWPCH_final`（W15，`hNKE` 槽由 W18/W19 的 `p17_NKEZBFC` 填）→ ② 槽 `hL`。

W16/W16b/W17/W13A–F、LA2/LA9 零改动；TameLp 仅 2 行可见性。
-/
import Kepler.Text.LocalAuto7W13F
import Kepler.Text.LocalAuto7W17
import Kepler.Text.TameLp

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-! ## 1. `lemma_face_representation`（HOL hypermap.hl:2737） -/

/-- **`u ∈ H.faceSet → ∃ x ∈ H.darts, u = H.face x`**：`faceSet` 是 `setOfOrbits`
（`{x | ∃ x_1 ∈ D, orbitMap f x_1 = x}`，Hypermap:1008 定义）⇒ 定义展开即得。 -/
theorem p20_face_representation {α : Type*} [DecidableEq α] (H : Hypermap α)
    {u : Set α} (hu : u ∈ H.faceSet) :
    ∃ x, x ∈ H.darts ∧ u = H.face x := by
  have hu' : ∃ x, x ∈ H.darts ∧ orbitMap H.faceMap x = u := hu
  obtain ⟨x, hx, hxu⟩ := hu'
  exact ⟨x, hx, hxu.symm⟩

/-! ## 2. `fully_surrounded_perimeter_bound` 的条件形（② 作显式前提） -/

/-- **`PerimeterBound V E hfan`**（条件形）：唯一显式前提 `hL` = HOL ②
`f_surr_localization_convex_local`（切片扇的凸性），索引集取 `H.darts`
（`⊆ dartOfFan`，见文件头）。其余全在库：③a（本件）、③b（`perimSumFaceArc`）、
`FAN_PERIMETER`、`WSEWPCH_final`（`hNKE` 槽）。 -/
theorem p21_fully_surrounded_perimeter_bound
    (hNKE : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      ConvexLocalFan U E' g → Generic U E' →
        0 ≤ solLocal_p2 (polarFan U E' g).2.1 (polarFan U E' g).2.2)
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
  exact WSEWPCH_final hNKE hcl hhedge

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p20_face_representation
#print axioms Kepler.Text.p21_fully_surrounded_perimeter_bound

end Kepler.Text
