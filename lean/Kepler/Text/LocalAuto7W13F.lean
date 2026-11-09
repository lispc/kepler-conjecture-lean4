/-
LocalAuto7W13F: W15 — `WSEWPCH_final`：凸局部扇的 perimeter ≤ 2π
（HOL polar_fan.hl:2213-3400 五分支归纳）。

## 分支顺序（关键：三分在前，`hia` 二分在后）

HOL 逐段（行号为 `scripts/local/polar_fan.hl`）：

```
WF_INDUCT_TAC (CARD V)                         -- :2260（IH 无 generic：递归只交
                                               --        CARD V' < CARD V + convex_local_fan V' E' FF'）
  ASM_CASES_TAC `circular V E`                 -- :2272
    circular   → KCHMAMG 路线                  -- :2276-2335
    ¬circular  → ASM_CASES_TAC `∃ v w, lunar`  -- :2336
      lunar    → lunar 支                      -- :2336-2350
      ¬lunar   → CIZMRRH 第一析取 ⇒ generic V E（三分互斥）
        ASM_CASES_TAC `∀ v, interiorAngle1 < π`  -- :2560
          TRUE  → generic 支（BGMIFTE + NKEZBFC）
          FALSE → straight 支（W13a–e 已全闭）
```

⇒ HOL 正文 straight 支（`:2705` 的 `hdis`）与 fan6（`:2801`）所需的 `generic V E`
**来自 `CIZMRRH` 的第一析取**，不是全局假设 ⇒ **本件不带 `hg`**。
（判读证据：`polar_fan.hl` 全文 `generic` 只作 *其它* 定理 `:410`/`:1067` 的前提出现；
WSEWPCH 正文两处用点 `:2705`/`:2801` 均为 `FIRST_X_ASSUM(... [Localization.generic])`，
而 `:2272` 已先分 circular、`:2336` 再分 lunar ⇒ 余下区域即 generic。）

## 本件唯一显式槽：`hNKE`

generic 支吃 `0 ≤ solLocal_p2 (polarE V E FF) (polarFF V E FF)`（HOL `Localization.NKEZBFC`；
本树 `LocalAuto2:1606` 仍为未证桩）。本件把它做成**显式前提 `hNKE`**（与
`p13w_generic_perimeter` 的槽同形）：

* straight / circular / lunar / CARD≤2 四支 **无条件**；
* generic 支条件在 `hNKE` 上；`NKEZBFC` 落库后本件**零改动**（一行实例化，见 `WSEWPCH_final` 注释）。

W13A–E / LA7 / W12E–P 零改动；显式 import `LocalFanPerimeterGeneric`
（`p13w_generic_perimeter`；该模块已在 W13B 的 import 闭包内，本件显式化，无新依赖）。
-/
import Kepler.Text.LocalAuto7W13E
import Kepler.Text.LocalFanPerimeterGeneric

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 强归纳主体（HOL `WF_INDUCT_TAC (CARD V)`；IH 无 generic） -/

/-- **`WSEWPCH` 主体的 `N`-索引强归纳形**。IH 只要求 `U.ncard < N` +
`ConvexLocalFan U E' g` + hedge，**不要求 `Generic`**（与 HOL `:2260` 的 IH 同形）。 -/
theorem WSEWPCH_final_aux :
    ∀ (N : ℕ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      V.ncard = N →
      (∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
        ConvexLocalFan U E' g → Generic U E' →
          0 ≤ solLocal_p2 (polarFan U E' g).2.1 (polarFan U E' g).2.2) →
      ConvexLocalFan V E FF → (∀ v ∈ V, ∃ w, {v, w} ∈ E) →
        fanPerimeter V E FF ≤ 2 * Real.pi := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V E FF hN hNKE hcl hedge
    -- ① `CARD V ≤ 2` 支（HOL :2633-2648）
    by_cases hsmall : V.ncard ≤ 2
    · exact FAN_PERIMETER_LE_2PI_OF_CARD_LE hcl hedge hsmall
    -- ② `3 ≤ CARD V` ⇒ 三分（HOL :2272 / :2336）
    have hcard3 : 3 ≤ V.ncard := by omega
    have hlf3 : localFan_p3 V E FF := localFan_p2.of_LocalFan_noIso hcl.1 hedge
    -- IH（无 generic 形；HOL :2790 的递归只交 `CARD V' < CARD V` + convex）
    have hIH : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
        U.ncard < V.ncard → ConvexLocalFan U E' g → (∀ v ∈ U, ∃ w, {v, w} ∈ E') →
          fanPerimeter U E' g ≤ 2 * Real.pi := by
      intro U E' g hlt
      exact ih U.ncard (by omega) U E' g rfl hNKE
    rcases CIZMRRH hlf3 with ⟨hgen, -⟩ | ⟨hcirc, -⟩ | ⟨⟨v, w, hlun⟩, -⟩
    · -- ③ generic 区（三分第一析取 ⇒ `hg` 就位）
      have hg : Generic V E := by simpa only [generic_p3, Generic] using hgen
      -- ④ `hia` 二分（HOL :2560）
      by_cases hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi
      · -- generic 子支（HOL :2553-2623）：唯一缺口 = `hNKE`
        exact p13w_generic_perimeter hcl hedge hg hia rfl (hNKE V E FF hcl hg)
      · -- straight 子支（W13a–e 已全闭）
        exact p13e_straight_perimeter_of_not_generic hIH hcl hedge hg hcard3 hia
    · -- ⑤ circular 支（HOL :2276-2335）
      exact FAN_PERIMETER_LE_2PI_OF_CIRCULAR hcl hedge
        (by simpa only [circular_p3, Circular] using hcirc)
    · -- ⑥ lunar 支（HOL :2336-2350）
      exact FAN_PERIMETER_LE_2PI_OF_LUNAR hcl hedge
        (by simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun)

/-! ## 对外形（**无 `hg`**，唯一槽 `hNKE`） -/

/-- **`WSEWPCH_final`**：`ConvexLocalFan V E FF → hedge → fanPerimeter V E FF ≤ 2π`。

**不带 `hg`**（`Generic V E` 由 `CIZMRRH` 三分第一析取供）。唯一显式槽 `hNKE` =
HOL `Localization.NKEZBFC`（本树 `LocalAuto2:1606` 仍为未证桩，属锥内 78 条待证义务之一）。

`NKEZBFC` 落库后的实例化形（**本件不落**，避免把未证桩拖进证明）：

```
WSEWPCH_final
  (fun U E' g hcl hg => NKEZBFC (p13w_convexLocalFan_p2_of_clf hcl) (by
      simpa only [generic_p2, Generic] using hg))
  hcl hedge
```

（`NKEZBFC` 吃 `generic_p2`，与 `Generic` 定义体同形，故只需一处 `simpa`。） -/
theorem WSEWPCH_final
    (hNKE : ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      ConvexLocalFan U E' g → Generic U E' →
        0 ≤ solLocal_p2 (polarFan U E' g).2.1 (polarFan U E' g).2.2)
    {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    fanPerimeter V E FF ≤ 2 * Real.pi :=
  WSEWPCH_final_aux V.ncard V E FF rfl hNKE hcl hedge

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.WSEWPCH_final_aux
#print axioms Kepler.Text.WSEWPCH_final

end Kepler.Text
