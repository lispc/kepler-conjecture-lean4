/-
Kepler/Text/LocalFanStepW42B.lean — wave W42b：hNKE provider（hia 形）+ 并行 WSEWPCH aux + 对外形。

裁定（W42 协调者）：W13F 的在库 hNKE 槽（无 hia）是渲染时漏前提——HOL
`polar_fan.hl:2552–2568` 中 NKEZBFC 在 **hia 分支内**对极扇 `(V',E',FF')`
实例化，凸性来自 BGMIFTE（`p11w2_polar_convex_of_eq`，**需 hia**）⇒ hia 是
语境前提不是槽。**W13F 陈述零改动**；本件新增并行形（SF 纪律，全在新文件）。
勘误（仅记于本 DELIVERY，不改源文件注释）：W13F docstring 的实例化草图
`NKEZBFC (p13w hcl) (simpa hg)` 类型不匹配——NKEZBFC 结论是**同扇**
`solLocal_p2 E FF`，槽要的是**极扇** solLocal；草图从未过类型检查。

件目：
* §1 `pW42_hNKE_hia`：`hB1`（逐字 = prep 的 hslots.2）⇒ 极扇形 stepB
  （`p11w2_polar_{convex,generic}_of_eq` @ hia ⇒ 极扇 p2 凸性/generic ⇒
  `pW42_prep_v4` 实例 + `solLocal_p9 = solLocal_p2` 定义体逐字 rfl 级）。
  hedge 由 `LOCAL_FAN_IMP_HEDGE` 机器导出（不占签名）。
* §2 `pW42_WSEWPCH_hia_aux`：W13F `WSEWPCH_final_aux` 逐字机械孪生——唯一
  改动 = hNKE 签名加 hia、generic 支调用加 `hia`（`p13e_*`/IH/各分支逐字）。
* §3 `pW42_perimeter_hia_v4`：对外形 `hB1 ⇒ fanPerimeter ≤ 2π`。
-/
import Kepler.Text.LocalFanStepW42A
import Kepler.Text.LocalAuto7W17
import Kepler.Text.LocalFanPerimeterGeneric

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 hNKE provider（hia 形，hB1 单一边界） -/

/-- **hNKE provider v4（hia 形）**：`hB1`（w 侧 1_2 族，逐字 = prep 的
hslots.2）+ 极扇（`p11w2_polar_*_of_eq` @ hia，来源 = BGMIFTE 链）。
`solLocal_p9 = solLocal_p2` 由定义体逐字相同（LA9:1288 / LA2:283）rfl 级。 -/
theorem pW42_hNKE_hia
    (hB1 : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) :
    ∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
      ConvexLocalFan U E' g → Generic U E' →
        (∀ v ∈ U, interiorAngle1 (0 : V3) g v < Real.pi) →
        0 ≤ solLocal_p2 (polarFan U E' g).2.1 (polarFan U E' g).2.2 := by
  intro U E' g hcl hg hia
  have hedge : ∀ v ∈ U, ∃ w, {v, w} ∈ E' := LOCAL_FAN_IMP_HEDGE hcl.1
  have hclp : ConvexLocalFan (polarFan U E' g).1 (polarFan U E' g).2.1
      (polarFan U E' g).2.2 :=
    p11w2_polar_convex_of_eq hcl hedge hg hia rfl
  have hgp : Generic (polarFan U E' g).1 (polarFan U E' g).2.1 :=
    p11w2_polar_generic_of_eq hcl hedge hg hia rfl
  exact pW42_prep_v4 p17_EJRCFJD_concl_p9
    (fun V E FF hcl' hg' => ⟨pW30_hstepEG hcl', hB1 V E FF hcl' hg'⟩)
    (polarFan U E' g).1 (polarFan U E' g).2.1 (polarFan U E' g).2.2
    (p13w_convexLocalFan_p2_of_clf hclp)
    (by simpa only [generic_p2, Generic] using hgp)

/-! ## §2 并行 WSEWPCH aux（W13F aux 孪生；唯一改动 = hNKE 加 hia） -/

theorem pW42_WSEWPCH_hia_aux :
    ∀ (N : ℕ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      V.ncard = N →
      (∀ (U : Set V3) (E' : Set (Set V3)) (g : Set (V3 × V3)),
        ConvexLocalFan U E' g → Generic U E' →
          (∀ v ∈ U, interiorAngle1 (0 : V3) g v < Real.pi) →
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
        exact p13w_generic_perimeter hcl hedge hg hia rfl (hNKE V E FF hcl hg hia)
      · -- straight 子支（W13a–e 已全闭）
        exact p13e_straight_perimeter_of_not_generic hIH hcl hedge hg hcard3 hia
    · -- ⑤ circular 支（HOL :2276-2335）
      exact FAN_PERIMETER_LE_2PI_OF_CIRCULAR hcl hedge
        (by simpa only [circular_p3, Circular] using hcirc)
    · -- ⑥ lunar 支（HOL :2336-2350）
      exact FAN_PERIMETER_LE_2PI_OF_LUNAR hcl hedge
        (by simpa only [lunar_p3, Lunar, circular_p3, Circular, Collinear3] using hlun)

/-! ## §3 对外形 -/

/-- **对外形（hia 形）**：`hB1` 单一边界 ⇒ `fanPerimeter V E FF ≤ 2π`。 -/
theorem pW42_perimeter_hia_v4
    (hB1 : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    fanPerimeter V E FF ≤ 2 * Real.pi :=
  pW42_WSEWPCH_hia_aux V.ncard V E FF rfl (pW42_hNKE_hia hB1) hcl hedge

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW42_hNKE_hia
#print axioms Kepler.Text.pW42_WSEWPCH_hia_aux
#print axioms Kepler.Text.pW42_perimeter_hia_v4
