/-
LocalAuto7W16: W16 — `EJRCFJD_ALT2` 链的前置：`EJRCFJD_ALT` 下游重述 + `ALT2 ⇒ EJRCFJD_concl_p9` 桥。

## 背景（W16 侦察结论，详见 `W16_EJRCFJD_ALT2_BLOCKED.md`）

`EJRCFJD_ALT2`（`LocalAuto2.lean:1589`，未证桩）的 7 合取**逐条依赖 LA2 的未证兄弟件**：

| ALT2 合取 | 依赖 | LA2 处 | 本树 axioms |
|---|---|---|---|
| 1–2 两切片 `convexLocalFan_p2` | `EJRCFJD_ALT` + 切片↔`vPrime/ePrime` 桥 | 1449 / 1434 | 未证轴 / 未证轴 |
| 3 `tauFun` 不等式 | `ejr_sum` + `CARD_SLICEF` + `HAFL_CIRCLE_FORM_LOCAL_FAN2_ALT` | 1580 / 1501 / 984 | 未证轴 ×3 |
| 4 `solLocal` 加法 | `ejr_sum` | 1580 | 未证轴 |
| 5–6 `ncard` 下降 | `CARD_SLICEV_LT` | 1501 | 未证轴 |
| 7 `generic` 传递 | `ejr_generic` | 1567 | 未证轴 |

⇒ **ALT2 本体 BLOCKED**（不是 150–250 行能收的），本文件只交其中**可立即闭环**的两件：

* `p16_EJRCFJD_ALT`：`EJRCFJD_ALT`（LA2:1449）的**下游重述**。LA2 不能 import LA6
  （LA6 import LA2 成环）⇒ 原位填不了；本件把 LA6 的正本 `EJRCFJD`（std3）在 LA2 下游
  以新名给出，陈述与 LA2 桩逐字同形。
* `p16_concl_p9_of_ALT2`：`EJRCFJD_ALT2`（`_p2` 词汇）⇒ `EJRCFJD_concl_p9`（`_p9` 词汇）。
  `order_p9` 与 `order_p2` 定义体逐字同形（`Classical.epsilon` 同一 λ）⇒ `slicev/e/f`、
  `tauFun`、`solLocal` 的 `_p9`/`_p2` 版本 **rfl 级相等**，故桥是恒等。

W13A–F / LA2 / LA6 / LA7 零改动；无新增 import 之外的依赖。
-/
import Kepler.Text.LocalAuto7W13F

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## 1. `EJRCFJD_ALT` 的下游重述（= LA6 正本 `EJRCFJD`，std3） -/

/-- **`EJRCFJD_ALT`（LA2:1449 的陈述，新名下游重述）**：与 LA6 正本 `EJRCFJD` 的结论
逐字同形（HOL `EJRCFJD_ALT` 的证明就是 `MESON_TAC[EJRCFJD]`），仅多三个 `↑V`/`↑E`/`↑FF`
非空见证（HOL 的 `hV : V` 等），此处原样保留以对齐 LA2 的桩陈述。 -/
theorem p16_EJRCFJD_ALT {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v w : V3} {fv fw : Set (V3 × V3)}
    (_hV : V) (_hE : E) (_hFF : FF) (HS : Hypermap (V3 × V3))
    (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw ∧
      ∀ ff : ℕ → ℝ,
        setSum {i | i < V.ncard}
            (fun i => ff i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv}
              (fun i => ff i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) +
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw}
              (fun i => ff i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) :=
  EJRCFJD hcl hv hw hvw hsub HS hHS hfv hfw

/-! ## 2. `EJRCFJD_ALT2` ⇒ `EJRCFJD_concl_p9`（`_p2`/`_p9` 词汇 rfl 级） -/

/-- **`EJRCFJD_ALT2` ⇒ `EJRCFJD_concl_p9`**：`slicev/e/f`、`tauFun`、`solLocal` 的
`_p9` 与 `_p2` 版本定义体逐字同形（`order_p9`/`order_p2` 同一 `Classical.epsilon` λ）
⇒ 只需把 `ALT2` 作为前提接过来，`EJRCFJD_concl_p9`（`NKEZBFC_PREP_p9` 的前提）即得。 -/
theorem p16_concl_p9_of_ALT2
    (hALT2 : ∀ {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {v w : V3},
      convexLocalFan_p2 V E FF →
        v ∈ V →
          w ∈ V →
            (∀ (u u1 : V3), u ∈ ({v, w} : Set V3) → u1 ∈ V → u ≠ u1 →
                ¬Collinear ℝ ({0, u, u1} : Set V3)) →
              (∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) →
                convexLocalFan_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w)
                    (slicef_p2 E FF v w) ∧
                  convexLocalFan_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v)
                      (slicef_p2 E FF w v) ∧
                    tauFun_p2 V E FF ≥
                        tauFun_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w)
                            (slicef_p2 E FF v w) +
                          tauFun_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v)
                            (slicef_p2 E FF w v) ∧
                      solLocal_p2 E FF =
                          solLocal_p2 (slicee_p2 E FF v w) (slicef_p2 E FF v w) +
                            solLocal_p2 (slicee_p2 E FF w v) (slicef_p2 E FF w v) ∧
                        (slicev_p2 E FF v w).ncard < V.ncard ∧
                          (slicev_p2 E FF w v).ncard < V.ncard ∧
                            (generic_p2 V E →
                              generic_p2 (slicev_p2 E FF v w) (slicee_p2 E FF v w) ∧
                                generic_p2 (slicev_p2 E FF w v) (slicee_p2 E FF w v))) :
    EJRCFJD_concl_p9 := by
  intro V E FF v w hcl hv hw hcol hsub
  exact hALT2 hcl hv hw hcol hsub

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p16_EJRCFJD_ALT
#print axioms Kepler.Text.p16_concl_p9_of_ALT2

end Kepler.Text
