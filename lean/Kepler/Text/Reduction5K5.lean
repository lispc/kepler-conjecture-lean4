/-
  Kepler.Text.Reduction5K5 — W2-a patch2：`reduction5.hl` 本体三件的链侧
  槽形移植（②③件；主定理槽形在 `TameSpine.JcajyduRed5Top`）。

  ┌─ 件表（HOL `reduction5.hl:54-157` 逐字；`//` 死注释段不移植）────
  │ `reductionK5`       :54-138  六前提合取 ⇒ `assumption_setK10`
  │   槽 = reduction_K4（:5319）/ betwn_corek_z_x（betwn_corek_z_x.hl:535）
  │        / marked_list_uniq_core（reduction4.hl:1747）
  │        / final_assumptions_not_next_core0_z_y（:5217）
  │        / final_assumptions_not_next_core_0_i（:5139）
  │        / transform_count_non0（reduction3.hl:796，槽形非 ☆Thm2 直 import，
  │          见文件尾勘误）
  │ `assumptionSetK10Thm` :141-148  reduction_K5 + betwn_core0_z_y
  │   （betwn_core0_z_y.hl:1300）槽形装配（HOL：`MATCH_MP_TAC
  │   reduction_K5; MESON[betwn_core0_z_y]` 两步）。
  │ 陈述性 def：`reductionK4Asm`（K4 前提六件）/ `reductionK4Concl`
  │ （K4 结论五合取）/ `reductionK5Concl`（betwn_core0_z_y 结论形 =
  │ K4 ②）。三载体槽（GoodNodesL/IsRestrictedL/Marked）沿用
  │ `Reduction3.assumptionSetK10` 的槽约定（D3b）。
  └────────────────────────────────────────────────────────────────

  ┌─ 勘误（对工单「transformCount_non0 ☆Thm2 槽形可直接 import」）──
  │ `Reduction3Thm2.transformCountNon0` 是 hfinal 条件槽形
  │ （Thm2:92-99：多一个非 HOL 前提 `finalList L (rtrans … transformCount)`），
  │ 直接 import 会把 hfinal 注入 reductionK5 签名（污染 HOL 逐字形）。
  │ 故 `transform_count_non0` 以**逐字槽** `hnon0` 进入（Thm2 无条件形
  │ 落库后一行代入消槽；与 h4 槽同款纪律）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动；
  零 import TameSpine（链侧纯）。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.Reduction3DefsAssumption

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList findFaceDarts nextEl listPairs)

/-! ## §0 陈述性 def（K4 前提/结论、K5 结论；HOL 逐字序） -/

/-- K4 前提六件（`reduction4.hl:5320-5326` ASSUMPTIONS 块逐字序：
good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final_list
∧ transform_count = k；后三者是 D3b 载体槽）。 -/
def reductionK4Asm (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ) : Prop :=
  GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧ Marked L N r x ∧
    ¬ finalList L r ∧ transformCount L N r x = k

/-- K5CONJ（`reduction5.hl:71-78` 活段 = K4 ②支 = betwn_core0_z_y
结论形，`betwn_core0_z_y.hl:1300-1309`）。 -/
def reductionK5Concl (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < k → (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1 →
    between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1 =
      between (core L (rtrans L N r x (i + 1))) (ztrans L N r x i).1
        (ytrans L N r x (i + 1)).1

/-- K4CONJ 五合取（`reduction4.hl:5326-5372` 逐字序）：
① betwn_corek_z_x（`PRE k` ↦ `k - 1`）② betwn_core0_z_y
③ not_next_core0_z_y ④ not_next_core_0_i 的 0 实例 ⑤ not_mem_yi_zi。 -/
def reductionK4Concl (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (k : ℕ) : Prop :=
  ((ztrans L N r x (k - 1)).1 ≠ x.1 →
      between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
        between (core L r) (ztrans L N r x (k - 1)).1 x.1) ∧
    reductionK5Concl L N r x k ∧
    (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
        (ytrans L N r x 0).1) ∧
    (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      nextEl (core L r) (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1) ∧
    (∀ i : ℕ, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉ listPairs (core L r))

/-! ## §1 `reductionK5`（`reduction5.hl:54-138`） -/

/-- HOL `Reduction5.reduction_K5`（逐字；HOL 证体 =
`MATCH_MP_TAC Reduction4.reduction_K4` + 逐支消 K4CONJ）。 -/
theorem reductionK5 (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              reductionK4Concl L N r x k) →
        Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked)
    (hbcK : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
              Marked L N r x ∧ transformCount L N r x = k → 0 < k →
              (ztrans L N r x (k - 1)).1 ≠ x.1 →
              between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
                between (core L r) (ztrans L N r x (k - 1)).1 x.1)
    (hmuc : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              Marked L N r x → (core L r).Nodup)
    (hnnzy : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧ Marked L N r x ∧
              ¬ finalList L r →
              (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
                nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
                  (ytrans L N r x 0).1))
    (hnn0i : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              ∀ i : ℕ, i < k →
              between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
              nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1)
    (hnon0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesL L ∧ Marked L N r x ∧ ¬ finalList L r →
              transformCount L N r x ≠ 0)
    (hprem : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              reductionK5Concl L N r x k) :
    Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked := by
  apply hK4
  intro L N r x k hAsm
  obtain ⟨hL, hgn, hres, hm, hfin, htc⟩ := hAsm
  have hk0 : k ≠ 0 := by
    rw [← htc]
    exact hnon0 L N r x ⟨hL, hgn, hm, hfin⟩
  have hbrl := betwnCoreReductionLemma L N r x k (hmuc L N r x hm) hk0
    (fun i hi hb => hnn0i L N r x k ⟨hL, hgn, hres, hm, hfin, htc⟩ i hi hb)
  exact ⟨fun hne =>
      hbcK L N r x k ⟨hL, hgn, hres, hm, htc⟩ (Nat.pos_of_ne_zero hk0) hne,
    hprem L N r x k ⟨hL, hgn, hres, hm, hfin, htc⟩,
    hnnzy L N r x ⟨hL, hgn, hres, hm, hfin⟩, hbrl.1, hbrl.2⟩

/-! ## §2 `assumptionSetK10Thm`（`reduction5.hl:141-148`） -/

/-- HOL `Reduction5.assumption_setK10`（定理形）：`MATCH_MP_TAC reduction_K5`
+ 前提由 `betwn_core0_z_y`（槽 `hbc0`）供给。 -/
theorem assumptionSetK10Thm (GoodNodesL : fgraph ℕ → Prop)
    (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              reductionK4Concl L N r x k) →
        Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked)
    (hbcK : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
              Marked L N r x ∧ transformCount L N r x = k → 0 < k →
              (ztrans L N r x (k - 1)).1 ≠ x.1 →
              between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
                between (core L r) (ztrans L N r x (k - 1)).1 x.1)
    (hmuc : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              Marked L N r x → (core L r).Nodup)
    (hnnzy : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧ Marked L N r x ∧
              ¬ finalList L r →
              (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
                nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
                  (ytrans L N r x 0).1))
    (hnn0i : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              ∀ i : ℕ, i < k →
              between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
              nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1)
    (hnon0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesL L ∧ Marked L N r x ∧ ¬ finalList L r →
              transformCount L N r x ≠ 0)
    (hbc0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesL IsRestrictedL Marked L N r x k →
              reductionK5Concl L N r x k) :
    Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked :=
  reductionK5 GoodNodesL IsRestrictedL Marked hK4 hbcK hmuc hnnzy hnn0i hnon0 hbc0

end Kepler.Text.Reduction5

/-! 探针（编译即执行；槽形件吃 Prop 参数，零 sorryAx、⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.reductionK5
#print axioms Kepler.Text.Reduction5.assumptionSetK10Thm
