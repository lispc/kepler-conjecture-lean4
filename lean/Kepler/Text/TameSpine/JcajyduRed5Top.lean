/-
  Kepler.Text.TameSpine.JcajyduRed5Top — W2-a patch2：HOL
  `restricted_hypermaps_are_planegraphs_thm`（`reduction5.hl:150-157`）
  的槽形孪生。

  ┌─ 结构─────────────────────────────────────────────────────────
  │ HOL 证体：`MATCH_MP_TAC Reduction3.reduction_F; REWRITE_TAC
  │ [assumption_setK10]` 两行。Lean 槽形：`reduction_F`（j3def T15，
  │ main_induction 下游）留唯一显式槽 `hF`；本体半边（assumption_setK10
  │ 定理 = `Reduction5.assumptionSetK10Thm`，其七槽 = reduction_K4 /
  │ betwn_corek_z_x / marked_list_uniq_core / not_next 族两件 /
  │ transform_count_non0 / betwn_core0_z_y）全部真证供给。
  │ 载体实例化 = D3b 三槽（`GoodNodesSlot`/`IsRestrictedSlot`/
  │ `MarkedSlot`，即 `assumptionSetK10Full`）。
  │ `hF` 落库（T15 一行折算）后本件即无条件形，供给
  │ `JcajyduShell.jcajyduShell` 的 `hp` 槽（J5 wrapper 接线点）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
  环方向：本件在 TameSpine 侧（消费链侧 Reduction5K5 + JcajyduShell 陈述），
  链侧消费者不 import 本文件。
-/

import Kepler.Text.Reduction5K5
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.JcajyduShell

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList findFaceDarts nextEl)
open Kepler.Text.Reduction3
  (assumptionSetK10Full GoodNodesSlot IsRestrictedSlot MarkedSlot)
open Kepler.Text.Reduction5
  (reductionK4Asm reductionK4Concl reductionK5Concl)

/-- **HOL `restricted_hypermaps_are_planegraphs_thm`**（`reduction5.hl:150-157`
逐字折算）：`restricted_hypermaps_are_planegraphs_v4`，`reduction_F` 槽形。 -/
theorem restrictedHypermapsArePlaneGraphsThm
    (hF : assumptionSetK10Full → restrictedHypermapsArePlaneGraphsV4)
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ) (k : ℕ),
              reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot L N r x k →
              reductionK4Concl L N r x k) → assumptionSetK10Full)
    (hbcK : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ) (k : ℕ), GoodList L ∧ GoodNodesSlot L ∧
              IsRestrictedSlot L ∧ MarkedSlot L N r x ∧
              Kepler.Text.Reduction5.transformCount L N r x = k → 0 < k →
              (Kepler.Text.Reduction5.ztrans L N r x (k - 1)).1 ≠ x.1 →
              between (Kepler.Text.Reduction5.core L
                  (Kepler.Text.Reduction5.rtrans L N r x k))
                (Kepler.Text.Reduction5.ztrans L N r x (k - 1)).1 x.1 =
              between (Kepler.Text.Reduction5.core L r)
                (Kepler.Text.Reduction5.ztrans L N r x (k - 1)).1 x.1)
    (hmuc : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ), MarkedSlot L N r x →
              (Kepler.Text.Reduction5.core L r).Nodup)
    (hnnzy : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ), GoodList L ∧ GoodNodesSlot L ∧ IsRestrictedSlot L ∧
              MarkedSlot L N r x ∧
              ¬ Kepler.Text.Reduction5.finalList L r →
              (between (findFaceDarts L x)
                  (Kepler.Text.Reduction5.ytrans L N r x 0)
                  (Kepler.Text.Reduction5.ztrans L N r x 0) = [] →
                nextEl (Kepler.Text.Reduction5.core L
                    (Kepler.Text.Reduction5.rtrans L N r x 0))
                  (Kepler.Text.Reduction5.ztrans L N r x 0).1 ≠
                  (Kepler.Text.Reduction5.ytrans L N r x 0).1))
    (hnn0i : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ) (k : ℕ),
              reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot L N r x k →
              ∀ i : ℕ, i < k →
              between (findFaceDarts L x)
                  (Kepler.Text.Reduction5.ytrans L N r x i)
                  (Kepler.Text.Reduction5.ztrans L N r x i) = [] →
              nextEl (Kepler.Text.Reduction5.core L r)
                (Kepler.Text.Reduction5.ytrans L N r x i).1 ≠
                (Kepler.Text.Reduction5.ztrans L N r x i).1)
    (hnon0 : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ), GoodList L ∧ GoodNodesSlot L ∧ MarkedSlot L N r x ∧
              ¬ Kepler.Text.Reduction5.finalList L r →
              Kepler.Text.Reduction5.transformCount L N r x ≠ 0)
    (hbc0 : ∀ (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
              (x : ℕ × ℕ) (k : ℕ),
              reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot L N r x k →
              reductionK5Concl L N r x k) :
    restrictedHypermapsArePlaneGraphsV4 :=
  hF (Kepler.Text.Reduction5.assumptionSetK10Thm GoodNodesSlot IsRestrictedSlot
    MarkedSlot hK4 hbcK hmuc hnnzy hnn0i hnon0 hbc0)

end Kepler.Text.TameSpine

/-! 探针（编译即执行；槽形件零 sorryAx、⊆ 标准三） -/
#print axioms Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsThm
