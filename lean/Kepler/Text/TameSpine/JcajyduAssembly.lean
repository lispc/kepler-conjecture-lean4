/-
  Kepler.Text.TameSpine.JcajyduAssembly — tame-corr nb43：J5-9 装配侦察 + 条件形装配件
  （`Assembly.jcajydu`，HOL `Jcajydu.JCAJYDU` JCAJYDU.hl:51-90）。

  ┌─ 本件定位 ─────────────────────────────────────────────────────
  │ 目标：把 `Assembly.lean:2509 theorem jcajydu` 的占位 stub 体
  │ 换成对 `jcajyduTameSpine` 的调用。侦察（见 DELIVERY-nb43 §1）结论：
  │ `jcajyduShell` 的 `hp : restrictedHypermapsArePlaneGraphsV4` 由
  │ `restrictedHypermapsArePlaneGraphsThm` 的 8 槽给出，其中：
  │   · `hF`（reduction_F / main_induction 下游）**缺**（J5-8 14i 在飞）；
  │   · `hK4`（reduction_K4，HOL reduction4.hl:5319）**树内零落点**；
  │   · `hmuc` 槽型 `MarkedSlot L N r x → (core L r).Nodup` **缺 `GoodList L`**，
  │     按字面不可证（DEF-FIX 候选；本件以带 `hL` 的修正版在内部绕过）；
  │   · 其余 5 槽（`hbcK`/`hnnzy`/`hnn0i`/`hnon0`/`hbc0`）**全部有现成供给件**。
  │ 故本件交付「除 hF/hK4 外全绿」的条件形装配：`jcajyduTameSpine` 只吃
  │ `hF`、`hK4` 两个显式前提，其余槽内部现证；结论 = Assembly `jcajydu`
  │ 同形（三桥折算见 `JcajyduShell` 头注 ①②③）。
  │ Assembly hunk 因 `hF`/`hK4` 未落而**挂起**（DELIVERY-nb43 §4 给未来
  │ hunk 文本）；不在本文件内伪造槽值。
  └────────────────────────────────────────────────────────────────

  ┌─ 槽 → 供给件（逐槽实测，详见 DELIVERY-nb43 §1）────────────────
  │ hbcK  ← `betwnCorekZX`（nb42 e929020f，HOL betwn_corek_z_x.hl:535）
  │ hmuc  ← 修正版：`markedListUniqCore` + 显式 `hL`（原槽缺 `hL`，不可证）
  │ hnnzy ← `finalAssumptionsNotNextCore0ZY`（Reduction5J5NotNextCore:81）
  │ hnn0i ← `finalAssumptionsNotNextCore0I`（Reduction5J5NotNextCore0I:68）
  │ hnon0 ← `transformCountNon0OfMarked`（Reduction5J5Termination:112）
  │ hbc0  ← `betwnCore0ZY`（Reduction5J7W4:49，J5-7 W4 主件）
  │ hK4   ← **缺**（无 reduction_K4）
  │ hF    ← **缺**（reduction_F / main_induction，J5-8 14i）
  └────────────────────────────────────────────────────────────────

  **纪律**：零禁词（公理/占位/反射式判定）；不改既有陈述/定义；
  主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.Reduction5K5
import Kepler.Text.Reduction5J5NotNextCore
import Kepler.Text.Reduction5J5NotNextCore0I
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J7W4
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.JcajyduShell
import Kepler.Text.TameSpine.JcajyduRed5Top
import Kepler.Text.TameSpine.JcajyduOfNum
import Kepler.Text.TameSpine.Reduction3J5BetwnCorekZX

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.Reduction3
  (assumptionSetK10Full GoodNodesSlot IsRestrictedSlot MarkedSlot)
open Kepler.Text.Reduction5
  (Dart reductionK4Asm reductionK4Concl reductionK5Concl transformCount ztrans
    ytrans rtrans core finalList)

/-- **`reduction_K5` 的 `hL` 修正版**（私件，30 行）：与在库
`Kepler.Text.Reduction5.reductionK5` 逐句同证，只把 `hmuc` 槽从
`MarkedSlot → Nodup` 强化为 `GoodList → MarkedSlot → Nodup`
（原槽缺 `GoodList L` 前提，按字面不可证；见模块头 DEF-FIX 记档）。
其余 6 槽逐字同形。 -/
private theorem reductionK5WithHL
    (GoodNodesL : fgraph ℕ → Prop) (IsRestrictedL : fgraph ℕ → Prop)
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
              GoodList L → Marked L N r x → (core L r).Nodup)
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
    Kepler.Text.Reduction3.assumptionSetK10 GoodNodesL IsRestrictedL Marked := by
  apply hK4
  intro L N r x k hAsm
  obtain ⟨hL, hgn, hres, hm, hfin, htc⟩ := hAsm
  have hk0 : k ≠ 0 := by
    rw [← htc]
    exact hnon0 L N r x ⟨hL, hgn, hm, hfin⟩
  have hbrl := Kepler.Text.Reduction5.betwnCoreReductionLemma L N r x k
    (hmuc L N r x hL hm) hk0
    (fun i hi hb => hnn0i L N r x k ⟨hL, hgn, hres, hm, hfin, htc⟩ i hi hb)
  exact ⟨fun hne =>
      hbcK L N r x k ⟨hL, hgn, hres, hm, htc⟩ (Nat.pos_of_ne_zero hk0) hne,
    hbc0 L N r x k ⟨hL, hgn, hres, hm, hfin, htc⟩,
    hnnzy L N r x ⟨hL, hgn, hres, hm, hfin⟩, hbrl.1, hbrl.2⟩

/-- **`assumptionSetK10Full` 的槽形装配**（`hL` 修正版）：吃 `hK4` + 5 个
D3b 槽；`hmuc` 由 `markedListUniqCore` 以显式 `hL` 现证（不占原槽）。 -/
private theorem assumptionSetK10FullOfSlots
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot
                L N r x k → reductionK4Concl L N r x k) →
        assumptionSetK10Full)
    (hbcK : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), GoodList L ∧ GoodNodesSlot L ∧ IsRestrictedSlot L ∧
              MarkedSlot L N r x ∧ transformCount L N r x = k → 0 < k →
              (ztrans L N r x (k - 1)).1 ≠ x.1 →
              between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
                between (core L r) (ztrans L N r x (k - 1)).1 x.1)
    (hnnzy : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesSlot L ∧ IsRestrictedSlot L ∧
              MarkedSlot L N r x ∧ ¬ finalList L r →
              (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
                nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
                  (ytrans L N r x 0).1))
    (hnn0i : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot
                L N r x k → ∀ i : ℕ, i < k →
              between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
              nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1)
    (hnon0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
              GoodList L ∧ GoodNodesSlot L ∧ MarkedSlot L N r x ∧
              ¬ finalList L r → transformCount L N r x ≠ 0)
    (hbc0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot
                L N r x k → reductionK5Concl L N r x k) :
    assumptionSetK10Full :=
  reductionK5WithHL GoodNodesSlot IsRestrictedSlot MarkedSlot hK4 hbcK
    (fun L N r x hL hm =>
      Kepler.Text.Reduction4Idx.markedListUniqCore L hL (hm hL))
    hnnzy hnn0i hnon0 hbc0

/-- `AqiunppSlot` 槽的链侧供给（`aqiunpp` 逐点展开）。 -/
private theorem aqiunppSlotOf (L : fgraph ℕ) (hL : GoodList L) :
    Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
  fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i

/-- **J5-9 装配件（条件形）**：只吃 `hF`（reduction_F）与 `hK4`（reduction_K4）
两个上游槽；其余 5 槽由在库件供给，`hmuc` 槽的 `hL` 缺失以修正版内部绕开。
结论 = `jcajyduShell` 的 TameSpine 形（与 Assembly `jcajydu` 三桥 defeq，
见 `JcajyduShell` 头注 ①②③）。 -/
theorem jcajyduTameSpine
    (hF : assumptionSetK10Full → restrictedHypermapsArePlaneGraphsV4)
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot
                L N r x k → reductionK4Concl L N r x k) →
        assumptionSetK10Full)
    {α : Type*} [DecidableEq α] (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' := by
  -- 槽 1：hbcK ← betwnCorekZX（nb42）
  have hbcK : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
      (k : ℕ), GoodList L ∧ GoodNodesSlot L ∧ IsRestrictedSlot L ∧
      MarkedSlot L N r x ∧ transformCount L N r x = k → 0 < k →
      (ztrans L N r x (k - 1)).1 ≠ x.1 →
      between (core L (rtrans L N r x k)) (ztrans L N r x (k - 1)).1 x.1 =
        between (core L r) (ztrans L N r x (k - 1)).1 x.1 := by
    intro L N r x k hAsm hk0 hne
    obtain ⟨hL, hgn, hres, hm, htc⟩ := hAsm
    exact Kepler.Text.TameSpine.betwnCorekZX L hL (hgn hL) (hres hL) (hm hL) htc hk0 hne
  -- 槽 3：hnnzy ← finalAssumptionsNotNextCore0ZY
  have hnnzy : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
      GoodList L ∧ GoodNodesSlot L ∧ IsRestrictedSlot L ∧ MarkedSlot L N r x ∧
      ¬ finalList L r →
      (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
        nextEl (core L (rtrans L N r x 0)) (ztrans L N r x 0).1 ≠
          (ytrans L N r x 0).1) := by
    intro L N r x hAsm
    obtain ⟨hL, hgn, hres, hm, hnf⟩ := hAsm
    exact Kepler.Text.Reduction5.finalAssumptionsNotNextCore0ZY L hL (hgn hL) (hres hL)
      (aqiunppSlotOf L hL) (hm hL) hnf
  -- 槽 4：hnn0i ← finalAssumptionsNotNextCore0I
  have hnn0i : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
      (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot L N r x k →
      ∀ i : ℕ, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
      nextEl (core L r) (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 := by
    intro L N r x k hAsm i hi hbet
    obtain ⟨hL, hgn, hres, hm, hnf, htc⟩ := hAsm
    exact Kepler.Text.Reduction5.finalAssumptionsNotNextCore0I L hL (hgn hL) (hres hL)
      (aqiunppSlotOf L hL) k (hm hL) hnf htc i hi hbet
  -- 槽 5：hnon0 ← transformCountNon0OfMarked
  have hnon0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart),
      GoodList L ∧ GoodNodesSlot L ∧ MarkedSlot L N r x ∧ ¬ finalList L r →
      transformCount L N r x ≠ 0 := by
    intro L N r x hAsm
    obtain ⟨hL, hgn, hm, hnf⟩ := hAsm
    exact Kepler.Text.Reduction5.transformCountNon0OfMarked L hL (hgn hL)
      (aqiunppSlotOf L hL) (hm hL) hnf
  -- 槽 6：hbc0 ← betwnCore0ZY（J5-7 W4）
  have hbc0 : ∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
      (k : ℕ), reductionK4Asm GoodNodesSlot IsRestrictedSlot MarkedSlot L N r x k →
      reductionK5Concl L N r x k := by
    intro L N r x k hAsm
    obtain ⟨hL, hgn, hres, hm, hnf, htc⟩ := hAsm
    exact Kepler.Text.Reduction5.betwnCore0ZY L hL (hgn hL) (hres hL)
      (aqiunppSlotOf L hL) (hm hL) hnf htc
  -- `hp` 由 `hF` + `hK4` + 五槽装配
  have hp : restrictedHypermapsArePlaneGraphsV4 :=
    hF (assumptionSetK10FullOfSlots hK4 hbcK hnnzy hnn0i hnon0 hbc0)
  -- 壳结论（TameSpine 三桥形）
  exact jcajyduOfNum hp H hres

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。 -/
#print axioms Kepler.Text.TameSpine.jcajyduTameSpine
