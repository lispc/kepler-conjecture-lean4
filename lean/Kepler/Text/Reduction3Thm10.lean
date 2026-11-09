/-
  Kepler.Text.Reduction3Thm10 — T10 批（reduction3.hl:3677）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ assumption_set3_assumption_setK10 :3677
  │   → assumptionSet3_of_assumptionSetK10
  │ 依赖面：`assumptionSet3`（:1818）/`assumptionSetK10`（:3559）两 def
  │ 已由 D3b 落在 `Reduction3DefsAssumption`（全树唯一落点；K10 双落已裁）。
  │ **判词：非 rfl 级，但无需桥**——纯合取投影：
  │   ① 前提侧两 def 的 13 合取同集，仅 `elementPre`/`newvertexPrepped`
  │      次序不同（HOL 逐字如此，D3b 已记档），证中重排即成 K10 前提；
  │   ② 结论侧 K10 的 42 合取以 set3 的 26 合取为**后缀**
  │      （第 17 条起逐字相同），16 次 `.2` 投影即得。
  │ 零 J2 / 零新机器。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsAssumption

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList indexf ntrans quotientList rtrans
  splitNormalList transformCount ytrans ztrans)

/-- HOL `assumption_set3_assumption_setK10`（reduction3.hl:3677）：
`assumption_setK10 ==> assumption_set3`（三载体参数形式）。
证：前提重排 + K10 结论后缀投影（16 次 `.2`）。 -/
theorem assumptionSet3_of_assumptionSetK10
    (GoodNodesL : fgraph ℕ → Prop)
    (IsRestrictedL : fgraph ℕ → Prop)
    (Marked : fgraph ℕ → List (List Dart) → List Dart → Dart → Prop)
    (h : assumptionSetK10 GoodNodesL IsRestrictedL Marked) :
    assumptionSet3 GoodNodesL IsRestrictedL Marked := by
  intro L N r x k uvns vs vs' fx v h3
  obtain ⟨hg, hgn, hir, hnvp, hmk, hep, hnf, hct, hdt, hvs, htc, hff, hprev⟩ := h3
  have hcond : GoodList L ∧ GoodNodesL L ∧ IsRestrictedL L ∧
      elementPre L N ∧ newvertexPrepped L N r x ∧ Marked L N r x ∧
      ¬ finalList L r ∧ coreTripleV4 L N r x = uvns ∧
      destTripleFull (core L r) v uvns = vs ∧ vs.filterMap id = vs' ∧
      transformCount L N r x = k ∧ findFaceDarts L x = fx ∧
      (prevEl (core L r) v, v) = x :=
    ⟨hg, hgn, hir, hep, hnvp, hmk, hnf, hct, hdt, hvs, htc, hff, hprev⟩
  exact (h L N r x k uvns vs vs' fx v hcond).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.assumptionSet3_of_assumptionSetK10
