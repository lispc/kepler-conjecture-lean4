import Kepler.Assembly

/-! # 终装配（Phase 6 终章，2026-10-10）

HOL `the_kepler_conjecture`（the_main_statement.hl:19-24）的**端到端形态**：
主定理自脊柱（`Kepler.Assembly`）四接口导出——`nonlinearInequalities`（Phase 4/G4
粘合，唯一裸接口 sorry）、`linearProgrammingResults`（真推导，债务集中于
`lpArchiveCertificates`）、`textCapstone`（真证明，经 §2c 骨架占位消费 TameSpine）、
`goodListArchive`（P6-C 已闭合）。

`#print axioms` 的输出即**主定理本身的实时债务图**（文末；同步入 DEBT.md 脊柱
探针节）：sorryAx 之上的每一笔清偿都直接体现为主定理债务递减。填证战线自此按
"主定理可达 sorry 递减"排序（docs/phase6-spine.md §6，M5′）。

陈述与 `Kepler.Statement.the_kepler_conjecture`（Statement.lean:111，Phase-1
sanctioned 占位）逐字相同（`Assembly.TheKeplerConjecture` 的 type 即其镜像）；
Statement 侧占位留待终版去重退役（Statement 在 import 图位于 Assembly 下游，
不能反向接线，故以本文件为端到端承载）。 -/

namespace Kepler

theorem the_kepler_conjecture_e2e :
    ∀ V : Set Space3, Packing V →
      ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
          Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2 :=
  Assembly.the_kepler_conjecture_from_interfaces

#print axioms the_kepler_conjecture_e2e

end Kepler
