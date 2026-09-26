/- TIMING MODULE arm=base (emit_fold2.py; scratch).
内核 `derivIExpr` 全量（matcher 展开 + 求值）：C549M2Der3 的全新
decide 复测（Mono2 模块本体已过；此处测本机隔离 decide 口径）. -/
import Kepler.Interval.Cases.C549Mono2

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace BaseTiming

open Kepler.Interval

theorem t :
    checkPosTMHull ((derivIExpr Kepler.Interval.Cases2.C549M2Expr 2))
      Kepler.Interval.Cases2.C549M2Box3
      Kepler.Interval.Cases2.C549M2DP3 = true := by
  decide

end BaseTiming
