/-
  Kepler.Targets.Wt2A — wt2A 目标的独立验收模块（2026-11-20，接管会话）。

  背景：`nliCell3QZECFICwt2A` 的证明项只是 `Kepler.NliBanks27.bank_wt2A`
  的定义别名；把它留在 `Kepler.Assembly` 里，会让目标验收被迫编译完整
  Assembly 容器（闭包 8,867 件，含 585 条 native shard 与 Text/Interval
  分支）。本模块把同一名字、同一陈述、同一证明项下沉到 89 件闭包，供
  `#print axioms Kepler.Assembly.nliCell3QZECFICwt2A` 在池恢复前先行验收。
  `Kepler.Assembly` 以 import 消费本模块，不重复声明；根面语义不变。
-/
import Kepler.NliBanks27

namespace Kepler.Assembly

/-- HOL ineq entry `QZECFIC wt2 A`（ineq.hl:1443；PA21 `bank_QZECFICwt2A`，
盒 [√2,√2]³×[2hmin,√8]²×[2,2hmin]，`h0cut y4/y5` 参数化双支）。
证明 = `NliBanks27.bank_wt2A` 的 62-cell 角点证书与 Lean 覆盖树。 -/
theorem nliCell3QZECFICwt2A : Kepler.Text.bank_QZECFICwt2A :=
  Kepler.NliBanks27.bank_wt2A

end Kepler.Assembly
