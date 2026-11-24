import Kepler.Text.TaylorSecond.LeafContract
import Kepler.Text.Gamma4Val
import Kepler.Text.NliQitnpea12ArctanSeries

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

-- Probe: generator pattern — per-node literal + equality lemma
def i1 : QInterval := ⟨(2491914507 : ℚ) / 10 ^ 9, (2505996600 : ℚ) / 10 ^ 9⟩
def i2 : QInterval := ⟨(2018059914 : ℚ) / 10 ^ 9, (2035959636 : ℚ) / 10 ^ 9⟩
def i3 : QInterval := ⟨(2016098303 : ℚ) / 10 ^ 9, (2032069079 : ℚ) / 10 ^ 9⟩

def m12 : QInterval := i1.mul i2
def m12v : QInterval :=
  ⟨(2514416387845886199 : ℚ) / 500000000000000000, (6377634906941547 : ℚ) / 1250000000000000⟩

lemma m12_eq : m12 = m12v := by
  norm_num [m12, i1, i2, QInterval.mul]
  rfl

#print axioms m12_eq

/- 生成器范式探针结论（2026-11-24，三槽 guard + memlim 12GB 实测）：

* import 层基线：LeafContract+Gamma4Val+NliQitnpea12ArctanSeries 全量首编
  162.5 s / 5.59 GB（time -l）；热缓存复编 ~7 s。
* 单个 interval-op 等式引理范式：`norm_num [子 def, QInterval.mul]` + `rfl`
  —— 归约分母字面量直接闭（m12_eq/m31_eq 实证）。
* 一击 norm_num 于 ~20 op 深树卡死（typeclass instance stuck）；decide 不能
  delta-展开普通 def —— 生成器必须逐节点发射等式引理，子节点用 def 内联
  （或 rw 子等式后再 norm_num，sA_eq 起的链式重写细节待闭）。
  这些数字即 Phase B「每叶成本」的 tactic-层依据。 -/
end Kepler.Text.TaylorSecond
