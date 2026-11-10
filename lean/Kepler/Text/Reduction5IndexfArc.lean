/-
  Kepler.Text.Reduction5IndexfArc — 编排者亲作（2026-11-10）：弧序基础式
  `indexfWArc`，reduction5 W2-c-3 conj 2（HQYMRTX1_list 链侧化）的 Blocker
  修复形（W2C_PLAN §8 补遗 `indexf_w_arc`）。

  路线注记：车道的原设计走「位置公式 + Nodup 单射」（~15 行）；本件改走
  **纯 MOD 算术**——`indexf` 自身的定义就是 `(idxOf y + (len − idxOf x)) MOD len`
  （弧距），故 `indexf w x + indexf x y ≡ indexf w y (MOD len)` 只需
  `Nat.add_mod` + `Nat.add_mod_right` + 一条 omega 和式，**不需要 Nodup、
  不需要 `nextElIterateGetElem`**（比原设计少两套基础设施依赖）。

  **纪律**：零公理、零占位证明、零反射式判定。
-/

import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

/-- **弧序基础式**（HOL 隐式事实，`indexf` 的 MOD 定义直读）：
`w, x, y ∈ r` ⇒ `indexf w x r + indexf x y r ≡ indexf w y r (MOD len r)`。
等式左端取主余形（`% len`）；右端 `indexf w y r` 本身已是 `% len` 项。 -/
theorem indexfWArc {α : Type} [DecidableEq α] {r : List α} {w x y : α}
    (hw : w ∈ r) (hx : x ∈ r) (hy : y ∈ r) :
    (indexf w x r + indexf x y r) % r.length = indexf w y r := by
  have hwx : indexf w x r = (r.idxOf x + (r.length - r.idxOf w)) % r.length := by
    simp [indexf, hw, hx]
  have hxy : indexf x y r = (r.idxOf y + (r.length - r.idxOf x)) % r.length := by
    simp [indexf, hx, hy]
  have hwy : indexf w y r = (r.idxOf y + (r.length - r.idxOf w)) % r.length := by
    simp [indexf, hw, hy]
  have hjw : r.idxOf w ≤ r.length :=
    Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hw)
  have hjx : r.idxOf x ≤ r.length :=
    Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hx)
  have hjy : r.idxOf y ≤ r.length :=
    Nat.le_of_lt (List.idxOf_lt_length_iff.mpr hy)
  have hsum : r.idxOf x + (r.length - r.idxOf w)
      + (r.idxOf y + (r.length - r.idxOf x))
      = (r.idxOf y + (r.length - r.idxOf w)) + r.length := by omega
  calc (indexf w x r + indexf x y r) % r.length
      = ((r.idxOf x + (r.length - r.idxOf w)) % r.length
          + (r.idxOf y + (r.length - r.idxOf x)) % r.length) % r.length := by
        rw [hwx, hxy]
    _ = (r.idxOf x + (r.length - r.idxOf w)
          + (r.idxOf y + (r.length - r.idxOf x))) % r.length :=
        (Nat.add_mod _ _ _).symm
    _ = ((r.idxOf y + (r.length - r.idxOf w)) + r.length) % r.length := by
        rw [hsum]
    _ = (r.idxOf y + (r.length - r.idxOf w)) % r.length :=
        Nat.add_mod_right _ _
    _ = indexf w y r := hwy.symm

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction5.indexfWArc
