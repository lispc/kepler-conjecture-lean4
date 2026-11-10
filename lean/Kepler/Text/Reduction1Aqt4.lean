/-
  Kepler.Text.Reduction1Aqt4 — dih2k 段 ②–⑤ 的共用桥件（hasOrders 的支持外延 +
  商 darts 成员桥）。本波只落这两件共用桥；②–⑤ 本体冻结（见 DELIVERY_AQT4 §2）。

  · `hasOrdersOfSupport` —— `has_orders` 的**支持外延**：置换在 support 内非恒等、
    在 support 上幂回自身 ⇒ 全函数面 `hasOrders_p3`。HOL 对应
    `power_permutation_outside_domain`（hypermap.hl:4905）在 has_orders 面的用法；
    ③（face k）/④（edge 2）/⑤（node 2）三件共用。
  · `mem_darts_quotient` —— 商 darts 成员 = 原子族成员（`quotientHypermap_spec`
    第 1 槽 + `Finset.mem_coe`），② 的入口桥。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1Aqt3
import Kepler.Text.Hypermap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-! ## §1 `has_orders` 的支持外延（③④⑤ 共用） -/

/-- **`has_orders` 的支持外延桥**：若置换 `f` 在有限 support `s` 上
①每个 `0 < i < k` 都动某点（`(f^i) a ≠ a`）且 ②`f^k` 逐点固定 `s`，
则 `hasOrders_p3 f k`（全函数面：`f^[i] ≠ id`（0<i<k）且 `f^[k] = id`）。
support 外的逐点固定由 `PermutesOn.pow_apply_eq_self_of_not_mem`
（HOL `power_permutation_outside_domain`）给。 -/
theorem hasOrdersOfSupport {β : Type*} (f : Equiv.Perm β) (s : Finset β) (k : ℕ)
    (hs : Kepler.Text.PermutesOn f s)
    (hne : ∀ i, 0 < i → i < k → ∃ a ∈ s, (f ^ i) a ≠ a)
    (hid : ∀ a ∈ s, (f ^ k) a = a) :
    Kepler.Text.hasOrders_p3 (f : β → β) k := by
  refine ⟨?_, ?_⟩
  · intro i h0 hk hEq
    obtain ⟨a, ha, hne'⟩ := hne i h0 hk
    apply hne'
    -- (f^i) a = a：hEq 是函数等式 f^[i] = id，经 Perm 幂 ↔ 迭代 换算
    have h1 : (f ^ i) a = f^[i] a := by
      rw [Equiv.Perm.coe_pow]
    simp [h1, hEq]
  · funext a
    by_cases ha : a ∈ s
    · exact hid a ha
    · exact Kepler.Text.Hypermap.PermutesOn.pow_apply_eq_self_of_not_mem hs ha k

/-! ## §2 商 darts 成员桥（② 入口） -/

/-- 商 hypermap 的 darts 成员 = 原子族成员（`quotientHypermap_spec` 第 1 槽）。 -/
theorem mem_darts_quotient {α : Type*} [DecidableEq α] {H : Hypermap α}
    {NF : Set (Loop α)} (hnf : H.IsNormalFamily NF) {a : Set α} :
    a ∈ (H.quotientHypermap hnf).darts ↔ a ∈ H.atomsOfFamily NF := by
  rw [← Finset.mem_coe, (H.quotientHypermap_spec hnf).1]

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.hasOrdersOfSupport
#print axioms Kepler.Text.Reduction1.mem_darts_quotient
