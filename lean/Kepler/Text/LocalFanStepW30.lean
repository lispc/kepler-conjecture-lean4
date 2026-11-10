/-
Kepler/Text/LocalFanStepW30.lean — wave W30：v4 链两个供给面（hprev-C1 装配 + hstep 消槽放电）。

按 WINDING_PLAN「件齐只差装配」两面：
* §1 `pW30_hprevC1`：**hprev-C1 供给件**（v4 链可消费）——
  `pW5b_flat_mem`（w 侧 flat-run 逐点成员，B 支第二 run 分支）+ `pW5w2_affGt_prev_21`
  （反向 2_1 桥）的接线。诚实域 = **跳跃后段** `i + 2 ≤ n ≤ k − 1`（flat-run 前提
  `i + 1 ≤ n` 的来源域；跳跃前段 C1 仍为槽——见 DELIVERY）。
* §2 `pW30_hstepEG`：run 前件 hstep 槽在 **EGHNAVX 语境**下的一行放电形
  （`pW26_hstep_at_run` 的 ∀-包装；槽的最终替代形）。
* §3 `pW30_hstep_wire`：抽象槽（W28 签名）前提 = `n+1 ≤ i` 域，**不足以**直接过
  `pW5b_hstep`（该件在索引 i 处还要 hflat/hnc）⇒ 如实列入三项端点补强
  （来源：EGHNAVX 首 run 分支给 hflat@i；hcol 给 hnc@i、hnc@(i+1)），
  装配后经 `pW5b_hstep` 得运行结论。**不造条件形充数**。

判据：三件 axioms 标准三零 sorryAx。
-/
import Kepler.Text.LocalFanStepW29

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 hprev-C1 供给（跳跃后段） -/

/-- **hprev-C1 供给件**（B 支跳跃后段）：`pW5b_flat_mem`（w 侧 flat-run 成员）
+ `pW5w2_affGt_prev_21`（反向 2_1 桥）⇒
`vv n ∈ affGt {0,p}{vv(n-1)}`（`i+2 ≤ n ≤ k−1`）。
诚实域说明：flat-run 前提 `i+1 ≤ n` 只在跳跃后段可用 ⇒ 本件供 `i ≥` 段；
跳跃前段（`2 ≤ n ≤ i+1`）不在本件范围（仍为槽，来源缺口记 DELIVERY）。 -/
theorem pW30_hprevC1 (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hiter : ∀ i, (rhoNode1_p2 FF)^[i] p = vv i)
    (hbta : ∀ i, azim 0 p (vv 1) (vv i) = bta i)
    {i : ℕ} (hi : i < k - 1) (hbilast : bta (i + 1) = bta (k - 1)) :
    ∀ n : ℕ, i + 2 ≤ n → n ≤ k - 1 → vv n ∈ affGt ({0, p} : Set V3) {vv (n - 1)} := by
  have hl : localFan_p2 V E FF := hcl.1
  intro n hin hnk
  refine pW5w2_affGt_prev_21 hcl hp hiter (n := n) (by omega) (by omega)
    ?_ ?_ ?_ ?_
  · -- `vv (n-1) ∈ affGt {0,p}{ιp}`：flat-run 成员（索引 n-1，`i+1 ≤ n-1`）
    exact pW5b_flat_mem hcl hg hp hk hiter hbta hi hbilast (n := n - 1)
      (by omega) (by omega)
  · -- `vv n ∈ affGt {0,p}{ιp}`：flat-run 成员（索引 n）
    exact pW5b_flat_mem hcl hg hp hk hiter hbta hi hbilast (n := n)
      (by omega) (by omega)
  · -- `vv (n-1) ≠ 0`
    intro hcon
    have hV : vv (n - 1) ∈ V := by
      rw [← hiter (n - 1)]
      exact LOCAL_FAN_ITER_RHO_NODE_IN_V hl hp (n - 1)
    exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
  · -- `vv (n-1) ≠ p`
    intro hcon
    have hd := LOFA_IMP_DIS_ELMS23 hl hp 0 (n - 1) (by omega) (by omega)
    rw [hiter (n - 1), show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact hd hcon

/-! ## §2 hstep 消槽：EGHNAVX 语境的一行放电 -/

/-- **hstep 槽的 EGHNAVX 语境形态**（终装替代形）：携带（bta, hbta, hcol,
`bta i = 0`）的 run 前件槽——放电 = 一行 `pW26_hstep_at_run`。
v4 链的抽象槽（hflat/hnc 前件形）在 EGHNAVX 语境下由此形态替换。 -/
theorem pW30_hstepEG (hcl : convexLocalFan_p2 V E FF) :
    ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ (bta : ℕ → ℝ), (∀ n, azim 0 p (vv 1) (vv n) = bta n) →
      (∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3)) →
      ∀ (i : ℕ), i + 1 < V.ncard → bta i = 0 →
        ∀ n, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)} :=
  fun _ hp _ hiter _ hbta hcol _ hik hbi =>
    pW26_hstep_at_run hcl hp hiter hbta hcol hik hbi

/-! ## §3 抽象槽的诚实补全（端点补强三项，`pW5b_hstep` 装配） -/

/-- **抽象槽的运行结论（诚实补全形）**：W28 槽前提（hflat/hnc 的 `n+1 ≤ i` 域）
**加三项端点补强** ⇒ 运行结论。补强来源（均 in-library）：
`hflat_i` ← EGHNAVX 首 run 分支（`vv i ∈ {vv m | 0<m ∧ m ≤ i}` 的成员）；
`hnc_i`/`hnc_i1` ← `hcol`（generic 非共线）+ `LOFA_IMP_DIS_ELMS23`。
必要性的机器证据：`pW5b_hstep` 体内在索引 `n+1` 处用 hflat/hnc（n+1 ≤ i 时
即索引 i），超出 `n+1 ≤ i` 前件域。 -/
theorem pW30_hstep_wire (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    {i : ℕ} (hik : i + 1 < V.ncard)
    (hflat : ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1})
    (hnc : ∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n))
    (hflat_i : vv i ∈ affGt ({0, p} : Set V3) {vv 1})
    (hnc_i : ¬ Collinear3 (0 : V3) p (vv i))
    (hnc_i1 : ¬ Collinear3 (0 : V3) p (vv (i + 1))) :
    ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)} := by
  have hρ : rhoNode1_p2 FF p = vv 1 := by
    have h := hiter 1
    simpa using h
  refine pW5b_hstep hcl hp hiter (by omega : i < V.ncard) ?_ ?_
  · intro n hn1 hni
    rw [hρ]
    rcases Nat.lt_or_ge n i with h | h
    · exact hflat n (by omega) (by omega)
    · rw [show n = i from by omega]
      exact hflat_i
  · intro n hn1 hni
    rcases Nat.lt_or_ge n i with h | h
    · exact hnc n (by omega) (by omega)
    · rcases Nat.lt_or_ge n (i + 1) with h2 | h2
      · rw [show n = i from by omega]
        exact hnc_i
      · rw [show n = i + 1 from by omega]
        exact hnc_i1

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW30_hprevC1
#print axioms Kepler.Text.pW30_hstepEG
#print axioms Kepler.Text.pW30_hstep_wire
