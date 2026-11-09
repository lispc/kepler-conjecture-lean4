/-
Kepler/Text/LocalFanStepBW2b.lean — wave C-W2b：B 支的跳跃索引存在性。

HOL 锚：`NKEZBFC.hl:1877-1884`。函数依赖（逐项）：

* `convexLocalFan_p2 V E FF`（取 `localFan_p2` 的 `INTERIOR_ANGLE1_POS`；
  并用 `pW1_azim_last` 的 `interior v = bta(k-1)`）；
* `v ∈ V`、`V.ncard = k`、`3 < k`；
* `hiter : ∀i, ρ^[i]v = vv i`、`hbta : ∀i, azim 0 v (vv 1) (vv i) = bta i`；
* **假设 `B : ∀i<k, bta i = 0 ∨ bta i = bta(k-1)`**（本件是 B 支内部的小件）；
* 结论：`∃ i < k-1, bta i = 0 ∧ bta(i+1) = bta(k-1)`。

不需 `interior v < π`：矛盾来自 `interior v = bta(k-1) > 0`（`INTERIOR_ANGLE1_POS`）
与全零归纳得到的 `bta(k-1)=0`。

陈述自查：`¬B` 下本命题不成立（缺口索引 `0 < bta i < bta(k-1)` 不满足 flat-run 前件，
且不保证存在 0→last 的跳跃）；因此本件必须带 `hB`。
-/
import Kepler.Text.LocalFanStepBW2

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **W2b**：B 支（全 0/全 last）下存在跳跃索引 `i`：`i<k-1`、`bta i=0`、
`bta(i+1)=bta(k-1)`（HOL NKEZBFC.hl:1877-1884）。 -/
theorem pW2b_jump_exists
    (hcl : convexLocalFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hk : V.ncard = k) (hk4 : 3 < k)
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v = vv i)
    (hbta : ∀ i, azim 0 v (vv 1) (vv i) = bta i)
    (hB : ∀ i, i < k → bta i = 0 ∨ bta i = bta (k - 1)) :
    ∃ i, i < k - 1 ∧ bta i = 0 ∧ bta (i + 1) = bta (k - 1) := by
  have hbta0 : bta 0 = 0 := by
    rw [← hbta 0]
    have hv0 : vv 0 = v := by rw [← hiter 0]; simp
    rw [hv0]
    unfold azim
    rw [if_pos (Or.inr (collinear3_pair_right (v0 := (0 : V3)) (v1 := v) rfl))]
  have hlast : azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) = bta (k - 1) :=
    pW1_azim_last hcl.1 hv hk hiter hbta
  have hpos : 0 < bta (k - 1) := by
    have hp := INTERIOR_ANGLE1_POS hcl.1 hv
    rw [show interiorAngle1_p2 0 FF v
        = azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) from rfl, hlast] at hp
    exact hp
  by_contra hno
  push Not at hno
  have hall : ∀ i, i < k → bta i = 0 := by
    intro i
    induction i with
    | zero => intro _; exact hbta0
    | succ n ih =>
      intro hn
      have hb : bta n = 0 := ih (by omega)
      rcases hB (n + 1) hn with h0 | hlastn
      · exact h0
      · exfalso
        have hnk1 : n < k - 1 := by omega
        exact (hno n hnk1 hb) hlastn
  have hz : bta (k - 1) = 0 := hall (k - 1) (by omega)
  linarith

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW2b_jump_exists
