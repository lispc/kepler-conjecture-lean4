/-
Kepler/Text/LocalFanStepW26.lean — wave W26-②：hstep 的 u-run 直供件（消槽放电件）。

判定（本波侦察，入账）：v3 链的 `hstep` 槽为**全 ∀ 形**，但其第二 run 的实例
不可证（`vv n ↦ vv(n+1)` 的径向序无保障，与 `hslot_w` 的 j=0 假支同机理，
W21 范围图谱的第三格）。消费者实际只调用 u-run 实例（K 案 `j := i₀`，
telescope 内 `n+1 ≤ j`）。⇒ 消槽的正确形态 = 槽携带 run 前件（v4 链），
以及本件：**EGHNAVX 直供的 u-run hstep 实例**（v4 消费件）——

`pW26_hstep_at_run`：EGHNAVX（bta i = 0 的 flat-run）+ generic ⇒
`∀ n, 0 < n → n+1 ≤ i → vv n ∈ affGt{0}{p, vv(n+1)}`
（= `pW5_flat_cone_order` 的放电：hflat 由 EGHNAVX 首 run 成员分支，
hnc 由 generic 非共线，ρ(p) = vv 1）。
-/
import Kepler.Text.LocalFanStepW25

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **W26-②**：u-run hstep 实例的 EGHNAVX 直供（v4 链放电件）。 -/
theorem pW26_hstep_at_run (hcl : convexLocalFan_p2 V E FF)
    {p : V3} (hp : p ∈ V) {vv : ℕ → V3} {bta : ℕ → ℝ} {i : ℕ}
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] p = vv n)
    (hbta : ∀ n, azim 0 p (vv 1) (vv n) = bta n)
    (hcol : ∀ z ∈ V, z ≠ p → ¬ Collinear ℝ ({0, p, z} : Set V3))
    (hik : i + 1 < V.ncard) (hbi : bta i = 0) :
    ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)} := by
  have hlf : localFan_p2 V E FF := hcl.1
  have hVV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  have hρ : rhoNode1_p2 FF p = vv 1 := by
    have h := hiter 1
    simpa using h
  obtain ⟨-, -, -, hflat⟩ :=
    EGHNAVX (pC_ConvexLocalFan_of_p2 hcl) hp rfl hcol hiter hbta
  refine pW5_flat_cone_order hcl hp hiter (by omega : i < V.ncard) ?_ ?_
  · -- hflat：首 run 成员 ⇒ affGt{0,p}{ρ(p)}
    intro n hn hni
    have hrun := (hflat i).1 ⟨hbi, by omega⟩
    have hmem : vv n ∈ {z : V3 | ∃ m, 0 < m ∧ m ≤ i ∧ vv m = z} :=
      ⟨n, by omega, by omega, rfl⟩
    have h2 : vv n ∈ affGt ({0, p} : Set V3) {vv 1} := hrun.2 hmem
    rw [hρ]
    exact h2
  · -- hnc：generic 非共线
    intro n hn hni
    have hne : vv n ≠ p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 n (by omega) (by omega)
      rw [hiter n, show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact hd
    exact hcol (vv n) (hVV n) hne

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW26_hstep_at_run
