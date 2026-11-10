/-
Kepler/Text/LocalFanStepW25.lean — wave W25-①：三槽条件形主件（hstep + C1 + C2）。

把 `pW19_stepB_sol_nonneg_v2` 的 `hprev` 槽（1_2 形，n ≥ 2）经
`pW20_hprev_iff_21` 精确分解为
  C1：`vv n ∈ affGt{0, p}{vv(n-1)}`（pW5w2 输出形）
  C2：`vv n ∈ affGt{0, vv(n-1)}{p}`（= 绕序槽的 det/cross-dot 消费点）
手头三槽 = 已知几何事实清单（hstep 前向 / C1 / C2），非任意假设；
C2 与绕序槽经 `pW22_c2_iff_det` / `pW24_c2_iff_crossdot` 互译（已在库）。
-/
import Kepler.Text.LocalFanStepW24
import Kepler.Text.LocalFanStepW20

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **W25-① 三槽条件形主件**：`hstep`（前向全 n）+ C1 + C2 两槽 ⇒ `0 ≤ solLocal_p9 E FF`。 -/
theorem pW24_stepB_sol_nonneg_v3
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 0 < n → n + 1 < V.ncard →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
    (hprevC1 : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
        vv n ∈ affGt ({0, p} : Set V3) {vv (n - 1)})
    (hprevC2 : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
        vv n ∈ affGt ({0, vv (n - 1)} : Set V3) {p}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  refine pW19_stepB_sol_nonneg_v2 hcl hg hnc hstep ?_
  intro p hp vv hiter n hn2 hnk
  have hVV : ∀ m : ℕ, vv m ∈ V := fun m => by
    rw [← hiter m]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp m
  have hne : vv (n - 1) ≠ p := by
    have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 (n - 1) (by omega) (by omega)
    rw [hiter (n - 1), show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
    exact hd
  have hncv : ¬ Collinear3 (0 : V3) p (vv (n - 1)) :=
    PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
      (vv (n - 1)) (hVV (n - 1)) hne
  exact (pW20_hprev_iff_21 hncv).mpr
    ⟨hprevC1 p hp vv hiter n hn2 hnk, hprevC2 p hp vv hiter n hn2 hnk⟩

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW24_stepB_sol_nonneg_v3
