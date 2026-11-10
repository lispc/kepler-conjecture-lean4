/-
Kepler/Text/LocalFanStepW29.lean — wave W29：v4 链 part 2（收口）。

照 `LocalFanStepW22` 的 `pW19_stepB_sol_nonneg_v2` 孪生复刻，差异三处对齐 part 1：
① `hstep` 用 **run 前件形**（签名与 `pW6k7_stepB_sol_nonneg_v4` 一致）；
② `hslot_w` 用 W27 诚实域 `0 < j`；
③ 消费 `pW6k8_stepB_sol_nonneg_affGe_v4`（u 侧 affGe 放电整体消失——由
   part 1 的 hstep 槽内部放电承接；w 侧转换逐字保留）。
C2 分解件按 v3 形态逐字对齐（不重新设计）：`pW24_stepB_sol_nonneg_v4`
= `hstep`(run 前件) + `hprevC1` + `hprevC2` → `pW19_v4`（经
`pW20_hprev_iff_21` 装配 hprev-v2）。

件目：
* §1 `pW19_stepB_sol_nonneg_v4`：w 侧 affGe 槽（pW5w_telescope i:=1）+ 假支。
* §2 `pW19_nkezbfc_prep_p9_v4`：LA9:3196 下游重述孪生（hslots 对 =
  (run 前件 hstep, hprev-v2)）。
* §3 `pW24_stepB_sol_nonneg_v4`：C1/C2 分解孪生（v3 形态逐字）。
-/
import Kepler.Text.LocalFanStepW28

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## §1 v4 装配（w 侧 affGe 槽 + 假支） -/

/-- **W19 装配 v4**：`hstep` run 前件形 + `hprev`（v2 诚实域 `2 ≤ n`）⇒
`0 ≤ solLocal_p9`。u 侧由 part 1 的 hstep 槽承接（本件不再放电）；w 侧
affGe 槽由 `pW5w_telescope`（`i := 1`）逐字复刻 v2。 -/
theorem pW19_stepB_sol_nonneg_v4
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ (i : ℕ), i + 1 < V.ncard →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
      ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
    (hprev : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
        vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  by_cases hlt : 3 < V.ncard
  · refine pW6k8_stepB_sol_nonneg_affGe_v4 hcl hg hnc hlt hstep ?_
    -- w 侧 affGe 槽：pW5w_telescope（i := 1，hprev-v2）+ 端点自成员
    intro p hp j hj0 hj
    have hprevb : ∀ n : ℕ, 1 + 1 ≤ n → n ≤ V.ncard - 1 →
        (rhoNode1_p2 FF)^[n] p ∈ affGt ({0} : Set V3)
          {p, (rhoNode1_p2 FF)^[n - 1] p} :=
      fun n hn hk => hprev p hp (fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl)
        n (by omega) hk
    have htel := pW5w_telescope (i := 1) hcl hp
      (vv := fun m => (rhoNode1_p2 FF)^[m] p) (fun _ => rfl) hprevb
    have hjt : V.ncard - j - 2 < V.ncard - 1 - 1 := by omega
    have hne1 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ≠ 0 := by
      intro hcon
      have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p ∈ V :=
        LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
      exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
    have hne2 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ≠ 0 := by
      intro hcon
      have hV : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p ∈ V :=
        LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp _
      exact (CVLF_LF_F hcl).2.2.2.2.1 (hcon ▸ hV)
    have hne12 : (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2) - 1] p
        ≠ (rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp
        (V.ncard - (V.ncard - j - 2) - 1) (V.ncard - (V.ncard - j - 2))
        (by omega) (by omega)
      exact Ne.symm hd
    have hidx1 : V.ncard - (V.ncard - j - 2) - 1 = j + 1 := by omega
    have hidx2 : V.ncard - (V.ncard - j - 2) = j + 2 := by omega
    have hz := (htel (V.ncard - j - 2) hjt
      ((rhoNode1_p2 FF)^[V.ncard - (V.ncard - j - 2)] p)).mpr
      ⟨V.ncard - j - 2, le_rfl,
        pW19_mem_affGe_pair_right hne1 hne2 hne12⟩
    rw [hidx1] at hz
    rw [hidx2] at hz
    have hρw : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j + 1] p) = (rhoNode1_p2 FF)^[j + 2] p := by
      rw [show j + 2 = Nat.succ (j + 1) from rfl]
      exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (j + 1) p).symm
    rw [hρw]
    exact hz
  · -- 假支：ncard = 3
    have h3 : 3 ≤ V.ncard := CARD_VERTEX_GE_3_LOCAL_FAN_p9 hcl
    exact SOL_LOCAL_FAN_POS_CASE3_p9 hcl (by omega)

/-! ## §2 LA9:3196 下游同形重述（v4 孪生） -/

/-- `NKEZBFC_PREP_p9`（LA9:3196）下游同形重述 v4：hslots 对 =
（run 前件 hstep，hprev-v2），其余与 v2 逐字同构。 -/
theorem pW19_nkezbfc_prep_p9_v4
    (h : EJRCFJD_concl_p9)
    (hslots : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
      (_ : convexLocalFan_p2 V E FF) (_ : generic_p2 V E),
      (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ (i : ℕ), i + 1 < V.ncard →
        (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
        (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
        ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
      ∧ (∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
        (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
        ∀ n : ℕ, 2 ≤ n → n ≤ V.ncard - 1 →
          vv n ∈ affGt ({0} : Set V3) {p, vv (n - 1)})) :
    ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E → 0 ≤ solLocal_p9 E FF := by
  intro V E FF hcl hg
  exact p9_main_induction h
    (fun V' E' FF' hcl' hg' hnc' =>
      pW19_stepB_sol_nonneg_v4 hcl' hg' hnc'
        (hslots V' E' FF' hcl' hg').1 (hslots V' E' FF' hcl' hg').2)
    V.ncard V E FF hcl hg rfl

/-! ## §3 C1/C2 分解孪生（v3 形态逐字） -/

/-- **W25-① 三槽条件形 v4**：`hstep`（run 前件） + C1 + C2 两槽 ⇒
`0 ≤ solLocal_p9 E FF`（`pW24_stepB_sol_nonneg_v3` 的机械孪生：hprev 经
`pW20_hprev_iff_21` 装配后交 `pW19_v4`）。 -/
theorem pW24_stepB_sol_nonneg_v4
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hstep : ∀ (p : V3), p ∈ V → ∀ (vv : ℕ → V3),
      (∀ n, (rhoNode1_p2 FF)^[n] p = vv n) →
      ∀ (i : ℕ), i + 1 < V.ncard →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0, p} : Set V3) {vv 1}) →
      (∀ n : ℕ, 0 < n → n + 1 ≤ i → ¬ Collinear3 (0 : V3) p (vv n)) →
      ∀ n : ℕ, 0 < n → n + 1 ≤ i → vv n ∈ affGt ({0} : Set V3) {p, vv (n + 1)})
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
  refine pW19_stepB_sol_nonneg_v4 hcl hg hnc hstep ?_
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
#print axioms Kepler.Text.pW19_stepB_sol_nonneg_v4
#print axioms Kepler.Text.pW19_nkezbfc_prep_p9_v4
#print axioms Kepler.Text.pW24_stepB_sol_nonneg_v4
