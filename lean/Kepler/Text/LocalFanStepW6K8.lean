/-
Kepler/Text/LocalFanStepW6K8.lean — wave C-W6-K7 patch ①：affGe 成员槽孪生形。

`pW6k7_stepB_sol_nonneg` 的望远镜槽（径向零点形态）转成**望远镜直供形态**
（affGe 成员，HOL NKEZBFC.hl:2281/2519 的 `ivs/rho_node1 FF u ∈ aff_ge
{0} {v, u}` 形），既有陈述零改——另立孪生形主件。

转换链（每槽 ~10 行）：`Set.pair_comm`（{p,u} → {u,p}）+
`pW6k6_azim_zero_of_affGe`（closed-cone 径向零点，§3 已落）+
`azim_eq_zero_symm`（测角换序）；边界退化（β = 0 支）由 §3 内部已收
（y = β•a 退化约定）。
-/
import Kepler.Text.LocalFanStepW6K7

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **patch ① 孪生形**：槽为望远镜直供的 affGe 成员形态，
`ι(vv j p) ∈ affGe {0} {p, vv j p}`、`ρ(vv(j+1) p) ∈ affGe {0} {p, vv(j+1) p}`。 -/
theorem pW6k8_stepB_sol_nonneg_affGe
    (hcl : convexLocalFan_p2 V E FF) (hg : generic_p2 V E)
    (hnc : ¬ ∃ p q : V3, p ∈ V ∧ q ∈ V ∧
      ∀ e ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 e E)
    (hk4 : 3 < V.ncard)
    (hslot_u : ∀ p : V3, p ∈ V → ∀ j : ℕ, 0 < j → j + 1 < V.ncard →
      ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)
        ∈ affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[j] p})
    (hslot_w : ∀ p : V3, p ∈ V → ∀ j : ℕ, j + 2 < V.ncard →
      rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)
        ∈ affGe ({0} : Set V3) {p, (rhoNode1_p2 FF)^[j+1] p}) :
    0 ≤ solLocal_p9 E FF := by
  have hlf : localFan_p2 V E FF := hcl.1
  have h0V : (0 : V3) ∉ V := (CVLF_LF_F hcl).2.2.2.2.1
  have hVV : ∀ p ∈ V, ∀ n : ℕ, (rhoNode1_p2 FF)^[n] p ∈ V :=
    fun p hp n => LOCAL_FAN_ITER_RHO_NODE_IN_V hlf hp n
  refine pW6k7_stepB_sol_nonneg hcl hg hnc hk4 ?_ ?_
  · -- hslot_u：affGe 成员 ⇒ 径向零点
    intro p hp j hj0 hj
    have huV : (rhoNode1_p2 FF)^[j] p ∈ V := hVV p hp j
    have hpu : p ≠ (rhoNode1_p2 FF)^[j] p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 j (by omega) (by omega)
      rw [show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact fun h => hd h.symm
    have hmem := hslot_u p hp j hj0 hj
    rw [Set.pair_comm] at hmem
    have hnc_up : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j] p) p := by
      have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
        ((rhoNode1_p2 FF)^[j] p) huV (Ne.symm hpu)
      rwa [← show ({0, (rhoNode1_p2 FF)^[j] p, p} : Set V3)
        = ({0, p, (rhoNode1_p2 FF)^[j] p} : Set V3) from by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    have hι : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j] p)
        (ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p)) :=
      LOFA_IMP_NOT_COLL_IVS hlf huV
    have hz := pW6k6_azim_zero_of_affGe
      (a := (rhoNode1_p2 FF)^[j] p) (x := p)
      (y := ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[j] p))
      (fun h => h0V (h ▸ huV)) hpu (fun h => h0V (h ▸ hp)) hnc_up hmem
    exact (azim_eq_zero_symm hnc_up hι).mp hz
  · -- hslot_w：affGe 成员 ⇒ 径向零点
    intro p hp j hj
    have hwV : (rhoNode1_p2 FF)^[j+1] p ∈ V := hVV p hp (j + 1)
    have hpw : p ≠ (rhoNode1_p2 FF)^[j+1] p := by
      have hd := LOFA_IMP_DIS_ELMS23 hlf hp 0 (j + 1) (by omega) (by omega)
      rw [show (rhoNode1_p2 FF)^[0] p = p from rfl] at hd
      exact fun h => hd h.symm
    have hmem := hslot_w p hp j hj
    rw [Set.pair_comm] at hmem
    have hnc_wp : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j+1] p) p := by
      have h := PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf (fun _ _ => trivial) hg p hp
        ((rhoNode1_p2 FF)^[j+1] p) hwV (Ne.symm hpw)
      rwa [← show ({0, (rhoNode1_p2 FF)^[j+1] p, p} : Set V3)
        = ({0, p, (rhoNode1_p2 FF)^[j+1] p} : Set V3) from by
        ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
    have hρ : ¬ Collinear3 (0 : V3) ((rhoNode1_p2 FF)^[j+1] p)
        (rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p)) :=
      LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf hwV
    have hz := pW6k6_azim_zero_of_affGe
      (a := (rhoNode1_p2 FF)^[j+1] p) (x := p)
      (y := rhoNode1_p2 FF ((rhoNode1_p2 FF)^[j+1] p))
      (fun h => h0V (h ▸ hwV)) hpw (fun h => h0V (h ▸ hp)) hnc_wp hmem
    exact (azim_eq_zero_symm hnc_wp hρ).mp hz

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW6k8_stepB_sol_nonneg_affGe
#print axioms Kepler.Text.pW6k8_stepB_sol_nonneg_affGe
