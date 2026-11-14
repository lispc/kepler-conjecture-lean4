/-
LocalAuto22Close — OCBICBY 收口汇点（DAG：LA22 不能 import LA19，见
docs/def-fix-charters/ocbicby-close/README.md）。四条声明逐字节下移自
LocalAuto22（donor HEAD 393405f3），无陈述/证明改动。
└──
-/

import Kepler.Text.LocalAuto22
import Kepler.Text.LocalAuto19
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

private theorem ocb_periodic_mod {α : Sort u} {f : ℕ → α} {n : ℕ} (hper : Periodic f n) :
    ∀ m, f (m % n) = f m := by
  have hstep : ∀ q r, f (q * n + r) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have h1 : f (q * n + r + n) = f (q * n + r) := hper _
      have h2 : (q + 1) * n + r = q * n + r + n := by ring
      rw [h2, h1, ih r]
  intro m
  conv_rhs => rw [show m = m / n * n + m % n from by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m n).symm]
  rw [hstep]

private theorem ocb_pent_inputs (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs5T1 vv) (j : ℕ) (hj : j < 5)
    (ht : taustarV39 scs5T1 vv < 0) :
    (0 ≤ deltaY ‖vv (j + 1)‖ ‖vv j‖ ‖vv (j + 2)‖ (dist (vv j) (vv (j + 2))) 2 2) ∧
    (0 ≤ deltaY ‖vv (j + 4)‖ ‖vv j‖ ‖vv (j + 3)‖ (dist (vv j) (vv (j + 3))) 2 2) ∧
    (dihY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2 ≤
      dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖ 2 (dist (vv j) (vv (j + 3)))
          (dist (vv j) (vv (j + 2))) +
      dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 1)‖ 2 2 (dist (vv j) (vv (j + 2))) +
      dihY ‖vv j‖ ‖vv (j + 3)‖ ‖vv (j + 4)‖ 2 2 (dist (vv j) (vv (j + 3)))) := by
  have hann : ∀ i : ℕ, vv i ∈ ballAnnulus := fun i => hB.1 (Set.mem_range_self i)
  have hper5 : Periodic vv 5 := hB.2.1
  have hdij : ∀ i i' : ℕ, csAdj 5 2 cstab i i' ≤ dist (vv i) (vv i') ∧
      dist (vv i) (vv i') ≤ csAdj 5 2 6 i i' := hB.2.2.1
  have hedge : ∀ i : ℕ, dist (vv i) (vv (i + 1)) = 2 :=
    fun i => scs_5T1_props_p22.2.2.2 vv i hB
  have hinj : ∀ i i' : ℕ, i < 5 ∧ i' < 5 ∧ vv i = vv i' → i = i' :=
    vv_inj_lemma_p22 scs5T1 vv 5 is_scs_5T1_p22 hB rfl
  have hgen : scsGeneric vv := scs_5T1_generic_p22 h vv hB ht
  have hgen' : Generic (Set.range vv) (Set.range fun n : ℕ => {vv n, vv (n + 1)}) := hgen
  have hcf : ConvexLocalFan (Set.range vv)
      (Set.range fun i => {vv i, vv (i + 1)}) (Set.range fun i => (vv i, vv (i + 1))) := by
    rcases hB.2.2.2 with hk3 | hcf
    · exact absurd hk3 (by norm_num : ¬ (5 : ℕ) ≤ 3)
    · exact hcf
  have h3le5 : (3 : ℕ) ≤ 5 := by norm_num
  have hmod : ∀ m : ℕ, vv (m % 5) = vv m := fun m => ocb_periodic_mod hper5 m
  have hvvne : ∀ c d : ℕ, c < 5 → d < 5 → c ≠ d → vv (j + c) ≠ vv (j + d) := by
    intro c d hc hd hcd he
    have h1 : vv ((j + c) % 5) = vv ((j + d) % 5) := by
      rw [hmod (j + c), hmod (j + d)]
      exact he
    have h2 := hinj ((j + c) % 5) ((j + d) % 5)
      ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), h1⟩
    omega
  have hprop : ∀ c d : ℕ, c < 5 → d < 5 → c ≠ d →
      ¬ Collinear3 0 (vv (j + c)) (vv (j + d)) := by
    intro c d hc hd hcd
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range vv)
      (Set.range fun n : ℕ => {vv n, vv (n + 1)}) (Set.range fun n : ℕ => (vv n, vv (n + 1)))
      (vv (j + c)) (vv (j + d)) hcf.1 (Set.mem_range_self _) (Set.mem_range_self _)
      (hvvne c d hc hd hcd) hgen'
  have hfanle : ∀ c : ℕ, c < 5 → azim 0 (vv (j + c)) (vv ((j + c) + 1)) (vv ((j + c) + 4)) ≤
      Real.pi := by
    intro c hc
    have hmem : (vv (j + c), vv ((j + c) + 1)) ∈
        (Set.range fun n : ℕ => (vv n, vv (n + 1))) := Set.mem_range_self _
    have h1 := (hcf.2 (vv (j + c), vv ((j + c) + 1)) hmem).1
    rw [azim_in_fan_azim_p22 vv _ 5 (j + c) hper5 h3le5 hinj rfl,
      show (j + c) + (5 - 1) = (j + c) + 4 from rfl] at h1
    exact h1
  have split_a := vv_split_azim_generic_p22 vv 5 j 3 4 hper5 h3le5
    (by norm_num : (0 : ℕ) < 3) (by norm_num : (3 : ℕ) < 4) (by norm_num : (4 : ℕ) < 5)
    hgen' hcf hinj
  have split_a2 := vv_split_azim_generic_p22 vv 5 j 2 3 hper5 h3le5
    (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) < 3) (by norm_num : (3 : ℕ) < 5)
    hgen' hcf hinj
  have hA0le : azim 0 (vv j) (vv (j + 1)) (vv (j + 4)) ≤ Real.pi := by
    have hf0 := hfanle 0 (by norm_num)
    rw [show j + 0 = j from rfl, show (j + 0) + 1 = j + 1 from rfl,
      show (j + 0) + 4 = j + 4 from rfl] at hf0
    exact hf0
  have hA1le : azim 0 (vv j) (vv (j + 1)) (vv (j + 2)) ≤ Real.pi := by
    have hf0 := hfanle 0 (by norm_num)
    rw [show j + 0 = j from rfl, show (j + 0) + 1 = j + 1 from rfl,
      show (j + 0) + 4 = j + 4 from rfl] at hf0
    have e := split_a
    rw [split_a2] at e
    linarith [azim_nonneg 0 (vv j) (vv (j + 2)) (vv (j + 3)),
      azim_nonneg 0 (vv j) (vv (j + 3)) (vv (j + 4))]
  have hA2le : azim 0 (vv j) (vv (j + 2)) (vv (j + 3)) ≤ Real.pi := by
    have hf0 := hfanle 0 (by norm_num)
    rw [show j + 0 = j from rfl, show (j + 0) + 1 = j + 1 from rfl,
      show (j + 0) + 4 = j + 4 from rfl] at hf0
    have e := split_a
    rw [split_a2] at e
    linarith [azim_nonneg 0 (vv j) (vv (j + 1)) (vv (j + 2)),
      azim_nonneg 0 (vv j) (vv (j + 3)) (vv (j + 4))]
  have hA3le : azim 0 (vv j) (vv (j + 3)) (vv (j + 4)) ≤ Real.pi := by
    have hf0 := hfanle 0 (by norm_num)
    rw [show j + 0 = j from rfl, show (j + 0) + 1 = j + 1 from rfl,
      show (j + 0) + 4 = j + 4 from rfl] at hf0
    have e := split_a
    rw [split_a2] at e
    linarith [azim_nonneg 0 (vv j) (vv (j + 1)) (vv (j + 2)),
      azim_nonneg 0 (vv j) (vv (j + 2)) (vv (j + 3))]
  have cA13 : azim 0 (vv j) (vv (j + 1)) (vv (j + 4)) = dihV 0 (vv j) (vv (j + 1)) (vv (j + 4)) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 1 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 4 (by norm_num) (by norm_num) (by norm_num)) hA0le
  have cA1 : azim 0 (vv j) (vv (j + 1)) (vv (j + 2)) = dihV 0 (vv j) (vv (j + 1)) (vv (j + 2)) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 1 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 2 (by norm_num) (by norm_num) (by norm_num)) hA1le
  have cA2 : azim 0 (vv j) (vv (j + 2)) (vv (j + 3)) = dihV 0 (vv j) (vv (j + 2)) (vv (j + 3)) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 2 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 3 (by norm_num) (by norm_num) (by norm_num)) hA2le
  have cA3 : azim 0 (vv j) (vv (j + 3)) (vv (j + 4)) = dihV 0 (vv j) (vv (j + 3)) (vv (j + 4)) :=
    AZIM_DIHV_SAME_STRONG (hprop 0 3 (by norm_num) (by norm_num) (by norm_num))
      (hprop 0 4 (by norm_num) (by norm_num) (by norm_num)) hA3le
  -- edge facts
  have hcommj : dist (vv (j + 1)) (vv j) = 2 := by
    rw [dist_comm]; exact hedge j
  have hcommj3 : dist (vv (j + 4)) (vv (j + 3)) = 2 := by
    rw [dist_comm]; exact hedge (j + 3)
  have hdj4 : dist (vv j) (vv (j + 4)) = 2 := by
    have h := hedge (j + 4)
    rw [show (j + 4) + 1 = j + 5 from rfl, hper5 j] at h
    rw [dist_comm]; exact h
  have hcommj4 : dist (vv (j + 4)) (vv j) = 2 := by rw [dist_comm]; exact hdj4
  -- delta nonnegativity (DELTA_Y_POS_4POINTS)
  have hd1 : 0 ≤ deltaY ‖vv (j + 1)‖ ‖vv j‖ ‖vv (j + 2)‖ (dist (vv j) (vv (j + 2))) 2 2 := by
    have h := DELTA_Y_POS_4POINTS (0 : V3) (vv (j + 1)) (vv j) (vv (j + 2))
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge (j + 1), hcommj] at h
    exact h
  have hd2 : 0 ≤ deltaY ‖vv (j + 4)‖ ‖vv j‖ ‖vv (j + 3)‖ (dist (vv j) (vv (j + 3))) 2 2 := by
    have h := DELTA_Y_POS_4POINTS (0 : V3) (vv (j + 4)) (vv j) (vv (j + 3))
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hcommj3, hcommj4] at h
    exact h
  -- the numeric input `0 < deltaY ... cstab ...` (registry 2125338128)
  have hnorm : ∀ i : ℕ, 2 ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 := fun i => ballAnnulus_norm_bounds (hann i)
  have h252 : (2:ℝ) * h0 = 2.52 := by rw [h0_eq_p22]; norm_num
  have hdlt : 0 < deltaY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2 := by
    have hreg : mainEstimate_2125338128 :=
      h "2125338128" (by simp [mainNonlinearTerminalV11Ids_t11])
    have h := hreg ‖vv (j + 1)‖ ‖vv (j + 4)‖ ‖vv j‖ (dist (vv j) (vv (j + 4)))
      (dist (vv j) (vv (j + 1))) cstab
      (hnorm (j + 1)).1 (by rw [← h252]; exact (hnorm (j + 1)).2)
      (hnorm (j + 4)).1 (by rw [← h252]; exact (hnorm (j + 4)).2)
      (hnorm j).1 (by rw [← h252]; exact (hnorm j).2)
      (by linarith [hdj4]) (by linarith [hdj4])
      (by linarith [hedge j]) (by linarith [hedge j])
      (by rw [cstab_eq_p22]; norm_num) (le_of_eq cstab_eq_p22)
    rw [hdj4, hedge j] at h
    have hperm : deltaY ‖vv (j + 1)‖ ‖vv (j + 4)‖ ‖vv j‖ 2 2 cstab
        = deltaY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2 := by
      unfold deltaY deltaX; ring
    rw [hperm] at h
    exact h
  -- `0 ≤ deltaY` at the true 4th slot (DELTA_Y_POS_4POINTS)
  have hdnn : 0 ≤ deltaY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖
      (dist (vv (j + 1)) (vv (j + 4))) 2 2 := by
    have h := DELTA_Y_POS_4POINTS (0 : V3) (vv j) (vv (j + 1)) (vv (j + 4))
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hdj4, hedge j] at h
    exact h
  have hdiag30 : ∀ i : ℕ, scsDiag 5 i (i + 3) := by
    intro i
    refine ⟨MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) < 5)
        (by norm_num : (3 : ℕ) ≠ 0) i,
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) < 5)
        (by norm_num : (2 : ℕ) ≠ 0) (i + 1),
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (4 : ℕ) < 5)
        (by norm_num : (4 : ℕ) ≠ 0) i⟩
  have h4le : cstab ≤ dist (vv (j + 1)) (vv (j + 4)) :=
    scs_5T1_props_p22.2.2.1 vv (j + 1) (j + 4) hB (hdiag30 (j + 1))
  have hmono := dih_y_mono_p22 ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2
    (dist (vv (j + 1)) (vv (j + 4))) h4le (by linarith [(hnorm j).1])
    (by rw [cstab_eq_p22]; norm_num) hdlt hdnn
  -- dihV <-> dihY conversions
  have hprop01 := hprop 0 1 (by norm_num) (by norm_num) (by norm_num)
  have hprop02 := hprop 0 2 (by norm_num) (by norm_num) (by norm_num)
  have hprop03 := hprop 0 3 (by norm_num) (by norm_num) (by norm_num)
  have hprop04 := hprop 0 4 (by norm_num) (by norm_num) (by norm_num)
  have e13v : dihV 0 (vv j) (vv (j + 1)) (vv (j + 4)) =
      dihY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ (dist (vv (j + 1)) (vv (j + 4))) 2 2 := by
    rw [DIHV_EQ_DIH_Y_4PT 0 (vv j) (vv (j + 1)) (vv (j + 4)) hprop01 hprop04]
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hdj4, hedge j]
  have e1v : dihV 0 (vv j) (vv (j + 1)) (vv (j + 2)) =
      dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 1)‖ 2 2 (dist (vv j) (vv (j + 2))) := by
    rw [DIHV_EQ_DIH_Y_4PT 0 (vv j) (vv (j + 1)) (vv (j + 2)) hprop01 hprop02]
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge (j + 1), hedge j]
    exact (dihY_swap23_p19 ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 1)‖ 2 2
      (dist (vv j) (vv (j + 2)))).symm
  have e2v : dihV 0 (vv j) (vv (j + 2)) (vv (j + 3)) =
      dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖ 2 (dist (vv j) (vv (j + 3)))
        (dist (vv j) (vv (j + 2))) := by
    rw [DIHV_EQ_DIH_Y_4PT 0 (vv j) (vv (j + 2)) (vv (j + 3)) hprop02 hprop03]
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge (j + 2)]
  have e3v : dihV 0 (vv j) (vv (j + 3)) (vv (j + 4)) =
      dihY ‖vv j‖ ‖vv (j + 3)‖ ‖vv (j + 4)‖ 2 2 (dist (vv j) (vv (j + 3))) := by
    rw [DIHV_EQ_DIH_Y_4PT 0 (vv j) (vv (j + 3)) (vv (j + 4)) hprop03 hprop04]
    rw [dist_zero_left, dist_zero_left, dist_zero_left, hedge (j + 3), hdj4]
  have hsum : dihV 0 (vv j) (vv (j + 1)) (vv (j + 4)) =
      dihV 0 (vv j) (vv (j + 1)) (vv (j + 2)) + dihV 0 (vv j) (vv (j + 2)) (vv (j + 3)) +
        dihV 0 (vv j) (vv (j + 3)) (vv (j + 4)) := by
    rw [← cA13, ← cA1, ← cA2, ← cA3, split_a, split_a2]
  refine ⟨hd1, hd2, ?_⟩
  calc dihY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2
      ≤ dihY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ (dist (vv (j + 1)) (vv (j + 4))) 2 2 := hmono
    _ = dihV 0 (vv j) (vv (j + 1)) (vv (j + 4)) := e13v.symm
    _ = dihV 0 (vv j) (vv (j + 1)) (vv (j + 2)) + dihV 0 (vv j) (vv (j + 2)) (vv (j + 3)) +
        dihV 0 (vv j) (vv (j + 3)) (vv (j + 4)) := hsum
    _ = dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖ 2 (dist (vv j) (vv (j + 3)))
          (dist (vv j) (vv (j + 2))) +
        dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 1)‖ 2 2 (dist (vv j) (vv (j + 2))) +
        dihY ‖vv j‖ ‖vv (j + 3)‖ ‖vv (j + 4)‖ 2 2 (dist (vv j) (vv (j + 3))) := by
        rw [e1v, e2v, e3v]
        try ring

/-- The `terminal_pent_taum2` numeric assembly (HOL OCBICBY.hl:3357-3402) in the
box-hypothesis form (`hbox` = the flattened HOL `ineq` premise): `angle_sum_5T1`
splits on `20 <= delta_y`, each branch feeds `terminal_pent_taum_p19` (the
second branch at the slot permutation `y1 y3 y2 y4 y6 y5`, aligned with
`taum_sym2`).  Kept private because the public statement's `ineqP22` conclusion
is unsatisfiable as ported (`ineqP22` is a conjunction builder): see
`DELIVERY_D2.md` and the SF proposal. -/
private theorem ocb_terminal_pent_taum2_core (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hbox : ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2),
      (3.01, y5, 3.237), (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)] True)
    (hd1 : 0 ≤ deltaY y126 y1 y2 y6 2 2)
    (hd2 : 0 ≤ deltaY y135 y1 y3 y5 2 2)
    (hsub : dihY y1 y126 y135 cstab 2 2 ≤
        dihY y1 y2 y3 y4 y5 y6 + dihY y1 y2 y126 2 2 y6 +
          dihY y1 y3 y135 2 2 y5) :
    0.616 < taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6 + taum y135 y1 y3 y5 2 2 := by
  obtain ⟨c1l, c1u, c2l, c2u, c3l, c3u, c4l, c4u, c5l, c5u, c6l, c6u,
    c7l, c7u, c8l, c8u, _⟩ := hbox
  have hboxA : ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0),
      (2, y126, 2 * h0), (2, y135, 2 * h0), (2, y4, 2), (cstab, y5, 3.237),
      (cstab, y6, 3.237)] True :=
    ⟨c1l, c1u, c2l, c2u, c3l, c3u, c7l, c7u, c8l, c8u, c4l, c4u,
      (by rw [cstab_eq_p22]; exact c5l), c5u,
      (by rw [cstab_eq_p22]; exact c6l), c6u, trivial⟩
  have hp1 : deltaY y1 y2 y126 2 2 y6 = deltaY y126 y1 y2 y6 2 2 := by
    unfold deltaY deltaX; ring
  have hp2 : deltaY y1 y3 y135 2 2 y5 = deltaY y135 y1 y3 y5 2 2 := by
    unfold deltaY deltaX; ring
  have ha1 : 0 ≤ deltaY y1 y2 y126 2 2 y6 := by rw [hp1]; exact hd1
  have ha2 : 0 ≤ deltaY y1 y3 y135 2 2 y5 := by rw [hp2]; exact hd2
  have hdisj := angle_sum_5T1_p22 h y1 y2 y3 y4 y5 y6 y126 y135 hboxA hsub ha1 ha2
  rcases hdisj with hbig1 | hbig2
  · have h126 : (20:ℝ) ≤ deltaY y126 y1 y2 y6 2 2 := by rw [← hp1]; exact hbig1
    exact terminal_pent_taum_p19 h y1 y2 y3 y4 y5 y6 y126 y135 h126 hd2
      ⟨c1l, c1u⟩ ⟨c2l, c2u⟩ ⟨c3l, c3u⟩ ⟨c4l, c4u⟩ ⟨c5l, c5u⟩ ⟨c6l, c6u⟩
      ⟨c7l, c7u⟩ ⟨c8l, c8u⟩
  · have h135' : (20:ℝ) ≤ deltaY y135 y1 y3 y5 2 2 := by rw [← hp2]; exact hbig2
    have hres : (0.616:ℝ) < taum y135 y1 y3 y5 2 2 + taum y1 y3 y2 y4 y6 y5 +
        taum y126 y1 y2 y6 2 2 :=
      terminal_pent_taum_p19 h y1 y3 y2 y4 y6 y5 y135 y126 h135' hd1
        ⟨c1l, c1u⟩ ⟨c3l, c3u⟩ ⟨c2l, c2u⟩ ⟨c4l, c4u⟩ ⟨c6l, c6u⟩ ⟨c5l, c5u⟩
        ⟨c8l, c8u⟩ ⟨c7l, c7u⟩
    rw [((taum_sym2 y1 y2 y3 y4 y5 y6).2).symm] at hres
    linarith

/-- The `terminal_pent_taum2` instance consumed by `empty5T1_pent_bridge_p22`
(HOL OCBICBY.hl:3787): `ocb_pent_inputs` supplies the three geometric inputs and
`ocb_terminal_pent_taum2_core` the numeric assembly, with the 8 box slots built
from `BBsV39 scs5T1` (edges = 2, diagonals in `[cstab, 1+sqrt 5]`). -/
private theorem ocb_pent_taum2_instance (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs5T1 vv) (j : ℕ) (hj : j < 5)
    (hdj2 : dist (vv j) (vv (j + 2)) ≤ 1 + Real.sqrt 5)
    (hdj3 : dist (vv j) (vv (j + 3)) ≤ 1 + Real.sqrt 5)
    (ht : taustarV39 scs5T1 vv < 0) :
    0.616 < taum ‖vv (j + 1)‖ ‖vv j‖ ‖vv (j + 2)‖ (dist (vv j) (vv (j + 2))) 2 2
      + taum ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖ (dist (vv (j + 2)) (vv (j + 3)))
          (dist (vv j) (vv (j + 3))) (dist (vv j) (vv (j + 2)))
      + taum ‖vv (j + 4)‖ ‖vv j‖ ‖vv (j + 3)‖ (dist (vv j) (vv (j + 3))) 2 2 := by
  obtain ⟨hd1, hd2, hsub⟩ := ocb_pent_inputs h vv hB j hj ht
  have hann : ∀ i : ℕ, vv i ∈ ballAnnulus := fun i => hB.1 (Set.mem_range_self i)
  have hnorm : ∀ i : ℕ, 2 ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 :=
    fun i => ballAnnulus_norm_bounds (hann i)
  have hedge : ∀ i : ℕ, dist (vv i) (vv (i + 1)) = 2 :=
    fun i => scs_5T1_props_p22.2.2.2 vv i hB
  have hdiag20 : ∀ i : ℕ, scsDiag 5 i (i + 2) := by
    intro i
    refine ⟨MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) < 5)
        (by norm_num : (2 : ℕ) ≠ 0) i,
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (1 : ℕ) < 5)
        (by norm_num : (1 : ℕ) ≠ 0) (i + 1),
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) < 5)
        (by norm_num : (3 : ℕ) ≠ 0) i⟩
  have hdiag30 : ∀ i : ℕ, scsDiag 5 i (i + 3) := by
    intro i
    refine ⟨MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) < 5)
        (by norm_num : (3 : ℕ) ≠ 0) i,
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) < 5)
        (by norm_num : (2 : ℕ) ≠ 0) (i + 1),
      MOD_INJ1_ALT (by norm_num : (5 : ℕ) ≠ 0) (by norm_num : (4 : ℕ) < 5)
        (by norm_num : (4 : ℕ) ≠ 0) i⟩
  have hdj2low : cstab ≤ dist (vv j) (vv (j + 2)) :=
    scs_5T1_props_p22.2.2.1 vv j (j + 2) hB (hdiag20 j)
  have hdj3low : cstab ≤ dist (vv j) (vv (j + 3)) :=
    scs_5T1_props_p22.2.2.1 vv j (j + 3) hB (hdiag30 j)
  have hlt : (1:ℝ) + Real.sqrt 5 < 3.237 := by
    have h1 : Real.sqrt 5 < 2.237 := by
      have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 5, h5, sq_nonneg (Real.sqrt 5 - 2.237)]
    linarith
  have hbox : ineqP22 [(2, ‖vv j‖, 2 * h0), (2, ‖vv (j + 2)‖, 2 * h0),
      (2, ‖vv (j + 3)‖, 2 * h0), (2, dist (vv (j + 2)) (vv (j + 3)), 2),
      (3.01, dist (vv j) (vv (j + 3)), 3.237), (3.01, dist (vv j) (vv (j + 2)), 3.237),
      (2, ‖vv (j + 1)‖, 2 * h0), (2, ‖vv (j + 4)‖, 2 * h0)] True :=
    ⟨(hnorm j).1, (hnorm j).2, (hnorm (j + 2)).1, (hnorm (j + 2)).2,
      (hnorm (j + 3)).1, (hnorm (j + 3)).2,
      by linarith [hedge (j + 2)], by linarith [hedge (j + 2)],
      by linarith [cstab_eq_p22, hdj3low], by linarith [hdj3, hlt],
      by linarith [cstab_eq_p22, hdj2low], by linarith [hdj2, hlt],
      (hnorm (j + 1)).1, (hnorm (j + 1)).2, (hnorm (j + 4)).1, (hnorm (j + 4)).2,
      trivial⟩
  have hsub' : dihY ‖vv j‖ ‖vv (j + 1)‖ ‖vv (j + 4)‖ cstab 2 2 ≤
      dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖ (dist (vv (j + 2)) (vv (j + 3)))
          (dist (vv j) (vv (j + 3))) (dist (vv j) (vv (j + 2))) +
        dihY ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 1)‖ 2 2 (dist (vv j) (vv (j + 2))) +
      dihY ‖vv j‖ ‖vv (j + 3)‖ ‖vv (j + 4)‖ 2 2 (dist (vv j) (vv (j + 3))) := by
    simpa only [hedge (j + 2)] using hsub
  exact ocb_terminal_pent_taum2_core h ‖vv j‖ ‖vv (j + 2)‖ ‖vv (j + 3)‖
    (dist (vv (j + 2)) (vv (j + 3))) (dist (vv j) (vv (j + 3))) (dist (vv j) (vv (j + 2)))
    ‖vv (j + 1)‖ ‖vv (j + 4)‖ hbox hd1 hd2 hsub'

/-- HOL `empty_6T1` (giant; the analytic core of the terminal emptiness). -/
theorem empty_6T1_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv) : 0 ≤ taustarV39 scs6T1 vv := by
  sorry

/-- HOL `empty_5T1` (giant).  DISCHARGED 2026-11-14 (lane ocbicby5t1-w1): the
`VPWSHTO_PRIME` pentagon window `j` (`empty5T1_vpwshto_p22`) plus the analytic
bridge `empty5T1_pent_bridge_p22`; the bridge's numeric input is supplied by
`ocb_pent_taum2_instance` (geometry `ocb_pent_inputs` + the `terminal_pent_taum2`
assembly `ocb_terminal_pent_taum2_core`, HOL OCBICBY.hl:3476-3942). -/
theorem empty_5T1_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs5T1 vv) : 0 ≤ taustarV39 scs5T1 vv := by
  by_contra hle
  push_neg at hle
  obtain ⟨j, hj, hdj2, hdj3⟩ := empty5T1_vpwshto_p22 vv hB
  exact (not_lt_of_ge (empty5T1_pent_bridge_p22 h vv hB j hj hdj2 hdj3
    (ocb_pent_taum2_instance h vv hB j hj hdj2 hdj3 hle))) hle

/-- HOL `terminal_pent_taum2`.  STILL SORRY (2026-11-14): the ported conclusion
`ineqP22 [8 boxes] concl` is unsatisfiable — `ineqP22` builds a conjunction
(so the goal demands `2 ≤ y1` for the universally quantified `y1`), while HOL
`ineq` is the box *implication*.  Proof is ready as
`ocb_terminal_pent_taum2_core`; the public statement needs the SF
(`(hbox : ineqP22 [boxes] True)` premise) — see `DELIVERY_D2.md`. -/
theorem terminal_pent_taum2_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hd1 : 0 ≤ deltaY y126 y1 y2 y6 2 2)
    (hd2 : 0 ≤ deltaY y135 y1 y3 y5 2 2)
    (hsub : dihY y1 y126 y135 cstab 2 2 ≤
        dihY y1 y2 y3 y4 y5 y6 + dihY y1 y2 y126 2 2 y6 +
          dihY y1 y3 y135 2 2 y5) :
    ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2),
      (3.01, y5, 3.237), (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)]
      (0.616 < taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6 +
        taum y135 y1 y3 y5 2 2) := by
  sorry

/-- HOL `OCBICBY` 5T1 branch (OCBICBY.hl:4761), discharged via the
`arrow_rewrite_list` glue: `MMsV39 scs5T1 = ∅` since `BBprimeV39` needs
`taustarV39 < 0`, contradicting `empty_5T1_p22`. -/
theorem OCBICBY_5T1_p22 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs5T1} ∅ := by
  rw [scs_arrow_sing_empty_p22]
  ext vv
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨⟨⟨hbb, _, hneg⟩, _⟩, _, _, _, _, _⟩ := hv
  exact (not_le.mpr hneg) (empty_5T1_p22 h _ hbb)

/-- HOL `OCBICBY`: the 14 T-row arrows to the empty system (giant; discharges
LocalAuto16's `JEJTVGB_case_breakdown_p16` NEEDS marker when the `empty_*`
lane lands). -/
theorem OCBICBY_p22 (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs6T1} ∅ ∧ scsArrowV39 {scs5T1} ∅ ∧ scsArrowV39 {scs4T1} ∅ ∧
      scsArrowV39 {scs4T2} ∅ ∧ scsArrowV39 {scs4T3} ∅ ∧ scsArrowV39 {scs4T4} ∅ ∧
      scsArrowV39 {scs4T5} ∅ ∧ scsArrowV39 {scs3T1} ∅ ∧ scsArrowV39 {scs3T2} ∅ ∧
      scsArrowV39 {scs3T3} ∅ ∧ scsArrowV39 {scs3T4} ∅ ∧ scsArrowV39 {scs3T5} ∅ ∧
      scsArrowV39 {scs3T6'} ∅ ∧ scsArrowV39 {scs3T7} ∅ := by
  sorry

end Kepler.Text
