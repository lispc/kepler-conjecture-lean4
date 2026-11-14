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

/-! ## LANE ocbicby6t4-w1 (2026-11-14): the 4T3/6T1 tail.

This file already imports both `LocalAuto22` (hence LocalAuto38) and
`LocalAuto19`, so it is the unique acyclic downstream point where the LA19
realified kit (`OWZLKVY4_p19`, `terminal_hex_taum_p19`) meets the LA38
`_p38` tau kit.  Contents of the lane (all NEW declarations; zero edits to
existing statements):

* `unit6'` — the HOL `unit6` body (`nonlin_def.hl:38`: the constant `1`).
  LA38's `unit6P38` stays its opaque stub; this real-bodied twin is what the
  `quad_4680581274_*'` bank below consumes.
* `taud_x_taum_x'` — twin of LA38:4729 (HOL terminal.hl:3764), via
  `OWZLKVY4_p19` at the square roots + the two `y_of_x` bridges.
* the `quad_4680581274` wrapper bank twins (HOL terminal.hl:3639-3940),
  carrying the HOL `LEMMA50` (cayleyR conic) / `LEMMA51` (discriminant)
  polynomial identities as local lemmas; stubs replaced by the real bodies
  `tauq` (`IneqClosureDefs`), `cayleytr_t11` (`LocalAuto1`) and `unit6'`.
* `empty_4T3_p22'` / `OCBICBY_4T3_p22'` (HOL terminal.hl:3943).
* `empty_6T1_p22_of_ht4nn` / `OCBICBY_6T1_p22_of_ht4nn` (HOL
  OCBICBY.hl:2855-3122 modulo the one LP box `ht4nn`).
-/

/-- HOL `unit6` (`nonlin_def.hl:38`): `unit6 x1 … x6 = 1` (constant).
Real-bodied twin of LA38's stub `unit6P38` (kept untouched there). -/
noncomputable def unit6' (_x1 _x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ := 1

/-- HOL `taud_x_taud` (`functional_equation.hl:1425`): `y_of_x taud_x = taud`
on the nonnegative cone (the same computation LA19's `OWZLKVY4_p19` uses as
its local `htx`). -/
theorem taud_x_taud_c (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) (h3 : 0 ≤ y3) :
    yOfX taudX_t11 y1 y2 y3 y4 y5 y6 = taudP19 y1 y2 y3 y4 y5 y6 := by
  unfold yOfX taudX_t11 taudP19 flatTermX_t11 flatTerm_t11 flatTerm_p19
    muY_t11 muY_p19 deltaY
  rw [Real.sqrt_mul_self h1, Real.sqrt_mul_self h2, Real.sqrt_mul_self h3]

/-- HOL `taud_x_taum_x` (terminal.hl:3764; LA38:4729 twin, byte-identical
statement): `taud_x ≤ taum_x` on the `scs_4T3`/`4680581274` x-box.
Route: `y_i := √x_i` (`taud_x_taud_c` + `taum_taum_x` are the two `y_of_x`
bridges and `OWZLKVY4_p19` is the y-space inequality). -/
theorem taud_x_taum_x' (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4 ≤ x1 → x1 ≤ (2 * h0) ^ 2 → 4 ≤ x2 → x2 ≤ (2 * h0) ^ 2 →
      4 ≤ x3 → x3 ≤ (2 * h0) ^ 2 → cstab ^ 2 ≤ x4 → x4 ≤ 3.915 ^ 2 →
      x5 = 4 → x6 = 4 → 0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      taudXP38 x1 x2 x3 x4 x5 x6 ≤ taumXP38 x1 x2 x3 x4 x5 x6 := by
  intro x1 x2 x3 x4 x5 x6 h1 h1u h2 h2u h3 h3u h4 h4u h5 h6 hd
  have hx1 : 0 ≤ x1 := by linarith
  have hx2 : 0 ≤ x2 := by linarith
  have hx3 : 0 ≤ x3 := by linarith
  have hx4 : 0 ≤ x4 := by
    have : (0:ℝ) < cstab := by norm_num [cstab]
    nlinarith
  have hx5 : 0 ≤ x5 := by rw [h5]; norm_num
  have hx6 : 0 ≤ x6 := by rw [h6]; norm_num
  have h2h0 : (0:ℝ) < 2 * h0 := by
    have : h0 = 1.26 := rfl
    rw [this]; norm_num
  -- the y-space box
  have hy1 : 2 ≤ Real.sqrt x1 := by
    nlinarith [Real.sq_sqrt hx1, Real.sqrt_nonneg x1]
  have hy1u : Real.sqrt x1 ≤ 2 * h0 := by
    nlinarith [Real.sq_sqrt hx1, Real.sqrt_nonneg x1,
      sq_nonneg (Real.sqrt x1 - 2 * h0)]
  have hy2 : 2 ≤ Real.sqrt x2 := by
    nlinarith [Real.sq_sqrt hx2, Real.sqrt_nonneg x2]
  have hy2u : Real.sqrt x2 ≤ 2 * h0 := by
    nlinarith [Real.sq_sqrt hx2, Real.sqrt_nonneg x2,
      sq_nonneg (Real.sqrt x2 - 2 * h0)]
  have hy3 : 2 ≤ Real.sqrt x3 := by
    nlinarith [Real.sq_sqrt hx3, Real.sqrt_nonneg x3]
  have hy3u : Real.sqrt x3 ≤ 2 * h0 := by
    nlinarith [Real.sq_sqrt hx3, Real.sqrt_nonneg x3,
      sq_nonneg (Real.sqrt x3 - 2 * h0)]
  have hcpos : (0:ℝ) < cstab := by norm_num [cstab]
  have hy4 : cstab ≤ Real.sqrt x4 := by
    nlinarith [Real.sq_sqrt hx4, Real.sqrt_nonneg x4]
  have hy4u : Real.sqrt x4 ≤ 3.915 := by
    nlinarith [Real.sq_sqrt hx4, Real.sqrt_nonneg x4,
      sq_nonneg (Real.sqrt x4 - 3.915)]
  have hy5 : Real.sqrt x5 = 2 := by rw [h5]; norm_num
  have hy6 : Real.sqrt x6 = 2 := by rw [h6]; norm_num
  have hnn1 : 0 ≤ Real.sqrt x1 := Real.sqrt_nonneg x1
  have hnn2 : 0 ≤ Real.sqrt x2 := Real.sqrt_nonneg x2
  have hnn3 : 0 ≤ Real.sqrt x3 := Real.sqrt_nonneg x3
  have hnn4 : 0 ≤ Real.sqrt x4 := Real.sqrt_nonneg x4
  have hdY : 0 ≤ deltaY (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
      (Real.sqrt x4) (Real.sqrt x5) (Real.sqrt x6) := by
    unfold deltaY
    rwa [Real.mul_self_sqrt hx1, Real.mul_self_sqrt hx2, Real.mul_self_sqrt hx3,
      Real.mul_self_sqrt hx4, Real.mul_self_sqrt hx5, Real.mul_self_sqrt hx6]
  have hOW := OWZLKVY4_p19 h (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
    (Real.sqrt x4) (Real.sqrt x5) (Real.sqrt x6)
    hy1 hy1u hy2 hy2u hy3 hy3u hy4 hy4u hy5 hy6 hdY
  -- the two `y_of_x` bridges at `x = y²`
  have htaud : taudXP38 x1 x2 x3 x4 x5 x6 =
      taudP19 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3) (Real.sqrt x4)
        (Real.sqrt x5) (Real.sqrt x6) := by
    have e := taud_x_taud_c (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
      (Real.sqrt x4) (Real.sqrt x5) (Real.sqrt x6) hnn1 hnn2 hnn3
    rw [yOfX] at e
    rw [Real.mul_self_sqrt hx1, Real.mul_self_sqrt hx2, Real.mul_self_sqrt hx3,
      Real.mul_self_sqrt hx4, Real.mul_self_sqrt hx5, Real.mul_self_sqrt hx6] at e
    exact e
  have htaum : taumXP38 x1 x2 x3 x4 x5 x6 =
      taum (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3) (Real.sqrt x4)
        (Real.sqrt x5) (Real.sqrt x6) := by
    have e := taum_taum_x (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
      (Real.sqrt x4) (Real.sqrt x5) (Real.sqrt x6) hnn1 hnn2 hnn3 hnn4
      (Real.sqrt_nonneg x5) (Real.sqrt_nonneg x6)
    rw [yOfX] at e
    rw [Real.mul_self_sqrt hx1, Real.mul_self_sqrt hx2, Real.mul_self_sqrt hx3,
      Real.mul_self_sqrt hx4, Real.mul_self_sqrt hx5, Real.mul_self_sqrt hx6] at e
    rw [← e]
  rw [htaud, htaum]
  exact hOW

/-- HOL `LTCTBAN` = `Collect_geom.LEMMA50` (`collect_geom.hl:1981`): `cayleyR`
is a quadratic in its 10th slot with coefficients `(ups_x, cayleytr·0,
cayleyR·0)`.  Pure polynomial identity (`REWRITE_TAC[...]; REAL_ARITH_TAC`
in HOL). -/
theorem cayleyR_conic_c (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℝ) :
    cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
      upsX x12 x13 x23 * x45 ^ 2 +
        cayleytr_t11 x12 x13 x14 x15 x23 x24 x25 x34 x35 0 * x45 +
        cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 0 := by
  simp only [cayleyR, upsX, cayleytr_t11]
  ring

/-- HOL `GJWYYPS` = `Collect_geom.LEMMA51` (`collect_geom.hl:2284`): the
`cayleyR` discriminant identity (`b^2 - 4ac = 16·delta·delta`). -/
theorem cayleyR_disc_c (x12 x13 x14 x15 x23 x24 x25 x34 x35 : ℝ) :
    cayleytr_t11 x12 x13 x14 x15 x23 x24 x25 x34 x35 0 ^ 2 -
        4 * upsX x12 x13 x23 * cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 0 =
      16 * deltaP x12 x13 x14 x23 x24 x34 * deltaP x12 x13 x15 x23 x25 x35 := by
  simp only [cayleyR, cayleytr_t11, upsX, deltaP]
  ring

/-- `LocalAuto1.cayleyR_t11` and `IneqClosureDefs.cayleyR` are the same body
(registry statements use the former, `quadCrossDiag2XP38` the latter). -/
theorem cayleyR_t11_eq_cayleyR (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℝ) :
    cayleyR_t11 x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
      cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 := by
  simp only [cayleyR_t11, cayleyR]

/-- HOL `abc_of_quadratic_cayleyR` (terminal.hl:3518; LA38:4557 twin with the
real `cayleytr_t11` in place of the `cayleytrP38` stub). -/
theorem abc_of_quadratic_cayleyR_c (x12 x13 x14 x15 x23 x24 x25 x34 x35 : ℝ) :
    abcOfQuadraticP38 (cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35) =
      (upsX x12 x13 x23,
        cayleytr_t11 x12 x13 x14 x15 x23 x24 x25 x34 x35 0,
        cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 0) := by
  have hfun : ∀ x45 : ℝ, cayleyRP38 x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
      upsX x12 x13 x23 * x45 ^ 2 +
        cayleytr_t11 x12 x13 x14 x15 x23 x24 x25 x34 x35 0 * x45 +
        cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 0 :=
    fun x45 => cayleyR_conic_c x12 x13 x14 x15 x23 x24 x25 x34 x35 x45
  simp only [abcOfQuadraticP38, hfun]
  ring

/-- HOL `quad_cross_diag2_x_bound` (terminal.hl:3551; LA38:4573 twin with the
real `cayleytr_t11`). -/
theorem quad_cross_diag2_x_bound_c (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : ℝ)
    (_ : 0 ≤ x1) (_ : 0 ≤ x2) (_ : 0 ≤ x3) (_ : 0 ≤ x4) (_ : 0 ≤ x5) (_ : 0 ≤ x6)
    (_ : 0 ≤ x7) (_ : 0 ≤ x8) (_ : 0 ≤ x9) (h10 : 0 ≤ x10)
    (hups : 0 < upsX x2 x3 x4)
    (hd1 : 0 ≤ deltaX x1 x2 x3 x4 x5 x6)
    (hd2 : 0 ≤ deltaX x7 x2 x3 x4 x8 x9)
    (hlin : 0 < 2 * upsX x2 x3 x4 * x10 +
      cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 0)
    (hcay : 0 < cayleyR x3 x2 x1 x7 x4 x5 x8 x6 x9 x10)
    (htr : cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 0 ≤ 0) :
    quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 < Real.sqrt x10 := by
  have hups' : upsX x3 x2 x4 = upsX x2 x3 x4 := by simp only [upsX]; ring
  have hq : quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
      Real.sqrt (quadraticRootPlus
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).1
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.1
        (abcOfQuadraticP38 (cayleyRP38 x3 x2 x1 x7 x4 x5 x8 x6 x9)).2.2) := rfl
  rw [hq, abc_of_quadratic_cayleyR_c]
  refine quadratic_square_root_upper_bound (upsX x3 x2 x4)
    (cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 0)
    (cayleyR x3 x2 x1 x7 x4 x5 x8 x6 x9 0) x10 ?_ ?_ ?_ ?_ htr h10
  · rw [hups']; exact hups
  · rw [hups']; exact hlin
  · have hcon := cayleyR_conic_c x3 x2 x1 x7 x4 x5 x8 x6 x9 x10
    linarith
  · have hdisc := cayleyR_disc_c x3 x2 x1 x7 x4 x5 x8 x6 x9
    have e1 : deltaP x3 x2 x1 x4 x5 x6 = deltaX x1 x2 x3 x4 x5 x6 := by
      rw [delta_delta_x]
      rw [show deltaX x3 x2 x1 x6 x5 x4 = deltaX x1 x2 x3 x4 x5 x6 by
        simp only [deltaX]; ring]
    have e2 : deltaP x3 x2 x7 x4 x8 x9 = deltaX x7 x2 x3 x4 x8 x9 := by
      rw [delta_delta_x]
      rw [show deltaX x3 x2 x7 x9 x8 x4 = deltaX x7 x2 x3 x4 x8 x9 by
        simp only [deltaX]; ring]
    rw [hdisc, e1, e2]
    have := mul_nonneg hd1 hd2
    linarith

/-- HOL `quad_4680581274_delta_issue` (terminal.hl:3639; LA38:4655 twin with
the real-bodied `unit6'`; the six registry ids and `LEMMA_…_delta_issue_ups` +
`quad_cross_diag2_x_bound_c` are the whole proof). -/
theorem quad_4680581274_delta_issue' (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ,
      0 ≤ deltaX x1 x2 x3 x4 x5 x6 →
      0 ≤ deltaX x7 x2 x3 x4 x8 x9 →
      ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26),
        (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26),
        (3.01 * 3.01, x4, 3.166 * 3.166), (4.0, x5, 4.0), (4.0, x6, 4.0),
        (4.0, x7, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x8, 4.0),
        (3.01 * 3.01, x9, 3.01 * 3.01)]
        (unit6' x1 x2 x3 x4 x5 x6 * 10 + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 +
            unit6' x1 x2 x3 x4 x5 x6 * -3.01 < 0) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 hd1 hd2
  have hnum1 : (2.0 * 1.26 * 2.0 * 1.26 : ℝ) = 6.3504 := by norm_num
  have hnum2 : (3.01 * 3.01 : ℝ) = 9.0601 := by norm_num
  have hnum3 : (3.166 * 3.166 : ℝ) = 10.023556 := by norm_num
  rw [hnum1, hnum2, hnum3]
  simp only [ineqP38]
  rcases lt_or_ge x1 (4.0 : ℝ) with hb1 | hb1
  · exact Or.inl hb1
  rcases lt_or_ge (6.3504 : ℝ) x1 with hb2 | hb2
  · exact Or.inr (Or.inl hb2)
  rcases lt_or_ge x2 (4.0 : ℝ) with hb3 | hb3
  · exact Or.inr (Or.inr (Or.inl hb3))
  rcases lt_or_ge (6.3504 : ℝ) x2 with hb4 | hb4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb4)))
  rcases lt_or_ge x3 (4.0 : ℝ) with hb5 | hb5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb5))))
  rcases lt_or_ge (6.3504 : ℝ) x3 with hb6 | hb6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb6)))))
  rcases lt_or_ge x4 (9.0601 : ℝ) with hb7 | hb7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb7))))))
  rcases lt_or_ge (10.023556 : ℝ) x4 with hb8 | hb8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb8)))))))
  rcases lt_or_ge x5 (4.0 : ℝ) with hb9 | hb9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb9))))))))
  rcases lt_or_ge (4.0 : ℝ) x5 with hb10 | hb10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb10)))))))))
  rcases lt_or_ge x6 (4.0 : ℝ) with hb11 | hb11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb11))))))))))
  rcases lt_or_ge (4.0 : ℝ) x6 with hb12 | hb12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb12)))))))))))
  rcases lt_or_ge x7 (4.0 : ℝ) with hb13 | hb13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb13))))))))))))
  rcases lt_or_ge (6.3504 : ℝ) x7 with hb14 | hb14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb14)))))))))))))
  rcases lt_or_ge x8 (4.0 : ℝ) with hb15 | hb15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb15))))))))))))))
  rcases lt_or_ge (4.0 : ℝ) x8 with hb16 | hb16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb16)))))))))))))))
  rcases lt_or_ge x9 (9.0601 : ℝ) with hb17 | hb17
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb17))))))))))))))))
  rcases lt_or_ge (9.0601 : ℝ) x9 with hb18 | hb18
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb18)))))))))))))))))
  -- in-box branch
  have h1l : (4.0:ℝ) ≤ x1 := by linarith
  have h1u : x1 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h2l : (4.0:ℝ) ≤ x2 := by linarith
  have h2u : x2 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h3l : (4.0:ℝ) ≤ x3 := by linarith
  have h3u : x3 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h4l : (3.01 * 3.01:ℝ) ≤ x4 := by linarith
  have h4u : x4 ≤ 3.166 * 3.166 := by linarith
  have h5l : (4.0:ℝ) ≤ x5 := by linarith
  have h5u : x5 ≤ 4.0 := by linarith
  have h6l : (4.0:ℝ) ≤ x6 := by linarith
  have h6u : x6 ≤ 4.0 := by linarith
  have h7l : (4.0:ℝ) ≤ x7 := by linarith
  have h7u : x7 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h8l : (4.0:ℝ) ≤ x8 := by linarith
  have h8u : x8 ≤ 4.0 := by linarith
  have h9l : (3.01 * 3.01:ℝ) ≤ x9 := by linarith
  have h9u : x9 ≤ 3.01 * 3.01 := by linarith
  by_cases hA : (10:ℝ) + deltaX x1 x2 x3 x4 x5 x6 * -1 < 0
  · right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; left
    simpa [unit6'] using hA
  by_cases hB : deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0
  · right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; left
    exact hB
  -- the third disjunct: `quad_cross_diag2_x_bound` at `x10 = 3.01^2`
  have hups : 0 < upsX x2 x3 x4 := by
    have hring : upsX x2 x3 x4 = 4 * x2 * x3 - (x4 - x2 - x3) ^ 2 := by
      simp only [upsX]; ring
    rw [hring]
    have hge : (4 : ℝ) * x2 * x3 ≥ 64 := by nlinarith
    have htsq : (x4 - x2 - x3) ^ 2 ≤ 3.7 ^ 2 := by
      have hp : (0 : ℝ) ≤ 3.7 + (x4 - x2 - x3) := by linarith
      have hq : (0 : ℝ) ≤ 3.7 - (x4 - x2 - x3) := by linarith
      have hprod : (3.7 + (x4 - x2 - x3)) * (3.7 - (x4 - x2 - x3)) ≥ 0 :=
        mul_nonneg hp hq
      have hexp : 3.7 ^ 2 - (x4 - x2 - x3) ^ 2 =
          (3.7 + (x4 - x2 - x3)) * (3.7 - (x4 - x2 - x3)) := by ring
      linarith
    linarith
  have htr : cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 0 ≤ 0 := by
    have hreg : mainEstimate_4680581274_delta_issue_cayleytr0 :=
      h "4680581274 delta issue-cayleytr0" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_delta_issue_cayleytr0 at hreg
    rcases hreg x1 x2 x3 x4 x5 x6 x7 x8 x9 h1l h1u h2l h2u h3l h3u h4l h4u
      h5l h5u h6l h6u h7l h7u h8l h8u h9l h9u with hlt | hA' | hB'
    · linarith
    · exact absurd hA' hA
    · exact absurd hB' hB
  have hlin : 0 < 2 * upsX x2 x3 x4 * (3.01 * 3.01) +
      cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 0 := by
    have hreg : mainEstimate_4680581274_delta_issue_cayleytr :=
      h "4680581274 delta issue-cayleytr" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_delta_issue_cayleytr at hreg
    rcases hreg x1 x2 x3 x4 x5 x6 x7 x8 x9 (3.01 * 3.01) h1l h1u h2l h2u h3l h3u
      h4l h4u h5l h5u h6l h6u h7l h7u h8l h8u h9l h9u
      (le_refl (3.01 * 3.01)) (le_refl (3.01 * 3.01)) with hlt | hA' | hB'
    · linarith
    · exact absurd hA' hA
    · exact absurd hB' hB
  have hcay : 0 < cayleyR x3 x2 x1 x7 x4 x5 x8 x6 x9 (3.01 * 3.01) := by
    have hreg : mainEstimate_4680581274_delta_issue_cayleyR :=
      h "4680581274 delta issue-cayleyR" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_delta_issue_cayleyR at hreg
    rcases hreg x1 x2 x3 x4 x5 x6 x7 x8 x9 (3.01 * 3.01) h1l h1u h2l h2u h3l h3u
      h4l h4u h5l h5u h6l h6u h7l h7u h8l h8u h9l h9u
      (le_refl (3.01 * 3.01)) (le_refl (3.01 * 3.01)) with hlt | hA' | hB'
    · rwa [cayleyR_t11_eq_cayleyR] at hlt
    · exact absurd hA' hA
    · exact absurd hB' hB
  have hbnd := quad_cross_diag2_x_bound_c x1 x2 x3 x4 x5 x6 x7 x8 x9
    (3.01 * 3.01) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) hups hd1 hd2 hlin hcay htr
  have hs : Real.sqrt (3.01 * 3.01) = 3.01 := by
    rw [show (3.01 * 3.01 : ℝ) = 3.01 ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  rw [hs] at hbnd
  right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; right
  simpa [unit6'] using (by linarith : quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 - 3.01 < 0)

/-- HOL `quad_4680581274_delta_y_issue` (terminal.hl:3712; **not in LA38**):
the y-space image of `quad_4680581274_delta_issue'` under `x_i = y_i^2`
(HOL's `Optimize.X_OF_Y_TAC`), with the real `tauq`/`enclosedP38` bodies. -/
theorem quad_4680581274_delta_y_issue' (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineqP38 [(2.0, y1, 2 * h0), (2.0, y2, 2 * h0), (2.0, y3, 2 * h0),
        (3.01, y4, 3.166), (2.0, y5, 2), (2.0, y6, 2), (2.0, y7, 2 * h0),
        (2.0, y8, 2), (3.01, y9, 3.01)]
        (0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
          0 ≤ deltaY y7 y2 y3 y4 y8 y9 →
          (deltaY y1 y2 y3 y4 y5 y6 > 10 ∨
            delta4Y y1 y2 y3 y4 y5 y6 > 0 ∨
            enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 < 3.01)) := by
  intro y1 y2 y3 y4 y5 y6 y7 y8 y9
  simp only [ineqP38]
  rcases lt_or_ge y1 (2.0 : ℝ) with hb1 | hb1
  · exact Or.inl hb1
  rcases lt_or_ge (2 * h0 : ℝ) y1 with hb2 | hb2
  · exact Or.inr (Or.inl hb2)
  rcases lt_or_ge y2 (2.0 : ℝ) with hb3 | hb3
  · exact Or.inr (Or.inr (Or.inl hb3))
  rcases lt_or_ge (2 * h0 : ℝ) y2 with hb4 | hb4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb4)))
  rcases lt_or_ge y3 (2.0 : ℝ) with hb5 | hb5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb5))))
  rcases lt_or_ge (2 * h0 : ℝ) y3 with hb6 | hb6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb6)))))
  rcases lt_or_ge y4 (3.01 : ℝ) with hb7 | hb7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb7))))))
  rcases lt_or_ge (3.166 : ℝ) y4 with hb8 | hb8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb8)))))))
  rcases lt_or_ge y5 (2.0 : ℝ) with hb9 | hb9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb9))))))))
  rcases lt_or_ge (2 : ℝ) y5 with hb10 | hb10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb10)))))))))
  rcases lt_or_ge y6 (2.0 : ℝ) with hb11 | hb11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb11))))))))))
  rcases lt_or_ge (2 : ℝ) y6 with hb12 | hb12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb12)))))))))))
  rcases lt_or_ge y7 (2.0 : ℝ) with hb13 | hb13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb13))))))))))))
  rcases lt_or_ge (2 * h0 : ℝ) y7 with hb14 | hb14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb14)))))))))))))
  rcases lt_or_ge y8 (2.0 : ℝ) with hb15 | hb15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb15))))))))))))))
  rcases lt_or_ge (2 : ℝ) y8 with hb16 | hb16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb16)))))))))))))))
  rcases lt_or_ge y9 (3.01 : ℝ) with hb17 | hb17
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb17))))))))))))))))
  rcases lt_or_ge (3.01 : ℝ) y9 with hb18 | hb18
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb18)))))))))))))))))
  right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right
  intro hd1 hd2
  have hres := quad_4680581274_delta_issue' h (y1 * y1) (y2 * y2) (y3 * y3)
    (y4 * y4) (y5 * y5) (y6 * y6) (y7 * y7) (y8 * y8) (y9 * y9)
    (by simpa only [deltaY] using hd1) (by simpa only [deltaY] using hd2)
  simp only [ineqP38] at hres
  have h252 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  have hx1l : (4.0:ℝ) ≤ y1 * y1 := by nlinarith
  have hx1u : y1 * y1 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx2l : (4.0:ℝ) ≤ y2 * y2 := by nlinarith
  have hx2u : y2 * y2 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx3l : (4.0:ℝ) ≤ y3 * y3 := by nlinarith
  have hx3u : y3 * y3 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx4l : (3.01 * 3.01:ℝ) ≤ y4 * y4 := by nlinarith
  have hx4u : y4 * y4 ≤ 3.166 * 3.166 := by nlinarith
  have hx5l : (4.0:ℝ) ≤ y5 * y5 := by nlinarith
  have hx5u : y5 * y5 ≤ 4.0 := by nlinarith
  have hx6l : (4.0:ℝ) ≤ y6 * y6 := by nlinarith
  have hx6u : y6 * y6 ≤ 4.0 := by nlinarith
  have hx7l : (4.0:ℝ) ≤ y7 * y7 := by nlinarith
  have hx7u : y7 * y7 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx8l : (4.0:ℝ) ≤ y8 * y8 := by nlinarith
  have hx8u : y8 * y8 ≤ 4.0 := by nlinarith
  have hx9l : (3.01 * 3.01:ℝ) ≤ y9 * y9 := by nlinarith
  have hx9u : y9 * y9 ≤ 3.01 * 3.01 := by nlinarith
  rcases hres with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | hD
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  have e1 : deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) =
      deltaY y1 y2 y3 y4 y5 y6 := rfl
  have e2 : deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) =
      delta4Y y1 y2 y3 y4 y5 y6 := rfl
  have e3 : quadCrossDiag2XP38 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6) (y7 * y7) (y8 * y8) (y9 * y9) =
      enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 := rfl
  rcases hD with hD | hD | hD
  · left; rw [e1] at hD; simp only [unit6'] at hD; linarith
  · right; left; rw [e2] at hD; linarith
  · right; right; rw [e3] at hD; simp only [unit6'] at hD; linarith

/-- HOL `quad_4680581274_a` (terminal.hl:3791; LA38:4672 twin with the real
`unit6'`): the `0.541`/`-0.028` registry pair + `taud_x_taum_x'` +
`taum_x_sym` arithmetic. -/
theorem quad_4680581274_a' (h : main_nonlinear_terminal_v11) :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℝ,
      ineqP38 [(4.0, x1, 2.0 * 1.26 * 2.0 * 1.26),
        (4.0, x2, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x3, 2.0 * 1.26 * 2.0 * 1.26),
        (3.01 * 3.01, x4, 3.166 * 3.166), (4.0, x5, 4.0), (4.0, x6, 4.0),
        (4.0, x7, 2.0 * 1.26 * 2.0 * 1.26), (4.0, x8, 4.0),
        (3.01 * 3.01, x9, 3.01 * 3.01)]
        (unit6' x1 x2 x3 x4 x5 x6 * 0.513 +
            taumXP38 x1 x2 x3 x4 x5 x6 * -1 +
            taumXP38 x7 x2 x3 x4 x8 x9 * -1 < 0 ∨
          deltaX x1 x2 x3 x4 x5 x6 + unit6' x1 x2 x3 x4 x5 x6 * -10 < 0 ∨
          deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0 ∨
          quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 +
            unit6' x1 x2 x3 x4 x5 x6 * -3.01 < 0) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9
  simp only [ineqP38]
  rcases lt_or_ge x1 (4.0 : ℝ) with hb1 | hb1
  · exact Or.inl hb1
  rcases lt_or_ge (2.0 * 1.26 * 2.0 * 1.26 : ℝ) x1 with hb2 | hb2
  · exact Or.inr (Or.inl hb2)
  rcases lt_or_ge x2 (4.0 : ℝ) with hb3 | hb3
  · exact Or.inr (Or.inr (Or.inl hb3))
  rcases lt_or_ge (2.0 * 1.26 * 2.0 * 1.26 : ℝ) x2 with hb4 | hb4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb4)))
  rcases lt_or_ge x3 (4.0 : ℝ) with hb5 | hb5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb5))))
  rcases lt_or_ge (2.0 * 1.26 * 2.0 * 1.26 : ℝ) x3 with hb6 | hb6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb6)))))
  rcases lt_or_ge x4 (3.01 * 3.01 : ℝ) with hb7 | hb7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb7))))))
  rcases lt_or_ge (3.166 * 3.166 : ℝ) x4 with hb8 | hb8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb8)))))))
  rcases lt_or_ge x5 (4.0 : ℝ) with hb9 | hb9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb9))))))))
  rcases lt_or_ge (4.0 : ℝ) x5 with hb10 | hb10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb10)))))))))
  rcases lt_or_ge x6 (4.0 : ℝ) with hb11 | hb11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb11))))))))))
  rcases lt_or_ge (4.0 : ℝ) x6 with hb12 | hb12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb12)))))))))))
  rcases lt_or_ge x7 (4.0 : ℝ) with hb13 | hb13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb13))))))))))))
  rcases lt_or_ge (2.0 * 1.26 * 2.0 * 1.26 : ℝ) x7 with hb14 | hb14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb14)))))))))))))
  rcases lt_or_ge x8 (4.0 : ℝ) with hb15 | hb15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb15))))))))))))))
  rcases lt_or_ge (4.0 : ℝ) x8 with hb16 | hb16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb16)))))))))))))))
  rcases lt_or_ge x9 (3.01 * 3.01 : ℝ) with hb17 | hb17
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb17))))))))))))))))
  rcases lt_or_ge (3.01 * 3.01 : ℝ) x9 with hb18 | hb18
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb18)))))))))))))))))
  have h1l : (4.0:ℝ) ≤ x1 := by linarith
  have h1u : x1 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h2l : (4.0:ℝ) ≤ x2 := by linarith
  have h2u : x2 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h3l : (4.0:ℝ) ≤ x3 := by linarith
  have h3u : x3 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h4l : (3.01 * 3.01:ℝ) ≤ x4 := by linarith
  have h4u : x4 ≤ 3.166 * 3.166 := by linarith
  have h5l : (4.0:ℝ) ≤ x5 := by linarith
  have h5u : x5 ≤ 4.0 := by linarith
  have h6l : (4.0:ℝ) ≤ x6 := by linarith
  have h6u : x6 ≤ 4.0 := by linarith
  have h7l : (4.0:ℝ) ≤ x7 := by linarith
  have h7u : x7 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by linarith
  have h8l : (4.0:ℝ) ≤ x8 := by linarith
  have h8u : x8 ≤ 4.0 := by linarith
  have h9l : (3.01 * 3.01:ℝ) ≤ x9 := by linarith
  have h9u : x9 ≤ 3.01 * 3.01 := by linarith
  have h2h0sq : ((2:ℝ) * h0) ^ 2 = 2.0 * 1.26 * 2.0 * 1.26 := by norm_num [h0]
  have h301sq : ((3.01:ℝ)) ^ 2 = 3.01 * 3.01 := by norm_num
  have h3166sq : ((3.166:ℝ)) ^ 2 = 3.166 * 3.166 := by norm_num

  by_cases hb : deltaX x1 x2 x3 x4 x5 x6 + unit6' x1 x2 x3 x4 x5 x6 * -10 < 0
  · right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; left
    exact hb
  by_cases hc : deltaX4 x1 x2 x3 x4 x5 x6 * -1 < 0
  · right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; right; left
    exact hc
  by_cases hd : quadCrossDiag2XP38 x1 x2 x3 x4 x5 x6 x7 x8 x9 +
      unit6' x1 x2 x3 x4 x5 x6 * -3.01 < 0
  · right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; right; right
    exact hd
  -- the first disjunct (`a ∨ b ∨ c ∨ d` under `¬b`, `¬c`, `¬d`)
  have hb' : ¬(deltaX x1 x2 x3 x4 x5 x6 < 10) := by
    intro hlt
    exact hb (by simpa [unit6'] using (by linarith : deltaX x1 x2 x3 x4 x5 x6 + (-10:ℝ) < 0))
  have h1x : (-0.028:ℝ) < taumXP38 x1 x2 x3 x4 x5 x6 := by
    have hreg : mainEstimate_4680581274_1x :=
      h "4680581274 1x" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_1x at hreg
    rcases hreg x1 x2 x3 x4 x5 x6 h1l (by rw [h2h0sq]; exact h1u)
      h2l (by rw [h2h0sq]; exact h2u) h3l (by rw [h2h0sq]; exact h3u)
      (by rw [h301sq]; exact h4l) (by rw [h3166sq]; exact h4u)
      (by linarith : (4:ℝ) ≤ x5) (by linarith : x5 ≤ (4:ℝ))
      (by linarith : (4:ℝ) ≤ x6) (by linarith : x6 ≤ (4:ℝ)) with hlt | hdl
    · have hle := taud_x_taum_x' h x1 x2 x3 x4 x5 x6
        (by linarith : (4:ℝ) ≤ x1) (by rw [h2h0sq]; exact h1u)
        (by linarith : (4:ℝ) ≤ x2) (by rw [h2h0sq]; exact h2u)
        (by linarith : (4:ℝ) ≤ x3) (by rw [h2h0sq]; exact h3u)
        (by rw [cstab_eq_p22, h301sq]; exact h4l)
        (by nlinarith : x4 ≤ 3.915 ^ 2)
        (by linarith : x5 = 4) (by linarith : x6 = 4)
        (by linarith : 0 ≤ deltaX x1 x2 x3 x4 x5 x6)
      exact lt_of_lt_of_le hlt hle
    · exact absurd hdl hb'
  have h2x : (0.541:ℝ) < taumXP38 x7 x3 x2 x4 x9 x8 := by
    have hreg : mainEstimate_4680581274_2x :=
      h "4680581274 2x" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_2x at hreg
    exact hreg x7 x3 x2 x4 x9 x8 h7l (by rw [h2h0sq]; exact h7u)
      h3l (by rw [h2h0sq]; exact h3u) h2l (by rw [h2h0sq]; exact h2u)
      (by rw [h301sq]; exact h4l) (by rw [h3166sq]; exact h4u)
      (by rw [h301sq]; exact h9l) (by rw [h301sq]; exact h9u)
      (by linarith : (4:ℝ) ≤ x8) (by linarith : x8 ≤ (4:ℝ))
  have hsym : taumXP38 x7 x3 x2 x4 x9 x8 = taumXP38 x7 x2 x3 x4 x8 x9 :=
    taum_x_sym x7 x2 x3 x4 x8 x9
  right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; left
  rw [← hsym]
  simpa [unit6'] using (by linarith :
    (1:ℝ) * 0.513 + taumXP38 x1 x2 x3 x4 x5 x6 * -1 +
      taumXP38 x7 x3 x2 x4 x9 x8 * -1 < 0)

/-- HOL `quad_4680581274_y` (terminal.hl:3854; LA38:4690 twin): the y-space
image of `quad_4680581274_a'` under `x_i = y_i^2`, with the real `tauq` body
(`IneqClosureDefs.tauq`). -/
theorem quad_4680581274_y' (h : main_nonlinear_terminal_v11) :
    ∀ y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineqP38 [(2.0, y1, 2 * h0), (2.0, y2, 2 * h0), (2.0, y3, 2 * h0),
        (3.01, y4, 3.166), (2.0, y5, 2), (2.0, y6, 2), (2.0, y7, 2 * h0),
        (2.0, y8, 2), (3.01, y9, 3.01)]
        (tauq y1 y2 y3 y4 y5 y6 y7 y8 y9 > 0.513 ∨
          deltaY y1 y2 y3 y4 y5 y6 < 10 ∨
          delta4Y y1 y2 y3 y4 y5 y6 > 0 ∨
          enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 < 3.01) := by
  intro y1 y2 y3 y4 y5 y6 y7 y8 y9
  simp only [ineqP38]
  rcases lt_or_ge y1 (2.0 : ℝ) with hb1 | hb1
  · exact Or.inl hb1
  rcases lt_or_ge (2 * h0 : ℝ) y1 with hb2 | hb2
  · exact Or.inr (Or.inl hb2)
  rcases lt_or_ge y2 (2.0 : ℝ) with hb3 | hb3
  · exact Or.inr (Or.inr (Or.inl hb3))
  rcases lt_or_ge (2 * h0 : ℝ) y2 with hb4 | hb4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb4)))
  rcases lt_or_ge y3 (2.0 : ℝ) with hb5 | hb5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb5))))
  rcases lt_or_ge (2 * h0 : ℝ) y3 with hb6 | hb6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb6)))))
  rcases lt_or_ge y4 (3.01 : ℝ) with hb7 | hb7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb7))))))
  rcases lt_or_ge (3.166 : ℝ) y4 with hb8 | hb8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb8)))))))
  rcases lt_or_ge y5 (2.0 : ℝ) with hb9 | hb9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb9))))))))
  rcases lt_or_ge (2 : ℝ) y5 with hb10 | hb10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb10)))))))))
  rcases lt_or_ge y6 (2.0 : ℝ) with hb11 | hb11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb11))))))))))
  rcases lt_or_ge (2 : ℝ) y6 with hb12 | hb12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb12)))))))))))
  rcases lt_or_ge y7 (2.0 : ℝ) with hb13 | hb13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb13))))))))))))
  rcases lt_or_ge (2 * h0 : ℝ) y7 with hb14 | hb14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb14)))))))))))))
  rcases lt_or_ge y8 (2.0 : ℝ) with hb15 | hb15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb15))))))))))))))
  rcases lt_or_ge (2 : ℝ) y8 with hb16 | hb16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb16)))))))))))))))
  rcases lt_or_ge y9 (3.01 : ℝ) with hb17 | hb17
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb17))))))))))))))))
  rcases lt_or_ge (3.01 : ℝ) y9 with hb18 | hb18
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb18)))))))))))))))))
  have hres := quad_4680581274_a' h (y1 * y1) (y2 * y2) (y3 * y3)
    (y4 * y4) (y5 * y5) (y6 * y6) (y7 * y7) (y8 * y8) (y9 * y9)
  simp only [ineqP38] at hres
  have h252 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  have hx1l : (4.0:ℝ) ≤ y1 * y1 := by nlinarith
  have hx1u : y1 * y1 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx2l : (4.0:ℝ) ≤ y2 * y2 := by nlinarith
  have hx2u : y2 * y2 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx3l : (4.0:ℝ) ≤ y3 * y3 := by nlinarith
  have hx3u : y3 * y3 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx4l : (3.01 * 3.01:ℝ) ≤ y4 * y4 := by nlinarith
  have hx4u : y4 * y4 ≤ 3.166 * 3.166 := by nlinarith
  have hx5l : (4.0:ℝ) ≤ y5 * y5 := by nlinarith
  have hx5u : y5 * y5 ≤ 4.0 := by nlinarith
  have hx6l : (4.0:ℝ) ≤ y6 * y6 := by nlinarith
  have hx6u : y6 * y6 ≤ 4.0 := by nlinarith
  have hx7l : (4.0:ℝ) ≤ y7 * y7 := by nlinarith
  have hx7u : y7 * y7 ≤ 2.0 * 1.26 * 2.0 * 1.26 := by nlinarith [h252]
  have hx8l : (4.0:ℝ) ≤ y8 * y8 := by nlinarith
  have hx8u : y8 * y8 ≤ 4.0 := by nlinarith
  have hx9l : (3.01 * 3.01:ℝ) ≤ y9 * y9 := by nlinarith
  have hx9u : y9 * y9 ≤ 3.01 * 3.01 := by nlinarith
  right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right
  rcases hres with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | hD
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  -- transport `a` to `tauq`
  have hn1 : 0 ≤ y1 := by linarith
  have hn2 : 0 ≤ y2 := by linarith
  have hn3 : 0 ≤ y3 := by linarith
  have hn4 : 0 ≤ y4 := by linarith
  have hn5 : 0 ≤ y5 := by linarith
  have hn6 : 0 ≤ y6 := by linarith
  have hn7 : 0 ≤ y7 := by linarith
  have hn8 : 0 ≤ y8 := by linarith
  have hn9 : 0 ≤ y9 := by linarith
  have e1 : taumXP38 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) =
      taum y1 y2 y3 y4 y5 y6 := by
    have h := taum_taum_x y1 y2 y3 y4 y5 y6 hn1 hn2 hn3 hn4 hn5 hn6
    rw [yOfX] at h
    rw [← h]
  have e2 : taumXP38 (y7 * y7) (y2 * y2) (y3 * y3) (y4 * y4) (y8 * y8) (y9 * y9) =
      taum y7 y2 y3 y4 y8 y9 := by
    have h := taum_taum_x y7 y2 y3 y4 y8 y9 hn7 hn2 hn3 hn4 hn8 hn9
    rw [yOfX] at h
    rw [← h]
  rcases hD with hD | hD | hD | hD
  · -- `a`: the `tauq` lower bound
    left
    rw [e1, e2] at hD
    simp only [unit6'] at hD
    unfold tauq
    linarith
  · -- `b`: `deltaY < 10`
    right; left
    have eb : deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) =
        deltaY y1 y2 y3 y4 y5 y6 := rfl
    rw [eb] at hD
    simp only [unit6'] at hD
    linarith
  · -- `c`: `delta4Y > 0`
    right; right; left
    have ec : deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) =
        delta4Y y1 y2 y3 y4 y5 y6 := rfl
    rw [ec] at hD
    linarith
  · -- `d`: `enclosed < 3.01`
    right; right; right
    have ed : quadCrossDiag2XP38 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
        (y6 * y6) (y7 * y7) (y8 * y8) (y9 * y9) =
        enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 := rfl
    rw [ed] at hD
    simp only [unit6'] at hD
    linarith

/-- HOL `quad_4680581274_derived` (terminal.hl:3886; LA38:4739 twin with the
real `tauq` body): the `delta top issue` + `4559601669` + `delta_y_issue` +
`_y` chain, with the `x < y → x ≤ y` final step folded into `lt_of_lt_of_le`. -/
theorem quad_4680581274_derived' (h : main_nonlinear_terminal_v11) :
    ∀ y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ,
      ineqP38 [(3.01, y0, 4), (2.0, y1, 2 * h0), (2.0, y2, 2 * h0),
        (2.0, y3, 2 * h0), (3.01, y4, 4), (2.0, y5, 2), (2.0, y6, 2),
        (2.0, y7, 2 * h0), (2.0, y8, 2), (3.01, y9, 3.01)]
        (enclosedP38 y1 y5 y6 y4 y2 y3 y7 y8 y9 = y0 ∧
          y4 ≤ y0 ∧
          0 ≤ deltaY y0 y9 y8 y4 y5 y6 ∧
          0 ≤ deltaY y1 y2 y3 y4 y5 y6 ∧
          0 ≤ deltaY y7 y2 y3 y4 y8 y9 →
          0.513 < tauq y1 y2 y3 y4 y5 y6 y7 y8 y9) := by
  intro y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
  simp only [ineqP38]
  rcases lt_or_ge y0 (3.01 : ℝ) with hb1 | hb1
  · exact Or.inl hb1
  rcases lt_or_ge (4 : ℝ) y0 with hb2 | hb2
  · exact Or.inr (Or.inl hb2)
  rcases lt_or_ge y1 (2.0 : ℝ) with hb3 | hb3
  · exact Or.inr (Or.inr (Or.inl hb3))
  rcases lt_or_ge (2 * h0 : ℝ) y1 with hb4 | hb4
  · exact Or.inr (Or.inr (Or.inr (Or.inl hb4)))
  rcases lt_or_ge y2 (2.0 : ℝ) with hb5 | hb5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb5))))
  rcases lt_or_ge (2 * h0 : ℝ) y2 with hb6 | hb6
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb6)))))
  rcases lt_or_ge y3 (2.0 : ℝ) with hb7 | hb7
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb7))))))
  rcases lt_or_ge (2 * h0 : ℝ) y3 with hb8 | hb8
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb8)))))))
  rcases lt_or_ge y4 (3.01 : ℝ) with hb9 | hb9
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb9))))))))
  rcases lt_or_ge (4 : ℝ) y4 with hb10 | hb10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb10)))))))))
  rcases lt_or_ge y5 (2.0 : ℝ) with hb11 | hb11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb11))))))))))
  rcases lt_or_ge (2 : ℝ) y5 with hb12 | hb12
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb12)))))))))))
  rcases lt_or_ge y6 (2.0 : ℝ) with hb13 | hb13
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb13))))))))))))
  rcases lt_or_ge (2 : ℝ) y6 with hb14 | hb14
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb14)))))))))))))
  rcases lt_or_ge y7 (2.0 : ℝ) with hb15 | hb15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb15))))))))))))))
  rcases lt_or_ge (2 * h0 : ℝ) y7 with hb16 | hb16
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb16)))))))))))))))
  rcases lt_or_ge y8 (2.0 : ℝ) with hb17 | hb17
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb17))))))))))))))))
  rcases lt_or_ge (2 : ℝ) y8 with hb18 | hb18
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb18)))))))))))))))))
  rcases lt_or_ge y9 (3.01 : ℝ) with hb19 | hb19
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb19))))))))))))))))))
  rcases lt_or_ge (3.01 : ℝ) y9 with hb20 | hb20
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb20)))))))))))))))))))
  right; right; right; right; right; right; right; right; right; right; right; right;
    right; right; right; right; right; right; right; right
  rintro ⟨hEnc, hy4le, hd0, hd1, hd2⟩
  have h252 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  -- `y4 ≤ 3.166` by contradiction with the `delta top issue` registry
  have hy43 : y4 ≤ 3.166 := by
    by_contra hcon
    push_neg at hcon
    have hreg : mainEstimate_4680581274_delta_top_issue :=
      h "4680581274 delta top issue" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4680581274_delta_top_issue at hreg
    have hneg := hreg y0 y9 y8 y4 y5 y6
      (by linarith : (3.166:ℝ) ≤ y0) (by linarith : y0 ≤ (4:ℝ))
      (by linarith : (3.01:ℝ) ≤ y9) (by linarith : y9 ≤ (3.01:ℝ))
      (by linarith : (2:ℝ) ≤ y8) (by linarith : y8 ≤ (2:ℝ))
      (by linarith : (3.166:ℝ) ≤ y4) (by linarith : y4 ≤ (4:ℝ))
      (by linarith : (2:ℝ) ≤ y5) (by linarith : y5 ≤ (2:ℝ))
      (by linarith : (2:ℝ) ≤ y6) (by linarith : y6 ≤ (2:ℝ))
    linarith
  -- the `4559601669` slot identity + registry
  have hperm : delta4Y y1 y5 y6 y4 y2 y3 = delta4Y y1 y2 y3 y4 y5 y6 := by
    unfold delta4Y yOfX deltaX4; ring
  have h455 : delta4Y y1 y2 y3 y4 y5 y6 < 0 := by
    have hreg : mainEstimate_4559601669 :=
      h "4559601669" (by simp [mainNonlinearTerminalV11Ids_t11])
    unfold mainEstimate_4559601669 at hreg
    have h' := hreg y1 y5 y6 y4 y2 y3
      (by linarith : (2:ℝ) ≤ y1) (by linarith : y1 ≤ (2.52:ℝ))
      (by linarith : (2:ℝ) ≤ y5) (by linarith : y5 ≤ (2:ℝ))
      (by linarith : (2:ℝ) ≤ y6) (by linarith : y6 ≤ (2:ℝ))
      (by linarith : (3.01:ℝ) ≤ y4) (by linarith : y4 ≤ (3.915:ℝ))
      (by linarith : (2:ℝ) ≤ y2) (by linarith : y2 ≤ (2.52:ℝ))
      (by linarith : (2:ℝ) ≤ y3) (by linarith : y3 ≤ (2.52:ℝ))
    rwa [hperm] at h'
  -- the `delta_y_issue` reduction at this box
  have hdy : 10 < deltaY y1 y2 y3 y4 y5 y6 := by
    have hres := quad_4680581274_delta_y_issue' h y1 y2 y3 y4 y5 y6 y7 y8 y9
    simp only [ineqP38] at hres
    rcases hres with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | hD
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    have hD' := hD hd1 hd2
    rcases hD' with hD' | hD' | hD'
    · exact hD'
    · linarith
    · linarith
  -- the `quad_4680581274_y` reduction at this box
  have hy := quad_4680581274_y' h y1 y2 y3 y4 y5 y6 y7 y8 y9
  simp only [ineqP38] at hy
  rcases hy with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | hD
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  rcases hD with hD | hD | hD | hD
  · exact hD
  · linarith
  · linarith
  · linarith

/-! ### `empty_4T3` assembly (HOL terminal.hl:3943-4128)

The LA22 halves (`emptykit_apos_4T3`, `emptykit_azim_4T3_pre` and the
`k = 4` injectivity/separation kit) are `private`, hence invisible here;
their bodies are copied verbatim below (`_c` suffix) and the `hnum` slot of
the reduction is discharged with `quad_4680581274_derived'` (the HOL
`vv_enclosed4` relabel, terminal.hl:4036-4127). -/

/-- HOL `empty_4T3` digression (terminal.hl:3957-3961): every off-diagonal
slot of the lower funlist is `2` or `cstab`, hence positive. (Verbatim copy
of LA22's private `emptykit_apos_4T3`.) -/
private theorem emptykit_apos_4T3_c :
    ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ i ≠ j →
      0 < funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j := by
  intro i j ⟨hi, hj, hne⟩
  interval_cases i <;> interval_cases j <;>
    first
      | exact absurd rfl hne
      | norm_num [funlistV39, psort, assocdV39, cstab_eq_p22]

/-- `k = 4` injectivity kit (verbatim copy of LA22's private `emptykit_hinj4`). -/
private theorem emptykit_hinj4_c (vv : ℕ → V3) (a : ℕ → ℕ → ℝ)
    (ha : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ i ≠ j → 0 < a i j)
    (hdij : ∀ i j : ℕ, a i j ≤ dist (vv i) (vv j)) :
    ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j := by
  intro i j ⟨hi, hj, heq⟩
  by_contra hne
  have hpos : 0 < a i j := ha i j ⟨hi, hj, hne⟩
  have hle : a i j ≤ dist (vv i) (vv j) := hdij i j
  rw [heq, dist_self] at hle
  linarith

/-- `k = 4` separation kit (verbatim copy of LA22's private `emptykit_hsep4`). -/
private theorem emptykit_hsep4_c (vv : ℕ → V3) (a : ℕ → ℕ → ℝ) (hper : Periodic vv 4)
    (hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j)
    (ha2 : ∀ i j : ℕ, i % 4 ≠ j % 4 → 2 ≤ a i j)
    (hdij : ∀ i j : ℕ, a i j ≤ dist (vv i) (vv j)) :
    ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j) := by
  intro i j hne
  have hne4 : i % 4 ≠ j % 4 := fun he =>
    hne ((periodic_vv_inj vv 4 hper (by norm_num) hinj i j).2 he)
  exact le_trans (ha2 i j hne4) (hdij i j)

/-- Box plumbing for the `quad_4680581274_derived'` ineq shell: the twenty
out-of-box disjuncts are refuted from the twenty box facts, leaving the
conclusion. -/
private theorem quad_box_out_c (P : Prop) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : ℝ)
    (h0l : 3.01 ≤ y0) (h0u : y0 ≤ 4)
    (h1l : 2 ≤ y1) (h1u : y1 ≤ 2 * h0)
    (h2l : 2 ≤ y2) (h2u : y2 ≤ 2 * h0)
    (h3l : 2 ≤ y3) (h3u : y3 ≤ 2 * h0)
    (h4l : 3.01 ≤ y4) (h4u : y4 ≤ 4)
    (h5l : 2 ≤ y5) (h5u : y5 ≤ 2)
    (h6l : 2 ≤ y6) (h6u : y6 ≤ 2)
    (h7l : 2 ≤ y7) (h7u : y7 ≤ 2 * h0)
    (h8l : 2 ≤ y8) (h8u : y8 ≤ 2)
    (h9l : 3.01 ≤ y9) (h9u : y9 ≤ 3.01)
    (h : ineqP38 [(3.01, y0, 4), (2.0, y1, 2 * h0), (2.0, y2, 2 * h0),
      (2.0, y3, 2 * h0), (3.01, y4, 4), (2.0, y5, 2), (2.0, y6, 2),
      (2.0, y7, 2 * h0), (2.0, y8, 2), (3.01, y9, 3.01)] P) : P := by
  simp only [ineqP38] at h
  rcases h with c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | c | h
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact h

/-- HOL `empty_4T3` (terminal.hl:3943): the azim-sum lower bound
(`terminal_quad_lemma`'s `h2` at `d = 0.513`).  The `hnum` slot of LA22's
`emptykit_azim_4T3_pre` is discharged here: the short-diagonal split's two
`i`-arms are relabelled onto `quad_4680581274_derived'`. -/
private theorem emptykit_azim_4T3_c (h : main_nonlinear_terminal_v11) :
    ∀ vv : ℕ → V3, Set.range vv ⊆ ballAnnulus → Periodic vv 4 →
      (∀ i j : ℕ,
        funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j
            ≤ dist (vv i) (vv j) ∧
          dist (vv i) (vv j) ≤
            funlistV39 [((0, 1), cstab), ((0, 2), 6), ((1, 3), 6)] 2 4 i j) →
      ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
        (Set.range fun i => (vv i, vv (i + 1))) →
      0.513 ≤ (rhoFun ‖vv 0‖ * azim 0 (vv 0) (vv 1) (vv 3) +
          rhoFun ‖vv 1‖ * azim 0 (vv 1) (vv 2) (vv 4) +
          rhoFun ‖vv 2‖ * azim 0 (vv 2) (vv 3) (vv 5) +
          rhoFun ‖vv 3‖ * azim 0 (vv 3) (vv 4) (vv 6) + 0) -
          (Real.pi + sol0) * (4 - 2) := by
  intro vv hsub hper hdij hcf
  have hann : ∀ i : ℕ, vv i ∈ ballAnnulus := fun i => hsub (Set.mem_range_self i)
  have hnorm : ∀ k : ℕ, (2:ℝ) ≤ ‖vv k‖ ∧ ‖vv k‖ ≤ 2 * h0 := fun k =>
    ballAnnulus_norm_bounds (hann k)
  have h40 : vv 4 = vv 0 := by rw [show (4 : ℕ) = 0 + 4 by norm_num]; exact hper 0
  have h50 : vv 5 = vv 1 := by rw [show (5 : ℕ) = 1 + 4 by norm_num]; exact hper 1
  have h62 : vv 6 = vv 2 := by rw [show (6 : ℕ) = 2 + 4 by norm_num]; exact hper 2
  -- the pinned `funlist` slots: both bounds coincide
  have e01 : dist (vv 0) (vv 1) = cstab := by
    have h1 := (hdij 0 1).1
    have h2 := (hdij 0 1).2
    norm_num [funlistV39, psort, assocdV39] at h1 h2
    exact le_antisymm h2 h1
  have e03 : dist (vv 0) (vv 3) = 2 := by
    have h1 := (hdij 0 3).1
    have h2 := (hdij 0 3).2
    norm_num [funlistV39, psort, assocdV39] at h1 h2
    exact le_antisymm h2 h1
  have e12 : dist (vv 1) (vv 2) = 2 := by
    have h1 := (hdij 1 2).1
    have h2 := (hdij 1 2).2
    norm_num [funlistV39, psort, assocdV39] at h1 h2
    exact le_antisymm h2 h1
  have e23 : dist (vv 2) (vv 3) = 2 := by
    have h1 := (hdij 2 3).1
    have h2 := (hdij 2 3).2
    norm_num [funlistV39, psort, assocdV39] at h1 h2
    exact le_antisymm h2 h1
  -- the two diagonal lower bounds
  have lo02 : cstab ≤ dist (vv 0) (vv 2) := by
    have h := (hdij 0 2).1
    norm_num [funlistV39, psort, assocdV39] at h
    exact h
  have lo13 : cstab ≤ dist (vv 1) (vv 3) := by
    have h := (hdij 1 3).1
    norm_num [funlistV39, psort, assocdV39] at h
    exact h
  have hinj : ∀ i j : ℕ, i < 4 ∧ j < 4 ∧ vv i = vv j → i = j :=
    emptykit_hinj4_c vv _ emptykit_apos_4T3_c (fun i j => (hdij i j).1)
  have hsep : ∀ i j : ℕ, ¬(vv i = vv j) → 2 ≤ dist (vv i) (vv j) := by
    refine emptykit_hsep4_c vv _ hper hinj ?_ (fun i j => (hdij i j).1)
    intro i j hne4
    have hred : funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4 i j =
        funlistV39 [((0, 1), cstab), ((0, 2), cstab), ((1, 3), cstab)] 2 4 (i % 4) (j % 4) := by
      simp only [funlistV39, psort, Nat.mod_mod]
    rw [hred]
    have hz1 : i % 4 < 4 := Nat.mod_lt i (by norm_num)
    have hz2 : j % 4 < 4 := Nat.mod_lt j (by norm_num)
    interval_cases i % 4 <;> interval_cases j % 4 <;>
      first
        | exact absurd rfl hne4
        | norm_num [funlistV39, psort, assocdV39, cstab_eq_p22]
  -- four sides pinned, well under `4`
  have hct : cstab < 4 := by rw [cstab_eq_p22]; norm_num
  have hd01 : dist (vv 0) (vv 1) < 4 := by rw [e01]; exact hct
  have hd03 : dist (vv 0) (vv 3) < 4 := by rw [e03]; norm_num
  have hd12 : dist (vv 1) (vv 2) < 4 := by rw [e12]; norm_num
  have hd23 : dist (vv 2) (vv 3) < 4 := by rw [e23]; norm_num
  -- the two diagonals: `delta_4680581274` plus 4-point delta positivity
  -- (HOL `PROOF_BY_CONTR_TAC` + `DELTA_Y_POS_4POINTS`, terminal.hl:4001-4029)
  have hd02 : dist (vv 0) (vv 2) < 4 := by
    by_contra hcon
    push Not at hcon
    have hδ := delta_4680581274 (dist (vv 1) (vv 3)) (dist (vv 0) (vv 2)) lo13 hcon
    have hpos := DELTA_Y_POS_4POINTS (vv 3) (vv 1) (vv 0) (vv 2)
    rw [show dist (vv 3) (vv 1) = dist (vv 1) (vv 3) from dist_comm _ _,
      show dist (vv 3) (vv 0) = dist (vv 0) (vv 3) from dist_comm _ _,
      show dist (vv 3) (vv 2) = dist (vv 2) (vv 3) from dist_comm _ _,
      show dist (vv 1) (vv 0) = dist (vv 0) (vv 1) from dist_comm _ _] at hpos
    rw [e03, e23, e12, e01] at hpos
    linarith
  have hd13 : dist (vv 1) (vv 3) < 4 := by
    by_contra hcon
    push Not at hcon
    have hδ := delta_4680581274 (dist (vv 0) (vv 2)) (dist (vv 1) (vv 3)) lo02 hcon
    have hpos := DELTA_Y_POS_4POINTS (vv 2) (vv 0) (vv 1) (vv 3)
    rw [show dist (vv 2) (vv 0) = dist (vv 0) (vv 2) from dist_comm _ _,
      show dist (vv 2) (vv 1) = dist (vv 1) (vv 2) from dist_comm _ _] at hpos
    rw [e12, e23, e03, e01] at hpos
    linarith
  -- short-diagonal split and the tau3 goal
  have hsplit := vv_quad_split_short vv hper hsub hd01 hd03 hd02 hd12 hd13 hd23 hsep hcf hinj
  rcases hsplit with ⟨i, hi2, hdiag, hspl⟩
  rw [h40, h50, h62]
  have h42 : (4 : ℝ) - 2 = 2 := by norm_num
  rw [h42, add_zero, hspl]
  have hd21 : dist (vv 2) (vv (2 + 2)) < 4 := by
    rw [show (2 + 2 : ℕ) = 0 + 4 by norm_num, hper 0, dist_comm (vv 2) (vv 0)]
    exact hd02
  have hd14 : dist (vv 1) (vv (1 + 3)) < 4 := by
    rw [show (1 + 3 : ℕ) = 0 + 4 by norm_num, hper 0, dist_comm]
    exact hd01
  have hd25 : dist (vv 2) (vv (2 + 3)) < 4 := by
    rw [show (2 + 3 : ℕ) = 1 + 4 by norm_num, hper 1, dist_comm]
    exact hd12
  interval_cases i
  · -- i = 0: relabel `(v1,v2,v3,v4) = (vv 3, vv 0, vv 2, vv 1)`
    have hEnc : enclosedP38 ‖vv 3‖ (dist (vv 2) (vv 3)) (dist (vv 3) (vv 0))
        (dist (vv 2) (vv 0)) ‖vv 0‖ ‖vv 2‖ ‖vv 1‖ (dist (vv 2) (vv 1))
        (dist (vv 0) (vv 1)) = dist (vv 3) (vv 1) := by
      have hv := vv_enclosed4 vv 2 hper hd23 hd25 hsep hsub hd21 hcf hinj
      simpa only [(by norm_num : (2 + 1 : ℕ) = 3), (by norm_num : (4 : ℕ) = 0 + 4),
        hper 0, (by norm_num : (5 : ℕ) = 1 + 4), hper 1] using hv.symm
    have hd0 : 0 ≤ deltaY (dist (vv 3) (vv 1)) (dist (vv 0) (vv 1))
        (dist (vv 2) (vv 1)) (dist (vv 2) (vv 0)) (dist (vv 2) (vv 3))
        (dist (vv 3) (vv 0)) := by
      have hpos := DELTA_Y_POS_4POINTS (vv 1) (vv 3) (vv 0) (vv 2)
      rw [show dist (vv 1) (vv 3) = dist (vv 3) (vv 1) from dist_comm _ _,
        show dist (vv 1) (vv 0) = dist (vv 0) (vv 1) from dist_comm _ _,
        show dist (vv 1) (vv 2) = dist (vv 2) (vv 1) from dist_comm _ _,
        show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 3) (vv 2) = dist (vv 2) (vv 3) from dist_comm _ _] at hpos
      exact hpos
    have hd1 : 0 ≤ deltaY ‖vv 3‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 2) (vv 0))
        (dist (vv 2) (vv 3)) (dist (vv 3) (vv 0)) := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 3) (vv 0) (vv 2)
      rw [dist_zero_left, dist_zero_left, dist_zero_left,
        show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 3) (vv 2) = dist (vv 2) (vv 3) from dist_comm _ _] at hpos
      exact hpos
    have hd2 : 0 ≤ deltaY ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 2) (vv 0))
        (dist (vv 2) (vv 1)) (dist (vv 0) (vv 1)) := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 1) (vv 0) (vv 2)
      rw [dist_zero_left, dist_zero_left, dist_zero_left,
        show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 1) (vv 2) = dist (vv 2) (vv 1) from dist_comm _ _,
        show dist (vv 1) (vv 0) = dist (vv 0) (vv 1) from dist_comm _ _] at hpos
      exact hpos
    have hy4le : dist (vv 2) (vv 0) ≤ dist (vv 3) (vv 1) := by
      simpa only [(by norm_num : (0 + 2 : ℕ) = 2), (by norm_num : (0 + 1 : ℕ) = 1),
        (by norm_num : (0 + 3 : ℕ) = 3), dist_comm (vv 0) (vv 2),
        dist_comm (vv 1) (vv 3)] using hdiag
    have hder := quad_box_out_c _ (dist (vv 3) (vv 1)) ‖vv 3‖ ‖vv 0‖ ‖vv 2‖
      (dist (vv 2) (vv 0)) (dist (vv 2) (vv 3)) (dist (vv 3) (vv 0)) ‖vv 1‖
      (dist (vv 2) (vv 1)) (dist (vv 0) (vv 1))
      (by simpa only [dist_comm (vv 1) (vv 3), cstab_eq_p22] using lo13)
      (by rw [dist_comm (vv 3) (vv 1)]; exact le_of_lt hd13)
      (hnorm 3).1 (hnorm 3).2 (hnorm 0).1 (hnorm 0).2
      (hnorm 2).1 (hnorm 2).2
      (by simpa only [dist_comm (vv 0) (vv 2), cstab_eq_p22] using lo02)
      (by rw [dist_comm (vv 2) (vv 0)]; exact le_of_lt hd02)
      (by rw [e23]) (by rw [e23])
      (by rw [dist_comm (vv 3) (vv 0), e03]) (by rw [dist_comm (vv 3) (vv 0), e03])
      (hnorm 1).1 (hnorm 1).2
      (by rw [dist_comm (vv 2) (vv 1), e12]) (by rw [dist_comm (vv 2) (vv 1), e12])
      (by rw [e01, cstab_eq_p22]) (by rw [e01, cstab_eq_p22])
      (quad_4680581274_derived' h (dist (vv 3) (vv 1)) ‖vv 3‖ ‖vv 0‖ ‖vv 2‖
        (dist (vv 2) (vv 0)) (dist (vv 2) (vv 3)) (dist (vv 3) (vv 0)) ‖vv 1‖
        (dist (vv 2) (vv 1)) (dist (vv 0) (vv 1)))
    have hder' := hder ⟨hEnc, hy4le, hd0, hd1, hd2⟩
    have e1 : tau3 (vv 3) (vv 0) (vv 2) =
        taum ‖vv 3‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 2) (vv 0)) (dist (vv 2) (vv 3))
          (dist (vv 3) (vv 0)) := by
      have h := tau3_taum_40 (vv 3) (vv 0) (vv 2) (hann 3) (hann 0) (hann 2)
        (by rw [dist_comm (vv 3) (vv 0), e03])
        (by rw [dist_comm (vv 3) (vv 2), e23])
        (by linarith [show (2:ℝ) ≤ cstab from by norm_num [cstab], lo02])
        (by rw [dist_comm (vv 3) (vv 0)]; exact hd03)
        (by rw [dist_comm (vv 3) (vv 2)]; exact hd23)
        hd02
      rw [show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 3) (vv 2) = dist (vv 2) (vv 3) from dist_comm _ _] at h
      exact h
    have e2 : tau3 (vv 1) (vv 0) (vv 2) =
        taum ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 2) (vv 0)) (dist (vv 2) (vv 1))
          (dist (vv 0) (vv 1)) := by
      have h := tau3_taum_40 (vv 1) (vv 0) (vv 2) (hann 1) (hann 0) (hann 2)
        (by rw [dist_comm (vv 1) (vv 0), e01, cstab_eq_p22]; norm_num)
        (by rw [e12])
        (by linarith [show (2:ℝ) ≤ cstab from by norm_num [cstab], lo02])
        (by rw [dist_comm (vv 1) (vv 0)]; exact hd01)
        hd12 hd02
      rw [show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 1) (vv 2) = dist (vv 2) (vv 1) from dist_comm _ _,
        show dist (vv 1) (vv 0) = dist (vv 0) (vv 1) from dist_comm _ _] at h
      exact h
    have hres : (0.513:ℝ) < tau3 (vv 3) (vv 0) (vv 2) + tau3 (vv 1) (vv 0) (vv 2) := by
      rw [e1, e2]
      unfold tauq at hder'
      linarith [hder']
    have g1 : tau3 (vv 0) (vv 1) (vv 2) = tau3 (vv 1) (vv 0) (vv 2) :=
      (tau3_sym (vv 0) (vv 1) (vv 2)).2
    have g2 : tau3 (vv 2) (vv 3) (vv 0) = tau3 (vv 3) (vv 0) (vv 2) :=
      (tau3_sym (vv 2) (vv 3) (vv 0)).2.trans (tau3_sym (vv 3) (vv 2) (vv 0)).1
    rw [g1, g2]
    linarith [hres]
  · -- i = 1: relabel `(v1,v2,v3,v4) = (vv 2, vv 1, vv 3, vv 0)`
    rw [show (1 + 3 : ℕ) = 0 + 4 from by norm_num, hper 0]
    have hEnc : enclosedP38 ‖vv 2‖ (dist (vv 2) (vv 3)) (dist (vv 1) (vv 2))
        (dist (vv 1) (vv 3)) ‖vv 1‖ ‖vv 3‖ ‖vv 0‖ (dist (vv 0) (vv 3))
        (dist (vv 0) (vv 1)) = dist (vv 2) (vv 0) := by
      have hv := vv_enclosed4 vv 1 hper hd12 hd14 hsep hsub hd13 hcf hinj
      rw [(by norm_num : (1 + 1 : ℕ) = 2), (by norm_num : (1 + 2 : ℕ) = 3),
        (by norm_num : (1 + 3 : ℕ) = 0 + 4), hper 0,
        dist_comm (vv 1) (vv 0), dist_comm (vv 3) (vv 0)] at hv
      have hsym := enclosed_sym ‖vv 2‖ ‖vv 1‖ ‖vv 3‖ (dist (vv 1) (vv 3))
        (dist (vv 2) (vv 3)) (dist (vv 1) (vv 2)) ‖vv 0‖
        (dist (vv 0) (vv 3)) (dist (vv 0) (vv 1))
      set_option maxRecDepth 65536 in
      exact hsym.trans hv.symm
    have hd0 : 0 ≤ deltaY (dist (vv 2) (vv 0)) (dist (vv 0) (vv 1))
        (dist (vv 0) (vv 3)) (dist (vv 1) (vv 3)) (dist (vv 2) (vv 3))
        (dist (vv 1) (vv 2)) := by
      have hpos := DELTA_Y_POS_4POINTS (vv 0) (vv 2) (vv 1) (vv 3)
      rw [show dist (vv 0) (vv 2) = dist (vv 2) (vv 0) from dist_comm _ _,
        show dist (vv 2) (vv 1) = dist (vv 1) (vv 2) from dist_comm _ _] at hpos
      exact hpos
    have hd1 : 0 ≤ deltaY ‖vv 2‖ ‖vv 1‖ ‖vv 3‖ (dist (vv 1) (vv 3))
        (dist (vv 2) (vv 3)) (dist (vv 1) (vv 2)) := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 2) (vv 1) (vv 3)
      rw [dist_zero_left, dist_zero_left, dist_zero_left,
        show dist (vv 2) (vv 1) = dist (vv 1) (vv 2) from dist_comm _ _] at hpos
      exact hpos
    have hd2 : 0 ≤ deltaY ‖vv 0‖ ‖vv 1‖ ‖vv 3‖ (dist (vv 1) (vv 3))
        (dist (vv 0) (vv 3)) (dist (vv 0) (vv 1)) := by
      have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 0) (vv 1) (vv 3)
      rw [dist_zero_left, dist_zero_left, dist_zero_left] at hpos
      exact hpos
    have hy4le : dist (vv 1) (vv 3) ≤ dist (vv 2) (vv 0) := by
      simpa only [(by norm_num : (1 + 2 : ℕ) = 3), (by norm_num : (1 + 1 : ℕ) = 2),
        (by norm_num : (1 + 3 : ℕ) = 0 + 4), hper 0,
        dist_comm (vv 2) (vv 0)] using hdiag
    have hder := quad_box_out_c _ (dist (vv 2) (vv 0)) ‖vv 2‖ ‖vv 1‖ ‖vv 3‖
      (dist (vv 1) (vv 3)) (dist (vv 2) (vv 3)) (dist (vv 1) (vv 2)) ‖vv 0‖
      (dist (vv 0) (vv 3)) (dist (vv 0) (vv 1))
      (by simpa only [dist_comm (vv 0) (vv 2), cstab_eq_p22] using lo02)
      (by rw [dist_comm (vv 2) (vv 0)]; exact le_of_lt hd02)
      (hnorm 2).1 (hnorm 2).2 (hnorm 1).1 (hnorm 1).2
      (hnorm 3).1 (hnorm 3).2
      (by simpa only [cstab_eq_p22] using lo13) (le_of_lt hd13)
      (by rw [e23]) (by rw [e23])
      (by rw [e12]) (by rw [e12])
      (hnorm 0).1 (hnorm 0).2
      (by rw [e03]) (by rw [e03])
      (by rw [e01, cstab_eq_p22]) (by rw [e01, cstab_eq_p22])
      (quad_4680581274_derived' h (dist (vv 2) (vv 0)) ‖vv 2‖ ‖vv 1‖ ‖vv 3‖
        (dist (vv 1) (vv 3)) (dist (vv 2) (vv 3)) (dist (vv 1) (vv 2)) ‖vv 0‖
        (dist (vv 0) (vv 3)) (dist (vv 0) (vv 1)))
    have hder' := hder ⟨hEnc, hy4le, hd0, hd1, hd2⟩
    have e1 : tau3 (vv 2) (vv 1) (vv 3) =
        taum ‖vv 2‖ ‖vv 1‖ ‖vv 3‖ (dist (vv 1) (vv 3)) (dist (vv 2) (vv 3))
          (dist (vv 1) (vv 2)) := by
      have h := tau3_taum_40 (vv 2) (vv 1) (vv 3) (hann 2) (hann 1) (hann 3)
        (by rw [dist_comm (vv 2) (vv 1), e12])
        (by rw [e23])
        (by linarith [show (2:ℝ) ≤ cstab from by norm_num [cstab], lo13])
        (by rw [dist_comm (vv 2) (vv 1)]; exact hd12)
        hd23 hd13
      rw [show dist (vv 2) (vv 1) = dist (vv 1) (vv 2) from dist_comm _ _] at h
      exact h
    have e2 : tau3 (vv 0) (vv 1) (vv 3) =
        taum ‖vv 0‖ ‖vv 1‖ ‖vv 3‖ (dist (vv 1) (vv 3)) (dist (vv 0) (vv 3))
          (dist (vv 0) (vv 1)) := by
      have h := tau3_taum_40 (vv 0) (vv 1) (vv 3) (hann 0) (hann 1) (hann 3)
        (by rw [e01, cstab_eq_p22]; norm_num)
        (by rw [e03])
        (by linarith [show (2:ℝ) ≤ cstab from by norm_num [cstab], lo13])
        hd01 hd03 hd13
      simpa only [dist_comm (vv 1) (vv 0)] using h
    have hres : (0.513:ℝ) < tau3 (vv 2) (vv 1) (vv 3) + tau3 (vv 0) (vv 1) (vv 3) := by
      rw [e1, e2]
      unfold tauq at hder'
      linarith [hder']
    have g1 : tau3 (vv 1) (vv 2) (vv 3) = tau3 (vv 2) (vv 1) (vv 3) :=
      (tau3_sym (vv 1) (vv 2) (vv 3)).2
    have g2 : tau3 (vv 3) (vv 0) (vv 1) = tau3 (vv 0) (vv 1) (vv 3) :=
      (tau3_sym (vv 3) (vv 0) (vv 1)).2.trans (tau3_sym (vv 0) (vv 3) (vv 1)).1
    rw [g1, g2]
    linarith [hres]

/-- HOL `empty_4T3` (terminal.hl:3943): the **first** in-tree declaration of
this theorem (LA22 keeps only the two PARTIAL halves `emptykit_apos_4T3` /
`emptykit_azim_4T3_pre`, and `empty_4T3` itself is not declared anywhere);
the statement is the HOL statement rendered with `scs4T3`. -/
theorem empty_4T3_p22' (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs4T3 vv) : 0 ≤ taustarV39 scs4T3 vv := by
  unfold scs4T3 at hB ⊢
  exact terminal_quad_lemma 0.513 _ _ emptykit_apos_4T3_c (emptykit_azim_4T3_c h) vv hB

/-- HOL `OCBICBY` 4T3 branch (OCBICBY.hl:4761): the arrow to the empty
system, exactly as the `OCBICBY_4T2_p22` template. -/
theorem OCBICBY_4T3_p22' (h : main_nonlinear_terminal_v11) :
    scsArrowV39 {scs4T3} ∅ := by
  rw [scs_arrow_sing_empty_p22]
  ext vv
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨⟨⟨hbb, _, hneg⟩, _⟩, _, _, _, _, _⟩ := hv
  exact (not_le.mpr hneg) (empty_4T3_p22' h _ hbb)

/-- HOL `empty_6T1` (giant; the analytic core of the terminal emptiness). -/
theorem empty_6T1_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv) : 0 ≤ taustarV39 scs6T1 vv := by
  sorry

/-! ### 6T1: the two-input conditional assembly (lanes `hex6t1prep-w1` /
`hex51-w2` interface)

`empty6T1_hex_bridge_p22` consumes two numeric inputs: the hex-tower
inequality `hnum` (`0.712 <` three `taum`s, HOL `terminal_hex_taum`) and the
fourth-ear nonnegativity `ht4nn`.  `hnum` is reduced here to a *single*
geometric input, `hE : 0 ≤ yOfX eulerAx_p19 …` (the Euler `A` of the even
triple `vv 0, vv 2, vv 4`), through the proved `terminal_hex_taum_p19`
(the other three disjuncts are `DELTA_Y_POS_4POINTS`).  See
`LP-OBLIGATION-6T1.md` for why `hE` holds geometrically and what is missing
in-tree. -/

/-- `hnum` of `empty6T1_hex_bridge_p22`, reduced to the Euler-`A` input `hE`
via the proved hex-tower theorem `terminal_hex_taum_p19` (LA19:4018); the
three `deltaY` escapes are `DELTA_Y_POS_4POINTS`. -/
theorem hex_tower_hnum_p22 (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv)
    (hE : 0 ≤ yOfX eulerAx_p19 ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4))
      (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2))) :
    0.712 < taum ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 0) (vv 2)) 2 2
      + taum ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4)) (dist (vv 0) (vv 4))
          (dist (vv 0) (vv 2))
      + taum ‖vv 5‖ ‖vv 0‖ ‖vv 4‖ (dist (vv 0) (vv 4)) 2 2 := by
  have hann : ∀ i : ℕ, vv i ∈ ballAnnulus := fun i => hB.1 (Set.mem_range_self i)
  have hnorm : ∀ i : ℕ, (2:ℝ) ≤ ‖vv i‖ ∧ ‖vv i‖ ≤ 2 * h0 := fun i =>
    ballAnnulus_norm_bounds (hann i)
  have h252 : (2:ℝ) * h0 = 2.52 := by norm_num [h0]
  have hper6 : Periodic vv 6 := hB.2.1
  have hedge : ∀ i : ℕ, dist (vv i) (vv (i + 1)) = 2 :=
    fun i => scs_6T1_props_p22.2.2.2 vv i hB
  have hdiag20 : ∀ i : ℕ, scsDiag 6 i (i + 2) := by
    intro i
    refine ⟨MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) < 6)
        (by norm_num : (2 : ℕ) ≠ 0) i,
      MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (1 : ℕ) < 6)
        (by norm_num : (1 : ℕ) ≠ 0) (i + 1),
      MOD_INJ1_ALT (by norm_num : (6 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) < 6)
        (by norm_num : (3 : ℕ) ≠ 0) i⟩
  have hdiag2 : ∀ i : ℕ, cstab ≤ dist (vv i) (vv (i + 2)) :=
    fun i => scs_6T1_props_p22.2.2.1 vv i (i + 2) hB (hdiag20 i)
  have h4i : ∀ i : ℕ, dist (vv i) (vv (i + 2)) ≤ 4 := by
    intro i
    have htri := dist_triangle (vv i) (vv (i + 1)) (vv (i + 2))
    rw [hedge i, hedge (i + 1)] at htri
    linarith
  have hreg : mainEstimate_6459846571 :=
    h "6459846571" (by simp [mainNonlinearTerminalV11Ids_t11])
  unfold mainEstimate_6459846571 at hreg
  have hdiag_le : ∀ i : ℕ, dist (vv i) (vv (i + 2)) < 3.915 := by
    intro i
    have hdpos := DELTA_Y_POS_4POINTS (0 : V3) (vv (i + 1)) (vv i) (vv (i + 2))
    rw [dist_zero_left, dist_zero_left, dist_zero_left,
      show dist (vv (i + 1)) (vv (i + 2)) = 2 from hedge (i + 1),
      show dist (vv (i + 1)) (vv i) = 2 from by rw [dist_comm]; exact hedge i] at hdpos
    have hb1 := ballAnnulus_norm_bounds (hann (i + 1))
    have hb2 := ballAnnulus_norm_bounds (hann i)
    have hb3 := ballAnnulus_norm_bounds (hann (i + 2))
    have hu : (2 : ℝ) * h0 = 2.52 := by rw [h0_eq_p22]; norm_num
    have hc2 := hdiag2 i
    rw [cstab_eq_p22] at hc2
    have hr := hreg ‖vv (i + 1)‖ ‖vv i‖ ‖vv (i + 2)‖ (dist (vv i) (vv (i + 2))) 2 2
      hb1.1 (by linarith [hb1.2, hu]) hb2.1 (by linarith [hb2.2, hu])
      hb3.1 (by linarith [hb3.2, hu]) (by linarith) (by linarith [h4i i])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rcases hr with hlt | hdlt
    · exact hlt
    · exact absurd hdlt (not_lt.mpr hdpos)
  -- the three diagonal slots (with the `vv 0 = vv 6` collapse for `vv 0 - vv 4`)
  have hy4l : (3.01:ℝ) ≤ dist (vv 2) (vv 4) := by
    have hh := hdiag2 2
    rwa [cstab_eq_p22] at hh
  have hy4u : dist (vv 2) (vv 4) ≤ 3.915 := le_of_lt (hdiag_le 2)
  have hy5eq : dist (vv 0) (vv 4) = dist (vv 4) (vv (4 + 2)) := by
    rw [show (4 + 2 : ℕ) = 0 + 6 by norm_num, hper6 0, dist_comm]
  have hy5l : (3.01:ℝ) ≤ dist (vv 0) (vv 4) := by
    have hh := hdiag2 4
    rw [show (4 + 2 : ℕ) = 0 + 6 by norm_num, hper6 0, dist_comm] at hh
    rwa [cstab_eq_p22] at hh
  have hy5u : dist (vv 0) (vv 4) ≤ 3.915 := by
    rw [hy5eq]
    exact le_of_lt (hdiag_le 4)
  have hy6l : (3.01:ℝ) ≤ dist (vv 0) (vv 2) := by
    have hh := hdiag2 0
    rwa [cstab_eq_p22] at hh
  have hy6u : dist (vv 0) (vv 2) ≤ 3.915 := le_of_lt (hdiag_le 0)
  -- the three `deltaY` nonnegativities (`DELTA_Y_POS_4POINTS`)
  have hD1 : 0 ≤ deltaY ‖vv 5‖ ‖vv 0‖ ‖vv 4‖ (dist (vv 0) (vv 4)) 2 2 := by
    have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 5) (vv 0) (vv 4)
    rw [dist_zero_left, dist_zero_left, dist_zero_left,
      show dist (vv 5) (vv 4) = 2 from by rw [dist_comm]; exact hedge 4,
      show dist (vv 5) (vv 0) = 2 from by
        have hh := hedge 5
        rw [show (5 + 1 : ℕ) = 0 + 6 by norm_num, hper6 0] at hh
        exact hh] at hpos
    exact hpos
  have hD2 : 0 ≤ deltaY ‖vv 1‖ ‖vv 0‖ ‖vv 2‖ (dist (vv 0) (vv 2)) 2 2 := by
    have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 1) (vv 0) (vv 2)
    rw [dist_zero_left, dist_zero_left, dist_zero_left,
      show dist (vv 1) (vv 2) = 2 from hedge 1,
      show dist (vv 1) (vv 0) = 2 from by rw [dist_comm]; exact hedge 0] at hpos
    exact hpos
  have hD3 : 0 ≤ deltaY ‖vv 3‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4)) 2 2 := by
    have hpos := DELTA_Y_POS_4POINTS (0 : V3) (vv 3) (vv 2) (vv 4)
    rw [dist_zero_left, dist_zero_left, dist_zero_left,
      show dist (vv 3) (vv 4) = 2 from hedge 3,
      show dist (vv 3) (vv 2) = 2 from by rw [dist_comm]; exact hedge 2] at hpos
    exact hpos
  have hdisj := terminal_hex_taum_p19 h ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4))
    (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2)) ‖vv 3‖ ‖vv 1‖ ‖vv 5‖
    ⟨(hnorm 0).1, by linarith [(hnorm 0).2, h252]⟩
    ⟨(hnorm 2).1, by linarith [(hnorm 2).2, h252]⟩
    ⟨(hnorm 4).1, by linarith [(hnorm 4).2, h252]⟩
    ⟨hy4l, hy4u⟩ ⟨hy5l, hy5u⟩ ⟨hy6l, hy6u⟩
    ⟨(hnorm 3).1, by linarith [(hnorm 3).2, h252]⟩
    ⟨(hnorm 1).1, by linarith [(hnorm 1).2, h252]⟩
    ⟨(hnorm 5).1, by linarith [(hnorm 5).2, h252]⟩
  rcases hdisj with hA | hD | hD
  · exact hA
  · rcases hD with hD | hD
    · linarith
    · linarith
  · rcases hD with hD | hD
    · linarith
    · linarith

/-- `empty_6T1_p22` on the two remaining numeric inputs (`ht4nn` = the
missing LP box, `hE` = the Euler-`A` nonnegativity of the even triple):
`hnum` is discharged by `hex_tower_hnum_p22`, then the bridge. -/
theorem empty_6T1_p22_of_ht4nn (h : main_nonlinear_terminal_v11) (vv : ℕ → V3)
    (hB : BBsV39 scs6T1 vv)
    (hE : 0 ≤ yOfX eulerAx_p19 ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4))
      (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2)))
    (ht4nn : 0 ≤ taum ‖vv 2‖ ‖vv 3‖ ‖vv 4‖ (dist (vv 3) (vv 4))
      (dist (vv 2) (vv 4)) (dist (vv 2) (vv 3))) :
    0 ≤ taustarV39 scs6T1 vv :=
  empty6T1_hex_bridge_p22 h vv hB (hex_tower_hnum_p22 h vv hB hE) ht4nn

/-- `OCBICBY` 6T1 branch on the same two inputs (template of
`OCBICBY_4T2_p22`; keeps the `empty_*` sorry face untouched). -/
theorem OCBICBY_6T1_p22_of_ht4nn (h : main_nonlinear_terminal_v11) :
    (∀ vv : ℕ → V3, BBsV39 scs6T1 vv →
      0 ≤ yOfX eulerAx_p19 ‖vv 0‖ ‖vv 2‖ ‖vv 4‖ (dist (vv 2) (vv 4))
        (dist (vv 0) (vv 4)) (dist (vv 0) (vv 2))) →
    (∀ vv : ℕ → V3, BBsV39 scs6T1 vv →
      0 ≤ taum ‖vv 2‖ ‖vv 3‖ ‖vv 4‖ (dist (vv 3) (vv 4))
        (dist (vv 2) (vv 4)) (dist (vv 2) (vv 3))) →
    scsArrowV39 {scs6T1} ∅ := by
  intro hE ht4nn
  rw [scs_arrow_sing_empty_p22]
  ext vv
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨⟨⟨hbb, _, hneg⟩, _⟩, _, _, _, _, _⟩ := hv
  exact (not_le.mpr hneg) (empty_6T1_p22_of_ht4nn h vv hbb (hE vv hbb) (ht4nn vv hbb))

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

/-- HOL `terminal_pent_taum2` (OCBICBY.hl:3357-3402).  **SF-109 修正**（2026-11-14：
`ineqP22` 结论壳 → `hbox` 前提 + 展平结论；原壳把合取放结论、陈述层不可满足）：
`angle_sum_5T1` 的 20-析取 + `terminal_pent_taum_p19` 两支装配，证明体 =
`ocb_terminal_pent_taum2_core`。 -/
theorem terminal_pent_taum2_p22 (h : main_nonlinear_terminal_v11)
    (y1 y2 y3 y4 y5 y6 y126 y135 : ℝ)
    (hbox : ineqP22 [(2, y1, 2 * h0), (2, y2, 2 * h0), (2, y3, 2 * h0), (2, y4, 2),
      (3.01, y5, 3.237), (3.01, y6, 3.237), (2, y126, 2 * h0), (2, y135, 2 * h0)] True)
    (hd1 : 0 ≤ deltaY y126 y1 y2 y6 2 2)
    (hd2 : 0 ≤ deltaY y135 y1 y3 y5 2 2)
    (hsub : dihY y1 y126 y135 cstab 2 2 ≤
        dihY y1 y2 y3 y4 y5 y6 + dihY y1 y2 y126 2 2 y6 +
          dihY y1 y3 y135 2 2 y5) :
    0.616 < taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6 + taum y135 y1 y3 y5 2 2 := by
  exact ocb_terminal_pent_taum2_core h y1 y2 y3 y4 y5 y6 y126 y135 hbox hd1 hd2 hsub

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
