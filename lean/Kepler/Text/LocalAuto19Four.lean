/-
LocalAuto19Four — 6T1 的 HOL 四项和版 hex tower（lane hexfour-w1, 2026-11-14）。

动机：`ht4nn`（第四耳非负）已被 `ht4nn-probe-w1` 用内核定理证假
（`taum 2 2 2 2 (883/256) 2 < 0`），故现有 6T1 桥的"三项 > 0.712 + 第四耳 ≥ 0"
分解是过度强化。HOL `OCBICBY.hl:3040` 的原语句是**四项和**：
`#0.712 <= tau3 (vv 0) (vv 1) (vv 2) + tau3 (vv 0) (vv 2) (vv 4)
   + tau3 (vv 0) (vv 4) (vv 5) + tau3 (vv 2) (vv 3) (vv 4)`。

本文件把 `LocalAuto19.terminal_hex_taum_p19` 的装配改造成四项和：第四耳
`taum y234 y2 y3 y4 2 2` 只能经 `terminal_hex_234_reduction_p19` 进入和式
（taum 可为负，不能"白加"），故链条是
135（f1 含第四耳）→ 126（f2 := 0, f1 含第四耳）→ 234 → r755 库条目，
与 HOL `mk_5`/`mk_25` 逐层同构，需要 r755 库的全部 125 个 (i,j,k) 干净条目。

零新增 axiom/sorry/native_decide；既有陈述零改动。
-/
import Kepler.Text.LocalAuto19

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## S3 diagonal discharge, generic index

`LocalAuto19.r755_noS45S56_1_p19` is the `(1,1,1)` case only; the four-term
chain consumes the `(m,m,m)` columns for every `m ≤ 4`, so the six-frame
cascade is replayed at a generic index. -/

theorem r755_noS45S56_p19 {i : ℕ}
    (hraw : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
          (3.01, y5, 3.915), (3.01, y6, 3.915)]
        (r755Body_p19 i i i 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
          (y6 < y4) (y5 < y6) y1 y2 y3 y4 y5 y6)) :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
          (3.01, y5, 3.915), (3.01, y6, 3.915)]
        (r755Body_p19 i i i 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
          False False y1 y2 y3 y4 y5 y6) := by
  intro y1 y2 y3 y4 y5 y6 c1 c2 c3 c4 c5 c6
  rw [r755Body_p19]
  rcases lt_trichotomy y6 y4 with h64 | he64 | h46
  · -- w < u
    rcases le_total y4 y5 with h45l | h54l
    · -- u ≤ v: the σ frame (y3,y2,y1,y6,y5,y4); both side disjuncts false
      have h := hraw y3 y2 y1 y6 y5 y4 c3 c2 c1 c6 c5 c4
      rw [r755Body_p19, taum_sym_jik_p19,
        (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).2.2.1,
        r755D234_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
        r755D126_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
        r755D135_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
        r755C234_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
        r755C126_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
        r755C135_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6] at h
      rcases h with hP | he | h3 | h4 | h135 | hs | hf2 | hb2
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inl h4))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h135))))
      · exact absurd hs (by linarith)
      · exact absurd hf2 (by linarith)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
    · rcases le_total y6 y5 with h65l | h56l
      · -- v ≤ u ∧ w ≤ v: the ρσ frame (y3,y1,y2,y6,y4,y5); two hops
        have h := hraw y3 y1 y2 y6 y4 y5 c3 c1 c2 c6 c4 c5
        rw [r755Body_p19, (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).2.1,
          taum_sym_ikj_p19 y3 y2 y1 y6 y5 y4,
          r755D234_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          r755D126_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          r755D135_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          r755C234_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          r755C126_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          r755C135_shuffle_ikj_p19 i y3 y2 y1 y6 y5 y4,
          taum_sym_jik_p19,
          r755D234_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
          r755D126_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
          r755D135_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
          r755C234_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
          r755C126_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6,
          r755C135_shuffle_jik_p19 i y1 y2 y3 y4 y5 y6] at h
        rcases h with hP | he | h3 | h4 | h135 | hs | hf2 | hb2
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        · exact Or.inr (Or.inr (Or.inl h135))
        · exact absurd hs (by linarith)
        · exact absurd hf2 (by linarith)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
      · -- v ≤ u ∧ v ≤ w: the τ frame (y2,y1,y3,y5,y4,y6); three hops
        have h := hraw y2 y1 y3 y5 y4 y6 c2 c1 c3 c5 c4 c6
        rw [r755Body_p19, (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).1,
          taum_sym_ikj_p19 y2 y3 y1 y5 y6 y4,
          r755D234_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          r755D126_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          r755D135_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          r755C234_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          r755C126_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          r755C135_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
          taum_sym_jik_p19 y1 y3 y2 y4 y6 y5,
          r755D234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755D126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755D135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          taum_sym_ikj_p19,
          r755D234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6] at h
        rcases h with hP | he | h3 | h4 | h135 | hs | hf2 | hb2
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · exact Or.inr (Or.inr (Or.inl h135))
        · exact absurd hs (by linarith)
        · exact absurd hf2 (by linarith)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
  · -- w = u
    rcases le_total y6 y5 with h65l | h56l
    · -- w ≤ v: the frame itself; both side disjuncts false
      have h := hraw y1 y2 y3 y4 y5 y6 c1 c2 c3 c4 c5 c6
      rw [r755Body_p19] at h
      rcases h with hP | he | h234 | h126 | h135 | hs | hf2 | hb2
      · exact Or.inl hP
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl h234))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h126)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h135))))
      · exact absurd hs (by linarith)
      · exact absurd hf2 (by linarith)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
    · -- v ≤ w: the τ frame (y2,y1,y3,y5,y4,y6); three hops
      have h := hraw y2 y1 y3 y5 y4 y6 c2 c1 c3 c5 c4 c6
      rw [r755Body_p19, (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).1,
        taum_sym_ikj_p19 y2 y3 y1 y5 y6 y4,
        r755D234_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        r755D126_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        r755D135_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        r755C234_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        r755C126_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        r755C135_shuffle_ikj_p19 i y2 y3 y1 y5 y6 y4,
        taum_sym_jik_p19 y1 y3 y2 y4 y6 y5,
        r755D234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        r755D126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        r755D135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        r755C234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        r755C126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        r755C135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
        taum_sym_ikj_p19,
        r755D234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
        r755D126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
        r755D135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
        r755C234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
        r755C126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
        r755C135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6] at h
      rcases h with hP | he | h3 | h4 | h135 | hs | hf2 | hb2
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      · exact Or.inr (Or.inr (Or.inl h135))
      · exact absurd hs (by linarith)
      · exact absurd hf2 (by linarith)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
  · -- w > u
    rcases le_total y6 y5 with h65l | h56l
    · -- w ≤ v: the frame itself; both side disjuncts false
      have h := hraw y1 y2 y3 y4 y5 y6 c1 c2 c3 c4 c5 c6
      rw [r755Body_p19] at h
      rcases h with hP | he | h234 | h126 | h135 | hs | hf2 | hb2
      · exact Or.inl hP
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl h234))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h126)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h135))))
      · exact absurd hs (by linarith)
      · exact absurd hf2 (by linarith)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
    · rcases le_total y4 y5 with h45l | h54l
      · -- u ≤ v ∧ v ≤ w: the ρ frame (y1,y3,y2,y4,y6,y5); both false
        have h := hraw y1 y3 y2 y4 y6 y5 c1 c3 c2 c4 c6 c5
        rw [r755Body_p19, taum_sym_ikj_p19,
          (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).2.2.2,
          r755D234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6] at h
        rcases h with hP | he | h234 | h126 | h135 | hs | hf2 | hb2
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inl h234))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h126))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h135)))
        · exact absurd hs (by linarith)
        · exact absurd hf2 (by linarith)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))
      · -- v ≤ u ∧ v ≤ w: the σρ frame (y2,y3,y1,y5,y6,y4); two hops
        have h := hraw y2 y3 y1 y5 y6 y4 c2 c3 c1 c5 c6 c4
        rw [r755Body_p19,
          taum_sym_jik_p19 y1 y3 y2 y4 y6 y5,
          (eulerA_x_sym_cases_p19 y1 y3 y2 y4 y6 y5).2.2.1,
          r755D234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755D126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755D135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C234_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C126_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          r755C135_shuffle_jik_p19 i y1 y3 y2 y4 y6 y5,
          taum_sym_ikj_p19, (eulerA_x_sym_cases_p19 y1 y2 y3 y4 y5 y6).2.2.2,
          r755D234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755D135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C234_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C126_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6,
          r755C135_shuffle_ikj_p19 i y1 y2 y3 y4 y5 y6] at h
        rcases h with hP | he | h3 | h4 | h135 | hs | hf2 | hb2
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
        · exact Or.inr (Or.inr (Or.inl h4))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h135)))
        · exact absurd hs (by linarith)
        · exact absurd hf2 (by linarith)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb2))))))

/-- The 125 clean r755 entries (`7550003505 i j k`, i,j,k ≤ 4) with both side
disjuncts (`s45`/`s56`) removed and `b2` kept as the eulerA escape.

The registry stores each hex-ear template once at its **ascending** index
triple (`mainEstimate_7550003505_a_b_c`, a ≤ b ≤ c — 35 of them); the other
90 index tuples are reached by the `ikj`/`jik` frame transports, exactly as
HOL's `get_ineq5` instantiation replays `r755_ikj`/`r755_jik`.  Flag
elimination is done once per multiset, at the sorted representative. -/
theorem r755_db_p19 (h : mainNonlinearTerminalV11_p18) :
    ∀ i j k : ℕ, i ≤ 4 → j ≤ 4 → k ≤ 4 →
      ∀ y1 y2 y3 y4 y5 y6 : ℝ,
        ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
            (3.01, y5, 3.915), (3.01, y6, 3.915)]
          (r755Body_p19 i j k 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
            False False y1 y2 y3 y4 y5 y6) := by
  intro i j k hi hj hk
  interval_cases i <;> interval_cases j <;> interval_cases k
  · exact r755_noS45S56_p19 (r755_res_both_p19 (h "7550003505 0 0 0" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 1" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 1" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 1 1" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 2 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 1" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 1 1" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 1 1" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_noS45S56_p19 (r755_res_both_p19 (h "7550003505 1 1 1" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 2 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 2" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 2 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 2" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 2" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 2 2" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 2 2" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 2 2" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_noS45S56_p19 (r755_res_both_p19 (h "7550003505 2 2 2" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 3 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 3 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 3 3" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_noS45S56_p19 (r755_res_both_p19 (h "7550003505 3 3 3" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 3 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 3 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 3 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 0 0 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 4 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 1 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 1 1 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 4 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 2 2 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 4 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 0 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 1 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_body_jik_p19 (r755_res_clean_p19 (by norm_num) (by norm_num) (h "7550003505 2 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_body_ikj_p19 (r755_noS45_p19 (r755_res_s45_p19 (by norm_num) (h "7550003505 3 3 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 3 4 4" (by simp [mainNonlinearTerminalV11Ids_t11]))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 0 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 1 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 2 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_body_ikj_p19 (r755_body_jik_p19 (r755_noS56_p19 (r755_res_s56_p19 (by norm_num) (h "7550003505 3 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))))
  · exact r755_noS45S56_p19 (r755_res_both_p19 (h "7550003505 4 4 4" (by simp [mainNonlinearTerminalV11Ids_t11])))

/-! ## The four-term hex tower (HOL `terminal_hex_taum`, `pent_hex.hl:3180`,
consumed by `OCBICBY.hl:3040` as a **four-term** sum)

`ht4nn-probe-w1` proved the old "fourth ear ≥ 0" input (`ht4nn`) **false** in
the kernel (`taum 2 2 2 2 (883/256) 2 < 0`), so the three-term + `ht4nn` split
is an over-strengthening; HOL keeps the fourth ear inside the sum.  The ear
cannot be appended to an existing `> 0.712` (it can be negative): it enters
through `terminal_hex_234_reduction_p19`, whose minimiser route covers
`taum y234 < 0 ≤ deltaY y234 …`.  Layering (HOL `mk_25` / `mk_5` / top):

* `hex234_step_p19` : db column `(m, j, k)` → `taum(y1..y6) + taum(y234) + D135_k + D126_j`
* `hex126_step_p19` : the five 234 steps over `j` → `taum(y1..y6) + taum(y234) + D135_i + taum(y126)`
* `hex135_step_p19` : the five 126 steps over `i` → `taum(y126) + taum(y1..y6) + taum(y234) + taum(y135)`
-/

/-- 234 step of the four-term chain (inner layer): introduces the fourth ear
`taum y234 y2 y3 y4 2 2` into the running sum.  `f1 = taum(y1..y6) + D135_k +
D126_j`, `f2 = 0`, `b1 = C135_k ∨ C126_j`, `b2 = eulerA < 0`. -/
theorem hex234_step_p19 (h : mainNonlinearTerminalV11_p18)
    (hdb : ∀ i j k : ℕ, i ≤ 4 → j ≤ 4 → k ≤ 4 →
      ∀ y1 y2 y3 y4 y5 y6 : ℝ,
        ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
            (3.01, y5, 3.915), (3.01, y6, 3.915)]
          (r755Body_p19 i j k 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
            False False y1 y2 y3 y4 y5 y6))
    {j k : ℕ} (hj : j ≤ 4) (hk : k ≤ 4) (y1 y2 y3 y4 y5 y6 y234 : ℝ) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6 > 0.712 ∨
        r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨
          r755C126_p19 j y1 y2 y3 y4 y5 y6 ∨
          (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
  have nmud234 : mud234xV1_p19 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
        * Real.sqrt (deltaY 2 y2 y3 y4 2 2) := by
    have h2 := nonfunctional_mud_234_p19 2 2 2 y1 y2 y3 y4 y5 y6
    rw [yOfX] at h2
    exact h2
  have nmudLs234 : mudLs234x_p19 4 10 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
        * (1 / 14 * (deltaY 2 y2 y3 y4 2 2 - 16) + 2 * 2) := by
    rw [nonfunctional_mudLs_234_p19 (y1 * y1) y2 y3 y4 (y5 * y5) (y6 * y6),
      show (4 : ℝ) = 2 * 2 from by norm_num]
  have h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6
          + yOfX (flatTerm2_234x_p19 0 4 4) y1 y2 y3 y4 y5 y6 + 0 > 0.712 ∨
        (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6) ∨ (deltaY 2 y2 y3 y4 2 2 < 0 ∨ deltaY 2.52 y2 y3 y4 2 2 > 0) ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hb := hdb 0 j k (by norm_num) hj hk y1 y2 y3 y4 y5 y6 e1 e2 e3 e4 e5 e6
    rw [r755Body_p19] at hb
    simp only [r755D234_p19, zero_add, add_zero] at hb
    rcases hb with hP | he | h3 | h4 | h5 | hF | hF2 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h4))
    · exact Or.inr (Or.inl (Or.inl h5))
    · exact absurd hF id
    · exact absurd hF2 id
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6
          + 0 + 0 > 0.712 ∨
        (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6) ∨ False ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hb := hdb 1 j k (by norm_num) hj hk y1 y2 y3 y4 y5 y6 e1 e2 e3 e4 e5 e6
    rw [r755Body_p19] at hb
    simp only [r755D234_p19, zero_add, add_zero] at hb
    rcases hb with hP | he | h3 | h4 | h5 | hF | hF2 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h4))
    · exact Or.inr (Or.inl (Or.inl h5))
    · exact absurd hF id
    · exact absurd hF2 id
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6
          + (muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * Real.sqrt (deltaY 2 y2 y3 y4 2 2) - sol0) + 0 > 0.712 ∨
        (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6) ∨ deltaY 2 y2 y3 y4 2 2 < 100 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hb := hdb 2 j k (by norm_num) hj hk y1 y2 y3 y4 y5 y6 e1 e2 e3 e4 e5 e6
    rw [r755Body_p19] at hb
    simp only [r755D234_p19, yOfX, zero_add, add_zero] at hb
    rw [nmud234] at hb
    rcases hb with hP | he | h3 | h4 | h5 | hF | hF2 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h4))
    · exact Or.inr (Or.inl (Or.inl h5))
    · exact absurd hF id
    · exact absurd hF2 id
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6
          + (muY_p19 2 (Real.sqrt (y2 * y2)) (Real.sqrt (y3 * y3))
              * (1 / 14 * (deltaY 2 y2 y3 y4 2 2 - 16) + 2 * 2) - sol0) + 0 > 0.712 ∨
        (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6) ∨ (deltaY 2 y2 y3 y4 2 2 < 16 ∨ deltaY 2 y2 y3 y4 2 2 > 100) ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hb := hdb 3 j k (by norm_num) hj hk y1 y2 y3 y4 y5 y6 e1 e2 e3 e4 e5 e6
    rw [r755Body_p19] at hb
    simp only [r755D234_p19, yOfX, zero_add, add_zero] at hb
    rw [nmudLs234] at hb
    rcases hb with hP | he | h3 | h4 | h5 | hF | hF2 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h4))
    · exact Or.inr (Or.inl (Or.inl h5))
    · exact absurd hF id
    · exact absurd hF2 id
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6
          + (0 - sol0) + 0 > 0.712 ∨
        (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6) ∨ (deltaY 2 y2 y3 y4 2 2 < 0 ∨ deltaY 2 y2 y3 y4 2 2 > 16) ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hb := hdb 4 j k (by norm_num) hj hk y1 y2 y3 y4 y5 y6 e1 e2 e3 e4 e5 e6
    rw [r755Body_p19] at hb
    simp only [r755D234_p19, zero_add, add_zero] at hb
    rcases hb with hP | he | h3 | h4 | h5 | hF | hF2 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inl (Or.inr h4))
    · exact Or.inr (Or.inl (Or.inl h5))
    · exact absurd hF id
    · exact absurd hF2 id
    · exact Or.inr (Or.inr (Or.inr hb2))
  intro d1 d2 d3 d4 d5 d6 d7
  have h := terminal_hex_234_reduction_p19 h y1 y2 y3 y4 y5 y6 y234
    (taum y1 y2 y3 y4 y5 y6 + r755D135_p19 k y1 y2 y3 y4 y5 y6
          + r755D126_p19 j y1 y2 y3 y4 y5 y6) 0
    (r755C135_p19 k y1 y2 y3 y4 y5 y6 ∨ r755C126_p19 j y1 y2 y3 y4 y5 y6)
    (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
    h0c h1c h2c h3c h4c
  rcases h d1 d2 d3 d4 d5 d6 d7 with hP | h2 | hb2
  · exact Or.inl (by linarith)
  · rcases h2 with hd | hb1
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
    · rcases hb1 with h5 | h4
      · exact Or.inr (Or.inl h5)
      · exact Or.inr (Or.inr (Or.inl h4))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hb2)))

/-- 126 step of the four-term chain (middle layer): consumed with
`f1 = taum(y1..y6) + taum(y234) + D135_i`, `f2 = 0`, `b1 = C135_i`,
`b2 = deltaY y234 … < 0 ∨ eulerA < 0`; its five antecedents are the 234 steps
over the `i126` slot.  The `i`-th `D135` slot stays folded here (`i` is still
generic). -/
theorem hex126_step_p19 (h : mainNonlinearTerminalV11_p18)
    (hdb : ∀ i j k : ℕ, i ≤ 4 → j ≤ 4 → k ≤ 4 →
      ∀ y1 y2 y3 y4 y5 y6 : ℝ,
        ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
            (3.01, y5, 3.915), (3.01, y6, 3.915)]
          (r755Body_p19 i j k 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
            False False y1 y2 y3 y4 y5 y6))
    {i : ℕ} (hi : i ≤ 4) (y1 y2 y3 y4 y5 y6 y234 y126 : ℝ) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      ((taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6) + taum y126 y1 y2 y6 2 2 + 0 > 0.712 ∨
        (deltaY y126 y1 y2 y6 2 2 < 0 ∨ r755C135_p19 i y1 y2 y3 y4 y5 y6) ∨
        (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
  have nmud126 : mud126xV1_p19 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
        * Real.sqrt (deltaY 2 y1 y2 y6 2 2) := by
    have h2 := nonfunctional_mud_126_p19 2 2 2 y1 y2 y3 y4 y5 y6
    rw [yOfX] at h2
    exact h2
  have nmudLs126 : mudLs126x_p19 4 10 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
        * (1 / 14 * (deltaY 2 y1 y2 y6 2 2 - 16) + 2 * 2) := by
    rw [nonfunctional_mudLs_126_p19 y1 y2 (y3 * y3) (y4 * y4) (y5 * y5) y6,
      show (4 : ℝ) = 2 * 2 from by norm_num]
  have h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6
          + yOfX (flatTerm2_126x_p19 0 4 4) y1 y2 y3 y4 y5 y6 + 0 > 0.712 ∨
        r755C135_p19 i y1 y2 y3 y4 y5 y6 ∨ (deltaY 2 y1 y2 y6 2 2 < 0 ∨ deltaY 2.52 y1 y2 y6 2 2 > 0) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hh := hex234_step_p19 h hdb (j := 0) (k := i) (by norm_num) hi
      y1 y2 y3 y4 y5 y6 y234 e1 e2 e3 e4 e5 e6 e7
    simp only [r755D126_p19, zero_add, add_zero] at hh
    rcases hh with hP | h5 | h4 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6
          + 0 + 0 > 0.712 ∨
        r755C135_p19 i y1 y2 y3 y4 y5 y6 ∨ False ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hh := hex234_step_p19 h hdb (j := 1) (k := i) (by norm_num) hi
      y1 y2 y3 y4 y5 y6 y234 e1 e2 e3 e4 e5 e6 e7
    simp only [r755D126_p19, zero_add, add_zero] at hh
    rcases hh with hP | h5 | h4 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6
          + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
              * Real.sqrt (deltaY 2 y1 y2 y6 2 2) - sol0) + 0 > 0.712 ∨
        r755C135_p19 i y1 y2 y3 y4 y5 y6 ∨ deltaY 2 y1 y2 y6 2 2 < 100 ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hh := hex234_step_p19 h hdb (j := 2) (k := i) (by norm_num) hi
      y1 y2 y3 y4 y5 y6 y234 e1 e2 e3 e4 e5 e6 e7
    simp only [r755D126_p19, yOfX, zero_add, add_zero] at hh
    rw [nmud126] at hh
    rcases hh with hP | h5 | h4 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6
          + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y2 * y2))
              * (1 / 14 * (deltaY 2 y1 y2 y6 2 2 - 16) + 2 * 2) - sol0) + 0 > 0.712 ∨
        r755C135_p19 i y1 y2 y3 y4 y5 y6 ∨ (deltaY 2 y1 y2 y6 2 2 < 16 ∨ deltaY 2 y1 y2 y6 2 2 > 100) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hh := hex234_step_p19 h hdb (j := 3) (k := i) (by norm_num) hi
      y1 y2 y3 y4 y5 y6 y234 e1 e2 e3 e4 e5 e6 e7
    simp only [r755D126_p19, yOfX, zero_add, add_zero] at hh
    rw [nmudLs126] at hh
    rcases hh with hP | h5 | h4 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52)]
      (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6
          + (0 - sol0) + 0 > 0.712 ∨
        r755C135_p19 i y1 y2 y3 y4 y5 y6 ∨ (deltaY 2 y1 y2 y6 2 2 < 0 ∨ deltaY 2 y1 y2 y6 2 2 > 16) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7
    have hh := hex234_step_p19 h hdb (j := 4) (k := i) (by norm_num) hi
      y1 y2 y3 y4 y5 y6 y234 e1 e2 e3 e4 e5 e6 e7
    simp only [r755D126_p19, zero_add, add_zero] at hh
    rcases hh with hP | h5 | h4 | hb2
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr hb2))
  intro d1 d2 d3 d4 d5 d6 d7 d8
  exact terminal_hex_126_reduction_p19 h y1 y2 y3 y4 y5 y6 y234 y126
    (taum y1 y2 y3 y4 y5 y6 + taum y234 y2 y3 y4 2 2
          + r755D135_p19 i y1 y2 y3 y4 y5 y6) 0
    (r755C135_p19 i y1 y2 y3 y4 y5 y6)
    ((deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0))
    h0c h1c h2c h3c h4c d1 d2 d3 d4 d5 d6 d7 d8

/-- 135 step of the four-term chain (top layer): `f1 = taum(y126) +
taum(y1..y6) + taum(y234)`, `b1 = deltaY y126 … < 0`, `b2 = deltaY y234 … < 0 ∨
eulerA < 0`; its five antecedents are the 126 steps over the `i135` slot. -/
theorem hex135_step_p19 (h : mainNonlinearTerminalV11_p18)
    (hdb : ∀ i j k : ℕ, i ≤ 4 → j ≤ 4 → k ≤ 4 →
      ∀ y1 y2 y3 y4 y5 y6 : ℝ,
        ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
            (3.01, y5, 3.915), (3.01, y6, 3.915)]
          (r755Body_p19 i j k 0 0 True (yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)
            False False y1 y2 y3 y4 y5 y6))
    (y1 y2 y3 y4 y5 y6 y234 y126 y135 : ℝ) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52),
        (2, y135, 2.52)]
      ((taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2) + taum y135 y1 y3 y5 2 2 > 0.712 ∨
        (deltaY y135 y1 y3 y5 2 2 < 0 ∨ deltaY y126 y1 y2 y6 2 2 < 0) ∨
        (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
  have nmud135 : mud135xV1_p19 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
        * Real.sqrt (deltaY 2 y1 y3 y5 2 2) := by
    have h2 := nonfunctional_mud_135_p19 2 2 2 y1 y2 y3 y4 y5 y6
    rw [yOfX] at h2
    exact h2
  have nmudLs135 : mudLs135x_p19 4 10 2 2 2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)
    = muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
        * (1 / 14 * (deltaY 2 y1 y3 y5 2 2 - 16) + 2 * 2) := by
    rw [nonfunctional_mudLs_135_p19 y1 (y2 * y2) y3 (y4 * y4) y5 (y6 * y6),
      show (4 : ℝ) = 2 * 2 from by norm_num]
  have h0c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2
          + yOfX (flatTerm2_135x_p19 0 4 4) y1 y2 y3 y4 y5 y6 > 0.712 ∨
        deltaY y126 y1 y2 y6 2 2 < 0 ∨ (deltaY 2 y1 y3 y5 2 2 < 0 ∨ deltaY 2.52 y1 y3 y5 2 2 > 0) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7 e8
    have hh := hex126_step_p19 h hdb (i := 0) (by norm_num)
      y1 y2 y3 y4 y5 y6 y234 y126 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [r755D135_p19, zero_add, add_zero] at hh
    rcases hh with hP | h2 | hb2
    · exact Or.inl (by linarith)
    · rcases h2 with h6 | h7
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h1c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2
          + 0 > 0.712 ∨
        deltaY y126 y1 y2 y6 2 2 < 0 ∨ False ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7 e8
    have hh := hex126_step_p19 h hdb (i := 1) (by norm_num)
      y1 y2 y3 y4 y5 y6 y234 y126 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [r755D135_p19, zero_add, add_zero] at hh
    rcases hh with hP | h2 | hb2
    · exact Or.inl (by linarith)
    · rcases h2 with h6 | h7
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h2c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2
          + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
              * Real.sqrt (deltaY 2 y1 y3 y5 2 2) - sol0) > 0.712 ∨
        deltaY y126 y1 y2 y6 2 2 < 0 ∨ deltaY 2 y1 y3 y5 2 2 < 100 ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7 e8
    have hh := hex126_step_p19 h hdb (i := 2) (by norm_num)
      y1 y2 y3 y4 y5 y6 y234 y126 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [r755D135_p19, yOfX, zero_add, add_zero] at hh
    rw [nmud135] at hh
    rcases hh with hP | h2 | hb2
    · exact Or.inl (by linarith)
    · rcases h2 with h6 | h7
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h3c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2
          + (muY_p19 2 (Real.sqrt (y1 * y1)) (Real.sqrt (y3 * y3))
              * (1 / 14 * (deltaY 2 y1 y3 y5 2 2 - 16) + 2 * 2) - sol0) > 0.712 ∨
        deltaY y126 y1 y2 y6 2 2 < 0 ∨ (deltaY 2 y1 y3 y5 2 2 < 16 ∨ deltaY 2 y1 y3 y5 2 2 > 100) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7 e8
    have hh := hex126_step_p19 h hdb (i := 3) (by norm_num)
      y1 y2 y3 y4 y5 y6 y234 y126 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [r755D135_p19, yOfX, zero_add, add_zero] at hh
    rw [nmudLs135] at hh
    rcases hh with hP | h2 | hb2
    · exact Or.inl (by linarith)
    · rcases h2 with h6 | h7
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr hb2))
  have h4c : ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52)]
      (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2
          + (0 - sol0) > 0.712 ∨
        deltaY y126 y1 y2 y6 2 2 < 0 ∨ (deltaY 2 y1 y3 y5 2 2 < 0 ∨ deltaY 2 y1 y3 y5 2 2 > 16) ∨ (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
    intro e1 e2 e3 e4 e5 e6 e7 e8
    have hh := hex126_step_p19 h hdb (i := 4) (by norm_num)
      y1 y2 y3 y4 y5 y6 y234 y126 e1 e2 e3 e4 e5 e6 e7 e8
    simp only [r755D135_p19, zero_add, add_zero] at hh
    rcases hh with hP | h2 | hb2
    · exact Or.inl (by linarith)
    · rcases h2 with h6 | h7
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr hb2))
  intro d1 d2 d3 d4 d5 d6 d7 d8 d9
  exact terminal_hex_135_reduction_p19 h y1 y2 y3 y4 y5 y6 y234 y126 y135
    (taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6
          + taum y234 y2 y3 y4 2 2)
    (deltaY y126 y1 y2 y6 2 2 < 0)
    ((deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0))
    h0c h1c h2c h3c h4c d1 d2 d3 d4 d5 d6 d7 d8 d9

/-- **Four-term hex tower top** (HOL `Pent_hex.terminal_hex_taum` at the
`OCBICBY.hl:3040` consumption shape): the sum of the four `tau3`-ears is
`> 0.712` unless one of the `deltaY` escapes or the Euler-`A` escape fires.
This is the replacement of the (false) three-term + `ht4nn` split. -/
theorem terminal_hex_taum_four_p19 (h : mainNonlinearTerminalV11_p18)
    (y1 y2 y3 y4 y5 y6 y234 y126 y135 : ℝ) :
    ineqP19 [(2, y1, 2.52), (2, y2, 2.52), (2, y3, 2.52), (3.01, y4, 3.915),
        (3.01, y5, 3.915), (3.01, y6, 3.915), (2, y234, 2.52), (2, y126, 2.52),
        (2, y135, 2.52)]
      ((taum y126 y1 y2 y6 2 2 + taum y1 y2 y3 y4 y5 y6 + taum y135 y1 y3 y5 2 2
          + taum y234 y2 y3 y4 2 2) > 0.712 ∨
        (deltaY y135 y1 y3 y5 2 2 < 0 ∨ deltaY y126 y1 y2 y6 2 2 < 0) ∨
        (deltaY y234 y2 y3 y4 2 2 < 0 ∨ yOfX eulerAx_p19 y1 y2 y3 y4 y5 y6 < 0)) := by
  intro d1 d2 d3 d4 d5 d6 d7 d8 d9
  have hh := hex135_step_p19 h (r755_db_p19 h) y1 y2 y3 y4 y5 y6 y234 y126 y135
    d1 d2 d3 d4 d5 d6 d7 d8 d9
  rcases hh with hP | h2 | hb2
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr hb2)

end Kepler.Text
