/-
Kepler.Text.NliQitnpea — lane qitnpea-w1 (2026-11-15): pure-algebra close of the
cone-interior debt `nliRestQITNPEA4003532128a` (Assembly.lean:1394; bank
`PackingAuto21.lean:460`).

Box `[2hmin,2hplus] × [2,√8] × [√2,√2]³ × [2,√8]`; conclusion
`delta4Y > 25 ∨ deltaY > 0.14 ∨ deltaY < 0`.

Reduction (PICKS PICK-2, `logs/qit4003.py`): the two-sided `√2` slots force
`y3 = y4 = y5 = √2`, hence with `x_i = y_i²` we have `x3 = x4 = x5 = 2` and

  `delta4Y = x1·(x2 + x6 − x1)`,
  `deltaY  = −2(x1²+x2²+x6²) + 4(x1x2+x1x6+x2x6) − x1x2x6`
           `= (x2x6)·(8−x1) − 2(x1−(x2+x6))²`.

Residual region `{delta4Y ≤ 25}` (the `deltaY < 0` branch is handled first):
with `u = 8−x1 ∈ [8−7.02674064, 8−6.0650528]` and `t = x2+x6−x1`,

  `deltaY ≥ (4(x2+x6)−16)(8−x1) − 2(x1−(x2+x6))²`   (`x2,x6 ≥ 4`)
         `= 16u − 4u² + 4tu − 2t²`,
  `u ≤ t`   (`x2+x6 ≥ 8`),      `t(8−u) ≤ 25`   (`delta4Y ≤ 25`),
  `t ≤ 3.558 + 0.587·(u − 0.97325936)`  (chord above the convex curve `25/(8−u)`),

and `16u − 4u² + 4tu − 2t²` is concave in `t` with vertex at `t = u`, so it is
`≥ 16u − 4u² + 4Tu − 2T²`, whose minimum on the `u`-interval is `0.3159…` at
`u = 0.97325936` (`> 0.14`). No certificates, no `sorry`/`axiom`/`native_decide`.
-/
import Kepler.Text.PackingAuto21
import Kepler.NliBanks3

set_option maxHeartbeats 4000000

namespace Kepler.NliQitnpea

open Kepler.Text
open Kepler.NliBanks3

theorem nliRestQITNPEA4003532128a_proved : bank_QITNPEA4003532128a := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hy3 : y3 = Real.sqrt 2 := le_antisymm h3h h3l
  have hy4 : y4 = Real.sqrt 2 := le_antisymm h4h h4l
  have hy5 : y5 = Real.sqrt 2 := le_antisymm h5h h5l
  have h3s : y3 * y3 = 2 := by rw [hy3, ← pow_two, Real.sq_sqrt (by norm_num)]
  have h4s : y4 * y4 = 2 := by rw [hy4, ← pow_two, Real.sq_sqrt (by norm_num)]
  have h5s : y5 * y5 = 2 := by rw [hy5, ← pow_two, Real.sq_sqrt (by norm_num)]
  have dY : deltaY y1 y2 y3 y4 y5 y6
      = -2 * ((y1 * y1) ^ 2 + (y2 * y2) ^ 2 + (y6 * y6) ^ 2)
        + 4 * ((y1 * y1) * (y2 * y2) + (y1 * y1) * (y6 * y6) +
            (y2 * y2) * (y6 * y6))
        - (y1 * y1) * (y2 * y2) * (y6 * y6) := by
    unfold deltaY deltaX
    rw [h3s, h4s, h5s]
    ring
  have dY4 : delta4Y y1 y2 y3 y4 y5 y6 =
      (y1 * y1) * (y2 * y2 + y6 * y6 - y1 * y1) := by
    unfold delta4Y yOfX deltaX4
    rw [h3s, h4s, h5s]
    ring
  by_cases hneg : deltaY y1 y2 y3 y4 y5 y6 < 0
  · exact Or.inr (Or.inr hneg)
  · by_cases hbig : 25 < delta4Y y1 y2 y3 y4 y5 y6
    · exact Or.inl hbig
    · push Not at hneg hbig
      -- ## box bounds in x-space
      have hy1pos : (0:ℝ) ≤ y1 := by
        have hm : (0:ℝ) < hminus := by linarith [mi_hminus_prop.1]
        linarith
      have hx1l : (6.0650528:ℝ) ≤ y1 * y1 := sq_ge_hminus y1 h1l
      have hx1h : y1 * y1 ≤ 7.02674064 := sq_le_hplus y1 hy1pos h1h
      have hx2l : (4:ℝ) ≤ y2 * y2 := sq_ge_4 y2 h2l
      have hy2pos : (0:ℝ) ≤ y2 := by linarith
      have hx2h : y2 * y2 ≤ 8 := sq_le_8 y2 hy2pos h2h
      have hx6l : (4:ℝ) ≤ y6 * y6 := sq_ge_4 y6 h6l
      have hy6pos : (0:ℝ) ≤ y6 := by linarith
      have hx6h : y6 * y6 ≤ 8 := sq_le_8 y6 hy6pos h6h
      set x1 : ℝ := y1 * y1 with hx1def
      set x2 : ℝ := y2 * y2 with hx2def
      set x6 : ℝ := y6 * y6 with hx6def
      have hd4 : x1 * (x2 + x6 - x1) ≤ 25 := by
        rw [dY4] at hbig
        exact hbig
      -- ## the two working variables u = 8−x1, t = x2+x6−x1
      obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 8 - x1 := ⟨8 - x1, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x2 + x6 - x1 := ⟨x2 + x6 - x1, rfl⟩
      obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 3.558 + 0.587 * (u - 0.97325936) :=
        ⟨3.558 + 0.587 * (u - 0.97325936), rfl⟩
      have hx1pos : (0:ℝ) < x1 := by linarith
      have h8u : (0:ℝ) < 8 - u := by rw [hu]; linarith
      have hu0 : (0.97325936:ℝ) ≤ u := by rw [hu]; linarith
      have hu1 : u ≤ 1.9349472 := by rw [hu]; linarith
      -- ## δ ≥ g(u,t) = 16u − 4u² + 4tu − 2t²  (x2,x6 ≥ 4)
      have hp : 4 * (x2 + x6) - 16 ≤ x2 * x6 := by
        have h : (0:ℝ) ≤ (x2 - 4) * (x6 - 4) := mul_nonneg (by linarith) (by linarith)
        nlinarith [h]
      have hstep1 : 16 * u - 4 * u ^ 2 + 4 * t * u - 2 * t ^ 2
          ≤ -2 * (x1 ^ 2 + x2 ^ 2 + x6 ^ 2) + 4 * (x1 * x2 + x1 * x6 + x2 * x6)
            - x1 * x2 * x6 := by
        have e1 : -2 * (x1 ^ 2 + x2 ^ 2 + x6 ^ 2) + 4 * (x1 * x2 + x1 * x6 + x2 * x6)
            - x1 * x2 * x6 = (x2 * x6) * (8 - x1) - 2 * (x1 - (x2 + x6)) ^ 2 := by
          ring
        have e2 : (4 * (x2 + x6) - 16) * (8 - x1) ≤ (x2 * x6) * (8 - x1) :=
          mul_le_mul_of_nonneg_right hp (by linarith : (0:ℝ) ≤ 8 - x1)
        have e3 : (4 * (x2 + x6) - 16) * (8 - x1) - 2 * (x1 - (x2 + x6)) ^ 2
            = 16 * u - 4 * u ^ 2 + 4 * t * u - 2 * t ^ 2 := by
          rw [hu, ht]; ring
        linarith
      -- ## δ4 ≤ 25 gives (8−u)·t ≤ 25, hence t ≤ T (chord above the convex curve)
      have ht25 : (8 - u) * t ≤ 25 := by
        have e : (8 - u) * t = x1 * (x2 + x6 - x1) := by rw [hu, ht]; ring
        linarith
      have hline : 0 ≤ (8 - u) * T - 25 := by
        rw [hT]
        have h1 : (0:ℝ) ≤ u - 0.97325936 := by linarith
        have h2 : (0:ℝ) ≤ 1.9349472 - u := by linarith
        nlinarith [mul_nonneg h1 h2]
      have htT : t ≤ T := by
        by_contra hcon
        push Not at hcon
        have hlt : (8 - u) * (T - t) < 0 := mul_neg_of_pos_of_neg h8u (by linarith)
        nlinarith [ht25, hline, hlt]
      have htu : u ≤ t := by rw [hu, ht]; linarith
      -- ## concavity in t: g(u,t) ≥ g(u,T) since u ≤ t ≤ T
      have hg : 16 * u - 4 * u ^ 2 + 4 * T * u - 2 * T ^ 2
          ≤ 16 * u - 4 * u ^ 2 + 4 * t * u - 2 * t ^ 2 := by
        have h1 : (0:ℝ) ≤ T - t := by linarith
        have h2 : (0:ℝ) ≤ T + t - 2 * u := by linarith
        nlinarith [mul_nonneg h1 h2]
      -- ## the concave quadratic in u stays above its endpoint minimum 0.3159…
      have hq : (0.14:ℝ) < 16 * u - 4 * u ^ 2 + 4 * T * u - 2 * T ^ 2 := by
        rw [hT]
        have h1 : (0:ℝ) ≤ u - 0.97325936 := by linarith
        have h2 : (0:ℝ) ≤ 1.9349472 - u := by linarith
        have hq0 : (0.3:ℝ) < 16 * 0.97325936 - 4 * (0.97325936:ℝ) ^ 2
            + 4 * 3.558 * 0.97325936 - 2 * 3.558 ^ 2 := by norm_num
        have hq1 : (13:ℝ) < 16 * 1.9349472 - 4 * (1.9349472:ℝ) ^ 2
            + 4 * 4.12251076208 * 1.9349472 - 2 * 4.12251076208 ^ 2 := by norm_num
        nlinarith [hq0, hq1, mul_nonneg h1 h2]
      refine Or.inr (Or.inl ?_)
      rw [dY]
      linarith

end Kepler.NliQitnpea
