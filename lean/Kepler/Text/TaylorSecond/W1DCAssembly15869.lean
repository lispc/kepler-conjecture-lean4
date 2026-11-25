/-
`Kepler.Text.TaylorSecond.W1DCAssembly15869` — assembly of the 25 certificate
boxes of wt1 case `15869` (lane `wt1-assembly-w1`, 2026-11-26).

Each `box_<ci>` composes the landed box module `Kepler.Text.TaylorSecond.W1DC_<id>`:
`b15869_cert_<ci>.Mem y4 y5 y6 → x ∈ W1DC_<id>.D` (floor/ceil bridge on the
`2^-200` grid) → `W1DC_<id>.Top_pos` → the mode bridge
`w1aF = w1F3 = w1F3Z/O = fTop` (`w1F3_eq_w1F3Z`/`w1F3_eq_w1F3O` +
`fTop_eq_w1F3Z`/`fTop_eq_w1F3O`, kink `2*h0 = 63/25`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks19

import Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_2

import Kepler.Text.TaylorSecond.W1DC_15869_LLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_2

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_2

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_3

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_4

import Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15869_RLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_RLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15869_RR_zero_0


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssembly15869

open Kepler.Text


/-- Case `15869` cert box `0` (mode `zero`). -/
private theorem box_0 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_0).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3282278147145474036901595575984424323206263971201617397425124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((260533032141259873 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3349283529071526350370849380623997140600378361554752331127370 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3259744451675458295364683681062850021319364576067050211644319 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_0.Top_pos x hD

/-- Case `15869` cert box `1` (mode `zero`). -/
private theorem box_1 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_1).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3282278147145474036901595575984424323206263971201617397425124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((260533032141259873 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3349283529071526350370849380623997140600378361554752331127370 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3259744451675458295364683681062850021319364576067050211644318 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((128567994058743339 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3305612814832936039645443177443374837594323164568514752685885 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LRR_zero_1.Top_pos x hD

/-- Case `15869` cert box `2` (mode `zero`). -/
private theorem box_2 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_2).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3282278147145474036901595575984424323206263971201617397425124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((260533032141259873 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3349283529071526350370849380623997140600378361554752331127370 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3259744451675458295364683681062850021319364576067050211644319 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_0.Top_pos x hD

/-- Case `15869` cert box `3` (mode `zero`). -/
private theorem box_3 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_3).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3282278147145474036901595575984424323206263971201617397425124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((260533032141259873 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3349283529071526350370849380623997140600378361554752331127370 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3259744451675458295364683681062850021319364576067050211644318 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((128567994058743339 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3305612814832936039645443177443374837594323164568514752685885 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((253567994058743339 : ℚ) / 125000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LRL_zero_1.Top_pos x hD

/-- Case `15869` cert box `4` (mode `zero`). -/
private theorem box_4 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_4).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3260067146082681609720573839884475934910427020417889172493768 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((128567994058743339 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3305612814832936039645443177443374837594323164568514752685885 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLRR_zero_0.Top_pos x hD

/-- Case `15869` cert box `5` (mode `zero`). -/
private theorem box_5 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_5).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((642444411864538193 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((4129473466986873008287620076080263288878926690667782494537514 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3236971617300331081205718034412895707748397550162318722809362 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_0.Top_pos x hD

/-- Case `15869` cert box `6` (mode `zero`). -/
private theorem box_6 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_6).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((642444411864538193 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((4129473466986873008287620076080263288878926690667782494537514 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3236971617300331081205718034412895707748397550162318722809361 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_1.Top_pos x hD

/-- Case `15869` cert box `7` (mode `zero`). -/
private theorem box_7 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_7).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4129473466986873008287620076080263288878926690667782494537513 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((642444411864538193 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((642444411864538193 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((642444411864538193 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLRLL_zero_2.Top_pos x hD

/-- Case `15869` cert box `8` (mode `zero`). -/
private theorem box_8 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_8).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3248257174822858793574851264109412726025372469191679044479152 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLRLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `9` (mode `zero`). -/
private theorem box_9 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_9).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2536664125759156211 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4076262089189359837682565532018046348137055970962063295749036 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3248257174822858793574851264109412726025372469191679044479152 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `10` (mode `zero`). -/
private theorem box_10 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_10).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4076262089189359837682565532018046348137055970962063295749035 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2536664125759156211 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3248257174822858793574851264109412726025372469191679044479152 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2536664125759156211 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2021395402534471977 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2536664125759156211 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLR_zero_1.Top_pos x hD

/-- Case `15869` cert box `11` (mode `zero`). -/
private theorem box_11 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_11).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4076350045408918483196547182795526378379295745396700328461177 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3231066631670419673132856746525364103305870274549213658802054 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3236971617300331081205718034412895707748397550162318722809362 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `12` (mode `zero`). -/
private theorem box_12 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_12).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4076350045408918483196547182795526378379295745396700328461177 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3231066631670419673132856746525364103305870274549213658802053 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3236971617300331081205718034412895707748397550162318722809362 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_1.Top_pos x hD

/-- Case `15869` cert box `13` (mode `zero`). -/
private theorem box_13 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_13).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4076350045408918483196547182795526378379295745396700328461177 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3236971617300331081205718034412895707748397550162318722809361 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((503593095711571227 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2536718861048965847 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLR_zero_2.Top_pos x hD

/-- Case `15869` cert box `14` (mode `zero`). -/
private theorem box_14 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_14).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((4062916958470786989584614849877123206138604691035250437971424 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((4010697701267235989 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3222471360094200112108390465603844654175138131057399664702403 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1003605913771032131 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3225465048563958417186788047109678026329554037573826552546846 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_0.Top_pos x hD

/-- Case `15869` cert box `15` (mode `zero`). -/
private theorem box_15 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_15).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((4062916958470786989584614849877123206138604691035250437971424 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3222471360094200112108390465603844654175138131057399664702402 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4010697701267235989 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3231066631670419673132856746525364103305870274549213658802054 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1003605913771032131 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3225465048563958417186788047109678026329554037573826552546846 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((4010697701267235989 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_1.Top_pos x hD

/-- Case `15869` cert box `16` (mode `zero`). -/
private theorem box_16 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_16).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((4062916958470786989584614849877123206138604691035250437971424 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3231066631670419673132856746525364103305870274549213658802054 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3225465048563958417186788047109678026329554037573826552546845 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1003605913771032131 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503605913771032131 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3237054008609936283289651909537030847614702087582067434490939 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1003605913771032131 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_2.Top_pos x hD

/-- Case `15869` cert box `17` (mode `zero`). -/
private theorem box_17 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_17).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_3.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4062916958470786989584614849877123206138604691035250437971423 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((317089857631120731 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((4076350045408918484803485227054516653921257837737862930983381 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3231066631670419673132856746525364103305870274549213658802054 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503605913771032131 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3237054008609936283289651909537030847614702087582067434490939 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((632089857631120731 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_3.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_3.Top_pos x hD

/-- Case `15869` cert box `18` (mode `zero`). -/
private theorem box_18 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_18).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_4.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((317089857631120731 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((4076350045408918484803485227054516653921257837737862930983381 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3231066631670419673132856746525364103305870274549213658802053 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((503605913771032131 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3237054008609936283289651909537030847614702087582067434490939 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2010697701267235989 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_4.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLL_zero_4.Top_pos x hD

/-- Case `15869` cert box `19` (mode `zero`). -/
private theorem box_19 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_19).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((317089857631120731 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((4076350045408918484803485227054516653921257837737862930983381 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1010697701267235989 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3248257174822858795181789308368403001567334561532841647001356 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3237054008609936281682713865278040572072739995240904831968735 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2014423655084128523 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((253593095711571227 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3260067146082681611327511884143466210452389112759051775015972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2014423655084128523 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLLLLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `20` (mode `zero`). -/
private theorem box_20 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_20).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((4042566705587604549 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3248077117831727294796228902462869901896316025554182835275040 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3260067146082681609720573839884475934910427020417889172493768 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((128567994058743339 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3305612814832936039645443177443374837594323164568514752685885 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `21` (mode `zero`). -/
private theorem box_21 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_21).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3248077117831727294796228902462869901896316025554182835275039 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4042566705587604549 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3260067146082681609720573839884475934910427020417889172493768 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((128567994058743339 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3305612814832936039645443177443374837594323164568514752685885 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((4042566705587604549 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((405748953138513963 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_LLLR_zero_1.Top_pos x hD

/-- Case `15869` cert box `22` (mode `zero`). -/
private theorem box_22 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_22).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_RLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1276664125759156211 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4103040306846064180999386591336362937918160397591488646538604 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3305612814832936038038505133184384562052361072227352150163681 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1056316867386391781 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3394871521991343194643680404485842097056016083859618626213724 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_RLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_RLL_zero_0.Top_pos x hD

/-- Case `15869` cert box `23` (mode `zero`). -/
private theorem box_23 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_23).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_RLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4103040306846064179392448547077372662376198305250326044016400 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2042566705587604549 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3282278147145474038508533620243414598748226063542779999947328 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3305612814832936038038505133184384562052361072227352150163681 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1056316867386391781 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3394871521991343194643680404485842097056016083859618626213724 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2553328251518312421 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_RLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_RLR_zero_0.Top_pos x hD

/-- Case `15869` cert box `24` (mode `zero`). -/
private theorem box_24 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15869_cert_24).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15869_RR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2586227043397993123 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127681837182791605083153915381655076085238945058627 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3282278147145474036901595575984424323206263971201617397425124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((260533032141259873 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3349283529071526350370849380623997140600378361554752331127370 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3305612814832936038038505133184384562052361072227352150163681 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1056316867386391781 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3394871521991343194643680404485842097056016083859618626213724 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((510641676396901137 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2057087904939893423 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15869_RR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15869_RR_zero_0.Top_pos x hD

/-- Every point of the `certs15869` cover has `w1aF > 0`. -/
theorem case_pos {y4 y5 y6 : ℝ}
    (h : ∃ b : Kepler.Text.TaylorSecond.Box3, b ∈ Kepler.Text.TaylorSecond.certs15869 ∧ b.Mem y4 y5 y6) :
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  obtain ⟨b, hb, hbmem⟩ := h
  simp only [Kepler.Text.TaylorSecond.certs15869, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using box_0 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_1 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_2 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_3 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_4 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_5 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_6 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_7 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_8 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_9 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_10 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_11 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_12 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_13 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_14 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_15 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_16 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_17 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_18 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_19 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_20 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_21 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_22 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_23 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_24 ![y4, y5, y6] (by simpa using hbmem)

#print axioms case_pos

end W1DCAssembly15869
end Kepler.Text.TaylorSecond
