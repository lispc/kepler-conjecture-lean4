/-
`Kepler.Text.TaylorSecond.W1DCAssembly15873` — assembly of the 62 certificate
boxes of wt1 case `15873` (lane `wt1-assembly-w1`, 2026-11-26).

Each `box_<ci>` composes the landed box module `Kepler.Text.TaylorSecond.W1DC_<id>`:
`b15873_cert_<ci>.Mem y4 y5 y6 → x ∈ W1DC_<id>.D` (floor/ceil bridge on the
`2^-200` grid) → `W1DC_<id>.Top_pos` → the mode bridge
`w1aF = w1F3 = w1F3Z/O = fTop` (`w1F3_eq_w1F3Z`/`w1F3_eq_w1F3O` +
`fTop_eq_w1F3Z`/`fTop_eq_w1F3O`, kink `2*h0 = 63/25`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks19

import Kepler.Text.TaylorSecond.W1DC_15873_LRRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_LRRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_LRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_LLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_RLLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_RLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_RLRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_RRLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15873_RRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b1

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b2

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b3

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b4

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b5

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b6

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_1

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_2

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b1

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b2

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b3

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_2


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssembly15873

open Kepler.Text


/-- Case `15873` cert box `0` (mode `one`). -/
private theorem box_0 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_0).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRRL_one_0.Top_pos x hD

/-- Case `15873` cert box `1` (mode `zero`). -/
private theorem box_1 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_1).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRRL_zero_0.Top_pos x hD

/-- Case `15873` cert box `2` (mode `one`). -/
private theorem box_2 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_2).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3510460874007134060438375719717885284776407433355397202668280 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_0.Top_pos x hD

/-- Case `15873` cert box `3` (mode `one`). -/
private theorem box_3 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_3).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3510460874007134060438375719717885284776407433355397202668279 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRRR_one_1.Top_pos x hD

/-- Case `15873` cert box `4` (mode `zero`). -/
private theorem box_4 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_4).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `5` (mode `one`). -/
private theorem box_5 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_5).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3314611029588618352746093279808905312537520549266499332518499 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_0.Top_pos x hD

/-- Case `15873` cert box `6` (mode `one`). -/
private theorem box_6 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_6).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3314611029588618352746093279808905312537520549266499332518498 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLR_one_1.Top_pos x hD

/-- Case `15873` cert box `7` (mode `zero`). -/
private theorem box_7 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_7).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `8` (mode `one`). -/
private theorem box_8 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_8).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_one_0.Top_pos x hD

/-- Case `15873` cert box `9` (mode `zero`). -/
private theorem box_9 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_9).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLLL_zero_0.Top_pos x hD

/-- Case `15873` cert box `10` (mode `one`). -/
private theorem box_10 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_10).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_one_0.Top_pos x hD

/-- Case `15873` cert box `11` (mode `zero`). -/
private theorem box_11 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_11).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LRLLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `12` (mode `one`). -/
private theorem box_12 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_12).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3510460874007134060438375719717885284776407433355397202668280 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_0.Top_pos x hD

/-- Case `15873` cert box `13` (mode `one`). -/
private theorem box_13 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_13).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3510460874007134060438375719717885284776407433355397202668279 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRR_one_1.Top_pos x hD

/-- Case `15873` cert box `14` (mode `zero`). -/
private theorem box_14 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_14).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `15` (mode `one`). -/
private theorem box_15 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_15).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1092683443924791857 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3511749192749366192033859271796436575893180983833901319568376 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_one_0.Top_pos x hD

/-- Case `15873` cert box `16` (mode `zero`). -/
private theorem box_16 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_16).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1092683443924791857 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3511749192749366192033859271796436575893180983833901319568376 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRLL_zero_0.Top_pos x hD

/-- Case `15873` cert box `17` (mode `one`). -/
private theorem box_17 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_17).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3511749192749366190426921227537446300351218891492738717046172 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_one_0.Top_pos x hD

/-- Case `15873` cert box `18` (mode `zero`). -/
private theorem box_18 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_18).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3511749192749366190426921227537446300351218891492738717046172 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLRLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `19` (mode `one`). -/
private theorem box_19 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_19).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((16994285809868563 : ℚ) / 8000000000000000) : ℚ) : ℝ) ≤
          (((3413595550361062411105935942573115052926837394774340463529752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_one_0.Top_pos x hD

/-- Case `15873` cert box `20` (mode `zero`). -/
private theorem box_20 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_20).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((16994285809868563 : ℚ) / 8000000000000000) : ℚ) : ℝ) ≤
          (((3413595550361062411105935942573115052926837394774340463529752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLRL_zero_0.Top_pos x hD

/-- Case `15873` cert box `21` (mode `one`). -/
private theorem box_21 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_21).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3413595550361062409498997898314124777384875302433177861007548 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_one_0.Top_pos x hD

/-- Case `15873` cert box `22` (mode `zero`). -/
private theorem box_22 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_22).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3413595550361062409498997898314124777384875302433177861007548 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `23` (mode `one`). -/
private theorem box_23 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_23).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3413595550361062409498997898314124777384875302433177861007548 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_one_0.Top_pos x hD

/-- Case `15873` cert box `24` (mode `zero`). -/
private theorem box_24 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_24).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3413595550361062409498997898314124777384875302433177861007548 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1062142863116785187 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `25` (mode `one`). -/
private theorem box_25 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_25).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((16994285809868563 : ℚ) / 8000000000000000) : ℚ) : ℝ) ≤
          (((3413595550361062411105935942573115052926837394774340463529752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLL_one_0.Top_pos x hD

/-- Case `15873` cert box `26` (mode `one`). -/
private theorem box_26 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_26).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((16994285809868563 : ℚ) / 8000000000000000) : ℚ) : ℝ) ≤
          (((3413595550361062411105935942573115052926837394774340463529752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_one_0.Top_pos x hD

/-- Case `15873` cert box `27` (mode `zero`). -/
private theorem box_27 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_27).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((16994285809868563 : ℚ) / 8000000000000000) : ℚ) : ℝ) ≤
          (((3413595550361062411105935942573115052926837394774340463529752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLLLLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `28` (mode `one`). -/
private theorem box_28 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_28).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_one_0.Top_pos x hD

/-- Case `15873` cert box `29` (mode `zero`). -/
private theorem box_29 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_29).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `30` (mode `one`). -/
private theorem box_30 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_30).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2225926538956964881 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3576926039175688273711463116146371350931089059408477867656791 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_0.Top_pos x hD

/-- Case `15873` cert box `31` (mode `one`). -/
private theorem box_31 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_31).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3576926039175688273711463116146371350931089059408477867656790 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2225926538956964881 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2225926538956964881 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_one_1.Top_pos x hD

/-- Case `15873` cert box `32` (mode `zero`). -/
private theorem box_32 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_32).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_LLLRL_zero_0.Top_pos x hD

/-- Case `15873` cert box `33` (mode `one`). -/
private theorem box_33 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_33).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLLR_one_0.Top_pos x hD

/-- Case `15873` cert box `34` (mode `zero`). -/
private theorem box_34 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_34).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLLR_zero_0.Top_pos x hD

/-- Case `15873` cert box `35` (mode `one`). -/
private theorem box_35 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_35).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3695917920740807035185576936687014761731548207681244142521586 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_0.Top_pos x hD

/-- Case `15873` cert box `36` (mode `one`). -/
private theorem box_36 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_36).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLLL_one_1.Top_pos x hD

/-- Case `15873` cert box `37` (mode `zero`). -/
private theorem box_37 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_37).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLLL_zero_0.Top_pos x hD

/-- Case `15873` cert box `38` (mode `one`). -/
private theorem box_38 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_38).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3872483074104485483762563847600462116610353069830531192583300 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_0.Top_pos x hD

/-- Case `15873` cert box `39` (mode `one`). -/
private theorem box_39 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_39).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3872483074104485483762563847600462116610353069830531192583299 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRR_one_1.Top_pos x hD

/-- Case `15873` cert box `40` (mode `zero`). -/
private theorem box_40 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_40).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3496675183019841619708434305859801893694935470686126224387405 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2275866769348891939 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3657176895331534927714491926432940808167242648130829510926176 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2175986308565037823 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `41` (mode `one`). -/
private theorem box_41 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_41).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3872483074104485483762563847600462116610353069830531192583300 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_0.Top_pos x hD

/-- Case `15873` cert box `42` (mode `one`). -/
private theorem box_42 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_42).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3872483074104485483762563847600462116610353069830531192583299 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4819704266682178589 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRL_one_1.Top_pos x hD

/-- Case `15873` cert box `43` (mode `zero`). -/
private theorem box_43 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_43).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RLRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3328442853248774984362277734465035951825398697263847784632583 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((8499946517832179 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3496675183019841621315372350118792169236897563027288826909609 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2071295072725485677 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RLRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RLRL_zero_0.Top_pos x hD

/-- Case `15873` cert box `44` (mode `one`). -/
private theorem box_44 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_44).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3695917920740807035185576936687014761731548207681244142521586 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_0.Top_pos x hD

/-- Case `15873` cert box `45` (mode `one`). -/
private theorem box_45 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_45).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLL_one_1.Top_pos x hD

/-- Case `15873` cert box `46` (mode `zero`). -/
private theorem box_46 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_46).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2371544367831263557 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3810924868316194111618669757894639523881267784824102002174871 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLL_zero_0.Top_pos x hD

/-- Case `15873` cert box `47` (mode `one`). -/
private theorem box_47 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_47).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRR_one_0.Top_pos x hD

/-- Case `15873` cert box `48` (mode `zero`). -/
private theorem box_48 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_48).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3657176895331534926107553882173950532625280555789666908403972 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1137933384674445969 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRR_zero_0.Top_pos x hD

/-- Case `15873` cert box `49` (mode `one`). -/
private theorem box_49 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_49).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3695917920740807035185576936687014761731548207681244142521586 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b1.Top_pos x hD

/-- Case `15873` cert box `50` (mode `one`). -/
private theorem box_50 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_50).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) ≤
          (((3884815476199281487620566322110909691580528632433028756600306 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b2.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b2.Top_pos x hD

/-- Case `15873` cert box `51` (mode `one`). -/
private theorem box_51 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_51).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b3.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4004094977807002572339065870186362461921488451632321464279390 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3884815476199281487620566322110909691580528632433028756600305 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b3.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b3.Top_pos x hD

/-- Case `15873` cert box `52` (mode `one`). -/
private theorem box_52 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_52).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b4.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004094977807002572339065870186362461921488451632321464279389 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3884815476199281487620566322110909691580528632433028756600305 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) ≤
          (((3741088992433704569544120872780379567836232433650175508331222 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b4.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b4.Top_pos x hD

/-- Case `15873` cert box `53` (mode `one`). -/
private theorem box_53 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_53).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b5.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004094977807002572339065870186362461921488451632321464279389 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3884815476199281487620566322110909691580528632433028756600305 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) ≤
          (((3921760780140825176424983626348539913201140102408073435074125 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3741088992433704569544120872780379567836232433650175508331221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b5.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b5.Top_pos x hD

/-- Case `15873` cert box `54` (mode `one`). -/
private theorem box_54 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_54).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b6.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004094977807002572339065870186362461921488451632321464279389 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ) ≤
          (((4026789424669829033352405171443046110138719997982479704619429 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3921760780140825176424983626348539913201140102408073435074124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3741088992433704569544120872780379567836232433650175508331221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((498350884418000923 : ℚ) / 200000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b6.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_0__b6.Top_pos x hD

/-- Case `15873` cert box `55` (mode `one`). -/
private theorem box_55 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_55).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026789424669829033352405171443046110138719997982479704619428 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3921760780140825176424983626348539913201140102408073435074124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3741088992433704569544120872780379567836232433650175508331221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((18737123272307375887 : ℚ) / 8000000000000000000) : ℚ) : ℝ) ≤
          (((3763674528280153336723392840827061970888574546634641191236040 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_1.Top_pos x hD

/-- Case `15873` cert box `56` (mode `one`). -/
private theorem box_56 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_56).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026789424669829033352405171443046110138719997982479704619428 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3921760780140825176424983626348539913201140102408073435074124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3763674528280153336723392840827061970888574546634641191236039 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((18737123272307375887 : ℚ) / 8000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1002350884418000923 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((18737123272307375887 : ℚ) / 8000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_2.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_one_2.Top_pos x hD

/-- Case `15873` cert box `57` (mode `zero`). -/
private theorem box_57 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_57).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3695917920740807035185576936687014761731548207681244142521586 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b1.Top_pos x hD

/-- Case `15873` cert box `58` (mode `zero`). -/
private theorem box_58 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_58).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3810924868316194110011731713635649248339305692482939399652667 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) ≤
          (((3884815476199281487620566322110909691580528632433028756600306 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((592886091957815889 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b2.Top_pos x hD

/-- Case `15873` cert box `59` (mode `zero`). -/
private theorem box_59 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_59).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b3.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3884815476199281487620566322110909691580528632433028756600305 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) ≤
          (((3741088992433704569544120872780379567836232433650175508331222 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b3.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_0__b3.Top_pos x hD

/-- Case `15873` cert box `60` (mode `zero`). -/
private theorem box_60 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_60).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3884815476199281487620566322110909691580528632433028756600305 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) ≤
          (((3921760780140825176424983626348539913201140102408073435074125 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3741088992433704569544120872780379567836232433650175508331221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((967010642402381409 : ℚ) / 400000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_1.Top_pos x hD

/-- Case `15873` cert box `61` (mode `zero`). -/
private theorem box_61 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15873_cert_61).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3921760780140825176424983626348539913201140102408073435074124 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3741088992433704569544120872780379567836232433650175508331221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((9762070900373194023 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((9312341582301235483 : ℚ) / 4000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15873_RRLR_zero_2.Top_pos x hD

/-- Every point of the `certs15873` cover has `w1aF > 0`. -/
theorem case_pos {y4 y5 y6 : ℝ}
    (h : ∃ b : Kepler.Text.TaylorSecond.Box3, b ∈ Kepler.Text.TaylorSecond.certs15873 ∧ b.Mem y4 y5 y6) :
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  obtain ⟨b, hb, hbmem⟩ := h
  simp only [Kepler.Text.TaylorSecond.certs15873, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simpa using box_25 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_26 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_27 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_28 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_29 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_30 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_31 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_32 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_33 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_34 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_35 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_36 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_37 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_38 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_39 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_40 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_41 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_42 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_43 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_44 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_45 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_46 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_47 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_48 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_49 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_50 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_51 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_52 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_53 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_54 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_55 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_56 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_57 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_58 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_59 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_60 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_61 ![y4, y5, y6] (by simpa using hbmem)

#print axioms case_pos

end W1DCAssembly15873
end Kepler.Text.TaylorSecond
