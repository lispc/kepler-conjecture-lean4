/-
`Kepler.Text.TaylorSecond.W1DCAssembly15874` — assembly of the 41 certificate
boxes of wt1 case `15874` (lane `wt1-assembly-w1`, 2026-11-26).

Each `box_<ci>` composes the landed box module `Kepler.Text.TaylorSecond.W1DC_<id>`:
`b15874_cert_<ci>.Mem y4 y5 y6 → x ∈ W1DC_<id>.D` (floor/ceil bridge on the
`2^-200` grid) → `W1DC_<id>.Top_pos` → the mode bridge
`w1aF = w1F3 = w1F3Z/O = fTop` (`w1F3_eq_w1F3Z`/`w1F3_eq_w1F3O` +
`fTop_eq_w1F3Z`/`fTop_eq_w1F3O`, kink `2*h0 = 63/25`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks19

import Kepler.Text.TaylorSecond.W1DC_15874_LRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLRLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_2

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_3

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_4

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_2

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLLR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_2

import Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_RL_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_RL_one_1

import Kepler.Text.TaylorSecond.W1DC_15874_RL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15874_RR_one_0

import Kepler.Text.TaylorSecond.W1DC_15874_RR_zero_0


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssembly15874

open Kepler.Text


/-- Case `15874` cert box `0` (mode `one`). -/
private theorem box_0 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_0).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3511749192749366190426921227537446300351218891492738717046172 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LRR_one_0.Top_pos x hD

/-- Case `15874` cert box `1` (mode `zero`). -/
private theorem box_1 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_1).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3511749192749366190426921227537446300351218891492738717046172 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2185366887849583713 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LRR_zero_0.Top_pos x hD

/-- Case `15874` cert box `2` (mode `one`). -/
private theorem box_2 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_2).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((4071295072726240037 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3271159470883983872614634565525809495696891582125136052142863 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1092683443924791857 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3511749192749366192033859271796436575893180983833901319568376 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_0.Top_pos x hD

/-- Case `15874` cert box `3` (mode `one`). -/
private theorem box_3 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_3).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271159470883983872614634565525809495696891582125136052142862 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4071295072726240037 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1092683443924791857 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3511749192749366192033859271796436575893180983833901319568376 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((4071295072726240037 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LRL_one_1.Top_pos x hD

/-- Case `15874` cert box `4` (mode `zero`). -/
private theorem box_4 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_4).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((1092683443924791857 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3511749192749366192033859271796436575893180983833901319568376 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LRL_zero_0.Top_pos x hD

/-- Case `15874` cert box `5` (mode `one`). -/
private theorem box_5 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_5).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLRR_one_0.Top_pos x hD

/-- Case `15874` cert box `6` (mode `zero`). -/
private theorem box_6 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_6).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLRR_zero_0.Top_pos x hD

/-- Case `15874` cert box `7` (mode `one`). -/
private theorem box_7 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_7).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLRLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLRLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLRLL_one_0.Top_pos x hD

/-- Case `15874` cert box `8` (mode `one`). -/
private theorem box_8 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_8).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_one_0.Top_pos x hD

/-- Case `15874` cert box `9` (mode `zero`). -/
private theorem box_9 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_9).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLRLR_zero_0.Top_pos x hD

/-- Case `15874` cert box `10` (mode `one`). -/
private theorem box_10 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_10).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3242897252627417844241880725564761174378292545589106499980994 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3239642599520623946607768622906337210818544087776995282638222 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_0.Top_pos x hD

/-- Case `15874` cert box `11` (mode `one`). -/
private theorem box_11 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_11).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3242897252627417844241880725564761174378292545589106499980994 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3239642599520623946607768622906337210818544087776995282638221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_one_1.Top_pos x hD

/-- Case `15874` cert box `12` (mode `zero`). -/
private theorem box_12 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_12).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3242897252627417844241880725564761174378292545589106499980994 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2018059914763434371 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLR_zero_0.Top_pos x hD

/-- Case `15874` cert box `13` (mode `one`). -/
private theorem box_13 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_13).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2505996599427186973 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4026981274403204104607767969039084150334597259879559052192425 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3239642599520623946607768622906337210818544087776995282638222 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2505996599427186973 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_0.Top_pos x hD

/-- Case `15874` cert box `14` (mode `one`). -/
private theorem box_14 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_14).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2505996599427186973 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4026981274403204104607767969039084150334597259879559052192425 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3239642599520623946607768622906337210818544087776995282638221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2505996599427186973 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLL_one_1.Top_pos x hD

/-- Case `15874` cert box `15` (mode `one`). -/
private theorem box_15 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_15).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026981274403204103000829924780093874792635167538396449670221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3239745064927179196779762664966799346683961431237267666344145 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2016098303541707263 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2016098303541707263 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_one_0.Top_pos x hD

/-- Case `15874` cert box `16` (mode `zero`). -/
private theorem box_16 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_16).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3239745064927179196779762664966799346683961431237267666344145 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2016098303541707263 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2016098303541707263 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRR_zero_0.Top_pos x hD

/-- Case `15874` cert box `17` (mode `one`). -/
private theorem box_17 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_17).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026981274403204103000829924780093874792635167538396449670221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4038232572967929798683287198739911816574293355935517197314845 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3228386670572699198466371477253038327482330312747927386552975 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3226810576722579874735312446954057413635164755572007969734551 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_0.Top_pos x hD

/-- Case `15874` cert box `18` (mode `one`). -/
private theorem box_18 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_18).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4038232572967929798683287198739911816574293355935517197314844 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2004514978690858593 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3221131379545339874775147830967681766263368150156756528577864 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3226810576722579874735312446954057413635164755572007969734551 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_1.Top_pos x hD

/-- Case `15874` cert box `19` (mode `one`). -/
private theorem box_19 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_19).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4038232572967929798683287198739911816574293355935517197314844 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3221131379545339874775147830967681766263368150156756528577863 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2004514978690858593 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3228386670572699198466371477253038327482330312747927386552975 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3226810576722579874735312446954057413635164755572007969734551 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1256499149856796743 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2004514978690858593 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_2.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_2.Top_pos x hD

/-- Case `15874` cert box `20` (mode `one`). -/
private theorem box_20 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_20).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_3.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026981274403204103000829924780093874792635167538396449670221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3228386670572699198466371477253038327482330312747927386552975 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3226810576722579874735312446954057413635164755572007969734550 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((3937691999104897 : ℚ) / 1953125000000000) : ℚ) : ℝ) ≤
          (((3239745064927179198386700709225789622225923523578430268866349 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_3.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_3.Top_pos x hD

/-- Case `15874` cert box `21` (mode `one`). -/
private theorem box_21 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_21).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_4.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4026981274403204103000829924780093874792635167538396449670221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3228386670572699198466371477253038327482330312747927386552974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((3937691999104897 : ℚ) / 1953125000000000) : ℚ) : ℝ) ≤
          (((3239745064927179198386700709225789622225923523578430268866349 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((626499149856796743 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_4.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_one_4.Top_pos x hD

/-- Case `15874` cert box `22` (mode `zero`). -/
private theorem box_22 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_22).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3228386670572699198466371477253038327482330312747927386552975 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) ≤
          (((3226810576722579874735312446954057413635164755572007969734551 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
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
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_0.Top_pos x hD

/-- Case `15874` cert box `23` (mode `zero`). -/
private theorem box_23 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_23).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((3228386670572699198466371477253038327482330312747927386552975 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3226810576722579874735312446954057413635164755572007969734550 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((3937691999104897 : ℚ) / 1953125000000000) : ℚ) : ℝ) ≤
          (((3239745064927179198386700709225789622225923523578430268866349 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((7843941999104897 : ℚ) / 3906250000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_1.Top_pos x hD

/-- Case `15874` cert box `24` (mode `zero`). -/
private theorem box_24 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_24).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3228386670572699198466371477253038327482330312747927386552974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((504514978690858593 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3242897252627417845848818769823751449920254637930269102503198 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((3937691999104897 : ℚ) / 1953125000000000) : ℚ) : ℝ) ≤
          (((3239745064927179198386700709225789622225923523578430268866349 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((1004514978690858593 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_2.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRLLRL_zero_2.Top_pos x hD

/-- Case `15874` cert box `25` (mode `one`). -/
private theorem box_25 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_25).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3265409110523267340524675016871358941050720095647242292151487 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_one_0.Top_pos x hD

/-- Case `15874` cert box `26` (mode `zero`). -/
private theorem box_26 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_26).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3265409110523267340524675016871358941050720095647242292151487 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLRR_zero_0.Top_pos x hD

/-- Case `15874` cert box `27` (mode `one`). -/
private theorem box_27 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_27).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLLR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3265409110523267340524675016871358941050720095647242292151487 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((203206907832532541 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLLR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLLR_one_0.Top_pos x hD

/-- Case `15874` cert box `28` (mode `one`). -/
private theorem box_28 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_28).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((4035959635933384609 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3242768542037509738036394543230305731701919212272058348007070 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3239642599520623946607768622906337210818544087776995282638222 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_0.Top_pos x hD

/-- Case `15874` cert box `29` (mode `one`). -/
private theorem box_29 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_29).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((4035959635933384609 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3242768542037509738036394543230305731701919212272058348007070 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3239642599520623946607768622906337210818544087776995282638221 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4032069078325325411 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_1.Top_pos x hD

/-- Case `15874` cert box `30` (mode `one`). -/
private theorem box_30 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_30).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_2.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3242768542037509738036394543230305731701919212272058348007069 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4035959635933384609 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2035959635933384609 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3271660995557038924988864901778286258359432436978531025411387 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2032069078325325411 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3265409110523267342131613061130349216592682187988404894673691 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((4035959635933384609 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_2.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLLLL_one_2.Top_pos x hD

/-- Case `15874` cert box `31` (mode `one`). -/
private theorem box_31 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_31).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3265008745844498877286488892657753239603986599452247535039372 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_0.Top_pos x hD

/-- Case `15874` cert box `32` (mode `one`). -/
private theorem box_32 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_32).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4004352225139158984076126205144022964095465099449681796475838 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3265008745844498877286488892657753239603986599452247535039371 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((622978626874456113 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_one_1.Top_pos x hD

/-- Case `15874` cert box `33` (mode `zero`). -/
private theorem box_33 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_33).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLRR_zero_0.Top_pos x hD

/-- Case `15874` cert box `34` (mode `one`). -/
private theorem box_34 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_34).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3265008745844498877286488892657753239603986599452247535039372 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_0.Top_pos x hD

/-- Case `15874` cert box `35` (mode `one`). -/
private theorem box_35 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_35).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4004352225139158985683064249403013239637427191790844398998042 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3271660995557038923381926857519295982817470344637368422889183 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3265008745844498877286488892657753239603986599452247535039371 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((63623738622918269 : ℚ) / 31250000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4063639861548112397 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((2491914507497824453 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_LLLRL_one_1.Top_pos x hD

/-- Case `15874` cert box `36` (mode `one`). -/
private theorem box_36 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_36).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_RL_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3695917920740807035185576936687014761731548207681244142521586 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_RL_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_RL_one_0.Top_pos x hD

/-- Case `15874` cert box `37` (mode `one`). -/
private theorem box_37 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_37).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_RL_one_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3695917920740807035185576936687014761731548207681244142521585 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4599950737298165281 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_RL_one_1.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_RL_one_1.Top_pos x hD

/-- Case `15874` cert box `38` (mode `zero`). -/
private theorem box_38 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_38).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_RL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_RL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_RL_zero_0.Top_pos x hD

/-- Case `15874` cert box `39` (mode `one`). -/
private theorem box_39 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_39).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_RR_one_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((3958706084081349650312387267672995165487025358932004983599310 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤
          (((4049483871532655494365744472699729758355951544332637944959468 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((246350884418000923 : ℚ) / 100000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut1 : x 0 ≤ 2 * h0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact h4hi.trans (by norm_num : ((((63 : ℚ) / 25) : ℚ) : ℝ) ≤ (63/25 : ℝ))
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3O x h4 h5 h6 hcut1,
    ← Kepler.Text.TaylorSecond.W1DC_15874_RR_one_0.fTop_eq_w1F3O]
  exact Kepler.Text.TaylorSecond.W1DC_15874_RR_one_0.Top_pos x hD

/-- Case `15874` cert box `40` (mode `zero`). -/
private theorem box_40 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15874_cert_40).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15874_RR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((63000000000015501 : ℚ) / 25000000000000000) : ℚ) : ℝ) ≤
          (((4049483871533651860230706817030176796531686758792705811703733 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2071295072726240037 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3328442853249987194145344946369293786349377176684686433682974 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15874_RR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15874_RR_zero_0.Top_pos x hD

/-- Every point of the `certs15874` cover has `w1aF > 0`. -/
theorem case_pos {y4 y5 y6 : ℝ}
    (h : ∃ b : Kepler.Text.TaylorSecond.Box3, b ∈ Kepler.Text.TaylorSecond.certs15874 ∧ b.Mem y4 y5 y6) :
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  obtain ⟨b, hb, hbmem⟩ := h
  simp only [Kepler.Text.TaylorSecond.certs15874, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

#print axioms case_pos

end W1DCAssembly15874
end Kepler.Text.TaylorSecond
