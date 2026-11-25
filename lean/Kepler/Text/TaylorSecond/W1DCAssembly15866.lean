/-
`Kepler.Text.TaylorSecond.W1DCAssembly15866` — assembly of the 23 certificate
boxes of wt1 case `15866` (lane `wt1-assembly-w1`, 2026-11-26).

Each `box_<ci>` composes the landed box module `Kepler.Text.TaylorSecond.W1DC_<id>`:
`b15866_cert_<ci>.Mem y4 y5 y6 → x ∈ W1DC_<id>.D` (floor/ceil bridge on the
`2^-200` grid) → `W1DC_<id>.Top_pos` → the mode bridge
`w1aF = w1F3 = w1F3Z/O = fTop` (`w1F3_eq_w1F3Z`/`w1F3_eq_w1F3O` +
`fTop_eq_w1F3Z`/`fTop_eq_w1F3O`, kink `2*h0 = 63/25`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks19

import Kepler.Text.TaylorSecond.W1DC_15866_LRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LRLRRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LRLRRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15866_LRLLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LRLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_1

import Kepler.Text.TaylorSecond.W1DC_15866_LLRRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLRLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15866_LLLRRR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLRRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLRLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_LLLRLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_RLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_RLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_RRL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15866_RRR_zero_0


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssembly15866

open Kepler.Text


/-- Case `15866` cert box `0` (mode `zero`). -/
private theorem box_0 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_0).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRR_zero_0.Top_pos x hD

/-- Case `15866` cert box `1` (mode `zero`). -/
private theorem box_1 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_1).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLRRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3873442857029564442377726794475776432795336968389899766119104 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLRRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLRRL_zero_0.Top_pos x hD

/-- Case `15866` cert box `2` (mode `zero`). -/
private theorem box_2 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_2).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLRRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3873442857029564442377726794475776432795336968389899766119104 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLRRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLRRR_zero_0.Top_pos x hD

/-- Case `15866` cert box `3` (mode `zero`). -/
private theorem box_3 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_3).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2410449407721708957 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3873442857029564443984664838734766708337299060731062368641308 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3314611029588618352746093279808905312537520549266499332518499 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_0.Top_pos x hD

/-- Case `15866` cert box `4` (mode `zero`). -/
private theorem box_4 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_4).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2410449407721708957 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3873442857029564443984664838734766708337299060731062368641308 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3314611029588618352746093279808905312537520549266499332518498 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLRL_zero_1.Top_pos x hD

/-- Case `15866` cert box `5` (mode `zero`). -/
private theorem box_5 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_5).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2410449407721708957 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3873442857029564443984664838734766708337299060731062368641308 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLLL_zero_0.Top_pos x hD

/-- Case `15866` cert box `6` (mode `zero`). -/
private theorem box_6 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_6).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LRLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3873442857029564442377726794475776432795336968389899766119104 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((602612351930427239 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LRLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LRLLR_zero_0.Top_pos x hD

/-- Case `15866` cert box `7` (mode `zero`). -/
private theorem box_7 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_7).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3510460874007134060438375719717885284776407433355397202668280 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_0.Top_pos x hD

/-- Case `15866` cert box `8` (mode `zero`). -/
private theorem box_8 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_8).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3510460874007134060438375719717885284776407433355397202668279 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4369130330256034347 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLRRR_zero_1.Top_pos x hD

/-- Case `15866` cert box `9` (mode `zero`). -/
private theorem box_9 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_9).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLRRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLRRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLRRL_zero_0.Top_pos x hD

/-- Case `15866` cert box `10` (mode `zero`). -/
private theorem box_10 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_10).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLRLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLRLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLRLL_zero_0.Top_pos x hD

/-- Case `15866` cert box `11` (mode `zero`). -/
private theorem box_11 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_11).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3415345970659256152801324330676495144488673018626250391912041 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2243755314796630181 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3605575777355011968075427108759275425064141848084544013424518 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((1062687507729702083 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLRLR_zero_0.Top_pos x hD

/-- Case `15866` cert box `12` (mode `zero`). -/
private theorem box_12 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_12).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLLR_zero_0.Top_pos x hD

/-- Case `15866` cert box `13` (mode `zero`). -/
private theorem box_13 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_13).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((3314611029588618352746093279808905312537520549266499332518499 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_0.Top_pos x hD

/-- Case `15866` cert box `14` (mode `zero`). -/
private theorem box_14 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_14).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((1293113521698845521 : ℚ) / 500000000000000000) : ℚ) : ℝ) ≤
          (((4155906627127196411731443805041727923930838565345106435456063 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3314611029588618352746093279808905312537520549266499332518498 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((4125375015459404167 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLLL_zero_1.Top_pos x hD

/-- Case `15866` cert box `15` (mode `zero`). -/
private theorem box_15 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_15).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLRRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLRRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLRRR_zero_0.Top_pos x hD

/-- Case `15866` cert box `16` (mode `zero`). -/
private theorem box_16 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_16).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLRRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3697021906848610735587526406415263591350835651540594098688607 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2300662380890623529 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLRRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLRRL_zero_0.Top_pos x hD

/-- Case `15866` cert box `17` (mode `zero`). -/
private theorem box_17 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_17).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLRLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3316141403171017201882115556374190998621605118997746796953787 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2125375015459404167 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3415345970659256154408262374935485420030635110967412994434245 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((515909965387028099 : ℚ) / 250000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLRLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLRLR_zero_0.Top_pos x hD

/-- Case `15866` cert box `18` (mode `zero`). -/
private theorem box_18 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_18).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_LLLRLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627127196410124505760782737648388876473003943832933859 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((230066238089062353 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3697021906848610737194464450674253866892797743881756701210811 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2063639861548112397 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3316141403171017203489053600633181274163567211338909399475991 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2586227043397691041 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_LLLRLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_LLLRLL_zero_0.Top_pos x hD

/-- Case `15866` cert box `19` (mode `zero`). -/
private theorem box_19 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_19).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_RLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_RLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_RLL_zero_0.Top_pos x hD

/-- Case `15866` cert box `20` (mode `zero`). -/
private theorem box_20 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_20).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_RLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777353892931774042121629174064586201493953724806748112 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((294524427812650441 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126069286634515722691112098944072823311500779727600 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2243755314795933803 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_RLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_RLR_zero_0.Top_pos x hD

/-- Case `15866` cert box `21` (mode `zero`). -/
private theorem box_21 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_21).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_RRL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3605575777355011966468489064500285149522179755743381410902314 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2356195422501535101 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3786260064126602103902664808873744373940916659619106874140858 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((112187765739831509 : ℚ) / 50000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_RRL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_RRL_zero_0.Top_pos x hD

/-- Case `15866` cert box `22` (mode `zero`). -/
private theorem box_22 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15866_cert_22).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15866_RRR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4049483871532655494365744472699729758355951544332637944959467 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((63 : ℚ) / 25) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126069285027577678432121823402110730970338177205396 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3786260064126602102295726764614754098398954567277944271618654 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((2463508844180643489 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((3958706084082368865229400930586170134821751572383118113547945 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < ((((2356195422501203527 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((23561954225015351 : ℚ) / 10000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((63 : ℚ) / 25) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15866_RRR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15866_RRR_zero_0.Top_pos x hD

/-- Every point of the `certs15866` cover has `w1aF > 0`. -/
theorem case_pos {y4 y5 y6 : ℝ}
    (h : ∃ b : Kepler.Text.TaylorSecond.Box3, b ∈ Kepler.Text.TaylorSecond.certs15866 ∧ b.Mem y4 y5 y6) :
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  obtain ⟨b, hb, hbmem⟩ := h
  simp only [Kepler.Text.TaylorSecond.certs15866, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

#print axioms case_pos

end W1DCAssembly15866
end Kepler.Text.TaylorSecond
