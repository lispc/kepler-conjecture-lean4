/-
`Kepler.Text.TaylorSecond.W1DCAssembly15872` — assembly of the 6 certificate
boxes of wt1 case `15872` (lane `wt1-assembly-w1`, 2026-11-26).

Each `box_<ci>` composes the landed box module `Kepler.Text.TaylorSecond.W1DC_<id>`:
`b15872_cert_<ci>.Mem y4 y5 y6 → x ∈ W1DC_<id>.D` (floor/ceil bridge on the
`2^-200` grid) → `W1DC_<id>.Top_pos` → the mode bridge
`w1aF = w1F3 = w1F3Z/O = fTop` (`w1F3_eq_w1F3Z`/`w1F3_eq_w1F3O` +
`fTop_eq_w1F3Z`/`fTop_eq_w1F3O`, kink `2*h0 = 63/25`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue
import Kepler.Text.TaylorSecond.W1aFJet
import Kepler.NliBanks19

import Kepler.Text.TaylorSecond.W1DC_15872_LR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_1

import Kepler.Text.TaylorSecond.W1DC_15872_RLL_zero_0

import Kepler.Text.TaylorSecond.W1DC_15872_RLR_zero_0

import Kepler.Text.TaylorSecond.W1DC_15872_RR_zero_0


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssembly15872

open Kepler.Text


/-- Case `15872` cert box `0` (mode `zero`). -/
private theorem box_0 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_0).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_LR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627126710984673157960741311656938059962263811323331294 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2618712561546525003 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4208108842128023591198046006917186063710983429577739302208268 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3249777411025826893921507996286165478295895448596016047279534 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2022341447846174787 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((204443876488221701 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3285286430447095451478442476708526264062080342287349052459705 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2022341447846174787 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_LR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_LR_zero_0.Top_pos x hD

/-- Case `15872` cert box `1` (mode `zero`). -/
private theorem box_1 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_1).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4155906627126710984673157960741311656938059962263811323331294 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((5204939604943913963 : ℚ) / 2000000000000000000) : ℚ) : ℝ) ≤
          (((4182007734627367287935601983829248860324521695920775312769781 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((505585361961543697 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3249777411025826895528446040545155753837857540937178649801738 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((16163919021233681 : ℚ) / 6250000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_0.Top_pos x hD

/-- Case `15872` cert box `2` (mode `zero`). -/
private theorem box_2 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_2).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_1.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4182007734627367287935601983829248860324521695920775312769780 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((5204939604943913963 : ℚ) / 2000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((2618712561546525003 : ℚ) / 1000000000000000000) : ℚ) : ℝ) ≤
          (((4208108842128023591198046006917186063710983429577739302208268 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((505585361961543697 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3249777411025826895528446040545155753837857540937178649801738 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((5204939604943913963 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((5204939604943913963 : ℚ) / 2000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_1.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_LL_zero_1.Top_pos x hD

/-- Case `15872` cert box `3` (mode `zero`). -/
private theorem box_3 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_3).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_RLL_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4208108842128023589591107962658195788169021337236576699686064 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((329350640939939311 : ℚ) / 125000000000000000) : ℚ) : ℝ) ≤
          (((4233968598619768089152035096935304017184191390127721483778067 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((505585361961543697 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3249777411025826895528446040545155753837857540937178649801738 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_RLL_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_RLL_zero_0.Top_pos x hD

/-- Case `15872` cert box `4` (mode `zero`). -/
private theorem box_4 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_4).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_RLR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4233968598619768087545097052676313741642229297786558881255863 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2634805127519514487 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((505585361961543697 : ℚ) / 250000000000000000) : ℚ) : ℝ) ≤
          (((3249777411025826895528446040545155753837857540937178649801738 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((2634805127519514487 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ (((2 : ℚ) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((2634805127519514487 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_RLR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_RLR_zero_0.Top_pos x hD

/-- Case `15872` cert box `5` (mode `zero`). -/
private theorem box_5 (x : Fin 3 → ℝ)
    (hx : (Kepler.Text.TaylorSecond.b15872_cert_5).Mem (x 0) (x 1) (x 2)) :
    0 < Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) := by
  obtain ⟨h4lo, h4hi, h5lo, h5hi, h6lo, h6hi⟩ := hx
  have hD : x ∈ Kepler.Text.TaylorSecond.W1DC_15872_RR_zero_0.D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (show (((4208108842128023589591107962658195788169021337236576699686064 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ) from by norm_num).trans h4lo
    · exact h4hi.trans (show ((((530160000000117889 : ℚ) / 200000000000000000) : ℚ) : ℝ) ≤
          (((4259671367722678624002131354900920658611375732509670947760558 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3213876088517980551083924184682325205044405987565585670602752 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          (((2 : ℚ) : ℚ) : ℝ) from by norm_num).trans h5lo
    · exact h5hi.trans (show ((((126791833192082937 : ℚ) / 62500000000000000) : ℚ) : ℝ) ≤
          (((3259945927323166126135092526159849810630340151469380259249923 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
    · exact (show (((3249777411025826893921507996286165478295895448596016047279534 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) ≤
          ((((2022341447846174787 : ℚ) / 1000000000000000000) : ℚ) : ℝ) from by norm_num).trans h6lo
    · exact h6hi.trans (show ((((204443876488221701 : ℚ) / 100000000000000000) : ℚ) : ℝ) ≤
          (((3285286430447095451478442476708526264062080342287349052459705 : ℤ)) : ℝ) * (2 : ℝ) ^ (-(200 : ℤ)) from by norm_num)
  have h4 : (0 : ℝ) ≤ x 0 := (by norm_num : (0 : ℝ) ≤ ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  have h5 : (0 : ℝ) < x 1 := (by norm_num : (0 : ℝ) < (((2 : ℚ) : ℚ) : ℝ)).trans_le h5lo
  have h6 : (0 : ℝ) ≤ x 2 := (by norm_num : (0 : ℝ) ≤ ((((2022341447846174787 : ℚ) / 1000000000000000000) : ℚ) : ℝ)).trans h6lo

  have hcut : 2 * h0 ≤ x 0 := by
    have h2 : (2 : ℝ) * h0 = (63/25 : ℝ) := by
      rw [Kepler.NliBanks19.nb19_two_h0]; norm_num
    rw [h2]
    exact (by norm_num : (63/25 : ℝ) ≤ ((((1309356280773262501 : ℚ) / 500000000000000000) : ℚ) : ℝ)).trans h4lo
  rw [show Kepler.NliBanks21.w1aF (x 0) (x 1) (x 2) = w1F3 x from rfl,
    w1F3_eq_w1F3Z x h4 h5 h6 hcut,
    ← Kepler.Text.TaylorSecond.W1DC_15872_RR_zero_0.fTop_eq_w1F3Z]
  exact Kepler.Text.TaylorSecond.W1DC_15872_RR_zero_0.Top_pos x hD

/-- Every point of the `certs15872` cover has `w1aF > 0`. -/
theorem case_pos {y4 y5 y6 : ℝ}
    (h : ∃ b : Kepler.Text.TaylorSecond.Box3, b ∈ Kepler.Text.TaylorSecond.certs15872 ∧ b.Mem y4 y5 y6) :
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  obtain ⟨b, hb, hbmem⟩ := h
  simp only [Kepler.Text.TaylorSecond.certs15872, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using box_0 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_1 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_2 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_3 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_4 ![y4, y5, y6] (by simpa using hbmem)
  · simpa using box_5 ![y4, y5, y6] (by simpa using hbmem)

#print axioms case_pos

end W1DCAssembly15872
end Kepler.Text.TaylorSecond
