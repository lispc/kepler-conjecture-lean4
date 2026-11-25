/-
`Kepler.Text.TaylorSecond.W1DCAssemblyFinal` — the wt1 `hcore` from the 9 case
modules and `Wt1Glue.cover_all_flat`, plus the bank
(lane `wt1-assembly-w1`, 2026-11-26).

`bank_QZECFICwt1_of_core` (`Kepler.NliBanks21:359`) consumes `wt1_hcore`;
`wt1_bank` is `Kepler.Text.bank_QZECFICwt1` (`PackingAuto21:230`) by that
reduction.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Wt1Glue

import Kepler.Text.TaylorSecond.W1DCAssembly15866

import Kepler.Text.TaylorSecond.W1DCAssembly15867

import Kepler.Text.TaylorSecond.W1DCAssembly15868

import Kepler.Text.TaylorSecond.W1DCAssembly15869

import Kepler.Text.TaylorSecond.W1DCAssembly15870

import Kepler.Text.TaylorSecond.W1DCAssembly15871

import Kepler.Text.TaylorSecond.W1DCAssembly15872

import Kepler.Text.TaylorSecond.W1DCAssembly15873

import Kepler.Text.TaylorSecond.W1DCAssembly15874


set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace W1DCAssemblyFinal

open Kepler.Text

/-- **wt1 core**: `w1aF > 0` on the whole closed-Delta region. -/
theorem wt1_hcore : ∀ y4 y5 y6 : ℝ, 2 * Kepler.Text.hminus ≤ y4 →
    y4 ≤ 2 * Kepler.Text.hplus →
    2 ≤ y5 → y5 ≤ 2 * Kepler.Text.hminus →
    2 ≤ y6 → y6 ≤ 2 * Kepler.Text.hminus →
    0 ≤ Kepler.Text.deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 →
    0 < Kepler.NliBanks21.w1aF y4 y5 y6 := by
  intro y4 y5 y6 h4 h4' h5 h5' h6 h6' hd
  obtain ⟨b, hb, hbmem⟩ :=
    cover_all_flat y4 y5 y6 h4 h4' h5 h5' h6 h6'
  simp only [Kepler.Text.TaylorSecond.allCerts, List.mem_append] at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb

  · exact W1DCAssembly15866.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15867.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15868.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15869.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15870.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15871.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15872.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15873.case_pos ⟨b, hb, hbmem⟩

  · exact W1DCAssembly15874.case_pos ⟨b, hb, hbmem⟩


/-- **The wt1 bank** `QZECFIC wt1` (`ineq.hl:1425`), by the core reduction. -/
theorem wt1_bank : Kepler.Text.bank_QZECFICwt1 :=
  Kepler.NliBanks21.bank_QZECFICwt1_of_core wt1_hcore

#print axioms wt1_hcore
#print axioms wt1_bank

end W1DCAssemblyFinal
end Kepler.Text.TaylorSecond
