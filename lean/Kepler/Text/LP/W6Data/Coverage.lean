/-
  Kepler/Text/LP/W6Data/Coverage — W6-A coverage against the frozen record
  registry.

  `recordIds` is rebuilt from the Marshal files in LPIds segment order and
  chunked exactly like LPIds.lean. Each 250-id chunk equality is a small
  `decide`; the segment and master equalities are `simp` rewrites over those
  chunks. No 43k-element single reduction (memory-safe sharded proof).

  Import note: this coverage module imports `Kepler.Text.LP.LPIds` (pure
  record data, imports LPCert only). It does NOT import Kepler.Assembly, so
  no cycle is created; the W6Data root imports this module deliberately.
-/
import Kepler.Text.LP.W6Data.RecordIds
import Kepler.Text.LP.LPIds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.Text.LP.W6Data

open Kepler.Text.LP

/-- **hcov**: every rebuilt record id is in the frozen registry. -/
theorem hcov : ∀ id ∈ recordIds, id ∈ lpTerminalIds := by
  intro id hid
  simp only [recordIds, recordIdsInfeas_eq, recordIdsRoot_eq,
    recordIdsEasy_eq, recordIdsHard_eq, lpTerminalIds, lpTerminalBoundIds,
    List.mem_append] at hid ⊢
  tauto

/-- **recordIds_eq_lpTerminalIds**: rebuilt ids coincide exactly (element and
order) with the frozen `LPIds.lpTerminalIds` registry. -/
theorem recordIds_eq_lpTerminalIds : recordIds = lpTerminalIds := by
  simp only [recordIds, recordIdsInfeas_eq, recordIdsRoot_eq,
    recordIdsEasy_eq, recordIdsHard_eq, lpTerminalIds, lpTerminalBoundIds]

/-- W6-A accounting: the rebuilt record-id count is the 43,078 baseline. -/
theorem recordIds_length_43078 : recordIds.length = 43078 := by
  rw [recordIds_eq_lpTerminalIds]
  exact lpTerminalIds_length

end Kepler.Text.LP.W6Data
