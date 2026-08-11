/-
Tri seed (p = 0) pilot: per-seed wiring of the enumeration certificate.

This is the evaluation-side file: `native_decide` is allowed here (see
DECISIONS.md, 2026-08-10); every assembly proof is a pure kernel proof.
No holes, no new axioms.

Pipeline (`pipeline/graphs/certgen.py top 0 4 ...`, UNTRUSTED data in
`CertData/TriTop.lean`):
- `TriTop`: BFS tree of `next_tame 0` from `Seed 0` down to depth < 4
  (6 nodes; node 0 is `Seed 0`).
- `TriTopChildren`: per-node children, tagged `(isFrontier, index)`.
- `TriFrontier`: the 5 depth-4 shard roots.
- `TriTopFinals`: final graphs in the top (EMPTY for Tri).

Verified here:
1. `tri_top_replay` / `tri_top_bounds` (native_decide): the tagged children
   tables replay `next_tame 0` exactly, with in-range indices.
2. `tri_top_closed` (kernel, generic `closed_of_replay`): `TriTop` is closed
   under `next_tame 0` up to `TriFrontier`.
3. `tri_top_final_archive` (kernel, generic `top_final_archive_of_no_finals`
   + native_decide `tri_top_no_finals`): no final graphs in the top, so the
   Archive membership obligation for the top is vacuous.  (For seeds with a
   nonempty finals table this is where per-entry `(i, j)` `preIsoTestB` /
   `iso_test` native_decide checks plus `iso_test_correct` and Archive
   membership assembly would be inserted.)
4. `tri_archive_pre` (native_decide) + `tri_archive_pre_iso` (kernel):
   every `TriData` entry satisfies `pre_iso_test`.
5. `tri_shard_0` … `tri_shard_4` (native_decide, fuel 500000): the worklist
   loop from each shard root certifies `checkFinal` on its whole `RTranCl`
   closure (`loop_some_true`).
6. `same_0` (kernel): `∀ g, TameEnumP 0 g → inIso g.fgraph Archive`,
   assembled via `frontier_cut` + `checkFinal_correct`.

Deviation from the task spec: `List.get!` does not exist in Lean v4.32.2;
the equivalent `l[i]!` (`getElem!`) notation is used throughout.
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.TriTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/- `resolveChild` / `closed_of_replay` / `top_final_archive_of_no_finals`
live in CertCheck.lean (shared with the generated seed wirings). -/

/-! ### Tri top replay (native_decide) and closure -/

/-- Replay: every top node's `next_tame 0` children are exactly its tagged
children table entries. -/
theorem tri_top_replay : (List.range TriTop.length).all (fun i =>
    decide (next_tame 0 TriTop[i]! =
      (TriTopChildren[i]!).map (resolveChild TriTop TriFrontier))) = true := by
  native_decide

/-- Bounds: every tagged child index is in range of its target list. -/
theorem tri_top_bounds : (List.range TriTopChildren.length).all (fun i =>
    (TriTopChildren[i]!).all (fun t =>
      (t.1 && decide (t.2 < TriFrontier.length)) ||
        (!t.1 && decide (t.2 < TriTop.length)))) = true := by
  native_decide

/-- `TriTop` is closed under `next_tame 0` up to `TriFrontier`. -/
theorem tri_top_closed : ∀ x ∈ TriTop, ∀ c ∈ next_tame 0 x,
    c ∈ TriTop ∨ c ∈ TriFrontier :=
  closed_of_replay rfl tri_top_replay tri_top_bounds

/-! ### Top final coverage (Tri: vacuous) -/

theorem tri_top_no_finals : (TriTop.all (fun g => !g.final)) = true := by
  native_decide

theorem tri_top_final_archive :
    ∀ g ∈ TriTop, g.final = true → inIso g.fgraph Archive :=
  top_final_archive_of_no_finals tri_top_no_finals

/-! ### Archive-side `pre_iso_test` -/

theorem tri_archive_pre : (TriData.all (fun a => preIsoTestB a)) = true := by
  native_decide

theorem tri_archive_pre_iso : ∀ a ∈ TriData, pre_iso_test a := fun a ha =>
  preIsoTestB_correct ((List.all_eq_true.mp tri_archive_pre) a ha)

/-! ### Shard runs (native_decide, fuel 500000) -/

theorem tri_shard_0 : loop (next_tame 0) (checkFinal (buildBuckets TriData))
    500000 [TriFrontier[0]!] = some true := by
  native_decide

theorem tri_shard_1 : loop (next_tame 0) (checkFinal (buildBuckets TriData))
    500000 [TriFrontier[1]!] = some true := by
  native_decide

theorem tri_shard_2 : loop (next_tame 0) (checkFinal (buildBuckets TriData))
    500000 [TriFrontier[2]!] = some true := by
  native_decide

theorem tri_shard_3 : loop (next_tame 0) (checkFinal (buildBuckets TriData))
    500000 [TriFrontier[3]!] = some true := by
  native_decide

theorem tri_shard_4 : loop (next_tame 0) (checkFinal (buildBuckets TriData))
    500000 [TriFrontier[4]!] = some true := by
  native_decide

/-! ### Assembly: `same_0` -/

/-- The seed-0 (`Tri`) case of the enumeration-completeness certificate:
every stage-0 tame-enumerated final graph is isomorphic to an Archive
entry. -/
theorem same_0 : ∀ g, TameEnumP 0 g → inIso g.fgraph Archive := by
  intro g htep
  obtain ⟨hr, hfin⟩ := htep
  have h0 : TriTop[0]'(by decide) = Seed 0 := by decide
  have hseed : Seed 0 ∈ TriTop := h0 ▸ List.getElem_mem _
  rcases frontier_cut TriTop TriFrontier hseed tri_top_closed hr with hS | ⟨h, hF, hrh⟩
  · exact tri_top_final_archive g hS hfin
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hF
    have hlen5 : TriFrontier.length = 5 := rfl
    rw [hlen5] at hj
    have hloop : loop (next_tame 0) (checkFinal (buildBuckets TriData)) 500000
        [TriFrontier[j]!] = some true := by
      rcases j with _ | _ | _ | _ | _ | j
      · exact tri_shard_0
      · exact tri_shard_1
      · exact tri_shard_2
      · exact tri_shard_3
      · exact tri_shard_4
      · exact absurd hj (by omega)
    rw [getElem!_pos TriFrontier j hj] at hloop
    have hcheck := loop_some_true hloop g
      ⟨TriFrontier[j]'hj, List.mem_singleton_self _, hrh⟩
    obtain ⟨a, ha, hiso⟩ := checkFinal_correct tri_archive_pre_iso hcheck hfin
    refine ⟨a, ?_, hiso⟩
    show a ∈ TriData ++ QuadData ++ PentData ++ HexData
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha))

end Kepler.Graphs
