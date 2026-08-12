"""Generate grandchild-split shards + Root assembly for one heavy child.

Usage: childsplitgen.py <dir_name> <prefix> <parent_expr> <nchildren> <fuel>
Example: childsplitgen.py PentR5 pentr5 "(next_tame 2 (PentFrontier[0]!))[1]!" 83 400000000
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "Kepler" / "Graphs"


def main():
    dirname, prefix, parent, n, fuel = (
        sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    d = LEAN / "CertShards" / dirname
    d.mkdir(parents=True, exist_ok=True)
    for g in range(n):
        (d / f"K{g:03d}.lean").write_text(f"""/- Grandchild shard {g} (contingency split, WorklistSplit).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Grandchild {g}: worklist closure certifies `checkFinal`. -/
theorem {prefix}_shard_{g} : decide (loop (next_tame 2)
    (checkFinal (buildBuckets PentData)) {fuel}
    [(next_tame 2 ({parent}))[{g}]!] = some true) = true := by
  native_decide

/-- Fuel-existential form. -/
theorem {prefix}_shardE_{g} : ∃ fuel, loop (next_tame 2)
    (checkFinal (buildBuckets PentData)) fuel
    [(next_tame 2 ({parent}))[{g}]!] = some true :=
  ⟨{fuel}, of_decide_eq_true {prefix}_shard_{g}⟩

end Kepler.Graphs
""")
    imports = "\n".join(
        f"import Kepler.Graphs.CertShards.{dirname}.K{g:03d}" for g in range(n))
    bullets = ["  interval_cases i\n"] + [
        f"  · exact {prefix}_shardE_{g}\n" for g in range(n)]
    (d / "Root.lean").write_text(f"""/- Assembly for the contingency split of one heavy child:
its closure follows from its {n} children's closures
(`loop_singleton_of_children`).  Kernel proof; `native_decide` only for
the (cheap) child count and `checkFinal` on the parent. -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist
import Kepler.Graphs.WorklistSplit
import Mathlib.Tactic.IntervalCases
{imports}

namespace Kepler.Graphs

/-- Child count of the parent under `next_tame 2`. -/
theorem {prefix}_len : (next_tame 2 ({parent})).length = {n} := by
  native_decide

/-- The parent closes: `checkFinal` holds on it and every child's
closure is certified by its shard. -/
theorem {prefix}_root : ∃ fuel, loop (next_tame 2)
    (checkFinal (buildBuckets PentData)) fuel [{parent}] = some true := by
  apply loop_singleton_of_children (by native_decide)
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hiN : i < {n} := {prefix}_len ▸ hi
  rw [← getElem!_pos _ i hi]
{"".join(bullets)}
end Kepler.Graphs
""")
    print(f"{dirname}: {n} shards + Root.lean")


if __name__ == "__main__":
    main()
