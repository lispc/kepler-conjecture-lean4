/- Shard group [1860, 1870) for seed Pent (p = 2).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [1860, 1870): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem pentr_shard_1860 : (List.range' 1860 10).all (fun j =>
    decide (loop (next_tame 2) (checkFinal (buildBuckets PentData)) 50000000
      [PentFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem pentr_shardE_1860 : ∀ j ∈ List.range' 1860 10,
    ∃ fuel, loop (next_tame 2) (checkFinal (buildBuckets PentData)) fuel
      [PentFrontier[j]!] = some true := fun j hj =>
  ⟨50000000, of_decide_eq_true ((List.all_eq_true.mp pentr_shard_1860) j hj)⟩

end Kepler.Graphs
