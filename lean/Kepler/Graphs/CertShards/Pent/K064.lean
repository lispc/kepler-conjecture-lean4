/- Shard group [3200, 3250) for seed Pent (p = 2).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [3200, 3250): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem pent_shard_3200 : (List.range' 3200 50).all (fun j =>
    decide (loop (next_tame 2) (checkFinal (buildBuckets PentData)) 50000000
      [PentFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem pent_shardE_3200 : ∀ j ∈ List.range' 3200 50,
    ∃ fuel, loop (next_tame 2) (checkFinal (buildBuckets PentData)) fuel
      [PentFrontier[j]!] = some true := fun j hj =>
  ⟨50000000, of_decide_eq_true ((List.all_eq_true.mp pent_shard_3200) j hj)⟩

end Kepler.Graphs
