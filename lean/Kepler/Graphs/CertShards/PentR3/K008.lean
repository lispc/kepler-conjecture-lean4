/- Shard group [8, 9) for seed Pent (p = 2).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [8, 9): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem pentr3_shard_8 : (List.range' 8 1).all (fun j =>
    decide (loop (next_tame 2) (checkFinal (buildBuckets PentData)) 300000000
      [PentFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem pentr3_shardE_8 : ∀ j ∈ List.range' 8 1,
    ∃ fuel, loop (next_tame 2) (checkFinal (buildBuckets PentData)) fuel
      [PentFrontier[j]!] = some true := fun j hj =>
  ⟨300000000, of_decide_eq_true ((List.all_eq_true.mp pentr3_shard_8) j hj)⟩

end Kepler.Graphs
