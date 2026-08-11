/- Shard group [25, 30) for seed Quad (p = 1).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.QuadTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [25, 30): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem quadr_shard_25 : (List.range' 25 5).all (fun j =>
    decide (loop (next_tame 1) (checkFinal (buildBuckets QuadData)) 50000000
      [QuadFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem quadr_shardE_25 : ∀ j ∈ List.range' 25 5,
    ∃ fuel, loop (next_tame 1) (checkFinal (buildBuckets QuadData)) fuel
      [QuadFrontier[j]!] = some true := fun j hj =>
  ⟨50000000, of_decide_eq_true ((List.all_eq_true.mp quadr_shard_25) j hj)⟩

end Kepler.Graphs
