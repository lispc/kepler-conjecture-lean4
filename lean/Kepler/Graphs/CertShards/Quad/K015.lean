/- Shard group [1500, 1583) for seed Quad (p = 1).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.QuadTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [1500, 1583): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem quad_shard_1500 : (List.range' 1500 83).all (fun j =>
    decide (loop (next_tame 1) (checkFinal (buildBuckets QuadData)) 4000000
      [QuadFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem quad_shardE_1500 : ∀ j ∈ List.range' 1500 83,
    ∃ fuel, loop (next_tame 1) (checkFinal (buildBuckets QuadData)) fuel
      [QuadFrontier[j]!] = some true := fun j hj =>
  ⟨4000000, of_decide_eq_true ((List.all_eq_true.mp quad_shard_1500) j hj)⟩

end Kepler.Graphs
