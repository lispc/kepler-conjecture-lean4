/- Shard group [3395, 3400) for seed Hex (p = 3).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.HexTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [3395, 3400): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem hexr_shard_3395 : (List.range' 3395 5).all (fun j =>
    decide (loop (next_tame 3) (checkFinal (buildBuckets HexData)) 50000000
      [HexFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem hexr_shardE_3395 : ∀ j ∈ List.range' 3395 5,
    ∃ fuel, loop (next_tame 3) (checkFinal (buildBuckets HexData)) fuel
      [HexFrontier[j]!] = some true := fun j hj =>
  ⟨50000000, of_decide_eq_true ((List.all_eq_true.mp hexr_shard_3395) j hj)⟩

end Kepler.Graphs
