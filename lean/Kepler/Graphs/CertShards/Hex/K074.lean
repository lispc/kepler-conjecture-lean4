/- Shard group [7400, 7500) for seed Hex (p = 3).
Evaluation-only file: `native_decide` allowed (DECISIONS.md 2026-08-10). -/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.HexTop
import Kepler.Graphs.Worklist

namespace Kepler.Graphs

/-- Shards [7400, 7500): worklist closure from each
frontier root certifies `checkFinal` (`loop_some_true`). -/
theorem hex_shard_7400 : (List.range' 7400 100).all (fun j =>
    decide (loop (next_tame 3) (checkFinal (buildBuckets HexData)) 4000000
      [HexFrontier[j]!] = some true)) = true := by
  native_decide

/-- Fuel-existential form: the certificate is valid regardless of the fuel
each shard file happened to use. -/
theorem hex_shardE_7400 : ∀ j ∈ List.range' 7400 100,
    ∃ fuel, loop (next_tame 3) (checkFinal (buildBuckets HexData)) fuel
      [HexFrontier[j]!] = some true := fun j hj =>
  ⟨4000000, of_decide_eq_true ((List.all_eq_true.mp hex_shard_7400) j hj)⟩

end Kepler.Graphs
