/-
  Kepler/Graphs/TopReplayTri — `topReplay` / Tri 全类闭合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  单片：全类 6 项一次 `decide +kernel`（纯内核，无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.TriTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Tri `topReplay` 全类闭合：6 项，单片。 -/
theorem topReplayTriAll : (List.range TriTop.length).all (fun i => decide (next_tame 0 TriTop[i]! = (TriTopChildren[i]!).map (resolveChild TriTop TriFrontier))) = true := by
  decide +kernel

#print axioms topReplayTriAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
