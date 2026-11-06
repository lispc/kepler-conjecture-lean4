/-
  Kepler/Graphs/TopBoundsTri — `topBounds` / Tri 全类闭合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  单片：全类 6 项一次 `decide +kernel`（纯内核，无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.TriTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Tri `topBounds` 全类闭合：6 项，单片。 -/
theorem topBoundsTriAll : (List.range TriTopChildren.length).all (fun i => (TriTopChildren[i]!).all (fun t => (t.1 && decide (t.2 < TriFrontier.length)) || (!t.1 && decide (t.2 < TriTop.length)))) = true := by
  decide +kernel

#print axioms topBoundsTriAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
