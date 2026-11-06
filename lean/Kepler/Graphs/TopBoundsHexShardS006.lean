/-
  Kepler/Graphs/TopBoundsHexShardS006 — `topBounds` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `topBounds` / Hex：覆盖 第 [600, 700) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.HexTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`topBounds` on slice 6/14 of Hex. -/
theorem topBoundsHexS006 : (((List.range HexTopChildren.length).drop 600).take 100).all (fun i => (HexTopChildren[i]!).all (fun t => (t.1 && decide (t.2 < HexFrontier.length)) || (!t.1 && decide (t.2 < HexTop.length)))) = true := by
  decide +kernel

#print axioms topBoundsHexS006

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
