/-
  Kepler/Graphs/TopReplayQuadShardS000 — `topReplay` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `topReplay` / Quad：覆盖 第 [0, 50) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.QuadTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`topReplay` on slice 0/6 of Quad. -/
theorem topReplayQuadS000 : ((List.range QuadTop.length).take 50).all (fun i => decide (next_tame 1 QuadTop[i]! = (QuadTopChildren[i]!).map (resolveChild QuadTop QuadFrontier))) = true := by
  decide +kernel

#print axioms topReplayQuadS000

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
