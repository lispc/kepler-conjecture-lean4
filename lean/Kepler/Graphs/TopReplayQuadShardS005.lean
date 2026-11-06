/-
  Kepler/Graphs/TopReplayQuadShardS005 — `topReplay` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `topReplay` / Quad：覆盖 第 [250, 286) 项（末片）。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.QuadTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`topReplay` on slice 5/6 of Quad. -/
theorem topReplayQuadS005 : ((List.range QuadTop.length).drop 250).all (fun i => decide (next_tame 1 QuadTop[i]! = (QuadTopChildren[i]!).map (resolveChild QuadTop QuadFrontier))) = true := by
  decide +kernel

#print axioms topReplayQuadS005

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
