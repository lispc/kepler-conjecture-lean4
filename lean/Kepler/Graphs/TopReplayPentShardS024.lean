/-
  Kepler/Graphs/TopReplayPentShardS024 — `topReplay` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `topReplay` / Pent：覆盖 第 [600, 625) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.PentTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`topReplay` on slice 24/31 of Pent. -/
theorem topReplayPentS024 : (((List.range PentTop.length).drop 600).take 25).all (fun i => decide (next_tame 2 PentTop[i]! = (PentTopChildren[i]!).map (resolveChild PentTop PentFrontier))) = true := by
  decide +kernel

#print axioms topReplayPentS024

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
