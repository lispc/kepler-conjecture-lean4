/-
  Kepler/Graphs/TopReplayHexShardS025 — `topReplay` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `topReplay` / Hex：覆盖 第 [625, 650) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.CertData.HexTop
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`topReplay` on slice 25/55 of Hex. -/
theorem topReplayHexS025 : (((List.range HexTop.length).drop 625).take 25).all (fun i => decide (next_tame 3 HexTop[i]! = (HexTopChildren[i]!).map (resolveChild HexTop HexFrontier))) = true := by
  decide +kernel

#print axioms topReplayHexS025

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
