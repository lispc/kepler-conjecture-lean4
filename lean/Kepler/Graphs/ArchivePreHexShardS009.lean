/-
  Kepler/Graphs/ArchivePreHexShardS009 — `archivePre` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `archivePre` / Hex：覆盖 第 [900, 1000) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.ArchiveData.Hex
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`archivePre` on slice 9/24 of Hex. -/
theorem archivePreHexS009 : ((HexData.drop 900).take 100).all (fun a => preIsoTestB a) = true := by
  decide +kernel

#print axioms archivePreHexS009

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
