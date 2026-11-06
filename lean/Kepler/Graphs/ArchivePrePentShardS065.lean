/-
  Kepler/Graphs/ArchivePrePentShardS065 — `archivePre` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `archivePre` / Pent：覆盖 第 [6500, 6600) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.ArchiveData.Pent
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`archivePre` on slice 65/161 of Pent. -/
theorem archivePrePentS065 : ((PentData.drop 6500).take 100).all (fun a => preIsoTestB a) = true := by
  decide +kernel

#print axioms archivePrePentS065

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
