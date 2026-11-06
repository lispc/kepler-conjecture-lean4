/-
  Kepler/Graphs/ArchivePreQuadShardS003 — `archivePre` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `archivePre` / Quad：覆盖 第 [300, 400) 项。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.ArchiveData.Quad
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`archivePre` on slice 3/13 of Quad. -/
theorem archivePreQuadS003 : ((QuadData.drop 300).take 100).all (fun a => preIsoTestB a) = true := by
  decide +kernel

#print axioms archivePreQuadS003

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
