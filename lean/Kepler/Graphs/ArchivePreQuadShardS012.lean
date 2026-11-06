/-
  Kepler/Graphs/ArchivePreQuadShardS012 — `archivePre` kernel 分片（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改，重新生成会覆盖。
  `archivePre` / Quad：覆盖 第 [1200, 1253) 项（末片）。
  信任模型：kernel `decide +kernel`（无 native_decide）。
-/
import Kepler.Graphs.CertCheck
import Kepler.Graphs.ArchiveData.Quad
import Kepler.Graphs.ReshardDefs

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`archivePre` on slice 12/13 of Quad. -/
theorem archivePreQuadS012 : (QuadData.drop 1200).all (fun a => preIsoTestB a) = true := by
  decide +kernel

#print axioms archivePreQuadS012

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
