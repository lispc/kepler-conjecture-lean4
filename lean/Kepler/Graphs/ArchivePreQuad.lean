/-
  Kepler/Graphs/ArchivePreQuad — `archivePre` / Quad 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：13 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.ArchivePreQuadShardS000
import Kepler.Graphs.ArchivePreQuadShardS001
import Kepler.Graphs.ArchivePreQuadShardS002
import Kepler.Graphs.ArchivePreQuadShardS003
import Kepler.Graphs.ArchivePreQuadShardS004
import Kepler.Graphs.ArchivePreQuadShardS005
import Kepler.Graphs.ArchivePreQuadShardS006
import Kepler.Graphs.ArchivePreQuadShardS007
import Kepler.Graphs.ArchivePreQuadShardS008
import Kepler.Graphs.ArchivePreQuadShardS009
import Kepler.Graphs.ArchivePreQuadShardS010
import Kepler.Graphs.ArchivePreQuadShardS011
import Kepler.Graphs.ArchivePreQuadShardS012

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Quad `archivePre` 全类闭合：1253 项，13 分片。 -/
theorem archivePreQuadAll : (QuadData).all (fun a => preIsoTestB a) = true :=
  all_of_take_drop_b archivePreQuadS000
      (all_drop_of_split_b archivePreQuadS001
      (all_drop_of_split_b archivePreQuadS002
      (all_drop_of_split_b archivePreQuadS003
      (all_drop_of_split_b archivePreQuadS004
      (all_drop_of_split_b archivePreQuadS005
      (all_drop_of_split_b archivePreQuadS006
      (all_drop_of_split_b archivePreQuadS007
      (all_drop_of_split_b archivePreQuadS008
      (all_drop_of_split_b archivePreQuadS009
      (all_drop_of_split_b archivePreQuadS010
      (all_drop_of_split_b archivePreQuadS011
      (archivePreQuadS012))))))))))))

#print axioms archivePreQuadAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
