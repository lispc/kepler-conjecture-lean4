/-
  Kepler/Graphs/ArchivePreHex — `archivePre` / Hex 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：24 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.ArchivePreHexShardS000
import Kepler.Graphs.ArchivePreHexShardS001
import Kepler.Graphs.ArchivePreHexShardS002
import Kepler.Graphs.ArchivePreHexShardS003
import Kepler.Graphs.ArchivePreHexShardS004
import Kepler.Graphs.ArchivePreHexShardS005
import Kepler.Graphs.ArchivePreHexShardS006
import Kepler.Graphs.ArchivePreHexShardS007
import Kepler.Graphs.ArchivePreHexShardS008
import Kepler.Graphs.ArchivePreHexShardS009
import Kepler.Graphs.ArchivePreHexShardS010
import Kepler.Graphs.ArchivePreHexShardS011
import Kepler.Graphs.ArchivePreHexShardS012
import Kepler.Graphs.ArchivePreHexShardS013
import Kepler.Graphs.ArchivePreHexShardS014
import Kepler.Graphs.ArchivePreHexShardS015
import Kepler.Graphs.ArchivePreHexShardS016
import Kepler.Graphs.ArchivePreHexShardS017
import Kepler.Graphs.ArchivePreHexShardS018
import Kepler.Graphs.ArchivePreHexShardS019
import Kepler.Graphs.ArchivePreHexShardS020
import Kepler.Graphs.ArchivePreHexShardS021
import Kepler.Graphs.ArchivePreHexShardS022
import Kepler.Graphs.ArchivePreHexShardS023

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Hex `archivePre` 全类闭合：2373 项，24 分片。 -/
theorem archivePreHexAll : (HexData).all (fun a => preIsoTestB a) = true :=
  all_of_take_drop_b archivePreHexS000
      (all_drop_of_split_b archivePreHexS001
      (all_drop_of_split_b archivePreHexS002
      (all_drop_of_split_b archivePreHexS003
      (all_drop_of_split_b archivePreHexS004
      (all_drop_of_split_b archivePreHexS005
      (all_drop_of_split_b archivePreHexS006
      (all_drop_of_split_b archivePreHexS007
      (all_drop_of_split_b archivePreHexS008
      (all_drop_of_split_b archivePreHexS009
      (all_drop_of_split_b archivePreHexS010
      (all_drop_of_split_b archivePreHexS011
      (all_drop_of_split_b archivePreHexS012
      (all_drop_of_split_b archivePreHexS013
      (all_drop_of_split_b archivePreHexS014
      (all_drop_of_split_b archivePreHexS015
      (all_drop_of_split_b archivePreHexS016
      (all_drop_of_split_b archivePreHexS017
      (all_drop_of_split_b archivePreHexS018
      (all_drop_of_split_b archivePreHexS019
      (all_drop_of_split_b archivePreHexS020
      (all_drop_of_split_b archivePreHexS021
      (all_drop_of_split_b archivePreHexS022
      (archivePreHexS023)))))))))))))))))))))))

#print axioms archivePreHexAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
