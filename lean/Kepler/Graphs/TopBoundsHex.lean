/-
  Kepler/Graphs/TopBoundsHex — `topBounds` / Hex 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：14 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.TopBoundsHexShardS000
import Kepler.Graphs.TopBoundsHexShardS001
import Kepler.Graphs.TopBoundsHexShardS002
import Kepler.Graphs.TopBoundsHexShardS003
import Kepler.Graphs.TopBoundsHexShardS004
import Kepler.Graphs.TopBoundsHexShardS005
import Kepler.Graphs.TopBoundsHexShardS006
import Kepler.Graphs.TopBoundsHexShardS007
import Kepler.Graphs.TopBoundsHexShardS008
import Kepler.Graphs.TopBoundsHexShardS009
import Kepler.Graphs.TopBoundsHexShardS010
import Kepler.Graphs.TopBoundsHexShardS011
import Kepler.Graphs.TopBoundsHexShardS012
import Kepler.Graphs.TopBoundsHexShardS013

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Hex `topBounds` 全类闭合：1363 项，14 分片。 -/
theorem topBoundsHexAll : (List.range HexTopChildren.length).all (fun i => (HexTopChildren[i]!).all (fun t => (t.1 && decide (t.2 < HexFrontier.length)) || (!t.1 && decide (t.2 < HexTop.length)))) = true :=
  all_of_take_drop_b topBoundsHexS000
      (all_drop_of_split_b topBoundsHexS001
      (all_drop_of_split_b topBoundsHexS002
      (all_drop_of_split_b topBoundsHexS003
      (all_drop_of_split_b topBoundsHexS004
      (all_drop_of_split_b topBoundsHexS005
      (all_drop_of_split_b topBoundsHexS006
      (all_drop_of_split_b topBoundsHexS007
      (all_drop_of_split_b topBoundsHexS008
      (all_drop_of_split_b topBoundsHexS009
      (all_drop_of_split_b topBoundsHexS010
      (all_drop_of_split_b topBoundsHexS011
      (all_drop_of_split_b topBoundsHexS012
      (topBoundsHexS013)))))))))))))

#print axioms topBoundsHexAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
