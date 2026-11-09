/-
  Kepler/Graphs/TopReplayPent — `topReplay` / Pent 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：31 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.TopReplayPentShardS000
import Kepler.Graphs.TopReplayPentShardS001
import Kepler.Graphs.TopReplayPentShardS002
import Kepler.Graphs.TopReplayPentShardS003
import Kepler.Graphs.TopReplayPentShardS004
import Kepler.Graphs.TopReplayPentShardS005
import Kepler.Graphs.TopReplayPentShardS006
import Kepler.Graphs.TopReplayPentShardS007
import Kepler.Graphs.TopReplayPentShardS008
import Kepler.Graphs.TopReplayPentShardS009
import Kepler.Graphs.TopReplayPentShardS010
import Kepler.Graphs.TopReplayPentShardS011
import Kepler.Graphs.TopReplayPentShardS012
import Kepler.Graphs.TopReplayPentShardS013
import Kepler.Graphs.TopReplayPentShardS014
import Kepler.Graphs.TopReplayPentShardS015
import Kepler.Graphs.TopReplayPentShardS016
import Kepler.Graphs.TopReplayPentShardS017
import Kepler.Graphs.TopReplayPentShardS018
import Kepler.Graphs.TopReplayPentShardS019
import Kepler.Graphs.TopReplayPentShardS020
import Kepler.Graphs.TopReplayPentShardS021
import Kepler.Graphs.TopReplayPentShardS022
import Kepler.Graphs.TopReplayPentShardS023
import Kepler.Graphs.TopReplayPentShardS024
import Kepler.Graphs.TopReplayPentShardS025
import Kepler.Graphs.TopReplayPentShardS026
import Kepler.Graphs.TopReplayPentShardS027
import Kepler.Graphs.TopReplayPentShardS028
import Kepler.Graphs.TopReplayPentShardS029
import Kepler.Graphs.TopReplayPentShardS030

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Pent `topReplay` 全类闭合：754 项，31 分片。 -/
theorem topReplayPentAll : (List.range PentTop.length).all (fun i => decide (next_tame 2 PentTop[i]! = (PentTopChildren[i]!).map (resolveChild PentTop PentFrontier))) = true :=
  all_of_take_drop_b topReplayPentS000
      (all_drop_of_split_b topReplayPentS001
      (all_drop_of_split_b topReplayPentS002
      (all_drop_of_split_b topReplayPentS003
      (all_drop_of_split_b topReplayPentS004
      (all_drop_of_split_b topReplayPentS005
      (all_drop_of_split_b topReplayPentS006
      (all_drop_of_split_b topReplayPentS007
      (all_drop_of_split_b topReplayPentS008
      (all_drop_of_split_b topReplayPentS009
      (all_drop_of_split_b topReplayPentS010
      (all_drop_of_split_b topReplayPentS011
      (all_drop_of_split_b topReplayPentS012
      (all_drop_of_split_b topReplayPentS013
      (all_drop_of_split_b topReplayPentS014
      (all_drop_of_split_b topReplayPentS015
      (all_drop_of_split_b topReplayPentS016
      (all_drop_of_split_b topReplayPentS017
      (all_drop_of_split_b topReplayPentS018
      (all_drop_of_split_b topReplayPentS019
      (all_drop_of_split_b topReplayPentS020
      (all_drop_of_split_b topReplayPentS021
      (all_drop_of_split_b topReplayPentS022
      (all_drop_of_split_b topReplayPentS023
      (all_drop_of_split_b topReplayPentS024
      (all_drop_of_split_b topReplayPentS025
      (all_drop_of_split_b topReplayPentS026
      (all_drop_of_split_b topReplayPentS027
      (all_drop_of_split_b topReplayPentS028
      (all_drop_of_split_b topReplayPentS029
      (topReplayPentS030))))))))))))))))))))))))))))))

#print axioms topReplayPentAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
