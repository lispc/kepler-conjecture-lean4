/-
  Kepler/Graphs/TopReplayHex — `topReplay` / Hex 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：55 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.TopReplayHexShardS000
import Kepler.Graphs.TopReplayHexShardS001
import Kepler.Graphs.TopReplayHexShardS002
import Kepler.Graphs.TopReplayHexShardS003
import Kepler.Graphs.TopReplayHexShardS004
import Kepler.Graphs.TopReplayHexShardS005
import Kepler.Graphs.TopReplayHexShardS006
import Kepler.Graphs.TopReplayHexShardS007
import Kepler.Graphs.TopReplayHexShardS008
import Kepler.Graphs.TopReplayHexShardS009
import Kepler.Graphs.TopReplayHexShardS010
import Kepler.Graphs.TopReplayHexShardS011
import Kepler.Graphs.TopReplayHexShardS012
import Kepler.Graphs.TopReplayHexShardS013
import Kepler.Graphs.TopReplayHexShardS014
import Kepler.Graphs.TopReplayHexShardS015
import Kepler.Graphs.TopReplayHexShardS016
import Kepler.Graphs.TopReplayHexShardS017
import Kepler.Graphs.TopReplayHexShardS018
import Kepler.Graphs.TopReplayHexShardS019
import Kepler.Graphs.TopReplayHexShardS020
import Kepler.Graphs.TopReplayHexShardS021
import Kepler.Graphs.TopReplayHexShardS022
import Kepler.Graphs.TopReplayHexShardS023
import Kepler.Graphs.TopReplayHexShardS024
import Kepler.Graphs.TopReplayHexShardS025
import Kepler.Graphs.TopReplayHexShardS026
import Kepler.Graphs.TopReplayHexShardS027
import Kepler.Graphs.TopReplayHexShardS028
import Kepler.Graphs.TopReplayHexShardS029
import Kepler.Graphs.TopReplayHexShardS030
import Kepler.Graphs.TopReplayHexShardS031
import Kepler.Graphs.TopReplayHexShardS032
import Kepler.Graphs.TopReplayHexShardS033
import Kepler.Graphs.TopReplayHexShardS034
import Kepler.Graphs.TopReplayHexShardS035
import Kepler.Graphs.TopReplayHexShardS036
import Kepler.Graphs.TopReplayHexShardS037
import Kepler.Graphs.TopReplayHexShardS038
import Kepler.Graphs.TopReplayHexShardS039
import Kepler.Graphs.TopReplayHexShardS040
import Kepler.Graphs.TopReplayHexShardS041
import Kepler.Graphs.TopReplayHexShardS042
import Kepler.Graphs.TopReplayHexShardS043
import Kepler.Graphs.TopReplayHexShardS044
import Kepler.Graphs.TopReplayHexShardS045
import Kepler.Graphs.TopReplayHexShardS046
import Kepler.Graphs.TopReplayHexShardS047
import Kepler.Graphs.TopReplayHexShardS048
import Kepler.Graphs.TopReplayHexShardS049
import Kepler.Graphs.TopReplayHexShardS050
import Kepler.Graphs.TopReplayHexShardS051
import Kepler.Graphs.TopReplayHexShardS052
import Kepler.Graphs.TopReplayHexShardS053
import Kepler.Graphs.TopReplayHexShardS054

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Hex `topReplay` 全类闭合：1363 项，55 分片。 -/
theorem topReplayHexAll : (List.range HexTop.length).all (fun i => decide (next_tame 3 HexTop[i]! = (HexTopChildren[i]!).map (resolveChild HexTop HexFrontier))) = true :=
  all_of_take_drop_b topReplayHexS000
      (all_drop_of_split_b topReplayHexS001
      (all_drop_of_split_b topReplayHexS002
      (all_drop_of_split_b topReplayHexS003
      (all_drop_of_split_b topReplayHexS004
      (all_drop_of_split_b topReplayHexS005
      (all_drop_of_split_b topReplayHexS006
      (all_drop_of_split_b topReplayHexS007
      (all_drop_of_split_b topReplayHexS008
      (all_drop_of_split_b topReplayHexS009
      (all_drop_of_split_b topReplayHexS010
      (all_drop_of_split_b topReplayHexS011
      (all_drop_of_split_b topReplayHexS012
      (all_drop_of_split_b topReplayHexS013
      (all_drop_of_split_b topReplayHexS014
      (all_drop_of_split_b topReplayHexS015
      (all_drop_of_split_b topReplayHexS016
      (all_drop_of_split_b topReplayHexS017
      (all_drop_of_split_b topReplayHexS018
      (all_drop_of_split_b topReplayHexS019
      (all_drop_of_split_b topReplayHexS020
      (all_drop_of_split_b topReplayHexS021
      (all_drop_of_split_b topReplayHexS022
      (all_drop_of_split_b topReplayHexS023
      (all_drop_of_split_b topReplayHexS024
      (all_drop_of_split_b topReplayHexS025
      (all_drop_of_split_b topReplayHexS026
      (all_drop_of_split_b topReplayHexS027
      (all_drop_of_split_b topReplayHexS028
      (all_drop_of_split_b topReplayHexS029
      (all_drop_of_split_b topReplayHexS030
      (all_drop_of_split_b topReplayHexS031
      (all_drop_of_split_b topReplayHexS032
      (all_drop_of_split_b topReplayHexS033
      (all_drop_of_split_b topReplayHexS034
      (all_drop_of_split_b topReplayHexS035
      (all_drop_of_split_b topReplayHexS036
      (all_drop_of_split_b topReplayHexS037
      (all_drop_of_split_b topReplayHexS038
      (all_drop_of_split_b topReplayHexS039
      (all_drop_of_split_b topReplayHexS040
      (all_drop_of_split_b topReplayHexS041
      (all_drop_of_split_b topReplayHexS042
      (all_drop_of_split_b topReplayHexS043
      (all_drop_of_split_b topReplayHexS044
      (all_drop_of_split_b topReplayHexS045
      (all_drop_of_split_b topReplayHexS046
      (all_drop_of_split_b topReplayHexS047
      (all_drop_of_split_b topReplayHexS048
      (all_drop_of_split_b topReplayHexS049
      (all_drop_of_split_b topReplayHexS050
      (all_drop_of_split_b topReplayHexS051
      (all_drop_of_split_b topReplayHexS052
      (all_drop_of_split_b topReplayHexS053
      (topReplayHexS054))))))))))))))))))))))))))))))))))))))))))))))))))))))

#print axioms topReplayHexAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
