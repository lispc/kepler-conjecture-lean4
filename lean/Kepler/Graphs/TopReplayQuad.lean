/-
  Kepler/Graphs/TopReplayQuad — `topReplay` / Quad 全类组合（机器生成）。

  生成器：`lean/scripts/gen_top_shards.py`；请勿手改。
  纯内核：6 个 `decide +kernel` 分片经 `all_of_take_drop_b` 串成原陈述。
-/
import Kepler.Graphs.TopReplayQuadShardS000
import Kepler.Graphs.TopReplayQuadShardS001
import Kepler.Graphs.TopReplayQuadShardS002
import Kepler.Graphs.TopReplayQuadShardS003
import Kepler.Graphs.TopReplayQuadShardS004
import Kepler.Graphs.TopReplayQuadShardS005

namespace Kepler.Graphs

set_option maxRecDepth 1000000 in
/-- Quad `topReplay` 全类闭合：286 项，6 分片。 -/
theorem topReplayQuadAll : (List.range QuadTop.length).all (fun i => decide (next_tame 1 QuadTop[i]! = (QuadTopChildren[i]!).map (resolveChild QuadTop QuadFrontier))) = true :=
  all_of_take_drop_b topReplayQuadS000
      (all_drop_of_split_b topReplayQuadS001
      (all_drop_of_split_b topReplayQuadS002
      (all_drop_of_split_b topReplayQuadS003
      (all_drop_of_split_b topReplayQuadS004
      (topReplayQuadS005)))))

#print axioms topReplayQuadAll

#print axioms all_of_take_drop_b
#print axioms all_drop_of_split_b

end Kepler.Graphs
