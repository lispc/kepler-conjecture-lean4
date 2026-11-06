/-
  Kepler/Assembly/GoodListShardPentS19 — good_list 量产分片（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`（slice=100，kernel 重切）；请勿手改，
  重新生成会覆盖。覆盖 PentData 第 [1900, 2000) 图（全类 16080 图）。
  信任模型：kernel `decide +kernel`（无 native_decide；100 图/片）
-/
import Kepler.Assembly.GoodListDefs

open Kepler.Graphs

namespace Kepler.Assembly

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`(PentData.drop 1900).take 100` 上 `goodListB` 全真。 -/
theorem goodListPentS19 : ((PentData.drop 1900).take 100).all goodListB = true := by
  decide +kernel

#print axioms goodListPentS19

end Kepler.Assembly
