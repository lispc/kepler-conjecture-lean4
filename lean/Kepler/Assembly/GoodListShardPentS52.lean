/-
  Kepler/Assembly/GoodListShardPentS52 — good_list 量产分片（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`（slice=100，kernel 重切）；请勿手改，
  重新生成会覆盖。覆盖 PentData 第 [5200, 5300) 图（全类 16080 图）。
  信任模型：kernel `decide +kernel`（无 native_decide；100 图/片）
-/
import Kepler.Assembly.GoodListDefs

open Kepler.Graphs

namespace Kepler.Assembly

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`(PentData.drop 5200).take 100` 上 `goodListB` 全真。 -/
theorem goodListPentS52 : ((PentData.drop 5200).take 100).all goodListB = true := by
  decide +kernel

#print axioms goodListPentS52

end Kepler.Assembly
