/-
  Kepler/Assembly/GoodListShardQuadS07 — good_list 量产分片（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`（slice=100，kernel 重切）；请勿手改，
  重新生成会覆盖。覆盖 QuadData 第 [700, 800) 图（全类 1253 图）。
  信任模型：kernel `decide +kernel`（无 native_decide；100 图/片）
-/
import Kepler.Assembly.GoodListDefs

open Kepler.Graphs

namespace Kepler.Assembly

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- 分片闭合：`(QuadData.drop 700).take 100` 上 `goodListB` 全真。 -/
theorem goodListQuadS07 : ((QuadData.drop 700).take 100).all goodListB = true := by
  decide +kernel

#print axioms goodListQuadS07

end Kepler.Assembly
