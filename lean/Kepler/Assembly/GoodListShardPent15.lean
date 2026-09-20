/-
  Kepler/Assembly/GoodListShardPent15 — good_list 量产分片（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`（slice=1000）；请勿手改，
  重新生成会覆盖。覆盖 PentData 第 [15000, 16000) 图（全类 16080 图）。
  信任模型：native_decide（DECISIONS.md 2026-08-10 scoped exception，
  2026-09-19 扩展至 Kepler.Assembly.GoodList*）。
-/
import Kepler.Assembly.GoodListDefs

open Kepler.Graphs

namespace Kepler.Assembly

/-- 分片闭合：`(PentData.drop 15000).take 1000` 上 `goodListB` 全真。 -/
theorem goodListPent15 : ((PentData.drop 15000).take 1000).all goodListB = true := by
  native_decide

#print axioms goodListPent15

end Kepler.Assembly
