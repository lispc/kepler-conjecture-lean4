/-
  Kepler.LP.W6Align.Bulk — 分段切片对账（O(n) 批形；与逐图 align_* 互为
  冗余校验：同一条对齐链的两种内核检查路线）。

  【2026-10-28 用户裁决：Bulk 冗余校验不做了】逐图 align_00000..19714 已
  承担同一条对齐链的内核验证；本模块原 10 条分片大定理（alignBulk_00..09，
  单条 decide 覆盖 2000 图）因最后片心跳爆顶（拆分后仍数小时级）停做。
  如日后需要批形冗余校验，由 W6-D 以小分片形式再生（生成器
  pipeline/lp/gen_w6a_align.py 需同步补分片发射）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。
-/
import Kepler.LP.W6Align.Basic

namespace Kepler.LP.W6Align

-- 本模块暂无常量：见头部裁决注记。

end Kepler.LP.W6Align
