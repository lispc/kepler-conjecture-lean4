/-
  Kepler.LP.W6Align — W6-A 逐图 archive 对齐数据模块根（车道 hlp-w6a）。

  机器生成：`pipeline/lp/gen_w6a_align.py`；不要手改。

  内容：
  * `CertOf` + `decodeHypermap`（HOL convert_to_list 直译）— Basic；
  * 正/逆 archive 对齐表 `certArchIdx` / `invCertIdx` + 族普查
    `usedFamilies` — Table；
  * 逐图对齐定理 `align_00000..align_19714`（19715 条，每条内核
    `decide`）— Align00..Align19；
  * 分段切片对账 `alignBulk_*` — Bulk。

  验收锚：`w6align`（表事实总合取）；公理面 = `#print axioms` 标准三
  （构建日志/探针核对）。本模块不被任何既有文件 import；独立构建：
  `lake build Kepler.LP.W6Align`。
-/
import Kepler.LP.W6Align.Basic
import Kepler.LP.W6Align.Table
import Kepler.LP.W6Align.Align00
import Kepler.LP.W6Align.Align01
import Kepler.LP.W6Align.Align02
import Kepler.LP.W6Align.Align03
import Kepler.LP.W6Align.Align04
import Kepler.LP.W6Align.Align05
import Kepler.LP.W6Align.Align06
import Kepler.LP.W6Align.Align07
import Kepler.LP.W6Align.Align08
import Kepler.LP.W6Align.Align09
import Kepler.LP.W6Align.Align10
import Kepler.LP.W6Align.Align11
import Kepler.LP.W6Align.Align12
import Kepler.LP.W6Align.Align13
import Kepler.LP.W6Align.Align14
import Kepler.LP.W6Align.Align15
import Kepler.LP.W6Align.Align16
import Kepler.LP.W6Align.Align17
import Kepler.LP.W6Align.Align18
import Kepler.LP.W6Align.Align19
import Kepler.LP.W6Align.Bulk

set_option maxRecDepth 4000000

namespace Kepler.LP.W6Align
open Kepler.Assembly Kepler.Text.LP Kepler.Text.LP.W6Data

theorem certArchIdx_length : certArchIdx.length = 19715 := by decide

theorem certArchIdx_bounds : certArchIdx.all (· < 19715) = true := by decide

theorem invCertIdx_length : invCertIdx.length = 19715 := by decide

theorem invCertIdx_bounds : invCertIdx.all (· < 19715) = true := by decide

/-- 表事实总合取（W6-B 消费入口）。 -/
theorem w6align :
    dataAll.length = 19715 ∧
    certArchIdx.length = 19715 ∧
    certArchIdx.all (· < 19715) = true ∧
    invCertIdx.length = 19715 ∧
    usedFamilyIds.length = 182 := by
  refine ⟨?_, certArchIdx_length, certArchIdx_bounds, invCertIdx_length, ?_⟩
  · exact W6Data.dataAll_length
  · exact usedFamilyIds_length

end Kepler.LP.W6Align
