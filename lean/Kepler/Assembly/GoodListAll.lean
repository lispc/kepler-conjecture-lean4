/-
  Kepler/Assembly/GoodListAll — 全 archive good_list 组合定理（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`；请勿手改。
  本模块纯内核：把各分片（native 或 kernel 切片）定理经 `all_of_take_drop`
  串成逐类总定理，最终 `goodListArchiveAll : AllGoodList tameArchiveLists`
  （HOL `ALL good_list tame_archive_lists`，the_kepler_conjecture.hl 装配的 good_list 支）。
-/
import Kepler.Assembly.GoodListShardTriS00
import Kepler.Assembly.GoodListShardQuadS00
import Kepler.Assembly.GoodListShardQuadS01
import Kepler.Assembly.GoodListShardQuadS02
import Kepler.Assembly.GoodListShardQuadS03
import Kepler.Assembly.GoodListShardQuadS04
import Kepler.Assembly.GoodListShardQuadS05
import Kepler.Assembly.GoodListShardQuadS06
import Kepler.Assembly.GoodListShardQuadS07
import Kepler.Assembly.GoodListShardQuadS08
import Kepler.Assembly.GoodListShardQuadS09
import Kepler.Assembly.GoodListShardQuadS10
import Kepler.Assembly.GoodListShardQuadS11
import Kepler.Assembly.GoodListShardQuadS12
import Kepler.Assembly.GoodListShardPent00
import Kepler.Assembly.GoodListShardPent01
import Kepler.Assembly.GoodListShardPent02
import Kepler.Assembly.GoodListShardPent03
import Kepler.Assembly.GoodListShardPent04
import Kepler.Assembly.GoodListShardPent05
import Kepler.Assembly.GoodListShardPent06
import Kepler.Assembly.GoodListShardPent07
import Kepler.Assembly.GoodListShardPent08
import Kepler.Assembly.GoodListShardPent09
import Kepler.Assembly.GoodListShardPent10
import Kepler.Assembly.GoodListShardPent11
import Kepler.Assembly.GoodListShardPent12
import Kepler.Assembly.GoodListShardPent13
import Kepler.Assembly.GoodListShardPent14
import Kepler.Assembly.GoodListShardPent15
import Kepler.Assembly.GoodListShardPent16
import Kepler.Assembly.GoodListShardHex00
import Kepler.Assembly.GoodListShardHex01
import Kepler.Assembly.GoodListShardHex02

open Kepler.Graphs

namespace Kepler.Assembly

set_option maxRecDepth 1000000 in
/-- Tri 类闭合：9 图，1 分片。 -/
theorem allGoodTri : TriData.all goodListB = true :=
  goodListTriS00

set_option maxRecDepth 1000000 in
/-- Quad 类闭合：1253 图，13 分片。 -/
theorem allGoodQuad : QuadData.all goodListB = true :=
  all_of_take_drop goodListQuadS00
      (all_of_take_drop goodListQuadS01
      (all_of_take_drop goodListQuadS02
      (all_of_take_drop goodListQuadS03
      (all_of_take_drop goodListQuadS04
      (all_of_take_drop goodListQuadS05
      (all_of_take_drop goodListQuadS06
      (all_of_take_drop goodListQuadS07
      (all_of_take_drop goodListQuadS08
      (all_of_take_drop goodListQuadS09
      (all_of_take_drop goodListQuadS10
      (all_of_take_drop goodListQuadS11
      (goodListQuadS12))))))))))))

set_option maxRecDepth 1000000 in
/-- Pent 类闭合：16080 图，17 分片。 -/
theorem allGoodPent : PentData.all goodListB = true :=
  all_of_take_drop goodListPent00
      (all_of_take_drop goodListPent01
      (all_of_take_drop goodListPent02
      (all_of_take_drop goodListPent03
      (all_of_take_drop goodListPent04
      (all_of_take_drop goodListPent05
      (all_of_take_drop goodListPent06
      (all_of_take_drop goodListPent07
      (all_of_take_drop goodListPent08
      (all_of_take_drop goodListPent09
      (all_of_take_drop goodListPent10
      (all_of_take_drop goodListPent11
      (all_of_take_drop goodListPent12
      (all_of_take_drop goodListPent13
      (all_of_take_drop goodListPent14
      (all_of_take_drop goodListPent15
      (goodListPent16))))))))))))))))

set_option maxRecDepth 1000000 in
/-- Hex 类闭合：2373 图，3 分片。 -/
theorem allGoodHex : HexData.all goodListB = true :=
  all_of_take_drop goodListHex00
      (all_of_take_drop goodListHex01
      (goodListHex02))

/-- HOL `ALL good_list tame_archive_lists`：全 archive 逐图 `good_list`。 -/
theorem goodListArchiveAll : AllGoodList tameArchiveLists := by
  intro L hL
  rw [tameArchiveLists, List.mem_append, List.mem_append, List.mem_append] at hL
  -- 重写后 hL 为左嵌套：((L ∈ TriData ∨ L ∈ QuadData) ∨ L ∈ PentData) ∨ L ∈ HexData
  cases hL with
  | inl hL => cases hL with
    | inl hL => cases hL with
      | inl hT => exact good_of_all allGoodTri L hT
      | inr hQ => exact good_of_all allGoodQuad L hQ
    | inr hP => exact good_of_all allGoodPent L hP
  | inr hH => exact good_of_all allGoodHex L hH

#print axioms goodListArchiveAll

end Kepler.Assembly
