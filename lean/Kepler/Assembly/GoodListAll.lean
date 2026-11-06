/-
  Kepler/Assembly/GoodListAll — 全 archive good_list 组合定理（P6-C，机器生成）。

  生成器：`lean/scripts/gen_goodlist_shards.py`；请勿手改。
  本模块纯内核：把各分片（native 或 kernel 切片）定理经 `all_of_take_drop`
  串成逐类总定理，最终 `goodListArchiveAll : AllGoodList tameArchiveLists`
  （HOL `ALL good_list tame_archive_lists`，the_kepler_conjecture.hl 装配的 good_list 支）。
-/
import Kepler.Assembly.GoodListChain
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
import Kepler.Assembly.GoodListShardPentS00
import Kepler.Assembly.GoodListShardPentS01
import Kepler.Assembly.GoodListShardPentS02
import Kepler.Assembly.GoodListShardPentS03
import Kepler.Assembly.GoodListShardPentS04
import Kepler.Assembly.GoodListShardPentS05
import Kepler.Assembly.GoodListShardPentS06
import Kepler.Assembly.GoodListShardPentS07
import Kepler.Assembly.GoodListShardPentS08
import Kepler.Assembly.GoodListShardPentS09
import Kepler.Assembly.GoodListShardPentS10
import Kepler.Assembly.GoodListShardPentS11
import Kepler.Assembly.GoodListShardPentS12
import Kepler.Assembly.GoodListShardPentS13
import Kepler.Assembly.GoodListShardPentS14
import Kepler.Assembly.GoodListShardPentS15
import Kepler.Assembly.GoodListShardPentS16
import Kepler.Assembly.GoodListShardPentS17
import Kepler.Assembly.GoodListShardPentS18
import Kepler.Assembly.GoodListShardPentS19
import Kepler.Assembly.GoodListShardPentS20
import Kepler.Assembly.GoodListShardPentS21
import Kepler.Assembly.GoodListShardPentS22
import Kepler.Assembly.GoodListShardPentS23
import Kepler.Assembly.GoodListShardPentS24
import Kepler.Assembly.GoodListShardPentS25
import Kepler.Assembly.GoodListShardPentS26
import Kepler.Assembly.GoodListShardPentS27
import Kepler.Assembly.GoodListShardPentS28
import Kepler.Assembly.GoodListShardPentS29
import Kepler.Assembly.GoodListShardPentS30
import Kepler.Assembly.GoodListShardPentS31
import Kepler.Assembly.GoodListShardPentS32
import Kepler.Assembly.GoodListShardPentS33
import Kepler.Assembly.GoodListShardPentS34
import Kepler.Assembly.GoodListShardPentS35
import Kepler.Assembly.GoodListShardPentS36
import Kepler.Assembly.GoodListShardPentS37
import Kepler.Assembly.GoodListShardPentS38
import Kepler.Assembly.GoodListShardPentS39
import Kepler.Assembly.GoodListShardPentS40
import Kepler.Assembly.GoodListShardPentS41
import Kepler.Assembly.GoodListShardPentS42
import Kepler.Assembly.GoodListShardPentS43
import Kepler.Assembly.GoodListShardPentS44
import Kepler.Assembly.GoodListShardPentS45
import Kepler.Assembly.GoodListShardPentS46
import Kepler.Assembly.GoodListShardPentS47
import Kepler.Assembly.GoodListShardPentS48
import Kepler.Assembly.GoodListShardPentS49
import Kepler.Assembly.GoodListShardPentS50
import Kepler.Assembly.GoodListShardPentS51
import Kepler.Assembly.GoodListShardPentS52
import Kepler.Assembly.GoodListShardPentS53
import Kepler.Assembly.GoodListShardPentS54
import Kepler.Assembly.GoodListShardPentS55
import Kepler.Assembly.GoodListShardPentS56
import Kepler.Assembly.GoodListShardPentS57
import Kepler.Assembly.GoodListShardPentS58
import Kepler.Assembly.GoodListShardPentS59
import Kepler.Assembly.GoodListShardPentS60
import Kepler.Assembly.GoodListShardPentS61
import Kepler.Assembly.GoodListShardPentS62
import Kepler.Assembly.GoodListShardPentS63
import Kepler.Assembly.GoodListShardPentS64
import Kepler.Assembly.GoodListShardPentS65
import Kepler.Assembly.GoodListShardPentS66
import Kepler.Assembly.GoodListShardPentS67
import Kepler.Assembly.GoodListShardPentS68
import Kepler.Assembly.GoodListShardPentS69
import Kepler.Assembly.GoodListShardPentS70
import Kepler.Assembly.GoodListShardPentS71
import Kepler.Assembly.GoodListShardPentS72
import Kepler.Assembly.GoodListShardPentS73
import Kepler.Assembly.GoodListShardPentS74
import Kepler.Assembly.GoodListShardPentS75
import Kepler.Assembly.GoodListShardPentS76
import Kepler.Assembly.GoodListShardPentS77
import Kepler.Assembly.GoodListShardPentS78
import Kepler.Assembly.GoodListShardPentS79
import Kepler.Assembly.GoodListShardPentS80
import Kepler.Assembly.GoodListShardPentS81
import Kepler.Assembly.GoodListShardPentS82
import Kepler.Assembly.GoodListShardPentS83
import Kepler.Assembly.GoodListShardPentS84
import Kepler.Assembly.GoodListShardPentS85
import Kepler.Assembly.GoodListShardPentS86
import Kepler.Assembly.GoodListShardPentS87
import Kepler.Assembly.GoodListShardPentS88
import Kepler.Assembly.GoodListShardPentS89
import Kepler.Assembly.GoodListShardPentS90
import Kepler.Assembly.GoodListShardPentS91
import Kepler.Assembly.GoodListShardPentS92
import Kepler.Assembly.GoodListShardPentS93
import Kepler.Assembly.GoodListShardPentS94
import Kepler.Assembly.GoodListShardPentS95
import Kepler.Assembly.GoodListShardPentS96
import Kepler.Assembly.GoodListShardPentS97
import Kepler.Assembly.GoodListShardPentS98
import Kepler.Assembly.GoodListShardPentS99
import Kepler.Assembly.GoodListShardPentS100
import Kepler.Assembly.GoodListShardPentS101
import Kepler.Assembly.GoodListShardPentS102
import Kepler.Assembly.GoodListShardPentS103
import Kepler.Assembly.GoodListShardPentS104
import Kepler.Assembly.GoodListShardPentS105
import Kepler.Assembly.GoodListShardPentS106
import Kepler.Assembly.GoodListShardPentS107
import Kepler.Assembly.GoodListShardPentS108
import Kepler.Assembly.GoodListShardPentS109
import Kepler.Assembly.GoodListShardPentS110
import Kepler.Assembly.GoodListShardPentS111
import Kepler.Assembly.GoodListShardPentS112
import Kepler.Assembly.GoodListShardPentS113
import Kepler.Assembly.GoodListShardPentS114
import Kepler.Assembly.GoodListShardPentS115
import Kepler.Assembly.GoodListShardPentS116
import Kepler.Assembly.GoodListShardPentS117
import Kepler.Assembly.GoodListShardPentS118
import Kepler.Assembly.GoodListShardPentS119
import Kepler.Assembly.GoodListShardPentS120
import Kepler.Assembly.GoodListShardPentS121
import Kepler.Assembly.GoodListShardPentS122
import Kepler.Assembly.GoodListShardPentS123
import Kepler.Assembly.GoodListShardPentS124
import Kepler.Assembly.GoodListShardPentS125
import Kepler.Assembly.GoodListShardPentS126
import Kepler.Assembly.GoodListShardPentS127
import Kepler.Assembly.GoodListShardPentS128
import Kepler.Assembly.GoodListShardPentS129
import Kepler.Assembly.GoodListShardPentS130
import Kepler.Assembly.GoodListShardPentS131
import Kepler.Assembly.GoodListShardPentS132
import Kepler.Assembly.GoodListShardPentS133
import Kepler.Assembly.GoodListShardPentS134
import Kepler.Assembly.GoodListShardPentS135
import Kepler.Assembly.GoodListShardPentS136
import Kepler.Assembly.GoodListShardPentS137
import Kepler.Assembly.GoodListShardPentS138
import Kepler.Assembly.GoodListShardPentS139
import Kepler.Assembly.GoodListShardPentS140
import Kepler.Assembly.GoodListShardPentS141
import Kepler.Assembly.GoodListShardPentS142
import Kepler.Assembly.GoodListShardPentS143
import Kepler.Assembly.GoodListShardPentS144
import Kepler.Assembly.GoodListShardPentS145
import Kepler.Assembly.GoodListShardPentS146
import Kepler.Assembly.GoodListShardPentS147
import Kepler.Assembly.GoodListShardPentS148
import Kepler.Assembly.GoodListShardPentS149
import Kepler.Assembly.GoodListShardPentS150
import Kepler.Assembly.GoodListShardPentS151
import Kepler.Assembly.GoodListShardPentS152
import Kepler.Assembly.GoodListShardPentS153
import Kepler.Assembly.GoodListShardPentS154
import Kepler.Assembly.GoodListShardPentS155
import Kepler.Assembly.GoodListShardPentS156
import Kepler.Assembly.GoodListShardPentS157
import Kepler.Assembly.GoodListShardPentS158
import Kepler.Assembly.GoodListShardPentS159
import Kepler.Assembly.GoodListShardPentS160
import Kepler.Assembly.GoodListShardHexS00
import Kepler.Assembly.GoodListShardHexS01
import Kepler.Assembly.GoodListShardHexS02
import Kepler.Assembly.GoodListShardHexS03
import Kepler.Assembly.GoodListShardHexS04
import Kepler.Assembly.GoodListShardHexS05
import Kepler.Assembly.GoodListShardHexS06
import Kepler.Assembly.GoodListShardHexS07
import Kepler.Assembly.GoodListShardHexS08
import Kepler.Assembly.GoodListShardHexS09
import Kepler.Assembly.GoodListShardHexS10
import Kepler.Assembly.GoodListShardHexS11
import Kepler.Assembly.GoodListShardHexS12
import Kepler.Assembly.GoodListShardHexS13
import Kepler.Assembly.GoodListShardHexS14
import Kepler.Assembly.GoodListShardHexS15
import Kepler.Assembly.GoodListShardHexS16
import Kepler.Assembly.GoodListShardHexS17
import Kepler.Assembly.GoodListShardHexS18
import Kepler.Assembly.GoodListShardHexS19
import Kepler.Assembly.GoodListShardHexS20
import Kepler.Assembly.GoodListShardHexS21
import Kepler.Assembly.GoodListShardHexS22
import Kepler.Assembly.GoodListShardHexS23

open Kepler.Graphs

namespace Kepler.Assembly

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Tri 类闭合：9 图，1 分片。 -/
theorem allGoodTri : TriData.all goodListB = true :=
  goodListTriS00

#print axioms allGoodTri

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Quad 类闭合：1253 图，13 分片。 -/
theorem allGoodQuad : QuadData.all goodListB = true :=
  all_of_take_drop goodListQuadS00
      (all_drop_of_split goodListQuadS01
      (all_drop_of_split goodListQuadS02
      (all_drop_of_split goodListQuadS03
      (all_drop_of_split goodListQuadS04
      (all_drop_of_split goodListQuadS05
      (all_drop_of_split goodListQuadS06
      (all_drop_of_split goodListQuadS07
      (all_drop_of_split goodListQuadS08
      (all_drop_of_split goodListQuadS09
      (all_drop_of_split goodListQuadS10
      (all_drop_of_split goodListQuadS11
      (goodListQuadS12))))))))))))

#print axioms allGoodQuad

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Pent 类闭合：16080 图，161 分片。 -/
theorem allGoodPent : PentData.all goodListB = true :=
  all_of_take_drop goodListPentS00
      (all_drop_of_split goodListPentS01
      (all_drop_of_split goodListPentS02
      (all_drop_of_split goodListPentS03
      (all_drop_of_split goodListPentS04
      (all_drop_of_split goodListPentS05
      (all_drop_of_split goodListPentS06
      (all_drop_of_split goodListPentS07
      (all_drop_of_split goodListPentS08
      (all_drop_of_split goodListPentS09
      (all_drop_of_split goodListPentS10
      (all_drop_of_split goodListPentS11
      (all_drop_of_split goodListPentS12
      (all_drop_of_split goodListPentS13
      (all_drop_of_split goodListPentS14
      (all_drop_of_split goodListPentS15
      (all_drop_of_split goodListPentS16
      (all_drop_of_split goodListPentS17
      (all_drop_of_split goodListPentS18
      (all_drop_of_split goodListPentS19
      (all_drop_of_split goodListPentS20
      (all_drop_of_split goodListPentS21
      (all_drop_of_split goodListPentS22
      (all_drop_of_split goodListPentS23
      (all_drop_of_split goodListPentS24
      (all_drop_of_split goodListPentS25
      (all_drop_of_split goodListPentS26
      (all_drop_of_split goodListPentS27
      (all_drop_of_split goodListPentS28
      (all_drop_of_split goodListPentS29
      (all_drop_of_split goodListPentS30
      (all_drop_of_split goodListPentS31
      (all_drop_of_split goodListPentS32
      (all_drop_of_split goodListPentS33
      (all_drop_of_split goodListPentS34
      (all_drop_of_split goodListPentS35
      (all_drop_of_split goodListPentS36
      (all_drop_of_split goodListPentS37
      (all_drop_of_split goodListPentS38
      (all_drop_of_split goodListPentS39
      (all_drop_of_split goodListPentS40
      (all_drop_of_split goodListPentS41
      (all_drop_of_split goodListPentS42
      (all_drop_of_split goodListPentS43
      (all_drop_of_split goodListPentS44
      (all_drop_of_split goodListPentS45
      (all_drop_of_split goodListPentS46
      (all_drop_of_split goodListPentS47
      (all_drop_of_split goodListPentS48
      (all_drop_of_split goodListPentS49
      (all_drop_of_split goodListPentS50
      (all_drop_of_split goodListPentS51
      (all_drop_of_split goodListPentS52
      (all_drop_of_split goodListPentS53
      (all_drop_of_split goodListPentS54
      (all_drop_of_split goodListPentS55
      (all_drop_of_split goodListPentS56
      (all_drop_of_split goodListPentS57
      (all_drop_of_split goodListPentS58
      (all_drop_of_split goodListPentS59
      (all_drop_of_split goodListPentS60
      (all_drop_of_split goodListPentS61
      (all_drop_of_split goodListPentS62
      (all_drop_of_split goodListPentS63
      (all_drop_of_split goodListPentS64
      (all_drop_of_split goodListPentS65
      (all_drop_of_split goodListPentS66
      (all_drop_of_split goodListPentS67
      (all_drop_of_split goodListPentS68
      (all_drop_of_split goodListPentS69
      (all_drop_of_split goodListPentS70
      (all_drop_of_split goodListPentS71
      (all_drop_of_split goodListPentS72
      (all_drop_of_split goodListPentS73
      (all_drop_of_split goodListPentS74
      (all_drop_of_split goodListPentS75
      (all_drop_of_split goodListPentS76
      (all_drop_of_split goodListPentS77
      (all_drop_of_split goodListPentS78
      (all_drop_of_split goodListPentS79
      (all_drop_of_split goodListPentS80
      (all_drop_of_split goodListPentS81
      (all_drop_of_split goodListPentS82
      (all_drop_of_split goodListPentS83
      (all_drop_of_split goodListPentS84
      (all_drop_of_split goodListPentS85
      (all_drop_of_split goodListPentS86
      (all_drop_of_split goodListPentS87
      (all_drop_of_split goodListPentS88
      (all_drop_of_split goodListPentS89
      (all_drop_of_split goodListPentS90
      (all_drop_of_split goodListPentS91
      (all_drop_of_split goodListPentS92
      (all_drop_of_split goodListPentS93
      (all_drop_of_split goodListPentS94
      (all_drop_of_split goodListPentS95
      (all_drop_of_split goodListPentS96
      (all_drop_of_split goodListPentS97
      (all_drop_of_split goodListPentS98
      (all_drop_of_split goodListPentS99
      (all_drop_of_split goodListPentS100
      (all_drop_of_split goodListPentS101
      (all_drop_of_split goodListPentS102
      (all_drop_of_split goodListPentS103
      (all_drop_of_split goodListPentS104
      (all_drop_of_split goodListPentS105
      (all_drop_of_split goodListPentS106
      (all_drop_of_split goodListPentS107
      (all_drop_of_split goodListPentS108
      (all_drop_of_split goodListPentS109
      (all_drop_of_split goodListPentS110
      (all_drop_of_split goodListPentS111
      (all_drop_of_split goodListPentS112
      (all_drop_of_split goodListPentS113
      (all_drop_of_split goodListPentS114
      (all_drop_of_split goodListPentS115
      (all_drop_of_split goodListPentS116
      (all_drop_of_split goodListPentS117
      (all_drop_of_split goodListPentS118
      (all_drop_of_split goodListPentS119
      (all_drop_of_split goodListPentS120
      (all_drop_of_split goodListPentS121
      (all_drop_of_split goodListPentS122
      (all_drop_of_split goodListPentS123
      (all_drop_of_split goodListPentS124
      (all_drop_of_split goodListPentS125
      (all_drop_of_split goodListPentS126
      (all_drop_of_split goodListPentS127
      (all_drop_of_split goodListPentS128
      (all_drop_of_split goodListPentS129
      (all_drop_of_split goodListPentS130
      (all_drop_of_split goodListPentS131
      (all_drop_of_split goodListPentS132
      (all_drop_of_split goodListPentS133
      (all_drop_of_split goodListPentS134
      (all_drop_of_split goodListPentS135
      (all_drop_of_split goodListPentS136
      (all_drop_of_split goodListPentS137
      (all_drop_of_split goodListPentS138
      (all_drop_of_split goodListPentS139
      (all_drop_of_split goodListPentS140
      (all_drop_of_split goodListPentS141
      (all_drop_of_split goodListPentS142
      (all_drop_of_split goodListPentS143
      (all_drop_of_split goodListPentS144
      (all_drop_of_split goodListPentS145
      (all_drop_of_split goodListPentS146
      (all_drop_of_split goodListPentS147
      (all_drop_of_split goodListPentS148
      (all_drop_of_split goodListPentS149
      (all_drop_of_split goodListPentS150
      (all_drop_of_split goodListPentS151
      (all_drop_of_split goodListPentS152
      (all_drop_of_split goodListPentS153
      (all_drop_of_split goodListPentS154
      (all_drop_of_split goodListPentS155
      (all_drop_of_split goodListPentS156
      (all_drop_of_split goodListPentS157
      (all_drop_of_split goodListPentS158
      (all_drop_of_split goodListPentS159
      (goodListPentS160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

#print axioms allGoodPent

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Hex 类闭合：2373 图，24 分片。 -/
theorem allGoodHex : HexData.all goodListB = true :=
  all_of_take_drop goodListHexS00
      (all_drop_of_split goodListHexS01
      (all_drop_of_split goodListHexS02
      (all_drop_of_split goodListHexS03
      (all_drop_of_split goodListHexS04
      (all_drop_of_split goodListHexS05
      (all_drop_of_split goodListHexS06
      (all_drop_of_split goodListHexS07
      (all_drop_of_split goodListHexS08
      (all_drop_of_split goodListHexS09
      (all_drop_of_split goodListHexS10
      (all_drop_of_split goodListHexS11
      (all_drop_of_split goodListHexS12
      (all_drop_of_split goodListHexS13
      (all_drop_of_split goodListHexS14
      (all_drop_of_split goodListHexS15
      (all_drop_of_split goodListHexS16
      (all_drop_of_split goodListHexS17
      (all_drop_of_split goodListHexS18
      (all_drop_of_split goodListHexS19
      (all_drop_of_split goodListHexS20
      (all_drop_of_split goodListHexS21
      (all_drop_of_split goodListHexS22
      (goodListHexS23)))))))))))))))))))))))

#print axioms allGoodHex

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
