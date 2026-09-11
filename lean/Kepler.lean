-- Root module of the Kepler conjecture formalization project.
-- See PLAN.md for the overall plan and module layout.
import Kepler.Statement
import Kepler.LP.HelloChecker
-- Phase 3: LP 证书 checker 试点（稀疏整数化对偶/原始证书，内核 decide 检验）
import Kepler.LP.Cert
-- Phase 4: 区间算术证书 checker 试点（二进制有理数端点区间 + soundness，内核 decide 检验）
import Kepler.Interval.Basic
-- Phase 4: 除法/倒数（divFloorQ 显式误差，Option 语义）+ 区间 recip/div
import Kepler.Interval.Div
-- Phase 4: 证书式平方根（内核只验证 s²≤n<(s+1)²，Int.sqrt 不可内核归约）
import Kepler.Interval.Sqrt
-- Phase 4: 中点半径包装（dyadic 中心+半径，与 DInterval 双向换算）
import Kepler.Interval.Ball
-- Phase 4: 超越层（Leibniz 交替级数界 + sin/cos/arctan 的 Taylor dyadic 区间/球，
-- π-shift 范围缩减）
import Kepler.Interval.Trans
-- Phase 4: 扩节点表达式层（IExpr 的 div/sqrt/trans 节点 + Option 求值 + checkPos soundness）
import Kepler.Interval.Expr
import Kepler.Geom.Azim
import Kepler.Geom.Aff
import Kepler.Geom.AzimLemmas
-- Phase 5: 体积层基础设施（radial_norm / sol / sol_spec，vol1.hl）
import Kepler.Geom.Volume
-- Phase 5 体积层：2D 扇形面积（polar coord）
import Kepler.Geom.SectorArea
-- Phase 5 体积层：HOL VOLUME_BALL_WEDGE（球∩楔形 = azim·2r³/3，flyspeck.ml:5452）
import Kepler.Geom.WedgeVolume
-- Phase 5 体积层：dihV + WEDGE_LUNE_GT + HAS_MEASURE_LUNE（flyspeck.ml:2995/3805/5529）
import Kepler.Geom.LuneVolume
-- Phase 5 体积层：HOL VOLUME_SOLID_TRIANGLE（球∩三棱锥 = (Σ dihV - π)r³/3，flyspeck.ml:5883）
import Kepler.Geom.SolidAngle
import Kepler.Text.Fan
import Kepler.Text.TopologyFan
-- Phase 5: 文字证明移植 —— planarity.hl（Fan 章的平面性部分）
import Kepler.Text.Planarity
-- Phase 5: planarity.hl:3667 not_cut_inside_fan（1,515 行单证明巨块，切片移植）
import Kepler.Text.PlanarityNotCut
-- Phase 5: planarity.hl:7788 AFF_GT_CUT_XFAN_IMP_EDGE_FAN（1,211 行单证明巨块，9 片切片移植）
import Kepler.Text.AffGtCut
-- Phase 5: planarity.hl:9297 起 angle/rcone 段（自动化移植 harness：骨架定稿 + big-pickle 填空）
import Kepler.Text.PlanarityAngle
-- Phase 5: planarity.hl:10812 起 dartset/连通分量段（同 harness）
import Kepler.Text.PlanarityComponent
-- Phase 5: planarity.hl:11111 起加边/DWWUTKW 段（harness 批次 4）
import Kepler.Text.PlanarityDarts
-- Phase 5: planarity.hl:11439 起 yfan 连通/边界段（harness 批次 5）
import Kepler.Text.PlanarityConnect
import Kepler.Text.PlanarityAuto6
import Kepler.Text.PlanarityAuto7
import Kepler.Text.PlanarityAuto8
import Kepler.Text.PlanarityAuto9
import Kepler.Text.PlanarityAuto10
import Kepler.Text.PlanarityAuto11
import Kepler.Text.PlanarityAuto12
import Kepler.Text.PlanarityAuto13
import Kepler.Text.PlanarityAuto14
import Kepler.Text.PlanarityAuto15
import Kepler.Text.PlanarityAuto16
-- Phase 5: Conforming.hl 顶层定义层（conforming_* / N_FAN / f1_fan）
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto1
import Kepler.Text.ConformingAuto2
import Kepler.Text.VectorAngleLemmas
-- Phase 4: 分支定界证书树（二分盒树 + covers/bb_sound，叶为内核 decide 的 checkPos）
import Kepler.Interval.Cert
import Kepler.Graphs.ListAux
import Kepler.Graphs.Rotation
import Kepler.Graphs.Graph
import Kepler.Graphs.Enumerator
import Kepler.Graphs.FaceDivision
import Kepler.Graphs.Plane
import Kepler.Graphs.Plane1
import Kepler.Graphs.Tame
import Kepler.Graphs.Generator
import Kepler.Graphs.TameEnum
import Kepler.Graphs.Sanity
-- The full Phase 2 cert chain (Cert*/CertShards/TameClassification) lives under
-- `Kepler.Graphs`; import it so the default target covers G2 end to end
-- (otherwise `lake build` / `make reprove` silently skips the shard files).
import Kepler.Graphs
-- Phase 5: 文字证明移植 —— hypermap 核心定义层
import Kepler.Text.Hypermap
