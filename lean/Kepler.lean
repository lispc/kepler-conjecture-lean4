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
import Kepler.Text.Fan
import Kepler.Text.TopologyFan
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
