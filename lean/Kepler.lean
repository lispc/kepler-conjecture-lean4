-- Root module of the Kepler conjecture formalization project.
-- See PLAN.md for the overall plan and module layout.
import Kepler.Statement
import Kepler.LP.HelloChecker
-- Phase 3: LP 证书 checker 试点（稀疏整数化对偶/原始证书，内核 decide 检验）
import Kepler.LP.Cert
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
