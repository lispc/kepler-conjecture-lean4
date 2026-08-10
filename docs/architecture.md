# architecture.md — 证书格式与流水线架构

> 活文档：每个 Phase 先用小案例打通"求解器→证书→checker→Lean 定理"全链路，
> 再规模化（PLAN.md §7 风险 4 的缓解）。本文件随各 Phase 推进持续补充。

## 总体信任模型

可信基 = Lean 内核 + Mathlib + 本项目中经 `#print axioms` 审计的 checker 证明。
`pipeline/` 下一切代码与输出均不受信任；所有计算性断言以证书形式进入 Lean，
由内核重放 checker 核验。`native_decide` 全项目禁用。

## Phase 2 — tame 平面图枚举

### 理论来源

以 AFP 条目 **Flyspeck-Tame**（Nipkow–Bauer）为蓝本，副本锁定于
`reference/afp-flyspeck-tame/`（sha256 见 `reference/LOCK.md`）。
其完备性定理 `Completeness.thy: completeness` 的结构：

1. `g ∈ PlaneGraphs` ⇒ 从某个 `Seed p` 经 `next_plane p` 可达（PlaneGraphs 的定义即如此）；
2. 不变量 `mgp` 允许换用带预剪枝的 `next_plane0`（`Invariants.thy`，约 2800 行——数学大头之一）；
3. `tame g` ⇒ `p ≤ 3`（`tame5`，简单）；
4. 剪枝保持 tame 可达性：`Seed p [next_tame0 p]→* g`（`TameEnumProps.thy` + `GeneratorProps.thy`
   + `LowerBound.thy` + `ScoreProps.thy`，数学大头之二）；
5. 计算部分：`fgraph ` TameEnum ⊆≃ Archive`（`Computation/ArchComp.thy`，同构比对）。

### Lean 侧现状（2026-08-09，Phase 2 第一周）

已移植可执行核心（`lean/Kepler/Graphs/`，逐文件对应 AFP 理论，无 sorry）：
Graph / Rotation / ListAux / Enumerator / FaceDivision / Plane / Plane1 /
Tame / Generator / TameEnum。含全部常量表（squanderTarget=15410 等）与
`next_tame` 剪枝枚举函数；`Sanity.lean` 有内核 `decide` 小测。

### 证书格式设计（定稿目标）

枚举本身在 Lean 中已是可执行函数，因此**不需要**把整棵搜索树导出为数据。
证书只覆盖"计算量大、内核重放不划算"的部分；剪枝的**正确性**（上述第 2、4 步）
是数学定理，在 Lean 中一次性证明，不属于证书。

- **Archive 证书**（每张图一条）：
  - fgraph：面列表（`List (List Nat)`，`rotate_min` 规范化）；
  - 可达性见证：从 `Seed p` 到该图的 `next_tame` 扩展序列（每步 =
    多边形尺寸 `i` + 枚举下标），checker 在 Lean 内逐步重放
    `next_tame`（内核计算）验证确实到达该图；
  - tame 见证：`tame9a..tame12o` 由 `decide` 直接核验；
    `tame13a` 附权重见证（与 `faces g` 平行的 `List Nat`），
    由 `admissibleCheck`/`tame13aCheck` 核验。
- **完备性**：`theorem tame_classification` 组装方式 = 上述第 1–4 步的 Lean 证明
  （移植 Invariants/TameEnumProps 等）+ 第 5 步的同构比对：
  对每张 TameEnum 产出图，证书给出它在 Archive 中的同构见证
  （顶点置换 + 面映射），checker 验证同构成立。
  TameEnum 的全集计算量大，打算用**分块内核重放**或
  把"产出图集合 = Archive 给出的集合"拆成逐图可达性证书（见上），
  避免一次性 decide 爆炸。具体拆分在打通 10 张小案例后定稿。
- **同构检查**：不移植 `iso_test` 搜索算法；证书携带显式同构见证，
  checker 只做代入验证（廉价）。
  **重要（2026-08-09 对拍发现）**：Archive 比对用的 `iso_fgraph`/`iso_test`
  （PlaneGraphIso.thy:834-878）允许**镜像**——`iso_test g1 g2 ≡
  pr_iso_test g1 g2 ∨ pr_iso_test g1 (map rev g2)`。checker 验证同构见证时
  必须同样允许面列表整体反转，否则 Tri 种子会多出 3 个"假extra"图。

### 枚举树证书：具体设计（2026-08-10 定稿，Tri 试点验证中）

AFP 的 `samet`/`tameEnumFilter`（trie + worklist + `by eval`）**不移植**。
我们的替代：把 `Relative_Completeness` 的 locale 假设换成 4 条逐点事实
`same_p : ∀ g, TameEnumP p g → inIso g.fgraph Archive`（p = 0..3），
每条由对应种子的**枚举树证书**在内核重放后导出。证书与 checker 设计：

- **证书内容**（每种子的枚举树，Python 生成、不受信）：
  节点数组，每节点 = 完整 `Graph` 记录 + 父节点下标；
  终节点（final）额外带：Archive 条目下标 + 同构见证（顶点映射表 + 镜像标志）。
- **逐节点重放**（唯一的重计算）：对每个节点内核 `decide`
  `next_tame p g = children`（children 由证书给出）。一次性 Replay 整棵树
  ≈ 362k 次单步求值（Tri 501 / Quad 29318 / Pent 302410 / Hex 29740）。
  **实测**（`pipeline/graphs/kern_probe.py` 生成探针）：Tri 各深度节点
  全树 7 个探针共 4.3s；Pent 首子路径 13 个探针（子节点数 10-74）
  共 2m13s ≈ 10s/节点（含大字面量 elaboration）。外推全量 362k 节点
  ≈ 950 核时，百核并行约 8-10 小时墙钟——可接受，即为 Phase 2 的
  `make reprove` 成本。分块到多模块由 lake 并行。
- **闭包定理**（通用，证一次）：节点集 S 含 `Seed p` 且对每个非 final
  `g ∈ S` 有 `next_tame p g` 的孩子都在 S，则 `RTranCl (next_tame p) (Seed p) g`
  蕴含 `g ∈ S`（对 RTranCl 归纳）。
- **可达性证明零成本复用**：节点按拓扑序处理，`RTranCl` 证明由父节点的
  RTranCl + 父节点重放等式的成员关系直接组装（`.succs`），不重复求值。
- **终节点 `inIso` 导出**：`RTranCl + final` ⇒ `TameEnumP` ⇒
  `mgp_TameEnum` ⇒ `minGraphProps g` ⇒ `mgp_pre_iso_test`（fgraph 侧前提）；
  Archive 条目侧 `pre_iso_test` 由 `decide`；代入 `iso_test_correct`
  （PlaneGraphIso.lean 已移植的 `iso_correct` 的 corollary）得
  `g.fgraph ≃ archiveEntry`，加上条目成员关系即 `inIso g.fgraph Archive`。
- **Archive 数据**：`pipeline/graphs/ml_to_lean.py` 把 4 个 .ML 原样转成
  `lean/Kepler/Graphs/ArchiveData/{Tri,Quad,Pent,Hex}.lean`
  （`TriData/QuadData/PentData/HexData : List (List (List Nat))`，
  19715 张共 ~4.9MB；需 `set_option maxRecDepth + maxHeartbeats 0`，
  注意 docstring 不能放在 `set_option ... in` 之前，否则解析失败）。
- **信任边界不变**：Python 侧一切不受信；内核重放失败 = 证书无效。
  `Graph` 记录的派生字段（faceListAt/heights）无需一致性检查——
  RTranCl 链从 `Seed p` 出发逐步经 `next_tame` 等式建立，记录字段再怪
  也不影响"它是 next_tame 后代"这一事实。

### 不受信生成器对拍状态（pipeline/graphs/）

- `enumerate.py`：`next_tame` 枚举的 Python 直译（与 Lean 移植同源）。
- `crosscheck.py`：dart-BFS 规范化（含镜像取小）+ Archive 比对。
- **p=0（Tri）对拍通过**：枚举 501 张原始图 → 9 个同构类，
  与 Archive 的 9 张完全一致（双向无差异）。
- **p=1（Quad）对拍通过**：枚举 29318 张原始图（96 核并行，frontier
  深度 4 分片 1583 块）→ 1253 个同构类，与 Archive 的 1253 张完全一致。
- **p=2（Pent）对拍通过**：枚举 302410 张原始图（110 核，frontier
  深度 5 分片 214190 块）→ 16080 个同构类，与 Archive 的 16080 张完全一致。
- **p=3（Hex）对拍通过**：枚举 29740 张原始图（110 核，frontier
  深度 4 分片 39505 块）→ 2373 个同构类，与 Archive 的 2373 张完全一致。
- **四个种子全部双向一致（9 + 1253 + 16080 + 2373 = 19715）**：
  Python 生成器、Lean 移植、Flyspeck/AFP Archive 三方语义自洽，
  枚举语义层面无遗漏图（1998 Java 版漏图问题由对拍 + 内核 checker 双保险覆盖）。

### 交叉核对状态

- `reference/flyspeck/formal_graph/archive/{Tri,Quad,Pent,Hex}.ML`
  与 `reference/afp-flyspeck-tame/Archives/*.ML` **逐字节一致**
  （9 + 1253 + 16080 + 2373 = 19715 张图；此为观察值，不硬编码进证明）。
- `string_archive.txt`（1998 Java 生成器原始输出）的解析级核对待做。
- plantri v5.5 已编译（`pipeline/graphs/tools/plantri55/`），
  作为独立交叉验证生成器（仅报警用，不入证明）。

## Phase 3 — LP（占位）

VIPR 证书 + 有理数 checker，见 PLAN.md §4。设计待 Phase 3 启动时补充。

## Phase 4 — 非线性不等式（占位）

dReal δ-证迹 / Arb 盒子剖分证书。设计待 Phase 4 启动时补充。
