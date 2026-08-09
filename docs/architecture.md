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

### 不受信生成器对拍状态（pipeline/graphs/）

- `enumerate.py`：`next_tame` 枚举的 Python 直译（与 Lean 移植同源）。
- `crosscheck.py`：dart-BFS 规范化（含镜像取小）+ Archive 比对。
- **p=0（Tri）对拍通过**：枚举 501 张原始图 → 9 个同构类，
  与 Archive 的 9 张完全一致（双向无差异）。
- **p=1（Quad）对拍通过**：枚举 29318 张原始图（96 核并行，frontier
  深度 4 分片 1583 块）→ 1253 个同构类，与 Archive 的 1253 张完全一致。
- p=2（Pent，16080 张）对拍运行中（110 核）；Hex（2373）待跑。

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
