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

### 枚举完备性：native_decide 分片方案（2026-08-10 定稿，替代逐节点内核重放）

**背景**（实测，详见 DECISIONS.md 2026-08-10 条目）：全树 18.7 亿节点
（AFP `ArchStat.thy` 官方数字），内核 `decide` 重放差 4-5 个数量级不可行；
枚举无非对称证书；模同构去重对本枚举器数学上不成立。经人类批准，
枚举闭包计算改用**限定范围 native_decide**。

**架构**：

- `Kepler.Graphs.Worklist`（通用，纯内核证明）：带精确去重的工作列表循环
  `loop succs check fuel work done : Option Bool`（fuel 截断免终止性证明）。
  （**建成版注**：最终实现简化为无去重的 `loop succs check fuel ws`，
  精确重复 pop 实测 ~0；闭包证明见 `loop_some_true`。）
  核心定理（对任意 fuel 成立）：
  `loop succs check fuel [r] ∅ = some true` 蕴含
  `∀ g, RTranCl succs r g → check g = true`。
  不变量：`R(work₀) ⊆ done ∪ R(work)` 且 `done` 相对 `work` 封闭
  （`d ∈ done ⇒ succs d ⊆ done ∪ R(work)`）且 `done` 中元素都通过了 check。
  另有 `frontier_cut` 引理：S ∋ Seed 且 `x ∈ S ⇒ succs x ⊆ S ∪ F`
  蕴含可达 g 满足 `g ∈ S ∨ ∃ h ∈ F, RTranCl h g`（用于分片粘接）。
- 每种子一个 `check g := !g.final || (pre_iso_test_b g.fgraph && bucketIso g)`，
  其中 `bucketIso` 按 hash 分桶查 Archive + `iso_test`；
  正确性：`check g = true → g.final → inIso g.fgraph Archive`
  （`iso_test_correct` + Archive 侧 `pre_iso_test` 一次性 decide +
  分桶 membership 引理为通用折叠定理，无需逐条 decide）。
- **分片**（仅为并行，不改变数学）：证书数据 = 浅层节点集 S（BFS < d 层）
  + 边界层 F；浅层逐节点 `next_tame p g = children` 用 native_decide 核验，
  `frontier_cut` 给出 `g ∈ S ∨ RTranCl F g`；F 中每个根 r 一个分片定理
  `∃ fuel, loop (next_tame p) (check p) fuel [r] ∅ = some true`（native_decide）。
  每个 final g 要么 ∈ S（数据直接给出 inIso 见证），要么被某分片覆盖。
- 预计算力：native 编译代码 ~20-55 核时（对照 AFP 11h），
  百核并行 ~15-35 分钟墙钟。
- **Tri 交叉校验**：Tri（312k 节点 ≈ 26 核时）另做纯内核 `decide` 版，
  与 native 路径跑同一套 `loop`/`check` 代码，双向印证。
- 早前"逐节点内核重放"证书设计（2026-08-10 上午版）仅保留于 Tri 交叉校验；
  `Cert.lean` 的 `closure_mem` 定理两者共用。
- Archive 数据：`pipeline/graphs/ml_to_lean.py` 转成
  `lean/Kepler/Graphs/ArchiveData/{Tri,Quad,Pent,Hex}.lean`
  （`TriData/QuadData/PentData/HexData : List (List (List Nat))`，
  19715 张共 ~4.9MB；需 `set_option maxRecDepth + maxHeartbeats 0`，
  注意 docstring 不能放在 `set_option ... in` 之前，否则解析失败）。

**建成状态（2026-08-12，G2 闭合，`tame_classification` 构建通过）**：

- 分片布局（`pipeline/graphs/{shardgen,reshardgen,childsplitgen}.py` 生成）：
  粗分片 fuel 4M（Quad/Hex G=100、Pent G=50）→ 失败区间细分（fuel 50M，
  QuadR/HexR G=5、PentR G=10）→ 超重 root 逐根拆分（G=1，PentR2/PentR3
  fuel 300M、HexR2 fuel 400M）。最终 575 个分片文件全部通过：
  Quad 12+80、Pent 142+16+30+10、Hex 66+219+5（另有每种子 4 条顶层
  native_decide：top_replay/top_bounds/no_finals/archive_pre）。
- 超重 root 实测（loopCount 探针，native 编译 ~4-11K pops/s）：
  Pent 有 9 个 4M-59M pops 的 root（j=74 最大 58,815,032 pops），
  j=0/j=1 更大（分片在 fuel 300M 内通过，单分片墙钟 15-23h）；
  全部 check=true，无 archive 失配。轻 root 典型值仅数百 pops，
  分布极重尾，适合递归拆分。
- j=0/j=1 精确 pops（2026-08-23 补测，Python 枚举器按 Worklist.loop
  无去重语义计数，split_depth=4 并行；CPython 与 PyPy 两次独立
  计数结果逐位一致）：**j=0 = 204,531,909 pops，j=1 = 132,292,386 pops**。
  计数脚本 `pipeline/graphs/popcount_par.py`（基于
  `pipeline/graphs/enumerate.py` 的 `frontier(2,3)` + `next_tame`；
  对 PyPy 3.11 兼容，实测 ~4× 快于 CPython）。
- 递归拆分预案（本次未启用，已验证可用）：`WorklistSplit.lean`
  （`loop_mono`/`loop_append`/`loop_list_of_forall`/
  `loop_singleton_of_children`，纯内核），可把任意超重 root 按其
  `next_tame` 子图再拆一层并行；组装结构（`interval_cases` + 逐子图
  分片定理）已经 axiom 桩预验证。
- 接线文件（`CertQuad/Pent/Hex.lean`）需 `set_option maxRecDepth 100000`
  （嵌套 dite 链 92-286 分支 + `frontier.length` 的 `rfl` 归约）。
- 公理审计（`#print axioms tame_classification`）：仅
  `propext`/`Classical.choice`/`Quot.sound` + 600 个 native_decide
  信任公理（tri 9、quad 16、quadr 80、pent 146、pentr 16、pentr2 30、
  pentr3 10、hex 70、hexr 219、hexr2 5），全部在上述限定范围内，无 sorry。
- 端到端墙钟：粗分片主构建 ~6.7h（220/239 一次通过），细分/逐根
  收尾 ~1.5 天（主要耗在 Pent j=0/j=1 两个 ~10⁸ pops 级 root 上）。

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

## Phase 3 — LP

稀疏整数对偶证书路线（VIPR 风格，全程 Int 以适配内核归约）：
`Kepler/LP/Cert.lean` 定义 `checkDual` 与弱对偶 `checkDual_sound`；
`pipeline/lp/socert.py` 把 SoPlex 精确模式（`-X/-Y` 有理输出）转换为
Lean 证书。真实图 204880136538（915 变量 × 3882 行）已端到端闭合。

**分片**（2026-08-25）：`checkDual` 的最贵合取项（列循环 `AᵀY ≥ D·c`）
按列拆片——`checkDualBase`（其余合取项一次 `decide`）+ `Cols<i>.lean`
（每片一个独立模块 `by decide`）+ `Assembly.lean`（term 模式链式组装经
`checkDual_of_shards`，内核不重算）。实测：单块 `decide` 25304 s →
分片端到端 **≈1542 s（16.4×，96 并发）**，单片内存有界、失败可重试。
用法见 `pipeline/lp/README.md`。

**全量化外推**：43,078 个终端 LP（19700 easy + 15 hard 图）按 ~7 core-h/LP
估计 ≈ 34 core-年，分片单独不够；下一步是 `Cert.lean` 头注释记录的
转置（列主序）证书表示，把对偶检查降为 O(nnz)（目标 ~30 s/LP）。

## Phase 4 — 非线性不等式

区间算术证书路线：`Kepler/Interval/Basic.lean` 定义二进制有理数
（dyadic `m·2^e`）端点的区间算术 + 表达式 AST（`IExpr`）与
`checkPos_sound`（盒上 f>0 的雏形）。求解侧工具链已验证：dReal
4.21.06.2（δ-完备决策）+ MPFR 4.2.2 + FLINT 3.3.1（内置 Arb），
见 `pipeline/interval/README.md`。

**除法/超越层已落地**（2026-08-28，全部零 sorry、零 native_decide、
公理仅标准三）：

- `Kepler/Interval/Div.lean`：`Dyadic.divFloorQ a b out` —— 在输出粒度
  `2^out` 下对 `a/b` 取底的 dyadic（`(a.m·2^k)/b.m`，`Int` 除法；负除数
  补偿 `-1`），带显式单 ulp 误差界（`divFloorQ_spec`/`divFloorQ_err`）；
  `Option` 语义（`b.m = 0` 或粒度无缩放空间则 `none`）。
  `DInterval.recip`（0 不在闭包内的区间取倒数，像 = `[1/hi, 1/lo]`，
  `recip_sound` 于 ℝ）与 `DInterval.div = I·recip J`（`div_sound`）。
- `Kepler/Interval/Sqrt.lean`：**证书式平方根** —— 关键发现：Lean 的
  `Nat.sqrt`/`Int.sqrt` 基于 `Nat.sqrt.iter`，内核 `decide` **不能归约**；
  故改为调用方提供根的尾数 `s`，内核只验证两个大整数不等式
  `s² ≤ m·2^(e%2) < (s+1)²`（`sqrtI`+`sqrtI_sound`，用
  `d.e = 2·⌊e/2⌋ + (e%2)` 的换算）。精度由放缩尾数控制；试点
  `sqrt2_bounds`：`1.4142 ≤ √2 ≤ 1.4143`（`sqrt2_cert` 仅依赖
  `[propext]`）。BnB 接口 `sqrtI_mem`。
- `Kepler/Interval/Ball.lean`：中点半径包装 `Ball = ⟨c, r⟩`
  （`mem` 于 ℝ），与 `DInterval` 双向精确换算（`midRadius`：对齐指数后
  指数减半即 `(lo+hi)/2`、`(hi-lo)/2` 均为精确 dyadic）；sound 的
  `add/neg/sub/mul`（乘积半径 `|c₁|r₂ + r₁(|c₂|+r₂)`）—— 超越函数
  "dyadic 值 + dyadic 半径" 的载体。
- `Kepler/Interval/Trans.lean`：**Leibniz 交替级数界**（自含证明
  `abs_sub_partial_le`：剥壳尾和 + 配对归纳 + `hasSum_nat_add_iff`/
  `tendsto_sum_nat` 取极限）⇒ `sin_abs_sub_partial_le`（[0,1] 上
  Mathlib `Real.hasSum_sin` 的显式余项）。检查层 `taylorIter`：通用
  逐项外向舍入（`divFloorQ` 按奇偶性进/舍）的交替 Taylor 累加器 +
  单 ulp 向上舍入的余项 `1/(2N+1)!` ⇒ `sinInterval`/`sinBall`
  （`sinInterval_sound`/`sinBall_sound` 于 ℝ）。**注意：[0,1] 外的
  变量缩减未做**（需周期性/对称性归约后再用）。试点：
  `sinPilot_real`（`0.4794 < sin(1/2)`，5 项 + 粒度 2⁻²⁰，区间宽 7 ulp，
  `decide` 闭合）与 `sinBallPilot_real`（球形式端到端）。

下一步：`IExpr` 扩展（div/sqrt/trans 节点，`Option` 评估器）、
分支定界证书格式（叶携带 `checkPos` 类检查 + `CertShards` 式分片）、
cos/arctan（`taylorIter` 已泛型，实例化即可）、范围缩减。
