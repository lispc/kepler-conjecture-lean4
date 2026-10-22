# Lean 4 生态 + Flyspeck 论文侦察（2026-10-22，只读）

> 目的：为 AJRIPQN 之后的 LP/nli/可信基工作找可复用模块。结论按“可落地性”排序，
> 不是论文综述。所有链接在 2026-10-22 可访问；未构建任何外部仓库。

## 0. 结论速览

1. **公开互联网上没有完整的 Lean 3/4 Kepler/Flyspeck 三维形式化。**
   GitHub `kepler+language:Lean` 只有本仓库与 `BhorisDhanjal/KeplersLawsLean`
   （开普勒行星定律，不是猜想）；`flyspeck+language:Lean` 为 0；arXiv
   `"Kepler conjecture" AND Lean` / `"Flyspeck" AND Lean` 均为 0。
   **我们是唯一公开的 Lean 4 Kepler 移植。**
2. 最值得直接复用的是 **`leanprover/lp-verify` + `lp-core`**（LP/Farkas 证书
   检查器，纯 Lean、约 2.3k 行、0 sorry/native_decide/自定义 axiom）。
   它正好覆盖我们 `pipeline/lp` 的证书检查缺口。
3. 最值得借鉴的工程范式是 **`contact-numbers-lean`**（证书分块 +
   `decide +kernel` + `Axioms.lean` 信任基检查）和 **`jtraverso/planar-list-colouring`**
   （Lean 4 rotation system / hypermap / Euler defect 基础）。
4. **可信性警告（必读）**：Thomas Hales 2026-10-09 客座文章记录，2026 年
   “Summer of Soundness Bugs” 期间 Lean 内核 bug 曾产生过**一个简短的非法
   Kepler 猜想 Lean 证明**；mathlib 已用修复后的内核重验。任何 Lean Kepler
   证明必须做 `leanchecker`/kernel replay + 公理审计 + 陈述审计，不能只信
   `native_decide` 或构建成功。
   来源：https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/

## 1. LP 证书：最高优先级

### `leanprover/lp-verify` + `lp-core`
- https://github.com/leanprover/lp-verify （Apache-2.0，Lean v4.33.1，约 2,311 行，
  0 sorry/admit/native_decide/自定义 axiom；依赖仅 `lp-core`，纯 Lean）
- 提供 `verifyOutcome`（optimal / infeasible / unbounded / unchecked）、
  `checkOptimal_sound` / `checkInfeasible_sound` / `checkUnbounded_sound`、
  稀疏 `Ax`/`Aᵀy`、Farkas 对偶、分子/分母位数预算。
- **行动**：把现有 `pipeline/lp` 输出适配成 `lp-core` 的 `Problem`/`Certificate`，
  用 `lp-verify` 做独立检查；生成器（SoPlex/glpk）保留为不受信前端。
  版本需从 4.32.2 升到 4.33.1 或 backport。
- 相关：`lp-core`、`lp-tactic`、`lp-backend-soplex-json`（实验性 JSON 后端）。

## 2. Interval / Taylor / nli

### `peti12352/lean-interval-bounds`（轻量，先接）
- https://github.com/peti12352/lean-interval-bounds （Apache-2.0，Lean v4.33.0-rc1，
  11 文件 2,562 行，0 sorry/native_decide/axiom）
- exp/log/sin/cos 的 Taylor–Lagrange 界 + `interval_decide`/`approx` tactic；
  仅单变量有理点/区间。适合先吃掉简单超越常数界的一部分 shard。

### `alerad/leancert`（功能全，按模块取）
- https://github.com/alerad/leancert （Apache-2.0，Lean v4.35.0，494 文件/123k 行）
- 有理/二进/仿射区间、Taylor 展开与余项、Taylor model、多变量盒
  branch-and-bound、根存在/唯一性、积分证书、`norm_num` 扩展；
  支持 `trust := kernel`（`decide +kernel`）。
- **注意**：默认模式有 330 个 `native_decide`；`Li2` 有 2 个 intentional sorry
  且默认根不导入。只按需取 `Core/Taylor`、`Engine/TaylorModel`、
  `Engine/Optimize`、`Validity/Bounds`，强制 kernel 模式。

### `girving/interval`（可借鉴，不作最终证书）
- https://github.com/girving/interval （Apache-2.0，Lean v4.34.1，核心 16k 行，
  0 sorry/native/axiom）
- 软件浮点 64+64、`Approx`/`Box`；语义是浮点区间，适合预计算/筛选，
  不适合作为 Flyspeck nli 的最终 kernel 证据。

### 算法参考（非 Lean）
- Solovyev & Hales, arXiv:1301.1702（Taylor interval approximations）；
  arXiv:1404.7282（formal nonlinear optimization）；
  Allamigeon–Gaubert–Magron–Werner, arXiv:1403.5899（LP/SOS templates）。
- Isabelle AFP `Taylor_Models`、`Affine_Arithmetic`。

## 3. Graph / hypermap / tame

### `jtraverso/planar-list-colouring`
- https://github.com/jtraverso/planar-list-colouring （Apache-2.0，Lean v4.35.0-rc3，
  71 文件/19,514 行；库本体 0 sorry/native/axiom，10 个 sorry 仅在 Challenge.lean）
- `Planar/Embedding.lean`（rotation system、PlaneMap、facePerm、Euler 公式）、
  `Planar/Hypermap.lean`（compSetoid、numComponents、eulerDefect 合并/拆分）、
  `Planar/Orbits.lean`（cycleCount、removeFromCycle、insertBefore）、
  `Wagner/HypermapKit.lean`（eulerDefect_mulSwap_* 等）。
- **行动**：作为我们 hypermap/tame graph 层的起点或对照；非常新（2026-10-14），
  需自行审计/构建。

### HOL Light tame graph PR #1（工程参考，不是 Lean）
- https://github.com/hol-light-family/Flyspeck/pull/1 （open，73 文件/28,715 行，MIT）
- 证书式枚举：child/prune/isomorphism witness；强 completion-excess 下界把
  ~2.1B 节点压到 ~43M；4 个 class 32 核约 2 小时；默认用
  `graph_deserialization` axiom 导入，native runner 可无 axiom 重证。
- 这是目前最成熟的 tame graph 证书架构，值得按证书格式移植。

### AFP `Flyspeck-Tame`
- https://www.isa-afp.org/entries/Flyspeck-Tame.html （BSD，35 个 .thy/15,138 行/872 lemmas）
- Bauer–Nipkow 的原始 tame 枚举；可借鉴定义/archive/剪枝，直接移植成本高。

## 4. 陈述对照 / 球堆积定义

- `lean-eval` 的 `LeanEval/Geometry/KeplerConjecture.lean`（59 行，已 merged）：
  `IsPacking`、`coveredFraction`、`density = limsup`、`Δ d = sSup {δ | ...}`、
  `theorem kepler_conjecture : Δ 3 = π / √18 := by sorry`。
  **最适合作为我们 e2e 陈述的独立对照**（我们用 `ncard` 的有限容器界，
  数学等价但编码不同）。
- `thefundamentaltheor3m/Sphere-Packing-Lean`（Apache-2.0，Lean v4.35.0-rc4，
  80 文件/17,266 行，62 个实际 sorry）：`SpherePacking/Basic/SpherePacking.lean`
  提供 `SpherePacking`、`balls`、`finiteDensity`、`density`、`SpherePackingConstant`
  及缩放/体积引理；可作为密度 API 对照，**不能当完整依赖**。
- `math-inc/Sphere-Packing-Lean`（Apache-2.0，Lean v4.28.0，830 文件/180k 行，
  0 sorry/native/axiom）：d=8/24 完成版，整体与 Kepler 无关；只取
  `Basic`/`CohnElkies`/`ForMathlib`/`Tactic` 思路。
- `seewoo5/cohn-elkies-refactor`（Apache-2.0，Lean v4.35.0，97 文件/68k 行，
  5 个 sorry 仅在挑战陈述）：比 `openai/ten-proofs` 的 55k 行单文件更干净，
  可读 Fourier/周期密度/径向化/解析上界。

## 5. 可信基 / 独立检查工具

- `leanprover/con-leche`（https://github.com/leanprover/con-leche，Apache-2.0）：
  外部 checker，自带一致性证明，只接受 `propext`/`Classical.choice`/`Quot.sound`，
  拒绝其他公理，`sorryAx` 忽略但报告。Lean 版 HOL Zero 的最佳候选。
- `ammkrn/nanoda_lib`（https://github.com/ammkrn/nanoda_lib，Apache-2.0）：
  Rust 外部 checker，读 `lean4export` JSON，permitted_axioms 可配置。
- `leanprover/con-ron`（con-leche 的 Rust 移植）、`leanprover-community/axiom-audit`
  （抓 `sorryAx`/`Lean.ofReduceBool`/自定义 axiom）、`leanprover/lean4checker`
  （kernel replay；发行版自带 `leanchecker`）、`GasStationManager/SafeVerify`
  （提交级同名同型/定义体/三公理检查）。
- **行动**：固定到含 2026 内核修复的 Lean 版本；CI 跑 `leanchecker` +
  `axiom-audit` + 静态扫描；e2e 陈述用 `lean-eval`/`creelie` 风格独立审计；
  不要用 `native_decide` 作为最终信任基。

## 6. 明确不要碰

| 项目 | 原因 |
|---|---|
| `YaelDillies/sphere-packing` | 404，不存在 |
| `YaelDillies/Polyhedral` | 60 个实际 sorry、无 LICENSE；只可 monitor |
| `EdouardBonnet/lax-109476` | 17 个自定义 axiom，不是证明 |
| `FusionSandwich/Testing` PR #56 | 无 LICENSE，关键事实全是 theorem parameters |
| `rjwalters/lean-genius` | 3.7 GB annotations，Kepler 只是 checklist |
| `bsniegowski/lean-planar-graphs` | 60 KB，信息不足 |
| `LeanCert` 整体 import + 默认模式 | 330 个 native_decide；只取模块并强制 kernel |
| `girving/interval` 作最终证书 | 浮点区间，不是精确有理/Taylor |
| Cohn–Elkies “LP bound” 当有限 LP 证书 | 解析函数空间优化界，不是 `lp-verify` 的有限有理 LP |

## 7. 排序建议

1. **`lp-verify` 适配**：把我们 43,078 个 LP 叶户的证书接到纯 Lean checker，
   替代“deferred-compute + kernel decide 单件 7h”的路线。这是最大杠杆。
2. **独立 kernel 重放试点**：`con-leche` 导出主定理/子树，只允许三公理；
   预期暴露 624 个 `native_decide`，作为可信基硬指标。
3. **`lean-interval-bounds` 先接**，再按模块接 `LeanCert` kernel 模式，
   逐步替换 nli/interval 的 native 计算。
4. **`contact-numbers-lean` 证书分块架构**：把 shard 按依赖图分块、
   并行构建、每块 `decide +kernel`、CI 禁止 `Lean.ofReduceBool`。
5. **`jtraverso` hypermap 层 + HOL Light PR #1 证书格式**：为 tame graph
   枚举移植做准备；这是 AJRIPQN 之后最重的独立支线。

## 8. 与 Flyspeck 论文的对照（arXiv:1501.02155）

- 论文的主定理形式（有限容器界 `πr³/√18 + cr²`）与我们的
  `Final.lean:22` **逐字一致**。
- 论文的 43,078 个 LP 与我们的 43,078 叶户完全一致；`reference/flyspeck/
  formal_lp/glpk/binary` 有 404 MB 原始证书，`verify_all.hl` 是官方 checker
  （HOL Light 约 15h）。
- 论文的 18,762 是 `formal_lp/hypermap/tests/test_all_lists.hl` 的 LP 测试图数；
  我们的 19,715 与 `formal_graph/archive/archive_all.ml` 一致
  （`make_archive.hl:38` 断言 `List.length Archive_all.tame_list = 19715`）。
- 论文的“最大风险=Isabelle→HOL 手工翻译”对应我们的 HOL→Lean 陈述桥；
  论文的 HOL Zero replay 对应 `con-leche`/`nanoda`；论文的 archive identity
  对应我们的 19,715 图 MD5 对账。三条都应纳入 P0 审计。
