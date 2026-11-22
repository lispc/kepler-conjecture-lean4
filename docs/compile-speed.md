# 编译速度基线（2026-11-21，`compile-speed-research-w1`）

> 状态：调研已收线 **GO**；本文件是**存档与复测入口**，不是已应用的优化。
> 任何代码/驱动改动（`-j2`、import kit、调度器）都尚未应用，需用户另批。
> 证据：快照 `~/c17_backup/lane_snapshots/compile-speed-research-w1/`（169 件，
> `MANIFEST.sha256` 全 OK，0 symlink）；`REPORT.md` / `PLAYBOOK.md` / `bench/` /
> `data/` / `logs/`。主仓 tracked 零改动。本文件数字 = 编排者 2026-11-21 独立复跑，
> 与快照 `REPORT.md` 的差异见 §1 勘误。

## 1. 三个基线数

| 指标 | 值 | 口径 |
|---|---|---|
| Mathlib import 固定费 | **3.4 s CPU / 5.5 GB RSS** | `import Mathlib` 与 `import Kepler.Interval.Basic` 探针；空文件 0.20 s / 0.39 GB |
| 付此费的 Kepler 模块 | **9,858 / 11,241（87.7%）** | 注释感知 import 图（含传递闭包）；`Interval` 7,788、`Text` 1,062、`LP` 961、`Geom`/NliBanks 胶水约 47；`Graphs` 951 **全部为 0** |
| 最重单模块 | **503.5 s / 4,921 CPU-s / 21.25 GB** | `Text.ZTGJoint0000CornersP`；次重 `Text.PackingAuto21` 483.5 s / 16.33 GB；`NliBanksZTGIJCF4Dih` 185.1 s / 11.35 GB |

**勘误（编排者，相对车道 `REPORT.md` §0）**：车道原文「7,975 / 11,241（70.9%），
`Graphs`/`LP` core-only」不成立。7,975 可精确复现为
`reach(Kepler.Interval.Basic)`（7,844）∪ 直接 `import Mathlib`（136），是**非传递下界**；
`LP` 1,150 个模块中 961 个经 `Kepler.LP.Cert`（或 `LP.Pilot… → Data → Cert`）传递到
`Mathlib`，`Text` 有 1,062/1,097 个传递到 `Mathlib`。`lean --deps` 亲验
`LP.Pilot204880136538.Cols223 → Data → Cert → Mathlib` 与
`Text.LocalFanPerimeterGeneric → LocalAuto7 → Mathlib` 两条链。真正 core-only 的只有
`Graphs`（0/951，例 `Graphs.Graph` 只 import `Mathlib.Data.Set.Defs`）。
**修正后固定费覆盖面更大（+18 个百分点），杠杆方向不变。**

## 2. 时间分层（重件）

- **import**：重件 0.05–0.6%；小模块 `Interval.Basic` 84%（import 2.64 s + interpretation 1.15 s）。
- **证明重建**：95–99%。`norm_num` 累计 142–2,250 s、`interpretation`（IR 解释器）
  120–1,710 s、`typeclass inference` 117–1,190 s；外层 `tactic execution` 与之重叠。
- **内核检查**：1–3%（12.4–31.4 s）；**olean 序列化**：2–6%（3.6–11.3 s）。
- **codegen：0**。olean 构建不调 clang；`native_decide` 也只编译 LMNF/IR 到进程内解释器
  （`LEAN_CC` wrapper 亲验 0 次调用，wrapper 自测可正常记录）。
- `linarith` 是最贵常规 tactic：单次约 **14–21 ms CPU**（解释器驱动）；`norm_num` 约 1–2 ms。
- `native_decide` 不是提速手段：fib30 上 **0.60 s（+1 条公理） vs `by decide` 0.17 s（零公理）**。
  585 基座维持不动；能过内核 `decide` 的目标鼓励换，过不了的不得新增 `native_decide`。

## 3. 杠杆与实测（编排者复跑）

| 杠杆 | 实测 | 结论 |
|---|---|---|
| 每模块 `-j2` | 单件 CertD：`-j1` 175.3 s / 175.5 CPU-s / 9.90 GB；`-j2` 100.1 s / 186.5 CPU-s / 9.72 GB。3 并发 CertD：`-j2` 122.7 s / 687.5 CPU-s vs `-j12` 109.3 s / 998.7 CPU-s | **采用为批量/CI 默认**：3 并发省 **31% CPU**、wall 仅 +12%；单件 wall −43%、CPU +6%（相对 -j1） |
| import kit | `import Mathlib` 3.59 s / 5.62 GB → kit A 1.46 s / 2.13 GB → kit B 0.99 s / 1.41 GB | **仅试点**：toy 文件成立；全仓需逐模块验证 import 面。改 `Kepler.Interval.Basic` = 改 7,844 个模块的可用引理面，高风险 |
| 按内存排槽 | 最重 21.25 GB；重证书 9.7–11.4 GB；CertShards ~1.6 GB | **采用**：重件 1 槽、轻件 2–3 槽；21.25 GB 件只能独占 |
| 绕开 `lake env` | 每次 0.43 s / 668 MB | 驱动层导出一次 `LEAN_PATH` |
| `decide` 替 `native_decide` | 3.5× 快且零公理（fib30） | 逐条测；585 基座不动 |

**排产硬约束（勘误）**：车道的「3 并发 CertD」实验是 3 × 9.72 GB ≈ **29.2 GB**，
超过 AGENTS §4 的 **24 GB** 总 RSS 硬闸（若池 worker 同时在场还超过 3 进程）。
它是**压力测试**，不是可执行的排产方案；生产排产最多 **2 个重件**（2×9.72=19.4 GB）
或 1 重 + 轻件。车道 `REPORT.md` §6「全程 lean ≤2」与 §4 D1 的 3 并发实验自相矛盾，
引用时以本条为准。

**Lake 5.0 无 `-j`**：`lake build -j1` 直接报 `unknown short option '-j'`；
`LAKE_JOBS=1` 无效，默认全核扇出（合成项目 40 个模块：2.75 s wall / 23.7 CPU-s）。
可控旋钮只有 `moreLeanArgs` 或自建驱动。

### 3.1 B 方案（import kit）到底是什么

现状：几乎每个 Interval/Text/LP 模块开头都是

```lean
import Mathlib   -- 一次载入约 8.8k 个 Mathlib 模块 / 约 5.4 GB olean
```

于是每个模块先付 **3.4 s / 5.5 GB** 的固定费，再编译自己。

kit 化 = 只 import 这个文件**真正用到**的子模块。例如一个只需要实数、`linarith`、`ring`
的文件：

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
```

车道合成探针实测：**3.59 s / 5.62 GB → 0.99 s / 1.41 GB**（wall −73%、RSS −75%）。

**为什么不能直接全仓改：**

- Lean 的 import 是传递闭包；少一个子模块，文件里某个 lemma/tactic/instance 就变成
  `unknown identifier`，编译直接失败。它是 **fail-fast**，不会静默造假；但 11,241 个模块
  各自到底用了哪些 Mathlib 名字，没有现成清单，只能逐模块编译验证。
- `Kepler.Interval.Basic` 只有一行 `import Mathlib`，但 **7,844 个 Kepler 模块**经它继承
  整个 Mathlib 面；改这一行 = 改这 7,844 个文件的可用引理面，风险最大。
- 车道只验证了 `linarith` / `ring` / `norm_num` 三条 tactic 的 toy 文件；真实 Cases/Text
  文件可能还依赖 `positivity`、`field_simp`、`interval_cases`、`Real.pi` 引理等，必须实测。

**B 的试点做法（尚未执行，需用户批）：**

1. 选一个**新增/孤立**模块（不动 `Interval.Basic`），把 `import Mathlib` 换成最小 kit；
2. `lean -o /tmp/...` 编译，RC=0 / error=0；
3. 再跑 `#print axioms`，确认仍恰标准三（正常情况漏 import 会先编译失败，但双检不省）；
4. 记录 wall/RSS，与 `import Mathlib` 基线对比；
5. 通过后试一个小簇（同目录 3–5 件），再决定是否拆入口：
   `Kepler.Interval.Basic`（最小）+ `...BasicMathlib`（全量），新文件只依赖最小入口。

**收益边界**：小模块/轻件的 wall 与 RSS 大降，可让 3 槽更安全；重证明件的 import 只占
0.05–0.6%，kit 不解决它们；`CertShards` 的 ~1.6 GB 地板主要是数据 olean，不是 Mathlib，
kit 对它们收益有限，需另测。import 不是公理，**不改信任面**；但改源文件 import 面属于
代码改动，需要用户批 + 正常编译闸。

### 3.2 `precompileModules`：IR 解释器 → 本机共享库（机制探针 + 真实 shard 探针 GO 条件式）

> 状态：**机制成立 + 真实 QuadR shard 有界探针收线 GO（条件式）**
> （2026-11-22 `precompile-shard-probe-w1`，编排者独立复跑）；**尚未 production 化、
> 未改主仓 lakefile/驱动**。探针证明执行模式与收益；Pent/Hex 未实测。

**机制探针（2026-11-22，编排者，`/tmp`，主仓零改动）**：core-only `fib35`，
`precompileModules=true` 把 `Bench.Fib` 编成 dylib；`lake env lean --load-dynlib=... Bench/Use2.lean`
（源文件无 `set_option`）→ **0.25 s / 0.17 user**；同一文件不加载 dylib →
**4.86 s / 4.76 user**（约 **19×**）。只设 `interpreter.prefer_native=true` 但不加载
dylib → 4.8 s（无改善）；加载 dylib 后加不加 `-D` 都是 ~0.25 s。**结论：
`--load-dynlib` 加载预编译模块是开关，`precompileModules` 单独不够（裸 `lean` 不会自动
加载）。** 真实 shard 的 blocker 是巨型数据模块（`QuadData` 32.9 MB / `PentData`
344.8 MB / `HexTop` 295 MB olean）的 C 编译时间与 dylib 体积，**当时未测；Quad 已由
下节探针实测，Pent/Hex 仍未测**。

**真实 shard 探针（2026-11-22，`precompile-shard-probe-w1`；编排者独立复跑）**：在
`/tmp` island 内用同一 `lean -c` 调用重建热闭包 olean+C、clang 链 dylib，`--load-dynlib`
运行真实 `QuadR` shard：

| 门 | 车道实测 | 编排者复跑 |
|---|---|---|
| 1 热枚举（10 roots × 20k pop，不跑 shard） | 14.03 → 3.15 s（4.45× wall / 5.18× user），输出 `(1583,8)` 相同 | **14.03 → 3.15 s（4.45× wall / 5.24× user），输出相同** |
| 2 `QuadR/K068`（只热 dylibs，数据不预编译） | 110.43 → 9.76 s（11.3×） | — |
| 2′ `QuadR/K068`（热+数据 dylibs） | 110.43 → 8.56 s（12.9×） | **107.41 → 8.14 s（13.2× wall / 13.75× user）** |
| 3 `QuadData` / `QuadTop` 的 `lean -c` + clang | 21.15 + 64.88 s；峰值 5.45 GB；dylib 2.28 + 4.78 MB | **21.89 + 68.31 s；峰值 5.42 GB；dylib 2.28 + 4.78 MB** |
| 3′ `QuadR/K071`（~22 min 长 shard） | 1,341.63 → 97.36 s（13.78×） | **native 97.14 s / 96.65 user（基线沿用车道 1,341.63/1,338.90；前车道 1,366.77 user）** |

- 一次性成本 **~90–100 s / 峰值 5.42 GB / dylib 合计 7.06 MB**；每 shard 省 ~100 s（K068）
  到 ~1,244 s（K071）。[EST] 192 件计时 32.49 h → 580 件 ~98 h，12–14× 后 **~7–8 h，
  省 ~90 h 量级**（Pent/Hex 未测，不外推为实测）。
- 信任面：K051/K068/K071 的基线/native `#print axioms` 逐字节相同；公理陈述哈希
  `a6a1ebeb84ff6a2b` / `c9122927f44dcfea` / `b24391d051620466` 与
  `docs/trust-base.tsv` 第 548/571/575 行一致（编排者重算 K068/K071 均 MATCH）。
  未新增 axiom/sorry/native_decide；585 名字/数量/类别不变。
- **production 化前必须消除三件探针手段**：① 11 个非预编译模块的 no-op 初始化器桩；
  ② 2 个跨包特化垫片（Mathlib `List.elem`、Plausible `List.foldr/sum`）须由真实
  Mathlib/Plausible native 闭包提供；③ `-c` 重建 olean 与主仓缓存 olean 同源同体积但
  SHA 不同，manifest 须记“源码+olean+dylib”三哈希或统一重建。
- 工程前置：预编译模块的 `initialize_M` 会调每个 import 的初始化器（缺失即 NULL 崩溃）；
  `Graph.fgraph` 定义在 `RelativeCompleteness`，须一并编译；`LEAN_PATH` 首项必须含完整
  import 闭包；Lake `:dynlib` facet 会构建 `Mathlib:shared` 并写主仓 `.lake`（探针已弃用，
  改手动 `lean -c`+clang，污染已清理）。复现脚本 `run_shard_perf.sh` 在 macOS bash 3.2
  的 `set -u` 下空 `ARGS` 会报 unbound，需用 `${ARGS[@]+"${ARGS[@]}"}`（编排者复跑补丁）。
- **Pent/Hex 未开**：`PentData` 344.8 MB → `-c` [EST] ~220 s、RSS 可能 10–20 GB；
  `HexTop` 前车道单编 20.71 GB，加 codegen 很可能贴 24 GB 闸。Pent 先只做 `Pent/K100`
  单件；Hex 须专用窗口 + RSS 探针。**均需用户另批，不量产。**

**机制依据。** 当前 `native_decide` 在 Lean 4.32 的 `Lean/Meta/Native.lean:31-67`
固定走 `addAndCompile` → `evalConst` → 检查 `Bool = true` → 生成 native 公理；
本仓重片 profile 约 99.9% 为 IR `interpretation`，且 `LEAN_CC` 零调用。Lake 的
`precompileModules`（本 toolchain `lake/README.md:196-207`、`Lake/Config/LeanLibConfig.lean:75-82`）
则会把模块编成本机共享库，并在 import 时加载，官方用途就是加速求值/metaprogram。
这是目前唯一与实测瓶颈直接对应的执行模式候选。

**后续试点（Quad 已过闸；以下需用户另批）：**

1. **Production 化三件**（真实初始化器闭包、真实 Mathlib/Plausible native 闭包、
   “源码+olean+dylib”三哈希 manifest），先复跑 K051/K068/K071；通过后再做
   **`Pent/K100` 单件**试点（`PentData`/`PentTop` 的 `-c` [EST] ~220/~250 s，RSS 可能
   10–20 GB，单槽独占）。不得全仓 11,241 模块一次开启。
2. 已选**手动 `lean -c` + clang** 路线（Lake `:dynlib` 会 `fetchImportLibs
   compileSelf=true` 构建 `Mathlib:shared` 并写主仓 `.lake`）；裸 `lean` 必须显式
   `--load-dynlib`（机制探针已证）。每批记录首次 C 编译/链接成本和每 shard 增量成本。
3. Pent 通过后再测一个 HexR 根与 `HexTop` 数据模块；前车道 `HexTop` 单编已 20.71 GB，
   加 codegen 须专用窗口先做 RSS 探针。**止损**：任一数据模块 `lean -c` >2–4 h 或
   dylib >数 GB，或 shard 加速 <2×，停止并交 UNRESOLVED。
4. 比较 CPU/wall/RSS/olean/native-lib 体积，并逐条核对布尔结果、定理陈述、585 公理
   名字/数量/类别。禁止新增 `extern`/`implemented_by`/公理；native 与 olean 必须同
   源同哈希，不能混用 stale 产物。
5. 采用前需把构建方式写入 manifest 并确认仍属现有 `native_decide` 信任类别；否则
   不采用。外部编译求值程序只能用于导航，不能凭其输出直接生成验收证明。

**与其它杠杆的关系：**若本机执行有数量级收益，优先于 C1+C3；若只有小幅收益，先做
C1+C3 的同语义 DEF-FIX。`-j` 不解决单线程 IR 枚举主循环，`decide +kernel` 也不是
免费替代品（既有全基座内核重放已判不可行）。

## 4. 不要做

- 无界 `lake build` / 全树构建（Lake 5.0 全核扇出；AGENTS §4 永久禁止）。
- 用 `native_decide` 提速（更慢 + 新增公理）；新增 585 之外的任何 `native_decide`。
- 静默引入 `@[implemented_by]` / `@[extern]`（信任面变更，且 codegen 不在 olean 路径）。
- `-M` 当加速旋钮（低于峰值直接 `memory_exception`）；靠 `touch` 触发重编（内容哈希）；
  用 `cmd | head` 的退出码判成功（崩溃可能回 0）。
- RAM disk / ccache（olean 构建不调 clang，无对象可缓存；热态 APFS 读 5.4 GB 约 1.7 s sys）。

## 5. 未闭合（UNRESOLVED）

- `precompileModules`：Quad 热闭包+数据已实测（K068/K071），**Pent/Hex 未测**；
  production 化三件（真实初始化器、真实跨包 native 闭包、三哈希 manifest）未做；
  K071 的基线未由编排者重跑（只复跑 native，基线沿用车道/前车道）。
- `Kepler.Assembly` / `Kepler.Final` 岛件与 `Graphs`/`LP` 分片的 `-j` 曲线：测量窗口内
  `Graphs` 318/951、`LP` 6/1,150 olean 缺失；探针 `probe/mods/P_assembly.lean` 已备。
- `interpretation` 桶的逐文件触发机制（可用线索：linarith 14–21 ms/次 + 巨型项 simp/unfold）。
- `--incr-save/--incr-load`、`--server`、`-T`、RAM disk（按优先级未测）。
- import-kit 的全仓可行性：toy 只验证了 linarith/ring/norm_num 三条 tactic。
- 快照缺口：3 并发重件的原始 `time_*.log` 留在 `/tmp/csr_conc_*`，未随快照保存；
  `cc_calls.log` 未保存。编排者已用自建 wrapper 与 `/tmp` 原始日志复核，数字成立。

## 6. 复测入口

```bash
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$(cat ~/c17_backup/lane_snapshots/compile-speed-research-w1/data/lean_path.txt)"
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean

# 单文件（-j 曲线 / 计时；输出只写 /tmp）
/usr/bin/time -l nice -n 19 lean -j2 -o /tmp/p.olean Kepler/Interval/Cases/C4717061266/CertD.lean

# 分层归因
nice -n 19 lean --profile -o /tmp/p.olean Kepler/Text/ZTGJoint0000CornersP.lean 2>&1 | tail -30
```

合成基准与整套 harness 在快照 `bench/`（`run_bench.sh --suite {core,mathlib,real}`）；
新机器 30 分钟流程、换版本回归表、发布预算模板、踩坑 10 条见快照 `PLAYBOOK.md`。
复测前过 guard：`lean ≤3 ∧ 总 RSS ≤24 GB ∧ pressure <2`，并记录并发环境。

## 7. 复核记录

- 快照 169 件、MANIFEST 全 OK、0 symlink；主仓 tracked 零改动；无新增 axiom/sorry。
- 编排者独立复跑：空文件 0.20 s / 0.39 GB；`Interval.Basic` 3.48 s / 5.47 GB；
  `Mathlib` 3.59 s / 5.62 GB；kit A/B 1.46/0.99 s；fib30 0.60/0.17 s；
  CertD `-j1`/`-j2`；`lake build -j1` 报错；3 并发原始日志重算 CPU 687.5/998.7。
- 重件原始 profile：`ZTGJoint0000CornersP` 503.52 s / 4309.92+611.24 CPU-s / 21.25 GB；
  `PackingAuto21` 483.51 s / 16.33 GB；`NliBanksZTGIJCF4Dih` 185.14 s / 11.35 GB。
- 复算 `P_packineq`（6,890 Kepler 模块闭包）：冷 wall 7.98 s，CPU 4.96 s，RSS 6.53 GB
  （相对 Mathlib 3.42 CPU-s，加 1.54 CPU-s / 1.06 GB），与车道热态 4.78 s 的结论一致。
