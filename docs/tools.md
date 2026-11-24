# 工具与操作入口

> 2026-11-22 汇总。本文回答“工具在哪、怎么跑、看哪个输出、结果能证明什么”。
> 实时状态与实测数字仍以 [`priority-queue.md`](priority-queue.md) 为准；硬规则仍以
> [`../AGENTS.md`](../AGENTS.md) 为准。`/tmp` 和车道快照中的工具不是主仓 tracked 源码，
> 换机器或重开 session 时先核对它们仍存在、版本与哈希仍匹配。

## 1. 当前源码可视化（不需要 olean）

现有两个页面都是 **`SOURCE_STATIC`**：用于当前源码导航、债务分族和 import DAG，
**不是 proof-term 可达图，不替代 `#print axioms` 或 `e2e_reach_map`**。

### 1.1 当前 NLI 债树

- 页面：<http://127.0.0.1:8791/>
- 内容：当前 Assembly NLI 债、分族和源码定位；不会把已关闭的小模块继续算作债。
- 生成器：`build_current_nli.py`；数据：`current_nli.tsv`、`tree.db`、`manifest.json`。

```bash
VIZ="$HOME/.zcode/v2/visualizations/571e2f5484263141668294a63494107b5f37ee99532a11d2a7d3d625ceaa225b"
cd "$VIZ/nli-current-tree"
PYTHONDONTWRITEBYTECODE=1 python3 -I build_current_nli.py
python3 server.py . 8791
```

成功重建的末行是 `CURRENT_NLI_OK`，并要求 `missing_parent=0`、`missing_edge=0`。
`manifest.json` 记录生成时 HEAD、输入和生成器哈希；HEAD 或车道状态变化后应重建。

### 1.2 当前 Text 模块/声明源图

- 页面：<http://127.0.0.1:8792/>
- 内容：tracked Text 模块、声明、分族和 Text 内部 import 边，可查看模块源码。
- 生成器：`build_current_text.py`；数据：`current_text.tsv`、`tree.db`、`manifest.json`。

```bash
VIZ="$HOME/.zcode/v2/visualizations/571e2f5484263141668294a63494107b5f37ee99532a11d2a7d3d625ceaa225b"
cd "$VIZ/text-current-tree"
PYTHONDONTWRITEBYTECODE=1 python3 -I build_current_text.py
python3 server.py . 8792
```

成功重建的末行是 `CURRENT_TEXT_OK`，同样要求缺失父边为零。这里的源码 `sorry`
计数包含锥外 Text/LP 骨架；账本的 **Text 0 是 e2e 锥内口径**，两者不可混用。

### 1.3 使用与停机注意

- 启动前检查对应端口是否已有服务，不要双开；上述两个服务目前由编排者后台任务维护。
- 停止时只终止该页面记录的 PID，不用 `pkill python` 一类宽匹配。
- 旧 `8790` 是历史 proof-term 快照，已停止；不要仅改数据库 meta 冒充当前树。
- 完整 proof-term 导出器是 `lean/scripts/export_e2e_tree.lean`，需要可用的 Assembly
  olean 闭包。恢复链现已停止，详见 §7；不能用静态源图代替这项验收。
- 数据口径和旧导出器细节见 [`e2e-tree-visualization.md`](e2e-tree-visualization.md)。

## 2. HOL 单根 instrument / fat1 终端导出

车道：`fat1-terminal-export-w1`。它在复制到 `/tmp` 的 HOL Light/Flyspeck 源码上插桩，
导出真实二叉搜索树、glue open/close、父子盒和终端 f/df/ddf/error/上下界；不改主仓
`reference/`。

### 2.1 位置与前置条件

- 可复现入口：`~/c17_backup/lane_snapshots/fat1-terminal-export-w1/REPLAY.sh`
- 运行目录：`/tmp/fat1-terminal-export-w1/`
- 插桩源与补丁：快照 `instrument/`
- 输入准备、运行和验证脚本：快照 `scripts/`
- 需要 OCaml native compiler、Camlp5 及该 Makefile 声明的库；当前兼容修复只适用于
  快照内版本组合，换版本必须重新做小探针。

**对象身份是硬闸。**当前上游 `ineqs.txt` 的 case 2028 已不是 fat1；本工具的单行输入
从原 fat1 条目提取后重编号为 2028。必须核对 `out/input_audit.json`、输入 SHA 和
`scripts/validate_tree.py` 的 `EXPECTED_HASH`，不得直接对整份 `ineqs.txt` 跑 2028。

### 2.2 真实重放与只读验证

```bash
# 会真实串行构建并运行唯一 #2028，不是 dry run。
bash "$HOME/c17_backup/lane_snapshots/fat1-terminal-export-w1/REPLAY.sh"

# 已有导出时，只重跑结构/身份验收，不重新运行 HOL 树。
cd /tmp/fat1-terminal-export-w1
python3 -I scripts/validate_tree.py
```

成功重放末行为 `REPLAY PASS`。主要输出：

| 文件 | 用途 |
|---|---|
| `out/hol_events.jsonl` | 原始插桩事件流 |
| `out/result_tree_2028.json`、`RESULT_TREE_2028.tsv` | 真实树与父子关系 |
| `out/TERMINALS_2028.tsv` | 真实终端盒与导数/误差数据 |
| `out/run_audit.json` | 进程 RC、时间、输入/verifier/导出哈希 |
| `out/tree_validation.json` | 树完整性、根盒、终端和定理哈希验收 |
| `logs/replay.log` | 重放总状态 |

**边界：**只跑注册的单根，不跑八根或全树；真实树 PASS 不等于终端与 Lean checker
兼容，也不等于顶层减债。只有通过树验收的注册真实终端才能进入双求值和
unchanged-checker 闸；certtm/Mono*/D 层继续 hold。最新终端状态见
[`priority-queue.md`](priority-queue.md)。

## 3. 单模块 Lean 编译、guard 与复制式岛

当前编排 wrapper：`/tmp/land-batch-w1/orch_compile.sh`。它提供 3 槽信号量、
`nice -n 19`、PPID=1 自杀检查，并调用 `~/c17_backup/orch_guard.sh` 检查 Lean 数、
总 RSS 和内存压力。

```bash
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
mkdir -p /tmp/kepler-check
MODULE=YourModule
bash /tmp/land-batch-w1/orch_compile.sh \
  "lean/Kepler/Text/${MODULE}.lean" \
  "/tmp/kepler-check/${MODULE}.olean"
```

- 日志应保留完整 stdout/stderr 和 `/usr/bin/time -l`；验收要求 RC=0、error=0，
  不能只凭 olean 出现就判 PASS。
- 可用 `ORCH_LP_PREFIX=<复制式岛>` 前缀扩展 `LEAN_PATH`。首个含 `Kepler/` 的 entry
  必须提供完整解析树；岛池只能 `cp/rsync`，禁止 symlink，写前检查 `test -L`。
- 共享 wrapper 不支持拿 `ORCH_SOURCE_ROOT` 任意切换源根；需要 `/tmp` 源根时使用
  经审查的车道 wrapper，不能假设设置该变量就够。
- 编译脚本禁止 `exec` 起 Lean，以免 EXIT trap 不释放槽位。发现槽目录先做进程/
  日志/持锁者取证；有有效编译活动时绝不能 `rmdir`。
- Graphs/Interval 的 shard 禁止 `lake build`；全树 build、`auto_gate.sh` 和地图仪器
  也不由车道运行。详细硬限制见 [`../AGENTS.md`](../AGENTS.md) §3–§4。

## 4. `#print axioms` 验收

唯一验收语言是 `#print axioms`。根定理探针已在
[`../lean/Kepler/Final.lean:29`](../lean/Kepler/Final.lean#L29)：

```lean
#print axioms the_kepler_conjecture_e2e
```

**验收 root = Kepler.Final**（P0-1，2026-11-23 用户明批）：lakefile 命名验收
target `KeplerAcceptance`（`roots = ["Kepler.Final"]`）是根面验收声明的编译入口；
`defaultTargets = ["Kepler"]` 的闭包（1,249 模块）不含根定理，全树构建被
AGENTS §4 禁止。静态自检（零编译）：`python3 scripts/check_acceptance_targets.py`
或 `make acceptance-check`（含 P0-3 sorry census 对账）。根探针也已并入
`lean/scripts/AxiomAudit.lean`（P0-2）。

依赖池恢复后，可由编排者用 §3 的 wrapper 编译 `lean/Kepler/Final.lean` 并亲读输出。
当前恢复链已停止，**不要把小模块审计写成完整 Assembly/Final 根面复验**。

新定理应在独立审计文件中 import 对应模块并逐条 `#print axioms`：

```lean
import Kepler.Text.YourModule
#print axioms Kepler.Text.your_theorem
```

编排者必须亲自编译审计文件并核对 RC/error；新增定理通常要求恰标准三，零 `sorryAx`。
根面的标准三、585 条地面 `native_decide` 和当前 sorry 口径见
[`../AGENTS.md`](../AGENTS.md) §1 与 [`trust-base.md`](trust-base.md)，不在此另抄数字。

## 5. `precompileModules` / `--load-dynlib` 探针

这是针对 `native_decide` IR 解释执行瓶颈的执行模式工具，不是新公理或许可证。
机制、已做探针和止损见 [`compile-speed.md`](compile-speed.md) §3.2；当前车道状态见
`priority-queue.md` 的 `precompile-shard-probe-w1`。

裸 Lean 加载预编译模块的形式为：

```bash
DYLIB=/absolute/path/to/same-source.dylib
PROBE=/absolute/path/to/Probe.lean
lake env lean --load-dynlib="$DYLIB" "$PROBE"
```

仅设置 `precompileModules=true` 不会让裸 Lean 自动加载已有库；仅设
`interpreter.prefer_native=true` 也不等于已加载对应 dylib。探针必须记录源/olean/dylib
哈希，防止 stale 库替换语义；不得全仓一次开启，不得借优化新增 `native_decide`。
真实 shard A/B 未过闸前，不得把 core-only 小型探针的加速比外推到 585 或全库。

## 6. 信任基座 manifest

仓内工具：[`../scripts/trust_manifest.py`](../scripts/trust_manifest.py)。

```bash
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
python3 scripts/trust_manifest.py --check
```

- `--check` 只校验，不写 `docs/trust-base.tsv`；默认模式会生成该文件，只由编排者使用。
- 它从仪器 TSV 取公理名单，检查地面性、shard-range 无缺口/无重叠分解、数据源和
  生成器 SHA。
- 它会调用 `lake env lean` 读取 Assembly olean，**不是纯文本扫描**；Assembly 闭包缺失时
  不能拿旧 manifest 冒充当前通过。
- 它审计 585 信任基座，不替代根定理 `#print axioms`，也不授权新增公理。

## 7. olean 定向恢复：已停止，等待新负责人

用户于 2026-11-22 要求停止 `pool_recovery_wt2a.py` 及当时 K000 编译，后续交给其他
负责人。当前**没有本恢复链运行实例，不得从本文自动重启**。

交接正本：

```text
~/c17_backup/lane_snapshots/cell3-wt2a-prod-w1/
  ORCHESTRATOR_CHECK/recovery_stop_2026-11-22/STOPPED.md
```

同目录保存调度器、handoff、编译 wrapper、进度日志、K000 停止日志和
`STOPPED_SHA256SUMS`。后续负责人须先重扫当前闭包、核对 regular-file olean、确认无
其他实例，再重新提交恢复范围/worker 数供裁决；不要沿用旧 ETA 或直接把旧分母相减。

**2026-11-23 补充（`precompile-integration-w1`；审计 GO 后已安装）**：Phase D 的
**300 个缺失 shard（HexR 219/Hex 66/PentR3 10/HexR2 5）+ HexTop** 已完成可安装性审计，
**300/300 GO**（shadow 池 = 主池 Kepler 树复制 + overlay；plain lean import 300/300、
公理/陈述哈希 300/300 MATCH、依赖闭包 340 模块 0 blocker）。**2026-11-23 07:25 已安装
301/301 到主仓 `.lake`**（SHA/字节后验一致；主池 olean 7,704→8,005；回滚 = 删除
`precompile-integration-w1/data/install301.tsv` 的 301 个 relpath）。安装后主池
**580/580 审计 MATCH**（2.14 s / 1.68 GB）。**根面 replay 仍 BLOCKED**：
首缺 `Kepler.Graphs`；安装 301 后仍缺 **1,028（Final 口径）/1,031（重扫口径）** 非 shard
模块（Text 446 / Graphs 非 shard 297 / TameSpine 267 / Interval 18），需常规定向编译；
harness `precompile-integration-w1/prod/run_acceptance_replay.sh` 当前 RC=2。
`PROD_MANIFEST.tsv` 的 986 行是 985 依赖模块 + bundle，不含 580 个消费者 shard；
shard olean 的 SHA 以 `phaseD/olean` 归档 + `measurements_all.csv` 字节为准。

**2026-11-23 09:28 补充（恢复重启 + 混世界）**：2-worker 恢复已重扫并续跑，
closure 8,868 / present 8,164 / **missing 704**（09:28 快照；实时以 pq 与
`olean-recovery-2w-w1/STATUS.md` 为准）。首轮 324 件 rc=0，6 件 deferred：5 件因并发
`lake build` 临时缺 `PackingAuto13`，1 件 `CertPent` 因池内两个 `Inhabited Graph`
世界不兼容。`Kepler/Graphs/CertPent|CertHex|TopReplayHex` 已用 `goodlist-w4` 的
source-identical canonical 预编译 olean 恢复并审计（198/290 条 trust-base 公理 + 标准三，
无 `sorryAx`）。**主池仍混用 300 个 canonical（Phase D shards）与 360 个 non-canonical
（旧 shards/CertCheck 等）**；恢复期间禁止与 `lake build` 共用主池，未来车道不得重编
跨世界消费者或覆盖 `CertCheck.olean`。永久修复 A（重建 280 旧 shard，天数）/
C（保留混合池 + 不变量）待裁决；证据与复现见
`~/c17_backup/lane_snapshots/olean-recovery-2w-w1/SHARD_WORLD_BLOCKER.md`。
下一个里程碑 = missing 0 + 根面 harness。

**2026-11-23 13:53 补充（恢复收线 + 根面复现，续1425）**：`olean-recovery-2w-w1` 完成：closure 8,868 / missing **0**（Final 闭包 8,869 全齐；本轮新装 1,033，详见 pq §8 续1425）。**编排者亲跑** `run_acceptance_replay.sh --pool <主池>`：589 = 585 native + 标准三 + `sorryAx`，585/585 在册、UNEXPECTED 仅 `sorryAx`（harness FAIL 只由 49 条锥内 sorry 债触发，预期态）——根面自基线 AQ `e4c384e6` 后首次可复现。根面验收从此按本文 §4 口径随时可跑；混世界 A/C 与 D1 缺陷处置仍待裁决（见 pq 续1425）。

## 8. 检索、补丁和哈希工具

### 8.1 快速检索

agent 优先使用专用 Grep/Glob 工具。shell 中统一用快速 rg，避免裸 grep 扫仓：

```bash
~/.kimi-code/bin/rg -n -E '^(theorem|lemma|def|noncomputable def) your_theorem' lean/Kepler
~/.kimi-code/bin/rg -n 'pool_recovery_wt2a|STOPPED' docs scripts
```

`rg -r` 是 replace 旗标；查行号要显式 `-n`。grep 命中注释不代表声明存在，落库判断
仍需真实声明或 `#check`。

### 8.2 车道 patch 预检

```bash
git apply --check /path/to/lane/patch.diff
# 应用后再查，防止 rename/删除和意外 untracked 文件：
git status --short
```

Lean patch 双侧路径必须是 `a/lean/...`、`b/lean/...`。纯新增与 DEF-FIX 分开，零删除
diff 不自动等于零风险。落库前仍需编排者亲编和公理审计。

### 8.3 哈希校验

```bash
cd /path/to/snapshot
shasum -a 256 -c SHA256SUMS
```

车道可能改用 `PAUSED_SHA256SUMS` 或 `STOPPED_SHA256SUMS`；以交付记录指定文件为准。

### 8.4 `integrate_lane.sh` 不是默认快捷键

`scripts/integrate_lane.sh` 会复制、stage，并串联旧 `auto_gate`、commit/push；即使
`--dry-run` 也会真实执行前面的写入步骤。当前车道纪律禁止它包含的旧全量闸流程，
因此不要把它当普通 patch 应用器运行；落库按 [`../AGENTS.md`](../AGENTS.md) §5 逐步执行。

## 9. 最短排障顺序

1. 先查真实进程、日志 mtime 和交付目录，不信“完成/失败”通知字面。
2. 再查源码、patch SHA、olean 是否 regular file、岛是否零 symlink。
3. 编译只走受 guard 的单文件路线，保留完整日志和 RC。
4. 数学交付必须独立重编 + `#print axioms`；根面结论必须编排者亲跑 Final。
5. 无法核实就标 UNRESOLVED；静态导航、数值采样、进程退出和旧 olean 都不能冒充证明。

## 编排者内存护栏 memlim.sh（2026-11-23 用户明批）

**背景**：FamilyG2Base 编译 footprint 133 GB（RSS 16 GB）把 swap 推到 97% 并被系统杀（续1445）；macOS 无 cgroups、`ulimit -v/-m` 不生效——轮询杀是唯一可靠的进程级内存限制。

**用法**：`~/c17_backup/memlim.sh [--rss-gb N] [--name TAG] -- cmd args...`
- 后台启动 cmd，每 `MEMLIM_POLL`（默认 5 s）轮询 **cmd 子树总 RSS**（BFS 覆盖 `lake env → time → lean` 深链）；≥ N GB → SIGKILL 子树，日志记 `BUDGET_EXHAUSTED(memcap)`，退出 137。默认 N=30。
- 内置 PPID=1 孤儿自杀（AGENTS §4）。日志 `${MEMLIM_LOG:-/tmp/memlim_<TAG>.log}`。
- **v2 关键语义**：只杀 cmd 子树，绝不碰调用者进程组（v1 按进程组杀误伤父 shell，部署前废弃）。
- 实测（2026-11-23）：正常通过 / 3 GB hog @2 GB cap 杀（rc=137，父 shell 存活；hog 的子树 RSS 读数 6 GB——bytearray 页计口径偏大，护栏判定偏保守，可接受）/ 包装 `lake env lean` 链 / `--version` 零耗。
- **车道义务**：所有 lean 编译一律包 memlim（编排者按件定 cap：W4 全尺寸 12 GB / ZTG M3 15 GB / wt1-close 12 GB〔续1453 errata 前为 8 GB〕）；`BUDGET_EXHAUSTED(memcap)` 是资源护栏事件，不是数学判词（§7.2）。
- **ERRATA（2026-11-23，wt1-close 车道实测、编排者收账）**：ps 子树 RSS 轮询口径**虚高 ~1.6×**（读 11 GB vs `/usr/bin/time` 真实 peak 6.83 GB，同一进程）——判定偏保守方向（早杀不漏杀），但会误杀本可完成的编译；关键长编译建议并行挂 `/usr/bin/time -l` 记真实 peak，双口径入报告；cap 定值按虚高口径换算（真实峰 × ~1.6 留余量）。
- **口径定标（2026-11-24，续1454）**：wt1-close 第二轮定标 real 6.5 GB → ps 读 ≥12 GB（**虚高 ~1.85×**，与 1.6× 同向）；wt1-close 帽据此 12→16 GB（ps 项，最保守 1.6× 换算真实 ≈10 GB）。**`ps -o footprint` 口径实测否决**（3 GB bytearray hog 的 footprint 读 ~55 MB，与 rss 3.16 GB 差 57×，不跟踪物理分配）——memlim 保持 ps 口径不变；替代口径不再排查。容量规划换算：real ≈ ps 读数 ÷ 1.6（取最保守）。
- **v2.1（2026-11-24，续1456）**：日志默认 `/tmp/memlim_<TAG>.log` → **`~/c17_backup/logs/memlim_<TAG>.log`（持久）**。教训：04:20 内核 panic 后 /tmp 全清，事故取证（哪些 guard 开过火）不可重建。另两条配套制度（账本续1456）：无人值守时段**同时只许一条车道持 lean**；checkpoint 原则 = 重跑成本 > 5 分钟工作量的进度必须落快照（/tmp 工作区在重启后即不存在）。
