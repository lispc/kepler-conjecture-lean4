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

## 4. 不要做

- 无界 `lake build` / 全树构建（Lake 5.0 全核扇出；AGENTS §4 永久禁止）。
- 用 `native_decide` 提速（更慢 + 新增公理）；新增 585 之外的任何 `native_decide`。
- 静默引入 `@[implemented_by]` / `@[extern]`（信任面变更，且 codegen 不在 olean 路径）。
- `-M` 当加速旋钮（低于峰值直接 `memory_exception`）；靠 `touch` 触发重编（内容哈希）；
  用 `cmd | head` 的退出码判成功（崩溃可能回 0）。
- RAM disk / ccache（olean 构建不调 clang，无对象可缓存；热态 APFS 读 5.4 GB 约 1.7 s sys）。

## 5. 未闭合（UNRESOLVED）

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
