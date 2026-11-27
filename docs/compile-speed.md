# 编译速度（Compile Speed）— 现状、实测、优化与实验台账

> 状态：**活文档**（最后更新 2026-11-27）。编译速度专题的**持续维护页**；
> 2026-11-21 的调研基线（§1–§7）保留原文，2026-11-26 起的普查/实验增量见
> §1.1、§3.3、§8。pq 只记日期与结论并链接本页，不再另抄一套数字。
> 规则：每个数字带**日期 + 来源**（commit 或快照路径）；实测与 `[EST]` 分开；
> 任一新测量先入本页，再在 pq 记一行。
> 任何构建/驱动改动（全局 `-j2`、import kit、precompile 接入、`lakefile` 改动）
> 仍**需用户明批**——本页记录不等于已应用。
> 证据：`~/c17_backup/lane_snapshots/compile-speed-research-w1/`（2026-11-21，169 件，
> `MANIFEST.sha256` 全 OK，0 symlink；`REPORT.md` / `PLAYBOOK.md` / `bench/` /
> `data/` / `logs/`）；2026-11-26 增补来源见各节。

## 0. 一分钟现状（2026-11-26）

| 项 | 当前值 | 来源 |
|---|---|---|
| 验收闭包 | **9,137 模块**（`Kepler.Final`） | `scripts/check_acceptance_targets.py`，2026-11-26 |
| 全仓 Lean 文件 | 11,241（`Interval/Cases` 7,600、`LP` 1,150、`Graphs` 951、`Text` 1,097） | 2026-11-21 基线；TskXLLIPLS 已含 |
| 4.36 census | **OK 877 / REUSED 100 / BLOCKED 0 / DEFERRED 1 / BUDGET_CAP 2**（2026-11-27 08:19 快照；主队列仍在跑） | `lean436-census-w1/census.tsv` |
| 最大单族成本 | **TskXLLIPLS 6,819 模块 × 29 s ≈ 55 CPU·h** | parity card / census 实测 |
| 第二大族 | **W1DC 221 箱 L1 = 3.73 CPU·h**（55–67 s/箱） | `fe1ec17f` 实测 |
| 固定 import 费 | **3.4 s CPU / 5.5 GB RSS**；9,858/11,241（87.7%）模块付此费 | §1 勘误 |
| 全闭包 import 地板 | 9,137 × 3.4 s ≈ **8.6 CPU·h** | 本页推算 |
| 4.36 全量重放预算 | TskXLLIPLS 51.6 h + **CertShards 237–465 h** + **Top\*Shard ≈1–2 h** + W1DC 3.7 h + 其余重件 ~10 h ≈ **303–532 CPU·h 串行**（import 已含在每模块时间，不再另加） | 2026-11-27 实测外推（R 360 件 37–75 min；Top\* 106 件 census 全编：104 OK、S000 >60 min、S013 顶 24 GiB `-M` 上限） |
| precompile 4.36 pilot | **GO：Hex 非 R 12.97× / HexR 12.96×**；bundle 1,041 模块 53.7 min / 19.40 GB；全量 575 投影 **19.1–23.3 h**（含一次性构建）；**全量 575 已批（2026-11-27），Phase 2A/2B 执行中** | `lean436-precompile-w1`（2026-11-27；oleans 与 census 池逐字节同） |

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

## 1.1 2026-11-26 族级成本普查（活数据）

> 口径：`Kepler.Final` 闭包 9,137 模块。主数据源 =
> `olean-recovery-2w-w1/measurements.csv`（1,042 次实测：wall 19,195 s /
> user+sys 23,226 s / 单件最大 1,911.9 s）、`lean436-pilot-w1/final_census.txt`（4.36）、
> `wt1-bulk-*`（L1 前，已作废）、`tsk-certunit-parity-w1/PARITY_CARD.md`、
> `tsk-certunit-m1-w1/RESULTS.md`。`[EST]` = 外推，不是实测。

| 族 | 模块数 | 源体积 | 单件实测 | 总量 | 机制 |
|---|---:|---|---|---|---|
| `Interval/Cases/TskXLLIPLS*` | 6,819 | 69.3 MB | 28.4–77.8 s（典型 29 s）/ 10.3 GB | **≈55 CPU·h 串行**（D5 78.19 CPU·h） | 内核 `decide` 深求值 |
| `Text/TaylorSecond/W1DC_*` | 221 生成 + 13 tracked | 66.6 MB / 777,090 行 | **55–67 s CPU** / olean ~3.6 MB（L1） | **13,445.5 s CPU = 3.73 h** | 内核 `decide`/`rfl` DC 树 |
| `Interval/Cases/*/Shard*` | 671 | 31 MB / 48,663 条 `by decide` | 最大 `C6096597438b/Shard1` **1,911.9 s / 10.9 GB** | `[EST]` 2–6 h | 内核 `decide` BBTree |
| `Interval/Cases/*Hull*` | 18 | 1.16 MB | **318–1,176 s / 9.6–12.5 GB**（14 件实测） | **1.92 h** | 内核 `decide` |
| `Graphs/TopReplay*` | 96 | 92 KB | p50 ≈18 s；最大 S013 **719.9 s / 22.17 GB** | **0.91 h**（87 件实测） | `decide +kernel` 重放 |
| `Text/LocalAuto*` | 91 | 10 MB | `LocalAuto35` **1,093.1 s / 10.0 GB** | **1.55 CPU·h**（90 件） | norm_num/linarith + 解释器 |
| `Graphs/CertShards/*` | 580 | 556 KB | census 实测：非 R Hex 23.5–606 s；**R 变体 37–75 min/件**（HexR.K001 2,216 s、QuadR.K000 4,478 s、PentR.K001 >70 min） | **全量 575 ≈237–465 h**（R 360 件 222–450 h + 非 R 14.6 h） | native_decide 分片（585 基座） |
| `Graphs/Top*Shard` | 106 | ~0.9 KB/件 | **`decide +kernel`**；**census 全编完成：104 OK + S000 `BUDGET_CAP`（>60 min）+ S013 `BUDGET_CAP`（24.0 GiB 顶 `-M 24576`，内核内存上限，非代码错误）**；OK 件 3.2–41.7 s | **≈1.6 h 实测墙钟和**（含 S000 3,682 s；S013 需 acceptance 单槽 `-M 0` 重跑） | 内核归约（**precompile 不覆盖**） |
| `Text/ZTG*` | 26 | 9.9 MB | `ZTGJoint0000CornersP` **503.5 s / 21.25 GB** | `[EST]` 1–2 h | norm_num/linarith 重建 |
| `Text/PackingAuto*` | 27 | 6.4 MB | `PackingAuto21` **483.5–519.1 s / 16.3–16.5 GB** | `[EST]` 0.5–1 h | 巨型项 simp/unfold |
| `Graphs/GoodListShard*` | 199 | 149 KB | PentS00 **21–26.6 s / 8.2 GB**；TriS00 3.2–4.2 s | ≈0.5 h | `decide +kernel` shard-range |
| `Graphs/ArchiveData`+`CertData` | 4 重件 | 26 MB | `Pent` **1,294.6 s / 20.57 GB**（4.36）；`PentTop` **973.2 s / 15.48 GB** | ≈0.65 h | 数据重建 + native shard |
| `Interval/Cases/*/CertD|P` | 9 | — | CertD 62.8–92.3 s / 8.3–11.2 GB；`CertP` **380.4 s / 22.2 GB**；`BernsteinRoot1100` 348 s / 17.2 GB | ≈0.3 h | norm_num/linarith 内核证书 |
| `NliBanksZTGIJCF4Dih` | 1 | 6,191 行 | **185.1 s / 11.35 GB** | 0.05 h | norm_num + 解释器 |
| `LP`（含 `W6Data`） | 1,150 | 28 MB | 多数轻；`W6AlignRoots` 107 s（42,855 行） | `[EST]` 0.5–1 h | 数据 def + 内核 decide |

**排序结论**：TskXLLIPLS 55 h ≫ **W1DC 3.7 h** > per-case Shard/Hull 4–8 h `[EST]` >
Graphs 重放与 Text 巨件各 1–2 h；另有 **9,137 × 3.4 s ≈ 8.6 CPU·h** 的 import 地板。

**内存分级（决定并发槽位）**：

| 档 | 单件峰值 | 族 |
|---|---|---|
| 16–22 GB，**只能 1 槽** | 22.17 / 22.2 / 21.25 / 20.57 / 17.2 / 16.33 / 15.48 | TopReplayS013、CertP、ZTGJointP、Pent、BernsteinRoot1100、PA21、PentTop |
| 10–12.5 GB，2 槽 | 10.0–12.5 | Hull、CertD、LocalAuto35、TskXLLIPLS（10.3） |
| ~6 GB，3 槽 | ~6 `[EST]` | W1DC（L1）、TopReplay 轻件 |

**4.36 全量验收重放预算**（census 只抽样，不等于验收）：

- TskXLLIPLS：6,412 叶 × 29 s ≈ **51.6 h 串行**；2 车道各 1 lean（2×10.3=20.6 GB）≈ 25.8 h 墙钟。
- W1DC：231 模块 × ~60 s ≈ **3.7 h**。
- **CertShards：全量 575 件 ≈237–465 h**（非 R 215 件 ≈14.6 h；R 360 件 222–450 h；`HexR.K001` 2,216 s、`QuadR.K000` 4,478 s、`PentR.K001` >70 min）；**远超单车道可接受范围**。
- **Top\*Shard：106 件 ≈1–2 h**（`decide +kernel`；9 件 census 实测 3.2–33.2 s / mean 11.9 s，唯 `TopBoundsHexShardS000` 60 min cap 未结束；**ERRATA**：原「31 min 未结束 ⇒ 50–60 h」是单件异常外推整族，作废）；**precompile 不覆盖**——4.32 的 13.889× 是 native_decide 分片，dylib 不加速核归约（该族已不是成本瓶颈）。
- 其余重件 + 证书：`[EST]` ~10 h。
- 合计 **≈303–532 CPU·h 串行**（import 已含在每模块时间，不再另加），**瓶颈仍是
  CertShards R 族（222–450 h）**。替代方案 A **已于 2026-11-27 4.36 pilot 实测 GO**
  （Hex 非 R **12.97×** / HexR **12.96×**；bundle 53.7 min / 19.40 GB；全量 575 投影
  **19.1–23.3 h**，含一次性构建）或 B（按族抽样 + 585 逐名审计）**已由用户 2026-11-27
  明批走 A**——先补 Pent/Quad + `QuadR.K000`，再全量 575，Phase 2A/2B 执行中；B 保留
  fallback。**Top\*Shard 不再是 A 的缺口**
  （≈1–2 h，可全编）；A 若获准全量，剩余验收串行 ≈ **85–91 h `[EST]`**
  （precompile 19.1–23.3 + TskXLLIPLS 51.6 + W1DC 3.7 + Top\* 1–2 + 其它 ~10）。

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

### 3.2 `precompileModules`：IR 解释器 → 本机共享库（三族全量 580/580 PASS）

> 状态：**生产化三件已消除 + Quad/Pent/Hex 全量 580/580 PASS**（2026-11-23
> `precompile-prod-all-w1`，编排者独立复核）；总 **7.184 h**，192 件基线聚合 **13.889×**，
> 580/580 审计 MATCH；HexTop 23.66 GB < 25 GB。**未改主仓 lakefile/驱动，未接入正式构建**。

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

**生产化与 Quad/Pent 复验（2026-11-22，`precompile-prod-quad-w1`；编排者独立复跑）**：

| 项 | 结果 |
|---|---|
| 真实初始化器闭包 | 11 个原桩模块全部真实 `lean -c`；真实闭包 = **944 包模块 + 39 Kepler + 1 PentTop = 984**（探针 11 个 no-op 桩砍掉了 944 个包模块）；bundle 内 **984 个 `_initialize_*` 符号**；无 stub/shim |
| 跨包特化 | 真实 `Mathlib.Tactic.Translate.Core`、`Plausible.Gen` dylib 提供 `List.elem`/`List.foldr` 特化；无 shim |
| manifest | 984 模块 × source/olean/dylib 三哈希 + bundle；编排者独立重算 **985/985 全对** |
| 一次性构建 | **2739.0 s lean + 210.2 s clang + 49.5 s link ≈ 50 min**；峰值 **24.52 GB**（PentData）；per-module dylib 150.5 MB；聚合 bundle **99,679,600 B** |
| 加载 | 983 个分开 `--load-dynlib` 实测 **504.70 s**（dyld flat namespace）；改单个 bundle，冷加载 wall +~3 s |
| Quad 复验 | K051 2.03→0.65 s（3.12×）；K068 **106.43→7.67 s（13.88× / 14.37× user）**；K071 **1311.38→92.47 s（14.18× / 14.22× user）**；编排者 user 14.2×/14.9× |
| Pent/K100 | `PentData` `-c` **1097.59 s / 24.52 GB / 23.74 MB dylib**；`PentTop` **846.15 s / 21.05 GB / 18.60 MB**；K100 **99.46→9.27 s（10.73× / 13.12× user）**；编排者 9.41/7.20 s（13.6× user） |
| 信任 | 四个 shard 的 base/prod `#print axioms` + 完整陈述逐字节相同；哈希 `a6a1ebeb84ff6a2b`/`c9122927f44dcfea`/`b24391d051620466`/`92b9c8df7837183b` 对 `trust-base.tsv` 548/571/575/389；585 不变 |

- **Guard 越线（已披露）**：`PentData` 峰值 24.52 GB（=22.84 GiB）超过 24 GB 硬闸，
  pressure 构建中到 2 后回落，rc=0。按硬闸口径这是**功能 PASS / guard 不满足**；
  Pent 量产必须专用窗口或降内存，Hex 须先做 `HexTop` RSS 探针。
- 未量产：只测 K051/K068/K071/K100 四个 shard；Pent 其它 197 件、Hex 家族未跑。
- 复现入口：快照 `precompile-prod-quad-w1/`（`DELIVERY.md` / `REPORT.md` /
  `PROD_MANIFEST.tsv` / `prod/` / `evidence/` / `ORCH_VERIFY.md`）；bundle + 关键数据
  dylib 已入快照，984 个 per-module dylib 未全入（三哈希在 manifest，可按
  `prod/build_prod.sh` 重建）。

**全量三族（Phase D，2026-11-23；编排者独立复核）**：

| 族 | 件数 | prod 总 wall | 基线 | 聚合加速 |
|---|---:|---:|---|---|
| Quad | 92 | 1,893.8 s（0.53 h） | 38 件 7,893.0 s | **15.963×** |
| Pent | 198 | 17,308.0 s（4.81 h） | 154 件 109,063.2 s | **13.760×** |
| Hex | 290 | **6,659.4 s（1.85 h）** | 无同岛基线 | 不宣称 |
| **合计** | **580** | **25,861.2 s（7.184 h）** | **192 件 116,956.2 s（32.488 h）** | **13.889×** |

- 580/580 RC=0；逐件 median **12.815×**、p90 14.320×、min 4.030×、max 19.980×。
- `HexTop` `lean -c` **1042.99 s / 23.66 GB**；bundle 重建 **120,357,712 B（985 成员）**；
  K068 冒烟冷 13.70 s / 温 7.73 s；最高采样 pressure **1**。
- 580/580 `#print axioms` 审计 MATCH（哈希对 `trust-base.tsv` 580 行）；编排者独立复跑
  K068（8.35 s，`c9122927f44dcfea`）与 HexR/K092（0.79 s，`64eb61add8ec5fdd`）均 MATCH。
- **ERRATA**：旧 `[EST] HexR 1,095 roots ≈ 730 h / 全基座 770 h` **作废**（把
  HexR/K005 的 5-root shard 实测 2,389.82 s 当成每 root ×1,095，至少 5× 分母错误，
  且未计 precompile）。Hex 290 件实测 prod **1.85 h**；**Hex 无同岛基线，正式加速比
  UNRESOLVED**；HexR2 5 件 1,743.2 s（占 Hex 26%，max 899.78 s）重跑需专用窗口。
- **主池接入（2026-11-23 `precompile-integration-w1`）**：300 个缺失 shard + HexTop
  **300/300 可安装**（0 依赖 blocker）；**已安装 301/301 到主仓 `.lake`**（SHA/字节后验
  一致，回滚=删 `install301.tsv` 301 路径）；安装后主池 **580/580 审计 MATCH**
  （2.14 s / 1.68 GB）；根面 replay **仍 BLOCKED**（首缺 `Kepler.Graphs`），安装后仍缺
  1,028/1,031 非 shard（Text/TameSpine/Graphs/Interval），需常规定向编译。

**机制依据。** 当前 `native_decide` 在 Lean 4.32 的 `Lean/Meta/Native.lean:31-67`
固定走 `addAndCompile` → `evalConst` → 检查 `Bool = true` → 生成 native 公理；
本仓重片 profile 约 99.9% 为 IR `interpretation`，且 `LEAN_CC` 零调用。Lake 的
`precompileModules`（本 toolchain `lake/README.md:196-207`、`Lake/Config/LeanLibConfig.lean:75-82`）
则会把模块编成本机共享库，并在 import 时加载，官方用途就是加速求值/metaprogram。
这是目前唯一与实测瓶颈直接对应的执行模式候选。

**后续（三族 580 件已全量跑通；以下需用户另批）：**

1. **接入正式构建/验收**：把生产 bundle + 三哈希 manifest 接入未来 585/589 的全量
   replay 流程；需决定安装/分发方式（bundle 与 toolchain 绑定、CI 复现、主仓 `.lake`
   的安装边界）。不得全仓 11,241 模块一次开启。
2. **Hex 基线**：Hex 290 件零同岛基线；若需正式加速比，补测代表件或全族 base（成本高），
   否则只保留 prod 时间。HexR2 5 件重跑需专用窗口。
3. **Pent/Hex 专用窗口**：`PentR3/K000+K001` 合计 4,766.6 s；HexR2 5 件 1,743.2 s；
   重跑建议独占、无其它 lean。**止损**：单进程 >25 GB 或 pressure ≥3 停止。
4. 比较 CPU/wall/RSS/olean/native-lib 体积，并逐条核对布尔结果、定理陈述、585 公理
   名字/数量/类别。禁止新增 `extern`/`implemented_by`/公理；native 与 olean 必须同
   源同哈希，不能混用 stale 产物。
5. 采用前需把构建方式写入 manifest 并确认仍属现有 `native_decide` 信任类别；否则
   不采用。外部编译求值程序只能用于导航，不能凭其输出直接生成验收证明。

**与其它杠杆的关系：**若本机执行有数量级收益，优先于 C1+C3；若只有小幅收益，先做
C1+C3 的同语义 DEF-FIX。`-j` 不解决单线程 IR 枚举主循环，`decide +kernel` 也不是
免费替代品（既有全基座内核重放已判不可行）。
**适用范围（2026-11-27 实测补充）**：`precompileModules` 加速的是 **native 求值**
（`native_decide` 分片，4.32 的 13.889×）；**`decide +kernel` 的 Top\*Shard 106 件
不吃 dylib**（2026-11-27 census 实测整族 **≈1–2 h**，已非成本瓶颈），两者不要混算。

## 3.3 2026-11-26 增补实验台账

| 实验 | 日期 / 来源 | 结果 | 判词 |
|---|---|---|---|
| **W1DC L1 形态替换** | `fe1ec17f`；`wt1-bulk-*` → L1 | 39,028 s → **13,445.5 s CPU（−65%）**；18.28× → **6.30× HOL**；55–67 s/箱、olean ~3.6 MB（−44%）、行数 −48%；221/221 八条公理标准三 | **成功 / 已落库**（用户明批 B） |
| **TskXLLIPLS route a M1** | `tsk-certunit-m1-w1`，2026-11-26 | R 4096→64 **0 贡献**；N 半化 −7.4 s、N→16 −12.6 s；**地板 15.3 s**（19,666 节点 × 6 维 `dfB` 包络）；自证 checker 0 Int / 标准三，但 **17.8 s / 7.64 GiB** | **(b) FAIL ⇒ `BUDGET_EXHAUSTED`**；量产 6,612×15.3 s = 28.1 h = **4.5× HOL，NO-GO**；非数学 NO-GO |
| **Planarity 拆分** | `3119ded7`，2026-11-26 | 4.36 在 5M heartbeats 下由超限 → **RC=0 / 43.69 s**；4.32 34.23 s | **成功 / 已落库** |
| 每模块 `-j2` | 2026-11-21 基线 | 3 并发重件总 CPU −31%（999→688 s），wall +12%；单件 CertD CPU −55% | **建议采用（批量/CI）**；未全局应用 |
| import kit（精确 import） | 2026-11-21 基线 | 3.63→0.99 s（−73%），RSS 5.62→1.41 GB（−75%）；toy 仅三 tactic | **仅试点**；全仓需逐模块验证 |
| `precompileModules` + `--load-dynlib` | 2026-11-22/23 | 三族 **580/580 PASS / 7.184 h**；192 件基线 13.889×；`PentData` 峰值 24.52 GB 越线 | **功能 PASS，未接入正式构建**；需用户批 |
| **`precompileModules` 4.36 pilot** | `lean436-precompile-w1`，2026-11-27 | Hex 非 R `Hex.K008` 606.00→**46.74 s**（**12.97×**）；HexR.K001 2,216.29→**170.97 s**（**12.96×**）；bundle 1,041 模块 **53.7 min / 19.40 GB**；两件 axioms = 标准三 + 各自 1 条同名 native ax、陈述哈希 MATCH `trust-base.tsv`、**olean base/dyn/census 三者逐字节同**；全量 575 投影 **19.1–23.3 h**（10.1–15.2×，含一次性构建） | **GO**（≥10×）；Pent/Quad 未跑、`QuadR.K000` 尾部 **35.2 h**（CONDITIONAL 带，仍 <58 h）；**全量 575 已批（2026-11-27），Phase 2A/2B 执行中** |
| `native_decide` 提速 | 2026-11-21 基线 | fib30 0.60 s vs `decide` 0.17 s（3.5× 慢）+ 1 条公理 | **负结果，不做** |
| 跳过 `-c` / `-i` | 2026-11-21 基线 | `-c` ≈ 0（1.23 vs 1.21 s）；`-i` +7% | **不做**（只省磁盘：C 16.6 GB + setup 25.4 GB） |
| `-M` 当加速旋钮 | 2026-11-21 基线 | 低于峰值直接 `memory_exception` | **只当护栏** |
| 无界 `lake build` / 高并发 | 2026-11-13 / 11-26 事故 | 默认 `-j12` 扇出；Assembly 事故 12 路 / 28.5 GB / swap 6.8 GB | **永久禁止**（AGENTS §4） |

## 3.4 2026-11-27 Track A/B：TskXLLIPLS 成本结构结论

来源：`~/c17_backup/lane_snapshots/tsk-opt-a-w1/`、`~/c17_backup/lane_snapshots/tsk-opt-b-w1/`；
pq 续1606/续1609。A/B 均零 Lean，所有成本为 [模型]（A 用 31 µs/原语标定，B 沿用）。

| 项 | 结果 | 判定 |
|---|---|---|
| 成本模型订正 | kernel 只走 live `ite` 分支：`ΣN_visited = 93·N`（原 AST 121,344 项，非字面 189,184）；`cost_leaf ≈ 15.0 s + 1.055e-4·ΣN_visited`；复现 29.16 s/叶 | [实测] |
| 最小 N（全族 6,612 叶） | **N_min=16：6,609 叶；N_min=32：3 叶**（kBox2933/2078/1607）；N≤8 全族不可行 | [实测] |
| N 杠杆 | 51.1 → **27.8 CPU·h**（decide-only）；+import 57.3 → 34.1 h = **4.41× / 5.40× HOL**；安全统一 N=32 ⇒ 28.1 / 34.4 h（4.46× / 5.44×） | [模型] |
| 精度 | 粒度 −80→−24（56 bit）40/40 样本仍正，但 D5 **0%**、D2 仅 −3.3% | 不是杠杆 |
| 叶树 | 自底向上合并 −11.8%（6,612→5,833）；独立 B&B 在 7/12/19/47 叶四档精确复现落地叶数 ⇒ 落地树已最优；更细分裂不划算（15 s/叶 vs ≤12.8 s 省） | [实测] |
| HOL 2-piece | HOL 只暴露 2 单元（y1 95.01% 切，y1=2.8195635、x=7.94994；文档 7.951434357936 为 x-space 假设，**ERRATA**）；两半 lb −7.9e4/−3.2e11 ⇒ 无捷径 | [实测] |
| 三杠杆叠加 | 最好 **3.89× / 4.77×**（24.6/30.1 h）；≤2× 需地板 ≤3.16 s（−79%），≤1.2× 需 ≤0.41 s | [模型] |
| **Design P（Track B 投影）** | 点 Taylor（`f(y)`、`∇f(y)`）+ 单元级 Hessian 曲率表（= HOL `m_taylor_error` 结构）；**84.7k 原语/叶 → 2.62 s/叶（5.7×）[模型]**；D5 **11.6 h（1.84×）**，叶树合并后 **10.3 h（1.63×）**，decide-only 0.76–0.86× | **WITHIN-BAND**（模型） |
| **Design P 一盒原型（2026-11-27）** | `PointTM.lean` **558 行**；`checkPosPt_sound` 标准三、叶 `pt_check`=[propext,Quot.sound]、RSS 6.194 GiB、K **150.6–301.8**（≤550）、**34/34** 非 straddle lb>0、12/12（11 直接 + 1 straddle 回落 TM）；**wall 8.61–8.82 s > 3.4 s**；根因 = Fixed-Grid 未实现（**75.6 vs 31 µs/op**；op 数 88,753 vs 84,766 = 1.047×）；S1/S2 仍为命名 Prop 假设（570–720 + 400–700 行未证）；straddle 15% 分裂无效、回落 TM 15.49 s ⇒ 摊销 **9.6 s/叶** | **WALL-FAIL / CONDITIONAL** |
| **M2b Fixed-Grid v2（2026-11-27）** | `PointTMFG.lean` **787 行 / ~60 声明**；RC=0 / 0 error / 零 `axiom`/`sorry`/`native_decide`/extern；`checkPosPt_sound` **标准三**。Fixed-Grid 原语 **184,838** vs M2 88,753 = **2.08×**（`ediv`+`abs` 各 43,960，全部来自半径路径）；**单叶 wall 未取得**——探针 `decide` 不闭合、`dualOnly` 核内早退 `none`（`sorryAx`；镜像 `fy=2.73` vs M2 `2.45e-2`、`curv` 一致 ⇒ 值链某节点分叉；`ofInterval`/`fgCeilD` 未排除）。按实测单价（Int.add 6 / Int.ediv 48 / Int.mul+ediv 98 µs）投影 **≈4.5–5 s/叶**（`[EST]`，非判词）：DESIGN §3.4 的「× = 1 mul + 1 shift」只在不要半径时成立，而不要半径不 sound | **UNRESOLVED / WALL-NOT-MEASURED**（非 PASS 非 WALL-FAIL；投影 >3.4 s） |
| 死候选 | 两级自然区间 0/12 闭合（相消 27×）；惰性/零跳过 1.65×；粗导数界 0/8（19× 膨胀）；均值形式紧度持平 | 不做 |
| 关键事实 | 现 `err` **过证 300×**（真二阶余项中位 2e-3·fB0 vs err 0.72·fB0）；换曲率后 lb 4.6e-3→1.6–2.8e-2（12/12 叶）；A 的 `ite_both=0` 是计数器假象，活路径 6/40 叶有未定 guard | **ERRATA 已记** |
| 残余风险 | 严格二阶 AD 的 K 未实现；实测幅度型 K=40–70 vs 容差 550（余量 8–13×）；15% guard-straddle 叶需梯子；Lean wall 未测 | UNRESOLVED |
| 下一步 | **M2b 已回（2026-11-27）= `UNRESOLVED / WALL-NOT-MEASURED`**：先修值链分叉再测、接受 ~4.5–5 s `[EST]` 重评、N=32 fallback、止损——**四选一等用户确认，车道内不动**；C 不做 | 待裁决 |

## 4. 不要做

- 把 6,612 个 TskXLLIPLS 叶当“冗余”随意合并/减少：叶数是 6 维 B&B 的输出，
  HOL 自己 7,763 个证书单元；少叶需要更强包络或新数学（§8），不是改证书格式。
- 无界 `lake build` / 全树构建（Lake 5.0 全核扇出；AGENTS §4 永久禁止）。
- 用 `native_decide` 提速（更慢 + 新增公理）；新增 585 之外的任何 `native_decide`。
- 静默引入 `@[implemented_by]` / `@[extern]`（信任面变更，且 codegen 不在 olean 路径）。
- `-M` 当加速旋钮（低于峰值直接 `memory_exception`）；靠 `touch` 触发重编（内容哈希）；
  用 `cmd | head` 的退出码判成功（崩溃可能回 0）。
- RAM disk / ccache（olean 构建不调 clang，无对象可缓存；热态 APFS 读 5.4 GB 约 1.7 s sys）。

## 5. 未闭合（UNRESOLVED）

- **TskXLLIPLS 优化（2026-11-27 更新）**：Track A 已把 M1 的“只剩惰性”扩展成完整结论——
  N/叶树/精度都动不了 15.0 s 地板，N 杠杆 4.41–4.46×，叶树 −11.8%，精度 0%；三杠杆叠加
  最好 3.89×。Track B 的 **Design P** [模型] 2.62 s/叶、D5 1.63–1.84×；**一盒原型已测
  （2026-11-27）**：wall **8.61–8.82 s（WALL-FAIL）**，根因 Fixed-Grid 未实现
  （75.6 vs 31 µs/op；op 数仅 1.047×），其余硬指标全 PASS（标准三、K 150.6–301.8、
  34/34 lb>0、12/12 含 straddle 回落）；S1/S2 仍为命名 Prop 假设。**M2b Fixed-Grid v2
  已回（2026-11-27）：`UNRESOLVED / WALL-NOT-MEASURED`，非 PASS 非 WALL-FAIL**——
  `PointTMFG.lean` 787 行、RC=0/0 error、`checkPosPt_sound` 标准三、零禁用构造；但探针
  `decide` 不闭合（`dualOnly` 核内早退 `none`；镜像 `fy=2.73` vs M2 `2.45e-2`、`curv`
  一致 ⇒ 值链某节点分叉，`ofInterval`/`fgCeilD` 未排除），单叶 wall 未取得。Fixed-Grid
  原语 **184,838（2.08×）**，`ediv`+`abs` 各 43,960 全来自半径路径；按实测单价投影
  **≈4.5–5 s/叶 `[EST]`**（`× = 1 mul + 1 shift` 只在不要半径时成立，而不要半径不 sound）。
  附带两条负结果：① `atan1K` 点值检测必须下沉到格点层（`c=2^S ∧ r=0`），Dyadic 端点
  `⟨2^164,−164⟩` 永不语法等于 `(1,0)`，落 `arctanI` 在 x=1/N=16 只有 2% 精度；
  ② `chopCeilTo` 不能当取格点用（`e₀ ≤ d.e` 时原样返回）。**下一步四选一（修值链再测 /
  接受 ~4.5–5 s 重评 / N=32 fallback / 止损）等用户确认；未确认前不动。**
  **B 的 UNRESOLVED**：① 严格二阶 AD 的膨胀因子 K（实测 40–70 vs 容差 550）未实现；
  ② 15% guard-straddle 叶的梯子成本未比较；③ 新紧度下最优叶数未重跑 B&B（若减半 → ~4 h）；
  ④ D4 最小 olean 未测；⑤ `√`/`atan` 二阶规则在驻点/`f→0` 的分支未实现。
- **N=32 / 模块合并**：N=32（DEF-FIX，4.46×/5.44×）作 Design P 失败后的 fallback；
  模块合并（C，`[EST]` −6 h import）按用户 2026-11-27 裁决不做。
- **4.36 census 的抽样边界**：叶族 83/6,412（`HOMOGENEOUS-SAMPLED`）；T\* 3/199
  （T1/T63/T150，叶并集 102）；**196 个 SAMPLED-OUT T\* 的叶并集 = 6,310**，
  **199 个 = 6,412 = 全部 PLeaf**（deps.tsv 精确去重）。根链
  `TskXLLIPLS → PackIneqTskXLLIPLSClose → Assembly → Final` 在 census 中
  **`DEFERRED`（非 BLOCKED/OOM/失败）**；`0 BLOCKED` 只覆盖已编模块。
  全量 6,412 叶重放（≈51.6 h 串行 / 10.3 GB 每叶）属 acceptance，见 §1.1。
- **CertShards 的抽样边界（2026-11-27）**：非 R Hex/Pent 已 9 件全绿；**R 变体 37–75 min/件**
  （HexR.K001 2,216 s、QuadR.K000 4,478 s、PentR.K001 >70 min）⇒ 抽样降为 **R 族各 1 件**
  （HexR/QuadR/PentR/PentR2/PentR3/HexR2，样本 ≥15–16），其余 `SAMPLED-OUT`；
  任一 R 件失败该 R 族整体回队列。抽样件必须核 `#print axioms` 与 585 manifest 同形
  （实测 = 标准三 + 1 条同名 manifest ax，无 `Lean.ofReduceBool`）。
  **全量 575 实测外推 237–465 h（非 R 14.6 h；R 360 件 222–450 h）⇒ `BUDGET_EXHAUSTED`**；
  验收替代方案 A（4.36 precompile 重建，4.32 实测 13.889×）或 B（按族抽样 + 585 逐名审计）
  待用户批，车道内不自批。
- **Top\*Shard 抽样撤销（2026-11-27，census 实测后改全编）**：106 件 `decide +kernel`
  （TopReplayHex 55 / TopReplayPent 31 / TopBoundsHex 14 / TopReplayQuad 6），源码
  0.8–0.9 KB、`gen_top_shards.py` 单模板。9 件抽样 **9/9 OK**，实测 **3.2–33.2 s**
  （TopBoundsHex S001 3.90 / S013 3.18；TopReplayHex S000 33.20 / S027 21.07 / S054 8.71；
  TopReplayPent S000 17.17 / S030 2.86；TopReplayQuad S000 7.23 / S005 9.64），唯
  `TopBoundsHexShardS000` **60 min cap 未结束（`BUDGET_CAP`）**。公理形状：`TopBounds*` =
  `[propext]`、`TopReplay*` = 标准三，**均无 native_decide 公理**。因此 `skip.tsv` 已撤掉
  97 行 `SAMPLED-OUT`，driver 恢复全编 106 件，整族 **≈1–2 h**。**ERRATA**：续1622 的
  “31 min 未结束 ⇒ 50–60 h” 是把单件异常外推整族，作废。**census 已全编完成**：
  104 OK + `TopBoundsHexShardS000` `BUDGET_CAP`（>60 min）+ `TopReplayPentShardS013`
  `BUDGET_CAP`（RSS 25,769,902,080 B = 24.0 GiB，顶 `-M 24576` 内核内存上限；error
  1「(kernel) excessive memory consumption」；同族 S010–S026 除 S013 全 OK、S024 最大
  19.6 GB；同源 4.32 olean 存在 ⇒ 预算中止，非 4.36 代码/证明错误）。S013 列入
  acceptance 未覆盖项：**单槽 `-M 0` 重跑并实测峰值**；当前 24 GB 总 RSS 闸不放宽
  （>24 GiB 独占窗口需用户明批）。**precompile 不覆盖**该族，但它已不是 acceptance
  成本瓶颈；验收若做 CertShards precompile，Top\* 另付 ≈1–2 h。
- **`-j2` 全局默认 / import kit 全仓**：均未获用户批准；前者只建议用于批量/CI，
  后者需逐模块验证 import 面。
- `precompileModules`：4.32 三族 580/580 跑通（7.184 h；192 件基线 13.889×）；
  **4.36 pilot 2026-11-27 = GO**——`Hex.K008` **12.97×**、`HexR.K001` **12.96×**
  （同岛配对 13.75×/13.86×），bundle 1,041 模块 **53.7 min / 峰值 19.40 GB**（<24 GB 闸；
  4.32 曾 24.52 GB 越线），两件 axioms/陈述哈希/**olean 逐字节**三项全同；全量 575 投影
  **19.1–23.3 h**。**未闭合**：Pent/Quad 族未在本 bundle 下跑（需补
  `CertData.PentTop`/`QuadTop` 两模块，+~20 min；本次 census 占 23.3 GB 槽未取）；
  `QuadR.K000` 尾部按 4,478 s 起点估 **35.2 h**（CONDITIONAL 带，仍 <58 h 最低线）；
  生产 bundle 未接入正式构建；**全量 575 已批（2026-11-27），Phase 2A/2B 执行中**。
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

## 8. 为什么是 6,612 个叶单元（而不是几个）

> 结论：**叶数是 6 维 B&B 算法的输出，不是冗余；HOL 原版自己也有 7,763 个证书单元
> （D1 = 0.852×），并没有用“几个叶”。** 真正的差距在验证引擎（内核 `decide` 29 s/单元
> vs HOL native C++ 2.928 s/单元），不在叶的数量。

1. **对象是 6 维局部不等式**：`0 < gamma4fgcy y1..y6 = volY − vol4f`，盒
   `[2hplus,√8]×[2,2.01]²×[2hplus,2.8]×[2,2.01]²`。函数由 **143 个 `.trans` 级数、
   79 个 `√`、165 个 `/`、60 个 `ite`、6,469 个 `×`** 组成（**19,666 个 AST 节点**）；
   atan 来自 `dihXf` 的二面角、`solY` 的球面超额与 `π = 4·atan 1` 展开。
2. **区间/Taylor 包络有依赖问题**：在大盒上直接算下界，变量相关会让包络变松、下界变负；
   B&B 把盒不断细分，直到每个终端盒的 Taylor 下界 > 0。**6,612 叶 = 6,612 个终端盒**，
   是算法输出，不是设计者主动拆这么多。
3. **“少叶”不是免费的**：盒越大，固定 AST 的 6 维包络越松；要么下界变负（失败），
   要么提高 Taylor 阶数/精度（更贵）。M1 实测：本盒 N=8 已负，N=16 最小可过；
   **15.3 s 地板是 per-node 6 维 `dfB` 包络，不是 N、也不是证书大小**。要把叶数降一个
   量级，等价于换更强的包络（Bernstein/affine）或换数学路线（单调/凸/降维），
   不是改证书格式能解决的。
4. **HOL 并没有更少**：`ineq.hl:304` 的 2 个子域定理共 **7,763 个证书单元**；我方 6,612
   叶单元（0.852×）。HOL 也是“分区 + 区间/Taylor 验证器”，只是每单元 2.928 s（native
   C++），我方 29 s（内核 `decide`）。差距 10× 在引擎，不在叶数。
5. **HOL 的三件不能直接抄**：
   - C++ 验证器 + 23,242 md5 白名单 + 1 条 `deserialization` 公理：AGENTS §2 禁止新增公理；
   - LCF 不落 proof object：DTT 必须落，D4 1.7 GB 是结构性差异（不是浪费）；
   - `pp/eps/max_depth/split` 是 HOL 自己的参数；2 段切点与分区树设计我们已对齐。
6. **能不能“几个叶”**：只有换数学路线才可能——证明 `gamma4fgcy` 对每个变量单调/凸、
   把 6 维降成边界/1 维、或用 Bernstein/affine 包络。HOL 没做这条；这是研究问题，
   需先做零 Lean 的设计研究 + 新 PARITY CARD，不能靠改证书格式或调 N/R 解决。
7. **6,612 个“模块”是工程粒度**：拆成 6,612 个模块是为了并行、增量编译与 24 GB 内存
   隔离（单叶 10.3 GB）。把 ~29 叶并成一个模块可省 import 地板，`[EST]`
   `6,612/29 × 28 × 3.4 s ≈ 6.0 h`，但内核工作不变，且单模块 RSS/增量粒度变差；
   可做 pilot，不是数学问题。
