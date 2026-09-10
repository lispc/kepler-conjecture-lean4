# 交接文档（Handoff）— 2026-09-10

> 面向接手者（人类或 agent）。本文件描述项目现状、验证纪律、环境细节、
> 待办与优先级。一页进度看板见 `STATUS.md`（每日刷新），长期设计决策见
> `DECISIONS.md`，阶段计划见 `PLAN.md`，模块对照见 `docs/module-map.md`。

## 0. 一句话现状

main @ 见 `git log -1 main`（全绿，唯一 sorry = `Statement.lean:111`
sanctioned 占位）。**Phase 2/3 已闭合；Phase 4 求解层 160/176（91%），
内核闭合（G4）未开工；Phase 5 planarity.hl 正由全自动流水线推进**
（`lean/scripts/auto_pipeline.sh`，deepseek-v4-flash 全权：骨架设计→
证明填空→机械闸→自动合并 main；Kimi 降为每 4h 汇报+抽查）。

## 1. 项目目标（不变）

Lean 4 + Mathlib（toolchain `leanprover/lean4:v4.32.2`）形式化开普勒猜想：

```
开普勒猜想（密度 ≤ π/√18）
  └── Phase 5 文字证明：堆积 → fan → hypermap → 归约为"tame 图得分 < 12"
        ├── Phase 2：tame 平面图分类（19,715 张）✅
        ├── Phase 3：每图 LP 上界（43,078 个终端 LP）✅
        └── Phase 4：176 条非线性不等式（支撑 LP 松弛与局部估计）🟡 91%
```

## 2. 各 Phase 状态

### Phase 2 — 图枚举 ✅ 闭合

- 19,715 张 tame 图全量枚举 + 内核验证（585 个 CertShards 分片）；
  公理 = 标准三公理 + 601 个限定范围 native_decide，零 sorryAx。
- **绝对不要** `rm -rf lean/.lake`：分片全量重建需 ~7 天。

### Phase 3 — LP ✅ 闭合（2026-09-07）

- 43,078/43,078 终端 LP 内核验证通过（SoPlex 精确模式 + 51 例
  glpsol --exact 对偶通道兜底）。账本 `~/lprun-logs/results.jsonl`。
- 链路细节与 SoPlex 用法（`-X/-Y` 有理输出才可信）见 `pipeline/lp/README.md`。

### Phase 4 — 非线性不等式 🟡 求解层 91% / 内核闭合 0%

- 流水线：ineq.hl 181 记录 → AST 176 → case JSON（y 空间 176 +
  prep 空间 745）→ bb_arb（C/FLINT 分支定界，二进制 /tmp/bb_arb_verify，
  编译命令在 `pipeline/interval/README.md`）。
- **2026-09-09 家族级对账**：176 条 = 68 y 空间闭合 + 92 prep 家族
  闭合（prep = Flyspeck 官方 x=y² 归一化，745/745 全闭合）+
  **16 条真残余**（清单 `pipeline/interval/out/residue16.txt`：
  TSKAJXY 系 4、TEWNSCJ/PEMKWKU/TXQTPVC/IXPOTPA、QZECFIC wt0 ×2、
  GRKIBMP B V2 等）。
- 待办：16 条逐条定策略（GRKIBMP B V2 有真反例叶=尖锐边界组，需 ε 余量
  或弱编码）；然后 **G4：BBTree 证书 → Lean 内核闭合**（bb_arb 已能出
  cert JSON；Lean 侧需扩 IExpr abs 节点 / TKind ln / Cert 叶带 guard
  符号+disj 备选——规格 `pipeline/interval/arb-layer.md` §3/§4）。

### Phase 5 — 文字证明 🟡 全自动流水线推进中

- 已收官：hypermap.hl 13,575 行 100%、fan.hl 系列 ~7,800 行 100%、
  topology.hl 4,718 行 100%。
- **planarity.hl（15,463 行）**：自动化批次推进，每批 10 定理。
  覆盖行数见 main 最新 commit 消息（"coverage :NNNNN"）。
  后续队列：planarity 剩余 → Conforming.hl 17,033 → polyhedron ~3,200 →
  packing/ ~28,000 → local/ ~30,000 → assembly。
- **全自动流水线**（`lean/scripts/auto_pipeline.sh`，2026-09-10 上线）：
  1. 从 `lean/scripts/auto_pipeline_state.txt` 读当前位置（起始行+批次号）；
  2. deepseek 设计骨架（陈述冻结，docstring 嵌 HOL 原文+证法+候选引理）；
  3. `auto_loop.sh` 逐定理派 deepseek 填空，**机械闸五道**（单文件 diff /
     签名冻结=删除行只能是 sorry / 禁词扫描 / lake build 绿 / 公理白名单），
     过闸自动 commit；单定理 3 次失败跳过、连续 3 跳闸熔断；
  4. 批次审计（全量 build + 冻结核验 + 全定理公理）→ ff main + push；
  5. 推进状态文件，下一批。FAIL-STOP 即停等人类。
- **Kimi 的残余职责**：每 4h 汇报 + STATUS.md + 陈述保真抽查 +
  处理 FAIL-STOP/NEEDS-HUMAN。
- 工人模板与历史教训：`docs/phase5-worker-template.md`。

## 3. 验证纪律（红线）

1. **main 零 sorry**（唯一例外 `Statement.lean:111`）；wip 分支允许骨架
   sorry，但 wip 只有在"所有被 import 的文件均无 sorry"时才合入 main。
2. `native_decide` 只允许 `Kepler/Graphs.Cert*`（601 个限定信任公理）。
3. 内核无法归约 Rat 算术——checker 检查层用 Int/dyadic，语义层 cast 桥接。
4. 合 main 前：`lake build Kepler` 全绿 + 签名冻结核验 + 公理白名单。
5. 不信任任何生成器/求解器，信任基 = Lean 内核 + 项目内 checker。

## 4. 环境备忘（本机）

- 128 核 / 503G RAM / 磁盘 98G（紧）。tmpfs 在 `/dev/shm`（252G，
  重启即失）；`/tmp` 不是 tmpfs。
- Lean 命令前 `export PATH="$HOME/.elan/bin:$PATH"`；项目在 `lean/`。
- 参考库浅克隆在 `/dev/shm/kepler-ref/`，symlink 回 `reference/`；
  重启后重克隆约半分钟（命令见 git 历史或 `reference/LOCK.md`）。
  **关键参考已入库**：`lean/scripts/planarity.hl`。
- LLM 通道（`~/.local/share/opencode/auth.json`）：
  `deepseek/deepseek-v4-flash`（付费，现任主力，~1-2 分钟/定理），
  `opencode/big-pickle`（免费，前主力），
  `zhipuai-coding-plan/glm-5.3`（订阅，设计/兜底），`glm-5.3-flash`（备胎）。
  调用：`cd lean && timeout 5400 opencode run -m <model> "<prompt>"`。
- git 身份 Zhang Zhuo <mycinbrin@gmail.com>（仓库级已设）。
- 双 3090 GPU 是别人生产容器，**绝不碰**。

## 5. 当前运行中的东西

- `auto_pipeline.sh`（若已启动）：日志 `/tmp/auto_pipeline.log`，
  状态 `lean/scripts/auto_pipeline_state.txt`，批次循环日志
  `/tmp/auto_loop.log`，闸日志 `/tmp/auto_gate.log`。
- 巡检 cron（Kimi 会话内）：每 4h 汇报+抽查。

## 6. 待办队列（优先级序）

1. Phase 5 planarity 收官（流水线自动推进中）→ 之后 Conforming.hl 等，
   流水线可直接改 HL 变量复用。
2. Phase 4：16 条残余策略 + G4 内核闭合（见 §2 Phase 4）。
3. Phase 6：主定理装配 + 终验。
4. 零散：`Kepler.Text.fan80/fan81` 重复定义去重；`ineqdata3q1h.hl` 解析。

## 7. 已知坑（近期新增；历史坑见 git 历史与 worker 模板）

- **闸的三个已修 bug**（教训：GATE-FAIL 先怀疑闸）：git diff 路径要
  `--relative`；公理全名=命名空间.定理名（非模块名）；`#print axioms`
  长输出会折行，匹配前先 `tr '\n' ' '`，另有 "does not depend on any
  axioms" 合法情形。
- 改动正在运行的 bash 脚本会被 bash 按字节偏移续读——先停再改。
- `pkill -f 'opencode run'` 会自匹配杀自己——用 `pkill -f '[o]pencode run'`。
- nohup 包装壳的 pid ≠ 真循环 pid，用 `pgrep -f 'auto_l[o]op.sh'` 取。
- 验收构建必须自然退出：掐死时 error 未 flush，grep 0 是假绿。
- 整条命令链末尾加 `&` 会把整条链后台化，前台输出全丢——分两条命令。
- 工人（opencode）读不了仓库外路径（external_directory auto-reject
  会杀会话）：HOL 原文一律粘贴进 prompt 或放仓库内。
- 标量-标量乘在 ascription 里写 `*` 不写 `•`（isDefEq 死循环）。

## 8. 快速自检（接手后第一件事）

```sh
cd /home/scroll/repos/kepler-conjecture-lean4
export PATH="$HOME/.elan/bin:$PATH"
git log --oneline -3 main
make check                      # build + 公理审计，应全绿
tail -20 /tmp/auto_pipeline.log # 流水线状态（若在跑）
```
