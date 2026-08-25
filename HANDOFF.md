# 交接文档（Handoff）— 2026-08-25

> 面向接手者。本文件描述项目现状、验证纪律、环境细节、待办与优先级。
> 长期设计决策见 `DECISIONS.md`，阶段计划见 `PLAN.md`，模块对照见
> `docs/module-map.md`，架构见 `docs/architecture.md`。

## 0. 一句话现状

仓库 `github.com:lispc/kepler-conjecture-lean4`（main @ `966496b`）全绿：
`make check`（build + 公理审计）通过，唯一 sorry 是 `Statement.lean:111`
的 sanctioned Phase-1 占位。Phase 2 已闭合；Phase 3 试点闭合并完成
分片提速；Phase 4 工具链与 checker 核心就绪；Phase 5 文字证明移植至
hypermap.hl 的 78%。

## 1. 项目目标（不变）

在 Lean 4 + Mathlib（toolchain `leanprover/lean4:v4.32.2`）中形式化
开普勒猜想。证明结构（Hales《Dense Sphere Packings》蓝图）：

```
开普勒猜想（密度 ≤ π/√18）
  └── Phase 5 文字证明：堆积 → fan → hypermap → 归约为"tame 图得分 < 12"
        ├── Phase 2：tame 平面图分类（19715 张）
        ├── Phase 3：每图 LP 上界（43,078 个终端 LP）
        └── Phase 4：~993 个非线性不等式（支撑 LP 松弛与局部估计）
```

四条线在数学上都是必须的；可选的只有工程加速与交叉保险（详见
PLAN.md 与各 README）。

## 2. 各 Phase 状态

### Phase 2 — 图枚举（✅ 闭合，已在新机器全量重建验证）

- 9287 jobs 全过；`tame_classification` 公理审计 = 标准三公理 + 601 个
  **限定范围**的 native_decide 信任公理（tri 9/quad 16/quadr 80/pent 146/
  pentr 16/pentr2 30/pentr3 10/hex 70/hexr 219/hexr2 5），零 sorryAx。
- 最重分片 `PentR3/K000` 实测 157.7h（j=0=204,531,909 / j=1=132,292,386
  pops，已记入 `docs/architecture.md`）。
- **绝对不要** `rm -rf lean/.lake` 或重建 `Kepler/Graphs/CertShards*`：
  585 个 native_decide 分片全量重建需 ~7 天。
- 公理审计：`lean/scripts/AxiomAudit.lean`（`make check` 覆盖）。

### Phase 3 — LP（🟡 试点闭合 + 分片落地；全量化待转置表示）

- 链路：Flyspeck easy 证书 → `parse_lpcert.py` → `gen_data.py` →
  GLPK 5.0 展开 → `flatten_lp.py` → SoPlex 8.0.3 精确模式
  （`pipeline/tools/soplex-8.0.3/bin/soplex`，用法与 exact.set 见
  `pipeline/lp/README.md`；**`-X/-Y` 有理输出才可信，Objective 行是浮点**）
  → `socert.py` 生成 Lean 证书 → `Kepler/LP/Cert.lean` 稀疏整数对偶
  checker（`checkDual_sound` 弱对偶）。
- 真实图 204880136538（915 变量 × 3882 行 × 8056 非零）端到端闭合：
  `Kepler/LP/Pilot204880136538/`（Data + 915 列分片 + Assembly），
  `bound_lt`（目标 < 12）公理仅标准三公理。
- **分片实测**（commit `b16300b`）：单块 `decide` 25304s（7h）→
  逐列分片 96 并发端到端 1542s（26min，16.4×）。生成：
  `socert.py --shard-cols K --terminal-bound 12`；构建：
  `pipeline/lp/build_shards.py <Module> --procs 96`（单片失败可 `--only`
  重试）。
- **全量化瓶颈与下一步（高优先级）**：43,078 LP × ~7 core-h ≈ 34 core-年，
  分片不够。出路是 `Cert.lean` 头注释记录的**转置（列主序）证书表示**：
  对偶检查从 O(numVars×nnz) 降为 O(nnz)，目标 ~30s/LP（≈15 core-天
  全量）。需要：列主序版 `checkDual` + 一致性/组装 soundness 引理 +
  `socert.py` 输出列主序数据。
- formal_lp 侦察结论：19715 图 = 19700 easy + 15 hard；hard_7 单图
  9,080 个 LP；阈值语义 = 每图 scriptL > 12；注意 model2.mod 被 sed 删过
  `main: sum ln >= 12`（详见 `pipeline/lp/README.md` 与 docs/hard-cases.md）。

### Phase 4 — 非线性（🟡 工具链 + checker 核心）

- 工具链已验证：dReal 4.21.06.2（deb 解压）+ MPFR 4.2.2 + FLINT 3.3.1
  （内置 Arb），见 `pipeline/interval/README.md`。
- `Kepler/Interval/Basic.lean`（490 行）：dyadic（`m·2^e`）端点区间算术 +
  `IExpr` AST + `checkPos_sound`（盒上 f>0 雏形）。文件头 "Next steps"
  写了下一块接口建议。
- **下一步**：除法/√/超越函数层（Taylor 中点半径），分支定界证书格式
  （docs/architecture.md Phase 4 节待补）。

### Phase 5 — 文字证明（🟡 进行中，人力主线）

- 路线：Hypermap（ch4 库）→ Fan（ch5）→ LocalFan（ch7）→ Assembly（ch9）。
- `Kepler/Text/Hypermap.lean` 8776 行，覆盖
  `reference/flyspeck/text_formalization/hypermap/hypermap.hl` 至
  **10641/13575（78%）**。已过最难部分：Euler 主定理、组合 Jordan 曲线
  定理、loop/atom/正规环族、商 hypermap、Iso、face collections、
  XWCNBMA、lemmaSTKBEPH。每块头注有覆盖/跳过对照表。
- **下一块**：hypermap.hl 10643 起——dihedral hypermaps、restricted
  hypermap `is_restricted`（11174）与 tame 前置，至全书收尾（估计 2–3 块）。
- 移植惯例：对应 HOL 行号写头注；Mathlib 已有的跳过并注明；零 sorry、
  零 native_decide、零自引入 axiom；每块 `lake build Kepler` 全绿 +
  公理抽查后才提交。

## 3. 验证纪律（红线）

1. **零 sorry**（唯一例外 `Statement.lean:111` 的 Phase-1 占位）。
2. **`native_decide` 只允许在 `Kepler/Graphs.Cert*`**（Phase 2 的 601 个
   限定信任公理），其余一律内核 `decide`/term 证明。
3. **内核无法归约 Rat 算术**（extern 限制）——所有 checker 检查层用
   Int/dyadic，语义层 cast 桥接。LP 与 Interval 共用此设计。
4. 提交前：`lake build Kepler` 全绿 + grep 目标文件无 sorry/native_decide +
   关键定理 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`。
5. `make check` = build + 公理审计（含 `tame_classification`）。
6. 不信任任何生成器/求解器代码，信任基 = Lean 内核 + 项目内 checker。

## 4. 环境备忘（本机）

- 128 核 / 503G RAM / 磁盘 98G 剩 ~40G（**磁盘紧，大文件放 tmpfs**）。
- `/tmp` 不是 tmpfs；tmpfs 在 **`/dev/shm`（252G）**。
- Lean 命令前必须 `export PATH="$HOME/.elan/bin:$PATH"`；项目在 `lean/`。
- 参考库浅克隆在 `/dev/shm/kepler-ref/{flyspeck,kepler98}`（hash 与
  `reference/LOCK.md` 一致：flyspeck@1ce0353、kepler98@90350ab），以
  symlink 挂回 `reference/`。**重启即失**，重克隆约半分钟：
  ```sh
  mkdir -p /dev/shm/kepler-ref && cd /dev/shm/kepler-ref
  git clone --depth 1 https://github.com/flyspeck/flyspeck.git
  git clone --depth 1 https://github.com/lispc/kepler98.git  # 按 LOCK.md 核对 hash
  ln -sfn /dev/shm/kepler-ref/flyspeck reference/flyspeck
  ln -sfn /dev/shm/kepler-ref/kepler98 reference/kepler98
  ```
- PyPy（可选加速 pipeline Python，~4×）：
  `/dev/shm/pypy3.11-v7.3.20-linux64/bin/pypy3`（重启即失需重装）。
- **单核很慢**：native_decide 实测 ~360 pops/s（原机 4–11K/s）——
  估算 native_decide 任务时长时务必按本机标定。
- SoPlex：`pipeline/tools/soplex-8.0.3/bin/soplex`（已编译验证）。
- git 提交身份沿用原作者 Zhang Zhuo <mycinbrin@gmail.com>
  （仓库级 `git config` 已设）；push 到 origin main。
- 磁盘清理注意：LP 分片 olean 体积可观，`Pilot204880136538` 全套
  olean 约数 GB 级；空间紧张时可删（源文件在 git 里，可重建）。

## 5. 多 agent 工作模式（前接手者的工作方式，可参考）

- 每个 Phase 一个 coder 子代理，文件归属隔离（Hypermap 归 Phase 5
  agent，LP 归 Phase 3 agent，Interval 归 Phase 4 agent），主 agent 统一
  验证 + commit + push，**子代理不许 git commit**。
- 主 agent 提交时只 `git add` 对应 Phase 的文件，避免把其他 agent 的在途
  半成品带进 commit。
- 子代理结束后其后台 bash 进程**可能**被回收——长任务（如分片构建）
  要由主 agent 起自己的后台监控接管。
- quota（403 usage limit）会周期性断；断了等恢复后 resume agent 即可，
  上下文保留。

## 6. 待办队列（按建议优先级）

1. **Phase 5 收尾**（风险最低、惯性最大）：Hypermap 第 15 块起
   （dihedral/restricted/tame 前置，hypermap.hl 10643–13575，约 2–3 块），
   然后开 `Kepler/Text/Fan.lean`（ch5）。
2. **Phase 3 转置证书表示**（收益最大的硬骨头）：列主序 `checkDual` +
   soundness + socert 输出，目标 ~30s/LP；随后谈 43,078 全量化才有意义。
3. **Phase 4 超越函数层**：除法/√/Taylor 中点半径；长线投入。
4. Phase 5 后续：Fan → LocalFan → Assembly；`docs/module-map.md` 随块更新。
5. 零散：`string_archive.txt` 解析级核对（bonus）；architecture.md
   Phase 4 节细化。

## 7. 已知坑（教训汇总）

- `Set.BijOn` 是 And 三元组 def：自建引理要用 `Set.BijOn` 命名空间或
  显式调用，根命名空间的 `hf.foo` 点记法会解析到 `And`。
- `(quot).darts` 与 `Set.Finite.toFinset` 只是 defeq 非句法相等，`rw`
  换不动，用 `mem_toFinset.mp` + defeq `exact`。
- 匿名构造子 `⟨…, rfl⟩` 的 `rfl` 在非句法相等时失败，用 `by rfl`/显式项。
- Lean 的 `SearchPath.findWithExt` 按包根取第一个 LEAN_PATH 条目——
  分片 olean 必须写入 lake 规范路径 `.lake/build/lib/lean/...`，独立
  输出树不可行（本机实测）。
- SoPlex 的 Objective 行是浮点近似，证书数值只取 `-X`/`-Y` 有理输出。
- 大批量改文件时保持文件可编译；用脚本批量替换时注意保留文件尾的
  `end` 标记（曾出过截断事故，已恢复零损失）。

## 8. 快速自检（接手后第一件事）

```sh
cd /home/scroll/repos/kepler-conjecture-lean4
export PATH="$HOME/.elan/bin:$PATH"
git log --oneline -3            # 应见 966496b 或更新
make check                      # build + 公理审计，应全绿
wc -l lean/Kepler/Text/Hypermap.lean   # 8776（截至 2026-08-25）
```

若 `.lake` 缓存完好，全量 build 约几分钟（除 CertShards 外均为增量）。
