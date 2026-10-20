# LAUNCH_FULL.md — 549 全量重演管线 v1 · single 类生产 launch runbook

工位：549 加速项目 · 全量重演管线 v1（single 类生产验证片）。
分支 `wip/auto-packing`。日期 2026-09-26。
前置：arctanK 曲率紧致化已合 main；rung=128 发射层钉死 + ladder 自适应；
本工位交付 **可断点续跑的生产编排 `pipeline/interval/run_full.sh`** + 1,000 叶
single 类生产验证片实测 + 全量吞吐/磁盘外推。

---

## 0. TL;DR

1. **管线已验证**：1,000 叶 single 验证片全链跑通——**全链 PASS 977/1000
   = 97.7%**（全部收官 rung 128），locheck 60 叶 2048 口径对账**verdict
   翻转 0（flagged 0；lb 漂移为信息性，见 §2.1）**，50 个生产 shard
   （`C549ProdS0001..0050`）decide 构建**全 EXIT 0、零裸 error、零 sorryAx**。
2. **全量外推（165,219 single 叶）**：stage-A ≈ **67h @16 路（2.8 天）**；
   decide 构建 ≈ **190h @12 路（7.9 天）**；合计 wall ≈ **8.0 天（流水重叠）
   / 10.8 天（串行相位）**；磁盘 ≈ **19GB**（源码 2.9 + olean 12.9 + 状态/清单 ~3）。
3. **启动一条命令，断点续跑 = 重跑同命令**（只处理 pending）：

```bash
cd /home/scroll/repos/kepler-conjecture-lean4
setsid nohup stdbuf -oL pipeline/interval/run_full.sh \
  --tag=full --class=single --start=0 --count=0 --stride=1 \
  --jobs=12 --a-jobs=16 --locheck-n=60 \
  > /tmp/opencode/prod549/full_run.log 2>&1 < /dev/null &
```

---

## 1. 管线架构（run_full.sh）

```
tight 证书 cert549_tight.json (212,798 叶)
   │ [0] manifest   普查池→master manifest：叶盒 + params 槽位 + 类标 single/straddle
   │                （single = guard 定号池 then/else = 165,219；straddle = none = 47,579）
   ▼ [1] select    --class/--start/--count/--stride 抽叶 → shard 分配（20 叶/shard）
   ▼ [2] stagea    stage-A 批探针 @rung 阶梯轮次 128→512→2048
   │               der（±∂xⱼ 两方向）→ cert（裸区间 interval 路线）∥ full（原盒基线）→ face（der 定向）
   │               轮次语义同 cmd_batch：不完备叶整体回退下一 rung（全部层重证、旧轮行作废）
   ▼ [3] merge     终态收敛：逐叶 PASS/FAIL + 首败层归因（der→face→cert）+ params 回填
   │               → final/{der,cert,face,full}.jsonl（emit 直读，逐叶 rung 一致性过滤）
   ▼ [4] locheck   done@128 抽样（≥50）× face @2048 对账：verdict 翻转 + loBound 指数；
   │               flagged 叶保守排除（重触发 merge）
   ▼ [5] emit      emit_mono.py emit --cert-route=interval --shard=20
   │               → namespace 重命名 → lean/Kepler/Interval/Cases/C549ProdS{NNNN}.lean
   ▼ [6] build     逐模块 `lake build Kepler.Interval.Cases.C549ProdS{NNNN}`（≤12 路，
   │               /usr/bin/time 记 wall+RSS；exit0 ∧ 零 ^error ∧ 零 sorryAx ⇒ shard PASS）
   ▼ [7] report    slice_report.json（PASS 率/分层归因/耗时/外推）
```

**状态机与断点续跑**：
- 叶状态 `pending → probe → PASS | FAIL(der|face|cert|locheck)`；
  shard 状态 `pending → probe → emitted → built → PASS | FAIL`。
- 一切产物按 shard/stage 落盘（`$WORK/shards/S<k>/r{rung}_{stage}.jsonl` 等），
  任务级**覆盖度校验**后复用（缺行/坏行自动重探）；派生态（回退轮工作集）
  每次 stagea 重算自愈。**断点续跑 = 重跑同命令**，只处理 pending。
- 状态文件：`$WORK/status.jsonl`（每 shard 一行，原子重写，短命令轮询用）、
  `$WORK/master.manifest.jsonl`（逐叶状态+params 终态回填）。
- 默认 `$WORK = pipeline/interval/out/prod549/<tag>`；全量建议单独 tag=full。

**CLI（monopoly 参数化）**：
```
run_full.sh --class=single|straddle|all --start=N --count=M --jobs=B
            [--a-jobs=A] [--stride=K(0=auto: ⌊pool/M⌋)] [--shard=20]
            [--tag=T] [--work=DIR] [--phases=...] [--locheck-n=60] [--no-native]
```
分批示例（straddle 类起点 / 补段）：`--class=single --start=20000 --count=20000`。

**资源预算（硬性）**：stage-A ≤16 路 lean（nice -19）；decide 构建 ≤12 路
（RSS 11-12GB/shard ×12 ≈ 145GB）；`ulimit -s unlimited` 全程零栈事故；
不做 git、不跑全量 `lake build`（只逐模块目标构建）。

---

## 2. 验证片实测（1,000 叶 single，stride 165 均布，2026-09-26）

输入：tight 证书 + 全量普查池 165,219 single；shard 20 叶 × 50；
stage-A 16 路 / decide 12 路；`val1000` workdir。

### 2.1 PASS 率与归因

| 项 | 数值 |
|---|---|
| 全链 PASS | **977/1000 = 97.7%**（与 1080 叶预演 97.8% 一致） |
| rung 分布 | **100% 收官 @128**（回退机制待命，未翻转任何叶） |
| 失败归因 | **der 层 23（2.3%）**——双方向 NEG 真不可折叠叶，512/2048 救回 0（同预演） |
| face / cert 层 | **零损失**（cert 裸区间路线 100% PASS） |
| 原盒全叶 full 基线 | PASS 1000/1000（失败叶 TM 仍可用 → 走全盒基线口径可回收，属 fold2/粗化工位） |
| locheck | 60 叶 × face@2048（120s/叶实测）：**verdict 翻转 0 → flagged 0**；lb 指数漂移 9/60、尾数漂移 30/60 记为**信息性**（两 rung 的 loBound 均为内核精确验证的 sound 下界，其序不固定——曲率紧致化后漂移面扩大属预期，判据已定为 flip-only） |

### 2.2 三阶段耗时

| 相位 | wall | 折算 |
|---|---|---|
| manifest+select | 4s | 一次性（普查池校验+抽叶） |
| stage-A（16 路） | **1,467s = 24.5 min** | **1.467 s/叶 wall@16 路**；core：der 13.5 + face 3.0 + full 3.3 + cert ~0 ≈ **19.8 core·s/叶**（@128 完备叶）；der-fail 叶阶梯重探额外 ~150 core·s/叶（2048 口径 full ~120s 主导，占 2.3% 叶） |
| locheck（60 叶 @2048） | **1,216s ≈ 20 min** | face@2048 实测 120s/叶（=39× face@128）× 60 ÷ 6 路；全量建议每 2 万叶 1 pass |
| emit（50 shard） | 10s | ~0.2s/shard |
| decide 构建（12 路） | 50 shard × 782–1082s = **4,978s ≈ 83 min** | **51.5 s/叶**（med 1024s/shard；与预演 53 shard 12 路实测 1016–1073s/shard 逐位一致；12 路并发零惩罚） |
| **端到端** | **6,461s ≈ 1.80h** | stage-A 24.5min + build 83min + 杂项 |

### 2.3 shard RSS / 墙钟

| 口径 | wall/shard（20 叶） | 峰值 RSS |
|---|---|---|
| decide 主线（12 路） | 869–1025s（med ~1022s） | **10.9–11.5GB** |
| native 对照（`C549ProdS0001NativeCtl`，非主线） | 208s（**10.4 s/叶，4.9×**） | 6.6GB |
| stage-A 探针驱动（16 路） | — | ≤3GB/进程（load 29@128 核，余量充足） |

### 2.4 失败叶分类

- **der 双方向 NEG（23 叶）**：真薄余量不可折叠；locheck 同构、全 rung 复证
  （512/2048 救回 0）；原盒 full TM 全 PASS → 可走全盒基线（不折叠）口径。
- face/cert/locheck：**零失败**。

---

## 3. 全量吞吐外推（165,219 single 叶）

由验证片实测线性外推（并发预算 stage-A 16 路 / decide 12 路）：

| 项 | 外推 | 依据 |
|---|---|---|
| 抽叶 | 8,261 shard（20 叶） | 165,219 / 20 |
| 预计发射 | **161,419 叶 = 8,071 shard**（97.7%） | 验证片 PASS 率 |
| stage-A wall | **67.3h ≈ 2.8 天** @16 路 | 1.467 s/叶 wall（1,467s/1,000 叶实测线性外推）；core 口径保守 73.8h |
| stage-A core | ~1,183 core·h | 25.7 core·s/叶（含 der-fail 阶梯重探） |
| decide 构建 wall | **192.4h ≈ 8.0 天** @12 路 | 8,071 × 1,024s / 12（med 实测） |
| decide core | ~2,309 core·h | 51.5 s/叶 × 161,419 |
| emit + manifest | ~40 min（可与构建重叠） | 0.2s/shard |
| locheck（每 2 万叶 1 pass） | ~2.7h 累计 | 20 min/pass（face@2048 120s/叶 × 60 ÷ 6 路） |
| **总 wall（相位串行）** | **≈ 262h ≈ 10.9 天** | |
| **总 wall（stage-A→build 流水重叠）** | **≈ 194h ≈ 8.1 天** | build 不等 stage-A 全清 |
| 磁盘：源码 | **2.9GB** | 18.5KB/叶 × 161,419 |
| 磁盘：olean | **12.5GB** | 81.4KB/叶 |
| 磁盘：状态/清单/日志 | ~3GB | master manifest ~0.3GB + 逐 shard |
| RSS 峰值 | build 12×11.8=142GB；stage-A 16×3=48GB | 机器 503GB ✓（验证片实测 med 11.0 / max 11.8GB） |

**杠杆对照**（不改变 v1 启动，仅记录）：
- native_decide 扩围（待批准）：161,419 × 10.4s = **466 core·h → @12 路 39h ≈ 1.6 天**；
  代价 axiom 面 `Lean.ofReduceBool`（对照模块已产，决策走 DECISIONS）。
- ÷7.7 粗化（fold2 工位）：折叠组 decide 51s/组 → 组数 20,986 → **297 core·h**；
  与 native 组合即车道日志十五更 109 native core·h 口径。
- der-fail 叶跳过回退轮重探（v1.1 优化）：省 ~150 core·h stage-A（语义差异需备案——
  当前轮次语义完整复证 der-NEG 于全 rung，与 cmd_batch 一致）。

---

## 4. Launch runbook（全量 single 类）

### 4.1 启动（后台 setsid，一条命令）

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/scroll/repos/kepler-conjecture-lean4
setsid nohup stdbuf -oL pipeline/interval/run_full.sh \
  --tag=full --class=single --start=0 --count=0 --stride=1 \
  --jobs=12 --a-jobs=16 --locheck-n=60 \
  > /tmp/opencode/prod549/full_run.log 2>&1 < /dev/null &
```

- `--count=0` = 全池 165,219 叶；建议先冒烟 `--count=40 --tag=fullsmoke` 链路复验
  （~25 min）再放全量。
- 分批口径：`--start=N --count=M`（如 4 × ~41,000 叶分周滚动）。
- straddle 类：`--class=straddle`（47,579 叶，另链口径，本 runbook 不覆盖）。

### 4.2 监控（短命令轮询）

```bash
W=pipeline/interval/out/prod549/full
tail -5 /tmp/opencode/prod549/full_run.log            # 相位心跳
python3 - <<'PY'                                      # shard 状态汇总
import json,collections
c=collections.Counter()
for l in open("$W/status.jsonl".replace("$W","pipeline/interval/out/prod549/full")):
    c[json.loads(l)["state"]]+=1
print(dict(c))
PY
grep -c PASS $W/builds/summary.txt 2>/dev/null        # 已 PASS 模块数
grep -c "rc!=0\|error" $W/taskfails.log 2>/dev/null   # 任务级失败
ps aux | grep -c "[l]ake build"                       # 在编进程数（≤12）
free -g | head -2                                     # RSS 余量
```

### 4.3 预计完成

| 相位 | 累计 wall（自启动） |
|---|---|
| stage-A（16 路） | +2.8 天 |
| 首批 shard 可入构建（流水重叠） | +25 min 起 |
| decide 构建（12 路） | +2.8 天起持续至 **≈ 8.0 天** |
| 终态 report / status | ≈ **8.0 天**（串行相位则 10.9 天） |

### 4.4 断点续跑

- 任何原因中断（机器重启/误杀/磁盘满）：**重跑 4.1 同一条命令**。
- 已 PASS shard / 已 valid 判定行 / 已构建模块全部跳过（覆盖度校验），
  只补 pending；已完成 1,000 叶验证片 workdir（val1000）不受影响。
- 单 shard 级失败（TASKFAIL/EMITFAIL/build FAIL）：`$W/taskfails.log` +
  `status.jsonl` 中 state=FAIL 行定位；修因后重跑即补。
- 构建零 error 判据：`builds/summary.txt` 每行 `rc=0 error行=0 sorryAx=0`；
  终验再加 `grep -c '^error' $W/builds/*.log` 全 0。

### 4.5 风险与护栏

| 风险 | 护栏 |
|---|---|
| der-fail 叶 2048 full 重探贵（120s/叶 × 2.3%） | 预算已含（+9h）；v1.1 可跳过 |
| 构建 RSS 12×11.5GB | 与其他工位共址时先 `free -g` 核对 ≥160GB 空闲 |
| locheck flagged > 0 | 管线自动保守排除 + 重收敛（预期 0，验证片实测 0） |
| CertTM/Trans 被并行工位改动 | 启动前 `git status` 确认二者无未合变更（本工位零改动） |
| 磁盘 | 需 ~19GB（936GB 盘现用 39%，充裕） |

---

## 5. 验证片构建零 error 证据

- `pipeline/interval/out/prod549/val1000/builds/summary.txt`：
  50 主线 + 1 native 行，**全 EXIT 0、`^error` 计数全 0、sorryAx 计数全 0**；
  逐模块 axiom 审计行（`#print axioms`）全标准三 `[propext, Classical.choice, Quot.sound]`。
- 冒烟链（40 叶 / 2 shard）先行全绿后放行千叶批（07:31 冒烟 → 08:15 千叶启动）。
- 判定数据与日志：`pipeline/interval/out/prod549/val1000/`
  （`slice_report.json` / `status.jsonl` / `master.manifest.jsonl` / `builds/` /
  `locheck/locheck_report.json`）；生产 shard：`lean/Kepler/Interval/Cases/C549ProdS00{01..50}.lean`。
- 工具面改动：`emit_mono.py` 仅修复 `probe --ladder` 终写崩溃
  （`ladder` bool → `ladder_seq`，该路径此前从未被端到端执行）；
  新增 `pipeline/interval/run_full.sh`；**CertTM/Trans/emit_hull_pilot/emit_fold2 零改动、零新增 axiom**。
