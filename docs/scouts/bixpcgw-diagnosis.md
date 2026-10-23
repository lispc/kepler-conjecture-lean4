# BIXPCGW 残叶病因分型诊断（2026-10-23，Lane E 交付）

> 快照：`lane_snapshots/bixpcgw/`（108 文件：samples/ 清单可复现、scripts/ 全部复现脚本、patches/bb_arb_diag.patch 行为保持插桩、logs/）。
> **总判**：残叶主因不是 sqrt(radicand≈0)，而是行列式型多项式子式的**区间 dependency overestimation**
> （644 对中 109 对 16.9% 丢符号）；TM 全案 0 闭合、mono-tree ≈148 CPU-days——**TM/mono 主攻 NO-GO**，
> **翻案** `docs/projects/archive/bixpcgw-residual.md` 旧处置建议。GO = gsplit2 守卫面感知切分（1.40×）
> + 纯多项式子式 sound 紧致化（centered form / affine arithmetic），验收线：resid336 ≥3× 且 100 盒全闭。
> 断点：1M 节点 21 pending（samples/pending21.json）；70,870 叶证书系 960df850 栈污染修复前伪影。

---

# BIXPCGW_7274157868_a 残叶病因诊断

日期: 2026-10-23. 车道: BIXPCGW 残叶攻坚（算法/数值，非 Lean 填证）。
主仓 HEAD: `c63e2f4b`（只读）。所有实验在 `/tmp/p4pE*`。

## 0. 结论先行

1. **134,788 STUCK 的主因不是 `sqrt(radicand≈0)`**，而是**行列式型多项式子式的
   区间求值丢失符号**（dependency problem）。这些多项式同时充当 ite guard、
   div 分母和 sqrt 的被开方因子；盒子真实符号是定的，但裸区间包络跨 0。
2. 在 23 个最硬残叶盒 × 28 个变量分母上：**真实角点符号变化 0/644**，
   而**区间包络跨 0 的有 109/644 = 16.9%**（另 535 对区间也定号）。
3. 因此当前 `--tm` / `--tm-tight` / `--tm-div2` / `--tm-ite-hull2` 都治不了根：
   - 全案 200k 节点内 TM+hull 有效模型 162,015 个，**闭合 0 个**；
   - 残叶盒样本上 TM 仅 1.08× 叶数削减，ite-hull2 1.04×；
   - **`--gsplit2`（guard 敏感度选维）1.40× 叶数削减**，是目前唯一 >1.2× 的杠杆，
     方向正确但仍不足以闭合全案。
4. `--mono-tree`/`--mono-dom-rung-keepconst=128` 是 Lean 证书发射层变换，
   不改变 bb_arb 叶数；本 case 的 kd 根 8/8 guard-straddle（gen-9），
   251k 叶成本 ~148 CPU-days。**不建议作为本 case 的主攻路线。**

## 1. 数据来源（实测 + 重建，非原始清单）

原始 134,788 盒清单**不在本机**（在 g4e worktree，未同步；全盘搜索无
`CRepairBIXPCGWx7274157868xaW1R12_m64.d`）。已检查的疑似位置：
`pipeline/interval/out/prod549/**/final_face.jsonl` 是 5490182221 的判定行
（schema `probe549-face`），不是本案；`c17_backup/lane_snapshots/w8rung/`
是本案的 mono-tree 证书实验（gen4–gen10），也不含残叶盒清单。
本报告的数据来源分三层：

### 1.1 种子证书（实测，逐数字复现）
- 用 `960df850^` 的 `bb_arb.c` 编译 `/tmp/p4pE_build/bb_arb_pre960`，跑
  `pipeline/interval/out/cases/BIXPCGW_7274157868_a.json`：
  **leaves=70870, nodes=141739, rc=0**，与 `pipeline/interval/out/bbarb_results3.txt`
  的历史行完全一致。该证书就是 repair 的种子（70,870 叶）。
- HEAD 的 `bb_arb` 在 `--max-nodes 1000000` 下**不闭合**：21 个 pending 叶。
  原因是 `960df850` 修的 disj 栈污染：70,870 叶证书是修复前的伪影证书之一
  （commit message: 旧 5 份波2证书 disj hit 伪影）。
- 所以“70,870 叶已闭合”与“134,788 残留”并不矛盾：前者是不可靠旧证书，
  后者是在它上面做 repair 的产物；HEAD 下本案仍有真实硬尾。

### 1.2 repair 机制（源码实测）
`pipeline/interval/repair_leaves.py` -> `emit_lean.stage_a_driver_disj`：
- 固定 rung `(12, -64)`；每轮把 FAIL 盒按**最宽维精确中点**二分；
- `FillParams.evalFill` 对 sqrt **现场算 `sqrtFloor` 证书**，不读 AST 的
  `(0,0)` 槽（`(0,0)` 只影响内核填参后的表达式）。因此“dummy sqrt 槽导致
  STUCK”的假说**被源码否定**（我们的 `--sqrtI-zero` C 模拟属于已排除假设，
  保留在日志里仅作反例）。
- `Trans.arctanI` 在 N 项交错 Taylor 截断下，|x|≈1 的余项 ~1/(2N+1)；
  closed `atan(1)` 固定 N=2048，open atan 用 rung N=12。

### 1.3 残叶盒样本（重建，固定清单）
原始清单缺失，因此用三类固定样本（全部有 md5、可复现）：
- `artifact_sample2000.json`: 从 70,870 叶证书按 seed 20261023 抽 2,000 叶。
- `pending21.json`: HEAD 1M 节点基线未闭合的 21 个前沿盒。
- `resid336.json`: 21 个前沿盒各按最宽维再分 4 次（16 子盒）= 336 个
  “残叶类”盒；宽度与 `bixpcgw-residual.md` 的 2^-4..2^-6 量级一致。
- `strat360.json` / `corner60.json`: 按残叶文档边缘分布合成的分层样本与
  全边缘 corner 样本，仅用于“边界假说”对照。
- 116 个敏感子式（18 个 sqrt radicand、36 个 div 分母、48 个 ite guard、
  14 个 abs 参数）拆成独立 mini-case，逐盒求区间
  （`subcases/index.json`）。

## 2. 病因分型（可复现表格）

### 2.1 敏感事件覆盖率（prec 64，逐盒独立求子式）
| 样本 | n | sqrt radicand 跨 0 | div 分母跨 0 | ite guard 跨 0 | abs 参数跨 0 | 触域边 |
|---|---|---|---|---|---|---|
| artifact 2,000 叶 | 2000 | 80 (4.0%) | 1708 (85.4%) | 2000 (100%) | 1652 (82.6%) | 1725 (86.2%) |
| resid336 | 336 | 73 (21.7%) | 73 (21.7%) | 173 (51.5%) | 38 (11.3%) | 328 (97.6%) |
| corner60 | 60 | 0 | 0 | 60 (100%) | 0 | 60 (100%) |
| strat360（逐维分层） | 360 | 1 (0.3%) | 267 (74.2%) | 358 (99.4%) | 266 (73.9%) | 240 (66.7%) |

注意：sqrt 与 div 的跨 0 是**同一组 73 个盒子**，因为它们共享同一些行列式
因子（sqrt 的被开方 = `4·y_i²·D`，div 的分母也是 D 的变体）。

resid336 的根盒裸判（prec 64，分档）：`disj` 137 / `zero` 126 /
`guard` 73；path-sensitive 计数 `itestr=173`（与上表 51.5% 一致）、
`div0=sqrt0=73`、`absx=27`。即 137 个盒子靠 disj 支闭合，126 个主式区间
含 0 但 guard 定号，73 个 guard 严格跨 0。

### 2.2 resid336 难度按类（bare bb_arb，max-nodes=20,000）
| 组 | n | pass | 总叶数 | 平均叶/盒 |
|---|---|---|---|---|
| sqrt(或 div) 跨 0 | 73 | 67 | 65,430 | **976.6** |
| 仅 guard 跨 0 | 100 | 95 | 46,530 | 489.8 |
| 无敏感事件 | 163 | 151 | 67,669 | 448.1 |
| 全部 | 336 | 313 | 179,629 | 534.6 |

- 无 sqrt/div 跨 0 的盒子平均 464 叶；有 sqrt/div 跨 0 的 977 叶 = **2.1×**。
- abs 跨 0：38 盒，平均 1,120 叶（2.2×）。
- 域边分组（同一基线）：
  | 边 | n | pass | 平均叶/盒 |
  |---|---|---|---|
  | y2=2 下缘 | 16 | 11 | **2,908** |
  | y4=2√2 上缘 | 112 | 89 | 1,561 |
  | y3=2 下缘 | 136 | 116 | 939 |
  | y1=2.6508 上缘 | 176 | 156 | 776 |
  | y6=2 下缘 | 256 | 236 | 635 |
  | y5=2 下缘 | 216 | 198 | 594 |
- 23 个在 20k 节点内未闭合的盒子**全部**是多边角点：同时贴 y2/y3/y5/y6→2、
  y1→2.6508、y4→2√2 中的 ≥3 个。8 个不贴任何边的盒子各只需 1 叶。
- 硬盒实例（box 0）：真实 D 角点范围 [0.399, 38.04]（正定、无符号变化），
  区间包络 [-17.11, 53.33]（跨 0）。这就是失败机制的最小复现。

### 2.3 符号丢失 census（23 个最硬盒 × 28 个变量分母 = 644 对）
| 类别 | 对数 |
|---|---|
| 真实角点符号变化 | **0** |
| 真实定号、区间包络跨 0 | **109 (16.9%)** |
| 真实定号、区间也定号 | 535 |
| 无法判定 | 0 |

结论：guard/div/sqrt 的“跨 0”是**区间依赖过估**，不是盒子真的跨过零面。

### 2.4 rung-N Taylor 截断（第二因，非主因）
用 C 复刻 `arctanI` 的 N 项截断（`--atan-rung N`），在 artifact 2,000 叶上：
| N | 12 | 16 | 20 | 24 | 32 | 48 | 64 | 96 | 128 | 裸 arb_atan |
|---|---|---|---|---|---|---|---|---|---|---|
| FAIL | 360 | 312 | 279 | 260 | 238 | 205 | 194 | 182 | 179 | 150 |

- N=12 时 18.0% fail（与历史 19,147/70,870=27% 同量级，样本不同）。
- 用 N=12 模型做 8 轮 repair proxy：18,216 → 6,090 → 8 → 0 fail，
  **二分在该模型下收敛**；所以 rung 截断单独解释不了“零收敛 STUCK”，
  必须叠加 2.3 的区间符号丢失。二者叠加时，guard 跨 0 的盒子永远走 hull，
  hull 宽度不随坐标二分快速下降 → 慢收敛/STUCK。

## 3. 与 `bixpcgw-residual.md` 的对照

**对上的部分**：
- 边界聚集：resid336 中 97.6% 贴边；最难的 y2=2 下缘、y4=2√2 上缘与文档一致。
- 盒宽量级：2^-4..2^-6（文档）与种子证书 + 4~8 次最宽维二分一致。

**需要修正的部分**：
- 文档标题的“sqrt 边界过估 √w”只是**下游症状**。变量 radicand 本身并不小
  （我们的样本中 radicand 上界 92–941），跨 0 来自行列式因子 D 的区间符号丢失。
- 文档的“sqrt 边界”无法解释为什么 `ite guard` 在 100%（artifact 叶）/
  51.5%（残叶盒）的盒子上跨 0；guard 才是修复路径上的第一道门。
- 文档的 134,788 数字无法逐盒复现（原始清单缺失）；本报告给出的是机制层面
  可复现的证据链，而不是同一批盒的重放。

## 4. 实测 / 推断 / 未跑

**实测**：
- 70,870 叶证书复现；HEAD 1M 节点 21 叶未闭合；200k 节点 9 叶未闭合。
- 全部敏感事件覆盖率、难度分组、符号丢失 census、rung-N 曲线、
  repair proxy 轮次、mini-case 配置表、边界切分负结果。
- 诊断二进制默认路径与 stock **stdout/stderr md5 逐字节相同**。

**推断**（有证据但未逐盒重放）：
- 原始 134,788 盒的分布与 resid336 同属“多边角点 + 行列式符号丢失”类。
- 历史 repair 的零收敛由“区间符号丢失 + 固定 rung 12”共同造成。

**未跑**：
- 全量 206,120 盒的 Lean 重放（原始清单缺失；Lean IR 解释器 ~1 min/盒，
  本机不可行，且按纪律不占锁）。
- `--mono-tree` 在本样本上的 Lean 端到端（它是发射层 flag，不是 bb_arb 路径；
  gen-9 已测 251k 叶 ≈148 CPU-days）。
- 真正的 centered/affine 多项式求值原型（见 DELIVERY 的建议；需要 C 侧
  ~500–800 行，本波未做）。

---

# BIXPCGW 残叶实验记录

日期: 2026-10-23. 环境: macOS arm64, 36 GB; `nice -n 19`; 并发 ≤2;
主仓只读, 所有产物在 `/tmp/p4pE_work`, 快照在
`/Users/zhangzhuo/c17_backup/lane_snapshots/bixpcgw/`。

## 0. 构建与回归

源代码: 主仓 `pipeline/interval/bb_arb.c`（开工时 HEAD c63e2f4b；
实验期间主仓前进到 5e52cf94（PA18/LP 提交），但 `bb_arb.c` 逐字节不变
（md5 `2225a8c6cf8417b092931b5a8734e61f`），故结果不失效）。
- `/tmp/p4pE_build/bb_arb_stock`: 原样编译。
- `/tmp/p4pE_build/bb_arb_diag`: 诊断补丁（`patches/bb_arb_diag.patch`），
  新增 `--plain-probe`、`--atan-rung N`、`--atan1-box`、`--sqrtI-zero`、
  `--tm-fixed`。默认路径零改动。

编译命令:
```
T=/tmp/p4prep/pipeline/tools
gcc -O2 -std=c99 -Wall -Wextra \
  -I$T/flint-3.3.1/include -I$T/mpfr-4.2.2/include -I$T/gmp-6.3.0/include \
  pipeline/interval/bb_arb.c -o bb_arb_stock \
  -L$T/flint-3.3.1/lib -L$T/mpfr-4.2.2/lib -L$T/gmp-6.3.0/lib \
  -lflint -lmpfr -lgmp -lm \
  -Wl,-rpath,$T/flint-3.3.1/lib -Wl,-rpath,$T/mpfr-4.2.2/lib \
  -Wl,-rpath,$T/gmp-6.3.0/lib
```

**裸路径逐字节回归**（默认旗标, `--max-nodes 2000`）:
```
stock: md5(out)=629e4dfe00dfb7076f6117cdb2d1f89a
       md5(err)=b4551758229dbea5ee4763b2fe723df7
diag : md5(out)=629e4dfe00dfb7076f6117cdb2d1f89a  (identical)
       md5(err)=b4551758229dbea5ee4763b2fe723df7  (identical)
```
`cmp` 也 `STDOUT_IDENTICAL` / `STDERR_IDENTICAL`。
补丁的 soundness 论证：所有新增代码只在 `g_diag` / `plain_probe_path` /
`g_atan_rung` / `g_sqrtI_zero` / `g_tm_fixed` 旗标开启时执行；默认分支的
判定、切分、证书输出代码路径未改。`--atan-rung` 与 `--sqrtI-zero` 是
**诊断模型**，明确不用于证书；`--atan1-box` 是 gen-10 的模型对照。

## 1. 数据重建

### 1.1 种子证书（pre-stack-fix）
```
git show 960df850^:pipeline/interval/bb_arb.c > bb_arb_pre960.c
# 同 0 节命令编译为 bb_arb_pre960
nice -n 19 ./bb_arb_pre960 BIXPCGW_7274157868_a.json \
    --max-nodes 1000000 --cert artifact.cert.json
```
结果: `CLOSED: leaves=70870 nodes=141739`（rc=0），与
`pipeline/interval/out/bbarb_results3.txt` 一致。

### 1.2 HEAD 基线
```
nice -n 19 ./bb_arb_stock BIXPCGW_7274157868_a.json --max-nodes 1000000
-> 节点超限（1000000），未闭合叶 21 个, rc=2
```
21 个盒已固定为 `samples/pending21.json`。

## 2. 全案配置对照（实测）

命令模板:
```
nice -n 19 ./bb_arb_stock CASE --max-nodes 200000 [FLAGS]
```
所有运行都在 200,000 节点上限处停止，**9 个 pending 叶**：

| 配置 | TM att | TM valid | TM closed | wall (s) | pending |
|---|---|---|---|---|---|
| baseline | – | – | – | 11.82 | 9 |
| `--tm` | 216 | 0 | 0 | 11.99 | 9 |
| `--tm --tm-tight` | 216 | 0 | 0 | 11.88 | 9 |
| `--tm --tm-div2` | 216 | 0 | 0 | 12.04 | 9 |
| `--tm --ite-hull2` | 216 | 216 | **0** | 13.25 | 9 |
| `--tm --ite-hull2 --gsplit2` | 216* | 216* | 0 | 13.13 | 9 |
| `--tm --tm-fixed --tm-w0 10` | 200000 | 0 | 0 | 75.71 | 9 |
| `--tm --ite-hull2 --tm-fixed --tm-w0 10` | 200000 | 162015 | **0** | 1108.06 | 9 |
| `--tm --tm-div2 --tm-fixed --tm-w0 10` | 200000 | 0 | 0 | 81.23 | 9 |

\* gsplit2 行的 TM 计数打印为部分跑（其超时行为与 hull2 同）。

- 自适应阈值在 `--tm` 下 216 次尝试后从 0.25 跌到 ~0.03（窗口 64 全灭），
  之后几乎不再尝试；`--tm-fixed` 冻结阈值用于公平统计。
- `guard跨0` 是 TM invalid 的唯一原因（无 hull 时）；有 hull 时 TM 有效但
  **0 闭合**。
- `--tm-fixed` + hull 用 18.5 min 证明“TM 模型有效 ≠ 能判定”：162k 个有效
  模型全部 `loBound ≤ 0`。

## 3. 残叶盒 mini-case 对照（主表）

固定样本: `samples/resid336.json`（336 盒）。取**前 100 盒**（确定性）做
全配置；baseline 的 336 盒结果也保留。每盒作为 case root，`--max-nodes 20000`。

命令:
```
nice -n 19 ./bb_arb_diag minicases/resid_XXXX.json --max-nodes 20000 [FLAGS]
```

| 配置 | pass | 叶数 | 节点数 | wall (s) | 叶数比 |
|---|---|---|---|---|---|
| baseline（100 盒） | 94/100 | 68,410 | 136,726 | ~120 | 1.000 |
| `--tm` | 94/100 | 63,141 | 126,188 | 64.7 | **0.923** |
| `--tm --tm-tight` | 94/100 | 63,141 | 126,188 | 69.7 | 0.923 |
| `--tm --tm-div2` | 94/100 | 63,141 | 126,188 | 68.2 | 0.923 |
| `--tm --ite-hull2` | 95/100 | 65,978 | 131,861 | 344.1 | 0.964 |
| `--tm --ite-hull2 --gsplit2` | 95/100 | **48,936** | **97,777** | 178.0 | **0.715** |

- **gsplit2 是唯一强杠杆：叶数 −28.5%，节点 −28.5%**，代价 wall 1.5×
  （相对 TM）、但比 ite-hull2 快 1.9×。
- `--tm-tight` / `--tm-div2` 在该样本上无差别（这些盒子没有 TM 可用的
  div 越零事件）。
- 336 盒 baseline: 313/336 pass, 179,629 叶, 358,945 节点, 395.3 s。
- 23/336 在 20k 节点内无法闭合；全部是 y1/y2/y3/y4 多边角点（见 DIAGNOSIS §2.2）。

## 4. 边界对齐切分原型（负结果）

脚本 `scripts/boundary_split.py`：对前 100 个残叶盒，若严格跨过
`y1=6627/2500` 或 `y4=2√2` 的有理近似 q（limit_denominator 2^40），
在该处切开，得到 212 个子盒；逐子盒跑 bare bb_arb（20k 节点）。

| 方案 | 根盒数 | pass | 叶数 | 节点 | wall |
|---|---|---|---|---|---|
| 不切（baseline） | 100 | 94 | 68,410 | 136,726 | ~120 s |
| 边界对齐切分 | 212 | 190 | **97,530** | 194,870 | 187.7 s |

- 叶数 **+42.6%**（负结果）。原因：y=2 是 root 下缘（只贴不跨）；
  y1=2.6508 / y4=2√2 只存在于 case 盒的相对外扩 sliver（~2e-10），
  切掉 sliver 对主要过估没有帮助，反而失去父盒二分共享工作。
- 该原型**不推荐**进入下一波。

## 5. rung-N 模型与 repair proxy

### 5.1 atan 截断曲线（artifact 2,000 叶, prec 64）
```
nice -n 19 ./bb_arb_diag CASE --prec 64 --atan-rung N \
    --plain-probe artifact_sample2000.json
```
| N | 12 | 16 | 20 | 24 | 32 | 48 | 64 | 96 | 128 | 裸 |
|---|---|---|---|---|---|---|---|---|---|---|
| fail | 360 | 312 | 279 | 260 | 238 | 205 | 194 | 182 | 179 | 150 |

### 5.2 repair proxy（8 轮, 最宽维二分）
- `prec 13`（校准到 26.5% 初始失败率）:
  round1 18,216 fail → round2 6,090 → round3 8 → round4 8 → round5 0。
- `prec 64 + --atan-rung 12`:
  11,963 → 4,034 → 0。
- 两个模型都收敛，而历史 Lean repair 零收敛；因此单一 rung 截断不是充分解释，
  必须叠加区间符号丢失（DIAGNOSIS §2.3）。

## 6. 敏感子式探针

- 生成: `scripts/subexpr_gen.py`（116 个唯一子式，318 条记录）。
- 求值: `scripts/run_subexpr_probe.py <tag> 64`，每子式一个 mini-case +
  `--plain-probe`。
- 分类: `scripts/classify_boxes.py <tag>`。
- 原始 JSONL 在 `/tmp/p4pE_work/subprobe_*_p64/`（快照只保留 flags 与
  index，原始可由脚本重生）。

## 7. Lean probe（未完成，纪律优先）

- `scripts/lean_repair_probe.py` 用**真实的** `stage_a_driver_disj` 驱动
  （pinned rung 12/-64）跑样本。
- 500 盒运行持全局锁 15 min 未完成（IR 解释器 + 闭式 atan N=2048 记忆化），
  按编排者要求 kill 并释放锁；5 盒再次尝试 5 min 未完成，同样 kill。
- 因此本报告**不声称**任何 Lean 逐盒 PASS/FAIL 数据。
- 已由源码确认的事实：`evalFill` 现场算 sqrt 证书；closed atan(1) = N=2048；
  open atan = rung N；`wave2-disj-design.md` 记录“4 个最深叶全档位 FAIL、
  best 停首档”和 out=-64 粒度嫌疑。

## 8. 日志索引

快照 `logs/`:
- `reg_stock.{out,err}`, `reg_diag3.{out,err}` — 回归 md5 证据。
- `q20k_*.{out,err}`, `q200k_*.{out,err}` — 全案配置。
- `calib_p*.jsonl` — prec 校准。
- `atanr*.jsonl` — rung-N 曲线（部分文件较大，快照只放摘要 + 一档原始）。
- `repair_proxy_p13.log`, `repair_proxy_atan12.log` — repair 轮次。
- `minicase2.log`, `minicase_results_100.json` — 残叶盒主表。
- `boundary_split.log`, `boundary_split_results.json` — 边界负结果。

## 9. 未跑 / 不能跑

- 134,788 原始盒的逐盒重放：原始清单缺失 + Lean 成本。
- 全量 206,120 叶 Lean 重建：本任务红线。
- centered/affine 多项式求值的 C 原型：本波未实现（下一波建议，见 DELIVERY）。
- `--mono-tree` 在本样本的 Lean 端到端：发射层 flag，需要 Lean 全链；
  gen-9 的 251k 叶成本模型 ~148 CPU-days。
