# WORK ORDER — `cert-pilot`（用户已批：证书路线**先试 1–2 条**，测实际机时再定后续）

> 状态：**用户 2026-11-06 已批准**（"2. 要不我们先做一两个看看实际运行时间，再定后续？"）。
> 铁律：**只做 1 条（最多 2 条），不许扩量**。这是测速，不是开工。

## 0. 目标（一句话）

拿**一条银行**跑完整的证书链，逐段记墙钟，回答："按现在的工具链，一条银行真做要多少机时？"

## 1. 选件

优先 `nliRestQITNPEA1_2_0`（`Assembly.lean:1561`；`bank_QITNPEA1_2_0`，余量 **1.63e−2**，
模板 `gamma4fgcy/w − 0.0057`，盒由 `PackingAuto21` 的 `bank_QITNPEA1tmpl` 决定）。
备选 `nliRestZTGIJCF4_1_1_0_0`（余量 3.70e−2）。

**为什么选银行而不是 `mainEstimate_*`**：28 条银行走的才是"逐案证书"那条路；
`mainEstimate_*` 的 88 条已实测不可排期（E4），拿它测速没有意义。

## 2. 链路（逐段计时，全部记录）

1. **case 构造**：从 `PackingAuto21` 的 `bank_*` def 抽出盒（每轴上下界，闭式）与结论式，
   生成 `bb_arb` 能吃的 case JSON（格式参考 `pipeline/interval/out/cases_prep/prep-*.json`；
   `emit_rpn.py` 的 `--ids` 走的是 prep 队列，银行没有 prep 记录 ⇒ 大概率要**手写 case JSON**，
   `--prec 64` + RPN prog 形）。
2. **探针**：`nice -n 19 <bb_arb> <case.json> --prec 64 --max-nodes 2000000 --cert <out>.cert.json`
   - 二进制：`/Users/zhangzhuo/c17_backup/tools/prep-p2/bb_arb`
   - **无 `--vars` 参数**（会被 `usage()` 拒绝；`vars` 从 case JSON 读）
   - 单条允许跑到 **3600 s**（这是测速，不是 browse）；记 `leaves / nodes / wall`
3. **发射**：`python3 pipeline/interval/emit_lean.py <cert> ...`（照 `EMISSION-RUNBOOK` 通路 A 的参数；
   参考 M4 的 `emit_lean.log`）。记 shard 数、源行数、源字节。
4. **编译**：按依赖序 `-o` 编 Base → shards（≤3 并发）→ top。逐段记墙钟。
5. **粘合**：写 `t11_*` 式 glue（若银行命题是 `∀ y, box → ineq`，glue 通常是
   `intro y …; exact C<id>_pos …` 一行 + 一个语义桥）。记行数与 axioms。
6. **探针验收**：`#print axioms` 该银行定理 = 标准三。

## 3. 必须交的数（缺一不可）

| 段 | 记什么 |
|---|---|
| case 构造 | 墙钟、是否手写（行数） |
| bb_arb | `status/leaves/nodes/wall_s`、cert 字节数 |
| emit_lean | 墙钟、shard 数、源行数/字节 |
| 编译 | 墙钟（分 Base/shards/top）、olean 总字节 |
| glue | 墙钟、行数、axioms |
| **合计** | **一条银行的总机时 / 总 olean**，以及"28 条 × 此数"的外推 |

## 4. 硬纪律

- 主仓 tracked 零改动；`/tmp/certpilot/` 工作；产物 → `~/c17_backup/lane_snapshots/cert-pilot/`。
- 证书 JSON 记字节后**立即删除**（单件可能几百 MB）。
- **不跑 Lean 全库构建**；只编本 case 需要的 shard。
- 单条超 3600 s（探针）或 4 小时（全链）⇒ 停，报"不可行 + 已到哪一步"。
- 用户尚未批准 28 条；**做完这条就停**，等裁决。

## 5. 交付

`~/c17_backup/lane_snapshots/cert-pilot/{DELIVERY.md,TIMING.tsv,logs/,case.json,glue.lean,patch.diff}`。
回我 ≤15 行：逐段墙钟、叶数/节点数、shard 数与 olean 体积、glue 行数、axioms、合计总机时、
以及一句「28 条按此外推 = 多少机时，值不值」。
