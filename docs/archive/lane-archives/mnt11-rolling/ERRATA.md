# ERRATA — `mnt11-rolling`

> 只增不改。纠正以本文件为准；`TRIAGE.tsv` 与 README 正文不覆写。

## E1（2026-11-06）`ox3q1hP25` 的 docstring 锚点错了

`lean/Kepler/Text/PackingAuto25.lean:86`（及 Assembly `分量 2/6` 注释）写
`NEEDS: exact Oxl_def.hl body`，但 **`Oxl_def.hl` 里没有 `ox3q1h` 这个 `let`**。

真实构造：`reference/flyspeck/text_formalization/nonlinear/merge_ineq.hl:87-92`

```
let ox n i = (idq_of_string (Printf.sprintf "OXLZLEZ 6346351218 %d %d" i n)).ineq;;
let ox_conj n = end_itlist (curry mk_conj) [tm0 n; tm1 n; tm2 n; tm3 n; tm4 n];;
let ox3q1h_term() = end_itlist (curry mk_conj) (map ox_conj (0--(numcases-1)));;
let ox3q1h() = new_definition (mk_eq (`ox3q1h:bool`,ox3q1h_term()));;
```

语义标签（即 `cc_real_model_v11` 的那个合取支）在
`reference/flyspeck/text_formalization/packing/OXLZLEZ1.hl:91-93`（行尾注释 `// ox3q1h`）。

数据规模：`ineqdata3q1h.hl` 46 record × 5 支 = **230 条**（Lean 侧 `ox3q1hIds.length = 230`，`rfl`）。
作者自述：*"the inequalities for the hard case of the cluster inequality, consisting of 4 blades,
3 quarters, and one half-weight"*。

**影响**：`ox3q1hP25 : Prop := sorry` 是**陈述级洞**（`sorryAx Prop`，连命题内容都不定），
不是证明洞。要真化必须两步：①渲染 230 条（机械，2–4k 行）②认证（证书农场）。
这也是 `real_model_ox3q1h_merge` 冻结的原因。**不是本轮改动，仅记账。**

## E2（2026-11-06）M0 的 `leaf_tier` 静态档位**不可作为成本依据**

M2 试点选 `1834976363`（`leaf_tier=T1`、`cost_rank=67`）的依据是 `prep_queue.jsonl` 的档位，
实测该档 `tier_source=static`（静态估计），真实运行 **10M 节点 / 605 pending 仍不收敛**，
8m17s 停手、**证书未发射**。

编排者补测（88 条 NEEDS-CERT 全量 cross-reference `prep_queue.jsonl`）：

| `probe.status` | 条数 | 说明 |
|---|---:|---|
| `closed` | **3** | 全 `tier_source=measured` 且全是 T6：`8405387449`(40,785 叶/0.592s)、`4680581274 delta issue-cayleytr`(75,965/4.32s)、`4680581274 1x`(133,228/2.799s) |
| `limit` | 4 | 含 `1834976363` |
| `timeout` | 1 | — |
| 无 probe | **80** | — |

而 **T0/T1/T2 那 28 条全部是 `tier_source=static`**。

**两条纠正**：

1. ~~「28 条 T0–T2 加起来是一个下午的活」~~ —— **不成立，已收回**。静态档位与实测收敛性无关。
2. **叶数大 ≠ 难证**：40,785 叶 0.59s 就闭合。真正的难点是"曲面型"命题
   （`num1=0` 曲面上要证 `dnum1<0`，plain B&B 沿曲面细分不收敛 ⇒ 需 disj 专用
   `--bbg --disj-gd` + stage-A manifest）。

**后续口径**：证书路线的成本判断**只认 `probe.status=closed` 的实测件**；静态档位只能用于排序报名，不能用于排期。

## E3（2026-11-06，M4 收尾）证书编译成本模型（实测拟合）+ stage-A 是第二遍全叶编译器

M4 试点三条 `probe.status=closed` 证书，得到可用于排期的**实测**成本模型。

### E3.1 编译成本

```
T(s) ≈ L × (0.032 + 8.0e-5 · ops)
olean(MB) ≈ L × (12–15 KB/叶)
```

`L` = 叶数（cert JSON 的 leaves），`ops` = cert JSON 的 `ops` 字段。

| 件 | L | ops | 公式预测 | 实测 |
|---|---:|---:|---:|---:|
| `8405387449` | 40,785 | 229 | 2,050 s | **2,050 s（34m10s）✓** |
| `4680581274 cayleytr` | 75,965 | 598 | 6,060 s | 停在 3,614 s（60m14s，528/891 shard）✓ |
| `4680581274 1x` | 133,228 | 223 | ~111 min | 未跑（未含 stage-A 与 sqrt/trans 加权，预计 150–200 min） |

**60 min 单件阈值**：`L ≤ 3600 / (0.032 + 8e-5·ops)` ⇒ `ops≈229` 时 ≤71.6k 叶，`ops≈598` 时 ≤45.1k 叶。

**结论**：已测 3 条里 **1 条在 60 min 内、2 条必须拆多轮**；其余 85 条**没有 probe 叶数**，
不能给确定条数 —— **必须先用 bb_arb 探一次拿 `L`/`ops`，再按上式分档**。
这与 E2 的「只认 probe-closed 实测件」是同一条口径的量化版。

### E3.2 stage-A 的真实成本（推翻「顺手回填」假设）

`sqrt`/`trans` 类目标必须先 `--fill --stage-a` 再 `--bbg --disj-gd`。
M4 在 `4680581274 1x` 上实测：

- 单文件 driver 模式跑 **16 min 无输出**（不可用）；
- data 模式（29 行 driver + 128 chunk + 133,228 行 boxes，生成 10.5s）跑 **14m16s**，
  得 **133,065 PASS / 163 叶 FAIL**（N=12…128 全部 163/133,228 失败）⇒ **params 不可用**。

**结论**：stage-A 不是「顺手回填的小工具」，它是**第二遍全叶编译器**，本身就有 15+ min 成本
且可能整批 FAIL（163 叶恒定失败 ⇒ 需要先定位这 163 叶的共性）。排期时必须单独计一项，
不能并进主编译预算。

### E3.3 M4 三条试点的最终状态

| # | 目标 | 状态 |
|---|---|---|
| 1 | `8405387449` | **闭环**，落库 `538f7e54`（500 文件 / 92,129 插入；`C8405387449_pos` 与 `t11_8405387449` 均标准三） |
| 2 | `4680581274 cayleytr` | **未闭环**，断点 528/891 shard / 526 MB olean；续跑命令在 `~/c17_backup/lane_snapshots/mnt11-rolling-M4/item2-.../DELIVERY.md` |
| 3 | `4680581274 1x` | **未开工**（stage-A 已实测，params 不可用；主编译预计 150–200 min） |

## E4（2026-11-06，`mnt11-census` 收尾）88 条 NEEDS-CERT 的普查结论：**不是排期表，是一张不可行域图**

普查产物：[`mnt11-census/CENSUS.md`](../mnt11-census/CENSUS.md) +
[`COST-MATRIX.tsv`](../mnt11-census/COST-MATRIX.tsv)（88 行 × 15 列）+
[`probe_index.tsv`](../mnt11-census/probe_index.tsv)（66 条探针原始索引）。

### E4.1 实测分布（不是估计）

| probe_status | 条数 | 含义 |
|---|---:|---|
| `closed` | **7** | 拿到叶数（M4 复用 3 + 新探 4） |
| `limit` | 9 | 2M 节点封顶（pending 9–37，`1834976363` 例外 609） |
| `timeout` | **53** | 180 s 墙钟内无收敛 |
| `no_case` | 19 | `emit_status=skip:recursion limit`，连 case 都发不出 |

⇒ **81/88 没有叶数**，成本公式对它们无定义。这不是「还没测」，是「这条路线测不出来」：
plain B&B 在 53 条上 180 s 不收敛，9 条卡在曲面/guard 边界叶（pending 不降），
19 条在 emitter 阶段就 `RecursionError`（提到 200k 仍立即复发 ⇒ 疑似定义展开成环，不是深度不足）。

### E4.2 能排的只有 6 条

A 档（单轮 ≤60 min）= **4**：`8405387449`(34.2 min, 40,785 叶) / `5557288534`(5.5 min, 4,264) /
`4821120729`(0.04 s, 1) / `6459846571`(23.2 min, 36,047)。
B 档（2–4 轮）= **2**：`4680581274 cayleytr`(101 min) / `4680581274 1x`(111 min)。
合计 **4.58 h 编译 + ≥1 h stage-A、olean 3.32–4.15 GiB**。
C 档 82 条里唯一 `closed` 的是 `5744538693`（**936,162 叶 / T_pred 11.55 h / 12 轮 / 10.7–13.4 GiB**），
单条即 A+B 的 2.5 倍 —— 已 7× 外推出 E3.1 公式的拟合域，不能当实测。

磁盘**不是**瓶颈：已知 7 条闭环合计 14.0–17.5 GiB = 249 GiB 的 5.6–7.0%，放大 10 倍仍 <180 GiB。

### E4.3 战略含义（比数字重要）

88 条 NEEDS-CERT 与 `mainNonlinearTerminalV11Ids_t11` 的 109 条**逐条对应**：
`109 = 20 PROVED + 1 PROVABLE + 88 NEEDS-CERT`（ids 集合实测相等，`TRIAGE.tsv` 110 行含表头）。
而 `nliMainNonlinearTerminalV11` 的陈述是 `∀ id ∈ 109, get_main_nonlinear id`
⇒ **该节点是 109/109 的全或无**。所以：

- 把 A 档 4 条做完，**锥内 `sorry` 计数一条都不减**（`t11_8405387449` 目前 grep 零消费者）；
  它只是为将来的一次性装配「存叶」。
- 在 82 条不可排期的情况下，`nliMainNonlinearTerminalV11` 与 `nliMainNonlinearTerminalV11Ids`
  两条 interface sorry **实际上被锁死**，不是「慢」，是「当前路线下无解」。

**处置建议（不改优先级，只改说法）**：证书农场不再是主线选项；要重启它，必须先做三件前置之一 ——
① 修 `emit_rpn.py` 的递归（19 条，纯 Python，最便宜）；② 给 9 条 limit 换 `--bbg --disj-gd` 路线；
③ 解释 53 条不收敛的共性（case 划分 / 区间宽度）。在此之前，主线仍走**按声明粒度可单条闭的**
`nliRest*` 43 条与 `nliTsk*` 7 条。
