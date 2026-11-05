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
