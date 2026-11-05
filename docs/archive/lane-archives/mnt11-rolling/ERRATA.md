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
