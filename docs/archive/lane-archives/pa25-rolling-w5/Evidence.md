# Evidence — pa25-rolling-w5

## 1. 公理面（`#print axioms` 原文）

取证方式：`axioms-probe-pa25-rolling-w5.lean` = `Work.lean` + 末尾 4 条 `#print axioms`，
standalone 编译（RC=0 / 0 error），日志 `logs/w5-axioms.log`。

```
'Kepler.Text.real_model_gamma8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gamma8b' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gckb' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.Kepler.Text.p25w5_QITNPEA_9063653052' depends on axioms: [propext, Classical.choice, Quot.sound]
```

四件均 = 标准三公理，**零 `sorryAx`**。`K-AXIOM` 护栏：无新增公理（新件全是
`private theorem`，无 `axiom` 声明）。

## 2. 整文件 RC / 错误数 / sorry 声明计数 N→M

命令（基线，HEAD 文件）：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q logs/base-full.log lean <repo>/lean/Kepler/Text/PackingAuto25.lean
```

| 指标 | 基线（HEAD） | 终稿（Work.lean） |
|---|---|---|
| `script` RC | 0 | 0 |
| `grep -c ': error:'` | 0 | 0 |
| `grep -c ': warning:'` | 173 | 170 |
| `grep -c 'declaration uses \`sorry\`'` | **23** | **20** |
| 其中裸 sorry | 22 | **19** |
| 其中冻结 `ox3q1hP25` 定义体 | 1 | 1 |
| `wc -l` | 14547 | 14868 |
| `md5` | 2fe12c2150f5aee916d5fd89efda08ca | 4f6fa20d2c0887efbe435299a8af764b |

警告谱面（非 sorry 部分）**逐条一致**：基线 150 条、终稿 150 条，
`collections.Counter` 相等（脚本比对，无 DIFF 行）。即本波未引入任何新 linter 警告
（`hnl`/`hsize`/`h0`/`h1`/`hper`/`hcey` 等 unusedVariables 警告全部为 HEAD 既有）。

## 3. 消失的 3 条 sorry 警告（逐条核对）

终稿仍-sorry 的 20 个声明名（行号取终稿）：

```
90 ox3q1hP25            6150 CELL_CLUSTER_ESTIMATE_REDUCE   6498 CELL_CLUSTER_N_LE_1
9749 real_model_sum_azim  9795 pkLeafRankCriticalEdge       9856 real_model_ox3q1h_merge
10494 real_model_quqy    10510 real_model_quqy_sym         12110 real_model_gamma10
12130 real_model_gamma11 13067 MCELL3_008                  13077 real_model_008
13206 real_model_cell23_008 13223 GAMMAX_008a              13235 GAMMAX_008b
13285 real_model_gr      13325 real_model_pema             13337 real_model_pemb
14011 real_model_txq     14023 real_model_tew
```

基线同一脚本跑出 23 个名字；差集 = `{real_model_gamma8, real_model_gamma8b,
real_model_gckb}`，无它。

## 4. 陈述冻结复核

脚本：从 `git show HEAD:lean/Kepler/Text/PackingAuto25.lean` 与 `Work.lean` 分别切出
`theorem <name> …` 到首个 `:= by` 之前的整段，去尾空白后逐字比较：

```
real_model_gamma8  STMT IDENTICAL
real_model_gamma8b STMT IDENTICAL
real_model_gckb    STMT IDENTICAL
```

声明清单差集（`^(theorem|private theorem|def|noncomputable def)` 全文件扫描）：
新增 8 个 `private theorem`（`p25w5_*`），删除 0 个。

## 5. 补丁与 `git apply`

```
$ git diff --no-index a b  (a=HEAD 树, b=Work 树) > patch-pa25-rolling-w5.diff
$ git -C <repo> apply --stat patch-pa25-rolling-w5.diff
 lean/Kepler/Text/PackingAuto25.lean |  327 +++++++++++++++++++++++++++++++++++
 1 file changed, 324 insertions(+), 3 deletions(-)
$ git -C <repo> apply --check patch-pa25-rolling-w5.diff
PASS
```

补丁头（逐字）：`diff --git a/lean/Kepler/Text/PackingAuto25.lean b/lean/Kepler/Text/PackingAuto25.lean`；
`git apply --stat` 只显示仓内路径（上）。

## 6. 雷区实测补记（供 w6）

1. `criticalEdgeY` 是 `Prop`，本体文件头的 `open … Classical` 是 HEAD 遗留；新内核件
   若在**陈述**里写 `if criticalEdgeY _` 会在无 `open Classical` 时报
   `synthInstanceFailed: Decidable`。解法：证明体首行 `classical`（tactic 形式，
   不触发 `open Classical` 禁令），`have` 的类型随后即可取到局部 `propDecidable`。
2. `leaf_CIHTIUM` 的实参是 (V, u0, u1, u2, hnl, hp, hs, leaf, hcey, 2hmin≤d02, 2hmin≤d12)；
   在 `¬(d03 小 ∧ d13 小)` 上要**先 `by_contra` 取反**（`not_lt.mp` 得 `2hmin ≤ d`，
   `not_le.mp` 得 `d < 2hmin`），方向搞反是本轮唯一一次返工。
3. `MCELL4_DOMAIN` 的上界是 `dist … < 2 * Real.sqrt 2`，银行要 `≤ Real.sqrt 8`：
   统一用 `le_trans (le_of_lt h) (le_of_eq mi_sqrt8_eq.symm)`。
4. `CC_3_PROPS` 是 33 元合取（前 17 项含 3 个 `leaf`、3 个 `hl`，18–22 是五个
   `2 ≤ dist`，23–27 是五个 `dist ≤ 2√2`，32 是 `azim_mcell = azim`，33 是
   `∃ y4, 2 ≤ y4 ∧ y4 ≤ 2√2 ∧ 0 < deltaY ∧ dihY…y4 ≤ azim ∧ 2 ≤ rad2 ∧ (… → y4 = d23)`）；
   逐位对齐 `obtain` 模式时数错一位不报错（同型命题），但语义全错——务必按位点数。
5. `bank_QITNPEA1tmpl` 只有 `i3 ∈ {1,2}`（y3 箱从 `2hmin` 起），**没有** `i3 = 0`：
   `QITNPEA1_9063653052` 的 y3 箱是 `[2hmin, √8]`，所以搬 `gamma8` 时必须先用
   `leaf_CIHTIUM` 把 `f(i+1)` 侧唯一非小边顶到 y3 槽。
