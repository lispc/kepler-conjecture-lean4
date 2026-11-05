# Evidence — pa25-rolling-w6

## 1. 基线读数（HEAD `7cdf4570` 的 PA25，日志 `logs/baseline.log`）

```
$ md5 lean/Kepler/Text/PackingAuto25.lean
MD5 (...) = 4f6fa20d2c0887efbe435299a8af764b
$ wc -l
14868
$ LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
    script -q logs/baseline.log lean <repo>/lean/Kepler/Text/PackingAuto25.lean
RC=0
$ tr -d '\r' < logs/baseline.log | grep -c ': error:'                 -> 0
$ tr -d '\r' < logs/baseline.log | grep -c ': warning:'               -> 170
$ tr -d '\r' < logs/baseline.log | grep -c 'declaration uses `sorry`' -> 20
```

（19 裸 sorry + 冻结 `ox3q1hP25`；与 w5 WORKORDER-w6 的验收期望一致。）

## 2. 终稿读数（`Work.lean`，日志 `logs/w6c-full.log`）

```
$ LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
    script -q logs/w6c-full.log lean $S/Work.lean
RC=0
$ tr -d '\r' < logs/w6c-full.log | grep -c ': error:'                 -> 0
$ tr -d '\r' < logs/w6c-full.log | grep -c ': warning:'               -> 175
$ tr -d '\r' < logs/w6c-full.log | grep -c 'declaration uses `sorry`' -> 13
$ wc -l Work.lean
15417
$ md5 Work.lean
766b6b2a86f6aacce24190a14d9a6077
```

13 = `ox3q1hP25`（第 90 行，定义体逐字未动）+ **12 裸 sorry**。
own-sorry **19 → 12**（-7）。

## 3. `#print axioms` 原文（`axioms-probe-pa25-rolling-w6.lean`，`logs/w6-axioms.log`）

```
'Kepler.Text.MCELL3_008' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GAMMAX_008a' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GAMMAX_008b' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_008' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_cell23_008' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_gr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.real_model_sum_azim' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.Kepler.Text.p25w6_cell3_008_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.Kepler.Text.p25w6_undiv_gamma3_nn' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.Kepler.Text.p25w6_dihY_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.Kepler.Text.p25w6_order_azim_sum2pi0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

全部标准三，零 sorryAx。（axioms-probe 整文件亦 RC=0。）

## 4. 前置双验（新引用依赖面）

`logs/ax1.log`（`probe-ax.lean`，对 PA25 olean）：

```
'Kepler.Text.gammaX_gamma3f' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MCELL3_DIHX' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MCELL3_CRITICAL_WEIGHT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.cell3_from_ineq_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.mi_gamma3f_gamma3f_x_div_sqrtdelta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.mi_ETA_Y_BOUNDS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MCELL3_EDGE_FIRST' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LEAF_RANK_GRUTOTI' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GAMMAX_GAMMA2_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MCELL3_DOMAIN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#check` 全部在 PA25 闭包内（同一文件/导入模块，编译通过即证）。

## 5. 补丁与 `git apply`

```
$ git apply --check --verbose patch-pa25-rolling-w6.diff
Checking patch lean/Kepler/Text/PackingAuto25.lean...
APPLY-CHECK PASS
$ git apply --stat patch-pa25-rolling-w6.diff
 lean/Kepler/Text/PackingAuto25.lean |  563 +++++++++++++++++++++++++++++++++++
 1 file changed, 556 insertions(+), 7 deletions(-)
```

Hunk 头（只落本波 7 件 + 新桥区）：

```
@@ -9743,7 +9743,69 @@     （private ORDER 拷贝 + 新桥头）
@@ -9752,7 +9814,19 @@     （real_model_sum_azim 体）
@@ -13062,7 +13136,295 @@   （9 枚 p25w6_* 私件）
@@ -13070,7 +13432,76 @@    （MCELL3_008 体）
@@ -13088,7 +13519,51 @@    （real_model_008 体）
@@ -13217,7 +13692,40 @@    （real_model_cell23_008 体）
@@ -13229,7 +13737,21 @@    （GAMMAX_008a 体）
@@ -13241,7 +13763,27 @@    （GAMMAX_008b 体）
@@ -13289,7 +13831,14 @@    （real_model_gr 体）
```

## 6. 陈述冻结（逐字）

```
MCELL3_008 IDENTICAL
GAMMAX_008a IDENTICAL
GAMMAX_008b IDENTICAL
real_model_008 IDENTICAL
real_model_cell23_008 IDENTICAL
real_model_gr IDENTICAL
real_model_sum_azim IDENTICAL
```

（脚本对 HEAD 原文与 Work.lean 各取 `theorem <name> … ` 至 `:= by`
之前整段 `cmp`。）

`ox3q1hP25` 定义体：HEAD 第 90 行与 Work.lean 第 90 行均为
`def ox3q1hP25 : Prop := sorry`，逐字一致；624 shard 面不在 diff hunk 内。

## 7. 搬债审计（新增行 → 仍-sorry 声明）

对 patch 的 556 条 `+` 行逐个 grep 12 个残件名 + `ox3q1hP25`：

```
CELL_CLUSTER_ESTIMATE_REDUCE 0
CELL_CLUSTER_N_LE_1 0
pkLeafRankCriticalEdge 0
real_model_ox3q1h_merge 0
real_model_quqy 0
real_model_quqy_sym 0
real_model_gamma10 0
real_model_gamma11 0
real_model_pema 0
real_model_pemb 0
real_model_txq 0
real_model_tew 0
ox3q1hP25 0
```

零搬债。

## 8. 探针

- `probe1-w6a.lean`：W6-A 桥 + `probe_MCELL3_008` + 5 连闭 + sum_azim，
  独立模块（`import Kepler.Text.PackingAuto25`）RC=0，证明私件块可
  在 PA25 内编译（PA25 私有件在探针里以同体副本顶替）。
- `probe-mini.lean`：`setSum` 两侧展开需 `simp only [setSum, dif_pos hfin]`
  （`rw [setSum, setSum, dif_pos hfin]` 只展开一侧，是本次踩到的坑）。
- `probe-ax.lean`：依赖面公理读数（§4）。
