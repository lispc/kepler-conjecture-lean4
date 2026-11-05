# Evidence：pa22-yssksqoy-pillars-w1

所有命令均在 `/tmp/pa22-yssksqoy-pillars-w1/`（cwd）下执行；`$S=/Users/zhangzhuo/c17_backup/lane_snapshots/pa22-yssksqoy-pillars-w1`。

## 0. 编译命令（standalone，零 lake）

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
  nice -n 19 script -q $S/logs/<log> lean $S/Work.lean
```

- 基线：`$S/logs/baseline.log`（HEAD 原文件复制为 Work.lean 后编译）
- 最终：`$S/logs/work3.log`
- 读数来源：`tr -d '\r' < <log>`（日志含 CR，先剥离）

## 1. RC / 错误数 / sorry 声明数（N→M）

```
$ tr -d '\r' < $S/logs/baseline.log | grep -c 'error'
0
$ tr -d '\r' < $S/logs/work3.log | grep -c 'error'
0
$ tail -1 <stdout>            # wrapper 打印
RC=0                          # 基线
RC=0                          # 最终
```

声明级 `declaration uses `sorry`` 计数：

```
$ tr -d '\r' < $S/logs/baseline.log | grep -c 'declaration uses `sorry`'
16
$ tr -d '\r' < $S/logs/work3.log | grep -c 'declaration uses `sorry`'
14
```

裸 `sorry` 行计数（`grep -c '^\s*sorry\s*$'`）：

```
$ git show HEAD:lean/Kepler/Text/PackingAuto22.lean | grep -c '^\s*sorry\s*$'
15
$ grep -c '^\s*sorry\s*$' $S/Work.lean
13
```

基线 16 个 sorry 声明行号（NOTE: 1980 号是 `sorry -- DEF-FIX` 带行尾注释，故裸 `sorry` 为 15）：
`1980 2712 6669 12285 12512 12520 12559 13037 13045 13127 13397 13919 13930 13937 13944 14286`

最终 14 个 sorry 声明行号：
`1980 2712 6669 12727 12735 12774 13252 13260 13342 13612 14345 14352 14359 14701`

差分（本波消除）：`GOTCJAH`（基线 :12285）与 `YSSKQOY_VECTOR`（基线 :13919）。

## 2. `#print axioms` 原文（新 olean：`lean -o` 构建后 import）

构建：
```
$ cd /tmp/pa22-yssksqoy-pillars-w1/mod
$ LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
    nice -n 19 script -q $S/logs/olean3.log \
    lean -o Kepler/Text/PackingAuto22.olean Kepler/Text/PackingAuto22.lean
RC=0
```
（mod/ 是 `.lake/build/lib/lean` 的符号链接镜像 + 本波新 `PackingAuto22.olean`；LEAN_PATH 首位为 mod，用于 `#print axioms` 探针。）

探针输出原文（`$S/logs/probe_ax.log`）：

```
'Kepler.Text.YSSKQOY_VECTOR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GOTCJAH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.EXISTS_M_POLYHEDRON' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_edge_sum' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.facet_3_facets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FCHANGED_MEASURABLE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_FACET_SUM_4Pi' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.gotcjah_sol_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EUSOTYP2_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.gotcjah_prep' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GOTCJAH_convex_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SATURATE_BALL_ANNULUS' depends on axioms: [propext, Classical.choice, Quot.sound]
```

基线（旧 olean）同一命令读数：
```
'Kepler.Text.YSSKQOY_VECTOR' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## 3. 前置双验（体内新引用的每个前置）

新代码只引用：`acs`（本文件 def）、Mathlib 的 `Real.arccos_*` / `Real.hasDerivAt_arccos` / `Real.sqrt_*` / `Real.cos_pi_div_three` / `antitoneOn_of_deriv_nonpos` / `exists_deriv_eq_slope` 系列、以及本文件既有件 `ckq_in_ball_annulus`、`gotcjah_prep`、`EUSOTYP2_general`、`gotcjah_sol_lemma`、`GOTCJAH_convex_sum`、`ORDER_AZIM_SUM2Pi`、`WEDGE_ORDER_DISJOINT`、`SOL_SUBSET`、`FCHANGED_MEASURABLE`、`FCHANGED_RADIAL`、`azim_nonneg`、`azim_lt_two_pi`、`p22w4_radial_union`、`p22w4_sol_empty`、`p22w4_sol_disjoint_union`、`norm_sq_eq_dot`、`inner_eq_dot`。

- (a) `#check` 全部通过：`logs/probe10.log`（签名逐条打印，0 unknown identifier，除刻意探测的 `SOL_UNIONS`/`SOL_EMPTY` 等闭包外名字）。
- (b) `#print axioms`：上表；YSSKQOY_VECTOR/GOTCJAH 的支撑件全为标准三，上游 GIANT 三个的 sorryAx 已如实列出（它们不是本波新引入）。
- 说明：`SOL_UNIONS`（ConformingAuto5）、`arcLength`/`YSSKQOY`（PackingAuto18）**不在 PA22 import 闭包内**（`#check` unknown identifier，`logs/probe10.log`/`probe1.log`），故 GOTCJAH 的并集可加性改用文件内 `p22w4_sol_disjoint_union` 归纳；YSSKQOY_VECTOR 改走纯 arccos 直接证法。未新增 import、未造边。

## 4. kit 与陈述冻结

```
$ git -C <repo> apply --check --verbose $S/kit-pa22-yssksqoy-pillars-w1.diff
Checking patch lean/Kepler/Text/PackingAuto22.lean...
apply-check RC=0
```

kit 头：
```
diff --git a/lean/Kepler/Text/PackingAuto22.lean b/lean/Kepler/Text/PackingAuto22.lean
```

stat：`1 file changed, 417 insertions(+), 2 deletions(-)`；两处删除即两个 `  sorry` 行被替换。

陈述切片 `cmp`（Python 逐字比较 HEAD 与 Work 的 `theorem … := by` 前缀）：
```
YSSKQOY_VECTOR statement identical: True len 238
GOTCJAH statement identical: True len 482
ALL_IDENTICAL True
```

新增行禁用词审计：
```
$ grep -E '^\+' $S/kit-….diff | grep -nE 'sorry|admit|native_decide|open Classical|^\+import'
(无输出)
```

## 5. 目标文件状态

`git status --porcelain` 中 `lean/Kepler/Text/PackingAuto22.lean` **未出现在修改列表**（本波对主仓目标文件零写入；Work.lean 只在 `$S` 与 /tmp）。同仓其它 lane 的改动（`LocalAuto18/21`、`TameCorrBase`、`docs/archive/...pa25-rolling-w6` 等）与本车道无关，未触碰。
