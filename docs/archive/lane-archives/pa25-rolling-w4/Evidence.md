# Evidence — lane pa25-rolling-w4

所有读数均来自 `$S/logs/` 原始日志（`script -q` 输出，读前 `tr -d '\r'`）。

## E1. 基线整文件（继承字节验证）

```sh
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/baseline.log lean \
  /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean/Kepler/Text/PackingAuto25.lean
echo "RC=$?"
```
读数：**RC=0**；`grep -c ': error:' baseline.clean.log` = **0**；
`grep -c 'declaration uses `sorry`' baseline.clean.log` = **26**；
`wc -l` = **14,393**；`md5` = **ca2eaedb3d421951635dd07119dbde9e**。

## E2. 逐轮整文件复核（Work.lean，/tmp 工作副本）

| 轮次 | 日志 | RC | `: error:` | sorry 警告 |
|---|---|---|---|---|
| 基线 | `logs/baseline.clean.log` | 0 | 0 | 26 |
| W4-A `gamma4fgcy_POS` 后 | `logs/after_W4A.clean.log` | 0 | 0 | 25 |
| W4-B `cc_prep_model_data` 后 | `logs/after_W4B.clean.log` | 0 | 0 | 24 |
| W4-C `EDGE_IMP_K23` 后（+`#print axioms` 尾） | `logs/after_W4C_axioms.clean.log` | 0 | 0 | 23 |

终稿 `Work.lean`：**14,547 行**，`grep -n '^  sorry$' | wc -l` = **22**，
`grep -n ':= sorry'` = **1**（`:90` `ox3q1hP25`，冻结未动），
`md5 Work.lean` = **2fe12c2150f5aee916d5fd89efda08ca**。

## E3. `#print axioms`（终稿文件末 `end Kepler.Text` 之后追加，行 878–880 原文）

```sh
cat >> WorkAxioms.lean <<'EOF'

#print axioms Kepler.Text.gamma4fgcy_POS
#print axioms Kepler.Text.cc_prep_model_data
#print axioms Kepler.Text.EDGE_IMP_K23
EOF
```
日志原文（`tr -d '\r'` 后）：

```
'Kepler.Text.gamma4fgcy_POS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.cc_prep_model_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EDGE_IMP_K23' depends on axioms: [propext, Classical.choice, Quot.sound]
```

零 `sorryAx`。以上为日志逐字原文。

探针侧同样读数（`probe_A2.log` / `probe_B.log` / `probe_C.log`）：

```
'probe_gamma4fgcy_POS' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_cc_prep_model_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_EDGE_IMP_K23' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## E4. 陈述冻结

```sh
cd /tmp/pa25-rolling-w4 && python3 -I statement_cmp_w4.py
```
原文：

```
gamma4fgcy_POS: IDENTICAL
cc_prep_model_data: IDENTICAL
EDGE_IMP_K23: IDENTICAL
RESULT=PASS
```

## E5. Patch 校验（主仓只读，未 apply）

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git apply --check /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/patch-pa25-rolling-w4.diff
echo "apply-check RC=$?"
git apply --stat /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/patch-pa25-rolling-w4.diff
```
原文：

```
apply-check RC=0
 lean/Kepler/Text/PackingAuto25.lean | 160 +++++++++++++++++++++++++++++++++++-
 1 file changed, 157 insertions(+), 3 deletions(-)
```

hunk 边界：`grep -c '^@@'` = **3**；每个 hunk 只删 `-  sorry` 一行
（`grep -n '^-'` 除 diff 头 = 3）。工作期间 `git status --porcelain`（tracked）为空。

**HEAD 漂移复核**：本波期间并发车道把主仓 HEAD 从 `4ab6a8e7` 推到 `8c003d0d`；
`git diff --stat 4ab6a8e7..HEAD -- lean/Kepler/Text/PackingAuto25.lean` 输出为空，
两处 PA25 MD5 均 `ca2eaedb3d421951635dd07119dbde9e`。patch 在 `8c003d0d` 上重跑
`git apply --check` 仍 **RC=0**、`--stat` 仍只列该文件（见 `logs/final_checks.log`）。
另：`cone-text-triage-w1/` 的 4 个未跟踪文件属并发车道，非本车道产物，未触碰。

## E6. 地图搬债审计读数

```sh
for n in …; do grep -c "Kepler.Text.$n	" docs/e2e-reachability-map.tsv; done
```
本波新引用件全部 **0 行**（`proj_bank_GLFVCVK4`、`ztg4w1_quarter_norm2hh`、
`MCELL2_EDGE_FIRST`、`MCELL3_EDGE_FIRST`、`K4_CC_WI_ALT`、`K4_CC_WIM`、
`EDGE_IMP_K2`(=`BumpP4`)、`STEM_EDGEX`、`EL_CC_UH`、`cc_uh_exists`、
`BARV_3_EXPLICIT`、`CC_KE_34`、`LEAF_RANK_PERIODIC`、`LEAF_RANK_S_LEAF`、
`S_LEAF_SYM` …）；
唯一带地图行的是目标本身 `cc_prep_model_data` → 1（parent=`LEAF_RANK_PROPS`，锥内，已闭）。

## E7. 未触面声明

- `ox3q1hP25`（`:90` `def … : Prop := sorry`）：字节未动（diff 无此 hunk）。
- 全文件 diff 仅 3 hunk，无任何 `def`/statement 行改动；624 shard 面（K_AXIOM）
  与 import 闭包零漂移。
- 未新增 `import`；未新增 `open Classical`（含局部形式）。

## E8. 终稿 Work.lean 本身整文件复核（最终权威读数）

```sh
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q logs/final_WORK.log lean /Users/zhangzhuo/c17_backup/lane_snapshots/pa25-rolling-w4/Work.lean
echo "RC=$?"
tr -d '\r' < logs/final_WORK.clean.log | grep -c ': error:'
tr -d '\r' < logs/final_WORK.clean.log | grep -c 'declaration uses `sorry`'
```
读数：**RC=0**；`: error:` = **0**；sorry 警告 = **23**。
