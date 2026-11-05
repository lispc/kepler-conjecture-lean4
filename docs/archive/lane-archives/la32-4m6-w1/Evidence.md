# Evidence — lane `la32-4m6-w1`（BLOCKED，0 闭合）

基线：简报指定 HEAD `8c003d0d`；本车道执行期间主仓 HEAD 被他车道推进到
`45c6d93c`（`80af154a` 发车 + `c831efac` PA25 + `45c6d93c` 对表）。
**目标文件未变**：

```sh
git diff --stat 8c003d0d 45c6d93c -- lean/Kepler/Text/LocalAuto32.lean   # 空输出
git show 8c003d0d:lean/Kepler/Text/LocalAuto32.lean | shasum -a 256
# 385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779
shasum -a 256 lean/Kepler/Text/LocalAuto32.lean
# 385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779
```

`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/la32-4m6-w1`。
所有读数由本车道 standalone 命令产出，日志在 `$S/logs/`。

## 1. 基线编译（`logs/baseline.log`）

命令原文：

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q /Users/zhangzhuo/c17_backup/lane_snapshots/la32-4m6-w1/logs/baseline.log \
  lean lean/Kepler/Text/LocalAuto32.lean
echo "RC=$?"
```

读数（命令原文 + 值）：

| 命令 | 读数 |
|---|---|
| `echo "RC=$?"`（上条命令后） | **RC=0** |
| `tr -d '\r' < $S/logs/baseline.log \| grep -c ': error:'` | **0** |
| ``tr -d '\r' < $S/logs/baseline.log \| grep -c 'declaration uses `sorry`'`` | **60** |
| `tr -d '\r' < $S/logs/baseline.log \| grep -c ': warning:'` | **81** |
| `wc -l lean/Kepler/Text/LocalAuto32.lean` | **1583** |

日志末三行（原文，去 `\r` 后）：

```
lean/Kepler/Text/LocalAuto32.lean:1562:8: warning: declaration uses `sorry`
lean/Kepler/Text/LocalAuto32.lean:1569:8: warning: declaration uses `sorry`
lean/Kepler/Text/LocalAuto32.lean:1576:8: warning: declaration uses `sorry`
```

## 2. 零漂移自证

```sh
git show HEAD:lean/Kepler/Text/LocalAuto32.lean > $S/Work.lean
shasum -a 256 $S/Work.lean lean/Kepler/Text/LocalAuto32.lean
```

两行均为 `385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779`；
`wc -l $S/Work.lean` = 1583。`git status --porcelain` = **0 行**。

## 3. 目标公理面（`logs/probe3.log`）

探针文件 `/tmp/la32-4m6-w1/probe3.lean`，命令：

```sh
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/probe3.log lean /tmp/la32-4m6-w1/probe3.lean
```

原文输出（`tr -d '\r'` 后）：

```
'Kepler.Text.EXTREMAL_SCS_4M6_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.BB_4M6_IMP_scs_4T3_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.MM_4M6_IMP_MM_4T3_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.NWDGKXH_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## 4. 前置/根公理面

### 4.1 实测含 `sorryAx`（`logs/probe1.log` / `probe2.log`）

```
'Kepler.Text.VASYYAU_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.TUAPYYU_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.PWEIWBZ_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T3_IS_SCS_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.VASYYAU_p25' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`VASYYAU_p25` 在 scope 内（`#check` 成功），但其体是 `VASYYAU_concl`（LA1:4913
`:= by sorry`）。这与分诊 `RANKED.md` 的"前置全绿"直接冲突。

### 4.2 实测标准三（`logs/probe2.log` / `probe4.log`）

```
'Kepler.Text.MMS_IMP_BBS_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BB_VV_FUN_EQ_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.STAB_MOD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YRTAFYH_p17' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_IS_SCS_p29' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_BASIC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.K_SCS_4M6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_STAND_OR_PRO_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.h0_LT_B_SCS_4M6_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_STAND_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.h0_CSTAB_LT_4_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T3_BASIC_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.K_SCS_4T3_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FZIOTEF_TRANS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FZIOTEF_UNION' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FZIOTEF_REFL' depends on axioms: [propext, Classical.choice, Quot.sound]
```

（`probe4.log` RC=0，无 error。）

## 5. 不可达性探针（`logs/probe3.log`）

`import Kepler.Text.LocalAuto32` 后，以下全名均为
`error(lean.unknownIdentifier): Unknown identifier`：

```
Kepler.Text.STAB_4M6_SCS_p33
Kepler.Text.SCS_4T5_IS_SCS_p33
Kepler.Text.MM_4M6_IMP_STAB_4M6_p33
Kepler.Text.quad_nonexist_849_p16
Kepler.Text.SET_STAB_4M6_ARROW_4T5_p33
Kepler.Text.isScs_mkFunlist_p33
```

即 LA33:3070 / 1492 / 4316 / 4298 与 LA16:799 的已证内容**不在** LA32 的 import 闭包；
零新 import 约束下不可引用。对照：`Kepler.Text.SCS_4M6_IS_SCS_p29`、
`SCS_4M6_BASIC`、`K_SCS_4M6` 的 `#check` 成功。

LA32 的 import 头（`LocalAuto32.lean:106-111`）：

```
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto17
import Kepler.Text.LocalAuto20
import Kepler.Text.LocalAuto23
import Kepler.Text.LocalAuto29
import Mathlib
```

## 6. 文件内缺席检查（grep）

| 命令 | 读数 |
|---|---|
| `grep -n "scs4T5\|SCS_4T5" lean/Kepler/Text/LocalAuto32.lean` | 仅 `1031:`（目标 `NWDGKXH_p32` 陈述本身） |
| `grep -n "STAB_4M6_SCS\|MM_4M6_IMP_STAB\|SET_STAB_4M6" lean/Kepler/Text/LocalAuto32.lean` | **0 行** |
| `grep -rn "theorem VASYYAU\|theorem TUAPYYU\|theorem PWEIWBZ" lean/Kepler/` | 仅 LA1 `_concl` + LA25 `_p25` 再导出 |
| `grep -rn "theorem SCS_4T5_IS_SCS" lean/Kepler/` | 仅 LA33:1492 |
| `grep -rn "theorem SET_STAB_4M6_ARROW_4T5\|theorem MM_4M6_IMP_STAB_4M6\|theorem STAB_4M6_SCS" lean/Kepler/` | 仅 LA33:4298 / 4316 / 3070 |

## 7. 根与目标行号（`awk`/`grep` 原文）

LA32 目标（同时是 `:= by` / `sorry` 行）：

```
993  theorem EXTREMAL_SCS_4M6_p32 :
997      dist (v 3) (v 0) = 2 ∧ dist (v 0) (v 1) = cstab := by
998    sorry
1003 theorem BB_4M6_IMP_scs_4T3_p32 :
1006     BBsV39 scs4T3 v := by
1007   sorry
1012 theorem MM_4M6_IMP_MM_4T3_p32 :
1015     MMsV39 scs4T3 ≠ ∅ := by
1016   sorry
1020 theorem SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 :
1024         s = scsStabDiagV39 scs4M6' i j}) := by
1025   sorry
1030 theorem NWDGKXH_p32 :
1031     main_nonlinear_terminal_v11 → scsArrowV39 {scs4M6'} {scs4T3, scs4T5} := by
1032   sorry
```

LA1 根（`awk 'NR>=4878 && NR<=4924'`）：

```
4880 theorem TUAPYYU_concl : ...
4889   sorry
4892 theorem WKZZEEH_concl : ...
4900   sorry
4903 theorem PWEIWBZ_concl : ...
4910   sorry
4913 theorem VASYYAU_concl : ...
4922   sorry
```

LA32 in-file 根：`247 theorem SCS_4T3_IS_SCS_p32 : isScsV39 scs4T3 := by` / `248 sorry`。

## 8. 搬债审计（`docs/e2e-reachability-map.tsv`）

```
grep -c "EXTREMAL_SCS_4M6_p32"                        → 0
grep -c "BB_4M6_IMP_scs_4T3_p32"                      → 0
grep -c "MM_4M6_IMP_MM_4T3_p32"                       → 0
grep -c "SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32"          → 0
grep -c "NWDGKXH_p32"                                 → 1
grep -c "VASYYAU" / "PWEIWBZ" / "TUAPYYU"             → 0 / 0 / 0
grep -c "SCS_4T3_IS_SCS_p32"                          → 0
```

`NWDGKXH_p32` 的唯一行：

```
100:Kepler.Text.LocalAuto32	Kepler.Text.NWDGKXH_p32	parent=Kepler.Text.NWDGKXH_discharged
```

本车道零编辑，未新增任何体内引用，故无搬债。

## 9. 结论

- 五件目标自身体均为 `sorry`，基线公理面均含 `sorryAx`。
- `EXTREMAL_SCS_4M6_p32` 的 HOL 证明体显式消费 `PWEIWBZ`/`VASYYAU`/`TUAPYYU`/
  `quad_nonexist_849`；前三者是 LA1 `:= by sorry`（实测 `sorryAx`），后者不在闭包。
- 其余四件经 `EXTREMAL_SCS_4M6_p32`、in-file `SCS_4T3_IS_SCS_p32`（`sorry`）、
  以及仅 LA33 的 `MM_4M6_IMP_STAB_4M6` / `SET_STAB_4M6_ARROW_4T5` / `SCS_4T5_IS_SCS`
  传递阻塞。本波无可行闭合路径（零新 import、零 sorry、目标文件唯一可动）。
