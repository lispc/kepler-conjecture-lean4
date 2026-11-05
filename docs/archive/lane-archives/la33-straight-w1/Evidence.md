# Evidence — la33-straight-w1

原始日志在 `$S/logs/`。所有读数均可用下方命令逐字复核。

## 1. 整文件编译（standalone）

命令（基线用 HEAD 拷贝 `Work.lean`，终版用剥探针尾后的 `Work.lean`）：

```
cd /tmp/la33-straight-w1
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q /Users/zhangzhuo/c17_backup/lane_snapshots/la33-straight-w1/logs/<log> lean /Users/zhangzhuo/c17_backup/lane_snapshots/la33-straight-w1/Work.lean
tr -d '\r' < /Users/zhangzhuo/c17_backup/lane_snapshots/la33-straight-w1/logs/<log> > /tmp/la33-straight-w1/<log>_clean.log
grep -c ': error:' /tmp/la33-straight-w1/<log>_clean.log
grep -c 'declaration uses `sorry`' /tmp/la33-straight-w1/<log>_clean.log
```

| 轮次 | 日志 | `: error:` 数 | sorry 声明数 | RC |
|------|------|-----------|-------------------------------|----|
| 基线（HEAD 原文件） | `logs/base.log` | **0** | **11** | 0 |
| 终版（两件闭合 + header 注记） | `logs/final.log` | **0** | **9** | **0** |

`Work.lean` 与 `final.log` 的编译对象逐字节一致（header 注记加入后重编，见
`logs/final.log`）；探针尾（`#print axioms` 三行）只在 `logs/axprobe.log` / `logs/axprobe2.log` 两轮出现
（后者跑在临时拷贝 `Work-ax.lean` 上，已删除），`Work.lean` 本身无探针尾
（`grep -c 'print axioms' Work.lean` = 0）。

## 2. 目标公理面（`logs/axprobe2.log` 原文 = 终版逐字内容实测；`logs/axprobe.log` 为同内容的先行探针）

```
'Kepler.Text.SCS_4I2_STRAIGHT_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_STRAIGHT_ALL_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MM_4I2_IMP_4T2_4T1_p33' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

- `SCS_4I2_STRAIGHT_p33` / `SCS_4I2_STRAIGHT_ALL_p33`：**标准三**。
- `MM_4I2_IMP_4T2_4T1_p33`：仍 `sorryAx`（本波 BLOCKED，保留原 `:= sorry`）。

## 3. 前置 `#print axioms`（`logs/p2.log` 原文，32 条）

```
^D'Kepler.Text.MMs_imp_BBs_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EDGE_4I2_LE_2H0_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_DIAG_4_ADD0_p33' depends on axioms: [propext, Quot.sound]
'Kepler.Text.SCS_DIAG_4_ADD2_p33' depends on axioms: [propext, Quot.sound]
'Kepler.Text.SCS_DIAG_ADD1_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DIST_DIAG_2_CASES_EQ_3_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.ASSUME_MIN_DIAG_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BBS_IMP_CONVEX_LOCAL_FAN_p34' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.IN_V_IMP_AZIM_LESS_PI' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.sum3_azim_fan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_GENERIC_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.ballAnnulus_norm_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.ear_acute_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DIHV_EQ_DIH_Y_4PT_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_dihv_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_dihv_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DIHV_SYM_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BB_VV_FUN_EQ_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BB_RHO_NODE_IVS_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Geom.azim_lt_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T2_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T1_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_BASIC_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T1_BASIC_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T2_BASIC_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4I2_3_LE_A_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.WL_IN_BALL_ANNULUS_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.NORM_LE_2_IN_BBS_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.MMS_IMP_BBS_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
```

全部 = `[propext, Classical.choice, Quot.sound]`；`XWNHLMD_MM_p33` 的文件内
docstring 所称 “sorryAx standing” 已被实测推翻（现为 standard three）。
`#check` 探针（`logs/p1.log`）证明上列全部在 `LocalAuto33` 的 import 闭包内。

## 4. 签名冻结 / 卫生

Python 逐字比较 HEAD 与 `Work.lean` 的“`theorem <name>` 至 `:=` 前缀”：

```
SCS_4I2_STRAIGHT_p33 SIGNATURE-FROZEN: True
SCS_4I2_STRAIGHT_ALL_p33 SIGNATURE-FROZEN: True
MM_4I2_IMP_4T2_4T1_p33 SIGNATURE-FROZEN: True
```

kit 新增行（`+` 且非 `+++`）扫描：

```
added contains 'sorry' : False
added contains 'admit' : False
added contains 'native_decide' : False
added contains 'open Classical' : False
added contains 'import ' : False
```

`grep -c 'sorry'`：HEAD 37（含注释/字符）→ `Work.lean` 35（两处 `:= sorry` 体消失）。

## 5. kit 与落库

```
$ git -C /Users/zhangzhuo/repos/kepler-conjecture-lean4 apply --check $S/kit-la33-straight-w1.diff
(exit 0)   # APPLY-CHECK PASS

$ git apply --stat $S/kit-la33-straight-w1.diff
lean/Kepler/Text/LocalAuto33.lean |  336 ++++++++++++++++++++++++++++++++++++-
 1 file changed, 330 insertions(+), 6 deletions(-)
```

kit 头：`diff --git a/lean/Kepler/Text/LocalAuto33.lean b/lean/Kepler/Text/LocalAuto33.lean`；
`--stat` 仅显示仓内路径 `lean/Kepler/Text/LocalAuto33.lean`。

环境：开工 HEAD `8c003d0d`；收尾主仓 HEAD `8635c297`（其它车道推进）。
`diff` 实测两 HEAD 之间 `lean/Kepler/Text/LocalAuto33.lean` 内容未变，kit 对当前工作树仍 PASS。

## 6. 复现要点（探针命令）

```
# 接口形（logs/p1.log）
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) lean p1.lean
# 公理面（logs/p2.log）
... lean p2.lean
# 影子证明（logs/sh1.log；最终文本已逐字搬入目标文件，仅改名）
... lean sh1.lean
```
