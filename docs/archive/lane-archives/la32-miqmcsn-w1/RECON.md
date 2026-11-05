# RECON — lane `la32-miqmcsn-w1`（LA32 / Flyspeck `MIQMCSN.hl` 装配波 1）

**基线**：主仓 `b89ee8b4`（`git rev-parse HEAD`），工作树干净（`git status --porcelain` 输出 0 行）。
`lean/Kepler/Text/LocalAuto32.lean` = 1583 行，sha256
`385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779`（与 `$S/Work.lean` 逐字节相同）。
**HOL 源**：`lean/scripts/local/MIQMCSN.hl`（3469 行）。
**方法**：逐个 `grep -n 'theorem <NAME>'` + 读声明体判 `:= by …` / `:= by sorry`；
in-file 名字引用闭包用 token 边界脚本扫描；`#print axioms` 用 standalone 探针（`logs/probe_*.log`，全名 `Kepler.Text.<name>`）。

## 0. 结论（一句话）

**三条目标全部 BLOCKED，本波闭合 0 件。** 每条目标在 HOL 里的装配所依赖的 in-file 中间箭头，
在 HEAD 上仍是 `:= by sorry`；按简报 §1 与 AGENTS §2，不得在其上做结构闭合（搬债）。
三条目标自身公理面实测均含 `sorryAx`。

## 1. 基线读数

| 指标 | 命令原文 | 读数 |
|---|---|---|
| 编译返回码 | `LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 script -q logs/baseline.log lean lean/Kepler/Text/LocalAuto32.lean` | **RC=0** |
| 错误数 | `tr -d '\r' < logs/baseline.log \| grep -c ': error:'` | **0** |
| sorry 声明数 | ``tr -d '\r' < logs/baseline.log \| grep -c 'declaration uses `sorry`'`` | **60** |
| warning 总数 | `tr -d '\r' < logs/baseline.log \| grep -c ': warning:'` | 81 |
| 文件行数 | `wc -l lean/Kepler/Text/LocalAuto32.lean` | 1583 |
| own-sorry（按声明计） | 脚本：逐声明取体，去 `--` 注释后含裸 `sorry` 计数 | **60**（与简报一致） |

三目标基线公理面（`logs/probe_axioms.log` 原文）：

```
'Kepler.Text.NWDGKXH_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YOBIMPP_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.MIQMCSN_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## 2. 目标 1 `NWDGKXH_p32` 依赖树

```
NWDGKXH_p32                                   LA32:1030  `:= by` :1031  sorry :1032
  HOL MIQMCSN.hl:2110-2129 (20 ln)                                           [目标]
  |
  +-- SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32      LA32:1020  `:= by` :1024  sorry :1025
  |     HOL MIQMCSN.hl:2048-2109 (62 ln)                                     [SORRY]
  |     |
  |     +-- EXTREMAL_SCS_4M6_p32              LA32:993   `:= by` :997   sorry :998
  |     |     HOL MIQMCSN.hl:1855-1991 (137 ln)                              [SORRY]
  |     |     |
  |     |     +-- SCS_4M6_STAND_OR_PRO_p32    LA32:960                       [PROVEN, clean]  <== 第一个已证节点
  |     |     +-- MMS_IMP_BBS_p28             LA28:194                       [PROVEN, clean, 经 LA29 传递 import]
  |     |     +-- BB_VV_FUN_EQ_p26            LA26:198                       [PROVEN, clean, 经 LA29 传递 import]
  |     |     +-- VASYYAU_concl               LA1:4913  `:= by` :4921  sorry :4922
  |     |                                                                   [根 SORRY]
  |     +-- STAB_MOD                          LA20:1655                      [PROVEN, clean]
  |     +-- YRTAFYH_concl                     LA1:4998                       [PROVEN, clean]
  |     +-- isScsV39 scs4T3  (S2 首合取)  ->  SCS_4T3_IS_SCS_p32  LA32:247  sorry :248
  |                                                                          [SORRY, 无干净孪生]
  |
  +-- isScsV39 scs4T5 (S2 首合取)             LA32 内无此声明
  |     干净孪生 LA33:1492 SCS_4T5_IS_SCS_p33                               [缺席 / 可移植]
  |
  +-- SET_STAB_4M6_ARROW_4T5                  LA32 内无此声明（HOL :2123 显式引用）
        干净孪生 LA33:4298 SET_STAB_4M6_ARROW_4T5_p33                        [缺席 / 可移植]
```

逐跳（根链，全部按 HOL 行段核对）：

1. `NWDGKXH_p32`（HOL 2110-2129）以 `MATCH_MP_TAC FZIOTEF_TRANS` 取中间集
   `{scs_4T3} ∪ {scs_stab_diag_v39 scs_4M6' i j | scs_diag 4 i j}`（:2113-2114）。
2. 第一段由 `ASM_SIMP_TAC[SCS_4M6_ARROW_SCS_4T3_STAB_4M6]` 供给（:2115）——
   即 LA32:1020，本文件内 `sorry`。
3. 第二段 `MATCH_MP_TAC FZIOTEF_UNION`，左支 `FZIOTEF_REFL` + `SCS_4T3_IS_SCS`（:2118-2126），
   右支 `SET_STAB_4M6_ARROW_4T5`（:2118）。`SCS_4T3_IS_SCS` 在本文件是 LA32:247 `sorry`；
   `SET_STAB_4M6_ARROW_4T5` 在本文件根本不存在。
4. `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`（HOL 2048-2109）在斜对角分支用 `EXTREMAL_SCS_4M6`，
   稳定分支用 `STAB_MOD`/`YRTAFYH`。
5. `EXTREMAL_SCS_4M6_p32`（HOL 1855-1991）的 `str` 分支落到 `VASYYAU`（HOL 原文
   `MRESAS_TAC VASYYAU`），对应 `VASYYAU_concl`（LA1:4913，`sorry` :4922）——**本树根节点**。

## 3. 目标 2 `YOBIMPP_p32` 依赖树

```
YOBIMPP_p32                                   LA32:1241  `:= by` :1243  sorry :1244
  HOL MIQMCSN.hl:2453-2490 (38 ln)                                           [目标]
  |
  +-- SCS_4M7_ARROW_STAB_4M7_4M6_p32          LA32:1162  `:= by` :1166  sorry :1167
  |     HOL MIQMCSN.hl:2361-2442 (82 ln)                                     [SORRY]
  |     NEEDS: BB/MM_4M7_IMP_* twins + STAB_MOD/YRTAFYH
  |     |
  |     +-- MIN_NOT_STAND_4M7_p32             LA32:1118  sorry :1122         [SORRY]
  |     |     +-- SCS_4M7_STAND_OR_PRO_p32    LA32:1096                      [PROVEN, clean] <== 第一个已证节点
  |     |     +-- MMS_IMP_BBS_p28 / BB_VV_FUN_EQ_p26                        [PROVEN, clean]
  |     |     +-- VASYYAU_concl               LA1:4913  sorry :4922          [根 SORRY]
  |     +-- BB_4M7_IMP_4M6_12_p32             LA32:1127  sorry :1131         [SORRY]
  |     +-- MM_4M7_IMP_MM_4M6_12_p32          LA32:1135  sorry :1139         [SORRY]
  |     +-- BB_4M7_IMP_4M6_01_p32             LA32:1143  sorry :1148         [SORRY]
  |     +-- MM_4M7_IMP_MM_4M6_01_p32          LA32:1153  sorry :1158         [SORRY]
  |     +-- MM_4M7_IMP_STAB_4M7_p32           LA32:510   sorry :514          [SORRY]
  |     +-- STAB_MOD / YRTAFYH_concl                                        [PROVEN, clean]
  |     +-- isScsV39 scs4M7 -> SCS_4M7_IS_SCS_p29 LA29:1350                  [PROVEN, clean]
  |
  +-- STAB_SCS_4M7_ARROW_3T3_3M1_3T4_p32      LA32:680   `:= by` :682  sorry :683
  |     HOL MIQMCSN.hl:1484-1496 (13 ln)                                     [SORRY]
  |     |
  |     +-- SET_EQ_DIAG_STAB_4M7_p32          LA32:597                       [PROVEN, clean] <== 第一个已证节点
  |     +-- FZIOTEF_UNION                     LA20:1379                      [PROVEN, clean]
  |     +-- SCS_4M7_SLICE_13_ARROW_3T4_p32     LA32:657   sorry :659
  |     |     HOL MIQMCSN.hl:1308-1325 (18 ln)                               [SORRY]
  |     |     |
  |     |     +-- SCS_4M7_SLICE_13_p32         LA32:649   sorry :652
  |     |     |     HOL MIQMCSN.hl:1182-1307 (126 ln)                        [SORRY]
  |     |     |     +-- LKGRQUI_concl          LA1:2884  sorry :2888          [根 SORRY]
  |     |     |     +-- SCS_DIAG_SCS_4M7_13    LA32 无声明；LA33:3143 `_p33` [PROVEN clean, 缺席]
  |     |     |     +-- STAB_4M7_SCS           LA32 无声明；LA33:3077 `_p33` [PROVEN clean, 缺席]
  |     |     +-- SCS_3T4_prime2_ARROW_MM_3T4_p32  LA32:388  sorry :390
  |     |     |     HOL MIQMCSN.hl:943-972 (30 ln)                           [SORRY]
  |     |     |     +-- SCS_4T3_IS_SCS_p32     LA32:247  sorry :248          [SORRY, 无干净孪生]
  |     |     |     +-- XWNHLMD_MM_p26         LA26:1642                     [PROVEN, clean]
  |     |     +-- PRO_EQU_ID1 (LA12:1010) / YXIONXL3 (LA12:1224)             [PROVEN clean, 不在 import 闭包]
  |     |
  |     +-- SCS_4M7_SLICE_02_ARROW_3T3_3M1_p32 LA32:673   sorry :675
  |           HOL MIQMCSN.hl:1454-1483 (30 ln)                               [SORRY]
  |           |
  |           +-- SCS_4M7_SLICE_02_p32         LA32:665   sorry :668
  |           |     HOL MIQMCSN.hl:1326-1453 (128 ln)                        [SORRY]
  |           |     +-- LKGRQUI_concl          LA1:2884  sorry :2888          [根 SORRY]
  |           |     +-- SCS_DIAG_SCS_4M7_02    LA33:3139 `_p33`               [PROVEN clean, 缺席]
  |           |     +-- STAB_4M7_SCS           LA33:3077 `_p33`               [PROVEN clean, 缺席]
  |           +-- SCS_3T3_prime_ARROW_MM_3T3_p32  LA32:408  sorry :410       [SORRY]
  |           +-- SCS_3M1_prime_ARROW_MM_3M1_p32  LA32:428  sorry :430       [SORRY]
  |           +-- PRO_EQU_ID1                  LA12:1010                     [PROVEN clean, 缺席]
  |
  +-- 外部 opp/perm 套件（HOL :2457-2489 显式；Lean NEEDS 注释指名）
        +-- YXIONXL2_concl                     LA1:2578  sorry :2580          [根 SORRY]
        +-- YXIONXL3_concl                     LA1:2876  sorry :2878          [根 SORRY]
        +-- SCS_OPP_REFL                       LA32 无声明；FanBaseKit:3135 `SCS_OPP_REFL_fb` [PROVEN clean, 缺席]
        +-- PRO_EQU_ID1                        LA12:1010                      [PROVEN clean, 缺席]
        +-- OPP_IS_SCS                         LA33 `OPP_IS_SCS_p33`          [PROVEN clean, 缺席]
        +-- isScsV39 scs3T3                    LA22:2324 `is_scs_3T3_p22` 带 sorryAx；
                                               LA33:1617 `SCS_3T3_IS_SCS_p33` clean 但缺席
                                                                              [根 缺口]
```

逐跳（HOL :2453-2490）：

1. `FZIOTEF_TRANS` 取中间集
   `{scs_4M6', scs_prop_equ_v39 (scs_opp_v39 scs_4M6') 1} ∪ {scs_stab_diag_v39 scs_4M7 i j | …}`（:2457-2458）。
2. 第一段 `SCS_4M7_ARROW_STAB_4M7_4M6`（:2459）——LA32:1162 `sorry`。
3. 第二段拆 `FZIOTEF_UNION`：stab 集由 `STAB_SCS_4M7_ARROW_3T3_3M1_3T4`（:2461）——
   LA32:680 `sorry`；`{scs_4M6'}` 由 `FZIOTEF_REFL` + `SCS_4M6_IS_SCS`（:2467-2470，已证）；
   末支 `{scs_prop_equ_v39 (scs_opp_v39 scs_4M6') 1}` 经 `PRO_EQU_ID1`（:2474）+
   `YXIONXL3`（:2475）坍缩到 `{scs_opp_v39 scs_4M6'}`，再 `YXIONXL2` / `SCS_OPP_REFL`（:2485-2489）。
4. `SCS_4M7_ARROW_STAB_4M7_4M6` 内部经 `MIN_NOT_STAND_4M7`（LA32:1118 `sorry`）落到
   `VASYYAU`（根）；stab 分支经 `YRTAFYH`（已证）。
5. 两条 SLICE 链的公共根是 `LKGRQUI_concl`（LA1:2884 `sorry`）。

## 4. 目标 3 `MIQMCSN_p32` 依赖树

```
MIQMCSN_p32                                   LA32:1576  `:= by` :1578  sorry :1579
  HOL MIQMCSN.hl:3436-3470 (35 ln)                                           [目标]
  |
  +-- SCS_4M8_ARROW_STEP_ONE_p32              LA32:1419  `:= by` :1423  sorry :1424
  |     HOL MIQMCSN.hl:2874-3015 (142 ln)                                    [SORRY]
  |     +-- MIN_NOT_STAND_4M8_p32             LA32:1366  sorry :1372         [SORRY]
  |     |     +-- SCS_4M8_STAND_OR_PRO_p32    LA32:1342                      [PROVEN, clean] <== 第一个已证节点
  |     |     +-- SCS_4M8_STAND_p32           LA32:1358                      [PROVEN, clean]
  |     |     +-- VASYYAU_concl               LA1:4913  sorry :4922          [根 SORRY]
  |     +-- BB_4M8_IMP_4M6_23_p32             LA32:1252  sorry :1256         [SORRY]
  |     +-- MM_4M8_IMP_MM_4M6_23_p32          LA32:1261  sorry :1265         [SORRY]
  |     +-- BB_4M8_IMP_4M6_01_p32             LA32:1269  sorry :1273         [SORRY]
  |     +-- MM_4M8_IMP_MM_4M6_01_p32          LA32:1278  sorry :1282         [SORRY]
  |     +-- BB_4M8_IMP_scs_4M8_02_p32         LA32:1377  sorry :1383         [SORRY]
  |     +-- MM_4M8_IMP_MM_4M8_02_p32          LA32:1388  sorry :1394         [SORRY]
  |     +-- BB_4M8_IMP_scs_4M8_13_p32         LA32:1398  sorry :1404         [SORRY]
  |     +-- MM_4M8_IMP_MM_4M8_13_p32          LA32:1409  sorry :1415         [SORRY]
  |     +-- MM_4M8_IMP_STAB_4M8_p32           LA32:697   sorry :701          [SORRY]
  |     +-- STAB_MOD / YRTAFYH_concl                                        [PROVEN, clean]
  |     +-- isScsV39 scs4M8 -> SCS_4M8_IS_SCS_p29 LA29:1462                  [PROVEN, clean]
  |
  +-- SET_STAB_4M8_ARROW_3T4_p32              LA32:896   `:= by` :898  sorry :899
  |     HOL MIQMCSN.hl:1799-1811 (13 ln)                                     [SORRY]
  |     +-- SET_EQ_DIAG_STAB_4M8_p32          LA32:760                       [PROVEN, clean] <== 第一个已证节点
  |     +-- FZIOTEF_UNION                     LA20:1379                      [PROVEN, clean]
  |     +-- SCS_4M8_SLICE_13_ARROW_3T4_p32     LA32:882   sorry :884
  |     |     HOL MIQMCSN.hl:1784-1791 (8 ln)                                [SORRY]
  |     |     +-- SCS_4M8_SLICE_13_p32         LA32:875   sorry :877
  |     |     |     HOL MIQMCSN.hl:1655-1783 (129 ln)                        [SORRY]
  |     |     |     +-- LKGRQUI_concl          LA1:2884  sorry :2888          [根 SORRY]
  |     |     |     +-- SCS_DIAG_SCS_4M8_13    LA33 `_p33`                    [PROVEN clean, 缺席]
  |     |     |     +-- STAB_4M8_SCS           LA33:3084 `_p33`               [PROVEN clean, 缺席]
  |     |     +-- SCS_3T4_prime2_ARROW_MM_3T4_p32  LA32:388  sorry :390       [SORRY]
  |     +-- SCS_4M8_SLICE_02_ARROW_3T4_p32     LA32:889   sorry :891
  |           HOL MIQMCSN.hl:1792-1798 (7 ln)                                [SORRY]
  |           +-- STAB_4M8_02_ARROW_4M8_13_p32 LA32:868   sorry :870
  |           |     HOL MIQMCSN.hl:1637-1654 (18 ln)                         [SORRY]
  |           |     +-- PROP_OPP_DIAG_4M8_13_p32  LA32:823                    [PROVEN, clean]
  |           |     +-- YXIONXL2/YXIONXL3/OPP_IS_SCS                        [外部，见根表]
  |           +-- SCS_4M8_SLICE_13_ARROW_3T4_p32  (同上)                      [SORRY]
  |
  +-- SCS_4M8_02_ARROW_3T7_p32                LA32:1569  `:= by` :1570  sorry :1571
        HOL MIQMCSN.hl:3428-3435 (8 ln)                                      [SORRY]
        +-- SCS_4M8_02_ARROW_4M8_13_p32       LA32:1562  sorry :1564
        |     HOL MIQMCSN.hl:3410-3427 (18 ln)                                [SORRY]
        |     +-- PROP_OPP_4M8_13_p32         LA32:1523                      [PROVEN, clean]
        |     +-- YXIONXL2/YXIONXL3/OPP_IS_SCS                              [外部]
        +-- SCS_4M8_13_ARROW_3T7_p32          LA32:1494  sorry :1496
              HOL MIQMCSN.hl:3336-3345 (10 ln)                                [SORRY]
              +-- SCS_4M8_13_SLICE_13_p32     LA32:1487  sorry :1489
              |     HOL MIQMCSN.hl:3207-3335 (129 ln)                         [SORRY]
              |     +-- LKGRQUI_concl         LA1:2884  sorry :2888           [根 SORRY]
              |     +-- SCS_DIAG_SCS_4M8_13_13_p32  LA32:1439                [PROVEN, clean]
              |     +-- STAB_4M8_13_SCS_p32   LA32:1451  sorry :1454
              |           HOL MIQMCSN.hl:3042-3053 (12 ln)                    [SORRY]
              |           +-- YRTAFYH_concl   LA1:4998                        [PROVEN, clean]
              +-- PRO_EQU_ID1 / YXIONXL3     LA12:1010 / LA12:1224            [PROVEN clean, 缺席]

  +-- isScsV39 scs3T7 (S2 首合取)  ->  SCS_3T7_IS_SCS_p32  LA32:279  sorry :280
                                                                              [SORRY, 无干净孪生]
  +-- isScsV39 scs3T4 (S2 首合取)  ->  SCS_3T4_IS_SCS_p29  LA29:853          [PROVEN, clean]
```

逐跳（HOL :3436-3470）：`FZIOTEF_TRANS` 取
`{scs_4M6', scs_opp_v39 scs_4M6', scs_4M8_02, scs_4M8_13} ∪ stab-diag 集`（:3439-3441）；
首段 `SCS_4M8_ARROW_STEP_ONE`（:3442），stab 集 `SET_STAB_4M8_ARROW_3T4`（:3443），
`{scs_4M8_02}` 经 `SCS_4M8_02_ARROW_3T7`（:3444），opp 支经 `YXIONXL2`/`SCS_OPP_REFL`（:3448-3470）。

## 5. 根节点表（按类型）

| 根节点 | 位置 | 状态 | 影响目标 |
|---|---|---|---|
| `VASYYAU_concl` | `LocalAuto1.lean:4913`（`sorry` :4922） | **根 SORRY**（import 闭包内） | T1, T2, T3 |
| `LKGRQUI_concl` | `LocalAuto1.lean:2884`（`sorry` :2888） | **根 SORRY**（import 闭包内） | T2, T3（全部 4 条 SLICE） |
| `YXIONXL2_concl` | `LocalAuto1.lean:2578`（`sorry` :2580） | **根 SORRY**（import 闭包内） | T2, T3 |
| `YXIONXL3_concl` | `LocalAuto1.lean:2876`（`sorry` :2878） | **根 SORRY**（import 闭包内） | T2, T3 |
| `SCS_4T3_IS_SCS_p32` | `LocalAuto32.lean:247`（`sorry` :248） | **根 SORRY**；全仓无干净孪生 | T1, T2 |
| `SCS_3T7_IS_SCS_p32` | `LocalAuto32.lean:279`（`sorry` :280） | **根 SORRY**；全仓无干净孪生 | T3 |
| `isScsV39 scs3T3` | 无干净证明（LA22:2324 带 `sorryAx`） | **根 缺口** | T2 |
| `SET_STAB_4M6_ARROW_4T5` | LA32 无声明；LA33:4298 clean | 缺席（可移植） | T1 |
| `isScsV39 scs4T5` | LA32 无声明；LA33:1492 clean | 缺席（可移植） | T1 |
| `SCS_OPP_REFL` / `OPP_IS_SCS` / `PRO_EQU_ID1` / `YXIONXL3`(LA12) / `STAB_4M7_SCS` / `STAB_4M8_SCS` / `SCS_DIAG_SCS_4M7_{13,02}` | FanBaseKit / LA33 / LA12 | clean 但**不在 import 闭包** | T2, T3 |

要点：**四条真根在 `LocalAuto1`（LA32 已 import，但仍是 `sorry`）**，不属本车道可动范围；
另有三条 `isScsV39` 缺口，其中 `scs4T3`/`scs3T7` 全仓没有干净证明。

## 6. 全仓孪生搜索（"是否有已证孪生"）

命令：`grep -rn '<NAME>' Kepler/ --include='*.lean' | grep -v 'LocalAuto32.lean' | wc -l`

| 名称 | LA32 外命中 | 结论 |
|---|---|---|
| 20 条 in-file 阻断件（§2-§4 中 `[SORRY]` 者） | **0** | 全仓无任何孪生（含已证/未证），只能在本文件新证 |
| `SET_STAB_4M6_ARROW_4T5` | 2 | 仅 LA33 `_p33`，已证 clean |
| `SCS_4T5_IS_SCS` | 5 | LA33:1492 clean；LA22 `_p22` 带 sorryAx |
| `SCS_4T3_IS_SCS` | 0 | **无干净孪生** |
| `SCS_3T7_IS_SCS` | 0 | **无干净孪生** |
| `MMS_IMP_BBS_p28` | LA28:194 | clean（LA29 传递 import） |
| `BB_VV_FUN_EQ_p26` | LA26:198 | clean（LA29 传递 import） |
| `XWNHLMD_MM_p26` | LA26:1642 | clean（LA29 传递 import） |

## 7. 公理面实测（决定"闭完是否干净"）

`logs/probe_toolkit.log`（import `Kepler.Text.LocalAuto32`，全部为 import 闭包内）：

```
MMS_IMP_BBS_p28            [propext, Classical.choice, Quot.sound]   clean
BB_VV_FUN_EQ_p26           [propext, Classical.choice, Quot.sound]   clean
XWNHLMD_MM_p26             [propext, Classical.choice, Quot.sound]   clean
YRTAFYH_concl              [propext, Classical.choice, Quot.sound]   clean
STAB_MOD                   [propext, Classical.choice, Quot.sound]   clean
SCS_4M6_STAND_OR_PRO_p32   [propext, Classical.choice, Quot.sound]   clean
SET_EQ_DIAG_STAB_4M7_p32   [propext, Classical.choice, Quot.sound]   clean
SET_EQ_DIAG_STAB_4M8_p32   [propext, Classical.choice, Quot.sound]   clean
PROP_OPP_DIAG_4M8_13_p32   [propext, Classical.choice, Quot.sound]   clean
SCS_{3T4,4M6,4M7,4M8}_IS_SCS_p29 / SCS_3M1_IS_SCS
                           [propext, Classical.choice, Quot.sound]   clean
LKGRQUI_concl              [propext, sorryAx, Classical.choice, Quot.sound]  ROOT
VASYYAU_concl              [propext, sorryAx, Classical.choice, Quot.sound]  ROOT
```

`logs/probe_twins*.log`（import LA12/LA13/LA22/LA33，不在 LA32 闭包）：

```
PRO_EQU_ID1                clean      YXIONXL3 (LA12)          clean
SCS_OPP_REFL_fb            clean      OPP_IS_SCS_p33           clean
SCS_4T5_IS_SCS_p33         clean      SET_STAB_4M6_ARROW_4T5_p33 clean
YXIONXL2_p33               clean      YXIONXL3_p33             clean
PRO_EQU_ID1_p33            clean      SCS_3T3_IS_SCS_p33       clean
STAB_4M7_SCS_p33           clean      STAB_4M8_SCS_p33         clean
SCS_DIAG_SCS_4M7_13_p33    clean      SCS_DIAG_SCS_4M7_02_p33  clean
SCS_DIAG_SCS_4M8_13_p33    clean      XWNHLMD_MM_p33           clean
is_scs_4T3_p22             [propext, sorryAx, ...]  <- 带 sorryAx
is_scs_4T5_p22             [propext, sorryAx, ...]  <- 带 sorryAx
is_scs_3T3_p22             [propext, sorryAx, ...]  <- 带 sorryAx
is_scs_3T7_p22             [propext, sorryAx, ...]  <- 带 sorryAx
```

结论：**除 4 条 `LocalAuto1` 根 sorry 与 3 条 `isScsV39` 缺口外，链上其余节点全部公理干净。**
即"闭完依赖链仍含 sorryAx"并非必然——只要 4 条根 + 3 条 `isScs` 缺口真证，
三条目标可以达到 `[propext, Classical.choice, Quot.sound]`。这是下波工单的核心依据。

## 8. 为什么本波零闭合

- 简报 §1：依赖仍 `sorry` 即 BLOCKED，"不许在它上面做结构闭合（搬债，AGENTS §2 明令作废）"。
- 简报 §2：**不碰** LA32 其余 57 条 sorry —— 而三条目标的直接依赖全部落在这 57 条里。
- 因此本波唯一正确动作是：给出依赖树 + 缺口表 + 下波工单（见 `WORKORDER-la32-deblock.md`），不落任何 `sorry` 支撑的证明。

## 9. 复现命令

```sh
S=/Users/zhangzhuo/c17_backup/lane_snapshots/la32-miqmcsn-w1
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git rev-parse HEAD                                  # b89ee8b4...
shasum -a 256 lean/Kepler/Text/LocalAuto32.lean     # 385fa907...
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/baseline.log lean lean/Kepler/Text/LocalAuto32.lean
tr -d '\r' < $S/logs/baseline.log | grep -c ': error:'                       # 0
tr -d '\r' < $S/logs/baseline.log | grep -c 'declaration uses `sorry`'       # 60
# 探针（在 /tmp/la32-miqmcsn-w1 下跑，-o 指到 /tmp，不写仓）
cd /tmp/la32-miqmcsn-w1
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/probe_axioms.log lean -o /tmp/la32-miqmcsn-w1/probe_axioms.olean probe_axioms.lean
```
