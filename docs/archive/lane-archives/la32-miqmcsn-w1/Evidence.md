# Evidence — lane `la32-miqmcsn-w1`（BLOCKED，0 闭合）

基线 HEAD `b89ee8b45bc9ecbe197dd9e0551423326a9e8873`（`git rev-parse HEAD`）。
目标文件 `lean/Kepler/Text/LocalAuto32.lean`，1583 行，own-sorry 60。
所有读数均由本车道 standalone 命令产出，日志在 `$S/logs/`（`$S=/Users/zhangzhuo/c17_backup/lane_snapshots/la32-miqmcsn-w1`）。

## 1. 基线编译（`logs/baseline.log`）

命令原文：

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q /Users/zhangzhuo/c17_backup/lane_snapshots/la32-miqmcsn-w1/logs/baseline.log \
  lean lean/Kepler/Text/LocalAuto32.lean
```

读数（命令原文 + 值）：

| 命令 | 读数 |
|---|---|
| `echo "RC=$?"`（上条命令后） | **RC=0** |
| `tr -d '\r' < logs/baseline.log \| grep -c ': error:'` | **0** |
| ``tr -d '\r' < logs/baseline.log \| grep -c 'declaration uses `sorry`'`` | **60** |
| `tr -d '\r' < logs/baseline.log \| grep -c ': warning:'` | **81** |
| `wc -l /tmp/la32-miqmcsn-w1/baseline.clean.log` | 131 |

日志末三行（原文）：

```
lean/Kepler/Text/LocalAuto32.lean:1562:8: warning: declaration uses `sorry`
lean/Kepler/Text/LocalAuto32.lean:1569:8: warning: declaration uses `sorry`
lean/Kepler/Text/LocalAuto32.lean:1576:8: warning: declaration uses `sorry`
```

## 2. 零漂移自证（`Work.lean` = HEAD）

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git show HEAD:lean/Kepler/Text/LocalAuto32.lean > $S/Work.lean
shasum -a 256 $S/Work.lean lean/Kepler/Text/LocalAuto32.lean
```

原文读数：

```
385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779  .../la32-miqmcsn-w1/Work.lean
385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779  lean/Kepler/Text/LocalAuto32.lean
```

即：**本波零改动**，`Work.lean` 与 HEAD 逐字节相同。

## 3. own-sorry 计数（脚本口径）

脚本：逐声明切体（到下一声明行前），去掉 `--` 注释后统计裸 `sorry`；输出 131 个声明、
其中 60 个含裸 `sorry`、71 个无。

```
total decls: 131
sorried: 60 proven: 71
```

与基线日志的 `` `declaration uses sorry` `` 60 条一致。

## 4. 三目标公理面（`logs/probe_axioms.log`）

探针文件 `/tmp/la32-miqmcsn-w1/probe_axioms.lean`（仓外），命令：

```sh
cd /tmp/la32-miqmcsn-w1
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/probe_axioms.log lean -o /tmp/la32-miqmcsn-w1/probe_axioms.olean probe_axioms.lean
```

原文（RC=0）：

```
'Kepler.Text.NWDGKXH_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YOBIMPP_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.MIQMCSN_p32' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

同日志的 `#check` 原文（证明三件直接前置的陈述存在，且其体是 `sorry`）：

```
Kepler.Text.SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32 :
  Kepler.Text.main_nonlinear_terminal_v11 →
    Kepler.Text.scsArrowV39 {Kepler.Text.scs4M6'}
      ({Kepler.Text.scs4T3} ∪
        {s | ∃ i j, Kepler.Text.scsDiag 4 i j ∧ s = Kepler.Text.scsStabDiagV39 Kepler.Text.scs4M6' i j})
Kepler.Text.SCS_4M7_ARROW_STAB_4M7_4M6_p32 :
  Kepler.Text.main_nonlinear_terminal_v11 →
    Kepler.Text.scsArrowV39 {Kepler.Text.scs4M7}
      ({Kepler.Text.scs4M6', Kepler.Text.scsPropEquV39 (Kepler.Text.scsOppV39 Kepler.Text.scs4M6') 1} ∪
        {s | ∃ i j, Kepler.Text.scsDiag 4 i j ∧ s = Kepler.Text.scsStabDiagV39 Kepler.Text.scs4M7 i j})
Kepler.Text.SCS_4M8_ARROW_STEP_ONE_p32 :
  Kepler.Text.main_nonlinear_terminal_v11 →
    Kepler.Text.scsArrowV39 {Kepler.Text.scs4M8}
      ({Kepler.Text.scs4M6', Kepler.Text.scsOppV39 Kepler.Text.scs4M6', Kepler.Text.scs4M8_02, Kepler.Text.scs4M8_13} ∪
        {s | ∃ i j, Kepler.Text.scsDiag 4 i j ∧ s = Kepler.Text.scsStabDiagV39 Kepler.Text.scs4M8 i j})
```

**本波 0 闭合，因此没有"新闭合件的 `#print axioms`"可交**；上列三行即三条目标的
**基线（= 终态）**公理面。

## 5. 工具箱公理面（`logs/probe_toolkit.log`，均在 LA32 import 闭包内）

原文：

```
'Kepler.Text.MMS_IMP_BBS_p28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BB_VV_FUN_EQ_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p26' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YRTAFYH_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.STAB_MOD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_STAND_OR_PRO_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SET_EQ_DIAG_STAB_4M7_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SET_EQ_DIAG_STAB_4M8_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PROP_OPP_DIAG_4M8_13_p32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_3T4_IS_SCS_p29' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M6_IS_SCS_p29' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M7_IS_SCS_p29' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4M8_IS_SCS_p29' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_3M1_IS_SCS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LKGRQUI_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.VASYYAU_concl' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## 6. 闭包外干净孪生（`logs/probe_twins.log` / `probe_twins2.log` / `probe_twins3.log`）

`probe_twins.lean`（import LA12/LA13/LA22/LA33）原文：

```
'Kepler.Text.PRO_EQU_ID1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YXIONXL3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_OPP_REFL_fb' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.is_scs_4T3_p22' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.is_scs_4T5_p22' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.is_scs_3T3_p22' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.is_scs_3T7_p22' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.SCS_4T5_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SET_STAB_4M6_ARROW_4T5_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YXIONXL2_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YXIONXL3_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.PRO_EQU_ID1_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.OPP_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`probe_twins2.lean` 原文：

```
'Kepler.Text.SCS_3T3_IS_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SET_EQ_DIAG_STAB_4M6_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.STAB_4M6_02_ARROW_4T5_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.STAB_4M6_13_ARROW_4T5_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XWNHLMD_MM_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`probe_twins3.lean` 原文：

```
'Kepler.Text.STAB_4M7_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_DIAG_SCS_4M7_13_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_DIAG_SCS_4M7_02_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.STAB_4M8_SCS_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SCS_DIAG_SCS_4M8_13_p33' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**结论**：`is_scs_{4T3,4T5,3T3,3T7}_p22`（LocalAuto22）虽声明体不是 `sorry`，但实测**带 `sorryAx`**，
不能作为干净前置；LocalAuto33 的 `_p33` 系列全部干净。

## 7. 零改动 / 无残留

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
git status --porcelain          # 本波开始时 0 行；无未跟踪文件
ls -la lean/Kepler/Text/ | grep -i LocalAuto32   # 仅 LocalAuto32.lean，无 .olean/.ilean
```

- 所有探针文件在 `/tmp/la32-miqmcsn-w1/`（仓外），`lean -o` 输出也指向 `/tmp`。
- 未运行任何 `lake` 子命令；未写 `lean/.lake/`（该目录内 `LocalAuto32.olean` 的 mtime
  为 12:30，早于本车道 12:37 的编译，非本车道产物）。
- 未生成 `kit-*.diff`（零 diff）；未生成 `Kit-draft-*.lean`（无残件）。

## 8. 归档

按验收口径，`DELIVERY.md` + `Evidence.md` + `RECON.md` + `WORKORDER-la32-deblock.md`
已放入 `docs/archive/lane-archives/la32-miqmcsn-w1/`（无 `kit-*.diff`：零 diff）。
`Work.lean` 不入库（可由 HEAD 重建）。
