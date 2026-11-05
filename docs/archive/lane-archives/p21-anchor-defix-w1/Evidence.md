# Evidence — lane `p21-anchor-defix-w1`（DEF-FIX：LA21/LA18 终端锚点）

- 仓库 `/Users/zhangzhuo/repos/kepler-conjecture-lean4`；车道发车 HEAD `873d2a2c`。
  车道期间其它车道把 HEAD 推进到 `47766955`；两目标文件在
  `873d2a2c..47766955` 全部提交中 byte-identical（`git diff --stat 873d2a2c HEAD --
  lean/Kepler/Text/LocalAuto18.lean lean/Kepler/Text/LocalAuto21.lean` 为空），
  故所有读数对发车基线有效。
- cwd `/tmp/p21-anchor-defix-w1/`；产物 `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/p21-anchor-defix-w1/`。
- 纪律：无 `lake` 子命令（唯一的 lake 进程是**其它车道**在跑，见 §6）；未写
  `lean/.lake/`；编译仅 standalone `lean`，`LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)`
  + `nice -n 19 script -q <log>`；探针串行。

## 1. 基线：旧命题可反驳（改前）

探针 `/tmp/p21-anchor-defix-w1/probe_p21.lean`：

```lean
import Kepler.Text.LocalAuto21
open Kepler.Text

theorem not_p21_anchor : ¬ mainNonlinearTerminalV11_p21 := by
  intro h
  have h0 := h (fun _ => 0)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h0
  linarith

#print axioms not_p21_anchor
```

命令与结果（`logs/probe-old-p21.log`，RC=0）：

```
'not_p21_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

即改前锚点 `∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p21 y` 是**可证伪**命题，
且证伪只用标准三 axioms。

## 2. 改后：别名生效

探针 `/tmp/p21-anchor-defix-w1/probe_print.lean`（`logs/print-anchors.log`，RC=0）：

```
def Kepler.Text.mainNonlinearTerminalV11_p21 : Prop :=
main_nonlinear_terminal_v11
def Kepler.Text.mainNonlinearTerminalV11_p18 : Prop :=
main_nonlinear_terminal_v11
Kepler.Text.mainNonlinearTerminalV11_p21 : Prop
Kepler.Text.mainNonlinearTerminalV11_p18 : Prop
```

## 3. 改后：旧命题不再存在（同一探针编译失败）

`logs/probe-post-p21.log`（RC=1）：

```
/tmp/p21-anchor-defix-w1/probe_p21.lean:6:15: error: Application type mismatch: The argument
  fun x => 0
has type
  ?m.5 → ℕ
but is expected to have type
  String
in the application
  h fun x => 0
'not_p21_anchor' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

（`sorryAx` 是 Lean 错误恢复生成的占位声明，不是证明；关键是第 6 行的
application type mismatch：`h` 的第一个显式参数已是 registry 的 `id : String`，
不再是 `Fin 6 → ℝ` 的函数。故旧 `∀ y` 命题已不存在。）

`_p18` 孪生同判：`logs/probe-post-p18.log`（RC=1），`probe_p18.lean:6:15`
同一 `Application type mismatch`。

## 4. 编译（补丁后，规定命令）

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q $S/logs/post-<File>.log lean <repo>/lean/Kepler/Text/<File>.lean
```

| 文件 | RC | error 行数 | `declaration uses \`sorry\``（改前 → 改后） |
|---|---|---|---|
| `LocalAuto18.lean` | 0 | 0 | 11 → 11 |
| `LocalAuto19.lean` | 0 | 0 | 29 → 29 |
| `LocalAuto21.lean` | 0 | 0 | 29 → 29 |
| `LocalConcl.lean` | 0 | 0 | — → 23 |

读法：`tr -d '\r' < log | grep -c 'declaration uses \`sorry\`'`（带反引号）。

**fresh-olean 传播验证**（辅助，`lean --root <repo>/lean -o <private>/…`）：
私有 overlay `/tmp/p21-anchor-defix-w1/olean`（symlink 全量 `Kepler` olean 树
+ shadow 树）内先重建 LA18（`logs/fresh-LocalAuto18.log`，RC=0，11 sorry），
再以该 fresh LA18 重建 LA19（`logs/fresh-LocalAuto19.log`，RC=0，29 sorry）。
LA21 的首次尝试（`logs/fresh-LocalAuto21.log`）失败于
`Kepler.Text.LocalAuto34`/`LocalAuto26`/`LocalAuto33` 的 olean 缺失——那是
**其它车道在飞**的 `LocalAuto16` 新 import 的依赖，与两行改动无关；并发
`lake build` 补齐这些 olean 后，规定命令下 LA21 RC=0（上表）。LA18/19/21
的 `.lake` olean 时间戳（13:55 / 13:58 / 14:00）均晚于补丁源
（13:54:06），确认 post 编译加载的是补丁后 olean。

## 5. 围栏与 kit 校验

- 两 gate 文件的 §2.1 fence 与各自 `git diff` 的 `-`/`+` 行**多重集逐一相等**：
  LA18 `4 dels / 10 adds`、LA21 `6 dels / 9 adds`，无缺无余（脚本核验）。
- `git diff` 的增删行中 `sorry`/`admit`/`native_decide` 计数 = **0**
  （净 sorry = 0）。
- `kit-p21-anchor-defix-w1.diff` = 2 个 lean 文件 diff + 3 个新章程
  no-index diff（共 5 个 `diff --git` 块，274 行）。
  - `git apply --check`（干净 HEAD 的两个目标文件副本，`/tmp/…/clean`）：**RC=0**。
  - `git apply --reverse --check`（当前工作树）：**RC=0**。
- 闸门规则 1–3 模拟（`auto_gate.sh` 截取到规则 4 之前，`LEAN_DIR=<repo>/lean`，
  不触 `lake`）：LA18 `GATE-SIM-PASS mainNonlinearTerminalV11_p18`（RC=0）、
  LA21 `GATE-SIM-PASS mainNonlinearTerminalV11_p21`（RC=0）。
  `LANE_FILES` 当时取值 = `Kepler/Text/LocalAuto16.lean,Kepler/Text/LocalAuto26.lean,
  Kepler/Text/LocalAuto18.lean,Kepler/Text/LocalAuto21.lean`（首次），
  以及交付时 `Kepler/Text/LocalAuto18.lean,Kepler/Text/LocalAuto21.lean,
  Kepler/Text/TameCorrBase.lean`（其它车道提交后）。规则 4/4b/5（`lake build`、
  `lake env lean` 公理检查）不在本车道执行，留给编排者跑正式闸门。
- md5：`LocalAuto18.lean = cdf5883aab3fbc1250ce4a86e4bb45b9`；
  `LocalAuto21.lean = 67e8acb8fee0d08a286a0e5ae0f63756`；
  `kit = cb767444dc3484bd7bc5373a5925a419`。

## 6. 并发环境说明

车道期间另一车道运行
`lake build Kepler.Text.Hypermap Kepler.Text.PackingConcl Kepler.Text.LocalConcl
Kepler.Text.LocalBridge Kepler.Text.TameLp Kepler.Text.AzimBridge Kepler.Text.ContraFan`，
并以当前工作树（含本 patch）重建了 `LocalAuto18/19/21/LocalConcl` 的 `.olean`；
`LocalConcl.olean`（14:01）构建成功，与本车道独立编译结果一致。本车道自身
**未调用任何 `lake` 子命令**，也未写 `lean/.lake/`。

## 7. 日志清单

`logs/`：`base-LocalAuto18/19/21.log`（改前）、`fresh-LocalAuto18/19/21.log`
（私有 overlay）、`post-LocalAuto18/19/21/LocalConcl.log`（改后规定命令）、
`probe-old-p21.log`、`probe-post-p21.log`、`probe-post-p18.log`、
`print-anchors.log`。
