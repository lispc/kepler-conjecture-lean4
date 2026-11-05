# Evidence — `reduction5-w0`

所有命令均在 `/Users/zhangzhuo/repos/kepler-conjecture-lean4/lean` 下执行；
主仓 HEAD 开工 `ca6b5bff` / 收工 `c5de2e48`（SF-102 落库，与本车道无关）；
本车道未改任何 tracked 文件（`git status --porcelain` 里本车道的新增项只有两个交付文件）。

## E-1 standalone 编译：`Reduction5Base.lean`（RC=0，零诊断）

```
$ nice -n 19 lake env lean Kepler/Text/Reduction5Base.lean \
    -o .lake/build/lib/lean/Kepler/Text/Reduction5Base.olean
RC=0
```

`logs/compile_Base.log` = **0 字节**（0 error / 0 warning）。
（`-o` 只为让 `Reduction5.lean` 能按模块名 import；产物在 `.lake/`，已 gitignore。）

## E-2 standalone 编译：`Reduction5.lean`（RC=0，零诊断）

```
$ nice -n 19 lake env lean Kepler/Text/Reduction5.lean \
    -o .lake/build/lib/lean/Kepler/Text/Reduction5.olean
RC=0
```

`logs/compile_Thm.log` = **0 字节**。

## E-3 `#print axioms`：9/9 定理 = 标准三

```
$ nice -n 19 lake env lean /tmp/reduction5-w0/probe/axioms.lean
'Kepler.Text.Reduction5.mem_listPairs_nextEl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.minNum_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.ntrans_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.rtrans_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.ytrans_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.ztrans_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.mtrans_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.ftrans_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.Reduction5.betwnCoreReductionLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
```

（原文见 `logs/axioms.log`；无 `sorryAx`。）

## E-4 环自检（工单 §4.4 的硬要求）

### E-4a 命令级：`#check` 必须 unknown identifier

`/tmp/reduction5-w0/probe/cycle.lean`：

```lean
import Kepler.Text.Reduction5Base
#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces
```

```
$ nice -n 19 lake env lean /tmp/reduction5-w0/probe/cycle.lean
probe RC=1
/tmp/reduction5-w0/probe/cycle.lean:3:8: error(lean.unknownIdentifier):
  Unknown identifier `Kepler.Assembly.the_kepler_conjecture_from_interfaces`
```

`Kepler.Assembly.the_kepler_conjecture_from_interfaces` 实际定义在
`Kepler/Assembly.lean:7181`（`grep -rn` 实测）。它在 `Reduction5Base` 的探针里
**不可见** ⇒ import 闭包不含 `Kepler.Assembly`。
（RC=1 是**期望值**：这条探针的"通过"就是 unknown identifier。）

### E-4b 静态闭包（独立复核）

```
$ python3 -I logs/closure.py <lean-root> Kepler.Text.Reduction5Base
module: Kepler.Text.Reduction5Base
local deps: 158
contains Kepler.Assembly: False

$ python3 -I logs/closure.py <lean-root> Kepler.Text.Reduction5
module: Kepler.Text.Reduction5
local deps: 159
contains Kepler.Assembly: False

$ python3 -I logs/closure.py <lean-root> Kepler.Text.Reduction5Base Kepler.Text.TameSpine
module: Kepler.Text.Reduction5Base
local deps: 158
contains Kepler.Text.TameSpine: False
```

脚本 `logs/closure.py` 会剥掉嵌套块注释与行注释（避免把 docstring 里的
`import …` 误算），再按 `^\s*import\s+X$` 走传递闭包。

## E-5 撞名检查

```
$ grep -rn "Kepler\.Text\.Reduction5" lean/Kepler/ \
    | grep -v "Kepler/Text/Reduction5Base.lean" | grep -v "Kepler/Text/Reduction5.lean"
（0 hits）
```

同**裸名**声明在 `lean/Kepler/Text/` 下共 7 处，全部在**不同 namespace**：

```
lp                  lean/Kepler/Text/LP/LPPilot.lean:109        namespace=Kepler.Text.LP.LPPilot
minNum              lean/Kepler/Text/LocalAuto1.lean:662       namespace=Kepler.Text
ly                  lean/Kepler/Text/SphereKit.lean:156        namespace=Kepler.Text
indexf              lean/Kepler/Text/TameSpine/TameList3.lean:90  namespace=Kepler.Text.TameSpine
partitionIntoAtom0  lean/Kepler/Text/TameSpine/TameList7.lean:446 namespace=Kepler.Text.TameSpine
partitionIntoAtom    lean/Kepler/Text/TameSpine/TameList7.lean:457 namespace=Kepler.Text.TameSpine
partitionIntoAtom0r lean/Kepler/Text/TameSpine/TameList9.lean:676 namespace=Kepler.Text.TameSpine
```

本 W0 的 FQN 全在 `Kepler.Text.Reduction5.*`（37 个，见 `logs/collision_check.txt`），
与上述 7 处**零重名**。

**遮蔽实测**：`Kepler.Text.ly` / `Kepler.Text.minNum` 在父 namespace，理论上会被
`Kepler.Text.Reduction5.ly` / `.minNum` 遮蔽。已用两份"合成遮蔽"文件验证：
`import Kepler.Text.SphereKit` + `import Kepler.Text.LocalAuto1` + 本文件全文，
编译 **RC=0**（`/tmp/reduction5-w0/probe/Thm_shadow.lean`）；最终真编译（TameLp 已含
这两个模块）同样 RC=0。

## E-6 定义逐字对照（HOL ↔ Lean）

`logs/def_dump.txt`（150 行）= `#print` 全部 26 个定义 + 1 条定理（27 个声明）的完整输出（RC=0），可逐行对照：

- `core`：`List.map (fun l => (l.headD (0,0)).1) (parts L r)` ↔ HOL `MAP (FST o HD) (parts L r)`；
- `splitNormalList`：`List.range' 1 (sz x.1 - 1)` ↔ HOL `upt 1 (sz (FST x))`；
- `transformList`：`if finalList L r then (N, r) else (N', split.2)` ↔ HOL 同形；
- `ftrans`：`if i = 0 then x.2 else (ztrans L N r x (i - 1)).1` ↔ HOL `if i = 0 then SND x else FST (ztrans … (PRE i))`；
- `coreSplitNormalList` / `rRtransEq` 的 `cat` 嵌套逐字保留（右结合）。

## E-7 禁造边检查

```
$ grep -n "sorry\|native_decide\|axiom\|admit" \
    lean/Kepler/Text/Reduction5Base.lean lean/Kepler/Text/Reduction5.lean
（0 hits，exit=1）
```

## E-8 patch

```
$ grep -n "^--- \|^+++ \|^new file" patch.diff
2:new file mode 100644
4:--- /dev/null
5:+++ b/lean/Kepler/Text/Reduction5Base.lean
262:new file mode 100644
264:--- /dev/null
265:+++ b/lean/Kepler/Text/Reduction5.lean

$ mkdir -p /tmp/w0clean/lean/Kepler/Text && cd /tmp/w0clean \
    && git apply --check ~/c17_backup/lane_snapshots/reduction5-w0/patch.diff
GIT APPLY CHECK PASS
```

`+` 行 401（= 256 + 143 + 2 个 `+++` 头）；`-` 行 2（两个 `---` 头）。

文件哈希：

```
0009ebfd00013473706d8c411bc8849d67e1f9cd15fabef1bcffbd9d3fccd254  lean/Kepler/Text/Reduction5Base.lean
c78971ed1de8b5ac675cb0162694df55b3423aeb3011c5893c1483193bbbed73  lean/Kepler/Text/Reduction5.lean
```

## E-9 环境缺口（复现须知）

开工（16:00）时 `Kepler.Text.TameLp` 闭包缺 6 个 olean，逐次报错：

```
object file '…/.lake/build/lib/lean/Kepler/Text/LocalAuto14.olean' … does not exist
object file '…/LocalAuto20.olean' … does not exist
object file '…/LocalAuto24.olean' … does not exist
object file '…/LocalAuto29.olean' … does not exist
object file '…/LocalAuto34.olean' … does not exist
object file '…/LocalAuto35.olean' … does not exist
```

这 6 个由**并发重建**（非本车道）在 16:07–16:14 补齐；补齐后 E-1/E-2 均 RC=0。
本车道只跑过 `nice -n 19 lake env lean <单文件>`（+ `-o`），**未跑** `lake build` /
`auto_gate.sh` / 地图仪器 / `git commit`。

## E-10 岛 off-by-one 交叉核对

```
$ #eval List.range' 1 3
[1, 2, 3]
$ #eval List.range' 1 0
[]
$ #eval List.range' 1 (3 - 1)
[1, 2]
```

HOL `upt 1 (sz (FST x)) = iota 1 (sz-1)`（长度 `sz-1`）；
`TameSpine/TameList17.lean:88-101` 的 `splitNormalListSpine` 用 `range' 1 (sz x.1)`（长度 `sz`）。
本 W0 用 `range' 1 (sz x.1 - 1)`。详见 `DELIVERY.md` §7。
