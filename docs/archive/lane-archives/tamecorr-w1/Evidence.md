# Evidence — tamecorr-w1（TameLp-only 版）

HEAD `873d2a2c`｜cwd `/tmp/tamecorr-w1/`｜快照 `$S=/Users/zhangzhuo/c17_backup/lane_snapshots/tamecorr-w1/`

> **口径变更（用户 2026-11-05 批）**：模块由 "import Assembly" 改为**只 import `Kepler.Text.TameLp`**，
> 结论全部改述到 `TameLp.IsHypermapOfListTl`；Assembly 层搬运留给 W2。
> 旧版（Assembly 版）证据保留在 `logs/build-TameCorrBase.log` / `probe1-3.log`，仅作历史对照，**不再代表当前交付**。

## 0. 纪律自检

| 约束 | 实测 |
|---|---|
| 禁止 `lake` 子命令 | 全程 0 次 |
| 不触 `lean/.lake/` | 只读 `ls`/轮询 `.olean`；零写入 |
| 只读引用 `/tmp/lfainteg/asm_check/leanpath.txt` | 是 |
| 仓内只改 `Kepler/Text/TameCorrBase.lean` | 是（`git status` 本车道仅 ` A` 该文件） |
| 零 sorry/admit/native_decide | 唯一 `grep` 命中 = 第 44 行头注纪律声明 |
| 禁 `open Classical` | 无；也未用 `classical` tactic |
| **新增 import 申报** | **仅 `Kepler.Text.TameLp`（第 46 行）**，无其它 |
| 探针单进程串行 | 是 |

## 1. import 行原文

```
import Kepler.Text.TameLp
```

无 `import Kepler.Assembly`、无 Mathlib 额外项。闭包（TameLp 头，46 行文件）：
`Hypermap, Fan, Assembly.GoodListDefs, TopologyFan, PackingAuto2, LocalAuto2, LocalAuto16,
AzimLemmas, ConformingDefs, ConformingAuto1, ConformingAuto21, ConformingAuto23, ContraFan,
ConformingAuto6, LuneVolume`——**零 `Kepler.Interval`**。
无环：`grep -rn "import Kepler.Text.TameCorrBase" lean/` = 0 命中（叶子模块）。

## 2. 编译与公理审计（standalone）

命令（逐字）：

```
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) \
  nice -n 19 script -q /tmp/tamecorr-w1/logs/build-TameCorrBase-tamelp.log \
  lean Kepler/Text/TameCorrBase.lean
```

- **RC=0，errors=0，warnings=0**（attempt 1，无需重试）
- 文件：174 行；diff 180 行
- `#print axioms` 8/8（日志内联）：

```
'Kepler.Text.TameCorrBase.hypermapOfList_isHypermapOfListTl_arity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.darts_hypermapOfList_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.mem_darts_hypermapOfList_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.isHypermapOfListTl_darts_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.isHypermapOfListTl_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.isHypermapOfListTl_eq_hypermapOfList' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.isHypermapOfListTl_iff_eq_hypermapOfList' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameCorrBase.hypermapIso_of_isHypermapOfListTl' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. "不碰 Assembly" 的实证（阴性对照）

同一 `LEAN_PATH`、同一 `script` 方式：

```
$ lean /tmp/tamecorr-w1/probe-asm.lean        # 内容仅: import Kepler.Assembly + #check
rc=1
/tmp/tamecorr-w1/probe-asm.lean:1:0: error: object file
 '…/.lake/build/lib/lean/Kepler/Interval/Cases/CQITNPEAx3725403817/Shard490.olean'
 of module Kepler.Interval.Cases.CQITNPEAx3725403817.Shard490 does not exist
```

（`logs/probe-asm2.log`）
shard 现状：`Kepler/Interval/Cases/*.lean` = **237** 个源文件，`.olean` = **36**（重建中）。
本模块在同环境下 RC=0 ⇒ 依赖已彻底摘净、与 shard 重建解耦。

## 4. 补丁完整性（只读）

```
$ git diff --stat -- lean/Kepler/Text/TameCorrBase.lean
 lean/Kepler/Text/TameCorrBase.lean | 174 +++++++++++++++++++++++++++++++++++++
 1 file changed, 174 insertions(+)

$ git cat-file -e HEAD:lean/Kepler/Text/TameCorrBase.lean
fatal: path … exists on disk, but not in 'HEAD'      # ⇒ 纯新增

$ git apply --check --reverse $S/kit-tamecorr-w1.diff
REVERSE-APPLY-OK
```

## 5. 关键源码坐标（供复核）

| 事实 | 坐标 |
|---|---|
| `TameLp.IsHypermapOfListTl`（四字段，与 Assembly 同体） | `lean/Kepler/Text/TameLp.lean:6126` |
| `hypermapOfList_isHypermapOfListTl`（规格实例，已在库） | `TameLp.lean:6139` |
| `hypermapOfList` 构造 | `TameLp.lean:5188` |
| 四字段求值律 | `TameLp.lean:5220/5225/5231/5238` |
| `Hypermap` 结构 / `PermutesOn`（`∀ x ∉ s, f x = x`） | `Text/Hypermap.lean:765/678` |
| `Hypermap.Iso` / `Iso.refl` | `Text/Hypermap.lean:8249/8255` |
| `hypermapOfList_iso_refl`（Tl 层自反） | `TameLp.lean:5257` |
| Assembly 谓词（W2 搬运目标） | `lean/Kepler/Assembly.lean:194` |
| 同体互转（另件，import Assembly，本波不取） | `Text/TameSpine/Keystone.lean:99` |
| `jcajydu` / `tameCorrespondenceIso`（W2/W3 占位） | `Assembly.lean:2441/2447` |
| `Reduction5.restricted_hypermaps_are_planegraphs_thm`（**仅注释**） | `Assembly.lean:1969` |
| 既有 `RXOKSKC` 主件 | `Text/TameSpine/TameList69.lean:605` |
| `is_restricted` 沿 iso 运输（公开） | `TameList15.lean:655` |

## 6. 快照清单（`$S/`）

```
kit-tamecorr-w1.diff        180 行（git diff，纯新增）
TameCorrBase.lean           174 行（= 仓内文件，byte-identical）
kit-tamecorr-w1-file.lean   同上（便于只看文件内容）
RECON.md                    Step 0 三项结论 + import 闭包 + W2 缺口（含口径变更附录）
DELIVERY.md                 逐件状态 + 残件 + W2 工单草案
Evidence.md                 本文件
logs/                       build-TameCorrBase-tamelp.log（当前交付）
                            probe-asm2.log（阴性对照）
                            build-TameCorrBase.log + probe1/2/3.log（旧 Assembly 版，历史对照）
                            baseline-*.txt
```
