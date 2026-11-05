# DELIVERY — `reduction5-w0`（W0 定义基座）

- 车道：`reduction5-w0`（长周期工程 `Reduction5` 第一波）
- 日期：2026-11-05
- 主仓 HEAD：开工 `ca6b5bff`，收工 `c5de2e48`（期间 SF-102 落库；两次 HEAD 均无 `Reduction5*` 文件，
  故 patch 对两者都适用）。本车道未改任何 tracked 文件。
- 工作目录：`/tmp/reduction5-w0/`；产物：`~/c17_backup/lane_snapshots/reduction5-w0/`
- 工单：`/tmp/reduction5-w0-workorder.md`

## 0. 一句话结论

W0 的 **20/20 件全部 DONE**（19 个 `tame_defs2` 定义 + `betwn_core_reduction_lemma`），
外加 8 个必需前置定义与 9 条定理；**0 GAP / 0 UNRESOLVED / 0 占位证明**。
两个新文件 standalone `lake env lean` **RC=0、零诊断**；9/9 定理
`#print axioms` = `[propext, Classical.choice, Quot.sound]`；
环自检：`#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces` 在
`Reduction5Base` 探针里 **unknown identifier**（静态闭包 158 模块，`Kepler.Assembly` = False）。

## 1. 交付物

| 文件 | 内容 |
|---|---|
| `patch.diff` | 纯新增两文件，`--- /dev/null`，`git apply --check` PASS（401 行 `+`） |
| `DELIVERY.md` | 本文件 |
| `Evidence.md` | 每条验收 = 命令 + 原始输出 |
| `logs/` | 编译日志（空=零诊断）、axioms、环探针、静态闭包、撞名、定义 dump、脚本源码 |

新增文件（相对 HEAD 均为 untracked）：

- `lean/Kepler/Text/Reduction5Base.lean`（254 行，定义基座）
- `lean/Kepler/Text/Reduction5.lean`（143 行，定理层）

**import 面（逐字）**：

```
import Kepler.Text.TameLp
import Kepler.Graphs.ListAux
```

`Reduction5.lean` 只 `import Kepler.Text.Reduction5Base`。
**零** `Kepler.Text.TameSpine.*` import（`logs/closure_noTameSpine.txt`：False）。

## 2. 逐件表

### 2a. 工单 §2 点名的 19 个定义 + 1 条引理（20/20 DONE）

| # | HOL 名 | Lean 名（`Kepler.Text.Reduction5.*`） | HOL 锚（自 grep） | 状态 |
|---|---|---|---|---|
| 1 | `core` | `core` | `tame_defs2.hl:129-130` | **DONE** |
| 2 | `parts` | `parts` | `tame_defs2.hl:126-127` | **DONE** |
| 3 | `quotient_list` | `quotientList` | `tame_defs2.hl:134-136` | **DONE** |
| 4 | `final_list` | `finalList` | `tame_defs2.hl:138-139` | **DONE**（+ `Decidable` 实例） |
| 5 | `l'm` | `lm` | `tame_defs2.hl:440-443` | **DONE** |
| 6 | `l'y` | `ly` | `tame_defs2.hl:445-446` | **DONE** |
| 7 | `l'p` | `lp` | `tame_defs2.hl:448-450` | **DONE** |
| 8 | `l'z` | `lz` | `tame_defs2.hl:452-453` | **DONE** |
| 9 | `transform_list` | `transformList` | `tame_defs2.hl:458-467` | **DONE** |
| 10 | `ntrans` | `ntrans` | `tame_defs2.hl:469-470` | **DONE** |
| 11 | `rtrans` | `rtrans` | `tame_defs2.hl:472-473` | **DONE** |
| 12 | `ytrans` | `ytrans` | `tame_defs2.hl:475-476` | **DONE** |
| 13 | `ztrans` | `ztrans` | `tame_defs2.hl:478-479` | **DONE** |
| 14 | `ftrans` | `ftrans` | `tame_defs2.hl:481-482` | **DONE** |
| 15 | `mtrans` | `mtrans` | `tame_defs2.hl:484-485` | **DONE** |
| 16 | `transform_count` | `transformCount` | `tame_defs2.hl:487-489` | **DONE** |
| 17 | `ifbetwn` | `ifbetwn` | `tame_defs2.hl:788-789` | **DONE** |
| 18 | `core_split_normal_list` | `coreSplitNormalList` | `tame_defs2.hl:770-784` | **DONE** |
| 19 | `r_rtrans_eq` | `rRtransEq` | `tame_defs2.hl:762-768` | **DONE** |
| 20 | `betwn_core_reduction_lemma` | `betwnCoreReductionLemma` | `reduction5.hl:19-52` | **DONE**（定理，标准三） |

### 2b. 未点名但为上述载体所必需的前置（8 定义，全部 DONE）

| HOL 名 | Lean 名 | HOL 锚 | 被谁需要 |
|---|---|---|---|
| `min_num` | `minNum` | `tame_defs.hl:313` | `lm` / `lp` / `transformCount` |
| `partition_into_atom0` | `partitionIntoAtom0` | `tame_defs2.hl:111-117` | `parts` |
| `partition_into_atom0r` | `partitionIntoAtom0r` | `tame_defs2.hl:119-121` | 同上（逐字保留） |
| `partition_into_atom` | `partitionIntoAtom` | `tame_defs2.hl:123-124` | `parts` |
| `core_list` | `coreList` | `tame_defs2.hl:108-109` | `quotientList` |
| `split_normal_list` | `splitNormalList` | `tame_defs2.hl:167-177` | `transformList` / `coreSplitNormalList` |
| `indexf` | `indexf` | `tame_defs2.hl:73-76` | `rRtransEq` |
| `mem_list_pairs_explicit` | `mem_listPairs_nextEl` | `list_hypermap-compiled.hl:295-303` | `betwnCoreReductionLemma` |

### 2c. 定理层（9 条，全部 DONE + 标准三）

| Lean 名 | 来源 | 性质 |
|---|---|---|
| `mem_listPairs_nextEl` | `list_hypermap-compiled.hl:295-303` | 真证（下标 + `idxOf` + 末位 `headD` 分支） |
| `minNum_spec` | `tame_defs.hl:313` 的规格件 | 真证（`Nat.find` + `Classical.epsilon_spec`） |
| `ntrans_zero` / `rtrans_zero` | `tame_defs2.hl:469-473` | `rfl` |
| `ytrans_def` / `ztrans_def` / `mtrans_def` | `tame_defs2.hl:475-485` | `rfl` |
| `ftrans_zero` | `tame_defs2.hl:481-482` | `simp [ftrans]`（`ftrans … 0 = x.2`） |
| `betwnCoreReductionLemma` | `reduction5.hl:19-52` | 真证（11 行 HOL 的两步逻辑） |

## 3. 总行数

| 文件 | 行数 |
|---|---|
| `Reduction5Base.lean` | 256 |
| `Reduction5.lean` | 143 |
| **合计** | **399** |

（工单估计 600–950 行；实际 399 行，因为 W0 的证明面只有 1 条 11 行引理 + 1 条 HOL 前置，
其余全是定义。未触 450 行单笔上限。）

## 4. `#print axioms` 汇总

9/9 定理 = `[propext, Classical.choice, Quot.sound]`（原始输出见 `logs/axioms.log`）。
**无 `sorryAx`、无新增公理、无 `native_decide`**（`grep -n "sorry\|native_decide\|axiom"` 两文件 0 命中）。

## 5. 缺口清单

- **GAP：0**。
- **UNRESOLVED：0**。
- **`split_normal_list`/`replace` 载体缺口：0**（`replace` 已在 `Graphs/ListAux.lean:55`；
  `splitNormalList` 为 10 行定义，已交）。工单 §3 的 150 行止损线未触发。
- **环境缺口（非 W0 产物问题，必须知会编排者）**：开工时 `Kepler.Text.TameLp` 的闭包缺
  6 个 olean（`LocalAuto14/20/24/29/34/35`），standalone 编译会报
  `object file '…LocalAutoXX.olean' does not exist`。本次由并发重建（非本车道执行）
  补齐后 RC=0。若后续再清理 `.lake`，W0 复验前需先重建这些上游模块。

## 6. 与 HOL 的逐字对照说明（定义类）

1. **类型特化**：HOL 多态 `A` → Lean `ℕ × ℕ`。理由：本链全部使用点为 `num#num`；
   复用的 `f_list`/`e_list`/`n_list`/`find_face`/`list_pairs`（`GoodListDefs`）本身已特化。
   定义体逐句未改（`logs/def_dump.txt` 可逐行对照 HOL）。
2. **`partition_into_atom0` 的 junk 补全**：HOL `HD (HD acc)` 在内层空表时无定义；
   Lean 用 `a.headD r`。可达输入（每个 atom 非空）上逐值一致，已写进 docstring。
3. **`min_num` 空集**：HOL `@m. …` 未定义，Lean `Classical.epsilon` 同样未定义（非空集上有 `minNum_spec`）。
4. **`ifbetwn`/`indexf`**：HOL 多态 + `=`；Lean 多态 + `[DecidableEq α]`（`BEq` 由实例导出）。
5. **`upt 1 n`**：Lean `List.range' 1 (n - 1)`（`#eval List.range' 1 3 = [1,2,3]` 已实测，
   故 `range' 1 (n-1)` 长度 = `n-1`，与 `iota 1 (n-1)` 一致）。
6. **`ftrans`/`core` 值域**：HOL 是 `A`（顶点），不是 `A#A`。Lean 分别为 `ℕ` 与 `List ℕ`。

## 7. 岛交叉核对（勘误候选，供编排者裁决）

`Kepler/Text/TameSpine/TameList17.lean:88-101` 的 `splitNormalListSpine` 用
`List.range' 1 (sz x.1)`（长度 `sz`），而 HOL `tame_defs2.hl:172` 是
`upt 1 (sz (FST x))`（长度 `sz-1`）。实测 `List.range' 1 3 = [1,2,3]`、`List.range' 1 0 = []`。
本 W0 用 `List.range' 1 (sz x.1 - 1)`，与 HOL 一致。
**含义**：W1+ 若复用岛内 `splitNormalListSpine`/其下游，会多插一层 `n_list` 迭代；
需先走 DEF-FIX/SF 通道裁决，不要静默对齐岛件。

## 8. 下一笔（W1）起手建议

按依赖序，先做 **变换机器的方程层**（全部在 `Reduction5.lean` 追加，不需要新文件）：

1. `finalList_iff_all`：`finalList L r ↔ r.all (fun d => fList L d == nextEl r d) = true`
   （把 Prop 形与 Bool 反射接起来；`transformList` 的分支判定与 W1 判定互转）。
2. `transformList_eq_of_final` / `transformList_eq_of_not_final`：
   `finalList L r` 真时 `transformList L x (N,r) = (N,r)`，假时等于 `(replace r [split.2] N ++ [split.1], split.2)`。
3. `transformCount_spec`：在 `∃ i, finalList L (rtrans L N r x i)` 前提下，
   用 `minNum_spec` 得「取到 + 最小」——这是 `reduction2`/`reduction3` 反复用的入口。
4. `lm`/`lp` 的 spec（集合非空性来自 `good_list` 的轨道有限性），
   以及 `splitNormalList` 的 `Nodup`/长度传播。

预计 W1 引理面 300–600 行（单笔 ≤450 拆两笔）。**不建议**在 W1 之前碰 `TameSpine`
（环未解，且 §7 的 off-by-one 未裁决）。
