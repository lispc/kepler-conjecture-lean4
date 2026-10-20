# FQN 冲突治理：SphereKit vs PackingAuto18/20/21（2026-09-20）

分支 `wip/pa-conflict-fix`。目标：治理后 `SphereKit` + `PackingAuto18/20/21` +
`IneqClosureDefs` 可以同 import 不撞。

## 0. 口径与方法

扫描器：`lean/scripts/fqn_scan.py`（解析 `namespace`/`section`/`end` 栈 +
`def|theorem|abbrev|opaque|lemma|instance` 声明，剥块注释；`private` 声明
被 Lean 改名 mangling，**不会**跨文件冲突，不计入）。

关键事实（本 toolchain Lean 4.32.2 实测）：**两个导出同名常量的模块在
import 时即报错**（`environment already contains 'X' from 'Y'`），不是等到
引用处才歧义。因此任何一对冲突文件都**无法 co-import**，下游粘合被卡死
是硬错误而非警告。

## 1. 冲突全图统计

全 `lean/Kepler/` 跨文件重复 FQN（非 private）共 **102 条**：

| 簇 | 条数 | 体一致性 | 说明 |
|---|---|---|---|
| `Text/` | 47 | identical 24 / same-signature 12 / divergent 11 | 本任务主战场 |
| `LP/PilotCM204880136538/` | 55 | 全 identical | `Bench.lean` 是 `Data.lean` 的逐字拷贝（+`Assembly` 孪生）；两者从不 co-import，**残留，不治理** |
| `Graphs/` | 0 | — | 扫描器初版的 3 条是 `getLast!` 等 `!` 后缀名的解析误报，已排除 |

`Text/` 47 条全清单（**粗体** = 目标闭包内、本次治理）：

| FQN | 定义位置 | 体一致性 | 处置 |
|---|---|---|---|
| **`Kepler.Text.atn2`** | SphereKit:33, PA18:154, PA20:66, PA21:106 | 逐字相同 | SphereKit canonical；PA18/20/21 改名 |
| **`Kepler.Text.deltaX`** | SphereKit:42, PA18:134 | 逐字相同 | 同上（PA18 改名） |
| **`Kepler.Text.deltaP`** | SphereKit:51, PA18:142 | 逐字相同 | 同上 |
| **`Kepler.Text.chiMsb`** | SphereKit:60, PA18:91, PA25:134 | 逐字相同 | PA18 改名；PA25 残留（§4） |
| **`Kepler.Text.upsX`** | SphereKit:68, PA18:149, PA25:171 | 逐字相同 | 同上 |
| **`Kepler.Text.dihXf`** | SphereKit:92, PA20:85, PA21:125 | 改名孪生（体只差 `deltaXf`/`deltaX4f` vs `deltaX`/`deltaX4` 引用，语义相同） | SphereKit canonical；PA20/21 改名 |
| **`Kepler.Text.dihY`** | SphereKit:99, PA20:90, PA21:130 | 逐字相同 | 同上 |
| **`Kepler.Text.solY`** | SphereKit:105, PA20:94, PA21:134 | 逐字相同 | 同上 |
| **`Kepler.Text.deltaXf`** | PA20:73, PA21:113 | 逐字相同 | PA20 canonical；PA21 改名 |
| **`Kepler.Text.deltaX4f`** | PA20:80, PA21:120 | 逐字相同 | 同上 |
| **`Kepler.Text.volXf`** | PA20:99, PA21:139 | 逐字相同 | 同上 |
| **`Kepler.Text.volY`** | PA20:103, PA21:143 | 逐字相同 | 同上 |
| **`Kepler.Text.vol3r`** | PA20:126, PA21:147 | 逐字相同 | 同上 |
| **`Kepler.Text.vol3f`** | PA20:129, PA21:150 | 逐字相同 | 同上 |
| **`Kepler.Text.gamma3f`** | PA20:138, PA21:159 | 逐字相同 | 同上 |
| **`Kepler.Text.HJKDESR1a_1cell`** | PA20:241, PA21:628 | 逐字相同（均为 sorry；PA21 自述 "dedupe at merge time"） | PA20 canonical；PA21 改名 |
| **`Kepler.Text.MCELL2_SUBSET_AFF_GE`** | PA18:1056, PA21:821 | **语义不同**（见 §3.1） | PA21 canonical；PA18 改名 |
| **`Kepler.Text.ANGLE_GT_PI2`** | PA6:696, PA7:140 | 同陈述；PA6 为 sorry 占位，PA7 已证 | PA7 canonical；PA6 改名 |
| **`Kepler.Text.ARCV_GT_PI2`** | PA6:610, PA7:145 | 同陈述；两侧均有证明（独立移植） | PA7 canonical（同组一致）；PA6 改名 |
| **`Kepler.Text.AZIM_COMPL_EXT`** | PA6:701, PA7:156 | 同陈述；PA6 sorry，PA7 已证 | 同上 |
| **`Kepler.Text.AZIM_EQ_SYM`** | PA6:708, PA7:165 | 同上 | 同上 |
| `Kepler.Text.deltaX4` | SphereKit:74, LocalAuto1:766 | 逐字相同 | 残留（§4） |
| `Kepler.Text.deltaX5` | SphereKit:84, LocalAuto1:776 | 逐字相同 | 残留（§4） |
| `Kepler.Text.leaf` | PA18:73, PA25:131 | 逐字相同 | 残留（§4） |
| `Kepler.Text.ccCell`/`ccPe1`/`ccPe2`/`ccUh`/`cc_pe_exists`/`cc_uh_exists` | PA18 vs PA25 | 逐字相同 | 残留（§4） |
| `Kepler.Text.ccKe` | PA18:123, PA25:164 | 体不同（`hl < √2` 判定写法差异） | 残留（§4） |
| `Kepler.Text.bis` | PA1:434, PA5:65 | 同签名 | 残留（§4） |
| `Kepler.Text.saturated` | PA1:440, PA2:263 | 语义不同 | 残留（§4） |
| `Kepler.Text.CLOSED_BIS_LE`/`KIUMVTC` | PA1 vs PA5 | 同签名 | 残留（§4） |
| `Kepler.Text.BOUNDED/CLOSED/COMPACT/CONVEX_VORONOI_CLOSED`、`DRUQUFE` | PA1 vs PA5 | 体不同 | 残留（§4） |
| `Kepler.Text.AFF_GE_MONO_TRANS` | LocalAuto5:1472, PA18:970 | 语义不同 | 残留（§4） |
| `Kepler.Text.CONDS_IN_CONV2` | LocalAuto5:1374, PA18:1061 | 同签名 | 残留（§4） |
| `Kepler.Text.FINITE_CARD1_IMP_SINGLETON` | LocalAuto5:1818, PA18:1280 | 同签名 | 残留（§4） |
| `Kepler.Text.EMPTY_NOT_EXISTS_IN` | LocalAuto5:1452, PA22:859 | 同签名 | 残留（§4） |
| `Kepler.Text.BIJ_SUM` | PA22:1607, PA3:470 | 语义不同 | 残留（§4） |
| `Kepler.Text.LOCAL_FAN_ORBIT_MAP_EXPLICIT` | LocalAuto2:608, LocalAuto7:438 | 语义不同 | 残留（§4） |
| `Kepler.Text.scsBasicV39`/`scsDiag` | LocalAnchors:65/69, LocalAuto1:615/655 | 语义不同 | 残留（§4） |

## 2. 治理策略

- **canonical 优先 SphereKit**（公共地基；其 doc 自述 "moved here so the
  PA18/PA20/PA21 lanes can share one kit"）。
- PA20/PA21 互为孪生的 kit 块：PA21 文件头自述 "copied from PackingAuto20;
  delete at merge time"，故 **PA20 canonical，PA21 改名**。
- PA6 vs PA7 四定理：PA7 四个全已证（且 PA7 内部 :310 引用
  `ANGLE_GT_PI2`）；PA6 中 `ANGLE_GT_PI2`/`AZIM_COMPL_EXT`/`AZIM_EQ_SYM`
  是 sorry 占位，`ARCV_GT_PI2` 虽有独立证明但与 PA7 重复 → PA7 canonical，
  PA6 四处改名（改名只动声明名与 doc，不动证明体）。
- 命名约定：camelCase 名直接追加模块标签（`deltaP` → `deltaPPA18`）；
  ALL-CAPS 名加下划线（`ANGLE_GT_PI2` → `ANGLE_GT_PI2_PA6`）。

## 3. 逐条决策与改名映射表

### 3.1 语义不同的同名定义（逐条理由）

**`MCELL2_SUBSET_AFF_GE`**（PA18:1056 vs PA21:821）：

- PA18 版：`(V : Set V3) (ul : List V3) : mcell2 V ul ⊆ affGe {hdV ul, hdV ul.tail} {mxi V ul, omegaListN V ul 3}` —— 无 `Packing`/`barV` 假设，sorry 占位，自述出处 "leaf_cell.hl:1870-?"（行号带问号，存疑）。
- PA21 版：带 `(hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)`，用 `elV ul 0/1`（在 `barV V 3` 下与 `hdV` 对齐），**有完整证明**，出处 TSKAJXY3.hl:1419，且被 PA25 引用。
- 决策：PA21 版为 canonical（陈述良构、已证、有下游）；PA18 占位改名
  `MCELL2_SUBSET_AFF_GE_PA18`。PA18 版缺假设、出处存疑，疑似误植，
  后续应整段复核是否删除。

### 3.2 改名映射表（opencode rebase 对齐用）

| 文件 | 旧 FQN | 新名 |
|---|---|---|
| PackingAuto6.lean | `Kepler.Text.ANGLE_GT_PI2` | `ANGLE_GT_PI2_PA6` |
| PackingAuto6.lean | `Kepler.Text.ARCV_GT_PI2` | `ARCV_GT_PI2_PA6` |
| PackingAuto6.lean | `Kepler.Text.AZIM_COMPL_EXT` | `AZIM_COMPL_EXT_PA6` |
| PackingAuto6.lean | `Kepler.Text.AZIM_EQ_SYM` | `AZIM_EQ_SYM_PA6` |
| PackingAuto18.lean | `Kepler.Text.atn2` | `atn2PA18` |
| PackingAuto18.lean | `Kepler.Text.chiMsb` | `chiMsbPA18` |
| PackingAuto18.lean | `Kepler.Text.deltaP` | `deltaPPA18` |
| PackingAuto18.lean | `Kepler.Text.deltaX` | `deltaXPA18` |
| PackingAuto18.lean | `Kepler.Text.upsX` | `upsXPA18` |
| PackingAuto18.lean | `Kepler.Text.MCELL2_SUBSET_AFF_GE` | `MCELL2_SUBSET_AFF_GE_PA18` |
| PackingAuto20.lean | `Kepler.Text.atn2` | `atn2PA20` |
| PackingAuto20.lean | `Kepler.Text.dihXf` | `dihXfPA20` |
| PackingAuto20.lean | `Kepler.Text.dihY` | `dihYPA20` |
| PackingAuto20.lean | `Kepler.Text.solY` | `solYPA20` |
| PackingAuto21.lean | `Kepler.Text.atn2` | `atn2PA21` |
| PackingAuto21.lean | `Kepler.Text.deltaXf` | `deltaXfPA21` |
| PackingAuto21.lean | `Kepler.Text.deltaX4f` | `deltaX4fPA21` |
| PackingAuto21.lean | `Kepler.Text.dihXf` | `dihXfPA21` |
| PackingAuto21.lean | `Kepler.Text.dihY` | `dihYPA21` |
| PackingAuto21.lean | `Kepler.Text.solY` | `solYPA21` |
| PackingAuto21.lean | `Kepler.Text.volXf` | `volXfPA21` |
| PackingAuto21.lean | `Kepler.Text.volY` | `volYPA21` |
| PackingAuto21.lean | `Kepler.Text.vol3r` | `vol3rPA21` |
| PackingAuto21.lean | `Kepler.Text.vol3f` | `vol3fPA21` |
| PackingAuto21.lean | `Kepler.Text.gamma3f` | `gamma3fPA21` |
| PackingAuto21.lean | `Kepler.Text.HJKDESR1a_1cell` | `HJKDESR1a_1cell_PA21` |

下游引用批量跟随（同名换名，体不变，不动证明）：

| 文件 | 跟随改名 |
|---|---|
| LocalAuto1 | `deltaX`→`deltaXPA18`, `upsX`→`upsXPA18` |
| LocalAuto7/16/18/19/21/22/23/25/26/28/31/33/34/35/36/37/38, LocalConcl | 按 §3.2 解析到 PA18 的引用同样换名（`atn2`/`chiMsb`/`deltaP`/`deltaX`/`upsX` → `*PA18`） |
| LocalAuto2 | `solY`→`solYPA20` |
| LocalAuto11 | `atn2`→`atn2PA20`, `dihXf`→`dihXfPA20`, `dihY`→`dihYPA20` |
| PackingAuto25 | 解析到 PA21 的引用换 `*PA21` 名（`atn2`/`dihXf`/`dihY`/`solY`/`deltaXf`/`deltaX4f`/`volY`/`gamma3f`） |

## 4. 残留冲突（本次不治理，记录理由）

以下冲突的双方**从不被同一模块 co-import**（用传递 import 闭包核实），
不阻塞本次目标；但它们同样是 import 时硬错误，后续粘合到这些模块时会再咬：

1. **PA18 vs PA25**（`leaf`/`ccCell`/`ccKe`/`ccPe1`/`ccPe2`/`ccUh`/`cc_pe_exists`/
   `cc_uh_exists`/`chiMsb`/`upsX`）：PA25 是 PA18 的并行孪生（多 sorry 占位）。
   建议方向：PA25 整段删除已上移的定义，import PA18/SphereKit。
2. **SphereKit vs LocalAuto1**（`deltaX4`/`deltaX5`，逐字相同）：LA1 在
   SphereKit 出现前自有一份。建议 LA1 删除本地版、改用 SphereKit。
3. **PA1 vs PA5/PA2**（`bis`/`saturated`/`CLOSED_BIS_LE`/`KIUMVTC`/
   `*_VORONOI_CLOSED`/`DRUQUFE`）：PA1 与 PA5 是并行 lane，部分体不同
   （如 `saturated` 语义不同），需要人工判定，不宜机械改名。
4. **LocalAuto5 vs PA18/PA22**（`AFF_GE_MONO_TRANS`（语义不同）/
   `CONDS_IN_CONV2`/`FINITE_CARD1_IMP_SINGLETON`/`EMPTY_NOT_EXISTS_IN`）。
5. **PA22 vs PA3** `BIJ_SUM`（语义不同）。
6. **LocalAuto2 vs LocalAuto7** `LOCAL_FAN_ORBIT_MAP_EXPLICIT`（语义不同）。
7. **LocalAnchors vs LocalAuto1** `scsBasicV39`/`scsDiag`（语义不同；
   LocalAuto18 文件头已记录 "NEEDS: merge"）。
8. **LP/PilotCM204880136538** `Bench.lean` 逐字复制 `Data.lean` 55 名：
   Bench 是独立 bench 入口，不与 Data co-import；如需根治应让 Bench
   `import` Data 而非拷贝。

## 5. 验证证据

编译环境：worktree 本地 overlay（`.build/lib`，LEAN_PATH overlay 优先，
依赖包取主仓 `.lake` 符号链接的 LEAN_PATH 但**剔除 wip Kepler 缓存路径**，
杜绝 drift 落入），`g4cap` toolchain lean v4.32.2，并发 ≤4。
注意：本 worktree `.build/lib` 里 2026-09-20 07:04 的旧 olean 曾被
wip 源污染（如 LocalAuto1.olean 记录了对 SphereKit 的 import，而当前
main 源无此 import）——本次验证前已删除全部非 Graphs olean 并从
main @ 3283db72 纯净源重建。

- 基线（改名前）：目标闭包 46 模块全部编译绿（SphereKit、PA18、PA20、
  PA21、IneqClosureDefs 及其传递依赖）。co-import 探针在 import 阶段即死：

  ```
  error: import Kepler.Text.PackingAuto18 failed,
    environment already contains 'Kepler.Text.deltaP' from Kepler.Text.SphereKit
  ```

- 基线同时证实 LocalAuto8/14/17/18/22/23/27/30/35/37 等 LA 文件在 main 上
  本来就红（同一 deltaP 冲突，经 LocalAuto1 → PA18 链）——即"已咬伤两次"
  的实锤；这些文件在治理后一并转绿（见下）。

### 5.1 治理后验证

- **改名模块全部编译绿**（overlay 自纯净源重建）：PackingAuto6/18/20/21/25
  及 20 个下游跟随文件（LocalAuto1/2/7/8/11/12/14/15/16/17/18/19/20/21/22/23/
  24/25/26/27/28/29/30/31/32/33/34/35/36/37/38、LocalConcl、PackingConcl）
  全部 `OK`。其中 LocalAuto8/14/17/18/22/23/27/30/35/37、LocalConcl 在 main
  上因本冲突**本来就红**，治理后转绿。
- **co-import 回归探针** `lean/scripts/CoImportProbe.lean`：同时 import
  SphereKit + PackingAuto18/20/21 + IneqClosureDefs，编译绿；全部 canonical
  名（`atn2`/`deltaX`/`deltaP`/`chiMsb`/`upsX`/`dihXf`/`dihY`/`solY`、
  PA7 四定理、PA20 hub kit、`MCELL2_SUBSET_AFF_GE`）唯一解析，改名侧
  `*PA18`/`*PA20`/`*PA21` 同名共存可用。
- `#print axioms` 抽查：`solY`、`dihXf`、`ANGLE_GT_PI2`（PA7 已证）、
  `ATN2_Y_NEG`（PA21，证中引用 `atn2PA21`）、`MCELL2_SUBSET_AFF_GE`
  （PA21 已证）、`solX`（IneqClosureDefs）均只依赖
  `[propext, Classical.choice, Quot.sound]`，**无 `sorryAx` 新增**。
- diff 完整性：`git diff` 全部改动行均含改名标识符或为改名注记 doc
  行，零证明体改动。
- 扫描器复核：目标闭包 46 模块内重复 FQN = **0**（治理前 19 条）；
  全仓 102 → 83（剩余均为 §4 记录的闭包外残留）。
