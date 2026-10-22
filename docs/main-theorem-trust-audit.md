# 主定理可信基座与重要边界清点（2026-10-22，只读审计）

> 目的：回答两个问题——(1) 当前 `Kepler.the_kepler_conjecture_e2e` 的
> `#print axioms` 里，到底哪些是"已知占位/特许计算"，哪些是"隐藏的弱形或
> 邻近债务"；(2) 我们正在推的 AJRIPQN / QZKSYKG2 / SLTSTLO2 / PA24
> 等战线，哪些真的在主定理的 import 锥内。
>
> 证据以 2026-10-21 的脊柱探针（`DEBT.md` §主定理可达债务）为基线；本审计
> 用 import 图 + 声明引用做**结构性**核对，不替代 Lean 级 reachability 探针。
> 文中 `[已核]` = 本次 grep/读文件确认；`[待核]` = 需要声明级依赖遍历。

## 0. 结论速览

1. **"主定理只剩 3 个接口"是顶层归因，不是完整债务图。** `Assembly` 直接
   import `PackingAuto21`/`PackingAuto25`，而 PA21 import PA17、PA25 又直接
   引用 `AJRIPQN`。因此 AJRIPQN 链（QZKSYKG2、SLTSTLO2、DDZUPHJ、
   QZKSYKG1 等）**很可能已经在 e2e 锥内**；PA25 自身还有 86 个 direct sorry。
   需要一次声明级依赖遍历把"在锥内/不在锥内"钉死 `[待核]`。
2. **PackingConcl / PA24 / REUHADY1 不在当前 e2e 锥内。** `Assembly` 不 import
   `PackingConcl`（全仓零 importer），也不 import `PackingAuto24`；PA25 也不
   import PA24。REUHADY1(d)、PA24 的 AJRIPQN inherited taint、以及
   PackingConcl 的 7 个 direct sorry 属于**邻近的 pack_concl 合并层**，
   不是当前 `the_kepler_conjecture_e2e` 的证明路径 `[已核]`。
3. **43,078 个 LP 叶户当前不在锥内。** `linearProgrammingResults` 是真推导，
   但它的唯一债点是 `lpArchiveCertificatesDebt`（Assembly:6040，单点 sorry）。
   43k LP 叶户只有在填实这个债点后才会进入主定理公理锥 `[已核]`。
4. **624 条 shard 公理是主定理唯一的非 sorry 可信计算。** 它们来自
   `goodListArchive`（19,715 张图 / 23 个 `GoodListShard*` 分片，
   `native_decide`，DECISIONS.md 2026-08-10 scoped exception）；内核不验证
   生成器，只验证公理后的组合器 `[已核：Assembly:6226 docstring + DEBT]`。
5. **最危险的不是已知占位，而是"接口填实后静默接入"的弱形/副本。**
   `DUUNHOR_concl` 前提加强、`MEASURE_NEGLIGIBLE_SYMDIFF` 只有不等式替身、
   `qzksykg1_p17`/`qzksykg2_p17` 副本、`MXI_EXISTS_concl` 成环、
   `RVFXZBU2_concl` shim（R3 家族）——它们当前多在邻近层或 off-path，
   但一旦接线，必须先逐条确认"逐字/可回退/不引入 sorryAx" `[已核：文件位置]`。

## 1. 当前 e2e 锥的骨架

```
Kepler.the_kepler_conjecture_e2e          Final.lean
└─ Assembly.the_kepler_conjecture_from_interfaces   Assembly.lean:6243
   └─ assembly hNL hLP hTC                Assembly.lean:6235
      ├─ hNL : TheNonlinearInequalities   Assembly.lean:261
      │  ├─ pack_nonlinear_non_ox3q1h     PA21:963 (def; 六分量之一)
      │  ├─ ox3q1hP25                     PA25
      │  ├─ main_nonlinear_terminal_v11   LocalAuto1
      │  ├─ LpIneqs / PackIneqDefA / KcblrqcIneqDef
      │  └─ nli* 具名骨架: 6 分量 + 14 个开放节点（Assembly §2a' 注记）
      ├─ hLP : LinearProgrammingResults   Assembly.lean:1123
      │  └─ linearProgrammingResults      Assembly.lean:6085
      │     └─ lpArchiveCertificatesDebt  Assembly.lean:6040  [单点 sorry]
      └─ hTC : TextCapstone               Assembly.lean:1149
         └─ textCapstone (真证明脚本)      Assembly.lean:6094
            ├─ PACKING_CHAPTER_MAIN_CONCLUSION  PA25:8380
            │  ├─ RDWKARC_concl / OXLZLEZ / TSKAJXY  [PA25 内部]
            │  └─ AJRIPQN                     PA17:929（PA25:234/2876/5071 引用）
            ├─ nonlinear_imp_lp_main_estimate_p16  LocalAuto16
            ├─ tame_classification             Phase 2 已证
            └─ goodListArchive                 Assembly:6226
               └─ 19,715 图 / 23 shards / 624 条 native_decide 公理
```

关键 import 事实 `[已核]`：
- `Assembly` imports `PackingAuto2/18/21/25`、`LocalAuto16`、`TameLp` 等；
- `PackingAuto21` imports `PackingAuto17`；
- `PackingAuto25` imports `PackingAuto21`，并直接引用 `AJRIPQN`；
- `Kepler.Statement` 只 import Mathlib，不接入 PackingConcl。

## 2. 三个接口的精确陈述与当前债点

| 接口 | 定义 | 当前证明 | 债点 | HOL |
|---|---|---|---|---|
| `TheNonlinearInequalities` | Assembly:261 | `nonlinearInequalities` Assembly:6076 六分量显式装配 | 分量 1 真；`nliOx3q1h`/`nliMainNonlinearTerminalV11`/`nliLpIneqs`/`nliPackIneqDefA`/`nliKcblrqcIneqDef` 均 sorry；另有 14 个开放骨架节点 | the_main_statement.hl:55-59 |
| `LinearProgrammingResults` | Assembly:1123（`LinearProgrammingResultsOn` :1117） | `linearProgrammingResults` Assembly:6085 真推导 | `lpArchiveCertificatesDebt` Assembly:6040 单点 sorry；43k LP 叶户尚未接入 | the_main_statement.hl:47-53 |
| `TextCapstone` | Assembly:1149 | `textCapstone` Assembly:6094 真证明脚本 | 消费 PA25/AJRIPQN/LocalAuto16/TameSpine 占位；PA25 有 86 direct sorry `[待核 reachability]` | the_main_statement.hl:170-175 |

`goodListArchive`（Assembly:6226）已闭合：19715 图、23 个
`GoodListShard*` 分片、纯内核组合器 `goodListArchiveAll`。它是 624 条
shard 公理的来源。

## 3. 在锥内 vs 邻近层（本次审计的核心区分）

### 3.1 很可能在 e2e 锥内（需声明级 reachability 确认）

- **AJRIPQN 链**：PA25 的证明引用 `AJRIPQN`（PA25:234/2814/2876/5071），
  而 `AJRIPQN` 的装配消费 QZKSYKG1/QZKSYKG2/SLTSTLO2/DDZUPHJ/
  `RVFXZBU_p14`。因此 QZKSYKG2/SLTSTLO2/DDZUPHJ/QZKSYKG1 的证明
  **直接减少主定理的 sorryAx**，不只是 PA24 的旁支。
- **PA25 的 86 direct sorry**：其中被 `PACKING_CHAPTER_MAIN_CONCLUSION`
  及其 `RDWKARC_concl`/`OXLZLEZ`/`TSKAJXY` 消费的部分在锥内；其余可能是
  backfill/off-path，需要逐声明遍历。
- **PA17 的 AJRIPQN 本体**：PA17 direct sorry = 0，但 `AJRIPQN` 的
  axiom cone 仍带 SLTSTLO2/DDZUPHJ/QZKSYKG1/QZKSYKG2 的 sorryAx
  （B2 已把 RVFXZBU 换成 PA14 的 clean 版）。

### 3.2 不在当前 e2e 锥内（邻近债务）

- **PackingConcl（7 direct sorry）**：`MXI_EXISTS_concl_discharged`
  （:337/:343）、`RVFXZBU1_concl_discharged`（:380/:384）、
  `RVFXZBU2_concl_discharged`（:388/:393）、
  `RVFXZBU3_concl_discharged`（:400/:405）等。全仓**零 importer**；
  Assembly 不 import 它 `[已核]`。
- **PA24 / REUHADY1(d)**：PA24 direct sorry = 0（SF-46/47 后），但
  `p24_wedge_witness_of_trace` 仍带 AJRIPQN inherited sorryAx；
  PA24 只被 PackingConcl import，不在 Assembly 锥内 `[已核]`。
- **43,078 LP 叶户**：`linearProgrammingResults` 的 `lpArchiveCertificatesDebt`
  填实前不进入锥。填实后，锥会一次性扩张到 43k 叶户 + LP 检查器公理，
  这是未来最大的一次锥扩张。
- **TameSpine 其余章节**：`textCapstone` 消费的是 PA25 的
  `PACKING_CHAPTER_MAIN_CONCLUSION`，不是 TameSpine 的 `TameList*` 模块；
  TameSpine 的战果通过 PA21/PA25 的 `pack_nonlinear_non_ox3q1h` 分量
  间接进入（需 reachability 确认）。B3 D 链是长线，但不是当前 e2e 的
  唯一入口。

## 4. 弱形 / 替身 / shim 清单（按风险排序）

| 件 | 位置 | 形态 | 当前在 e2e 锥？ | 风险/动作 |
|---|---|---|---|---|
| `DUUNHOR_concl` | PA2:3504 | 比 pack_concl 多 `Packing`/`saturated` 前提 | 经 PA17 stage 3，很可能在 | 不是逐字 pack_concl；若最终要逐字接口，另立 `_verbatim`，不要改现有件 |
| `p17_measure_sdiff_ge` | PA17:297 | 只有 `volume s = 0 → volume (s \ t) ≤ volume (t \ s)` 型不等式，非 HOL `MEASURE_NEGLIGIBLE_SYMDIFF` | 经 PA17 stage 3，很可能在 | 确认用途足够；不足则补逐字件 |
| `RVFXZBU` (PA10) | PA10:413 | weak-permutes + i=3 sorry | **否**（B2 后 PA17 改用 PA14 `RVFXZBU_p14`） | off-path orphan；DEBT 记账保留，不再消费 |
| `RVFXZBU_p14` | PA14:1102 | 带 `hfix`，i=0/1/2/4 + B1 收 i=3 | 是（PA17 hRV） | clean；探针标准三零 |
| `QZKSYKG1` | PA14:1243 | SF-20 hfix 已应用；仍 sorry | 是（AJRIPQN hQ1） | B3 目标 |
| `QZKSYKG2` | PA14:1286 | SF-38 tail-fixed；k=2 在飞；k=3/4 待 | 是（AJRIPQN hQ2） | 当前 QZKSYKG2 k=2 车道 + 后续 k=3/4 |
| `qzksykg1_p17`/`qzksykg2_p17` | PA17:236/259 | PA14 件的私有转发副本 | 是（PA17 内部） | PA14 本体落地后删除副本，避免双账 |
| `MXI_EXISTS_concl` | PA2:5473 | pack_concl 接口；PA11 `mxiExplicit` 消费（成环） | 经 PA17？`MXI_EXPLICIT` 在 PA12，PA17 stage 3 | 成环未解；列入 shim 清理批 |
| `RVFXZBU2_concl` | PA2:5496 | 无 twin 的 pack_concl 接口 | 否（PackingConcl:388 桥在邻近层） | 列入 R3/shim 盘点；PA24 `p24_edgeX_of_leaf23` 消费其桥 |
| `RVFXZBU3_concl` | PA2:5507 | twin mismatch（PA10 只覆盖 i≤4） | 否 | off-path；DEBT 记账保留 |
| PA10 剩余 3 sorry | PA10:488/604/608 | RVFXZBU i=3 / YNHYJIT i=2/3 | 否（PA14 已重落 RVFXZBU/YNHYJIT i=3） | off-path；YNHYJIT i=2 待 S₂ kit |

## 5. 建议的验证动作（按优先级）

1. **P0 — 声明级 reachability 地图（1 个只读车道或主 agent 脚本）**：
   从 `the_kepler_conjecture_e2e` 出发遍历 proof term 的常量依赖，输出
   "每个 sorryAx 来源声明 + 是否可达"的清单。重点确认：
   `PACKING_CHAPTER_MAIN_CONCLUSION` 是否真的消费 `AJRIPQN` 与 PA25 的
   哪些 sorry；`textCapstone` 的 86+2+... 个导入 sorry 中哪些在路径上。
   这会把"3 接口"归因升级为可审计的债务图。
2. **P0 — 624 shard 公理 manifest + 抽样 replay**：把
   `GoodListShard*` 23 个分片的公理名、图数、生成器版本、复核命令写成
   manifest；抽 10% 分片用 kernel 路径重放，确认 `ofReduceBool` 族无异常。
3. **P1 — LP 端到端审计**：在填 `lpArchiveCertificatesDebt` 之前，先验
   43,078 个 LP 叶户的证书格式、Farkas 检查器公理面、抽样 replay；
   否则一次接线会让主定理锥从 3+624 跳到 43k。
4. **P1 — 逐接口 HOL 陈述对照**：把 `TheNonlinearInequalities` /
   `LinearProgrammingResults` / `TextCapstone` 三个 def 与
   the_main_statement.hl 的原文并排，补进 `docs/statement-fidelity.md`
   的接口节；同时确认 `DUUNHOR_concl` 的前提加强不影响最终接口。
5. **P2 — shim 清理批**：`MXI_EXISTS_concl` 成环、`RVFXZBU2_concl`
   R3 家族、`qzksykg*_p17` 副本、PA10 off-path 三 sorry，统一入
   `docs/e2e-debt-map.md` 的邻居节，标"在锥/不在锥/替代路"。

## 6. 与当前战线的对应

- **QZKSYKG2 k=2 / SLTSTLO2 / DDZUPHJ / QZKSYKG1**：若 reachability 确认
  AJRIPQN 在 e2e 路径上，这些是**直接的主定理债务削减**，优先级高于
  PA24/REUHADY1（后者当前只在 PackingConcl 邻近层）。
- **PA24/REUHADY1**：不是"不重要"，而是"当前 e2e 不 import"；它是
  pack_concl 合并层的核心，需要在 PackingConcl 接线前完成，但不阻塞
  e2e 主定理。这个区分应写进下一版 `docs/e2e-debt-map.md` 的派工依据。
- **gen-10 / W8**：与 e2e 公理面正交（Phase 2 可信计算），但 624 shard
  公理与 251k 树是最终可信基座的一部分；gen-10 的 opt-in 落地不改变
  公理面，只改变计算成本。

## 7. 出处

- `DEBT.md` §主定理可达债务（2026-10-21 11:27 脊柱探针，main @ ea42f97f）。
- `lean/Kepler/Assembly.lean`：261（NLI def）、1117/1123（LPR）、1149
  （TextCapstone）、6040（lpArchiveCertificatesDebt）、6076/6085/6094
  （三接口证明）、6226（goodListArchive）、6243（e2e 装配）。
- `lean/Kepler/Final.lean`（e2e 定理）。
- `lean/Kepler/Text/PackingAuto25.lean`：8380（PACKING_CHAPTER_MAIN_CONCLUSION）、
  234/2814/2876/5071（AJRIPQN 引用）。
- `lean/Kepler/Text/PackingConcl.lean`：337/343、384、388/393、400/405
  （四个 `*_concl_discharged` sorry）。
- `docs/phase6-spine.md`、`docs/statement-fidelity.md`、`docs/scouts/ajripqn-scout.md`。
