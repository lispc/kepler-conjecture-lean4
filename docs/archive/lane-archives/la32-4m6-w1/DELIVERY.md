# DELIVERY — lane `la32-4m6-w1`（LA32 / Flyspeck `MIQMCSN.hl` 4M6 五件线性梯子）

## 结论：**0 闭合 — BLOCKED 交付（未写任何证明，目标文件零改动）**

五件全部 BLOCKED。阻断不是策略问题，而是可 `grep` 复核的静态事实：`EXTREMAL_SCS_4M6_p32`
的 HOL 证明体（`MIQMCSN.hl:1855-1991`）逐字消费 `PWEIWBZ`(×3)、`VASYYAU`(×2)、
`TUAPYYU`(×1)、`quad_nonexist_849`(×3)；前三者在 Lean 侧是 LA1 注册表里的
`:= by sorry`，实测 `#print axioms Kepler.Text.VASYYAU_p25` =
`[propext, sorryAx, Classical.choice, Quot.sound]`。后四件经 `EXTREMAL_SCS_4M6_p32`、
in-file `SCS_4T3_IS_SCS_p32`（`LocalAuto32.lean:247` 仍是 `sorry`）、以及只存在于
**未 import** 的 LA33 的 `MM_4M6_IMP_STAB_4M6` / `SET_STAB_4M6_ARROW_4T5` /
`SCS_4T5_IS_SCS` 传递阻塞。简报 §1 的判据（"依赖树显示本波某件被根卡住 → 如实标 BLOCKED"）
在此命中：4M6 梯子与上一车道 4M7/4M8 共享同一批根（`VASYYAU_concl`/`TUAPYYU_concl`/
`PWEIWBZ_concl`）。

- **own-sorry：60 → 60**（无变化）
- **整文件 RC=0 / `: error:` 0 / `` `sorry` `` 声明 60 / warning 81**（基线复现，`logs/baseline.log`）
- **目标文件 sha256 前后一致** `385fa907275d5469007e19ead9596da05ed54739a3d9b017e6168e0ed5581779`
  （`8c003d0d` 与当前 `45c6d93c` 上同值；本车道期间 HEAD 被他车道推进，目标文件未变）
- **主仓零改动、零未跟踪**（`git status --porcelain` = 0 行）
- **无 kit、无 `Kit-draft`**：零 diff，没有产生任何可编译的助件；`git apply --check` 无需执行
- 五件目标基线公理面实测均为 `[propext, sorryAx, Classical.choice, Quot.sound]`
- K-REACH：`NWDGKXH_p32` 未闭合，锥内 SORRIED 不减；COVERAGE/SHIMS/ORPHANS/K-AXIOM 无漂移

## 1. 闭合件表

**空。** 本波没有闭合任何声明。

| # | 件 | 状态 |
|---|---|---|
| — | — | 无 |

## 2. 基线读数（命令原文 + 值）

```sh
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4
LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt) nice -n 19 \
  script -q /Users/zhangzhuo/c17_backup/lane_snapshots/la32-4m6-w1/logs/baseline.log \
  lean lean/Kepler/Text/LocalAuto32.lean
```

| 命令 | 读数 |
|---|---|
| 上条命令后 `echo "RC=$?"` | **RC=0** |
| `tr -d '\r' < logs/baseline.log \| grep -c ': error:'` | **0** |
| ``tr -d '\r' < logs/baseline.log \| grep -c 'declaration uses `sorry`'`` | **60** |
| `tr -d '\r' < logs/baseline.log \| grep -c ': warning:'` | **81** |
| `wc -l lean/Kepler/Text/LocalAuto32.lean` | **1583** |

## 3. 残件精确缺口表（逐件）

目标行号（当前 HEAD `45c6d93c`，文件与简报基线 `8c003d0d` 逐字节相同）：

| 件 | 声明行 | `:= by` | `sorry` |
|---|---|---|---|
| `EXTREMAL_SCS_4M6_p32` | 993 | 997 | 998 |
| `BB_4M6_IMP_scs_4T3_p32` | 1003 | 1006 | 1007 |
| `MM_4M6_IMP_MM_4T3_p32` | 1012 | 1015 | 1016 |
| `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32` | 1020 | 1024 | 1025 |
| `NWDGKXH_p32` | 1030 | 1031 | 1032 |

### 3.1 `EXTREMAL_SCS_4M6_p32`（LA32:993；HOL `MIQMCSN.hl:1855-1991`）

HOL 证明体的直接输入（逐条核对原文）：

| HOL 引用 | Lean 对应 | 状态 |
|---|---|---|
| `SCS_4M6_IS_SCS` | `SCS_4M6_IS_SCS_p29` LA29:1103 | 已证，标准三（probe4） |
| `MMS_IMP_BBS` | `MMS_IMP_BBS_p28` LA28:194 | 已证，标准三（probe2） |
| `BB_VV_FUN_EQ` | `BB_VV_FUN_EQ_p26` LA26:198 | 已证，标准三（probe2） |
| `PWEIWBZ` ×3 | `PWEIWBZ_p25` LA25:2530 → `PWEIWBZ_concl` LA1:4903（`sorry` :4910） | **sorryAx**（probe1/2） |
| `VASYYAU` ×2 | `VASYYAU_p25` LA25:2541 → `VASYYAU_concl` LA1:4913（`sorry` :4922） | **sorryAx**（probe2） |
| `TUAPYYU` ×1 | `TUAPYYU_p25` LA25:2251 → `TUAPYYU_concl` LA1:4880（`sorry` :4889） | **sorryAx**（probe1） |
| `quad_nonexist_849` ×3 | `quad_nonexist_849_p16` LA16:799 | 已证，但 **不在 LA32 import 闭包**（probe3 `unknown identifier`） |
| `SCS_4M6_BASIC` / `K_SCS_4M6` | LA20:588 / LA20:624 | 已证，标准三（probe4） |
| `SCS_4M6_STAND_OR_PRO` / `SCS_4M6_STAND` / `h0_LT_B` / `h0_CSTAB_LT_4` | LA32:960 / :980 / :906 / :987 | 已证，标准三（probe2/4） |

**精确缺口**：`PWEIWBZ_concl`、`TUAPYYU_concl`、`VASYYAU_concl` 三个 LA1 注册表
`sorry`（均实测 `sorryAx`）；外加 `quad_nonexist_849_p16` 的可达性（LA16 未 import，
零新 import 下不可用）。结论不能由闭包内已证的逐边区间/表格引理替代——HOL 把等号
（`dist = 2` / `dist = cstab`）全部交给上述三个深层引理，文件自己的 NEEDS 注释也写
`VASYYAU (str case split)`。

### 3.2 `BB_4M6_IMP_scs_4T3_p32`（LA32:1003；HOL `MIQMCSN.hl:1992-2030`）

- 直接缺口：`EXTREMAL_SCS_4M6_p32`（3.1 全部根）。
- 其余：`MMS_IMP_BBS_p28` 已证；`scs4T3` 的逐槽 `BBsV39` 表匹配用的是 in-file
  `funlistV39`/`scs4M6'` 展开（`h0_LT_B_SCS_4M6_p32` 的 proof 已示范该写法），无额外根。

### 3.3 `MM_4M6_IMP_MM_4T3_p32`（LA32:1012；HOL `MIQMCSN.hl:2031-2047`）

- 直接缺口：`BB_4M6_IMP_scs_4T3_p32`（→ 3.1）+ `SCS_4T3_IS_SCS_p32`（LA32:247，**in-file `sorry` :248**，实测 `sorryAx`）。
- 其余：`XWNHLMD_MM_p26`（LA26:1642）标准三；`SCS_4T3_BASIC_p32`（LA32:338）、
  `K_SCS_4T3_p32`（LA32:342）、`MMS_IMP_BBS_p28` 标准三。

### 3.4 `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`（LA32:1020；HOL `MIQMCSN.hl:2048-2109`）

`scsArrowV39` 展开为两合取：

1. `∀ s ∈ S2, isScsV39 s`，`S2 = {scs4T3} ∪ {scsStabDiagV39 scs4M6' i j | scsDiag 4 i j}`：
   - `isScsV39 scs4T3` = `SCS_4T3_IS_SCS_p32` LA32:247 **sorry**；
   - stab 成员可由 `YRTAFYH_p17`（LA17:1129，标准三）+ `SCS_4M6_IS_SCS_p29` +
     `SCS_4M6_BASIC` + `K_SCS_4M6` + `h0_LT_B_SCS_4M6_p32` 的 `a ≤ cstab` 取得（无需 LA33）。
2. `(∀ s ∈ S1, MMsV39 s = ∅) ∨ ∃ s ∈ S2, MMsV39 s ≠ ∅`：
   - 若 `MMsV39 scs4M6' = ∅`，左支；
   - 否则取 `v ∈ MMsV39 scs4M6'`，按 HOL 再分：全对角 `> cstab` 支需
     `MM_4M6_IMP_MM_4T3_p32`（→ 3.3 → 3.1），某对角 `≤ cstab` 支需
     `MM_4M6_IMP_STAB_4M6` —— **LA32 无此声明；仅 LA33:4316 `_p33`**（probe3 `unknown identifier`，
     其依赖 `MM_STAN_p33`/`BB_STAN_p33` 同在 LA33，均不在 import 闭包）。
- **精确缺口**：3.3 全部根 + in-file `SCS_4T3_IS_SCS_p32` + `MM_4M6_IMP_STAB_4M6` 不可达。

### 3.5 `NWDGKXH_p32`（LA32:1030；HOL `MIQMCSN.hl:2110-2129`；TSV 锥内唯一件）

- 直接缺口：`SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32`（3.4）。
- 中继 `FZIOTEF_TRANS`（LA1:2181）、`FZIOTEF_UNION`（LA20:1379）、`FZIOTEF_REFL`（LA1:2171）均标准三；
  但还需 `scsArrowV39 ({scs4T3} ∪ stabset) {scs4T3, scs4T5}`：
  - `isScsV39 scs4T5`：**LA32 无声明**；仅 LA33:1492 `_p33`（probe3 `unknown identifier`）；
  - `SET_STAB_4M6_ARROW_4T5`：**LA32 无声明**；仅 LA33:4298 `_p33`，其链
    `SET_EQ_DIAG_STAB_4M6_p33` / `STAB_4M6_02_ARROW_4T5_p33` / `STAB_4M6_13_ARROW_4T5_p33` /
    `SCS_4T5_IS_SCS_p33` / `FZIOTEF_BOTH_p33` 全在 LA33（不在闭包）。
- **精确缺口**：3.4 全部根 + `isScsV39 scs4T5` + `SET_STAB_4M6_ARROW_4T5` 及其 LA33 链不可达。

## 4. 根节点与实测公理面

| 根 | 位置 | `#print axioms` 实测（全名） |
|---|---|---|
| `Kepler.Text.TUAPYYU_concl` | LA1:4880，`sorry` :4889 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `Kepler.Text.PWEIWBZ_concl` | LA1:4903，`sorry` :4910 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `Kepler.Text.VASYYAU_concl` | LA1:4913，`sorry` :4922 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `Kepler.Text.WKZZEEH_concl`（VASYYAU 的 HOL 内部依赖） | LA1:4892，`sorry` :4900 | 未单独探测（同族 `sorry`；`VASYYAU_concl` 体为裸 `sorry`） |
| `Kepler.Text.SCS_4T3_IS_SCS_p32` | LA32:247，`sorry` :248 | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| LA33 簇 `STAB_4M6_SCS_p33` / `SCS_4T5_IS_SCS_p33` / `MM_4M6_IMP_STAB_4M6_p33` / `SET_STAB_4M6_ARROW_4T5_p33` | LA33:3070 / 1492 / 4316 / 4298 | **不在 import 闭包**（probe3 `unknown identifier`） |
| `Kepler.Text.quad_nonexist_849_p16` | LA16:799（已证） | **不在 import 闭包**（probe3 `unknown identifier`） |

已证且标准三（probe2/4 原文）：`VASYYAU_p25` **除外**；`MMS_IMP_BBS_p28`、
`BB_VV_FUN_EQ_p26`、`STAB_MOD`、`YRTAFYH_p17`、`XWNHLMD_MM_p26`、`SCS_4M6_IS_SCS_p29`、
`SCS_4M6_BASIC`、`K_SCS_4M6`、`SCS_4M6_STAND_OR_PRO_p32`、`h0_LT_B_SCS_4M6_p32`、
`SCS_4M6_STAND_p32`、`h0_CSTAB_LT_4_p32`、`SCS_4T3_BASIC_p32`、`K_SCS_4T3_p32`、
`FZIOTEF_TRANS`、`FZIOTEF_UNION`、`FZIOTEF_REFL` 全部标准三。

## 5. 与分诊报告的三处事实冲突（重要）

1. **`VASYYAU_p25` 不是干净前置**。`RANKED.md` 车道 3 的"前置全绿"清单把
   `VASYYAU_p25`（LA25:2541）列为已证；实测其体是 `VASYYAU_concl`（LA1:4913
   `:= by sorry`），`#print axioms Kepler.Text.VASYYAU_p25` 含 `sorryAx`。
2. **`SET_STAB_4M6_ARROW_4T5_p33`（LA33:4298）不可用**：LA33 不在 LA32 的 import 闭包
   （LA32 imports: `LocalAuto1/17/20/23/29` + Mathlib；probe3 对 `_p33` 全名报
   `unknown identifier`），零新 import 约束下不能引用。
3. **`SCS_4T3_IS_SCS_p32`（LA32:247）是 in-file `sorry`**，而它是 3.3/3.4/3.5 的 `S2`
   合取 `isScsV39 scs4T3` 的唯一来源；分诊未把它列为风险。

分诊的失败模式：只核了声明存在性/文本，没有核 `#print axioms` 与 import 闭包可达性。

## 6. 搬债审计（`docs/e2e-reachability-map.tsv`，行数 = grep 命中数）

| 名字 | 命中行数 |
|---|---|
| `EXTREMAL_SCS_4M6_p32` | 0 |
| `BB_4M6_IMP_scs_4T3_p32` | 0 |
| `MM_4M6_IMP_MM_4T3_p32` | 0 |
| `SCS_4M6_ARROW_SCS_4T3_STAB_4M6_p32` | 0 |
| `NWDGKXH_p32` | **1**（`:100 Kepler.Text.LocalAuto32  Kepler.Text.NWDGKXH_p32  parent=Kepler.Text.NWDGKXH_discharged`） |
| `VASYYAU` / `PWEIWBZ` / `TUAPYYU` | 0 / 0 / 0 |
| `SCS_4T3_IS_SCS_p32` | 0 |

**本波没有新增任何引用**（零编辑），因此没有搬债动作。拟用但被拒的候选引用
（`VASYYAU_concl`/`TUAPYYU_concl`/`PWEIWBZ_concl`）在锥外（0 行），且本身 `sorryAx`，
未进任何证明体。

## 7. 解锁判据（按依赖序）

1. 关闭 LA1 注册表三根：`PWEIWBZ_concl`（LA1:4903）、`TUAPYYU_concl`（LA1:4880）、
   `VASYYAU_concl`（LA1:4913），以及 VASYYAU 的 HOL 内部依赖 `WKZZEEH_concl`（LA1:4892）；
   闭后须复核 `#print axioms` 为标准三。
2. 让 `quad_nonexist_849_p16` 在 LA32 可用：要么按 BFS 无环 + 全文件漂移核开放
   `import Kepler.Text.LocalAuto16`（本车道约束下禁止），要么把 `quad_nonexist_849_p16`
   与 `DELTA_Y_POS_4POINTS_p16` 移植进 LA32（其体只消费 `main_nonlinear_terminal_v11`
   的 `8495326405` 项，LA1 内可达）。
3. 证明 in-file `SCS_4T3_IS_SCS_p32`（LA32:247）；LA33:1430 的 `_p33` 孪生依赖
   `isScs_mkFunlist_p33`（同样不在闭包），不能直接抄。
4. 让 LA33 簇可用（import 或移植）：`MM_4M6_IMP_STAB_4M6`（LA33:4316）、
   `STAB_4M6_SCS`（LA33:3070）、`SCS_4T5_IS_SCS`（LA33:1492）、
   `SET_STAB_4M6_ARROW_4T5`（LA33:4298）及其 `STAB_4M6_02/13_ARROW_4T5` / `SET_EQ_DIAG_STAB_4M6` 链。
5. 以上齐备后，按 HOL 顺序即可执行：EXTREMAL → BB_4M6 → MM_4M6 / ARROW → NWDGKXH。

## 8. 预算与工件

- 工具调用约 45 次；墙钟约 40 min（`13:13`–`13:55` 量级）；未触发中途简报阈值（~55）。
- 工件：`$S/DELIVERY.md`、`$S/Evidence.md`、`$S/Work.lean`（= HEAD 原文，sha 一致）、
  `$S/logs/{baseline,probe1,probe2,probe3,probe4}.log`。
- 无 `kit-*.diff`（零 diff）；无 `Kit-draft-la32-4m6-w1.lean`（未产生助件）。
- 归档：`docs/archive/lane-archives/la32-4m6-w1/{DELIVERY.md,Evidence.md}`（`git add`，
  主仓 tracked 改动仅此二文件）。
