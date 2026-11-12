# DEF-FIX 章程：LocalAuto DAG 声明切面波（2026-11-12，dagcut-w2 车道拟；用户 2026-11-12 已批裁决 ②a）

> 依据：`docs/handoff-2026-11-12.md` §3.2 + §6 裁决表 ②a（**声明切面（DEF-FIX）：批准**
> —— LA38←LA18、LA21←LA16、LA34/LA31←LA18 的纯搬运；保陈述逐字节、零 sorry 增减）；
> 配方来源 `~/c17_backup/lane_snapshots/jcyfmrp-w1/`（`DELIVERY.md` §3、`dag_wave_demo.diff`
> shadow 验证）。AGENTS §2：陈述改动只走 SF 通道、定义改动只走 DEF-FIX 通道——
> 本波**不改任何定义体/陈述**，只改**声明归属模块**与 import 边，属 DEF-FIX 通道。

## 0. 一句话

把 10 个声明沿两条 import 环**逐字节搬模块**（donor 删整块、target 加同一块，
名字/陈述/证明体一字不动），切断 4 条边：`LA38→LA18`、`LA21→LA16`、
`LA31→LA18`、`LA34→LA18`；切断后 `LocalAuto27` 可以 `import LocalAuto21`
（该 import 行本身**不在本补丁**，留给 JCYFMRP 证明波），`CUXVZOZ_p21` 仍标准三。

## 1. 对象与环证据

环（`jcyfmrp-w1/logs/import_cycles.log`，递归 `^import` 闭包，HEAD `0a1ff76d` 同本基线源码）：

```
LA21 -> LA16 -> LA26 -> LA27        （LA21 为 JCYFMRP/CUXVZOZ 证明面所在）
LA21 -> LA38 -> LA18 -> LA27
LA31 -> LA18 -> LA27 ;  LA34 -> LA18 -> LA27 ;  LA28 -> LA34 -> LA18 -> LA27
```

切后终态模拟（`logs/simulate.log`，对 HEAD 全图重算 import 闭包 + SCC）：
**patch-only 零环；LA27+import LA21 零环**；`closure(LA21)` 不再含 LA16/LA18/LA27/
LA31/LA34/LA28；`closure(LA38)` 不再含 LA18/LA27；LA18/LA16 经新增 import 仍能
看见被搬走的声明（下游消费不破）。

## 2. 声明搬迁清单（10 件，全部逐字节；+import 边调整）

| # | 声明 | 性质 | donor（HEAD 位置） | target | 行数 |
|---|---|---|---|---|---|
| 1 | `azimCycle_p18` | `noncomputable def` | LA18:128–136 | **LA38** | 9 |
| 2 | `coplanar_delta_y_zero_p18` | theorem | LA18:435–468 | **LA21** | 34 |
| 3+4 | `periodic_mod_p18` + `periodic2_mod_p18` | theorem ×2 | LA18:1096–1119（连续块，含中间空行） | **LA21** | 24 |
| 5–8 | `dihY222222_p16` / `const1_eq_p16` / `taum_dih_y_aux_p16`（private ×3）+ `taum_dih_y_p16` | 4 件连续块 | LA16:1020–1112 | **LA21** | 93 |
| 9+10 | `w5cC_hedge_of_LocalFan`（LA31:878–889）+ `w5cC_lf2_of_LocalFan`（LA31:891–893） | theorem ×2 | LA31:878–893（连续块，含中间空行） | **LA21** | 16 |

import 边调整（`+` = 新增，`-` = 删除）：

| 文件 | import 变化 | 理由 |
|---|---|---|
| LA38 | **−LA18** | azimCycle_p18 已本地持有（断 `LA38→LA18`） |
| LA21 | **−LA16**；**+XivphksKit +PackingAuto18 +LocalAuto38Bridge +LocalAuto22** | 断 `LA21→LA16`；4 条新边均为无环模块（demo shadow 实测，demo `dag_la21c.log` RC=0） |
| LA31 | **−LA18**；**+LA21 +LA1 +LA5 +LA9 +AzimBridge +LA23 +LA35** | LA31 原经 LA18 网关拿 periodic 对与 6 个模块的传递依赖；改从 LA21/直接 import 取（demo 同款 6 条 + LA21） |
| LA34 | **−LA18**；**+LA21** | LA34 用 LA18 仅为 periodic 两件（`LocalAuto34.lean:7933/7937` 实测唯二使用） |
| LA18 | **+LA21**（下游 consumer 补 import） | LA18 内部 4 处用 `azimCycle_p18`（146/1799/1801/1990）+ 4 处 periodic（1140/1143/1269/1272/1970）改经 LA21→LA38/LA21 传递解析 |
| LA16 | **+LA21**（下游 consumer 补 import） | LA16:1349 用 `taum_dih_y_p16`、LA16:1843 `#print axioms taum_dih_y_p16` 改经传递解析 |

**与 demo 配方的三处必要偏离**（原因与证据）：

1. **搬运（move）而非复制（copy）**。demo 把 `taum_dih_y_p16`、`periodic_mod_p18`
   等同名**复制**进 LA21、donor 原样保留。这在生产上必炸：切边后 `LA16→LA27→LA21`
   与 `LA18→LA27→LA21` 使 donor 的 import 闭包**包含** LA21，donor 自己再声明同名
   公有声明 ⇒ 编译 LA16/LA18 时报 `has already been declared`（同
   `cycle_test_with_stale_olean.log` 43 条同名错误的机制）。demo 只 shadow 编了
   LA27/21/31/34/38，**从未重编 LA16/LA18**，故未暴露。生产版必须 donor 删、target 加。
2. **`w5cC_hedge_of_LocalFan` / `w5cC_lf2_of_LocalFan` 从 LA31 搬进 LA21**（demo 是
   复制进 LA21）。原因同 1：本方案 LA31 import LA21，若 LA21 保留 LA31 公有定理的
   同名副本 ⇒ 编 LA31 时闭包含 LA21 ⇒ 撞名。全树使用测绘（`git grep -w`）证实
   仅 LA21（:4532）与 LA31（内部 18 处）使用这两件；LA31 内部使用改经 import LA21 解析。
3. **LA16/LA18 各补一条 `import LocalAuto21`**（patch 独立成立所必需）。本补丁
   **不含** LA27→LA21 解锁边（按任务边界留给 JCYFMRP 波）；若 LA16/LA18 不补 import，
   它们对被搬走声明的内部使用会 unknown identifier。新增边无环（`logs/simulate.log`）。

零重命名：全程无 `azimCycle_p38` 之类改名；LA38 的 sorry 定理
`PRIOR_TO_LESS_THAN_PI_LEMMA_ALT`（LA38:2522–2523 邻域）陈述行**逐字未动**
（demo 的改名版会动它，这正是 demo NOT FOR LANDING 的原因）。

## 3. 陈述冻结证据（机器自检，RC=0）

`logs/byte_check.log`（脚本 `logs/byte_check.py`，对 patch 触及的 6 个文件比对
HEAD 版 vs patched 版）：

- **SIG 不变量**：6 文件并集 813 条 `^(private )?(theorem|lemma)` 签名行，
  HEAD 与 patched 多重集**完全相等**；逐文件差集恰好 = 上表 10 件搬迁
  （LA16 −4、LA18 −3、LA31 −2、LA21 +9），无任何就地编辑。
- **SORRY 不变量**：并集 91 条含 `sorry` 行完全相等——零 sorry 增减。
- **DEF 不变量**：并集 59 条 `^(noncomputable )?def` 签名行完全相等
  （azimCycle_p18 的 −1/+1 互抵）。
- **搬迁块逐字节**：5 个块（LA16 93 行、coplanar 34 行、periodic 24 行、
  azimCycle 9 行、w5cC 16 行）donor HEAD 文本 vs target patched 文本逐行 EQUAL。
- 零 `axiom`/`native_decide` 增删（diff 全文不含这些词，见 `patch.diff`）。

## 4. 编译验证（shadow farm，全部 `nice -n 19` 单文件，压力级 1）

岛协议：`cp -al .lake/build/lib/lean/Kepler farm/`（7,240 olean 硬链接）→ 编前
`rm farm/<mod>.olean`（防硬链接写回 .lake）→ `LEAN_PATH=farm:$LP lean <file> -o farm/...`。
consumer 用 HEAD 源对 patched farm 只做 typecheck（无 `-o`）。全序列串行。

| 编译对象 | RC | errors | sorry-decls | 备注 |
|---|---|---|---|---|
| LA38（target，断 LA18） | 0 | 0 | 45 | = demo 基线 45（`baseline_la38.log`） |
| LA21（target，断 LA16+搬 9 件） | 0 | 0 | 2 | = LA21 基线 2 |
| LA18（donor，补 import LA21） | 0 | 0 | 10 | 内部 azimCycle `unfold` 等对导入定义照常工作 |
| LA16（donor，补 import LA21） | 0 | 0 | 1 | :1349 使用 + :1843 `#print axioms` 解析正常 |
| LA31（target，断 LA18，补 7 import） | 0 | 0 | 0 | 与 demo 切版一致 |
| LA34（target，断 LA18，补 LA21） | 0 | 0 | 0 | 与 demo 切版一致 |
| **LA27 + import LA21（解锁验证）** | **0** | **0** | 4 | = LA27 基线 4；**该 import 行不进 patch** |
| LA19（consumer of LA18） | 0 | 0 | 29 | 新闭包（含 LA21/LA38）零撞名 |
| LA33（consumer of LA18） | 0 | 0 | 9 | 同上 |
| LA28（consumer of LA34） | 0 | 0 | 2 | 新闭包含 LA21 零撞名 |
| OdxlstcBridge（consumer of LA31） | 0 | 0 | 0 | 同上 |
| VasTuaKit（consumer of LA34） | 0 | 0 | 0 | 同上 |
| TameLp（consumer of LA16） | 0 | 0 | 1 | 同上 |

公理探针（pit 17 纪律：patched `LocalAuto21.olean` 临时装入 `.lake` 再探针，
探针后原 olean 已还原——备份 `backup_LocalAuto21.olean`，逐字节复原）：
`logs/probe_axioms.log`： **`CUXVZOZ_p21`、`CJBDXXN_p21`、`general_482_deformation_p21`、
`taum_dih_y_p16`（新家）全部 = `[propext, Classical.choice, Quot.sound]`（标准三，
零 `sorryAx`）**。

## 5. 不验证项与留给闸门/编排者的验收

- **LocalConcl / Assembly 未重编**（体量决策）：LocalConcl 在 HEAD 就同时 import
  本波全部 6 个模块 ⇒ 其闭包声明集 patch 前后**不变**（搬迁在六模块并集内守恒，
  见 §3 不变量）；Assembly 经 LocalConcl 同证。二者留给编排者闸口的模块构建步。
- 根面 `#print axioms` 由编排者亲跑（AGENTS §4 验收口径 ③）。
- `git apply --check`：PASS（`logs/git_apply_check.log`，相对 HEAD `0eb579b8`）。

## 6. 落库后下一步（不在本补丁）

JCYFMRP 证明波在 LA27 加 `import Kepler.Text.LocalAuto21`（解锁边，本车道已验证
RC=0）+ 证明体搬运；同法可评估 LFLACKU / SCS_6I1 / OCBICBY 的切面
（handoff §5.1）。
