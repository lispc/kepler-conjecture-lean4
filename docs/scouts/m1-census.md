# m1-census — M1 全库 sorry 总普查（清账底账）

- 基线：主仓 `63a3bbeec980d3b7bf8a497628c26c8b477a13a7`（main，2026-10-28 12:12 +0800），
  工作树实测（含未提交改动：LocalAuto1/LocalConcl 修改、GiFactorization.lean 未跟踪）。
- 方法：python3 只读扫描（`scan_sorry.py`）——剥离 Lean 嵌套块注释 `/- -/`、行注释、
  字符串字面量后逐 token 普查；逐处定位声明（`scan_file` 声明区间表），按声明体
  `:= (by)? sorry` 全匹配判语句级，否则 tactic 级。发射产物按文件头
  `机器生成/勿手改/machine generated, do not edit` 实测判定。
- 主仓零写入、零构建、零锁。

## 0. 一行总数

**全库真实 sorry 44,293 处**（231 文件 / 44,291 声明；语句级 44,255 + tactic 级 38）
＝ 发射产物 42,889（96.8%）＋ 手写 1,404（M0 直源 151 + M1 独有 1,253）。

## 1. 分布统计

### 1.1 粗口径 vs 实测

| 口径 | 数 | 说明 |
|---|---|---|
| rg 行口径 | 45,228 行 / 371 文件 | 含注释提及 |
| rg token 口径 | 45,252 | 24 行含 2+ 处 |
| **实测（剥注释/字符串）** | **44,293 处 / 231 文件** | 本账口径 |
| 注释噪声 | 935 处 / 369 文件（2.1%） | 最大：PA24 52、PA23 49、Assembly 28、LocalConcl 24、PackingConcl 23 |

实债为 0 但 grep 有命中的典型：`PackingAuto23.lean`（49 全注释）、`PackingAuto24.lean`
（52 全注释；其直 sorry 已于 2026-10-20 十三发波收口 1→0，文档部分滞后）、
`IneqClosureDefs.lean`（8）、`CertG.lean`/`CertTM.lean`（注释自述 "No sorry"，属实）、
`Interval/*` 17 文件、`Graphs/Sanity`、`Geom/SimplexVolume`、`lean/scripts/*` 5 文件、
`Final.lean`、`LPIds/LPAll/LPCert/LPLeafInfeas00`、`GiFactorization.lean`（未跟踪件，
注释自述零 sorry）。

### 1.2 语句级 / tactic 级

| 级 | 处 | 说明 |
|---|---|---|
| 语句级（声明体即 stub） | 44,255 | LP 叶全属此类；手写侧为 `*_concl`/bank 一行桩 |
| tactic 级（证体内嵌） | 38 | 手写 M1 37 + M0 直源 1（LA22 `OCBICBY_p22`:1936，同声明 2 处） |

多 sorry 声明仅 2 个：`LocalAuto19.sol0Bounds_p19`（2）、`PackingConcl.OXLZLEZ_concl_discharged`（2）。

### 1.3 按 class（M0 / M1 / 发射）

| class | 处 | 文件 | 备注 |
|---|---|---|---|
| EMISS 发射产物 | 42,889 | 173 | LPLeafHard 19,290（78 文件）＋ LPLeafRoot 19,237（77）＋ LPLeafEasy 4,362（18） |
| M0 直源 | 151 | 10 | = e2e SORRIED = triage 151，逐处全配对 |
| M1 独有（手写） | 1,253 | 58 | 见 1.4 |

发射产物族实债为零的：`LPIds`、`LPAll`、`LPCert`、`LPLeafInfeas00`（gen_lp_skeleton.py 族）；
`LP/W6Align*`（23 文件，gen_w6a_align.py）、`Text/LP/W6Data*`（21 文件，gen_w6_lean.py，
含 RecordIds/Shard00-02/Hard00-14/Coverage/Basic）——grep 实测均 0 处。

### 1.4 M1 独有 1,253 处按任务书三组

| 组 | 处 | 文件 | 清零路径（一句话） |
|---|---|---|---|
| 接口层（hNL/hLP/hTC 脊） | **6** | 2 | Assembly.lean `*Ids` 发射镜像桩 5（:1207/:1228/:1250/:1266/:1283）→ 随 LP/终端证书发射波同步生成闭合；Statement.lean `the_kepler_conjecture` 主定理 Phase-1 占位 1（:116，tactic 级）→ 三接口清零后整体闭合（终局步） |
| Text 层文件簇 | **1,247** | 56 | 分簇见下表 |
| 基础设施（Interval/Graphs/Geom/scripts） | **0** | 0 | 实债为零（grep 命中全为注释），无需清零路径 |

Text 层分簇：

| 簇 | 处 | 文件 | 清零路径 |
|---|---|---|---|
| LocalAuto 簇（LA1-38+Anchors+Bridge） | 1,033 | 39 | port 证填：farm 六批挂接 + SF 通道，按文件从大到小推波 |
| PackingAuto 簇（PA1-25） | 168 | 13 | port 证填（同上）；其中 PA2 26 处＝PA2 残桩族，**删除类候选（用户已裁暂留）**：接口已由 PA23/PA24 同陈述 capstone 替代，合并期 discharge |
| LocalConcl 装配 | 30 | 1 | 下游已证孪生绑定 discharge（SF 通道，装配机制已建，最快降表） |
| PackingConcl 装配 | 9 | 1 | 同 LocalConcl 机制 + farm |
| TameSpine 簇 | 7 | 1 | B1 地基批续打证填（TameList16 为主） |

### 1.5 手写侧最大文件 Top10（处）

| 文件 | 实债 | 备注 |
|---|---|---|
| Text/LocalAuto1.lean | 82 | 含 M0 直源 23；mnt11 章根 1 处（`main_nonlinear_terminal_v11`） |
| Text/LocalAuto22.lean | 82 | 含 M0 4（A3+OCBICBY_p22 tactic 级） |
| Text/LocalAuto32.lean | 65 | |
| Text/LocalAuto28.lean | 63 | |
| Text/LocalAuto34.lean | 60 | |
| Text/PackingAuto25.lean | 60 | 含 M0 31（C3 LEAF 族 + E28 bank 叶） |
| Text/LocalAuto24.lean | 53 | 含 M0 4 |
| Text/LocalAuto6.lean | 53 | |
| Text/LocalAuto38.lean | 47 | tactic 级 5 处（全库单文件最多） |
| Text/LocalAuto23.lean | 42 | 含 M0 2 |

## 2. 三口径对账

### 2.1 e2e 直源 151（docs/e2e-reachability-map.tsv，2026-10-27 重扫）

**151/151 全配对，差异：无。** 每个直源声明恰含 1 处 sorry（151 处）；文件分布与
triage-w1 完全一致（Assembly 81、PA25 31、LA1 23、LA22 4、LA24 4、LA20 3、LA23 2、
LA27 1、PA2 1、TameLp 1）。64 处行号漂移 >2 行（triage 基线 `4ff27ac1` 后 SF-70 等
波次所致），名字级 join 稳定。

### 2.2 triage-w1 分级（A3/B28/C14/D0/E106/F0）

ledger M0 行分级计数 **A3 + B28 + C14 + E106 = 151，与 triage 完全一致**；
D=0/F=0 与实扫一致（直源内无陈述误植、无文档假阳性）。注意 triage 按声明计 151，
本账按处计 151 恰好重合（每直源 1 处；唯一多 sorry 直源 OCBICBY_p22 的 2 处中
1 处声明行即 stub 行，配对仍成立）。

### 2.3 已知大块

| 块 | 实测 | 结论 |
|---|---|---|
| LA1 `main_nonlinear_terminal_v11` 整章 | LocalAuto1 章根 1 处 + Assembly `nliMainNonlinearTerminalV11Ids` 镜像桩 1 处 | 落位，均已入账（M0/M1 各 1） |
| PA2 残桩族 | PackingAuto2 实债 26（grep 42，噪声 16） | 已标删除类，**未删**（用户已裁暂留） |
| CertG TM demo | CertG/CertTM 实债 0 | 注释自述与实测一致，不占债 |
| terminal11-scout 在飞标 | A2 件 `nliRestQITNPEA3725403817`（Assembly:739）仍 sorry（M0/B 级）；PA20「B3 在飞」为 Assembly:6408 注释，无实债 | 在飞件仍在飞 |

## 3. M1=0 清理序列建议（按现有流水线外推）

1. **发射层 42,889（96.8%）**：LP 叶 173 文件走 LP 证书重跑发射管线
   （`socert.py --col-major` 形逐叶转发，`gen_lp_skeleton.py` 再生成即替换）——
   生成-重跑批量闭合，非逐处填证。清完即 44,293 → 1,404。
2. **装配 discharge 39**：LocalConcl 30 + PackingConcl 9，SF/绑定通道机制现成，
   最快可见降表，先行。
3. **LocalAuto 簇 1,033**：按 port 波次从大到小（LA1/LA22 → LA32/LA28/LA34 →
   LA24/LA6/LA38/LA23…），farm 六批挂接 + SF 通道。
4. **PackingAuto 簇 168**：同机制；PA2 26 处按用户裁决在合并期 discharge/删除（暂不动）。
5. **收尾 13**：TameSpine 7 证填；Assembly `*Ids` 5 随发射波同步闭合；
   TameSpine 之外 tactic 级 37 处随所在簇证填消化。
6. **终局 1**：Statement.lean `the_kepler_conjecture` 三接口清零后整体闭合 → M1=0（全库 0）。

## 4. 口径预公告风险点

- **e2e 151 将上浮**：Assembly 5 个 `*Ids` 镜像桩（:1207/:1228/:1250/:1266/:1283）
  不在 2026-10-27 可达图内（map 中零个 `Ids` 声明）；Statement 主定理占位亦不在
  assembly 可达集。下次重扫预期 SORRIED 151 → 156+Δ，需预公告。
- **勿用裸 grep 公告**：45,228 行口径含 935 处注释假阳性；PA23（49）/PA24（52）/
  IneqClosureDefs（8）等 15+ 文件实债为 0。
- **「PA24 整合 +84」**：实测 PA24 现直 sorry 已收口（2026-10-20，1→0），文件实债 0；
  若按旧文档口径公告将失真——整合前须重扫该文件实债（现为 0）。
- **计数口径**：按处 44,293 / 按声明 44,291（LA19 `sol0Bounds_p19`、PackingConcl
  `OXLZLEZ_concl_discharged` 各含 2 处 tactic sorry）。
- **工作树在飞**：LocalAuto1/LocalConcl 未提交改动、GiFactorization.lean 未跟踪——
  本账按工作树实测，后续波次会使手写侧数字漂移（发射层 42,889 稳定）。
