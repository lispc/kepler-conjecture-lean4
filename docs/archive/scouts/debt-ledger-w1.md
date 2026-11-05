# LEDGER — 车道 `debt-ledger-w1`（全库证书债/证明债总账本）

- 日期：2026-11-04　车道：debt-ledger-w1（只读 + grep + 写账本；零编译、零 lake、零 auto_gate、零官方地图仪器）
- **审计基线 HEAD：`56436b12f04607e0870da354a84aa05c6c60b1bd`**（2026-11-04 14:32 +0800，lv910-w1 落库「LV9+LV10 … SORRIED +0 / AXIOM 624; GATE-PASS @812837d4」）
- 主仓 tracked 现存 5 项在飞改动（`docs/e2e-reachability-map.md`、`docs/priority-queue.md`、`lean/Kepler.lean`、`lean/Kepler/Text/TameSpine/TameList16.lean`、`lean/scripts/e2e_reach_map.lean`）——均系他道在途件，本车道未触碰、未增删。
- **口径声明**：债务名单以基线 J 官方仪器输出 `/tmp/reachmap_J.out`（2026-11-04 08:35；K_REACH **2,081,706** / K_SORRIED **134** / K_AXIOM 624 / K_MODULES 4,184 / K_UNIVERSE 2,094,462）为准。HEAD（14:32）晚于 J，今日落库（lv910-w1 等）均为锥不变项，名单仍有效；**在飞车道一律按「在飞口径」标注，不冒充终值**。本车道已实测到的漂移逐处注明（如 LA37 12→11）。
- 交付：本册 + `Evidence.md`（命令实录）+ `logs/`（grep 原始输出）。主仓零改动。

---

## 第一部分：锥内 SORRIED 134 直源逐条挂账

### 1.0 分类计数（机器生成，见 `logs/sorried_134_table.md.counts`）

| 分类 | 件数 | 一句话 |
|---|---:|---|
| 农场（nli 证书叶/PA25 bank 叶） | **84** | nliRest 55 + nliTsk 8 + nliCell3 5 + real_model\* 15 + ox3q1hP25 1 |
| 农场-nli 直挂（语句级+证书级双缺口） | **5** | nliOx3q1h / nliMainNonlinearTerminalV11 / nliLpIneqs / nliPackIneqDefA / nliKcblrqcIneqDef |
| 文本波可闭（twin-body/装配） | **35** | LocalAuto 各章 `_pNN` 冻结桩（含 URRPHBZ2） |
| 移植（C-真数学：章级真移植） | **7** | hTC 3（fcdjdot/jcajydu/tameCorrespondenceIso）+ LEAF 族 3 + TameLp 1 |
| 接口锚（terminal11 prep 件） | **2** | mnt11_anchor（随农场 terminal11 波）/ p21_anchor（文本小件） |
| LP 叶重跑带 | **1** | lpArchiveCertificatesDebt（hLP 接口） |
| **合计** | **134** | 与 K_SORRIED 134 逐位一致 |

死债 **0**、可裁件 **0**（triage-w1 全量分诊 D 面=0 / F 面=0 的口径在 134 上维持；每一条都是真 sorry 债）。

### 1.1 与 scout 基线的口径漂移（记档，不冒充终值）

- **nliRest：nliscout（2026-10-22）口径 59 → 基线 J 55**。已点名确认的闭合 2 件：`nliRestQITNPEA3725403817`（A2 完工波）、`nliRestJSPEVYT`；其余差额系 nliscout REPORT 表格式机器提取不完全（`logs/rest_closed_since_scout.txt`；A1 `FWGKMBZ` 与 3 件手工先例 6096597438a/b、1965189142x34、ZTGIJCF0 本就在 scout「已闭」口径内）。
- **nliCell3Bank：scout 口径 7 源 → J 时点 5 sorried**（2 件已闭）。
- **今日落库均为锥不变项**（lv910-w1 HEAD commit 自述 SORRIED +0），134 名单在 HEAD 仍有效。

### 1.2 逐条挂账总表（134 行，机器生成）

原始名单：`logs/sorried_134_raw.txt`（= `/tmp/reachmap_J.out` :13-146 逐字）。每条：模块 / 声明名 / 父边 / 分类 / 闭合路径一句话 / 阻塞谁。

| # | 模块 | 声明名 | 父边 | 分类 | 闭合路径（一句话） | 阻塞谁（下游消费面） |
|---|---|---|---|---|---|---|
| 1 | `Assembly` | `fcdjdot` | `Kepler.Assembly.textCapstone` | 移植（hTC，C-真数学） | 章级移植，独立最深（DLWCHEM/XULJEPR 计数 GIANT）；无已备短路径 | textCapstone→e2e 根 |
| 2 | `Assembly` | `jcajydu` | `Kepler.Assembly.textCapstone` | 移植（hTC，C-真数学） | 章级移植（hTC 最后两根 Assembly 级柱之一） | textCapstone→e2e 根 |
| 3 | `Assembly` | `lpArchiveCertificatesDebt` | `Kepler.Assembly.lpArchiveCertificates` | LP 叶重跑带（hLP 接口，Assembly:6236） | 与 LP 叶量产带（lp-w1/W6 系）同链回灌；纯逻辑部分已真推导 | hLP 分量→Assembly；M2 信任审计 43,078 LP 叶户对账 |
| 4 | `Assembly` | `nliCell3QZECFICwt0` | `Kepler.Assembly.nliCell3Bank` | 农场（nliCell3Bank；scout 口径 7 源，J 时点 5 sorried） | G4 证书发射+粘合入 cell3_bank | cell3_bank→分量1/6→…→e2e |
| 5 | `Assembly` | `nliCell3QZECFICwt0corner` | `Kepler.Assembly.nliCell3Bank` | 农场（nliCell3Bank；scout 口径 7 源，J 时点 5 sorried） | G4 证书发射+粘合入 cell3_bank | cell3_bank→分量1/6→…→e2e |
| 6 | `Assembly` | `nliCell3QZECFICwt0sqrt8` | `Kepler.Assembly.nliCell3Bank` | 农场（nliCell3Bank；scout 口径 7 源，J 时点 5 sorried） | G4 证书发射+粘合入 cell3_bank | cell3_bank→分量1/6→…→e2e |
| 7 | `Assembly` | `nliCell3QZECFICwt1` | `Kepler.Assembly.nliCell3Bank` | 农场（nliCell3Bank；scout 口径 7 源，J 时点 5 sorried） | G4 证书发射+粘合入 cell3_bank | cell3_bank→分量1/6→…→e2e |
| 8 | `Assembly` | `nliCell3QZECFICwt2A` | `Kepler.Assembly.nliCell3Bank` | 农场（nliCell3Bank；scout 口径 7 源，J 时点 5 sorried） | G4 证书发射+粘合入 cell3_bank | cell3_bank→分量1/6→…→e2e |
| 9 | `Assembly` | `nliKcblrqcIneqDef` | `Kepler.Assembly.nonlinearInequalities` | 农场-nli 直挂（双缺口） | 证书发射/语句补全 | nonlinearInequalities 分量6/6→…→e2e |
| 10 | `Assembly` | `nliLpIneqs` | `Kepler.Assembly.nonlinearInequalities` | 农场-nli 直挂（双缺口；lp_ineqs 分量） | 3397113841 为全库唯一接线样板，逐条复制 | nonlinearInequalities 分量4/6→…→e2e |
| 11 | `Assembly` | `nliMainNonlinearTerminalV11` | `Kepler.Assembly.nonlinearInequalities` | 农场-nli 直挂（=terminal11 109 分账，见第四部分；T0 已展开 109 具名债） | 109 具名债逐条证书发射+粘合；20 条证书在库待粘、87 farm 直发（52 单+35 hex）、2 prep | nonlinearInequalities 分量3/6→…→e2e；mnt11_anchor→CUXVZOZ_concl 边紧→contravening pair |
| 12 | `Assembly` | `nliOx3q1h` | `Kepler.Assembly.nonlinearInequalities` | 农场-nli 直挂（语句级+证书级双缺口；与 ox3q1hP25 同根并案） | 证书发射/语句补全；直挂件无独立捷径 | nonlinearInequalities 分量2/6→…→e2e |
| 13 | `Assembly` | `nliPackIneqDefA` | `Kepler.Assembly.nonlinearInequalities` | 农场-nli 直挂（双缺口） | 证书发射/语句补全 | nonlinearInequalities 分量5/6→…→e2e |
| 14 | `Assembly` | `nliRest1965189142a` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 15 | `Assembly` | `nliRestBIXPCGW1738910218a2` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 16 | `Assembly` | `nliRestBIXPCGW6652007036a2` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 17 | `Assembly` | `nliRestBIXPCGW7080972881a2` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 18 | `Assembly` | `nliRestBIXPCGW7274157868a` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 19 | `Assembly` | `nliRestBIXPCGW9455898160` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 20 | `Assembly` | `nliRestBIXPCGWb` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 21 | `Assembly` | `nliRestFHBVYXZa` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 22 | `Assembly` | `nliRestFHBVYXZb` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 23 | `Assembly` | `nliRestFHBVYXZv2a` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 24 | `Assembly` | `nliRestGCKBQEA` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 25 | `Assembly` | `nliRestGLFVCVK4` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 26 | `Assembly` | `nliRestGLFVCVK4a8328676778` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 27 | `Assembly` | `nliRestGLFVCVK4y4crit` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 28 | `Assembly` | `nliRestGLFVCVK4y4subcrit` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 29 | `Assembly` | `nliRestGLFVCVK4y4supercrit` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 30 | `Assembly` | `nliRestIXPOTPA` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 31 | `Assembly` | `nliRestMKFKQWU` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 32 | `Assembly` | `nliRestMKFKQWUhalfwt` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 33 | `Assembly` | `nliRestPEMKWU` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 34 | `Assembly` | `nliRestQITNPEA1_1_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 35 | `Assembly` | `nliRestQITNPEA1_1_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 36 | `Assembly` | `nliRestQITNPEA1_1_2` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 37 | `Assembly` | `nliRestQITNPEA1_2_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 38 | `Assembly` | `nliRestQITNPEA1_2_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 39 | `Assembly` | `nliRestQITNPEA1_2_2` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 40 | `Assembly` | `nliRestQITNPEA2134082733` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 41 | `Assembly` | `nliRestQITNPEA3848804089` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 42 | `Assembly` | `nliRestQITNPEA4003532128a` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 43 | `Assembly` | `nliRestQITNPEA5400790175a` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 44 | `Assembly` | `nliRestQITNPEA5400790175b` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 45 | `Assembly` | `nliRestQITNPEA5653753305` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 46 | `Assembly` | `nliRestQITNPEA5814748276` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 47 | `Assembly` | `nliRestQITNPEA6206775865` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 48 | `Assembly` | `nliRestQITNPEA9939613598` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 49 | `Assembly` | `nliRestQITNPEAv24003532128` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 50 | `Assembly` | `nliRestRQWUDDU` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 51 | `Assembly` | `nliRestTEWNSCJ` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 52 | `Assembly` | `nliRestTXQTPVC` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 53 | `Assembly` | `nliRestZTGIJCF4_0_0_0_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 54 | `Assembly` | `nliRestZTGIJCF4_0_0_0_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 55 | `Assembly` | `nliRestZTGIJCF4_0_0_1_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 56 | `Assembly` | `nliRestZTGIJCF4_0_0_1_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 57 | `Assembly` | `nliRestZTGIJCF4_0_1_0_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 58 | `Assembly` | `nliRestZTGIJCF4_0_1_0_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 59 | `Assembly` | `nliRestZTGIJCF4_0_1_1_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 60 | `Assembly` | `nliRestZTGIJCF4_0_1_1_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 61 | `Assembly` | `nliRestZTGIJCF4_1_0_0_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 62 | `Assembly` | `nliRestZTGIJCF4_1_0_0_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 63 | `Assembly` | `nliRestZTGIJCF4_1_0_1_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 64 | `Assembly` | `nliRestZTGIJCF4_1_0_1_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 65 | `Assembly` | `nliRestZTGIJCF4_1_1_0_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 66 | `Assembly` | `nliRestZTGIJCF4_1_1_0_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 67 | `Assembly` | `nliRestZTGIJCF4_1_1_1_0` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 68 | `Assembly` | `nliRestZTGIJCF4_1_1_1_1` | `Kepler.Assembly.nliPackNonlinearRest` | 农场（nliRest 证书叶；nliscout b1 管道已闭 19 / b2 无 case 模板 22 / b3 求解失败 18） | G4 证书发射+evalReal 粘合一行桩替换；样板 A1 FWGKMBZ(286d11b8)；BIXPCGW9455898160 先 statement-fix（陈疑假差 0.01138） | nliPackNonlinearRest→分量1/6→TheNonlinearInequalities→textCapstone→e2e；PA25 proj_bank 5 条中 TEWNSCJ 唯一通道 |
| 69 | `Assembly` | `nliTskGXSA` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 70 | `Assembly` | `nliTskIYOUOBFsharpv2` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 71 | `Assembly` | `nliTskIYOUOBFsym` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 72 | `Assembly` | `nliTskRIBCYXUsharp` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 73 | `Assembly` | `nliTskRIBCYXUsym` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 74 | `Assembly` | `nliTskTADIAMB` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 75 | `Assembly` | `nliTskWKGUESBsym` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 76 | `Assembly` | `nliTskXLLIPLS` | `Kepler.Assembly.nliTskBank` | 农场（nliTskBank 8 源全 open） | G4 证书发射+粘合入 tsk_bank 查表 | tsk_bank→分量1/6→…→e2e |
| 77 | `Assembly` | `tameCorrespondenceIso` | `Kepler.Assembly.textCapstone` | 移植（hTC，C-真数学） | 章级移植（hTC 柱）；textCapstone 体真推导、唯三 Assembly 消费点之一 | textCapstone→e2e 根 |
| 78 | `Text.LocalAuto20` | `AQICLXA` | `Kepler.Text.OEHDBEN` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 79 | `Text.LocalAuto25` | `ASSWPOW_p25` | `Kepler.Text.ASSWPOW_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 80 | `Text.LocalAuto18` | `AURSIPD_p18` | `Kepler.Text.AURSIPD_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 81 | `Text.LocalAuto26` | `AXJRPNC_p26` | `Kepler.Text.AXJRPNC_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 82 | `Text.LocalAuto27` | `FEKTYIY_p27` | `Kepler.Text.FEKTYIY_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 83 | `Text.LocalAuto20` | `FZIOTEF` | `Kepler.Text.OEHDBEN` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 84 | `Text.LocalAuto28` | `IMJXPHRv2_p28` | `Kepler.Text.IMJXPHRv2_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 85 | `Text.LocalAuto27` | `JCYFMRP_p27` | `Kepler.Text.JCYFMRP_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 86 | `Text.LocalAuto23` | `LFLACKU_p23` | `Kepler.Text.JEJTVGB_case_breakdown_p16` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 87 | `Text.LocalAuto37` | `MHAEYJN_p37` | `Kepler.Text.MHAEYJN_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 88 | `Text.LocalAuto32` | `MIQMCSN_p32` | `Kepler.Text.MIQMCSN_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 89 | `Text.LocalAuto33` | `MM_4I2_IMP_4T2_4T1_p33` | `Kepler.Text.ARDBZYE_p33` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 90 | `Text.LocalAuto26` | `MXQTIED_p26` | `Kepler.Text.MXQTIED_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 91 | `Text.LocalAuto28` | `NUXCOEAv2_p28` | `Kepler.Text.NUXCOEAv2_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 92 | `Text.LocalAuto32` | `NWDGKXH_p32` | `Kepler.Text.NWDGKXH_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 93 | `Text.LocalAuto22` | `OCBICBY_p22` | `Kepler.Text.JEJTVGB_case_breakdown_p16` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 94 | `Text.LocalAuto28` | `ODXLSTCv2_p28` | `Kepler.Text.ODXLSTCv2_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 95 | `Text.LocalAuto15` | `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15` | `Kepler.Text.POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR2_p15` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 96 | `Text.LocalAuto26` | `PPBTYDQ_p26` | `Kepler.Text.PPBTYDQ_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 97 | `Text.LocalAuto11` | `PQCSXWG1_p11` | `Kepler.Text.PQCSXWG1_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 98 | `Text.LocalAuto11` | `PQCSXWG2_WITHINREAL_p11` | `Kepler.Text.PQCSXWG2_ATREAL_p11` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 99 | `Text.LocalAuto26` | `RRCWNSJ_p26` | `Kepler.Text.RRCWNSJ_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 100 | `Text.LocalAuto33` | `SCS_4I1_IMP_SCS_4I2_p33` | `Kepler.Text.SCS_4I1_ARROW_SCS_4I2_STAB_4I1_p33` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 101 | `Text.LocalAuto33` | `SCS_4I2_IMP_SCS_4T1_p33` | `Kepler.Text.ARDBZYE_p33` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 102 | `Text.LocalAuto29` | `SCS_5M2_IMP_SCS_5T1_p29` | `Kepler.Text.HIJ_STEP_1_p29` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 103 | `Text.LocalAuto20` | `SCS_6I1_BERAK_BY_CSTAB` | `Kepler.Text.OEHDBEN_PRIME` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 104 | `Text.LocalAuto27` | `TFITSKC_p27` | `Kepler.Text.TFITSKC_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 105 | `Text.TameLp` | `fully_surrounded_perimeter_bound` | `Kepler.Text.TameLp.MQMSMAB` | 移植（TameLp，C-真数学） | W5 尾波章级移植（WMLNYMD/Local_lemmas 三桥，triage §3-W5） | TameLp.MQMSMAB→锥 |
| 106 | `Text.LocalAuto30` | `UAGHHBM_p30` | `Kepler.Text.UAGHHBM_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 107 | `Text.PackingAuto13` | `URRPHBZ2` | `Kepler.Text.QZYZMJC` | 文本波可闭（PA13 章冻结桩） | b7 车道同章先例（DDZUPHJ 已闭）；PA13 余 URRPHBZ2(:364)/SLTSTLO2(:824) | QZYZMJC 已闭孪生的对偶件→PA13→锥 |
| 108 | `Text.LocalAuto15` | `VPWSHTO_p15` | `Kepler.Text.VPWSHTO_PRIME_p15` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 109 | `Text.LocalAuto36` | `XWITCCN` | `Kepler.Text.XWITCCN_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 110 | `Text.LocalAuto32` | `YOBIMPP_p32` | `Kepler.Text.YOBIMPP_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 111 | `Text.LocalAuto14` | `ZLZTHIC_p14` | `Kepler.Text.ZLZTHIC_discharged` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 112 | `Text.PackingAuto25` | `cc_prep_model_data` | `Kepler.Text.LEAF_RANK_PROPS` | 移植（LEAF 族 3，C-真数学：真移植非 farm） | 上游 :2286/:2449/三 wedge 件真移植（poolc-w3 W3 波工单） | LEAF_RANK_PROPS→PA25→锥 |
| 113 | `Text.LocalAuto21` | `general_482_deformation_p21` | `Kepler.Text.CUXVZOZ_p21` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 114 | `Text.PackingAuto25` | `ox3q1hP25` | `Kepler.Assembly.textCapstone` | 农场（PA25 bank 叶，与 nliOx3q1h 同根并案） | 同 nliOx3q1h 波 | textCapstone 分量2/6→…→e2e |
| 115 | `Text.PackingAuto25` | `pkLeafRankAzimPointwise` | `Kepler.Text.LEAF_RANK_PROPS` | 移植（LEAF 族 3，C-真数学：真移植非 farm） | 上游 :2286/:2449/三 wedge 件真移植（poolc-w3 W3 波工单） | LEAF_RANK_PROPS→PA25→锥 |
| 116 | `Text.PackingAuto25` | `pkLeafRankCriticalEdge` | `Kepler.Text.LEAF_RANK_PROPS` | 移植（LEAF 族 3，C-真数学：真移植非 farm） | 上游 :2286/:2449/三 wedge 件真移植（poolc-w3 W3 波工单） | LEAF_RANK_PROPS→PA25→锥 |
| 117 | `Text.PackingAuto25` | `real_model_cell23` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 118 | `Text.PackingAuto25` | `real_model_gamma10` | `Kepler.Text.pkrmQx` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 119 | `Text.PackingAuto25` | `real_model_gamma11` | `Kepler.Text.pkrmQx` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 120 | `Text.PackingAuto25` | `real_model_gamma8` | `Kepler.Text.pkrmQx` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 121 | `Text.PackingAuto25` | `real_model_gamma8b` | `Kepler.Text.pkrmQx` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 122 | `Text.PackingAuto25` | `real_model_gckb` | `Kepler.Text.pkrmAzim` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 123 | `Text.PackingAuto25` | `real_model_gr` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 124 | `Text.PackingAuto25` | `real_model_ox3q1h_merge` | `Kepler.Text.pkrmQuarter` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 125 | `Text.PackingAuto25` | `real_model_pema` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 126 | `Text.PackingAuto25` | `real_model_pemb` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 127 | `Text.PackingAuto25` | `real_model_quqy` | `Kepler.Text.pkrmQu` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 128 | `Text.PackingAuto25` | `real_model_quqy_sym` | `Kepler.Text.pkrmQu` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 129 | `Text.PackingAuto25` | `real_model_sum_azim` | `Kepler.Text.pkrmAzim` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 130 | `Text.PackingAuto25` | `real_model_tew` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 131 | `Text.PackingAuto25` | `real_model_txq` | `Kepler.Text.pkrmQy` | 农场（PA25 bank 叶：pkrm* 真装配枢纽的 deferred-compute 外部认证锚） | G4 证书排产按 real_model_fhbv2 已证模板（poolc 系先例） | pkrmQu/Qx/Qy/Azim/Quarter 五枢纽→PA25→锥 |
| 132 | `Text.LocalAuto12` | `sgtrnaf_p12` | `Kepler.Text.NOT_EMPETY_MMS_TRANSFER` | 文本波可闭（twin-body/装配） | 以已真证 discharged 孪生体 transfer/重写闭（先例 LocalConcl 47 条 S1 接线波）；章级装配件按 triage §3-W1 模式 | 其 _discharged 孪生已接 e2e（shim 放行+sorryAx 流动），闭则转净证 |
| 133 | `Text.LocalConcl` | `mnt11_anchor` | `Kepler.Text.TFITSKC_discharged` | 接口锚（terminal11 prep 件） | = terminal_v11 本体锚；随 terminal11 109 农场波闭合 | CUXVZOZ_concl/CJBDXXN_concl 边紧→contravening pair；lp_main_estimate（JEJTVGB 链，M1 记账） |
| 134 | `Text.LocalConcl` | `p21_anchor` | `Kepler.Text.CUXVZOZ_discharged` | 接口锚（terminal11 prep 件） | ∀y 盒壳锚；terminal→p21 取支桥（HOL 同构实例化，代价小） | CUXVZOZ_concl/CJBDXXN_concl 边紧→contravening pair；lp_main_estimate（JEJTVGB 链，M1 记账） |

### 1.3 家族级要点（逐条表的路据）

1. **nliRest\*（55，农场）**：nliscout 判定 b1 管道已闭 19（其中 2 证书 Lean 源在库）/ b2 无 case 模板族 22 / b3 求解失败超时 18（含 4 条 residue16 真残余）。不存在查表批量填捷径（目标是 `bank_*` 非 `CertifiedIneqHolds id`）。最便宜首发 = **B 批（rest 10 + rest 62 + rest 1，共 139 叶证书）**，1 波解锁 3 件。**`nliRestBIXPCGW9455898160` 必须先 statement-fix**：Lean 陈述 `> 0.00569` vs HOL `> -0.00569`，强了 0.01138，证书永远粘不上（nliscout §0-5）。阻塞面：PA25 proj_bank 5 条，其中 **TEWNSCJ 是 PA25 TEWNSCJ_MERGED 唯一证明通道**。
2. **直挂 5（双缺口）**：`nliMainNonlinearTerminalV11` = 第四部分 terminal11 主体；`nliOx3q1h` 与 PA25 `ox3q1hP25` 同根并案；`nliLpIneqs` 有全库唯一接线样板 `3397113841`。
3. **real_model\*（15，农场 bank 叶）**：五真装配枢纽 pkrmQu/Qx/Qy/Azim/Quarter 的 deferred-compute 外部认证锚，枢纽本体均已真推导；模板 = poolc 系已证 `real_model_fhbv2`。
4. **文本波 35**：绝大多数是「已接 e2e 的 `_discharged` 孪生 vs 尚 sorried 的 `_pNN` 原件」结构（S1 接线波 +24 显形的债），闭法 = twin-body transfer/重写（先例 LocalConcl 47 条）；LA28 三主箭头孪生（IMJXPHRv2/NUXCOEAv2/ODXLSTCv2_p28）「线通债在」，闭则主箭头线转净证，**调度价值最高**。
5. **移植 7**：hTC 3 件是 textCapstone 真体的唯三 Assembly 级 sorry 消费点；`fcdjdot` 独立最深（DLWCHEM/XULJEPR 计数 GIANT）——**无已备短路径**（诚实记档）。
6. **lpArchiveCertificatesDebt**：hLP 唯一 Assembly 件（:6236），纯逻辑部分已真推导，余量 = 与 LP 叶量产带同链回灌。

---

## 第二部分：塔群 own-sorry 台账

现值 = 本车道 HEAD 裸 grep 实测（`grep -cE '^\s+sorry\s*$'`，logs 重建命令见 Evidence §4）：

| 塔 | HEAD 实测 | 任务书口径 | 在飞波 | 下一波工单指针 | 预计剩余波数 |
|---|---:|---|---|---|---|
| **LA37** | **11**（漂移：12→11） | 12（B6 落库点） | B7 在飞（MHAEYJN 链；快照未落，未对账） | `la37-tower-w1/DELIVERY-b6.md` §4 TOWER-STATE（B2→B6 进度 + resume 要点 (a)-(h)） | ~2-3（余 12 件 = LA6 巨证链 3 + hypermap-iso 3 + XRECQNS 1 + SUB_LUNAR 总装 3 + iter 链 2） |
| **LA34** | **60** ✓ | 60（W1 在飞 60→49 口径） | **W1 在飞收尾**：11 根件证明体全部完成并 splice（kit +807/−12，`git apply --check` PASS，60→49） | `la34-tower-scout/DELIVERY.md` §1.2 全清单（19+14+7+20 四节）+ 波谱 W1→W6 | 6 波谱（首两波 W1+W2 = 19 件即 60→41） |
| **LA14** | **33** ✓ | 33 | W2 已落（11 件全净基础层）；**W3 撞 V3-coe 墙 0 闭合**（33→33 持平） | **`la14-tower-w2/Kit-draft-w5cA3.lean`（实测 622 行；DELIVERY 标 597 行）= 波 4 完整起点**（cos_sin 点式刻画 + continuousAt_azim + azim_0_as_closed 主体已写） | ≥2（波 4 连续性 kit 收口 + 尾波） |
| **LA31** | **3** ✓ | 3 | 无独立波（塔顶装配） | 前提槽直读 LA14 本塔出口（priority-queue `la14-tower-w2` 条目原文） | 随姊妹塔（LA14/LA34）翻净后单波装配 |
| **LA28** | **63** ✓ | 63（LA34 的 `_MK` 平行塔） | 无独立波 | **方向实证：LA28 imports LA34（债主塔→债源塔）**；LA34 每翻一件给对应 `_MK` 件供配方（非自动折减，多一层 ww_defor 复合胶水）；全名单在 `la34-tower-scout/logs/` | 随 LA34 后 2-3 波（三主箭头配方 = IMJXPHR_p34 + ZLZTHIC_concl + MHAEYJN_concl 的 MESON 重排） |

塔群合计 **170 件 own-sorry**（11+60+33+3+63）。两条跨塔前提（la34-scout 勘验）：LA34 全翻 ≠ IMJXPHRv2_concl 自动翻净——registry 净证卡 = LA1 `ZLZTHIC_concl`（LA14 在飞）+ `MHAEYJN_concl`（LA37 B7 在飞）。
**防误引**：快照目录 `b7/`（PA13 DDZUPHJ，2026-10-22）是 P4 旧车道，**不是** LA37 B7 波。

---

## 第三部分：岛/未接入带挂账

### 3.1 LP 叶带（最大单一带）

- **量数（实测）**：`lean/Kepler/Text/LP/` 185 文件、**42,889 处 bare sorry**（grep 实测 `logs/textlp_bare_sorry_full.txt`，与任务口径逐位一致）。orphan-scout 口径：Text.LP 章本体 205 模块「互相抱团、无人接入 e2e 宇宙」（`docs/scouts/orphan-scout.md:79`）。
- **W1 首批 5,000 断点（lp-w1-root，活账）**：目标 5,000 = 10 子批 × 500（账本序 `root_pass_ids.txt` 前 5,000）。**中断点：pilot(5)+sb00-02 已 emit 1,505（源码已回拷，build 排队）；sb03-09（3,500 条）待 emit。** 上轮发车时 A2 大构建持锁（CQITNPEAx3725403817 ~8,700/11,442 分片），v3 分段锁（~60 条/段，段间放锁 120s）排队属正常。
- **重启命令链**（幂等续跑，断点=OK 行跳过）：`source w1_env.sh && w1_run_batches.sh`（v2：sb00→sb09 全链编排，sb03+ 先 emit 后 build；探针不过 / df<30GB / emit 崩溃三 ABEND 闸）。全套脚本与状态机见 `lp-w1-root/DELIVERY.md` 发射器表（v3 件：`w1_build_segmented.sh`/`w1_run_batches.sh`/`w1_follow_smoke.sh`/`w1_snapshot_loop.sh` 等 8 件；v1 `w1_build_batch.sh` 已退役留档）。
- **剩余量估算**：42,889 − 已 emit ~1,505 ≈ **41,384 条未发**（口径注明：emit ≠ build ≠ probe ≠ installed 四级；build 单条 ≈2.3 min，全带纯持机）。信任面：sha256(Data) 对账 + 每子批 5 枚标准三探针，不放宽。
- **`lpArchiveCertificatesDebt`（Assembly 唯一 hLP 件）**：本带在锥内的唯一挂账口；叶户 43,078 的 M2 全链对账未开（priority-queue M2 条目）。

### 3.2 D 证书层（用户 hold，口径勘误）

- **Interval.Cases 13,293 = 文件数，非 sorry 数**（勘误记档）：`docs/scouts/orphan-scout.md:77/:184` 原文「`Interval.Cases.*` | 13,293 | 机械证书层冻结（env 只入了 IneqPilot 试点案例 C3397113841 的子树）」「13,293 文件 / in-env 1,557 声明」。本车道实测：Cases 目录 bare sorry = **0**（全部 'sorry' 字符串 2 处均注释级，logs/cases_bare_sorry.txt）；地图口径「Cases 内 SORRIED 实测 0」（`docs/e2e-reachability-map.md:33`）。**它不是 sorry 债，是冻结在 universe 外的机械证书文件层。**
- **LP 机械证书层 ~952**：`Kepler.LP.Pilot*/W6Align/RandShard12x20/T62586200165*` ~952 孤儿（orphan-scout.md:78/:181）。
- 两项均为**显式用户保留项**（certtm 重锚 hold + D 解冻 hold，priority-queue §1 头注「两项显式用户保留项不变」）。解冻动作 = 物化波（Kepler.lean import + 根注册，同 hypermap/W6Align 先例），解冻后 union 口径相应 +N，**本账只记账不解冻**。

### 3.3 CertTM 618（hold；两案成本对照）

- 定性（certtm-mat-scout）：**「引擎完备、待接整车」的健全备用引擎**；618 = proof-term 孤儿**机制**而非债务——锥内证书叶形全为裸区间 `checkPos`，A2 证书语句形 `checkPosTMHull … = true := by decide` 不引用检查器；现消费者仅 CertG（117 处引用去重后只碰 Dyadic 底座，岛内闭包 114 件）。全岛闭包上限 fresh = **646**（618 孤儿 + 28 邻接），INTREE 114 / ORPHAN 618（certtm-root-w1 ARCHIVE）。
- **两案对照**（勘边成本均已付清， designate 即接）：
  | 案 | 路线 | 成本形状 | 指针 |
  |---|---|---|---|
  | **TM3 农场** | `bb_arb` 驱动量产 emit_lean schema v3，`taylorLeaf`/hull 叶经 `checkPosTMHull` 单入口闭合 | 机器量产（持机）；单入口已验（R1 fresh +76 / R2 fresh +55） | `pipeline/interval/taylor-model-design.md` §4 行 TM3；certtm-mat-scout DELIVERY |
  | **Mono\* 文本** | `MonoCorner`/`MonoTree`（`checkMonoCorner`/`monoTree_sound`，premises 形即 `checkPosTMHull` 成功）被任一锥内模块 import 且 proof-term 消费 | 文本/接线成本（人日级）；R1 簇经 MonoCorner→CertTM 边入锥 | certtm-root-w1 ARCHIVE §2 路线 2 |
  - 候选根表（REACH_ROOT 口径，K_REACH/SORRIED/AXIOM/fresh 四列）在 `certtm-root-w1/ARCHIVE.md` §1；P2「链上他点该引用 TM soundness」勘验**不成立**（当前宇宙）。
- 状态：**certtm 重锚 hold（用户显式保留项）**。

### 3.4 W6Align 19,715（入宇宙在飞）

- `w6align-wire-w1` 判 **GO**：岛 24 文件 standalone 复验全绿（RC=0/errs=0 逐件）、零 importer、零 bare sorry、根定理 `Kepler.LP.W6Align.w6align` 实名且标准三（根体 = 表事实总合取，`dataAll.length = 19715` 等）。
- kit 三文件：`Kepler.lean` +1 import（LP 组末位）+ `global_reach_map.lean` / `orphan_histogram.lean` 各 +1 根（8→9）。**落库后 union 口径 +19,715**（在飞口径注明，未对账不冒充终值）。

### 3.5 TameSpine #7（止损件）

- `lean/Kepler/Text/TameSpine/TameList16.lean:33` 与 `:1094` 原文：**dart_of 选择函数章 `dart_of_card_node` 链（HOL :8043-:8221）未移植，陈述逐字冻结，sorry 债务记账**。
- 在飞：`tamespine-wire-w1`（§2-19 波 1）= 步0 cone 根消解 + TameList16 七 sorry 闭（**2-strike 止损**条款）+ `Kepler.lean` +3 import（899 入宇宙）；该文件现列主仓 5 项在飞改动中，落库后按在飞口径对账。

### 3.6 LA35 visibility 353 / LV 结构不可达 349（visibility 波候选）

- **LA35**：模块孤儿 **741 → 353**（`docs/e2e-reachability-map.md:217`）；LA35 own-sorry 已清零（pm12 收官 `pmPlaneCrowding_p35` 根闭合，priority-queue 续 235）。
- **LV**：第一期**结构不可达 349** 与第二期 324 同性质——「私有/机器派生尾，需文件内可见性波 L3 型，**不推荐**」（`leftover-mat-scout-2/DELIVERY.md:118` 原文）。第二期 614 出口 = 472 干净 / 142 sorried，GO +1,060 / union +1,052 / SORRIED +0；波序 LV9-15 现成待槽。**LV9+LV10 已落库**（HEAD commit 56436b12，+165 支等）——已落未对账，按在飞口径。
- 二者同属「可见性/接入」型候选：闭法不是证明而是 import/根注册/文件内可见性重排，跑仪器前不产生 K_REACH 变化。

---

## 第四部分：terminal11 109 分账（复核现值）

### 4.1 现值复核（本车道实测）

- 聚合骨架 `nliMainNonlinearTerminalV11` 仍 sorried（J134 在列，Assembly 分量 3/6）。
- **T0 已落库**（terminal11-t0，2026-11-03）：LA1 `main_nonlinear_terminal_v11` name/type 冻结，body 由 `sorry` 换成 HOL 同构查表式；**109/109 具名 `mainEstimate_<idv>` 声明**落地，id 清单与 `IdLists.mainNonlinearTerminalV11Ids` 逐条同序（机器核）；访问器与 `get_main_nonlinear` 同构。本车道复核：LA1 内 `mainEstimate_` 命中 223 处、**`theorem mainEstimate_*` 证明件 = 0** → **109 条全部仍未证，无一被后续波闭**（诚实核销：「有些可能已被闭」的假设实测不成立）。
- 证书在库抽查：`Interval/Cases/` 271 顶层条目中 `C4717061266`/`C2125338128`/`C8346775862` 三样 2 命中（与「20 在库」口径一致）。
- `mnt11_anchor`（LocalConcl）仍 `:= sorry`——terminal_v11 证成只关第一支锚；`p21_anchor` 需取支桥。

### 4.2 分账（terminal11-scout §2.1/§4.1 判决 + 核销）

| 分账 | 条数 | 现值 | 成本（runbook 标定） |
|---|---:|---|---|
| **A 在库待粘** | **20** | 无一波动工（theorem 计数 0） | 粘合+语义命题+查表 2-4 h/条（IneqPilot 样板复制）；prep 形 19 条另摊 prep⇒原形桥首例 4-8 h（一次）；C4717061266 553 分片 ≈6.5h 机器已付 |
| **B farm 直发** | **87**（52 单条 + 35 hex 耳模板族） | 未发 | 发射（持机）+ 段建 5-10 机器时/条 + 粘合 2-4 h/条；**hex 35 = 一次 for 循环发射 + 单桥共享**，粘合 1.5-2.5 h/条 |
| **C prep 形路线** | **2** | 未发 | 共享 A 的 prep 桥；cayleyR（10 变元）/cayleytr（9 变元）各 1 次发射；cayleytr0 证书即该路线在库先例 |
| 接口级 3 项 | — | LA1 def 展开 **已完成**（T0）；terminal→p21 取支桥未做（1-2 天）；LA1/LA18/LA21 三胞胎合并未做（0.5-1 天） | — |

**口径勘误（记档）**：任务书写「20/89/2」；scout 分账实为 **20+87+2 = 109**（89 与 87 之差 = hex 35 按模板计的口径差）。以 scout 机器核对（`extract_109.py` 内核级比对）为准。
消费者价值：terminal_v11 证成 → CUXVZOZ/CJBDXXN 边紧 → contravening pair 收尾触锥；lp_main_estimate（JEJTVGB 链）M1 记账；LA19/LA38/LocalBridge 约 191 处取支前提就位等此 def。

---

## 第五部分：死债与卫生

### 5.1 PA2 冻结桩（死声明，rule-2 面合法可删）

- **现值（实测）**：`lean/Kepler/Text/PackingAuto2.lean`（5,887 行）内 bare sorry 体 **26 处**（grep 实测）。
- **具名死声明 3 件**（每件给证据指针）：
  1. `GRUTOTI1_concl`（PA2:5843，体 :5848 `by sorry`）：island-wire-w1（2026-11-03）已把 `PackingConcl.GRUTOTI1_concl_discharged` 的证明项**直接实现为 PA23 `GRUTOTI` 本体**（PA23 已随 grutoti1-d-w1 `e561b60e` 入锥；`PackingConcl.lean:1081-1098` 原文「the proof term is `GRUTOTI` itself … no longer the Auto2 interface」）。PA2 桩已全面旁路，现存引用均为注记/PR 化 statement-copy（PA23:12-13、PA24:123-126、PackingConcl:32），无 proof-term 消费。
  2. `REUHADY_concl`（PA2:5853 起，体 :5866 `by sorry`）：PA24 `REUHADY1` 已由 pa24-rvfxzbu2 前缀件（AJRIPQN+LEPJBDJ 串联，标准三）转全净，不再消费 PA2 桩（pa2-rvfxzbu2/DELIVERY §0）。
  3. `RVFXZBU2_concl`：唯一活消费（PA24:4688）已换接同一前缀件；且 DEP_MAP 第 24 行前提勘误入档（`RVFXZBU` 与 `RVFXZBU2_concl` 互不推出，pa2-rvfxzbu2/DELIVERY §1）。
- **删除合法性**：闸 rule 2 面 = `docs/lane-brief-template.md:58`「删除行只许 sorry / 空行 / 注释 / docstring（规则 2）」+ `docs/e2e-reachability-map.md:266`「卫生波删除（rule 2 裸 sorry 删除合法）；低优先」。**注意**：三件是整 theorem（陈述+docstring+`by sorry` 壳）而非孤立 sorry 行；整壳删除属卫生波口径，须编排者按 rule-2 面批并逐件复跑消费面 grep（PA2 被 PA10/PA14/PA17/PA24 import，删除后四下游需 RC 复验）。其余 23 处 bare sorry 体**未逐件勘消费面**——诚实记档：本车道未完成全 26 件死活判决，只点名上述 3 件为已证死声明。

### 5.2 过时 NEEDS / 史志注记

- NEEDS 总命中 43,822（logs/needs_total.txt），其中 ~42,889 属 Text/LP 生成叶（与 LP 叶同带，不单列卫生）。**真实过时注记样本**：
  - Assembly nli 桩统一 docstring「NEEDS: G4 证书发射 + 粘合入 §2a 查表（**nli 28+127 接线主波**）」——数字已漂移（现账 89 farm 件），属批量注记滞后，建议随 nli farm 总波一并刷新；
  - PA17/PA14/PA23 文件头「sorried」史志注记过时：AJRIPQN、QZKSYKG1/2 已闭合（pa2-grutoti1-concl/DELIVERY「上游核查」节实测）；
  - PA24 GRUTOTI1_concl_p24 SHIMMED 注记过时（「off the discharge path since 2026-10-12」已在 PackingConcl:1086 记档，PA24 侧头注未同步）。
  - 处置：注记类属 rule-2 的注释/docstring 面，可随任一触达波顺带清，不立专波。

### 5.3 退役 kit 残留

- **主仓 tracked**：本车道 grep 未发现需删除的退役 kit 文件（诚实记档：未做全库 kit 普查，超预算；现 5 项 tracked 改动均为他道在途件）。
- **快照区（lane_snapshots，备份带，不入主仓）**：`lp-w1-root/w1_build_batch.sh`（v1 长持锁版，已退役留档——保留作史志，勿复用）；`pa2-grutoti1-concl/Kit-draft-*.lean`（45 unknown 残余，已被 grutoti1-d 路线 (d) 取代，留档）；`la14-tower-w2/Kit-draft-w5cA3.lean`（622 行）**在用非残留**（波 4 起点）。

---

## 第六部分：汇总页

### 6.1 双口径总额

| 口径 | 数值 | 出处 |
|---|---|---|
| 全锥 K_REACH | **2,081,706**（COVERAGE ≈99.36% / K_UNIVERSE 2,094,462） | 基线 J 头部（logs/sorried_134_raw.txt 同源） |
| **ex-Cases K_REACH** | **21,283**（K_UNIVERSE 32,488；K_SORRIED_XCASES = 134，Cases 内 0） | `docs/e2e-reachability-map.md:22-33`（基线 J 同轮校验） |
| Cases 子树节点 | ≈2,060,423（2,081,706 − 21,283），**证书量产机械副产品，非证明进展** | map 头注（:18） |

**件数口径**（134 条直源）：**文本侧可还 43**（文本波 35 + 移植 7 + p21_anchor 1）；**农场侧可还 91**（农场 84 + 直挂 5 + mnt11_anchor 1 + LP 带 1——LP 带随叶量产回灌，机时型）。**节点数口径**：本车道未跑仪器，逐件节点权重以 `docs/e2e-reachability-map.tsv` 为准（唯一权威刻度，priority-queue 头注同款声明）；已知的定性锚 = LA28 三主箭头线、mnt11→CUXVZOZ 边紧链、nliRest→分量 1/6。ex-Cases 侧 21,283 节点里，塔群 170 + SORRIED 134 几乎构成全部人类数学债。

### 6.2 还债排序建议（按调度价值）

**文本类排波提案**（人时型，无机器依赖，单位波收益最高）：
1. **文本波 35 件 twin-body 批**：先取 LA28 三主箭头孪生 3 件（IMJXPHRv2/NUXCOEAv2/ODXLSTCv2_p28，线已通，闭则 LocalConcl 主箭头线转净证），余 32 件按章分组 2-3 波清（先例：S1 接线波 47 条 twin-body）。
2. **terminal11 接口级 2 项**（取支桥 1-2 天 + 三胞胎合并 0.5-1 天）+ `p21_anchor`：解锁 CUXVZOZ/CJBDXXN 边紧触锥路与三文件双胞胎债。
3. **塔群接力**（姊妹塔链，唯一真前置已勘明）：LA34 W1 验收落库（60→49，kit 已 splice）→ LA37 B7（MHAEYJN，兼供 LA28/LA34 registry 前提）→ LA14 波 4（Kit-draft-w5cA3 622 行起点）→ LA31 塔顶 3 件随出口装配 → LA28 `_MK` 塔按配方跟进。

**农场类按机时成本排序**（持机型）：
4. **terminal11 T1**：20 在库待粘（机器已付，2-4 h/条人时 + prep 桥首例 4-8 h 一次）——单波 −20，性价比全场最高；随后 hex 35（一次 for 循环发射）。
5. **nliRest B 批**（rest 10+62+1，139 叶证书，1 波解锁 3 件最便宜）+ **BIXPCGW9455898160 statement-fix 先行**；直挂 5 件含语句级前置（需人时，无捷径）。
6. **LP 叶带重启**（W1 首批 5,000 幂等续跑，纯持机，不占人时）；real_model\* 15 按 fhbv2 模板排产；CertTM/W6Align/LA35/LV 四个物化候选（解冻需用户点头，W6Align 已 GO 在飞）。
7. **压轴**：hTC 3 件（fcdjdot GIANT 独立最深，无已备短路径——诚实记档，勿提前排产）。

### 6.3 与终局形态的对接

- 本账 = 交接包的**「欠什么」正文**：134 直源逐条（§1.2）+ 塔群 170（§2）+ 岛带（§3）+ terminal11 109 分账（§4）+ 卫生面（§5）。
- 「怎么还」与 **farm-handover 审计**（另车道，未发）对接：以 §6.2 排序表的指针行为索引——farm 侧模板/机时/发射器明细（EMISSION-RUNBOOK、nli-farm-runbook 七步、lp-w1 管线 8 件、TM3 bb_arb）在该册展开；两册合并即为完整交接包。
- **未尽事项（诚实清单）**：① 节点级债务权重未测（需地图仪器解禁后重扫）；② nliRest 59→55 差额仅点名 2/4；③ PA2 26 桩仅 3 件完成死活判决；④ 在飞 5 车道 + lv910 已落未对账，落库后本账各行号/现值需按新基线刷新（行号漂移先例：lpArchiveCertificatesDebt 6224→6236）。
