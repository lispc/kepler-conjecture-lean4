# priority-queue.md — 未来待办优先级队列（长期维护）

> **维护者**：编排者（ZCode 主会话）。
> **更新时机**：每次车道并网或侦察入档后即刻更新对应条目状态；每周对表一次；
> 里程碑达成时重写 §0。条目状态枚举：`在飞` / `就绪` / `排队` / `等用户裁决` / `搁置` /
> `完成（日期 · commit）`。
> **北极限**：`#print axioms Kepler.the_kepler_conjecture_e2e`（Final.lean:22）=
> `[propext, Classical.choice, Quot.sound]`。
> **债务刻度**：一律以 `docs/e2e-reachability-map.tsv` 为准。

## 0. 里程碑对表

| 里程碑 | 定义 | 现状（2026-10-26 上午，续 5） |
|---|---|---|
| **M0** 主定理锥直源清零 | e2e TSV 直接 sorryAx 源 = 0 | **152**（TSV `bfe278b5`：池C `db3ae79f` −2、池C-W2 `621a7566` −1；Assembly 81 / Text 散布 71〔PA25 32 + LA1 23 + LA20–27 14 + PA2/TameLp 各 1〕） |
| **M1** 全库 sorry 清账 | tactic sorry 清零或逐条记账（含邻近层 PA24 / PackingConcl 整合决策） | 未开；整合时机等用户裁决 |
| **M2** 信任审计收官 | 624 shard manifest + 抽样 replay（trust-audit P0-2）；43,078 LP 叶户入锥后全链对账；一键复现（Docker + `#print axioms` 断言） | 均未开；不阻塞 M0 |

三接口独立债量（Assembly 81 的分解）：**hNL（非线性不等式）= 77 条 nli\***（57
`nliPackNonlinearRest`（TSV 实数，含 A2 在飞的 rest 9）+ 8 `nliTskBank` + 7 `nliCell3Bank` + 直挂若干）；**hLP（线性规划）
= 1 条**（`lpArchiveCertificatesDebt`，Assembly:6224，纯逻辑部分已真推导）；**hTC
（TextCapstone）= 3 条 Assembly 件**（`fcdjdot`/`jcajydu`/`tameCorrespondenceIso`）+ Text 层
~74 条。接口完成难度排序与理由见 2026-10-25 战略备忘录（会话记录）：hNL ≳ hLP ≫ hTC。

## 1. 在飞（并发上限实测已放宽——2026-10-26 四车道同发成功；并网后 1:1 补位）

| 车道 | 任务 | 文件 | 计分属性 |
|---|---|---|---|
| **poolc-w3** | PA25 锥源收割：TSV 盘点 **32 枚锥直源**（最大 Text 簇）三族——`real_model_*` 28 枚（汇入 pkrmQu/Qx/Qy/Azim/Quarter 五枢纽，先勘枢纽与共享结构定波界）+ LEAF_RANK_PROPS 族 3 枚（cc_prep_model_data / pkLeafRankAzimPointwise / pkLeafRankCriticalEdge）+ `ox3q1hP25` 1 枚（直挂 textCapstone）；基线 `e2c636ec` | PackingAuto25.lean | **锥直源最多 −32**（按实际闭合计） |
| **wsewpch-w6b** | **KCHMAMG**（LA5:5026，HOL ~280 行，circular 支主件）+ LA5 余三枚银行桩：INTERSECTION_LEMMA(:4156) → EXISTS_INTERSECTION_PROPERPLY(:4886) / LOFA_V_SUBSET_AFF_HULL(:4900) → 新增 WHEN_A_B_POS_ARCV_STABLE（全树缺）；W4 查明 :4886/:4900 被 :4156 传递阻塞 | LocalAuto5.lean | 锥 0；W6c circular 支前置 |
| **nkezbfc-giant-w2** | `NKEZBFC_PREP_p9` 主石波（总装已就位 `exact p9_main_induction h stepB`）：stepB 无弦分支（EGHNAVX 300–450 行，拆 EG-1/EG-2）+ AZIM_EQ（先查 Geom.AzimLemmas 拼装）+ 机械余料；COMPATIBLE_BW_TWO_LEMMAS 编排者裁决 = 先查消费面，需要则 p9_* 孪生，未经双核禁 import LA6。任务书 `lane_snapshots/nkezbfc-giant-w2/TASK.md` | LocalAuto9.lean | 锥 0；闭 PREP 后解锁 NKEZBFC → W6c generic 支 |
| **la1-localfan-scout** | 只读核查 W5b 两枚 SF 提案：A 级 LA1 `LocalFan` 弱编码（hypermapOfFan 不排孤立点 ⇒ LA7:1046–1121 foundation 桩疑似假，含机器反例试验）+ B 级 `Generic` affGt 偏弱 → `docs/scouts/la1-localfan-scout.md` | 新文档（不碰 .lean、不构建） | 防 foundation 波建在假桩上 |
| **A2-W2b′** | **提速已执行（用户批准，`8f789c60`）**：Base 4× `.arctanK(1)×1024` → `.atan1K`（pi4D 盒）+ 2,775 分片 967,759 处 `(by decide)` → `(by decide +kernel)` + emitter gen-11（atan1K 默认 ON、判定统一 `DECIDE_TAC`）。构建 09:18 重启：**分片单墙钟实测 181–512 s（原 3,000–7,000 s，提速 6–20×）**。**勘误（午）**：早前「118/2776、~123 片/时、~1 天」系把提速前残留 olean 误计（盘上 109 枚旧残件）；真实口径 **92/2776 @ 1h51m，~50 片/时（仍为旧吞吐 ~4.8×）→ ETA ~2–2.5 天**；完工后探针 → olean 回灌 → Glue 粘合落库 **−1 源** | 后台构建 | rest 9 粘合落库 **−1 源** |

已并网车道不再逐行保留（详见 §8 日志）：GRHIDFA W2–W6（PA3 归零 `cc3cb531`、PA4 桥 `09674a65`）、FCHKUGT W2–W5（全链收官 `43bde50e`）、WSEWPCH W1 `20ff16c3` / W3a `209b1bbd` / W5a `b1e1224d` / **W2 `057a0683`**（AzimBridge 20 件，11 对桥全 rfl 级）/ **池C `db3ae79f`**（PA25 五件，**锥 −2** 实测 155→153）、**池C-W2 `621a7566`**（PA25 四件，**锥 −1** 实测 153→152，TSV `bfe278b5`）、**W3b `9d08844d`**、**W4 `1043a77e`**、**SF-53 `b30bad76`**、**W5b `79586134`**、**cc4p4-discharge `e2c636ec`**（SF-53 解锁的 20 枚 CC4P4 桩全闭，PA4 29→9，探针 20/20 标准三）（LA7 arc half + 2 枚 W6a foundation 件；BGMIFTE 本体留待；两枚 SF 提案 → la1-localfan-scout 核查中）、**fidelity-v1 `fc4afc08`**（`lean/scripts/fidelity_check.py` 自检 PASS，配对率 69.4%，HEAD 全量 H 级恰为 SF-53 两处）、**lp-design-scout**（本提交，`docs/scouts/lp-design-scout.md`）、A2-W1 / W2a `3fab5ee1`。

> **A2-W1 已完成（2026-10-25，关键事实翻案）**：rest 9 证书源 **2,777 文件全部
> tracked 在库**（`CQITNPEAx3725403817`，964,984 叶 prec 64 bb_arb）——**无需 G4
> 发射**；prog 超越节点 ↔ kit 对照**无缺口**（atan×7/sqrt×4/ite×3 全支持，dihY 展开
> 与 prog 语义零分歧，400+64 点数值对证 max 误差 0.0）；glue 三件手写引理标准三，
> 终局形状 = 前提槽一行代入。**新阻断：CertG.lean:248/:420 两枚 TM 教学 demo
> decide=false（CertTM 语义演进未重烤，SF-42 已知尾波债）**——A2-W2a 处理中。
> 交付物：Glue.lean / RUNBOOK-G4.md（发射 CLI 勘误 + 分段构建 + 回灌 + 落库全流程）/
> APPLY-DRAFT.md / prog 节点清单，存 `lane_snapshots/a2-rest9-w1/`。

## 2. 排队（按序补位）

1. `在飞` **NKEZBFC_PREP GIANT 第二波（主石 stepB）**（见 §1 nkezbfc-giant-w2；第一波已落库 `3034e8f7`，LA9 NKEZBFC 节 19→9，`p9_main_induction` 骨架就位）；之后 `EJRCFJD_ALT2`（LA2:1589，正本 EJRCFJD LA6:1135）+ `NKEZBFC`（LA2:1606）一行装配——注意 LA2 import LA5/LA9 均成环，装配层需走 LA9 侧或桥文件。
2. `在飞` **WSEWPCH W4 lunar**（见 §1 wsewpch-w4）。
3. `已完成` **SF-53 应用 + CC4P4 discharge**（`b30bad76` + `e2c636ec`）：20 桩全闭，PA4 文件级 29→9，探针 20/20 标准三，锥 0；余 9 枚 §4/§5 cellParams/bump 桩另行排队。
4. `待 A2-W2b` **A2 落地波**：探针 `CQITNPEAx3725403817_pos` 标准三 → olean 回灌（RUNBOOK-G4 §4）→ 新建 `A2QITNPEAGlue.lean` + Assembly:739 替换 → **−1 源**。
5. `已批·分波执行` **hLP 终端语义移植**（`docs/scouts/lp-design-scout.md`）：用户 2026-10-26 批准 **W6-A**（在飞，§1）与 **W1 root 首批**。**W1 执行口径（磁盘闸）**：本机仅 113 GB 空闲 < 110 GB/批，故先以 1,000–2,000 条子批开工（`df` 硬闸：余量 <30 GB 即停），待 A2 完工清理 `/tmp/a2-rest9w2` 工作区后放大到 5,000 条/批；`enqueue`。W6-B/C 可随后开（W6-B 仍待 GoodListNodes 裁决；W6-C 无前置）。其余见 §6 第 8 项。
6. `就绪` **BO LA1 注册表侦察**（只读）：JEJTVGB 暴露的 22+ 条 `*_concl` 箭头族 + LA2x 机器——B 类最大单块，预判多为 scs 记录展开。
7. `已批` **F1 UPFZBZM 改线**（见 §3）。
8. `在飞` **WSEWPCH W5b BGMIFTE**（见 §1 wsewpch-w5b）。另 **W6a/b/c 收官三波**（待 W2 ✅ / W3b / W4）、**W1b 小波** LA7 UNION_AFF_GE_1_2 / ANGLES_ADD_AFF_GE（~200 行，待 w5b 释放 LA7）。
9. `在飞` **nli B 批工具链复活**（用户 2026-10-26「有空闲 lane 就开始试试」→ nli-b-toolchain 车道已发车）：Homebrew flint 3.6.0 已在（FLINT 3 单库含 Arb），本机 clang 复活 `bb_arb.c` → 重解 RQWUDDU(46 叶) + QITNPEAv2_4003532128(16 叶) → emit_lean(gen-11) → 构建+探针 → APPLY-DRAFT（A1 模板 `286d11b8`）。成功则 B 批 **锥 −2**，且为 17 条重发射 + 18 条硬解铺路。
   > 勘误（10-26）：此前此项写作「nli A1 批 待 A2 完工再开」——**A1（rest 20 FWGKMBZ）早已于 2026-10-22 落库 `286d11b8`**（Assembly:805–8xx 真证，606 olean 在主仓，今日探针标准三），系沿用 10-22 侦察报告建议未核对所致。
10. `排队` **WSEWPCH W2(c)** LA2:1488 / LA7:444 双桩统一小波（待 w5a 释放 LA2）。

## 3. 两周战术排序（2026-10-25 战略备忘录定稿）

1. **F1 UPFZBZM 重接线**（`已批`）：PA25 加 import PA19 + 以 PA2 `_p2` kit 重推
   RDWKARC_concl 装配（~80-140 行）；PA2.RDWKARC_concl / PA2.UPFZBZM_concl 随 merge 退役。
2. **nli A2 攻坚**（hNL 技术闸）：rest 9 的 sqrt/atan/ite 区间编码 + 预构建
   oleans/分机（冷构建外推 40-45h）。**过了它，57 条 rest 是 A1 模板（CFWGKMBZ，
   `286d11b8`）的流水线复制**——这是 156 直源里最大单簇（58 条）的总闸。
3. **保真度全库审计 v1**（`scripts/fidelity_check.py`）：✅ **已落库 `fc4afc08`**（2026-10-26，自检 PASS，配对率 69.4%，HEAD 全量 H 级恰为 SF-53 两处；Top-5 人审入 §6 第 7 项；v2 = 接入 881 条 NEEDS 指针提配对率）。
4. **LP 终端语义移植设计侦察**：✅ **已落库**（`docs/scouts/lp-design-scout.md`，2026-10-26；波次计划与三件裁决入 §2 第 5 项 / §6 第 8 项）。
5. **`scripts/integrate_lane.sh` 固化**：md5 校验 → cp → diff 断言（纯追加/预期删除
   模式）→ 闸 → 消息模板 → push → 地图重生成提醒。背景：编排者人肉链已踩
   后台 shell cwd 重置（闸 127 空跑 ×3）与提交相对路径两坑。

## 4. 中期（1-2 月）

- **nli 农场**：57 rest + nliTskBank 8 + nliCell3Bank 7 按分片数排序批量接线；
  证书生成/重放并行 farm（本机 nice-19 只是其中一路），接线模板函数化。
- **GRHIDFA / FCHKUGT / WSEWPCH 三链收官**（见 §2）。
- **证书 shard 拆独立 lake 库**：应用层重建不动证书；624 shard `native_decide`
  评估总时长测量（终局可交付性）。
- **PA24 / PackingConcl 整合设计**（时机等用户裁决）。
- **HOL→Lean tactic 翻译器实验车道**（B 类压缩，赌一周）：只覆盖最高频 20% 模式
  （UNDISCH2 链 / MATCH_MP_TAC / ASM_REWRITE_TAC），失败成本一周，成功砍 B 类折算行数一半。

## 5. 长期 / 终局

- **M1 全清账**：PA2 残桩、LA1 `main_nonlinear_terminal_v11`（109 条 Main_estimate
  合取的整章债，外部锚定性 def）。
- **M2**：624 shard manifest + 抽样 replay；LP 43,078 叶户入锥的**口径预公告**
  （可达声明数会暴涨，防"债务反弹"误读，同 JEJTVGB +36 教训）。
- **一键独立复现**：Docker + build + `#print axioms` 断言脚本。
- **终局 `native_decide` / `Lean.ofReduceBool` 政策**（是否要求 vanilla decide）——等用户裁决。

## 6. 等用户裁决（编排者不单方面动）

1. **PA2 桩族去留**：26 处 sorried 桩中已实锤死代码/沉睡件（XNHPWAB1/4 已退役、
   `MXI_EXISTS_concl` 消费者已断、`GRUTOTI1_concl` 沉睡）——删除可减文件噪声，
   但删除类保留用户。
2. **PA24 / PackingConcl 整合时机**（全仓零 importer 的邻近层，终局绕不开）。
3. **终局 native_decide 政策**（见 §5）。
4. ~~**SF-53**~~ → **已批准并应用**（`b30bad76`，闸 PASS；patch 归档已规范化）。
5. ~~**A2-W2b 算力去向**~~ → 已被第 6 项取代。
6. ~~**A2 提速方案**~~ → **已批准（2026-10-26 用户）并执行**（`8f789c60`：atan1K + decide +kernel + emitter gen-11；构建重启，分片 181–512 s 实测，预计 ~1 天完工）。
7. **fidelity-v1 Top-5 可疑项人审**（编排者先人审，涉陈述改动再走 SF）：SphereKit:144 `num1` 重建体与正本差交叉项且符号布局不同；ContraFanDeep:3598 `cf4_etaP_box` 正本指针与 Lean 盒形态不符疑引错条目；LocalAuto11:192 `dartStd4_p11` 正本三常数在 Lean 陈述中缺失疑截断移植；PA21:599 `bank_BIXPCGW9455898160` docstring 与已修陈述自相矛盾（注释级）；SF-53 两处被独立复现（HEAD 全量 H 级恰为此两处）。
8. **hLP 剩余两件 + 磁盘窗口**（`docs/scouts/lp-design-scout.md` §4）：W6-A、W1 已批（见 §2 第 5 项执行口径）。仍待：(i) `GoodListNodes := True` 占位真化（陈述/定义变更，W6-B 前置）；(ii) W6-PIN 冻结面钉定升级（statement-fix 流程）；(iii) W5/W7 算力与磁盘窗口——bound 叶全量灌装 olean 860–940 GB、终装配 **≥ 1.5 TB**，本机 460 GB 盘承载不了，届时需外置盘/多机策略。

## 7. 文档/代码卫生（2026-10-25 盘点）

- ~~e2e-debt-map.md 自称"现行度量文件"~~ → 已加存档标记（本日）。
- module-map.md / packing-manifest.md / local-manifest.md 的进度勾选滞后 → 列入周对表项。
- scouts/ 与 handoffs/ 为归档区，不维护（天然历史）。**例外标注**（2026-10-26）：`formal-lp-verify-scout.md` 七处过时（核心是「编译 [360,7,800] 核时」风险已被 root 实测推翻，新瓶颈为磁盘 860–940 GB oleans；189 infeasible 模块已落库未反映）、`lp-w6-coverage-scout.md` infeas 半边 sorryAx 一句失效——以 `lp-design-scout.md` §5 为准。
- phase6-spine.md 保留（§6 仍是里程碑定义源）；phase5-worker-template.md 等
  phase 系列随归档处理，不再更新。

## 8. 变更日志

- **2026-10-26（午，续）**：**nkezbfc-giant-w1 落库 `3034e8f7`**（LA9 +768/−11，闸 PASS @SOL_LOCAL_FAN_POS_CASE3_p9 默认七根：归纳基例 + 有弦分支全闭 + `p9_main_induction` 骨架，NKEZBFC 节 19→9 桩，LA9 32→22；import 零变动，探针 6 枚标准三；移交警告 env-lean 假绿 11 处实证 → 波 2 每 3–4 枚终验）。1:1 补位发车 **nkezbfc-giant-w2**（主石 stepB + AZIM_EQ + 机械余料；编排者裁决 COMPATIBLE_BW_TWO_LEMMAS：先查消费面，需要则 p9_* 孪生，未经无环+撞名双核禁 import LA6——LA6 零下游 importer 是既成格局）。
- **2026-10-26（午）**：**cc4p4-discharge 落库 `e2c636ec`**（PA4 +171/−20，闸 PASS @GRHIDFA 默认七根：SF-53 解锁的 20 枚 CC4P4 桩全数 discharge，PA4 29→9，主仓复核探针 20/20 标准三；新增 §2 首桩前 7 枚 p4a* 前向私件——Lean 无前向引用，§2c 桥在桩位后不可见；雷区入册：陈旧 olean 假 sorryAx，必须先 build 再 probe）。la1-localfan-scout 首航 API 故障（EPIPE）零产出中断，原任务书补发（新基线 aff2188a）。**A2 口径勘误**：重启实为今日 09:18，盘上 109 枚旧残件曾被误计进度；真实 92/2776 @ 1h51m、~50 片/时、ETA ~2–2.5 天。1:1 补位发车 **poolc-w3**（PA25 锥源收割：TSV 盘点 32 枚锥直源为最大 Text 簇——real_model_* 28 汇入 pkrm* 五枢纽 + LEAF_RANK_PROPS 族 3 + ox3q1hP25 直挂终端）。§0 口径微校（Assembly 81 非 80）。
- **2026-10-26（上午，续 7）**：用户三项裁决落地——(1) nli B 批工具链复活试local：**nli-b-toolchain 发车**（flint 3.6.0 已在 Homebrew，bb_arb.c 本机 clang 复活 → 重解两案 → gen-11 发射 → A1 模板粘合草案）；(2) **W6-A 批准并发车**（hlp-w6a：19,715 图证书树 light 数据 + 族名普查）；(3) **W1 批准入队**，执行口径改子批 + 磁盘硬闸（本机 113 GB 空闲 < 110 GB/批；A2 完工清理工作区后放大）。§2 第 5/9 项、§6 第 8 项改写。
- **2026-10-26（上午，续 6）**：连落四波——**SF-53 应用 `b30bad76`**（闸 PASS；首轮 FAIL 系 patch 头带 diff -u 时间戳，归档规范化后重跑，雷区入册）、**池C-W2 `621a7566`**（PA25 四件含锥源 K3_CC_WI_ALT，**地图实测 153→152**，TSV `bfe278b5`，可达 218,326）、**W5b `79586134`**（LA7 +255/−2：arc half p7w2_half_polar_arc + 对偶引擎 p7w2_hvihvec + W6a 预支两枚 foundation 件；BGMIFTE 本体留待；**新地图死角**：LA2:1488/LA7:1063 同名桩致 LA7 不得 import 任何传递达 LA2 的模块；两枚 SF 提案）。补位发车 cc4p4-discharge（PA4）+ la1-localfan-scout（只读）。A2 重建 169/2776、分片 146–954 s。
- **2026-10-26（上午，续 5）**：用户裁决三项——**A2 提速批准并执行**（`8f789c60`：Base atan1K ×4、2,775 分片 967,759 处 `+kernel`、emitter gen-11；旧构建中止，重启后**分片单墙钟实测 181–512 s（原 3,000–7,000 s）**，118/2776，预计 ~1 天完工）；**SF-53 批准**（patch 已贴工作树，STATEMENT-FIX 闸跑中；首轮闸 FAIL 系 patch 头带 diff -u 时间戳致 awk 全等提取落空，归档已规范化后重跑——雷区入册）；**nli B 批证书随 G4 机器损坏丢失**（§2 第 9 项改写：nli 农场真前置 = 复活 pipeline 工具链，候选本机 Docker+flint/arb，待侦察）。WSEWPCH W4 落库 `1043a77e`（LA5 lunar 两件 6→4），补位发车 wsewpch-w6b（LA5 KCHMAMG）。
- **2026-10-26（上午，续 4）**：WSEWPCH W3b 落库 `9d08844d`（LA3 +367/−3，AFF_GE_TO_AFF_GT2_GE1 / AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL / **CIZMRRH** 三件标准三，11→8，import 零变动；W6c 三臂互斥已装进 `hneg`）。披露：车道以字面 `~` 路径在主仓 `lean/` 下误建草稿副本目录（未追踪、已比对后删除、追踪文件零污染）——后续任务书改用绝对路径。补位发车 **nkezbfc-giant-w1**（LA9）。WSEWPCH 现况：W1/W2/W3a/W3b/W5a 五波落库，W4/W5b 在飞，余 W6a（待 LA7 释放）/ W6b KCHMAMG（待 LA5 释放）/ W6c 装配 + NKEZBFC 链。
- **2026-10-26（上午，续 3）**：lp-design-scout 落库（`docs/scouts/lp-design-scout.md` 291 行）：hLP 债点保真核对无新误植；发现 189 infeasible LP 模块早已落库（`7ba6b5b7`）而两份旧侦察未反映；42,889 bound 叶开放、磁盘为新瓶颈（终装配 ≥1.5 TB）；三条路线判定 + W1/W6-A 推荐首波入 §2 第 5 项，三件用户裁决入 §6 第 8 项。补位发车 **wsewpch-w4**（LA5 HALP_CIRCLE_IS_INTERSECTION → HKIRPEP；勘误：RHO_NODE1_MONO_WITH_AZIM 已真非「全树缺」）。§3 第 3/4 项（保真审计 v1、LP 设计侦察）标记完成。
- **2026-10-26（上午，续 2）**：三波落库——WSEWPCH W2 `057a0683`（AzimBridge +155，20 件标准三，11 对桥全 rfl 级，新 import LA2）、**池C `db3ae79f`**（PA25 +380/−22，五件标准三含任务书外 MCELL4_DIHX_AZIM，新 import PA24，**锥 −2**：地图重生成 TSV `09f84c2e` 实测 155→153，可达 218,297）、fidelity-v1（`lean/scripts/fidelity_check.py` 1,235 行 + 审计报告/TSV，自检 PASS，发现 SF-49 已在 HEAD 修复）。补位发车 wsewpch-w5b（LA7 BGMIFTE）、lp-design-scout（只读）、poolc-w2（PA25 K3_CC_WI_ALT 锥链）。**A2 慢因调研收口**（§6 第 6 项）：非固有，π/4 常数的 1024 项级数编码 + decide 双遍求值；`.atan1K` + `+kernel` 实测 ~40×，待用户批准重跑。§0 勘误：nliRest 开放数 58→57（TSV 实数）。
- **2026-10-26（上午，续）**：WSEWPCH W5a 落库 `b1e1224d`（LA9 +119/−3，四件标准三，36→33，新 import LA5 无环实核；NKEZBFC 阻于 NKEZBFC_PREP_p9 900 行 GIANT + EJRCFJD_ALT2，LA2 零改动）；1:1 补位发车 **wsewpch-w3b**（LA3 CIZMRRH + 同节两枚仿射引理）。雷区入册：闸命令 `GATE_ROOTS` 不接受速记 `[Kepler.Text.Downstream]`（unknown target），省略即用脚本默认七根（Hypermap/PackingConcl/LocalConcl/LocalBridge/TameLp/AzimBridge/ContraFan）。
- **2026-10-26（上午）**：应用户「再起三四条」指令，**四车道同发**（poolc-wedge / wsewpch-w2 / wsewpch-w5a / fidelity-v1），全部启动成功——并发上限实测已不再是 2。两项编排者裁定入档：PA25 加 import PA24 预批准（无环实核）；AzimBridge 无主→W2 直接追加。侦察发现 **A2-W2b 吞吐远低于计划**（Shard54–100 单片 3,000–7,000 s，184/2776，剩余 ~2 周）→ 列入 §6 用户裁决第 5 项，默认本机续跑不中断；nli A1 批据此改为「待 A2 完工再开」。§1 表清理：已并网行收进一句摘要，不再逐行保留。**同日勘误**：§2 第 9 项「nli A1 待 A2 完工」有误——A1 早已落库（`286d11b8`，10-22），改为 nli B 批（rest 10 + rest 62，待 G4 导出两份 cert JSON，锥 −2）。nli 现况：62 具名 / 已闭 5（rest 2、4、60 真算术 + A1 rest 20 + N2 rest 1）/ 开放 57（含 A2 在飞）；rest 57 中证书 Lean 源在库的只剩 rest 9。
- **2026-10-26（凌晨）**：GRHIDFA W5 落库 `cc3cb531`（PA3 归零，主链收官）；地图重生成 `67788c99` 直源 **156→155**；**口径更正**：此前把 PA3 文件级 −9 误写为锥计分 −9——锥只记 GRHIDFA_concl 单源，实际 −1；今后计分预告一律区分「文件级 sorry」与「锥直源」两种刻度。FCHKUGT W5 落库 `43bde50e`（全链收官，锥 0——FCHKUGT 不在锥，收益为 PA25 侧转净）。A2-W2a CertG 重烤热修 `3fab5ee1`，A2-W2b 40h 分段构建启动。WSEWPCH W3a 发车。

- **2026-10-25（晚）**：建档并首轮更新。落库：GRHIDFA W2（`9f4df3d1`，PA3 +989）、
  FCHKUGT W2（`60753fd6`，PA18 三件标准三）、WSEWPCH W1（`20ff16c3`，LA7 十件标准三，
  零计分资产，TSV 实测不变）、FCHKUGT W3（`ef96e0eb`，FUEIMOV_4 标准三，bare sorry
  17→16）。发车：GRHIDFA-W3、A2-W1（rest 9 粘合波，用户指令，第三次发车才成功——
  并发上限实测收紧至 2）。文档卫生：e2e-debt-map.md 打存档标记；勘误三条——
  e2e-reachability-map.md 头版实为最新（156，先前"漂移 128"系压缩前旧读取所致，
  收回）；HALP_CIRCLE_IS_INTERSECTION 实为 LA5:7670 桩（侦察误记为 LA7 W1 件）；
  新雷区：Lean `--` 注记行在闸门 `^---` 过滤器中伪装 diff 头（删除行假阴性）。
