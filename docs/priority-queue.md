# priority-queue.md — 未来待办优先级队列（长期维护）

> **维护者**：编排者（ZCode 主会话）。
> **更新时机**：每次车道并网或侦察入档后即刻更新对应条目状态；每周对表一次；
> 里程碑达成时重写 §0。条目状态枚举：`在飞` / `就绪` / `排队` / `等用户裁决` / `搁置` /
> `完成（日期 · commit）`。
> **北极限**：`#print axioms Kepler.the_kepler_conjecture_e2e`（Final.lean:22）=
> `[propext, Classical.choice, Quot.sound]`。
> **债务刻度**：一律以 `docs/e2e-reachability-map.tsv` 为准。

## 0. 里程碑对表

| 里程碑 | 定义 | 现状（2026-10-25） |
|---|---|---|
| **M0** 主定理锥直源清零 | e2e TSV 直接 sorryAx 源 = 0 | **155**（TSV `67788c99`，2026-10-26：GRHIDFA_concl 出列；Assembly 81 / Text 散布 73+1 / TameLp 1） |
| **M1** 全库 sorry 清账 | tactic sorry 清零或逐条记账（含邻近层 PA24 / PackingConcl 整合决策） | 未开；整合时机等用户裁决 |
| **M2** 信任审计收官 | 624 shard manifest + 抽样 replay（trust-audit P0-2）；43,078 LP 叶户入锥后全链对账；一键复现（Docker + `#print axioms` 断言） | 均未开；不阻塞 M0 |

三接口独立债量（Assembly 81 的分解）：**hNL（非线性不等式）= 77 条 nli\***（58
`nliPackNonlinearRest` + 8 `nliTskBank` + 7 `nliCell3Bank` + 直挂若干）；**hLP（线性规划）
= 1 条**（`lpArchiveCertificatesDebt`，Assembly:6224，纯逻辑部分已真推导）；**hTC
（TextCapstone）= 3 条 Assembly 件**（`fcdjdot`/`jcajydu`/`tameCorrespondenceIso`）+ Text 层
~74 条。接口完成难度排序与理由见 2026-10-25 战略备忘录（会话记录）：hNL ≳ hLP ≫ hTC。

## 1. 在飞（并发上限实测已放宽——2026-10-26 四车道同发成功；并网后 1:1 补位）

| 车道 | 任务 | 文件 | 计分属性 |
|---|---|---|---|
| **poolc-wedge** | PA25 MCELL4_FULL_WEDGE 链：REUHADY(:1797) → MCELL3_DIHX_POS(:2902) → LEAF_RANK_REUHADY(:2611) → MCELL4_FULL_WEDGE(:3963)；加分 WEDGE_UNIQUE_CC_CELL / K3_CC_WI_ALT。编排者裁定：预批准 PA25 加 `import PackingAuto24`（PA24 闭包 = PA2/5/6/12/17 + ConicCapVolume/Polytope/TopologyFan/Geom，不含 PA25，无环），失败则显式前提槽 | PackingAuto25.lean | **锥直源 −1 至 −3**（LEAF_RANK_REUHADY / MCELL4_FULL_WEDGE / K3_CC_WI_ALT 各一） |
| **wsewpch-w2** | `_p2`↔`_p3` 11 对词表桥 + `localFan_p3.of_LocalFan` 打包。编排者裁定：AzimBridge 无主 → 直接追加新节，不新建模块；侦察 §W2(c) LA2:1488/LA7:444 双桩统一**本波不做**（LA2 被 w5a 占用） | AzimBridge.lean | 锥 0；W6 foundation 前置 |
| **wsewpch-w3b** | LA3 同节三件：AFF_GE_TO_AFF_GT2_GE1(:1871, HOL WRGCVDR.hl:2954) / AFF_GE_INTER_AFF_LT_IMP_NOT_EQ_COL(:1875, :3011) / **CIZMRRH**(:1881, :3056, 275 行三分 exclusive-or；TameLp ×2 + LA31 消费) | LocalAuto3.lean | 锥 0；W6c 三分支装配核心前提 |
| **fidelity-v1** | 陈述保真扫描器 `lean/scripts/fidelity_check.py`（数值常量 / 符号与不等号方向 / 区间与求和界 off-by-one / 无正本 四类启发式；`--selftest` 必须抓到 HEAD 仍在的 SF-49 与 SF-53）+ `docs/scouts/fidelity-audit-v1.{md,tsv}` | 新脚本 + 新文档（不碰 .lean、不构建） | 锥 0；防再翻车（已 5 处误植） |
| **A2-W2b** | 分段构建进行中（`/tmp/a2-rest9w2`，olean **184**/2776）。**实测单分片 3,000–7,000 s**（Shard54–100 样本，nice 19 下约 8–10 并行）→ 按当前吞吐剩余 **~11–18 天**，远超计划 40h；见 §6 第 5 项 | 后台构建 | rest 9 粘合落库 **−1 源** |

已并网车道不再逐行保留（详见 §8 日志）：GRHIDFA W2–W6（PA3 归零 `cc3cb531`、PA4 桥 `09674a65`）、FCHKUGT W2–W5（全链收官 `43bde50e`）、WSEWPCH W1 `20ff16c3` / W3a `209b1bbd` / **W5a `b1e1224d`**（LA9 四件标准三 36→33，新 import LA5；NKEZBFC 阻于 GIANT 见 §2）、A2-W1 / W2a `3fab5ee1`。

> **A2-W1 已完成（2026-10-25，关键事实翻案）**：rest 9 证书源 **2,777 文件全部
> tracked 在库**（`CQITNPEAx3725403817`，964,984 叶 prec 64 bb_arb）——**无需 G4
> 发射**；prog 超越节点 ↔ kit 对照**无缺口**（atan×7/sqrt×4/ite×3 全支持，dihY 展开
> 与 prog 语义零分歧，400+64 点数值对证 max 误差 0.0）；glue 三件手写引理标准三，
> 终局形状 = 前提槽一行代入。**新阻断：CertG.lean:248/:420 两枚 TM 教学 demo
> decide=false（CertTM 语义演进未重烤，SF-42 已知尾波债）**——A2-W2a 处理中。
> 交付物：Glue.lean / RUNBOOK-G4.md（发射 CLI 勘误 + 分段构建 + 回灌 + 落库全流程）/
> APPLY-DRAFT.md / prog 节点清单，存 `lane_snapshots/a2-rest9-w1/`。

## 2. 排队（按序补位）

1. `新立` **NKEZBFC_PREP GIANT 波**：`NKEZBFC_PREP_p9`（LA9:1071，HOL 900 行 CARD V−3 归纳：凸 local fan 内角和 ≥ (n−2)π）+ `EJRCFJD_ALT2`（LA2:1589，正本 EJRCFJD LA6:1135）→ 之后 `NKEZBFC`（LA2:1606）一行装配。注意 LA2 import LA5/LA9 均成环，装配层需走 LA9 侧或桥文件。非初等，建议拆 2–3 波。
2. `就绪` **WSEWPCH W4 lunar**：RHO_NODE1_MONO_WITH_AZIM（全树缺，依赖全真）→ HALP_CIRCLE_IS_INTERSECTION（LA5:7670 桩）→ HKIRPEP（LA5:7986 桩）；LA5 体量大、下游多，开波前编排者先核 LA5 无人占用。
3. `待批` **SF-53 应用 + CC4P4 discharge 波**：用户批准后 STATEMENT-FIX 闸（patch 53，THM=`p4_real_model_of_sumfix`）→ PA4 20 桩 discharge（PA4 29→9，锥 0）。
4. `待 A2-W2b` **A2 落地波**：探针 `CQITNPEAx3725403817_pos` 标准三 → olean 回灌（RUNBOOK-G4 §4）→ 新建 `A2QITNPEAGlue.lean` + Assembly:739 替换 → **−1 源**。
5. `就绪` **LP 设计侦察**（只读）：hLP 单源 `lpArchiveCertificatesDebt`（Assembly:6224）终端语义移植路线（W6 覆盖桥侦察已定为多波项目）。
6. `就绪` **BO LA1 注册表侦察**（只读）：JEJTVGB 暴露的 22+ 条 `*_concl` 箭头族 + LA2x 机器——B 类最大单块，预判多为 scs 记录展开。
7. `已批` **F1 UPFZBZM 改线**（见 §3）。
8. `就绪` **WSEWPCH W5b BGMIFTE**（LA7:662，HOL 1050 行，本核最大单件）：W5a 已落库，LA7 加 `import LocalAuto9` 即可消费（车道实核无环）；可白拿 IN_V_IMP_AZIM_LESS_PI + inangle≡azimInFan 字典 + sol_local↔Σ interior_angle 重指数；**不可依赖** NKEZBFC 链。另 **W6a/b/c 收官三波**（待 W2 / W3b / W4）、**W1b 小波** LA7 UNION_AFF_GE_1_2 / ANGLES_ADD_AFF_GE（~200 行）。
9. `待 G4 一步` **nli B 批（rest 10 `RQWUDDU` 46 叶 + rest 62 `QITNPEAv2_4003532128` 16 叶）**：G4 已解出（`bbarb_results` rc=0），但证书 JSON 未导出进仓（`out/cert/`、`out/cases/` 被 gitignore；`nli2/certs/` 只有已闭合的 6096597438_b）。用户在 G4 上导出两份 cert JSON（或直接 `emit_lean.py` 发射 Lean 源提交）后，本机 Lean 批 ~200–300 行、构建秒级 → **锥 −2**。这是 nli 剩余 57 件里最便宜的一步。
   > 勘误（10-26）：此前此项写作「nli A1 批 待 A2 完工再开」——**A1（rest 20 FWGKMBZ）早已于 2026-10-22 落库 `286d11b8`**（Assembly:805–8xx 真证，606 olean 在主仓，今日探针标准三），系沿用 10-22 侦察报告建议未核对所致。
10. `排队` **WSEWPCH W2(c)** LA2:1488 / LA7:444 双桩统一小波（待 w5a 释放 LA2）。

## 3. 两周战术排序（2026-10-25 战略备忘录定稿）

1. **F1 UPFZBZM 重接线**（`已批`）：PA25 加 import PA19 + 以 PA2 `_p2` kit 重推
   RDWKARC_concl 装配（~80-140 行）；PA2.RDWKARC_concl / PA2.UPFZBZM_concl 随 merge 退役。
2. **nli A2 攻坚**（hNL 技术闸）：rest 9 的 sqrt/atan/ite 区间编码 + 预构建
   oleans/分机（冷构建外推 40-45h）。**过了它，57 条 rest 是 A1 模板（CFWGKMBZ，
   `286d11b8`）的流水线复制**——这是 156 直源里最大单簇（58 条）的总闸。
3. **保真度全库审计 v1**（`scripts/fidelity_check.py`）：解析全部 `.hl` 定理语句 ↔ Lean
   冻结签名做规范化结构比对（前提序/符号/槽形/量词序），先报告不拦截。已实锤 3 起
   misplant（CFFONNL 前提序 / bank_TSKAJXYGXSA 符号 / OEHDBEN 注册表形）。
   **必须在 nli 批量接线之前出第一版**——防模板带隐性 misplant 复制 58 次。
4. **LP 终端语义移植设计侦察**（hLP 先行设计，只读）：LP 树/分裂/numerics 的 Lean
   对象模型方案与波次拆分（`5d57f21e` 定性为多波项目，波次尚未拆）。
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
4. **SF-53**（PA4:197/:519 `Icc 0 card` → `Icc 0 (card-1)`，patch 已归档、修复后 build EXIT=0 实测）——批准后解锁 20 枚 CC4P4 桩。
5. **A2-W2b 算力去向**：实测单分片 3,000–7,000 s（远超计划口径），本机 nice 19 续跑预计还要 **~2 周**；可选 (a) 本机继续（零额外成本，期间其他车道照常）、(b) 迁 G4/Linux 多核机重跑（RUNBOOK-G4 §3 分段命令可直接复用，olean 回灌流程不变）、(c) 两边并跑，先到先用。编排者默认 (a) 不中断；用户若选 (b)/(c) 告知即可。

## 7. 文档/代码卫生（2026-10-25 盘点）

- ~~e2e-debt-map.md 自称"现行度量文件"~~ → 已加存档标记（本日）。
- module-map.md / packing-manifest.md / local-manifest.md 的进度勾选滞后 → 列入周对表项。
- scouts/ 与 handoffs/ 为归档区，不维护（天然历史）。
- phase6-spine.md 保留（§6 仍是里程碑定义源）；phase5-worker-template.md 等
  phase 系列随归档处理，不再更新。

## 8. 变更日志

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
