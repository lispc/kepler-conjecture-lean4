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

## 1. 在飞（车道 ≤3，并网后 1:1 补位）

| 车道 | 任务 | 文件 | 计分属性 |
|---|---|---|---|
| GRHIDFA-W3 | ✅ **完成**（`bef9abae`，IPVICGW 支 10 行 + 14 私件，十件标准三，+814/−0） | PackingAuto3.lean | 零计分（W5 才回填九桩），W4 前置 |
| FCHKUGT-W4 | ✅ **完成**（`fff95dbc`，FUEIMOV_3 一次迭代通过，标准三，bare sorry 16→15；**W5 前置 W1-W4 全齐，本体 :7432 装配解锁**） | PackingAuto18.lean | 零计分资产，W5 前置 |
| A2-W2a | ✅ **完成**（`3fab5ee1`，选项 A 重烤成功：exGTMP/exTM1BP mantissa 照 C549Mono 先例重烤，CertG build 绿 8665 jobs，两 demo end-to-end 标准三；Base/Shard1/Shard2 三连 EXIT=0 = **rest 9 构建链阻断解除**；8 demo 全保留零删除） | Kepler/Interval/CertG.lean | 40h 构建的第 0 步 |
| FCHKUGT-W5 | ✅ **完成（落库 `43bde50e`，闸 PASS）**（+210/−2，FCHKUGT 本体标准三，bare sorry 15→14；**FCHKUGT 全链 W1-W5 收官**；PA25 LEAF_RANKING_LEMMA 零编辑重建自动转净 = p25_leaf_azim_inj+FCHKUGT 链实测成立；REUHADY 楔二择支解锁，其债面收窄至 REUHADY1+EWYBJUA 两锚） | PackingAuto18.lean | 收官；池C 解锁 |
| **A2-W2b** | **40h 分段构建进行中**（编排者后台：`/tmp/a2-rest9w2` 克隆，断点续跑，olean 计数 3→2776）+ 完工后 olean 回灌主仓 → 粘合落库 **−1 源** | 后台构建 | rest 9 = 59 条 nli rest 最大单件 |
| GRHIDFA-W5 | ✅ **完成（落库 `cc3cb531`，闸 PASS）**：capstone 四件 + 九桩回填，十三件标准三，+551/−55，**PA3 bare sorry 9→0 全模块归零**；GRHIDFA 主链 W1-W5 收官。披露：车道 agent 收尾文书阶段被配额上限中断，源文件已成品，编排者独立重建+探针+冻结核对后代补交付 | PackingAuto3.lean | **锥 −1（GRHIDFA_concl 出列；PA3 文件级 9→0。地图 `67788c99` 实测 156→155）** |
| WSEWPCH-W3a | LA6 近机械轨道件 6-7 枚（CARD_IS_LEAST_CYCLE / POINT_PRESENTED_IN_RHOND1 / LT_CARD_MONO_LOFA / …）；文书先行纪律（每 2 件快照） | LocalAuto6.lean | WSEWPCH 核前置，LA6 60→54± |
| GRHIDFA-W4 | ✅ **完成**（`173e18e2`，RSIWAMP+UTEOITF + 5 私件，双件标准三，+218/−0；勘误：UTEOITF 实为 nn=3/≠3 两支非三支，card=5 已被 RSIWAMP 灭） | PackingAuto3.lean | 零计分，W5 前置 |
| FCHKUGT-W5 | **本体四分支装配（:7432，收官波）**——W1-W4 前置全齐 | PackingAuto18.lean | 收官解锁 PA25 侧 WEDGE_UNIQUE_CC_CELL |

> **A2-W1 已完成（2026-10-25，关键事实翻案）**：rest 9 证书源 **2,777 文件全部
> tracked 在库**（`CQITNPEAx3725403817`，964,984 叶 prec 64 bb_arb）——**无需 G4
> 发射**；prog 超越节点 ↔ kit 对照**无缺口**（atan×7/sqrt×4/ite×3 全支持，dihY 展开
> 与 prog 语义零分歧，400+64 点数值对证 max 误差 0.0）；glue 三件手写引理标准三，
> 终局形状 = 前提槽一行代入。**新阻断：CertG.lean:248/:420 两枚 TM 教学 demo
> decide=false（CertTM 语义演进未重烤，SF-42 已知尾波债）**——A2-W2a 处理中。
> 交付物：Glue.lean / RUNBOOK-G4.md（发射 CLI 勘误 + 分段构建 + 回灌 + 落库全流程）/
> APPLY-DRAFT.md / prog 节点清单，存 `lane_snapshots/a2-rest9-w1/`。

## 2. 排队（按序补位）

1. `就绪` **FCHKUGT W5**：本体四分支装配（:7432；W1-W4 前置全齐 `fff95dbc`，k=4 支 d 已由 FUEIMOV_4 解锁）——FCHKUGT 全链收官波。
2. `就绪` **GRHIDFA W6**：PA4 CC4P4→CcV11 桥（1 桥件 + periodic Prop/Eq 引理）+ 30 桩 discharge（21 CC4P4 经桥 + 9 `_v11` 孪生 `:= PA3.同名_concl`）+ PackingConcl 九连 #print axioms 复核（PA4 文件级 −30；**锥刻度预期 0**——PA4/PackingConcl 不在 e2e 锥内，属邻近层资产）。
3. `排队` **A2-W2b**（待 W2a）：编排者跑 40h 分段构建（segbuild.sh 断点续跑）→ olean 回灌 → 粘合落库 **−1 源**。
4. `排队` **WSEWPCH W2（词表桥波）**：`_p2`↔`_p3` rfl 桥 + localFan_p3.of_LocalFan 正向打包（撞 AzimBridge 无主文件，需编排者确认归属）；另 LA7 余两件 UNION_AFF_GE_1_2 / ANGLES_ADD_AFF_GE（~200 行，路线已入档）可作 W1b 小波。
5. `排队` **WSEWPCH W3-W5a**：核四真缺口（BGMIFTE 1050 / KCHMAMG 280 / CIZMRRH 275 / HALP 165——注意 HALP_CIRCLE_IS_INTERSECTION 实为 LA5:7670 桩，LA5 不可 import，需编排者单独立项）。
6. `排队` **BO LA1 注册表侦察**（只读）：JEJTVGB 暴露的 22+ 条 `*_concl` 箭头族 + LA2x 机器——B 类最大单块，预判多为 scs 记录展开。
7. `排队` **池C MCELL4_FULL_WEDGE**：等 FCHKUGT 全清（楔二择支解锁）。
8. `排队` **WSEWPCH W3b**：CIZMRRH（LA3:1881，HOL 275 行三分 exclusive-or）。

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

## 7. 文档/代码卫生（2026-10-25 盘点）

- ~~e2e-debt-map.md 自称"现行度量文件"~~ → 已加存档标记（本日）。
- module-map.md / packing-manifest.md / local-manifest.md 的进度勾选滞后 → 列入周对表项。
- scouts/ 与 handoffs/ 为归档区，不维护（天然历史）。
- phase6-spine.md 保留（§6 仍是里程碑定义源）；phase5-worker-template.md 等
  phase 系列随归档处理，不再更新。

## 8. 变更日志

- **2026-10-26（凌晨）**：GRHIDFA W5 落库 `cc3cb531`（PA3 归零，主链收官）；地图重生成 `67788c99` 直源 **156→155**；**口径更正**：此前把 PA3 文件级 −9 误写为锥计分 −9——锥只记 GRHIDFA_concl 单源，实际 −1；今后计分预告一律区分「文件级 sorry」与「锥直源」两种刻度。FCHKUGT W5 落库 `43bde50e`（全链收官，锥 0——FCHKUGT 不在锥，收益为 PA25 侧转净）。A2-W2a CertG 重烤热修 `3fab5ee1`，A2-W2b 40h 分段构建启动。WSEWPCH W3a 发车。

- **2026-10-25（晚）**：建档并首轮更新。落库：GRHIDFA W2（`9f4df3d1`，PA3 +989）、
  FCHKUGT W2（`60753fd6`，PA18 三件标准三）、WSEWPCH W1（`20ff16c3`，LA7 十件标准三，
  零计分资产，TSV 实测不变）、FCHKUGT W3（`ef96e0eb`，FUEIMOV_4 标准三，bare sorry
  17→16）。发车：GRHIDFA-W3、A2-W1（rest 9 粘合波，用户指令，第三次发车才成功——
  并发上限实测收紧至 2）。文档卫生：e2e-debt-map.md 打存档标记；勘误三条——
  e2e-reachability-map.md 头版实为最新（156，先前"漂移 128"系压缩前旧读取所致，
  收回）；HALP_CIRCLE_IS_INTERSECTION 实为 LA5:7670 桩（侦察误记为 LA7 W1 件）；
  新雷区：Lean `--` 注记行在闸门 `^---` 过滤器中伪装 diff 头（删除行假阴性）。
