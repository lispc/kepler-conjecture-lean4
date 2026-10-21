# 项目总进度（Status）— 2026-10-17

> **⚠️ 环境变更（2026-09-28）：旧生产服务器（128 核/503G）报废**，磁盘不可恢复。
> 仅存本机外部存储的产物丢失（cert549_tight.json / LP 43,078 持久化产物 / bb_arb 重跑
> 证书 35 份 / 549·257 分片 olean / .lake 缓存；完整清单见 DECISIONS.md 2026-09-28 条）
> ——代码与文档零损失（git 全量）。新基线：Apple M3 Pro 12 核/36GB。
> **重型计算全部挂起待强机器，本文件所有旧机时间口径作废**；主力转向 Phase 5 填证
> 与轻量 Lean 任务（LLM 工人 = ZCode sub agents，opencode CLI 退役）。
> 遗留风险：~~本机 GitHub key 无 push 权限~~（2026-09-28 已解决，main 全天正常 push）。
>
> 一页看板：各 Phase 完成度、已完成什么、还差什么。每批次由主 agent 例行刷新。
> 计划与当前战略（会师模型）见 `PLAN.md`（2026-10-10 合并 HANDOFF 后的权威版），
> 长期决策见 `DECISIONS.md`。
> 当前 main @ 见本 commit；最近验收：各批次根构建绿（wip/auto-packing 批次提交信息 "38-way root clean"，`aa4baf6b`；HANDOFF 记录 `make check` 绿 `c425db2`，2026-09-14）。
> 注意：2026-09-13 起接班 agent 改为 main 直推模式，允许在制骨架 sorry 短暂存在；
> 历史 sanctioned 占位仍为 `Statement.lean` 主定理（见 Phase 1）。
> **2026-10-08/10 双日班（滚动 sub-agent 批次制首两周，~35 commits）**：用户令
> "每批清空即开下一批 3-5 线连续滚动"，ZCode sub agents 全职工人化。五大里程碑：
> ①**LUNAR 链转真（闸门 axiom 实录认证）**：LA3 WRGCVDR 波（`0ad09801`，
> BIJ_BETWEEN_FF_AND_V 直构+6 连带，18→11）→ LA2 p2 镜像（`454b9479`，
> WRGCVDR_BIJ+级联验证 LOFA 两件转真）→ **OZQVSFF 填空（`54cb5660`，+557）**——
> `LUNAR_IMP_INTERIOR_ANGLE1_EQ_PI` axiom 面 = `[propext, Classical.choice,
> Quot.sound]`，sorryAx 清零。
> ②**GRUTOTI 全章收口在望**：GT-4 region 全清（`p23_region_data`，`eb726964`）→
> **SF31：`grutoti_sum_volD` 冻结陈述被 V:=∅ 机验反例判定为假（`f6622814`）→
> 方案 a1 重建前提面后真证零 sorry（`9851f2af`）**→ B1 VX-前向桥（`4ca2e550`，
> HDTFNFZ 整体吞掉 ε-分案零 AJRIPQN 依赖）→ SF32/33 region 门执行波在飞；
> capstone 本体已是纯组装真证，余债 = hcov（填证波在飞）+ pivot 反向 k=3/4
> （全场最后一块真数学缺口，~200-400 行）。
> ③**BIEFJHU GIANT 真闭**（`98de523a`，9747 行装配，asm 裕度全精确
> k=3..6=0.0239/0.0154/0.0029/0.0059）——揭露**探针同名失明假象**（探针头
> import 同名 sorry 版致 Lean 静默跳过证明体 elaboration，上轮"58→0"只对 kit
> 成立），改名探针法入纪律。
> ④**聚合根全部复活**：SF34（PA22 BIJ_SUM→private，`778f4f5e`）+SF35
> （IneqClosureDefs rho→rhoICD，`a11a7222`，循 arcLengthICD 先例）双撞名修复 →
> LocalBridge/Assembly 从长期不可构建到全绿 → **脊柱波落地（`4aad0387`，
> +219/−2，两笔骨架真闭，`Kepler.Assembly` 全聚合构建绿）**。
> ⑤**feeder 收官**：585 片全建成（两只 K000 怪物 PentR3.K000/K004 数小时级攻
> 克）；五片孤儿（非 wire 引用、覆盖已被 300M/400M 逐根片内核级取代）经用户批
> 准删除（`beafaba3`）→ `lake build Kepler` glob 收敛 G2 已验证态；wire 588 片
> olean 零缺失。**DEBT 账本 1951→1719（净 −232）**；**脊柱公理探针首次本机全闭
> 包跑通**（Graphs olean 就位后 mac 移植生效；主定理 axiom 面 = sorryAx(3 冻结
> 接口)+624 shard+标准三，异常项无）。
> 其余：套件下移 A′（cell_params_d kit PA21→PA20 逐字迁移，`960576f2`；闸走
> PA20 零删除侧新范式）→ PA20 四巨人三真闭（DIHX/SOL/HJKDESR1a 免 Taylor 初
> 等路线，`0d4ace7b`）；REUHADY1 两支收口（shim sorry 消除，(α) 230 行真证
> d≥2 关键补强，`74bcf7a0`）；p24 非平坦胞路线图五档已进两档（ω₁=p 识别+B2
> 纠错 r₃<2 真形态——原 √2 目标被 d=2.4 反例证伪；一阶段 √2 签名 vacuous 缺陷
> 入档待装配波修正）；SF28-35 全流程闭环（提案→批准→补丁→应用→闸）；
> 楔形 GIANT 恢复波 MCELL2_VOL/SOL 双巨人真闭（`bb6cefeb`）；侦察六份入库
> （dedup/TIWWFYQ/gammaX 体积桥翻案 C→B/PA2 桩地图 46 桩 A 类 20 根可收割/
> p24 路线图/会话收官）。
> **2026-09-29 日班（M5′ 填证，18 commits）**：四线并进——
> ①**Merge_ineq 通道开张即收割**：章程入库（`ccc003a4`，81 条银行/19 切片逐字锚点）→
> 波 0 银行结构化 + eta_y 重指向（`2f2c431c`）→ 波 1 **GRKIBMP 闭合**（`1591e1c1`）；
> TSKAJXY（PA21:1428）距收口剩波 2a kit（在飞）→ 波 2b 主定理 → 3 行机械闭合。
> ②**CF-3 `LEMMA_3_POINTS_FINAL` 真化**（`e9ee264a`，路线 B 二次型角点恒等 + 有理余弦界，
> contraveningFan 深几何核 −1；CF-4 开新模块 ContraFanDeep.lean 三波进行中）。
> ③**TameLp W1 keystone 落地**（`9d775467`，+492 行 hypermapOfList 构造 + Iso 实例化 +
> GoodListNodesTl def 层，A7/A9 硬阻塞解除），前置 **GoodListDefs import 收窄**
> （`9cb0cf9f`，伞模块闭包 9017→955 jobs）——**Text 侧填证从此不被 Graphs 分片尾巴阻塞**
> （换机后 CertShards 重建 2-worker feeder 推进中：585 片余 343，尾部 18 枚 15-23h
> 超重根，预估 5-7 天，用户拍板不扩容）。
> ④**陈述/定义修复波**：DEF-FIX 首件 planar 编码纠正（`be9e777a`，净 +15 显式入账，
> auto_gate 新增 GATE_MODE=DEF-FIX）+ SF13 DUUNHOR 双前提（`88951853`）+
> SF17 tau3_taum 补陈 + LA38 机械填证 24/26 行（`5bcb4e11`/`8939b636`）+
> planar 重填波 1 四枚（`4eff461a`）。另 MHFTTZN 上游专项 −3（`53e0438d`/`0178ce1f`：
> PA5 16→15、PA6 14→13，lemma2 留 GIANT 带完整草稿 NEEDS 注记）。
> 侦察五份入账（tame 章 A7-A9 / MQMSMAB A10 / TSKAJXY / ContraFan / 项 12-13a 复核）；
> 闸门第 7-9 演化 + playbook §6 Wave 5 五条教训。
> 债务：账本 07:45 = **1951**（DEF-FIX +15 入账后），日内填证净 **−8**（在飞 6 lane
> 未计：lemma2 / 波 2a kit / TameLp 脚手架 / CF-4a / PA2 RDWKARC / PA22 波 2；
> 账本重生成待静默窗口）。
> **Wave 2/2r 收官（2026-09-28 晚）**：换机后首个全 sub-agent 波收官——
> 9 条 lane 全部过闸落地（LA38 二轮+DIHV 桥 / PA18 / PA4 攻坚 / PA22 桩致假 8 枚立
> 案+二轮 20 枚 / PA2 OAPVION 三件套+GLTVHUM·DUUNHOR 侦察注记 / PA25 11 枚 / LA5
> 二轮 8 枚+假陈述提案官 10 项裁决），**全天两波合计 ~115 枚 sorry 清偿（精确数见
> DEBT.md）**。闸门同日四演进（NOTES-LANE/STATEMENT-FIX 模式/规则②逐字加回与
> 拆行骨架豁免/规则③ sorry 净计数/规则⑤ sorryAx 转白）；陈述修复波获授权
> （DECISIONS.md 2026-09-28 条，提案文档+补丁草案已入库）。**下一 milestone = M5′
> 主定理端到端可达**（`docs/phase6-spine.md` §6：脊柱已存在，债务图 instrumentation
> 为 Step 0，lane 按"主定理可达 sorry 递减"排序）。环境纪律：worktree/共享 .lake
> 符号链接禁令、lake 环境级操作禁并发（当日两次 mathlib 包目录事故的教训）。
> **重大进展（2026-09-19）**：**Phase 6 装配脊柱已立（`0742680a`）**——
> `Kepler/Assembly.lean` 冻结四接口 sorry + 真证明装配定理（Phase 2 tame_classification
> 已接线），`the_kepler_conjecture_from_interfaces` 的 `#print axioms` = 全项目债务图入口；
> **接口之一 `goodListArchive` 已闭合（P6-C，`05b9653d`）：19,715 图 good_list 全库
> 23 分片 native_decide + 内核组合器，零 sorryAx**；DEBT.md 新增"主定理可达债务"
> 脊柱探针节（`spine_axioms.py`，P6-F `1618f6a4`/`0b9ac85a`）。
> **Phase 4 G4（Kimi 线，wip/g4-emit 已合 main `2a9f547b`）**：Q 案 QITNPEA_3725403817
> 已内核闭合（2026-09-18，`184d4a86`，96.5 万叶 2775 分片，公理标准三）；
> **5490182221 全链贯通至内核构建（2026-09-21）**：stage-A 360/360 完成
> （357 顶档干净，3 chunk 残余 1478 失败叶）→ repair 8 轮 9 分钟收敛（pinned rung
> 是关键，证书 1,356,184 叶仅 +0.14%）→ emit 6321 BBTreeG 分片 → **内核构建中**
> （24 并发，~80min/分片，预估约两周——全叶 rung-12/N=2048 高阶 Taylor，单叶内核
> 成本为 Q 案十倍量级）。**波2 双修复治本**：bb_arb disj 支栈污染（`960df850`，
> 旧 6 份波2 证书 disj hit 全为伪影）+ ite 跨 0 hull 语义入内核（`b081b853`）；
> W2.5 closed-arg 记忆化落地（BIXPCGW 257s→~1s/叶）。BIXPCGW 19,147 失败叶
> seeded repair 末轮收官 **STUCK-AT-DEPTH**（2026-09-22：round 8 后 134,788/206,120
> 残留，逐轮 19k→206k 膨胀恒 2.0× 零收敛，二分修复对此案无效确证；**残留叶特征
> 分析 `docs/projects/archive/bixpcgw-residual.md`（`537b2f0b`）——失败盒强烈聚集域边界：
> y2/3/5/6 的 65-67% 贴 y→2 下缘、y1→2.6508/y4→2√2 上缘，sqrt 边界过估 √w 律，
> 闭合移交 549 加速车道 mono/convex 降维 + TM**）；
> 约半数失败叶二分不收敛 = 裸区间 O(w) 过估的实证，**原始证明调研确认
> Flyspeck 用一阶多元 Taylor 模型 + 单调性/凸性降维 + 自适应分割树（官方
> 5000 核时/遍，审计×2）**。**Taylor 模型（TM）双侧已落地合 main（2026-09-21/22，
> 至 `97f5e6ce`：TM0 一元 → TM1 div → TM2 trans sin/ln/atan + chopCeilTo，
> 单叶成本 200s→3.2s；150 叶复测 0/150，根因钉死 sqrt(radicand≈0)+ite/abs hull，
> 单叶口径作废、改二分树总叶数口径**；**549 加速项目立项并移交 opencode 车道
> （`docs/projects/archive/549-acceleration.md`，主杠杆 L1 mono/convex 降维，里程碑 M0-M6）**，
> opencode 连推：ite-hull 决定性实验 **4.8× 叶数削减、guard 跨 0 清零**
> （`04f395e4`）+ CertTM 内核 ite-hull 规则（`3e731659`）+ **schema v3 第一刀
> evalTMHullD 试点 0/20→16/20 PASS、C/Lean 交叉验证吻合**（`120e0d8c`）+
> gsplit/gsplit2 双负结果实证 df-hull 唯一路径、200 叶全量发射演练暴露新瓶颈
> **内核 decide 21.4s/叶**（`a0ac7af7`）+ **余项压薄 --tm-tight 叶数 −24.5%**
> （`7d1ca613`，诚实口径阶段位置 52×）+ **M1 facePos 单调性折叠规则落地**
> （`94d89947`/`d2d5b37c`，mono/convex 进入实质开发，T5 contraveningFan 真化 §2c 11→10）
> + facePos 全量评估（资格 77.6%/全链 PASS 50.7%，`8e61e2ca`）+ **cert 层瘦身 78.3%**
> （裸区间定号全链）+ straddle HullD2 批量 79.8%（`de84f9c3`，err 语义=唯一瓶颈）
> + **arctan 曲率紧致化落地（`3715ad81`，81/99 翻正、Hull200 200/200，全量
> ~95%+ 可验证、wall ~2.7h@40 逼近 M5）**；**Kimi 线 atn2 复合规则交付**
> （`wip/atn2-chop` `0b603559`：atn2DivTM/valid_atn2Div + checkPosTMHullA，
> 纯追加 559 行零 sorry，侦察报告 `docs/projects/archive/atn2-chop-design.md` 已入 main
> `8a5d87ad`——@227 div 越零 26,415 叶分类，关键结论：guard 全跨零下 hull
> 语义结构性 NEG、chop 压定号机制不成立，救回主体在 guard 层收紧/域切分）；
> 5 案诚实重求解 4h 全部超时零产出，待拍板改走 BBTreeGD 管线；145 证书重跑
> wave1+fallback16 收官（35 份）；prep 原型结论：胶合机制可行零膨胀，但 MKFKQWU 级
> 案例区间过估固有叶数 ≥10⁹，方向待决策（Taylor 模型 / 符号消 div / 挂起）。
> **2026-09-20 第二波**：P6-E 155 定义闭包收官（124/124 全 B，`0d1b9cea`）+
> FQN 冲突治理（`74c083eb`，闭包 19→0；opencode 已自行 merge main 解冲突）+
> 六 ID 清单（`242aa531`，实测 580/去重 539，勘误"993"口径）；**43,078 LP 定理持久化
> 内核重跑**（`/home/scroll/lprun-persist/`，2026-09-22 机器重启暴露 shm 事故——
> harness sys.path 顺序 bug + REF 依赖 /dev/shm，已根治并入 git；主批 6,866/6,925
> 跑完，尾部 59 个 SoPlex 未解类经 glpsol 精确对偶通道（`glpsol_tail.py`）
> **59/59 PASS 零失败收官（2026-09-24）——43,078 LP 持久化 100% 完结**）；**2570626711 全链贯通至内核
> 构建（2026-09-22）**：stage-a 512/512 → 255,121 失败叶 repair **45 分钟收敛**
> （round1 2.0× 膨胀后 round2 起 96.3% 骤闭，round5 clean——549 型边界精度叶，
> 非 BIXPCGW 型诚实负面）→ 2,155,467 叶/529,786 参数叶 → emit 12,553 BBTreeG
> 分片 → 内核构建中（24 并发，与 549 共享 64 lean 槽，预估 ~3-4 周）；
> **⚠️ 完整性修订（2026-09-20）：prep 空间 92 家族"745/745 闭合"记录经根因调查判定不可信**（pass2 无任何可审计执行痕迹且 37 倍预算不可复现），求解层口径从 91% 下修为 39%，92 家族需重新求解（策略未定，见上 prep 原型结论）。单案例"证书→接口"粘合试点已端到端打通（C3397113841：粘合引理 1 行 simp 模板，量产每案例 ~30 行机械模板）。
> 政策变更（2026-09-17 用户批准，已执行 2026-09-18）：main 允许携带 sorry 债务，
> wip/auto-packing 已合入 main（`aad4fb35`），债务刻度 = `DEBT.md`（基线 2400）。

图例：✅ 完成并验证 / 🟡 进行中 / ⬜ 未启动。完成度为行数或条目数口径的粗略估计。

---

## Phase 0 — 环境与参考库 ✅

- [x] Lean 4 toolchain（v4.32.2，elan 锁定）、lake 构建可用
- [x] 参考库落盘 `reference/`（flyspeck 文本形式化等，`reference/LOCK.md`）
- [x] 求解器：SoPlex 8.0.3（精确模式）、glpsol --exact、GLPK
- [x] 128 核 / 503G RAM 生产机器；系统盘已扩容至 936G（2026-09-16 起弃用 tmpfs，日志/工件直落盘）

## Phase 1 — 定理陈述形式化 ✅（陈述层）

- [x] 堆积密度定义与主定理陈述 `the_kepler_conjecture`（`Kepler/Statement.lean`）
- [x] 陈述保真性对照文档（`docs/statement-fidelity.md`）
- [ ] 主定理**证明**本体（`Statement.lean:111` 的唯一 sanctioned sorry）——全项目终点，Phase 6 装配

## Phase 2 — tame 平面图枚举 ✅ 100%（闭合）

- [x] 19,715 张 tame 平面图全量枚举 + 内核验证（585 个 CertShards 分片）
- [x] 公理审计通过（`make check`；601 个限定范围 native_decide 信任公理，零 sorryAx）
- [x] 新机器全量重建验证过
- [x] ⚠️→✅ **换机后 CertShards 分片重建收官（2026-10-10）**：585 片全建成
  （两只 K000 级怪物 PentR3.K000/K004 数小时级攻克）；五片孤儿（非 wire 引用、
  覆盖已被 300M/400M 逐根片内核级取代）经用户批准删除（`beafaba3`），
  `lake build Kepler` glob 收敛 G2 已验证态；wire 588 片 olean 零缺失
- ⚠️ 红线：绝不 `rm -rf lean/.lake`，分片重建需 ~7 天

## Phase 3 — 线性规划 ✅ 100%（2026-09-07 全闭合；root 区预灌装重跑在跑，产物待灌）

- [x] 证书链路全通：Flyspeck 证书解析 → LP 展开/扁平化 → SoPlex 精确求解 → 整数对偶证书 → Lean 内核弱对偶 checker（`Kepler/LP/Cert.lean`、`ColMajor.lean`）
- [x] 试点图端到端闭合（行主序 + 列主序，`3cbe979`）；生产 harness 入 git（`pipeline/lp/run/`）
- [x] easy 23,640/23,640 终端内核验证通过
- [x] hard_1 偏差根因修复（`d5e32af`：branch.py 逐节点数值收紧重放）
- [x] **全部 43,078 个终端 LP 内核验证通过**：SoPlex 数值放弃的 51 例全部经 glpsol 精确对偶通道闭合（`glpsol_dual.py`，glpsol --exact 最慢 13.5h/例 + 内核 decide ~245s/例）。账本 `~/lprun-logs/results.jsonl`（43,078/43,078 exit=0）
- [x] 🔄 **root 区 LP 预灌装重跑在跑（2026-10-12 启动，看护手册 `/Users/zhangzhuo/lprun/MONITOR.md`）**：root 区 19,237 条（与 `LPIds.lean` lpRootIds 77 chunk 同集已核）按 hlen 升序、恒 2 solver（用户 2 核配额）；首批 6,900 条 2,500/6,900 零 fail（2026-10-20 快照，预计 10-22 上午收）。**重跑产物证书待灌回仓库**——上两行 ✅ 指 2026-09 通道/账本闭合口径，灌回是独立收尾步

## Phase 4 — 非线性不等式 🟡 求解层 ~85% / 内核闭合 8 案端到端 + C1.7 收官（量产/粘合收尾中）

- [x] 区间算术全层（`Kepler/Interval/`：Basic/Div/Sqrt/Ball/Trans/Expr/BBTree 分支定界，`f3cea0f`）
- [x] dyadic 精确算术、证书式 sqrt、Taylor/sin soundness、分支定界证书格式
- [x] 量产流水线：`ineq.hl` 记录解析（181 条）→ 公式 AST（176 条）→ 定义表（348 定义依赖闭包零缺失）→ RPN case JSON（176/176，`f99dd04`）
- [x] **bb_arb：C/FLINT 球算术分支定界器**（`8b7c3c4`）：RPN 求值 + dyadic 二分 + ite guard + disj + 证书 JSON 输出；sqrt8 端点精度 bug 已修（2⁻³⁰ 网格）
- [x] y 空间直跑：**65/176 闭合**（dReal 41 + bb_arb 新增）
- [ ] ~~prep 745/745 全闭合~~ **证据链不可信（2026-09-20 根因调查判定）**：pass1（36 闭合）可追溯可复现；**pass2（709/709）无 runner、无日志、无入仓产物、不可复现**——pass2-only 案例在 37 倍名义预算（150M 节点）下实测仍不闭合。prep 案例生成链本身已验证保真（叶数逐数复现），92 prep 家族的求解需重做（域剖分+树胶合或搜索策略改进，未启动）
- [x] **家族级分析（2026-09-09；2026-09-20 修订口径）**：176 条不等式 = 68 y 空间闭合（其中 51 已有/在产 bb_arb 证书）+ ~~92 条 prep 家族覆盖闭合~~（**证据降级为无**，见上条）+ 16 条真残余（清单 `pipeline/interval/out/residue16.txt`）。**求解层可信口径：68/176（39%）已闭合 + 92 待重做 + 16 残余**
- [ ] 16 条真残余逐条定策略（GRKIBMP B V2 有真反例叶=尖锐边界组，需 ε 余量或弱编码；其余先试更大预算/域剖分）
- [ ] **BBTree 证书 → Lean 内核闭合**（G4）：bb_arb 已能出 cert JSON；Lean 侧扩展进度：
  - [x] `IExpr.abs` + `DInterval.abs` + soundness（`Basic.lean`/`Expr.lean`）
  - [x] `IExpr.ite`：**区间决定 guard**（`C.hi<0`→then，`C.lo≥0`→else，跨 0→STRADDLE 返回 none），`eval_mem` 证分支一致——无需单独 guard 证书
  - [x] 析取证书 `Kepler/Interval/CertDisj.lean`：`DisjGoal = pos e | varLt i j`，`BBTreeD` + `bb_sound_disj`（覆盖 58 条 disj 案例）
  - [x] `TKind.lnK` + `logI` 全链（2026-09-13，`3aed260` 进 main）：`log2D` dyadic 常数证书、`lnI`/`logInterval` soundness（`[1,2]` artanh 级数）、试点 2/3 < log x on [2,4]，公理仅标准三
  - [x] **`emit_lean.py` 证书→Lean 分片生成器 + 端到端通路（2026-09-13/14，wip/g4-emit 分支，Kimi 负责）**：
    - 树重建：扁平叶表 → 二分树（任意无横跨维满足 splitOK，优先最宽维）
    - 分片三层结构 Base/ShardK/根（公理标准三）：**7 案例端到端闭合**——`C1965189142x34`（1 叶）、`C3397113841`（1.5k 叶 35.7s）、`C4717061266`（55k 叶 4m50s）、`CFWGKMBZ`（205k 叶 59m50s，`642fa5c`）、`C6078657299`（694k 叶，首个真实 disj 大案例，`625fd10`）、`C8425800388`（**1.35M 叶** 4h47m，`8b31098`）、`C3253650737`（**1.67M 叶** 5h19m，`a55b02d`）
    - `CertBool.lean`：`splitOKB`/`coversB`（BBTree + BBTreeD）——整树覆盖一次内核 `decide`
    - `CertG.lean`/`BBTreeG`：**跨叶 sqrt/div/trans 参数机制**——`evalReal` 忽略证书参数，逐叶特化表达式 + `rfl` 语义桥（试点端到端绿）
    - disj 发射（BBTreeD/var_lt 校验）已实现，合成 mixed-hits 案例端到端绿（假证书被内核正确拒收）
    - **4 个真缺陷治本**：`divFloorQ` 缩放空间缺陷（深负指数除法 none→双分支精确取整）；`atan(1)` 边界不可求值（Abel 式极限放宽为 ≤）；修复扫描假绿防护（驱动错误即中止）；**dyadic 规范化形态 vs 内核 midRadius 形态**（偶数 mantissa 中点结构不等——全管线改 (m,e) 表示 + midRadius 同款中点，`0aea134`）
  - [x] **FillParams 参数填充工具链（2026-09-14，`0588df2`）**：Lean 编译态逐叶算 sqrt mantissa（零镜像失真）+ (N,out) 阶梯 + 279 叶小样端到端绿；封闭 atan 参数高 Taylor 阶 trick（阶数后经实测下调，见下）
  - [x] **FillParams stage-a 分片并行化（2026-09-15，wip/g4-emit）**：单体驱动（354MB/96万叶数组字面量）elaboration 不可扩展（11.5h 未果）→ 改造为 `--stage-a-shards=K` 连续切块小驱动 + `runMain` argv 派发（无参走阶梯 / `N out` 钉死单点）+ `stagea_merge.py`（全局 rung 裁定 + STALE 补算 + 全局索引合并）；256 chunk × 64 路并行
  - [x] **repair_leaves.py 叶修复回路（`85f5ae7`）**：编译态逐叶扫描 → 失败叶二分加深（splitOK 对任意细化保持）→ 修复证书
  - [ ] 现存 16 证书收尾：已闭合 6 份（另加早期 2 小案共 8 案例）；波1 sqrt4/atan7 三份——**QITNPEA_3725403817 已闭合（2026-09-18，`184d4a86`：964,984 叶 = 964,792 + 192 修复衍生，2775 BBTreeG shards，11,441 jobs，根 decide 180s，公理标准三）**；**5490182221 已贯通至内核构建（2026-09-21：stage-A 360/360，残余 1478 叶 repair 8 轮 9 分钟收敛——pinned-rung 二分修复范式确立，1,356,184 叶 6321 shards，构建至 784/6321 后**应用户要求暂停（2026-09-24，olean 保留可幂等续跑，等加速管线收口再定恢复/重发射）**）**；**2570626711 已贯通至内核构建（2026-09-22：stage-a 512/512，255,121 失败叶 repair 45 分钟收敛，2,155,467 叶 12,553 shards，构建至 770/12,553 后同批暂停）**；**波2 disj+sqrt 家族（2026-09-20/21）**：bb_arb 栈污染修复（旧 6 份证书 disj hit 伪影根因）+ ite hull 语义 + W2.5 记忆化全部入库；BIXPCGW 19,147 失败叶 seeded repair **STUCK-AT-DEPTH 收官（2026-09-22**，残留 134,788 盒聚集域边界，特征分析 `docs/projects/archive/bixpcgw-residual.md`，闭合归 549 加速项目 TM/mono/convex 车道）；5 案诚实重求解全超时，待改走 BBTreeGD；末位 2 份 3112-sqrt 怪物（需参数共享优化）
  - [ ] 证书量产：145 个已闭合案例需 bb_arb `--cert` 重跑出证书——**wave1+fallback16 已收官（2026-09-20，35 份证书落盘 `/home/scroll/bb-cert-rerun/certs/`）**，后续批次随波2/波3 排期（9893763499 案例 bb_arb 失控吐 117GB 日志已记录）
  - [ ] G4 粘合收尾：155 定义闭包的 Lean 定义 + 每案例 `evalReal e ρ = 展开式 ρ` 对应引理（依赖 packing 章定义，**主体剩余**）
  - 规格：`pipeline/interval/arb-layer.md` §3/§4
- [ ] GRKIBMP_B_V2 尖锐边界组单独处理（我们把 ≥ 加强成严格 > 导致等号边界不可闭，需 ε 余量或弱编码）
- [ ] `ineqdata3q1h.hl` 的 Mathematica record 单独解析（2026-09-20 P6-E 更正：实测
  `raw_nonlindatah` 为 **46 条** record × 5 支 = 230 支不等式，非"7 条/35 条"；与
  merge_ineq.hl:22-24 "5*46 / 230" 注释一致。ID 清单已量产——`lean/scripts/
  gen_idlists.py` → `Kepler/Assembly/IdLists.lean` 的 `ox3q1hIds`；record 内容解析
  仍是本项债务）
- 数字口径：底账 181 条记录；y 空间 176 案例 / prep 空间 745 案例；Assembly 六分量
  ID 口径（2026-09-20 实测）：81 + 230 + 109 + 127 + 5 + 28 = 580（去重并集 539；
  注册表总 547）——更正 phase6-spine.md 的"993"说法，折算登记
  docs/statement-fidelity.md 附录 B

## Phase 5 — 文字证明移植 🟡（全项目最大头，已全自动化）

**生产模式（2026-09-10 v2）**：`lean/scripts/auto_pipeline.sh` 全自动批次流水线——
deepseek-v4-flash 全权负责：骨架设计（陈述冻结）→ 工人填空 → 机械闸五道 →
批次审计 → 自动 ff-push main。满血 glm-5.3 留作 NEEDS-HUMAN 前最后兜底；
**Kimi 降为每 4h 汇报 + STATUS.md + 陈述保真抽查 + 处理熔断**。
模板：`docs/phase5-worker-template.md`。
实测吞吐：批次 4（10 枚）21 分钟、批次 5（10 枚）15 分钟，全 deepseek 一次过。
2026-09-21 opencode 侧进展：AzimBridge 主桥闭合（716 行 49 定理，azimCycle↔sigmaFan
orbit 传输 + LocalFan↔localFan_p3 数据桥）；裁定波 7——**7 枚移植失真"假陈述"全部裁定**
（比硬填更有价值：诚实标注 false-as-stated 并修正）；分支 sorry 2417（自 merge main
后口径）。2026-09-21/22 续：TameSpine 填证 T1-T4 波（`387f9047`/`2fea2def`：
Assembly 秒填批 3 件闭合、JGTDEBU 全组/NODE_TYPE_lemma 真证明、CKQOWSA 章移植、
CDTETAT/KCBLRQC 链真化——**TameLp 桥链全通**）。

| 模块（HOL 源文件） | 行数 | 状态 | 完成度 |
|---|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 全书收官 | 100% |
| fan/fan.hl 系列（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 全书收官（hypermapOfFan 完整构造） | 100% |
| fan/topology.hl | 4,718 | ✅ 全书收官（`36c37c6`，dart_leads_into 全套） | 100% |
| fan/planarity.hl | 15,463 | ✅ **全书收官（2026-09-11，`48ff904`）**：批次 1-15 自动闭合 + 批次 16 的 `solid_of`/`MOZNWEH` 经体积层人工攻坚闭合，全部进 main | **100%** |
| fan/Conforming.hl | 17,033 | ✅ **全书收官（2026-09-12）**：批次 1-23 全闭合（~230 枚定理，全部零 sorry、标准公理），含巨证 `lemma_connect_hypermap`（~1900 行 HOL 证明，6 段 sub-agent 流水攻克）与收尾 Euler/`Hypermap.Planar`；已合入 main | **100%** |
| fan/polyhedron.hl | 3,200 | ✅ **全书收官（2026-09-14）**：71 条定理 + Polytope 面理论基层（`Kepler/Text/Polytope.lean` ~2.5k 行，0 sorry）全部闭合进 main；巨证 `FLVNSME`（~1000 行 HOL）经 6 段 sub-agent 流水 + 两阶段规划攻克；曾发现 FaceOf 闭/开线段编码 bug，已修正为 Brøndsted 开线段规范并诚实重做受污染证明 | **100%** |
| packing/（Rogers/OXLZLEZ3/REUHADY/counting_spheres/marchal…） | **99,350（43 文件，2026-09-13 实测）** | 🟡 **骨架 100% 就位（2026-09-15）**：25 模块 20.5k 行 Lean，~1114 定理全部陈述（GRUTOTI/OXLZLEZ/URRPHBZ3 等多个 capstone 已证），920 sorry 纯填证期；REUHADY1 十一波收官（10-20）：**p24 直 sorry 2→1**（SF-44/45 应用+cover_strong 四件装配+:3625 换接）、PA2 shim 退役；GRUTOTI 终章在飞 | 骨架100% / 填证推进中（09-15 的 ~25% 口径已过时，现值以 `docs/e2e-debt-map.md` 可达债图为准） |
| local/（IMJXPHR/QKNVMLB/XWITCCN/local_lemmas/terminal…） | **174,694（68 文件，2026-09-13 实测）** | 🟡 **骨架 100% 就位（2026-09-16，`aa4baf6b`）**：W1-W7 七波 39 模块（LocalAuto1-38 + LocalAnchors），174.7k 行 HOL 源全部骨架化，各批根构建绿（38-way root clean），1793 sorry 纯填证期；LA5 POS_DIRECT 根系五件已真证（2026-10-19） | 骨架100% / 填证推进中（09-16 的 ~10% 口径已过时，以债图为准） |
| **tame/ 文字章（TameSpine 移植线，2026-10 立线）** | **98,000（64 .hl；tame_list.hl 14,428）** | 🟡 **首本 tame_list.hl 全书收官（2026-10-20，`f0361c78`）**：批 1-59 五十九批 :23-:14428 零缺口覆盖，649 主定理全真证、axiom 探针零 sorryAx；下一领土 reduction1.hl（4,976 行，批 49/56 已越章预收部分件）——当前发车冻结待用户令 | 首本 100%（1/64 文件） |
| trigonometry/（trig1/trig2/euler） | 10,511 | 🟡 EULER 三代车道在飞（2026-10 起：p21e_* 家族 + W-乘积恒等式/模度书/M>0/h14 链，克隆内 v19 打磨、尚未入库，自写 HANDOFF 接续）；trig1/trig2 未启动（部分语义已被 azim 层覆盖） | 入库 0%（试炼件在飞） |
| volume/vol1.hl | 1,421 | 🟡 已用 :18/:458/:651 三段（`radialNorm`/`sol`），其余待移植 | ~25% |
| fan/ 残余（hypermap_iso-compiled 1,174 + GMLWKPK 297） | 1,471 | ⬜ 未评估（可能为编译产物/可跳过） | — |
| assembly（ch9 终装配） | — | ⬜ 未启动 | 0% |

> 行数口径说明（2026-09-13 实测 `reference/flyspeck/text_formalization/`）：Phase 5 全书总量
> ≈ **359k 行**（已完成 60.8k + 剩余 ~298.6k）。旧估计"packing 28k / local 30k"实测为
> 99k / 175k，此前完成度高估约 3 倍，已据此下修。不计入：nonlinear/（93k，Phase 4 数据）、
> tame/（98k，Phase 2 数据）、general/theorem_digest*（60k，自动生成索引）。

已落地的公共地基（`Kepler/Geom/` + `Kepler/Text/`）：

- [x] **体积层基础设施 `Kepler/Geom/Volume.lean`（2026-09-11 新增，已验证无 sorry、
  公理仅标准三）**：`radialNorm`（vol1.hl:18）、`sol`（vol1.hl:651，用
  `Classical.choose` 编码 HOL `new_specification`）、`sol_spec`（体积密度规格）、
  `radialNorm.volume_scaling`（vol1.hl:458 `lemma_r_r'` 的标度不变性）、
  `sol_radius_independent`，以及 `volume.real` 在平移/标度下的引理。这是
  Conforming/packing/local 大量 `sol` 代数定理的前置；**不依赖** VOLUME_SOLID_TRIANGLE。
- [x] Azim 方位角全层（Azim/AzimLemmas：ON 标架、角加法、AZIM_EQ/COMPL 等）
- [x] Aff 仿射符号层（affGe/affGt/affLt/affsign）
- [x] Coplanar 移植（`Kepler/Geom/Coplanar.lean`，`757a33d`）
- [x] vectorAngle/angle 引理族（`VectorAngleLemmas.lean` + 三点角）
- [x] azim 平移桥 `azim_sub_self` + JBDNJJB 混合积 + cross_dot 族
- [ ] 遗留去重：`Kepler.Text.fan80/fan81`（Planarity）与 `Kepler.Text.Fan.fan80/fan81`（Fan.lean:222）重复定义，待合并

生产经验（新）：工人读不了仓库外路径（external_directory auto-reject 杀会话）；
标量-标量乘在 ascription 里写 `*` 不写 `•`（isDefEq 死循环）；定理应用严格按签名
参数个数；验收构建必须自然退出（掐死时 error 未 flush 是假绿）；闸误杀先修闸
（`--relative` 路径事故，`1a32e53`）。

**planarity 收官（2026-09-11，已解决，`48ff904`）**：原先卡住的 2 枚
（`solid_of_dartset_leads_into_fan_triangle_fan` + `MOZNWEH`）已通过自建体积层闭合。
关键技术路线（可复用于后续 Volume/Packing/Local 章节）：
- `Kepler/Geom/Volume.lean`：`sol` / `sol_spec`（vol1.hl，`Classical.choose` 编码）。
- `Kepler/Geom/SectorArea.lean`：2D 扇形面积 = ρ²θ/2（`Complex.polarCoord` 变量替换）。
- `Kepler/Geom/WedgeVolume.lean`：HOL `VOLUME_BALL_WEDGE`（球∩楔形 = azim·2r³/3）——
  含平移/旋转归约、ON 标架等距、`azim↔arg` 桥、Fubini + 扇形积分。
- `Kepler/Geom/LuneVolume.lean`：`dihV`、`azim_dihv_same`、`WEDGE_LUNE_GT`、
  `HAS_MEASURE_LUNE(_SIMPLE)`。
- `Kepler/Geom/SolidAngle.lean`：HOL `VOLUME_SOLID_TRIANGLE`（= (Σ dihV − π)r³/3）。
全部零 sorry、公理仅标准三。`solid_of`/`MOZNWEH` 改用 `sol` 陈述后由上述引理组装。
**经验**：这类研究级引理用「专项子 agent（同一主模型）+ 迭代编译 + 允许诚实部分完成」
可以攻下（本会话 4 个子 agent 分别拿下扇形、楔形、lune、solid triangle）。

**Conforming.hl 收官（2026-09-13，`d77c13f` 进 main）**：流水线
`scripts/auto_pipeline_conforming.sh` 批次 1-23 全部闭合（~230 枚定理，零 sorry、
标准公理）。收尾两枚 `WGVWSKE`/`GGRLKHP` 依赖 `lemma_connect_hypermap`
（~1900 行 HOL 巨证，6 段 sub-agent 流水攻克）+ Euler 恒等式 ⇒ `Hypermap.Planar`。
工作流在本书期间两次升级：多 lane 并行分支 + "axiom closure pending" 暂存机制、
two-stage（planner+executor）难题拆解法。已知坑：HOL 原文存在同名不同义的重复绑定
（如 `add_edge_graph` :2304/:2431），跨模块同环境会撞名——骨架设计阶段必须查重。

**polyhedron blocker 台账（2026-09-13 建，用户批准；2026-09-14 全部核销）**：
原 12 枚真实 sorry 全部闭合——前 9 枚（`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`、
`EXISTS_EDGE_POLYTOPE`、`AMHFNXP_BIJ`、`EXISTS_EDGE_AT_VERTICES`、
`CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`、`BSXAQBQ`、`POLYTOPE_FAN80`、`WBLARHH`）+
末 3 枚（`POLYHEDRON_FAN`、`EXPAND_EDGE_POLYTOPE`、`FLVNSME` ~990 行巨证经
P1-P5 分段流水攻克）。**polyhedron.hl 100% 达成（71/71 定理零 sorry + 根构建绿，
`c425db2` 进 main）**。

## Phase 6 — 集成与交付 🟡（装配脊柱已立，接口 1/4 闭合）

- [x] **装配脊柱 `Kepler/Assembly.lean`（2026-09-19，`0742680a`）**：HOL `kepler_conjecture_with_assumptions_and_archive` 逐行镜像；四接口 sorry 冻结（`nonlinearInequalities`/`linearProgrammingResults`/`textCapstone`/`goodListArchive`）+ 真证明 `assembly`（tame_classification 分量由 Phase 2 已证定理直接接线）；设计文档 `docs/phase6-spine.md`，折算点登记 `docs/statement-fidelity.md` 附录；脊柱故意不被根模块 import（终装配时接线）
- [x] **接口 4 `goodListArchive` 闭合（P6-C，2026-09-19，`05b9653d`）**：19,715 图（Tri 9 / Quad 1253 / Pent 16080 / Hex 2373）good_list 三合取项全库 native_decide，23 分片 + 内核组合器（take/drop 链，覆盖完备性由类型检查保证），`#print axioms` 零 sorryAx
- [x] **可达债务探针（P6-F，`1618f6a4`/`0b9ac85a`）**：DEBT.md 新增"主定理可达债务"节——`the_kepler_conjecture_from_interfaces` 的 `#print axioms` = sorryAx（剩余 3 接口）+ 624 特许 shard 公理 + 标准三，异常项无
- [ ] 接口 1 `nonlinearInequalities`：**155 定义闭包已 B=112/124 就位**（2026-09-20，批 1/2/3/5/尾批，`42bcf24a`；余批 4×12 赖 LA38 未移植 lane）；单案例粘合试点已打通（C3397113841，IneqPilot 入 main）；待 G4 内核证书接入 + 六 ID 清单填实
- [ ] 接口 2 `linearProgrammingResults`：桥模式已验证（P6-D 原型）；**持久化重跑 100% 收官（2026-09-24）：主批 6,866 + glpsol 尾部 59/59 PASS 零失败，43,078 LP 全部内核验证（产物含 sha256 + 账本交叉校验 + 公理足迹）**
- [ ] 接口 3 `textCapstone`：待 Phase 5 填证收官 + 镜像语义差绕行（ELLLNYZ 析取形，P6-C 原型已探明）
- [ ] 终装配：脊柱接入根模块 + 替换 Statement.lean:111 的 sorry
- [ ] 全量公理审计终验（目标：仅 propext / Classical.choice / Quot.sound + 限定 native_decide）
- [ ] 最终文档与复现脚本

---

## 整体估计

- **计算三线**（Phase 2/3/4）：图枚举 ✅100%；LP ✅100%（持久化重跑 2026-09-24 全收官：6,925/6,925，43,078 LP 全内核验证）；非线性求解层 **68/176（39%）可信闭合**（2026-09-20 修订：92 prep 家族闭合证据链不可信已降级，详见 Phase 4 节），残余 16 条已列清单；内核闭合 **G4 已百万叶级量产**（**8 案例端到端进内核**：最大 1,670,962 叶 5h19m；2026-09-18 首个 sqrt/atan 全量案 QITNPEA_3725403817 闭合；**5490182221 + 2570626711 双双全链贯通至内核构建（合计 351 万叶、18,874 分片，分别构建至 784/6321、770/12553 后于 2026-09-24 应用户要求暂停，olean 保留可续跑）**；BIXPCGW repair STUCK 收官、残留叶特征入 `docs/projects/archive/bixpcgw-residual.md`——治本归 549 加速项目（TM 已合 main，opencode 车道 ite-hull 4.8× 叶数削减 + schema v3 试点 16/20 PASS + df-hull 唯一路径实证）；剩 10 证书收尾 + 92 prep 家族重做方向待定 + 155 定义粘合）。
- **文字证明**（Phase 5，占全项目工作量 60%+）：已完成 hypermap + fan + topology + **planarity 100%** + **Conforming 100%** + **polyhedron 100%（2026-09-14）** ≈ **61.8k 行 HOL 源全证**；**packing 99.4k 骨架 100% 陈述（2026-09-15，25 模块 20.5k 行 Lean / 920 sorry 填证期）**；**local 174.7k 骨架 100% 陈述（2026-09-16，39 模块 / 1793 sorry 填证期）**——至此全书主体三章陈述层齐备，剩余：填证 2713 sorry + tame 文字章（TameSpine 线 2026-10 立线，首本 tame_list.hl 已收官 649 件，余 63 文件）+ trigonometry 10.5k / volume 1.1k / fan 残余。**按行数口径 ~17%+全部骨架**；考虑已完成部分含大量最难地基（hypermap 构造、体积测度层从零建），而 local/packing 多为模式重复引理工厂，**工作量口径估计 35-45%**（opencode 侧按骨架完成口径自估 ~75%，口径不同：其将骨架陈述计入完成度）。按 packing 实测吞吐（99.4k 行骨架 2 天）线性外推，剩余填证约需 30-45 天连轴。
  另：**体积/测度论层已从零建成**（`Kepler/Geom/*.lean`，~3.4k 行，含 HOL Light 多元库的球面立体角链），这是原计划里没算到的关键前置，现已就位，后续 Packing/Local 可复用。
- **全项目粗略完成度：~55%（packing + local 骨架全部就位，填证期全面开启）**。

## 验证纪律

1. main 分支：`lake build Kepler` 全绿；**2026-09-17 政策变更（DECISIONS.md）：main 允许携带 sorry 债务，债务刻度 = `DEBT.md`（`lean/scripts/debt_ledger.py --with-spine` 生成，基线 2400，**2026-10-10 账本现值 1719**（09-29 账面 1951 → 净 −232；脊柱公理探针首次本机全闭包跑通：主定理 axiom 面 = sorryAx(3 冻结接口)+624 shard+标准三，异常项无））**；终验标准不变只是推迟——项目终点要求主定理证明本体零 sorry 可达 + `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`（+ Phase 2 限定 native_decide）；陈述保真审查（`docs/statement-fidelity.md`）是唯一质量阀门，不随本政策放宽；
2. 批次闭合标准：该批全部定理零 sorry + 根模块构建绿 + 陈述保真抽查；
3. 自动化 harness 的提交由机械闸背书 + 主 agent 审计兜底；人工派工的提交由主 agent 逐块验收。


## 2026-10-20 晚/21 mega 波（三发批准落地日 + SF-45/46/47 三连 + 批 60-66 六连 + Phase 5 移交令）

- **十一发波终账（双并行车道，用户批准"并行"）**：收获车道（p4pa24d）任务 1+3
  全量落地（`80b4554d`）——SF-44+45 应用（语句净变更 = 两 patch 叠加逐字，
  全量波差最终权归档 `44b-…fullwave.patch`，5dcb2695）+ cover_strong 四件装配
  八新件 + :3625 gated 换接，**PA24 直 sorry 2→1**；p4pa24e 车道交 PA2 shim
  退役（`a5960367`，直 sorry 28→26）+ cover WIP 分期稿。快照撞名事故互相恢复。
- **十二发波（`39d26502`）**：k=4 臂 kit 六件真证（纯追加 345 行零 R1 债）；
  scaffold 3 诚实分期未收口（直 sorry 1→1），**两墙定位**——墙 A（k∈{2,3}
  叶胞非零测性 = R1-GIANT 人质）、墙 B（点态冻结语句 = HL 测度级原文的真
  加强形）。**SF-46 立案并获批**（点态→测度级降级，3c1f6f5c/3a029f3f）。
- **十三发波（交付已核验、待 SF-47 入库）**：按获批 SF-46 收口 scaffold 3，
  **PA24 直 sorry 1→0 实测三闸绿**（8700/8715/9359 jobs）；覆盖链 R1-free
  实证；但语句净变更两 hunk——hunk 2（capstone cover_strong 末合取同形换接）
  超任务书范围，**SF-47 立案待批**（1463ad31，+2/−2 已归档）；批则 46∘47
  联合走闸入库（44∘45 先例），不批维持 12gen 态。新 taint 一条如实记账：
  `p24_edgeX_of_leaf23` 消费 PA2 `RVFXZBU2_concl` shim（R3 家族，入清理盘点）。
- **TameSpine 批 60-66 六连（B3 链 W2 起跑）**：批 60 AUQTZYZ 前段
  （`7854f380`）→ 批 61 atom 块（`04bbab7d`）→ 批 62 EPC 地基 19 件
  （`cc9da66a`）→ 批 63 **主峰 EXISTS_PATH_COMPLEMENT 十二合取全闭**
  （`aa81f704`）→ 批 64 **AUQTZYZ 章收官**（`9fd64f83`，hedge 弱化形缺口
  如实挂账）→ 批 65 **hedge 闭合 = AUQTZYZ_hol 全形**（`89608ac9`，第三
  路线短一量级）+ RXOKSKC 开链至 :507 → 批 66 六站前件 5/6 闭 :25-:492
  （`f7a559d6`）。**批 67 在飞**（冲 :523 RXOKSKC = **A9 接口件**）；雷区
  登记至 #167。
- **发车冻结两道令**：10-20 "每个 lane 结束后不发新的"（`6039cb69`）→
  10-20 晚三发批准（十五分钟间隔，`655191f5`）→ **10-21 收口令："这些 sub
  agents 结束后，不要启动新的了"**（`b5da6e4b`）——在飞两条（批 67、舰队）
  跑完即止；gen-8（含 decide-mode 开关）取消待令。
- **专家四条处理**（`d16e9985`/`b3b22d1d`）：STATUS 主表刷新（Phase 3/4/5
  陈旧口径清账）；**projects/ 首次收官归档 14 件**（archive/README 记规则+
  因由表，全库 12 处引用同步）；HANDOFF 交班清单 wrap 规则向实践靠拢
  （波次节并入 STATUS 即算数）+ 新增⑥收官归档条 + 文档债拐点记账
  （proposals 124KB/playbook 81KB，触发线 200KB）。
- **Lake 旗标事故**（HANDOFF 新增 §5.5，`ec0eb263`）：Lake 5.0.0 无
  `-j`/`--jobs`（任务书 `-j2` 使十二发波首发秒死，车道自救）；`-K` 未知键
  静默毒化缓存（编排者亲测）。并发控制固化为操作性纪律。
- **root runner**：2,500→4,340/6,900（135 条/时提速中，零 fail），预计周三
  深夜-周四凌晨收；收后 ZCode 做终账 + spine 探针补跑（--with-spine，
  债图 10-20 节已记欠账）。
- **🔴 移交令（用户 2026-10-21）**：**Phase 5 → opencode**（接管入口
  `docs/projects/phase5-opencode-takeover.md`，自足简报）；ZCode 只收工
  批 67/舰队/root runner 三件。TameSpine 线交棒点 = 批 67 落库后的批 68
  （RXOKSKC :523-:1105 章末处方已备）。

## 2026-10-20 波（tame_list 收官 + 十一发波分期 + 发车冻结）

- **B1 线里程碑**：批 59 落地（`f0361c78`）——tame_list.hl 全本收官：:23-:14428 由
  59 批零缺口覆盖，649 主定理全真证（勘误：650 口径实测 649），闸 PASS
  @uniqFlattenAllUniq，axiom 十六探针零 sorryAx。
- **SF-45 立案并获批**（`3beae353` 立案 / `4b75ec83` 批准入账，用户 "SF 45: 同意"）：
  PA24 `p24_cell_cap_dihX` hwit 前提加 ¬nullSet 门（SF-44 应用批 1 行联动微调）；
  无门形对退化见证角点胞无货源，加门后与 HL :2818 门形对齐。与 SF-44 同批
  应用走"全量波差最终权"归档闸。
- **十一发波交付（双并行车道，用户批准"并行"；终账以收获车道为准）**：
  - ✅ **任务 2 PA2 shim 退役（p4pa24e 车道）**：删 `XNHPWAB1_concl`/
    `XNHPWAB4_concl` 两 sorry shim（零代码消费者，下游走 PackingConcl
    `_discharged` 真证版），PA2 直 sorry 28→26，下游全链重建绿
    （闸 @XNHPWAB2_concl，`a5960367`）。
  - ✅ **任务 1+3 全量落地（p4pa24d 收获车道，`80b4554d`）**：cover_strong
    四件装配八新件（走廊点覆盖/门下见证/hnullarm 全族=楔族活胞恒有正锥帽迹
    定案/hcov 组装；五件标准三零，witness_of_trace 携 AJRIPQN inherited、
    cover_strong 携 scaffold 3 inherited，均如实记账）+ SF-44 逐字应用 +
    SF-45 §45.3-2 hwit 门形微调（编排者逐字核验 = 44∘45 批准文本）+ :3625
    gated 换接。**PA24 直 sorry 2→1**（唯一残余 :3366 `p24_cap_wedge_cover`
    scaffold 3），闸 PASS @p24_cell_cap_dihX（STATEMENT-FIX，全量波差
    最终权补丁 `44b-…fullwave.patch`，`5dcb2695`），根全树 9359 jobs 绿；
    `p24_cell_cap_dihX` axiom 标准三零。SF-44 立案时"应用后 2→1"承诺兑现。
  - 📦 p4pa24e 车道任务 1 诚实分期稿（①②③ ~730 行未收敛 WIP + 12 根因
    fixnotes 处方）留档，作 scaffold 3 残余收口参考底稿；两车道文件不相交，
    快照撞名事故互相恢复有账。
- **十二发波处方（挂起待用户令，发车冻结中）**：scaffold 3 残余真证收口
  （缺口件 =「叶表 mcell 非零测性」+ 侧指认 min-max）→ PA10 可测链 →
  PA7 唯一性族 → fan 三件 → AJRIPQN 本体（门下见证的 inherited 债主）。
- **发车冻结（用户令）**："每个 lane 结束后不发新的，等我新的指令"——批 60/
  W8 gen-8/GIANT 分期/十二发波全部挂起；HANDOFF 已入档（`6039cb69`），巡检
  自动化钉死不得代发。
- **后台**：root runner 2,500/6,900 零 fail（预计 10-22 上午收）；EULER3 v19 在飞；
  TM 舰队重烤在飞。

## 2026-10-14/15 mega 波（八线两班全收日 + 环境事故 + 负载治理）

**Lean 侧 15 提交十四闸全绿**（0f4999e8..f40cfe4c），两批八线全收：
- **PA18 双波**：ZASUVOR+CFFONNL kit（`bdd93009`，ZASUVOR 定义闭真证零上游债）→
  **CFFONNL C2+C3 收官**（`6c37299c`，+519）——CONVEX_PLANE_INTER 第三击
  （WithLp 分量级 funext+ring 收口）+ CONVEX_R3_INTER（**纠前任 NEEDS 处方之
  错**：max-形 s 会出负权，改 HOL 同款 abs-形）+ CFFONNL 十槽全装配 =
  **MCELL4_LEAF_S_LEAF 阻塞面清零**；C4 侦察判死 MHFTTZN1 消除路线（通用
  VoronoiList-affDim 桥不存在）。grep 口径 64→42。
- **PA25 四波**（123→101）：coplanar 消费（`488f688f`）→ MERGED 双件转真
  （`239e9c53`；TEWNSCJ 卡 PA3 opaque 常数桥待 SF 立项）→ **楔形双件
  MCELL4_LEAF_S_LEAF+MCELL4_DOMAIN**（`5c09ab9f`，阻塞清零当日收割）→
  **GDRQXLGv3 解析桥**（`0509d5dc`，rad2 支升真+WEDGE3_Y4 rad2 支就绪）。
- **PA21+Assembly 接线地基**：merge-ineq 四件+三投影（`b5f64641`，11 新件全
  零债）→ **bank 具名投影 62/62**（`ed9b939a`）→ **Assembly
  nliPackNonlinearRest 62/62 展开**（`f79c0fb4`，3 条真闭合零债 rest
  2/4/60 + 59 具名骨架 + 13 裸链位投影，nli 28+127 主波就绪）。
- **SF-40**（`72dcf9a1`，用户批准）：LA11 `x1DeltaY_p11` def 体误抄纠正
  （旧体下冻结定理为假命题有反例）+ atn2 同根十件填实（36→26）。
- **措辞诚实化 ×2**（`a23b86dc`/`3d2e9b64`）：PA21 MCELL2_SOL、PA14 双桥的
  "PROVED/sorry-free" 虚标经 #print axioms 核查降级。
- **Phase 4 双武器**：W6a mono 原型（`17474eae`，**13/13 盒实证翻 POS**，锚
  未达=df-enclosure 16× 污染先紧 enclosure；顺手抓 W5 div 反号真 bug）→
  **W7 evalReal 链式法则**（`9b191a85`，MonoCorner.lean 880 行八主定理零债，
  checkMonoCorner 全 decide 总装 + `--mono-lean` 内核重放单盒端到端；W8
  批量化接续：sqrt re-bake/分树/flat 维）。
- **TameSpine 双批**：批 15（`c4cf64bb`，Hypermap_iso 桥章）+ 批 16
  （`f40cfe4c`，quotient_list 章 :9375-:9903，9 真证+7 记账）；B1 链至
  HOL :9903+收束件；批 17 起点 :10100（前置 transform 定义层）。
- **DEBT 44,646→44,674**：nli 59 具名骨架（细粒度记账债）压过填实净额
  （PA25 −22 / PA18 −22 / LA11 −10 / Assembly +58 记账）。

**环境事故 + 负载治理（双入册）**：mathlib 删包事故（根因链：车道软链
packages 进隔离 clone → lake URL 校验 rm -rf；深层：全局 gitconfig
`insteadOf` https→git@ 致 lake 判 URL 变更）——确定性恢复（浅克隆
@905b9581 + cache 8639 oleans + 冒烟绿 20s），新纪律：**隔离 clone 禁软链
packages，cp -Rc only**。负载两轮：renice 降载（p4asm 九工人 nice 15）→
B 道 nohup nice-5 继承饿死（starvation 3× 实测，renice 无法升优先级）→
**fresh 重启 nice 0 + --timeout-min 180 平权续跑**；假超时账目手术（B031-033
剔除重队）编排者亲办。

**C1.7 长尾（自治在跑）**：A 道 54 绿/12 非 ok @B067；B 道 38 绿/4 非 ok
@B039；root runner 独立环境照常。跑空后编排者统一假超时重队。

**收口令执行**：两批八线全收零在飞 Lean 线，停等用户指令。待拍板三项：
W6b 方案 A（√ mantissa 填充）、TEWNSCJ PA3 opaque 桥 SF 立项、W8 mono 批量化。

## 2026-10-16/17 mega 波（C1.7 全线收官日 + 内存事故 + 七 commit）

**C1.7 全线收官**（用户令"都发"波）：①**PA25 wwtcount6_y finisher**（`7b492f63`，
+240/−2，闸 PASS）——"两侧同 6 被判等器全拒"是烟幕弹，真解法 = congrArg 把
ncard 等式整只推过 Nat.cast 让数值等式不被调用；②**批 20 TameList20**（`9a4406d5`，
六件全真证；勘误：交接脚手架从未编译过，"已过审计"是虚账）；③**DomOK v2**（`b661ff07`，
+896/−22）——mono stage-B 批化（domTable 单趟+纯表消费器+双 O(n) decide 错表
只能 fail），sb12 A/B 定位真瓶颈 = W8 默认 rung 2048 闭式 atan 内核 Taylor
（witness 冗余仅 1.6×），下一杆 witness 位降 rung 移交 W8；④**SF-42**（`3e8cdca6`，
STATEMENT-FIX 闸 PASS）——sqrtRel 相对粒度 2⁻⁸⁰ 恒宽根治 var-at-point 发散，
C549Mono 12/12 重烤转绿，**TM 舰队 197 模块/18,477 站点重烤=尾波排队**；⑤
**Text/LP infeas 落地**（`7ba6b5b7`，193 文件 +42,761/−950，闸 PASS）——189
闭合模块+列→行桥 LPFarkasCM+骨架转发，**infeas 段 sorry 清零**；⑥**统一终账**
（`51f3403a`）：全队列 189 条列主序重刷 **189/189 全绿零失败**（最慢 662.6s）。
DEBT 44,481（−193：infeas 清账 189+本波收官 4；debt_ledger.py 重生成）。

**列主序手术（本波方法论主角）**：行主序 coreColSum 每列重走全行+行内位置游走
= O(列×行²) 内核遍历（B087 ≈2×10⁹ 链表访问→足迹 65.8GB>36GB RAM+30GB swap
不可完成；B086 侥幸 4h22m）；列主序单列一趟乘加后 **B086 33.8×/B087 9m10s**
——与 DomOK v1→v2 同款病理第二次以重排/批化治好（大核 decide 的嵌套表布局
= 结构性内存陷阱，巨表一律列主序或批化）。

**16:13 内存打穿强重启事故**：五 lane 并发构建+双驱动+巨物同机 → swap 打穿 →
WindowServer 看门狗强重启；**/tmp 全清**（五车道克隆+redo 工作区损失）；
排查顺手破案：此前"环境收割者"25-55min 杀 lean = 磁盘满→swap 断供→jetsam
（15 车道克隆 ×16G 塞满 460G 盘）。**内存三规立**（入 playbook）：lane 串行/
起 build 前查空闲 ≥12GB/B 级巨物禁与构建并行。打捞纪律验证：删除前 diff
快照存 c17_backup → SF-42/wwtcount6/批20 三线全部从打捞物零损失续跑
（wwtcount6 死前 11 分钟刚编译通的 Mini2 直接成了交付钥匙）。

**EULER_TRIANGLE**：二代诚实止损——:2081 真实需求 = EULER_TRIANGLE 闭式
立体角定理本体（HOL ~1300 行微积分 GIANT，全仓无立体角闭式资产），非三角链；
W-乘积法设计+sympy 符号/数值双验证完成、dih 桥已证、工件备份；三代按施工图
在飞。**root runner**：16:13 阵亡→当日复活，账本零损失，3,485/8,283 本轮
done（含 1,791 历史 fail 重试消化中命中率 ~100%），ETA ≈ 34h；**六小时巡检
automation 上岗**（CronCreate，自动救活双驱动+系统越线只报不动）。

## 2026-10-13 波（三线全收日 + 收波停等令）

**TameSpine B1 三连批**（批 10-12，`1baa5d6d`/`93181878`/`50b35415`，+2,232 行/
94 件全真证零 sorry）：:5580→:8920 无缺口——批 10 = 前任限额阵亡完整草稿的端到端
独立机械验收后零编辑采用（salvage 验收模式再验证）；批 11 = 原子理论章全量
（atomListBij 帽石）；批 12 = MEM_EXTENSION→min_num 块（lQSpine 证明参折算诚实
记账）。批 13 起点 = HOL :8921 contour_list_cons 旗塔章。

**脊柱**：A10 第二波 `a54ebb61`——**CRTTXAT 帽石装配完成 = B6 出口件一号全清**
（arc kit 五件套全零；方法论突破 face_sum_snd_eq_fst 鸽笼原理替代全树未移植的
SUM_ORBIT；TameLp 7→6）；A6 续四 `daa89ba9` + 钥匙件 salvage `0ab0bc73`——
柱② 仅剩归一化本体一件（Lean 路线 spec 已入 NEEDS，无需 ℝ^150）。

**Phase 4**：路由表批准 `715addd3`（R1-R4 混合策略）+ 92 prep 画像 `7bc4cbb7`
（94.3% 记录可立即灌装）+ W3 四工位 `aaae330c`（**guard-straddle = 证书结构
缺口**根因钉死 + disj 端到端首绿 + decide 成本 122.7 s/叶实测 + formal_ineqs
考古）。diagSB 孤儿进程事件收尾（新雷区三条入册）。

**C1/A12**：**C1.6 G5 收官 `1f3da927`**（gen_farkas.py，189/189 精确预检 +
试点 B 端到端 [propext]，93 族零 UNKNOWN——C1c"真实叶不闭合"缺口关闭）；
root runner 长跑 2,170/19,237 pass 100% @174.9/h（ETA ≈ 3.9 天，脱离进程不受
停令影响）。

**收官**：用户令"本批 sub agents 结束后不再启动新线"，三线全收后编排者停等
（详见 docs/e2e-debt-map.md 2026-10-13 增量节二）。

## 2026-10-12 mega 波（三件真数学日）

**三件真数学全部清账**（用户令，详见 docs/projects/milestones-and-risks-2026-10-12.md
与 docs/e2e-debt-map.md 2026-10-12 增量节）：①GRKIBMP 组全套闭合（B V2/A V2
解析手证+一行装配，residue16 销账 2/16）；②PA24 B2 支收口（泛具+退化换叶，
capstone p24_exists_mcell_not_flat 本体全真）；③AJRIPQN 闭合（SF-38 + 一行
机械闭合，GT 区最后一件真数学；勘误：pivot 反向早已闭合 GT-6）。其余：A2
脊柱接口收口（Assembly 49→22）；PA7 19→13（V3 点积 Finset-kit 全树首件）；
PA25 141→127；TameSpine 批 4-8 五批 ~3,600 行零 sorry（B1 :2936-5579）；
C1 立项+三波落地（LP 钉定 schema/Farkas checker/infeasible 占位退役，
A12 降为纯数据绑定）；SF 备忘录六件终账+项 37/38 应用；闸 EV22-24 三笔演进；
Phase4 常驻车道设立（用户指令二）+ 5h 配额帽五线阵亡 salvage 全胜实录。
