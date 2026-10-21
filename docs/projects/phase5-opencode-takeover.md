# Phase 5 → opencode 移交简报（2026-10-21）

> **读者**：接手 Phase 5（文字证明移植）的 opencode。
> **写者**：ZCode 编排者（用户令 2026-10-21："未来这个项目逐渐会让 opencode
> 负责一部分……目前，我打算让他负责 phase5 部分"）。
> **目标**：本文自足——读完即可接手 Phase 5 产线，不需要考古对话史。
> 配套必读：`HANDOFF.md`（全局入口）、`docs/projects/tamespine-port-plan.md`
> （Phase 5 主产线的作战地图）、`docs/fill-worker-playbook.md`（工人手册）。

---

## 0. 项目 30 秒

用 Lean 4 + Mathlib 以"证书化计算"范式重造 Kepler 猜想端到端形式化证明
（蓝图 = Hales《Dense Sphere Packings》/ Flyspeck）。终态 =
`Kepler/Final.lean` 的 `the_kepler_conjecture_e2e`，公理面仅
[propext, Classical.choice, Quot.sound]（+ Phase 2 限定 native_decide）。
六大 Phase 中 **Phase 0/1/2 已收官，Phase 3（LP）计算收官待灌回，
Phase 4（非线性证书）量产中，Phase 5（文字证明移植）是最大头
（占全项目工作量 60%+），Phase 6（终装配）靠各 Phase 喂饱**。

**Phase 5 的产出物 = `Kepler.Text.*` 文字章模块**：把
`reference/flyspeck/text_formalization/` 下 ~359k 行 HOL Light 证明逐字
移植为 Lean（总量 ~11.4M 行 Lean 已在树，其中 90% 为生成 shard；
手写 ~1.15M 行）。终点消费方 = Phase 6 脊柱四接口之**接口 3
`textCapstone`**（`Kepler/Assembly.lean`，现 sorry 冻结）。

## 1. 移交时刻的精确状态（2026-10-21 凌晨）

### 1.1 已全本收官的章（不要重做）

| 章（HOL 源） | 行数 | 状态 |
|---|---|---|
| hypermap/hypermap.hl | 13,575 | ✅ 100% |
| fan/fan.hl 系（fan_defs/fan_misc/fan/CFYXFTY/hypermap_and_fan） | ~7,800 | ✅ 100% |
| fan/topology.hl | 4,718 | ✅ 100% |
| fan/planarity.hl | 15,463 | ✅ 100%（`48ff904`） |
| fan/Conforming.hl | 17,033 | ✅ 100%（23 批） |
| fan/polyhedron.hl + Polytope.lean | 3,200 | ✅ 100% |
| **tame/tame_list.hl**（TameSpine B1） | 14,428 | ✅ **100%（2026-10-20，批 1-59，649 主定理，`f0361c78`）** |
| **tame/AUQTZYZ.hl**（TameSpine B3 首本） | 2,624 | ✅ **100%（2026-10-21，批 60-64+65，`9fd64f83`/`89608ac9`）** |

### 1.2 TameSpine 产线（Phase 5 现役主力，opencode 接手的就是它）

- **66 个模块 / 28,234 行 Lean 全部零 sorryAx**（`Kepler/Text/TameSpine/TameList1-66.lean`）。
- **当前位置**：RXOKSKC.hl（1,105 行，B3 第二本）六站前件 5/6 已闭
  （:25-:492 全段，批 66 `f7a559d6`）；**:523 `RXOKSKC` 是 A9 接口件**
  （Assembly 接口 9 的消费目标：`iso H (hypermap_of_list L)` 钉几何
  hypermap 到有限 list 表示）。
- **在飞**：批 67（ZCode 车道，冲 :523 + 章末）——**ZCode 收尾落库后，
  opencode 从批 68 接力**。批 67 的交付报告 + `TameList67.lean` 头注 +
  `lane_snapshots/t67/` 里有精确接续处方。
- **B3 剩余**（RXOKSKC 之后）：DANGEYJ(949)→PWSSRAT→OHCGKFU→PPLHULJ→
  NCVIBWU→PBFLHET→{DIOWAAS→RYIUUVK, QCDVKEA, PNXVWFS}→KBWPBHQ→
  {HOJODCM, LEBHIRJ, OBDATYB}，**14 文件 ~10,467 行**（§2 拓扑与依赖序
  见 port-plan）。

### 1.3 其余 Phase 5 章（骨架 100% 就位、填证期）

| 章 | HOL 行 | 状态 |
|---|---|---|
| packing/（Rogers/OXLZLEZ3/REUHADY/counting_spheres/marchal…） | 99,350 | 骨架 100%；填证推进中。**REUHADY1 (PA24) 直 sorry 已 1→0 待 SF-47 入库**（见 §4 治理）；链上仅余 AJRIPQN inherited |
| local/（IMJXPHR/QKNVMLB/XWITCCN/local_lemmas/terminal…） | 174,694 | 骨架 100%；填证推进中（LA5 POS_DIRECT 根系五件已真证） |
| trigonometry/（trig1/trig2/euler） | 10,511 | **EULER 三代车道止损收官**：W-乘积链全绿（scratch 479 行快照 `lane_snapshots/euler3/P21EulerScratch.lean.v23b`），余 19 错有完备接续处方（`FINAL_STATUS.md`），**主仓零改动**——重启 = "euler 四代"，待用户令 |
| volume/vol1.hl | 1,421 | 已用 :18/:458/:651 三段，其余待移植 |

### 1.4 账本与债务刻度

- `DEBT.md`（生成物勿手改）：总 sorry 44,478（2026-10-20 重生成；
  其中 43,078 为 LP 叶户占位，可比口径 **1,400**）。
- `docs/e2e-debt-map.md`：**派工依据**（贪心触达制：cleanable(L) 不动点
  排名，lane 排序依据 = 本图）。最新增量节 2026-10-20。
- spine 探针（`--with-spine` 主定理可达债务面）**欠一次补跑**——root
  runner（ZCode 辖）周四收完后的安静窗口做。

## 2. 工作模式（relay 全协议——照此执行，别发明新流程）

### 2.1 批次制

**1 批 = 1 个新 Lean 模块 + 根构建绿 + 零 sorry + 陈述保真对账 + 交付报告**。
体量 15-20 定理 / ~400-700 行（先例：Conforming 740 行/批、TameSpine
~400-700 行/批）。每批的"接续点"（下一批从 HOL 哪行吃到哪行）写进
模块头注 + 交付报告，**下一批任务书 = 上一批交付报告的接续点节**。

### 2.2 车道纪律（红线，违反即废）

1. **冻结语句一字不动**：既有定理/def 签名逐字冻结；新件纯追加
   private（跨模块需要时按"公开件同证重推导"体例或 §0' 本地私桥复制
   体例——见 TameList63/65 先例）。
2. **零 sorry**：卡死件按止损纪律诚实分期（已完成件照交 + 精确接续处方 +
   残留根因清单），严禁 sorry 顶替。先例：批 62（19 件落地 + 1,429 行
   草稿留快照给批 63 照方收口）。
3. **移植失真就地裁定**：陈述与 HOL 逐字对账；发现"假陈述"（过强/丢约束）
   不硬填——走 SF 流程（§2.5）。先例：SF-44（丢约束）、SF-46/47（移植期
   加强度）、PEUTLZH 体例（同语句别名件记档不落）。
4. **零 git 写操作**（车道不 add/commit/push）、构建用 plain `lake build`
   **无任何旗标**（Lake 5.0.0 无 `-j`/`--jobs`；**禁 `-K` 未知键**——静默
   触发 reconfigure 毒化缓存，HANDOFF §5.5）。
5. **内存纪律**（12 核/36G Mac）：重 lean 构建同时 ≤3；每 lane 单 build
   串行；只用热缓存（rsync 自主仓后仅变更闭包重编）；冷重建只进安静窗口；
   `memory_pressure -Q` 空闲 <50% 停手报告。

### 2.3 克隆纪律

- 工作克隆 = rsync 自主仓（含 `.lake` 热缓存）+ `bash scripts/fix_pkg_origins.sh`
  （防 mathlib 包 origin 校验失败触发 6.5G 重克隆）。
- 现成热克隆：`/tmp/p4t21`（TameSpine 线，缓存暖至 TameList66）。
  /tmp 重启即失是已知事实——**关键交付必须落 `c17_backup` 快照**
  （`/Users/zhangzhuo/c17_backup/lane_snapshots/<lane>/`，全文件终稿 +
  构建日志 + axiom 探针日志 + MANIFEST）。

### 2.4 交付协议（交付自检三条——每批报告逐条给证据）

1. 主仓落盘复核：新模块为唯一 untracked（`git status --short` 仅一件
   `??`），`git diff HEAD` 空（零既有文件触碰）；
2. md5 三方一致：主仓 = 克隆 = 快照；
3. 报告与实际一致：开工基线 md5 对账、构建 jobs 数、axiom 探针输出为
   实际运行结果（`lake env lean` 探针文件，`#print axioms` 全部新件）。

### 2.5 陈述保真治理（SF 流程）

**Statement 冻结是全项目唯一质量阀门**。需要改语句时（发现假陈述/死前提/
移植期失真）：
1. 在 `docs/statement-fix-proposals.md` 立案：分级 + 机理 + **(a) HOL 逐字
   引文**（reference/flyspeck 对应 .hl 行号）+ (b) 修复补丁归档
   （`docs/statement-fix-proposals-patches/N-*.patch`）+ (c) 验收与应用计划；
2. **用户批准**（"SF N: 同意"）后才能应用；
3. 应用批走闸：`GATE_MODE=STATEMENT-FIX SF_ITEM=N SF_PATCH=<归档 patch>`
   `lean/scripts/auto_gate.sh <file> <验收定理>`——闸做语句 hunk 逐字
   multiset 对比 + 构建 + axiom 探针（修复件须零 sorryAx）。
4. 多 patch 叠加应用走"全量波差最终权归档"（先例 44∘45、46∘47：把整波
   diff 归档为补丁，statement 净变更 = 各批准 patch 叠加逐字，编排者核验）。
- **已决先例速查**：§13/15/16/25/28/29/36/37/38/39/40/41/42/43/44/45/46
  已应用；§47（PA24 cover_strong 末合取测度级形）**待批**。

### 2.6 雷场 register

**#1-#167 已入 TameList1-66 各文件头注**（每批新雷区顺延编号）。
要点速查：TameList59-66 头注含最新 60+ 条（omega 原子化 #127、camelCase
普查盲区 #157、泛型层 `L[i]!` 走 ?-some 形 #160、Equiv.Perm.ext #154 等）。
**待办**：雷场收口进 `docs/fill-worker-playbook.md`（81KB，已到重组拐点，
HANDOFF 文档债节有触发线与方案）。

### 2.7 走闸（land 一批的标准动作）

```bash
git add lean/Kepler/Text/TameSpine/TameListNN.lean
cd lean && ../lean/scripts/auto_gate.sh Kepler/Text/TameSpine/TameListNN.lean <锚定理名>
# GATE-PASS 后回仓根：git commit（ dense 中文信息：逐件账+HOL 锚点+雷区+接续点）+ push
```
闸的规则：单文件 tracked-diff、冻结签名检查（新文件零删除豁免）、构建、
锚定理 axiom 探针。多车道并行用 `LANE_FILES=a,b` 白名单。

## 3. 短期计划（opencode 接手即干，按序）

1. **批 68**：RXOKSKC :523-:1105 章末（处方 = 批 67 交付报告 +
   `lane_snapshots/t67/`；大证五槽中 iso 三槽 :928-:1065 为全章最重段）。
   RXOKSKC 收官 = **A9 接口件在树**（`iso H (hypermap_of_list L)`）。
2. **B3 链推进**（14 文件 ~10,467 行，依赖序见 port-plan §2）：
   DANGEYJ(949) → PWSSRAT → OHCGKFU → PPLHULJ → NCVIBWU → PBFLHET →
   {DIOWAAS→RYIUUVK, QCDVKEA, PNXVWFS} → KBWPBHQ → {HOJODCM, LEBHIRJ,
   OBDATYB}。链顶 Hojodcm = AQ 入口前置。
3. **B2 叶件**（3,040 行，可并行插队）：arc_properties、Inequalities、
   tame_opposite、MEEIXJO（AUQTZYZ 已在 B3 收官）。B2 收 = opposite_
   components（A7 前置）+ arc 全章（B6-U1 前置）。
4. **B4 AQ 链**（17,585 行）：Aq1→Aq23→Aq4→{Aq56,Aq7,…,Aq11}→Aq12
   (←MEEIXJO)→Aq13。Aq56.TL_LAST 是 reduction1 消费件。
5. **B5 reduction 链**（25,361 行）：R1→R2→{R3, More_lemma1→More_lemma2→
   betwn_corek→betwn_core0}→R4→R5。**R5.restricted_hypermaps_are_
   planegraphs_thm = A9 出口件**；R4.generatePolygon 系落 AFP
   FaceDivision/GeneratorProps（可拆 3 子波）。
6. **B-D 簇**（port-plan §4）：B-D1 A7 支撑（Tame_list map/REVERSE 家族
   + Asfutbf iso_opposite 群）、B-D2 correspondence（Oxaxucs + Asfutbf
   hyp_conj）、B-D3 A8 本体（Wmlnymd→Dpzgbyf→Jcajydu 装配 → **A8/A9 离账**）、
   B-D4 A2/A5 镜像（Asfutbf 镜像链 + Geom 侧 azim_mirror 工具链单列）。
7. **W0 keystone**（串行，阻塞 A7/A8/A9）：S1 hypermapOfList 构造 + S3 Iso
   孪生桥 + S11 GoodGraphV4/GoodListNodes def 忠实化（Assembly def 体，
   走 STATEMENT-FIX——注意 Assembly 侧 GoodListNodes 现为 True 桩）。
8. 每聚类收口跑一次公理审计（新模块不 import Assembly 本体，防接口 sorry
   污染——GoodListShard 惯例）。

吞吐校准：TameSpine 实测 66 批/1.5 天≈ 早期批次慢、近期 ~1-1.5h/批
（接力成熟+载体命中率高）。B3 剩余 + B4 + B5 ≈ 50-70 批量级。

## 4. 长期计划（Phase 5 → Phase 6 会师）

1. **Phase 5 全书收官** = port-plan §7 W2→W5 波次走完：B3/B4/B5 三大链 +
   B-D 簇 + B6 fan 几何出口（CRTTXAT、HRXEFDM、tame_general 余量 →
   **A10 可接线**）+ B7 FATUGPD（独立出口）。
2. **出口件 ↔ Assembly 接口映射**（port-plan §3 全表）：A7（B-D1 后离账）、
   A2/A5（B-D4）、A8/A9（B-D3+Jcajydu 99 行装配）、A10（B6 + mqmsmab-scout
   Step 0-3 单列装配本体 250-350 行）。
3. **接口 3 `textCapstone` 闭合**：Phase 5 填证收官后，capstone 证明体
   （现真实推导骨架）吃通 packing 章链 + ELLLNYZ 析取形镜像语义差绕行
   （P6-C 原型已探明）→ SF 流程解冻。
4. 终点：Phase 6 脊柱四接口全闭 → `the_kepler_conjecture_e2e` 公理面
   仅标准三 + Phase 2 特许 → 全量公理审计终验。

## 5. 边界与协作（谁管什么）

| 域 | 负责 | 备注 |
|---|---|---|
| **Phase 5 文字移植**（TameSpine 线 + packing/local/trig 填证） | **opencode**（本简报） | 从批 68 起接力 |
| Phase 3 LP（root runner 收工 + 证书灌回 + 接口 2 档案件） | ZCode（收工中）→ 之后待定 | root runner 周三深夜-周四凌晨收，产物灌回是独立收尾步 |
| Phase 4 非线性证书（G4/W8 加速线 + 接口 1） | ZCode → 之后待定 | gen-8 方案已备未发（用户令冻结） |
| Phase 6 脊柱与终装配（Assembly/Final） | ZCode → 之后待定 | A1-A5 已清；接口 4 已闭 |
| SF 治理 | 起草方起草，**用户批准**，任意一方走闸 | 立案/归档规范 §2.5 |
| EULER（trig/euler.hl） | 待用户令（euler 四代） | 接续处方完备，见 §1.3 |

**通用纪律跨系统有效**：Statement 冻结、SF 流程、零 sorry 红线、构建
纪律（§2.2-2.4）。两个系统不并发写同一文件；Phase 5 内部 lanes 由
opencode 自行调度（接力制已验证）。

## 6. 文档地图（去哪查什么）

| 要什么 | 去哪 |
|---|---|
| 全局入口/已知坑（血泪清单 §5，含 Lake 旗标 §5.5） | `HANDOFF.md` |
| Phase 5 作战地图（64 文件盘点/依赖拓扑/批次表/出口映射/波次） | `docs/projects/tamespine-port-plan.md` |
| 工人手册 | `docs/fill-worker-playbook.md` |
| 派工依据（可达债图） | `docs/e2e-debt-map.md` |
| 债务刻度 | `DEBT.md` |
| SF 提案与补丁 | `docs/statement-fix-proposals.md` + `-patches/` |
| 实时进度看板（波次节） | `STATUS.md` |
| 权威计划 | `PLAN.md` |
| TameSpine 各批雷场 | `lean/Kepler/Text/TameSpine/TameList*.lean` 头注（#1-#167） |
| 车道快照 | `/Users/zhangzhuo/c17_backup/lane_snapshots/` |
| HOL 源 | `reference/flyspeck/text_formalization/`（`reference/LOCK.md`） |
