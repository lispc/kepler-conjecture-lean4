# lp-design-scout — `lpArchiveCertificatesDebt` 终端 LP 语义移植波次设计侦察（只读）

> 车道：lp-design-scout（只读，零 .lean 改动、零 lake build、零 git 操作）
> 仓库基线：`db3ae79f`（BASE_COMMIT.txt）；工作区 `/tmp/lp-design-scout/repo`（主仓未动）
> 快照：`~/c17_backup/lane_snapshots/lp-design-scout/`；日期：2026-10-23
> 口径：源码逐字对照 + HOL Flyspeck 原文对照 + 两个 `lake env lean` 只读探针
> （`#check` 类型 + 陈述等价 `example`，全用现成 olean）。
> 标记约定：**【原文】** = 源码/文档字面；**【推断】** = 据证据推断未实测。

---

## 0. 结论速览

1. **债点语义一句话**：`lpArchiveCertificatesDebt (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
   ∀ V hfan L, L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V`
   （`Assembly.lean:6224`）逐字镜像 HOL `linear_programming_results`
   （`the_kepler_conjecture.hl:21-27`）；两个前提在 HOL 终端 LP 验证机里分工完全不同——
   **`hmain` 被消费**（`contravening_lp_tau` → 每面 tau 下界），**`hlpineq` 只被携带不被消费**
   （`prove_flyspeck_lp.hl` 全文仅第 1 行 `needs` 引用）。陈述保真核对**未发现新的误植**。
2. **探针实证**：债点签名与 `LinearProgrammingResults`（`Assembly.lean:1301/1307`）双向等价
   （前提外提 ⟺ 内含，构造性，探针 PROBE4 零错误）。Lean 侧相对 HOL 多一个显式
   `FAN 0 V (ESTD V)` 前提（在案折算，`Assembly.lean:184-186`；语境下由
   `contraveningFan` 消解，非弱化风险）。
3. **证书数据现状**：Flyspeck 二进制证书 **404 MB 全部 tracked 在库**
   （`formal_lp/glpk/binary/`，easy 24 + hard 15 + hard_7.tar.gz；19,715 图 / 43,078 终端记录
   / 189 infeasible）。Lean 侧 **189 条 infeasible 证书产物模块已落库且叶全闭合**
   （`lean/Kepler/LP/T*.lean` 41,440 行，commit `7ba6b5b7` 2026-10-17，`lpAllInfeas`
   公理标准三零）；**42,889 条 bound 叶全部开放**——root 19,237 有 2026-10 账本可重发射
   （sha 5/5 复现），easy 4,362 + hard 19,290 旧账丢失**必须重跑**。
4. **三路线判定**：(a) 逐记录对偶/Farkas 证书 + `decide` checker **已是既定范式**（infeas 189
   + PilotCM + root 试点 4 条全链走通），它补数据层、不补语义层；(b) "127 族查表"独立路线
   **不成立**（每记录 LP 各不相同，且 HOL 的 127 条 `lp_ineqs` 在 LP 链里本来就不被消费），
   但它以"族线性化层（getIneqs）"的形式成为 (a) 的语义子层；(c) 重接线**最便宜且零保真风险**：
   覆盖归约（LPCoverage 形）+ `hlpineq` 按携带语义不消费 + `hmain` 消费局部化到单一 tau 桥。
   **最便宜** = (c)+(a) 的树数据波；**最稳** = (a) 全案（范式已两次端到端实证）。
5. **波次计划**：沿用 lpaudit 立的 W1–W7 主干，把 W6（覆盖桥）细化为 W6-A…W6-F 六波。
   **立即可开**：W1（root 灌装首批）、W6-A（证书树数据）、W6-B（lp_fan/lp_cond/lp_tau）、
   W6-C（split 纯算术）。**需裁决**：W6-PIN（LPAll 钉定升级，动冻结面）、GoodListNodes 真化、
   W5/W7 的算力与磁盘窗口（终装配 ≥1.5 TB）。
6. **关键结构性发现（缩小移植面）**：HOL 终端 LP 验证对 `lp_ineqs` **零消费** ⟹ Lean 侧
   `hlpineq`（现为空清单占位，空洞成立）**不阻塞**任何语义波——把 `LpIneqs` 内容化
   （127 条 `lpIneqsIds`，IdLists.lean:484 已在库）**不是**本债点的前置。真正的前置只有
   树数据、split 算术、lp_cond/lp_tau、族线性化四件。
7. **两份旧侦察的主要过时点**：formal-lp-verify-scout 的"头号风险=编译时间
   [360,7,800] 核时"已被实测推翻（root p50 49.2 s/条；全量 feasible 675–1,370 CPU-h；
   新瓶颈=磁盘 olean 860–940 GB）；其 G1/G7（infeasible 通道）已闭合；G2 钉定 schema
   已落（未接 LPAll）。lp-w6-coverage-scout 基本现行，仅"总量定理传递 sorryAx"一句
   在 infeas 半边已失效（189 侧已零 sorryAx）。
8. **推荐编排者第一波**：**W1（root 19,237 首批灌装，5,000 条/chunk 批）与 W6-A（证书树
   light 数据）并行立波**——W1 只花构建机时（账本在库、sha 可复核、范式已实证），W6-A
   是全部语义波的唯一数据前提且机械可生成；两波互不依赖、互不抢文件。

---

## 1. Q1 债点精确语义与 HOL 保真

### 1.1 陈述逐字（`lean/Kepler/Assembly.lean:6224-6230`）

```lean
theorem lpArchiveCertificatesDebt (hlpineq : LpIneqs) (hmain : lp_main_estimate) :
    ∀ (V : Set V3) (hfan : FAN 0 V (ESTD V)) (L : fgraph ℕ),
      L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V := by
  sorry
```

**【原文】** `:6226-6228` 起 docstring：资产状态 deferred-compute + 语义桥缺口；
旁挂骨架层 `Kepler.Text.LP.*`；NEEDS ①42,889 bound 叶逐条重跑产物转发 + 189
不可行通道定形；②覆盖桥 = HOL formal_lp 链的 Lean 移植。

### 1.2 两个前提各提供什么

| 前提 | Lean 定义 | HOL 原文 | 在终端 LP 验证机中的角色 |
|---|---|---|---|
| `hlpineq : LpIneqs` | `AllCertified idsLpIneqs`，`idsLpIneqs = []`（Assembly:249/254，占位空洞；清单本体 `lpIneqsIds` 127 条在 `IdLists.lean:484`，`_length = 127` :615） | `lp_ineqs`（the_main_statement.hl:29-45：`Lp`/`Tablelp`/`Lp_aux` 标签 ∪ `6170936724`，剔除 `deprecated_quads`，`setify` 后合取） | **只携带、不消费**：`prove_flyspeck_lp.hl` 全文对 `lp_ineqs` 的引用只有第 1 行 `needs`；verify_all 的对账（:121-127）只要求它是证书定理的 DISCH 假设之一。**【原文】** |
| `hmain : lp_main_estimate` | `JEJTVGB_concl`（LocalAuto16.lean:509；六分量 LocalAuto1.lean:580-643） | `lp_main_estimate = JEJTVGB_concl`（JEJTVGB.hl:232；Appendix.hl:190-196 六合取 `list_mk_conj`） | **被消费**：`contravening_lp_tau`（lp_main_estimate-compiled.hl:1682-1706）用它 + `CRTTXAT` + `tame_9a` + 面表示引理，把每面 `tauVEF` 压到 `d_tame` 表常量（`#0.206/#0.4819/#0.712`，REAL_LE_TRANS）。**【原文】** |

`hmain` 的供给链：`linearProgrammingResults`（:6270-6272）以
`hnl.2.2.2.1`（`LpIneqs` 分量）与 `nonlinear_imp_lp_main_estimate_p16 hnl.2.2.1`
（`main_nonlinear_terminal_v11 → lp_main_estimate`，LocalAuto16.lean:516-518，
HOL JEJTVGB.hl:244 同名定理镜像）喂给 `lpArchiveCertificates`。

### 1.3 调用链位置（当前 HEAD 行锚，全部实测）

```
the_kepler_conjecture_from_interfaces        Assembly.lean:6427
  └ assembly (hNL) (hLP) (hTC)               :6419   ← hLP : LinearProgrammingResults
      └ linearProgrammingResults hnl         :6269
          └ linearProgrammingResultsOf hnl   :6241   （HOL tame_result_lemma + 装配镜像，真推导）
              └ lpArchiveCertificates        :6234   := lpArchiveCertificatesDebt hlpineq hmain (:6237)
                  └ lpArchiveCertificatesDebt :6224  ⬜ 唯一直源（by sorry）
  旁挂（不进默认闭包）：LinearProgrammingResultsOn :1301 / LinearProgrammingResults :1307
  消费上游：textCapstone :6278（接口 3，自行重建 hmain :6281）
```

### 1.4 陈述保真核对（逐条对照 HOL）

| # | 检查项 | Lean 锚 | HOL 锚 | 判定 |
|---|---|---|---|---|
| F1 | 结论 `¬contravening V` 七合取 | Assembly:92-99 | tame_defs.hl:248-254 | **逐字同构**（packing/ball_annulus/scriptL>12/极大性/CARD 13-15/surrounded ESTD/ECTC∨‖v‖=2） |
| F2 | `linear_programming_results` 全式 | Assembly:1301-1307 | the_kepler_conjecture.hl:21-27（权威版；tame/linear_programming_results.hl:12-17 同文） | **逐字同构**；前提外提差异经探针 PROBE4 证双向等价（构造性，`⟨trivial,…⟩` 方向用 `hli hme` 喂入） |
| F3 | `FAN 0 V (ESTD V)` 显式前提 | Assembly:184-190（在案折算） | HOL `hypermap_of_fan` 全函数无此前提 | **已记账的弱化**；语境下 `contraveningFan`（Assembly:1548）供给，非风险 |
| F4 | `FanHypermapIsoList` = `iso (hypermap_of_fan …) (hypermap_of_list L)` 镜像 | Assembly:176-194（IsHypermapOfList 规格级 + HypermapIso） | hypermap.hl:9614 `iso`；list_hypermap-compiled.hl:60 | **规格级保真**；`hypermapOfList` 构造未落地（在案 P6-C 差距，Assembly:166-176）；同构方向（fan→list）两侧一致 |
| F5 | `lp_main_estimate` 六分量 | LocalAuto1.lean:580-643 | Appendix.hl:116-196 | **逐常量核对通过**：d_tame 表 0/0.206/0.4819/0.712/1.541（appendix.hl:108-113）、pent 0.616×2、quad_pro 0.477、quad_diag 0.467（2013-06-03 修正注记两侧一致）、sqrt8/`2*h0`/`3` 界、`tau3 ≥ 0` |
| F6 | `tameArchiveLists` | GoodListDefs.lean:82（`TriData ++ QuadData ++ PentData ++ HexData`，Graphs/ArchiveData/*.lean） | the_kepler_conjecture.hl:40 `archive = set_of_list tame_archive_lists`；good_list_archive.hl:10 | **数据实例化**（Phase 2 在库数据），非字面转录；顺序无语义影响（合取/成员量化） |
| F7 | 镜像支（`IMAGE (--) V` / `contravening_negative`） | 不在债点（属 textCapstone 消费侧） | the_main_statement.hl:222-248（kepler_conjecture_with_assumptions 内） | **位置一致**：HOL `linear_programming_results` 本体也不含镜像支 |

**结论：债点链条未发现新的陈述误植。** 两处已知占位（`idsLpIneqs = []`、
`GoodListNodes := True` Assembly:1528）均为在案标记，不是误植。

## 2. Q2 证书数据现状

### 2.1 数据面总表

| 库存 | 位置 | 体量 | tracked | 状态 |
|---|---|---|---|---|
| Flyspeck 二进制 LP 证书（tame 图归档 + 每图分支树 + 每终端 LP/对偶解，OCaml Marshal） | `reference/flyspeck/formal_lp/glpk/binary/`：easy_1..24.dat + hard_1..15.dat + hard_7.tar.gz | **404 MB** | **是**（git 在库） | 完整源数据：19,715 图（easy 19,700 + hard 15）、43,078 终端记录、478 多终端图、189 infeasible |
| Lean 产物模块（infeasible Farkas，列主序 core + rowCore/row_check 转发件） | `lean/Kepler/LP/T*.lean` **189 个文件** | 41,440 行 | **是**（`7ba6b5b7` 2026-10-17 落库） | **189/189 infeas 叶全闭合**；`lpAllInfeas00` 公理 = 标准三零 sorryAx；两巨物列主序 decide 622 s |
| Lean 产物样板（bound 形） | `lean/Kepler/LP/PilotCM204880136538/`、`CertPilot204880136538.lean`、`CertHello*`/`CertRand*` | ~1 MB 级 | 是 | 试点样板，非量产记录 |
| 42,889 bound 记录产物 | **不在库** | — | — | root 19,237：2026-10 账本在 lpaudit 快照（`results.jsonl` 21,037 行，exit=0 全覆盖，Data.lean sha 5/5 逐字节复现，总 CPU 302.7 h，p50 49.2 s/条）；easy 4,362 + hard 19,290：2026-09 账本/产物随旧机丢失，**必须重跑** |
| 骨架层 | `lean/Kepler/Text/LP/`：LPIds（44,528 行）+ LPLeaf*（174 文件，43,078 叶）+ LPAll（565 行）+ LPCert（89）+ LPSchema（440）+ LPSchemaFarkas + LPFarkas（484）+ LPFarkasCM（247） | ~5.7 万行 | 是 | infeas 叶闭合 / bound 42,889 open sorry；`lpAllInfeas` :190 真证、`lpTerminalBoundAll` :553 开放 |
| 工具链 | `pipeline/lp/`：parse_lpcert / gen_data / flatten_lp / socert / gen_farkas / build_shards + `run/`（driver/gen_one/glpsol_dual，macOS 零改动可跑，SoPlex 钉 8.1.0） | ~数 k 行 | 是 | 全链已四段实证（hello/rand → PilotCM → infeas 189 → root 试点 4 条） |
| `certificates/` 登记目录 | `certificates/README.md` | — | 空表 | 证书本体不进 git 的预留登记处（GB 级），当前无批次 |
| 覆盖组合层 | `LPCoverage.lean` 267 行 | — | **否**（lpw6 快照） | 组合归约真证未入仓（import 环待拆） |

### 2.2 口径澄清（防混淆）

- formal-lp-verify-scout 的"easy 4,403 + hard 19,438"是**记录总数**；lpaudit 的
  "easy 4,362 + hard 19,290"是**可行（bound）记录数**，差值恰为 infeasible
  （easy 41 + hard 148 = 189）。两个口径都对，用途不同。
- STATUS.md:178 的 2026-10-23 审计注记**原文**："⚠️ 2026-10-23 审计：该 2026-09 账本与
  产物不在本机，此 ✅ 是当时通道/账本口径；当前可复核证据仅 root 19,237（2026-10 账本）
  + infeas 189（在库闭合）"。

---

## 3. Q3 设计空间：三条路线

### 3.1 路线 (a) 逐记录对偶/Farkas 证书 + Lean `decide` checker（nli 范式同构）

- **Lean 侧检查器形态**：已存在且已冻结——bound 形 `checkDualCMTF`（`Kepler/LP/ColMajor.lean`
  列主序弱对偶 checker，928 行零 sorry）；infeasible 形 `farkasCheck`（`Kepler/Text/LP/
  LPFarkas.lean`，非负整数乘子 m：列和恒零 + rhs 加权和 < 0，`LPSchemaFarkas.lean` 语义
  定形节逐行对照 HOL `prove_flyspeck_lp.hl:287-348`）。每记录一产物模块
  （`T<id>.lean` 形）+ 叶 `exact` 转发。
- **证书体量**：Flyspeck 源 404 MB 在库；Lean 产物实测 infeas 均值 ~220 行/条（41,440/189），
  bound 形 root 单条 Data.lean 20-22 MB 源/olean（sha 可复现）。
- **内核检查成本粗估**：root 实测 p50 49.2 s/条（单 build 61.6-87.3 s，2026-10-23 审计）；
  全 feasible 675-1,370 CPU-h ≈ 14-28.5 天 @2 workers。infeas 已付讫（189 全闭）。
- **风险**：低——范式已两次端到端实证（infeas 189 全绿 + root 试点 4 条标准三零）。
  头号风险已从 CPU 移到**磁盘**（Data.olean 20-22 MB/条 → 全量 860-940 GB，终装配 ≥1.5 TB）。
- **覆盖面判定**：只补**数据层**（42,889 bound 叶）；不触碰终端语义（树覆盖/lp_cond/lp_tau），
  叶全闭合也**不会**清 `lpArchiveCertificatesDebt`（lpaudit 在案硬门槛 ①）。

### 3.2 路线 (b) 更粗的 LP 不等式族查表（`CertifiedIneqHolds` 形）

- **提案形态**：把 43,078 记录的终端 LP 归结为对 127 条 `lpIneqsIds` 的查表
  （`idsLpIneqs := lpIneqsIds` + 表语义），像 nli 侧 `CertifiedIneqHolds` 批量填。
- **判定：作为独立路线不成立**。三个理由：
  1. **类型面**：债点结论是每图 `¬Contravening V`，不是 `CertifiedIneqHolds id`；每记录
     终端 LP 行/界各不相同（抽样 43.5-52 行 × ~23 界，root 试点 3,882 行），127 条固定
     不等式不可能逐记录替换。
  2. **HOL 语义面**：127 条 `lp_ineqs` 在终端 LP 验证机里**不被消费**（§1.2）——查表
     真化了它也帮不到树覆盖。
  3. **先例面**：HOL 自己走的就是逐记录精确 Farkas/对偶乘法（`transform_le_ineq` 乘
     int64 乘子后 fold-add），没有全局查表层。
- **残余价值**：族**线性化层**（HOL `get_ineqs`：族名+下标 → ye/yn 线性式实例，90-150 个
  实际使用族）天然是"族级查表"，它是路线 (a) 语义侧的 **G5 子层**，不是替代品。
  `lpIneqsIds`（127 条）与它同源但角色不同：前者是"非线性不等式成立"的注册表
  （`LpIneqs` 内容化，供 `nliLpIneqs` 消费），后者是"线性实例生成器"。

### 3.3 路线 (c) 缩小"终端语义移植"面的重接线

- **c1 覆盖归约接线（零保真风险，已设计）**：`lpArchiveCertificatesDebt` 的证明体
  := 覆盖归约 + `hsem`（LPCoverage `lpArchiveCertificatesDebt_of_coverage` 形），
  冻结陈述一字不动；`:6237` 一行改接。**这是收口波的唯一接线动作。**
- **c2 `hlpineq` 按携带语义不消费（本报告新证）**：HOL 终端 LP 链对 `lp_ineqs`
  零消费 ⟹ Lean 语义波**不需要** `LpIneqs` 内容化作前置；证明体把它当未用前提携带
  即可（与 HOL DISCH 同构，非"利用空清单平凡闭合"——闭合的是债点不是 `LpIneqs` 本身，
  政策红线不触碰）。**移植面净减一层依赖。**
- **c3 `hmain` 消费局部化（本报告新证）**：`lp_main_estimate` 在语义链里只有一个消费点
  ——`contravening_lp_tau`（每面 tau 下界）。Lean 侧可把它隔离为单一桥引理
  `ContraveningLpTau : Contravening V → lp_main_estimate → LpTau V`，独立成波；
  其余语义（lp_cond/树/记录证书）不碰 `lp_main_estimate`。
- **c4（需用户裁决）**：`LPAll`/`LPCert` 冻结面从 id 不敏感谓词升级为 `LpTerminalPin`
  钉定形——语义诚实性收口，但动冻结面，须 statement-fix 流程（见 W6-PIN）。
- **成本**：c1-c3 本身不产生独立代码量（结构纪律），c1 接线 ~1 行，c2/c3 是波次划界。

### 3.4 判定

- **最便宜**：路线 (c) 的三条结构纪律 + 路线 (a) 的 W6-A 树数据波（人写 ≤300 行 +
  机器生成数据，Mac 可做）。
- **最稳**：路线 (a) 全案——checker/产物/生成器/账本四件全部经实测，风险只剩资源窗口；
  路线 (b) 独立形态应放弃，其合理内核（族查表）并入 (a) 的 W6-D。

---

## 4. Q4 波次计划（沿用 lpaudit W1–W7 主干；W6 细化为 A–G）

> 折算口径：HOL 语义机 ~8,700 行（lpw6 附录 B）；代码按 1.2-1.6× 折算 5k-10k Lean 行；
> 数据波机器生成不计人写。每波独立验收（构建绿 + axiom 探针 + 盘点基线 43,078 不变）。

```
W1..W3(root 灌装) ──┐
W4(easy 重跑) ──────┼─→ 42,889 叶材料就绪 ────────────┐
W5(hard 重跑) ──────┘                                ├─→ W6-G 收口接线 → W7 终装配
W6-A(树数据) → W6-D(族线性化) ──┐                    │
W6-B(lp_cond/lp_tau 词表) ──┬───┴→ W6-E(树递归) ──────┘
W6-C(split 算术) ──────────┘     W6-F(tau 桥) ↗
W6-PIN(钉定升级，裁决) ─→ 随 W6-G 接入
```

| 波 | 内容 | 行数区间（人写） | 成功率 | 验收 | 前置 |
|---|---|---|---|---|---|
| **W1** | root 19,237 首批灌装（~5,000 条/chunk 批）：`driver.py` 发射产物模块 + 生成器叶闭合 + 抽样探针 | 0 手写（机器生成 ~10 万行/批） | ~95% | 构建绿；抽样 20 条 axiom 标准三零；sha 对账；盘点基线不变 | lpaudit 账本快照；磁盘 ~110 GB/批；2 workers。**立即可开** |
| **W2** | root 中批（~7,500 条） | 同 W1 | ~95% | 同 W1 | W1 让出磁盘（或双 worker 分盘） |
| **W3** | root 尾批（~6,737 条）；root 段叶清零 | 同 W1 | ~95% | root 19,237 叶 0 sorry；`lpRootAll` 形分治引理（若加）全绿 | W1+W2 |
| **W4** | easy 4,362 bound 重跑（`run/` 驱动，SoPlex 钉 8.1.0；69 CPU-h） | 0 手写 | ~85% | results.jsonl exit=0 全覆盖 + 灌装批同 W1 | pipeline 车道；**本机可开**（glpk/soplex brew 已验证路径） |
| **W5** | hard 19,290 bound 重跑（304 CPU-h + glpsol 尾部 0-689 CPU-h） | 0 手写 | ~75%（尾部不可行/放弃类需 `glpsol_dual.py` 重新命中） | 同 W4 | **算力+磁盘窗口，用户裁决**（本机长跑 vs G4） |
| **W6-A** | 证书树 light 数据：19,715 图 `LpCaseTree`（split 型/face/旗标）+ `LpGraphCert` + `CertOf` archive 对齐表；生成器 ~200 行 | 150-300 + 数据模块 2,000-4,000（机器生成） | ~85% | 逐图 `hypermapString` ↔ `tameArchiveLists` 对齐定理（对齐失败=停批事件）；抽样 478 多终端树 countTerminals 对账；`hdata`/`hcov` decide | **无**。**立即可开**（parse_lpcert.py 在库；族名普查一夜扫描顺带产出 W6-D 输入） |
| **W6-B** | `LpFan`/`LpCond`/`LpTau` 定义 + `contraveningHasLpFan`（HOL lp_ineqs_proofs-compiled.hl:385-392 直译） | 100-250 | ~80% | 定义 + `contraveningHasLpFan` 真证（消费 Contravening 分量 6/7 + 2.52 距离折算）；纯定义零 sorry | GoodListNodes 真化（**用户裁决**，Assembly:1528 占位）；**裁决后立即可开** |
| **W6-C** | `ynList`/`yeList` + split218/236/225（le_total）+ split4/5/6（5/11/7 析取，linarith） | 150-300 | ~85% | 析取定理全 linarith 闭合；公理标准三 | **无**（词表依赖可用抽象接口先行）。**立即可开** |
| **W6-D** | 族线性化 `getIneqs`：90-150 实际使用族 → ye/yn 线性式实例定理 | 1,200-3,000 | ~70% | 每族一条实例定理；hard_2（17 终端）全实例化对账；族清单与证书引用集逐字节闭合 | W6-A 族普查 + W6-B 词表 |
| **W6-E** | `VerifyLpCase` 树递归（10 split 型组合子 + 边界附加不等式 + lnsum 链） | 400-800 | ~70% | 对 1 张样例图（hard_2）走通"记录证书 + 树覆盖 → 每图 `¬Contravening`"（玩具见证可） | W6-C + W6-D |
| **W6-F** | `ContraveningLpTau` 桥（消费 `lp_main_estimate` 的唯一语义件；CRTTXAT + JEJTVGB + 面表示） | 150-350 | ~70% | `Contravening V → lp_main_estimate → LpTau V` 真证；与 TameLp tau 群零重复（冲突时私件化再换正） | W6-B；TameLp 共享件时窗对齐 |
| **W6-PIN** | `LPAll`/`LPCert` 冻结面钉定升级（`LpTerminalPin` 接入，id 不敏感缺口收敛） | 100-300 + 生成器补丁 | ~90% | 错 id 发射=编译错演示；`lpAllInfeas`/`lpTerminalBoundAll` 陈述升级后全链重绿 | **用户裁决**（statement-fix 流程）；随数据波并行 |
| **W6-G** | 收口装配：per-graph `hsem` 组装 + `lpArchiveCertificatesDebt` 证明体改接（c1）+ `LPCoverage` 入仓拆环 | 300-800 | ~75% | `#print axioms lpArchiveCertificates` 不再含该债点 sorryAx（余 `main_nonlinear_terminal_v11` 上游链除外，按当时账实况）；冻结陈述零改动 | W1-W5 叶材料 + W6-A..F；LPCoverage import 环拆解 |
| **W7** | 终装配/磁盘迁移（olean ≥1.5 TB） | 0 | — | 全仓 build + 主定理锥审计 | **机器裁决** |

**开工性标注**：立即可开 = W1（默认首推）、W4、W6-A、W6-C；裁决后可开 = W6-B
（GoodListNodes）、W6-PIN；资源窗口 = W5、W7；长链前置 = W6-D/E/F/G。
**需要用户裁决的三件**：① GoodListNodes 真化（占位定义变更）；② W6-PIN 冻结面升级；
③ W5/W7 算力与磁盘窗口。**本计划零陈述变更**（债点/接口面一字不动）。

---

## 5. Q5 过时文档清单

### 5.1 `docs/scouts/formal-lp-verify-scout.md`（2026-10-12）vs 现状

| # | 旧文断言 | 现状 | 证据 |
|---|---|---|---|
| 1 | "缺口 (a) 189 infeasible 通道——`LpTerminalInfeasibleCertified := True` 是在案占位（LPCert.lean:73），需 Farkas 形 checker（150-400 行）" | **已闭合**：DEF-FIX（2026-10-12）落真语义 `∃ c : LpFarkasCore, farkasCheck c = true`；`7ba6b5b7`（2026-10-17）189 产物模块落库、189 叶全闭、`lpAllInfeas00` 标准三零 | LPCert.lean:77 现文（旧 :73 占位已被替换）；`T*.lean` 189 文件；STATUS.md:483-484 |
| 2 | "编译时间是头号风险：43,078 × [30 s, 650 s] ≈ [360, 7,800] 核时" | **已被实测取代**：root p50 49.2 s/条、单 build 61.6-87.3 s（2026-10-23 审计）；全 feasible 675-1,370 CPU-h；新头号风险 = 磁盘（Data.olean 20-22 MB/条，860-940 GB；终装配 ≥1.5 TB） | e2e-debt-map.md:770-796（LP 灌装审计节） |
| 3 | "G2 记录级钉定……schema 冻结必须在数据波前（Mac 现在就能做）" | **schema 已落**（LPSchema `LpTerminalPin`/`LpInfeasPin`，C1a `0e788792`）；但 `LPAll` 仍用冻结 id 不敏感谓词，钉定未接入——"部分完成" | LPSchema.lean:333-358/421；LPAll.lean:190/553 |
| 4 | "第一批 A12-C1 = infeasible checker + 钉定 schema + 树 schema + 3 条端到端试点" | **全部完成或被吸收**：C1a/C1b 落库；C1c 试点 + root 审计 4 条试点（2026-10-23）做完（61.6-87.3 s/条，sha 5/5） | e2e-debt-map.md:204-207/770+ |
| 5 | "42,889 叶闭合数据波……预估 3,000-8,000 核时" | 区间收窄为实测口径：root 302.7 CPU-h（19,237 条）+ easy ~69 + hard 304-993 → 675-1,370 CPU-h | 同上 |
| 6 | "43,078 LP 内核验证 100% 完结（2026-09-24）"语境 | 旧账/产物**不在本机**（2026-10-23 审计口径修正）；可复核 = root 19,237 + infeas 189 | STATUS.md:178 原文注记 |
| 7 | "数据波灌装顺序 root → easy → hard（先小后大）" | 与 lpaudit 建议一致，无冲突；补充 root 账本已重跑（2026-10）故 W1-W3 只需重发射 | STATUS.md:179 |

### 5.2 `docs/scouts/lp-w6-coverage-scout.md`（2026-10-23）vs 现状

| # | 旧文断言 | 现状 | 说明 |
|---|---|---|---|
| 1 | "`lpTreeTerminalCertified_of_coverage`……含 sorryAx（叶未闭合的 deferred-compute 传递）" | **infeas 半边已失效**：`lpAllInfeas` 侧 189 叶全闭零 sorryAx，sorryAx 仅自 42,889 bound 叶流入 | `7ba6b5b7` 早于该侦察落库版说明，侦察正文未更新此句 |
| 2 | "第一波建议 W6-A/B/C……不要从 prove_flyspeck_lp_step1 起手" | **仍然成立**，本报告沿用并细化（W6-D/E/F/G）；补充：W6-A 应顺带产出族名普查（W6-D 输入） | 无冲突 |
| 3 | "`LpIneqs` 现在是空清单占位，不可消费"（S10） | **细化**：终端 LP 语义波本来就不该消费它（HOL 侧零消费，§1.2）；"不可消费"只对把它当数据库用的读法成立 | 本报告 c2 |
| 4 | 行锚 `Assembly.lean:6224`/`:6271` | 当前 HEAD 实测 :6224/:6271 | 一致，无更新 |

### 5.3 两份侦察共同遗漏（本报告补）

- 均未记录 `run/` 车道（root 批量灌装驱动）已 macOS 化（README 环境变量化 + brew 依赖表）——
  W4 的"本机可开"判定依据。
- 均未给出 `lp_main_estimate` 六分量的逐常量保真核对（本报告 F5）。
- 均未指出 `lp_ineqs` 在 LP 链中零消费这一可砍依赖（本报告 c2）。

---

## 6. 方法与复现

```sh
# 债点与链条锚（工作区 /tmp/lp-design-scout/repo）
grep -n 'lpArchiveCertificatesDebt' lean/Kepler/Assembly.lean        # :6224
sed -n '6419,6431p' lean/Kepler/Assembly.lean                        # assembly + from_interfaces
# HOL 原文
sed -n '22,28p' reference/flyspeck/text_formalization/general/the_kepler_conjecture.hl
sed -n '248,254p' reference/flyspeck/text_formalization/tame/tame_defs.hl        # contravening
sed -n '116,196p' reference/flyspeck/text_formalization/local/Appendix.hl        # JEJTVGB 六分量
grep -n 'lp_ineqs' reference/flyspeck/formal_lp/hypermap/main/prove_flyspeck_lp.hl  # 仅 :1 needs
# 探针（现成 olean，秒级；PROBE4 零错误）
cd lean && lake env lean /tmp/lp_probe4.lean
# 数据面
ls lean/Kepler/LP/T*.lean | wc -l            # 189
grep -h '^theorem lpT' lean/Kepler/Text/LP/LPLeaf*.lean | wc -l   # 43,078
grep -c sorry lean/Kepler/Text/LP/LPLeafInfeas00.lean             # 1（头注字面，非叶）
du -sh reference/flyspeck/formal_lp/glpk/binary/                  # 404M
```

**未做 / 未声称**：未改任何 .lean；未 `lake build`；未跑 git 写操作；未验证
easy/hard 23,652 条的可解性（无账本，仅引 lpaudit 口径）；未实测 `LPCoverage.lean`
入仓后的 import 环拆解成本；19,715 图的 archive 对齐未跑（W6-A 的工作内容）。
探针文件在 `/tmp/lp_probe1..4.lean`（会话临时件，不入库）。
