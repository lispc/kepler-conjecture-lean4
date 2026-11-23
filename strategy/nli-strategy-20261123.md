# NLI 战略复盘与 1–2 周车道规划（2026-11-23）

> **性质**：战略讨论稿 + 车道规划，不是账本。实时状态数字唯一出处仍是
> `docs/priority-queue.md` 文件头/§1/§8 与 `docs/e2e-reachability-map.tsv`。
> 本文数字为 **2026-11-23 写作时点快照**，带来源标签；`MEA` = 本仓实测，
> `DOC` = 账本/文档，`EST` = 估算。写作时 HEAD `f8302b52`。
>
> 输入：`nli-strategy-review-w1` 只读复盘（`REPORT.md` 677 行 + `evidence/`，
> 快照 `~/c17_backup/lane_snapshots/nli-strategy-review-w1/`）；编排者已独立核对
> 48+1 计数、5 条锥外 `*Ids`、分档 1/15/27/1/2/3。相关正本：
> [`docs/nli-campaign.md`](../docs/nli-campaign.md)（路线图/负结果）、
> [`docs/priority-queue.md`](../docs/priority-queue.md)（实时账本）、
> [`docs/tools.md`](../docs/tools.md) §7（olean 恢复交接）。

---

## 0. TL;DR

- 当前仓面 **49 = 48 条锥内 `nli*` + 1 hLP**；`Assembly.lean` 另有 **5 条锥外
  `*Ids`**（3 条 `True` 回落假绿 + 2 条真债），不计入 49。
- 逐件分档 **1（T1 近闭）/ 15（T2 结构化）/ 27（T3 农场）/ 1（T3-mixed）/
  2（T4 阻塞）/ 3（T5 LP，含 hLP）**。**33/49 在 1–2 周内不可能靠数学队列清零**；
  现实数学可动面是 T1+T2 共 16 条。
- 推荐主线：**根面恢复 → wt1（−1）→ ZTG joint-6 trio（潜在 −3）→
  ZTG 余债/解耦 4 → qitnpea 共享 floor**；fat1、ox3q1h 先只做零 Lean 预认证；
  27 条农场与 LP 保持 hold。备选 = c2 outer58 → outer 扫的 HOL 忠实二阶移植。
- **新增的硬约束（2026-11-23 09:xx 实测）**：主池混用两个 `Inhabited Graph`
  实例世界——300 个 Phase-D canonical shard vs 360 个旧 non-canonical olean。
  `CertPent`/`CertHex`/`TopReplayHex` 已用 source-identical 预编译 olean 恢复并审计，
  但**未来车道不得重编跨世界消费者，也不得覆盖主池 `CertCheck.olean`**。
  永久修复 A（重建 280 旧 shard，天数）/C（保留混合池 + 不变量）待裁决。
- **近期现实目标：49 → 45**（wt1 −1 + trio −3，均 EST）；trio 部分过则 46/47。
  不把农场/LP 的 CPU·h 计入承诺。

---

## 1. 事实基线（写作时点快照）

| 指标 | 值 | 来源/状态 |
|---|---|---|
| 仓面 SORRIED | **49 = 48 `nli*` + 1 hLP，Text 0** | pq 文件头；`1ec06b28` 后源码层计数（DOC） |
| 根面 `#print axioms` | 最后完整实测 **589 = 585 + 标准三 + `sorryAx`**（基线 AQ `e4c384e6`）；当前池未齐，harness RC=2 | pq 文件头/续1415（DOC） |
| 恢复闭包 | closure **8,868** / present **8,164** / missing **704**（2026-11-23 09:28 重扫） | `olean-recovery-2w-w1/STATUS.md`（MEA） |
| 恢复首轮 | 324 件 rc=0；6 件 deferred（5 件并发 `lake build` 临时缺 `PackingAuto13`；1 件 `CertPent` 混世界） | 同快照 `failures.tsv`/`SHARD_WORLD_BLOCKER.md`（MEA） |
| 池世界 | canonical `instInhabitedGraph` **300** vs non-canonical `instInhabitedGraph_lean` **360**；`both=0` | `SHARD_WORLD_BLOCKER.md` §2（MEA，8,239 olean 字节扫描） |
| 三件恢复 | `CertPent`/`CertHex`/`TopReplayHex` 从 `goodlist-w4` 恢复；`CertPent`=198 pent 公理+标准三、`CertHex`=290 hex 公理+标准三、`TopReplayHex` 无额外公理；全部在 `trust-base.tsv` | 同文 §3/§5（MEA） |
| wt1 首盒 | `p0` 577 叶外候选（`续1410`） | pq §8（DOC） |
| wt1 第二盒 | `p1_i0j0k0` m4=0，2,192 叶外候选，pp=3×2095/4×97，pending=0（`续1421`） | pq §8（DOC） |
| wt1 三边 | E00/E01/E11 均 EXTERNAL_CANDIDATE_READY；E00 下界 4.514331609e−5 > 4.5e−5，E01 0.003877895，E11 0.014596426（`续1420`） | pq §8（DOC） |
| wt1 二阶底座 | `taylor-second-bounded-lean-w1` 交付并正在落库（10 个 `TaylorSecond` 模块 build + import audit） | 车道快照/进程（MEA） |
| 信任基座 | **585 = 580 shard-range + 5 tri-single-seed**，未动 | `docs/trust-base.md`（DOC） |
| precompile | 580/580 PASS、7.184 h、192 件基线 **13.889×** | pq 续1409（DOC） |

**口径提醒**：49 是源码层计数；根面自 `e4c384e6` 后未完整复跑。任何“−1 已完成”在
根面复跑前都只是 source-level 结论。单债 −1 不改变根面 589（其余 `sorry` 仍在），
变化体现在 SORRIED 清单 −1 与本件消费链恰标准三（`nli-campaign.md` ERRATA）。

---

## 2. 分档与攻击序列

### 2.1 分档（逐件清单见复盘 `evidence/nli_inventory.tsv`，49 行）

| 档 | 条数 | 内容 | 当前可动性 |
|---|---:|---|---|
| T1 近闭 | **1** | `nliCell3QZECFICwt1` | 只剩 `hP1`（`w1F2≤0` 全盒）+ E00/E01/E11；三边已外证，前两盒 hP1 已外证，余 14 盒待扫 |
| T2 结构化/共享 kit | **15** | wt0 1、FHB a/v2a 2、ZTG joint-6 6、ZTG 解耦 4 4、ox3q1h 1、fat1 1 | 有落库 kit，各差关键符号证书或共享面 |
| T3 农场/hold | **27** | tsk sym 3 + F1 6 + F2a 10 + F2b GLF 5 + FHBb 1 + F2c 2 | 等用户解冻 ①②；无数学 blocker |
| T3-mixed | **1** | `nliMainNonlinearTerminalV11`（109 合取） | 3 MATH + 21 接线 + 85 农场；缺一支不减 SORRIED |
| T4 阻塞/需新数学 | **2** | `nliTskIYOUOBFsharpv2`、`nliRestIXPOTPA` | iyou L23 BLOCKED-forensics；IXPOTPA 单调归约被精确反例否决 |
| T5 LP | **3** | `nliLpIneqs`、`nliKcblrqcIneqDef`、hLP | 等解冻 ④⑤ |

**读法**：1–2 周数学队列真正能碰的是 T1+T2 共 16 条；T3/T3-mixed/T4/T5 合计 **33 条**
不能靠本轮数学清零。合取债（ox3q1h 230、TerminalV11 109、LpIneqs 127、Kcblrqc 28）
只报“已闭分量/总分量”，不报“接近 −1”。

### 2.2 攻击序列（Wave）

- **Wave 0（先于一切 −1）**：完成 olean 恢复 + 根面 `#print axioms`。
  当前 704 缺件、恢复 2-worker 在跑；池世界不变量同时生效。
- **Wave 1（wt1，−1）**：先补 **剩余 14 盒**的 P1 联合 Taylor 外候选（零 Lean），
  再用已落库的二阶底座 + 三边证书做 Lean 装配。**只有 16/16 盒 + 三边全闭才能 −1**；
  前两盒 + 三边只够做 Lean 骨架与验收面，不能预支。
- **Wave 2（ZTG，潜在 −3 到 −6）**：joint-6 **trio** 共享表（8 片全凹/36 角/36 值）
  先下；随后 W2/W3/W4。ZTG 解耦 4 先用精确 Bernstein 原子包络做零 Lean hstep 预认证，
  成功后再 Lean；不上 certtm/TM 农场。
- **Wave 3（共享面/目标件）**：qitnpea 共享 `γ4≥23/2000` 面（潜在服务 1_0/1_2/2_0，
  1_1 是 w=3 不服务）；FHB a/v2a 在共享 kit 上并行；fat1、ox3q1h 只做预认证。
- **Wave 4（合取债去风险）**：TerminalV11 的 3 MATH + 补粘 + 21 支进锥；Kcblrqc 的
  1 条无 LP 依赖项。**不产生 SORRIED −1**，只去未知。
- **Wave 5（农场批量）**：27 条，等解冻 ①②；先按 `537ed78d` 重发 case（RQ y1 假域 bug）。
- **Wave 6（LP）**：2 nli + hLP，等解冻 ④⑤；只做表示审计，不做数学侦察。

### 2.3 合并 vs 单点

| 合并 | 理由 | 单点 | 理由 |
|---|---|---|---|
| ZTG joint-6 六债 | 同一 template、同一 96/216 角点、trio 一张表 | IXPOTPA | 宽盒 + 非单调 γ23；无共享结构 |
| ZTG 解耦 4 | 同一 Dih kit、32 角、9 片 hstep | IYOUOBFsharpv2 | L23 forensics；发射器/谓词问题 |
| QITNPEA 共享 floor（3 债） | 同一 `γ4≥23/2000` 面 | fat1 | 三条路线均未闭；等二阶底座/终端 checker |
| FHB a/v2a | 同骨架/η 曲线/地板归约 | RQWUDDU | 宽盒 + case 域 bug；只剩农场 |
| wt1/wt2A/sqrt8 | 共享 cell3 盒/槽结构；wt1 走二阶塔 | ox3q1h chain_idx2 | 230 合取；单件阻塞整族 |
| 二阶底座 | wt1 hP1、c2 outer58、fat1 终端共用 | LP/hLP | 等解冻 + 磁盘；独立层 |

---

## 3. 四条路线的战略权重（基于实测）

### (a) 结构化数学 + 共享分析 kit + 区间/BB 数值内核 —— **高（主线）**

- 已闭 5 件中 3 件走此类：sqrt8 26-cell、wt2A 62-cell、XLLIPLS Rule P 农场。
- wt1 A′ 二阶塔把一阶 2,902 叶压到约 50–60 件证书（`cell3-wt1-tower-scout-w1` GO）；
  第二盒 2,192 叶外候选再次验证模板可移植。
- 资产存量约 17.8 万行（NliBanks + Wt1/FHB/Ox3q1h/ZTG），复用率最高。
- 局限：宽盒 0.4–0.65 不适用（10⁵ 叶）；S2a/ox3q1h 卡在 f'' 的 sound 包络。
- **推翻条件**：wt1 hP1 在有限剖分/Bernstein 后仍 >0；ZTG 片证书三级 fallback 后仍不 sound；
  qitnpea 完整覆盖出现负点。

### (b) certtm/TM 证书 —— **中低（窄盒/点证书工具）**

- 正面：XLLIPLS 6,612 叶；Rule P 单叶 27–31 s，族 B 1,400 叶 15.78 CPU·h。
- 负面：Gate-0 certtm2 宽盒叶数外推 s*≈35–80 ≫30；fat1 三终端 unchanged checker 0/3。
- 结论：两次 pilot 没有封死“certtm 永远不可行”，但封死了“用它一次性解决宽盒 48 条”。
  只在窄盒/点锚定（Rule P）或专门二阶 TM 规则下有位置；后者需新规则 + 用户解冻。

### (c) fat1/outer58 的 HOL 终端证书 —— **中（真值源 + 备选捷径）**

- 运行时阻塞已解除（`brew install ocaml camlp5`；#2028 树 REPLAY PASS）。
- 当前真阻塞是 **checker 兼容性**：三终端 dual 一致、落在 HOL enclosure 内，但
  unchanged Rule P/BaseC/朴素 IA 0/3；需要二阶 checker 或 TaylorM 升级。
- c2 outer58：HOL 84 叶/83 glue 全闭，但 Lean 前置合同 PASS_LEAN_NOT_READY
  （90 行 = REUSE 4 / ADAPTER 45 / MISSING 41）。
- 结论：提供 HOL 真值/真实叶结构；不是 47 条债的通用施工路线，权重低于 (a)。

### (d) precompile 13.889× 迁移到 NLI —— **对数学为零，对基座重建高**

- 机制：`precompileModules` + `--load-dynlib` 把 `native_decide` 的 IR 解释换成本机执行。
- NLI 叶检查走 kernel `decide`/`linarith`/`norm_num`，不是 `native_decide`；bb_arb/TM
  搜索在 Python，不受益；Rule P 27–31 s/叶是 kernel 检查成本。
- 可迁移：585 shard 的重建/复验（~98 h → ~7–8 h EST）；**不解决当前 704 非 shard 缺件**。
- 不能把它当作 NLI 证书农场的加速器；本仓也禁止新增 `native_decide`。

---

## 4. 推荐主线与备选

### 主线：结构化数学 + 二阶共享底座

1. **Wave 0**：恢复 + 根面验收（704 → 0；harness RC=0）。
2. **Wave 1**：wt1 余 14 盒零 Lean 外候选 → Lean 装配 → **−1**。
3. **Wave 2**：ZTG joint-6 trio → **−3**；余 3 债按 W2/W3/W4 推进。
4. **Wave 3**：qitnpea 共享 floor / FHB a/v2a 并行；fat1/ox3q1h 只预认证。
5. 农场/LP 保持 hold，不纳入 1–2 周承诺。

**成立前提**：二阶底座在 wt1 代表叶 RC=0/标准三；P1 原子表在 16 盒上 sound；
每个代表件有第二实现/独立重放；常数方向逐件审计；≤3 lean / ≤24 GB / pressure<2。

**推翻条件**：hP1 在有限剖分/Bernstein 后仍 >0；二阶底座与 HOL/Lean 语义不一致；
ZTG 片证书三级 fallback 后仍不 sound；qitnpea 完整覆盖出现负点。
若通用二阶底座失败：主线与备选同时失效，独立退路 = ZTG 角点表 + 农场 hold 决策；
不要把“底座失败”误判为 NLI 全盘失败。

### 备选：HOL 忠实二阶移植（c2 outer58 → outer 扫）

- 启动条件：主线在 hP1 或 ZTG 片证书上连续 3 轮结构卡死，且通用二阶底座已落地。
- 内容：把 outer58 的 84 叶/83 glue 从 PASS_LEAN_NOT_READY 推到 READY；补 45 ADAPTER
  + 41 MISSING；随后同模板扫其余 outer；fat1 三终端用同一二阶 checker 复测。
- 推翻条件：MISSING 41 项无法在合理预算补齐；二阶 checker 对 fat1 三终端仍 0/3 且无新增证力。

---

## 5. 未来 1–2 周车道规划（5 个方向）

> 当前 Lean 槽：olean 恢复 2 worker + `taylor-second-bounded` 落库 1 = 3（满）。
> 零 Lean 车道不占槽；Lean 车道按回执释放槽位。

### 方向 1：`pool-world-consistency-w1`（零 Lean，决策/审计）

| 项 | 内容 |
|---|---|
| 目标 | 把混世界债务从“已绕过”变成“可裁决”：逐 olean 的世界清单 + 依赖边 + 未来 lane 风险面；给出 A/C 成本表与推荐 |
| 输入 | `SHARD_WORLD_BLOCKER.md`、主池 8,239 olean、`goodlist-w4` 三件、`docs/trust-base.tsv` |
| 边界 | 不重建 shard、不改池、不覆盖 `CertCheck.olean`；只读 + 清单 |
| 验收 | `world_manifest.tsv`（module → world → mtime → sha?）；A 的成本（280 件旧 shard，按旧日志 outlier 估）与 C 的不变量条款；风险 lane 清单 |
| 资源 | 零 Lean；字节扫描 + 依赖图 |
| 工期 | 1–2 车道日（EST） |
| 止损 | 世界边界无法从 olean 字节可靠判定 ⇒ 标 UNRESOLVED，给出可复现探针 |
| 依赖 | 无；与恢复并行（只读） |
| hold | 不触碰 |

### 方向 2：`cell3-wt1-box-sweep-w1`（零 Lean，wt1 关键路径）

| 项 | 内容 |
|---|---|
| 目标 | 把已验证的 P1 联合 Taylor 模板（m4=1 与 m4=0 两支）扫到剩余 14 盒；每盒 candidate/replay + 第二实现 + pending=0 + 严格负叶 |
| 输入 | 首盒 577 叶、第二盒 2,192 叶、三边证书（`续1410/1420/1421`）、`cell3-wt1-ddmatan-refine-w1` 紧包络、`Wt1TowerDomain/Tower` |
| 边界 | 不重做前两盒；不做 Lean/patch；不改陈述；不把采样当证书；不预支 −1 |
| 验收 | 每盒 `DELIVERY` + 独立重放；14/14 盒覆盖表；未过盒逐盒 UNRESOLVED（当前表示） |
| 资源 | 零 Lean；Python/区间，建议 `nice -n 19`，单 worker 先校准 |
| 工期 | 1.5–3 车道日（EST；第二盒约 1h45m 含独立重跑，14 盒外推） |
| 止损 | 单盒成本 >2× 第二盒且无结构解释 ⇒ 暂停并交覆盖表；不设数学判否 |
| 依赖 | 与恢复/落库并行（CPU 竞争时让路）；wt1-close 消费其输出 |
| hold | 不触碰 |

### 方向 3：`wt1-close-w1`（Lean，−1）

| 项 | 内容 |
|---|---|
| 目标 | 在二阶底座 + 三边 + 16 盒外候选齐后，装配 `Kepler.Targets.Wt1`，闭合 `nliCell3QZECFICwt1` |
| 输入 | `TaylorSecond` 底座（落库中）、`Wt1MatanDDAnti` `884bd80d`、`Wt1Tower*`、三边证书、盒扫描输出 |
| 边界 | 不重做 wt2A/sqrt8；不改陈述；不新增 sorry/axiom；16/16 未齐不组装最终 −1；不碰 certtm/Mono*/D |
| 验收 | 单文件 RC=0/error=0；`#print axioms Kepler.Assembly.nliCell3QZECFICwt1` 恰标准三；根面复跑（池可用时）仍 589 同集；SORRIED 49→48 |
| 资源 | 单 lean；峰值预计 6–10 GB |
| 工期 | 骨架 1–2 车道日 + 全盒装配 2–4 车道日（EST，取决于盒扫描） |
| 止损 | hP1 sound 包络在有限剖分/Bernstein 后仍 >0；单文件 >15 min / RSS >24 GB；3 轮结构卡死 ⇒ 交缺口 |
| 依赖 | 等 `taylor-second` 落库回执、盒扫描 14 盒、根面恢复（验收） |
| hold | 不触碰 |

### 方向 4：`ztg-joint6-trio-w1`（Lean，潜在 −3）

| 项 | 内容 |
|---|---|
| 目标 | 先闭 W1 trio（`0_0_0_1`/`0_0_1_0`/`1_0_0_0`）共享表（8 片全凹/36 角/36 值），再按 W2 `1_0_0_1` → W3 `0_0_0_0` → W4 `0_1_0_0` 推进 |
| 输入 | `ZTGJointKit`、W1 K/P/HM、L1 支撑、二阶符号辅助、96/216 角点资产、Bernstein peel |
| 边界 | 不用 certtm/TM；不重试整盒 Q 凹性；不把采样凹性当 Lean 证据；不扩解耦 4；不改陈述 |
| 验收 | 每条 `#print axioms Kepler.Assembly.nliRestZTGIJCF4_<bits>` 标准三；SORRIED 49→46（trio 全闭）；根面仍 589 |
| 资源 | 单 lean；每模块 2–6 min、≤10 GB（SCOUT 估计）；trio 共享表 5k–15k 行（EST） |
| 工期 | trio 3–5 车道日（EST）；全 6 债 6–10 车道日（EST） |
| 止损 | 片证书三级 fallback 后仍不 sound；行数 >48k；单模块 >6 min/10 GB ⇒ 停该债留 WIP |
| 依赖 | 等 Lean 槽（恢复完成或降到 1 worker）；与 wt1 并行需 3 槽预算 |
| hold | 不触碰 |

### 方向 5：`qitnpea-shared-floor-w2`（零 Lean → Lean，潜在 −3 消费者）

| 项 | 内容 |
|---|---|
| 目标 | 证 `γ4≥23/2000` 在 QITNPEA 共同盒上的全盒精确下界；完整覆盖 + pending=0 + 第二实现；服务 1_0/1_2/2_0（1_1 是 w=3 不服务） |
| 输入 | `qitnpea1-shared-floor-w1` 快照、13 份 JSON、新 kink `(2.52,2,2.52,2,2,2)`、`PackingAuto21:681-700` |
| 边界 | 不覆盖 1_1；不把局部区间当全盒；不预支 −3；不做新 universal Bernstein 后端；不碰 certtm |
| 验收 | 零 Lean：完整覆盖 + pending=0 + 第二实现；Lean：共享 floor 引理 + 消费者 `#print axioms` 标准三 |
| 资源 | 零 Lean 无 lean；Lean 单 lean；精确有理系数中等 |
| 工期 | 零 Lean 2–3 车道日 + Lean 3–4 车道日（EST） |
| 止损 | 完整覆盖出现负点；margin < 舍入；无精确全盒包络 ⇒ UNRESOLVED（当前表示） |
| 依赖 | 零 Lean 可立即并行；Lean 等槽；与方向 2 共享 Bernstein/区间工具 |
| hold | 不触碰 |

**保留方向（本轮不派）**：`ztg-decouple4-hstep-w1`（Bernstein 原子包络，2–3+3–5 车道日、
高不确定）、`terminal11-math-wire-w1`（不承诺 −1）、`nli-root-accept-w1`（恢复完成后 0.5–1 日）。

---

## 6. 风险与纪律

### 风险 1：根面验收是 binding constraint

- 49 是源码层；根面自 `e4c384e6` 后未完整复跑；当前缺 704，harness RC=2。
- 缓解：Wave 0 先行；所有 lane 同时要求“小模块 `#print axioms` + 池可用时根面复跑”；
  不把 source-level 49 写成根面已复验。

### 风险 2：49 不是同质队列

- 33 条农场/混合/阻塞/LP；4 条合取债部分证明不减 SORRIED。
- 缓解：报告按“可动层/门控层”分栏；合取债只报分量覆盖。

### 风险 3：二阶底座与共享 kit 的耦合 = 单点故障 + 语义漂移

- 同一底座服务 wt1 hP1、c2 outer58 Lean、fat1 终端 checker。
- 已发生漂移：RQ case y1 下界 bug、nb20 K2 常数方向、wt2A y5 单调反例、
  lmfun factor-2、HOL/Lean 一阶 vs 二阶 Taylor 口径差。
- 缓解：每件第二实现/独立重放 + 文件尾 axioms 审计；常数括号标注方向；
  HOL 映射保持 REUSE/ADAPTER/MISSING 三级。

### 风险 4（新增）：主池混世界

- 300 canonical vs 360 non-canonical；跨世界消费者无法从源码重编；
  三件已用预编译 olean 绕过并审计。
- 缓解（默认 C）：保留混合池 + 不变量——不覆盖 `CertCheck.olean`、不重编
  `CertPent`/`CertHex`/`TopReplayHex`、新 lane 先做世界探针；若未来必须重编跨世界消费者，
  再启动 A（重建 280 旧 shard，天数，重审 280 条 trust-base 公理）。
- 这是工程/表示问题，不是数学判否；不影响已审计的 585。

---

## 7. 不做什么

- 不用 certtm/TM 一次性解决宽盒农场；不重启 S2b-a 当前 976 点量产。
- 不以 precompile 加速 NLI 数学；不新增 `native_decide`。
- 不把农场/LP 的 CPU·h 计入 1–2 周承诺；不把“部分分支已闭”写成“接近 −1”。
- 不在混世界池上重编跨世界消费者；不覆盖 `CertCheck.olean`。
- 不把采样凹性/数值一致当作 Lean 证据；不用自设预算判数学 NO-GO。

---

## 8. 复查触发条件

- 恢复 missing=0 或 harness RC=0/≠0：重跑根面并更新 §1。
- wt1 14 盒扫描完成或单盒成本超 2×：更新 Wave 1 工期与 ETA。
- ZTG trio 首债闭合或三级 fallback 失败：更新 Wave 2 判词。
- 混世界 A/C 决定：若选 A，单独立项并重审 280 条 trust-base 公理。
- 用户解冻农场 ①② 或 LP ④⑤：重排 Wave 5/6，不自动改变数学主线。

---

## 9. 证据与修订

- 复盘正本：`~/c17_backup/lane_snapshots/nli-strategy-review-w1/REPORT.md`（677 行）+
  `evidence/nli_inventory.tsv`（49 行）、`git-log-since-1110-full.txt`（1,143 commits）。
- 恢复/混世界：`~/c17_backup/lane_snapshots/olean-recovery-2w-w1/SHARD_WORLD_BLOCKER.md` +
  `STATUS.md` + `failures.tsv`。
- wt1 新资产：`续1420`（三边）、`续1421`（第二盒）、`884bd80d`（matanDD）。
- 2026-11-23 初稿（HEAD `f8302b52`）；后续修订在本节追加，不改上文历史结论。
