# priority-queue.md — 当前待办优先级队列（长期维护）

> **维护者**：编排者。每次车道并网、侦察交付或用户裁决后即刻更新；每周对表一次。
> 状态枚举：`在飞` / `就绪` / `排队` / `等用户裁决` / `暂缓（超时/资源暂停，可重启）` / `搁置` / `完成（日期 · commit）`。
>
> **状态口径（2026-11-18 用户指正）**：`UNRESOLVED` 只表示目标尚未闭合，不是判死；
> **timeout 一律先记 `暂缓`，不是 NO-GO**。不自动 resume 只是防重复执行、无头运行和资源冲突，
> 不剥夺以后从 WIP 重启的资格。只有明确反例、可信结构否证或信任约束冲突，才能对
> **某一条具体路线**写 NO-GO；这不等于对应定理为假或其它路线不可行。
>
> **北极限**：`#print axioms Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22`）
> = `[propext, Classical.choice, Quot.sound]` ∪ 585 条地面 `native_decide` 公理；**零 `sorryAx`**。
> 终局口径与禁造边见 `AGENTS.md` §1–§2。
>
> **2026-11-18 重组**：J 战役后路线图、Text 旧估算/闭包矩阵、旧排产与续990–1242
> 全文日志已移至 [`archive/priority-queue-2026-11-18-pre-nli-math.md`](archive/priority-queue-2026-11-18-pre-nli-math.md)。
> 本文件只保留当前基线、真实在飞、可执行队列、待裁决和最近日志。

**当前实测（2026-11-26）：wt1 全量证书闭合后仓面 SORRIED 48（`4bcbd7ad`）。历史：基线 AQ @`e4c384e6`（2026-11-18，`nliTskXLLIPLS` 真证）时为 51；wt2A 小模块验收后 49（`1ec06b28`，2026-11-20；根面复跑池后）**：

- cone `K_REACH 2,108,657`（基线实测；P0/P1/P2 置换的锥缩记账随池复跑仪器，见 §8 续1310/1312）/ **SORRIED 49→48**（2026-11-26 wt1 关闭）/ **`K_AXIOM 585`**；
  MODULES 12,140 / UNIVERSE 2,140,793 / COVERAGE 98.4989%；
  口径 II 39,125 / 51 / 585 / 49,868（仪器口径池后复跑；**49,868 = 仪器口径，未随 wt1 关闭重跑**，见续1563）。
- **SORRIED 48（2026-11-26：`nliCell3QZECFICwt1` 真证，49→48；`1ec06b28` 时为 49）
  = Assembly 48（47 `nli*` + 1 hLP）+ Text 0**。
  47 `nli*` = 38 `nliRest*` + 4 `nliTsk*` + **1 `nliCell3*`**（sqrt8 / wt2A / **wt1** 已闭）+ 4 直挂
  （`nliKcblrqcIneqDef` / `nliLpIneqs` / `nliMainNonlinearTerminalV11` / `nliOx3q1h`）。
- 根面 **589 = 585 native + 标准三 + `sorryAx`**；基座 585 未动。wt2A 已闭只减 sorry 源（50→49）。**2026-11-23 池归零后编排者亲跑复现 589 同集（585/585 在册、UNEXPECTED 仅 `sorryAx`；续1425）。**
- **运行态事故（2026-11-19，`lp-packed-single-leaf-w2`）**：主仓
  `lean/.lake/build/lib/lean/Kepler/LP/` 有 **969 个自指符号链接**（193 `.olean`、194 `.ilean`、
  194 `.trace`、388 `.hash`），由 farm 父目录穿透后 `ln -sfn` 误替换；`W6Align/` 幸存。
  **1,150 个 tracked LP 源文件无损、主仓 tracked 无改动**；上述基线仍是最后实测。
  **二次事故（2026-11-19 晚，PR-49）：rsync 从链接式旧池回灌把 36,198 个真 olean 变自指死链**，
  死链已全清、**v4 重编链在跑**（PID 31920，3,331 件断点续跑、3 槽并行，ETA 今晚；§8 续1308–1312）；
  根面/Assembly/Final 验收 2026-11-23 起可复跑：池 missing=0（恢复链 13:53 收线），编排者亲跑根面探针 589 同集（续1425）。
  修复链由编排者跑；禁止擅自 `lake build` 全量重建。事故报告在车道快照 `INCIDENT.md` 与登记册 PR-49。
- 仪器原样：[`e2e-reachability-map.tsv`](e2e-reachability-map.tsv)（12,795 行）；
  历史基线叙事：[`e2e-reachability-map.md`](e2e-reachability-map.md)。

核心阅读：[`hf-proof-map.md`](hf-proof-map.md)（证明主线）、
[`nli-campaign.md`](nli-campaign.md)（nli 数学路线与负结果）、
[`handoff-2026-11-18.md`](handoff-2026-11-18.md)（复现命令、易失池、快照索引）。

---

## 0. 当前里程碑

| 里程碑 | 当前状态 | 下一步 |
|---|---|---|
| M0 / 根面与可达图 | **wt2A 后仓面 SORRIED 49 / AXIOM 585**（`1ec06b28`，2026-11-20；根面 589 HEAD 精确态复现于 `84c3b4b4` 后，§8 续1425/1428） | 所有落库后重跑仪器；数字只在本文件头和地图维护 |
| M1a / Text 清债 | **完成：Text 0** | 不重开旧 Text 战役；历史矩阵见 §2.1d |
| M1b / 接口 | hTC 0；**hNL 48 + hLP 1** | 主攻 nli 数学压缩；LP 独立处理 |
| M2 / 信任基座 | 585 定格；manifest 数据源/生成器钉定已完成 | 抽样 replay、Docker 一键复现与最终公理断言，重算窗口另批 |
| M3 / 北极限 | **49 = 48 `nli*` + 1 hLP**（sqrt8、wt2A 已闭） | 先数学归约与复用，再证剩余计算核心；不以生成行数作为进展 |

### 0.1 剩余债务边界

- **hNL**：48 条。逐条路线和已证负结果以 [`nli-campaign.md`](nli-campaign.md) 为准；
  当前新侦察集中在二阶代数凹性、同盒联合包络、Bernstein 后端。
- **hLP**：`lpArchiveCertificatesDebt`，待证 42,889 条 bound 叶（189 infeasible 已闭）。
  **现有 bound 叶已经使用 `Y/D` 对偶向量 + `checkDualCMTF` 弱对偶检查 + `by decide`**；
  后续应审数据表示、内核归约和 olean 成本，不是重新发明 dual checker。
- `nliLpIneqs` 与 `nliKcblrqcIneqDef` 属 LP-gated 债，不能指望 γ4 路线顺带关闭。

---

## 1. 在飞

证明车道施工期间主仓 tracked 零改动；编译走 3 槽信号量 + guard 护栏（≤3 lean ∧ ≤24 GB ∧ pressure<2）。
每车道仍 ≤1 Lean，车道快照在 `~/c17_backup/lane_snapshots/<lane>/`。历史在飞表原文见
[`history/priority-queue-inflight-2026-11-26.md`](history/priority-queue-inflight-2026-11-26.md)。

| 车道 | 回执 | 唯一目标与止损 |
|---|---|---|
| `planarity-split-w1` | **在飞（2026-11-26 编排者发车；ZCode `agent_7283d025`；≤1 Lean）** | `Text.Planarity` 4.36 @5M：先应用 patch 11 的三处 proof-only 适配，再把 `azim_cone_of_combo`（:1811 起）拆 2–4 个 private lemma；既有声明签名/陈述逐字冻结；禁调 heartbeats；4.32/4.36 + 公理三路；3 轮卡死写 PAUSE_COST |
| `packing-chain-w1` | **在飞（2026-11-26 编排者发车；ZCode `agent_c983bc09`；≤1 Lean）** | 18/19 双验落库候选 + `PackingAuto8:295` 的 `VSub (Set V3)` 显式标注 + `PackingAuto14` @4.36（6/7/8 新 olean 解锁后 11 处同模式）；proof-body only；缺上游 4.36 olean 即报第一个缺失名 |
| `assembly-pattern-w1` | **在飞（2026-11-26 编排者发车；ZCode `agent_3dc88ca4`；≤1 Lean）** | `Assembly.lean:3693/3707/3722` **先测后修**（fragment 探针 4.36）；4.32 全模块 + 公理对照；输出 23 文件/80 处同模式 inventory 供 census；不改陈述 |
| `wt0-hol-replay-w1` | **在飞（2026-11-26 用户明批两 nli 各一发；`agent-6` / `agent-psiqcu0q`；≤1 Lean）** | 只做 HOL `(prep-QZECFIC wt0,0)` 原版 Taylor pass/glue 与 cell 覆盖；先真实单件再按原 80/79 推进；pp/分裂/终止参数不得自创；不走 route R、不扩其余 cell、不接 Assembly |
| `qitnpea-hol-replay-w1` | **在飞（2026-11-26 用户明批两 nli 各一发；`agent-7` / `agent-r0ek0a6b`；≤1 Lean）** | 只做 `QITNPEA1_1_2` 一个有完整原版规格的 case 及 Taylor pass/glue；不走角点电池/11片/456点，不接 Assembly；原数据缺失记 UNRESOLVED |

### 最近完成（仅作导航；完整结果见 §8 最近日志）

| 车道 | 回执 | 唯一目标与止损 |
|---|---|---|
| `lean436-blockers-w1` + `lean436-landing-w1` | **候选交付完成；15 笔逐笔落库 `577c3754`…`ab382e5c`（2026-11-26；双版本/公理/根面逐笔验收）；`16` 后补落库 `0caffebc`（SF-112）** | `01–10`、`12–17` 已提交；Assembly/Final 岛编译 RC=0，根面 589 同集；`11` Planarity 仍 BLOCKED（`planarity-split-w1` 在飞），`18/19` 在 `packing-chain-w1` 验证，GoodList/Auto8 未决；主工具链仍 4.32.2，清单见快照 `LANDED.tsv` |
| `wt0-r1-core-w1` | **完成：UNRESOLVED（2026-11-26；y4 目标 0 条；辅助 2/2 标准三；主仓未落库）** | `wt0_delta_bounds` 与 `wt0_small_matanD_bracket` 可复用；三 sol 槽聚合 dSE 紧包络未闭合，不是 wt0/route R 反证；不做 y5/y6/R3，SORRIED −0 |
| `qitnpea-wave1-y6-w1` | **完成：BUDGET_EXHAUSTED（2026-11-26；16 GB memcap；SHA 80/80；主仓未落库）** | 14 个置换元组截零检查与运输 elaboration errors=0，但内核/olean 生成超 16 GB；`curvCheckClamp_decide`、C.2、ConcaveOn/consumer 未闭；D3=150,022 B（当前单片用户明批），SORRIED −0，不量产 |
| `wt0-route-r-first-w1` | **完成/落库 `65d8039a`（2026-11-26；R4+R2 共 35/35 标准三；编排者 SHA 15/15 + 模块构建/最终公理复验 + push）** | R4 5 定理 + R2 30 定理，`wt0_corner_pos` 成立；505 行/22,653 B，olean 4,121,888 B，顺序编译 20.81 s；已落 `NliWt0LogKit`/`NliWt0Corner` 供 R1 复用；未接 Assembly、SORRIED −0；全 route R 仍 UNRESOLVED |
| `lean436-trans-workaround-w1` | **完成/主 patch 落库 `999aadb5`（2026-11-26；双版本与 Final 589 复验 + push）** | 离线中间值 + 小 decide + `taylorIter.eq_2`/rfl 已应用：4.32 模块构建 RC=0/20.51 s，4.36 直编 RC=0/35.57 s；五证书 `[propext]`、五 `_real` 标准三，API/陈述不变；Final 根面 589。后续由 `lean436-blockers-w1` 处理，主工具链仍 4.32.2 |
| `repo-hygiene-review-w1` | **完成（2026-11-26；只读交付，编排者 SHA 5/5 + P0 现场 spot-check）** | **不建议大面积重构**；优先 README/PLAN/pq/campaign 文档纠偏与账本瘦身，再 NliBanks18→20 复用 `nb12_nonneg_of_deriv` 两文件 pilot；17 项 arctan 公共化另卡另 pilot；Assembly 三对私有桥随必要改动顺带；两 tracked `.pyc` 可独立清理；REPORT/CODE_REVIEW/DOCS_REVIEW/RECOMMENDATIONS 在快照，未执行建议 |
| `qitnpea-wave1-prep-w1` | **完成（2026-11-26；wave1-slim-v2 当前 OVER-BAND，slim 条件目标 WITHIN-BAND；编排者 SHA 4/4 + HOL/字节/stdout/SAMPLE 复核 PASS）** | 交付六维卡、首件工单、EVIDENCE、11 项 ERRATA；456=144+96+216 首波合计，D5 37.24 min 首波投影；全表须程序化生表；y6 用 2.4636 外扩，复用二阶/CFWGKMBZ 域证书，局部凹性用 boxInf_le_of_slice_min；不支持直接量产 |
| `wt0-route-r-prep-w1` | **完成（2026-11-26；routeR-v1 整卡 UNRESOLVED，仅放行 R4+R2；编排者 SHA 9/9 + 双 Python 复算 PASS）** | HOL 8 cell/520 pass/512 glue/1,959.218513 s 复核；R4 已有 NB12+Trans 可薄适配，R2 余量约 8.278e−6；交付六维卡、WORK_ORDER、EVIDENCE、ERRATA；不支持全 route R 量产 |
| `a-l3-m2-probe-w1` | **完成（2026-11-26；M1 25.91 s = 2.68× ⇒ NO-GO；M2 未启动；wt1 停在 B）** | A/L3 1 箱 M1→M2：数据表 + 通用 checker；M1 值通道 >10 s 即 NO-GO；M2 全量 `t_full/9.661`（≤14.49 GO / >19.32 NO-GO），终端 `dcSlack` 通用化硬要求；不改主仓/不改 221/kit；≤1 Lean。**用户同日后续指令：wt1 不新增任务，只等本探针结果** |

---

## 2. 排队（按序补位）

### 2.1 用户指定记录的 D/E/F（D 的 packed 后续在飞）

| 候选 | 状态 | 范围与验收 | 边界 |
|---|---|---|---|
| **D** `lp-dual-representation-audit-w1` | **packed-w2 b2 单叶 bounded GO（独立验收）** | 字段等价无公理、六输出一致；独立两轮 wall/A0=1.063/1.048，olean=395,784 B | 无可落 patch，不车队化、不改 LP/D 层、不外推；LP 池恢复另批 |
| **E** `terminal11-family-compression-w1` | **第一阶段完成，组织性资产；三处勘误** | 独立重跑 parse/assign/cluster 一致；五模板覆盖 80 支、另 5 支独立；置换脚本仅测 74 显式 def；ly 文档公式已勘误 | 超越核未解决，不是证明 GO；不跑 85 支农场/批量发射，第二阶段等用户裁决 |
| **F** `cell3-wt-math-w1` | **已收线，UNRESOLVED** | wt2A 已归约到三维核 `Δ≥0 ⇒ 0<w2aF`，wt1 未动笔；y5 全盒严格增有数值反例 | 归约与消费探针标准三；后续 `cell3-wt2a-core-w1` 已超时暂缓，WIP 已抢救，重启等用户裁决 |

D 的 `lp-packed-single-leaf-w2` 已于 2026-11-19 获批发车；E 已收线，详见 `nli-campaign.md` §1.24；F 保持 UNRESOLVED。

### 2.2 A/B/C 的条件后续

`g4-hessian-lean-w1`、`fhb-seam-curve-w1`、`bernstein-kernel-pilot-w1` 已于 2026-11-18 获批发车，见 §1；下列仍待条件与用户裁决。

| 条件后续 | 前置 | 允许做什么 |
|---|---|---|
| `b0-master-lean-w1` | **搁置：原整盒凹性归约已证伪** | 需要新的分段/代数证书（CAD-lite 或消费端分段假设）；不得重试单调性/逐坐标凹性/张量三路 |
| `g4-fixed-base-w6-w1` | 低优先、用户裁决 | 仅机械固定 all-2 基点 W2–W6；不宣称整盒、不直接计为 B0 六债闭合 |
| `fhb-floor-mono-w1` | **已收线，UNRESOLVED** | 一阶导全盒为正有数值反例；只交付凹性 + 端点 ⇒ m3/m4/m5 的已验归约，H1/H2 未证；不自动续发高维证书车道 |
| `fhb-g3pos-w1/w2` | **w2 Phase 1 完成，整体暂缓** | 曲线核心与右端点均独立验收标准三；尾部单调性只有数值评估。后续从已证端点 fresh 做一阶导数 + 小盒界 pilot，等用户裁决 |
| FHBv2a | FHBa 真闭合 + 用户裁决 | 余量更紧；在 FHBa 曲线证书落地前不启动超越部分 |
| 完整 BernsteinKit | **搁置：单叶定标 UNRESOLVED** | 未获得合格 81 系数叶，禁止量产 1,215 系数或全库后端 |
| `bernstein-kernel-representation-w1` | 低优先、fresh session + 用户裁决 | 仅重做 81 叶的显式指数向量/内核友好 Decidable 表示；不得沿用当前 Quot/Finsupp 路径，两小时无合格叶即再次暂缓并复审，不写永久放弃 |

### 2.3 既有非农场候选（保留，不与 D/E/F 重复）

| 项 | 状态 | 备注 |
|---|---|---|
| `nliTskIYOUOBFsharpv2` | 排队 | 已判纯 MATH/hybrid；独立于 A–E，可复用新的导数资产 |
| ZTG γ4 解耦 4 | 排队 | dihY 半边已落；优先消费 A/B 的联合/凹性结果，不重开泰勒量产 |
| `ox3q1h` S2a margin″ | **等用户裁决** | SF 111 已解锁；小规模数学装配与 S2b 量产分开评估 |
| TerminalV11 的 3 MATH + 1 补粘 | 排队 | 可先做，但**不会单独减少顶层 SORRIED**；完整闭合仍需 E 的压缩结果和剩余计算路线 |
| M2 manifest replay / Docker | 排队 | 重算窗口另批；不阻塞当前零 Lean 数学侦察 |

### 2.4 只读数学调研候选（首项及联合包络后续已发车，其余等用户裁决）

推荐先做**单债、零 Lean 的证伪探针**，不把五条同时开成新路线。覆盖条数和加速比均不预支。

| 候选 | 数学内容与最小闸 | 当前边界 |
|---|---|---|
| `nli-algebraize-fat1-scout-w1` | **已收线，条件 GO（数值）**；`QITNPEA1_1_2` 两半 ρ≈0.125/0.139，8 区域 | 后续 `fat1-g3-exact-w1` 已收线：通用交错 Taylor 引理与 G3 S39 独立验收标准三，patch 未落库；bank/G 正性仍未闭合，详见 `nli-campaign.md` §1.25 |
| `fat1-g-positivity-w1` | **超时暂缓（可重启），WIP 已抢救**；最新 2,975 行原样 RC=1，注释修复探针仍有 82 个 error，无公理面 | 不自动 resume、不接旧 patch；用户另批后 fresh 从快照，先修发射器、逐段验证并简洁化，不直接重生成整件 |
| `joint-envelope-extension-scout-w1` | **已收线，两处勘误**；#147 仅否定独立值域服务算法；QITNPEA1 并盒候选经复跑，但 1_1 分母纠错后不覆盖 | 修正后仅数值覆盖在案 1_0/1_2/2_0，零 Lean、零减债；详见 `nli-campaign.md` §1.23 |
| `qitnpea1-shared-floor-w1` | **已收线 UNRESOLVED（§8 续1411）**：fat1 w=2服务余量1/20000，共享面仍有正面数值/局部区间证据；新kink勘误已入档 | 无精确全盒证书与完整覆盖，朴素/闭式Taylor均pending；只否定当前表示闭合并候选，不否定原命题。后续须更紧sound包络+pending=0+独立逐叶重放，详见`nli-campaign`§1.27 |
| `disjunction-lp-scout-w1` | **已收线，常数权重 NO-GO**；三点 Farkas 证人独立复核最小分量 +0.001271705 | 不否定析取命题；h0cut 单分片亦失败，更细分片/变权重不优先 |
| 1-D 残差短证书 | ox3q1h 的 y4 内点残差尝低次 Bernstein/弦线；优先复用树内模式 | 依赖代数化先行；不自动重启完整 BernsteinKit |
| Hessian 分类服务 | 用精确符号分类决定哪些盒允许凹性/凸性 glue，正反例先挡住错误车道 | 是负过滤器和共享服务，不承诺直接减债；W1/W5 仍未落库 |

### 2.1d Text 闭包矩阵（历史编号保留，已结案）

**Text 0，旧 18 条估算、闭包矩阵与 J 战役队列表不再执行。**
历史正文见 [`archive/priority-queue-2026-11-18-pre-nli-math.md`](archive/priority-queue-2026-11-18-pre-nli-math.md) §2.1d；
独立报告见 [`archive/scouts/text-closure-matrix-2026-11-12.md`](archive/scouts/text-closure-matrix-2026-11-12.md)。

---

## 3. 等用户裁决 / 保持 hold

| 项 | 当前处理 |
|---|---|
| `ox3q1h` S2a margin″ 装配车道 | 未批；与 S2b 分开裁决 |
| `ox3q1h` S2b 其余批（约 67 万行估计） | 未批；建议等 A–C 结果，不在本轮擅自量产 |
| 农场解冻 5 项（nli 农场 / Rule P 规模化 / certtm 特性 / LP 证书层 / 磁盘算力） | 未批；全部保持 EST 与 hold |
| certtm TM3 量产、Mono*、D 其它项、585 信任基座 | 保持 hold；零新增 axiom/sorry/native_decide |
| **主仓 LP 构建池恢复** | **等用户裁决**：`lp-packed-single-leaf-w2` farm 穿透事故见文件头警示；源码无损但 LP 产物不可用，根验收暂不可复跑。不得擅自全量重建；先确定恢复范围/串行 shard 方案与备份 |
| push | 未批；`origin/main..HEAD = 68`（实测 HEAD `4f9e12cd`，2026-11-18） |

### 3.1 shard 压缩三候选（2026-11-21 用户：先记录，以后再说）

> 状态：**暂缓，不开发**。细节与“不要再试”清单见
> [`shard-math-roadmap.md`](shard-math-roadmap.md)；数字出处见 §8 续1367 与
> `~/c17_backup/lane_snapshots/shard-math-research-w1/`。以下只为以后重启时
> 保留入口，不代表已批。

| 候选 | 内容与已知证据 | 重启前置 / 裁决点 |
|---|---|---|
| **W1** notame7 进 native `next_tame` | `next_tame` 与 AFP 同形、不含 notame7；剪枝因子 Tri 1.68× / Pent 1.96×（终图集逐根相等）；soundness 零件全在库，缺 frontier-`inv` | 第一问 = **pruned-loop ⇒ unpruned-loop bridge 是否成立**（成立则 585 陈述不变、免 SF）；不成立再走改 `next_tame` + SF + 用户改裁 |
| **W2** 成本均衡合并 585 → K+5 | 合并墙钟 −36%、RSS 1.6 GB 不变、总时间不升；K=3 时 **8 条公理**（与 Isabelle 8 条 `by eval` 同量级） | 与 AGENTS §1「恰好 585」冲突 ⇒ **必须用户改裁**；失去分片级续跑 |
| **W3** Interval cases-swap P3-GO 批 | 149,727 行 → ≈32.6k（−78%）；五族精确 Bernstein min 已在 `cases-swap-prep-w1/PREP.md` §3 验证；不改信任面 | **未批缓行**；CertD/CertP 单文件 11–22 GB，只能单槽；批产前先做 C2125338128M |

**不要重试**（机器证据已关闭）：CertShards 跨根记忆化/根覆盖、根内去重、343 死根、
Interval 叶级去重/对称、靠重分片省总时间。详见 roadmap §5。

---

## 4. 当前 nli 数学路线与禁重复项

**当前路线**：

```text
同盒归约 / 消分支 / 联合包络
  → 单调性与二阶代数凹性，消成有限边界候选
  → 只对剩余多项式符号义务使用 Bernstein
  → 少量有理数据 + 内核 decide
```

不把“数据化”误当成数学减叶，也不把 Bernstein 系数凸包称为“零 wrap”。
新版通用引擎、S2b 量产和农场都必须先过代表样本与真实 Lean 单叶定标。

**不要重复以下已判负或已澄清的路线**：

- rad2 望远镜路线已用尽；ZTG 剩余 10 条不能靠 rad2 支关闭。
- CertTM2 / Gate-0 已实测 NO-GO；它只否定该类包络，不否定精确代数凹性。
- ox3q1h 不能拆成独立的 `γ4≥G` 与 `dihY≥D`；必须联合处理。
- IXPOTPA 不得再使用「γ23 在 F3∩F4 对 y2 单调增 / 共享最差角」归约（A/B 精确反例，续1351）；eta 单调下集仍成立，原定理未被反证。旧 `battery_threshold.py` 在宽度/深度上限强制归 F3，不算零 pending 证书。
- Bernstein 仍有值域外包；`sqrt/atan` 需要有理逼近和误差账，不能直接当多项式。
- LP bound 叶已经是 weak-dual certificate；不得把“新增 dual checker”当成新收益。

详细证据与逐条债表：[`nli-campaign.md`](nli-campaign.md) 与
`~/c17_backup/lane_snapshots/farm-ops-w1/FARM_PLAN.md` / `DEBTS.tsv`。

---

## 5–7. 文档、归档与维护规则

- 现役数字只在本文件头维护；其它文档引用，不另抄一份。
- 当前战略讨论稿：[`../strategy/nil-math-20261118-glm53.md`](../strategy/nil-math-20261118-glm53.md)。
  其中 Bernstein/LP 的强度判断按 §4 的澄清使用，不视为实测结论。
- **2026-11-23 NLI 战略复盘与车道规划**：[`../strategy/nli-strategy-20261123.md`](../strategy/nli-strategy-20261123.md)
  （49 件分档 1/15/27/1/2/3；主线 wt1→ZTG trio；5 个方向；混世界 A/C 待裁）。
- 2026-11-18 重组前全文：[`archive/priority-queue-2026-11-18-pre-nli-math.md`](archive/priority-queue-2026-11-18-pre-nli-math.md)。
- 更早队列/战术/J 战役表：[`archive/priority-queue-legacy-2026-10.md`](archive/priority-queue-legacy-2026-10.md)。
- 2026-11-26 瘦身迁出的 328 个旧日期条目见
  [`history/changelog-archive-3.md`](history/changelog-archive-3.md)；续990–1242 全文另见
  2026-11-18 重组前快照；续306–989 见
  [`history/changelog-archive-2.md`](history/changelog-archive-2.md)，续1–344 见
  [`history/changelog-archive.md`](history/changelog-archive.md)。
- 历史只搬不删；旧数字需要纠正时加 ERRATA，不覆写历史原文。
- §8 只保留最近窗口；超出后机械迁入历史/快照，保持当前队列可读。

---

## 8. 变更日志（新 → 旧）


> 当前仅保留最近 **20 个日期条目**；迁出的旧窗口原文见
> [`history/changelog-archive-3.md`](history/changelog-archive-3.md)。
> 续号有缺号与历史重叠，以日期条目和 commit 为准，不按续号推测完整性。

- **2026-11-26（Lean 4.36 Wave 0 落库 + Wave 1 三车道发车；续1591）**：
  ① **SF-112 / patch 16 落库 `0caffebc`**：`PackingAuto2` 六处陈述 `mcellSet V X` → `X ∈ mcellSet V`（`QZYZMJC_concl`/`KIZHLTL3_concl`/`TSKAJXY_statement`/`GRUTOTI1_concl`/`REUHADY_concl`/`REUHADY_concl_version2`）+ 一处证明体 `setOf`（:2779）；分级 A，HOL `pack_concl.hl:185/210/224/294/306/325` 原文即应用形。闸 `GATE_MODE=STATEMENT-FIX SF_ITEM=112` → GATE-PASS；4.36 岛直编 RC=0/0 err/28.18 s/6.32 GB；`TSKAJXY_statement` 公理原/候选一致 `[propext, Classical.choice, Quot.sound]`，五 sorry 声明仍 `sorryAx`；解锁 71 个 import 下游（含 18/19）。存档 patch `docs/statement-fix-proposals-patches/112-…patch`。
  ② **pin 与口径 `8de76453`**：新增 `docs/lean-4.36-pin.md`（toolchain commit `611c117b…` + mathlib `fc4f59e5…` + 8 包 rev + cache 9,117 + 切换检查单 + 未决 5 项）；`lakefile.toml` 的 Final 闭包注释 8,869 → **9,137**（实测 `scripts/check_acceptance_targets.py`；1,249 是模块 `Kepler` 闭包，口径无误，不是 ERRATA）。
  ③ **Wave 1 三车道发车（异步，≤3 lean）**：`planarity-split-w1`（ZCode `agent_7283d025`，Planarity 拆 2–4 private lemma，5M 不调）、`packing-chain-w1`（`agent_c983bc09`，18/19 + Auto8 VSub + Auto14 同模式）、`assembly-pattern-w1`（`agent_3dc88ca4`，Assembly 三处先测后修 + 80 处 inventory）。全部复制式 / 主仓零改动 / 禁 lake build。
  ④ **用户 2026-11-26 裁定（本项已拍）**：GoodList `+Classical.choice` 漂移 = **记录 + 一轮实例定位，不当切换硬阻塞**（根面 589 不变；漂移只影响「good_list 零公理」叙述）。探针设计（排在 Wave 1 之后，不超 3 lean）：先用最小文件 `import Kepler.Assembly.GoodListDefs` + `#print axioms goodListB` 在 4.32/4.36 对照——若 `def goodListB` 本身在 4.36 已含 `Classical.choice`，则漂移源在它自己的三处 `decide` 项（与 shard 证明无关），再用三个同形小 def 逐项二分；若 `goodListB` 干净，才回到 shard 层做 `trace.Meta.synthInstance`。census（~1 天机器时间）等 Wave 1 收线后发。
  ⑤ **两 nli 改走 HOL 原版复刻首件（用户明批）**：`wt0-hol-replay-w1`（`agent-6` / `agent-psiqcu0q`）只做 `(prep-QZECFIC wt0,0)` 的真实 Taylor pass/glue 与原 80/79 cell 覆盖；`qitnpea-hol-replay-w1`（`agent-7` / `agent-r0ek0a6b`）只做 `QITNPEA1_1_2` 一个有完整原版规格的 case。两卡与 TASK 已先落各自快照；不走 route R、角点电池、11 片、456 点，不接 Assembly，pp/分裂/终止参数不自创。与既有 Wave 1 共享 ≤3 lean 护栏，编译排队，不扩量产。
- **2026-11-26（Lean 4.36 兼容补丁 15 笔逐笔验收并落库；续1590）**：
  ① **逐笔 commit**：01 `577c3754`；07 `0b0e942f`；03 `d34abf8c`；04 `535a8d60`；02 `3c9e8b8c`；08 `07f2caa0`；05 `ba222bfc`；06 `f1ab403d`；09 `64721101`；10 `c01fff8d`；12 `8a7be704`；13 `682f5826`；14 `1aed8889`；15 `ba3aa0ce`；17 `ab382e5c`。每笔均先应用候选、4.32/4.36 单文件 RC=0、相关公开/私有 `#print axioms` 通过、根面公理列表与基线逐名一致后才独立 commit；逐笔证据见 `~/c17_backup/lane_snapshots/lean436-landing-w1/LANDED.tsv` 与 logs。
  ② **最终岛验收**：`Kepler/Assembly.lean` RC=0 / 106.60 s，`Kepler/Final.lean` RC=0 / 5.85 s；编排者亲跑根面 = **589 = 585 native + 标准三 + `sorryAx`**，与开工基线逐名相同。SORRIED 48 / AXIOM 585 不变，主工具链仍 **4.32.2**，未做 139、585 全量或版本切换。
  ③ **未纳入**：`11` Planarity 在原 5M heartbeats 下仍 BLOCKED（20M 仅诊断）；`16` 含陈述印刷形 DIFFERS 但无 SF 立案，`18/19` 依赖其 4.36 适配，三笔均未落。GoodList `+Classical.choice` 漂移、`PackingAuto8` VSub、Assembly 三处同模式仍是升级 blocker；K009 实测无公理漂移。
- **2026-11-26（wt0 R1 与 QITNPEA y6 首件收线：均未减债；续1589）**：
  ① **wt0 `UNRESOLVED`**：y4 `MonotoneOn ... [2.01,2.30]` 未证，保留 `wt0_delta_bounds`、`wt0_small_matanD_bracket` 两条标准三辅助定理；卡点是三 sol 槽聚合 dSE 的相关性紧包络，不能外推原命题或 route R 为假。主仓未落辅助 patch，SORRIED −0。
  ② **QITNPEA `BUDGET_EXHAUSTED`**：14 个置换元组的截零探针均 some/lo 正、运输 elaboration errors=0，但内核检查/olean 生成在 16 GB memcap 被终止；`curvCheckClamp_decide`、C.2、ConcaveOn 与 consumer 未闭。D3=150,022 B（2.946×）按用户「超过 2× 还好，先继续」仅对当前单片记 USER-APPROVED，不是 D3 达标或量产授权。SHA 80/80，SORRIED −0。
  ③ **边界**：两条均未接 Assembly、未做 11 片/456 点/农场，后续均等用户指令，不自动 resume。下一条：续1588。
- **2026-11-26（Trans 兼容 patch 应用并推送 `999aadb5`；升级 blockers 车道发车；续1588）**：
  ① **应用与双版本验收**：候选 patch 已应用，源与 `Trans.offline.lean` 逐字节一致（+242/−5）。4.32 `lake build Kepler.Interval.Trans` RC=0/20.51 s；4.36 直编 RC=0/35.57 s、峰值 6.04 GB。五计算证书均恰 `[propext]`，五 `_real` 均标准三；`Kepler.Final` 重编并亲跑根面 **589 = 585 native + 标准三 + sorryAx**。commit/push `999aadb5`，主工具链仍 4.32.2。
  ② **新 lane 回执**：`lean436-blockers-w1` = 原 `agent-3` resume / `agent-qeyxbrsn`；任务书已同批落快照。目标 = 同一份源在 4.32/4.36 通过的候选补丁，先 `exLn_eval` 原等式离线证明，再 Conic/Geom/Graphs/Packing 破类，随后 CFW 短链、NliBanks21/实际大证书、K009/GoodList 两形状公理漂移，并形成 MIGRATION。
  ③ **边界**：本车道不直接升级/改主仓，候选 patch 验收后才落库；禁 native_decide/sorry/skipKernelTC/深度或心跳当修复、禁全139/全库，≤1 Lean。Trans 解决不等于整仓升级，剩余 API/elaboration/信任/根面逐项判。下一条：续1587。
- **2026-11-26（Lean 4.36 升级绕法收线：完整生产 Trans 双版本通过；整仓仍留 4.32.2；续1587）**：
  ① **实质突破**：`lean436-trans-workaround-w1` 用**离线中间值 + 小 `decide` + `taylorIter.eq_2` + `rfl`** 消除五个 `maxRecDepth` 硬破；只改五个 pilot 证明体（+237 行），全部声明、陈述、模块路径、API 保持不变，不是隔离/删测试。完整 `Trans.offline.lean`：4.36 **RC=0 / 22.27 s**，4.32 **RC=0 / 24.33 s**；五计算证书双版本均恰 `[propext]`，五 `_real` 均标准三，生产抽样亦标准三。零 native_decide/新公理/skipKernelTC/提高深度。
  ② **验收与边界**：SHA **157/157**、`git apply --check` PASS；主 patch 未应用、未 commit。消费者静态复核表明五组 pilot 仓外无引用，但生产仍经 Final→Assembly→CQITNPEA→Trans，故绕法有生产意义。通用 norm_num/simp+decide 因公理漂移未采用；模块隔离只作备选。
  ③ **整仓判词**：仍暂留 **4.32.2**。`exLn_eval` 深递归尚无离线原等式修复（其演示隔离后的 CFW 短链双版本通过）；Conic `lintegral_add_compl` 隐参名 A→s、Geom elaboration 3–25×、GoodListShard 公理漂移、585/139/Final 根面均未解决或未重验。建议把 patch 作为独立升级准备候选，下一轮先处理 exLn/Conic/实际证书抽样，**不把 Trans 单点成功写成整仓可升级**。下一条：续1585。
- **2026-11-26（wt0 R4/R2 落库推送 + R1 y4 代表单调核发车；续1586）**：
  ① **R4/R2 落库**：`NliWt0LogKit` + `NliWt0Corner` 以 **`65d8039a`** commit/push。两个单模块构建均成功，源文件 warning/error=0；最终 `#print axioms Kepler.NliWt0Corner.wt0_corner_pos` 仍恰 `[propext, Classical.choice, Quot.sound]`。R4+R2 共35定理，SORRIED 48 / AXIOM 585 不变，不接 Assembly。
  ② **R1 回执**：`wt0-r1-core-w1` = 原 `agent-0` resume / `agent-jh56tuws`；新卡 `routeR-R1-y4-v1` 与任务书已同批落快照。唯一目标为 `MonotoneOn (fun y4 => pc3 y4 y5 y6) (Icc 2.01 2.30)`（y5/y6 同盒），在新模块重建5–6位槽导数括号，private `nb18_step0` 只作模板。
  ③ **边界**：只做 y4 代表件，不做 y5/y6、R3/R5、Assembly、T2/农场；约450行或三轮结构性卡死即交班，缩核/换表先更新卡。开工前 lean=0/pressure=1，≤1 Lean；全定理公理与D1/D3/D4/D5实测后交付，首件 SORRIED −0。下一条：续1587。
- **2026-11-26（用户批准账本瘦身 + NliBanks18/20 公共引理复用试点；续1585）**：
  ① **账本瘦身**：pq 从 **2,738→543 行**（58.8 KB）；§1 由 69 行旧表改为当时 3 条真实在飞 + 4 条最近完成，§8 由 343 个日期条目保留最近 20。新增 `history/priority-queue-inflight-2026-11-26.md` 与 `history/changelog-archive-3.md`（323 条）；独立校验 **343=20+323，全部条目逐字同序、§1 原文保留**，并更新 `docs/README.md` 与 pq 的归档链接。
  ② **helper 试点**：删除 NliBanks18/20 两份私有 `*_nonneg_of_deriv` 副本，所有 5 个调用点改调 `Kepler.NliBanks12.nb12_nonneg_of_deriv`；零新增 import、公开陈述不变。单模块 `lake build Kepler.NliBanks18` / `Kepler.NliBanks20` 分别 PASS（97.73 s / 212.45 s），独立直编与 NliBanks27 消费编译（55.86 s）均 RC=0/error=0。
  ③ **公理验收**：修改前后对照 `Kepler.NliBanks18.nb18_bank` 与 `Kepler.NliBanks27.bank_wt2A` 均恰 `[propext, Classical.choice, Quot.sound]`；零新增 sorry/axiom/native_decide，SORRIED 48 / AXIOM 585 不变。wt0 首件在同基线上另复验通过（续1584）。
  ④ 本批未提交 commit；用户另问的 **不 retro-fit 全部旧证明到 NliKit.BoxTree** 仅作架构边界解释，不重开已闭合件。下一条：续1584。
- **2026-11-26（wt0 R4+R2 首件完成：35/35 标准三；独立复验通过；续1584）**：
  ① `wt0-route-r-first-w1` 完成 R4 log kit 5 定理与 R2 有理角点 30 定理，最终 `wt0_corner_pos : (17/100000:ℝ) < pc3 (201/100) 2 2`。源码 **505 行 / 22,653 B**，olean **4,121,888 B**，顺序编译 **20.81 s**；35/35 恰 `[propext, Classical.choice, Quot.sound]`，零 sorryAx/native_decide，首件不接 Assembly、SORRIED −0。
  ② 编排者验收：SHA **15/15**、`git apply --check` PASS、快照 symlink=0；另从最终交付源独立重编 R4/R2（R4 5.34 s、R2 15.45 s，均 RC=0/error=0/warning=0），且在 NliBanks18 helper 整理后无回归。patch 与证据留快照，**未落主仓、未 commit**。
  ③ 全 route R 仍 **UNRESOLVED**：R1/R3/R5 未施工，R3-i/ii 未选，D2/D4 下界未闭合；只具备另立 R1 工单与六维卡的工程条件，**不自动发车**。下一条：续1583。
- **2026-11-26（代码/文档组织只读审查收线：不建议大重构；文档纠偏 > 账本瘦身 > 两文件去重；续1583）**：
  ① **交付验收**：`repo-hygiene-review-w1` 交付 REPORT/CODE_REVIEW/DOCS_REVIEW/RECOMMENDATIONS/INVENTORY，SHA **5/5**；142 处 path:line 静态检查通过，真实采样覆盖 Text/NliBanks/Gamma4/TaylorSecond/W1DC/NliKit/Assembly/Interval/Graphs/LP 与生成器，零 Lean/主仓改动。编排者另 spot-check README/PLAN/pq/campaign，P0 漂移当前仍成立。
  ② **代码结论**：规模主要在证书与生成物（221 个 ignored W1DC 即 777,090 行），不全仓拆 Assembly、统一两种 DC/生成证书、import 最小化或重排编号模块。最小安全去重 = NliBanks18→20 复用 `NliBanks12.nb12_nonneg_of_deriv`（现有闭包已含）；17 项 arctan 约 96.7% 同构但需独立 pilot/PARITY；Assembly 三对私有桥只随必要改动顺带。
  ③ **文档结论**：README 仍指引已禁 `make build/check/reprove`，PLAN 横幅 51、pq M0/M3 49、hNL 48、LP 根面不可复跑与现行 48/恢复完成冲突；campaign 的 wt2A 未证/wt1 旧卡/456 每债/旧在飞亦需纠偏。§1 混历史、§8 超窗，按既定规则机械迁 history，入口数字尽量改 pq 指针。两个 tracked `.pyc` 可独立清理，pipeline 证据不动。
  ④ **处置**：报告仅建议，用户之后决定；本线不执行重构/清理。Top 3 = 文档安全与状态纠偏 → 账本瘦身 → 两文件 helper pilot。SORRIED 48 / AXIOM 585 不变。下一条：续1582。
- **2026-11-26（用户派发 Lean 4.36 升级绕法评估；续1582）**：
  ① **回执**：`lean436-trans-workaround-w1` = `agent-3` / `agent-ik9hahnb`；任务书已同批落快照。当前 4.32.2 不动，本机已有 4.36.0，无需下载；旧 `lean436-pilot-w1` 的 139 模块、Trans 五处内核 decide/maxRecDepth 与其余升级为唯一基线。
  ② **优先假设**：五个失败点位于 Trans 末尾 pilot 区，先核真实消费者与生产闭包，评估把 pilot 隔离到可选模块而保持生产 API/陈述不变；有真实消费者时再测证明型算术、浅递归/分块、离线数据+内核小检查。禁止 native_decide、skipKernelTC、删生产义务或用更深上限冒充修复。
  ③ **边界**：≤1 Lean、memlim/三槽、复制式岛，主仓/toolchain/.lake/旧快照只读；不重复旧四轮战役或已知 SIGABRT。若 Trans 解开，仅小样本核 ConicCapVolume/NliBanks/CFWGKMBZ 等剩余阻塞，仍单列 elaboration 3–25×、GoodListShard 公理漂移和 585/根面未验；不把单点成功写成整仓可升级。SORRIED 48 / AXIOM 585 不变。下一条：续1581。
- **2026-11-26（QITNPEA 首波准备线验收并续入 y6 受限 Lean 首件；续1581）**：
  ① **准备线验收**：`qitnpea-wave1-prep-w1` 交付 `wave1-slim-v2` 卡/工单/证据/11 项 ERRATA；SHA **4/4**。编排者独立复核 HOL 三源 1,992 hash 双射与 family 1,942 case、D3 四段 **25,464 B**（严格 2×=50,928）、stdout JSON 与准备线逐字节一致，并复跑 25 个债务-轴-片 SAMPLE（全负但非证明）。当前实测 **OVER-BAND**，slim 仅为条件式 WITHIN-BAND 目标。
  ② **关键修正**：456=144+96+216 是首波合计，N=40 投影 **37.24 min 首波合计**；53,753 B 两点 kit 加字面表至少 2.79143×，必须程序化生表且生成器计入 D3。y2/y5/y6 上端改 **2.4636**，避免 2.4635 截真盒；二阶闭式与 CFWGKMBZ `deltaY>0` 可复用，wide 定理不能用于 y4>2hplus；局部凹性必须消费带 hx 的 `boxInf_le_of_slice_min`，不能用过强包装。
  ③ **首件回执**：`qitnpea-wave1-y6-w1` = 原 `agent-1` resume / `agent-m4s5djo4`；任务书已同批落快照。≤1 Lean，开工前 lean=0/pressure=1；做两行回归、D3 瘦身/生表最小接口、y6 曲率/ConcaveOn/真实消费探针，全部新 Lean+生成器源 **≤50,928 B**，超标记 PAUSE_COST；不做其余片/456 点/Assembly，SORRIED −0 / AXIOM 585 不变。下一条：续1580。
- **2026-11-26（wt0 route R 准备线验收并续入 R4+R2 Lean 首件；续1580）**：
  ① **准备线验收**：`wt0-route-r-prep-w1` 交付 `routeR-v1` 六维卡/工单/证据/ERRATA；SHA **9/9**，编排者独立重跑 `recompute_hol.py`/`recompute_corner.py` 均与交付日志逐字节一致。整卡保持 **UNRESOLVED**，只允许 R4+R2 最小首件，不支持 R1/R3/R5 或量产。HOL 基线复核 = 8 cell / 520 pass / 512 glue / **1,959.218513 s**。
  ② **关键新发现**：R4 不是零存量，`NliBanks12:291` 负支双侧括号 + `Interval/Trans:1676,1737` atanh 级数/尾界可薄适配；R2 目标 `17/100000 < pc3 (201/100) 2 2` 的余量仅约 **8.278e−6**，NB18 常量件为 private 且过宽，须从公开 Gamma4Val 新证紧 K1/K2。另登记 R 编号、旧 a1 探针代值、trig 投影加法与 D3 字节口径 ERRATA。
  ③ **首件回执**：`wt0-route-r-first-w1` = 原 `agent-0` resume / `agent-eexkljz0`；任务书已同批落快照。≤1 Lean，开工前 lean=0/pressure=1；只做 R4+R2，全定理公理审计并回填 D1/D3/D4/D5，不做 R1/R3/R5/Assembly/T2/农场，SORRIED −0 / AXIOM 585 不变。下一条：续1579。
- **2026-11-26（用户派发 1 个代码/文档组织只读审查 subagent；续1579）**：
  ① **回执**：`repo-hygiene-review-w1` = `agent-2` / `agent-dqbczl3x`；任务书已同批落快照。用户明确要求只读、汇总建议后再决定下一步，本车道不执行重构/文档修改。
  ② **范围**：目录与 import 组织、手写/生成/证书代码分层采样；大面积重构必要性；重复候选按可安全抽取/需 pilot/不要抽/生成器层分桶，至少追一个消费者；文档入口层/账本层/历史层与过时项。
  ③ **边界**：零 Lean/lake/build/地图仪器，主仓与旧快照只读，不干扰 QITNPEA/wt0 两条准备线；产物仅快照 `REPORT.md` + `CODE_REVIEW.md` + `DOCS_REVIEW.md` + `RECOMMENDATIONS.md` + 轻量清单/SHA。SORRIED 48 / AXIOM 585 不变。下一条：续1578。
- **2026-11-26（A/L3 1 箱 M1 实测 = NO-GO；wt1 停在 B；QITNPEA 456 / wt0 R 编号两处 ERRATA；续1578）**：
  ① **A/L3 M1 NO-GO**：`a-l3-m2-probe-w1` 全量 25.91 s / 6.51 GB / RC=0；box-only 14.94 s；
  同日 L1 对照 71.04 s（机器慢 1.43×）；主判据 `r = 25.91/9.661 = 2.68×`；决定性单元 =
  一次 shape 表内核求值 3.07 s vs 落库 1.12 s（2.74× 原始 / 1.92× 漂移校正）；
  M1 >10 s 触发卡 §2.3 止损，**M2 未启动**；全量投影 33–43 s/箱 = 3.4–4.5×。
  ② **结构原因**：内核只归约 `List`/`Option`/`match`，`Array.get` 不归约；动态索引查表每节点
  ≤152 步 + 每 op 一次 match；唯一出路是按节点特化 run = 落库 L1 形态本身。**判词范围 =
  本求值器设计（索引式 List 表机）的值通道 M1**；不外推到原命题/其它求值策略。
  ③ **数据/信任**：50 个落库 DC 字面量 0 不符；17 条 axioms 全标准三、0 sorryAx/native_decide；
  0 error。缺口：`boxTopF=w1F3Z` 不能 rfl、M2 未做、只 3 个 matan 臂、两套 shape 表、
  每箱数据 4,967 B（S4 级）、olean 1,316,616 B（0.371×）。
  ④ **ERRATA-1（QITNPEA 口径）**：首波 456 = **144+96+216 合计**，不是每债 456；
  D5 4.9 s/点 × 456 ≈ **37 min 合计**；旧「37 min/债、13 债 8 h」（续1573/1574）作废。
  ⑤ **ERRATA-2（wt0 R 编号）**：以旧执行卡为准 **R1 核 / R2 角点 / R3 墙 / R4 log kit /
  R5 装配**；施工次序 R4→R2→R1→R3→R5；handoff 旧版 §3.2 漂移已改。
  ⑥ **处置**：wt1 停在 B（`7b0ae9bd`），不再投 L1/杠杆②/A；三线中 wt1 线转维护，Lean 槽给
  QITNPEA/wt0。两条零 Lean 准备线（续1577）继续。SORRIED 48 / AXIOM 585 不变。下一条：续1577。
- **2026-11-26（用户明批「先发车 QITNPEA 和 wt0，wt1 等那边结果」；两条零 Lean 准备车道已发；续1577）**：
  ① **用户裁决**：QITNPEA / wt0 现在发车；wt1 不新增任务，只等既有 `a-l3-m2-probe-w1` 结果，不重复派 A 探针。
  ② **QITNPEA 回执**：`qitnpea-wave1-prep-w1` = `agent-1` / `agent-m9lp0l0h`；任务书已落快照同批。零 Lean 更新首波 PARITY CARD + 下一条首件工单：D3 机械缩减、y6 曲率表单片、456=144+96+216 首波合计与 D5 口径勘误；不生成全表、不量产。
  ③ **wt0 回执**：`wt0-route-r-prep-w1` = `agent-0` / `agent-fmxghi0p`；任务书已落快照同批。零 Lean 新建 route R 六维卡 + R4 log kit/R2 有理角点首件工单；统一 R1 核/R2 角点/R3 墙/R4 log/R5 装配，T2/DC 与 38,011 叶农场禁行。
  ④ **后续闸**：两卡由编排者验收后直接续入对应 Lean 首件；首件绿 + 卡更新前不量产。两车道主仓 tracked/`.lake` 只读、零新增公理；SORRIED 48 / AXIOM 585 不变。下一条：续1576（A/L3 派单回执见 §1 与 `a0586c13`）；再下一条续1575。
- **2026-11-26（B on wt1 落库 `7b0ae9bd`：221 生成模块移出 tracked；我独立 221/221 逐字节复现；验收自检修复并 PASS；续1575）**：
  ① **落库**：221 个 `W1DC_*.lean` `git rm --cached`（65,404,398 B / 777,090 行；工作区保留、olean 不失效）；
  新增 `lean/scripts/wt1emit/{boxes221.json, gen_m9.py, dcrep.py, node_table.py, mk_l1.py, gen_all.py,
  manifest.sha256, README.md}` + `check_wt1_generated.py` + `Makefile` 的 `gen-wt1`/`check-wt1` +
  `.gitignore`。干净 checkout 必须先 `make gen-wt1`。
  ② **我独立复现（不是引用车道快照）**：从 `3dd1d16c` 的 `git archive` 树打 patch、**删空 221 个文件**、
  `gen_all.py` 重发 → **221/221 与 HEAD 逐字节相同**（`diff` 0 行；65,404,398 B / 777,090 行），
  生成 17.4 s；二跑 `up-to-date=221 written=0`。`mismatch=0`（生成器对 manifest 硬校验）。
  ③ **闸**：`make check-wt1` OK；`make gen-wt1` 幂等（mtime 保留）；`git check-ignore` 221/221，
  6 个负控（`W1DC15873`/`W1DCBridge`/`W1DCTermPilot`/`W1DCAssemblyFinal`/`W1aFJet`/`DCKit`）不误伤；
  `make acceptance-check` **PASS**（修了 pre-existing census pin：wt1 闭合后 repo/cone 各 −1，
  43422/499→**43421/498**；`nliCell3QZECFICwt1` 入 `EXEMPT_STALE_SORRIED`；`acceptance-check`
  依赖 `gen-wt1`，覆盖干净 checkout）；根面 **589 = 585 native + 标准三 + sorryAx**，
  与 L1 审计规范化逐名同（我亲跑，`/tmp/orch-b-verify/root_audit_after_b.log`）。
  ④ **B 车道抽样链**：6 箱 × 8 条 axioms 全标准三；9 case + final 标准三（4.83–15.77 s）；
  `Assembly` 岛 olean 12,764,936 B sha `a98361d8…` 与 `.lake` 现值同；0 error。
  ⑤ **三本账（B 车道实测）**：① box-module tracked 65,404,398 → **242,908 B = 0.147×**；
  ② wt1 tracked 总账 → **4,558,615 B = 2.754×**；③ 章程字面（tracked + 构建期生成）→
  **69,963,013 B = 42.27×**（几乎不变）。**D1/D2/D4/D5/D6 不变；wt1 `OVER-BAND` 判词不动。**
  B 是体积/可审计性净收益，不是 parity 修复。
  ⑥ 未做全 221 重编（字节相同、现有 oleans 有效；全量 13,445.6 s CPU / 单车道 ≈3.7 h）。
  下一条：续1574。
- **2026-11-26（L3 探针卡 + B 口径注记收线：D5 判据钉死、D3 cover 地板 2.21×、B 三本账；UNRESOLVED D5；续1574）**：
  ① **卡落库**：`~/c17_backup/lane_snapshots/parity-l3-b-prep-w1/{PARITY_CARD_wt1_l3_probe.md,
  PARITY_NOTE_wt1_b_refactor.md, EVIDENCE.md, SHA256SUMS}`（`l3-probe-v1`；零 Lean；主仓零改动）。
  ② **D5 判据（主判据 `r = t_full / 9.661 s` = HOL 2,135.001/221）**：≤1.5×（≤14.49 s）GO；
  1.5–2×（14.49–19.32）带条件；>2× NO-GO；并报 `t/49.64`、`t/60.29`、`221t/2,135`。
  **M1 值通道 6–9 s 是陷阱**（不含 part 12.66 s，会假绿）；**只有 M2 全量可做 GO**，
  EST **12–26 s = 1.3–2.7×**；E1 复用 21.5–25.5 s（2.2–2.6×，NO-GO）、E2 共享 12.2–17.3
  （1.26–1.79×，唯一进带假设）、S3p 物化 part 15.7–19.7（1.63–2.04×，兜底）。
  **part 通道 12.66 s 是唯一大头。**
  ③ **D3 关键发现**：证书层 S1（端点 154.5 B/箱）**0.44–0.48× PARITY**；S3p 2.36–2.41×；
  S3 3.62–3.67×。**整 wt1 因 cover/装配 3,654,359 B 有 ≥2.21× 地板 ⇒ L3 单独不可能让整 wt1
  D3 ≤2×**（不重构 cover）；1.5–2.5× 带 = per-box 数据 11–18 KB。
  ④ **D4**：S1 50–120 KB/箱 = 1.13–2.71× 自身下界；**终端 `dcSlack` 不通用化 ⇒ +400 KB/箱 ≥8×**
  （`PD_terminal.olean` 400,352 B）；checker 一次性 0.5–3 MB。D2：S1 端点若可行 = 1.0–1.2× 下界，
  可闭合 L1 卡 UNRESOLVED #3；S3p/S3 仍 32–53×。
  ⑤ **B 口径注记（三本账）**：① box-module tracked 65,404,398 → **248,324 B = 0.15×**；
  ② wt1 tracked 总账 69,719,108 → **4,456,468 B = 2.69×**；③ 章程字面（tracked+构建期生成）
  69,719,108 → **69,860,866 B = 42.20×（几乎不变）**。**不得只报 0.15×**；B 不改 D1/D2/D4/D5/D6，
  wt1 `OVER-BAND` 判词不动。生成物 221/221 逐字节同（B 车道在飞快照；落库后重验 olean sha 221/221）。
  ⑥ **两处我的口径勘误**：(a) 派单写「tracked source 69,058,757 → 0.2–0.3 MB」——69,058,757 含
  cover/装配 3,654,359，B 不覆盖；0.2–0.3 MB 只对应账①；(b) 我此前「每箱 314 `_mem` / 16 `by decide`」
  是 `_mem :` / `:= by decide` 的窄计数；卡按声明/全部 `decide` 计为 329/98，属计数口径差。
  ⑦ SORRIED 48 / AXIOM 585 不变。下一步：B 落库后派 A 的 M2 1 箱探针（等用户指令）。下一条：续1573。
- **2026-11-26（QITNPEA 单表+反射最小样品：链条成立；D1 0.081×、D5 0.14×；D3 逐波 2.11×/家族 0.73× 待裁决；两处卡 ERRATA + 探针 V6 误判纠正；续1573）**：
  ① **样品绿（我亲跑复核）**：`qitnpea-table-probe-w1`（快照 34 文件 + `SHA256SUMS` + `ORCH_ERRATA.md`；
  主仓零改动）；四文件 1,095 行 / **53,753 B**；`cornerLB_two`（两角点 γ4 下界）标准三；
  `checkRows_decide`（一次内核判定覆盖两行表）= `[propext]`；`rowComp_sound`（行反射，任意行）标准三。
  我亲跑 `scripts/build.sh` **RC=0 / 0 error**，axioms 逐条一致（`logs/orch_build_rerun.log`）。
  ② **两处设计级卡 ERRATA**：(a) **`ℚ` 内核不可归约**（`Rat.blt` 卡死）⇒ 表/包络必须建在
  `Kepler.Interval.Dyadic`（`⟨m:ℤ,e:ℤ⟩`）；(b) **atan 已落库**：`Kepler.Interval.arctanI`
  （`Interval/Trans.lean:1251`，sound `:1274`）是全域、纯 `Int`、内核可归约的包络；U2 的真缺口只有
  sqrt 尾数，已用燃料 `isqrt`（`T1_core.lean:47-104`）+ `Dyadic.sqrtI` 闭（soundness 借 `sqrtI_sound`，
  isqrt 只负责完备性）。
  ③ **六维实测回填**：D1 **3/37 = 0.081×**（卡 0.46×）；D3 **53,753 B**：逐波 2.11×
  （超 2× 线 5.5%）、家族 0.73×（13 债共享同一 kit）；D4 **1.77 MB**（STRUCTURAL-DIFF 不变）；
  D5 **4.9 s/角点（N=40）⇒ 456 角点 ≈ 37 min/债**（卡「5–20 s」低约 100×；vs HOL 15,490 s =
  **0.14×**，仍 PARITY；N=10 约 25 min/债）；D6 PARITY（零新公理/零 `native_decide`）。
  ④ **凹性腿**：二阶导闭式**已落库**（`Gamma4Concave.lean:130…361` 六条、`ZTGJoint0000DihSecond.lean:95-140`
  六条、`Gamma4DerivSecond.lean` 六条），无 `ConcaveOn γ4`；`Gamma4Concave` 头注自记 ∂²γ4 两项
  O(3) 相消到 O(0.03) ⇒ 值层证书目标，正是本 kit 可复用处（11 片 `ConcaveOn` 仍待证）。
  **卡 ERRATA #1 的「无二阶导资产」作废。**
  ⑤ **我纠正探针一处误判**：探针称 `Gamma4Val.olean` 陈旧不可加载、把 π/mm1/mm2 括号做成假设。
  亲测 `import Kepler.Text.Gamma4Val` **RC=0**，`g4v_pi_bounds_d8`/`g4v_mm1_bounds`/`g4v_mm2_bounds`
  均标准三 ⇒ 三条假设可由 import 直接消去（探针 V6 与 `Gamma4ValP` 改名重建作废；
  `logs/orch_g4bracket_probe.log`）。
  ⑥ **待用户裁决**：D3 口径——**逐波 2.11×（OVER-BAND，超 5.5%）vs 家族 0.73×（PARITY）**；
  机械缩减已定位（`rowComp_sound` 展开式 + `solSumI_mem`/`dSumI_mem` 的 List 形，约 3–8 KB
  ⇒ 乐观 45 KB = 1.8×）。**第一波仍缺 V4 的 11 片 `ConcaveOn`，不是「样品绿即 −3」**；
  13 条债里 11 条 γ4-基可用此机，两条 γ3 债例外。
  ⑦ SORRIED 48 / AXIOM 585 不变；样品未落主仓。下一条：续1572。
- **2026-11-26（L1 PARITY CARD 回填：OVER-BAND（D5 6.30×，用户明批 B）；两处数字 ERRATA；Final 根面重编闭环；续1571）**：
  ① **卡片落库**：`~/c17_backup/lane_snapshots/holparity-wt1-l1-backfill-w1/PARITY_CARD_wt1_value_L1.md`
  （`value-L1-v1`，基线 `fe1ec17f`；+ EVIDENCE/SHA256SUMS）。六维：D1 `PARITY` 0.357×；
  D2 `STRUCTURAL-DIFF`（每箱命名内容 8,144 B vs 可重算下界 154.5 B = 52.7×；旧 33,265 B/215×）；
  D3 机制层 `PARITY` 0.40× / 章程字面 `OVER-BAND` 42.1×（旧 88.4×）；D4 `STRUCTURAL-DIFF`
  不达自身下界（3,632,744 B/箱 vs 44–440 KB ⇒ 8.3–81.9×）；D5 `OVER-BAND` **6.30×**；
  D6 `PARITY`（1,768 + 11 审计点全标准三）。**判词 = OVER-BAND，用户明批 B 仅覆盖本次替换。**
  ② **数字复核（与续1570 对表）**：13,445.6 s（0.1 s 舍入）；6.2977×；单车道 5.1384×；
  墙 77.07 min = 2.166×；221 箱 olean 802,836,336 B（均 3,632,744；含组装 808,972,600 B，−43.27%）。
  ③ **ERRATA-1（我的）**：行数不是 `~782k/−48%`——那是「每箱均值×221」投影；落库 221 件精确
  **777,090 行 / 65,404,398 B ⇒ −50.68% 行 / −53.94% 字节**。
  ④ **ERRATA-2（我的，动作）**：续1570 ②「10 个组装模块 + Assembly + `Final` 全部重编」里的
  Final 实为 `W1DCAssemblyFinal`；`Kepler/Final.olean` 未重编（mtime 11-23）。**已闭环**：
  08:26 岛协议重编 `Kepler/Final.lean`（RC=0 / 6.17 s / 8.32 GB / olean 129,912 B）→ 回灌
  `.lake`（sha256 `12c60f2f…`）→ 重跑根面探针 = **589（585 native + 标准三 + sorryAx）**，
  与 08:11 输出**规范化后逐名相同**（旧日志省略 `Kepler.` 前缀，纯 pretty-printer 显示差异）。
  证据：`~/c17_backup/lane_snapshots/wt1-l1-close-w1/{final_compile.log,root_audit.log,rootface_min.lean}`。
  ⑤ **证据缺口（非数字错）**：C 车道 raw 重发射 `cmp` 的 `raw/` 目录未入快照（报告称 73/73）；
  分析车道独立复算 prefix §0–§2b、terminal §5、4 根事实陈述均 **221/221** 相同 ⇒ 结论不受影响。
  ⑥ **单调性**：四计费维（D5/D4/D3/D2）全改善；**唯一转差 = 峰值 RSS 均值 +2.2%**
  （5.948→6.077 GiB，整树 `part` 中间项更大），按 §7.3 记录上报，不改变 D5 判定与护栏。
  ⑦ **杠杆结论**：①（字面量操作数）不推荐——只买 D5 且把 D2/D4 打回；②（声明面瘦身）唯一四维
  同向但叠加 ① 后仍 2.1–2.9× >2× ⇒ **wt1 不再投入**；未来只在复用同一证书单位的 bank 上先做
  1 箱探针（3–5 天 + 重编；须先出卡、用户明批）。
  ⑧ 在飞：QITNPEA 单表最小样品探针。SORRIED 48 / AXIOM 585 不变。下一条：续1570。
- **2026-11-26（L1 形态落库 `fe1ec17f`：221/221 绿；D5 18.28×→6.30×；续1570）**：
  ① **三车道 L1 重发射全绿**：A 74/74（55.10–62.85 s，olean 3.415–4.819 MB，行 3,040–3,641）+
  B 74/74（58.3–67.3 s，3.54–3.77 MB）+ C 73/73（56.99–62.76 s，3.16–3.84 MB）；
  每箱 8 条 axioms 全标准三、0 error/0 sorryAx；`gen_m9.py` sha256 三车道一致 `05e5f9bd…`，
  `mk_l1.py` 原样 `ba30fc7a…`。**raw 重发射与落库文件逐字节相同**（A 74/74、C 73/73 实测）⇒ L1 是纯形态替换。
  ② **落库 `fe1ec17f`**：221 个模块替换为 L1（813,189 deletions + 14,651 insertions；删 957 条/箱
  逐节点 `ev_/p_/op_`，整树 `rfl`）；10 个组装模块 + `Assembly`（岛协议 41.02 s / 9.48 GB / 0 error /
  olean 12,764,936 B）+ `Final` 全部重编；根面 **589 = 585 native + 标准三 + sorryAx 不变**；
  `nliCell3QZECFICwt1` 仍标准三。
  ③ **实测回填（重要，订正预估值）**：总编译 **13,445.5 s CPU**（A 4,480.1 + B 4,520.3 + C 4,445.1）
  ⇒ vs HOL 2,135.001 s = **6.30×**（单车道投影 10,970 s = 5.14×；三车道并行让单箱 49.6→61 s）；
  墙 3 车道并行 ≈77 min ⇒ **2.16×** HOL 单进程。olean 均 ~3.6 MB/箱（合计 ~796 MB，−44%）；
  行数 ~782k（−48%）。**D5 仍 OVER-BAND（6.30×），用户已明批 B；D4 仍超自身可实现下界
  （3.6 MB vs 77.5–440 KB/箱，8–46×）。**
  ④ 机制勘误入册 **PR-66**：bash `$PPID` 是启动快照，循环里的 `[ "$PPID" = 1 ]` 在 reparent 后
  不触发；逐轮孤儿自检必须 `ps -o ppid= -p $$`。另：`python3 -I` 不把脚本目录加入 sys.path，
  `gen_m9.py` 需用 `runpy` + 显式插入生成器目录。
  ⑤ 下一步：PARITY CARD 回填 L1 实测（分析车道）+ **QITNPEA 单表最小样品探针**
  （1 片凹性 + 2 角点 + 可计算 dyadic atan 包络，验证 456→3 表、D1 0.46×/D3 1.9×）。
  SORRIED 48 / AXIOM 585 不变（wt1 已关闭，形态替换不改债务）。下一条：续1569。
