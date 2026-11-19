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

**当前实测 = 基线 AQ @`e4c384e6`（2026-11-18，`nliTskXLLIPLS` 真证）**：

- cone `K_REACH 2,108,657` / **SORRIED 51** / **`K_AXIOM 585`**；
  MODULES 12,140 / UNIVERSE 2,140,793 / COVERAGE 98.4989%；
  口径 II 39,125 / 51 / 585 / 49,868。
- **SORRIED 51 = Assembly 51（50 `nli*` + 1 hLP）+ Text 0**。
  50 `nli*` = 38 `nliRest*` + 4 `nliTsk*` + 4 `nliCell3*` + 4 直挂
  （`nliKcblrqcIneqDef` / `nliLpIneqs` / `nliMainNonlinearTerminalV11` / `nliOx3q1h`）。
- 根面 **589 = 585 native + 标准三 + `sorryAx`**；基座 585 未动。
- **运行态事故（2026-11-19，`lp-packed-single-leaf-w2`）**：主仓
  `lean/.lake/build/lib/lean/Kepler/LP/` 有 **969 个自指符号链接**（193 `.olean`、194 `.ilean`、
  194 `.trace`、388 `.hash`），由 farm 父目录穿透后 `ln -sfn` 误替换；`W6Align/` 幸存。
  **1,150 个 tracked LP 源文件无损、主仓 tracked 无改动**；但根面/Assembly/Final 验收在
  LP 池恢复前不可复跑。上述基线仍是最后实测，不表示当前构建池可用。修复须另批，
  禁止擅自 `lake build` 全量重建。事故报告在车道快照 `INCIDENT.md`。
- 仪器原样：[`e2e-reachability-map.tsv`](e2e-reachability-map.tsv)（12,795 行）；
  历史基线叙事：[`e2e-reachability-map.md`](e2e-reachability-map.md)。

核心阅读：[`hf-proof-map.md`](hf-proof-map.md)（证明主线）、
[`nli-campaign.md`](nli-campaign.md)（nli 数学路线与负结果）、
[`handoff-2026-11-18.md`](handoff-2026-11-18.md)（复现命令、易失池、快照索引）。

---

## 0. 当前里程碑

| 里程碑 | 当前状态 | 下一步 |
|---|---|---|
| M0 / 根面与可达图 | **基线 AQ**：SORRIED 51 / AXIOM 585 | 所有落库后重跑仪器；数字只在本文件头和地图维护 |
| M1a / Text 清债 | **完成：Text 0** | 不重开旧 Text 战役；历史矩阵见 §2.1d |
| M1b / 接口 | hTC 0；**hNL 50 + hLP 1** | 主攻 nli 数学压缩；LP 独立处理 |
| M2 / 信任基座 | 585 定格；manifest 数据源/生成器钉定已完成 | 抽样 replay、Docker 一键复现与最终公理断言，重算窗口另批 |
| M3 / 北极限 | **51 = 50 `nli*` + 1 hLP** | 先数学归约与复用，再证剩余计算核心；不以生成行数作为进展 |

### 0.1 剩余债务边界

- **hNL**：50 条。逐条路线和已证负结果以 [`nli-campaign.md`](nli-campaign.md) 为准；
  当前新侦察集中在二阶代数凹性、同盒联合包络、Bernstein 后端。
- **hLP**：`lpArchiveCertificatesDebt`，待证 42,889 条 bound 叶（189 infeasible 已闭）。
  **现有 bound 叶已经使用 `Y/D` 对偶向量 + `checkDualCMTF` 弱对偶检查 + `by decide`**；
  后续应审数据表示、内核归约和 olean 成本，不是重新发明 dual checker。
- `nliLpIneqs` 与 `nliKcblrqcIneqDef` 属 LP-gated 债，不能指望 γ4 路线顺带关闭。

---

## 1. 在飞

**当前授权在飞 3 条（`ztg-bernstein-pilot-w1` / `iyou-sharpv2-slots-w1` / `cell3-wt1-build-w1`）；`nli-plan-cards-w1` 与 `cell3-wt1-scout-w1` 均已收线入档。** cell3 与 Bernstein 试点已双双收线 GO 并落库（`ebd11b13` / `9a4a9dc6`）；A 已超时记暂缓、不自动 resume；D 已收线。另：**LP 池恢复三链并行中**（编排者后台计算，非车道：A/B 主力死链 + C 补漏被删件；真受损面修正 = 193 死链 + 9 被删文件，~930 个 Pilot/RandShard 碎片源经核实从未入池、排除）；链尾自动接 e2e 树可视化重建。QITNPEA1 共享下界、taum 数学侦察与其它暂缓资产不自动续发。
证明车道的主仓 tracked 零改动；所有 Lean 编译统一经 `/tmp/lean_global_lock.d` 原子锁串行，锁内执行压力/RSS 护栏。车道快照在 `~/c17_backup/lane_snapshots/<lane>/`。

| 车道 | 回执 | 唯一目标与止损 |
|---|---|---|
| `ztg-bernstein-pilot-w1` | 编排者会话后台 agent，running（用户批「可以启动」） | ①剪枝胶水两条 Lean 化（x1 方向 729 / x4 方向 162 差分常数，deriv⇒monotone，消费 Gamma4Deriv 闭式）——接通 BernsteinLeaf0011 剪枝面叶到**原始盒**义务；② q=64/25 三债 1,215 系数**首张根叶定标**（预算 ≤5 min / ≤10 GB）；只做一张不量产；~1 天止损，量产等批 |
| `iyou-sharpv2-slots-w1` | 编排者会话后台 agent，running（用户批「启动」） | 真证 `nliTskIYOUOBFsharpv2`（Assembly.lean:946）目标 **SORRIED −1**：四轴单调降维（min ∂ +0.13110）+ 2 维三块（edge 线性桥 +1.358e-5 最紧主风险 / strip ∂y4 ≥ +0.15 / 上方 30–80 叶小证书走已生效 Rule P）；产出 Text 新文件 ~2.5–4.7k 行 + Assembly 1 import 1 body；3–5 天，结构点 2 轮卡死即交班 |
| `cell3-wt1-build-w1` | 编排者会话后台 agent，running（用户批「Wt1 启动吧」） | 照 §9.2 执行卡 v2 施工路线 A「折点+单调面」：NliBanks21 显式核+归约 → 两导数引理（精确/区间收口，[sampled] 证据不许直接当证书）→ 底面 1D 两段 → 折点单点有理证书（余量 1.4e-6）→ K2 上界小件 → Assembly 接线；目标 **SORRIED −1**；3–5 天；导数引理 3 轮卡死转路线 B 无导数 cell |
| `cell3-wt1-scout-w1` | **已收线（见下）** | — |
| `nli-plan-cards-w1` | **已收线（见下）** | — |

**cell3-wt1-scout-w1 已收线（2026-11-19，~1 h）：wt1 路线成立（高置信，区间级）——执行卡升级为「可启动」。** **全域 D 正性已由 iv B&B 全证**（两折点片 92.6k evals/180 s 零未决叶，不依赖采样）；y5/y6 全盒严格单调增 60 dps 成立（min ∂ = **+0.0030472209238**，比 wt2A 被推翻结论肥 36 倍；结构性原因：wt1 的 m5/m6 系数 `lfun(y5/2) ∈ [0.1087,1]` 永不过零）；数值极小 **+4.5143350968e-5** 在 h0cut 折点 (2.52,2,2)（census 数值对、**位置错**——其内点 2.534 是抛光停在折点右平台）；折点是**单点有理证书**（y4=63/25、δ=8184078/390625 全有理，余量 1.4e-6）。路线 A「折点+单调面」~800–1500 行/3–5 车道日（唯一真风险 = 两个 3D 导数引理现证据 [sampled]，3 轮卡死转路线 B 无导数 cell 兜底）；**nb20 勘误一条**（0.06468 是 K2 下界方向，wt1 需补 `K2 < 0.06472` 上界小件，Fraction 已证组合系数全盒非正）。卡已合入 nli-campaign §9.2。交付在快照 `cell3-wt1-scout-w1/`。

**nli-plan-cards-w1 已收线（2026-11-19）：nli-campaign §9 逐债执行卡补全至 51 债全覆盖（50 nli + hLP），patch 已应用入档。** §9 由 ~90 行扩到 585 行：9.0 名词速查（普通话术语表）+ 9.1–9.4 全部执行卡 + 9.5 覆盖对账表（51 行逐名，与 DEBTS.tsv / 地图 SORRIED 段双向差集为空、25 个 commit 锚核实存在）。机器自检零缺失；**5 处数据源矛盾如实标注未擅裁**（FHBa/v2a 的 DEBTS 农场口径已被 η 曲线+凹性路线取代、RIBCYXU 析取支数 8 vs 7 以 Lean 陈述为准、Kcblrqc 无 LP 合取项编号、ZTG/fat1 余量两源并存）；「待侦察」卡 3 组（ZTG joint 6 / cell3 wt1 / WKGUESBsym）。交付与审计在 `~/c17_backup/lane_snapshots/nli-plan-cards-w1/`。

**cell3-wt2a-core-w2 已收线（2026-11-19）：GO——机器层修通 + 代表 cell00 端到端 + 52 cell 成本外推，落库 `ebd11b13`。** `NliBanks20.lean` 1,576 行：WIP 19 处错全消（含 `dlt_anti_b/c` 恒等式按真族重写、`lfun` 无 ite 勘正）；通用 `w2a_cell` + `cell00_core`（margin +1.2e-3）+ `bank_wt2A_of_cell00` 真实消费 `NliBanks19.bank_QZECFICwt2A_of_core`；探针 10/10 恰标准三。52 剩余实 cell ≈ 11,130 行 / 编译 9–26 min（结构同构，生成器 ~300 行 python）——**量产与 Assembly 接线等用户批**，执行卡入 `nli-campaign.md` §9.1；新雷 PR-43（linarith 语法原子化）入册。交付在 `~/c17_backup/lane_snapshots/cell3-wt2a-core-w2/`。

**Bernstein 表示试点已收线（2026-11-19）：GO——81 系数叶以 peel 表示过内核，落库 `9a4a9dc6`。** `ztgG_leaf_0_0_1_1`（ZTG q=36/25 根盒多项式正性义务剪枝面形）直编 RC=0/14.9 s，4 公理面亲验恰标准三；peel 表示 = 手写 `peel2` 二次剥皮 ×4 层 + 40 小 ring 恒等式 + 81 闭式 norm_num 折叠，零 MvPolynomial/Finsupp/Quot/decide。**诚实边界**：剪枝面形（x1/x4 钉两次单调剪枝端点，剪枝本身未形式化，胶水两条在快照 DELIVERY §4）；**1,215 系数根叶定标与 ZTG 量产未批不做**。交付与审计在 `~/c17_backup/lane_snapshots/bernstein-kernel-representation-w1/`。

**A fat1 G 正性已超时暂缓（2026-11-19，`fat1-g-positivity-w1`）：WIP 已抢救，不判死、不自动 resume。** 最新 2,975 行源与 patch 的 2,955 行旧版不同；原样独立编译 RC=1（unterminated comment），隔离闭合 14 处章节注释后仍有 82 个 `error:`，没有可接受证明或公理面。Δ 中心展开、小区与逐组 Taylor/checkPos 设计保留为数学资产；约 3,000 行生成整件及旧 patch 不接收入库。fresh 重启须用户另批，先小组件与简洁化。详见 `nli-campaign.md` §1.26 与快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**D packed-w2 已收线（2026-11-19）：b2 单叶 bounded GO，独立两轮验收通过。** 从 A0 重生成候选并逐字节比对；cs/b/certY 字段等价均无公理、六输出逐字节相同、Count=5,565/5,565。独立 wall/A0=1.062659/1.048097，合并均值比 1.055329；olean=395,784 B（约49.0×），最大 RSS=8.254 GB。目标源不在主仓，无可落 patch，不车队化、不改 D 层。LP 构建池事故另见文件头与 §3，恢复未批、未执行；详见快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**A fat1 精确 G3 已收线（2026-11-19，`fat1-g3-exact-w1`）：通用交错 Taylor 引理与 G3 S39 独立验收通过。** 205 行 patch **已落库 `248fde92`**（2026-11-19 封账批：编排者重编 RC=0 + 3 公理面亲验标准三）；m=1 展开与负系数消费探针亦通过。G3 的 Hermite 锚不再是 arctan 上界义务，但 G 正性、方向链、覆盖、bank 与 Assembly 未闭合；G2(bB+) 未通过车道的 m≤9 筛选，不传播“全组 m=9”。详见 `nli-campaign.md` §1.25 与快照审计。

**B 联合包络已收线（2026-11-19，`joint-envelope-extension-scout-w1`）：两处判词经独立审计勘误。** 原 R2 把 QITNPEA1_1_1 的分母误写为 2，实际为 3，故 γ4≥23/2000 不能服务它；修正后的同一并盒候选只数值覆盖在案 1_0、1_2(fat1)、2_0。#147 只否定独立 `d-range + A_min` 服务算法，不是任意联合平面的结构否证。编排者复跑并盒估计与精确算术；仍零 Lean、零减债。详见 `nli-campaign.md` §1.23 与快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**C TerminalV11 压缩已收线（2026-11-19，`terminal11-family-compression-w1`）：组织性资产，带三处口径勘误。** parse/assign/cluster 独立重跑与交付逐字节一致；五个模板实际覆盖 80 支，另 5 支独立；置换检查只覆盖 74 条带 tree 的显式 def，35 条 hex 未测；REDUCTIONS 的 ly 第二等式写错，evalfun 与 Lean 一致。模板仍含未实现的超越核工序，不是证明 GO，不进入 85 支发射。详见 `nli-campaign.md` §1.24 与快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**fat1-w2 已超时暂缓（2026-11-19，`nli-algebraize-fat1-w2`）：修复账推进，bank 未闭合。** T5/T7 独立编译 RC=0（4.17 s / 5.53 GB）且标准三；r2 分组与系数勘误复核成立。G3 非 s_hi 错误（两脚本均 D≤Dmid），而是精确锚失败、1e-6 有理锚后 minA≈+1.4e−15，故只属数值临界通过，形式化仍未做。r5 朴素 enclosure 6001 叶后两半仍负，判该具体路线不可行；一阶 Taylor 叶仅估计。主仓未落库，SORRIED 51 不变。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**TXQTPVC 析取探针已收线（2026-11-19，`disjunction-lp-scout-w1`）：常数非负权重 NO-GO（具体路线）。** 编排者绕过 subset/mu 版本错配，按 dual.log 三点以 60 dps 独立复算：`E_μ[f]` 最小分量 +0.001271705>0，μ 非负且三者在现行与较宽 hminus 档内均在 Lean 盒中，故任意常数 `aᵢ≥0` 必有一个证人点使组合为正。h0cut 单分片亦数值失败；这不否定析取命题或其它证明路线，SORRIED 51 不变。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**packed 单叶已收线（2026-11-19，`lp-packed-single-leaf-w1`）：原 A2 拒收；编排者修复版 UNRESOLVED。** 原 A2 的 cs 被生成器错误删除所有负系数，虽 olean 仅 363 KB 也不能接受。独立修复解析后，cs/b/certY 全部由内核 `decide` 证等，六声明输出与 A0 一致，olean **406,304 B（约 47.8×）**；但两轮平均 wall/A0 ≈ **1.42×**，超过预注册 1.30×，故不是全项 GO。原 patch 草案目标不在主仓，apply-check 失败；修复版也未车队化。审计与修复源在快照 `ORCHESTRATOR_CHECK/`。

**FHB g3pos-w2（2026-11-18）：Phase 1 阶段完成，整体暂缓（可重启）。** 2 h timeout 发生在最终文档落盘前，快照无 DELIVERY，但有 patch/Evidence/完整日志。旧 WIP 不是单纯慢：r0 有截断、根值、精确等式、命名实参与 D 因子错位；修复后 v2 端点真证。编排者隔离应用 patch 并逐字节比对源，独立重编 RC=0（263.35 s / 6.90 GB），消费探针 RC=0（3.37 s / 5.55 GB），`g3c_endpoint_gamma4` 与 consumption 均标准三。尾部仅有数值单调性 GO，内部/G2/N3D/m3m4m5 未闭，故端点 ≠ 曲线 ≠ g3pos ≠ FHBa；曲线+端点两文件**已落库 `20ee1cd5`**（2026-11-19 封账批，curve 头注虚假声称已勘正），义务仍未闭合，SORRIED 51 不变。定案在快照 `ORCHESTRATOR_NOTE.md`。

**cell3 wt2A 核暂缓（2026-11-18，`cell3-wt2a-core-w1`）：2 h 超时，可重启，未判路线不可行。** 快照原只有 START，编排者已从 /tmp 抢救完整 WIP。最终数值设计为 62 cell（9 vacuous、53 实 cell），超过原 12-cell 目标；`NliBanks20.lean` 886 行仍以 RC=1 结束，master/核/bank/Assembly patch 均未完成。Probe20 已由编排者从快照源独立复跑 RC=0（3.30 s / 5.56 GB），`matan_le_one`、`sol_euler4_eq`、`dih4_eq` 标准三；这只证明三个小引理，机器层和核仍未闭合。重启入口 = fresh 从 WIP 先修机器层 + 一个代表 cell，若不能显著降 cell/行数则继续暂缓；不自动续跑、SORRIED 51 不变。详见快照 `ORCHESTRATOR_NOTE.md`。

**LP 表示审计已收线（2026-11-18，`lp-dual-representation-audit-w1`）：阶段完成；后续 `lp-packed-single-leaf-w1` 已于 22:56 获批发车，见 §1 在飞表。** 编排者复跑统计与源占比一致；137,780 B→19,380,352 B 是闭合试点叶，Text 骨架叶是另一对象。CALIB 直接记录 Data 19.33 MB / Assembly 0.07 MB，支持数据字面量占约 99.6%；term/VM 分解和 packed 4–10× 仍是推断。A/B Phase 0 原建议新增 250 条 sorry，违反硬规则，已改为 `trivial` 闭合对照 + 复用现有骨架，禁止执行原探针。零 Lean、未改 LP/D 层、SORRIED 51 不变。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**代数化单债探针已收线（2026-11-18，`nli-algebraize-fat1-scout-w1`）：条件 GO（数值），但原 Hermite 清单不可直接量产。** 编排者复跑确认分母 2、余量约 0.03496919、两半 ρ≈0.12456/0.13908、8 区域。新增两个修复闸：① G4 左区 24/15625 点的 t̂<0，T5 局部方向反（最大约 2e−14，合成账未失真），须符号感知；② 少数 t̂ 超出原 Hermite 锚区间，按 t̂ 重锚后 8 组中 7 组恢复，bB+ G3 仍失败（−5.15e−5），须加切或换界。后续 `nli-algebraize-fat1-w2` 已于 22:56 获批发车，须先修误差账；探针本身零 Lean、零 patch、SORRIED 51 不变。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

**FHB g3pos 暂缓（2026-11-18，`fhb-g3pos-w1`）：2 h 超时，UNRESOLVED；本次执行暂停但可重启，未判路线不可行。** 端点后台编译被终止，快照无 DELIVERY/patch；约 801 行端点生成证明与数值区间未获编译验收。105 行 `FhbG3posCurve.lean` 的四个真实声明由编排者经岛协议独立编译 RC=0（3.42 s / 5.72 GB）、导入探针 RC=0（3.23 s / 5.55 GB），公理面均标准三；文件头声称的 `g3c_curve_gamma4_ge` 实际不存在。数值诊断提示 V/S/D 极值不对齐造成约 0.01–0.013 装配松弛，尾段需凹性 + 端点，但内部区域、G2/N3D 与 m3/m4/m5 均未闭合，SORRIED 51 不变。定案见快照 `ORCHESTRATOR_NOTE.md`。

**FHB floor 已收线（2026-11-18，`fhb-floor-mono-w1`）：UNRESOLVED，m3/m4/m5 均未证明。** 独立高精度复算给出 B0 内非单调反例：∂γ4/∂y4≈−0.09314667568151，∂γ4/∂y3、∂y5≈−0.05788818698070；自适应微分与中心差分约 15 位一致，撤销 seam 侦察的“三轴一阶导全盒为正”。这不是 Lean 形式反证；车道闭式端口在同点虽同号但数值不一致，不得再拿它作定量互证。交付的 166 行 `FhbFloorMono.lean` 只证“纤维凹性 + 端点比较 ⇒ m3/m4/m5”；编排者独立编译 RC=0（3.74 s / 5.58 GB）、五个公理面标准三，消费真实 `FhbEtaCurve.fhb_hba_of_floor3` 的岛探针 RC=0（3.21 s）且标准三。H1 凹性、H2 端点与 g3pos 仍未闭合；`FhbFloorMono.lean` **已落库 `032857d0`**（2026-11-19 封账批），SORRIED 51 不变。日志在快照 `ORCHESTRATOR_CHECK/`。

**只读数学调研已收线（2026-11-18，`nli-math-research-w1`）：候选已登记 §2.4，仅代数化单债探针于 19:22 获批发车，其余未发车。** 原版确证局部单调/凸性 glue、共享二阶导界、非负组合消析取与 Bernstein 代数化先例。编排者复核 Hales 回顾、Revision §5、IneqAgent 论文及公开源码后修正其强结论：IneqAgent 的公开 Flyspeck Bernstein 件走显式 `node + positivity + ring`，并非我们卡住的 `MvPolynomial/Finsupp + decide`；它提供另一种证明项形状，也同时带来大表达式/生成代码，不能称为已解决本仓表示问题。覆盖 35–40 债、1–2k 行、加速倍数均为未验证估计，见 `nli-campaign.md` §1.16。

**cell3 wt 已收线（2026-11-18，`cell3-wt-math-w1`）：UNRESOLVED，wt2A 核与 wt1 均未证明。** 新文件 `NliBanks19.lean`（288 行）真证 wt2A 的显式核、η²/Δ 双向归约及 `bank_QZECFICwt2A_of_core`；编排者独立编译 RC=0（5.70 s / 5.78 GB）、八公理面标准三，真实 bank 类型消费岛探针 RC=0（3.20 s）且标准三。核义务仍是三维 `Δ≥0 ⇒ 0<w2aF`；1 cell 正下界与 8–12 cell 方案均为数值估计，不是 Lean 证书。独立 60 dps 复算在 `(2.4635,2.5156,2)` 得 ∂w2aF/∂y5≈−8.4182758e−5（三档步长一致），撤销旧“wt2A y5 全盒严格增”；wt1 未动笔。`NliBanks19.lean` **已落库 `431fb92a`**（2026-11-19 封账批；`cell3-wt2a-core-w2` 重启车道的接续入口），SORRIED 51 不变。日志在快照 `ORCHESTRATOR_CHECK/`。

**Bernstein kernel 暂缓（2026-11-18，`bernstein-kernel-pilot-w1`）：UNRESOLVED，未获得合格小叶；原表示路线不优先，但不是永久判死。** 设计 A 的 MvPolynomial `DecidableEq` 不可归约有实证；设计 B' 通用核曾在 `bk13` 单次 RC=0，但当前 WIP 又有 exponent/Finsupp 错误与 heartbeat 超时。81 系数叶仍卡 Quot/Finsupp/Eq.rec 的 decide 归约与指数类型，1,215 根叶未开始，故不存在完整 wall/RSS/olean/axioms 定标。原跑与续跑均撞 2 h 超时，按长上下文/多轮暂缓；最新 WIP、日志和 `ORCHESTRATOR_NOTE.md` 已同步快照。以后出现更合适的表示或性价比证据时可由用户明批 fresh 重启。不得把 Python GO 或 bk13 单次 RC=0 写成 Lean pilot GO。

**Hessian Lean 已收线（2026-11-18，`g4-hessian-lean-w1`）：UNRESOLVED，整盒量化未闭合。** W5 `Gamma4ConcaveBridge.lean` 与 W1 全部 6 条对角 `dihXf_hasDerivAt2_x{i}_x{i}` 已真证；编排者独立编译 RC=0（2.23 s / 5.05 s）、8 个检查公理面标准三，岛协议消费探针通过。**整盒单调性/逐坐标凹性/张量三路均否证或不可行**；独立复算插值 `∂²Q/∂y2²` 精确网格 12 非正、4 正，故 B0 母定理不得按原凹性方案发车。另发现 Scout lmfun 权重 factor-2 错误；修正后复跑两片凹性与 ZTG 失败见证仍成立，旧数值作废。交付与独立验收在 `~/c17_backup/lane_snapshots/g4-hessian-lean-w1/`；两文件**已落库 `b9134d34`**（2026-11-19 封账批）。

**FHB 新 pilot 已收线（2026-11-18，`fhb-seam-curve-w1`）：UNRESOLVED，未真实 −1。** 405 行 `FhbEtaCurve.lean` 证明 η126 二次边界、显式根式曲线及三个归约接口；编排者从快照源独立编译 RC=0（约 9 s / 5.8 GB）、11 个公理面标准三，岛协议消费探针通过。剩余义务 = m3/m4/m5 地板比较（原一阶单调方案已见数值反例）+ 3-D guard 正性（N3D、7 边界片、1-D 曲线 `γ4≥7e−3`）；v2a 未启动。交付与独立验收日志在 `~/c17_backup/lane_snapshots/fhb-seam-curve-w1/`；`FhbEtaCurve.lean` **已落库 `8848b526`**（2026-11-19 封账批）。

此前 A/B/C 均已交付并收线，未移动 SORRIED。

**A 已收线（2026-11-18，`g4-hessian-scout-w1`）**：**GO（有条件）**。dihXf 全部 36 个二阶偏导有 atan-free 闭式，商公式与 Lean 一阶闭式精确一致。**后续 factor-2 勘误**：Scout 的 lmfun 权重两处减半，旧 N/D 数值作废；修正装配复跑后，B0 易切片 y1 两片凹性（新 max 约 −4.39e102/−2.04e91）与 ZTG `0_1_0_0` 失败见证仍成立。W5/W1 已由后续 Lean 车道真证，但整盒基坐标量化被证伪；γ3/taum 独立压力测试和证书成本仍未解决。交付在 `~/c17_backup/lane_snapshots/g4-hessian-scout-w1/`，修正证据在 `g4-hessian-lean-w1/`。

**B 已收线（2026-11-18，`b0-joint-envelope-w1`）**：联合包络 **GO（数值侦察，非形式证明）**。五主债由 L1/L3/L5 三张共享支撑面覆盖，Q581/Q565 被纯有理支配；FHBb 主支全盒为正。上述六债共享 96 角点 / 60 对称轨道，最小均在 `(2.52,2⁵)`。FHBa/v2a 的 η 守卫不可由二维包络分离，且 `max(g,c−η²)` 非凹，**不得套 96 角点表**，改走两条一维 η 边界曲线 + 8 个单调性符号；其中 floor 三轴的一阶单调性已有数值反例，该部分旧方案作废。旧 audit 的 sharp 余量勘误为 **+4.813e−3 / +1.104e−3**。交付在 `~/c17_backup/lane_snapshots/b0-joint-envelope-w1/`；全局最小均为 ESTIMATE，待 A 的凹性与曲线证书。

**C 已收线（2026-11-18，`bernstein-representative-w1`）**：多项式义务 **GO（仍待真实 Lean 单叶定标）**；超越函数“整盒有理界 + 单分数组合” **NO-GO**；全 37 债通用引擎灰区偏 NO-GO。ZTG 四债均为根盒 1 叶，q=64/25 三债各 1,215 系数 / 57,142 B，q=36/25 经两次单调剪枝为 81 系数 / 2,488 B；BIX 代表节点的 √ 整盒误差 5.944（约为 slack 的 2,662 倍），单分数组合达 126,607,131 系数。交付在 `~/c17_backup/lane_snapshots/bernstein-representative-w1/`。

判停共识：

- A：公式持续爆炸或三轮仍无紧凑符号证书 ⇒ NO-GO，不硬凑。
- B：需几十个支撑面、包络吃掉余量或退化为八套独立证书 ⇒ NO-GO。
- C：≤10³ 叶且数据可控为 GO；10³–10⁴ 为灰区；>10⁴ 或次数/字节爆炸为 NO-GO。
- 任何通知先按 `AGENTS.md` §7.1-22/24 核查快照与活性，不因 completed/failed 通知直接接管或归档。

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
| `qitnpea1-shared-floor-w1` | **等用户裁决**：研究并盒 γ4≥23/2000 的短证书，及分离 1_1 后的二盒/分段常数面 | 先数学归约与代表小片，不承包全家族、不直接生成农场；可能绕开 fat1 atan/G3，但实际形式化成本未知 |
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
- IXPOTPA 最新实测为自相似阶梯、全 TRUNC，维持 BLOCKED，旧 0.59 CPU·h 不再采用。
- Bernstein 仍有值域外包；`sqrt/atan` 需要有理逼近和误差账，不能直接当多项式。
- LP bound 叶已经是 weak-dual certificate；不得把“新增 dual checker”当成新收益。

详细证据与逐条债表：[`nli-campaign.md`](nli-campaign.md) 与
`~/c17_backup/lane_snapshots/farm-ops-w1/FARM_PLAN.md` / `DEBTS.tsv`。

---

## 5–7. 文档、归档与维护规则

- 现役数字只在本文件头维护；其它文档引用，不另抄一份。
- 当前战略讨论稿：[`../strategy/nil-math-20261118-glm53.md`](../strategy/nil-math-20261118-glm53.md)。
  其中 Bernstein/LP 的强度判断按 §4 的澄清使用，不视为实测结论。
- 2026-11-18 重组前全文：[`archive/priority-queue-2026-11-18-pre-nli-math.md`](archive/priority-queue-2026-11-18-pre-nli-math.md)。
- 更早队列/战术/J 战役表：[`archive/priority-queue-legacy-2026-10.md`](archive/priority-queue-legacy-2026-10.md)。
- 续990–1242 全文见 2026-11-18 重组前快照；续306–989 见
  [`history/changelog-archive-2.md`](history/changelog-archive-2.md)，续1–344 见
  [`history/changelog-archive.md`](history/changelog-archive.md)。
- 历史只搬不删；旧数字需要纠正时加 ERRATA，不覆写历史原文。
- §8 只保留最近窗口；超出后机械迁入历史/快照，保持当前队列可读。

---

## 8. 变更日志（新 → 旧）

- **2026-11-19（14:53 实测，续1286）**：**iyou 车道首程收线（结构性交付、未达 −1）+ 全场槽位饿死事故与处置。**
  ① `iyou-sharpv2-slots-w1` 首程：**全案源树完成**（60 文件/35,150 行，复刻层全验证：落库 XLLIPLS 叶 lb 20 位逐位一致、43/43 sqrt 证书 bit-exact、990 检查零失败）但**编译 0 分钟**——未获槽位，按 §7 纪律不作完成声明。**两条工单路线实测证伪**（烧内核前抓住）：hmono 全盒解析粗界合计 −0.27<0（真值 +0.131 只对真值成立）、底边线性下桥余量 1.8e-11；**替代路线已建好**：六导数 TM-hull 证书（atan-free）+ 角区塌缩到已证 `gamma4_at_sqrt8` + 复用 `TskXLLIPLSAtan1Expr`；合计 536 叶/内核估 3.5–4.5 h（XLLIPLS 先例的 8%）。§9.1 iyou 卡的路线数字待内核波收线后一并勘误。
  ② **槽位饿死事故**：LP 链 C 的 `CertPilot204880136538`（830 KB/8.2 GB RSS 大件）以 22.9% CPU 磨 72+ min 把 pressure 顶到 2；护栏设计缺陷（等待者**先取槽后过 guard**、三槽被不推进的等待者占满）⇒ LP 双链 23 min 零推进、iyou 全程饿死。**处置**：杀大件（改排终局链夜间重编）→ 压力回落 1、3 lean 恢复流动；**终局链 `lp_finale.sh` 已挂**（等 A/B/C 排干 → 重试散件 → 全量 olean 核对 → 导出器 + tree.db 重建）；**PR-46 入册**（guard 先行过闸再取槽；脚本改造须等静默窗口，PR-44 约束）。
  ③ iyou 车道已 resume 跑剩余波次（Phase-1→Base→Close→58 模块内核波→Slots），按替代路线收口。在飞 3 条（ztg / iyou / wt1 施工）。SORRIED 51 / AXIOM 585 不变。下一条：续1287。

- **2026-11-19（14:50 实测，续1285）**：**`cell3-wt1-build-w1` 发车（用户批「Wt1 启动吧」）：照执行卡 v2 施工，目标 SORRIED −1。**
  ① 路线 A「折点+单调面」~800–1500 行/3–5 车道日：NliBanks21 显式核+`bank_QZECFICwt1_of_core` 归约 → `∂w1aF/∂y5、∂y6 ≥ 0` 两引理（**侦察证据 [sampled]，施工必须精确/区间收口**）→ 底面 1D 两段 → 折点单点有理证书（4.50e-5 目标、余量 1.4e-6）→ K2 上界小件（nb20 勘误方向）→ Assembly 1 import 1 body。
  ② ②引理 3 轮卡死转路线 B 无导数 cell（SE 槽必须 `nb20_matan_ge_taylor` 下界）。在飞现 3 条（ztg 试点 / iyou / wt1 施工）；**两条 −1 车道同时在飞（iyou + wt1），双双落地即 51→49**。SORRIED 51 / AXIOM 585 不变。下一条：续1286。

- **2026-11-19（14:28 实测，续1284）**：**`cell3-wt1-scout-w1` 收线（~1 h，远低于 1 天预算）：wt1 路线成立（区间级），§9.2 执行卡升级为「可启动」。**
  ① 关键数字：全域 D 正性 iv B&B 全证（零未决叶、不依赖采样）；y5/y6 单调 min ∂ **+0.0030472209238**（60 dps 多档一致；求值器以 12 位复现 wt2A 反例作标定）；极小 **+4.5143350968e-5** @ h0cut 折点 (2.52,2,2)（census 数值对、位置错）；折点单点全有理（δ=8184078/390625，证书余量 1.4e-6）。
  ② 路线 A「折点+单调面」~800–1500 行/3–5 天（推荐；真风险 = ∂/∂y5、∂/∂y6 两引理现证据 [sampled]）；路线 B 无导数 cell 兜底（~10²–10³ cell，性价比弱于 A）。与 wt2A 差异清单 + K2 上界小件一条已写入卡。
  ③ **nb20 勘误**：0.06468 为 K2 下界方向；wt1 施工需补 `K2 < 0.06472` 上界括号件（不影响已落库 wt2A 件本身）。
  ④ 侦察实际用 ~1 h（预算 1 天）；全部数字带 [interval]/[exact-point]/[sampled] 标注；卡已合入 §9.2（合入时编排者一度弄乱卡片头两行，当场修复）。wt1 **施工未批不做**；在飞剩 ztg 试点 / iyou 两条。下一条：续1285。

- **2026-11-19（13:26 实测，续1283）**：**cell3 wt1 精确重测侦察发车（用户批「按你建议来」）；LP 恢复范围修正入档；两处日志时间戳勘误。**
  ① `cell3-wt1-scout-w1` 发车：旧 census 对 wt1 的「y5/y6 严格单调增、极小 +4.514e-5」为采样结论（wt2A 同款结论已被精确复算推翻），本车道零 Lean 用区间/精确方法重测全部符号断言 + 照 NliBanks19 范式起草核显式化 + 升级 §9.2 执行卡；~1 天止损。**后续排定（用户同批批准）**：ZTG joint 6 侦察在 `ztg-bernstein-pilot-w1` 收线后立刻发（一次比完角点/分段与 Bernstein 化两路线）；WKGUESBsym 挂起等农场裁决捎带。
  ② **LP 恢复范围修正**：真受损面 = 193 个自指死链（链 A/B 修复中）**+ 9 个被事故直接删除的文件**（`Cert`/`ColMajor`/`CertHello` 族 7 件 + `W6Align`/`W6AlignRoots`，补漏链 C 按依赖序修复）；全量扫描出的 ~930 个 Pilot/RandShard/PilotCM 碎片源经核实**从未入池**（LP 段全 88 MB、无 import 者单件 16–21 MB），排除恢复范围。`T161847242261t1208` 的 FAIL 为假警报（olean 25.9 MB 实已编出，包装脚本死于 PR-44 mid-flight 重读）；链 A 因 failed.txt 非空将跳过自动可视化步，该步由编排者在三链收线后**手动执行**（全量 olean 核对 → 导出器 → tree.db 重建）。
  ③ **ERRATA（本文件两处时间戳）**：续1281 标「13:20」实际 ≈12:56、续1282 标「14:05」实际 ≈13:05（写时为估算未打 `date`）。教训入册 PR-45：**账本时间戳必须来自实测 `date`，不许估值**。
  ④ SORRIED 51 / AXIOM 585 不变。下一条：续1284。

- **2026-11-19（14:05，续1282）**：**`nli-plan-cards-w1` 收线入档——nli-campaign §9 逐债执行卡 51 债全覆盖，patch 应用落库。**
  ① 覆盖 = 50 `nli*` + 1 hLP 零缺失（9.5 对账表 51 行逐名，与 DEBTS.tsv / 地图 SORRIED 双向差集空；族分解复算吻合；25 commit 锚核实存在；`Assembly.lean` 行号与 DEBTS 逐行一致）。
  ② §9 由 ~90 行扩到 585 行：9.0 普通话名词速查 + 9.1–9.4 全部执行卡 + 9.5 对账表；单 hunk 只动 §9（§1–8 逐字节不动）；今日变化同步（wt2A 补 `ebd11b13` 锚、ZTG 试点在飞、iyou 在飞）。
  ③ **5 处数据源矛盾如实标注未擅裁**（FHBa/v2a DEBTS 农场口径已过时 / RIBCYXU 支数 8 vs 7 以 Lean 为准 / Kcblrqc 无 LP 项编号 / ZTG·fat1 余量两源并存）；「待侦察」卡 3 组（ZTG joint 6 / cell3 wt1 / WKGUESBsym）；DEBTS.tsv 待按新口径刷新（另批）。
  ④ 编排者验收：apply-check PASS、单 hunk 范围核查、9.0/9.5 抽查通过；零 Lean；SORRIED 51 / AXIOM 585 不变。在飞剩 2 条（ztg 试点 / iyou）。下一条：续1283。

- **2026-11-19（13:20，续1281）**：**用户连批三单，三条异步发车并登记 running 回执，当前授权在飞 3 条。**
  ① `ztg-bernstein-pilot-w1`（用户批「可以启动」）：剪枝胶水两条 + q=64/25 首张 1,215 系数根叶定标，~1 天有界试点；成功 ⇒ ZTG 解耦 4 债的量产包就绪（其余三叶 + `ztg_of_main` 接线 ⇒ −4），量产另行报批。
  ② `iyou-sharpv2-slots-w1`（用户批「启动」）：真证 `nliTskIYOUOBFsharpv2` 目标 **−1**——四轴单调降维 + 2 维三块（edge 线性桥 / strip / 上方 30–80 叶小证书），产出 Text 新文件 ~2.5–4.7k 行 + Assembly 接线；3–5 车道日。
  ③ `nli-plan-cards-w1`（用户批「启动」）：零 Lean 纯文档，nli-campaign §9 逐债执行卡补全至 50 nli + hLP 全覆盖（普通话行文，五要素），产出 docs patch 由编排者应用。
  三条均主仓 tracked 零改动、3 槽信号量护栏内（LP 双链恢复同刻并行，共享 ≤3 并发）；派发时无卡死。SORRIED 51 / AXIOM 585 不变。下一条：续1282。

- **2026-11-19（12:45，续1280）**：**双 GO 日收官：Bernstein 表示试点与 cell3 wt2A 核双双收线 GO 并落库；编译并发放宽（≤3）；LP 双链恢复中；AGENTS 雷区重组。**
  ① `bernstein-kernel-representation-w1` **GO**：81 系数叶以 peel 表示（IneqAgent 式 `node+positivity+ring` 变体，零 MvPolynomial/Finsupp/decide）过内核——`ztgG_leaf_0_0_1_1` 直编 RC=0/14.9 s，4 公理面亲验恰标准三；落库 `9a4a9dc6`。诚实边界 = 剪枝面形（两次单调剪枝未形式化）；**ZTG 解耦 4 的 Bernstein 路线解锁，执行卡入 nli-campaign §9.1（①胶水②根叶定标为有界试点，量产等批）**。
  ② `cell3-wt2a-core-w2` **GO**：`NliBanks20` 机器层修通 + `cell00_core` 代表 cell 端到端 + `bank_wt2A_of_cell00` 真实消费 NliBanks19 归约；探针 10/10 标准三；落库 `ebd11b13`。**52-cell 量产（≈11,130 行 + Assembly 接线）用户明示先不启动**，执行卡入 nli-campaign §9.1；新雷 PR-43 入册。
  ③ **编译并发放宽（用户裁定）**：AGENTS §4 由「同时只许 1 个 lean」改为 **≤3 并发 ∧ 总 RSS ≤24 GB ∧ pressure <2**（3 槽信号量 `/tmp/lean_slot{1..3}.d`；每车道仍 ≤1；禁裸多目标 lake build 不变）；LP 恢复随之改双链并行（A 正序/B 倒序，SKIP 去重），ETA 从 ~27.5 h 收窄至 **~17:30–18:30**；链尾自动 e2e 可视化重建。
  ④ Kimi 编排会话收尾入档 `363a2841`（续1279）。
  ⑤ **AGENTS 雷区重组（用户裁定 ≤20 条）**：§7.1 精简为现行 20 条（候选 37 exec-trap 直接入表为第 20 条，此后走登记册晋升规则不需逐条批）；全文/历史/散件入新档 `docs/pitfall-register.md`（PR-1..37 + handoff §6 五条升格 PR-38..42 + cell3 新雷 PR-43 + 编排者 mid-flight 脚本重写事故 PR-44 + playbook/车道散件索引）；`§7.1-N` 外部引用编号不变。
  ⑥ **nli-campaign 新设 §9 逐债执行计划登记**（用户裁定「启动即照做」）：cell3 wt2A 量产卡、ZTG Bernstein 三步卡、iyou/FHBa/ox3q1h/TerminalV11 3 MATH/LP 类等待批卡；hf-proof-map 状态更新五十一入档。
  ⑦ SORRIED 51 / AXIOM 585 不变；push 已获用户批（本批后执行）。下一条：续1281。

- **2026-11-19（10:42，续1279）**：**A fat1 G 正性超时暂缓，最新 WIP 已抢救并独立确认未通过；不自动 resume**。
  ① timed_out 后 wire 终止于 cancelled、无对应编译进程；DELIVERY/Evidence 均为草案。最新 2,975 行源已保存到快照 `ORCHESTRATOR_CHECK/`，patch 的 2,955 行版本不是最新。
  ② 原样独立编译 RC=1（18.55 s / 约 8.14 GB），末尾 unterminated comment；隔离闭合 14 处章节注释后仍 RC=1，含 82 个 `error:`，涉及解析、sqrt、盒成员和代数归约。没有 fat1_main 或 `#print axioms` 证据，旧 patch 不接收入库，接管按止损停止。
  ③ 保留 Δ 中心展开、bB− 小区、18→6 分组与逐组 Taylor/checkPos 设计为数学资产；数值包络不升级为证书。205 行通用交错 Taylor 引理已另件落库 `248fde92`，与本 WIP 分开。
  ④ 后续须用户另批 fresh 从快照，先小组件、发射器与简洁化，不直接重生成整件。当前授权在飞为另一会话 cell3/Bernstein；SORRIED 51 / AXIOM 585 不变，LP 池恢复仍独立待批。下一条：续1280。

- **2026-11-19（11:20，续1278）**：**封账批次收线：六件已验收 Lean 资产全部落库（6 commit），SORRIED 51 / AXIOM 585 不变。**
  ① 落库清单（每件流程：快照逐字节对表 → 岛协议直编 RC=0/0 err → 编排者亲跑 `#print axioms` 恰 `[propext, Classical.choice, Quot.sound]` → 一件一 commit）：
  `8848b526` FhbEtaCurve（405 行，4 公理面）；
  `b9134d34` Gamma4ConcaveBridge + Gamma4DerivSecond（44+476 行，8 公理面，atan-free 二阶闭式）；
  `032857d0` FhbFloorMono（166 行，`fhb_orchestrator_consume` 消费探针标准三）；
  `431fb92a` NliBanks19（288 行，bank 消费探针标准三；`cell3-wt2a-core-w2` 重启车道的接续入口）；
  `20ee1cd5` FhbG3posCurve + FhbG3posEndpoint（105+979 行，`g3c_endpoint_gamma4` 端点真证，重编 332 s，5 公理面；curve 头注虚假 `g3c_curve_gamma4_ge` 声称勘正后落库，仅注释改动）；
  `248fde92` NliQitnpea12ArctanSeries（205 行，交错 Taylor arctan 上界 FTC 证书，3 公理面）。
  全部纯新增 cone-neutral、无 Assembly 接线 ⇒ 根面结构性不变；Text 池 3 个 g3pos stale symlink（w2 验收遗物）已随落库换成真 olean；§1 各段「主仓未落库」已同步翻转。
  ② **exec-trap 遗锁事故与修复**（与续1277 的 LP 池事故相互独立）：fat1 车道 `compile_lean.sh` 以 `exec lean` 起编译 ⇒ EXIT trap 不存活，compile9/10 各遗留一把无主锁，全场编译楔死 2×约 20 min（compile5–8 空日志 = 各自 20 min lock timeout）。编排者 10:05 去 exec 修复 + `/tmp/fat1-g-positivity-w1/FIXES-APPLIED.md` 留档；两把 stale 锁按 §7.1-22 取证（无 lean 进程/无日志增长）后清除，bernstein 车道亦独立取证清锁一次（成因同源）。**「exec 起编译丢 trap」建议入 AGENTS §7.1 雷区表候选（37），待用户裁定。**
  ③ **AGENTS §7.1-36 与 handoff 运行态警示随本批入 git**（内容见续1277 ②③；LP 池恢复 = 193 个受损 olean 重编、非 bound 债重放，等用户裁决）；两新车道 `cell3-wt2a-core-w2` / `bernstein-kernel-representation-w1` 均已书面确认复制式 island + 禁 `ln -s` + 主仓 `.lake` 只读。
  ④ 本批零陈述改动、零删除、零新增 axiom/native_decide；与续1277（D packed-w2 bounded GO）互不覆盖。下一条：续1279。

- **2026-11-19（09:45，续1277）**：**D packed-w2 b2 单叶 bounded GO 独立验收通过；同时确认 LP 构建池事故，恢复待用户裁决**。
  ① 从 A0 重生成候选并逐字节比对；独立两轮 cs/b/certY 字段等价均无公理、六输出逐字节相同、Count=5,565/5,565。wall/A0=1.062659/1.048097，合并均值比 1.055329；olean=395,784 B，最大 RSS=8.254 GB。目标源不在主仓，无可落 patch，不车队化、不改 D 层。详见 `nli-campaign.md` §6.3 与快照 `ORCHESTRATOR_CHECK/AUDIT.md`。
  ② 独立清点 LP 自指链接，精确范围见文件头；193 个受损 olean 全部有 tracked 源（189 T* + 4 顶层），恢复不是重放 42,889 条 bound 债。未执行恢复、lake build 或根探针；当前根验收不可复跑，SORRIED 51 / AXIOM 585 只沿用最后实测基线。
  ③ 事故预防已加入 `AGENTS.md` §7.1-36，handoff 增加运行态警示；A farm 为真实目录，无同类穿透。空锁只在无 Lean/无对应脚本且长期不变时释放，有效 PID 锁不动。
  ④ 当前授权在飞为 A + 另一编排会话的 cell3/Bernstein（其状态原样保留）；LP 池恢复与串行重建方案等用户批准。下一条：续1278。

- **2026-11-19（09:55，续1276）**：**封账批次启动（用户批「封账 + 勘误 + cell3/Bernstein 两车道」）**。
  ① **本 commit 首次入 git**：pq 2026-11-18 重组正文、`archive/priority-queue-2026-11-18-pre-nli-math.md` 归档件、`history/nli-six-lanes-2026-11-18.md` 六车道总结、nli-campaign §1.10–§1.25 新增节、README 导航——此前全部悬在工作树。
  ② **strategy 提案入档**（`strategy/nil-math-20261118-glm53.md`）并追加 §11 实测勘误：LP dual 机制勘正（dual+decide 早就在用，真杠杆=打包/表示）、通用超越整盒 NO-GO（BIX √ 误差=slack 2,662×）、整盒凹性精确反例、采样≠证明、Python GO≠Lean GO；存活杠杆 = atan-free 二阶导 / 多项式 Bernstein（ZTG 根盒 1 叶）/ B0 联合包络。
  ③ **两车道发车**：`cell3-wt2a-core-w2`（WIP 重启：机器层 + 代表 cell + 成本外推）与 `bernstein-kernel-representation-w1`（81 系数叶新表示，2 h 止损）；均后台异步、全局锁串行，§1 在飞表已登记。
  ④ **落库批次开工（本日编排者亲做）**：六笔已验收资产逐笔「直编 RC=0 + 亲跑 #print axioms + 一笔一 commit」——FhbEtaCurve（405 行）、Gamma4ConcaveBridge + Gamma4DerivSecond、FhbFloorMono（166 行）、NliBanks19（288 行）、FhbG3posCurve + FhbG3posEndpoint（w2 patch，979 行端点已验）、NliQitnpea12ArctanSeries（fat1 G3，205 行 patch）。全部纯新增 cone-neutral、无 Assembly 接线，**SORRIED 51 / AXIOM 585 不变**；落库结果由后续封账日志记档。下一条：续1277。

- **2026-11-19（08:30，续1275）**：**用户批准 A/D，两条异步发车并登记 running 回执，当前授权在飞 2 条**。
  ① `fat1-g-positivity-w1`（agent-20 / agent-9torpddk）：消费已验交错 Taylor 界，只做一个代表小区的 G>0 与真实 IExpr/checkPos；逐组选阶，不默认展开39次，不重开 Hermite、上千叶、bank 或 Assembly。
  ② `lp-packed-single-leaf-w2`（agent-21 / agent-7ymi9di5）：fresh 从 w1 修复版起，最多两个优化臂；必须保留 cs/b/certY 字段级 decide 等价与六输出比较，最终候选两轮 wall/A0≤1.30×且语义/公理全合格才 GO，不车队化、不改 D 层、不做 LP 全量重放。
  ③ 两条均主仓 tracked 零改动、全局 Lean 锁串行、快照交付；QITNPEA1 共享下界、taum 数学侦察和其它暂缓资产不自动续发。派发时无 Lean 进程/锁；SORRIED 51 / AXIOM 585 不变。下一条：续1276。

- **2026-11-19（08:02，续1274）**：**A fat1 通用交错 Taylor 引理与 G3 S39 独立验收通过，局部数学进展，bank 未闭合**。
  ① completed 后 wire 停止、无对应进程，交付齐全。patch 双侧路径正确，主仓 apply-check PASS；隔离 apply 与快照 205 行源逐字节一致，主仓未应用。
  ② 独立重编 RC=0、原文件零 error/warning（4.46 s / 最大 RSS 约 5.55 GB），三条 `#print axioms` 恰标准三；另补 m=1 七次展开与负系数反向放缩，两个消费声明亦标准三。通用上界对全部 t≤0 成立，arctan 层不再依赖 Hermite 锚。
  ③ 四个数值脚本独立复跑一致：g3_compare 的 b 变体误选与 n=4 网格 min G≈0.0798 均复现，仍非全盒证书。Hermite 仅记本路线弃用，不写普遍 NO-GO；G2(bB+) 未通过 m≤9 筛选，其它组逐组选阶。
  ④ G 正性、方向链、slab/Δ、覆盖、bank 与 Assembly 未闭合，patch 未落库；SORRIED 51 / AXIOM 585 不变，当前授权在飞 0。`fat1-g-positivity-w1` 与 `qitnpea1-shared-floor-w1` 均登记待裁决，不自动发车。下一条：续1275。

- **2026-11-19（07:42，续1273）**：**C TerminalV11 家族压缩收线为组织性资产，独立复跑一致，三处口径勘误**。
  ① completed 后 wire 停止、无对应进程，交付齐全；编排者从存档输入重跑 parse/assign/cluster，parsed109、FAMILIES、cluster 输出逐字节一致，109 唯一 ID 与 85/21/3 路由计数成立。
  ② FAMILIES 实际 10 个 FARM 标签；五模板覆盖 80 支，K6 两支与 K7/K10/K11 各一支共 5 支独立，不能称 85→5 完整覆盖。置换脚本只测 74 条带 tree 的显式 def，35 hex 未测；REDUCTIONS 的 ly 第二等式错误，正确 `(2.52−y)/0.52`，evalfun 与 Lean 一致。
  ③ 完整 probe 未重跑，数值全部 ESTIMATE；模板中的超越核/退化带仍未实现，70% 发射估计不预支。不是证明 GO，不自动进入第二阶段，SORRIED 51 / AXIOM 585 不变。详见 `nli-campaign.md` §1.24 与快照审计。下一条：续1274。

- **2026-11-19（07:41，续1272）**：**B 联合包络收线，独立复核纠正 QITNPEA1 分母与 #147 否证范围**。
  ① completed 后 wire 停止、无对应进程，快照交付齐全。独立复跑并盒估计、精确服务算术与 #147 服务公式；所有全局极值仍为 ESTIMATE，局部 iv 不是全盒证书。
  ② QITNPEA1_1_1 的分母为 3 而非 2，γ4≥23/2000 对它精确服务余量 −0.0056，原“一面闭 1_0/1_1/2_0”拒收。修正后若并盒下界真证，可服务在案 1_0、1_2(fat1)、2_0，不覆盖 1_1，不记 −3。
  ③ #147 只否定独立 `d-range + A_min` 服务算法，不否定相关联合平面或原命题。`qitnpea1-shared-floor-w1` 登记等用户裁决，未自动发车；主仓零 Lean/patch，SORRIED 51 / AXIOM 585 不变。详见 `nli-campaign.md` §1.23 与快照审计。下一条：续1273。

- **2026-11-19（07:00，续1271）**：**用户批准 A/B/C，三条异步发车并登记 running 回执，当前授权在飞 3 条**。
  ① `fat1-g3-exact-w1`（agent-17 / agent-bab1awe5）：fresh 从 fat1-w2 修复账接续，只做有理锚、真实 t̂ enclosure 与 G3 的精确数学/代表小引理；1e−15 数值临界不当证书，精确账不过即暂缓，不扩 Taylor 叶、bank 或 Assembly。
  ② `joint-envelope-extension-scout-w1`（agent-18 / agent-6vso05yu）：零 Lean，最多 2–3 个非重复代表盒，检验 `(dihY,γ4)` 共享分片下包络；不得继承整盒凹性，每盒 >4 面或余量耗尽即记该设计不经济，不预支跨债覆盖。
  ③ `terminal11-family-compression-w1`（agent-19 / agent-dbo5wsxr）：零 Lean，消费现有 109 支 census，最多研究 2–3 个 hex/atan 代表族的精确共享归约与人工模板；不重复 census、不批量发射、不承诺部分证明减顶层 SORRIED。
  ④ 三条均主仓 tracked 零改动、快照交付；timeout=暂缓、不判死。派发时无 Lean 进程/锁；SORRIED 51 / AXIOM 585 不变。下一条：续1272。

- **2026-11-19（01:05，续1270）**：**fat1-w2 超时暂缓；Taylor/分组/系数资产验收通过，G3 仅数值临界，bank 未闭合**。
  ① timed_out 后无 agent-14/Lean 进程，快照有 DELIVERY/REPAIRED_LEDGER 与数据。独立编译 T5/T7 RC=0（4.17 s / 5.53 GB）且标准三；r2 复核残差≤5.4e−61，直接 dih 系数与常数项与 Lean 展开一致，scout 多加 C_SOL 属保守高估。
  ② **ERRATA（w2 对 s_hi 的归因）**：scout m12 与编排者 audit 都是 `D<=Dmid`，没有 `D<=m1` 转录错。G3 在精确锚下 −5.15e−5，外扩至 1e-6 有理锚后 minA=+1.4021e−15，故真正差异是有理锚；该数值处于临界，不能当 Lean 证书。
  ③ r5 朴素 enclosure 6001 叶后 bB- −0.56024、bB+ −0.50489，具体路线 NO-GO；一阶 Taylor 叶 10³–10⁴ 仅估计，未实现。bank/接线未闭合，SORRIED 51 / AXIOM 585 不变，当前授权在飞 0。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。下一条：续1271。

- **2026-11-19（00:13，续1269）**：**TXQTPVC 常数权重 NO-GO，三点 Farkas 证人独立复核成立**。
  ① completed 后 wire 停止、无 agent-15 进程，快照交付齐全、零 Lean。直接复跑 verify_points 时发现 subset.npy=156 与 mu.npy=138 版本错配，不能用其输出判案。
  ② 编排者改用 dual.log 的实际三点与 μ，以 60 dps 重算：E_μ[f] 最小分量 +0.001271705>0，μ 非负；三点在 nb17 与较宽 hminus 档内均满足 Lean 盒。故任意常数 aᵢ≥0 必有证人点使 Σaᵢfᵢ>0，常数非负组合路线精确排除。
  ③ h0cut 单分片亦数值失败；命题为真仍只是 ESTIMATE，常数权重失败不否定其它路线。SORRIED 51 / AXIOM 585 不变。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。下一条：续1270。

- **2026-11-19（00:13，续1268）**：**packed 原 A2 因负系数漏失拒收；编排者修复版语义/olean 合格但 wall 未过预注册门槛**。
  ① 独立重编基座/A0/A2：原 A2 olean 363,208 B、六声明输出与 A0 相同，但字段级内核检查证明 cs 为假、b/certY 为真。根因是生成器不接受 `(i,(-c))` 的嵌套括号，系统性删掉所有负系数，故原 53× 结果拒收。
  ② 独立修复互斥括号解析：cs/b/certY 全部由 `decide` 证等，六声明输出与 A0 相同。修复版 olean **406,304 B（约 47.8×）**；两轮 wall/A0 比值均约 **1.42×**，超过 1.30×，所以只记 UNRESOLVED，需优化或用户另批，不车队化。
  ③ 原始 cs 由 Lean 计数 5,565 项，与元数据 3202 nnz 不一致，外推不得按 3202 直接估算；旧 account_leaf_source.py 同类括号统计亦不可靠。patch 草案目标不在主仓、apply-check 失败。审计与修复源在快照 `ORCHESTRATOR_CHECK/`。下一条：续1269。

- **2026-11-18（22:56，续1267）**：**用户批准 A/B/C 三条，全部异步发车并登记 running 回执**。
  ① `nli-algebraize-fat1-w2`（agent-14 / agent-qofow3f2）：先修 G4 跨零和实际 t̂ 锚区间，bB+ G3 未闭不得写 Lean；全绿后单区 pilot→bank，优先保持 8 区，单文件约 450 行/三轮暂缓。
  ② `disjunction-lp-scout-w1`（agent-15 / agent-rq8kaesb）：零 Lean TXQTPVC 六支非负组合，fᵢ<0 方向按 PackingAuto21:485-493 钉定，交付显式权重/对偶证据；不装依赖、最多一种简单分片诊断，不做通用引擎。
  ③ `lp-packed-single-leaf-w1`（agent-16 / agent-7ukkflzu）：先做 ByteArray/Nat 小探针与 A0，再≤2主臂；olean≤50%、wall≤1.3×且公理/陈述全等才建议生成器改造，禁新 sorry、禁车队化和 LP 全量重放。
  ④ 三条均主仓 tracked 零改动、统一全局 Lean 锁；其它暂缓资产不自动续发。当前授权在飞 3 条。下一条：续1268。

- **2026-11-18（22:43，续1266）**：**g3pos-w2 Phase 1 端点真证独立验收；cell3 Probe20 亦独立验收；两车道整体暂缓，当前授权在飞 0**。
  ① g3pos-w2 超时发生在最终 DELIVERY 前，但快照 patch/Evidence/日志齐全。编排者隔离 apply patch 并逐字节比对曲线与端点源，独立重编 RC=0（263.35 s / 6.90 GB）；消费探针 RC=0（3.37 s / 5.55 GB），`g3c_endpoint_gamma4` 与 consumption 均标准三。旧 WIP 的系统性错误已修复，证明 timeout 不能单独判死或判 GO。
  ② 端点只证明 `y1=2hplus` 一点；Phase 2 单调尾部仅数值 GO（F'≤−0.2488），未形式化。内部/G2/N3D/m3m4m5 未闭，端点不等于曲线/g3pos/FHBa，主仓未落库，SORRIED 51 / AXIOM 585 不变。整体暂缓，可 fresh 从端点续，不自动发车。
  ③ cell3 Probe20 从快照源独立复跑 RC=0（3.30 s / 5.56 GB），`matan_le_one`/`sol_euler4_eq`/`dih4_eq` 标准三；NliBanks20 机器层与 wt2A 核仍未闭合，62-cell 分层路线仍为可重启暂缓。
  ④ 两份快照 `ORCHESTRATOR_NOTE.md` 与日志均已更新；不预支任何顶层减债。下一条：续1267。

- **2026-11-18（21:28，续1265）**：**cell3-wt2a-core-w1 两小时超时，记暂缓（可重启）；/tmp WIP 已抢救，未判路线不可行**。
  ① timed_out 后 turn cancelled、无 cell3 编译进程；当前锁属于 g3pos-w2。快照原只有 START，编排者已把 island 源、数值脚本、日志完整补入快照 `WIP/`。无 DELIVERY/patch，SORRIED 51 / AXIOM 585 不变。
  ② 最终数值设计 62 cell（9 vacuous、53 实 cell），超过原 12-cell 目标；886 行 `NliBanks20.lean` 的 `nb20_machinery.log` RC=1，仍有 rewrite/defeq/导数/单调性/lfun 错误，master、三维核、bank 消费与 Assembly patch 均未完成，不得写成接近闭合。
  ③ Probe20 车道日志 RC=0（4.43 s / 5.71 GB），`matan_le_one`/`sol_euler4_eq`/`dih4_eq` 标准三；编排者尚未在锁内重跑，暂只记车道证据。
  ④ 按用户指正后的口径记 **暂缓（可重启）**：fresh 从 WIP 先修机器层 + 一个代表 cell，若不能显著降 cell/行数则继续暂缓；不自动续跑、不做大规模 auto-gen。详见快照 `ORCHESTRATOR_NOTE.md`。下一条：续1266。

- **2026-11-18（21:09，续1264）**：**LP 表示审计阶段完成；单叶 A/B 登记 GO 但未发车，违规 sorry 探针已修正**。
  ① completed 后 wire 超 1 min 无增长、无 agent-13 进程，快照交付完整、零 Lean。编排者复跑两个统计脚本一致：137,780 B Bench 是闭合试点叶，Text 骨架 174 模块回归约 19,161 B/定理，两口径不得混用。
  ② CALIB/Evidence 直接记录 Bench.olean 19,380,352 B、生产形 Data+Assembly 19.33+0.07 MB，支持数据字面量约 99.6%；当前这些 /tmp olean 已不在池，故标历史实测。term/VM 分解、Expr 节点成本、packed 4–10× 和 0.83 TB 外推不冒充新验收。
  ③ **硬规则修正**：原 A/B Phase 0 新增 250 条 sorry 即使在 /tmp 也禁止；改 `trivial` 闭合对照 + 复用现有骨架。单叶 A/B 本身 GO，ByteArray/Nat 解码与 wall/RSS/olean 未测，车队级重构条件待命，不自动发车、不改 LP/D 层。
  ④ 审计与复跑在快照 `ORCHESTRATOR_CHECK/`；SORRIED 51 / AXIOM 585 不变，当前在飞 cell3-wt2a-core-w1 与 fhb-g3pos-w2。下一条：续1265。

- **2026-11-18（20:47，续1263）**：**代数化探针收线为条件 GO（数值）；编排者复跑一致，并补出两个正式接口修复闸**。
  ① completed 后 wire 超 1 min 无增长、无 agent-11 进程，快照交付完整、零 Lean/patch。独立复跑 m1/m12(n=5) 与交付一致：主支 γ4/2>0.0057、m≈0.03496919、两半 ρ≈0.12456/0.13908、8 区域。
  ② **G4 跨零**：24/15625 点 t̂<0，T5 局部反向最大约 1.98e−14，合成仍正；负侧 T7 实为上界（交付候选表方向表述需修正），正式引理须符号感知。
  ③ **Hermite 锚区间**：原脚本用真实 t 区间，少数 t̂ 出界使局部上界失败（最差 −7.93e−7）；按 t̂ 重锚后 7/8 组恢复，bB+ G3 仍 −5.15e−5，须加切/换界，直接 T7 左端误差约 0.0111 不是免费修复。
  ④ 裁决仍为条件 GO（路线值得保留），但原 DELIVERY §7 清单不得直接量产；w2 未批，须先交修复账。审计与复跑日志在快照 `ORCHESTRATOR_CHECK/`。SORRIED 51 / AXIOM 585 不变，当前在飞 3 条。下一条：续1264。

- **2026-11-18（20:33，续1262）**：**用户批准 A/D，两条异步发车；旧 Bernstein 无头 Leaf64 先按暂缓决定停止并备份**。
  ① `fhb-g3pos-w2`（agent-12 / agent-nzqwi4dv）：fresh 从 w1 WIP 接续，先原样验收约 801 行端点（建议 30 min 观察窗），全绿后才试一个尾部凹性区间；每阶段可重启，不承包 FHBa，不把 timeout 判死。
  ② `lp-dual-representation-audit-w1`（agent-13 / agent-hqh6b733）：零 Lean 成本归因，先实测源/olean 尺寸，做 bound/infeasible/Pilot 对照并给单叶 A/B 设计；不改 LP/D 证书层，不预设缩小倍数。
  ③ 派发前发现旧 Bernstein agent-3 又占锁约 14 min 编译 1,215 系数 Leaf64；已按既定暂缓决定终止进程链、备份最新 WIP 并释放锁。这不改变未来用户明批 fresh 重启的资格。当前授权在飞 4 条。下一条：续1263。

- **2026-11-18（20:22，续1261）**：**用户指正 timeout 状态口径：统一改为“暂缓（可重启）”，不得默认判死**。
  ① `UNRESOLVED` 只表示目标未闭合；timeout 只表示本次时间/资源预算耗尽，不能区分“算法慢”与“路线不通”，因此不得写成 NO-GO。
  ② 不自动 resume 仅是防重复执行、无头运行与资源冲突；保存 WIP 后，未来出现新证据或合适性价比时可由用户明批 fresh 重启。NO-GO 仅用于有明确反例、可信结构否证或信任冲突的具体路线，且不外推为定理假或其它路线不可行。
  ③ `fhb-g3pos-w1` 改为暂缓：曲线核心已验收，端点未验收不是数学判死；后续可评估端点验收/压缩再续。`bernstein-kernel-pilot-w1` 同样改为暂缓：当前 Quot/Finsupp 表示降优先，但可由新表示 fresh 重启。两份快照 ORCHESTRATOR_NOTE 均已追加 ERRATA，`nli-campaign.md` §7 新增统一原则。此次只改状态口径，未启动任何车道。下一条：续1262。

- **2026-11-18（20:03，续1260）**：**g3pos 两小时超时收线；曲线代数核心独立验收通过；旧 Bernstein 无头活动再次止损**。
  ① `fhb-g3pos-w1` 的 turn 已 cancelled、端点后台编译已 killed，快照无 DELIVERY/patch；不机械 resume。105 行曲线件四声明经岛协议独立编译 RC=0（3.42 s / 5.72 GB）、探针 RC=0（3.23 s / 5.55 GB），全标准三。约 801 行端点生成件无编译合格证据，g3pos/FHBa 均未闭，SORRIED 51 / AXIOM 585 不变；定案在快照 `ORCHESTRATOR_NOTE.md`。
  ② g3 的 stale lock（mtime=1795002667）在确认无 g3/Lean 进程后清除。首次核心独立编译因缺 FhbEtaCurve 岛路径失败，改 symlink farm 后通过，不把路径错误记为证明失败。
  ③ **headless 警报**：已止损的 Bernstein agent-3 仍推进到 turn 48–49。编排者把 WIP 备份到快照 `HEADLESS_2026-11-18/`、追加 ORCHESTRATOR_NOTE 并终止旧等待链；其后无头手动 leaf36F 仍 RC=1（recursion depth、mod_cast 类型、whnf heartbeat）；turn 50 又擅自启动 leaf36G，主会话 TaskStop 不适用，已按核实 PID 终止其父/子进程并备份。没有合格叶，不重开路线、不派接管；wire 仍可能增长，下轮必须复查并阻止新编译。
  ④ 当前授权在飞仅 cell3-wt2a-core-w1 与 nli-algebraize-fat1-scout-w1；其它候选不自动补位。下一条：续1261。

- **2026-11-18（19:22，续1259）**：**用户批准“直接闭合 + 零 Lean 探针”组合，两条异步发车并登记 running 回执**。
  ① `cell3-wt2a-core-w1`（agent-10 / agent-kgu7886m）：从已验收 NliBanks19 归约继续，真证三维 `Δ≥0 ⇒ 0<w2aF` 核、bank 消费与 Assembly patch；先查 y6 走步的 Δ/eta 域，y5 只按实际分片，目标 ≤12 常规 cell + dip 2×2，约 450 行/三轮止损，不碰 wt1。
  ② `nli-algebraize-fat1-scout-w1`（agent-11 / agent-4q928r7n）：零 Lean、只做 QITNPEA1_1_2 的局部夹逼误差预算，≤8 区域，ρ<1/3 才建议后续；不重启 BernsteinKit。
  ③ **派发前陈述勘误**：`bank_QITNPEA1tmpl 1 2` 的分母为 `1+bankGenMid 1+bankGenMid 2 = 2`，主支是 **γ4/2>0.0057**，调研报告的 γ4/3 错；旧 +3.585e−2 余量暂停引用，车道须从 Lean 陈述与校准求值器重算。其余联合包络、析取 LP、Hessian 服务不自动补位。下一条：续1260。

- **2026-11-18（19:10，续1258）**：**只读数学调研收线；候选入 §2.4，外部先例经编排者复核并降调**。
  ① completed 后 wire 超 1 min 无增长、无 agent-9 进程；严格只读，无 patch/编译/主仓改动。报告给五候选，优先保留局部代数化、联合 `(dihY,γ4)` 包络与低成本析取 LP；未批任何后续车道。
  ② 原文确认 Hales 回顾 §5.3 的单调降维、共享二阶导界、非负组合建议；Revision §5 确认 sharp 点取等的单向多项式夹逼 + Bernstein 先例；仓内 `partial_convex_max`/`mono_depth=200` 和既有 arctan 下界件也命中。
  ③ **信任/表示修正**：IneqAgent 论文确有精确 Bernstein + Lean 翻译，但公开 `IneqTSKAJXY_TADIAMB.lean` 用显式 node、positivity、ring，而非本仓失败的 MvPolynomial/Finsupp/decide；公开 `Ineq7067938795.lean` 仍 sorry。它只证明另一证明项形状可能，不能宣称本仓表示问题已解决，也不接受大规模 auto-gen 或新 native_decide。
  ④ **数学判据修正**：常数非负权重消析取的可行性应对 `0 ∉ conv{f(y)}` 做 LP/对偶检验，不是“各零集必须正距离分离”。调研的 35–40 覆盖、1–2k 行、27–31×加速全部标为未验证估计，不进入进度口径。详见 `nli-campaign.md` §1.16。下一条：续1259。

- **2026-11-18（19:03，续1257）**：**`cell3-wt-math-w1` 收线为 UNRESOLVED；wt2A 核归约验收通过，y5 全盒单调性撤销**。
  ① completed 后 wire 超 1 min 无增长、无 agent-8 进程，快照交付与 patch 齐全；patch 双侧 a/lean、b/lean，`git apply --check` PASS，源与镜像逐字节一致，未应用、未落库。
  ② 288 行 `NliBanks19.lean` 真证显式核、h0cut/lfun 辅助、η²/Δ 双向归约和 `bank_QZECFICwt2A_of_core`；编排者独立编译 RC=0（5.70 s / 5.78 GB）、八公理面标准三，真实 bank 类型消费岛探针 RC=0（3.20 s）且标准三。
  ③ **核仍未证**：剩余为三维盒上 `Δ≥0 ⇒ 0<w2aF`；bottom-edge 单 cell 下界 +2.97e−4、后续 8–12 cell 及 wt1 余量全是数值导航，不能写成减债。wt1 未动笔，SORRIED 51 / AXIOM 585 不变。
  ④ **ERRATA**：独立 BackendM 60 dps 在 `(2.4635,2.5156,2)` 得 ∂w2aF/∂y5=−8.4182757987e−5，步长 1e−7/1e−9/1e−11 一致且 Δ>0；旧“wt2A y5 严格增”不可用。y5=2.513 处反而为正，故只记录反例点，不把整个 `[2.513,2.519]` 都写成负导数。下一条：续1258。

- **2026-11-18（18:57，续1256）**：**`fhb-floor-mono-w1` 收线为 UNRESOLVED；三轴一阶单调路线撤销，凹性 + 端点归约独立验收通过**。
  ① completed 后 wire 超 1 min 无增长、无 agent-6 进程，快照 DELIVERY/patch 齐全；patch 双侧 a/lean、b/lean 且 `git apply --check` PASS，未应用、未落库。
  ② 编排者以 60 dps 独立复算 B0 内点：∂γ4/∂y4=−0.09314667568151258 @ `(2.6508,2,2,2.4635,2,2)`；∂γ4/∂y3、∂y5=−0.05788818698069536 @ `(2.6508,2,2.4635,2,2.4635,2)`。自适应微分与中心差分约 15 位一致，y4 纤维值也直接先升后降；这是高精度数值反例，不是 Lean 形式反证，但足以撤销 seam Evidence §3/§5 的全盒正导数结论。
  ③ **额外勘误**：车道闭式端口在上述点分别给 −0.07182445/−0.05463538/−0.04736590，与自适应微分同号但不等值；所谓“三法定量互证”不成立，本日志只采自适应微分 + FD 的符号结论。
  ④ 166 行 `FhbFloorMono.lean` 的 3 条归约把 m3/m4/m5 归到 H1 纤维凹性 + H2 端点比较；编排者独立编译 RC=0（3.74 s / 5.58 GB）、五公理面标准三，真实 `FhbEtaCurve` 消费岛探针 RC=0（3.21 s）且标准三。H1/H2/g3pos 均未证，m3/m4/m5 本体也未证，SORRIED 51 / AXIOM 585 不变；不自动续发车道。下一条：续1257。

- **2026-11-18（18:39，续1255）**：**用户批准追加一条严格只读的 nli 数学加速深度调研，已异步发车**。
  `nli-math-research-w1`（agent-9 / agent-0gwhzy5z）：仓内考古 + 公开文献，重点寻找共享母定理、自然坐标下的凸性/单调性、短而精确的代数证书及专门几何结构；最多给 5 个有公式的候选和 1 个 bounded pilot。
  明确排除普通 B0 凹性、通用超越 Bernstein、农场及大规模自动代码；不接管三条在飞证明车道，不写任何文件、不编译、不重算。内置浏览器首次检索遇 `ERR_CONNECTION_RESET`，调研改用 WebSearch/FetchURL 并须给原文 URL。下一条：续1256。

- **2026-11-18（17:57，续1254）**：**用户批准推荐的三条直接减债车道，全部异步发车**。
  ① `fhb-floor-mono-w1`（agent-6 / agent-h7gnywj3）：证 m3/m4/m5，直接喂 `fhb_hba_of_floor3`，不做整盒凹性或 g3pos。
  ② `fhb-g3pos-w1`（agent-7 / agent-o3k090sz）：先 1-D seam 曲线，再 G2/边界片/N3D；禁止 96 角点表、Newton 种子充证和通用新引擎。
  ③ `cell3-wt-math-w1`（agent-8 / agent-u2y42rsd）：旧 math5-w4 已确认无活动进程，从 WIP 接管，先 wt2A 后 wt1，不碰 wt0sqrt8。
  ④ 三条均主仓 tracked 零改动、统一 `/tmp/lean_global_lock.d` 串行编译、三轮止损；D/E、B0 母定理、BernsteinKit、FHBv2a 不自动补位。下一条：续1256。

- **2026-11-18（17:46，续1253）**：**六车道总结入档，下一轮候选排序明确**。
  ① 新增 `docs/history/nli-six-lanes-2026-11-18.md`：六车道判词、实测加速与证据等级、三份独立验收 Lean 资产、失败边界、下一步和九条经验教训；`docs/README.md` 与 `nli-campaign.md` §8 已链接。
  ② 总结口径：精巧数学确实能压缩问题，但 Python GO ≠ Lean GO、切片 ≠ 整盒；SORRIED 51 / AXIOM 585 不变，三份 Lean 资产未落库。
  ③ 下一轮推荐三条：`fhb-floor-mono-w1`（m3/m4/m5）、`fhb-g3pos-w1`（N3D + 边界片 + 1-D 曲线）、`cell3-wt-math-w1`（wt2A→wt1）；目标分别补齐 FHBa 与直接减债，均尚未发车。
  ④ B0 母定理原凹性路线、完整 BernsteinKit、通用超越后端继续搁置；D/E 与 fresh Bernstein 表示仅作备选。下一条：续1254。

- **2026-11-18（17:17，续1252）**：**`bernstein-kernel-pilot-w1` 第二次 2 h 超时，按多轮/长上下文止损为 UNRESOLVED，不再 resume**。
  ① 原跑与续跑均超时；第二次 wire 停止后无 Lean/编译进程、无 stale lock。最新 /tmp WIP 与 logs 已同步快照，`ORCHESTRATOR_NOTE.md` 给出定案。
  ② 设计 A 的 MvPolynomial `DecidableEq` 归约失败有 probe 实证；设计 B' 通用核虽在 `bk13` 单次 RC=0，但 `olean7` 又有 exponent/Finsupp 错误与 heartbeat 超时，当前 WIP 不得按已绿交付。
  ③ 81 系数叶仍卡 Quot/Finsupp/Eq.rec 的 `Decidable` 归约和指数类型，1,215 根叶未开始 ⇒ **没有完整 wall/RSS/olean/axioms 定标，Python GO 不等于 Lean pilot GO**。
  ④ 经过 bk1–13、leaf36b–f 等多轮，符合止损与 fresh-session 条件；不第三次 resume。完整 BernsteinKit 搁置；仅低优先登记 `bernstein-kernel-representation-w1`（fresh、仅 81 叶、显式指数表示、用户另批）。
  ⑤ 三条新 pilot 至此全部收线，无在飞车道；SORRIED 51、AXIOM 585 不变。`nli-campaign.md` §1.10 与 §8 已同步。下一条：续1253。

- **2026-11-18（17:02，续1251）**：**`g4-hessian-lean-w1` 收线为 UNRESOLVED——W1/W5 真证，整盒量化否证；Scout factor-2 勘误同步**。
  ① completed 后 wire 超 1 min 无增长、无 agent/Lean 进程，快照有 DELIVERY/patch，判真完成；主仓未落库，SORRIED 51 不变。
  ② W5 `Gamma4ConcaveBridge` + W1 `Gamma4DerivSecond`（6 条对角二阶导）由编排者独立编译 RC=0（2.23 s / 5.05 s，峰值 2.22 / 5.84 GB），8 个检查公理面标准三；岛协议消费探针通过。
  ③ **ERRATA**：Scout `assemble_slices.py` 的 ell 分母应由 52 改为 26、lam 应由 −100/104 改为 −100/52（两处权重减半）。旧 N/D 数值与余量作废；修正装配由编排者重跑，B0 两片仍全负（左 max 约 −4.39e102、右约 −2.04e91），ZTG `0_1_0_0` 在 20001/10000 仍精确凹性破坏，结论方向保留。
  ④ 整盒量化三轮 = 单调性否证 / 逐坐标凹性否证 / 张量爆炸。编排者直接读 `Qy2_interp.pickle` 重算 `∂²Q/∂y2²` 的 4×4 精确网格 = **12 非正、4 正**（4 点均在 y2=2309/1000），证原凹性归约不可用；修正装配 4,374 点全负只是数值证据，不是盒证。
  ⑤ `b0-master-lean-w1` 搁置，禁止按原方案发车；固定 all-2 `g4-fixed-base-w6-w1` 仅低优先登记，不能冒充整盒。Bernstein kernel 继续在飞；`nli-campaign.md` §1.12 已重写并同步 §8。下一条：续1252。

- **2026-11-18（15:13，续1250）**：**Bernstein kernel 与 Hessian Lean 同时撞 2 h 超时；按快照无接管式 resume，stale lock 已清理**。
  ① 两条均 timed_out、无 DELIVERY；逐条 wire 复核最后增长均为 15:08:20，至 15:11:05 无新增，ps 无 Lean/编译进程。第一次锁清理命令的脚本名检查自匹配而拒绝，未强删；随后用无自匹配检查确认无人持有后 rmdir。
  ② `bernstein-kernel-pilot-w1` 以 `agent-nb60wvnk` 续跑（agent-3 保留上下文）：从设计 B' 和当前源继续，先 81 后 1,215 系数，中段即写 DELIVERY，禁止再次无交接超时。
  ③ `g4-hessian-lean-w1` 以 `agent-nx72k3st` 续跑（agent-4）：**W5 `concaveOn_of_hasDerivAt2_nonpos` 已标准三（2.20 s）**，继续整盒基坐标量化；固定切片仍不算成功。
  ④ 两次 resume 均获 running 回执并登记；不是新批量产，不改变止损边界。FHB 已收线，SORRIED 51、AXIOM 585 不变。下一条：续1251。

- **2026-11-18（14:26，续1249）**：**`fhb-seam-curve-w1` 收线为 UNRESOLVED——η 曲线代数核心与三个归约接口真证，FHBa 尚未闭合**。
  ① completed 后 wire 超 1 min 无增长、无 agent 进程，快照有 DELIVERY/patch，判真完成；主仓 tracked 零改动、未落库、SORRIED 51 不变。
  ② 405 行 `FhbEtaCurve.lean`：η² 商式、二次边界、判别式、显式根式、盒内/边界 + `nliRestFHBVYXZa_of_eta_disj` / `fhb_eta_disj_of_hba` / `fhb_hba_of_floor3`。
  ③ 编排者从快照源独立编译 RC=0（8.66 s / 5.83 GB），11 个公理面恰标准三；初次消费探针因 LEAN_PATH 缺新 olean 失败，按岛协议 symlink farm 后 RC=0，接口与公理复核通过；日志已存快照 `ORCHESTRATOR_CHECK/`。
  ④ 剩余 = m3/m4/m5 + g3pos（N3D、7 边界片、1-D 曲线 γ4≥7e−3）；∂y6/∂y2 变号，B0 的“简单四坐标单调”草案已修正。后续 `fhb-floor-mono-w1` / `fhb-g3pos-w1` 仅登记未发车；v2a 冻结。
  ⑤ Bernstein kernel 与 Hessian Lean 继续在飞；`nli-campaign.md` 新增 §1.13。下一条：续1250。

- **2026-11-18（13:09，续1248）**：**用户按推荐批准三条 Lean pilot，全部异步发车；替代候选保留在队列**。
  ① `bernstein-kernel-pilot-w1`（agent-3 / agent-b38xy1hv）：81 → 1,215 系数真实单叶定标，单叶 >5 min 或三轮卡死即停。
  ② `g4-hessian-lean-w1`（agent-4 / agent-ynl3lw6b）：先 W5，再做 B0 y1 一条轴的整盒基坐标量化；固定切片不算成功，不量产其它轴。
  ③ `fhb-seam-curve-w1`（agent-5 / agent-7xfvb23w）：先 FHBa η126 边界曲线 + 4 单调性符号，再评估 v2a；禁止套 96 角点表。
  ④ 三条均主仓 tracked 零改动，统一以原子 `mkdir /tmp/lean_global_lock.d` 串行所有 Lean 编译，锁内检查 lean=0、总 RSS<20 GB、pressure<2；禁 lake build/auto_gate/地图/Assembly/Final 构建。
  ⑤ 其他想法已保留：F `cell3-wt-math-w1`（稳妥直接减债）、D LP 表示审计、E TerminalV11 家族压缩；B0 母定理与完整 BernsteinKit 均仍等前置 + 用户裁决，不自动补位。下一条：续1249。

- **2026-11-18（12:54，续1247）**：**A 的全景数值交叉验收完成**。
  `derive_second / verify_t2 / exact_check / assemble_slices / numcheck` 整串进程 RC=0；
  10/10 切片 worst-2nd-diff 与交付一致（含 0_1_0_0 正二阶导和 1_1_0_0 −0.02687）。
  续1246 的 numcheck RUNNING 状态由此关闭，A 的侦察交付全部复现完毕；盒级量化/W5/Lean 成本等待后续 pilot，不因本验收消失。下一条：续1248。

- **2026-11-18（12:51，续1246）**：**`g4-hessian-scout-w1` 收线——atan-free Hessian 与一正一负切片证书成立，GO（有条件）；A/B/C 全部收线**。
  ① completed 通知后核查：wire 最后增长 12:42:24，至 12:50:06 无新增、无匹配 agent 进程，快照交付齐全，判真完成。
  ② dihXf 全部 36 个二阶偏导有 atan-free 闭式；编排者复跑 derive_second / verify_t2 / exact_check / assemble_slices：36 闭式、商公式精确等式、B0 y1 两片 Bernstein 全负、ZTG `0_1_0_0` 精确凹性破坏见证均与交付一致。
  ③ **仍未解决**：固定基点切片到整盒基坐标量化、W5 的 C²→ConcaveOn 桥、Lean/大有理数证书成本、γ3/taum 独立压力测试。后续 `g4-hessian-lean-w1` 已收窄为一条轴的 W1–W6 整盒端到端，待用户裁决，未发车。
  ④ 编排者追加的全景 numcheck 仍在后台运行，**该项验收 = RUNNING，不提前记全量复现 PASS**；完成后另记。`nli-campaign.md` 新增 §1.12 并刷新 §8。
  ⑤ 三条数学侦察均已收线，未移动 SORRIED 51 / AXIOM 585；无新 Lean 施工或量产。下一条：续1247。

- **2026-11-18（12:04，续1245）**：**`b0-joint-envelope-w1` 收线——六债共享包络 GO（数值）；FHBa/v2a 改走 η 曲线；附 C 验收勘误**。
  ① completed 通知后核查：wire 最后增长 11:59:15，至 12:01:47 无新增、无匹配进程，快照齐全，判真完成。
  ② 编排者端到端复跑全过：12 pin、gamma3f 直组/桥、421,875 点扫描、主债细化、seam3/4、包络、96 点/60 轨道；全部全局最小仍标 ESTIMATE，未移动 SORRIED。
  ③ 五主债由 L1/L3/L5 覆盖，Q581/Q565 纯有理支配；FHBb 主支全盒估计 +3.804e−3。六债共享 96 角点，最小均在 `(2.52,2⁵)`。
  ④ **ERRATA（对 nli-rest-math-audit-w1）**：FHBa/v2a 全局 sharp = **+4.813e−3/+1.104e−3**，旧 +7.677e−3/+2.124e−3 为非最优驻点；两条债 `max(g,c−η²)` 非凹，禁止套角点表，候选 `fhb-seam-curve-w1` 已登记，未发车。
  ⑤ **C 验收勘误**：续1244 的 P1 复跑打印了全部关键数字，但 ε 曲线继续进入 level 3（262,144 盒）并于 840 s 超时，无残留进程；不得记作“P1 全进程 PASS”。这不改变已复现的负向数值，完整 RC 标 UNRESOLVED；`nli-campaign.md` §1.10 已同步。
  ⑥ A 继续在飞；`nli-campaign.md` 新增 §1.10/§1.11 并刷新 §8。基线 SORRIED 51、AXIOM 585 不变。下一条：续1246。

- **2026-11-18（11:54，续1244）**：**`bernstein-representative-w1` 收线——多项式 Bernstein GO（待 Lean 单叶），通用超越后端 NO-GO**。
  ① completed 通知后按纪律核查：wire 最后增长 11:46:44，至 11:48:03 无新增、无匹配进程，快照交付齐全，判真完成；主仓无本车道改动。
  ② 编排者复跑：42 项自检、ZTG 四债、两组守卫全部 PASS；P1 脚本输出复现 √ 误差 5.944、Q 跨 −1、`chord(S)^5` 126,607,131 系数与 ε 细分曲线。
  ③ 正向：ZTG 四债根盒各 1 叶；q=64/25 三债各 1,215 系数 / 57,142 B、约 0.42 s，q=36/25 经两次单调剪枝为 81 系数 / 2,488 B；守卫 1–3 叶毫秒级。
  ④ 负向：BIX 代表节点 √ 整盒误差为 slack 的 2,662 倍，单分数组合爆炸；**杠杆 A（先代数化）是必需门，不是可选项**。
  ⑤ 后续仅保留 `bernstein-kernel-pilot-w1` 候选：ZTG 根叶 + 小尺寸对照的真实 Lean 定标，待用户裁决，未发车。A/B 继续在飞；基线 SORRIED 51、AXIOM 585 不变。下一条：续1245。

- **2026-11-18（11:02，续1243）**：**用户批准 A/B/C 三条零 Lean 数学侦察；D/E/F 记入排队；priority queue 全面重组**。
  ① 已异步发车：`g4-hessian-scout-w1`（agent-0）、`b0-joint-envelope-w1`（agent-1）、`bernstein-representative-w1`（agent-2），成功回执与任务边界见 §1；三条均主仓 tracked 零改动、零 Lean。
  ② D `lp-dual-representation-audit-w1`、E `terminal11-family-compression-w1`、F `cell3-wt-math-w1` 仅登记，未发车，见 §2.1。
  ③ 旧 2,708 行账本全文（含本次回执）已保存到 `archive/priority-queue-2026-11-18-pre-nli-math.md`；现役文件改为基线/在飞/排队/裁决/负结果/最近日志。`docs/README.md` 同步新归档入口。
  ④ 本批为文档与派单操作，不改 Lean、不重跑基线；SORRIED 51、AXIOM 585 不变。下一条：续1244。

- **2026-11-18（09:35，续1242）**：**`handoff-2026-11-18.md` 新建，整体状态 dump 入档**。
  内容 = 基线 AQ、当日落库、4 项待裁决、ox3q1h 剩余路径、farm-ops 摘要、复现命令与易失池风险、护栏、快照索引；`docs/README.md` 交接列表同步置顶。下一条：续1243。

- **2026-11-18（09:20，续1241）**：**SF 111 落库 `b11c1627`，S2a margin″ 装配解锁**。
  `sf-hslp-box-w1` 完成 hsl/hslp 387 处盒前提 + 2 个 `_box` 步骤引理（14 文件，+1,101/−596）；结论/槽序未动。14 模块直编 RC=0/0 err，17/17 公理探针标准三。S2b 其余批与 push 仍待裁决。下一条：续1242。

- **2026-11-18（09:05，续1240）**：**`farm-ops-w1` 收线，统一排产交付**。
  `FARM_PLAN.md` + `DEBTS.tsv` 对账 51 条现役债；43 条 Gate-0 冻结债未消，非农场可闭 8 条，农场估算约 27,000 CPU·h。五项解冻仅呈请求，未获批准；F1 仍是唯一校准点。下一条：续1241。

- **2026-11-18（08:55，续1239）**：**TSKAJXY 全盒装配落地，基线 AQ 定档，SORRIED 52→51**。
  `58ade83a`（6,612 leaf 源）+ `c940aae7`（202 装配模块/23,832 行）+ `e4c384e6`（Assembly 接线）。编排者从落地源重编全链 RC=0/0 err，关键件公理标准三；根面 589 与基线 AP 同集合，K_AXIOM 585 未动。当前 51 = Assembly 51（50 `nli*` + 1 hLP）+ Text 0。下一条：续1240。
