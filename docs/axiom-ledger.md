# 孪生/出口 Axiom 台账正本总表（axiom-ledger）

> **点时快照**（point-in-time snapshot）：2026-10-28 由 axiomledger-doc-w1 车道汇总七份
> 车道快照台账合成，主仓基线 `08348d9e`（HEAD）。本文件是**纯文档综合**：零探针、零构建、
> 零 `.lean` 改动；全部数据来自各来源快照（基线各异，见 §0.2），缺数据处标 `UNRESOLVED`
> 而非补探。后续落库/探针发生后请在新车道内增补行或在备注列记差异，勿覆写历史行。

## 0.1 口径定义

| 术语 | 定义 |
|---|---|
| **标准三** | `#print axioms` = `[propext, Classical.choice, Quot.sound]`（Lean 4 默认公理，无 sorryAx）→ 可接线转 PROVED |
| **sorryAx 面** | `[propext, sorryAx, Classical.choice, Quot.sound]`（证明项含 `sorry`，即债面；闸 rule5 自 2026-09-28 起允许 sorryAx） |
| **搬债式**（debt-consolidating） | 出口陈述按 SF 修正落库后接线到带 sorryAx 的孪生：**不转 PROVED**，债从出口本位搬到已知上游根（SF-63/71/73 停手判例；ASSEMBLY WAVE 2026-09-21 契约「sorryAx 随证明项流动」）。根闭合后下游零改动自动转净（cone 自愈） |
| **债转移** | 搬债的账面效应：出口本位 −1、根位 +0（根已在账）；e2e 151 / M0 直源计数不变，除非出口/根恰在 e2e 口径内。装配层出口全树零 importer → 今日装配层接线按构造 **M0 −0** |
| **类别四分** | **注册表concl** = LA1 注册表 `*_concl` 条件箭头（e2e 锥内直源 151 口径）；**装配出口** = LocalConcl/PackingConcl `*_discharged` 出口 + anchor 注入（锥外）；**波件** = 波 1/波 2 等编译窗待落件及其 /tmp 预验件；**根件** = 污染根（case bank、slice farm、anchor、kernel 等） |
| **判词取值** | 可接线PROVED / 搬债 / HOLD / NEEDS-SF / 已落库 commit / UNRESOLVED |

## 0.2 来源快照与基线（全部 `c17_backup/lane_snapshots/` 下）

| 来源快照 | 台账 | 行数 | 主仓基线（自报） | 一句话内容 |
|---|---|---:|---|---|
| twinprobe-w1 | twinprobe-ledger.tsv | 95 | `a6464251` | 62 WIRE 出口 + SF-64~74 孪生 + 种子复核 + 波 1 四件的 `#print axioms` 全量普查（94 CONFIRMED / 1 REFUTED / 0 UNRESOLVED） |
| la2027-w2prep | w2probe-ledger.tsv | 59 | `aacaf3e5` | 波 2（LA20-27）52 声明 + 5 kit-check 探针台账（翻案①：EAPGLE 闸 = case bank + 总装双前置） |
| m1asm-w1 | CLASSIFY.tsv | 34 | `851e1b49` | 装配 discharge 批 32 件/33 处 A/B/C 全判词（A=0 / B=7 / C=25）+ 2 anchor |
| la1reroute-w1 | REROUTE-PLAN.md | — | `725699f4` | (c1) 上移装配点施工图：21 箭头 `_discharged` axiom 面（21/21 全脏）、27 新进锥行、切换日账 151→157、兑现序至 130 |
| sf6373debt-w1 | kits ×3 | 3 件 | `8c451a6d` | SF-63/71/73 搬债式接线 kit 预验证通过（在册待裁决） |
| sf77draft-w1 | patch 77 | 1 件 | `aacaf3e5` | §77 LA22 funlist 双表化（判 A·B 级），patch 在册未落 |
| sf78draft-w1 | patch 78+79 | 2 件 | `3f31e839` | §78 XYOFCGX / §79 IVFICRK TWIN MISMATCH 判 A′，patch 在册未落 |
| sfc1c2draft-w1 | patch 80+81a/81b | 3 件 | `9cd305ad` | SF-80（k=3 builder 行索引化）+ SF-81 两案（81a 加参 / 81b 删字段），patches 在册未落 |
| w1asm-w2 | REVISED-PLAN + kits ×4 | 4 件 | `8c451a6d` | 波 1 修订：4 kit 全部 /tmp 验净（标准三）、3T1/3T5 改道路线 (b)、funlist 降级 |
| la24casebank-w1 | PORT-PLAN + probes ×6 | 6 探针 | `851e1b49` | LA24 case bank 四件部分闭合 + HDPLYGY 分层移植 + SF-80/81 取证（立案见 sffile-w1） |

> 缩写：TP=twinprobe-w1、W2P=la2027-w2prep、M1=m1asm-w1、RR=la1reroute-w1、CB=la24casebank-w1、W1A=w1asm-w2。
>
> **快照指纹**（sha256 前 12 位，合成时点 2026-10-28）：twinprobe-ledger.tsv `a449a629f60f` ·
> w2probe-ledger.tsv `1e89ca4135eb` · CLASSIFY.tsv `b1d334b94896` · REROUTE-PLAN.md `9d71a9731d0f` ·
> TWIN-MISMATCH.md `329d435f30d6` · patch 77 `b5b344e5de50` · patch 78/79 `4f5d3220385b` ·
> patch 80 `0425c6b21dac` · patch 81a `4f37cc43f191` · patch 81b `c18042a5208a`。

## 0.3 今日结论速览（2026-10-28）

**① 装配层不在 e2e 锥内（awaiting-user）。** LocalConcl/PackingConcl 出口全树零 importer、
锥内零出现（e2e 直接吃 LA1 注册表 sorry 版，经 LA16:488 `JEJTVGB_p16` 21 实参 + LA20 WKEIDFT 支）；
今日装配层接线按构造 M0 −0。唯一清零通道 = **(c1) 上移装配点**（RR 全要素验证、全栈探针通过）：
LocalConcl +2 定理 + Assembly 1 import 边 + 2 换名，切换日 e2e SORRIED **151→157（净 +6**，
修正 sf78draft 估算 +2~+4 的漏计）**，此后按兑现序（LA18 −5、LA24 −4、LA32 −3、LA29 −1、
LA33 −11、LA17 −1、mnt11_anchor −1、WKEIDFT 须 phase-2）每闭一根 −1，理想上限 **130**（= 今日 −21）。
**awaiting-user：切换日中间态上浮（+6）换 22 件 LA1 注册表清零通道，待编排者裁**；C1(LocalConcl)→C2(Assembly+重扫)
可随任一编译窗落，与 m1asm B 批同文件串行、与 A2 的 Assembly 编辑编译窗互斥。

**② 波 1 / 波 2 / 编译窗待落件。**
- **波 1**（W1A，LA20/22/23）：4 kit 全部 /tmp 验净（落库后均标准三）——`is_scs_3M1_p22`、`s_init_list_alt_p23`、
  `is_scs_3T1_p22`+`is_scs_3T5_p22`（改道路线 (b) LA20 直证同款）；直源账 **−4（14→10）**；
  kit4 `is_scs_funlist_basic_p22` 降级为可选（附 SF-77 前置）。无 NEEDS-WINDOW 件。
- **波 2**（W2P，LA20-27）：主清单 5 件链图探明——`XWITCCN_CASE_4/5/6`（CB 部分闭合：装配体验净 + HDPLYGY
  四件移植验净，余 LA23/LA24 前置件填体）、`XWITCCN_CASE_3`（**阻塞 = SF-80** 陈述级失真）、
  `EAPGLE_p27`（胶合已验，**闸 = case bank + ZITHLQN 总装双前置**，翻案①）；条件位 `AQICLXA`/`FZIOTEF`
  （W2*，SLICE 灌证即净，等 QKNVMLB 波）。直源账：波 1 后 10 → 全落 −5 = **5** → 条件位 −2 = **3**。
- **编译窗其他在册**：m1asm B 批 7 kit（搬债，LocalConcl 单文件，§2.2 判 B 行）、RR C1→C4
  （§0.3①）、CB HDPLYGY 节 + CASE_4/5/6 体（§3.2）、poolc-w6-replay / A2 落地波（本台账面外）。

**③ SF 已立案未落清单（§77-81，立案 commit 见本提交）（patch 全部在册未落，零消费者零穿参）。**

| SF | 对象 | 判 | 修后 axiom 面 | 状态 |
|---|---|---|---|---|
| §77 | LA22 `is_scs_funlist_basic_p22` 单 d 塌缩（HOL 双表） | A（移植误植）·B 级 | kit4 灌证后标准三 | patch `77-funlist-dual-table.patch` 在册 |
| §78 | `XYOFCGX_concl` 缺 `Packing V`（packing-free 形数学为假） | A′（向 Rogers.hl:6559 归正） | **标准三（真消债）** | patch 与 §79 同文件在册 |
| §79 | `IVFICRK_concl` 第二合取支缺两前提 | A′（向 Rogers.hl:9929 归正）+ C-残余 NEEDS 附注 | 搬债（根 PA7:3953 单点化） | 同上 |
| §80（原 SF-C1） | LA24 k=3 四件 builder `cycRow` 误植（成员不约束 l，机检可反驳/被空真） | 陈述失真 | sorry 体不变、陈述归正 | patch `80-k3-builder.patch` 在册 |
| §81（原 SF-C2） | `StableSyP23.stable` 字段 `:=sorry` 常量级污染（LA23:232，提及即 sorryAx） | def 编码，**81a 加参 / 81b 删字段两案待裁** | 案①债转 IS_SCS_STABLE_SYSTEM（TRACKED） | patches `81a/81b` 在册 |

## 1. 注册表 concl（LA1 22 件，e2e 锥内直源）

> LA1 在 151 口径共 23 行 = 本表 22 件 + `main_nonlinear_terminal_v11`（109 合取 deliberate
> 外部锚，在账不动，非本台账债面）。21 件 parent=`JEJTVGB_p16`（LA16:488 证明项实参）、
> `WKEIDFT_concl` parent=`EQ_DIAG_STAB_6I1_03`（LA20:1311/1326 消费）。axiom 面均
> sorryAx（注册表 shim `:= sorry` 本体）；各行污染根 = 其孪生/上游根（RR §2 逐位映射 +
> TP 源1 同名 `_discharged` 行）。**不做 (c1) 重排，上游灌证单独发生时这 22 个名字一个也不会出 151。**

| 声明全名 | 文件:行（LocalAuto1.lean） | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.WKEIDFT_concl | LocalAuto1.lean:2286 | 注册表concl | sorryAx（`:= sorry` shim 本体） | LocalConcl:1309 `WKEIDFT_discharged` HOLD(b)；孪生 LA24:146 循环再出口 | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=EQ_DIAG_STAB_6I1_03 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.OTMTOTJ1_concl | LocalAuto1.lean:2518 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA24:1045 骨架占位 sorry | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.OTMTOTJ2_concl | LocalAuto1.lean:2523 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA24:1053 骨架占位 sorry | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.OTMTOTJ3_concl | LocalAuto1.lean:2528 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA24:~1060 骨架占位 sorry | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.OTMTOTJ4_concl | LocalAuto1.lean:2534 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA24:~1069 骨架占位 sorry | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.HIJQAHA_concl | LocalAuto1.lean:2540 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA29:2567 缺 SCS_5M3_SLICE/ARROW 6 件 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.CNICGSF1_concl | LocalAuto1.lean:2547 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA18:1047-1053 slice + LA1 YXIONXL3_concl | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.CNICGSF2_concl | LocalAuto1.lean:2552 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA18:1056-1062 slice + LA1 YXIONXL3_concl | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.CNICGSF3_concl | LocalAuto1.lean:2557 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA18:1064-1070 slice + LA1 YXIONXL3_concl | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.CNICGSF4_concl | LocalAuto1.lean:2562 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA18:1072-1078 slice + LA1 YXIONXL3_concl | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.CNICGSF5_concl | LocalAuto1.lean:2567 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA18:1080-1086 slice + LA1 YXIONXL3_concl | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.ARDBZYE_concl | LocalAuto1.lean:2572 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA33:1285 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.FYSSVEV_concl | LocalAuto1.lean:2576 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA33:1506 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.AUEAHEH_concl | LocalAuto1.lean:2581 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33:1515-1516 slice | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.VQFYMZY_concl | LocalAuto1.lean:2591 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33 OPP_IS_SCS_p33:126 链（ZNLLLDL/SCS_4I3 族） | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.BNAWVNH_concl | LocalAuto1.lean:2595 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33:2032 4M2-slice | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.RAWZDIB_concl | LocalAuto1.lean:2600 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33:2213 4M3'-slice | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.MFKLVDK_concl | LocalAuto1.lean:2605 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33:2347/2354 4M4'-slice ×2 | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.RYPDIXT_concl | LocalAuto1.lean:2610 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 根 LA33:2536 4M5'-slice | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.NWDGKXH_concl | LocalAuto1.lean:2687 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA32:870 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.YOBIMPP_concl | LocalAuto1.lean:2697 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA32:1082 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |
| Kepler.Text.MIQMCSN_concl | LocalAuto1.lean:2708 | 注册表concl | sorryAx（`:= sorry` shim 本体） | 孪生 LA32:1379 + mnt11_anchor | 搬债·经 (c1) 上移装配点清零（awaiting-user） | parent=JEJTVGB_p16 | e2e-reachability-map.tsv + la1reroute-w1 + twinprobe-w1 |

## 2. 装配出口（LocalConcl / PackingConcl，全树零 importer、锥外）

### 2.1 LocalConcl 62 WIRE 已接线出口（TP 源 1，基线 `a6464251`）

> 62 条 w0prep WIRE 预测全数 CONFIRMED（CLEAN 7 + TAINTED 55），无一翻案。7 件标准三
> （YXIONXL3/EYYPQDW/EYYPQDW2/EYYPQDW3/unadorned_MMs/HXHYTIJ/DRNDRDV）= 早已净面；
> 55 件 sorryAx = 搬债口径、不可转 PROVED。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 对 w0 预测 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.YXIONXL1_discharged | LocalConcl.lean:499 | 装配出口 | sorryAx | sgtrnaf_p12 (LocalAuto12.lean:278-280 sorry锚) 经 NOT_EMPETY_MMS_TRANSFER(LocalAuto12.lean:284); 尾注ledger"十条classic吃波内sorry输入"点名例 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.YXIONXL3_discharged | LocalConcl.lean:580 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.EYYPQDW_discharged | LocalConcl.lean:587 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.EYYPQDW2_discharged | LocalConcl.lean:605 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.EYYPQDW3_discharged | LocalConcl.lean:508 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.unadorned_MMs_discharged | LocalConcl.lean:639 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.HXHYTIJ_discharged | LocalConcl.lean:645 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.PQCSXWG2_discharged | LocalConcl.lean:655 | 装配出口 | sorryAx | PQCSXWG2_WITHINREAL_p11 (LocalAuto11.lean:1381, sorry:1397); 尾注ledger点名例"PQCSXWG2 via PQCSXWG2_ATREAL_p11" | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.GSXRFWM_discharged | LocalConcl.lean:529 | 装配出口 | sorryAx | GSXRFWM1_p33 (LocalAuto33.lean:523-524 sorry, k=4 genericity案例库); LocalConcl docstring自注"modulo the wave's own sorried GSXRFWM1_p33 input" | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.AUEAHEH_discharged | LocalConcl.lean:536 | 装配出口 | sorryAx | SCS_4I1_SLICE_02_p33 (LocalAuto33.lean:1515-1516 sorry); docstring自注"modulo the wave's sorried slice identity" | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.ZNLLLDL_discharged | LocalConcl.lean:542 | 装配出口 | sorryAx | SCS_4I3_ARROW_4T4_p33/STAB_4I3_02_ARROW_4I3_13_p33 (LA33:1773-1781)→OPP_IS_SCS_p33 (LA33:126 sorry); 注: BB_4I3_IMP_4T4_p33已于09-20闭(docstring的sorried注记过时,但OPP链仍在) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.VQFYMZY_discharged | LocalConcl.lean:548 | 装配出口 | sorryAx | 闭包显式含ZNLLLDL_p33与SCS_4I3_ARROW_4T4_p33→OPP_IS_SCS_p33(LA33:126 sorry); arrowSetRight置换shim本身干净 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.BNAWVNH_discharged | LocalConcl.lean:554 | 装配出口 | sorryAx | 4M2-slice件 (LocalAuto33.lean:2032 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.RAWZDIB_discharged | LocalConcl.lean:560 | 装配出口 | sorryAx | 4M3'-slice件 (LocalAuto33.lean:2213 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.MFKLVDK_discharged | LocalConcl.lean:567 | 装配出口 | sorryAx | 两个4M4'-slice件 (LocalAuto33.lean:2347/2354 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.RYPDIXT_discharged | LocalConcl.lean:573 | 装配出口 | sorryAx | 4M5'-slice件 (LocalAuto33.lean:2536 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.XWITCCN_discharged | LocalConcl.lean:676 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto36.lean:2524); docstring自注"still sorried — debt flows" | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.XWITCCN2_discharged | LocalConcl.lean:681 | 装配出口 | sorryAx | 孪生已证但闭包含UXCKFPE2_p27(LA27:546)→UXCKFPE_p24(LA24:1395)→XWITCCN_CASE_3/4/5/6_IS_SCS_p24(LA24:1387/1128/1163/1196全sorry); TSV"已证"乐观注记被推翻——已证≠sorry-free | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.AYQJTMD_discharged | LocalConcl.lean:686 | 装配出口 | sorryAx | SGTRNAF_p27(LA27:564)→UXCKFPE2_p27(LA27:546)→UXCKFPE_p24(LA24:1395)→k-case bank(4×sorry); s_init_scs_p27八初始系统is_scs记录全已证(LA22:994-1049生成器+LA20:403+LA27:730), 非污染源; 污染唯LA24 case bank | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.EAPGLE_discharged | LocalConcl.lean:691 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto27.lean:869, NEEDS JEJTVGB registry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.JKQEWGV1_discharged | LocalConcl.lean:790 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto23.lean:948) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.JKQEWGV2_discharged | LocalConcl.lean:798 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto23.lean:956) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.JKQEWGV3_discharged | LocalConcl.lean:807 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto23.lean:968) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.ZLZTHIC_discharged | LocalConcl.lean:697 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto14.lean:1068, lunar-deformation车道) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.UAGHHBM_discharged | LocalConcl.lean:823 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto30.lean:1212, restriction-isScs fork) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.LKGRQUI_discharged | LocalConcl.lean:714 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto27.lean:896); 本体LKGRQUI_concl亦sorry — W1头号解锁件 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.ODXLSTCv2_discharged | LocalConcl.lean:837 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto28.lean:2354) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.IMJXPHRv2_discharged | LocalConcl.lean:850 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto28.lean:2340) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.NUXCOEAv2_discharged | LocalConcl.lean:871 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto28.lean:2321) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.PQCSXWG1_discharged | LocalConcl.lean:896 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto11.lean:1360); 无已证mkSimplex1距离恒等式 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.FEKTYIY_discharged | LocalConcl.lean:721 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto27.lean:880, ball-annulus非共面) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.AURSIPD_discharged | LocalConcl.lean:727 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto18.lean:1004, stratum计数的RRCWNSJ式案例库) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.PPBTYDQ_discharged | LocalConcl.lean:733 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto26.lean:779) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.MXQTIED_discharged | LocalConcl.lean:913 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto26.lean:764, d-等式shim); 注: LA1本体MXQTIED_concl已证(2026-09-30), e2e若改道本体出口可脱taint — W0可裁 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.AXJRPNC_discharged | LocalConcl.lean:924 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto26.lean:565) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.RRCWNSJ_discharged | LocalConcl.lean:935 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto26.lean:343) + 注入mnt11_anchor (LocalConcl.lean:487 sorry) — 双重污染 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.JCYFMRP_discharged | LocalConcl.lean:947 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto27.lean:483, NEEDS CUXVZOZ) + 注入mnt11_anchor(LocalConcl.lean:487 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.TFITSKC_discharged | LocalConcl.lean:961 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto27.lean:321) + 注入mnt11_anchor(LocalConcl.lean:487 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.AQICLXA_discharged | LocalConcl.lean:977 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto20.lean:986, NEEDS LKGRQUI_concl+AQICLXA_SLICE sorry:957) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.FUNOUYH_discharged | LocalConcl.lean:753 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto20.lean:1008, NEEDS FUNOUYH_SLICE sorry:1001) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.HIJQAHA_discharged | LocalConcl.lean:984 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto29.lean:2567, 缺SCS_5M3_SLICE/ARROW 6件) + 注入mnt11_anchor(LocalConcl.lean:487 sorry) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CNICGSF1_discharged | LocalConcl.lean:765 | 装配出口 | sorryAx | SCS_5I1_SLICE_02_p18 (LocalAuto18.lean:1047-1053 sorry, LKGRQUI lane巨件) + LA1本体YXIONXL3_concl (LocalAuto1.lean:1683-1685 sorry); 双 sorried 输入 — bola1立减5的5条之一, W0不闭 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CNICGSF2_discharged | LocalConcl.lean:771 | 装配出口 | sorryAx | SCS_5I2_SLICE_02_p18 (LocalAuto18.lean:1056-1062 sorry) + LA1.YXIONXL3_concl(LocalAuto1.lean:1683 sorry); 同上 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CNICGSF3_discharged | LocalConcl.lean:777 | 装配出口 | sorryAx | SCS_5M1_SLICE_02_p18 (LocalAuto18.lean:1064-1070 sorry) + LA1.YXIONXL3_concl; 同上 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CNICGSF4_discharged | LocalConcl.lean:759 | 装配出口 | sorryAx | SCS_5M1_SLICE_03_p18 (LocalAuto18.lean:1072-1078 sorry) + LA1.YXIONXL3_concl; 同上 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CNICGSF5_discharged | LocalConcl.lean:783 | 装配出口 | sorryAx | SCS_5M1_SLICE_24_p18 (LocalAuto18.lean:1080-1086 sorry) + LA1.YXIONXL3_concl; 同上 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.ARDBZYE_discharged | LocalConcl.lean:992 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto33.lean:1285, NEEDS SCS_4I2_IMP_SCS_4T1+MM_4I2_IMP_4T2_4T1) + 注入mnt11_anchor(LocalConcl.lean:487 sorry); LocalConcl docstring"PROVED ARDBZYE_p33"已过时 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.FYSSVEV_discharged | LocalConcl.lean:997 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto33.lean:1506) + 注入mnt11_anchor; docstring"PROVED"同样过时 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.NWDGKXH_discharged | LocalConcl.lean:1004 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto32.lean:870, MM_4M6_IMP_MM_4T3链) + 注入mnt11_anchor | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.YOBIMPP_discharged | LocalConcl.lean:1011 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto32.lean:1082, MM_4M7→4M6两方向) + 注入mnt11_anchor | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.MIQMCSN_discharged | LocalConcl.lean:1018 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto32.lean:1379, MM_4M8→4M6/4M8_02/13) + 注入mnt11_anchor | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.BKOSSGE_discharged | LocalConcl.lean:740 | 装配出口 | sorryAx | 本体真证(无sorry, w1asm翻案属实)但闭包含is_scs_3T1_p22/is_scs_3T5_p22/is_scs_3M1_p22 (LocalAuto22.lean:1668/1688/1703全sorry); "本体已证≠cone-clean"的典型 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.YRTAFYH_discharged | LocalConcl.lean:745 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto17.lean:1036, 巨型case树); 注: LA1本体YRTAFYH_concl已证(2026-09-30), e2e若改道本体出口可脱taint — W0可裁 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.MHAEYJN_discharged | LocalConcl.lean:1354 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto37.lean:1042; 逐字Prop-def MHAEYJN_prop_p37已建未灌) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CUXVZOZ_discharged | LocalConcl.lean:1026 | 装配出口 | sorryAx | 注入p21_anchor (LocalConcl.lean:493 sorry) + 引擎general_482_deformation_p21 (LocalAuto21.lean:1161 sorry巨件); 孪生本体已证但双重taint | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.CJBDXXN_discharged | LocalConcl.lean:1056 | 装配出口 | sorryAx | 同CUXVZOZ: p21_anchor(LocalConcl.lean:493 sorry) + general_482_deformation_p21(LA21:1161 sorry); mirror-index搬运shim干净 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.OTMTOTJ1_discharged | LocalConcl.lean:1198 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto24.lean:1045, 骨架占位; HOL链=BERAK_5I1(mnt11)+SET_EQ_DIAG_STAB_5I1+FZIOTEF kit) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.OTMTOTJ2_discharged | LocalConcl.lean:1205 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto24.lean:1053); 同上(5I2) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.OTMTOTJ3_discharged | LocalConcl.lean:1212 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto24.lean:~1060); 同上(5I3, 三stab目标) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.OTMTOTJ4_discharged | LocalConcl.lean:1220 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto24.lean:~1069); 同上(5M1) | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.ASSWPOW_discharged | LocalConcl.lean:1165 | 装配出口 | sorryAx | 孪生直接sorry (LocalAuto25.lean:1165); HOL原证VASYYAU.hl:154(BBS_IMP_CONVEX_LOCAL_FAN kit+arclength_lt_1553)未移植 | 搬债·不可转PROVED（SF-63/71/73 停手判例） | CONFIRMED(预测TAINTED) | twinprobe-w1·源1(62WIRE) |
| Kepler.Text.DRNDRDV_discharged | LocalConcl.lean:1153 | 装配出口 | 标准三 | 无(闭包=标准三) | 可接线PROVED | CONFIRMED(预测CLEAN) | twinprobe-w1·源1(62WIRE) |

### 2.2 LocalConcl 未接线出口 24 件（M1 CLASSIFY，基线 `851e1b49`）

> A=0：残面无净孪生可接。B=7（LFLACKU/YXIONXL2/SYNQIWN/CQAOQLR/QKNVMLB1/2/3）六段 kit
> 已落 `kits/`、7/7 探针通过（elaborate 0 错、axiom 全名 gate-faithful），待编译窗；
> QKNVMLB 组须 LocalConcl 加 `import Kepler.Text.LocalAuto35`（无环已验）。C=17：
> (a) 无孪生 5、(b) 注册表桩循环再出口 11（接线零债集中价值，OTMTOTJ 判例区分）、
> JLXFDMJ mod-transfer 真桥 1。B 批落地后 LocalConcl 出口残面 24→17、文件债 26→19。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根/缺口 | 判词 | 备注（孪生/同形） | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.HFNXPZA_discharged | LocalConcl.lean:1113 | 装配出口 | —（出口自体 sorryAx） | 缺口=上游证缺席（class iii，k=3 二面角和<2π 无任何 lane 证明）；通道=M1 port 证填（真新数学） | 不可接（C） | 无（corpus 唯 appendix.hl:710 registry let；无 proved lemma；无 HFNXPZA.hl 证明文件；k=3 lane 无 dihV …；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.EQTTNZI1_discharged | LocalConcl.lean:1127 | 装配出口 | — | 缺口=上游证缺席（iii）；通道=port 证填或删除裁决 | 不可接（C） | 无（appendix.hl:1110 let；restriction_typ1_v39 为零消费者死端 new_definition）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.EQTTNZI2_discharged | LocalConcl.lean:1139 | 装配出口 | — | 缺口=上游证缺席（iii）；通道=port 证填或删除裁决 | 不可接（C） | 无（appendix.hl:1115 let；同 EQTTNZI1 死端形）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.EFLYGAU_discharged | LocalConcl.lean:1178 | 装配出口 | — | 缺口=上游证缺席（iii）；通道=port 证填 | 不可接（C） | 无（appendix.hl:1500 let；scs_arrow {4M7}{4M6'} 无任何证明；近邻 MM_4M7_IMP_STAB_4M7 是不同陈述）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.BJTDWPS_discharged | LocalConcl.lean:1190 | 装配出口 | — | 缺口=上游证缺席（iii）；通道=port 证填 | 不可接（C） | 无（appendix.hl:1506 let；scs_arrow {4M8}{4M6',3T7} 无任何证明）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.ZITHLQN_discharged | LocalConcl.lean:1231 | 装配出口 | — | 缺口=循环再出口（接线债根=同陈述 LA1 注册表桩，零债集中价值；HOLD(b) 判例在案，实测 LA25:1002-1003 原文）；通道=LA25 ZITHLQN 案件银行证填 | 不可接·循环再出口（C(b)） | LA25.ZITHLQN_p25（LA25:1002，体=ZITHLQN_concl h 注册表再出口）；同形？同形但孪生即注册表 sorry 镜像 | m1asm-w1/CLASSIFY |
| Kepler.Text.WGDHPPI_discharged | LocalConcl.lean:1238 | 装配出口 | — | 同上（实测 LA25:1009-1011） | 不可接·循环再出口（C(b)） | LA25.WGDHPPI_p25（LA25:1009，体=WGDHPPI_concl 调用）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.TUAPYYU_discharged | LocalConcl.lean:1245 | 装配出口 | — | 同上（实测 LA25:1282） | 不可接·循环再出口（C(b)） | LA25.TUAPYYU_p25（LA25:1282，体=fun _ => TUAPYYU_concl）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.YEBWJNG_discharged | LocalConcl.lean:1258 | 装配出口 | — | 同上 | 不可接·循环再出口（C(b)） | LA25.YEBWJNG_p25（LA25:1584）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.WKZZEEH_discharged | LocalConcl.lean:1270 | 装配出口 | — | 同上 | 不可接·循环再出口（C(b)） | LA25.WKZZEEH_p25（LA25:1418）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.PWEIWBZ_discharged | LocalConcl.lean:1282 | 装配出口 | — | 同上 | 不可接·循环再出口（C(b)） | LA25.PWEIWBZ_p25（LA25:1561）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.VASYYAU_discharged | LocalConcl.lean:1294 | 装配出口 | — | 同上 | 不可接·循环再出口（C(b)） | LA25.VASYYAU_p25（LA25:1572）；LA32 六处 VASYYAU.hl 提及均 NEEDS 注释非孪生；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.WKEIDFT_discharged | LocalConcl.lean:1309 | 装配出口 | — | 同上（实测 LA24:150-151） | 不可接·循环再出口（C(b)） | LA24.WKEIDFT_concl_p24（LA24:146，体=WKEIDFT_concl）；v2 WKEIDFT/WKEIDFT_EQU 孪生仍 sorried；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.PEDSLGV1_discharged | LocalConcl.lean:1320 | 装配出口 | — | 同上（实测 LA20:739-742） | 不可接·循环再出口（C(b)） | LA20.PEDSLGV1（LA20:739，体=PEDSLGV1_concl 调用）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.PEDSLGV2_discharged | LocalConcl.lean:1327 | 装配出口 | — | 同上（实测 LA20:819-822） | 不可接·循环再出口（C(b)） | LA20.PEDSLGV2（LA20:819）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.OIQKKEP_discharged | LocalConcl.lean:1335 | 装配出口 | — | 同上 | 不可接·循环再出口（C(b)） | LA26.OIQKKEP_p26（LA26:768，exact OIQKKEP_concl）；同形？同形但同上 | m1asm-w1/CLASSIFY |
| Kepler.Text.YXIONXL2_discharged | LocalConcl.lean:1346 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行71） | 根=LA33:120 自体 sorry（m1-ledger:43721 M1-LocalAuto簇）；债集中单根，填根自愈；kit=kit-yxionxl2-debtwire | 搬债·B（kit 在册待编译窗） | YXIONXL2_p33（LocalAuto33.lean:119）；同形？同形（仅 binder 名差；3<s.k 已随 SF-67 归正，出口 docstring 滞后失实） | m1asm-w1/CLASSIFY |
| Kepler.Text.SYNQIWN_discharged | LocalConcl.lean:1378 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行74） | 根=LA22:1478 自体 sorry（m1-ledger:43380 M1-LocalAuto簇）；kit=kit-synqiwn-debtwire | 搬债·B（kit 在册待编译窗） | SYNQIWN_p22（LocalAuto22.lean:1466）；同形？同形（六路 hears 序+三槽上限+结论逐字；SF-70 归正后；docstring 滞后失实） | m1asm-w1/CLASSIFY |
| Kepler.Text.CQAOQLR_discharged | LocalConcl.lean:1398 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行75） | 根=LA16:1002 自体 sorry（m1-ledger:43212 M1-LocalAuto簇）；kit=kit-cqaoqlr-debtwire | 搬债·B（kit 在册待编译窗） | CQAOQLR_p16（LocalAuto16.lean:1001，型=Prop-def CQAOQLR_concl_p16 LA16:907）；同形？同形（def 体逐字=出口陈述；SF-72 归正后；docstring 滞后失实） | m1asm-w1/CLASSIFY |
| Kepler.Text.JLXFDMJ_discharged | LocalConcl.lean:1416 | 装配出口 | — | 缺口=mod-transfer 真桥；通道=SF 陈述统一裁决（向孪生形归正）或 mod-transfer 引理证填 | 不可接（C） | JLXFDMJ_p27（LocalAuto27）；同形？异形：孪生吃 j % s.k ∉ scsM s，注册表 j ∉ scsM s；mod 越界传递（i+1 在 i=k-1… | m1asm-w1/CLASSIFY |
| Kepler.Text.LFLACKU_discharged | LocalConcl.lean:1428 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行76） | 根=LA23:312 自体 sorry（m1-ledger:43426 **M0-直源 C2**，W5-C尾）——债集中至已在账 M0 件，M0 计数不变；kit=kit-lflacku-debtwire | 搬债·B（kit 在册待编译窗） | LFLACKU_p23（LocalAuto23.lean:310）；同形？同形（binder 名差 (h :) vs →；SF-74 归正为 JOTSWIX {3I1}→∅ 正本形；docst… | m1asm-w1/CLASSIFY |
| Kepler.Text.QKNVMLB1_discharged | LocalConcl.lean:1453 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行64） | 根=LA35:641 体 sorry ← QKNVMLB1_LE4F_p35 LA35:611 + QKNVMLB1_EQ4F_p35 LA35:624（m1-ledger:43816-43818 M1）；kit 需加 import LocalAuto35（现 import 面无 LA35）；kit=kit-qknvmlb1-debtwire | 搬债·B（kit 在册待编译窗） | QKNVMLB1_p35（LocalAuto35.lean:634）；同形？同形（索引约定已按 RULING 2026-09-21 IV 对齐孪生形；差=孪生 s'/vv' 显式带方程 bind… | m1asm-w1/CLASSIFY |
| Kepler.Text.QKNVMLB2_discharged | LocalConcl.lean:1469 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行67） | 根=LA35:887 自体 sorry（m1-ledger:43819 M1）；需 import LocalAuto35；kit=kit-qknvmlb2-debtwire | 搬债·B（kit 在册待编译窗） | QKNVMLB2_p35（LocalAuto35.lean:878）；同形？同形（差=tuple 方程 (s',s'')=scsSliceV39... vs 孪生两 half-slice 方程；… | m1asm-w1/CLASSIFY |
| Kepler.Text.QKNVMLB3_discharged | LocalConcl.lean:1556 | 装配出口 | [propext, sorryAx, Classical.choice, Quot.sound]（twinprobe 行68） | 根=QKNVMLB3_LE4_p35 LA35:1248 + QKNVMLB3_Eq4_p35 LA35:1276（m1-ledger:43826/43827 M1）；需 import LocalAuto35；kit=kit-qknvmlb3-debtwire | 搬债·B（kit 在册待编译窗） | QKNVMLB3_p35（LocalAuto35.lean:1285，本体已证 rcases 分支组合）；同形？同形（同上 tuple 桥） | m1asm-w1/CLASSIFY |

### 2.3 LocalConcl anchor 注入 2 处（非出口·在账）

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根/缺口 | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.mnt11_anchor（非出口-在账） | LocalConcl.lean:487 | 装配出口 | sorryAx 直 | 接口锚服务已接线 WIRE 件（mnt11 E 件 LA1:815 的装配面镜像），随 LA1 mnt11 根闭合 | 非出口·在账锚 | —；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.p21_anchor（非出口-在账） | LocalConcl.lean:493 | 装配出口 | sorryAx 直 | 同上（LA21 p21 银行锚，服务 CUXVZOZ/CJBDXXN 已接线件） | 非出口·在账锚 | —；同形？— | m1asm-w1/CLASSIFY |

### 2.4 SF-63/69/71/73 已落库接线 4 件（孪生面复核，TP 种子）

> SF-69（`2f38b757`）唯一真净接线；63/71/73 搬债口径独立复核成立。SF-63/71/73 kit
> 预验证三件全过（sf6373debt-w1，基线 `8c451a6d`，在册待裁决 B）。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.VPWSHTO_PRIME_p15 | LocalAuto15.lean:487 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | refine到master VPWSHTO_p15 自体sorry LA15:409 | 不可接(与编排者裁定一致) | —(复核=CONFIRMED种子) | twinprobe-w1/种子复核-SF-63 |
| Kepler.Text.TBRMXRZ1_p22 | LocalAuto22.lean:659 | 孪生/链面（SF-63/69/71/73 已落库复核） | 标准三 | 无 | 可接线(已落库 commit 2f38b757) | —(复核=CONFIRMED种子) | twinprobe-w1/种子复核-SF-69 |
| Kepler.Text.XWNHLMD_p26 | LocalAuto26.lean:795 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 本体真证无自sorry(吃XWNHLMD_MM_p26 LA26:806); 链:MM_p26(LA26:786本体真证)→SGTRNAF_p27(LA27:568本体真证)→UXCKFPE2_p27(LA27:546本体真证)→UXCKFPE_p24(LA24:1395组合)→根=XWITCCN_CASE_3/4/5/6_IS_SCS_p24 sorry LA24:1387/1128/1163… | 不可接(与编排者裁定一致) | —(复核=CONFIRMED种子) | twinprobe-w1/种子复核-SF-71 |
| Kepler.Text.XWNHLMD_MM_p26 | LocalAuto26.lean:786 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 本体真证无自sorry(吃TAUSTAR_LE_0_XWNHLMD_p26 LA26:703-705+SGTRNAF_p27); 根同上LA24 case bank | 不可接 | — | twinprobe-w1/种子复核-SF-71-kernel |
| Kepler.Text.OEHDBEN | LocalAuto20.lean:1480 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 本体纯组合(LA20:1483-1497 吃AQICLXA+FZIOTEF+OEHDBEN_PRIME); 根=AQICLXA sorry LA20:986(←AQICLXA_SLICE sorry LA20:957) + FZIOTEF sorry LA20:1008(←FUNOUYH_SLICE sorry LA20:999) + OEHDBEN_PRIME←SCS_6I1_BERAK_BY… | 不可接(与编排者裁定一致) | —(复核=CONFIRMED种子) | twinprobe-w1/种子复核-SF-73 |
| Kepler.Text.OEHDBEN_PRIME | LocalAuto20.lean:1462 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 本体组合(LA20:1466-1474 吃SCS_6I1_BERAK_BY_CSTAB); 根=BERAK自体sorry LA20:1221 | 不可接 | — | twinprobe-w1/种子复核-SF-73链 |
| Kepler.Text.AQICLXA | LocalAuto20.lean:984 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 自体sorry LA20:986; 深根=AQICLXA_SLICE sorry LA20:957 (QKNVMLB kit挡) | 不可接(波2*待SLICE) | — | twinprobe-w1/种子复核-SF-73链 |
| Kepler.Text.FZIOTEF | LocalAuto20.lean:1006 | 孪生/链面（SF-63/69/71/73 已落库复核） | sorryAx | 自体sorry LA20:1008; 深根=FUNOUYH_SLICE sorry LA20:999 | 不可接(波2*待SLICE) | — | twinprobe-w1/种子复核-SF-73链 |

### 2.5 PackingConcl 8 件（M1 CLASSIFY，基线 `851e1b49`）

> 全 C：TWIN MISMATCH 4（XYOFCGX/IVFICRK→SF-78/79 在册；GOTCJAH/RVFXZBU3）、NO TWIN 2、
> self-loop 1、OXLZLEZ 已接线无动作 1。8 件/9 处（OXLZLEZ 单行双 sorry）。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根/缺口 | 判词 | 备注（孪生/同形） | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.XYOFCGX_concl_discharged | PackingConcl.lean:226 | 装配出口 | — | 缺口=接口加前提 SF 裁决（registry 形 vs 孪生形二选一）；通道=SF STATEMENT-FIX | 不可接（C） | PA7.XYOFCGX（Rogers.hl:6559）；同形？异形：孪生需 Packing V 前提，接口不带（XYOFCGX_*_0 案件引理同） | m1asm-w1/CLASSIFY |
| Kepler.Text.IVFICRK_concl_discharged | PackingConcl.lean:308 | 装配出口 | — | 缺口=接口/孪生强弱裁决+补证；通道=SF | 不可接（C） | PA7.IVFICRK（Rogers.hl:9929）；同形？异形：孪生第二合取支多两前提（i∈Icc 0 (k+1)、permutes σ (Icc 0 k)）——孪生严格弱于接口 | m1asm-w1/CLASSIFY |
| Kepler.Text.MXI_EXISTS_concl_discharged | PackingConcl.lean:337 | 装配出口 | — | 缺口=由 barV V 3 ul 导出 ul=[u0,u1,u2,u3]（BARV_3_EXPLICIT 可导）的真证填；通道=小证填 kit（非接线） | 不可接·自环（C） | 无可用（唯一下游载体 PA12.MXI_EXPLICIT 自环消费本接口；SF-37 前提已补）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.RVFXZBU1_concl_discharged | PackingConcl.lean:380 | 装配出口 | — | 缺口=上游件缺位（Auto10 波未落地）；通道=PA10/PA13 port 证填 | 不可接（C） | 无（Auto3-25 无下游陈述；PA13 SLTSTLO2 证注 NEEDS RVFXZBU1 未落地）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.RVFXZBU2_concl_discharged | PackingConcl.lean:388 | 装配出口 | — | 缺口=上游件缺位；通道=port 证填（真新数学） | 不可接（C） | 无（Auto3-25 全域无 permutation-forcing 件）；同形？— | m1asm-w1/CLASSIFY |
| Kepler.Text.RVFXZBU3_concl_discharged | PackingConcl.lean:400 | 装配出口 | — | 缺口=PA10 支证填 + 全 i 桥（真工作）；通道=PA10 波先行再裁 | 不可接（C） | PA10.RVFXZBU（ENCODING-FIX 孪生）；同形？异形：孪生限 i∈{0,1,2,3,4} 且其 i=2,3 支仍 sorried；接口全 i 量化（i≥5 尾窗 [4… | m1asm-w1/CLASSIFY |
| Kepler.Text.OXLZLEZ_concl_discharged | PackingConcl.lean:512 | 装配出口 | 2×sorryAx（:515 单行双 sorry） | 缺口=两 bank 叶证填（= triage PA25 bank E28 族在账）；本波无 kit——现形已是最小债面，改写无净收益 | 已接线·无动作（C） | PA25.OXLZLEZ（capstone，已 term 级接线）；同形？已接线（特殊形：两 bank 叶 pack_nonlinear_non_ox3q1h PA21:147 / ox3q1… | m1asm-w1/CLASSIFY |
| Kepler.Text.GOTCJAH_concl_discharged | PackingConcl.lean:543 | 装配出口 | — | 缺口=真几何桥（PA22 故意不 import）；通道=port 证填裁决 | 不可接（C） | PA22.GOTCJAH（counting_spheres.hl:4366）；同形？异形：编码全不同（fchanged c=WF vs topologicalComponentYfan 成员、asn v… | m1asm-w1/CLASSIFY |

## 3. 波件（编译窗待落）

### 3.1 波 1（LA20/22/23，TP 源 3 + W1A 修订，基线 `a6464251`/`8c451a6d`）

> W1A 修订：3T1/3T5 改道 = 路线 (b)（LA20 直证同款，先例 SCS_6I1/5I1_IS_SCS 净）；
> 生成器直套路线 (a) 否决（funlist REFUTED + 单 d 死端）。四 kit 落库后全部标准三，直源账 −4。
> REFUTED 条 = `is_scs_funlist_basic_p22`（scout 三处「已证✓」翻案）。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.is_scs_3T1_p22 | LocalAuto22.lean:1668 | 波件 | sorryAx | 自体sorry LA22:1669 | 扣留改道:生成器直套路线否决(见funlist行),改LA20直证同款或先灌生成器 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/波1-is_scs_3T1 |
| Kepler.Text.is_scs_3T5_p22 | LocalAuto22.lean:1688 | 波件 | sorryAx | 自体sorry LA22:1689 | 扣留改道:同上 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/波1-is_scs_3T5 |
| Kepler.Text.is_scs_3M1_p22 | LocalAuto22.lean:1703 | 波件 | sorryAx | 自体sorry LA22:1704; 移植源SCS_3M1_IS_SCS实测净 | 放行(整段移植LA20:209路线验净) | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/波1-is_scs_3M1 |
| Kepler.Text.s_init_list_alt_p23 | LocalAuto23.lean:318 | 波件 | sorryAx | 自体sorry LA23:321 (叶上自sorry,无传递历史); 依赖periodic2_funlist_p20/PSORT_5_EXPLICIT实测净 | 放行 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/波1-s_init_list_alt |
| Kepler.Text.is_scs_funlist_basic_p22 | LocalAuto22.lean:1333 | 波件（依赖/先例） | sorryAx | 自体sorry LA22:1347 | 先行件:波1若走生成器须先灌证本体,否则必带sorryAx入闸 | REFUTED(la2027-scout报告+dep-map记「已证✓」实为sorry)；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/依赖-生成器 |
| Kepler.Text.SCS_3M1_IS_SCS | LocalAuto20.lean:209 | 波件（依赖/先例） | 标准三 | 无 | 净(3M1移植源验净) | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/依赖-移植源 |
| Kepler.Text.periodic2_funlist_p20 | LocalAuto20.lean:199 | 波件（依赖/先例） | 标准三 | 无 | 净 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/依赖 |
| Kepler.Text.PSORT_5_EXPLICIT | LocalAuto20.lean:61 | 波件（依赖/先例） | 标准三 | 无 | 净(零公理) | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/依赖 |
| Kepler.Text.SCS_BASIC_TAUSTAR_p26 | LocalAuto26.lean:684 | 波件（依赖/先例） | 标准三 | 无 | 净(XWNHLMD链此支路排除) | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/依赖-XWNHLMD支路 |
| Kepler.Text.SCS_6I1_IS_SCS | LocalAuto20.lean:181 | 波件（依赖/先例） | 标准三 | 无(=is_scs_6I1_p22 LA22:994转发) | 净(直证先例路线验净) | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/3T5改道 |
| Kepler.Text.SCS_5I1_IS_SCS | LocalAuto20.lean:396 | 波件（依赖/先例） | 标准三 | 无(=is_scs_5I1_p22 LA22:1004转发) | 净 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/3T5改道 |
| Kepler.Text.BKOSSGE_p16 | LocalAuto16.lean:254 | 波件（依赖/先例） | sorryAx | 本体真证(自body 0 sorry,LA16:258-279实构造); 根=is_scs_3T1/3T5/3M1_p22 sorry LA22:1669/1689/1704 + XWNHLMD_MM_p26链→LA24 case bank sorry LA24:1387/1128/1163/1196 | 波1三R件闭后isScs半自愈;MMs半仍欠XWNHLMD族 | —；w1asm-w2：3T1/3T5 改道路线(b)、funlist 降级 kit4 | twinprobe-w1/下游-红利件 |

### 3.2 波 2 主清单与支撑件（W2P，基线 `aacaf3e5`）

> 五件主清单不消费波 1 四件（零硬依赖）；case bank 四件落地即 UXCKFPE 五族 cone 自愈
> （**打折条款 = SF-81**：`scsToStableSy_p23.stable := sorry` 常量级污染不解则 axiom 面不净，CB 取证）。
> 翻案①：EAPGLE 闸 = case bank + 总装双前置（AYQJTMD 链）；翻案②：通用 HDPLYGY 树内不存在
> （CB 已分层移植：EVT 核/端口主件/两还原件 CLEAN + 4 NEEDS 腿）。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.UXCKFPE_p24 | LocalAuto24.lean:1395 | 波件/根件 | sorryAx | 本体组合已证(LA24:1397-1404 rcases); 根=XWITCCN_CASE_3/4/5/6_IS_SCS_p24 自体sorry LA24:1387/1128/1163/1196 | 本体复用件; case bank落后cone自愈 | — | la2027-w2prep/probeA |
| Kepler.Text.XWITCCN_CASE_4_IS_SCS_p24 | LocalAuto24.lean:1124(sorry:1128) | 波件/根件 | sorryAx | 自体叶sorry, 无传递历史 | kit2 (NEEDS-WINDOW, M级真数学; 链况全图见kit2 §0) | — | la2027-w2prep/probeA |
| Kepler.Text.XWITCCN_CASE_5_IS_SCS_p24 | LocalAuto24.lean:1159(sorry:1163) | 波件/根件 | sorryAx | 自体叶sorry | kit3 (NEEDS-WINDOW, CASE_4镜像) | — | la2027-w2prep/probeA |
| Kepler.Text.XWITCCN_CASE_6_IS_SCS_p24 | LocalAuto24.lean:1192(sorry:1196) | 波件/根件 | sorryAx | 自体叶sorry | kit4 (NEEDS-WINDOW, CASE_4镜像) | — | la2027-w2prep/probeA |
| Kepler.Text.XWITCCN_CASE_3_IS_SCS_p24 | LocalAuto24.lean:1383(sorry:1387) | 波件/根件 | sorryAx | 自体叶sorry | kit5 (NEEDS-WINDOW, 最重; 八件链全sorried) | — | la2027-w2prep/probeA |
| Kepler.Text.FINITE_J1_TS_p24 | LocalAuto24.lean:1259 | 波件（含支撑净件） | 标准三 | 无 | 净, CASE_3链直接复用 | CONFIRMED(scout称已证→验证属实) | la2027-w2prep/probeA |
| Kepler.Text.tri_sy_explicit_p24 | LocalAuto24.lean:1290 | 波件（含支撑净件） | 标准三 | 无 | 净, CASE_3链直接复用 | CONFIRMED(scout称已证→验证属实) | la2027-w2prep/probeA |
| Kepler.Text.CONTINUOUS_ON_D_FUN3_p24 | LocalAuto24.lean:1272(sorry:1283) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_IS_SCS_CASE_3_p24 | LocalAuto24.lean:1206(sorry:1215) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.NOT_EMPTY_CASE_3_IS_SCS_p24 | LocalAuto24.lean:1233(sorry:1241) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_NOT_EMPTY_B1_SY_3_IS_SCS_p24 | LocalAuto24.lean:1220(sorry:1228) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_B_SY1_COLLINEAR_CASE_3_IS_SCS_p24 | LocalAuto24.lean:~1313(sorry:1322) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.HDPLYGY_CASE_30_p24 | LocalAuto24.lean:1328(sorry:1365) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌(CONTINUITY链) | — | la2027-w2prep/probeA |
| Kepler.Text.TAUSTAR_EQ_TAU_STAR_3_IS_SCS_p24 | LocalAuto24.lean:1372(sorry:1377) | 波件（含支撑净件） | sorryAx | 自体sorry | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.NOT_EMPTY_CASE_4_IS_SCS_p24 | LocalAuto24.lean:1098(sorry:1103) | 波件（含支撑净件） | sorryAx | 自体sorry | kit2前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_NOT_EMPTY_B1_SY_4_IS_SCS_p24 | LocalAuto24.lean:1109(sorry:1118) | 波件（含支撑净件） | sorryAx | 自体sorry | kit2前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_IS_SCS_CASE_4_p23 | LocalAuto23.lean:697(sorry:706) | 波件（含支撑净件） | sorryAx | 自体sorry | kit2前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.NOT_EMPTY_CASE_5_IS_SCS_p24 | LocalAuto24.lean:1136(sorry:1141) | 波件（含支撑净件） | sorryAx | 自体sorry | kit3前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_NOT_EMPTY_B1_SY_5_IS_SCS_p24 | LocalAuto24.lean:1145(sorry:1154) | 波件（含支撑净件） | sorryAx | 自体sorry | kit3前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.NOT_EMPTY_CASE_6_IS_SCS_p24 | LocalAuto24.lean:1169(sorry:1174) | 波件（含支撑净件） | sorryAx | 自体sorry | kit4前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IN_NOT_EMPTY_B1_SY_6_IS_SCS_p24 | LocalAuto24.lean:1178(sorry:1187) | 波件（含支撑净件） | sorryAx | 自体sorry | kit4前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IS_SCS_STABLE_SYSTEM_p23 | LocalAuto23.lean:597(sorry:600) | 波件（含支撑净件） | sorryAx | 自体sorry(torsor展开) | kit2-4共同前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.IS_SCS_TRI_STABLE_SYSTEM_p23 | LocalAuto23.lean:604(sorry:608) | 波件（含支撑净件） | sorryAx | 自体sorry(torsor k=3) | kit5前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_4_p23 | LocalAuto23.lean:712(sorry:716) | 波件（含支撑净件） | sorryAx | 自体sorry | kit2前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_5_p23 | LocalAuto23.lean:768(sorry:772) | 波件（含支撑净件） | sorryAx | 自体sorry | kit3前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.TAUSTAR_EQ_TAU_STAR_IS_SCS_CASE_6_p23 | LocalAuto23.lean:815(sorry:819) | 波件（含支撑净件） | sorryAx | 自体sorry | kit4前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.V_E_FF_IS_SCS_CASES_4_p23 | LocalAuto23.lean:688(sorry:693) | 波件（含支撑净件） | sorryAx | 自体sorry | kit2前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.V_E_FF_IS_SCS_CASES_5_p23 | LocalAuto23.lean:746(sorry:751) | 波件（含支撑净件） | sorryAx | 自体sorry | kit3前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.V_E_FF_IS_SCS_CASES_6_p23 | LocalAuto23.lean:793(sorry:798) | 波件（含支撑净件） | sorryAx | 自体sorry | kit4前置待灌 | — | la2027-w2prep/probeA |
| Kepler.Text.EAPGLE_p27 | LocalAuto27.lean:867(sorry:869) | 波件（含支撑净件） | sorryAx | 自体sorry; 消费ZITHLQN总装+AYQJTMD_p27 | kit1(胶合已验; 总装NEEDS-WINDOW; 闸受case bank牵制=翻案①) | — | la2027-w2prep/probeA |
| Kepler.Text.AYQJTMD_p27 | LocalAuto27.lean:861 | 波件（含支撑净件） | sorryAx | 本体已证无自sorry; 链=SGTRNAF_p27(LA27:564)→UXCKFPE2_p27(LA27:546)→UXCKFPE_p24(LA24:1395)→case bank 4 sorry | kit1闸必须等case bank(翻案①) | REFUTED(scout dep-map记「AYQJTMD_p27✓」作EAPGLE唯一深前置=口径不完整; twi… | la2027-w2prep/probeA |
| Kepler.Text.UXCKFPE2_p27 | LocalAuto27.lean:546 | 波件（含支撑净件） | sorryAx | 本体已证; 链=UXCKFPE_p24→case bank | case bank落后自愈 | CONFIRMED(twinprobe:19同链) | la2027-w2prep/probeA |
| Kepler.Text.SGTRNAF_p27 | LocalAuto27.lean:564 | 波件（含支撑净件） | sorryAx | 本体已证; 链=UXCKFPE2_p27→case bank | case bank落后自愈 | CONFIRMED(twinprobe:20同链) | la2027-w2prep/probeA |
| Kepler.Text.s_init_scs_p27 | LocalAuto27.lean:~730 | 波件（含支撑净件） | 标准三 | 无 | 净(EAPGLE消费件; 注意≠波1的s_init_list_alt_p23) | CONFIRMED(twinprobe:20「非污染源」判词直证) | la2027-w2prep/probeA |
| Kepler.Text.S_INIT_IS_UNADORNED_p27 | LocalAuto27.lean | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.unadorned_MMs_p27 | LocalAuto27.lean | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.ZITHLQN_concl | LocalAuto1.lean:651(sorry:654) | 波件（含支撑净件） | sorryAx | 自体sorry(HOL ZITHLQN总装未移植) | kit1前置=总装落点两案(LA25推荐/LA1)待编排者裁 | — | la2027-w2prep/probeA |
| Kepler.Text.ZITHLQN_p25 | LocalAuto25.lean:1004 | 波件（含支撑净件） | sorryAx | 本体零内容=re-export := ZITHLQN_concl h(LA1:651 sorry) | 总装落位候选一(推荐) | CONFIRMED(scout「re-export缺位」判词) | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_3_p25 | LocalAuto25.lean:431 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED(scout八CASE全证→验证属实且净) | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_4_p25 | LocalAuto25.lean:668 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_5_p25 | LocalAuto25.lean:694 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_6_p25 | LocalAuto25.lean:720 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_4_3_p25 | LocalAuto25.lean:912 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_5_sqrt8_p25 | LocalAuto25.lean:939 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_5_pro_cs_p25 | LocalAuto25.lean:876 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.ZITHLQN_CASE_4_pro_cs_p25 | LocalAuto25.lean:968 | 波件（含支撑净件） | 标准三 | 无 | 净, 总装输入 | CONFIRMED | la2027-w2prep/probeB |
| Kepler.Text.YXIONXL3 | LocalAuto12.lean:1220 | 波件（含支撑净件） | 标准三 | 无 | 净, kit6/7 helper输入 | CONFIRMED(scout半箭头就绪→验证属实) | la2027-w2prep/probeA |
| Kepler.Text.PROP_EQU_IS_SCS | LocalAuto12.lean:579 | 波件（含支撑净件） | 标准三 | 无 | 净 | CONFIRMED | la2027-w2prep/probeA |
| Kepler.Text.PRO_EQU_ID | LocalAuto12.lean:981 | 波件（含支撑净件） | 标准三 | 无 | 净 | CONFIRMED | la2027-w2prep/probeA |
| Kepler.Text.PRO_EQU_ID1 | LocalAuto12.lean:1006 | 波件（含支撑净件） | 标准三 | 无 | 净(helper幂等塌缩件) | CONFIRMED | la2027-w2prep/probeA |
| Kepler.Text.FZIOTEF_TRANS | LocalAuto1.lean:990 | 波件（含支撑净件） | 标准三 | 无 | 净, kit6/7装配输入 | CONFIRMED | la2027-w2prep/probeA |
| Kepler.Text.FZIOTEF_UNION | LocalAuto20.lean:965 | 波件（含支撑净件） | 标准三 | 无 | 净, kit6装配输入 | CONFIRMED | la2027-w2prep/probeA |
| Kepler.Text.SCS_3M1_IS_SCS | LocalAuto20.lean:209 | 波件（含支撑净件） | 标准三 | 无 | 净 | CONFIRMED(twinprobe:90同) | la2027-w2prep/probeA |
| Kepler.Text.SCS_5M1_IS_SCS | LocalAuto20.lean:267 | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.SCS_4M2_IS_SCS | LocalAuto20.lean:335 | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.K_SCS_3M1 | LocalAuto20.lean:592 | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.K_SCS_5M1 | LocalAuto20.lean:601 | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.K_SCS_4M2 | LocalAuto20.lean:616 | 波件（含支撑净件） | 标准三 | 无 | 净 | — | la2027-w2prep/probeA |
| Kepler.Text.LKGRQUI_concl | LocalAuto1.lean:~1692 | 根件 | sorryAx | 自体sorry | SLICE深根, QKNVMLB波接口 | CONFIRMED(twinprobe:27/:72同) | la2027-w2prep/probeA |

### 3.3 波 2 kit-check（W2P 车道内验针，非树内声明）

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| (本车道kit-check) | probeC_w2star_assembly.lean | 波件（本车道 kit-check，非树内声明） | 标准三（kit-check） | 无 | 新helper验净; kit6/7落位为private halfArrow_w2 | — | la2027-w2prep/probeC-kit |
| (本车道kit-check, SLICE假设形) | probeC_w2star_assembly.lean | 波件（本车道 kit-check，非树内声明） | 标准三（kit-check） | 无 | kit6装配端到端验净; SLICE灌证即净 | — | la2027-w2prep/probeC-kit |
| (本车道kit-check, SLICE假设形) | probeC_w2star_assembly.lean | 波件（本车道 kit-check，非树内声明） | 标准三（kit-check） | 无 | kit7装配端到端验净; SLICE灌证即净 | — | la2027-w2prep/probeC-kit |
| (本车道kit-check, real-form) | probeC_w2star_assembly.lean | 波件（本车道 kit-check，非树内声明） | sorryAx | 唯一链=AQICLXA_SLICE自体sorry LA20:957 | SLICE灌证条件位取证 | — | la2027-w2prep/probeC-kit |
| (本车道kit-check, real-form) | probeC_w2star_assembly.lean | 波件（本车道 kit-check，非树内声明） | sorryAx | 唯一链=FUNOUYH_SLICE自体sorry LA20:999 | SLICE灌证条件位取证 | — | la2027-w2prep/probeC-kit |
| (本车道kit-check, ZITHLQN假设形) | probeA_casebank_eapgle.lean | 波件（本车道 kit-check，非树内声明） | sorryAx | 唯一链=AYQJTMD_p27→case bank(非ZITHLQN!) | EAPGLE闸=case bank+总装双前置 | 翻案①取证 | la2027-w2prep/probeA-kit |
| (本车道kit-check, real-form) | probeA_casebank_eapgle.lean | 波件（本车道 kit-check，非树内声明） | sorryAx | ZITHLQN_concl自体+AYQJTMD链 | kit1闸排case bank后 | — | la2027-w2prep/probeA-kit |

## 4. 根件（污染根集合）

### 4.1 锥外孪生侧根（TP 源 2：SF-64~74 孪生，基线 `a6464251`）

> LA35 组（SF-64/65/66）= QKNVMLB 波根；YXIONXL2_p33/LKGRQUI_p27/SYNQIWN_p22/CQAOQLR_p16/
> LFLACKU_p23 = m1asm B 批七 kit 的根（LFLACKU 根 LA23:312 = **M0 直源 C2**，W5-C 尾）。
> SF-67（k=3 忠实形 3<s.k）已裁 corpus 外新数学不接。

| 声明全名 | 文件:行 | 类别 | axiom 面 | 污染根（文件:行） | 判词 | 备注 | 台账来源 |
|---|---|---|---|---|---|---|---|
| Kepler.Text.QKNVMLB1_p35 | LocalAuto35.lean:634 | 根件（锥外孪生侧） | sorryAx | 自体sorry占位 LA35:641 (受阻于LE4F/EQ4F); 根=QKNVMLB1_LE4F_p35 sorry LA35:611 + QKNVMLB1_EQ4F_p35 sorry LA35:624 | 不可接(等LE4F/EQ4F灌证) | — | twinprobe-w1/SF-64 |
| Kepler.Text.QKNVMLB1_LE4F_p35 | LocalAuto35.lean:603 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA35:611 | 不可接(W2/W3真数学债) | — | twinprobe-w1/SF-64-kernel |
| Kepler.Text.QKNVMLB1_EQ4F_p35 | LocalAuto35.lean:616 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA35:624 | 不可接(W2/W3真数学债) | — | twinprobe-w1/SF-64-kernel |
| Kepler.Text.QKNVMLB2_p35 | LocalAuto35.lean:878 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA35:887 | 不可接 | — | twinprobe-w1/SF-65 |
| Kepler.Text.QKNVMLB3_p35 | LocalAuto35.lean:1285 | 根件（锥外孪生侧） | sorryAx | 本体为组合无自sorry; 根=QKNVMLB3_LE4_p35 sorry LA35:1248 + QKNVMLB3_Eq4_p35 sorry LA35:1276 | 不可接(W2/W3) | — | twinprobe-w1/SF-66 |
| Kepler.Text.QKNVMLB3_LE4_p35 | LocalAuto35.lean:1238 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA35:1248 (HOL巨件~965行) | 不可接 | — | twinprobe-w1/SF-66-kernel |
| Kepler.Text.QKNVMLB3_Eq4_p35 | LocalAuto35.lean:1266 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA35:1276 (HOL ~470行) | 不可接 | — | twinprobe-w1/SF-66-kernel |
| Kepler.Text.YXIONXL2_p33 | LocalAuto33.lean:119 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA33:120 (忠实形3<s.k) | 不可接(k=3为corpus外新数学,fixscout已裁) | — | twinprobe-w1/SF-67 |
| Kepler.Text.LKGRQUI_p27 | LocalAuto27.lean:893 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA27:896; 非源:SLICE_IS_UNADORNED_p27实测净; 忠实形装配LKGRQUI_faithful_w1asm未落仓(仅LA1:1692注记) | 不可接(陈述修正已落,装配归w1asm波) | — | twinprobe-w1/SF-68 |
| Kepler.Text.SLICE_IS_UNADORNED_p27 | LocalAuto27.lean:888 | 根件（锥外孪生侧） | 标准三 | 无 | 净(排除污染源) | — | twinprobe-w1/SF-68支路 |
| Kepler.Text.SYNQIWN_p22 | LocalAuto22.lean:1466 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA22:1478 | 不可接 | — | twinprobe-w1/SF-70 |
| Kepler.Text.CQAOQLR_p16 | LocalAuto16.lean:1001 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA16:1002 (CQAOQLR_concl_p16为def LA16:907不可直探,测其消费者) | 不可接(等W1装配波) | — | twinprobe-w1/SF-72 |
| Kepler.Text.LFLACKU_p23 | LocalAuto23.lean:310 | 根件（锥外孪生侧） | sorryAx | 自体sorry LA23:312 | 不可接(等taum桥/TAUM kit,波3) | — | twinprobe-w1/SF-74 |

### 4.2 (c1) 切换日新进锥 27 行（RR 子锥精算，基线 `725699f4`；行级锚见 TP 源 1 污染根列）

| 模块 | 行数 | 明细（根件） | 文件:行（TP/RR） | 兑现波 |
|---|---:|---|---|---|
| LA18 | 5 | SCS_5I1_SLICE_02_p18、SCS_5I2_SLICE_02_p18、SCS_5M1_SLICE_02_p18、SCS_5M1_SLICE_03_p18、SCS_5M1_SLICE_24_p18 | LA18:1047-1053 / 1056-1062 / 1064-1070 / 1072-1078 / 1080-1086（TP 源1 CNICGSF1-5 行） | triage 波 1（LKGRQUI slice 族）；另 LA18 侧 5 处改引已证 YXIONXL3 再 −1 |
| LA24 | 4 | OTMTOTJ1/2/3/4_p24 骨架占位 | LA24:1045/1053/~1060/~1069 | w1asm/a2 case-bank 波 |
| LA29 | 1 | HIJQAHA_p29 | LA29:2567 | SCS_5M3 slice 族 |
| LA32 | 3 | NWDGKXH_p32、YOBIMPP_p32、MIQMCSN_p32 | LA32:870/1082/1379 | farm 面（吃 mnt11_anchor，根闭后 anchor 行仍在） |
| LA33 | 11 | ARDBZYE_p33、FYSSVEV_p33、SCS_4I1_SLICE_02_p33、SCS_4M2_SLICE_13_p33、SCS_4M3_SLICE_13_p33、SCS_4M4_SLICE_02_p33、SCS_4M4_SLICE_13_p33、SCS_4M5_SLICE_13_p33、OPP_IS_SCS_p33、XWNHLMD_MM_p33、YXIONXL2_p33 | LA33:1285/1506/1515-1516/2032/2213/2347/2354/2536/126/行 UNRESOLVED/119-120 | slice farm + OPP/XWNHLMD 链（SF-73 邻接面） |
| LA17 | 1 | YRTAFYH_p17 | LA17:1036 | 经 LA33 STAB_SCS 链 |
| LA1 | 1 | YXIONXL3_concl | LocalAuto1.lean（行 UNRESOLVED；净出口 YXIONXL3_discharged 已在且 CLEAN） | LA18 侧改引即 −1 |
| LocalConcl | 1 | `_private…mnt11_anchor` | LocalConcl.lean:487 | terminal bank（SF-73 mnt11 银行闭时单点兑现） |

> 账式：151 − 21（LA1 `_concl` 出锥）+ 27（新行）= **157**；共用 16 行（LA20
> AQICLXA/FZIOTEF/SCS_6I1_BERAK_BY_CSTAB、LA1 WKEIDFT_concl/main_nonlinear_terminal_v11、
> LA27 EAPGLE_p27、LA22 OCBICBY_p22 与 is_scs_3{M1,T1,T5}_p22、LA23 LFLACKU_p23/
> s_init_list_alt_p23、LA24 XWITCCN_CASE_{3,4,5,6}_IS_SCS_p24）无 delta。

### 4.3 锥外根·其余（仅在 §2.1 污染根列出现的孪生侧直 sorry，未单独立行）

LA36:2524（XWITCCN）、LA23:948/956/968（JKQEWGV1-3）、LA14:1068（ZLZTHIC）、
LA30:1212（UAGHHBM）、LA28:2354/2340/2321（ODXLSTCv2/IMJXPHRv2/NUXCOEAv2）、
LA11:1360（PQCSXWG1，无已证 mkSimplex1 距离恒等式）、LA11:1381/1397（PQCSXWG2_ATREAL_p11）、
LA27:896（LKGRQUI）/880（FEKTYIY）/869（EAPGLE）/483（JCYFMRP）/321（TFITSKC）、
LA18:1004（AURSIPD case 库）、LA26:779/764/565/343（PPBTYDQ/MXQTIED/AXJRPNC/RRCWNSJ）、
LA37:1042（MHAEYJN，prop-def 已建未灌）、LA21:1161（general_482_deformation_p21 巨件）、
LA25:1165（ASSWPOW，HOL 原证未移植）、LA15:409（VPWSHTO_p15，SF-63 根）、
LA20:957（AQICLXA_SLICE）/999（FUNOUYH_SLICE）/1221（SCS_6I1_BERAK_BY_CSTAB，mnt11 银行）、
LA22:1347（funlist）/1478（SYNQIWN）/1669/1689/1704（is_scs_3T1/3T5/3M1）、LA16:1002（CQAOQLR）、
LA23:312（LFLACKU，M0-C2）、LA23:321（s_init_list_alt 叶 sorry）、LA35:611/624/641/887/1248/1276（QKNVMLB 组）、
LA33:120（YXIONXL2）/523-524（GSXRFWM1_p33）、LA24 case bank 四根（LA24:1387/1128/1163/1196）、
mnt11_anchor（LocalConcl:487）、p21_anchor（LocalConcl:493）。
LA20 出口侧已证可复用净件：SCS_3M1/5M1/4M2_IS_SCS、K_SCS_3M1/5M1/4M2、FZIOTEF_TRANS/UNION、
periodic2_funlist_p20、PSORT_5_EXPLICIT（零公理）、SCS_BASIC_TAUSTAR_p26（W2P/TP 双探一致）。

## 5. 冲突与 UNRESOLVED 记录

**多源同声明不一致（已按最新探针裁决，备注列留痕）：**

| # | 声明 | 冲突 | 裁决 |
|---|---|---|---|
| 1 | `Kepler.Text.SCS_3M1_IS_SCS` | TP:90 与 W2P:54 双探 | 一致（标准三），无冲突，双源并记 |
| 2 | `is_scs_funlist_basic_p22` | la2027-scout 报告/dep-map 记「已证✓」×3 处 vs TP:89 实测 SORRYAX | **REFUTED 翻案成立**（以 TP 为准）；W1A 改道路线 (b) 落档 |
| 3 | `AYQJTMD_p27` 深前置 | scout dep-map 记「AYQJTMD_p27✓ = EAPGLE 唯一深前置」vs W2P:32 实测 SORRYAX（链→case bank） | **REFUTED 翻案①成立**：EAPGLE 闸 = case bank + 总装双前置 |
| 4 | `XWITCCN2` 孪生 | 前档 TSV「已证」乐观注记 vs TP:19 实测 SORRYAX（已证≠sorry-free） | 以 TP 为准，注记作废 |
| 5 | (c1) 切换日净行数 | sf78draft 估「净 +2~+4」vs RR 子锥精算「净 +6」（漏计 4 个中间链行） | 以 RR（更新、更精）为准：**按 +6 立账** |
| 6 | 通用 HDPLYGY | W2P 翻案②「树内不存在」vs CB 后续「分层移植完成（4 CLEAN + 4 NEEDS 腿）」 | 以 CB（更新）为准：已移植待落库 |
| 7 | `s_init_scs_p27`（净，LA27） vs `s_init_list_alt_p23`（波 1 件，LA23） | 同族异件易混淆 | W2P:35 显式区分：非同件，波 1 件为 `s_init_list_alt_p23` |

**UNRESOLVED（缺数据未补探，留待后续车道）：**

| # | 项 | 缺口 |
|---|---|---|
| U1 | w2probe:36/37（S_INIT_IS_UNADORNED_p27、unadorned_MMs_p27） | 行号未采集（仅 LocalAuto27.lean） |
| U2 | w2probe:60 LKGRQUI_concl = LocalAuto1.lean:~1692；TP:60/61 OTMTOTJ3/4 孪生 = LA24:~1060/~1069；W2P:13 IN_B_SY1_COLLINEAR_CASE_3 = LA24:~1313 | 行号为约数（`~`） |
| U3 | M1 CLASSIFY JLXFDMJ 孪生（LocalAuto27） | 孪生行号未采集 |
| U4 | §4.2 XWNHLMD_MM_p33、YXIONXL3_concl | LA33/LA1 行号未采集 |
| U5 | sfc1c2draft-w1 | 无 DELIVERY/PROGRESS，基线 commit 未自报（patches 3 枚在册） |
| U6 | `LKGRQUI_faithful_w1asm` | 未落仓（仅 LA1:1692 注记，TP:72） |
| U7 | WKEIDFT 净 −1 兑现 | 须 phase-2 栈上移 + LA24 v2 链真证，二者缺一不可（RR §6；今日 HOLD↔HOLD 净 0） |

---

*合成车道：axiomledger-doc-w1（2026-10-28）。生成方式：脚本直转三份 TSV 台账 +
RR/PORT-PLAN/各 DELIVERY 判词手写节；未运行任何 lean/lake/构建。上游台账为准，
本表仅做去重、归类与冲突裁决；行内文字以各来源原文为准（超长截断以 … 标记）。*
