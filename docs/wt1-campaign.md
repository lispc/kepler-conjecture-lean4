# wt1 战役档案 — `nliCell3QZECFICwt1` / `bank_QZECFICwt1`

> 状态：**已关闭**（2026-11-26，`4bcbd7ad`）。SORRIED 49 → 48（47 `nli*` + 1 hLP）。
> 验收：`#print axioms Kepler.Assembly.nliCell3QZECFICwt1` = `[propext, Classical.choice, Quot.sound]`
> （接线前 `[sorryAx]`）；根面 `the_kepler_conjecture_e2e` 仍 589 = 585 native + 标准三 + `sorryAx`
> （剩余 48 条债仍带 sorryAx，故名字集不变）。
> 本文是**战役级**回顾：历程、得失、给未来战役的经验。逐条时间线数字的权威在
> `docs/priority-queue.md` §8（续1537–续1568），本文只引用不另抄；PARITY 细节见
> `~/c17_backup/lane_snapshots/holparity-wt1-value-w1/PARITY_CARD_wt1_value.md`。

---

## 1. 对象与验收

- **义务**：`Kepler.NliBanks21.bank_QZECFICwt1_of_core` 的 `hcore`：
  `∀ y4 y5 y6, 2·hminus ≤ y4 ≤ 2·hplus → 2 ≤ y5 ≤ 2·hminus → 2 ≤ y6 ≤ 2·hminus →
  0 ≤ deltaX (y4²) 2 (y5²) 2 (y6²) 2 → 0 < w1aF y4 y5 y6`
  （`w1aF = w1aG − 0.008·w1aD`，`w1aG/w1aD = yOfX (gamma3fXDivSqrtdelta …) (√2)³ y4 y5 y6`）。
- **HOL 原版**：`ineq.hl:1425`「QZECFIC wt1」；9 个外层 cell；digest
  `theorem_nonlinear_digest.hl:23240-23248`；HOL 侧 total 1,543.027 s + 载入 591.974 s（9 cell，单进程）。
- **收口点**：`Kepler/Assembly.lean` 的 `nliCell3QZECFICwt1 := W1DCAssemblyFinal.wt1_bank`
  （`wt1_bank = Kepler.NliBanks21.bank_QZECFICwt1_of_core wt1_hcore`）。

## 2. 最终形态（四层）

1. **覆盖层**（`Wt1Glue`，`01b7dfd4`，17,983 行 / 2,390 定理）：
   9 个根箱 → 597 个 `x=y²` 分裂树叶 → 173 个合并箱 → **221 个证书箱**
   （137 level-0 + 36 箱细化成 84 叶；`allCerts_length = 221` 由 `rfl` 定死）。
   `root_cover` 无条件（用 `HminusTight18` 的 18 位 `2·hminus` 双侧界）；
   `cover_all_flat : region → ∃ b ∈ allCerts, b.mem`。
   **221 箱与 `refine_t2.json` 的 221 叶按精确有理数双向 0 差**（编排者复算）。
2. **证书层**（221 个 `W1DC_<id>` 模块）：每箱一棵 152/154 节点 DC 树
   （box pass + point pass + part 通道 + T2 终端），全部 `by decide` 门在字面量上；
   8 条 `#print axioms`（`val_facts` 仅 `[propext, Quot.sound]`，其余标准三）。
3. **组装层**（`W1DCAssembly<case>` ×9 + `W1DCAssemblyFinal`，`4cffee15`）：
   每箱 `b.mem → x ∈ D`（floor/ceil 桥）→ `Top_pos` → 按 mode 的 `w1aF = fTop` 桥；
   `wt1_hcore : ∀ y ∈ region, 0 < w1aF`，`wt1_bank : bank_QZECFICwt1`。
4. **接线**（`Assembly.lean:431`，`4bcbd7ad`）：`nliCell3QZECFICwt1 := W1DCAssemblyFinal.wt1_bank`；
   岛协议编译 Assembly RC=0 / 10.03 GB / 0 error。

## 3. 方向演化（重要节点）

| 阶段 | 路线 | 判词 / 转折 |
|---|---|---|
| R0 | Route E（QInterval 403 片） | 403/403 绿，但 **25.7× D1、DC 层 0 条 soundness 引理** ⇒ 只作兜底，不关 wt1 |
| R1 | 联合 Taylor（`w1F2`） | 首盒 577 叶外候选成立，但整盒 diff2c/递归桥未备；`SelectedLeafEvidence` 未构造 ⇒ 不量产 |
| R2 | QInterval 逐节点 / 整树发射 | 289 s/箱 / 36 s/箱×173 ⇒ 超带宽；**证明形态问题不是数学** |
| R3 | **转 DC + T2-only** | `Empty 3.64 s` vs `TV 5.77 s`（+2.13 s/decide）⇒ 外推 0.54–0.72× HOL；D1 684→183→**221** |
| R4 | DC kit（DCKit/DCMatan/DCTaylor2/DCJet） | 算子落库、标准三；`dInv/log2` 的 whnf 雷（PR-62）用 `@[irreducible]` 槽解决 |
| R5 | `Nat.sqrt` 内核不归约 | M6 的 >600 s 爆炸根因；`DCSqrtLit`（sqrt 字面量 + 两条 Nat 平方夹逼）⇒ 0.12 s/节点 |
| R6 | 单箱端到端（M7） | `W1DC15873` 6,139 行、6 条标准三、亲编 27.2 s（多线程口径） |
| R7 | 221 预飞（M8a） | **21/221 过**：196 箱 T2 负（整箱 matan 臂太宽）、8 箱 Dlt 真负 ⇒ 两个 kit 缺口 |
| R8 | 端点 hull（M8b/v2/v3） | 「端点括号 + matan 单调」预测 **221/221**（v3 最小 +1.06e−5）；`DCMatanMono` 落库 |
| R9 | v4 预飞 + 6 样本（M9） | **221/221 PASS**；8 跨零箱走 cross 臂；6/6 样本 146–162 s/箱、标准三 |
| R10 | 量产（A/B/C） | 221/221 数学绿；3 车道 3.9 h；两次外部/平台事故按 PR-65 处置 |
| R11 | 组装 + 接线 | `wt1_hcore`/`wt1_bank` 标准三；`nliCell3QZECFICwt1` 关闭 |
| R12 | PARITY CARD + L1 | 判 **OVER-BAND**（18.28×）；L1（整树 `rfl`）3.3× 提速 ⇒ 单车道投影 5.14×、**实测 6.30×**；用户明批 B 后重发射（`fe1ec17f`） |

## 4. 成本与 PARITY（实测回填）

| 维 | HOL | 原形态 | L1 形态（`mk_l1`；卡 `value-L1-v1`） |
|---|---|---|---|
| D1 义务数 | 619 pass + 610 glue = 1,229 | 221 箱 + 11 glue = 0.357× / 0.018×（PARITY） | 同（结构不变） |
| D2 证书单位 | 每 pass 磁盘 0 B（LCF） | 命名内容 33,265 B/箱（对 154.5 B 下界 = 215×） | **8,144 B/箱（distinct DC 106–190，−75.5%）⇒ 52.7×**（`STRUCTURAL-DIFF`，真下界 UNRESOLVED） |
| D3 源码字节 | 机制 1,655,295 B；生成证书源码 0 B | 物化 145,663,392 B（字面 88.4×） | 物化 **69,058,757 B**；箱 **777,090 行 / 65,404,398 B**（−50.7% 行 / −53.9% 字节）；机制 0.40× PARITY、字面 **42.1×** |
| D4 产物字节 | 0 B proof object（LCF） | 6.43 MB/箱，1,426,091,616 B | **3,162,864–4,819,248 B/箱（均 3,632,744；221 箱 802,836,336 B；含组装 808,972,600 B，−43.3%）**；对四读数下界 8.3–81.9× |
| D5 计算成本 | 1,543.027 s + 载入 591.974 s = 2,135.001 s | 39,028 s ≈ **18.28×**（OVER-BAND） | **13,445.6 s = 6.30×**（三车道并行；单车道投影 10,970 s = 5.14×；墙 77 min = 2.17×） |
| D6 信任 | 0 `new_axiom` | 标准三，零禁造 | 同（1,768 + 11 审计点） |

> 关键读法（来自值函数 PARITY CARD 的订正）：HOL 的 1,543.027 s 是 **total**
> （prep + informal + formal），不是 prep；18.28× 是总量对总量的有效比较。
> D5 不是结构性差距：逐箱归因 tactic 75.7% / 类型检查 4.4%；L1 把 tactic 砍 ~80%，
> 剩余大头是「非根声明面 ~1,200 条 × ~30 ms」。**≤1.2× 在本证书单位下未看到可达路径**
> （DTT 证明项/声明面是结构性下限，对应 D4 的 77.5 KB–440 KB/箱 可实现下界带）。
>
> **L1 卡是上表的数字出处**（`holparity-wt1-l1-backfill-w1/PARITY_CARD_wt1_value_L1.md`，
> `value-L1-v1`）：13,445.6 s / 6.2977× / 802,836,336 B / 777,090 行；**唯一转差 = 峰值
> RSS 均值 +2.2%**（5.948→6.077 GiB，整树 `part` 中间项更大），按 §7.3 记录上报。
> **wt1 不再投入**：杠杆 ①（字面量操作数）反转 D2/D4，②（声明面瘦身）叠加后仍 2.1–2.9×。

## 5. 得（可复用资产）

- **kit（全部标准三）**：`DCKit`（`02b6412b`）、`DCMatan`（`f7a99211`）、`DCTaylor2`（`3cd3927e`）、
  `DCJet`（`c85af7a7`）、`DCSqrtLit`（`33f5054f`）、`HminusTight`（`ee90f65e`）、
  `HminusTight18`（`e8163547`）、`Wt1Glue`（`01b7dfd4`）、`DltCornerWide`（`96ddb1d0`）、
  `W1aFJet`+`W1DCBridge`（`5b00df85`）、`M8Kit`（`503218be`）、`DCMatanMono`（`bc7e7498`）、
  `MatanC1`（`f60a76f7`）。
- **发射链**：`gen_m9.py`（manifest 取数、zero/one 两树、wide 角点、sqrt 字面量、KZ slack、
  桥 rfl）+ `mk_l1.py`（整树 `rfl` 变换）+ `preflight221_v4.py`（门枚举 + 精确 replica）。
- **组装链**：`gen_assembly.py`、9 个 case 模块 + final 的模板、`Assembly.lean` 接线样板。
- **治理产物**：值函数 PARITY CARD、**L1 PARITY CARD**（`holparity-wt1-l1-backfill-w1/`，
  `value-L1-v1`）、L1 探针报告、PR-62/63/64/65；Final 重编与根面审计证据在
  `wt1-l1-close-w1/`（`final_compile.log` + `root_audit.log` + `rootface_min.lean`）。

## 6. 失与勘误（全部机器证据）

1. **我的 `dInv/log2` 爆炸假设是错的**：V0 探针 `dInv/dMul` 链 0.07–0.11 s，无爆炸；
   真因是 `Nat.sqrt` 内核不归约（`DCSqrtLit` 修复；续1554）。
2. **M6 的 `>600 s` 不可复现**（原文日志 0 字节）；可复现的慢点只有 sqrt 门控（续1554 ERRATA）。
3. **M7 的箱不是 221 证书箱**：它是 597 树叶 `15873/RRLLRL`（y4 宽 6e−15 的 zero 薄片）；
   221 轮必须用 `refine_t2.json` 的叶坐标（续1555 ③）。
4. **无条件桥 `∀x∈D, w1aF = fTop` 是假的**：M7 箱 `I4.lo = 2·h0 − 0.52·2^-200 < 2h0`，
   箱内含 pq1 项存活的点；正确形式是精确分解 + `2h0 ≤ x0` 条件桥（续1556 ③，ERRATA 我的工单）。
5. **预飞 17→0**：`compute()` 用落库 `dMatanTight`、发射用 `dMatanTightW`，
   replica 与发射不同步，且 wp 分支域外 ⇒ **gate 通过 ≠ 可编译，两者都必须跑**（续1557 ④）。
6. **「换行解析假阴性」是我误判**：C 车道解析器本就跨行；8 行 FAIL 的真因是
   **olean 6 MB 阈值过拟合**（4 箱 80–100 门、olean 5.94–5.99 MB；`pearson(gates,olean)=0.79`）；
   判据改为 ≥5.5 MB 后 73/73（续1562 ④ ERRATA）。
7. **`⟨A.k, Mhi.lo, Mlo.hi⟩` 跨 dyadic scale 不 sound**：端点括号与箱常在不同 k
   （199/201/200）；自测 hull 得 `[-0.644,-0.515]` vs 真 `[-1.289,-0.258]`；`dRescale` 修复（PR-64）。
8. **wt0 等价关系的常数订正**：`gamma3fXDivSqrtdelta 1 1 1` 的 `1` 是 `m4/m5/m6`，
   `mk456` 把 1–3 槽钉成 `two6=2`（`nb18_indep`）；wt0 = `w1F3O − fNeg2`，与"2→1"无关（续1568）。
9. **并行让单箱变慢 ~23%**（149 → 173–189 s）；3 车道仍划算（3.9 h 总墙 vs 10.9 h 串行）。
10. **同机事故**：兄弟车道清 orphan 误杀在飞编译（外部 SIGTERM 签名：rc=−15、RSS 只剩 shim、
    无 error）；平台 ~60 min 整组杀。规则入册 **PR-65**（只按自己的 `--root` 匹配、分段续跑）。
11. **同对象旧快照被撞见**：wt0 侦察与 2026-11-19 的 `cell3-wt0-scout-w1` 同名；旧件完好、
    新件做了等价复核与 PARITY 预表，未浪费。教训：**派同对象车道前先查快照目录与 campaign §9 卡**。
12. **行数降幅抄了投影值**：账本/档案原写「~782k（−48%）」是「每箱均值×221」外推；落库 221 件
    精确 **777,090 行（−50.68%）/ 65,404,398 B（−53.94%）**。**聚合指标必须逐件复算**
    （续1571 ③）。
13. **「Final 重编」措辞错**：续1570 ② 实际重编的是 `W1DCAssemblyFinal`；`Kepler/Final.olean`
    停在 11-23。已闭环：岛协议重编 Final（6.17 s / 8.32 GB）+ 根面探针重跑，589 规范化逐名同
    （续1571 ④）。**账本里写 Final 必须区分 `W1DCAssemblyFinal` 与 `Kepler/Final`。**

## 7. 给未来 nli 战役的经验（按重要性）

1. **PARITY CARD 先行，且量全六维**。wt1 是"先做完再补卡"，结果 18.28× 被判 OVER-BAND、
   需要用户明批；如果先做卡，会在第一天就改设计（L1）而不是量产后返工。
   **HOL 侧 `total_time` 是总量（含 formal），不要拿 prep 洗白倍率。**
2. **发射成本先量再量产**（PR-61 类）：QInterval 29 min/箱的教训之后，DC 的 4.6 s 是量出来的；
   L1 的 3.3× 也是单箱探针量出来的。**任何形态在 ≥50 箱量产前必须有单箱实测 + 目标带**。
3. **形态问题 ≠ 数学问题**：D5 的 75.7% 是 tactic 执行、4.4% 是类型检查；换形态（整树 `rfl`）
   比换数学便宜一个量级。**先做分量计时归因，再谈优化**。
4. **预飞的 gate 集合必须从发射文本枚举，且 replica 与发射共用一个 plan 对象**（续1557 ④）。
5. **证书精度必须与 cover 设计口径一致**：cover 的 T2 用端点括号 + 单调，证书却用整箱臂
   ⇒ 196/221 假失败。**先对齐口径，再调 cover**（不要先细化 cover）。
6. **内核归约四纪律**：复合项不 `rfl`（一 op 一引理）；`decide` 不展开树（字面量 V/G）；
   跨 dyadic scale 必 `dRescale`；`Nat.sqrt` 永不进内核（字面量 + 平方夹逼）。
   见 PR-62/63/64 与 `DCSqrtLit`/`DCMatanMono`/`MatanC1`。
7. **共享事实源**：同一定理不要在每个箱文件里证一遍（C¹ 五条 → `MatanC1`；wide 角点 → `M8Kit`）；
   量产前先把 box 无关件落库，产物和墙钟都会降。
8. **覆盖是长杆，先做"\u53ef\u884c\u6027 + D1"两件事**：wt1 的 cover 从 684→183→193→221 反复了多轮；
   wt0 的侦察显示 T2 形态 D1 409、而手写 route R 只要 60–150 cell ⇒ **同一对象的 D1 强依赖证书形态**，
   要先选定形态再切 cover。
9. **债务账本口径**：根面 `#print axioms` 的**名字集**在单条 sorry 关闭时不变（sorryAx 仍在）；
   可验收的是**局部定理的 axioms**（`nliCell3QZECFICwt1` 标准三）+ 锥内 sorry 计数的 −1。
   报告时必须分开写"根面名字集"与"债务计数"。
10. **同机多车道纪律**（PR-65）：只按自己的 `--root` 清理、优先不 kill、平台组杀按恢复事件分段续跑；
    **subagent 永不设超时**，平台中断只 resume 不判失败。

## 8. 复用清单（下一批债直接用）

- 对象形态相同（`yOfX` + `gamma3fXDivSqrtdelta`/`dih`/`matan`）⇒ 直接用 `W1aFJet` 的 one-mode 树
  （`fPos1`/`w1F3O`）+ `DCMatanMono` 端点 hull + `MatanC1` + `M8Kit`。
- 盒宽与 wt1 同量级 ⇒ 直接复用 cover 细化脚本（`coverage.py`/`refine_t2.py` 的 T2 口径），
  但**先量形态**（T2 发射 vs 手写 route R 的 D1 可能差 4–7×）。
- 组装/接线/岛协议/`#print axioms` 审计：照 `W1DCAssembly*` + `Assembly.lean:431` 的样板。
- 发射：`gen_m9.py` + `mk_l1.py`（L1 形态是当前默认；`@[irreducible]` 槽、`dSqrt` 字面量、
  `dRescale`、`KZ=1024` slack 都已内建）。
- PARITY：直接套 `PARITY_CARD_wt1_value.md` 的六维模板 + 两个已校准的坑
  （HOL `total_time`、olean 不设绝对阈值）。
- **L3 探针卡（`parity-l3-b-prep-w1/`，`l3-probe-v1`，2026-11-26）**：D5 主判据
  `t_full/9.661 s`（HOL 单箱预算）；**只有 M2 全量可做 GO**，EST 12–26 s = 1.3–2.7×
  （值通道 6–9 s 是假绿，不含 part 12.66 s）；D3 证书层 S1（端点 154.5 B/箱）0.44–0.48×，
  但 **cover/装配 3,654,359 B ⇒ 整 wt1 D3 地板 2.21×**（L3 单独拉不进 2×）；
  D4 终端 `dcSlack` 不通用化 ≥400 KB/箱 ⇒ 通用终端是硬要求。**wt1 本身不重投。**

## 9. 指针

- 账本：`docs/priority-queue.md` §8 续1537–续1568；文件头 SORRIED 48。
- 代码：`lean/Kepler/Text/TaylorSecond/{DCKit,DCMatan,DCTaylor2,DCJet,DCSqrtLit,
  DltCornerWide,M8Kit,DCMatanMono,MatanC1,W1aFJet,W1DCBridge,Wt1Glue}.lean`、
  `W1DC_<id>.lean` ×221、`W1DCAssembly*` ×10；`Kepler/Assembly.lean:431`。
- 快照：`~/c17_backup/lane_snapshots/wt1-emission-pilot-w1/`（M3–M9、生成器、报告）、
  `wt1-glue-bridge-w1/`（W1aFJet/W1DCBridge）、`wt1-m8-preflight-w1/`（v1/v2/v3 预飞）、
  `wt1-m9-emission-w1/`（gen_m9 终版）、`wt1-l1-probe-w1/`（L1）、
  `wt1-bulk-{a,b,c}-w1/`（221 量产）、`wt1-assembly-w1/`（组装）、
  `holparity-wt1-value-w1/`（原形态 PARITY CARD）、`holparity-wt1-l1-backfill-w1/`（L1 卡）、
  `parity-l3-b-prep-w1/`（L3 探针卡 + B 口径注记）、`wt1-l1-close-w1/`（Final 重编 + 根面审计）。
- 章程：`docs/hol-parity-gate.md`、`AGENTS.md` §7.3；雷区：PR-62/63/64/65。
