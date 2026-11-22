# nli 战役路线图与结论（活文档）

> **定位**：`nli*` 非线性不等式债的**路线图 / 已闭件 / 负结果 / 下一步**。
> **实时状态数字只有一个出处**：`docs/priority-queue.md` §1/§8 与
> `docs/e2e-reachability-map.tsv`；本文不重复维护账本数字。
> **历史只读侦察**（不是当前状态，勿按它们排产）：
> - `docs/archive/scouts/nli-farm-runbook.md`（旧 G4/lake farm 流程，已被当前
>   内核直编 + 全局单 lean 锁取代）；
> - `docs/archive/scouts/nli-rest-scout.md`（2026-10-22 的 59 rest 侦察）；
> - `docs/archive/lane-archives/nli-bank-triage/`（68 bank 的纯 Lean triage）。
>
> 本文是它们的**当前汇总与索引**；旧文只作证词。

## 0. 口径

- `nli*` = `Assembly.lean` 里的非线性 inequality bank 债；每个是一条 6 维盒上的
  量化不等式（常带析取支），由 HOL `ineq.hl` / `PackingAuto*` 的 `bank_*` 陈述承载。
- 终局口径见 `AGENTS.md` §1：585 条 `native_decide` 是**信任基座**，不是债；
  债 = 锥内 `sorryAx` 来源。
- 路线标签（`nli-triage-w1` 口径）：
  - `WIRE`：已有证明/证书，只差接线；
  - `MATH`：残差是单条显式数学命题（代数/单调性/区间）；
  - `MATH-FARM`：数学 + 真实分支切换/接缝分析；
  - `SMALL-CERT`：盒薄/退化，本地小证书可跑；
  - `FARM`：证书回放（bb_arb/TM）才能关；
  - `LP`：`lpArchiveCertificatesDebt`（hLP），43,078 条 LP 终端记录。

## 1. 当前分诊（2026-11-15）

来源：`nli-triage-w1`（`a09ad494` 前）的 54+1 对账 + 后续两次闭合。

- 原 54 条 `nli*` 的路线分布：`WIRE 1` + `MATH 5` + `MATH-FARM 13` +
  `FARM-CERT 1` + `FARM 34`；hLP 另计 `LP`。
- **已闭 2 条**：
  - `nliPackIneqDefA`（WIRE，`a09ad494`）：UKBRPFE/WAZLDCD/BIEFJHU 三组件全在库，
    Assembly 1 import + 1 body；
  - `nliRestQITNPEA4003532128a`（MATH，`06285994`）：纯代数，见 §2。
- 当前剩余 = 50 条 `nli*` + hLP（基线 AQ `e4c384e6`；见 pq 文件头；SORRIED 构成以 pq 为准）。

### 1.1 审计结论（重要）

- **0 条假陈述 / 0 条空盒**（锥内代表盒逐槽核 + 54 条析取支逐条核）。
  没有 `ht4nn` 式陷阱。
- **3 条锥外影子 `*Ids` 是 VACUOUS**（`certLookupDomain → True` 支）：
  `nliOx3q1hIds` 230/230、`nliPackIneqDefAIds` 5/5、
  `nliMainNonlinearTerminalV11Ids` 100/109。
  **必须从“nli 接线主波”工单剔除**，否则会假绿。
- `nliLpIneqsIds`（127/127）与 `nliKcblrqcIneqDefIds`（28/28）是**真债**，别一起除名。
- `get_main_nonlinear` 有 `| _ => True` 回落（109 清单 vs 108 显式分支），
  需一次对表（`nli-triage` PICK-3）。
- `ZTGIJCF4` 模板的 m 槽乘子 `betaBumpLb = −0.005` 比 HOL 后续版本严格强 0.005；
  数值实测陈述仍真（主支余量 +0.0274），建议走 SF 记档。

### 1.2 已排除的便宜路线（不要再试）

- **rad2 望远镜路线已用尽**：39 条 rest 债里带 rad2 析取支的 min rad2 =
  1.674–1.944 < 2；带 `<2` 支的 max = 2.463–2.783 > 2。只有已证的 6 个
  `ZTGIJCF4` 实例满足 ≥ 2（正因已证而不在剩余债里）。
- `RQWUDDU`：dih/η 双支同时贴边，最小余量 4.7e−3，数值路线不便宜。
- `nliTskIYOUOBFsharpv2` 的 `h2d`：sharp corner + 2 维非单调，单点规则不够。
- `nliCell3QZECFICwt0sqrt8` / `wt0corner`：3 轴单调拼接，一轮 ≥ 数百行，
  不是“小证书”。

### 1.3 FARM 34 条重排结论（`nli-recost-w1`，2026-11-15）

- 34 = 30 case-mapped + 4 接口级。分层：**≤10 只有 1 条**
  `nliRestIXPOTPA`（0.59 CPU·h；前 6 个析取支全是多项式，99,915/100,000 叶走
  poly 档，**区间 0.17–28.9**，若 poly 叶实际要 ~1 s 则回到 ~28 h）；10–50 三条
  （`PEMKWU`/`TEWNSCJ` 27.8、`QITNPEAv24003532128` 33.8）；50–200 三条；
  **>200 共 20**（19 条 case-mapped 典型 1,100–1,170 + `nliOx3q1h` ≈64.6k）。
  26 条实测合计 **21,156 CPU·h**，外推 30 条 **≈25.6k**（单核 ≈2.9 年）。
- **根因：宽盒叶树是 ~10⁵，不是 10³**（二叉树恒等式 `leaves=(nodes+1)/2`，
  TSKAJXY 6,512/13,023 交叉验证）；Rule P 单叶生成 6.7–13.4 s、内核 27–50 s。
  TSKAJXY 便宜是因为盒宽只有 0.01；一般 FARM 盒宽 0.4–0.65 ⇒ 差两个数量级。
- **3 条 cell3 = BLOCKED（规则缺失，不是贵）**：case 含 `log`（matan 负分支）⇒
  `tmexact.transOn` 无此 kind；bb_arb 实测 50% 尝试 `sqrt/log 底非正`
  （Lean `Real.sqrt` 负支=0，检查器无此规则）。`TskWKGUESBsym` 1200 s TIMEOUT。
- **盒超集陷阱**：`out/cases` 把 `hminus` 展开成 `[1.2,1.3]`（choice），而 Lean
  真盒被两条标准三定理钉在 `[1.23175,1.23176]` ⇒ `2hminus ∈ [2.4635,2.46352]`；
  必须用 `cases_narrow/`，否则主支数值为负、证书不可能闭合。
- 4 个 `QITNPEA1` case 原缺失（HOL OCaml 模板生成），已用
  `parse_body_raw + emit_rpn.translate_record` 重建。
- 编排者复核：`get_main_nonlinear` **109 显式分支 ↔ 109 ids 精确双射、
  零 `|_ => True` 命中**（AUDIT A-3 的 SUSPECT 关闭；旧「108」漏了字母开头的
  `OMKYNLT 3336871894`）。
- `pipeline/interval/tmexact.py:1172` 的 `arctanINegP` 曾用 `neg`（Dyadic）
  而非 `ineg`（DInterval），真 emitter 在 27 条里 12 条直接崩——已修
  `2d9eb9cc`（smoke `[3,4] → [1.2490,1.3258]` 正确）。
- **判读**：FARM 本地量产判死；`IXPOTPA` 是唯一 FARM-MATH 候选。后续优先
  MATH/MATH-FARM（ZTGIJCF4 γ4/dihY 套件）与 `nliOx3q1h` 的
  「每盒联合角点」路线（230 合取 → 46 线性 + 184 γ4；48 个 y-盒；
  完整签名 = **22 个 dihY 系数 / 44 个 (γ4,dih) 对 / 71 个 (盒,对) /
  125 个全签名 / 144 个 (盒,全签名)**。旧「19 签名 / 67 组合」只看了
  a/b/bump 的部分签名，**ERRATA**）。

### 1.4 `nliOx3q1h` 可行性（`g4feas-w1`，2026-11-15）

- **46 条线性合取全部可 `linarith`**：精确有理算术，最小余量 **1.416e−7**（仍 >0）；
  这是 230 条里零风险的一批，可先落。
- **184 条 γ4 余量全正**：最小 **3.0205e−4**（#147/#149）、中位 1.975e−3
  （ESTIMATE：60 dps + 角点/5⁶/坐标下降 + argmin 40 dps 区间佐证）。
- **不能拆 `γ4≥G` + `dihY≥D`**：`γ4≥0` 在 18/48 盒为假
  （`γ4(2.52,2⁵) = −0.0055589`）；`dihY≥arccos(1/3)` 在 25/48 盒为假；
  即使用**每盒完美 γ4 下界**，残差仍 9.0e−4…0.2005（中位 0.0678）——
  γ4 最小点与 dihY 极值点不同点。唯一可行形状是**每 (盒,签名) 联合下界**。
- **角点表规模很小**：64/96/128 角点/盒；48 盒 = **3,456 次求值、去重 1,056 点**
  （比旧估 10,368 便宜 3×）。**166/184** 极小在 kink 角点；**18/184 在 y4 内部**，
  角点表高估至多 6.018e−4（16 条 >1e−4）⇒ 这 18 条需一维（y4）补丁。
- **γ4 Taylor/centered form**：ZTGIJCF4 4 条解耦箱 k=2 可行
  （+0.050292 / +0.074140 vs G=0.0403/0.0703），但 131,072 叶 ⇒
  Rule P **983 CPU·h**、生成 1.3–5×10⁷ 行，比角点表贵 2–3 个数量级，**不换**；
  ox3q1h 需 16⁶ 子盒/条 ⇒ **8.6×10⁵ CPU·h（≈98 CPU·年），不可行**。
- **窄盒正面结论**：centered form 损失 ≈ ½·L·r²（L≈1.3–2.4）⇒ 半径 ≤0.03 的盒
  （QITNPEA1/TSKAJXY 类）**一片 Taylor 叶**即可给 γ4 下界；宽盒（r≥0.1）必须靠
  凹性/角点表。朴素区间算术在宽盒上爆（`deltaX` 区间 [−619,1422]），须走
  atom 级 Taylor model。
- **下一步**：先落 46 条 LINEAR；再拿 #147 所在盒做单盒联合角点表 pilot；
  ZTGIJCF4 仍走 Kit A + 216 角点表。

### 1.4.1 联合角点草案实测验证（`ox3q1h-corner-scout-w1`，2026-11-19，判词 GO 条件式）

- **数学成立、全数字可复现**：角点电池 184/184 ≥ B_i（slack +4.5e-8…+1.6e-7）；
  rebate+split 后 min **1.3299e-4**（#71）[exact]；最坏三盒 6⁶ 密网 + 随机点全部
  ≥ 认证下界（头寸 2.8–12.3×）；**解耦口径必死复现**（#147 解耦 −0.1417 vs
  联合 +3.02e-4）——§1.4 的「唯一可行形状是联合下界」结论实测成立。
- **工单级记账缺口（P0 前置，必先修）**：落库 `Ox3q1hChainSplit1/2` 的 hcorner
  槽 = 全维等分格点乘积，19 条 split 合取在现 uniform-m 方案下需 **39,792 个
  非顶点新格点**（当前 S2b 账面 976 点/61 文件/67 万行**完全不含**，40× 缺口）。
  修法纯发射器/常数重发、零陈述改动。
- **重压缩三档（今日武器）**：y4 在 12/19 条全盒 MONO+ [sampled] ⇒ 单调塌缩；
  逐维最优 m ⇒ 10,556 点；真实常数 /8 ⇒ **推荐 3,524 点**（紧 K 档 1,924）；
  修订 S2b 总账 ≈ 4,500 点（976 顶点 + 3,524 格点）。
- **ERRATA 两条**：recost「#138/#208 需更紧 hminus 界」**取代**——真括号
  [1.23175,1.23176] 下 184/184 正、负值只在 choice 超集盒（树内已证处）；
  624 个 y4-patch 点**不需要**（落库链从不消费）。
- **S2a 风险定量化**：K 表正侧头寸实测 1.12–1.56×（y2 族仅 1.12×）；收不进
  ⇒ 机械升 K 重跑三表（脚本随快照，m≤8 仍有 7.5e-5…3e-4 余量）。
- **考古 + PR-47 复核**：HOL 原版（ineq.hl:1559–1581）对 230 条**无专门引理**
  ——全交 `formal_ineqs`（二阶 Taylor + mono_depth=200 导数剪枝，
  **7,318 叶 / 757.3 CPU·h** [exact azure 日志]）+ deserialization 公理导入
  （违 AGENTS §2 不可抄）；64.6k vs 757h 的 **85× 差 = 纯「导数剪枝有无」**。
  64.6k 推导对 naive-farm 口径内洽（无规范形失配），但引用必须带
  「naive-farm」限定——结构化真实规模是 10³–10⁴ 件级（低 3–4 个数量级）。
- **施工规格（SCOUT §6）**：P0 重发 split（mono kit ~50–150 行 + 常数 ~2k 行，
  0.5–1 车道日）→ S2a ~1,350 槽件（20–80 lean-h）→ S2b 976 + 3,524 点
  （现式 3.0M 行/~8 h；**采纳 ZTG G4CORNER 压缩式 110–250 行/点 ⇒ 0.5–1.1M
  行/2–3 h，L2 压缩表示法是 ZTG↔ox3q1h 最大反向转移机会**）→ S5 ~240 行；
  合计墙钟 1.5–3 周、0 农场、0 解冻。快照 `ox3q1h-corner-scout-w1/`。
  **验收口径勘误（编排者裁定）**：单债 −1 后根面仍 **589 逐条同集**（其余
  sorry 在则 sorryAx 在）——变化 = K_SORRIED −1 + 本件消费链恰标准三；侦查
  原报「589→588 sorryAx 消失」口径有误（同 sqrt8 车道同款错误）。

### 1.5 HOL γ4 考古裁决（`g4hol-w1`，2026-11-16）

- **HOL 没有更便宜的 γ4 形式化路线，只有更便宜的信任路线**：叶子层（ZTGIJCF4 16、
  ox3q1h 230、GLFVCVK4 等 6D 盒）不在主树证，走独立 `formal_ineqs` 验证器
  （二阶 Taylor + `mono_depth=200` 局部导数剪枝 + 凸性 glue + 自适应搜索，
  **32–139 叶/盒**），再用 **23,242 条 digest + `deserialization` 公理**导入
  （`serialization.hl:612/623`）。后者违反 AGENTS §2，**不可照抄**。
- **合并层我们已 100% 移植**：`gamma4fgcy_div_sqrtdelta`、`tsk_lemma1`、
  `REAL_WLOG_SIMPLEX`、`CRIT/BRANCH`、`ztg4_ALT`（PA25:13537）、Euler 锚
  （PA21:11558 已证）。剩余债就是 10 条 `bank_ZTGIJCF4_*` + `GLFVCVK4` 4 条 +
  ox3q1h 的 46 线性 + 184 γ4。
- **实测 HOL 成本**（azure `Time` 行）：ZTGIJCF4 16 条 **76.0 CPU·h/556 叶**
  （剩余 10 ≈72.5；`0_0_0_0` 17.8 h、`0_1_0_0` 22.1 h）；ox3q1h 230 条
  **757.3 CPU·h/7,318 叶**；GLFVCVK4 127.9 h/846 叶；中位 404 s/叶。
- **可移植的真杠杆**：`CertTM2` = 二阶 Taylor 节点 + **逐子盒局部导数符号剪枝** +
  凸性对接 + 自适应搜索。我们现有 `Gamma4WideD`/`Gamma4Mono0` 是全局手写引理，
  而 γ4 全局不单调；HOL 用的是局部符号，所以成立，并把叶数从 10⁴–10⁵ 压到 10²。
- **判词**：照抄 HOL+digest 公理 = 禁止；只移合并层 = 零收益；引擎升级 ⇒
  ≤10² CPU·h 有条件 YES；≤10³ 行/盒 YES，≤10³ 行/10 条全债 NO（≈10⁴ 行）；
  现行一阶 Taylor/角点表直上宽盒 = NO（4⁶–16⁶ 叶）。
- **建议**：立 `g4port-w1`（引擎车道，非合并层），pilot `ZTGIJCF4_0_0_0_0` +
  `_0_1_0_0` + ox3q1h `#147`；判停线 ≤3 CPU·h 内核、≤5k 行/件。零风险并行：
  ox3q1h 46 条线性立刻 `linarith`。
- **`g4port-w1` 结果（2026-11-16 09:39，GO 条件式）**：四杠杆全部复现；pilot 叶数
  **81/60/47**（s=10）/ **30/22/10**（s=3），估计内核 **1.35/1.00/0.78 CPU·h**、
  行数 **4.15k/3.10k/2.45k**；对比 HOL 139/75/~32 叶、bb_arb ~10⁵ 叶、
  centered-form 131k/16⁶ 叶。**唯一 Gate = Lean 侧可证三阶导界 `Jet3`
  等效 safety ≲10**（s=30 ⇒ 380/288/134 叶，仍 <10× NO-GO 线但超 2× GO 线；
  s≥100 不闭合）。Gate-0（1 天）= `Jet3.lean` dyadic 三阶区间 AD 紧度 pilot；
  过关 ⇒ `CertTM2.lean`(~2k 行)+`BBTree2` ⇒ 落地 #147→p1→p2。全部叶数为
  ESTIMATE（L3 是采样界），形式化必须由 Lean 三阶 Taylor model 重做。
- **勘误**：`NliBanks17.lean:12-14` / `NliBanksZTGIJCF4Route.lean:57-60` 的
  “Euler 锚未证”已过时；`PackingAuto25.lean:12031` 的“两处 sorry”注释过时；
  Route 头注把 γ4 桥不可用归因于锚，真因是该桥只适用两长四短窄型盒。

### 1.6 剩余 MATH/MATH-FARM 审计（`nli-rest-math-audit-w1`，2026-11-16）

- **ENGINE 三条**：`FHBVYXZa`（**分支改写：主支 ∨ eta126²<1.34² 两支即足，rad2 冗余**；
  minimax +7.677e−3；80–260 叶/1.4–4.4 CPU·h）、`FHBVYXZv2a`（接缝最紧 +2.124e−3；
  100–300 叶/1.7–5.0 h）、`QITNPEA5400790175a`（主支 min −7.2693e−3 在双折点角；
  minimax +4.121e−3；100–280 叶/1.7–4.7 h）——全部在 g4port 判停线内。
- `RQWUDDU` = ENGINE primary（MATH 备选高风险）：minimax **+2.155e−3** 三支严格等振；
  **ERRATA**：triage X-1 的 0.00474 → 0.002155（2.2× 紧）。
- **MATH-REDUCE 三条（纯手工可写）**：`Cell3corner` 300–500 行最便宜（三轴导数
  +0.017585 全正、matan 全程正支，无需 NliBanks12 拼接）；`Cell3sqrt8` 400–800 行
  （三轴导数全正，matan 实参变号但导数不变号）；`IYOUOBFsharpv2` 1–1.5k 行 hybrid
  （hmono min ∂ +0.13110 + h2d 三件套）。
- **前 3 推荐工单**：`cell3-corner-mono-w1` → `cell3-sqrt8-mono-w1` →
  `iyou-sharpv2-slots-w1`（各 −1 sorry，纯 MATH）。ENGINE 波（Gate-0 后）顺序
  **FHBVYXZa → QITNPEA → v2a → RQWUDDU**。
- CONFIRM：三处角点 dip 精化为 −5.55894e−3/−1.12589e−2/−7.26930e−3（VERIFIED-iv）；
  NliBanks12 Δ 范围逐位复现；g4hol 外推无矛盾。
- **ERRATA（2026-11-18，`b0-joint-envelope-w1`）**：FHBVYXZa/v2a 的上述
  minimax +7.677e−3/+2.124e−3 是**非最优驻点，不是全局 sharp 余量**；本车道复现为
  **+4.813e−3/+1.104e−3**（数值 ESTIMATE）。两条债的 η 接缝有内点极小，
  `max(g,c−η²)` 非凹，不能套 96 角点表。详见 §1.11。

### 1.7 全量路线地图（`nli-map52-w1`，2026-11-16）

> **ERRATA（2026-11-16 16:39，`terminal11-census-w1` 实测对表，详见 §1.9）**：
> 本节 TerminalV11 相关判词修正——① 「104 NO-CASE」→ 实为 **83**（漏 cases_prep/
> 18 + 库内证书 21，全层覆盖 26/109）；② 「4717061266 补粘合」「语句级先行步未估」
> 双双 **STALE**（T0 语句级展开已落库 LA1:1900–2158）；③ 「68 MATH 候选」shape 口径
> CONFIRM 但 route 口径 6→3（574/183 测后改判机器分割）；④ 本条 route_tag
> MATH-REDUCE → 实为 **FARM 主导**（109 支 = 85 FARM-EMIT / 21 ENGINE-LEAF /
> 3 MATH）。其余 51 条不受影响。

- **对账零差异**：52 条 `nli*` + 1 hLP 在 map.tsv SORRIED 段 / pq 文件头 /
  `Assembly.lean` 债行（:402–:1834 52 条 + :7104 hLP）三方逐名吻合；
  族分解 rest 38（含 ZTGIJCF4×10）+ tsk 5 + cell3 5 + 直挂 4 = 52。
- **路线全判、零 UNRESOLVED**（`NLI52_MAP.tsv` 53 行×11 列，快照 `nli-map52-w1/`）：
  **CERTTM2-ENGINE 31 / ZTGIJCF4-KIT 10 / MATH-REDUCE 4 / FARM-BLOCKED 3**
  （cell3 wt0/wt1/wt2A，log+负底规则缺失）**/ LP-GATED 2**（`nliLpIneqs`/
  `nliKcblrqcIneqDef`）**/ CORNER-TABLE 1**（`nliOx3q1h`）**/ IN-FLIGHT 1**
  （`nliTskXLLIPLS`）。本车道新判 0 条——52 条全部落在 recost 34 + audit 7 +
  g4feas/g4port 12 + 在飞上下文的覆盖内；本图价值 = 判词首次逐条对齐到债单本体
  （Assembly 行号 + ineq.hl 锚 + gate 依赖 + 排产位）。24 条锚逐条开文件核过
  （发现 HOL id `PEMKWKU` 比 Lean `PEMKWU` 多一 K）。
- **endgame 两分支**：
  - **Gate-0 过** ⇒ ENGINE 波可吃 **43/52**：XLLIPLS 收尾（在飞）→ 纯 MATH 3 →
    现行引擎 4（IXPOTPA 0.59 CPU·h 起，共 ~90 h）→ audit 序 4 条
    （FHBVYXZa→QITNPEA→v2a→RQWUDDU，1.4–13 h/条）→ ox3q1h 46 线性立即 linarith →
    ZTGIJCF4 γ4 10 + ox3q1h 184 γ4 + P5 大批 23 条（1,100–1,170 h 压到 0.8–2 h
    量级，**ESTIMATE**，形式化须 Lean 重做）。
  - **Gate-0 挂** ⇒ 无 gate 只能整条清 **9 条**（XLLIPLS + MATH 3 + 现行引擎 4 +
    ox3q1h 走 48 盒联合角点表）；ZTGIJCF4 Kit A dihY 半边可落但非整条 sorry；
    其余 43 条冻结在 Gate-0/农场/LP 三类 gate。
- **空白点（UNRESOLVED-类风险，如实标注）**：
  ① `nliMainNonlinearTerminalV11` 最粗——109 清单 104 条 NO-CASE、68 条 MATH 候选
  无逐条余量 ⇒ **下一个审计车道候选**；
  ② cell3 wt0/wt1/wt2A 主盒单调性未测量（audit 只测 corner/sqrt8 子盒；当前按
  FARM-BLOCKED 记）；
  ③ **锥外 5 条 `*Ids` sorry**（Assembly:1905/1926/1961/1988/2005）不在任何债单
  （§1.1 有记；锥扩展则 SORRIED +5，3 VACUOUS + 2 真债清单侧）；
  ④ `Assembly.lean:1897` 注释「ox3q1hP25 本体即 sorry 型 opaque def」过时
  （本体 2026-11-06 DEF-FIX 已显式化 PA25:94，nliOx3q1h 是纯证书债）——
  过时注释清理第 4 条候选。
- hLP 附注：LP-GATED（42,889 bound 叶 + 磁盘 ≥1.2 TB 硬墙，等用户算力裁决）。

### 1.8 Gate-0 预研（`jet3-pre-w1`，2026-11-16）——Gate 定义修正 + 施工图

- **GO 概率 ~60–65%，且比 §1.5/g4port 设想更便宜**：判据不是"三阶导界是否存在"
  （1-D MVT 伸缩必存在、无四阶项），而是 **d2B 包络紧度**。
- **Gate-0 重定义（修正 g4port 判词）**：由"evalJet3 紧度 pilot"改为
  **"d2B 供给器紧度 pilot"**——三供给器同测，**C1（符号 ∂² + 盒区间求值）首选**：
  HOL `formal_ineqs` 以同一配方量产 23,237 叶（`informal_taylor.hl:31–135`），
  等效 safety 落我们 s=3–10 区间；C1 的 Lean 侧资产 90% 已在树内量产
  （`derivIExprM`/`DerivSafeOnM`/`checkPosFaceLo_sound` 在 `C549Mono.lean:52/87/438`、
  `evalTMHullD2` 在 `CertTM.lean:3814`），**新数学仅 2 件**（`taylor2_faceLo`、
  `concFace`）。Jet3 三阶 flat 槽（`Fin n → Fin n → Fin n → DInterval`，非嵌套）
  降级为"C1 太肥时的升级件"。
- **体量**：C1-最短 GO 路径 ~19 引理/**1,900–2,600 行**；Jet3 全量条件追加
  +21 引理/+2,600–3,800 行；发射器 400–600 行 Python。
- **GO 判定表**：主判据 = certified 包络回灌 B&B 叶数（s*≤10 GO / 10–30 灰区 /
  \>30 NO-GO；等价 2×HOL = p1≤278、p2≤150、p3≤64）；辅 ρ1=cert/true≤3、
  decide≤3 min/叶、300 点采样零违例。**最大风险** = p1 MONO 宽维叶
  （w≈0.116、余量 7.8e-4）。
- **考古**：HOL `formal_ineqs` 止于二阶（`m_taylor_interval` 无三阶层，
  soundness 用 `has_bounded_second_derivative`）——三阶为本仓新杠杆，
  无上游死路/活路标记。
- 工单建议已就绪：**`jet3-g0-w1`**（P0–P3，见 `jet3-pre-w1/DELIVERY.md`）——
  半天可判 C1；发车时机 = 二 lean 槽空出（ztgmain Kit A 收线后）。
  详细 `lane_snapshots/jet3-pre-w1/JET3_PLAN.md`（31KB）。
- **2026-11-16 20:20 发射器落库 + Gate-0 判定精化**（`certtm2-emitter-w1`，
  落库 `c10e1f6d`）：生产发射器 `pipeline/interval/certtm2/`（10 文件 2,583 行，
  纯新增）——3 叶校验 **81/60/47 与 g4port s=10 零失配**、采样 **0 违例**
  （float 300 点×188 叶 + mpmath 60dps 复核 98 叶块）、确定性 SHA 双跑一致。
  **关键测量 `certOk = 0/188`**：C1 纯区间求值在 s=10 宽叶 wrap 严重
  （GB ~500×、HB ~5000×；2^s 细分每级仅 ×2 收敛不可行；归因 = rad 分子/分母
  相关性丢失 + 二阶链式 (∂)² 复利 + 19 dihY 项无关联求和）⇒ **`jet3-g0-w1` 的
  C1 判定必须用 TM-hull/Δ-族精确值域作载体**（与 JET3_PLAN 原设计一致），
  纯区间版出局；NO-GO 分支下 engine/dyad/audit/exprs 仍可复用。
- **2026-11-17 02:10 Gate-0 判定 = NO-GO（边缘、外推口径）**（`jet3-g0-w1`）：
  TM-hull 版 certOk **132/188**（≥100 线 PASS；g0 还发现并修复了 emitter
  `exprs.dihXf_t` 置换 radicand floor 缺陷——0/188 的一大半根因，落库 `ca1c7677`）；
  P2 decide ≤4 s/叶 + axioms [propext] 全 GO；**但 certified B&B 宽前沿 60–120
  s/节点 → 叶数外推 s*≈35–80 ≫ 30**。ρ1 中位 24.7；瓶颈 = 一阶线性 wrap
  （每细分级 ~2×）。**后果（§1.7 挂分支）：ENGINE 波四工单搁置，43 条冻结**；
  无 gate 可清 = 9 条。战略分叉（接受 NO-GO / 质疑外推 / 混合路线：132 叶当场闭 +
  56 宽叶角点表）**待用户裁决**。详见 `jet3-g0-w1/P3_MEMO.md`。

### 1.9 TerminalV11 109 支普查（`terminal11-census-w1`，2026-11-16）——闭合算术定案

- **109 支全判零 UNRESOLVED**（`TERMINAL11_CENSUS.tsv` 109×18，快照
  `terminal11-census-w1/`）：结构 = 74 显式 HOL add（`main_estimate_ineq.hl` 71 条带
  Main_estimate tag 全命中 + `ineq.hl` 3）+ 35 hex 循环族（`make_hex_ear`，C(7,3)）；
  `get_main_nonlinear` 109↔109 双射复核通过、`|_ => True` 回落零命中。
- **route_tag**：**ENGINE-LEAF 21**（20 支 T11Glue 已粘 + `8405387449` 在库未粘
  40,785 叶/498 分片——scout「20」之后的增量）/ **FARM-EMIT 85**（5 case JSON 在库 +
  35 hex 模板 + 40 直发 atan + 2 高维 prep + 3 多项式分割）/ **MATH-REDUCE 3**。
- **闭合算术**：关 `nliMainNonlinearTerminalV11` 还差 **88 支证明 + 接线** = 85 农场
  （scout 口径 500–700 mh；TM 层视 Gate-0）+ 3 MATH（余量已测：num1 顶点极小
  **+52.512319 / +11.734635** 精确有理、645 slab deltaY **−0.46104538** 精确——三者皆
  「multiaffine + 单变量凹 ⇒ 64 顶点枚举」即完整证明）+ 1 补粘（8405387449）；
  **部分证明不减 SORRIED**（合取债）；20 支已粘但 T11Glue 未 import 进锥；
  语句级展开 T0 已落库（LA1:1900–2158），剩的是接线与证明、不是语句缺口。
  另：574/183 已被 iv 分割**全闭**（uncovered=0）、717 disj1 支配 99.1% 网格
  （剩余条带归机器分割）。
- **cell3 wt 三条补测**（map52 空白点③解除，`WT_CELL3_MARGINS.md`）：三 prog 对
  hminus 偏导恒 0；**wt0** farm 盒全局最小 **+1.783e-4**（iv，角点 (2.01,2,2)），
  无反例但三轴导数变号 ⇒ corner 单调模板不能照搬、**FARM-BLOCKED 维持**
  （阻塞在 log/matan 规则层非负值）；旧判 **wt1/wt2A** Lean 盒 y5/y6 严格单调增 ⇒
  「单调归约 + y4 一维证书」MATH 可行（极小 +4.514e-5 / +3.011e-3，iv 包围）。
  **ERRATA（2026-11-18，§1.15）**：wt2A 的 y5 全盒严格增已有高精度数值反例；
  wt1 未由本车道证明，旧单调结论不得直接当已验资产。
- **ERRATA（对 map52/recost/scout，§1.7 已注）**：① 104 NO-CASE→83；② 「5 γ4」→
  109 支无 γ4（实为 taum×4 + deltaY-disj×1）；③ 补粘合/先行步两条 STALE；
  ④ recost「引用型 36」→ 35；⑤ route 口径 6→3；⑥ scout「89 vs 87」内部不一致 →
  现行 FARM-EMIT 85。求值器 4 组 pin 全过（restcore.c3 逐点吻合、nb11
  3.7446884e-3 复现、recost DISJUNCTS 独立复现）。

## 1.10 Bernstein 代表定标（`bernstein-representative-w1`，2026-11-18）

- **多项式义务 GO（仍待真实 Lean 单叶定标）**：ZTG 四债均根盒 1 叶；
  q=64/25 三债各 1,215 系数 / 57,142 B / 约 0.42 s，q=36/25 经两次单调剪枝为
  81 系数 / 2,488 B；rad2/eta 守卫 1–3 叶毫秒级。与库内 bespoke 对照，
  32 角点 + Jensen 链可由一张六维 Bernstein 张量替代。
- **通用超越后端 NO-GO**：BIX 代表节点的 √ 整盒仿射误差 5.944，约为 slack 的
  2,662 倍；atan 的 Q 跨 −1；`chord(S)^5` 单分数组合达 126,607,131 系数。
  **先代数化是 Bernstein 后端的必要门，不是可选优化。**
- 编排者复跑 42 项自检、ZTG、守卫均 PASS；P1 输出复现关键数字。**验收勘误**：
  编排者追加的 ε 曲线复跑继续进入 level 3（262,144 盒）并于 840 s 超时，
  故不记“P1 全进程 PASS”；车道原始日志与已打印的 0–2 级曲线可供复核，
  不据此补称完整 RC。
- **Lean 单叶定标 = 暂缓（`bernstein-kernel-pilot-w1`，UNRESOLVED，可重启）**：设计 A 的
  MvPolynomial `DecidableEq` 不可归约；设计 B' 通用核虽在 `bk13` 单次 RC=0，但当前
  WIP 又有 exponent/Finsupp 错误和 heartbeat 超时。81 系数叶仍卡 Quot/Finsupp/Eq.rec
  的 decide 归约，1,215 根叶未开始，故没有完整 wall/RSS/olean/axioms 定标。
  原跑与续跑均 2 h 超时，按多轮/长上下文暂缓；**Python GO 不得写成
  Lean pilot GO，完整 BernsteinKit 当前搁置**。这不表示永久判死；以后若有新表示或
  性价比证据，可由用户明批 fresh representation 重启。详见快照 `ORCHESTRATOR_NOTE.md`。
- 交付：`~/c17_backup/lane_snapshots/bernstein-representative-w1/`。

## 1.11 B0 八债联合包络（`b0-joint-envelope-w1`，2026-11-18）

- **数值 GO，非形式证明**：五主债由 L1/L3/L5 三张共享支撑面覆盖；Q581/Q565
  由纯有理支配推出。FHBb 主支全盒估计最小 +3.804e−3，析取冗余。
  这六债共享 96 角点 / 60 对称轨道，最小均在 `(2.52,2⁵)`，联合包络最紧余量
  **+7.968e−5（ESTIMATE + 局部 iv）**。
- **FHBa/v2a 不能套角点表**：η 守卫集在 d 空间不可分，`max(g,c−η²)` 非凹；
  改走两条一维 η 边界曲线 + 8 个单调性符号。sharp 余量 = **+4.813e−3 / +1.104e−3**，
  推翻 §1.6 的非最优驻点值。
- B0 内 `deltaX ≥ 144`（数值估计），唯一 lmfun 折面 `y1=2.52`；96 角点精确求值用
  `63/25`，避免浮点字面量造成约 1e−11 误差。
- 编排者端到端复跑：12 pin、gamma3f 直组/桥（差 7e−15）、421,875 点扫描、主债细化、
  seam3/4、包络、96 点/60 轨道均与交付一致。全局最小仍是 ESTIMATE，形式化依赖
  `g4-hessian-scout-w1` 的凹性证书与两条曲线证书，**未移动 SORRIED**。
- 后续候选：`b0-master-lean-w1`（hL1/hL3/hL5/hbb 六债共享装配）与
  `fhb-seam-curve-w1`（两条 η 曲线），均待用户裁决。
- 交付：`~/c17_backup/lane_snapshots/b0-joint-envelope-w1/`（含
  `ENVELOPE.tsv` / `CANDIDATE_POINTS.tsv` / `B0_MASTER_PROPOSAL.md`）。

## 1.12 二阶导代数化与整盒否证（scout + `g4-hessian-lean-w1`，2026-11-18）

- **atan-free Hessian 成立**：dihXf 全部 36 个二阶偏导可写为
  `A·Pᵢⱼ(x)/(4x₁^a(u₁₂₆u₁₃₅)^bΔ²)`，P 为次数 ≤12 的多项式；商公式与 Lean
  一阶闭式在 ℚ(x) 精确相等，36 对 40 位三段互验通过。
- **切片纯多项式化**：在 kink 片内，分段仿射加权二面角函数可写为
  `main''(t)=s·N(t)/D(t)`（s=√Δ）；符号由 `N·D` 决定。N 对
  `(2mm1/π,8mm2/π)` 分别线性，故四个有理角点 + 1-D 精确 Bernstein 即充分。
- **ERRATA（Scout lmfun 权重 factor-2）**：`assemble_slices.py` 两处把权重减半
  （ell 分母 52→26、lam −100/104→−100/52）。旧 N/D 数值与旧余量一律不再引用。
  修正装配已由编排者重跑：B0 两片四角点 Bernstein 仍全负（左 max 约
  −4.39e102、右约 −2.04e91）；ZTG `0_1_0_0` 在 `t=20001/10000` 仍有
  sign(N)=sign(D)=−1、Δ>0，凹性破坏成立。**结论方向保留，旧数字作废。**
- **Lean W1/W5 已真证并独立验收**：`Gamma4ConcaveBridge.lean` 给出
  `concaveOn_of_hasDerivAt2_nonpos`；`Gamma4DerivSecond.lean` 给出全部 6 条对角
  `dihXf_hasDerivAt2_x{i}_x{i}`。编排者从快照源编译 RC=0（2.23 s / 5.05 s）、
  岛协议消费探针通过，8 个检查公理面均标准三；~~文件尚未落库~~
  **已落库 `b9134d34`（2026-11-19，joint-6 侦察勘误：本注记过时）**。
- **整盒基坐标量化 = UNRESOLVED，且凹性归约被证伪**：单调性、盒级逐坐标凹性、
  张量直铺三路均不可行。交付插值多项式独立复算 `∂²Q/∂y2²` 的 4×4 精确网格为
  12 非正、4 正，故不能套角点凹性归约。修正装配 4,374 点 Q 全负仅是数值证据；
  整盒需要新的分段/代数证书，不得直接发 `b0-master-lean-w1`。
- 固定 all-2 基点路线仍有低成本数据（N=M·P₇、4 角点 P₇≤0、deg-78/80 ring
  约 7.4 s），但它不等于整盒定理，只能作为低优先机械件。
- 交付：Scout `~/c17_backup/lane_snapshots/g4-hessian-scout-w1/`；
  Lean/勘误/整盒否证 `~/c17_backup/lane_snapshots/g4-hessian-lean-w1/`。

## 1.13 FHB η 边界代数核心（`fhb-seam-curve-w1`，2026-11-18）

- **UNRESOLVED，未真实 −1**：405 行 `FhbEtaCurve.lean` 已证 η126² 的有理商式、
  边界二次曲线、判别式因式分解、显式根式 `fhbX2Root/fhbY2Star` 及盒内/边界性质；
  另证 `nliRestFHBVYXZa_of_eta_disj`、`fhb_eta_disj_of_hba`、`fhb_hba_of_floor3`
  三个归约接口。主仓未落库，Assembly sorry 未动。
- 编排者从快照源独立编译 RC=0（约 9 s / 5.8 GB），11 个 `#print axioms` 全标准三；
  岛协议消费探针通过。独立日志在快照 `ORCHESTRATOR_CHECK/`。
- **B0 草案修正与 ERRATA**：旧稿所谓 ∂γ4/∂y3、∂y4、∂y5 全盒数值为正，是 guard 采样
  误推全盒；`fhb-floor-mono-w1` 已给出三轴非单调的高精度数值反例（§1.14）。∂y6 与 ∂y2
  在 guard 上变号，也不能简单单调推进。剩余 = m3/m4/m5 + 3-D guard 正性（N3D、7 边界片、
  1-D 曲线 `γ4(y1,y2*(y1),2⁴)≥7e−3`）。304 个 Newton 种子仅是侦察，不是 N3D 证明。
- `fhb-floor-mono-w1` 已收线为 UNRESOLVED（§1.14）；`fhb-g3pos-w1` 独立在飞。
  FHBv2a 在 FHBa 真闭合前不启动超越部分。
- 交付：`~/c17_backup/lane_snapshots/fhb-seam-curve-w1/`。

## 1.14 FHB 地板比较：一阶单调否证与凹性归约（`fhb-floor-mono-w1`，2026-11-18）

- **UNRESOLVED，未真实 −1**：m3/m4/m5 本体均未证明，主仓未落库，Assembly sorry 未动。
- **一阶单调路线撤销**：编排者用 60 dps 自适应微分与中心差分独立复算，二者约 15 位一致：
  `∂γ4/∂y4 = −0.09314667568151258` @ `(2.6508,2,2,2.4635,2,2)`；
  `∂γ4/∂y3 = ∂γ4/∂y5 = −0.05788818698069536` @
  `(2.6508,2,2.4635,2,2.4635,2)`。这些点均在 B0；y4 纤维函数值也直接先升后降。
  这是**高精度数值反例，不是 Lean 形式反证**，但足以否定继续按“全盒一阶导数 ≥0”
  证明地板比较的路线。
- **求值器定量勘误**：车道闭式端口在同点分别给 −0.07182445、−0.05463538、−0.04736590，
  与自适应微分同号但不等值；因此不能宣称“闭式/FD/mpmath 三法定量互证”。当前只采
  自适应微分 + FD 的符号结论，车道关于分量抵消量的定量叙述不据此升级为证据。
- **已真证的只是归约**：166 行 `FhbFloorMono.lean` 给出三条
  `fhb_m{i}_of_concaveOn_and_endpoint`：槽纤维在 `[2,2hminus]` 上凹，且地板值不超过
  顶端值，即推出原 m3/m4/m5。编排者独立编译 RC=0（3.74 s / 5.58 GB），五公理面标准三；
  岛协议将三归约直接喂入真实 `FhbEtaCurve.fhb_hba_of_floor3`，RC=0（3.21 s）且标准三。
- **剩余义务**：H1 纤维凹性与 H2 五维端点比较均未证；243 点二阶导全负和随机采样仅是
  数值侦察，不是盒级凹性或不等式证明。车道把它们估为高维证书工作，但这不是形式化的
  复杂度下界；不自动续发农场、CAD 或分段陈述改动。日志在快照 `ORCHESTRATOR_CHECK/`。

## 1.15 cell3 wt2A 核归约与 y5 单调性勘误（`cell3-wt-math-w1`，2026-11-18）

- **UNRESOLVED，未真实 −1**：wt2A 的三维核不等式未证，wt1 未动笔；主仓未落库，
  Assembly sorry 未动。
- **已真证归约**：新文件 `NliBanks19.lean`（288 行）给出显式 `w2aG/w2aD/w2aF`、
  h0cut/lfun 辅助、盒上 `upsX>0`、`eta_y²` 与 `deltaX` 的双向归约，以及
  `bank_QZECFICwt2A_of_core`。剩余精确义务是
  `∀ y4 y5 y6 ∈ box, deltaX(y4²,2,y5²,2,y6²,2) ≥ 0 → 0 < w2aF y4 y5 y6`。
  编排者独立编译 RC=0（5.70 s / 5.78 GB），八公理面标准三；真实 bank 类型的
  消费岛探针 RC=0（3.20 s）且标准三。日志在快照 `ORCHESTRATOR_CHECK/`。
- **旧 y5 单调路线有反例**：独立 BackendM 60 dps 在 `(2.4635,2.5156,2)` 得
  `∂w2aF/∂y5 = −8.4182757987e−5`，步长 `1e−7/1e−9/1e−11` 一致，且该点 Δ>0。
  因此旧 `WT_CELL3_MARGINS` 的“wt2A y5 全盒严格增”不可用。y5=2.513 处导数反为正，
  所以这里只确认反例，不把整个 `[2.513,2.519]` 误写成负导数区间。该反例是数值证据，
  不是 Lean 形式反证。
- **数值可行性 ≠ 证书**：bottom-edge 单 cell 矩形下界约 +2.97e−4，车道建议
  8–12 cell 的无导数路线；但其极值来自采样，核证书尚不存在。极小约 +3.25e−3、
  wt1 约 +4.514e−5 都仍是估计，不能计为闭合。不自动续发 cell 量产车道。

## 1.16 只读数学/文献调研（`nli-math-research-w1`，2026-11-18）

**这是路线调研，不是证明成果；以下候选均未发车，覆盖数与加速比均为估计。**

- **原版机制已核实**：[Hales 回顾 §5.3](https://arxiv.org/html/2402.08032v1)
  明确给出二阶 Taylor + B&B、偏导定号降维，并建议共享二阶导界、批量利用共同结构及
  非负线性组合消析取。HOL 还有 `partial_convex_max`
  （`reference/flyspeck/formal_ineqs/verifier/m_verifier.hl:798`）和
  `mono_depth=200`（`reference/flyspeck/formal_ineqs/informal/informal_search.hl:266`）。
  这些是局部 glue/共享服务，不意味着 B0 整盒凹性或 wt2A 全盒单调成立。
- **代数化确有原版先例**：[A Revision of the Proof of the Kepler Conjecture §5](https://arxiv.org/pdf/0902.0350v1.pdf)
  对 √、倒数、arctan 按正负出现方向采用单向多项式逼近，并在 sharp 点取等；
  一例最后得到 12,945 单项、总次数 18 的有理系数多项式。它支持“局部、紧夹逼 +
  多项式证书”，不支持已被本仓否证的“整盒宽界 + 单分数组合”。
- **首选最小探针**：只拿 `QITNPEA1_1_2` 做零 Lean Phase 0，测 sharp 点锚定的
  arctan 有理夹逼、√ 割线/切线与区域雕刻的总误差/余量；不过线即停。其次是把
  `(dihY,γ4)` 联合下包络外推到 ox3q1h/QITNPEA 代表盒，每盒超过 4 张面即判不经济。
  两者都是候选，候选闸见 `priority-queue.md` §2.4；其中 QITNPEA 单债探针已于
  19:22 获批发车，其余未发车。
- **陈述勘误（派发前核对）**：`bank_QITNPEA1tmpl 1 2` 的主支分母为
  `1 + bankGenMid 1 + bankGenMid 2 = 2`，即 **γ4/2 > 0.0057**，不是调研报告误写的
  γ4/3（`lean/Kepler/Text/PackingAuto21.lean:681-698`）。旧 +3.585e−2 余量暂停引用，
  探针必须从 Lean 陈述重算；不得靠错误分母选择“肥债”。
- **析取组合的正确数学口径**：常数 `aᵢ≥0` 使 `Σaᵢfᵢ<0` 确实推出某支 `<0`，
  Hales 原文也明确建议；但常数权重可行性应对 `0 ∉ conv{f(y):y∈B}` 做 LP/对偶检验，
  **不是**“各零集必须正距离分离”。常数权重失败也不否定分片或变权重。TXQTPVC
  可作低成本探针，RQWUDDU 不应与首个代数化探针捆绑。
- **IneqAgent 参考必须降调**：[论文](https://arxiv.org/html/2610.20681v1)确有
  Bernstein 精确恢复与 Lean 翻译；但公开 [`IneqTSKAJXY_TADIAMB.lean`](https://raw.githubusercontent.com/gaolei-he/IneqAgent/main/LitIneq/IneqTSKAJXY_TADIAMB.lean)
  走显式 `node + positivity + ring`，不是本仓卡住的 `MvPolynomial/Finsupp + decide`；
  [`Ineq7067938795.lean`](https://raw.githubusercontent.com/gaolei-he/IneqAgent/main/LitIneq/Ineq7067938795.lean)
  仍含 sorry。论文附录还记录某些大型有限等式使用 `native_decide`。因此它只提示
  另一种证明项形状，并未直接解决本仓表示/信任约束；其大表达式生成风格也不符合
  当前“少 auto-gen”的目标。编排者只读源码，未编译其项目。
- **不升级为主路线**：SOS/SDP、CAD/QE、dReal、Schläfli、新通用引擎均没有在当前
  Lean 接口上显示出比上述小探针更好的投入产出；Hessian 分类只作负过滤器。
  完整报告在 agent-9 的只读输出；本节的候选与修正以编排者复核为准。

## 1.17 FHB g3pos 曲线核心与端点暂缓（`fhb-g3pos-w1`，2026-11-18）

- **暂缓（2 h 超时，可重启）；UNRESOLVED 仅表示未闭合**：agent-7 两小时超时，
  端点后台编译被终止；快照无 DELIVERY/patch。本次执行暂停以防止重复/无头运行，
  **不是判定算法或数学路线不可行**。以后可从 WIP fresh 评估端点验收/压缩，再试
  尾部凹性；重启由资源与性价比决定。g3pos、FHBa 均未闭合，主仓未落库。
- **曲线代数核心已独立验收**：105 行 `FhbG3posCurve.lean` 给出
  `g3c_curve_x2`（y2*² 对 `(y1²,√fhbD4)` 仿射）、`g3c_dihXf_eq/g3c_dihY_eq`
  和 arctan 界搬运。编排者经岛协议编译 RC=0（3.42 s / 5.72 GB）、独立导入探针
  RC=0（3.23 s / 5.55 GB），四个真实声明公理面均标准三。文件头提到的
  `g3c_curve_gamma4_ge` 不存在，不能按注释计资产。
- **端点证明未验收**：约 801 行 `FhbG3posEndpoint.lean` 是生成件；数值区间
  `[0.00736218,0.00736247]` 与生成器不等于 Lean 证明，超时前没有 RC=0 结果。
  不为部分端点再自动投入长编译或大规模生成。
- **数值路线诊断**：车道称 V/S/D 极值不对齐使精确值域装配仍留下约 0.01–0.013
  松弛，故端点尾段需凹性 + 端点；这些数值仅作导航，未上升为形式证据。内部区域、
  尾部凹性、G2/N3D 及 m3/m4/m5 均未闭。定案与日志见快照 `ORCHESTRATOR_NOTE.md`、
  `ORCHESTRATOR_CHECK/`。
- **相关止损**：旧 Bernstein agent-3 在止损后出现 headless 编译活动；leaf36F
  仍 RC=1（recursion depth、mod_cast、whnf heartbeat），随后擅自启动的 leaf36G 也已按
  核实 PID 终止，没有合格叶。WIP 已备份并再次写明禁止**无头**续跑；不派接管、不在
  当前上下文重开 BernsteinKit。以后若有新表示或性价比证据，可由用户明批 fresh
  重启；无头 wire 尚未确认停止，下轮必须复查。

## 1.18 单债局部代数化探针（`nli-algebraize-fat1-scout-w1`，2026-11-18）

- **条件 GO（数值），未真实 −1**：目标 `nliRestQITNPEA1_1_2`，零 Lean、零 patch。
  编排者复跑确认主支为 **γ4/2>0.0057**，估计余量 `m≈0.03496919`，极小在
  `(2.52,2,2hminus,2hplus,2,2)`；推荐 6 slab + 2 超越区，两半
  `ρ≈0.12456/0.13908`。所有数字和覆盖仍是网格估计，不是证明。
- **数学结构**：归并成 6 组后，18 个 atn2 系数均负，故下界需要 atan 上界；
  Δ 为共同平方根核，正侧 T5、负侧端点锚 Hermite 二次与分段 √ 界在数值上显著优于
  整盒线性界。最终有理式不要通分（单项 T5 分子已达 7,260 项），应走现有 enclosure。
- **编排者修复闸 1（跨零方向）**：G4 左区有 24/15625 点 `t̂<0`，脚本仍用 T5；
  局部反向最大约 `1.98e−14`，合成界未失真，但正式引理必须符号感知。负侧 T7
  实为上界（交付候选表的方向表述有误），可用于该窄片。
- **编排者修复闸 2（实际 t̂ 锚区间）**：原 Hermite 只在真实 t 区间验证，少数 t̂
  出界导致局部上界失败（最差 `−7.93e−7`）。按 t̂ 重锚后 7/8 组恢复，
  **bB+ G3 仍失败（−5.15e−5）**，须加切或换更高阶界；直接换 T7 的左端误差约
  0.0111，不能当免费修复。故原 DELIVERY §7 清单不得直接量产，w2 未批。
- 独立审计与复跑日志在快照 `ORCHESTRATOR_CHECK/`。后续若获批，先交修复后的误差账，
  再做 Lean 引理；不重启 BernsteinKit、不动 certtm hold 项。

## 1.19 cell3 wt2A 核分层证书暂缓（`cell3-wt2a-core-w1`，2026-11-18）

- **暂缓（2 h 超时，可重启），未真实 −1**：turn cancelled，无 cell3 编译进程；
  快照原只有 START，编排者已从 /tmp 抢救 island 源、数值脚本与日志到 `WIP/`。
  无 DELIVERY/patch，主仓未落库；本次 timeout 不判路线不可行。
- **数值路线仍有信息**：Δ<0 cell 可对核义务 vacuous；y6 全高矩形损失过大，必须分层。
  但最终为 62 cell（9 vacuous、53 实 cell），远超原 12-cell 目标，说明低成本估计未成立。
- **机器层未通过**：886 行 `NliBanks20.lean` 的日志 RC=1，仍有 rewrite/defeq/导数/
  单调性/lfun 错误；master、三维核、bank 消费与 Assembly patch 均未完成。不得把
  62-cell 数值下界或生成数据写成 Lean 证书。
- **Probe20 已独立验收**：编排者从快照源复跑 RC=0（3.30 s / 5.56 GB），
  `matan_le_one`、`sol_euler4_eq`、`dih4_eq` 均标准三；这只证明三个小引理，
  不改变机器层与核未闭合的状态。
- **可重启入口**：fresh 从 WIP 先修机器层与一个代表 cell，若不能显著减少 cell/
  每 cell 行数则继续暂缓，不做大规模 auto-gen。详见快照 `ORCHESTRATOR_NOTE.md`。

## 1.20 FHB g3pos-w2 右端点真证（`fhb-g3pos-w2`，2026-11-18）

- **Phase 1 阶段完成；整体暂缓（可重启），未真实 −1**。agent-12 超时发生在最终
  DELIVERY 前，快照无 DELIVERY，但 patch/Evidence/日志齐全；主仓未应用 patch。
- **旧 WIP 不是单纯慢**：r0 暴露常数截断、根值手抄、假精确等式、非法命名实参、
  D 因子错位等系统问题。v2 修复后，端点编译通过；这再次说明 timeout 本身既不能
  判死，也不能替代独立验收。
- **端点已独立验收**：编排者隔离应用 patch 并逐字节比对曲线与端点源，独立重编
  RC=0（263.35 s / 6.90 GB）；消费探针 RC=0（3.37 s / 5.55 GB），
  `g3c_endpoint_gamma4` 与 consumption 均标准三。即
  `7e-3 ≤ gamma4fgcy (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 lmfun` 为真证。
- **端点不等于曲线**：Phase 2 只有数值评估，F' 在 `[2.63,2.6508]` 估计 ≤−0.2488，
  可用“单调尾部 + 已证右端点”，不需凹性桥或左端点；其导数闭式、盒界与生成成本均未
  形式化。内部区域、G2/N3D、m3/m4/m5 未闭，故 FHBa 未减债。
- **可重启入口**：从已验收端点 fresh，先证一阶导数闭式与一个尾部小盒界，再决定是否
  展开；不自动发车、不做大规模生成。独立日志与定案在快照 `ORCHESTRATOR_NOTE.md`、
  `ORCHESTRATOR_CHECK/`。

## 1.21 TXQTPVC 常数权重消析取否证（`disjunction-lp-scout-w1`，2026-11-19）

- **具体路线 NO-GO，不是命题为假**：任意常数 `aᵢ≥0` 都有盒内证人点使
  `Σaᵢfᵢ>0`，故不能用一张非负线性组合证明六支析取。
- **三点 Farkas 证人独立复核**：编排者按 dual.log 坐标以 60 dps 重算，
  `E_μ[f]` 最小分量 **+0.001271705**；μ 非负，三点在现行 `nb17` 与较宽 hminus
  档内均满足 Lean 盒。对偶逻辑与 `0∉conv{f}` 一致。
- **重放打包问题**：`subset.npy` 长度 156、`mu.npy` 长度 138，不是同一求解状态，
  原 verify_points.py 的输出不可采用；上述结论改为直接按 dual.log 实际坐标复算。
  审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。
- h0cut 单分片也数值失败；更细分片/变权重不优先。析取本身为真仍只是 ESTIMATE，
  SORRIED 51 不变，零 Lean、零 patch。

## 1.22 fat1 代数化修复账与 enclosure 暂缓（`nli-algebraize-fat1-w2`，2026-11-19）

- **暂缓（可重启），未真实 −1**：两条 Taylor 引理独立编译 RC=0（4.17 s / 5.53 GB）
  且标准三；r2 复核确认 18 项归并 6 个精确三元组，直接 dih 系数与常数项与 Lean
  展开一致，scout 多加 C_SOL 属保守高估。
- **ERRATA（w2 对 s_hi 的归因）**：scout m12 与编排者 audit 都是 `D<=Dmid`，没有
  `D<=m1` 转录错。G3 在精确锚下失败，外扩到 1e-6 有理锚后 minA=+1.4021e−15，
  所以真正差异是**有理锚**。该值仅为数值临界，不能当 Lean 证书；94 条断言为车道
  日志，未由编排者全量重跑。
- **朴素 enclosure 具体路线不可行**：r5 的 6001 叶后 bB- 仍 −0.56024、bB+ 仍
  −0.50489。它不是 bank 为假的证据；一阶 Taylor 叶 10³–10⁴ 只是估计，未实现。
- bank、t-enclosure、atan(B_g)、G 正性、slab/Δ、覆盖与 Assembly 接线均未闭合，
  SORRIED 51 / AXIOM 585 不变。后续先形式化有理锚与 t̂ enclosure，再考虑小叶 pilot；
  不自动发车、不做 10⁵ 叶农场。审计在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。

## 1.23 联合包络外推与 QITNPEA1 分母勘误（`joint-envelope-extension-scout-w1`，2026-11-19）

- **零 Lean 侦察已收线，无顶层减债**。交付完整，编排者复跑并盒扫描与精确服务算术；
  所有全局极值仍为 ESTIMATE，argmin 附近的局部区间不是全盒证书。
- **#147 否证降调**：原报告只排除了把 dihY 值域与仿射项最小值分别代入的仿射平面
  服务算法，并未否定利用相关性的任意联合平面，更未否定原不等式。独立复算该服务
  公式的两段斜率与峰值一致，但 c0 处原目标上界仍为正，不能当作反例。
- **QITNPEA1 原 R2 判词有分母错误**：模板 `PackingAuto21:681-689` 的分母为
  `1+bankGenMid i3+bankGenMid i4`，故 **1_1 的 w=3**，不是 w=2；γ4≥23/2000 对它的
  精确服务余量为 −0.0056，原“一面闭 1_0/1_1/2_0”不成立。
- **修正后的数值候选**：并盒 U 的 min γ4≈0.016989287956，γ4≥23/2000 的估计余量
  ≈+0.005489287956。若将来真证该全盒下界，可服务当前在案 **1_0、1_2(fat1)、2_0**
  三条，不覆盖 1_1；2_1/2_2 已证。它可能提供绕开 fat1 atan/G3 误差账的替代路线，
  但全盒证书成本未知，不记 −3、不自动发车。
- ox3q1h 的 125 record-group、B0 三面不可外推与 R3 单走等车道数据保留在快照，
  本次未全量重跑，不升级为形式结论。独立审计见快照 `ORCHESTRATOR_CHECK/AUDIT.md`；
  后续候选 `qitnpea1-shared-floor-w1` 等用户裁决。

## 1.24 TerminalV11 家族压缩的组织性资产与口径勘误（`terminal11-family-compression-w1`，2026-11-19）

- **零 Lean 第一阶段收线，无顶层减债**。编排者从存档输入重跑 parse/assign/cluster，
  parsed109、FAMILIES 与 cluster 输出逐字节一致；109 条唯一 ID、85/21/3 路由计数成立。
- **覆盖算术勘误**：FAMILIES 实际有 10 个 FARM 标签（合并 K1 两形也有 9 个概念组），
  不是 8 族。K1/K2/K3/K4/K5 五个参数化 schema 覆盖 **80 支**；K6 两支与 K7/K10/K11
  各一支，共 **5 支仍须独立处理**，不能写成 85 支完整压成 5 个目标。
- **置换检查范围勘误**：cluster 只对 74 条带 tree 的显式 def 检查置换；35 条 hex
  全部没有 tree，直接返回 None。因此“109 条置换等价对=0”只能降为“74 条显式 def
  在该算法下未发现等价对”。hex 的 π 对称和注册顺序须另证，数值验证不等于 Lean 转运。
- **R1 的 ly 文档公式勘误**：正确为 `1−(y−2)/0.52=(2.52−y)/0.52`，不是
  `(4.52−y)/2.52`（`SphereKit.lean:156`）。evalfun 实现与 Lean 一致，故这是文档错误；
  完整 probe 网格未由编排者重跑，所有极值/覆盖率仍为 ESTIMATE。
- 可保留的是 AST、结构分族、共享原子、槽区间表和人工审查伪代码。模板中的
  `<CertT1/S1/E1>`、taum/dihY 超越核、sqrt/delta 耦合与退化带都未解决；发射侧
  70%/150–250 mh 是不预支的估计。审计见快照 `ORCHESTRATOR_CHECK/AUDIT.md`；
  不自动进入第二阶段或 85 支发射。

## 1.25 fat1 交错 Taylor 精确界（`fat1-g3-exact-w1`，2026-11-19）

- **局部 Lean pilot 独立验收通过，未落库、未减顶层债**。205 行候选文件
  `NliQitnpea12ArctanSeries.lean` 证明
  `∀ m, ∀ t≤0, arctan t ≤ Σ_{i=0}^{2m+1} (-1)^i t^(2i+1)/(2i+1)`，
  方法为几何级数 + FTC；m=9 给出 G3 的 39 次显式上界。隔离 apply 与快照源逐字节一致，
  主仓 `git apply --check` PASS，未应用。
- 编排者重编 RC=0（4.46 s / 最大 RSS 约 5.55 GB），原文件零 error/warning，三条
  `#print axioms` 均恰标准三。另补 m=1 七次展开与负系数反向放缩两个真实消费例，
  均编译通过且标准三。通用上界对全部 t≤0 成立，**arctan 这一层不需要 Hermite 锚**。
- **G3 数值勘误复现**：g3_compare 确因约 −7.8e−62 的舍入伪影误选 b 变体，产生
  −5.15e−5；a 变体在扫描中触零。rounded 的 +1.4e−15 同样不是可消费余量。
  Hermite 仅记“本车道弃用”，不把切点触零夸大为所有 Hermite/SOS 路线普遍 NO-GO。
- n=4 网格两半区 min G≈0.0798、min γ4−G>0 均独立复现，仍属 ESTIMATE；
  G 正性、t̂ 方向链、slab/Δ、覆盖和 Assembly 未闭合。m=3/5/7/9 筛选未给 G2(bB+)
  合格项，故不得向后续传播“全部负组统一 m=9”的口径，其它组须逐组选阶。
- 审计见快照 `ORCHESTRATOR_CHECK/AUDIT.md`。`fat1-g-positivity-w1` 已于
  2026-11-19 获批发车，只做代表小区；`qitnpea1-shared-floor-w1` 仍待用户裁决，
  两条路线不得重复建设相同 glue。SORRIED 51 / AXIOM 585 不变。

## 1.26 fat1 G 正性小区 WIP 暂缓（`fat1-g-positivity-w1`，2026-11-19）

- **2 h 超时，暂缓（可重启），不是判死；不自动 resume**。DELIVERY/Evidence 均为
  “编译结果后补”的草案，没有可接受的 fat1_main、公理面或 patch。
- 最新 farm 源 **2,975 行**，已抢救到快照 `ORCHESTRATOR_CHECK/`；快照 patch 为
  **2,955 行**旧版。原样独立编译 RC=1（18.55 s / 约 8.14 GB），末尾
  `unterminated comment`。隔离闭合 14 处章节注释后仍 RC=1，日志含 82 个 `error:`，
  涉及解析、sqrt 改写、盒成员与代数归约；故不是“只差注释”，按止损停止接管。
- **可复用的是数学设计而非生成整件**：临界角附近 bB− 小区、Δ 中心展开以降低
  IExpr 依赖、18→6 分组、逐组 S7/S11/T5 与 kernel checkPos。Fraction 包络与网格
  min 值仍只是车道导航，不是全盒 Lean 证书。205 行通用交错 Taylor 引理已另件落库
  `248fde92`，不与本 WIP 的失败混合。
- 后续若获用户另批，fresh 从快照 WIP，先修发射器并逐段验证，再把主证明压成可人工
  审查的小文件；不直接重生成约 3,000 行整件，也不把旧 patch_with_series（含已落库
  依赖）应用主仓。审计见快照 `ORCHESTRATOR_CHECK/AUDIT.md`；SORRIED 51 / AXIOM 585 不变。

## 2. 已闭件 1：`nliRestQITNPEA4003532128a`

- 债点：`Assembly.lean:1394`；bank `PackingAuto21:460`；盒
  `[2hmin,2hplus]×[2,√8]×[√2,√2]³×[2,√8]`，结论 `δ4>25 ∨ δ>0.14 ∨ δ<0`。
- 关键化简：两侧 `√2` 夹 ⇒ `y3=y4=y5=√2` ⇒ `x3=x4=x5=2`（`x_i=y_i²`），
  于是
  - `delta4Y = x1·(x2+x6−x1)`，
  - `deltaY = (x2x6)(8−x1) − 2(x1−(x2+x6))²`。
- 残区 `δ4≤25`：用 `u=8−x1`、`t=x2+x6−x1`，得
  `δ ≥ g(u,t)=16u−4u²+4tu−2t²`；`g` 对 t 凹 ⇒ 只查顶点 `t=u`；
  弦线 `t ≤ 3.558+0.587(u−0.97325936)` 盖住凸曲线 `25/(8−u)`。
- 结果：`δ>0.14` 余量 **0.1759**，数值真 min **0.31759**；
  `NliQitnpea.lean` **142 行**，标准三，零证书。
- 先例意义：这是“先降维/代数化，再决定是否需要证书”的样板。

## 3. 已闭件 2：`nliPackIneqDefA`（WIRE）

- `PackIneqDefA = UKBRPFE_bank ∧ WAZLDCD_bank ∧ BIEFJHU_bank`；
  六个组件全部在库真证。
- Assembly +14/−2（1 import + 1 body），陈述逐字未动；标准三。
- 先例意义：接到债点前先查“是不是只差接线”，不要直接发证书车道。

## 4. TSKAJXY-XLLIPLS：`nliTskXLLIPLS`（FARM-CERT，已降级为本地窗口）

- bank：`PackingAuto21:308`；盒 `[2hplus,√8]×[2,2.01]²×[2hplus,2.8]×[2,2.01]²`，
  结论 `0 < gamma4fgcy y lmfun`。
- **叶**：证书树把 6 维盒切成 6,512 个 6 维子盒；每叶 = `kBox_i` + `TMParams` +
  一条 `checkPosTMHullC/P ... = true := by decide +kernel` 定理。叶定理经
  soundness 变成该子盒上的 `0 < expr`；6,512 叶 + 覆盖树 = 整个 bank。
- 进度（复刻扫描/内核实测，详见 pq 续1149/1150/1159/1164/1166）：
  - 原 `.arctanK` AST：0/6,512 PASS；`.atan1K` 后 **5,012/6,512**；
  - 族 A 100 叶：最宽维二分一次 100/100 PASS；
  - 族 B 1,400 叶：`iteHullTM2` guard 跳变；**分支一致性是精确恒等**
    （6 个全局 ite 节点，HOL `atn2` 分支树；`max|t−e|=1.56e−61`，零集上 `t=e=π/4`）。
  - **Rule P**（点锚定，无条件 sound）1,400/1,400 PASS，min 余量 +0.00306；
    实现 `058b2c12`，优化 `229f731f`（点求值 11–20×，单叶 26.7–27.1 s /
    10.2–10.3 GB）。1,400 回放 ≈ **15 CPU·h**（单 lean ~10.3 h）。
- **口径校正（2026-11-15 复核）**：上面的 5,012/6,512 是 **Python 复刻扫描**，
  不是内核验收；仓库里只有 pilot 叶 `Atan1Leaf0/657` 的 olean。**全盒内核收线 =
  1,400（族 B，在飞）+ 5,112 叶（5,012 旧叶 + 族 A 100 叶）**：
  Rule P ≈ **37.6 CPU·h**（27 s/叶），旧 Rule C ≈ **464 CPU·h**（333 s/叶），
  Rule P 是唯一本地可行路线。装配前必须补完这 5,112 叶的内核模块（~1.3–1.5 GB olean）。
- **2026-11-16 01:46 全盒预扫收线**（`rulep-fullbox-prescan-w1`，4 worker，无 lean）：
  非族 B **5,112 叶** = 5,010 旧叶 + 100 族 A + 2 pilot；**5,012 PASS / 100 FAIL**
  （98.04%）；FAIL **恰好 = 族 A 100/100**（`oracle-reject`，非族 A 零 FAIL）。
  PASS lb min **+3.858e−6**（叶 2078）、P50 +3.62e−3；**516 叶 <1e−3、3 叶 <1e−5**。
  族 A 的 lb 与旧 C-rule 最大差 5e−14 ⇒ **Rule P 不收紧族 A，必须按 CALIB2 切叶**
  （100 → 200 子叶）。总 18.88 CPU·h；`kernel_worklist_pass.idx` 5,012 叶，
  27–31 s/叶 ≈ **37.6–43.2 h 单 lean**。
- **2026-11-16 02:20 族 A 切叶收线**（`famsplit-w1`，2 worker，无 lean）：100 父叶
  沿最宽实测宽度维 dyadic 二分 → **200 子盒，Rule P 200/200 PASS**（lb min
  **+3.526e−3**、P50 +5.060e−3、max +9.460e−3）；100/100 父叶翻正；
  **0 Rule C fallback**；0.728 CPU·h / 22 min；200 个未编译模块在快照 `modules/`。
  ⇒ 全盒内核波 = **5,012 + 200 = 5,212 叶**，单 lean **≈39–45 h**。
- **2026-11-16 05:36 族 B 1,400 叶收线**（`rulep-replay-w2`）：预扫 + 内核
  **1,400/1,400 PASS、0 FAIL**；`_check` 全 `[propext, Quot.sound]`、`_pos` 全标准三；
  `sorryAx/error/warning` 0；总 **15.78 CPU·h**（预扫 4.81 + 内核 10.97）；内核
  P50/P95 **28/30 s**、max RSS **9.620 GiB**；pool 374 MB（1,400 olean 258 KB/叶，
  已备份 `rulep-replay-w1/pool_olean/` 341 MB）。1,400 olean 经 MANIFEST 0 不符 +
  3 叶端到端消费探针复核。
- **2026-11-16 05:36 全盒内核波发车**：`rulep-fullbox-kernel-w1`——**5,212 叶**
  （5,012 旧 + 200 族 A）+ 1,400 B = 6,612 叶池；15 叶/块 + checkpoint + 每批
  axiom probe；单 lean **39–45 h**；preflight 3 叶后量产。
- **2026-11-16 10:19 装配材料就绪**（`tskasm-prep-w1`，纯 Python）：6,612 叶
  三重核对全过；族 A 100→200 替换后树 **6,612 叶/13,223 节点**逐节点精确 tile；
  **方案 X = 202 模块/23,832 行**（泛型 `PosTree` 134 行 + 199 shard + 骨架/收尾），
  decide 位点仅 397，可编译源已生成；`VALIDATE_OK` 174,135 项 0 失败；
  装配净预算 **5–8 h**（kernel 波收线后）；唯二 TODO = `tsk_atan1_eval` 桥与
  `tsk_box_eq := rfl` 复核。
- **2026-11-16 19:25 装配预检收线**（`asm-precheck-w1`，零 lean）：双 TODO 纸面判定
  **均 `rfl`**（HIGH 置信；AST 逐字节对拍，最终裁决 = P0 分钟级探针）；**抓到阻断级
  缺陷 A**——6,612 条 `.leaf` 首实参被生成器写成模块名（validate.py 漏检），另
  203 个 cap-24 stale shard 与 Close 缺 set_option——**三缺陷已由编排者按车道命令
  当场修复**（`tskasm-prep-w1/FIXES-APPLIED.md`）；落地 runbook 净装配
  **≈3–5.5 h 串行**（shard 波 1.7–3.3 h 为大头），落地起点 = P0 探针。
- **命名空间注意**：叶定理在模块根命名空间（`namespace Kepler.Interval.Cases`
  已闭合）⇒ 消费/探针写 `tskaJXY_xllipls_p_leaf<idx>_check/_pos`；辅助 def
  `kParams*/kBox*` 才在 `Kepler.Interval.Cases` 下。
- **不要**再做 guard 超平面切分：分支恒等让切分零收益（`guardcons-w1` 判定）。
- **不要**把“130 GB olean”当真：TSKAJXY 叶 olean 实测 ~0.2 MB/叶 ⇒ 全盒 ~1.3–1.5 GB；
  130 GB 是混入 LP 叶 16–21 MB/叶 的误估。

## 5. ZTGIJCF4：10 条剩余（MATH-FARM → 主支套件）

- 16 个实例；**6 个已证**（`NliBanks4/5`）恰好是 `H=rhoX−8deltaX` **正角点**那 6 个
  （+16.9…+226.1）。
- 剩余 10 个的角点全负（−51.31…−187.77）；`H` 在箱上逐变量单调 ⇒
  **`rad2>2` 第二析取支在整个箱上为假**，唯一活路是第一析取支 `gamma4fgcy` 主支。
- 已落库归约资产（`1b401275`，567 行，36/36 标准三）：
  - `NliBanksZTGIJCF4Route`：`ztg_of_main`（主支>0 ⇒ bank）、10 条 `_rad2_refuted`、
    10 条 `_main_forced`；
  - `NliBanksZTGIJCF4Bounds`：`γ4≥G ∧ dihY≥D ⇒ bank` + 4 条条件归约。
- 关键正面发现：10/10 主支最小点都落在 **kink 增广角点集**（96–216 点/条，
  与 `NliBanks9` 的有限候选归约吻合）。逐条数值余量：3 条 +0.03698
  （可解耦 `γ4≥0.06`+`dihY≥1.1`）、1 条 +0.02434、1 条 +0.00754、3 条 +0.00359、
  1 条 +0.02677、`0_0_0_0` **+0.00078**（最紧）。
- 下一步：**`ztgmain-w1`**（2026-11-15 19:12 已发车；19:49 Phase 0 收线）——
  **dihY 半边找到便宜路线**：`dihY ≥ π/4 ⟺ Δ4 ≤ √(4x1Δ)`，对有理 `s` 化为
  `s²Δ4² ≤ 4x1Δ`；`F'=4x1lo·Δ−s²Δ4²` 逐变量凹 ⇒ 64 角 + 6 条凹性步。
  `s=11/5` 时 `D_lb=1.143674897`（min F' +619.99）；`s=6/5` 时
  `D_lb=0.849988714`（+684.85）。4 条解耦设计点 `G=0.0403/0.0703`，
  余量 +2.5e−2/+1.6e−2，侧条件 +8.4e−3/+5.3e−3。
- **但 γ4 半边是阻塞**：逐分量包络丢 0.22–0.77、单调/折面路线数值为假；
  唯一活路是逐片凹性（9/10 成立，`0_1_0_0` 例外）+ 216 角点表，
  需宽盒 2 阶导包络 + ~600 角度区间引理/条 ⇒ 4 条约 10 万行生成码、5–7 天；
  6 条 joint 同阻塞（`main` 凹性余量仅 0.0146，`0_1_0_0` 破）。
  ⇒ 4 条解耦本窗口未关；先落 Kit A（dihY，~600 行，w2 收线后编译），
  γ4 Kit B 另立车道/另裁决。
- **2026-11-16 21:15 Kit A 落库**（`ztgmain-w1`，`f47d472f`，cone-neutral）：
  `ZTGDihKit` 8 声明全标准三（编排者岛协议+亲跑 axioms 复验）——
  `ztg_atn2_ge`（**角度下界化归多项式不等式**：`s·|y|≤x ⇒ atn2 x y ≥ arctan s − π/2`）
  + 有理 arctan 下界（`arctan(8/5) ≥ 1.008`/`arctan(6/5) ≥ 0.875`）+ 逐线证书多项式
  `ztgG`（irreducible）。四箱端点未闭：`ztgG_box5` 两条实现路线 `isDefEq` 爆
  40M heartbeats（数学 32/32 线已验证 +1218/+684；候选解法三条含逐叶 `have` 链
  ~1k 行）。Phase-0：六条 joint 债 dihY 直接形式不成立（需联合 trade-off ✓）。
  下一车道清单见 `ztgmain-w1/DELIVERY.md` §4。
- **2026-11-17 08:15 四箱收口落库**（`ztgmain-w2`，`decbc61c`，cone-neutral）：
  `NliBanksZTGIJCF4Dih`（新模块 6,191 行/143 声明全标准三）——**`ztgG_box5` (c) 路线
  一轮成型**（32 角点假设显式命名 + 31 步 Jensen 链 term-mode + 逐坐标二次符号化/
  linarith，零 defeq 爆炸）；**`ztg_dihY_1_1_0_0/0_1_1_0/0_1_0_1 : 1.008 ≤ dihY`、
  `ztg_dihY_0_0_1_1 : 0.875 ≤ dihY`**（编排者亲跑 axioms 复验）。勘误：w1 字面角点
  不可证 → 改 `NliBanks7.hminus_ge_123175` + `mi_hminus_lt_h0`（零新 import）；
  gen_dih.py 三 latent bug 修复。数学新发现：`deltaX` 在每个坐标 x2..x6 都是二次。
  ⛔ γ4 侧仍等角点表路线裁决（Gate-0 NO-GO 后）；四箱+Kit A = ZTGIJCF4 任何 γ4
  路线的共同前置，已备。
- **2026-11-17 13:30 γ4 侧角点表侦察判 GO**（`ztg-g4corner-scout-w1`，零 lean 33 min）：
  **真实成本 ~1.2–2.4 万行（中位 ~1.8 万）/4–7 车道日，比"10 万行"外推低 4–8×**。
  成本杠杆 = **候选集塌缩 216→8 角点/债**（36 cells：34 逐片单调-up、36 全逐片凹，
  双基点族 216+64 独立复核 ⇒ 候选塌缩 {lo, kink}，每债 8 个纯有理角点，8 点 min γ4
  与 216 点逐位一致）；恒等式覆盖率 0/1752（Gamma4Sharp 不命中本盒族，非杠杆）。
  扩盒消灭 hminus（有理端点 2.4635/2.46352，依据 `nb17_two_hminus_bounds`）。
  成本主体 = 16 逐片单调 + 2 逐片凹性符号判定证书（8–15k 行；`Gamma4Deriv1-8` 闭式
  已落库 `c05928f5c`，sign GAP 明示）；风险 R1 = 宽盒包络精度（fallback 全凹性证书
  数值 36/36 为真）。四债角点余量 +2.52e−2~+3.43e−2；**施工车道待用户批
  （4–7 车道日，dihY 半边已全落库，补齐即最多 −4）**。
  路线的共同前置，已备。
- **ERRATA（`ztgijcf4-w1/TABLE.md`）**：`1_0_0_0`/`0_0_1_0`/`0_0_0_1` 的
  `min γ4` 实为 **0.0139727**（非 0.02257），解耦界改 **−0.01085**；
  `min γ4` 与 `min main` 的 argmin 不同；kink 角点须按槽型过滤
  （critical 槽不含 y=2），去重后 216/144/96；`0_0_0_0` 的 γ4 角点 min
  **−0.0055589** 与 `Gamma4ValCorner0` 吻合。**不要**再按“折面最小”设计
  （`g4w_gamma4_fold_min_y1` 前提在本箱为假）。
- **`g4hol-w1` 补充（2026-11-16）**：HOL 合并层已 100% 移植；剩余 10 条的真正
  杠杆是**引擎**（二阶 Taylor + 局部单调剪枝 + 凸性 + 自适应），HOL 实测
  ZTGIJCF4 16 条仅 76 CPU·h/556 叶。建议立 `g4port-w1` 引擎车道，pilot
  `0_0_0_0` + `0_1_0_0` + ox3q1h `#147`，判停线 ≤3 CPU·h/≤5k 行每件。
- **`g4port-w1` 引擎原型 GO（条件式，2026-11-16 09:39）**：pilot `0_0_0_0`
  **81 叶** / `0_1_0_0` **60 叶**（s=10），估计内核 **1.35/1.00 CPU·h**、
  行数 **4.15k/3.10k**；s=3 时 30/22 叶。**Gate = Lean `Jet3` 三阶导界
  等效 safety ≲10**（s=30 ⇒ 380/288 叶，<10× NO-GO 线内但超 2× GO 线）。
  Gate-0（1 天）过关 ⇒ `CertTM2.lean`(~2k 行)+`BBTree2` ⇒ 落地
  #147(47)→p1(81)→p2(60)。Kit A（dihY 半边）仍是便宜且可复用的件；
  若 CertTM2 成立，10 条 ZTGIJCF4 主支可直接引擎闭合（HOL 折算 ≈4–8 CPU·h）。

## 6. hLP / LP（与 nli* 同账本，但独立）

- `lpArchiveCertificatesDebt` 背后 43,078 条 LP 终端记录；**189/189 infeasible 已落库**
  （`LPLeafInfeas00` 零 sorry + 189 个 `Kepler.LP.T*` Farkas 模块），所以实际待证 =
  **42,889 bound 叶**。
- `lp-pilot-w1` 定标：生成 120.6 + 编译/内核 674.2 = **794.8 CPU·h**；
  1 lean 15–19 天、2 lean×10 叶批 ≈7.8 天、128 核农场理想 ≈6.2 h；
  批量 20 叶安全上限（19.3 GB）；35/35 `bound` 标准三。
- **磁盘是硬墙**：olean 0.70–0.95 TB（中心 0.83 TB）；本机清理后 237 GB 仍不够。
  选项：≥1 TB（建议 1.2 TB）外部盘 + 2 lean×10 叶批 ≈7.8 天 / 农场（≥0.85 TB）/
  继续冻结。
- 旧成本档（`LPPilot` 的 socert 3.5 min/条、Data 423 s 等）作废；以 `lp-pilot-w1`
  的 CALIB 为准。

### 6.1 LP 对偶表示审计（`lp-dual-representation-audit-w1`，2026-11-18）

- **阶段完成，单叶 A/B = GO（仅设计，未发车）**。137,780 B→19,380,352 B 是
  `T114084514923t0000` 闭合试点叶；Text 骨架 174 模块是另一对象，源中位约 71.9 KB、
  olean 主体约 3.93 MB，回归约 19,161 B/定理，不能混用口径。
- CALIB 直接记录生产形 Data 19.33 MB / Assembly 0.07 MB，支持**数据字面量约占
  99.6%**；`by decide` 主要成本是 elaboration wall/RSS，不应把 olean 字节都归给 decide。
  这些是历史实测；当前对应 /tmp olean 已不在池，未重新编译。
- **单叶 A/B 值得做**：ByteArray packed 与单 Nat 容器各一臂，另可测分片 decide 的 CPU；
  必须先探 ByteArray.get 和 Nat 解码，指标为 wall/RSS/olean/axioms/陈述不变。
  **原 Phase 0 新增 250 条 sorry 违反硬规则，禁止执行**；改 `trivial` 闭合对照 +
  复用现有骨架。车队级重构、4–10× 缩小和 0.83 TB 外推仍未验证，不预支、不自动发车。
- 独立审计与复跑日志在快照 `ORCHESTRATOR_CHECK/`。LP/D 证书层未改。

### 6.2 packed 单叶表示：负系数漏失与修复版性能门槛（2026-11-19）

- **原 A2 拒收**：虽然 olean 363,208 B、声明输出与 A0 相同，但字段级内核检查证明
  cs 不等（b/certY 相等）。生成器未识别 `(i,(-c))` 的嵌套括号，系统性删除所有负系数，
  故原 53× 结论无效。
- **编排者修复版的语义合格**：修复互斥括号解析后，cs/b/certY 全部由 `decide`
  证等，六声明输出与 A0 一致；olean = **406,304 B（约 47.8×）**。
- **但 wall 未过预注册门槛**：两轮平均修复版/A0 ≈ **1.42×**，超过 1.30×，故记
  UNRESOLVED，不车队化、不改 LP/D 层。需要优化解码/发射或由用户重新裁决阈值。
- 原始 cs 经 Lean 计数为 5,565 项，与元数据 3202 nnz 不一致，旧 account_leaf_source.py
  的同类括号统计也不可靠；不得按 3202 直接外推收益。patch 草案目标不在主仓，
  apply-check 失败。审计、修复源与日志在快照 `ORCHESTRATOR_CHECK/`。
### 6.3 packed-w2 双流单叶 GO 与构建池事故（2026-11-19）

- **b2 单叶 bounded GO，编排者独立两轮验收通过**。从 A0 重生成 Data 与交付源逐字节
  一致，Assembly 与 A0 一致；cs/b/certY 字段级 `decide` 等价均无公理，Count=
  5,565/5,565，六声明输出逐字节相同，`bound/bound_lt` 标准三。
- 独立 wall/A0：r1=1.062659、r2=1.048097；均值 A0=51.42 s、b2=54.27 s，
  合并比 **1.055329**，通过预注册 ≤1.30×。A0 olean=19,404,032 B，b2=
  **395,784 B**（约49.0×）；最大 RSS=8.254 GB，全部日志零 error/warning。
- 设计 = 双流 base-2^64 条目打包 + hex 发射 + 单趟解码；车道分解探针提示主要成本在
  giant-Nat 字面量 elaboration，而非解码循环。目标源不在主仓 tracked 集，**没有可落
  patch，不车队化、不改 LP/D 层、不按单叶倍数外推总体磁盘**。
- **独立运行态事故**：该车建 symlink farm 时父目录穿透，误替换主仓 LP 构建产物；
  tracked 源码无损，但根验收在恢复前不可复跑。精确清点以 `priority-queue.md` 文件头
  为唯一出处；193 个受损 olean 全部有 tracked 源，恢复不等于重放 42,889 条 bound 债。
  处置见 `priority-queue.md` §3，未获用户批准前不重建。审计在快照
  `ORCHESTRATOR_CHECK/{AUDIT,INCIDENT_AUDIT}.md`。

## 7. 路线原则（nli 专用）

1. **先数学，后证书**：分诊时先找 WIRE / 单调性 / 代数恒等式 / 分支一致 /
   有限候选；证书是通用兜底。
2. **导数信息已在证书里**：`TaylorM` 是一阶 Taylor 模型（`dfB` 斜率区间 + `err`），
   不是裸高阶展开；单调性/凸性都可以作为专门规则或手写引理加入。
3. **不做假陈述、不绕假桩**：盒/析取支发现为空或假 → `AUDIT` 记档，走 SF/DEF-FIX；
   `ht4nn` 是反面先例。
4. **hold 边界**：certtm 的 TM3 量产 / Mono\* / D 其它项仍 hold；Rule P 是
   bounded opt-in（`058b2c12` / `229f731f`）；585 信任基座不动。
5. **负结果也是资产**：rad2 路线、ZTGIJCF4 模板、guard 超平面切分都已被机器证伪；
   后续工单不要再重复试。
6. **timeout = 暂缓，不是判死（2026-11-18 用户指正）**：先查 wire/快照/进程，再保存
   WIP；只把本次执行记为 `暂缓（可重启）`。不自动 resume 是防重复与资源冲突，不能
   推出算法不可行。NO-GO 只用于有明确反例、可信结构否证或信任冲突的**具体路线**；
   以后出现新证据或合适性价比时可从快照 fresh 重启。

## 8. 下一步清单（2026-11-18 更新）

1. **A/B/C 侦察已全部收线**：A 二阶导代数化（§1.12，含 factor-2 勘误）；
   B0 联合包络数值 GO（§1.11）；Bernstein 多项式 GO、通用超越后端 NO-GO（§1.10）。
   三者都只提供路线与数据，未移动 SORRIED。
2. **Hessian Lean 已收线为 UNRESOLVED**：W5 + 6 条对角二阶导真证可复用；
  整盒量化三路均否证/不可行，逐坐标凹性已有精确反例（§1.12）。固定 all-2 基点
  只能作低优先机械件，**B0 母定理不得按原凹性方案发车**。
3. **FHB floor 已收线为 UNRESOLVED**：三轴一阶导全盒为正有高精度数值反例；
   已验收的只有“凹性 + 端点 ⇒ m3/m4/m5”归约，H1/H2 均未证（§1.14）。不得续走旧单调路线。
4. **cell3 wt 已收线为 UNRESOLVED**：wt2A 核归约与消费探针标准三，核本身和 wt1 未证；
   wt2A 的 y5 全盒严格增有高精度数值反例（§1.15）。8–12 cell 只是数值方案，不自动续发。
5. **当前授权在飞 2 条（另一编排会话的 cell3/Bernstein）**。
   `fat1-g-positivity-w1` 已超时记暂缓、可重启，WIP 与失败证据见 §1.26，不自动 resume；
   `lp-packed-single-leaf-w2` 的 b2 经独立两轮验收为单叶 bounded GO（§6.3），不车队化。
   QITNPEA1 共享下界、taum 数学侦察与其它暂缓资产不自动续发；实时回执以
   `priority-queue.md` §1 为准。六车道总结见
   [`history/nli-six-lanes-2026-11-18.md`](history/nli-six-lanes-2026-11-18.md)。
6. **其它排队**：QITNPEA1 共享下界 pilot、taum 数学侦察等；实时状态与回执见
   `priority-queue.md` §1–§2。
7. **既有非农场候选**：iyou-sharpv2、ZTG γ4 解耦 4、ox3q1h S2a；S2b 量产、农场、
   certtm/TM3/Mono*/D 层与 push 继续保持用户 hold。
8. **不再重复**：rad2 望远镜、CertTM2/Gate-0、IXPOTPA 旧 0.59 CPU·h、
   超越函数“整盒有理界 + 单分数组合”、FHBa/v2a 的 96 角点表、FHB floor 三轴一阶单调、
   cell3 wt2A 的 y5 全盒单调。

---

## 9. 逐债执行计划登记（2026-11-19 新设：启动即照做）

> **规则（2026-11-19 用户裁定）**：每债一卡，记「当前最优路线 + 依赖资产 +
> 启动即执行的工单模板 + 预算/止损」。真启动时照卡派单，不再重侦察。状态枚举：
> `可启动`（依赖齐备等点头）/ `有界试点建议`（先试再量产）/ `待侦察` / `等解冻` /
> `UNRESOLVED`；另两个派生态：`等批`（依赖已齐、用户明示暂不启动）、`在飞`
> （工单已发车，回执见 `priority-queue.md` §1）。数字以本文件 §1.x 判词 +
> `~/c17_backup/lane_snapshots/farm-ops-w1/DEBTS.tsv` 为唯一出处，本节只做执行
> 索引、不另抄数字。本节引用的编号一律是指针：`FARM_PLAN.md` §4 的本地工单
> N1–N5、§5 的农场批 F1–F5、§6 的解冻项 ①–⑤，含义见该文件；`PR-43` 指
> `docs/pitfall-register.md` 的生成代码书写规范条目。**覆盖对账表在 §9.5**
> （51 = 50 `nli*` + hLP 逐名）。

### 9.0 名词速查（第一次读卡先看这一段）

每条 `nli*` 债长得都差不多：**六个实变量 `y1..y6` 在一个「6 维盒」
（每维给定上下界）里变化，要证某个不等式在整个盒上成立**。六个变量描述的是
局部构形（与一个单形/胞腔相关的一组边长参数），盒就是这些参数的允许范围。
其余术语一句话版：

- **γ4（`gamma4fgcy`）**：HOL 传下来的非线性「打分」函数，大多数 rest 债的
  主角；由体积项、二面角项与一个可变乘子组合而成，不等式通常要求它在盒上
  为正或有下界。
- **dihY**：二面角函数；在 ZTG / ox3q1h 一族里与 γ4 联合出现，两者不能各自
  单独取下界（ox3q1h 已有反例，见 §1.4）。
- **lmfun**：γ4 内部的分段乘子（与 Marchal 四次式挂钩，在 `hminus` 处取 0）；
  它的「折面」会让最小值出现在拼接点而非普通角点。
- **2hminus / 2hplus**：两个有理常数 ≈ 2.4635 / 2.6508（`hminus`≈1.23175、
  `hplus`=1.3254）；绝大多数盒的端点就是它们（或 √2、√8、2.001 这类钉死值）。
- **析取支 / 合取债**：陈述形如「A ∨ B」时证一支即可；形如「A ∧ B ∧ …」时
  每个分量都要证，**缺一支不减债**（SORRIED 不动）。
- **角点表**：先用单调性/凹性证明「函数在盒上的最小值只能落在有限个角点
  （或折点）上」，再逐点精确求值——把连续问题压成有限次有理数检查。
- **Bernstein 叶 / peel 表示**：把盒上的多项式改写成 Bernstein 基；若全部
  系数同号，多项式全盒同号。一张「叶」= 一个子盒上的这样一次检查；
  「peel 表示」是本仓 2026-11-19 落库的手写剥皮写法（`9a4a9dc6`），绕开了
  MvPolynomial/Finsupp/decide 的内核归约死路。
- **叶 / 覆盖树 / 装配 / 胶水**：大盒切成子盒逐叶发证书，再用一棵覆盖树把
  所有叶拼回整盒；「装配」是最后接回 Assembly 债行的接线；「胶水」是把
  证书定理（往往对某个等价表达式证）与 bank 原陈述接起来的恒等式引理。
- **bb_arb 发射器**：现行分支定界证书生成器（Python `pipeline/`），把盒二分
  到每叶通过区间/TM 检查为止。
- **Rule P**：库内点锚定 TM-hull 叶检查规则（`058b2c12` + 优化 `229f731f`，
  有界 opt-in），单叶 27–31 s；TSKAJXY 6,612 叶全量走的就是它。
- **certtm / TM（Taylor 模型）**：处理 √/atan 等超越函数的区间估计封装；
  「certtm 特性开发」指为它补规则（log、负底、mixed-tm 析取），**不是**量产
  解冻。
- **农场**：一次性的大批量「发射 + 内核逐叶重放 + 装配」算力窗口，
  **用户保留项**；本节所有农场核时/磁盘都是 EST（recost TRUNC 下界外推），
  未批不动；解冻项清单 = FARM_PLAN §6 的 ①–⑤。
- **SORRIED −N**：锥内 sorry 债减少 N 条；唯一验收 = 编排者亲跑
  `#print axioms`。

### 9.1 有完整执行包（启动即可做）

**`nliCell3QZECFICwt2A` —— 52-cell 量产（状态：**已闭合 `1ec06b28`，2026-11-20**；六模块 `d733f61d` + 验收下沉 `Kepler.Targets.Wt2A`，90 件闭包亲验标准三；SORRIED 50→49，根面复验未做；olean 恢复已停止并交接新负责人（pq 续1385））**

- **这是什么**：`Assembly.lean:431`；HOL `ineq.hl:1443`（「QZECFIC wt2 A」）。
  6 维盒 `[√2,√2]³ × [2hminus,√8]² × [2,2hminus]`（前三维钉死在 √2），
  结论带 `h0cut y4/y5` 双支参数化；要证的是 bank 陈述 `bank_QZECFICwt2A`
  （`PackingAuto21`）。同族兄弟 `wt0corner` 已闭（`83144d4d`，`NliBanks18`）。
- **依赖（已全部落库）**：`NliBanks19`（`431fb92a`，288 行，把 bank 归约到
  显式三维核「`deltaX ≥ 0 ⇒ 0 < w2aF`」）；`NliBanks20`（`ebd11b13`，1,576 行，
  机器层 + 通用 `w2a_cell` + 代表 cell00 范式 `cell00_core`/
  `bank_wt2A_of_cell00`，探针 10/10 标准三）。
- **候选已完成**：52 个剩余实 cell + 8 个剩余 vac + 全 62-cell 覆盖/bank + Assembly 最小接线 patch；
  编排者独立重编六模块全 RC=0，67/67 公理审计恰标准三（含 `NliBanks27.bank_wt2A`）。
- **还缺（终验执行中，pq 续1346）**：完整 patch 已应用工作区、七文件逐字节匹配，六件已验
  olean 已复制进主池，未 commit。候选 Assembly 闭包 8,867 件，既有缺件 1,493；恢复已改为
  定向闭包单 worker，不再等待无关全池件。K030 已自然完成（6,310.68 s），定向链已接管，
  当前 K031。随后重编修改版 Assembly 并亲跑目标 `#print axioms`，通过才落库并记 −1。
- **启动做法**：① 生成器 ~300 行 python（模板 = cell00 的 214 行/cell 结构，
  数据 = 快照 `cells_raw.json` 53 实 cell；书写规范遵守 PR-43 的 linarith
  原子化）；② 按 y6 层拆 6 文件量产 52 cell；③ Assembly 接线：逐 cell 按
  `bank_wt2A_of_cell00` 范式组装 → 消费 `bank_QZECFICwt2A_of_core`；
  ④ 验收 = 亲跑 `#print axioms nliCell3QZECFICwt2A` 恰标准三。
- **预算**：生成 1–2 车道日 + 编译 9–26 min（编译并发 ≤3 放宽后 ~5–10 min）+
  装配半天；生成码 ~11,130 行（cell3-wt2a-core-w2 成本外推，pq §1）。
- **止损**：单 cell 编译 >60 s 或 cell margin <1e-4 时复查 `cells_raw.json`。
- **判词指针**：§1.15 / §1.19 / DEBTS 行 4 / FARM_PLAN §4 N2。

**ZTG 解耦 4（`nliRestZTGIJCF4_1_1_0_0` / `_0_1_1_0` / `_0_1_0_1` / `_0_0_1_1`）—— 真缺件 = 每债 9 片 hstep（状态：32 角 + conditional 归约落库 `3e12214e`；凹性-only 车道 2026-11-21 收线 **UNRESOLVED**——f'' 的 sound 6 变元证书超树内引擎，Bernstein 原子包络新线索待接；盒级 hG/Assembly 未闭；pq §8 续1342/1360/1362）**

- **这是什么**：`Assembly.lean:1738/1777/1783/1795`；HOL `ineq.hl:486-499`
  `make_F4` 循环的四个实例（模板 `bank_ZTGIJCF4tmpl`，id 1821661595），
  盒宽 0.46–0.52。陈述 = 「γ4 主支为正 ∨ rad2 > 2」；rad2 支已逐条证假
  （`1b401275` 的 `_rad2_refuted`），唯一活路是 γ4 主支。
- **依赖（已落库）**：dihY 半边 `decbc61c`（四箱 `ztg_dihY_* : 1.008/0.875 ≤
  dihY`，6,191 行 143 声明全标准三）+ Kit A `f47d472f`；`ztg_of_main` /
  `_rad2_refuted` / `_main_forced` 归约（`1b401275`）；peel 表示范式
  `BernsteinLeaf0011`（`9a4a9dc6`，q=36/25 的 81 系数叶 14.9 s 标准三）；
  witness 数据（快照 bernstein-representative-w1：q=64/25 三债各 1,215
  系数 / q=36/25 一债剪枝后 81 系数）。q 是 Bernstein 基的阶参数。
- **试点（已完成，2026-11-19）**：`ztg-bernstein-pilot-w1` 三件全绿落库
  `57eded64`（972 系数 Dgrad + 1,215 系数根叶 + 剪枝胶水，12 探针标准三，
  千系数件 = 分钟级定标）。**角色勘误（18:41 接线车道实测钉死）**：ztgG
  盒义务只证 **dihY 半边**，该半边树内**早已闭合**（`decbc61c`
  `ztg_dihY_1_1_0_0 : 1.008 ≤ dihY` / `ztg_dihY_0_0_1_1 : 0.875 ≤ dihY`，
  32 角点证书路线）——**`57eded64` 是同一盒事实的第二条独立内核证明，
  对债面零增量**（试点价值 = 表示定标 + 剪枝必走债的唯一胶水模板）。
- **已完成（`3e12214e`，编排者亲验）**：32 个有效 γ4 角 + 128 个去重二面角元组，
  通用 slice 归约，以及每债 `hstep ⇒ hG ⇒ bank` 的 conditional 消费链；
  Dih/Corners/SliceKit/Residual 审计分别 132/288/5/20 全标准三。
  原 residual margin 双 PASS：a5+b5·1.008 = 0.011093 < 0.05/3、
  a5+b5·0.875 = 0.017022 < 0.065/3。
- **还缺（真正缺件 = 每债 9 片 hstep）**：盒级 hG 与无条件 bank 仍未闭合，
  当前每债 0/9；没有 Assembly hunk。**凹性-only 车道实测（2026-11-21
  `ztg-g4-concave-closure-w1`）**：36/36 cell 采样 f'' 严格负（最坏 −0.2565）、
  216 片顶点 216/216 > target（min 0.0655350/0.0862670），但 **sound 证书失败**——
  自然区间 Δ `[−746.578, 1784.788]`（真值 ~[253.6,526.3]），均匀剖分
  6,400/22,500 盒最坏 f'' 上界仍 +342.1/+55.8；CertTM 一阶 hull 64 盒
  `ok=0/64`、`minLo=−1.73e12`。**阻塞点纯是 f'' 的 6 变元 sound 符号证书**，
  不是数学；需要二阶/带曲率 TM 规则、相关和结构分解、或 CAD-lite（旧禁向）。
- **新线索（编排者零 Lean 预侦察，2026-11-21，未落库）**：把多项式原子
  （Δ/Δ4/u126/u135/∂Δ）换成**精确 Bernstein 包络**（每变量 degree ≤2 ⇒
  3⁶=729 系数，精确有理）后，同一 cell 的 Δ 从 `[−746,1784]` 收紧到
  **`[227.30, 583.16]`（与真值采样逐位一致）**；f'' 上界从 **+2.45e6 降到
  +44.9**；再 2× 均匀剖分（256 盒）→ **+8.94**。仍 >0，但主因是 Δ 的区间
  依赖、不是数学；下一可行方向 = **有理 Bernstein 证书**（清正分母后对
  分子做 Bernstein，保留交叉项）+ 有界剖分，而非二阶 TM 农场。
- **计划勘误**：`lmfun(2.4635/2) = 113/1040`，不是 `113/10400`；
  精确 margin 自检拦截初版后已修正。hstep 新施工成本未估，不沿用旧 4–7 车道日总包。
- **止损 / 翻车点**：γ4 角点表片证书包络精度（同 joint-6 R1 三级 fallback）；
  **「根叶 = 每债主交付」已证伪——任何 Bernstein 侧后续量产先对照本卡
  角色勘误**；胶水机制仅对根张量含负系数的债保留为剪枝必走模板。
- **判词指针**：§1.10 / §5（含 ERRATA）/ DEBTS 行 5–8 / FARM_PLAN §4 N3。

**`nliTskIYOUOBFsharpv2` —— 四轴单调 + 2 维三块（状态：**BLOCKED-forensics 可翻案**，2026-11-20 `iyou-build-w1` 收口 −0 如实；L23 家族三重机器证据判死当前路线）**
- **波侧兑现并已落库**：32 件 kernel 验证模块（6 D 树 + L1 全系 + IysBase/Close + `IyouSharpV2` 接口件 `bank_TSKAJXYIYOUOBFsharpv2_of_slots` 标准三）纯新增入仓；IysClose 六 identity 修复（两段式 simp + ring_nf，仅证零陈述）。
- **L23 三重死因（全实测）**：① 20:15 版叶数据被 kernel 判假（N00 @64MB 栈：8/12 叶 false——**replica 逐位复现 ≠ kernel 语义一致**，宽盒 regime 暗区，PR-52）；② cap-47 修版发射器 TWOP 填充维无限分裂汇（永不终止，墙钟心跳揭出）；③ ~27% 肥盒含病态子域（55-triple 核 depth 70+ 仍占主，≤51 门救不了收敛）。
- **翻案条件**：发射器 replica 修复（43<false≤55 暗区定界）或新谓词/新表示出现 ⇒ 接第二笔（接线 hunk `patch_assembly_iyou_v2.diff` 与 15 件翻案工具已留档快照）；翻案前 iyou 保持 50 债之一，K_SORRIED 不变。

- **这是什么**：`Assembly.lean:946`；HOL `ineq.hl:242`「TSKAJXY-IYOUOBF
  sharp v2」。盒 `[2hplus,√8] × [2,2.001]² × [2,2hminus] × [2,2.001]²`；
  结论 `0 < gamma4fgcy y lmfun` 型（bank `TSKAJXYIYOUOBFsharpv2`）。
- **路线（审计已测余量）**：**四轴单调降维**（四个坐标方向偏导下界
  +0.13110，把 6 维压到 2 维）+ **2 维三块**——边缘一条线性下桥（余量
  1.358e-5，全债最紧点）、带状区 `∂/∂y4 ≥ +0.15`（y4∈[2,2.05]）、上方区域
  30–80 张 2 维小证书（余量 1.76e-3）。sharp corner + 2 维非单调，单点规则
  不够，必须混合（§1.2）。
- **依赖**：余量已测（§1.6）；模板 `Gamma4Feed`/`Gamma4VolY` 在库；一阶偏导
  闭式 `Gamma4Deriv1-8`（`c05928f5c`）；2 维小证书走 Rule P（有界 opt-in
  已生效，无需新解冻）。
- **还缺**：新 NliBanks 同型文件 + Assembly 1 import + 1 body（施工中）。
- **预算**：3–5 车道日；产出 ~2.5–4.7k 行（pq §1 在飞表口径）。
- **止损**：2 轮结构卡死交班；edge 线性桥余量太紧时先复查区间算术舍入方向，
  不硬凑。
- **判词指针**：§1.2 / §1.6 / DEBTS 行 2 / FARM_PLAN §4 N1。

### 9.2 可启动但依赖未齐 / 等前置

**FHBa（`nliRestFHBVYXZa`）—— η 曲线 + 地板凹性 + g3pos（状态：可启动，两车道；两处都成才 −1）**

- **这是什么**：`Assembly.lean:1569`；HOL `ineq.hl:914`（「FHBVYXZ a」），
  盒宽 0.46–0.83。陈述 = 「γ4 主支为正 ∨ η 守卫」，η 守卫是 `eta_y` 平方
  的下界支。主支在盒内为负（角点 dip −5.5589e-3，VERIFIED-iv），所以必须
  走「守卫支 + 主支」的联合结构；η 守卫集在 d 空间不可分、`max(g,c−η²)`
  非凹 ⇒ **不能套 96 角点表**（§1.11）。
- **路线三段**：① η 边界曲线（二次曲线 + 显式根式，代数核心已证）；
  ② 地板比较 m3/m4/m5——三条「槽纤维凹且地板值 ≤ 顶端值 ⇒ 原不等式」的
  比较引理（审计代号 m3/m4/m5，FhbEtaCurve 的 `fhb_hba_of_floor3` 消费它们）；
  ③ g3pos 内部——γ4 沿一条一维缝合曲线 ≥ 7e-3（内部区域、7 个边界片、
  尾部单调；右端点已真证）。
- **依赖已落库**：`FhbEtaCurve`（`8848b526`，405 行，η 二次边界曲线 + 三个
  归约接口）；`FhbFloorMono`（`032857d0`，166 行，凹性+端点 ⇒ m3/m4/m5 的
  归约三件套）；`Gamma4DerivSecond` + `Gamma4ConcaveBridge`（`b9134d34`，
  atan-free 二阶偏导闭式 + 「二阶导非正 ⇒ 凹」桥）；`FhbG3posCurve` +
  `FhbG3posEndpoint`（`20ee1cd5`，缝合曲线 + 右端点真证
  `7e-3 ≤ gamma4fgcy (2*hplus) (fhbY2Star (2*hplus)) 2 2 2 2 lmfun`）。
- **还缺**：m3/m4/m5 的 H1 纤维凹性证书（三轴一阶单调已有高精度数值反例，
  §1.14——唯一活路 = 对角二阶 atan-free 闭式 + 凹桥）+ H2 五维端点比较 +
  g3pos 内部（N3D、7 边界片、1 维尾部单调；尾部只有数值 GO：F′ 估计
  ≤ −0.2488）。
- **预算**：H1 车道 2–4 天；g3pos 3–5 天。
- **止损**：任一槽纤维凹性被精确反例打破 ⇒ 该纤维转分段凹（不许改陈述）；
  g3pos 内部 3 轮结构卡死交班。
- **判词指针**：§1.6 / §1.11 / §1.13 / §1.14 / §1.20 / DEBTS 行 41
  （注：DEBTS 该行的「农场口径、无解析路线」已被 §1.11 之后的路线取代，
  见 9.4 的 audit 卡口径注）。

**FHBv2a（`nliRestFHBVYXZv2a`）—— FHBa 的孪生债（状态：等前置；FHBa 真闭合后再启）**

- **这是什么**：`Assembly.lean:1575`；HOL `ineq.hl:888`。与 FHBa 同骨架
  （同一 γ4 + η 守卫结构），但接缝更紧：sharp 余量 **+1.104e-3**（§1.11
  勘误；audit 旧记 +2.124e-3 是非最优驻点，勿再引用）。
- **路线**：FHBa 的曲线/凹性证书直接复用（η 曲线 + 地板归约同模板，只换
  常数）；农场兜底 = 两支改写 + bb_arb（见 9.4 audit 卡）。
- **还缺**：FHBa 真闭合；v2a 自己的端点/接缝重算。
- **预算**：FHBa 收线后 2–3 天。
- **止损**：余量 1.104e-3 若被区间舍入吃掉 ⇒ 先重测再续，不硬凑。
- **判词指针**：§1.6 / §1.11 / DEBTS 行 42。

**`nliCell3QZECFICwt1` —— cell3 二号（状态：`cell3-wt1-closure-w1` 已收线 BLOCKED at Gate 1，pq §8 续1371；固定 16 盒仅 5 盒双向聚合严格负，独立槽相关性损失待解；目标未闭，SORRIED −0）**

- **固定 16 盒外证闸已收线（pq §8 续1371）**：16/16 均完成主证和第二实现重放，480/480 对象、pending=0，主/重放各 1,617,824 个完整张量商系数检查；只有 5/16 盒双向聚合上端严格为负。其余 11 盒是独立槽区间合成精确失败，首盒正误差主要来自相关 D4 项，**不是 `w1F2≤0` 点反例**。因此未进入 P1 内核化、三边、Targets 或 Assembly，无 Lean patch。后续需要保留相关性的 D4/槽证书或新的有限路线，不得删掉失败盒/D4 或用采样顶替。编排者复核在快照 `ORCHESTRATOR_CHECK/AUDIT.md`。
- **P1 原子紧界证书闸已收线（pq §8 续1361）**：配对 Bernstein 保留商相关性，
  9 个 D-slot 硬原子及代表盒全部 24 原子 + 6 个 matan 自变量均获精确有理界；
  编排者独立重放全网格系数后，代表盒 `p0_i0j1k1` 聚合严格为负、pending=0。
  最小 Lean pilot 三定理落库 `3faf2e39`，亲验标准三；但它只消费显式槽界假设，
  未内核化完整原子区间。**这只是一盒外证 + 最小 pilot，不是全 P1 GO**；其余 15 盒、
  matanD/DD 工具、三边与 Assembly 未做，SORRIED −0。旧 √2 括号上端也小于真值的
  健全性错误已排除；kink 重复 SE1 经机器恒等式确认不是笔误。
- **这是什么**：`Assembly.lean:425`；HOL `ineq.hl:1425`「QZECFIC wt1」。
  盒 `[√2,√2]³ × [2hminus,2hplus] × [2,2hminus]²`，`h0cut y4` 单折点参数化；
  要证 `bank_QZECFICwt1`（`PackingAuto21.lean:230`）。兄弟件 wt2A 的机器层
  （`NliBanks19`/`NliBanks20`）已落库，**复用面 90%+**（侦察差异清单见下）。
- **侦察收线（`cell3-wt1-scout-w1`，2026-11-19，快照有全量数字/脚本）**：
  - 数值极小 **+4.5143350968e-5**，位置 **(2.52, 2, 2)——h0cut 折点本身**
    （60 dps，全盒与核域 D 同点收敛；[interval] 认证：**全域 D 正性已由
    iv B&B 全证**（两折点片，92.6k evals/180 s，零未决叶，不依赖采样）；
    面 1D ≥ 4.51287021067e-5；3D 全局下界 ≥ +2.17e-6）。
    census 的 +4.514e-5 数值对、**位置错**（其「内点 y4≈2.534」是抛光停在
    折点右平台；2.534 处真值 2.064e-4）。
  - **y5/y6 全盒严格单调增在 60 dps 下成立**：min ∂w1aF/∂y5 =
    **+0.0030472209238** @ (2·hminus, 2·hminus, 2)（61³ 格 ≈ 22.7 万点 +
    坐标抛光 + 步长 1e-9…1e-25 十三位一致）。census 的 +3.05e-3 复现。
    **与 wt2A 命运不同的结构性原因**：wt1 的 m5/m6 槽系数 =
    1·lfun(y5/2) ∈ [0.1087, 1] 永不过零，而 wt2A 的 m5 = h0cut(y5)·lfun(y5/2)
    在 y5>2.52 整段为零、lfun 过 2.52 变号。标定：本求值器复现 wt2A 已知
    反例 −8.4182757987e-5（12 位），口径与 §1.15 的 BackendM 一致。
  - 折点平滑恒等式精确成立：lfun(1.26) = 0（Fraction），δ(2.52,2,2) =
    8184078/390625 精确有理 ⇒ 折点值是**单点有理证书**（不是内点包围电池）。
  - D4 组合系数 `K2·lfun(y4/2)·h0cut(y4) − 0.008 ≤ 0.06472·0.10865 − 0.008
    = −0.000968 < 0` 全盒一致非正（Fraction 认证；**nb20 勘误**：其 0.06468
    是 K2 的**下**界方向，wt1 需补一条 `K2 < 0.06472` 上界括号小件）。
- **路线（已定型，两条，共享服务件）**：
  - **A「折点 + 单调面」（推荐首发，footprint ~800–1500 行）**：
    ① `NliBanks21` 显式核 + 对偶 + `bank_QZECFICwt1_of_core` 归约
    （nb19 同型，无 /2 步；`nb19_g3_unfold`/`nb19_dih4_pin` 槽系数无关直接复用）；
    ② D 上 ∂w1aF/∂y5, ∂w1aF/∂y6 ≥ 0 两引理（余量 +3.05e-3，比核义务肥
    68 倍——粗 cell 化的导数证书或 atan-free 一阶闭式分片定号均可；
    `Gamma4Deriv1-8`（`c05928f5c`）为先例）；③ 底面两段 1D 单调
    （5000 点采样斜率：左支 d/dy4 ∈ [−0.01923, −0.01187] 恒负、
    右支 ∈ [+0.00275, +0.01189] 恒正；1D 证书便宜）；
    ④ **折点单点有理证书** `4.50e-5 < w1aF (2.52) 2 2`（y4 = 63/25 全有理，
    δ = 8184078/390625、δ4 全有理；`FhbG3posEndpoint`（`20ee1cd5`）生成范式，
    ~200–400 行；真值 4.51434e-5、iv 认证 ≥ 4.51287e-5 ⇒ 目标 4.50e-5 的
    有理括号余量 1.4e-6，对端到端有理夹逼绰绰有余）；
    ⑤ 装配消费 `of_core` ⇒ `#print axioms nliCell3QZECFICwt1` 恰标准三。
  - **B「无导数 cell」兜底（wt2A 62-cell layered3 同款）**：`nb21_wt1_cell`
    （`w2a_cell` 同型），**SE 槽必须用 `nb20_matan_ge_taylor` 的 1−u/3 下界
    而非 `matan ≤ 1`**（后者每盒损 ~2.5e-4 > 4.5e-5 余量，判死）；D4 槽 DU 角
    单边（系数 ≤ −0.000968）；D5/D6 槽 K2_lo·lfun 单边。cell 数按区间 B&B
    叶统计：近折点硬管叶 ~1.2k @ w=1.2e-4（iv 损失口径），Lean per-cell 更锐后
    估 **~10²–10³ cells**——**比 wt2A 的 62 cell 多**（wt1 余量 4.5e-5 比
    wt2A 的 3.0e-3 小 68 倍，cell 数必然更多），但 vacuous 剪除面大
    （wt1 的 D 几乎全盒，eta 守卫壳只在远角薄层）。
    **此口径下路线 B 性价比弱于路线 A**（A 不需要 3D cell）。
- **与 wt2A 的差异清单（施工前必读）**：槽系数 (h0cut y4, 1, 1) vs
  (h0cut y4, h0cut y5, 1)；无 /2；y4 盒上端 2·hplus（不是 √8）；单折点
  （y4=2.52）；极小在折点端点（非底边内点）；K2 上界方向新小件一条。
  其余（h0cut 系/lfun 恒等式/对偶引理/常数括号/Taylor 机）全部直接复用。
- **预算**：路线 A 施工 3–5 车道日（核+对偶+归约 ~1 天；单调面 2 引理
  ~1–2 天，最大不确定项；折点证书 ~0.5–1 天）；路线 B 视 cell 数
  +1–2 天。编译单文件预估 <5 min/文件。
- **止损**：① 路线 A 的 ∂/∂y5、∂/∂y6 引理若 3 轮结构性卡死（这是 A 的
  唯一真风险——现证据为 [sampled]，非形式），转路线 B，不许硬凑；
  ② 折点单点证书的区间算术吃掉 1.4e-6 余量 ⇒ 加括号位数，不许改陈述；
  ③ 任何一步触发「假桩/上游 BLOCKED」按 AGENTS §2 报告，不绕行。
- **施工收线（`cell3-wt1-build-w1`，2026-11-19 车道日 1，判词 BLOCKED-on-cost）**：
  - **数学为真**：D 上 `∂w1aF/∂y5 ≥ 0` 已由区间 B&B **完备证明**
    （2902 证明叶 + 5 vacuous + **0 未决叶**）；侦察 min +3.0472209e-3 复现一致。
  - **堵点纯在 Lean 化成本**：证书实测需 **2902 cell**（卡的「粗 cell /
    atan-free 闭式」估计不成立——corner-mono 派生原子任何尺度过不了
    单调认证；centered 兜底后斜率 1.0/w）⇒ ≈2,900 个 cell 实例 ≈
    **10⁵ 行**，超预算两个数量级。三段卡点史（naive → centered →
    corner-mono 各一轮结构性卡死）后按止损条款收线呈裁。
  - **路线 B 同损失模型实测更差**（余量小 68 倍 ⇒ 叶数 ~68³ 倍）——
    卡的 cell 兜底不成立。
  - **已落库资产 `NliBanks21`**（`e8d58205`，397 行，16 声明全标准三）：
    核显式化 + **三槽向量 Δ 对称恒等**（`nb21_dlt_eq/perm`）+ **Δ 三向
    非增代数恒等**（`(x5−x5')·(16−(x4−4)(x6−4)−2(x5+x5'))` 型——
    单调 walk 全程留 D、eta/δ=0 曲面零特殊处理）+
    `bank_QZECFICwt1_of_core` 完整归约。
  - **数字修正**：折点证书装配下界 **4.509910066e-5**（margin
    +1.0457e-7，Fraction 精确）——6 位 nb18/nb20 常数括号吃光余量，
    **必须 8 位级 π = 4(atan½+atan⅓) + sol0 链**（字面量已生成于快照
    `work/kink_lean_pieces.txt`，Lean 化估 400–600 行未施工）；
    **K2 勘误：路线 A 不需要新 `K2 < 0.06472` 件**（nb20 的 0.06476
    已够任何消费点；卡的 ⑤ 是路线 B 件）。
  - **Assembly 接线**：`Assembly.lean:431` sorry 原样未动（诚实收线）；
    接线点已备好（`bank_QZECFICwt1_of_core` + import + 1 行 body），
    只等 hcore 证书。
  - **呈裁三选项**：(a) 机器生成 cell 电池（585-shard 式政策件，~29
    shard / ~9 万行 / 串行编译 8–15 h，**需明批**）；(b) **二阶塔**——
    实测 ∂²F/∂y5² ∈ [−0.068, −0.036] 恒负、∂²F/∂y4∂y5 切片余量
    +0.0056，M5 可折叠为「3D 凹性 + 2D 切片 + 1D 边曲线 + 1 角点」，
    先修二阶因式化原子表（1–2 车道日）有望把叶数压到 **10¹–10²**；
    (c) 挂起等更优证书。快照 `cell3-wt1-build-w1/`（DELIVERY/Evidence +
    work/ 17 脚本 + 6 份 B&B 日志）。
  - **选项 (b) 裁决（2026-11-19 `cell3-wt1-tower-scout-w1` 收线 GO，用户批
    「Wt1 b 侦察启动」）——二阶塔路线 A′ 成立，工单级规格在 SCOUT.md**：
    ① **原子表（成败关键）过线**：干净 level-2 形（无 1/Δ 奇异、无
    matan‴）18 原子，FD 交叉验证 ≤1.5e-5；6 个 `_A` 原子全是**平方**
    （符号由形式定）；6 槽符号确定全盒 corner-mono，D4 权重消费已落库
    `nb20_k2_upper`（≤ −0.00097 < 0）；P1 收口 `∂²F/∂y5² ≤ −0.0071 < 0`
    （4× 余量）；8-角 ℚ(√2) 顶点证书演示 [exact] 全 PASS。
    ② **塔定案（A′）**：全盒凹性 ×2 + 对称引理 ⇒ `F ≥ min{E00,E01,
    E10,E11}` 4 棱——无 Δ=0 曲面件、无 KEY LEMMA A 依赖、全矩形域；
    全局最小 = 折点值 `F(2.52,2,2) = 4.5143e-5`（④ 字面量 kink_
    lean_pieces.txt **直接复用**）。**证书总数 ≈ 50–60 件（10¹–10² 达标，
    对比路线 A 的 2,902 叶）**；上车道「导数角 +3.0462e-3 与 ④ 混称」
    勘误（A′ 不需要导数角证书）。
    ③ **Lean 件预算**：直接消费 of_core / concaveOn 桥 / nb20 K1/K2 /
    g4s_quad_deriv / ④ 字面量；新件 = 对称引理 ~150–220 行 +
    matan 三阶括号 kit ~540–1,050（最重，log 支 HasDerivAt）+
    y5-切片导数链 ~500–850 + P1 证书层（生成器 ≈13–19k 行 / 手写
    ≈5.5–7k）+ 棱/点证书 ~1.4–2.7k + 接线 ~200–400 ⇒ **手写合计
    ≈4–5.5k 行 + P1 生成块**。风险主项：mono 义务目前 [sampled]，
    level-3 符号证明是最大未量化劳动（退路 = 子盒顶点证书，预算 ×2–3
    仍达标）。快照 `~/c17_backup/lane_snapshots/cell3-wt1-tower-scout-w1/`
    （SCOUT.md + work/ 16 脚本 + atoms2.pkl）。
- **判词指针**：快照 `cell3-wt1-scout-w1/`（SCOUT.md 全量数字+方法标注 /
  work/ 可复现脚本 11 件）/ 施工快照 `cell3-wt1-build-w1/` / 旧口径 §1.9
  （含 ERRATA）/ §1.15（wt2A 对照）/ DEBTS 行 3 / FARM_PLAN §4 N2。
- **还缺**：wt1 核显式化（未动笔）+ 单调性重测 + cell 方案定型。
- **预算**：侦察 0.5–1 天 + 施工 5–8 车道日（FARM_PLAN §4 N2 口径）。
- **止损**：+4.514e-5 的余量 3 轮内收不进区间算术 ⇒ 转农场兜底并记档
  （FARM_PLAN §4 N2 同款止损）。
- **判词指针**：§1.9（含 ERRATA）/ §1.15 / DEBTS 行 3 / FARM_PLAN §4 N2。

**`nliOx3q1h` —— S2a→S2b→S5（状态：`ox3q1h-s2ba-vertex-w1` **PAUSED／暂不采用**；`chainidx2-y4-sign-cert-w1` 已收线 BLOCKED（pq §8 续1389）；`chainidx2-hol-path-w1` 已收线 NO-GO（pq §8 续1391）；`ox3q1h-c2-joint-taylor-w1` 已收线 UNRESOLVED（parser 运行时阻塞，pq §8 续1395）；旧 S2a 代表仍 BLOCKED，共享 kit `2b521ae0`；**P0 重发已闭**（2026-11-20 `ox3q1h-p0-split-w1`）：39,792→**3,524 点** −91.1% 缺口闭合率 100%、5,516 非顶点 (行,格点) 对 margin 全正 [exact Fraction] 全局 min **+1.32e-3**、19 split 合取全可行（min +1.41e-5）、184/184 角点电池从 [sampled] 升 [exact] 复证；S2a 槽件 **1,159 件逐件枚举就绪**（13 mono 槽全有回退档）、S2b 批产表就绪（现式 2.36M 行 / G4CORNER 压缩式 0.39–0.88M 行）；SCOUT 勘误 4 条入档（mono 13/19 非 12/19 等，详见快照 DELIVERY §ERRATA）；**S2a/y4 精确符号证书待闭；S2b 当前量产方案暂不采用**）**

- **S2a 代表定标收线（pq §8 续1380）**：`chain_idx2` 的整盒二阶导符号证书未闭，S2a 0/1,159。原始 N/D 900 s 超时、共享原子上界 +181050.6515、保留商式 N·D 上界 +6.68e98，均不能作证且不是命题反例。第二代表件、P0 安装、mono、def 重发、S2b/S5 未做。已落库 `2b521ae0`：`Ox3q1hS2aConsumerKit`（开区间二阶导/移位凹性桥）与 `Ox3q1hS2aDomainKit`（宽盒/`deltaY>0`/update 域），编排者独立重编与 import 审计 **7/7 标准三**。后续必须先闭一件 `chain_idx2` 的精确符号包络。
- **S2b-a 当前量产方案暂停且不采用（pq §8 续1384）**：代表批通过后展开的逐点高精度有理数证书在源码、编译内存、时间和 olean 上都过重；用户明确暂停并不采用现有 patch。完成量、成本和审计口径只以 pq 与快照 `ox3q1h-s2ba-vertex-w1/PAUSED.md` 为准；未由编排者独立重编、未落库、未减债。重启须先换更小的共享证书表示，不直接续跑剩余批次。
- **chain_idx2/y4 当前证书路线已收线 BLOCKED（pq §8 续1389）**：双实现公式校验通过，但 root、split2 与预注册最终深度 split16 的精确上界都为正；最终 21 项独立重放齐全、pending=0，仍不能形成负性证书。编排者亲跑 final_audit 并核验全部交付 SHA；没有 Lean 新证或顶层减债。正上界不是命题反例，禁止原样续跑或突破 cell 上限。`chainidx2-hol-path-w1` 已收线 NO-GO：原版证明整个 `c2_mfuna>0`，二阶导只用于联合 Taylor 误差，并不存在可直接转移的 y4 凹性 cell/结构；不得把原外层盒或 Taylor 总量当成下一证书工程（pq §8 续1391）。
- **HOL 直接正性 pilot 收线 UNRESOLVED（pq §8 续1395）**：低pass代表outer 58 经两轮parser兼容修正仍无法构建，HOL rerun=0、真实inner path/pp未恢复，因而没有真实叶、联合Taylor外证或Lean候选。它不是数学NO-GO；但最低真实outer已有84叶，当前整cell≤64叶上限排除所有outer，六个Lean外包薄壳也未决。若续作须另批从fat1已验兼容层开始，不做第三轮盲改，不突破cell/叶/rerun上限。
- **这是什么**：`Assembly.lean:1904`；陈述本体 `ox3q1hP25`
  （`PackingAuto25.lean:94`，2026-11-06 DEF-FIX 显式化为 **230 条非线性不等式
  合取** = `ineqdata3q1h.hl` 46 record × 5 支）。这是 quarter case 的证书
  不等式库；**纯证书债**（无语句级缺口）。
- **结构**：230 = 46 条线性合取（全部可 `linarith`，最小余量 1.416e-7）+
  184 条 γ4 合取（最小余量 3.0205e-4）；按 **48 个 y-盒**联合处理——
  **不能**拆成独立的 `γ4≥G` 与 `dihY≥D`（γ4 在 18/48 盒为负、dihY 在 25/48
  盒为假，§1.4）。
- **依赖已落库**：S1 `Ox3q1hLin46`（`930d0dd1`）；S2 骨架 `6fc8db4b` /
  `bc6265b4` / `ce9174b4`；S3 链 184（`062c1799`/`df42274f`/`e18cd427`/
  `6730ea89`）；S4 gates 230（`2779a9da`，10,627 行）；S4.5 splits
  （`8d6b04a8`）；S2a 试点（`cec2264f` / `b3df5dc8`）；S2b Batch1（`8326ca5e`，
  42,882 行/1,672 定理）；SF 111 盒前提（`b11c1627`，14 文件 +1,101/−596，
  387 处）。清单见 `handoff-2026-11-18.md` §3.1。
- **还缺**：① S2a margin″ 装配（48 盒 × 6 槽 ≈ 288 槽的 `|f″| ≤ K` 双侧
  包络，试点已完 1 盒 y4）；② S2b 其余批（48 盒剩余角点 bank：~976 去重点
  ≈ 61 个 16-角点文件 ≈ 67 万行生成，或届时重估 Bernstein 化）；③ S5 接线
  （230 分量 `⟨…⟩` 逐位 + Assembly 替换）。
- **预算**：S2a 剩余 20–80 lean-h（EST）；S2b 生成零 lean、编译 ~2–3 h；
  S5 接线 ~240 行；合计 1–2 周墙钟；**0 农场**。
- **止损**：单轮 >15 min 编译失败触发「sorry 探针策略」（先出类型全绿版
  再分批装回）；两条 3 轮卡死即按 §7 交班。
- **判词指针**：§1.4 / handoff-2026-11-18 §3.2 / DEBTS 行 15 /
  FARM_PLAN §4 N4。

**TerminalV11 的 3 条纯数学支 —— 可启动但不减 SORRIED（合取债的一部分）**

- **这是什么**：`nliMainNonlinearTerminalV11`（全债卡见 9.4）109 支合取中
  的三条 MATH 支（§1.9 census 路由 3 条）：两条 num1 顶点极小
  （**+52.512319 / +11.734635**）+ 一条 645 slab deltaY（**−0.46104538**），
  全部精确有理。
- **路线**：「multiaffine + 单变量凹 ⇒ 64 顶点枚举」即完整证明；1 天级。
- **价值**：合取债去 3 支（**不单独减 SORRIED**）；完整闭合仍需 85 农场支 +
  补粘 + 21 支进锥。
- **判词指针**：§1.9 / DEBTS 行 45 / FARM_PLAN §2.2。

### 9.3 等解冻 / 等裁决

**LP 三债共享一张叶表（状态：等解冻 ④ LP 证书层 + ⑤ 磁盘/算力）**

- **共享背景**：LP（线性规划）证书层背后是 **43,078 条终端记录**
  （root 19,237 + easy 4,403 + hard 19,438），其中 **189 条 infeasible 已闭**
  （`LPLeafInfeas00` 零 sorry + 189 个 Farkas 模块），实际待证 =
  **42,889 条 bound 叶**。每叶 = 一张 LP 对偶证书（对偶向量 + 弱对偶检查 +
  `by decide`），机制已在用，不要重新发明 checker（pq §0.1）。单叶定标：
  生成 + 编译/内核 794.8 CPU·h/120 叶（lp-pilot-w1）；批量 20 叶安全上限
  19.3 GB；**磁盘是硬墙**：olean 0.70–0.95 TB（中心 0.83）。**packed b2
  格式已验证**（§6.3）：单叶 olean 395,784 B（≈49×）、wall 1.06×、六输出
  逐字节一致 ⇒ 若车队化，全量磁盘有望从 0.83 TB 降到 ~17 GB 量级
  （**外推 EST**；pq §1 明言不按单叶倍数外推、不车队化）。
- **`nliLpIneqs`**（`Assembly.lean:1944`）：`LpIneqs = AllCertified
  idsLpIneqs`，127 条 LP 域不等式（HOL `the_main_statement.hl:29-45` 清单）。
  域覆盖已真证（`lpIneqs_domain_covered`：`False` 回落不可达，无 else-True
  退化）。闭合 = 42,889 bound 叶表 + 总装配。锥外孪生 `nliLpIneqsIds`
  （127/127）是**真债**（§1.1），别当 VACUOUS 除名。判词：§6 / §6.3 /
  DEBTS 行 48。
- **hLP `lpArchiveCertificatesDebt`**（`Assembly.lean:7114`）：陈述 = 「给定
  `LpIneqs` 与 `lp_main_estimate` 两个前提，对每张 archive 图证反例不存在
  （`¬Contravening V`）」。逻辑桥已就位（前提消费形），**不产生额外农场
  成本**——它消费的就是上面同一张 42,889 叶表 + `lp_main_estimate`（后者是
  TerminalV11 消费链的出口，`LocalAuto16.lean:505`）。所以 hLP 是 LP 链最后
  一环：`nliLpIneqs` 闭 + main estimate 在位后只剩逐叶装配。判词：§6 /
  DEBTS 行 46 / FARM_PLAN F4。
- **`nliKcblrqcIneqDef`**（`Assembly.lean:2003`）：`KcblrqcIneqDef`
  （HOL `tame_lemmas-compiled.hl:34-46`，28 条折算）的**四条合取**：
  ① `azimDart` 上下界（按面基数分档：三边面 0.852 < azim < 1.893、多边面
  azim > 1.15）——按 Lean 陈述（`TameLp.lean:516`）这是**唯一不带
  `lp_main_estimate` 前提的合取项**，可走纯数值矛盾先单独收；②③④ 都带
  `lp_main_estimate` 前提 ⇒ 等 LP 表。**口径注**：DEBTS 行 47 把无 LP 件记作
  「#2」，与 Lean 合取序不一致（待核），但「有一件无 LP 依赖、可先收」两边
  一致。注意：只收 ① **不减 SORRIED**（合取债），价值是去风险。锥外
  `nliKcblrqcIneqDefIds`（28/28）同样是真债（§1.1）。判词：§1.1 / §1.7
  （LP-GATED 2）/ DEBTS 行 47。
- **预算（三债同批 = FARM_PLAN F4）**：42,889 叶，中心 **845 CPU·h**
  （区间 795–900，lp-pilot 定标）；磁盘 0.83–0.95 TB 硬墙（或 packed 后
  ~17 GB 量级，EST）；2 lean × 10 叶批 ≈ 7.8 天本地长跑或农场窗口。
  **止损**：磁盘无第二卷且已用 >0.95 TB ⇒ 停；单批 >20 叶（19.3 GB）⇒ 强制
  拆批；`LPLeaf` olean 单叶 >25 MB ⇒ 停。

**`nliCell3QZECFICwt0` —— 手工路线已定型（状态：可启动，待用户批产；2026-11-19 精确重测收线，③解冻仍兼容）**

- **这是什么**：`Assembly.lean:406`；HOL `ineq.hl:1372`。盒
  `[1,1]³ × [2.01,2hminus] × [2,2hminus]²`（前三维钉死），结论
  `bank_QZECFICwt0`（裸正性 `0 < pc3`，核 = `NliBanks18.pc3`，NB18:414）。
- **旧判词勘正（2026-11-19 `cell3-wt0-scout-w1`）**：11-17 判「三轴导数
  变号 ⇒ 角点模板不可用 + log 项 ⇒ 规则堵」两项均需修正：
  ① **数值面**：全局极小 **+1.7827835116391709e-4 恰在有理角点
  (2.01,2,2)**（census +1.783e-4 数值/位置双复现）；三轴变号属实但
  **全部结构化在远端三面墙**（∂/∂y4<0 ⊂ {y4≥2.3501}×{y5,y6≤2.3708} 等，
  循环对称），墙内 min ≥ **2.753486e-3 = 极小的 15.4 倍**；角点邻域
  [2.01,2.30]³ 三轴全单调（余量 +2.82e-3，槽导数分解 K1|SE|−K2|DH|
  的 10× 抵消 = nb18 同款括号游戏）。「角点模板」复活为
  「**单调核 + 有理角点证书 + 单墙**」。
  ② **规则面**：log 支只在 δ<0 帽（**0.02% 体积**、帽 min +0.0164 =
  92 倍余量），matan 负实参 |t| ≤ 4.5e-2 ≪ 1，Taylor 面
  `1−t/3 ≤ matan t` **在 log 支同样成立**；负底（sqrt/log 底非正）盒上
  **从不出现**（δ4/a/ups/lfun 恒正）。手工 log 规则 kit ≈ 100–200 行
  （atanh 正项级数），不是拦路虎。
- **银行义务已 iv 认证**：全盒 `0 < pc3` 由区间 B&B 直接证明
  （θ=0，**38,011 proven / 0 pending，306 s**；快照
  `cell3-wt0-scout-w1/work/bb_wt0.py`）——债为真不依赖采样。
  纯路线 a（三轴单调直搬）定量判死：反例点 ∂/∂y4 = −9.429e-3 @
  (2hminus,2,2) 在案；纯路线 b（裸 iv cell 农场）38,011 叶不可手写，
  仅作③农场口径叶数下界。
- **推荐路线 R（五件套，可启动）**：R1 核 [2.01,2.30]³ 三轴单调
  （nb18 §6–§8 同型括号链，800–1,200 行）；R2 角点 (201/100,2,2)
  有理证书（槽值全 Q(√2)/Q 已符号重构验证，4 个 atan 支 matan 点括号，
  300–500 行）；R3 单墙盒 [2.30,2hminus]×[2,2hminus]²（y5/y6 墙由
  已落库 `nb18_cycle` 免费转移；两方案：嵌套单调子盒 600–1,500 行 /
  wt2A 式 cell 表 ~60–150 cell × ~120 行）；R4 log 支 kit 100–200 行；
  R5 装配 ~150 行。**总 footprint ~2,000（乐观）– ~21,000（悲观）行，
  单车道 1–3 周**。施工次序 **R4→R2→R1→R3→R5**；R2+R4 一周内可出
  首个真件闸。
- **预算**：R1 2–4 天、R2 2–4 天、R3-方案i 3–5 天 / 方案ii 生成器
  2–3 天 + 量产 1–2 天、R4+R5 1–2 天。**止损**：R1 括号链 3 轮结构性
  卡死 → 降核 [2.01,2.25]³（余量 +5.66e-3）把薄层划给墙；R3-方案i
  子盒数超 ~10 → 转方案 ii cell 表。
- **与③解冻的关系**：不冲突、可先行。本重测顺带产出 EMIT-EXT 的
  **精确验收规格**：只需 matan 负支 log 规则（t ∈ [−0.046, 0)，atanh
  ≤24 项级数余项 ≤1e-15），**无需负底规则**；分支面单张
  （δ=0 ⟺ eta²=2），跨面盒双支 hull 即 sound。③若解冻，R3 的 cell
  表可改机器发射（叶数档 1–2 万，比 IXPOTPA 便宜两个量级），但
  R1/R2 两路线下都要手写。
- **判词指针**：§1.3 / §1.9 补测行勘正（wt0 条）/ DEBTS 行 49 /
  FARM_PLAN §2.1 / 快照 `~/c17_backup/lane_snapshots/cell3-wt0-scout-w1/`
  （SCOUT.md 全数字 + wt0_card.md + work/ 14 件可复现脚本，60 dps
  求值器 19 项标定阀门全 PASS）。

**`nliCell3QZECFICwt0sqrt8`（sqrt8）—— 已闭合落库 `8c7dfc34`（2026-11-20；10-cell 首选路线施工演进为 26-cell perSlot+prodMin 终态 = `w2a_cell` 严格孪生（S0 回退链末端），精确有理 margin 最小 +2.6398e-4；编排者亲编 RC=0/error 0 + 11 定理 `#print axioms` 全恰标准三 + `#check s8_bank : bank_QZECFICwt0sqrt8`；Assembly `1a-3/7` 槽接线；K_SORRIED 51→50，根面 589 不变池后补验）**

- **这是什么**：`Assembly.lean:419`；HOL `ineq.hl:1406`。盒
  `[1,1]³ × [2hplus,√8] × [2,2hminus]²`；第二析取支
  `eta_y y4 y5 y6 ^ 2 > 2`。角点余量 **+3.745e-3**。
- **ERRATA（2026-11-19 双侦察独立同源：`cell3-sqrt8-sa-math-w1` +
  `cell3-sqrt8-reeval-w1`）**：本卡原「判死」依据
  （a-矩形损失 0.0293 = 8×余量 ⇒ 需 125–512 cell，math5-w4 route_map §9）
  **公式失准**——根因已精确定位：§9.1「纠错后 a-公式」**term4 转录错**
  （第六槽抄成字面量 2；正确 term4 = √x3·x1/2，不存在 `(…+2−y6²)` 项；
  角点 y5=y6=2 时两形式同值，故角点自检漏检）。以已落库已证的
  `NliBanks20` 规范形（`ea4X/ea5X/ea6X` + `sol_euler4/5/6_eq`）为准：
  诚实全盒超额 **0.00552–0.00586 ≈ 1.5–1.6×余量**（S·a 侦察 1.5× /
  重估侦察 1.57×，独立复算同源）；朴素均匀链 −0.0182 的主要损失在
  dih/lfun 侧（lfun 系数三重损失 ≈0.016），不在 a-侧。「必须 125–512
  cell」「matan 括弧全不可达」两条均不成立；**生成器范式实测 38–67 cell
  即可收线**（区间 B&B @ τ=2e-4：38 自适应叶 / 67 wt2A 同款 y6-分层
  矩形设计 / 236 朴素网格）。math5-w4 §12 的四条 eta⟺δ 对偶基石**仍全部
  有效**、已在库。注意：朴素**逐项矩形链本身仍判死**（同格 (3,10,10)
  下 product-of-mins −0.000739 ✗），死因改写为「不共享折点、不按单调
  组合」。
- **已认证的硬事实（重估侦察 [interval]，比 cell 数更硬）**：
  ① **D = {δT ≥ 0} 上全域 `0 < c3Main` 已认证**（iv B&B 6,311 叶零未决、
  22 s；真极小 = 角点 **+3.7446884e-3**，与已证 `nb11_c3_corner_pos`
  8 位对齐）；② **route-A 三坐标偏导全盒为正**（min +5.00e-3 / +5.91e-3
  / +5.91e-3，B&B 117/125/126 叶）——旧 probe 的 ∂/∂y5 负点
  (2.6508, **2.6**, 2) 在盒外，「导数证不可用」的输入失效；但导数是
  抵消敏感和（±0.02 分量净 +0.006），~370 导数符号 cell 贵于值 cell
  电池 ⇒ route-A 降为回退不作首选；③ sharper matan 界（S1 37 / S2 34）
  只省 ≤10%，不值新增引理——杠杆是 vacuous/自适应分级。
- **最优解（可启动）**：**antitone-角点组合 + 10-cell 共享 y4 电池**
  （`w2a_cell` 孪生范式）：三条 box 级反单调引理（δ 三向 / lfun·D5·D6 /
  Σ1/a）按**角点组合**保留相关性——同格从 −0.000739 转 **+0.000940**；
  10 cell 全部 **y4 零分割**（折点仅 y5/y6 的 6 层二进有理分割），
  y5↔y6 对称后 **8 cell**；60 dps 证书最小余量 **+4.7758e-4**、
  有理化后 **+4.7757e-4**（有理化总代价 1e-8）；逐 cell 28³ 精扫
  soundness 0 违反。关键代数巧合：y4h=√8 时 δ(hi) = −2(8−B−C)² ≤ 0
  恒成立 ⇒ dih 括弧只需 `matan ≥ 1`（负支），完全不需要 1−t/3 形。
- **引理清单（SCOUT §4，全部装配件已落库或属已验证范式）**：
  L1 δ 反单调 ×3（仿 `dlt_anti_a` NliBanks20:509 因式分解）；L2 a_i
  逐坐标单调 ×12（机械）；L3 t5 反单调（L1+分母单调）；L4 matan 库
  （`≤1` 已落库 `nb20_matan_le_one`；`≥1` 负支 ~15 行；单调已落库
  NliBanks13 `matanDeriv`；**新增** 2-项 Taylor 上括弧 ~40 行——最紧
  cell T ≤ 0.0166，括弧只吃 6e-9）；L5 `lfun·D5` 反单调 ~30 行；
  L6 cell 主引理（`w2a_cell` 孪生，margin norm_num）；L7 `cell_vacuous`
  范式直接复用（NliBanks20:1294）；L8 y5↔y6 对称 ~20 行（cell 10→8）。
  装配：`nb11_c3_unfold`（已落库）+ `nb18_s8_eta_dlt_neg`（已落库、
  private 转 public 或复证 ~30 行——**已知小缺口**）+ by_cases 分派；
  接线 `Assembly:419`。
- **预算（双侦察施工资格表）**：**首选 S·a 10-cell**（8–10 cell、新引理
  L1–L5/L8 ~300–400 行、总 ~700–1000 行、编译 <5 min、**~1–1.5 车道日**）；
  **保守备胎 S0-67**（wt2A 同款 y6-分层矩形设计、δ-anti 链 + of_core 头 +
  s8_cell ~500 行机器层、~10–14k 生成 + ~900 机器层、编译 11–34 min 串行、
  **~1.5–3 车道日**；sqrt8 核是 `w2a_cell` 严格子集：无 /2、无 d4/DU/
  m4/m5/h0cut）。**无需**：certtm、③解冻、125–512 cell。
- **回退链（双侦察并单后；2026-11-19 施工实测改选）**：~~matanJoint-10
  （+4.8e-4，主案）~~ **施工证伪（cell3-sqrt8-build-w1 构造期抓到）**：
  matan 全域**递减**（matan(0)=1 > matan(1)=π/4）⇒ 左支 v₅ 反单调时
  matan 因子**递增**、L5「三反单调之积」**不 per-factor 成立**（数值真性
  依赖 S/D 跨侧抵消，Lean 不可机械）；perSlot-24 的 antiHi D-界同依赖 L5
  ⇒ **实际采用链条末端 S0（perSlot+prodMin）= `w2a_cell` 严格孪生**，每因子
  方向独立成立、零新数学、零陈述改动 → sumAnti-12（需 sum-antitone
  难件）→ route-A ~370 导数符号 cell。**施工实测（停泊态，等池恢复收尾）**：
  30 叶覆盖全盒（0 缺口）、对称后 26 实例**全编译 PASS**、精确有理 margin
  最小 **+2.6398e-4**（Fraction 逐 cell）、逐 cell 22³ soundness 0 违反、
  静态扫描全清；NliSqrt8.lean 4,058 行就绪，欠 round-8 复跑（池事故停泊）
  + 闸（预期：s8_bank 恰标准三、根面仍 589 逐条同集、K_SORRIED 51→50）。
- **③包处置**：sqrt8 **移出③解冻包**（双侦察一致：其解冻唯一动机
  「不可写」已灭；即便解冻，certtm 的工程+信任面成本也高于 10-cell 纯
  Lean 电池）。③包剩余内容 = wt0 log 规则 + IXPOTPA mixed-tm 两债。
- **判词指针**：§1.2 / §1.9 / DEBTS 行 50 / FARM_PLAN §2.2 /
  `~/c17_backup/lane_snapshots/cell3-sqrt8-sa-math-w1/SCOUT.md` +
  `~/c17_backup/lane_snapshots/cell3-sqrt8-reeval-w1/SCOUT.md`
  （含 `sqrt8_card.md` 合入本卡、`work/` 可复现脚本与 B&B 日志）。

**`nliRestIXPOTPA` —— 单调角点归约被证前闸精确否决（状态：NUMERICAL_ONLY；原定理未反证；旧施工 GO 撤回，pq §8 续1351）**

- **决定性反例**：A=(247/100,239/100,2,√8,2,2)、B=(247/100,12/5,2,√8,2,2)
  均在真盒与 F3∩F4，eta 失效由 Fraction 精确比较确认，且不在折点。两种表达式区间实现
  均给 margin(A)>0、margin(B)>0，且 margin(A)−margin(B)>0；故 γ23 随 y2 增大严格下降。
  两点 γ23 支本身成立，所以被否决的只是单调归约，**不是 bank_IXPOTPA 的反例**。
- **编排者独立验收**：快照 replay PASS；核对 Lean `gamma23Full8X/gamma3X/dihY` 后，
  另以原生高精度 atan 第三求值复得 A−B=0.0000452772840089955173272708520945889…>0。
  完整外证仍为 **0% / pending=1（全盒）**，未启动 Lean pilot，无公理输出、无 patch、SORRIED −0。
- **这是什么**：`Assembly.lean:1408`；HOL `ineq.hl:1265`。**全债最宽盒**
  （DEBTS 实测 w=2.372）：`[2hminus,2hplus] × [2,2hminus]² × [√8,4hminus] ×
  [2,2hminus]²`。poly 析取支网格最小 −519.9，真最小 +0.05–0.17（在另一支）。
- **ERRATA（2026-11-19 `ixpotpa-arch-w1`，PR-47 再中）**：「自相似无限阶梯」
  判词失准——非自相似、非尺度不变。真结构 = eta 支零面是**单调下集边界**；
  伪象 = 朴素 IA wrap 实测 **≈2340·w**（六次单项式依赖）对着边界处 margin→0
  永不可判 ⇒ 幻觉出 ~1e-6 宽细胞需求 ⇒ 3M+ 叶。与 BLOCKED.md 的 ±0.27–1.08
  wrap、15–21 栈全部定量对上。旧「区间不终止」观察本身仍真（朴素 IA 确实
  不终止），死因改写。
- **考古问答（AGENTS §8 纪律）**：HOL 原版**没有数学分解**——它走
  2h0=2.52 切 y1 消 h0cut ite → Xconvert 转 x 空间 → **61 片自适应分割**
  （33+28）→ Solovyev 形式化区间算术，重放合计 **163,524 s = 45.4 CPU·h**（azure 61 条
  Time 行求和；**ERRATA 2026-11-20 hol-cost-gap-census-w1 §9.6 + 编排者复跑**：旧记
  「163.36 s」系千秒误标秒，量级差 ~10³；61 片、单调塌缩同构等判读不受影响）。能终止的关键 = `allow_derivatives=true` 的**单调性维数
  塌缩**（bb_arb 没有的东西）——原版从不盲细分，先做单调变量端点代入；
  其分割树与我们独立推出的 eta 下集边界**完全同构**（考古与数学双向印证）。
  Isabelle 侧只有 tame 枚举部，非线性部不在仓内，无可考古对象。
- **仍成立的精确事实**：eta126² 三坐标偏导的代数因式与有理严格正下界成立，
  故 eta 逐坐标严格增、失效集为下集；共享角 `(63/25,2,2,√8,2,2)` 的 margin 严格为正。
  但共享角已不再具备全域最差角资格，不能推出 `F3∩F4` 上 γ23 恒正。
- **旧侦察 ERRATA**：192k/37,316/30,000 等采样均未给完整证书；γ23 单调方向集和
  两半共享最差角归约现已由 A/B 精确反例否决。旧 `battery_threshold.py:45-46` 在
  宽度/深度上限未经高角验证便强制归 F3，故 42+102=144 叶不构成零 pending 电池。
  全盒 `d3∨d4∨γ23`、F3∩F4 上 γ23 恒正、有限完整值证书和全部 Lean 工作均未决。
  后续只能另做非单调值证书或新的可证细分归约，不按旧 SCOUT F7/F8/L-G1..G5 量产。
- **③包处置**：旧「IXPOTPA 分解路线 GO ⇒ ③整体清空」判断撤回；③、农场和
  mixed-tm 均保持 hold，不因本次反例自动解冻或改开另一条量产路线。原 HOL 61 片
  形式化路线不受此辅助命题反例质疑。
- **止损**：停用旧 SCOUT §5 的施工 GO；任何重启先过新的完整外证零 pending +
  独立重放闸。朴素 dyadic 分割禁用（自爆栈教训），未自动续派新 agent。
- **判词指针**：pq §8 续1351 / 快照 `~/c17_backup/lane_snapshots/ixpotpa-cert-gate-w1/`
  （双区间实现、精确 eta 证据、反例与 replay）；历史侦察
  `~/c17_backup/lane_snapshots/ixpotpa-arch-w1/` 仅作考古与反例复核入口。

**`nliTskWKGUESBsym` —— 数学归约 GO + 成本重标定（状态：主路 F2b ~1,045 CPU·h 维持参考；旁路经 sym-face-math-w1 实测重标为 700–2,200 CPU·h 平价或更差，「15–25 CPU·h」判废；2026-11-20 `sym-face-math-w1` 收线）**：① **var_lt 数据债已修复**（4 case 修后生成器重发，AFTER==bank 逐位、BEFORE==bank 反向逐位 [exact]，F2b 发射前置清除）；② **四条单调归约全真且更干净**——全盒 min ∂γ4/∂y_k = +0.0926…+0.0946（40dps FD-of-RPN、argmin 在盒角、14/14 角 [exact]）、20/20 d2 混合偏导全正（原侦察 3 条负值系 float64 FD 伪象，PR-47 非对称点复推全转正）；S4 对称 ⇒ 一条 canonical 事实 + 3 个置换搬运；③ Route-1 atom-chain 平移 NO-GO（Fraction IA：4096 片仍 −1.86）；④ **AD NO-GO 机理翻案**（零 ite 闭式 regime：g₂ 闭式无 guard 发射，大片 45,297 叶双 CLOSED）但叶数对片内裕度超线性 ⇒ 全盒 60k–200k 叶 ≈ 700–2,200 CPU·h；⑤ 旁路复活前置 = P0-a（最小纯覆盖枚举压死/确认 60k–200k）+ P0-b（闭式叶率实测校准）两探针（≤1 车道时/个，**待用户批**），P0 过闸前不批 L0a 施工。**成本反差普查收线（2026-11-20 `hol-cost-gap-census-w1` §9.6，编排者亲复跑）**：HOL 形式化实耗 **256.8 CPU·h/234 叶** [exact] ⇒ 形式化对形式化反差 **~4.1×**——旧 ~280× 系 informal 13,337 s 锚（qed_log.txt:975，2010 OCaml 单发）混用，勘误；「贵得有理」（guard straddle 94–99%，HOL 也付大钱）。**三探针判词（2026-11-20 `p0-probe-batch-w1` 收线，编排者亲验）**：**旁路复活 = 否（NO-GO）**——P0-a 最小纯覆盖 **74 片 ≫30**（大片 A 1 + 补区域 73：54 b1 纯 + 19 不可角点纯化 STUCK；几何原因 = 翻转角点位于区域角上，剥离链每区 ~20 片，角点纯覆盖不存在）；P0-b 闭式 prescan 实测 **1.10–1.16 s/叶**（较 XLLIPLS 13.3 s/叶 **12× 便宜**）但 kernel 项 27–31 s/叶占主导 ⇒ 总叶率 **28–32 s/叶 [EST]**；全盒叶数 ≈**215,909 [EST]**（60k–200k 确认并顶到上沿）⇒ 旁路总成本 **1,680–1,920 CPU·h**，比主路 F2b 1,045 **更差 1.6–1.8×**。**裁决：L0a 不批、旁路归档「数学全真、载体成本平价或更差」、主路 F2b 维持参考；K1 的 WKGUESB 消费线随之关闭；ERRATA 2026-11-20 23:18：FHBa H1 入口亦关闭——`k1-d2-pruning-pilot-w1` 判 NO-GO（两盒定号俱败 + 一换五叶数账），见 §9.6。**

- **这是什么**：`Assembly.lean:981`；HOL `ineq.hl:281`「TSKAJXY-WKGUESB
  sym」。盒 `[2hplus,√8] × [2.01,2hminus] × [2,2hminus] × [2hplus,√8] ×
  [2,2hminus]²`，析取四排序支；网格主支最小 **+8.534e-3**（正，不紧；
  侦察定位 = 64 角点网格 min @ (√8, 2.01, 2, √8, 2, 2)）。
- **超时根因（[interval] 实测，卡上「未分段」假设证伪）**：**6.6% 墙钟
  near-miss**——正定向 case 跑满 200k 节点需 **1,279 s**，被 recost 的
  1,200 s 上限击杀（空日志 = SIGKILL 丢缓冲）；逐节点 165/s（同族
  210/196），慢因 = **ite guard straddle 率 94–99%**（y1,y4 长维把
  gamma4fgcy 的 60 条 ite 分支面推入跨 0 态；RIBCYXU 仅 30%）。HOL 原版
  自己也是 prep 预切 234 片消 hull 成本（239,884 cells/299–374 s），但
  bb_arb 隐式二分对分支面的发现成本与 HOL 同阶——**预切不会降低节点
  预算**，无需分段。
- **数据债（✅ 已修复 2026-11-20 `sym-face-math-w1`：4 case 用 `392517111` 修后生成器重发，形状级自检 AFTER==bank 逐位/BEFORE==bank 反向逐位 [exact]，成本口径逐字节无损——发射前置清除；历史判词原文如下）**：case json 的
  var_lt 是 **2026-10-26 `392517111` 修复前的反定向**，与 bank 陈述
  （`PackingAuto21.lean:321-322`/ineq.hl:286-287）**不同向**——发射出的
  证明粘不上 bank；**recost 30 case 里全部 4 个 var_lt case 同病**
  （WKGUESB/IYOUOBF/RIBCYXU/QITNPEAv2_4003532128），发射前一律用现行
  emit_rpn 重发 + 重窄化。幸运无 CEX 风险：主支全盒为正（HOL 无析取版
  同盒 QED 13,337 s 外部锚；flip-hard 区采样 min +5.09e-2）。
- **主路（立即可排，等农场/长跑裁决）**：重发正定向 case → bb_arb
  200k、**超时 ≥1,500 s** → 92,952 TM 叶 + ~7,039 裸区间叶 + 9 未闭叶
  （贴对角带，同族 13 叶同型）→ **≈1,045 CPU·h**（prescan 344 + kernel
  697 + plain 2）+ 磁盘 ~20–40 GB；验收照 FARM_PLAN §5.3。
- **旁路（半程实测，math 车道可选）**：四短维 ∂γ4/∂y_k ≥ +0.128
  [sampled]、短对二阶超模全正、prog 零引用 hminus ⇒ 全盒 min 收拢 2-D
  face；**Face 证书实测 bb_arb 2 s CLOSED、210 叶 ≈ 2.4 CPU·h**——但
  单独不闭合 bank（缺 Cert A 四条单调归约）；AD 直证试点 NO-GO（31 min
  无 CLOSE 已止损），二阶符号归约为 math 车道级工作（ZTG-joint6 kit
  形状，3 条边缘对 −0.013/−0.006/−0.0008 先符号核实）。若落地总
  ~15–25 CPU·h（**比主路便宜 ~50–70×**）；不落地主路独走无损失。
- **判词指针**：§1.3 / DEBTS 行 52 / FARM_PLAN §2.1 BLK / 快照
  `~/c17_backup/lane_snapshots/wkguesbsym-seg-scout-w1/`（SCOUT.md 15.2KB
  + work/ 29 项探针脚本/face 证书/cases_narrow；探针合计 ~70 min CPU）。

**ZTG joint 6（`nliRestZTGIJCF4_0_0_0_0` / `_0_0_0_1` / `_0_0_1_0` / `_0_1_0_0` / `_1_0_0_0` / `_1_0_0_1`）—— 路线 B 角点表全家族成立（状态：`0_0_0_0` 的 96 角 + L1 支撑件落库 `53c9a79a`、4 条二阶符号辅助落库 `4fad4b72`，七条全盒证书未闭；其余五债战役包待批产）**

- **L1 施工收线（pq §8 续1343，UNRESOLVED）**：七纯新增模块的导数/连续性/
  条件 ConcaveOn/96 角消费/of_nonpos 接口均已亲验，89/89 恰标准三；
  但七条 `ztgDMainSecond≤0` 全盒证书均未完成，Assembly 未接，SORRIED −0。
  下一步只能直接生成精确片内符号证书，必要时 R1 片切；采样凹性不是 Lean 证据。
- **二阶符号双片 pilot 已收线 UNRESOLVED（pq §8 续1345）**：`ztg-joint6-sign-pilot-w1`
  留下 `ZTGJoint0000SignPilot` 149 行、两个紧凑分子和 4 条恒等式/符号桥，编排者独立
  重编与公理审计均过，落库 `4fad4b72`。但 y1 左片、y2 全片的整段 `ztgDMainSecond≤0`
  主目标 **0/2**，不能消费对应 `of_nonpos`，无 Assembly、SORRIED −0。归一化 Bernstein
  仅 y4 方向统一，朴素有界中点两片均 0/64；核心单调性仍只有采样，未借 hold 中 CertTM
  填洞，也无精确反例。只判本 pilot 未决，不判整条数学路线 NO-GO；未自动扩七片或续派。
- **这是什么**：`Assembly.lean:1813/1807/1801/1789/1764/1758`；同
  `make_F4` 循环（ineq.hl:486-499，id 1821661595）的六个 joint 实例。
  rad2 支已被 `1b401275` 的 ×10 `rad2_refuted` 证假——六债全走
  `bank_ZTGIJCF4tmpl` 主支。**六债零覆盖**（dihY 半边 / γ4-main 联合 /
  条件闭合 / 接线全缺）；共享前置已全落库（`ztg_of_main` 归约、Kit A、
  一阶闭式 `c05928f5c`、二阶对角闭式+ConcaveOn 桥 `b9134d34`、V5 角点链、
  slice-min 母形、试点生成器 `57eded64`）。
- **侦察裁决（2026-11-19，快照 `ztg-joint6-scout-w1/`，管道三重校准
  全中——g4corner 12 位一致 / G_need 精确复现 / 根张量 min 与试点逐位）**：
  - **前提修正**：ztgG 多项式只证 dihY ≥ arctan s（dih 半边）；γ4 =
    volY−vol4f 超越、无 Bernstein 叶——「root/剪枝叶 = 每债主交付」
    **不成立**；认证 D 下逐债解耦 margin 全负（1_0_0_1 −0.0216 / trio
    −0.0247 / 0_1_0_0 −0.0556 / 0_0_0_0 −0.0195）⇒ **六债必须联合证书**。
  - **逐债路线 B（角点表压 main）全胜**：1_0_0_1 → 9 片全凹 / 18 角 /
    12 值；trio（`0_0_0_1`/`0_0_1_0`/`1_0_0_0` 三债同张量+2 置换）→
    **一张表 8 片全凹 / 36 角 / 36 值共享库**；0_1_0_0 → 4 混合单元
    **2.2 一刀后 8 子片全 mono-up** / 4 角 / 4 值；0_0_0_0（最薄
    +0.00078）→ 数值侦察 7 片候选凹（形式符号证书后续仍未闭）/ 现行 96 角。
  - **三个决定性实测**：① **角落塌缩零损失**（全盒字母表角点 min =
    稠密 min 逐位相等 ⇒ B 的结构风险为零）；② 判据通过（≥6/6 正联合
    余量 ∧ 凹性单元 raw 44/48 = 91.7%、2.2 切后 100%）；③ A′ 单元路线
    ≥10M 行被 B 支配 300×（留单片应急备胎）；F5 农场兜底比 B 贵
    10–30×。**剪枝问题答案：六债无一需要 Dgrad/剪枝**（safe-s 下四
    几何根张量直过）。
- **bank 接线清单（每债一件套，全消费已落库件）**：新模块
  `ztg_main_<bits>_pos` ＝ 逐片符号证书（树内一/二阶闭式 + 1-D Bernstein
  peel）+ slice-min 适配器（`NliBanks9` 母形）+ 角点值证书（V5 链 +
  **L0 唯一缺件 `ztg_atn2_le` 上界镜像**）→ `ztg_of_main` → Assembly
  6×(1 import + 1 body)。零新 def、零陈述改动、零解冻。
- **战役包（呈批形态）**：**W0 工具 kit（0.5–1 天）→ W1 trio 一张表
  （−3，摊销最大）→ W2 1_0_0_1（−4）→ W3 0_0_0_0 精度档（−5）→
  W4 0_1_0_0（−6）**。总计 ~18k–48k 行（中位 31k）、6–10 车道日
  （W2/W4 并行 ⇒ 墙钟 4–7 天）、机器编译全家族 ~0.5–2 h（每模块
  2–6 min、3 槽串行、≤~10 GB/模块）。**与 9.1 解耦 4 角点表共享全部
  L0/L1/L2 模板，两包并跑可一次性清零 ZTGIJCF4 全家族（−10，合计
  30k–70k 行）**。可选保险（不占关键路径）：四几何 dih 根叶 4 张
  ≈ 90k 行 / 23 min 机器，按需插队。风险主项 R1 = 片证书包络精度
  （三级 fallback：片再切 → 全凹化 → 单片 A′）；0_0_0_0 的 +0.00078
  对 1e-8 档链有 4 个量级余量但方向敏感，逐角点机器核查。
- **判词指针**：§5（含 ERRATA）/ DEBTS 行 9–14 / FARM_PLAN §4 N5 /
  快照 `~/c17_backup/lane_snapshots/ztg-joint6-scout-w1/`（SCOUT.md
  17.8KB + work/ 6 脚本 + out/ 数据）。

### 9.4 农场类（等 ① 农场批 + ② Rule P 规模化解冻；数据预算以 `FARM_PLAN.md` §5 / `DEBTS.tsv` 为准）

> **总口径**：本组全部走「bb_arb 发射 → 内核逐叶重放 → 装配」的农场管线，
> 需要用户解冻 ①（nli 农场证书批）+ ②（Rule P 规模化；不批 = 旧 Rule C
> 核时 ×12）。核时全部是 **recost TRUNC 下界外推（EST）**；**F1 是唯一实测
> 校准点**，F1 不批则以下数字全部保持 EST。
>
> **重估注（2026-11-19）**：peel 表示 GO（`9a4a9dc6`）后，「多项式可代数化」
> 子集的叶成本按新范式重估——多项式义务优先试 Bernstein 叶（零
> MvPolynomial/decide 路线），再回 bb_arb；heavy-√/atan 债（BIX 类
> c_sqrt=3112）维持农场口径（√ 整盒仿射误差为 slack 的 2,662 倍，§1.10
> NO-GO）。

**F1 便宜档 6 债（状态：等解冻 ①②；其中三条是已实测的「无 gate」便宜档）**

- **逐名**（陈述锚 + 网格主支最小 + recost 实测核时；DEBTS 行 16–21）：
  - `nliRestPEMKWU`（`Assembly.lean:1439`，ineq.hl:1169，盒 `[2hminus,2hplus]×
    [2,√8]×[2,2hminus]×[2,√8]×[2,2hminus]×[2,√8]`，5 析取支，网格主支
    −5.939e-3 由支承接）：**27.77 CPU·h**。小注：HOL 侧 id `PEMKWKU` 比
    Lean 名 `PEMKWU` 多一个 K（§1.7 考古勘误），跨 HOL 检索时两拼法都查。
  - `nliRestTEWNSCJ`（`:1446`，ineq.hl:1146，盒 `[2hminus,2hplus]×
    [2,2hminus]³×[2,√8]×[2,2hminus]²`，网格 +2.234e-2，实测最便宜农场
    case）：**27.77**。
  - `nliRestQITNPEAv24003532128`（`:1433`，ineq.hl:1193，盒同 TEWNSCJ，
    3 支 + 3 var_lt，网格 −0.1845 由支承接）：**33.82**。
  - `nliRestTXQTPVC`（`:1415`，ineq.hl:1241，盒 `[2hminus,2hplus]×
    [2,2hminus]²×[2,√8]×[2,2hminus]²`，六支析取，网格 −1.842e-3）：
    **79.93**。注：**「常数非负权重消析取」已被三点 Farkas 证人精确排除**
    （§1.21：`E_μ[f]` 最小分量 +0.001271705>0，任意常数 `aᵢ≥0` 有证人点使
    组合为正）——这条的捷径已死，农场口径维持；析取命题为真仍是 EST。
  - `nliRestQITNPEA5400790175b`（`:1453`，ineq.hl:1121，盒 `[2hminus,2hplus]×
    [2,2hminus]³×[2hminus,√8]×[2,2hminus]²`，heavy-sqrt c_sqrt=3112，
    网格 +8.971e-3）：**99.77**。
  - `nliRestBIXPCGW7274157868a`（`:1633`，ineq.hl:776，盒 `[2hminus,2hplus]×
    [2,2hminus]³×[2hplus,√8]×[2,2hminus]²`，网格 +1.563e-2）：**149**。
- **批预算**：6 债一次窗口，中心 **418 CPU·h**（区间 209–836；叶数各 ~10⁵
  TRUNC 下界；磁盘 ~120 GB；12 GB/lean 进程）。
- **启动做法**：FARM_PLAN §5.3 六步模板（emit → 叶分类 → 叶源 → 内核重放
  → 装配 → 验收四件套：编排者亲跑 axioms + error/`rg sorry` 双检 + SORRIED
  对账 + 根面不动）。
- **硬止损**：实测 s/叶 >60 s 或 olean >2 MB/叶 ⇒ **停批重估**（F1 是全计划
  校准点，此处失真则 F2 全部作废）；单债 >300 CPU·h 未闭 ⇒ 退回 BLOCKED。
- **判词指针**：§1.3 / §1.21 / FARM_PLAN §5.1 F1 行。

**QITNPEA 家族 10 + `nliRestBIXPCGW9455898160`（状态：等解冻 ①②，F2a 批）**

- **这是什么**：同一条 HOL idv 循环（`ineq.hl:845-862` 等）量产出的 11 张
  同模板债（`Assembly.lean:1602–1633` 区段），盒宽 0.464（宽盒 ⇒ 叶树 ~10⁵
  起）。共享同一 case JSON 生成器（recost 已量产 24 个 case，FARM_PLAN
  §3.1）。
- **逐名**（网格主支最小 + 核时；DEBTS 行 22–32）：
  `nliRestQITNPEA1_1_0`（`:1620`）+4.192e-3 / 1,122 CPU·h；
  `nliRestQITNPEA1_1_1`（`:1614`）+1.739e-2 / 1,122——**分母勘误**：其主支
  分母 = `1+bankGenMid 1+bankGenMid 2 = 3`（§1.23），「并盒 γ4≥23/2000」
  共享下界服务不了它（精确余量 −0.0056）；
  `nliRestQITNPEA1_1_2`（`:1608`）+3.585e-2（旧网格值；重算 m≈0.03497，
  §1.18）/ 1,128——**fat1，见下**；
  `nliRestQITNPEA1_2_0`（`:1602`）+1.906e-2 / 1,128；
  `nliRestQITNPEA2134082733`（`:1582`，盒 `[2hminus,2hplus]×[2,2hminus]³×
  [2hminus,√8]×[2,2hminus]²`）+4.898e-3 / 1,169；
  `nliRestQITNPEA3848804089`（`:1465`，盒 `[2hminus,2hplus]×[2,2hminus]⁵`）
  +2.881e-3 / 1,164；
  `nliRestQITNPEA5653753305`（`:1483`，盒同上）+2.981e-3 / 1,161——B0 联合
  包络的「Q565」（§1.11 纯有理支配覆盖）；
  `nliRestQITNPEA5814748276`（`:1471`，盒同上）+2.669e-3 / 1,165——B0 的
  「Q581」（同上）；
  `nliRestQITNPEA6206775865`（`:1477`，盒同上）+2.200e-3 / 1,169；
  `nliRestQITNPEA9939613598`（`:1627`，盒 `[2hminus,2hplus]×[2,2hminus]³×
  [2hplus,√8]×[2,2hminus]²`）+3.804e-3 / 1,169；
  `nliRestBIXPCGW9455898160`（`:1490`，盒 `[2hminus,2hplus]×[2,2hminus]⁵`，
  HOL 字面 `-- #0.00569` 双重负号笔误已由陈述核对钉死，Assembly rest 19/62
  注）+2.233e-3 / 1,122。
- **fat1 = `nliRestQITNPEA1_1_2` 的解析替代路线（暂缓中，资产已落库一半）**：
  主支 = **`γ4/2 > 0.0057`**（分母勘误后，§1.16/§1.18）。路线 = 局部代数化：
  6 个 slab + 2 个超越区，atan 用上界——已落库：交错 Taylor arctan 上界
  `NliQitnpea12ArctanSeries`（`248fde92`，G3 的 Hermite 锚已撤销，任意阶
  精确）+ √ 分段界 + G 正性。**当前状态：G 正性车道 2 h 超时暂缓**（§1.26，
  2,975 行 WIP 原样 RC=1/82 err，WIP 已抢救，不自动 resume；朴素 enclosure
  6001 叶后两半仍负，该具体路线不可行，§1.22）。若用户另批：从快照 fresh、
  先修发射器逐段验证，不重生成 ~3,000 行整件。另有**共享下界替代**：并盒
  `γ4 ≥ 23/2000` 若真证可服务 `1_0`/`1_2(fat1)`/`2_0` 三条（不覆盖 `1_1`；
  `2_1`/`2_2` 已证）——`qitnpea1-shared-floor-w1` 等用户裁决（§1.23）；
  两条路线不得重复建设相同胶水。
- **批预算**：11 债合计中心 **12,619 CPU·h**（区间 6.3k–25.2k；磁盘
  ~220 GB）。
- **止损**：单债 >2× 上界（2,200 CPU·h）未闭 ⇒ 停债留 WIP；家族 >30% 叶需
  Rule P 且单叶 >35 s ⇒ 停批改档（FARM_PLAN §5.4）。
- **判词指针**：§1.3 / §1.16 / §1.18 / §1.22 / §1.23 / §1.25 / §1.26 /
  FARM_PLAN §5.1 F2a 行。

**GLFVCVK4 家族 5（状态：等解冻 ①②，F2b 批）**

- **这是什么**：同一张 GLFVCVK4 bank 的 y4 三分裂 + 主 bank
  （`Assembly.lean:1669–1696` 区段）：
  主债 `nliRestGLFVCVK4`（`:1696`，ineq.hl:559，盒 `[2hminus,2hplus]×
  [2,√8]⁵`，**全债第二宽盒** w=0.828；网格主支 −3.457e-3 由析取支承接）
  1,128 CPU·h；
  `nliRestGLFVCVK4a8328676778`（`:1690`，ineq.hl:586，盒 `[2hminus,2hplus]×
  [2,2hminus]²×[2hminus,2hplus]×[2,2hminus]²`，w=0.464，+6.068e-3）
  1,130；
  y4 分裂三子 `nliRestGLFVCVK4y4crit`（`:1683`，ineq.hl:623，盒
  `[2hminus,2hplus]×[2hminus,2hplus]×[2,2hminus]×[2hminus,2hplus]×
  [2,2hminus]²`，+1.739e-2）1,128；
  `nliRestGLFVCVK4y4subcrit`（`:1669`，ineq.hl:675，盒 `[2hminus,2hplus]×
  [2hminus,√8]×[2,2hminus]⁴`，+4.213e-3）1,123；
  `nliRestGLFVCVK4y4supercrit`（`:1676`，ineq.hl:649，盒 `[2hminus,2hplus]×
  [2,2h0]×[2,2hminus]×[2hplus,√8]×[2,2hminus]²`，+4.965e-3）1,128。
- **共享**：同一 bank 的分裂产物 ⇒ case JSON 骨架同源；HOL 侧参考成本
  127.9 CPU·h/846 叶（§1.5）——说明引擎杠杆存在，但 Gate-0 已实测 NO-GO
  （`12c81dee`）⇒ 当前按 bb_arb 农场口径排。
- **批预算**：F2b 批 = 本家族 5 + `FHBVYXZb` + sym×2（下两卡）合计中心
  **8,118 CPU·h**（区间 4.1k–16.2k；磁盘 ~160 GB）。止损同 F2a。
- **判词指针**：§1.3 / §1.5 / DEBTS 行 34–38 / FARM_PLAN §5.1 F2b 行。

**`nliRestFHBVYXZb` —— heavy-sqrt（状态：等解冻 ①②，F2b 批）**

- **这是什么**：`Assembly.lean:1564`；HOL `ineq.hl:942`。heavy-sqrt 表达式
  （c_sqrt=3112，约 36k 运算），2 析取支；网格主支 +7.844e-3；
  **332 CPU·h**。
- **解析替代（数值 GO、非形式）**：B0 联合包络给出 FHBb 主支全盒估计最小
  +3.804e-3、析取冗余（§1.11）；但整盒凹性归约已被证伪（§1.12），母定理
  `b0-master-lean-w1` 搁置 ⇒ **当前按农场口径排**，包络证书将来真证才切换。
- **判词指针**：§1.3 / §1.11 / §1.12 / DEBTS 行 33。

**TSKAJXY sym 2 债（状态：等解冻 ①②，F2b 批）**

- `nliTskIYOUOBFsym`（`Assembly.lean:952`，ineq.hl:223）：盒
  `[2hplus,√8] × [2.001,2hminus] × [2,2hminus]⁴`，析取三排序支
  （`y2 < y3/y5/y6`）；宽盒 r≈0.46、无解析路线（DEBTS 行 39）；网格主支
  +1.313e-4；1,116 CPU·h。
- `nliTskRIBCYXUsym`（`:969`，ineq.hl:183）：盒 `[2.001,2hminus] ×
  [2,2hminus]⁵`，析取排序支（**口径差**：Assembly 注释记八支、DEBTS 行 40
  记 7 支——发射时以 Lean 陈述为准）；网格主支 +8.234e-5；1,033 CPU·h。
- **共享**：19,614 运算的同模板 sym 发射器；**XLLIPLS 的 Rule P + 装配管线
  直接复用**（6,612 叶全量先例，`58ade83a`/`c940aae7`/`e4c384e6`）。
- **判词指针**：§1.3 / §4（装配先例）/ DEBTS 行 39–40 / FARM_PLAN §3.1
  TSKAJXY sym 组。

**audit 引擎 4 债（状态：等解冻 ①②，F2c 批；FHBa/v2a 的解析路线另见 9.2）**

- **这是什么**：`rest-math-audit` 判定的四条「主支在盒内为负、必须先改写
  两支再引擎出叶」的债（§1.6）：
  - `nliRestQITNPEA5400790175a`（`Assembly.lean:1459`，ineq.hl:1103，盒同
    `5400790175b`）：主支 min **−7.2693e-3** 在双折点角；minimax 改写后
    +4.121e-3。
  - `nliRestRQWUDDU`（`:1839`，ineq.hl:1332）：主支 min **−0.1536**；
    minimax 改写后 **+2.155e-3**（**ERRATA**：triage 旧记 0.00474，2.2× 紧，
    §1.6）。dih/η 双支同时贴边（§1.2）；MATH 备选高风险。
    **三探针判词（2026-11-20 `p0-probe-batch-w1`，编排者亲验）**：
    ① **mono-prescan 塌缩 NO-GO**（10⁵→10² 不成立）——d1 定号真实（主支
    y1/y4 MONO+、两 η 支全 MONO+ [sampled+exact]），但逐支全局塌缩摧毁 η 支
    关叶（全局 inf 深负）；修正臂闭叶尺寸**更细不更粗**（mean 0.0553 vs
    0.0746），600 s full-run 两臂均不收（1.19M/1.50M 叶）；唯一收益 = 每节点
    ~1.2× 常数加速。**R1 归档「②b 不可手工弥补」，农场口径维持 1,100 CPU·h
    [EST]**。② **【重大发现】case 盒 y1 下界 bug**：真 hminus = 1.231754422…
    （`NliHminus.lean:24`）⇒ 真域 y1 ≥ 2.4635088；case
    `pipeline/interval/out/cases/RQWUDDU.json` y1 下界 = 2576980377/2^30 ≈ 2.4
    （prep 丢 hminus 耦合外扩）⇒ **目标在 y1∈[2.4, 2.4635) 上为假**（反例
    (2.4,2.0,2.72755,2.0,2.0,2.72754) 三支全 −0.0247，60 dps，编排者独立
    复算逐位复现）⇒ bb_arb 类引擎在此 case 永不收口（假口袋无限二分 = 历次
    full-run 不收直接原因）。**修复候选（pq §8 续1341 编排者勘误）= y1 下界
    2645162983/2^30 + Lean `hminus ≥ 1.23175`**：旧 `2645184458` 实为
    floor(2.46352·2³⁰)，高于真 2*hminus，拒绝；新分子是 floor(2.4635·2³⁰)，
    三条覆盖定理已由编排者亲验标准三。本机 ignored JSON 已修；2026-11-20 生成器根修
    `537ed78d`（hminus choice box clamp）。③ **同族 48 案复核**：根修前 9 FATAL_CEX +
    1 SOUND_DEAD_HMINUS + 38 UNRESOLVED；根修后 **1 FATAL + 1 DEAD + 46 UNRESOLVED**
    （余 1 件 RQWUDDU = [2.4635,2.4635088) spurious slice，真域外，不是真反例）；
    RQ 外其余 8 件已转 UNRESOLVED。④ 真域数值等振
    +1.9657e−3 [sampled] 与审计 +2.155e−3 同结构同量级，但不是全局 minimax 证明，
    也不推出修域后必收口。
  - `nliRestFHBVYXZa` / `nliRestFHBVYXZv2a`：解析路线已推进大半（9.2 两卡），
    本卡仅记其**农场兜底**口径。
- **路线**：每债先写 60–100 行「主支 ∨ `eta126² < 1.34²` 两支改写」引理，
  再引擎出叶。**注意**：audit 估的 80–800 叶是 CertTM2 投影，CertTM2 已随
  Gate-0 NO-GO（`12c81dee`）出局 ⇒ 现行 bb_arb 下回到 ~10⁵ 叶 ≈
  **1,100 CPU·h/债**（EST）。FHBa/v2a 的 η 接缝有内点极小、`max(g,c−η²)`
  非凹，**不能套 96 角点表**（§1.11 ERRATA——audit 旧 minimax 值也是非
  最优驻点，已勘误为 +4.813e−3/+1.104e−3）。
- **批预算**：4 债合计中心 **4,400 CPU·h**（区间 1.6k–8.8k；磁盘 ~80 GB）。
- **止损**：两支改写件 >300 行 ⇒ 停（audit 估 60–100）；bb_arb 叶数
  >5×10⁵ ⇒ 停（说明改写没起作用，FARM_PLAN §5.4）。
- **DEBTS 口径注**：DEBTS 行 41/42 对 FHBa/v2a 记「FARM-BB、no MATH/corner
  route、FROZEN」，这是 §1.6 audit 时点的口径；§1.11–§1.14（更晚）已给出
  η 曲线 + 地板凹性路线且相关资产全部落库（9.2 两卡按新口径）。两债以
  9.2 为准，本卡仅作农场兜底——**DEBTS 该两行待 farm-ops 复核时刷新**。
- **判词指针**：§1.2 / §1.6 / §1.11 / DEBTS 行 41–44 / FARM_PLAN §5.1
  F2c 行。

**`nliMainNonlinearTerminalV11` —— 109 支合取（状态：3 MATH + 补粘可启动；85 农场支等解冻 ①②）**

- **这是什么**：`Assembly.lean:1926`；陈述 `main_nonlinear_terminal_v11`
  （HOL `terminal.hl:24-44`），109 条 Main_estimate 支的**合取**。语句级
  展开已落库（LA1:1900–2158，T0）——剩的是证明与接线，不是语句缺口。
  锥外孪生 `nliMainNonlinearTerminalV11Ids` 是 **VACUOUS**（§1.1，
  100/109 查表命中 `True` 回落），已从接线主波剔除，**不是真债**。
- **闭合算术**（§1.9 census，109 支全判零 UNRESOLVED）：21 支在库（20 支
  T11Glue 已粘 + `8405387449` 在库 40,785 叶/498 分片**未粘**，只差接线）+
  **3 支纯数学**（9.2 卡：64 顶点枚举即完整证明，1 天级）+ **85 支农场**
  （5 case JSON 在库 + 35 hex 模板 + 40 直发 atan + 2 高维 prep + 3 多项式
  分割）。**合取债：缺一支不减 SORRIED。**
- **正确顺序**（FARM_PLAN §7-4）：3 MATH → 补粘 → 21 支进锥 → 85 支农场
  （F3 批，中心 **600 CPU·h**，区间 500–700；磁盘 50–150 GB）。不要先烧
  农场——预算烧完仍 0 收益。
- **家族压缩资产**（§1.24）：五个参数化模板覆盖 80 支、另 5 支须独立处理；
  置换等价只对 74 条显式 def 验证过、35 条 hex 未测；发射侧 70%/150–250
  machine-h 是**不预支的估计**——发射前先过代表样本定标。
- **硬止损**：5 个子族任一**发射不出** ⇒ 停（合取债缺一支 = 0 收益，不许把
  84/85 记成进展）；单支 >10 machine-h ⇒ 停。
- **判词指针**：§1.9 / §1.24 / DEBTS 行 45 / FARM_PLAN §5.1 F3 行。

### 9.5 覆盖对账表（50 `nli*` + hLP 逐名；与 DEBTS.tsv / 地图 SORRIED 段对齐）

| 债名 | 状态 | 卡位 | 判词主出处 |
|---|---|---|---|
| `nliCell3QZECFICwt0` | 可启动（手工路线 R 五件套，待批产；11-19 重测收线 GO） | 9.3 | §1.3 / §1.9 |
| `nliCell3QZECFICwt0sqrt8` | **已闭合 `8c7dfc34`（2026-11-20）**：26-cell antitone S0 终态，margin +2.6398e-4，11 定理标准三编排者亲测 | 9.3 | §1.2 / §1.9 |
| `nliCell3QZECFICwt1` | **P1 代表盒外证闭环 + 最小 Lean pilot `3faf2e39`（pq 续1361）**；全盒 hP1 其余 15 盒、E00/E01/E11 与 Assembly 未闭，SORRIED −0 | 9.2 | §1.9 / §1.15 |
| `nliCell3QZECFICwt2A` | **已闭合 `1ec06b28`（2026-11-20）**：六模块 `d733f61d` + 验收下沉 `Kepler.Targets.Wt2A`；小模块闭包 90、亲跑 `#print axioms` 恰标准三；根面复验未做；olean 恢复已停止并交接新负责人（pq 续1385） | 9.1 | §1.15 / §1.19 |
| `nliTskIYOUOBFsharpv2` | **BLOCKED-forensics（2026-11-20）**：三重机器证据（kernel 判 8/12 叶假 / TWOP 永不终止 / ~27% 病态子域）；波侧 32 件已落库；翻案 = replica 暗区定界或新谓词（hunk+工具留档） | 9.1 | §1.2 / §1.6 |
| `nliTskIYOUOBFsym` | 等解冻①②；**var_lt 数据债已修复**（sym-face-math-w1 11-20，4 case 逐字节重发对齐 bank，发射前置清除） | 9.4 | §1.3 |
| `nliTskRIBCYXUsym` | 等解冻①②；**var_lt 数据债已修复**（同上） | 9.4 | §1.3 |
| `nliTskWKGUESBsym` | 数学归约 GO；var_lt 已修复；**P0 三探针判词（11-20）：旁路 NO-GO**（74 片 ≫30 + 叶率只降 1.25–1.4× ⇒ 总 1,680–1,920 CPU·h 更差 1.6–1.8×）——主路 F2b 1,045 CPU·h 维持，L0a 不批；普查勘正：HOL formal 256.8 h/234 叶 ⇒ 4.1× | 9.3 | §1.3 / §9.3 / §9.6 |
| `nliRestBIXPCGW7274157868a` | 等解冻①②（F1） | 9.4 | §1.3 |
| `nliRestBIXPCGW9455898160` | 等解冻①②（F2a） | 9.4 | §1.3 |
| `nliRestFHBVYXZa` | 可启动（两车道） | 9.2 | §1.11–§1.14 |
| `nliRestFHBVYXZb` | 等解冻①②（F2b） | 9.4 | §1.3 / §1.11 |
| `nliRestFHBVYXZv2a` | 等前置（FHBa） | 9.2 | §1.6 / §1.11 |
| `nliRestGLFVCVK4` | 等解冻①②（F2b） | 9.4 | §1.3 / §1.5 |
| `nliRestGLFVCVK4a8328676778` | 等解冻①②（F2b） | 9.4 | §1.3 |
| `nliRestGLFVCVK4y4crit` | 等解冻①②（F2b） | 9.4 | §1.3 |
| `nliRestGLFVCVK4y4subcrit` | 等解冻①②（F2b） | 9.4 | §1.3 |
| `nliRestGLFVCVK4y4supercrit` | 等解冻①②（F2b） | 9.4 | §1.3 |
| `nliRestIXPOTPA` | **NUMERICAL_ONLY（pq 续1351）**：γ23-y2 单调角点归约有精确反例，原定理未反证；旧施工 GO 撤回，完整外证 0% / pending=1，未做 Lean | 9.3 | §1.3 / §8 |
| `nliRestPEMKWU` | 等解冻①②（F1） | 9.4 | §1.3 |
| `nliRestQITNPEA1_1_0` | 等解冻①②（F2a） | 9.4 | §1.3 / §1.23 |
| `nliRestQITNPEA1_1_1` | 等解冻①②（F2a） | 9.4 | §1.23 |
| `nliRestQITNPEA1_1_2` | **`fat1-terminal-export-w1` 三终端诊断已产出、待独立验收（pq 续1388）**：真实树与 248 终端精确 ifloat 复核 PASS；三例 dual 均 PASS，但 unchanged IA/RuleP/BaseC 均未接受。未做 Lean，其余 245 终端未测，不预支减债 | 9.4 | §1.18 / §1.22 / §1.25 / §1.26 / §9.6 |
| `nliRestQITNPEA1_2_0` | 等解冻①②（F2a） | 9.4 | §1.3 / §1.23 |
| `nliRestQITNPEA2134082733` | 等解冻①②（F2a） | 9.4 | §1.3 |
| `nliRestQITNPEA3848804089` | 等解冻①②（F2a） | 9.4 | §1.3 |
| `nliRestQITNPEA5400790175a` | 等解冻①②（F2c） | 9.4 | §1.6 |
| `nliRestQITNPEA5400790175b` | 等解冻①②（F1） | 9.4 | §1.3 |
| `nliRestQITNPEA5653753305` | 等解冻①②（F2a） | 9.4 | §1.3 / §1.11 |
| `nliRestQITNPEA5814748276` | 等解冻①②（F2a） | 9.4 | §1.3 / §1.11 |
| `nliRestQITNPEA6206775865` | 等解冻①②（F2a） | 9.4 | §1.3 |
| `nliRestQITNPEA9939613598` | 等解冻①②（F2a） | 9.4 | §1.3 |
| `nliRestQITNPEAv24003532128` | 等解冻①②（F1） | 9.4 | §1.3 |
| `nliRestRQWUDDU` | **生成器根修 `537ed78d`（2026-11-20）**：hminus choice box clamp 到 [1.23175,1.23176]；48 案 9→1 FATAL + 1 DEAD + 46 UNRESOLVED；剩余 1 件 RQWUDDU 是 [2.4635,2.4635088) spurious slice（真域外），不是真反例；清零需更紧形式 hminus 界或 case-box 排除引理；HOL result_tree 兼容探针仍未做；债未闭 | 9.4 | §1.2 / §1.6 / §9.4 |
| `nliRestTEWNSCJ` | 等解冻①②（F1） | 9.4 | §1.3 |
| `nliRestTXQTPVC` | 等解冻①②（F1） | 9.4 | §1.3 / §1.21 |
| `nliRestZTGIJCF4_0_0_0_0` | **96 角 + L1 支撑件落库 `53c9a79a`；二阶符号双片 pilot 已收线 UNRESOLVED，4 条辅助落库 `4fad4b72`（pq 续1345）；七条全盒证书与 Assembly 未闭** | 9.3 | §5 / DEBTS 行 9 |
| `nliRestZTGIJCF4_0_0_0_1` | 可启动（W1 trio 共享表，−3） | 9.3 | §5 / DEBTS 行 10 |
| `nliRestZTGIJCF4_0_0_1_0` | 可启动（W1 trio 共享表，−3） | 9.3 | §5 / DEBTS 行 11 |
| `nliRestZTGIJCF4_0_0_1_1` | hD 双证已闭；缺 hG=γ4≥0.065（角点表待批） | 9.1 | §1.10 / §5 |
| `nliRestZTGIJCF4_0_1_0_0` | 可启动（W4，2.2 一刀全 mono-up，−6） | 9.3 | §5 / DEBTS 行 12 |
| `nliRestZTGIJCF4_0_1_0_1` | 同族缺件（γ4 半边角点表，随 G4CORNER 摊销） | 9.1 | §1.10 / §5 |
| `nliRestZTGIJCF4_0_1_1_0` | 同族缺件（γ4 半边角点表，随 G4CORNER 摊销） | 9.1 | §1.10 / §5 |
| `nliRestZTGIJCF4_1_0_0_0` | 可启动（W1 trio 共享表，−3） | 9.3 | §5 / DEBTS 行 13 |
| `nliRestZTGIJCF4_1_0_0_1` | 可启动（W2，−4） | 9.3 | §5 / DEBTS 行 14 |
| `nliRestZTGIJCF4_1_1_0_0` | hD 双证已闭；缺 hG=γ4≥0.05（角点表待批） | 9.1 | §1.10 / §5 |
| `nliKcblrqcIneqDef` | 等解冻④（无 LP 合取项可先收） | 9.3 | §1.1 / §1.7 |
| `nliLpIneqs` | 等解冻④⑤ | 9.3 | §6 |
| `nliMainNonlinearTerminalV11` | 3 MATH + 补粘可启动；85 支等解冻①② | 9.2 / 9.4 | §1.9 / §1.24 |
| `nliOx3q1h` | **P0 已闭**；S2a 代表仍 BLOCKED，chain_idx2/y4 精确外证未闭；S2b-a 当前量产方案 **PAUSED／暂不采用**（pq 续1384），未落库、未减债 | 9.2 | §1.4 |
| hLP `lpArchiveCertificatesDebt` | 等解冻④⑤ | 9.3 | §6 |

> 维护：相关车道收线/落库后更新对应卡；新判词以 §1.x 为准，本节只同步状态行。

### 9.6 成本反差普查（`hol-cost-gap-census-w1`，2026-11-20 收线；编排者亲复跑逐数复现）

- **HOL 侧成本底账首次逐债落地 [exact]**：azure `results/output` 39,196 行 `Time` 日志
  双格式聚合（batch1-oxl 无索引格式坑已修补定标）= 原版 Azure 形式化
  **23,223 行 / 5,002.1 CPU·h / 中位 404.6 s/叶**；三档案锚（ox3q1h 757.3 h /
  ZTGIJCF4 76.0 h / GLFVCVK4 主 bank 127.9 h）逐位复现；**编排者重跑
  `hol_cost_v2.py` 全数核对**（WKGUESBsym 256.8 h/234 叶、RQWUDDU 0.4 h/2 条顶层
  Time 记录、IXPOTPA 45.4 h/61 叶）。全表 = 快照 `CENSUS.tsv`（49 nli + hLP + 3 参照 × 12 列）；
  urban 重跑树（9,274.9 h，慢 ~1.85×）不混入「当年」口径。
- **两锚点勘误**：① WKGUESBsym「~280×」= informal 13,337 s（qed_log.txt:975，
  2010 OCaml 单发）与形式化成本**混币**——formal vs formal **~4.1×**
  （1,045/256.8），「贵得有理」；② IXPOTPA「重放 163.36 s」实为
  **163,524 s = 45.4 CPU·h**（千秒误标秒，route c 判读不受影响）。
- **反差谱系**：我们**反超三条** = ox3q1h **0.03–0.11×**（「85×」是 naive-farm
  口径，结构化角点表落地后反转）、TEWNSCJ 0.76×、TerminalV11 0.19× [EST 押 F1
  校准]；5–10× 档（WKGUESBsym/TXQTPVC/FHBVYXZb/PEMKWU/GLFVCVK4）与 20–137×
  农场档（QITNPEA 群/BIXPCGW/FHBa farm 口径/sym 双债）由机制 **②a 叶数**
  （HOL 单调塌缩 + 导数剪枝；源码锚 informal_search.hl:266 / m_verifier.hl:798 /
  recurse.hl:189）解释；**单叶我们反快 HOL 13–15×**（Rule P 27–31 s vs 中位
  404.6 s）；③ elaboration 税只对 LP 数据字面量（66 s/叶）与生成码体量成立。
- **红旗（扣机制残差，全在 ②b 单叶证力）**：R1 RQWUDDU **~2,780×**（HOL 两顶层
  split、10,194 Taylor 终端叶 + 10,192 普通 glue、零 convex glue，945.4+479.2 s [exact]；
  旧「两终端叶」口径见 pq 续1341勘误）；R2 QITNPEA1 族 **248–1,271×**（HOL idv 模板债
  ≤31 条 prep Time/≤4.5 h [exact]；终端数须逐案恢复，fat1 urban=2,948）；R3 IYOUOBF/RIBCYXU sym 98–137×（发射器无 straddle
  感知切维——候选 = 纯发射器改动，可随 P0 批同测）；R4 mild = wt1 一阶 2,902 叶
  已被二阶塔 A′ 自愈（kit 数学第一次救场的已发生实例）。
- **kit 裁决**：**K1 引理族整合件条件 GO**——整合已落库资产（Gamma4Deriv1–8 /
  d2 对角闭式 + 凹桥 / FhbFloorMono / V5 角点链 / peel 模板），唯一新数学 =
  d2 混合偏导闭式族（~2–4 车道日含 pilot）；入口 = **FHBa H1 落地时顺手收口**
  （1–2 车道日，**不得让在飞 joint-6 改道**）。**ERRATA 2026-11-20 23:18（`k1-d2-pruning-pilot-w1` 收线，编排者独立复算 + 亲跑 probe）：条件 GO 撤销 → NO-GO**——两代表盒定号俱败（FHBa B0 13/15 对 mixed，内点 3⁶ 亦负；sym (1,4) 内点 562/729 负），且「一换五」证书账使叶数方向与 ≥10× 相反（字面叶数 UNRESOLVED）；HOL 原版无混合偏导剪枝（一阶单调 + 对角凸，已逐行核）。30 条 off-diagonal 闭式降为期权资产，FHBa H1 正路 = 对角二阶 + 凹桥。**K2 发射器 mono 塌缩通用 NO-GO**
  （Gate-0 `12c81dee` 立着；K2 ≠ CertTM2——只改搜索侧叶数、不动叶检查器）。
  **RQWUDDU mono-prescan 单点 GO：并入 sym P0-a/P0-b 探针批一次呈批**（1 车道日、
  零 Lean、纯 Python 叶数测量；若 10⁵→10² 塌缩不成立，R1 就地归档
  「②b 不可手工弥补，农场口径维持」）。**（2026-11-20 判词：三探针全 NO-GO——
  旁路关闭、R1 归档、K1 期权化，见 §9.3/§9.4 卡；RQWUDDU case 盒 y1 下界 bug
  为附带重大发现，正确候选下界 2645162983/2^30 已在本机 ignored 数据落地；
  2026-11-20 生成器根修 `537ed78d`：hminus choice box clamp 到 [1.23175,1.23176]，
  48 案审计 9→1 FATAL（余 1 件 RQWUDDU 为 [2.4635,2.4635088) spurious slice，
  真域外，不是真反例）；真实 result_tree 恢复仍未决，见 pq 续1357。）**
- **fat1 红旗解剖收线 UNRESOLVED（2026-11-21，pq §8 续1364）**：8 条 prep Time
  不是 8 终端叶；urban 同哈希运行 = 2,948 Taylor pass + 2,940 普通 glue，mono/convex
  等全 0。原 output 无内部 result_tree，故未做 Lean pilot。编排者 replay PASS；
  约 34× 叶数 ×37.47× 单叶全包成本仅是原时配 urban 叶数的混合估算，不是原逐叶实测。
  下一最小输入 = 从 `construct_certificate` 导出真实终端树，不自动重跑 HOL 或续派。
- **UNRESOLVED（宁缺毋编）**：HOL 侧 wt1/wt2A/IYOUOBFsharpv2 原版耗时（sharp-5
  无 Time 行；urban 重跑 0.68/0.14 h 仅参考）、LP 族（formal_lp 无计时档）、
  Isabelle 8 条 `by eval` 实测（只有 50,400 s 超时上限）、informal 枚举面逐类
  耗时；我们侧 F2 全系 TRUNC 下界 [EST]（F1 唯一校准点）、iyou-sharpv2 替代
  路线现值。
- **判词指针**：快照 `~/c17_backup/lane_snapshots/hol-cost-gap-census-w1/`
  （DELIVERY.md + CENSUS.tsv + 7 聚合脚本）；pq 续1331；strategy §12 ERRATA。
