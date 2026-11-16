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
- 当前剩余 = 52 条 `nli*` + hLP（见 pq 文件头；SORRIED 构成以 pq 为准）。

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
  （阻塞在 log/matan 规则层非负值）；**wt1/wt2A** Lean 盒 y5/y6 严格单调增 ⇒
  「单调归约 + y4 一维证书」**MATH 可行**（极小 +4.514e-5 / +3.011e-3，iv 包围）——
  cell3 工单族 **+2 候选**（`cell3-wt1-mono-w1` / `cell3-wt2a-mono-w1`）。
- **ERRATA（对 map52/recost/scout，§1.7 已注）**：① 104 NO-CASE→83；② 「5 γ4」→
  109 支无 γ4（实为 taum×4 + deltaY-disj×1）；③ 补粘合/先行步两条 STALE；
  ④ recost「引用型 36」→ 35；⑤ route 口径 6→3；⑥ scout「89 vs 87」内部不一致 →
  现行 FARM-EMIT 85。求值器 4 组 pin 全过（restcore.c3 逐点吻合、nb11
  3.7446884e-3 复现、recost DISJUNCTS 独立复现）。

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

## 8. 下一步清单

1. 等 `rulep-replay-w2` 收线（1,400 叶）→ **全盒内核补叶 5,112 叶（~38 CPU·h，
   Rule P）** → 装配 → `Assembly.nliTskXLLIPLS`（SORRIED 再 −1）。
2. 并行（纯 Python）：`nli-recost-w1` 重排 34 条 FARM，产出 ≤10 CPU·h 短名单
   （2026-11-15 16:14 发车）。
3. 回放后发 `ztgmain-w1`（γ4/dihY 套件，10 条 ZTGIJCF4）。
4. `nli-triage` 的 PICK-3：`get_main_nonlinear` 109 vs 108 对表；ZTGIJCF4
   `betaBumpLb` SF 记档。
5. LP 路线裁决（外部盘/农场/冻结）。
6. FARM 34 条：**不再排本地证书波次**（见 §1.3）；唯一候选 `nliRestIXPOTPA`
   （poly 档，0.59 CPU·h 起）；3 条 cell3 先补 `log`/负底规则；其余转 MATH/MATH-FARM。
7. `nliOx3q1h`：先落 **46 条线性**（`linarith`，零风险）；184 条 γ4 二选一——
   若 `g4port` Gate-0（`Jet3` 三阶导界 safety ≲10）过关，走 **CertTM2 引擎**
   （HOL 折算 ~81 CPU·h；#147 pilot 47 叶/0.78 CPU·h）；否则**每 (盒,签名)
   联合角点表**（48 盒 / 1,056 去重点 / 3,456 次求值；166 条角点 + 18 条 y4
   内部需一维补丁），**不要拆侧条件**（完美每盒界仍亏 9e−4…0.2）；
   uniform centered-form 不可行（16⁶ 子盒/条 ≈98 CPU·年）。
