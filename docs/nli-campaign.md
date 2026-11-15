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
- 当前：`rulep-replay-w2` 正在续跑 w1 checkpoint（预扫 610/1,400 0 FAIL、内核 3 叶；
  实时进度以 pq 续1166/后续条目为准）。回放完成后做全盒装配
  （5,012 old + 1,400 P 叶）→ `packIneqTskXLLIPLS_of_hull` →
  `Assembly.nliTskXLLIPLS`。
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
- 下一步：**`ztgmain-w1`**——建 γ4 下界 + dihY 下界套件，先在 3 条 +0.03698 上验证，
  再推 10 条。**不要**重派“套 NliBanks4/5 模板”。

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

1. 等 `rulep-replay-w2` 收线（1,400 叶）→ 全盒装配 → `Assembly.nliTskXLLIPLS`
   （SORRIED 再 −1）。
2. 回放后发 `ztgmain-w1`（γ4/dihY 套件，10 条 ZTGIJCF4）。
3. `nli-triage` 的 PICK-3：`get_main_nonlinear` 109 vs 108 对表；ZTGIJCF4
   `betaBumpLb` SF 记档。
4. LP 路线裁决（外部盘/农场/冻结）。
5. 其余 34 条 FARM：按 `tmparams`/Rule P 新成本重排，优先找 ≤10 CPU·h 的小盒。
