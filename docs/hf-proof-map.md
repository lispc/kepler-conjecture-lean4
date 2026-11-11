# Hales–Ferguson 证明主线 ↔ 我们的 Lean 树 对照

> **路线图（2026-11-09 用户指定）**：本文件是推进的基础。维护规则：
> 行号与正文随落库漂移时，在下方「状态更新」追加带日期的条目，不覆写正文；
> 引用行号对不上时按声明名 grep（名是稳定锚点）。
>
> ## 状态更新
>
> - **2026-11-12（06:50，编排者，十二）**：**`RRCWNSJ_p26` 真证落库（`75ed6d07`）——J 收工后第一条
>   真还债的锥内 sorry；基线 Z**。实测：cone `K_REACH 2,095,561`（+77，证明体 kit 入锥）/
>   **SORRIED 74**（75→74；清单 diff：closed 恰 `{Kepler.Text.RRCWNSJ_p26}`、added ∅）/
>   `K_AXIOM 585`（0/0）/ MODULES 5,219 / UNIVERSE 2,108,677 / COVERAGE 99.3796%；
>   口径 II 35,138 / 74 / 585 / 46,697。根面 589 **逐字节 IDENTICAL**；TSV 5,897 行 + manifest PASS。
>   另 `g482-482-w3` 增量落库（`3d8db02b`，19 条 `g482w3_*` 求和 kit +271 纯新增，全标准三）。
>   wave 12 在飞：`g482-482-w4`（general_482 续写 Body2 511 行 + T2–T8）/ `la7gen`（LA7 复制 W12A 真证）。
> - **2026-11-12（05:59，编排者，十一）**：**四笔落库 + 基线 Y**——`la22mono`（`3ebeecdd`，LA22 两件 +
>   23 条 private taum kit + import Gamma4Deriv2）、`la22aux`（`055dfcea`，xrr 两界 + LOCAL_FAN_AZIM_POS +
>   dih_y_mono）、`SF-108`（`4db35f92`，a/b/azim 7 处 ∃-ε 括号，陈述保真）、`cuxvzozG`（`e56181cb`，
>   Section G 六件）。四笔均不动锥内 sorry：SORRIED 仍 **75**（清单 0/0）、`K_AXIOM 585`（0/0）、
>   K_REACH 2,095,484（0）、K_UNIVERSE 2,108,564（+175 私有 kit，不可达）、COVERAGE 99.3797%。
>   根面 589 逐字节 IDENTICAL；TSV 5,898 行 + manifest PASS。**`general_482` 根路径 7 件 + 2 桥全绿**
>   ⇒ `g482-482-w2` 发车；`la27wire` 判 BLOCKED（`JCYFMRP_p27` 唯一缺口 = general_482；
>   `TFITSKC_p27` 缺 `TFITSKCv1_p27` + LA7 `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`）。
>   池事故与闸例外已入 `handoff §6` pit 16。
> - **2026-11-12（03:00，编排者，十）**：**三笔落库（g482kit `38d64102` / SF-107 `405df55d` /
>   g482 #1–#3 `66e70eb4`）+ 基线 X**——三笔均不动锥内 sorry：SORRIED 仍 **75**（清单 diff 0/0）、
>   `K_AXIOM 585`（名单 0/0）、K_REACH 2,095,484（0）、K_UNIVERSE 2,108,389（+32 = LA21 新增私有
>   helper，不可达）、COVERAGE 99.3879%（分母涨）。根面 589 与基线 W **逐字节 IDENTICAL**；
>   TSV 换装 5,898 行、manifest `--check` PASS。**SF-107**：`TUAPYYU_concl` 补
>   `main_nonlinear_terminal_v11` 前提（HOL `VASYYAU.hl:524-525` 陈述定义本身是条件式），
>   LA1/LA25/LocalConcl/VasTuaKit 链式岛编 0 err。**g482-w1**：#1–#3 全绿（HOL
>   CUXVZOZ.hl:839/:974/:1004），LA21 sorry 17→14。wave 4 在飞：g482no4（#4 本体）/
>   vas-nhx（NEHXMWH_p23）/ cuxvzozF（Section F 四件）；**g482-482 判 BLOCKED**——general_482
>   本体根路径实测 7 件 tainted + 2 桥（LA22:2298 / LA21:2248·2348·2192·2149·2170·2380 /
>   LA18:436 + `NOT_COL_EQ_UPS_X_POS` 无孪生），triage「七条前置」对本体不成立（续1001 ERRATA）。
> - **2026-11-12（02:25，编排者，九）**：**两笔落库 + 基线 W**——`mntdedup`（`1de85f96`）去重
>   `mnt11_anchor`（锥内 SORRIED **76→75**，清单 diff：closed 恰 `_private…mnt11_anchor`、added ∅；
>   **去重非还债**，银行债务 `nliMainNonlinearTerminalV11` 未动）+ `vas-w1`（`fb89790e`）
>   `VasTuaKit` 149 行三件真证（零删除资产；`TUAPYYU_concl` 目标判 BLOCKED）。
>   实测：cone `K_REACH 2,095,484`（−1）/ SORRIED **75** / `K_AXIOM 585`（名单 0/0）/
>   MODULES 5,219 / UNIVERSE 2,108,357（−1）/ COVERAGE 99.3894%；口径 II 35,061 / 75 / 585 / 46,377。
>   根面 589 与改前**逐字节 IDENTICAL**；TSV 换装 5,898 行、manifest `--check` PASS（pins OK）。
>   **SF-107 立案 + SF-102 ERRATA**：HOL `VASYYAU.hl:524` 的 `TUAPYYU_concl` 陈述本身带
>   `main_nonlinear_terminal_v11 ==>` ⇒ SF-102 的「排除项」误判（只读证明脚本漏看陈述定义）。
>   wave 3 在飞：g482-w1（#1）/ sf107-w1（执行 SF-107）/ g482kit-w1（simplex kit 两件）。
> - **2026-11-12（01:40，编排者，八）**：**J4-w1 落库（@`9ac1bc89`）——Text 章级债 21→20，锥总 77→76**。
>   实测：cone `K_REACH 2,095,485` / **SORRIED 76**（清单 diff：closed 恰 `{Kepler.Text.pkLeafRankCriticalEdge}`、
>   added ∅）/ `K_AXIOM 585`（名单 diff 0/0）/ MODULES 5,219 / UNIVERSE 2,108,358 / COVERAGE 99.3883%；
>   口径 II 35,062 / 76 / 585 / 46,378。根面 589 与基线 U **逐字节 IDENTICAL**；TSV 换装 5,899 行、
>   manifest `--check` PASS。**两车道 BLOCKED 判词**：aq13-w1（根 = `general_482_deformation_p21`）、
>   tame-corr-w1（根 = VASYYAU 家族 HOLD(b) ~1,815 HOL 行）；**general_482 前置 4/7 已真证**
>   （编排者探针：`deform_simplex_decrease_edge23_p21`/`deformation_BBs_p21`/`deformation_BBs_ALT_p21`/
>   `tau3_azim_p21` 全标准三；剩 3 kit 件仍 `sorryAx`）⇒ wave 2 三车道发车（g482 / vas / mntdedup）。
> - **2026-11-11（21:38，编排者，七）**：**基线 U 定格（@`64663be3`，J5-9 会师）——hTC Assembly 三件全闭；
>   e2e 剩余债 = 55 `nli*` + 1 hLP + 21 Text 章级**。实测：cone `K_REACH 2,095,443`（较 T +6,474）/
>   **SORRIED 77**（78→77；清单 diff：closed 恰 `{Kepler.Assembly.jcajydu}`、added ∅）/
>   `K_AXIOM 585`（名单 diff 0/0）/ MODULES 5,219（+472）/ UNIVERSE 2,108,348（+7,164）/
>   COVERAGE 99.3879%；口径 II 35,020 / 77 / 585 / 46,368；TSV 已换装（5,900 行）、
>   manifest `--check` PASS。根面 `#print axioms the_kepler_conjecture_e2e` = **589** = 585 native +
>   标准三 + `sorryAx`（fresh compile）。**两条判词**：① 路线图第 0 步「hTC 全闭 ⇒ e2e 只剩 hNL+hLP」
>   **只对 Assembly 侧成立**——`textCapstone` 消费的 Text 章级债 21 条仍在锥（基线 T 就在，非回归），
>   故 §5 行与 §7 行的 Text 层债务应继续按 `SORRY` 读；② **仪器勘误**：Lean 4.32 `#print axioms`
>   对导入声明读 olean 内**预计算公理表**（`CollectAxioms.lean:100-148`），池内旧 `Final.olean`
>   （2026-11-06）会报两条已删 `top_replay` **幻影公理**；已重编回灌，探针纪律见 `e2e-reachability-map.md` 基线 U。
> - **2026-11-09（编排者，六）**：§7 考古——**HOL 原版怎么证 tsk_bank 三条难件**（编排者实读，
>   详证见 pq 续408）：双层机器。前层 = `merge_ineq.hl prove_ineq` 按 tags 拼 tactic
>   （h0 切分 → `BRANCH_TAC` 分段引理 → `X_OF_Y_TAC` y→x 转换 / `SERIES3Q1H_5D_TAC` 6→5 维）
>   归约到 `prepared_nonlinear ==> ineq`；后层 = `mk_all_ineq.hl` 逐 prep 件真证 `|- prepared_nonlinear`
>   （`break_case_exec.prove_prep`：prep.hl 的 x-空间展开形 + `break_case_log.hl` 的 Iarg
>   切面树 + `SERIAL_TAC` 反序列化叶子证明——叶子证明由官方构建农场离线跑区间/TM 验证器
>   生成缓存，严格构建在内核内重放，`new_axiom`/`mk_thm` 已机械禁用）。**三条各自的证法**：
>   XLLIPLS = 1 次切面（x1@0.9501）+1 叶；WKGUESB 非对称版因「slow calculation」**被废弃**，
>   换对称版（析取缩域）——与我们候选方向 2（对称归约）同构；IYOUOBF sharp v2 = Xconvert
>   x-空间路线（Eps 1e-12/Sharp tags；无专用 break 树，走公共 prep 机制）。
>   **关键差异**：HOL 从不做「逐格 D_s 包络」，成本控制 = 对称缩域 + x 转换 + 按件手调切面
>   + 叶级 B&B 序列化重放 —— 即我们候选方向 1（branch-and-bound）+ 2（对称）+ 3（x 空间）。
> - **2026-11-09（编排者，五）**：**信任基座定格（基线 T @`52275a1c`）**——goodList 波四落地：
>   最后 2 条 `{hex,pent}_top_replay` 换 kernel `decide`+符号链，`K_AXIOM` **587→585**（根面 591→589，
>   Δ=2 精确命中）；manifest 再生 PASS，形状定格 **2 种**（shard-range 580 + tri-single-seed 5）。
>   **本文件正文中以下现时数字已被基线 T 取代**：§0 表 §6 行「585+2 native_decide」→「585 native_decide」、
>   §0 表 §9 行「根面 591 未清」→「根面 589 未清」、§10/§11/§12 处的「587 axiom」→ 585
>   （§6 的收尾**已完成**，不再是「在飞」）；SORRIED 78 与各项 sorry 结构不变。
>   本条目与「口径与数字出处」指针为权威，其余 587/591 字样按本条目折算。
> - **2026-11-09（编排者，四）**：§11 #3 拆单定案（jcajydu-scout）——jcajydu 本体是 99 行薄壳，
>   全部数学在前提 `restricted_hypermaps_are_planegraphs_thm`（reduction5.hl:150，
>   传递闭包 ≈20k HOL 行；"全树 0 移植"陈旧：基座/RXOKSKC/DANGEYJ/壳装配件已落，
>   reduction1-4 主体与 `nfgtrans'` 定义层仍零命中）。HOL capstone（the_main_statement.hl:179）
>   拿**真证定理**喂前提 ⇒ jcajydu 可真闭，但直接填 = 吞 17.7k 行链（NO-GO）。
>   路径：C1 壳波（条件形、200–300 行、无悔）→ C2=J0 → J1–J5 战役（20k/60–80 批/数周，立项待用户）。
> - **2026-11-09（编排者，三）**：§11 #9 勘误——`KcblrqcIneqDef` 定义侧**不是**零证书纯数学：
>   HOL `TRIANGULAR_FACE_AZIM_DART_BOUNDS`（tame_general.hl:739）以机器 ineq
>   `5735387903`/`5490182221` 为**显式前件**（`mk_imp`），而 Lean 定义（TameLp:516）
>   无此前件 ⇒ Lean 陈述强于 HOL 形，定义侧被注册表侧挡死
>   （`kcblrqc-defside` BLOCKED，编排者复核通过，见 pq 续402）。
> - **2026-11-09（编排者，二）**：§11 #4 重定义——`fully_surrounded_perimeter_bound` 的真路线**不是**移植三桥
>   （三引理已全覆盖：`Hypermap.face_representation`:2794 / `perimSumFaceArc` TameLp:903 / `yk10_convexLocalFan`:10642；
>   CIZMRRH 已证 LA3:2734；KCHMAMG 2-槽形已落 LA35:24547），而是树内已有的
>   `yk11_perimeterBound_of_core`（TameLp:10960）归约到**全称版 hcore** = WSEWPCH 本体
>   （polar_fan.hl:2213，1,150 HOL 行）——正主 = wsewpch 程序（W6a 任务单已立未跑，W6c 装配一行）。
>   §5 剩余根的拆分因此改为：`jcajydu`（侦察中）+ hcore（wsewpch-w6a/w6c）。
> - **2026-11-09（编排者）**：§7 差异 1 与 §11 #10/#12 的「`lp-registry` 在飞未提交、
>   `idsLpIneqs := []`（恒真）」表述**已被取代**：`60d0f544` DEF-FIX 落库，
>   `idsLpIneqs := lpIneqsIds`（127 条）+ `CertifiedIneqHolds := lpIneqProp`
>   —— `LpIneqs` 从恒真变**真债**（127 条真命题、未证），锥/根面不变
>   （SORRIED 78 / 根面 591）。§7 差异 2 的回落链描述仍准确（五兄弟分量仍 `True`）。
>   §6 收尾在飞：`goodlist-w4`（2 条 `{hex,pent}_top_replay` ⇒ 587→585）。
>
> 生成日期：2026-11-06。车道 `hf-proof-map`。**只读、零编译、主仓零改动。**
>
> ## 行号口径（先读这段）
> 本文件生成时，主仓 HEAD = `26b4f702`（2026-11-06 19:36），但工作树里有**在飞车道
> `lp-registry` 的未提交改动**：`M lean/Kepler/Assembly.lean`（+61/−30）、
> `?? lean/Kepler/Assembly/LpIneqProps.lean`（1714 行）。
> **本文所有 `Assembly.lean` 行号按工作树（含该改动）给**；纯 HEAD 版本里 `Assembly.lean`
> 尾部整体上移约 31 行、头部上移 6 行。引用前请先 `git diff --stat lean/Kepler/Assembly.lean`。
> 其余文件（`Text/`、`Graphs/`、`LP/`、`docs/`）行号 = HEAD。
> 声明**名**是稳定锚点：行号对不上时按名字 grep。
>
> ## 口径与数字出处（本文不自己重算任何指标）
> - 根面/债务/公理数：`docs/priority-queue.md` 文件头（**基线 Z @`75ed6d07`，2026-11-12**）
>   —— cone SORRIED **74**（= 55 `nli*` + 1 hLP + 18 Text 章级）/ `K_AXIOM` **585** /
>   根面 589 = 585 native + 标准三 + `sorryAx`。基线 Y（`e56181cb`）/ X / W 均为 SORRIED 75 / 根面 589；
>   基线 V（`9ac1bc89`）为 SORRIED 76 / 根面 589；
>   基线 U（`64663be3`）为 SORRIED 77 / 根面 589；基线 T（`52275a1c`）为 SORRIED 78 / 根面 589。
> - 75 的构成（56 Assembly + 19 Text）、585 的构成（580 shard-range + 5 tri-single-seed）：
>   `docs/e2e-reachability-map.md` 基线 Z + `handoff-2026-11-06.md` §0。
> - 信任基座逐类对照（含 `by eval` ↔ `native_decide`）、原版怎么处理 624：`docs/trust-base.md` §2 + `handoff §0.1`。
> - 图数 19,715（Tri 9 / Quad 1253 / Pent 16080 / Hex 2373）：`Kepler/Assembly.lean:7295-7299` docstring。
> - LP 记录 43,078（root 19,237 + easy 4,403 + hard 19,438、infeasible 189）：`Kepler/Text/LP/LPCert.lean:28-35` 文件头（该文件自己的盘点口径）。
> - HOL 源码：`reference/flyspeck/`（commit 1ce0353，见 `Assembly.lean:7`）；AFP：`reference/afp-flyspeck-tame/`。
>
> **完成度词汇**严格用七个：`PROVED` / `AXIOM` / `SORRY` / `MISSING` / `DIFFERS` / `NA` / `UNRESOLVED`。
> 一节拆成两半时写复合标签（例如 `PROVED / MISSING`），不做四舍五入。

---

## 0. 一句话总览表

| § | 这一步在证什么 | 完成度 | 我们这边的承重声明（file:line） |
|---|---|---|---|
| 1 | δ ≤ π/√18；FCC/HCP 取等 | **PROVED / MISSING** | `Kepler.the_kepler_conjecture_e2e`（`Final.lean:22`）；`kcImpTheKc`（`Assembly.lean:7021`）；取等无对象 |
| 2 | Voronoi 把密度变体积；`vol Ω ≥ √32` **不成立** | **PROVED / NA** | `fccCompatible`（`Text/PackingAuto2.lean:298`）；`FCC_COMPATABILITY_FUNC`（`Text/PackingAuto19.lean:590`） |
| 3 | 校正量 `A(v)`：`vol Ω + A ≥ √32`，`Σ A = O(R²)` | **PROVED** | `FCC_COMPATABILITY_FUNC`（PA19:590）+ `NEGLIGIBLE_FUNC`（PA19:754）+ `jgxzygw_p`（`Text/PackingJGXZYGW.lean:610`） |
| 4 | decomposition star `D`；`σ(D)`；`pt`；`σ ≤ 8pt` | **DIFFERS** | `FAN 0 V (ESTD V)`（`Text/Fan.lean:56`）；`sum_tauVEF_upper_bound`（`Text/TameLp.lean:1467`）——常数是 `4π−20sol0`，无 `pt` |
| 5 | contravening ⇒ 平面图 `G(D)` ⇒ tame | **SORRY** | `contraveningFan`（`Assembly.lean:2320`）、`mqmsmab`（`:2469`）、`tameCorrespondenceIso`（`:2521`）真证；`jcajydu`（`:2509`）与 `fully_surrounded_perimeter_bound`（`Text/TameLp.lean:925`）sorry |
| 6 | 枚举有限清单，且**无遗漏** | **AXIOM** | `tame_classification`（`Graphs/TameClassification.lean:23`）= `completeness`（`Graphs/RelativeCompleteness.lean:170`，真证）+ `same_0..3`（585+2 native_decide） |
| 7 | 每图：变量+约束 ⇒ 非线性层 + LP 层 ⇒ 排除 | **SORRY** | `TheNonlinearInequalities`（`Assembly.lean:317`，六分量 5 条 sorry）；`lpArchiveCertificatesDebt`（`:7073`） |
| 8 | 只剩 `G_fcc`/`G_hcp`/`G_pent`；`8pt + 6·0` | **NA / MISSING** | 架构不做三分支：`tameArchiveLists`（`Assembly/GoodListDefs.lean:82`）19715 张全走 LP；`pt`/`quad cluster` 分解无对象 |
| 9 | 局部 ⇒ 全局 ⇒ 密度上界；取等 ⇒ 完成 | **PROVED / SORRY+AXIOM（上游）** | `assembly`（`Assembly.lean:7319`）+ `the_kepler_conjecture_from_interfaces`（`:7327`）真装配；根面 591 未清 |

---

## 1. §1 要证明什么：密度上界 δ ≤ π/√18，FCC/HCP 取等

- **标准证明这一步在做什么**：把「单位球堆积的中心密度」写成 `#(V ∩ B_r) ≤ πr³/√18 + c·r²`，
  常数 π/√18 就是 fcc/hcp 的渐近密度；顺带指出 fcc/hcp 达到等号，所以常数不可改进。
- **HOL 对应物**：
  - `the_kepler_conjecture_def`（`reference/flyspeck/text_formalization/general/the_main_statement.hl:19-24`）
  - `kepler_conjecture`（`.../packing/pack_defs.hl:24`，体积/密度形）
  - `kc_imp_the_kc`（`the_main_statement.hl:82-107`）+ `FLYSPECK_DEVOLUTION` / `CPNKNXN`（`packing/flyspeck_devol.hl:135` 起）
- **我们的对应物**：
  - 陈述：`TheKeplerConjecture`（`lean/Kepler/Assembly.lean:2020-2025`）；
    镜像 `Kepler.the_kepler_conjecture_e2e`（`lean/Kepler/Final.lean:22-27`）；
    Phase-1 陈述占位 `Kepler.Statement.the_kepler_conjecture`（`lean/Kepler/Statement.lean:111`，body 仍 `sorry`，不在锥内）。
  - 体积形：`Kepler.Text.keplerConjecture`（`lean/Kepler/Text/PackingAuto2.lean:301-306`）。
  - 折算链：`kcImpTheKc`（`Assembly.lean:7021`）、`cpnknxn`（`:6810`）、`flyspeckDevolution`（`:6875`）。
- **完成度**：`PROVED / MISSING`
  - 密度**上界**这一步（陈述 + 体积↔计数折算 + saturated 扩张）全真证，`kcImpTheKc` 无 sorry。
  - **FCC/HCP 取等**：`MISSING`——见「差异」。
- **证据**：
  - `grep -n "^theorem kcImpTheKc" lean/Kepler/Assembly.lean` → `7021`，proof body 无 `sorry`。
  - `grep -rn "FCC\|HCP\|fcc\|hcp" lean/Kepler/ docs/` → 只命中定理名 `DAKEFCC`（`tame/tame_list.hl:9360` 的别名）与哈希串；无 fcc/hcp 图/取等陈述。
- **差异 / 风险**：
  - 标准证明的「FCC/HCP 取等」是**关于最优性的陈述**（δ = π/√18 可达）。**我们的根定理与 HOL `the_kepler_conjecture` 都只陈述上界**，
    没有「存在达到等号的堆积」这一条。`MISSING` 不是 bug，是两份形式化共同的范围选择；但读文档的人容易以为「取等」也在树里。
  - `Statement.lean:111` 的 Phase-1 `sorry` 仍在，但 `Final.lean` 走的是 Assembly 侧独立重述，不消费它（`Assembly.lean:2015-2019` 注记）。

---

## 2. §2 Voronoi 胞腔把密度变成局部体积问题；`vol Ω(v) ≥ √32` 单胞不等式**不成立**

- **标准证明这一步在做什么**：用 Voronoi 胞腔把「球覆盖体积」摊到每个中心一个胞腔
  `Ω(v) = voronoi_open V v`，于是密度问题变成 `vol Ω(v)` 的下界问题；
  朴素猜测 `vol Ω(v) ≥ √32`（正四面体胞腔体积）在一般堆积里**是假的**。
- **HOL 对应物**：
  - `voronoi_open` / `voronoi_closed` / `voronoi_set`（`.../general/sphere.hl:304/307/310`；重复于 `packing/pack1.hl:153`）
  - 失败的那条不等式本身在 HOL **没有单独命名**；它只以「被校正后的形态替代」出现：
    `fcc_compatible f S = (!v. v IN S ==> sqrt(&32) <= measure(voronoi_open S v) + f v)`
    （`packing/pack_defs.hl:22`，重复 `pack1.hl:332`）
  - 体积侧支撑：`pack1.hl:476` `ineq_lm5_3_step3`（`√32·#(S∩B) ≤ Σ(A+vol Ω)`）
- **我们的对应物**：
  - `voronoiOpen` / `voronoiClosed` / `voronoiSet` / `voronoiList` / `voronoiNondg`
    （`lean/Kepler/Text/PackingAuto2.lean:192/196/200/203/206`；`PackingAuto5.lean:60` 另有公开副本）
  - `fccCompatible`（`lean/Kepler/Text/PackingAuto2.lean:298-299`）：
    `∀ v ∈ S, Real.sqrt 32 ≤ volume.real (voronoiOpen S v) + f v`
  - 消费：`FCC_COMPATABILITY_FUNC`（`lean/Kepler/Text/PackingAuto19.lean:590-616`，真证）
- **完成度**：`PROVED / NA`
  - 校正形式（`vol + A ≥ √32`）`PROVED`；
  - 「朴素不等式不成立」这一**否定命题**在我们的架构里被 `NA`（消掉）：不需要证伪它，直接把校正项写进 `fccCompatible`。
- **证据**：
  - `grep -rn "sqrt 32" lean/Kepler/` → `PackingAuto2.lean:298`、`PackingAuto19.lean:585/601`、`PackingJGXZYGW.lean:613`。
  - HOL 侧 `grep -rn "SQRT_OF_32_lemma\|sqrt(&32)" reference/flyspeck/text_formalization/packing/` → `UPFZBZM.hl:97` 起（`SQRT_OF_32_lemma`）、`pack_defs.hl:22`。
- **差异 / 风险**：HOL 把 `voronoi_open` 同时定义在 `sphere.hl` 与 `pack1.hl`（两份），
  我们的 `voronoiOpen` 在 `PackingAuto2` 是 `private`、`PackingAuto5` 有公开副本、`PackingAuto16/19` 又各有 `_p16/_p19` 私有副本
  （`PackingAuto19.lean:572`、`PackingAuto16.lean:871`）。文档里出现「Voronoi」时先确认是哪一份；
  `p19_fcc_congr`（`PackingAuto19.lean:580-583`）就是靠「body 相同」做 `exact` 转移的桥。

---

## 3. §3 校正量 `A(v)`：局部 `vol Ω + A ≥ √32`，全局 `Σ A = O(R²)`

- **标准证明这一步在做什么**：构造显式校正函数
  `A(v) = −vol Ω(v) + 8·mm1 − 8·mm2·Σ_{w 邻近 v} lmfun(hl[v,w])`，
  证明它把每个胞腔补到 √32 以上（局部），同时它在球内的总和只增长 `O(R²)`（全局可忽略）。
  两个性质合起来 ⇒ 密度上界（Lemma 5.3 / `JGXZYGW`）。
- **HOL 对应物**：
  - `negligible_fun_p` / `negligible_fun_0`（`pack_defs.hl:18/20`）
  - `FCC_COMPATABILITY_FUNC_concl`（`packing/UPFZBZM.hl:58-64`）、`NEGLIGIBLE_FUNC_concl`（`:66-77`）、装配 `UPFZBZM`（`:227`）
  - `JGXZYGW`（`packing/pack1.hl:519`，Lemma 5.3 本体）；`JGXZYGW_KY`（`packing/RDWKARC.hl:76-91`）
  - 常数：`mm1`/`mm2`（`sphere.hl:511/513`）、`h0`（`:203`）、`lmfun`（`:523`）
- **我们的对应物**：
  - `negligibleFunP`（`lean/Kepler/Text/PackingAuto2.lean:290-292`）、`negligibleFun0`（`:294`）
  - `FCC_COMPATABILITY_FUNC`（`lean/Kepler/Text/PackingAuto19.lean:590`）、`NEGLIGIBLE_FUNC`（`:754`）、装配 `UPFZBZM`（`:915`）
  - 密度链叶子：`jgxzygw_p`（`lean/Kepler/Text/PackingJGXZYGW.lean:610`，**标准三公理**）
  - 消费：`JGXZYGW_p19`（`PackingAuto19.lean:934`，private）、`JGXZYGW_KY`（`:947`）、
    `rdwkarcConcl_pc`（`lean/Kepler/Text/PackingConcl.lean:1331`，`:1349-1350` 调 `UPFZBZM` + `JGXZYGW_KY`）
- **完成度**：`PROVED`
- **证据**：
  - `grep -n "^theorem UPFZBZM" lean/Kepler/Text/PackingAuto19.lean` → `915`；proof body 调
    `NEGLIGIBLE_FUNC`（:920）与 `FCC_COMPATABILITY_FUNC`（:921），两头都无 sorry。
  - `PackingJGXZYGW.lean:6-10` docstring：「the twelve `sorry` items discharged … capstone `jgxzygw_p`」。
  - `PackingConcl.lean:1349-1350`：`obtain ⟨G, hG0, hGf⟩ := UPFZBZM …; exact hden (JGXZYGW_KY …)`。
- **差异 / 风险**：无实质差异。唯一要注明的：`negligibleFunP` 的 `setSum` 对无限集走 `dif_neg` 分支取 0
  （`PackingAuto2.lean:124` 附近的有限支撑折算），与 HOL `sum` 对无限集的约定一致；
  消费点都显式携带 `Finite` 证据（如 `JGXZYGW_p19` 的 `fun r hr hfin => …`）。

---

## 4. §4 `decomposition star` `D`；得分 `σ(D)`；`pt`；核心命题 `σ(D) ≤ 8pt`

- **标准证明这一步在做什么**：把一个中心点周围的局部构型打包成「分解星」`D`（顶点 + 边 + 面 + 立体角），
  定义得分 `σ(D)`（各面 τ 贡献之和），然后证明核心局部不等式：contravening 的星满足 `σ(D) ≤ 8·pt`，
  `pt = 4 arctan(√2/5) − π/3 ≈ 0.0554` 是正四面体贡献的常数。
- **HOL 对应物**：
  - 「分解星」**没有这个名字**。对应物是**扇** `(V,E)` + 组合超映射：
    `fan` 谓词、`hypermap_of_fan`（`.../tame/tame_defs.hl:230`）、`face_set_of_fan`（`:235`）
  - 得分：`tauVEF`（`tame_defs.hl:274`；正文副本 `local/localization.hl:1559`），
    按面求和 = `sum (face_set (hypermap_of_fan (V,E))) (λf. tauVEF (V,E,f))`
  - 核心命题的实际形态：`sum_tauVEF_upper_bound`
    （`tame/ssreflect/tame_lemmas-compiled.hl:529-532`）：
    `&12 <= scriptL V ==> Σ_{f} tauVEF ≤ &4*pi − &20*sol0`
  - `sol0`/`tgt`：`sphere.hl:207`、`local/appendix.hl:106`
- **我们的对应物**：
  - 扇：`FAN 0 V (ESTD V)`（`lean/Kepler/Text/Fan.lean:56`）、`hypermapOfFan`（`:1189`）、
    `hypermapOfFanTl`（`lean/Kepler/Text/TameLp.lean:68`）、`faceSetOfFan`（TameLp:352 起）
  - 得分：`tauVEF_p2`（`lean/Kepler/Text/LocalAuto2.lean:369`），面集求和见
    `TameLp.sum_tauVEF_upper_bound`（`lean/Kepler/Text/TameLp.lean:1467-1471`）
  - `sol0`/`tgt`/`dTame`/`bTame`：`lean/Kepler/Text/LocalAuto1.lean:203/205`、`SphereKit.lean`
  - `squanderTarget = 15410`（= tgt·10⁴）：`lean/Kepler/Graphs/Tame.lean:21`，
    HOL 同值 `tame/import_tame_classification.hl:50`，桥 `tame/OXAXUCS.hl:105-111`
- **完成度**：`DIFFERS`
- **证据**：
  - `grep -rn "decomposition_star\|decomposition star" reference/flyspeck/ lean/Kepler/` → **零命中**。
  - `grep -rn "\bpt\b" reference/flyspeck/text_formalization/ lean/Kepler/ docs/` → `pt` 从未作为常数出现
    （Lean 命中全是 `MonoCorner.lean:712` 等局部变量 `pt : ℕ → …`；HOL 命中全是 `-- #0.055356` 这类系数）。
  - `grep -n "^theorem sum_tauVEF_upper_bound" -A 4 lean/Kepler/Text/TameLp.lean` → `1467`，结论
    `setSum (hypermapOfFanTl V E hfan).faceSet (fun f => tauVEF_p2 V E f) ≤ 4 * Real.pi - 20 * sol0`。
- **差异 / 风险**（必读）：
  1. **「星」被替换成「扇」**：没有独立的 `decomposition_star` 类型；`(V, ESTD V)` 这对数据 +
     `hypermapOfFan` 就是星的全部形式内容。所有「星的性质」都以 `FAN`/`hypermap` 谓词出现。
  2. **`pt` 与 `8pt` 在两棵树里都不存在**。HOL/Lean 实际用的界是 `σ ≤ 4π − 20·sol0`
     （数值 ≈ 1.54066，再放宽成 `tgt = 1.541`）。我核过 `4π − 20·sol0 ≠ 8·(4arctan(√2/5) − π/3)`
     （前者 ≈1.54066，后者 ≈0.4427），所以**不能**把 `sum_tauVEF_upper_bound` 说成「书里的 σ ≤ 8pt」。
     两者是同一层（面得分总和的上界）的不同归一化/不同常数；确切换算关系见 §12 `UNRESOLVED`。
  3. 这一步的**证明**在我们树里真证（`sum_tauVEF_upper_bound` 于 2026-10-23 真证明，见 `TameLp.lean:5-6`），
     但它的下游 `MQMSMAB` 仍经 `fully_surrounded_perimeter_bound` 的 sorry（见 §5）。

---

## 5. §5 反例（contravening star）⇒ 提取平面图 `G(D)` ⇒ `tame plane graph`

- **标准证明这一步在做什么**：若局部不等式失败，就得到一个「反例星」（packing、落在球壳、
  `scriptL > 12`、极大、13/14/15 个点、每点都被邻域包围）；从它的扇结构抽出平面超映射/平面图，
  证明它是 `tame` 的（平面、连通、单、无重边、面度 3–6、点度 3–7、例外面规则、权重和 < tgt）。
- **HOL 对应物**：
  - `contravening`（`.../tame/tame_defs.hl:248-253`）；`ESTD`/`ECTC`（`:191/194`）；`surrounded_node`（`:241`）
  - `FCDJDOT_concl`（`tame/tame_concl.hl:40-41`）：`?W packing ∧ ⊆annulus ∧ scriptL W > 12 ==> ?V. contravening V`
  - `UBHDEUU1/2`（`tame_concl.hl:28/30`，`packing ∧ ⊆annulus ⇒ FAN(…,ESTD/ECTC…)`）
  - `JGTDEBU1..11`（`tame_concl.hl:46-73`）、`CDTETAT`/`SZIPOAS`/`KCBLRQC`/`BDJYFFB1/2`/`CRTTXAT`（`:76-99`）、总装 `MQMSMAB_concl`（`:105`）
  - `tame_planar_hypermap`（`tame_defs.hl:183-186`，12 合取）
  - 反向（镜像支）：`hypermap_of_fan_neg`（`tame/ASFUTBF.hl:1007`）、`contravening_negative`（`:699`）
- **我们的对应物**：
  - `Contravening`（`lean/Kepler/Assembly.lean:129-135`，七合取）+ 具名投影 `proj_nliContrav_*`（`:143-176`）
  - `contraveningFan`（`Assembly.lean:2320`，真证）；`fcdjdot`（`:6746`，2026-11-06 `fcdjdot-body` 真证）
  - `mqmsmabWired`（`:2446`，真证）/ `mqmsmab`（`:2469`，一行转发）
  - `tamePlanarHypermapRestricted`（`:2484`，真证）；`TamePlanarHypermap`（`:2203`，12 合取）
  - `jcajydu`（`:2509`，**sorry**）；`tameCorrespondenceIso`（`:2521`，真证 → `Kepler.Text.TameCorrMain`）
  - `contraveningNegative`（`:4223`，真证）、`hypermapOfFanNeg`（`:4090`，真证）、`elllnyz`（`:3025`，真证）
  - TameLp 侧：`LpFan`（`Text/TameLp.lean:344`）、`contravening_lp_fan`（`:831`）、`JGTDEBU1..11`（`:2217` 起）、
    `SZIPOAS`（`:3012`）、`BDJYFFB1`（`:3110`）、`MQMSMAB`（`:10895`）
- **完成度**：`SORRY`
- **证据**：
  - 唯二 sorry 根：`jcajydu`（`Assembly.lean:2509-2514`，inline `sorry`）与
    `fully_surrounded_perimeter_bound`（`Text/TameLp.lean:925-933`，inline `sorry`；被 `TameLp.MQMSMAB:10900` 消费）。
  - `grep -n "^theorem contraveningFan\|^theorem mqmsmab\|^theorem tamePlanarHypermapRestricted\|^theorem tameCorrespondenceIso\|^theorem contraveningNegative" lean/Kepler/Assembly.lean`
    → `2320 / 2469 / 2484 / 2521 / 4223`，body 内无 `sorry`。
  - `textCapstone` 的消费链在 `Assembly.lean:7185-7218`（`PACKING_CHAPTER_MAIN_CONCLUSION_discharged` → `fcdjdot` →
    `contraveningFan` → `mqmsmab` → `tamePlanarHypermapRestricted` → `jcajydu` → `tameCorrespondenceIso`）。
- **差异 / 风险**：
  - HOL 的 `MQMSMAB` 前提含 `tame_planar_hypermap_calcs`（`tame_concl.hl:105` 一行的前件），
    我们把它拆成 `KcblrqcIneqDef` + `lp_main_estimate` 两个显式前提（`Assembly.lean:2469-2472`）——`DIFFERS`（参数化，不是弱化）。
  - `jcajydu` 是 `restricted hypermap → 平面图 g` 的构造，HOL 原文 `tame/JCAJYDU.hl:43`（调 `DAKEFCC`）。
    这条 sorry 与 §6 的枚举**不**相连（枚举只吃 `tame g`），它是「把超映射落到 Graph 层」的桥。

---

## 6. §6 图枚举：所有 tame 图有限清单，且**枚举无遗漏**

- **标准证明这一步在做什么**：`tame` 条件把图的规模卡死（面度/点度/点数 13–15/权重和），
  于是 tame 图只有有限多；跑一个工作列表式枚举器，把所有 tame 图枚举出来，
  与预先算好的 archive 逐一同构比对，证明「不漏」。
- **HOL 对应物**：
  - `tame`（平面图版）：`tame/import_tame_classification.hl:116-118`（`tame9a∧tame10∧tame11a∧tame11b∧tame12o∧tame13a`）
  - `tame_classification`（`text_formalization/general/the_main_statement.hl:63-68`）
  - `import_tame_classification`（`general/the_kepler_conjecture.hl:44-45`）、`archive`（`:40`）、
    数据 `formal_graph/archive/archive_all.ml`、`tame/good_list_archive.hl`
  - **原版怎么处理**：`tame/tame_concl.hl:26` 原文 `(* WTEMDTA_concl skipped. Tame hypermap classification theorem. *)`
    ——**HOL 把分类定理整条跳过**，`import_tame_classification` 在最终定理里是**前提**；
    枚举那一半由 Isabelle AFP 的 `Computation/ArchComp.thy` 用 8 条 `by eval` 做
    （`docs/handoff-2026-11-06.md` §0.1 实测引文）。
- **我们的对应物**：
  - `tame`（图版，6 合取）：`lean/Kepler/Graphs/Tame.lean:164-165`
  - `TameClassification`（`Assembly.lean:248-249`）：`∀ g, PlaneGraphs g → tame g → inIso g.fgraph {y | y ∈ a}`
  - `tame_classification`（`lean/Kepler/Graphs/TameClassification.lean:23-25`）= `completeness same_0 same_1 same_2 same_3 hpg ht`
  - `completeness`（`lean/Kepler/Graphs/RelativeCompleteness.lean:170-181`，**内核真证**，Isabelle `Relative_Completeness.thy` 的移植）
  - `same_0..same_3`：`Graphs/CertTri.lean:113` / `CertQuad.lean:142` / `CertPent.lean:248` / `CertHex.lean:340`
  - `Archive`（`RelativeCompleteness.lean:110`）= `{x | x ∈ TriData ++ QuadData ++ PentData ++ HexData}`，
    与 `tameArchiveLists`（`Assembly/GoodListDefs.lean:82`）逐字同体
  - 分片执行体：`Graphs/**/*Shard*.lean`（218 个文件）+ `ArchivePre*`/`TopReplay*`/`ReshardDefs.lean`
- **完成度**：`AXIOM`
- **证据**：
  - `grep -c "native_decide" lean/Kepler/Graphs/CertTri.lean` → 命中 `tri_shard_0..4` 段（`:86-106`）。
  - 公理数 587 = 585 shard + 2 `{hex,pent}_top_replay`：`docs/priority-queue.md` 文件头 + `handoff §0`。
  - 「无遗漏」的**结构**部分是真证：`completeness` 消费 `TameEnum_Archive`（`RelativeCompleteness.lean:180`）
    与 `tame5`（`:179`，`p ≤ 3` 的界），无 sorry。
- **差异 / 风险**：
  - **比 HOL 强、比 Isabelle 同类**：HOL 把分类定理跳过了（`import_tame_classification` 是前提），
    我们把它**证了**，代价是 585 条 `native_decide` 公理；这正是 `docs/trust-base.md` §2 的裁决对象
    （「与 `by eval` 同类、同数据」）。
  - 分片合起来**无损**这一点是组合检查（`trust_manifest.py` 的 (b)，`trust-base.md` §3），不是重算。
  - `TameClassification` 在 `TextCapstone` 里是**参数化前提**（`Assembly.lean:2035-2038`），
    在 `assembly` 里才由 `tame_classification` 填实（`:7319-7323`）。读的时候别把
    「`TextCapstone` 有 `TameClassification` 前提」误读成「没证」。
  - `tame13a`（admissible weight 的 LP）在**图版** `tame` 里是 `∃ w, admissible w g ∧ sum < squanderTarget`
    （`Graphs/Tame.lean:155-157`）。它**没有**独立证书通道：`tame13aCheck`（`:160-161`）的 docstring 自述是
    「the intended certificate format for the **future** certificate+checker pipeline」——即当前枚举
    把它烘在生成器/分片的 `native_decide` 里，没有可复算的权重见证文件。风险点，见 §11 #13。

---

## 7. §7 每张图：变量 + 约束 ⇒ 非线性区间算术层 + 线性规划层 ⇒ 排除

- **标准证明这一步在做什么**：对枚举出的每张图，把它的几何量写成有限个变量
  （平方边长 `y_ij`、二面角、立体角、`σ_R`、`τ_R`），在盒约束下导出两类可机器验证的判定：
  (a) **非线性不等式**：`f(y) > 0` 在盒上成立，用区间算术/Taylor 模型验证；
  (b) **线性规划**：把非线性问题线性化/分支后得到 LP，用精确有理对偶证书验证 `γ < 12` 或不可行。
  两类都过 ⇒ 该图不可能出现 contravening 星。
- **HOL 对应物**：
  - 非线性层：`text_formalization/formal_ineqs/`（区间算术、Taylor 模型）；
    不等式库 `nonlinear/ineq.hl`（`ineq_datum = {ineq; idv; doc; tags}`，`types.hl:44-50`）、
    `nonlinear/ineqdata3q1h.hl:265-541`、`nonlinear/main_estimate_ineq.hl`、`merge_ineq.hl`
  - `the_nonlinear_inequalities`（`general/the_main_statement.hl:55-59`，六合取）
  - `main_nonlinear_terminal_v11`（`local/terminal.hl:24-44`，`Main_estimate` 标签过滤）
  - LP 层：`formal_lp/verify_all.hl`（逐图终端证书）、`formal_lp/glpk/binary/{easy,hard}_*.dat`、
    `tame/linear_programming_results.hl:24/40`（`tame_result_lemma`、`linear_programming_results_th`）、
    `local/JEJTVGB.hl:232/236/244`（`lp_main_estimate`、`lp_main_estimate_JEJTVGB`、`nonlinear_imp_lp_main_estimate`）
  - `lp_ineqs` 构造：`general/the_main_statement.hl:29-45`（`Lp`/`Tablelp`/`Lp_aux` 标签 + id `"6170936724"`，剔除 `deprecated_quads`）
- **我们的对应物**：
  - 变量族：`deltaY`/`dihY`/`solY`/`etaY`/`gamma3f`/`gamma4fgcy`/`taum`/`azimDart`
    （`Text/SphereKit.lean:103/109/121/171`、`Text/IneqClosureDefs.lean:620`、`Text/PackingAuto20.lean:123/139`、`Text/Fan.lean:183`）；
    `tauVEF_p2`（`Text/LocalAuto2.lean:369`）
  - 非线性层：`Kepler/Interval/`（`IExpr` `Interval/Expr.lean:98`、`checkPos:428`、`checkPos_sound:435`、
    `CertTM.lean:4009` `checkPosTM`、`MonoCorner.lean` 单调性）；证书 `Kepler/Interval/Cases/`（273 个条目，3.8 GB）
  - 六分量：`TheNonlinearInequalities`（`Assembly.lean:317-320`）=
    `pack_nonlinear_non_ox3q1h ∧ ox3q1hP25 ∧ main_nonlinear_terminal_v11 ∧ LpIneqs ∧ PackIneqDefA ∧ KcblrqcIneqDef`
    - `pack_nonlinear_non_ox3q1h`：`Text/PackingAuto21.lean:968`（81 条）
    - `ox3q1hP25`：`Text/PackingAuto25.lean:94`（**230 条显式合取** = 46 record × 5 支）
    - `main_nonlinear_terminal_v11`：`Text/LocalAuto1.lean:2139`（109 条 ID，清单 `:1902`，长度钉子 `:2015`）
    - `LpIneqs`：`Assembly.lean:299`，注册表 `idsLpIneqs`（`:294`）
    - `PackIneqDefA`：`Assembly.lean:305` → `Text/PackingAuto22.lean:406`
    - `KcblrqcIneqDef`：`Assembly.lean:309` → `Text/TameLp.lean:516`
  - 查表语义：`CertifiedIneqHolds`（`Assembly.lean:286`）→ `lpIneqProp`（`Assembly/LpIneqProps.lean:1632-1636`）
  - LP 层：`checkDualCMTF`（`Kepler/LP/ColMajor.lean:773`，soundness `:809`）、
    `farkasCheck`（`Text/LP/LPFarkas.lean:67`，soundness `:198`）、
    `LpTerminalCertified`（`Text/LP/LPCert.lean:60-66`）、
    43,078 具名叶 `Text/LP/LPLeaf{Root,Easy,Hard,Infeas}*.lean`、装配 `Text/LP/LPAll.lean:190/553`
  - 接口：`lpArchiveCertificatesDebt`（`Assembly.lean:7073-7079`）
- **完成度**：`SORRY`
- **证据**：
  - `grep -n "^theorem nliOx3q1h\b\|^theorem nliMainNonlinearTerminalV11\b\|^theorem nliLpIneqs\b\|^theorem nliPackIneqDefA\b\|^theorem nliKcblrqcIneqDef\b" lean/Kepler/Assembly.lean`
    → `1885 / 1907 / 1925 / 1958 / 1973`，**五条都是 `:= sorry`**。
  - `grep -n "def idsLpIneqs\|def CertifiedIneqHolds" lean/Kepler/Assembly.lean` → `294` / `286`；
    值 `lpIneqsIds`（127 条，钉子 `lpIneqsIds_length = 127`）/ `lpIneqProp`。
  - `grep -c "sorry" lean/Kepler/Text/LP/LPLeafRoot00.lean` → 每叶一 sorry（骨架 deferred-compute）。
  - 唯一端到端闭合的 ineq 样板：`ineq_3397113841`（`Assembly/IneqPilot.lean:50-97`），`#print axioms` = 标准三。
  - 唯一端到端闭合的 LP 样板：`Kepler/LP/PilotCM204880136538/{Data,Bench,Assembly}.lean`
    （915 变量 / 3882 行，`dual_check` + `bound` 全 `decide`）。
- **差异 / 风险**（必读）：
  1. **LP 注册表刚被真化，但只是「从恒真变真债」**。在飞车道 `lp-registry`（**未提交**）把
     `idsLpIneqs := []` 改成 `lpIneqsIds`（127 条），把 `CertifiedIneqHolds := certifiedIneqHolds_pilot`
     改成 `lpIneqProp`（`LpIneqProps.lean:1632`，127 条字面命题按 id 查表）。
     文件头自述：「127 条命题本身是本轮**未证债务**（`nliLpIneqs` 仍是 sorry）；本文件只把它们从
     '空量化恒真' 换成 '真实但未证'」。已提交的 HEAD 仍是 `idsLpIneqs := []`（恒真）。
     **引用数字时务必区分这两个状态**（`docs/trust-base.md` §2 / `priority-queue.md` §1 描述的是 HEAD）。
  2. **`CertifiedIneqHolds` 的回落链仍然退化**：`lpIneqProp` 的四个分支是
     LP 清单内→字面命题；`"3397113841"`→已证试点；`certLookupDomain` 内其余（五个兄弟分量）→ **`True`**；域外→`False`
     （`LpIneqProps.lean:1632-1636`）。`False` 域外分支是相对 HEAD 的**收紧**，但五个非 LP 分量的
     `True` 回落仍是「静默退化」区（`trust-base.md` §2 列为必须修）。
  3. **tag 机制不存在**。HOL 的 `ineq_datum` 带 `tags : tag list`（`types.hl:44-50`），
     其中 `Quad_cluster of float`（`:36`，语义见 `:138-140`：「an ineq on a coupled pair of simplices，
     float 是 breaksapart 的 margin」）、`Dim_red`、`Set_rad2`、`Delta126min/max` 等 20+ 种
     都是给验证器/优化器的**控制提示**。我们的 Lean 树里**没有 `tag`/`Ineq` 记录类型**
     （`grep -rn "Dim_red\|Set_rad2\|Delta126" lean/Kepler/` 零命中），每条 ineq 直接落成
     「`∀ y1..y6, 盒 → 不等式`」的命题；`Quad_cluster` 的「耦合对单纯形」语义只能从
     `ox3q1hP25` 的字面（`y1 y12 y23 y34 y41` 五变量分支）间接读出。
  4. **LP 的 43,078 条记录一条都没有真正重跑/灌装**：只有 1 条 pilot 记录
     （`114084514923_t0000`，`Text/LP/LPPilot.lean:2-31`）与 1 条 pilot LP 实例
     （`PilotCM204880136538`）真的跑过。覆盖桥（per-record 总量 → `¬Contravening V`）自述「真缺口」
     （`Assembly.lean:7272`）。
  5. `TameLp.lean` 文件头仍写「剩余 sorry = `fully_surrounded_perimeter_bound` / `ineq_tauK_tauVEF_std` 群」，
     但 `grep -n "sorry" lean/Kepler/Text/TameLp.lean` 只剩 `:933` 一处 —— `ineq_tauKτ_std` 群已收口
     （`TameLp.lean:10799` 注记「占位行已收口删除」）。**文件头 stale**。

---

## 8. §8 只剩 `G_fcc`、`G_hcp`、`G_pent`；`8·pt + 6·0 = 8pt`；`G_pent` 专门论证

- **标准证明这一步在做什么**：把 §7 的逐图排除法做完后，**只剩三张图**：
  fcc 与 hcp（各由 8 个拟正则四面体贡献 `8·pt`，6 个 quad cluster 贡献 0，合计恰好 `8pt`，故取等）
  和五边形图 `G_pent`（另有一套专门论证）。这一步同时锁定「常数不可改进」。
- **HOL 对应物**：**无同名对象**。最接近的机制是：
  - 归档清单 `tame_archive_lists`（`formal_graph/archive/archive_all.ml`）——19715 张图，无 fcc/hcp/pent 分类标签；
  - `HRXEFDM_concl`（`tame/tame_concl.hl:43-44`）：`contravening V ==> Σ_face tauVEF < 4π − 20·sol0`
    ——但 `HRXEFDM.hl:7` 原文注明「use `Tame_lemmas.sum_tauVEF_upper_bound` because the theorem below
    has unproved assumptions」，实际走 `sum_tauVEF_upper_bound`；
  - 真正的排除是 `lp_ineqs` + 逐图 LP（`linear_programming_results`）。
- **我们的对应物**：
  - 归档：`tameArchiveLists`（`Assembly/GoodListDefs.lean:82`）= `TriData ++ QuadData ++ PentData ++ HexData`；
    `ArchiveData/{Tri,Quad,Pent,Hex}.lean`；`Archive`（`Graphs/RelativeCompleteness.lean:110`）
  - 排除机制：`lpArchiveCertificatesDebt`（`Assembly.lean:7073`）+ 43,078 叶（§7）
  - 取等/极值：**无对象**（`grep -ri "fcc\|hcp" lean/ docs/ reference/flyspeck/` 的命中全是定理名 `DAKEFCC` 或哈希片段）
- **完成度**：`NA / MISSING`
- **证据**：
  - `grep -rn "8 \* pt\|8pt\|quad_cluster" reference/flyspeck/text_formalization/ lean/Kepler/ docs/` →
    唯一命中是 `nonlinear/types.hl:36` 的构造子 `Quad_cluster of float`（tag，见 §7 差异 3）；`8pt` 零命中。
  - `grep -rn "tame_archive_lists" reference/flyspeck/` → 清单本身（`archive_all.ml`），无三图子集。
- **差异 / 风险**（这是最容易「以不同方式实现」的一节，必须说清）：
  1. **我们（以及 HOL）根本不做「只剩三张图」这一步**。形式化把**所有** 19715 张 tame 图
     一视同仁地送进 LP/非线性层，`¬Contravening` 对每张图独立成立；
     「哪张图取等」是**元层面的观察**，不是证明义务。因此没有 `G_fcc`/`G_hcp`/`G_pent` 对象，
     也没有「6 个 quad cluster 贡献 0」这个核算。标记 `NA`。
  2. **`8pt + 6·0` 的算术不在树里**。没有 `pt` 常数（§4），所以 `8·pt + 6·0 = 8pt` 无从写。
     若将来要形式化「常数最优」，需新开一条线（`MISSING`）。
  3. **`G_pent` 的「专门论证」在形式化里被吸收进 LP 记录**：`PentData`（16080 张图）只是 archive 的一段，
     走同一套 `lpArchiveCertificatesDebt`。`pent_hex.hl`
     （`reference/flyspeck/text_formalization/local/pent_hex.hl:1-13`，「Terminal Pent and Hex cases，
     pent with 5 top edges=2」）是**主估计的终端情形章**，不是 §8 的 `G_pent`，别混。

---

## 9. §9 局部结果代回全局 ⇒ 密度上界；FCC/HCP 取等 ⇒ 完成

- **标准证明这一步在做什么**：把 §3 的「局部不等式 + 可忽略」代回 §1 的密度陈述：
  对任意 packing，把球内点数用 Voronoi 体积 + 校正量夹住，得到 `π/√18 + c/r`；
  再指出 fcc/hcp 取等，于是定理与其最优性同时成立。
- **HOL 对应物**：
  - `kc_imp_the_kc`（`general/the_main_statement.hl:82-107`）
  - `reduction_to_local_annulus_inequality`（`:111-139`）：`the_nonlinear_inequalities ∧ (∀V, cell_cluster_inequality V) ∧ (∀V, packing ∧ ⊆annulus ⇒ local_annulus_inequality V) ⇒ the_kepler_conjecture`
  - `kepler_conjecture_with_assumptions`（`:170-251`，80 行 tactic）
  - 总装 `kepler_conjecture_with_assumptions_and_archive`（`general/the_kepler_conjecture.hl:69-85`）
  - `PACKING_CHAPTER_MAIN_CONCLUSION`（`packing/OXLZLEZ3.hl:9019-9039`）：
    `~kepler_conjecture ∧ pnn ∧ ox3q1h ⇒ ∃V, packing ∧ ⊆annulus ∧ ¬local_annulus_inequality V`
- **我们的对应物**：
  - `kcImpTheKc`（`Assembly.lean:7021`）、`cpnknxn`（`:6810`）、`flyspeckDevolution`（`:6875`）
  - `PACKING_CHAPTER_MAIN_CONCLUSION`（`Text/PackingAuto25.lean:16086-16099`）与 `_discharged`（`Text/PackingConcl.lean:1456-1466`）
  - `rdwkarcConcl_pc`（`Text/PackingConcl.lean:1331`）、`OXLZLEZ`（`Text/PackingAuto25.lean:16068`）、
    `CELL_CLUSTER_ESTIMATE_PROPS`（`:16044`）、`GRHIDFA_concl`（`Text/PackingAuto3.lean:3545`，经 `p3k_GRHIDFA`）
  - 接口装配：`nonlinearInequalities`（`:7110`）、`linearProgrammingResults`（`:7119`）、
    `textCapstone`（`:7128`）、`goodListArchive`（`:7301`）、`assembly`（`:7319`）、
    `the_kepler_conjecture_from_interfaces`（`:7327`）
- **完成度**：`PROVED / SORRY+AXIOM（上游）`
  - 「代回全局」这一步本身是**真装配**：`assembly` 只消费三个接口 + 已证的 `tame_classification`。
  - 根面 `#print axioms Kepler.the_kepler_conjecture_e2e` 仍是 **591**（= 587 native + 标准三 + `sorryAx`，
    `docs/priority-queue.md` 文件头实测），所以**根定理不是 PROVED**。
- **证据**：
  - `grep -n "^theorem assembly\|^theorem the_kepler_conjecture_from_interfaces" lean/Kepler/Assembly.lean` → `7319 / 7327`。
  - `Assembly.lean:7321`：`refine hTC tameArchiveLists ⟨?_, ⟨goodListArchive, hLP⟩, hNL⟩`（三个前提都在）。
  - `Assembly.lean:7323`：`exact Kepler.Graphs.tame_classification hpg ht`（枚举真证填 `TameClassification`）。
- **差异 / 风险**：
  - HOL 的总装是 `import_tame_classification ∧ linear_programming_results ∧ the_nonlinear_inequalities ⇒ the_kepler_conjecture`，
    其中 `import_tame_classification` **是自由前提**；我们把它证了（§6），因此根定理的**前提面更小**，
    代价是 585 条 `native_decide` 公理。这是两份形式化最实质的架构差。
  - `Statement.lean:111` 的 `the_kepler_conjecture`（Phase-1 `sorry`）在树里仍在，但**不在锥内**；
    锥走 `Final.lean` → `Assembly.the_kepler_conjecture_from_interfaces`。

---

## 10. 逻辑链总表

用户给的 boxed 链（密度上界 ⟸ 局部不等式 + 可忽略 ⟸ σ≤8pt ⟸ tame 图有限 ⟸ 区间+LP 排除 ⟸ FCC/HCP 取等），逐箭头拆：

| # | 链上的箭头 | 我们这边对应哪一步 | 骨架（sorry/公理） | 已真证 |
|---|---|---|---|---|
| 1 | 密度上界 ⟸ 局部 `vol+A≥√32` + 全局 `ΣA=O(R²)` | `JGXZYGW_KY`（PA19:947）/ `jgxzygw_p`（PackingJGXZYGW:610）⟸ `UPFZBZM`（PA19:915） | 无 | **全部**（§2/§3） |
| 2 | 局部不等式 ⟸ `σ(D)` 上界 | `MQMSMAB`（TameLp:10895）的 `MQMSMAB_tame13a` 分支 ⟸ `sum_tauVEF_upper_bound`（TameLp:1467，`≤ 4π−20sol0 < tgt`） | `fully_surrounded_perimeter_bound`（TameLp:925） | `sum_tauVEF_upper_bound`、`Adm1/2/3` 装配 |
| 3 | `σ≤8pt` ⟸ tame 图有限 | **HOL/我们没有这条箭头**：tame 性是**从 contravening 直接推出**（`MQMSMAB`），不是从 σ 界 + 枚举反推 | — | `mqmsmab` 链（除 #2 的 sorry） |
| 4 | tame 图有限 ⟸ 枚举无遗漏 | `TameClassification`（Assembly:248）⟸ `tame_classification`（Graphs:23）⟸ `completeness`（RelativeCompleteness:170）+ `same_0..3` | **585+2 native_decide 公理** | `completeness`（结构无遗漏）、`TameEnum_Archive`、`tame5` |
| 5 | 排除 ⟸ 区间 + LP | `Contravening V ⇒ ¬Contravening V` 由 `hLPR`（`textCapstone:7185-7218`）给出 ⟸ `lpArchiveCertificatesDebt`（Assembly:7073）；非线性侧由 `TheNonlinearInequalities` 六分量供 `OXLZLEZ`/`TSKAJXY`/`MQMSMAB` 的银行前提 | **`lpArchiveCertificatesDebt` + 43,078 叶；`nli*` 五条 + 57 条 Assembly sorry** | 区间/Taylor 内核（`IExpr`/`checkPos`/`checkPosTM`）、LP 内核检查器（`checkDualCMTF`/`farkasCheck`）、各 1 条 pilot |
| 6 | FCC/HCP 取等 ⟸ 完成 | **无对象**（§8） | — | — |
| — | 总装：局部 ⇒ 全局 | `assembly`（Assembly:7319）→ `the_kepler_conjecture_from_interfaces`（:7327）→ `Final.lean:22` | 上游 78 sorry + 587 axiom | `assembly` 本体、`kcImpTheKc`、`cpnknxn`、`flyspeckDevolution` |

**读法**：链的**算术骨架**（#1、#4、总装）在我们树里是真的；链的**计算内容**（#5）几乎全是 sorry；
链的**最优性尾巴**（#6）不存在。`#3` 是书里的叙事倒装——形式化不需要它。

---

## 11. 缺口清单（按「离根定理最近」排序）

| # | 缺口 | file:line | 完成度 | 一句话为什么还没补上 |
|---|---|---|---|---|
| 1 | `nonlinearInequalities` 的六分量骨架（14 个开放节点，直接是根的三前提之一） | `Assembly.lean:7110` 及其骨架件（`:395`–`:1973`） | `SORRY` | 五条分量本体（`nliOx3q1h:1885`、`nliMainNonlinearTerminalV11:1907`、`nliLpIneqs:1925`、`nliPackIneqDefA:1958`、`nliKcblrqcIneqDef:1973`）+ 81/109/230 条逐条证书灌装；证书农场是用户保留的重型计算项（`AGENTS.md` §4） |
| 2 | `lpArchiveCertificatesDebt`（hLP 的唯一 sorry 根） | `Assembly.lean:7073-7079` | `SORRY` | 43,078 条 LP 终端记录一条都没有重跑/灌入；注册表（127 条）已真化但只是「真命题、未证」；覆盖桥（per-record → `¬Contravening`）自述「真缺口」（`:7272`） |
| 3 | `jcajydu`（hTC 三件之一） | `Assembly.lean:2509-2514` | `SORRY` | `restricted hypermap → 平面图 + GoodGraphV4 + iso` 的构造；HOL 原文 `tame/JCAJYDU.hl`，依赖 `DAKEFCC`（`iso_restricted`）。同章另两件（`fcdjdot`、`tameCorrespondenceIso`）已真证 |
| 4 | `TameLp.fully_surrounded_perimeter_bound` | `Text/TameLp.lean:925-933` | `SORRY` | `MQMSMAB`（TameLp:10895）的 12 合取之一（`tame12o`/`Adm2` 线的周长上界）。缺三座桥：`WSEWPCH`/`FAN_PERIMETER`/`BGMIFTE`（LocalAuto7 周长 lane 仍是 faithful sorry）+ `f_surr_localization_convex_local` 等三件未移植（原位 NEEDS 注记） |
| 5 | `ox3q1hP25` 的 230 条本体 | `Text/PackingAuto25.lean:94`（定义）→ `Assembly.lean:1885`（`:= sorry`） | `SORRY` | DEF-FIX（`b85eaade`）已把 `def := sorry` 换成显式 230 条合取，但**证明**一条都没闭合；需要 46 record × 5 支的区间证书 |
| 6 | `main_nonlinear_terminal_v11` 的 109 条 | `Text/LocalAuto1.lean:2139` → `Assembly.lean:1907` | `SORRY` | 109 条 `Main_estimate` 逐条 `mainEstimate_*` def 已具名，证书未灌装 |
| 7 | `pack_nonlinear_non_ox3q1h` 的 81 条残余（1a–1d 四骨架件） | `Text/PackingAuto21.lean:968` → `Assembly.lean:1828-1874` | `SORRY` | cell3/tsk/grk 多数已真证，`nliPackNonlinearRest`（62 条）等仍是 sorry；A2 车道在飞 |
| 8 | `PackIneqDefA`（3 族 5 条盒式） | `Text/PackingAuto22.lean:406` → `Assembly.lean:1958` | `SORRY` | 真合取本体已真化在 PA22（`UKBRPFE/WAZLDCD/BIEFJHU`），但 `nliPackIneqDefA` 这一跳仍是 sorry |
| 9 | `KcblrqcIneqDef`（azim 界 + `cdTetatPairs`） | `Text/TameLp.lean:516` → `Assembly.lean:1973` | `SORRY` | 定义已是真切片（不再是 `True` 占位），证明未闭合；喂 `MQMSMAB` 的 `KCBLRQC` |
| 10 | `lp_ineqs` 127 条真命题（`lpIneqProp` 正文） | `Assembly/LpIneqProps.lean:1632`（查表）+ 127 条 `lpIneq_*` def | `SORRY` | 在飞 `lp-registry` 只做了「转写」：命题真实但未证。`nliLpIneqs`（`Assembly.lean:1925`）仍是 sorry |
| 11 | 43,078 个 LP 叶 | `Text/LP/LPLeaf*.lean`（各一 sorry） | `SORRY` | 全部 `deferred-compute`：SoPlex 精确主批 + glpsol 精确对偶尾部；只有 1 条 pilot 真的跑了（`LPPilot.lean`） |
| 12 | `CertifiedIneqHolds` 的 `else True` 回落（五个非 LP 分量） | `Assembly/LpIneqProps.lean:1632-1636`（第三分支 `certLookupDomain → True`） | `SORRY`（结构性） | 域外已收紧为 `False`，但五个兄弟分量的域内 id 仍退化为 `True`；`trust-base.md` §2 列为必须修 |
| 13 | 枚举公理（585 shard + 2 top） | `Graphs/Cert{Shards,Tri,Quad,Pent,Hex,TopReplay*}`；`Graphs/TameClassification.lean:23` | `AXIOM` | **已裁决为信任基座**（`trust-base.md` §1：唯一还算债的是 `sorryAx`）；列为缺口只为排序完整 |
| 14 | `tame13a` 权重见证没有独立证书通道 | `Graphs/Tame.lean:156-161`（`tame13aCheck` 自述「future pipeline」） | `UNRESOLVED` | 当前烘在 shard 的 `native_decide` 里；若将来要求「可复算权重文件」，需新机制 |
| 15 | `pt` / `8pt` / `G_fcc` / `G_hcp` / `G_pent` / `quad cluster` 分解 | — | `MISSING` | 不在证明义务里（§8 `NA`）；只有做「常数最优性」时才需要 |

---

## 12. 我搜过但没找到的

| 关键词 | 搜过的目录 | 结论 |
|---|---|---|
| `decomposition_star` / `decomposition star` / `star_set` | `reference/flyspeck/`（全树）、`lean/Kepler/`（全树）、`docs/` | **零命中**。只有 `decomposition_planar_by_angle_fan`（`local/WJSCPRO.hl:699` 等，平面图论引理）、`FULLY_SURROUNDED_NODE_DECOMPOSITION`（`tame/CDTETAT.hl:198`）、`MEASURE_LUNE_DECOMPOSITION`（我们的 `Geom/SolidAngle.lean:512`）——三者都不是 §4 的星。→ §4 标 `DIFFERS`（星 = 扇 + hypermap） |
| `pt`、`8pt`、`4 * atn (sqrt (&2) / &5)`、`arctan (√2/5)`、`0.0553/0.0554/0.05537` | `reference/flyspeck/`（`.hl`/`.ml`）、`lean/Kepler/`、`docs/*.md` | **作为常数零命中**。HOL 里 `atn` 只出现在数值证书（`local/lp_details.hl:1304` 等）；`#0.055356` 是 `ineqdata3q1h.hl` 的线性系数，不是 `pt`。→ §4/§8 标 `MISSING`/`UNRESOLVED` |
| `4π − 20·sol0` 与 `8pt` 的换算 | `sphere.hl:207`（`sol0`）、`tame_defs.hl:77`（`tgt`）、`local/appendix.hl:106`（`tgt`）、`tame/OXAXUCS.hl:105`（`tgt = squanderTarget/10000`） | **定不下来**。`sol0 = 3·acs(1/3) − π` ⇒ `4π − 20·sol0 ≈ 1.54066`；`8·(4·arctan(√2/5) − π/3) ≈ 0.4427`。两者数值不等，树里也没有 bridge 引理。→ **UNRESOLVED** |
| `fcc` / `hcp`（作为图名） | `reference/flyspeck/`、`reference/afp-flyspeck-tame/`、`lean/Kepler/`、`docs/` | 只有噪声：`DAKEFCC`（`tame/tame_list.hl:9360` 的 `iso_restricted` 别名）、`trig3.hl` 与 `.nb` 里的零散串。**无 fcc/hcp 图对象、无取等陈述** → §1/§8 `MISSING` |
| `quad_cluster` / `QuadCluster` | `reference/flyspeck/text_formalization/nonlinear/`、`lean/Kepler/` | HOL 只有**构造子** `Quad_cluster of float`（`types.hl:36`，语义 `:138-140`）；**Lean 零命中**（整个 `tag`/`Ineq` 记录类型都不存在）→ §7 差异 3、§8 `MISSING` |
| `G_pent` / 「pent graph」/ pent 专门论证 | `reference/flyspeck/text_formalization/local/pent_hex.hl`、`tame/`、`lean/Kepler/` | `pent_hex.hl` 是「Terminal Pent and Hex cases」（主估计终端情形），不是 §8 的 `G_pent`；`PentData`（`ArchiveData/Pent.lean`）只是 archive 的一段。→ §8 `NA` |
| `τ_R` / `σ_R`（书里的记号） | `lean/Kepler/`（`tauV`/`sigma`/`tauR`/`sigmaR`）、`reference/flyspeck/` | 没有叫 `σ_R`/`τ_R` 的对象。按**角色**最近的：`tauVEF`（HOL `tame_defs.hl:274`）/ `tauVEF_p2`（`LocalAuto2.lean:369`）与 `taum`（`sphere.hl:215`）/ `SphereKit.lean:171`。→ 按角色映射，标 `UNRESOLVED`（无逐字对应） |
| `tauV`（`sphere.hl:219`）的 Lean 逐字副本 | `lean/Kepler/`（`\btauV\b`） | **零命中**（只有 `tauVEF`/`tauVEF_p2` 命中子串）。`sphere.hl:219` 的 `tauV` 未逐字移植。→ `UNRESOLVED` |
| `A(v)`（校正量作为具名函数） | HOL + Lean | 没有叫 `A` 的对象；HOL 用 `G`（`UPFZBZM.hl:58-64` 的 `G = λu. −vol + 8mm1 − 8mm2·Σlmfun`），我们用同一个显式 λ（`PackingAuto19.lean:600-602`）。→ 映射成立，但不是「同名对象」 |
| `pt`-型「最优性/取等」定理 | `lean/Kepler/`（`attains`/`equality`/`optimal`）、`docs/` | 根的陈述只有 `≤`；**无取等/最优性定理** → §1 `MISSING` |
| `saturated` 的 Lean 侧「原版语义」 | `Statement.lean`、`PackingAuto2.lean`、`PackingJGXZYGW.lean` | `saturated` 有多个副本（`Statement` / `PackingAuto2` / `PackingJGXZYGW:611` 内联 `∀ x, ∃ y ∈ S, dist x y < 2`）。不是缺口，但引用时要指明副本 |
| `WTEMDTA`（分类定理本体） | HOL + Lean | HOL 明写 skipped（`tame_concl.hl:26`）；Lean 侧**无此名**，对应物是 `Graphs/TameClassification.lean:23`（已证，走 native_decide）。→ 映射成立但要注明「HOL 没证、我们证了」 |
| 最终入口 `Proof.lean` / `Main.lean` | `lean/Kepler/` | 不存在；唯一端到端入口是 `Kepler/Final.lean`。仅供读者定位 |
