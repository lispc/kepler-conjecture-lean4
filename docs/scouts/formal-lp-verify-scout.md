# formal-lp-verify-scout — A12 `lpArchiveCertificates`（43,078 终端 LP）× formal_lp `verify_all` 移植侦察报告（零改动只读侦察）

> 2026-10-12 侦察 lane 交付。对象：HOL `reference/flyspeck/formal_lp/`（129 文件，
> HL/ML 22,403 行 + C# LP-HL 求解器 + **404MB 二进制证书数据在库**）与 Lean
> `lean/Kepler/Text/LP/`（177 模块）+ `lean/Kepler/LP/`（ColMajor checker +
> PilotCM 模板）+ `pipeline/lp/` 工具链。所有 file:line 经 grep/sed 实测核对；
> 纪律：零 .lean 改动、零 git 写操作、零 lake build；只跑了两个只读 Python
> 探针（/tmp/lp_probe.py，单进程，读 `hard_2.dat`/`easy_1.dat` 统计证书内容，
> 经已提交读器 `pipeline/lp/parse_lpcert.py`）。
>
> **核心结论先行**：
> ① **基线比立项简报假设的先进得多——A12 已不是"移植起步"而是"四缺口收尾"**：
> T2 波（2026-10-08）已落树 43,078 记录的完整骨架层（177 模块：`LPIds` 44,528 行
> 记录清单 + 174 个 `LPLeaf*` 文件恰 43,078 枚 `lpT<id>` 叶 + `LPAll` 量化装配，
> 注册表三件**零 sorry**、43,078 枚 sorry 全在叶上）；内核 checker
> `Kepler.LP.ColMajor`（928 行，零 sorry 零 native_decide）+ 产物模块模板
> `PilotCM204880136538`（Data+Assembly 五定理形）+ 三件工具链
> （`parse_lpcert.py`/`socert.py`/`gen_lp_skeleton.py`）全在库。
> ② **Flyspeck 侧证书数据 404MB 就在本仓**（`formal_lp/glpk/binary/`，easy 24 +
> hard 15 + hard_7.tar.gz；实点校验 hard_2=1 图 17 终端、easy_1=424 图 1000 终端）。
> DECISIONS 2026-09-28 所列丢失物是**旧机 Lean 侧重跑产物**（`~/lprun-persist`
> 账本/产物 + 6,925 任务账本），**不是** Flyspeck 二进制证书——重算 = 从在库
> .dat 重建终端 LP → SoPlex 精确对偶 → Lean 产物模块，无需重建 Flyspeck 证书。
> ③ **剩余缺口恰四件**：(a) 189 条 infeasible 通道——`LpTerminalInfeasibleCertified
> := True` 是在案占位（LPCert.lean:73），需 Farkas 形 checker（Lean 新机制，
> Mac 可设计+玩具验证）；(b) 记录级钉定——`LpTerminalCertified` 对 id 不敏感
> （LPCert.lean:52-59 在案保真缺口），量产闭合前必须落"id ↔ 自己的重跑产物模块"
> 恒等钉定（schema/generator 工作，Mac 可做）；(c) **覆盖桥**——per-record 总量
> → Assembly 冻结签名"每图 ¬Contravening"的语义移植（HOL `prove_flyspeck_lp.hl`
> split-tree 结构半边 + 约 90–150 个实际使用的不等式族线性化，Lean 预估
> 2,500–5,000 行，结构半边 Mac 可开工）；(d) **42,889 叶闭合数据波**——强机器
> 重跑，预估 3,000–8,000 核时，是 A12 的主体成本与三重绑定所在。
> ④ **编译时间是头号风险**：PilotCM 实测 ~650 s/单核（915 变量×3882 行×8056 非零，
> 旧机慢核，PILOTCM_PERF_NOTES.md:19）；终端记录 LP 尺寸**双峰**（抽样 easy/root
> 终端 ~44 行×~24 界 vs 硬图试点 ~3900 行），43,078 × [30 s, 650 s] ≈
> **[360, 7,800] 核时**——Mac 只配做"试点切片校准"，全量必须强机器且要先定
> 灌装顺序（小记录先行摊平风险）。
> ⑤ **建议立项"第一批（Mac-now, A12-C1）"**：infeasible 通道 checker + 钉定
> schema + 每图 split-tree 数据 schema + 最小 root 记录 3 条端到端试点
> （顺带把单条编译秒数从"区间猜测"变成"实测"）。数据波与覆盖桥主体不抢跑。

---

## §1 HOL 侧 verify_all 解剖

### 1.1 入口与数据流（`formal_lp/hypermap/verify_all.hl`，129 行）

```
Verify_all.verify_all [] None            (:116-119) = verify_hard ++ verify_easy
  ├─ init_ineqs() (:78-84)               装载不等式库（head+body+process_raw_ineqs）
  ├─ 逐文件扫 glpk/binary/{hard,easy}_*  (:12-27；.gz 自动 tar 解包, lp_certificate.hl:124-137)
  ├─ 每文件 read_lp_certificates         OCaml Marshal 读 lp_certificate list
  └─ 每证书 verify_lp_certificate        (:55 → prove_flyspeck_lp.hl:1042)
test_result result (:121-127)            对账：concl 并集须全是 `contravening V ==> F`，
                                         hyp 并集（去 iso）须恰为 [lp_ineqs; lp_main_estimate]
```

README.txt:66-67：全量 15 小时（2005 年 Mac mini 2GHz）。`opt_good_table` 参数
是 `good_list` 定理缓存（:50-55），可选、None 即重算。

### 1.2 证书 schema 与实测内容（`hypermap/main/lp_certificate.hl`:3-35）

```ocaml
constraint_type = string * int list * int64 list   (* 不等式族名, 实例下标, 整数乘子 *)
terminal_case = { precision:int; infeasible:bool; constraints; target_variables; variable_bounds }
lp_certificate_case = Lp_terminal of terminal_case | Lp_split of split_case * tree
lp_certificate = { hypermap_string : string;  root_case }   (* hypermap_string 编码图 L *)
```

探针实测（/tmp/lp_probe.py，经 parse_lpcert.py 读器）：

| 文件 | 图 | 终端 | infeas | precision | 行数/终端 | 界/终端 | 最大下标串 | split 型 | 族名数 |
|---|---|---|---|---|---|---|---|---|---|
| hard_2.dat | 1 | 17 | 0 | {3:1, 4:15, 5:1} | 均值 47.0 / 最大 52 | 均值 23.6 | 43 | 仅 quad | 73 |
| easy_1.dat | 424 | 1000 | 1 | {3:493, 4:488, 5:17, 6:2} | 均值 43.5 / 最大 60 | 均值 23.2 | 64 | 仅 quad | 93 |

高频族名（两文件并集 top）：`y1..y6_def(_neg)`、`azim_sum(_neg)`、`rhazim_sum`、
`sol_sum3_neg`、`tau_sum3_neg`、`ln_def`、`rho_def`、`edge_sym(_neg)`、`RHA`、
`ineq107/108/109/111/112/115`…——全库并集估计 **90–150 个族**（HOL 库注册更多，
证书只引用子集；全量精确清单可在 Mac 用 parse_lpcert.py 一夜扫出）。

### 1.3 单终端验证语义——精确整数 Farkas 机器（`prove_flyspeck_lp.hl`:287-348）

`prove_flyspeck_lp_step1 hyp_list hyp_set hyp_fun std_flag precision infeasible constraints target_variables variable_bounds`：

1. `precision_constant = 10^precision`（p∈3..7，实测分布见 1.2）；
2. 每条 constraint `(name, indices, c)`：`get_ineqs`（:263-277）按族名+精度取
   族定理 → 实例化到 `L`（hypermap list）→ 按下标 `select_all` 选实例 →
   `simplify_ineq`/`prove_conditions` 把非线性项化成 `ye/yn` 变量的线性式并消去
   平凡条件 → `transform_le_ineq` 乘 int64 乘子（精确 real-int conv）；
3. 全部 fold-add（`lin_f_add_conv`，合并同类项系数精确相加）；
   非 infeasible 时再叠加 `lnsum_ineqs[p]`（:43-53，预制的 `&12 <= scriptL` 链）；
4. variable_bounds + target_variables 进变量表，`add_cancel_step` 逐变量消去
   （`c·x <= bound` 与主和式对消）；
5. 终态 `lin_f [] <= --&n` 且 `NUM_EQ0_HASH_CONV` 证 `n ≠ 0` → 矛盾
   （FINAL_INEQ :40-41）。

**精确性口径**：全程 HOL 有理数/整数精确算术（`more_arith/arith_int.hl` 275 行的
`my_real_int_{neg,add,sub,mul}_conv`、`REAL_RAT_*_CONV`；`lin_f.hl` 112 行的
`lin_f` 折叠定义），**无浮点**；int64 系数 × 10^p 缩放使全部数据整型化。
单条 verify 与 verify_all 的关系：verify_all 纯粹是"文件循环 × verify_lp_certificate
+ 对账"，无独立语义。

### 1.4 split 树机制（:864-1038，A12 覆盖桥的移植对象）

10 种 split 型 `tri/quad/pent/hex/edge/218/236/mid/high/add_big`（:880-902）。
每型的形态：**子情形各证同款结论 + 二分/多分引理合取**：
- 二分型（`edge/218/236`）：`REAL_LE_TOTAL` 实例（如 :521-523 `#2.25 <= ye(d) \/ ye(d) <= #2.25`）；
- 多分型：`split4_lemma`（:483-490，quad 对角线 5 析取）、`split5_lemma`（:493-507，
  pent 11 析取）、`split6_lemma`（:509-518，hex 7 析取）——纯序算术，ARITH_TAC 闭合；
- 合取子：`(A==>C) /\ (B==>C) ==> (A\/B==>C)`（:448-451）；
- 每型的附加引擎：`gen_triangle_ineqs`（:747，三角和 #6.25 对称化 + extra 小侧
  不等式）、`gen_mid/high/add_big`（:792/:823/:775，节点不等式补充）、ye 对称化
  `gen_ye_sym_ineqs`（:589）；quad/pent/hex 还需 split 后 `lp_cond` 重算
  （`split_lp_conditions` :717）与 `lp_tau` 输运（`tau_split4/5_one/5_two/6` :552-554）。
- 抽样数据里只见 `quad`（两文件），但 hard 大图（hard_1/5/7 未探）预计含 pent/hex/tri；
  HOL 机制按 10 型全备移植。

### 1.5 依赖基础设施与 A12 移植边界（谁进 A12、谁走接口假设）

| HOL 件 | 行数 | 归属 |
|---|---|---|
| verify_all.hl | 129 | A12（Lean 侧已由注册表+LPAll 替代大半） |
| main/prove_flyspeck_lp.hl | 1,066 | **A12 覆盖桥主体**（结构半边 + Farkas 语义） |
| main/lp_certificate.hl | 158 | 纯 schema（parse_lpcert.py 已镜像） |
| more_arith/{lin_f,arith_int,prove_lp} | 827 | A12（Lean 对应物 = ColMajor lin 机器，大部已替代） |
| hypermap/computations/{list_hypermap_computations,list_conversions2,informal_computations,more_theory} | ~3,290 | A12 覆盖桥消费（Lean 侧 TameSpine W0 keystone + Hypermap 已有底座） |
| hypermap/ssreflect/*-compiled | 3,809 | 同上（list hypermap/iso 理论） |
| ineqs/lp_ineqs*.hl + lp_head/body/gen/approx/defs | ~2,460 | **不进 A12**：其证明 discharge 成 `lp_ineqs` 假设（A11/共享线） |
| ineqs/lp_{ineqs_proofs,ineqs_proofs2,main_estimate}-compiled | 6,737 | 同上（A11 `LpIneqs`/`lp_main_estimate` 接口的 HL 原像） |
| glpk/*（build 侧）+ LP-HL/（C# 求解器） | ~2,600 + C# | 不移植：重跑走 SoPlex（socert.py 路线已打通） |

关键口径：**A12 不需要移植不等式数据库的证明**。HOL 定理形状
`lp_ineqs, lp_main_estimate, iso … |- contravening V ==> F`（README.txt:78-91）
里前两项是 DISCH 假设，Lean 冻结签名（Assembly.lean:1018-1021）逐字同构，由
`LpIneqs`（Assembly.lean:197 `:= AllCertified idsLpIneqs`，A11 线）与
`lp_main_estimate`（LocalAuto16.lean:185 `:= JEJTVGB_concl`）供给我方。
但 A12 **需要**移植"族名 → 线性式实例"的*生成*语义（`lp_gen_ineqs`/`lp_ineqs_defs`
层），即每个实际使用族在 `L` 上的一条 Lean 线性化定理——这是覆盖桥里逐族计数
的主体。

## §2 Lean 侧消费形状（全部实测）

### 2.1 语义核心（`lean/Kepler/Text/LP/LPCert.lean`，85 行，手写）

```lean
def LpTerminalCertified (_id : String) : Prop :=          -- :60-63
  ∃ (lp : LPCM) (d : ℕ) (Y : List Int) (D : ℕ) (G : Int),
    checkDualCMTF lp d (ITree.ofList Y d) Y D G = true ∧ (G : Int) < 12 * (D : Int)
def LpTerminalInfeasibleCertified (_id : String) : Prop := True   -- :73 占位
def AllLpTerminalCertified (ids : List String) : Prop := ∀ id ∈ ids, …  -- :78-79
```
见证 = 重跑产物模块的五元组 `(lp, d, Y, D, G)`；`checkDualCMTF` 是
`Kepler.LP.ColMajor`（928 行）的内核 Bool checker（`checkDualCMTBase` :338 + 
`checkDualCMTCols` :348；`checkDualCMTF_sound` 桥到有理语义"一切可行点
cmObj ≤ G/D"）。文件头 :52-59 诚实记录两 NEEDS：①记录级钉定；②12 阈
Flyspeck 终端语义与 `LpIneqs`/覆盖桥。

### 2.2 注册表承诺（LPIds/LPLeaf/LPAll，机器生成勿手改）

- `LPIds.lean`（44,528 行）：43,078 条 id 字符串清单，174 个 chunk def（250 条/chunk）
  + 逐 chunk `length` 定理 + 段总长定理（`lpInfeasIds=189`、`lpRootIds=19,237`、
  `lpEasyIds=4,403`、`lpHardIds=19,290`、`lpTerminalBoundIds=42,889`、
  `lpTerminalIds=43,078`，文件尾 norm_num 真证）。
- `LPLeaf{Infeas00,Root00-76,Easy00-17,Hard00-77}`（174 文件，各 ~1,769 行）：
  `grep -h "^theorem lpT" LPLeaf*.lean | wc -l` = **43,078**（实测）；每叶 5-7 行
  open `sorry` + NEEDS 注记（LPLeafEasy00.lean:18-21 样例）。
- `LPAll.lean`（565 行）：`lpAllInfeas/lpAllRoot/lpAllEasy/lpAllHard/lpTerminalBoundAll`
  五个总量定理，真证明（rcases 分发 + exact 逐 chunk 转发；文件内零 sorry）。
- 生成器 `lean/scripts/gen_lp_skeleton.py`：确定性重导 + 盘点基线 43,078 校验
  （漂移退出码 2），chunk/文件/分发单元 1:1:1。

### 2.3 数据灌入接口面（回答"一条记录 = 什么"）

**一条记录 = 一个产物模块 + 一次叶改写**（非 eval 化、非 native_decide）：
1. `socert.py --col-major` 从终端 LP（SoPlex 精确模式解出）发射
   `Kepler.LP.T<id 消毒>/`：`Data.lean`（LPCM 字面量 + certY/certD/certG）
   + `Assembly.lean`（58 行五定理：`cols_check := decide`、`dual_check`、
   `bound`（一切有理可行点 ≤ γ）、`gamma_lt := decide`、`bound_lt`（< 12））
   ——PilotCM204880136538 在库样板（`lean/Kepler/LP/PilotCM204880136538/`）；
2. 叶闭合 = `LPLeaf*.lean` 中该叶 `sorry` → `exact`（转发产物模块的
   bound/bound_lt 与五元组见证）。模板见 PilotCM Assembly.lean:24-57。
3. 编译模型：两个独立内核 `decide`（base + cols），字面量阐明是每 LP 固定成本。

### 2.4 接口消费位（`lean/Kepler/Assembly.lean`）

- 冻结接口 `lpArchiveCertificates`（:1018-1021）与具名债点
  `lpArchiveCertificatesDebt`（:995-1011，同签名），T2 波已把证明体重接线。
  签名 `(hlpineq : LpIneqs) (hmain : lp_main_estimate) → ∀ V hfan L,
  L ∈ tameArchiveLists → FanHypermapIsoList V hfan L → ¬Contravening V`
  ——与 HOL `test_result` 对账形状（1.1）逐字同构。
- 上游消费：`linearProgrammingResults`（:1053-1056）已接线，
  `TextCapstone`（:1062-）消费之。A12 收口即该链自动真化。
- 已有可复用底座：`IsHypermapOfList`/`FanHypermapIsoList`（Assembly.lean:116-135）、
  `isHypermapOfList_hypermapOfList` keystone（`Text/TameSpine/Keystone.lean:117-124`
  已真证，W0）、`tameArchiveLists` + `goodListArchive`（Assembly.lean:1185）。
- 先例对照：A11 的 CertTM 线同形（`Interval/CertTM.lean` 5,507 行：内核可计算
  checker + 数据证书 + 零 sorry 零 native_decide），A12 的 ColMajor/PilotCM
  即其 LP 对应物，形态已冻结。

## §3 缺口地图（从"强机器重跑"到"Lean 全绿"）

| # | 环节 | 性质 | 量级 | 时机 |
|---|---|---|---|---|
| G1 | **189 infeasible 通道**：Farkas 形 checker（`colMajor` 加不可行性支：整数对偶射线 s≥0、Aᵀs≤0、bᵀs>0 之类）+ `LpTerminalInfeasibleCertified` 真语义替换 + 产物发射格式 | 必移植 Lean 代码（新机制） | 150–400 行 | **Mac 现在就能做**（玩具 LP 验证；189 条闭合需数据） |
| G2 | **记录级钉定**：产物模块 ↔ 记录 id 恒等（"只准用自己记录的模块转发"），防 id 无关性静默退化 | schema/generator（Lean 形 + 脚本） | 脚本 + 每叶 1 行钉定 | **Mac 现在就能做**（schema 冻结必须在数据波前） |
| G3 | **每图 split-tree 数据 schema**：478 张多终端图的树结构（split_type/face/子叶 id）+ 19,237 root 恒等图映射，进 Lean 数据模块（gen_lp_skeleton.py 扩展或新 gen_lp_trees.py） | 纯数据 + 可脚本生成 | 数据 ~478 树 + 生成器 ~200 行 | **Mac 现在就能做**（parse_lpcert.py 已能读树，--tree 实测可用） |
| G4 | **覆盖桥结构半边**：split4/5/6 + 二分族 + combine + ye 对称 + lnsum/tau 链的 Lean 定理库（HOL §1.4 机制直译；tau 侧消费 TameLp/lp_main_estimate 现状） | 必移植 Lean 代码 | 800–1,800 行 | **Mac 现在能开工**（split 引理是纯序算术；tau 运输件依赖 TameLp 共享件状态） |
| G5 | **覆盖桥族线性化**：93–150 个实际使用族的"实例 = ye/yn 线性式"Lean 定理（HOL lp_gen_ineqs/lp_ineqs_defs 层对应物） | 必移植 Lean 代码 | 1,200–3,000 行（按族均摊 8–20 行） | **有数据才能收口**（族清单全量扫描需读 404MB；陈述面依赖 A11 `LpIneqs` 语句形态）——族清单扫描本身 Mac 一夜可做 |
| G6 | **42,889 bound 叶闭合**：终端 LP 重建（.dat 终端数据 + 族实例 → .lp）→ SoPlex 精确对偶 → 产物模块 → 叶转发 | 纯数据 + 可脚本生成（数据本体） | 42,889 模块；**3,000–8,000 核时** | **强机器才能做**（Mac 仅试点切片） |
| G7 | **189 infeasible 闭合**：同 G6 但走 G1 通道 | 纯数据 | 189 模块 | 强机器（量小，随 G6 首批） |
| G8 | **总装配**：per-graph 覆盖定理（G3+G4+G5+G6 组装，478 张逐图 + root 逐图批量）→ `lpArchiveCertificatesDebt` 收口 | 必移植 Lean 代码 | 300–800 行 + 逐图数据行 | 有数据才能收口（结构可先写） |
| G9 | 附带对账工具：Lean 侧 `test_result` 等价物（总量 concl/hyp 对账审计脚本） | 可脚本生成 | ~100 行脚本 | Mac 现在就能做 |

依赖序：G2/G3（schema 冻结）→ G1/G4（Mac 可并行）→ G5（等 A11 语句面 + 族清单）→
G6/G7（强机器）→ G8（收口）。**G2 是 G6 的前置闸**：钉定 schema 不先冻结，
43,078 叶闭合后返工代价最大。

## §4 量级估计

**HOL 侧**：A12 真正的移植对象（覆盖桥 + 语义）≈ `prove_flyspeck_lp.hl` 1,066 +
computations 层按需 ~1,500 + 族生成层 ~1,000 ≈ **3,000–3,500 HL 行**（不等式证明库
6,737 行走 A11 接口假设，不重付）。数据侧 404MB 二进制 = 43,078 终端 + 478 树。

**Lean 侧**（先例折算：conforming 1.47x 展开、TameList ~1x；本块数据密集，
代码部分按 1.2–1.6x）：
- G1+G4+G5+G8（代码）≈ **2,500–6,000 行**，中值 ~4,000；
- G2/G3/G9（脚本+数据模块）≈ 脚本 500 行 + 树数据模块 ~2,000–4,000 行（机器生成，不计人写）；
- 叶闭合 43,078 × (~30 行产物模块/叶，机器生成不计人写) + 174 文件叶改写（机器生成）。
**批数**（对齐 ~1,000 行/批、250 条/chunk 先例）：代码 4–6 批；
数据波 174 chunk（建议按 chunk 灌装，与现存叶文件 1:1，天然对账单元）。

**算力**（本节是 A12 与一切先例的分野）：PilotCM 实测 ~650 s/单核（915×3882，
旧机慢核 ~360 pops/s 基准，PILOTCM_PERF_NOTES.md:19-39）；抽样终端 LP ~44 行
（easy_1/hard_2），尺寸谱双峰。43,078 × [30 s, 650 s] ≈ **[360, 7,800] 核时**；
即便 M3 Pro 单核按 2–3 倍快折算，Mac 全量也是数百小时级 wall（且违反 -J 6 政策）
——维持 deferred-compute 判定正确。Graphs CertShards 先例（30–2,100 s/片）与本
估计同量级，不冲突。

## §5 风险清单

1. **编译时间（最高）**：§4 区间上下差 20 倍，主要不确定项是 root 批 19,237 条
   小 LP 的单条编译秒数（无实测点）。缓解 = 第一批 3 条最小 root 端到端试点把
   区间钉窄；灌装顺序按"先小后大"（root → easy → hard chunk 序天然近似）。
2. **钉定滞后返工**：`LpTerminalCertified` 的 id 无关性使"跨记录借见证"在
   类型层合法（LPCert.lean:52-59 在案）。若数据波先于 G2 冻结开跑，返工面 =
   43,078 叶。缓解 = G2 列为数据波前置闸；钉定形式建议"产物模块内自证
   `recordId = "<id>"` 字面量 + 叶转发时 `decide` 校验"。
3. **数值口径**：HOL 用 int64×10^p 精确有理（p∈3..7）；Lean 侧 D=lcm 整数化。
   两边同为精确算术、无浮点，**无舍入风险**；真风险是**重跑 LP ≠ HOL 终端 LP**
   （行缩放/变量排序/`>=` 行翻转不一致导致证书验的是另一个 LP）。缓解 =
   产物模块携带 LPCM 本体（现设计已如此），G5 的族线性化定理把"LPCM = 该记录
   族实例 LP"钉成定理面；socert 已内置强对偶不受信校验（README 步骤 4）。
4. **infeasible 占位假绿**：`:= True` 占位若被"总量已证"口径误读即静默退化
   （LPCert.lean:65-72 已写退化防线）。G1 落地前，189 条不得计入任何
   "已证"汇报口径。
5. **覆盖桥共享件竞争**：G4 的 tau 运输件（lp_tau_split4/5/6 对应物）与
   TameLp 章的 `sum_tauVEF_upper_bound`/KCBLRQC 群（TameLp.lean:2018-2035 备忘）
   同源；若 TameLp lane 尚未铺到，A12 需私件化再换正——排期时与 A9/TameLp
   时窗对齐，防两 lane 重复移植。
6. **split 型覆盖不确定**：抽样仅见 quad；pent/hex/tri 等型在 hard_1/5/7 的
   出现频率未测（404MB 全扫一夜可测）。若某型终端占比高，G4 对应件优先级上调。
7. **hard_7.tar.gz 等大文件的工具链内存**：parse_lpcert.py 全量扫描 404MB 需要
   分文件+回收（探针实测单文件 OK；hard_1=37MB 未测）。纯工程风险。

## §6 立项建议

**建议拆 3 波立项；第一批（A12-C1）Mac 现在即可动工。**

- **A12-C1（Mac-now，schema/checker 冻结批，~800–1,500 行 + 脚本）**：
  ① G1 infeasible 通道（checker + 真语义 + 玩具验证）；
  ② G2 记录级钉定 schema 冻结（生成器 + 1 叶样例改写演示）；
  ③ G3 每图树数据 schema + 生成器（先出 478 树的 Lean 数据模块）；
  ④ **3 条最小 root 记录端到端试点**（.dat → 终端 LP 重建 → socert →
  产物模块 → 叶闭合），验收锚点 = 3 叶真闭合 + 单条编译秒数实测表。
  验收总锚：`#print axioms` 过标准三、盘点基线 43,078 不变、零手改叶。
- **A12-C2（覆盖桥批，1,500–3,000 行，Mac 可开工、随 A11 语句面收口）**：
  G4 split 机制库 + G5 族线性化（先做族清单全量扫描定序）+ G9 对账脚本。
  验收锚 = 对 1 张多终端样例图（hard_2 的 17 终端图，数据最小）走通
  "17 叶证书 → 每图 ¬Contravening"全链（数据可先用玩具/占位见证）。
- **A12-C3（数据波，强机器，174 chunk）**：G6+G7 灌装 + G8 总装配收口。
  验收锚 = 逐 chunk 叶闭合 + `lpTerminalBoundAll` 前提全真 +
  `lpArchiveCertificatesDebt` 改接到 C2 组装件。

**第一批现在能否在 Mac 上动工：能**——C1 四件全部不依赖强机器数据；
唯一外部依赖是 A11 的 `LpIneqs` 语句形态（只影响 C2 的 G5，不影响 C1）。

---

### 立项裁决请求

**建议：立项（先立 A12-C1 第一批，Mac-now）。** 一句话理由：骨架/checker/工具链
三件套已在库且超预期完整，剩余缺口里真正昂贵的是"等强机器的数据波"与"Mac 可先行的
覆盖桥+钉定 schema"，C1 以 ~1 千行级投入同时冻结钉定闸门、补齐 infeasible 通道、
并把 43,078 条的编译时间从 20 倍宽的区间钉到实测——是全项目最大单块债的最低成本去风险步。

---

关键文件：`reference/flyspeck/formal_lp/hypermap/verify_all.hl`（:116 入口、:55 单证书、
:121 对账）、`reference/flyspeck/formal_lp/hypermap/main/prove_flyspeck_lp.hl`
（:287 Farkas 机器、:864-1038 split 机制、:1042 verify_lp_certificate）、
`reference/flyspeck/formal_lp/hypermap/main/lp_certificate.hl`（:3-35 schema）、
`reference/flyspeck/formal_lp/glpk/binary/`（404MB 数据在库）、
`lean/Kepler/Text/LP/LPCert.lean`（:60 语义、:73 占位、:52-59 缺口在案）、
`lean/Kepler/Text/LP/LPIds.lean`（44,528 行清单+长度定理）、
`lean/Kepler/Text/LP/LPAll.lean`（:190-560 五总量）、
`lean/Kepler/LP/ColMajor.lean`（:91 LPCM、:338/:348/:354 checker）、
`lean/Kepler/LP/PilotCM204880136538/{Data,Assembly}.lean`（产物模板）、
`pipeline/lp/{parse_lpcert,socert}.py` + `lean/scripts/gen_lp_skeleton.py`（工具链）、
`pipeline/lp/PILOTCM_PERF_NOTES.md`（:19-39 编译实测）、
`lean/Kepler/Assembly.lean`（:995-1021 债点与冻结签名、:1053 上游接线）、
`DECISIONS.md`:67-98（丢失物清单与挂起政策）。
