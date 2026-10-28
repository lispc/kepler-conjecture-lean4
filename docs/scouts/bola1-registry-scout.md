# BO LA1 注册表侦察报告（bola1-scout）

- 车道：队列 §2 第 6 项（`就绪`，只读侦察）
- 基线：`4ff27ac1`（SF-57 应用②）
- 正本对照：`reference/flyspeck/text_formalization/local/appendix.hl`（1571 行）
- 快照：`/Users/zhangzhuo/c17_backup/lane_snapshots/bola1-scout/`
- 硬约束遵守：主仓零写入、零构建零锁、shell 仅 grep/rg/ls/wc/sed/awk + git 只读。

---

## 1. 注册表清点（98 项，逐条对齐）

| 侧 | 计数 | 构成 |
|---|---|---|
| HOL `appendix.hl` | 97 活跃 `let *_concl` + 1 `new_definition` | 96 个 grep 命中 − 1 条被源注释的 `CNFNTYP_concl`（:1435）；7 条为 JEJTVGB 族（:116/126/142/152/166/180/190），`JEJTVGB_assume_v39` 是唯一 `new_definition`（:195） |
| Lean `LocalAuto1.lean`（2,823 行） | 90 `theorem *_concl` + 8 Prop-valued `def` = **98** | 90 定理 ↔ HOL 97 lets 中非 JEJTVGB 的 90 条；8 defs = 6 分项 + `JEJTVGB_concl` + `JEJTVGB_assume_v39` |

对齐结论：**一一对应，零缺漏、零多余**（CNFNTYP 两侧都不搬；HOL `scs_data` 元组模式、
terminal-case 引文、`ear_cs` 等按头注约定跳过）。appendix.hl:1055-1084 的
QKNVMLB1/2/3 与 :1110/1115 的 EQTTNZI1/2、:710 的 HFNXPZA、:1500/1506 的
EFLYGAU/BJTDWPS 在 HOL corpus 中**只有 statement-let、没有 prove**（LocalConcl
2026-09-21 IV form audit 已裁，本次独立复核确认）。

HOL 证明正本不在 appendix.hl（其内仅 21 条机械引理挂 `prove_by_refinement`），
而是 `text_formalization/local/` 下**按定理名一文件**（ARDBZYE.hl 2,907 行、
HIJQAHA.hl 4,145 行、QKNVMLB.hl 10,699 行、IMJXPHR.hl 11,028 行……共 17.5 万行）。
逐条锚点与行数见 `bola1-dep-map.tsv`。

## 2. Lean 状态（双层真貌）

**第一层（LA1 本体）**：90 条 _concl 定理 = **8 真证 + 82 sorry**。
真证：`unadorned_MMs`(09-30)、`EQTTNZI1`(09-30)、`EQTTNZI2`(10-08)、
`HXHYTIJ`(09-30)、`MXQTIED`、`PEDSLGV1`(10-08)、`PEDSLGV2`(10-08)、
`YRTAFYH`(09-30)。88 个 sorry 行 = 82 定理体 + 6 非定理行（43/45/50 头注、
974/975 `main_nonlinear_terminal_v11 := sorry` 不透明 Prop 桩、2823 尾注）。

**第二层（`LocalConcl.lean`，1,615 行装配出口，任务书未点名但决定全局）**：
90/90 全部以 `<name>_discharged` 重暴露——
- **WIRE 62** = 16 classic + 46 assembly（(c) 类 38 + OTMTOTJ1-4 + ASSWPOW +
  DRNDRDV + CUXVZOZ/CJBDXXN 经注入 `p21_anchor`）；
- **HOLD 28** = (a) 无孪生 5、(b) 循环再出口 11、(c) 孪生形状差 7、(d) 形状差 5。
WIRE 可能故意带 sorryAx（债=孪生自身债，`#print axioms` 块为诚实口径）。

**双层合并后的真实分布**（本侦察口径）：
- 已闭或审计即净（W0）：LA1 本体 8 条 + WIRE 中孪生已证的 18 条左右
  （CNICGSF1-5、AUEAHEH、ZNLLLDL、VQFYMZY、BNAWVNH、RAWZDIB、MFKLVDK、
  RYPDIXT、GSXRFWM、DRNDRDV、EYYPQDW×3、YXIONXL1/3、XWITCCN2、AYQJTMD，
  taint 待 `#print axioms` 实证）≈ 26 条；
- 纯装配/重写链可闭（W1）：≈ 14 条；
- 中量真数学（W2）：≈ 12 条；
- mnt11 银行/巨型/无正本（W3+backlog）：≈ 30 条；
- 陈述修正（FIX，锁 10 条的解锁前提）：TBRMXRZ1（**注册表陈述从自身前提不可证**，
  孪生反向复合已证）、OEHDBEN（尾槽 scs3M1 vs scs3T1 异系）、QKNVMLB1/2/3
  （索引约定 (i+p)%s'.k vs i%s'.k+p%s.k，RULING 判孪生侧忠实）、
  VPWSHTO/XWNHLMD/SYNQIWN/CQAOQLR/YXIONXL2/LFLACKU 形状差。

## 3. 消费面（全树 grep，排除 .lake/.git/reference；文件数）

箭头族几乎全是**叶**：AQICLXA/FUNOUYH/ZNLLLDL/EFLYGAU/BJTDWPS/YXIONXL1/2 = 4，
箭头族主体 6–9。高消费件：`JEJTVGB_assume_v39` 53、`ZLZTHIC_concl` 53、
`MHAEYJN_concl` 50、`WKEIDFT_concl` 27、`TUAPYYU_concl` 26、`JEJTVGB_std_concl` 24、
`ODXLSTCv2_concl` 20、`PQCSXWG1/2_concl` 16。引用源=LA1 定义 + LocalConcl 出口 +
孪生模块 + docs/scouts；**没有 Text 层之外的代码消费者把箭头当父件用**——
唯一父链是 JEJTVGB_p16（已于 2026-10-25 翻除，债下沉为直源）。

## 4. M0 对账（「LA1 23 直源」）

`docs/e2e-reachability-map.tsv` LA1 23 行 =
1. **21 条 scs_arrow_v39 箭头**（parent=`JEJTVGB_p16`）：OTMTOTJ1-4、HIJQAHA、
   CNICGSF1-5、ARDBZYE、FYSSVEV、AUEAHEH、VQFYMZY、BNAWVNH、RAWZDIB、MFKLVDK、
   RYPDIXT、NWDGKXH、YOBIMPP、MIQMCSN —— 与 `JEJTVGB.hl:219`
   `mnt11 ==> JEJTVGB_assume_v39` 的 case_breakdown 消费面（OEHDBEN/OTMTOTJ×4/
   HIJQAHA/CNICGSF×5/FYSSVEV/ARDBZYE/AUEAHEH/VQFYMZY/BNAWVNH/RAWZDIB/MFKLVDK/
   RYPDIXT/NWDGKXH/YOBIMPP/MIQMCSN/BKOSSGE）**重合 21 条**（BKOSSGE 在 e2e 里
   经 LA16 而非 LA1 直源）。即：**这 21 条直源本体就是「直源」，不是谁的父件**——
   它们是 JEJTVGB 案例树对 8 个初始系统的终端剪枝。
2. `WKEIDFT_concl`（parent=`EQ_DIAG_STAB_6I1_03`）：唯一有下游父链的箭头。
3. `main_nonlinear_terminal_v11`（parent=`textCapstone`）：109 条 Main_estimate
   整章债，与 Assembly `nliMainNonlinearTerminalV11` 同根。

## 5. LA2x 机器勘察

**勘误**：`LocalAuto2.lean`（1,732 行）是 **localization 车道**（`local_fan` 族、
HYP 超图 kit、wedge/azim、`sol_local`/`tau_fun`/`tauVEF`、slicev/e/f、LDURDPN/
LFJCIXP），32 sorry（`nn_of_hyp_elim`/`ff_of_hyp_elim`/`hypermap_HYP_elim`/
`rho_rho_fun_p2` 等）。它与 LA1 **零 import 关系**，不承载 scs 记录展开机器；
它支撑的是 JEJTVGB 六分项（ConvexLocalFan/tauFun 一侧）的未来灌证，不是箭头族。

**真正的记录展开机器（已建成且大体已证）**：
- `ScsV39` 结构与 21 合取 `isScsV39`、BB*/MM* 塔、8+ Concrete 系统、FZIOTEF
  REF L/TRANS/UNION kit —— 全在 **LA1 本体且已证**（头注 21 条机械引理）。
- LA22 `is_scs_funlist_basic_p22` + `is_scs_adj_p22` csAdj 机（已证）；
- **LA29 `isScs_mkFunlist_p29`**（已证骨架）+ **16 条 `SCS_*_IS_SCS_p29` 全部
  DISCHARGED（2026-09-19）** + `SCS_*_BASIC/K/J` ×13/13/12 已证 +
  `STAB_5I1/5I2/5M3_SCS` 已证（LA20 `STAB_6I1_SCS` 方法推广）；
- LA20：10 条 `SCS_*_IS_SCS` + `STAB_6I1_SCS` + `EQ/SET_EQ_DIAG_STAB_6I1_02/03`
  已证；LA33：4I1/4I2/3T3/4M3-4M8 的 IS_SCS/BASIC/K/J + 全部 BB 桥 +
  `SCS_DIAG_SCS_*_{02,13}` 全表已证；
- 见证侧样板：LA1 `PEDSLGV1/2`（各约 100 行 MMs 非空见证）+
  `unadorned_MMs_concl`（MMs=BBprime2 定义性恒等）。

**箭头族仍在 sorried 的机器缺件**（波次的真实对象）：
LA20 `AQICLXA/FUNOUYH(FZIOTEF)/AQICLXA_SLICE/FUNOUYH_SLICE/SCS_6I1_BERAK_BY_CSTAB/
SCS_6I1_IMP_SCS_6T1`；LA24 `SCS_5I1/5I2/5I3/5M1_BERAK_BY_CSTAB`×4 +
`SET_EQ_DIAG_STAB_5I1/5I2/5M1`×3；LA29 `SCS_5M3_SLICE_{02,03,24}` +
`SCS_5M3_{02,03,24}_ARROW_*`×6；LA32 `MM_4M7/4M8_IMP_STAB/4M6`×8；
LA33 `SCS_4I2_IMP_SCS_4T1/SCS_4I1_IMP_SCS_4I2/SCS_4I1_SLICE_02/SCS_4M*_SLICE_13/
SCS_4I2_STRAIGHT*`。

## 6. 难度分级汇总（R 记录展开 / S 重写链 / M 真数学 / X 外部依赖）

| 级 | 条数(约) | 代表 |
|---|---|---|
| R（含已完成/W0 审计） | 26 | 8 条本体已证；CNICGSF1-5 与 LA33 六箭头孪生已证；DRNDRDV/EQTTNZI×2/unadorned_MMs/HXHYTIJ 定义性 |
| S | 14 | LKGRQUI(269 行)、AQICLXA/FUNOUYH(组装)、HIJQAHA(5M3 slice 组装)、SET_EQ_DIAG_STAB_5*×3、FEKTYIY、OIQKKEP、JLXFDMJ、ASSWPOW、WKEIDFT、CQAOQLR、PQCSXWG1 |
| M | 12+ | XWITCCN(8020 行 case tree)、JKQEWGV×3、AURSIPD、ARDBZYE、UAGHHBM、MHAEYJN、ZITHLQN/EAPGLE 胶合、MMs 见证类、HFNXPZA/EFLYGAU/BJTDWPS(无正本需自主建证) |
| X（mnt11 银行/巨型） | 30 | main_nonlinear_terminal_v11(109 条)、BERAK_5I*×4+6I1、RRCWNSJ/JCYFMRP/TFITSKC、CUXVZOZ/CJBDXXN(p21 引擎)、ZLZTHIC、ODXLSTCv2/IMJXPHRv2(11,028 行)/NUXCOEAv2、VASYYAU 族 6 循环条、NWDGKXH/YOBIMPP/MIQMCSN |
| FIX（陈述修正，锁 10+ 条） | 10 | TBRMXRZ1(不可证)、OEHDBEN(3M1/3T1)、QKNVMLB1/2/3(索引约定)、VPWSHTO/XWNHLMD/SYNQIWN/YXIONXL2/CQAOQLR/LFLACKU(形状差) |

**预判裁定**：「多为 scs 记录展开」**部分成立**——isScsV39/记录半侧 100% 机械化
且机器已建成；但箭头的 `MMs=∅` 空半侧（BERAK 族）与 MMs 见证半侧是真数学，
约 30 条落在 mnt11 银行阴影里。按条数：R+S ≈ 40/90（44%），M ≈ 20/90，
X ≈ 30/90。

## 7. 与 triage-w1 的交叉核对（显式一致/修正）

一致核心：**箭头族整体是装配级判断成立**——`scsArrowV39` 的 isScs 半侧由
`is_scs_funlist_basic_p22`/`isScs_mkFunlist_p29` 生成器批量覆盖，转移半侧由
FZIOTEF kit + BB 桥 + transferV39 覆盖；YXIONXL1 先例（LocalConcl:500）属实。
triage 的 W1-银行装配波与我的波 1 方向一致。

修正三点（记档价值）：
1. **22 条 B 中约 12 条其实已经闭了**：CNICGSF1-5（LA18 2026-09-19 已证）+
   AUEAHEH/ZNLLLDL/VQFYMZY/BNAWVNH/RAWZDIB/MFKLVDK/RYPDIXT/GSXRFWM（LA33 已证，
   LocalConcl 走 arrowSetRight 置换 shim）。这些的剩余工作只是 `#print axioms`
   审计 + 若 taint 来自已证输入则 e2e 直源立减 5（CNICGSF1-5）——不是待施工量。
2. **OTMTOTJ1-4/NWDGKXH/YOBIMPP/MIQMCSN 不是纯记录展开**：LA24 骨架的注释链
   `FZIOTEF_TRANS over SCS_5I*_BERAK_BY_CSTAB + …` 中 BERAK×4 是 mnt11 消费者
   （真数学/外部银行）；LA32 的 MM_4M7/4M8 链 8 条全 sorry。这 8 条的 R 半
   （SET_EQ_DIAG_STAB_5*×3，镜像已证 6I1 对）可先行，空半侧必须等波 3。
3. **transferV39 孪生真实规模小**：YXIONXL1/3 已闭，YXIONXL2 只差 k=3 缺口
   （p33 孪生多 `3 < s.k` 前提、p13 孪生错车道类型）——估 ≤200 行。
   **EAPGLE 表面 = ZITHLQN 装配**：HOL 原证 8 行胶合（AYQJTMD.hl:222，
   `MATCH_MP ZITHLQN + AYQJTMD + taustar 二分`），Lean 侧 LA25
   CASE_3/4/5/6+pro_cs/sqrt8/4_3 八件全已证、AYQJTMD_p27 已证，
   缺的只是 ZITHLQN 蕴含式装配（LA25 ZITHLQN_p25 目前是循环再出口）。

## 8. 波次方案（W0 审计 + 3 波 + FIX 并行线）

**W0（桌审，半天）**：对 62 条 WIRE 跑 `#print axioms`（或读构建产物 axioms），
锁定孪生已证且 taint 净的名单。预期战果：CNICGSF1-5 五条直源 cone-clean；
LA33 六箭头 + EYYPQDW×3 + YXIONXL1/3 + XWITCCN2 + AYQJTMD + DRNDRDV 归入已闭。
产出：修正版 e2e TSV 行。

**FIX 并行线（陈述修正，STATEMENT-FIX 闸）**：TBRMXRZ1（必改——现状不可证）、
OEHDBEN（尾槽 3T1↔3M1 二选一：改注册表或改孪生目标集）、QKNVMLB1/2/3
（按 2026-09-21 IV RULING 把注册表索引改成孪生忠实形）、VPWSHTO/XWNHLMD/
SYNQIWN/CQAOQLR/YXIONXL2/LFLACKU 形状差逐条裁决。FIX 是 10+ 条 HOLD 的解锁前提，
应随波 1 同窗提交。

**波 1（装配收尾波，R/S，预计 diff ≈ 1,200–1,800 行）**：
- 箭头清单：LKGRQUI → AQICLXA、FUNOUYH；SET_EQ_DIAG_STAB_5I1/5I2/5M1 →
  OTMTOTJ1-4 的 R 半；HIJQAHA（LA29 5M3 slice/arrow 6 件）；FEKTYIY、OIQKKEP、
  WKEIDFT、JLXFDMJ、BKOSSGE、ASSWPOW、PPBTYDQ、PQCSXWG1、LFLACKU、
  ZITHLQN 装配 → EAPGLE。
- 闸建议：`THM @LocalConcl` 全量 + `#print axioms LKGRQUI_discharged` 等
  无 sorryAx 抽样；e2e 直源 −10 ± 3。
- 风险：LKGRQUI_p27/AQICLXA 链的 `mkj` Prop 打包形状（LA20 注释已具名
  funlist 表匹配）；HIJQAHA 的 48 行 psort 表已在库（PSORT_5_EXPLICIT）。

**波 2（k≤6 认证链波，M，预计 ≈ 2,500–4,000 行）**：
- 箭头清单：XWITCCN master（LA36 IS_TRI_STABLE 8 条已证，剩 case 组装）、
  JKQEWGV1/2/3（LA23 CASE_4/5/6 组件需先灌）、AURSIPD、ARDBZYE/FYSSVEV
  （4I1→4I2 straight 链 + SCS_4I3_IS_SCS）、UAGHHBM（restriction-isScs fork）、
  MHAEYJN（LA37 孪生灌证）、QKNVMLB×3（FIX 后接 LA35 已证形）。
- 闸：`#print axioms` 全净抽样 + HIJQAHA/FYSSVEV 下游無回归。
- 风险：JKQEWGV 组件与 master 双 sorry（无重推导路线，需从 HOL 3307 行直译）；
  XWITCCN 8020 行是本波大头，建议按 k=3/4/5/6 拆四案并行。

**波 3（mnt11 银行波，X→M，规模=整章）**：
- 内容：`main_nonlinear_terminal_v11` 109 条 Main_estimate 本体（与 Assembly
  nliMainNonlinearTerminalV11 同根双闭）→ 释放 BERAK_5I1/5I2/5I3/5M1/6I1 →
  OTMTOTJ1-4 空半、OEHDBEN、RRCWNSJ/JCYFMRP/TFITSKC、CUXVZOZ/CJBDXXN
  （general_482_deformation_p21 引擎）、ZLZTHIC、ODXLSTCv2/IMJXPHRv2/NUXCOEAv2、
  NWDGKXH/YOBIMPP/MIQMCSN（MM_4M7/4M8 链）、VASYYAU 族 6 循环条真证、
  JEJTVGB 六分项灌证（消费 LA2 localization 车道，需先清其 32 sorry 中的
  hypermap elim 族）。
- 闸：e2e 直源 151→~110；`JEJTVGB` 主链 `mnt11 ⇒ JEJTVGB_assume_v39` 在 Lean
  侧重放（JEJTVGB.hl:219 的 case_breakdown 结构）。
- 风险：本波是 M1 备注里的「LA1 main_nonlinear_terminal_v11（109 条）」同一座山，
  不建议在本车道发起，应与 nli 车道合并立项。

**生成器/模板建议**（预判成立部分的施工法）：
1. `scsArrow.isScsTargets`：`∀ s ∈ S2, isScsV39 s` 由 `isScs_mkFunlist_p29`/
   `is_scs_adj_p22`/`is_scs_funlist_basic_p22` 三生成器覆盖——缺的只是
   SCS_4I3_IS_SCS 一件（LA33 直排 21 合取即可，样板 SCS_4I1 已证）。
2. `scsArrow.ofWitness`：`(h2 : ∀ s ∈ S2, isScsV39 s) → (∃ s ∈ S2, MMsV39 s ≠ ∅)
   → scsArrowV39 S1 S2`（3 行引理，一次入库全族复用）。
3. `scsArrow.ofEmpty`：对称的空半版（BBs 假设经 unadorned_MMs 降载）。
4. `stabDiagSetExpand k i j`：SET_EQ_DIAG_STAB 模板——6I1_02/03 已证对即模板，
   5I1/5I2/5M1 三件是逐字重实例化（波 1 的 R 主件）。
5. `arrowSetRight/Left` 已在 LocalConcl 私有；建议升公（LA33 七箭头的置换 shim
   全靠它）。

## 9. 未决问题

1. WIRE 62 条的逐条 sorryAx taint 无法离线判定（`#print axioms` 需构建环境，
   本车道零构建）——W0 桌审需一个能跑 `lake env lean` 的窗口或读 .lake 产物。
2. OEHDBEN 尾槽（scs3T1 vs scs3M1）与 QKNVMLB 索引约定的注册表改法，需
   registry-refactor 轮统一裁决（LA1 本轮冻结惯例是否延续）。
3. TBRMXRZ1 注册表陈述确认不可证（孪生反向复合）——按 STATEMENT-FIX 流程
   走还是留 HOLD 待 nli 车道，需编排者裁。
4. `main_nonlinear_terminal_v11` 的归属：本报告按任务书口径记为 LA1 注册表
   第 23 直源，但其施工主体属 nli/terminal 银行，波 3 只做接口。
5. LA2（localization 车道）32 sorry 中 `rho_rho_fun_p2`/`tauVEF_tau_fun` 是
   JEJTVGB 六分项灌证的前置——其规模评估不在本车道任务书内，未展开。
