# PACKING 章前提树材料单（只读侦察，2026-10-08）

> 从 `PACKING_CHAPTER_MAIN_CONCLUSION`（PA25 = PackingAuto25.lean:3692）出发
> 向下的全前提树 + textCapstone 其余消费件状态。标注：✅ 真证（本体）/
> 🟡 在飞（哪条线）/ ⬜ 缺口（sorry，含量级）。
> 盘面基准：PA23 余 1 笔（pivot ¬nullSet 支 :5072，终章波在飞）；PA24 余 2 笔
> （:1118、:3587）；PA20 gammaX 双巨余 2 笔（:1478、:1506，Wave V/E/M）。
> 注意：PA23:5040 附近"¬nullSet 支仍 1 处结构化 sorry"的注记准确；
> `grutoti_volD_pos` 上方"STILL sorry"注释已陈旧（体是一行 `volumeConicCapPos`，真证）。

## 1. PACKING_CHAPTER_MAIN_CONCLUSION（PA25:3692）✅真证（条件式）

```
陈述：(hkc : ¬keplerConjecture) (hnl : pack_nonlinear_non_ox3q1h) (hox : ox3q1hP25) :
  ∃ V, Packing V ∧ V ⊆ ballAnnulus ∧ ¬localAnnulusInequality V
证明体（3695-3704，HOL Oxlzlez 装配 verbatim）：
  refine RDWKARC_concl hkc ?_ ?_
  · OXLZLEZ 臂：intro V hp hs; exact OXLZLEZ V hnl hox hp hs
  · TSKAJXY 臂：intro V X hs hp hm hcrit; exact TSKAJXY V X hnl hs hp hm hcrit
```

前提树（自上而下，递归到叶）：

```
PACKING_CHAPTER_MAIN_CONCLUSION  PA25:3692  ✅
│
├─ hnl : pack_nonlinear_non_ox3q1h（bank 假设，PA21:404 def，非 sorry）
│   └─ = cell3_bank ∧ tsk_bank ∧ grk_bank ∧ pack_nonlinear_rest
│       └─ pack_nonlinear_rest  PA21:396  ⬜ def-sorry（Merge_ineq 81 条 registry
│          的 62 条余叶，PLACEHOLDER(G4)；三切片 cell3/tsk/grk 已结构化直通）
│
├─ hox : ox3q1hP25  PA25:89  ⬜ def-sorry（Oxl_def.hl 外部锚：cc_v11 实模型
│      n=4 象限案认证不等式；G4 证书侧，PA3 内只有 inline 形）
│
├─ RDWKARC_concl  PA2:5199-5305  ✅（全内联真证：反例解包 + UPFZBZM/JGXZYGW
│   │   密度矛盾 + witness 平移重编 sum；私件 6 件 packingTrans_p2/
│   │   radVPair_p2/radVTransEq_p2/hlPairAdd_p2/setSumCongr_p2/setSumImage_p2 全 ✅）
│   ├─ UPFZBZM_concl  PA2:5048  ⬜ sorry 桩
│   │   └─ 孪生 PA19.UPFZBZM  PA19:915  ✅真证可移植（2 行 witness 装配；
│   │       上游 FCC_COMPATABILITY_FUNC + NEGLIGIBLE_FUNC 均 PA19 真证）
│   │       └─ NEGLIGIBLE_FUNC → PA16.KIZHLTL4 (PA16:1424) ✅体
│   │           └─ 吃 PA2.GRUTOTI1_concl 桩 (PA2:5368) 🟡
│   │              └─ PA23.GRUTOTI (PA23:5101) 🟡终章波：桥体纯组装 ✅，
│   │                 唯一余债 = grutoti_pivot ¬nullSet 支 (PA23:5072) ⬜
│   │                 （hl/√2-barV ← PA15:578 HL_LE_SQRT2_IMP_BARV_1 sorry
│   │                  为传递债；AJRIPQN (PA17) 为上游债，不在临界路径）
│   └─ JGXZYGW_KY_p2  PA2:5180  ✅ → jgxzygw_p（PackingJGXZYGW 新叶模块）
│       ✅已 bank（#print axioms 仅标准三）
│
├─ OXLZLEZ  PA25:3674-3683  ✅（反例 → CELL_CLUSTER_ESTIMATE_PROPS 压缩模型
│   │   见证 → GRHIDFA_concl 出 False）
│   ├─ CELL_CLUSTER_ESTIMATE_PROPS  PA25:3657  ⬜ sorry【几何→压缩模型见证巨】
│   │   └─ 预定路线：cc_real_model_data  PA25:3647  ⬜ sorry
│   │       ├─ cc_real_data / cc_card_data  PA25:2140/2134  ✅（rfl 投影）
│   │       ├─ wedge 链（PA25 1500-3000 区块 sorried 簇）：
│   │       │   REUHADY 本地副本  PA25:1074  ⬜（PA24 lane 孪生）🟡
│   │       │   LEAF_RANK_REUHADY  PA25:1581  ⬜ 🟡（卡 REUHADY）
│   │       │   LEAF_RANK_BIJ  PA25:1590  ⬜
│   │       │   LEAF_RANK_GRUTOTI  PA25:1603  ⬜ 🟡（经 REUHADY 吃 GRUTOTI）
│   │       │   LEAF_RANK_GG_SUM  PA25:1614  ⬜
│   │       │   c_4_azim_mcell_dih_y  PA25:2484  ⬜ 🟡
│   │       │   real_model_sum_azim  PA25:2906  ⬜ 🟡
│   │       │   CELL_CLUSTER_N_LE_1  PA25:2200  ⬜
│   │       │   （另卡 PA18.cc_pe_exists PA18:148 / cc_uh_exists PA18:163，
│   │       │     均 ⬜——leaf_cell.hl YBZFUPO/NWVRFMF 两根）
│   │       └─ real_model_* 区间 bank（txq/tew/008/gamma*/pema/... ~40 件 ⬜，
│   │           大多卡外部认证锚 Flyspeck_constants.calc / G4；gammaX_gamma4fgcy_ALT
│   │           PA25:2722、mcell3_gammaX_gamma3f PA25:2942 为 PA20 双巨的
│   │           PA25 本地 wedge 版 ⬜ 🟡）
│   └─ GRHIDFA_concl  PA3:711  ⬜ sorry【OXLZLEZ1 组合引擎：负 gg 和压缩模型
│       不可能】
│           └─ PA3:665-714 六件 cc_v11 结构引理 ⬜（CHQSQEY/MTMLSRF/LXDEYBO/
│               UNPNFVW/IPVICGW/RSIWAMP/UTEOITF/LUIKGMH_concl）
│               + PA4 九件 public *_v11 孪生（:645-713）⬜
│               + PA4 私 CC4P4 编码 39 件波（CHQSQEY..GRHIDFA :624-634）⬜
│               ——双编码并行、证明银行均未开工
│
└─ TSKAJXY  PA21:6358-6381  ✅（by_cases 分案组装）
    ├─ TSKAJXY_1  PA21:2995  ✅（1-胞；GAMMAX_NULLSET ✅ + GAMMAX_MCELL1 ✅
    │   + MCELL1_VOL ✅）
    ├─ TSKAJXY_2  PA21:6307  ✅（2-胞；GAMMAX_GAMMA2_X PA21:6223 ✅（经
    │   LocalAuto38Bridge，0 sorry）+ MCELL2_VX_PROPS ✅ + GRKIBMP ✅）
    ├─ TSKAJXY_034  PA21:1335  ⬜ sorry【0/3/4 胞巨案，~600 步 refinement】
    │   └─ 填证路线已备：GRKIBMP ✅（PA21:491，bank 实例化）+
    │       cell3_from_ineq_thm ✅（PA21:1263）+ tsk_bank 假设直通；
    │       3/4-胞臂需 PA20 双巨 🟡：
    │         gammaX_gamm4fgcy  PA20:1470  ⬜（k=4；余 (a) Cayley-Menger
    │           四面体体积桥 = 新子工程，(b) edgeX 六对和/k-识别）
    │         gammaX_gamma3f   PA20:1494  ⬜（k=3；余 cell_params_d 唯一性
    │           k=3 实例 + 同上 edgeX 和；k-识别与 AJRIPQN/p24 同件）
    └─ cell3_from_ineq_thm  PA21:1263  ✅（九 COMMENT 轨 8/9 已 discharge）
        ├─ p21_cell3_core  PA21:1153  ✅（七条 cell3 bank 条件覆盖论证）
        └─ p21_track7  PA21:1138  ✅
            └─ mi_gamma3f_gamma3f_x_div_sqrtdelta  PA21:959-973  ⬜ sorry
                （需 sol_x_sol_euler_x merge_ineq.hl:841 + matan 换算 :1060/:920
                 + EULER_TRIANGLE——全树未移植 → 新波）
```

## 2. textCapstone（Assembly.lean:842）✅真证——全部直接消费件

| 件 | 位置 | 状态 | 上游/备注 |
|---|---|---|---|
| kcImpTheKc | Assembly:776 | ⬜ | 体积形→计数形；处方已写：FLYSPECK_DEVOLUTION + CPNKNXN（Zorn）+ KIUMVTC，~25 行装配 |
| PACKING_CHAPTER_MAIN_CONCLUSION | PA25:3692 | ✅体 | 见 §1 |
| nonlinear_imp_lp_main_estimate_p16 | LA16:192 | ✅体（一行） | → JEJTVGB_p16 LA16:180 ⬜（缺 OEHDBEN 一件改写 + BKOSSGE_p16 LA16:114 ⬜，后者 verbatim = LocalAuto1.BKOSSGE_concl，BKOSSGE 波落地即消）|
| localAnnulusInequalityScriptL | Assembly:730 | ✅ | 定义性恒等（RADV2 + 求和约定）|
| fcdjdot | Assembly:756 | ⬜ | 卡 PackIneqDefA 占位 |
| contraveningFan | Assembly:457 | ✅体 | 经 ContraFan（16/18 真证；LEMMA_3/4_POINTS_FINAL 深核 sorry 沿此流动）|
| mqmsmab | Assembly:466 | ⬜ | tame 章 MQMSMAB |
| tamePlanarHypermapRestricted | Assembly:481 | ✅ | 纯组装 |
| jcajydu | Assembly:506 | ⬜ | tame 章 |
| tameCorrespondenceIso | Assembly:512 | ⬜ | tame 章 |
| elllnyz | Assembly:519 | ⬜ | 镜像析取形 |
| hypermapOfFanNeg | Assembly:539 | ⬜ | 卡镜像链工具链（azim_mirror + sigmaFan 镜像逆，~500 行，全树未移植）|
| contraveningNegative | Assembly:725 | ⬜ | 5/7 数据合取项私件已真（scriptLNegative 等）；第 6/7 合取项卡同一镜像链 |
| hypermapIsoTrans / isoOppositeEq | Assembly:782/591 | ✅ | 纯逻辑 |
| （上层供给）nonlinearInequalities | Assembly:825 | ⬜接口 | 六分量：前三已是真 Prop（pnn/ox3/mnt），LpIneqs/PackIneqDefA/KcblrqcIneqDef 占位（G4/P6-E）|
| （上层供给）goodListArchive | Assembly:889 | ✅ | P6-C native_decide 分片 |

## 3. 会师点清单（终章/p24/gammaX 落地后自动顶死 vs 需新波）

**落地即顶死（零新波或纯移植装配）：**
1. GRUTOTI 终章（pivot ¬nullSet 支，PA23:5072 在飞）→
   a. PA2.GRUTOTI1_concl 桩可 `exact PA23.GRUTOTI`（merge 时删 `_p24`/`_pub` shim，改 PA16:1617 与 PackingConcl:605 指向）；
   b. PA16.KIZHLTL4 转洁净（唯一外部 sorry 输入）；
   c. PA19.UPFZBZM 转洁净（经 NEGLIGIBLE_FUNC→KIZHLTL4；KIZHLTL1/2 已洁净）；
   d. PA2.UPFZBZM_concl (PA2:5048) 按 PA19 真证移植填证（纯移植）→ **RDWKARC_concl 全洁净** → 主结论 RDWKARC 臂零债。
2. p24 两笔（PA24:1118 REUHADY 主件 + :3587 p24_exists_mcell_not_flat，在飞）→
   a. PA2.REUHADY_concl/_version2 两桩（PA2:5378/5395）删；
   b. PA25.REUHADY 本地副本（:1074）真证化 → LEAF_RANK_REUHADY/LEAF_RANK_BIJ/LEAF_RANK_GRUTOTI/real_model_sum_azim/c_4_azim_mcell_dih_y 装配级可填（各 ~30-100 行）。
   注意：p24 (i) k′-识别与 PA17.AJRIPQN 刚性件同件，AJRIPQN 波会抢。
3. PA20 gammaX 双巨（Wave V/E/M 在飞）→ TSKAJXY_034 的 3/4-胞臂解锁（0-胞臂 GRKIBMP+cell3_from_ineq 已备）；TSKAJXY_034 本体仍是 ~600 步装配波（B 级）。

**需新波（无在飞线覆盖）：**
4. mi_gamma3f_gamma3f_x_div_sqrtdelta（PA21:973）：EULER_TRIANGLE + sol_x_sol_euler_x 链移植（cell3_from_ineq 的唯一继承债）。
5. GRHIDFA_concl 簇（PA3:711 + PA3 六件 + PA4 九件 v11 + PA4 私编码 39 件）：cc_v11 组合引擎，双编码待合并，估 1000-3000 行。
6. CELL_CLUSTER_ESTIMATE_PROPS / cc_real_model_data：等 2（REUHADY 群）+ PA18 cc_pe_exists/cc_uh_exists（YBZFUPO/NWVRFMF 新波）+ real_model_* 区间锚（G4 侧）。
7. ox3q1hP25 / pack_nonlinear_rest 两枚 bank 叶：Oxl_def.hl 正文回填 + G4 62 条余叶（外部认证，非 Lean 波）。
8. PA20 双巨自身的 (a) Cayley-Menger 体积桥 = 独立数学子工程（Mathlib 无 simplex-volume 基建）。
9. textCapstone KC/tame 侧：kcImpTheKc（~25 行，处方全）、BKOSSGE/OEHDBEN、镜像链（hypermapOfFanNeg+contraveningNegative 共享，~500 行）、tame 章四接口、fcdjdot。

## 4. 债务量汇总（PA25 主结论临界路径）

| 路径 | 余债 | 量级 |
|---|---|---|
| RDWKARC 臂 | UPFZBZM_concl 桩（GRUTOTI 收口后纯移植）| ~50 行装配 |
| TSKAJXY 臂 | TSKAJXY_034 + PA20 双巨 + mi_gamma3f | ~600 步装配 + CM 桥子工程 + EULER 波 |
| OXLZLEZ 臂 | CELL_CLUSTER_ESTIMATE_PROPS（→cc_real_model_data→wedge 链+bank 锚）+ GRHIDFA 簇 | 装配波 + 1000-3000 行组合引擎 |
| bank 前提 | ox3q1hP25 + pack_nonlinear_rest | G4 证书侧 |
