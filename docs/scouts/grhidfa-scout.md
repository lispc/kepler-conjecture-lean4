# GRHIDFA_concl 测绘：PA3 唯一直源（OXLZLEZ2 巨件）（SCOUT，2026-10-23，Lane BJ 只读交付）

> 车道：GRHIDFA 拆波可行性侦察（**完全只读**——零构建、零 tracked 写、零 git 写操作；
> 仅有的两条 git 查询为 `status`/`log` 只读命令，无状态变更）。
> 基线：PA3 头部提交 `5d050ade`（SF-41 应用），文件 md5 见 MD5SUMS。
> 方法：OXLZLEZ1.hl 全文精读（578 行）+ OXLZLEZ2.hl 逐块引用扫描（python 依赖闭包机械计算）
> + PA3/PA4/PackingConcl/PA25/Assembly 五文件定理级 sorry 普查 + 消费端逐行对账。
> 交付：本文件 + `DEP_MAP.tsv`（77 块逐行）+ `WAVES.md`（6 波施工计划）+ `MD5SUMS`。
> 无任何编译/axiom 探针；涉及 "#print axioms" 的记账一律转引树内注记（PackingConcl:787-796）。

---

## 0. 结论速览（编排者先读这段）

1. **能拆波，且必须拆波——但这是一条"全有或全无"的车道**。GRHIDFA 的 HOL 证明是
   严格的漏斗形：全部 4,037 行定理内容最终汇入一个 11 行的 capstone（OXLZLEZ2.hl:4512）。
   中间任何一行不落，PA3:717 的 sorry 就摘不掉、PA25.OXLZLEZ 的 taint 就减不了一分。
   拆波的意义是**分期降险**（每波一个可验收中间里程碑），不是分期收获。
2. **任务书三条前提实测修正**（详见 §1）：
   (a) "PA3:693 IPVICGW_concl 与 :705 UTEOITF_concl 已真证"——**不成立**。两行与 GRHIDFA
   同为 `by sorry`（PA3 全部 9 处 sorry 恰为九大结论行集）；PA4 侧 CC4P4 版(:536/:600)与
   CcV11 孪生版(:674/:688)也全部 sorried；PackingConcl 九连 `_discharged` 全走 sorryAx
   （树内注记自证，PackingConcl:721/739 "sorry body — taint flows"）。
   (b) "HOL 侧 OXLZLEZ2.hl 约 3,350 行压在 GRHIDFA 后"——**漏算 17-20%**。四单源侦察
   （four-singles-scout §1.2）把闭链估为 3,300-3,400 HL 行，但其 "IPVICGW 链 ~1,490" 一项
   误并了两件互不相关的东西，且漏掉了 **MTMLSRF（510 行）与 LXDEYBO（121 行）这两个
   传递依赖**（经 UNPNFVW→CC_CARD_LESS_THAN_5 与 IPVICGW_C33/C43_C44 硬消费）。
   机械算得的精确传递闭包 = **77 块 / 定理体 4,037 HL 行**（DEP_MAP.tsv 逐行可复核）。
   折算 Lean 随之上修：**2,950-5,800 行（中位 ~4,200）**，四单源的 2,600-4,600 需按比例上移。
   (c) "PA4 CC4P4 同构桩可互抄"——**成立且比侦察稿说的更好**：PA4 §2 的 30 行骨架里
   **已有 19 行真证**（QU_OR_QXY:257、SUM_POS_LT_NUMSEG:266、SUM_BETA:273、MOD_INJ1:290、
   THREE_MOD_CONSECUTIVES:321、MOD_PERIOD_BOUNDED:336、MOD_PERIOD_BOUNDED2:344、
   CC_4CELL_QUQX:362、QX_NN00:374、QY_NN00:380、NUMSEG_SET_VER:390、FINITE_INITIAL_SEG2:396、
   MOD_NUMSEG:406、NUMSEG_INTER_22:461、PERIODIC_IMAGE_EQUAL:470、LEAST_BOUND_CC_GG:548、
   LITTLE_CC_GG3BB:559、LITTLE_CC_GG3AA:576、NOT_QY_LEM:612）。四单源侦察 §1.3 "Lean 侧该链
   零移植" 是 grep 词表太窄（只查了 5 个结论名）造成的漏报。这 19 行是 W1 波的现成参考实现。
3. **无条件化问题（任务书核心疑虑）证伪：不存在无条件化**。PA3:717-721 的 GRHIDFA_concl
   四前提一个不少（`_hb : cc_bool_model_v11 cc`、`_hp : cc_bool_prep_v11 cc`、
   `_hr : cc_real_model_v11 cc`、`_hsum : ∑ … < 0`），下划线只是命名约定，**证明体内完全可消费**
   （Lean 4 中 `_hb` 是合法绑定名）。与 HOL OXLZLEZ1.hl:173-174 的
   `!cc. cc_bool_model_v11 cc /\ cc_bool_prep_v11 cc /\ cc_real_model_v11 cc /\ (sum…< &0) ==> (F)`
   逐前提同序同形。HOL 证明体对两个 bool 前提的实质依赖点已全部定位（§4）：
   cc_bool_model_v11 → periodic_fn/QY_QX_QU/THREE_LE_CC_CARD（经 CHQSQEY）；
   cc_bool_prep_v11 → UNIQUE_QY/UNIQUE_QY2/CARD5 系。**这些前提在 Lean 侧原样可用，
   PA25 的 CELL_CLUSTER_ESTIMATE_PROPS（:9938 真装配）正是按此签名供货**——
   PA25:9968 `exact GRHIDFA_concl _ hbm hprep hr hsum` 一行消费，接口零改。
4. **误植检查：三件冻结陈述零误植**（§2，含 PA4 同位桩 11 行逐前提对照）；另记两处
   树内注记行号漂移（Assembly:6339 写 PA3:711、PA4 docstring 写 OXLZLEZ1.hl:548，见 §2.3）。
5. **消费面（GRHIDFA 闭了谁跟着转）**：直接消费者仅三处——PA25.OXLZLEZ:9968（真装配，
   收益=PA3 摘出 taint 源）、PA4.GRHIDFA:627 与 PA4.GRHIDFA_v11:702（同为 sorried 桩）、
   PackingConcl.GRHIDFA_concl_discharged:762（吃 PA4 孪生）。**Assembly.lean:6339 是纯记账
   注记，无代码消费**。注意：GRHIDFA 单闭不能让 PackingConcl 九连转净（九行互相独立，
   需九枚孪生全闭）；PA25.OXLZLEZ 即便 GRHIDFA 闭了也仍被 cc_prep_model_data(PA25:5238 ⬜)
   与 cc_real_model_data(PA25:9903 ⬜) 染色——**本车道与 PA25 数据臂是两条独立债**。
6. **工期**：HOL 4,037 行（九大件 3,229 行占八成）→ Lean 2,950-5,800；单工人 6 波
   **3-5 周**；双 lane（W2/W3 并行）可压到 2-3 周。成功率 ~85%（无真数学缺口，全部机械
   移植；HOL 全证，数值全是固定常数）。降级路线与卡壳预案见 §8。
7. **立项建议**：与四单源侦察一致——"可立即开（不欠任何前置）"。W1 波有 PA4 的 19 行
   真证参考实现，**明天可开工**（任务书草案见 WAVES.md §4）。但它是四单源中体量最大、
   中途无产出的一件；若编排者本周要 SORRIED 计数下降，别选它；要啃最硬的骨头，它是正主。

---

## 1. 任务书前提逐条复核

### 1.1 "IPVICGW/UTEOITF 已真证"——证伪

全树 grep `IPVICGW|UTEOITF`（Lean 侧）命中四处定义位，全部 sorry：

| 位置 | 形态 | 状态 |
|---|---|---|
| PA3:693-696 `IPVICGW_concl` | CcV11，`∀ i, cc_small_v11 cc i` | **SORRY** |
| PA3:705-708 `UTEOITF_concl` | CcV11，`∀ i, cc_4cell_v11 cc i` | **SORRY** |
| PA4:536-540 `IPVICGW` | CC4P4 私有 | **SORRY** |
| PA4:600-605 `UTEOITF` | CC4P4 私有 | **SORRY** |
| PA4:674-679 `IPVICGW_v11` | CcV11 公开孪生 | **SORRY** |
| PA4:688-693 `UTEOITF_v11` | CcV11 公开孪生 | **SORRY** |

PackingConcl:720-727/:738-745 的 `IPVICGW_concl_discharged`/`UTEOITF_concl_discharged`
是吃 PA4 孪生的项级装配（本身无 sorry），树内 `#print axioms` 注记（:787-796）明言
"expect sorryAx on each"。**本任务书该句应更正为：九大结论在两代编码中共 27 处陈述桩，
一处真证都没有；真证的是它们脚下的 kit（PA3:398-664 十八行 + PA4:257-612 十九行）。**

### 1.2 体量：3,350 → 4,037 HL 行

四单源侦察的账（IPVICGW 链 ~1,490 + UTEOITF 462 + GRHIDFA_ALT 312 + LUIKGMH 262 +
kit ~756 + RSIWAMP 21 ≈ 3,303）有四处出入：

1. **漏算 MTMLSRF（OXLZLEZ2.hl:564-1073，510 行）**：UNPNFVW 首步 `NHANH MTMLSRF`
   （:1338 实测），UNPNFVW 在闭包内（UNIQUE_QY/CARD5 系/CC_CARD_LESS_THAN_5 都吃它）。
2. **漏算 LXDEYBO（:403-523，121 行）**：IPVICGW_C33 首步 `NHANH LXDEYBO`（:1830 块内
   实测）、IPVICGW_C43_C44、EXISTS_QY_CARD5、CC_CARD_LESS_THAN_5 四处硬消费。
3. **多算了 NUMSEG_INTER_22 + PERIODIC_IMAGE_EQUAL（27 行）**：闭包内无任何块引用它们
   （互相引用 + 被 PA4 已真证的同名行覆盖），非 GRHIDFA 依赖。
4. **漏算尾 kit ~110 行**（LEAST_BOUND_CC_GG 13 + periodic_mod1 7 + LITTLE_CC_GG3BB 12 +
   MOD_ADD_CANCEL 6 + LITTLE_CC_GG3AA 52 + SUM_NUMSEG 族 21 等，全是 UTEOITF 的前提）。

修正后：**4,037 HL 定理行 / 77 块**（python 闭包机械计算，DEP_MAP.tsv 全表）。
另：文件本身 4,522 行，闭包外 = tactic 基建 182 行 + 死代码 166 行（glt/e1-e4/SUM_POS_LT_NUMSEG
只被死代码引用）+ 闭包外小件，均无需移植。

### 1.3 "PA4 桩可互抄"——成立，且升级

四单源侦察只看到 PA4 桩的"陈述冻结已做"；实测 **19/30 行已真证**（§0.2 清单），
覆盖了 W1 波的全部 kit 需求。剩 11 行 sorried 大件 + 9 行 `_v11` 孪生。
PA4:55-58 自己写明设计意图："the private `CC4P4` twins of section 2 are the eventual
proof bank these rows will be discharged from"——但注意 PA3 **不能** import PA4
（PA4:66 import Kepler.Text.PackingAuto3），所以证明银行只能落在 PA3（详见 §7 波次架构）。

---

## 2. 冻结陈述与误植检查（零容忍项）

### 2.1 三件主陈述 vs HOL（逐前提）

| 件 | HOL（OXLZLEZ1.hl） | Lean（PA3） | 判定 |
|---|---|---|---|
| GRHIDFA_concl | :173-174 `!cc. cc_bool_model_v11 cc /\ cc_bool_prep_v11 cc /\ cc_real_model_v11 cc /\ (sum (0..cc_card_v11 cc -1) (cc_gg_v11 cc) < &0) ==> (F)` | :717-721 四具名前提同序（_hb/_hp/_hr/_hsum，∑ i ∈ Icc 0 (card-1), gg i < 0）结论 `False` | **一致** |
| IPVICGW_concl | :156-157 `… ==> (!i. cc_small_v11 cc i)` | :693-696 同 | **一致** |
| UTEOITF_concl | :167-168 `… ==> (!i. cc_4cell_v11 cc i)` | :705-708 同 | **一致** |

前提次序均为 bool_model → bool_prep → real_model → gg-sum<0；sum 表达式均为
`0..card-1` 闭区间和。OXLZLEZ2.hl 内部的结论复制件（:548/:554/:3452/:4231/:4236）与
OXLZLEZ1 正本同文（逐一目验）。PA4 的九枚 `_v11` 孪生（:645-706）与 PA3 九行**逐字相同**
（同文件内对照），PA4 的 CC4P4 版（IPVICGW:536/RSIWAMP:542/UTEOITF:600/GRHIDFA_ALT:606/
LUIKGMH:619/GRHIDFA:627/PRE_IPVICGW:524/CC_CARD_LESS_THAN_5:530/IPVICGW_C33:430/
IPVICGW_C43_C44:451/EXISTS_QY_CARD5:456/CARD5_1074_LE_QYI:510）与 HOL 对应块
（:3308/:3320/:3457/:3919/:4249/:4512/:3229/:3264/:1830/:2068/:2464/:2527）逐前提对照
**零误植**（含 `ccCardP4 cc ≠ 4` ↔ `~(cc_card_v11 cc = 4)` 的 GRHIDFA_ALT 否定形式）。

### 2.2 数值常数抽查（零漂移）

cc_eps 0.0057（PA3:46 ↔ OXLZLEZ1:23 ↔ PA4:175）、a_spine5 0.0560305（PA3:55 ↔ PA4:178）、
b_spine5 −0.0445813（PA3:60 ↔ PA4:181）、azim1/gaz4/gaz6/gaz9/azim2/cell3/pem/tew/txq 各系数
（PA3:156-205 ↔ OXLZLEZ1:80-133 逐合取位次一致；四单源 §5.1 的 34 合取对账结论本轮复核维持）。

### 2.3 注记行号漂移（两处，不影响陈述）

1. Assembly.lean:6339 记账图写 "GRHIDFA_concl（PA3:711 ⬜…）"——行号已漂，实为 :717
   （:711 是 LUIKGMH_concl）；"1000-3000 行" 的估计偏小（见 §1.2）。
2. PA4:535 docstring "OXLZLEZ2.hl:3308 (`IPVICGW_concl`, OXLZLEZ1.hl:548)"——OXLZLEZ1 侧
   实为 :156-157；:548 是 OXLZLEZ2 自己的结论复制件行号，两文件行号在此被误并。

---

## 3. OXLZLEZ2.hl 内部结构：四段 + GRHIDFA 精确消费

全文件 4,522 行 = 四个"可独立交付的段"（段间依赖单向）：

| 段 | HL 行域 | 内容 | 定理行数 | GRHIDFA 消费? |
|---|---|---|---|---|
| S0 战术基建 | :1-182 | NHANH/DOWN/DOWNS/PHA/ASM_SEARCH 等 30 个战术定义 | 0（战术） | 否（Lean 侧有等价 have/exact 习语，PA4 已示范） |
| S1 章内小结 | :183-1227 | QU_OR_QXY、SUM_POS_LT_NUMSEG、死代码 glt/e1-e4、LXDEYBO、MTMLSRF、MOD_INJ1、WKR_COMPTED、CHQSQEY(oxl6142) | ~770（死代码 166 不计） | **是**（全段入闭包，除死代码） |
| S2 结论上梯 | :1228-2526 | THREE_LE_CC_CARD、UNPNFVW、mod/periodic kit、UNIQUE_QY(2)、IPVICGW_C33、IPVICGW_C43_C44、EXISTS_QY_CARD5 | ~800 | **是**（NUMSEG_INTER_22/PERIODIC_IMAGE_EQUAL 除外） |
| S3 card5 攻坚 | :2527-3456 | CARD5_1074_LE_QYI、CARD5_LT_1074_QYI、PRE_IPVICGW、CC_CARD_LESS_THAN_5、IPVICGW、RSIWAMP、尾 kit、UTEOITF | ~1,170 | **是**（全段） |
| S4 capstone | :3457-4522 | UTEOITF、GRHIDFA_ALT、LUIKGMH、GRHIDFA | ~1,140 | **是**（全段） |

**GRHIDFA 的直接与传递消费（DEP_MAP.tsv 全表）**：
- capstone :4512-4522（11 行）：`PHA THEN NHANH LUIKGMH THEN NHANH GRHIDFA_ALT THEN
  NHANH RSIWAMP … DOWNS 3 THEN ARITH_TAC`——**吃三件：LUIKGMH、GRHIDFA_ALT、RSIWAMP**。
- GRHIDFA_ALT（312）硬吃 UTEOITF + IPVICGW；LUIKGMH（263）经 NOT_QY_LEM 吃 UTEOITF；
  UTEOITF（462）吃 IPVICGW + RSIWAMP + UNIQUE_QY + 尾 kit；IPVICGW（12）吃
  CC_CARD_LESS_THAN_5 + THREE_LE_CC_CARD + IPVICGW_C33/C43_C44 + PRE_IPVICGW。
- 底部汇入 OXLZLEZ1 已证 kit（**PA3 全部已有**：QX_NN:546、QY_NN:553、QY_QX_QU:563、
  QUARTER1:572、QU_EXISTS:601、CC_CARD2:610、periodic_fn:523、periodic_sum:493、
  periodic_mod:410、MOD_IN_NUMSEG:419、MOD_INJ:425、MOD_INJ1_ALT:451、MOD_SURJ:464、
  BIJ_SUM:476、periodic_numseg:635、BIJ_NUMSEG:645、PERIODIC_PROPERTY:661）——
  **树内零缺口，W1 波前无前置**。
- 九大件（占闭包八成）：MTMLSRF 510 / UTEOITF 462 / CARD5_LT_1074_QYI 418 /
  UNPNFVW 413 / IPVICGW_C43_C44 396 / GRHIDFA_ALT 312 / CARD5_1074_LE_QYI 276 /
  LUIKGMH 263 / IPVICGW_C33 179 = 3,229 行。全部是有限 case 分裂 + 集合计数 +
  周期移位求和（MTMLSRF 12 个 ASM_CASES_TAC、UNPNFVW 3 个），无测度论、无浮点不定性。

---

## 4. 无条件化问题：cc_bool_model_v11 / cc_bool_prep_v11 的实质依赖点

结论先行：**Lean 陈述无条件化从未发生，HOL 证明结构可 1:1 照搬**。HOL 证明体对两个
bool 前提的消费点（逐块扫描实测）：

| 前提 | 消费位置（OXLZLEZ2.hl） | 用途 | Lean 侧替代资产 |
|---|---|---|---|
| cc_bool_model_v11 | oxl6142(:1195)→THREE_LE_CC_CARD(:1228)；QY_QX_QU(OXLZLEZ1:386) 经 QU_OR_QXY(:183)；periodic_fn(OXLZLEZ1:347) 经 UTEOITF:3479/GRHIDFA_ALT:3929；cc_bool_model ⇒ card≠0（CC_CARD_LESS_THAN_5:3294 内联 prove） | card≥3 推导、三分法、hassmall/qu/qx/qy 周期性、card≠0 | PA3 periodic_fn:523、QY_QX_QU:563、QUARTER1:572 全已证；card≠0 一行 `SIMP_TAC[cc_bool_model_v11]` 照抄 |
| cc_bool_prep_v11 | UNIQUE_QY(:2009)/UNIQUE_QY2(:2052)（qy 不相邻 ⇒ 唯一 qy）；CARD5_1074_LE_QYI/CARD5_LT_1074_QYI 的 card=5 情形 | card5 时 qy 唯一性 | 无现成件，但 UNIQUE_QY 本身就是 W3 波行，照抄即可 |
| （对照）cc_real_model_v11 | QX_NN00(:1740)/QY_NN00(:1745)、PRE_IPVICGW、CARD5 系、LUIKGMH | gamma_qx/gamma_qy/求和非负 | PA3 QX_NN:546/QY_NN:553 已证；PA4:374-388 已示范合取位解构习语 |

PA25 侧供货接口已冻结且为真装配：CELL_CLUSTER_ESTIMATE_PROPS（PA25:9938）给出
`cc_bool_model_v11 (cc_data_v8 V f u0 u1)`、`cc_bool_prep_v11 (…)`、`cc_real_model_v11 (…)`
三项（其中 bool_model 项经 **已真证** 的 cc_bool_model_data PA25:5120-5237，118 行真证）。
即：**不存在"Lean 侧要替 HOL 补盒模型存在性"的问题**——前提由 PA25 数据臂供给，
GRHIDFA 只管在同一前提下推出 False。任务书设想的"用 cc_bool_model 资产替代"方案无需启动。

---

## 5. 树内存量（五层）

| 层 | 状态 | 明细 |
|---|---|---|
| PA3 | **9 sorry / 722 行**，全部是九大结论桩；定义+TARJJUW+周期 kit+model 推论（:35-664）全真证 | 陈述库模块 |
| PA4 | **39 tactic sorry / 2,177 行**（另 3 处为注记文字提及 sorry，非 tactic）；OXLZLEZ2 波 30 行 sorried（21 CC4P4 + 9 `_v11` 孪生）+ 19 行真证 kit；其余 9 处在 MCELL_*_CELL_PARAMETERS_EXIST/MCELL_PARAM_UL/MCELL3_VX 系（bump 章，另一条债） | 骨架批 |
| PackingConcl | 0 直接 sorry；九连 `_discharged`（:668-768）吃 PA4 孪生，taint 流经（#print axioms 注记 :787-796 自证） | 装配层 |
| PA25 | OXLZLEZ:9959 **真装配**（18 行，体无 sorry），经 :9968 吃 PA3.GRHIDFA_concl；自身债 = cc_prep_model_data:5238 ⬜ + cc_real_model_data:9903 ⬜（LEAF_RANK_PROPS:8053 真装配但其 W1/W2 前提树另计） | 数据臂 |
| Assembly | GRHIDFA 仅 :6339 记账注记；代码消费经 PA25.PACKING_CHAPTER_MAIN_CONCLUSION:9977（真装配）→ textCapstone | e2e 层 |

---

## 6. 消费面：GRHIDFA 闭了谁跟着转

1. **PA25.OXLZLEZ:9968**（唯一代码级直接消费者）：`exact GRHIDFA_concl _ hbm hprep hr hsum`。
   GRHIDFA 闭 → PA3 从 PA25 的 taint 源列表划掉；但 PA25.OXLZLEZ 本身不清零
   （cc_prep_model_data/cc_real_model_data 两枚 sorry 仍在）。HOL 对位 = OXLZLEZ3.hl:9011
   `INTRO_TAC Oxl_2012.GRHIDFA`（OXLZLEZ capstone，全库唯一 HOL 级消费者）。
2. **PA4.GRHIDFA:627（CC4P4）与 PA4.GRHIDFA_v11:702（CcV11 孪生）**：同为 sorried 桩，
   互为证明银行关系（PA4:55-58 注记）。GRHIDFA_v11 闭 → PackingConcl:762 的
   GRHIDFA_concl_discharged 转纯（条件：九枚孪生全闭，非仅此一枚）。
3. **PackingConcl 九连**：GRHIDFA 一枚闭只净一行；九行互相独立、须全闭。
4. **Assembly:6339**：纯记账，随 PA25.OXLZLEZ 状态走。
5. **不跟着转的**：PA25 数据臂（独立债）、PA4 bump 章 12 处 sorry（独立债）、
   四单源 #2/#3/#4（无耦合）。

---

## 7. 折算、工期与波次架构（详表见 WAVES.md）

**架构裁定**：证明银行必须落在 PA3（CcV11 编码），理由：PA4 import PA3（单向），
PA3 不能反向 import；PA25 消费的是 PA3 的行。W1-W5 在 PA3 内新建 ~31 行
（W1 kit 24 行 + W2 7 行 + W3 10 行 + W4 2 行 + W5 4 行，其中 W3 的
CARD5_LT_1074_QYI 是 PA4 骨架都缺的行）；W6 在 PA4 内建 CC4P4→CcV11 桥
（~120-250 行，一次性）后 30 行 sorried 桩全部一至三行 discharge，`_v11` 九孪生
直接 `:= PA3.<同名>`。备选（在 PA4 内证 CC4P4 再桥回）被 PA3 不能 import PA4 否决；
"九大件写两遍"被成本否决（+30-40%）。

**折算**：HOL 4,037 → Lean 2,950-5,800（中位 ~4,200，比率 0.73-1.44；
参照 ContraFan GIANT 1,390→1,100-1,700 = 0.79-1.22x，本件 refine 噪声略高但
PA4 已有 19 行参考实现拉低 W1）。

**工期**：单工人 **3-5 周**（6 波，每波 2-6 施工日）；双 lane（W2/W3 并行）2-3 周。
四单源的 "2-4 周" 基于 3,400 行，按 4,037 行上修。

**成功率 ~85%**。风险集中两处：MTMLSRF（510 行，最大单块，W2）与 CC4P4→CcV11 桥的
Iff/getD 记账（W6）。均非数学缺口。

---

## 8. 工期风险与备胎（降级路线）

| 风险 | 概率 | 预案 |
|---|---|---|
| MTMLSRF 卡壳（W2，510 行 12 分裂） | 中 | 分两段提交：前半（gg<0 的 qu 存在性 + 集合拆分 :564-800）独立验收；后半（周期求和移位 :800-1073）照 periodic_sum 习语。PA4:283 桩与 HOL 逐行对抄，无替代证明需求 |
| CcV11 getD 访问器让 case 分析难写 | 中 | W1 加发一个 50 行 `getD/EL 工具箱`（getD_eq_of_lt_length 等），后续行全部按 HOL EL 习语直译；PA3 现有 QUARTER1/CC_CARD2 已趟过此路 |
| W3 card5 双件（694 行）超预估 | 低-中 | CARD5_1074_LE_QYI(:2527,276) 与 CARD5_LT_1074_QYI(:2811,418) 拆两个里程碑，各自独立可验；共用 UNIQUE_QY/PREV kit |
| W6 桥的 periodicPropP4(Iff) vs periodic(Prop 上的 Eq) 记账 | 低 | 二者经 propext 定义等价（PA3 periodic 定义 :135 对 Prop 即 Iff）；桥内一次性引理 + 30 处复用 |
| 工期爆炸（>5 周） | 低 | 降级 A：W1-W4 完成后停（PA3 得 31 行真证 kit/中件，SORRIED 计数 −24 枚 PA4+PA3 骨架行不能实现但资产沉淀）；降级 B：W6 只桥 GRHIDFA/UTEOITF/IPVICGW 三枚主件、CC4P4 余桩挂 NEEDS（省 ~80 行） |
| 本车道不开 | - | 后果：PA25.OXLZLEZ 臂永久挂起（四单源判定其为最低优先级大而钝件，成立）；无其他车道被闸 |

**"全有或全无"警示（重复一次，编排者排期用）**：W1-W4 的全部产物是 PA3 内部中间件，
除 W1 的 24 行 kit 外无外部消费者；SORRIED 总数在 W5 完成前**一枚都不会降**。
若需要中途可见产出，唯一选择是 W1 kit 波（PA3 +24 真证行，可提前合并）。

---

## 9. 立项判断（对四单源侦察的最终复核）

四单源 §1.5 "可立即开（不欠任何前置），但属最低优先级的'大而钝'件" —— **维持，
三处细化**：(1) 不欠前置成立（PA3 kit 全证 + PA4 参考实现 19 行在库）；
(2) "消费面只有 OXLZLEZ 一跳"成立（PA25:9968 一行 + PA4 双桩 + PackingConcl 一行）；
(3) "别选它如果本周要减 SORRIED 计数" **加强**：本件在 W5 落地前 SORRIED 计数零变化，
是六条在飞车道里唯一全程无中间计分的一件。拆波价值 = 风险分期，不是收益分期。
