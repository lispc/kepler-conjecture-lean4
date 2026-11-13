# tauxkit-w1 DELIVERY — tau_x kit 并案侦察（2026-11-14）

> 车道性质：侦察/章程车道，**全程只读**（主仓 tracked 零改动；探针只在 /tmp + 快照）。
> 三件套：① 本报告（HOL 考古 + 消费者盘点 + 顺手可收清单 + 雷区）；② `charter-draft.md`；
> ③ `logs/`（探针脚本 + 输出）。结论一句话：**两个零桩的假不是"未证"是"按字为假"**，
> 而真身（逐字 HOL 同体）早已在树内（`LocalAuto1` 的 `_t11` kit + ICD），DEF-FIX 只需
> "指真身 + 补 7 件证明"，**全部消费者按字仍为真，零 SF**。

## 0. 执行摘要

| 问题 | 结论 | 机器证据 |
|---|---|---|
| 两桩（`taumX_p19`/`tauResidualX_p19`，LA19:128/132，`fun _ => 0`）原版是什么？ | sphere.hl:827 `taum_x`（rhazim 三项 −(1+const1)π）/ nonlin_def.hl:181 `tau_residual_x`（rhazim_x_div_sqrtdelta_posbranch 三旋转和） | 行段全文 §1；真身已在树 = `taumX_t11`（LA1:1243）/`tauResidualX_t11`（LA1:1237）逐字同体 |
| 存量陈述是假的吗？ | **是（零桩按字为假）**：`tau_x_tau_residual_x_general_p19` 在平坦点 (4,4,4,12,4,4) 处 LHS≡0、RHS=−sol0≠0 | `probe_a_stub_literal_false` 编译过，**标准三 axioms**（logs/probe_a.log） |
| 换真身后消费者还成立吗？ | **7/7 按字仍为真，无需 SF**：LA19 1 件 + LA38 6 件形状全部编译过（probe_b 6/6）+ 数值验证（numprobe：残差恒等式 6/6 随机有效点、taum_x_sym、taum_taum_x、taud_x_taum_x、OWZLKVY4、quad_a 全部 OK） | logs/probe_b.log、logs/numprobe.out |
| delta=0 分支在 Lean 里长什么样？ | 有理平坦点 (4,4,4,12,4,4)：三个二面角坍缩为 π/0/0，恒等式退化为 `π·const1 = sol0`（树内 LA22:4979 `la22_const1_eq` 已证的桥） | `probe_a_flat_identity` 标准三（除假设 hc 外零新增债务） |

## 1. HOL 考古（任务件 ①）

### 1.1 原版定义全文（行段）

`taum_x` —— `reference/flyspeck/text_formalization/general/sphere.hl:827-829`：
```
let taum_x = new_definition `taum_x x1 x2 x3 x4 x5 x6 =
    rhazim_x x1 x2 x3 x4 x5 x6 + rhazim2_x x1 x2 x3 x4 x5 x6 +
     rhazim3_x x1  x2 x3 x4 x5 x6 - (&1 + const1)* pi`;;
```
`tau_residual_x` —— `reference/flyspeck/text_formalization/nonlinear/nonlin_def.hl:181-185`：
```
let tau_residual_x  = new_definition
 `tau_residual_x x1 x2 x3 x4 x5 x6 =
     rhazim_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6
+     rhazim2_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6
+     rhazim3_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6`;;
```
依赖链（全部行段已核对原文）：

```
taum_x (sphere.hl:827)
  ├─ rhazim_x x.. = rhazim (sqrt x1)..        sphere.hl:677-678
  │    └─ rhazim y.. = rho y1 * dih_y y..      sphere.hl:211
  │         └─ rho y = &1 + const1 − const1·ly y   sphere.hl:201
  │              ├─ const1 = sol_y 2 2 2 2 2 2 / pi  sphere.hl:197
  │              └─ ly y = interp 2 1 2.52 0 y       sphere.hl:199
  ├─ rhazim2_x = (node2_y rhazim)∘sqrt ; node2_y f y = f y2 y3 y1 y5 y6 y4  sphere.hl:222/226
  ├─ rhazim3_x = (node3_y rhazim)∘sqrt ; node3_y 同理（y3 y1 y2 y6 y4 y5）    sphere.hl:228
  └─ (&1 + const1) * pi

tau_residual_x (nonlin_def.hl:181)
  ├─ rhazim_x_div_sqrtdelta_posbranch x.. = rho(sqrt x1) · dih_x_div_sqrtdelta_posbranch x..  nonlin_def.hl:169-171
  │    └─ dih_x_div_sqrtdelta_posbranch x.. = (sqrt(4 x1)/d_x4)·matan((4 x1 d)/(d_x4²))      nonlin_def.hl:138-142
  │         ├─ d_x4 = delta_x4；d = delta_x（sphere.hl:86-90 / SphereKit:46 同式）
  │         └─ matan x（三分支：x=0→1；x>0→atn(√x)/√x；x<0→log 形）  sphere.hl:728-731
  ├─ rhazim2_x_div_sqrtdelta_posbranch = rotate2 rhazim_x_div_sqrtdelta_posbranch  nonlin_def.hl:173-175
  │    └─ rotate2 f x.. = f x2 x3 x1 x5 x6 x4   sphere.hl:654-655
  └─ rhazim3_x_div_sqrtdelta_posbranch = rotate3 …（x3 x1 x2 x6 x4 x5）  nonlin_def.hl:177-179 / sphere.hl:657-658

同套件（LA38 的另两桩）：
  flat_term_x x = flat_term (sqrt x)；flat_term y = sol0·(y−2h0)/(2h0−2)  sphere.hl:825/527
  taud_x = flat_term_x x1 + sqrt(delta_x)·mu_y(sqrt x1, sqrt x2, sqrt x3)  nonlin_def.hl:413-416（add6/mul6 组合子展开形）
```

### 1.2 原版证明其关键性质的引理清单（任务件 ① 第三问）

**`tau_x_tau_residual_x_general`**（pent_hex.hl:136-214 == terminal.hl:3069-3147，双生同证）：
- 情形 `delta_x = 0`：`Merge_ineq.atn2_0`（merge_ineq.hl:582，ATN2_BREAKDOWN 的 0 特化）、
  `Nonlinear_lemma.rho_alt`（nonlinear_lemma.hl:578：`rho y = 1 + const1·(y−2)/0.52`）、
  `Nonlinear_lemma.sol0_const1`（:232：`sol0 = pi·const1`，经 :229 `sol0_over_pi_EQ_const1` ←
  :208 `sol0_EQ_sol_y`：`sol0 = sol_y 2 2 2 2 2 2`，acs_atn2/ATN2_RNEG/ATN2_LMUL_EQ 计算）、
  `Sphere.flat_term_x/flat_term/h0`。
- 情形 `delta_x > 0`：`Merge_ineq.dih_x_dih_x_div_sqrtdelta_negbranch`（merge_ineq.hl:963：
  `0<x1 ∧ 0<delta_x ∧ delta_x4<0 ⇒ dih_x = pi + sqrt(delta_x)·dih_x_div_sqrtdelta_posbranch`）、
  `Merge_ineq.dih_x_dih_x_div_sqrtdelta_posbranch`（:920：正支，无 pi 项）、
  `matan_pos`（merge_ineq.hl:584）、`Trigonometry1.ATN2_RNEG`/`ATN2_BREAKDOWN`/`SQRT_DIV_R`、
  `pi2_sub_atn2`、rho_alt、sol0_const1，外加 `delta_x` 在 rotate2/3 下的多项式不变（REAL_ARITH 级）。

**`OWZLKVY4`**（pent_hex.hl:216-288 == terminal.hl:3149 双生）：DB 引理 "2314572187"（delta≥80 情形）+
"7796879304"（残差情形）+ `Functional_equation.taud_x_taud`（functional_equation.hl:1425：
`y_of_x taud_x = taud`）+ `Terminal.taum_taum_x`（terminal.hl:169）+ 本 kit 的
`tau_x_tau_residual_x_general` + `Terminal.EAR_DELTA_X4`（terminal.hl:2264，DB "8346775862"/"8631418063"）
+ `Misc_defs_and_lemmas.ABS_SQUARE_LE`、`Nonlinear_lemma.sqrtxx`（:1111）。

**`taum_taum_x`**（terminal.hl:169）：`Nonlinear_lemma.taum_123`（nonlinear_lemma.hl:554：
`taum = rhazim+rhazim2+rhazim3 −(1+const1)pi`；经 `sol_y_123` :524、`rhazim2_alt/3_alt` :537/546）
+ `sqrtxx`。

**`taum_x_sym`**（terminal.hl:3752）：`Nonlinear_lemma.dih_y_sym`（:506）+ `dih_x_sym`（:481：
delta_x/delta_x4 在 (x2 x3) 对换下的不变，PAIR_EQ + REAL_ARITH）。

**`taud_x_taum_x`**（terminal.hl:3764）：OWZLKVY4 + `taud_x_taud` + `taum_taum_x` + sqrt 引理群。

**`taud_x_taud`**（functional_equation.hl:1425）与 **`taum_taum_x`** 是仅有的两件"纯 unfold + sqrtxx"级。

### 1.3 真身已在树内（关键发现）

HOL 依赖链的**每一个**原件在 Lean 树内都已有逐字或等价孪生：

| HOL 原件 | 树内孪生 | 位置 |
|---|---|---|
| `matan` | `matan` / `matan_t11` | `IneqClosureDefs.lean:31` / `LocalAuto1.lean:990` |
| `rotate2/3` | `rotate2_t11`/`rotate3_t11`（ICD 有 unsuffixed） | LA1:997/1001；ICD rotate 族 |
| `dih_x_div_sqrtdelta_posbranch` | `dihXDivSqrtdeltaPosbranch`/`_t11` | ICD:95；LA1:1005 |
| `rho` | `rhoICD`/`rhoICD_t11`（=1+const1−const1·ly） | ICD:756；LA1:1025 |
| `rhazim`/`rhazim2` | `rhazim`（ICD:763）/`rhazim_t11`/`rhazim2_t11` | LA1:1028/1032 |
| `rhazim_x_div_sqrtdelta_posbranch` | `rhazimXDivSqrtdeltaPosbranch_t11` | LA1:1233 |
| **`tau_residual_x` 整体** | **`tauResidualX_t11`（逐字）** | **LA1:1237-1240** |
| **`taum_x` 整体** | **`taumX_t11`（逐字）** | **LA1:1243-1250** |
| `flat_term_x`/`taud`/`taud_x` | `flatTerm_t11`/`flatTermX_t11`/`taud_t11`/`taudX_t11` | LA1:1113/1117/1120/1124 |
| `sol0_const1` | `la22_const1_eq`（`const1 = sol0/π`，方向可互换） | `LocalAuto22.lean:4979`（+ :4981 `solY 2^6 = 3 arccos(1/3) − π`） |
| posbranch 桥 `dih_x = √delta·dih_div√delta` | `p21k_dih_bridge`（private，正支全证） | `PackingAuto21.lean:10926-10934` |
| `matan_pos` | `ea1_matan_pos` | `EulerAtn2Kit.lean:209` |
| `const1`/`ly`/`dihXf`/`dihY`/`solY`/`taum`/`deltaX`/`deltaX4`/`atn2`/`yOfX` | SphereKit 全套 | `SphereKit.lean`（46/78/37/96/103/109/156/161/164/171/118） |

`_t11` 后缀的来由（LA1:980-987 注）：ICD 与 Text 根的 `sqrt3` 孪生撞名，ICD 不可 import，
故 LA1 以 `_t11` 复制了全套体——**这正是 LA19/LA38 桩注释里"unported tau_x kit"的真实状态：
不是未移植，是移植后以 `_t11` 旁挂、未被桩消费**。LA1 的 mainEstimate registry
（:1463 `4680581274_2x`、:1535 `5202826650 a`、:1802 `7796879304`）已在陈述层消费 `_t11` 真身。

## 2. 在树消费者盘点（任务件 ②）

全树 `rg` 测绘（含 ICD/LA1 孪生名）：`taumX_p19`/`tauResidualX_p19` 仅 **LA19:440-441**
（C1 陈述）出现；`taumXP38`/`tauResidualXP38`/`taudXP38`/`flatTermXP38` 仅 **LA38**
（4 个 def + 5 处陈述）出现；LA22:3675-3702 为排期注记（非消费）。**无证明体消费**
（所有消费者本身 `:= by sorry`），无 `native_decide` 涉入。

### LA19 侧（零桩 `fun _ => 0`）

| # | 消费者 | 位置 | 消费方式 | 换真身影响预判 | 证据 |
|---|---|---|---|---|---|
| C1 | `tau_x_tau_residual_x_general_p19` | LA19:433-443 | 陈述出现（`taumX_p19`/`tauResidualX_p19`）+ sorry | **按字仍为真**；无需 SF。证明需补：neg/posbranch 桥、rho_alt、sol0_const1、deltaX 旋转不变。零桩下**按字为假** | 假：`probe_a_stub_literal_false`（标准三）。真：数值 [1] 6/6 点；delta=0 分支 `probe_a_flat_identity`（标准三） |
| C2 | OWZLKVY4/hex/pent 塔（`OWZLKVY4_p19` :447 及其下游） | LA19:445+ | 证明依赖（HOL 路径经 C1 + `taum_taum_x` 形 + DB） | 陈述不含桩名，**不受影响**；塔解锁取决于 C1 + DB 2314572187/7796879304 + EAR_DELTA_X4 | HOL pent_hex.hl:216-288 证明路径；数值 [6]（OWZLKVY4 陈述 6/6 点 OK） |

### LA38 侧（`:= sorry` 不透明桩）

| # | 消费者 | 位置 | 消费方式 | 换真身影响预判 | 证据 |
|---|---|---|---|---|---|
| C3 | `taum_taum_x` | LA38:378-384 | 陈述出现（`yOfX taumXP38`）+ sorry | **按字仍为真**（HOL terminal.hl:169）。证明 = taum_123 形 + sqrtxx | 形状 `probe_b_taum_taum_x` 编译；数值 [4] 4/4 点 |
| C4 | `tau_x_tau_residual_x_general` | LA38:3462-3472 | 陈述出现 + sorry | 同 C1（HOL terminal.hl:3069 双生） | 形状 `probe_b_residual_general` 编译 |
| C5 | `quad_4680581274_a` | LA38:3662-3676 | 陈述出现（ineqP38 析取内两处 `taumXP38`）+ sorry | **按字仍为真**（DB+LP 级）；真身化后陈述不变 | 形状 `probe_b_quad_a` 编译；数值 [7] 6/6 样本 taum 对满足首析取支 |
| C6 | `taum_x_sym` | LA38:3693-3695 | 陈述出现 + sorry | **按字仍为真**（HOL terminal.hl:3752）。⚠️ 零桩/sorry 桩下此陈述**既不可证也不为假**（不透明常量两侧非 defeq）——真身化把它从"不可判"变"可证" | 形状 `probe_b_taum_x_sym` 编译；数值 [3] 4/4 点 |
| C7 | `taud_x_taum_x` | LA38:3698-3704 | 陈述出现（`taudXP38 ≤ taumXP38`）+ sorry | **按字仍为真**（HOL terminal.hl:3764，经 OWZLKVY4） | 形状 `probe_b_taud_x_taum_x` 编译；数值 [5] 6/6 点 |
| C8 | `OWZLKVY4` | LA38:3475-3481 | 陈述出现（`taudP38 ≤ taum`，`taudP38` :174 是**另一个** sorry 桩）+ sorry | **按字仍为真**；`taudP38` 真身 = `taud_t11`/`taudP19` 同体，须一并处置（同套件附带） | 形状 `probe_b_owzl` 编译；数值 [6] 6/6 点 |

**总判词：7/7 消费者换真身后按字仍为真，零 SF、零陈述微调。** LA19/LA38 的陈述文本已与
HOL 逐字对齐（本次逐行比对 pent_hex.hl:136-146 / terminal.hl:3069-3079 / 169-172 / 3752-3753 /
3764-3773 / 3149-3156 / 3791-3809）。

### 附带：套件内其余桩（建议同案顺带，范围须在章程里钉死）

- `taudXP38`（LA38:178）— C7 陈述消费；
- `flatTermXP38`（LA38:188）— C4 陈述消费；
- `taudP38`（LA38:174）— C8 陈述消费；
- `rhazimP38`（LA38:163）— 本案**不**消费（LA38:370 的 `dih_y ≤ rhazimP38` 是消费者，但不在 tau_x kit 内；留原 lane）。
- `tauqP38`（LA38:208）/`eulerAXP38`/`cayleyR*`/`enclosedP38` 等 — **范围外**（quad 簇/enclosed 簇自己的 anchor）。

## 3. 探针证据汇总（`logs/`）

| 探针 | 内容 | 结果 |
|---|---|---|
| `probe_a.lean` | import LA19；`probe_a_stub_literal_false`（平坦点 (4,4,4,12,4,4) 否定 C1 陈述） | RC=0，axioms = **标准三**（log 尾行） |
| `probe_a.lean` | `probe_a_flat_identity`：真身下 delta=0 分支在有理平坦点成立（假设 `π·const1 = sol0` = LA22 已证桥） | RC=0，**标准三** |
| `probe_b.lean` | import LA38；6 个形状 example（C3-C8 陈述以 `_t11` 真身代桩） | RC=0，6  sorry 警告（预期），零 error |
| `numprobe.py` | Python 高精度数值验证（公式逐字转录自 SphereKit/LA1）：[1] 残差恒等式 6/6 随机有效点（machine-eps）；[2] delta=0 有理平坦点（2e-8 差为 y 侧 √12 浮点伪影，x 侧恒等式为严格有理恒等式——`probe_a_flat_identity` 已符号证）；[3] taum_x_sym 4/4；[4] taum_taum_x 4/4；[5] taud_x_taum_x 6/6；[6] OWZLKVY4 6/6；[7] quad_a 析取 6/6；[8] 零桩假值确认 | `logs/numprobe.out` |

平坦点注记：x=(4,4,4,12,4,4) 满足 h9/h10/h11/h12（deltaX=0，deltaX4=−48，两旋转=48），
**全有理**——Lean 侧证明零超越输入（sqrt 12 在 dihY 内以 `√12·√12=12` 消去）。

## 4. 顺手可收清单（侦察车道不证；建议编排者另派小车道）

1. **negbranch 桥**（本案最重独立件）：`deltaX4 < 0 → dihXf = π + √(deltaX)·dihXDivSqrtdeltaPosbranch`
   （HOL merge_ineq.hl:963）。正支孪生 `p21k_dih_bridge`（PA21:10926，private）已证可仿；
   需 `matan` 负宗引理与 `pi2_sub_atn2`/`ATN2_RNEG` 的 Mathlib 桥（EulerAtn2Kit 多半有 ea1_* 形）。
2. **`dih_x_sym`/`dih_y_sym` Lean 孪生**（HOL nonlinear_lemma.hl:481/506）：deltaX/deltaX4 对换不变 +
   atn2 对换不变——C6（taum_x_sym）前置；纯结构小件，可独立先证。
3. **`rho_alt`/`rhoSqrtx` 形**：`rhoICD y = 1 + const1·(y−2)/0.52`（unfold `ly` + ring 级）。
4. **`yOfX taudX_t11 = taud_t11`（y 非负）**：functional_equation.hl:1425 的 taud_x_taud；
   LA19:1157-1163 已有 p19 版本，改名词即成。
5. **`taum_123` 形**（SphereKit `taum` 展开为 rhazim 三项 −(1+const1)π）：C3 前置；
   需 `solY = dihY+dihY(rot)+dihY(rot) − π`（sol_y_123 形）+ `lnazim` 换位——中等件。
6. **DB 引理核查**："2314572187"（OWZLKVY4 delta≥80 情形）是否已在 LA1 registry
   （"7796879304" 已确认在，LA1:1796）；"8346775862"/"8631418063"（EAR_DELTA_X4）。

## 5. 雷区（本车道实测 + 适用旧条）

1. **"假"与"不可证"必须分清**（本案新实证）：LA19 零桩 → 陈述**按字为假**（可 `¬` 证）；
   LA38 `:= sorry` 桩 → 陈述**不可证也不为假**（不透明常量两侧非 defeq，`probe_a` 式否定探针
   对 C3-C8 不适用）。报告/账本措辞别把两者混写。
2. **§7.1-25 孪生 def 勘正纪律**：树内 tau_x 链已有 ≥3 组孪生（`matan`/`matan_t11`、
   `rhoICD`/`rhoICD_t11`/LA1:186 `rho`、`dihXDivSqrtdeltaPosbranch`/`_t11`）。
   LA1:186 `rho`（rho_fun 形）与 `rhoICD` 语义相等（经 sol0=π·const1）但**不同 def**——
   真身化时必须指定唯一 canonical 宿主再统一改指，否则 rfl 级证明卡壳。
3. **matan 三分支**：`x = 0 / x > 0 / x < 0`。neg/posbranch 桥的 `matan ((4 x1 d)/d4²)` 宗由
   `d > 0` 保证为正，走 `if_pos`（参 ea1_matan_pos）；但 `d = 0` 分支（C1 第一分支）走
   `matan 0 = 1` 与 `atn2 0 y` 化简——探针 `ha1`/`ha2` 给出 `atn2 0 48 = π/2`、
   `atn2 0 (-48) = -π/2` 的可用 simp 形。
4. **`Real.sqrt` 不 definitional**：`√4 ≠ 2` by rfl；一律 `Real.sqrt_sq`/`Real.mul_self_sqrt` 引理化
   （探针全部如此处理）。x 侧陈述（C1/C4/C5/C7）避免 y 侧 sqrt：有理平坦点使 delta=0 分支零超越。
5. **§7.1-14 双检**：换真身 + 补证明的落库件必须 "`error` 计数 0 + `#print axioms`" 双检——
   本案 7 件目标全部是"陈述已在树、只换证明体"，落库时逐个跑 axioms。
6. **LA38:174 `taudP38` 别漏**：OWZLKVY4（C8）陈述消费的是它而不是 `taudXP38`；两个都是 sorry 桩。
7. **DB 依赖是 NEEDS-DB 级**：C2/C8 的完全证明需 nonlinear DB 引理（2314572187 / 7796879304 /
   8346775862 / 8631418063）——本章程只负责"换真身 + 套件内 7 件证明义务可达"，DB 部分仍挂
   NEEDS-DB（与 LA19 头部注记一致）。
8. 基准面：本车道**零主仓改动**，根面不变；探针在 /tmp + 快照，未入任何仓内路径。

## 6. 交付物

- `DELIVERY.md`（本文件）
- `charter-draft.md`（DEF-FIX 章程草案，p21-anchor 格式）
- `logs/probe_a.lean`、`logs/probe_a.log`（F1 假 + F1.5 真，均标准三）
- `logs/probe_b.lean`、`logs/probe_b.log`（6/6 形状编译）
- `logs/numprobe.py`、`logs/numprobe.out`（数值验证全绿）
- `logs/evidence-notes.md`（HOL 行段工作笔记）
