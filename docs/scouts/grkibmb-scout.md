# grkibmb-scout — "GRKIBMB 尖锐边界组" 侦察报告（零改动只读侦察）

> 2026-10-12 侦察 lane 交付。纪律：零 .lean 改动、零 git 写操作、未跑 lake build。
> 所有 file:line 经 grep/sed 实测核对；数值经手算复核（mm1≈1.0121 等以树内注释
> 与定义交叉验证）。

**核心结论先行**：

① **"GRKIBMB" 是拼写变体，全仓库实体为 GRKIBMP 切片**：字符串 `GRKIBMB` 在
lean/、reference/、pipeline/ 全部 **0 命中**，仅存在于 HANDOFF.md:193 与
milestones doc（§0/§2）两处文档；PLAN.md:197 同一短语写作"GRKIBMP 尖锐边界组"。
实体 = PA21 bank 的 **GRKIBMP A V2 + GRKIBMP B V2** 两条（IdLists.lean:48-49），
其中 **B V2 是尖锐边界件**（STATUS.md:189/209："GRKIBMP B V2 有真反例叶=
尖锐边界组"，`pipeline/interval/out/residue16.txt` 第 11 条）。

② **Lean 侧形状已 pin 死，只欠 bank 本体两枚证明**：调度件
`GRKIBMP : grk_bank → GRKIBMP_concl`（PackingAuto21.lean:1040）**已闭合**
（wave 1，2026-09-29，commit 1591e1c1）；两条 bank 陈述显式盒式
（PA21:364/371）；唯一债务 = `nliGrkBank : grk_bank := sorry`
（Assembly.lean:258）。消费端 TSKAJXY_2（PA21:6883）与 TSKAJXY capstone
（PA21:6928）都已写好、只等 bank。

③ **尖锐性是真数学，但极小**：B V2 化简后是**单变量**因式分解——
`f(y) = (√8−y)·[(√8+y)y/24 − 4·mm1/(π·√8)]`，y∈[2hplus,√8]，等号恰在
y=√8 角点（HOL sharp.hl:246 `GRKIBMP_B_V2_SHARP` 12 行证 =0）。区间求解器
关不掉它**不是**因为不等式难，而是因为真下确界 =0（在角点取到），任何含角点
子盒都无法与 0 分离——纯 branch-and-bound 结构性不可能，角点条带必须符号化处理。
手写 Lean 证明路线（因式分解 + 单调性 + mm1<4/3 数值种子）估 **200-450 行**。

④ **A V2 根本不是真数学**：非尖锐（无 Sharp tag，0.008 舒适余量），
bb_arb 已闭合（bbarb_results2.txt：`GRKIBMP_A_V2 rc=0 leaves=21 nodes=41`，
dReal unsat）——纯证书发射+粘合数据债（~0.3-0.5 车道）；且因 lfun 是线性式
（PA2:46），A V2 也可全解析手证（~120-300 行），完全绕开证书机器。

⑤ **量级裁决**：全组 = **~350-750 行 Lean ≈ 0.5-1 批 ≈ 1-2 车道**，是三件
"真数学"中最小、准备度最高的一件（调度/消费/陈述全部在树且闭合，纯插件式
填证）。**裁决：真数学，但"伪装偏大"——B V2 是小型真数学，A V2 是工程/数据债；
尖锐边界之名暗示的难度在解析因式分解下消解**。建议三件真数学中**最先做**。

---

## §0 定位与消费链

### 0.1 名字考古（问题 1：它是谁）

| 来源 | 写法 | 位置 |
|---|---|---|
| HANDOFF.md:193 | GRKIBMB 尖锐边界组 | 三件真数学清点 |
| milestones-and-risks-2026-10-12.md §0/§1/§2 | GRKIBMB（3 处，"体量未探明"） | 用户指令对象 |
| PLAN.md:197 | **GRKIBMP** 尖锐边界组 | 同一清点的另一份 |
| STATUS.md:189/209 | GRKIBMP **B V2** 尖锐边界组 | 具体到条目 |
| residue16.txt:11 | GRKIBMP B V2 | 16 条真残余清单 |

`grep -rn GRKIBMB`：lean/ 0、reference/ 0、pipeline/ 0——**GRKIBMB 不是任何
HOL/Lean 标识符**，是 GRKIBMP（+B V2 语境）的文档层转写讹误。
"组"的严格口径 = **2 枚 bank 条目**（A V2 + B V2，merge_ineq.hl:3795
`add_hyp` 序）；B V2 是其中唯一尖锐件。

### 0.2 HOL 侧原文（问题 1）

- **GRKIBMP A V2**：`ineq.hl:1520-1535`。盒 `[2, 2hplus]×{1}⁵`，结论
  `y_of_x (gamma2_x1_div_a_v2 (h0cut y1)) y1…y6 > 0.008`，doc "gamma2 at
  least 0.008 per azim along critical edge"，tags `[Marchal;…;Branching;Split[0]]`
  ——**无 Sharp tag**。
- **GRKIBMP B V2**：`ineq.hl:1537-1552`。盒 `[2hplus, sqrt8]×{1}⁵`，结论
  `y_of_x (gamma2_x1_div_a_v2 (&0)) y1…y6 >= &0`，doc "gamma2 nonnegative in
  general"，tags 含 **`Sharp; Eps 1.0e-8`**——尖锐+1e-8 余量（数据库外部验证口径）。
- **函数定义**：`nonlin_def.hl:341-347`
  `gamma2_x_div_azim_v2 m x = (8−x)·√x/24 − (2·(2mm1/π)·(1−√x/√8) − (8mm2/π)·m·lfun(√x/2))`；
  `gamma2_x1_div_a_v2 m = promote1_to_6(…)`（六变量提升，**忽略 y2..y6**）；
  `functional_equation.hl:1237-1242 nonf_gamma2_x1_div_a_v2`（y_of_x 剥壳）。
- **GRKIBMP 定理**（HOL）：`merge_ineq.hl:3794-3816`，~16 行：按
  `2hplus ≤ y` 分 case，长边侧 `h0cut y = 0`（`Optimize.h0cutB` +
  `h0_lt_hplus`）后退到 B V2。 Lean 侧逐行镜像已闭合（PA21:1040-1057）。
- **结论式**：`GRKIBMP_concl = !y. 2 ≤ y /\ y ≤ sqrt8 ==> 0 ≤
  gamma2_x_div_azim_v2 (h0cut y) (y*y)`（`TSKAJXY2.hl:73-75`）。
- **尖锐角点件**：`sharp.hl:246-259 GRKIBMP_B_V2_SHARP`：角点
  `y_of_x (gamma2_x1_div_a_v2 0) sqrt8 1 1 1 1 1 = 0`，4 步 rewrite +
  REAL_ARITH，12 行。sharp.hl 全文件 429 行、含 6 枚尖锐角点定理
  （OMKYNLT/gamma4f_delta0/TSKAJXY_RIBCYXU/TSKAJXY_IYOUOBF_V2/
  GRKIBMP_B_V2/QZECFIC_WT0_CORNER）+ atn/acs 辅件——Flyspeck 作者自己
  对"sharp 不等式在角点取等"的符号化处理范本。

### 0.3 Lean 侧落点（问题 1/2）

| 资产 | 位置 | 状态 |
|---|---|---|
| `bank_GRKIBMPAV2`（0.008 < …，箭头形） | PA21:364-367 | 陈述 pin 死，**证明债** |
| `bank_GRKIBMPBV2`（0 ≤ …，**非严格**） | PA21:371-375 | 陈述 pin 死，**证明债（尖锐）** |
| `grk_bank := A ∧ B` | PA21:391 | 纯定义 |
| `GRKIBMP : grk_bank → GRKIBMP_concl` | PA21:1040-1057 | **真证闭合**（1591e1c1） |
| `yOfX` 剥壳 defeq 桥 `p21_nonf_gamma2x1DivAV2_yOfX` | PA21:1033-1035 | **闭合**（rfl） |
| `h0cut`/`gamma2x1DivAV2`/`gamma2_x_div_azim_v2` 定义 | PA21:169/198/153 | 闭合 |
| `p21_h0_lt_hplus`（h0=1.26 < hplus=1.3254） | PA21:1022 | 闭合 |
| Assembly 骨架 `nliGrkBank : grk_bank` | Assembly.lean:258 | **唯一 sorry** |
| 装配 `nliPackNonlinearNonOx3q1h` 四分量显式装配 | Assembly.lean:288-289 | 真推导，无独立债务 |

**消费面（问题 2）**——两路，全在 e2e 可达路径上：
1. **PA21 文本侧**：`TSKAJXY_2`（mcell2 分支，PA21:6856-6885，:6883 直接
   `GRKIBMP (proj_grk_bank hnl) …`）→ `TSKAJXY` capstone（PA21:6907-6930，
   :6928 `hgrk : GRKIBMP_concl` 喂 `TSKAJXY_034`）→ Marchal 2-cell 非负性
   （gammaX ≥ 0，critical edge）→ `Kepler.Text.TSKAJXY_statement`（PA2:845）。
   注意 TSKAJXY_034 本体另是一枚 sorried giant（PA21:1884-1886，HOL
   TSKAJXY2.hl:92-722 ~600 步）——**独立债务，不在本组**。
2. **Assembly 接口侧**：`nliGrkBank` → `pack_nonlinear_non_ox3q1h`（81 条
   四分量装配，Assembly:288）→ T1 单根接口 `nonlinearInequalities` 六分量
   展开（Assembly §2a'）→ 主陈述非线性接口。

堵住的口子：81 条银行记账中"1c 两条"（Assembly.lean:279 A11 重记账注）、
residue16 之 1/16、PA21 grk 切片 2/19。

## §1 HOL 证明解剖（问题 3）

**数据库条目本身在 HOL 无内嵌证明**（Cfsqp/Clusterlp/Branching 外部区间/
分支验证 + `Eps 1.0e-8` 口径），HOL 只证"条目 ⇒ 结论"的调度（GRKIBMP 16 行）
与角点取等（sharp.hl 12 行）。**尖锐的数学内容一句话**：B V2 的被证函数在盒
角点 y1=√8（x=8）处**恰好取 0**（(8−x) 因子与 (1−√x/√8) 因子同时归零），
因此闭合盒上的下确界 =0、不等式无正slack——任何含角点的区间子盒下界必触 0，
分支定界无限细分，bb_arb 报"真反例叶"（rc=1）；这是**求解器编码现象**
（bb_arb 需严格分离），不是 Lean 陈述问题——Lean bank 已是非严格 `0 ≤`
（PA21:375），与 HOL `>= &0` 忠实一致。STATUS:209"我们把 ≥ 加强成严格 >"
指求解层编码，**不适用于 Lean bank**。

## §2 数学内核与 Lean 路线（问题 3/4）

### 2.1 B V2 手证路线（推荐，绕开证书机器）

m=0 杀掉 mm2 项，y2..y6 被 promote 忽略（[1,1] 盒 `le_rfl` 收），x=y1²、
√x=y1（y1>0），得**单变量**：

```
f(y) = (8−y²)·y/24 − (4·mm1/π)·(1−y/√8)
     = (√8−y) · [ (√8+y)·y/24 − 4·mm1/(π·√8) ]
```

- 盒 `[2hplus, √8]` 上 `√8−y ≥ 0`；
- 方括号对 y 递增（两支均增），min 在 y=2hplus=2.6508：
  `(2.8284+2.6508)·2.6508/24 ≈ 0.6052`；
- `4·mm1/(π√8) ≈ 0.4556`（mm1≈1.0121，PA16:81 注）——**余量 ≈0.15，舒适**。

Lean 步骤：(a) 沿 `p21_nonf_gamma2x1DivAV2_yOfX` rfl 剥壳 + `ring` 因式分解
（~40-80 行）；(b) 方括号单调性 `Real.add_le_add`/`mul_le_mul`（~30-60 行）；
(c) 常数种子 **mm1 < 4/3**（见 2.3）；(d) 收尾 nlinarith（~40-80 行）。
**估 200-450 行**。STATUS 的"ε 余量/弱编码"是对求解器说的；对 Lean bank
解析路线无必要——纯间隔法关不掉角点，符号条带反正躲不掉。

### 2.2 A V2 双路线（任选）

- **解析**（估 120-300 行）：h0cut 按 `2h0=2.52` 分两支。m=1 支（y∈[2,2.52]）：
  lfun 是**线性式** `lfun h = (h0−h)/(h0−1)`（PA2:466），lfun(y/2) ∈ [0,1]
  初等；m=0 支（y∈[2.52,2.6508]）：同 2.1 分解，端点 f≈0.027-0.033 > 0.008，
  余量 ~3×。全 elementary。
- **证书**（估 0.3-0.5 车道 + 微算力）：bb_arb 已 21 叶闭合，走现成
  `emit_lean.py` 分片管线 + §2a 查表粘合（对 PA21 rest 叶量产同款动作，
  可搭车）。

### 2.3 在库 kit 覆盖度逐项判断

| kit | 判定 |
|---|---|
| PA21 Merge_ineq 银行 81 条/19 切片 | **直接复用**——grk 2 条即切片成员；陈述/序/箭头形全就位 |
| GRKIBMP 调度件套件（rfl 剥壳桥/h0cutB/h0<hplus） | **直接复用**——bank 证明用同一套剥壳与盒收口 |
| 常数定义 mm1/sol0/tau0/hplus/h0/lfun/lmfun | **全部在树且精确**（PA2:424-469；hplus=1.3254、h0=1.26 是字面量；`m1_minus_12m2 : mm1−12·mm2=√(1/2)` PA19:422 精确恒等式） |
| mm1 上界 | **缺口**——现成只有 `HJKDESR1a_1cell : mm1 < π√2/3≈1.481`（PA20:2721），不够（需 <1.3444）。需加 **mm1 < 4/3**：⟺ `sol0·(3√8+80) < 16π` ⟺ `arcsin(1/3) > (π/2−9/16)/3 ≈ 0.3361`，sin-Taylor 一步（`sin t ≤ t−t³/6+t⁵/120`，0.3375 处 ≈0.3311 < 1/3，余量足）+ PA20 HJKDESR1a 同款 arccos/π-bounds/nlinarith 技术（**可直接照抄其证明骨架**，PA20:2715-2760）。估 30-80 行 |
| cellParams kit | **不适用**（bank 盒式不等式，非 cell 参数案） |
| G4 证书管线（emit_lean/CertG/FillParams） | **B V2 不需要**（结构上关不掉尖锐角点）；A V2 可选搭车 |
| pack_nonlinear_rest（62 bank pin 死等证书） | **平行不阻塞**——grk 切片是其 19 消费切片的 2 条，B V2 不卡证书数据（解析路线零证书）；与 62 条 rest 的唯一交点 = §2a 查表粘合样式 |

### 2.4 缺口子清单（问题 4）

| # | 缺口 | 估行 | 性质 |
|---|---|---|---|
| G1 | `mm1 < 4/3`（sol0/arcsin 数值种子） | 30-80 | 小真数学（照抄 HJKDESR1a 骨架） |
| G2 | B V2 因式分解+单调+收尾 → `bank_GRKIBMPBV2` | 200-450 | **核心真数学** |
| G3 | A V2 两支解析（或证书搭车） → `bank_GRKIBMPAV2` | 120-300（或 0.3-0.5 车道） | 可选解析 / 数据债 |
| G4 | Assembly `nliGrkBank := ⟨G3, G2⟩` 转真 + 记账注更新 | <10 | 机械 |

## §3 量级、风险与立项（问题 5）

- **总量**：~350-750 行 Lean ≈ 0.5-1 批（批=700-1300 行）≈ **1-2 车道**；
  单波可交付（G1+G2+G4 一波；G3 可同波或并行搭证书量产车）。
- **最大不确定点**：(a) G1 数值种子的 Taylor/常数链细节（已给两条可行阈值
  路线，余量已验算，风险低）；(b) 因式分解后 ring/nlinarith 在 `Real.sqrt 8`
  形态下的摩擦（树内 `mi_sqrt8_eq`/`sqrt8_2` 同类先例多，风险低）；
  (c) A V2 若走证书路线，emit 管线排队即外部依赖（解析路线消除此依赖）。
- **范围纪律**：residue16 另有 4 条疑似同病（QZECFIC wt0 / wt0 corner /
  TSKAJXY-RIBCYXU / TSKAJXY-IYOUOBF，sharp.hl 各有 HOL 角点定理可参照）——
  **不要**顺势扩入本组；单独立项侦察后再定。
- **波次建议**：
  - **W1（本组主体，1 车道）**：G1 → G2 → G4，`nliGrkBank` 转真，
    grk sorry 断流，81 条记账 1c 收窄为 1 条（A V2）。
  - **W2（可选并行，0.3-0.5 车道）**：A V2 解析收尾（或证书搭车），
    1c 清零。
- **排序建议**：三件真数学中**最先**做本组（体量最小、准备度最高、
  纯插件式）；其次 PA24 B2 支撑面引理（~200-300 行，自设计）；
  pivot 反向 k=3/4 最后（~200-400 行但逆向重造 + GIANT 深水区邻居）。

## §4 裁决（对三件真数学排序的影响）

**GRKIBMB（=GRKIBMP 切片尖锐边界组）是"真数学"，但是小型真数学，
且一半（A V2）实为工程/数据债。** "尖锐"的恐惧来自区间求解器的结构性失
败模式，不是陈述难度：B V2 因式分解后是一条单变量、单调、余量 15% 的
初等不等式。它**不**伪装成大债——真正的信号是：调度件与全部消费端已在树
且闭合，债务收敛于两枚 bank 本体。三件真数学中性价比最高，建议置顶。
