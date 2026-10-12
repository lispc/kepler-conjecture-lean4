/-
  Kepler/Text/LP/LPSchemaFarkas — A12-C1b：189 条 infeasible 终端记录的
  Farkas 钉定外壳对接（scout 缺口 (a)，2026-10-12）。2026-10-12 DEF-FIX
  （章程 docs/projects/lp-infeas-deffix.md）起，内核五件 + soundness 引理
  族 + 两 private 备件已逐字下沉 `Kepler/Text/LP/LPFarkas.lean`（本文件
  经 import 引用、全名不变，防孪生），本模块保留：缩放衔接（LpPrecision
  形）、钉定外壳（§4）、demo 与真实记录切片（§3/§5）。

  C1b 波原文（lane 文件 = 新模块，import Kepler.Text.LP.LPSchema）：本模块
  只落内核、正确性、钉定别名（LPSchema §3 四步路径的 ①②④）。2026-10-12
  DEF-FIX 波（编排者章程 lp-infeas-deffix.md）：① 已下沉 LPFarkas.lean、
  ③ 已落地（LPCert :73 定义体换 `∃ c : LpFarkasCore, farkasCheck c = true`，
  冻结陈述面不动）、④ `toCertified` 证明体换见证形——四步路径全部关闭。

  ## 语义定形（HOL 对账记录）

  对象 = HOL `formal_lp/hypermap/main/prove_flyspeck_lp.hl:287-348`
  `prove_flyspeck_lp_step1` 的 infeasible 支（`std_flag`、族线性化、
  `lnsum_ineqs` 叠加为 bound 支专属——infeasible 支**不加** lnsum，
  :332 直接跳过）。HOL 机器逐行：
  1. 每条约束 `(name, indices, c)`：族定理实例化为实数线性不等式，乘
     int64 乘子 `c`（`transform_le_ineq`，`REAL_POS'` + `REAL_LE_LMUL'`：
     乘子非负自然数）；逐条 fold-add（`add_step'`：两边相加）；
  2. variable_bounds / target_variables 同样以非负乘子并入（var_table
     消去只是逐变量对消的**计算技巧**，`LIN_F_ADD_SING_{L,R}CANCEL`，
     语义上仍是同一非负组合的一部分）；
  3. 整体乘 `precision_constant = 10^p`（`mul_step`，:331；p ∈ 3..7）；
  4. 终态 `lin_f [] ≤ --&n` 且 `n ≠ 0`（`FINAL_INEQ` :40-41 +
     `NUM_EQ0_HASH_CONV`）——即 `0 ≤ -n ≤ -1 < 0` 矛盾。

  因此 **Farkas 形状的精确语义**：证书 = 一组非负整数乘子 `mⱼ`，使得
  LP 不等式组 `A·x ≤ b`（行 = constraints ∪ bounds ∪ targets 解析后的
  缩放整系数形式）的非负组合满足
  **`∀ 列 i：Σ_j mⱼ·A[j][i] = 0`（系数恒等式）且 `Σ_j mⱼ·bⱼ < 0`**——
  即组合导出 `0 ≤ 负数`。任一实/有理赋值若满足全部行，则按行非负缩放
  求和得 `0 ≤ Σ mⱼ bⱼ < 0`，矛盾。这就是下沉件 `farkasCheck`
  （现 `Kepler.Text.LP.LPFarkas`，DEF-FIX 下沉）的谓词。

  ## 设计取舍（逐条记账）

  1. **乘子选 `Nat`**：与 HOL 乘子的 num 类型逐字对应（`transform_le_ineq`
     的非负性由类型承担，checker 无需额外合取项；HOL `REAL_POS'` 同理）。
  2. **系数/右端选 `Int`**：10^p 缩放后全部数据整型化（与 LPSchema §1
     `LpIneqInst.coeffs` 的 int64×10^p 口径一致）；内核 checker 纯 Int
     结构递归，`decide` 可求值（内核不能归约 Rat——ColMajor 已实测）。
     缩放的精确性论证显式给出：`decimal_scale_le_iff`（DECIMAL 系统与
     缩放整系数系统等价，两边同乘 10^p > 0）+ `farkasCheck_scaled_sound`
     （缩放系统不可行 ⟸ 整数 checker 通过）。
  3. **checker 形状选 Bool（`farkasCheck : LpFarkasCore → Bool`）**，对接
     `LpInfeasPin` 的 `check : data → Prop` 槽位时以 `farkasCheck c.core =
     true` 作 Prop（`LpInfeasCheck`）——照 `LpTerminalPin.check =
     checkDualCMTF … = true` 的 §2 house 模式；decide 灌装两件式。
  4. **数据选密集行主序 `List (List Int)`（`LpFarkasCore`）而非
     LPCM/ITree 稀疏列主序**：infeasible 终端记录小（easy_1 实测最小
     161 实例，行均值 ~47），密集 checker 内核代价 = nvars×rows 次 Int
     乘加，decide 充裕；Farkas 语义需要 A 与 b 显式在场，密集形使
     正确性定理（`farkas_combo_eval`：Σ 交换）保持纯 ℤ/ℚ 线性代数。
     若 C3 实测 decide 预算不足，升级路径 = 载体换 LPCM+ITree（沿用
     ColMajor 两教训），checker 形状与钉定外壳不变。
  5. **变量表 = 展开侧平坦编号**：`nvars` 列的顺序由 C3 发射侧的族解析
     层定义（HOL var_table 的 term 键在 Lean 侧无对象层，族解析属覆盖
     桥 G5）；checker 只看系数矩阵，对编号约定不敏感。
  6. **行集 = constraints ∪ variableBounds ∪ targetVariables**：三段在
     HOL 机器里同入非负组合（var_table 消去不改语义），故证书核不区分
     来源；记录原案保留在 `LpInfeasCert.case`（`LpTerminalCase` 全量
     字面量）供对账，`LpInfeasCheck` 并入 `case.infeasible = true`
     （HOL 分发表按记录旗标选 Farkas 支的镜像）。

  ## LPSchema §3 四步路径状态（2026-10-12 DEF-FIX 落地后全关）

  - ① 数据载体 + 内核：**已下沉** `Kepler.Text.LP.LPFarkas`
    （`LpFarkasCore`/`coreColSum`/`coreRhsSum`/`coreShape`/`farkasCheck`
    + soundness 引理族 + 两 private 备件，逐字搬运防孪生；依赖
    `LpPrecision` 的缩放衔接两件留在本模块 §2）；
  - ② 别名定形：§4 `LpTerminalInfeasiblePin id :=
    LpInfeasPin id LpInfeasCert LpInfeasCheck`（LPSchema §3 外壳原样
    实例化，未造第二套 id 机制）；
  - ③ **已落地**（2026-10-12 DEF-FIX，章程 lp-infeas-deffix.md §3.2）：
    LPCert 头部加 `import Kepler.Text.LP.LPFarkas`，`LPCert.lean:73` 的
    `def LpTerminalInfeasibleCertified (_id : String) : Prop := True`
    已替换为
    `def LpTerminalInfeasibleCertified (_id : String) : Prop :=`
    `  ∃ c : LpFarkasCore, farkasCheck c = true`
    （id 钉定语义留在 LpTerminalPin 层，与本层存在量化分工符合 C1a
    架构）；
  - ④ 转发/量化镜像：§4 照 §2 模式四件（`toCertified`/`toInfeasExists`/
    `AllLpTerminalInfeasiblePinned` + 两条 `to…`），另附
    `LpTerminalInfeasibleCertifiedPinned`（LPSchema §3 泛型壳）桥；
    `toCertified` 证明体已换见证形，`toInfeasExists` 转为非平凡性
    验收件。

  ## 实测记录（本波 /tmp 隔离探针 + 本模块 demo 段）

  - 内核 decide：`toyInfeas`（1 变量 2 行）/`toyInfeas2`（3 变量 4 行，
    10^3 缩放实数语义不可行系统）通过、`toyNeg`（列和非零）拒绝；
  - 真实记录数据面：`reference/flyspeck/formal_lp/glpk/binary/easy_1.dat`
    第 392 图（id `234511714565_t0000`）经 `pipeline/lp/parse_lpcert.py`
    读器解码（/tmp/fk_probe4.py）：precision=3、infeasible、27 constraints
    + 0 targets + 15 bounds、161 实例，乘子全为非负 int64（Farkas 系数
    在案：如 `azim_sum_neg [0,1,3,4] [1000,195,196,143]`）；本模块 §5
    落其头部切片字面量 + rfl 对账。**边界（诚实记账）**：解析行
    （族名 → 线性式实例）属覆盖桥（G5），C1b 不含；故全链端到端
    （真实行 + 真实乘子 → decide）留待 C3 数据波，本波 checker 层测试
    = 玩具全链 + 真实记录 schema 对账。
-/
import Kepler.Text.LP.LPFarkas
import Kepler.Text.LP.LPSchema

namespace Kepler.Text.LP

/-! ## §2 缩放精确性衔接（LpPrecision 形；内核与正确性引理族已逐字下沉
`Kepler.Text.LP.LPFarkas`——DEF-FIX 2026-10-12，章程
docs/projects/lp-infeas-deffix.md。防孪生：本文件不再持有内核副本，
经 import 引用全名不变的名字；依赖 LPSchema 侧类型 `LpPrecision` 的
两件留在本处） -/

/-- `LpPrecision` 的 p ∈ 3..7 为正（decide 闭合）。 -/
theorem LpPrecision.toNat_pos (p : LpPrecision) : 0 < p.toNat := by
  cases p <;> decide

/-- 缩放不可行性推论（LpPrecision 形）：记录精度 p3..p7 直连。 -/
theorem farkasCheck_scaled_soundP (d : LpFarkasCore) (h : farkasCheck d = true)
    (p : LpPrecision) (w : Nat → ℚ) :
    ¬ ∀ j < d.rows.length,
      (∑ i ∈ Finset.range d.nvars,
        ((d.rows.getD j []).getD i 0 : ℚ) / (10 : ℚ) ^ p.toNat * w i)
        ≤ ((d.rhs.getD j 0 : ℚ) / (10 : ℚ) ^ p.toNat) :=
  farkasCheck_scaled_sound d h p.toNat w

/-! ## §3 内核 demo（decide 实测；玩具 id，不对应任何真实记录） -/

/-- 玩具例 1（最小）：`x ≤ 1 ∧ x ≥ 2`（10^3 缩放整系数；乘子全 1）。 -/
def toyInfeas : LpFarkasCore := ⟨1, [[1000], [-1000]], [1000, -2000], [1, 1]⟩

theorem toyInfeas_check : farkasCheck toyInfeas = true := by decide

/-- 玩具例 1 语义使用：任何 ℚ 赋值都违反某行（正确性定理直用）。 -/
theorem toyInfeas_nosol (w : Nat → ℚ) :
    ¬ ∀ j < toyInfeas.rows.length,
      (∑ i ∈ Finset.range toyInfeas.nvars,
        ((toyInfeas.rows.getD j []).getD i 0 : ℚ) * w i)
        ≤ ((toyInfeas.rhs.getD j 0 : ℚ)) :=
  farkasCheck_sound toyInfeas toyInfeas_check w

/-- 玩具例 2（3 变量 4 行，10^3 缩放）：`x0 ≤ 3 ∧ x1 ≤ 5 ∧ x2 ≤ 100 ∧
x0+x1+x2 ≥ 109` 无可行（max 和 = 108 < 109；乘子全 1：
`3000+5000+100000-109000 = -1000 < 0`）。 -/
def toyInfeas2 : LpFarkasCore :=
  ⟨3, [[1000, 0, 0], [0, 1000, 0], [0, 0, 1000], [-1000, -1000, -1000]],
    [3000, 5000, 100000, -109000], [1, 1, 1, 1]⟩

theorem toyInfeas2_check : farkasCheck toyInfeas2 = true := by decide

/-- 反例：checker 拒绝非证书（列和非零 `1000 ≠ 0`）。 -/
def toyNeg : LpFarkasCore := ⟨1, [[1000]], [1000], [1]⟩

theorem toyNeg_check : farkasCheck toyNeg = false := by decide

/-! ## §4 钉定外壳对接（四步路径 ②④；③ = DEF-FIX，见模块头） -/

/-- ① 记录级证书数据：记录原案（LPSchema §1 `LpTerminalCase` 全量字面量，
C3 发射侧按 parse_lpcert 解码灌入，§5 切片演示对账形状）+ 内核核。
`check` 槽位谓词 `LpInfeasCheck` 并入记录旗标对账
（HOL `verify_lp_certificate` 按旗标分发到 Farkas 支的镜像）。 -/
structure LpInfeasCert where
  /-- 记录原案（precision / infeasible 旗标 / constraints / targets / bounds） -/
  case : LpTerminalCase
  /-- Farkas 内核核（解析行系统 + 乘子） -/
  core : LpFarkasCore

/-- check 谓词定形（对接 `LpInfeasPin` 的 `check : data → Prop` 槽；
照 §2 `checkDualCMTF … = true` 的 Bool-as-Prop house 模式）。 -/
def LpInfeasCheck (c : LpInfeasCert) : Prop :=
  c.case.infeasible = true ∧ farkasCheck c.core = true

/-- ② 钉定别名定形：id 类型索引 + graph/ti 对账 + `idCanonical` decide，
与 bound 支 `LpTerminalPin` 完全同构（LPSchema §3 外壳原样实例化，
零第二套 id 机制）。 -/
abbrev LpTerminalInfeasiblePin (id : String) :=
  LpInfeasPin id LpInfeasCert LpInfeasCheck

/-- 钉定形 infeasible 语义谓词（灌装叶闭合目标形；§2
`LpTerminalCertifiedPinned` 的 infeasible 镜像）。 -/
def LpTerminalInfeasiblePinned (id : String) : Prop := Nonempty (LpTerminalInfeasiblePin id)

/-- ④ 转发到冻结陈述（2026-10-12 DEF-FIX 真语义化落地：
`LpTerminalInfeasibleCertified = ∃ c : LpFarkasCore, farkasCheck c = true`，
本件即非平凡见证转发——pin 的证书核 + checker 合取项直接构成 ∃ 见证）。 -/
theorem LpTerminalInfeasiblePin.toCertified {id : String} (p : LpTerminalInfeasiblePin id) :
    LpTerminalInfeasibleCertified id := ⟨p.cert.core, p.hcheck.2⟩

/-- ④ 非平凡性验收件（DEF-FIX 已落地）：pin 给出**非平凡**证书见证
（记录原案 + checker 合取项）；与 `toCertified`（见证形转发）互补，
189 叶闭合链的验收口径经此件逐条对账。 -/
theorem LpTerminalInfeasiblePin.toInfeasExists {id : String} (p : LpTerminalInfeasiblePin id) :
    ∃ c : LpInfeasCert, c.case.infeasible = true ∧ farkasCheck c.core = true :=
  ⟨p.cert, p.hcheck⟩

/-- §3 泛型壳桥：专用钉定形 → 泛型 `LpInfeasPin` 谓词形（defeq 直通）。 -/
theorem LpTerminalInfeasiblePinned.toGeneric {id : String} (h : LpTerminalInfeasiblePinned id) :
    LpTerminalInfeasibleCertifiedPinned id LpInfeasCert LpInfeasCheck := h

/-- 泛型壳桥的逆（同一 Nonempty 的两端；灌装工人按便利面取用）。 -/
theorem LpTerminalInfeasiblePinned.ofGeneric {id : String}
    (h : LpTerminalInfeasibleCertifiedPinned id LpInfeasCert LpInfeasCheck) :
    LpTerminalInfeasiblePinned id := h

/-- 钉定形 → 冻结陈述（谓词形转发；§2 `LpTerminalCertifiedPinned.toCertified`
的 infeasible 镜像；DEF-FIX 落地后转发即非平凡语义）。 -/
theorem LpTerminalInfeasiblePinned.toCertified {id : String}
    (h : LpTerminalInfeasiblePinned id) : LpTerminalInfeasibleCertified id := by
  obtain ⟨p⟩ := h
  exact p.toCertified

/-- ④ 注册表量化（钉定形）。 -/
def AllLpTerminalInfeasiblePinned (ids : List String) : Prop :=
  ∀ id ∈ ids, LpTerminalInfeasiblePinned id

/-- ④ 量化转发 A：钉定形注册表 → 冻结注册表（`AllLpTerminalInfeasibleCertified`；
DEF-FIX 已落地，随 `toCertified` 见证形转发即真语义）。 -/
theorem AllLpTerminalInfeasiblePinned.toCertified {ids : List String}
    (h : AllLpTerminalInfeasiblePinned ids) : AllLpTerminalInfeasibleCertified ids :=
  fun id hid => (h id hid).toCertified

/-- ④ 量化转发 B：钉定形注册表 → 逐条非平凡见证（DEF-FIX 验收口径：
189 条每条给出数据 + checker 合取项；非平凡性 = 该 ∃ 的 witness 承载
真实记录的行系统与乘子）。 -/
theorem AllLpTerminalInfeasiblePinned.toInfeasExists {ids : List String}
    (h : AllLpTerminalInfeasiblePinned ids) :
    ∀ id ∈ ids, ∃ c : LpInfeasCert, c.case.infeasible = true ∧ farkasCheck c.core = true := by
  intro id hid
  obtain ⟨p⟩ := h id hid
  exact p.toInfeasExists

/-! ## §5 灌装演示 + 真实记录切片 -/

/-! ### 玩具 pin 全链（id 显式玩具，不对应任何真实记录；C3 发射模板） -/

section PinDemo

/-- 玩具 pin：五步全机械（idCanonical/hcheck 均 decide/rfl 闭合）。
真实灌装（C3）：`cert.case` = parse_lpcert 解码的记录全量字面量、
`cert.core` = 族解析层发射的缩整行系统 + 记录乘子，模板照 §2 手册。 -/
def toyInfPin : LpTerminalInfeasiblePin "toyinf_t0000" where
  graphId := "toyinf"
  ti := 0
  idCanonical := by decide
  cert := ⟨⟨.p3, true, [], [], []⟩, toyInfeas⟩
  hcheck := ⟨rfl, toyInfeas_check⟩

/-- 全链演示 A：钉定形谓词成立。 -/
theorem toyInfPin_demo : LpTerminalInfeasiblePinned "toyinf_t0000" := ⟨toyInfPin⟩

/-- 全链演示 B：非平凡见证（DEF-FIX 落地后即叶闭合形）。 -/
theorem toyInfPin_fwd :
    ∃ c : LpInfeasCert, c.case.infeasible = true ∧ farkasCheck c.core = true :=
  toyInfPin.toInfeasExists

/-- 反向实测（钉定有效性）：错 id 的 pin 构造即编译期失败
（`idCanonical : "toyinf_t0001" = lpRecordId "toyinf" 0` 的 decide 拒绝；
§2 演练同款）。 -/
example : ¬ ("toyinf_t0001" = lpRecordId "toyinf" 0) := by decide

end PinDemo

/-! ### 真实记录切片（easy_1#392 = `234511714565_t0000`；对账面） -/

section RealRecordSlice

/-- 记录切片：precision=3、infeasible=true、constraints 头两条、bounds
头一条。数值逐字来自 `binary/easy_1.dat` 第 392 图 t0000 的 Marshal
解码（/tmp/fk_probe4.py，经 pipeline/lp/parse_lpcert.py 读器）；演示
`LpInfeasCert.case` 的灌入形状，**非**证书数据。 -/
def realSlice : LpTerminalCase :=
  { precision := .p3, infeasible := true,
    constraints :=
      [{ family := "azim_sum_neg", indices := [0, 1, 3, 4], coeffs := [1000, 195, 196, 143] },
       { family := "rhazim_sum", indices := [1, 3, 4], coeffs := [195, 196, 143] }],
    targetVariables := [],
    variableBounds :=
      [{ family := "azim_lo", indices := [5, 7, 10], coeffs := [16, 16, 16] }] }

theorem realSlice_precision : realSlice.precision = .p3 := rfl
theorem realSlice_infeasible : realSlice.infeasible = true := rfl
theorem realSlice_c0 :
    (realSlice.constraints[0]?).map (fun x => x.family) = some "azim_sum_neg" := rfl
theorem realSlice_c0m0 :
    (realSlice.constraints[0]?).bind (fun x => x.coeffs[0]?) = some 1000 := rfl
theorem realSlice_b0 :
    (realSlice.variableBounds[0]?).map (fun x => x.family) = some "azim_lo" := rfl

end RealRecordSlice

end Kepler.Text.LP
