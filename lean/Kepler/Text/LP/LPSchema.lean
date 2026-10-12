/-
  Kepler/Text/LP/LPSchema — A12-C1 schema 冻结波（2026-10-12）：LP 终端记录的
  两层数据 schema——缺口 (b) 记录级钉定 + 缺口 (c) split 树数据编码。

  对象（docs/scouts/formal-lp-verify-scout.md §缺口地图 (b)(c)、§立项建议 C1 波）：
  - HOL `reference/flyspeck/formal_lp/hypermap/main/lp_certificate.hl`（:3-35
    schema）与 `prove_flyspeck_lp.hl`（:880-902 十型分发表）的 Lean 数据直译；
  - `Kepler.Text.LP.LPCert` :52-59 在案保真缺口（`LpTerminalCertified` 对 id
    不敏感）的钉定 schema 消解。

  ## 设计取舍（schema 冻结记录）

  1. **lane 文件选新模块，不 extend LPCert.lean**。LPCert 是手写语义核心
    （`LpTerminalCertified` 等冻结陈述所在），本模块是纯数据 schema 层；
    分开后 schema 演进永不触碰冻结陈述文件。叶文件在灌装波经产物模块
    （`Kepler.LP.T<id 消毒>`）传递 import 获得本模块全部名字，零 import 改动。

  2. **钉定粒度 = 类型索引（缺口 (b) 核心）**。`LpTerminalPin (id : String)`
    把记录 id 字面量放进类型的索引位：跨记录借见证 = 产物模块发射时的
    类型错误，不再是纪律承诺。附带 `graphId`/`ti` 字段与 `idCanonical`
    证明（`id = lpRecordId graphId ti`，decide 闭合），把记录进一步钉到
    「图 × DFS 终端序」——id 不再是自由字符串，而是从图 id 与 DFS 序规范
    推导的值（`lpRecordId` 与 `gen_lp_skeleton.py` 的 `f"{hid}_t{ti:04d}"`
    逐字符同构；本文件用 LPIds/LPLeaf 真实头两条 id 做 rfl 对账演示）。
    诚实边界：钉定保证「见证与 id 同模块发射、id 为 graph×ti 规范值」；
    「lp 数据 = 该记录真实族实例 LP」的语义面由 scout G5（族线性化定理）
    钉死，不在本层（LPCert NEEDS ② 在案）。

  3. **容器选型 = HOL 直译结构体 + List**（缺口 (c)）。`LpCaseTree` 逐字段
    对应 lp_certificate.hl（constraint_type / terminal_case / split_case /
    lp_certificate_case / lp_certificate），子树用 `List LpCaseTree`（与
    Marshal/parse_lpcert 同形，符合 socert 生成侧 chunk-literal 预算）；
    整数一律 `Int`（int64 ⊂ Int 无损）；split 型用 10 构造子归纳类型 +
    字符串往返（`name`/`ofName?`/`ofName_name`），把 HOL `verify_lp_case`
    的字符串分发表冻结成类型。树的旗标/计数/取载全部由**单一 DFS**
    （`dfsTerminals`）定义性派生——同源枚举天然对齐，杜绝多套遍历漂移，
    `ti` 的语义（DFS 前序终端序号）即 id 方案的 `t%04d` 分量。

  4. **ColMajor 接口形状**。pin 载荷 = socert `--col-major` 产物五元组
    `(lp, d, Y, D, G)` 原样（PilotCM204880136538 字段名），外加两个已证
    合取项（`check` = 产物 `dual_check`、`bound` = 产物 `gamma_lt`）——
    产物模板只需增发一个 `def pin`（见下手册第 2 步），叶闭合单行
    `LpTerminalPin.toCertified`，灌装波零 schema 改动。

  ## 工具链对齐（命名与流，不重写）

  - `pipeline/lp/parse_lpcert.py`：读器；`to_cert`/`terminal_info` 字段名
    与 §1 结构体一一对应（family/indices/coeffs ↔ constraint_type 三元组）。
  - `pipeline/lp/socert.py --col-major`：产物发射器；灌装波在
    `emit_col_major_sharded` 的 Assembly 模板**增发第 6 件 `def pin`**
    （手册模板），Data.lean 五元组字段名不变。
  - `lean/scripts/gen_lp_skeleton.py`：骨架生成器；`hypermap_id` = 本文件
    `lpHypermapId`、`collect_flags` = 本文件 `LpCaseTree.flags`、
    `f"{hid}_t{ti:04d}"` = 本文件 `lpRecordId`（三者均有 rfl 对账演示）。
    灌装波的叶改写 = 该叶占位行换单行转发（手册第 3 步），生成器本体
    增一个叶模板变体即可。

  ## 强机器日灌装操作手册（每条 bound 记录的完整步骤）

  1. **产物发射**：`socert.py --col-major` 从该记录终端 LP（SoPlex 精确
     对偶）发射 `Kepler.LP.T<id 消毒>/`（Data.lean + Assembly.lean，
     五定理形，PilotCM204880136538 在库样板）。
  2. **增发 pin**（产物 Assembly.lean 第 6 件，全机械：字面量 + 两个已证
     名 + 一句 decide；id 写错 = 类型错误，graph/ti 写错 = decide 失败）：
     ```lean
     def pin : Kepler.Text.LP.LpTerminalPin "<id>" where
       graphId := "<graphid>"
       ti := <ti>
       idCanonical := by decide
       lp := lp
       d := d
       Y := certY
       D := certD
       G := certG
       check := dual_check
       bound := gamma_lt
     ```
  3. **叶闭合**（LPLeaf*.lean 该叶：占位行换单行转发）：
     ```lean
     theorem lpT<id消毒> : LpTerminalCertified "<id>" :=
       LpTerminalPin.toCertified Kepler.LP.T<id消毒>.pin
     ```
  4. **对账自检**（灌装批脚本口径，非逐条手工）：叶 id ∈ LPIds 清单
     （生成器 1:1 已保证）；`#print axioms lpT<id消毒>` 只含 propext 与
     Quot.sound（标准三）；多终端图另验 `rootCase.countTerminals` = 该图叶数。
  5. **审计红线**：跨记录借见证在本 schema 下是类型错误；若见手工写出的
     五元组（非产物模块转发），即违反灌装纪律，整批打回。

  【infeasible 记录（189 条）】同构 5 步，走 §3 `LpInfeasPin` 外壳
  （C1b 定形 checker 后注入），见 §3 用法注释。

  【多终端图（G3 数据波，478 张）】每图一条 `LpGraphCert` 字面量 + 逐终端
  走上面 5 步；图级对账 = `rootCase.countTerminals` 与该图叶数一致。

  ## 演练记录（本波 /tmp 隔离实测，模板可照抄）

  - **产物模块第 6 件**：手册第 2 步模板逐字编译通过（五元组 + dual_check/
    gamma_lt + pin 全类型核；pin 构造零内核负担，decide 只算 id 字符串）；
  - **叶单行转发**：真实叶 import 条件下（LPIds + 产物模块、叶 namespace 内
    全限定转发）编译通过，`#print axioms lpT<id>` = 标准三；
  - **钉定有效性（反向实测）**：拿 `id = "toy_t0001"` 的 pin 给 `"toy_t0002"`
    的叶闭合，编译期类型错误（信息自释，灌装工人可直接定位）：
    `Application type mismatch: The argument LP.Tdemotoy.pin has type
    LpTerminalPin "toy_t0001" but is expected to have type
    LpTerminalPin "toy_t0002"`。
-/
import Kepler.Text.LP.LPCert

namespace Kepler.Text.LP

open Kepler.LP

/-! ## §0 记录 id 的规范形（canonical record id） -/

/-- 左补零到至少 4 位（fuel 版；`ti < 43078 < 2^16`，fuel 8 富余）。 -/
def lpPad4Aux : Nat → String → String
  | 0, s => s
  | k + 1, s => if 4 ≤ s.length then s else lpPad4Aux k ("0" ++ s)

/-- `ti` 的 4 位零填充十进制（`"%04d"` 语义；≥5 位自然溢出不截断）。 -/
def lpPad4 (n : Nat) : String := lpPad4Aux 8 (String.ofList (Nat.toDigits 10 n))

/-- 规范记录 id：`"<graphId>_t<ti:04d>"`，与 `gen_lp_skeleton.py` 的
`f"{hid}_t{ti:04d}"` 逐字符同构。 -/
def lpRecordId (graphId : String) (ti : Nat) : String := graphId ++ "_t" ++ lpPad4 ti

/-- 去掉字符表中全部 `_`（Python `str.replace("_", "")` 的字符表实现，
结构递归内核可求值）。 -/
def lpDropUnderscoreCs : List Char → List Char
  | [] => []
  | '_' :: t => lpDropUnderscoreCs t
  | c :: t => c :: lpDropUnderscoreCs t

/-- 首个单空格 token 的字符表（第一个 `' '` 即止；生成侧不变量：hypermap
串不以空格开头、token 单空格分隔）。 -/
def lpFirstTokenCs : List Char → List Char
  | [] => []
  | ' ' :: _ => []
  | c :: t => c :: lpFirstTokenCs t

/-- 图 id：hypermap 串的首 token 去下划线，与
`gen_lp_skeleton.py :: hypermap_id`（`hs.replace("_", "").split()[0]`）同构
（去 `_` 与分词可交换：`_` ≠ 空格，删 `_` 不动分词位置）。 -/
def lpHypermapId (hs : String) : String :=
  String.ofList (lpDropUnderscoreCs (lpFirstTokenCs hs.toList))

/-- 对账演示：4 位零填充的三个边界（0 / 两位数 / 5 位溢出）。 -/
theorem lpPad4_demo0 : lpPad4 0 = "0000" := rfl
theorem lpPad4_demo42 : lpPad4 42 = "0042" := rfl
theorem lpPad4_demo43077 : lpPad4 43077 = "43077" := rfl

/-- 对账演示（真实注册表头两条）：规范 id 复现 LPIds/LPLeaf 的真实 id——
`"229367313231_t0000"` = LPLeafEasy00.lean:18 首叶、
`"234511714565_t0000"` = LPIds.lean:19 首条 infeas。 -/
theorem lpRecordId_demo_easy : lpRecordId "229367313231" 0 = "229367313231_t0000" := rfl
theorem lpRecordId_demo_infeas : lpRecordId "234511714565" 0 = "234511714565_t0000" := rfl

/-- 对账演示：`lpHypermapId` 的分词与去下划线语义。 -/
theorem lpHypermapId_demo : lpHypermapId "123456789 12_34 5" = "123456789" := rfl

/-! ## §1 缺口 (c)：split 树数据 schema（HOL lp_certificate.hl 直译） -/

/-- 不等式族实例 = HOL `constraint_type = string * int list * int64 list`
的直译：族名 + 实例下标 + int64×10^p 精确整数乘子（`Int` ⊇ int64 无损；
乘子已含 10^precision 缩放，`precision` 在终端级记录）。 -/
structure LpIneqInst where
  /-- 不等式族名（如 `"y1_def"` / `"azim_sum"` / `"ineq107"`；HOL `get_ineqs` 键） -/
  family : String
  /-- 该族的实例下标（HOL `select_all` 选择子） -/
  indices : List Int
  /-- int64 精确整数乘子（HOL `transform_le_ineq` 的系数） -/
  coeffs : List Int

/-- 精度 p ∈ 3..7（HOL `precision_constant = 10^precision`；实测分布
scout §1.2：easy_1 {3:493, 4:488, 5:17, 6:2}、hard_2 {3:1, 4:15, 5:1}）。
若全量扫描发现出域 p，属 schema 修订事件（冻结波裁决），勿私自加构造子。 -/
inductive LpPrecision where
  | p3 | p4 | p5 | p6 | p7

namespace LpPrecision
/-- p 的自然数值。 -/
def toNat : LpPrecision → Nat
  | .p3 => 3 | .p4 => 4 | .p5 => 5 | .p6 => 6 | .p7 => 7
end LpPrecision

/-- 终端 case = HOL `terminal_case` 直译。 -/
structure LpTerminalCase where
  /-- 精度 p（3..7） -/
  precision : LpPrecision
  /-- 该终端 LP 是否不可行（true → Farkas 支，C1b 通道 + infeas 段） -/
  infeasible : Bool
  /-- 主约束（族实例列表） -/
  constraints : List LpIneqInst
  /-- 目标变量（HOL `target_variables`） -/
  targetVariables : List LpIneqInst
  /-- 变量界（HOL `variable_bounds`） -/
  variableBounds : List LpIneqInst

/-- split 型 = HOL `verify_lp_case` 的十支字符串分发表冻结为类型
（prove_flyspeck_lp.hl :880-902：tri/quad/pent/hex/edge/218/236/mid/high/
add_big；`218`/`236` 以 `s` 前缀合法定名）。 -/
inductive LpSplitType where
  | tri | quad | pent | hex | edge | s218 | s236 | mid | high | addBig

namespace LpSplitType
/-- HOL 侧字符串名（往返见 `ofName_name`）。 -/
def name : LpSplitType → String
  | .tri => "tri"     | .quad => "quad"
  | .pent => "pent"   | .hex => "hex"
  | .edge => "edge"   | .s218 => "218"
  | .s236 => "236"    | .mid => "mid"
  | .high => "high"   | .addBig => "add_big"

/-- 字符串 → 型（HOL/parse_lpcert 的 dispatch 键；未知名 `none`——
灌装批遇到即停，不得静默归类）。 -/
def ofName? : String → Option LpSplitType
  | "tri" => some .tri     | "quad" => some .quad
  | "pent" => some .pent   | "hex" => some .hex
  | "edge" => some .edge   | "218" => some .s218
  | "236" => some .s236    | "mid" => some .mid
  | "high" => some .high   | "add_big" => some .addBig
  | _ => none

/-- 往返定理：十型字符串分发表的完备性（每型 `rfl`）。 -/
theorem ofName_name (t : LpSplitType) : ofName? t.name = some t := by
  cases t <;> rfl
end LpSplitType

/-- split 节点 = HOL `split_case` 直译。 -/
structure LpSplitNode where
  /-- split 型 -/
  splitType : LpSplitType
  /-- split 面（顶点/边 id；HOL `split_face : int list`） -/
  splitFace : List Int

/-- 证书树 = HOL `lp_certificate_case` 直译：终端叶，或 split 节点 +
子 case 列表。非空性为生成侧纪律（HOL/本类型均不强制，与 Marshal 同形）；
灌装批生成器须断言 split 子列表非空。 -/
inductive LpCaseTree where
  /-- 终端叶 -/
  | terminal : LpTerminalCase → LpCaseTree
  /-- split 节点 + 子 case 列表（HOL `Lp_split of split_case * list`） -/
  | split : LpSplitNode → List LpCaseTree → LpCaseTree

namespace LpCaseTree

/-- DFS 终端序枚举：`(ti, 终端载荷)` 表，`ti` = 全树 DFS 前序的终端序号
（与 `gen_lp_skeleton.py :: collect_flags` 的枚举序一致——记录 id 的
`t%04d` 分量由此定义）。**单一 DFS 同源枚举**：旗标/计数/取载全部由本表
定义性派生（见 `flags`/`countTerminals`/`terminalAt`），天然对齐无漂移。 -/
def dfsTerminals (t : LpCaseTree) : List (Nat × LpTerminalCase) :=
  go t 0
where
  /-- 单棵子树的 DFS（`i` = 进入时的终端计数起点） -/
  go : LpCaseTree → Nat → List (Nat × LpTerminalCase)
    | .terminal c, i => [(i, c)]
    | .split _ cs, i => goList cs i
  /-- 兄弟列表的 DFS（ti 随已枚举终端数推进） -/
  goList : List LpCaseTree → Nat → List (Nat × LpTerminalCase)
    | [], _ => []
    | c :: rest, i => go c i ++ goList rest (i + (go c i).length)

/-- infeasible 旗标表（= `collect_flags` 直译；第 i 项即 `ti = i` 的旗标）。 -/
def flags (t : LpCaseTree) : List Bool :=
  t.dfsTerminals.map (fun p => p.2.infeasible)

/-- 终端计数（HOL `count_terminals` 对应量；定义性 = `flags.length`）。 -/
def countTerminals (t : LpCaseTree) : Nat := t.flags.length

/-- 不可行终端计数（G1/G7 的 189 对账口径）。 -/
def countInfeasible (t : LpCaseTree) : Nat := t.flags.countP (fun b => b)

/-- `ti` → 终端载荷（越界 `none`；记录 id ↔ 树位的对账接口）。 -/
def terminalAt (t : LpCaseTree) (i : Nat) : Option LpTerminalCase :=
  (t.dfsTerminals[i]?).map (fun p => p.2)

/-- `ti` → 规范记录 id（越界 `none`；图 × DFS 序 ↔ id 的对账函数）。 -/
def recordIdAt (graphId : String) (t : LpCaseTree) (i : Nat) : Option String :=
  if i < t.countTerminals then some (lpRecordId graphId i) else none

/-- 单一 DFS 派生的对账不变量：旗标表长度 = 终端计数（定义性成立；
本定理名供灌装批审计引用）。 -/
theorem flags_length (t : LpCaseTree) : t.flags.length = t.countTerminals := rfl

end LpCaseTree

/-- 每图证书 = HOL `lp_certificate` 直译。 -/
structure LpGraphCert where
  /-- hypermap 串（图 L 的编码；首空白 token 去 `_` = 图 id，
  `lpHypermapId` 同构） -/
  hypermapString : String
  /-- 根 case（终端或 split 树） -/
  rootCase : LpCaseTree

/-! ### §1 树 schema 演示（全 rfl；玩具 quad，不对应任何真实图）

HOL `split4_lemma` 五析取形 → quad 节点挂 5 终端支，第 4 支（ti=3）
infeasible——对账面 = 计数 / 旗标表 / 越序取载 / 规范 id 全链。 -/

section TreeSchemaDemo

def toyQuadChildren : List LpCaseTree :=
  [.terminal ⟨.p4, false, [], [], []⟩,
   .terminal ⟨.p4, false, [], [], []⟩,
   .terminal ⟨.p4, false, [], [], []⟩,
   .terminal ⟨.p4, true, [], [], []⟩,
   .terminal ⟨.p4, false, [], [], []⟩]

def toyQuad : LpCaseTree := .split ⟨.quad, [1, 2, 3, 4]⟩ toyQuadChildren

theorem toyQuad_count : toyQuad.countTerminals = 5 := rfl
theorem toyQuad_infeas : toyQuad.countInfeasible = 1 := rfl
theorem toyQuad_flags : toyQuad.flags = [false, false, false, true, false] := rfl
theorem toyQuad_at3 : toyQuad.terminalAt 3 = some ⟨LpPrecision.p4, true, [], [], []⟩ := rfl
theorem toyQuad_at9 : toyQuad.terminalAt 9 = none := rfl
theorem toyQuad_idAt3 : toyQuad.recordIdAt "toygraph" 3 = some "toygraph_t0003" := rfl
theorem toyQuad_idAt9 : toyQuad.recordIdAt "toygraph" 9 = none := rfl
theorem toyQuad_flags_length : toyQuad.flags.length = toyQuad.countTerminals := rfl

end TreeSchemaDemo

/-! ## §2 缺口 (b)：记录级钉定（id 索引的认证包装） -/

/-- **单条 bound 终端记录的认证包装**（缺口 (b) 钉定机制；LPCert :52-59
在案缺口的 schema 消解）。记录 id 是类型的索引位：跨记录借见证 = 产物
模块发射时的类型错误，id 不再是可自由套用的谓词参数。

对账字段：`graphId`/`ti`（图 id × DFS 终端序）+ `idCanonical`（id = 规范
推导值，decide 闭合）把记录钉到「图 × 树位」，与 §1 `recordIdAt` 同一口径。
载荷字段 = socert `--col-major` 产物五元组 `(lp, d, Y, D, G)` 原样
（PilotCM204880136538 字段名）+ 两个已证合取项（`check` = 产物
`dual_check`、`bound` = 产物 `gamma_lt`）。 -/
structure LpTerminalPin (id : String) where
  /-- 图 id（hypermap 首 token 去 `_`，`lpHypermapId` 同构） -/
  graphId : String
  /-- DFS 终端序（记录 id 的 `t%04d` 分量） -/
  ti : Nat
  /-- id 规范性钉定：id = `"<graphId>_t<ti:04d>"`（产物模块发射时
  decide 闭合；id 与 graph/ti 任一写错即拒） -/
  idCanonical : id = lpRecordId graphId ti
  /-- 终端 LP（列主序；socert `--col-major` 的 `lp : LPCM`） -/
  lp : LPCM
  /-- 对偶树深（`2^d ≥ b.length`） -/
  d : Nat
  /-- 整数化对偶向量（`y = Y/D`） -/
  Y : List Int
  /-- 整数化分母 -/
  D : Nat
  /-- 上界分子（`γ = G/D`） -/
  G : Int
  /-- 内核列主序弱对偶 checker 合取项（产物模块 `dual_check`） -/
  check : checkDualCMTF lp d (ITree.ofList Y d) Y D G = true
  /-- 终端条件 `γ < 12`（产物模块 `gamma_lt`） -/
  bound : (G : Int) < 12 * (D : Int)

/-- **钉定形单条语义谓词**（灌装波的叶闭合目标形；冻结陈述
`LpTerminalCertified` 的钉定升级）。 -/
def LpTerminalCertifiedPinned (id : String) : Prop := Nonempty (LpTerminalPin id)

/-- 钉定形 → 冻结陈述的转发（叶闭合单行；43,078 叶的机械改写目标，
模板见模块头手册第 3 步）。 -/
theorem LpTerminalPin.toCertified {id : String} (p : LpTerminalPin id) :
    LpTerminalCertified id :=
  ⟨p.lp, p.d, p.Y, p.D, p.G, p.check, p.bound⟩

/-- 谓词形转发（`LpTerminalCertifiedPinned` 的消费位，LPAll 级升级用）。 -/
theorem LpTerminalCertifiedPinned.toCertified {id : String}
    (h : LpTerminalCertifiedPinned id) : LpTerminalCertified id := by
  obtain ⟨p⟩ := h
  exact p.toCertified

/-- 注册表量化（钉定形；镜像 `LPCert.AllLpTerminalCertified`）。 -/
def AllLpTerminalCertifiedPinned (ids : List String) : Prop :=
  ∀ id ∈ ids, LpTerminalCertifiedPinned id

/-- 量化转发：钉定形注册表 → 冻结注册表（灌装批的验收面）。 -/
theorem AllLpTerminalCertifiedPinned.toCertified {ids : List String}
    (h : AllLpTerminalCertifiedPinned ids) : AllLpTerminalCertified ids :=
  fun id hid => (h id hid).toCertified

/-! ### §2 灌装模板演示（1 叶样例改写演示，scout C1-②）

用 ColMajor 的 `exCM` 小样（9 行玩具 LP + 已证内核 checker）走通
「pin 构造 → 叶转发」全链——这是强机器日产物模块第 6 件（`def pin`）+
叶单行闭合的逐字段样板。`"toy_t0000"` 是显式玩具 id，不对应任何真实
记录；真实灌装的 `check`/`bound` 来自产物模块的 `dual_check`/`gamma_lt`。 -/

section PinSchemaDemo

def toyPin : LpTerminalPin "toy_t0000" where
  graphId := "toy"
  ti := 0
  idCanonical := by decide
  lp := exCM
  d := 2
  Y := [1, 1]
  D := 3
  G := 9
  check := exCM_flat_check
  bound := by decide

/-- 全链演示：钉定包装 → 冻结陈述的单行转发（= 真实叶的闭合形）。 -/
theorem toyPin_demo : LpTerminalCertified "toy_t0000" := toyPin.toCertified

end PinSchemaDemo

/-! ## §3 缺口 (b) 的 infeasible 支外壳（C1b 接口预制件，189 条） -/

/-- **infeasible 记录的钉定外壳**（C1b 波 = scout G1 通道的 id 机制
预制件）。Farkas 形 checker 在 Lean 侧是新机制，其谓词形状由 C1b 定形后
作 `check` 参数注入；钉定机制（id 类型索引 + graph/ti 对账 + 字面量
decide）与 bound 支（§2）完全同构，避免 C1b 另造第二套 id 机制。

用法（C1b 收口路径，四步）：
1. 定义内核 Farkas checker 与数据载体（`data` 形如 §2 五元组 + 射线载荷）；
2. 别名定形：`def LpTerminalInfeasiblePin (id : String) :=
     LpInfeasPin id <data> <checker谓词>`；
3. 真语义替换 `LPCert.LpTerminalInfeasibleCertified` 的平凡占位
  （改动落在 LPCert 冻结文件，须编排者拍板——陈述面不动、只换定义体）；
4. 转发/量化件照 §2 镜像（`toCertified` 两枚 + 注册表量化两枚）。 -/
structure LpInfeasPin (id : String) (data : Type) (check : data → Prop) where
  /-- 图 id -/
  graphId : String
  /-- DFS 终端序 -/
  ti : Nat
  /-- id 规范性钉定（同 `LpTerminalPin.idCanonical`） -/
  idCanonical : id = lpRecordId graphId ti
  /-- Farkas 证书数据（C1b 定形；预计为整数化对偶射线 + 线性条件组
  载体，具体形状 C1b 定） -/
  cert : data
  /-- C1b 定形的内核 checker 合取项 -/
  hcheck : check cert

/-- 钉定形 infeasible 语义谓词（C1b 定形 `data`/`check` 后即用；
到冻结陈述 `LpTerminalInfeasibleCertified` 的升级件待真语义落地后镜像
§2——占位是平凡的，升级件的验收口径 = 非平凡性，见 LPCert 退化防线）。 -/
def LpTerminalInfeasibleCertifiedPinned (id : String) (data : Type)
    (check : data → Prop) : Prop := Nonempty (LpInfeasPin id data check)

end Kepler.Text.LP
