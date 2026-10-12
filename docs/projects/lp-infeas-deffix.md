# DEF-FIX 章程：LP infeasible 通道占位真语义化（2026-10-12，编排者拟）

> 依据：C1 立项（2026-10-12 用户批，docs/scouts/formal-lp-verify-scout.md §立项建议）
> + C1b 交付报告 ③ 精确 diff 建议。闸模式 = `GATE_MODE=DEF-FIX`，`DF_PATCH=本文件`。
> 净 sorry 配额：**0**（本章程范围零新增 sorry；LPLeafInfeas 系既有 190 处
> deferred-compute 骨架 sorry 不在本章程范围，照旧等 C3 数据波闭合）。

## 1. 对象与 HOL 锚

- 冻结 def：`LpTerminalInfeasibleCertified (LPCert.lean:73)`，现体 `:= True`
  （2026-10-08 T2 波占位，:65-72 头注退化防线在案：不得经占位平凡闭合为
  「已证」口径）。
- HOL 语义锚：`reference/flyspeck/formal_lp/prove_flyspeck_lp.hl:287-348`
  infeasible 支（Farkas 非负乘子组合：列加权和为零 ∧ rhs 加权和 < 0；不加
  lnsum，乘子 Nat 直译）——C1b 车道已逐行对账并落地为
  `LPSchemaFarkas.farkasCheck`（soundness 已证）。

## 2. 破坏面分析（编排者 2026-10-12 实查，DEF-FIX 前置已满足）

- `LpTerminalInfeasibleCertified` 的全部消费叶 = `LPLeafInfeas*.lean` 系
  190 处定理，**全部为开放 `sorry` 骨架**（机器生成，docstring 记
  deferred-compute），无一处平凡闭合现绿证明 → 换体零破坏。
- 注册表 `AllLpTerminalInfeasibleCertified`（LPCert:82）量化于该 def，
  随 def 换体自动获得真语义，无独立消费点。

## 3. 改动范围（三文件，净 sorry 0）

1. **新建 `lean/Kepler/Text/LP/LPFarkas.lean`**（仅依赖 Mathlib 基础）：
   从 LPSchemaFarkas §1-§2 **逐字搬入**内核五件
   `LpFarkasCore`/`coreColSum`/`coreRhsSum`/`coreShape`/`farkasCheck`
   及 soundness 引理族 + `getD_cons_zero'`/`getD_cons_succ'` 两 private 备件
   （下沉原因：LPCert ← LPSchema ← LPSchemaFarkas import 链方向使 LPCert
   不可见内核，循环 import 禁止）。
2. **`LPCert.lean`**：头部加 `import Kepler.Text.LP.LPFarkas`；`:73` 定义体
   替换为
   `def LpTerminalInfeasibleCertified (_id : String) : Prop := ∃ c : LpFarkasCore, farkasCheck c = true`
   （陈述面/签名不动，仅 def 体；id 钉定语义留在 LpTerminalPin 层，与本层
   存在量化分工符合 C1a 架构）。
3. **`LPSchemaFarkas.lean`**：§1-§2 改为引用 LPFarkas（防孪生，逐字节同名）；
   `LpTerminalInfeasiblePin.toCertified` 证明体 `trivial` → 见证形
   （`⟨p.cert.core, p.hcheck.2⟩` 方向）；`AllLpTerminalInfeasiblePinned.toCertified`
   相应真化；`toInfeasExists` 转为非平凡性验收件。

## 4. 验收

- 三文件 + 依赖根 `lake build` 零 error；净 sorry 配额 0（新增行禁词零命中）；
- `LpTerminalInfeasiblePin.toCertified` 公理面 = 标准三零 sorryAx；
- 反向回归锚：`toyNeg`（列和≠0）仍被 `farkasCheck` 拒绝；
- 叶文件 LPLeafInfeas\* 不在本章程范围（零触碰，其 sorry 等数据波）。
