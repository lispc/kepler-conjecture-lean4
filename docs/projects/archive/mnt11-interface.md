# mnt11 ↔ G4 证书对接规格（2026-09-21）

## 1. 现状

- **Lean 侧**：`Kepler.Text.main_nonlinear_terminal_v11`（LocalAuto1.lean:815）=
  黑盒 `Prop := sorry`。被 20+ appendix 结论定理作为前提消费
  （`CUXVZOZ_concl` 等），并经 `nonlinear_imp_lp_main_estimate_p16`（LA16）
  供给 `lp_main_estimate`——即主定理脊柱的 **Phase 4 唯一主叶子**。
- **HOL 原件**：`terminal.hl:24-44`——由 `mk_all_ineq` 从 Ineq 数据库按
  `Main_estimate` 标签生成的 993 条非线性不等式巨型合取。每条形如
  `!y1..y6. box 约束 ==> 不等式`。
- **G4 侧**（wip/g4-emit，Kimi）：bb_arb/BBTreeGD 证书 + 内核闭合，已有
  7 案例端到端；prep 92 家族重求解中（求解层口径 39%）；43,078 LP 持久化
  重跑并行。

## 2. 对接需求（G4 交付物 → Lean 落点）

每条不等式（以 HOL Ineq ID 为键）需要一张**内核闭合的 Lean 定理**：

```lean
theorem ineq_<ID> : ∀ y1 y2 y3 y4 y5 y6 : ℝ, <box 约束> → <不等式体> := by
  <G4 证书发射：native_decide/decide 链或 BBTreeGD 评估定理>
```

键对齐要求：
1. **ID 空间**：与 HOL `Ineq` 数据库的标签一一对应（`Main_estimate` 标签
   子集 = 993 条；G4 案例名如 `C1965189142`/`QITNPEA_3725403817` 需映射表）。
2. **box 约束形态**：必须与 terminal.hl:24-44 逐条一致（区间端点、开闭）。
3. **公理面**：标准三公理 + （如需）scoped native_decide 例外
   （DECISIONS.md 2026-08-10）。

## 3. Lean 侧落地形态（建议）

采用 Assembly §1c 已批准的注册表折算，mnt11 从黑盒改注册表：

```lean
def idsMainNonlinearTerminalV11 : List String := [...993 个 ID...]
def CertifiedIneqHolds (id : String) : Prop := <按 ID 查表展开为字面不等式>
def main_nonlinear_terminal_v11 : Prop := AllCertified idsMainNonlinearTerminalV11
```

填实 = 每条 `CertifiedIneqHolds id` 由 G4 证书定理闭合（`exact ineq_<ID>`）。
ID 清单可由 `mk_all_ineq`/terminal.hl 机械导出（脚本化）。

## 4. 待两侧确认

- [ ] G4：证书定理命名约定 + ID↔案例映射表的产出形式
- [ ] G4：prep 92 家族重求解的覆盖对齐（39% 口径下哪些家族进 mnt11 首批）
- [ ] Lean：ID 清单导出脚本（terminal.hl → idsMainNonlinearTerminalV11）
- [ ] Lean：`CertifiedIneqHolds` 查表机制（String → Prop 的 finite 注册；
      用 `match id` 或 decidable 键表）
