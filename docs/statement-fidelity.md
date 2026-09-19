# statement-fidelity.md — 陈述保真度对照（Phase 1 交付）

目的（PLAN.md §4 Phase 1）：论证 `lean/Kepler/Statement.lean` 中的
`Kepler.the_kepler_conjecture` 与 Flyspeck 的 `the_kepler_conjecture`
语义一致，防止"证错了定理"。

对照基准：`reference/flyspeck` @ `1ce0353`
`text_formalization/general/the_main_statement.hl:19-24`：

```
the_kepler_conjecture <=>
  (!V. packing V
         ==> (?c. !r. &1 <= r
                      ==> &(CARD(V INTER ball(vec 0,r))) <=
                          pi * r pow 3 / sqrt(&18) + c * r pow 2))
```

本项目（`lean/Kepler/Statement.lean`）：

```lean
theorem the_kepler_conjecture :
    ∀ V : Set Space3, Packing V →
      ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
          Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2
```

## 逐项对照

| Flyspeck (HOL Light) | 本项目 (Lean 4) | 说明 |
|---|---|---|
| `V : real^3 -> bool` | `V : Set Space3`，`Space3 := EuclideanSpace ℝ (Fin 3)` | HOL Light 的 `real^3` 即带欧氏度量的 ℝ³；Mathlib 的 `EuclideanSpace ℝ (Fin 3)` 是其标准模型，`dist` 同为欧氏距离。唯一表示差异，无语义差别。 |
| `packing V`（`general/sphere.hl:425`） | `Packing V` | 逐字相同：`∀ u v ∈ V, dist u v < 2 → u = v`（单位球心两两距离 ≥ 2）。 |
| `CARD (V INTER ball (vec 0, r))` | `(V ∩ Metric.ball 0 r).ncard` | 两者对无限集都约定为 0；在 `Packing` 假设下该集合必有限（见下），此时两者都等于真实计数。 |
| `&(CARD ...)` | `((...).ncard : ℝ)` | 自然数到实数的强制转换。 |
| `ball (vec 0, r)` | `Metric.ball 0 r` | 均为**开**球。 |
| `pi * r pow 3 / sqrt(&18)` | `Real.pi * r ^ 3 / Real.sqrt 18` | HOL 的 `sqrt(&18)` 是实数开方；`Real.sqrt 18`（`18 : ℝ`）相同。 |
| `?c. !r. &1 <= r` | `∃ c : ℝ, ∀ r : ℝ, 1 ≤ r` | 量词顺序与约束相同；`c` 均无符号约束。 |

## 有限性补注

HOL Light 的 `CARD` 与 Lean 的 `Set.ncard` 对无限集均返回 0。
在 `Packing V` 下 `V ∩ ball 0 r` 必为有限集——`Kepler.Packing.finite_inter_ball`
已给出**完整证明**（无 sorry）：球心两两距离 ≥ 2 ⇒ 半径 1 的开球两两不交
且全部落入 `ball 0 (r+1)`，体积计数给出 `(T.card : ℝ) ≤ (r+1)³`。
因此两个系统中的计数都等于真实球心数，无"无限集退化为 0"的语义陷阱。

## 与 Flyspeck 另一形态的关系

`text_formalization/packing/pack_defs.hl:24` 另有一个体积比形态
`kepler_conjecture`（含 `saturated V` 与球体积比），Flyspeck 用
`kc_imp_the_kc`（`the_main_statement.hl:82-107`）由它推出计数形态。
Flyspeck 最终审计（`general/audit_formal_proof.hl:49`）以计数形态
`the_kepler_conjecture` 为终点定理，本项目与之对齐。

## 结论

除 `real^3` ↔ `EuclideanSpace ℝ (Fin 3)` 这一标准表示差异外，
陈述逐项对应；无常数篡改（`π`、`√18`、指数 3、2、阈值 `1 ≤ r` 均一致）。
已知偏差：无。

---

## 附录：Phase 6 装配脊柱的折算点（2026-09-19，P6-B 复审登记）

`Kepler/Assembly.lean`（设计 `docs/phase6-spine.md`）的接口陈述经 P6-B 逐条
对照 HOL 原文复审通过。以下折算点已知晓并记录，消除接口 sorry 时必须随附补证：

1. **`the_nonlinear_inequalities` 量化折算**（用户批准 2026-09-19）：HOL 的 993 条
   字面合取 → Lean 的"ID 清单（数据）+ `AllCertified` 量化命题"。**当前六个 ID 清单
   为空、`CertifiedIneqHolds := True` 占位**——脊柱冻结的是形状；填实由 G4 负责，
   届时每条 ID 到字面不等式的映射表本身也是保真对象，须逐条抽查。
2. **`FAN 0 V (ESTD V)` 显式前提**：HOL `hypermap_of_fan` 为全函数，Lean
   `hypermapOfFan` proof-parameterized；消 LP 接口 sorry 时需补
   `Contravening V → FAN 0 V (ESTD V)`（surrounded_node 合取项给出）。
3. **dart 编码差**：Lean 用 `dart1OfFan`（不含孤立 dart），HOL 用 `dart_of_fan`；
   Contravening 语境下无孤立点，两编码一致，消 sorry 时补证。
4. **`IsHypermapOfList` 规格级镜像**：`hypermap_of_list` 的构造属 P6-C；
   落地后须证 `IsHypermapOfList L (hypermapOfList L)` 并展开回 HOL 原句。
5. **镜像语义**：`iso_fgraph`（允许镜像，improper）与 HOL 一致；hypermap 层
   `Iso` 保定向——两层之间必须是 ELLLNYZ 形析取桥（镜像分支走镜像 fan 绕行：
   `hypermap_of_fan_neg` + `contravening_negative`），属 Phase 5 capstone 内部债务。
6. **`CARD`/`sum` 的无限集约定**：均取 0，与 HOL 垃圾值约定一致。
