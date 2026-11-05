# RECON — la11-mksimplex-cont-w1

基线 HEAD `b89ee8b45bc9ecbe197dd9e0551423326a9e8873`（`b89ee8b4`）。
目标文件 `lean/Kepler/Text/LocalAuto11.lean`（1853 行 @HEAD）。
HOL 正本 `lean/scripts/local/PQCSXWG.hl:214-300`。

## 1. `mkSimplex1_p11` 的定义形状

`lean/Kepler/Text/LocalAuto11.lean:1263`（@HEAD）：

```lean
noncomputable def mkSimplex1_p11 (v0 v1 v2 : V3) (x1 x2 x3 x4 x5 x6 : ℝ) : V3 :=
  let uinv := 1 / upsX x1 x2 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  let d5 := deltaX5 x1 x2 x3 x4 x5 x6
  let d4 := deltaX4 x1 x2 x3 x4 x5 x6
  let vcross : V3 :=
    (WithLp.toLp 2 (crossProduct (WithLp.ofLp (v1 - v0))
      (WithLp.ofLp (v2 - v0))) : V3)
  v0 + uinv • ((2 * Real.sqrt d) • vcross + d5 • (v1 - v0) + d4 • (v2 - v0))
```

拆解后的算子清单（与 HOL 的 `mk_simplex1` 逐槽对齐）：

| HOL 槽 | Lean 渲染 | 连续性来源 |
|---|---|---|
| `uinv = &1 / ups_x x1 x2 x6` | `1 / upsX (x1 t) (x2 t) (x6 t)` | `ContinuousWithinAt.div` + `upsX ≠ 0`（= 目标件的 `hups`） |
| `d = delta_x x1..x6` | `deltaX (x1 t) … (x6 t)` | 多项式，`unfold deltaX; fun_prop` |
| `d5 = delta_x5` | `deltaX5 …`（SphereKit canonical） | 多项式，`unfold deltaX5; fun_prop` |
| `d4 = delta_x4` | `deltaX4 …`（SphereKit canonical） | 多项式，`unfold deltaX4; fun_prop` |
| `sqrt d` | `Real.sqrt (deltaX …)` | `ContinuousWithinAt.sqrt`（Mathlib `sqrt` 处处连续） |
| `cross (v1-v0) (v2-v0)` | `WithLp.toLp 2 (crossProduct (ofLp …) (ofLp …))` | 分量公式 + `PiLp.continuous_ofLp/toLp` |
| `v0 + uinv • (...)` | 同形 | `ContinuousWithinAt.add` / `.smul` |

关键事实：`mkSimplex1_p11` 的 let 链在 `fun t => …` 里可用 **`rfl`** 一次性展开
（probe 已验证，见 `pD.lean` / `Work.lean` 的 `hfun`），因此不需要 `simp only [mkSimplex1_p11]`
的脆弱重写。

## 2. 同文件里已真证的连续性样板

`grep -n 'ContinuousWithinAt' lean/Kepler/Text/LocalAuto11.lean` → 22 行，其中**样板只有
§B 的 8 条 sqrt-compose 套件**（:1283-1326，全部真证、body 就是 `hf.sqrt`）：

```
1283  CONTINUOUS_WITHIN_SQRT_COMPOSE_p11        (hf : ContinuousWithinAt f s a) …
1288  CONTINUOUS_AT_SQRT_COMPOSE_p11
1298  REAL_CONTINUOUS_WITHIN_SQRT_COMPOSE_p11
1303  REAL_CONTINUOUS_AT_SQRT_COMPOSE_p11
1312  CONTINUOUS_WITHINREAL_SQRT_COMPOSE_p11
1317  CONTINUOUS_ATREAL_SQRT_COMPOSE_p11
1325  REAL_CONTINUOUS_WITHINREAL_SQRT_COMPOSE_p11
1330  REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE_p11
```

**结论**：文件内没有「多元多项式 + 向量值」的连续性样板；`POLY_CONT_TAC` 的 HOL 手搓
`CONTINUOUS_MUL/ADD/SUB` 递归在 Lean 侧由 `fun_prop` 直接接管（`unfold <def>; fun_prop`
在 6 元多项式 `deltaX/deltaX4/deltaX5/upsX` 上实测通过）。跨乘积（HOL `CONTINUOUS_CROSS`）
文件内无对应物，需自备（见 §3）。

## 3. `Collect_geom2.NOT_COL_EQ_UPS_X_POS` 的桥 — 不可达，需就地重推

`grep -rn 'NOT_COL_EQ_UPS_X_POS' lean/Kepler/Text/` 只有 4 处，全是**注释/docstring**：

```
lean/Kepler/Text/LocalAuto18.lean:1382   -- Merge_ineq.DIHV_DIH_X and Collect_geom2.NOT_COL_EQ_UPS_X_POS
lean/Kepler/Text/LocalAuto11.lean:1645   `Collect_geom2.NOT_COL_EQ_UPS_X_POS`; DISCHARGES
lean/Kepler/Text/EulerSimplexGeom.lean:293   collect_geom2.hl:1420 `NOT_COL_EQ_UPS_X_POS`
lean/Kepler/Text/LocalAuto21.lean:1085   -- distances), Collect_geom2.NOT_COL_EQ_UPS_X_POS, Merge_ineq.dih_gt_pi2
```

真正的 Lean 桥是 `Kepler.Text.EulerSimplexGeom.ea2_upsX_pos_iff`（:294）：

```lean
theorem ea2_upsX_pos_iff (a b c : V3) :
    0 < upsX (dist a b ^ 2) (dist a c ^ 2) (dist b c ^ 2) ↔ ¬ Collinear3 a b c
```

**但 `Kepler.Text.EulerSimplexGeom` 不在 `LocalAuto11` 的 import 闭包里**：

```
LocalAuto11 → LocalAuto2 → {Polytope, Fan, TopologyFan, PackingAuto2, PackingAuto3, PackingAuto5, PackingAuto20}
            → LocalAuto4 → {Polytope, PackingAuto2, PackingAuto5, Fan}
            + Kepler.Geom.Aff + Kepler.Geom.Azim + Mathlib
PackingAuto20 → LocalAuto38Bridge → {Geom.LuneVolume, SphereKit, TopologyFan}
EulerSimplexGeom → {SphereKit, Geom.LuneVolume}          -- 与上面无交集路径
```

本车道**零新 import**，故 `ea2_upsX_pos_iff` 不可用。可用的替代件（全部已在闭包内）：

| 需要的件 | 实际可用件 | 位置 | 状态 |
|---|---|---|---|
| 非共线 ⇒ `ups_x > 0` | `p38_upsX_pos_noncollinear`（**private**，仅作证法模板） | `LocalAuto38Bridge.lean:523` | 真证；private 不可跨文件引用，抄证法 |
| `Collinear3 v w w1 ↔ ∃ c, w1 - v = c • (w - v)`（`w ≠ v`） | `collinear3_iff_smul` | `Kepler/Geom/Azim.lean:86` | 真证，**public，已 import** |
| `2(x·y) = ‖x‖²+‖y‖²-dist x y²` | `p38_cos_law`（private 模板）→ 自备 `w11_cos_law` | `LocalAuto38Bridge.lean:99` | 真证 |
| `upsX a b f = 4(ab - p²)` | `p38_upsX_gram`（private 模板）→ 内联 `linear_combination` | `LocalAuto38Bridge.lean:225` | 真证 |
| Cauchy–Schwarz 等号情形 | `norm_inner_eq_norm_tfae`（Mathlib） | Mathlib | 已 import |
| `‖x‖² = x ⬝ᵥ x` / `inner ℝ x y = x ⬝ᵥ y` | `norm_sq_eq_dot` / `inner_eq_dot` | `Kepler/Geom/Azim.lean:70,74` | 真证，**public，已 import** |

证法路线（与 `p38_upsX_pos_noncollinear` 同构，但把 apex-0 形式一般化到 `{v0,v1,v2}`）：
令 `u = v1-v0`、`w = v2-v0`，则 `upsX x1 x2 x6 = 4(‖u‖²‖w‖² − (u·w)²)`；
若括号 ≤ 0，Cauchy–Schwarz 夹逼得等号，`norm_inner_eq_norm_tfae` 给 `u = 0` 或 `w = c • u`，
两者都迫使 `Collinear3 v0 v1 v2`，与 `hnc` 矛盾。

**退化分支处理**（与 p38 不同、必须自己补的点）：`u = 0` 意味着 `v1 = v0`，
此时 `collinear3_iff_smul` 的前提 `v1 ≠ v0` 不成立，必须走
`Collinear ℝ {v0,v0,v2}`（`collinear_pair` + 集合去重）这条路。见 `w11_collinear_dup`。

## 4. BLOCKED 评估

**非 BLOCKED。** :1646 的关键输入 `¬Collinear3 → upsX ≠ 0` 在闭包内可**自足重推**
（不依赖任何 sorried 件、不依赖新 import）；:1629 所需的连续性律全部是 Mathlib 现成件。
两件均已在整文件上闭合（见 `Evidence.md`）。

## 5. 侦察阶段发现的额外事实（对下波有用）

1. `ContinuousWithinAt.smul` 的 `f • g` 形态**不能**由 elaboration 从 `fun t => f t • g t`
   反推（higher-order unification 失败）。必须：(a) 把 `have` 写成 lambda 形，再用 `exact`
   做 defeq 转换；或 (b) 显式给 `(f := …) (g := …)`。本 lane 用 (a)。
2. `continuousWithinAt_const` 的隐式 `c` 未定时，其后的 `by` 块会报
   `invalid 'by' tactic, expected type has not been provided`。需要先单独 `have` 出内层连续性。
3. `PiLp.continuous_ofLp` / `PiLp.continuous_toLp`（不是 `WithLp.*`、也不是 root 名）是
   `V3 ↔ (Fin 3 → ℝ)` 连续性的正解；`Continuous.comp_continuousWithinAt` **不存在**，
   要用 `Continuous.continuousAt.comp_continuousWithinAt`。
4. `continuous_pi_iff` + `fin_cases i <;> simp [cross_apply, Matrix.cons_val] <;> fun_prop`
   可一次性证出 `Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => crossProduct p.1 p.2)`。
5. `sorry` 体的声明**不会**触发 `linter.unusedVariables`；换成真证后若某个 binder 真未用
   （本例 `hd`，HOL 也未用），会**新增**一条 warning。本 lane 用一行
   `have hdne : … := ne_of_gt hd` 显式消费它以保持 warning 谱面不变（见 `Evidence.md` §3）。
