# DELIVERY — la11-mksimplex-cont-w1

- 车道：`la11-mksimplex-cont-w1`（LA11 / Flyspeck `PQCSXWG.hl`，`mkSimplex1` 九元连续性，锥内一件）
- 基线 HEAD：`b89ee8b45bc9ecbe197dd9e0551423326a9e8873`（`b89ee8b4`）
- 目标文件：`lean/Kepler/Text/LocalAuto11.lean`（唯一触碰文件）
- kit：`kit-la11-mksimplex-cont-w1.diff`（3 hunk / +168 / −2）
- 状态：**2/2 闭合，0 残件**（无需 `Kit-draft-*.lean`）

## 1. 闭合件表

| # | 声明 | @HEAD 行 | 闭合后公理面 | 证法一句 |
|---|---|---|---|---|
| 1 | `CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11` | :1629 | `[propext, Classical.choice, Quot.sound]` | `rfl` 展开 `mkSimplex1_p11` 的 let 链成 7 个分量，逐槽用 `ContinuousWithinAt.add/smul/div/sqrt/mul` 拼（多项式槽 `unfold <def>; fun_prop`，`1/upsX` 用 `hups`，跨乘积用自备 `w11_continuousWithinAt_crossV`）。 |
| 2 | `PQCSXWG2_WITHINREAL_p11` | :1646 | `[propext, Classical.choice, Quot.sound]` | `refine CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11 ?_ hd …`，唯一缺口 `upsX (x1 a) (x2 a) (x6 a) ≠ 0` 由自备 `w11_upsX_pos_of_noncollinear`（余弦律 + Cauchy–Schwarz 等号情形 + `collinear3_iff_smul`）给出。 |

### 连带转干净的既有件（证明体未改）

| 声明 | @HEAD 公理面 | 现在 | 说明 |
|---|---|---|---|
| `PQCSXWG2_ATREAL_p11` | 含 `sorryAx` | `[propext, Classical.choice, Quot.sound]` | 经 :1646 沾 `sorryAx`，:1646 一闭即断根 |
| `PQCSXWG2_p11` | 含 `sorryAx` | `[propext, Classical.choice, Quot.sound]` | 同上 |
| `PQCSXWG2_concl_p11` | 干净（def） | 干净 | 未变 |
| `MK_SIMPLEX_TRANSLATION_p11` | 干净 | 干净 | 未变 |
| `CONTINUOUS_WITHIN_SQRT_COMPOSE_p11` | 干净 | 干净 | 未变 |

→ **整条 `PQCSXWG2` 链的 `sorryAx` 已断根**（Evidence.md §1 原文）。

## 2. 新增助件（全部 `private` + `w11_` 前缀）

| 助件 | 作用 |
|---|---|
| `w11_coe_sub` | `((a-b : V3) : Fin 3 → ℝ) = a - b`（rfl） |
| `w11_cos_law` | 余弦律 `2(x·y) = ‖x‖² + ‖y‖² − dist x y²` |
| `w11_collinear_dup` | `Collinear ℝ {a,a,b}`（退化共线分支用） |
| `w11_continuous_cross` | `Continuous (fun p : (Fin 3→ℝ) × (Fin 3→ℝ) => crossProduct p.1 p.2)`（HOL `CONTINUOUS_CROSS`） |
| `w11_continuousWithinAt_crossV` | 上面这条推到 `ContinuousWithinAt` + `WithLp` 往返 |
| `w11_upsX_pos_of_noncollinear` | `¬Collinear3 v0 v1 v2` + 三条距离平方等式 ⇒ `0 < upsX x1 x2 x6`（`Collect_geom2.NOT_COL_EQ_UPS_X_POS` 的就地重推） |

## 3. 残件精确缺口表

**无残件。** 两个目标件全部闭合，kit 中不含 `sorry` 占位，`Kit-draft-la11-mksimplex-cont-w1.lean` 未生成。

## 4. 搬债审计（以 `docs/e2e-reachability-map.tsv` 地图行为准）

命令与读数（0 行 = 不在锥）：

```
$ grep -c "	PQCSXWG2_WITHINREAL_p11	" docs/e2e-reachability-map.tsv
1        # 在锥，parent=Kepler.Text.PQCSXWG2_ATREAL_p11（第 102 行）
$ grep -c "	CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11	" docs/e2e-reachability-map.tsv
0        # 不在锥（台账项，闭合不影响 K_SORRIED）
```

**体内新引用的每个 Kepler 声明逐个查地图**（全部 0 行 = 非 sorried，无搬债）：

```
mkSimplex1_p11                     -> 0
upsX                               -> 0
deltaX4                            -> 0
deltaX5                            -> 0
collinear3_iff_smul                -> 0
norm_sq_eq_dot                     -> 0
inner_eq_dot                       -> 0
Collinear3                         -> 0
```

非 Kepler 侧引用（Mathlib，无需查图）：`norm_inner_eq_norm_tfae`、`abs_real_inner_le_norm`、
`abs_mul_abs_self`、`mul_self_inj_of_nonneg`、`Real.norm_eq_abs`、`collinear_pair`、
`continuous_pi_iff`、`cross_apply`、`PiLp.continuous_ofLp`、`PiLp.continuous_toLp`、
`ContinuousWithinAt.{add,sub,mul,div,smul,sqrt,prodMk}`、`continuousWithinAt_const`、
`Continuous.continuousAt`、`ContinuousAt.comp_continuousWithinAt`。

**结论：零搬债。** 两个证明体不引用任何 sorried 声明，`hups` 是目标件自己的假设，
`upsX ≠ 0` 是就地真证而非转嫁。

**指标影响（估算，需仪器复核）**：
- `K_SORRIED`：锥内 `PQCSXWG2_WITHINREAL_p11` 的 `sorryAx` 消失 → **−1**（119 → 118，基线 TSV 头部读数）。
  `CONTINUOUS_MK_SIMPLEX_WITHINREAL_p11` 不在锥，**不贡献** K_SORRIED 变化（纯台账）。
- `K_AXIOM`：**0**（无新公理、无 `native_decide`）。
- `K_REACH`：新增 6 个 `_private.Kepler.Text.w11_*` 节点（都在 `PQCSXWG2_WITHINREAL_p11`
  的 proof term 里，故都可达）→ **+6**；`K_UNIVERSE` 同步 +6，COVERAGE 近似不变（微升）。
- `ORPHANS`：0 新增（6 个助件全部可达）。
- `SHIMS`：不变（未新增 `*_concl`）。

## 5. 下波工单

1. **落库**：在 `b89ee8b4`（或 rebase 后的 HEAD）上 `git apply kit-la11-mksimplex-cont-w1.diff`，
   随后跑一次 standalone 整文件复核（本 lane 已实测 RC=0 / 0 error / 22 sorry 声明）。
2. **LA11 剩余 20 条 own-sorry 分诊**（本 lane 未碰）：按 `docs/e2e-reachability-map.tsv`
   逐条 `grep` 判锥内/锥外；锥内优先。建议下一波取 §A 的 `quad_4240815464_a_p11` /
   `quad_3862621143_revised_p11`（依赖 `quadNonlinearV10` 契约，先判是否 BLOCKED）或
   §C TECOXBM 三条锥内件。
3. **可复用资产**：`w11_cos_law` / `w11_upsX_pos_of_noncollinear` / `w11_continuousWithinAt_crossV`
   三条是通用件，后续 LA11/LA17/LA34/LA38 一带若需要「非共线 ⇒ ups_x>0」或「V3 值跨乘积连续性」
   可直接复制（private，无跨文件耦合）。
4. **文档债**：`LocalAuto11.lean:1645` 的 docstring 仍写
   `` `Collect_geom2.NOT_COL_EQ_UPS_X_POS`; DISCHARGES ``。本 lane 按「陈述冻结逐字」**未改 docstring**；
   若要更新，建议单独一个 doc-only commit（同时可去掉 `(long continuity choreography; DISCHARGES)`）。

## 6. 预算自报

- 调用数：约 **64** 次工具调用（预算 ≤120）。
- 墙钟：约 **55 分钟**（预算 ≤3h）。
- 整文件编译：3 次（HEAD 基线 1 次 6.99s / WorkCheck 2 次各 ~7s），全部 `nice -n 19` 单进程串行。
- 未使用任何 `lake` 子命令；未写 `/tmp/lfainteg/`、`/tmp/pm12_oleans`、`/tmp/orch_*`、`/tmp/lane_*`
  或其它车道 scratch；主仓源码零改动。
- 中途简报（满 ~55 调用）：本环境无 `SendMessage` 工具，未发；进度以本文件与最终回复为准。
