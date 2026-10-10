# jgxzygw-scout — JGXZYGW 链侦察结案报告（零改动只读侦察）

> 2026-09-29 侦察 lane 交付，编排者落库。纪律记录：零 repo 文件改动、零 git 操作、未跑
> auto_gate；轻量验证仅用 /tmp scratch + `lake env lean`（单 lake 进程，未 build 任何仓库
> 模块，PA1 的 typecheck 不落 olean 产物）。所有 file:line 经 grep/sed 实测核对；Lean 侧
> defeq 断言经 /tmp/jgx_check.lean 编译验证。

**核心结论先行**：

① **这不是 GIANT，是一座半成品山**：PA1 已把整条链（pack1.hl:325-592）移植成 Lean 骨架，
22 件中 10 件**已证且经本机验证编译通过**（PA1 零 error），仅剩 **12 件 sorry**，全部机械/
中等档，**无任何解析银行（零浮点、零极限、零积分）**；整链填证预估 **210–360 行**。

② **上一侦察"从 PA1 在 p=0 推出"的捷径裁定被推翻（就当前 checkout 而言）**：PA1.JGXZYGW:1026
本身是 sorry、PA1 在本 checkout **无 olean**（build/lib 里只有 PA2–PA25，无 PackingAuto1）、
且 PA1↔PA2 双向 import 被 `Kepler.Text.saturated` 公开同名**硬冲突**封死（PA1:441 vs
PA2:263）。该捷径只在 merge 期成立，作为当期填证路径不合法。

③ **落点裁定：新叶模块**（`Kepler/Text/PackingJGXZYGW.lean`，只 import Statement+Mathlib，
链件全 private + 一枚唯一名公开 capstone），PA2 与 PA19 各加 1 行 import + ~10 行 shim：
**一次移植同时喂饱两个银行**（PA2.JGXZYGW_KY_p2 与 PA19.JGXZYGW_p19）。关键新发现：
PA25:3695 直接消费 `PackingAuto2.RDWKARC_concl`，所以 PA2 侧银行是主干道，只填 PA19
会漏掉 PA25 手臂。

④ 波计划 3 波（§4）：机械 8 连 → 测度主点+实代数 3 件 → capstone+双 shim。总风险中等，
最大不确定点是 `measure_unions_sum_voronoi` 的有限并加性与 `ineq_lm5_3_step4` 的实代数
长链（HOL 见证已锚定：`63π/√18 + 4c/√32`，PA1:52 注明）。

---

## §0 定位与消费链（Lean 侧实测）

```
HOL: pack1.hl JGXZYGW (:519) ──p=0 特化──> RDWKARC.hl JGXZYGW_KY (:76-91, prove_by_refinement, MESON 桥)
Lean 侧双臂：
PA2.JGXZYGW_KY_p2 (PackingAuto2.lean:1091, private, sorry)
  └─> PA2.RDWKARC_concl (:1108-1125, 装配已真化 16f31f68, 调用点 :1125)
        └─> PA25.PACKING_CHAPTER_MAIN_CONCLUSION (PackingAuto25.lean:3693-3695 `refine RDWKARC_concl hkc ?_ ?_`)  ← 主干道消费者
PA19.JGXZYGW_p19 (PackingAuto19.lean:659-665, private, sorry)
  └─> PA19.JGXZYGW_KY (:669-674, 已证, body = `JGXZYGW_p19 S 0 hV hs hA`)
        └─> PA19.RDWKARC (:783-793, GIANT sorry)
              └─> PackingConcl.RDWKARC_concl_discharged (PackingConcl.lean:518-523, `RDWKARC`)
import 方向实测：PA19 imports PA2 (:123)；PA2 imports {Polytope, Fan, Statement, Mathlib}（无 PA1，PA2:69 明文拒绝）；
PA1 imports {Polytope, Statement, Mathlib} (:62-64)，全仓库**零文件 import PA1**；PA1 零 olean（.lake/build/lib/lean/Kepler/Text/ 只有 PackingAuto2..25 的 olean）。
```

## §1 HOL 侧链全图（pack1.hl）

HOL 源：`reference/flyspeck/text_formalization/packing/pack1.hl`

| HOL 件 | pack1.hl 行号 | Lean 对应 | 定级 | 备注 |
|---|---|---|---|---|
| `voronoi_open` def | :153 | PA1:430 已证环境 | — | 链上游 |
| `KIUMVTC`（Lemma 5.1 有限性） | :140-145 | PA1:363 已证 / Statement.lean:46 `Packing.finite_inter_ball` | — | 链上游 |
| `voronoi_in_ball` | :285 | PA1:704 已证 | — | 链上游 |
| `DRUQUFE`/`measurable_voronoi` | :315/:322 | PA1:775/:782 已证 | — | 链上游 |
| `negligible_fun_p` def | :329 | PA1:791 def | — | C≥0 + Σ f ≤ C·r² |
| `fcc_compatible` def | :332 | PA1:796 def | — | √32 ≤ vol(cell)+f v |
| `packing_subset_unions_ball` | :335-338 | PA1:800 **sorry** | 机械 | dist 三角不等式集合账 |
| `measurable_packing_lm1` | :339 | PA1:807 已证 | — | |
| `map_to_ball`/`surj_map_to_ball`/`finite_set_packing_in_ball` | :342-352 | PA1 未移植（编码绕开，用 ncard+KIUMVTC） | n/a | |
| `measurable_packing_lm2` | :353 | PA1:819 **sorry** | 机械 | 有限并可测 |
| `measure_ineq_lm53_1` | :357 | PA1:839 已证 | — | |
| **`measure_ineq_lm53_2`**（Step 1） | :363-370 | PA1:892 **sorry** | 中等 | `MEASURE_UNIONS_LE` → Mathlib `measure_biUnion_finset_le`（OuterMeasure/Basic.lean:80）+ ENNReal→ℝ 记账 |
| `card_eq_ball_point` | :371-379 | PA1:863 已证 | — | |
| voronoi 几何三件（:380/:383/:385） | 380-387 | PA1:901/908/919 已证 | — | |
| `surj_map_to_voronoi_db` | :390 | PA1:930 **sorry** | 机械 | |
| `finite_set_voronoi_center_in_ball` | :394 | PA1:938 **sorry** | 机械 | |
| `measurable_unions_voronoi` | :398 | PA1:946 **sorry** | 机械 | |
| `negligible_voronoi` | :400-406 | PA1:954 **sorry** | 机械-中等 | 异胞不相交 → inter=∅ |
| `inj_map_to_voronoi` | :407-416 | PA1:964 **sorry** | 机械 | |
| **`measure_unions_sum_voronoi`**（测度主点） | :417-469（53 行，链内最大件） | PA1:973 **sorry** | 中等 | `MEASURE_NEGLIGIBLE_UNIONS`；Mathlib 无现成逐字件，需 Finset 归纳 + `measure_union_add_inter`（MeasureSpace.lean:135）+ 零交重写；PA1 编码已去掉 CROSS/pair 机器，比 HOL 简单 |
| `sum_measure_voronoi_le_ball`（Step 2） | :470 | PA1:982 **sorry** | 机械 | |
| `ineq_lm5_3_step3`（Step 3） | :476 | PA1:991 已证 | — | |
| **`ineq_lm5_3_step4`**（Step 4） | :485-518（34 行实代数） | PA1:1015 **sorry** | 中等 | 见证 `63π/√18+4c/√32`（PA1:52 注明）；field_simp+positivity/nlinarith，无浮点 |
| **`JGXZYGW`**（capstone） | :519-592（74 行） | PA1:1026 **sorry** | 中等 | 纯账面代数 + `sqrt32/sqrt18=4/3` 恒等式 |

总量：链体 pack1.hl:325-:592 ≈ **268 行 HOL**（含上游共 ~400 行）。**无解析银行**：全链只
涉及有限集测度加性、开球体积 `4π/3`、实数不等式账；浮点/极限/积分硬点为零。难度总定级：
**中等**（约 2 个中等波，非 GIANT）。

## §2 树内存量盘点

**PA1:1026 `JGXZYGW` vs PA19:659 `JGXZYGW_p19` vs PA2:1091 `JGXZYGW_KY_p2`**：三者为
**同一陈述的编码变体，无弱化**。差异全部是 rfl 级或 ≤10 行 shim 级（已实测验证）：

- 类型：`Space3`（Statement.lean:30 abbrev）≡ `V3`（Geom/Azim.lean:33 abbrev），
  `Kepler.Space3 = Kepler.Geom.V3` 经 **rfl 验证**；
- 体积：PA1 的 `(volume X).toReal` ≡ PA2/PA19 的 `volume.real X`（Mathlib
  `MeasureTheory.Measure.real`，MeasureSpaceDef.lean:101，body 即 `(μ s).toReal`），
  **rfl 验证**；
- `saturated`：PA1:441 与 PA2:263 body 逐字相同（`∀ x, ∃ y ∈ V, dist x y < 2`）；
- `fcc_compatible`（PA1:796）vs `fccCompatible`（PA2:293）：body 相同，仅
  `voronoi_open`/`voronoiOpen`（PA2:189 private，body 相同）+ 体积编码差，rfl 级；
- `negligible_fun_p`（PA1:791）vs `negligibleFunP`（PA2:285）：PA1 显式量化有限性
  `∀ h : (S∩ball p r).Finite, ∑ h.toFinset ≤ C*r²`；PA2 用 `setSum`（PA2:124，无限集取 0，
  无限时断言平凡真）——内容等价，桥接 ~5 行（split/dif_neg）；
  `negligibleFun0 = negligibleFunP _ _ 0` 是定义展开（PA2:289）。
- PA1 为箭头形假设 `(∃ A, …) → …`，PA19/PA2 为显式参数 `hA : ∃ A, …`：curry 级差异。

**已证覆盖率**：PA19 侧只证了平凡桥 `JGXZYGW_KY`（1 行实内容，<5%）。PA1 侧是真正的存量：
链 22 件中 **10 件已证**（可测性上节、lm53_1、card_eq、voronoi 几何三件、step3、体积两助记），
**12 件 sorry**（:800/:819/:892/:930/:938/:946/:954/:964/:973/:982/:1015/:1026，与
`lake env lean` 的 sorry 警告清单逐条吻合）。PA1 全文件 1505 行、30 处 sorry（其余 17 处在
pack2 闭胞链 :1217+，不在本目标内）、**0 error（本机验证）**。

## §3 落点裁定

- **"从 PA1 在 p=0 推出"（上一侦察裁定）：当期不成立，仅 merge 期成立。** 陈述级捷径本身
  为真（§2 的桥全部成立，KY_p2 = PA1.JGXZYGW@p:=0 模 curry/rfl/shim），但三重阻断：
  PA1.JGXZYGW 自身 sorry；PA1 无 olean 且零 importer；PA1↔PA2 任一方向 import 都因
  `Kepler.Text.saturated` 同 namespace 公开重复声明而**编译冲突**（另涉
  `voronoi_open`/`KIUMVTC` 等公开名）。PA19 imports PA2 又封死 PA2←PA19 方向。
- **PA1 原地填**：最省单点（骨架已验证编译），但当期**零银行价值**（无下游可达），且留
  saturated 冲突给 merge。否。
- **PA19 扩私件**：只喂 PackingConcl 手臂；漏 PA25:3695 直接消费的 PA2.RDWKARC_concl。
  次优。
- **PA2 原地扩私**：只喂 PA25 手臂；PA19 臂需二次移植。次优。
- **推荐：新叶模块**（`Kepler/Text/PackingJGXZYGW.lean`，import 仅 Statement+Mathlib；
  链件全 private，公开一枚唯一名 capstone，如 `jgxzygw_p : Packing S → saturated S →
  (∃ A, fcc-form ∧ neg-form) → ∃ c, …` over `Space3`）：**无环**（不 import 任何 Text
  模块）、**零 name-clash**（private+唯一名）、**一次移植双臂收账**——PA2 加 1 行 import +
  ~10 行 shim 填 KY_p2，PA19 加 1 行 import + ~10 行 shim 填 JGXZYGW_p19（`JGXZYGW_KY`
  桥已证自动受益）。可整段复制 PA1:785-1032 已验证的 10 件已证代码，只填 12 件 sorry。
  先例：contrafan-scout 同款"独立深模块"裁定。重建代价：任何 PA2 侧改动都必然触发
  PA18/19/21/25/PackingConcl 子树重建，新模块不增加边际成本。

## §4 波计划

- **Wave JGXZ-1（机械 8 连，~60–100 行）**：packing_subset_unions_ball、
  measurable_packing_lm2、surj_map_to_voronoi_db、finite_set_voronoi_center_in_ball、
  measurable_unions_voronoi、negligible_voronoi、inj_map_to_voronoi、
  sum_measure_voronoi_le_ball。风险低；唯一细节坑是 negligible_voronoi 的严格三角不等式
  方向。
- **Wave JGXZ-2（测度主点 + 实代数，~100–150 行）**：measure_unions_sum_voronoi（Finset
  归纳 + `measure_union_add_inter` + 零交；PA1:826 `volume_ball_ne_top` 供 toReal 有限性）、
  measure_ineq_lm53_2（`measure_biUnion_finset_le` + ENNReal→ℝ 记账）、ineq_lm5_3_step4
  （见证 `63π/√18+4c/√32`；field_simp/positivity 组合，防 nlinarith 爆
  hearts——500 万 heartbeats 已设）。风险中：Mathlib 逐字件缺位需自组；实代数搜索失败回退
  手工 reassociate。
- **Wave JGXZ-3（capstone + 双 shim，~80–110 行）**：JGXZYGW 本体（~50–80 行纯账）+ 新模块
  落地 + PA2:1091 与 PA19:659 两枚 shim（~10 行/枚）+ 2 行 import。风险低，但触发 PA2
  子树大重建，建议单独时窗。
- 也可并成单 lane 单 PR（总 210–360 行，中等档），3 波切法仅为降低回滚粒度。全程无解析
  银行、无浮点常数风险。

## §5 残留不确定点

- PA1 的 pack2 闭胞链 sorry（:1217–1269 等 17 处）与本链无关，勿误伤；
- PA25 的 `PACKING_CHAPTER_MAIN_CONCLUSION` 还押着 `ox3q1hP25`/`pack_nonlinear_non_ox3q1h`
  等其他银行，本链填平只清 `RDWKARC_concl` 这一路；
- merge 期 PA1 存废决策（PA19/PA2 的 NEEDS 注记倾向 "delete `_p19` in favor of
  PackingAuto1.JGXZYGW"）与 saturated 重名如何解，超出本侦察权限，留给编排者。

关键文件：`lean/Kepler/Text/PackingAuto1.lean`（链骨架 + 12 sorry）、
`lean/Kepler/Text/PackingAuto2.lean`（:1091 银行）、`lean/Kepler/Text/PackingAuto19.lean`
（:659 银行 + :669 已证桥）、`lean/Kepler/Text/PackingAuto25.lean`（:3695 主干道消费者）、
`reference/flyspeck/text_formalization/packing/pack1.hl`（:519 HOL 源）、
`reference/flyspeck/text_formalization/packing/RDWKARC.hl`（:76 KY 桥源）。
