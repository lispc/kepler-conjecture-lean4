# VERDICT — `pa22-face-scout`

> 侦察对象：「3-多面体一条棱至多属 2 个 facet」能否在现有 Mathlib / 本仓资产上做出来。
> 约束：**未写 Lean、未改主仓、未编译 Lean**（只做 grep / 只读 / python 数值验证）。
> 基线：`lean/Kepler/Text/PackingAuto22.lean`（16247 行，`sorry` 6 处：
> 2081 / 6775 / 13550 / 13982 / 14066 / 14346）。

---

## 0. 结论速览

| 问题 | 判决 |
|---|---|
| 这句话是否**数学上真** | **是**（任意 3-维多面体，含无界，每条 1-维面恰属 2 个 facet） |
| Mathlib 有没有现成 Face / polytope 理论 | **完全没有**。mathlib `v4.32.2` 全树无 `Polytope` 结构、无 `Face`、无面格、无 Euler 公式 |
| 路线 A（凸几何维数论证） | **可行**，`EDGE_TWO` 本体 **160–220 行**；`#9` 合计 **270–400 行**（含计数装配） |
| 路线 B（扇/组合） | **可行但最贵**：等价于 `#8` 的 `EDGES0_SUBSET_FAN`（CFYXFTY1 反向），**300–500 行**，且两枚重前置 `CONVEX_OPEN_AFF_GT_FACE` / `CLOSURE_INTERS_CONVEX_OPEN` **全树没有** |
| 路线 C（有限枚举，用 `ncard ∈ {13,14,15}`） | **不可用**（0 行）：冻结陈述对任意 `n` 量化，数值界进不去；粗界 `k_f ≤ n` 给出的上界远超 `6n-12` |
| 能否绕开「至多 2」 | **不能**。需要的方向是上界 `M ≤ #darts = 2E`；「至少 2」给的是反向，无用。可弱化成**计数形**（fiber 的 `ncard ≤ 2`），但绕不过去 |
| `fcdjdot` 是否锁死 | **部分锁死**：`#9` **不锁**（只差 `EDGE_TWO`，不需 `#8`）；`#10 EXISTS_M_POLYHEDRON` **锁死且陈述为假**——因 `weaklySaturatedP22 := True` 定义洞（反例见 §1.3，已数值验证） |
| 最小施工序第一件 | `p22_edge_facets_ncard_le_two`（`{f | FacetOf f P ∧ FacetOf e f}.ncard ≤ 2`），按 §2.1 的 6 步证，验收 = 零新 `sorry` + `#print axioms` 标准三 |

**对 w4/w5 一句话总结的更正**：`#9`/`#10` **不是**「同一句」卡住。
- `#10` 的 HOL 证明（`counting_spheres.hl:5888–6152`）**完全不用**「棱 ≤2 facet」；
- 它真正的卡点是 **定义洞** `weaklySaturatedP22 := True`（PA22:357）+ 缺 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`；
- `#9` 才需要「至多 2」，而且**不需要** `#8`。

---

## 1. F1：#9 / #10 的精确需求（逐字陈述 + 依赖清单）

### 1.1 `#9 polyhedron_edge_sum`（PA22:14059–14066，HOL `counting_spheres.hl:5476`）

```lean
theorem polyhedron_edge_sum (P : Set V3) (n : ℝ) (hb : Bornology.IsBounded P)
    (hp : polyhedron P) (hi : (0 : V3) ∈ interior P)
    (hsize : ({f : Set V3 | FacetOf f P}).Finite ∧
      ({f : Set V3 | FacetOf f P}).ncard = n)
    (hn : 2 ≤ n) :
    (∑ f ∈ hsize.1.toFinset,
        (({e : Set V3 | FacetOf e f}).ncard : ℝ)) ≤ 6 * n - 12 := by
  sorry
```

**它到底是什么**：这不是「棱 ≤2」，本质是 3-多面体的 Euler 型界 `E ≤ 3F − 6`
（等价：`∑_f k_f = 2E ≤ 6F − 12`）。HOL 走的是 hypermap Euler。

**Lean 侧可行的最短链（全部件除 N2/N3 外已在树）**：

| # | 中间事实 | 出处 / 状态 | 作用 |
|---|---|---|---|
| N1 | `polyhedron_sum_sum_edge`：`∑_f #{e | FacetOf e f} = #{(f,e) | f facet P ∧ e facet f} =: M` | PA22:14002 **已证** | 把 LHS 变成 incidence 计数 `M` |
| N2 | **`M ≤ #darts`** ⟸ 每个 `e` 的 fiber `{f | FacetOf f P ∧ FacetOf e f}` 的 `ncard ≤ 2` | **缺口（本单主角）** | 上界唯一来源 |
| N3 | `#darts = 2 * #(edges P)` | **缺口（小）**，`FAN` 的 `Graph` + `Finset.card_eq_sum_card_fiberwise` | 才能接 N4 |
| N4 | `darts.card ≤ 6 * numberOfFaces - 12` | `POLYHEDRON_TGJISOK`（PA22:13038）**已证**（内部 `Hypermap.darts_card_le`，Hypermap.lean:1637） | Euler 端 |
| N5 | `numberOfFaces = n` | `numberOfFaces := faceSet.ncard`（Hypermap.lean:1026）+ `BIJ_FACET_HYPERFACE`（PA22:12895）**已证** + `hsize.2` | 换 `n` |

即：`∑_f k_f = M ≤ #darts = 2E ≤ 6n − 12`。**只差 N2、N3 两条**。
（`e` 是 `P` 的棱：`FacetOf e f → FacetOf f P` ⇒ `edgeOf e P`，由 `EDGE_OF_FACET_EDGE`（PA22:13730，已证）给；必要性闭合。）

**替代路线（Route B）**：不证 N2/N3，直接证 `#8 BIJ_DART_POLYEDGE`（PA22:13977，`sorry`）得 `M = #darts`。
该件只剩 `BIJ_EDGES_DART_FACE`（13543，`sorry`）反向；更贵（见 §2.2）。

### 1.2 `#10 EXISTS_M_POLYHEDRON`（PA22:14329–14346，HOL `counting_spheres.hl:5888`）

```lean
theorem EXISTS_M_POLYHEDRON (V : Set V3) (theta : V3 → ℝ) (r : ℝ) (n : ℝ)
    (hV : V ⊆ ballAnnulus) (hP : Packing V)
    (hws : weaklySaturatedP22 V r (2 * h0))
    (hsize : V.Finite ∧ V.ncard = n) (hne : V ≠ ∅)
    (hr : 2 ≤ r ∧ r ≤ 2 * h0)
    (htheta : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → theta v + theta w ≤ arcV 0 v w)
    (hthetapos : ∀ v ∈ V, 0 < theta v ∧ theta v < Real.pi / 2) :
    ∃ b : V3 → ℝ, ∃ f : V3 → Set V3, ∃ h : V3 → Set V3, ∃ P : Set V3,
      (∀ v ∈ V, h v = {p : V3 | v ⬝ᵥ p ≤ b v}) ∧
      (⋂ v ∈ V, h v) = P ∧
      (∀ v ∈ V, 0 < b v) ∧ polyhedron P ∧ Bornology.IsBounded P ∧
      (0 : V3) ∈ interior P ∧
      Set.BijOn f V {c : Set V3 | FacetOf c P} ∧
      (∀ v ∈ V, f v = P ∩ {p : V3 | v ⬝ᵥ p = b v}) ∧
      (∀ v ∈ V, b v = ‖v‖ * Real.cos (theta v)) ∧
      (∀ v ∈ V, rconeGt 0 v (Real.cos (theta v)) ⊆ fchanged (f v)) ∧
      (∀ v ∈ V, 0 < Real.cos (theta v) ∧ Real.cos (theta v) < 1) := by
  sorry
```

**它需要什么（对照 HOL 证明体逐句）**：

| # | 中间事实 | 状态 |
|---|---|---|
| N6 | `FACET_OF_POLYHEDRON_EXPLICIT_ALT`（facet ↔ 约束索引双射） | PA22:14163 **已证** |
| N7 | `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`（HOL `counting_spheres.hl:5518`）：`p` 只在 `v0` 上取紧、其余严格 ⇒ `p ∈ relint (P ∩ {v0 紧})` | **全树没有**（`grep` 0 命中）。等价/更弱的 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`（Polytope.lean:874，**已证**）要求 irredundant 表示，HOL 的 `_ALT` 特意不要 |
| N8 | `TARJJUW`（多面体非空 ⇒ 有界） | PackingAuto3:388 在树、已证，**但签名吃 `weakly_saturated`** |
| N9 | `weaklySaturatedP22` 真定义 | **DEFHOLE**：PA22:357 `:= True`；真定义在 PackingAuto3:35 `weakly_saturated`，PA22 不 import PA3 |
| N10 | `rcone_refl` / `rcone_dot_pos` / `rcone_def_alt` / `rcone_gt_facet` / `cos_bounds_0_Pi2` | PA22:12615/12628/12600/12704/12636 全部**已证** |
| N11 | 真 `weak_saturation`（补点至饱和） | **连带缺口**：PA22:6883 当前证明是 `⟨W, …, trivial, …⟩`（靠 `True` 桩），一改定义即失效；HOL 版是「最大基数扩张」论证（`counting_spheres.hl:1527`），`card_packing_annulus`（PA22:6853，**已证**）够用，估 120–250 行 |

**关键**：`#10` 的依赖里**没有任何一条**是「棱 ≤2 facet」。w4/w5 那句话对 `#10` 是误记。

### 1.3 决定性发现：`#10` 在当前陈述下是**假**的

`weaklySaturatedP22 := True` 使 `hws` 空洞，于是定理退化为：

> 任意有限 packing `V ⊆ ballAnnulus` + θ 条件 ⇒ 切半空间族 `{v·x ≤ ‖v‖cos θ_v}` 的交 `P` 有界且 `0 ∈ int P`。

**反例（已数值验证，见 `scripts/check_existsM_counterexample.py`）**：
`V` = 半径 2 的圆上正六边形（6 点，`z = 0`），`θ ≡ π/6`，`r = 2`，`n = 6`。

- `V ⊆ ballAnnulus`：`‖v‖ = 2 ∈ [2, 2h0 = 2.52]`，且 `2 ∉ ball 0 2`（开球）✓
- `Packing V`：相邻弦长 `= 2·2·sin30° = 2`，故 `dist < 2` 永不发生 ✓
- `θ+θ = π/3 ≤ arcV 0 v w`（相邻恰等号，其余更大）✓
- `0 < θ < π/2` ✓；`V.Finite ∧ ncard = 6`、`V ≠ ∅`、`2 ≤ r ≤ 2h0` ✓
- `hws`：`True` ✓

但 `b v = 2·cos(π/6) = √3`，所有 `v` 的 `z` 分量为 0 ⇒ 约束与 `z` 无关 ⇒
`(0,0,t) ∈ P` 对任意 `t` 成立 ⇒ `P` 含整条 z 轴，`Bornology.IsBounded P` 假，
`0 ∈ interior P` 也假。

**因此 `#10` 在 DEF-FIX 前不可能被证**（不是「难」，是「假」）。
这也意味着 `existsM_polyhedron_sums`（PA22:15989）与 `DLWCHEM_full` / `XULJEPR_full`
当前都建立在一条假引理 + `sorryAx` 上。

---

## 2. F2：三条路线逐条判定

### 2.1 路线 A（凸几何维数论证）— **可行，160–220 行**

**Mathlib 盘点（结论：零现成可用）**

| 想要的 | Mathlib 现实 |
|---|---|
| `Polytope` / `Face` / 面格 / 维数公式 | **完全没有**。`find Mathlib -name "*Polytope*"` 空；`grep "structure Polytope"` 空；`grep "^namespace Polytope"` 空。`Mathlib/Geometry/` 只有 `Convex / Diffeology / Euclidean / Group / Manifold / Polygon / RingedSpace` |
| 凸锥的 face | `Mathlib/Geometry/Convex/Cone/Face/Basic.lean:50` `structure IsFaceOf (F C : PointedCone R M)` —— **只对 pointed cone**，没有「多面体的面」 |
| 极面 | `Mathlib/Analysis/Convex/Exposed.lean:55` `IsExposed`；`Extreme.lean:133` `mem_extremePoints` —— 只有定义与初等性质 |
| 相对内部 | `Mathlib/Analysis/Convex/Intrinsic.lean:61` `intrinsicInterior`；`:75` `mem_intrinsicInterior`；`:89` `intrinsicInterior_subset`；`:450` `Set.Nonempty.intrinsicInterior` ✓ |
| 线性代数（关键） | `Mathlib/LinearAlgebra/Span/Defs.lean:518` `Submodule.mem_span_pair`；`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:173` `LinearMap.finrank_range_add_finrank_ker`；`Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:251/259` `Submodule.eq_of_le_of_finrank_le/_eq` |
| 计数 | `Mathlib/Data/Set/Card.lean:925` `Set.ncard_le_ncard_of_injOn`；`:1335/:1339` `Set.two_lt_ncard_iff` / `Set.two_lt_ncard`；`:704` `ncard_prod`；`Mathlib/Data/Set/Card/Arithmetic.lean:110` `Finite.ncard_biUnion`；`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:979` `Finset.card_eq_sum_card_fiberwise` |

**本仓有的面几何 kit（`lean/Kepler/Text/Polytope.lean`，2503 行）**：
`FaceOf`（:42）、`FacetOf`（:47）、`edgeOf`（:51）、`edges`（:56）、`polyhedron`（:60）、
`affDim`（:33）；
`FaceOf.trans`（:97）、`faceOf_face`（:104）、`faceOf_inter`（:121）、
`FACE_OF_AFF_DIM_LT`（:1061）、`subset_of_faceOf`（:369）、`faceOf_eq`（:416）、
`affDim_mono`（:155）、`mem_rint_iff`（:252）、`FACET_OF_POLYHEDRON`（:1755，**给出支撑半空间**）、
`FACE_OF_POLYHEDRON`（:1770）、`RELATIVE_INTERIOR_OF_POLYHEDRON`（:1793）、
`FINITE_POLYHEDRON_FACETS`（:1855）、`FACE_OF_POLYHEDRON_POLYHEDRON`（:2110）。
PA22 另有 `FACET_AFF_DIM_2`（10587，已证）、`EDGE_OF_FACET_EDGE`（13730，已证）、
`SEGMENT_EDGE_ONTO`（13553，已证）。

**证明（6 步，已逐条核对可用性）** — 目标形式取最弱（计数形）：

```lean
theorem p22_edge_facets_ncard_le_two (P : Set V3) (e : Set V3)
    (hp : polyhedron P) (hb : Bornology.IsBounded P)
    (hi : (0 : V3) ∈ interior P) :
    ({f : Set V3 | FacetOf f P ∧ FacetOf e f}).ncard ≤ 2
```

设 `f1 f2 f3` 两两不同、都是 `P` 的 facet 且都以 `e` 为 facet（`two_lt_ncard` 反证）。

1. **辅助件 L1**（同维面含 ⇒ 相等）：`FaceOf t s → FaceOf u s → t ⊆ u → affDim t = affDim u → t.Nonempty → t = u`。
   取 `x ∈ intrinsicInterior t`；`aff t = aff u`（`vectorSpan` 同 finrank + 包含）；
   `mem_rint_iff` 把 `relint t` 的球搬到 `u` ⇒ `x ∈ relint u` ⇒ `¬Disjoint` ⇒ `faceOf_eq`。
   **20–30 行**。
2. **两两相交 = 棱**：`f1 ≠ f2` ⇒ `f1 ∩ f2 = e`。
   `faceOf_inter` 给 `FaceOf (f1∩f2) P`；`faceOf_face` 给 `FaceOf (f1∩f2) f1`；
   `FACE_OF_AFF_DIM_LT` 给 `affDim (f1∩f2) < 2`；`e ⊆ f1∩f2` + `affDim_mono` 给 `≥ 1`
   ⇒ `= 1 = affDim e` ⇒ L1。**35–50 行**。
3. **取棱上两点**：`EDGE_OF_FACET_EDGE` 给 `edgeOf e P`，`SEGMENT_EDGE_ONTO` 给
   `e = segment ℝ v w`，`v ≠ w`；记 `d := w - v ≠ 0`。**15–25 行**。
4. **每个 facet 的超平面都含 `aff e`**：`FACET_OF_POLYHEDRON hp hf_i` 给
   `a_i ≠ 0`、`P ⊆ {a_i·x ≤ b_i}`、`f_i = P ∩ {a_i·x = b_i}`；`v,w ∈ f_i` ⇒ `a_i·v = a_i·w = b_i`
   ⇒ `a_i·d = 0`。**15–20 行**。
5. **`a1,a2` 线性无关**：否则 `a2 = c•a1`，则 `H1 ⊆ H2`（顶点处 `c b1 = b2`），
   两个超平面同为 2 维 ⇒ `H1 = H2` ⇒ `f1 = f2`，矛盾。**15–20 行**。
6. **`a3 ∈ span{a1,a2}` 并收口**：`a1,a2,a3 ∈ ker(dotRight d)`，
   `finrank ker (dotRight d) = 2`（**模板已存在**：`Polytope.lean:238–243` 用
   `LinearMap.finrank_range_add_finrank_ker` + `finrank_top` + `finrank_euclideanSpace_fin`），
   而 `a1,a2` 无关 ⇒ 是基 ⇒ `Submodule.mem_span_pair` 给 `a3 = α•a1 + β•a2`。
   先由 `f3 ≠ f1, f2` 排除 `αβ = 0`（`α=0 ⇒ a3 ∥ a2 ⇒ H3 = H2 ⇒ f3 = f2`，反之亦然）。
   对 `x ∈ f3`：`0 = a3·x − b3 = α(a1·x−b1) + β(a2·x−b2)`（用 `b3 = a3·v = α b1 + β b2`，`v ∈ e ⊆ f3`），
   两个括号 `≤ 0`；`α,β ≠ 0` 的四种符号情形都推出两括号 `= 0` ⇒ `x ∈ f1 ∩ f2 = e`。
   故 `f3 ⊆ e`，但 `affDim f3 = 2 > 1 = affDim e`，矛盾。**20–30 + 25–40 行**。

合计 **160–220 行**（含 L1）。风险：**中低**。唯一非平凡的是第 6 步的行空间论证，
但 `dotRight` + `finrank_ker = 2` 的模板在同一仓库已跑通，可照抄结构。
**不依赖 `#8`、不依赖任何 Mathlib polytope 理论。**

### 2.2 路线 B（扇/组合）— **可行但最贵，300–500 行，前置 2 枚缺件**

`fanOfPolyhedronP22`（PA22:314）+ `conformingFanOfPolyhedronP22`（PA22:12851）+
`WBLARHH_BIJ`（12866）+ `BIJ_FACET_HYPERFACE`（12895）+ `AMHFNXP_BIJ` 都在树且已证。

**但**：从 fan 读「棱 ≤2」的唯一通道是
> facet `f` 含棱 `e` ⇒ 存在 `f` 的面轨道里的 dart `d` 使 `{d.1,d.2} = e`

—— 这正是 `#8` 缺的那半：HOL `Cfyxfty.EDGES0_SUBSET_FAN`（`CFYXFTY.hl:1065`），
即 `EDGES0_FAN p f1 ⊆ {{pr2 e, pr3 e} | e ∈ f}`。有了它才 `|face orbit| = |edges f1|`，
再由「一条棱恰 2 个 dart」得到 fiber ≤ 2。

**成本**：HOL 原证 ~95 行密集策略，依赖
`CONVEX_OPEN_AFF_GT_FACE`、`CLOSURE_INTERS_CONVEX_OPEN`（**两枚全树 0 命中**）、
`CLOSURE_SUBSET`、`CONVEX_CLOSURE`、`GINGUAP`（ConformingAuto1:有）、`PIIJBJK`（ConformingAuto21:有）、
`exists_point_in_component_yfan`（PlanarityConnect:有）、`origin_is_not_aff_gt_fan`（Planarity:有）。
W3 的正向半（`p22_dart_edge_mem_edges`，13471）用了 **286 行**自建球坐标路线绕开
`CONVEX_OPEN_AFF_GT_FACE`；反向是**满射性**，比正向强，估 **300–500 行**、风险 **高**。
**收益**：顺带清掉 `#8` 两处 `sorry`（13550 / 13982）。但对 `fcdjdot` **不必要**（见 §3）。

### 2.3 路线 C（有限枚举 + `ncard ∈ {13,14,15}`）— **不可用，0 行**

三条独立理由，任一条即否决：

1. **量化范围不对**：`polyhedron_edge_sum` 的陈述是 `n : ℝ` 任意、只带
   `facets.ncard = n` 与 `2 ≤ n`。`V'.ncard ∈ {13,14,15}` 是 `DLWCHEM_full` 下半段的**下游**
   事实，冻结陈述里进不来（改陈述 = DEF-FIX，不在本单权限内）。
2. **粗界数值上差太远**：`n ≤ 15` ⇒ 需证 `∑_f k_f ≤ 6n−12 ∈ {66,72,78}`；
   而每个 facet 的边数 `k_f ≤ #(P 的顶点) ≤ 2n−4`（Euler 的推论；连它都要 Euler），
   `n = 15` 时粗界 `≤ 15·26 = 390`，离 78 差一个量级。要收紧就必须用 `2E` 与 Euler —— 又回到 §2.1。
3. **「有限顶点集」也只到 `polytope = conv(extremes)`**（`FINITE_POLYHEDRON_EXTREME_POINTS`，
   Polytope.lean:1896，已证），而 `∑_f #vertices(f) = ∑_v #{facets through v}` 这一步
   同样要「每棱 ≤2」或等价的面-棱关联双射。

结论：路线 C 没有任何一行可用于 `#9`。

---

## 3. F3：能否绕开「至多 2」

**不能，且方向是刚性的。** 严格论证：

- `#9` 的 LHS 经 `N1` 等于 `M`（incidence 个数）。
- Euler 端只给 **上界** `#darts ≤ 6n − 12`（`POLYHEDRON_TGJISOK`）。
- 要闭合必须 `M ≤ #darts`。对映射 `(f,e) ↦ e` 取 fiber：`fiber(e) = {f | FacetOf f P ∧ FacetOf e f}`，
  `#darts = Σ_e 2`，于是 `M ≤ #darts ⟺ fiber(e) ≤ 2` **逐点成立**。
- 「**至少** 2」给的是 `M ≥ #darts`，与所需方向相反，**完全无用**（不是「弱一点也行」，
  是符号错了）。
- 也不存在「对 `edges` 换一种分解」：任何 `M = Σ_{e∈S} fiber(e)` 的分解里，fiber 就是
  「含该棱的 facet 集合」，其上界只能是 2。

**可做的弱化（推荐）**：
1. 只证**计数形** `ncard ≤ 2`，不证唯一性等式、不证「恰好 2」、不证存在性；
2. 有界性 `hb` 只有一处软用（调 `EDGE_OF_FACET_EDGE` / `SEGMENT_EDGE_ONTO` 取棱上两点）；
   也可改走 `affDim e = 1 ⇒ e 非单点` 直接去掉 `hb`。`polyhedron_edge_sum` 本来就有 `hb`，无需动；
3. 不必对「任意 `e`」陈述：只需 `e` 真的是一条棱时（`∃ f, FacetOf f P ∧ FacetOf e f`），
   而这个前提从 set 非空自动给出。

**唯一的「等价绕法」**：改证 `#8 BIJ_DART_POLYEDGE`（更强，直接给 `M = #darts`）。
成本见 §2.2，比 `EDGE_TWO` 贵 1.5–2 倍，且不改变 `fcdjdot` 的可行性结论。

---

## 4. F4：判决与最小施工序

### 4.1 逐条判决

| 件 | 判决 | 估行数 | 备注 |
|---|---|---|---|
| `EDGE_TWO`（棱 ≤2，计数形） | **可行**（路线 A） | **160–220** | 只吃本仓 `Polytope` kit + 初等线代 |
| `#9 polyhedron_edge_sum` | **可行**（A + N3 + 装配） | **270–400**（含 `EDGE_TWO`） | **完全不需要 `#8`** |
| `#8 BIJ_EDGES_DART_FACE / BIJ_DART_POLYEDGE` | 可行但贵（路线 B） | 300–500 | 不在 `fcdjdot` 路径上 |
| `#10 EXISTS_M_POLYHEDRON` | **当前陈述为假**；DEF-FIX 后可行 | 见下 | 与「≤2」无关 |
| `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`（N7） | 可行 | 40–70 | 连续性直证：`p` 只在一约束取紧 ⇒ 存在球 `B(p,ε)` 其余严格 ⇒ `B ∩ aff ⊆ P∩H` ⇒ `mem_rint_iff` |
| 真 `weaklySaturatedP22` + 真 `weak_saturation`（N9/N11） | **必须先做 DEF-FIX** | 定义 3 行 + 证明 120–250 | `card_packing_annulus`（PA22:6853）已在树；HOL 是「最大基数扩张」论证 |
| `#10` 装配本体 | 可行（DEF-FIX 后） | 300–450 | N6/N8/N10 全在树 |

### 4.2 `fcdjdot` 是否锁死

- **`#9` 侧：不锁死。** 只差 `EDGE_TWO` + `darts = 2E` 两件，路线清晰、有模板、低风险。
- **`#10` 侧：锁死，且原因不是「≤2」。** 当前陈述假（§1.3）。解锁条件是
  **DEF-FIX**：把 `weaklySaturatedP22` 从 `True` 改成真定义（PA3:35 的
  `weakly_saturated`，或就地逐字复制），并重证 `weak_saturation`。
  这是**定义面变更**，需 DEF-FIX 章程批准；改后 `SATURATE_BALL_ANNULUS` /
  `DLWCHEM_full` / `XULJEPR_full` 的假设会从空洞变实，但它们本来就按 HOL 真假设编排，
  逻辑方向是**变强/变真**，不需要改陈述形状。
- 一句话：**「至多 2」不是 `fcdjdot` 的锁；`weaklySaturatedP22 := True` 才是。**

### 4.3 最小施工序（按依赖，逐件验收）

| 序 | 件 | 内容 | 估行 | 验收标准 |
|---|---|---|---|---|
| **1** | `p22_edge_facets_ncard_le_two` | 「棱 ≤2」计数形（§2.1 六步） | 160–220 | 零新 `sorry`；`#print axioms` = `[propext, Classical.choice, Quot.sound]`；陈述逐字 = `{f | FacetOf f P ∧ FacetOf e f}.ncard ≤ 2`，假设只 `polyhedron P`、`(0:V3) ∈ interior P`（`hb` 可留可去） |
| 2 | `p22_darts_card_eq_two_mul_edges` | `(hypermapOfPolyhedronP22 p …).darts.card = 2 * (edgesP22 p).ncard` | 40–70 | 同上三标准；只吃 `Fan.finite_dart1_fan` + `Graph` + fiberwise |
| 3 | `p22_incidences_le_darts` | `M ≤ darts.card`（fiberwise 分解，镜像 `polyhedron_sum_sum_edge`） | 50–80 | 同上 |
| 4 | `polyhedron_edge_sum`（#9 本体） | N1 + 2 + 3 + N4 + N5 + cast 处理 | 40–70 | `#print axioms` 标准三；**`sorry` 14066 消失**；`BIJ_DART_POLYEDGE` 仍可留 `sorry`（不在路径） |
| 5 | DEF-FIX 决策 | `weaklySaturatedP22` → 真定义（+ import PA3 或就地复制） | 3 + 审查 | 章程批准；`weak_saturation` 陈述不变但证明作废 |
| 6 | 真 `weak_saturation` | 最大基数扩张 | 120–250 | `#print axioms` 标准三 |
| 7 | `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT` | 连续性直证 | 40–70 | 同上 |
| 8 | `EXISTS_M_POLYHEDRON`（#10） | HOL 逐句装配 | 300–450 | `#print axioms` 标准三；`sorry` 14346 消失 |
| 9 | `existsM_polyhedron_sums` 复跑 + 柱③ | 装配层零改写通过，`DLWCHEM_full`/`XULJEPR_full` 转干净 | — | `#print axioms` 标准三（`fcdjdot` 本体落 `Assembly.lean`） |

**第一件就是第 1 行**：`p22_edge_facets_ncard_le_two`。它单项可独立验收，
且一旦落地，`#9` 的剩余部分（第 2–4 行）全是可预测的 Finset 装配，无数学风险。
若第 1 件卡住（唯一风险点：第 6 步 `α,β` 符号分类的 `linarith` 收口），
回退方案是改走 §2.2 路线 B，但那会把 `#9` 从 270–400 行推到 400–650 行。

---

## 5. 证据索引

- `needs.tsv`：F1 的 12 行需求台账（含状态 / 估行 / 证据位置）
- `mathlib_hits.txt`：Mathlib `v4.32.2` 逐条 grep 结果（含**否定结果**：无 Polytope / 无 Face / 无 Euler）
- `scripts/check_existsM_counterexample.py`：`#10` 为假的反例数值验证（已跑，全 PASS）
- 关键行号（主仓，只读）：
  - `lean/Kepler/Text/PackingAuto22.lean:314` `fanOfPolyhedronP22`；`:12851` `conformingFanOfPolyhedronP22`；`:12866` `WBLARHH_BIJ`；`:12895` `BIJ_FACET_HYPERFACE`；`:13038` `POLYHEDRON_TGJISOK`；`:13543` `BIJ_EDGES_DART_FACE`（sorry）；`:13553` `SEGMENT_EDGE_ONTO`；`:13977` `BIJ_DART_POLYEDGE`（sorry）；`:14002` `polyhedron_sum_sum_edge`；`:14059` `polyhedron_edge_sum`（sorry）；`:14163` `FACET_OF_POLYHEDRON_EXPLICIT_ALT`；`:14329` `EXISTS_M_POLYHEDRON`（sorry）；`:357` `weaklySaturatedP22 := True`；`:6883` `weak_saturation`（桩利用）；`:6853` `card_packing_annulus`；`:15989` `existsM_polyhedron_sums`
  - `lean/Kepler/Text/Polytope.lean:1755` `FACET_OF_POLYHEDRON`（支撑半空间）；`:1061` `FACE_OF_AFF_DIM_LT`；`:416` `faceOf_eq`；`:252` `mem_rint_iff`；`:193/238` `dotRight` + `finrank ker = 2` 模板
  - `lean/Kepler/Text/PackingAuto3.lean:35` `weakly_saturated`；`:388` `TARJJUW`
  - `lean/Kepler/Text/Hypermap.lean:1026` `numberOfFaces`；`:1637` `darts_card_le`
  - HOL：`lean/scripts/packing/counting_spheres.hl:5476` `polyhedron_edge_sum`；`:5888` `EXISTS_M_POLYHEDRON`；`:1527` `weak_saturation`；`reference/flyspeck/text_formalization/fan/CFYXFTY.hl:1065` `EDGES0_SUBSET_FAN`

---

## 回执（2026-11-06，`pa22-edge-two`）：**`#9 polyhedron_edge_sum` 已闭，270–400 行的估算是准的**

四步全 DONE，零 GAP。落地：`P22EdgeFacets.lean` 426 行（本体 280）+ `P22EdgeCount.lean` 195 行
+ PA22 内 74 行装配；**patch 的全部删除面 = 1 行 `sorry`**，`#9` 陈述逐字未动。

实测（编排者复核）：`polyhedron_edge_sum`、`p22_edge_facets_ncard_le_two`、
`p22_darts_card_eq_two_mul_edges`、`p22_incidences_le_darts` 四件
`#print axioms` 全 = `[propext, Classical.choice, Quot.sound]`；
PA22 整文件 `declaration uses sorry` **6 → 5**；编译 1:43.03 / RC=0 / 0 error。

### §2.1 第 6 步的符号分类**有漏洞**（车道发现并修正）

我在 `§2.1` 写的「`αu + βv = 0`，`u,v ≤ 0` 四情形都归零」**不成立**：`αβ < 0` 时有非零解。
正确做法是**改解另一个法向**：

```
α > 0 > β  ⇒  a₁ = (1/α)·a₃ + (−β/α)·a₂      两系数皆正 ⇒ f₁ ⊆ f₃ ⇒ 两 facet 相等
```

四情形由此闭合。**结论不变但更强**：`EDGE_TWO` **不需要 `hb`**、不需要方向 B、不需要 `#8`
（`hb` 只是为对齐 `#9` 的签名保留）。这条修正已写入 `P22EdgeFacets.lean` 的注释。

### `#10` 的剩余账（没有变）

`#10 EXISTS_M_POLYHEDRON` 仍差三件，且**第一件不是数学**：
① `weaklySaturatedP22 := True` 定义洞（PA22:357，当前陈述**为假**，须 DEF-FIX）；
② 全树缺失的 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT_ALT`；
③ `#10` 本体 300–450 行装配。
