# EVIDENCE — `pa22-fanstub-scout`

HEAD `ec57d345565970832ed5142851d970b2cd9c1482`。
toolchain `leanprover/lean4:v4.32.2`。所有探针只写 `/tmp/pa22fan/`，主仓零改动。
oleans 实测时间：`PackingAuto22.olean` 2025-11-05 16:31，`Assembly.olean` 16:33。

运行方式（所有日志里的 RC 都是这个命令的退出码）：

```
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean
nice -n 19 lake env lean /tmp/pa22fan/<probe>.lean
```

探针原文与日志已复制到 `logs/`。

---

## A. 14 条 sorry 的 `#print axioms` 实测（`logs/probe_axioms.log`）

```
'Kepler.Text.insert_v' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.regular_spherical_polygon_area_asnFnhk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.vol_solid_triangle_ortho' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.BIJ_FACET_HYPERFACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_CONFORMING_FAN' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.EDGE_PAIR_pr23' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.HYPERFACE_EXISTS' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.BIJ_DART_POLYEDGE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_edge_sum' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.EXISTS_M_POLYHEDRON' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.PACK_INEQ_DEF_A_797' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR2_ALT' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_FACET_SUM_4Pi' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

同一次运行里的"无辜件"（同一编译单元、无 sorryAx）：

```
'Kepler.Text.DLWCHEM_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BIEFJHU_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.UKBRPFE_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_TGJISOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_D1_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_PLAIN' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_NODE_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EDGE_pr23' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.INJ_EDGES_FACE_pr23' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FINITE_EDGE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_sum_sum_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.facet_3_facets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.GOTCJAH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FCHANGED_MEASURABLE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.weak_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SATURATE_BALL_ANNULUS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.THETA_BOUNDS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.fat_lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FACET_SOL_NN' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LMFUN_INEQ_CENTER_IMP_13' depends on axioms: [propext, Classical.choice, Quot.sound]
```

注：`PA22:5753/5806` 的文档串说 `DLWCHEM_sum`/`XULJEPR_sum` 仍吃
`BIEFJHU_explicit` 的 sorry —— **该记账已陈旧**：`BIEFJHU_explicit` 本身是标准三，
两条和式层实测零 `sorryAx`。

### A3. #3 的反例（手工，未机器化）

`volSolidTriangleP22 x u v w r := 0`（PA22:296）。取
`u = e0 = (1,0,0)`、`v = e1 = (0,1,0)`、`w = e0 + e2 = (1,0,1)`：

- `hcp`：`{0,e0,e1,e0+e2}` 张成 3 维，不共面 ✓
- `h1 : (w-u)·v = e2·e1 = 0` ✓
- `h2 : (w-u)·u = e2·e0 = 0` ✓
- `t = cos (arcV 0 v u)`，`v·u = 0` ⇒ `arcV 0 v u = π/2` ⇒ `t = 0`
- `bet = dihV 0 v u w`：投影到轴 `v=e1` 的正交补上，`u` 投到 `e0`，
  `w` 投到 `e0+e2`，夹角 `= π/4`（用 `arcV 0 e0 (e0+e2)` 直接算：
  `arccos (1/√2) = π/4`）

于是结论两边 `0 = π/4 - asn(0) = π/4` 矛盾。`dihV` 的具体数值是手算，
**未**写 Lean 探针（缺 `dihV` 数值 API）；结构性事实 `volSolidTriangleP22 ≡ 0`
是定义即得（`rfl`）。这是 "FALSE-AS-STATED ⇒ 需 DEF-FIX"，不是 "BLOCKED"。

---

## B. 依赖图的机器证据（`grep`）

```
$ grep -rn "POLYHEDRON_TGJISOK" lean/Kepler/
Kepler/Text/PackingAuto22.lean:12804:/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955). The stub dart set is
Kepler/Text/PackingAuto22.lean:12806:theorem POLYHEDRON_TGJISOK (p : Set V3) (hb : Bornology.IsBounded p)
```

即：**零消费者**。

```
$ grep -rn "hypermap1OfFanxP22\|dFanP22\|d1FanP22\|eFanP22\|verticesP22\|edgesP22\|dartsetLeadsIntoFanP22\|topologicalComponentYfanP22" lean/Kepler/ | grep -v "Kepler/Text/PackingAuto22.lean"
(no output)
```

即：七个定义层假桩**没有一个跨出 PA22**；全部污染都在本文件内。

```
$ for s in PACK_INEQ_DEF_A_797 YSSKQOY_VECTOR2 YSSKQOY_VECTOR2_ALT; do grep -rn "$s" lean/Kepler/ | grep -v PackingAuto22.lean; done
(no output)
```

`YSSKQOY_VECTOR2_ALT` 在 PA22 内的唯一消费者是 `XULJEPR_full`（:15105）；
`PACK_INEQ_DEF_A_797` / `YSSKQOY_VECTOR2` 连文件内消费者都没有。

---

## C1. 假桩的当前形态（逐字）

**Lean `POLYHEDRON_TGJISOK`**（PA22:12804-12811）：

```lean
/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955). The stub dart set is
empty, so the (truncated) `ℕ` inequality holds trivially. -/
theorem POLYHEDRON_TGJISOK (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).darts.card ≤
      6 * (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).numberOfFaces - 12 := by
  simp only [hypermap1OfFanxP22]
  exact Nat.zero_le _
```

形态判定：**不是 `:= True` 型，也不是空洞化占位**；它是"关于空 hypermap 的真定理"，
证明干净（标准三）。但它**不对应 HOL 陈述**，因为三个参数定义
（`hypermap1OfFanxP22`/`verticesP22`/`edgesP22`）都是空桩。

定义层逐字（PA22:234-272）：

```lean
abbrev Dart3 := V3 × V3 × V3

def hypermap1OfFanxP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Hypermap Dart3 :=
  { darts := ∅, edgeMap := .refl _, nodeMap := .refl _, faceMap := .refl _,
    edgeMap_permutes := permutesOn_refl _, nodeMap_permutes := permutesOn_refl _,
    faceMap_permutes := permutesOn_refl _, comp_eq_one := rfl }

def dFanP22 ...  : Set Dart3 := (hypermap1OfFanxP22 x V E).darts
def d1FanP22 ... : Set Dart3 := ∅
def eFanP22 ... (d : Dart3) : Dart3 := d
def verticesP22 (p : Set V3) : Set V3 := ∅
def edgesP22 (p : Set V3) : Set (Set V3) := ∅
def dartsetLeadsIntoFanP22 ... (f : Set Dart3) : Set V3 := ∅
def topologicalComponentYfanP22 ... (U : Set V3) : Prop := True
```

**HOL 对应物**：
- `POLYHEDRON_TGJISOK`：`lean/scripts/packing/counting_spheres.hl:4955-5002`
  （`H = hypermap1_of_fanx (vec 0, vertices p, edges p)` 上的真陈述，
  证明经 `Hypermap.lemmaTGJISOK` + `POLYHEDRON_CONFORMING_FAN` + `POLYHEDRON_PLAIN` + `WGVWSKE`）。
- `BIJ_DART_POLYEDGE`：`counting_spheres.hl:5301-5416`。

## C2. `BIJ_DART_POLYEDGE` 在现桩下为假的机器证伪

`logs/probe_false.lean`，RC=0，输出全为标准三：

```
'ProbeFanStub.refute_BIJ_DART_POLYEDGE' depends on axioms: [propext, Classical.choice, Quot.sound]
```

证明骨架（探针原文）：

1. 造具体多面体 `bx = {x | e0·x ≤ 1 ∧ e1·x ≤ 1 ∧ e2·x ≤ 1 ∧ (-eS)·x ≤ 1}`
   （simplex），证 `polyhedron bx` / `IsBounded bx` / `0 ∈ interior bx`（全部 RC=0）；
2. `AFF_DIM_INTERIOR_EQ_3` ⇒ `affDim bx = 3`，再 `polyhedron_3_facets` ⇒
   `3 ≤ ncard {c | FacetOf c bx}` ⇒ 有 facet `f1`；
3. `facet_3_facets` ⇒ `3 ≤ ncard {e | FacetOf e f1}` ⇒ 有 `e`；
4. 于是 `(f1, e) ∈ {fe | FacetOf fe.2 fe.1 ∧ FacetOf fe.1 bx}`；
5. 但 `hypermap1OfFanxP22 … .darts = ∅`，`Set.BijOn b ∅ B` 的 `surjOn`
   要求对 `(f1,e)` 给 `x ∈ ∅` —— 矛盾。

同理（同一探针）：
`refute_BIJ_FACET_HYPERFACE`、`refute_HYPERFACE_EXISTS`、
`refute_POLYHEDRON_CONFORMING_FAN` 全部 RC=0 / 标准三。

## C3. DEF-FIX 需要的移植量（实测清单见 DEPGRAPH §4）

- **已在树内且标准三**（`logs/probe_fankit.log` / `probe_fan2.log` / `probe_conf.log`）：
  `FAN`、`hypermapOfFan`、`dartsetLeadsIntoFan`、`topologicalComponentYfan`、
  `conformingFan`、`PIIJBJK`、`WGVWSKE`、`Hypermap.darts_card_le`、
  `AMHFNXP_BIJ`、`WBLARHH`、`CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON`、
  `POLYTOPE_FAN80`、`POLYHEDRON_FAN`、`SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET`、
  `SUM_SOL_IN_FACE_SET_EQ_4PI`、`PREIMAGE_BIJ`/`BIJ_SYM`/`BIJ_TRANS`、
  `polyhedron_3_facets`/`facet_3_facets`/`FINITE_EDGE`/`polyhedron_sum_sum_edge`、
  `AFF_DIM_INTERIOR_EQ_3`、`POLYHEDRON_INTER_AFFINE_MINIMAL`、`FACET_OF_POLYHEDRON_EXPLICIT`、`dih_dot`。
- **缺**：
  1. `WBLARHH_BIJ`（`PolyAuto7.lean:23-26` 明说 = WBLARHH + PIIJBJK 的推论，~12 行）；
  2. `vertices p := Set.extremePoints ℝ p` 的**具名定义**（PolyAuto3/PolyAuto7 都是内联使用，Polytope 无 `vertices`）；
  3. `PolyAuto3.POLYHEDRON_FAN` 的内联边集与 `Polytope.edges p` 的桥（`FaceOf(segment v w) p` vs `edgeOf (segment v w) p = FaceOf … ∧ affDim = 1`，约 20-40 行）；
  4. `d1_fan` / `e_fan` 的真体在 `Fan.lean` 已有 `eFanPair`/`dart1OfFan`，但 `d1_fan` 的具名对照需确认/补一行转发。

一句话（C4）：**这一簇是"能修"，不是"长尾"** —— 上游 90% 已移植且零 sorryAx，
剩下的是定义层接线（DEF-FIX）+ 一个 12 行推论 + 四个小重证，估计 300–400 行。

---

## D1. 柱子③ 的准确污染根

`logs/probe_axioms.log` 实测：

```
'Kepler.Text.DLWCHEM_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

链路（源级调用，行号 = PA22）：

| DLWCHEM_full (15036-15070) 调用 | 该件 `#print axioms` | 引入的 sorry |
|---|---|---|
| `LMFUN_INEQ_CENTER_IMP_13` (15044) | 标准三 | — |
| `SATURATE_BALL_ANNULUS` (15047) → `weak_saturation` | 标准三 | — |
| `YSSKQOY_VECTOR` (15054) | 标准三 | — |
| `THETA_BOUNDS` (15058) | 标准三 | — |
| `existsM_polyhedron_sums` (15059) → `EXISTS_M_POLYHEDRON` (14986) | **sorryAx** | **#10** |
| 同上 → `polyhedron_edge_sum` (14992) | **sorryAx** | **#9** |
| 同上 → `POLYHEDRON_FACET_SUM_4Pi` (15025) | **sorryAx** | **#14** |
| 同上 → `facet_3_facets`/`GOTCJAH`/`FACET_SOL_NN` | 标准三 | — |
| `DLWCHEM_VECTOR_sumReal` (15065) → `DLWCHEM_sum` → `BIEFJHU_explicit` | 标准三（实测） | — |
| `fat_lemma1` (15043) | 标准三 | — |

⇒ **DLWCHEM_full 的 sorryAx 根 = {#9, #10, #14}**。

`XULJEPR_full` (15075-15128) 另加：

| XULJEPR_full 调用 | 状态 |
|---|---|
| `YSSKQOY_VECTOR2_ALT` (15105) | **sorryAx** ⇒ **#13** |
| `YSSKQOY_VECTOR`、`THETA_BOUNDS`、`SATURATE_BALL_ANNULUS` | 标准三 |
| `existsM_polyhedron_sums`（同上） | #9/#10/#14 |
| `XULJEPR_VECTOR_sumReal` → `XULJEPR_sum` → `BIEFJHU_explicit`/`UKBRPFE_explicit` | 标准三（实测） |

⇒ **XULJEPR_full 的 sorryAx 根 = {#9, #10, #14, #13}**。

命令级复核（"797 不在 DLWCHEM_full 的证明文本里"）：

```
$ sed -n '15036,15071p' lean/Kepler/Text/PackingAuto22.lean | grep -n "PACK_INEQ_DEF_A_797\|YSSKQOY_VECTOR2"
(no output; the only YSSKQOY hit is YSSKQOY_VECTOR at the theta-angle line 15054)
```

补充说明：本机 olean 不保留 theorem proof term（`ConstantInfo.value? = none`，
见 `logs/probe_dbg*.lean` 的诊断），所以无法用 `Expr.getUsedConstants` 做
证明项的传递闭包；上表因此是"逐 callee `#print axioms` + 源级调用行"的合成，
每个 callee 的实测输出都在 `logs/probe_axioms.log`。

## D2. 只闭合 #11/#12/#13 能否让柱子③转标准三？—— **不能**

命令级判定：

1. **前**：`#print axioms Kepler.Text.DLWCHEM_full`
   = `[propext, sorryAx, Classical.choice, Quot.sound]`；`XULJEPR_full` 同。
2. **#11/#12 与 DLWCHEM_full/XULJEPR_full 的证明文本无任何交集**（上一条 grep：
   两件在 15036-15127 一次都不出现）；`#11`/`#12` 在全树也零消费者。
   因此闭合它们对柱子③的 `#print axioms` **没有任何影响**。
3. **#13 只在 XULJEPR_full 里被调用**（15105）。闭合它只从 XULJEPR_full 的根集
   里去掉一项。
4. 即便 #13 闭合，`XULJEPR_full` 仍经 `existsM_polyhedron_sums` 吃
   **#9 `polyhedron_edge_sum` / #10 `EXISTS_M_POLYHEDRON` / #14 `POLYHEDRON_FACET_SUM_4Pi`**
   （三条实测均带 `sorryAx`），所以仍是
   `[propext, sorryAx, Classical.choice, Quot.sound]`。
5. `DLWCHEM_full` 更是与 #13 无关，闭合 #11/#12/#13 后仍带 `sorryAx`。

⇒ **判定：NO。柱子③ 的标准三最短根集 = {#9, #10, #14}（XULJEPR 侧再加 #13）。**

## D3. 若还要转标准三，按依赖序还差

1. `#10 EXISTS_M_POLYHEDRON`（独立，无假桩，HOL 267 行 → Lean ~400 行）；
2. DEF-FIX（`vertices/edges/hypermap1OfFanx/eFan/dartsetLeadsIntoFan/topologicalComponentYfan`）；
3. `WBLARHH_BIJ`（12 行）+ 重证 `#4` / `#5` / `#7` / `#8`；
4. `#9 polyhedron_edge_sum`（依赖 2+3）；
5. `#14 POLYHEDRON_FACET_SUM_4Pi`（依赖 2+3 的 #5 侧）；
6. `#13 YSSKQOY_VECTOR2_ALT`（依赖 #12；#12 依赖 #11 的 arclength 桥）。

## D4. `pa22-fcdjdot-body` 施工波建议

| 波 | 任务 | 预估 |
|---|---|---|
| W0 | DEF-FIX 接线（vertices/edges/FAN witness/Dart3/hypermap/eFan/d1Fan/dartset/topological） | 200-300 行（含桥） |
| W1 | `WBLARHH_BIJ` + 重证 #5/#7/#4 | 12 + 30+30+40 行 |
| W2 | 重证 #8 | ~120 行 |
| W3 | 重证 #9 + #14 | ~60 + ~50 行 |
| W4 | #10 EXISTS_M_POLYHEDRON | ~400 行 |
| W5 | #11 → #12 → #13（797 支线，与柱子③解耦，可并行） | ~80+25+30 行 |
| W6 | 柱子③ 终验 `#print axioms DLWCHEM_full/XULJEPR_full` | 0 |

（#1 insert_v ~150 行、#2 3 行、#3 DEF-FIX+60 行不阻塞柱子③。）

---

## E. #2 的可证性（SF-103 之后）

`regularSphericalPolygonAreaP22` 与 `asnFnhk` 都是**同一闭式**：
`2π - 2k·asin(L·sin(π/k))`，其中 `L = h√3/4 + √(1-(h/2)²)/2`。
`asnFnhkP22 h k … = asnFnhk h ↑k …`（`IneqClosureDefs.lean:727-729`）。
所以 #2 **不需要任何 `Sphere.regular_spherical_polygon_area` / `Sphere.asnFnhk`
的桥**——它们是定义等价的（只差 `4.0` 与 `4` 的字面量归一）。

`logs/probe_easy.lean`（RC=0）：

```lean
theorem probe_asnFnhk (h : ℝ) (k : ℕ) (hk : 3 ≤ k) (hh : 1 ≤ h ∧ h ≤ h0) :
    regularSphericalPolygonAreaP22
        (h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2) k =
      2 * Real.pi - 2 * asnFnhkP22 h k 1 1 1 1 := by
  have h4 : (4.0 : ℝ) = 4 := by norm_num
  simp only [regularSphericalPolygonAreaP22, asnFnhkP22, asnFnhk, asn, h4]
  ring
```

输出：`'probe_asnFnhk' depends on axioms: [propext, Classical.choice, Quot.sound]`，
且 `hk`/`hh` 未被引用（证明只做定义展开）⇒ 关它就是删 `sorry` 加 3 行。

## F. #6 的机器证伪（`logs/probe_easy.lean`，RC=0）

```lean
theorem probe_EDGE_PAIR_pr23_false :
    ¬ (∀ (x : V3) (V : Set V3) (E : Set (Set V3)) (d d' : Dart3),
        eFanP22 x V E d = d' → pr2 d = pr3 d' ∧ pr3 d = pr2 d')
```

取 `d = d' = (0, 0, e0)`（`e0 = EuclideanSpace.single 0 1 ≠ 0`），
`h : eFanP22 … d = d` 由 `eFanP22 = id` 自动成立，结论要求 `0 = e0`。
输出标准三。

## 局限与 UNRESOLVED

- `#3` 的 `dihV 0 e1 e0 (e0+e2) = π/4` 未机器化（只给手算）；`volSolidTriangleP22 ≡ 0`
  是定义即得。若要把 #3 的 FALSE 升级为"机器证伪"，只需补一个 `dihV` 数值探针。
- `#11` 的 `arcLengthICD` 单调性/`acs` 恒等式在树内**不存在**
  （`LocalAuto22.arclength_xrr_p22` 自己也是 sorry，并注明同一缺口），所以 #11 判
  NEEDS-MATH 而非 PROVABLE。
- `#1` 的 111 行 HOL 移植未做，故判 NEEDS-MATH（不是 PROVABLE）。
- Proof term 不可从 olean 读取（`value? = none`），D1 的根集是
  "逐 callee `#print axioms` + 源级调用行"的合成，不是证明项闭包。

## 日志说明（哪些 error 是预期的）

- `logs/probe_axioms.log`：2 条 `unknownIdentifier` 来自两个我猜错的名字
  （`Kepler.Text.existsM_polyhedron_sums` 是 private；`Kepler.Text.cosg_p22` 也是 private）。
  14 条 sorry + 上游件的 `#print axioms` 全部正常打印。
- `logs/probe_fankit.log`：1 条 `unknownIdentifier` = `Kepler.Text.darts_card_le`
  （真名是 `Kepler.Text.Hypermap.darts_card_le`，已在 `probe_fan2.log` 补测，标准三）。
- `logs/probe_conf.log`：5 条 `unknownIdentifier` = 我把 `hypermapOfFan`/`topologicalComponentYfan`/
  `FAN`/`eFanPair`/`dart1OfFan` 写在了 `Kepler.Text` 而非 `Kepler.Text.Fan` 命名空间下；
  其余（`SUM_SOL_*`、`conformingFan`、`dartsetLeadsIntoFan`）全部标准三。
- `logs/probe_deps.log`：**不是有效证据**。它试图用
  `ConstantInfo.value?` 走证明项闭包，但本机 olean 不存 theorem proof
  （`hasValue=false`，见 `probe_dbg*.lean`），结果里所有 `=false` 都无意义。
  D1 的根集因此改用"逐 callee `#print axioms` + 源级调用行"（都在 `probe_axioms.log`）。
- `logs/probe_false.log` / `probe_easy.log` / `probe_fan2.log`：0 error，RC=0。
