# EVIDENCE.md — 柱③ 真依赖闭包（只读探针原始证据）

lane `pa22-fcdjdot-pillars-recon-w1`，HEAD 侦察起点 `117511bb`，源文件 pin：

| file | sha256 @117511bb | lines |
|---|---|---|
| `lean/Kepler/Text/PackingAuto22.lean` | `1397802c4cf13190c9af1e51382d2273ab29decf033ed7f85e2f7f93ac585ed0` | 14434 |
| `lean/Kepler/Assembly.lean` | `91beaba05d77934c63b91d0af2659f58b39f08e3f3c70d5a6b8b7e0a1b6a09fd` | 7195 |

侦察期间 HEAD 前进到 `dcb1a0fb`（`pa22-eusotyp2-assembly-w1` 归档提交，只新增
`c17_backup/.../kit-pa22-eusotyp2-assembly-w1.diff` 等 3 个归档文件，`git diff
117511bb HEAD -- lean/` 为空）。随后该车道把补丁落到工作树并提交为 `f1f41235`
（"PA22 EUSOTYP2_general 真证 (16->15)"，+336/−1；其后 `8635c297` 只动
DECISIONS/priority-queue）：PA22 变为 14769 行，`EUSOTYP2_general`
10827→10930（+103），其后全部声明 +335。本报告的 `行号@117511bb` 为冻结基准，
`live` 列给当前工作树行号；探针用的是 13:28 重建后的 olean（目标声明体未变，
`#print axioms` 结果与 117511bb 一致）。原始 pin 快照见同目录
`PackingAuto22.at117511bb.lean` / `Assembly.at117511bb.lean`。

---

## 1. 闭包算法（不依赖 `#print axioms` 的声明链）

`deps.py` / `closure2.py`：去注释（嵌套 `/- -/` + `--`，保留行号）→ 顶层声明切块
（`theorem/lemma/def/abbrev/instance/...`，块尾=下一声明首行-1）→ 块内整词匹配
文件内全部声明名 → 从 4 个根做 BFS。结果（`python3 -I deps.py`）：

```
parsed 514 decls; sorry decls = 17
=== closure (87 decls) ===
D0 14252 proved DLWCHEM_full
D0 14288 proved XULJEPR_full
D0 14346 proved DLWCHEM_of_stub_bridge
D0 14353 proved XULJEPR_of_stub_bridge
D1  311 proved fat_lemma1
D1 13574 proved facet_3_facets
D1 13584 sorry  YSSKQOY_VECTOR        <- DLWCHEM_full
D1 13609 sorry  YSSKQOY_VECTOR2_ALT   <- XULJEPR_full
D1 13633 proved THETA_BOUNDS
D1 13902 proved LMFUN_INEQ_CENTER_IMP_13
D1 13930 proved SATURATE_BALL_ANNULUS
D1 13966 proved DLWCHEM_VECTOR_sumReal
D1 14045 proved XULJEPR_VECTOR_sumReal
D1 14179 proved existsM_polyhedron_sums (private)
D2 11950 sorry  GOTCJAH                 <- existsM_polyhedron_sums
D2 12792 sorry  polyhedron_edge_sum     <- existsM_polyhedron_sums
D2 13062 sorry  EXISTS_M_POLYHEDRON     <- existsM_polyhedron_sums
D2 13951 sorry  POLYHEDRON_FACET_SUM_4Pi<- existsM_polyhedron_sums
...
（其余 60+ 个节点全部 proved）
```

无深度上限复跑（`closure2.py`）：可达 sorry 集合不变，且 **depth=4 的节点没有任何
sorry 子件**，所以“深度 ≤4”没有截断债务。

```
== reachable sorries (depth) ==
depth=1 13584 YSSKQOY_VECTOR
depth=1 13609 YSSKQOY_VECTOR2_ALT
depth=2 11950 GOTCJAH
depth=2 12792 polyhedron_edge_sum
depth=2 13062 EXISTS_M_POLYHEDRON
depth=2 13951 POLYHEDRON_FACET_SUM_4Pi
reachable sorry: total 6 of 17
```

每个 sorry 的**唯一**已证消费者：

```
GOTCJAH                 -> existsM_polyhedron_sums
polyhedron_edge_sum     -> existsM_polyhedron_sums
EXISTS_M_POLYHEDRON     -> existsM_polyhedron_sums
YSSKQOY_VECTOR          -> DLWCHEM_full
YSSKQOY_VECTOR2_ALT     -> XULJEPR_full
POLYHEDRON_FACET_SUM_4Pi-> existsM_polyhedron_sums
```

源码调用点（`PackingAuto22.at117511bb.lean`）：

- `DLWCHEM_full` 体：`:14267 exact YSSKQOY_VECTOR ...`；`:14273 existsM_polyhedron_sums`；
  `:14278 DLWCHEM_VECTOR_sumReal`；`:14266/14270 THETA_BOUNDS`。
- `XULJEPR_full` 体：`:14318 exact YSSKQOY_VECTOR2_ALT ...`；`:14332 existsM_polyhedron_sums`；
  `:14336 XULJEPR_VECTOR_sumReal`。
- `existsM_polyhedron_sums`（private, `:14179`）体：`:14199 EXISTS_M_POLYHEDRON`、
  `:14205 polyhedron_edge_sum`、`:14222 GOTCJAH`、`:14238 POLYHEDRON_FACET_SUM_4Pi`。

---

## 2. `#print axioms` 原始输出（standalone lean，`LEAN_PATH=$(cat /tmp/lfainteg/asm_check/leanpath.txt)`）

`probe1.log`（import `Kepler.Text.PackingAuto22`）：

```
'Kepler.Text.DLWCHEM_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_of_stub_bridge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_of_stub_bridge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR2_ALT' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.GOTCJAH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_edge_sum' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.EXISTS_M_POLYHEDRON' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_FACET_SUM_4Pi' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.facet_3_facets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.THETA_BOUNDS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.LMFUN_INEQ_CENTER_IMP_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SATURATE_BALL_ANNULUS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_VECTOR_sumReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.regularSphericalPolygonAreaP22' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FACET_SOL_NN' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.weaklySaturatedP22' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_3_facets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.DLWCHEM_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.XULJEPR_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BIEFJHU_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.UKBRPFE_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FCHANGED_MEASURABLE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SOL_NN' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.arclength22' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.packIneqDefAP22' does not depend on any axioms
'Kepler.Text.PACK_INEQ_DEF_A_797' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY_VECTOR2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`probe2.log`（PA22 前置 + PackingAuto18 Ysskqoy 银行）：

```
'Kepler.Text.gotcjah_prep' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.gotcjah_sol_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.convex_sum_corollary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.ORDER_AZIM_SUM2Pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.SOL_SUBSET' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FCHANGED_RADIAL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EMPTY_NOT_EXISTS_IN' depends on axioms: [propext, Quot.sound]
'Kepler.Text.WEDGE_ORDER_DISJOINT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.EUSOTYP2_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FACET_OF_POLYHEDRON_EXPLICIT_ALT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.rcone_gt_facet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.rcone_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.rcone_dot_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.cos_bounds_0_Pi2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.polyhedron_sum_sum_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.FINITE_EDGE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_TGJISOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.BIJ_FACET_HYPERFACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.BIJ_DART_POLYEDGE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.POLYHEDRON_CONFORMING_FAN' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.YSSKQOY' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.arc_derivative' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.arc_derivative2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.arc_length1_increasing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.arc_length2_increasing' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Text.yssk_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.arclength2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.arc_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.arcLength' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`probe3b.log`（import `Kepler.Assembly`）：

```
'Kepler.Text.ContraFanDeep.cf4_LEMMA_4_POINTS_FINAL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Assembly.localAnnulusInequalityScriptL' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Assembly.fcdjdot' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

（`Kepler.Text.contraveningFanTl`/`LEMMA_4_POINTS_FINAL` 实为
`Kepler.Text.ContraFan.*` 命名空间，探针名未解析；其下端
`cf4_LEMMA_4_POINTS_FINAL` 已标准三 ⇒ Assembly:4339 的“继承 CKQOWSA 债务”注记已过时。）

`probe3.lean`（同时 import PA22 + Assembly）失败，**结构性证据**：

```
/tmp/.../probe3.lean:1:0: error: import Kepler.Text.IneqClosureDefs failed,
environment already contains 'Kepler.Text.sqrt3' from Kepler.Text.PackingAuto22
```

→ `Assembly → PackingAuto22` 的直接 import 当前被 `Kepler.Text.sqrt3` 双胞胎挡死
（PA22:176 与 IneqClosureDefs:719 都是 `noncomputable def sqrt3 : ℝ := Real.sqrt 3`；
LocalAuto1.lean:981-984 有同款记录：“importing both fails … The needed bodies are
therefore copied verbatim under the `_t11` suffix”）。PA22 内 `sqrt3` 用量 231 处、全部
在本文件；IneqClosureDefs 内 5 处、LocalAuto1 3 处。

---

## 3. `#check` 陈述形状（probe1 原文，节选）

```
DLWCHEM_full : ∀ (V : Set Kepler.Geom.V3), Kepler.Packing V → packIneqDefAP22 →
  V ⊆ ballAnnulus → ¬localAnnulusInequality V → V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15
XULJEPR_full : ∀ (V : Set Kepler.Geom.V3), Kepler.Packing V → V ⊆ ballAnnulus →
  packIneqDefAP22 → (∃ v ∈ V, ‖v‖ = 2 ∧ ∀ u ∈ V, u ≠ v → 2 * h0 ≤ dist u v) →
  localAnnulusInequality V
YSSKQOY_VECTOR : ∀ (v w : V3) (theta : V3 → ℝ), v ∈ ballAnnulus → w ∈ ballAnnulus →
  v ≠ w → 2 ≤ dist v w → (fun v => acs (‖v‖ / 4) - Real.pi / 6) = theta →
  theta v + theta w ≤ Kepler.Geom.arcV 0 v w
YSSKQOY_VECTOR2 : ∀ (v0 w : V3), v0 ∈ ballAnnulus → w ∈ ballAnnulus → w ≠ v0 →
  2 * h0 ≤ dist w v0 → packIneqDefAP22 → ‖v0‖ = 2 →
  0.797 + acs (‖w‖ / 4) - Real.pi / 6 ≤ Kepler.Geom.arcV 0 v0 w
YSSKQOY_VECTOR2_ALT : ∀ (V) (v w v0) (theta), V ⊆ ballAnnulus → Packing V → v ∈ V →
  w ∈ V → v0 ∈ V → v ≠ w → (∀ w ∈ V, w ≠ v0 → 2*h0 ≤ dist w v0) → packIneqDefAP22 →
  ‖v0‖ = 2 → (fun v => if v = v0 then 0.797 else acs (‖v‖/4) - π/6) = theta →
  theta v + theta w ≤ arcV 0 v w
GOTCJAH : ... polyhedron P → IsBounded P → 0 < b → 0 ∈ interior P → FacetOf c P →
  fchanged c = WF → 0 < t ∧ t < 1 → (c = P ∩ {p | p·v = b} ∧ rconeGt 0 v t ⊆ WF) →
  ({u | FacetOf u c}.Finite ∧ {u | FacetOf u c}.ncard = n) →
  2π - 2n·asn(t·sin(π/n)) ≤ sol 0 WF
polyhedron_edge_sum : ... IsBounded P → polyhedron P → 0 ∈ interior P → hsize → 2 ≤ n →
  ∑ f ∈ hsize.1.toFinset, {e | FacetOf e f}.ncard ≤ 6*n - 12
EXISTS_M_POLYHEDRON : ... 12-conjunct existential (b, f, h, P) ...
POLYHEDRON_FACET_SUM_4Pi : polyhedron P → IsBounded P → 0 ∈ interior P →
  setSum {c | FacetOf c P} (fun c => sol 0 (fchanged c)) = 4 * Real.pi
```

前置定义全部可达（`#check` 通过）：`Kepler.Geom.arcV : V3→V3→V3→ℝ`、
`Kepler.Geom.sol : V3→Set V3→ℝ`、`Kepler.Packing : Set Kepler.Space3→Prop`、
`FacetOf/polyhedron/fchanged : Set V3 → ...`、`rconeGt`、`ballAnnulus`、`h0`、`acs`、`asn`。

---

## 4. 判“在路径上”的 HOL 证据（counting_spheres.hl，行号为 HOL 原文件）

`python3 -I holspans.py`（HOL `let` 块跨度；tactics 近似）：

```
7063  DLWCHEM                 lines=124  tactics~76
7191  XULJEPR                 lines=146  tactics~95
6490  YSSKQOY_VECTOR          lines=50   tactics~26
6599  YSSKQOY_VECTOR2         lines=25   tactics~11
6624  YSSKQOY_VECTOR2_ALT     lines=33   tactics~10
5888  EXISTS_M_POLYHEDRON     lines=267  tactics~170
4366  GOTCJAH                 lines=195  tactics~163
5476  polyhedron_edge_sum     lines=148  tactics~87
6245  POLYHEDRON_FACET_SUM_4Pi lines=34  tactics~17
6679  THETA_BOUNDS            lines=25   tactics~16
6175  LMFUN_INEQ_CENTER_IMP_13 lines=46  tactics~25
6221  SATURATE_BALL_ANNULUS   lines=24   tactics~5
6814  DLWCHEM_VECTOR_sum      lines=91   tactics~60
6905  XULJEPR_VECTOR_sum      lines=121  tactics~85
6540  PACK_INEQ_DEF_A_797     lines=59
```

HOL 体内引用的同文件声明（整词匹配）：

```
YSSKQOY_VECTOR          -> [ckq_in_ball_annulus] (+ external Ysskqoy.YSSKQOY)
YSSKQOY_VECTOR2         -> [PACK_INEQ_DEF_A_797, ckq_in_ball_annulus]
YSSKQOY_VECTOR2_ALT     -> [YSSKQOY_VECTOR, YSSKQOY_VECTOR2]
GOTCJAH                 -> [EMPTY_NOT_EXISTS_IN, EUSOTYP2_general, FCHANGED_MEASURABLE,
                            FCHANGED_RADIAL, GOTCJAH_concl, ORDER_AZIM_SUM2Pi, SOL_SUBSET,
                            WEDGE_ORDER_DISJOINT, convex_sum_corollary, gotcjah_prep,
                            gotcjah_sol_lemma]
EXISTS_M_POLYHEDRON     -> [FACET_OF_POLYHEDRON_EXPLICIT_ALT, cos_bounds_0_Pi2,
                            rcone_dot_pos, rcone_gt_facet, rcone_refl]
polyhedron_edge_sum     -> [BIJ_DART_POLYEDGE, BIJ_FACET_HYPERFACE, BIJ_SYM, BIJ_TRANS,
                            FINITE_EDGE, POLYHEDRON_TGJISOK, polyhedron_sum_sum_edge]
POLYHEDRON_FACET_SUM_4Pi-> [POLYHEDRON_CONFORMING_FAN] (+ POLYHEDRON_FAN, AMHFNXP_BIJ,
                            SUM_SOL_IN_FACE_SET_E... external)
DLWCHEM                 -> [... YSSKQOY_VECTOR, EXISTS_M_POLYHEDRON, GOTCJAH,
                            polyhedron_edge_sum, POLYHEDRON_FACET_SUM_4Pi, THETA_BOUNDS ...]
XULJEPR                 -> [... YSSKQOY_VECTOR2_ALT, EXISTS_M_POLYHEDRON, GOTCJAH,
                            polyhedron_edge_sum, POLYHEDRON_FACET_SUM_4Pi, THETA_BOUNDS ...]
```

HOL `POLYHEDRON_FACET_SUM_4Pi` 的 34 行是假象：证明体里 `INTRO_TAC
Conforming.SUM_SOL_IN_FACE_SET_EQ_4PI` + `Polyhedron.POLYHEDRON_FAN` +
`POLYHEDRON_CONFORMING_FAN` + `Polyhedron.AMHFNXP_BIJ` +
`SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET` 五件全在外部章（Lean 树内：
`POLYHEDRON_CONFORMING_FAN` 仍 sorry@12185；其余三件 ABSENT）。

**YSSKQOY_VECTOR 的上游**：HOL 核心是 `Ysskqoy.YSSKQOY`（YSSKQOY.hl:531-549），其
Lean 双胞胎 `Kepler.Text.YSSKQOY`（PackingAuto18:1622）**仍 sorry**，且同文件另有
4 条链上 sorry：

```
YSSKQOY.hl:365  arc_derivative          35 行 -> PackingAuto18:1593 sorry
YSSKQOY.hl:400  arc_derivative2         47 行 -> PackingAuto18:1601 sorry
YSSKQOY.hl:447  arc_length2_increasing  44 行 -> PackingAuto18:1608 sorry
YSSKQOY.hl:491  arc_length1_increasing  40 行 -> PackingAuto18:1614 sorry
YSSKQOY.hl:531  YSSKQOY                 22 行 -> PackingAuto18:1622 sorry
（已证：arcLength 1118 / arclength2 1510 / yssk_reduction 1570 / arc_sym 1502）
```

并且 `arcV ↔ arcLength` 的桥（HOL `Trigonometry1.arcVarc` + `ACS_ARCLENGTH`）在 Lean
全树 **不存在**（`grep -rn "arcVarc|ACS_ARCLENGTH" lean/Kepler` = 0 命中）→
YSSKQOY_VECTOR 不是 50 行的搬运。

---

## 5. `PACK_INEQ_DEF_A_797` 是 DEFHOLE（当前陈述为假）

`PackingAuto22:13926-13934 @117511bb`：

```
/-- NEEDS HOL `arclength` (pack1.hl; PackingAuto1, no olean). Stub: 0. -/
noncomputable def arclength22 (r h d : ℝ) : ℝ := 0
...
theorem PACK_INEQ_DEF_A_797 ... :
    0.797 + acs (‖v‖ / 4) - Real.pi / 6 < arclength22 (‖v‖) 2 (dist v v0) := by sorry
```

取 `v = -v0`、`‖v0‖ = 2`：`dist v v0 = 4 ≥ 2*h0`，`‖v‖ = 2`，假设全满足；
LHS `= 0.797 + acs(1/2) - π/6 = 0.797 + π/3 - π/6 ≈ 1.3206 > 0 = RHS`。
⇒ 该陈述在 `hpa : packIneqDefAP22 (= True)` 下**可反驳**，不能靠填 sorry 变绿；
必须先修陈述（把 `arclength22` 换成 PA18 的真 `arcLength`，并把
`packIneqDefAP22 := True`（PA22:306）/ `PackIneqDefA := True`（Assembly:279）真化）。
`arclength22` 全树唯一消费者就是这条（grep 仅 :13592/:13598）。

---

## 6. fcdjdot 本体输入（Assembly 侧证据）

四柱（`Assembly.lean`）：

```
4206 theorem localAnnulusInequalityScriptL (V : Set V3) :
       localAnnulusInequality V ↔ scriptL V ≤ 12        -- proved, std3 (probe3b)
4408 private theorem bijScriptL {V W} (hV : V.Finite) (f) (hbij : Set.BijOn f V W)
       (hnorm : ∀ u ∈ V, ‖u‖ = ‖f u‖) : scriptL V = scriptL W
4710 private theorem scriptLAttainsMaxInBallAnnulus :
       ∃ W, Packing W ∧ W ⊆ ballAnnulus ∧ ∀ V, Packing V → V ⊆ ballAnnulus → scriptL V ≤ scriptL W
6202 private theorem fnjlbxsCore {V} (hpack) (hsub) :
       ∃ W φ, Set.BijOn φ V W ∧ Packing W ∧ W ⊆ ballAnnulus ∧ (∀ v ∈ V, ‖v‖ = ‖φ v‖) ∧
         ∀ w ∈ W, setOfEdge w W (ESTD W) = ∅ ∨ surroundedNode W (ESTD W) w
4206 之上另有 private notSurroundedNodeNormECTC (5811)、isolatedNodeNormECTC (5563)、
       notSurroundedECTC (5352)；ECTC ⊆ ESTD 已在 :4168 内联证过 (have hECTCsub)。
```

`Contravening`（Assembly:113-119）七合取；`ESTD/ECTC/scriptL`（Assembly:87/92/99）与
HOL `tame_defs.hl:207/210/245` 逐句镜像；`PackIneqDefA : Prop := True`（Assembly:279）。

HOL `FCDJDOT`（FNJLBXS-compiled.hl:1766-1797，~32 行 ssreflect）只做四件事：
① `scriptL_attains_max_in_ball_annulus` 取 W1；② `FNJLBXS` 归一化得 V/φ；
③ `bij_scriptL` 搬 `scriptL V = scriptL W1 > 12`；④ 七合取收尾（DLWCHEM 的 ncard 三分、
XULJEPR 的 `¬localAnnulusInequality` 反证 + 两个 surrounded 合取经
`not_surrounded_node_norm_ECTC`/`isolated_node_norm_ECTC`）。

**落点结论**：本体必须在 `Assembly.lean`（四柱里 3 个是 Assembly 的 private 声明，
PA22 无法 import Assembly——方向相反）。但 `Assembly` 现在既没有 import PA22
（imports 24-65 无 PackingAuto22），**也 import 不了**（sqrt3 撞名，见 §2 的 probe3
失败）。所以本体落地 = 两次 Assembly 编辑（`import Kepler.Text.PackingAuto22` + 本体体）
外加一次 PA22/ICD 的 `sqrt3` 去重（建议把 PA22:176 改 `private`，231 处全在文件内；
或把 IneqClosureDefs:719 改 private，那里只有 5 处）→ 属“需独立车道 + 冻结面审计”。

本体规模：HOL 32 行；Lean 侧需要展开 7 合取 + 两次 `¬localAnnulusInequality` 换算
（`localAnnulusInequalityScriptL.mpr` 的逆否），估 **150-300 行**（计划注释的
200-400 行同量级；不含柱①-④本身）。

---

## 7. 关于“YSSKQOY_VECTOR 的 DISCHARGES 注记点名 EXISTS_M_POLYHEDRON/THETA_BOUNDS”

全树 grep `DISCHARGES`：仅 `LocalAuto33.lean:2431`、`docs/*`，PA22 的
`YSSKQOY_VECTOR` 块（13583-13592）**没有 DISCHARGES 注记**（只有 docstring
“HOL `YSSKQOY_VECTOR` (counting_spheres.hl:6490). GIANT (Ysskqoy bank).”）。

不存在闭环：`YSSKQOY_VECTOR` 的陈述只含 `ballAnnulus/dist/arcV/acs`，不含
`EXISTS_M_POLYHEDRON`；`THETA_BOUNDS` 是独立已证叶子（std3）；`EXISTS_M_POLYHEDRON`
不引用 `YSSKQOY_VECTOR`。HOL 侧 `DLWCHEM` 同时消费二者，是并列而非互引。⇒ **无环**。
（若编排者手里的 DISCHARGES 注记来自别处版本，本条标 UNRESOLVED-出处，但环本身已排除。）
