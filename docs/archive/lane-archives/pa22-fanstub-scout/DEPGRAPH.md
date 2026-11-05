# DEPGRAPH — `PackingAuto22.lean` 多面体簇的假桩依赖图

HEAD `ec57d345`；行号均指该 commit 的 `lean/Kepler/Text/PackingAuto22.lean`。
本文件只写机器可核的事实（`grep` 命令 + `#print axioms` 实测见 `EVIDENCE.md`）。

## 0. 关键结论先说

1. **`POLYHEDRON_TGJISOK` 在 Lean 侧零消费者**。全树 `grep -rn POLYHEDRON_TGJISOK Kepler/`
   只有 PA22:12804/12806（声明自身）。它是"关于空 hypermap 的真定理"，
   公理面干净（标准三），但**没有一条陈述吃它**。真正的假桩在**定义层**。
2. 多面体簇的假桩不是两条，而是**七个 `_p22` 定义**：
   `hypermap1OfFanxP22`（`darts := ∅`，`edgeMap/nodeMap/faceMap := refl`）、
   `dFanP22`（派生）、`d1FanP22`（`∅`）、`eFanP22`（`id`）、
   `verticesP22`（`∅`）、`edgesP22`（`∅`）、
   `dartsetLeadsIntoFanP22`（`∅`）、`topologicalComponentYfanP22`（`True`）。
3. 因此 #4/#5/#6/#7/#8 **不是"被假桩卡住"，而是"在现桩下为假"**（见 §2 的机器证伪）。
4. **这一簇里有一个"完全不吃假桩"的件：#10 `EXISTS_M_POLYHEDRON`**
   （陈述只用 `polyhedron`/`FacetOf`/`rconeGt`/`fchanged`，源证明也不引用任何 `_p22`
   fan 定义）。其余全部经由定义层或多或少的假桩。
5. **上游其实基本已移植完**：`FAN` / `hypermapOfFan` / `dartsetLeadsIntoFan` /
   `topologicalComponentYfan` / `conformingFan` / `PIIJBJK` / `WGVWSKE` /
   `AMHFNXP_BIJ` / `WBLARHH` / `POLYHEDRON_FAN` / `SUM_SOL_*` 全在树内且
   `#print axioms` = 标准三（§4 有清单）。缺的只有 `WBLARHH_BIJ`（12 行推论）
   和一处 `vertices/edges` 桥接。

## 1. 依赖图（`A --> B` = B 的证明/陈述吃 A）

```
[定义层假桩]
  hypermap1OfFanxP22  (darts := ∅, 三映射 := refl)
      |-- dFanP22 = darts
      |-- POLYHEDRON_D1_D      (proved std3, VACUOUS: dFan = d1Fan = ∅)
      |-- POLYHEDRON_PLAIN     (proved std3, VACUOUS: refl 是 plain)
      |-- POLYHEDRON_NODE_3    (proved std3, VACUOUS: hx : x ∈ ∅ 直接矛盾)
      |-- POLYHEDRON_TGJISOK   (proved std3, VACUOUS: 0 ≤ 6·0-12 经 Nat 截断)
      |-- EDGE_pr23            (proved std3, VACUOUS: hy : y ∈ ∅)
      |-- INJ_EDGES_FACE_pr23  (proved std3, VACUOUS: faceSet = ∅)
      |-- p22_faceSet_stub     (private, proved)
      |-- #4 BIJ_FACET_HYPERFACE   <-- FALSE (codomain faceSet = ∅, domain 非空)
      |-- #7 HYPERFACE_EXISTS      <-- FALSE (f ∈ ∅)
      |-- #8 BIJ_DART_POLYEDGE     <-- FALSE (domain darts = ∅, codomain 非空)
  eFanP22 (id)
      |-- #6 EDGE_PAIR_pr23        <-- FALSE (h : d = d' 后仍要求 pr2 d = pr3 d)
      |-- EDGE_pr23                (VACUOUS)
  verticesP22 = ∅ , edgesP22 = ∅
      |-- #5 POLYHEDRON_CONFORMING_FAN <-- FALSE (Fan.FAN 0 ∅ ∅ 假, fan1 要 V ≠ ∅)
  dartsetLeadsIntoFanP22 = ∅
  topologicalComponentYfanP22 = True
      |-- #7 HYPERFACE_EXISTS      <-- FALSE
[真定义/真情形的假桩旁路]
  #10 EXISTS_M_POLYHEDRON  (NEEDS-MATH; 唯一 fake-stub-free 的簇内件)
[簇内的真依赖（来自 HOL 证明，不是 Lean 陈述）]
  #4 --+
  #8 --+--> #9 polyhedron_edge_sum   <-- BLOCKED (HOL:5476 证明确调 #4/#8/真TGJISOK)
  (真) POLYHEDRON_TGJISOK --+
  #5 --> #14 POLYHEDRON_FACET_SUM_4Pi <-- BLOCKED (HOL:6245 证明确调 #5)
[柱③ 的 797 支线（与本簇不相交）]
  #11 PACK_INEQ_DEF_A_797 --> #12 YSSKQOY_VECTOR2 --> #13 YSSKQOY_VECTOR2_ALT --> XULJEPR_full
  #11/#12 全树零消费者（grep 实测）；#13 唯一消费者 = XULJEPR_full:15105
```

## 2. 哪些件"在现桩下为假"（机器证伪，RC=0，全部标准三）

`logs/probe_false.lean`（对 `bx` 这个具体有界多面体实例化假设）：

| # | 陈述 | 证伪定理 | 一句话理由 |
|---|---|---|---|
| #4 | `BIJ_FACET_HYPERFACE` | `ProbeFanStub.refute_BIJ_FACET_HYPERFACE` | `faceSet = ∅`，`BijOn b A ∅` 强制 `A = ∅`，而 `polyhedron_3_facets` 给 ≥3 个 facet |
| #5 | `POLYHEDRON_CONFORMING_FAN` | `refute_POLYHEDRON_CONFORMING_FAN` | `verticesP22 p = ∅` ⇒ `Fan.FAN 0 ∅ ∅`；其 `fan1 = V.Finite ∧ V ≠ ∅` 为假 |
| #6 | `EDGE_PAIR_pr23` | `probe_EDGE_PAIR_pr23_false` | `eFanP22 = id` ⇒ `h : d = d'`，结论退化为 `∀ d, pr2 d = pr3 d` |
| #7 | `HYPERFACE_EXISTS` | `refute_HYPERFACE_EXISTS` | 结论是 `∃! f, f ∈ ∅ ∧ …`，无见证 |
| #8 | `BIJ_DART_POLYEDGE` | `refute_BIJ_DART_POLYEDGE` | `darts = ∅`，但 `(f1, e) ∈ {fe | FacetOf fe.2 fe.1 ∧ FacetOf fe.1 P}` 非空（`facet_3_facets`） |
| #3 | `vol_solid_triangle_ortho` | 手工反例（见 EVIDENCE §A3） | `volSolidTriangleP22 := 0` ⇒ LHS=0；`u=e0,v=e1,w=e0+e2` 给 RHS=π/4 |

## 3. "不吃假桩"的子集

**簇内（#4–#10、#14）：只有 #10 `EXISTS_M_POLYHEDRON` 完全不吃假桩。**
- #9 / #14 的**陈述**不吃假桩（只用 `FacetOf`/`sol`/`fchanged`），但 HOL 证明吃 #4/#8/#5。
- #11/#12/#13 在簇外（797 支线），陈述与证明都不吃 fan 假桩。

因此**没有"可以先按波施工、且零 DEF-FIX"的多面体子集可挖**——除 #10 一条独立大件。
若先做 DEF-FIX，则 #4/#5/#7/#8 可在 1–2 波内转真（§4），#9/#14 紧随其后。

## 4. 上游移植现状（全部 `#print axioms` = `[propext, Classical.choice, Quot.sound]`）

| HOL 件 | Lean 位置 | 状态 |
|---|---|---|
| `FAN` | `Kepler/Text/Fan.lean:56` | def，std3 |
| `hypermap_of_fan` | `Fan.lean:1189 hypermapOfFan` | 需 `hfan : FAN` 见证，std3 |
| `dartset_leads_into_fan` | `PlanarityComponent.lean:348` | 需 hfan，std3 |
| `topological_component_yfan` | `Fan.lean:199` | std3 |
| `fan80` / `e_fan_pair` / `dart1_of_fan` | `Fan.lean:227/…` | std3 |
| `conforming_fan` + 4 子谓词 | `ConformingDefs.lean:184` | 需 hfan，std3 |
| `PIIJBJK`（`POLYHEDRON_CONFORMING_FAN` 的核心） | `ConformingAuto21.lean:903` | **已证**，std3 |
| `WGVWSKE`（TGJISOK 的输入） | `ConformingAuto23.lean:1899` | **已证**，std3 |
| `lemmaTGJISOK` | `Hypermap.lean:1637 darts_card_le` | **已证**，std3 |
| `AMHFNXP_BIJ` | `PolyAuto7.lean:1314` | **已证**，std3 |
| `WBLARHH` | `PolyAuto7.lean:3158` | **已证**，std3 |
| `WBLARHH_BIJ` | — | **未移植**（PolyAuto7:23-26 明说是 WBLARHH+PIIJBJK 的 ~12 行推论） |
| `POLYHEDRON_FAN` | `PolyAuto3.lean:1608` | **已证**，std3（但用的 E 是内联边集，需与 `Polytope.edges` 桥） |
| `POLYTOPE_FAN80` | `PolyAuto7.lean` | 已证，std3 |
| `CARD_SET_OF_EDGE_INEQ_1_POLYHEDRON` | `PolyAuto7.lean:2593` | 已证，std3 |
| `SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET` | `ConformingAuto5.lean:124` | 已证，std3 |
| `SUM_SOL_IN_FACE_SET_EQ_4PI` | `ConformingAuto6.lean:735` | 已证，std3 |
| `PREIMAGE_BIJ`/`BIJ_SYM`/`BIJ_TRANS` | `PackingAuto22.lean:12729/12708/12714` | 已证，std3 |
| `polyhedron_3_facets` / `facet_3_facets` / `FINITE_EDGE` / `polyhedron_sum_sum_edge` | `PackingAuto22.lean` | 已证，std3 |

## 5. 建议施工顺序（DEF-FIX 通道，见 C4）

W0（1 波，纯定义 + 桥）：
1. `verticesP22`/`edgesP22` 换成 `Set.extremePoints ℝ p` / `Polytope.edges p`（新增 DEF-FIX 章程）；
2. 用 `POLYHEDRON_FAN` 造 `FAN 0 (vertices p) (edges p)` 见证；
3. `hypermap1OfFanxP22` 换成 `hypermapOfFan 0 … hfan`；`Dart3` 从 `V3×V3×V3` 换成 `V3×V3`；
4. `eFanP22` → `eFanPair`，`d1FanP22` → 真 `d1_fan`，`dartsetLeadsIntoFanP22` → `dartsetLeadsIntoFan`，
   `topologicalComponentYfanP22` → `Fan.topologicalComponentYfan`。
   （签名要加 `hfan`：属 DEF-FIX/SF 辖区，不是普通重构。）
W1：`WBLARHH_BIJ`（12 行）+ 重证 #5（~30）、#7（~30）、#4（~40）。
W2：重证 #8（~120，HOL 116 行）。
W3：重证 #9（~60）、#14（~50）。
W4：#10（~400，独立）。
