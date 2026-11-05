# WAVES.md — 柱③ 清理波次（DLWCHEM_full / XULJEPR_full）

lane `pa22-fcdjdot-pillars-recon-w1` · 只读侦察产出 · 基准 `117511bb`
（live=`dcb1a0fb` + 工作树 eusotyp2 补丁；本文件行号除注明外均为 `117511bb`）

## 0. 基线账（先对齐口径）

- PA22 own-sorry @`117511bb` = **16**（任务书 16 条；外加 `insert_v` 的 DEF-FIX
  body-sorry 共 17 个 `sorry` token，`insert_v` 不在 16 条清单内且 OFF-PATH）。
- 侦察期间 `pa22-eusotyp2-assembly-w1` 落地 `EUSOTYP2_general`（10827→proved），
  故 live 基线 = **15**。
- 柱③ 真依赖 still-sorry：**6 经句法闭包 + 2 经 HOL 意图 = 8**（见 DEPS.txt）：
  - 真在路径（6）：`YSSKQOY_VECTOR`、`YSSKQOY_VECTOR2_ALT`、`GOTCJAH`、
    `polyhedron_edge_sum`、`EXISTS_M_POLYHEDRON`、`POLYHEDRON_FACET_SUM_4Pi`
  - 经 HOL 意图追加（2）：`YSSKQOY_VECTOR2`、`PACK_INEQ_DEF_A_797`
  - 可跳过（句法上）：无——6 条全部在 `DLWCHEM_full`/`XULJEPR_full` 的证明项里
    （分别经直接调用或 `existsM_polyhedron_sums` 枢纽）。
- 分类：**S 0 条 / M 2 条 / L 3 条 / BLOCKED 2 条 / DEFHOLE 1 条**（8 条口径）。
- 最大单件：`EXISTS_M_POLYHEDRON`（HOL 267 行，估 **350-500** Lean 行）。
- `POLYHEDRON_FACET_SUM_4Pi` **在路径上**（`existsM_polyhedron_sums:14238` 的 4π 端），
  但 34 行 HOL 是假象：五件外部依赖（`POLYHEDRON_FAN`/`POLYHEDRON_CONFORMING_FAN`/
  `AMHFNXP_BIJ`/`SUM_SOL_IN_FACE_SET_EQ_4PI`/`SUM_SOL_IN_TOPOLOGICAL_COMPONENET…`）
  在 Lean 侧 1 sorry + 3 ABSENT ⇒ **BLOCKED，不可跳过**。

## 1. 三波 + 一条阻塞尾（必须一起读）

> 诚实结论先行：**三波不能把柱③清成标准三**。三波清掉 6 条句法依赖中的 4 条、
> 以及 2 条 HOL 意图件；`polyhedron_edge_sum` 与 `POLYHEDRON_FACET_SUM_4Pi` 必须
> 等 fan/Conforming lane，故 `DLWCHEM_full`/`XULJEPR_full` 的 `sorryAx` 在三波后
> 仍会由这两条供给。若编排者要“柱③零 sorryAx”，需把「尾」排成第 4 波并入 fan lane。

```
W1 GOTCJAH ─────────────┐
                        ├─→ existsM_polyhedron_sums（枢轴）─→ DLWCHEM_full / XULJEPR_full
W2 EXISTS_M_POLYHEDRON ─┘                                        ↑
W3 Ysskqoy 三件 + arclength 真化 ────────────────────────────────┘
尾 polyhedron_edge_sum + POLYHEDRON_FACET_SUM_4Pi（BLOCKED；fan 车道输入，暂不排期）
```

依赖序说明：W1 与 W2 相互独立（都只喂 `existsM_polyhedron_sums`，彼此不互吃）；
W3 与 W1/W2 独立（`YSSKQOY_VECTOR` 直接喂 `DLWCHEM_full:14267`，`_ALT` 直接喂
`XULJEPR_full:14318`），但 W3 内部有严格序：`arclength 真化 → YSSKQOY_VECTOR →
YSSKQOY_VECTOR2 → PACK_INEQ_DEF_A_797 → YSSKQOY_VECTOR2_ALT`。

---

## W1 — `GOTCJAH`（M）

| 项 | 内容 |
|---|---|
| 目标件 | `GOTCJAH`（11950；live 12285）单件 |
| 依赖序 | 前置 10 件全部已证且 `std3`（探针：`gotcjah_prep` 11647、`gotcjah_sol_lemma` 11477、`convex_sum_corollary` 11902、`ORDER_AZIM_SUM2Pi` 9534、`SOL_SUBSET` 11937、`FCHANGED_RADIAL` 10006、`EMPTY_NOT_EXISTS_IN` 7512、`WEDGE_ORDER_DISJOINT` 9518、`EUSOTYP2_general` 10827→已闭） ⇒ **无阻塞，可直接开工** |
| HOL 锚 | `counting_spheres.hl:4366-4560`（195 行，tactics~163） |
| 预估 Lean | **200-350 行**（同区 HOL→Lean 比 0.77-1.7×：EUSOTYP2 341→262、gotcjah_prep 102→79、sol_lemma 143→110） |
| 验收 | PA22 own-sorry 15→14；`#print axioms Kepler.Text.GOTCJAH` = `[propext, Classical.choice, Quot.sound]`；`existsM_polyhedron_sums:14222` 调用点零改写通过 |
| 波间前置 | 产物是 W2 之后 `existsM_polyhedron_sums` 转标准三的必要输入（不是 W2 的输入） |
| 风险/止损 | 唯一风险 = 几何 case split 膨胀。若超 **450 行**：不再硬推，按 `gotcjah_prep`/`sol_lemma` 已闭的分界拆成「facet-side 角度和」与「sol 下界」两个子件回交，单独成波 |

## W2 — `EXISTS_M_POLYHEDRON`（L，最大单件）

| 项 | 内容 |
|---|---|
| 目标件 | `EXISTS_M_POLYHEDRON`（13062；live 13397）单件 |
| 依赖序 | 前置 5 件全部已证且 `std3`：`FACET_OF_POLYHEDRON_EXPLICIT_ALT` 12896、`rcone_gt_facet` 12054、`rcone_refl` 11965、`rcone_dot_pos` 11978、`cos_bounds_0_Pi2` 11986 ⇒ **无阻塞** |
| HOL 锚 | `counting_spheres.hl:5888-6154`（267 行，tactics~170；12 合取存在式） |
| 预估 Lean | **350-500 行**（12 合取的 `refine ⟨…⟩` 簿记 + rcone 包含 + b=‖v‖cosθ） |
| 验收 | own-sorry 14→13；`#print axioms Kepler.Text.EXISTS_M_POLYHEDRON` = `std3`；`existsM_polyhedron_sums:14199` 解构零改写通过 |
| 波间前置 | 与 W1 合流后 `existsM_polyhedron_sums` 只剩 `polyhedron_edge_sum`+`POLYHEDRON_FACET_SUM_4Pi` 两条债 |
| 风险/止损 | **本件就是“超 450 单独成波”的候选**（估上界 500）。若超 600：拆 (a) facet 显式刻画与 `b>0`、(b) `Set.BijOn f V facets`（满射是最重的一段）、(c) `b=‖v‖cosθ` + `rconeGt ⊆ fchanged`；三段各自可独立验收 |

## W3 — Ysskqoy 三件 + `arclength` 真化（L，跨车道）

| 项 | 内容 |
|---|---|
| 目标件 | `YSSKQOY_VECTOR`(13584)、`YSSKQOY_VECTOR2`(13602)、`PACK_INEQ_DEF_A_797`(13595)、`YSSKQOY_VECTOR2_ALT`(13609) |
| 依赖序（严格） | ① `arcV ↔ arcLength` 桥（**ABSENT**，HOL `Trigonometry1.arcVarc`+`ACS_ARCLENGTH`）→ ② PA18 银行 5 件（`arc_derivative` 1593、`arc_derivative2` 1601、`arc_length2_increasing` 1608、`arc_length1_increasing` 1614、`YSSKQOY` 1622，全 sorry）→ ③ `YSSKQOY_VECTOR` → ④ `YSSKQOY_VECTOR2` → ⑤ `PACK_INEQ_DEF_A_797`（**先改陈述**）→ ⑥ `YSSKQOY_VECTOR2_ALT` |
| HOL 锚与行数 | `YSSKQOY_VECTOR` 6490-6539（50）；`YSSKQOY_VECTOR2` 6599-6623（25）；`PACK_INEQ_DEF_A_797` 6540-6598（59）；`YSSKQOY_VECTOR2_ALT` 6624-6656（33）；上游 `YSSKQOY.hl` 5 件合计 188 行 |
| 预估 Lean | **600-1150 行**：桥 100-250（UNRESOLVED）、PA18 银行 250-450、PA22 四件 250-450 |
| 验收 | own-sorry 13→9（4 条转 `std3`）；`YSSKQOY_VECTOR`/`YSSKQOY_VECTOR2`/`PACK_INEQ_DEF_A_797`(修后)/`YSSKQOY_VECTOR2_ALT` 全部无 `sorryAx`；`DLWCHEM_full:14267`、`XULJEPR_full:14318` 两调用点零改写 |
| 波间前置 | 需要 **PA18 Ysskqoy 银行**（跨车道，属 PA18/LA18 责任田；`arc_length1_increasing` 等 5 条不清，本条无望）。W3 不依赖 W1/W2，可在 W1/W2 之外并行（但占同一文件 PA22，须串行改同一文件的窗口） |
| 风险/止损 | ① `PACK_INEQ_DEF_A_797` 现陈述**可反驳**（`arclength22 := 0`，取 v=-v0 得 `1.3206 < 0`）：这不是“填证明”，是**改陈述**，须冻结面审计 + 同时决定 `packIneqDefAP22 := True`(PA22:306)/`PackIneqDefA := True`(Assembly:279) 是否真化。② 若 `arcV↔arcLength` 桥超 450 行：先单独立「桥」微件波（不改任何陈述），再回 W3。③ 若编排者拒绝改 `_797` 陈述：`_ALT` 的 `v0` 分支只能走直接几何路线，但 0.797 常数下界本身仍要一条 ≥250 行的独立证明，等于换名字的同一工作量 |

---

## 尾 — fan/Conforming 阻塞对（BLOCKED，暂不排期）

| 件 | 阻塞证据 | 解锁条件 |
|---|---|---|
| `polyhedron_edge_sum` 12792 | HOL 5476 体消费 `BIJ_FACET_HYPERFACE`(12177 sorry)、`BIJ_DART_POLYEDGE`(12710 sorry)；`POLYHEDRON_TGJISOK`(12216) 虽 std3 但**空洞**——`hypermap1OfFanxP22` 的 `darts := ∅`（PA22:237），Euler 内容为零；真 `E ≤ 3F-6` 全树无 | fan/dart 机器（`hypermap1_of_fanx`、`vertices/edges`、`darts`）接线 + Euler 定理移植 |
| `POLYHEDRON_FACET_SUM_4Pi` 13951 | 34 行体消费 `POLYHEDRON_CONFORMING_FAN`(12185 sorry) + `POLYHEDRON_FAN`/`AMHFNXP_BIJ`/`SUM_SOL_IN_FACE_SET_EQ_4PI` 三件 ABSENT | Conforming lane（PA22:13944-13949 NEEDS 明写；ConformingAuto6:735 只是桥，不是本体） |

两者合计估 **500-900 行**，但真正成本在 fan 章；不建议由本波次承接。

---

## 2. 波次汇总与验收口径

| 波 | 件数 | own-sorry | 预估行数 | 阻塞 |
|---|---|---|---|---|
| 基线 live（EUSOTYP2 已闭） | — | 15 | — | — |
| W1 `GOTCJAH` | 1 | 15→14 | 200-350 | 无 |
| W2 `EXISTS_M_POLYHEDRON` | 1 | 14→13 | 350-500 | 无 |
| W3 Ysskqoy trio + `arclength` 真化 | 4（含 1 DEFHOLE） | 13→9 | 600-1150 | 需 PA18 银行 + `arcV` 桥 + 陈述修改裁决 |
| 尾 fan/Conforming | 2 | 9→7 | 500-900 | BLOCKED |
| 柱③ 全会话 | 8（6 句法 + 2 HOL 意图） | 15→7（最终） | 1650-2800 | 尾不落，柱③ 永带 `sorryAx` |

对 `fcdjdot` 本体的意义：
- W1+W2 落 ⇒ `existsM_polyhedron_sums` 只剩尾两条；`DLWCHEM_full` 仍带 2 债 → 本体可写但继承 `sorryAx`，不可交付。
- W1+W2+W3 落 ⇒ `DLWCHEM_full`/`XULJEPR_full` 仍各有 2 债（同一对尾件）→ 本体仍带 `sorryAx`。
- 只有“三波 + 尾”全落，`fcdjdot` 本体才可能 `std3`；本体本身 **150-300 行**，落
  `Assembly.lean`，并需先解 `Kepler.Text.sqrt3` 双胞胎（PA22:176 vs
  IneqClosureDefs:719）才能加 `import Kepler.Text.PackingAuto22`。
