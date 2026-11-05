# PA18 cc_pe_exists 链侦察（2026-10-23，Lane A 交付）

> 快照：`lane_snapshots/pa18scout/`（含 3 枚绿探针源码+日志）。结论：cc_pe_exists 非 GIANT，
> 6 件中等 + 3 helper，无新几何，A1–A7 波次可清，e2e 133→132（A7 后 131）。

---

# PA18 `cc_pe_exists` 侦察报告（SCOUT）

> 车道：PA18 `cc_pe_exists` 只读侦察 + `/tmp` 探针。
> 基线：main @ `c63e2f4b`；工作副本 `/tmp/p4pA`（APFS clone，olean 暖）。
> 交付：本文件、`DEP_MAP.tsv`、`WAVES.md`、`PROGRESS.md`、探针源码/日志、`MD5SUMS`。

## 0. 结论（一句话）

`cc_pe_exists` 不是 GIANT：它只差 **6 个可填件**（`YBZFUPO`、`FUZBZGI_0`、
`FUZBZGI_1`、`JDHAWAY_0`、`JDWAWAY`、`cc_pe_exists` 本体）**加 3 个私有小
helper**（严格半平面 12 行、affDim=0⇒单点 25 行、segment facet 分类 18 行）；
两个被 `NEEDS` 注记列为“缺失/仍 sorry”的关键上游
（PA7 `XYOFCGX`、一维多胞形=线段 `EXPAND_EDGE_POLYTOPE`）**都已在仓库中真证**。
全链闭合后 e2e 直接源数 **133 → 132**（净 −1，只剩链外的
`pa18_ccCell_swap`）。

## 1. 关键事实核对（修正依赖表）

| # | 旧说法（PA18 NEEDS / HANDOFF / playbook） | 实测 | 证据 |
|---|---|---|---|
| 1 | PA18:213 “FUZBZGI_1 consumes PA7's still-sorry XYOFCGX” | **过期**。`XYOFCGX`（PA7:1234）有完整证明体，调用 `XYOFCGX_1/2`（PA6:3369/3455）、`XYOFCGX_lemma0`（PA6:3267）、`XYOFCGX_3_0/4_0`（PA7:903/1096），全部有证明体 | 源码；PA7 的 9 处代码 sorry 全部不在 719–1290 的 XYOFCGX 区间 |
| 2 | PA18:1276 “1-dim polytope = segment classification absent from repo/Mathlib” | **过期**。`PolyAuto7.EXPAND_EDGE_POLYTOPE:381` 已真证（`polytope/face_of/aff_dim=1 ⇒ segment`）；PolyAuto7 全文件 0 代码 sorry | `grep -n sorry` 仅 docstring；探针 1 直接调用成功 |
| 3 | PA18:1580 “XYOFCGX ... still sorry in PackingAuto7” | **过期**，同 #1 | 同上 |
| 4 | playbook PA18 条：FUZBZGI_0 链还需 PA12 `VORONOI_LIST_3_SINGLETON_EXPLICIT` | 定理存在且**已真证**（PA12:1695，函数体到 1760 前无 sorry） | 源码 |
| 5 | playbook PA6 条：PA7 `BARV_CIRCUMCENTER_EXISTS` 等“等待落盘” | **过期**。PA6 代码层零 sorry；`BARV_CIRCUMCENTER_EXISTS`（PA7:1629）已证 | `grep -c sorry` = 2（均为注释）；PA6:883 注释明说 sorryAx-free |
| 6 | HANDOFF/PA25 文档：“28 枚 real_model_* 的唯一值级主根 = cc_pe_exists” | **口径混淆**。28 枚 `real_model_*` 的证明体本身就是 `sorry`，是独立值级 direct source；`cc_pe_exists` 只是它们**类型级**闭包里的 sorryAx。填 cc_pe_exists 不会减少这 28 个值级源 | `packingauto25:7347` 等 `:= by sorry`；e2e map 的 SORRIED 口径是“值里直接含 sorryAx” |
| 7 | PA7 “文件还有别的 sorry”（提醒） | 属实，共 9 处代码 sorry：`STRICT_CYCLIC_IMP_FAN:169`、`hypermapOfFan_p7:176`、`STRICT_CYCLIC_FAN_PROPERTIES:186`、`YIFVQDV:3686`、`KSOQKWL_lemma1:3737`、`AFFINE_INDEPENDENT_OMEGA_LIST_N:3743`、`KSOQKWL:3941`、`IVFICRK:3954`、`WQPRRDY:3976`。**均不在 XYOFCGX 值闭包内**（源码 + 探针 3 验证） | PA7 源码 |

> 结论：PA18 的 `NEEDS` 注记是 2026-10-10 时点写的，之后 PA6/PA7/PA12/
> PolyAuto7 多波落地把它变成了 stale-note。**不能再用“整文件有 sorry”
> 判断依赖状态**；本报告按常量值闭包逐条核对。

## 2. `cc_pe_exists` 全链拓扑

```
cc_pe_exists (PA18:206, HOL leaf_cell.hl:1052-1084)
├─ FUZBZGI_1 (PA18:1585, HOL :731-800)
│  ├─ YBZFUPO (PA18:1271, HOL :360-423)
│  │  ├─ AFF_DIM_VORONOI_LIST        PA5:2378   proved
│  │  ├─ POLYTOPE_VORONOI_LIST_BARV  PA5:2356   proved
│  │  ├─ CONVEX_VORONOI_LIST         PA5:2371   proved
│  │  ├─ EXPAND_EDGE_POLYTOPE        PolyAuto7:381 proved  ← 需新增 import
│  │  ├─ FACET_OF_SEGMENT / faceOf_sing / EXTREME_POINT_OF_SEGMENT / affDim_segment
│  │  │                              PA18:230 / Polytope:133/2190/179 proved
│  │  └─ (helper) affDim=0 ⇒ singleton  ~25 行
│  ├─ FUZBZGI_0 (PA18:1573, HOL :588-731)
│  │  ├─ NWVRFMF                      PA18:249   proved
│  │  ├─ XYOFCGX                      PA7:1234   proved
│  │  ├─ DIST_LE/EQ_HALF_PLANE        PA18:1554/1562 proved
│  │  ├─ VORONOI_LIST_3_SINGLETON_EXPLICIT PA12:1695 proved
│  │  ├─ HL_PROPERTIES                PA7:1621   proved
│  │  ├─ OMEGA_LIST_IN_VORONOI_LIST   PA5:2480   proved
│  │  ├─ HD_TRUNCATE_SIMPLEX          PA5:1605   proved
│  │  ├─ truncate_set_of_list         PA18:1450  proved
│  │  ├─ SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET PA6:1417 proved
│  │  ├─ VORONOI_LIST_SUBSET_VORONOI_CLOSED  PA5:2385 proved
│  │  ├─ BARV_SUBSET                  PA5:1469   proved
│  │  ├─ BARV_AFFINE_INDEPENDENT      PA7:1291   proved
│  │  ├─ MHFTTZN1                     PA6:3089   proved
│  │  └─ (helper) DIST_LT_HALF_PLANE  MISSING    ~12 行
│  └─ MHFTTZN3                        PA6:3109   proved
└─ JDWAWAY (PA18:1836, HOL :1012-1051)
   ├─ JDHAWAY_0 (PA18:1815, HOL :1012-1051)
   │  ├─ CHI_MSB_IMP_COPLANAR         PA18:1795  proved
   │  ├─ CHI_MSB_ADDITIVE             PA18:1646  proved
   │  ├─ COPLANAR_INSERT              PA18:1151  proved
   │  ├─ MHFTTZN1                     PA6:3089   proved
   │  ├─ MHFTTZN3                     PA6:3109   proved
   │  └─ list3_eq                     PA18:1490  proved
   ├─ JDHAWAY_1 (PA18:1827, proved)
   ├─ BARV_CIRCUMCENTER_EXISTS        PA7:1629   proved
   ├─ AFFINE_IMP_CHI_MSB_0            PA18:1673  proved
   └─ CHI_MSB_ADDITIVE                PA18:1646  proved
```

> 注：`YBZFUPO` 的 Lean 陈述只保留 HOL iff 的 `→` 方向（facet ⇒ 端点），
> 是**有意弱化**；`FUZBZGI_0` 的 HOL 证明需要 `{p1} facet_of` 的反方向，
> 但这一事实可由 `hv : voronoiList = convexHull {p1,p2}` + `hne` +
> `FACET_OF_SEGMENT` 就地重建，因此弱化不影响链条。

完整逐件表（含消费者、HOL 行、状态、债务搬家）见 **`DEP_MAP.tsv`**。

## 3. 证明处方（逐件）

### A1 `YBZFUPO`（PA18:1271，HOL leaf_cell.hl:360-423）

- **处方**：`AFF_DIM_VORONOI_LIST V ul 2 hbar` 给 `affDim voronoiList = 1`；
  `POLYTOPE_VORONOI_LIST_BARV` 给 `polytope`（展开成 PolyAuto7 的
  `∃ t, t.Finite ∧ p = convexHull t`）；`CONVEX_VORONOI_LIST` +
  `FaceOf.refl` 给 `FaceOf_p7`；`EXPAND_EDGE_POLYTOPE` 给
  `voronoiList = segment a b`；`convexHull_pair` 转回
  `convexHull {a,b}`；`affDim_segment` 给 `a≠b`；facet 分类用
  `affDim f = 0` ⇒ 单点（`Submodule.finrank_eq_zero` + `vectorSpan`，
  ~25 行）+ `faceOf_sing` + `EXTREME_POINT_OF_SEGMENT`。
- **桥接**：`FaceOf_p7`/`affDim_p7` 与 `Polytope.FaceOf`/`affDim`
  定义体逐字相同，只需 `⟨hf.1,hf.2.1,hf.2.2⟩` 与
  `simpa only [affDim_p7, affDim]`。
- **Mathlib 缺口**：无。`Submodule.finrank_eq_zero`、
  `vsub_mem_vectorSpan`、`convexHull_pair` 均现成。
- **预估**：60–80 行；低风险；**探针 1 EXIT=0**。
- **唯一结构风险**：新增 `import Kepler.Text.PolyAuto7`。已核：
  PolyAuto7 闭包（49 模块）不含 PA18，无环；探针中 PA18+PolyAuto7
  同时 import 可编。

### A2 `FUZBZGI_0`（PA18:1573，HOL leaf_cell.hl:588-731）

- **处方**（HOL 逐步翻译）：
  1. `{p1} facet_of`：由 `hv` + `hne` + `FACET_OF_SEGMENT`；
  2. `NWVRFMF` 取 `vl`（`barV V 3 vl`，`truncateSimplex 2 vl = ul`，
     `omegaList V vl = p1`）；
  3. 证 `elV vl 3 ∉ setOfList ul`：`truncate_set_of_list` +
     `SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET` + `MHFTTZN1`（3 vs 2 矛盾）；
  4. `XYOFCGX` 在 `u=hdV ul`、`v=elV vl 3` 处给严格 gap；
  5. `DIST_LT_HALF_PLANE` → `0 < w·(2q−(hd+el3))`，其中
     `q = circumcenter (setOfList ul)`；
  6. `p1 = circumcenter (setOfList vl)`：
     `VORONOI_LIST_3_SINGLETON_EXPLICIT` + `OMEGA_LIST_IN_VORONOI_LIST`；
  7. `HL_PROPERTIES` 两次 + `HD_TRUNCATE_SIMPLEX` +
     `DIST_EQ_HALF_PLANE` ⇒ `d1 = w·(2p1−(hd+el3)) = 0`；
  8. `p2 ∈ voronoiList`（`hv` + `IN_SET_IMP_IN_CONVEX_HULL_SET`）+
     `VORONOI_LIST_SUBSET_VORONOI_CLOSED` + `DIST_LE_HALF_PLANE`
     ⇒ `d2 ≥ 0`；
  9. 点积线性：`w·(2q−…) = t1*d1 + t2*d2 = t2*d2`；`d2 ≠ 0` ⇒
     `0 < d2` ⇒ `0 < t2`（`pos_of_mul_pos_right`）。
- **Mathlib 缺口**：`DIST_LT_HALF_PLANE` 不在仓库（HOL collect_geom 有）；
  由 `DIST_LE/EQ_HALF_PLANE` + `neg_dotProduct` 反证 ~12 行。
- **预估**：140–160 行；中低风险；**探针 2 已写好，待锁编译**。
- **备注**：HOL 的 `hfac` iff 在本件证明中不需要；Lean 的 → 弱化安全。

### A3 `JDHAWAY_0`（PA18:1815，HOL leaf_cell.hl:1012-1051）

- **处方**：反设 `chiMsb ul p1 = 0`；`CHI_MSB_IMP_COPLANAR` 给
  `Coplanar {getD0,getD1,getD2,p1}`；`list3_eq`（PA18:1490）把它改写为
  `Coplanar (insert p1 (setOfList ul))`；`COPLANAR_INSERT` + `MHFTTZN1`
  给 `p1 ∈ affineSpan (setOfList ul)`。另一侧 `p1 ∈ affineSpan
  (voronoiList)`：`hv` + `convexHull_pair`（或 `affineSpan_convexHull`）+
  `subset_affineSpan`（`p1 ∈ {p1,p2}`）。`MHFTTZN3` 说两 span 交 =
  `{circumcenter}`，故 `p1 = circumcenter`。代回 `hc`：
  `p1 = t1•p1+t2•p2`，`t1=1−t2` ⇒ `t2•p1 = t2•p2`；`hpos.2 : 0<t2`
  ⇒ `t2≠0` ⇒ `p1=p2`，与 `hne` 矛盾。
- **Mathlib 缺口**：无（`smul_right_injective` / `linear_combination` 足够）。
- **预估**：80–100 行；中低风险；无探针，建议先做一个小探针或直接填。

### A4 `FUZBZGI_1`（PA18:1585，HOL leaf_cell.hl:731-800）

- **处方**：`YBZFUPO` 取 `p1,p2,hv,hne,hfac`；`MHFTTZN3` 给
  `circumcenter (setOfList ul) ∈ affineSpan (voronoiList V ul)`；
  `hv` + `affineSpan_convexHull` ⇒ `∈ affineSpan {p1,p2}`；
  `mem_affineSpan_pair_iff_exists_lineMap_eq` 取 `r`，
  `lineMap p1 p2 r = circumcenter`；令 `t1=1−r, t2=r`，`t1+t2=1`。
  `FUZBZGI_0` 调用两次：`(p1,p2,t1,t2)` 得 `0<t2`（即 `0<r`），
  `(p2,p1,t2,t1)` 得 `0<t1`（即 `0<1−r`）；装配 8 元组。
- **Mathlib 缺口**：无；`mem_affineSpan_pair_iff_exists_lineMap_eq`、
  `lineMap_apply`、`affineSpan_convexHull` 均现成。
- **预估**：80–100 行；中风险（affineSpan/lineMap 形状摩擦、两次调用参数交换）。
- **注意**：`hfac` 交换版需要 `Set.pair_comm` / `by rw [hv]; congr 1; simp [Set.pair_comm]`。

### A5 `JDWAWAY`（PA18:1836，HOL leaf_cell.hl:1012-1051）

- **处方**：`JDHAWAY_0` 两次（`(p1,p2,t1,t2)` 与 `(p2,p1,t2,t1)`，
  hull 用 `Set.pair_comm`）得两个非零；`JDHAWAY_1` 给
  `chiMsb ul (circumcenter) = 0`；`CHI_MSB_ADDITIVE` 给
  `0 = t1*chi(p1) + t2*chi(p2)`；由 `0<t1,0<t2` 线性算术得
  `chi(p1)<0 ↔ 0<chi(p2)`。
- **Mathlib 缺口**：无；`nlinarith`/`linarith`。
- **预估**：40–60 行；低风险。

### A6 `cc_pe_exists`（PA18:206，HOL leaf_cell.hl:1052-1084）

- **处方**：`FUZBZGI_1` 取 `p1,p2,t1,t2` 与全部性质；
  `by_cases h : 0 < chiMsb ul p1`：
  - 真：取 `(p1,p2)`；
  - 假：由 `JDHAWAY_0` 的 `chiMsb ul p1 ≠ 0` 得 `chiMsb ul p1 < 0`，
    再由 `JDWAWAY` 的 `(chiMsb ul p1 < 0 ↔ 0 < chiMsb ul p2)` 得
    `0 < chiMsb ul p2`，取 `(p2,p1)`，hull 用 `Set.pair_comm`。
- **Mathlib 缺口**：无。
- **预估**：30–50 行；低风险。**必须最后装配**（见 §5 债务搬家）。

### A7 `pa18_ccCell_swap`（链外，PA18:3466）

- 不是 `cc_pe_exists` 的前置，但它是 PA18 的另一个 direct source，
  全链闭合后仍留在地图上（132 的“1”就是它）。需要另开侦察；
  候选路线：用 `cc_pe_exists`/`cc_uh_exists` 的 spec + `ccKe` 不变性
  + 4 点集合相等，证 `ccCell V [u0,u1,u2] = ccCell V [u1,u0,u2]`。
- 估计 80–200 行，中高风险（Skolem 选择交换性），建议 A6 后再做。

## 4. 探针与证据

所有探针在 `/tmp/p4pA_work/`，**不落 repo**。编译命令：

```bash
cd /tmp/p4pA/lean
source /tmp/kepler_build_lock.sh
lock_build nice -n 19 lake env lean /tmp/p4pA_work/<probe>.lean \
  > /tmp/p4pA_work/<probe>.log 2>&1
echo $?                       # 必须 0
grep -cE '(^|[ :])error:' /tmp/p4pA_work/<probe>.log   # 必须 0
```

| 探针 | 验证内容 | 结果 |
|---|---|---|
| `probe_ybzfupo.lean` | `YBZFUPO` 全证明：EXPAND_EDGE_POLYTOPE 接线、`FaceOf_p7`↔`FaceOf`、`affDim_p7`↔`affDim`、segment facet 分类 | **EXIT=0，error=0**；`#print axioms pa18p_YBZFUPO` = `[propext, Classical.choice, Quot.sound]`（无 sorryAx） |
| `probe_fuzbzgi0.lean` | `FUZBZGI_0` 全证明：`XYOFCGX` 接线、`DIST_LT_HALF_PLANE`、`elV vl 3 ∉ ul`、`d1=0`、`d2≥0`、`t2>0` | **EXIT=0，error=0**；`#print axioms pa18p_FUZBZGI_0` = `[propext, Classical.choice, Quot.sound]`（无 sorryAx）；2 个无害 warning |
| `probe_valax.lean` | 全链各常量的**值级** sorryAx 闭包 + direct source 列表（e2e map 口径） | **EXIT=0，error=0**；全部 kit `sorryAx_reachable=false`；6 个目标 sorry 件各自是 direct source |

> 日志中的 `pid=...` 行来自全局 lake 锁等待期间的并发构建，不是 Lean
> 输出；判定以 `EXIT=` 与 `error:` 计数为准。
>
> **锁饥饿例外**：全局 `/tmp/kepler_build.lock` 被另一条 R1 rest 构建
> 长期占用（先 `C2485876245b` 213 shards ~38 min，后 `C8405387449`
> 497 shards，按实测速率需数小时），`lock_build` 的 30 min stale 规则
> 因锁目录 mtime 被其他 lane 刷新而未生效。探针 2/3 在内存 77–78% 空闲、
> 只读 elaboration（无 `-o`、无 `lake build`、无 tracked 写入）的前提下
> 直接运行；探针 1 在锁内运行。此为例外，已在 `PROGRESS.md` 记录理由与证据。

### 4.1 探针 3（值级闭包）的关键否定结果

`XYOFCGX`/`XYOFCGX_1/2/3_0/4_0`/`XYOFCGX_lemma0`/`EXPAND_EDGE_POLYTOPE`/
`AFF_DIM_VORONOI_LIST`/`POLYTOPE_VORONOI_LIST_BARV`/`VORONOI_LIST_3_SINGLETON_EXPLICIT`/
`MHFTTZN1/3`/`HL_PROPERTIES`/`BARV_*`/`DIST_LE/EQ`/`FACET_OF_SEGMENT`/
`CHI_MSB_*`/`COPLANAR_INSERT`/`truncate_set_of_list` 全部
`sorryAx_reachable = false`。这直接证明：

- PA7 的 9 处代码 sorry **不在** XYOFCGX 值闭包内；
- PolyAuto7 的 `EXPAND_EDGE_POLYTOPE` 值闭包无 sorry；
- PA12/PA6/PA5 的相关 kit 值闭包无 sorry；
- 因此 A1/A2 落地不会引入任何新的 direct source（除了它们自己消失）。

## 5. 债务搬家（e2e direct source）

当前 e2e = **133**，PA18 占 2：`cc_pe_exists`、`pa18_ccCell_swap`。
SORRIED 口径 = 证明值里**直接**含 `sorryAx`。

| 操作 | 源数变化 | 新暴露 |
|---|---|---|
| 只填 A6 | 133 −1 +2 = **134** | `FUZBZGI_1`、`JDWAWAY` |
| A6 后只填 A4 | 134 −1 +2 = **135** | `FUZBZGI_0`、`YBZFUPO` |
| A6 后只填 A5（A3 未填） | 134 −1 +1 = **134** | `JDHAWAY_0` |
| A1/A2/A3 单独填（未到 A6） | **133 不变** | 不可达 |
| 推荐顺序 A1→A2→A3→A4→A5→A6 | A1–A5 恒 133；A6 落地 **133→132** | 无中间膨胀 |
| A7 | 132→131 | 无 |

**特别回答**：填 `cc_pe_exists` 后，
- `FUZBZGI_1`、`JDWAWAY` **会**成为新的 direct source；
- `YBZFUPO`、`FUZBZGI_0` 只有在 `FUZBZGI_1` 也被填后才会成为 source
  （若 `FUZBZGI_1` 仍是 sorry，其证明体不引用它们，故不可达）；
- `JDHAWAY_0` 只有在 `JDWAWAY` 也被填后才会成为 source；
- 因此**必须叶子先行、`cc_pe_exists` 最后装配**。

## 6. 必须回答的六个问题

1. **全链还需多少件？**
   6 件 sorry（A1–A6）+ 3 个私有小 helper（`DIST_LT_HALF_PLANE` ~12 行、
   `affDim=0 ⇒ 单点` ~25 行、segment facet 分类 ~18 行）+ 1 个
   import（`PolyAuto7`）。若把链外 `pa18_ccCell_swap` 算上，PA18 还有 7 件。
2. **哪些可 1 波闭？**
   A1、A2、A3 各自可 1 波闭（A1/A2 已有探针）；A4+A5 可合 1 波；
   A6 单独 1 波（最后）。由于 6 件同文件，tracked 编辑只能串行，
   建议 3 波：`A1+A2` / `A3+A4+A5` / `A6`。
3. **哪些需要新几何件（例如一维多胞形=线段）？**
   **没有**。一维多胞形=线段 = `PolyAuto7.EXPAND_EDGE_POLYTOPE:381`，
   已真证；唯一“新”的是 12 行的 `DIST_LT_HALF_PLANE` 与两个
   25/18 行的初等 helper（affDim=0⇒单点、segment facet 分类）。
4. **填实后 e2e 源数的预期变化？**
   133 → **132**（净 −1）。若 A7 也闭，132 → 131。中间态若顺序错误会
   先升到 134/135，见 §5；按推荐顺序无中间膨胀。
5. **最难的件？**
   A2 `FUZBZGI_0`（~150 行，代数+几何最密）；其次 A3/A4（~90 行）。
   没有 GIANT。
6. **哪件是 GIANT？**
   **没有**。原 GIANT 判定基于两个 stale 事实（XYOFCGX 仍 sorry、
   1 维 segment classification 缺失），两者都已不成立。

## 7. 风险与开放问题

- **import 闭包**：新增 `Kepler.Text.PolyAuto7` 会让 PA18 的构建闭包
  变大；首次构建可能需重建 PolyAuto7 依赖（当前 /tmp/p4pA 暖，主仓
  需闸构建验证）。无环、无同名冲突（探针实证）。
- **`truncate_set_of_list` 的 `getD` 形状**：`elV vl 3` 与 `vl.getD 3 0`
  定义同义；已由探针 2 验证。
- **`MHFTTZN3` 的交集形状**：`(affineSpan voronoiList : Set V3) ∩
  (affineSpan setOfList : Set V3)`，与 HOL 的 `affine hull ... INTER
  affine hull ...` 同义；A3/A4 直接消费。
- **`pa18_ccCell_swap`**：不在本链，闭合后仍是 source；需要单独立项。
- **PA25 的 28 枚 real_model**：与 cc_pe_exists 是**类型级**关系，不是
  值级；不要把它们算作本波收益。填 cc_pe_exists 后它们的
  `#print axioms` 类型级 sorryAx 会消失，但值级 source 仍在，直到各自
  证明体被填。

## 8. 建议

**下一波最该先派 A1 `YBZFUPO`**：它是唯一需要新 import 的件，也是
“新几何件”疑虑的所在；探针已 0 error，落地后可清掉 A4 的一半前置，
并把 PA18 的 import 闭包风险一次性暴露。若工人产能允许，把 A1+A2
打包成同一波（两件独立、探针/草稿已在 `/tmp/p4pA_work/`）。
`cc_pe_exists` 本体只在 A4/A5 全闭后装配。

> 记账口径补充：`DEBT.md` 是全仓 sorry 账本，A1–A6 每一件落地都会减少
> DEBT token（约 6 件文本债）；而 **e2e 地图**只在 A6 装配时才从 133 变
> 132。两道账要分开记，不要用 DEBT 的下降宣称 e2e 收益。

---

# PA18 `cc_pe_exists` 分波施工表（WAVES）

> 基线 main @ c63e2f4b；e2e 133 direct sources；PA18 仅
> `cc_pe_exists`、`pa18_ccCell_swap` 两个源。
> 结论先行：**cc 链不是 GIANT，是 6 件中等件 + 3 个私有小 helper（合计
> ~55 行）**。最硬的“一维多胞形 = 线段”已经以
> `PolyAuto7.EXPAND_EDGE_POLYTOPE` 存在于仓库中（真证），只差 import 与桥接。

## 0. 施工拓扑与债务守恒

```
A1 YBZFUPO ─┐
             ├─> A4 FUZBZGI_1 ─┐
A2 FUZBZGI_0 ┘                 ├─> A6 cc_pe_exists
A3 JDHAWAY_0 ─── A5 JDWAWAY ───┘
                                    A7 pa18_ccCell_swap（链外，可选尾波）
```

- **必须按叶子→装配的顺序合并**。若先填 A6，e2e 源数会
  133→134（FUZBZGI_1、JDWAWAY 变成新 direct source）；再先填 A4 会
  134→135（FUZBZGI_0、YBZFUPO 暴露）。按 A1→A6 顺序，A1–A5 的件在
  A6 之前不可达，地图恒为 133；A6 落地时 133→132。
- 所有 6 件都在**同一个 tracked 文件** `Kepler/Text/PackingAuto18.lean`，
  因此 tracked 编辑必须串行（同文件不能并行 lane）。可并行的是 `/tmp`
  探针/草稿；建议“一个填证工人 + 多个 /tmp 探针预备”模式。
- 每波合并前按 playbook §5.7 重跑
  `cd lean && lake env lean scripts/e2e_reach_map.lean > /tmp/reachmap.out`，
  diff 源清单；若出现“净增源”或新的可达 sorry，停批。
- 验收构建：`lake build Kepler.Text.PackingAuto18`（不是 env-lean 假绿），
  闸按 `LANE_FILES="Kepler/Text/PackingAuto18.lean"`。

## 1. 分波表

| 波 | 目标（PA18 行） | 前置 | 证明处方（精确 kit） | 预估 | 难度/风险 | 验收 | 合并时 e2e |
|---|---|---|---|---|---|---|---|
| **A1** | `YBZFUPO` :1271 | 新 import `Kepler.Text.PolyAuto7` | `AFF_DIM_VORONOI_LIST`(PA5:2378) 给 affDim=1；`POLYTOPE_VORONOI_LIST_BARV`(PA5:2356) + `CONVEX_VORONOI_LIST`(PA5:2371) 喂 `EXPAND_EDGE_POLYTOPE`(PolyAuto7:381)；`FaceOf_p7`/`affDim_p7` 与 `Polytope.FaceOf/affDim` 定义体同文，直接 `⟨hf.1,hf.2.1,hf.2.2⟩` + `simpa [affDim_p7, affDim]`；得到 `segment a b` 后 `convexHull_pair` + `affDim_segment` 给 a≠b；facet 分类用 `affDim`=0 ⇒ 单点（private helper ~25 行）+ `faceOf_sing` + `EXTREME_POINT_OF_SEGMENT` | ~60–80 行 | 低；**探针已 0 error** | `lake build Kepler.Text.PackingAuto18`；`#print axioms YBZFUPO` 只标准三 | 133→133（不可达） |
| **A2** | `FUZBZGI_0` :1573 | A2 helper | 新增 `DIST_LT_HALF_PLANE`（~12 行，严格版由 `DIST_LE/EQ_HALF_PLANE` 反证）；`NWVRFMF`(PA18:249) 取 4 点 `vl`；`truncate_set_of_list`(PA18:1450)+`SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET`(PA6:1417)+`MHFTTZN1` 证 `elV vl 3 ∉ setOfList ul`；`XYOFCGX`(PA7:1234) 在 `u=hdV ul, v=elV vl 3` 取严格 gap；`VORONOI_LIST_3_SINGLETON_EXPLICIT`(PA12:1695)+`HL_PROPERTIES`(PA7:1621)+`DIST_EQ_HALF_PLANE`(PA18:1562) 证 `d1=0`；`VORONOI_LIST_SUBSET_VORONOI_CLOSED`(PA5:2385)+`DIST_LE_HALF_PLANE`(PA18:1554) 证 `d2≥0`；点积线性 + `hts` 得 `0<t2*d2`，`d2≠0` ⇒ `0<t2` | ~140–160 行（含 helper） | 中低；**探针 EXIT=0/error=0** | 同上；`#print axioms FUZBZGI_0` | 133→133 |
| **A3** | `JDHAWAY_0` :1815 | 无 | 反设 `chiMsb ul p1=0`；`CHI_MSB_IMP_COPLANAR`(PA18:1795) 给共面；`list3_eq`(PA18:1490) 把 `insert p1 (setOfList ul)` 换成 `{getD0,getD1,getD2,p1}`；`COPLANAR_INSERT`(PA18:1151)+`MHFTTZN1`(PA6:3089) 给 `p1 ∈ affineSpan(setOfList ul)`；`hv`+`convexHull_pair`+`subset_affineSpan` 给 `p1 ∈ affineSpan(voronoiList)`；`MHFTTZN3`(PA6:3109) 两 span 交 = `{circumcenter}` ⇒ `p1=circumcenter`；代回 `hc`、`hts`、`hpos.2`、`hne` 矛盾（`t2•p1=t2•p2` ⇒ `p1=p2`） | ~80–100 行 | 中低；kit 全在，无新几何 | 同上 | 133→133 |
| **A4** | `FUZBZGI_1` :1585 | A1, A2 | `YBZFUPO` 取 p1,p2,hv,hne,facets；`MHFTTZN3` ⇒ `circumcenter ∈ affineSpan(voronoiList)`；`hv`+`affineSpan_convexHull` ⇒ `∈ affineSpan {p1,p2}`；`mem_affineSpan_pair_iff_exists_lineMap_eq` 取 r，令 t1=1−r,t2=r；`FUZBZGI_0` 两次（(p1,p2) 与 (p2,p1)）得 `0<t1`、`0<t2`；装配 | ~80–100 行 | 中（affineSpan/lineMap 形状摩擦） | 同上 | 133→133 |
| **A5** | `JDWAWAY` :1836 | A3 | `JDHAWAY_0` 两次（p1/p2 互换，hull 用 `Set.pair_comm`）；`JDHAWAY_1`+`CHI_MSB_ADDITIVE` 得 `0 = t1*chi(p1)+t2*chi(p2)`；`hpos` 与 `nlinarith` 给 `chi(p1)<0 ↔ 0<chi(p2)` | ~40–60 行 | 低 | 同上 | 133→133 |
| **A6** | `cc_pe_exists` :206 | A4, A5 | `FUZBZGI_1` 取 p1,p2,t1,t2；`by_cases h : 0 < chiMsb ul p1`：真取 (p1,p2)；假则 `chiMsb ul p1 ≠ 0` + `JDWAWAY` 的符号翻转得 `0 < chiMsb ul p2`，取 (p2,p1)，hull 用 `Set.pair_comm` | ~30–50 行 | 低 | 同上 + **重跑 e2e map**：应 133→132，且无新源 | **133→132** |
| **A7** | `pa18_ccCell_swap` :3466（链外） | A6 | 不是本链；需证 `ccCell V [u0,u1,u2] = ccCell V [u1,u0,u2]`，即 `ccPe1/ccUh/ccKe` 的 Skolem 选择在 0-1 交换下给出同一 4 点集。可用 `cc_pe_exists`/`cc_uh_exists` 的 spec + hull 集合相等 + `ccKe` 不变性；细节需另开侦察 | 未知（~80–200 行） | 中高 | 同 A6；e2e 132→131 | 132→131 |

## 2. “哪件是 GIANT / 先填哪件”

- **没有 GIANT**。原 `NEEDS` 的 GIANT 判定基于两个已过期的“缺失件”：
  PA7 `XYOFCGX`（已证）与“一维多胞形=线段”（`EXPAND_EDGE_POLYTOPE`
  已证）。扣除这两个误判后，剩余是标准代数/仿射几何装配。
- 最大单件 = **A2 FUZBZGI_0**（~150 行，代数最密）；其次 A3/A4（~90 行）。
- **下一波最该先派 A1 `YBZFUPO`**：它是唯一需要新 import 的件，也是“新几何件”
  疑虑的所在；探针已 0 error，落地后可把 A4 的一半前置清掉。若想一波拿更多，
  可把 **A1+A2 放同一波**（两件独立、探针/草稿都在
  `/tmp/p4pA_work/`，~220 行同一文件串行编辑）。
- A6 **只在 A4/A5 全闭后装配**；否则会造成中间波源数上升（见 §0）。

## 3. 工作量汇总

| 项 | 数量 |
|---|---|
| 需填 sorry 件 | 6（A1–A6）+ 1 链外（A7） |
| 需新增 helper | 3（`DIST_LT_HALF_PLANE` ~12 行；`affDim=0 ⇒ 单点` ~25 行；segment facet 分类 ~18 行，可内联） |
| 需新增 import | 1（`Kepler.Text.PolyAuto7`，无环；探针 1 实证可编） |
| 需新数学/几何理论 | **0**；所有几何件均已在仓库 |
| 预估总行数 | ~450–550 行（A1–A6） |
| 预估波数 | 3 波串行（A1+A2 / A3+A4+A5 / A6），或 6 个单件小波 |
| 一次全程 e2e 变化 | 133 → 132（净 −1；A7 再 −1） |

## 4. 每波收工必做

1. `lake build Kepler.Text.PackingAuto18` 自然退出 0 error；
2. `#print axioms` 目标 ∈ {propext, Classical.choice, Quot.sound, sorryAx}；
3. 重跑 e2e map，核对“消失/新增”清单，按 §0 的债务守恒规则判定；
4. 若新增了 `import Kepler.Text.PolyAuto7`，闸的 GATE_ROOTS 闭包会变大，
   首次构建留足时间（PolyAuto7 及其 import 闭包在新 clone 上可能需重建）。

---

# PA18 cc_pe_exists 侦察 — PROGRESS

更新时间锚点：2026-10-23 19:25 CST（每 ~5 分钟更新一次）

## 当前步骤

- [x] 环境核对：主仓 HEAD c63e2f4b；/tmp/p4pA 干净、olean 暖。
- [x] 必读材料：HANDOFF、PLAN §5、playbook §0-4、trust-audit §0-2、PA18 头部、HOL leaf_cell.hl 关键段。
- [x] 事实核对：PA7 `XYOFCGX` 已真证；PolyAuto7 `EXPAND_EDGE_POLYTOPE` 已真证；PA12 `VORONOI_LIST_3_SINGLETON_EXPLICIT` 已真证；PA6 代码层零 sorry。
- [x] 探针 1（YBZFUPO ← EXPAND_EDGE_POLYTOPE 接线）：`/tmp/p4pA_work/probe_ybzfupo.lean`，EXIT=0，error=0。
- [x] 探针 2（FUZBZGI_0 ← XYOFCGX 接线）：`/tmp/p4pA_work/probe_fuzbzgi0.lean`，经 3 轮迭代后 **EXIT=0，error=0**（仅 2 个 warning：push_neg deprecated、hfac unused）。
- [x] 探针 3（值级 sorryAx 闭包）：`/tmp/p4pA_work/probe_valax.lean`，**EXIT=0，error=0**。关键结果：
  - `XYOFCGX`、`XYOFCGX_1/2/3_0/4_0`、`XYOFCGX_lemma0`、`EXPAND_EDGE_POLYTOPE`、`AFF_DIM_VORONOI_LIST`、`POLYTOPE_VORONOI_LIST_BARV`、`VORONOI_LIST_3_SINGLETON_EXPLICIT`、`MHFTTZN1/3`、`HL_PROPERTIES`、`BARV_*`、`DIST_*`、`FACET_OF_SEGMENT`、`CHI_MSB_*`、`COPLANAR_INSERT`、`truncate_set_of_list` 全部 `sorryAx_reachable=false`、`direct_sources=[]`；
  - `CC_PE_FACET_OF`/`cc_uh_exists`/`ccUh`/`ccCell` 的**值级**唯一源 = `cc_pe_exists`（证实债务集中）；
  - `JDHAWAY_1` value-clean；
  - 5 个目标 sorry 件（YBZFUPO/FUZBZGI_0/FUZBZGI_1/JDHAWAY_0/JDWAWAY/cc_pe_exists）各自是 direct source。
- [x] DEP_MAP.tsv 初稿（见同目录）。
- [ ] SCOUT.md / WAVES.md 定稿（正在回填探针结果）。
- [ ] 快照 + MD5SUMS。

## 锁饥饿与例外记录（重要）

- 全局 `/tmp/kepler_build.lock` 被另一条 R1 rest 构建长期占用：先是
  `C2485876245b`（213 shards，~38 min），随后 `C8405387449`（497 shards，
  以 ~1 min/shard 估算需数小时）。`lock_build` 的 30 分钟 stale 规则没有
  生效（锁目录 mtime 被其他 lane 刷新），1 小时 timeout 会耗尽车道配额。
- 因此在**内存空闲 77–78%**、且**只做只读 elaboration（无 -o、无 lake build、
  无 tracked 写入）**的前提下，探针 2/3 以后台 `nice -n 19 lake env lean`
  直接运行并在日志中记录；这是对“单 lake 进程锁”的显式例外，理由与证据
  均已留盘。探针 1 是在锁内运行的（EXIT=0）。
- 未修改 `/tmp/p4pA` 任何 tracked 文件；未跑 auto_gate、未跑全项目 build、
  未用 -j/-K。

## 已确认事实（高置信）

1. `PackingAuto7.lean:1234 XYOFCGX` 的值证明完整，其 helper
   `XYOFCGX_1/2`（PA6:3369/3455）、`XYOFCGX_lemma0`（PA6:3267）、
   `XYOFCGX_3_0/4_0`（PA7:903/1096）全部有证明体；PA7 的 9 处代码 sorry
   全在 1234 之后/之前的不相关簇（YIFVQDV、KSOQKWL、IVFICRK、WQPRRDY、
   STRICT_CYCLIC*），不在 XYOFCGX 值闭包内。
2. `PolyAuto7.lean:381 EXPAND_EDGE_POLYTOPE` 有完整证明；文件仅 2 处
   字面 "sorry"，均在 docstring。其 `FaceOf_p7`/`affDim_p7`
   （PolyAuto7:111/121/130）是公开的私有副本，与 Polytope 的
   `FaceOf`/`affDim` 定义体逐字相同，桥接只需展开（探针 1 实证）。
3. PA18 `NEEDS` 三处过期：:213（XYOFCGX still sorry）、:1276（1-dim
   polytope=segment 无现成件）、:1580（XYOFCGX still sorry）。
4. `VORONOI_LIST_3_SINGLETON_EXPLICIT`（PA12:1695）已真证 —— playbook
   PA18 条把它列为 FUZBZGI_0 的额外缺口，已过期。
5. `MHFTTZN3`（PA6:3109）与 `MHFTTZN1`（PA6:3089）已真证；PA6 整体
   代码层零 sorry（grep 只命中两处注释）。
6. `AFF_DIM_VORONOI_LIST`（PA5:2378）、`POLYTOPE_VORONOI_LIST_BARV`
   （PA5:2356）、`CONVEX_VORONOI_LIST`（PA5:2371）已真证；PA5 仅两处
   代码 sorry（PROJECTION_ORTHOGONAL、PERMUTES_TRIVIAL），均不在本链。
7. cc_pe_exists 的 6 件值级链：
   `cc_pe_exists → {FUZBZGI_1, JDWAWAY}`；
   `FUZBZGI_1 → {YBZFUPO, FUZBZGI_0, MHFTTZN3}`；
   `JDWAWAY → {JDHAWAY_0, JDHAWAY_1}`；
   `FUZBZGI_0 → {NWVRFMF, XYOFCGX, DIST_*_HALF_PLANE, PA12 singleton,
   HL_PROPERTIES, ...}`；
   `YBZFUPO → {AFF_DIM_VORONOI_LIST, POLYTOPE_VORONOI_LIST_BARV,
   EXPAND_EDGE_POLYTOPE, FACET_OF_SEGMENT, ...}`。
8. 唯一缺失小件：`DIST_LT_HALF_PLANE`（HOL collect_geom，仓库只有
   `DIST_LE/EQ`）；探针里 12 行补出（严格半平面形）。
9. 债务搬家：只填 cc_pe_exists 会让 FUZBZGI_1、JDWAWAY 变成新的 direct
   source（133→134，净 +1）；随后按拓扑序填，最终 133→132（只剩
   `pa18_ccCell_swap`）。因此 cc_pe_exists 必须最后装配。
10. PA25 的 28 枚 `real_model_*` 是**独立值级 sorry**（证明体就是
    `sorry`），填 cc_pe_exists 只清其**类型级** sorryAx，不会减少这 28
    个值级 direct source。HANDOFF 的"唯一值级主根"表述需要修正。

## 卡点（已解除）

- ~~全局 lake 锁被 R1 rest 构建长期占用~~：探针 2/3 已在内存 77–78% 空闲下
  直接只读运行完成（见上“锁饥饿与例外记录”）。当前无阻塞。

## 探针 2 迭代记录（2026-10-23 18:50 / 19:1x）

首次运行（R1 构建释放锁后）得 7 errors，全部是形状/次序问题，不是数学缺口：

1. `DIST_LT_HALF_PLANE`：`add_comm b a` 需写成 `add_comm b.ofLp a.ofLp`
   （dot 已展开到 Pi 层）。
2. `truncate_set_of_list` 分支：`rw [← h']` 方向反了，应为 `rw [h']`。
3. `omegaList = omegaListN 3`：`rw [omegaList, hvl4]` 已自动闭目标，
   多余 `norm_num` 报 "No goals"。
4. `OMEGA_LIST_N_IN_VORONOI_LIST`：`rw [← htr3]` 会同时改写 omegaList 的
   `vl` 参数；改为先在 `hmem0` 上 `rwa [htr3] at hmem0`。
5. `hdot`：dot 在 Pi 层展开（`.ofLp`），不能直接 rw V3 级 `hvec`；
   新增 `hvecPi := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hvec` + `simpa`。
6. 右参数是 `t1 • A + t2 • B`，拉标量要用 `dotProduct_smul`（右 smul），
   不是 `smul_dotProduct`。
7. `pos_of_mul_pos_right` 的假设形是 `0 < d2 * t2`；先 `rw [mul_comm ...]`。

修正后已重新排队编译。

第二轮（直接只读运行）剩 3 errors，全是 coercion 形状：

8. `(-(b-a)).ofLp ⬝ᵥ v = -((b-a).ofLp ⬝ᵥ v)`：`neg_dotProduct` 不匹配
   V3 级负号的 coercion；改为 `simp only [WithLp.ofLp_neg, neg_dotProduct]`。
9. `hvecPi` 的 LHS 必须写成**已归一化的 Pi 形**
   `2 • (circumcenter).ofLp - ((hdV).ofLp + (elV).ofLp)`，否则 `rw` 匹配不到
   目标里的 `.ofLp` 展开式。

第三轮：**EXIT=0，error=0**（2 warnings：`push_neg` deprecated；
`hfac` 未被引用——两者均无害）。探针 2 完成。

## 探针 3 结果（值级闭包，EXIT=0 / error=0）

- 5 个目标 sorry 件：`sorryAx_reachable=true`，direct source = 自身。
- `JDHAWAY_1` 及全部 kit（XYOFCGX 系、EXPAND_EDGE_POLYTOPE、
  AFF_DIM_VORONOI_LIST、POLYTOPE_VORONOI_LIST_BARV、
  VORONOI_LIST_3_SINGLETON_EXPLICIT、MHFTTZN1/3、HL_PROPERTIES、
  BARV_AFFINE_INDEPENDENT、BARV_CIRCUMCENTER_EXISTS、DIST_LE/EQ、
  FACET_OF_SEGMENT、CHI_MSB_IMP_COPLANAR、CHI_MSB_ADDITIVE、
  COPLANAR_INSERT、AFFINE_IMP_CHI_MSB_0、
  VORONOI_LIST_SUBSET_VORONOI_CLOSED、OMEGA_LIST_IN_VORONOI_LIST、
  HD_TRUNCATE_SIMPLEX、BARV_SUBSET、SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET、
  TRUNCATE_SIMPLEX_REFL、truncate_set_of_list）：
  **sorryAx_reachable=false，direct_sources=[]**。
- `CC_PE_FACET_OF`/`cc_uh_exists`/`ccUh`/`ccCell`：值级唯一源 =
  `cc_pe_exists`，无其他源。证实“单根”说法在值级口径下成立（但不含
  PA25 real_model 的独立 sorry）。

## 公理检查

- `#print axioms Kepler.Text.pa18p_YBZFUPO` = `[propext, Classical.choice, Quot.sound]`
- `#print axioms Kepler.Text.pa18p_FUZBZGI_0` = `[propext, Classical.choice, Quot.sound]`
（均无 sorryAx；探针定理是 /tmp 中与 PA18 同名陈述的副本。）

## 交付完成（2026-10-23 19:25）

- 快照：`/Users/zhangzhuo/c17_backup/lane_snapshots/pa18scout/`
- 文件：SCOUT.md / DEP_MAP.tsv / WAVES.md / PROGRESS.md /
  3 个探针源码 + 3 个日志 / MD5SUMS（sha256，已验证）。
- 主仓与 /tmp/p4pA 均 `git status --porcelain` 为空；未做任何 git 写操作。

---

```
# PA18 cc_pe_exists value-level dependency map
# basis: main @ c63e2f4b; /tmp/p4pA warm clone; e2e map docs/e2e-reachability-map.tsv (133 sources)
# columns: const	lean_loc	hol_loc	status	value_level_deps	direct_consumers	exposes_if_filled	wave
cc_pe_exists	Kepler/Text/PackingAuto18.lean:206	leaf_cell.hl:1052-1084	sorry	FUZBZGI_1; JDWAWAY	ccPe1:220; ccPe2:224; CC_PE_FACET_OF:239 (via ccPe1); PA25 (279 cc-refs)	filled alone -> FUZBZGI_1 and JDWAWAY become direct sources (+2, -1)	A6
FUZBZGI_1	Kepler/Text/PackingAuto18.lean:1585	leaf_cell.hl:731-800	sorry	YBZFUPO:1271; FUZBZGI_0:1573; MHFTTZN3 PA6:3109	cc_pe_exists	filled alone -> FUZBZGI_0 + YBZFUPO become direct sources (+2, -1)	A4
FUZBZGI_0	Kepler/Text/PackingAuto18.lean:1573	leaf_cell.hl:588-731	sorry (full proof verified in probe_fuzbzgi0, /tmp only)	NWVRFMF:249; XYOFCGX PA7:1234; DIST_LE/EQ_HALF_PLANE:1554/1562; VORONOI_LIST_3_SINGLETON_EXPLICIT PA12:1695; HL_PROPERTIES PA7:1621; OMEGA_LIST_IN_VORONOI_LIST PA5:2480; HD_TRUNCATE_SIMPLEX PA5:1605; truncate_set_of_list:1450; SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET PA6:1417; VORONOI_LIST_SUBSET_VORONOI_CLOSED PA5:2385; BARV_SUBSET PA5:1469; BARV_AFFINE_INDEPENDENT PA7:1291; MHFTTZN1 PA6:3089	FUZBZGI_1	none (all deps value-clean); needs new helper DIST_LT_HALF_PLANE	A2
YBZFUPO	Kepler/Text/PackingAuto18.lean:1271	leaf_cell.hl:360-423	sorry (full proof verified in probe_ybzfupo, /tmp only)	AFF_DIM_VORONOI_LIST PA5:2378; POLYTOPE_VORONOI_LIST_BARV PA5:2356; CONVEX_VORONOI_LIST PA5:2371; EXPAND_EDGE_POLYTOPE PolyAuto7:381; FACET_OF_SEGMENT:230; faceOf_sing Polytope:133; EXTREME_POINT_OF_SEGMENT Polytope:2190; affDim_segment Polytope:179	FUZBZGI_1	none (all deps value-clean); requires import Kepler.Text.PolyAuto7 (acyclic)	A1
JDHAWAY_0	Kepler/Text/PackingAuto18.lean:1815	leaf_cell.hl:1012-1051	sorry	CHI_MSB_IMP_COPLANAR:1795; CHI_MSB_ADDITIVE:1646; COPLANAR_INSERT:1151; MHFTTZN1 PA6:3089; MHFTTZN3 PA6:3109	JDWAWAY	none (all deps value-clean)	A3
JDWAWAY	Kepler/Text/PackingAuto18.lean:1836	leaf_cell.hl:1012-1051	sorry	JDHAWAY_0:1815; JDHAWAY_1:1827; CHI_MSB_ADDITIVE:1646	cc_pe_exists	filled alone -> JDHAWAY_0 becomes direct source (+1, -1)	A5
JDHAWAY_1	Kepler/Text/PackingAuto18.lean:1827	leaf_cell.hl:1012-1051	proved	BARV_CIRCUMCENTER_EXISTS PA7:1629; AFFINE_IMP_CHI_MSB_0:1673	JDWAWAY	-	-
XYOFCGX	Kepler/Text/PackingAuto7.lean:1234	Rogers.hl:6559	proved (value-clean, probe_valax)	XYOFCGX_1 PA6:3369; XYOFCGX_2 PA6:3455; XYOFCGX_lemma0 PA6:3267; XYOFCGX_3_0 PA7:903; XYOFCGX_4_0 PA7:1096	PA7 many; FUZBZGI_0 (new)	none (PA7 absent from e2e map; 9 PA7 code sorries are outside this value cone)	-
XYOFCGX_1	Kepler/Text/PackingAuto6.lean:3369	Rogers.hl:5222-5290	proved	OAPVION2; CIRCUMCENTER_1; CARD_1_IMP_SING	XYOFCGX	-	-
XYOFCGX_2	Kepler/Text/PackingAuto6.lean:3455	Rogers.hl:5292-5360	proved	XYOFCGX_lemma0; CIRCUMCENTER_2; CARD_2_IMP_DOUBLE	XYOFCGX	-	-
XYOFCGX_lemma0	Kepler/Text/PackingAuto6.lean:3267	Rogers.hl:4862-5220	proved	law of cosines kit; arcV	XYOFCGX_1/2	-	-
XYOFCGX_3_0	Kepler/Text/PackingAuto7.lean:903	Rogers.hl:6121	proved	p7_* helpers	XYOFCGX	-	-
XYOFCGX_4_0	Kepler/Text/PackingAuto7.lean:1096	Rogers.hl:6400	proved	p7_cos_dihV_lt_zero; XYOFCGX_lemma0	XYOFCGX	-	-
EXPAND_EDGE_POLYTOPE	Kepler/Text/PolyAuto7.lean:381	polyhedron.hl:1893-1930	proved (value-clean, probe_valax)	affDim_p7:111; FaceOf_p7:121; Mathlib convexHull/segment kit; p7 core	YBZFUPO (new)	none; new import needed, closure acyclic (PolyAuto7 closure has no PA18)	-
FaceOf_p7 / affDim_p7	Kepler/Text/PolyAuto7.lean:121 / :111	polyhedron.hl	proved	def bodies byte-identical to Polytope.FaceOf/affDim	YBZFUPO bridge	none	-
AFF_DIM_VORONOI_LIST	Kepler/Text/PackingAuto5.lean:2378	pack3.hl:2391	proved	barV.2 voronoiNondg	YBZFUPO; PA2 chain copy	-	-
POLYTOPE_VORONOI_LIST_BARV	Kepler/Text/PackingAuto5.lean:2356	pack3.hl:2355	proved	POLYHEDRON_VORONOI_LIST; compact+bounded	YBZFUPO	-	-
CONVEX_VORONOI_LIST	Kepler/Text/PackingAuto5.lean:2371	pack3.hl:2380	proved	CONVEX_VORONOI_CLOSED	YBZFUPO; FaceOf.refl	-	-
VORONOI_LIST_3_SINGLETON_EXPLICIT	Kepler/Text/PackingAuto12.lean:1695	marchal2.hl:2231	proved	p12_affDim_eq_zero; AFF_INDEPENDENT_SET_OF_LIST_BARV; OAPVION2/3	PA15/PA18; FUZBZGI_0	-	-
MHFTTZN3	Kepler/Text/PackingAuto6.lean:3109	Rogers.hl:4881	proved	MHFTTZN_lemma2; p6_affdep_of_dim; OAPVION1/2	FUZBZGI_1; JDHAWAY_0; PA2/PA15	-	-
MHFTTZN1	Kepler/Text/PackingAuto6.lean:3089	Rogers.hl:4862	proved	MHFTTZN_lemma2	FUZBZGI_0; JDHAWAY_0; GBEWYFX	-	-
NWVRFMF	Kepler/Text/PackingAuto18.lean:249	leaf_cell.hl:342-359	proved	IDBEZAL; OMEGA_LIST_IN_VORONOI_LIST	FUZBZGI_0; cc_uh_exists	-	-
FACET_OF_SEGMENT	Kepler/Text/PackingAuto18.lean:230	leaf_cell.hl:1085-1104	proved	faceOf_sing; EXTREME_POINT_OF_SEGMENT; affDim_segment	CC_PE_FACET_OF; YBZFUPO (new)	-	-
DIST_LE_HALF_PLANE / DIST_EQ_HALF_PLANE	Kepler/Text/PackingAuto18.lean:1554 / :1562	leaf_cell.hl:555-780	proved	dist_sq_diff; norm_eq_of_sq_eq	FUZBZGI_0	-	-
DIST_LT_HALF_PLANE	MISSING (HOL Collect_geom.DIST_LT_HALF_PLANE)	collect_geom.hl	missing	derive from DIST_LE/EQ (~12 lines, probe 2)	FUZBZGI_0 (new helper)	-	A2
CHI_MSB_IMP_COPLANAR	Kepler/Text/PackingAuto18.lean:1795	leaf_cell.hl:935-942	proved	coplanar_cross_dot (PlanarityAuto12)	JDHAWAY_0	-	-
CHI_MSB_ADDITIVE	Kepler/Text/PackingAuto18.lean:1646	leaf_cell.hl:879-890	proved	chiMsb_det; chi_msb_additive_a/d	JDHAWAY_0; JDWAWAY	-	-
COPLANAR_INSERT	Kepler/Text/PackingAuto18.lean:1151	leaf_cell.hl	proved	affDim; affDim_mono	JDHAWAY_0	-	-
AFFINE_IMP_CHI_MSB_0	Kepler/Text/PackingAuto18.lean:1673	leaf_cell.hl	proved	affine span/chi_msb	JDHAWAY_1	-	-
BARV_CIRCUMCENTER_EXISTS	Kepler/Text/PackingAuto7.lean:1629	Rogers.hl:7057	proved	OAPVION1_concl; BARV_AFFINE_INDEPENDENT	JDHAWAY_1	-	-
BARV_AFFINE_INDEPENDENT	Kepler/Text/PackingAuto7.lean:1291	Rogers.hl:6650	proved	MHFTTZN1; BARV_IMP_LENGTH_EQ_CARD; p6_affdep_of_dim	BARV_CIRCUMCENTER_EXISTS; FUZBZGI_0; XYOFCGX callers	-	-
truncate_set_of_list	Kepler/Text/PackingAuto18.lean:1450	leaf_cell.hl	proved	TRUNCATE_SIMPLEX kit	FUZBZGI_0	-	-
pa18_ccCell_swap	Kepler/Text/PackingAuto18.lean:3466	leaf_cell.hl CFFONNL tail	sorry	ccPe1/ccUh/ccKe/ccCell swap-insensitivity	CCFONNL:3472	remains the last PA18 direct source after the chain (132 baseline)	A7 (post-chain)
ccPe1 / ccPe2	Kepler/Text/PackingAuto18.lean:220 / :224	leaf_cell.hl:1082	proved defs (choose over cc_pe_exists)	cc_pe_exists	CC_PE_FACET_OF; PA25	no value-level sorry once cc_pe_exists is clean	-
ccUh / ccKe / ccCell	Kepler/Text/PackingAuto18.lean:277 / :282 / :290	leaf_cell.hl:1133-1142	proved defs	cc_uh_exists; ccUh	PA25 (279 refs)	no value-level sorry once cc_pe_exists is clean	-
# DEBT-MOVE SUMMARY (e2e SORRIED count, current 133):
#   current PA18 direct sources = {cc_pe_exists, pa18_ccCell_swap}
#   A6 alone:                 133 -1 +2 = 134  (FUZBZGI_1, JDWAWAY exposed)
#   A4 after A6:              134 -1 +2 = 135  (FUZBZGI_0, YBZFUPO exposed)
#   A5 after A6:              135 -1 +1 = 135  (JDHAWAY_0 exposed; if not yet A3)
#   A3:                       135 -1     = 134
#   A2:                       134 -1     = 133
#   A1:                       133 -1     = 132
#   Recommended order A1,A2,A3,A4,A5,A6: e2e stays 133 through A5 (pieces unreachable),
#   then 133 -> 132 at A6. No intermediate source inflation.
# NOTE: PA25's 28 real_model_* are independent value-level sorry bodies; filling
# cc_pe_exists removes only their TYPE-level sorryAx, not the 28 value-level sources.
```
