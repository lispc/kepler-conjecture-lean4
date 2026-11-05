# EVIDENCE — 每条结论的命令与原始输出

环境：主仓 HEAD `ec57d345`（读取时）/ `0abccb51`（交卷时；他道仅改 docs，Assembly/TameLp 行号锚点复核实测不变）；Lake 工具链 `leanprover/lean4:v4.32.2`；所有 Lean 探针用
`cd lean && nice -n 19 lake env lean /tmp/tciso/<probe>.lean`（AGENTS §3/§4，未跑 `lake build`；未写主仓）。

---

## A. HOL 计数与主定理

命令：

```bash
wc -l reference/flyspeck/text_formalization/tame/WMLNYMD.hl
grep -c prove_by_refinement reference/flyspeck/text_formalization/tame/WMLNYMD.hl
grep -c new_definition reference/flyspeck/text_formalization/tame/WMLNYMD.hl
grep -c new_specification reference/flyspeck/text_formalization/tame/WMLNYMD.hl
```

原始输出（`logs/hol_counts.log`）：

```
    1515 reference/flyspeck/text_formalization/tame/WMLNYMD.hl
56
16
1
```

73 个 `let` 绑定 = 56 prove + 17 def。逐条机器表（name/line/kind/nlines/internal_refs/external_refs/statement）：
`logs/hol_items.tsv`（由 `logs/parse_hol2.py` 生成，74 行含表头）。

主定理陈述与证明体（`WMLNYMD.hl:1498-1512`）：

```
let tame_correspondence_iso = prove_by_refinement(
  `!g H:(A)hypermap. good_graph_v4 g /\ tame_planar_hypermap H /\ 
    iso H (hypermap_of_list (fgraph g)) ==>
    tame g`,
  [
  REWRITE_TAC[tame_planar_hypermap];
  REPEAT WEAKER_STRIP_TAC;
  MATCH_MP_TAC tame_correspondence1;
  FIRST_X_ASSUM (MP_TAC o MATCH_MP Hypermap_iso.iso_imp_hyp_iso) THEN REPEAT WEAKER_STRIP_TAC;
  ASM_REWRITE_TAC[];
  BY(ASM_MESON_TAC[Oxaxucs.tame9a_iso;Oxaxucs.tame10_iso;Oxaxucs.tame11a_iso;Oxaxucs.tame11b_iso;Oxaxucs.tame12o_iso;Oxaxucs.tame13a_iso;])
  ]);;
```

内部依赖（`logs/hol_items.tsv` 的 `internal_refs` 列）与直接前置链见 `SCOPE.md` §A.2。

---

## B. 两份 `TamePlanarHypermap` 是否定义级相等

### B.1 探针源码（`logs/probeB.lean` / `logs/probeAdm.lean` / `logs/probeS11.lean`）

```lean
-- probeB.lean（截取）
example : @Kepler.Assembly.Tame1 = @Kepler.Text.TameLp.Tame1 := rfl
...  -- Tame2..Tame12o 共 11 条
example : @Kepler.Assembly.Tame13a = @Kepler.Text.TameLp.Tame13a := rfl   -- 预期失败

-- probeAdm.lean
example : @Kepler.Assembly.Adm1 = @Kepler.Text.TameLp.Adm1 := rfl
example : @Kepler.Assembly.Adm2 = @Kepler.Text.TameLp.Adm2 := rfl
example : @Kepler.Assembly.Adm3 = @Kepler.Text.TameLp.Adm3 := rfl        -- 失败
example : @Kepler.Assembly.AdmissibleWeight = @Kepler.Text.TameLp.AdmissibleWeight := rfl  -- 失败
example : @Kepler.Assembly.totalWeight = @Kepler.Text.TameLp.totalWeight := rfl
example : @Kepler.Assembly.Tame9a = @Kepler.Text.TameLp.Tame9a := rfl
```

### B.2 原始输出（`logs/probes.log`）

```
$ probeB (component defeq)
/tmp/tciso/probeB.lean:18:68: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  @Assembly.Tame13a = @Text.TameLp.Tame13a

$ probeAdm
/tmp/tciso/probeAdm.lean:5:62: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  @Assembly.Adm3 = @Text.TameLp.Adm3
/tmp/tciso/probeAdm.lean:6:86: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  @Assembly.AdmissibleWeight = @Text.TameLp.AdmissibleWeight
```

说明：Lean 只打印错误；`probeB.lean` 前 17 行（Tame1..Tame12o 的 `rfl`）与 `probeAdm.lean` 的 Adm1/Adm2/totalWeight/Tame9a **无输出 = 全部通过**。唯一失败点是 `Adm3`（及其传递的 `AdmissibleWeight`/`Tame13a`）。

### B.3 逐字定义

`Assembly.lean:2101-2102`：

```lean
def Adm3 (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) → True
```

`TameLp.lean:443-445`：

```lean
def Adm3 {α : Type*} [DecidableEq α] (H : Hypermap α) (w : Set α → ℝ) : Prop :=
  ∀ x ∈ H.darts, typeOfNode H x = (5, 0, 1) →
    aTame ≤ setSum (setOfTrianglesMeetingNode H x) w
```

HOL 源（`tame_defs.hl:124-127`）：

```
let adm_3 = new_definition' 
  `adm_3 (H:(A)hypermap) (w:(A->bool)->real) <=>
  (!x:A. x IN dart H /\ type_of_node H x = 5, 0, 1 ==> 
     (sum (set_of_triangles_meeting_node H x) w)  >= a_tame)`;;
```

结论：**不是定义级相等**；Assembly 版严格弱（`True`），TameLp 版忠实。存在单向私有桥 `b3_tamePlanarHypermap`（`Assembly.lean:2367`），反向不存在。

### B.4 S11 勘误：`GoodGraphV4` 五占位已真化

`logs/probeS11.lean` 对六个 def 两两 `rfl`：`FinalGraph/AllUniq/GoodFacesV3/VerticesSet2Eq/GoodListNodes/GoodGraphV4` 全部通过（输出仅第 15 行 Tame13a 的预期错误）。原始输出（`logs/probes.log:53-62`）：

```
$ probeS11
/tmp/tciso/probeS11.lean:15:68: error: Type mismatch
  ... @Assembly.Tame13a = @Text.TameLp.Tame13a
'Kepler.Text.TameSpine.goodGraphV4Spine_implies' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Text.TameSpine.goodGraphV4Spine_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kepler.Assembly.tamePlanarHypermapRestricted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## C. Lean 资产普查

`ASSETS.tsv` 为 73 行（56 prove + 17 def），表头逐字按要求。分类计数（由 `logs/gen_assets.py` 生成）：

```
rows 73 Counter({'MISSING': 71, 'EXISTS-STD3': 1, 'EXISTS-TAINTED': 1})
```

- `EXISTS-STD3`：`sumn_cons` → `Kepler.Text.TameSpine.sumnCons`（`TameList45.lean:117`），`#print axioms = [propext]`，语句逐字 `∀ {h}{hs}, (h::hs).sum = h + hs.sum`（`logs/probes.log:65-68`）。
- `EXISTS-TAINTED`：`tame_correspondence_iso` → `Kepler.Assembly.tameCorrespondenceIso`（`Assembly.lean:2450`），`[propext, sorryAx, Classical.choice, Quot.sound]`；污染根 = 自身 `sorry`（`logs/probes.log:1-7`）。
- `EXISTS-DEF-EQ`：0。
- `MISSING`：71（含 54 个 prove + 17 个 def）。

岛内 WMLNYMD 移植检索（`logs/island_grep.log`）：

```
$ grep -rn "WMLNYMD\|wmlnymd\|tame_correspondence\|tameCorrespondence" lean/Kepler/Text/TameSpine/
lean/Kepler/Text/TameSpine/GoodGraph.lean:143:Assembly.lean:681 的 `∃ H'` 分量）与 A8 假设侧（`tameCorrespondenceIso` 的
```

即：只有一条注释提及，**零移植**。岛 75 文件、5 个直接 import Assembly（`Keystone/GoodGraph/TameList1/2/3`）。

---

## D. 规模比例（实测）

命令与原始输出见 `logs/size_ratios.log`：

```
    14428 reference/flyspeck/text_formalization/tame/tame_list.hl
   30250 lean/Kepler/Text/TameSpine/TameList1..69 合计     -> 2.097x
      949 reference/flyspeck/text_formalization/tame/DANGEYJ.hl
      329+642+639 = 1610 TameList70..72                  -> 1.697x
     1105 reference/flyspeck/text_formalization/tame/RXOKSKC.hl
      261+553+516+615 = 1945 TameList65+66+68+69          -> 1.760x
```

Conforming 1.47x 引自 `docs/archive/projects/tamespine-port-plan.md` §4（非本波实测）。本波采用区间 **1.5–2.1x**；WMLNYMD 本体 1,461 行 prove 区 → 2,649–3,034 行；端到端 4,199–5,394 行。明细见 `SIZING.md`。

---

## E. 前置判定

### E1/E2：`jcajydu` / `Reduction5` 零依赖

```
$ grep -n "JCAJYDU\|Jcajydu\|jcajydu\|Reduction5\|reduction5\|restricted_hypermap" WMLNYMD.hl
(zero matches)
```

`WMLNYMD.hl` 全文唯一外部 Oxaxucs 引用是 :1509 的六件 iso 引理。主定理证明体不构造图、不调 `jcajydu`。

### E3：岛的 74/75 环

BFS 原始输出（`logs/import_bfs.log`）：

```
island files: 75
island files that do NOT reach Kepler.Assembly: ['Kepler.Text.TameSpine.TameOpposite1']
TameList45 reaches Assembly: True
TameList56 reaches Assembly: True
Assembly reaches TameList45: False
LocalConcl reaches TameList45: False
```

结论：**74/75 岛文件传递 import Assembly**；Assembly/LocalConcl 当前不 import 岛（无现存环）。W3 若落成“import 岛”的下游模块，Assembly 无法 import 它（会成环）。W3 需要的具体岛件见 `PLAN.md` §E3（`sumnCons`、`memFaceLemma`/`cardFaceOfList`、`listOfFaces`/`faceRep`、`hypIsoCardComponents` 等）。

### E4：主定理陈述与现状态

`#print` 原始输出（`logs/probes.log:1-7`）：

```
theorem Kepler.Assembly.tameCorrespondenceIso.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (g : Kepler.Graphs.Graph)
  (H : Kepler.Text.Hypermap α) (H' : Kepler.Text.Hypermap (ℕ × ℕ)),
  Kepler.Assembly.GoodGraphV4 g →
    Kepler.Assembly.TamePlanarHypermap H →
      Kepler.Assembly.HypermapIso H H' → Kepler.Assembly.IsHypermapOfList g.fgraph H' → Kepler.Graphs.tame g :=
fun {α} [DecidableEq α] g H H' hgg ht hiso hIs => sorry
```

`#print axioms`（`logs/probe_bridge.log`）：

```
'Kepler.Assembly.tameCorrespondenceIso' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Kepler.Assembly.jcajydu' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`TameCorrBase`（Assembly-free、标准三）已提供 `isHypermapOfListTl_unique` / `isHypermapOfListTl_iff_eq_hypermapOfList` / `hypermapIso_of_isHypermapOfListTl`（`lean/Kepler/Text/TameCorrBase.lean:107/148/156`；`tamecorr-w1/logs/*` 实测标准三），故 Lean 的 `hIs` 可归约到 canonical `hypermapOfList`，与 HOL 的 `iso H (hypermap_of_list …)` 等价。**不能**据此消除 `Adm3` 缺口（见 B）。

---

## F/G 的支撑

- `Graphs/Tame.lean:164` 与 HOL `import_tame_classification.hl:116` 的六合取逐项对照：见 `SIZING.md`/`PLAN.md` §G2；两侧都是 `tame9a/10/11a/11b/12o/13a`，无缺项。
- `Assembly.lean:2444` `jcajydu` 与 :2450 `tameCorrespondenceIso` 是两个并列 `sorry`，互不引用（`#print` 与 `grep`）。
- 探针未触碰主仓：`git status --short` 在本波前后均为空（见 `logs/baseline_status.txt`，如附）。

---

## H. W3 上游安全基座复核（2026-11-06 本波实测）

`TameCorrBase.olean` 在 `.lake` 中缺失（源码在 HEAD `aa567796` 落库，但构建产物不在）。本波用
`lake env lean -o /tmp/tciso/build/Kepler/Text/TameCorrBase.olean Kepler/Text/TameCorrBase.lean`
standalone 重编（RC=0，4.6s），临时放入 `.lake` 后跑探针，随后删除该临时 olean（主仓 tracked 零改动）。

探针（`logs/probeW3base.lean`）输出（`logs/probe_w3base.log`）：

```
Kepler.Text.TameCorrBase.isHypermapOfListTl_unique {L} {H₁ H₂}
  (h₁ : IsHypermapOfListTl L H₁) (h₂ : IsHypermapOfListTl L H₂) : H₁ = H₂
Kepler.Text.TameCorrBase.isHypermapOfListTl_iff_eq_hypermapOfList {L} {hL : GoodList L} {H} :
  IsHypermapOfListTl L H ↔ H = hypermapOfList L hL
Kepler.Text.TameLp.hypermapOfList (L) (hL : GoodList L) : Hypermap (ℕ × ℕ)
Kepler.Graphs.tame (g : Graph) : Prop
'...isHypermapOfListTl_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'...isHypermapOfListTl_iff_eq_hypermapOfList' depends on axioms: [propext, Classical.choice, Quot.sound]
```

结论：W3 的基座（TameLp + TameCorrBase + Graphs）可独立编译、标准三；唯一实时工程注记是
`TameCorrBase.olean` 需在 W3 车道内重编（或先补 `.lake`）。
