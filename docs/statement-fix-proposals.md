# 陈述修复提案（statement-fix-proposals）

> 提案官轮产出（2026-09-28）。本轮**零 .lean 改动**：全部修复以本文件 + `docs/statement-fix-proposals-patches/`
> 补丁草案交付，供人类与编排者审查后由专门的修复波（陈述修改需闸门豁免）执行。
> 依据：`docs/fill-worker-playbook.md`（§5.1 跳过清单即本轮黑名单）、
> `docs/statement-fidelity.md`（唯一质量阀门；每个修复的 (d) 节按其口径写）。
> 对照基准：`reference/flyspeck` @ `1ce0353`。

## 0. 总表与分级统计

| # | 陈述 | Lean 位置 | HOL 原文 | 偏差性质 | 分级 |
|---|---|---|---|---|---|
| 1 | `SUM_INTER` | LocalAuto38.lean:419 | local/terminal.hl:233 | 移植错误（junk 约定失配） | **A** |
| 2 | `regular_spherical_polygon_area_asnFnhk` | PackingAuto22.lean:731 | counting_spheres.hl:945 | 桩依赖（asnFnhkP22=0） | B |
| 3 | `vol_solid_triangle_ortho` | PackingAuto22.lean:1008 | counting_spheres.hl:1335 | 桩依赖（volSolidTriangleP22=0） | B |
| 4 | `EDGE_PAIR_pr23` | PackingAuto22.lean:2815 | counting_spheres.hl:5003 | 桩依赖（eFanP22=恒等） | B |
| 5 | `BIJ_FACET_HYPERFACE` | PackingAuto22.lean:2768 | counting_spheres.hl:4821 | 桩依赖（faceSet=∅ 等） | B |
| 6 | `HYPERFACE_EXISTS` | PackingAuto22.lean:2926 | counting_spheres.hl:5286 | 桩依赖（faceSet=∅ 等） | B |
| 7 | `RELATIVE_INTERIOR_AFFINE_FACE` | PackingAuto22.lean:1659 | counting_spheres.hl:2702 | **无病**（反例指控不成立） | **A**（原位填证） |
| 8 | `BIJ_DART_POLYEDGE` | PackingAuto22.lean:2934 | counting_spheres.hl:5301 | 桩依赖（darts=∅） | B |
| 9 | `PACK_INEQ_DEF_A_797` | PackingAuto22.lean:3172 | counting_spheres.hl:6540 | 桩依赖（arclength22=0） | B |
| 10 | `MCELL4_EDGE` vs `MCELL_EDGE` | PackingAuto4.lean:1524 / 1561 | bump.hl:766 / 816 | **无病**（疑点解除） | 解除（零补丁） |
| 13 | `DUUNHOR_concl` | PackingAuto2.lean:556 | Rogers.hl:1682 | 前提缺失（缺 Packing/saturated） | **A′**（前提补全型） |

**统计：A = 2（项 1、7），B = 7（项 2–6、8、9），C = 0；另项 10 = 疑点解除，无需修复。**

分级口径：A = 可立即修（加前提后即等价于 HOL / 陈述无病可直接填证）；
B = 等 def 落地再修（陈述忠实且冻结不动，桩语义下不可证）；
C = 需重移植（本轮无一例——8 枚 PA22 陈述全部与 HOL 逐字同义，无移植错误）。

## 1. `SUM_INTER` — 分级 A（加 `A.Finite` 前提）

**(a) HOL 裁决**：`reference/flyspeck/text_formalization/local/terminal.hl:233-236`，
陈述**无条件**：
`!(A:A->bool) B f. sum (A INTER B) f = sum A (\i. if (i IN B) then f i else &0)`。
当前 Lean 陈述（LocalAuto38.lean:419-420）与之逐字同义，但**分歧不在陈述文本而在
`sum` 的移植约定**：HOL 的 `sum` 是支撑集（support）求和——非零点集有限时对支撑集
正常求和，仅支撑集无限时 junk 为 0；而项目的 `setSum`
（PackingAuto2.lean:124-126）按**集合**取 junk——只要集合无限一律 0
（其注释"same convention"仅对有限支撑情形成立）。故这是**移植错误，非桩依赖**：
无条件命题在 `setSum` 语义下为假。

**(b) Lean 层验证（已机器验证，0 error）**：反例 `A = univ(Set ℕ), B = {0},
f = const 1`：LHS = `setSum({0}, const 1) = 1`；RHS = `setSum(univ, …) = 0`
（junk）。ScratchStmtCheck1 第一节以
`example : ¬ ∀ {α} (A B) (f), setSum (A ∩ B) f = setSum A (fun i => if i ∈ B then f i else 0)`
形态构造该反例并编译通过。

**(c) 修复补丁**：`/tmp/statement-fix-proposals/01-SUM_INTER.patch`。
新陈述全文（唯一实质改动 = 前提 `(hA : A.Finite)` + 证明删去两个 junk 分支）：

```lean
theorem SUM_INTER {α : Type*} (A B : Set α) (f : α → ℝ) (hA : A.Finite) :
    setSum (A ∩ B) f = setSum A (fun i => if i ∈ B then f i else 0) := by
  by_cases hAB : (A ∩ B).Finite
  · rw [setSumDifpos_p38 f hAB]
    rw [setSumDifpos_p38 (fun i => if i ∈ B then f i else 0) hA]
    have hsub : hAB.toFinset ⊆ hA.toFinset := by
      intro w hw
      rw [Set.Finite.mem_toFinset] at hw ⊢
      exact hw.1
    have h0 : ∀ w ∈ hA.toFinset, w ∉ hAB.toFinset →
        (if w ∈ B then f w else 0) = 0 := by
      intro w hAw hw
      rw [if_neg (fun hB => hw ((Set.Finite.mem_toFinset hAB).mpr
        ⟨(Set.Finite.mem_toFinset hA).mp hAw, hB⟩))]
    have key : ∑ w ∈ hAB.toFinset, f w =
        ∑ w ∈ hAB.toFinset, (if w ∈ B then f w else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Set.Finite.mem_toFinset] at hw
      rw [if_pos hw.2]
    rw [key, Finset.sum_subset hsub h0]
  · exact absurd (Set.Finite.subset hA Set.inter_subset_left) hAB
```

消费者核查：全树 grep `SUM_INTER` 无任何消费点（仅同名前缀
`SUM_INTERIOR_AGL_LEMMA` 无关），改陈述零波及。副作用：`setSumDifneg_p38`
（LocalAuto38.lean:408）在删除 junk 分支后成为死代码——闸门禁删结构行，保留即可。

**(d) 保真论证**（statement-fidelity.md 口径）：在 `A.Finite` 前提下 `setSum`
两侧均取真求和分支，与 HOL 的 `sum` 逐点相等，故修复后陈述在所有可满足实例上
与 HOL 定理语义一致。删去的无限-A 分支在 HOL 中由支撑集约定自动为真，但
Flyspeck 全部用例 `A` 有限（原 docstring 已核注），故前提不削弱任何 HOL 用例的
可用性。**须随修复登记的折算点**（类比 statement-fidelity.md 附录折算 6 的
CARD/sum 无限集约定）：`setSum` 的按集合 junk 约定与 HOL 支撑集 junk 的偏差
自此由本条前提吸收；若未来出现 `A` 无限的 `setSum` 移植需求，应走支撑集精确
版 `setSum`（全局改动，C 级，本轮不提案）。

**(e) 分级：A**（加前提即闭合，反例已核，零消费者波及）。

**(f) 状态（2026-10-12 用户批准；应用波复核记录）**：批准见
docs/projects/archive/sf-decision-batch-2026-10-12.md 项 1。应用波（LocalAuto38
车道）复核发现本修复**已随 `ddc3683e`（2026-09-29，STATEMENT-FIX 闸 PASS）
落地**：以 ddc3683e^ 为基 `git apply` 本补丁成功，且应用产物 SUM_INTER 区域
与现树 LocalAuto38.lean:426-454 逐字节一致；全树零消费者复核依旧成立；
`lake build Kepler.Text.LocalAuto38` 自然退出 0 error（2026-10-12）。
**工作树对该文件零 diff——无重起草应用波可执行，STATEMENT-FIX 闸无需再走**；
补丁 01-SUM_INTER.patch 转历史存档（头注已核账），不可再贴。

## 2. `regular_spherical_polygon_area_asnFnhk` — 分级 B

**(a)** Lean PackingAuto22.lean:729-737；HOL `counting_spheres.hl:945-947`
（`!h k. 3 <= k /\ &1 <= h /\ h <= h0 ==> regular_spherical_polygon_area (h*sqrt3/4 + sqrt(&1-(h/&2) pow 2)/&2) (&k) = &2*pi - &2*asnFnhk h (&k) (&1) (&1) (&1) (&1)`）。
Lean 陈述与之逐字同义，**移植无错**；偏差纯为桩依赖：`asnFnhkP22 := 0`
（PA22:261 桩，真定义在 Ysskqoy.hl / PackingAuto18 bank）。LHS 用的
`regularSphericalPolygonAreaP22` 是**真公式**（PA22:266-268），非桩。

**(b)** 反例 `h = 1, k = 3`（前提 1 ∈ [1, h0=1.26] ✓）：桩下 RHS = 2π − 6·0 = 2π，
而 LHS = 2π − 6·asn(√3/2·sin(π/3)) = 2π − 6·asn(3/4) ≠ 2π，因 asn(3/4) = arcsin(3/4) > 0。
已机器验证（ScratchStmtCheck2，用后即删；仅用 arcsin 正性与 π>0，无需精确三角值）。

**(c)** `/tmp/statement-fix-proposals/02-regular_spherical_polygon_area_asnFnhk.patch`
—— 无陈述改动；陈述冻结至 `asnFnhkP22` 落地。

**(d)** 陈述文本不动，落地后即为 HOL 镜像。落地后证明是展开级的：HOL 侧证明
就是 `REWRITE_TAC[Sphere.regular_spherical_polygon_area; Sphere.asnFnhk; Sphere.h0]`
三条定义展开；Lean 侧 `unfold regularSphericalPolygonAreaP22 asnFnhkP22新定义 + congr`
（参照同文件已证的 `regular_spherical_polygon_area_797`：unfold + congr 1）。

**(e) 分级：B**。

## 3. `vol_solid_triangle_ortho` — 分级 B

**(a)** Lean PackingAuto22.lean:1007-1014；HOL `counting_spheres.hl:1335-1341`。
逐字同义，移植无错；桩依赖：`volSolidTriangleP22 := 0`（PA22:263）。
（`dihV`/`arcV`/`asn` 均为真定义：Geom/LuneVolume.lean:33-43、PA22:107。）

**(b)** 反例（纸面，全步骤初等）：`u = e1, v = e2, w = e1+e3`。
前提：`(w−u)·v = e3·e2 = 0` ✓，`(w−u)·u = e3·e1 = 0` ✓；
`¬Coplanar{0,e1,e2,e1+e3}`：det[e1;e2;e1+e3] = 1 ≠ 0，四点仿射无关。
结论侧：`t = cos(arcV 0 e2 e1) = cos(arccos 0) = 0`；
`bet = dihV 0 e2 e1 (e1+e3)`：按 LuneVolume 定义逐项代入，va = e1, vb = e1+e3,
vc = e2 两两正交故投影不变，vap = e1, vbp = e1+e3，
`bet = arcV 0 e1 (e1+e3) = arccos(1/√2) = π/4`。
桩下定理断言 `3·0 = π/4 − asn(sin(π/4)·0) = π/4`，假。
（本项目 kit 无 ¬Coplanar 负向引理，仿射无关→不共面的机器化留待恢复后补，
见 §11；其余每一步均可按 PA22:2223-2230 的 explicit-vector 惯用法机器化。）

**(c)** `/tmp/statement-fix-proposals/03-vol_solid_triangle_ortho.patch` —— 无陈述改动。

**(d)** 陈述文本不动，落地（Sphere.vol_solid_triangle 真定义）后即为 HOL 镜像；
HOL 证明 = `REWRITE_TAC[vol_solid_triangle]` 后解析归零，属定义展开级。

**(e) 分级：B**。

## 4. `EDGE_PAIR_pr23` — 分级 B

**(a)** Lean PackingAuto22.lean:2814-2817；HOL `counting_spheres.hl:5003-5006`
（`!x V E d d'. e_fan x V E d = d' ==> pr2 d = pr3 d' /\ pr3 d = pr2 d'`）。
逐字同义，移植无错；桩依赖：`eFanP22 := 恒等`（PA22:216）。

**(b)** 反例（已机器验证）：取 `d = (0, x, 0)`，
`x = EuclideanSpace.single 0 1 ≠ 0`（V3 = EuclideanSpace ℝ (Fin 3)，
`pr2 d = d.2.1 = x`，`pr3 d = d.2.2 = 0`）。恒等桩下取 `d' = d`，前提
`eFanP22 x V E d = d'` 即 `rfl` 平凡成立，结论要求 `pr2 d = pr3 d` 即 `x = 0`，
矛盾（`‖x‖ = 1 ≠ 0`）。

**(c)** `/tmp/statement-fix-proposals/04-EDGE_PAIR_pr23.patch` —— 无陈述改动。

**(d)** 陈述文本不动；落地（fan.hl `e_fan`，Planarity lane）后即为 HOL 镜像。
HOL 证明 = `REWRITE_TAC[Fan.e_fan; Fan.pr2; Fan.pr3]` + PAIR_SURJECTIVE，定义展开级。

**(e) 分级：B**。

## 5. `BIJ_FACET_HYPERFACE` — 分级 B

**(a)** Lean PackingAuto22.lean:2767-2774；HOL `counting_spheres.hl:4821-4825`
（`?b. BIJ b {f | f facet_of p} (face_set (hypermap1_of_fanx (vec 0, vertices p, edges p)))`）。
逐字同义，移植无错；**三重桩依赖**：`hypermap1OfFanxP22` 空超图桩
（PA22:204-209，darts=∅、三个置换=恒等）、`verticesP22 := ∅`（PA22:222）、
`edgesP22 := ∅`（PA22:225）。

**(b)** 桩机制（已机器验证）：桩 faceSet =
`setOfOrbits ∅ _ = ∅`；`Set.BijOn b S ∅` 的 MapsTo 分量强制 `S = ∅`
（每个 `f ∈ S` 须 `b f ∈ ∅`）。但 `{f | FacetOf f p}` 对任何满足前提的 p 非空：
有界 polyhedron + 0 ∈ interior ⇒ 满维多面体必有 facet（经典多面体论；HOL 自身
证明经 `BIJ_TRANS` 过 `topological_component_yfan` 构造出真双射，故 HOL 侧
face_set 非空——两系统同题，唯桩侧空）。前提可满足性（纸面）：p = ±e_i 六点
凸包（八面体）满足 bounded/polyhedron/interior 三前提。

**(c)** `/tmp/statement-fix-proposals/05-BIJ_FACET_HYPERFACE.patch` —— 无陈述改动。

**(d)** 陈述文本不动；三桩落地后即为 HOL 镜像；落地后按 HOL 原证明
（BIJ_TRANS 两跳，经 topological_component_yfan）重移植，非定义展开级，
属修复波 GIANT 工作量。

**(e) 分级：B**。

## 6. `HYPERFACE_EXISTS` — 分级 B

**(a)** Lean PackingAuto22.lean:2925-2932；HOL `counting_spheres.hl:5286-5291`
（`?!f. f IN face_set (hypermap1_of_fanx (vec 0, vertices P, edges P)) /\ dartset_leads_into_fan (vec 0) (vertices P) (edges P) f = U`）。
逐字同义，移植无错；三重桩依赖：faceSet=∅（同项 5）、
`topologicalComponentYfanP22 := True`（PA22:230-231，使前提 hU 平凡可满足）、
`dartsetLeadsIntoFanP22 := ∅`（PA22:219-220）。

**(b)** 桩机制（已机器验证）：对**任何** P、U，结论的
∃! 存在半边要求 `f ∈ faceSet = ∅`，不可满足——即桩语义下"前提可满足 ⇒ 结论为假"
（与项 5 不同，这里连 P 的前提都不必实例化：机制对一切 P 成立）。前提可满足性
（纸面）：同项 5 的八面体实例。

**(c)** `/tmp/statement-fix-proposals/06-HYPERFACE_EXISTS.patch` —— 无陈述改动。

**(d)** 陈述文本不动；五桩（hypermap/vertices/edges/topologicalComponentYfan/
dartsetLeadsIntoFan）落地后即为 HOL 镜像；落地后按 HOL 原证明
（`Polyhedron.WBLARHH_BIJ`）重移植。

**(e) 分级：B**。

## 7. `RELATIVE_INTERIOR_AFFINE_FACE` — 分级 A（原位填证；反例指控不成立）

**(a)** Lean PackingAuto22.lean:1658-1662；HOL `counting_spheres.hl:2702-2705`
（`!C p f. convex C /\ f face_of C /\ p IN affine hull f /\ p IN relative_interior C ==> f = C`）。
逐字同义。**playbook §5.1 记载的 "f=∅ 反例" 经裁决不成立**：FaceOf ∅ C 确可满足
（Polytope.lean:79 `empty_faceOf`），但反例卡死在另一前提上——
`hap : p ∈ (affineSpan ℝ ∅ : Set V3)` 不可满足：`affineSpan ℝ ∅ = ⊥`，
而 `↑(⊥ : AffineSubspace ℝ V3) = ∅`（Mathlib `affineSpan_empty` + bot 载体）。
故 f = ∅ 时陈述空真；f ≠ ∅ 时同文件已证的私有 helper
`p22_face_of_affine_rint`（PA22:1672-1676，faceOf_disjoint_rinterior +
faceOf_eq_affineInter + mem_rint_iff 路线）直接闭合。**偏差性质 = 无**
（既非移植错误亦非桩依赖），系前两轮工人漏看 `hap ⇒ f.Nonempty` 这一步。

**(b) Lean 层验证（已机器验证，0 error）**：ScratchStmtCheck1 第二、三节：
(i) 机器证明 `p ∈ affineSpan ℝ f → f.Nonempty`（`by_contra` + 
`AffineSubspace.span_empty` + `AffineSubspace.bot_coe`）；(ii) 复制 helper 证明体
（私有不可跨文件引用）；(iii) 以**与原定理逐字相同的陈述**完整证明
`RELATIVE_INTERIOR_AFFINE_FACE_fixed`。原 sorry 可原位填掉，无需任何陈述修改。

**(c)** `/tmp/statement-fix-proposals/07-RELATIVE_INTERIOR_AFFINE_FACE.patch`
—— 陈述不变，`sorry` 替换为（该形式已经 probe 文件与 scratch 完整验证）：

```lean
  have hfne : f.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty.mp h0, AffineSubspace.span_empty,
      AffineSubspace.bot_coe] at hap
    exact hap
  exact p22_face_of_affine_rint hf hfne hc hap hip
```

（此改动 = 删一行 sorry + 增证明行，**连闸门豁免都不需要**，走普通填证验收即可。）

**(d) 保真论证**：陈述文本一字不动，与 HOL 逐字一致维持冻结。playbook 提议的
"加 `f.Nonempty` 前提"方案虽也忠实（该前提可由 hap 导出，修复后陈述与原陈述
在 HDF 语义下等价），但属对 HOL 的无谓表面弱化，且多一条陈述 diff 须走豁免；
原位填证严格更优，本提案据此推翻原方案。

**(e) 分级：A**（零陈述改动、纯填证、helper 已在库）。

## 8. `BIJ_DART_POLYEDGE` — 分级 B

**(a)** Lean PackingAuto22.lean:2933-2939；HOL `counting_spheres.hl:5301-5306`
（`?b. BIJ b (dart (hypermap1_of_fanx (vec 0, vertices P, edges P))) {(e,f1) | e facet_of f1 /\ f1 facet_of P}`）。
逐字同义，移植无错；桩依赖：darts = ∅（同项 5 桩）。

**(b)** 桩机制（已机器验证）：源集 ∅ 时 `Set.BijOn`
的 SurjOn 分量强制目标集 `⊆ b '' ∅ = ∅`；而目标
`{fe | FacetOf fe.2 fe.1 ∧ FacetOf fe.1 P}` 对满足前提的 P 非空（纸面：取
f₁ facet of P，f₁ 为多边形必有边/facet e——注意 FacetOf 要求 f ≠ ∅ 且
affDim = affDim s − 1，故不能取平凡的 (P,P) 实例，须两层 facet，见
Polytope.lean:47-48 的 FacetOf 定义）。

**(c)** `/tmp/statement-fix-proposals/08-BIJ_DART_POLYEDGE.patch` —— 无陈述改动。

**(d)** 陈述文本不动；hypermap 桩落地后即为 HOL 镜像；落地后按 HOL 原证明
（`PREIMAGE_BIJ`，双射取 `fchanged ∘ SND` 经 face 的复合）重移植。

**(e) 分级：B**。

## 9. `PACK_INEQ_DEF_A_797` — 分级 B

**(a)** Lean PackingAuto22.lean:3169-3175；HOL `counting_spheres.hl:6540-6546`
（`pack_ineq_def_a /\ norm v0 = &2 /\ &2*h0 <= dist (v,v0) /\ &2 <= norm v /\ norm v <= &2*h0 ==> #0.797 + acs(norm v / &4) - pi/&6 < arclength (norm v) (&2) (dist (v,v0))`）。
逐字同义，移植无错；桩依赖：`arclength22 := 0`（PA22:3170，"NEEDS HOL arclength
(pack1.hl; PackingAuto1, no olean)"）。顺带核过常量：`h0 = 1.26`
（PackingAuto2.lean:458）= `pack_defs.hl:147` ✓ 忠实。

**(b)** 反例（已机器验证）：`v0 = single 0 2`，
`v = single 0 (−2)`（EuclideanSpace.single 惯用法，PA12:651-655 同款）：
`‖v0‖ = 2` ✓；`2·h0 = 2.52 ≤ 4 = dist v v0` ✓；`2 ≤ ‖v‖ = 2 ≤ 2.52` ✓；
`packIneqDefAP22 = True` 桩平凡 ✓。桩下结论：`0.797 + acs(1/2) − π/6 < 0`；
但 `acs(1/2) = arccos(1/2) ≥ 0`（`Real.arccos_nonneg`）且 `0.797 > π/6`
（`π < 22/7 < 4.782`，`Real.pi_lt_22_div_7`），LHS > 0，矛盾。

**(c)** `/tmp/statement-fix-proposals/09-PACK_INEQ_DEF_A_797.patch` —— 无陈述改动。

**(d)** 陈述文本不动；arclength 落地（先 PackingAuto1 后接 `arclength22`）后
即为 HOL 镜像；落地后按 HOL 原证明（REWRITE[Sphere.ineq; acs_sqrt_x1_d4;
arclength_x_123] + Ysskqoy `ineq` 在 `(‖v‖², ‖v0‖², (2h0)², 1, 1, 1)` 处实例化）
重移植。

**(e) 分级：B**。

## 10. `MCELL4_EDGE` vs `MCELL_EDGE` 裁决 — 疑点解除，零补丁

**(a) HOL 对照**：
- `MCELL4_EDGE` = `bump.hl:766-768`：`packing ∧ saturated ∧ ¬NULLSET(mcell4 V ul) ∧ barV V 3 ul ==> ({u,v} IN edgeX V (mcell4 V ul) <=> ~(u=v) /\ {u,v} SUBSET set_of_list ul)`；
- `MCELL_EDGE` = `bump.hl:816-819`：`k < 4 ∧ packing ∧ saturated ∧ ¬NULLSET(mcell k V ul) ∧ barV V 3 ul ∧ e IN edgeX V (mcell k V ul) ==> e SUBSET set_of_list(truncate_simplex 2 ul)`。

Lean 两侧（PackingAuto4.lean:1524-1537 / 1561-1611；任务书写的历史行号 1021/1039
为填证前旧行号，二定理之间现隔 MCELL3_EDGE 与 EDGE_MCELL_EL）与 HOL 逐字同义
（前提排列次序不同，内容一致），**移植无误**。

**(b) 不相容疑点不成立的两个独立理由**：
1. **论域不相交**：`MCELL_EDGE` 有 `k < 4` 前提，只谈 mcell 0..3；
   `MCELL4_EDGE` 只谈 mcell 4（= mcell4，PackingAuto2.lean:349-357 + 359-363 的
   dispatch）。疑点的唯一成因是在 k=4 处套用 MCELL_EDGE 的结论——mcell 4 的边
   可含 `{el 0 ul, el 3 ul}`（∉ set_of_list(trunc 2 ul)），与 MCELL4_EDGE 相抵——
   但被 `k < 4` 挡死。同一 ul 下两类胞还在 hl 条件上互斥（mcell3 要求
   √2 ≤ hl ul，mcell4 要求 hl ul < √2，PA2:340-357），¬nullSet（非空测度）下
   两者不能同为非空胞，边集无从打架。
2. **机器事实**：两定理当前在 PA4 内**均已完整证明**（MCELL4_EDGE 经
   `hdtfnfz_p4` + `LEPJBDJ`(PA11:338) + `setOfList_truncateSimplex3_p4` +
   `edgeX_pair_iff_p4`(PA4:960) 闭合；MCELL_EDGE 经 `EDGE_MCELL_EL` +
   `MCELL3_EDGE`/`MCELL2_EDGE`/`EDGE_IMP_K2` 闭合，证明体无 sorry）；
   一致内核中两条已证定理不可能不相容——"疑似不相容"在二者证成之刻即已消解。
   （复核动作：`lake build Kepler.Text.PackingAuto4` 确认二声明无
   "declaration uses 'sorry'" 警告，见 §11。）

**(c)** 零补丁，两处陈述冻结不动。

**(d)** 两陈述均与 HOL 逐字同义，保真状态不变。

**(e) 裁决：解除**（不适用 A/B/C；建议编排者将 §5.4 PA4 条的该疑点注记划掉）。

## 11. 机器验证状态与环境事故注记

本轮使用两个未跟踪 scratch 模块做反例/机制验证（按"用完即删"纪律，
**验证通过后已删除**，连同其构建产物）：

- `ScratchStmtCheck1.lean`（import PA2 + Polytope）：项 1 反例 + 项 7 原位证明；
- `ScratchStmtCheck2.lean`（import PA2 + Hypermap + Polytope；PA22 桩 def 逐字
  内联副本）：项 4/2/9 反例 + 项 5/6/8 桩机制。

**全部机器验证通过（2026-09-28 本轮，direct lean 对现存 olean，0 error）**：

- 项 1：`¬ ∀ {α} (A B) (f), setSum (A ∩ B) f = setSum A (fun i => if i ∈ B then f i else 0)`
  的反例实例化证明通过；patch 01 的**新陈述 + 证明体整体**另经 /tmp probe
  （复制私有 `setSumDifpos`）端到端编译通过；
- 项 7：与原定理逐字相同的陈述完整证明通过；patch 07 的
  `rw [AffineSubspace.span_empty, AffineSubspace.bot_coe]` 形式经 probe 验证
  （注意：本 toolchain 无 `affineSpan_empty`，正确名 `AffineSubspace.span_empty`；
  `↑(⊥) = ∅` 为 `AffineSubspace.bot_coe`）；
- 项 2/4/9：三个反例的完整 `¬ ∀ …` 证明通过（仅用 arcsin 正性/arcsin_eq_zero_iff、
  `EuclideanSpace.single_eq_zero_iff`/`dist_single_same`、`Real.arccos_nonneg`/
  `Real.pi_lt_four` 等已证库引理）；项 5/6/8：桩机制
  （faceSet=∅、`BijOn` 的 MapsTo/SurjOn 半边强制空、∃! 空集不可满足）证明通过；
- 项 10：源码复核 `hdtfnfz_p4`（PA4:826）与 `LEPJBDJ`（PA11:338）证明体均无
  sorry（PA11 检出的 "sorry" 是其 docstring 文字），两主定理证明体完整（见 §10）。

**环境事故（供编排者知悉）**：2026-09-28 20:36 前后，本仓库
`lean/.lake/packages/mathlib` 工作树与全部 Mathlib olean 被外部并发的
`git clone mathlib4` 进程清除并反复覆写（观测到 ≥3 个并发 clone 竞争同一路径，
其中一路来自另一工作副本 `/private/tmp/kcwt`；时间点在本轮两次 lake build 之间，
非本轮所为），Mathlib 于 20:40 前后重建完成。同窗口内另有**并行填证工人**在
修改 PA4/PA6/PA7/PA18/PA22/LA38（git status 可证），PA6/PA7 一度中间态导致
PA22 暂不可 import——ScratchStmtCheck2 因此改为仅依赖健康模块 + PA22 桩逐字
内联副本完成验证，结论不变。本轮零 .lean 改动、零 tracked 文件改动，
唯一仓库写入即本文档。

## 12. 给修复波的执行顺序建议

1. **项 7**（A，无豁免）：普通填证验收，patch 即 diff，先做——零风险且立即清账；
2. **项 1**（A，豁免）：按 §1 patch 改陈述；闸门第②道按 §6 惯例以"新增行逐字
   重现冻结前缀"校验（前缀 = `theorem SUM_INTER {α : Type*} (A B : Set α) (f : α → ℝ) `，
   注意新增前提插在 `(f : α → ℝ)` 之后）；
3. **项 2–6、8、9**（B）：不动陈述；把 `asnFnhkP22`（等 PackingAuto18 bank）、
   `volSolidTriangleP22`、`eFanP22`/`hypermap1OfFanxP22`/`verticesP22`/
   `edgesP22`/`topologicalComponentYfanP22`/`dartsetLeadsIntoFanP22`、
   `arclength22`（等 PackingAuto1/pack1.hl）列入 def 落地波的需求单，
   落地即按各项 (d) 注记的证明路线填证；
4. **项 10**：划掉 §5.4 PA4 疑点注记，零动作。

---

## 13. `DUUNHOR_concl` — 分级 A′（前提补全型，2026-09-28 增补；流程已授权）

**(a) HOL 裁决**：`reference/flyspeck/text_formalization/packing/Rogers.hl:1682`
（侦察 lane 2026-09-28）：陈述带 `packing V ∧ saturated V`。当前 Lean 陈述
（PackingAuto2.lean:556-558）缺这两前提；HOL 证明第一步（Rogers.hl:1745）即经
`VORONOI_CLOSED_EQ_LEMMA`（Rogers.hl:1256，陈述带 `packing V`）证明 `HD ul = HD vl`
——PA6:837"前提未用"注记与 HOL 原文不符。

**(b) 机器验证状态**：无前提版真伪未验证（可能假、也可能只是不可证）；修复波
第一步先尝试无前提版反例（`barV`/`rogers` 语义下的反例空间待探）。

**(c) 修复方向**：前提补全型——补 `Packing V ∧ saturated V` 与 HOL 对齐；
**连带**：PA6:841 `DUUNHOR` 背引用同步加参（零内容背引用，加参后仍自动变绿）。

**(c′) 消费侧连带（2026-10-08 增补，编排者依本项授权链归档）**：PA2/PA6 侧
（88951853 落地）使 PackingConcl 的弱形镜像 `DUUNHOR_concl_discharged`
（barV-only, sorry）成为孤儿——其 BLOCKED(b) 案由即 "twin 多
`Packing V`/`saturated V` 两前提"。消费侧随上游同步升形为 r2（shape-verbatim
于 `PackingAuto6.DUUNHOR`），弱形全仓零消费者（grep 复核 2026-10-08）；
补丁的 PackingConcl 节由落地 diff 反向归档（先代码后存档，闸门多重集从此
接管），PackingConcl 台账重算 52→46 / 54 / 49 / BLOCKED 9→8 随件。

**(d) 落地路线**：依赖 ROGERS_AFF_DIM_FULL（PA6:763 未证）、POLYHEDRON_VORONOI_LIST
（PA5:1454 未证）、OMEGA_LIST_N_LEMMA（PA5:1502 未证）——详见 PA2:557 原位
NEEDS 注记（commit 8d8d898f）。affDim≤2 退化分支机械（PA6:707 可引），
卡双满维主情形（~770 行，GIANT）。

**(e) 补丁**：修复波起草后存档
`docs/statement-fix-proposals-patches/13-DUUNHOR_concl.patch`，经
STATEMENT-FIX 闸门模式验收（DECISIONS.md 2026-09-28 条）。
5. **项 13**（DUUNHOR_concl，2026-09-28 增补，A′）：先试无前提版反例；补
   `Packing V ∧ saturated V` + PA6:841 背引用同步加参；补丁起草后存档
   `13-DUUNHOR_concl.patch` 走 STATEMENT-FIX 闸门。

---

# 第二轮提案（r2，2026-09-28 增补）

> 第二轮（PA22 r2 四枚 + PA7 两枚 + DUUNHOR + 项 1 复核）。纪律同 R1：零 .lean
> 改动，全部交付 = 本文件增补 + `docs/statement-fix-proposals-patches/` 补丁草案；
> scratch 模块 `ScratchA.lean`（未跟踪，验证后删除）。对照基准：
> `reference/flyspeck` @ `1ce0353`。机器验证：`lake env lean`，ScratchA 最终
> **0 error**（反例 + 修复后陈述全验证；详见各项 (b)）。

## 14'. r2 总表与分级统计

| # | 陈述 | Lean 位置 | HOL 原文 | 偏差性质 | 分级 |
|---|---|---|---|---|---|
| 11 | `facet_rep_uniq` | PackingAuto22.lean:333 | counting_spheres.hl:161 | 弱化定义（facetOfC 缺 ≠∅ 与 aff_dim）| **A**（补 ≠∅ 前提即闭合）|
| 12 | `affine_facet_hyper` | PackingAuto22.lean:564 | counting_spheres.hl:320 | 弱化定义（同上，且需 aff_dim）| **C**（需重移植/定义立项）|
| 13a | `pad2d3d_facet` | PackingAuto22.lean:1275 | counting_spheres.hl:1737 | 弱化定义（结论侧 facetOfC 计数混入 ∅ 与顶点面）| **C**（同上）|
| 14 | `ARG_ORDER` | PackingAuto22.lean:1349 | counting_spheres.hl:1822 | 语义错植（Complex.arg (-π,π] vs HOL Arg [0,2π)）| **A′**（改述 holArg，证明待收口）|
| 15 | `KSOQKWL` | PackingAuto7.lean:787 | Rogers.hl:9588 | 弱化定义（permutes 缺补集逐点固定）| **A′**（补 hpout 前提）|
| 16 | `IVFICRK` | PackingAuto7.lean:796 | Rogers.hl:9929 | **无病**（弱编码下仍真；HOL 的 g 不可移植）| 解除（附 g 重构注记）|
| 1′ | `SUM_INTER` 补丁复核 | LocalAuto38.lean:419 | terminal.hl:233 | — | 维持 **A**|
| 13′ | `DUUNHOR_concl` | PackingAuto2.lean:565 | Rogers.hl:1682 | 前提缺失 | **A′**（补丁已起草）|

**r2 统计：A = 1（项 11），A′ = 2（项 14、15）+ 1（项 13 维持），C = 2（项 12、13a），
解除 = 1（项 16）；另项 1 复核通过（补丁更正后重归修复队列）。**

编号注记：任务书将 PA22 r2 四枚编为 11–14，而 R1 增补项 13（DUUNHOR_concl）
的补丁名 `13-DUUNHOR_concl.patch` 已在 DECISIONS 2026-09-28 登记 —— 编号 13
双占，以文件名全称消歧（`13-pad2d3d_facet.patch` vs `13-DUUNHOR_concl.patch`）。
下文 PA22 r2 的 pad2d3d_facet 记作 **13a** 以免混淆。

结构性结论（r2 立项建议）：`facetOfC`（= faceOfC ∧ f ≠ s）与 `polyhedronC`
（每点在某"真面"内）均系对 flyspeck polytope1.ml 定义的误移植
（HOL `facet_of` = face_of ∧ ~(f = {}) ∧ aff_dim f = aff_dim s − 1；
HOL `polyhedron` = 有限半空间交，H-表示）。这使 14 枚已填 planar-kit 填证
空洞化为真（经 p22_ball_face_contra 的 vacuous 路线）。若修复波纠正定义，
该 14 枚需按 HOL 原文重填。**建议单独立项**（含 ℂ 上 aff_dim 重移植），
本轮不提案定义改动。

## 15'. 项 11 `facet_rep_uniq` — 分级 A（补 c1 ≠ ∅ ∧ c2 ≠ ∅ 前提）

**(a) HOL 裁决**：`counting_spheres.hl:161`：`!(P:real^2->bool) a b1 b2.
polyhedron P /\ c1 facet_of P /\ c2 facet_of P /\ ... ==> (b1 = b2) /\ (c1 = c2)`。
Lean 陈述（PA22:333-339）逐字同义，唯 `facet_of` 被弱化为 `facetOfC`
（= faceOfC ∧ f ≠ s，缺 `~(f = {})` 与 aff_dim 条件）。

**(b) 机器验证（ScratchA §1，0 error）**：反例 P = {0, 1, I}
（`polyhedronC_triangle`：三点集每点为极点，openSegment 27 案例全验），
c1 = c2 = ∅（`facetOfC ∅ P`：faceOfC ∅ 平凡 + ∅ ≠ P），a = 0，b1 = 1，b2 = 2：
`c1 = P ∩ {x | dot2 0 x = 1} = ∅` 同 c2，全部前提可满足而 b1 = b2 假
（`facet_rep_uniq_counter` 端到端编译）。

**(c) 修复补丁**：`11-facet_rep_uniq.patch` —— 补前提
`(h1ne : c1.Nonempty) (h2ne : c2.Nonempty)` + 小学级证明（b1 ≤ b2 ≤ b1 纯由
非空点的支撑不等式推出，不需 face/facet 内容）：`facet_rep_uniq_fixed`
已在 ScratchA §7 端到端编译验证。消费者核查：全树 grep 无 `facet_rep_uniq`
消费点（`facet_rep_uniq_c` 由 facet_rep_spec 另行推导，不受影响）。

**(d) 保真论证**：补的 ≠∅ 恰为 HOL `facet_of` 的 `~(f = {})` 合取支
（aff_dim 支未补 —— 本定理证明不需它，见 (c)；若定义立项落地，本补丁前提
被新 facetOfC 蕴含，陈述自动弱化为 HOL 镜像，无需回滚）。冻结前缀
`theorem facet_rep_uniq (P c1 c2 : Set ℂ) (a : ℂ) (b1 b2 : ℝ) ` 逐字不变。

**(e) 分级：A**（前提补全即闭合 + 零消费者波及 + 证明已机器验证）。

## 16'. 项 12 `affine_facet_hyper` — 分级 C（需重移植，零补丁）

**(a) HOL 裁决**：`counting_spheres.hl:320`：`c facet_of P /\ polyhedron P /(affine hull P = (:real^N)) /\ ~(a = vec 0) /\ P INTER {x | a dot x = b} = c ==>
(affine hull c = {x | a dot x = b})`。Lean 陈述（PA22:564-568）逐字同义，
唯 facet_of/polyhedron 为弱化移植。

**(b) 机器验证（ScratchA §2，0 error）**：反例一
（`affine_facet_hyper_counter`）：P = {0, 1, I}（全维 + polyhedronC），
c = ∅，a = 1，b = −1：P ∩ {x | x.re = −1} = ∅ = c，而 affineSpan ∅ = ∅ ≠
该直线。**反例二（纸面已核）：仅补 c ≠ ∅ 仍假** —— P = {0, 1, I}，
c = {0}（顶点面，facetOfC {0} P ✓），a = 1+i，b = 0：
P ∩ {x | x₁+x₂ = 0} = {0} = c，而 affineSpan {0} = {0} ≠ 该直线。

**(c) 修复评估**：HOL 证明走 AFF_DIM_EQ_AFFINE_HULL（aff_dim c =
aff_dim P − 1 + P 全维 ⇒ 同 hull），本质消费 aff_dim 内容；前提补 ∅ 排除
不足以顶掉顶点面。修复需 ℂ 上 aff_dim + 真 facet_of —— 归入定义立项。

**(d)** 陈述冻结黑名单（假陈述无人可填）。

**(e) 分级：C**（零补丁；`12-affine_facet_hyper.patch` 为裁决存档）。

**(f) DEF-FIX 状态（2026-09-29）：解冻前置已就绪** —— planar 编码定义纠正
（`docs/projects/archive/planar-encoding-fix.md` §2 补丁）已落地：新 `facetOfC` 自带 ≠∅ + `affDimC`
条件、新 `polyhedronC` 为 HOL 镜像，本项陈述在新定义下即真（HOL 镜像）。
仍按 (d) 冻结至重填 kit（affDimC 超平面 kit → §2.3 表）落地后入重填队列
（章程 §3c：中等档，kit 后）。

**(g) 编排者复核（2026-09-29）：反例消解确认，正式转入 kit 波填证队列** ——
两级反例（∅ 面 / 顶点面 {0}）在新 `facetOfC` 的 `affDimC f = affDimC s - 1`
条件下均不可满足（affDimC ∅ = -1 ≠ 1；affDimC {0} = 0 ≠ 1），陈述冻结解除；
填证路线 = (b) 所记 HOL `AFF_DIM_EQ_AFFINE_HULL`，前置件 = affDimC kit（§2.3）。

## 17'. 项 13a `pad2d3d_facet` — 分级 C（需重移植，零补丁）

**(a) HOL 裁决**：`counting_spheres.hl:1737`：`!P n. polyhedron P /(!u. u IN P ==> u$3 = &0) /\ {c | c facet_of P} HAS_SIZE n ==>
{d | d facet_of (IMAGE (dropout 3) P)} HAS_SIZE n`。Lean 陈述
（PA22:1275-1281）逐字同义，但前提侧 FacetOf 为真移植（Polytope.lean，
含 aff_dim），结论侧 facetOfC 为弱化版 —— 计数口径不一。

**(b) 机器验证（ScratchA §3，0 error）**：反例
（`pad2d3d_facet_counter`）：P = {(0:V3)}：polyhedron ✓（六半空间交显式
给出）、hz ✓、{c | FacetOf c P} = ∅（Finite ✓ ncard = 0 ✓ —— FacetOf c P
⇒ c ⊆ {0} ⇒ c = ∅（违 ≠∅）或 c = {0}（affDim 0 ≠ 0 − 1）），
而结论侧 {d | facetOfC d (dropout3P22 '' P)} ∋ ∅（facetOfC ∅
{dropout 0} ✓），ncard ≥ 1 ≠ 0。

**(c) 修复评估**：仅排 ∅ 不够 —— 顶点面混入（n 边形：真 facet n 个 vs
弱计数 n + 顶点数 + 1）；修复需 ℂ 上真 facet_of。归入定义立项。

**(d)** 陈述冻结黑名单。

**(e) 分级：C**（`13-pad2d3d_facet.patch` 为裁决存档；编号 13 双占见 14' 注）。

**(f) DEF-FIX 状态（2026-09-29）：解冻前置已就绪** —— planar 编码定义纠正
（`docs/projects/archive/planar-encoding-fix.md` §2 补丁）已落地：结论侧 `facetOfC` 已含 ≠∅ +
`affDimC` 条件，前提/结论计数口径统一（HOL 镜像），(b) 的 ∅ 混入反例不再成立。
仍按 (d) 冻结至重填 kit（`FACET_OF_LINEAR_IMAGE` ℂ 版，§2.3 表）落地后入重填
队列（章程 §3c：GIANT 档）。

**(g) 编排者复核（2026-09-29）：反例消解确认，正式转入 kit 波填证队列** ——
前提/结论计数口径已随 DEF-FIX 统一（双侧 affDimC 忠实形），(b) 的 ∅/顶点面
混入反例均不可满足；前置件 = `FACET_OF_LINEAR_IMAGE` ℂ 版（§2.3 kit），
GIANT 档顺延波 3。

## 18'. 项 14 `ARG_ORDER` — 分级 A′（改述 holArg，证明待收口）

**(a) HOL 裁决**：`counting_spheres.hl:1822`：`!u h n. ~(u = Cx &0) /(!i. i IN 1..n ==> ~(h i = Cx &0)) /\ (!i j. i IN 1..n /\ j IN 1..n /\ i < j ==>
Arg (h i/ u) < Arg (h j/ u)) /\ h (n+1) = h 1 ==> (!i j. ... ==>
Arg (h (i+1)/h i) <= Arg (h j/h i))`。HOL Arg（Ysskqoy kit）取值 [0, 2π)。
Lean 陈述（PA22:1349-1356）逐字同义但用 `Complex.arg`（取值 (−π, π]）——
与本文件 holArg/ARG_INV_ALT 已批改述同病。

**(b) 机器验证（ScratchA §4，0 error）**：反例
（`ARG_ORDER_counter`）：n = 3，u = 1，h 1 = 1，h 2 = I，h 3 = −1：
前提（Complex.arg 排序 0 < π/2 < π）全真，结论在 (i, j) = (2, 1) 处要求
arg(−1/I) = arg I = π/2 ≤ arg(1/I) = −π/2，假。（n = 2 不构成反例 ——
两对 (i,j) 的结论平凡为等式，首版 n = 2 反例被 scratch 否决后改为 n = 3。）

**(c) 修复补丁**：`14-ARG_ORDER.patch` —— 前提与结论的 Complex.arg 改为
`holArg`（照抄本文件 ARG_INV_ALT 已批改法）。**证明状态**：holArg 版为真
（HOL 原文即该语义）；scratch 草案已完成辅助引理 holArg_mem_Ico / polar_rep
/ arg_cos_sin_I（经 arg_myform + Complex.arg_cos_add_sin_mul_I）/ polar_inj
/ polar_div / holArg_div_polar 中的前四件并编译，主证明 8 分支尚有 ~4 处
rw 对齐未收口 —— **补丁体暂以 sorry 标注，修复波按草案收口后方可过闸第⑤
道；完成前 ARG_ORDER 保持冻结黑名单**（假陈述无人可填）。

**(d) 保真论证**：holArg 即 HOL Arg 的忠实重构（[0, 2π) 语义），改述后
陈述与 HOL 逐字同义；消费者核查：全树无 ARG_ORDER 消费点
（POLYSORT_BIJ2 为 sorry，其 NEEDS 注记按 holArg 语义读）。

**(e) 分级：A′**（改述方向 + 反例已核；证明收口后升 A）。

## 19'. 项 15 `KSOQKWL` — 分级 A′（补 hpout 前提）

**(a) HOL 裁决**：`Rogers.hl:9588`：`!V ul p k. packing V /\ ul IN barV V k /hl ul < sqrt2 /\ p permutes (0..k) /\ rogers V ul = rogers V (left_action_list p ul)
==> p = identity`。HOL `permutes`（permutations.ml:9）=
`!x. ¬(x IN s) ==> p(x) = x`（补集逐点固定）；Lean `permutes`
（PA2:162）= `∀ x, x ∈ s ↔ p x ∈ s`（集合稳定）—— 弱化。

**(b) 反例（结构已核；几何实例化见注）**：p := Equiv.swap (k+1) (k+2)：
0..k 逐点不动 → 弱前提真；ul.length = k+1 时 leftActionList p ul = ul
（PA2:156：各位 i ≤ k 有 p.symm i = i）→ hrog 平凡真；结论 p = refl 假。
HOL 原文下该 p 不满足 permutes（k+1 在补集中被 p 移动）。**机器验证状态**：
p/leftActionList/permutes/rogers-平凡性半边可在 scratch 闭验，barV/Packing/
hl ul < √2 的几何实例化（barV V 0 [0]：V 取 {0, 2e₁, 2e₂, 2e₃}，需 voronoi
胞 affDim = 3 计算）本轮未收口 —— 反例构造完整给出，修复波或黑名单登记时
补机器验证。

**(c) 修复补丁**：`15-KSOQKWL.patch` —— 补前提
`(hpout : ∀ x : ℕ, k < x → p x = x)`（恰为 HOL permutes 的补集固定内容；
Equiv.Perm 类型自带双射 = HOL permutes 的第二合取支）。补后陈述 ≡ HOL 原文。
证明体保持 sorry（闭合需 NOT_ID_IMP_LISTS_NOT_EQ → KSOQKWL_lemma0/1 →
ROGERS_EQ 唯一性链，GIANT；该链 5 枚同病桥的修复波同批处理时照抄本补丁模式）。

**(d) 保真论证**：hpout = HOL permutes 的缺失合取支，补后逐字同义；
不改 `permutes` 定义（改定义波及 PA5/PA7 全部消费点，另立项）。

**(e) 分级：A′**。

**(f) 状态（2026-10-12 用户批准；应用波复核记录）**：复核发现本修复**已随
2026-09-30 batch A 落地**（PA7:2389 `KSOQKWL` 签名已带 `hpout`，文件头注
:42 记 ENCODING-FIX；消费侧 PackingConcl:293 `KSOQKWL_concl_discharged` 与
PA2:5456 孪生（项 25）同步带参）。批准附带的"应用前反例几何实例化机器验证"
前置件**已补齐**（验证车道 /tmp/sf15-verify，exit 0 零 sorryAx）：反例取
更省的合法实例 `k:=0, ul:=[0], V:={0}, p:=swap 1 2`（提案 (b) 的
V:={0,2e₁,2e₂,2e₃} 不再需要）——弱前提全部真证（Packing 单点平凡/barV V 0 [0]
经 voronoi 胞=univ 给 affDim=3/hl=radV{0}=0<√2/permutes 固定 0/leftActionList
平凡相等），结论 p≠refl 与 `¬hpout` 同时机器确立；三条公开定理
`sf15_KSOQKWL_weak_false`/`sf15_counterexample_witness`/`sf15_hpout_blocks`
公理面 = 标准三。验证探针归档
`docs/assets/sf15-ksoqkwl-counterexample-probe.lean`（192 行，可作回归锚：
任何人回退 hpout 即撞机器证伪）。零工作树 diff，无需再走闸。

## 20'. 项 16 `IVFICRK` — 裁决：无病（解除，附重构注记）

**(a) 疑点**：工人报"同编码可疑"。裁决：**假指控不成立，但 HOL 的显式 g
不可移植** —— 弱编码下目标集 T 含补集上任意移动的置换，HOL 的 g ≈
τ(i,k+1)∘σ 不必落入 T。

**(b) 真性论证（纸面）**：弱编码下存在显式修正 g：ψ = (g(i,σ)).symm
分段 —— x ≤ k：σ.symm x + (if i ≤ σ.symm x then 1 else 0)；x = k+1：i；
x ≥ k+2：φ⁻¹(σ(φ x))，φ x = x − 1。三段双射拼合为置换；应用子句经
`(dropIth ul i).getD m = ul.getD (m + (i ≤ m))`（PA2:144，对一切 ul 归纳
可证）+ ψ 在 0..k 的逐点式直接闭合；InjOn/SurjOn 经 i（ψ(k+1) 位）、
σ|_{Icc 0 k}（0..k 位）、σ 尾段（φ 共轭）三分量恢复。全部 Equiv/List
机械题（~250 行，无几何）。**机器验证未做** —— 裁决"无病"为纸面论证，
修复波吃下证明时若发现反例再回滚本裁决。

**(c) 零补丁**（陈述冻结；`16-IVFICRK.patch` 为裁决与 g 重构注记存档）。

**(d)/(e)**：解除（不适用 A/B/C）。

## 21'. 项 1 复核（r2）— SUM_INTER 补丁更正后重归队列

**发现**：R1 草案 `01-SUM_INTER.patch` 的 hunk 头新侧行数误记（27，实际
29），`git apply` 拒绝（patch(1) 可过，但 STATEMENT-FIX 闸门按 git 工具链
验收）。**更正**：同内容经 `git diff` 规范重生成（旧侧行与 LA38@HEAD
415-445 逐字节一致，`--check` 通过），冻结前缀
`theorem SUM_INTER {α : Type*} (A B : Set α) (f : α → ℝ) ` 逐字不变，
唯一 sorry 出现为删除行（净计数 −1）。新证明体另在 r2 scratch 重验编译
（SUM_INTER_fixed）。修复队列顺位不变（第 2 位，项 7 之后）。

## 22'. 项 13（R1 增补）r2 进展 — DUUNHOR_concl 补丁已起草

**(b)-进展**：无前提版反例尝试：构造可行（V = 两簇远距四点组，ul/vl 各为一簇
barV 3 序：8 组 affDim + 两侧共球唯一性 + 半空间分离；机器化估 ~400 行），
超出本轮预算未收口。按 DECISIONS 2026-09-28 授权改走保真对齐：
**`13-DUUNHOR_concl.patch` 已起草**（两文件：PA2:565 陈述补
`Packing V → saturated V`；PA6:592 背引用同步加参 hP hs + 陈旧 docstring
更正 + PA2 原位 NEEDS 注记记录裁决）。**(c)** 补前提后 ≡ HOL 原文；
PA4:1370 等 9 处"缺件"注记与 PA17:275/304、PackingConcl:132 的孪生注记
（TWIN MISMATCH：接口无 packing）由修复波一并复核（孪生
`DUUNHOR_concl_discharged` 为独立 sorry 陈述，不在本补丁范围，注记需同步）。
**(d)** 落地路线不变（GIANT）。**(e)** 闸门验收；零 sorry 净变化。

## 23'. r2 执行顺序建议（修复波）

1. **项 11**（A，补丁 11）：前提补全 + 证明已验证，第 1 顺位；
2. **项 15**（A′，补丁 15）：前提补全（证明体 GIANT 另行）；
3. **项 13**（A′，补丁 13-DUUNHOR_concl）：两文件前提补全（证明体 GIANT 另行）；
4. **项 14**（A′，补丁 14）：改述 holArg —— **须先按 scratch 草案收口证明**
   （gate ⑤），收口前不动；
5. **项 12、13a**（C）：等"planar 编码定义纠正"立项（facetOfC/polyhedronC/
   ℂ-affDim），立项前冻结黑名单；
6. **项 16**（解除）：零动作；PA7 若吃 IVFICRK 证明，按 16-patch 注记重构 g。

---

# 第三轮提案（r3，2026-09-28 增补）

> LA38 `tau3_taum` 陈述补陈（officer lane；立项依据 `docs/e2e-debt-map.md:31`
> B 表行）。纪律同前：**零 .lean 改动**，交付 = 本文件增补 +
> `docs/statement-fix-proposals-patches/17-tau3_taum_dist_bound.patch`（可贴性
> `git apply --check` 已验；本 lane 只读纪律未跑 lake，编译验收留给修复波）。
> 对照基准：`reference/flyspeck` @ `1ce0353`；`lean/scripts/local/terminal.hl`
> 为孪生副本（548-615 行已核对与 flyspeck 侧逐字一致）。

## 24'. 项 17 `tau3_taum_d`/`tau3_taum_dfun` — 分级 A′（前提补全型：补 6 个 box-bound 合取支）

| # | 陈述 | Lean 位置 | HOL 原文 | 偏差性质 | 分级 |
|---|---|---|---|---|---|
| 17 | `tau3_taum_d` / `tau3_taum_dfun` | LocalAuto38.lean:1338 / 1358 | terminal.hl:549-567 / 584-602 | 前提缺失（缺 `2 ≤ a01 ∧ 2 ≤ a12 ∧ 2 ≤ a02 ∧ b01 ≤ 3.62 ∧ b12 ≤ 3.62 ∧ b02 ≤ 3.62` 六合取支 ⇒ `2 ≤ dist` 不可导） | **A′**（补陈后证明转机械；收口后升 A） |

### (a) HOL 裁决

`reference/flyspeck/text_formalization/local/terminal.hl:549-567`
（`tau3_taum_d`；`tau3_taum_dfun` 同构在 584-602，f-修正版）：陈述为

```
!d a01 a12 a02 b01 b12 b02.
  (&2 <= a01 /\ &2 <= a12 /\ &2 <= a02 /\ b01 <= #3.62 /\
   b12 <= #3.62 /\ b02 <= #3.62 /\        (* ← terminal.hl:550（dfun :585）*)
   (!y1..y6. &2 <= y1 /\ y1 <= &2*h0 /\ ... /\ &0 <= delta_y ...
             ==> d <= taum y1..y6)) ==>
  (!v0 v1 v2. &2 <= norm v0 /\ norm v0 <= &2*h0 /\ ... /\
   a01 <= dist(v0,v1) /\ dist(v0,v1) <= b01 /\ ... ==> d <= tau3 v0 v1 v2)
```

六合取支是 **h 之外对 box 参数自身的独立前提**。B 表"缺 `2 ≤ dist` 下界"即其
效果：只有经 `2 ≤ a01` + `a01 ≤ dist ≤ b01` + `b01 ≤ #3.62` 才导出
`2 ≤ dist ≤ 3.62`。HOL 证明（terminal.hl:570-578；dfun 605-614）第一步
`GMATCH_SIMP_TAC tau3_taum` 即消费 `tau3_taum` 的 `2 ≤ dist` ∧ `≤ #3.62` 前提
（ball_annulus 成员经 `Fnjlbxs.in_ball_annulus` + REAL_ARITH 出自 norm 界），
随后把 h 用于 y = (norm v0, norm v1, norm v2, dist(v1,v2), dist(v0,v2),
dist(v0,v1))，deltaY ≥ 0 侧条件走 DELTA_Y_POS_4POINTS + DIST_L_ZERO——
六合取支是该证明的承重墙。

### (b) 误移植诊断

Lean r1 移植（LA38:1338-1371）把 h 原样搬来，但**丢了六合取支**（弱化方向：
假设侧）。后果链：现陈述下 a01 可取 0 ⇒ `2 ≤ dist v_i v_j` 不可导 ⇒ 已
DISCHARGED 的 `tau3_taum`（LA38:1275）及其底座 `p38_tau3_eq_taum`/
`p38_dihV_eq_dihY`（LA38:1244/1119；`2 ≤ dist < 4` 强制 ups_x > 0）对该定理
全部不可用——平行楔形退化（如 v0 = v1 时 dihV 出 π/2-junk ≠ dihY 的 junk
口径）卡死；原位 sorry 注记（LA38:1350-1354）如实记录为 statement-level
question。**真伪**：未机器收口。纸面可见的为假风险：取 a01 = b01 = 0（钉死
dist v0 v1 = 0）、‖v0‖ = 2、v2 = −v0，h 的 box 在 (2,2,2,4,4,0) 处
delta_y = 0 ≥ 0 激活，迫使 d ≤ taum 2 2 2 4 4 0（dihY-junk 口径），而结论在
退化点比对 tau3 的 dihV-junk 口径——两个 junk 口径无理由对齐，选合适的 d 即
可能为假；机器化收口（及"可能只是不可证而非假"的排除）超出本 lane 预算，
补陈后此问题自然消失（box 被六合取支钉进 [2,3.62]，退化点不可达）。

### (c) 提案陈述全文（补丁 17 落地后）

```lean
/-- HOL `tau3_taum_d` (terminal.hl:549-567).  The six box-bound conjuncts
`&2 <= a01 /\ &2 <= a12 /\ &2 <= a02 /\ b01 <= #3.62 /\ b12 <= #3.62 /\
b02 <= #3.62` (terminal.hl:550) are part of the HOL antecedent; they force
`2 ≤ dist ≤ 3.62` on all three edges, so the box-to-vector transfer rewrites
via `tau3_taum`.  STATEMENT-FIX item 17 (2026-09-28): the r1 port dropped
them, leaving `2 ≤ dist v_i v_j` underivable and the transfer blocked on
degenerate parallel wedges (docs/statement-fix-proposals.md item 17). -/
theorem tau3_taum_d (d a01 a12 a02 b01 b12 b02 : ℝ)
    (h1 : 2 ≤ a01) (h2 : 2 ≤ a12) (h3 : 2 ≤ a02)
    (h4 : b01 ≤ 3.62) (h5 : b12 ≤ 3.62) (h6 : b02 ≤ 3.62)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 → y1 ≤ 2 * h0 → 2 ≤ y2 → y2 ≤ 2 * h0 → 2 ≤ y3 → y3 ≤ 2 * h0 →
      a01 ≤ y6 → y6 ≤ b01 → a12 ≤ y4 → y4 ≤ b12 → a02 ≤ y5 → y5 ≤ b02 →
      0 ≤ deltaY y1 y2 y3 y4 y5 y6 →
      d ≤ taum y1 y2 y3 y4 y5 y6)
    (v0 v1 v2 : V3) :
    2 ≤ ‖v0‖ → ‖v0‖ ≤ 2 * h0 → 2 ≤ ‖v1‖ → ‖v1‖ ≤ 2 * h0 → 2 ≤ ‖v2‖ →
    ‖v2‖ ≤ 2 * h0 → a01 ≤ dist v0 v1 → dist v0 v1 ≤ b01 →
    a12 ≤ dist v1 v2 → dist v1 v2 ≤ b12 → a02 ≤ dist v0 v2 →
    dist v0 v2 ≤ b02 → d ≤ tau3 v0 v1 v2 := by
  intro _ _ _ _ _ _ _ _ _ _ _ _
  sorry -- 填证路线见原位注记（tau3_taum + p38_deltaY_pos_4，机械题）

theorem tau3_taum_dfun (d : ℝ) (a01 a12 a02 b01 b12 b02 : ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (h1 : 2 ≤ a01) (h2 : 2 ≤ a12) (h3 : 2 ≤ a02)
    (h4 : b01 ≤ 3.62) (h5 : b12 ≤ 3.62) (h6 : b02 ≤ 3.62)
    (h : ∀ y1 y2 y3 y4 y5 y6 : ℝ, … d + f y4 y5 y6 ≤ taum y1 y2 y3 y4 y5 y6)
    (v0 v1 v2 : V3) :
    … → d + f (dist v1 v2) (dist v0 v2) (dist v0 v1) ≤ tau3 v0 v1 v2
```

（dfun 版 h 的 9 条箭头前提与结论逐字同 r1 现状，唯一改动 = 同样插入 h1-h6；
补丁含全文。）命名注：h1-h6 六个命名前提 = HOL 六合取支的 currying（语义同
合取），排版照本文件 `taustar_taum`/`taustar_taum_dfun`（LA38:1374-1376/
1409-1411，同一 HOL 合取支块的既有移植）先例；`theorem` 冻结前缀
`tau3_taum_d (d a01 a12 a02 b01 b12 b02 : ℝ)` 及 h/向量侧全部逐字不动。

### (d) 消费面影响清单（全库 grep `tau3_taum_d`/`tau3_taum_dfun`，排除 .lake/.git/reference/certificates）

1. **零直接消费点**：全库仅定义处（LA38:1338、1358）、文件头 LEDGER 提及
   （LA38:78）、dfun NEEDS 注记回指（LA38:1370）、B 表立项行
   （e2e-debt-map.md:31）。加参不破坏任何调用。
2. 间接消费链（收益面，非破坏面）：
   - `taustar_taum`（LA38:1374，sorry）：HOL 证明 terminal.hl:637
     `MATCH_MP_TAC tau3_taum_d`——补陈后 Lean 同路线可把自身 h1-h6 传入；
   - `taustar_taum_dfun`（LA38:1409，sorry）：HOL terminal.hl:679 同上；
   - `empty_3T2`（LA38:2901，sorry，吃 `main_nonlinear_terminal_v11`）的
     BLOCKED 注记（LA38:2904）"taustar_taum (tau3_taum hole)" 即经此链——
     这就是 B 表"经 main_nonlinear_terminal_v11 合取项间接"的实指；
   - LocalAuto23:39/308 的 `taustar_taum_dfun` bridge 注记（v39/BB 侧）不受
     本补丁影响，无需改。
3. 上游依赖不受影响：`tau3_taum`（LA38:1275）、`p38_dihV_eq_dihY`（1119）、
   `p38_upsX_pos_box`（957）、`p38_deltaY_pos_4`（1052）、
   `p38_tau3_eq_taum`（1244）均已 DISCHARGED，补丁不触碰。
4. **B 表同步**：e2e-debt-map.md:31 由修复波落地后注记"已补陈（提案项 17）"。

### (e) 风险

1. 加参使定理变弱（HOL 忠实方向）：未来消费者须自供六合取支；在
   main_nonlinear_terminal_v11/LP 合取项语境它们自带（`taustar_taum` 的
   h1-h6 即同款），无实质风险。
2. 陈述改动须走 STATEMENT-FIX 闸门（DECISIONS 2026-09-28 条）；`git apply
   --check` 已过，编译验收（0 error）待修复波——本 lane 禁跑 lake。
3. sorry 净变化 0（两陈述各保其 sorry；原位注记改为机械填证路线，填证与
   HOL 证明 terminal.hl:570-578 同构，风险极低）。
4. 若修复波在填证时发现意外（理论上为纯假设推演），回滚窗口 = 补丁仅动
   1337-1371 两个陈述块，revert 即净。

### (f) 状态：草案待审（2026-09-28 officer lane 产出；补丁可贴性已验，
编译与闸门验收待修复波）。

### (g) 状态（2026-10-12 用户批准；应用波复核记录）：批准见
docs/projects/archive/sf-decision-batch-2026-10-12.md 项 17。应用波（LocalAuto38
车道）复核发现本修复**已于 2026-09-29 落地且超出本提案**：陈述补陈随
`5bcb4e11`（STATEMENT-FIX 闸 PASS，h1-h6 与 (c) 节提案陈述逐字一致），
两定理证明体已随 `8939b636` 填成真证零 sorry（ballAnnulus 成员 + `tau3_taum`
重写 + `h` 消费于 y=(‖v0‖,‖v1‖,‖v2‖,dist v1 v2, dist v0 v2, dist v0 v1) +
`p38_deltaY_pos_4 0 v0 v1 v2` 供 deltaY 支；sorry 净 −2，闸 PASS；现树
LocalAuto38.lean:1492-1574）；全树零直接消费点复核依旧成立；
`lake build Kepler.Text.LocalAuto38` 自然退出 0 error（2026-10-12）。
**工作树对该文件零 diff——无重起草应用波可执行，STATEMENT-FIX 闸无需再走**；
补丁 17-tau3_taum_dist_bound.patch 转历史存档（头注已核账），不可再贴。

## merge-ineq-bank. 波 0 ——银行结构化 + eta_y 重指向（Merge_ineq 通道章程 §2）

> 立项与章程：`docs/projects/archive/merge-ineq-channel.md`（编排者审定通过，见章程末
> "附：编排者审定意见"）。本条目为波 0（陈述级）的**执行存档**：补丁已于
> 2026-09-29 落地 `lean/Kepler/Text/PackingAuto21.lean`（下称 PA21），构建
> 与台账验收实测见 (f)。补丁正文不再重复誊写，以章程 §2.1/§2.2 为准。

### (a) HOL 裁决

- **银行 def**：merge_ineq.hl:118-134——`packing_ineq_data` =
  `has_flypaper_tag ["UKBRPFE";"BIEFJHU";"OXLZLEZ";"TSKAJXY"] ∧ ¬is_ox3q1h`
  对 Ineq 数据库的全库过滤合取；`mk_pack_nonlinear` 把合取注册为常量
  `pack_nonlinear_non_ox3q1h`，`get_pack_nonlinear_non_ox3q1h` 按名投影。
  全量 81 条（IdLists.lean:43-126 + :128 `rfl`）；TSKAJXY 消费切片 19 条
  （`tsk_required_ineq`，TSKAJXY3.hl:2240-2249），逐条 idv/box/结论见章程
  §1.2 表（cell3 组 7 + tsk 组 10 + grk 组 2；grk 组定义锚点 =
  ineq.hl:1520-1535/:1537-1552）。
- **eta_y**：sphere.hl:131-135，`eta_y y1 y2 y3 = eta_x (y1²) (y2²) (y3²)`，
  `eta_x = sqrt(x1·x2·x3/ups_x …)`。忠实体在树内：
  `IneqClosureDefs.lean etaY`（经 etaX/upsX，逐字）。
- **陈述级结论**：19 条切片在 PA21 以箭头形逐字材料化（HOL `Sphere.ineq`
  区间蕴含包装按章程 §6.2 决策不移植，直接展平为
  `∀ y1…y6, a_i ≤ y_i → y_i ≤ b_i → … → concl`）；x-空间三条目
  （GXSABWC DIV/delta_x4/eulerA）变量名用 x。

### (b) 诊断

PA21 原三枚 def-sorry 不透明阻断收口链：`eta_y := sorry`（PA21 旧 :131）、
`tsk_hyp := sorry`（旧 :142，HOL = 10 条合取）、
`pack_nonlinear_non_ox3q1h := sorry`（旧 :147，81 条银行）——三者使
TSKAJXY:1428 的 0/3/4 臂无法从银行投影任何前提，且 `eta_y` 不透明使
PA25 的 ETA_Y_* 填证队列（RADV_ETAY、ETA_Y_POS_LE_ALT 等）整体冻结。

### (c) 补丁正文

= 章程 §2.1（eta_y 一行重指向 `:= etaY y4 y5 y6` + import
`Kepler.Text.IneqClosureDefs`）+ §2.2（19 条 `bank_*` def + 三组显式合取
`cell3_bank`/`tsk_bank`/`grk_bank` + `pack_nonlinear_rest := sorry` 62 条
单叶挂账【`-- NEEDS: G4 主案（Merge_ineq 章程 §2.2/附则1）` 注记入账】+
`pack_nonlinear_non_ox3q1h := cell3_bank ∧ tsk_bank ∧ grk_bank ∧
pack_nonlinear_rest` + `tsk_hyp := tsk_bank` + 具名投影引理三枚
`proj_cell3_bank`/`proj_tsk_bank`/`proj_grk_bank`）+ 骨架两枚
（`GRKIBMP : grk_bank → GRKIBMP_concl`、`cell3_from_ineq_thm :
cell3_bank → cell3_from_ineq`，体 `sorry -- MERGE-INEQ: <HOL 锚点>
merge_ineq.hl:3794-3816 / :3507-3745`；**未接** :1428 臂，0/3/4 臂保持
原 sorry，防假绿）。落地新增配套 def 两枚：`eulerAX`
（sphere.hl:830-833 逐字）、`gamma2x1DivAV2`（nonlin_def.hl:346-347
promote1_to_6 形）；`gamma3fXDivSqrtdelta` 章程时点判缺、实测已由
IneqClosureDefs:441 忠实承载，直接复用（比章程少一枚新 def）。

### (d) 消费面

= 章程 §3：`pack_nonlinear_non_ox3q1h` 全部 76 处消费（PA21 3 + PA25 ~70 +
PackingConcl 1 + Assembly 2）零改动——换体不改常量类型，无任何
unfold/rw 触及（§2.3 逐条论证；机器落点 = PA25:3704
`exact TSKAJXY V X hnl …` 在换体后重构建绿，实测见 (f)）。
`eta_y`/`tsk_hyp`/`tsk_hyp_new`/`TSKAJXY_034` 等消费点同理零改动。

### (e) 风险

1. **执行期实证缺陷（已处置）**：章程 §2.1/§3d 断言 import
   IneqClosureDefs "无环、无名冲突"只在 PA21 闭包内实测；PA25 = PA18 ∪
   PA21 闭包，而 IneqClosureDefs:656 与 PackingAuto18:183 同在
   `Kepler.Text` 声明 `arcLength`，import 即报
   `environment already contains`（PA25/PackingConcl/Assembly 全链红）。
   经全库 top-decl 相交实测，冲突面**仅此 1 名**；经用户授权（2026-09-29
   波 0 会话），IneqClosureDefs 内 `arcLength → arcLengthICD`（同文件
   def + 内部引用 + `#print axioms` 行，~12 处；该模块彼时全库零
   importer，外部零波及；PA18 侧及其消费者 LA1/LA25/LA29 不动）。
   教训：import 级冲突面应按**全链消费模块**（PA25/Assembly 的附加
   import 集）相交复查，不能只查直接受益文件。
2. 62 条挂账叶 `pack_nonlinear_rest` 为单叶 sorry：PA25 的
   IXPOTPA/TXQTPVC/TEWNSCJ_MERGED、JSP_BOUNDS 等将来填证向其取前提，
   最终由 G4 主案拆单（路线 A′ 既定）；拆单前 TSKAJXY 链透传债不变。
3. 折算登记（statement-fidelity 附录口径）：①合取顺序 = 消费组序而非
   81 条前插序；②62 条并入单叶；③`Sphere.ineq` 包装不移植、条目展平为
   箭头形；④`Real.sqrt 8`/`2.8^2`/十进制字面量按 §6.1 内联口径。
4. 波 3 前禁接 ：1428；`GRKIBMP`/`cell3_from_ineq_thm` 两骨架对
   TSKAJXY 的 `#print axioms` 无新增影响（未被 capstone 引用）。

### (f) 状态：章程已审定，本条目为执行存档（2026-09-29 波 0 落地）。
验收实测：`lake env lean` PA21 0 error；`lake build Kepler.Text.PackingAuto21`
/ `Kepler.Text.PackingAuto25` / `Kepler.Text.PackingConcl` 三构建退出码
全 0（PA25 零适配回归成立）；sorry 台账净 +0（eta_y/tsk_hyp/
pack_nonlinear_non_ox3q1h 三枚 def-sorry 消失，pack_nonlinear_rest +
GRKIBMP + cell3_from_ineq_thm 三枚新增，全带 `-- MERGE-INEQ:` 标签；
PA21 声明级 sorry 37 → 37）；:1428 臂与六条冻结陈述零改动。

## 18. `grutoti_volD_pos` — 分级 A′（前提补全型：补 `hne : u0 ≠ u1`）
（2026-09-29 GT-2 填证 lane 产出；任务书授权走 STATEMENT-FIX 文档通道，
**PA23 冻结陈述零改动**——应用需编排者凭用户裁决走 GATE_MODE=STATEMENT-FIX。）

### (a) HOL 裁决

GRUTOTI.hl 全文只有一条定理 `GRUTOTI1_concl`（:48-58），其前提显式带
`~(u0 = u1)`；`grutoti_volD_pos` 对应内容是 `prove_by_refinement` 巨块
（:60-8001，636 个 NEW_GOAL 无显式子引理）末段的子目标 `&0 < vol D`
（:7983-8000，经 `VOLUME_CONIC_CAP` 消元），其证明上下文含
`~(u0 = u1)`。故 HOL 侧该断言**从来是在 `u0 ≠ u1` 下陈述的**。
`VOLUME_CONIC_CAP` 源在 flyspeck_multivariate.ml（本地 reference 树无源，
docs/scouts/grutoti-scout.md §5.1），无法逐字对照；但 Lean 侧 GT-1 已落地的
`ConicCapVolume.volumeConicCapPos`（kernel 验证的帽体积公式正性件，
:961）携带同样的 `hne : v0 ≠ v1` 前提，与退化情形一致：
`ConicCapVolume.ccv_conicCap_empty`（:154，已证）机器见证
`ccvConicCap v0 v0 r a = ∅`，故 `vol = 0`，冻结陈述在 `u1 = u0` 时
**假**（PA23:307-314 诚实注记在案；反例 = 该 empty-lemma + `volume`
对 ∅ 取 0，一句话反例，机器可核）。

### (b) 诊断

`grutoti_volD_pos` 是骨架作者重构出的 private 里程碑（非 HOL 逐字移植），
签名漏抄了 `u0 ≠ u1`；调用点 `GRUTOTI`（PA23:334-339）上下文里有 `hne`
（GRUTOTI 陈述自带），改签名后调用点只需补传一参。

### (c) 修复补丁

`docs/statement-fix-proposals-patches/18-grutoti_volD_pos.patch`。
唯一实质改动三处：① 头部加 `import Kepler.Text.ConicCapVolume`
（ConicCapVolume 只 import Geom + PA2，无环；与 PA23 现有 import 集零撞名，
GT-2 lane 已实测）；② `grutoti_volD_pos` 补前提 `(hne : u0 ≠ u1)`，
体由 `sorry` 换为一行 `volumeConicCapPos hr hd hd1 hne`
（`grutotiConicCap` 与 `ccvConicCap` 同为
`Metric.closedBall v0 r ∩ rconeGt v0 v1 a`，defeq 直取）；③ capstone 调用点
补传 `hne`。**补丁可贴性已验**：patched 变体整文件
`lake env lean` 0 error，`declaration uses 'sorry'` 5 → 4（volD_pos 的
sorry 断流），capstone 其余四 giant 照旧挂账。新陈述全文：

```lean
private theorem grutoti_volD_pos (u0 u1 : V3) (r d : ℝ) (hr : 0 < r) (hd : 0 < d)
    (hd1 : d < 1) (hne : u0 ≠ u1) : 0 < volume.real (grutotiConicCap u0 u1 r d) :=
  volumeConicCapPos hr hd hd1 hne
```

### (d) 消费面

全树 grep：`grutoti_volD_pos` 零外部消费者（PA23 零 importer，
PackingConcl 不经 PA23 走线，docs/scouts/grutoti-scout.md §0.2），唯一调用点是同文件
capstone `GRUTOTI` 内一处（补丁 ③）。属 GT-2/GT-3/GT-4 收口时
`GRUTOTI1_concl_discharged` 断流链的前置件。

### (e) 风险

1. patch ③ 处 `hne` 在 `GRUTOTI` 的 intro 序里已存在（PA23:330
   `intro V u0 u1 e hs hp hu0 hu1 hne hhl he`），补传即可，无舍入风险。
2. `import Kepler.Text.ConicCapVolume` 进 PA23 后，未来任何 lane 给 PA23
   加 importer 时 ConicCapVolume 的传递闭包一并入链——其闭包
   （Geom/WedgeVolume 等）全零 sorry，无新增透传债。

### (f) 状态：草案待审（2026-09-29 GT-2 lane 产出；补丁可贴性已验，
编译 0 error；应用待编排者 GATE_MODE=STATEMENT-FIX）。

### (g) 状态（2026-10-12 用户批准；应用波复核记录）：批准见
docs/projects/archive/sf-decision-batch-2026-10-12.md 项 18。续作车道（PA23）复核
发现本修复**已随 `54fe4ee2`（2026-09-30，用户批准 2026-09-30）应用落地**，
(f) 的"草案待审"状态行已过时：机器实证——以 54fe4ee2^ 为基 `git apply`
本补丁成功，且应用产物与 54fe4ee2 树的 PackingAuto23.lean **逐字节一致**
（对现树 `git apply --check` 拒贴，真因是修复已在树而非行号漂移）。现树
PA23:6386-6388 `grutoti_volD_pos` 已带 `(hne : u0 ≠ u1)`、体 =
`volumeConicCapPos hr hd hd1 hne`（零 sorry），capstone 调用点 PA23:6407
已补传 `hne`，`import Kepler.Text.ConicCapVolume` 已在（PA23:205）；
全树零外部代码消费者复核依旧成立（ConicCapVolume 两处提及均为 docstring；
其后 GT-3d/e/f、SF 28/29/31/32/33 诸波均在该基线上继续演进，本修复无再
应用面）。`lake build Kepler.Text.PackingAuto23` 自然退出 0 error
（2026-10-12）。**工作树对该文件零 diff——无重起草应用波可执行，
STATEMENT-FIX 闸无需再走**；补丁 18-grutoti_volD_pos.patch 转历史存档
（头注已核账），不可再贴。

## 附：GT-2 lane 同批侦察发现（未立项，供编排者定夺）

**`grutoti_sum_volD`（PA23:283-289）冻结签名缺 `Packing V`/`saturated V`**：
第一合取支 `(grutotiEdgeCells V e).Finite` 对一般 `V` 为假——反例形状：
`V = {u0,u1} ∪ 无穷多个互距 ≥ 2 的远处 generic 点`（不需 saturated），
每四个点构成的 barV V 3 表的 `mcell 4` 胞都含 `e ∈ edgeX V X`，族无穷。
修复 = 补 `hp hs` 前提（正路 = FINITE_EDGE_X2，已填）＋（第二合取支）
region 覆盖假设——见 PA23:279-303 NEEDS 注记，属 GT-3/GT-4 协同件，
非单陈述修复可收口，故未单独立项、只在此登记。

## 19. PA21 `LEFT_ACTION_LIST_1_PROPERTIES_ALT` 缺 tail-fixedness 假设（为假）

### (a) HOL 出处：TSKAJXY3.hl:1694（HOL `LEFT_ACTION_LIST_1_PROPERTIES`，marchal3 本体；PA14:785 正本按 PA10 编码裁定带 tail-fixedness）。缺陷：

PA21 冻结陈述 `LEFT_ACTION_LIST_1_PROPERTIES_ALT`（:1694 附近）缺
`hfix : ∀ j ≥ 2, p j = j`（01-交换须固定 tail）。PA14 落地波
（2026-09-30，`9c792954`）在 PA10 编码裁定下证得**带此假设**的版本
（PA14:785，sorry-free）：无 tail-fixedness 时 barV/mxi 保持性对 junk-slot
反例为假。

### (b) 修复（执行版 = DEDUP，2026-09-30 LA38-wrapper lane 落地）

执行方式较原案更强：PA14 正本（含 `hfix`，sorry-free）经 PA17→PA14 已入
PA21 传递闭包，故**直接删除 PA21 的两枚同名 sorried 孪生**
（`LEFT_ACTION_LIST_1_PROPERTIES_ALT`/`MCELL2_PERMUTE_01`，删除前 verified
与 PA14 逐字同 statement——缺陷陈述不再存在，接口由 PA14 修正正本承担；
`MCELL2_VOL` 消费点无感切换上游真证）。同波附带 `GAMMAX_GAMMA2_X`
sorry→真证（普通填充，非陈述变更）。本 patch 为执行后实际 diff 的归档。

### (c) 状态：**已应用（执行版 DEDUP，见 (b)）**（2026-09-30 用户批准；
中途 LA38-wrapper lane 发现删除孪生强于补前提，编排者核 verified 同
statement 后采纳；patch = 执行后实际 diff 归档；闸走
GATE_MODE=STATEMENT-FIX）。

## 20. PA14 `QZKSYKG1` 弱 permutes 编码下为假（junk-slot 反例）

### (a) HOL 出处：QZKSYKG.hl（HL `QZKSYKG1`，k≤3 案；HOL-Light `permutes` 为 complement-fixing，`p permutes 0..(k-1)` 即 `∀ j ≥ k, p j = j`，PA10:183 已裁定）。缺陷：

`QZKSYKG1`（PA14:900）k≤3 情形在按点弱 `permutes` 编码下**陈述为假**
（junk-slot 反例；HL 本体隐含 tail-fixedness，PA10 已裁定为编码前提）。

### (b) 修复

冻结陈述补 tail-fixedness 前提（PA10 式 `∀ j ≥ k, p j = j` 或等价
ENCODING-FIX 注记）；k=4 情形另需 YIFVQDV_1 巨人（与陈述修复正交）。

### (c) 状态：**已应用**（2026-09-30 用户批准）。消费面补充：PA17 的
forward shim `qzksykg1_p17`（:234，私有转发件，无真实调用点——唯一提及在
sorry 掉的 AJRIPQN docstring）同步透传 `hfix`，随本项一并提交。
教训：consumer 扫描输出被 head 截断导致首轮漏查 PA17 调用点，闸门链构建
抓出（四连挂稳定复现）。

## 21. PA23 `grutoti_cell_vol` 冻结签名缺边胞前提（GT-3b/c 波立案）

### (a) HOL 出处：TSKAJXY3.hl §D–§H（`grutoti_cell_vol` 全部四臂均在
边胞语境 `e ∈ edgeX V X` 下运行）；缺陷：Lean 冻结签名缺该前提，
k=0,1 计数臂（需 `p23_edge_cell_k_ge_two`）与 k=4 退化闭合无法消费。

### (b) 修复

签名补 `(he : e ∈ edgeX V X)` 型前提（与 ②sum_volD/③pivot 的
Packing/saturated/region 前提同批走）；供给语境 = pivot 填充波。
k=2 核走 `volumeConicCapWedge` + mcell2 形；k=3 走 `AZIM_COMPL_EXT`
(PA6:2107)；k=4 需 grutoti_region 极值数据。

### (c) 状态：**草案待审**（2026-09-30 GT-3b/c 波立案 `11 私件已落
（公理全净），cell_vol 退化臂已内联闭合；应用建议与 ②③ 及 pivot 填充波
同批，待用户拍板）。

### (d) 状态（2026-10-12 用户批准；应用波复核记录）：批准见
docs/projects/archive/sf-decision-batch-2026-10-12.md 项 21。续作车道（PA23）复核
发现本修复**已随 `3aef75fa`（2026-09-30，用户已批准，GATE_MODE=STATEMENT-FIX
过）应用落地**——签名补 `(he : {u0, u1} ∈ edgeX V X)`（执行形把 (b) 节
`e ∈ edgeX V X` 具象为 `{u0,u1} ∈ edgeX V X`，与 (a) 节 §D–§H 边胞语境
等价）；同日 `2bc2134c` 修正 binder 换序（`(X : Set V3)` 提到 `he` 之前——
autoImplicit 下 `he` 类型里的 X 曾炼成哑变量致前提空转；SF 28/29 立案随该波
记档）。机器实证：归档补丁 21-pa23-cellvol-edgeX.patch 即 `2bc2134c` 执行版
diff——patch index 行 `346893c1..935add32` 与 `git rev-parse` 取自
3aef75fa / 2bc2134c 两 commit 的 PA23 blob 逐一对上（3aef75fa 的 PA23 blob
= 2bc2134c^ 同 blob，中间 commit 未触 PA23），以 346893c1 为基 `patch -p1`
应用产物与 935add32 **逐字节一致**；对现树 `git apply --check` 拒贴，真因是
修复已在树而非行号漂移。现树 PA23:4309-4312 前提面就位（X 在 he 前）；前提
面后由 SF 28/29 续补（hp/hw1/hw3/hw4/hjunk），k=2/3/4 本体已随 GT-3f 收口
（`0c0df90b`，本体 sorry 3→0）。`lake build Kepler.Text.PackingAuto23`
自然退出 0 error（2026-10-12）。**工作树对该文件零 diff——无重起草应用波
可执行，STATEMENT-FIX 闸无需再走**；补丁转历史存档（头注已核账），不可再贴。

## 22. PA22 `ARG_ORDER` 用 `Complex.arg`（值域 (−π,π]）而 flyspeck 依赖 [0,2π) 的 `Arg`——为假

### (a) HOL 出处：Ysskqoy `Arg`（[0,2π)）；缺陷：冻结陈述用 `Complex.arg`
（主值域 (−π,π]），序关系被 2π 折叠破坏。反例（lane 实测）：u=1、n=3、
h1=e^{−iπ/2}、h2=e^{i(π/2−0.1)}、h3=−1 满足全部假设，但
arg(h2/h1)=π−0.1 > −π/2=arg(h3/h1)，结论不成立。

### (b) 修复

陈述的 `Complex.arg` 抬升为 [0,2π) 值域的 `holArg`（与文件头 ARG_INV_ALT
注记同缺陷类）；下游消费者需同步核查。完整反例已录 PA22 文件内注释。

### (c) 状态：**草案待审**（2026-09-30 PA22 独立清单波发现；应用待用户
拍板 + GATE_MODE=STATEMENT-FIX）。

## 23. PA7:995 `NOT_ID_IMP_LISTS_NOT_EQ` — 分级 A′（补 `hfix`，批 A）

### (a) HOL 出处：flyspeck permutes（Library/perms.ml）为 complement-fixing，
`p permutes Icc 0 k` 即 `∀ j > k, p j = j`；扫雷报告 C2-1（docs/scouts/encoding-risk-sweep.md
§2.1，探针 P1-P3 机器反例）。缺陷：弱编码下 junk 对换 `(k+1 k+2)` 满足全部
前提而结论假（文件内注记自认 unprovable）。

### (b) 修复

补 `hfix : ∀ j : ℕ, k < j → p j = j`（与 SF15/19' 的 `hpout` 同形统一）。

### (c) 状态：**已批准（2026-09-30 用户"SF 批准"），随批 A 应用。**

## 24. PA7:1003 `NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX` — 分级 A′（批 A）

### (a) HOL 出处：同 23（扫雷报告 C2-2，同探针反例）。缺陷：同型弱编码。

### (b) 修复

同 23 补 `hfix`。

### (c) 状态：**已批准，随批 A 应用。**

## 25. PA2:3146 `KSOQKWL_concl`（+ PackingConcl:286 穿透）— 分级 A′（批 A，**延期**）

### (a) HOL 出处：pack_concl.hl:104-105 注册表件（扫雷报告 C2-3，探针反例：
junk 对换下 hrog 平凡真而 p ≠ refl）。缺陷：SF15 补丁只覆盖 PA7:1014 母件，
此孪生漏覆盖。

### (b) 修复

补 `hpout : ∀ x, k < x → p x = x`（SF15 同形）；**消费点穿透扩围（批 A PA7
应用波实测，2026-09-30）**：PackingConcl.lean:292 真实调用
`KSOQKWL V ul p k hP hbar hl2 hperm hrog`，且该 consumer 自身是冻结接口
陈述（无 hpout）——故本项 = PA2:3146 补前提 + **PackingConcl 的
KSOQKWL_concl_discharged 陈述同步补参（自身也要 SF）**+ 调用点加参，三处
同一 patch/同车提交（SF20 的 PA17-shim 教训：consumer 扫描不截断）。

### (c) 状态：**已批准；PA2 正被 DUUNHOR 阶段2 lane 编辑，文件空闲后自动应用。**

## 26. PA5:132 `PERMUTES_TRIVIAL` — 冻结黑名单处置（批 A 同车，不阻塞）

### (a) HOL 出处：pack3.hl:103 语义（permutes↔恒等识别仅在补集固定语义下
为真）；扫雷报告 C2-4（探针 P4：`swap 1 2` 反例）。缺陷：不可加前提修——
陈述本身是 permutes↔恒等的识别件，弱编码下形为假。

### (b) 处置

**冻结黑名单**：陈述不改，sorry 永久记账（"弱编码下不可证，待语义
`permutesHL` 重述波"）；当前零真实消费者（仅 PA14:882 docstring 提及）。

### (c) 状态：**已批准（黑名单选项）。**

## 27. PA22 holArg 四件（`insert_v`:1910 / `poly_sort_fn`:1940 / `POLYSORT_BIJ2`:3196 / `EUSOTYP_simple`:3218）— 分级 M（批 B，**延期**）

### (a) HOL 出处：Ysskqoy `Arg`（[0,2π)）；扫雷报告 §3（语义分叉坐实、反例
待立）：与 SF22 ARG_ORDER 同病——主值域 (−π,π] ≠ 圆序 [0,2π)。

### (b) 修复

与 SF22 同车：统一改述 `holArg`；`poly_sort_fn` 是 def（M/L 档），其三个已证
消费件需同步核查。

### (c) 状态：**已批准；PA22 正被 sloc2/UKBRPFE lane 编辑，文件空闲后与
SF22 同车应用。**

## 28. PA23 `grutoti_cell_vol` 缺窄性前提（k=2/3/4 臂解锁条件）— 分级 A′

### (a) HOL 出处：GRUTOTI.hl §D/§F/§E（per-cell 分析在 region witness
`r = 1/2, d = max c (max d1 d2)` 下运行）；cell_vol 波实测（2026-10-01）：
k=2 对不透明 d 可构造反例形态（a = hl[trunc1]/√2 > d 时 rconeGe 截割正
测度）——"盲填"不可行。

### (b) 修复

二选一：(i) 签名补窄性前提（`d ≥ d1`/`d ≥ d2`/`r ≤ r1` 型，随 region
witness 供给）；(ii) 沿 `grutoti_region` 的 witness 重述（region 已闭合，
同文件私有可直用）。配套：region docstring DEVIATIONS 注记的极值数据
（f1/f2>0）需随此项导出。

### (c) 状态：**已应用（2026-10-08 GT-3e 波；2026-10-01 三连批 28/29/30）**。
前提落地：`hp : Packing V`（k=2 反锥 packing 距离）、`hw1 : hl [u0,u1]/√2 ≤ d`
（k=1/2 楔窄性）、`hw3/hw4`（k=3/4 far-face 距离 + 锥-扇形不交，带
¬nullSet (mcell k V vl ∩ D) 门，族 = barV V 3 vl ∧ truncateSimplex 1 vl =
[u0;u1]）。k=0/1 计数臂与退化/null 臂已闭；k∈{2,3,4} 楔恒等式本体为结构化
sorry（消费端 kit 全部 banked 零错，见 PA23 GT-3e lane）。

## 29. PA23 `grutoti_cell_vol` ε-junk 角（cellParams 逆序表）— 分级 A′

### (a) HOL 出处：HL per-cell 分析天然携带 per-cell 前提；cell_vol 波发现：
无效 witness（如参数表逆序 [u1;u0,…]）时 `dihX` 读 junk 值——**潜在
frozen-false 角**。

### (b) 修复

签名加 `truncateSimplex 1 (cellParams V X).2 = [u0, u1]` 型前提封角。

### (c) 状态：**已应用（2026-10-08 GT-3e 波；2026-10-01 三连批 28/29/30）**。
`hjunk : truncateSimplex 1 (cellParams V X).2 = [u0, u1]` 落地；ε-junk 逆序表
角整支消失（cellParams-witness 经 `p23_trunc1_of_init` 兼为 cellParamsD-
witness，`initialSublist` 桥接）。

## 30. PA22 bisector 家族 holArg 同缺陷（SF22+27 应用波发现）— 分级 M

### (a) HOL 出处：Ysskqoy `Arg` [0,2π)（同 SF22/27）；holArg 批应用波
实测：`bisector_point_exists`（:2319 附近，sorry）的 spec 为
new_specification 且基于 `Complex.arg`，**波及 `bisector_point` 全部下游**。

### (b) 修复

与 SF22/27 同车改述 `holArg`；注意 holArg 对 Complex.arg **无单调性**
（(−π,0)↦(π,2π) 分支反序，仅单射）——refill 时凡"arg 序⟹holArg 序"的
推理不成立（批应用波已录）。

### (c) 状态：**已批准（2026-10-01 用户三连批 28/29/30 之一）；已应用（2026-10-10）**

补丁 `docs/statement-fix-proposals-patches/30-pa22-bisector.patch`（开发波
4f6171af 产出，探针空间 7 轮收敛 EXIT=0、往返字节一致）于 2026-10-10 应用到
PA22（BIEFJHU 清场后窗口；`git apply --check` 干跑过，两 hunk 锚 :43/:2317
未受 +2230 行增量影响）。改述内容：`bisector_point_exists` spec 的
`Complex.arg`→`holArg` 共 8 处（4 exists + 4 props），refill 经
`p22_holArg_cos_sin` 精确极坐标表示绕开 holArg 非单调（全程无 arg 序⟹holArg
序转移），`bisector_point`/`bisector_point_props` 随上游自动闭合，PA22 sorry
−1。同批应用注记：本条应用与存量 PA3↔PA22 `BIJ_SUM` 公共撞名修复（待批）
无关；闸门走 SF 模式 + 自根通道（LocalBridge 被存量撞名挡，偏差记录在案）。

## 31. PA23 `grutoti_sum_volD` 前提面不足——冻结陈述可反驳 — 分级 M（STATEMENT 修正）

### (a) HOL 出处：GRUTOTI.hl:7962-7966

HOL 原文在全称语境携带装填/饱和/edge 门（packing、saturated、u0 ≠ u1、hl
下界、e 具体化 {u0,u1}、region 见证参数）；Lean 冻结版只留
`he : e = {u0, u1}` 一条，V/u0/u1/r/d 全自由——移植时前提丢失，非"难证"。

### (b) 反例（机器验证，docs/assets/grutoti/probe_sum_volD_falsity.lean）

V := ∅（任取 u0 ≠ u1，r := 1，d := 1/2）：`barV ∅ 3 ul` 恒假 ⇒
`mcellSet ∅ = ∅` ⇒ `grutotiEdgeCells ∅ e = ∅` ⇒ setSum = 0；而
`volume.real (grutotiConicCap u0 u1 1 (1/2)) > 0`
（volumeConicCapPos，ConicCapVolume.lean:961）。强形式：对每对 u0 ≠ u1 即假，
无需任何前提；探针含冻结陈述逐字 → False 封闭推论（:4418-4423 全量词形式）。

### (c) 修复（二选一，供批）

(a1) 最小门 = p23_region_data 同款（hs hp hu0 hu1 hne hhl he）+ `0 < r ∧ d < 1`
+ 显式测度覆盖/两两零测前提 ⇒ 主体变 FINITE_EDGE_X2（PA15:775 真证，一行，
有限性支已机验）+ p23_measure_setSum_biUnion 纯装配；
(a2) ∃-式沿 grutoti_region 见证重述（region_data 的 r d 见证内化）。
两条均需 GRUTOTI capstone 调用点（PA23:4484-4494，六条前提全在 scope）同一
SF 打包联动。测度覆盖的数学缺口（TIWWFYQ/GLTVHUM/SLTSTLO1 + PA17 AJRIPQN）
是独立巨型，不在本 SF 范围——本 SF 只把债显式化到前提面。

### (d) 状态：**已批准（2026-10-09 用户拍板"31 批，方案 a1"）；已应用（2026-10-09）**

执行版补丁 `docs/statement-fix-proposals-patches/31-pa23-sum-volD.patch`
（自工作区 diff 生成，闸门多重集比对按构造全等；+64/−21）。应用内容三件：
1. `grutoti_sum_volD` 签名按 (a1) 扩展——门族七条逐字（hs hp hu0 hu1 hne
   hhl he）+ `hr : 0 < r` + `hd : d < 1` + 四条测度前提（hmeas 可测性 /
   hpair 两两零测 / hvol 体积有限 / hcov 覆盖恒等式 `volume.real (⋃₀ 迹) =
   volume.real D`），结论不变；主体真证零 sorry：`FINITE_EDGE_X2`（有限性支，
   PA15:775，∈-体已机验）+ `p23_measure_setSum_biUnion`（rw 改写 + hcov
   收尾）。
2. 新增债务桥私件 `p23_grutoti_sum_volD_measure_facts`（sorry 1 处，NEEDS
   定点：hcov = TIWWFYQ/GLTVHUM/SLTSTLO1 覆盖巨型；hpair = PA17 AJRIPQN
   逐边实例；hmeas/hvol = mcell 可测性+闭球有限体积可证支待拆）。
3. `GRUTOTI` capstone 调用点重接线（陈述冻结未动，证明体仍真，改经债务桥
   obtain 四条测度事实后传入新签名）。
附带：GT-2 lane note 反例 sketch 修正（mcell4 路线不成立，远点族走
mcell0/2/3）已随新 docstring 落档。

附带修正建议：GT-2 lane note"mcell 4 cells carry e"反例 sketch 不成立
（远点族 hl ≥ √2 ⇒ mcell4 = ∅）；无穷性支路应走远点 Delaunay 族的
mcell0/2/3。随本 SF 落档。

## 32. PA23 `p23_grutoti_cap_measure_cover` 缺 region 门（hcov 覆盖恒等式）— 分级 A（STATEMENT 修正）

### (a) HOL 出处：GRUTOTI.hl:7228-7400（同 SF31 源，§G 测度覆盖段）

HOL 原文在全称语境携带 region 见证（`c ≤ d`、`hl/√2 ≤ d`、`c`-锥 Rogers
覆盖）。Lean 版（SF32 拆分波定点）只有 region-block 形 `0 < r ≤ 1 ∧ 0 < d < 1`
——d < hl/√2 时恒等式很可能为假（D 伸进非携边胞、正测度），与 SF31 同类的
移植前提丢失。

### (b) 反例方向（定性）

d 充分小时 `rconeGt u0 u1 d` 严格大于 `rconeGt u0 u1 (hl/√2)`，差锥区含非携
边胞的正测度迹，`⋃₀ 迹 = D` 不成立。精确反例可沿 SF31 的 ∅-思路变体构造，
立案阶段以侦察地图（docs/scouts/tiwwfyq-coverage-scout.md §2 缺口 G1）为准。

### (c) 修复方案

前提面加 region 门：`(hcovW : ∃ c, c ≤ d ∧ ball u0 1 ∩ rconeGt u0 u1 c ⊆
⋃₀ (rogers V '' p23Fam) ∧ ...)`——或直接收 `p23_region_data` 的输出形状
（c ≤ d ∧ hl/√2 ≤ d ∧ mcell 覆盖），与 SF31 的 (a1) 精神一致：债显式化到
前提面，主体变 `p23_C_sub_rogers` 实例 + SLTSTLO1 逐点 + B1 VX-桥 + 双
measure_mono 纯装配（~150-250 行）。GRUTOTI 调用点与
`p23_grutoti_sum_volD_measure_facts` 同步联动。

### (d) 状态：**已批准（2026-10-10 用户四件合并批）；执行波在飞**

## 33. PA23 `grutoti_pivot` 缺 region 门与 hw* 窄性（楔形 pivot 恒等式）— 分级 A（STATEMENT 修正）

### (a) HOL 出处：GRUTOTI.hl:7962-7966（§G/§H 7441-7958）

HOL 语境携带 packing/饱和/hl 下界与 hw1-hw4 窄性数据；Lean 冻结版只有
`hr hr1 hd hd1 he hfin` 六条。

### (b) 不可证性（定性）

¬nullSet(X∩D) 支需要 k≥2 计数（`p23_edge_cell_k_ge_two` 真证）+ 逐 k 窄性
（k=3/4 走 CONIC_CAP_INTER_CONVEX_HULL_4_GT_0——PA15:2275 已真证，旧注
"still sorried" 过期；k=2 走 hw1），全部需要 region 数据；冻结签名收不进来。

### (c) 修复方案

前提面加 `(hs hp hu0 hu1 hne hhl) + hw1 hw3 hw4`（恰为 `grutoti_cell_vol`
消费形，`p23_region_data` 逐字供给）；主体 null 支 + u0-首向支变
`p23_setSum_congr` + `grutoti_cell_vol` 逐点纯装配（~100-200 行）；反向支
k=2 走 MCELL2_PERMUTE_01 镜像（~100-150 行），k=3/4 反向（dihX 定向 junk
语义）为真缺口 G3 另案。GRUTOTI 调用点同步联动。

### (d) 状态：**已批准（2026-10-10 用户四件合并批）；执行波在飞**

## 34. PA22 `BIJ_SUM` 跨模块公共撞名（LocalBridge 不可构建）— 分级 A（名字空间修复）

### (a) HOL 出处：counting_spheres.hl:6308（PA22 侧；PA3:470 侧为 OXLZLEZ1.hl:307-315）

两侧是不同 HOL 源、不同陈述的同名公共定理（PA22 侧 Set 版 / PA3 侧 Finset 版）。
LocalBridge（PA22 唯一导入方）同时导入 PA3 ⇒ import 级撞名，`lake build
Kepler.Text.LocalBridge` 在 HEAD 即败（存量缺陷，近期闸门以根覆盖绕过未暴露，
2026-10-10 BIEFJHU 闸首次踩上）。

### (c) 修复

PA22 侧 `theorem BIJ_SUM` → `private theorem BIJ_SUM`（一行可见性修正；全仓
外部消费者为零——PA4 引用的是 PA3 侧，已核）。陈述文本一字不动。

### (d) 状态：**已批准（2026-10-10 用户四件合并批）；已应用（2026-10-10）**——
执行版补丁 `docs/statement-fix-proposals-patches/34-pa22-bij-sum.patch`（一行
可见性修正，闸 BIEFJHU_explicit 过，SF 模式多重集全等；LocalBridge 撞名解除）。

## 35. IneqClosureDefs `rho` 与 LocalAuto1 `rho` 跨模块公共撞名（Assembly 不可构建）— 分级 A（名字空间修复）

### (a) HOL 出处：IneqClosureDefs.lean:752（`rho` = 1 + const1 − const1·ly y，
ineq.hl ρ 函数闭包侧）；LocalAuto1.lean:180（`rho` = 1 + (y−2)·(sol0/π)/(2h0−2)，
localization 侧）——同名不同定义。

Assembly（:20 导 LA1；IneqClosureDefs 经 PA21 传递）同时见到两者 ⇒ `lake build
Kepler.Assembly` 在 HEAD 即败（存量缺陷）。LA1 侧消费者家族庞大
（LocalConcl/AzimBridge/LA2/5/12/14/17/18/23/29/33/34/36/38…）不可动；
IneqClosureDefs 侧外部消费者仅 PA21（2 处 bare 使用）。

### (c) 修复

循 arcLength→arcLengthICD 先例（2f2c431c 编排者核定同款）：IneqClosureDefs
`rho` → `rhoICD`（8 处文件内 + PA21 的 2 处使用同步改写）。定义体与陈述零改动。

### (d) 状态：**已批准（2026-10-10 用户四件合并批）；已应用（2026-10-10）**——
执行版补丁 `docs/statement-fix-proposals-patches/35-ineqclosuredefs-rho.patch`
（单文件 8 处 rho→rhoICD 含 docstring；PA21 两处为注释提及零代码改动，核验
后未触碰）。

## 36. Assembly `CertifiedIneqHolds` 占位语义落实（T1 展开波随件）— 分级 A（def 语义修正）

### (a) HOL 出处：ineq.hl 各记录 ID（CertifiedIneqHolds 的查表语义）；Assembly 头部
docstring 既定消除顺序原文："先填六个 ID 清单与 `CertifiedIneqHolds` 语义，再逐条
闭合证书"。

### (b) 不可证性（占位判定）

原 def `CertifiedIneqHolds (_id : String) : Prop := True` —— 恒真占位使任何
基于它的陈述平凡可证，接口语义为空。T1 批（用户 2026-10-10 第一批批准，含
"CertifiedIneqHolds 语义填实"）将其落为诚实最小形：查表体 =
`certifiedIneqHolds_pilot`（键 "3397113841" → ineq.hl 字面量化不等式，G4 证书
1504 叶 + 粘合引理支撑；表外回落 True——回落分支的平凡性由 IdLists.lean:699
else-True 警告注记明确防线：不得经回落/空清单平凡闭合）。

### (c) 状态：**已批准（2026-10-10 用户第一批）；执行版补丁随 T1 工作区 diff 生成**

## 37. PA2:5477 `MXI_EXISTS_concl`（+ PackingConcl:336 穿透 + 4 调用点加参）— 分级 A（STATEMENT 修正：concl-shim 欠 `r₃ < √2` 卫兵，为假）

### (a) HOL 出处与裁决

- **现 shim 镜像**：`pack_concl.hl:120-123` `MXI_EXISTS_concl` —— 该件在 HOL
  只是**结论陈述模板**（backquote 注册件，非 `prove_by_refinement`）：
  `saturated V /\ packing V /\ barV V 3 ul /\ sqrt(&2) <= hl ul ==> (mxi V ul IN
  convex hull {omega_list_n V ul 2, omega_list_n V ul 3}) /\ (dist(mxi V ul,
  HD ul) = sqrt(&2))`。HOL 侧**没有任何前提下按此弱前提集使用它**——它的实际
  载体是 marchal2.hl:2516 `MXI_EXPLICIT`（**Lemma 46**，`prove_by_refinement`）：
  前提为 `packing V /\ saturated V /\ barV V 3 ul /\ ul = [u0;u1;u2;u3] /\
  hl (truncate_simplex 2 ul) < sqrt(&2) /\ sqrt(&2) <= hl ul`。**pack_concl
  模板是丢失截断卫兵的有损接口；PA2 立项期照模板冻结，即照丢**。
- **缺陷**：shim 陈述在现前提集下**为假**——B2 形反例（PA24 第四波侦察纠错
  2026-10-12，PA24:4983-4996 记档；判别件 `p24_caseB2_mxi_eq`（PA24:5122，
  **真证**）：`√2 ≤ hl (truncateSimplex 2 vl) → mxi V vl = omegaListN V vl 2`）：
  取 `r₃ := hl (truncateSimplex 2 ul) ≥ √2`（mxi 定义 if 正支翻转），则
  `mxi V ul = ω₂`；ω₂ ∈ 三点 voronoi 胞 ⊆ 外轴线 `L = {x | dist x u0 = dist x u1
  = dist x v}`（⊥ 三角形外心 cc），毕氏恒等式 `dist(u0, ω₂)² = r₃² +
  ‖ω₂ − cc‖² ≥ r₃²`，一般严格 > 2，与结论 `dist(mxi, HD ul) = √2` 矛盾。
  `barV V 3 ul` 不可补救：barV 只约束整表（`BARV_3_EXPLICIT`（PA8:207，真证）
  给四元组形），不约束**真截断** `truncateSimplex 2 ul` 的高度。
- **分级 A**（为假陈述 + 有真实消费者），SF25 同型穿透（PA2 concl-shim +
  PackingConcl 镜像 + 调用点）。

### (b) 修复补丁

执行版补丁
`docs/statement-fix-proposals-patches/37-mxi-exists-trunc-hl.patch`
（已过 `git apply --check`，对生成时工作树可干净应用；6 文件 21+/12−）：

1. **PA2:5477（主件）**：陈述补前提
   `hl (truncateSimplex 2 ul) < Real.sqrt 2 →`（Lean 侧名 `truncateSimplex
   (j : ℕ) (ul : List V3)`，PA2:216；插在 `barV V 3 ul →` 与
   `Real.sqrt 2 ≤ hl ul →` 之间，**与 HOL MXI_EXPLICIT 前提序一致**）；
   docstring 改记 marchal2.hl:2516 出处与不可去性。**两个结论合取支零改动**；
   证明体 `sorry` 原位。
2. **PackingConcl:336（镜像穿透，SF25 教训同款）**：
   `MXI_EXISTS_concl_discharged` 陈述同步补参 + docstring 修正（原文称
   `ul = [u0,u1,u2,u3]` "not derivable" 不确——`BARV_3_EXPLICIT` 可从
   `barV V 3 ul` 导出四元组形；不可导的只是截断卫兵）。该镜像现无下游消费者
   （全树仅定义处一 hit）。
3. **4 个调用点加参（同一 patch，防半应用破树）**：PA11:457、PA12:1949、
   PA20:2031、PA24:4647（见 (c)，各 1 行）。

### (c) 消费面核实（4 代码调用点 + 1 镜像；逐点"能否供出新前提"）

| 消费点 | 外层定理 | 新前提实参 | 供出方式 | 判定 |
| --- | --- | --- | --- | --- |
| PA24:4647 | `p24_caseB3_aux`（private） | `hr3` | 外层假设 `(hr3 : hl (truncateSimplex 2 vl) < Real.sqrt 2)` 即 B3 支判别式；`subst`/`set` 后型恰为 `hl (truncateSimplex 2 [u0,u1,v,w]) < √2`，插 `hr3 hr4` | **能供，零改写** |
| PA11:457 | `mxiExplicit`（private，marchal2.hl:2516 装配） | `hc1` | 外层假设 `(hc1 : hl (truncateSimplex 2 [u0,u1,u2,u3]) < Real.sqrt 2)` 本就在 scope（此前 shim 用不上它），插 `hc1 hc2` | **能供，零改写** |
| PA12:1949 | `MXI_EXPLICIT`（public，marchal2.hl:2516 正本） | `h2` | 外层假设 `(h2 : hl (truncateSimplex 2 ul) < Real.sqrt 2)`，插 `h2 h3`；MXI_EXPLICIT 自身签名不动 → 其下游（PA12:2014 OLD、PA13:729、PA15:1095、PA18:1886、PA18:2094）**零波及** | **能供，零改写** |
| PA20:2031 | `p20g_apex_dist3`（private） | `hlow` | 调用前 3 行自 `mcell 3` ite 展开 + `hneX` 内部已导出 `hcond : hl (truncateSimplex 2 [a,b,c,d]) < √2 ∧ √2 ≤ hl [a,b,c,d]`，`obtain ⟨hlow, hhigh⟩`，插 `hlow hhigh` | **能供，零改写** |
| PackingConcl:336 | `MXI_EXISTS_concl_discharged`（陈述孪生） | — | 陈述同步补参（同 patch） | 已同步 |

docstring 纯提及（零代码改动）：PA11:59/445、PA13:67/591、PA20:2312/2326、
PA23:6009、PA24:4216/4517/4985/4991/5200/5203（后四者为 PA24 侦察纠错记档，
历史记录保留）。

**类型级验证**：探针（`lake env lean` 单进程，axiom 替身复刻新签名）验证
新前提面良构 + 四调用形（含各点实参实名 hr3/hr4、hc1/hc2、h2/h3、hlow/hhigh）
全部 typecheck，exit 0。

### (d) 保真论证

补后 shim 陈述 ≡ marchal2 `MXI_EXPLICIT` 的合取形，差仅两处无损重排：
(i) HOL 的 `ul = [u0;u1;u2;u3]` 在 shim 中省去——`barV V 3 ul` 经
`BARV_3_EXPLICIT`（PA8:207，真证）给 `∃ u0 u1 u2 u3, ul = [u0,u1,u2,u3]`，
∃-形重打包无损（HD/omegaListN/mxi 均按表索引，与具体顶点名无关）；
(ii) HOL 结论 `?s. between s (ω₂,ω₃) ∧ dist (u0,s) = √2 ∧ mxi V ul = s`
经 between↔convexHull-pair 与 `s = mxi` 化为 shim 的两合取支（PA11:458-462 /
PA12:1950-1953 现有装配即此换向，可互为见证）。前提序与 HOL 逐项一致。

### (e) 风险

- **陈述修正 ≠ 闭合**：`sorry` 原位不动，**sorry 净变化 0**；闭合另行走
  PA12 `MXI_EXPLICIT` 正本或 SEGMENT_INTER_CBALL_LEMMA 路线。
- 4 调用点必须与主件**同 patch 同车**（SF20/SF25 教训：半应用 = 4 处编译错；
  PA11/PA12/PA20/PA24 均直接 import PA2，无环依赖，应用顺序无关）。
- PA24 `p24_caseB3_aux` 的 B3 支路线图不受影响（其分支判别式恰含新卫兵，
  PA24:4985 记档"记账待 PA2 车道修"即本项；B2 支改道路线与 PA24:4991 之后的
  修正后处方照旧执行，不受本项牵动）。

### (f) 状态：**已立项起草（2026-10-12 用户批）；补丁草案就绪待应用波**
（应用时闸参数建议：`SF_ITEM=37`，审计对象 `Kepler.Text.MXI_EXISTS_concl` +
`Kepler.Text.MXI_EXISTS_concl_discharged`，namespace `Kepler.Text`；验收 =
六文件 `lake build` 零新错 + `sorry` 计数差 0）。

## 38. PA14 `QZKSYKG2` 冻结 comprehension 欠尾固定合取项（弱 permutes 族不可消费，AJRIPQN 闭合最后一块）— 分级 A（STATEMENT 修正）

### (a) HOL 出处与裁决

- **HOL 正本**：`QZKSYKG2`（QZKSYKG.hl:255-262 concl，proof 325-2251，~1900
  行巨案）：`mcell k V ul` 被全体 `left_action_list p ul`（`p` 取遍 `0..k-1`
  的排列）的 Rogers 单形并覆盖。HL `permutes`
  （azure/hol-light-nat/Library/permutations.ml:9）为 **complement-fixing**
  双射（`!x. ~(x IN s) ==> p x = x` 合取支；`PERMUTES_TRIVIAL`：
  `p permutes 0..0 <=> p = I`）——PA10:183 已裁定此为本体前提。故 HOL
  结论的被并集族 = **尾固定**排列族。
- **缺陷**：Lean 冻结陈述（PA14:932-937）的被并集族只按弱按点
  `permutes`（`∀ x, x ∈ Icc 0 (k-1) ↔ p x ∈ Icc 0 (k-1)`，PackingAuto2
  编码）筛，junk 尾排列（如 k = 1 时 p 1 ↦ 7 把 getD-default 点甩进
  `leftActionList` 尾槽）混入族内。与 SF-20（QZKSYKG1）的"为假"**不同
  类**：弱式并集更大 ⇒ 覆盖更弱 ⇒ 冻结陈述**不假**，但**不可消费**——从
  弱式并集取出的 p 无尾固定性，无法交给带 `hfix` 的下游 `QZKSYKG1`/
  `RVFXZBU`（PA17:802-804 已记档："neither QZKSYKG1 nor RVFXZBU can
  consume them"）。AJRIPQN 五阶段装配（PA17 `p17_ajripqn_of_pieces`:
  683-687 / `p17_ajripqn_of_tailfix`:824-827 的 `hQ2` 参数）恰按补后形
  冻结参数型，弱式供不出 ⇒ PA17:810 的
  `exact p17_ajripqn_of_tailfix … (QZKSYKG2-补后形 …)` 闭合路径断链。
- **分级 A**（真实消费者 + 陈述修正方向唯一）；同病先例：SF-20（同文件
  同家族 `QZKSYKG1`，2026-09-30 用户批准已应用）。

### (b) 修复补丁

草案 `docs/statement-fix-proposals-patches/38-qzksykg2-tailfix.patch`
（2 文件 +31/−9；对生成时工作树 `git apply --check` 干净可贴）：

1. **PA14 `QZKSYKG2`（主件，:932-937）**：comprehension 补合取项
   `{p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k - 1)) ∧ ∀ n : ℕ,
   k ≤ n → p n = n}`——合取项逐字 = `p17_ajripqn_of_tailfix` 的 `hQ2`
   消费形（PA17:826-827，`∀ n : ℕ` 显式类型同款）。**前提面零改动**；
   证明体 `sorry` 原位。docstring 补 Statement 记档行 + NEEDS 注记同步。
2. **PA17 `qzksykg2_p17`（:253-259 转发 shim）**：statement 同步补同款
   合取项，转发 term `QZKSYKG2 hsat hpack hbar hk` **一字不动**（SF-20
   `qzksykg1_p17` 同步透传先例）。**必须同 patch 同车**：弱式下 shim 的
   声明型是冻结形，主件补强后转发 term 型不匹配（两 set-comprehension
   差一合取支，非 defeq），半应用 = PA17 编译错——SF-20 教训同款。
3. **注记同步（同 patch，纯注释）**：PA14 头部 ENCODING-FIX 段
   （"keep the plain `permutes` form" 对两件已双料过时）与 Proof status
   行；PA17 shim docstring 补项 38 记档。

### (c) 消费面核实（全树 grep `QZKSYKG2` + comprehension 形状扫描）

| 消费点 | 性质 | 判定 |
| --- | --- | --- |
| PA17:259 `qzksykg2_p17` 转发 term | `QZKSYKG2` **唯一代码调用点** | **破损点**：补强后 term 型与 shim 声明型不匹配 ⇒ 同车同步（(b)2）；shim 为 private 且**全树零代码调用点**（仅 PA17:64/876/897/918 docstring 提及），同步零波及 |
| PA17:824-827 `p17_ajripqn_of_tailfix` 的 `hQ2` | 新消费（参数化假设） | 本项动机；补后 `QZKSYKG2` 经 `k ≤ 4 → k ∈ {0,1,2,3,4}` 转换（`upTo4KyLemma_p17`）直接供给；探针已验证 |
| PA17:683-687 `p17_ajripqn_of_pieces` 的 `hQ2` 参数 | 新消费 | 参数型本就按补后形冻结（PA17:686-687），不受影响 |
| PA14 文件内 | 无其他调用 | 主件 `sorry` 原位，文件内无第二消费点 |
| PA4:1370-1495 / PA15:521 / LocalAuto38Bridge:42 | 纯注释提及 | 零代码改动；PA4 记的"QZKSYKG1-2 仍未证"指本体 sorry（仍成立） |
| PA20:816/2102 | 消费的是 `QZKSYKG1` | 已带 `hfix`（SF-20 产物），本项不触 |
| 单调回退通道 | 补后式 ⇒ 冻结弱式 | 逐元素重打包（`hp.1` 舍弃合取支）即得（探针 4）；任何未来弱式消费者有一条行补救 |

### (d) 保真论证

补后 comprehension 族 = HL `permutes` 本义下的排列族：complement-fixing
的 `∀ n ≥ k, p n = n` 逐字展开即所补合取支。冻结陈述是丢编码前提的有损
接口，补后式才是 HOL `QZKSYKG2` concl 的忠实编码——与 SF-20 给
`QZKSYKG1` 补 `hfix` 前提同一裁据（PA10:183 ruling）。方向性差异记档：
SF-20 是"补前提 = 变弱"，本项是"收窄结论族 = 变强"，两者同朝 HOL 收敛
（"补合取支 = 加参变弱 = HOL 忠实方向"在本项的落实形为：弱编码相对 HOL
少了限制，补上即回正本）。

### (e) 风险

- **陈述修正 ≠ 闭合**：`sorry` 原位，两文件 sorry 计数差 0（探针实测：
  PA14 三处 sorry 同位平移 705→709 / 895→899 / 932→942；PA17 一处
  `AJRIPQN` 不动）。k ≤ 3 本体仍卡 `LEFT_ACTION_LIST_PROPERTIES`
  （marchal2.hl:4460 S₃ 巨案，`ynhyjit_p14` i = 3 NEEDS）；k = 4 仍卡
  `YIFVQDV_1`（与 `QZKSYKG1` 的 k = 4 案共享）——两巨案不受本项影响。
- **补强与 HL 证结构同向**：HL 原证在 k = 2/3 案经
  `LEFT_ACTION_LIST_PROPERTIES`（"permutations fixing indices ≥ i-1"）
  本就只对尾固定族工作，闭合时无需重排证法、无新增数学义务。
- 主件与 shim 必须同车（(b)2）；PA17 直接 import PA14，无环依赖，应用
  顺序无关。尾部固定语义与 PA10 `RVFXZBU`/SF-20 `QZKSYKG1` 的既有
  `hfix` 前提逐字同族（`∀ j/n : ℕ, k ≤ j/n → p j/n = j/n`），无新概念。

### (f) 状态：**已立项起草（2026-10-12 用户批）；补丁草案就绪待应用波**
（应用时闸参数建议：`SF_ITEM=38`，GATE_MODE=STATEMENT-FIX；审计对象
`Kepler.Text.QZKSYKG2`（主件）+ `Kepler.Text.qzksykg2_p17`（同步 shim，
private）；namespace `Kepler.Text`；验收 = `lake build
Kepler.Text.PackingAuto14 Kepler.Text.PackingAuto17` 零新错 + sorry 计数
差 0。起草期已单进程预演（`lake env lean`，工作树零改动）：修补后 PA14
整文件 exit 0；axiom 替身复刻新签名 + shim 转发形 + `hQ2` 消费形 + 单调
回退四项 typecheck exit 0；LEAN_PATH 前置 /tmp olean 的配对编译（补后
PA14 + 补后 PA17）exit 0。）

---

## 39. Assembly `KcblrqcIneqDef` 占位统一（`:= True` → TameLp 真切片，MQMSMAB 终接线唯一缺口）— 分级 A（def 语义修正）

**立案：2026-10-13，A10 第四波（MQMSMAB Assembly 终接线 lane）交付随件。**
lane 纪律禁止本波自行动用陈述变更权，接线按「凡依赖该裁决的路径诚实记账
卡 SF 待批，其余能落全落」完成：B4 十二短引理 + B3 语义桥 + 装配件
`mqmsmabWired` 已在 `lean/Kepler/Assembly.lean` §2c' 全绿落地
（`lake build Kepler.Assembly` EXIT=0），`mqmsmab` 本体原位待批。

### (a) HOL 出处与缺陷

`Assembly.lean:212`：`def KcblrqcIneqDef : Prop := True`（`PLACEHOLDER(P6-E)`）。
HOL `kcblrqc_ineq_def`（`tame/ssreflect/tame_lemmas-compiled.hl:34-46`）是
Ineq 数据库 28 条机器不等式的 mk_conj 大合取（MQMSMAB-compiled.hl:24 的
section 前提 `ineqs := kcblrqc_ineq_def` 消费）。`Kepler.Text.TameLp.lean:512-532`
已有其 **MQMSMAB/KCBLRQC/BDJYFFB 消费切片真形**（四类：azim 双边界、
`get_b_tame_ineq` 表 r=0 情形 20 对、6 个 r>0 node-type 的数值矛盾、
(5,0,1) 行 tauVEF 和 ≥ 0.6366；TameLp:495-509 保真注记 + :506 自认
「两处接口在 G4 落地后统一」）。

占位的两类病并发（scout `docs/scouts/mqmsmab-scout.md` §6.1 分类）：
①**不可证**——`mqmsmab` 的 `hkcblrqc` 前提需供出 `TameLp.KcblrqcIneqDef`
真切片（`KCBLRQC`/`BDJYFFB1/2`/`SZIPOAS`/`CDTETAT` 的 `hineq` 前提是
DIH_Y_INEQ 等机器不等式，**不可能从 `True` 推出**），A10 终接线死锁；
②**接口虚设**——`TheNonlinearInequalities`（Assembly:222）第 6 分量在
占位语义下空洞成立，textCapstone 的三前提链第 3 腿名存实虚。

### (b) 修复补丁

单文件单行 def 体替换（scout §4 Step 0 方案 a）：

```
- def KcblrqcIneqDef : Prop := True
+ def KcblrqcIneqDef : Prop := Kepler.Text.TameLp.KcblrqcIneqDef
```

**零 import 变更**（`import Kepler.Text.TameLp` 已于 A10 第三波前置在位，
Assembly:15；TameLp 不 import Assembly，无环）。随批同车一行：`mqmsmab`
证明体占位行替换为 `mqmsmabWired V hkcblrqc hmain hfan hc`（备件已全绿）。
受控孪生（§5.2 playbook「不要新增孪生」条款的反向清偿）：两处接口统一于
TameLp 正本。

### (c) 消费面核实（全树 grep `KcblrqcIneqDef`）

| 消费点 | 性质 | 判定 |
| --- | --- | --- |
| Assembly:222 `TheNonlinearInequalities` def 第 6 合取项 | def 体引用 | 语义自动增强，文本零改 |
| Assembly:384 `nliKcblrqcIneqDef`（骨架占位） | 唯一以占位语义受益的声明 | 陈述文本零改；其真化 = 28 条证书接线（IdLists.lean:630-658 `kcblrqcIneqDefIds`），独立波不随本项 |
| Assembly:393 `nliKcblrqcIneqDefIds`（清单侧） | `AllCertified` | 不受影响 |
| Assembly:667 `mqmsmab` 的 `hkcblrqc` 前提 | **受益主体** | 批准后证明体 = `mqmsmabWired …` 一行（已备件） |
| Assembly:5232 `nonlinearInequalities` 聚合 | 引用 | 文本零改 |
| textCapstone（Assembly:5248 起）经 `hNL` 第 6 分量传递 | 间接 | 自动受益；MQMSMAB 调用点 :5263 已在位 |
| Assembly/IdLists.lean:629 | 纯注释 | 零改动 |
| 单调回退通道 | 补后式 ⇒ 占位式 | `True` 由任意命题平凡蕴含；当前无人从 `KcblrqcIneqDef` 抽取具体事实（纯前提位），回退一行可补 |

### (d) 保真论证

补后 def 体 = `TameLp.lean:512-532` 真切片逐字引用，其四类切片与 HOL
`tame_lemmas-compiled.hl:34-46` 大合取的对应保真论证已在该处注记 + scout
§4 Step 0 记档（两条 azim 边界 = `TRIANGULAR_FACE_AZIM_DART_BOUNDS`
（tame_general.hl:739-746，机器 ineq `5735387903`/`5490182221`）与
`non_triangular_face_azim_dart_bound`（ssreflect/tame_lemmas-compiled.hl:895-918，
机器 DIH_Y_INEQ）的结论形；b_tame 表 r=0 情形 = KCBLRQC.vhl `lp_data`；
6 类型矛盾 = 同表机器不等式数值组合；(5,0,1) 行 ≥ 0.6366 = BDJYFFB2
消费形）。本项属「前提侧省略内容」型占位（非语义分歧、非弱编码偏置）：
修复方向唯一（换入真切片），无 SUM_INTER 式 junk 语义风险；同分级先例 =
SF-36（Assembly `CertifiedIneqHolds` 占位语义落实，def 语义修正类）。

### (e) 风险

- **陈述修正 ≠ 闭合**：def 体替换本身 sorry 计数差 0；两骨架
  （nliKcblrqcIneqDef/Ids）原位，28 条 G4 证书接线是独立工作量。本项落地
  即解锁的是**结构接线**（mqmsmab → textCapstone 脊柱贯通），数值内容沿
  TameLp 六枚上游占位件（fully_surrounded_perimeter_bound / sum_tauVEF /
  ineq_tauK×4）按「消费含占位前提定理」惯例合法流动（Assembly:449-451
  先例）。
- 语义增强面 = `TheNonlinearInequalities` 第 6 分量 + `mqmsmab` 可证性；
  无任何既有证明会因前提变强而破损（唯一消费 `hkcblrqc` 的 `mqmsmab`
  当前的证明体就是待替换占位行）。
- 同族不在范围：Assembly `Adm3` `True` 尾（:570）与 `GoodGraphV4` 四
  `True`（:445-455 一带）是 A9 债务（scout §6.1 已记），本项不触。

### (f) 状态：**已批准并应用（2026-10-14 用户批准 SF-39；执行版补丁 docs/statement-fix-proposals-patches/39-kcblrqcineqdef-mqmsmab.patch 同车，STATEMENT-FIX 闸）**
（应用时闸参数建议：`SF_ITEM=39`，GATE_MODE=STATEMENT-FIX；审计对象
`Kepler.Assembly.mqmsmabWired`（全绿在位）+ 批准后的 `Kepler.Assembly.mqmsmab`；
namespace `Kepler.Assembly`；验收 = `lake build Kepler.Assembly` 零新错 +
sorry 计数差 0（mqmsmab 占位行减 1 为预期）。接线波已单进程验证：桥层
探针（/tmp，import Kepler.Assembly + 实例盾复制）exit 0，落位后
`lake build Kepler.Assembly` EXIT=0。）

## 40. LA11 `x1DeltaY_p11` def 体误抄纠正（δ_x1 偏导 → HOL 逐字 `delta_x`；冻结定理在其上为假）— 分级 A（def 语义修正）

**立案：2026-10-14，LA11 atn2-merge 同根清偿车道交付随件。** 车道纪律禁止
自行动用陈述/定义变更权；本波十件填实（`lindihpi_lt_small_p11` 家族，36→26）
已在隔离 clone 全绿验证（`lake build Kepler.Text.LocalAuto11` EXIT=0），
原位待批。

### (a) HOL 出处与缺陷

`LocalAuto11.lean:171`（HEAD 口径）：`x1DeltaY_p11` def 体为
`y1 * y1 * deltaX1f_p11 …`，即乘的是 **delta_x1 偏导**；而 HOL 原文
`x1_delta_y`（sphere.hl:842）= `y_of_x x1_delta_x`，其中
`x1_delta_x = x1 * delta_x`（sphere.hl:840，**全量 delta_x**，非偏导）。
def 体与 docstring 同错（误抄）。

病：在该体下，本波冻结陈述 `lindihpi_lt_y_small_p11`
（lp_details.hl:1296）为**假命题**——反例 y=(1,2,2,2,2,2), b=3.4：
左边 4·y1²·δ_x1 = 160 < 166.6 为真，而右边 dihY ≈ 1.0855 ≥
arctan√3.4 ≈ 1.0743 为假，蕴含式不成立。十件填实中的 y-变体与其
数值族均消费此 def，不纠正则填实件无法全数转真。

影响面：全仓 grep 验证 `x1DeltaY_p11` **零其他消费者**；def 签名
（类型）不变，所有消费定理签名逐字冻结不变——纯 def 体一行替换
（`deltaX1f_p11` → `deltaX`）+ docstring 重写。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/40-x1deltay-lat11.patch`
（git diff 全量：def 体一行 + docstring + 本波十件填实 + 5 枚新私件）。
SF 闸锚 `lindihpi_lt_small_p11`；公理面规则⑤白名单。

## 41. PA3 `a_spine5`/`b_spine5` opaque 常数体揭示（sphere.hl:632/634 逐字；`TEWNSCJ_MERGED` 桥唯一缺口）— 分级 A（def 语义修正 · 常数重指向）

**立案：2026-10-13，PA25 merge-ineq 波记账随件 + 侦察车道（TEWNSCJ PA3
opaque 桥，HANDOFF 待拍板项清偿）交付随件。** 车道纪律禁止本波自行动用
陈述/定义变更权（PA3 实际变更待批准后另行走闸）；全部验证在隔离 clone
（/tmp/p4tew，`git clone` + `cp -Rc` .lake，零软链 packages）以探针仪器
完成（playbook 雷区 ㉚/㉛/㉜）。

### (a) HOL 出处与缺陷

`PackingAuto3.lean:51/54`（HEAD 口径）：`opaque a_spine5 : ℝ` /
`opaque b_spine5 : ℝ`——真 opaque（无体），docstring 自述 "kept opaque
here … every theorem below is conditional on it"。但本仓持久参考件
**sphere.hl:632/634 是 `new_definition` 而非外部公理**，逐字引文
（reference/flyspeck/text_formalization/general/sphere.hl，
"(* nonlinear inequalities *)" 节）：

    let a_spine5 = new_definition `a_spine5 = #0.0560305`;;
    let b_spine5 = new_definition `b_spine5 = -- #0.0445813`;;

且仓库已两处携带同值体：`aSpine5`/`bSpine5`（IneqClosureDefs.lean:598/601，
sphere.hl:632/634 记档，:603 `rfl` 数值自检；PA21 bank 系消费）与 private
`aSpine5P4`/`bSpine5P4`（PackingAuto4.lean:178/181，同值）。PA3 opaque 是
全仓第三处、唯一无体形态——搬运时省体（docstring 记 "defined in
Flyspeck_constants outside OXLZLEZ1.hl"，与参考件内联定义口径不符）。

病：PA25 `TEWNSCJ_MERGED`（:5921，冻结陈述）结论携带 `a_spine5 + b_spine5
* dihY …`，证明唯一通道 `bank_TEWNSCJ`（PA21:526，rest 12/62）首析取支是
数值体 `yOfX (gamma23Full8X (h0cut y1)) … > aSpine5 + bSpine5 * dihY …`；
opaque 常数无定义等式，桥 `a_spine5 = aSpine5 ∧ b_spine5 = bSpine5` 不可证
⇒ 十行机械收口卡死（PA25:5913-5920 记账、头部 :227-228、e2e-debt-map:287
同源）。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/41-pa3-spine5-tewnescj.patch`
（git diff 全量，两文件）：

1. **PA3（声明体改动，陈述文本零改动）**：`opaque` → `def` 带 sphere.hl
   632/634 逐字体 + docstring 重写。两常数的全文件代码出现点仅
   `cc_real_model_v11` 四合取支（:168/:191/:193/:195），文本不变；零
   import 变更（数值逐字内联，不引 IneqClosureDefs 名，PA3 导入闭包不动）。
2. **PA25（受益面收口，同车）**：`TEWNSCJ_MERGED` `sorry` → 十八行战术体
   （`proj_bank_TEWNSCJ` 投影 + `p25_gamma23Full8X_yOfX_eq` 复合桥 +
   `rad2YP25 = yOfX rad2X` rfl 桥（TXQTPVC_MERGED:5901 同款）+ hrad/he1/he2
   否证支；常数桥以 `show a_spine5 = aSpine5 from rfl` 两改写落实）+ 冻结
   陈述签名一字不改 + 头部记账行（:227-228）与本件 docstring 同步（纯注释）。

先例对照：**rad2XP25 形最接近**（PA25:91-98，def 体改逐字重指向、陈述零
改动、解锁 rfl 桥）；分级同 SF-39（占位语义 → 真内容，def 语义修正类）；
SF-40 为误抄纠正，本案非误抄而是搬运省体，"揭示逐字体"动作同形。

### (c) 消费面核实（全树 grep `a_spine5`/`b_spine5`，代码消费全图）

| 消费点 | 性质 | 判定 |
| --- | --- | --- |
| PA3 `cc_real_model_v11` 四合取支（:168/:191/:193/:195） | def 体引用 | 文本零改；语义不变（opaque→def 保守扩张：常数符号不变，仅增 defeq 展开面） |
| PA25 `real_model_ztg4`(:5040)/`pema`(:5508)/`pemb`(:5520)/`tew`(:5967) | 冻结陈述引用 | 文本零改；各自 sorry 待 G4 证书（独立债，不随本项） |
| PA25 `pkrmQu`(:6157)/`pkrmQy`(:6333/:6339/:6344) | 装配引用 | 文本零改；下游自动受益（未来数值证书可经 defeq 转移） |
| PA25 `TEWNSCJ_MERGED`(:5928) | **受益主体** | 收口转真（axiom 面标准三） |
| PA4 `aSpine5P4`/`bSpine5P4`(:178/:181, private) | 独立私有拷贝（同值） | 不受影响（后续统一可选，不在本项） |
| IneqClosureDefs `aSpine5`/`bSpine5`(:598/:601) | 桥的对端（bank 系数值体） | 不动 |
| PA21 `bank_TEWNSCJ`(:526)/`proj_bank_TEWNSCJ`(:2500) | 投影层 | 不动 |
| Assembly `nliRestTEWNSCJ`(:458) | G4 证书骨架 | 不动（证书债独立） |
| 单调回退通道 | 补后式 ⇒ 冻结前式 | opaque→def 保守：一切旧证明保持有效；反向（def→opaque）才破损 |

### (d) 保真论证

补后体 = sphere.hl:632/634 逐字（(a) 引文），与 in-repo 两处同值互证
（IneqClosureDefs:603 `example : (aSpine5, bSpine5) = (0.0560305,
-0.0445813) := rfl`）。`TEWNSCJ_MERGED` 冻结陈述文本一字不改。
axiom 面无回归（clone 探针实测：opaque 常数本就不进 `#print axioms`——
修复前 `real_model_tew` = [propext, sorryAx, Classical.choice, Quot.sound]，
修复后 `TEWNSCJ_MERGED` = [propext, Classical.choice, Quot.sound] 标准三，
无自引入 axiom）。修复方向唯一（换入参考件逐字体），无 junk 语义风险。

### (e) 风险

- **陈述修正 ≠ 全闭合**：`real_model_tew`/`pema`/`pemb`/`ztg4` 四切片仍
  sorry（各自 G4 证书债）；`nliRestTEWNSCJ` 骨架原位。PA25 sorry 计数
  101 → 100（clone 实测 100 条 "declaration uses sorry"）。
- **金标 build 待应用波**：clone 验证走探针仪器（㉛：拷贝 .lake/build 跨
  工作区 trace 判 stale，金标 `lake build` 只能在主工作区跑）；应用波验收
  `lake build Kepler.Text.PackingAuto25`，下游重编面 = clone 实测
  {PA3, PA4, PA18, PA21, PA25} 五件（PA25 导入闭包 59 件中 PA3 下游仅
  PA4/PA18/PA21 三件 + 本件）。
- **雷区预演**：隔离 clone 曾触发 ㉜ "URL has changed" 删包重克隆
  （mathlib）；已按 SOP 处置（杀并发 → pinned rev `905b9581` 核对 → 主仓
  构建产物 `cp -Rc` 回填 → 探针冒烟双跑稳定）。应用波若重建 clone 照抄
  本车环境配方。

### (f) 状态：**待批准**
（应用时闸参数建议：`SF_ITEM=41`，GATE_MODE=STATEMENT-FIX；审计对象
`Kepler.Text.a_spine5`/`Kepler.Text.b_spine5` +
`Kepler.Text.TEWNSCJ_MERGED`；namespace `Kepler.Text`；验收 = `lake build
Kepler.Text.PackingAuto25` 零新错 + `#print axioms TEWNSCJ_MERGED` 标准
三 + sorry 计数差 −1。隔离 clone 验证（2026-10-13）：探针链
PA3→PA4→PA18→PA21→PA25 全绿 exit 0（20s/10s/23s/32s/17s，零新警告，仅
既有 sorry/linter 噪）；桥 `rfl` 三例 + `#print axioms` 探针 exit 0。）

## 42. CertTM `TaylorM.sqrt` 证书粒度根治（`Dyadic.sqrtRel` 固定 2⁻⁸⁰ 相对粒度；var-at-point 宽度记账发散根治）— 分级 A（def 语义修正 · 内核证书基建）

**立案：2026-10-15，W8.1 df 发散破案随件（6ba98ca4 待批项"CertTM sqrt 粒度
修复提案"）+ 第三次发车执行波。** 前两波死于机器事故（1310 三线阵亡），WIP
全量打捞于 `/Users/zhangzhuo/c17_backup/clone_salvage/p4sf42.CertTM.diff`
（+172/−21，当日记账："sqrtRel 章主体"）。本波新 clone
（/tmp/p4sf42b，HEAD f75c305d；CertTM.lean 自 6ba98ca4 未动，diff 干净
应用）续完：sqrtRel 主实现 + reducibility decide 测试 + 受影响 leaf 重烤。

(a) HOL：无对应 HOL 语句——本件为纯机器侧内核证书基建（Dyadic 证书层是
Lean 侧新增设施，非 Flyspeck 移植物；reference/flyspeck 全树无 sqrt 证书
定义），故无 HOL 误抄可能；语义锚 = 在库 `Kepler/Interval/Sqrt.lean` 的
`Dyadic.sqrtI` 定义（本件不动其语句，仅新增 sqrtRel 相对粒度模式并将
`TaylorM.sqrt` 的证书源切换过去，切换前后的语义等价由 §(b) 内
`sqrtRel_sound`/`valid_sqrt` 内核证成）。

### (a) 出处与缺陷（机器侧；无 HOL 误抄，语义对应物 = Interval/Sqrt.lean 证书定义）

`Dyadic.sqrtI d s`（Sqrt.lean）返回证书 `⟨⟨s, d.e/2⟩, ⟨s+1, d.e/2⟩⟩`——
粒度按 **表示**（radicand mantissa 位数）取，不按 **值**：同一实数值，
mantissa 越小证书越肥。极端案 = var-at-point / 面盒退化 radicand：
`√⟨4,0⟩` 拿 `[2, 3]`（绝对宽 1，相对宽 ~50%），而 mantissa ≥ 2⁸⁰ 的
radicand 拿 ~2⁻⁸⁰ 相对宽。后果两级：

1. **宽度记账发散**：内核 `TaylorM.sqrt` 模型与镜像在同值不同表示的
   radicand 上走出不同宽度（emit_lean.py:489-495 W8.1 var-at-point 阻塞
   记档；6ba98ca4 雷区三条"var-at-point 粒度需 CertTM 提案走闸"）。
2. **值重写救不了**（已否决记录在案）：mul-wrap √(x·2^120)·2^−60 门爆
   c=−1.2e222——sqrtI 粒度按表示，值重写只挪表示不改宽度记账，且 TM 模型
   携 2^60 绝对宽度因子毁下游加性语境。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/42-certtm-sqrtrel-granularity.patch`
（git diff 全量，两文件；对 f75c305d 干净应用已验）：

1. **CertTM.lean（+172/−21，打捞件 + 本章收口）**：
   - `Dyadic.sqrtRel`：**固定相对粒度 sqrt 证书**——radicand 先按 **值**
     上移 `⟨d.m·2^160, d.e⟩`（`toReal_mul_pow`：mantissa 移 = 值缩），
     `sqrtI` 验 `s′² ≤ d.m·2^(d.e%2)·2^160 < (s′+1)²`，返回
     `[s′, s′+1]·2^(e/2−80)`（`toReal_e_sub_80`：指数移 = 纯表示去缩）：
     每个 radicand 无论 mantissa 多小，相对宽度恒 ~2⁻⁸⁰
     （`√8 = ⟨8,0⟩`：`[2.8284…, 2.8284…+2⁻⁸⁰]`，裸 `sqrtI` 给 `[2, 3]`）。
   - 私件四枚 `toReal_e_sub_80`/`toReal_mul_pow`/`sqrtRel_sound`（ℝ 括号
     逐端去缩，√(d·2^160)·2⁻⁸⁰ = √d）/`sqrtRel_lo_nonneg`。
   - **reducibility decide 测试两枚**：`sqrt8_rel_cert`
     （⌊2^80·√8⌋ = 3419358580004036860274166）与 `sqrt4_rel_cert`
     （⌊2^80·√4⌋ = 2^81）——纯内核 BigInt 双比较（无 Int.sqrt）；
     `sqrt8_rel_bounds`/`sqrt4_rel_bounds` 转 ℝ 语义括号。
   - 消费面切换：`TaylorM.sqrt` 三证书 `sqrtI` → `sqrtRel`；生成器镜像
     `evalTMHullFill`/`evalTMHullFill2`/`evalTMHullFill2B` 的
     `sqrtMantissa` → `sqrtMantissaRel`（新增 def
     ⌊√(d.m·2^(d.e%2)·2^160)⌋，d.m < 0 时 0，与正性门同形）；
     `valid_sqrt` 证明体换引新私件，**冻结语句一字不改**。
   - 区间路线零改动：`evalIParams`/`evalIParamsFill`/`MonoTree.slotsDeep`
     照旧裸 `sqrtI`/`sqrtMantissa`（b661ff07 DomOK 区不踩，emit_lean.py
     本波零改动——pad 路径无需动：重烤走内核 `evalTMHullFill2` 编译跑，
     不经 Python 镜像）。
2. **C549Mono.lean（受影响 leaf 重烤示范，+15/−15）**：新码下 12 枚
   `checkPosTMHull decide` 翻假（`M₀.sqrt p` 拒旧证书 → orElse fallback →
   零阶模型过宽失正性；重烤前 broken 中间态实测 `C549MonoFold5` 泄漏
   sorryAx）——用新 `evalTMHullFill2` 于同一 (expr, box) 编译跑重算
   三元组（miniP/miniDP/C549MonoPF1-5/DP1-5；粒度字段一字不动仅换
   mantissa 值；mini 试金 radicand ⟨1,−1⟩：22 →
   27354868640032294882193329 ≈ 22·2^80）+ docstring 记重烤出处。
   **全部定理陈述文本零改动**（decide 命题逐字同，仅参数 def 体换值）。

先例对照：SF-39（占位语义 → 真内容）；本件无 HOL 误抄，是机器侧 def 体
修正（证书粒度语义），分级同 SF-39/40（def 语义修正类）。

### (c) 消费面核实（全树 grep + clone 实测）

| 消费点 | 性质 | 判定 |
| --- | --- | --- |
| `TaylorM.sqrt`（CertTM:377） | 内核消费体 | sqrtI → sqrtRel（本件主体） |
| `evalTMHullFill`/`2`/`2B` | 生成器镜像 | sqrtMantissa → sqrtMantissaRel |
| `valid_sqrt` | 冻结语句 | 语句零改；证明体引 sqrtRel_sound/lo_nonneg |
| `evalIParams`/`evalIParamsFill`/`MonoTree.slotsDeep` | 区间路线 | 零改动（DomOK 区不踩） |
| C549Mono 12 decide（TM 路线 leaf 链） | 受影响主体 | 重烤后重建绿 12/12，axioms 无 sorryAx |
| TM 路线舰队（197 模块/18,477 站点，grep checkPosTMHull/evalTMHullD2 口径） | 下游 | 需逐模块重编定账：C549ProdS0040 诚实重编实测 40 枚翻假（DP/PF 同病，重烤处方同 C549Mono）；舰队重烤 = 应用波 |
| checkPosI 舰队（区间路线） | 下游 | 零影响（证书语义不变） |

### (d) 保真论证

`sqrtRel_sound`：√(d·2^160)·2⁻⁸⁰ = √d（值移可去），bracket 逐端去缩；
`sqrt8_rel_cert`/`sqrt4_rel_cert` 内核 decide 实证 reducibility；
`#print axioms` 全零自引（clone 实测：sqrt8/sqrt4_rel_cert 与
sqrtMantissaRel 仅 [propext]；sqrtRel_sound/sqrtRel_lo_nonneg/
toReal_e_sub_80/toReal_mul_pow/valid_sqrt/checkPosTMHull_sound/miniSemantic
= 标准三；重烤后 C549MonoFold1/3/5 = [propext, Quot.sound]，miniFolded
= [propext, Quot.sound]）。方向保守：成功的新证书区间恒不肥于旧证书
（相对 2⁻⁸⁰ vs 表示界），`M₀.sqrt` 失败则 orElse 裸区间 fallback 原样
保底——soundness 面无新径，纯紧化。

### (e) 风险

- **舰队重烤波未完（主要尾债）**：197 模块全量重编未跑（decide 成本
  10⁻¹–10² s/枚）；已探二件：C549Mono 翻 12 枚（已烤绿）、
  C549ProdS0040 翻 40 枚（处方同，未烤）。舰队免烤/需烤名单须整舰队
  诚实重编后定账；重烤全机械（`evalTMHullFill2` 编译跑 → 三元组换值），
  可批量。
- **trace 毒缓存雷区升级（入册建议：㉛ 增补）**：`cp -Rc` 拷 .lake/build
  跨工作区后 lake 对源变更判 fresh（CertTM 首趟全量 build 假绿 ~60s）、
  乃至 olean 缺失仍判 fresh（ProdS0040 首趟跳建假绿）——诚实重编前必须
  rm 目标 {olean,ilean,trace,*.hash}；clone 验证一律以
  "Building <目标>" 行为准。
- **decide 成本**：rel mantissa 增 ~80 二进制位，内核双比较上浮
  ~20-30%（mini 22 → 26 位十进制）；实测无爆炸（C549Mono 全模块重建
  与旧码同量级）。

### (f) 状态：**已批准（用户 SF-42 批规格）；本波=模式落地+受影响 leaf 重烤示范完成；舰队重烤=应用波待命**
（隔离 clone /tmp/p4sf42b 实测：CertTM 自新源重建绿；C549Mono 重烤重建
绿 12/12；默认闭包 `lake build` 9359 jobs 绿；axiom 审计标准三零。
闸参数建议：`SF_ITEM=42`，GATE_MODE=STATEMENT-FIX；审计对象
`Kepler.Interval.Dyadic.sqrtRel_sound` + `Kepler.Interval.Cases.C549MonoFold1`；
验收 = `lake build Kepler.Interval.Cases.C549Mono` 零新错 + 上述 axiom
标准三零 + 舰队重烤波按 (e) 清单续。）
## 43. PA22 `localAnnulusInequalityP22` 桩换本体（pack_defs.hl:202-203 逐字；四占位消费件真证闭合）— 分级 A（def 语义修正 · 桩换本体）

**立案：2026-10-19，A6③ 落地随件待批项（d82bc7d1 记档："待批项: :302 桩换
PackingAuto2:541 localAnnulusInequality 本体(语句级 SF)后两桥闭合占位"），
用户批准（"：302 桩的 SF 提案：批准"）。** 执行 clone /tmp/p4a63（A6③ 原
clone，包 origin 已 fix_pkg_origins 归一），build 绿 8698 jobs。

(a) HOL：pack_defs.hl:202-203 逐字 `let local_annulus_inequality =
new_definition \`!(V:real^N->bool). local_annulus_inequality V =
sum V ( \v. lmfun (hl [vec 0;v]) ) <= &12`;;`——PA22 :302 桩
`localAnnulusInequalityP22 (V : Set V3) : Prop := True` 换为 PA2:541-542
真定义 `localAnnulusInequality`（同一 HOL 定义的一次性 Lean 移植：
`setSum V (fun v => lmfun (hl [0, v])) ≤ 12`）的定义转发；下游四件签名零改。

### (a) 出处与缺陷（桩空转）

:302 桩 `:= True` 使四件既有占位消费件空转：DLWCHEM/DLWCHEM_VECTOR_sum 的
`absurd trivial hloc`（`¬True` 即荒谬）与 XULJEPR/XULJEPR_VECTOR_sum 的
`trivial`——证明与真身无关，语句在桩语义下为空壳。A6③ 已对照真定义搭好
全链（DLWCHEM_full/XULJEPR_full/DLWCHEM_VECTOR_sumReal/XULJEPR_VECTOR_sumReal
零欠债真证 + 两枚换桩桥 `DLWCHEM_of_stub_bridge`/`XULJEPR_of_stub_bridge`，
给定 `∀ U, P22 U ↔ localAnnulusInequality U` 即零成本闭合占位），只欠此
定义本体到位。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/43-pa22-localannulus-stub.patch`
（对 d82bc7d1 干净应用已验；65+/54−，单文件）：

1. **:302 桩换本体**：`:= True` → `:= localAnnulusInequality V`（定义
   转发；docstring 同步 NEEDS→HOL 记档）。
2. **四占位消费件迁至桥/Real 版之后真证**（原 :10050-10110 带迁至文件尾，
   语句逐字冻结）：
   - `DLWCHEM_VECTOR_sum`/`XULJEPR_VECTOR_sum`：ℕ-transport 胶水——冻结
     陈述的自动绑定 `n` 被 binrel% 上抬为 ℝ（`hsize.2 : ↑V.ncard = n`），
     `hncard`/`hnN`（Nat.cast_lt）/`hcast`（Nat.cast_sub 链）三件 cast
     搬运后喂 Real 版；axiom 探针**零 sorryAx**（本波核心增量：两 GIANT
     由占位空壳转零欠债真证）。
   - `DLWCHEM`/`XULJEPR`：经 A6③ 换桩桥闭合（iff 取平凡方向），携带
     DLWCHEM_full/XULJEPR_full 链内既有上游债（A6③ 已记档，非本波新增）。
3. **既有语句逐字冻结**：四件定理签名一字未动；:302 仅换体。

### (c) 验收

clone build 绿 8698 jobs；axiom 探针：`DLWCHEM_VECTOR_sum`/
`XULJEPR_VECTOR_sum` 零 sorryAx，`DLWCHEM`/`XULJEPR` 仅 propext/
Classical.choice/Quot.sound/sorryAx 白名单轴（上游债既记）；文件 sorry
面持平（本波零新增债）。闸参数：`SF_ITEM=43`，GATE_MODE=STATEMENT-FIX，
验收定理 `DLWCHEM`。

## 44. PA24 `p24_cell_cap_dihX` 冻结语句补五前提（hw1+hw3+hw4+hn+hwit；HL 原生前提整条丢失+骨架期自由变量抽象丢约束）— 分级 A（statement 保真修正 · 假陈述修复）

**立案：2026-10-19/20，REUHADY1 六发波发现+七发波 HL 对账补全，用户批准双轨
（"并行"）并过目终修法（"SF 44: 同意"）。** 对象 = PA24 冻结直 sorry 2 号位
`p24_cell_cap_dihX`（scaffold 2，HL REUHADY.hl 2386-7358+8187-8241 的逐臂
体积比例义务）。车道七发波已在树上真证应用后的全部承重件
（`p24_cell_cap_dihX_strong` 逐臂派发 + k=3/4 帽石 + kit，25 件 axiom 三零）。

(a) HOL：REUHADY.hl:2818-2823 逐字 `(NEW_GOAL \`!X. mcell_set V X /\
~NULLSET (X INTER D) ==> vol (X INTER D) = vol (D) * (dihX V X (u0,u1)) /
(&2 * pi)\`);`——HL 本体 (i) 自带非零测迹前提 `~NULLSET (X INTER D)`；
(ii) 锥参数 `D` 从非自由变量：HL :1254 `c = max b (hl[u0;u1]/sqrt 2)`、
:1978 `r = min 1 (min r1 r2)`、:2783 `d = max c (max d1 d2)`（走廊章构造
内定窄性）。骨架期把 `r d` 抽象成自由变量只带 (0,1)/(0,1] 界，三条结构性
约束全丢 → 按现前提为假（非仅难证）。

### (a) 出处与缺陷（三失真点）

1. **k=2 双锥窗（六发波发现）**：rconeGt 的 `d` 为余弦参数，mcell2 双锥窗
   = arccos(hl[u0,u1]/√2)；`d < hl/√2` 时锥帽方位角窗 `(arccos a, arccos d]`
   正体积漏出双锥，切片恒等式失效（LHS > 比例式右端）。
2. **k=3/4 逐臂窄性（七发波补证）**：hull 体积式需远面距离 `r ≤ r1/r2` 与
   锥不交 `d ≥ d1/d2`（SMALLEST_ANGLE_LINE 方向余弦极大值）——PA23
   `grutoti_cell_vol` 的 `hw3/hw4` 即此 Lean 化。
3. **HL 原生 `~NULLSET` 前提整条丢失**：无迹前提则 junk 侧体积恒等式无意义。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/44-pa24-cellcap-dihx-strong.patch`
（对七发波树干净应用已验；+16/−3）：冻结语句加五前提
`hw1`（hl/√2 ≤ d）+ `hw3`/`hw4`（k=3/4 逐臂，PA23 同形）+ `hn`（¬nullSet
(X ∩ cap)）+ `hwit`（cellParamsD 见证三元组）；证明体 `sorry` →
`exact p24_cell_cap_dihX_strong …`（七发波真证 axiom 三零）。形态裁决
Option A 单语句加前提（HL 本体即单语句 premise-minimal 形；PA23 SF-28+29
先例；记账锚不拆；消费合同单一）。**影响面**：唯一消费者 REUHADY1:3625
装配线。

### (c) 验收与应用计划

应用与走闸随八发波同批：hnullarm 本体 + scaffold 3-2 加强形 cover（五前提
供给方）+ REUHADY1 换接 + 本 patch 应用一次成型；走闸时以全量波差为最终权
补丁归档（statement 变更部分即本 patch 逐字不变），STATEMENT-FIX 模式
`SF_ITEM=44`；应用后 PA24 直 sorry 2→1。八发波交付报告给用户终验。

## 45. PA24 `p24_cell_cap_dihX` hwit 前提加门（SF-44 应用批 1 行联动微调；门下 hwit 为装配链正式接口形）— 分级 A（statement 保真修正 · 死前提预防）

**立案：2026-10-20，pa24reuhady 车道九发波侦察产出（9gen_SF45_draft.md），
编排者代车道正式入册；用户批准（2026-10-20，"SF 45: 同意"）——批准「门下
hwit」为 REUHADY1 装配链正式接口形 + SF-44 应用批 hwit 行 1 行联动微调；
七发波无门件 `p24_wedge_setSum_eq_azim_strong` 的退役/加门改造二选一仍按
§45.3-1 届时再呈。** 对象 = SF-44 批准补丁的 `hwit` 前提行
（未门形）。SF-44 应用批的装配链供给侧（scaffold 3 加强形 cover）按
HL :1531-1629 走廊覆盖 + 门下见证推导 `?k vl` 见证，恰在 `~NULLSET` 门下
成立；无门形 `hwit` 对退化见证角点胞（全 witnesses 非 [u0,u1] 头，
`initialSublist [u0,u1] p.2` 不可满足）无货源 ⇒ SF-44 应用后该前提成为
不可供货死前提，:3625 换接在角点胞卡死。

(a) HOL：REUHADY.hl:2818-2823 逐字 `(NEW_GOAL \`!X. mcell_set V X /\
~NULLSET (X INTER D) ==> vol (X INTER D) = vol (D) * (dihX V X (u0,u1)) /
(&2 * pi)\`);`——HL 本体的见证由走廊覆盖链在 `~NULLSET (X INTER D)` 门下
推导，从不要求全族无条件 hwit；SF-44 的 `hn` 前提即此门的单胞形，本项把
`hwit` 同步收窄为门形（`¬ nullSet (X ∩ conicCapP24 u0 u1 r d) → 三元组`），
门在消费点（仅非零测臂）恒真，数值语义与 SF-44 批准文本一致。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/45-pa24-hwit-gate.patch`
（相对基准 = 44 补丁应用后的树；+2/−1）：`hwit` 行加门 + 消费点
`hwit.1/hwit.2.1/hwit.2.2` 改门下取元组（门由装配侧 hX/hn 供证）。消费侧
适配器 `p24_wedge_setSum_eq_azim_gated`（九发波已入树，零语句改动）与本项
同接口形。七发波无门件 `p24_wedge_setSum_eq_azim_strong`（当前零消费者）
在本项批准后由后续清理批退役或加门改造（二选一，届时再呈）。

### (c) 验收与应用计划

与 SF-44 应用同批一次成型：scaffold 3-2 加强形 cover（§45.4 施工图四件：
走廊覆盖/门下见证/hnullarm 全族/hcov 主体）+ 本 patch 应用 + :3625 换接
gated 适配器，走闸以全量波差为最终权补丁归档（statement 变更部分 = 44
补丁逐字 + 本 patch 逐字），STATEMENT-FIX 模式 `SF_ITEM=44`（statement
净变更为两 patch 之叠加）；应用后 PA24 直 sorry 2→1。若本项不批，SF-44
仍按批准原文逐字应用（:3625 换接以无门强件为目标，角点胞受阻如实记账，
直 sorry 收口顺延）。

## 46. PA24 `p24_cap_wedge_cover`（scaffold 3）冻结覆盖语句点态形 → HL 测度级原文形（移植期真加强形降级为忠实形）— 分级 A（statement 保真修正 · 过度加强形修复）

**立案：2026-10-20/21，十二发波两墙定位产出（12gen_LEDGER_updated.md），编排者
代车道入册；用户批准（2026-10-20，"新Sf：批准"）——scaffold 3 覆盖结论恢复为
HL 忠实测度级形即行生效；十三发波按 §46(c) 执行：patch 起草→编排者核→
STATEMENT-FIX 闸 SF_ITEM=46→应用后 PA24 直 sorry 1→0（REUHADY1 链仅余
AJRIPQN inherited）。** 对象 = scaffold 3（PA24 :3366，现全文件唯一直 sorry）
冻结语句的覆盖结论：现形为点态 `cap ∩ wedgeGe ⊆ ⋃楔族胞`。十二发波逐臂对位
HL D6 覆盖段（REUHADY.hl :7395-7790）证明该点态形是移植期**真加强**：HL 原生
为**测度级**（`E DIFF ⋃族 迹 ⊆ ⋃零迹迹` + NEGLIGIBLE_SYMDIFF，REUHADY.hl
:7483-7790）。点态加强形按现树状态**不可证**（非仅难证），两墙：
（墙 A）k∈{2,3} 叶表胞非零测性 = R1-GIANT 人质（edgeX 入族需 `¬nullSet`，
`k2Case`/`k3Subset` 为 PA11 open 核心，全树只消费未证明；走廊覆盖必产 i=2/3
胞，无绕行；HL 原生测度级论证不需要此点态性）；（墙 B）边界扇点若仅被 W2-侧
胞覆盖则点态结论失效，HL 原生靠 NEGLIGIBLE_SYMDIFF 吸收，点态形需扇邻接 +
三面角径向界等树内不存在的新组合结构。与 SF-44 同型的移植期语句失真（方向
相反：44 是骨架丢约束，46 是移植期加强度）。

(a) HOL：REUHADY.hl:7483-7790 逐字 D6 覆盖收尾——零迹自毁 + NEGLIGIBLE_SYMDIFF
的测度级覆盖；本提案即把冻结语句的覆盖结论恢复为该忠实形（测度级 ⊆* /
对称差零迹形，精确 hunk 由十三发波车道按 HL 原文起草后随批归档）。

### (b) 修复路径与影响面

- 修法形态：scaffold 3 覆盖结论点态 `⊆` → 测度级（volume/NEGLIGIBLE 形）；
  前提与半径产出部分（0<r≤1、0<d<1）不动。patch 由十三发波车道起草，归档后
  走 STATEMENT-FIX 闸（`SF_ITEM=46`）。
- **修订则十二发波 kit 六件直接装配收口**（车道实证：连续性 + 有限族 + 闭性
  路线可复原测度级；`p24_mcell4_leaf_nonnull` 等件零 R1 债）。k∈{2,3} 臂在
  测度级形下不再需要 edgeX 非零测性入族——墙 A 解除。
- 下游消费合同不变：`p24_cap_wedge_cover_strong` 等消费件的**语句冻结不动**，
  证明体改接测度级覆盖（体积求和恒等式只需 a.e. 覆盖，nullSet 差异不进 vol）。
- 不修订的替代路（若用户不批）：按 12gen_LEDGER 十三发波处方闭 R1 两核心
  （`k2Case` :126-656 / `k3Subset` :740-906，PA11，GIANT 级）+ 边界扇组合
  结构新数学（树内无件，工作量显著更大且偏离 HL 原生论证）。

### (c) 验收与应用计划

十三发波首机械动作：patch 起草 → 编排者核（语句净变更 = 本提案批准形逐字）
→ STATEMENT-FIX 闸 `SF_ITEM=46` → 应用后 PA24 直 sorry 1→0（REUHADY1 链仅余
AJRIPQN inherited）。应用批随带 kit 装配收口件走全量波差归档闸（§44(c)/§45(c)
先例）。

## 47. PA24 `p24_cap_wedge_cover_strong` 末合取点态 hcov → 测度级零迹形（SF-46 联动：墙 B 的 capstone 载体）— 分级 A（statement 保真修正 · 过度加强形修复）

**立案：2026-10-21，十三发波车道产出、编排者核（13gen 波差语句净变更恰两处，
hunk 1 = SF-46 批准形逐字，hunk 2 = 本项——车道超出任务书"只许一处"约束时
如实上报，本项即对该越界的正式立案）；用户批准（2026-10-21，"批 SF-47"）
——capstone 末合取测度级形即行生效，与 SF-46 联合走闸入库。** 对象 = capstone 件
`p24_cap_wedge_cover_strong` 末合取的点态覆盖 `∀ x ∈ cap ∩ wedgeGe, x ∈
⋃₀ wedgeCells`。机理：该合取即十二发波**墙 B 的冻结载体**——scaffold 3 经
SF-46 恢复测度级形后点态合取无货源（点态与测度级之差恰为边界扇零迹，HL
原生 NEGLIGIBLE_SYMDIFF 吸收、从不点态承诺）；编排者在 §46(b) 预写的
"消费件语句冻结不动"条款不成立（当时误判测度级+零迹侧可复原点态——不可），
以本项修正。

(a) HOL：REUHADY.hl:7483-7790 逐字（同 SF-46 (a)）——HL 的覆盖承诺自始为
测度级零迹形；本项把 capstone 件的对应合取恢复为忠实形（nullSet 对称差式，
与 scaffold 3 新形同构）。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/47-pa24-coverstrong-msr.patch`
（+2/−2）：末合取点态 → `nullSet ((cap ∩ wedgeGe) \ ⋃₀ (X∩cap∩wedgeGe)''
wedgeCells)`，其余合取（hw3/hw4/hnullarm/hwit 族）零改动。十三发波车道已在
克隆实测：两 hunk 联合应用后 scaffold 3 真证收口，**PA24 直 sorry 1→0**，
PA24/PackingConcl/根全树 8700/8715/9359 jobs 三绿，axiom 28 件探针 EXIT=0。

### (c) 验收与应用计划

与 SF-46 应用批（13gen 全量波差）一次走闸：语句净变更 = SF-46 ∘ SF-47 两
patch 叠加逐字（§44+45 先例），全量波差最终权归档，STATEMENT-FIX 模式
`SF_ITEM=46`（净变更含两 patch 时以全量波差归档件为准）。若不批：13gen
交付件不入库，PA24 维持 12gen 态（直 sorry 1），capstone 点态合取按十三发波
处方等待 R1-GIANT 路线（k2Case/k3Subset）+ 边界扇组合结构。

### (d) 附带记账（非本项范围）

新 taint 一条：`p24_edgeX_of_leaf23`（十三发波新件）消费 PA2 `RVFXZBU2_concl`
shim（:5496，pack_concl.hl:145-147，R3 家族）——替代路为 LEPJBDJ k∈{2,3}
content（R1-GIANT，墙 A 复活），按"覆盖链 R1-free"取向定案。该 shim 列入
未来 shim 清理批盘点（同 MXI_EXISTS_concl 成环案）。

## 48. PA12 `LEFT_ACTION_LIST_PROPERTIES` 新件立案（S₃ action kit 补尾固定 `hfix`；AJRIPQN B1 前置）— 分级 B（新增陈述保真立案）

**立案：2026-10-21，AJRIPQN 分期侦察报告（`docs/scouts/ajripqn-scout.md` §4 B1）
产出；用户批准（2026-10-22，"SF-48：批准。AJRIPQN B1：发"）——B1 车道即行
开工。** 对象 = **新增**定理 `Kepler.Text.LEFT_ACTION_LIST_PROPERTIES`（落
PA12），不触碰任何冻结陈述。机理：HOL `permutes` 是 complement-fixing
（`!x. ~(x IN s) ==> p x = x`），Lean 的 `permutes p s := ∀ x, x ∈ s ↔ p x ∈ s`
不含尾固定；本件读 index 3（`ul.length = 4`），弱式允许 p 把 index 3 换成
junk 点，陈述为假/不可证。`hfix` 是 HOL 语义的显式化，补后式 ⇒ 弱式
（丢弃 `hfix` 即回退），无下游破坏。

(a) HOL：marchal2.hl:4460-4474 逐字：

```hol
let LEFT_ACTION_LIST_PROPERTIES = prove_by_refinement (
 `!V ul p.
    packing V /\ saturated V /\ barV V 3 ul /\
    hl (truncate_simplex 2 ul) < sqrt (&2) /\ sqrt (&2) <= hl ul /\
    p permutes 0..2 /\
    xl = left_action_list p ul
    ==> xl IN barV V 3 /\
        omega_list_n V xl 2 = omega_list_n V ul 2 /\
        omega_list_n V xl 3 = omega_list_n V ul 3 /\
        mxi V xl = mxi V ul`,
```

HOL `permutes` 语义（`reference/flyspeck/azure/hol-light-nat/Library/permutations.ml:9`）：

```ml
let permutes = new_definition
 `p permutes s <=> (!x. ~(x IN s) ==> p(x) = x) /\ (!y. ?!x. p x = y)`;;
```

即 complement-fixing，自动固定所有 `j ≥ 3`。

### (b) 陈述宪章

存档 `docs/statement-fix-proposals-patches/48-pa12-left-action-list-properties.patch`
（对 PA12 EOF 追加，+17 行、零既有行改动；`patch -p1 --dry-run` EXIT=0）。
批准形（逐字）：

```lean
theorem LEFT_ACTION_LIST_PROPERTIES {V : Set V3} {ul xl : List V3} {p : Equiv.Perm ℕ}
    (hpack : Packing V) (hsat : saturated V) (hbar : barV V 3 ul)
    (h1 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (h2 : Real.sqrt 2 ≤ hl ul)
    (hperm : permutes p (Set.Icc 0 2))
    (hfix : ∀ j : ℕ, 3 ≤ j → p j = j)
    (hxl : xl = leftActionList p ul) :
    barV V 3 xl ∧
      omegaListN V xl 2 = omegaListN V ul 2 ∧
      omegaListN V xl 3 = omegaListN V ul 3 ∧
      mxi V xl = mxi V ul
```

### (c) 验收与应用计划

B1 车道在 PA12 落地该陈述并真证（零 sorry/零 sorryAx，普通闸；新增件不是
STATEMENT-FIX 模式）。陈述须与 (b) 逐字（binder 名与换行可异，命题结构不可
动；不得删 `hfix`、不得加前提）。PA12 禁止 import PA13/PA14（环）；S₂ 模板
`LEFT_ACTION_LIST_1_PROPERTIES_ALT`（PA14:792）按 §0' 复制私件体例，不反向
import。B2 消费：PA14 重落 `RVFXZBU_p14`/`ynhyjit_i3_p14`，PA17 的 `hRV`
一行改接；PA10 源件保留为 off-path orphan（另账）。

### (d) 记账

- `PERMUTES_TRIVIAL`（PA5:135）仍 sorry，本件禁用。
- 本件不进入 `pack_concl` 逐字接口；它只服务 AJRIPQN 五阶段的 S₃ 对称性。

### (e) 应用记录（2026-10-22）

B1 车道落地，提交 `ae475e70`，PA12 md5 `4674279c69612855ca563624ced18ade`；
新增 716 行 `p12_` 私件 + 公开定理。闸 PASS @LEFT_ACTION_LIST_PROPERTIES；
`#print axioms` = `[propext, Classical.choice, Quot.sound]`（零 sorryAx）；新增区
零 sorry / 零 axiom / 无 native_decide。构建：clone PA12 8695 jobs、
Text roots 8789 jobs、主仓 `lake build Kepler` 9359 jobs 全绿。陈述与 (b) 逐字
相同（`h2` 未消费但按冻结形保留）。B2 待办：PA14 重落
`RVFXZBU_p14`/`ynhyjit_i3_p14`，PA17 `hRV` 一行改接。

## 49. PA21 `bank_BIXPCGW9455898160` 符号纠正（HOL `> -0.00569`，Lean 误写 `> +0.00569`）— 分级 A（statement 保真修正 · 假陈述修复）

**立案：2026-10-22，`nliPackNonlinearRest` 侦察车道
（`docs/scouts/nli-rest-scout.md` §2.3）产出，编排者复核 HOL 原文与
pipeline AST；用户批准（2026-10-22，"Sf 批准"）——本项即行应用。** 对象 = PA21:596
`bank_BIXPCGW9455898160` 的结论常量符号。机理：HOL `ineq.hl:985` 为
`gamma4fgcy ... > -- #0.00569`（HOL `--` 是一元负号），同条 doc 自述
"If X is a quarter, then γ(X,L) ≥ -0.00569"；pipeline 的 AST
`records[35]` 与 case RPN 也按 `-0.00569` 编码。Lean 写成 `> +0.00569`，
比 HOL 强 0.01138——该 Prop 在给定 box 上为假，证书永远粘不上。
`Assembly.lean:677-681` 的 docstring 自己记了 "`-- #0.00569` 双重负号"，
但转录结论写反。

(a) HOL：`reference/flyspeck/text_formalization/nonlinear/ineq.hl:982-998`
逐字：

```hol
add
{
  idv = "BIXPCGW 9455898160";
  ineq = all_forall `ineq
   [(&2 * hminus, y1, &2 * hplus);
    (&2,y2, &2 * hminus);
    (&2,y3, &2 * hminus);
    (&2,y4, &2 * hminus);
    (&2,y5, &2 * hminus);
    (&2,y6, &2 * hminus)
   ]
    (gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun > -- #0.00569) `;
  doc =   "
  OXLZLEZ.mod 'gamma_qu'
     If $X$ is a quarter, then $\\gamma(X,L)\\ge -0.00569$.";
  tags=[Marchal;Flypaper["OXLZLEZ";];Cfsqp;Clusterlp;Tex;Xconvert;Branching;Split[0]];
};;
```

（`--` 为一元负号；同源 `sphere.hl:632/634` 的
`b_spine5 = -- #0.0445813` 是负数用法。）

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/49-pa21-bixpcgw-sign.patch`
（+1/−1）：`> 0.00569` → `> -0.00569`；其余零改动。
`patch -p1 --dry-run` EXIT=0。

### (c) 验收与应用计划

用户批准后按 STATEMENT-FIX 模式应用（`SF_ITEM=49`，工作树 diff 与 patch
多重集相等）；应用后 PA21 构建 + `bank_BIXPCGW9455898160` /
`nliRestBIXPCGW9455898160` 探针。pipeline 侧已按 `-0.00569` 生成，无需重产。
若与 euler 任务 4 的 PA21 交付冲突，以本 patch 为最终权（一行，手工重放）。

### (d) 附带记账

- 59 个 nliRest 源中唯一陈述级问题；其余为证书/规模问题
  （19 已解 / 22 无 case 模板 / 18 硬解）。
- 本件在 e2e 锥内：`nliRestBIXPCGW9455898160`（Assembly:682）→
  `nliPackNonlinearRest` → 分量 1/6 `pack_nonlinear_non_ox3q1h`。

## 50. PA18 `CFFONNL` 前提回归 HOL 原序（`hne : X ≠ ccCell V ul`；A7 `pa18_ccCell_swap` 假陈述整体删除）+ PA25 `MCELL4_LEAF_S_LEAF` 二分装配按 HOL 原文改回两支构造性 — 分级 A（statement 保真修正 · 假陈述修复）

**立案：2026-10-23，lane pa18a7（T）反证钉死 A7 为假 + 本线（sfcffonnl）独立
核对与执行版补丁草案，编排者→用户批准流程。** 对象 = PA18 冻结链
`CFFONNL`（PA18:4623 现行行；proof 内部 step 10 消费假陈述 A7 的 sorry，
sorryAx 由此流入）与其唯一项级消费者 PA25 `MCELL4_LEAF_S_LEAF`
（PA25:2938 现行号）。T 的反证四件套（`pa18_ccCell_swap_ne` 等四件真证，
axiom 标准三）已在树上，本 SF 保留为永久公共资产。

(a) HOL：leaf_cell.hl:2178-2181 逐字 `let CFFONNL = prove_by_refinement(\`!V ul X. packing V /\ saturated V /\ leaf V ul /\ X IN mcell_set V /\ {EL 0 ul,EL 1 ul} IN edgeX V X /\ ~(X INTER cc_A0 ul = {}) /\ ~(X = cc_cell V ul) ==> (X = cc_cell V [EL 1 ul;EL 0 ul;EL 2 ul])\`)`——HOL 前提是不等式 **`~(X = cc_cell V ul)`（原序 ul）**，结论才是换位序 `[EL 1;EL 0;EL 2]`。Lean 移植把前提误植为换位序 `X ≠ ccCell V [EL 1, EL 0, EL 2]`（PA18 现行 :4628），与 HOL 唯一偏离点即此（he/hA 两前提逐字吻合）。HOL 证明的方向裁决步靠该前提直接矛盾闭合，全程不需要任何 swap 引理——A7（`ccCell V ul = ccCell V [u1,u0,u2]`）是被 T 的 `pa18_ccCell_swap_ne` 机器反证的**假陈述**（两取向 cc 胞分居茎平面两侧闭半空间：`chi_msb_swap_01` 反对称 + `cc_pe_exists` 特征性质选相反端点 + `CELL3_NONDEG`/`K4_CHI_MSB_POS`/`CC_CELL34` 半空间论证）。

### (a2) 本线对 T 处方的唯一修正（PA25 消费侧）

T DELIVERY §5.1 写"不等式支改供原序 hne（反得等式而爆炸）"。**静态核对
判定 absurd 形对修复后形态不成立**：CFFONNL 结论在 HOL 与修复后的 Lean 中
都是**换位序**等式，与原序 `hEq : ¬(mcell4 = ccCell [EL 0,EL 1,u])` 非同一
命题，`absurd` 类型不合；且 `mcell4 = 换位胞` 与 `mcell4 ≠ 原序胞` 可同时
为真（两胞不等正是反证内容），无矛盾可爆。正确装配 = HOL 原文
OXLZLEZ3.hl:1980-2053 的**两支构造性**形态（:1990 把
`premises ∧ ~d ==> e` 改写为 `premises ==> d ∨ e` 后 :2019 STRIP）：第一支
（:2020-2032）原序等式 + AJRIPQN 原序钉 `cc_ke 原序 = 4`（s_leaf 左析取支）；
第二支（:2034-2052）CFFONNL 给出换位序等式 + AJRIPQN 换位序（leaf 经
ZASUVOR，:2041）钉 `cc_ke 换位 = 4`（右析取支）。Lean `s_leaf`
（PA25:380-382）本就是对两茎序对称的析取定义（HOL OXLZLEZ3.hl:24-25 逐字），
两支皆可直接闭合。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/50-cffonnl-hol-original-order.patch`
（对基线工作树 dry-run 干净应用 + 往返字节一致已验；228 行，PA18 5 hunks
+ PA25 3 hunks；PA18 直 sorry 32→31，PA25 81 不变）：

1. **PA18 `CFFONNL` 前提回归原序**（1 行）：`hne : X ≠ ccCell V ul`。
   结论一字不动。保真说明：HOL :2181 前提逐字；换位只在结论，是 HOL 原文形。
2. **PA18 证明体 3 行**：step 0 两行 `rw [e1,e0,e2] at hne ⊢` /
   `rw [pa18_getD3_1,pa18_getD3_0,pa18_getD3_2] at hne ⊢` 去掉 hne 目标
   （原序 hne 无需改写）；step 10 第一支 `rw [hXYc, pa18_ccCell_swap …]`
   → `exact absurd hXYc hne`（`absurd` 为 core，本文件 :1090/:4786/:5194
   多处既有同型使用；Ne/Not 通过 delta 互演，PA25:3014 既有先例）。
   逐行依赖核对见 VERIFICATION.md §2。
3. **PA18 A7 整体删除**：`pa18_ccCell_swap`（含 sorry）连同其旧
   docstring 与编排者叠回的 `--` 注记段删除，换一段审计记账注释（保留反证结论与保留反证 kit 的
   理由）；头部记账注记改 CLOSED；反证 kit 两处注释同步（纯注释）。
   保真说明：删除假陈述 + 纯注释重写，零陈述面变化。
4. **PA25 `MCELL4_LEAF_S_LEAF` 两支构造性重排**（见 (a2)）：by_cases 换
   原序等式 1 行；第一支 = 原等式支逐字对称换序（ZASUVOR→hl'、
   `Or.inr`→`Or.inl`、AJRIPQN/`cc_uh_exists`/`CC_KE_34`/hI 全部换原序列表）；
   第二支 = `have hEq' := CFFONNL … hEq`（HOL 原序 hne 直接喂入）经
   `EL_CC_UH` rw 桥转具体形后，**原等式支代码逐字**（ZASUVOR、AJRIPQN
   换位序、`Or.inr`、hI/hn 闭环全保留）。docstring 同步改写为两支构造性
   记账。保真说明：OXLZLEZ3.hl:1980-2053 逐支对应。

### (c) 消费面影响清单（全树 grep `CFFONNL`，排除注释）

项级消费点**唯一**：PA25:3015（MCELL4_LEAF_S_LEAF 不等式支，本 SF 同步
重排）。其余全为注释/NEEDS 记账（PA25:232/2928/2933/2969/3007/3425/3484/
3786/3827/3846/3860），其中 MCELL4_LEAF_S_LEAF docstring 与 PA25:232 头部
注记随 diff 改写；PA25:3425/3484/3786/3827/3846/3860 为下游 sorry 件的
NEEDS 注记（MCELL4_FI/LEAF_RANK4_CHI_MSB(_ALT)/CC_CELL_WEDGE_MATCH_UH 等），
其"CFFONNL→pa18_ccCell_swap 值级债"表述随本 SF 应用转为过时，建议随应用
批顺带刷新或留给下游填证波（由编排者决定，不进本 diff）。

### (d) 验收与应用计划（gate 预演参数）

两跑闸门（STATEMENT-FIX 多重集比对逐文件生效，本 patch 双文件节齐备）：

- 跑 A：`GATE_MODE=STATEMENT-FIX SF_PATCH=docs/statement-fix-proposals-patches/50-cffonnl-hol-original-order.patch SF_ITEM=50 GATE_ROOTS="Kepler.Text.PackingAuto18" lean/scripts/auto_gate.sh Kepler/Text/PackingAuto18.lean CFFONNL`
- 跑 B：`GATE_MODE=STATEMENT-FIX SF_PATCH=… SF_ITEM=50 GATE_ROOTS="Kepler.Text.PackingAuto25" lean/scripts/auto_gate.sh Kepler/Text/PackingAuto25.lean MCELL4_LEAF_S_LEAF`

预期：两 THM `#print axioms` = `[propext, Quot.sound, choice]` 标准三
（CFFONNL 修复后证明闭包内全部真证：ZWVCBMN PA18:3787 已于 edge-rigidity
波闭合、AJRIPQN_0 PA18:4507 真证、CONVEX_PLANE_INTER/CHI_MSB_POS2/
CHI_MSB_AFF_GT_0/CONVEX_R3_INTER/CC_CELL34/CELL3_NONDEG/K4_CHI_MSB_POS
皆已证；MCELL4_LEAF_S_LEAF 闭包 = CFFONNL + AJRIPQN PA17:931 真证 +
MCELL4 卡具）。下游追加审计（不进闸）：`LEAF_RANK_ONTO → LEAF_IN_WEDGE_GE
→ MCELL4_FI_EL → MCELL4_FI` 与 `MCELL4_AZIM_LT_PI →
LEAF_RANK4_CHI_MSB(_ALT)`、`CC_CELL_WEDGE_MATCH_UH`（+其
NOT_COPLANAR_AFF_3 本地复制）按 pa25wim/k3k4wim 草稿机械填——合计 5+ 枚
e2e 直源入清偿射程（T §5.1 解锁面判定维持，路径 = 本 SF 而非填 A7）。

### (e) 孤儿评估（A7 删除面）

- A7 本体 proof 是 `sorry`，删除不孤儿化任何件。
- `p18cc_*` 孪生 kit（PA18:217-1000，30 件）服务对象是 `cc_pe_exists`
  （kit 头注记 :219-223），与 A7 无消费关系，**全部保留**。逐一 grep 引用
  数后唯一零消费件 = `p18cc_dot_sub18`（PA18:575，仅定义行）——系**既有
  孤儿**（其非孪生原件 `dot_sub18` :2395 才是在用版），非本 SF 造成；
  是否随本 SF 顺手清理由编排者决定（删之为 −3 行纯减债，与本项目
  反孪生纪律一致）。
- 反证四件套（`pa18_chi_halfspace_convex`/`pa18_ccCell_apex_pos`/
  `pa18_ccCell_chi_nonneg`/`pa18_ccCell_swap_ne`）：今日项级消费者仅 kit
  内部，但 T §5.1 建议保留为永久公共资产（"两取向 cc 胞分居茎平面两侧"
  是独立数学事实，WEDGE_UNIQUE_CC_CELL 类论证可消费）——本 SF 保留。

### (f) 风险与回滚

- 风险 1（基线漂移）：主仓 PA18 在本线工作期间两次并发变更
  （361ef126 → b9ec957a → 555a3532，均注释区：后者为编排者把 REVERSED
  VERDICT docstring 改写为 `--` 注释）。本 diff 以末态 555a3532 为基线；
  闸门按逐行多重集比对，应用时若工作树 ≠ 本 diff 基线会被拦下；届时以
  当时工作树重放核对即可（本 SF 改动面按文本锚定、无行号依赖）。
- 风险 2（下游草稿过时）：pa25wim/k3k4wim 下游填证草稿若按"absurd 形"
  预写 PA25 分支，须按 (a2) 修正为两支构造性（本 diff 已内联正确形态，
  草稿仅余下游件的填充部分）。
- 回滚：`git apply -R 50-cffonnl-hol-original-order.patch` 逐字节还原；
  无 def/命名/记账结构变化；反证 kit 不受影响；CFFONNL 消费面唯一已证。

## 51. PA21 `bank_TSKAJXYGXSA` 内括号符号回归 HOL 原文（`1/12 − (X − Y)`，Lean 误植为 `1/12 − X − Y`）— 分级 A（statement 保真修正 · nli 叶陈述误植）

**立案：2026-10-24，lane tskajxy-w5（AS，解析半波）移植 `TSKAJXY_DERIVED4`
四件套时发现并以 HOL 忠实叶 `p21k_glsa_correct` 显式前提绕行；编排者独立
核对 HOL 原文 + 消费面后立案，编排者→用户批准流程。** 对象 = PA21 冻结
nli 叶 `bank_TSKAJXYGXSA`（PA21:267，`def … : Prop`），HOL ineq.hl:359
`TSKAJXY-GXSABWC DIV` 的 x-空间转录。

(a) HOL（ineq.hl:357-383 逐字）：
```
((&1 / &12 -
  (
    (&2 * mm1 / pi) * (sol_euler_x_div_sqrtdelta … + … + … + …) -
    (&8 * mm2 / pi) * (ldih2_x_div_sqrtdelta_posbranch … + … + … + …)
  ) >= &0) \/ (delta_x x1 x2 x3 x4 x5 x6 < &0)
```
即 `1/12 − (X − Y) ≥ 0`，其中 X = (2mm1/π)·Σsol、Y = (8mm2/π)·Σldih。
Lean（PA21:271-285 现行）转录为 `1/12 − X − Y ≥ 0`：内括号丢失，
Y 项符号由 + 变 −。Y 的四个 `ldih*XDivSqrtdeltaPosbranch` 在盒上非负
（posbranch 分支），故 Lean 版**严格强于** HOL 证书所证——HOL 的
nonlinear 证书证不出 Lean 叶，而 `gamma4fgcy_div_sqrtdelta`
（merge_ineq.hl:1160）恒等式右端 Y 项带 + 号，与 Lean 叶直接不合。
3 胞先例 `mi_gamma3fXDivSqrtdelta_unfold`（PA21）的 ldih 块已是加号，
佐证本叶应为 + 号。

### (b) 修复补丁

存档 `docs/statement-fix-proposals-patches/51-tskajxygxsa-hol-sign.patch`：

1. **PA21 `bank_TSKAJXYGXSA` 一处符号**：`-\n      (8 * mm2 / Real.pi) *`
   → `+\n      (8 * mm2 / Real.pi) *`（1 行）。盒、量词、deltaX 析取支
   一字不动。保真说明：HOL :357-383 逐字；变化仅内括号展开后的 Y 项符号。
2. **docstring 补一句记账**（纯注释）：注明 2026-10-24 SF-51 回归 HOL
   内括号形。

### (c) 消费面影响清单（全树 grep `TSKAJXYGXSA`，排除注释）

- `lean/Kepler/Assembly.lean:398` `theorem nliTskGXSA : bank_TSKAJXYGXSA := sorry`
  （e2e 直源之一，父 `nliTskBank`）——**sorried，证明体不受影响**；其陈述
  含义随 def 修正为 HOL 证书真正证明的命题（原 Lean 形本就不可被该证书
  放电）。
- `lean/Kepler/Text/PackingAuto21.lean:394` `tsk_bank` 合取（十叶之一）——
  bundle 含义同步修正；`TSKAJXY_034`（:4168）的假设 `hyp : tsk_hyp_new`
  经 `.2.2 : tsk_bank` 含此叶，其假设面随之变为 HOL 原形（更弱、正确）。
- `lean/Kepler/Text/PackingAuto21.lean` TSKAJXY034W5 区 `p21k_glsa_correct`
  （public def，AS 交付）= 修正后 `bank_TSKAJXYGXSA` 逐字同体——SF 应用后
  可由 `hyp.2.2` 对应分量直接放电（后续收编波一行），该 def 转为可回收
  的过渡资产（不删，纯追加纪律）。
- 无任何证明体 unfold 此 def（全树 grep 仅上述三处 + AS 注释记账）。

### (d) 验收与应用计划（gate 预演参数）

`GATE_MODE=STATEMENT-FIX SF_PATCH=docs/statement-fix-proposals-patches/51-tskajxygxsa-hol-sign.patch SF_ITEM=51`，
`LANE_FILES="Kepler/Text/PackingAuto21.lean"`，闸 1 `GATE_ROOTS=Kepler.Text.PackingAuto21`
THM=`Kepler.Text.bank_TSKAJXYGXSA`（def，axiom 面空/标准三）；闸 2
`GATE_ROOTS=Kepler.Assembly` THM=`Kepler.Assembly.nliTskGXSA`（预期标准三 +
sorryAx，sorried 源本身）。预期：PA21 直 sorry 计数不变（1）；Assembly
不变；e2e 直源数不变（128→ 本 SF 零变化，仅陈述面保真）。

### (e) 孤儿评估

无删除；无新增孤儿。`p21k_glsa_correct` 由"外部锚"降级为"可一行放电的
过渡 def"，建议随 :4168 收编波回收（纯追加纪律下保留 def 本体）。

### (f) 风险与回滚

单符号修正，def 无 unfold 消费者，编译零风险。回滚 = 反向 1 行。
**不批准的后果**：`nliTskGXSA` 永不可被 HOL 证书放电（Lean 叶更强），
且 `cell4_from_ineq_thm`（:4168 翻除的最后一块）必须永久携带
`p21k_glsa_correct` 显式前提。

## 52. PA24 换接去 shim：`p24_edgeX_of_leaf23` 不再消费 PA2 sorried 桩 `RVFXZBU2_concl`，改由树内真证 AJRIPQN+LEPJBDJ 链直接供给（新增 private 真证 `p24_rvfxzbu2_prefix`）— 分级 A（证明体重接线 · 恢复 HOL 直接结构）

**立案：2026-10-25，Lane BF（pa2-rvfxzbu2）路线 B 交付，双重克隆验证（工作区 +
独立净版克隆）；编排者按用户批准的重接线程序（F1 UPFZBZM 重接线 + "都批"，2026-10-25）
走本通道应用。** 对象 = PA24:4688（现行号）`p24_edgeX_of_leaf23` 证明体内对
PA2:5496 `RVFXZBU2_concl := sorry` 的唯一活消费。

### (a) HOL 对位与 shim 溯源
HOL pack_concl.hl:145-147 逐字 `RVFXZBU2_concl` 仅有语句绑定——本地 flyspeck 全量
reference 实测**无任何 HL 证明体、无任何 HL 消费者**；Lean 侧该 shim 是 SF-20 家族
冻结占位。HOL 的 REUHADY 装配链由已证的 AJRIPQN（PA17:931 真证）/LEPJBDJ 覆盖理论
直接导出 edgeX 事实，不经任何 RVFXZBU2 形语句。本重接线在 PA24 内新增 private 真证
`p24_rvfxzbu2_prefix`（AJRIPQN 胞相等 + LEPJBDJ 顶点抽取，~20 行核心，#print axioms
= 标准三）并换接消费点，恢复 HOL 的直接结构。

### (b) 修复补丁
存档 `docs/statement-fix-proposals-patches/52-pa24-rvfxzbu2-rewire.patch`（+47/−20，
单文件 PA24）：新增 `p24_rvfxzbu2_prefix`；`p24_edgeX_of_leaf23` 内换接（消费面实测
只需首段集合形；`p`/`hpIcc`/`hvleq` 仅用于导出 `htr'`）；PA2 桩原位不动（删除归用户保留）。
验证：patch 可贴、PA24 编译绿（8701 jobs）、`p24_edgeX_of_leaf23` axiom 面
sorryAx → 标准三、**`REUHADY1` → 标准三全净**（该链对 PA13 URRPHBZ2/QZYZMJC 无活依赖）。

### (c) 消费面影响清单
- PA24:4688 唯一活消费被换接；`RVFXZBU2_concl` 转**零活消费沉睡态**（PA2 bare sorry
  计数不变；e2e 直源数不变——`p24_edgeX_of_leaf23` 与 `REUHADY1` 本就不是 direct source，
  本 SF 减少的是间接 taint 跳数）。
- 连带：REUHADY1 链转净后，PA25 `LEAF_RANK_REUHADY` 对 FCHKUGT 之外的债面收窄。
- 遗留（不在本 SF）：PackingConcl:388 孪生 `_discharged` 链；PA2 桩族
  （RVFXZBU1/SLTSTLO2/LEPJBDJ_concl）与 PA10 RVFXZBU 非推论关系（BF 勘误，DEP_MAP 第 24 行前提不成立）。

### (d) 验收与应用计划
`GATE_MODE=STATEMENT-FIX SF_PATCH=docs/statement-fix-proposals-patches/52-pa24-rvfxzbu2-rewire.patch SF_ITEM=52`，
`LANE_FILES="Kepler/Text/PackingAuto24.lean"`，闸 `GATE_ROOTS=Kepler.Text.PackingAuto24`
THM=`Kepler.Text.p24_edgeX_of_leaf23`（rule 5：修复后须 sorryAx-free，BF 实测标准三）。

### (e) 孤儿评估
无删除；`RVFXZBU2_concl` 成孤儿（零活消费）但保留在册（删除归用户裁决）。

### (f) 风险与回滚
证明体重接线，陈述零变化；双重克隆验证；回滚 = 反向 patch。

## 53. PA4 azim 求和区间两处误植：`ccRealModelP4`（:197）与 `CARD5_1074_LE_QYI`（:519）的 `∑ Icc 0 card` → `∑ Icc 0 (card - 1)`，恢复 HOL 正本区间 — 分级 A（移植误植 · 两行修正）

提案日期 2026-10-26。提案人：编排者（依据 GRHIDFA-W6 车道发现，编排者独立复核实锤）。

### (a) HOL 引文
- `reference/flyspeck` 移植源 `lean/scripts/packing/OXLZLEZ1.hl:90`：
  `(sum (0..(cc_card_v11 cc - 1)) (cc_azim_v11 cc) = &2 * pi)`。
- `lean/scripts/packing/OXLZLEZ2.hl:2527`（CARD5_1074_LE_QYI 前提行）：
  `sum (0..cc_card_v11 cc - 1) (cc_gg_v11 cc) < &0)`。
- 树内已证同构：PA3:163（`cc_real_model_v11` 同合取项 `Icc 0 (cc_card_v11 cc - 1)`）、
  PA3:2462（`p3i_CARD5_1074_LE_QYI` 的 `_hsum` 同为 `0..card-1`）。
- PA4 现行（误植）：`PackingAuto4.lean:197` 与 `:519` 均为 `Finset.Icc 0 (ccCardP4 cc)`。

### (b) 修复补丁
存档 `docs/statement-fix-proposals-patches/53-pa4-azim-sum-range.patch`（+4/−4，单文件
PA4，两行各一删一加，`Icc 0 (ccCardP4 cc)` → `Icc 0 (ccCardP4 cc - 1)`）。
验证：patch 可贴；修复后 `lake build Kepler.Text.PackingAuto4` EXIT=0（8695 jobs，0 error，
W6 工作区实测）。

### (c) 消费面影响清单
- 语义变化（车道双向显式反例已核）：周期性下 `∑_{0..card} = ∑_{0..card-1} + azim 0` 且
  `azim ≥ 0.606 > 0`，故 PA4 现行 `= 2π`（card+1 项）与 HOL `= 2π`（card 项）**互不蕴含**
  ——现行 PA4 陈述强于 HOL，真证不可能，属移植误植非语义等价变体。
- 受阻消费面：PA4 §2 的 **20 枚 CC4P4 私有桩**（LXDEYBO…GRHIDFA 全列）结构性无法经 PA3
  阶梯闭合（W6 已备 139 行全真证桥 `toV11` + accessor + iff + 前提槽引擎
  `p4_real_model_of_sumfix`/`p4_model4_of_sumfix`，修复后每桩 1-3 行 discharge）。
- e2e 锥：PA4/PackingConcl 不在锥内，本修复**锥直源 0 变化**；收益 = 邻近层
  （PackingConcl 九连已由 W6 清净，OXLZLEZ 波 30 桩全链可达真证）。
- PackingConcl 消费的 `*_v11` 九孪生不依赖两误植行（其陈述用 `0..card-1`，本就正确）。

### (d) 验收与应用计划
`GATE_MODE=STATEMENT-FIX SF_PATCH=docs/statement-fix-proposals-patches/53-pa4-azim-sum-range.patch
SF_ITEM=53`，`LANE_FILES="Kepler/Text/PackingAuto4.lean"`，闸
`GATE_ROOTS="Kepler.Text.PackingAuto4 Kepler.Text.PackingConcl"`，
THM=`Kepler.Text.p4_real_model_of_sumfix`（rule 5：修复后该件 sorryAx-free——
其为纯前提槽引擎，W6 已实测全真证；修复后另开收尾车道把 20 桩逐枚 discharge，
PA4 文件级预期 29→9）。

### (e) 孤儿评估
无删除；无孤儿。

### (f) 风险与回滚
两行陈述修正，语义向 HOL 回归（同 SF-51 符号回归先例）；下游 20 桩为 sorry 桩、
九孪生与 PackingConcl 链不受影响；回滚 = 反向 patch。
