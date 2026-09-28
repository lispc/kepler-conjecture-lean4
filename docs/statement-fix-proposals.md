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
