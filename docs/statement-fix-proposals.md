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
（`docs/planar-encoding-fix.md` §2 补丁）已落地：新 `facetOfC` 自带 ≠∅ + `affDimC`
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
（`docs/planar-encoding-fix.md` §2 补丁）已落地：结论侧 `facetOfC` 已含 ≠∅ +
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

## merge-ineq-bank. 波 0 ——银行结构化 + eta_y 重指向（Merge_ineq 通道章程 §2）

> 立项与章程：`docs/merge-ineq-channel.md`（编排者审定通过，见章程末
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
grutoti-scout §5.1），无法逐字对照；但 Lean 侧 GT-1 已落地的
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
PackingConcl 不经 PA23 走线，grutoti-scout §0.2），唯一调用点是同文件
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
`p permutes Icc 0 k` 即 `∀ j > k, p j = j`；扫雷报告 C2-1（encoding-risk-sweep
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

### (c) 状态：**草案待审**（cell_vol 波立案；k=0,1 计数臂与退化/null 臂
已闭，仅 k∈{2,3,4} wedge 恒等式本体卡此项）。

## 29. PA23 `grutoti_cell_vol` ε-junk 角（cellParams 逆序表）— 分级 A′

### (a) HOL 出处：HL per-cell 分析天然携带 per-cell 前提；cell_vol 波发现：
无效 witness（如参数表逆序 [u1;u0,…]）时 `dihX` 读 junk 值——**潜在
frozen-false 角**。

### (b) 修复

签名加 `truncateSimplex 1 (cellParams V X).2 = [u0, u1]` 型前提封角。

### (c) 状态：**草案待审**（cell_vol 波立案）。
