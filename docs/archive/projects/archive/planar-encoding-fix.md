# planar-encoding-fix.md — "planar 编码定义纠正"立项章程（DEF-FIX）

> 立项依据：`DECISIONS.md` 2026-09-29 条（用户已批）。本文 = 侦察轮（只读）交付物：
> 四节 = ①HOL 语义基准 ②定义补丁草案 ③波及面清单 ④DEF-FIX 闸门规程。
> 侦察轮纪律：零 .lean 改动、scratch 验证用后即删（`/tmp/ScratchDefFix.lean`，已删）。
> 对照基准：`reference/flyspeck` @ `1ce0353`。
> 机器验证状态：补丁草案的新定义形态 + 基本引理（affDimC ∅/{x}、facet 非空、
> facet ≠ s、polyhedronC 凸/半空间/univ/∅ 实例、交封闭、cone0=affGt、锥严格性
> witness）在 scratch 端到端编译 **0 error、0 sorry**（axioms = propext + choice +
> Quot.sound，2026-09-28 实测；`lake env lean` 直连现存 olean）。
> ⚠ 范围注记：定义纠正授权范围 = PA22 的 `facetOfC`/`polyhedronC`/`cone0P22`
> 三 def（含 ℂ 上 affDim 支撑件）。Polytope.lean（V3 真版）不动；PA22 的
> `polyhedron`/`FacetOf`/`affDim`（Kepler.Text 命名空间，引用 Polytope）不动。

---

## §1 HOL 语义基准（逐字抄录）与 Lean 侧错误点

### 1.1 `facet_of` — polytope1.ml:1504–1507

HOL 原文（`reference/flyspeck/azure/hol-light-nat/Multivariate/polytope1.ml`）：

```
parse_as_infix("facet_of",(12, "right"));;

let facet_of = new_definition
 `f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1`;;
```

其中 `face_of` = polytope1.ml:22–26（`t SUBSET s ∧ convex t ∧ !a b x. a IN s ∧
b IN s ∧ x IN t ∧ x IN segment(a,b) ==> a IN t ∧ b IN t`，`segment(a,b)` 为开线段
——与 Lean `openSegment` 一致）；`aff_dim` = convex1.ml:3784–3786（仿射无关基的
基数约定）。

**Lean 现定义**（`lean/Kepler/Text/PackingAuto22.lean:121`）：

```lean
def facetOfC (f s : Set ℂ) : Prop := faceOfC f s ∧ f ≠ s
```

**错误点**：合取支 2 以"真面" `f ≠ s` 冒充 `~(f = {})`；合取支 3（aff_dim 条件）
整个缺失。后果：∅ 与顶点面（affDim 差 1 以上）都成为合法 facet——r2 项 11 反例
（P = {0,1,I}，c = ∅）即由此而来。`faceOfC`（PA22:116）本身是 `face_of` 的忠实
移植，**不动**。

### 1.2 `polyhedron` — polytope1.ml:2546–2549

HOL 原文：

```
let polyhedron = new_definition
 `polyhedron s <=>
        ?f. FINITE f /\
            s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})`;;
```

**Lean 现定义**（PA22:125–126）：

```lean
def polyhedronC (P : Set ℂ) : Prop :=
  ∀ x : ℂ, x ∈ P → ∃ c : Set ℂ, facetOfC c P ∧ x ∈ c
```

**错误点**：整个谓词换成了"每点属于某真面"（PA22:123–124 注释自认 "every
point is in a facet"），与 H-表示无关。后果三连：
- 对**真 polytope**（有内点）不可满足——`p22_ball_face_contra`（PA22:135–168）
  即利用此点把 14 枚 planar-kit 填证空洞化为真；
- 对**非凸集**反而可满足（{0,1} 每点取 c = ∅ 即可），凸性全失；
- 语义上既不弱于也不强于 HOL polyhedron（{0} 两者皆满足、三角形仅 HOL 版满足、
  {0,1} 仅弱版满足），是**移植错误**而非弱化。

旁证：Polytope.lean:60–62 的 V3 版 `polyhedron` 是同一 HOL 定义的**忠实**移植
（H-表示），planar 层却走了另一条错路——两版并存本身就是误移植证据。

### 1.3 `aff_gt` / `cone0` — sphere.hl:279–296

HOL 原文（`reference/flyspeck/text_formalization/general/sphere.hl`）：

```
let affsign = new_definition `affsign sgn s t (v:real^A) = (?f.
  (v = lin_combo (s UNION t) f) /\ (!w. t w ==> sgn (f w)) /\ (sum (s UNION t) f = &1))`;;
let sgn_gt = new_definition `sgn_gt = (\t. (&0 < t))`;;
let sgn_ge = new_definition `sgn_ge = (\t. (&0 <= t))`;;
let cone0 = new_definition `cone0 v S:real^A->bool = affsign sgn_gt {v} S`;;
let aff_gt_def = new_definition `aff_gt = affsign sgn_gt`;;
```

加之 `CONE0_AFF_GT`（counting_spheres.hl:3770–3774）：
`!x U. cone0 (x:real^A) U = aff_gt {x} U`（HOL 证明 `REWRITE_TAC[cone0; aff_gt_def]`
= 定义展开）。

**Lean 现定义**（PA22:241）：

```lean
def cone0P22 (x : V3) (U : Set V3) : Set V3 := affGe {x} U
```

**错误点**：`sgn_gt`（`0 <`）写成了 `sgn_ge`（`0 ≤`）——严格锥弱化成闭锥。
PA22:240 自己的 docstring 写的就是 "the open cone `aff_gt {x} U`"，定义与自身
文档矛盾；PA22 头部 ENCODING NOTES（:55–56）亦自认此编码并预言 "CONE0_AFF_GT
becomes rfl"。严格版 `affGt` 在 `lean/Kepler/Geom/Aff.lean:39` **早已定义且全树
零消费**（`Affsign` 有限性显式化版本，同 flyspeck.ml:688 移植口径），修复 = 一词
之改。后果：弱锥包含全部边界母线（系数可取 0），`CONE0_FCHANGED` 家族 5 枚陈述
在弱语义下假化（见 §3b；纸面反例：s = {u1,u2}、v = u1 端点 ∈ affGe{0}s 而
∉ fchanged(conv hull s)）。

---

## §2 定义补丁草案（DEF-FIX 主补丁）

### 2.0 前置评估：ℂ 上 affDim 的路线选择

| 路线 | 内容 | 裁决 |
|---|---|---|
| A. 平面孪生 `affDimC`（在 PA22 内新写） | `Polytope.affDim`（V3 版）逐字孪生：`if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)`；所需引理以 Polytope.lean:148–250 为模板 | **采纳**。在授权范围内（DECISIONS"含 ℂ 上 affDim 支撑件如需"）；ℂ 与 V3 类型不同无法复用；与 planar 编码层既有孪生惯例（dot2/faceOfC/asn/acs）一致 |
| B. 沿 ℝ-线性同构搬运 | ℂ ≃ EuclideanSpace ℝ (Fin 2) 转移 | 否决：Polytope kit 在 V3（Fin 3）上，无到 V3 的同构；Fin 2 上无现成 kit |
| C. 泛化 Polytope.affDim 后特化回 V3 | 改已证 2000+ 行文件 | 否决：越出授权范围、重开已绿文件的构建风险；留作未来全局去孪生提案 |

Mathlib 无现成 `aff_dim`（`vectorSpan + Module.finrank` 就是 Polytope.affDim 的
做法），故"复用 Mathlib"与路线 A 殊途同归。孪生债务按 statement-fidelity 附录
惯例**登记折算点**（见 §4 验收清单第 9 条）。

### 2.1 主补丁正文（`docs/statement-fix-proposals-patches/DEF-FIX-planar-encoding.patch`）

hunk 1 —— 新 `affDimC` + `facetOfC` 新体 + `polyhedronC` 新体（PA22:115–126，
`faceOfC` 逐字不动）：

```diff
-/-- Planar copy of Polytope.`FaceOf` (polytope1.ml:22 face kit). -/
+/-- Planar copy of HOL `aff_dim` (convex1.ml:3784; twin of Polytope.affDim):
+`∅ ↦ -1`, else the finrank of the direction of the affine hull. -/
+noncomputable def affDimC (s : Set ℂ) : ℤ :=
+  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)
+
+/-- Planar copy of Polytope.`FaceOf` (polytope1.ml:22 face kit). -/
 def faceOfC (t s : Set ℂ) : Prop :=
   t ⊆ s ∧ Convex ℝ t ∧
     ∀ a b x : ℂ, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

-/-- Planar copy of HOL `facet_of` (proper face). -/
-def facetOfC (f s : Set ℂ) : Prop := faceOfC f s ∧ f ≠ s
+/-- Planar copy of HOL `facet_of` (polytope1.ml:1506): `f facet_of s <=>
+f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1`. -/
+def facetOfC (f s : Set ℂ) : Prop :=
+  faceOfC f s ∧ f ≠ ∅ ∧ affDimC f = affDimC s - 1

-/-- Planar copy of HOL `polyhedron` (polytope1.ml:2546): every point is in a
-facet. -/
-def polyhedronC (P : Set ℂ) : Prop :=
-  ∀ x : ℂ, x ∈ P → ∃ c : Set ℂ, facetOfC c P ∧ x ∈ c
+/-- Planar copy of HOL `polyhedron` (polytope1.ml:2546): finite intersection
+of halfspaces `{x | a dot x ≤ b}` with `a ≠ 0` (H-representation). -/
+def polyhedronC (P : Set ℂ) : Prop :=
+  ∃ F : Set (Set ℂ), F.Finite ∧ P = ⋂₀ F ∧
+    ∀ h ∈ F, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b}
```

hunk 2 —— 删除 `p22_ball_face_contra` 及其 docstring（PA22:128–168，**DEF-FIX
白名单删除项**）：新 `polyhedronC` 语义下 "polyhedronC P + 球含于 P ⇒ False" 为
**假**（univ 即反例），该私件不可保留；其全部 14 个消费点随 hunk 3 回退。
（闸门"结构性代码行禁删"规则在 DEF-FIX 模式下对本行显式豁免。）

hunk 3 —— 14 枚 planar-kit 填证回退（声明冻结不动，证明体替换）：
`facet_rep_in_facet`(PA22:439)、`facet_rep_refl`(:447)、`POLYHEDRON_MEMBER`(:571)、
`facet_rep_in_poly`(:578)、`facet_arg_lt_pi`(:584)、`insert_v`(:619)、
`facet_rep_a_uniq`(:631)、`poly_sort_antisym`(:645)、`POLY_SORT_LEMMA`(:658)、
`POLY_SORT`(:667)、`POLY_SORT_BIJ`(:678)、`bisector_point_exists`(:697)、
`POLYSORT_BIJ2`(:1359)、`EUSOTYP_simple`(:1381)——各证明体（现为
`(p22_ball_face_contra …).elim` 及其包装）替换为
`sorry -- DEF-FIX: refill per counting_spheres.hl:<行号> §3a`。
逐字核对结论：**陈述文本零改动**（三 def 同名换体，所有前提/结论字符串不变）。
不受影响的近邻（核查过）：`poly_sort_trans`(:652，纯序关系组装)、
`facet_rep_spec/props/uniq_c`(:349/:374/:383，消费 eus1)、`facet_rep_nz`(:689)、
`bisector_point_props`(:716)、`facetRepPair`/`facet_rep_a/b`/`poly_sort_fn`/
`bisector_point`（def，类型不受影响）。

hunk 4 —— `cone0P22` 严格化（PA22:240–241）：

```diff
-/-- HOL `cone0 x U` (3d.tex): the open cone `aff_gt {x} U`. -/
-def cone0P22 (x : V3) (U : Set V3) : Set V3 := affGe {x} U
+/-- HOL `cone0 x U` (sphere.hl:290 `cone0 v S = affsign sgn_gt {v} S`), i.e.
+the open cone `aff_gt {x} U` (`Kepler.Geom.affGt`, counting_spheres.hl:3770
+CONE0_AFF_GT). -/
+def cone0P22 (x : V3) (U : Set V3) : Set V3 := affGt {x} U
```

hunk 5 —— 陈述侧同病纠正（`aff_gt` 被硬编码为 `affGe` 的三处 + CONE0_AFF_GT）：

```diff
 /-- HOL `cone0_subset_lune` (counting_spheres.hl:3058). GIANT. -/
 theorem cone0_subset_lune (u0 u1 u2 u3 : V3) :
-    cone0P22 u0 {u1, u2, u3} ⊆ affGe {u0, u1} {u2, u3} := by
+    cone0P22 u0 {u1, u2, u3} ⊆ affGt {u0, u1} {u2, u3} := by
   sorry -- DEF-FIX: refill（原证明的严格版逐字搬运，见 §3b）

 /-- HOL `AFF_GT_RELATIVE_INTERIOR` (counting_spheres.hl:3120). GIANT. -/
 theorem AFF_GT_RELATIVE_INTERIOR (s : Set V3) (hf : s.Finite) (h : 1 < s.ncard) :
-    affGe (∅ : Set V3) s ⊆ intrinsicInterior ℝ (convexHull ℝ s) := by
+    affGt (∅ : Set V3) s ⊆ intrinsicInterior ℝ (convexHull ℝ s) := by
   sorry -- DEF-FIX: 陈述纠正（原为假：弱锥含边界点，不在相对内部）

 /-- HOL `CONE0_AFF_GT` (counting_spheres.hl:3770). -/
-theorem CONE0_AFF_GT (x : V3) (U : Set V3) : cone0P22 x U = affGe {x} U := rfl
+theorem CONE0_AFF_GT (x : V3) (U : Set V3) : cone0P22 x U = affGt {x} U := rfl
```

及 `gotcjah_sol_half`（PA22:2405–2406）结论侧
`X ⊆ affGe {0, v} {w0, w1} ∩ W` → `X ⊆ affGt {0, v} {w0, w1} ∩ W`
（HOL 原文 counting_spheres.hl:3897 为 `aff_gt {vec 0, v} {w0, w1}`；该定理本为
sorry，陈述纠正后仍冻结黑名单至 GOTCJAH 专项）。

hunk 6 —— 注释/文档同步（纯注释，闸门原有规则即可）：头部 ENCODING NOTES
:38–39（"*C copies … proper-face form" → "faithful copies of polytope1.ml
facet_of/polyhedron"）、:55–56（cone0 编码注记改为 affGt）。

### 2.2 scratch 已验证的基本引理（即新定义的最小配套，重填波可扩）

以下在 scratch 端到端编译通过（0 error 0 sorry），可作为重填波第 1 波的
现成模板：

- `affDimC ∅ = -1`（`if_pos rfl`，同 Polytope.affDim_empty）；
  `affDimC {x} = 0`（`vectorSpan_singleton` + `finrank_bot`）；
- `facetOfC f s → f.Nonempty`；`¬ facetOfC ∅ s`；`facetOfC f s → f ≠ s`
  （由 affDim 条件 omega 推出——旧定义的显式合取支被此引理替代）；
- `polyhedronC P → Convex ℝ P`（dot2 ℝ-线性 + `convex_sInter`）；
  实例：半空间（`a ≠ 0`）、univ（空族）、∅（两反向半空间之交，经交封闭）；
  交封闭 `polyhedronC P → polyhedronC Q → polyhedronC (P ∩ Q)`（`F_P ∪ F_Q` +
  `Set.sInter_union`）；
- `cone0P22 x U = affGt {x} U := rfl`；
  严格性 witness：`(0:V3) ∈ affGe {0} {u}`（弱）∧ `(0:V3) ∉ affGt {0} {u}`
  （严格，u ≠ 0）——语义变化非空的机器证据。

### 2.3 重填波还需的前置 kit（一次性投入；模板全在 Polytope.lean）

| kit 件 | 模板位置 | 用途 | 体量估计 |
|---|---|---|---|
| `affDimC_mono`/`affDimC_hyperplane`(=1)/全维(=2) | Polytope.lean:155/203 | affine_facet_hyper、facet 论证 | ~150 行 |
| `FACET_OF_POLYHEDRONC_EXPLICIT` 及 face 结构定理 | Polytope.lean:1390–1790（minrep/slice 机制） | eus1、POLYHEDRON_MEMBER、sort/bisector 族 | **~500 行，最大单项** |
| `CONTAINS_BALL_AFFINE_HULL` ℂ 版 | Packing3.CONTAINS_BALL_AFFINE_HULL | POLYHEDRON_MEMBER 族 | ~60 行 |
| `FACET_OF_LINEAR_IMAGE` ℂ 版（pad2d3dP22/dropout3P22 线性+等距） | polytope1.ml FACET_OF_LINEAR_IMAGE | pad2d3d_facet | ~200 行 |
| dot2 线性 kit | PA22:402–436 已有大半 ✓ | 全部 | 余量小 |

---

## §3 波及面清单（关键交付）

**全树 grep 结论**：`facetOfC`/`polyhedronC`/`cone0P22`/`faceOfC` 及其定理族的
消费者**全部在 PA22 之内**（唯一 import PA22 的文件 LocalBridge.lean 只消费
`localAnnulusInequalityP22` 桩，零波及）。以下为 PA22 内逐枚分类。

### 3a. 失效需重填（14 枚已填 planar-kit；陈述冻结，证明回退后按 HOL 原文重填）

| # | 定理 | PA22 行 | HOL 原文行 | HOL 证明路线（核对状态） | 重填档 |
|---|---|---|---|---|---|
| 1 | `facet_rep_uniq`★ | 333 | counting_spheres.hl:161 | 小学级（非空点支撑不等式 b1≤b2≤b1；**已核**，r2 patch 11 的证明体直接可用） | 机械 |
| 2 | `facet_rep_in_facet` | 439 | hl:227 | facet_rep_uniq_c + norm1_cauchy_eq + Cauchy–Schwarz（**已核** ~40 行代数） | 中等 |
| 3 | `POLYHEDRON_MEMBER` | 571 | hl:346 | CONTAINS_BALL_AFFINE_HULL + FACET_OF_POLYHEDRON_EXPLICIT（**已核**；依赖 §2.3 大 kit） | GIANT |
| 4 | `facet_rep_in_poly` | 578 | hl:435 | 待人工确认（未逐行核） | GIANT |
| 5 | `facet_arg_lt_pi` | 584 | hl:453 | 待人工确认 | GIANT |
| 6 | `insert_v` | 619 | hl:529 | 待人工确认 | GIANT |
| 7 | `facet_rep_a_uniq` | 631 | hl:640 | 待人工确认 | GIANT |
| 8 | `poly_sort_antisym` | 645 | hl:682 | 待人工确认 | GIANT |
| 9 | `POLY_SORT_LEMMA` | 658 | hl:729 | 待人工确认 | GIANT |
| 10 | `POLY_SORT` | 667 | hl:746 | 待人工确认 | GIANT |
| 11 | `POLY_SORT_BIJ` | 678 | hl:795 | 待人工确认 | GIANT |
| 12 | `bisector_point_exists` | 697 | hl:825 | 待人工确认 | GIANT |
| 13 | `POLYSORT_BIJ2` | 1359 | hl:1964 | 待人工确认 | GIANT |
| 14 | `EUSOTYP_simple` | 1381 | hl:2112 | 待人工确认 | GIANT |

★ = r2 项 11 的 patch 11（补 ≠∅ 前提）**随之撤回**：DEF-FIX 落地后其前提由
`facetOfC` 自带（`.2.1`），陈述回到 HOL 镜像，`facet_rep_uniq_fixed` 证明体 +
`have h1ne := h1.2.1` 即重填。须在 statement-fix-proposals.md 登记撤回注记，
防止修复波对同一陈述双补丁。

连带根件：`eus1`（PA22:325，sorry，hl:85）与 `facet_rep_uniq` 是全族的上游；
eus1 路线 = FACET_OF_POLYHEDRON ℂ 版 + 单位法向缩放（**已核** HOL 前半）。GIANT
档的重填在 §2.3 kit 落地前不要开工。

### 3b. 陈奏为真 / 变机械（CONE0 族 + aff_gt 陈述同病位）

| 定理 | PA22 行 | 现状 | 定义纠正后 | 重填路线与档 |
|---|---|---|---|---|
| `CONE0_AFF_GT` | 2358 | rfl"已证"（弱语义） | 陈述改 affGt，仍 rfl | 零工作量（随补丁） |
| `cone0_subset_lune` | 2120 | **已填**（弱语义+RHS 病） | 陈述 RHS 改 affGt；原证明的 `have hv' : Affsign (0 ≤ ·) := hv` 强制失效，严格→严格系数逐字搬运（`hsign` 直接给出 >0） | 机械 |
| `AFF_GT_RELATIVE_INTERIOR` | 2213 | sorry（弱陈述为假：边界点不在相对内部） | 陈述改 affGt 后为真 | hl:3120 `EXPLICIT_SUBSET_RELATIVE_INTERIOR_CONVEX_HULL` 路线；中等 |
| `CONE0_FCHANGED_AFF_GT` | 2292 | sorry，**弱语义下假**（端点反例，纸面已核） | 变真 | hl:3185；中等 |
| `CONE0_SCALE` | 2379 | sorry（弱强皆真） | 不变真 | hl:3792，系数重整 `f u0 ↦ f u0 / t`；机械-中等 |
| `CONE0_FCHANGED_SCALE` | 2385 | sorry，弱语义下假（待人工确认） | 变真 | hl:3837 = CONE0_SCALE + CONE0_FCHANGED 拼装；中等 |
| `CONE0_FCHANGED` | 2297 | sorry，弱语义下假（待人工确认） | 变真 | hl:3288；GIANT（原标签不变） |
| `CONE0_SUBSET_WEDGE` | 2352 | sorry（弱语义真伪未逐一验证） | 变真 | hl:3752；GIANT |
| `gotcjah_sol_half` | 2393 | sorry | 陈述 affGe→affGt（hunk 5） | hl:3879；GIANT（GOTCJAH 测度专项，playbook 已列） |

说明：DECISIONS 2026-09-29 条的 "CONE0_FCHANGED 家族 5 枚假化" 按本表精确化为
——弱语义下**确证为假**的 1 枚（CONE0_FCHANGED_AFF_GT，纸面）+ 待核 3 枚
（CONE0_FCHANGED/FCHANGED_SCALE，机制同）+ 修复后反而需改述的 1 枚
（CONE0_AFF_GT）；假化判定不影响修复路线（一律以 HOL 原文为准），机器验证可留
到重填波顺手做。playbook §5.1 相应黑名单条目在修复落地后划掉。

### 3c. 解冻项（提案 12/13a）

| 项 | PA22 行 | HOL | 解冻后路线 | 档 |
|---|---|---|---|---|
| 12 `affine_facet_hyper` | 564 | hl:320 | 新 defs 下陈述即 HOL 镜像；AFF_DIM_EQ_AFFINE_HULL + `affDimC` 超平面 kit（§2.3 第 1 行） | 中等（kit 后）；kit 前冻结 |
| 13a `pad2d3d_facet` | 1275 | hl:1737 | 陈述本就混合 V3 前提/FacetOf 与 ℂ 结论/facetOfC；纠正后计数口径统一；BIJECTIONS_HAS_SIZE + `FACET_OF_LINEAR_IMAGE` ℂ 版（pad2d3d 线性等距） | GIANT |

冻结纪律：两枚在对应 kit 落地前保持黑名单（假陈述无人可填 → 纠正后为真但仍
sorry，入重填队列）。

### 3d. 重填优先序估算

- **第 1 波（机械，~5 枚）**：CONE0_AFF_GT（随补丁零成本）、cone0_subset_lune、
  facet_rep_uniq（用 patch 11 证明体）、CONE0_SCALE、CONE0_FCHANGED_SCALE；
- **第 2 波（中等，~4 枚）**：facet_rep_in_facet、AFF_GT_RELATIVE_INTERIOR、
  CONE0_FCHANGED_AFF_GT、affine_facet_hyper；
- **kit 波（一次性）**：affDimC kit（~150 行）→ FACET_OF_POLYHEDRONC_EXPLICIT
  （~500 行，关键路径）→ CONTAINS_BALL_AFFINE_HULL ℂ 版；
- **第 3 波（GIANT，~13 枚）**：eus1 → POLYHEDRON_MEMBER → facet_rep_in_poly /
  facet_arg_lt_pi / insert_v / facet_rep_a_uniq → poly_sort 4 枚 →
  bisector_point_exists → POLYSORT_BIJ2 / EUSOTYP_simple → CONE0_FCHANGED /
  CONE0_SUBSET_WEDGE → pad2d3d_facet → gotcjah_sol_half（可拆多 lane 并行；
  gotcjah 仍归 GOTCJAH 专项）。
- 体量对照：本清单 GIANT 档总数 ~13 枚 + kit ~900 行，与 PA22 现存 sorry 存量
  （53 @r2）同量级，属专项波而非单 lane 波。

---

## §4 DEF-FIX 闸门规程

### 4.1 机制（复用 STATEMENT-FIX 的 SF_PATCH 骨架）

`GATE_MODE=DEF-FIX` + `DF_PATCH`（补丁存档
`docs/statement-fix-proposals-patches/DEF-FIX-planar-encoding.patch`）+
`DF_ITEM=planar-encoding-fix`（本章程）。补丁含 def 行与**白名单删除行**
（`p22_ball_face_contra` 块）与**白名单 sorry 行**（§3a 的 14+1 枚回退），这三点
是对 SF 机制的扩展，逐项机器校验如下。

### 4.2 验收清单（闸门逐道）

1. **逐字一致性**（同 SF①）：工作区 diff 与补丁逐行多重集一致，上下文漂移
   不敏感、内容严格；
2. **def 行逐字 + 名字存在性**：补丁新增 def 引用的每个名字
   （`affGt`、`affGe`、`vectorSpan`、`Module.finrank`、`dot2`、`faceOfC`、
   `openSegment`）必须已在依赖闭包中（scratch §2.2 已证 elaboration 可行——
   防止"补丁假设了不存在的辅助件"）；
3. **波及面核对**：diff 触及的每个定理/def 名 ∈ 本章程 §2/§3 清单，超出即拒
   （防借道夹带）；
4. **陈述冻结**：hunk 3/4/5 之外的定理陈述行零改动；hunk 5 的三处陈述纠正
   （affGe→affGt）逐字对照本文件；
5. **构建绿**：`lake build Kepler.Text.PackingAuto22` 自然退出 0 error（回退
   sorry 保证可构建）；
6. **sorry 台账**：新增 15 条 `sorry -- DEF-FIX:` 行与 §3a/§3b 清单逐一对应，
   DEBT.md 计数 +15 可追溯；其余新增行禁词规则（sorry/admit/native_decide）
   不变；
7. **白名单删除核对**：被删行集 = 恰好 PA22:128–168（docstring +
   p22_ball_face_contra），以行前缀校验；
8. **周边回归**：LocalBridge.lean（唯一下游）构建绿；PA22 在 {PA22, PA23,
   Polytope, TopologyFan} 收官根下全绿（§5.4 PA22 惯例）；
9. **折算登记**：按 statement-fidelity 附录惯例登记——`affDimC` 系
   Polytope.affDim 的 planar 孪生（与 dot2/faceOfC 同层），未来全局去孪生提案
   应一并收编；`Affsign` 有限性显式化口径不变（Geom/Aff.lean 头注）。

### 4.3 定义与重填的 commit 策略：**分开 commit、同批推进**（建议）

**建议：DEF-FIX 补丁独立成一个 commit（闸门验收后立即落地），重填按 §3d 分波
各自普通验收 commit。** 理由：

1. **验收性质不同**：定义变更是"人类审定对象"（逐字补丁，闸门豁免），重填是
   "编排者验收对象"（普通填证五道闸）——绑在一个 PR 会让两套验收互相拖累；
2. **止血优先**：定义不落地，14 枚假绿填证和 CONE0 假陈述就一直在树上冒充进度；
   补丁落地当天树的状态就从"假绿"变为"显式债务"（15 条 DEF-FIX sorry 入
   DEBT.md），符合 2026-09-17 决策"债务以台账为唯一权威刻度"的精神；
3. **重填周期长**：GIANT 档 ~13 枚 + kit ~900 行是周级工作量，绑定会让定义
   纠正被重填进度无限期阻塞，且阻塞期内 statement-fix 队列无法处理任何
   facetOfC 相关项（旧语义上继续堆补丁 = 未来返工）。

配套顺序硬约束（闸门之外的流程纪律）：

- 补丁落地**同日**登记：DEBT.md 刷新 + playbook §5.1 黑名单更新（PA22 r2 三枚
  根因条目改写为"待重填"）+ statement-fix-proposals.md 项 11 撤回注记；
- 重填期间 **STATEMENT-FIX 队列冻结**一切触及 `facetOfC`/`polyhedronC`/`cone0P22`
  消费者的新补丁（防止旧语义补丁堆积）；
- 项目关闭条件 = §3a/§3b/§3c 全部 25 枚（14 重填 + 9 CONE0 族 + 2 解冻）离账，
  届时在 DECISIONS 2026-09-29 条追加"已闭环"注记。

### 4.4 执行顺序建议（对应 DECISIONS (a)→(b)→(c)）

1. （本轮，已完成）本章程 + scratch 机器验证 + 补丁草案正文；
2. 用户审定 §2 补丁 → 正式 diff 存档 `DEF-FIX-planar-encoding.patch`；
3. DEF-FIX 闸门验收 → **Commit 1**（定义纠正 + 回退）+ 台账三件套；
4. 第 1 波机械重填（5 枚）——立即清账、验证补丁可用性；
5. kit 波（affDimC → FACET_OF_POLYHEDRONC_EXPLICIT）——关键路径；
6. 第 2 波中等（4 枚）与第 3 波 GIANT（13 枚，可多 lane）；
7. 收尾：黑名单划账、项 11 撤回注记、12/13a 解冻销账、DECISIONS 追加闭环条。

---

## 附：侦察轮机器验证与只读纪律记录

- scratch：`/tmp/ScratchDefFix.lean`（untracked，验证后已删）：新定义形态 +
  §2.2 全部基本引理端到端编译 **0 error、0 sorry**；`#print axioms` =
  propext + choice + Quot.sound（Classical.choice 系 `Classical` open 的常规
  足迹，无 sorryAx）；
- 本轮零 .lean 改动、零 tracked 文件改动，唯一仓库写入 = 本文档；
  （工作树中 `Assembly.lean`/`LocalAuto38.lean` 的未提交改动系并行 lane 所有，
  本轮未触碰；PA22 pristine。）
- 待人工确认清单（预算所限未猜）：§3a 表中标注"待人工确认"的 11 枚 HOL 证明体
  细读；CONE0 弱语义假化 3 枚的机器反例；`wedge`/`rconeGt`/`sol` 等 GOTCJAH
  邻接 kit 对 cone0 严格化的隐含依赖（重填第 3 波时核查）。
