/-
Kepler.Text.PolyAuto1 — polyhedron.hl 第 1 批（:122–:182，不变性记账 10 条）

源：`scripts/polyhedron.hl`（module Polyhedron，Invariance theorems 块开头）。
本批 = `graph`/`cyclic_set`/`fan1`/`fan2` 对平移与线性双射的不变性
（对应 HOL 的 `GEOM_TRANSLATE_TAC`/`GEOM_TRANSFORM_TAC` 机制；这些
   定理随后经 `add_translation_invariants`/`add_linear_invariants` 注册，
   注册动作本身不移植，见 Kepler/Text/ConformingDefs.lean 同类注记）。

编码约定（本文件起为 polyhedron.hl 各批沿用）：
- `real^3` ↔ `V3`（Kepler/Geom/Azim.lean:33）；`(real^3->bool)` ↔ `Set V3`；
  `(real^3->bool)->bool` ↔ `Set (Set V3)`。
- 平移 `IMAGE (\x. a + x) s` ↔ `(fun z => a + z) '' s`（点加形式，
  与 HOL `a + x` 逐字对应；加法交换故与 `y + a` 等价）。
- 线性像 `IMAGE f s` ↔ `f '' s`，`f : V3 →L[ℝ] V3`（仓库首次引入该编码；
  ContinuousLinearMap 自带 linear，HOL 侧 `linear f` 前提即被类型吸收，
  单射前提 `!x y. f x = f y ==> x = y` ↔ `∀ x y, f x = f y → x = y`）。
- `affine hull {v, w}` ↔ `affineSpan ℝ ({v, w} : Set V3)`（同
  Kepler/Geom/SolidAngle.lean:90 用法）；`h % (v - w)` ↔ `h • (v - w)`。
- `cyclic_set` 此前未移植（Kepler/Text/TopologyFan.lean:41 注记），本文件
  以 `cyclicSet` 补上定义，`CYCLIC_SET` 即其 unfold 特征。
- `GRAPH` 与 Kepler/Text/Planarity.lean:4965 同名同义，本批改名 `GRAPH_p1`。

各行定理逐条 `sorry`；均为公开 API，供 polyhedron.hl 后续批（p1 内后继
文件）以及 `FAN`(3-7) 批使用。
-/

import Kepler.Text.Fan

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan

/-! ## cyclic_set（sphere/hypermap 层定义，polyhedron.hl:126 处 unfold） -/

/-- HOL `cyclic_set W v w`：`v ≠ w`、`W` 有限、`W` 中任两元素之差不落在
`v - w` 的非零倍线上（等距圆周packing 的排挤前提），且 `W` 与弦
`{v, w}` 的仿射包不交。conjunct 顺序与 `CYCLIC_SET` 的展开一致。 -/
def cyclicSet (W : Set V3) (v w : V3) : Prop :=
  v ≠ w ∧ W.Finite ∧
    (∀ p ∈ W, ∀ q ∈ W, ∀ h : ℝ, p - q = h • (v - w) → p = q) ∧
    W ∩ affineSpan ℝ ({v, w} : Set V3) = ∅

/-- HOL polyhedron.hl :122-124
`GRAPH = prove (`!E. graph E <=> !e. e IN E ==> e HAS_SIZE 2`)`
（GRAPH 与 Kepler/Text/Planarity.lean:4965 `Kepler.Text.GRAPH` 同名同义，
   本批改名 `GRAPH_p1`；HOL `e HAS_SIZE 2` ↔ 仓库 `Graph` 的显式有限版
   `∃ hf : e.Finite, hf.toFinset.card = 2`，同 Planarity.lean 渲染。）
证明：`Graph`（Kepler/Text/Fan.lean:37）即右边逐点定义，双向 `exact`。
候选：`Graph` Kepler/Text/Fan.lean:37；同义已证 Kepler/Text/Planarity.lean:4965。 -/
theorem GRAPH_p1 (E : Set (Set V3)) :
    Graph E ↔ ∀ e ∈ E, ∃ hf : e.Finite, hf.toFinset.card = 2 := by
  constructor
  · intro h e he
    exact h e he
  · intro h e he
    exact h e he

/-- HOL polyhedron.hl :126-132
```
CYCLIC_SET = prove
 (`cyclic_set W v w <=>
         ~(v = w) /\
         FINITE W /\
         (!p q h. p IN W /\ q IN W /\ p - q = h % (v - w) ==> p = q) /\
         W INTER affine hull {v, w} = {}`)
```
证明：`cyclicSet`（本文件上方）即按此式定义，unfold 后双向 `exact`
（仓库此前未移植 cyclic_set，见 TopologyFan.lean:41 注记）。
候选：`cyclicSet` Kepler/Text/PolyAuto1.lean（本文件）；仿射包记法
   Kepler/Geom/SolidAngle.lean:90。 -/
theorem CYCLIC_SET (W : Set V3) (v w : V3) :
    cyclicSet W v w ↔ v ≠ w ∧ W.Finite ∧
      (∀ p ∈ W, ∀ q ∈ W, ∀ h : ℝ, p - q = h • (v - w) → p = q) ∧
      W ∩ affineSpan ℝ ({v, w} : Set V3) = ∅ := by
  rfl

/-- HOL polyhedron.hl :134-136
```
CYCLIC_SET_TRANSLATION_EQ = prove
 (`!a:real^N s x y.
    cyclic_set (IMAGE (\x. a + x) s) (a + x) (a + y) <=> cyclic_set s x y`)
```
证明：unfold `CYCLIC_SET` 后逐 conjunct 平移：点像 `(· + a) '' s` 有限
（`Set.Finite.image`），`p - q` 与 `affineSpan` 均平移不变
（差与 `h • (v - w)` 中的平移项相消；仿射包经平移映射）。
候选：`Set.Finite.image` Mathlib/Data/Set/Finite/Basic.lean:566；
   `Set.mem_image` Mathlib/Data/Set/Operations.lean:136；
   `Set.image_congr` Mathlib/Data/Set/Image.lean:211。 -/
theorem CYCLIC_SET_TRANSLATION_EQ (a x y : V3) (s : Set V3) :
    cyclicSet ((fun z => a + z) '' s) (a + x) (a + y) ↔ cyclicSet s x y := by
  have hfinIff : ((fun z : V3 => a + z) '' s).Finite ↔ s.Finite :=
    Set.finite_image_iff (fun p _ q _ h => add_left_cancel h)
  have hline : ∀ u v : V3, ∀ r : ℝ,
      AffineMap.lineMap (a + u) (a + v) r = a + AffineMap.lineMap u v r := by
    intro u v r
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    rw [add_sub_add_left_eq_sub]
    abel
  constructor
  · rintro ⟨hne, hfin, hdiff, hspan⟩
    refine ⟨fun h => hne (by rw [h]), hfinIff.mp hfin, ?_, ?_⟩
    · intro p hp q hq hs hheq
      have hs' : (fun z : V3 => a + z) p - (fun z : V3 => a + z) q
          = hs • ((fun z : V3 => a + z) x - (fun z : V3 => a + z) y) := by
        simp only [add_sub_add_left_eq_sub]
        exact hheq
      exact add_left_cancel (hdiff (a + p) ⟨p, hp, rfl⟩ (a + q) ⟨q, hq, rfl⟩ hs hs')
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Set.mem_inter_iff] at hz
      obtain ⟨hzs, hzl⟩ := hz
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hzl
      obtain ⟨r, hr⟩ := hzl
      exact (Set.eq_empty_iff_forall_notMem.mp hspan) (a + z)
        (⟨⟨z, hzs, rfl⟩,
        mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r, by
          rw [hline x y r]; exact congrArg (fun w => a + w) hr⟩⟩)
  · rintro ⟨hne, hfin, hdiff, hspan⟩
    refine ⟨fun h => hne (add_left_cancel h), hfinIff.mpr hfin, ?_, ?_⟩
    · intro p hp q hq hs hheq
      rw [Set.mem_image] at hp hq
      obtain ⟨p', hp's, rfl⟩ := hp
      obtain ⟨q', hq's, rfl⟩ := hq
      simp only [add_sub_add_left_eq_sub] at hheq
      exact congrArg (fun w => a + w) (hdiff p' hp's q' hq's hs hheq)
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Set.mem_inter_iff] at hz
      obtain ⟨⟨w, hw, rfl⟩, hzw⟩ := hz
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hzw
      obtain ⟨r, hr⟩ := hzw
      exact (Set.eq_empty_iff_forall_notMem.mp hspan) w
        (⟨hw, mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r,
        add_left_cancel (by rw [← hline x y r]; exact hr)⟩⟩)

/-- HOL polyhedron.hl :139-144
```
CYCLIC_SET_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s x y.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (cyclic_set (IMAGE f s) (f x) (f y) <=> cyclic_set s x y)`)
```
证明：HOL `linear f` 由 `f : V3 →L[ℝ] V3` 类型吸收；单射性经
`injective_iff_map_eq_zero` 换为核平凡，差向量按线性性提系数，
仿射包经线性映射（injective 时保持交空）。
候选：`injective_iff_map_eq_zero` Mathlib/Algebra/Group/Hom/Basic.lean:193；
   `Set.Finite.image` Mathlib/Data/Set/Finite/Basic.lean:566；
   `Set.mem_image` Mathlib/Data/Set/Operations.lean:136。 -/
theorem CYCLIC_SET_LINEAR_IMAGE (f : V3 →L[ℝ] V3)
    (hf : ∀ x y : V3, f x = f y → x = y) (s : Set V3) (x y : V3) :
    cyclicSet (f '' s) (f x) (f y) ↔ cyclicSet s x y := by
  have hfinIff : (f '' s).Finite ↔ s.Finite :=
    Set.finite_image_iff (fun p _ q _ h => hf p q h)
  have hline : ∀ u v : V3, ∀ r : ℝ,
      AffineMap.lineMap (f u) (f v) r = f (AffineMap.lineMap u v r) := by
    intro u v r
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    rw [map_add, map_smul, map_sub]
  constructor
  · rintro ⟨hne, hfin, hdiff, hspan⟩
    refine ⟨fun h => hne (congrArg f h), hfinIff.mp hfin, ?_, ?_⟩
    · intro p hp q hq hs hheq
      have hs' : f p - f q = hs • (f x - f y) := by
        rw [← map_sub, ← map_sub, ← map_smul]
        exact congrArg f hheq
      exact hf p q (hdiff (f p) ⟨p, hp, rfl⟩ (f q) ⟨q, hq, rfl⟩ hs hs')
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Set.mem_inter_iff] at hz
      obtain ⟨hzs, hzl⟩ := hz
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hzl
      obtain ⟨r, hr⟩ := hzl
      exact (Set.eq_empty_iff_forall_notMem.mp hspan) (f z)
        (⟨⟨z, hzs, rfl⟩,
        mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r, by
          rw [hline x y r]; exact congrArg f hr⟩⟩)
  · rintro ⟨hne, hfin, hdiff, hspan⟩
    refine ⟨fun h => hne (hf x y h), hfinIff.mpr hfin, ?_, ?_⟩
    · intro p hp q hq hs hheq
      rw [Set.mem_image] at hp hq
      obtain ⟨p', hp's, rfl⟩ := hp
      obtain ⟨q', hq's, rfl⟩ := hq
      have hheq' : f p' - f q' = hs • (f x - f y) := hheq
      have h2 : f (p' - q') = f (hs • (x - y)) := by
        rw [map_sub, hheq', ← map_sub, ← map_smul]
      refine congrArg f (hdiff p' hp's q' hq's hs (hf _ _ h2))
    · rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Set.mem_inter_iff] at hz
      obtain ⟨⟨w, hw, rfl⟩, hzw⟩ := hz
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hzw
      obtain ⟨r, hr⟩ := hzw
      exact (Set.eq_empty_iff_forall_notMem.mp hspan) w
        ⟨hw, mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r,
        hf _ _ (by rw [← hline x y r]; exact hr)⟩⟩

/-- HOL polyhedron.hl :151-153
```
GRAPH_TRANSLATION_EQ = prove
 (`!a:real^N E. graph (IMAGE (IMAGE (\x. a + x)) E) <=> graph E`)
```
证明：unfold `GRAPH_p1` 后逐边：`e ∈ 双重像` ↔ `e = (· + a) '' e'`，
平移为双射故 `card` 不变（`Finset.card_image_of_injOn` 一类）。
候选：`Set.mem_image` Mathlib/Data/Set/Operations.lean:136；
   `Set.image_congr` Mathlib/Data/Set/Image.lean:211；
   `Graph` Kepler/Text/Fan.lean:37。 -/
theorem GRAPH_TRANSLATION_EQ (a : V3) (E : Set (Set V3)) :
    Graph ((fun s : Set V3 => (fun z => a + z) '' s) '' E) ↔ Graph E := by
  constructor
  · intro hG e he
    have hiff : ((fun z : V3 => a + z) '' e).Finite ↔ e.Finite :=
      Set.finite_image_iff (fun p _ q _ h => add_left_cancel h)
    obtain ⟨hf, hcard⟩ := hG ((fun z : V3 => a + z) '' e) ⟨e, he, rfl⟩
    have he' : e.Finite := hiff.mp hf
    have h1 := Set.Finite.toFinset_image (fun z : V3 => a + z) he' hf
    rw [h1, Finset.card_image_of_injOn (fun p _ q _ h => add_left_cancel h)] at hcard
    exact ⟨he', hcard⟩
  · intro hG e he
    rw [Set.mem_image] at he
    obtain ⟨e', he'E, rfl⟩ := he
    obtain ⟨hf, hcard⟩ := hG e' he'E
    have hfin : ((fun z : V3 => a + z) '' e').Finite :=
      Set.Finite.image (fun z : V3 => a + z) hf
    refine ⟨hfin, ?_⟩
    rw [Set.Finite.toFinset_image (fun z : V3 => a + z) hf hfin]
    rw [Finset.card_image_of_injOn (fun p _ q _ h => add_left_cancel h)]
    exact hcard

/-- HOL polyhedron.hl :155-158
```
GRAPH_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (graph(IMAGE (IMAGE f) E) <=> graph E)`)
```
证明：同上逐边，单射线性映射限制在有限集上仍单射，`toFinset.card`
在像下不变。
候选：`Set.mem_image` Mathlib/Data/Set/Operations.lean:136；
   `injective_iff_map_eq_zero` Mathlib/Algebra/Group/Hom/Basic.lean:193；
   `Graph` Kepler/Text/Fan.lean:37。 -/
theorem GRAPH_LINEAR_IMAGE_EQ (f : V3 →L[ℝ] V3)
    (hf : ∀ x y : V3, f x = f y → x = y) (E : Set (Set V3)) :
    Graph ((fun s : Set V3 => f '' s) '' E) ↔ Graph E := by
  constructor
  · intro hG e he
    have hiff : (f '' e).Finite ↔ e.Finite :=
      Set.finite_image_iff (fun p _ q _ h => hf p q h)
    obtain ⟨hfin, hcard⟩ := hG (f '' e) ⟨e, he, rfl⟩
    have he' : e.Finite := hiff.mp hfin
    have h1 := Set.Finite.toFinset_image f he' hfin
    rw [h1, Finset.card_image_of_injOn (fun p _ q _ h => hf p q h)] at hcard
    exact ⟨he', hcard⟩
  · intro hG e he
    rw [Set.mem_image] at he
    obtain ⟨e', he'E, rfl⟩ := he
    obtain ⟨hfe, hcard⟩ := hG e' he'E
    have hfin' : (f '' e').Finite := Set.Finite.image f hfe
    refine ⟨hfin', ?_⟩
    rw [Set.Finite.toFinset_image f hfe hfin']
    rw [Finset.card_image_of_injOn (fun p _ q _ h => hf p q h)]
    exact hcard

/-- HOL polyhedron.hl :161-163
```
FAN1_TRANSLATION_EQ = prove
 (`!a:real^N x V E.
        fan1(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan1(x,V,E)`)
```
证明：`fan1`（Kepler/Text/Fan.lean:41）= `V.Finite ∧ V ≠ ∅`，平移像
有限（`Set.Finite.image`）、非空（`Set.image_nonempty`），与 apex 无关。
候选：`Set.Finite.image` Mathlib/Data/Set/Finite/Basic.lean:566；
   `Set.image_nonempty` Mathlib/Data/Set/Image.lean:393；
   `fan1` Kepler/Text/Fan.lean:41。 -/
theorem FAN1_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan1 (a + x) ((fun z => a + z) '' V)
      ((fun s : Set V3 => (fun z => a + z) '' s) '' E) ↔ fan1 x V E := by
  show ((fun z => a + z) '' V).Finite ∧ (fun z => a + z) '' V ≠ ∅ ↔ V.Finite ∧ V ≠ ∅
  have hinj : Function.Injective (fun z : V3 => a + z) := fun p q h => add_left_cancel h
  have hfinIff : ((fun z : V3 => a + z) '' V).Finite ↔ V.Finite :=
    Set.finite_image_iff (fun p _ q _ h => add_left_cancel h)
  have hneq : ((fun z : V3 => a + z) '' V) = ∅ ↔ V = ∅ := Set.image_eq_empty
  constructor
  · rintro ⟨hfin, hne⟩
    refine ⟨hfinIff.mp hfin, ?_⟩
    intro h
    exact hne (hneq.mpr h)
  · rintro ⟨hfin, hne⟩
    refine ⟨Set.Finite.image (fun z : V3 => a + z) hfin, ?_⟩
    intro h
    exact hne (hneq.mp h)

/-- HOL polyhedron.hl :167-170
```
FAN1_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan1(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan1(x,V,E))`)
```
证明：`fan1` 与 apex 无关；`V.Finite` 经 `Set.Finite.image` 保持，
`V ≠ ∅` 经 `Set.image_nonempty` 保持（无需单射）。
候选：`Set.Finite.image` Mathlib/Data/Set/Finite/Basic.lean:566；
   `fan1` Kepler/Text/Fan.lean:41。 -/
theorem FAN1_LINEAR_IMAGE_EQ (f : V3 →L[ℝ] V3)
    (hf : ∀ x y : V3, f x = f y → x = y) (x : V3) (V : Set V3)
    (E : Set (Set V3)) :
    fan1 (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) ↔ fan1 x V E := by
  show (f '' V).Finite ∧ f '' V ≠ ∅ ↔ V.Finite ∧ V ≠ ∅
  have hfinIff : (f '' V).Finite ↔ V.Finite := Set.finite_image_iff (fun p _ q _ h => hf p q h)
  have hneq : f '' V = ∅ ↔ V = ∅ := Set.image_eq_empty
  constructor
  · rintro ⟨hfin, hne⟩
    refine ⟨hfinIff.mp hfin, ?_⟩
    intro h
    exact hne (hneq.mpr h)
  · rintro ⟨hfin, hne⟩
    refine ⟨Set.Finite.image f hfin, ?_⟩
    intro h
    exact hne (hneq.mp h)

/-- HOL polyhedron.hl :173-175
```
FAN2_TRANSLATION_EQ = prove
 (`!a:real^N x V E.
        fan2(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan2(x,V,E)`)
```
证明：`fan2`（Kepler/Text/Fan.lean:44）= `x ∉ V`；`a + x ∈ (· + a) '' V`
↔ `x ∈ V`（`Set.mem_image` + 加法双射）。
候选：`Set.mem_image` Mathlib/Data/Set/Operations.lean:136；
   `fan2` Kepler/Text/Fan.lean:44。 -/
theorem FAN2_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan2 (a + x) ((fun z => a + z) '' V)
      ((fun s : Set V3 => (fun z => a + z) '' s) '' E) ↔ fan2 x V E := by
  show a + x ∉ (fun z => a + z) '' V ↔ x ∉ V
  constructor
  · intro H hmem
    exact H ⟨x, hmem, rfl⟩
  · intro H v
    obtain ⟨w, hw, hwf⟩ := v
    have hwf' : a + w = a + x := hwf
    have hwx : w = x := add_left_cancel hwf'
    exact H (by rw [← hwx]; exact hw)

/-- HOL polyhedron.hl :179-182
```
FAN2_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan2(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan2(x,V,E))`)
```
证明：`f x ∈ f '' V` ↔ `x ∈ V` 由单射性（`Set.mem_image_eq` 一类）。
候选：`Set.mem_image` Mathlib/Data/Set/Operations.lean:136；
   `injective_iff_map_eq_zero` Mathlib/Algebra/Group/Hom/Basic.lean:193；
   `fan2` Kepler/Text/Fan.lean:44。 -/
theorem FAN2_LINEAR_IMAGE_EQ (f : V3 →L[ℝ] V3)
    (hf : ∀ x y : V3, f x = f y → x = y) (x : V3) (V : Set V3)
    (E : Set (Set V3)) :
    fan2 (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) ↔ fan2 x V E := by
  show f x ∉ f '' V ↔ x ∉ V
  constructor
  · intro H hmem
    exact H ⟨x, hmem, rfl⟩
  · intro H v
    obtain ⟨w, hw, hwf⟩ := v
    exact H (by rw [← hf w x hwf]; exact hw)

end Kepler.Text
