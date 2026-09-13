/-
Port of the HOL Light Flyspeck polyhedron theory (Fan chapter), slice 2:
skeleton pass of `scripts/polyhedron.hl` :185-:282 (batch 2, 10 theorems).

Source: `scripts/polyhedron.hl` (persistent copy of Flyspeck book
formalization `reference/flyspeck/text_formalization/fan/polyhedron.hl`).

Coverage (batch 2 of polyhedron.hl, `let … = prove` lines :185-:261):
- `FAN3_TRANSLATION_EQ` (:185)          `FAN3_LINEAR_IMAGE_EQ` (:191)
- `FAN4_TRANSLATION_EQ` (:204)          `FAN4_LINEAR_IMAGE_EQ` (:210)
- `FAN5_TRANSLATION_EQ` (:216)          `FAN5_LINEAR_IMAGE_EQ` (:222)
- `FAN6_TRANSLATION_EQ` (:230)          `FAN6_LINEAR_IMAGE_EQ` (:236)
- `FAN7_TRANSLATION_EQ` (:242)          `FAN7_LINEAR_IMAGE_EQ` (:251)
Batch 1 (:161-:184: `GRAPH_*`, `FAN1_*`, `FAN2_*`) and batch 3 (:283 onward:
`FAN_TRANSLATION_EQ`, `FAN_LINEAR_IMAGE_EQ`, `BASE_POINT_FAN_*`,
`SET_OF_EDGE_*`) are NOT in this file.

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `fan3(x,V,E) <=> !e. e IN E ==> CARD e = 2` is NOT ported as a
  standalone def; it coincides with `Graph` (Kepler/Text/Fan.lean:39), the
  encoding already used inside `FAN` (Fan.lean:56). Statements below use
  `Graph` directly (the `x`/`V` arguments of HOL `fan3` are dummies and are
  kept as explicit-but-unused parameters for verbatim shape).
- HOL `fan4(x,V,E) <=> !e. e IN E ==> e SUBSET V` and
  HOL `fan5(x,V,E) <=> !v. v IN V ==> v IN UNIONS E` are NOT ported as
  defs anywhere in the repo (the `FAN` encoding absorbs fan4 as
  `⋃₀ E ⊆ V`, Fan.lean:56); both are inlined in the statements below.
- HOL `fan6`/`fan7` ↔ `fan6`/`fan7` (Kepler/Text/Fan.lean:47/51).
- `IMAGE (\x. a + x) V` ↔ `(fun y : V3 => a + y) '' V`;
  `IMAGE (IMAGE (\x. a + x)) E` ↔
  `(fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E` (pointwise image on
  the edge set). Likewise for a linear map `f`.
- HOL `linear f /\ (!x y. f x = f y ==> x = y)` ↔ a bundled linear map
  `f : V3 →ₗ[ℝ] V3` with hypothesis `Function.Injective f` (repo idiom,
  cf. Kepler/Text/PlanarityAuto12.lean:580); HOL's general `real^M ->
  real^N` type is narrowed to the V3-typed fan definitions.
- These ten lemmas are the invariance register entries that HOL feeds to
  `add_translation_invariants`/`add_linear_invariants` (:263-:280); the
  register mechanism itself is HOL-specific and not ported.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan

/-! ## 公共引理（fan3/fan4/fan5 的逐边搬运，polyhedron.hl:185-:228 证明支件） -/

/-- 平移 `fun y => a + y` 是单射。 -/
private theorem addV3_right_injective (a : V3) :
    Function.Injective (fun y : V3 => a + y) := by
  intro p q h
  have h' : a + p = a + q := h
  exact add_left_cancel h'

/-- `Graph` 对双射的逐边像不变（FAN3 的核心：平移/单射线性像下基数 2 传递）。 -/
private theorem graph_image_eq {g : V3 → V3} (hg : Function.Injective g)
    {E : Set (Set V3)} : Graph ((fun e : Set V3 => g '' e) '' E) ↔ Graph E := by
  classical
  constructor
  · intro h e he
    obtain ⟨hfin, hcard⟩ := h (g '' e) ⟨e, he, rfl⟩
    have hfin' : e.Finite := hfin.of_finite_image hg.injOn
    refine ⟨hfin', ?_⟩
    rw [← Finset.card_image_of_injOn hg.injOn, ← Set.Finite.toFinset_image g hfin' hfin]
    exact hcard
  · intro h e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨hfin, hcard⟩ := h e₀ he₀
    refine ⟨hfin.image g, ?_⟩
    rw [Set.Finite.toFinset_image g hfin, Finset.card_image_of_injOn hg.injOn]
    exact hcard

/-- `fan4` 内联条款对双射逐边像的不变。 -/
private theorem fan4c_image_eq {g : V3 → V3} (hg : Function.Injective g)
    {V : Set V3} {E : Set (Set V3)} :
    (∀ e ∈ (fun e : Set V3 => g '' e) '' E, e ⊆ g '' V) ↔ ∀ e ∈ E, e ⊆ V := by
  constructor
  · intro h e he
    have h' := h (g '' e) ⟨e, he, rfl⟩
    rwa [Set.image_subset_iff, Set.preimage_image_eq V hg] at h'
  · intro h e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact Set.image_mono (h e₀ he₀)

/-- `fan5` 内联条款对单射逐边像的不变（正向需单射性消去 `g`）。 -/
private theorem fan5c_image_eq {g : V3 → V3} (hg : Function.Injective g)
    (V : Set V3) (E : Set (Set V3)) :
    (∀ v ∈ g '' V, v ∈ ⋃₀ ((fun e : Set V3 => g '' e) '' E)) ↔ ∀ v ∈ V, v ∈ ⋃₀ E := by
  constructor
  · intro h v hv
    obtain ⟨e, he, hv⟩ := Set.mem_sUnion.1 (h (g v) ⟨v, hv, rfl⟩)
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨w, hw, hwv⟩ := hv
    refine Set.mem_sUnion.2 ⟨e₀, he₀, ?_⟩
    rwa [← hg hwv]
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨e, he, hv⟩ := Set.mem_sUnion.1 (h w hw)
    exact Set.mem_sUnion.2 ⟨g '' e, ⟨e, he, rfl⟩, ⟨w, hv, rfl⟩⟩

/-! ## fan6/fan7 的不变性（polyhedron.hl:230-:261） -/

/-- V3 上 `+ᵥ` 即 `+`（向量空间视作自身的仿射扭转群）。 -/
private theorem vadd_eq_addV3 (v p : V3) : v +ᵥ p = v + p := rfl

/-- `Collinear` 的平移不变：方向向量不变、基点随平移。 -/
private theorem collinear_translation_iff (s : Set V3) (a : V3) :
    Collinear ℝ ((fun y : V3 => a + y) '' s) ↔ Collinear ℝ s := by
  rcases Set.eq_empty_or_nonempty s with hs | ⟨p₀, hp₀⟩
  · subst hs
    simp [collinear_empty]
  · have hmem : a + p₀ ∈ (fun y : V3 => a + y) '' s := ⟨p₀, hp₀, rfl⟩
    rw [collinear_iff_of_mem hmem, collinear_iff_of_mem hp₀]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v, fun p hp => ?_⟩
      obtain ⟨r, hr⟩ := hv (a + p) ⟨p, hp, rfl⟩
      simp only [vadd_eq_addV3] at hr
      refine ⟨r, ?_⟩
      apply add_left_cancel (a := a)
      rw [vadd_eq_addV3, hr]
      module
    · rintro ⟨v, hv⟩
      refine ⟨v, fun p hp => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hp
      obtain ⟨r, hr⟩ := hv w hw
      simp only [vadd_eq_addV3] at hr ⊢
      refine ⟨r, ?_⟩
      rw [hr]
      module

/-- `Collinear` 经单射线性映射不变：方向向量与基点同时作用 `g`；
反向由单射性把方向向量拉回（退化情形：所有点重合时取零方向）。 -/
private theorem collinear_linear_image_iff (s : Set V3) (g : V3 →ₗ[ℝ] V3)
    (hg : Function.Injective g) : Collinear ℝ (g '' s) ↔ Collinear ℝ s := by
  rcases Set.eq_empty_or_nonempty s with hs | ⟨p₀, hp₀⟩
  · subst hs
    simp [collinear_empty]
  · have hmem : g p₀ ∈ g '' s := ⟨p₀, hp₀, rfl⟩
    rw [collinear_iff_of_mem hmem, collinear_iff_of_mem hp₀]
    constructor
    · -- 拉回（难方向）：退化情形
      rintro ⟨v, hv⟩
      by_cases hall : ∀ w ∈ s, w = p₀
      · refine ⟨0, fun p hp => ?_⟩
        have hrw := hall p hp
        exact ⟨0, by simp only [vadd_eq_addV3, zero_smul, hrw, zero_add]⟩
      · push_neg at hall
        obtain ⟨p₁, hp₁s, hp₁q⟩ := hall
        obtain ⟨r₁, hr₁⟩ := hv _ ⟨p₁, hp₁s, rfl⟩
        simp only [vadd_eq_addV3] at hr₁
        have hr₁z : r₁ ≠ 0 := by
          intro hz
          refine hp₁q ?_
          exact hg (by rw [hr₁, hz, zero_smul, zero_add])
        have hgsub : g (p₁ - p₀) = r₁ • v := by
          rw [map_sub, hr₁]
          module
        have hvw : v = g (r₁⁻¹ • (p₁ - p₀)) := by
          rw [map_smul, hgsub, smul_smul, inv_mul_cancel₀ hr₁z, one_smul]
        refine ⟨r₁⁻¹ • (p₁ - p₀), fun p hp => ?_⟩
        obtain ⟨r, hr⟩ := hv _ ⟨p, hp, rfl⟩
        simp only [vadd_eq_addV3] at hr
        refine ⟨r, ?_⟩
        apply hg
        simp only [vadd_eq_addV3]
        rw [hr, map_add, map_smul, hvw]
    · -- 推前（易方向）
      rintro ⟨v, hv⟩
      refine ⟨g v, fun p hp => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hp
      obtain ⟨r, hr⟩ := hv w hw
      simp only [vadd_eq_addV3] at hr ⊢
      exact ⟨r, by rw [hr, map_add, map_smul]⟩


/-- HOL polyhedron.hl :185-:189 `FAN3_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
        fan3(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan3(x,V,E)
```

编码说明：HOL `fan3(x,V,E) <=> !e. e IN E ==> CARD e = 2` 未单独移植，
与 `Graph`（Kepler/Text/Fan.lean:39，`FAN` 内同款编码，Fan.lean:56）重合，
故陈述用 `Graph` 表出；`x`、`V` 为哑元，保留占位以贴近原文形状。
`IMAGE (IMAGE (\x. a + x)) E` ↔ 逐边取像
`(fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E`。

证明思路：`Graph` 只看每条边的基数；平移 `fun y => a + y` 是双射
（`add_right_cancel`），逐边用 `Set.Finite.image` 传递有限性、
`Set.card_image_of_injOn` 传递基数 2，两次 `Set.mem_image` 展开成员关系。

候选已有引理：
- `Set.mem_image`、`Set.image_image`（Mathlib/Data/Set/Basic.lean）
- `Set.Finite.image`（Mathlib/Data/Set/Finite/Basic.lean:566）
- `Set.card_image_of_injOn`（Mathlib/Data/Set/Finite/Basic.lean:778）
- `add_right_cancel`（Mathlib/Algebra/Group/Basic.lean） -/
theorem FAN3_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    Graph ((fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E) ↔ Graph E :=
  graph_image_eq (addV3_right_injective a)

/-- HOL polyhedron.hl :191-:202 `FAN3_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan3(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan3(x,V,E))
```

编码说明：`fan3` ↔ `Graph`（见 FAN3_TRANSLATION_EQ）；`linear f` 打包为
`f : V3 →ₗ[ℝ] V3`，单射性单独作前提 `hf`（类型收窄 `real^M->real^N` 到
`V3`，repo 惯例 cf. PlanarityAuto12.lean:580）。HOL 证明中的内点引理
（`{w | {a,w} IN IMAGE (IMAGE f) s} = IMAGE f {w | {a,f w} IN …}`，HOL
:193-:200）是 GEOM_TRANSFORM_TAC 的支撑件，无需单独落地。

证明思路：与 FAN3_TRANSLATION_EQ 相同，双射性由线性 + 单射给出
（`hf` 即单射），逐边 `Set.Finite.image` + `Set.card_image_of_injective`
传递基数。

候选已有引理：
- `Set.mem_image`、`Set.image_image`（Mathlib/Data/Set/Basic.lean）
- `Set.Finite.image`（Mathlib/Data/Set/Finite/Basic.lean:566）
- `Set.card_image_of_injective`（Mathlib/Data/Set/Finite/Basic.lean:788） -/
theorem FAN3_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (hf : Function.Injective f)
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Graph ((fun e : Set V3 => f '' e) '' E) ↔ Graph E :=
  graph_image_eq hf

/-- HOL polyhedron.hl :204-:208 `FAN4_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
        fan4(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan4(x,V,E)
```

编码说明：HOL `fan4(x,V,E) <=> !e. e IN E ==> e SUBSET V` 未单独移植
（`FAN` 将其吸收为 `⋃₀ E ⊆ V`，Fan.lean:56），此处按定义逐条内联；
`e SUBSET IMAGE (\x. a + x) V` ↔ `e ⊆ (fun y : V3 => a + y) '' V`。

证明思路：逐边化归到 `e = (a + ·) '' e₀`（`Set.mem_image`），再用平移的
双射性把 `e₀ ⊆ V` 与 `(a + ·) '' e₀ ⊆ (a + ·) '' V` 互推
（`Set.image_subset_iff` + `Set.subset_image_iff` + `add_right_cancel`）。

候选已有引理：
- `Set.mem_image`（Mathlib/Data/Set/Basic.lean）
- `Set.image_subset_iff`（Mathlib/Data/Set/Image.lean:407）
- `Set.subset_image_iff`（Mathlib/Data/Set/Image.lean:498）
- `add_right_cancel`（Mathlib/Algebra/Group/Basic.lean） -/
theorem FAN4_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    (∀ e ∈ (fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E,
        e ⊆ (fun y : V3 => a + y) '' V) ↔ ∀ e ∈ E, e ⊆ V :=
  fan4c_image_eq (addV3_right_injective a)

/-- HOL polyhedron.hl :210-:214 `FAN4_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan4(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan4(x,V,E))
```

编码说明：`fan4` 内联（见 FAN4_TRANSLATION_EQ）；`linear f` 打包为
`f : V3 →ₗ[ℝ] V3` + `hf : Function.Injective f`。

证明思路：逐边化归 `e = f '' e₀` 后，`e₀ ⊆ V → f '' e₀ ⊆ f '' V` 平凡；
反向用单射性：`f '' e₀ ⊆ f '' V` 经 `Set.image_subset_iff` 得
`e₀ ⊆ f ⁻¹' (f '' V)`，再由 `hf` 收出 `e₀ ⊆ V`。

候选已有引理：
- `Set.image_subset_iff`（Mathlib/Data/Set/Image.lean:407）
- `Set.mem_image`（Mathlib/Data/Set/Basic.lean）
- `Function.Injective`（core/Mathlib） -/
theorem FAN4_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (hf : Function.Injective f)
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    (∀ e ∈ (fun e : Set V3 => f '' e) '' E, e ⊆ f '' V) ↔ ∀ e ∈ E, e ⊆ V :=
  fan4c_image_eq hf

/-- HOL polyhedron.hl :216-:220 `FAN5_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
        fan5(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan5(x,V,E)
```

编码说明：HOL `fan5(x,V,E) <=> !v. v IN V ==> v IN UNIONS E` 未单独移植，
就地内联；`UNIONS E` ↔ `⋃₀ E`（Set.sUnion，Fan.lean:56 同款记号）。
`x` 为哑元，保留占位。

证明思路：`⋃₀ ((a + ·) ''·) '' E` 先经 `Set.sUnion_image`
（Mathlib/Data/Set/Lattice.lean:932）化为 `⋃ e ∈ E, (a + ·) '' e`，
成员关系经 `Set.mem_iUnion`/`Set.mem_image` 平凡双向搬运。

候选已有引理：
- `Set.sUnion_image`（Mathlib/Data/Set/Lattice.lean:932）
- `Set.mem_sUnion`、`Set.mem_iUnion`、`Set.mem_image`
  （Mathlib/Data/Set/Lattice.lean、Mathlib/Data/Set/Basic.lean） -/
theorem FAN5_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    (∀ v ∈ (fun y : V3 => a + y) '' V,
        v ∈ ⋃₀ ((fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E)) ↔
      ∀ v ∈ V, v ∈ ⋃₀ E :=
  fan5c_image_eq (addV3_right_injective a) V E

/-- HOL polyhedron.hl :222-:228 `FAN5_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan5(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan5(x,V,E))
```

编码说明：`fan5` 内联（见 FAN5_TRANSLATION_EQ）；`linear f` 打包为
`f : V3 →ₗ[ℝ] V3` + `hf : Function.Injective f`。HOL 原证明用
GEN_REWRITE_TAC 把前提拉进量词再 GEOM_TRANSFORM_TAC；Lean 侧线性/单射
已置于前提，无需该预处理。

证明思路：`⋃₀ ((f ''·) '' E)` 经 `Set.sUnion_image` 化为
`⋃ e ∈ E, f '' e`，成员关系经 `Set.mem_iUnion`/`Set.mem_image` 双向搬运
（此条对任意 `f` 都成立，无需 `hf`）。

候选已有引理：
- `Set.sUnion_image`（Mathlib/Data/Set/Lattice.lean:932）
- `Set.mem_sUnion`、`Set.mem_iUnion`、`Set.mem_image`
  （Mathlib/Data/Set/Lattice.lean、Mathlib/Data/Set/Basic.lean） -/
theorem FAN5_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (hf : Function.Injective f)
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    (∀ v ∈ f '' V, v ∈ ⋃₀ ((fun e : Set V3 => f '' e) '' E)) ↔
      ∀ v ∈ V, v ∈ ⋃₀ E :=
  fan5c_image_eq hf V E

/-- HOL polyhedron.hl :230-:234 `FAN6_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
        fan6(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan6(x,V,E)
```

编码说明：HOL `fan6` ↔ `fan6`（Kepler/Text/Fan.lean:47，
`∀ e ∈ E, ¬ Collinear ℝ (insert x e)`）；`INSERT` ↔ `insert`。

证明思路：`Collinear` 平移不变：经
`collinear_iff_exists_forall_eq_smul_vadd`
（Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:483，基点平移
`a + p₀`、方向向量不变）把 `Collinear ℝ (insert (a + x) ((a + ·) '' e))`
与 `Collinear ℝ (insert x e)` 互推；边集上的逐边搬运走 `Set.mem_image`，
`insert` 与像交换走 `Set.insert_image`。

候选已有引理：
- `collinear_iff_exists_forall_eq_smul_vadd`
  （Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:483）
- `Set.insert_image`、`Set.mem_image`（Mathlib/Data/Set/Basic.lean）
- `fan6`（Kepler/Text/Fan.lean:47） -/
theorem FAN6_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan6 (a + x) ((fun y : V3 => a + y) '' V)
        ((fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E) ↔
      fan6 x V E := by
  have hinj : Function.Injective (fun y : V3 => a + y) := addV3_right_injective a
  have hcol : ∀ e : Set V3,
      Collinear ℝ (insert (a + x) ((fun y : V3 => a + y) '' e)) ↔ Collinear ℝ (insert x e) := by
    intro e
    have heq : insert (a + x) ((fun y : V3 => a + y) '' e)
        = (fun y : V3 => a + y) '' (insert x e) := by
      rw [Set.image_insert_eq]
    rw [heq]
    exact collinear_translation_iff _ a
  simp only [fan6]
  constructor
  · intro h e he
    exact fun hc => h _ ⟨e, he, rfl⟩ ((hcol e).mpr hc)
  · intro h e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact fun hc => h e₀ he₀ ((hcol e₀).mp hc)

/-- HOL polyhedron.hl :236-:240 `FAN6_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan6(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan6(x,V,E))
```

编码说明：`fan6` ↔ `fan6`（Kepler/Text/Fan.lean:47）；`linear f` 打包为
`f : V3 →ₗ[ℝ] V3` + `hf : Function.Injective f`。

证明思路：`Collinear` 经单射线性映射不变：仍用
`collinear_iff_exists_forall_eq_smul_vadd`，把 `p = r • v +ᵥ p₀` 两边作用
`f`（`map_smul`、`map_add`），得 `f p = r • f v +ᵥ f p₀`；反向由 `hf`
消去 `f`。边级搬运同 FAN6_TRANSLATION_EQ（`Set.mem_image`、
`Set.insert_image`）。

候选已有引理：
- `collinear_iff_exists_forall_eq_smul_vadd`
  （Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:483）
- `map_smul`、`map_add`、`map_sum`（Mathlib/Algebra/Module/LinearMap/*）
- `Set.insert_image`、`Set.mem_image`（Mathlib/Data/Set/Basic.lean） -/
theorem FAN6_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (hf : Function.Injective f)
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan6 (f x) (f '' V) ((fun e : Set V3 => f '' e) '' E) ↔ fan6 x V E := by
  have hcol : ∀ e : Set V3,
      Collinear ℝ (insert (f x) (f '' e)) ↔ Collinear ℝ (insert x e) := by
    intro e
    have heq : insert (f x) (f '' e) = (f : V3 → V3) '' (insert x e) := by
      rw [Set.image_insert_eq]
    rw [heq]
    exact collinear_linear_image_iff _ f hf
  simp only [fan6]
  constructor
  · intro h e he
    exact fun hc => h _ ⟨e, he, rfl⟩ ((hcol e).mpr hc)
  · intro h e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact fun hc => h e₀ he₀ ((hcol e₀).mp hc)

/-- HOL polyhedron.hl :242-:249 `FAN7_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
        fan7(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) <=>
        fan7(x,V,E)
```

编码说明：HOL `fan7` ↔ `fan7`（Kepler/Text/Fan.lean:51，量词域
`E ∪ {s | ∃ v ∈ V, s = {v}}`）；平移下单点边像 `(a + ·) '' {v} = {a + v}`
（`Set.image_singleton`）。HOL 原证明在 REWRITE_TAC[fan7] 后先拆
UNION 成员（SET_RULE :246-:248）再 GEOM_TRANSLATE_TAC。

证明思路：展开 `fan7` 后，两个量词域按成员分情形
（`Set.mem_union` + `Set.mem_setOf_eq` + `Set.image_singleton`）化归到
`affGe` 的平移等变：`affsign` 的显式有限和表征
（Kepler/Geom/Aff.lean:32）在 `y = a + ∑ f w • w` 与
`y = ∑ f w • (a + w)` 间换算（`Finset.sum_smul` + `Finset.sum_add_distrib`
+ 系数和为 1），交等式两边同减 `a`。

候选已有引理：
- `Affsign`（Kepler/Geom/Aff.lean:32）、`affGe`（Kepler/Geom/Aff.lean:42）
- `fan7`（Kepler/Text/Fan.lean:51）
- `Set.mem_union`、`Set.image_singleton`、`Set.mem_image`
  （Mathlib/Data/Set/Basic.lean）
- `Finset.sum_smul`、`Finset.sum_add_distrib`
  （Mathlib/Algebra/BigOperators/*） -/
theorem FAN7_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan7 (a + x) ((fun y : V3 => a + y) '' V)
        ((fun e : Set V3 => (fun y : V3 => a + y) '' e) '' E) ↔
      fan7 x V E := by
  sorry

/-- HOL polyhedron.hl :251-:261 `FAN7_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
    linear f /\ (!x y. f x = f y ==> x = y)
    ==> (fan7(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> fan7(x,V,E))
```

编码说明：`fan7` ↔ `fan7`（Kepler/Text/Fan.lean:51）；`linear f` 打包为
`f : V3 →ₗ[ℝ] V3` + `hf : Function.Injective f`。单点边像
`f '' {v} = {f v}`（`Set.image_singleton`）。

证明思路：展开 `fan7` 后量词域按成员分情形（HOL 原证明 :253-:260 用
LEFT_OR_DISTRIB/RIGHT_OR_DISTRIB + TAUR 拆分，Lean 侧 `Set.mem_union` +
`Set.mem_setOf_eq` 即可），核仍是 `affGe` 的线性等变：`Affsign`
（Kepler/Geom/Aff.lean:32）的有限和经 `map_sum`/`map_smul` 作用 `f`，
反向由 `hf` 注入消去（`Finset.sum_apply` 路线），交等式两边同作用 `f`。

候选已有引理：
- `Affsign`（Kepler/Geom/Aff.lean:32）、`affGe`（Kepler/Geom/Aff.lean:42）
- `fan7`（Kepler/Text/Fan.lean:51）
- `Set.mem_union`、`Set.image_singleton`、`Set.mem_image`
  （Mathlib/Data/Set/Basic.lean）
- `map_sum`、`map_smul`、`map_add`（Mathlib/Algebra/Module/LinearMap/*）
- `Function.Injective`（Mathlib/Logic/Function/Basic.lean） -/
theorem FAN7_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (hf : Function.Injective f)
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    fan7 (f x) (f '' V) ((fun e : Set V3 => f '' e) '' E) ↔ fan7 x V E := by
  sorry

end Kepler.Text
