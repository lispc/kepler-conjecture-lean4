/-
Kepler.Geom.Aff — 仿射半空间词汇（flyspeck 几何章，Lean 移植）

源：HOL Light `Multivariate/flyspeck.ml:685–699`（持久副本
`/home/scroll/hol-light-ref/Multivariate-flyspeck.ml`）：

    lin_combo V f = vsum V (λv. f v • v)
    affsign sgn s t v ⟺ ∃f. v = lin_combo (s ∪ t) f
                              ∧ (∀w. w ∈ t → sgn (f w))
                              ∧ ∑(s ∪ t) f = 1
    aff_gt/ge/lt/le = affsign sgn_gt/ge/lt/le

语义注记：HOL 的 `sum`/`vsum` 在无限集上给出未指定废值；所有 fan 章消费
方都是有限点集。Lean 侧把有限性做成显式见证（`∃ h : (s ∪ t).Finite`），
无限情形 `Affsign` 直接为 False（HOL 为废值，理论不触及）。
-/

import Kepler.Geom.Azim
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Classical

namespace Kepler.Geom

variable {s t : Set V3}

/-- HOL `lin_combo V f`（flyspeck.ml:685）。无限集上 HOL 为废值；此处取 0。 -/
noncomputable def linCombo (S : Set V3) (f : V3 → ℝ) : V3 :=
  if h : S.Finite then ∑ w ∈ h.toFinset, f w • w else 0

/-- HOL `affsign sgn s t v`（flyspeck.ml:688，有限性显式化版本）。 -/
def Affsign (sgn : ℝ → Prop) (s t : Set V3) (v : V3) : Prop :=
  ∃ f : V3 → ℝ, ∃ h : (s ∪ t).Finite,
    v = ∑ w ∈ h.toFinset, f w • w ∧
      (∀ w ∈ t, sgn (f w)) ∧
      ∑ w ∈ h.toFinset, f w = 1

/-- HOL `aff_gt = affsign sgn_gt`（严格正组合锥）。 -/
def affGt (s t : Set V3) : Set V3 := {v | Affsign (fun x => 0 < x) s t v}

/-- HOL `aff_ge = affsign sgn_ge`。 -/
def affGe (s t : Set V3) : Set V3 := {v | Affsign (fun x => 0 ≤ x) s t v}

/-- HOL `aff_lt = affsign sgn_lt`。 -/
def affLt (s t : Set V3) : Set V3 := {v | Affsign (fun x => x < 0) s t v}

/-- HOL `aff_le = affsign sgn_le`。 -/
def affLe (s t : Set V3) : Set V3 := {v | Affsign (fun x => x ≤ 0) s t v}

/-- 三点并集的 toFinset 求和分解。 -/
private theorem sum_union_pair_singleton {f : V3 → ℝ} {v0 v1 x : V3}
    (hfin : ({v0, v1} ∪ {x} : Set V3).Finite) (hv0v1 : v0 ≠ v1) (hx0 : x ≠ v0)
    (hx1 : x ≠ v1) :
    ∑ w ∈ hfin.toFinset, f w = f v0 + f v1 + f x := by
  have h3 : hfin.toFinset = ({v0, v1, x} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hv0v1, Ne.symm hx0]),
    Finset.sum_insert (by simp [Ne.symm hx1]), Finset.sum_singleton]
  ring

/-- 三点并集的 toFinset 向量和分解。 -/
private theorem sum_union_pair_singleton_v {f : V3 → ℝ} {v0 v1 x : V3}
    (hfin : ({v0, v1} ∪ {x} : Set V3).Finite) (hv0v1 : v0 ≠ v1) (hx0 : x ≠ v0)
    (hx1 : x ≠ v1) :
    ∑ w ∈ hfin.toFinset, f w • w = f v0 • v0 + f v1 • v1 + f x • x := by
  have h3 : hfin.toFinset = ({v0, v1, x} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hv0v1, Ne.symm hx0]),
    Finset.sum_insert (by simp [Ne.symm hx1]), Finset.sum_singleton]
  abel

/-- HOL AFF_GT_2_1 的射线刻画：三点互异时
`y ∈ aff_gt {v0,v1} {x} ↔ ∃ c>0, ∃ h, y - v0 = c•(x - v0) + h•(v1 - v0)`。 -/
theorem affGt_pair_iff {v0 v1 x y : V3} (hv0v1 : v0 ≠ v1) (hx0 : x ≠ v0)
    (hx1 : x ≠ v1) :
    y ∈ affGt {v0, v1} {x} ↔
      ∃ c : ℝ, 0 < c ∧ ∃ h : ℝ, y - v0 = c • (x - v0) + h • (v1 - v0) := by
  have hfin : ({v0, v1} ∪ {x} : Set V3).Finite :=
    ((Set.finite_singleton v1).insert v0).union (Set.finite_singleton x)
  constructor
  · rintro ⟨f, hfin', hsum, hpos, hone⟩
    have hxm : x ∈ ({v0, v1} ∪ {x} : Set V3) :=
      Set.mem_union_right _ (Set.mem_singleton x)
    rw [sum_union_pair_singleton_v hfin' hv0v1 hx0 hx1] at hsum
    rw [sum_union_pair_singleton hfin' hv0v1 hx0 hx1] at hone
    have hf0 : f v0 = 1 - f v1 - f x := by linarith
    refine ⟨f x, hpos x (Set.mem_singleton x), f v1, ?_⟩
    rw [hsum, hf0]
    module
  · rintro ⟨c, hc, h, hy⟩
    refine ⟨fun z => if z = x then c else if z = v1 then h else 1 - c - h, hfin, ?_, ?_, ?_⟩
    · rw [sum_union_pair_singleton_v hfin hv0v1 hx0 hx1]
      simp only [if_neg (Ne.symm hx0), if_neg hv0v1, if_neg (Ne.symm hx1),
        if_pos rfl, if_true]
      rw [show y = (y - v0) + v0 from (sub_add_cancel y v0).symm, hy]
      module
    · intro w hw
      simp only [Set.mem_singleton_iff] at hw
      rcases hw with rfl
      simpa using hc
    · rw [sum_union_pair_singleton hfin hv0v1 hx0 hx1]
      simp only [if_neg (Ne.symm hx0), if_neg hv0v1, if_neg (Ne.symm hx1),
        if_pos rfl, if_true]
      ring


/-- 单点 ∪ 单点 的标量/向量和分解。 -/
theorem sum_insert_single_s {f : V3 → ℝ} {x v : V3}
    (hfin : ({x} ∪ {v} : Set V3).Finite) (hxv : x ≠ v) :
    ∑ w ∈ hfin.toFinset, f w = f x + f v := by
  have h2 : hfin.toFinset = ({x, v} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h2, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]

theorem sum_insert_single_v {f : V3 → ℝ} {x v : V3}
    (hfin : ({x} ∪ {v} : Set V3).Finite) (hxv : x ≠ v) :
    ∑ w ∈ hfin.toFinset, f w • w = f x • x + f v • v := by
  have h2 : hfin.toFinset = ({x, v} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h2, Finset.sum_insert (by simp [hxv]), Finset.sum_singleton]

/-- 单点 ∪ 两点集 的标量/向量和分解。 -/
theorem sum_insert_pair_s {f : V3 → ℝ} {x v u : V3}
    (hfin : ({x} ∪ {v, u} : Set V3).Finite) (hxv : x ≠ v) (hxu : x ≠ u)
    (hvu : v ≠ u) :
    ∑ w ∈ hfin.toFinset, f w = f x + f v + f u := by
  have h3 : hfin.toFinset = ({x, v, u} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hxv, hxu]), Finset.sum_insert (by simp [hvu])]
  simp only [Finset.sum_singleton]
  ring

theorem sum_insert_pair_v {f : V3 → ℝ} {x v u : V3}
    (hfin : ({x} ∪ {v, u} : Set V3).Finite) (hxv : x ≠ v) (hxu : x ≠ u)
    (hvu : v ≠ u) :
    ∑ w ∈ hfin.toFinset, f w • w = f x • x + f v • v + f u • u := by
  have h3 : hfin.toFinset = ({x, v, u} : Finset V3) := by
    apply Finset.ext
    intro w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    try tauto
  rw [h3, Finset.sum_insert (by simp [hxv, hxu]), Finset.sum_insert (by simp [hvu])]
  simp only [Finset.sum_singleton]
  abel

/-- 三点组合的 affsign 见证（构造方向）。 -/
theorem Affsign.of_triple {sgn : ℝ → Prop} {x v u y : V3} (t1 t2 : ℝ)
    (h1 : sgn t1) (h2 : sgn t2)
    (hy : y = (1 - t1 - t2) • x + t1 • v + t2 • u)
    (hxv : x ≠ v) (hxu : x ≠ u) (hvu : v ≠ u) :
    Affsign sgn {x} {v, u} y := by
  have hfin2 : ({x} ∪ {v, u} : Set V3).Finite :=
    (Set.finite_singleton x).union ((Set.finite_singleton u).insert v)
  refine ⟨fun z => if z = v then t1 else if z = u then t2 else 1 - t1 - t2,
    hfin2, ?_, ?_, ?_⟩
  · rw [sum_insert_pair_v
        (f := fun z => if z = v then t1 else if z = u then t2 else 1 - t1 - t2)
        hfin2 hxv hxu hvu]
    rw [if_pos (rfl : v = v), if_neg (Ne.symm hvu), if_pos (rfl : u = u),
      if_neg hxv, if_neg hxu, hy]
  · intro z hz
    rcases hz with rfl | rfl
    · simp only [if_pos rfl]
      exact h1
    · simp only [if_neg (Ne.symm hvu), if_pos rfl]
      exact h2
  · rw [sum_insert_pair_s
        (f := fun z => if z = v then t1 else if z = u then t2 else 1 - t1 - t2)
        hfin2 hxv hxu hvu]
    rw [if_pos (rfl : v = v), if_neg (Ne.symm hvu), if_pos (rfl : u = u),
      if_neg hxv, if_neg hxu]
    ring

/-- aff_ge {x} {v} 的射线提取。 -/
theorem affGe_ray {x v y : V3} (hxv : x ≠ v) (hmem : y ∈ affGe {x} {v}) :
    ∃ t : ℝ, y - x = t • (v - x) := by
  obtain ⟨f, hfin, hsum, -, hone⟩ := hmem
  rw [sum_insert_single_s hfin hxv] at hone
  rw [sum_insert_single_v hfin hxv] at hsum
  refine ⟨f v, ?_⟩
  have hfx : f x = 1 - f v := by linarith
  rw [hsum, hfx]
  module

end Kepler.Geom

/- 计划中的首批引理（下一块）：（flyspeck.ml:732，
 系数吸收手术）、 展开律。 -/
