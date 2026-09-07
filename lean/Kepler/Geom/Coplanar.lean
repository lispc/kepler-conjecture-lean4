/-
Kepler.Geom.Coplanar — HOL Light `coplanar` 概念的移植。

源：HOL Light `trig2.hl:1548`
  `coplanar s <=> ?u v w. s SUBSET affine hull {u,v,w}`
即：集合共面 ⟺ 含于某三点的仿射包。Mathlib 对应写法：
`affineSpan ℝ ({u, v, w} : Set V3)`；三维类型为 `Kepler.Geom.V3`
（= HOL `real^3`，见 `Kepler/Geom/Azim.lean`）。

约定：与 `Collinear3` 一致取三点字面集 `{u, v, w}`；退化情形
（三点共线/重合）自动退化为更低维仿射包，与 HOL 语义相同。
-/

import Kepler.Geom.Azim

namespace Kepler.Geom

private theorem mem_affineSpan_coe {p : V3} {s : Set V3} (hp : p ∈ s) :
    p ∈ (affineSpan ℝ s : Set V3) :=
  SetLike.mem_coe.mpr (mem_affineSpan ℝ hp)

/-- HOL `coplanar`（trig2.hl:1548）：`s` 含于三点的仿射包。 -/
def Coplanar (s : Set V3) : Prop :=
  ∃ u v w : V3, s ⊆ affineSpan ℝ {u, v, w}

/-- 平面的（共面）子集仍共面。 -/
theorem Coplanar.subset {s t : Set V3} (hst : s ⊆ t) (ht : Coplanar t) : Coplanar s := by
  obtain ⟨u, v, w, htw⟩ := ht
  exact ⟨u, v, w, hst.trans htw⟩

/-- 单点共面（HOL `COPLANAR_SING`）。 -/
theorem coplanar_singleton (x : V3) : Coplanar ({x} : Set V3) := by
  refine ⟨x, x, x, fun p hp => ?_⟩
  rw [Set.mem_singleton_iff] at hp
  subst hp
  exact mem_affineSpan_coe (by simp)

/-- 两点共面（HOL `COPLANAR_PAIR`）。 -/
theorem coplanar_pair (x y : V3) : Coplanar ({x, y} : Set V3) := by
  refine ⟨x, y, y, fun p hp => ?_⟩
  rw [show ({x, y, y} : Set V3) = {x, y} from by ext q; simp]
  exact mem_affineSpan_coe hp

/-- 三点共面：`{x, y, z}` 含于自身的仿射包。 -/
theorem coplanar_triple (x y z : V3) : Coplanar ({x, y, z} : Set V3) :=
  ⟨x, y, z, fun _ hp => mem_affineSpan_coe hp⟩

/-- 空集共面。 -/
theorem coplanar_empty : Coplanar (∅ : Set V3) :=
  ⟨0, 0, 0, Set.empty_subset _⟩

end Kepler.Geom
