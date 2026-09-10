/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18n.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18n of block 18, planarity.hl:12819-13120): the
cross/dot sign-invariance layer
- `condition_cross_dot_4point` (12819)
- `aff_gt_2_1_cross_dotl_4point` (12857)
- `aff_gt_2_1r_rcross_dotl_4point` (12885)
- `aff_gt_1_2_cross_dotr_4point` (12913)
- `aff_gt_1_2_cross_dotr_4point_neg` (12952)
- `aff_gt_1_2_cross_dotr_4point_zero` (12991)
- `exists_esilon_real` (13025)
- `invariant_cross_dotr_esilon_3piont` (13059)
- `invariant_rcross_dot_esilon_3piont` (13081)
- `invariant_crossr_dot_esilon_3piont` (13101)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `cross` has no public V3-level definition in the repo (`cross3` in
  Kepler/Text/TopologyFan.lean:2257 is private). The established idiom is
  the Pi-side `crossProduct` (Mathlib `LinearAlgebra.CrossProduct`); when a
  V3 result is required it is lifted with `WithLp.toLp 2` (cf.
  Kepler/Text/PlanarityAngle.lean:115, Kepler/Text/TopologyFan.lean:2257).
  Hence HOL `a cross b` is encoded as
  `crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)` (Pi-side, for `dot`) or
  `WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))` (V3-side).
- HOL `dot` ↔ `⬝ᵥ` (`dotProduct`), available on both `V3` and
  `Fin 3 → ℝ` (cf. Kepler/Geom/Azim.lean:40).
- HOL `%` (scalar multiplication) ↔ `•`.
- HOL `~collinear {a,b,c}` ↔ `¬ Collinear3 a b c`
  (Kepler/Geom/Azim.lean:43).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39).
- HOL `let a = e in body` is kept as a Lean `let` binding in the statement,
  so the theorem type mirrors the HOL quantifier/let structure literally.
- HOL `exists_esilon_real` (13025) is a pure real-analysis statement. No
  exact Mathlib lemma exists (searched for a direct `∃ t, 0 < t ∧ t < 1 ∧
  ∀ h, ...`); closest are the filter/open-set formulations
  `eventually_nhdsWithin_iff` and `isOpen_lt`-style arguments, which do not
  yield an explicit `t`. Therefore it is NOT skipped and is ported as-is.
- HOL `th3`, `AFF_GT_2_1`, `AFF_GT_1_2`, `CROSS_LAGRANGE` are not ported
  under those names. Closest:
  `collinear3_iff_mem_affineSpan` (Kepler/Text/TopologyFan.lean:785),
  `affGt_pair_iff` (Kepler/Geom/Aff.lean:82),
  `aff_gt_1_2` (Kepler/Text/Planarity.lean:165),
  `affGt_of_triple` (Kepler/Text/TopologyFan.lean:812),
  and the private `cross3_cross3` (Kepler/Text/TopologyFan.lean:2340).
-/

import Kepler.Text.PlanarityAuto9

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 四点 cross/dot 符号（planarity.hl:12819-13023） -/

/-- 向量三重积恒等式（`cross_cross_eq_smul_sub_smul'` 的 `toLp` 提升）：
`(a ⨯ b) ⨯ (c ⨯ d) = ((a ⨯ b)·d)•c + (-((a ⨯ b)·c))•d`。 -/
private theorem cross_cross_toLp (a b c d : V3) :
    WithLp.toLp 2 (crossProduct (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))
                                 (crossProduct (c : Fin 3 → ℝ) (d : Fin 3 → ℝ)))
      = ((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (d : Fin 3 → ℝ)) • c +
        (-((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ))) • d := by
  have hPi :
      crossProduct (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))
          (crossProduct (c : Fin 3 → ℝ) (d : Fin 3 → ℝ))
        = ((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (d : Fin 3 → ℝ)) •
            (c : Fin 3 → ℝ) +
          (-((crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)) ⬝ᵥ (c : Fin 3 → ℝ))) •
            (d : Fin 3 → ℝ) := by
    rw [cross_cross_eq_smul_sub_smul']
    rw [dotProduct_comm (c : Fin 3 → ℝ)
      (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))]
    rw [sub_eq_add_neg, ← neg_smul]
  rw [hPi]
  simp only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp]

/-- HOL planarity.hl :12819-12851 `condition_cross_dot_4point`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
              let va = a1 cross a2 in
              let vb = a3 cross a4 in
              let v3 = va cross vb + x in 
 ~collinear {x,v,u}
/\ &0<(a1 cross a2) dot a4 /\  &0 < --((a1 cross a2) dot a3)
==> v3 IN aff_gt {x} {v,u}
```

证明思路：展开 `let`，记 `va = a1 ⨯ a2`、`vb = a3 ⨯ a4`。用 `aff_gt_1_2`
把目标 `v3 ∈ aff_gt {x} {v,u}` 化为显式组合 `t1•x + t2•v + t3•u`：取
`t1 = 1 - va·a4 + va·a3`、`t2 = va·a4`、`t3 = -(va·a3)`，由两条正性假设得
`t2,t3 > 0` 且 `t1+t2+t3 = 1`。再展开 `v3`、`vb` 用 `cross3_cross3`
（HOL `CROSS_LAGRANGE`）与向量环等式收尾。

编码缺口：`va`、`vb` 用 Pi 侧 `crossProduct` 表示，`v3` 用
`WithLp.toLp 2 (crossProduct va vb) + x`（HOL `cross` 的最近编码）。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `affGt_of_triple`（Kepler/Text/TopologyFan.lean:812）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `cross_dot_cross`（Mathlib/LinearAlgebra/CrossProduct.lean:111） -/
theorem condition_cross_dot_4point (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    let va : Fin 3 → ℝ := crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)
    let vb : Fin 3 → ℝ := crossProduct ((a3 : V3) : Fin 3 → ℝ) ((a4 : V3) : Fin 3 → ℝ)
    let v3 : V3 := WithLp.toLp 2 (crossProduct va vb) + x
    ¬ Collinear3 x v u →
    (0 < va ⬝ᵥ ((a4 : V3) : Fin 3 → ℝ)) →
    (0 < -(va ⬝ᵥ ((a3 : V3) : Fin 3 → ℝ))) →
    v3 ∈ affGt ({x} : Set V3) ({v, u} : Set V3) := by
  dsimp only
  intro hnc hpos4 hpos3
  have hxv : x ≠ v := fun he =>
    hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  have hxu : x ≠ u := fun he =>
    hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := u) he.symm)
  have hvu : v ≠ u := fun he =>
    hnc (collinear3_pair_right (v0 := x) (v1 := v) (x := u) he.symm)
  refine Affsign.of_triple (sgn := fun r => 0 < r)
    ((crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((u - x : V3) : Fin 3 → ℝ))
    (-((crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((v - x : V3) : Fin 3 → ℝ)))
    hpos4 hpos3 ?_ hxv hxu hvu
  rw [cross_cross_toLp]
  module

/-- HOL planarity.hl :12857-12879 `aff_gt_2_1_cross_dotl_4point`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 ~collinear {x,z,v}
/\ u IN aff_gt {x,z} {v}
/\ &0<(a1 cross a2) dot a3 
==> &0<(a1 cross a2) dot a4 
```

证明思路：由 `u ∈ aff_gt {x,z} {v}` 用 `affGt_pair_iff`（HOL `AFF_GT_2_1`）
得 `u - x = c•(v - x) + h•(z - x)`（`c > 0`）。展开 `a4 = u - x`，用点积双线性
得 `(a1 ⨯ a2)·a4 = c·((a1 ⨯ a2)·a3) + h·((a1 ⨯ a2)·a2)`，其中
`(a1 ⨯ a2)·a2 = 0`（`cross` 与因子正交），故等于 `c·((a1 ⨯ a2)·a3) > 0`。
`~collinear {x,z,v}` 提供 `x ≠ z` 等互异性。

候选已有引理：
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `cross3_dot_right`（Kepler/Text/TopologyFan.lean:2336，private）
- `dotProduct` 双线性（Mathlib `Matrix.dotProduct`） -/
theorem aff_gt_2_1_cross_dotl_4point (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    ¬ Collinear3 x z v →
    u ∈ affGt ({x, z} : Set V3) ({v} : Set V3) →
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a4 : V3) : Fin 3 → ℝ)) := by
  dsimp only
  intro hnc hgt hpos
  have hxz : x ≠ z := fun he =>
    hnc (collinear3_of_eq (v := x) (w := z) (w1 := v) he.symm)
  have hvx : v ≠ x := fun he =>
    hnc (collinear3_pair_left (v0 := x) (v1 := z) (x := v) he)
  have hvz : v ≠ z := fun he =>
    hnc (collinear3_pair_right (v0 := x) (v1 := z) (x := v) he)
  obtain ⟨c, hc, h, hu⟩ :=
    (affGt_pair_iff (v0 := x) (v1 := z) (x := v) (y := u) hxz hvx hvz).mp hgt
  rw [hu]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul]
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
  have hA2 : crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((z - x : V3) : Fin 3 → ℝ) = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self _ _
  rw [hA2, smul_zero, add_zero, smul_eq_mul]
  exact mul_pos hc hpos

/-- HOL planarity.hl :12885-12907 `aff_gt_2_1r_rcross_dotl_4point`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 ~collinear {x,v,y}
/\ u IN aff_gt {x,v} {y}
/\ &0<(a1 cross a2) dot a3 
==> &0<(a4 cross a2) dot a3 
```

证明思路：由 `u ∈ aff_gt {x,v} {y}` 用 `affGt_pair_iff`（HOL `AFF_GT_2_1`）
得 `u - x = c•(y - x) + h•(v - x)`（`c > 0`），即 `a4 = c•a1 + h•a3`。代入
`(a4 ⨯ a2)·a3 = c·((a1 ⨯ a2)·a3) + h·((a3 ⨯ a2)·a3)`，末项因
`(a3 ⨯ a2) ⊥ a3` 为零，故等于 `c·((a1 ⨯ a2)·a3) > 0`。用 `cross` 的双线性
（`CROSS_LMUL`/`CROSS_LADD`）展开。

候选已有引理：
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `crossProduct` 双线性（Mathlib/LinearAlgebra/CrossProduct.lean） -/
theorem aff_gt_2_1r_rcross_dotl_4point (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    ¬ Collinear3 x v y →
    u ∈ affGt ({x, v} : Set V3) ({y} : Set V3) →
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    (0 < (crossProduct ((a4 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) := by
  sorry

/-- HOL planarity.hl :12913-12946 `aff_gt_1_2_cross_dotr_4point`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 ~collinear {x,v,u}
/\ y IN aff_gt {x} {v,u}
/\ &0<(a1 cross a2) dot a3
 ==> &0< --((a1 cross a2) dot a4)
```

证明思路：由 `y ∈ aff_gt {x} {v,u}` 用 `aff_gt_1_2`（HOL `AFF_GT_1_2`）得
`a1 = t2•a3 + t3•a4`（`t2,t3 > 0`）。代入并用 `cross`/`dot` 双线性、`cross`
自反为零化简，得 `(a1 ⨯ a2)·a3 = t3·((a4 ⨯ a2)·a3)`（`cross` 换序变号后
`(a3 ⨯ a2)·a3 = 0`）。由假设 `0 < (a1 ⨯ a2)·a3` 与 `t3 > 0` 反推
`0 < (a4 ⨯ a2)·a3`，再用 `cross` 反对称得 `0 < -((a1 ⨯ a2)·a4)`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `cross_anticomm`（Mathlib/LinearAlgebra/CrossProduct.lean:63） -/
theorem aff_gt_1_2_cross_dotr_4point (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    ¬ Collinear3 x v u →
    y ∈ affGt ({x} : Set V3) ({v, u} : Set V3) →
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    (0 < -((crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a4 : V3) : Fin 3 → ℝ))) := by
  sorry

/-- HOL planarity.hl :12952-12987 `aff_gt_1_2_cross_dotr_4point_neg`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 ~collinear {x,v,u}
/\ y IN aff_gt {x} {v,u}
/\ &0< --((a1 cross a2) dot a3)
 ==> &0< ((a1 cross a2) dot a4)
```

证明思路：与 `aff_gt_1_2_cross_dotr_4point` 同构，仅假设符号取反。由
`y ∈ aff_gt {x} {v,u}` 得 `a1 = t2•a3 + t3•a4`（`t2,t3 > 0`），代入化简得
`-((a1 ⨯ a2)·a3) = t3·(-((a4 ⨯ a2)·a3))`，由正性假设与 `t3 > 0` 得
`0 < (a4 ⨯ a2)·a3`，再反对称化为 `0 < (a1 ⨯ a2)·a4`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `cross_anticomm`（Mathlib/LinearAlgebra/CrossProduct.lean:63） -/
theorem aff_gt_1_2_cross_dotr_4point_neg (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    ¬ Collinear3 x v u →
    y ∈ affGt ({x} : Set V3) ({v, u} : Set V3) →
    (0 < -((crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ))) →
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a4 : V3) : Fin 3 → ℝ)) := by
  sorry

/-- HOL planarity.hl :12991-13022 `aff_gt_1_2_cross_dotr_4point_zero`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 ~collinear {x,v,u}
/\ y IN aff_gt {x} {v,u}
/\ (a1 cross a2) dot a3= &0
 ==> ((a1 cross a2) dot a4)= &0
```

证明思路：与 `aff_gt_1_2_cross_dotr_4point` 同构。由 `y ∈ aff_gt {x} {v,u}`
得 `a1 = t2•a3 + t3•a4`（`t2,t3 > 0`），代入化简得
`(a1 ⨯ a2)·a3 = t3·((a4 ⨯ a2)·a3)`。由假设该值为零且 `t3 > 0`，得
`(a4 ⨯ a2)·a3 = 0`，反对称化为 `(a1 ⨯ a2)·a4 = 0`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `mul_eq_zero`（Mathlib/Algebra/Order/Ring/Lemmas.lean） -/
theorem aff_gt_1_2_cross_dotr_4point_zero (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    ¬ Collinear3 x v u →
    y ∈ affGt ({x} : Set V3) ({v, u} : Set V3) →
    ((crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) = 0 →
    ((crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a4 : V3) : Fin 3 → ℝ)) = 0 := by
  sorry

/-! ## 实分析 epsilon 引理（planarity.hl:13025-13055） -/

/-- HOL planarity.hl :13025-13055 `exists_esilon_real`

HOL 原文：
```
!a:real b:real.
&0<a ==> ?t. &0< t /\ t< &1 /\ 
(!h. &0< h /\ h< t==> &0< a- h * b)
```

证明思路：对 `b` 分情形。若 `b ≤ 0`，取 `t = 1/2`，此时 `h·b ≤ 0`，故
`a - h·b ≥ a > 0`。若 `0 < b`，取 `t = min(a/b, 1)/2 > 0`（严格小于 `1` 且
`t < a/b`）；对 `0 < h < t` 有 `h·b < a`，即 `a - h·b > 0`。

Mathlib 缺口：无同形引理；最接近的是
`eventually_nhdsWithin_iff`/`isOpen_lt` 的开集论证（只给出“最终”形式，
不给出显式 `t`），故按 HOL 原样落地、不跳过。

候选已有引理：
- `lt_div_iff₀`（Mathlib/Algebra/Order/Field/Basic.lean）
- `min_lt_iff`（Mathlib/Order/MinMax.lean）
- `mul_lt_of_lt_div`（Mathlib/Algebra/Order/Field/Basic.lean） -/
theorem exists_esilon_real (a b : ℝ) (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ h : ℝ, 0 < h → h < t → 0 < a - h * b := by
  sorry

/-! ## cross/dot 符号的 epsilon 不变性（planarity.hl:13059-13120） -/

/-- HOL planarity.hl :13059-13077 `invariant_cross_dotr_esilon_3piont`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 &0<(a1 cross a2) dot a3
 ==>
?t. &0< t /\ t< &1 /\ 
(!h. &0< h /\ h< t==>
 &0< ((a1 cross a2) dot ((&1 - h) % v + h % u-x)))
```

证明思路：把 `(1-h)%v + h%u - x` 重写为 `(1-h)•a3 + h•a4`，用点积双线性得
`(a1 ⨯ a2)·((1-h)•a3 + h•a4) = ((a1 ⨯ a2)·a3) - h·(((a1 ⨯ a2)·a3) -
((a1 ⨯ a2)·a4))`。对 `a = (a1 ⨯ a2)·a3 > 0` 与 `b = ((a1 ⨯ a2)·a3) -
((a1 ⨯ a2)·a4)` 应用 `exists_esilon_real` 即得。

候选已有引理：
- `exists_esilon_real`（本文件，HOL :13025）
- `dotProduct` 双线性（Mathlib `Matrix.dotProduct`）
- `smul_dotProduct` / `dotProduct_add`（Mathlib/Data/Matrix/...） -/
theorem invariant_cross_dotr_esilon_3piont (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ h : ℝ, 0 < h → h < t →
        0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
          ((((1 - h) • v + h • u - x : V3)) : Fin 3 → ℝ) := by
  sorry

/-- HOL planarity.hl :13081-13098 `invariant_rcross_dot_esilon_3piont`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 &0<(a1 cross a2) dot a3
 ==>
?t. &0< t /\ t< &1 /\ 
(!h. &0< h /\ h< t==>
 &0< (((&1 - h) % y + h % u-x) cross a2) dot a3)
```

证明思路：把 `(1-h)%y + h%u - x` 重写为 `(1-h)•a1 + h•a4`，用 `cross` 双线性
得 `(((1-h)•a1 + h•a4) ⨯ a2)·a3 = ((a1 ⨯ a2)·a3) - h·(((a1 ⨯ a2)·a3) -
((a4 ⨯ a2)·a3))`。对 `a = (a1 ⨯ a2)·a3 > 0` 与
`b = ((a1 ⨯ a2)·a3) - ((a4 ⨯ a2)·a3)` 应用 `exists_esilon_real` 即得。

注意：HOL 证明体里误写成 `(&1 - h) % v`，但 HOL 陈述用的是 `y`；此处忠实
于陈述，采用 `y`。

候选已有引理：
- `exists_esilon_real`（本文件，HOL :13025）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `crossProduct` 双线性（Mathlib/LinearAlgebra/CrossProduct.lean） -/
theorem invariant_rcross_dot_esilon_3piont (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ h : ℝ, 0 < h → h < t →
        0 < (crossProduct
              ((((1 - h) • y + h • u - x : V3)) : Fin 3 → ℝ)
              ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ ((a3 : V3) : Fin 3 → ℝ) := by
  sorry

/-- HOL planarity.hl :13101-13118 `invariant_crossr_dot_esilon_3piont`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
 &0<(a1 cross a2) dot a3
 ==>
?t. &0< t /\ t< &1 /\ 
(!h. &0< h /\ h< t==>
 &0< (a1 cross ((&1 - h) % z + h % u-x)) dot a3)
```

证明思路：把 `(1-h)%z + h%u - x` 重写为 `(1-h)•a2 + h•a4`，用 `cross` 双线性
得 `(a1 ⨯ ((1-h)•a2 + h•a4))·a3 = ((a1 ⨯ a2)·a3) - h·(((a1 ⨯ a2)·a3) -
((a1 ⨯ a4)·a3))`。对 `a = (a1 ⨯ a2)·a3 > 0` 与
`b = ((a1 ⨯ a2)·a3) - ((a1 ⨯ a4)·a3)` 应用 `exists_esilon_real` 即得。

候选已有引理：
- `exists_esilon_real`（本文件，HOL :13025）
- `cross3_cross3`（Kepler/Text/TopologyFan.lean:2340，private）
- `crossProduct` 双线性（Mathlib/LinearAlgebra/CrossProduct.lean） -/
theorem invariant_crossr_dot_esilon_3piont (x y z v u : V3) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    (0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ) ((a2 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a3 : V3) : Fin 3 → ℝ)) →
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ h : ℝ, 0 < h → h < t →
        0 < (crossProduct ((a1 : V3) : Fin 3 → ℝ)
              ((((1 - h) • z + h • u - x : V3)) : Fin 3 → ℝ)) ⬝ᵥ
            ((a3 : V3) : Fin 3 → ℝ) := by
  sorry

end Kepler.Text
