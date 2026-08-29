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

end Kepler.Geom

/- 计划中的首批引理（下一块）：（flyspeck.ml:732，
 系数吸收手术）、 展开律。 -/
