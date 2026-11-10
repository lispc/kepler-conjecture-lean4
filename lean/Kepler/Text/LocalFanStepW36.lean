/-
Kepler/Text/LocalFanStepW36.lean — wave W36a：`th3` 簇移植（fan.hl:357–388 的 Lean 对件）。

HOL 原文（`reference/flyspeck/text_formalization/fan/fan.hl`，经 `open Fan` 进
NKEZBFC 作用域）：
```
th3a12 : ~collinear {x,v,u} ==> DISJOINT {x,u} {v}
th3a   : ~collinear {x,v,u} ==> DISJOINT {x,v} {u}
th3b   : ~collinear {x,v,u} ==> ~(x=v)
th3b1  : ~collinear {x,v,u} ==> ~(x=u)
th3c   : ~collinear {x,v,u} ==> ~(u IN aff{x,v})
th3d   : ~(x=v) /\ ~(x=u) ==> DISJOINT {x} {v,u}
th3    ≡ 上述六件合取（MESON_TAC 组装）
```
**语义判定（勘误）**：th3 簇 = **非共线三点的分离件**（两两互异 + 三 DISJOINT +
`u ∉ aff{x,v}`），**不含任何锥/度量内容**——它与「非共线前提」逐件等价
（th3c ⟺ 非共线，经 Mathlib `collinear_insert_of_mem_affineSpan_pair`）。

件目（7 件，全部 std3；复用 `collinear3_pair_left/right`、`collinear_pair`、
`collinear_insert_of_mem_affineSpan_pair`、`Set.disjoint_singleton_*`）：
* §1 th3a12 / th3a / th3b / th3b1 / th3c / th3d。
* §2 th3（六合取总装）。
-/
import Kepler.Text.LocalFanStepW32

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## §1 th3 分件 -/

/-- `th3b`（fan.hl:377）：非共线 ⇒ `x ≠ v`。 -/
theorem pW36_th3b {x v u : V3} (h : ¬ Collinear3 x v u) : x ≠ v := by
  intro he
  apply h
  rw [he]
  show Collinear ℝ ({v, v, u} : Set V3)
  have hset : ({v, v, u} : Set V3) = {v, u} := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact collinear_pair ℝ v u

/-- `th3b1`（fan.hl:380）：非共线 ⇒ `x ≠ u`。 -/
theorem pW36_th3b1 {x v u : V3} (h : ¬ Collinear3 x v u) : x ≠ u := by
  intro he
  apply h
  rw [he]
  show Collinear ℝ ({u, v, u} : Set V3)
  have hset : ({u, v, u} : Set V3) = {u, v} := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact collinear_pair ℝ u v

/-- `th3a`（fan.hl:368）：非共线 ⇒ `DISJOINT {x,v} {u}`。 -/
theorem pW36_th3a {x v u : V3} (h : ¬ Collinear3 x v u) :
    Disjoint ({x, v} : Set V3) {u} := by
  have hux : u ≠ x := fun he => h (by
    rw [he]
    show Collinear ℝ ({x, v, x} : Set V3)
    have hset : ({x, v, x} : Set V3) = {x, v} := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ x v)
  have huv : u ≠ v := fun he => h (by
    rw [he]
    show Collinear ℝ ({x, v, v} : Set V3)
    have hset : ({x, v, v} : Set V3) = {x, v} := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ x v)
  rw [Set.disjoint_singleton_right]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hux, huv⟩

/-- `th3a12`（fan.hl:363）：非共线 ⇒ `DISJOINT {x,u} {v}`。 -/
theorem pW36_th3a12 {x v u : V3} (h : ¬ Collinear3 x v u) :
    Disjoint ({x, u} : Set V3) {v} := by
  have hvx : v ≠ x := fun he => h (by
    rw [he]
    show Collinear ℝ ({x, x, u} : Set V3)
    have hset : ({x, x, u} : Set V3) = {x, u} := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ x u)
  have hvu : v ≠ u := fun he => h (by
    rw [he]
    show Collinear ℝ ({x, u, u} : Set V3)
    have hset : ({x, u, u} : Set V3) = {x, u} := by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ x u)
  rw [Set.disjoint_singleton_right]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hvx, hvu⟩

/-- `th3c`（fan.hl:383）：非共线 ⇒ `u ∉ aff{x,v}`（Mathlib 桥：
`collinear_insert_of_mem_affineSpan_pair` 的逆否）。 -/
theorem pW36_th3c {x v u : V3} (h : ¬ Collinear3 x v u) :
    u ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
  intro hu
  apply h
  show Collinear ℝ ({x, v, u} : Set V3)
  have hcol := collinear_insert_of_mem_affineSpan_pair (k := ℝ)
    (p₁ := u) (p₂ := x) (p₃ := v)
    (show u ∈ line[ℝ, x, v] from hu)
  have hset : ({x, v, u} : Set V3) = {u, x, v} := by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact hcol

/-- `th3d`（fan.hl:385）：互异 ⇒ `DISJOINT {x} {v,u}`。 -/
theorem pW36_th3d {x v u : V3} (h1 : x ≠ v) (h2 : x ≠ u) :
    Disjoint ({x} : Set V3) {v, u} := by
  rw [Set.disjoint_singleton_left]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h1, h2⟩

/-! ## §2 `th3` 总装（HOL :388） -/

/-- **`th3`（fan.hl:388）**：非共线三点的分离六合取（证明 = `MESON_TAC` 六件）。 -/
theorem pW36_th3 {x v u : V3} (h : ¬ Collinear3 x v u) :
    x ≠ v ∧ x ≠ u ∧ Disjoint ({x, v} : Set V3) {u} ∧
      Disjoint ({x, u} : Set V3) {v} ∧ Disjoint ({x} : Set V3) {v, u} ∧
      u ∉ (affineSpan ℝ ({x, v} : Set V3) : Set V3) := by
  have hb := pW36_th3b h
  have hb1 := pW36_th3b1 h
  exact ⟨hb, hb1, pW36_th3a h, pW36_th3a12 h, pW36_th3d hb hb1, pW36_th3c h⟩

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW36_th3b
#print axioms Kepler.Text.pW36_th3b1
#print axioms Kepler.Text.pW36_th3a
#print axioms Kepler.Text.pW36_th3a12
#print axioms Kepler.Text.pW36_th3c
#print axioms Kepler.Text.pW36_th3d
#print axioms Kepler.Text.pW36_th3
