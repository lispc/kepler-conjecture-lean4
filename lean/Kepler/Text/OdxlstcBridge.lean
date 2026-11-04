/-
OdxlstcBridge — the parameter-version bridge from the LA31 `ODXLSTC` lane to
the LA34 `IMJXPHR` lane.

LA31 proves the parametric `ODXLSTCv2` (`ODXLSTCv2_p31`) with **arrow-shaped**
time windows

  `∃ e, 0 < e ∧ ∀ t, -e < t → t < e → ...`,

while LA34 states the registry props `ZLZTHIC_prop_p34` / `MHAEYJN_prop_p34`
with **conjunction-shaped** windows

  `∃ e, 0 < e ∧ ∀ t, -e < t ∧ t < e → ...`.

The two window shapes are propositionally (not definitionally) equivalent, so
LA34 must cross an explicit bridge.  This module provides the two-directional
`ZLZTHIC`/`MHAEYJN` bridges plus the assembled parametric `ODXLSTCv2` in the
exact shape the LA34 `IMJXPHR_p34` proof consumes, i.e. with hypotheses

  `ZLZTHIC_prop_p34 → MHAEYJN_prop_p34 → <ODXLSTCv2 conclusion>`.

Import DAG / acyclicity: this module imports **only** `Kepler.Text.LocalAuto31`
(which imports `LocalAuto18`, `PackingAuto2`, `Mathlib`).  The transitive
closure of `LocalAuto31` does not contain `LocalAuto34` (nor `LocalAuto28`), so
adding `import Kepler.Text.OdxlstcBridge` to `LocalAuto34` cannot create an
import cycle: `LocalAuto34 → OdxlstcBridge → LocalAuto31 → [LocalAuto18 → … ]`.
The mirrored `*_prop_p34_bridge` definitions below are byte-for-byte copies of
the `Prop` bodies in `LocalAuto34` (which cannot be imported here without
closing the cycle); they are transparent `def`s, hence definitionally equal to
the LA34 originals — LA34 consumes these theorems directly.

Provenance: statements and proofs are the verified `probe_bridge.lean` of lane
`la34-odxlstc-w13` (RC=0, all five theorems std-3), adapted only by renaming
the mirrored props and by dropping the now-unneeded `import LocalAuto34`.
-/

import Kepler.Text.LocalAuto31

set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- Copy of `LocalAuto34.ZLZTHIC_prop_p34` (conjunction-shaped window).
Kept in the bridge so the bridge does not import `LocalAuto34`. -/
def ZLZTHIC_prop_p34_bridge : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3),
    ConvexLocalFan V E FF →
    Generic V E →
    Deformation f V a b →
    (∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Generic ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- Copy of `LocalAuto34.MHAEYJN_prop_p34` (conjunction-shaped window).
Kept in the bridge so the bridge does not import `LocalAuto34`. -/
def MHAEYJN_prop_p34_bridge : Prop :=
  ∀ (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (v w u : V3),
    ConvexLocalFan V E FF →
    Lunar v w V E →
    Deformation f V a b →
    interiorAngle1 0 FF v < Real.pi →
    u ∈ V → u ≠ v → u ≠ w →
    (∀ u' ∈ V, u ≠ u' → ∀ t ∈ Icc a b, f u' t = u') →
    (∀ t ∈ Icc a b, f u t ∈ affineSpan ℝ ({0, v, w, u} : Set V3)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Lunar v w ((fun v => f v t) '' V)
        ((fun e => (fun v => f v t) '' e) '' E)

/-- Propositional bridge: LA31's `ZLZTHIC_concl_p31` (arrow-shaped window)
implies LA34's `ZLZTHIC_prop_p34` (conjunction-shaped window). -/
theorem w13_zlzthic_p34_of_p31 (h : ZLZTHIC_concl_p31) :
    ZLZTHIC_prop_p34_bridge := by
  intro a b V E FF f hcf hg hd hang
  obtain ⟨e, he, hee⟩ := h a b V E FF f hcf hg hd hang
  exact ⟨e, he, fun t ht => hee t ht.1 ht.2⟩

/-- Converse bridge. -/
theorem w13_zlzthic_p31_of_p34 (h : ZLZTHIC_prop_p34_bridge) :
    ZLZTHIC_concl_p31 := by
  intro a b V E FF f hcf hg hd hang
  obtain ⟨e, he, hee⟩ := h a b V E FF f hcf hg hd hang
  exact ⟨e, he, fun t ht1 ht2 => hee t ⟨ht1, ht2⟩⟩

/-- Propositional bridge: LA31's `MHAEYJN_concl_p31` implies LA34's
`MHAEYJN_prop_p34`. -/
theorem w13_mhaeyjn_p34_of_p31 (h : MHAEYJN_concl_p31) :
    MHAEYJN_prop_p34_bridge := by
  intro a b V E FF f v w u hcf hl hd hang hu hv hw hpin haff
  obtain ⟨e, he, hee⟩ := h a b V E FF f v w u hcf hl hd hang hu hv hw hpin haff
  exact ⟨e, he, fun t ht => hee t ht.1 ht.2⟩

/-- Converse bridge. -/
theorem w13_mhaeyjn_p31_of_p34 (h : MHAEYJN_prop_p34_bridge) :
    MHAEYJN_concl_p31 := by
  intro a b V E FF f v w u hcf hl hd hang hu hv hw hpin haff
  obtain ⟨e, he, hee⟩ := h a b V E FF f v w u hcf hl hd hang hu hv hw hpin haff
  exact ⟨e, he, fun t ht1 ht2 => hee t ⟨ht1, ht2⟩⟩

/-- The LA31 parametric conclusion re-typed into LA34's registry props:
this is the exact shape the LA34 `IMJXPHR_p34` lane consumes. -/
theorem w13_ODXLSTCv2_parametric_from_p31
    (h : ZLZTHIC_concl_p31 → MHAEYJN_concl_p31 → ODXLSTCv2_concl_p31)
    (hz : ZLZTHIC_prop_p34_bridge) (hm : MHAEYJN_prop_p34_bridge) :
    ∀ (s : ScsV39) (k : ℕ) (w : ℕ → V3) (l : ℕ),
      isScsV39 s → w ∈ MMsV39 s → s.k = k → 3 < k →
      (∀ i, scsDiag k l i → 4 * h0 < s.b l i) → ‖w l‖ ≠ 2 →
      (∀ i : ℕ, ¬(i % k = l % k) → s.a l i < dist (w l) (w i)) →
      (∀ i, ¬ s.J l i) →
      (∀ (V : Set V3) (E : Set (Set V3)) (v : V3), V = Set.range w →
        E = (Set.range fun i : ℕ => {w i, w (i + 1)}) → ¬ Lunar v (w l) V E) →
      False := by
  intro s k w l hs hmw hk hk3 hdiag1 hnorm hlt hJ hlunar
  exact h (w13_zlzthic_p31_of_p34 hz) (w13_mhaeyjn_p31_of_p34 hm)
    s k l w hs hmw hk hk3 hdiag1 hnorm hlt hJ hlunar

end Kepler.Text
