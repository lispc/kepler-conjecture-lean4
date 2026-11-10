/-
  Kepler.Text.TameSpine.Reduction3J5PartsRot — tame-corr nb26：J5-6 rot 族两件
  （HOL `parts_rot` :62 / `core_rot` :75，final 支）。

  路线：`finalListParts`（在库，`parts L f = f.map (fun x => [x])`）两侧 +
  `rotFinalList`（在库，`final r ⇒ final (rot n r)`）+ `List.map_rotate`。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.TameSpine.Reduction3J5CoreFinal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart parts core finalList)

/-- **HOL `parts_rot`**（betwn_corek_z_x.hl:62）：
`good_list ∧ (∀x∈r, x∈darts) ∧ EdgeNondeg ∧ r.Nodup ∧ final r
⇒ parts L (r.rotate n) = (parts L r).rotate n`。 -/
theorem partsRot (L : fgraph ℕ) (hL : GoodList L) {r : List Dart}
    (hall : ∀ x ∈ r, x ∈ listOfDarts L)
    (hne : (Kepler.Text.TameLp.hypermapOfList L hL).EdgeNondegenerate)
    (hnd : r.Nodup) (hfin : finalList L r) (n : ℕ) :
    parts L (r.rotate n) = (parts L r).rotate n := by
  have hnd' : (r.rotate n).Nodup := List.nodup_rotate.mpr hnd
  have hall' : ∀ x ∈ r.rotate n, x ∈ listOfDarts L := by
    intro x hx
    exact hall x (List.mem_rotate.mp hx)
  have hfin' : finalList L (r.rotate n) := Kepler.Text.Reduction5.rotFinalList hfin hnd ⟨n, rfl⟩
  rw [Kepler.Text.Reduction5.finalListParts hL hall' hne hfin' hnd',
    Kepler.Text.Reduction5.finalListParts hL hall hne hfin hnd,
    List.map_rotate]

/-- **HOL `core_rot`**（betwn_corek_z_x.hl:75）：
同前提 ⇒ `core L (r.rotate n) = (core L r).rotate n`。 -/
theorem coreRot (L : fgraph ℕ) (hL : GoodList L) {r : List Dart}
    (hall : ∀ x ∈ r, x ∈ listOfDarts L)
    (hne : (Kepler.Text.TameLp.hypermapOfList L hL).EdgeNondegenerate)
    (hnd : r.Nodup) (hfin : finalList L r) (n : ℕ) :
    core L (r.rotate n) = (core L r).rotate n := by
  rw [show core L (r.rotate n)
        = (parts L (r.rotate n)).map (fun l => (l.headD (0, 0)).1) from rfl,
    show core L r = (parts L r).map (fun l => (l.headD (0, 0)).1) from rfl,
    partsRot L hL hall hne hnd hfin n, List.map_rotate]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.partsRot
#print axioms Kepler.Text.TameSpine.coreRot
