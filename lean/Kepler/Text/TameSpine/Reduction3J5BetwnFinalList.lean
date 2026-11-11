/-
  Kepler.Text.TameSpine.Reduction3J5BetwnFinalList — tame-corr nb27：J5-6
  `betwn_final_list`（HOL betwn_corek_z_x.hl:42）。

  查重命中（不重落）：`betwn_rot` = `TameSpine.betwnRot`（JcajyduBetwnRot:179，
  已含 `n` 全函数化强化）；本件只做 `finalListRot` 换元 + `betwnRot` 消去。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.JcajyduBetwnRot
import Kepler.Text.Reduction5BetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList findFaceDarts listOfDarts)
open Kepler.Text.Reduction5 (Dart finalList)

/-- **HOL `betwn_final_list`**（betwn_corek_z_x.hl:42）：
`good_list ∧ uniq r ∧ final r ∧ x,y,z∈r ∧ y≠z ∧ x∈darts
⇒ between (find_face L x) y z = between r y z`。 -/
theorem betwnFinalList (L : fgraph ℕ) (hL : GoodList L) {r : List Dart}
    {x y z : Dart} (hnd : r.Nodup) (hfin : finalList L r)
    (hx : x ∈ r) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hxd : x ∈ listOfDarts L) :
    between (findFaceDarts L x) y z = between r y z := by
  obtain ⟨n, hn⟩ := Kepler.Text.Reduction5.finalListRot hL hfin hx hnd hxd
  rw [← hn]
  exact (betwnRot hnd hy hz hyz n).symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.betwnFinalList
