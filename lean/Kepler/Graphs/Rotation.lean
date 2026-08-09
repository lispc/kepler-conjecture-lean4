/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Rotation.thy`.

Source: `reference/afp-flyspeck-tame/Rotation.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).
Only the definitions `rotate_to` and `rotate_min` are ported; the lemmas
(about `cong`, rotation equivalence) are not needed for the executable core.
-/
import Kepler.Graphs.ListAux

namespace Kepler.Graphs

/-- `Rotation.thy: rotate_to`. Rotates `vs` so that `v` becomes the head. -/
def rotate_to [BEq α] (vs : List α) (v : α) : List α :=
  v :: (splitAt v vs).2 ++ (splitAt v vs).1

/-- `Rotation.thy: rotate_min`. Rotates `vs` so that its minimal element
becomes the head. -/
def rotate_min (vs : List Nat) : List Nat :=
  rotate_to vs (min_list vs)

end Kepler.Graphs
