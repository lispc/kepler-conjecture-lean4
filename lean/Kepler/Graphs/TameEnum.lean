/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `TameEnum.thy`.

Source: `reference/afp-flyspeck-tame/TameEnum.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).
-/
import Kepler.Graphs.Generator

namespace Kepler.Graphs

/-- `TameEnum.thy: is_tame`. -/
def is_tame (g : Graph) : Bool :=
  tame10 g && tame11a g && tame12o g && is_tame13a g

/-- `TameEnum.thy: next_tame`. -/
def next_tame (p : Nat) (g : Graph) : List Graph :=
  (next_tame0 p g).filter (fun g' => !g'.final || is_tame g')

/-- `TameEnum.thy: TameEnumP`. -/
def TameEnumP (p : Nat) : Graph → Prop :=
  fun g => RTranCl (next_tame p) (Seed p) g ∧ g.final

/-- `TameEnum.thy: TameEnum`. -/
def TameEnum : Graph → Prop := fun g => ∃ p, p ≤ 3 ∧ TameEnumP p g

end Kepler.Graphs
