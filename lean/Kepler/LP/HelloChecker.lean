/-
  Hello-checker: the smallest possible instance of this project's
  "untrusted generator → certificate → verified checker" pipeline.

  A `BoundCert` is a certificate claiming `claim ≤ bound` over the
  rationals. The checker is a plain `Bool`-valued function on `Rat`;
  certificate validity is established by proofs the Lean kernel can
  re-check (`norm_num` produces kernel-checkable proof terms).
  (`native_decide` is forbidden project-wide, see PLAN.md §2.)
-/
import Mathlib

namespace Kepler.LP

/-- A certificate claiming that `claim ≤ bound`. -/
structure BoundCert where
  claim : Rat
  bound : Rat
deriving DecidableEq

/-- Checker: the certificate is valid iff the claimed inequality holds. -/
def BoundCert.check (c : BoundCert) : Bool :=
  c.claim ≤ c.bound

/-- Soundness: a passing certificate really witnesses the inequality. -/
theorem BoundCert.check_sound (c : BoundCert) (h : c.check = true) :
    c.claim ≤ c.bound :=
  of_decide_eq_true h

/-- Example certificate produced by an (untrusted) external generator. -/
def exampleCert : BoundCert := ⟨355 / 113, 22 / 7⟩

/-- The kernel re-checks the certificate: 355/113 ≤ 22/7. -/
theorem exampleCert_valid : exampleCert.check = true :=
  decide_eq_true (show (355 / 113 : Rat) ≤ 22 / 7 by norm_num)

/-- End-to-end: the extracted mathematical fact, kernel-verified. -/
theorem example_bound : (355 / 113 : Rat) ≤ 22 / 7 :=
  BoundCert.check_sound exampleCert exampleCert_valid

end Kepler.LP
