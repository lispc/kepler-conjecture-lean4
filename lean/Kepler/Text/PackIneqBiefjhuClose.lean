/-
  BIEFJHU-a: the TM/hull certificate closes `bank_1965189142a`.
  The mathematics lives in `Kepler.Text.PackingAuto22PackIneqBiefjhu`
  (`pka_bief_close`, conditional on the certificate's positivity lemma);
  this file supplies that lemma from the schema-v3 hull certificate.
  No axiom / sorry / native_decide; the only `decide`s are the certificate
  machinery's kernel replays inside `C1965189142aHull`.
-/
import Kepler.Text.PackingAuto22PackIneqBiefjhu
import Kepler.Interval.Cases.C1965189142aHull

namespace Kepler.Text

/-- **BIEFJHU-a closed** (HOL ineq entry `1965189142 a`, ineq.hl:1598). -/
theorem packIneqABIEFJHUa : bank_1965189142a :=
  pka_bief_close (fun ρ hρ => Kepler.Interval.Cases.C1965189142aHull_pos ρ hρ)

#print axioms packIneqABIEFJHUa

end Kepler.Text
