import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

/-! BIEFJHU-a (HOL ineq entry `1965189142 a`) — schema-v3 hull expression.

Case `1965189142 a hybrid`, box `[1, 1352914700/2^30] × [3,34] × [1,1]^4`
(box top = dyadic ceiling of the HOL bound 1.26, P0' fix).
sqrt slots are dummy `(0, 0)`; the per-leaf mantissa certificates live in the
shard `TMParams.sqrtCerts`, open `atan` args at rung (128, -80), closed
`atan 1` args at (2048, -64).  Auto-generated — do not edit by hand. -/

/-- The hull-route expression of the BIEFJHU-a certificate. -/
def C1965189142aHullExpr : IExpr 6 :=
  (.sub (.sub (.mul (.const ⟨2, 0⟩) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64)))) (.mul (.const ⟨2, 0⟩) (.mul (.var 1) (.mul (.const ⟨2, 0⟩) (.trans .arctanK (.div (.mul (.add (.div (.mul (.var 0) (.mul (.trans .cosK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨6, 0⟩) (-64)) 2048 (-64)) (.const ⟨2, 0⟩))) (.const ⟨4, 0⟩) (-64)) (.div (.sqrt (.sub (.const ⟨1, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.div (.var 0) (.const ⟨2, 0⟩) (-64))) (.div (.var 0) (.const ⟨2, 0⟩) (-64)))) 0 0) (.const ⟨2, 0⟩) (-64))) (.ite (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) (.const ⟨3, -2⟩)) (.trans .sinK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) 128 (-80)) (.trans .cosK (.abs (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)))) 128 (-80)))) (.add (.const ⟨1, 0⟩) (.sqrt (.sub (.const ⟨1, 0⟩) (.mul (.mul (.add (.div (.mul (.var 0) (.mul (.trans .cosK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨6, 0⟩) (-64)) 2048 (-64)) (.const ⟨2, 0⟩))) (.const ⟨4, 0⟩) (-64)) (.div (.sqrt (.sub (.const ⟨1, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.div (.var 0) (.const ⟨2, 0⟩) (-64))) (.div (.var 0) (.const ⟨2, 0⟩) (-64)))) 0 0) (.const ⟨2, 0⟩) (-64))) (.ite (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) (.const ⟨3, -2⟩)) (.trans .sinK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) 128 (-80)) (.trans .cosK (.abs (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)))) 128 (-80)))) (.mul (.add (.div (.mul (.var 0) (.mul (.trans .cosK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨6, 0⟩) (-64)) 2048 (-64)) (.const ⟨2, 0⟩))) (.const ⟨4, 0⟩) (-64)) (.div (.sqrt (.sub (.const ⟨1, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.div (.var 0) (.const ⟨2, 0⟩) (-64))) (.div (.var 0) (.const ⟨2, 0⟩) (-64)))) 0 0) (.const ⟨2, 0⟩) (-64))) (.ite (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) (.const ⟨3, -2⟩)) (.trans .sinK (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)) 128 (-80)) (.trans .cosK (.abs (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.var 1) (-64)))) 128 (-80)))))) 0 0)) (-64)) 128 (-80)))))) (.add (.sub (.div (.const ⟨591, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.mul (.div (.const ⟨331, 0⟩) (.const ⟨10000, 0⟩) (-64)) (.var 1))) (.mul (.div (.const ⟨253, 0⟩) (.const ⟨500, 0⟩) (-64)) (.div (.sub (.div (.const ⟨63, 0⟩) (.const ⟨50, 0⟩) (-64)) (.var 0)) (.sub (.div (.const ⟨63, 0⟩) (.const ⟨50, 0⟩) (-64)) (.const ⟨1, 0⟩)) (-64)))))

end Kepler.Interval.Cases
