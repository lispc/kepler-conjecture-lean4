/-
Copyright (c) 2026 Kepler Lean4 lane `v3coe-t1`. Released under Apache 2.0.

# V3Coe attribute registration

Declares the `v3coe` simp attribute (the WithLp-coercion canonical-form
simp set consumed by `Kepler.Text.V3Coe`).  It lives in its own module
because a simp attribute cannot be used in the file that declares it
(same rule as Mathlib's `Mathlib/Tactic/Attr/Register.lean`).

Imported only by `Kepler.Text.V3Coe`; towers never need to import this
file directly.
-/

import Mathlib

/-- The V3Coe canonical-form simp set (see `Kepler.Text.V3Coe`). -/
register_simp_attr v3coe
