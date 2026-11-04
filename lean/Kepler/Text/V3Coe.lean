/-
Copyright (c) 2026 Kepler Lean4 lane `v3coe-t1`. Released under Apache 2.0.

# V3Coe: WithLp-coercion form canonicalization layer

`V3 = EuclideanSpace ℝ (Fin 3) = WithLp 2 (Fin 3 → ℝ)` towers (LA14 ZLZTHIC
continuity kit, LA34 v3_defor/azim kit, LA28 `_MK` tower) suffer a
context-dependent coercion-representation problem: the same mathematical
term `(x + y : V3)` lands as `(x + y).ofLp` (projection form) in one
context and `(WithLp.toLp 2 (x.ofLp + y.ofLp)).ofLp` (toLp-reinjection
form) in another.  The two are definitionally equal but not syntactically
equal, so `rw` / `simp` pattern matching fails across forms.

This file provides:
* the `v3coe` simp set (registered in `Kepler.Text.V3CoeAttr`) — a
  canonical-form simp lemma set that collapses every WithLp-coercion
  shape to the Pi-level (or surface V3-level) canonical form;
* `V3Coe.canonicalize` — a goal-side convenience tactic over the set;
* `V3Coe.canonicalGoal` — normalize the goal AND all local hypotheses
  with the set (per-location failure tolerant), after which plain
  `rw`/`ring`/`linarith` composition works.

It imports only `Kepler.Text.V3CoeAttr` (which imports only Mathlib) —
no other Kepler module — so it can never create import cycles.  Towers
register their own bridges (`dot3_eq_p14`, `inner_eq_dot`, ...) into the
set with `attribute [local v3coe] ...` after importing this module.

All lemmas here are standard-three (`propext, Classical.choice,
Quot.sound`) — no new axioms, no `sorry`.
-/

import Kepler.Text.V3CoeAttr

namespace Kepler.Text.V3Coe

/-! ## The `v3coe` set: canonical form contract

Both directions, no loops:
* coe of a structure-level operation  →  Pi-level operation
  (`WithLp.ofLp_add/sub/neg/zero/smul`);
* re-injection kills: `(WithLp.toLp p f).ofLp → f` (`WithLp.ofLp_toLp`),
  `WithLp.toLp p (WithLp.ofLp x) → x` (`WithLp.toLp_ofLp`);
* toLp of a Pi-level operation  →  surface WithLp operation
  (`WithLp.toLp_add/sub/neg/zero/smul`);
* subtractive/additive junk removal at both levels
  (`sub_zero`, `add_zero`, `zero_add`);
* `inner`/`norm²` on `EuclideanSpace ℝ ι` in terms of the Pi-level
  `dotProduct` (Mathlib-only counterparts of Kepler's `inner_eq_dot` /
  `norm_sq_eq_dot`, same orientation).
-/

attribute [v3coe] WithLp.ofLp_add
attribute [v3coe] WithLp.ofLp_sub
attribute [v3coe] WithLp.ofLp_neg
attribute [v3coe] WithLp.ofLp_zero
attribute [v3coe] WithLp.ofLp_smul
attribute [v3coe] WithLp.ofLp_toLp
attribute [v3coe] WithLp.toLp_add
attribute [v3coe] WithLp.toLp_sub
attribute [v3coe] WithLp.toLp_neg
attribute [v3coe] WithLp.toLp_zero
attribute [v3coe] WithLp.toLp_smul
attribute [v3coe] WithLp.toLp_ofLp
attribute [v3coe] sub_zero
attribute [v3coe] add_zero
attribute [v3coe] zero_add

/-- `inner` on `EuclideanSpace ℝ ι` is the Pi-level dot product
(orientation matched to Kepler's `inner_eq_dot`). -/
@[v3coe]
theorem inner_eq_dotProduct {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = (x.ofLp ⬝ᵥ y.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- Norm-squared on `EuclideanSpace ℝ ι` is the Pi-level self dot product
(orientation matched to Kepler's `norm_sq_eq_dot`). -/
@[v3coe]
theorem norm_sq_eq_dotProduct {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = (x.ofLp ⬝ᵥ x.ofLp) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]

/-! ## Tactics -/

open Lean Meta Simp Elab Tactic in
/-- Normalize the current goal and all non-dependent `Prop` hypotheses with
the `v3coe` set.  Per-location failure tolerant: a hypothesis whose
rewrite fails (e.g. motive-not-type-correct) is left untouched; the
tactic itself never fails.  Compose with the closer of your choice:
`canonicalGoal; linarith` etc. -/
elab (name := canonicalGoal) "canonicalGoal" : tactic => do
  let some ext ← Lean.Meta.getSimpExtension? `v3coe |
    throwError "V3Coe: `v3coe` attribute not registered"
  let thms ← ext.getTheorems
  let congr ← Lean.Meta.getSimpCongrTheorems
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false })
      (simpTheorems := #[thms]) (congrTheorems := congr)
  let simprocs ← Simp.getSimprocs
  liftMetaTactic fun g0 => do
    let rec go (g : MVarId) : MetaM (List MVarId) := do
      if (← g.isAssigned) then return []
      let mut g := g
      let mut closed := false
      -- hypotheses first, one at a time, tolerant to per-location failure
      for fv in (← g.getNondepPropHyps) do
        let before := g
        try
          let (r, _) ← simpGoal g ctx (simprocs := #[simprocs])
              (simplifyTarget := false) (fvarIdsToSimp := #[fv])
          match r with
          | none => closed := true
          | some (_, g') => g := g'
        catch _ =>
          g := before
      if closed then return []
      -- goal last
      try
        let (r, _) ← simpGoal g ctx (simprocs := #[simprocs])
            (simplifyTarget := true) (fvarIdsToSimp := #[])
        match r with
        | none => return []
        | some (_, g') =>
          -- normalization often leaves `a = a` with differing instance
          -- terms; try to close reflexively
          let rflClosed ← try
            g'.refl
            pure true
          catch _ => pure false
          if rflClosed then return [] else return [g']
      catch _ =>
        return [g]
    go g0

/-- Goal-side canonicalization: `simp only [v3coe]`, wrapped in `try` so it
is convenient to sprinkle before `rw` hot spots. -/
macro (name := canonicalize) "canonicalize" : tactic =>
  `(tactic| try simp only [v3coe])

end Kepler.Text.V3Coe
