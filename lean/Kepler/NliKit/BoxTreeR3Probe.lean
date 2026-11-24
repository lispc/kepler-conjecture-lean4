/-
Kepler.NliKit.BoxTreeR3Probe — R3 single-cell decide-leaf probe (lane
`nlikit-boxtree-impl-w1`; G-3 scope: ONE cell, parallel only, NOT wired
into the Cover).

Cell: `Kepler.NliBanks20.cell00_core` (wt2A layer0 corner cell)
    y4 ∈ [2.67421356, √8], y5 ∈ [2.52, √8], y6 ∈ [2, 2.058], hd domain.

What this probe validates, per REGRESSION-v2 §0 R3:

1. **Decide leaf (zero axioms)**: the leaf data row `probeRow` is emitted in
   the `LeafRow 3 Unit` form and the closed ℤ data certificate
   (`probeLeafCheck`) is discharged by kernel `decide` — no `axiom`, no
   `sorry`, no `native_decide`.  The certificate is the endpoint window of
   the cell against the shared 2^-40 dyadic grid: every comparison is a
   closed integer cross-multiplication.
2. **Endpoint consistency**: each probe endpoint literal is registered as a
   `by decide` identity, so the row data is pinned to the emitted integers
   (same pattern as the replay vD facts).
3. **Same box, same predicate**: `probe_leaf_sound` re-derives the cell's
   real predicate on `rowBox probeRow` from the ORIGINAL cell witness
   `cell00_core`; the row's box is proven inside the cell window.  This is
   an unwired parallel validation — it is not referenced by any `Cover`.

G-3 stands: decide-ization of the full wt2A leaf predicate (hd fold +
norm_num margin) is NOT attempted here; the decide layer is the closed ℤ
data certificate.
-/
import Kepler.NliKit.BoxTree
import Kepler.NliBanks20

set_option maxHeartbeats 1000000

namespace Kepler.NliKit.BoxTreeR3Probe

open Kepler.NliKit.BoxTree

/-- point endpoint on the 2^-40 grid -/
def pt (m : ℤ) : DC := ⟨(40 : ℤ), m, m⟩

/-- cell00 dyadic data row: lo = ceil(cell lo), hi = floor(cell hi).
The row box is the closed dyadic box [lo, hi] on each axis. -/
def probeRow : LeafRow 3 Unit :=
  { boxLo := fun i => match (i : ℕ) with
      | 0 => pt 2940328904377   -- ceil(2.67421356 * 2^40)
      | 1 => pt 2770769301996   -- ceil(2.52 * 2^40)
      | _ => pt 2199023255552   -- 2 * 2^40
    boxHi := fun i => match (i : ℕ) with
      | 0 => pt 3109888506756   -- floor(2.82842712 * 2^40)
      | 1 => pt 3109888506756
      | _ => pt 2262794929963   -- floor(2.058 * 2^40)
    aux := () }

/-- closed ℤ data certificate (the "leaf check"): per-axis ordering plus the
cell window containment, all as integer cross-multiplications against the
2^-40 grid.  Kernel `decide` on this fold is the R3 decide-leaf pass. -/
def probeLeafCheck : Bool :=
  decide (2940328904377 ≤ 3109888506756) &&
  decide (2770769301996 ≤ 3109888506756) &&
  decide (2199023255552 ≤ 2262794929963) &&
  -- 2.67421356 ≤ lo4: 267421356 * 2^40 ≤ 2940328904377 * 10^8
  decide (267421356 * 1099511627776 ≤ 2940328904377 * 100000000) &&
  -- hi4 ≤ 2.82842712
  decide (3109888506756 * 100000000 ≤ 282842712 * 1099511627776) &&
  -- 2.52 ≤ lo5
  decide (252 * 1099511627776 ≤ 2770769301996 * 100) &&
  -- 2 ≤ lo6
  decide (2 * 1099511627776 ≤ 2199023255552) &&
  -- hi6 ≤ 2.058
  decide (2262794929963 * 1000 ≤ 2058 * 1099511627776)

/-- R3 decide-leaf pass: kernel `decide`, zero axioms. -/
theorem probe_leaf_pass : probeLeafCheck = true := by decide

/-- Endpoint literals pinned by `decide` (same idiom as the replay vD facts). -/
theorem probe_lo4 : probeRow.boxLo (0 : Fin 3) = pt 2940328904377 := by decide
theorem probe_hi4 : probeRow.boxHi (0 : Fin 3) = pt 3109888506756 := by decide
theorem probe_lo5 : probeRow.boxLo (1 : Fin 3) = pt 2770769301996 := by decide
theorem probe_hi5 : probeRow.boxHi (1 : Fin 3) = pt 3109888506756 := by decide
theorem probe_lo6 : probeRow.boxLo (2 : Fin 3) = pt 2199023255552 := by decide
theorem probe_hi6 : probeRow.boxHi (2 : Fin 3) = pt 2262794929963 := by decide

/-- the shared 2^-40 grid lemma used by the value bridges -/
theorem kNat : ((40 : ℤ).toNat) = 40 := rfl

/-- ℝ-side bridge: the probe box sits inside the cell00 window. -/
theorem probe_lo4_val : (probeRow.boxLo (0 : Fin 3)).value
    = (2940328904377 : ℝ) / 1099511627776 := by
  rw [probe_lo4]; simp [DC.value, pt, kNat]; norm_num

theorem probe_hi4_val : (probeRow.boxHi (0 : Fin 3)).value
    = (3109888506756 : ℝ) / 1099511627776 := by
  rw [probe_hi4]; simp [DC.value, pt, kNat]; norm_num

theorem probe_lo5_val : (probeRow.boxLo (1 : Fin 3)).value
    = (2770769301996 : ℝ) / 1099511627776 := by
  rw [probe_lo5]; simp [DC.value, pt, kNat]; norm_num

theorem probe_hi5_val : (probeRow.boxHi (1 : Fin 3)).value
    = (3109888506756 : ℝ) / 1099511627776 := by
  rw [probe_hi5]; simp [DC.value, pt, kNat]; norm_num

theorem probe_lo6_val : (probeRow.boxLo (2 : Fin 3)).value
    = (2199023255552 : ℝ) / 1099511627776 := by
  rw [probe_lo6]; simp [DC.value, pt, kNat]; norm_num

theorem probe_hi6_val : (probeRow.boxHi (2 : Fin 3)).value
    = (2262794929963 : ℝ) / 1099511627776 := by
  rw [probe_hi6]; simp [DC.value, pt, kNat]; norm_num

/-- R3 "same box, same predicate": the original cell00 witness discharges the
target predicate on the probe row box.  Parallel validation only — nothing in
the replay modules references this theorem. -/
theorem probe_leaf_sound :
    ∀ x ∈ rowBox probeRow,
      (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
      0 < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2) := by
  intro x hx hd
  have h4 := hx (0 : Fin 3)
  have h5 := hx (1 : Fin 3)
  have h6 := hx (2 : Fin 3)
  rw [probe_lo4_val, probe_hi4_val] at h4
  rw [probe_lo5_val, probe_hi5_val] at h5
  rw [probe_lo6_val, probe_hi6_val] at h6
  refine Kepler.NliBanks20.cell00_core (by linarith) ?_ (by linarith) ?_
    (by linarith) ?_ hd
  · have hlt : (3109888506756 : ℝ) / 1099511627776 ≤ (2.82842712:ℝ) := by
      norm_num [show (1099511627776 : ℝ) = (2:ℝ)^40 from by norm_num]
    have hsqrt : (2.82842712:ℝ) ≤ Real.sqrt 8 :=
      Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  · have hlt : (3109888506756 : ℝ) / 1099511627776 ≤ (2.82842712:ℝ) := by
      norm_num [show (1099511627776 : ℝ) = (2:ℝ)^40 from by norm_num]
    have hsqrt : (2.82842712:ℝ) ≤ Real.sqrt 8 :=
      Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  · have hlt : (2262794929963 : ℝ) / 1099511627776 ≤ (2.058:ℝ) := by
      norm_num [show (1099511627776 : ℝ) = (2:ℝ)^40 from by norm_num]
    linarith

#print axioms probe_leaf_pass
#print axioms probe_leaf_sound

end Kepler.NliKit.BoxTreeR3Probe
