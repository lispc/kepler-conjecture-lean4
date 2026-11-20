/-
Kepler.Text.Wt1TowerTower — lane `cell3-wt1-tower-build-w2` (2026-11-20),
phase 2 of the wt1 second-order tower (route A′): the tower assembly.

This file reduces the core obligation of `bank_QZECFICwt1_of_core`
(`0 < w1aF` on the box, `Δ ≥ 0`) to two explicit certificate families:

* `hP1`: the y5-second-derivative nonpositivity `w1F2 ≤ 0` on the box
  (the P1 certificate layer, phase-2 main body);
* `hE00`, `hE01`, `hE11`: positivity on the three independent edges
  `y5 = y6 = 2`, `y5 = 2, y6 = 2*hminus`, `y5 = y6 = 2*hminus`
  (the 1D edge certificates); the fourth edge `E10` follows by the
  `y5 ↔ y6` symmetry `nb21_w1aF_symm`.

Tower logic:
1. `w1aF_concaveOn_y5`: P1 + the assumption-free D1/D2 chain
   (`Wt1TowerDomain`) + `concaveOn_of_hasDerivAt2_nonpos` give concavity
   of `s ↦ w1aF y4 s y6` on `Icc 2 (2*hminus)`;
2. the same for `s ↦ w1aF y4 y5 s` by `nb21_w1aF_symm`;
3. `ConcaveOn.min_le_of_mem_Icc` (two-fold) gives
   `w1aF y4 y5 y6 ≥ min` over the four edges;
4. the three edge facts + symmetry close the core, and
   `bank_QZECFICwt1_of_core` gives the bank.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.Wt1TowerDomain
import Kepler.Text.Wt1TowerSymm
import Kepler.Text.Gamma4ConcaveBridge
import Mathlib.Analysis.Convex.Jensen

set_option maxHeartbeats 2000000

namespace Kepler.Text
open Kepler.NliBanks21
open Set

/-! ## 1. Concavity from the P1 hypothesis -/

/-- Concavity in `y5` on `[2, 2*hminus]`, from `w1F2 ≤ 0` on the box slice. -/
theorem w1aF_concaveOn_y5 (y4 y6 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hminus)
    (hP1 : ∀ s ∈ Set.Ioo (2 : ℝ) (2 * hminus), w1F2 y4 s y6 ≤ 0) :
    ConcaveOn ℝ (Set.Icc (2 : ℝ) (2 * hminus)) (fun s => w1aF y4 s y6) := by
  refine concaveOn_of_hasDerivAt2_nonpos (f' := fun s => w1F1 y4 s y6)
    (f'' := fun s => w1F2 y4 s y6) ?_ ?_ ?_
  · intro t ht
    exact w1aF_hasDerivAt_y5_hminus y4 t y6 h4 h4' ht.1 ht.2 h6 h6'
  · intro t ht
    exact w1aF_hasDerivAt2_y5_hminus y4 t y6 h4 h4'
      (le_of_lt ht.1) (le_of_lt ht.2) h6 h6'
  · intro t ht
    exact hP1 t ht

/-- Concavity in `y6` on `[2, 2*hminus]`, by the `y5 ↔ y6` symmetry. -/
theorem w1aF_concaveOn_y6 (y4 y5 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (hP1 : ∀ s ∈ Set.Ioo (2 : ℝ) (2 * hminus), w1F2 y4 s y5 ≤ 0) :
    ConcaveOn ℝ (Set.Icc (2 : ℝ) (2 * hminus)) (fun s => w1aF y4 y5 s) := by
  refine ConcaveOn.congr (w1aF_concaveOn_y5 y4 y5 h4 h4' h5 h5' hP1) ?_
  intro s hs
  exact nb21_w1aF_symm y4 s y5 (by linarith) (by linarith [hs.1]) (by linarith)

/-! ## 2. The two-fold minimum principle -/

/-- **Tower step**: the value at `(y5, y6)` is at least the minimum over the
four edges `{2, 2*hminus} × {2, 2*hminus}`. -/
theorem w1aF_ge_edges (y4 y5 y6 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hminus)
    (hP1 : ∀ a b : ℝ, 2 ≤ a → a ≤ 2 * hminus → 2 ≤ b → b ≤ 2 * hminus →
      w1F2 y4 a b ≤ 0)
    (hE : 0 < w1aF y4 2 2 ∧ 0 < w1aF y4 2 (2 * hminus) ∧
      0 < w1aF y4 (2 * hminus) 2 ∧ 0 < w1aF y4 (2 * hminus) (2 * hminus)) :
    0 < w1aF y4 y5 y6 := by
  -- concavity in y6 at fixed y5, and in y5 at both endpoints
  have hcy6 := w1aF_concaveOn_y6 y4 y5 h4 h4' h5 h5'
    (fun s hs => hP1 s y5 (le_of_lt hs.1) (le_of_lt hs.2) h5 h5')
  have hcy5a := w1aF_concaveOn_y5 y4 2 h4 h4' le_rfl (by linarith [h4])
    (fun s hs => hP1 s 2 (le_of_lt hs.1) (le_of_lt hs.2) le_rfl (by linarith [h4]))
  have hcy5b := w1aF_concaveOn_y5 y4 (2 * hminus) h4 h4' (by linarith [h4]) le_rfl
    (fun s hs => hP1 s (2 * hminus) (le_of_lt hs.1) (le_of_lt hs.2)
      (by linarith [h4]) le_rfl)
  have h_lo : (2 : ℝ) ≤ 2 * hminus := by linarith [h4]
  -- step 1: fold y6
  have step1 : min (w1aF y4 y5 2) (w1aF y4 y5 (2 * hminus)) ≤ w1aF y4 y5 y6 :=
    hcy6.min_le_of_mem_Icc (Set.mem_Icc.mpr ⟨le_rfl, h_lo⟩)
      (Set.mem_Icc.mpr ⟨h_lo, le_rfl⟩) (Set.mem_Icc.mpr ⟨h6, h6'⟩)
  -- step 2: fold y5 at both y6 endpoints
  have step2a : min (w1aF y4 2 2) (w1aF y4 (2 * hminus) 2) ≤ w1aF y4 y5 2 :=
    hcy5a.min_le_of_mem_Icc (Set.mem_Icc.mpr ⟨le_rfl, h_lo⟩)
      (Set.mem_Icc.mpr ⟨h_lo, le_rfl⟩) (Set.mem_Icc.mpr ⟨h5, h5'⟩)
  have step2b : min (w1aF y4 2 (2 * hminus)) (w1aF y4 (2 * hminus) (2 * hminus))
      ≤ w1aF y4 y5 (2 * hminus) :=
    hcy5b.min_le_of_mem_Icc (Set.mem_Icc.mpr ⟨le_rfl, h_lo⟩)
      (Set.mem_Icc.mpr ⟨h_lo, le_rfl⟩) (Set.mem_Icc.mpr ⟨h5, h5'⟩)
  -- positivity of the nested minimum
  have h1 : 0 < min (w1aF y4 2 2) (w1aF y4 (2 * hminus) 2) := lt_min hE.1 hE.2.2.1
  have h2 : 0 < min (w1aF y4 2 (2 * hminus)) (w1aF y4 (2 * hminus) (2 * hminus)) :=
    lt_min hE.2.1 hE.2.2.2
  have h3 : 0 < min (min (w1aF y4 2 2) (w1aF y4 (2 * hminus) 2))
      (min (w1aF y4 2 (2 * hminus)) (w1aF y4 (2 * hminus) (2 * hminus))) :=
    lt_min h1 h2
  have h4le : min (min (w1aF y4 2 2) (w1aF y4 (2 * hminus) 2))
      (min (w1aF y4 2 (2 * hminus)) (w1aF y4 (2 * hminus) (2 * hminus)))
      ≤ min (w1aF y4 y5 2) (w1aF y4 y5 (2 * hminus)) :=
    min_le_min step2a step2b
  exact lt_of_lt_of_le (lt_of_lt_of_le h3 h4le) step1

/-! ## 3. Core reduction and the bank -/

/-- The core margin follows from P1 plus the three independent edge facts
(the fourth edge being the `y5 ↔ y6` mirror). -/
theorem w1aF_pos_core
    (hP1 : ∀ y4 y5 y6 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
      w1F2 y4 y5 y6 ≤ 0)
    (hE00 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 0 < w1aF y4 2 2)
    (hE01 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 0 < w1aF y4 2 (2 * hminus))
    (hE11 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      0 < w1aF y4 (2 * hminus) (2 * hminus)) :
    ∀ y4 y5 y6 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
      0 < w1aF y4 y5 y6 := by
  intro y4 y5 y6 h4 h4' h5 h5' h6 h6'
  have hhm : (2 : ℝ) ≤ 2 * hminus := by linarith [h4]
  have hE10 : 0 < w1aF y4 (2 * hminus) 2 := by
    have hs := nb21_w1aF_symm y4 (2 * hminus) 2 (by linarith [h4])
      (by linarith [h4]) (by norm_num)
    rw [hs]
    exact hE01 y4 h4 h4'
  exact w1aF_ge_edges y4 y5 y6 h4 h4' h5 h5' h6 h6'
    (fun a b ha ha' hb hb' => hP1 y4 a b h4 h4' ha ha' hb hb')
    ⟨hE00 y4 h4 h4', hE01 y4 h4 h4', hE10, hE11 y4 h4 h4'⟩

/-- **The bank from the tower certificates.**  Residual obligations:
`hP1` (`w1F2 ≤ 0` on the box, the P1 certificate layer) and the three
edge facts `hE00`/`hE01`/`hE11` (the 1D edge certificates). -/
theorem bank_QZECFICwt1_from_tower
    (hP1 : ∀ y4 y5 y6 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
      w1F2 y4 y5 y6 ≤ 0)
    (hE00 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 0 < w1aF y4 2 2)
    (hE01 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus → 0 < w1aF y4 2 (2 * hminus))
    (hE11 : ∀ y4 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      0 < w1aF y4 (2 * hminus) (2 * hminus)) :
    bank_QZECFICwt1 :=
  bank_QZECFICwt1_of_core
    (fun y4 y5 y6 h4 h4' h5 h5' h6 h6' _ =>
      w1aF_pos_core hP1 hE00 hE01 hE11 y4 y5 y6 h4 h4' h5 h5' h6 h6')

/-! ## 4. Axiom audit -/

#print axioms w1aF_concaveOn_y5
#print axioms w1aF_concaveOn_y6
#print axioms w1aF_ge_edges
#print axioms w1aF_pos_core
#print axioms bank_QZECFICwt1_from_tower

end Kepler.Text
