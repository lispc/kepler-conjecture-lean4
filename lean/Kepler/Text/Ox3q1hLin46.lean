/-/
Kepler.Text.Ox3q1hLin46 - lane `ox3q1h-nogate-w1`, Front 1.

The 46 LINEAR conjuncts of `ox3q1hP25` (indices 0,5,10,...,225;
HOL: ineqdata3q1h.hl records x branch tm0, merged by
merge_ineq.hl:78-92).  Statements are VERBATIM conjuncts of
`ox3q1hP25` (PackingAuto25.lean:94 sqq., DEF-FIX b85eaade);
generator: lane scripts/lin46_emit.py.

Proofs: pure `linarith` over the box polytope with the exact
rational brackets  hminus ∈ [1.23175, 1.23176]
(Kepler.NliBanks17.nb17_hminus_bounds, tree-proved)  and
π ∈ (3.14159265358979323846, 3.14159265358979323847)
(Mathlib `Real.pi_gt_d20` / `Real.pi_lt_d20`, 1e-20 width;
same bracket as the tree's g4v_pi_bounds), plus the constant
equations `h0 = 1.26` and `hplus = 1.3254` (rfl; needed because
16 conjuncts bound y1 via hplus-terms).
Exact-rational margin audit (lane lin46_verify.py, Fractions
over the same brackets):
* min margin 1.4155960853703958516e-7 at conjunct #100;
* all 46 strictly positive; cross-checked against
  g4feas-w1/OX3Q1H_MARGINS.tsv (max rel diff < 5e-6, float).

No `sorry`/`axiom`/`native_decide`; statements frozen verbatim.
Axiom audit at file end.
-/
import Kepler.Text.PackingAuto25
import Kepler.NliBanks17

namespace Kepler.Text

/-- ox3q1hP25 conjunct #0 (record 0, branch tm0; exact margin 35359418919101064689/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_000 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129913 + ((-0.060416) + 0.01764 + 0.045166 + 0.021777) * y1 + 2 * (0.002372 +
    (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 *
    ((-0.002372) + 0.002372) * y41 + ((-0.113134) + (-0.198777) + (-0.306092) + (-0.259166)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #5 (record 1, branch tm0; exact margin 180617205740676367947/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_005 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129699 + ((-0.060316) + 0.019214 + 0.021887 + 0.019214) * y1 + 2 * (0.002264 +
    (-0.002264)) * y12 + 2 * ((-0.002264) + 0.002264) * y23 + 2 * (0.002264 + (-0.002264)) * y34 + 2 *
    ((-0.002264) + 0.002264) * y41 + ((-0.112116) + (-0.203309) + (-0.29619) + (-0.203309)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #10 (record 2, branch tm0; exact margin 35359418919101064689/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_010 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129913 + ((-0.060416) + 0.021777 + 0.045166 + 0.01764) * y1 + 2 * (0.002372 +
    (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 *
    ((-0.002372) + 0.002372) * y41 + ((-0.113134) + (-0.259166) + (-0.306092) + (-0.198777)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #15 (record 3, branch tm0; exact margin 3070644792055552357/3125000000000000000000000 > 0). -/
theorem ox3q1hLin_015 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.114872) + (0.133539 + 0.148605 + 0.08743 + 0.148605) * y1 + 2 * ((-0.080919) +
    0.080919) * y12 + 2 * (0.080919 + (-0.080919)) * y23 + 2 * ((-0.080919) + 0.080919) * y34 + 2 *
    (0.080919 + (-0.080919)) * y41 + (0.532524 + (-0.855148) + 0.593722 + (-0.855148)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #20 (record 4, branch tm0; exact margin 73347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_020 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.008732) + 0.072591 + 0.042651 + 0.055356) * y1 + 2 * ((-0.024884) +
    0.024884) * y12 + 2 * (0.024884 + (-0.024884)) * y23 + 2 * ((-0.024884) + 0.024884) * y34 + 2 *
    (0.024884 + (-0.024884)) * y41 + (0.097156 + (-0.464803) + 0.008797 + (-0.458108)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #25 (record 5, branch tm0; exact margin 79347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_025 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.029778) + 0.072591 + 0.055356 + 0.072591) * y1 + 2 * ((-0.027449) +
    0.027449) * y12 + 2 * (0.027449 + (-0.027449)) * y23 + 2 * ((-0.027449) + 0.027449) * y34 + 2 *
    (0.027449 + (-0.027449)) * y41 + (0.170713 + (-0.485323) + (-0.039438) + (-0.485323)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #30 (record 6, branch tm0; exact margin 77347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_030 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.008732) + 0.055356 + 0.072591 + 0.037947) * y1 + 2 * (0.025458 +
    (-0.025458)) * y12 + 2 * ((-0.025458) + 0.025458) * y23 + 2 * (0.025458 + (-0.025458)) * y34 + 2 *
    ((-0.025458) + 0.025458) * y41 + ((-0.30558) + (-0.055371) + (-0.469389) + 0.025236) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #35 (record 7, branch tm0; exact margin 4320644791743052357/3125000000000000000000000 > 0). -/
theorem ox3q1hLin_035 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * hminus) ≤ y1 → y1 ≤ (2 * h0) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.114872) + (0.116669 + 0.08743 + 0.148605 + 0.08743) * y1 + 2 * (0.080919 +
    (-0.080919)) * y12 + 2 * ((-0.080919) + 0.080919) * y23 + 2 * (0.080919 + (-0.080919)) * y34 + 2 *
    ((-0.080919) + 0.080919) * y41 + ((-0.7251449999999999) + 0.595546 + (-0.853324) + 0.595546) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #40 (record 8, branch tm0; exact margin 27359418919101064689/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_040 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129913 + ((-0.09152) + 0.347659 + (-0.105208) + (-0.150931)) * y1 + 2 * (0.002372 +
    (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 *
    ((-0.002372) + 0.002372) * y41 + ((-0.034749) + (-1.030425) + 0.072849 + 0.176057) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #45 (record 9, branch tm0; exact margin 27359418919101064689/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_045 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129913 + (0.340765 + (-0.094917) + (-0.150931) + (-0.094917)) * y1 + 2 * (0.002372 +
    (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 *
    ((-0.002372) + 0.002372) * y41 + ((-1.124108) + 0.084866 + 0.138108 + 0.084866) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #50 (record 10, branch tm0; exact margin 27359418919101064689/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_050 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.129913 + ((-0.09152) + 0.291645 + (-0.105208) + (-0.094917)) * y1 + 2 * (0.002372 +
    (-0.002372)) * y12 + 2 * ((-0.002372) + 0.002372) * y23 + 2 * (0.002372 + (-0.002372)) * y34 + 2 *
    ((-0.002372) + 0.002372) * y41 + ((-0.034749) + (-0.939234) + 0.072849 + 0.084866) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #55 (record 11, branch tm0; exact margin 74722889501504858709/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_055 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.128506 + (0.290371 + (-0.070878) + (-0.097658) + (-0.121835)) * y1 + 2 * (0.003287 +
    (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 *
    ((-0.003287) + 0.003287) * y41 + ((-1.026581) + 0.033394 + 0.050047 + 0.13571) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #60 (record 12, branch tm0; exact margin 74722889501504858709/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_060 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.128506 + (0.263591 + (-0.070878) + (-0.121835) + (-0.070878)) * y1 + 2 * (0.003287 +
    (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 *
    ((-0.003287) + 0.003287) * y41 + ((-0.957343) + 0.033394 + 0.083125 + 0.033394) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #65 (record 13, branch tm0; exact margin 33452889501504858709/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_065 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.128506 + ((-0.066254) + 0.234791 + (-0.097658) + (-0.070878)) * y1 + 2 * (0.003287 +
    (-0.003287)) * y12 + 2 * ((-0.003287) + 0.003287) * y23 + 2 * (0.003287 + (-0.003287)) * y34 + 2 *
    ((-0.003287) + 0.003287) * y41 + ((-0.104563) + (-0.786309) + 0.050047 + 0.033394) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #70 (record 14, branch tm0; exact margin 20160680017651836199/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_070 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.127166 + ((-0.07331) + 0.23984 + (-0.096981) + (-0.069548)) * y1 + 2 * (0.003788 +
    (-0.003788)) * y12 + 2 * ((-0.003788) + 0.003788) * y23 + 2 * (0.003788 + (-0.003788)) * y34 + 2 *
    ((-0.003788) + 0.003788) * y41 + ((-0.105909) + (-0.767737) + 0.04248 + 0.032155) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #75 (record 15, branch tm0; exact margin 30815584678260648881/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_075 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * 0.126777 + ((-0.053069) + 0.196466 + (-0.093532) + (-0.049865)) * y1 +
    2 * (0.003525 + (-0.003525)) * y12 + 2 * ((-0.003525) + 0.003525) * y23 + 2 * (0.003525 +
    (-0.003525)) * y34 + 2 * ((-0.003525) + 0.003525) * y41 + ((-0.142652) + (-0.667227) + 0.035622 +
    (-0.022307)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #80 (record 16, branch tm0; exact margin 193201680651441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_080 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.014413) + (-0.02241)) * y1 +
    2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 +
    (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.594377 + (-0.377571) +
    0.608509) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #85 (record 17, branch tm0; exact margin 193201680651441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_085 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.02241) + (-0.014413)) * y1 +
    2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 +
    (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530636) + 0.594377 + (-0.36344) +
    0.594377) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #90 (record 18, branch tm0; exact margin 193201680651441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_090 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.02241) + (-0.014413) + (-0.014413)) * y1 +
    2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 +
    (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.608509 + (-0.377571) +
    0.594377) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #95 (record 19, branch tm0; exact margin 39551547668621773697/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_095 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) →
    (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) →
    (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.036939) + (0.050064 + (-0.016688) + (-0.016688) +
    (-0.016688)) * y1 + 2 * ((-0.057593) + 0.057593) * y12 + 2 * (0.057593 + (-0.057593)) * y23 + 2 *
    ((-0.057593) + (-0.057593)) * y34 + 2 * ((-0.057593) + (-0.057593)) * y41 + (0.397884 + (-0.362427)
    + 0.559062 + 0.559062) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #100 (record 20, branch tm0; exact margin 3538990213425989629/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_100 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.049823) + (0.047052 + (-0.015684) + (-0.015684) + (-0.015684)) * y1
    + 2 * ((-0.061687) + 0.061687) * y12 + 2 * (0.061687 + (-0.061687)) * y23 + 2 * ((-0.061687) +
    0.061687) * y34 + 2 * (0.061687 + (-0.061687)) * y41 + (0.463622 + (-0.379191) + 0.607807 +
    (-0.379191)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #105 (record 21, branch tm0; exact margin 49548491207532579093/12500000000000000000000000 > 0). -/
theorem ox3q1hLin_105 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.053582) + (0.049452 + (-0.013853) + (-0.020791) + (-0.013853)) * y1
    + 2 * ((-0.06302) + 0.06302) * y12 + 2 * (0.06302 + (-0.06302)) * y23 + 2 * ((-0.06302) +
    (-0.062897)) * y34 + 2 * ((-0.062897) + (-0.06302)) * y41 + (0.475514 + (-0.389234) + 0.637132 +
    0.618101) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #110 (record 22, branch tm0; exact margin 7642680328104163201/5000000000000000000000000 > 0). -/
theorem ox3q1hLin_110 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.066935) + (0.079693 + (-0.021495) + (-0.021495) + (-0.036704)) * y1 + 2 * (0.066241 +
    (-0.066241)) * y12 + 2 * ((-0.066241) + 0.066241) * y23 + 2 * (0.066241 + (-0.066241)) * y34 + 2 *
    ((-0.066241) + 0.066241) * y41 + ((-0.605497) + 0.685308 + (-0.374549) + 0.715304) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #115 (record 23, branch tm0; exact margin 7642680328104163201/5000000000000000000000000 > 0). -/
theorem ox3q1hLin_115 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.066935) + (0.028887 + (-0.021495) + 0.014102 + (-0.021495)) * y1 + 2 * (0.066241 +
    (-0.066241)) * y12 + 2 * ((-0.066241) + 0.066241) * y23 + 2 * (0.066241 + (-0.066241)) * y34 + 2 *
    ((-0.066241) + 0.066241) * y41 + ((-0.477466) + 0.685308 + (-0.472584) + 0.685308) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #120 (record 24, branch tm0; exact margin 7642680328104163201/5000000000000000000000000 > 0). -/
theorem ox3q1hLin_120 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.066935) + (0.028887 + 0.014102 + (-0.021495) + (-0.021495)) * y1 + 2 * ((-0.066241) +
    0.066241) * y12 + 2 * (0.066241 + (-0.066241)) * y23 + 2 * ((-0.066241) + 0.066241) * y34 + 2 *
    (0.066241 + (-0.066241)) * y41 + (0.582391 + (-0.472584) + 0.685308 + (-0.374549)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #125 (record 25, branch tm0; exact margin 111555311314997225763/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_125 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 2 + 1 * hplus / 2) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.070081) + (0.043025 + (-0.014342) + (-0.014342) + (-0.014342)) * y1
    + 2 * (0.06775 + (-0.06775)) * y12 + 2 * ((-0.06775) + 0.06775) * y23 + 2 * (0.06775 + (-0.06775)) *
    y34 + 2 * ((-0.06775) + 0.06775) * y41 + ((-0.520998) + 0.681778 + (-0.402228) + 0.681778) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #130 (record 26, branch tm0; exact margin 39611941557041680029/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_130 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 *
    hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 *
    hminus) → 2 * Real.pi * (-0.074623) + (0.079355 + (-0.023711) + (-0.023711) + (-0.031932)) * y1 + 2
    * (0.068595 + (-0.068595)) * y12 + 2 * ((-0.068595) + 0.068595) * y23 + 2 * (0.068595 + (-0.068595))
    * y34 + 2 * ((-0.068595) + 0.068595) * y41 + ((-0.608613) + 0.719631 + (-0.37789) + 0.735738) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #135 (record 27, branch tm0; exact margin 14611941557041680029/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_135 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 *
    hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 *
    hminus) → 2 * Real.pi * (-0.074623) + (0.019702 + (-0.023711) + (-0.031932) + 0.035942) * y1 + 2 *
    ((-0.081204) + 0.081204) * y12 + 2 * (0.081204 + (-0.081204)) * y23 + 2 * ((-0.081204) + 0.081204) *
    y34 + 2 * (0.081204 + (-0.081204)) * y41 + (0.740105 + (-0.47876) + 0.836608 + (-0.629086)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #140 (record 28, branch tm0; exact margin 14611941557041680029/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_140 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 *
    hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 *
    hminus) → 2 * Real.pi * (-0.074623) + (0.019702 + (-0.031932) + (-0.023711) + 0.035942) * y1 + 2 *
    ((-0.068595) + 0.068595) * y12 + 2 * (0.068595 + (-0.068595)) * y23 + 2 * ((-0.068595) + 0.068595) *
    y34 + 2 * (0.068595 + (-0.068595)) * y41 + (0.639237 + (-0.361784) + 0.719631 + (-0.528217)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #145 (record 29, branch tm0; exact margin 19066598184980027307/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_145 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (7 * h0 / 4 + 1 * hplus / 4) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) →
    (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) →
    (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.090009) + (0.04151 + (-0.013837) + (-0.013837) +
    (-0.013837)) * y1 + 2 * (0.073665 + (-0.073665)) * y12 + 2 * ((-0.073665) + 0.073665) * y23 + 2 *
    (0.073665 + (-0.073665)) * y34 + 2 * ((-0.073665) + 0.073665) * y41 + ((-0.523458) + 0.755879 +
    (-0.422755) + 0.755879) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #150 (record 30, branch tm0; exact margin 202874732459769563/100000000000000000000000 > 0). -/
theorem ox3q1hLin_150 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (7 * h0 / 4 + 1 * hplus / 4) → (2) ≤ y12 → y12 ≤ (2 *
    hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 *
    hminus) → 2 * Real.pi * (-0.17025) + (0.094709 + (-0.021455) + 0.009749 + (-0.021455)) * y1 + 2 *
    (0.098535 + (-0.098535)) * y12 + 2 * ((-0.098535) + 0.098535) * y23 + 2 * (0.098535 + (-0.098535)) *
    y34 + 2 * ((-0.098535) + 0.098535) * y41 + ((-0.692034) + 1.087114 + (-0.568591) + 1.087114) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #155 (record 31, branch tm0; exact margin 8763698508567317609/12500000000000000000000000 > 0). -/
theorem ox3q1hLin_155 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (3 * h0 / 2 + 1 * hplus / 2) → (2) ≤ y12 → y12 ≤ (2 *
    hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 *
    hminus) → 2 * Real.pi * (-0.172166) + (0.09973 + 0.014169 + (-0.017353) + 0.014169) * y1 + 2 *
    ((-0.099785) + 0.099785) * y12 + 2 * (0.099785 + (-0.099785)) * y23 + 2 * ((-0.099785) + 0.099785) *
    y34 + 2 * (0.099785 + (-0.099785)) * y41 + (0.882284 + (-0.586728) + 1.0903 + (-0.586728)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #160 (record 32, branch tm0; exact margin 187975261248944789247/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_160 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.084789) + (0.039845 + (-0.013282) + (-0.013282) + (-0.013282)) * y1 + 2 * ((-0.071708)
    + (-0.071708)) * y12 + 2 * ((-0.071708) + (-0.071708)) * y23 + 2 * ((-0.071708) + 0.071708) * y34 +
    2 * (0.071708 + (-0.071708)) * y41 + (0.632521 + 0.731624 + 0.731624 + (-0.415701)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #165 (record 33, branch tm0; exact margin 39347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_165 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.052337) + 0.23854 + (-0.073933) + (-0.11227)) * y1 + 2 * ((-0.02292) +
    0.02292) * y12 + 2 * (0.02292 + (-0.02292)) * y23 + 2 * ((-0.02292) + 0.02292) * y34 + 2 * (0.02292
    + (-0.02292)) * y41 + (0.191326 + (-0.867278) + 0.286871 + (-0.019974)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #170 (record 34, branch tm0; exact margin 39347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_170 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.052337) + 0.23854 + (-0.11227) + (-0.073933)) * y1 + 2 * (0.02292 +
    (-0.02292)) * y12 + 2 * ((-0.02292) + 0.02292) * y23 + 2 * (0.02292 + (-0.02292)) * y34 + 2 *
    ((-0.02292) + 0.02292) * y41 + ((-0.17539) + (-0.500562) + (-0.019974) + 0.286871) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #175 (record 35, branch tm0; exact margin 39347334369079588759/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_175 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * 0.065103 + ((-0.052337) + (-0.11227) + 0.23854 + (-0.073933)) * y1 + 2 * (0.02292 +
    (-0.02292)) * y12 + 2 * ((-0.02292) + 0.02292) * y23 + 2 * (0.02292 + (-0.02292)) * y34 + 2 *
    ((-0.02292) + 0.02292) * y41 + ((-0.175391) + 0.346743 + (-0.867278) + 0.286871) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #180 (record 36, branch tm0; exact margin 33088033817001946193/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_180 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.062681 + ((-0.026929) + (-0.06441) + 0.176245 + (-0.084906)) * y1 + 2 * (0.023742 +
    (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 *
    ((-0.023742) + 0.023742) * y41 + ((-0.242815) + 0.273568 + (-0.72849) + 0.3039) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #185 (record 37, branch tm0; exact margin 33088033817001946193/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_185 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.062681 + ((-0.026929) + 0.176245 + (-0.084906) + (-0.06441)) * y1 + 2 * (0.023742 +
    (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 *
    ((-0.023742) + 0.023742) * y41 + ((-0.242815) + (-0.348621) + (-0.075969) + 0.273568) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #190 (record 38, branch tm0; exact margin 33088033817001946193/50000000000000000000000000 > 0). -/
theorem ox3q1hLin_190 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) →
    (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2
    * Real.pi * 0.062681 + ((-0.026929) + (-0.084906) + 0.176245 + (-0.06441)) * y1 + 2 * (0.023742 +
    (-0.023742)) * y12 + 2 * ((-0.023742) + 0.023742) * y23 + 2 * (0.023742 + (-0.023742)) * y34 + 2 *
    ((-0.023742) + 0.023742) * y41 + ((-0.242815) + 0.3039 + (-0.72849) + 0.273568) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #195 (record 39, branch tm0; exact margin 37548817975004053121/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_195 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (1 * h0 / 2 + 3 * hplus / 2) ≤ y1 → y1 ≤ (2 * hplus) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * 0.061714 + ((-0.014502) + 0.134266 + (-0.059882) + (-0.059882)) * y1 +
    2 * ((-0.02407) + 0.02407) * y12 + 2 * (0.02407 + (-0.02407)) * y23 + 2 * ((-0.02407) + (-0.02407))
    * y34 + 2 * ((-0.02407) + (-0.02407)) * y41 + (0.104941 + (-0.631477) + 0.261947 + 0.261947) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #200 (record 40, branch tm0; exact margin 193201680651441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_200 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.014413) + (-0.02241)) * y1 +
    2 * (0.060747 + (-0.060747)) * y12 + 2 * ((-0.060747) + 0.060747) * y23 + 2 * (0.060747 +
    (-0.060747)) * y34 + 2 * ((-0.060747) + 0.060747) * y41 + ((-0.530637) + 0.594377 + (-0.377571) +
    0.608509) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #205 (record 41, branch tm0; exact margin 193201680651441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_205 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.014413) + (-0.02241) + (-0.014413)) * y1 +
    2 * ((-0.073427) + 0.073427) * y12 + 2 * (0.073427 + (-0.073427)) * y23 + 2 * ((-0.073427) +
    0.073427) * y34 + 2 * (0.073427 + (-0.073427)) * y41 + (0.542756 + (-0.479016) + 0.709954 +
    (-0.479016)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #210 (record 42, branch tm0; exact margin 193201680641441887/250000000000000000000000 > 0). -/
theorem ox3q1hLin_210 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.0469) + (0.051237 + (-0.02241) + (-0.014413) + (-0.014413)) * y1 +
    2 * ((-0.060747) + 0.060747) * y12 + 2 * (0.060747 + (-0.060747)) * y23 + 2 * ((-0.060747) +
    0.060747) * y34 + 2 * (0.060747 + (-0.060747)) * y41 + (0.44131200000000004 + (-0.36344) + 0.594377
    + (-0.377571)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #215 (record 43, branch tm0; exact margin 39551547668621773697/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_215 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (3 * h0 / 4 + 5 * hplus / 4) ≤ y1 → y1 ≤ (1 * h0 / 2 + 3 * hplus / 2) →
    (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) →
    (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 * Real.pi * (-0.036939) + (0.050064 + (-0.016688) + (-0.016688) +
    (-0.016688)) * y1 + 2 * (0.057593 + (-0.057593)) * y12 + 2 * ((-0.057593) + 0.057593) * y23 + 2 *
    (0.057593 + (-0.057593)) * y34 + 2 * ((-0.057593) + 0.057593) * y41 + ((-0.523604) + 0.559062 +
    (-0.362427) + 0.559062) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #220 (record 44, branch tm0; exact margin 9351201639232269967/5000000000000000000000000 > 0). -/
theorem ox3q1hLin_220 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (h0 + hplus) ≤ y1 → y1 ≤ (3 * h0 / 4 + 5 * hplus / 4) → (2) ≤ y12 → y12 ≤
    (2 * hminus) → (2) ≤ y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤
    (2 * hminus) → 2 * Real.pi * (-0.177145) + (0.151334 + 0.041584 + 0.00995 + 0.041584) * y1 + 2 *
    ((-0.103308) + 0.103308) * y12 + 2 * (0.103308 + (-0.103308)) * y23 + 2 * ((-0.103308) + 0.103308) *
    y34 + 2 * (0.103308 + (-0.103308)) * y41 + (0.774954 + (-0.677721) + 1.057518 + (-0.677721)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-- ox3q1hP25 conjunct #225 (record 45, branch tm0; exact margin 39959794672638786447/25000000000000000000000000 > 0). -/
theorem ox3q1hLin_225 :
    ∀ y1 y12 y23 y34 y41 : ℝ, (2 * h0) ≤ y1 → y1 ≤ (h0 + hplus) → (2) ≤ y12 → y12 ≤ (2 * hminus) → (2) ≤
    y23 → y23 ≤ (2 * hminus) → (2) ≤ y34 → y34 ≤ (2 * hminus) → (2) ≤ y41 → y41 ≤ (2 * hminus) → 2 *
    Real.pi * (-0.121189) + (0.06473 + (-0.016252) + (-0.022099) + (-0.016252)) * y1 + 2 * ((-0.084657)
    + 0.084657) * y12 + 2 * (0.084657 + (-0.084657)) * y23 + 2 * ((-0.084657) + 0.084657) * y34 + 2 *
    (0.084657 + (-0.084657)) * y41 + (0.741383 + (-0.45858) + 0.911046 + (-0.45858)) < 0
    := by
  intro y1 y12 y23 y34 y41 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hmn := Kepler.NliBanks17.nb17_hminus_bounds
  have hcon : h0 = (1.26:Real) /\ hplus = (1.3254:Real) :=
    ⟨rfl, rfl⟩
  have hp : (3.14159265358979323846 : Real) < Real.pi /\
      Real.pi < (3.14159265358979323847 : Real) :=
    ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
  linarith [hmn.1, hmn.2, hcon.1, hcon.2, hp.1, hp.2]

/-! ## Axiom audit -/

#print axioms ox3q1hLin_000
#print axioms ox3q1hLin_005
#print axioms ox3q1hLin_010
#print axioms ox3q1hLin_015
#print axioms ox3q1hLin_020
#print axioms ox3q1hLin_025
#print axioms ox3q1hLin_030
#print axioms ox3q1hLin_035
#print axioms ox3q1hLin_040
#print axioms ox3q1hLin_045
#print axioms ox3q1hLin_050
#print axioms ox3q1hLin_055
#print axioms ox3q1hLin_060
#print axioms ox3q1hLin_065
#print axioms ox3q1hLin_070
#print axioms ox3q1hLin_075
#print axioms ox3q1hLin_080
#print axioms ox3q1hLin_085
#print axioms ox3q1hLin_090
#print axioms ox3q1hLin_095
#print axioms ox3q1hLin_100
#print axioms ox3q1hLin_105
#print axioms ox3q1hLin_110
#print axioms ox3q1hLin_115
#print axioms ox3q1hLin_120
#print axioms ox3q1hLin_125
#print axioms ox3q1hLin_130
#print axioms ox3q1hLin_135
#print axioms ox3q1hLin_140
#print axioms ox3q1hLin_145
#print axioms ox3q1hLin_150
#print axioms ox3q1hLin_155
#print axioms ox3q1hLin_160
#print axioms ox3q1hLin_165
#print axioms ox3q1hLin_170
#print axioms ox3q1hLin_175
#print axioms ox3q1hLin_180
#print axioms ox3q1hLin_185
#print axioms ox3q1hLin_190
#print axioms ox3q1hLin_195
#print axioms ox3q1hLin_200
#print axioms ox3q1hLin_205
#print axioms ox3q1hLin_210
#print axioms ox3q1hLin_215
#print axioms ox3q1hLin_220
#print axioms ox3q1hLin_225

end Kepler.Text
