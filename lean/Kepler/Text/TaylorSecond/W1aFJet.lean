/-
Kepler.Text.TaylorSecond.W1aFJet — lane `wt1-emission-pilot-w1` (2026-11-25).

Generic (box-independent) half of the wt1 *Taylor* certificate emission:

  §1 the rational box `w1Box3`, its centre / half-width, convexity;
  §2 coordinate and constant jets;
  §3 the whole slot tree of `w1aF` as `WholeBoxJet` combinators, in the parse
     shape of the landed `Wt1TowerDeriv` slots (the tree of
     `wt1-taylor-model-w1/scripts/wtspec.py`);
  §4 the slot-identification lemmas (`fDlt x = w1Dlt …`, `fA x = w1aA …`, …);
  §5 the identity `w1F3 = w1F3Z` on `{2 h0 ≤ y4, 0 ≤ y4, 0 < y5, 0 ≤ y6}` (the
     `h0cut` branch is exactly `0` there, so the smoothed `pq1` term drops);
  §6 the generic Taylor terminal.

Per-box inputs are only: the three box intervals, the four real-constant
brackets (√2, π, mm1, mm2), the nine `invUnaryBox`es of the positive slot
denominators, and the six `matan` `UnaryBox`es — everything else is derived
here from the variable projections.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Mathlib.Algebra.Order.Floor.Defs
import Kepler.Text.TaylorSecond.InvSqrt
import Kepler.Text.TaylorSecond.Taylor3
import Kepler.Text.TaylorSecond.LeafKitPrec
import Kepler.Text.TaylorSecond.LeafGenKit
import Kepler.Text.TaylorSecond.Wt1C2
import Kepler.NliBanks21

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TaylorSecond

noncomputable section

open Kepler.Text
open Kepler.NliBanks21

/-! ## 1. The box, centre and half-width -/

/-- A closed box given by three exact rational intervals. -/
def w1Box3 (I4 I5 I6 : QInterval) : Set (Fin 3 → ℝ) :=
  {x | I4.mem (x 0) ∧ I5.mem (x 1) ∧ I6.mem (x 2)}

/-- The leaf data of one box: the three coordinate intervals, the four real
constant brackets, and their soundness. -/
structure W1Leaf where
  I4 : QInterval
  I5 : QInterval
  I6 : QInterval
  h4 : I4.lo ≤ I4.hi
  h5 : I5.lo ≤ I5.hi
  h6 : I6.lo ≤ I6.hi
  sI : QInterval
  piI : QInterval
  mm1I : QInterval
  mm2I : QInterval
  hsI : sI.mem (Real.sqrt 2)
  hpi : piI.mem Real.pi
  hmm1 : mm1I.mem mm1
  hmm2 : mm2I.mem mm2
  hpi0 : 0 < piI.lo

namespace W1Leaf

theorem mem_iff {L : W1Leaf} {x : Fin 3 → ℝ} :
    x ∈ w1Box3 L.I4 L.I5 L.I6 ↔ L.I4.mem (x 0) ∧ L.I5.mem (x 1) ∧ L.I6.mem (x 2) :=
  Iff.rfl

/-- Componentwise centre. -/
def c (L : W1Leaf) : Fin 3 → ℝ :=
  ![(((L.I4.lo + L.I4.hi) / 2 : ℚ) : ℝ), (((L.I5.lo + L.I5.hi) / 2 : ℚ) : ℝ),
    (((L.I6.lo + L.I6.hi) / 2 : ℚ) : ℝ)]

/-- Componentwise half-width. -/
def w (L : W1Leaf) : Fin 3 → ℝ :=
  ![(((L.I4.hi - L.I4.lo) / 2 : ℚ) : ℝ), (((L.I5.hi - L.I5.lo) / 2 : ℚ) : ℝ),
    (((L.I6.hi - L.I6.lo) / 2 : ℚ) : ℝ)]

theorem h4R (L : W1Leaf) : (L.I4.lo : ℝ) ≤ L.I4.hi := by exact_mod_cast L.h4
theorem h5R (L : W1Leaf) : (L.I5.lo : ℝ) ≤ L.I5.hi := by exact_mod_cast L.h5
theorem h6R (L : W1Leaf) : (L.I6.lo : ℝ) ≤ L.I6.hi := by exact_mod_cast L.h6

theorem c_mem (L : W1Leaf) : L.c ∈ w1Box3 L.I4 L.I5 L.I6 := by
  have h4 := L.h4R; have h5 := L.h5R; have h6 := L.h6R
  refine ⟨?_, ?_, ?_⟩
  · change (L.I4.lo : ℝ) ≤ L.c 0 ∧ L.c 0 ≤ (L.I4.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    constructor <;> linarith
  · change (L.I5.lo : ℝ) ≤ L.c 1 ∧ L.c 1 ≤ (L.I5.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    constructor <;> linarith
  · change (L.I6.lo : ℝ) ≤ L.c 2 ∧ L.c 2 ≤ (L.I6.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one, Rat.cast_div,
      Rat.cast_add, Rat.cast_ofNat]
    constructor <;> linarith

theorem seg_mem (L : W1Leaf) {x : Fin 3 → ℝ} (hx : x ∈ w1Box3 L.I4 L.I5 L.I6)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun i => L.c i + t * (x i - L.c i)) ∈ w1Box3 L.I4 L.I5 L.I6 := by
  have h4 := L.h4R; have h5 := L.h5R; have h6 := L.h6R
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨ht0, ht1⟩ := ht
  simp only [QInterval.mem] at hx0 hx1 hx2
  refine ⟨?_, ?_, ?_⟩
  · change (L.I4.lo : ℝ) ≤ L.c 0 + t * (x 0 - L.c 0) ∧
      L.c 0 + t * (x 0 - L.c 0) ≤ (L.I4.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    constructor <;> nlinarith
  · change (L.I5.lo : ℝ) ≤ L.c 1 + t * (x 1 - L.c 1) ∧
      L.c 1 + t * (x 1 - L.c 1) ≤ (L.I5.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    constructor <;> nlinarith
  · change (L.I6.lo : ℝ) ≤ L.c 2 + t * (x 2 - L.c 2) ∧
      L.c 2 + t * (x 2 - L.c 2) ≤ (L.I6.hi : ℝ)
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one, Rat.cast_div,
      Rat.cast_add, Rat.cast_ofNat]
    constructor <;> nlinarith

theorem w_abs (L : W1Leaf) {x : Fin 3 → ℝ} (hx : x ∈ w1Box3 L.I4 L.I5 L.I6) (i : Fin 3) :
    |x i - L.c i| ≤ L.w i := by
  have h4 := L.h4R; have h5 := L.h5R; have h6 := L.h6R
  obtain ⟨hx0, hx1, hx2⟩ := hx
  simp only [QInterval.mem] at hx0 hx1 hx2
  fin_cases i
  · change |x 0 - L.c 0| ≤ L.w 0
    simp only [c, w, Matrix.cons_val_zero, Rat.cast_div, Rat.cast_add, Rat.cast_sub,
      Rat.cast_ofNat]
    rw [abs_le]; constructor <;> linarith
  · change |x 1 - L.c 1| ≤ L.w 1
    simp only [c, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Rat.cast_div, Rat.cast_add, Rat.cast_sub,
      Rat.cast_ofNat]
    rw [abs_le]; constructor <;> linarith
  · change |x 2 - L.c 2| ≤ L.w 2
    simp only [c, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_fin_one, Rat.cast_div,
      Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
    rw [abs_le]; constructor <;> linarith

end W1Leaf

/-! ## 2. Coordinate and constant jets -/

/-- Coordinate partial of a projection. -/
theorem partial1_coord (i j : Fin 3) (x : Fin 3 → ℝ) :
    partial1 j (fun y : Fin 3 → ℝ => y i) x = if j = i then 1 else 0 := by
  have hC2 : ContDiffAt ℝ 1 (fun y : Fin 3 → ℝ => y i) x := by fun_prop
  rw [partial1_eq_deriv_update hC2 j]
  by_cases h : j = i
  · have hfun : (fun t : ℝ => (Function.update x j t) i) = fun t => t := by
      funext t
      rw [Function.update_apply, if_pos h.symm]
    rw [hfun, if_pos h]
    simp
  · have hfun : (fun t : ℝ => (Function.update x j t) i) = fun _ => x i := by
      funext t
      rw [Function.update_of_ne (Ne.symm h)]
    rw [hfun, if_neg h]
    simp

/-- Mixed second partial of a projection vanishes. -/
theorem partial2_coord (i j k : Fin 3) (x : Fin 3 → ℝ) :
    partial2 j k (fun y : Fin 3 → ℝ => y i) x = 0 := by
  have hC2 : ContDiffAt ℝ 2 (fun y : Fin 3 → ℝ => y i) x := by fun_prop
  rw [partial2_eq_deriv_update hC2 j k]
  have hconst : (fun t : ℝ => partial1 k (fun y : Fin 3 → ℝ => y i) (Function.update x j t))
      = fun _ => (if k = i then (1 : ℝ) else 0) := by
    funext t
    exact partial1_coord i k (Function.update x j t)
  rw [hconst]
  simp

/-- Coordinate jet. -/
def coordJet (i : Fin 3) (I : QInterval) (D : Set (Fin 3 → ℝ))
    (hmem : ∀ x ∈ D, I.mem (x i)) : WholeBoxJet (fun x : Fin 3 → ℝ => x i) D where
  value := I
  first := fun j => if j = i then QInterval.const 1 else QInterval.const 0
  second := fun _ _ => QInterval.const 0
  diff2c := fun _ _ => by fun_prop
  value_mem := hmem
  first_mem := by
    intro x hx j
    rw [partial1_coord i j x]
    by_cases h : j = i
    · simp only [if_pos h]
      simpa using QInterval.mem_const (q := 1)
    · simp only [if_neg h]
      simpa using QInterval.mem_const (q := 0)
  second_mem := by
    intro x hx i' j hij
    rw [partial2_coord i j i' x]
    show (QInterval.const 0).mem (0 : ℝ)
    simpa using QInterval.mem_const (q := 0)

/-- Constant jet for a real value with a rational enclosure. -/
def constJet (c : ℝ) (V : QInterval) (hmem : V.mem c) (D : Set (Fin 3 → ℝ)) :
    WholeBoxJet (fun _ : Fin 3 → ℝ => c) D where
  value := V
  first := fun _ => QInterval.const 0
  second := fun _ _ => QInterval.const 0
  diff2c := fun _ _ => contDiffAt_const
  value_mem := fun _ _ => hmem
  first_mem := by
    intro x hx i
    rw [show partial1 i (fun _ : Fin 3 → ℝ => c) x = 0 by simp [partial1]]
    show (QInterval.const 0).mem (0 : ℝ)
    simpa using QInterval.mem_const (q := 0)
  second_mem := by
    intro x hx i j hij
    rw [show partial2 j i (fun _ : Fin 3 → ℝ => c) x = 0 by simp [partial2, partial1]]
    show (QInterval.const 0).mem (0 : ℝ)
    simpa using QInterval.mem_const (q := 0)

/-- Rational constant jet (`q` written as a real numeral). -/
def ratJet (c : ℝ) (q : ℚ) (h : c = (q : ℝ)) (D : Set (Fin 3 → ℝ)) :
    WholeBoxJet (fun _ : Fin 3 → ℝ => c) D :=
  constJet c (QInterval.const q) (h ▸ QInterval.mem_const) D

/-! ## 2.5 The 1e-9 outward layout

Exact-rational interval arithmetic makes the endpoints grow to 10^3–10^4 digits
by the top of the tree, which no `norm_num` evaluation survives.  Rounding every
*jet node* outward to the absolute grid `1e-9` keeps all endpoints <= ~20 digits
(so each node certificate is a 10–30 ms `norm_num`) and is sound (the brackets
only widen; total loss ~2e-8 against a ~4e-5 margin).  This is also the shape of
HOL's own certificate (`m_taylor.hl:741` `eval_m_taylor` `pp` recompute,
`:1179` `eval_m_taylor_bounds0`).

The **box endpoints stay exact** — the tiling and the `2 h0 ≤ y4` branch depend
on them. -/

/-- 1e-9 grid. -/
def g9 : ℚ := 10 ^ 9

/-- Outward rounding of an interval to the 1e-9 grid. -/
def rndOut (I : QInterval) : QInterval :=
  QInterval.mk (⌊I.lo * g9⌋ / g9) (⌈I.hi * g9⌉ / g9)

theorem rndOut_lo_le (I : QInterval) : (rndOut I).lo ≤ I.lo := by
  unfold rndOut
  have h : ((⌊I.lo * g9⌋ : ℤ) : ℚ) ≤ I.lo * g9 := Int.floor_le _
  have hg : (0:ℚ) < g9 := by norm_num [g9]
  exact (div_le_iff₀ hg).mpr h

theorem le_rndOut_hi (I : QInterval) : I.hi ≤ (rndOut I).hi := by
  unfold rndOut
  have h : I.hi * g9 ≤ ((⌈I.hi * g9⌉ : ℤ) : ℚ) := Int.le_ceil _
  have hg : (0:ℚ) < g9 := by norm_num [g9]
  exact (le_div_iff₀ hg).mpr h

theorem mem_rndOut {I : QInterval} {x : ℝ} (h : I.mem x) : (rndOut I).mem x := by
  have h1 : ((rndOut I).lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast rndOut_lo_le I
  have h2 : (I.hi : ℝ) ≤ ((rndOut I).hi : ℝ) := by exact_mod_cast le_rndOut_hi I
  exact ⟨le_trans h1 h.1, le_trans h.2 h2⟩

/-- Round every channel of a jet outward to the 1e-9 grid. -/
def roundJet (J : WholeBoxJet f D) : WholeBoxJet f D where
  value := rndOut J.value
  first := fun i => rndOut (J.first i)
  second := fun i j => rndOut (J.second i j)
  diff2c := J.diff2c
  value_mem := fun x hx => mem_rndOut (J.value_mem x hx)
  first_mem := fun x hx i => mem_rndOut (J.first_mem x hx i)
  second_mem := fun x hx i j h => mem_rndOut (J.second_mem x hx i j h)

#print axioms mem_rndOut
#print axioms roundJet

/-! ## 3. The slot tree of `w1aF` -/

/-- Coordinate projection. -/
def fY4 : (Fin 3 → ℝ) → ℝ := fun x => x 0
def fY5 : (Fin 3 → ℝ) → ℝ := fun x => x 1
def fY6 : (Fin 3 → ℝ) → ℝ := fun x => x 2
def fSI : (Fin 3 → ℝ) → ℝ := fun _ => Real.sqrt 2
def fPI : (Fin 3 → ℝ) → ℝ := fun _ => Real.pi
def fMM1 : (Fin 3 → ℝ) → ℝ := fun _ => mm1
def fMM2 : (Fin 3 → ℝ) → ℝ := fun _ => mm2
def fC2 : (Fin 3 → ℝ) → ℝ := fun _ => (2 : ℝ)
def fC4 : (Fin 3 → ℝ) → ℝ := fun _ => (4 : ℝ)
def fC8 : (Fin 3 → ℝ) → ℝ := fun _ => (8 : ℝ)
def fCN2 : (Fin 3 → ℝ) → ℝ := fun _ => (-2 : ℝ)
def fCH : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 2 : ℝ)
def fCH0 : (Fin 3 → ℝ) → ℝ := fun _ => (63 / 50 : ℝ)
def fCH0i : (Fin 3 → ℝ) → ℝ := fun _ => (50 / 13 : ℝ)
def fC008 : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 125 : ℝ)
def fC112 : (Fin 3 → ℝ) → ℝ := fun _ => (1 / 12 : ℝ)

def fX4 : (Fin 3 → ℝ) → ℝ := fun x => fY4 x * fY4 x
def fX5 : (Fin 3 → ℝ) → ℝ := fun x => fY5 x * fY5 x
def fX6 : (Fin 3 → ℝ) → ℝ := fun x => fY6 x * fY6 x
def fS2 : (Fin 3 → ℝ) → ℝ := fun x => (fX4 x * fX4 x + fX5 x * fX5 x) + fX6 x * fX6 x
def fS1 : (Fin 3 → ℝ) → ℝ := fun x => (fX4 x * fX5 x + fX4 x * fX6 x) + fX5 x * fX6 x
def fDlt : (Fin 3 → ℝ) → ℝ :=
  fun x => (fCN2 x * fS2 x + fC4 x * fS1 x) - (fX4 x * fX5 x) * fX6 x
def fA : (Fin 3 → ℝ) → ℝ := fun x =>
  ((((fSI x * fY5 x) * fY4 x + (fY5 x * (fY4 x * fY4 x)) * fCH x) +
      (fSI x * ((fY5 x * fY5 x + fY4 x * fY4 x) - fY6 x * fY6 x)) * fCH x) +
    (fY4 x * (fY5 x * fY5 x)) * fCH x)
def fB : (Fin 3 → ℝ) → ℝ := fun x =>
  ((((fSI x * fY6 x) * fY5 x + (fY6 x * (fY5 x * fY5 x)) * fCH x) +
      (fSI x * ((fY6 x * fY6 x + fY5 x * fY5 x) - fY4 x * fY4 x)) * fCH x) +
    (fY5 x * (fY6 x * fY6 x)) * fCH x)
def fC : (Fin 3 → ℝ) → ℝ := fun x =>
  ((((fSI x * fY4 x) * fY6 x + (fY4 x * (fY6 x * fY6 x)) * fCH x) +
      (fSI x * ((fY4 x * fY4 x + fY6 x * fY6 x) - fY5 x * fY5 x)) * fCH x) +
    (fY6 x * (fY4 x * fY4 x)) * fCH x)
def fD4A : (Fin 3 → ℝ) → ℝ := fun x =>
  (fY5 x * fY5 x) * ((fY4 x * fY4 x + fY6 x * fY6 x) - fY5 x * fY5 x)
def fD4B : (Fin 3 → ℝ) → ℝ := fun x =>
  (fY6 x * fY6 x) * ((fY5 x * fY5 x + fY4 x * fY4 x) - fY6 x * fY6 x)
def fD4C : (Fin 3 → ℝ) → ℝ := fun x =>
  (fY4 x * fY4 x) * ((fY6 x * fY6 x + fY5 x * fY5 x) - fY4 x * fY4 x)
def fKA : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fY5 x * fY5 x)
def fKB : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fY6 x * fY6 x)
def fKC : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fY4 x * fY4 x)
def fNA : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY5 x
def fNB : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY6 x
def fNC : (Fin 3 → ℝ) → ℝ := fun x => fC2 x * fY4 x
def fLf4 : (Fin 3 → ℝ) → ℝ := fun x => (fCH0 x - fY4 x * fCH x) * fCH0i x
def fLf5 : (Fin 3 → ℝ) → ℝ := fun x => (fCH0 x - fY5 x * fCH x) * fCH0i x
def fLf6 : (Fin 3 → ℝ) → ℝ := fun x => (fCH0 x - fY6 x * fCH x) * fCH0i x
def fINVPI : (Fin 3 → ℝ) → ℝ := fun x => (fPI x)⁻¹
def fK1 : (Fin 3 → ℝ) → ℝ := fun x => (fC2 x * fMM1 x) * fINVPI x
def fK2 : (Fin 3 → ℝ) → ℝ := fun x => (fC8 x * fMM2 x) * fINVPI x
def f4a2A : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fA x * fA x)
def f4a2B : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fB x * fB x)
def f4a2C : (Fin 3 → ℝ) → ℝ := fun x => fC4 x * (fC x * fC x)
def fA2A : (Fin 3 → ℝ) → ℝ := fun x => fD4A x * fD4A x
def fA2B : (Fin 3 → ℝ) → ℝ := fun x => fD4B x * fD4B x
def fA2C : (Fin 3 → ℝ) → ℝ := fun x => fD4C x * fD4C x
def fT4A : (Fin 3 → ℝ) → ℝ := fun x => (f4a2A x)⁻¹
def fT4B : (Fin 3 → ℝ) → ℝ := fun x => (f4a2B x)⁻¹
def fT4C : (Fin 3 → ℝ) → ℝ := fun x => (f4a2C x)⁻¹
def fTA : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4A x
def fTB : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4B x
def fTC : (Fin 3 → ℝ) → ℝ := fun x => fDlt x * fT4C x
def fInvA2A : (Fin 3 → ℝ) → ℝ := fun x => (fA2A x)⁻¹
def fInvA2B : (Fin 3 → ℝ) → ℝ := fun x => (fA2B x)⁻¹
def fInvA2C : (Fin 3 → ℝ) → ℝ := fun x => (fA2C x)⁻¹
def fGA : (Fin 3 → ℝ) → ℝ := fun x => (fKA x * fDlt x) * fInvA2A x
def fGB : (Fin 3 → ℝ) → ℝ := fun x => (fKB x * fDlt x) * fInvA2B x
def fGC : (Fin 3 → ℝ) → ℝ := fun x => (fKC x * fDlt x) * fInvA2C x
def fInvD4A : (Fin 3 → ℝ) → ℝ := fun x => (fD4A x)⁻¹
def fInvD4B : (Fin 3 → ℝ) → ℝ := fun x => (fD4B x)⁻¹
def fInvD4C : (Fin 3 → ℝ) → ℝ := fun x => (fD4C x)⁻¹
def fIA : (Fin 3 → ℝ) → ℝ := fun x => (fA x)⁻¹
def fIB : (Fin 3 → ℝ) → ℝ := fun x => (fB x)⁻¹
def fIC : (Fin 3 → ℝ) → ℝ := fun x => (fC x)⁻¹
def fWA : (Fin 3 → ℝ) → ℝ := fun x => fNA x * fInvD4A x
def fWB : (Fin 3 → ℝ) → ℝ := fun x => fNB x * fInvD4B x
def fWC : (Fin 3 → ℝ) → ℝ := fun x => fNC x * fInvD4C x
def fMtA : (Fin 3 → ℝ) → ℝ := fun x => matan (fTA x)
def fMtB : (Fin 3 → ℝ) → ℝ := fun x => matan (fTB x)
def fMtC : (Fin 3 → ℝ) → ℝ := fun x => matan (fTC x)
def fMgA : (Fin 3 → ℝ) → ℝ := fun x => matan (fGA x)
def fMgB : (Fin 3 → ℝ) → ℝ := fun x => matan (fGB x)
def fMgC : (Fin 3 → ℝ) → ℝ := fun x => matan (fGC x)
def fDihA : (Fin 3 → ℝ) → ℝ := fun x => fWA x * fMgA x
def fDihB : (Fin 3 → ℝ) → ℝ := fun x => fWB x * fMgB x
def fDihC : (Fin 3 → ℝ) → ℝ := fun x => fWC x * fMgC x
def fSeA : (Fin 3 → ℝ) → ℝ := fun x => fMtA x * fIA x
def fSeB : (Fin 3 → ℝ) → ℝ := fun x => fMtB x * fIB x
def fSeC : (Fin 3 → ℝ) → ℝ := fun x => fMtC x * fIC x
def fSe : (Fin 3 → ℝ) → ℝ := fun x => fSeA x + fSeB x + fSeC x
def fFirst : (Fin 3 → ℝ) → ℝ := fun x => fC112 x - fK1 x * fSe x
def fPos : (Fin 3 → ℝ) → ℝ := fun x => fK2 x * (fLf5 x * fDihA x + fLf6 x * fDihB x)
def fNeg2 : (Fin 3 → ℝ) → ℝ := fun x => fC008 x * fDihC x

/-- **The tree function**: `w1aF` with the `h0cut`-smoothed `pq1` term dropped
(it vanishes identically on `{2 h0 ≤ y4}`). -/
def w1F3Z (x : Fin 3 → ℝ) : ℝ := fFirst x + fPos x - fNeg2 x

/-! ### 3.1 Coordinate, constant and rational jets -/

def JY4 (L : W1Leaf) : WholeBoxJet fY4 (w1Box3 L.I4 L.I5 L.I6) :=
  coordJet 0 L.I4 _ (fun x hx => hx.1)
def JY5 (L : W1Leaf) : WholeBoxJet fY5 (w1Box3 L.I4 L.I5 L.I6) :=
  coordJet 1 L.I5 _ (fun x hx => hx.2.1)
def JY6 (L : W1Leaf) : WholeBoxJet fY6 (w1Box3 L.I4 L.I5 L.I6) :=
  coordJet 2 L.I6 _ (fun x hx => hx.2.2)

def JSI (L : W1Leaf) : WholeBoxJet fSI (w1Box3 L.I4 L.I5 L.I6) :=
  constJet (Real.sqrt 2) L.sI L.hsI _
def JPI (L : W1Leaf) : WholeBoxJet fPI (w1Box3 L.I4 L.I5 L.I6) :=
  constJet Real.pi L.piI L.hpi _
def JMM1 (L : W1Leaf) : WholeBoxJet fMM1 (w1Box3 L.I4 L.I5 L.I6) :=
  constJet mm1 L.mm1I L.hmm1 _
def JMM2 (L : W1Leaf) : WholeBoxJet fMM2 (w1Box3 L.I4 L.I5 L.I6) :=
  constJet mm2 L.mm2I L.hmm2 _

def JCN2 (L : W1Leaf) : WholeBoxJet fCN2 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (-2) (-2) (by norm_num) _
def JC4 (L : W1Leaf) : WholeBoxJet fC4 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet 4 4 (by norm_num) _
def JC8 (L : W1Leaf) : WholeBoxJet fC8 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet 8 8 (by norm_num) _
def JC2 (L : W1Leaf) : WholeBoxJet fC2 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet 2 2 (by norm_num) _
def JCH (L : W1Leaf) : WholeBoxJet fCH (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (1/2) (1/2) (by norm_num) _
def JCH0 (L : W1Leaf) : WholeBoxJet fCH0 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (63/50) (63/50) (by norm_num) _
def JCH0i (L : W1Leaf) : WholeBoxJet fCH0i (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (50/13) (50/13) (by norm_num) _
def JC008 (L : W1Leaf) : WholeBoxJet fC008 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (1/125) (1/125) (by norm_num) _
def JC112 (L : W1Leaf) : WholeBoxJet fC112 (w1Box3 L.I4 L.I5 L.I6) :=
  ratJet (1/12) (1/12) (by norm_num) _

/-! ### 3.2 The additive slots -/

def JX4 (L : W1Leaf) : WholeBoxJet fX4 (w1Box3 L.I4 L.I5 L.I6) := (JY4 L).mul (JY4 L)
def JX5 (L : W1Leaf) : WholeBoxJet fX5 (w1Box3 L.I4 L.I5 L.I6) := (JY5 L).mul (JY5 L)
def JX6 (L : W1Leaf) : WholeBoxJet fX6 (w1Box3 L.I4 L.I5 L.I6) := (JY6 L).mul (JY6 L)
def JS2 (L : W1Leaf) : WholeBoxJet fS2 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JX4 L).mul (JX4 L)).add ((JX5 L).mul (JX5 L)) |>.add ((JX6 L).mul (JX6 L))
def JS1 (L : W1Leaf) : WholeBoxJet fS1 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JX4 L).mul (JX5 L)).add ((JX4 L).mul (JX6 L)) |>.add ((JX5 L).mul (JX6 L))
def JDlt (L : W1Leaf) : WholeBoxJet fDlt (w1Box3 L.I4 L.I5 L.I6) :=
  (((JCN2 L).mul (JS2 L)).add ((JC4 L).mul (JS1 L))).sub
    (((JX4 L).mul (JX5 L)).mul (JX6 L))
def JA (L : W1Leaf) : WholeBoxJet fA (w1Box3 L.I4 L.I5 L.I6) :=
  (((((JSI L).mul (JY5 L)).mul (JY4 L)).add
      (((JY5 L).mul ((JY4 L).mul (JY4 L))).mul (JCH L))).add
    (((JSI L).mul ((((JY5 L).mul (JY5 L)).add ((JY4 L).mul (JY4 L))).sub
        ((JY6 L).mul (JY6 L)))).mul (JCH L))).add
    (((JY4 L).mul ((JY5 L).mul (JY5 L))).mul (JCH L))
def JB (L : W1Leaf) : WholeBoxJet fB (w1Box3 L.I4 L.I5 L.I6) :=
  (((((JSI L).mul (JY6 L)).mul (JY5 L)).add
      (((JY6 L).mul ((JY5 L).mul (JY5 L))).mul (JCH L))).add
    (((JSI L).mul ((((JY6 L).mul (JY6 L)).add ((JY5 L).mul (JY5 L))).sub
        ((JY4 L).mul (JY4 L)))).mul (JCH L))).add
    (((JY5 L).mul ((JY6 L).mul (JY6 L))).mul (JCH L))
def JC (L : W1Leaf) : WholeBoxJet fC (w1Box3 L.I4 L.I5 L.I6) :=
  (((((JSI L).mul (JY4 L)).mul (JY6 L)).add
      (((JY4 L).mul ((JY6 L).mul (JY6 L))).mul (JCH L))).add
    (((JSI L).mul ((((JY4 L).mul (JY4 L)).add ((JY6 L).mul (JY6 L))).sub
        ((JY5 L).mul (JY5 L)))).mul (JCH L))).add
    (((JY6 L).mul ((JY4 L).mul (JY4 L))).mul (JCH L))
def JD4A (L : W1Leaf) : WholeBoxJet fD4A (w1Box3 L.I4 L.I5 L.I6) :=
  ((JY5 L).mul (JY5 L)).mul
    ((((JY4 L).mul (JY4 L)).add ((JY6 L).mul (JY6 L))).sub ((JY5 L).mul (JY5 L)))
def JD4B (L : W1Leaf) : WholeBoxJet fD4B (w1Box3 L.I4 L.I5 L.I6) :=
  ((JY6 L).mul (JY6 L)).mul
    ((((JY5 L).mul (JY5 L)).add ((JY4 L).mul (JY4 L))).sub ((JY6 L).mul (JY6 L)))
def JD4C (L : W1Leaf) : WholeBoxJet fD4C (w1Box3 L.I4 L.I5 L.I6) :=
  ((JY4 L).mul (JY4 L)).mul
    ((((JY6 L).mul (JY6 L)).add ((JY5 L).mul (JY5 L))).sub ((JY4 L).mul (JY4 L)))
def JKA (L : W1Leaf) : WholeBoxJet fKA (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JY5 L).mul (JY5 L))
def JKB (L : W1Leaf) : WholeBoxJet fKB (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JY6 L).mul (JY6 L))
def JKC (L : W1Leaf) : WholeBoxJet fKC (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JY4 L).mul (JY4 L))
def JNA (L : W1Leaf) : WholeBoxJet fNA (w1Box3 L.I4 L.I5 L.I6) := (JC2 L).mul (JY5 L)
def JNB (L : W1Leaf) : WholeBoxJet fNB (w1Box3 L.I4 L.I5 L.I6) := (JC2 L).mul (JY6 L)
def JNC (L : W1Leaf) : WholeBoxJet fNC (w1Box3 L.I4 L.I5 L.I6) := (JC2 L).mul (JY4 L)
def JLf4 (L : W1Leaf) : WholeBoxJet fLf4 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JCH0 L).sub ((JY4 L).mul (JCH L))).mul (JCH0i L)
def JLf5 (L : W1Leaf) : WholeBoxJet fLf5 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JCH0 L).sub ((JY5 L).mul (JCH L))).mul (JCH0i L)
def JLf6 (L : W1Leaf) : WholeBoxJet fLf6 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JCH0 L).sub ((JY6 L).mul (JCH L))).mul (JCH0i L)
def JINVPI (L : W1Leaf) : WholeBoxJet fINVPI (w1Box3 L.I4 L.I5 L.I6) :=
  (JPI L).comp (invUnaryBox L.piI (Or.inl L.hpi0))
def JK1 (L : W1Leaf) : WholeBoxJet fK1 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JC2 L).mul (JMM1 L)).mul (JINVPI L)
def JK2 (L : W1Leaf) : WholeBoxJet fK2 (w1Box3 L.I4 L.I5 L.I6) :=
  ((JC8 L).mul (JMM2 L)).mul (JINVPI L)

/-! ### 3.3 The inverse-argument jets (per-box inverse boxes) -/

def J4a2A (L : W1Leaf) : WholeBoxJet f4a2A (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JA L).mul (JA L))
def J4a2B (L : W1Leaf) : WholeBoxJet f4a2B (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JB L).mul (JB L))
def J4a2C (L : W1Leaf) : WholeBoxJet f4a2C (w1Box3 L.I4 L.I5 L.I6) :=
  (JC4 L).mul ((JC L).mul (JC L))
def JA2A (L : W1Leaf) : WholeBoxJet fA2A (w1Box3 L.I4 L.I5 L.I6) := (JD4A L).mul (JD4A L)
def JA2B (L : W1Leaf) : WholeBoxJet fA2B (w1Box3 L.I4 L.I5 L.I6) := (JD4B L).mul (JD4B L)
def JA2C (L : W1Leaf) : WholeBoxJet fA2C (w1Box3 L.I4 L.I5 L.I6) := (JD4C L).mul (JD4C L)

def JT4A (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value) :
    WholeBoxJet fT4A (w1Box3 L.I4 L.I5 L.I6) := (J4a2A L).comp INVA
def JT4B (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value) :
    WholeBoxJet fT4B (w1Box3 L.I4 L.I5 L.I6) := (J4a2B L).comp INVB
def JT4C (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value) :
    WholeBoxJet fT4C (w1Box3 L.I4 L.I5 L.I6) := (J4a2C L).comp INVC

def JTA (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value) :
    WholeBoxJet fTA (w1Box3 L.I4 L.I5 L.I6) := (JDlt L).mul (JT4A L INVA)
def JTB (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value) :
    WholeBoxJet fTB (w1Box3 L.I4 L.I5 L.I6) := (JDlt L).mul (JT4B L INVB)
def JTC (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value) :
    WholeBoxJet fTC (w1Box3 L.I4 L.I5 L.I6) := (JDlt L).mul (JT4C L INVC)

def JInvA2A (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value) :
    WholeBoxJet fInvA2A (w1Box3 L.I4 L.I5 L.I6) := (JA2A L).comp IA2A
def JInvA2B (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value) :
    WholeBoxJet fInvA2B (w1Box3 L.I4 L.I5 L.I6) := (JA2B L).comp IA2B
def JInvA2C (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value) :
    WholeBoxJet fInvA2C (w1Box3 L.I4 L.I5 L.I6) := (JA2C L).comp IA2C

def JGA (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value) :
    WholeBoxJet fGA (w1Box3 L.I4 L.I5 L.I6) :=
  ((JKA L).mul (JDlt L)).mul (JInvA2A L IA2A)
def JGB (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value) :
    WholeBoxJet fGB (w1Box3 L.I4 L.I5 L.I6) :=
  ((JKB L).mul (JDlt L)).mul (JInvA2B L IA2B)
def JGC (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value) :
    WholeBoxJet fGC (w1Box3 L.I4 L.I5 L.I6) :=
  ((JKC L).mul (JDlt L)).mul (JInvA2C L IA2C)

def JIA (L : W1Leaf) (IA : UnaryBox (fun t : ℝ => t⁻¹) (JA L).value) :
    WholeBoxJet fIA (w1Box3 L.I4 L.I5 L.I6) := (JA L).comp IA
def JIB (L : W1Leaf) (IB : UnaryBox (fun t : ℝ => t⁻¹) (JB L).value) :
    WholeBoxJet fIB (w1Box3 L.I4 L.I5 L.I6) := (JB L).comp IB
def JIC (L : W1Leaf) (IC : UnaryBox (fun t : ℝ => t⁻¹) (JC L).value) :
    WholeBoxJet fIC (w1Box3 L.I4 L.I5 L.I6) := (JC L).comp IC

def JInvD4A (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4A L).value) :
    WholeBoxJet fInvD4A (w1Box3 L.I4 L.I5 L.I6) := (JD4A L).comp ID4A
def JInvD4B (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4B L).value) :
    WholeBoxJet fInvD4B (w1Box3 L.I4 L.I5 L.I6) := (JD4B L).comp ID4B
def JInvD4C (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4C L).value) :
    WholeBoxJet fInvD4C (w1Box3 L.I4 L.I5 L.I6) := (JD4C L).comp ID4C

def JWA (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4A L).value) :
    WholeBoxJet fWA (w1Box3 L.I4 L.I5 L.I6) := (JNA L).mul (JInvD4A L ID4A)
def JWB (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4B L).value) :
    WholeBoxJet fWB (w1Box3 L.I4 L.I5 L.I6) := (JNB L).mul (JInvD4B L ID4B)
def JWC (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4C L).value) :
    WholeBoxJet fWC (w1Box3 L.I4 L.I5 L.I6) := (JNC L).mul (JInvD4C L ID4C)

/-! ### 3.4 The `matan` compositions and the assembly -/

def JMtA (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value)
    (BTA : UnaryBox matan (JTA L INVA).value) :
    WholeBoxJet fMtA (w1Box3 L.I4 L.I5 L.I6) := (JTA L INVA).comp BTA
def JMtB (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value)
    (BTB : UnaryBox matan (JTB L INVB).value) :
    WholeBoxJet fMtB (w1Box3 L.I4 L.I5 L.I6) := (JTB L INVB).comp BTB
def JMtC (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value)
    (BTC : UnaryBox matan (JTC L INVC).value) :
    WholeBoxJet fMtC (w1Box3 L.I4 L.I5 L.I6) := (JTC L INVC).comp BTC
def JMgA (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value)
    (BGA : UnaryBox matan (JGA L IA2A).value) :
    WholeBoxJet fMgA (w1Box3 L.I4 L.I5 L.I6) := (JGA L IA2A).comp BGA
def JMgB (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value)
    (BGB : UnaryBox matan (JGB L IA2B).value) :
    WholeBoxJet fMgB (w1Box3 L.I4 L.I5 L.I6) := (JGB L IA2B).comp BGB
def JMgC (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value)
    (BGC : UnaryBox matan (JGC L IA2C).value) :
    WholeBoxJet fMgC (w1Box3 L.I4 L.I5 L.I6) := (JGC L IA2C).comp BGC

def JDihA (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4A L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value)
    (BGA : UnaryBox matan (JGA L IA2A).value) :
    WholeBoxJet fDihA (w1Box3 L.I4 L.I5 L.I6) :=
  (JWA L ID4A).mul (JMgA L IA2A BGA)
def JDihB (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4B L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value)
    (BGB : UnaryBox matan (JGB L IA2B).value) :
    WholeBoxJet fDihB (w1Box3 L.I4 L.I5 L.I6) :=
  (JWB L ID4B).mul (JMgB L IA2B BGB)
def JDihC (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4C L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value)
    (BGC : UnaryBox matan (JGC L IA2C).value) :
    WholeBoxJet fDihC (w1Box3 L.I4 L.I5 L.I6) :=
  (JWC L ID4C).mul (JMgC L IA2C BGC)

def JSeA (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JA L).value)
    (BTA : UnaryBox matan (JTA L INVA).value) :
    WholeBoxJet fSeA (w1Box3 L.I4 L.I5 L.I6) :=
  (JMtA L INVA BTA).mul (JIA L IA)
def JSeB (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JB L).value)
    (BTB : UnaryBox matan (JTB L INVB).value) :
    WholeBoxJet fSeB (w1Box3 L.I4 L.I5 L.I6) :=
  (JMtB L INVB BTB).mul (JIB L IB)
def JSeC (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JC L).value)
    (BTC : UnaryBox matan (JTC L INVC).value) :
    WholeBoxJet fSeC (w1Box3 L.I4 L.I5 L.I6) :=
  (JMtC L INVC BTC).mul (JIC L IC)

def JSe (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JA L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JB L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JC L).value)
    (BTA : UnaryBox matan (JTA L INVA).value)
    (BTB : UnaryBox matan (JTB L INVB).value)
    (BTC : UnaryBox matan (JTC L INVC).value) :
    WholeBoxJet fSe (w1Box3 L.I4 L.I5 L.I6) :=
  ((JSeA L INVA IA BTA).add (JSeB L INVB IB BTB)).add (JSeC L INVC IC BTC)

def JFirst (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JA L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JB L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JC L).value)
    (BTA : UnaryBox matan (JTA L INVA).value)
    (BTB : UnaryBox matan (JTB L INVB).value)
    (BTC : UnaryBox matan (JTC L INVC).value) :
    WholeBoxJet fFirst (w1Box3 L.I4 L.I5 L.I6) :=
  (JC112 L).sub ((JK1 L).mul (JSe L INVA INVB INVC IA IB IC BTA BTB BTC))

def JPos (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4A L).value)
    (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4B L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value)
    (BGA : UnaryBox matan (JGA L IA2A).value)
    (BGB : UnaryBox matan (JGB L IA2B).value) :
    WholeBoxJet fPos (w1Box3 L.I4 L.I5 L.I6) :=
  (JK2 L).mul (((JLf5 L).mul (JDihA L ID4A IA2A BGA)).add
    ((JLf6 L).mul (JDihB L ID4B IA2B BGB)))

def JNeg2 (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4C L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value)
    (BGC : UnaryBox matan (JGC L IA2C).value) :
    WholeBoxJet fNeg2 (w1Box3 L.I4 L.I5 L.I6) :=
  (JC008 L).mul (JDihC L ID4C IA2C BGC)

/-- **The assembled `WholeBoxJet` of `w1F3Z`.** -/
def JTop (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2A L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2B L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2C L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JA L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JB L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JC L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2A L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2B L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2C L).value)
    (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4A L).value)
    (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4B L).value)
    (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4C L).value)
    (BTA : UnaryBox matan (JTA L INVA).value)
    (BTB : UnaryBox matan (JTB L INVB).value)
    (BTC : UnaryBox matan (JTC L INVC).value)
    (BGA : UnaryBox matan (JGA L IA2A).value)
    (BGB : UnaryBox matan (JGB L IA2B).value)
    (BGC : UnaryBox matan (JGC L IA2C).value) :
    WholeBoxJet w1F3Z (w1Box3 L.I4 L.I5 L.I6) :=
  ((JFirst L INVA INVB INVC IA IB IC BTA BTB BTC).add
    (JPos L ID4A ID4B IA2A IA2B BGA BGB)).sub (JNeg2 L ID4C IA2C BGC)





/-! ## 3.5 The rounded (1e-9) twin of the tree

Every *computed* node is wrapped in `roundJet`; the coordinate jets and the
constant leaves stay exact (the box endpoints and the tiling must not move).
This is the chain the per-box emission instantiates (`REPORT.md` §3 B2). -/
def JY4R (L : W1Leaf) : WholeBoxJet fY4 (w1Box3 L.I4 L.I5 L.I6)  := coordJet 0 L.I4 _ (fun x hx => hx.1)
def JY5R (L : W1Leaf) : WholeBoxJet fY5 (w1Box3 L.I4 L.I5 L.I6)  := coordJet 1 L.I5 _ (fun x hx => hx.2.1)
def JY6R (L : W1Leaf) : WholeBoxJet fY6 (w1Box3 L.I4 L.I5 L.I6)  := coordJet 2 L.I6 _ (fun x hx => hx.2.2)
def JSIR (L : W1Leaf) : WholeBoxJet fSI (w1Box3 L.I4 L.I5 L.I6)  := constJet (Real.sqrt 2) L.sI L.hsI _
def JPIR (L : W1Leaf) : WholeBoxJet fPI (w1Box3 L.I4 L.I5 L.I6)  := constJet Real.pi L.piI L.hpi _
def JMM1R (L : W1Leaf) : WholeBoxJet fMM1 (w1Box3 L.I4 L.I5 L.I6)  := constJet mm1 L.mm1I L.hmm1 _
def JMM2R (L : W1Leaf) : WholeBoxJet fMM2 (w1Box3 L.I4 L.I5 L.I6)  := constJet mm2 L.mm2I L.hmm2 _
def JCN2R (L : W1Leaf) : WholeBoxJet fCN2 (w1Box3 L.I4 L.I5 L.I6)  := ratJet (-2) (-2) (by norm_num) _
def JC4R (L : W1Leaf) : WholeBoxJet fC4 (w1Box3 L.I4 L.I5 L.I6)  := ratJet 4 4 (by norm_num) _
def JC8R (L : W1Leaf) : WholeBoxJet fC8 (w1Box3 L.I4 L.I5 L.I6)  := ratJet 8 8 (by norm_num) _
def JC2R (L : W1Leaf) : WholeBoxJet fC2 (w1Box3 L.I4 L.I5 L.I6)  := ratJet 2 2 (by norm_num) _
def JCHR (L : W1Leaf) : WholeBoxJet fCH (w1Box3 L.I4 L.I5 L.I6)  := ratJet (1/2) (1/2) (by norm_num) _
def JCH0R (L : W1Leaf) : WholeBoxJet fCH0 (w1Box3 L.I4 L.I5 L.I6)  := ratJet (63/50) (63/50) (by norm_num) _
def JCH0iR (L : W1Leaf) : WholeBoxJet fCH0i (w1Box3 L.I4 L.I5 L.I6)  := ratJet (50/13) (50/13) (by norm_num) _
def JC008R (L : W1Leaf) : WholeBoxJet fC008 (w1Box3 L.I4 L.I5 L.I6)  := ratJet (1/125) (1/125) (by norm_num) _
def JC112R (L : W1Leaf) : WholeBoxJet fC112 (w1Box3 L.I4 L.I5 L.I6)  := ratJet (1/12) (1/12) (by norm_num) _
def JX4R (L : W1Leaf) : WholeBoxJet fX4 (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JY4R L).mul (JY4R L))
def JX5R (L : W1Leaf) : WholeBoxJet fX5 (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JY5R L).mul (JY5R L))
def JX6R (L : W1Leaf) : WholeBoxJet fX6 (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JY6R L).mul (JY6R L))
def JS2R (L : W1Leaf) : WholeBoxJet fS2 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JX4R L).mul (JX4R L)).add ((JX5R L).mul (JX5R L)) |>.add ((JX6R L).mul (JX6R L)))
def JS1R (L : W1Leaf) : WholeBoxJet fS1 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JX4R L).mul (JX5R L)).add ((JX4R L).mul (JX6R L)) |>.add ((JX5R L).mul (JX6R L)))
def JDltR (L : W1Leaf) : WholeBoxJet fDlt (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((((JCN2R L).mul (JS2R L)).add ((JC4R L).mul (JS1R L))).sub
    (((JX4R L).mul (JX5R L)).mul (JX6R L)))
def JAR (L : W1Leaf) : WholeBoxJet fA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((((((JSIR L).mul (JY5R L)).mul (JY4R L)).add
      (((JY5R L).mul ((JY4R L).mul (JY4R L))).mul (JCHR L))).add
    (((JSIR L).mul ((((JY5R L).mul (JY5R L)).add ((JY4R L).mul (JY4R L))).sub
        ((JY6R L).mul (JY6R L)))).mul (JCHR L))).add
    (((JY4R L).mul ((JY5R L).mul (JY5R L))).mul (JCHR L)))
def JBR (L : W1Leaf) : WholeBoxJet fB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((((((JSIR L).mul (JY6R L)).mul (JY5R L)).add
      (((JY6R L).mul ((JY5R L).mul (JY5R L))).mul (JCHR L))).add
    (((JSIR L).mul ((((JY6R L).mul (JY6R L)).add ((JY5R L).mul (JY5R L))).sub
        ((JY4R L).mul (JY4R L)))).mul (JCHR L))).add
    (((JY5R L).mul ((JY6R L).mul (JY6R L))).mul (JCHR L)))
def JCR (L : W1Leaf) : WholeBoxJet fC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((((((JSIR L).mul (JY4R L)).mul (JY6R L)).add
      (((JY4R L).mul ((JY6R L).mul (JY6R L))).mul (JCHR L))).add
    (((JSIR L).mul ((((JY4R L).mul (JY4R L)).add ((JY6R L).mul (JY6R L))).sub
        ((JY5R L).mul (JY5R L)))).mul (JCHR L))).add
    (((JY6R L).mul ((JY4R L).mul (JY4R L))).mul (JCHR L)))
def JD4AR (L : W1Leaf) : WholeBoxJet fD4A (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JY5R L).mul (JY5R L)).mul
    ((((JY4R L).mul (JY4R L)).add ((JY6R L).mul (JY6R L))).sub ((JY5R L).mul (JY5R L))))
def JD4BR (L : W1Leaf) : WholeBoxJet fD4B (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JY6R L).mul (JY6R L)).mul
    ((((JY5R L).mul (JY5R L)).add ((JY4R L).mul (JY4R L))).sub ((JY6R L).mul (JY6R L))))
def JD4CR (L : W1Leaf) : WholeBoxJet fD4C (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JY4R L).mul (JY4R L)).mul
    ((((JY6R L).mul (JY6R L)).add ((JY5R L).mul (JY5R L))).sub ((JY4R L).mul (JY4R L))))
def JKAR (L : W1Leaf) : WholeBoxJet fKA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JY5R L).mul (JY5R L)))
def JKBR (L : W1Leaf) : WholeBoxJet fKB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JY6R L).mul (JY6R L)))
def JKCR (L : W1Leaf) : WholeBoxJet fKC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JY4R L).mul (JY4R L)))
def JNAR (L : W1Leaf) : WholeBoxJet fNA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC2R L).mul (JY5R L))
def JNBR (L : W1Leaf) : WholeBoxJet fNB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC2R L).mul (JY6R L))
def JNCR (L : W1Leaf) : WholeBoxJet fNC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC2R L).mul (JY4R L))
def JLf4R (L : W1Leaf) : WholeBoxJet fLf4 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JCH0R L).sub ((JY4R L).mul (JCHR L))).mul (JCH0iR L))
def JLf5R (L : W1Leaf) : WholeBoxJet fLf5 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JCH0R L).sub ((JY5R L).mul (JCHR L))).mul (JCH0iR L))
def JLf6R (L : W1Leaf) : WholeBoxJet fLf6 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JCH0R L).sub ((JY6R L).mul (JCHR L))).mul (JCH0iR L))
def JINVPIR (L : W1Leaf) : WholeBoxJet fINVPI (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JPIR L).comp (invUnaryBox L.piI (Or.inl L.hpi0)))
def JK1R (L : W1Leaf) : WholeBoxJet fK1 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JC2R L).mul (JMM1R L)).mul (JINVPIR L))
def JK2R (L : W1Leaf) : WholeBoxJet fK2 (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JC8R L).mul (JMM2R L)).mul (JINVPIR L))
def J4a2AR (L : W1Leaf) : WholeBoxJet f4a2A (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JAR L).mul (JAR L)))
def J4a2BR (L : W1Leaf) : WholeBoxJet f4a2B (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JBR L).mul (JBR L)))
def J4a2CR (L : W1Leaf) : WholeBoxJet f4a2C (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC4R L).mul ((JCR L).mul (JCR L)))
def JA2AR (L : W1Leaf) : WholeBoxJet fA2A (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4AR L).mul (JD4AR L))
def JA2BR (L : W1Leaf) : WholeBoxJet fA2B (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4BR L).mul (JD4BR L))
def JA2CR (L : W1Leaf) : WholeBoxJet fA2C (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4CR L).mul (JD4CR L))
def JT4AR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value) :
    WholeBoxJet fT4A (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((J4a2AR L).comp INVA)
def JT4BR (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value) :
    WholeBoxJet fT4B (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((J4a2BR L).comp INVB)
def JT4CR (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value) :
    WholeBoxJet fT4C (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((J4a2CR L).comp INVC)
def JTAR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value) :
    WholeBoxJet fTA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JDltR L).mul (JT4AR L INVA))
def JTBR (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value) :
    WholeBoxJet fTB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JDltR L).mul (JT4BR L INVB))
def JTCR (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value) :
    WholeBoxJet fTC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JDltR L).mul (JT4CR L INVC))
def JInvA2AR (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value) :
    WholeBoxJet fInvA2A (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JA2AR L).comp IA2A)
def JInvA2BR (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value) :
    WholeBoxJet fInvA2B (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JA2BR L).comp IA2B)
def JInvA2CR (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value) :
    WholeBoxJet fInvA2C (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JA2CR L).comp IA2C)
def JGAR (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value) :
    WholeBoxJet fGA (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JKAR L).mul (JDltR L)).mul (JInvA2AR L IA2A))
def JGBR (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value) :
    WholeBoxJet fGB (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JKBR L).mul (JDltR L)).mul (JInvA2BR L IA2B))
def JGCR (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value) :
    WholeBoxJet fGC (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JKCR L).mul (JDltR L)).mul (JInvA2CR L IA2C))
def JIAR (L : W1Leaf) (IA : UnaryBox (fun t : ℝ => t⁻¹) (JAR L).value) :
    WholeBoxJet fIA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JAR L).comp IA)
def JIBR (L : W1Leaf) (IB : UnaryBox (fun t : ℝ => t⁻¹) (JBR L).value) :
    WholeBoxJet fIB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JBR L).comp IB)
def JICR (L : W1Leaf) (IC : UnaryBox (fun t : ℝ => t⁻¹) (JCR L).value) :
    WholeBoxJet fIC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JCR L).comp IC)
def JInvD4AR (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4AR L).value) :
    WholeBoxJet fInvD4A (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4AR L).comp ID4A)
def JInvD4BR (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4BR L).value) :
    WholeBoxJet fInvD4B (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4BR L).comp ID4B)
def JInvD4CR (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4CR L).value) :
    WholeBoxJet fInvD4C (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JD4CR L).comp ID4C)
def JWAR (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4AR L).value) :
    WholeBoxJet fWA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JNAR L).mul (JInvD4AR L ID4A))
def JWBR (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4BR L).value) :
    WholeBoxJet fWB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JNBR L).mul (JInvD4BR L ID4B))
def JWCR (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4CR L).value) :
    WholeBoxJet fWC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JNCR L).mul (JInvD4CR L ID4C))
def JMtAR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value)
    (BTA : UnaryBox matan (JTAR L INVA).value) :
    WholeBoxJet fMtA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JTAR L INVA).comp BTA)
def JMtBR (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value)
    (BTB : UnaryBox matan (JTBR L INVB).value) :
    WholeBoxJet fMtB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JTBR L INVB).comp BTB)
def JMtCR (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value)
    (BTC : UnaryBox matan (JTCR L INVC).value) :
    WholeBoxJet fMtC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JTCR L INVC).comp BTC)
def JMgAR (L : W1Leaf) (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value)
    (BGA : UnaryBox matan (JGAR L IA2A).value) :
    WholeBoxJet fMgA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JGAR L IA2A).comp BGA)
def JMgBR (L : W1Leaf) (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value)
    (BGB : UnaryBox matan (JGBR L IA2B).value) :
    WholeBoxJet fMgB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JGBR L IA2B).comp BGB)
def JMgCR (L : W1Leaf) (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value)
    (BGC : UnaryBox matan (JGCR L IA2C).value) :
    WholeBoxJet fMgC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JGCR L IA2C).comp BGC)
def JDihAR (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4AR L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value)
    (BGA : UnaryBox matan (JGAR L IA2A).value) :
    WholeBoxJet fDihA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JWAR L ID4A).mul (JMgAR L IA2A BGA))
def JDihBR (L : W1Leaf) (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4BR L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value)
    (BGB : UnaryBox matan (JGBR L IA2B).value) :
    WholeBoxJet fDihB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JWBR L ID4B).mul (JMgBR L IA2B BGB))
def JDihCR (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4CR L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value)
    (BGC : UnaryBox matan (JGCR L IA2C).value) :
    WholeBoxJet fDihC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JWCR L ID4C).mul (JMgCR L IA2C BGC))
def JSeAR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JAR L).value)
    (BTA : UnaryBox matan (JTAR L INVA).value) :
    WholeBoxJet fSeA (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JMtAR L INVA BTA).mul (JIAR L IA))
def JSeBR (L : W1Leaf) (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JBR L).value)
    (BTB : UnaryBox matan (JTBR L INVB).value) :
    WholeBoxJet fSeB (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JMtBR L INVB BTB).mul (JIBR L IB))
def JSeCR (L : W1Leaf) (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JCR L).value)
    (BTC : UnaryBox matan (JTCR L INVC).value) :
    WholeBoxJet fSeC (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JMtCR L INVC BTC).mul (JICR L IC))
def JSeR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JAR L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JBR L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JCR L).value)
    (BTA : UnaryBox matan (JTAR L INVA).value)
    (BTB : UnaryBox matan (JTBR L INVB).value)
    (BTC : UnaryBox matan (JTCR L INVC).value) :
    WholeBoxJet fSe (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JSeAR L INVA IA BTA).add (JSeBR L INVB IB BTB)).add (JSeCR L INVC IC BTC))
def JFirstR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JAR L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JBR L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JCR L).value)
    (BTA : UnaryBox matan (JTAR L INVA).value)
    (BTB : UnaryBox matan (JTBR L INVB).value)
    (BTC : UnaryBox matan (JTCR L INVC).value) :
    WholeBoxJet fFirst (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC112R L).sub ((JK1R L).mul (JSeR L INVA INVB INVC IA IB IC BTA BTB BTC)))
def JPosR (L : W1Leaf) (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4AR L).value)
    (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4BR L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value)
    (BGA : UnaryBox matan (JGAR L IA2A).value)
    (BGB : UnaryBox matan (JGBR L IA2B).value) :
    WholeBoxJet fPos (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JK2R L).mul (((JLf5R L).mul (JDihAR L ID4A IA2A BGA)).add
    ((JLf6R L).mul (JDihBR L ID4B IA2B BGB))))
def JNeg2R (L : W1Leaf) (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4CR L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value)
    (BGC : UnaryBox matan (JGCR L IA2C).value) :
    WholeBoxJet fNeg2 (w1Box3 L.I4 L.I5 L.I6)  := roundJet ((JC008R L).mul (JDihCR L ID4C IA2C BGC))
def JTopR (L : W1Leaf) (INVA : UnaryBox (fun t : ℝ => t⁻¹) (J4a2AR L).value)
    (INVB : UnaryBox (fun t : ℝ => t⁻¹) (J4a2BR L).value)
    (INVC : UnaryBox (fun t : ℝ => t⁻¹) (J4a2CR L).value)
    (IA : UnaryBox (fun t : ℝ => t⁻¹) (JAR L).value)
    (IB : UnaryBox (fun t : ℝ => t⁻¹) (JBR L).value)
    (IC : UnaryBox (fun t : ℝ => t⁻¹) (JCR L).value)
    (IA2A : UnaryBox (fun t : ℝ => t⁻¹) (JA2AR L).value)
    (IA2B : UnaryBox (fun t : ℝ => t⁻¹) (JA2BR L).value)
    (IA2C : UnaryBox (fun t : ℝ => t⁻¹) (JA2CR L).value)
    (ID4A : UnaryBox (fun t : ℝ => t⁻¹) (JD4AR L).value)
    (ID4B : UnaryBox (fun t : ℝ => t⁻¹) (JD4BR L).value)
    (ID4C : UnaryBox (fun t : ℝ => t⁻¹) (JD4CR L).value)
    (BTA : UnaryBox matan (JTAR L INVA).value)
    (BTB : UnaryBox matan (JTBR L INVB).value)
    (BTC : UnaryBox matan (JTCR L INVC).value)
    (BGA : UnaryBox matan (JGAR L IA2A).value)
    (BGB : UnaryBox matan (JGBR L IA2B).value)
    (BGC : UnaryBox matan (JGCR L IA2C).value) :
    WholeBoxJet w1F3Z (w1Box3 L.I4 L.I5 L.I6)  := roundJet (((JFirstR L INVA INVB INVC IA IB IC BTA BTB BTC).add
    (JPosR L ID4A ID4B IA2A IA2B BGA BGB)).sub (JNeg2R L ID4C IA2C BGC))

/-! ## 4. Slot identification (`f… x = w1…` on the box) -/

section SlotEq

variable (x : Fin 3 → ℝ)

theorem fSI_eq : fSI x = Real.sqrt 2 := rfl
theorem fPI_eq : fPI x = Real.pi := rfl
theorem fMM1_eq : fMM1 x = mm1 := rfl
theorem fMM2_eq : fMM2 x = mm2 := rfl

theorem fDlt_eq : fDlt x = w1Dlt (x 0) (x 1) (x 2) := by
  simp only [fDlt, fS2, fS1, fX4, fX5, fX6, fY4, fY5, fY6, fCN2, fC4]
  unfold w1Dlt
  ring

theorem fA_eq : fA x = w1aA (x 0) (x 1) (x 2) := by
  simp only [fA, fSI, fY4, fY5, fY6, fCH]
  unfold w1aA
  ring

theorem fB_eq : fB x = w1aB (x 0) (x 1) (x 2) := by
  simp only [fB, fSI, fY4, fY5, fY6, fCH]
  unfold w1aB
  ring

theorem fC_eq : fC x = w1aC (x 0) (x 1) (x 2) := by
  simp only [fC, fSI, fY4, fY5, fY6, fCH]
  unfold w1aC
  ring

theorem fD4A_eq : fD4A x = w1d4A (x 0) (x 1) (x 2) := by
  simp only [fD4A, fY4, fY5, fY6]; unfold w1d4A; ring
theorem fD4B_eq : fD4B x = w1d4B (x 0) (x 1) (x 2) := by
  simp only [fD4B, fY4, fY5, fY6]; unfold w1d4B; ring
theorem fD4C_eq : fD4C x = w1d4C (x 0) (x 1) (x 2) := by
  simp only [fD4C, fY4, fY5, fY6]; unfold w1d4C; ring

theorem f4a2A_eq : f4a2A x = 4 * w1aA (x 0) (x 1) (x 2) ^ 2 := by
  simp only [f4a2A, fC4, fA_eq x]; ring
theorem f4a2B_eq : f4a2B x = 4 * w1aB (x 0) (x 1) (x 2) ^ 2 := by
  simp only [f4a2B, fC4, fB_eq x]; ring
theorem f4a2C_eq : f4a2C x = 4 * w1aC (x 0) (x 1) (x 2) ^ 2 := by
  simp only [f4a2C, fC4, fC_eq x]; ring

theorem fTA_eq : fTA x = w1tA (x 0) (x 1) (x 2) := by
  simp only [fTA, fT4A, f4a2A_eq x, fDlt_eq x]; unfold w1tA w1tOf; ring
theorem fTB_eq : fTB x = w1tB (x 0) (x 1) (x 2) := by
  simp only [fTB, fT4B, f4a2B_eq x, fDlt_eq x]; unfold w1tB w1tOf; ring
theorem fTC_eq : fTC x = w1tC (x 0) (x 1) (x 2) := by
  simp only [fTC, fT4C, f4a2C_eq x, fDlt_eq x]; unfold w1tC w1tOf; ring

theorem fA2A_eq : fA2A x = w1d4A (x 0) (x 1) (x 2) ^ 2 := by
  simp only [fA2A, fD4A_eq x]; ring
theorem fA2B_eq : fA2B x = w1d4B (x 0) (x 1) (x 2) ^ 2 := by
  simp only [fA2B, fD4B_eq x]; ring
theorem fA2C_eq : fA2C x = w1d4C (x 0) (x 1) (x 2) ^ 2 := by
  simp only [fA2C, fD4C_eq x]; ring

theorem fGA_eq : fGA x = w1gA (x 0) (x 1) (x 2) := by
  simp only [fGA, fInvA2A, fA2A_eq x, fKA, fC4, fY5, fDlt_eq x]
  unfold w1gA w1gOf
  ring
theorem fGB_eq : fGB x = w1gB (x 0) (x 1) (x 2) := by
  simp only [fGB, fInvA2B, fA2B_eq x, fKB, fC4, fY6, fDlt_eq x]
  unfold w1gB w1gOf
  ring
theorem fGC_eq : fGC x = w1gC (x 0) (x 1) (x 2) := by
  simp only [fGC, fInvA2C, fA2C_eq x, fKC, fC4, fY4, fDlt_eq x]
  unfold w1gC w1gOf
  ring

theorem fWA_eq : fWA x = w1WA (x 0) (x 1) (x 2) := by
  simp only [fWA, fInvD4A, fNA, fC2, fY5, fD4A_eq x]; unfold w1WA w1WOf; ring
theorem fWB_eq : fWB x = w1WB (x 0) (x 1) (x 2) := by
  simp only [fWB, fInvD4B, fNB, fC2, fY6, fD4B_eq x]; unfold w1WB w1WOf; ring
theorem fWC_eq : fWC x = w1WC (x 0) (x 1) (x 2) := by
  simp only [fWC, fInvD4C, fNC, fC2, fY4, fD4C_eq x]; unfold w1WC w1WOf; ring

theorem fK1_eq : fK1 x = 2 * mm1 / Real.pi := by
  simp only [fK1, fINVPI, fC2, fMM1, fPI]; ring
theorem fK2_eq : fK2 x = 8 * mm2 / Real.pi := by
  simp only [fK2, fINVPI, fC8, fMM2, fPI]; ring

theorem fLf4_eq : fLf4 x = lfun (x 0 * 0.5) := by
  simp only [fLf4, fCH0, fCH, fCH0i, fY4]; unfold lfun h0; ring
theorem fLf5_eq : fLf5 x = lfun (x 1 * 0.5) := by
  simp only [fLf5, fCH0, fCH, fCH0i, fY5]; unfold lfun h0; ring
theorem fLf6_eq : fLf6 x = lfun (x 2 * 0.5) := by
  simp only [fLf6, fCH0, fCH, fCH0i, fY6]; unfold lfun h0; ring

end SlotEq

/-! ## 5. The identity `w1F3 = w1F3Z` on the `h0cut = 0` region -/

/-- On `{2 h0 ≤ y4, 0 ≤ y4, 0 < y5, 0 ≤ y6}` the original `w1aF` equals the
`pq1`-dropped tree function `w1F3Z`. -/
theorem w1F3_eq_w1F3Z (x : Fin 3 → ℝ)
    (h4 : 0 ≤ x 0) (h5 : 0 < x 1) (h6 : 0 ≤ x 2) (hcut : 2 * h0 ≤ x 0) :
    w1F3 x = w1F3Z x := by
  have hv : h0cut (x 0) * lfun (x 0 * 0.5) = 0 := nb21_h0cut_lfun_vanish hcut
  unfold w1F3
  rw [w1aF, nb21_w1aG_explicit (x 0) (x 1) (x 2) h4 h5.le h6, nb21_w1aD_explicit]
  rw [w1_seA_unfold (x 0) (x 1) (x 2) h4 h5.le,
    w1_seB_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_seC_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_dihA_unfold (x 0) (x 1) (x 2) h5.le,
    w1_dihB_unfold (x 0) (x 1) (x 2) h6,
    w1_dihC_unfold (x 0) (x 1) (x 2) h4]
  rw [show lfun (x 0 * 0.5) * h0cut (x 0) *
      (w1WC (x 0) (x 1) (x 2) * matan (w1gC (x 0) (x 1) (x 2)))
      = (h0cut (x 0) * lfun (x 0 * 0.5)) *
        (w1WC (x 0) (x 1) (x 2) * matan (w1gC (x 0) (x 1) (x 2))) from by ring]
  rw [hv, zero_mul]
  simp only [w1F3Z, fFirst, fPos, fNeg2, fSe, fSeA, fSeB, fSeC, fDihA, fDihB, fDihC,
    fMtA, fMtB, fMtC, fMgA, fMgB, fMgC, fK1_eq x, fK2_eq x, fLf5_eq x, fLf6_eq x,
    fTA_eq x, fTB_eq x, fTC_eq x, fGA_eq x, fGB_eq x, fGC_eq x, fWA_eq x, fWB_eq x,
    fWC_eq x, fC112, fC008, fIA, fIB, fIC, fA_eq x, fB_eq x, fC_eq x]
  ring

/-! ## 5.1 The `h0cut = 1` (one-mode) twin: `w1F3 = w1F3O`

On `{0 ≤ y4, 0 < y5, 0 ≤ y6, y4 ≤ 2 h0}` the `h0cut` slot is exactly `1`, so
the `pq1` term does **not** drop: it stays as `fLf4 * fDihC`.  This is the
tree function the one-mode per-box emission (`M8`) has to certify. -/

/-- One-mode positive slot: the `pq1` term `fLf4 * fDihC` is **kept**, and it
is the leftmost summand (the shape `nb21_w1aG_explicit` emits). -/
def fPos1 : (Fin 3 → ℝ) → ℝ :=
  fun x => fK2 x * ((fLf4 x * fDihC x + fLf5 x * fDihA x) + fLf6 x * fDihB x)

/-- The one-mode tree function of `w1F3`. -/
def w1F3O (x : Fin 3 → ℝ) : ℝ := fFirst x + fPos1 x - fNeg2 x

/-- On `{0 ≤ y4, 0 < y5, 0 ≤ y6, y4 ≤ 2 h0}` (the `h0cut = 1` branch) the
original `w1aF` equals the one-mode tree function `w1F3O`. -/
theorem w1F3_eq_w1F3O (x : Fin 3 → ℝ)
    (h4 : 0 ≤ x 0) (h5 : 0 < x 1) (h6 : 0 ≤ x 2) (hcut1 : x 0 ≤ 2 * h0) :
    w1F3 x = w1F3O x := by
  have hh : h0cut (x 0) = 1 := by unfold h0cut; rw [if_pos hcut1]
  unfold w1F3
  rw [w1aF, nb21_w1aG_explicit (x 0) (x 1) (x 2) h4 h5.le h6, nb21_w1aD_explicit]
  rw [w1_seA_unfold (x 0) (x 1) (x 2) h4 h5.le,
    w1_seB_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_seC_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_dihA_unfold (x 0) (x 1) (x 2) h5.le,
    w1_dihB_unfold (x 0) (x 1) (x 2) h6,
    w1_dihC_unfold (x 0) (x 1) (x 2) h4]
  rw [hh]
  simp only [w1F3O, fFirst, fPos1, fNeg2, fSe, fSeA, fSeB, fSeC, fDihA, fDihB, fDihC,
    fMtA, fMtB, fMtC, fMgA, fMgB, fMgC, fK1_eq x, fK2_eq x, fLf4_eq x, fLf5_eq x,
    fLf6_eq x, fTA_eq x, fTB_eq x, fTC_eq x, fGA_eq x, fGB_eq x, fGC_eq x, fWA_eq x,
    fWB_eq x, fWC_eq x, fC112, fC008, fIA, fIB, fIC, fA_eq x, fB_eq x, fC_eq x]
  ring

/-- **Total (mode-split) form**: on the rational box, `w1aF` is either the
zero-mode tree `w1F3Z` (above the kink) or the one-mode tree `w1F3O` (at or
below it) — exactly, with no sliver in between. -/
theorem w1F3_eq_ite (x : Fin 3 → ℝ)
    (h4 : 0 ≤ x 0) (h5 : 0 < x 1) (h6 : 0 ≤ x 2) :
    w1F3 x = if 2 * h0 ≤ x 0 then w1F3Z x else w1F3O x := by
  by_cases h : 2 * h0 ≤ x 0
  · rw [if_pos h]; exact w1F3_eq_w1F3Z x h4 h5 h6 h
  · rw [if_neg h]
    exact w1F3_eq_w1F3O x h4 h5 h6 (le_of_lt (lt_of_not_ge h))

/-! ## 6. The generic Taylor terminal -/

/-- Lower-triangular Hessian entry (upper triangle mirrored by `partial2_comm`). -/
def hessEntry {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) (i j : Fin 3) : QInterval :=
  if j ≤ i then J.second i j else J.second j i

theorem hessEntry_00 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 0 0 = J.second 0 0 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_10 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 1 0 = J.second 1 0 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_11 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 1 1 = J.second 1 1 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_20 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 2 0 = J.second 2 0 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_21 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 2 1 = J.second 2 1 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_22 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 2 2 = J.second 2 2 := by
  simp only [hessEntry]; rw [if_pos (by decide)]
theorem hessEntry_01 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 0 1 = J.second 1 0 := by
  simp only [hessEntry]; rw [if_neg (by decide)]
theorem hessEntry_02 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 0 2 = J.second 2 0 := by
  simp only [hessEntry]; rw [if_neg (by decide)]
theorem hessEntry_12 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) : hessEntry J 1 2 = J.second 2 1 := by
  simp only [hessEntry]; rw [if_neg (by decide)]

/-- **Taylor positivity terminal.**  If the certificate slack of the jet is
positive, `f` is positive on the whole box.  The slack is stated in the
explicit lower-triangular form (`1/2` by the Lagrange remainder, off-diagonal
entries counted twice). -/
theorem w1F3Z_pos_of_slack {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c w : Fin 3 → ℝ} (J : WholeBoxJet f D)
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hslack : 0 < (J.value.lo : ℝ) - (
      w 0 * ((J.first 0).iabs : ℝ) + w 1 * ((J.first 1).iabs : ℝ) +
      w 2 * ((J.first 2).iabs : ℝ) +
      (1 / 2) * (
        w 0 * w 0 * ((J.second 0 0).iabs : ℝ) +
        w 0 * w 1 * ((J.second 1 0).iabs : ℝ) +
        w 1 * w 0 * ((J.second 1 0).iabs : ℝ) +
        w 0 * w 2 * ((J.second 2 0).iabs : ℝ) +
        w 2 * w 0 * ((J.second 2 0).iabs : ℝ) +
        w 1 * w 1 * ((J.second 1 1).iabs : ℝ) +
        w 1 * w 2 * ((J.second 2 1).iabs : ℝ) +
        w 2 * w 1 * ((J.second 2 1).iabs : ℝ) +
        w 2 * w 2 * ((J.second 2 2).iabs : ℝ)))) :
    ∀ x ∈ D, 0 < f x := by
  have hhe : ∀ x ∈ D, ∀ i j, |partial2 j i f x| ≤ ((hessEntry J i j).iabs : ℝ) := by
    intro u hu i j
    by_cases h : j ≤ i
    · have hm := QInterval.abs_le_iabs (J.second_mem u hu i j h)
      simpa [hessEntry, if_pos h] using hm
    · have hij : i ≤ j := le_of_lt (lt_of_not_ge h)
      have hm := QInterval.abs_le_iabs (J.second_mem u hu j i hij)
      rw [hessEntry, if_neg h]
      rwa [partial2_comm (J.diff2c u hu) j i]
  have hhg : ∀ i, |partial1 i f c| ≤ ((J.first i).iabs : ℝ) :=
    fun i => QInterval.abs_le_iabs (J.first_mem c hc i)
  have hval : (J.value.lo : ℝ) ≤ f c := (J.value_mem c hc).1
  have hsum : (∑ i : Fin 3, w i * ((J.first i).iabs : ℝ) +
      (1 / 2) * ∑ i : Fin 3, ∑ j : Fin 3, w i * w j * ((hessEntry J i j).iabs : ℝ)) =
      (w 0 * ((J.first 0).iabs : ℝ) + w 1 * ((J.first 1).iabs : ℝ) +
        w 2 * ((J.first 2).iabs : ℝ) +
        (1 / 2) * (w 0 * w 0 * ((J.second 0 0).iabs : ℝ) +
          w 0 * w 1 * ((J.second 1 0).iabs : ℝ) +
          w 1 * w 0 * ((J.second 1 0).iabs : ℝ) +
          w 0 * w 2 * ((J.second 2 0).iabs : ℝ) +
          w 2 * w 0 * ((J.second 2 0).iabs : ℝ) +
          w 1 * w 1 * ((J.second 1 1).iabs : ℝ) +
          w 1 * w 2 * ((J.second 2 1).iabs : ℝ) +
          w 2 * w 1 * ((J.second 2 1).iabs : ℝ) +
          w 2 * w 2 * ((J.second 2 2).iabs : ℝ))) := by
    rw [Fin.sum_univ_three]
    simp only [Fin.sum_univ_three, hessEntry_00 J, hessEntry_10 J, hessEntry_11 J,
      hessEntry_20 J, hessEntry_21 J, hessEntry_22 J, hessEntry_01 J, hessEntry_02 J,
      hessEntry_12 J, Fin.zero_eta, Fin.mk_one]
    ring
  intro u hu
  have h := taylor3_lower (f := f) (D := D) (c := c) (w := w)
    (fc := (J.value.lo : ℝ)) (g := fun i => ((J.first i).iabs : ℝ))
    (e := fun i j => ((hessEntry J i j).iabs : ℝ))
    hc hconv (fun u hu => J.diff2c u hu) hw hval hhg hhe u hu
  rw [hsum] at h
  linarith

/-- **Value-only terminal (T1).**  If the box-wide value enclosure is strictly
positive, `f` is positive on the whole box — no gradient, no Hessian. -/
theorem w1F3Z_pos_of_value {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (J : WholeBoxJet f D) (h : 0 < (J.value.lo : ℝ)) :
    ∀ x ∈ D, 0 < f x := by
  intro x hx
  have hv := (J.value_mem x hx).1
  linarith

/-- **Dual-jet Taylor terminal (T3, pilot-2 form).**

`Jc` is the assembly on the degenerate point box `{c}` (its value and gradient
channels are the *centre* data), `Jb` the assembly on the box `D` (its Hessian
channel is the box-wide bound).  Feeding a single jet is either too weak (box
jet: `value.lo` is a box bound, far below the centre value) or unsound (point
jet: `second_mem` would only give a *point* Hessian while the conclusion is
box-wide). -/
theorem w1F3Z_pos_of_slack2 {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c w : Fin 3 → ℝ} (Jc : WholeBoxJet f {c}) (Jb : WholeBoxJet f D)
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hslack : 0 < (Jc.value.lo : ℝ) - (
      w 0 * ((Jc.first 0).iabs : ℝ) + w 1 * ((Jc.first 1).iabs : ℝ) +
      w 2 * ((Jc.first 2).iabs : ℝ) +
      (1 / 2) * (
        w 0 * w 0 * ((Jb.second 0 0).iabs : ℝ) +
        w 0 * w 1 * ((Jb.second 1 0).iabs : ℝ) +
        w 1 * w 0 * ((Jb.second 1 0).iabs : ℝ) +
        w 0 * w 2 * ((Jb.second 2 0).iabs : ℝ) +
        w 2 * w 0 * ((Jb.second 2 0).iabs : ℝ) +
        w 1 * w 1 * ((Jb.second 1 1).iabs : ℝ) +
        w 1 * w 2 * ((Jb.second 2 1).iabs : ℝ) +
        w 2 * w 1 * ((Jb.second 2 1).iabs : ℝ) +
        w 2 * w 2 * ((Jb.second 2 2).iabs : ℝ)))) :
    ∀ x ∈ D, 0 < f x := by
  have hcpt : c ∈ ({c} : Set (Fin 3 → ℝ)) := rfl
  have hhe : ∀ x ∈ D, ∀ i j, |partial2 j i f x| ≤ ((hessEntry Jb i j).iabs : ℝ) := by
    intro u hu i j
    by_cases h : j ≤ i
    · have hm := QInterval.abs_le_iabs (Jb.second_mem u hu i j h)
      simpa [hessEntry, if_pos h] using hm
    · have hij : i ≤ j := le_of_lt (lt_of_not_ge h)
      have hm := QInterval.abs_le_iabs (Jb.second_mem u hu j i hij)
      rw [hessEntry, if_neg h]
      rwa [partial2_comm (Jb.diff2c u hu) j i]
  have hhg : ∀ i, |partial1 i f c| ≤ ((Jc.first i).iabs : ℝ) :=
    fun i => QInterval.abs_le_iabs (Jc.first_mem c hcpt i)
  have hval : (Jc.value.lo : ℝ) ≤ f c := (Jc.value_mem c hcpt).1
  have hsum : (∑ i : Fin 3, w i * ((Jc.first i).iabs : ℝ) +
      (1 / 2) * ∑ i : Fin 3, ∑ j : Fin 3, w i * w j * ((hessEntry Jb i j).iabs : ℝ)) =
      (w 0 * ((Jc.first 0).iabs : ℝ) + w 1 * ((Jc.first 1).iabs : ℝ) +
        w 2 * ((Jc.first 2).iabs : ℝ) +
        (1 / 2) * (w 0 * w 0 * ((Jb.second 0 0).iabs : ℝ) +
          w 0 * w 1 * ((Jb.second 1 0).iabs : ℝ) +
          w 1 * w 0 * ((Jb.second 1 0).iabs : ℝ) +
          w 0 * w 2 * ((Jb.second 2 0).iabs : ℝ) +
          w 2 * w 0 * ((Jb.second 2 0).iabs : ℝ) +
          w 1 * w 1 * ((Jb.second 1 1).iabs : ℝ) +
          w 1 * w 2 * ((Jb.second 2 1).iabs : ℝ) +
          w 2 * w 1 * ((Jb.second 2 1).iabs : ℝ) +
          w 2 * w 2 * ((Jb.second 2 2).iabs : ℝ))) := by
    rw [Fin.sum_univ_three]
    simp only [Fin.sum_univ_three, hessEntry_00 Jb, hessEntry_10 Jb, hessEntry_11 Jb,
      hessEntry_20 Jb, hessEntry_21 Jb, hessEntry_22 Jb, hessEntry_01 Jb, hessEntry_02 Jb,
      hessEntry_12 Jb, Fin.zero_eta, Fin.mk_one]
    ring
  intro u hu
  have h := taylor3_lower (f := f) (D := D) (c := c) (w := w)
    (fc := (Jc.value.lo : ℝ)) (g := fun i => ((Jc.first i).iabs : ℝ))
    (e := fun i j => ((hessEntry Jb i j).iabs : ℝ))
    hc hconv (fun u hu => Jb.diff2c u hu) hw hval hhg hhe u hu
  rw [hsum] at h
  linarith

/-! ## 8. `matan` point-bracket kit wrappers and per-slot box builders -/

/-- Order-9/11 direct-form point bracket (mirrors `lk_matan_direct9`). -/
def P9 (t : ℚ) : QInterval :=
  QInterval.mk
    (1 - t / 3 + t ^ 2 / 5 - t ^ 3 / 7 + t ^ 4 / 9 - t ^ 5 / 11)
    (1 - t / 3 + t ^ 2 / 5 - t ^ 3 / 7 + t ^ 4 / 9)

/-- w-form point bracket (mirrors `lk_matan_wplus`). -/
def PWp (ql qh : ℚ) : QInterval :=
  QInterval.mk
    ((lkPIlo / 4 + ((ql - 1) / (qh + 1) - ((ql - 1) / (qh + 1)) ^ 3 / 3
        + ((ql - 1) / (qh + 1)) ^ 5 / 5 - ((ql - 1) / (qh + 1)) ^ 7 / 7)) / qh)
    ((lkPIhi / 4 + ((qh - 1) / (ql + 1) - ((qh - 1) / (ql + 1)) ^ 3 / 3
        + ((qh - 1) / (ql + 1)) ^ 5 / 5)) / ql)

/-- u-form point bracket (mirrors `lk_matan_u9`). -/
def PU9 (ql qh : ℚ) : QInterval :=
  QInterval.mk
    ((lkPIlo / 2 - (1 / ql - (1 / ql) ^ 3 / 3 + (1 / ql) ^ 5 / 5 - (1 / ql) ^ 7 / 7
        + (1 / ql) ^ 9 / 9)) / qh)
    ((lkPIhi / 2 - (1 / qh - (1 / qh) ^ 3 / 3 + (1 / qh) ^ 5 / 5 - (1 / qh) ^ 7 / 7
        + (1 / qh) ^ 9 / 9 - (1 / qh) ^ 11 / 11)) / ql)

/-- Mirror-branch point bracket `π/(2√t) − matan(1/t)/t`. -/
def PMir (t ql qh : ℚ) (M : QInterval) : QInterval :=
  QInterval.mk (lkPIlo / (2 * qh) - M.hi / t) (lkPIhi / (2 * ql) - M.lo / t)

/-- Point `matanDD` bracket through `e(t) = 1/(1+t) − matan t`. -/
def DDp (t : ℚ) (P : QInterval) : QInterval := gDp t (gE t P)

theorem P9_mem {t : ℚ} (ht : (0:ℚ) < t) :
    (P9 t).mem (matan ((t : ℚ) : ℝ)) := by
  unfold P9
  exact lk_matan_direct9 (P9 t) t ht rfl

theorem PWp_mem {t ql qh : ℚ} (ht : (1:ℚ) < t)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((t : ℚ) : ℝ))
    (hqh2 : ((t : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hq0 : (0:ℚ) < ql) (hq1 : ql ≤ qh) (hq2 : (1:ℚ) ≤ qh) (hq3 : (qh : ℚ) < 1 + ql)
    (hq4 : (1:ℚ) ≤ ql) :
    (PWp ql qh).mem (matan ((t : ℚ) : ℝ)) := by
  unfold PWp
  exact lk_matan_wplus (PWp ql qh) t ql qh ht hql2 hqh2 hq0 hq1 hq2 hq3 hq4 rfl

theorem PU9_mem {t ql qh : ℚ} (ht : (1:ℚ) < t)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((t : ℚ) : ℝ))
    (hqh2 : ((t : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hq0 : (0:ℚ) < ql) (hq1 : ql ≤ qh) (hq2 : (1:ℚ) ≤ qh) (hq3 : (1:ℚ) ≤ ql) :
    (PU9 ql qh).mem (matan ((t : ℚ) : ℝ)) := by
  unfold PU9
  exact lk_matan_u9 (PU9 ql qh) t ql qh ht hql2 hqh2 hq0 hq1 hq2 hq3 rfl

/-- **Mirror-branch point enclosure**: `matan t = π/(2√t) − matan(1/t)/t`
composed with rational sqrt brackets `ql² ≤ t ≤ qh²` and a point bracket for
`matan (1/t)`. -/
theorem PMir_mem {t ql qh : ℚ} (M : QInterval)
    (ht : (0:ℚ) < t) (hql0 : (0:ℚ) < ql) (hqlqh : ql ≤ qh)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((t : ℚ) : ℝ))
    (hqh2 : ((t : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hM : M.mem (matan (((1 / t : ℚ)) : ℝ))) :
    (PMir t ql qh M).mem (matan ((t : ℚ) : ℝ)) := by
  have htR : (0:ℝ) < ((t : ℚ) : ℝ) := by exact_mod_cast ht
  have hqlR : (0:ℝ) < ((ql : ℚ) : ℝ) := by exact_mod_cast hql0
  have hqhR : (0:ℝ) ≤ ((qh : ℚ) : ℝ) := by
    have h1 : ((ql : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) := by exact_mod_cast hqlqh
    linarith
  have hsp : (0:ℝ) < Real.sqrt ((t : ℚ) : ℝ) := Real.sqrt_pos.mpr htR
  have hslo : ((ql : ℚ) : ℝ) ≤ Real.sqrt ((t : ℚ) : ℝ) := Real.le_sqrt_of_sq_le hql2
  have hshi : Real.sqrt ((t : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) :=
    (Real.sqrt_le_left hqhR).mpr hqh2
  have hM' : M.mem (matan (1 / ((t : ℚ) : ℝ))) := by
    have h : (((1 / t : ℚ)) : ℝ) = 1 / ((t : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_one]
    rwa [h] at hM
  have hPI := lk_pi_mem
  have hPI0 : (0:ℝ) < (lkPIlo : ℝ) := by norm_num [lkPIlo]
  rw [lk_matan_mirror htR]
  constructor
  · have h1 : (lkPIlo : ℝ) / (2 * ((qh : ℚ) : ℝ)) ≤ Real.pi / (2 * Real.sqrt ((t : ℚ) : ℝ)) := by
      have hq0 : (0:ℝ) < 2 * ((qh : ℚ) : ℝ) := by
        have h1 : (0:ℝ) < ((qh : ℚ) : ℝ) := lt_of_lt_of_le hqlR (by exact_mod_cast hqlqh)
        linarith
      have hs0 : (0:ℝ) < 2 * Real.sqrt ((t : ℚ) : ℝ) := by linarith [hsp]
      rw [le_div_iff₀ hs0, div_mul_eq_mul_div, div_le_iff₀ hq0]
      nlinarith [hPI.1, hshi, hqhR, htR, Real.pi_pos]
    have h2 : matan (1 / ((t : ℚ) : ℝ)) / ((t : ℚ) : ℝ) ≤ M.hi / ((t : ℚ) : ℝ) :=
      div_le_div_of_nonneg_right hM'.2 htR.le
    have hexp : ((PMir t ql qh M).lo : ℝ) = (lkPIlo : ℝ) / (2 * ((qh : ℚ) : ℝ))
        - (M.hi : ℝ) / ((t : ℚ) : ℝ) := by
      simp only [PMir, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    rw [hexp]
    linarith
  · have h1 : Real.pi / (2 * Real.sqrt ((t : ℚ) : ℝ)) ≤ (lkPIhi : ℝ) / (2 * ((ql : ℚ) : ℝ)) := by
      have hqs0 : (0:ℝ) < 2 * Real.sqrt ((t : ℚ) : ℝ) := by linarith [hsp]
      have hl0 : (0:ℝ) < 2 * ((ql : ℚ) : ℝ) := by linarith [hqlR]
      rw [div_le_iff₀ hqs0, div_mul_eq_mul_div, le_div_iff₀ hl0]
      nlinarith [hPI.2, hslo, hqlR, hqlR.le]
    have h2 : (M.lo : ℝ) / ((t : ℚ) : ℝ) ≤ matan (1 / ((t : ℚ) : ℝ)) / ((t : ℚ) : ℝ) :=
      div_le_div_of_nonneg_right hM'.1 htR.le
    have hexp : ((PMir t ql qh M).hi : ℝ) = (lkPIhi : ℝ) / (2 * ((ql : ℚ) : ℝ))
        - (M.lo : ℝ) / ((t : ℚ) : ℝ) := by
      simp only [PMir, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    rw [hexp]
    linarith

theorem DDp_mem {t : ℚ} {P : QInterval} (ht : (0:ℚ) < t)
    (hP : P.mem (matan ((t : ℚ) : ℝ))) :
    (DDp t P).mem (matanDD ((t : ℚ) : ℝ)) := by
  unfold DDp gE gDp
  exact lk_matanDD_pt_mem t P _ _ ht hP rfl rfl

/-- Assemble a `matan` `UnaryBox` on `I` from the two endpoint value brackets
and the two endpoint `matanDD` brackets. -/
def matanBoxOf (I : QInterval) (hI : 0 < I.lo) (ho : I.lo ≤ I.hi)
    (Plo Phi Dl Dh : QInterval)
    (hPlo : Plo.mem (matan ((I.lo : ℚ) : ℝ)))
    (hPhi : Phi.mem (matan ((I.hi : ℚ) : ℝ)))
    (hDl : Dl.mem (matanDD ((I.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((I.hi : ℚ) : ℝ))) :
    UnaryBox matan I :=
  matanUnaryBox I (gM Plo Phi) (gMD I (gM Plo Phi)) (gMDD Dl Dh) hI
    (fun t ht => g_m_vf I Plo Phi hI hPlo hPhi t ht.1 ht.2)
    (fun t ht => g_mD_vf I (gM Plo Phi) hI ho
      (fun s hs1 hs2 => g_m_vf I Plo Phi hI hPlo hPhi s hs1 hs2) t ht.1 ht.2)
    hDh.1 hDl.2

/-- Direct-branch slot box (both endpoints in `(0, 1]`). -/
def matanBoxD9 (I : QInterval) (hI : 0 < I.lo) (ho : I.lo ≤ I.hi) :
    UnaryBox matan I :=
  matanBoxOf I hI ho (P9 I.lo) (P9 I.hi) (DDp I.lo (P9 I.lo)) (DDp I.hi (P9 I.hi))
    (P9_mem hI) (P9_mem (lt_of_lt_of_le hI ho))
    (DDp_mem hI (P9_mem hI))
    (DDp_mem (lt_of_lt_of_le hI ho) (P9_mem (lt_of_lt_of_le hI ho)))

/-- u-form slot box (`1 < I.lo`). -/
def matanBoxU9 (I : QInterval) (hI : (1:ℚ) < I.lo) (ho : I.lo ≤ I.hi)
    (qlLo qhLo qlHi qhHi : ℚ)
    (c1 : ((qlLo : ℚ) : ℝ) ^ 2 ≤ ((I.lo : ℚ) : ℝ))
    (c2 : ((I.lo : ℚ) : ℝ) ≤ ((qhLo : ℚ) : ℝ) ^ 2)
    (c3 : (0:ℚ) < qlLo) (c4 : qlLo ≤ qhLo) (c5 : (1:ℚ) ≤ qhLo) (c6 : (1:ℚ) ≤ qlLo)
    (c7 : ((qlHi : ℚ) : ℝ) ^ 2 ≤ ((I.hi : ℚ) : ℝ))
    (c8 : ((I.hi : ℚ) : ℝ) ≤ ((qhHi : ℚ) : ℝ) ^ 2)
    (c9 : (0:ℚ) < qlHi) (c10 : qlHi ≤ qhHi) (c11 : (1:ℚ) ≤ qhHi) (c12 : (1:ℚ) ≤ qlHi) :
    UnaryBox matan I :=
  matanBoxOf I (lt_trans (by norm_num : (0:ℚ) < 1) hI) ho
    (PU9 qlLo qhLo) (PU9 qlHi qhHi) (DDp I.lo (PU9 qlLo qhLo)) (DDp I.hi (PU9 qlHi qhHi))
    (PU9_mem hI c1 c2 c3 c4 c5 c6)
    (PU9_mem (lt_of_lt_of_le hI ho) c7 c8 c9 c10 c11 c12)
    (DDp_mem (lt_trans (by norm_num : (0:ℚ) < 1) hI) (PU9_mem hI c1 c2 c3 c4 c5 c6))
    (DDp_mem (lt_of_lt_of_le (lt_trans (by norm_num : (0:ℚ) < 1) hI) ho)
      (PU9_mem (lt_of_lt_of_le hI ho) c7 c8 c9 c10 c11 c12))

/-- Mirror-branch slot box (`0 < I.lo`, `I.hi < 1`, inner `wplus` brackets). -/
def matanBoxMir (I : QInterval) (hI : 0 < I.lo) (ho : I.lo ≤ I.hi) (hhi : I.hi < 1)
    (qlLo qhLo qlHi qhHi : ℚ)
    (o1 : ((qlLo : ℚ) : ℝ) ^ 2 ≤ ((I.lo : ℚ) : ℝ))
    (o2 : ((I.lo : ℚ) : ℝ) ≤ ((qhLo : ℚ) : ℝ) ^ 2)
    (o3 : (0:ℚ) < qlLo) (o4 : qlLo ≤ qhLo)
    (o5 : ((qlHi : ℚ) : ℝ) ^ 2 ≤ ((I.hi : ℚ) : ℝ))
    (o6 : ((I.hi : ℚ) : ℝ) ≤ ((qhHi : ℚ) : ℝ) ^ 2)
    (o7 : (0:ℚ) < qlHi) (o8 : qlHi ≤ qhHi)
    (slLo shLo slHi shHi : ℚ)
    (i1 : (1:ℚ) < 1 / I.lo) (i2 : ((slLo : ℚ) : ℝ) ^ 2 ≤ (((1 / I.lo : ℚ)) : ℝ))
    (i3 : (((1 / I.lo : ℚ)) : ℝ) ≤ ((shLo : ℚ) : ℝ) ^ 2)
    (i4 : (0:ℚ) < slLo) (i5 : slLo ≤ shLo) (i6 : (1:ℚ) ≤ shLo) (i7 : (shLo : ℚ) < 1 + slLo)
    (i8 : (1:ℚ) ≤ slLo)
    (j1 : (1:ℚ) < 1 / I.hi) (j2 : ((slHi : ℚ) : ℝ) ^ 2 ≤ (((1 / I.hi : ℚ)) : ℝ))
    (j3 : (((1 / I.hi : ℚ)) : ℝ) ≤ ((shHi : ℚ) : ℝ) ^ 2)
    (j4 : (0:ℚ) < slHi) (j5 : slHi ≤ shHi) (j6 : (1:ℚ) ≤ shHi) (j7 : (shHi : ℚ) < 1 + slHi)
    (j8 : (1:ℚ) ≤ slHi) :
    UnaryBox matan I :=
  matanBoxOf I hI ho (PMir I.lo qlLo qhLo (PWp slLo shLo))
    (PMir I.hi qlHi qhHi (PWp slHi shHi))
    (DDp I.lo (PMir I.lo qlLo qhLo (PWp slLo shLo)))
    (DDp I.hi (PMir I.hi qlHi qhHi (PWp slHi shHi)))
    (PMir_mem _ hI o3 o4 o1 o2 (PWp_mem i1 i2 i3 i4 i5 i6 i7 i8))
    (PMir_mem _ (lt_of_lt_of_le hI ho) o7 o8 o5 o6 (PWp_mem j1 j2 j3 j4 j5 j6 j7 j8))
    (DDp_mem hI (PMir_mem _ hI o3 o4 o1 o2 (PWp_mem i1 i2 i3 i4 i5 i6 i7 i8)))
    (DDp_mem (lt_of_lt_of_le hI ho)
      (PMir_mem _ (lt_of_lt_of_le hI ho) o7 o8 o5 o6 (PWp_mem j1 j2 j3 j4 j5 j6 j7 j8)))

#print axioms PMir_mem
#print axioms matanBoxOf
#print axioms matanBoxD9
#print axioms matanBoxU9
#print axioms matanBoxMir

/-! ## 9. Audit -/

#print axioms partial1_coord
#print axioms partial2_coord
#print axioms coordJet
#print axioms constJet
#print axioms W1Leaf.c_mem
#print axioms W1Leaf.seg_mem
#print axioms W1Leaf.w_abs
#print axioms fDlt_eq
#print axioms fA_eq
#print axioms fTA_eq
#print axioms fGA_eq
#print axioms fWA_eq
#print axioms fK1_eq
#print axioms fLf5_eq
#print axioms w1F3_eq_w1F3Z
#print axioms w1F3_eq_w1F3O
#print axioms w1F3_eq_ite
#print axioms w1F3Z_pos_of_slack
#print axioms w1F3Z_pos_of_value
#print axioms w1F3Z_pos_of_slack2

end

end Kepler.Text.TaylorSecond
