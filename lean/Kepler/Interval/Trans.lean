/-
  Phase 4, step 4: **transcendental bounds** — verified alternating Taylor
  estimates for `sin` on `[0, 1]`, packaged as dyadic intervals / balls.

  Following the "Next steps" note in `Basic.lean`: transcendental functions
  enter as *"dyadic value + dyadic radius"* rather than as exact endpoints.

  ## The real (semantic) layer

  `abs_sub_partial_le` is the classical **Leibniz alternating-series bound**:
  for `a : ℕ → ℝ` antitone with `a i ≥ 0`, if `∑ (-1)^i a i = S` then
  `|S − ∑_{i<n} (-1)^i a i| ≤ a n`.  Proof (self-contained):
  the *peeled tail* `altTail n k = ∑_{j<k} (-1)^j a (n+j)` satisfies
  `0 ≤ altTail n k ≤ a n` by paired induction — the peel identity
  `altTail n (k+2) = a n − altTail (n+1) (k+1)` avoids the parity juggling of
  single-step induction — and passing to the limit along
  `HasSum.tendsto_sum_nat` of the shifted series (`hasSum_nat_add_iff`) gives
  the signed tail bound `0 ≤ (−1)^n (S − s_n) ≤ a n`.

  `sin_abs_sub_partial_le` instantiates this with Mathlib's `Real.hasSum_sin`
  (valid for all `x`; the terms are antitone for `x ∈ [0, 1]` — **range
  reduction beyond `[0,1]` is not done here**; future work would first reduce
  `x` by periodicity/symmetry into `[0, 1]` and then apply `sinInterval`).

  ## The checked (dyadic) layer

  `taylorIter` accumulates outward-rounded partial sums: the term `x^(2i+1)`
  (exact dyadic `npow`) is divided by `(2i+1)!` via `Dyadic.divFloorQ`
  (mantissa floor for the lower sum, `+ one ulp` for the upper sum,
  sign-adjusted by parity of `i`), all in `Int` — kernel `decide` evaluates
  the whole loop.  The alternating remainder `a N ≤ 1/(2N+1)!` (for `x ≤ 1`)
  is likewise rounded up through `divFloorQ 1 ((2N+1)!)`.  `sinInterval`
  wraps loop + remainder; `sinBall` repackages via `DInterval.midRadius`
  (the "dyadic value + dyadic radius" interface of `Ball.lean`).

  Checking layer: `Int` only. No `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.Div
import Kepler.Interval.Ball

namespace Kepler.Interval

/-! ## Dyadic natural powers -/

namespace Dyadic

/-- Exact dyadic power (repeated multiplication). -/
def npow (x : Dyadic) : ℕ → Dyadic
  | 0 => ⟨1, 0⟩
  | n + 1 => x.mul (x.npow n)

theorem toReal_npow (x : Dyadic) (n : ℕ) : (x.npow n).toReal = x.toReal ^ n := by
  induction n with
  | zero => simp [npow, toReal_def]
  | succ m ih =>
    show Dyadic.toReal (x.mul (x.npow m)) = x.toReal ^ (m + 1)
    rw [toReal_mul, ih, pow_succ]
    ring

end Dyadic

/-! ## The alternating-series (Leibniz) tail bound, over `ℝ` -/

section Alternating

variable (a : ℕ → ℝ)

/-- The peeled alternating tail: `altTail n k = ∑_{j<k} (-1)^j a (n+j)`. -/
private def altTail (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1:ℝ)^j * a (n + j)

private theorem altTail_zero (n : ℕ) : altTail a n 0 = 0 := by
  simp [altTail]

private theorem altTail_one (n : ℕ) : altTail a n 1 = a n := by
  simp [altTail]

private theorem altTail_peel (n k : ℕ) :
    altTail a n (k + 2) = a n - altTail a (n + 1) (k + 1) := by
  simp only [altTail]
  rw [Finset.sum_range_succ']
  have hterm : ∀ j : ℕ, (-1:ℝ)^(j+1) * a (n + (j+1))
      = -((-1:ℝ)^j * a (n + 1 + j)) := by
    intro j
    rw [pow_succ]
    have hidx : n + (j + 1) = n + 1 + j := by omega
    rw [hidx]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_neg_distrib]
  simp
  ring

/-- Paired-induction core: both parities of tail length are bounded. -/
private theorem altTail_bounds_pair (ha : Antitone a) (hann : ∀ i, 0 ≤ a i) (m n : ℕ) :
    0 ≤ altTail a n (2*m) ∧ altTail a n (2*m) ≤ a n ∧
      0 ≤ altTail a n (2*m+1) ∧ altTail a n (2*m+1) ≤ a n := by
  induction m generalizing n with
  | zero =>
    rw [altTail_zero, altTail_one]
    exact ⟨le_refl 0, hann n, hann n, le_refl (a n)⟩
  | succ m ih =>
    have han : ∀ n, a (n + 1) ≤ a n := fun n => ha (Nat.le_succ n)
    have evenH : ∀ n, 0 ≤ altTail a n (2*(m+1)) ∧ altTail a n (2*(m+1)) ≤ a n := by
      intro n
      rw [show 2*(m+1) = 2*m + 2 from by omega, altTail_peel]
      obtain ⟨_, _, h0'', h1''⟩ := ih (n + 1)
      exact ⟨by linarith [h1'', han n], by linarith [h0'']⟩
    have oddH : 0 ≤ altTail a n (2*(m+1)+1) ∧ altTail a n (2*(m+1)+1) ≤ a n := by
      rw [show 2*(m+1)+1 = 2*m + 1 + 2 from by omega, altTail_peel]
      have hEven' : 0 ≤ altTail a (n + 1) ((2*m+1) + 1)
          ∧ altTail a (n + 1) ((2*m+1) + 1) ≤ a (n + 1) := by
        rw [show (2*m+1) + 1 = 2*(m+1) from by omega]
        exact evenH (n + 1)
      exact ⟨by linarith [hEven'.2, han n], by linarith [hEven'.1]⟩
    exact ⟨(evenH n).1, (evenH n).2, oddH.1, oddH.2⟩

/-- The Leibniz tail bound: `0 ≤ ∑_{j<k} (-1)^j a (n+j) ≤ a n` for antitone
nonnegative `a`. -/
private theorem altTail_bounds (ha : Antitone a) (hann : ∀ i, 0 ≤ a i) (k n : ℕ) :
    0 ≤ altTail a n k ∧ altTail a n k ≤ a n := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [← two_mul m]
    exact ⟨(altTail_bounds_pair a ha hann m n).1, (altTail_bounds_pair a ha hann m n).2.1⟩
  · subst hm
    exact ⟨(altTail_bounds_pair a ha hann m n).2.2.1, (altTail_bounds_pair a ha hann m n).2.2.2⟩

end Alternating

/-- **Leibniz alternating-series bound** (semantic layer, over `ℝ`): if
`a` is antitone and nonnegative and `∑ (-1)^i a i = S`, then every partial
sum approximates `S` with error at most the next term. -/
theorem abs_sub_partial_le {a : ℕ → ℝ} (ha : Antitone a) (hann : ∀ i, 0 ≤ a i)
    {S : ℝ} (h : HasSum (fun i => (-1:ℝ)^i * a i) S) (n : ℕ) :
    |S - ∑ i ∈ Finset.range n, (-1:ℝ)^i * a i| ≤ a n := by
  have hta : HasSum (fun m => (-1:ℝ)^(m+n) * a (m+n))
      (S - ∑ i ∈ Finset.range n, (-1:ℝ)^i * a i) := by
    have h2 : HasSum (fun i => (-1:ℝ)^i * a i)
        ((S - ∑ i ∈ Finset.range n, (-1:ℝ)^i * a i)
          + ∑ i ∈ Finset.range n, (-1:ℝ)^i * a i) := by
      rw [sub_add_cancel]
      exact h
    exact (hasSum_nat_add_iff n).mpr h2
  have htend := (hta.tendsto_sum_nat).const_mul ((-1:ℝ)^n)
  have hrel : ∀ m : ℕ, ((-1:ℝ)^n) * (∑ i ∈ Finset.range m, (-1:ℝ)^(i+n) * a (i+n))
      = altTail a n m := by
    intro m
    rw [Finset.mul_sum]
    have hterm : ∀ i : ℕ, ((-1:ℝ)^n) * ((-1:ℝ)^(i+n) * a (i+n))
        = (-1:ℝ)^i * a (n+i) := by
      intro i
      have h2n : ((-1:ℝ)^(2*n)) = 1 := by
        rw [pow_mul]
        norm_num
      calc ((-1:ℝ)^n) * ((-1:ℝ)^(i+n) * a (i+n))
          = ((-1:ℝ)^(i+n) * (-1:ℝ)^n) * a (i+n) := by ring
        _ = ((-1:ℝ)^(i+n+n)) * a (i+n) := by rw [← pow_add]
        _ = ((-1:ℝ)^(i+2*n)) * a (i+n) := by rw [show i+n+n = i+2*n from by omega]
        _ = ((-1:ℝ)^i * (-1:ℝ)^(2*n)) * a (i+n) := by rw [pow_add]
        _ = ((-1:ℝ)^i) * a (i+n) := by rw [h2n, mul_one]
        _ = ((-1:ℝ)^i) * a (n+i) := by rw [Nat.add_comm i n]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rfl
  have hb : ∀ m : ℕ,
      0 ≤ ((-1:ℝ)^n) * (∑ i ∈ Finset.range m, (-1:ℝ)^(i+n) * a (i+n)) ∧
      ((-1:ℝ)^n) * (∑ i ∈ Finset.range m, (-1:ℝ)^(i+n) * a (i+n)) ≤ a n := by
    intro m
    rw [hrel m]
    exact altTail_bounds a ha hann m n
  have hL0 := ge_of_tendsto htend (Filter.Eventually.of_forall (fun m => (hb m).1))
  have hL1 := le_of_tendsto htend (Filter.Eventually.of_forall (fun m => (hb m).2))
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn1 : (-1:ℝ)^n = 1 := by
      rw [hm, ← two_mul m, pow_mul]
      norm_num
    rw [hn1, one_mul] at hL0 hL1
    rw [abs_of_nonneg hL0]
    exact hL1
  · have hn1 : (-1:ℝ)^n = -1 := by
      rw [hm, pow_succ, pow_mul]
      norm_num
    rw [hn1, neg_one_mul] at hL0 hL1
    rw [abs_of_nonpos (by linarith)]
    exact hL1

/-! ## `sin` on `[0, 1]`: alternating Taylor with explicit remainder -/

/-- The Taylor coefficients of `sin` are antitone on `[0, 1]`. -/
private theorem sin_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun i => x^(2*i+1)/((Nat.factorial (2*i+1) : ℕ):ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro i
  have hf : ((Nat.factorial (2*i+3 : ℕ) : ℕ):ℝ)
      = ((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ) * ((2*i+3 : ℕ):ℝ) := by
    have h1 : ((2*i+3 : ℕ)).factorial = ((2*i+1 : ℕ)).factorial * ((2*i+2 : ℕ)) * ((2*i+3 : ℕ)) := by
      rw [show (2*i+3 : ℕ) = (2*i+2) + 1 from by omega, Nat.factorial_succ,
        show (2*i+2 : ℕ) = (2*i+1) + 1 from by omega, Nat.factorial_succ]
      ring
    exact_mod_cast h1
  show x^(2*(i+1)+1)/((Nat.factorial (2*(i+1)+1 : ℕ) : ℕ):ℝ)
    ≤ x^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)
  rw [show 2*(i+1)+1 = 2*i+3 from by omega, hf]
  have hx2 : x * x ≤ 1 := by nlinarith
  have hden : (1:ℝ) ≤ ((2*i+2 : ℕ):ℝ) * ((2*i+3 : ℕ):ℝ) := by
    have ha1 : (1:ℕ) ≤ (2*i+2) := by omega
    have ha2 : (1:ℕ) ≤ (2*i+3) := by omega
    have hle : (1:ℕ) ≤ (2*i+2) * (2*i+3) := Nat.mul_le_mul ha1 ha2
    exact_mod_cast hle
  have hp : (0:ℝ) ≤ x^(2*i+1) := pow_nonneg hx0 _
  have h1 : x * x * x^(2*i+1) ≤ 1 * x^(2*i+1) := mul_le_mul_of_nonneg_right hx2 hp
  have h2 : x^(2*i+1) * 1
      ≤ x^(2*i+1) * (((2*i+2 : ℕ):ℝ) * ((2*i+3 : ℕ):ℝ)) := mul_le_mul_of_nonneg_left hden hp
  have h3 : x^(2*i+3) = x * x * x^(2*i+1) := by ring
  have hfa : (0:ℝ) < ((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) := by positivity
  have hfb : (0:ℝ) < ((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ) * ((2*i+3 : ℕ):ℝ) := by
    positivity
  rw [div_le_iff₀ hfb, div_mul_eq_mul_div, le_div_iff₀ hfa]
  rw [h3]
  nlinarith [h1, h2, hfa, hden, hp]

/-- **Explicit Taylor remainder for `sin` on `[0,1]`** (semantic layer): the
partial alternating sum misses `sin x` by at most the next term. -/
theorem sin_abs_sub_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |Real.sin x - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)|
      ≤ x^(2*n+1)/((Nat.factorial (2*n+1 : ℕ) : ℕ):ℝ) := by
  have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ))
      = ((-1:ℝ)^i * x^(2*i+1))/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) := by
    intro i
    rw [mul_div_assoc']
  have hsumEq : (∑ i ∈ Finset.range n, (-1:ℝ)^i * (x^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)))
      = ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) :=
    Finset.sum_congr rfl (fun i _ => hcongr i)
  have h := abs_sub_partial_le (sin_terms_antitone hx0 hx1)
    (fun i => div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    (by simpa only [← hcongr] using Real.hasSum_sin x) n
  rwa [hsumEq] at h

/-! ## The checked Taylor loop (generic in term / denominator) -/

/-- One mantissa step above `q` is one ulp above `q.toReal` (when `q.e = out`). -/
private theorem toReal_succ_ulp {q : Dyadic} {out : Int} (hq : q.e = out) :
    Dyadic.toReal ⟨q.m + 1, out⟩ = q.toReal + (Dyadic.ulp out).toReal := by
  rw [Dyadic.toReal_def, Dyadic.toReal_def, Dyadic.toReal_ulp, hq]
  push_cast
  ring

/-- Generic outward-rounded alternating Taylor accumulator: for `fuel` steps
from index `i` on, divide `term j` by the integer `den j` at granularity
`2^out` (`divFloorQ`), adding the floor to the lower bound and the
one-ulp-up value to the upper bound when `j` is even, and the reverse when
`j` is odd.  All arithmetic in `Int`; kernel-evaluable by `decide`. -/
def taylorIter (term : ℕ → Dyadic) (den : ℕ → ℤ) (out : Int) :
    ℕ → ℕ → Dyadic → Dyadic → Option (Dyadic × Dyadic)
  | 0, _, lw, hg => some (lw, hg)
  | fuel + 1, i, lw, hg =>
      match Dyadic.divFloorQ (term i) ⟨den i, 0⟩ out with
      | none => none
      | some q =>
          if i % 2 = 0 then
            taylorIter term den out fuel (i + 1) (lw.add q) (hg.add ⟨q.m + 1, out⟩)
          else
            taylorIter term den out fuel (i + 1) (lw.dsub ⟨q.m + 1, out⟩) (hg.dsub q)

/-- **Soundness of `taylorIter`**: if every rounded term brackets `A j`, the
final `(lw, hg)` brackets the alternating partial sum of `A`. -/
theorem taylorIter_spec (term : ℕ → Dyadic) (den : ℕ → ℤ) (out : Int) (A : ℕ → ℝ)
    (hA : ∀ i (q : Dyadic), Dyadic.divFloorQ (term i) ⟨den i, 0⟩ out = some q →
      q.toReal ≤ A i ∧ A i ≤ Dyadic.toReal ⟨q.m + 1, out⟩) :
    ∀ (fuel i : ℕ) (lw hg : Dyadic),
      lw.toReal ≤ ∑ j ∈ Finset.range i, (-1:ℝ)^j * A j →
      ∑ j ∈ Finset.range i, (-1:ℝ)^j * A j ≤ hg.toReal →
      ∀ res, taylorIter term den out fuel i lw hg = some res →
      ((res.1).toReal ≤ ∑ j ∈ Finset.range (i + fuel), (-1:ℝ)^j * A j ∧
        ∑ j ∈ Finset.range (i + fuel), (-1:ℝ)^j * A j ≤ (res.2).toReal) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i lw hg hlo hhi res h
    obtain rfl : res = (lw, hg) := (Option.some.inj (show some (lw, hg) = some res from h)).symm
    rw [Nat.add_zero]
    exact ⟨hlo, hhi⟩
  | succ fuel ih =>
    intro i lw hg hlo hhi res h
    have hstep : (match Dyadic.divFloorQ (term i) ⟨den i, 0⟩ out with
        | none => none
        | some q =>
            if i % 2 = 0 then
              taylorIter term den out fuel (i + 1) (lw.add q) (hg.add ⟨q.m + 1, out⟩)
            else
              taylorIter term den out fuel (i + 1) (lw.dsub ⟨q.m + 1, out⟩) (hg.dsub q))
        = some res := h
    cases hq : Dyadic.divFloorQ (term i) ⟨den i, 0⟩ out with
    | none => rw [hq] at hstep; simp at hstep
    | some q =>
      rw [hq] at hstep
      obtain ⟨hq1, hq2⟩ := hA i q hq
      have hU : Dyadic.toReal ⟨q.m + 1, out⟩ = q.toReal + (Dyadic.ulp out).toReal :=
        toReal_succ_ulp (Dyadic.divFloorQ_e hq)
      have hstep' : (if i % 2 = 0 then
            taylorIter term den out fuel (i + 1) (lw.add q) (hg.add ⟨q.m + 1, out⟩)
          else
            taylorIter term den out fuel (i + 1) (lw.dsub ⟨q.m + 1, out⟩) (hg.dsub q))
          = some res := hstep
      rw [show i + (fuel + 1) = (i + 1) + fuel from by omega]
      by_cases hmod : i % 2 = 0
      · rw [if_pos hmod] at hstep'
        have hn1 : (-1:ℝ)^i = 1 := by
          rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
          · rw [hk, ← two_mul k, pow_mul]
            norm_num
          · exact absurd hk (by omega)
        have hsucc : ∑ j ∈ Finset.range (i + 1), (-1:ℝ)^j * A j
            = (∑ j ∈ Finset.range i, (-1:ℝ)^j * A j) + A i := by
          rw [Finset.sum_range_succ, hn1, one_mul]
        exact ih (i + 1) (lw.add q) (hg.add ⟨q.m + 1, out⟩)
          (by rw [Dyadic.toReal_add, hsucc]
              exact add_le_add hlo hq1)
          (by rw [Dyadic.toReal_add, hsucc]
              exact add_le_add hhi hq2)
          res hstep'
      · rw [if_neg hmod] at hstep'
        have hn1 : (-1:ℝ)^i = -1 := by
          rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
          · exact absurd hk (by omega)
          · rw [hk, pow_succ, pow_mul]
            norm_num
        have hsucc : ∑ j ∈ Finset.range (i + 1), (-1:ℝ)^j * A j
            = (∑ j ∈ Finset.range i, (-1:ℝ)^j * A j) - A i := by
          rw [Finset.sum_range_succ, hn1, neg_one_mul]
          ring
        exact ih (i + 1) (lw.dsub ⟨q.m + 1, out⟩) (hg.dsub q)
          (by rw [Dyadic.toReal_dsub, hU, hsucc]
              linarith [hlo, hq2])
          (by rw [Dyadic.toReal_dsub, hsucc]
              linarith [hhi, hq1])
          res hstep'

/-! ## `sinInterval` / `sinBall` -/

/-- Interval enclosure of `sin x.toReal` for `x.toReal ∈ [0, 1]`:
`N` alternating Taylor terms with outward per-term rounding at granularity
`2^out`, plus the one-ulp-up rounded remainder bound `1/(2N+1)!`. -/
def sinInterval (x : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  match taylorIter (fun i => x.npow (2*i+1)) (fun i => (Nat.factorial (2*i+1) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => none
  | some (lw, hg) =>
      match Dyadic.divFloorQ ⟨1, 0⟩ ⟨(Nat.factorial (2*N+1) : ℤ), 0⟩ out with
      | none => none
      | some u => some ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩

/-- **Soundness of `sinInterval`** (over `ℝ`): on `0 ≤ x.toReal ≤ 1`, the
returned interval contains `sin` of the real semantics. -/
theorem sinInterval_sound {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : sinInterval x N out = some I) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1) :
    I.lo.toReal ≤ Real.sin x.toReal ∧ Real.sin x.toReal ≤ I.hi.toReal := by
  simp only [sinInterval] at h
  cases hloop : taylorIter (fun i => x.npow (2*i+1)) (fun i => (Nat.factorial (2*i+1) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => rw [hloop] at h; simp at h
  | some lr =>
    obtain ⟨lw, hg⟩ := lr
    rw [hloop] at h
    cases hu : Dyadic.divFloorQ ⟨1, 0⟩ ⟨(Nat.factorial (2*N+1) : ℤ), 0⟩ out with
    | none => rw [hu] at h; simp at h
    | some u =>
      rw [hu] at h
      obtain rfl : I = ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩ :=
        (Option.some.inj h).symm
      -- the real coefficients and their dyadic brackets
      have hA : ∀ i (q : Dyadic),
          Dyadic.divFloorQ (x.npow (2*i+1)) ⟨(Nat.factorial (2*i+1) : ℤ), 0⟩ out = some q →
          q.toReal ≤ x.toReal^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) ∧
            x.toReal^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)
              ≤ Dyadic.toReal ⟨q.m + 1, out⟩ := by
        intro i q hq
        obtain ⟨hs1, hs2⟩ := Dyadic.divFloorQ_spec hq
        rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hs1 hs2
        exact ⟨hs1, hs2⟩
      have hbase : (⟨0, 0⟩ : Dyadic).toReal
          = ∑ j ∈ Finset.range 0, (-1:ℝ)^j * (fun i => x.toReal^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)) j := by
        rw [Dyadic.toReal_def]
        simp
      obtain ⟨hs1, hs2⟩ :=
        taylorIter_spec (fun i => x.npow (2*i+1)) (fun i => (Nat.factorial (2*i+1) : ℤ)) out
          (fun i => x.toReal^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ)) hA
          N 0 ⟨0, 0⟩ ⟨0, 0⟩
          (by rw [← hbase]) (by rw [← hbase]) ⟨lw, hg⟩ hloop
      -- the remainder bracket
      obtain ⟨_, hu2⟩ := Dyadic.divFloorQ_spec hu
      rw [Dyadic.toReal_int, Dyadic.toReal_int] at hu2
      push_cast at hu2
      have hU : Dyadic.toReal ⟨u.m + 1, out⟩ = u.toReal + (Dyadic.ulp out).toReal :=
        toReal_succ_ulp (Dyadic.divFloorQ_e hu)
      have hfactpos : (0:ℝ) < ((Nat.factorial (2*N+1 : ℕ) : ℕ):ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      -- `A N ≤ 1/(2N+1)! ≤ ⟨u.m + 1, out⟩`
      have hxpow : x.toReal^(2*N+1) ≤ 1 := by
        calc x.toReal^(2*N+1) ≤ x.toReal^1 :=
              pow_le_pow_of_le_one hx0 hx1 (by omega)
          _ = x.toReal := by ring
          _ ≤ 1 := hx1
      have key : x.toReal^(2*N+1)/((Nat.factorial (2*N+1 : ℕ) : ℕ):ℝ)
          ≤ 1/((Nat.factorial (2*N+1 : ℕ) : ℕ):ℝ) := by
        rw [le_div_iff₀ hfactpos, div_mul_cancel₀ _ (ne_of_gt hfactpos)]
        exact hxpow
      have hAN : x.toReal^(2*N+1)/((Nat.factorial (2*N+1 : ℕ) : ℕ):ℝ)
          ≤ Dyadic.toReal ⟨u.m + 1, out⟩ := le_trans key hu2
      -- assemble
      have hsin := sin_abs_sub_partial_le hx0 hx1 N
      rw [abs_le] at hsin
      rw [Nat.zero_add] at hs1 hs2
      have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x.toReal^(2*i+1)/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ))
          = ((-1:ℝ)^i * x.toReal^(2*i+1))/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) := by
        intro i
        rw [mul_div_assoc']
      have hsumEq : (∑ j ∈ Finset.range N, (-1:ℝ)^j * (x.toReal^(2*j+1)/((Nat.factorial (2*j+1 : ℕ) : ℕ):ℝ)))
          = ∑ i ∈ Finset.range N, ((-1:ℝ)^i * x.toReal^(2*i+1))/((Nat.factorial (2*i+1 : ℕ) : ℕ):ℝ) :=
        Finset.sum_congr rfl (fun j _ => hcongr j)
      rw [hsumEq] at hs1 hs2
      constructor
      · show Dyadic.toReal (lw.dsub ⟨u.m + 1, out⟩) ≤ Real.sin x.toReal
        rw [Dyadic.toReal_dsub, hU]
        linarith [hs1, hsin.1, hAN]
      · show Real.sin x.toReal ≤ Dyadic.toReal (hg.add ⟨u.m + 1, out⟩)
        rw [Dyadic.toReal_add]
        linarith [hs2, hsin.2, hAN]

/-- `sin` as a midpoint-radius ball (the "dyadic value + dyadic radius"
packaging recommended by `Basic.lean`'s "Next steps" note). -/
def sinBall (x : Dyadic) (N : ℕ) (out : Int) : Option Ball :=
  match sinInterval x N out with
  | some I => some I.midRadius
  | none => none

/-- **Soundness of `sinBall`**: on `0 ≤ x.toReal ≤ 1`, the ball contains
`sin` of the real semantics. -/
theorem sinBall_sound {x : Dyadic} {N : ℕ} {out : Int} {b : Ball}
    (h : sinBall x N out = some b) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1) :
    b.mem (Real.sin x.toReal) := by
  simp only [sinBall] at h
  cases hI : sinInterval x N out with
  | none => rw [hI] at h; simp at h
  | some I =>
    rw [hI] at h
    obtain rfl : b = I.midRadius := (Option.some.inj h).symm
    obtain ⟨hs1, hs2⟩ := sinInterval_sound hI hx0 hx1
    exact I.mem_midRadius ⟨hs1, hs2⟩

/-! ## Pilot: `sin(1/2) > 0.4794` (kernel `decide` only) -/

/-- The checked certificate: five alternating Taylor terms of `sin` at
`x = 1/2`, outward-rounded at granularity `2^-20`, plus the one-ulp-up
remainder `1/11!` — all computed by kernel `decide` (the mantissas stay
below `2^24`). -/
theorem sinPilot_cert :
    sinInterval ⟨1, -1⟩ 5 (-20) = some ⟨⟨502712, -20⟩, ⟨502719, -20⟩⟩ := by
  decide

/-- End-to-end real statement: `0.4794 < sin(1/2)` (the true value is
`0.4794255…`). -/
theorem sinPilot_real : (2397:ℝ)/5000 < Real.sin ((1:ℝ)/2) := by
  have hx0 : (0:ℝ) ≤ Dyadic.toReal ⟨1, -1⟩ := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx1 : Dyadic.toReal ⟨1, -1⟩ ≤ 1 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx : Dyadic.toReal ⟨1, -1⟩ = (1:ℝ)/2 := by
    rw [Dyadic.toReal_def]
    norm_num
  obtain ⟨h1, _⟩ := sinInterval_sound sinPilot_cert hx0 hx1
  rw [hx, Dyadic.toReal_def] at h1
  dsimp only at h1
  have hlo : (((502712:Int):ℝ)) * (2:ℝ)^((-20:Int)) = ((502712:Int):ℝ)/1048576 := by
    rw [show ((2:ℝ)^((-20:Int))) = 1/((1048576:ℝ)) from by norm_num, mul_one_div]
  rw [hlo] at h1
  have hnum : (2397:ℝ)/5000 < ((502712:Int):ℝ)/1048576 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1048576), div_mul_eq_mul_div,
      div_lt_iff₀ (by norm_num : (0:ℝ) < 5000)]
    norm_num
  exact lt_of_lt_of_le hnum h1

/-- The ball packaging of the same computation: center `1005431/2^21` ≈
`0.4794254` with radius `7/2^21` (kernel `decide`). -/
theorem sinBallPilot :
    sinBall ⟨1, -1⟩ 5 (-20) = some ⟨⟨1005431, -21⟩, ⟨7, -21⟩⟩ := by
  decide

/-- End-to-end ball statement over `ℝ`: `|sin(1/2) − 1005431/2^21| ≤ 7/2^21`. -/
theorem sinBallPilot_real :
    |Real.sin ((1:ℝ)/2) - (1005431:ℝ)/2097152| ≤ (7:ℝ)/2097152 := by
  have hx0 : (0:ℝ) ≤ Dyadic.toReal ⟨1, -1⟩ := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx1 : Dyadic.toReal ⟨1, -1⟩ ≤ 1 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx : Dyadic.toReal ⟨1, -1⟩ = (1:ℝ)/2 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hb := sinBall_sound sinBallPilot hx0 hx1
  have hc : (⟨1005431, -21⟩ : Dyadic).toReal = (1005431:ℝ)/2097152 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hr : (⟨7, -21⟩ : Dyadic).toReal = (7:ℝ)/2097152 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [hx] at hb
  simp only [Ball.mem] at hb
  rw [hc, hr] at hb
  exact hb

end Kepler.Interval

