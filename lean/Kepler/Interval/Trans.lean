/-
  Phase 4, step 4: **transcendental bounds** — verified alternating Taylor
  estimates for `sin`/`cos`/`arctan`, packaged as dyadic intervals / balls,
  plus interval-level wrappers (endpoint monotonicity) and π-shift range
  reduction for `sin`.

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

  Instantiations (terms antitone on `[0, 1]`; `Mathlib.HasSum` sources):
  + `sin`: `Real.hasSum_sin` (valid for all `x`);
  + `cos`: `Real.hasSum_cos` (valid for all `x`);
  + `arctan`: `Real.hasSum_arctan` (valid for `‖x‖ < 1` — hence the *strict*
    range checks `blt` in `arctanI` below).

  **Range reduction** (`sinRed`): `sin` is only Taylor-enclosed on `[0, 1]`;
  for arguments in a band around `±π` we shift by the dyadic π enclosure
  `piD = [3.125, 3.1875]` (proved correct from `Real.pi_gt_d6`/`pi_lt_d6`)
  and use `sin (x ∓ π) = −sin x` (`Real.sin_sub_pi`/`sin_add_pi`), landing
  in `[-1, 1]` where `sinI` applies.  Coverage: `[-1, 1]` (`sinI`) plus the
  bands `[2.25, 4.1]` and `[-4.1, -2.25]` — in particular all of `|x| ≤ 4`
  away from `(1, 2.25)` and `(-2.25, -1)`.

  ## The checked (dyadic) layer

  `taylorIter` accumulates outward-rounded partial sums: the term `x^(2i+1)`
  (exact dyadic `npow`) is divided by `(2i+1)!` via `Dyadic.divFloorQ`
  (mantissa floor for the lower sum, `+ one ulp` for the upper sum,
  sign-adjusted by parity of `i`), all in `Int` — kernel `decide` evaluates
  the whole loop.  `sinInterval` adds the one-ulp-up rounded remainder bound
  `1/(2N+1)!` (for `x ≤ 1`); `cosInterval`/`arctanInterval` reuse the same
  loop with even powers (`x^(2i)/(2i)!`) resp. odd powers over odd integers
  (`x^(2i+1)/(2i+1)`), each with its term-shaped remainder.  The
  **interval-level wrappers** `sinI`/`cosI`/`arctanI` enclose
  `{f y : y ∈ J}` on `J ⊆ [-1,1]` (resp. `[0,1]` for `cos`) via endpoint
  monotonicity (`Real.sin_le_sin_of_le_of_le_pi_div_two`,
  `Real.cos_le_cos_of_nonneg_of_le_pi`, `arctan_mono`) applied to the point
  enclosures, with odd/even sign handling.

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

/-! ## `cos` on `[0, 1]`: alternating Taylor with explicit remainder -/

/-- The Taylor coefficients of `cos` are antitone on `[0, 1]`. -/
private theorem cos_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun i => x^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro i
  have hf : ((Nat.factorial (2*(i+1) : ℕ) : ℕ):ℝ)
      = ((Nat.factorial (2*i : ℕ) : ℕ):ℝ) * ((2*i+1 : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ) := by
    have h1 : ((2*(i+1) : ℕ)).factorial
        = ((2*i : ℕ)).factorial * ((2*i+1 : ℕ)) * ((2*i+2 : ℕ)) := by
      rw [show (2*(i+1) : ℕ) = (2*i+1) + 1 from by omega, Nat.factorial_succ,
        show (2*i+1 : ℕ) = 2*i + 1 from by omega, Nat.factorial_succ]
      ring
    exact_mod_cast h1
  show x^(2*(i+1))/((Nat.factorial (2*(i+1) : ℕ) : ℕ):ℝ)
    ≤ x^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)
  rw [hf]
  have hx2 : x * x ≤ 1 := by nlinarith
  have hden : (1:ℝ) ≤ ((2*i+1 : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ) := by
    have ha1 : (1:ℕ) ≤ (2*i+1) := by omega
    have ha2 : (1:ℕ) ≤ (2*i+2) := by omega
    have hle : (1:ℕ) ≤ (2*i+1) * (2*i+2) := Nat.mul_le_mul ha1 ha2
    exact_mod_cast hle
  have hp : (0:ℝ) ≤ x^(2*i) := pow_nonneg hx0 _
  have h1 : x * x * x^(2*i) ≤ 1 * x^(2*i) := mul_le_mul_of_nonneg_right hx2 hp
  have h2 : x^(2*i) * 1
      ≤ x^(2*i) * (((2*i+1 : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ)) := mul_le_mul_of_nonneg_left hden hp
  have h3 : x^(2*(i+1)) = x * x * x^(2*i) := by ring
  have hfa : (0:ℝ) < ((Nat.factorial (2*i : ℕ) : ℕ):ℝ) := by positivity
  have hfb : (0:ℝ) < ((Nat.factorial (2*i : ℕ) : ℕ):ℝ) * ((2*i+1 : ℕ):ℝ) * ((2*i+2 : ℕ):ℝ) := by
    positivity
  rw [div_le_iff₀ hfb, div_mul_eq_mul_div, le_div_iff₀ hfa, h3]
  nlinarith [h1, h2, hfa, hden, hp]

/-- **Explicit Taylor remainder for `cos` on `[0,1]`** (semantic layer). -/
theorem cos_abs_sub_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |Real.cos x - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i))/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)|
      ≤ x^(2*n)/((Nat.factorial (2*n : ℕ) : ℕ):ℝ) := by
  have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ))
      = ((-1:ℝ)^i * x^(2*i))/((Nat.factorial (2*i : ℕ) : ℕ):ℝ) := by
    intro i
    rw [mul_div_assoc']
  have hsumEq : (∑ i ∈ Finset.range n, (-1:ℝ)^i * (x^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)))
      = ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i))/((Nat.factorial (2*i : ℕ) : ℕ):ℝ) :=
    Finset.sum_congr rfl (fun i _ => hcongr i)
  have h := abs_sub_partial_le (cos_terms_antitone hx0 hx1)
    (fun i => div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    (by simpa only [← hcongr] using Real.hasSum_cos x) n
  rwa [hsumEq] at h

/-! ## `arctan` on `[0, 1)`: alternating series with explicit remainder -/

/-- The alternating-series coefficients of `arctan` are antitone on `[0, 1]`. -/
private theorem arctan_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun i => x^(2*i+1)/((2*i+1 : ℕ):ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro i
  have hd1 : (1:ℝ) ≤ ((2*i+1 : ℕ):ℝ) := by
    have : (1:ℕ) ≤ 2*i+1 := by omega
    exact_mod_cast this
  have hd3 : ((2*i+1 : ℕ):ℝ) ≤ ((2*i+3 : ℕ):ℝ) := by
    have : (2*i+1 : ℕ) ≤ 2*i+3 := by omega
    exact_mod_cast this
  have hdpos : (0:ℝ) < ((2*i+1 : ℕ):ℝ) := by linarith
  have hdpos3 : (0:ℝ) < ((2*i+3 : ℕ):ℝ) := by linarith
  have hp : (0:ℝ) ≤ x^(2*i+1) := pow_nonneg hx0 _
  have hx2 : x * x ≤ 1 := by nlinarith
  show x^(2*(i+1)+1)/((2*(i+1)+1 : ℕ):ℝ) ≤ x^(2*i+1)/((2*i+1 : ℕ):ℝ)
  rw [show 2*(i+1)+1 = 2*i+3 from by omega,
    div_le_iff₀ hdpos3, div_mul_eq_mul_div, le_div_iff₀ hdpos]
  have h3 : x^(2*i+3) = x * x * x^(2*i+1) := by ring
  have hc : x * x * x^(2*i+1) * ((2*i+1 : ℕ):ℝ)
      ≤ x^(2*i+1) * ((2*i+1 : ℕ):ℝ) := by
    calc x * x * x^(2*i+1) * ((2*i+1 : ℕ):ℝ)
        ≤ 1 * x^(2*i+1) * ((2*i+1 : ℕ):ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx2 hp) (by linarith)
      _ = x^(2*i+1) * ((2*i+1 : ℕ):ℝ) := by ring
  have hd : x^(2*i+1) * ((2*i+1 : ℕ):ℝ) ≤ x^(2*i+1) * ((2*i+3 : ℕ):ℝ) :=
    mul_le_mul_of_nonneg_left hd3 hp
  rw [h3]
  linarith

/-- **Explicit alternating-series remainder for `arctan` on `[0,1)`**
(semantic layer; `Real.hasSum_arctan` needs the strict bound). -/
theorem arctan_abs_sub_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    |Real.arctan x - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ)|
      ≤ x^(2*n+1)/((2*n+1 : ℕ):ℝ) := by
  have hx1' : x ≤ 1 := le_of_lt hx1
  have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x^(2*i+1)/((2*i+1 : ℕ):ℝ))
      = ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ) := by
    intro i
    rw [mul_div_assoc']
  have hsumEq : (∑ i ∈ Finset.range n, (-1:ℝ)^i * (x^(2*i+1)/((2*i+1 : ℕ):ℝ)))
      = ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ) :=
    Finset.sum_congr rfl (fun i _ => hcongr i)
  have hsum : HasSum (fun i => (-1:ℝ)^i * (x^(2*i+1)/((2*i+1 : ℕ):ℝ))) (Real.arctan x) := by
    have h := Real.hasSum_arctan (x := x) (by
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith)
    simpa only [← hcongr] using h
  have h := abs_sub_partial_le (arctan_terms_antitone hx0 hx1')
    (fun i => div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)) hsum n
  rwa [hsumEq] at h

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

/-! ## `cosInterval` / `arctanInterval` (checked layer) -/

/-- Interval enclosure of `cos x.toReal` for `x.toReal ∈ [0, 1]`: `N`
alternating Taylor terms (even powers) with outward per-term rounding at
granularity `2^out`, plus the term-shaped remainder `x^(2N)/(2N)!`. -/
def cosInterval (x : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  match taylorIter (fun i => x.npow (2*i)) (fun i => (Nat.factorial (2*i) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => none
  | some (lw, hg) =>
      match Dyadic.divFloorQ (x.npow (2*N)) ⟨(Nat.factorial (2*N) : ℤ), 0⟩ out with
      | none => none
      | some u => some ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩

/-- **Soundness of `cosInterval`** (over `ℝ`): on `0 ≤ x.toReal ≤ 1`, the
returned interval contains `cos` of the real semantics. -/
theorem cosInterval_sound {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : cosInterval x N out = some I) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1) :
    I.lo.toReal ≤ Real.cos x.toReal ∧ Real.cos x.toReal ≤ I.hi.toReal := by
  simp only [cosInterval] at h
  cases hloop : taylorIter (fun i => x.npow (2*i)) (fun i => (Nat.factorial (2*i) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => rw [hloop] at h; simp at h
  | some lr =>
    obtain ⟨lw, hg⟩ := lr
    rw [hloop] at h
    cases hu : Dyadic.divFloorQ (x.npow (2*N)) ⟨(Nat.factorial (2*N) : ℤ), 0⟩ out with
    | none => rw [hu] at h; simp at h
    | some u =>
      rw [hu] at h
      obtain rfl : I = ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩ :=
        (Option.some.inj h).symm
      have hA : ∀ i (q : Dyadic),
          Dyadic.divFloorQ (x.npow (2*i)) ⟨(Nat.factorial (2*i) : ℤ), 0⟩ out = some q →
          q.toReal ≤ x.toReal^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ) ∧
            x.toReal^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)
              ≤ Dyadic.toReal ⟨q.m + 1, out⟩ := by
        intro i q hq
        obtain ⟨hs1, hs2⟩ := Dyadic.divFloorQ_spec hq
        rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hs1 hs2
        exact ⟨hs1, hs2⟩
      have hbase : (⟨0, 0⟩ : Dyadic).toReal
          = ∑ j ∈ Finset.range 0, (-1:ℝ)^j * (fun i => x.toReal^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)) j := by
        rw [Dyadic.toReal_def]
        simp
      obtain ⟨hs1, hs2⟩ :=
        taylorIter_spec (fun i => x.npow (2*i)) (fun i => (Nat.factorial (2*i) : ℤ)) out
          (fun i => x.toReal^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ)) hA
          N 0 ⟨0, 0⟩ ⟨0, 0⟩
          (by rw [← hbase]) (by rw [← hbase]) ⟨lw, hg⟩ hloop
      obtain ⟨hu1, hu2⟩ := Dyadic.divFloorQ_spec hu
      rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hu1 hu2
      push_cast at hu1 hu2
      have hU : Dyadic.toReal ⟨u.m + 1, out⟩ = u.toReal + (Dyadic.ulp out).toReal :=
        toReal_succ_ulp (Dyadic.divFloorQ_e hu)
      have hcos := cos_abs_sub_partial_le hx0 hx1 N
      rw [abs_le] at hcos
      rw [Nat.zero_add] at hs1 hs2
      have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x.toReal^(2*i)/((Nat.factorial (2*i : ℕ) : ℕ):ℝ))
          = ((-1:ℝ)^i * x.toReal^(2*i))/((Nat.factorial (2*i : ℕ) : ℕ):ℝ) := by
        intro i
        rw [mul_div_assoc']
      have hsumEq : (∑ j ∈ Finset.range N, (-1:ℝ)^j * (x.toReal^(2*j)/((Nat.factorial (2*j : ℕ) : ℕ):ℝ)))
          = ∑ i ∈ Finset.range N, ((-1:ℝ)^i * x.toReal^(2*i))/((Nat.factorial (2*i : ℕ) : ℕ):ℝ) :=
        Finset.sum_congr rfl (fun j _ => hcongr j)
      rw [hsumEq] at hs1 hs2
      constructor
      · show Dyadic.toReal (lw.dsub ⟨u.m + 1, out⟩) ≤ Real.cos x.toReal
        rw [Dyadic.toReal_dsub, hU]
        linarith [hs1, hcos.1, hu2]
      · show Real.cos x.toReal ≤ Dyadic.toReal (hg.add ⟨u.m + 1, out⟩)
        rw [Dyadic.toReal_add]
        linarith [hs2, hcos.2, hu2]

/-- Interval enclosure of `arctan x.toReal` for `0 ≤ x.toReal < 1`: `N`
alternating series terms (odd powers over odd integers) with outward
per-term rounding at granularity `2^out`, plus the term-shaped remainder
`x^(2N+1)/(2N+1)`. -/
def arctanInterval (x : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  match taylorIter (fun i => x.npow (2*i+1)) (fun i => ((2*i+1 : ℕ) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => none
  | some (lw, hg) =>
      match Dyadic.divFloorQ (x.npow (2*N+1)) ⟨((2*N+1 : ℕ) : ℤ), 0⟩ out with
      | none => none
      | some u => some ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩

/-- **Soundness of `arctanInterval`** (over `ℝ`): on `0 ≤ x.toReal < 1`, the
returned interval contains `arctan` of the real semantics. -/
theorem arctanInterval_sound {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : arctanInterval x N out = some I) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal < 1) :
    I.lo.toReal ≤ Real.arctan x.toReal ∧ Real.arctan x.toReal ≤ I.hi.toReal := by
  have hx1' : x.toReal ≤ 1 := le_of_lt hx1
  simp only [arctanInterval] at h
  cases hloop : taylorIter (fun i => x.npow (2*i+1)) (fun i => ((2*i+1 : ℕ) : ℤ)) out N 0
      ⟨0, 0⟩ ⟨0, 0⟩ with
  | none => rw [hloop] at h; simp at h
  | some lr =>
    obtain ⟨lw, hg⟩ := lr
    rw [hloop] at h
    cases hu : Dyadic.divFloorQ (x.npow (2*N+1)) ⟨((2*N+1 : ℕ) : ℤ), 0⟩ out with
    | none => rw [hu] at h; simp at h
    | some u =>
      rw [hu] at h
      obtain rfl : I = ⟨lw.dsub ⟨u.m + 1, out⟩, hg.add ⟨u.m + 1, out⟩⟩ :=
        (Option.some.inj h).symm
      have hA : ∀ i (q : Dyadic),
          Dyadic.divFloorQ (x.npow (2*i+1)) ⟨((2*i+1 : ℕ) : ℤ), 0⟩ out = some q →
          q.toReal ≤ x.toReal^(2*i+1)/((2*i+1 : ℕ):ℝ) ∧
            x.toReal^(2*i+1)/((2*i+1 : ℕ):ℝ)
              ≤ Dyadic.toReal ⟨q.m + 1, out⟩ := by
        intro i q hq
        obtain ⟨hs1, hs2⟩ := Dyadic.divFloorQ_spec hq
        rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hs1 hs2
        exact ⟨hs1, hs2⟩
      have hbase : (⟨0, 0⟩ : Dyadic).toReal
          = ∑ j ∈ Finset.range 0, (-1:ℝ)^j * (fun i => x.toReal^(2*i+1)/((2*i+1 : ℕ):ℝ)) j := by
        rw [Dyadic.toReal_def]
        simp
      obtain ⟨hs1, hs2⟩ :=
        taylorIter_spec (fun i => x.npow (2*i+1)) (fun i => ((2*i+1 : ℕ) : ℤ)) out
          (fun i => x.toReal^(2*i+1)/((2*i+1 : ℕ):ℝ)) hA
          N 0 ⟨0, 0⟩ ⟨0, 0⟩
          (by rw [← hbase]) (by rw [← hbase]) ⟨lw, hg⟩ hloop
      obtain ⟨hu1, hu2⟩ := Dyadic.divFloorQ_spec hu
      rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hu1 hu2
      push_cast at hu1 hu2
      have hU : Dyadic.toReal ⟨u.m + 1, out⟩ = u.toReal + (Dyadic.ulp out).toReal :=
        toReal_succ_ulp (Dyadic.divFloorQ_e hu)
      have harc := arctan_abs_sub_partial_le hx0 hx1 N
      rw [abs_le] at harc
      have hcast : ((2*N+1 : ℕ):ℝ) = 2*((N:ℝ)) + 1 := by push_cast; ring
      rw [hcast] at harc
      rw [Nat.zero_add] at hs1 hs2
      have hcongr : ∀ i : ℕ, (-1:ℝ)^i * (x.toReal^(2*i+1)/((2*i+1 : ℕ):ℝ))
          = ((-1:ℝ)^i * x.toReal^(2*i+1))/((2*i+1 : ℕ):ℝ) := by
        intro i
        rw [mul_div_assoc']
      have hsumEq : (∑ j ∈ Finset.range N, (-1:ℝ)^j * (x.toReal^(2*j+1)/((2*j+1 : ℕ):ℝ)))
          = ∑ i ∈ Finset.range N, ((-1:ℝ)^i * x.toReal^(2*i+1))/((2*i+1 : ℕ):ℝ) :=
        Finset.sum_congr rfl (fun j _ => hcongr j)
      rw [hsumEq] at hs1 hs2
      constructor
      · show Dyadic.toReal (lw.dsub ⟨u.m + 1, out⟩) ≤ Real.arctan x.toReal
        rw [Dyadic.toReal_dsub, hU]
        linarith [hs1, harc.1, hu2]
      · show Real.arctan x.toReal ≤ Dyadic.toReal (hg.add ⟨u.m + 1, out⟩)
        rw [Dyadic.toReal_add]
        linarith [hs2, harc.2, hu2]

/-! ## Interval-level wrappers: endpoint monotonicity + sign handling -/

/-- Point-level `sin` enclosure for `|z.toReal| ≤ 1`: negative inputs reduce
to positive ones via `sin (-u) = -sin u` (`sin` is odd). -/
def sinPoint (z : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  if z.isNeg then (sinInterval (-z) N out).map DInterval.neg
  else sinInterval z N out

theorem sinPoint_sound {z : Dyadic} {N : ℕ} {out : Int} {K : DInterval}
    (hz1 : -1 ≤ z.toReal) (hz2 : z.toReal ≤ 1)
    (h : sinPoint z N out = some K) : K.mem (Real.sin z.toReal) := by
  unfold sinPoint at h
  by_cases hn : z.isNeg = true
  · rw [if_pos hn] at h
    have hzn : z.toReal < 0 := (Dyadic.isNeg_iff z).mp hn
    have hnz0 : (0:ℝ) ≤ Dyadic.toReal (-z) := by
      rw [Dyadic.toReal_neg]
      linarith
    have hnz1 : Dyadic.toReal (-z) ≤ 1 := by
      rw [Dyadic.toReal_neg]
      linarith
    cases hs : sinInterval (-z) N out with
    | none => rw [hs] at h; simp at h
    | some L =>
      rw [hs] at h
      obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
      obtain ⟨h1, h2⟩ := sinInterval_sound hs hnz0 hnz1
      have hid : Real.sin z.toReal = -Real.sin (Dyadic.toReal (-z)) := by
        rw [Dyadic.toReal_neg, Real.sin_neg]
        ring
      rw [hid]
      exact DInterval.mem_neg ⟨h1, h2⟩
  · rw [if_neg hn] at h
    have hz0 : 0 ≤ z.toReal := by
      by_contra hc
      exact hn ((Dyadic.isNeg_iff z).mpr (by linarith))
    exact sinInterval_sound h hz0 hz2

/-- Interval-level `sin` on `J ⊆ [-1, 1]`: `sin` is monotone on
`[-π/2, π/2] ⊇ [-1, 1]`, so the endpoints' point enclosures bracket all of
`{sin y : y ∈ J}`. -/
def sinI (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.ble J.hi ⟨1, 0⟩ then
    match sinPoint J.lo N out, sinPoint J.hi N out with
    | some L, some H => some ⟨L.lo, H.hi⟩
    | _, _ => none
  else none

/-- **Soundness of `sinI`**: if the range checks succeed, the result contains
`sin y` for every real `y ∈ J` (range hypotheses are internal to the check). -/
theorem sinI_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : sinI J N out = some K) : K.mem (Real.sin y) := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold sinI at h
  by_cases hchk : Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.ble J.hi ⟨1, 0⟩
  · rw [if_pos hchk] at h
    have hlo : (-1:ℝ) ≤ J.lo.toReal := by
      have h := Dyadic.ble_toReal (Bool.and_eq_true_iff.mp hchk).1
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    have hhi : J.hi.toReal ≤ 1 := by
      have h := Dyadic.ble_toReal (Bool.and_eq_true_iff.mp hchk).2
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    have hpi : (1:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_d6]
    cases hl : sinPoint J.lo N out with
    | none => rw [hl] at h; simp at h
    | some L =>
      rw [hl] at h
      cases hh : sinPoint J.hi N out with
      | none => rw [hh] at h; simp at h
      | some H =>
        rw [hh] at h
        obtain rfl : K = ⟨L.lo, H.hi⟩ := (Option.some.inj h).symm
        obtain ⟨hl1, _⟩ := sinPoint_sound (by linarith) (by linarith) hl
        obtain ⟨_, hh2⟩ := sinPoint_sound (by linarith) (by linarith) hh
        have hmono1 : Real.sin J.lo.toReal ≤ Real.sin y :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hy1
        have hmono2 : Real.sin y ≤ Real.sin J.hi.toReal :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hy2
        exact ⟨le_trans hl1 hmono1, le_trans hmono2 hh2⟩
  · rw [if_neg hchk] at h; simp at h

/-- Interval-level `cos` on `J ⊆ [0, 1]`: `cos` is antitone on `[0, π] ⊇
[0, 1]`, so the endpoints' point enclosures (reversed) bracket all of
`{cos y : y ∈ J}`. -/
def cosI (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if J.lo.isNN && Dyadic.ble J.hi ⟨1, 0⟩ then
    match cosInterval J.hi N out, cosInterval J.lo N out with
    | some Lh, some Hl => some ⟨Lh.lo, Hl.hi⟩
    | _, _ => none
  else none

/-- **Soundness of `cosI`**: if the range checks succeed, the result contains
`cos y` for every real `y ∈ J`. -/
theorem cosI_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : cosI J N out = some K) : K.mem (Real.cos y) := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold cosI at h
  by_cases hchk : J.lo.isNN && Dyadic.ble J.hi ⟨1, 0⟩
  · rw [if_pos hchk] at h
    have hlo : (0:ℝ) ≤ J.lo.toReal := (Dyadic.isNN_iff J.lo).mp
      (Bool.and_eq_true_iff.mp hchk).1
    have hhi : J.hi.toReal ≤ 1 := by
      have h := Dyadic.ble_toReal (Bool.and_eq_true_iff.mp hchk).2
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    have hpi : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
    have hy0 : (0:ℝ) ≤ y := by linarith
    cases hlh : cosInterval J.hi N out with
    | none => rw [hlh] at h; simp at h
    | some Lh =>
      rw [hlh] at h
      cases hhl : cosInterval J.lo N out with
      | none => rw [hhl] at h; simp at h
      | some Hl =>
        rw [hhl] at h
        obtain rfl : K = ⟨Lh.lo, Hl.hi⟩ := (Option.some.inj h).symm
        obtain ⟨hlh1, _⟩ := cosInterval_sound hlh (by linarith) hhi
        obtain ⟨_, hhl2⟩ := cosInterval_sound hhl hlo (by linarith)
        have hmono1 : Real.cos y ≤ Real.cos J.lo.toReal :=
          Real.cos_le_cos_of_nonneg_of_le_pi hlo (by linarith) hy1
        have hmono2 : Real.cos J.hi.toReal ≤ Real.cos y :=
          Real.cos_le_cos_of_nonneg_of_le_pi hy0 (by linarith) hy2
        exact ⟨le_trans hlh1 hmono2, le_trans hmono1 hhl2⟩
  · rw [if_neg hchk] at h; simp at h

/-- Point-level `arctan` enclosure for `|z.toReal| < 1`: negative inputs
reduce via `arctan (-u) = -arctan u` (odd). -/
def arctanPoint (z : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  if z.isNeg then (arctanInterval (-z) N out).map DInterval.neg
  else arctanInterval z N out

theorem arctanPoint_sound {z : Dyadic} {N : ℕ} {out : Int} {K : DInterval}
    (hz1 : -1 < z.toReal) (hz2 : z.toReal < 1)
    (h : arctanPoint z N out = some K) : K.mem (Real.arctan z.toReal) := by
  unfold arctanPoint at h
  by_cases hn : z.isNeg = true
  · rw [if_pos hn] at h
    have hzn : z.toReal < 0 := (Dyadic.isNeg_iff z).mp hn
    have hnz0 : (0:ℝ) ≤ Dyadic.toReal (-z) := by
      rw [Dyadic.toReal_neg]
      linarith
    have hnz1 : Dyadic.toReal (-z) < 1 := by
      rw [Dyadic.toReal_neg]
      linarith
    cases hs : arctanInterval (-z) N out with
    | none => rw [hs] at h; simp at h
    | some L =>
      rw [hs] at h
      obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
      obtain ⟨h1, h2⟩ := arctanInterval_sound hs hnz0 hnz1
      have hid : Real.arctan z.toReal = -Real.arctan (Dyadic.toReal (-z)) := by
        rw [Dyadic.toReal_neg, Real.arctan_neg]
        ring
      rw [hid]
      exact DInterval.mem_neg ⟨h1, h2⟩
  · rw [if_neg hn] at h
    have hz0 : 0 ≤ z.toReal := by
      by_contra hc
      exact hn ((Dyadic.isNeg_iff z).mpr (by linarith))
    exact arctanInterval_sound h hz0 hz2

/-- Interval-level `arctan` on `J ⊆ (-1, 1)` (**strict**: the series identity
needs `‖x‖ < 1`): `arctan` is monotone, so the endpoints' point enclosures
bracket all of `{arctan y : y ∈ J}`. -/
def arctanI (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.blt (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.blt J.hi ⟨1, 0⟩ then
    match arctanPoint J.lo N out, arctanPoint J.hi N out with
    | some L, some H => some ⟨L.lo, H.hi⟩
    | _, _ => none
  else none

/-- **Soundness of `arctanI`**: if the (strict) range checks succeed, the
result contains `arctan y` for every real `y ∈ J`. -/
theorem arctanI_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : arctanI J N out = some K) : K.mem (Real.arctan y) := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold arctanI at h
  by_cases hchk : Dyadic.blt (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.blt J.hi ⟨1, 0⟩
  · rw [if_pos hchk] at h
    have hlo : (-1:ℝ) < J.lo.toReal := by
      have h := Dyadic.blt_toReal (Bool.and_eq_true_iff.mp hchk).1
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    have hhi : J.hi.toReal < 1 := by
      have h := Dyadic.blt_toReal (Bool.and_eq_true_iff.mp hchk).2
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    cases hl : arctanPoint J.lo N out with
    | none => rw [hl] at h; simp at h
    | some L =>
      rw [hl] at h
      cases hh : arctanPoint J.hi N out with
      | none => rw [hh] at h; simp at h
      | some H =>
        rw [hh] at h
        obtain rfl : K = ⟨L.lo, H.hi⟩ := (Option.some.inj h).symm
        obtain ⟨hl1, _⟩ := arctanPoint_sound (by linarith) (by linarith) hl
        obtain ⟨_, hh2⟩ := arctanPoint_sound (by linarith) (by linarith) hh
        have hmono1 : Real.arctan J.lo.toReal ≤ Real.arctan y := Real.arctan_mono hy1
        have hmono2 : Real.arctan y ≤ Real.arctan J.hi.toReal := Real.arctan_mono hy2
        exact ⟨le_trans hl1 hmono1, le_trans hmono2 hh2⟩
  · rw [if_neg hchk] at h; simp at h

/-! ## Range reduction for `sin` by π-shifts -/

/-- Coarse dyadic enclosure of `π`: `[3.125, 3.1875]` (kernel-decidable
endpoints; the width is far below the reduction margins). -/
def piD : DInterval := ⟨⟨50, -4⟩, ⟨51, -4⟩⟩

theorem piD_mem : piD.mem Real.pi := by
  constructor
  · show Dyadic.toReal ⟨50, -4⟩ ≤ Real.pi
    simp only [Dyadic.toReal_def]
    have h := Real.pi_gt_d6
    have h2 : (((50 : ℤ) : ℝ)) * (2:ℝ)^((-4:ℤ)) = 25/8 := by norm_num
    rw [h2]
    linarith
  · show Real.pi ≤ Dyadic.toReal ⟨51, -4⟩
    simp only [Dyadic.toReal_def]
    have h := Real.pi_lt_d6
    have h2 : (((51 : ℤ) : ℝ)) * (2:ℝ)^((-4:ℤ)) = 51/16 := by norm_num
    rw [h2]
    linarith

/-- **π-shift range reduction for `sin`**: for an interval in the upper band
(`I.lo ≥ 2.25`) the argument is shifted by `-π`; in the lower band
(`I.hi ≤ -2.25`) by `+π`; both land in `[-1, 1]` (guaranteed whenever
`I ⊆ [2.25, 4.1]` resp. `I ⊆ [-4.1, -2.25]`, since `piD` has width `≤ 1/16`)
and the result is negated via `sin (x ∓ π) = -sin x`.  Soundness is
*unconditional* — all range requirements live inside the `sinI` checks;
out-of-band inputs simply give `none`. -/
def sinRed (I : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble (⟨9, -2⟩ : Dyadic) I.lo then
    (sinI (I.sub piD) N out).map DInterval.neg
  else if Dyadic.ble I.hi (⟨-9, -2⟩ : Dyadic) then
    (sinI (I.add piD) N out).map DInterval.neg
  else none

/-- **Soundness of `sinRed`**: whenever the reduction succeeds, the result
contains `sin x` for every real `x ∈ I`. -/
theorem sinRed_sound {I : DInterval} {N : ℕ} {out : Int} {K : DInterval} {x : ℝ}
    (hx : I.mem x) (h : sinRed I N out = some K) : K.mem (Real.sin x) := by
  unfold sinRed at h
  by_cases hband : Dyadic.ble (⟨9, -2⟩ : Dyadic) I.lo
  · rw [if_pos hband] at h
    cases hs : sinI (I.sub piD) N out with
    | none => rw [hs] at h; simp at h
    | some L =>
      rw [hs] at h
      obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
      have hsub : (I.sub piD).mem (x - Real.pi) := DInterval.mem_sub hx piD_mem
      have hL := sinI_sound hsub hs
      have hid : Real.sin x = -Real.sin (x - Real.pi) := by
        rw [Real.sin_sub_pi]
        ring
      rw [hid]
      exact DInterval.mem_neg hL
  · rw [if_neg hband] at h
    by_cases hband2 : Dyadic.ble I.hi (⟨-9, -2⟩ : Dyadic)
    · rw [if_pos hband2] at h
      cases hs : sinI (I.add piD) N out with
      | none => rw [hs] at h; simp at h
      | some L =>
        rw [hs] at h
        obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
        have hadd : (I.add piD).mem (x + Real.pi) := DInterval.mem_add hx piD_mem
        have hL := sinI_sound hadd hs
        have hid : Real.sin x = -Real.sin (x + Real.pi) := by
          rw [Real.sin_add_pi]
          ring
        rw [hid]
        exact DInterval.mem_neg hL
    · rw [if_neg hband2] at h; simp at h

/-- Full interval-level `sin`: direct on `[-1, 1]`, π-shift reduction
otherwise (coverage: `[-1, 1] ∪ [2.25, 4.1] ∪ [-4.1, -2.25]`). -/
def sinGen (I : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  match sinI I N out with
  | some J => some J
  | none => sinRed I N out

/-- **Soundness of `sinGen`**: whenever evaluation succeeds, the result
contains `sin y` for every real `y ∈ I`. -/
theorem sinGen_sound {I : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : I.mem y) (h : sinGen I N out = some K) : K.mem (Real.sin y) := by
  unfold sinGen at h
  cases hs : sinI I N out with
  | none => rw [hs] at h; exact sinRed_sound hy h
  | some J =>
    rw [hs] at h
    obtain rfl : K = J := (Option.some.inj h).symm
    exact sinI_sound hy hs

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

/-! ## Pilots: `cos(1/4)`, `arctan(1/2)` and range-reduced `sin` (kernel `decide` only) -/

/-- The checked certificate: five alternating Taylor terms of `cos` at
`x = 1/4`, outward-rounded at granularity `2^-20`, plus the term-shaped
remainder `x^10/10!` — all computed by kernel `decide`. -/
theorem cosPilot_cert :
    cosInterval ⟨1, -2⟩ 5 (-20) = some ⟨⟨1015975, -20⟩, ⟨1015982, -20⟩⟩ := by
  decide

/-- End-to-end real statement: `0.9689 < cos(1/4)` (the true value is
`0.9689124…`). -/
theorem cosPilot_real : (9689:ℝ)/10000 < Real.cos ((1:ℝ)/4) := by
  have hx0 : (0:ℝ) ≤ Dyadic.toReal ⟨1, -2⟩ := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx1 : Dyadic.toReal ⟨1, -2⟩ ≤ 1 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx : Dyadic.toReal ⟨1, -2⟩ = (1:ℝ)/4 := by
    rw [Dyadic.toReal_def]
    norm_num
  obtain ⟨h1, _⟩ := cosInterval_sound cosPilot_cert hx0 hx1
  rw [hx, Dyadic.toReal_def] at h1
  dsimp only at h1
  have hlo : (((1015975:Int):ℝ)) * (2:ℝ)^((-20:Int)) = ((1015975:Int):ℝ)/1048576 := by
    rw [show ((2:ℝ)^((-20:Int))) = 1/((1048576:ℝ)) from by norm_num, mul_one_div]
  rw [hlo] at h1
  have hnum : (9689:ℝ)/10000 < ((1015975:Int):ℝ)/1048576 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1048576), div_mul_eq_mul_div,
      div_lt_iff₀ (by norm_num : (0:ℝ) < 10000)]
    norm_num
  exact lt_of_lt_of_le hnum h1

/-- The checked certificate: five alternating series terms of `arctan` at
`x = 1/2`, outward-rounded at granularity `2^-20`, plus the term-shaped
remainder `x^11/11` — all computed by kernel `decide`. -/
theorem arctanPilot_cert :
    arctanInterval ⟨1, -1⟩ 5 (-20) = some ⟨⟨486159, -20⟩, ⟨486258, -20⟩⟩ := by
  decide

/-- End-to-end real statement: `0.46 < arctan(1/2)` (the true value is
`0.4636476…`). -/
theorem arctanPilot_real : (23:ℝ)/50 < Real.arctan ((1:ℝ)/2) := by
  have hx0 : (0:ℝ) ≤ Dyadic.toReal ⟨1, -1⟩ := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx1 : Dyadic.toReal ⟨1, -1⟩ < 1 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hx : Dyadic.toReal ⟨1, -1⟩ = (1:ℝ)/2 := by
    rw [Dyadic.toReal_def]
    norm_num
  obtain ⟨h1, _⟩ := arctanInterval_sound arctanPilot_cert hx0 hx1
  rw [hx, Dyadic.toReal_def] at h1
  dsimp only at h1
  have hlo : (((486159:Int):ℝ)) * (2:ℝ)^((-20:Int)) = ((486159:Int):ℝ)/1048576 := by
    rw [show ((2:ℝ)^((-20:Int))) = 1/((1048576:ℝ)) from by norm_num, mul_one_div]
  rw [hlo] at h1
  have hnum : (23:ℝ)/50 < ((486159:Int):ℝ)/1048576 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1048576), div_mul_eq_mul_div,
      div_lt_iff₀ (by norm_num : (0:ℝ) < 50)]
    norm_num
  exact lt_of_lt_of_le hnum h1

/-- Range-reduction pilot: `sin` on `[7/2, 4]` via the π-shift `x ↦ x - π`
(landing in `[5/16, 7/8]`), evaluated at granularity `2^-40` — kernel
`decide` (the shifted arguments carry exponent `-4`, hence the finer
`out`). -/
theorem sinRedPilot_cert :
    sinRed (⟨⟨7, -1⟩, ⟨4, 0⟩⟩ : DInterval) 5 (-40)
      = some ⟨⟨-843923039390, -40⟩, ⟨-338032194059, -40⟩⟩ := by
  decide

/-- End-to-end real statement: `sin x < -3/10` on `[7/2, 4]` (the true values
run from `-0.3508` to `-0.7568`). -/
theorem sinRedPilot_real (x : ℝ) (hx1 : (7:ℝ)/2 ≤ x) (hx2 : x ≤ 4) :
    Real.sin x < -3/10 := by
  have hmem : (⟨⟨7, -1⟩, ⟨4, 0⟩⟩ : DInterval).mem x := by
    constructor
    · show Dyadic.toReal ⟨7, -1⟩ ≤ x
      rw [Dyadic.toReal_def]
      have h7 : (((7:ℤ):ℝ)) * (2:ℝ)^((-1:ℤ)) = (7:ℝ)/2 := by norm_num
      rw [h7]
      exact hx1
    · show x ≤ Dyadic.toReal ⟨4, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  obtain ⟨_, h2⟩ := sinRed_sound hmem sinRedPilot_cert
  have hhi : Dyadic.toReal ⟨-338032194059, -40⟩
      = -((338032194059:ℝ))/1099511627776 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [hhi] at h2
  have hnum : -((338032194059:ℝ))/1099511627776 < -3/10 := by
    have hp : (3:ℝ)/10 < (338032194059:ℝ)/1099511627776 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1099511627776), div_mul_eq_mul_div,
        div_lt_iff₀ (by norm_num : (0:ℝ) < 10)]
      norm_num
    linarith
  exact lt_of_le_of_lt h2 hnum

end Kepler.Interval

