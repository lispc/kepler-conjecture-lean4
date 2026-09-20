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
  + `arctan`: `Real.hasSum_arctan` (valid for `‖x‖ < 1`; the endpoints
    `x = ±1` are closed off separately by continuity —
    `arctan_abs_sub_partial_le_one` — so the range checks in `arctanIBase`
    are the *non-strict* `ble`).

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
  **interval-level wrappers** `sinI`/`cosI` enclose
  `{f y : y ∈ J}` on `J ⊆ [-1,1]` (resp. `[0,1]` for `cos`) via endpoint
  monotonicity (`Real.sin_le_sin_of_le_of_le_pi_div_two`,
  `Real.cos_le_cos_of_nonneg_of_le_pi`, `arctan_mono`) applied to the point
  enclosures, with odd/even sign handling.  `arctanI` is total on `ℝ`: the
  base branch covers `J ⊆ [-1, 1]` (`arctanIBase`), `1 ≤ J.lo` reduces via
  `arctan x = π/2 − arctan x⁻¹` (`arctanIPos`, with the `π/2` envelope
  `halfPiI = 2·arctan 1` at Taylor order `max N 512`), `J.hi ≤ −1` by odd
  symmetry (`arctanINeg`), and intervals crossing `±1` are split at the
  crossing points and joined by hulls (`arctanHull`).

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

/-- **Boundary case `x = 1`** of the `arctan` remainder bound.  The series
identity itself (`Real.hasSum_arctan`) is only stated for `|x| < 1`, but
both sides of `arctan_abs_sub_partial_le` are continuous in `x` and the
inequality holds on `[0, 1)`, so it survives at the endpoint `x = 1`
(Abel-type passage to the limit; no new analysis is needed).  This is what
allows the *closed* gate `J ⊆ [-1, 1]` in `arctanI` — needed e.g. for
`arctan 1 = π/4` arguments (`2570626711`-style dihedral cases). -/
theorem arctan_abs_sub_partial_le_one (n : ℕ) :
    |Real.arctan 1 - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * (1:ℝ)^(2*i+1))/((2*i+1 : ℕ):ℝ)|
      ≤ (1:ℝ)^(2*n+1)/((2*n+1 : ℕ):ℝ) := by
  have hS : Continuous (fun x : ℝ =>
      ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ)) :=
    continuous_finsetSum _ fun i _ =>
      (continuous_const.mul (continuous_pow (2*i+1))).div_const _
  have hf : Continuous (fun x : ℝ =>
      |Real.arctan x - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ)|) :=
    (Real.continuous_arctan.sub hS).abs
  have hg : Continuous (fun x : ℝ => x^(2*n+1)/((2*n+1 : ℕ):ℝ)) :=
    (continuous_pow (2*n+1)).div_const _
  have hsub : Set.Ico (0:ℝ) 1 ⊆ {x : ℝ |
      |Real.arctan x - ∑ i ∈ Finset.range n, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ)|
        ≤ x^(2*n+1)/((2*n+1 : ℕ):ℝ)} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    exact arctan_abs_sub_partial_le hx.1 hx.2 n
  have hmem := closure_minimal hsub (isClosed_le hf hg)
    (by rw [closure_Ico (by norm_num : (0:ℝ) ≠ 1)]
        exact ⟨zero_le_one, le_refl 1⟩)
  exact hmem

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

/-- **Soundness of `arctanInterval`, core** (over `ℝ`): given the analytic
alternating-series estimate at `x.toReal`, the returned interval contains
`arctan` of the real semantics.  Factored out so both the strict (`x < 1`)
and the boundary (`x = 1`, via `arctan_abs_sub_partial_le_one`) instances
can reuse it. -/
theorem arctanInterval_sound_core {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : arctanInterval x N out = some I)
    (harc : |Real.arctan x.toReal
        - ∑ i ∈ Finset.range N, ((-1:ℝ)^i * x.toReal^(2*i+1))/((2*i+1 : ℕ):ℝ)|
        ≤ x.toReal^(2*N+1)/((2*N+1 : ℕ):ℝ)) :
    I.lo.toReal ≤ Real.arctan x.toReal ∧ Real.arctan x.toReal ≤ I.hi.toReal := by
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

/-- **Soundness of `arctanInterval`** (over `ℝ`): on `0 ≤ x.toReal < 1`, the
returned interval contains `arctan` of the real semantics. -/
theorem arctanInterval_sound {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : arctanInterval x N out = some I) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal < 1) :
    I.lo.toReal ≤ Real.arctan x.toReal ∧ Real.arctan x.toReal ≤ I.hi.toReal :=
  arctanInterval_sound_core h (arctan_abs_sub_partial_le hx0 hx1 N)

/-- **Soundness of `arctanInterval`, closed interval** (over `ℝ`): on
`0 ≤ x.toReal ≤ 1` — the endpoint `x = 1` uses the boundary estimate
`arctan_abs_sub_partial_le_one`. -/
theorem arctanInterval_sound_closed {x : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : arctanInterval x N out = some I) (hx0 : 0 ≤ x.toReal) (hx1 : x.toReal ≤ 1) :
    I.lo.toReal ≤ Real.arctan x.toReal ∧ Real.arctan x.toReal ≤ I.hi.toReal := by
  rcases lt_or_eq_of_le hx1 with hlt | heq
  · exact arctanInterval_sound h hx0 hlt
  · apply arctanInterval_sound_core h
    rw [heq]
    exact arctan_abs_sub_partial_le_one N

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

/-- Point-level `arctan` enclosure for `|z.toReal| ≤ 1`: negative inputs
reduce via `arctan (-u) = -arctan u` (odd). -/
def arctanPoint (z : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  if z.isNeg then (arctanInterval (-z) N out).map DInterval.neg
  else arctanInterval z N out

theorem arctanPoint_sound {z : Dyadic} {N : ℕ} {out : Int} {K : DInterval}
    (hz1 : -1 ≤ z.toReal) (hz2 : z.toReal ≤ 1)
    (h : arctanPoint z N out = some K) : K.mem (Real.arctan z.toReal) := by
  unfold arctanPoint at h
  by_cases hn : z.isNeg = true
  · rw [if_pos hn] at h
    have hzn : z.toReal < 0 := (Dyadic.isNeg_iff z).mp hn
    have hnz0 : (0:ℝ) ≤ Dyadic.toReal (-z) := by
      rw [Dyadic.toReal_neg]
      linarith
    have hnz1 : Dyadic.toReal (-z) ≤ 1 := by
      rw [Dyadic.toReal_neg]
      linarith
    cases hs : arctanInterval (-z) N out with
    | none => rw [hs] at h; simp at h
    | some L =>
      rw [hs] at h
      obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
      obtain ⟨h1, h2⟩ := arctanInterval_sound_closed hs hnz0 hnz1
      have hid : Real.arctan z.toReal = -Real.arctan (Dyadic.toReal (-z)) := by
        rw [Dyadic.toReal_neg, Real.arctan_neg]
        ring
      rw [hid]
      exact DInterval.mem_neg ⟨h1, h2⟩
  · rw [if_neg hn] at h
    have hz0 : 0 ≤ z.toReal := by
      by_contra hc
      exact hn ((Dyadic.isNeg_iff z).mpr (by linarith))
    exact arctanInterval_sound_closed h hz0 hz2

/-- Interval-level `arctan` on the **closed** range `J ⊆ [-1, 1]` (the
endpoints `±1` are covered by the boundary estimate
`arctan_abs_sub_partial_le_one`; the alternating-series remainder is still
valid there): `arctan` is monotone, so the endpoints' point enclosures
bracket all of `{arctan y : y ∈ J}`.  This is the base branch of `arctanI`;
large arguments are handled by range reduction (`arctanIPos`/`arctanINeg`)
and crossing intervals by hulls (`arctanHull`). -/
def arctanIBase (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.ble J.hi ⟨1, 0⟩ then
    match arctanPoint J.lo N out, arctanPoint J.hi N out with
    | some L, some H => some ⟨L.lo, H.hi⟩
    | _, _ => none
  else none

/-- **Soundness of `arctanIBase`**: if the range checks succeed, the
result contains `arctan y` for every real `y ∈ J`. -/
theorem arctanIBase_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : arctanIBase J N out = some K) : K.mem (Real.arctan y) := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold arctanIBase at h
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

/-- Enclosure of `π / 2`: twice the point enclosure of `arctan 1 = π / 4`
(`Real.arctan_one`).  The caller picks the Taylor order `Nπ` — the
alternating-series remainder at `x = 1` is `~1 / (2·Nπ+1)`, far coarser than
the output granularity. -/
def halfPiI (Nπ : ℕ) (out : Int) : Option DInterval :=
  (arctanPoint ⟨1, 0⟩ Nπ out).map fun A =>
    ⟨(⟨2, 0⟩ : Dyadic).mul A.lo, (⟨2, 0⟩ : Dyadic).mul A.hi⟩

/-- **Soundness of `halfPiI`**: the result contains `π / 2`. -/
theorem halfPiI_sound {Nπ : ℕ} {out : Int} {K : DInterval}
    (h : halfPiI Nπ out = some K) : K.mem (Real.pi / 2) := by
  unfold halfPiI at h
  cases hp : arctanPoint ⟨1, 0⟩ Nπ out with
  | none => rw [hp] at h; simp at h
  | some A =>
    rw [hp] at h
    obtain rfl : K = ⟨(⟨2, 0⟩ : Dyadic).mul A.lo, (⟨2, 0⟩ : Dyadic).mul A.hi⟩ :=
      (Option.some.inj h).symm
    have hz1 : (-1:ℝ) ≤ Dyadic.toReal ⟨1, 0⟩ := by
      rw [Dyadic.toReal_int]
      norm_num
    have hz2 : Dyadic.toReal ⟨1, 0⟩ ≤ 1 := by
      rw [Dyadic.toReal_int]
      norm_num
    obtain ⟨hA1, hA2⟩ := arctanPoint_sound hz1 hz2 hp
    have hz1v : Dyadic.toReal ⟨1, 0⟩ = 1 := by
      rw [Dyadic.toReal_int]
      norm_num
    rw [hz1v, Real.arctan_one] at hA1 hA2
    have h2 : Dyadic.toReal (⟨2, 0⟩ : Dyadic) = 2 := by
      rw [Dyadic.toReal_int]
      norm_num
    constructor
    · show Dyadic.toReal ((⟨2, 0⟩ : Dyadic).mul A.lo) ≤ Real.pi / 2
      rw [Dyadic.toReal_mul, h2]
      linarith
    · show Real.pi / 2 ≤ Dyadic.toReal ((⟨2, 0⟩ : Dyadic).mul A.hi)
      rw [Dyadic.toReal_mul, h2]
      linarith

/-- The inner combination of `arctanIPos`, given the reciprocal interval
`R ⊇ {1/y : y ∈ J}`: point enclosures of `arctan` at the endpoints of `R`
(clamped to `[0, 1]` — harmless, since `1/y ∈ (0, 1]` already, so the clamp
only tightens), then `π/2 − ·` via `DInterval.sub` (note the endpoint
crossing: `π/2 − arctan(1/y)` is antitone in the enclosed value).  The `π/2`
envelope uses Taylor order `max N 512`: the alternating-series remainder at
`x = 1` is `~1/(2Nπ+1)`, and the node's own `N` can be as low as the rung
minimum. -/
def arctanIPosAux (R : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  match arctanPoint (Dyadic.dmax R.lo ⟨0, 0⟩) N out,
      arctanPoint (Dyadic.dmin R.hi ⟨1, 0⟩) N out, halfPiI (max N 512) out with
  | some L, some H, some P => some (P.sub ⟨L.lo, H.hi⟩)
  | _, _, _ => none

/-- **Soundness of `arctanIPosAux`**: for `z ∈ R ∩ [0, 1]`, the result
contains `π / 2 - arctan z`. -/
theorem arctanIPosAux_sound {R : DInterval} {N : ℕ} {out : Int} {K : DInterval} {z : ℝ}
    (hmem : R.mem z) (hz0 : (0:ℝ) ≤ z) (hz1 : z ≤ 1)
    (h : arctanIPosAux R N out = some K) : K.mem (Real.pi / 2 - Real.arctan z) := by
  obtain ⟨hR1, hR2⟩ := hmem
  unfold arctanIPosAux at h
  cases hL : arctanPoint (Dyadic.dmax R.lo ⟨0, 0⟩) N out with
  | none => rw [hL] at h; simp at h
  | some L =>
    rw [hL] at h
    cases hH : arctanPoint (Dyadic.dmin R.hi ⟨1, 0⟩) N out with
    | none => rw [hH] at h; simp at h
    | some H =>
      rw [hH] at h
      cases hP : halfPiI (max N 512) out with
      | none => rw [hP] at h; simp at h
      | some P =>
        rw [hP] at h
        obtain rfl : K = P.sub ⟨L.lo, H.hi⟩ := (Option.some.inj h).symm
        have h0 : Dyadic.toReal (⟨0, 0⟩ : Dyadic) = 0 := by
          rw [Dyadic.toReal_int]
          norm_num
        have h1d : Dyadic.toReal (⟨1, 0⟩ : Dyadic) = 1 := by
          rw [Dyadic.toReal_int]
          norm_num
        have hlo0 : (-1:ℝ) ≤ Dyadic.toReal (Dyadic.dmax R.lo ⟨0, 0⟩) := by
          rw [Dyadic.toReal_dmax, h0]
          exact le_trans (by norm_num) (le_max_right _ _)
        have hlo1 : Dyadic.toReal (Dyadic.dmax R.lo ⟨0, 0⟩) ≤ 1 := by
          rw [Dyadic.toReal_dmax, h0]
          exact max_le (le_trans hR1 hz1) (by norm_num)
        have hhi0 : (-1:ℝ) ≤ Dyadic.toReal (Dyadic.dmin R.hi ⟨1, 0⟩) := by
          rw [Dyadic.toReal_dmin, h1d]
          exact le_trans (by norm_num) (le_trans hz0 (le_min hR2 hz1))
        have hhi1 : Dyadic.toReal (Dyadic.dmin R.hi ⟨1, 0⟩) ≤ 1 := by
          rw [Dyadic.toReal_dmin, h1d]
          exact min_le_right _ _
        obtain ⟨hL1, _⟩ := arctanPoint_sound hlo0 hlo1 hL
        obtain ⟨_, hH2⟩ := arctanPoint_sound hhi0 hhi1 hH
        obtain ⟨hP1, hP2⟩ := halfPiI_sound hP
        have hm1 : Real.arctan (Dyadic.toReal (Dyadic.dmax R.lo ⟨0, 0⟩))
            ≤ Real.arctan z := by
          apply Real.arctan_mono
          rw [Dyadic.toReal_dmax, h0]
          exact max_le hR1 hz0
        have hm2 : Real.arctan z
            ≤ Real.arctan (Dyadic.toReal (Dyadic.dmin R.hi ⟨1, 0⟩)) := by
          apply Real.arctan_mono
          rw [Dyadic.toReal_dmin, h1d]
          exact le_min hR2 hz1
        exact DInterval.mem_sub ⟨hP1, hP2⟩ ⟨le_trans hL1 hm1, le_trans hm2 hH2⟩

/-- **Positive large-argument branch** (`1 ≤ J.lo`): the identity
`arctan x = π / 2 - arctan x⁻¹` (`Real.arctan_inv_of_pos`).  The reciprocal
interval `R = J.recip out ⊇ {1/y : y ∈ J}` lies in `(0, 1]`, so
`arctanIPosAux` applies. -/
def arctanIPos (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble (⟨1, 0⟩ : Dyadic) J.lo then
    match J.recip out with
    | none => none
    | some R => arctanIPosAux R N out
  else none

/-- **Soundness of `arctanIPos`**: if the checks succeed, the result
contains `arctan y` for every real `y ∈ J`. -/
theorem arctanIPos_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : arctanIPos J N out = some K) : K.mem (Real.arctan y) := by
  have ⟨hy1, hy2⟩ := hy
  unfold arctanIPos at h
  by_cases hchk : Dyadic.ble (⟨1, 0⟩ : Dyadic) J.lo
  · rw [if_pos hchk] at h
    have hJlo : (1:ℝ) ≤ J.lo.toReal := by
      have h := Dyadic.ble_toReal hchk
      rw [Dyadic.toReal_int] at h
      push_cast at h
      exact h
    have hy0 : (0:ℝ) < y := by linarith
    have hy1' : (1:ℝ) ≤ y := le_trans hJlo hy1
    cases hR : J.recip out with
    | none => rw [hR] at h; simp at h
    | some R =>
      rw [hR] at h
      have haux : arctanIPosAux R N out = some K := h
      have hmem : R.mem ((1:ℝ) / y) := J.recip_sound hy hR
      have hsub := arctanIPosAux_sound hmem (one_div_nonneg.mpr (le_of_lt hy0))
        ((div_le_one hy0).mpr hy1') haux
      have hid : Real.arctan y = Real.pi / 2 - Real.arctan (1 / y) := by
        have h := Real.arctan_inv_of_pos hy0
        rw [inv_eq_one_div] at h
        linarith
      rw [hid]
      exact hsub
  · rw [if_neg hchk] at h; simp at h

/-- **Negative large-argument branch** (`J.hi ≤ −1`): odd symmetry
`arctan y = −arctan(−y)` with `−y ∈ J.neg ⊆ [1, ∞)`. -/
def arctanINeg (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble J.hi ⟨-1, 0⟩ then
    (arctanIPos J.neg N out).map DInterval.neg
  else none

/-- **Soundness of `arctanINeg`**: if the checks succeed, the result
contains `arctan y` for every real `y ∈ J`. -/
theorem arctanINeg_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : arctanINeg J N out = some K) : K.mem (Real.arctan y) := by
  unfold arctanINeg at h
  by_cases hchk : Dyadic.ble J.hi ⟨-1, 0⟩
  · rw [if_pos hchk] at h
    cases hs : arctanIPos J.neg N out with
    | none => rw [hs] at h; simp at h
    | some L =>
      rw [hs] at h
      obtain rfl : K = DInterval.neg L := (Option.some.inj h).symm
      have hL := arctanIPos_sound (DInterval.mem_neg hy) hs
      have hid : Real.arctan y = -Real.arctan (-y) := by
        rw [Real.arctan_neg]
        ring
      rw [hid]
      exact DInterval.mem_neg hL
  · rw [if_neg hchk] at h; simp at h

/-- Union hull of two interval results (`none` if either fails — the
enclosure is only sound when *both* branches were computable). -/
def arctanHull (a b : Option DInterval) : Option DInterval :=
  match a, b with
  | some A, some B => some ⟨Dyadic.dmin A.lo B.lo, Dyadic.dmax A.hi B.hi⟩
  | _, _ => none

/-- **Soundness of `arctanHull`**: if either component contains `z`, the
hull contains `z`. -/
theorem arctanHull_sound {a b : Option DInterval} {K : DInterval} {z : ℝ}
    (h : arctanHull a b = some K)
    (hz : (∀ A, a = some A → A.mem z) ∨ (∀ B, b = some B → B.mem z)) :
    K.mem z := by
  unfold arctanHull at h
  cases ha : a with
  | none => rw [ha] at h; simp at h
  | some A =>
    rw [ha] at h
    cases hb : b with
    | none => rw [hb] at h; simp at h
    | some B =>
      rw [hb] at h
      obtain rfl : K = ⟨Dyadic.dmin A.lo B.lo, Dyadic.dmax A.hi B.hi⟩ :=
        (Option.some.inj h).symm
      rcases hz with hz | hz
      · obtain ⟨h1, h2⟩ := hz A ha
        constructor
        · show Dyadic.toReal (Dyadic.dmin A.lo B.lo) ≤ z
          rw [Dyadic.toReal_dmin]
          exact le_trans (min_le_left _ _) h1
        · show z ≤ Dyadic.toReal (Dyadic.dmax A.hi B.hi)
          rw [Dyadic.toReal_dmax]
          exact le_trans h2 (le_max_left _ _)
      · obtain ⟨h1, h2⟩ := hz B hb
        constructor
        · show Dyadic.toReal (Dyadic.dmin A.lo B.lo) ≤ z
          rw [Dyadic.toReal_dmin]
          exact le_trans (min_le_right _ _) h1
        · show z ≤ Dyadic.toReal (Dyadic.dmax A.hi B.hi)
          rw [Dyadic.toReal_dmax]
          exact le_trans h2 (le_max_right _ _)

/-- Interval-level `arctan`, total on all of `ℝ`: the base branch covers
`J ⊆ [-1, 1]`; `1 ≤ J.lo` reduces via `arctan x = π/2 − arctan x⁻¹`
(`arctanIPos`); `J.hi ≤ −1` by odd symmetry (`arctanINeg`); intervals
crossing `±1` are split at the crossing points and the pieces are joined by
hulls (`arctanHull`).  Each piece's own range check makes every branch
independently sound. -/
def arctanI (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.ble J.hi ⟨1, 0⟩ then
    arctanIBase J N out
  else if Dyadic.ble (⟨1, 0⟩ : Dyadic) J.lo then
    arctanIPos J N out
  else if Dyadic.ble J.hi ⟨-1, 0⟩ then
    arctanINeg J N out
  else if Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo then
    -- `−1 ≤ J.lo < 1 < J.hi`: split at `1`
    arctanHull (arctanIBase ⟨J.lo, ⟨1, 0⟩⟩ N out)
      (arctanIPos ⟨⟨1, 0⟩, J.hi⟩ N out)
  else if Dyadic.ble J.hi ⟨1, 0⟩ then
    -- `J.lo < −1 < J.hi ≤ 1`: split at `−1`
    arctanHull (arctanINeg ⟨J.lo, ⟨-1, 0⟩⟩ N out)
      (arctanIBase ⟨⟨-1, 0⟩, J.hi⟩ N out)
  else
    -- `J.lo < −1` and `1 < J.hi`: split at both `−1` and `1`
    arctanHull (arctanINeg ⟨J.lo, ⟨-1, 0⟩⟩ N out)
      (arctanHull (arctanIBase ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩ N out)
        (arctanIPos ⟨⟨1, 0⟩, J.hi⟩ N out))

/-- **Soundness of `arctanI`**: whenever evaluation succeeds, the result
contains `arctan y` for every real `y ∈ J`. -/
theorem arctanI_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : arctanI J N out = some K) : K.mem (Real.arctan y) := by
  have ⟨hy1, hy2⟩ := hy
  unfold arctanI at h
  by_cases h1 : Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo && Dyadic.ble J.hi ⟨1, 0⟩
  · rw [if_pos h1] at h
    exact arctanIBase_sound hy h
  · rw [if_neg h1] at h
    by_cases h2 : Dyadic.ble (⟨1, 0⟩ : Dyadic) J.lo
    · rw [if_pos h2] at h
      exact arctanIPos_sound hy h
    · rw [if_neg h2] at h
      by_cases h3 : Dyadic.ble J.hi ⟨-1, 0⟩
      · rw [if_pos h3] at h
        exact arctanINeg_sound hy h
      · rw [if_neg h3] at h
        by_cases h4 : Dyadic.ble (⟨-1, 0⟩ : Dyadic) J.lo
        · rw [if_pos h4] at h
          apply arctanHull_sound h
          rcases le_total y 1 with hyL | hyR
          · exact Or.inl fun A hA => arctanIBase_sound (J := ⟨J.lo, ⟨1, 0⟩⟩)
              ⟨hy1, by
                show y ≤ Dyadic.toReal (⟨1, 0⟩ : Dyadic)
                rw [Dyadic.toReal_int]
                exact_mod_cast hyL⟩ hA
          · exact Or.inr fun B hB => arctanIPos_sound (J := ⟨⟨1, 0⟩, J.hi⟩)
              ⟨by
                show Dyadic.toReal (⟨1, 0⟩ : Dyadic) ≤ y
                rw [Dyadic.toReal_int]
                exact_mod_cast hyR, hy2⟩ hB
        · rw [if_neg h4] at h
          by_cases h5 : Dyadic.ble J.hi ⟨1, 0⟩
          · rw [if_pos h5] at h
            apply arctanHull_sound h
            rcases le_total y (-1) with hyL | hyR
            · exact Or.inl fun A hA => arctanINeg_sound (J := ⟨J.lo, ⟨-1, 0⟩⟩)
                ⟨hy1, by
                  show y ≤ Dyadic.toReal (⟨-1, 0⟩ : Dyadic)
                  rw [Dyadic.toReal_int]
                  exact_mod_cast hyL⟩ hA
            · exact Or.inr fun B hB => arctanIBase_sound (J := ⟨⟨-1, 0⟩, J.hi⟩)
                ⟨by
                  show Dyadic.toReal (⟨-1, 0⟩ : Dyadic) ≤ y
                  rw [Dyadic.toReal_int]
                  exact_mod_cast hyR, hy2⟩ hB
          · rw [if_neg h5] at h
            apply arctanHull_sound h
            rcases le_total y (-1) with hyL | hyR
            · exact Or.inl fun A hA => arctanINeg_sound (J := ⟨J.lo, ⟨-1, 0⟩⟩)
                ⟨hy1, by
                  show y ≤ Dyadic.toReal (⟨-1, 0⟩ : Dyadic)
                  rw [Dyadic.toReal_int]
                  exact_mod_cast hyL⟩ hA
            · exact Or.inr fun B hB => arctanHull_sound hB (by
                rcases le_total y 1 with hyL1 | hyR1
                · exact Or.inl fun A hA => arctanIBase_sound (J := ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩)
                    ⟨by
                      show Dyadic.toReal (⟨-1, 0⟩ : Dyadic) ≤ y
                      rw [Dyadic.toReal_int]
                      exact_mod_cast hyR,
                     by
                      show y ≤ Dyadic.toReal (⟨1, 0⟩ : Dyadic)
                      rw [Dyadic.toReal_int]
                      exact_mod_cast hyL1⟩ hA
                · exact Or.inr fun A hA => arctanIPos_sound (J := ⟨⟨1, 0⟩, J.hi⟩)
                    ⟨by
                      show Dyadic.toReal (⟨1, 0⟩ : Dyadic) ≤ y
                      rw [Dyadic.toReal_int]
                      exact_mod_cast hyR1, hy2⟩ hA)

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

/-! ## `log` via `artanh`: the semantic layer

The engine identity is `log u = 2·artanh((u-1)/(u+1))` for `u > 0`: the
Möbius substitution `y = (u-1)/(u+1)` maps `[1, 2]` to `[0, 1/3]`, where the
`artanh` series `∑ y^{2j+1}/(2j+1)` converges geometrically (all terms
*positive* — unlike the alternating `arctan` family, so the Leibniz bound
does not apply; the tail is bounded geometrically instead).  The series
identity is derived from Mathlib's complex log Taylor series
(`Complex.hasSum_taylorSeries_log`/`_neg_log`), bridged to `ℝ` by
`Complex.hasSum_re`, and reindexed over odd indices fiberwise. -/

/-- **Engine identity**: `log u = 2·artanh((u-1)/(u+1))` for `u > 0`. -/
theorem log_eq_two_mul_artanh {u : ℝ} (hu : 0 < u) :
    Real.log u = 2 * Real.artanh ((u - 1) / (u + 1)) := by
  have hu1 : (0:ℝ) < u + 1 := by linarith
  have hu2 : u + 1 ≠ 0 := by linarith
  have hy : ((u - 1) / (u + 1)) ∈ Set.Icc (-1) 1 := by
    constructor
    · rw [le_div_iff₀ hu1]; linarith
    · rw [div_le_iff₀ hu1]; linarith
  have h1 : 1 + (u - 1) / (u + 1) = 2 * u / (u + 1) := by
    field_simp
    linarith
  have h2 : 1 - (u - 1) / (u + 1) = 2 / (u + 1) := by
    field_simp
    linarith
  have hfrac : (2 * u / (u + 1)) / (2 / (u + 1)) = u := by
    field_simp
  rw [Real.artanh_eq_half_log hy, h1, h2, hfrac]
  ring

/-- The real Taylor series of `log(1-z)` (`Σ zⁿ/n = -log(1-z)`, `|z| < 1`),
bridged from `Complex.hasSum_taylorSeries_neg_log`. -/
theorem real_hasSum_neg_log {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ ↦ y ^ n / (n : ℝ)) (-Real.log (1 - y)) := by
  have hnorm : ‖(y : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hc := Complex.hasSum_taylorSeries_neg_log hnorm
  have hre := Complex.hasSum_re hc
  have hz : ((1:ℂ) - (y:ℂ)) = (((1 - y : ℝ) : ℂ)) := by norm_cast
  rw [hz] at hre
  rw [Complex.neg_re, Complex.log_ofReal_re] at hre
  have hcoef : (fun n : ℕ ↦ (((y : ℂ) ^ n / ((n : ℕ) : ℂ)) : ℂ).re)
      = (fun n : ℕ ↦ y ^ n / (n : ℝ)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [← Complex.ofReal_pow]
      have hn2 : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [hn2, ← Complex.ofReal_div, Complex.ofReal_re]
  rwa [hcoef] at hre

/-- The real Taylor series of `log(1+y)` (`Σ (-1)^{n+1} yⁿ/n = log(1+y)`,
`|y| < 1`), bridged from `Complex.hasSum_taylorSeries_log`. -/
theorem real_hasSum_log_one_add {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) * y ^ n / (n : ℝ)) (Real.log (1 + y)) := by
  have hnorm : ‖(y : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hc := Complex.hasSum_taylorSeries_log hnorm
  have hre := Complex.hasSum_re hc
  have hz : ((1:ℂ) + (y:ℂ)) = (((1 + y : ℝ) : ℂ)) := by norm_cast
  rw [hz] at hre
  rw [Complex.log_ofReal_re] at hre
  have hcoef : (fun n : ℕ ↦ ((((-1 : ℂ) ^ (n + 1) * (y : ℂ) ^ n) / ((n : ℕ) : ℂ)) : ℂ).re)
      = (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) * y ^ n / (n : ℝ)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hc : (((-1 : ℂ) ^ (n + 1) : ℂ)) = (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
        norm_cast
      rw [hc, ← Complex.ofReal_pow]
      have hn2 : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [hn2, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  rwa [hcoef] at hre

/-- **The `artanh` power series** `∑ y^{2n+1}/(2n+1) = artanh y` on `|y| < 1`:
even terms cancel between the two log series; odd terms double. -/
theorem real_hasSum_artanh {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ ↦ y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) (Real.artanh y) := by
  rw [abs_lt] at hy
  have hnorm : |y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h1 := real_hasSum_log_one_add hnorm
  have h2 := real_hasSum_neg_log hnorm
  have hdiv : Real.log (1 + y) + -Real.log (1 - y)
      = Real.log ((1 + y) / (1 - y)) := by
    rw [Real.log_div (by linarith : (1:ℝ) + y ≠ 0) (by linarith : (1:ℝ) - y ≠ 0)]
    ring
  have hmem : y ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hhalf := Real.artanh_eq_half_log hmem
  -- combine the two coefficient families: even `n` cancel, odd `n` double
  have hsum := h1.add h2
  have hfe : (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) * y ^ n / (n : ℝ) + y ^ n / (n : ℝ))
      = (fun n : ℕ ↦ (((-1 : ℝ) ^ (n + 1) + 1) * y ^ n) / (n : ℝ)) := funext fun n => by
    ring
  rw [hfe] at hsum
  rw [hdiv] at hsum
  -- reindex over `n = k*2 + b`, `b ∈ Fin 2`
  have hre : HasSum (fun p : ℕ × Fin 2 ↦
        (((-1 : ℝ) ^ ((p.1 * 2 + (p.2 : ℕ)) + 1) + 1) * y ^ (p.1 * 2 + (p.2 : ℕ)))
          / ((p.1 * 2 + (p.2 : ℕ) : ℕ) : ℝ))
      (Real.log ((1 + y) / (1 - y))) :=
    (Nat.divModEquiv 2).symm.hasSum_iff.mpr hsum
  have hfib : ∀ k : ℕ,
      HasSum (fun b : Fin 2 ↦ (((-1 : ℝ) ^ ((k * 2 + ↑b) + 1) + 1) * y ^ (k * 2 + ↑b))
          / (↑(k * 2 + ↑b) : ℝ))
        (2 * y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    intro k
    convert! hasSum_fintype (_ : Fin 2 → ℝ) using 1
    rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    have hodd : (-1 : ℝ) ^ (k * 2 + 0 + 1) = -1 := by
      rw [show k * 2 + 0 + 1 = 2 * k + 1 from by ring]
      exact Odd.neg_one_pow ⟨k, by omega⟩
    have hev : (-1 : ℝ) ^ (k * 2 + 1 + 1) = 1 := by
      rw [show k * 2 + 1 + 1 = 2 * k + 2 from by ring]
      exact Even.neg_one_pow ⟨k + 1, by omega⟩
    simp only [hodd, hev]
    simp only [Nat.mul_zero, zero_add, Nat.add_zero, mul_one, pow_zero,
      Nat.mul_one, neg_one_mul, neg_add_cancel, zero_mul, zero_div,
      add_zero, one_mul]
    field_simp
    ring
  have hfib2 : HasSum (fun k : ℕ ↦ 2 * y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      (Real.log ((1 + y) / (1 - y))) := hre.prod_fiberwise hfib
  have hhalf' : Real.artanh y = (2:ℝ)⁻¹ * Real.log ((1 + y) / (1 - y)) := by
    rw [hhalf]; field_simp
  have hfe2 : (fun k : ℕ ↦ (2:ℝ)⁻¹ * (2 * y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)))
      = fun k : ℕ ↦ y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := funext fun k => by field_simp
  have hfin := hfib2.mul_left (2:ℝ)⁻¹
  rw [hfe2] at hfin
  rw [hhalf']
  exact hfin

/-- **Partial-sum bounds for `artanh`** (semantic layer): for `0 ≤ y < 1`
the `N`-term partial sum of `∑ y^{2j+1}/(2j+1)` under-estimates `artanh y`,
and the tail is bounded geometrically:
`artanh y ≤ s_N + y^{2N+1}/(1-y²)`. -/
theorem real_artanh_partial_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤ Real.artanh y ∧
    Real.artanh y ≤ (∑ i ∈ Finset.range N, y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))
      + y ^ (2 * N + 1) / ((1 : ℝ) - y ^ 2) := by
  have hnorm : |y| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hy2 : (0:ℝ) ≤ y ^ 2 := by positivity
  have hy2lt : y ^ 2 < 1 := by nlinarith
  set S : ℕ → ℝ := fun i ↦ y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) with hS
  have hsum : HasSum S (Real.artanh y) := real_hasSum_artanh hnorm
  have hf : Summable S := hsum.summable
  -- the geometric majorant of the tail and its exact sum
  set G : ℕ → ℝ := fun k ↦ y ^ (2 * N + 1) * (y ^ 2) ^ k with hG
  have hGsum : HasSum G (y ^ (2 * N + 1) * (1 - y ^ 2)⁻¹) := by
    rw [hG]
    exact (hasSum_geometric_of_lt_one hy2 hy2lt).mul_left _
  have hGsumm : Summable G := hGsum.summable
  have hGval : ∑' k : ℕ, G k = y ^ (2 * N + 1) * (1 - y ^ 2)⁻¹ := hGsum.tsum_eq
  have hterm : ∀ k : ℕ, S (k + N) ≤ G k := by
    intro k
    simp only [hS, hG]
    have hexp : y ^ (2 * (k + N) + 1) = y ^ (2 * N + 1) * (y ^ 2) ^ k := by
      rw [show 2 * (k + N) + 1 = (2 * N + 1) + 2 * k from by omega, pow_add, ← pow_mul]
    calc y ^ (2 * (k + N) + 1) / ((2 * (k + N) + 1 : ℕ) : ℝ)
        ≤ y ^ (2 * (k + N) + 1) := by
          have h1le : (1:ℝ) ≤ ((2 * (k + N) + 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : (1:ℕ) ≤ 2 * (k + N) + 1)
          have hpos : (0:ℝ) < ((2 * (k + N) + 1 : ℕ) : ℝ) := by positivity
          rw [div_le_iff₀ hpos]
          exact le_mul_of_one_le_right (pow_nonneg hy0 _) h1le
      _ = y ^ (2 * N + 1) * (y ^ 2) ^ k := hexp
  have htail : ∑' k : ℕ, S (k + N) ≤ y ^ (2 * N + 1) / ((1 : ℝ) - y ^ 2) := by
    have hinj : Function.Injective (fun k : ℕ ↦ k + N) := fun a b h => by
      simpa using h
    have hSsumm : Summable (fun k : ℕ ↦ S (k + N)) := hf.comp_injective hinj
    calc ∑' k : ℕ, S (k + N) ≤ ∑' k : ℕ, G k := hSsumm.tsum_le_tsum hterm hGsumm
      _ = y ^ (2 * N + 1) * (1 - y ^ 2)⁻¹ := hGval
      _ = y ^ (2 * N + 1) / ((1 : ℝ) - y ^ 2) := by rw [inv_eq_one_div]; ring
  have hsplit := hf.sum_add_tsum_nat_add N
  rw [hsum.tsum_eq] at hsplit
  have htail0 : (0:ℝ) ≤ ∑' k : ℕ, S (k + N) := by
    refine tsum_nonneg fun k => ?_
    simp only [hS]
    exact div_nonneg (pow_nonneg hy0 _) (Nat.cast_nonneg _)
  constructor
  · linarith
  · linarith

/-! ## `log` via `artanh`: the checked dyadic layer

`logAcc` accumulates the *positive* series `∑ y^{2j+1}/(2j+1)` with
outward per-term rounding — each term `d.npow (2j+1)` (exact dyadic power)
is divided by the odd integer `2j+1` at the *per-term* granularity
`(2j+1) * out` (so `divFloorQ`'s exponent precondition holds), the floor
going to the lower sum and the one-ulp-up value to the upper sum; exact
`Dyadic.add` keeps the sums exact.  `logInterval` evaluates `u ∈ [1, 2]`:
`d = y_low ≤ (u-1)/(u+1) =: y_true ≤ y_high = d + one ulp`, the check
`y_high ≤ 5/16` (in particular `< 1`, and `5/16 < 1/3` covers the whole
window), the series at `y_low` gives the lower bracket (the tail is
nonnegative) and the series at `y_high` plus the *exact* remainder bound
`9/8 · y_high^{2N+1}` (valid since `1/(1-t²) ≤ 9/8` for `t ≤ 5/16`:
`256/231 < 9/8`) gives the upper bracket. -/

/-- Positive-term outward-rounded Taylor accumulator for
`∑ d^{2i+1}/(2i+1)`. -/
def logAcc (d : Dyadic) (out : Int) :
    ℕ → ℕ → Dyadic → Dyadic → Option (Dyadic × Dyadic)
  | 0, _, lw, hg => some (lw, hg)
  | fuel + 1, i, lw, hg =>
      match Dyadic.divFloorQ (d.npow (2 * i + 1)) ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩
          ((2 * i + 1) * out) with
      | none => none
      | some q =>
          logAcc d out fuel (i + 1) (lw.add q) (hg.add ⟨q.m + 1, (2 * i + 1) * out⟩)

/-- **Soundness of `logAcc`**: if every rounded term brackets its exact
term, the final `(lw, hg)` brackets the partial sums of the exact series. -/
theorem logAcc_spec (d : Dyadic) (out : Int) (A : ℕ → ℝ)
    (hA : ∀ i (q : Dyadic),
      Dyadic.divFloorQ (d.npow (2 * i + 1)) ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩ ((2 * i + 1) * out)
        = some q →
        q.toReal ≤ A i ∧ A i ≤ Dyadic.toReal ⟨q.m + 1, (2 * i + 1) * out⟩) :
    ∀ (fuel i : ℕ) (lw hg : Dyadic),
      lw.toReal ≤ ∑ j ∈ Finset.range i, A j →
      ∑ j ∈ Finset.range i, A j ≤ hg.toReal →
      ∀ res, logAcc d out fuel i lw hg = some res →
        ((res.1).toReal ≤ ∑ j ∈ Finset.range (i + fuel), A j ∧
          ∑ j ∈ Finset.range (i + fuel), A j ≤ (res.2).toReal) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i lw hg hlo hhi res h
    obtain rfl : res = (lw, hg) := (Option.some.inj (show some (lw, hg) = some res from h)).symm
    rw [Nat.add_zero]
    exact ⟨hlo, hhi⟩
  | succ fuel ih =>
    intro i lw hg hlo hhi res h
    have hstep : (match Dyadic.divFloorQ (d.npow (2 * i + 1)) ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩
          ((2 * i + 1) * out) with
        | none => none
        | some q =>
            logAcc d out fuel (i + 1) (lw.add q) (hg.add ⟨q.m + 1, (2 * i + 1) * out⟩))
        = some res := h
    cases hq : Dyadic.divFloorQ (d.npow (2 * i + 1)) ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩
        ((2 * i + 1) * out) with
    | none => rw [hq] at hstep; simp at hstep
    | some q =>
      rw [hq] at hstep
      obtain ⟨hq1, hq2⟩ := hA i q hq
      have hU : Dyadic.toReal ⟨q.m + 1, (2 * i + 1) * out⟩
          = q.toReal + (Dyadic.ulp ((2 * i + 1) * out)).toReal :=
        toReal_succ_ulp (Dyadic.divFloorQ_e hq)
      rw [show i + (fuel + 1) = (i + 1) + fuel from by omega]
      have hsucc : ∑ j ∈ Finset.range (i + 1), A j
          = (∑ j ∈ Finset.range i, A j) + A i := Finset.sum_range_succ A i
      exact ih (i + 1) (lw.add q) (hg.add ⟨q.m + 1, (2 * i + 1) * out⟩)
        (by rw [Dyadic.toReal_add, hsucc]; exact add_le_add hlo hq1)
        (by rw [Dyadic.toReal_add, hsucc]; exact add_le_add hhi hq2)
        res hstep

private theorem mantissa_nonneg {a : Dyadic} (h : 0 ≤ a.toReal) : 0 ≤ a.m := by
  by_contra hcon
  rw [Dyadic.toReal_def] at h
  push_neg at hcon
  have hz : ((a.m : ℝ) * (2:ℝ) ^ a.e) < 0 :=
    mul_neg_of_neg_of_pos (by exact_mod_cast hcon) (by positivity)
  linarith

private theorem mantissa_neg {a : Dyadic} (h : a.m < 0) : a.toReal < 0 := by
  rw [Dyadic.toReal_def]
  exact mul_neg_of_neg_of_pos (by exact_mod_cast h) (by positivity)

/-- Interval enclosure of `log u.toReal` for `u.toReal ∈ [1, 2]`: `N`
positive series terms of `2·artanh((u-1)/(u+1))` with outward per-term
rounding at granularity `out`, plus the exact remainder bound
`9/8 · y_high^{2N+1}` on the upper side. -/
def logInterval (u : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  match Dyadic.divFloorQ (u.dsub ⟨1, 0⟩) (u.add ⟨1, 0⟩) out with
  | none => none
  | some d =>
      if Dyadic.ble ⟨d.m + 1, out⟩ ⟨3, -3⟩ then
        match logAcc d out N 0 ⟨0, 0⟩ ⟨0, 0⟩,
            logAcc ⟨d.m + 1, out⟩ out N 0 ⟨0, 0⟩ ⟨0, 0⟩ with
        | some (lw, _), some (_, hg) =>
            some (DInterval.mk (lw.add lw)
              (Dyadic.add (Dyadic.add hg
                (Dyadic.mul (Dyadic.mul ⟨(7:ℤ), 0⟩ (Dyadic.npow ⟨d.m + 1, out⟩ (2 * N + 1))) ⟨1, -2⟩))
                (Dyadic.add hg
                  (Dyadic.mul (Dyadic.mul ⟨(7:ℤ), 0⟩ (Dyadic.npow ⟨d.m + 1, out⟩ (2 * N + 1))) ⟨1, -2⟩))))
        | _, _ => none
      else none

set_option maxHeartbeats 10000000 in
/-- **Soundness of `logInterval`** (over `ℝ`): on `1 ≤ u.toReal ≤ 2`, the
returned interval contains `log` of the real semantics. -/
theorem logInterval_sound {u : Dyadic} {N : ℕ} {out : Int} {I : DInterval}
    (h : logInterval u N out = some I) (h1 : Dyadic.toReal ⟨1, 0⟩ ≤ u.toReal)
    (h2 : u.toReal ≤ 2) :
    I.mem (Real.log u.toReal) := by
  rw [Dyadic.toReal_int] at h1
  push_cast at h1
  have hden : (0:ℝ) < (u.add ⟨1, 0⟩).toReal := by
    rw [Dyadic.toReal_add, Dyadic.toReal_int]
    push_cast
    linarith
  have hnum : (0:ℝ) ≤ (u.dsub ⟨1, 0⟩).toReal := by
    rw [Dyadic.toReal_dsub, Dyadic.toReal_int]
    push_cast
    linarith
  have hy : (u.dsub ⟨1, 0⟩).toReal / (u.add ⟨1, 0⟩).toReal
      = (u.toReal - 1) / (u.toReal + 1) := by
    rw [Dyadic.toReal_dsub, Dyadic.toReal_add, Dyadic.toReal_int]; ring
  simp only [logInterval] at h
  cases hd : Dyadic.divFloorQ (u.dsub ⟨1, 0⟩) (u.add ⟨1, 0⟩) out with
  | none => rw [hd] at h; dsimp only at h; simp at h
  | some d =>
    obtain ⟨hlow, hhigh⟩ := Dyadic.divFloorQ_spec hd
    rw [hy] at hlow hhigh
    have hdm : (0:ℤ) ≤ d.m := by
      rcases Dyadic.divFloorQ_cases hd with
        ⟨hbpos, _, hdq⟩ | ⟨hbneg, _, hdq⟩ | ⟨hbpos, _, hdq⟩ | ⟨hbneg, _, hdq⟩
      · rw [hdq]
        exact Int.ediv_nonneg (mul_nonneg (mantissa_nonneg hnum)
          (by exact_mod_cast Nat.zero_le ((2:ℕ) ^ _))) (by omega)
      · exact absurd (mantissa_neg hbneg) (by linarith)
      · rw [hdq]
        exact Int.ediv_nonneg (mantissa_nonneg hnum)
          (le_of_lt (Int.mul_pos hbpos (pow_pos (by norm_num : (0:ℤ) < 2) _)))
      · exact absurd (mantissa_neg hbneg) (by linarith)
    rw [hd] at h
    dsimp only at h
    by_cases hchk : Dyadic.ble ⟨d.m + 1, out⟩ ⟨3, -3⟩
    · have h38 : Dyadic.toReal ⟨d.m + 1, out⟩ ≤ (3:ℝ) / 8 := by
        have hb := Dyadic.ble_toReal hchk
        have hb38 : Dyadic.toReal ⟨3, -3⟩ = (3:ℝ) / 8 := by
          rw [Dyadic.toReal_def]; norm_num
        rw [hb38] at hb
        exact hb
      rw [if_pos hchk] at h
      cases hloop1 : logAcc d out N 0 ⟨0, 0⟩ ⟨0, 0⟩ with
      | none => simp only [hloop1] at h; simp at h
      | some lr1 =>
        obtain ⟨lw, _⟩ := lr1
        simp only [hloop1] at h
        cases hloop2 : logAcc ⟨d.m + 1, out⟩ out N 0 ⟨0, 0⟩ ⟨0, 0⟩ with
        | none => simp only [hloop2] at h; simp at h
        | some lr2 =>
          obtain ⟨_, hg⟩ := lr2
          simp only [hloop2, Option.some.injEq] at h
          obtain rfl := h.symm
          set Ad : ℕ → ℝ := fun i ↦ d.toReal ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) with hAd
          set Ah : ℕ → ℝ := fun i ↦ Dyadic.toReal ⟨d.m + 1, out⟩ ^ (2 * i + 1)
              / ((2 * i + 1 : ℕ) : ℝ) with hAh
          have hAd' : ∀ i (q : Dyadic),
              Dyadic.divFloorQ (d.npow (2 * i + 1)) ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩
                  ((2 * i + 1) * out) = some q →
              q.toReal ≤ Ad i ∧ Ad i ≤ Dyadic.toReal ⟨q.m + 1, (2 * i + 1) * out⟩ := by
            intro i q hq
            obtain ⟨hs1, hs2⟩ := Dyadic.divFloorQ_spec hq
            rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hs1 hs2
            exact ⟨hs1, hs2⟩
          have hAh' : ∀ i (q : Dyadic),
              Dyadic.divFloorQ ((⟨d.m + 1, out⟩ : Dyadic).npow (2 * i + 1))
                  ⟨((2 * i + 1 : ℕ) : ℤ), 0⟩
                  ((2 * i + 1) * out) = some q →
              q.toReal ≤ Ah i ∧ Ah i ≤ Dyadic.toReal ⟨q.m + 1, (2 * i + 1) * out⟩ := by
            intro i q hq
            obtain ⟨hs1, hs2⟩ := Dyadic.divFloorQ_spec hq
            rw [Dyadic.toReal_npow, Dyadic.toReal_int] at hs1 hs2
            exact ⟨hs1, hs2⟩
          obtain ⟨h1a, h1b⟩ := logAcc_spec d out Ad hAd' N 0 ⟨0, 0⟩ ⟨0, 0⟩
            (by rw [Dyadic.toReal_def]; simp) (by rw [Dyadic.toReal_def]; simp) _ hloop1
          obtain ⟨h2a, h2b⟩ := logAcc_spec ⟨d.m + 1, out⟩ out Ah hAh' N 0 ⟨0, 0⟩ ⟨0, 0⟩
            (by rw [Dyadic.toReal_def]; simp) (by rw [Dyadic.toReal_def]; simp) _ hloop2
          rw [Nat.zero_add] at h1a h1b h2a h2b
          dsimp only at h1a h2b
          have hupos : (0:ℝ) < u.toReal := by linarith
          have hlog := log_eq_two_mul_artanh hupos
          have hy0 : (0:ℝ) ≤ (u.toReal - 1) / (u.toReal + 1) := by
            apply div_nonneg <;> linarith
          have hy3 : (u.toReal - 1) / (u.toReal + 1) ≤ 1 / 3 := by
            rw [div_le_iff₀ (by linarith : (0:ℝ) < u.toReal + 1)]
            nlinarith
          have hyd : d.toReal ≤ (u.toReal - 1) / (u.toReal + 1) := hlow
          have hyh : (u.toReal - 1) / (u.toReal + 1) ≤ Dyadic.toReal ⟨d.m + 1, out⟩ := hhigh
          have hlt1 : Dyadic.toReal ⟨d.m + 1, out⟩ < 1 := by linarith
          have hb0 : (0:ℝ) ≤ d.toReal := by
            rw [Dyadic.toReal_def]
            exact mul_nonneg (by exact_mod_cast hdm) (by positivity)
          have hb1 : (0:ℝ) ≤ Dyadic.toReal ⟨d.m + 1, out⟩ := by
            rw [Dyadic.toReal_def]
            exact mul_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ d.m + 1)) (by positivity)
          have hpartd := real_artanh_partial_bounds (hy0 := hb0) (hy1 := by linarith) N
          have hparth := real_artanh_partial_bounds (hy0 := hb1) (hy1 := hlt1) N
          have hmono1 : Real.artanh d.toReal
              ≤ Real.artanh ((u.toReal - 1) / (u.toReal + 1)) :=
            Real.artanh_le_artanh (by linarith) (by linarith) hyd
          have hmono2 : Real.artanh ((u.toReal - 1) / (u.toReal + 1))
              ≤ Real.artanh (Dyadic.toReal ⟨d.m + 1, out⟩) :=
            Real.artanh_le_artanh (by linarith) hlt1 hyh
          have ht2 : (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2 ≤ (9:ℝ) / 64 := by
            have hq1 : (0:ℝ) ≤ (3:ℝ)/8 - Dyadic.toReal ⟨d.m + 1, out⟩ := by linarith
            have hq2 : (0:ℝ) ≤ (3:ℝ)/8 + Dyadic.toReal ⟨d.m + 1, out⟩ := by linarith
            have hq3 : (0:ℝ) ≤ ((3:ℝ)/8 - Dyadic.toReal ⟨d.m + 1, out⟩)
                  * ((3:ℝ)/8 + Dyadic.toReal ⟨d.m + 1, out⟩) := mul_nonneg hq1 hq2
            have hq4 : ((3:ℝ)/8 - Dyadic.toReal ⟨d.m + 1, out⟩)
                  * ((3:ℝ)/8 + Dyadic.toReal ⟨d.m + 1, out⟩)
                = (9:ℝ)/64 - (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2 := by ring
            linarith [hq3, hq4]
          have hR : Dyadic.toReal
              (Dyadic.mul (Dyadic.mul ⟨(7:ℤ), 0⟩
                (Dyadic.npow (⟨d.m + 1, out⟩ : Dyadic) (2 * N + 1))) ⟨1, -2⟩)
              = (7:ℝ) / 4 * (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1) := by
            have h14 : Dyadic.toReal ⟨1, -2⟩ = (1:ℝ) / 4 := by
              rw [Dyadic.toReal_def]; norm_num
            rw [Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_int, Dyadic.toReal_npow,
              h14]
            ring
          constructor
          · show Dyadic.toReal (lw.add lw) ≤ Real.log u.toReal
            rw [Dyadic.toReal_add, hlog]
            calc (lw.toReal + lw.toReal)
                ≤ 2 * (∑ i ∈ Finset.range N, Ad i) := by linarith
              _ ≤ 2 * Real.artanh d.toReal :=
                    mul_le_mul_of_nonneg_left hpartd.1 (by norm_num)
              _ ≤ 2 * Real.artanh ((u.toReal - 1) / (u.toReal + 1)) :=
                    mul_le_mul_of_nonneg_left hmono1 (by norm_num)
          · have hhi : Dyadic.toReal
                ((hg.add
                    (Dyadic.mul (Dyadic.mul ⟨(7:ℤ), 0⟩
                      (Dyadic.npow (⟨d.m + 1, out⟩ : Dyadic) (2 * N + 1))) ⟨1, -2⟩)).add
                  (hg.add
                    (Dyadic.mul (Dyadic.mul ⟨(7:ℤ), 0⟩
                      (Dyadic.npow (⟨d.m + 1, out⟩ : Dyadic) (2 * N + 1))) ⟨1, -2⟩)))
                = 2 * (hg.toReal
                    + (7:ℝ) / 4 * (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1)) := by
              rw [Dyadic.toReal_add, Dyadic.toReal_add, hR]
              ring
            have hUB : Real.artanh ((u.toReal - 1) / (u.toReal + 1))
                ≤ hg.toReal
                  + (7:ℝ) / 4 * (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1) := by
              have h2 := hparth.2
              have h64 : ((9:ℝ)/64 : ℝ) < 1 := by norm_num
              have hpos : (0:ℝ) < (1:ℝ) - (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2 := by
                linarith
              have htnonneg : (0:ℝ) ≤ (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1) :=
                pow_nonneg hb1 _
              have hlin : (1:ℝ) ≤ (7:ℝ) / 4
                  * ((1:ℝ) - (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2) := by
                have h55 : ((55:ℝ)/64 : ℝ) ≤ 1 - (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2 := by
                  linarith
                have hmul := mul_le_mul_of_nonneg_left h55
                  (by norm_num : (0:ℝ) ≤ (7:ℝ) / 4)
                have hnum : (1:ℝ) ≤ (7:ℝ) / 4 * ((55:ℝ) / 64) := by norm_num
                linarith
              have hrem' : (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1)
                    / ((1:ℝ) - (Dyadic.toReal ⟨d.m + 1, out⟩) ^ 2)
                  ≤ (7:ℝ) / 4 * (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1) := by
                rw [div_le_iff₀ hpos]
                nlinarith [hlin, htnonneg]
              linarith
            have h1'' : (2:ℝ) * Real.artanh ((u.toReal - 1) / (u.toReal + 1))
                  ≤ 2 * (hg.toReal + (7:ℝ) / 4
                      * (Dyadic.toReal ⟨d.m + 1, out⟩) ^ (2 * N + 1)) :=
              mul_le_mul_of_nonneg_left hUB (by norm_num)
            rw [hlog]
            dsimp only
            linarith [h1'', hhi]
    · rw [if_neg hchk] at h; simp at h

/-! ## Dyadic enclosure of `log 2` and integer scaling -/

/-- Dyadic enclosure of `log 2`: `[45425·2⁻¹⁶, 45430·2⁻¹⁶]`, obtained from
`logInterval ⟨2, 0⟩ 8 (-16)` (`2·artanh(1/3)` with 8 series terms at
granularity `2⁻¹⁶` plus the exact `7/4` remainder bound) rounded outward to
granularity `2⁻¹⁶`. -/
def log2D : DInterval := ⟨⟨45425, -16⟩, ⟨45430, -16⟩⟩

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem log2D_mem : log2D.mem (Real.log 2) := by
  have hcert : logInterval ⟨2, 0⟩ 8 (-16)
      = some ⟨⟨1224664839723253066757532368272827966897654092888104932391667849000070544, -240⟩,
              ⟨21041551031267394410589974817095804438051737544098602624748996252542645910946185216, -274⟩⟩ := by
    decide
  have h1 : Dyadic.toReal ⟨1, 0⟩ ≤ Dyadic.toReal ⟨2, 0⟩ := by
    rw [Dyadic.toReal_int, Dyadic.toReal_int]; norm_num
  have h2 : Dyadic.toReal ⟨2, 0⟩ ≤ 2 := by rw [Dyadic.toReal_int]; norm_num
  obtain ⟨hlo, hhi⟩ := logInterval_sound hcert h1 h2
  have htwo : Dyadic.toReal ⟨2, 0⟩ = 2 := by rw [Dyadic.toReal_int]; norm_num
  have hlo' : Dyadic.toReal
      ⟨1224664839723253066757532368272827966897654092888104932391667849000070544, -240⟩
      ≤ Real.log (Dyadic.toReal ⟨2, 0⟩) := hlo
  have hhi' : Real.log (Dyadic.toReal ⟨2, 0⟩) ≤ Dyadic.toReal
      ⟨21041551031267394410589974817095804438051737544098602624748996252542645910946185216, -274⟩ := hhi
  rw [htwo, Dyadic.toReal_def] at hlo' hhi'
  constructor
  · rw [Dyadic.toReal_def]
    show ((45425:ℤ):ℝ) * (2:ℝ)^(-16:ℤ) ≤ Real.log 2
    have hk : ((45425:ℤ) * (2:ℤ)^224 : ℤ)
        ≤ 1224664839723253066757532368272827966897654092888104932391667849000070544 := by
      decide
    have hz : ((2:ℝ)^(-16:ℤ):ℝ) = (2:ℝ)^224 * (2:ℝ)^(-240:ℤ) := by
      have he : ((2:ℝ)^(-16:ℤ):ℝ) = (2:ℝ)^((-240:ℤ)+224) := by norm_num
      have hbz := zpow_add₀ (show (2:ℝ) ≠ 0 by norm_num) (-240 : ℤ) 224
      rw [he, hbz]
      ring
    have hk0 : (((45425 * 2^224 : ℤ):ℝ)) ≤ (((1224664839723253066757532368272827966897654092888104932391667849000070544 : ℤ):ℝ)) := by
      exact_mod_cast hk
    have hmul : ((45425:ℤ):ℝ) * ((2:ℝ)^224 * (2:ℝ)^(-240:ℤ))
        = (((45425 * 2^224 : ℤ):ℝ)) * (2:ℝ)^(-240:ℤ) := by
      push_cast; ring
    rw [hz, hmul]
    exact le_trans (mul_le_mul_of_nonneg_right hk0
      (by norm_num : (0:ℝ) ≤ (2:ℝ)^(-240:ℤ))) hlo'
  · rw [Dyadic.toReal_def]
    show Real.log 2 ≤ ((45430:ℤ):ℝ) * (2:ℝ)^(-16:ℤ)
    have hk : 21041551031267394410589974817095804438051737544098602624748996252542645910946185216
        ≤ (45430:ℤ) * (2:ℤ)^258 := by
      decide
    have hz : ((2:ℝ)^(-16:ℤ):ℝ) = (2:ℝ)^258 * (2:ℝ)^(-274:ℤ) := by
      have he : ((2:ℝ)^(-16:ℤ):ℝ) = (2:ℝ)^((-274:ℤ)+258) := by norm_num
      have hbz := zpow_add₀ (show (2:ℝ) ≠ 0 by norm_num) (-274 : ℤ) 258
      rw [he, hbz]
      ring
    have hk0 : (((21041551031267394410589974817095804438051737544098602624748996252542645910946185216 : ℤ):ℝ)) ≤ (((45430 * 2^258 : ℤ):ℝ)) := by
      exact_mod_cast hk
    have hmul : ((45430:ℤ):ℝ) * ((2:ℝ)^258 * (2:ℝ)^(-274:ℤ))
        = (((45430 * 2^258 : ℤ):ℝ)) * (2:ℝ)^(-274:ℤ) := by
      push_cast; ring
    rw [hz, hmul]
    exact le_trans hhi' (mul_le_mul_of_nonneg_right hk0 (by norm_num : (0:ℝ) ≤ (2:ℝ)^(-274:ℤ)))

/-- Scaling of an interval by an integer (reversing the endpoints for
negative `k`): `iscale I k` contains `k * x` whenever `I` contains `x`. -/
def iscale (I : DInterval) (k : Int) : DInterval :=
  if 0 ≤ k then ⟨⟨k * I.lo.m, I.lo.e⟩, ⟨k * I.hi.m, I.hi.e⟩⟩
  else ⟨⟨k * I.hi.m, I.hi.e⟩, ⟨k * I.lo.m, I.lo.e⟩⟩

theorem iscale_mem {I : DInterval} {x : ℝ} (hx : I.mem x) (k : Int) :
    (iscale I k).mem (k * x) := by
  obtain ⟨h1, h2⟩ := hx
  rw [Dyadic.toReal_def] at h1 h2
  unfold iscale DInterval.mem
  split
  · next hk =>
    refine ⟨?_, ?_⟩
    · simp only [Dyadic.toReal_def]
      rw [show (((k:ℤ) * I.lo.m : ℤ):ℝ) * (2:ℝ)^I.lo.e
            = (k:ℝ) * (((I.lo.m : ℤ):ℝ) * (2:ℝ)^I.lo.e) from by push_cast; ring]
      exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast hk)
    · simp only [Dyadic.toReal_def]
      rw [show (((k:ℤ) * I.hi.m : ℤ):ℝ) * (2:ℝ)^I.hi.e
            = (k:ℝ) * (((I.hi.m : ℤ):ℝ) * (2:ℝ)^I.hi.e) from by push_cast; ring]
      exact mul_le_mul_of_nonneg_left h2 (by exact_mod_cast hk)
  · next hk =>
    refine ⟨?_, ?_⟩
    · simp only [Dyadic.toReal_def]
      rw [show (((k:ℤ) * I.hi.m : ℤ):ℝ) * (2:ℝ)^I.hi.e
            = (k:ℝ) * (((I.hi.m : ℤ):ℝ) * (2:ℝ)^I.hi.e) from by push_cast; ring]
      have hk' : (k:ℝ) ≤ 0 := by
        have hk'' : (k:ℤ) ≤ 0 := by omega
        exact_mod_cast hk''
      exact mul_le_mul_of_nonpos_left h2 hk'
    · simp only [Dyadic.toReal_def]
      rw [show (((k:ℤ) * I.lo.m : ℤ):ℝ) * (2:ℝ)^I.lo.e
            = (k:ℝ) * (((I.lo.m : ℤ):ℝ) * (2:ℝ)^I.lo.e) from by push_cast; ring]
      have hk' : (k:ℝ) ≤ 0 := by
        have hk'' : (k:ℤ) ≤ 0 := by omega
        exact_mod_cast hk''
      exact mul_le_mul_of_nonpos_left h1 hk'

/-! ## `2^k` range reduction and the interval-level `ln` wrapper -/

/-- Point enclosure of `log z.toReal` for `z.toReal > 0`: write
`z.toReal = u·2^k` with `u.toReal ∈ [1, 2)` (`k = ⌊log₂ z.toReal⌋` via
`Nat.log2` of the mantissa), enclose `log u` by `logInterval`, and add the
`k·log 2` contribution via `log2D.iscale k`. -/
def logPoint (z : Dyadic) (N : ℕ) (out : Int) : Option DInterval :=
  if z.isPos then
    match logInterval ⟨z.m, -(Nat.log2 z.m.toNat : ℤ)⟩ N out with
    | some J => some (J.add (iscale log2D ((Nat.log2 z.m.toNat : ℤ) + z.e)))
    | none => none
  else none

set_option maxRecDepth 4000 in
theorem logPoint_sound {z : Dyadic} {N : ℕ} {out : Int} {K : DInterval}
    (h : logPoint z N out = some K) (hz : 0 < z.toReal) : K.mem (Real.log z.toReal) := by
  unfold logPoint at h
  split at h
  · next hpos =>
    have hzm : (0:ℤ) < z.m := by
      by_contra hcon
      push_neg at hcon
      have hle : Dyadic.toReal z ≤ 0 := by
        rw [Dyadic.toReal_def]
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hcon) (by positivity)
      linarith
    have hmpos : (0:ℕ) < z.m.toNat := by
      have := Int.toNat_of_nonneg (le_of_lt hzm)
      omega
    set n : ℕ := Nat.log2 z.m.toNat with hn_def
    have h2n : (2:ℕ)^n ≤ z.m.toNat := by
      rw [hn_def, Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hlt2n : z.m.toNat < (2:ℕ)^(n + 1) := by
      rw [hn_def, Nat.log2_eq_log_two, Nat.pow_succ]
      exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) z.m.toNat
    have hzmeq : ((z.m.toNat : ℕ) : ℝ) = (z.m : ℝ) :=
      by exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hzm))
    have h2n_dup : (2:ℕ)^Nat.log2 z.m.toNat ≤ z.m.toNat := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hlt2n : z.m.toNat < (2:ℕ)^(Nat.log2 z.m.toNat + 1) := by
      rw [Nat.log2_eq_log_two, Nat.pow_succ]
      exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) z.m.toNat
    have hzmeq : ((z.m.toNat : ℕ) : ℝ) = (z.m : ℝ) :=
      by exact_mod_cast (Int.toNat_of_nonneg (le_of_lt hzm))
    cases hl : logInterval ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩ N out with
    | none => rw [hl] at h; simp at h
    | some J =>
      rw [hl] at h
      obtain rfl : K = J.add (iscale log2D ((Nat.log2 z.m.toNat : ℤ) + z.e)) :=
        (Option.some.inj h).symm
      have hutwo : Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩
          = ((z.m : ℤ):ℝ) * (2:ℝ)^(-(Nat.log2 z.m.toNat : ℤ)) := by
        rw [Dyadic.toReal_def]
      have hge : ((2:ℝ)^((↑(Nat.log2 z.m.toNat) : ℤ)):ℝ) ≤ ((z.m:ℤ):ℝ) := by
        rw [show ((2:ℝ)^((↑(Nat.log2 z.m.toNat) : ℤ)):ℝ)
              = (((2:ℕ)^(Nat.log2 z.m.toNat) : ℕ) : ℝ) from by rw [zpow_natCast]; norm_cast,
          ← hzmeq]
        exact_mod_cast h2n
      have hXpos : (0:ℝ) < (2:ℝ)^((↑(Nat.log2 z.m.toNat) : ℤ)) := by positivity
      have hutwo' : Dyadic.toReal ⟨z.m, -(↑(Nat.log2 z.m.toNat) : ℤ)⟩
          = ((z.m:ℤ):ℝ) / (2:ℝ)^((↑(Nat.log2 z.m.toNat) : ℤ)) := by
        rw [Dyadic.toReal_def, div_eq_mul_inv, zpow_neg]
      have hu1 : (1:ℝ) ≤ Dyadic.toReal ⟨z.m, -(↑(Nat.log2 z.m.toNat) : ℤ)⟩ := by
        rw [hutwo', le_div_iff₀ hXpos, one_mul]
        exact hge
      have hu2 : Dyadic.toReal ⟨z.m, -(↑(Nat.log2 z.m.toNat) : ℤ)⟩ < 2 := by
        have hz2 : ((2:ℝ)^((↑(Nat.log2 z.m.toNat) + 1 : ℤ)):ℝ)
            = ((2:ℝ)^((↑(Nat.log2 z.m.toNat) : ℤ)):ℝ) * 2 := by
          rw [zpow_add₀ (show (2:ℝ) ≠ 0 by norm_num)
            ((↑(Nat.log2 z.m.toNat) : ℤ)) (1:ℤ), zpow_one]
        have hlt2 : ((z.m:ℤ):ℝ) < ((2:ℝ)^((↑(Nat.log2 z.m.toNat) + 1 : ℤ)):ℝ) := by
          have he : (((Nat.log2 z.m.toNat : ℤ)) + 1)
              = ((Nat.log2 z.m.toNat + 1 : ℕ) : ℤ) := by
            push_cast; omega
          rw [show ((2:ℝ)^((↑(Nat.log2 z.m.toNat) + 1 : ℤ)):ℝ)
                = (((2:ℕ)^(Nat.log2 z.m.toNat + 1) : ℕ) : ℝ) from by
                rw [he, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat], ← hzmeq]
          exact_mod_cast hlt2n
        rw [hutwo', div_lt_iff₀ hXpos, mul_comm]
        exact hlt2
      have hJ : J.mem (Real.log (Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩)) :=
        logInterval_sound hl
          (show Dyadic.toReal ⟨1, 0⟩ ≤ Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩ from by
            rw [Dyadic.toReal_int]
            exact_mod_cast hu1) (le_of_lt hu2)
      have hS := iscale_mem (I := log2D) (k := (Nat.log2 z.m.toNat : ℤ) + z.e)
        log2D_mem
      have hu_eq : Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩
            * (2:ℝ)^((Nat.log2 z.m.toNat : ℤ) + z.e) = z.toReal := by
        rw [hutwo, mul_assoc]
        have hzpow : (2:ℝ)^(-(Nat.log2 z.m.toNat : ℤ))
              * (2:ℝ)^((Nat.log2 z.m.toNat : ℤ) + z.e) = (2:ℝ)^(z.e) := by
          have hzz2 := zpow_add₀ (show (2:ℝ) ≠ 0 by norm_num)
            (-(Nat.log2 z.m.toNat : ℤ)) ((Nat.log2 z.m.toNat : ℤ) + z.e)
          rw [show (-(Nat.log2 z.m.toNat : ℤ))
                  + ((Nat.log2 z.m.toNat : ℤ) + z.e) = z.e from by omega] at hzz2
          exact hzz2.symm
        rw [hzpow]
        show ((z.m : ℤ):ℝ) * (2:ℝ)^(z.e) = _
        rw [Dyadic.toReal_def]
      have hadd := DInterval.mem_add hJ hS
      have hpos2 : (0:ℝ) < (2:ℝ)^((Nat.log2 z.m.toNat : ℤ) + z.e) := by positivity
      have hupos : (0:ℝ) < Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩ :=
        lt_of_lt_of_le one_pos hu1
      have hsum : Real.log (Dyadic.toReal ⟨z.m, -((Nat.log2 z.m.toNat : ℤ))⟩)
            + (((Nat.log2 z.m.toNat : ℤ) + z.e : ℤ) : ℝ) * Real.log 2
          = Real.log z.toReal := by
        rw [← Real.log_zpow (x := (2:ℝ)) (n := ((Nat.log2 z.m.toNat : ℤ) + z.e : ℤ)),
          ← Real.log_mul (ne_of_gt hupos) (by positivity), ← hu_eq]
      rwa [hsum] at hadd
  · next hn =>
    rw [Dyadic.isPos_iff] at hn
    exact absurd hz hn

set_option exponentiation.threshold 2048 in
example : logInterval ⟨2, 0⟩ 8 (-16)
    = some ⟨⟨1224664839723253066757532368272827966897654092888104932391667849000070544, -240⟩,
            ⟨21041551031267394410589974817095804438051737544098602624748996252542645910946185216, -274⟩⟩ := by
  decide

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
example : logInterval ⟨2, 0⟩ 8 (-16)
    = some ⟨⟨1224664839723253066757532368272827966897654092888104932391667849000070544, -240⟩,
            ⟨21041551031267394410589974817095804438051737544098602624748996252542645910946185216, -274⟩⟩ := by
  decide

/-- Interval-level `log` on `J` with `J.lo.toReal > 0`: `log` is monotone,
so the endpoints' point enclosures bracket all of `{log y : y ∈ J}`. -/
def lnI (J : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  if J.lo.isPos then
    match logPoint J.lo N out, logPoint J.hi N out with
    | some L, some H => some ⟨L.lo, H.hi⟩
    | _, _ => none
  else none

/-- **Soundness of `lnI`**: if the range check succeeds, the result contains
`log y` for every real `y ∈ J`. -/
theorem lnI_sound {J : DInterval} {N : ℕ} {out : Int} {K : DInterval} {y : ℝ}
    (hy : J.mem y) (h : lnI J N out = some K) : K.mem (Real.log y) := by
  obtain ⟨h1, h2⟩ := hy
  unfold lnI at h
  by_cases hchk : J.lo.isPos
  · rw [if_pos hchk] at h
    have hy0 : (0:ℝ) < y := by
      rw [Dyadic.isPos_iff] at hchk
      exact lt_of_lt_of_le hchk h1
    cases hl : logPoint J.lo N out with
    | none => rw [hl] at h; simp at h
    | some L =>
      rw [hl] at h
      cases hh : logPoint J.hi N out with
      | none => rw [hh] at h; simp at h
      | some H =>
        rw [hh] at h
        obtain rfl : K = ⟨L.lo, H.hi⟩ := (Option.some.inj h).symm
        have hlo0 : (0:ℝ) < Dyadic.toReal J.lo := by
          rw [Dyadic.isPos_iff] at hchk
          exact hchk
        have hhi0 : (0:ℝ) < Dyadic.toReal J.hi :=
          lt_of_lt_of_le hy0 h2
        obtain ⟨hl1, _⟩ := logPoint_sound hl hlo0
        obtain ⟨_, hh2⟩ := logPoint_sound hh hhi0
        exact ⟨le_trans hl1 (Real.log_le_log hlo0 h1),
          le_trans (Real.log_le_log hy0 h2) hh2⟩
  · rw [if_neg hchk] at h; simp at h

#eval match lnI ⟨⟨2, 0⟩, ⟨4, 0⟩⟩ 8 (-16) with
  | some I => s!"LO {I.lo.m} {I.lo.e} HI {I.hi.m} {I.hi.e}"
  | none => "none"

#print axioms logInterval_sound
#print axioms log2D_mem
#print axioms iscale_mem
#print axioms logPoint_sound
#print axioms lnI_sound

#print axioms logInterval_sound
#print axioms log2D_mem
#print axioms logPoint_sound
#print axioms lnI_sound

end Kepler.Interval
