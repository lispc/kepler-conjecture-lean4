import Kepler.NliBanks3

/-!
Kepler.NliBanks9 — lane `nli-rest-b1`, reduction kit for the ZTGIJCF4 /
QITNPEA1 template batch (14 banks).

This module contains **no bank proof**.  It formalises the two pieces of the
work-order template that are mathematically sound and reusable:

1. the explicit `lmfun` kink at `y = 2 * h0 = 2.52` (`lmfun (y/2)` has slope
   `-1/0.52` below the kink and `0` above it), so that every kink-crossing
   axis can be split exactly at `2.52`;
2. the finite-candidate reduction: if for every coordinate `i` and every
   box-admissible setting of the other coordinates the slice
   `t ↦ f (update x i t)` admits a candidate `c ∈ cands i` with
   `f (update x i c) ≤ f (update x i (x i))` — in particular when the slice
   is concave on each kink piece, so that `c ∈ {lo, 2.52, hi}` — then the
   minimum of `f` over the box is attained on the product of the `cands`.

The remaining inputs for the 14 banks are therefore isolated as explicit
hypotheses: (a) per-slice piecewise concavity of
`gamma4fgcy/w + m·betaBumpLb − (aSpine5 + bSpine5·dihY)` (resp.
`gamma4fgcy/w − 0.0057`) on each box, and (b) the corner-value bounds at the
refined vertices.  Neither is available in the library; see DELIVERY.md.

No `sorry`/`axiom`/`native_decide`.
-/

set_option maxHeartbeats 1000000

namespace Kepler.NliBanks9
open Kepler.Text

/-! ## 1. The `lmfun` kink at `y = 2 * h0` -/

/-- Below the kink: `lmfun (y/2) = (2h0 − y) / (2(h0 − 1))`. -/
theorem lmfun_div_two_of_le {y : ℝ} (hy : y ≤ 2 * h0) :
    lmfun (y / 2) = (2 * h0 - y) / (2 * (h0 - 1)) := by
  have hle : y / 2 ≤ h0 := by linarith
  rw [lmfun, if_pos hle]
  field_simp

/-- Above the kink: `lmfun (y/2) = 0`. -/
theorem lmfun_div_two_of_gt {y : ℝ} (hy : 2 * h0 < y) : lmfun (y / 2) = 0 := by
  have hle : ¬ y / 2 ≤ h0 := by linarith
  rw [lmfun, if_neg hle]

/-- Kink value, left branch, with literal constants (`2h0 = 2.52`). -/
theorem lmfun_div_two_kink_left {y : ℝ} (hy : y ≤ 2.52) :
    lmfun (y / 2) = (2.52 - y) / 0.52 := by
  have hh : 2 * h0 = 2.52 := by
    rw [show h0 = 1.26 from rfl]; norm_num
  have hh2 : 2 * (h0 - 1) = 0.52 := by
    rw [show h0 = 1.26 from rfl]; norm_num
  rw [lmfun_div_two_of_le (by rw [hh]; exact hy), hh, hh2]

/-- Kink value, right branch, with literal constants (`2h0 = 2.52`). -/
theorem lmfun_div_two_kink_right {y : ℝ} (hy : 2.52 ≤ y) :
    lmfun (y / 2) = 0 := by
  have hh : 2 * h0 = 2.52 := by
    rw [show h0 = 1.26 from rfl]; norm_num
  rcases lt_or_eq_of_le hy with hy' | hy'
  · exact lmfun_div_two_of_gt (by rw [hh]; exact hy')
  · rw [← hy', lmfun_div_two_kink_left le_rfl]
    norm_num

/-! ## 2. One-dimensional concavity ⇒ minimum at an endpoint -/

/-- A concave function on `[lo, hi]` is bounded below by the smaller of its
two endpoint values. -/
theorem concaveOn_min_endpoints {f : ℝ → ℝ} {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hf : ConcaveOn ℝ (Set.Icc lo hi) f) {t : ℝ} (ht : t ∈ Set.Icc lo hi) :
    min (f lo) (f hi) ≤ f t := by
  rcases eq_or_lt_of_le hlohi with h | h
  · have htlo : t = lo := le_antisymm (by simpa [← h] using ht.2) (by simpa [h] using ht.1)
    simp [htlo]
  · have hden : (0:ℝ) < hi - lo := by linarith
    set a : ℝ := (hi - t) / (hi - lo) with ha_def
    set b : ℝ := (t - lo) / (hi - lo) with hb_def
    have ha : 0 ≤ a := by
      rw [ha_def]; exact div_nonneg (by linarith [ht.2]) (le_of_lt hden)
    have hb : 0 ≤ b := by
      rw [hb_def]; exact div_nonneg (by linarith [ht.1]) (le_of_lt hden)
    have hab : a + b = 1 := by
      rw [ha_def, hb_def]
      field_simp
      ring
    have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
    have hhi_mem : hi ∈ Set.Icc lo hi := ⟨hlohi, le_rfl⟩
    have hconv : a • lo + b • hi = t := by
      rw [ha_def, hb_def]
      simp only [smul_eq_mul]
      field_simp
      ring
    simp only [smul_eq_mul] at hconv
    have hconc := hf.2 hlo_mem hhi_mem ha hb hab
    simp only [smul_eq_mul] at hconc
    rw [hconv] at hconc
    have hmin : min (f lo) (f hi) ≤ a * f lo + b * f hi := by
      have h1 : a * min (f lo) (f hi) ≤ a * f lo :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) ha
      have h2 : b * min (f lo) (f hi) ≤ b * f hi :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hb
      have h3 : a * min (f lo) (f hi) + b * min (f lo) (f hi) ≤
          a * f lo + b * f hi := add_le_add h1 h2
      have h4 : a * min (f lo) (f hi) + b * min (f lo) (f hi) =
          min (f lo) (f hi) := by
        rw [← add_mul, hab, one_mul]
      linarith
    linarith

/-- Piecewise-concave slice with a kink at `k`: the minimum over `[lo, hi]`
is at one of `lo`, `k`, `hi`. -/
theorem min_of_piecewise_concave {f : ℝ → ℝ} {lo k hi : ℝ}
    (hlk : lo ≤ k) (hkh : k ≤ hi)
    (hl : ConcaveOn ℝ (Set.Icc lo k) f) (hr : ConcaveOn ℝ (Set.Icc k hi) f)
    {t : ℝ} (ht : t ∈ Set.Icc lo hi) :
    min (f lo) (min (f k) (f hi)) ≤ f t := by
  by_cases htk : t ≤ k
  · have ht' : t ∈ Set.Icc lo k := ⟨ht.1, htk⟩
    have hle := concaveOn_min_endpoints hlk hl ht'
    have hmm : min (f lo) (min (f k) (f hi)) ≤ min (f lo) (f k) :=
      min_le_min le_rfl (min_le_left _ _)
    linarith
  · have htk' : k ≤ t := le_of_lt (not_le.mp htk)
    have ht' : t ∈ Set.Icc k hi := ⟨htk', ht.2⟩
    have hle := concaveOn_min_endpoints hkh hr ht'
    have hmm : min (f lo) (min (f k) (f hi)) ≤ min (f k) (f hi) :=
      min_le_right _ _
    linarith

/-! ## 3. Finite-candidate (corner) reduction in `n` dimensions

`boxInf cands f` is the infimum of `f` over the product of the candidate
sets.  The work-order template uses `cands i = {lo i, 2.52, hi i}` on every
kink-crossing axis (`{lo i, hi i}` otherwise). -/

/-- Infimum of `f` over the product of the per-coordinate candidate sets
(encoded as a `Finset.pi` of dependent selections). -/
noncomputable def boxInf {n : ℕ} (cands : Fin n → Finset ℝ)
    (hne : ∀ i, (cands i).Nonempty) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (Finset.univ.pi cands).inf'
    (by
      rw [Finset.pi_nonempty]
      intro i _
      exact hne i)
    (fun s => f (fun i => s i (Finset.mem_univ i)))

/-- Core reduction: if every slice `i` admits a candidate that does not
increase `f` (for every box-admissible setting of the other coordinates),
then the infimum over the candidate product is a lower bound for `f` on the
box.  The candidate sets must lie in the corresponding axis intervals. -/
theorem boxInf_le_of_slice_min {n : ℕ} (lo hi : Fin n → ℝ)
    (cands : Fin n → Finset ℝ) (hne : ∀ i, (cands i).Nonempty)
    (hsub : ∀ i, ∀ c ∈ cands i, c ∈ Set.Icc (lo i) (hi i))
    {f : (Fin n → ℝ) → ℝ}
    (hstep : ∀ (i : Fin n) (x : Fin n → ℝ),
      (∀ j, x j ∈ Set.Icc (lo j) (hi j)) →
      ∃ c ∈ cands i, f (Function.update x i c) ≤ f x)
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    boxInf cands hne f ≤ f x := by
  classical
  -- Invariant on a set `S` of already-reduced coordinates: a point agreeing
  -- with `x` off `S`, candidate-valued on `S`, still inside the box, and no
  -- larger than `x`.
  have key : ∀ S : Finset (Fin n), ∃ y : Fin n → ℝ,
      (∀ i ∈ S, y i ∈ cands i) ∧ (∀ i, i ∉ S → y i = x i) ∧
        (∀ i, y i ∈ Set.Icc (lo i) (hi i)) ∧ f y ≤ f x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨x, by simp, by simp, hx, le_rfl⟩
    | insert i S hi ih =>
        obtain ⟨y, hyS, hyout, hybox, hyf⟩ := ih
        obtain ⟨c, hc, hle⟩ := hstep i y hybox
        refine ⟨Function.update y i c, ?_, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]; exact hc
          · have hjS : j ∈ S := by
              rcases Finset.mem_insert.mp hj with h | h
              · exact absurd h hji
              · exact h
            rw [Function.update_apply, if_neg hji]
            exact hyS j hjS
        · intro j hj
          have hji : j ≠ i := by
            intro h; exact hj (by simp [h])
          have hjS : j ∉ S := by
            intro h; exact hj (by simp [h])
          rw [Function.update_apply, if_neg hji]
          exact hyout j hjS
        · intro j
          by_cases hji : j = i
          · rw [hji, Function.update_self]
            exact hsub i c hc
          · rw [Function.update_apply, if_neg hji]
            exact hybox j
        · calc f (Function.update y i c) ≤ f y := hle
            _ ≤ f x := hyf
  obtain ⟨y, hy, -, -, hyf⟩ := key Finset.univ
  let s0 : (a : Fin n) → a ∈ (Finset.univ : Finset (Fin n)) → ℝ := fun i _ => y i
  have hmem : s0 ∈ Finset.univ.pi cands := by
    rw [Finset.mem_pi]
    intro i _
    exact hy i (Finset.mem_univ i)
  have hle := Finset.inf'_le
    (s := Finset.univ.pi cands)
    (fun s => f (fun i => s i (Finset.mem_univ i))) hmem
  have hy_eq : (fun i => s0 i (Finset.mem_univ i)) = y := by
    funext i
    rfl
  rw [hy_eq] at hle
  unfold boxInf
  exact le_trans hle hyf

/-- Kink-specialised form: with candidate sets `{lo, k, hi}`, per-slice
piecewise concavity at the kink `k` supplies the `boxInf_le_of_slice_min`
hypothesis.  This is the exact shape the 14 banks need with `k = 2.52`. -/
theorem boxInf_le_of_piecewise_concave {n : ℕ} (lo hi : Fin n → ℝ)
    (k : Fin n → ℝ) (hlk : ∀ i, lo i ≤ k i) (hkh : ∀ i, k i ≤ hi i)
    (f : (Fin n → ℝ) → ℝ)
    (hconc : ∀ (i : Fin n) (x : Fin n → ℝ),
      ConcaveOn ℝ (Set.Icc (lo i) (k i)) (fun t => f (Function.update x i t)) ∧
      ConcaveOn ℝ (Set.Icc (k i) (hi i)) (fun t => f (Function.update x i t)))
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    boxInf (fun i => {lo i, k i, hi i}) (fun i => ⟨lo i, by simp⟩) f ≤ f x := by
  classical
  refine boxInf_le_of_slice_min lo hi (fun i => {lo i, k i, hi i})
    (fun i => ⟨lo i, by simp⟩) ?_ ?_ hx
  · intro i c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨le_rfl, le_trans (hlk i) (hkh i)⟩
    · exact ⟨hlk i, hkh i⟩
    · exact ⟨le_trans (hlk i) (hkh i), le_rfl⟩
  · intro i y' hybox
    have hpair := hconc i y'
    have ht : y' i ∈ Set.Icc (lo i) (hi i) := hybox i
    have h1 := min_of_piecewise_concave (hlk i) (hkh i) hpair.1 hpair.2 ht
    have ht_update : Function.update y' i (y' i) = y' := Function.update_eq_self i y'
    rw [ht_update] at h1
    -- the min of the three candidate values is one of them
    rcases min_cases (f (Function.update y' i (lo i)))
        (min (f (Function.update y' i (k i))) (f (Function.update y' i (hi i)))) with hA | hA
    · refine ⟨lo i, by simp, ?_⟩
      rw [hA.1] at h1
      exact h1
    · rcases min_cases (f (Function.update y' i (k i)))
          (f (Function.update y' i (hi i))) with hB | hB
      · refine ⟨k i, by simp, ?_⟩
        rw [hA.1, hB.1] at h1
        exact h1
      · refine ⟨hi i, by simp, ?_⟩
        rw [hA.1, hB.1] at h1
        exact h1

end Kepler.NliBanks9

#print axioms Kepler.NliBanks9.lmfun_div_two_kink_left
#print axioms Kepler.NliBanks9.concaveOn_min_endpoints
#print axioms Kepler.NliBanks9.min_of_piecewise_concave
#print axioms Kepler.NliBanks9.boxInf_le_of_slice_min
#print axioms Kepler.NliBanks9.boxInf_le_of_piecewise_concave
