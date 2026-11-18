/-
Ox3q1hChainSplitKit: split-grid step bridges for the 19 KREBATE-INFEASIBLE
conjuncts of ox3q1hP25 (lane `ox3q1h-s3-fresh-w1`, S4.5).

NOGATE §5 "k ≤ −K variant": for a coordinate axis split into `M` equal
pieces of width `w`, per-PIECE shifted-concavity certificates
(`f − K/2·t²` concave on each `[lo + k·w, lo + (k+1)·w]`) yield the
∃-step over ANY candidate set containing the grid points, with per-step
rebate `K·w²/8` (vs the unsplit `K·W²/8`) — the equal-split reading of
`K·(W/m)²/8` per SPLIT_PLAN's `m`.

`hstep_split_m` is generic in `M` (induction: prefix descent via the
m-piece IH, or the last piece via the chord rebate) and generic in the
candidate set `S` (only `grid k ∈ S` is required), so one lemma serves
every row/coordinate with `m ∈ {2,3,4,5}` (and the degenerate `m = 1`
whole-interval shape).  `cands_split_sub_aux` shows every grid point of
an m-split coordinate lies in the box.

No numeric data; no `sorry`/`axiom`/`native_decide`.
-/
import Mathlib
import Kepler.Text.Ox3q1hSliceRebate

open Set Filter Topology

namespace Kepler.Text

/-- Every grid point `lo + k·w` of an `m`-split coordinate lies in the
axis interval `[lo, hi]` (`hi = lo + m·w`). -/
theorem cands_split_sub_aux {lo hi w : ℝ} {m : ℕ} (hw : 0 ≤ w) (hm : 0 < m)
    (hmw : hi = lo + (m : ℝ) * w) (k : ℕ) (hk : k ≤ m) :
    lo + (k : ℝ) * w ∈ Set.Icc lo hi := by
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hp : 0 ≤ (k : ℝ) * w := mul_nonneg hk0 hw
  have hmul : (k : ℝ) * w ≤ (m : ℝ) * w := mul_le_mul_of_nonneg_right hkm hw
  constructor
  · linarith [hp]
  · linarith [hmul, hmw]

/-- Split-grid step (the `k ≤ −K` variant, equal pieces): if
`f − K/2·t²` is concave on every piece `[lo + k·w, lo + (k+1)·w]`
(`k + 1 ≤ M`) and the candidate set `S` contains all `M + 1` grid
points of `lo + M·w`, then from any `y i` in `[lo, lo + M·w]` some
candidate `c` moves the `i`-slice by at most the per-piece rebate
`K·w²/8`. -/
theorem hstep_split_m {n : ℕ} {f : (Fin n → ℝ) → ℝ} (i : Fin n) {lo w : ℝ} {K : ℝ}
    {S : Finset ℝ} (M : ℕ) (hM : 1 ≤ M)
    (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hsl : ∀ (k : ℕ) (hk : k + 1 ≤ M) (y : Fin n → ℝ),
      ConcaveOn ℝ (Set.Icc (lo + (k : ℝ) * w) (lo + ((k + 1 : ℕ) : ℝ) * w))
        (fun t => f (Function.update y i t) - K / 2 * t * t))
    (hmem : ∀ (k : ℕ), k ≤ M → (lo + (k : ℝ) * w) ∈ S)
    (y : Fin n → ℝ) (hy : y i ∈ Set.Icc lo (lo + (M : ℝ) * w)) :
    ∃ c ∈ S, f (Function.update y i c) ≤ f y + K * w ^ 2 / 8 := by
  induction M with
  | zero => exact absurd hM (Nat.not_succ_le_zero 0)
  | succ m ih =>
    by_cases hlast : y i ≤ lo + (m : ℝ) * w
    · -- prefix: m pieces (or the degenerate single point when m = 0)
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have hy0 : y i = lo := le_antisymm (by simpa using hlast) hy.1
        have hc : (lo : ℝ) ∈ S := by simpa using hmem 0 (by omega)
        refine ⟨lo, hc, ?_⟩
        have hupf : Function.update y i lo = y := by
          rw [← hy0]
          funext a
          by_cases ha : a = i
          · subst ha
            simp [Function.update_self]
          · rw [Function.update_of_ne ha]
        have hp : 0 ≤ K * w ^ 2 / 8 :=
          div_nonneg (mul_nonneg hK (sq_nonneg w)) (by norm_num)
        rw [hupf]
        linarith [hp]
      · have hmemm : ∀ (k : ℕ), k ≤ m → (lo + (k : ℝ) * w) ∈ S :=
          fun k hk => hmem k (le_trans hk (Nat.le_succ m))
        have hslm : ∀ (k : ℕ) (hk : k + 1 ≤ m) (z : Fin n → ℝ),
            ConcaveOn ℝ (Set.Icc (lo + (k : ℝ) * w) (lo + ((k + 1 : ℕ) : ℝ) * w))
              (fun t => f (Function.update z i t) - K / 2 * t * t) :=
          fun k hk z => hsl k (le_trans hk (Nat.le_succ m)) z
        refine ih (by omega) hslm hmemm ⟨hy.1, hlast⟩
    · -- last piece [lo + m·w, lo + (m+1)·w] (works for all m ≥ 0)
      have hlt : lo + (m : ℝ) * w < y i := not_le.mp hlast
      have hmem_y : y i ∈ Set.Icc (lo + (m : ℝ) * w) (lo + ((m + 1 : ℕ) : ℝ) * w) :=
        ⟨le_of_lt hlt, hy.2⟩
      have hkm : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
      have hab : lo + (m : ℝ) * w ≤ lo + ((m + 1 : ℕ) : ℝ) * w := by
        linarith [add_le_add_left (mul_le_mul_of_nonneg_right hkm hw) lo]
      have hwid : (lo + ((m + 1 : ℕ) : ℝ) * w) - (lo + (m : ℝ) * w) = w := by
        rw [Nat.cast_add_one]
        ring
      have hg : ConcaveOn ℝ (Set.Icc (lo + (m : ℝ) * w) (lo + ((m + 1 : ℕ) : ℝ) * w))
          (fun t => f (Function.update y i t) - K / 2 * t * t) :=
        hsl m (by omega) y
      have hp : 0 ≤ K * w ^ 2 / 8 :=
        div_nonneg (mul_nonneg hK (sq_nonneg w)) (by norm_num)
      have hupeq : Function.update y i (y i) = y := by
        funext a
        by_cases ha : a = i
        · subst ha
          simp [Function.update_self]
        · rw [Function.update_of_ne ha]
      have hpp := rebate_of_concave_shifted hab hK hg (t := y i) hmem_y
      rw [hupeq] at hpp
      rw [hwid] at hpp
      have hmin : min (f (Function.update y i (lo + (m : ℝ) * w)))
          (f (Function.update y i (lo + ((m + 1 : ℕ) : ℝ) * w))) ≤ f y + K * w ^ 2 / 8 := by
        linarith [hpp, hp]
      rcases min_le_iff.mp hmin with hc | hc
      · exact ⟨lo + (m : ℝ) * w, hmem m (Nat.le_succ m), hc⟩
      · exact ⟨lo + ((m + 1 : ℕ) : ℝ) * w, hmem (m + 1) (le_refl _), hc⟩

/-- Split-grid step from a BOXED piecewise shifted-concavity hypothesis
(SF 111 supply-slot form): `hsl` is only demanded at points whose every
coordinate lies in `[blo j, bhi j]`, and the induction only ever consumes it
at its fixed point `y` (the same `y` at every recursion level). Same proof
as `hstep_split_m` with `hybox` threaded to the single hsl applications. -/
theorem hstep_split_m_box {n : ℕ} {f : (Fin n → ℝ) → ℝ} {blo bhi : Fin n → ℝ}
    (i : Fin n) {lo w : ℝ} {K : ℝ} {S : Finset ℝ} (M : ℕ) (hM : 1 ≤ M)
    (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hsl : ∀ (k : ℕ), k + 1 ≤ M → ∀ (y : Fin n → ℝ),
      (∀ j, y j ∈ Set.Icc (blo j) (bhi j)) →
      ConcaveOn ℝ (Set.Icc (lo + (k : ℝ) * w) (lo + ((k + 1 : ℕ) : ℝ) * w))
        (fun t => f (Function.update y i t) - K / 2 * t * t))
    (hmem : ∀ (k : ℕ), k ≤ M → (lo + (k : ℝ) * w) ∈ S)
    (y : Fin n → ℝ) (hybox : ∀ j, y j ∈ Set.Icc (blo j) (bhi j))
    (hy : y i ∈ Set.Icc lo (lo + (M : ℝ) * w)) :
    ∃ c ∈ S, f (Function.update y i c) ≤ f y + K * w ^ 2 / 8 := by
  induction M with
  | zero => exact absurd hM (Nat.not_succ_le_zero 0)
  | succ m ih =>
    by_cases hlast : y i ≤ lo + (m : ℝ) * w
    · rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have hy0 : y i = lo := le_antisymm (by simpa using hlast) hy.1
        have hc : (lo : ℝ) ∈ S := by simpa using hmem 0 (by omega)
        refine ⟨lo, hc, ?_⟩
        have hupf : Function.update y i lo = y := by
          rw [← hy0]
          funext a
          by_cases ha : a = i
          · subst ha
            simp [Function.update_self]
          · rw [Function.update_of_ne ha]
        have hp : 0 ≤ K * w ^ 2 / 8 :=
          div_nonneg (mul_nonneg hK (sq_nonneg w)) (by norm_num)
        rw [hupf]
        linarith [hp]
      · have hmemm : ∀ (k : ℕ), k ≤ m → (lo + (k : ℝ) * w) ∈ S :=
          fun k hk => hmem k (le_trans hk (Nat.le_succ m))
        have hslm : ∀ (k : ℕ), k + 1 ≤ m → ∀ (z : Fin n → ℝ),
            (∀ j, z j ∈ Set.Icc (blo j) (bhi j)) →
            ConcaveOn ℝ (Set.Icc (lo + (k : ℝ) * w) (lo + ((k + 1 : ℕ) : ℝ) * w))
              (fun t => f (Function.update z i t) - K / 2 * t * t) :=
          fun k hk z hz => hsl k (le_trans hk (Nat.le_succ m)) z hz
        exact ih (by omega) hslm hmemm ⟨hy.1, hlast⟩
    · have hlt : lo + (m : ℝ) * w < y i := not_le.mp hlast
      have hmem_y : y i ∈ Set.Icc (lo + (m : ℝ) * w) (lo + ((m + 1 : ℕ) : ℝ) * w) :=
        ⟨le_of_lt hlt, hy.2⟩
      have hkm : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
      have hab : lo + (m : ℝ) * w ≤ lo + ((m + 1 : ℕ) : ℝ) * w := by
        linarith [add_le_add_left (mul_le_mul_of_nonneg_right hkm hw) lo]
      have hwid : (lo + ((m + 1 : ℕ) : ℝ) * w) - (lo + (m : ℝ) * w) = w := by
        rw [Nat.cast_add_one]
        ring
      have hg : ConcaveOn ℝ (Set.Icc (lo + (m : ℝ) * w) (lo + ((m + 1 : ℕ) : ℝ) * w))
          (fun t => f (Function.update y i t) - K / 2 * t * t) :=
        hsl m (by omega) y hybox
      have hp : 0 ≤ K * w ^ 2 / 8 :=
        div_nonneg (mul_nonneg hK (sq_nonneg w)) (by norm_num)
      have hupeq : Function.update y i (y i) = y := by
        funext a
        by_cases ha : a = i
        · subst ha
          simp [Function.update_self]
        · rw [Function.update_of_ne ha]
      have hpp := rebate_of_concave_shifted hab hK hg (t := y i) hmem_y
      rw [hupeq] at hpp
      rw [hwid] at hpp
      have hmin : min (f (Function.update y i (lo + (m : ℝ) * w)))
          (f (Function.update y i (lo + ((m + 1 : ℕ) : ℝ) * w))) ≤ f y + K * w ^ 2 / 8 := by
        linarith [hpp, hp]
      rcases min_le_iff.mp hmin with hc | hc
      · exact ⟨lo + (m : ℝ) * w, hmem m (Nat.le_succ m), hc⟩
      · exact ⟨lo + ((m + 1 : ℕ) : ℝ) * w, hmem (m + 1) (le_refl _), hc⟩

/-! ### Axiom audit -/

#print axioms cands_split_sub_aux
#print axioms hstep_split_m
#print axioms hstep_split_m_box

end Kepler.Text
