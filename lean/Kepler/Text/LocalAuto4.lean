/-
Port of the HOL Light Flyspeck file `scripts/local/dih2k.hl`
(module `Dih2k_hypermap`, Local Fan chapter, Hoang Le Truong 2010;
15 definitions + 95 theorems: the `ball_annulus` / `dih2k` kit).

Encoding (HOL → Lean):
- HOL `real^N^M` (m×n real matrix, 1-based `row i v`) ↦
  `FinMat m n = Fin m → Fin n → ℝ` (0-based; `row i v` ↦ `v i`).
- HOL `(A,B)finite_product` with `dimindex = dimindex(:A) * dimindex(:B)`
  ↦ `FinVec m n = Fin (m * n) → ℝ` (no new type needed;
  `finite_product_tybij` ↦ `finProdEquiv` below).
- `matvec`/`vecmat`/`vecmats` are the 0-based analogues of the HOL
  1-based `DIV`/`MOD` flattening; the tybij laws
  `VECMATS_MATVEC_ID`/`MATVEC_VECMATS_ID` hold by plain arithmetic.
- HOL `norm`/`dot` (Euclidean) ↦ `nrm`/`dotp` below (Mathlib's Pi norm
  on `Fin k → ℝ` is the sup norm, so explicit Euclidean defs are used).
- HOL `real^3` ↦ `V3` (Kepler.Geom); rows of `real^3^M` ↦ `Fin m → V3`.
  `ball_annulus` ↦ `ballAnnulus`, `h0`/`sol0` ↦ `h0`/`Fan.sol0`.
- HOL `angle a b c = acs((a-b)·(c-b)/(|a-b||c-b|))` ↦ `angle_p4`.
- External Flyspeck defs used by the hypermap section but not yet ported
  get private `_p4` copies with `NEEDS` markers (merge note: replace by
  imports once owned; precedent Kepler/Text/PackingAuto4.lean).
  `_p4` copies: `azimCycle_p4`, `ivsAzimCycle_p4`, `EE_p4`, `ordPairs_p4`,
  `selfPairs_p4`, `dartsOfHyp_p4`, `eeOfHyp_p4`, `nnOfHyp_p4`,
  `ffOfHyp_p4`, `hyp_p4`, `face_p4`, `hasOrders_p4`, `dih2k_p4`,
  `localFan_p4`, `convexLocalFan_p4`, `azimInFan_p4`, `wedgeGe_p4`,
  `wedgeInFanGe_p4`.
- Section F (hypermap of the fan) statements are ported verbatim; their
  proofs are `sorry` (giants), except a few mechanical ones.
- FILL LEDGER (proof-fill worker, this wave): the two sorried `_p4`
  definitions were discharged (48 -> 46 sorries; the 46 remaining are the
  5 ball-annulus geometry giants and the 41 Section-F SY hypermap giants,
  none of which has a proved blocker in the current tree).
  Filled: azimCycle_p4 (verbatim body copy of LocalAuto3.azimCycle_p3 —
  needs `projection`, hence the new `import Kepler.Text.PackingAuto5`);
  hyp_p4 (dite on `FAN x V E`: `hypermapOfFan` (Fan.lean) under the fan,
  a junk empty-dart hypermap otherwise — every downstream Section-F
  statement carries the FAN hypothesis and only constrains edge darts, on
  which `hypermapOfFan`'s maps agree with the `_p4` of-hyp maps).
-/

import Kepler.Text.Polytope
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.Fan
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical
open Kepler.Text.Fan
open scoped Matrix

/-! ## Finite-product encoding: tybij and index arithmetic -/

/-- HOL `real^N^M`: an `m × n` real matrix; row `i` is `v i : Fin n → ℝ`. -/
abbrev FinMat (m n : ℕ) : Type := Fin m → Fin n → ℝ

/-- HOL `(M,N)finite_product`: the flattening of `FinMat m n`. -/
abbrev FinVec (m n : ℕ) : Type := Fin (m * n) → ℝ

theorem divMod_lt_mul {m n i : ℕ} (hi : i < m * n) : i / n < m ∧ i % n < n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp at hi
  · refine ⟨?_, Nat.mod_lt i hn⟩
    by_contra hge
    push_neg at hge
    have h1 : n * (i / n) ≤ i := by
      have := Nat.div_mul_le_self i n
      calc n * (i / n) = (i / n) * n := Nat.mul_comm _ _
        _ ≤ i := this
    exact absurd hi (by nlinarith)

theorem mul_add_lt_mul {m n j k : ℕ} (hn : 0 < n) (hj : j < m) (hk : k < n) :
    j * n + k < m * n := by
  have h1 : j * n + k < j * n + n := by linarith
  have h2 : j * n + n = (j + 1) * n := by ring
  have h3 : (j + 1) * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
  omega

/-- `finite_product_tybij`: `Fin m × Fin n ≃ Fin (m * n)` (HOL 1-based
`DIV`/`MOD` flattening becomes the 0-based `j * n + k`). -/
def finProdEquiv (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := ⟨p.1 * n + p.2, by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact absurd p.2.isLt (Nat.not_lt_zero _)
    · exact mul_add_lt_mul hn p.1.isLt p.2.isLt⟩
  invFun i := ⟨⟨i / n, (divMod_lt_mul i.isLt).1⟩, ⟨i % n, (divMod_lt_mul i.isLt).2⟩⟩
  left_inv p := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact False.elim (absurd p.2.isLt (Nat.not_lt_zero _))
    · have h1 : (p.1 * n + p.2) / n = p.1 := by
        have he : p.1 * n + p.2 = p.2 + n * p.1 := by ring
        rw [he, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
      have h2 : (p.1 * n + p.2) % n = p.2 := by
        have he : p.1 * n + p.2 = p.2 + n * p.1 := by ring
        rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.2.isLt]
      exact Prod.ext (Fin.val_injective h1) (Fin.val_injective h2)
  right_inv i := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact False.elim
        (absurd (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_zero m)) (Nat.not_lt_zero _))
    · refine Fin.val_injective ?_
      have hdm := (i : ℕ).div_add_mod n
      show (i / n) * n + i % n = (i : ℕ)
      rw [Nat.mul_comm]
      exact hdm

/-- Bridge sum: a sum over `Fin (m * n)` splits into an `m × n` double sum. -/
theorem sum_finProdEquiv {m n : ℕ} (g : Fin (m * n) → ℝ) :
    ∑ i, g i = ∑ j, ∑ k, g (finProdEquiv m n ⟨j, k⟩) := by
  have h := Fintype.sum_equiv (finProdEquiv m n)
    (fun p => g (finProdEquiv m n p)) (fun i => g i) fun _ => rfl
  exact h.symm.trans (Fintype.sum_prod_type fun p => g (finProdEquiv m n p))

/-! ## matvec / vecmat / vecmats (dih2k.hl:107-121) -/

/-- HOL `matvec` (dih2k.hl:107), 0-based analogue. -/
def matvec_p4 {m n : ℕ} (v : FinMat m n) : FinVec m n :=
  fun i => v ⟨i / n, (divMod_lt_mul i.isLt).1⟩ ⟨i % n, (divMod_lt_mul i.isLt).2⟩

/-- HOL `vecmat` (dih2k.hl:113), 0-based analogue. -/
def vecmat_p4 {m n : ℕ} (j : Fin m) (f : FinVec m n) : Fin n → ℝ :=
  fun k => f (finProdEquiv m n ⟨j, k⟩)

/-- HOL `vecmats` (dih2k.hl:117), 0-based analogue. -/
def vecmats_p4 {m n : ℕ} (f : FinVec m n) : FinMat m n :=
  fun j k => f (finProdEquiv m n ⟨j, k⟩)
/-- The index of `(j, k)` in the flattening (HOL `j * dimindex(:N) + i'`). -/
theorem finProdEquiv_val {m n : ℕ} (j : Fin m) (k : Fin n) :
    (finProdEquiv m n ⟨j, k⟩ : ℕ) = j * n + k := rfl

/-- HOL `INDEX_VECMAT` (dih2k.hl:148): the flattened index is in range. -/
theorem INDEX_VECMAT {m n : ℕ} (j : Fin m) (k : Fin n) : j * n + k < m * n := by
  rw [← finProdEquiv_val j k]
  exact (finProdEquiv m n ⟨j, k⟩).isLt

theorem div_mod_row {m n : ℕ} (hn : 0 < n) (j k : ℕ) (hj : j < m) (hk : k < n) :
    (j * n + k) / n = j ∧ (j * n + k) % n = k := by
  have he : j * n + k = k + n * j := by ring
  refine ⟨?_, ?_⟩
  · rw [he, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hk, Nat.zero_add]
  · rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

/-- HOL `VECMAT_ROW` (dih2k.hl:160): rows of the flattening. -/
theorem VECMAT_ROW {m n : ℕ} (v : FinMat m n) (j : Fin m) :
    vecmat_p4 j (matvec_p4 v) = v j := by
  funext k
  have hn : 0 < n := by have := k.isLt; omega
  obtain ⟨d1, d2⟩ := div_mod_row hn j k j.isLt k.isLt
  have A : (⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) / n,
      (divMod_lt_mul (finProdEquiv m n ⟨j, k⟩).isLt).1⟩ : Fin m) = j :=
    Fin.val_injective (by
      show (finProdEquiv m n ⟨j, k⟩ : ℕ) / n = j
      rw [finProdEquiv_val]
      exact d1)
  have B : (⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) % n,
      (divMod_lt_mul (finProdEquiv m n ⟨j, k⟩).isLt).2⟩ : Fin n) = k :=
    Fin.val_injective (by
      show (finProdEquiv m n ⟨j, k⟩ : ℕ) % n = k
      rw [finProdEquiv_val]
      exact d2)
  show v ⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) / n, _⟩ ⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) % n, _⟩ = v j k
  rw [A, B]

/-- HOL `VECMATS_MATVEC_ID` (dih2k.hl:187). -/
theorem VECMATS_MATVEC_ID {m n : ℕ} (v : FinMat m n) : vecmats_p4 (matvec_p4 v) = v := by
  funext j k
  have hn : 0 < n := by have := k.isLt; omega
  obtain ⟨d1, d2⟩ := div_mod_row hn j k j.isLt k.isLt
  have A : (⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) / n,
      (divMod_lt_mul (finProdEquiv m n ⟨j, k⟩).isLt).1⟩ : Fin m) = j :=
    Fin.val_injective (by
      show (finProdEquiv m n ⟨j, k⟩ : ℕ) / n = j
      rw [finProdEquiv_val]
      exact d1)
  have B : (⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) % n,
      (divMod_lt_mul (finProdEquiv m n ⟨j, k⟩).isLt).2⟩ : Fin n) = k :=
    Fin.val_injective (by
      show (finProdEquiv m n ⟨j, k⟩ : ℕ) % n = k
      rw [finProdEquiv_val]
      exact d2)
  show v ⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) / n, _⟩ ⟨(finProdEquiv m n ⟨j, k⟩ : ℕ) % n, _⟩ = v j k
  rw [A, B]

/-- HOL `MATVEC_VECMATS_ID` (dih2k.hl:204). -/
theorem MATVEC_VECMATS_ID {m n : ℕ} (f : FinVec m n) : matvec_p4 (vecmats_p4 f) = f := by
  funext i
  show f (finProdEquiv m n ⟨⟨i / n, (divMod_lt_mul i.isLt).1⟩,
    ⟨i % n, (divMod_lt_mul i.isLt).2⟩⟩) = f i
  have h : (finProdEquiv m n ⟨⟨i / n, (divMod_lt_mul i.isLt).1⟩,
      ⟨i % n, (divMod_lt_mul i.isLt).2⟩⟩) = i :=
    Fin.val_injective (by
      show (i / n) * n + i % n = i
      rw [Nat.mul_comm]
      exact (i : ℕ).div_add_mod n)
  rw [h]

/-- HOL `LINEAR_VECMAT` (dih2k.hl:253): `linear (vecmat i)` in HOL's sense. -/
theorem LINEAR_VECMAT {m n : ℕ} (j : Fin m) (x y : FinVec m n) (c : ℝ) :
    vecmat_p4 j (x + y) = vecmat_p4 j x + vecmat_p4 j y ∧
      vecmat_p4 j (c • x) = c • vecmat_p4 j x :=
  ⟨funext fun _ => rfl, funext fun _ => rfl⟩

/-- HOL `VECMAT_VEC` (dih2k.hl:258): constant rows pull back to constants. -/
theorem VECMAT_VEC {m n : ℕ} (j : Fin m) (c : ℝ) :
    vecmat_p4 j (fun _ : Fin (m * n) => c) = (fun _ : Fin n => c) := funext fun _ => rfl

/-- HOL `VECMAT_ADD` (dih2k.hl:265). -/
theorem VECMAT_ADD {m n : ℕ} (j : Fin m) (x y : FinVec m n) :
    vecmat_p4 j (x + y) = vecmat_p4 j x + vecmat_p4 j y := funext fun _ => rfl

/-- HOL `VECMAT_CMUL` (dih2k.hl:270). -/
theorem VECMAT_CMUL {m n : ℕ} (j : Fin m) (c : ℝ) (x : FinVec m n) :
    vecmat_p4 j (c • x) = c • vecmat_p4 j x := funext fun _ => rfl

/-- HOL `VECMAT_NEG` (dih2k.hl:274). -/
theorem VECMAT_NEG {m n : ℕ} (j : Fin m) (x : FinVec m n) :
    -(vecmat_p4 j x) = vecmat_p4 j (-x) := by
  have h : (-x : FinVec m n) = (-1 : ℝ) • x := by funext k; simp
  rw [h, VECMAT_CMUL]; simp

/-- HOL `VECMAT_SUB` (dih2k.hl:279). -/
theorem VECMAT_SUB {m n : ℕ} (j : Fin m) (x y : FinVec m n) :
    vecmat_p4 j (x - y) = vecmat_p4 j x - vecmat_p4 j y := by
  have h : (-y : FinVec m n) = (-1 : ℝ) • y := by funext k; simp
  show vecmat_p4 j (x - y) = vecmat_p4 j x + vecmat_p4 j (-y)
  rw [h, VECMAT_CMUL]
  funext k; simp [vecmat_p4, sub_eq_add_neg]

/-- HOL `MATVEC_SUB` (dih2k.hl:284). -/
theorem MATVEC_SUB {m n : ℕ} (x y : FinMat m n) :
    matvec_p4 x - matvec_p4 y = matvec_p4 (x - y) := funext fun _ => rfl

/-! ## Euclidean norm/dot on function rows and the flattening -/

/-- HOL `norm` on `real^k` (Euclidean; Mathlib's Pi norm is the sup norm). -/
noncomputable def nrm_p4 {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- HOL `dot` on `real^k`. -/
noncomputable def dotp_p4 {k : ℕ} (x y : Fin k → ℝ) : ℝ := ∑ i, x i * y i

theorem sqrt_add_le_sqrt_add_p4 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), ?_⟩
  rw [add_sq]
  have e1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have e2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have h1 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  rw [e1, e2]
  linarith

theorem sqrt_sum_le_sum_sqrt_p4 {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (s : Finset ι) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (sqrt_add_le_sqrt_add_p4 (f a) (∑ i ∈ s, f i) (hf a)
      (Finset.sum_nonneg fun i _ => hf i)) ?_
    exact add_le_add_right ih _

theorem dist_coord_le {n : ℕ} (a b : Fin n → ℝ) (k : Fin n) :
    dist (a k) (b k) ≤ dist a b := by
  by_cases hpos : 0 < dist a b
  · exact (dist_pi_le_iff (f := a) (g := b) hpos.le).mp (le_refl _) k
  · rw [not_lt] at hpos
    have h0 : a = b := dist_eq_zero.mp (le_antisymm hpos dist_nonneg)
    subst h0; simp

/-- HOL `NORM_VECMAT` (dih2k.hl:342): row norm ≤ whole norm. -/
theorem NORM_VECMAT {m n : ℕ} (x : FinVec m n) (j : Fin m) :
    nrm_p4 (vecmat_p4 j x) ≤ nrm_p4 x := by
  show Real.sqrt (∑ i, (vecmat_p4 j x) i ^ 2) ≤ Real.sqrt (∑ i, x i ^ 2)
  refine Real.sqrt_le_sqrt ?_
  refine le_trans (Finset.single_le_sum
    (f := fun (j' : Fin m) => ∑ k, x (finProdEquiv m n ⟨j', k⟩) ^ 2)
    (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j)) ?_
  exact (sum_finProdEquiv (fun i : Fin (m * n) => x i ^ 2)).symm.le

/-- HOL `DIST_VECMAT` (dih2k.hl:374): row distance ≤ whole distance. -/
theorem DIST_VECMAT {m n : ℕ} (x y : FinVec m n) (j : Fin m) :
    dist (vecmat_p4 j x) (vecmat_p4 j y) ≤ dist x y := by
  by_cases hpos : 0 < dist x y
  · refine (dist_pi_le_iff (f := vecmat_p4 j x) (g := vecmat_p4 j y)
      hpos.le).mpr fun k => dist_coord_le x y (finProdEquiv m n ⟨j, k⟩)
  · rw [not_lt] at hpos
    have h0 : x = y := dist_eq_zero.mp (le_antisymm hpos dist_nonneg)
    subst h0; simp

/-- HOL `DOT_VECMAT` (dih2k.hl:379): dot splits over rows. -/
theorem DOT_VECMAT {m n : ℕ} (x y : FinVec m n) :
    (∑ j, dotp_p4 (vecmat_p4 j x) (vecmat_p4 j y)) = dotp_p4 x y :=
  (sum_finProdEquiv (fun i => x i * y i)).symm

/-- HOL `NORM_VECMAT_SUM` (dih2k.hl:409): norm ≤ sum of row norms. -/
theorem NORM_VECMAT_SUM {m n : ℕ} (x : FinVec m n) :
    nrm_p4 x ≤ ∑ j, nrm_p4 (vecmat_p4 j x) := by
  have key := sum_finProdEquiv (fun i : Fin (m * n) => x i ^ 2)
  have step1 : Real.sqrt (∑ i, x i ^ 2)
      ≤ Real.sqrt (∑ j, ∑ k, x (finProdEquiv m n ⟨j, k⟩) ^ 2) :=
    Real.sqrt_le_sqrt key.le
  have step2 : Real.sqrt (∑ j, ∑ k, x (finProdEquiv m n ⟨j, k⟩) ^ 2)
      ≤ ∑ j, Real.sqrt (∑ k, x (finProdEquiv m n ⟨j, k⟩) ^ 2) :=
    sqrt_sum_le_sum_sqrt_p4 (fun j : Fin m => ∑ k, x (finProdEquiv m n ⟨j, k⟩) ^ 2)
      (fun j => Finset.sum_nonneg fun k _ => sq_nonneg _) Finset.univ
  exact le_trans step1 (le_trans step2 le_rfl)

/-- HOL `BOUNDED_MATVEC` (dih2k.hl:503). -/
theorem BOUNDED_MATVEC {m n : ℕ} (s : Fin m → Set (Fin n → ℝ))
    (hs : ∀ j, Bornology.IsBounded (s j)) :
    Bornology.IsBounded {x : FinVec m n | ∀ j : Fin m, vecmats_p4 x j ∈ s j} := by
  have hB : ∀ j : Fin m, ∃ C : ℝ, ∀ u ∈ s j, ∀ v ∈ s j, dist u v ≤ C := fun j =>
    Metric.isBounded_iff.mp (hs j)
  choose C hC using hB
  refine Metric.isBounded_iff.mpr ⟨(∑ j, |C j|) + 1, ?_⟩
  have hpos : 0 < (∑ j, |C j|) + 1 :=
    by linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (C j))]
  intro x hx y hy
  have hx' : x = matvec_p4 (vecmats_p4 x) := (MATVEC_VECMATS_ID x).symm
  have hy' : y = matvec_p4 (vecmats_p4 y) := (MATVEC_VECMATS_ID y).symm
  rw [hx', hy', dist_pi_le_iff (β := Fin (m * n)) (X := fun _ : Fin (m * n) => ℝ)
    (f := matvec_p4 (vecmats_p4 x)) (g := matvec_p4 (vecmats_p4 y))
    (r := (∑ j, |C j|) + 1) hpos.le]
  intro k
  calc dist (matvec_p4 (vecmats_p4 x) k) (matvec_p4 (vecmats_p4 y) k)
      = dist (vecmats_p4 x ⟨k / n, (divMod_lt_mul k.isLt).1⟩
          ⟨k % n, (divMod_lt_mul k.isLt).2⟩)
          (vecmats_p4 y ⟨k / n, (divMod_lt_mul k.isLt).1⟩
          ⟨k % n, (divMod_lt_mul k.isLt).2⟩) := rfl
    _ ≤ dist (vecmats_p4 x ⟨k / n, (divMod_lt_mul k.isLt).1⟩)
          (vecmats_p4 y ⟨k / n, (divMod_lt_mul k.isLt).1⟩) :=
        dist_coord_le _ _ _
    _ ≤ C (⟨k / n, (divMod_lt_mul k.isLt).1⟩ : Fin m) :=
        hC _ _ (hx _) _ (hy _)
    _ ≤ ∑ j, |C j| :=
        le_trans (le_abs_self _)
          (Finset.single_le_sum (f := fun j => |C j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ _))
    _ ≤ (∑ j, |C j|) + 1 := by linarith

/-- HOL `CLOSED_MATVEC` (dih2k.hl:536). -/
theorem CLOSED_MATVEC {m n : ℕ} (s : Fin m → Set (Fin n → ℝ))
    (hs : ∀ j, IsClosed (s j)) :
    IsClosed {x : FinVec m n | ∀ j : Fin m, vecmats_p4 x j ∈ s j} := by
  have hset : {x : FinVec m n | ∀ j : Fin m, vecmats_p4 x j ∈ s j}
      = ⋂ j, (fun x : FinVec m n => vecmats_p4 x j) ⁻¹' s j := by
    ext x; simp [Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun j => (hs j).preimage ?_
  exact continuous_pi fun k => continuous_apply _

/-- HOL `COMPACT_MATVEC` (dih2k.hl:583). -/
theorem COMPACT_MATVEC {m n : ℕ} (s : Fin m → Set (Fin n → ℝ))
    (hs : ∀ j, IsCompact (s j)) :
    IsCompact {x : FinVec m n | ∀ j : Fin m, vecmats_p4 x j ∈ s j} :=
  Metric.isCompact_of_isClosed_isBounded
    (CLOSED_MATVEC s fun j => (hs j).isClosed)
    (BOUNDED_MATVEC s fun j => (hs j).isBounded)

/-! ## ball_annulus facts (dih2k.hl:590-608, 635-757) -/

/-- HOL `cstab` (dih2k.hl:42). -/
def cstab_p4 : ℝ := 3.01

/-- HOL `SUC_NOT` (dih2k.hl:610), 0-based analogue on `i % k + 1`. -/
theorem SUC_NOT {k i : ℕ} (hk : 1 < k) :
    1 ≤ i % k + 1 ∧ i % k + 1 ≤ k ∧ i ≠ i % k + 1 := by
  have h1 : i % k < k := Nat.mod_lt i (by omega)
  refine ⟨by omega, by omega, ?_⟩
  intro he
  rcases Nat.lt_or_ge (i % k + 1) k with hlt | hge
  · have h2 : i % k = i := Nat.mod_eq_of_lt (by omega)
    omega
  · have heq : i = k := by omega
    have h2 : i % k = 0 := by rw [heq]; exact Nat.mod_self k
    omega

/-- HOL `CLOSED_BALL_ANNULUS` (dih2k.hl:590). -/
theorem CLOSED_BALL_ANNULUS : IsClosed ballAnnulus :=
  IsClosed.sdiff Metric.isClosed_closedBall Metric.isOpen_ball

/-- HOL `BOUNDED_BALL_ANNULUS` (dih2k.hl:595). -/
theorem BOUNDED_BALL_ANNULUS : Bornology.IsBounded ballAnnulus :=
  Metric.isBounded_closedBall.subset fun v hv => Set.sdiff_subset hv

/-- HOL `COMPACT_BALL_ANNULUS` (dih2k.hl:602). -/
theorem COMPACT_BALL_ANNULUS : IsCompact ballAnnulus :=
  Metric.isCompact_of_isClosed_isBounded CLOSED_BALL_ANNULUS BOUNDED_BALL_ANNULUS

theorem ballAnnulus_norm_bounds {v : V3} (hv : v ∈ ballAnnulus) :
    2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := by
  obtain ⟨hin, hnot⟩ := hv
  have h1 : ‖v‖ ≤ 2 * h0 := by
    simpa [dist_zero_right] using Metric.mem_closedBall.mp hin
  have h2 : 2 ≤ ‖v‖ := by
    have : ¬ (dist v (0:V3) < 2) := hnot
    simpa [dist_zero_right] using this
  exact ⟨h2, h1⟩

private theorem nonparallel_ball_annulus_aux {cstab : ℝ} (hc4 : cstab < 4)
    {v w : V3} (hv : v ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
    (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ cstab) : ¬ Collinear3 (0:V3) v w := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hv
  obtain ⟨hw2, hwu⟩ := ballAnnulus_norm_bounds hw
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hv2; norm_num at hv2
  have h0126 : h0 = 1.26 := rfl
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul hvne).mp hcol
  have hwv : w = c • v := by simpa using hc
  have e2 : ‖w‖ = |c| * ‖v‖ := by rw [hwv, norm_smul, Real.norm_eq_abs]
  by_cases hc0 : 0 ≤ c
  · have e3 : ‖w‖ = c * ‖v‖ := by rw [e2, abs_of_nonneg hc0]
    have e1 : ‖v - w‖ = |(1 - c) * ‖v‖| := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖v‖)]
    have habs : (1 - c) * ‖v‖ = ‖v‖ - c * ‖v‖ := by ring
    have e4 : ‖v - w‖ = |‖v‖ - ‖w‖| := by
      rw [e1, habs, e3]
    have hb : |‖v‖ - ‖w‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h02 : h0 < 2 := by norm_num [h0126]
    rw [e4] at h2
    linarith
  · have e1 : ‖v - w‖ = ‖v‖ + ‖w‖ := by
      rw [hwv]
      have hs : v - c • v = (1 - c) • v := by module
      rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - c)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : c < 0)]
      ring
    rw [e1] at hup
    linarith

/-- HOL `NONPARALLEL_BALL_ANNULUS` (dih2k.hl:635). -/
theorem NONPARALLEL_BALL_ANNULUS {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ cstab_p4) :
    ¬ Collinear3 (0:V3) v w :=
  nonparallel_ball_annulus_aux (by have h : cstab_p4 = 3.01 := rfl; norm_num [h])
    hv hw h2 hup

/-- HOL `NONPARALLEL_BALL_ANNULUS362` (dih2k.hl:697). -/
theorem NONPARALLEL_BALL_ANNULUS362 {v w : V3} (hv : v ∈ ballAnnulus)
    (hw : w ∈ ballAnnulus) (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ 3.62) :
    ¬ Collinear3 (0:V3) v w :=
  nonparallel_ball_annulus_aux (by norm_num) hv hw h2 hup

private theorem affGe_zero_smul {v z : V3} (hz : z ∈ affGe {0} {v}) :
    ∃ t : ℝ, 0 ≤ t ∧ z = t • v := by
  have hz' : Affsign (fun x : ℝ => 0 ≤ x) ({0} : Set V3) ({v} : Set V3) z := by
    simpa [affGe] using hz
  unfold Affsign at hz'
  obtain ⟨f, hf⟩ := hz'
  obtain ⟨hfin, heq, hfv, hsum1⟩ := hf
  refine ⟨f v, hfv v (by simp), ?_⟩
  rw [heq]
  by_cases hv0 : v = 0
  · subst hv0
    have hfin2 : hfin.toFinset = {0} := by ext x; simp
    rw [hfin2]; simp
  · have hfin2 : hfin.toFinset = {v, 0} := by ext x; simp [hv0]
    rw [hfin2, Finset.sum_insert (by simpa using hv0), Finset.sum_singleton]
    simp

private theorem collinear_pos_dist {v w : V3} (hvm : v ∈ ballAnnulus)
    (hwm : w ∈ ballAnnulus) (h2 : 2 ≤ ‖v - w‖) {c : ℝ} (hc0 : 0 < c)
    (hcw : w = c • v) : False := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hvm
  obtain ⟨hw2, hwu⟩ := ballAnnulus_norm_bounds hwm
  have h0126 : h0 = 1.26 := rfl
  have e3 : ‖w‖ = c * ‖v‖ := by rw [hcw, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0.le]
  have e1 : ‖v - w‖ = |(1 - c) * ‖v‖| := by
    rw [hcw]
    have hs : v - c • v = (1 - c) • v := by module
    rw [hs, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖v‖)]
  have habs : (1 - c) * ‖v‖ = ‖v‖ - c * ‖v‖ := by ring
  have e4 : ‖v - w‖ = |‖v‖ - ‖w‖| := by rw [e1, habs, e3]
  have hb : |‖v‖ - ‖w‖| ≤ 2 * h0 - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h02 : h0 < 2 := by norm_num [h0126]
  rw [e4] at h2
  linarith

/-- HOL `VEC0_BALL_ANNULUS` (dih2k.hl:758). -/
theorem VEC0_BALL_ANNULUS {v w z : V3} (h2 : 2 ≤ ‖v - w‖) (hvm : v ∈ ballAnnulus)
    (hwm : w ∈ ballAnnulus) (hzv : z ∈ affGe {0} {v}) (hzw : z ∈ affGe {0} {w}) :
    z = 0 := by
  obtain ⟨t, ht0, htz⟩ := affGe_zero_smul hzv
  obtain ⟨s, hs0, hsw⟩ := affGe_zero_smul hzw
  by_cases ht : t = 0
  · rw [ht, zero_smul] at htz; exact htz
  by_cases hs : s = 0
  · rw [hs, zero_smul] at hsw; exact hsw
  have htlt : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  have hslt : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  exfalso
  refine collinear_pos_dist hvm hwm h2 (c := t / s) (div_pos htlt hslt) ?_
  have hne2 : s ≠ 0 := ne_of_gt hslt
  have htv : s • w = t • v := hsw.symm.trans htz
  have key : w = (t / s) • v := by
    calc w = s⁻¹ • (s • w) := (inv_smul_smul₀ hne2 w).symm
      _ = s⁻¹ • (t • v) := by rw [htv]
      _ = (t / s) • v := by rw [smul_smul, inv_mul_eq_div]
  simpa using key

/-- HOL `angle a b c = acs((a-b)·(c-b)/(|a-b||c-b|))` (flyspeck `angle_def`). -/
noncomputable def angle_p4 (a b c : V3) : ℝ :=
  Real.arccos ((inner ℝ (a - b) (c - b)) / (‖a - b‖ * ‖c - b‖))

/-- HOL `BALL_ANNULUS_3PONITS_ANGLE` (dih2k.hl:814). -/
theorem BALL_ANNULUS_3PONITS_ANGLE {v w : V3} (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hvw : v ≠ w) (h2 : 2 ≤ ‖v - w‖) (hvm : v ∈ ballAnnulus) (hwm : w ∈ ballAnnulus) :
    0 < Real.cos (angle_p4 v w 0) := by
  obtain ⟨hv2, hvu⟩ := ballAnnulus_norm_bounds hvm
  obtain ⟨w2, wu⟩ := ballAnnulus_norm_bounds hwm
  have h0126 : h0 = 1.26 := rfl
  have hden : 0 < ‖v - w‖ * ‖(0:V3) - w‖ := by
    have e1 : (0:ℝ) < ‖v - w‖ := by linarith
    have e2n : ‖(0:V3) - w‖ = ‖w‖ := by simp
    have e3 : (0:ℝ) < ‖w‖ := by linarith
    exact mul_pos e1 (e2n ▸ e3)
  have hcauchy : |inner ℝ (v - w) ((0:V3) - w)| ≤ ‖v - w‖ * ‖(0:V3) - w‖ :=
    abs_real_inner_le_norm _ _
  have hab := abs_le.mp hcauchy
  have h1 : -1 ≤ inner ℝ (v - w) ((0:V3) - w) / (‖v - w‖ * ‖(0:V3) - w‖) := by
    rw [le_div_iff₀ hden]
    linarith
  have h2r : inner ℝ (v - w) ((0:V3) - w) / (‖v - w‖ * ‖(0:V3) - w‖) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hcos : Real.cos (angle_p4 v w 0)
      = inner ℝ (v - w) ((0:V3) - w) / (‖v - w‖ * ‖(0:V3) - w‖) :=
    Real.cos_arccos h1 h2r
  rw [hcos]
  have hexpand : inner ℝ (v - w) ((0:V3) - w) = ‖w‖ ^ 2 - inner ℝ v w := by
    rw [zero_sub, inner_sub_left, inner_neg_right, inner_neg_right,
      real_inner_self_eq_norm_sq]
    ring
  have hsq : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    exact real_inner_sub_sub_self v w
  have h4 : (4:ℝ) ≤ ‖v - w‖ ^ 2 := by nlinarith
  have h1b : ‖v‖ ^ 2 ≤ (2 * h0) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have h2w : (4:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
  have h0sq : h0 ^ 2 < 2 := by norm_num [h0126]
  have hkey : inner ℝ v w < ‖w‖ ^ 2 := by
    have h2i : 2 * inner ℝ v w ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 - 4 := by
      have := h4
      nlinarith [hsq]
    nlinarith [h2i, h1b, h2w, h0sq]
  rw [hexpand]
  exact div_pos (by linarith) hden

/-! ## Continuity and limits (dih2k.hl:1297-1578) -/

/-- HOL `CONTINUOUS_ON_LIFT_PRODUCT` (dih2k.hl:1297): a product of
continuous reals becomes a continuous pi-valued map. -/
theorem CONTINUOUS_ON_LIFT_PRODUCT {m n : ℕ} {s : Set (Fin m → ℝ)}
    (c : Fin n → (Fin m → ℝ) → ℝ) (hc : ∀ j, ContinuousOn (c j) s) :
    ContinuousOn (fun x j => c j x) s :=
  continuousOn_pi.mpr hc

/-- HOL `CONTINUOUS_ON_DET` (dih2k.hl:1323). -/
theorem CONTINUOUS_ON_DET {m : ℕ} (s : Set (FinVec m m)) :
    ContinuousOn (fun y => Matrix.det (Matrix.of (vecmats_p4 y))) s :=
  Continuous.continuousOn
    (Continuous.matrix_det (continuous_pi fun _ => continuous_pi fun _ => continuous_apply _))

/-- HOL `ROW_SUB` (dih2k.hl:1370). -/
theorem ROW_SUB {m n : ℕ} (x y : FinVec m n) (j : Fin m) :
    vecmats_p4 (x - y) j = vecmats_p4 x j - vecmats_p4 y j :=
  funext fun _ => rfl

/-- HOL `LIM_MATVEC` (dih2k.hl:1374). -/
theorem LIM_MATVEC {m n : ℕ} (x : ℕ → FinMat m n) (l : FinMat m n)
    (h : ∀ j : Fin m, Filter.Tendsto (fun k => x k j) Filter.atTop (nhds (l j))) :
    Filter.Tendsto (fun k => matvec_p4 (x k)) Filter.atTop (nhds (matvec_p4 l)) := by
  rw [tendsto_pi_nhds]
  intro kk
  have hj : kk / n < m ∧ kk % n < n := divMod_lt_mul kk.isLt
  have hidx : (finProdEquiv m n (⟨kk / n, hj.1⟩, ⟨kk % n, hj.2⟩) : ℕ) = kk := by
    show (kk / n) * n + kk % n = (kk : ℕ)
    rw [Nat.mul_comm]
    exact (kk : ℕ).div_add_mod n
  have hxe : (fun i : ℕ => matvec_p4 (x i) kk)
      = (fun i : ℕ => x i ⟨kk / n, hj.1⟩ ⟨kk % n, hj.2⟩) := rfl
  have hle : (fun i : ℕ => matvec_p4 l kk)
      = (fun i : ℕ => l ⟨kk / n, hj.1⟩ ⟨kk % n, hj.2⟩) := rfl
  rw [hxe]
  rw [show matvec_p4 l kk = l ⟨kk / n, hj.1⟩ ⟨kk % n, hj.2⟩ from rfl]
  exact (tendsto_pi_nhds.mp (h ⟨kk / n, hj.1⟩)) ⟨kk % n, hj.2⟩

/-- HOL `LIM_VECMAT` (dih2k.hl:1443). -/
theorem LIM_VECMAT {m n : ℕ} (x : ℕ → FinMat m n) (l : FinMat m n)
    (h : Filter.Tendsto (fun k => matvec_p4 (x k)) Filter.atTop (nhds (matvec_p4 l))) :
    ∀ j : Fin m, Filter.Tendsto (fun k => x k j) Filter.atTop (nhds (l j)) := by
  intro j
  rw [tendsto_pi_nhds] at h
  rw [tendsto_pi_nhds]
  intro k
  have hxe : (fun a : ℕ => matvec_p4 (x a) (finProdEquiv m n ⟨j, k⟩))
      = (fun a : ℕ => x a j k) :=
    funext fun a => congrFun (VECMAT_ROW (x a) j) k
  have hle0 : matvec_p4 l (finProdEquiv m n ⟨j, k⟩) = l j k :=
    congrFun (VECMAT_ROW l j) k
  have hinst := h (finProdEquiv m n ⟨j, k⟩)
  rw [hxe, hle0] at hinst
  exact hinst

theorem continuous_ofLpV3 : Continuous (fun v : V3 => (WithLp.ofLp v : Fin 3 → ℝ)) :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).continuous

theorem continuous_toLpV3 : Continuous (fun w : Fin 3 → ℝ => (WithLp.toLp 2 w : V3)) :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm.continuous

theorem continuous_dotP {X : Type*} [TopologicalSpace X] {u v : X → (Fin 3 → ℝ)}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => (u x) ⬝ᵥ (v x)) := by
  simp only [dotProduct]
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hu).mul ((continuous_apply i).comp hv)

theorem continuous_crossP {X : Type*} [TopologicalSpace X] {u v : X → (Fin 3 → ℝ)}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => (u x) ⨯₃ (v x)) := by
  apply continuous_pi fun i => ?_
  simp only [cross_apply]
  fin_cases i
  all_goals
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact (((continuous_apply _).comp hu).mul ((continuous_apply _).comp hv)).sub
      (((continuous_apply _).comp hu).mul ((continuous_apply _).comp hv))

/-- HOL `CROSS_DOT_SEQUENTIALLY` (dih2k.hl:1467). -/
theorem CROSS_DOT_SEQUENTIALLY {f g h : ℕ → V3} {a b c : V3}
    (hf : Filter.Tendsto f Filter.atTop (nhds a))
    (hg : Filter.Tendsto g Filter.atTop (nhds b))
    (hh : Filter.Tendsto h Filter.atTop (nhds c)) :
    Filter.Tendsto (fun n => ((WithLp.ofLp (f n) : Fin 3 → ℝ) ⨯₃
      (WithLp.ofLp (g n) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (h n) : Fin 3 → ℝ)) Filter.atTop
      (nhds (((WithLp.ofLp (a) : Fin 3 → ℝ) ⨯₃ (WithLp.ofLp (b) : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp (c) : Fin 3 → ℝ))) := by
  have hcont : Continuous fun q : (V3 × V3) × V3 =>
      ((WithLp.ofLp q.1.1 : Fin 3 → ℝ) ⨯₃ (WithLp.ofLp q.1.2 : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp q.2 : Fin 3 → ℝ) := by
    have h1 : Continuous fun q : (V3 × V3) × V3 => (WithLp.ofLp q.1.1 : Fin 3 → ℝ) :=
      continuous_ofLpV3.comp (continuous_fst.comp continuous_fst)
    have h2 : Continuous fun q : (V3 × V3) × V3 => (WithLp.ofLp q.1.2 : Fin 3 → ℝ) :=
      continuous_ofLpV3.comp (continuous_snd.comp continuous_fst)
    have h3 : Continuous fun q : (V3 × V3) × V3 => (WithLp.ofLp q.2 : Fin 3 → ℝ) :=
      continuous_ofLpV3.comp continuous_snd
    exact continuous_dotP (continuous_crossP h1 h2) h3
  have hpair : Filter.Tendsto (fun n => ((f n, g n), h n)) Filter.atTop
      (nhds ((a, b), c)) := by
    refine Filter.Tendsto.prodMk_nhds ?_ hh
    exact Filter.Tendsto.prodMk_nhds hf hg
  have hcomp : Filter.Tendsto (fun n => (fun q : (V3 × V3) × V3 =>
      ((WithLp.ofLp q.1.1 : Fin 3 → ℝ) ⨯₃ (WithLp.ofLp q.1.2 : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp q.2 : Fin 3 → ℝ)) ((f n, g n), h n)) Filter.atTop
      (nhds ((fun q : (V3 × V3) × V3 =>
      ((WithLp.ofLp q.1.1 : Fin 3 → ℝ) ⨯₃ (WithLp.ofLp q.1.2 : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp q.2 : Fin 3 → ℝ)) ((a, b), c))) :=
    (hcont.tendsto ((a, b), c)).comp hpair
  have heq : (fun n => (fun q : (V3 × V3) × V3 =>
      ((WithLp.ofLp q.1.1 : Fin 3 → ℝ) ⨯₃ (WithLp.ofLp q.1.2 : Fin 3 → ℝ)) ⬝ᵥ
        (WithLp.ofLp q.2 : Fin 3 → ℝ)) ((f n, g n), h n))
      = (fun n => ((WithLp.ofLp (f n) : Fin 3 → ℝ) ⨯₃
      (WithLp.ofLp (g n) : Fin 3 → ℝ)) ⬝ᵥ (WithLp.ofLp (h n) : Fin 3 → ℝ)) :=
    funext fun n => rfl
  rw [heq] at hcomp
  exact hcomp

/-! ## Remaining ball_annulus geometry (dih2k.hl:852-1578) -/

/-- HOL `BALL_ANNULUS_3PONITS_NORM_MIN` (dih2k.hl:852, ~300-line HOL proof). -/
theorem BALL_ANNULUS_3PONITS_NORM_MIN {v w z : V3} {a t : ℝ}
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w) (hnc : ¬ Collinear3 (0:V3) v w)
    (h2 : 2 ≤ ‖v - w‖) (hvm : v ∈ ballAnnulus) (hwm : w ∈ ballAnnulus)
    (hzw : z = t • w) (ht : 0 < t) (ha : a = Real.sqrt (4 - h0 ^ 2)) :
    a ≤ ‖v - z‖ := by
  sorry

/-- HOL `BALL_ANNULUS_4PONITS_AFF_GT` (dih2k.hl:1149). -/
theorem BALL_ANNULUS_4PONITS_AFF_GT {v w z : V3}
    (hnc1 : ¬ Collinear3 (0:V3) v z) (hnc2 : ¬ Collinear3 (0:V3) w z)
    (h2 : 2 ≤ ‖v - w‖) (hup : ‖v - w‖ ≤ cstab_p4) (h3 : 2 ≤ ‖z - v‖)
    (h4 : 2 ≤ ‖z - w‖) (hvm : v ∈ ballAnnulus) (hwm : w ∈ ballAnnulus)
    (hzm : z ∈ ballAnnulus) : z ∉ affGt {0} {v, w} := by
  sorry

/-- HOL `AFF_INTER_AFF_GT_EQ_EMPTY` (dih2k.hl:1208); HOL `aff {x,y}` is
`affineSpan ℝ {x,y}`. -/
theorem AFF_INTER_AFF_GT_EQ_EMPTY {x y z : V3} (hnc : ¬ Collinear3 x y z) :
    ((affineSpan ℝ {x, y} : Set V3) ∩ affGt {x} {y, z}) = ∅ := by
  sorry

/-- HOL `AFF_GE_INTER_AFF_GT_EQ_EMPTY` (dih2k.hl:1244). -/
theorem AFF_GE_INTER_AFF_GT_EQ_EMPTY {x y z u : V3} (hnc : ¬ Collinear3 x y z)
    (hxu : x ≠ u) (hu : u ∉ affGt {x} {y, z}) :
    (affGe {x} {u} ∩ affGt {x} {y, z}) = ∅ := by
  sorry

/-- HOL `POINT_COM_AFF_GT_INTER` (dih2k.hl:1542). -/
theorem POINT_COM_AFF_GT_INTER {y z z1 w : V3}
    (h1 : ¬ Collinear3 (0:V3) y z) (h2 : ¬ Collinear3 (0:V3) y z1)
    (hw : w ∈ affGt {0} {y, z} ∩ affGt {0} {y, z1}) :
    z1 ∈ affGe {0, y} {z} := by
  sorry

/-! ## finite_product cardinality (dih2k.hl:127-146) -/

/-- HOL `FINITE_PRODUCT_IMAGE`: the flattening is surjective on the type. -/
theorem FINITE_PRODUCT_IMAGE {m n : ℕ} :
    Set.univ = Set.range (matvec_p4 (m := m) (n := n)) := by
  ext x
  refine ⟨fun _ => ?_, fun _ => Set.mem_univ _⟩
  exact ⟨vecmats_p4 x, MATVEC_VECMATS_ID x⟩

/-- HOL `DIMINDEX_HAS_SIZE_FINITE_PRODUCT` (dih2k.hl:134). -/
theorem DIMINDEX_HAS_SIZE_FINITE_PRODUCT {m n : ℕ} :
    Set.Finite (Set.univ : Set (Fin (m * n))) ∧
      Set.ncard (Set.univ : Set (Fin (m * n))) = m * n := by
  refine ⟨Set.toFinite Set.univ, ?_⟩
  simp

/-- HOL `DIMINDEX_FINITE_PRODUCT` (dih2k.hl:142). -/
theorem DIMINDEX_FINITE_PRODUCT {m n : ℕ} :
    Fintype.card (Fin (m * n)) = m * n :=
  Fintype.card_fin _

/-! ## `_p4` copies of external flyspeck defs (NEEDS: replace by imports
at merge; sources WRGCVDR.hl:78-140, localization.hl:66-95) -/

/-- NEEDS: flyspeck `EE` (WRGCVDR.hl:95) `EE v S = {w | {v,w} IN S}`. -/
def EE_p4 (v : V3) (S : Set (Set V3)) : Set V3 := {w | {v, w} ∈ S}

/-- NEEDS: flyspeck `azim_cycle` (fan library; the azimuthal successor).
DISCHARGED (was `sorry`): verbatim body copy of `Kepler.Text.azimCycle_p3`
(LocalAuto3 = WRGCVDR.hl:78, identical modulo binder names); kept as a
`_p4` copy per the lane convention. -/
noncomputable def azimCycle_p4 (W : Set V3) (v0 u w : V3) : V3 :=
  if W ⊆ {w} then w
  else
    Classical.epsilon fun z : V3 => z ≠ w ∧ z ∈ W ∧ ∀ q ∈ W, q ≠ w →
      azim v0 u w z < azim v0 u w q ∨
        azim v0 u w z = azim v0 u w q ∧
          ‖projection (z - v0) (u - v0)‖ ≤ ‖projection (q - v0) (u - v0)‖

/-- NEEDS: flyspeck `ivs_azim_cycle` (WRGCVDR.hl:126). -/
noncomputable def ivsAzimCycle_p4 (W : Set V3) (v0 v w : V3) : V3 :=
  if h : ∃ x, x ∈ W ∧ azimCycle_p4 W v0 v x = w then h.choose else w

/-- NEEDS: flyspeck `ord_pairs` (WRGCVDR.hl:100). -/
def ordPairs_p4 (E : Set (Set V3)) : Set (V3 × V3) := {p | {p.1, p.2} ∈ E}

/-- NEEDS: flyspeck `self_pairs` (WRGCVDR.hl:101). -/
def selfPairs_p4 (E : Set (Set V3)) (V : Set V3) : Set (V3 × V3) :=
  {p | p.1 = p.2 ∧ p.1 ∈ V ∧ EE_p4 p.1 E = ∅}

/-- NEEDS: flyspeck `darts_of_hyp` (WRGCVDR.hl:102). -/
def dartsOfHyp_p4 (E : Set (Set V3)) (V : Set V3) : Set (V3 × V3) :=
  ordPairs_p4 E ∪ selfPairs_p4 E V

/-- NEEDS: flyspeck `ee_of_hyp` (WRGCVDR.hl:105). -/
noncomputable def eeOfHyp_p4 (x : V3) (V : Set V3) (E : Set (Set V3)) (p : V3 × V3) : V3 × V3 :=
  if p ∈ dartsOfHyp_p4 E V then (p.2, p.1) else p

/-- NEEDS: flyspeck `nn_of_hyp` (WRGCVDR.hl:113). -/
noncomputable def nnOfHyp_p4 (x : V3) (V : Set V3) (E : Set (Set V3)) (p : V3 × V3) : V3 × V3 :=
  if p ∈ dartsOfHyp_p4 E V then (p.1, azimCycle_p4 (EE_p4 p.1 E) x p.1 p.2) else p

/-- NEEDS: flyspeck `ff_of_hyp` (WRGCVDR.hl:130). -/
noncomputable def ffOfHyp_p4 (x : V3) (V : Set V3) (E : Set (Set V3)) (p : V3 × V3) : V3 × V3 :=
  if p ∈ dartsOfHyp_p4 E V then (p.2, ivsAzimCycle_p4 (EE_p4 p.2 E) x p.2 p.1) else p

/-- NEEDS: flyspeck `has_orders` (WRGCVDR.hl:78), infix `has_orders k`. -/
def hasOrders_p4 {α : Type*} (f : α → α) (k : ℕ) : Prop :=
  (∀ i, 0 < i → i < k → f^[i] ≠ id) ∧ f^[k] = id

/-- NEEDS: flyspeck `HYP`/`hypermap` (WRGCVDR.hl:140) packed into the Lean
`Hypermap` structure; the proof fields are exactly the Section-F content.
DISCHARGED (was `sorry`): under `FAN x V E` this is the importable
`Kepler.Text.Fan.hypermapOfFan x V E` (its dart set is `dart1OfFan`, which
is what the Section-F statements constrain — all their darts are edge
darts, and `edgeMap/nodeMap/faceMap` agree with the `_p4` of-hyp maps on
`dart1OfFan`); off the fan a junk hypermap is taken (no downstream
statement constrains it). -/
noncomputable def hyp_p4 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Hypermap (V3 × V3) := by
  by_cases h : FAN x V E
  · exact hypermapOfFan x V E h
  · exact
      { darts := ∅, edgeMap := 1, nodeMap := 1, faceMap := 1,
        edgeMap_permutes := fun x _ => rfl, nodeMap_permutes := fun x _ => rfl,
        faceMap_permutes := fun x _ => rfl, comp_eq_one := by simp }

/-- NEEDS: flyspeck `face` (hypermap.hl) `= {y | y IN dart H ∧ ∃ n,
ITER n (face_map H) x = y}`; reconcile with `Hypermap.faceSet`. -/
noncomputable def face_p4 (H : Hypermap (V3 × V3)) (p : V3 × V3) : Set (V3 × V3) :=
  {y | y ∈ (H.darts : Set (V3 × V3)) ∧ ∃ n : ℕ, H.faceMap^[n] p = y}

/-- NEEDS: flyspeck `dih2k` (WRGCVDR.hl:86). -/
def dih2k_p4 (H : Hypermap (V3 × V3)) (k : ℕ) : Prop :=
  H.darts.card = 2 * k ∧
    (∀ p ∈ H.darts, (↑H.darts : Set (V3 × V3))
      = face_p4 H p ∪ (H.nodeMap : V3 × V3 → V3 × V3) '' face_p4 H p) ∧
    hasOrders_p4 (H.faceMap : V3 × V3 → V3 × V3) k ∧
    hasOrders_p4 (H.edgeMap : V3 × V3 → V3 × V3) 2 ∧
    hasOrders_p4 (H.nodeMap : V3 × V3 → V3 × V3) 2

/-- NEEDS: flyspeck `wedge_ge` (localization.hl:85). -/
def wedgeGe_p4 (v0 v1 w1 w2 : V3) : Set V3 :=
  {z | 0 ≤ azim v0 v1 w1 z ∧ azim v0 v1 w1 z ≤ azim v0 v1 w1 w2}

/-- NEEDS: flyspeck `wedge_in_fan_ge` (localization.hl:88). -/
noncomputable def wedgeInFanGe_p4 (e : V3 × V3) (E : Set (Set V3)) : Set V3 :=
  if 1 < (EE_p4 e.1 E).ncard then
    wedgeGe_p4 0 e.1 e.2 (azimCycle_p4 (EE_p4 e.1 E) 0 e.1 e.2)
  else Set.univ

/-- NEEDS: flyspeck `azim_in_fan` (localization.hl:74). -/
noncomputable def azimInFan_p4 (e : V3 × V3) (E : Set (Set V3)) : ℝ :=
  if 1 < (EE_p4 e.1 E).ncard then
    azim 0 e.1 e.2 (azimCycle_p4 (EE_p4 e.1 E) 0 e.1 e.2)
  else 2 * Real.pi

/-- NEEDS: flyspeck `local_fan` (localization.hl:66); CARD ↦ `Set.ncard`. -/
def localFan_p4 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  FAN 0 V E ∧
    (∃ p ∈ (hyp_p4 0 V E).darts, FF = face_p4 (hyp_p4 0 V E) p) ∧
    dih2k_p4 (hyp_p4 0 V E) FF.ncard

/-- NEEDS: flyspeck `convex_local_fan` (localization.hl:92). -/
def convexLocalFan_p4 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)) : Prop :=
  localFan_p4 V E FF ∧
    ∀ x ∈ FF, azimInFan_p4 x E ≤ Real.pi ∧ V ⊆ wedgeInFanGe_p4 x E

/-! ## The section-1 definitions (dih2k.hl:42-124) -/

/-- HOL `rho_fun` (dih2k.hl:44). -/
noncomputable def rhoFun_p4 (y : ℝ) : ℝ :=
  1 + (1 / (2 * h0 - 2)) * (1 / Real.pi) * sol0 * (y - 2)

/-- Fin-successor with wraparound (`SUC (i MOD dimindex(:M))` 0-based). -/
def finNext {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- HOL `tau_fun` (dih2k.hl:46); the HOL set-sum is encoded as a `Finset`
sum (finiteness is an input of the flyspeck applications). -/
noncomputable def tauFun_p4 (f : Finset (V3 × V3)) (E : Set (Set V3)) : ℝ :=
  f.sum (fun e => rhoFun_p4 ‖e.1‖ * azimInFan_p4 e E) -
    (Real.pi + sol0) * (f.card - 2)


/-- HOL `torsor` (dih2k.hl:48). -/
def torsor_p4 {α : Type*} (s : Finset α) (k : ℕ) (f : α → α) : Prop :=
  (∀ x ∈ s, f x ∈ s) ∧ (∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) ∧
    (∀ i x, 0 < i → i < k → x ∈ s → f^[i] x ≠ x) ∧
    (∀ x ∈ s, f^[k] x = x) ∧ s.card = k

/-- HOL `constraint_system` (dih2k.hl:52); the polymorphic HOL index type is
instantiated at `ℕ` (the only instantiation used by the dih2k chapter). -/
def constraintSystem_p4 (k d : ℕ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  3 ≤ k ∧ k ≤ 6 ∧ torsor_p4 s k f ∧
    (∀ i j, a i j = a j i ∧ b i j = b j i ∧ a i j ≤ b i j) ∧
    (∀ i j, a i j = a i (f^[k] j) ∧ b i j = b i (f^[k] j)) ∧
    J ⊆ (s.image fun i => {i, f i} : Finset (Finset ℕ)) ∧
    J.card + k ≤ 6

/-- HOL `stable_system` (dih2k.hl:61). -/
def stableSystem_p4 (k d : ℕ) (s : Finset ℕ) (a b : ℕ → ℕ → ℝ)
    (J : Finset (Finset ℕ)) (f : ℕ → ℕ) : Prop :=
  constraintSystem_p4 k d s a b J f ∧
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 ≤ a i j) ∧
    (∀ i ∈ s, a i i = 0 ∧ b i (f i) ≤ cstab_p4) ∧
    (∀ i j, {i, j} ∈ J → a i j = Real.sqrt 8 ∧ b i j = cstab_p4)

/-- HOL `V_SY` (dih2k.hl:70): `rows v`. -/
def V_SY_p4 {m : ℕ} (v : Fin m → V3) : Set V3 := Set.range v

/-- HOL `E_SY` (dih2k.hl:73): cyclic 2-element edges. -/
def E_SY_p4 {m : ℕ} (v : Fin m → V3) : Set (Set V3) :=
  (fun i : Fin m => {v i, v (finNext i)}) '' Set.univ

/-- HOL `F_SY` (dih2k.hl:76): cyclic ordered darts. -/
def F_SY_p4 {m : ℕ} (v : Fin m → V3) : Set (V3 × V3) :=
  (fun i : Fin m => (v i, v (finNext i))) '' Set.univ

/-- HOL `CONDITION1_SY` (dih2k.hl:79). -/
def CONDITION1_SY_p4 {m : ℕ} (a b : Fin m → Fin m → ℝ) (v : Fin m → V3) : Prop :=
  ∀ i j : Fin m, a i j ≤ ‖v i - v j‖ ∧ ‖v i - v j‖ ≤ b i j

/-- HOL `CONDITION2_SY` (dih2k.hl:88). -/
def CONDITION2_SY_p4 {m : ℕ} (v : Fin m → V3) : Prop :=
  convexLocalFan_p4 (V_SY_p4 v) (E_SY_p4 v) (F_SY_p4 v)

/-- HOL `B_SY1` (dih2k.hl:122). -/
def B_SY1_p4 {m : ℕ} (a b : Fin m → Fin m → ℝ) : Set (FinVec m 3) :=
  (fun v : Fin m → V3 =>
      fun i : Fin (m * 3) =>
        (v ⟨(i : ℕ) / 3, (Nat.div_lt_iff_lt_mul (k := 3) (by norm_num)).mpr i.isLt⟩ :
              Fin 3 → ℝ) ⟨(i : ℕ) % 3, Nat.mod_lt (i : ℕ) (by norm_num : 0 < 3)⟩)
    '' {v | (∀ i : Fin m, v i ∈ ballAnnulus) ∧ CONDITION1_SY_p4 a b v ∧
      CONDITION2_SY_p4 v}



/-! ## Section F: the hypermap of the fan (dih2k.hl:1579-3320)

Vocabulary: `l : FinVec m 3`, `VN = vecmatsV3_p4 l`, `V = V_SY_p4 VN`,
`E = E_SY_p4 VN`, `H = hyp_p4 0 V E`, `u = VN i`, `v = VN (finNext i)`,
`w = VN (finNext (finNext i))`.  The injectivity hypothesis is HOL's
`!i j. 1<=i /\ i<=dimindex(:M) /\ ... /\ row i (vecmats l) = row j (vecmats l) ==> i=j`.
Most proofs are `sorry` (giants). -/

/-- HOL `vecmats l` with `real^3` rows. -/
def vecmatsV3_p4 {m : ℕ} (l : FinVec m 3) : Fin m → V3 :=
  fun j => (WithLp.toLp 2 (vecmats_p4 l j) : V3)

/-- HOL `EDGE_IN_E_SY` (dih2k.hl:1610). -/
theorem EDGE_IN_E_SY {m : ℕ} (l : FinVec m 3) (i : Fin m) :
    {vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i)} ∈
      E_SY_p4 (vecmatsV3_p4 l) :=
  ⟨i, Set.mem_univ _, rfl⟩

/-- HOL `MOD_IMP_EQ` (dih2k.hl:1679). -/
theorem MOD_IMP_EQ {k i j : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hmod : i % k = j % k) : i = j := by
  rcases Nat.lt_or_ge i k with h1 | h1
  · rcases Nat.lt_or_ge j k with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod; exact hmod
    · have h4 : j = k := le_antisymm hjk h2
      rw [h4, Nat.mod_self] at hmod
      rw [Nat.mod_eq_of_lt h1] at hmod
      omega
  · have h4 : i = k := le_antisymm hik h1
    rcases Nat.lt_or_ge j k with h2 | h2
    · rw [h4, Nat.mod_self] at hmod
      rw [Nat.mod_eq_of_lt h2] at hmod
      omega
    · have h5 : j = k := le_antisymm hjk h2
      exact h4.trans h5.symm

/-- HOL `SUC_POWER2_NOT` (dih2k.hl:2325). -/
theorem SUC_POWER2_NOT {k i : ℕ} (hk : 2 < k) (hik : i ≤ k) :
    i ≠ (i % k + 1) % k + 1 := by
  intro he
  rcases Nat.lt_or_ge i k with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at he
    rcases Nat.lt_or_ge (i + 1) k with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at he; omega
    · have h3 : i + 1 = k := le_antisymm (by omega) h2
      rw [h3, Nat.mod_self] at he
      omega
  · have h4 : i = k := le_antisymm hik h1
    rw [h4, Nat.mod_self] at he
    rw [Nat.mod_eq_of_lt (by omega)] at he
    omega

/-- HOL `FINITE_F_SY` (dih2k.hl:2380). -/
theorem FINITE_F_SY {m : ℕ} (l : FinVec m 3) :
    (F_SY_p4 (vecmatsV3_p4 l)).Finite :=
  Set.Finite.image _ (Set.toFinite Set.univ)

/-- HOL `FINITE_IMAGE_F_SY` (dih2k.hl:2399). -/
theorem FINITE_IMAGE_F_SY {m : ℕ} (l : FinVec m 3) :
    ((fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) ''
      Set.univ).Finite :=
  Set.Finite.image _ (Set.toFinite Set.univ)

/-- HOL `CARD_F_SY_EQ` (dih2k.hl:2007). -/
theorem CARD_F_SY_EQ {m : ℕ} (l : FinVec m 3)
    (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    Set.ncard (F_SY_p4 (vecmatsV3_p4 l)) = m := by
  have hinj2 : Function.Injective
      (fun i : Fin m => (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))) :=
    fun p q hpq => hinj _ _ (congrArg Prod.fst hpq)
  rw [F_SY_p4, Set.ncard_image_of_injective _ hinj2, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- HOL `CARD_IMAGE_F_SY_EQ` (dih2k.hl:2298). -/
theorem CARD_IMAGE_F_SY_EQ {m : ℕ} (l : FinVec m 3)
    (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    Set.ncard ((fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) ''
      Set.univ) = m := by
  have hinj2 : Function.Injective
      (fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) :=
    fun p q hpq => hinj _ _ (congrArg Prod.snd hpq)
  rw [Set.ncard_image_of_injective _ hinj2, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- HOL `EXISTS_POINT_DART_OF_HYP` (dih2k.hl:2825). -/
theorem EXISTS_POINT_DART_OF_HYP {m : ℕ} (l : FinVec m 3) (hm : 2 < m) :
    ∃ x, x ∈ dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)) := by
  have h0 : 0 < m := by omega
  have hed := EDGE_IN_E_SY l ⟨0, by omega⟩
  refine ⟨(vecmatsV3_p4 l ⟨0, by omega⟩, vecmatsV3_p4 l (finNext ⟨0, by omega⟩)),
    Set.mem_union_left _ ?_⟩
  exact hed

/-- HOL `DART_FAN_SY` (dih2k.hl:1579). -/
theorem DART_FAN_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) (i : Fin m)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))) :
    x ∈ (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))).darts := by
  sorry

/-- HOL `DART_FAN_SY1` (dih2k.hl:1594). -/
theorem DART_FAN_SY1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) (i : Fin m)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) :
    x ∈ (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))).darts := by
  sorry

/-- HOL `EQ_EDGE_E_SY` (dih2k.hl:1622). -/
theorem EQ_EDGE_E_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {v x w : V3} (hv : vecmatsV3_p4 l i = v)
    (hx : vecmatsV3_p4 l (finNext i) = x)
    (hvw : ({v, x} : Set V3) = ({v, w} : Set V3)) :
    x = w := by
  sorry

/-- HOL `EQ_EDGE_E_SY1` (dih2k.hl:1652). -/
theorem EQ_EDGE_E_SY1 {m : ℕ} (l : FinVec m 3) (hm : 1 < m)
    (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {v x w : V3} (hv : vecmatsV3_p4 l i = v)
    (hx : vecmatsV3_p4 l (finNext i) = x)
    (hvw : ({v, x} : Set V3) = ({w, x} : Set V3)) :
    v = w := by
  sorry

/-- HOL `SET_OF_EDGE_CARD_EQ2` (dih2k.hl:1715). -/
theorem SET_OF_EDGE_CARD_EQ2 {m : ℕ} (l : FinVec m 3) (hm : 1 < m)
    (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    setOfEdge v (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) = {u, w} := by
  sorry

/-- HOL `INV_AZIM_CYCLE_EQ` (dih2k.hl:1789). -/
theorem INV_AZIM_CYCLE_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    ivsAzimCycle_p4 (EE_p4 v (E_SY_p4 (vecmatsV3_p4 l))) 0 v u = w := by
  sorry

/-- HOL `INV_AZIM_CYCLE_EQ1` (dih2k.hl:1828). -/
theorem INV_AZIM_CYCLE_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    ivsAzimCycle_p4 (EE_p4 v (E_SY_p4 (vecmatsV3_p4 l))) 0 v w = u := by
  sorry

/-- HOL `FF_OF_HYP_EQ` (dih2k.hl:1871).  Verify conclusion against
WRGCVDR `ff_of_hyp` at merge. -/
theorem FF_OF_HYP_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) (u, v) =
      (v, w) := by
  sorry

/-- HOL `AZIM_CYCLE_EQ1` (dih2k.hl:2035). -/
theorem AZIM_CYCLE_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    azimCycle_p4 (EE_p4 v (E_SY_p4 (vecmatsV3_p4 l))) 0 v w = u := by
  sorry

/-- HOL `AZIM_CYCLE_EQ` (dih2k.hl:2073). -/
theorem AZIM_CYCLE_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    azimCycle_p4 (EE_p4 v (E_SY_p4 (vecmatsV3_p4 l))) 0 v u = w := by
  sorry

/-- HOL `NN_OF_HYP_EQ1` (dih2k.hl:2110). -/
theorem NN_OF_HYP_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    (v, u) = nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) (v, w) := by
  sorry

/-- HOL `NN_OF_HYP_EQ` (dih2k.hl:2136). -/
theorem NN_OF_HYP_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) {u v w : V3} (hu : vecmatsV3_p4 l i = u)
    (hv : vecmatsV3_p4 l (finNext i) = v)
    (hw : vecmatsV3_p4 l (finNext (finNext i)) = w) :
    (v, w) = nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)) (v, u) := by
  sorry

/-- HOL `POWER_FF_OF_HYP_EQ` (dih2k.hl:1899). -/
theorem POWER_FF_OF_HYP_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) {u v : V3}
    (hu : vecmatsV3_p4 l ⟨i - 1, by omega⟩ = u)
    (hv : vecmatsV3_p4 l (finNext ⟨i - 1, by omega⟩) = v)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l ⟨0, by omega⟩,
      vecmatsV3_p4 l (finNext ⟨0, by omega⟩))) :
    (u, v) = (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[i - 1] x := by
  sorry

/-- HOL `POWER_FF_HYP_ID` (dih2k.hl:1936). -/
theorem POWER_FF_HYP_ID {m k : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hmk : m = k) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l ⟨0, by omega⟩,
      vecmatsV3_p4 l (finNext ⟨0, by omega⟩))) :
    x = (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[k] x := by
  sorry

/-- HOL `FACE_HYP_FAN_SY` (dih2k.hl:1966). -/
theorem FACE_HYP_FAN_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l ⟨0, by omega⟩,
      vecmatsV3_p4 l (finNext ⟨0, by omega⟩))) :
    F_SY_p4 (vecmatsV3_p4 l) =
      face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x := by
  sorry

/-- HOL `DART_OF_HYP_SY_EQ` (dih2k.hl:2161). -/
theorem DART_OF_HYP_SY_EQ {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)) =
      F_SY_p4 (vecmatsV3_p4 l) ∪
        (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) ''
          F_SY_p4 (vecmatsV3_p4 l) := by
  sorry

/-- HOL `IMAGE_NN_OF_HYP_F_SY` (dih2k.hl:2254). -/
theorem IMAGE_NN_OF_HYP_F_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) ''
      F_SY_p4 (vecmatsV3_p4 l) =
      (fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ := by
  sorry

/-- HOL `F_SY_INTER_IMAGE_NN_EMPTY` (dih2k.hl:2348). -/
theorem F_SY_INTER_IMAGE_NN_EMPTY {m : ℕ} (l : FinVec m 3) (hm : 2 < m)
    (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    F_SY_p4 (vecmatsV3_p4 l) ∩
      ((fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) = ∅ := by
  sorry

/-- HOL `CARD_DART_OF_HYP` (dih2k.hl:2430). -/
theorem CARD_DART_OF_HYP {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    Set.ncard (dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l))) = 2 * m := by
  sorry

/-- HOL `IMAGE_NN_OF_HYP_EQ_F_SY` (dih2k.hl:2451). -/
theorem IMAGE_NN_OF_HYP_EQ_F_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) ''
      ((fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ)
      = F_SY_p4 (vecmatsV3_p4 l) := by
  sorry

/-- HOL `DART_OF_HYP_SY_EQ1` (dih2k.hl:2500). -/
theorem DART_OF_HYP_SY_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (S : Set (V3 × V3))
    (hS : ((fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) = S) :
    dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)) =
      S ∪ (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) '' S := by
  sorry

/-- HOL `F_SY_EQ_FACE` (dih2k.hl:2516). -/
theorem F_SY_EQ_FACE {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) (x : V3 × V3)
    (hx : x = (vecmatsV3_p4 l i, vecmatsV3_p4 l (finNext i))) :
    F_SY_p4 (vecmatsV3_p4 l) =
      face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x := by
  sorry

/-- HOL `FF_OF_HYP_EQ1` (dih2k.hl:2534): `j = dimindex - i + 1` and the base
dart is `(row 2, row 1)`. -/
theorem FF_OF_HYP_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) {u v : V3}
    (hu : vecmatsV3_p4 l ⟨i - 1, by omega⟩ = u)
    (hv : vecmatsV3_p4 l (finNext ⟨i - 1, by omega⟩) = v)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l (finNext ⟨0, by omega⟩),
      vecmatsV3_p4 l ⟨0, by omega⟩)) :
    (v, u) = (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[m - i + 1] x := by
  sorry

/-- HOL `POWER_FF_OF_HYP_EQ1` (dih2k.hl:2563). -/
theorem POWER_FF_OF_HYP_EQ1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) {u v : V3}
    (hu : vecmatsV3_p4 l ⟨i - 1, by omega⟩ = u)
    (hv : vecmatsV3_p4 l (finNext ⟨i - 1, by omega⟩) = v)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l (finNext ⟨0, by omega⟩),
      vecmatsV3_p4 l ⟨0, by omega⟩)) :
    (v, u) = (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[m - i + 1] x := by
  sorry

/-- HOL `POWER_FF_HYP_ID1` (dih2k.hl:2608). -/
theorem POWER_FF_HYP_ID1 {m k : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hmk : m = k) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l (finNext ⟨0, by omega⟩),
      vecmatsV3_p4 l ⟨0, by omega⟩)) :
    x = (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[k] x := by
  sorry

/-- HOL `FACE_HYP_FAN_SY1` (dih2k.hl:2626). -/
theorem FACE_HYP_FAN_SY1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3) (hx : x = (vecmatsV3_p4 l (finNext ⟨0, by omega⟩),
      vecmatsV3_p4 l ⟨0, by omega⟩))
    (S : Set (V3 × V3))
    (hS : S = (fun i : Fin m => (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) '' Set.univ) :
    S = face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x := by
  sorry

/-- HOL `F_SY_EQ_FACE1` (dih2k.hl:2676). -/
theorem F_SY_EQ_FACE1 {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 1 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (i : Fin m) (x : V3 × V3)
    (hx : x = (vecmatsV3_p4 l (finNext i), vecmatsV3_p4 l i)) :
    F_SY_p4 (vecmatsV3_p4 l) =
      face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x := by
  sorry

/-- HOL `DART_OF_HYP_EQ_FACE_SY` (dih2k.hl:2697). -/
theorem DART_OF_HYP_EQ_FACE_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3)
    (hxd : x ∈ dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)))
    (S : Set (V3 × V3))
    (hS : S = face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x) :
    dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)) =
      S ∪ (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) '' S := by
  sorry

/-- HOL `ID_FF_OF_HYP_NOT_DARTS` (dih2k.hl:2739). -/
theorem ID_FF_OF_HYP_NOT_DARTS {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (n : ℕ) {v u : V3} (hnd : (v, u) ∉
      dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l))) :
    (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[n] (v, u) =
      (v, u) := by
  sorry

/-- HOL `CARD_FACE_SY` (dih2k.hl:2760). -/
theorem CARD_FACE_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3)
    (hxd : x ∈ dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l)))
    (S : Set (V3 × V3))
    (hS : S = face_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) x) :
    Set.ncard S = m := by
  sorry

/-- HOL `FF_OF_HYP_POWER_EQ_ID` (dih2k.hl:2802). -/
theorem FF_OF_HYP_POWER_EQ_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[m] = id := by
  sorry

/-- HOL `FF_OF_HYP_NOT_EQ_ID` (dih2k.hl:2843). -/
theorem FF_OF_HYP_NOT_EQ_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    ∀ i, 0 < i → i < m →
      (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[i] ≠ id := by
  sorry

/-- HOL `FF_OF_HYP_HAS_ORDERS` (dih2k.hl:2865). -/
theorem FF_OF_HYP_HAS_ORDERS {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    hasOrders_p4 (ffOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) m := by
  sorry

/-- HOL `NODE_SY_POWER_ID` (dih2k.hl:2881). -/
theorem NODE_SY_POWER_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3)
    (hxd : x ∈ dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l))) :
    ((hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))).nodeMap :
        V3 × V3 → V3 × V3)
      (((hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))).nodeMap :
        V3 × V3 → V3 × V3) x) = x := by
  sorry

/-- HOL `ID_NN_OF_HYP_NOT_DARTS` (dih2k.hl:2963). -/
theorem ID_NN_OF_HYP_NOT_DARTS {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (n : ℕ) {v u : V3} (hnd : (v, u) ∉
      dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l))) :
    (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[n] (v, u) =
      (v, u) := by
  sorry

/-- HOL `NN_OF_HYP_POWER_EQ_ID` (dih2k.hl:2986). -/
theorem NN_OF_HYP_POWER_EQ_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[2] = id := by
  sorry

/-- HOL `NODE_SY_NOT_ID` (dih2k.hl:3010). -/
theorem NODE_SY_NOT_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j)
    (x : V3 × V3)
    (hxd : x ∈ dartsOfHyp_p4 (E_SY_p4 (vecmatsV3_p4 l)) (V_SY_p4 (vecmatsV3_p4 l))) :
    ((hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))).nodeMap :
        V3 × V3 → V3 × V3) x ≠ x := by
  sorry

/-- HOL `NN_OF_HYP_NOT_EQ_ID` (dih2k.hl:3117). -/
theorem NN_OF_HYP_NOT_EQ_ID {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    ∀ i, 0 < i → i < 2 →
      (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))^[i] ≠ id := by
  sorry

/-- HOL `NN_OF_HYP_HAS_ORDERS` (dih2k.hl:3138). -/
theorem NN_OF_HYP_HAS_ORDERS {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    hasOrders_p4 (nnOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) 2 := by
  sorry

/-- HOL `EE_OF_HYP_HAS_ORDERS` (dih2k.hl:3150). -/
theorem EE_OF_HYP_HAS_ORDERS {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    hasOrders_p4 (eeOfHyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l))) 2 := by
  sorry

/-- HOL `DIH2K_FAN_HYP_SY` (dih2k.hl:3217): the main statement of the file. -/
theorem DIH2K_FAN_HYP_SY {m : ℕ} (l : FinVec m 3)
    (hfan : FAN 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
    (hm : 2 < m) (hinj : ∀ i j : Fin m, vecmatsV3_p4 l i = vecmatsV3_p4 l j → i = j) :
    dih2k_p4 (hyp_p4 0 (V_SY_p4 (vecmatsV3_p4 l)) (E_SY_p4 (vecmatsV3_p4 l)))
      (Set.ncard (F_SY_p4 (vecmatsV3_p4 l))) := by
  sorry


/-- HOL `COMPACT_BALL_ANNULUS_MATVEC` (dih2k.hl:606). -/
theorem COMPACT_BALL_ANNULUS_MATVEC {m : ℕ} :
    IsCompact {x : FinVec m 3 | ∀ j : Fin m,
      (WithLp.toLp 2 (vecmats_p4 x j) : V3) ∈ ballAnnulus} := by
  have hrowsC : IsClosed {w : Fin 3 → ℝ | (WithLp.toLp 2 w : V3) ∈ ballAnnulus} :=
    IsClosed.preimage continuous_toLpV3 CLOSED_BALL_ANNULUS
  have hrowsB : Bornology.IsBounded {w : Fin 3 → ℝ | (WithLp.toLp 2 w : V3) ∈ ballAnnulus} := by
    refine Metric.isBounded_iff.mpr ⟨4 * h0, ?_⟩
    intro u hu v hv
    have h0p : (0:ℝ) < 4 * h0 := by
      have hh : h0 = 1.26 := rfl
      norm_num [hh]
    rw [dist_pi_le_iff (by linarith)]
    intro k
    have h2u : ‖(WithLp.toLp 2 u : V3)‖ ≤ 2 * h0 := (ballAnnulus_norm_bounds hu).2
    have h2v : ‖(WithLp.toLp 2 v : V3)‖ ≤ 2 * h0 := (ballAnnulus_norm_bounds hv).2
    have hu1 : |(WithLp.ofLp (WithLp.toLp 2 u) : Fin 3 → ℝ) k| ≤ ‖(WithLp.toLp 2 u : V3)‖ := by
      have hp := PiLp.norm_apply_le (x := WithLp.toLp 2 u) (i := k)
      rwa [show (WithLp.ofLp (WithLp.toLp 2 u) : Fin 3 → ℝ) k = u k from rfl] at hp
    have hv1 : |(WithLp.ofLp (WithLp.toLp 2 v) : Fin 3 → ℝ) k| ≤ ‖(WithLp.toLp 2 v : V3)‖ := by
      have hp := PiLp.norm_apply_le (x := WithLp.toLp 2 v) (i := k)
      rwa [show (WithLp.ofLp (WithLp.toLp 2 v) : Fin 3 → ℝ) k = v k from rfl] at hp
    have e : dist (u k) (v k) = |(WithLp.ofLp (WithLp.toLp 2 u) : Fin 3 → ℝ) k -
        (WithLp.ofLp (WithLp.toLp 2 v) : Fin 3 → ℝ) k| := rfl
    rw [e]
    have htri := abs_sub (WithLp.ofLp (WithLp.toLp 2 u) k) (WithLp.ofLp (WithLp.toLp 2 v) k)
    linarith
  have hrowsK : IsCompact {w : Fin 3 → ℝ | (WithLp.toLp 2 w : V3) ∈ ballAnnulus} :=
    Metric.isCompact_of_isClosed_isBounded hrowsC hrowsB
  exact COMPACT_MATVEC
    (fun _ => {w : Fin 3 → ℝ | (WithLp.toLp 2 w : V3) ∈ ballAnnulus})
    (fun _ => hrowsK)

/-- HOL `ABS_LT_EPSI` (dih2k.hl:1494). -/
theorem ABS_LT_EPSI (a b : ℝ) (h : |a - b| < b / 4) (hb : 0 < b) : 0 < a := by
  have hh := abs_lt.mp h
  linarith

/-- HOL `LIM_SUBSEQUENCE1` (dih2k.hl:1502). -/
theorem LIM_SUBSEQUENCE1 {α : Type*} [TopologicalSpace α] (s : ℕ → α) (l : α)
    (r : ℕ → ℕ) (hs : Filter.Tendsto s Filter.atTop (nhds l)) (hr : ∀ n, n ≤ r n) :
    Filter.Tendsto (s ∘ r) Filter.atTop (nhds l) := by
  rw [Filter.tendsto_iff_forall_eventually_mem]
  intro U hU
  have hmem : Filter.Eventually (fun n => s n ∈ U) Filter.atTop := hs.eventually hU
  rw [Filter.eventually_atTop] at hmem
  obtain ⟨N, hmem⟩ := hmem
  rw [Filter.eventually_atTop]
  exact ⟨N, fun n hn => hmem (r n) (le_trans hn (hr n))⟩

/-- HOL `SEQUENTIALLY_EQ_2POINT` (dih2k.hl:1508). -/
theorem SEQUENTIALLY_EQ_2POINT {α : Type*} (h f g : ℕ → α)
    (hh : ∀ n, h n = f n ∨ h n = g n) :
    (∃ r : ℕ → ℕ, ∀ n, n ≤ r n ∧ h (r n) = f (r n)) ∨
      (∃ r : ℕ → ℕ, ∀ n, n ≤ r n ∧ h (r n) = g (r n)) := by
  by_cases hA : {n : ℕ | h n = f n}.Infinite
  · left
    have hinf : ∀ n, ∃ m, n ≤ m ∧ h m = f m := by
      intro n
      obtain ⟨m, hmf, hm⟩ := hA.exists_gt n
      exact ⟨m, le_of_lt hm, hmf⟩
    choose r hr using hinf
    exact ⟨r, hr⟩
  by_cases hB : {n : ℕ | h n = g n}.Infinite
  · right
    have hinf : ∀ n, ∃ m, n ≤ m ∧ h m = g m := by
      intro n
      obtain ⟨m, hmg, hm⟩ := hB.exists_gt n
      exact ⟨m, le_of_lt hm, hmg⟩
    choose r hr using hinf
    exact ⟨r, hr⟩
  exfalso
  have huniv : (Set.univ : Set ℕ) = {n | h n = f n} ∪ {n | h n = g n} := by
    ext n; simp [hh n]
  have : (Set.univ : Set ℕ).Finite := by
    rw [huniv]
    exact Set.Finite.union (Set.not_infinite.mp hA) (Set.not_infinite.mp hB)
  exact Set.infinite_univ.not_finite this

/-- HOL `LIM_IN_SET` (dih2k.hl:1529). -/
theorem LIM_IN_SET {f g h : ℕ → V3} {a b c : V3}
    (hf : Filter.Tendsto f Filter.atTop (nhds a))
    (hg : Filter.Tendsto g Filter.atTop (nhds b))
    (hc : Filter.Tendsto h Filter.atTop (nhds c))
    (hh : ∀ n, h n = f n ∨ h n = g n) : c = a ∨ c = b := by
  obtain ⟨r, hr⟩ | ⟨r, hr⟩ := SEQUENTIALLY_EQ_2POINT h f g hh
  · left
    have h1 := LIM_SUBSEQUENCE1 h c r hc (fun n => (hr n).1)
    have h2 := LIM_SUBSEQUENCE1 f a r hf (fun n => (hr n).1)
    have heqfun : (h ∘ r) = (f ∘ r) := funext fun n => (hr n).2
    rw [heqfun] at h1
    exact tendsto_nhds_unique h1 h2
  · right
    have h1 := LIM_SUBSEQUENCE1 h c r hc (fun n => (hr n).1)
    have h2 := LIM_SUBSEQUENCE1 g b r hg (fun n => (hr n).1)
    have heqfun : (h ∘ r) = (g ∘ r) := funext fun n => (hr n).2
    rw [heqfun] at h1
    exact tendsto_nhds_unique h1 h2

end Kepler.Text
