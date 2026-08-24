/-
  Phase 3 pilot: kernel-checkable certificates for sparse rational linear
  programs (the Lean side of the "untrusted solver → certificate → verified
  checker" pipeline for the Flyspeck LP bounds; see PLAN.md §2 and
  DECISIONS.md: `native_decide` is forbidden here, all certificate checks
  are re-done by the kernel via `decide`).

  LP form:  max cᵀx  s.t.  A·x ≤ b, x ≥ 0,  semantics over `Rat`
  (so the soundness theorems quantify over *rational* feasible points `x`).

  A **dual certificate** claims `max ≤ γ`. The checker verifies `y ≥ 0`,
  `Aᵀy ≥ c` (column-wise over `List.range numVars`) and `bᵀy ≤ γ`;
  soundness (`checkDual_sound`) is weak duality: `cᵀx ≤ bᵀy ≤ γ` for every
  primal-feasible `x`. An optional **primal certificate** `x` is checked
  for feasibility by `checkPrimal`.

  ## Design decisions

  - *Integerized checking layer (key decision).* The kernel **cannot**
    reduce `Rat` arithmetic at all: `Rat.add`/`Rat.normalize` are
    `@[extern]`-backed, so even `1 + 1 = 2 : Rat` fails `by decide`
    (verified empirically on toolchain v4.32.2; this is also why
    `Kepler.LP.HelloChecker` uses `norm_num` instead). Therefore all
    certificate *data and checking* live over `Int` (`SparseI`, `dotLI`,
    `colDotI`), where kernel arithmetic is `Nat`-backed and fast, while
    the *semantics and the weak-duality proof* live over `Rat` via the
    `Int.cast` ordered-ring-homomorphism bridge (`dotRat_eq_sum`,
    `dotLI_cast`, `colDotI_cast`, `Int.cast_le`/`Int.cast_nonneg`).
    This is exactly the standard VIPR workflow: rational solver output is
    cleared of denominators before certification.
  - *Explicit denominator `D`.* A rational dual certificate `(y, γ)` is
    presented as integers `(Y, D, G)` with `y = Y/D`, `γ = G/D` (assuming
    integral LP data, as produced by the Flyspeck LP generation pipeline;
    rational data would be scaled row-wise first — future work). The
    checker verifies `Y ≥ 0`, `AᵀY ≥ D·c`, `bᵀY ≤ G`; soundness concludes
    `cᵀx ≤ G/D`. E.g. the tight dual `y = (1/3,1/3)`, `γ = 3` of the pilot
    LP is checked as `Y = (1,1)`, `D = 3`, `G = 9`.
  - *Sparse representation.* Rows and the objective are `List (ℕ × Int)`
    (column index, coefficient); only the support is scanned. **Duplicate
    indices are allowed and summed semantically** (`SparseI.get`), which
    avoids `Nodup` side conditions in every lemma.
  - *Weak duality proof idea* (the only math here):
      D·cᵀx = Σⱼ (D·cⱼ)xⱼ ≤ Σⱼ (AᵀY)ⱼxⱼ          [AᵀY ≥ D·c, x ≥ 0]
            = Σᵢ Yᵢ (Σⱼ Aᵢⱼ xⱼ)                  [Finset.sum_comm + factor]
            = Σᵢ Yᵢ (A·x)ᵢ ≤ Σᵢ Yᵢ bᵢ = bᵀY ≤ G  [A·x ≤ b, Y ≥ 0],
    then divide by `D > 0` (`le_div_iff₀`).
  - *Correction to the pilot example:* for max x+y with 2x+y ≤ 4, x+2y ≤ 5,
    the dual `y = (1,1)` gives `bᵀy = 9` (valid but loose — kept below as
    the `D = 1` certificate); the tight certificate is `y = (1/3,1/3)`,
    `γ = 3`, realized in integerized form as `(Y, D, G) = ((1,1), 3, 9)`.

  ## Scaling considerations (kernel `decide` on `Int`)

  `Int` ops reduce in the kernel via `Nat` (GMP-accelerated literals), and
  the checker is a structural fold over the supports, so `decide` cost is
  linear in the total number of stored coefficients — fine for the pilot
  cases below. For ~10⁵-row instances the plan is:
  1. *Sharding*: emit each column constraint (`AᵀY ≥ D·c`), each row
     evaluation (`A·x ≤ b`) and the final bound as independent `decide`
     theorems in shard files (the `Kepler.Graphs.CertShards` pattern),
     then assemble with `checkDual_sound`/`checkPrimal_sound`.
  2. Keep certificates `Int`-valued (this file) — no `Rat` normalization
     anywhere in the checked data path.
  3. Solver hookup: an untrusted script parses the exact rational solver
     output (SoPlex/QSopt_ex VIPR), clears denominators, and prints
     `(numVars, c, A, Y, D, G)` in this sparse `(index, coeff)` format;
     the Lean side only re-checks.

  Downstream wiring: `Kepler.lean` (import), `docs/module-map.md`.
-/
import Mathlib

namespace Kepler.LP

/-! ## Sparse integer vectors (the checked data layer) -/

/-- Sparse vector: a list of `(column index, coefficient)` pairs.
Duplicate indices are allowed and are summed by the semantics `SparseI.get`. -/
abbrev SparseI := List (ℕ × Int)

/-- Semantics of a sparse vector at column `j`: the sum of all coefficients
with index `j` (0 if absent). -/
def SparseI.get (s : SparseI) (j : ℕ) : Int :=
  s.foldr (fun p acc => if p.1 = j then p.2 + acc else acc) 0

/-- Executable dot product of a sparse vector with a dense integer vector. -/
def SparseI.dotI (s : SparseI) (x : List Int) : Int :=
  s.foldr (fun p acc => p.2 * x.getD p.1 0 + acc) 0

/-- Rational-valued dot product of a sparse (integer) vector with a dense
rational vector: the semantic objective/row-evaluation function. -/
def SparseI.dotRat (s : SparseI) (x : List Rat) : Rat :=
  s.foldr (fun p acc => (p.2 : Rat) * x.getD p.1 0 + acc) 0

/-- Well-formedness check: every index is a valid column. -/
def SparseI.wf (s : SparseI) (n : ℕ) : Bool :=
  s.all (fun p => decide (p.1 < n))

/-- The canonical cast of an integer vector to a rational vector. -/
def castL (x : List Int) : List Rat := x.map Int.cast

/-- Boolean `≤` on `Int` with its soundness direction. -/
def rleI (a b : Int) : Bool := decide (a ≤ b)

theorem rleI_true {a b : Int} (h : rleI a b = true) : a ≤ b := of_decide_eq_true h

/-- `getD i` of a list is a member when `i` is in range. -/
theorem getD_mem_of_lt {α : Type*} [Inhabited α] {l : List α} {i : ℕ}
    (h : i < l.length) : l.getD i default ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih (Nat.succ_lt_succ_iff.mp h))

/-- `getD` commutes with `List.map` when `f` maps the default to the default. -/
theorem getD_map' {α β : Type*} (f : α → β) (dα : α) (dβ : β)
    (hf : f dα = dβ) (l : List α) (i : ℕ) :
    (l.map f).getD i dβ = f (l.getD i dα) := by
  induction l generalizing i with
  | nil => cases i <;> exact hf.symm
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i

/-- A single spike sums to its value: the key point-sum identity. -/
theorem sum_ite_mul_getD (n k : ℕ) (b : Rat) (x : List Rat) (hk : k < n) :
    ∑ j ∈ Finset.range n, (if j = k then b else 0) * x.getD j 0 = b * x.getD k 0 := by
  have h : ∀ j ∈ Finset.range n, (if j = k then b else 0) * x.getD j 0 =
      if j = k then b * x.getD j 0 else 0 := fun j _ => by
    by_cases hjk : j = k <;> simp [hjk]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)]

/-- Bridge: the executable sparse dot product equals the dense `Finset`
sum, provided all indices are in range. -/
theorem SparseI.dotRat_eq_sum (s : SparseI) (x : List Rat)
    (hwf : ∀ p ∈ s, p.1 < x.length) :
    SparseI.dotRat s x = ∑ j ∈ Finset.range x.length, (s.get j : Rat) * x.getD j 0 := by
  induction s with
  | nil => simp [SparseI.dotRat, SparseI.get]
  | cons p s ih =>
    obtain ⟨k, b⟩ := p
    have hk : k < x.length := hwf (k, b) List.mem_cons_self
    have hwf' : ∀ q ∈ s, q.1 < x.length := fun q hq => hwf q (List.mem_cons_of_mem _ hq)
    have hget : ∀ j, ((SparseI.get ((k, b) :: s) j : Int) : Rat) =
        (if j = k then (b : Rat) else 0) + (SparseI.get s j : Rat) := by
      intro j
      by_cases hjk : j = k
      · simp [SparseI.get, List.foldr_cons, hjk, Int.cast_add]
      · have hkj : k ≠ j := fun h => hjk h.symm
        simp [SparseI.get, List.foldr_cons, hjk, hkj]
    show (b : Rat) * x.getD k 0 + SparseI.dotRat s x = _
    rw [ih hwf']
    have h2 : ∀ j ∈ Finset.range x.length,
        (SparseI.get ((k, b) :: s) j : Rat) * x.getD j 0 =
          (if j = k then (b : Rat) else 0) * x.getD j 0 +
            (SparseI.get s j : Rat) * x.getD j 0 := by
      intro j _
      rw [hget j, add_mul]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, sum_ite_mul_getD _ k (b : Rat) x hk]

/-! ## Dense dot product over `Int` and the LP data -/

/-- Dense dot product over `Int` (truncating; used only with equal lengths). -/
def dotLI : List Int → List Int → Int
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => a * b + dotLI as bs

/-- Casting `dotLI` to `Rat` yields the dense `Finset` sum of casts. -/
theorem dotLI_cast (u v : List Int) (h : u.length = v.length) :
    (dotLI u v : Rat) =
      ∑ i ∈ Finset.range v.length, (u.getD i 0 : Rat) * (v.getD i 0 : Rat) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [dotLI]
    | cons b bs => simp at h
  | cons a as ih =>
    cases v with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      show ((a * b + dotLI as bs : Int) : Rat) = _
      rw [Int.cast_add, Int.cast_mul, ih bs h', List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

/-- One constraint row: `coeffs · x ≤ rhs`. -/
structure RowI where
  coeffs : SparseI
  rhs : Int
deriving Repr

instance : Inhabited RowI := ⟨⟨[], 0⟩⟩

/-- Rational left-hand side of a row evaluated at a rational `x`. -/
def RowI.evalRat (r : RowI) (x : List Rat) : Rat := r.coeffs.dotRat x

/-- A sparse LP with integral data: `max cᵀx` subject to `A·x ≤ b`, `x ≥ 0`
(over the rationals), with `numVars` variables and one `RowI` per constraint. -/
structure LPI where
  numVars : ℕ
  c : SparseI
  A : List RowI
deriving Repr

/-- Column `j` of the constraint matrix, as a dense vector over the rows. -/
def colVecI (A : List RowI) (j : ℕ) : List Int := A.map (fun r => r.coeffs.get j)

/-- Column `j` of `AᵀY`: `(AᵀY)ⱼ = Σᵢ Yᵢ · Aᵢⱼ`. -/
def colDotI (A : List RowI) (Y : List Int) (j : ℕ) : Int := dotLI (colVecI A j) Y

/-- Casting `colDotI` to `Rat` yields the row-indexed `Finset` sum. -/
theorem colDotI_cast (A : List RowI) (Y : List Int) (j : ℕ) (h : Y.length = A.length) :
    (colDotI A Y j : Rat) =
      ∑ i ∈ Finset.range Y.length,
        ((A.getD i default).coeffs.get j : Rat) * (Y.getD i 0 : Rat) := by
  rw [colDotI, colVecI, dotLI_cast _ _ (by simp [h])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_map' (f := fun r : RowI => r.coeffs.get j) (dα := default) (dβ := 0) rfl A i]

/-! ## The checkers -/

/-- Dual certificate checker for the integerized certificate `(Y, D, G)`
representing the rational dual `y = Y/D` and claimed bound `γ = G/D`:
verifies `D > 0`, sizes/well-formedness, `Y ≥ 0`, `AᵀY ≥ D·c` column-wise,
and `bᵀY ≤ G`. -/
def checkDual (lp : LPI) (Y : List Int) (D : ℕ) (G : Int) : Bool :=
  decide (0 < D) &&
  decide (Y.length = lp.A.length) &&
  lp.c.wf lp.numVars &&
  lp.A.all (fun r => r.coeffs.wf lp.numVars) &&
  Y.all (fun v => rleI 0 v) &&
  (List.range lp.numVars).all (fun j => rleI ((D : Int) * lp.c.get j) (colDotI lp.A Y j)) &&
  rleI (dotLI (lp.A.map RowI.rhs) Y) G

/-- Primal certificate checker: verifies `x ≥ 0` and `A·x ≤ b` (all `Int`). -/
def checkPrimal (lp : LPI) (x : List Int) : Bool :=
  decide (x.length = lp.numVars) &&
  x.all (fun v => rleI 0 v) &&
  lp.A.all (fun r => rleI (r.coeffs.dotI x) r.rhs)

/-- **Soundness of the dual checker (weak duality).**
A passing integerized certificate `(Y, D, G)` bounds the objective value of
every rational primal-feasible point by `G/D`. -/
theorem checkDual_sound (lp : LPI) (Y : List Int) (D : ℕ) (G : Int)
    (h : checkDual lp Y D G = true) (x : List Rat)
    (hxlen : x.length = lp.numVars)
    (hx0 : ∀ j < lp.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ lp.A, r.evalRat x ≤ (r.rhs : Rat)) :
    lp.c.dotRat x ≤ (G : Rat) / (D : Rat) := by
  simp only [checkDual, Bool.and_eq_true, List.all_eq_true, SparseI.wf] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hylen⟩, hcwf⟩, hAwf⟩, hY0⟩, hcol⟩, hb⟩ := h
  have hD' : 0 < D := of_decide_eq_true hD
  have hy_len : Y.length = lp.A.length := of_decide_eq_true hylen
  have hY_nonneg : ∀ v ∈ Y, 0 ≤ v := fun v hv => rleI_true (hY0 v hv)
  have hcolI : ∀ j < lp.numVars, (D : Int) * lp.c.get j ≤ colDotI lp.A Y j :=
    fun j hj => rleI_true (hcol j (List.mem_range.mpr hj))
  have hbI : dotLI (lp.A.map RowI.rhs) Y ≤ G := rleI_true hb
  have hc_wf : ∀ p ∈ lp.c, p.1 < x.length := fun p hp => by
    have h2 := of_decide_eq_true (hcwf p hp); rwa [← hxlen] at h2
  have hA_wf : ∀ r ∈ lp.A, ∀ p ∈ r.coeffs, p.1 < x.length := fun r hr p hp => by
    have h2 := of_decide_eq_true (hAwf r hr p hp); rwa [← hxlen] at h2
  have hcol_le : ∀ j < x.length,
      (((D : Int) * lp.c.get j : Int) : Rat) ≤ (colDotI lp.A Y j : Rat) :=
    fun j hj => Int.cast_le.mpr (hcolI j (by rwa [hxlen] at hj))
  have hx0' : ∀ j < x.length, 0 ≤ x.getD j 0 :=
    fun j hj => hx0 j (by rwa [hxlen] at hj)
  have key : (D : Rat) * lp.c.dotRat x ≤ (G : Rat) := by
    calc (D : Rat) * lp.c.dotRat x
        = ∑ j ∈ Finset.range x.length,
            (((D : Int) * lp.c.get j : Int) : Rat) * x.getD j 0 := by
          rw [SparseI.dotRat_eq_sum lp.c x hc_wf, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring
      _ ≤ ∑ j ∈ Finset.range x.length, (colDotI lp.A Y j : Rat) * x.getD j 0 := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul_of_nonneg_right (hcol_le j (Finset.mem_range.mp hj))
            (hx0' j (Finset.mem_range.mp hj))
      _ = ∑ j ∈ Finset.range x.length,
            (∑ i ∈ Finset.range Y.length,
              ((lp.A.getD i default).coeffs.get j : Rat) * (Y.getD i 0 : Rat)) *
              x.getD j 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [colDotI_cast lp.A Y j hy_len]
      _ = ∑ j ∈ Finset.range x.length, ∑ i ∈ Finset.range Y.length,
            ((lp.A.getD i default).coeffs.get j : Rat) * (Y.getD i 0 : Rat) *
              x.getD j 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ i ∈ Finset.range Y.length, ∑ j ∈ Finset.range x.length,
            ((lp.A.getD i default).coeffs.get j : Rat) * (Y.getD i 0 : Rat) *
              x.getD j 0 :=
          Finset.sum_comm
      _ = ∑ i ∈ Finset.range Y.length, (Y.getD i 0 : Rat) *
            ∑ j ∈ Finset.range x.length,
              ((lp.A.getD i default).coeffs.get j : Rat) * x.getD j 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ i ∈ Finset.range Y.length,
            (Y.getD i 0 : Rat) * (lp.A.getD i default).evalRat x := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : i < lp.A.length := by
            rw [← hy_len]; exact Finset.mem_range.mp hi
          rw [RowI.evalRat, SparseI.dotRat_eq_sum _ _ (hA_wf _ (getD_mem_of_lt hi'))]
      _ ≤ ∑ i ∈ Finset.range Y.length,
            (Y.getD i 0 : Rat) * ((lp.A.getD i default).rhs : Rat) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i < lp.A.length := by
            rw [← hy_len]; exact Finset.mem_range.mp hi
          exact mul_le_mul_of_nonneg_left (hxA _ (getD_mem_of_lt hi'))
            (Int.cast_nonneg (hY_nonneg _ (getD_mem_of_lt (Finset.mem_range.mp hi))))
      _ = (dotLI (lp.A.map RowI.rhs) Y : Rat) := by
          rw [dotLI_cast _ _ (by simp [hy_len])]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [getD_map' (f := RowI.rhs) (dα := default) (dβ := 0) rfl lp.A i]
          exact mul_comm _ _
      _ ≤ (G : Rat) := Int.cast_le.mpr hbI
  have hDpos : (0 : Rat) < (D : Rat) := Nat.cast_pos.mpr hD'
  rw [le_div_iff₀ hDpos]
  rwa [mul_comm] at key

/-- Evaluating a sparse integer dot product on the cast of an integer
vector commutes with the cast. -/
theorem SparseI.dotRat_map_cast (s : SparseI) (x : List Int) :
    SparseI.dotRat s (x.map Int.cast) = (SparseI.dotI s x : Rat) := by
  induction s with
  | nil => simp [SparseI.dotRat, SparseI.dotI, Int.cast_zero]
  | cons p s ih =>
    obtain ⟨k, b⟩ := p
    show (b : Rat) * (x.map Int.cast).getD k 0 + SparseI.dotRat s (x.map Int.cast) =
      ((b * x.getD k 0 + SparseI.dotI s x : Int) : Rat)
    rw [getD_map' (f := Int.cast) (dα := 0) (dβ := 0) Int.cast_zero x k, ih,
      Int.cast_add, Int.cast_mul]

/-- **Soundness of the primal checker**: the cast of a passing integer
primal certificate is rationally feasible. -/
theorem checkPrimal_sound (lp : LPI) (x : List Int) (h : checkPrimal lp x = true) :
    (castL x).length = lp.numVars ∧
      (∀ j < lp.numVars, 0 ≤ (castL x).getD j 0) ∧
      ∀ r ∈ lp.A, r.evalRat (castL x) ≤ (r.rhs : Rat) := by
  simp only [checkPrimal, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hxlen, hx0⟩, hxA⟩ := h
  have hxlen' : x.length = lp.numVars := of_decide_eq_true hxlen
  refine ⟨by simp [castL, hxlen'], fun j hj => ?_, fun r hr => ?_⟩
  · simp only [castL]
    rw [getD_map' (f := Int.cast) (dα := 0) (dβ := 0) Int.cast_zero x j]
    exact Int.cast_nonneg
      (of_decide_eq_true (hx0 _ (getD_mem_of_lt (by rwa [← hxlen'] at hj))))
  · rw [RowI.evalRat]
    simp only [castL]
    rw [SparseI.dotRat_map_cast]
    exact Int.cast_le.mpr (of_decide_eq_true (hxA r hr))

/-! ## Small pilot cases (kernel `decide` only, no `native_decide`)

### Case 1: max x+y s.t. 2x+y ≤ 4, x+2y ≤ 5 (optimum 3)

The tight rational dual is `y = (1/3, 1/3)`, `γ = 3`; its integerized form
is `Y = (1,1)`, `D = 3`, `G = 9` (checker: `AᵀY = (3,3) ≥ 3c`, `bᵀY = 9 ≤ G`).
The loose dual `y = (1,1)`, `γ = 9` is the `D = 1` certificate with the same
`Y`. The primal point `x = (1,2)` attains the optimum. -/

def exLP : LPI where
  numVars := 2
  c := [(0, 1), (1, 1)]
  A := [⟨[(0, 2), (1, 1)], 4⟩, ⟨[(0, 1), (1, 2)], 5⟩]

/-- The kernel re-checks the tight integerized dual certificate. -/
theorem exDual_check : checkDual exLP [1, 1] 3 9 = true := by decide

/-- End-to-end: every rational-feasible point of `exLP` has objective ≤ 3. -/
theorem exLP_bound (x : List Rat) (hxlen : x.length = exLP.numVars)
    (hx0 : ∀ j < exLP.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ exLP.A, r.evalRat x ≤ (r.rhs : Rat)) :
    exLP.c.dotRat x ≤ 3 := by
  have h := checkDual_sound exLP [1, 1] 3 9 exDual_check x hxlen hx0 hxA
  rwa [show ((9 : Int) : Rat) / ((3 : ℕ) : Rat) = 3 by norm_num] at h

/-- The loose certificate `y = (1,1)`, `γ = 9` (i.e. `D = 1`) is accepted. -/
theorem exDual_loose_check : checkDual exLP [1, 1] 1 9 = true := by decide

/-- A claimed bound below the dual value is rejected (`bᵀ(1,1) = 9 > 8`). -/
theorem exDual_bad_bound : checkDual exLP [1, 1] 3 8 = false := by decide

/-- A dual violating `AᵀY ≥ D·c` is rejected (column 1: `1 < 3`). -/
theorem exDual_bad_dual : checkDual exLP [1, 0] 3 9 = false := by decide

/-- A dual with a negative component is rejected. -/
theorem exDual_neg_check : checkDual exLP [1, -1] 3 9 = false := by decide

/-- `D = 0` is rejected (the certificate must carry a positive denominator). -/
theorem exDual_zero_D : checkDual exLP [1, 1] 0 9 = false := by decide

/-- The primal certificate `x = (1,2)` is feasible. -/
theorem exPrimal_check : checkPrimal exLP [1, 2] = true := by decide

/-- Its objective value is 3, matching the dual bound (strong duality). -/
theorem exPrimal_obj : exLP.c.dotI [1, 2] = 3 := by decide

/-- Feasibility of the cast of `x = (1,2)`, extracted from the checker. -/
theorem exLP_feasible :
    (castL [1, 2]).length = exLP.numVars ∧
      (∀ j < exLP.numVars, 0 ≤ (castL [1, 2]).getD j 0) ∧
      ∀ r ∈ exLP.A, r.evalRat (castL [1, 2]) ≤ (r.rhs : Rat) :=
  checkPrimal_sound exLP [1, 2] exPrimal_check

/-- The primal certificate attains the dual bound: objective value 3. -/
theorem exPrimal_attains : exLP.c.dotRat (castL [1, 2]) = 3 := by
  simp only [castL]
  rw [SparseI.dotRat_map_cast, exPrimal_obj]
  norm_num

/-! ### Case 2: max x s.t. x ≤ 5 (one variable, one constraint) -/

def exLP1 : LPI where
  numVars := 1
  c := [(0, 1)]
  A := [⟨[(0, 1)], 5⟩]

theorem exLP1_dual_check : checkDual exLP1 [1] 1 5 = true := by decide

theorem exLP1_bound (x : List Rat) (hxlen : x.length = exLP1.numVars)
    (hx0 : ∀ j < exLP1.numVars, 0 ≤ x.getD j 0)
    (hxA : ∀ r ∈ exLP1.A, r.evalRat x ≤ (r.rhs : Rat)) :
    exLP1.c.dotRat x ≤ 5 := by
  have h := checkDual_sound exLP1 [1] 1 5 exLP1_dual_check x hxlen hx0 hxA
  rwa [show ((5 : Int) : Rat) / ((1 : ℕ) : Rat) = 5 by norm_num] at h

end Kepler.LP
