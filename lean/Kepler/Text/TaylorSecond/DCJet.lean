/-
Kepler.Text.TaylorSecond.DCJet — lane `wt1-emission-pilot-w1`, M2 item 2
(2026-11-25).

The **value + first-partial DC jet**: the dyadic counterpart of the
`value`/`first` channels of `WholeBoxJet` (`Bounds.lean:17`), with the Hessian
channel dropped (the T2 terminal never reads it).

A jet is the plain data pair `⟨value, part⟩` (`part : Fin 3 → DC` holds the
three coordinate partials); the semantic content is a separate predicate
`JetMem J f D`:

  * `J.value` brackets `f` on `D`,
  * `J.part i` brackets `partial1 i f` on `D`,
  * `f` is `C¹` on `D` (what the chain rules `partial1_add/sub/mul/comp` need).

Every op is defined at the DC level (`value` = the landed DC op, partials = the
forward-AD formula) and comes with one `_mem` lemma; the `matan` node is an arm
(`dMatan9` / `dMatanWp` / `dMatanU9` / `dMatanMir`) whose partial slot is the
landed `dMatanD`.  The mirror arm's inner `matan (1/r)` is produced by
`dMatanTight`: the tight arms (`dMatanWp` for `1/r ≤ 4`, else `dMatanU9`)
applied to `dInv A ∋ 1/r` — the DC counterpart of the landed QInterval
emission's `PMir`/`PWp` pairing (`W1aFJet.lean:1332`, whose inner fact is
`M.mem (matan (1/t))`, i.e. the argument is `1/t`, not `1/√t`).

**Layout note.**  The work order sketched the fields as `value f4 f5 f6`; they
are stored here as `value` plus `part : Fin 3 → DC`.  Same data, but every op's
partial slot is then *definitionally* a function of the children's slots (no
`![f4,f5,f6]`/`fin_cases` projection lemmas — those blew the whnf heartbeat
budget in an isolated probe even for a single `fin_cases i <;> rfl`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.DCTaylor2
import Kepler.Text.TaylorSecond.Coordinate
import Kepler.Text.TaylorSecond.Arithmetic
import Kepler.Text.TaylorSecond.Matan
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxHeartbeats 8000000

namespace Kepler.Text.TaylorSecond

open DCKit

/-- Value + first-partial DC jet data (no Hessian channel). -/
structure DCJet where
  value : DC
  part : Fin 3 → DC

namespace DCJetKit

open DCMatan

/-- `J` brackets `f` and its coordinate partials on `D`. -/
def JetMem (J : DCJet) (f : (Fin 3 → ℝ) → ℝ) (D : Set (Fin 3 → ℝ)) : Prop :=
  (∀ x ∈ D, ContDiffAt ℝ 1 f x) ∧
    (∀ x ∈ D, J.value.mem (f x)) ∧
      (∀ x ∈ D, ∀ i, (J.part i).mem (partial1 i f x))

/-- `C² ⟹ C¹` at a point, with the `n` numeral type fixed by the goal (writing
the ascription by hand picks the wrong `WithTop` instance). -/
theorem c1_of_c2 {f : ℝ → ℝ} {t : ℝ} (h : ContDiffAt ℝ 2 f t) : ContDiffAt ℝ 1 f t :=
  h.of_le (by decide)

#print axioms c1_of_c2

/-! ## Coordinate partial of a projection (local copy of `W1aFJet`'s lemma) -/

theorem partial1_coord (i j : Fin 3) (x : Fin 3 → ℝ) :
    partial1 j (fun y : Fin 3 → ℝ => y i) x = if j = i then 1 else 0 := by
  have hC1 : ContDiffAt ℝ 1 (fun y : Fin 3 → ℝ => y i) x := by fun_prop
  rw [partial1_eq_deriv_update hC1 j]
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

#print axioms partial1_coord

/-! ## §1 Constants and coordinates -/

/-- Integer constant jet. -/
def const (q : ℤ) : DCJet := ⟨dInt q, fun _ => dInt 0⟩

theorem const_mem (q : ℤ) (D : Set (Fin 3 → ℝ)) :
    JetMem (const q) (fun _ : Fin 3 → ℝ => (q : ℝ)) D := by
  refine ⟨fun _ _ => contDiffAt_const, fun _ _ => dInt_mem q, fun x _ i => ?_⟩
  have h0 : partial1 i (fun _ : Fin 3 → ℝ => (q : ℝ)) x = 0 := by
    simp [partial1]
  rw [h0]
  show (dInt 0).mem (0 : ℝ)
  simpa using dInt_mem 0

/-- Coordinate projection jet: `value = I ∋ x i`, partial `1` in slot `i`. -/
def coord (i : Fin 3) (I : DC) : DCJet :=
  ⟨I, fun j => dInt (if j = i then 1 else 0)⟩

theorem coord_mem (i : Fin 3) (I : DC) (D : Set (Fin 3 → ℝ))
    (hmem : ∀ x ∈ D, I.mem (x i)) :
    JetMem (coord i I) (fun x : Fin 3 → ℝ => x i) D := by
  refine ⟨fun x _ => ?_, hmem, fun x _ j => ?_⟩
  · fun_prop
  · rw [partial1_coord i j x]
    show (dInt (if j = i then 1 else 0)).mem (if j = i then (1 : ℝ) else 0)
    by_cases h : j = i
    · rw [if_pos h, if_pos h]
      simpa using dInt_mem 1
    · rw [if_neg h, if_neg h]
      simpa using dInt_mem 0

#print axioms const_mem
#print axioms coord_mem

/-! ## §2 Additive structure -/

def add (J K : DCJet) : DCJet :=
  ⟨dAdd J.value K.value, fun i => dAdd (J.part i) (K.part i)⟩

theorem add_mem {J K : DCJet} {f g : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hK : JetMem K g D) :
    JetMem (add J K) (fun x => f x + g x) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  obtain ⟨k1, k2, k3⟩ := hK
  refine ⟨fun x hx => (h1 x hx).add (k1 x hx),
    fun x hx => dAdd_mem (h2 x hx) (k2 x hx), fun x hx i => ?_⟩
  rw [partial1_add (h1 x hx) (k1 x hx) i]
  exact dAdd_mem (h3 x hx i) (k3 x hx i)

def neg (J : DCJet) : DCJet :=
  ⟨dNeg J.value, fun i => dNeg (J.part i)⟩

theorem neg_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) :
    JetMem (neg J) (fun x => -f x) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  refine ⟨fun x hx => (h1 x hx).neg, fun x hx => dNeg_mem (h2 x hx),
    fun x hx i => ?_⟩
  rw [partial1_neg]
  exact dNeg_mem (h3 x hx i)

def sub (J K : DCJet) : DCJet := add J (neg K)

theorem sub_mem {J K : DCJet} {f g : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hK : JetMem K g D) :
    JetMem (sub J K) (fun x => f x - g x) D := by
  have h := add_mem hJ (neg_mem hK)
  simpa [sub, sub_eq_add_neg] using h

#print axioms add_mem
#print axioms neg_mem
#print axioms sub_mem

/-! ## §3 Product, inverse, quotient -/

def mul (J K : DCJet) : DCJet :=
  ⟨dMul J.value K.value,
   fun i => dAdd (dMul J.value (K.part i)) (dMul K.value (J.part i))⟩

theorem mul_mem {J K : DCJet} {f g : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hK : JetMem K g D) :
    JetMem (mul J K) (fun x => f x * g x) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  obtain ⟨k1, k2, k3⟩ := hK
  refine ⟨fun x hx => (h1 x hx).mul (k1 x hx),
    fun x hx => dMul_mem (h2 x hx) (k2 x hx), fun x hx i => ?_⟩
  rw [partial1_mul (h1 x hx) (k1 x hx) i]
  exact dAdd_mem (dMul_mem (h2 x hx) (k3 x hx i)) (dMul_mem (k2 x hx) (h3 x hx i))

/-- Reciprocal jet: `∂(1/f) = -∂f · (1/f) · (1/f)`. -/
def inv (J : DCJet) : DCJet :=
  ⟨dInv J.value,
   fun i => dNeg (dMul (dMul (dInv J.value) (dInv J.value)) (J.part i))⟩

theorem inv_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hpos : 0 < J.value.lo) :
    JetMem (inv J) (fun x => (f x)⁻¹) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ (-(J.value.k : ℤ)) := mem_zero_pow J.value.k
  have hv0 : ∀ x ∈ D, f x ≠ 0 := by
    intro x hx
    have hlo : (0 : ℝ) < (J.value.lo : ℝ) := by exact_mod_cast hpos
    exact ne_of_gt (lt_of_lt_of_le (mul_pos hlo hkpos) (h2 x hx).1)
  refine ⟨fun x hx => (h1 x hx).inv (hv0 x hx),
    fun x hx => dInv_mem hpos (h2 x hx), fun x hx i => ?_⟩
  have hinv : ContDiffAt ℝ 1 (fun t : ℝ => t⁻¹) (f x) :=
    contDiffAt_inv (𝕜 := ℝ) (x := f x) (hv0 x hx)
  have hcomp : partial1 i ((fun t : ℝ => t⁻¹) ∘ f) x
      = deriv (fun t : ℝ => t⁻¹) (f x) * partial1 i f x :=
    partial1_comp hinv (h1 x hx) i
  have hderiv : deriv (fun t : ℝ => t⁻¹) (f x) = -((f x)⁻¹ * (f x)⁻¹) := by
    rw [deriv_inv, pow_two, mul_inv]
  have htarget : partial1 i (fun y => (f y)⁻¹) x
      = -(((f x)⁻¹ * (f x)⁻¹) * partial1 i f x) := by
    have hfun : (fun y => (f y)⁻¹) = (fun t : ℝ => t⁻¹) ∘ f := rfl
    rw [hfun, hcomp, hderiv]
    ring
  rw [htarget]
  exact dNeg_mem (dMul_mem
    (dMul_mem (dInv_mem hpos (h2 x hx)) (dInv_mem hpos (h2 x hx))) (h3 x hx i))

/-- Quotient jet. -/
def div (J K : DCJet) : DCJet := mul J (inv K)

theorem div_mem {J K : DCJet} {f g : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hK : JetMem K g D) (hpos : 0 < K.value.lo) :
    JetMem (div J K) (fun x => f x / g x) D := by
  have h := mul_mem hJ (inv_mem hK hpos)
  simpa [div, div_eq_mul_inv] using h

#print axioms mul_mem
#print axioms inv_mem
#print axioms div_mem

/-! ## §4 Square root -/

/-! **Slot wrappers.**  `whnf` on a compound DC term containing `dInv`
unfolds `dInv`'s `Int.log2` (a well-founded recursion) on a symbolic argument and
never terminates usefully — a single `exact` whose goal exposes such a term cost
290 s in the profiler.  Every AD slot whose head sits under `dMul … dInv` is
therefore wrapped in an `@[irreducible]` def, with an equation lemma for the one
explicit unfolding the proofs need. -/

/-- Square-root derivative slot `∂f / (2√f)`. -/
@[irreducible] def sqrtSlot (A p : DC) : DC := dMul (dInv (dMul (dInt 2) (dSqrt A))) p

theorem sqrtSlot_eq (A p : DC) : sqrtSlot A p = dMul (dInv (dMul (dInt 2) (dSqrt A))) p := by
  unfold sqrtSlot
  rfl

/-- Square-root jet: `∂√f = ∂f / (2√f)`. -/
def sqrt (J : DCJet) : DCJet :=
  ⟨dSqrt J.value, fun i => sqrtSlot J.value (J.part i)⟩

theorem sqrt_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hbig : dLoBig J.value = true)
    (hden : 0 < (dMul (dInt 2) (dSqrt J.value)).lo) :
    JetMem (sqrt J) (fun x => Real.sqrt (f x)) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ (-(J.value.k : ℤ)) := mem_zero_pow J.value.k
  have hlo : (0 : ℝ) < (J.value.lo : ℝ) := by exact_mod_cast dLoBig_sound hbig
  have hvpos : ∀ x ∈ D, (0 : ℝ) < f x := fun x hx =>
    lt_of_lt_of_le (mul_pos hlo hkpos) (h2 x hx).1
  refine ⟨fun x hx => (h1 x hx).sqrt (hvpos x hx).ne',
    fun x hx => dSqrt_mem (hvpos x hx).le (h2 x hx), fun x hx i => ?_⟩
  have hcomp : partial1 i (Real.sqrt ∘ f) x
      = deriv Real.sqrt (f x) * partial1 i f x :=
    partial1_comp (Real.contDiffAt_sqrt (hvpos x hx).ne') (h1 x hx) i
  have hderiv : deriv Real.sqrt (f x) = (2 * Real.sqrt (f x))⁻¹ := by
    rw [(Real.hasDerivAt_sqrt (hvpos x hx).ne').deriv, one_div]
  have htarget : partial1 i (fun y => Real.sqrt (f y)) x
      = (2 * Real.sqrt (f x))⁻¹ * partial1 i f x := by
    have hfun : (fun y => Real.sqrt (f y)) = Real.sqrt ∘ f := rfl
    rw [hfun, hcomp, hderiv]
  rw [htarget]
  change (sqrtSlot J.value (J.part i)).mem ((2 * Real.sqrt (f x))⁻¹ * partial1 i f x)
  rw [sqrtSlot_eq]
  exact dMul_mem
    (dInv_mem hden (dMul_mem (by simpa using dInt_mem 2) (dSqrt_mem (hvpos x hx).le (h2 x hx))))
    (h3 x hx i)

#print axioms sqrtSlot_eq
#print axioms sqrt_mem

/-! ## §5 `matan` nodes — four arms and the derivative slot -/

/-- `matan` derivative slot `∂f · matanD`. -/
@[irreducible] def matanSlot (A Mv p : DC) : DC := dMul (dMatanD A Mv) p

theorem matanSlot_eq (A Mv p : DC) : matanSlot A Mv p = dMul (dMatanD A Mv) p := by
  unfold matanSlot
  rfl

/-- `matan` jet with the value bracket `Mv` and the landed derivative
`dMatanD`: partial slot `∂f · matanD`. -/
def matanWith (J : DCJet) (Mv : DC) : DCJet :=
  ⟨Mv, fun i => matanSlot J.value Mv (J.part i)⟩

theorem matanWith_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (Mv : DC) (hMv : ∀ x ∈ D, Mv.mem (matan (f x)))
    (hbig : dLoBig J.value = true) (hden1 : dLoBig (dAdd ONE J.value) = true)
    (hden2 : dLoBig (dMul (dInt 2) J.value) = true) :
    JetMem (matanWith J Mv) (fun x => matan (f x)) D := by
  obtain ⟨h1, h2, h3⟩ := hJ
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ (-(J.value.k : ℤ)) := mem_zero_pow J.value.k
  have hlo : (0 : ℝ) < (J.value.lo : ℝ) := by exact_mod_cast dLoBig_sound hbig
  have hvpos : ∀ x ∈ D, (0 : ℝ) < f x := fun x hx =>
    lt_of_lt_of_le (mul_pos hlo hkpos) (h2 x hx).1
  have hmat : ∀ x ∈ D, ContDiffAt ℝ 1 matan (f x) := fun x hx =>
    c1_of_c2 (contDiffAt_matan_of_pos (hvpos x hx))
  refine ⟨fun x hx => (hmat x hx).comp x (h1 x hx), hMv, fun x hx i => ?_⟩
  have hcomp : partial1 i (matan ∘ f) x = deriv matan (f x) * partial1 i f x :=
    partial1_comp (hmat x hx) (h1 x hx) i
  have htarget : partial1 i (fun y => matan (f y)) x = deriv matan (f x) * partial1 i f x := by
    have hfun : (fun y => matan (f y)) = matan ∘ f := rfl
    rw [hfun, hcomp]
  rw [htarget]
  change (matanSlot J.value Mv (J.part i)).mem (deriv matan (f x) * partial1 i f x)
  rw [matanSlot_eq]
  exact dMul_mem (dMatanD_mem (h2 x hx) (hMv x hx) hbig hden1 hden2) (h3 x hx i)

/-- Direct-9 arm (`0 < r ≤ 0.1019`). -/
def matan9 (J : DCJet) : DCJet := matanWith J (dMatan9 J.value)

theorem matan9_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hbig : dLoBig J.value = true)
    (hden1 : dLoBig (dAdd ONE J.value) = true)
    (hden2 : dLoBig (dMul (dInt 2) J.value) = true) :
    JetMem (matan9 J) (fun x => matan (f x)) D :=
  matanWith_mem (J := J) (f := f) (D := D) (Mv := dMatan9 J.value) hJ
    (fun x hx => dMatan9_mem (hJ.2.1 x hx) hbig) hbig hden1 hden2

/-- w-form arm (`1 < r ≤ 4`). -/
def matanWp (J : DCJet) : DCJet := matanWith J (dMatanWp J.value)

theorem matanWp_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hbig : dLoBig J.value = true)
    (h1 : dLoGt J.value ONE = true)
    (hden : dLoBig (dAdd (dSqrt J.value) ONE) = true)
    (hden1 : dLoBig (dAdd ONE J.value) = true)
    (hden2 : dLoBig (dMul (dInt 2) J.value) = true) :
    JetMem (matanWp J) (fun x => matan (f x)) D :=
  matanWith_mem (J := J) (f := f) (D := D) (Mv := dMatanWp J.value) hJ
    (fun x hx => dMatanWp_mem (hJ.2.1 x hx) hbig h1 hden) hbig hden1 hden2

/-- u-form arm (`r > 0`). -/
def matanU9 (J : DCJet) : DCJet := matanWith J (dMatanU9 J.value)

theorem matanU9_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (hbig : dLoBig J.value = true)
    (hden1 : dLoBig (dAdd ONE J.value) = true)
    (hden2 : dLoBig (dMul (dInt 2) J.value) = true) :
    JetMem (matanU9 J) (fun x => matan (f x)) D :=
  matanWith_mem (J := J) (f := f) (D := D) (Mv := dMatanU9 J.value) hJ
    (fun x hx => dMatanU9_mem (hJ.2.1 x hx) hbig) hbig hden1 hden2

/-- Mirror arm `matan r = π/(2√r) − matan(1/r)/r` (`0 < r < 1`) with the inner
bracket supplied by the caller. -/
def matanMir (J : DCJet) (Minner : DC) : DCJet := matanWith J (dMatanMir J.value Minner)

theorem matanMir_mem {J : DCJet} {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hJ : JetMem J f D) (Minner : DC) (hMinner : ∀ x ∈ D, Minner.mem (matan (1 / f x)))
    (hbig : dLoBig J.value = true)
    (hden1 : dLoBig (dAdd ONE J.value) = true)
    (hden2 : dLoBig (dMul (dInt 2) J.value) = true) :
    JetMem (matanMir J Minner) (fun x => matan (f x)) D :=
  matanWith_mem (J := J) (f := f) (D := D) (Mv := dMatanMir J.value Minner) hJ
    (fun x hx => dMatanMir_mem (hJ.2.1 x hx) (hMinner x hx) hbig) hbig hden1 hden2

/-! ### The tight mirror inner -/

/-- **The tight mirror-inner bracket**: for `A ∋ r` the bracket of
`matan (1/r)` built by `dMatanWp` on `dInv A ∋ 1/r` when its upper end is below
`4`, and by `dMatanU9` otherwise.  (The QInterval emission's `PMir` consumes
exactly `M.mem (matan (1/t))` — `W1aFJet.lean:1220` — with `PWp`/`PU9` as the
inner arms; this is the DC counterpart.) -/
def dMatanTight (A : DC) : DC :=
  if dHiLt (dInv A) (dInt 4) then dMatanWp (dInv A) else dMatanU9 (dInv A)

theorem dMatanTight_mem {A : DC} {r : ℝ} (hA : A.mem r) (hbig : dLoBig A = true)
    (hR1 : dLoGt (dInv A) ONE = true) (hRden : dLoBig (dAdd (dSqrt (dInv A)) ONE) = true)
    (hRbig : dLoBig (dInv A) = true) :
    (dMatanTight A).mem (matan (1 / r)) := by
  have hA0 : (0 : ℤ) < A.lo := by exact_mod_cast dLoBig_sound hbig
  have hR : (dInv A).mem (1 / r) := by
    have h := dInv_mem hA0 hA
    simpa [one_div] using h
  unfold dMatanTight
  split
  · next h => exact dMatanWp_mem hR hRbig hR1 hRden
  · next h => exact dMatanU9_mem hR hRbig

#print axioms matanSlot_eq
#print axioms matanWith_mem
#print axioms matan9_mem
#print axioms matanWp_mem
#print axioms matanU9_mem
#print axioms matanMir_mem
#print axioms dMatanTight_mem

end DCJetKit
end Kepler.Text.TaylorSecond
