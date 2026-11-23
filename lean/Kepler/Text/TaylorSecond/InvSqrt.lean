import Kepler.Text.TaylorSecond.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology

private theorem nonzero_of_mem {I : QInterval} {x : ℝ} (hx : I.mem x)
    (h : 0 < I.lo ∨ I.hi < 0) : x ≠ 0 := by
  cases h with
  | inl hl =>
      have hl' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hl
      exact ne_of_gt (lt_of_lt_of_le hl' hx.1)
  | inr hu =>
      have hu' : (I.hi : ℝ) < 0 := by exact_mod_cast hu
      exact ne_of_lt (lt_of_le_of_lt hx.2 hu')

private theorem mul_lo_pos {I J : QInterval}
    (hI : 0 < I.lo) (hIwf : I.lo ≤ I.hi) (hJ : 0 < J.lo) (hJwf : J.lo ≤ J.hi) :
    0 < (I.mul J).lo := by
  have hI' : 0 < I.hi := lt_of_lt_of_le hI hIwf
  have hJ' : 0 < J.hi := lt_of_lt_of_le hJ hJwf
  exact lt_min (lt_min (mul_pos hI hJ) (mul_pos hI hJ'))
    (lt_min (mul_pos hI' hJ) (mul_pos hI' hJ'))

private theorem scale_two_pos {I : QInterval} (hI : 0 < I.lo) (hIwf : I.lo ≤ I.hi) :
    0 < (QInterval.scale 2 I).lo := by
  exact mul_lo_pos (by norm_num [QInterval.const]) (by norm_num [QInterval.const]) hI hIwf

/-- Reciprocal as a unary C² certificate.  Its derivative intervals are
expressed using `I⁻¹`, so no reciprocal of a possibly zero-crossing square is needed. -/
noncomputable def invUnaryBox (I : QInterval) (h : 0 < I.lo ∨ I.hi < 0) :
    UnaryBox (fun t : ℝ => t⁻¹) I where
  firstFun := fun t => -(t⁻¹ * t⁻¹)
  secondFun := fun t => 2 * (t⁻¹ * t⁻¹ * t⁻¹)
  value := I.inv
  first := (I.inv.mul I.inv).neg
  second := QInterval.scale 2 ((I.inv.mul I.inv).mul I.inv)
  smooth := fun t ht => contDiffAt_inv ℝ (nonzero_of_mem ht h)
  first_eq := by
    intro t ht
    rw [deriv_inv]
    simp only [pow_two, mul_inv]
  second_eq := by
    intro t ht
    have htwo := iter_deriv_inv (𝕜 := ℝ) 2 t
    norm_num [Function.iterate_succ_apply, Nat.factorial] at htwo
    simpa [zpow_neg, zpow_ofNat, pow_succ, mul_assoc] using htwo
  value_mem := fun t ht => QInterval.mem_inv ht h
  first_mem := by
    intro t ht
    exact QInterval.mem_neg (QInterval.mem_mul (QInterval.mem_inv ht h) (QInterval.mem_inv ht h))
  second_mem := by
    intro t ht
    exact QInterval.mem_scale (QInterval.mem_mul
      (QInterval.mem_mul (QInterval.mem_inv ht h) (QInterval.mem_inv ht h))
      (QInterval.mem_inv ht h))

/-- Positive square root as a unary C² certificate.  `V` is a rational outer
interval for the square-root values, with a strictly positive lower endpoint. -/
noncomputable def sqrtUnaryBox (I V : QInterval) (hIwf : I.lo ≤ I.hi) (hVwf : V.lo ≤ V.hi)
    (hI : 0 < I.lo) (hV : 0 < V.lo)
    (hVmem : ∀ t, I.mem t → V.mem (Real.sqrt t)) : UnaryBox Real.sqrt I where
  firstFun := fun t => (2 * Real.sqrt t)⁻¹
  secondFun := fun t => -((2 * Real.sqrt t)⁻¹ * (2 * t)⁻¹)
  value := V
  first := (QInterval.scale 2 V).inv
  second := ((QInterval.scale 2 V).inv.mul (QInterval.scale 2 I).inv).neg
  smooth := by
    intro t ht
    have ht0 : t ≠ 0 := nonzero_of_mem ht (Or.inl hI)
    exact Real.contDiffAt_sqrt ht0
  first_eq := by
    intro t ht
    have ht0 : t ≠ 0 := nonzero_of_mem ht (Or.inl hI)
    simpa only [one_div] using (Real.hasDerivAt_sqrt ht0).deriv
  second_eq := by
    intro t ht
    have htpos : 0 < t := by
      have hI' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
      exact lt_of_lt_of_le hI' ht.1
    have ht0 : t ≠ 0 := ne_of_gt htpos
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hs0 : Real.sqrt t ≠ 0 := ne_of_gt hs
    have hbase : HasDerivAt (fun y : ℝ => 2 * Real.sqrt y)
        (2 * (1 / (2 * Real.sqrt t))) t := (Real.hasDerivAt_sqrt ht0).const_mul 2
    have hderiv := (hbase.inv (by positivity : (2 : ℝ) * Real.sqrt t ≠ 0)).deriv
    have he : deriv Real.sqrt =ᶠ[𝓝 t] (fun y : ℝ => (2 * Real.sqrt y)⁻¹) := by
      filter_upwards [Ioi_mem_nhds htpos] with y hy
      simpa only [one_div] using (Real.hasDerivAt_sqrt (ne_of_gt hy)).deriv
    rw [he.deriv_eq]
    change deriv (fun y : ℝ => (2 * Real.sqrt y)⁻¹) t =
      -(2 * (1 / (2 * Real.sqrt t))) / (2 * Real.sqrt t) ^ 2 at hderiv
    rw [hderiv]
    have hsquare : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
    field_simp [ht0, hs0]
    ring_nf
    rw [hsquare]
  value_mem := hVmem
  first_mem := by
    intro t ht
    exact QInterval.mem_inv (QInterval.mem_scale (hVmem t ht))
      (Or.inl (scale_two_pos hV hVwf))
  second_mem := by
    intro t ht
    exact QInterval.mem_neg (QInterval.mem_mul
      (QInterval.mem_inv (QInterval.mem_scale (hVmem t ht))
        (Or.inl (scale_two_pos hV hVwf)))
      (QInterval.mem_inv (QInterval.mem_scale ht) (Or.inl (scale_two_pos hI hIwf))))

#print axioms invUnaryBox
#print axioms sqrtUnaryBox

end Kepler.Text.TaylorSecond
