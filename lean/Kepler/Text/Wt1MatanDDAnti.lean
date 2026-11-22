import Kepler.Text.Wt1TowerKit

set_option maxHeartbeats 4000000

namespace Kepler.Text

open Filter
open scoped Topology

/-- The rational lower bound for `arctan` whose strictness is equivalent to
 negativity of the third derivative of `matan` on the positive branch. -/
theorem wt1_arctan_gt_matanDDD_bound {s : ℝ} (hs : 0 < s) :
    s * (15 + 40 * s ^ 2 + 33 * s ^ 4) / (15 * (1 + s ^ 2) ^ 3) < Real.arctan s := by
  have hcont : ContinuousOn
      (fun x : ℝ => Real.arctan x -
        x * (15 + 40 * x ^ 2 + 33 * x ^ 4) / (15 * (1 + x ^ 2) ^ 3)) (Set.Ici 0) := by
    refine Real.continuous_arctan.continuousOn.sub ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      positivity
  have h := strictMonoOn_of_deriv_pos (D := Set.Ici (0 : ℝ))
    (f := fun x : ℝ => Real.arctan x -
      x * (15 + 40 * x ^ 2 + 33 * x ^ 4) / (15 * (1 + x ^ 2) ^ 3))
    (convex_Ici 0) hcont (fun x hx => by
      have hx0 : (0 : ℝ) < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        have h := hasDerivAt_pow 2 x
        simpa [pow_one, mul_comm] using h
      have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
        have h := hasDerivAt_pow 4 x
        simpa [pow_succ] using h
      have hp : HasDerivAt (fun y : ℝ => 15 + 40 * y ^ 2 + 33 * y ^ 4)
          (80 * x + 132 * x ^ 3) x := by
        have h := ((hasDerivAt_const x (15 : ℝ)).add
          ((hasDerivAt_pow 2 x).const_mul 40)).add ((hasDerivAt_pow 4 x).const_mul 33)
        convert h using 1 <;> first | rfl | ring
      have hnum : HasDerivAt (fun y : ℝ => y * (15 + 40 * y ^ 2 + 33 * y ^ 4))
          ((15 + 40 * x ^ 2 + 33 * x ^ 4) + x * (80 * x + 132 * x ^ 3)) x := by
        convert (hasDerivAt_id x).mul hp using 1 <;>
          first | rfl | ((try simp only [id_eq]); ring)
      have hden : HasDerivAt (fun y : ℝ => 15 * (1 + y ^ 2) ^ 3)
          (90 * x * (1 + x ^ 2) ^ 2) x := by
        have hbase : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
          convert (hasDerivAt_const x (1 : ℝ)).add h2 using 1 <;> first | rfl | ring
        have hcube := hbase.pow 3
        have h := hcube.const_mul 15
        convert h using 1 <;> first | rfl | ring
      have hquot : HasDerivAt
          (fun y : ℝ => y * (15 + 40 * y ^ 2 + 33 * y ^ 4) / (15 * (1 + y ^ 2) ^ 3))
          ((((15 + 40 * x ^ 2 + 33 * x ^ 4) + x * (80 * x + 132 * x ^ 3)) *
              (15 * (1 + x ^ 2) ^ 3) -
            x * (15 + 40 * x ^ 2 + 33 * x ^ 4) * (90 * x * (1 + x ^ 2) ^ 2)) /
            (15 * (1 + x ^ 2) ^ 3) ^ 2) x :=
        hnum.div hden (by positivity)
      have hderiv := (Real.hasDerivAt_arctan x).sub hquot
      have hfun : ((Real.arctan : ℝ → ℝ) -
          (fun y : ℝ => y * (15 + 40 * y ^ 2 + 33 * y ^ 4) /
            (15 * (1 + y ^ 2) ^ 3))) =
          (fun y : ℝ => Real.arctan y -
            y * (15 + 40 * y ^ 2 + 33 * y ^ 4) / (15 * (1 + y ^ 2) ^ 3)) := by
        funext y
        rfl
      rw [hfun] at hderiv
      rw [hderiv.deriv]
      have hEq : 1 / (1 + x ^ 2) -
          (((15 + 40 * x ^ 2 + 33 * x ^ 4) + x * (80 * x + 132 * x ^ 3)) *
              (15 * (1 + x ^ 2) ^ 3) -
            x * (15 + 40 * x ^ 2 + 33 * x ^ 4) * (90 * x * (1 + x ^ 2) ^ 2)) /
            (15 * (1 + x ^ 2) ^ 3) ^ 2 =
          16 * x ^ 6 / (5 * (1 + x ^ 2) ^ 4) := by
        field_simp
        ring
      rw [hEq]
      positivity)
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
  simpa using h

/-- A nonzero form of `matanDD` obtained by substituting `matanD`. -/
theorem matanDD_eq_matanD_of_ne {t : ℝ} (ht : t ≠ 0) :
    matanDD t = -(3 / (2 * t)) * matanD t - 1 / (2 * t * (1 + t) ^ 2) := by
  rw [matanDD_of_ne ht, matanD_of_ne ht]
  ring

/-- The third derivative of `matan`, stated as the derivative of `matanDD`,
on the positive branch. -/
theorem matanDD_hasDerivAt_of_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt matanDD
      (15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
        5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have h3over : HasDerivAt (fun u : ℝ => 3 / (2 * u)) (-(3 / (2 * t ^ 2))) t := by
    have h := (hasDerivAt_const t (3 : ℝ)).div
      ((hasDerivAt_id t).const_mul 2) (by positivity)
    convert h using 1 <;> first | rfl |
      ((try simp only [id_eq]); (field_simp [ht0]; ring))
  have hcoef : HasDerivAt (fun u : ℝ => -(3 / (2 * u))) (3 / (2 * t ^ 2)) t := by
    convert h3over.neg using 1 <;> first | rfl | ring
  have hbase : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
    simpa using (hasDerivAt_id t).const_add 1
  have hsq : HasDerivAt (fun u : ℝ => (1 + u) ^ 2) (2 * (1 + t)) t := by
    convert hbase.pow 2 using 1 <;> first | rfl | ring
  have hden : HasDerivAt (fun u : ℝ => 2 * u * (1 + u) ^ 2)
      (2 * (1 + t) ^ 2 + 2 * t * (2 * (1 + t))) t := by
    convert ((hasDerivAt_id t).const_mul 2).mul hsq using 1 <;>
      first | rfl | ((try simp only [id_eq]); ring)
  have hposinv : HasDerivAt (fun u : ℝ => 1 / (2 * u * (1 + u) ^ 2))
      (-1 / (2 * t ^ 2 * (1 + t) ^ 2) - 1 / (t * (1 + t) ^ 3)) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).div hden (by positivity)
    convert h using 1 <;> first | rfl | (field_simp [ht0, h1t]; ring)
  have hform : HasDerivAt
      (fun u : ℝ => -(3 / (2 * u)) * matanD u - 1 / (2 * u * (1 + u) ^ 2))
      (15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
        5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3)) t := by
    have h := hcoef.mul (matanD_hasDerivAt (by linarith : (-1 : ℝ) < t)) |>.sub hposinv
    refine h.congr_deriv ?_
    rw [matanD_of_ne ht0, matanDD_of_ne ht0]
    field_simp [ht0, h1t]
    ring
  refine hform.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show 0 < t by exact ht)
    (show t < t + 1 by linarith)] with u hu
  exact matanDD_eq_matanD_of_ne (ne_of_gt hu.1)

/-- `matanDD` has strictly negative derivative on the positive branch. -/
theorem matanDD_deriv_neg_of_pos {t : ℝ} (ht : 0 < t) : deriv matanDD t < 0 := by
  rw [(matanDD_hasDerivAt_of_pos ht).deriv]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hs4 : Real.sqrt t ^ 4 = t ^ 2 := by
    calc Real.sqrt t ^ 4 = (Real.sqrt t ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hs2]
  have hm : matan t = Real.arctan (Real.sqrt t) / Real.sqrt t := by
    unfold matan
    rw [if_neg ht0, if_pos ht]
  have hbound := wt1_arctan_gt_matanDDD_bound hs
  rw [hs2, hs4] at hbound
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 15 * (1 + t) ^ 3)] at hbound
  have hkey : 15 + 40 * t + 33 * t ^ 2 < 15 * (1 + t) ^ 3 * matan t := by
    rw [hm]
    rw [show 15 * (1 + t) ^ 3 * (Real.arctan (Real.sqrt t) / Real.sqrt t) =
      (15 * (1 + t) ^ 3 * Real.arctan (Real.sqrt t)) / Real.sqrt t by ring]
    rw [lt_div_iff₀ hs]
    calc (15 + 40 * t + 33 * t ^ 2) * Real.sqrt t =
        Real.sqrt t * (15 + 40 * t + 33 * t ^ 2) := by ring
      _ < Real.arctan (Real.sqrt t) * (15 * (1 + t) ^ 3) := hbound
      _ = 15 * (1 + t) ^ 3 * Real.arctan (Real.sqrt t) := by ring
  have hform : 15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
      5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3) =
      (15 + 40 * t + 33 * t ^ 2 - 15 * (1 + t) ^ 3 * matan t) /
        (8 * t ^ 3 * (1 + t) ^ 3) := by
    field_simp [ht0, h1t]
    ring
  rw [hform]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `matanDD` is strictly antitone on `(0, ∞)`. -/
theorem matanDD_strictAntiOn_pos : StrictAntiOn matanDD (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (matanDD_hasDerivAt_of_pos hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact matanDD_deriv_neg_of_pos hx

/-- Exact endpoint envelope of `matanDD` on a positive interval. -/
theorem matanDD_mem_Icc_of_pos {l t u : ℝ} (hl : 0 < l) (hlt : l ≤ t) (htu : t ≤ u) :
    matanDD t ∈ Set.Icc (matanDD u) (matanDD l) := by
  have ht : 0 < t := lt_of_lt_of_le hl hlt
  have hu : 0 < u := lt_of_lt_of_le ht htu
  constructor
  · exact matanDD_strictAntiOn_pos.antitoneOn ht hu htu
  · exact matanDD_strictAntiOn_pos.antitoneOn hl ht hlt

#print axioms wt1_arctan_gt_matanDDD_bound
#print axioms matanDD_eq_matanD_of_ne
#print axioms matanDD_hasDerivAt_of_pos
#print axioms matanDD_deriv_neg_of_pos
#print axioms matanDD_strictAntiOn_pos
#print axioms matanDD_mem_Icc_of_pos

end Kepler.Text
