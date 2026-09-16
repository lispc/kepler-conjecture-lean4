/-
Kepler/Text/LocalAuto6.lean — port of HOL Light Flyspeck
`scripts/local/local_lemmas1.hl` (4 defs + 116 declared results: the
lunar-deform / arcV / continuity / local-fan-slicing chapter,
Hoang Le Truong 2010).

Encoding (HOL → Lean):
- HOL `real^3` ↦ `V3` (Kepler.Geom); `real^N`-generic statements are
  specialized to `V3` (the chapter's only use).
- HOL `arcV` ↦ `Kepler.Geom.arcV` (bridged to Mathlib's real inner product
  by `arcV_eq` below); `azim` ↦ `azim`; `orthonormal` ↦ `Orthonormal3`;
  `collinear {a,b,c}` ↦ `Collinear3`; `wedge` ↦ `wedge`.
- HOL `wedge_ge`/`wedge_in_fan_ge`/`wedge_in_fan_gt`/`azim_in_fan`/
  `azim_cycle`/`EE`/`rho_node1`/`ivs_rho_node1`/`interior_angle1`/
  `local_fan`/`convex_local_fan`/`v_prime`/`e_prime`/`darts_of_hyp`/
  `circular`/`lunar` ↦ the importable `_p2` kit of Kepler.Text.LocalAuto2
  (no `_p6` re-copies). `cyclic_set` ↦ `cyclicSet_p3` (LocalAuto3).
- HOL `deformation`/`localization` (defs 3–4 of this source) are already
  encoded by the importable `deformation_p2`/`localization_p2`
  (`real_interval (a,b)` ↦ `Set.Icc a b`; `continuous atreal` ↦
  `ContinuousAt`), used directly below. NEEDS: dedup at merge.
- HOL `f continuous atreal r` (metric) and `f real_continuous atreal r`
  (scalar ε-δ) both ↦ `ContinuousAt f r` (identical ε-δ content).
- HOL `hypermap (HYP (vec 0, V, E))` hypotheses ↦ `IsHyp_p2 0 V E HS`;
  `face HS d` ↦ `HS.face d`; `ITER n (rho_node1 FF) v` ↦
  `(rhoNode1_p2 FF)^[n] v`; `CARD S` ↦ `S.ncard`; `sum S f` ↦ `setSum S f`
  (PackingAuto2); `graph E` ↦ `Kepler.Text.Fan.Graph`.
- HOL `ups_x` ↦ copy `upsX_p6` (PackingAuto18/25 both define
  `Kepler.Text.upsX`, so reuse would be ambiguous). NEEDS: dedup at merge.
- The local-fan slicing chapter (FACE_MAP_*, HAFL_CIRCLE_*, DETERMINE_FV*,
  SUM_INTERIOR_AGL_LEMMA, THE_SLICING_INTO_2_LEMMA, EJRCFJD, ...) is
  stated verbatim with `sorry` (giants); the arcV / wedge / continuity /
  real-arithmetic kit is proved.
-/

import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto3
import Kepler.Text.Polytope
import Kepler.Text.Fan
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## Definitions -/

/-- HOL `normize (v:real^N)` (local_lemmas1.hl:32). -/
noncomputable def normize (v : V3) : V3 := (1 / ‖v‖) • v

/-- HOL `lunar_deform (e1,e2,e3) t x` (local_lemmas1.hl:27). -/
noncomputable def lunarDeform (e1 e2 e3 : V3) (t : ℝ) (x : V3) : V3 :=
  (‖x‖ * Real.cos ((1 - t) * azim 0 e3 e1 x) * Real.sin (arcV 0 e3 x)) • e1 +
    (‖x‖ * Real.sin ((1 - t) * azim 0 e3 e1 x) * Real.sin (arcV 0 e3 x)) • e2 +
    (‖x‖ * Real.cos (arcV 0 e3 x)) • e3

/-- HOL `ups_x (x1,x2,x6)` (packing_defs); canonical home PackingAuto18/25
(ambiguous `upsX`), `_p6` copy. NEEDS: dedup at merge. -/
noncomputable def upsX_p6 (x1 x2 x6 : ℝ) : ℝ :=
  1 / 2 *
    (x1 + x2 + x6 +
      Real.sqrt ((x1 + x2 + x6) * (x1 + x2 + x6) - 2 * (x1 * x1 + x2 * x2 + x6 * x6)))

/-! ## arcV elementary kit -/

/-- `arcV` via Mathlib's real inner product (bridge for computations;
HOL `Trigonometry2.NOT_EQ_IMPCOS_ARC` shape). -/
theorem arcV_eq (u v w : V3) :
    arcV u v w = Real.arccos (inner ℝ (v - u) (w - u) / (dist v u * dist w u)) := by
  rw [arcV, ← inner_eq_dot]
  rfl

/-- Master computation: `arcV u v (u + t • (v - u)) = arccos (t / |t|)`
(`t / |t|` evaluates to `0` at `t = 0`, giving the degenerate `π/2`). -/
theorem arcV_add_smul_sub {u v : V3} (huv : u ≠ v) (t : ℝ) :
    arcV u v (u + t • (v - u)) = Real.arccos (t / |t|) := by
  have hnu : ‖v - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => huv h.symm)
  have hsub : (u + t • (v - u) : V3) - u = t • (v - u) :=
    add_sub_cancel_left u (t • (v - u))
  have hnum : inner ℝ (v - u) ((u + t • (v - u) : V3) - u) = t * (‖v - u‖ * ‖v - u‖) := by
    rw [hsub, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hden : dist v u * dist (u + t • (v - u)) u = ‖v - u‖ * (|t| * ‖v - u‖) := by
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  have hfr : inner ℝ (v - u) ((u + t • (v - u) : V3) - u) /
      (dist v u * dist (u + t • (v - u)) u) = t / |t| := by
    by_cases ht0 : t = 0
    · subst ht0
      rw [hnum, hden]
      simp
    · have habs : |t| ≠ 0 := abs_ne_zero.mpr ht0
      rw [hnum, hden, div_eq_iff (mul_ne_zero hnu (mul_ne_zero habs hnu)),
        div_mul_eq_mul_div, eq_div_iff habs]
      ring
  rw [arcV_eq, hfr]

/-- HOL `ACR_REFL` (local_lemmas1.hl:58). -/
theorem ACR_REFL {u v : V3} (h : u ≠ v) : arcV u v v = 0 := by
  have hnu : ‖v - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun hh => h hh.symm)
  have hin : inner ℝ (v - u) (v - u) = ‖v - u‖ * ‖v - u‖ := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [arcV_eq, hin, dist_eq_norm, div_self (mul_ne_zero hnu hnu)]
  exact Real.arccos_one

/-- HOL `ARC_OPPOSITE` (local_lemmas1.hl:66). -/
theorem ARC_OPPOSITE {u v : V3} (h : u ≠ v) : arcV u v (2 • u - v) = Real.pi := by
  have hnu : ‖v - u‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun hh => h hh.symm)
  have hpt : ((2 • u - v : V3) - u) = (-1 : ℝ) • (v - u) := by module
  rw [arcV_eq, hpt, real_inner_smul_right, real_inner_self_eq_norm_sq,
    dist_eq_norm, dist_eq_norm, hpt, norm_smul, Real.norm_eq_abs]
  simp only [abs_neg, abs_one, one_mul]
  rw [show ((-1 : ℝ) * ‖v - u‖ ^ 2 / (‖v - u‖ * ‖v - u‖)) = -1 from by
    rw [div_eq_iff (mul_ne_zero hnu hnu)]
    ring]
  exact Real.arccos_neg_one

/-- HOL `ARCV_EQ_0` (local_lemmas1.hl:77). -/
theorem ARCV_EQ_0 {u v : V3} (h : u ≠ v) {t : ℝ} (ht : 0 < t) :
    arcV u v (u + t • (v - u)) = 0 := by
  rw [arcV_add_smul_sub h, abs_of_pos ht, div_self ht.ne', Real.arccos_one]

/-- HOL `ARCV_EQ_0_ORIGIN` (local_lemmas1.hl:82). -/
theorem ARCV_EQ_0_ORIGIN {u : V3} (h : u ≠ 0) {t : ℝ} (ht : 0 < t) :
    arcV 0 u (t • u) = 0 := by
  have h1 : arcV 0 u (t • u) = arcV 0 u (0 + t • (u - 0)) := by
    rw [zero_add, sub_zero]
  rw [h1]
  exact ARCV_EQ_0 h.symm ht

/-- HOL `ARCV_PI_OPPOSITE` (local_lemmas1.hl:87). -/
theorem ARCV_PI_OPPOSITE {u v : V3} (h : u ≠ v) {t : ℝ} (ht : t < 0) :
    arcV u v (u + t • (v - u)) = Real.pi := by
  rw [arcV_add_smul_sub h, abs_of_neg ht, (show t / -t = (-1 : ℝ) from by
    rw [div_eq_iff (neg_ne_zero.mpr (ne_of_lt ht))]; ring), Real.arccos_neg_one]

/-- HOL `DOT_0_ARCV` (local_lemmas1.hl:99). -/
theorem DOT_0_ARCV {u v w : V3} (h : (v - u) ⬝ᵥ (w - u) = 0) :
    arcV u v w = Real.pi / 2 := by
  rw [arcV, h, zero_div]
  exact Real.arccos_zero

/-- HOL `ARCV_DEGENERATE` (local_lemmas1.hl:102). -/
theorem ARCV_DEGENERATE (u v : V3) :
    arcV u u v = Real.pi / 2 ∧ arcV u v u = Real.pi / 2 := by
  have e1 : (u - u : V3) ⬝ᵥ (v - u) = 0 := by
    rw [sub_self, ← inner_eq_dot]
    exact inner_zero_left _
  have e2 : (v - u : V3) ⬝ᵥ (u - u) = 0 := by
    rw [sub_self, ← inner_eq_dot]
    exact inner_zero_right _
  exact ⟨DOT_0_ARCV e1, DOT_0_ARCV e2⟩

/-- HOL `ARCV_DIRECTIONS` (local_lemmas1.hl:112). -/
theorem ARCV_DIRECTIONS {u v : V3} (h : u ≠ v) (t : ℝ) :
    (arcV u v (u + t • (v - u)) = 0 ↔ 0 < t) ∧
      (arcV u v (u + t • (v - u)) = Real.pi ↔ t < 0) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · refine ⟨Iff.intro ?_ ?_, Iff.intro ?_ ?_⟩
    · intro hh
      rw [ARCV_PI_OPPOSITE h ht] at hh
      exact absurd hh Real.pi_ne_zero
    · intro hh
      exact absurd hh (by linarith)
    · intro _; exact ht
    · intro _; exact ARCV_PI_OPPOSITE h ht
  · subst ht
    obtain ⟨hd1, hd2⟩ := ARCV_DEGENERATE u v
    have hsimp : (u + (0 : ℝ) • (v - u) : V3) = u := by
      rw [zero_smul, add_zero]
    refine ⟨Iff.intro ?_ ?_, Iff.intro ?_ ?_⟩
    · intro hh
      rw [hsimp] at hh
      rw [hd2] at hh
      exact absurd hh (by linarith [Real.pi_pos])
    · intro hh
      exact absurd hh (lt_irrefl (0 : ℝ))
    · intro hh
      rw [hsimp] at hh
      rw [hd2] at hh
      exact absurd hh (by linarith [Real.pi_pos])
    · intro hh
      exact absurd hh (lt_irrefl (0 : ℝ))
  · refine ⟨Iff.intro ?_ ?_, Iff.intro ?_ ?_⟩
    · intro _; exact ht
    · intro _; exact ARCV_EQ_0 h ht
    · intro hh
      rw [ARCV_EQ_0 h ht] at hh
      exact absurd hh.symm Real.pi_ne_zero
    · intro hh
      exact absurd hh (by linarith)

/-- HOL `ARCV_ORI_DIRECTIONS` (local_lemmas1.hl:125). -/
theorem ARCV_ORI_DIRECTIONS {v : V3} (h : v ≠ 0) (t : ℝ) :
    (arcV 0 v (t • v) = 0 ↔ 0 < t) ∧ (arcV 0 v (t • v) = Real.pi ↔ t < 0) := by
  have h0 : arcV 0 v (t • v) = arcV 0 v (0 + t • (v - 0)) := by
    rw [zero_add, sub_zero]
  rw [h0]
  exact ARCV_DIRECTIONS h.symm t

/-- HOL `REAL_NEG_MUL_EQ` (local_lemmas1.hl:134). -/
theorem REAL_NEG_MUL_EQ {a x : ℝ} (ha : a < 0) :
    (a * x < 0 ↔ 0 < x) ∧ (0 < a * x ↔ x < 0) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hp : 0 < a * x := by nlinarith
    exact ⟨iff_of_false (not_lt.mpr hp.le) (not_lt.mpr hx.le), iff_of_true hp hx⟩
  · subst hx
    exact ⟨by simp, by simp⟩
  · have hp : a * x < 0 := mul_neg_of_neg_of_pos ha hx
    exact ⟨iff_of_true hp hx, iff_of_false (not_lt.mpr hp.le) (not_lt.mpr hx.le)⟩

/-- HOL `NOT_EQ_0` (local_lemmas1.hl:145, a `REAL_ARITH` theorem). -/
theorem NOT_EQ_0 (x : ℝ) : ¬(x = 0) ↔ 0 < x ∨ x < 0 := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with hh | hh
    · exact Or.inr hh
    · exact Or.inl hh
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h

/-- HOL `SIN_ARCV_EQ_0` (local_lemmas1.hl:148). -/
theorem SIN_ARCV_EQ_0 {u v : V3} (h : u ≠ v) {t : ℝ} (ht : t ≠ 0) :
    Real.sin (arcV u v (u + t • (v - u))) = 0 := by
  rcases lt_or_gt_of_ne ht with ht' | ht'
  · rw [ARCV_PI_OPPOSITE h ht', Real.sin_pi]
  · rw [ARCV_EQ_0 h ht', Real.sin_zero]

/-- HOL `COLLINEAR_SIN_ARCV_0` (local_lemmas1.hl:154). -/
theorem COLLINEAR_SIN_ARCV_0 {u v x : V3} (hcol : Collinear3 u v x) (hx : u ≠ x)
    (hv : u ≠ v) : Real.sin (arcV u v x) = 0 := by
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (w := v) (w1 := x) (v := u)
    (by exact hv.symm : v ≠ u)).mp hcol
  have hxc : x = u + c • (v - u) := by
    rw [← hc, add_sub_cancel]
  rcases lt_trichotomy c 0 with hc' | hc' | hc'
  · rw [hxc, ARCV_PI_OPPOSITE hv hc', Real.sin_pi]
  · subst hc'
    rw [hxc, zero_smul, add_zero] at hx
    exact absurd rfl hx
  · rw [hxc, ARCV_EQ_0 hv hc', Real.sin_zero]

/-! ## Collinearity, normize, cos-arcs -/

/-- HOL `COLL_AFF_GT_2_1` (local_lemmas1.hl:178). -/
theorem COLL_AFF_GT_2_1 (x v w : V3) (hcol : ¬ Collinear3 x v w) :
    affGt ({x, v} : Set V3) ({w} : Set V3) =
      {y | ∃ t1 t2 t3 : ℝ, 0 < t3 ∧ t1 + t2 + t3 = 1 ∧
        y = t1 • x + t2 • v + t3 • w} := by
  have hxv : x ≠ v := fun hh => hcol (collinear3_of_eq hh.symm)
  have hwx : w ≠ x := fun hh => hcol (collinear3_pair_left hh)
  have hwv : w ≠ v := fun hh => hcol (collinear3_pair_right hh)
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, h, hy'⟩ := (affGt_pair_iff hxv hwx hwv).mp hy
    refine ⟨1 - c - h, h, c, by linarith, by linarith, ?_⟩
    have hy2 : y = c • (w - x) + h • (v - x) + x := sub_eq_iff_eq_add.mp hy'
    rw [hy2]
    module
  · intro ⟨t1, t2, t3, ht3, hsum, hy'⟩
    refine (affGt_pair_iff hxv hwx hwv).mpr ⟨t3, ht3, t2, ?_⟩
    have hz : y - x - (t3 • (w - x) + t2 • (v - x)) = 0 := by
      rw [show (t1 : ℝ) = 1 - t2 - t3 from by linarith] at hy'
      rw [hy']
      module
    exact sub_eq_zero.mp hz

/-- HOL `COLL_EQ_DEPENDENT` (local_lemmas1.hl:190). -/
theorem COLL_EQ_DEPENDENT (x y : V3) :
    Collinear3 0 x y ↔ ∃ tx ty : ℝ, ¬(tx = 0 ∧ ty = 0) ∧
      tx • x + ty • y = (0 : V3) := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact ⟨1, 0, by simp, by simp [hx]⟩
    by_cases hy : y = 0
    · exact ⟨0, 1, by simp, by simp [hy]⟩
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := x) (w1 := y)
      (by simpa using hx)).mp h
    rw [sub_zero, sub_zero] at hc
    refine ⟨-c, 1, by simp, ?_⟩
    rw [hc]
    module
  · rintro ⟨tx, ty, hne, hsum⟩
    by_cases hty : ty = 0
    · have htx : tx ≠ 0 := by
        intro htx0
        rw [htx0] at hne
        exact hne ⟨rfl, hty⟩
      rw [hty, zero_smul, add_zero] at hsum
      have hx0 : x = 0 := by
        rcases smul_eq_zero.mp hsum with h | h
        · exact absurd h htx
        · exact h
      rw [hx0]
      exact collinear3_of_eq rfl
    · by_cases hx : x = 0
      · rw [hx]
        exact collinear3_of_eq rfl
      have h2 := congrArg (fun z : V3 => (1 / ty) • z) hsum
      rw [smul_add, smul_smul, smul_smul, one_div, inv_mul_cancel₀ hty,
        one_smul, smul_zero] at h2
      rw [add_comm ((ty⁻¹ * tx) • x) y] at h2
      have hy : y = -(ty⁻¹ * tx) • x := by
        linear_combination (norm := module) h2
      exact (collinear3_iff_smul (v := 0) (w := x) (w1 := y)
        (by simpa using hx)).mpr ⟨-(ty⁻¹ * tx), by rw [sub_zero, sub_zero, hy]⟩

/-- HOL `NOT_COLL_ORTHONORMAL` (local_lemmas1.hl:233) — giant. -/
theorem NOT_COLL_ORTHONORMAL {x y : V3} (h : ¬ Collinear3 0 x y) :
    ∃ u : V3, u ∈ affineSpan ℝ ({0, x, y} : Set V3) ∧ ‖u‖ = 1 ∧ x ⬝ᵥ u = 0 :=
  sorry

/-- HOL `NORM1_NOT_0` (local_lemmas1.hl:263). -/
theorem NORM1_NOT_0 {x : V3} (h : ‖x‖ = 1) : x ≠ (0 : V3) := by
  intro hx
  rw [hx, norm_zero] at h
  norm_num at h

/-- HOL `ARCV_DETER_DIRECTION` (local_lemmas1.hl:269) — giant. -/
theorem ARCV_DETER_DIRECTION {x y u : V3} {tu ty : ℝ} (hty : 0 < ty)
    (hx : x = tu • u + ty • y) (hcol : ¬ Collinear3 0 u y) (hnx : ‖x‖ = 1)
    (hny : ‖y‖ = 1) (harc : arcV 0 u x = arcV 0 u y) : x = y :=
  sorry

/-- HOL `NORM_NORMIZE` (local_lemmas1.hl:359; HOL form is
`Trigonometry2.NOT_VEC0_UNITABLE` rewritten by `GSYM normize`). -/
theorem NORM_NORMIZE {v : V3} (h : v ≠ (0 : V3)) : ‖normize v‖ = 1 := by
  have hv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  rw [normize, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hvp)]
  field_simp

/-- HOL `ARCV_EQ_IMP_NORMIZE` (local_lemmas1.hl:363) — giant. -/
theorem ARCV_EQ_IMP_NORMIZE {x y u : V3} (hgt : x ∈ affGt ({0, u} : Set V3) ({y} : Set V3))
    (hcol : ¬ Collinear3 0 u y) (harc : arcV 0 u x = arcV 0 u y) : normize x = normize y :=
  sorry

/-- HOL `AZIM_AND_ARCV_EQ_IMP_PARA` (local_lemmas1.hl:443) — giant. -/
theorem AZIM_AND_ARCV_EQ_IMP_PARA {v0 u v x y : V3} (hcol : ¬ Collinear3 v0 u v)
    (haz : azim v0 u v x = azim v0 u v y) (harc : arcV v0 u x = arcV v0 u y) :
    y = v0 ∨ ∃ t : ℝ, 0 ≤ t ∧ x - v0 = t • (y - v0) :=
  sorry

/-- HOL `NORM_CAUCHY_SCHWARZ_FRAC2` (local_lemmas1.hl:635). -/
theorem NORM_CAUCHY_SCHWARZ_FRAC2 (u v : V3) :
    -1 ≤ u ⬝ᵥ v / (‖u‖ * ‖v‖) ∧ u ⬝ᵥ v / (‖u‖ * ‖v‖) ≤ 1 := by
  have hd : |u ⬝ᵥ v| ≤ ‖u‖ * ‖v‖ := by
    have h := abs_real_inner_le_norm u v
    rwa [inner_eq_dot] at h
  by_cases hden : ‖u‖ * ‖v‖ = 0
  · obtain ⟨h1, h2⟩ := abs_le.mp hd
    have hx0 : u ⬝ᵥ v = 0 := by
      rw [hden] at h1 h2
      exact le_antisymm h2 (by simpa using h1)
    constructor <;> simp [hx0]
  · have hpos : 0 < ‖u‖ * ‖v‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg u) (norm_nonneg v)) (Ne.symm hden)
    have key : |u ⬝ᵥ v / (‖u‖ * ‖v‖)| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg v)),
        div_le_one hpos]
      exact hd
    exact abs_le.mp key

/-- HOL `ARCV_BOUNDS` (local_lemmas1.hl:651). -/
theorem ARCV_BOUNDS (x y z : V3) : 0 ≤ arcV x y z ∧ arcV x y z ≤ Real.pi := by
  rw [arcV_eq]
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- HOL `COS_ARCV_EQ_ARCV` (local_lemmas1.hl:644). -/
theorem COS_ARCV_EQ_ARCV (x y z xx yy zz : V3) :
    Real.cos (arcV x y z) = Real.cos (arcV xx yy zz) ↔ arcV x y z = arcV xx yy zz := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := ARCV_BOUNDS x y z
    obtain ⟨h3, h4⟩ := ARCV_BOUNDS xx yy zz
    exact Real.injOn_cos (Set.mem_Icc.mpr ⟨h1, h2⟩) (Set.mem_Icc.mpr ⟨h3, h4⟩) h
  · intro h
    rw [h]

/-- HOL `SIN_ARCV_EQ_0_EQ_LAP` (local_lemmas1.hl:659). -/
theorem SIN_ARCV_EQ_0_EQ_LAP (x y z : V3) :
    Real.sin (arcV x y z) = 0 ↔ arcV x y z = 0 ∨ arcV x y z = Real.pi := by
  obtain ⟨h1, h2⟩ := ARCV_BOUNDS x y z
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    rcases lt_trichotomy n 0 with hn' | hn' | hn'
    · have hnc : (n : ℝ) < 0 := by exact_mod_cast hn'
      have hlt : (n : ℝ) * Real.pi < 0 := by nlinarith [hnc, Real.pi_pos]
      rw [← hn] at h1
      linarith
    · rw [hn'] at hn
      simp at hn
      exact Or.inl hn.symm
    · have hge : (1 : ℤ) ≤ n := by omega
      have hge' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
      rw [← hn] at h2
      have heq : (n : ℝ) * Real.pi = Real.pi :=
        le_antisymm h2 (by nlinarith [hge', Real.pi_pos])
      have hn1 : (n : ℝ) = 1 := by nlinarith [Real.pi_pos, heq]
      rw [hn1] at hn
      simp at hn
      exact Or.inr hn.symm
  · rintro (h | h)
    · rw [h, Real.sin_zero]
    · rw [h, Real.sin_pi]

/-- HOL `ORTHONORMAL_NOT_COLLINEAR` (local_lemmas1.hl:669). -/
theorem ORTHONORMAL_NOT_COLLINEAR {e1 e2 e3 : V3} (horth : Orthonormal3 e1 e2 e3) :
    ¬ Collinear3 0 e3 e1 := by
  have hn1 : ‖e1‖ = 1 := by
    have h := norm_sq_eq_dot e1
    rw [horth.1] at h
    nlinarith [norm_nonneg e1]
  have hn3 : ‖e3‖ = 1 := by
    have h := norm_sq_eq_dot e3
    rw [horth.2.2.1] at h
    nlinarith [norm_nonneg e3]
  intro hcol
  have he3 : e3 ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at hn3
    norm_num at hn3
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := e3) (w1 := e1) he3).mp hcol
  rw [sub_zero, sub_zero] at hc
  have hpar : e1 = c • e3 := hc
  have hdot : e1 ⬝ᵥ e3 = 0 := horth.2.2.2.2.1
  have hval : e1 ⬝ᵥ e3 = c := by
    rw [← inner_eq_dot, hpar, real_inner_smul_left, real_inner_self_eq_norm_sq, hn3]
    ring
  have hc0 : c = 0 := hval.symm.trans hdot
  rw [hpar, hc0, zero_smul, norm_zero] at hn1
  norm_num at hn1

/-- HOL `LUNAR_DEFORM_INJ` (local_lemmas1.hl:679) — giant. -/
theorem LUNAR_DEFORM_INJ {e1 e2 e3 : V3} (horth : Orthonormal3 e1 e2 e3) {t : ℝ}
    (ht1 : 0 ≤ t) (ht2 : t < 1) :
    ∀ x y : V3, lunarDeform e1 e2 e3 t x = lunarDeform e1 e2 e3 t y → x = y :=
  sorry

/-- HOL `GRAPH_IMAGE_IMAGE` (local_lemmas1.hl:801). -/
theorem GRAPH_IMAGE_IMAGE {E : Set (Set V3)} (f : V3 → V3) (hE : Graph E)
    (hinj : ∀ x y : V3, f x = f y → x = y) :
    Graph ((fun e : Set V3 => f '' e) '' E) := by
  intro e he
  obtain ⟨e0, he0E, rfl⟩ := he
  obtain ⟨hf0, hcard⟩ := hE e0 he0E
  have hinjOn : Set.InjOn f e0 := fun a _ b _ hab => hinj a b hab
  have hfin : (f '' e0).Finite := Finite.image f hf0
  haveI : DecidableEq V3 := Classical.decEq _
  refine ⟨hfin, ?_⟩
  have hinjOn' : Set.InjOn f (hf0.toFinset : Set V3) := by
    rw [hf0.coe_toFinset]
    exact hinjOn
  rw [Finite.toFinset_image f hf0 hfin, Finset.card_image_of_injOn hinjOn']
  exact hcard

/-- HOL `LUNAR_DEFORM_ORIGIN` (local_lemmas1.hl:821). -/
theorem LUNAR_DEFORM_ORIGIN (e1 e2 e3 : V3) (t : ℝ) : lunarDeform e1 e2 e3 t 0 = 0 := by
  simp [lunarDeform]

/-- HOL `CVLF_COLLINEAR_CIRCULAR_LUNAR` (local_lemmas1.hl:944). -/
theorem CVLF_COLLINEAR_CIRCULAR_LUNAR {v w : V3} (hcl : convexLocalFan_p2 V E FF)
    (hsub : ({v, w} : Set V3) ⊆ V) (hcol : Collinear3 0 v w) (hvw : v ≠ w) :
    circular_p2 V E ∨ lunar_p2 v w V E := by
  by_cases hc : circular_p2 V E
  · exact Or.inl hc
  · exact Or.inr ⟨hc, hsub, hvw, hcol⟩

/-! ## Continuity kit (HOL `continuous atreal` / `real_continuous atreal`
both ↦ `ContinuousAt`) -/

/-- HOL `TOW_REAL_EXISTS_COMBINED` (local_lemmas1.hl:959). -/
theorem TOW_REAL_EXISTS_COMBINED (P Q : ℝ → Prop)
    (h1 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → P t)
    (h2 : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → Q t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e → P t ∧ Q t := by
  obtain ⟨e1, he1, hP⟩ := h1
  obtain ⟨e2, he2, hQ⟩ := h2
  refine ⟨min e1 e2, lt_min he1 he2, fun t ht => ⟨?_, ?_⟩⟩
  · exact hP t ⟨by linarith [min_le_left e1 e2, min_le_right e1 e2],
      by linarith [min_le_left e1 e2, min_le_right e1 e2]⟩
  · exact hQ t ⟨by linarith [min_le_left e1 e2, min_le_right e1 e2],
      by linarith [min_le_left e1 e2, min_le_right e1 e2]⟩

/-- HOL `CONTINUOUS_FUNS_DISTINCT_POINTS` (local_lemmas1.hl:990). -/
theorem CONTINUOUS_FUNS_DISTINCT_POINTS (f g : ℝ → V3) (r rr : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g rr) (hne : f r ≠ g rr) :
    ∃ d : ℝ, 0 < d ∧ ∀ x y : ℝ, |x - r| < d ∧ |y - rr| < d → f x ≠ g y := by
  have heps : 0 < dist (f r) (g rr) / 2 :=
    half_pos (dist_pos.mpr hne)
  obtain ⟨df, hdf, htf⟩ := Metric.tendsto_nhds_nhds.mp hf _ heps
  obtain ⟨dg, hdg, htg⟩ := Metric.tendsto_nhds_nhds.mp hg _ heps
  refine ⟨min df dg, lt_min hdf hdg, ?_⟩
  intro x y hx
  by_contra hcon
  have e1 := htf (x := x) (by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx.1 (min_le_left df dg))
  have e2 := htg (x := y) (by
    rw [Real.dist_eq]
    exact lt_of_lt_of_le hx.2 (min_le_right df dg))
  rw [← hcon] at e2
  have t1 : dist (f r) (g rr) ≤ dist (f r) (f x) + dist (f x) (g rr) := dist_triangle _ _ _
  have t2 : dist (f x) (g rr) ≤ dist (f x) (g y) + dist (g y) (g rr) := dist_triangle _ _ _
  rw [← hcon, dist_self] at t2
  linarith [dist_comm (f r) (f x), dist_comm (f x) (g rr)]

/-- HOL `CONTINUOUS_TWO_POINTS_DISTINCT` (local_lemmas1.hl:1036). -/
theorem CONTINUOUS_TWO_POINTS_DISTINCT {ff : V3 → ℝ → V3} {v1 v2 : V3} {r : ℝ}
    (h1 : ContinuousAt (ff v1) r) (h2 : ContinuousAt (ff v2) r) (hne : ff v1 r ≠ ff v2 r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ff v1 t ≠ ff v2 t := by
  obtain ⟨d, hd, hall⟩ := CONTINUOUS_FUNS_DISTINCT_POINTS (ff v1) (ff v2) r r h1 h2 hne
  exact ⟨d, hd, fun t ht => hall t t ⟨ht, ht⟩⟩

/-- HOL `CONTINUOUS_ATREAL_DISTINCT` (local_lemmas1.hl:1155). -/
theorem CONTINUOUS_ATREAL_DISTINCT {ff : V3 → ℝ → V3} {v v0 : V3} {r : ℝ}
    (h : ContinuousAt (ff v) r) (hne : ff v r ≠ v0) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ff v t ≠ v0 := by
  have heps : 0 < dist v0 (ff v r) := dist_pos.mpr (Ne.symm hne)
  obtain ⟨d, hd, hlt⟩ := Metric.tendsto_nhds_nhds.mp h _ heps
  refine ⟨d, hd, fun t ht hcon => ?_⟩
  have hlt' := hlt (by rw [Real.dist_eq]; exact ht)
  rw [hcon] at hlt'
  linarith

/-- HOL `CONTINUOUS_FUN_DISTINCT_FINITE_SET` (local_lemmas1.hl:1048). -/
theorem CONTINUOUS_FUN_DISTINCT_FINITE_SET {ff : V3 → ℝ → V3} {r : ℝ} {v0 : V3} (V : Set V3)
    (hV : V.Finite) (h1 : ∀ v1 ∈ V, v1 ≠ v0 → ff v0 r ≠ ff v1 r)
    (h2 : ∀ v ∈ insert v0 V, ContinuousAt (ff v) r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, v1 ≠ v0 → ff v0 t ≠ ff v1 t :=
  sorry

/-- HOL `CONTINUOUS_ATREAL_INJ_PRESERVED` (local_lemmas1.hl:1100). -/
theorem CONTINUOUS_ATREAL_INJ_PRESERVED {ff : V3 → ℝ → V3} {r : ℝ} (V : Set V3)
    (hV : V.Finite) (h1 : ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 r ≠ ff v2 r)
    (h2 : ∀ v ∈ V, ContinuousAt (ff v) r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d →
      ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 t ≠ ff v2 t :=
  sorry

/-- HOL `CONTINUOUS_ATREAL_DISTINCT_FINITE` (local_lemmas1.hl:1177). -/
theorem CONTINUOUS_ATREAL_DISTINCT_FINITE {ff : V3 → ℝ → V3} {r : ℝ} {v0 : V3} (V : Set V3)
    (hV : V.Finite) (h1 : ∀ v1 ∈ V, ff v1 r ≠ v0)
    (h2 : ∀ v ∈ V, ContinuousAt (ff v) r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, ff v1 t ≠ v0 :=
  sorry

/-- HOL `CON_ATREAL_REAL_CON` (local_lemmas1.hl:1211). -/
theorem CON_ATREAL_REAL_CON (f : ℝ → V3) (t : ℝ) (h : ContinuousAt f t) :
    ContinuousAt (fun s => dist (f s) v0) t := h.dist continuousAt_const

/-- HOL `CON_ATREAL_REAL_CON2` (local_lemmas1.hl:1221). -/
theorem CON_ATREAL_REAL_CON2 (f g : ℝ → V3) (t : ℝ) (h1 : ContinuousAt f t)
    (h2 : ContinuousAt g t) : ContinuousAt (fun s => dist (f s) (g s)) t := h1.dist h2

/-- HOL `CON_ATREAL_REAL_CON2_REDO` (local_lemmas1.hl:6010). -/
theorem CON_ATREAL_REAL_CON2_REDO (f g : ℝ → V3) (r : ℝ) (h1 : ContinuousAt f r)
    (h2 : ContinuousAt g r) : ContinuousAt (fun s => dist (f s) (g s)) r := h1.dist h2

/-- HOL `SET2_HAS_SIZE2` (local_lemmas1.hl:1248); `HAS_SIZE 2` ↦ `ncard = 2`. -/
theorem SET2_HAS_SIZE2 {α : Type*} (a b : α) : ({a, b} : Set α).ncard = 2 ↔ a ≠ b := by
  rw [Set.ncard_eq_two]
  constructor
  · rintro ⟨x, y, hxy, heq⟩ hac
    have h1 : ({a, b} : Set α) = {a} := by rw [hac]; simp
    have hx : x ∈ ({a, b} : Set α) := by rw [heq]; simp
    have hy : y ∈ ({a, b} : Set α) := by rw [heq]; simp
    rw [h1] at hx hy
    exact hxy (hx.trans hy.symm)
  · rintro hne
    exact ⟨a, b, hne, rfl⟩

/-- HOL `DIJ_AFF_GE_PARTITION` (local_lemmas1.hl:1265) — giant. -/
theorem DIJ_AFF_GE_PARTITION {u v w : V3} (h : Disjoint ({u, v} : Set V3) ({w} : Set V3)) :
    affGe ({u, v} : Set V3) ({w} : Set V3) =
      {z | z ∈ affineSpan ℝ ({u, v} : Set V3)} ∪
        affGt ({u, v} : Set V3) ({w} : Set V3) :=
  sorry

/-- HOL `AFF_GE_WEDGE_DISJOINTION` (local_lemmas1.hl:1296) — giant. -/
theorem AFF_GE_WEDGE_DISJOINTION (v0 v1 w1 w2 : V3) :
    affGe ({v0, v1} : Set V3) ({w1} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅ ∧
      affGe ({v0, v1} : Set V3) ({w2} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅ :=
  sorry

/-- HOL `HAS_SIZE_2_EXISTS2` (local_lemmas1.hl:1335). -/
theorem HAS_SIZE_2_EXISTS2 {α : Type*} (S : Set α) :
    S.ncard = 2 ↔ ∃ x y : α, x ≠ y ∧ S = {x, y} :=
  Set.ncard_eq_two

/-! ## Edge/wedge basics, EE -/

/-- HOL `FAN_E_SUB_V` (local_lemmas1.hl:1344). -/
theorem FAN_E_SUB_V {x y : V3} (h : FAN 0 V E) (he : {x, y} ∈ E) : x ∈ V ∧ y ∈ V := by
  have h0 := h.1
  exact ⟨h0 (Set.subset_sUnion_of_mem he (by simp)),
    h0 (Set.subset_sUnion_of_mem he (by simp))⟩

/-- HOL `LOCAL_E_SUB_V` (local_lemmas1.hl:1350). -/
theorem LOCAL_E_SUB_V {x y : V3} (h : localFan_p2 V E FF) (he : {x, y} ∈ E) :
    x ∈ V ∧ y ∈ V := by
  obtain ⟨HS, _, _, _, _, hFAN, _, _⟩ := h
  exact FAN_E_SUB_V hFAN he

/-- HOL `EDGE_NOT_INTER_WITH_WEDGE` (local_lemmas1.hl:1358). -/
theorem EDGE_NOT_INTER_WITH_WEDGE (v0 v1 w1 w2 : V3) :
    ((affineSpan ℝ ({v0, v1} : Set V3) : Set V3) ∩ wedge v0 v1 w1 w2) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  by_cases hv : v0 = v1
  · exact hy2.1 (collinear3_of_eq hv.symm)
  · refine hy2.1 ?_
    show Collinear ℝ ({v0, v1, y} : Set V3)
    have hcol := collinear_insert_of_mem_affineSpan_pair (k := ℝ) hy1
    have hsub : ({v0, v1, y} : Set V3) ⊆ {y, v0, v1} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    exact Collinear.subset hsub hcol

/-- HOL `AFF_GE11_SUB_AFF2` (local_lemmas1.hl:1368). -/
theorem AFF_GE11_SUB_AFF2 (v0 v1 : V3) :
    affGe ({v0} : Set V3) ({v1} : Set V3) ⊆ affineSpan ℝ ({v0, v1} : Set V3) := by
  classical
  intro z hz
  obtain ⟨f, hfin, hz', hpos, hsum⟩ := hz
  by_cases hv0v1 : v0 = v1
  · subst hv0v1
    have hts : hfin.toFinset = {v0} := by ext u; simp [hfin.mem_toFinset]
    rw [hts, Finset.sum_singleton] at hsum hz'
    have hgoal : z ∈ affineSpan ℝ ({v0, v0} : Set V3) := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨f v0, ?_⟩
      rw [AffineMap.lineMap_apply_module', hz', hsum, one_smul, sub_self, zero_add,
        one_smul]
    exact hgoal
  · have hts : hfin.toFinset = insert v0 (insert v1 ∅ : Finset V3) := by
      ext u; simp [hfin.mem_toFinset, hv0v1]; tauto
    rw [hts, Finset.sum_insert (by simp [hv0v1]), Finset.sum_insert (by simp),
      Finset.sum_empty] at hz' hsum
    have hgoal : z ∈ affineSpan ℝ ({v0, v1} : Set V3) := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨f v1, ?_⟩
      rw [AffineMap.lineMap_apply_module', hz']
      have hsum' : f v0 = 1 - f v1 := by rw [← hsum]; ring
      rw [hsum']
      module
    rw [affineSpan_affineSpan]
    exact hz

/-- HOL `AZ_REFL11` (local_lemmas1.hl:2132): CONJUNCT1 of `AZIM_DEGENERATE`
refl-dropped. -/
theorem AZ_REFL11 (v w1 w2 : V3) : azim v v w1 w2 = 0 := by
  rw [azim, if_pos (Or.inl (collinear3_of_eq rfl))]

/-- HOL `AZIM_POS_IMP_CYCLIC_SET` (local_lemmas1.hl:2138) — giant. -/
theorem AZIM_POS_IMP_CYCLIC_SET {v0 v1 w1 w2 : V3} (h : 0 < azim v0 v1 w1 w2) :
    cyclicSet_p3 {w1, w2} v0 v1 :=
  sorry

/-- HOL `AZIM_POS_IMP_SUM_2PI` (local_lemmas1.hl:2223). -/
theorem AZIM_POS_IMP_SUM_2PI {a b c d : V3} (h : 0 < azim a b c d) :
    azim a b c d + azim a b d c = 2 * Real.pi := by
  have hnc : ¬ (Collinear3 a b c ∨ Collinear3 a b d) := by
    intro hc
    rw [azim, if_pos hc] at h
    norm_num at h
  have h1 : ¬ Collinear3 a b c := fun hc => hnc (Or.inl hc)
  have h2 : ¬ Collinear3 a b d := fun hc => hnc (Or.inr hc)
  rw [azim_compl h1 h2, if_neg (by linarith)]
  linarith

/-- HOL `FST_LST_IN_WEDGE_GE` (local_lemmas1.hl:3858). -/
theorem FST_LST_IN_WEDGE_GE (v0 v1 w1 w2 : V3) :
    w1 ∈ wedgeGe_p2 v0 v1 w1 w2 ∧ w2 ∈ wedgeGe_p2 v0 v1 w1 w2 := by
  constructor
  · exact ⟨azim_nonneg _ _ _ _, by rw [azim_self]; exact azim_nonneg _ _ _ _⟩
  · exact ⟨azim_nonneg _ _ _ _, le_refl _⟩

/-- HOL `EE_UNION` (local_lemmas1.hl:2070). -/
theorem EE_UNION (v : V3) (E S : Set (Set V3)) :
    EE_p2 v (E ∪ S) = EE_p2 v E ∪ EE_p2 v S := by
  ext x; simp [EE_p2]

/-- HOL `EE_SING_SING` (local_lemmas1.hl:2079). -/
theorem EE_SING_SING (v w : V3) : EE_p2 v {{v, w}} = {w} := by
  ext x
  simp only [EE_p2, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.pair_eq_pair_iff, false_or]
  refine ⟨?_, ?_⟩
  · rintro (⟨_, h2⟩ | ⟨h1, h2⟩)
    · exact h2
    · exact h2.trans h1
  · intro hx
    exact Or.inl ⟨True.intro, hx⟩

/-- HOL `IN_DARTS_EXTENSION` (local_lemmas1.hl:1846). -/
theorem IN_DARTS_EXTENSION {x y : V3} {E S : Set (Set V3)} (h : {x, y} ∈ E) :
    (x, y) ∈ dartsOfHyp_p2 (E ∪ S) V := by
  refine Or.inl ?_
  show {x, y} ∈ E ∪ S
  exact Or.inl h

/-- HOL `LOCAL_RHO_NODE_PAIR_E` (local_lemmas1.hl:1857) — giant. -/
theorem LOCAL_RHO_NODE_PAIR_E (h : localFan_p2 V E FF) (hv : v ∈ V) :
    {v, rhoNode1_p2 FF v} ∈ E :=
  sorry

/-- HOL `CROSS_PAIR_NOT_IN_FF` (local_lemmas1.hl:2088) — giant. -/
theorem CROSS_PAIR_NOT_IN_FF (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    (v, w) ∉ FF :=
  sorry

/-- HOL `LOFA_IMP_ITER_RHO_NODE_ID2` (local_lemmas1.hl:4808;
`Local_lemmas.LOFA_IMP_ITER_RHO_NODE_ID` is external, not ported) — giant. -/
theorem LOFA_IMP_ITER_RHO_NODE_ID2 (h : localFan_p2 V E FF) (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard] v = v :=
  sorry

/-! ## Slicing chapter: the local-fan half-circle kit (giants, stated
verbatim over the `_p2` kit) -/

/-- HOL `PROVE_SLICING_FAN` (local_lemmas1.hl:1378) — giant. -/
theorem PROVE_SLICING_FAN (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    FAN 0 V (E ∪ {{v, w}}) :=
  sorry

/-- HOL `FACE_MAP_ADD_SET2_EQ` (local_lemmas1.hl:1725) — giant. -/
theorem FACE_MAP_ADD_SET2_EQ (HS1 HS2 : Hypermap (V3 × V3)) (a b x y : V3)
    (hd : (x, y) ∈ dartsOfHyp_p2 (E ∪ {{a, b}}) V) (hya : y ≠ a) (hyb : y ≠ b)
    (hE1 : FAN 0 V E) (hE2 : FAN 0 V (E ∪ {{a, b}}))
    (hHS1 : IsHyp_p2 0 V (E ∪ {{a, b}}) HS1) (hHS2 : IsHyp_p2 0 V E HS2) :
    HS1.faceMap (x, y) = HS2.faceMap (x, y) :=
  sorry

/-- HOL `LOCAL_FACE_MAP_RHO_NODE1` (local_lemmas1.hl:1789) — giant. -/
theorem LOCAL_FACE_MAP_RHO_NODE1 (h : localFan_p2 V E FF)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V E HS) (hd : (x, y) ∈ FF) :
    HS.faceMap (x, y) = (rhoNode1_p2 FF x, rhoNode1_p2 FF y) :=
  sorry

/-- HOL `LOFA_HYP_UNION_CARD_GT2` (local_lemmas1.hl:1868) — giant. -/
theorem LOFA_HYP_UNION_CARD_GT2 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    2 < fv.ncard :=
  sorry

/-- HOL `LOCAL_FAN_SIMPLE_HYP` (local_lemmas1.hl:2050) — giant. -/
theorem LOCAL_FAN_SIMPLE_HYP (h : localFan_p2 V E FF)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V E HS) : HS.Simple :=
  sorry

/-- HOL `FACE_MAP_AT_TURNING_DART` (local_lemmas1.hl:2233) — giant. -/
theorem FACE_MAP_AT_TURNING_DART (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hxv : (x, v) ∈ FF) :
    HS.faceMap (x, v) = (v, w) :=
  sorry

/-- HOL `WEDGE_IN_FAN_LOFA_DETER` (local_lemmas1.hl:2422) — giant. -/
theorem WEDGE_IN_FAN_LOFA_DETER (h : localFan_p2 V E FF) (hv : v ∈ V)
    (hw : rhoNode1_p2 FF v = w) :
    wedgeInFanGt_p2 (w, rhoNode1_p2 FF w) E = wedge 0 w (rhoNode1_p2 FF w) v :=
  sorry

/-- HOL `FACE_MAP_SLICING_HYP_TRANS_POINT` (local_lemmas1.hl:2443) — giant. -/
theorem FACE_MAP_SLICING_HYP_TRANS_POINT (h : localFan_p2 V E FF) (hv : v ∈ V)
    (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS) :
    HS.faceMap (v, w) = (w, rhoNode1_p2 FF w) :=
  sorry

/-- HOL `FACE_MAP_AT_TURNING_DART1` (local_lemmas1.hl:2641) — giant. -/
theorem FACE_MAP_AT_TURNING_DART1 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hxw : (x, w) ∈ FF) :
    HS.faceMap (x, w) = (w, v) :=
  sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_VITERFF` (local_lemmas1.hl:2659) — giant. -/
theorem LOCAL_FAN_ORBIT_MAP_VITERFF (h : localFan_p2 V E FF) (hv : v ∈ V) (n : ℕ) :
    ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v) ∈ FF :=
  sorry

/-- HOL `DETERMINE_FV` (local_lemmas1.hl:2672) — giant. -/
theorem DETERMINE_FV (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    fv = insert (w, v) {p | ∃ n : ℕ,
      (∀ m : ℕ, m < n + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
        p = ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v)} :=
  sorry

/-- HOL `CARD_IS_LEAST_CYCLE` (local_lemmas1.hl:3056) — giant. -/
theorem CARD_IS_LEAST_CYCLE (h : localFan_p2 V E FF) (hv : v ∈ V) (n : ℕ)
    (hn : (rhoNode1_p2 FF)^[n] v = v) (hnz : n ≠ 0) : V.ncard ≤ n :=
  sorry

/-- HOL `HAFL_CIRCLE_FORM_LOCAL_FAN` (local_lemmas1.hl:3077) — giant. -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv :=
  sorry

/-- HOL `HAFL_CIRCLE_FORM_LOCAL_FAN2` (local_lemmas1.hl:3742) — giant. -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN2 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      localFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw :=
  sorry

/-- HOL `LOCAL_FAN_RHO_NODE_IVS` (local_lemmas1.hl:3768) — giant. -/
theorem LOCAL_FAN_RHO_NODE_IVS (h : localFan_p2 V E FF) (hv : v ∈ V) :
    rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v :=
  sorry

/-- HOL `LOCAL_FAN_IVS_IN_V` (local_lemmas1.hl:3797) — giant. -/
theorem LOCAL_FAN_IVS_IN_V (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ivsRhoNode1_p2 FF v ∈ V :=
  sorry

/-- HOL `LF_AZIM_CYCLE_EQ_IVS_ND` (local_lemmas1.hl:3807) — giant. -/
theorem LF_AZIM_CYCLE_EQ_IVS_ND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v) = ivsRhoNode1_p2 FF v :=
  sorry

/-- HOL `AZIM_IN_FAN_RHOND_IVS_RHOND` (local_lemmas1.hl:3820) — giant. -/
theorem AZIM_IN_FAN_RHOND_IVS_RHOND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    azimInFan_p2 (v, rhoNode1_p2 FF v) E =
      azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) :=
  sorry

/-- HOL `LOFA_IMP_EE_TWO_ELMS_INS_ND` (local_lemmas1.hl:3834) — giant. -/
theorem LOFA_IMP_EE_TWO_ELMS_INS_ND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    EE_p2 v E = {rhoNode1_p2 FF v, ivsRhoNode1_p2 FF v} :=
  sorry

/-- HOL `WEDGE_IN_FAN_RHOND_IVS_RHOND` (local_lemmas1.hl:3844) — giant. -/
theorem WEDGE_IN_FAN_RHOND_IVS_RHOND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    wedgeInFanGe_p2 (v, rhoNode1_p2 FF v) E =
      wedgeGe_p2 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) :=
  sorry

/-- HOL `IVS_RHO_NODE_DIFF_ID` (local_lemmas1.hl:3866) — giant. -/
theorem IVS_RHO_NODE_DIFF_ID (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ivsRhoNode1_p2 FF v ≠ v :=
  sorry

/-- HOL `POINT_PRESENTED_IN_RHOND1` (local_lemmas1.hl:3877) — giant. -/
theorem POINT_PRESENTED_IN_RHOND1 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ n : ℕ, n < V.ncard ∧ (rhoNode1_p2 FF)^[n] v = w ∧
      (∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) :=
  sorry

/-- HOL `POINTS_IN_HAFL_CIRCLE` (local_lemmas1.hl:3894) — giant. -/
theorem POINTS_IN_HAFL_CIRCLE (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    vPrime_p2 V fv = {z | ∃ n : ℕ,
      (∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
        z = (rhoNode1_p2 FF)^[n] v} :=
  sorry

/-- HOL `COVEX_OF_LOFA_HALF_CIRCLE` (local_lemmas1.hl:3973) — giant. -/
theorem COVEX_OF_LOFA_HALF_CIRCLE (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv :=
  sorry

/-- HOL `COVEX_OF_LOFA_HALF_CIRCLE2` (local_lemmas1.hl:4650) — giant. -/
theorem COVEX_OF_LOFA_HALF_CIRCLE2 (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw :=
  sorry

/-- HOL `CARD_V_TWO_HAFL_CIRCLE` (local_lemmas1.hl:4671) — giant. -/
theorem CARD_V_TWO_HAFL_CIRCLE (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) (n n' : ℕ) (hn : (rhoNode1_p2 FF)^[n] v = w)
    (hn' : (rhoNode1_p2 FF)^[n'] w = v) (hnc : n < V.ncard) (hn'c : n' < V.ncard) :
    n + n' = V.ncard :=
  sorry

/-- HOL `DIFFERENCE_IMP_LT_CARDV` (local_lemmas1.hl:4721) — giant. -/
theorem DIFFERENCE_IMP_LT_CARDV (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (m : ℕ) (hm : ∀ n : ℕ, n < m → ¬((rhoNode1_p2 FF)^[n] v = w)) :
    m < V.ncard :=
  sorry

/-- HOL `LT_CARD_MONO_LOFA` (local_lemmas1.hl:4746) — giant. -/
theorem LT_CARD_MONO_LOFA (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ∀ i j : ℕ, i < V.ncard ∧ j < V.ncard ∧ (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[j] v →
      i = j :=
  sorry

/-- HOL `CONDS_IN_V_PRIME_NUM` (local_lemmas1.hl:4759) — giant. -/
theorem CONDS_IN_V_PRIME_NUM (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w) :
    ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv ↔ i < n + 1 :=
  sorry

/-- HOL `CONDS_IN_V_PRIME_NUM2` (local_lemmas1.hl:4816) — giant. -/
theorem CONDS_IN_V_PRIME_NUM2 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w))
    (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w) :
    ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw ↔
      i = 0 ∨ n ≤ i ∧ i < V.ncard :=
  sorry

/-- HOL `DETERMINE_FV2` (local_lemmas1.hl:4935) — giant. -/
theorem DETERMINE_FV2 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w) :
    fv = insert (w, v) {p | ∃ m : ℕ, m < n ∧
      p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} :=
  sorry

/-- HOL `INTERIOR_ANGLE_LEM_SLICING_FAN` (local_lemmas1.hl:4988) — giant. -/
theorem INTERIOR_ANGLE_LEM_SLICING_FAN (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    interiorAngle1_p2 0 fv v + interiorAngle1_p2 0 fw v = interiorAngle1_p2 0 FF v :=
  sorry

/-- HOL `INTERIOR_ANGLE_LEM_SLICING_FAN2` (local_lemmas1.hl:5121) — giant. -/
theorem INTERIOR_ANGLE_LEM_SLICING_FAN2 (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    interiorAngle1_p2 0 fv v + interiorAngle1_p2 0 fw v = interiorAngle1_p2 0 FF v ∧
      interiorAngle1_p2 0 fw w + interiorAngle1_p2 0 fv w = interiorAngle1_p2 0 FF w :=
  sorry

/-- HOL `INTERIOR_AGL_EQ` (local_lemmas1.hl:5148) — giant. -/
theorem INTERIOR_AGL_EQ (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w) :
    ∀ i : ℕ, 0 < i ∧ i < n →
      interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v) =
        interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v) :=
  sorry

/-- HOL `SUM_INTERIOR_AGL_LEMMA` (local_lemmas1.hl:5212) — giant. -/
theorem SUM_INTERIOR_AGL_LEMMA (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    ∀ g : ℕ → ℝ,
      setSum {i | i < V.ncard}
          (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
        setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv}
            (fun i => g i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) +
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw}
            (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) :=
  sorry

/-- HOL `THE_SLICING_INTO_2_LEMMA` (local_lemmas1.hl:5580) — giant. -/
theorem THE_SLICING_INTO_2_LEMMA (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw ∧
      (∀ g : ℕ → ℝ,
        setSum {i | i < V.ncard}
            (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv}
              (fun i => g i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) +
            setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw}
              (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v))) :=
  sorry

/-- HOL `WEDGE_IN_FAN_LOFA_DETER2` (local_lemmas1.hl:5609) — giant. -/
theorem WEDGE_IN_FAN_LOFA_DETER2 (h : localFan_p2 V E FF) (hv : v ∈ V) :
    wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E =
      wedge 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) :=
  sorry

/-- HOL `AZIM_COND_FOR_COPLANAR` (local_lemmas1.hl:5620) — giant. -/
theorem AZIM_COND_FOR_COPLANAR (v0 v1 w1 w2 : V3) :
    azim v0 v1 w1 w2 = 0 ∨ azim v0 v1 w1 w2 = Real.pi ↔ Coplanar {v0, v1, w1, w2} :=
  sorry

/-- HOL `AFF_SUB_PLANE` (local_lemmas1.hl:5640). -/
theorem AFF_SUB_PLANE (P : Set V3) (hP : plane_p2 P) {S : Set V3} (hS : S ⊆ P) :
    ∀ z ∈ affineSpan ℝ S, z ∈ P :=
  sorry

/-- HOL `PROVE_THE_SLICE_ASSUMPTION` (local_lemmas1.hl:5647) — giant. -/
theorem PROVE_THE_SLICE_ASSUMPTION (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V)
    (hw : w ∈ V) (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) :=
  sorry

/-- HOL `EJRCFJD` (local_lemmas1.hl:5967) — giant. -/
theorem EJRCFJD (hcl : convexLocalFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv ∧
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw ∧
      (∀ g : ℕ → ℝ,
        setSum {i | i < V.ncard}
            (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
          setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv}
              (fun i => g i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) +
            setSum {i | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw}
              (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v))) :=
  sorry

/-- HOL `DIST_TRIANGLE_AS_ABS` (local_lemmas1.hl:6001). -/
theorem DIST_TRIANGLE_AS_ABS (x y z : V3) : |dist x y - dist x z| ≤ dist y z := by
  have h1 : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  have h2 : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  rw [abs_le]
  constructor <;> linarith [dist_comm y z]

/-- HOL `REAL_POS_LT_MUL` (local_lemmas1.hl:6057). -/
theorem REAL_POS_LT_MUL {a b x y : ℝ} (ha : 0 ≤ a) (hab : a < b) (hx : 0 ≤ x)
    (hxy : x < y) : a * x < b * y := by
  nlinarith

/-- HOL `LUNAR_DEFORM_PRESERVE_NORM` (local_lemmas1.hl:43) — giant
(needs the spherical-coordinate expansion of `x` in the frame). -/
theorem LUNAR_DEFORM_PRESERVE_NORM {e1 e2 e3 : V3} (horth : Orthonormal3 e1 e2 e3)
    (t : ℝ) (x : V3) : ‖lunarDeform e1 e2 e3 t x‖ = ‖x‖ :=
  sorry

/-- HOL `COS_ARCV` (local_lemmas1.hl:827). -/
theorem COS_ARCV (v0 u w : V3) :
    Real.cos (arcV v0 u w) =
      (u - v0) ⬝ᵥ (w - v0) / (‖u - v0‖ * ‖w - v0‖) := by
  have key := NORM_CAUCHY_SCHWARZ_FRAC2 (u - v0) (w - v0)
  rw [← inner_eq_dot] at key
  rw [arcV_eq, dist_eq_norm, dist_eq_norm, ← inner_eq_dot]
  exact Real.cos_arccos key.1 key.2

/-- HOL `REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN` (local_lemmas1.hl:6070). -/
theorem REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN (f g : ℝ → ℝ) (r : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) :
    ContinuousAt (fun t => f t * g t) r := hf.mul hg

/-- HOL `REAL_CONTINUOUS_ATREAL_POW_2` (local_lemmas1.hl:6150). -/
theorem REAL_CONTINUOUS_ATREAL_POW_2 (f : ℝ → ℝ) (r : ℝ)
    (h : ContinuousAt f r) : ContinuousAt (fun t => f t ^ 2) r := by
  have h2 : (fun t => f t * f t) =ᶠ[nhds r] fun t => f t ^ 2 := by
    filter_upwards with t
    exact (pow_two (f t)).symm
  exact (REAL_CONTINUOUS_ATREAL_IMP_MUL_FUN f f r h h).congr h2

/-- HOL `CONSTANCE_FUN_CONTINUOUS` (local_lemmas1.hl:6157). -/
theorem CONSTANCE_FUN_CONTINUOUS (c : ℝ) (r : ℝ) :
    ContinuousAt (fun _ : ℝ => c) r := continuousAt_const

/-- HOL `REAL_CONS_IMP_SCALAR_MUL` (local_lemmas1.hl:6163). -/
theorem REAL_CONS_IMP_SCALAR_MUL (f : ℝ → ℝ) (r : ℝ) (c : ℝ)
    (h : ContinuousAt f r) : ContinuousAt (fun t => c * f t) r :=
  continuousAt_const.mul h

/-- HOL `CONS_IMP_SO_IVS` (local_lemmas1.hl:6171). -/
theorem CONS_IMP_SO_IVS (f : ℝ → ℝ) (r : ℝ) (h : ContinuousAt f r) :
    ContinuousAt (fun t => -f t) r := h.neg

/-- HOL `REAL_CONS_IMP_SUM_CONS` (local_lemmas1.hl:6179). -/
theorem REAL_CONS_IMP_SUM_CONS (f g : ℝ → ℝ) (r : ℝ) (h1 : ContinuousAt f r)
    (h2 : ContinuousAt g r) : ContinuousAt (fun t => f t + g t) r := h1.add h2

/-- HOL `REAL_CONS_IMP_SCALAR_MUL_ALT` (local_lemmas1.hl:6206). -/
theorem REAL_CONS_IMP_SCALAR_MUL_ALT (f : ℝ → ℝ) (r : ℝ)
    (h : ContinuousAt f r) (c : ℝ) : ContinuousAt (fun t => c * f t) r :=
  REAL_CONS_IMP_SCALAR_MUL f r c h

/-- HOL `CONTS_FUN_CONTINUOUS_ATREAL` (local_lemmas1.hl:6264). -/
theorem CONTS_FUN_CONTINUOUS_ATREAL (v0 : V3) (r : ℝ) :
    ContinuousAt (fun _ : ℝ => v0) r := continuousAt_const

/-- HOL `REAL_CONS_STILL_DIFF` (local_lemmas1.hl:6271). -/
theorem REAL_CONS_STILL_DIFF (f : ℝ → ℝ) (r a : ℝ)
    (h : ContinuousAt f r) (hne : f r ≠ a) :
    ∃ d : ℝ, 0 < d ∧ ∀ rr : ℝ, |rr - r| < d → f rr ≠ a := by
  have heps : 0 < |f r - a| :=
    lt_of_le_of_ne (abs_nonneg _) (by
      intro hh
      rw [eq_comm, abs_eq_zero] at hh
      exact hne (by linarith))
  obtain ⟨d, hd, hlt⟩ := Metric.tendsto_nhds_nhds.mp h _ heps
  refine ⟨d, hd, fun rr hr hcon => ?_⟩
  have hlt' := hlt (x := rr) (by rw [Real.dist_eq]; exact hr)
  rw [hcon, Real.dist_eq] at hlt'
  rw [abs_sub_comm] at hlt'
  linarith

/-- HOL `UPS_X_CONTS_FUNC` (local_lemmas1.hl:6210) — giant (ups_x
continuity; `ups_x` ↦ `upsX_p6`). -/
theorem UPS_X_CONTS_FUNC (f g h : ℝ → V3) (r : ℝ) (hf : ContinuousAt f r)
    (hg : ContinuousAt g r) (hh : ContinuousAt h r) :
    ContinuousAt
      (fun r => upsX_p6 (dist (f r) (g r) ^ 2) (dist (h r) (f r) ^ 2)
        (dist (g r) (h r) ^ 2)) r :=
  sorry

/-- HOL `CONTINUOUS_PRESERVE_COLLINEAR` (local_lemmas1.hl:6286) — giant. -/
theorem CONTINUOUS_PRESERVE_COLLINEAR (v0 : V3) (f g : ℝ → V3) (r : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r)
    (hnc : ¬ Collinear3 v0 (f r) (g r)) :
    ∃ e : ℝ, 0 < e ∧ ∀ r' : ℝ, |r - r'| < e → ¬ Collinear3 v0 (f r') (g r') :=
  sorry

/-- HOL `EACH_ELM_PRESERVED_IMP_ALLL` (local_lemmas1.hl:6316) — giant. -/
theorem EACH_ELM_PRESERVED_IMP_ALLL (phii : V3 → ℝ → V3) (E : Set (Set V3))
    (h1 : ∀ x ∈ E, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      ¬ Collinear ℝ (Set.insert (0 : V3) ((fun v : V3 => phii v t) '' x)))
    (hE : E.Finite) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      ∀ e' ∈ (fun x : Set V3 => (fun v : V3 => phii v t) '' x) '' E,
        ¬ Collinear ℝ (Set.insert (0 : V3) e') :=
  sorry

/-- HOL `ALL_TO_THE_NONPARALLEL_PART` (local_lemmas1.hl:6378) — giant. -/
theorem ALL_TO_THE_NONPARALLEL_PART (phii : V3 → ℝ → V3) (V : Set V3) (E : Set (Set V3))
    (a b : ℝ) (hdef : deformation_p2 phii V a b) (hfan : FAN 0 V E) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, -e < t ∧ t < e →
      (⋃₀ ((fun s : Set V3 => (fun v : V3 => phii v t) '' s) '' E)) ⊆
          (fun v : V3 => phii v t) '' V ∧
        Graph ((fun s : Set V3 => (fun v : V3 => phii v t) '' s) '' E) ∧
        fan1 0 ((fun v : V3 => phii v t) '' V)
          ((fun s : Set V3 => (fun v : V3 => phii v t) '' s) '' E) ∧
        fan2 0 ((fun v : V3 => phii v t) '' V)
          ((fun s : Set V3 => (fun v : V3 => phii v t) '' s) '' E) ∧
        fan6 0 ((fun v : V3 => phii v t) '' V)
          ((fun s : Set V3 => (fun v : V3 => phii v t) '' s) '' E) :=
  sorry

end Kepler.Text
