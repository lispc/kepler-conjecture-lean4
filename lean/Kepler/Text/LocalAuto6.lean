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
- HOL `ups_x` ↦ copy `upsX_p6`. DEDUP (atn2-merge pass): NOT a twin —
  SphereKit's `upsX` is the sphere.hl Gram form; `upsX_p6` renders the
  packing_defs `½(x1+x2+x6+√…)` function and STAYS here (plan §3).
- The local-fan slicing chapter (FACE_MAP_*, HAFL_CIRCLE_*, DETERMINE_FV*,
  SUM_INTERIOR_AGL_LEMMA, THE_SLICING_INTO_2_LEMMA, EJRCFJD, ...) is
  stated verbatim with `sorry` (giants); the arcV / wedge / continuity /
  real-arithmetic kit is proved.
-/

import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto5
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
    ∃ u : V3, u ∈ affineSpan ℝ ({0, x, y} : Set V3) ∧ ‖u‖ = 1 ∧ x ⬝ᵥ u = 0 := by
  have hx0 : x ≠ 0 := by
    intro hx
    apply h
    show Collinear ℝ ({0, x, y} : Set V3)
    rw [hx]
    have hset : ({0, 0, y} : Set V3) = {0, y} := by simp
    rw [hset]
    exact collinear_pair ℝ 0 y
  set v : V3 := (x ⬝ᵥ y) • x - (x ⬝ᵥ x) • y with hv
  have hxx_pos : 0 < x ⬝ᵥ x := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    positivity
  have hv0 : v ≠ 0 := by
    intro hvz
    have h1 : (x ⬝ᵥ x) • y = (x ⬝ᵥ y) • x := by
      rw [hv] at hvz
      exact (sub_eq_zero.mp hvz).symm
    have hy_eq : y = ((x ⬝ᵥ y) / (x ⬝ᵥ x)) • x := by
      calc y = (x ⬝ᵥ x)⁻¹ • ((x ⬝ᵥ x) • y) := by
                rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hxx_pos), one_smul]
           _ = (x ⬝ᵥ x)⁻¹ • ((x ⬝ᵥ y) • x) := by rw [h1]
           _ = ((x ⬝ᵥ y) / (x ⬝ᵥ x)) • x := by rw [smul_smul, div_eq_inv_mul]
    exact h ((collinear3_iff_smul (w := x) (v := 0) (w1 := y) hx0).mpr
      ⟨_, by simpa using hy_eq⟩)
  have hform : normize v = ((1/‖v‖) * (x ⬝ᵥ y)) • x + (-((1/‖v‖) * (x ⬝ᵥ x))) • y := by
    rw [normize, hv, smul_sub, smul_smul, smul_smul]
    module
  have hnormv : ‖normize v‖ = 1 := by
    have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv')
    rw [normize, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hvp)]
    field_simp
  refine ⟨normize v, ?_, hnormv, ?_⟩
  · have h0mem : (0:V3) ∈ ({0, x, y} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
    have hxmem : x ∈ ({0, x, y} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
    have hymem : y ∈ ({0, x, y} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> tauto
    have hxdir : x ∈ vectorSpan ℝ ({0, x, y} : Set V3) := by
      have h := vsub_mem_vectorSpan ℝ (p₁ := x) (p₂ := (0:V3)) hxmem h0mem
      simpa using h
    have hydir : y ∈ vectorSpan ℝ ({0, x, y} : Set V3) := by
      have h := vsub_mem_vectorSpan ℝ (p₁ := y) (p₂ := (0:V3)) hymem h0mem
      simpa using h
    have hdir : ((1/‖v‖) * (x ⬝ᵥ y)) • x + (-((1/‖v‖) * (x ⬝ᵥ x))) • y
        ∈ vectorSpan ℝ ({0, x, y} : Set V3) :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxdir) (Submodule.smul_mem _ _ hydir)
    rw [hform]
    have h0asp : (0:V3) ∈ affineSpan ℝ ({0, x, y} : Set V3) := mem_affineSpan ℝ h0mem
    have hdir' : ((1/‖v‖) * (x ⬝ᵥ y)) • x + (-((1/‖v‖) * (x ⬝ᵥ x))) • y
        ∈ (affineSpan ℝ ({0, x, y} : Set V3)).direction := by
      rw [direction_affineSpan]
      exact hdir
    have hvadd := AffineSubspace.vadd_mem_of_mem_direction hdir' h0asp
    simpa using hvadd
  · rw [← inner_eq_dot, hform]
    simp only [inner_add_right, real_inner_smul_right, inner_eq_dot]
    ring

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
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, v1 ≠ v0 → ff v0 t ≠ ff v1 t := by
  revert h1 h2
  refine Set.Finite.induction_on V hV ?h0 ?hstep
  · intro h1 h2
    exact ⟨1, one_pos, fun t _ v1 hv1 => absurd hv1 (Set.notMem_empty v1)⟩
  · intro a s ha hs ih h1 h2
    have h1s : ∀ v1 ∈ s, v1 ≠ v0 → ff v0 r ≠ ff v1 r :=
      fun v1 hv1 => h1 v1 (by simp only [Set.mem_insert_iff]; exact Or.inr hv1)
    have h2s : ∀ v ∈ insert v0 s, ContinuousAt (ff v) r := by
      intro v hv
      exact h2 v (by simp only [Set.mem_insert_iff] at hv ⊢; tauto)
    obtain ⟨d, hdpos, hd⟩ := ih h1s h2s
    by_cases hav : a = v0
    · refine ⟨d, hdpos, fun t ht v1 hv1 hne => ?_⟩
      simp only [Set.mem_insert_iff] at hv1
      rcases hv1 with hva | h
      · exact absurd (hva.trans hav) hne
      · exact hd t ht v1 h hne
    · have haCont : ContinuousAt (ff a) r := h2 a (by simp)
      have hv0Cont : ContinuousAt (ff v0) r := h2 v0 (by simp)
      have hne' : ff a r ≠ ff v0 r :=
        Ne.symm (h1 a (by simp) hav)
      obtain ⟨d', hd'pos, hd'⟩ := CONTINUOUS_TWO_POINTS_DISTINCT haCont hv0Cont hne'
      refine ⟨min d d', lt_min hdpos hd'pos, fun t ht v1 hv1 hne => ?_⟩
      have hmin1 : |t - r| < d := lt_of_lt_of_le ht (min_le_left _ _)
      have hmin2 : |t - r| < d' := lt_of_lt_of_le ht (min_le_right _ _)
      simp only [Set.mem_insert_iff] at hv1
      rcases hv1 with hva | hmem
      · rw [hva]
        exact fun hcon => hd' t hmin2 hcon.symm
      · exact hd t hmin1 v1 hmem hne

/-- HOL `CONTINUOUS_ATREAL_INJ_PRESERVED` (local_lemmas1.hl:1100). -/
theorem CONTINUOUS_ATREAL_INJ_PRESERVED {ff : V3 → ℝ → V3} {r : ℝ} (V : Set V3)
    (hV : V.Finite) (h1 : ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 r ≠ ff v2 r)
    (h2 : ∀ v ∈ V, ContinuousAt (ff v) r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d →
      ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → ff v1 t ≠ ff v2 t := by
  revert h1 h2
  refine Set.Finite.induction_on V hV ?h0 ?hstep
  · intro h1 h2
    exact ⟨1, one_pos, fun t _ v1 hv1 => absurd hv1 (Set.notMem_empty v1)⟩
  · intro a s ha hs ih h1 h2
    have h1s : ∀ v1 ∈ s, ∀ v2 ∈ s, v1 ≠ v2 → ff v1 r ≠ ff v2 r :=
      fun v1 hv1 v2 hv2 =>
        h1 v1 (by simp only [Set.mem_insert_iff]; exact Or.inr hv1)
          v2 (by simp only [Set.mem_insert_iff]; exact Or.inr hv2)
    have h2s : ∀ v ∈ s, ContinuousAt (ff v) r :=
      fun v hv => h2 v (by simp only [Set.mem_insert_iff]; exact Or.inr hv)
    obtain ⟨d, hdpos, hd⟩ := ih h1s h2s
    have h2a : ∀ v ∈ insert a s, ContinuousAt (ff v) r := h2
    have h1a : ∀ v1 ∈ s, v1 ≠ a → ff a r ≠ ff v1 r :=
      fun v1 hv1 hne =>
        h1 a (by simp) v1 (by simp only [Set.mem_insert_iff]; exact Or.inr hv1) (Ne.symm hne)
    obtain ⟨d', hd'pos, hd'⟩ := CONTINUOUS_FUN_DISTINCT_FINITE_SET s hs h1a h2a
    refine ⟨min d d', lt_min hdpos hd'pos, fun t ht v1 hv1 v2 hv2 hne => ?_⟩
    have hmin1 : |t - r| < d := lt_of_lt_of_le ht (min_le_left _ _)
    have hmin2 : |t - r| < d' := lt_of_lt_of_le ht (min_le_right _ _)
    simp only [Set.mem_insert_iff] at hv1 hv2
    rcases hv1 with hva | hvs
    · rcases hv2 with hva2 | hvs2
      · exact absurd (hva.trans hva2.symm) hne
      · rw [hva] at hne ⊢
        exact hd' t hmin2 v2 hvs2 (Ne.symm hne)
    · rcases hv2 with hva2 | hvs2
      · rw [hva2] at hne ⊢
        exact fun hcon => hd' t hmin2 v1 hvs hne hcon.symm
      · exact hd t hmin1 v1 hvs v2 hvs2 hne

/-- HOL `CONTINUOUS_ATREAL_DISTINCT_FINITE` (local_lemmas1.hl:1177). -/
theorem CONTINUOUS_ATREAL_DISTINCT_FINITE {ff : V3 → ℝ → V3} {r : ℝ} {v0 : V3} (V : Set V3)
    (hV : V.Finite) (h1 : ∀ v1 ∈ V, ff v1 r ≠ v0)
    (h2 : ∀ v ∈ V, ContinuousAt (ff v) r) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, |t - r| < d → ∀ v1 ∈ V, ff v1 t ≠ v0 := by
  revert h1 h2
  refine Set.Finite.induction_on V hV ?h0 ?hstep
  · intro h1 h2
    exact ⟨1, one_pos, fun t _ v1 hv1 => absurd hv1 (Set.notMem_empty v1)⟩
  · intro a s ha hs ih h1 h2
    have h1s : ∀ v1 ∈ s, ff v1 r ≠ v0 := fun v1 hv1 => h1 v1 (Set.mem_insert_of_mem a hv1)
    have h2s : ∀ v ∈ s, ContinuousAt (ff v) r :=
      fun v hv => h2 v (Set.mem_insert_of_mem a hv)
    obtain ⟨d, hdpos, hd⟩ := ih h1s h2s
    obtain ⟨d', hd'pos, hd'⟩ :=
      CONTINUOUS_ATREAL_DISTINCT (h2 a (by simp)) (h1 a (by simp))
    refine ⟨min d d', lt_min hdpos hd'pos, fun t ht v1 hv1 => ?_⟩
    have hmin1 : |t - r| < d := lt_of_lt_of_le ht (min_le_left _ _)
    have hmin2 : |t - r| < d' := lt_of_lt_of_le ht (min_le_right _ _)
    simp only [Set.mem_insert_iff] at hv1
    rcases hv1 with hva | hmem
    · rw [hva]
      exact hd' t hmin2
    · exact hd t hmin1 v1 hmem

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
        affGt ({u, v} : Set V3) ({w} : Set V3) := by
  have huw : u ≠ w := Set.disjoint_iff_forall_ne.mp h (Or.inl rfl) rfl
  have hvw : v ≠ w := Set.disjoint_iff_forall_ne.mp h (Or.inr rfl) rfl
  have hwu : w ≠ u := Ne.symm huw
  have hwv : w ≠ v := Ne.symm hvw
  ext z
  constructor
  · intro hz
    by_cases huv : u = v
    · have hsets : ({u, v} : Set V3) = {u} := by rw [huv]; simp
      rw [hsets] at hz ⊢
      rw [mem_affGe_singleton huw] at hz
      obtain ⟨t1, t2, ht2, hsum, hzeq⟩ := hz
      rcases eq_or_lt_of_le ht2 with ht20 | ht2pos
      · left
        have ht1 : t1 = 1 := by linarith
        rw [← ht20, zero_smul, add_zero, ht1, one_smul] at hzeq
        rw [← hzeq]
        exact subset_affineSpan ℝ _ (by simp)
      · right
        have hfin : (({u} : Set V3) ∪ ({w} : Set V3)).Finite :=
          (Set.finite_singleton u).union (Set.finite_singleton w)
        have hfs : hfin.toFinset = ({u, w} : Finset V3) := by
          ext q
          simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
            Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] <;> tauto
        set f : V3 → ℝ := fun q => (if q = u then t1 else 0) + (if q = w then t2 else 0)
          with hf
        have hfu : f u = t1 := by simp [hf, huw]
        have hfw : f w = t2 := by simp [hf, hwu]
        have hunot : u ∉ ({w} : Finset V3) := by
          simp only [Finset.mem_singleton]; exact huw
        refine ⟨f, hfin, ?_, ?_, ?_⟩
        · rw [hfs, Finset.sum_insert hunot, Finset.sum_singleton, hfu, hfw, ← hzeq]
        · intro q hq
          simp only [Set.mem_singleton_iff] at hq
          rw [hq, hfw]; exact ht2pos
        · rw [hfs, Finset.sum_insert hunot, Finset.sum_singleton, hfu, hfw]
          exact hsum
    · rw [mem_affGe_pair h huv] at hz
      obtain ⟨t1, t2, t3, ht3, hsum, hzeq⟩ := hz
      rcases eq_or_lt_of_le ht3 with ht30 | ht3pos
      · left
        change z ∈ affineSpan ℝ ({u, v} : Set V3)
        rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        have ht1 : t1 = 1 - t2 := by linarith
        refine ⟨t2, ?_⟩
        rw [AffineMap.lineMap_apply, hzeq, ← ht30, zero_smul, add_zero, ht1]
        simp only [vsub_eq_sub, vadd_eq_add]
        module
      · right
        rw [affGt_pair_iff huv hwu hwv]
        refine ⟨t3, ht3pos, t2, ?_⟩
        have ht1' : t1 = 1 - t2 - t3 := by linarith
        have hz' : z = (1 - t2 - t3) • u + t2 • v + t3 • w := by
          rw [hzeq, ht1']
        rw [hz']
        module
  · rintro (hz | hz)
    · have hzu : z ∈ affineSpan ℝ ({u, v} : Set V3) := hz
      by_cases huv : u = v
      · have hsets : ({u, v} : Set V3) = {u} := by rw [huv]; simp
        rw [hsets] at hzu
        have hzu' : z ∈ (affineSpan ℝ ({u} : Set V3) : Set V3) := hzu
        rw [show (affineSpan ℝ ({u} : Set V3) : Set V3) = {u} from by simp] at hzu'
        rw [hsets, hzu']
        rw [mem_affGe_singleton huw]
        exact ⟨1, 0, le_refl 0, by norm_num, by simp⟩
      · rw [mem_affGe_pair h huv]
        obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hzu
        refine ⟨1 - r, r, 0, le_refl 0, ?_, ?_⟩
        · ring
        · rw [← hr, AffineMap.lineMap_apply]
          simp only [vsub_eq_sub, vadd_eq_add]
          module
    · change Affsign (fun x => 0 < x) ({u, v} : Set V3) ({w} : Set V3) z at hz
      obtain ⟨f, hfin, hzvec, hpos, hone⟩ := hz
      exact ⟨f, hfin, hzvec, fun q hq => le_of_lt (hpos q hq), hone⟩

/-- HOL `AFF_GE_WEDGE_DISJOINTION` (local_lemmas1.hl:1296) — giant. -/
theorem AFF_GE_WEDGE_DISJOINTION (v0 v1 w1 w2 : V3) :
    affGe ({v0, v1} : Set V3) ({w1} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅ ∧
      affGe ({v0, v1} : Set V3) ({w2} : Set V3) ∩ wedge v0 v1 w1 w2 = ∅ := by
  have hwedge0 : Collinear3 v0 v1 w1 → wedge v0 v1 w1 w2 = ∅ := by
    intro hcol
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have h0 : 0 < azim v0 v1 w1 y := hy.2.1
    have haz : azim v0 v1 w1 y = 0 := by
      rw [azim]
      exact if_pos (Or.inl hcol)
    rw [haz] at h0
    exact lt_irrefl 0 h0
  constructor
  · by_cases hcol1 : Collinear3 v0 v1 w1
    · rw [hwedge0 hcol1, Set.inter_empty]
    · rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hyge, hyw⟩ := hy
      have haz : azim v0 v1 w1 y = 0 := (AZIM_EQ_0_GE_ALT2 v0 v1 w1 y hcol1).mpr hyge
      have h0 : 0 < azim v0 v1 w1 y := hyw.2.1
      rw [haz] at h0
      exact lt_irrefl 0 h0
  · by_cases hcol1 : Collinear3 v0 v1 w1
    · rw [hwedge0 hcol1, Set.inter_empty]
    · rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hyge, hyw⟩ := hy
      by_cases hcol2 : Collinear3 v0 v1 w2
      · have haz : azim v0 v1 w1 w2 = 0 := by
          rw [azim]
          exact if_pos (Or.inr hcol2)
        have h0 : 0 < azim v0 v1 w1 y := hyw.2.1
        have hlt : azim v0 v1 w1 y < azim v0 v1 w1 w2 := hyw.2.2
        rw [haz] at hlt
        linarith
      · have haz : azim v0 v1 w2 y = 0 := (AZIM_EQ_0_GE_ALT2 v0 v1 w2 y hcol2).mpr hyge
        have hgt : y ∈ affGt ({v0, v1} : Set V3) ({w2} : Set V3) :=
          (azim_eq_zero_iff_alt hcol2 hyw.1).mp haz
        have heq : azim v0 v1 w1 y = azim v0 v1 w1 w2 :=
          (azim_eq_azim_iff_alt hcol1 hyw.1 hcol2).mpr hgt
        have hlt : azim v0 v1 w1 y < azim v0 v1 w1 w2 := hyw.2.2
        linarith

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
    -- DEDUP-note fix (atn2-merge pass): the draft tail `rw [affineSpan_affineSpan]`
    -- referenced a nonexistent lemma; `hgoal` already has the goal's type.
    exact hgoal

/-- HOL `AZ_REFL11` (local_lemmas1.hl:2132): CONJUNCT1 of `AZIM_DEGENERATE`
refl-dropped. -/
theorem AZ_REFL11 (v w1 w2 : V3) : azim v v w1 w2 = 0 := by
  rw [azim, if_pos (Or.inl (collinear3_of_eq rfl))]

/-- HOL `AZIM_POS_IMP_CYCLIC_SET` (local_lemmas1.hl:2138) — giant. -/
theorem AZIM_POS_IMP_CYCLIC_SET {v0 v1 w1 w2 : V3} (h : 0 < azim v0 v1 w1 w2) :
    cyclicSet_p3 {w1, w2} v0 v1 := by
  have hne : v0 ≠ v1 := by
    intro hv
    rw [hv, AZ_REFL11] at h
    exact lt_irrefl 0 h
  have hn1 : ¬ Collinear3 v0 v1 w1 := by
    intro hc
    have h0 : azim v0 v1 w1 w2 = 0 := by
      rw [azim]; exact if_pos (Or.inl hc)
    rw [h0] at h
    exact lt_irrefl 0 h
  have hn2 : ¬ Collinear3 v0 v1 w2 := by
    intro hc
    have h0 : azim v0 v1 w1 w2 = 0 := by
      rw [azim]; exact if_pos (Or.inr hc)
    rw [h0] at h
    exact lt_irrefl 0 h
  have hn1' : ¬ Collinear ℝ ({v0, v1, w1} : Set V3) := hn1
  have hn2' : ¬ Collinear ℝ ({v0, v1, w2} : Set V3) := hn2
  have hdisj1 : Disjoint ({v0, v1} : Set V3) ({w1} : Set V3) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1 hz2
    rcases hz1 with h0 | h1
    · exact (fun he => hn1' (collinear3_pair_left he)) ((h0.symm.trans hz2).symm)
    · exact (fun he => hn1' (collinear3_pair_right he)) ((h1.symm.trans hz2).symm)
  have hdisj2 : Disjoint ({v0, v1} : Set V3) ({w2} : Set V3) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1 hz2
    rcases hz1 with h0 | h1
    · exact (fun he => hn2' (collinear3_pair_left he)) ((h0.symm.trans hz2).symm)
    · exact (fun he => hn2' (collinear3_pair_right he)) ((h1.symm.trans hz2).symm)
  refine ⟨hne, ?_, ?_, ?_⟩
  · exact Set.Finite.insert w1 (Set.finite_singleton w2)
  · intro p hp q hq c hpq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with hp1 | hp2
    · rcases hq with hq1 | hq2
      · rw [hp1, hq1]
      · exfalso
        rw [hp1, hq2] at hpq
        have hge : w1 ∈ affGe ({v0, v1} : Set V3) ({w2} : Set V3) := by
          rw [mem_affGe_pair hdisj2 hne]
          refine ⟨c, -c, 1, by norm_num, by ring, ?_⟩
          have hw1 : w1 = w2 + c • (v0 - v1) := by
            rw [← hpq]; abel
          rw [hw1]; module
        have hz21 : azim v0 v1 w2 w1 = 0 := (AZIM_EQ_0_GE_ALT2 v0 v1 w2 w1 hn2).mpr hge
        have hz12 : azim v0 v1 w1 w2 = 0 := (AZIM_EQ_0_SYM2 v0 v1 w1 w2).mpr hz21
        rw [hz12] at h
        exact lt_irrefl 0 h
    · rcases hq with hq1 | hq2
      · exfalso
        rw [hp2, hq1] at hpq
        have hge : w2 ∈ affGe ({v0, v1} : Set V3) ({w1} : Set V3) := by
          rw [mem_affGe_pair hdisj1 hne]
          refine ⟨c, -c, 1, by norm_num, by ring, ?_⟩
          have hw2 : w2 = w1 + c • (v0 - v1) := by
            rw [← hpq]; abel
          rw [hw2]; module
        have hz12 : azim v0 v1 w1 w2 = 0 := (AZIM_EQ_0_GE_ALT2 v0 v1 w1 w2 hn1).mpr hge
        rw [hz12] at h
        exact lt_irrefl 0 h
      · rw [hp2, hq2]
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hzw, hzspan⟩ := hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzw
    rcases hzw with rfl | rfl
    · exact hn1 ((collinear3_iff_mem_affineSpan hne).mpr hzspan)
    · exact hn2 ((collinear3_iff_mem_affineSpan hne).mpr hzspan)

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
    {v, rhoNode1_p2 FF v} ∈ E := by
  have hd : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  exact LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hd

/-- HOL `CROSS_PAIR_NOT_IN_FF` (local_lemmas1.hl:2088) — giant. -/
theorem CROSS_PAIR_NOT_IN_FF (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    (v, w) ∉ FF := by
  intro hmem
  -- the midpoint of the slice segment is a strict ``aff_gt`` point
  have hmid : ∀ x₀ : V3, x₀ ≠ v → x₀ ≠ w →
      (1/2 : ℝ) • v + (1/2 : ℝ) • w ∈ affGt ({x₀} : Set V3) {v, w} := by
    intro x₀ hxv hxw
    have hfin : (({x₀} : Set V3) ∪ ({v, w} : Set V3)).Finite :=
      (Set.finite_singleton x₀).union (Set.Finite.insert v (Set.finite_singleton w))
    have hfs : hfin.toFinset = ({v, w, x₀} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    set f : V3 → ℝ :=
      fun z => (if z = v then (1/2 : ℝ) else 0) + (if z = w then (1/2 : ℝ) else 0)
      with hf
    have hfv : f v = 1/2 := by simp [hf, hvw]
    have hfw : f w = 1/2 := by simp [hf, Ne.symm hvw]
    have hfx : f x₀ = 0 := by simp [hf, hxv, hxw]
    have hvnot : v ∉ ({w, x₀} : Finset V3) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvw, Ne.symm hxv⟩
    have hwnot : w ∉ ({x₀} : Finset V3) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hxw
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [hfs, Finset.sum_insert hvnot, Finset.sum_insert hwnot, Finset.sum_singleton,
        hfv, hfw, hfx]
      module
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hfv]; norm_num
      · rw [hfw]; norm_num
    · rw [hfs, Finset.sum_insert hvnot, Finset.sum_insert hwnot, Finset.sum_singleton,
        hfv, hfw, hfx]
      norm_num
  have hfanE : FAN 0 V E := by
    obtain ⟨-, -, -, -, -, hf, -, -⟩ := h
    exact hf
  have hv0 : v ≠ 0 := FAN_IMP_V_DIFF hfanE v hv
  have hw0 : w ≠ 0 := FAN_IMP_V_DIFF hfanE w hw
  have hnc0 : ¬ Collinear ℝ ({0, (v, w).1, (v, w).2} : Set V3) :=
    LOCAL_FAN_IN_FF_NOT_COLLINEAR h hmem
  have hnc : ¬ Collinear ℝ ({0, v, w} : Set V3) := hnc0
  set p : V3 := (1/2 : ℝ) • v + (1/2 : ℝ) • w with hp
  have hpgt : p ∈ affGt ({0} : Set V3) {v, w} := by
    rw [hp]
    exact hmid 0 hv0.symm hw0.symm
  have hdisj0 : Disjoint ({0, v} : Set V3) ({w} : Set V3) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1 hz2
    rcases hz1 with h0 | hv'
    · rw [h0] at hz2
      exact hw0.symm hz2
    · rw [hv'] at hz2
      exact hvw hz2
  have hpge : p ∈ affGe ({0, v} : Set V3) ({w} : Set V3) := by
    rw [mem_affGe_pair hdisj0 (Ne.symm hv0)]
    refine ⟨0, 1/2, 1/2, by norm_num, by norm_num, ?_⟩
    rw [hp]
    module
  have hazim0 : azim 0 v w p = 0 := (AZIM_EQ_0_GE_ALT2 0 v w p hnc).mpr hpge
  have hcardw : 1 < (EE_p2 v E).ncard := by
    have h2 := LOFA_CARD_EE_V_1 h hv
    omega
  have hpwedge : p ∈ wedgeInFanGt_p2 (v, w) E := hsub (v, w) hmem hpgt
  rw [wedgeInFanGt_p2, if_pos hcardw] at hpwedge
  have hpos : 0 < azim 0 v w p := hpwedge.2.1
  rw [hazim0] at hpos
  exact lt_irrefl 0 hpos

/-- HOL `LOFA_IMP_ITER_RHO_NODE_ID2` (local_lemmas1.hl:4808;
`Local_lemmas.LOFA_IMP_ITER_RHO_NODE_ID` is external, not ported) — giant. -/
theorem LOFA_IMP_ITER_RHO_NODE_ID2 (h : localFan_p2 V E FF) (hv : v ∈ V) :
    (rhoNode1_p2 FF)^[V.ncard] v = v :=
  LOFA_IMP_ITER_RHO_NODE_ID h hv

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
    HS1.faceMap (x, y) = HS2.faceMap (x, y) := by
  obtain ⟨-, -, -, hF1⟩ := hHS1
  obtain ⟨-, -, -, hF2⟩ := hHS2
  rw [hF1, hF2]
  have hdE : (x, y) ∈ dartsOfHyp_p2 E V := by
    rcases Set.mem_or_mem_of_mem_union hd with ho | hs
    · simp only [ordPairs_p2, Set.mem_setOf_eq] at ho ⊢
      rcases Set.mem_or_mem_of_mem_union ho with hE | hnew
      · exact Or.inl hE
      · exfalso
        have hy : y ∈ ({x, y} : Set V3) := by simp
        rw [hnew] at hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        exact hy.elim hya hyb
    · simp only [selfPairs_p2, Set.mem_setOf_eq] at hs ⊢
      obtain ⟨hxy, hxV, hEE⟩ := hs
      refine Or.inr ⟨hxy, hxV, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem] at hEE ⊢
      intro u hu
      exact hEE u (Or.inl hu)
  simp only [ffOfHyp_p2]
  rw [if_pos hd, if_pos hdE]
  have hEEeq : EE_p2 y (E ∪ {{a, b}}) = EE_p2 y E := by
    ext u
    simp only [EE_p2, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso
        have hy : y ∈ ({y, u} : Set V3) := by simp
        rw [h] at hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        exact hy.elim hya hyb
    · exact Or.inl
  rw [hEEeq]

/-- HOL `LOCAL_FACE_MAP_RHO_NODE1` (local_lemmas1.hl:1789) — giant. -/
theorem LOCAL_FACE_MAP_RHO_NODE1 (h : localFan_p2 V E FF)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V E HS) (hd : (x, y) ∈ FF) :
    HS.faceMap (x, y) = (rhoNode1_p2 FF x, rhoNode1_p2 FF y) := by
  obtain ⟨-, -, -, hF⟩ := hHS
  have hxy : rhoNode1_p2 FF x = y := DETER_RHO_NODE h hd
  have hxV : x ∈ V := (LOCAL_FAN_IMP_IN_V h hd hd).1
  have hyV : y ∈ V := (LOCAL_FAN_IMP_IN_V h hd hd).2.1
  have hdD : (x, y) ∈ dartsOfHyp_p2 E V := Or.inl (LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hd)
  have hEE : EE_p2 y E = {rhoNode1_p2 FF y, x} :=
    LOFA_IMP_EE_TWO_ELMS (vv := x) (v := y) h hxV hxy
  have hne : rhoNode1_p2 FF y ≠ x := by
    have h2 : (EE_p2 y E).ncard = 2 := LOFA_CARD_EE_V_1 h hyV
    rw [hEE] at h2
    exact (SET2_HAS_SIZE2 _ _).mp h2
  rw [hF]
  simp only [ffOfHyp_p2]
  rw [if_pos hdD, hxy]
  have hgoal : ivsAzimCycle_p2 (EE_p2 y E) 0 y x = rhoNode1_p2 FF y := by
    rw [hEE]
    have hspec : rhoNode1_p2 FF y ∈ ({rhoNode1_p2 FF y, x} : Set V3) ∧
        azimCycle_p2 ({rhoNode1_p2 FF y, x} : Set V3) 0 y (rhoNode1_p2 FF y) = x :=
      ⟨by simp, AZIM_CYCLE_TWO_POINT_SET _ _ 0 y⟩
    have huniq : ∀ z, z ∈ ({rhoNode1_p2 FF y, x} : Set V3) ∧
        azimCycle_p2 ({rhoNode1_p2 FF y, x} : Set V3) 0 y z = x →
        z = rhoNode1_p2 FF y := by
      intro z hz
      obtain ⟨hzm, haz⟩ := hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzm
      rcases hzm with h1 | h2
      · exact h1
      · exfalso
        rw [h2] at haz
        have hcy : azimCycle_p2 ({rhoNode1_p2 FF y, x} : Set V3) 0 y x =
            rhoNode1_p2 FF y := by
          have h := AZIM_CYCLE_TWO_POINT_SET x (rhoNode1_p2 FF y) 0 y
          simpa [Set.pair_comm] using h
        rw [hcy] at haz
        exact hne haz
    have hne0 : ({rhoNode1_p2 FF y, x} : Set V3) ≠ ∅ := by
      intro h0
      have hmem : rhoNode1_p2 FF y ∈ (∅ : Set V3) := by rw [← h0]; simp
      exact hmem
    simp only [ivsAzimCycle_p2]
    rw [if_neg hne0]
    exact epsilonFixed hspec huniq
  rw [hgoal]

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
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V E HS) : HS.Simple := by
  obtain ⟨HS', hd', hE', hN', hF', -, ⟨x, hx, -⟩, hdih⟩ := h
  have hHS' : IsHyp_p2 0 V E HS' := ⟨hd', hE', hN', hF'⟩
  have hEq : HS = HS' := by
    have hdarts : HS.darts = HS'.darts := by
      ext d
      have h1 : d ∈ (↑HS.darts : Set (V3 × V3)) ↔
          d ∈ (↑HS'.darts : Set (V3 × V3)) := by
        rw [hHS.1, hd']
      simpa using h1
    have hedge : HS.edgeMap = HS'.edgeMap := by
      apply Equiv.coe_fn_injective
      change (⇑HS.edgeMap : V3 × V3 → V3 × V3) = ⇑HS'.edgeMap
      rw [hHS.2.1, hHS'.2.1]
    have hnode : HS.nodeMap = HS'.nodeMap := by
      apply Equiv.coe_fn_injective
      change (⇑HS.nodeMap : V3 × V3 → V3 × V3) = ⇑HS'.nodeMap
      rw [hHS.2.2.1, hHS'.2.2.1]
    have hface : HS.faceMap = HS'.faceMap := by
      apply Equiv.coe_fn_injective
      change (⇑HS.faceMap : V3 × V3 → V3 × V3) = ⇑HS'.faceMap
      rw [hHS.2.2.2, hHS'.2.2.2]
    cases HS
    cases HS'
    simp_all
  rw [hEq]
  have hk : FF.ncard ≠ 0 := by
    intro h0
    have hcard := hdih.1
    rw [h0, mul_zero] at hcard
    have hne : HS'.darts.card ≠ 0 := Finset.card_ne_zero.mpr ⟨x, hx⟩
    exact hne hcard
  exact DIH2K_IMP_SIMPLE_HYPERMAP hdih hk

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
    wedgeInFanGt_p2 (w, rhoNode1_p2 FF w) E = wedge 0 w (rhoNode1_p2 FF w) v := by
  have hdart : (v, w) ∈ FF := by
    have h1 := (LOCAL_FAN_RHO_NODE_PROS h).1 v hv
    rwa [hw] at h1
  have hwV : w ∈ V := by rw [← hw]; exact LOFA_IN_V_SO_DO_RHO_NODE_V h hv
  have hinj : Set.InjOn (rhoNode1_p2 FF) V :=
    (SELF_CYCLIC_IMP_BIJ (rhoNode1_p2 FF) V
      (fun x hx => (LOCAL_FAN_ORBIT_MAP_V h hx).symm)).2.1
  have hivs : ivsRhoNode1_p2 FF w = v := by
    refine RHO_NODE_INVERSE_POINT hdart ?_
    intro ww hww
    refine hinj (LOCAL_FAN_IMP_IN_V h hww hww).1 hv ?_
    rw [DETER_RHO_NODE h hww, hw]
  have hEE : EE_p2 w E = {rhoNode1_p2 FF w, v} :=
    LOFA_IMP_EE_TWO_ELMS (vv := v) (v := w) h hv hw
  have hcard : 1 < (EE_p2 w E).ncard := by
    have h2 := LOFA_CARD_EE_V_1 h hwV
    omega
  rw [wedgeInFanGt_p2, if_pos hcard, hEE, AZIM_CYCLE_TWO_POINT_SET]

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
    ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v) ∈ FF := by
  have hmem := (LOCAL_FAN_RHO_NODE_PROS h).1 ((rhoNode1_p2 FF)^[n] v)
    (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n)
  have hstep : (rhoNode1_p2 FF)^[n + 1] v = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[n] v) :=
    Function.iterate_succ_apply' (rhoNode1_p2 FF) n v
  rw [hstep]
  exact hmem

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
    (hn : (rhoNode1_p2 FF)^[n] v = v) (hnz : n ≠ 0) : V.ncard ≤ n := by
  by_contra hc
  have hlt : n < V.ncard := by omega
  have hp : 0 < n := by omega
  have hne := LOFA_IMP_DIS_ELMS23 h hv 0 n hp hlt
  exact hne (by rw [hn]; rfl)

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
    rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := by
  have hpos : 0 < V.ncard := by
    by_contra hcon
    have h0 : V.ncard = 0 := by omega
    have hV0 : V = ∅ := Set.ncard_eq_zero (hs := LOCAL_FAN_FINITE_V h) |>.mp h0
    rw [hV0] at hv
    exact absurd hv (by simp)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, V.ncard = c + 1 := ⟨V.ncard - 1, by omega⟩
  have hivs : (rhoNode1_p2 FF)^[c] v = ivsRhoNode1_p2 FF v := by
    have hit := ITER_CARD_MINUS1_EQ_IVS_RN1 h hv
    rw [hc] at hit
    exact hit
  have hstep : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[c] v)
      = (rhoNode1_p2 FF)^[c + 1] v :=
    (Function.iterate_succ_apply' (rhoNode1_p2 FF) c v).symm
  rw [← hivs, hstep, ← hc]
  exact LOFA_IMP_ITER_RHO_NODE_ID h hv

/-- HOL `LOCAL_FAN_IVS_IN_V` (local_lemmas1.hl:3797) — giant. -/
theorem LOCAL_FAN_IVS_IN_V (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ivsRhoNode1_p2 FF v ∈ V :=
  by
    have hivs := ITER_CARD_MINUS1_EQ_IVS_RN1 h hv
    rw [← hivs]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (V.ncard - 1)

/-- HOL `LF_AZIM_CYCLE_EQ_IVS_ND` (local_lemmas1.hl:3807) — giant. -/
theorem LF_AZIM_CYCLE_EQ_IVS_ND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v) = ivsRhoNode1_p2 FF v :=
  by
    rw [LOFA_IMP_EE_TWO_ELMS h (LOCAL_FAN_IVS_IN_V h hv) (LOCAL_FAN_RHO_NODE_IVS h hv)]
    exact AZIM_CYCLE_TWO_POINT_SET _ _ 0 v

/-- HOL `AZIM_IN_FAN_RHOND_IVS_RHOND` (local_lemmas1.hl:3820) — giant. -/
theorem AZIM_IN_FAN_RHOND_IVS_RHOND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    azimInFan_p2 (v, rhoNode1_p2 FF v) E =
      azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) :=
  by
    have hcard : (1 : ℕ) < (EE_p2 v E).ncard := by
      rw [LOFA_CARD_EE_V_2 h (LOCAL_FAN_IVS_IN_V h hv) (LOCAL_FAN_RHO_NODE_IVS h hv)]
      norm_num
    rw [azimInFan_p2, if_pos hcard]
    rw [LF_AZIM_CYCLE_EQ_IVS_ND h hv]

/-- HOL `LOFA_IMP_EE_TWO_ELMS_INS_ND` (local_lemmas1.hl:3834) — giant. -/
theorem LOFA_IMP_EE_TWO_ELMS_INS_ND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    EE_p2 v E = {rhoNode1_p2 FF v, ivsRhoNode1_p2 FF v} :=
  LOFA_IMP_EE_TWO_ELMS h (LOCAL_FAN_IVS_IN_V h hv) (LOCAL_FAN_RHO_NODE_IVS h hv)

/-- HOL `WEDGE_IN_FAN_RHOND_IVS_RHOND` (local_lemmas1.hl:3844) — giant. -/
theorem WEDGE_IN_FAN_RHOND_IVS_RHOND (h : localFan_p2 V E FF) (hv : v ∈ V) :
    wedgeInFanGe_p2 (v, rhoNode1_p2 FF v) E =
      wedgeGe_p2 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) :=
  by
    have hcard : (1 : ℕ) < (EE_p2 v E).ncard := by
      rw [LOFA_CARD_EE_V_2 h (LOCAL_FAN_IVS_IN_V h hv) (LOCAL_FAN_RHO_NODE_IVS h hv)]
      norm_num
    rw [wedgeInFanGe_p2, if_pos hcard]
    rw [LF_AZIM_CYCLE_EQ_IVS_ND h hv]

/-- HOL `IVS_RHO_NODE_DIFF_ID` (local_lemmas1.hl:3866) — giant. -/
theorem IVS_RHO_NODE_DIFF_ID (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ivsRhoNode1_p2 FF v ≠ v := by
  have hit := ITER_CARD_MINUS1_EQ_IVS_RN1 h hv
  have hmem := LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (V.ncard - 1)
  rw [hit] at hmem
  obtain ⟨hne, -, -⟩ := LOCAL_FAN_CHARACTER_OF_RHO_NODE h hmem
  have hid : rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h hv
  rw [hid] at hne
  exact Ne.symm hne

/-- HOL `POINT_PRESENTED_IN_RHOND1` (local_lemmas1.hl:3877) — giant. -/
theorem POINT_PRESENTED_IN_RHOND1 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ n : ℕ, n < V.ncard ∧ (rhoNode1_p2 FF)^[n] v = w ∧
      (∀ m : ℕ, m < n → ¬((rhoNode1_p2 FF)^[m] v = w)) := by
  have hset := LOFA_IMP_LT_CARD_SET_V h hv
  have hmem : w ∈ {(rhoNode1_p2 FF)^[n] v | n < V.ncard} := by
    rw [hset]; exact hw
  obtain ⟨n, hnlt, hnw⟩ := hmem
  refine ⟨n, hnlt, hnw, ?_⟩
  intro m hm hmeq
  exact LOFA_IMP_DIS_ELMS23 h hv m n hm hnlt (hnw.trans hmeq.symm)

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
  by
    -- Orbit counting: `d = n + n'` is a period at `v` (`ρ^[n] v = w`, `ρ^[n'] w = v`)
    -- and `V.ncard` is a period (`LOFA_IMP_ITER_RHO_NODE_ID2`).  If `d < V.ncard`
    -- this collides with the pairwise distinctness of the first `V.ncard` iterates
    -- (`LOFA_IMP_DIS_ELMS23`); if `d > V.ncard` the same lemma kills the residual
    -- period `d - V.ncard`; hence `d = V.ncard`.
    have hN : (rhoNode1_p2 FF)^[V.ncard] v = v := LOFA_IMP_ITER_RHO_NODE_ID2 h hv
    have hd : (rhoNode1_p2 FF)^[n + n'] v = v := by
      rw [Nat.add_comm n n', Function.iterate_add_apply, hn, hn']
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hp
      · exfalso
        rw [h0] at hn
        simp only [Function.iterate_zero, id] at hn
        exact hvw hn
      · exact hp
    have hdlt : n + n' < 2 * V.ncard := by omega
    rcases lt_trichotomy (n + n') V.ncard with hlt | heq | hgt
    · have hdis := LOFA_IMP_DIS_ELMS23 h hv 0 (n + n') (by omega) hlt
      simp only [Function.iterate_zero, id] at hdis
      exact absurd hd hdis
    · exact heq
    · set r := n + n' - V.ncard with hr
      have hrpos : 0 < r := by omega
      have hrlt : r < V.ncard := by omega
      have hrv : (rhoNode1_p2 FF)^[r] v = v := by
        have hdr : n + n' = r + V.ncard := by omega
        rw [hdr, Function.iterate_add_apply, hN] at hd
        exact hd
      have hdis := LOFA_IMP_DIS_ELMS23 h hv 0 r hrpos hrlt
      simp only [Function.iterate_zero, id] at hdis
      exact absurd hrv hdis

/-- HOL `DIFFERENCE_IMP_LT_CARDV` (local_lemmas1.hl:4721) — giant. -/
theorem DIFFERENCE_IMP_LT_CARDV (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (m : ℕ) (hm : ∀ n : ℕ, n < m → ¬((rhoNode1_p2 FF)^[n] v = w)) :
    m < V.ncard :=
  by
    -- Orbit covering: `w` occurs among the first `V.ncard` iterates of `v`
    -- (`LOFA_IMP_LT_CARD_SET_V`), so `m ≥ V.ncard` would put that occurrence
    -- below `m`, contradicting the hypothesis.
    by_contra hcon
    have hmN : V.ncard ≤ m := by omega
    have hset := LOFA_IMP_LT_CARD_SET_V h hv
    have hmem : w ∈ {(rhoNode1_p2 FF)^[n] v | n < V.ncard} := by
      rw [hset]; exact hw
    obtain ⟨n, hnlt, hnw⟩ := hmem
    exact hm n (by omega) hnw

/-- HOL `LT_CARD_MONO_LOFA` (local_lemmas1.hl:4746) — giant. -/
theorem LT_CARD_MONO_LOFA (h : localFan_p2 V E FF) (hv : v ∈ V) :
    ∀ i j : ℕ, i < V.ncard ∧ j < V.ncard ∧ (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[j] v →
      i = j := by
  intro i j ⟨hilt, hjlt, hij⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact (LOFA_IMP_DIS_ELMS23 h hv i j hlt hjlt).symm hij
  · exact LOFA_IMP_DIS_ELMS23 h hv j i hgt hilt hij

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
      wedge 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
  have hivsV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V h hv
  have hr : rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h hv
  exact WEDGE_IN_FAN_LOFA_DETER (v := ivsRhoNode1_p2 FF v) (w := v) h hivsV hr

/-- HOL `AZIM_COND_FOR_COPLANAR` (local_lemmas1.hl:5620) — giant. -/
theorem AZIM_COND_FOR_COPLANAR (v0 v1 w1 w2 : V3) :
    azim v0 v1 w1 w2 = 0 ∨ azim v0 v1 w1 w2 = Real.pi ↔ Coplanar {v0, v1, w1, w2} :=
  sorry

/-- HOL `AFF_SUB_PLANE` (local_lemmas1.hl:5640). -/
theorem AFF_SUB_PLANE (P : Set V3) (hP : plane_p2 P) {S : Set V3} (hS : S ⊆ P) :
    ∀ z ∈ affineSpan ℝ S, z ∈ P := by
  obtain ⟨u, v, w, -, hPeq⟩ := hP
  rw [hPeq] at hS ⊢
  intro z hz
  exact affineSpan_le.mpr hS hz

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
    (t : ℝ) (x : V3) : ‖lunarDeform e1 e2 e3 t x‖ = ‖x‖ := by
  set aa : ℝ := (1 - t) * azim 0 e3 e1 x with haa
  set bb : ℝ := arcV 0 e3 x with hbb
  set A : ℝ := ‖x‖ * Real.cos aa * Real.sin bb with hA
  set B : ℝ := ‖x‖ * Real.sin aa * Real.sin bb with hB
  set C : ℝ := ‖x‖ * Real.cos bb with hC
  have hu : lunarDeform e1 e2 e3 t x = A • e1 + B • e2 + C • e3 := by
    rw [lunarDeform, ← haa, ← hbb, ← hA, ← hB, ← hC]
  have h11 : e1 ⬝ᵥ e1 = 1 := horth.1
  have h22 : e2 ⬝ᵥ e2 = 1 := horth.2.1
  have h33 : e3 ⬝ᵥ e3 = 1 := horth.2.2.1
  have h12 : e1 ⬝ᵥ e2 = 0 := horth.2.2.2.1
  have h13 : e1 ⬝ᵥ e3 = 0 := horth.2.2.2.2.1
  have h23 : e2 ⬝ᵥ e3 = 0 := horth.2.2.2.2.2.1
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact h12
  have h31 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact h13
  have h32 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact h23
  have hsq : ‖A • e1 + B • e2 + C • e3‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      inner_eq_dot, h11, h22, h33, h12, h21, h13, h31, h23, h32]
    have hxx : x ⬝ᵥ x = ‖x‖ ^ 2 := by rw [← inner_eq_dot, real_inner_self_eq_norm_sq]
    have hsin : Real.sin aa ^ 2 + Real.cos aa ^ 2 = 1 := Real.sin_sq_add_cos_sq aa
    have hsin2 : Real.sin bb ^ 2 + Real.cos bb ^ 2 = 1 := Real.sin_sq_add_cos_sq bb
    rw [hA, hB, hC, hxx]
    ring_nf
    linear_combination (‖x‖ ^ 2 * Real.sin bb ^ 2) * hsin + (‖x‖ ^ 2) * hsin2
  have hnn : 0 ≤ ‖A • e1 + B • e2 + C • e3‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖x‖ := norm_nonneg _
  rw [hu]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hx0 : ‖x‖ = 0 := by linarith
    rw [hx0] at h ⊢
    linarith

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
  by
    unfold upsX_p6
    fun_prop

/-- Continuity at a point of the coordinate cross product of two
continuous-at maps `ℝ → (Fin 3 → ℝ)` (coordinate expansion). -/
private lemma w6g_continuousAt_crossProduct {u v : ℝ → (Fin 3 → ℝ)} {r : ℝ}
    (hu : ContinuousAt u r) (hv : ContinuousAt v r) :
    ContinuousAt (fun t => crossProduct (u t) (v t)) r := by
  have hu' : ∀ i, ContinuousAt (fun t : ℝ => u t i) r := fun i => continuousAt_pi.mp hu i
  have hv' : ∀ i, ContinuousAt (fun t : ℝ => v t i) r := fun i => continuousAt_pi.mp hv i
  rw [continuousAt_pi]
  intro i
  fin_cases i <;> simp [cross_apply] <;>
    exact ((hu' _).mul (hv' _)).sub ((hu' _).mul (hv' _))

/-- `Collinear3 v0 a b` iff the cross product of the two difference
vectors vanishes (both directions via `collinear3_iff_smul` and
`crossProduct_ne_zero_iff_linearIndependent`). -/
private lemma w6g_collinear3_iff_cross_eq_zero (v0 a b : V3) :
    Collinear3 v0 a b ↔
      crossProduct ((a - v0 : V3) : Fin 3 → ℝ) ((b - v0 : V3) : Fin 3 → ℝ) = 0 := by
  constructor
  · intro h
    by_cases ha : a = v0
    · have hz : ((a - v0 : V3) : Fin 3 → ℝ) = 0 := by
        rw [ha, sub_self]
        rfl
      rw [hz]
      simp
    · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := v0) (w := a) (w1 := b) ha).mp h
      have hc' : ((b - v0 : V3) : Fin 3 → ℝ) = c • ((a - v0 : V3) : Fin 3 → ℝ) := by
        rw [hc]
        rfl
      rw [hc', map_smul, cross_self, smul_zero]
  · intro hcross
    by_contra hcol
    have hnotli : ¬ LinearIndependent ℝ
        ![((a - v0 : V3) : Fin 3 → ℝ), ((b - v0 : V3) : Fin 3 → ℝ)] := by
      intro hli
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) hcross
    by_cases hu : ((a - v0 : V3) : Fin 3 → ℝ) = 0
    · have ha0 : (a - v0 : V3) = 0 := by
        apply WithLp.ofLp_injective 2
        simpa using hu
      exact hcol (collinear3_of_eq (v := v0) (w := a) (w1 := b) (sub_eq_zero.mp ha0))
    · have hnotall : ¬ ∀ c : ℝ, c • ((a - v0 : V3) : Fin 3 → ℝ)
          ≠ ((b - v0 : V3) : Fin 3 → ℝ) := by
        rwa [← LinearIndependent.pair_iff' hu]
      obtain ⟨c, hc⟩ := not_forall.mp hnotall
      have hc' : ((b - v0 : V3) : Fin 3 → ℝ) = c • ((a - v0 : V3) : Fin 3 → ℝ) :=
        (not_not.mp hc).symm
      have hc3 : (b - v0 : V3) = c • (a - v0 : V3) := by
        apply WithLp.ofLp_injective 2
        simpa using hc'
      have ha : a ≠ v0 := by
        intro he
        apply hu
        rw [he, sub_self]
        rfl
      exact hcol ((collinear3_iff_smul (v := v0) (w := a) (w1 := b) ha).mpr ⟨c, hc3⟩)

/-- HOL `CONTINUOUS_PRESERVE_COLLINEAR` (local_lemmas1.hl:6286) — giant. -/
theorem CONTINUOUS_PRESERVE_COLLINEAR (v0 : V3) (f g : ℝ → V3) (r : ℝ)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r)
    (hnc : ¬ Collinear3 v0 (f r) (g r)) :
    ∃ e : ℝ, 0 < e ∧ ∀ r' : ℝ, |r - r'| < e → ¬ Collinear3 v0 (f r') (g r') :=
  by
    have hkey : ∀ t : ℝ, Collinear3 v0 (f t) (g t) ↔
        crossProduct ((f t - v0 : V3) : Fin 3 → ℝ) ((g t - v0 : V3) : Fin 3 → ℝ) = 0 :=
      fun t => w6g_collinear3_iff_cross_eq_zero v0 (f t) (g t)
    have hHne : crossProduct ((f r - v0 : V3) : Fin 3 → ℝ) ((g r - v0 : V3) : Fin 3 → ℝ) ≠ 0 :=
      fun hz => hnc ((hkey r).mpr hz)
    have hH : ContinuousAt
        (fun t : ℝ => crossProduct ((f t - v0 : V3) : Fin 3 → ℝ) ((g t - v0 : V3) : Fin 3 → ℝ)) r := by
      apply w6g_continuousAt_crossProduct
      · have h := hf.sub (continuousAt_const : ContinuousAt (fun _ : ℝ => v0) r)
        fun_prop
      · have h := hg.sub (continuousAt_const : ContinuousAt (fun _ : ℝ => v0) r)
        fun_prop
    have hpos : 0 < ‖crossProduct ((f r - v0 : V3) : Fin 3 → ℝ) ((g r - v0 : V3) : Fin 3 → ℝ)‖ :=
      norm_pos_iff.mpr hHne
    obtain ⟨e, he, hball⟩ := Metric.continuousAt_iff.mp hH _ hpos
    refine ⟨e, he, ?_⟩
    intro r' hr'
    have hdist : dist r' r < e := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hr'
    have hlt := hball (x := r') hdist
    intro hcol
    have hz := (hkey r').mp hcol
    rw [hz, dist_zero_left] at hlt
    exact lt_irrefl _ hlt

/-- HOL `EACH_ELM_PRESERVED_IMP_ALLL` (local_lemmas1.hl:6316) — giant. -/
theorem EACH_ELM_PRESERVED_IMP_ALLL (phii : V3 → ℝ → V3) (E : Set (Set V3))
    (h1 : ∀ x ∈ E, ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      ¬ Collinear ℝ (Set.insert (0 : V3) ((fun v : V3 => phii v t) '' x)))
    (hE : E.Finite) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
      ∀ e' ∈ (fun x : Set V3 => (fun v : V3 => phii v t) '' x) '' E,
        ¬ Collinear ℝ (Set.insert (0 : V3) e') :=
  by
    classical
    have aux : ∀ s : Finset (Set V3),
        (∀ x ∈ (s : Set (Set V3)), ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
          ¬ Collinear ℝ (Set.insert (0 : V3) ((fun v : V3 => phii v t) '' x))) →
        ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, |t| < e →
          ∀ e' ∈ (fun x : Set V3 => (fun v : V3 => phii v t) '' x) '' (s : Set (Set V3)),
            ¬ Collinear ℝ (Set.insert (0 : V3) e') := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro h1
        refine ⟨1, zero_lt_one, ?_⟩
        intro t ht e' he'
        simp only [Finset.coe_empty, Set.image_empty, Set.mem_empty_iff_false] at he'
      | insert a s has ih =>
        intro h1
        obtain ⟨ea, hea_pos, hea⟩ := h1 a (by simp)
        obtain ⟨es, hes_pos, hes⟩ := ih (fun x hx => h1 x (by
          simp only [Finset.coe_insert, Set.mem_insert_iff]
          exact Or.inr hx))
        refine ⟨min ea es, lt_min hea_pos hes_pos, ?_⟩
        intro t ht e' he'
        simp only [Finset.coe_insert, Set.image_insert_eq, Set.mem_insert_iff] at he'
        rcases he' with rfl | he'
        · exact hea t (lt_of_lt_of_le ht (min_le_left ea es))
        · exact hes t (lt_of_lt_of_le ht (min_le_right ea es)) e' he'
    have hcoe : (hE.toFinset : Set (Set V3)) = E := hE.coe_toFinset
    rw [← hcoe]
    exact aux hE.toFinset (fun x hx => h1 x (by rw [← hcoe]; exact hx))

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
