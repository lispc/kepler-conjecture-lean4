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

import Kepler.Text.ConicCapVolume
import Kepler.Text.LocalAuto2
import Kepler.Text.LocalAuto3
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto10
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

/-- `cos` of `arcV` at the origin (helper for `ARCV_DETER_DIRECTION`). -/
private theorem w1_cos_arcV_zero {u w : V3} (hu : u ≠ 0) (hw : w ≠ 0) :
    Real.cos (arcV 0 u w) = inner ℝ u w / (‖u‖ * ‖w‖) := by
  rw [arcV_eq]
  simp only [dist_zero_right, sub_zero]
  have hden : 0 < ‖u‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hw)
  have hb := abs_real_inner_le_norm u w
  have h1 : -1 ≤ inner ℝ u w / (‖u‖ * ‖w‖) := by
    rw [le_div_iff₀ hden]
    linarith [neg_abs_le (inner ℝ u w)]
  have h2 : inner ℝ u w / (‖u‖ * ‖w‖) ≤ 1 := by
    rw [div_le_one hden]
    exact le_trans (le_abs_self _) hb
  exact Real.cos_arccos h1 h2

/-- HOL `ARCV_DETER_DIRECTION` (local_lemmas1.hl:269). -/
theorem ARCV_DETER_DIRECTION {x y u : V3} {tu ty : ℝ} (hty : 0 < ty)
    (hx : x = tu • u + ty • y) (hcol : ¬ Collinear3 0 u y) (hnx : ‖x‖ = 1)
    (hny : ‖y‖ = 1) (harc : arcV 0 u x = arcV 0 u y) : x = y := by
  have hu0 : u ≠ 0 := by
    intro hu
    apply hcol
    rw [hu]
    exact collinear3_of_eq rfl
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, norm_zero] at hny
    norm_num at hny
  have hx0 : x ≠ 0 := by
    intro hx'
    rw [hx', norm_zero] at hnx
    norm_num at hnx
  -- angle equality -> inner products against u equal
  have hcos : Real.cos (arcV 0 u x) = Real.cos (arcV 0 u y) := congrArg Real.cos harc
  rw [w1_cos_arcV_zero hu0 hx0, w1_cos_arcV_zero hu0 hy0] at hcos
  have hux : inner ℝ u x = inner ℝ u y := by
    rw [hnx, hny, mul_one] at hcos
    exact (div_left_inj' (norm_ne_zero_iff.mpr hu0)).mp hcos
  -- two scalar equations
  have hE1 : tu * (inner ℝ u u) + ty * (inner ℝ u y) = inner ℝ u y := by
    have h : inner ℝ u x = tu * inner ℝ u u + ty * inner ℝ u y := by
      rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [← h]
    exact hux
  have hE2 : tu ^ 2 * (inner ℝ u u) + 2 * tu * ty * (inner ℝ u y) + ty ^ 2 = 1 := by
    have hyy : inner ℝ y y = 1 := by
      rw [real_inner_self_eq_norm_sq, hny]
      norm_num
    have hxx : inner ℝ x x = 1 := by
      rw [real_inner_self_eq_norm_sq, hnx]
      norm_num
    have hexp : inner ℝ x x =
        tu ^ 2 * inner ℝ u u + 2 * tu * ty * inner ℝ u y + ty ^ 2 * inner ℝ y y := by
      rw [hx]
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_right, real_inner_comm]
      ring
    have hexp' : inner ℝ x x =
        tu ^ 2 * inner ℝ u u + 2 * tu * ty * inner ℝ u y + ty ^ 2 := by
      rw [hexp, hyy, mul_one]
    rw [← hexp', hxx]
  have ha_pos : 0 < inner ℝ u u := by
    rw [real_inner_self_eq_norm_sq]
    have h := norm_pos_iff.mpr hu0
    positivity
  by_cases hb0 : inner ℝ u y = 0
  · have htu : tu = 0 := by
      have h' : tu * inner ℝ u u = 0 := by
        simpa [hb0] using hE1
      exact (mul_eq_zero.mp h').resolve_right (ne_of_gt ha_pos)
    have hty1 : ty = 1 := by
      have hsq : ty ^ 2 = 1 := by
        rw [hb0, htu] at hE2
        simpa using hE2
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · linarith
    rw [hx, htu, hty1, zero_smul, one_smul, zero_add]
  · have hb_sq_lt : (inner ℝ u y) ^ 2 < inner ℝ u u := by
      have hb_abs : |inner ℝ u y| ≤ ‖u‖ := by
        have h := abs_real_inner_le_norm u y
        rwa [hny, mul_one] at h
      have hne : |inner ℝ u y| ≠ ‖u‖ := by
        intro heq
        have hnormeq : ‖inner ℝ u y‖ = ‖u‖ * ‖y‖ := by
          rw [Real.norm_eq_abs, hny, heq, mul_one]
        obtain ⟨r, _hr, hyr⟩ := (norm_inner_eq_norm_iff hu0 hy0).mp hnormeq
        apply hcol
        exact (collinear3_iff_smul (v := 0) (w := u) (w1 := y) hu0).mpr
          ⟨r, by simpa using hyr⟩
      have hlt : |inner ℝ u y| < ‖u‖ := lt_of_le_of_ne hb_abs hne
      have h2 : (|inner ℝ u y|) ^ 2 < ‖u‖ ^ 2 := by
        nlinarith [hlt, abs_nonneg (inner ℝ u y), norm_nonneg u]
      rwa [sq_abs, ← real_inner_self_eq_norm_sq] at h2
    by_cases hty1 : ty = 1
    · have htu : tu = 0 := by
        have h' : tu * inner ℝ u u = 0 := by
          rw [hty1] at hE1
          linarith
        exact (mul_eq_zero.mp h').resolve_right (ne_of_gt ha_pos)
      rw [hx, htu, hty1, zero_smul, one_smul, zero_add]
    · have htu_eq : tu * (inner ℝ u u) = (inner ℝ u y) * (1 - ty) := by
        have h' : tu * (inner ℝ u u) = inner ℝ u y - ty * inner ℝ u y := by
          linarith
        rw [h']; ring
      have htu_val : tu = (inner ℝ u y) * (1 - ty) / (inner ℝ u u) := by
        rw [eq_div_iff (ne_of_gt ha_pos)]
        exact htu_eq
      have hE2sub := hE2
      rw [htu_val] at hE2sub
      field_simp [ne_of_gt ha_pos] at hE2sub
      have hkey : (1 - ty ^ 2) * (1 - (inner ℝ u y) ^ 2 / (inner ℝ u u)) = 0 := by
        field_simp [ne_of_gt ha_pos]
        nlinarith
      have hfrac_ne : 1 - (inner ℝ u y) ^ 2 / (inner ℝ u u) ≠ 0 := by
        intro hz
        have hz' : (inner ℝ u y) ^ 2 / (inner ℝ u u) = 1 := by linarith
        field_simp [ne_of_gt ha_pos] at hz'
        linarith
      have hty_sq : ty ^ 2 = 1 := by
        have hz : 1 - ty ^ 2 = 0 := (mul_eq_zero.mp hkey).resolve_right hfrac_ne
        linarith
      have hty_one : ty = 1 := by
        rcases sq_eq_one_iff.mp hty_sq with h | h
        · exact h
        · linarith
      exact absurd hty_one hty1

/-- HOL `NORM_NORMIZE` (local_lemmas1.hl:359; HOL form is
`Trigonometry2.NOT_VEC0_UNITABLE` rewritten by `GSYM normize`). -/
theorem NORM_NORMIZE {v : V3} (h : v ≠ (0 : V3)) : ‖normize v‖ = 1 := by
  have hv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hvp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  rw [normize, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos one_pos hvp)]
  field_simp

/-- HOL `ARCV_EQ_IMP_NORMIZE` (local_lemmas1.hl:363). -/
theorem ARCV_EQ_IMP_NORMIZE {x y u : V3} (hgt : x ∈ affGt ({0, u} : Set V3) ({y} : Set V3))
    (hcol : ¬ Collinear3 0 u y) (harc : arcV 0 u x = arcV 0 u y) : normize x = normize y := by
  have hu0 : u ≠ 0 := by
    intro hu
    apply hcol
    rw [hu]
    exact collinear3_of_eq rfl
  have hy0 : y ≠ 0 := by
    intro hy
    apply hcol
    rw [hy]
    exact collinear3_pair_left rfl
  have hset := COLL_AFF_GT_2_1 (0 : V3) u y hcol
  rw [hset] at hgt
  obtain ⟨t1, t2, t3, ht3, hsum, hxeq⟩ := hgt
  have hx : x = t2 • u + t3 • y := by
    rw [hxeq, smul_zero, zero_add]
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply hcol
    refine (COLL_EQ_DEPENDENT u y).mpr ⟨t2, t3, ?_, ?_⟩
    · intro hboth
      exact absurd hboth.2 (ne_of_gt ht3)
    · rw [← hx, hxzero]
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hnx1 : ‖(1 / ‖x‖) • x‖ = 1 := by
    simpa [normize] using NORM_NORMIZE hx0
  have hny1 : ‖(1 / ‖y‖) • y‖ = 1 := by
    simpa [normize] using NORM_NORMIZE hy0
  have hy_ny : y = ‖y‖ • ((1 / ‖y‖) • y) := by
    rw [smul_smul, one_div, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul]
  have hrepr : (1 / ‖x‖) • x =
      ((1 / ‖x‖) * t2) • u + ((1 / ‖x‖) * t3 * ‖y‖) • ((1 / ‖y‖) • y) := by
    calc (1 / ‖x‖) • x = ((1 / ‖x‖) * t2) • u + ((1 / ‖x‖) * t3) • y := by
          rw [hx, smul_add, smul_smul, smul_smul]
      _ = ((1 / ‖x‖) * t2) • u +
            ((1 / ‖x‖) * t3) • (‖y‖ • ((1 / ‖y‖) • y)) := by
          conv_lhs => rw [hy_ny]
      _ = ((1 / ‖x‖) * t2) • u +
            (((1 / ‖x‖) * t3) * ‖y‖) • ((1 / ‖y‖) • y) := by rw [smul_smul]
  have hcoef_pos : 0 < (1 / ‖x‖) * t3 * ‖y‖ := by
    have h1 : 0 < 1 / ‖x‖ := div_pos one_pos hxnorm_pos
    positivity
  have hcol_ny : ¬ Collinear3 0 u ((1 / ‖y‖) • y) := by
    intro hc
    obtain ⟨c, hc'⟩ := (collinear3_iff_smul (v := 0) (w := u)
      (w1 := (1 / ‖y‖) • y) hu0).mp hc
    apply hcol
    refine (collinear3_iff_smul (v := 0) (w := u) (w1 := y) hu0).mpr
      ⟨‖y‖ * c, ?_⟩
    have hc'' : (1 / ‖y‖) • y = c • u := by simpa using hc'
    have hcalc : y = (‖y‖ * c) • u := by
      calc y = ‖y‖ • ((1 / ‖y‖) • y) := hy_ny
        _ = ‖y‖ • (c • u) := by rw [hc'']
        _ = (‖y‖ * c) • u := by rw [smul_smul]
    simpa [sub_zero] using hcalc
  have hscale_x : arcV 0 u x = arcV 0 u ((1 / ‖x‖) • x) := by
    have h := WHEN_A_B_POS_ARCV_STABLE (a := 1) (b := 1 / ‖x‖)
      (x := u) (y := x) one_pos (div_pos one_pos hxnorm_pos)
    simpa using h
  have hscale_y : arcV 0 u y = arcV 0 u ((1 / ‖y‖) • y) := by
    have h := WHEN_A_B_POS_ARCV_STABLE (a := 1) (b := 1 / ‖y‖)
      (x := u) (y := y) one_pos (div_pos one_pos hynorm_pos)
    simpa using h
  have harc_norm : arcV 0 u ((1 / ‖x‖) • x) = arcV 0 u ((1 / ‖y‖) • y) := by
    rw [← hscale_x, ← hscale_y]
    exact harc
  have hmain := ARCV_DETER_DIRECTION (x := (1 / ‖x‖) • x)
    (y := (1 / ‖y‖) • y) (u := u) (tu := (1 / ‖x‖) * t2)
    (ty := (1 / ‖x‖) * t3 * ‖y‖) hcoef_pos hrepr hcol_ny hnx1 hny1 harc_norm
  simpa [normize] using hmain

private theorem w1_arcV_translate (a u w : V3) :
    arcV a u w = arcV 0 (u - a) (w - a) := by
  rw [arcV, arcV]
  simp [dist_eq_norm]

private theorem w1_collinear3_translate {a u z : V3} (hu : u ≠ a) :
    Collinear3 a u z ↔ Collinear3 0 (u - a) (z - a) := by
  rw [collinear3_iff_smul (v := a) (w := u) (w1 := z) hu,
      collinear3_iff_smul (v := 0) (w := u - a) (w1 := z - a)
        (sub_ne_zero.mpr hu)]
  simp

private theorem w1_sin_arcv_eq_zero_lap (x y z : V3) :
    Real.sin (arcV x y z) = 0 ↔ arcV x y z = 0 ∨ arcV x y z = Real.pi := by
  have h1 : 0 ≤ arcV x y z := by
    rw [arcV_eq]
    exact Real.arccos_nonneg _
  have h2 : arcV x y z ≤ Real.pi := by
    rw [arcV_eq]
    exact Real.arccos_le_pi _
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

private theorem w1_azim_eq_zero_of_collinear {v0 u v z : V3}
    (h : Collinear3 v0 u z) : azim v0 u v z = 0 := by
  unfold azim
  exact if_pos (Or.inr h)

private theorem w1_arcv_zero_or_pi_collinear {a u w : V3}
    (hu : u ≠ a) (hw : w ≠ a)
    (h : arcV a u w = 0 ∨ arcV a u w = Real.pi) : Collinear3 a u w := by
  have hden : 0 < dist u a * dist w a :=
    mul_pos (dist_pos.mpr hu) (dist_pos.mpr hw)
  have hb := abs_real_inner_le_norm (u - a) (w - a)
  have hb' : |inner ℝ (u - a) (w - a)| ≤ dist u a * dist w a := by
    simpa [dist_eq_norm] using hb
  have hbnd : -1 ≤ inner ℝ (u - a) (w - a) / (dist u a * dist w a) ∧
      inner ℝ (u - a) (w - a) / (dist u a * dist w a) ≤ 1 := by
    constructor
    · rw [le_div_iff₀ hden]
      linarith [neg_abs_le (inner ℝ (u - a) (w - a)), hb']
    · rw [div_le_one hden]
      exact le_trans (le_abs_self _) hb'
  have habs : |inner ℝ (u - a) (w - a) / (dist u a * dist w a)| = 1 := by
    rcases h with h | h
    · rw [arcV_eq] at h
      have h1 : inner ℝ (u - a) (w - a) / (dist u a * dist w a) = 1 :=
        le_antisymm hbnd.2 (Real.arccos_eq_zero.mp h)
      rw [h1, abs_one]
    · rw [arcV_eq] at h
      have h1 : inner ℝ (u - a) (w - a) / (dist u a * dist w a) = -1 :=
        le_antisymm (Real.arccos_eq_pi.mp h) hbnd.1
      rw [h1, abs_neg, abs_one]
  have hnorm : ‖inner ℝ (u - a) (w - a)‖ = ‖u - a‖ * ‖w - a‖ := by
    have h1 : |inner ℝ (u - a) (w - a)| = dist u a * dist w a := by
      rw [abs_div, abs_of_pos hden, div_eq_iff (ne_of_gt hden)] at habs
      linarith
    rw [Real.norm_eq_abs, h1, dist_eq_norm, dist_eq_norm]
  have hu' : u - a ≠ 0 := sub_ne_zero.mpr hu
  have hw' : w - a ≠ 0 := sub_ne_zero.mpr hw
  obtain ⟨r, _hr, hr⟩ := (norm_inner_eq_norm_iff hu' hw').mp hnorm
  exact (collinear3_iff_smul (v := a) (w := u) (w1 := w) hu).mpr ⟨r, hr⟩

private theorem w1_arcv_line_smul_eq {u : V3} (hu : u ≠ 0) {a b : ℝ}
    (h : arcV 0 u (a • u) = arcV 0 u (b • u)) :
    (a = 0 ∧ b = 0) ∨ 0 < a * b := by
  have hA := ARCV_ORI_DIRECTIONS hu a
  have hB := ARCV_ORI_DIRECTIONS hu b
  by_cases ha0 : a = 0
  · left
    refine ⟨ha0, ?_⟩
    by_contra hb0
    have hz : arcV 0 u (b • u) = Real.pi / 2 := by
      have hdeg : arcV 0 u ((0:ℝ) • u) = Real.pi / 2 := by
        simpa using (ARCV_DEGENERATE (0:V3) u).2
      rw [ha0] at h
      rw [← h]
      exact hdeg
    rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
    · have hpi := hB.2.mpr hbneg
      rw [hpi] at hz
      linarith [Real.pi_pos]
    · have hzero := hB.1.mpr hbpos
      rw [hzero] at hz
      linarith [Real.pi_pos]
  · right
    rcases lt_or_gt_of_ne ha0 with haneg | hapos
    · have hpi := hA.2.mpr haneg
      rw [hpi] at h
      have hbneg : b < 0 := hB.2.mp h.symm
      nlinarith
    · have hzero := hA.1.mpr hapos
      rw [hzero] at h
      have hbpos : 0 < b := hB.1.mp h.symm
      nlinarith

/-- HOL `AZIM_AND_ARCV_EQ_IMP_PARA` (local_lemmas1.hl:443). -/
theorem AZIM_AND_ARCV_EQ_IMP_PARA {v0 u v x y : V3} (hcol : ¬ Collinear3 v0 u v)
    (haz : azim v0 u v x = azim v0 u v y) (harc : arcV v0 u x = arcV v0 u y) :
    y = v0 ∨ ∃ t : ℝ, 0 ≤ t ∧ x - v0 = t • (y - v0) := by
  have hv0u : v0 ≠ u := by
    intro h
    apply hcol
    rw [h]
    exact collinear3_of_eq rfl
  by_cases hycol : Collinear3 v0 u y
  · have hzy : azim v0 u v y = 0 := w1_azim_eq_zero_of_collinear hycol
    by_cases hxcol : Collinear3 v0 u x
    · obtain ⟨a, ha⟩ := (collinear3_iff_smul (v := v0) (w := u) (w1 := x)
        (Ne.symm hv0u)).mp hxcol
      obtain ⟨b, hb⟩ := (collinear3_iff_smul (v := v0) (w := u) (w1 := y)
        (Ne.symm hv0u)).mp hycol
      by_cases hb0 : b = 0
      · left
        rw [← sub_eq_zero, hb, hb0, zero_smul]
      · right
        have hu' : u - v0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hv0u)
        have hline : arcV 0 (u - v0) (a • (u - v0)) =
            arcV 0 (u - v0) (b • (u - v0)) := by
          calc arcV 0 (u - v0) (a • (u - v0))
              = arcV 0 (u - v0) (x - v0) := by rw [← ha]
            _ = arcV v0 u x := (w1_arcV_translate v0 u x).symm
            _ = arcV v0 u y := harc
            _ = arcV 0 (u - v0) (y - v0) := w1_arcV_translate v0 u y
            _ = arcV 0 (u - v0) (b • (u - v0)) := by rw [← hb]
        rcases w1_arcv_line_smul_eq hu' hline with ⟨_ha0, hbzero⟩ | hab
        · exact absurd hbzero hb0
        · refine ⟨a / b, ?_, ?_⟩
          · have hdiv : 0 < a / b := by
              rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
              · have haneg : a < 0 := by nlinarith [hab, hbneg]
                exact div_pos_of_neg_of_neg haneg hbneg
              · have hapos : 0 < a := by nlinarith [hab, hbpos]
                exact div_pos hapos hbpos
            exact le_of_lt hdiv
          · rw [ha, hb, smul_smul]
            field_simp [hb0]
    · by_cases hyv0 : y = v0
      · exact Or.inl hyv0
      · exfalso
        have hxnotv0 : x ≠ v0 := fun h => hxcol (collinear3_pair_left h)
        have hsin_y : Real.sin (arcV v0 u y) = 0 :=
          COLLINEAR_SIN_ARCV_0 hycol (fun h => hyv0 h.symm) hv0u
        have hsin_x : Real.sin (arcV v0 u x) = 0 := by rw [harc]; exact hsin_y
        have harc_x : arcV v0 u x = 0 ∨ arcV v0 u x = Real.pi :=
          (w1_sin_arcv_eq_zero_lap v0 u x).mp hsin_x
        exact hxcol (w1_arcv_zero_or_pi_collinear (Ne.symm hv0u) hxnotv0 harc_x)
  · by_cases hxcol : Collinear3 v0 u x
    · by_cases hxv0 : x = v0
      · right
        exact ⟨0, le_refl 0, by rw [hxv0, sub_self, zero_smul]⟩
      · exfalso
        have hsin_x : Real.sin (arcV v0 u x) = 0 :=
          COLLINEAR_SIN_ARCV_0 hxcol (fun h => hxv0 h.symm) hv0u
        have hsin_y : Real.sin (arcV v0 u y) = 0 := by rw [← harc]; exact hsin_x
        have harc_y : arcV v0 u y = 0 ∨ arcV v0 u y = Real.pi :=
          (w1_sin_arcv_eq_zero_lap v0 u y).mp hsin_y
        have hyv0 : y ≠ v0 := fun h => hycol (collinear3_pair_left h)
        exact hycol (w1_arcv_zero_or_pi_collinear (Ne.symm hv0u) hyv0 harc_y)
    · have hyv0 : y ≠ v0 := fun h => hycol (collinear3_pair_left h)
      obtain ⟨t1, t2, t3, ht3, hsum, hxeq⟩ := by
        have hset := COLL_AFF_GT_2_1 v0 u y hycol
        have hmem : x ∈ affGt ({v0, u} : Set V3) {y} :=
          (azim_eq_azim_iff_alt (v0 := v0) (v1 := u) (w := v) (x := x) (y := y)
            hcol hxcol hycol).mp haz
        rwa [hset] at hmem
      have hxsub : x - v0 = t2 • (u - v0) + t3 • (y - v0) := by
        have ht1 : t1 = 1 - t2 - t3 := by linarith
        rw [hxeq, ht1]
        module
      have hcol_y' : ¬ Collinear3 0 (u - v0) (y - v0) := by
        intro h
        exact hycol ((w1_collinear3_translate (Ne.symm hv0u)).mpr h)
      have hgt : (x - v0) ∈ affGt ({0, u - v0} : Set V3) ({y - v0} : Set V3) := by
        have hset := COLL_AFF_GT_2_1 (0 : V3) (u - v0) (y - v0) hcol_y'
        rw [hset]
        refine ⟨t1, t2, t3, ht3, hsum, ?_⟩
        rw [smul_zero, zero_add]
        exact hxsub
      have harc' : arcV 0 (u - v0) (x - v0) = arcV 0 (u - v0) (y - v0) := by
        rw [← w1_arcV_translate v0 u x, ← w1_arcV_translate v0 u y]
        exact harc
      have hnorm := ARCV_EQ_IMP_NORMIZE (x := x - v0) (y := y - v0)
        (u := u - v0) hgt hcol_y' harc'
      have hx'0 : x - v0 ≠ 0 := sub_ne_zero.mpr (fun h => hxcol (collinear3_pair_left h))
      have hy'0 : y - v0 ≠ 0 := sub_ne_zero.mpr hyv0
      set s : ℝ := ‖x - v0‖ / ‖y - v0‖ with hs
      have hs_eq : x - v0 = s • (y - v0) := by
        have h := hnorm
        rw [normize, normize] at h
        calc x - v0 = (‖x - v0‖ * (1 / ‖x - v0‖)) • (x - v0) := by
              rw [one_div, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx'0), one_smul]
          _ = ‖x - v0‖ • ((1 / ‖x - v0‖) • (x - v0)) := by rw [smul_smul]
          _ = ‖x - v0‖ • ((1 / ‖y - v0‖) • (y - v0)) := by rw [h]
          _ = s • (y - v0) := by
              rw [hs, smul_smul]
              congr 1
              field_simp
      have hs_pos : 0 < s := by
        rw [hs]
        exact div_pos (norm_pos_iff.mpr hx'0) (norm_pos_iff.mpr hy'0)
      have hlin : ∀ a b : ℝ, a • (u - v0) + b • (y - v0) = 0 → a = 0 ∧ b = 0 := by
        intro a b hab
        by_contra hne
        exact hycol ((w1_collinear3_translate (Ne.symm hv0u)).mpr
          ((COLL_EQ_DEPENDENT (u - v0) (y - v0)).mpr ⟨a, b, hne, hab⟩))
      have hz : t2 • (u - v0) + (t3 - s) • (y - v0) = 0 := by
        have hxsub' := hxsub
        rw [hs_eq] at hxsub'
        rw [sub_smul, hxsub']
        module
      have ht2 : t2 = 0 := (hlin t2 (t3 - s) hz).1
      have ht3s : t3 = s := by
        have := (hlin t2 (t3 - s) hz).2
        linarith
      refine Or.inr ⟨t3, le_of_lt (by rw [ht3s]; exact hs_pos), ?_⟩
      rw [hxsub, ht2, zero_smul, zero_add]

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

/-! ## PROVE_SLICING_FAN support kit (lane la6-slice-w4)

Port of the fan7 new-edge cone analysis (HOL `local_lemmas1.hl:1378`): the
cone algebra (`affGe`/`affGt` renders), the wedge exclusion at a face tail
(`noRayOfFaceTail`), the open-cone/old-edge-cone miss (`openConeMissEdge`),
and the fan7 augmentation assembly.  All helpers private. -/

/-- 锥点渲染：`x ∈ affGe {0} {v, w}` ⟹ 非负系数组合。 -/
private theorem sliceW4_affGePairRender {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) {x : V3}
    (hx : x ∈ affGe ({0} : Set V3) ({v, w} : Set V3)) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • v + t • w := by
  rw [affGe, Set.mem_setOf_eq, Affsign] at hx
  obtain ⟨f, hfin, hval, hsgn, hsum⟩ := hx
  have h3 : hfin.toFinset = ({(0:V3), v, w} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({v, w} : Finset V3) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hv0 h'
    · exact hw0 (Finset.mem_singleton.mp h')
  have hvn : (v:V3) ∉ ({w} : Finset V3) := fun h =>
    hwv (Finset.mem_singleton.mp h).symm
  have hsumV : ∑ q ∈ hfin.toFinset, f q • q
      = f (0:V3) • (0:V3) + f v • v + f w • w := by
    rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton]
    simp [add_assoc]
  rw [hsumV] at hval
  refine ⟨f v, f w, hsgn v (by simp), hsgn w (by simp), ?_⟩
  rw [hval]
  simp [add_assoc]

/-- 开锥点渲染：`x ∈ affGt {0} {v, w}` ⟹ 正系数组合。 -/
private theorem sliceW4_affGtPairRender {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) {x : V3}
    (hx : x ∈ affGt ({0} : Set V3) ({v, w} : Set V3)) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ x = s • v + t • w := by
  rw [affGt, Set.mem_setOf_eq, Affsign] at hx
  obtain ⟨f, hfin, hval, hsgn, hsum⟩ := hx
  have h3 : hfin.toFinset = ({(0:V3), v, w} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({v, w} : Finset V3) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hv0 h'
    · exact hw0 (Finset.mem_singleton.mp h')
  have hvn : (v:V3) ∉ ({w} : Finset V3) := fun h =>
    hwv (Finset.mem_singleton.mp h).symm
  have hsumV : ∑ q ∈ hfin.toFinset, f q • q
      = f (0:V3) • (0:V3) + f v • v + f w • w := by
    rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton]
    simp [add_assoc]
  rw [hsumV] at hval
  refine ⟨f v, f w, hsgn v (by simp), hsgn w (by simp), ?_⟩
  rw [hval]
  simp [add_assoc]

/-- 严格锥成员：正系数组合落在开锥 `affGt {0} {v, w}`。 -/
private theorem sliceW4_affGtPairOfSums {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : V3) (hx : x = s • v + t • w) :
    x ∈ affGt ({0} : Set V3) ({v, w} : Set V3) := by
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  have hfin : (({(0:V3)} : Set V3) ∪ ({v, w} : Set V3)).Finite := by simp
  have h3 : hfin.toFinset = ({(0:V3), v, w} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({v, w} : Finset V3) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hv0 h'
    · exact hw0 (Finset.mem_singleton.mp h')
  have hvn : (v:V3) ∉ ({w} : Finset V3) := fun h =>
    hwv (Finset.mem_singleton.mp h).symm
  refine ⟨fun z => if z = v then s else if z = w then t else 1 - s - t, hfin,
    ?_, ?_, ?_⟩
  · rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton]
    show x = (if (0:V3) = v then s else if (0:V3) = w then t else 1 - s - t) • (0:V3)
        + ((if (v:V3) = v then s else if (v:V3) = w then t else 1 - s - t) • v
          + (if (w:V3) = v then s else if (w:V3) = w then t else 1 - s - t) • w)
    rw [if_neg hv0, if_neg hw0, if_pos rfl, if_neg hwv, if_pos rfl, hx]
    simp
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h1 | h1
    · rw [h1]
      show 0 < (if (v:V3) = v then s else if (v:V3) = w then t else 1 - s - t)
      rw [if_pos rfl]
      exact hs
    · rw [h1]
      show 0 < (if (w:V3) = v then s else if (w:V3) = w then t else 1 - s - t)
      rw [if_neg hwv, if_pos rfl]
      exact ht
  · rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton]
    show (if (0:V3) = v then s else if (0:V3) = w then t else 1 - s - t)
        + ((if (v:V3) = v then s else if (v:V3) = w then t else 1 - s - t)
          + (if (w:V3) = v then s else if (w:V3) = w then t else 1 - s - t)) = 1
    rw [if_neg hv0, if_neg hw0, if_pos rfl, if_neg hwv, if_pos rfl]
    ring

/-- 单点锥渲染：`x ∈ affGe {0} {u}` ⟹ `x = r • u`，`r ≥ 0`。 -/
private theorem sliceW4_affGeOneRender {u : V3} (hu0 : (0:V3) ≠ u)
    {x : V3} (hx : x ∈ affGe ({0} : Set V3) ({u} : Set V3)) :
    ∃ r : ℝ, 0 ≤ r ∧ x = r • u := by
  rw [affGe, Set.mem_setOf_eq, Affsign] at hx
  obtain ⟨f, hfin, hval, hsgn, hsum⟩ := hx
  have h3 : hfin.toFinset = ({(0:V3), u} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({u} : Finset V3) := fun h => hu0 (Finset.mem_singleton.mp h)
  have hsumV : ∑ q ∈ hfin.toFinset, f q • q = f (0:V3) • (0:V3) + f u • u := by
    rw [h3, Finset.sum_insert h0n, Finset.sum_singleton]
  rw [hsumV] at hval
  refine ⟨f u, hsgn u (by simp), ?_⟩
  rw [hval]
  simp

/-- 双点锥成员（非负系数）：`s•v + t•w ∈ affGe {0} {v, w}`。 -/
private theorem sliceW4_memConePair {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s • v + t • w ∈ affGe ({0} : Set V3) ({v, w} : Set V3) := by
  have hfin : (({(0:V3)} : Set V3) ∪ ({v, w} : Set V3)).Finite := by simp
  have h3 : hfin.toFinset = ({(0:V3), v, w} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({v, w} : Finset V3) := by
    intro h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hv0 h'
    · exact hw0 (Finset.mem_singleton.mp h')
  have hvn : (v:V3) ∉ ({w} : Finset V3) := fun h =>
    hwv (Finset.mem_singleton.mp h).symm
  set f : V3 → ℝ := fun z => if z = (0:V3) then 1 - s - t else if z = v then s else t
    with hf
  have f0 : f (0:V3) = 1 - s - t := by simp [hf]
  have fv : f v = s := by simp [hf, Ne.symm hv0]
  have fw : f w = t := by simp [hf, Ne.symm hw0, hwv]
  refine ⟨f, hfin, ?_, ?_, ?_⟩
  · rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton,
      f0, fv, fw]
    simp only [smul_zero, zero_add]
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h1 | h1
    · subst h1; rw [fv]; exact hs
    · subst h1; rw [fw]; exact ht
  · rw [h3, Finset.sum_insert h0n, Finset.sum_insert hvn, Finset.sum_singleton,
      f0, fv, fw]
    ring

/-- 零向量在双点锥中：`0 ∈ affGe {0} {v, w}`。 -/
private theorem sliceW4_zeroMemConePair {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) :
    (0:V3) ∈ affGe ({0} : Set V3) ({v, w} : Set V3) := by
  have h := sliceW4_memConePair hv0 hw0 hwv (s := 0) (t := 0) (le_refl 0) (le_refl 0)
  simpa using h

/-- 单点锥成员（非负系数）：`r•u ∈ affGe {0} {u}`。 -/
private theorem sliceW4_memConeOne {u : V3} (hu0 : (0:V3) ≠ u) {r : ℝ}
    (hr : 0 ≤ r) :
    r • u ∈ affGe ({0} : Set V3) ({u} : Set V3) := by
  have hfin : (({(0:V3)} : Set V3) ∪ ({u} : Set V3)).Finite := by simp
  have h3 : hfin.toFinset = ({(0:V3), u} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  have h0n : (0:V3) ∉ ({u} : Finset V3) := fun h => hu0 (Finset.mem_singleton.mp h)
  set f : V3 → ℝ := fun z => if z = (0:V3) then 1 - r else r with hf
  have f0 : f (0:V3) = 1 - r := by simp [hf]
  have fu : f u = r := by simp [hf, Ne.symm hu0]
  refine ⟨f, hfin, ?_, ?_, ?_⟩
  · rw [h3, Finset.sum_insert h0n, Finset.sum_singleton, f0, fu]
    simp only [smul_zero, zero_add]
  · intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    rw [fu]
    exact hr
  · rw [h3, Finset.sum_insert h0n, Finset.sum_singleton, f0, fu]
    ring

/-- 零向量在单点锥中：`0 ∈ affGe {0} {u}`。 -/
private theorem sliceW4_zeroMemConeOne {u : V3} (hu0 : (0:V3) ≠ u) :
    (0:V3) ∈ affGe ({0} : Set V3) ({u} : Set V3) := by
  have h := sliceW4_memConeOne hu0 (r := 0) (le_refl 0)
  simpa using h

/-- 空 apex 锥塌缩为原点：`affGe {0} ∅ = {0}`（集合形式）。 -/
private theorem sliceW4_affGeEmptySet :
    affGe ({0} : Set V3) (∅ : Set V3) = ({(0:V3)} : Set V3) := by
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · intro hq
    rw [affGe, Set.mem_setOf_eq, Affsign] at hq
    obtain ⟨f, hfin, hval, -, hsum⟩ := hq
    have h3 : hfin.toFinset = ({(0:V3)} : Finset V3) := by
      ext z
      simp
    rw [h3, Finset.sum_singleton] at hval hsum
    rw [hval, hsum]
    simp
  · intro hq
    rw [hq]
    simp only [affGe, Set.mem_setOf_eq, Affsign]
    have hfin : (({(0:V3)} : Set V3) ∪ (∅ : Set V3)).Finite := by simp
    have h3 : hfin.toFinset = ({(0:V3)} : Finset V3) := by
      ext z
      simp
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [h3, Finset.sum_singleton]
      simp
    · intro z hz
      exact absurd hz (Set.notMem_empty z)
    · rw [h3, Finset.sum_singleton]

/-- 单点锥落双点锥：`affGe {0} {v} ⊆ affGe {0} {v, w}`。 -/
private theorem sliceW4_coneOneSubsetConePair {v w : V3} (hv0 : (0:V3) ≠ v)
    (hw0 : (0:V3) ≠ w) (hwv : w ≠ v) :
    affGe ({0} : Set V3) ({v} : Set V3) ⊆ affGe ({0} : Set V3) ({v, w} : Set V3) := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := sliceW4_affGeOneRender hv0 hx
  have h := sliceW4_memConePair hv0 hw0 hwv (s := r) (t := 0) hr (le_refl 0)
  rw [hx]
  simpa using h

/-- 单点锥的 smul 成员：`x = r•u`、`0 ≤ r` ⟹ `x ∈ affGe {0} {u}`。 -/
private theorem sliceW4_coneOneOfSmul {u : V3} (hu0 : (0:V3) ≠ u) {r : ℝ}
    (hr : 0 ≤ r) {x : V3} (hx : x = r • u) :
    x ∈ affGe ({0} : Set V3) ({u} : Set V3) := by
  rw [hx]
  exact sliceW4_memConeOne hu0 hr

/-- 边的两元素提取（`Graph E` 的 HAS_SIZE 2）。 -/
private theorem sliceW4_edgePairElms {V : Set V3} {E : Set (Set V3)}
    (hF : FAN 0 V E) {e2 : Set V3} (he2 : e2 ∈ E) :
    ∃ y y' : V3, y ≠ y' ∧ e2 = ({y, y'} : Set V3) := by
  obtain ⟨hfin, hcard⟩ := hF.2.1 e2 he2
  have hnc : e2.ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card e2 hfin]
    exact hcard
  exact Set.ncard_eq_two.mp hnc

/-- 零向量在旧边锥中。 -/
private theorem sliceW4_zeroConeEdge {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : localFan_p2 V E FF) {e2 : Set V3} (he2 : e2 ∈ E) :
    (0:V3) ∈ affGe ({0} : Set V3) e2 := by
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := h
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  obtain ⟨y, y', hyy, he2y⟩ := sliceW4_edgePairElms hF he2
  have hyV : y ∈ V := hF.1 (Set.mem_sUnion_of_mem (by rw [he2y]; simp) he2)
  have hy'V : y' ∈ V := hF.1 (Set.mem_sUnion_of_mem (by rw [he2y]; simp) he2)
  rw [he2y]
  exact sliceW4_zeroMemConePair (fun hc => h0V (hc ▸ hyV))
    (fun hc => h0V (hc ▸ hy'V)) (fun hc => hyy hc.symm)

/-- 双邻点楔展开：`wedgeInFanGt_p2 (a,b) E` 在 `1 < ncard` 时是开扇形。 -/
private theorem sliceW4_wedgeUnpackPair {a b : V3} {E : Set (Set V3)}
    (hc2 : 1 < (EE_p2 a E).ncard) :
    wedgeInFanGt_p2 (a, b) E
      = wedge 0 a b (azimCycle_p2 (EE_p2 a E) 0 a b) := by
  rw [wedgeInFanGt_p2, if_pos hc2]

/-- 二元 `azimCycle` 取另一邻居。 -/
private theorem sliceW4_azimCyclePair {a b c : V3} {E : Set (Set V3)}
    (hEE : EE_p2 a E = ({b, c} : Set V3)) :
    azimCycle_p2 (EE_p2 a E) 0 a b = c := by
  rw [hEE]
  exact AZIM_CYCLE_TWO_POINT_SET b c 0 a

/-- `AzimSpec` 的射线缩放 + 轴向平移不变性（HOL `AZIM_EQ` 机制）。 -/
private theorem sliceW4_azimSpecRayShift {v w w1 w2 : V3} {θ c t : ℝ}
    (hwv : w ≠ v) (hc : 0 < c) (h : AzimSpec v w w1 w2 θ) :
    AzimSpec v w w1 (v + c • (w2 - v) + t • (w - v)) θ := by
  obtain ⟨hb0, hb1, hh1, hh2, hframes⟩ := h
  refine ⟨hb0, hb1, hh1, c * hh2 + t, ?_⟩
  intro e1 e2 e3 hon hax _
  obtain ⟨ψ, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframes e1 e2 e3 hon hax hwv
  refine ⟨ψ, r1, c * r2, hrep1, ?_, hr1, mul_pos hc hr2⟩
  have hpt : v + c • (w2 - v) + t • (w - v) - v = c • (w2 - v) + t • (w - v) := by
    rw [add_assoc, add_sub_cancel_left]
  rw [hpt, hrep2]
  module

/-- 方位角的射线-轴平移不变（消费形）：`x = c•z + t•y`（`0 < c`）时自 `z`
与自 `x` 的方位相同。 -/
private theorem sliceW4_azimConeRay {y b z x : V3} {c t : ℝ}
    (hy0 : y ≠ (0:V3)) (hc : 0 < c)
    (hx : x = c • z + t • y)
    (hnb : ¬ Collinear ℝ ({0, y, b} : Set V3))
    (hnz : ¬ Collinear ℝ ({0, y, z} : Set V3))
    (hnx : ¬ Collinear ℝ ({0, y, x} : Set V3)) :
    azim (0:V3) y b x = azim (0:V3) y b z := by
  obtain ⟨θ, hθ⟩ := azimSpec_exists (v := (0:V3)) (w := y) (w1 := b) (w2 := z) hnb hnz
  have h1 := azim_eq_of_spec (v := (0:V3)) (w := y) (w1 := b) (w2 := z) hnb hnz hθ
  have hrs := sliceW4_azimSpecRayShift (v := (0:V3)) (w := y) (w1 := b) (w2 := z)
    (θ := θ) (c := c) (t := t) hy0 hc hθ
  have heq : (0:V3) + c • (z - (0:V3)) + t • (y - (0:V3)) = c • z + t • y := by
    simp only [sub_zero, zero_add]
  have hrs' : AzimSpec (0:V3) y b x θ := by
    rw [hx, ← heq]
    exact hrs
  exact (azim_eq_of_spec hnb hnx hrs').trans h1.symm

/-- **面尾射线排除**：`u` 是某 FF dart 的尾 ⟹ `u` 射线不在对角开锥内
（切片楔以 `u` 为轴，`wedge` 的共线支直接排除）。 -/
private theorem sliceW4_noRayOfFaceTail {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w u : V3} (h : localFan_p2 V E FF)
    (hu : u ∈ V)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    {b : V3} (hd : (u, b) ∈ FF) :
    u ∉ affGt ({0} : Set V3) ({v, w} : Set V3) := by
  have hc2 : 1 < (EE_p2 u E).ncard := by
    have h2 := LOFA_CARD_EE_V_1 h hu
    omega
  have hu' := hsub (u, b) hd
  rw [sliceW4_wedgeUnpackPair (a := u) (b := b) hc2] at hu'
  intro huA
  obtain ⟨hnc, -, -⟩ := hu' huA
  exact hnc (collinear3_pair_right (v0 := (0:V3)) (v1 := u) (x := u) rfl)

/-- **开锥-旧边锥楔排除**：`e2 ∈ E` 的闭锥与对角开锥至多交于原点。内点支 =
面尾 dart 的切片楔（hsub）+ azim 正缩放不变 + 二元 `azimCycle` 取定另一邻居；
边界支 = 正缩放把边端点归入对角开锥，被面尾射线排除。 -/
private theorem sliceW4_openConeMissEdge {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {p q : V3} (h : localFan_p2 V E FF)
    (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 x E)
    {e2 : Set V3} (he2 : e2 ∈ E) {x : V3}
    (hxgt : x ∈ affGt ({0} : Set V3) ({p, q} : Set V3))
    (hxe : x ∈ affGe ({0} : Set V3) e2) :
    x = (0:V3) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  have hp0 : (0:V3) ≠ p := fun hc => h0V (hc ▸ hp)
  have hq0 : (0:V3) ≠ q := fun hc => h0V (hc ▸ hq)
  obtain ⟨y, y', hyy, he2y⟩ := sliceW4_edgePairElms hF he2
  have hyy' : y' ≠ y := fun hc => hyy hc.symm
  have he2' : ({y, y'} : Set V3) ∈ E := by rw [← he2y]; exact he2
  have hyEe : y ∈ e2 := by rw [he2y]; simp
  have hy'Ee : y' ∈ e2 := by rw [he2y]; simp
  have hyV : y ∈ V := hF.1 (Set.mem_sUnion_of_mem hyEe he2)
  have hyV' : y' ∈ V := hF.1 (Set.mem_sUnion_of_mem hy'Ee he2)
  have hy0 : y ≠ (0:V3) := fun hc => h0V (hc ▸ hyV)
  have hy'0 : y' ≠ (0:V3) := fun hc => h0V (hc ▸ hyV')
  -- 面尾 dart 与射线排除
  have hdFF : (y, rhoNode1_p2 FF y) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 y hyV
  have hdFF' : (y', rhoNode1_p2 FF y') ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 y' hyV'
  have hny := sliceW4_noRayOfFaceTail h hyV hsub hdFF
  have hny' := sliceW4_noRayOfFaceTail h hyV' hsub hdFF'
  -- 开锥与 e2 锥渲染
  obtain ⟨a, b, ha0, hb0, hxab⟩ := sliceW4_affGtPairRender hp0 hq0 (Ne.symm hpq) hxgt
  rw [he2y] at hxe
  obtain ⟨s, t, hs0, ht0, hxst⟩ :=
    sliceW4_affGePairRender (Ne.symm hy0) (Ne.symm hy'0) hyy' hxe
  rcases le_iff_eq_or_lt.mp hs0 with rfl | hs
  · -- s = 0：x = t•y'
    rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
    · simp at hxst
      exact hxst
    · have hx'eq : x = t • y' := by rw [hxst]; simp
      have hy'inv : y' = t⁻¹ • x := by
        rw [hx'eq, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
      exact absurd (sliceW4_affGtPairOfSums hp0 hq0 (Ne.symm hpq)
        (mul_pos (inv_pos.mpr ht) ha0) (mul_pos (inv_pos.mpr ht) hb0) y'
        (by rw [hy'inv, hxab]; module)) hny'
  · -- s > 0
    rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
    · -- 边界射线：y 正缩放归入对角开锥，楔排除
      have hxeq : x = s • y := by rw [hxst]; simp
      have hyinv : y = s⁻¹ • x := by
        rw [hxeq, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
      exact absurd (sliceW4_affGtPairOfSums hp0 hq0 (Ne.symm hpq)
        (mul_pos (inv_pos.mpr hs) ha0) (mul_pos (inv_pos.mpr hs) hb0) y
        (by rw [hyinv, hxab]; module)) hny
    · -- 内点支：面尾 dart (y, db) 的切片楔 + azim 正缩放不变
      have hc2 : 1 < (EE_p2 y E).ncard := by
        have h2 := LOFA_CARD_EE_V_1 h hyV
        omega
      have hwedge := hsub (y, rhoNode1_p2 FF y) hdFF
      rw [sliceW4_wedgeUnpackPair (a := y) (b := rhoNode1_p2 FF y) hc2] at hwedge
      have hdE : ({y, rhoNode1_p2 FF y} : Set V3) ∈ E := by
        have ho := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdFF
        simpa only [ordPairs_p2, Set.mem_setOf_eq] using ho
      have hdEE : rhoNode1_p2 FF y ∈ EE_p2 y E := hdE
      have hncdb : ¬ Collinear ℝ ({0, y, rhoNode1_p2 FF y} : Set V3) :=
        LOCAL_FAN_IN_FF_NOT_COLLINEAR (d := (y, rhoNode1_p2 FF y)) h hdFF
      have hncyy' : ¬ Collinear ℝ ({0, y, y'} : Set V3) :=
        hF.2.2.2.2.1 ({y, y'} : Set V3) he2'
      -- EE y E = {db, c2}
      obtain ⟨c2, hdc2, hEEins⟩ :
          ∃ c2 : V3, rhoNode1_p2 FF y ≠ c2 ∧
            (EE_p2 y E) = ({rhoNode1_p2 FF y, c2} : Set V3) := by
        obtain ⟨p1, q1, hpq1, hEE1⟩ := Set.ncard_eq_two.mp (LOFA_CARD_EE_V_1 h hyV)
        have hdbins : rhoNode1_p2 FF y ∈ ({p1, q1} : Set V3) := by
          rw [← hEE1]; exact hdEE
        have hdb2 : rhoNode1_p2 FF y = p1 ∨ rhoNode1_p2 FF y = q1 := by
          rcases Set.mem_insert_iff.mp hdbins with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Set.mem_singleton_iff.mp hh)
        rcases hdb2 with hh | hh
        · exact ⟨q1, fun hc => hpq1 (hh ▸ hc), by rw [hEE1, hh]⟩
        · exact ⟨p1, fun hc => hpq1 (hc.symm.trans hh),
            by rw [hEE1, hh, Set.pair_comm p1 q1]⟩
      have hdd : azimCycle_p2 (EE_p2 y E) (0:V3) y (rhoNode1_p2 FF y) = c2 :=
        sliceW4_azimCyclePair hEEins
      have hxw : x ∈ wedge (0:V3) y (rhoNode1_p2 FF y) c2 := by
        rw [← hdd]
        exact hwedge hxgt
      obtain ⟨hncx, hpos, hupper⟩ := hxw
      -- 正缩放下 x 与 y' 同方位
      have hazim : azim (0:V3) y (rhoNode1_p2 FF y) x
          = azim (0:V3) y (rhoNode1_p2 FF y) y' :=
        sliceW4_azimConeRay (y := y) (b := rhoNode1_p2 FF y) (z := y') (c := t) (t := s)
          hy0 ht (by rw [hxst]; module) hncdb hncyy'
          (show ¬ Collinear ℝ ({0, y, x} : Set V3) from hncx)
      -- y' 是 y 的邻居：{db, c2} 两者皆矛盾
      have hy'ins : y' ∈ ({rhoNode1_p2 FF y, c2} : Set V3) := by
        rw [← hEEins]
        exact he2'
      have hy'eq : y' = rhoNode1_p2 FF y ∨ y' = c2 := by
        rcases Set.mem_insert_iff.mp hy'ins with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Set.mem_singleton_iff.mp h1)
      rcases hy'eq with h1 | h1
      · rw [h1] at hazim
        rw [hazim, azim_self] at hpos
        exact (lt_irrefl (0:ℝ) hpos).elim
      · rw [h1] at hazim
        rw [hazim] at hupper
        exact (lt_irrefl _ hupper).elim

/-- **fan7 对角支（`p ∈ e2`、`q ∉ e2`）**：旧边 `e2` 与对角锥的分配律，
RHS 塌缩为 `affGe {0} {p}`。 -/
private theorem sliceW4_fan7NewEdgeHit {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {p q : V3} (h : localFan_p2 V E FF)
    (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 x E)
    {e2 : Set V3} (he2 : e2 ∈ E) (hpE : p ∈ e2) (hqE : q ∉ e2) :
    affGe ({0} : Set V3) ({p, q} : Set V3) ∩ affGe ({0} : Set V3) e2
      = affGe ({0} : Set V3) (({p, q} : Set V3) ∩ e2) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  have hp0 : (0:V3) ≠ p := fun hc => h0V (hc ▸ hp)
  have hq0 : (0:V3) ≠ q := fun hc => h0V (hc ▸ hq)
  have h7 : Kepler.Text.Fan.fan7 0 V E := hF.2.2.2.2.2
  have hint : ({p, q} : Set V3) ∩ e2 = ({p} : Set V3) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨(h1 | h1), h2⟩
      · exact h1
      · exact absurd (h1 ▸ h2) hqE
    · rintro h1
      exact ⟨Or.inl h1, h1 ▸ hpE⟩
  rw [hint]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨s, t, hs0, ht0, hxst⟩ := sliceW4_affGePairRender hp0 hq0 (Ne.symm hpq) hxA
    rcases le_iff_eq_or_lt.mp hs0 with rfl | hs
    · rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
      · simp at hxst
        rw [hxst]
        exact sliceW4_zeroMemConeOne hp0
      · -- x = t•q ∈ cone{q}；h7：cone{q} ∩ cone e2 = {0}
        have h7q : affGe ({0} : Set V3) ({q} : Set V3) ∩ affGe ({0} : Set V3) e2
            = affGe ({0} : Set V3) (({q} : Set V3) ∩ e2) :=
          h7 ({q} : Set V3) (Set.mem_union_right _
            (show ({q} : Set V3) ∈ {s : Set V3 | ∃ u ∈ V, s = ({u} : Set V3)} from
              ⟨q, hq, rfl⟩)) e2 (Set.mem_union_left _ he2)
        rw [Set.singleton_inter_of_notMem hqE, sliceW4_affGeEmptySet] at h7q
        have hxq : x = t • q := by rw [hxst]; simp
        have hx0 : x ∈ ({(0:V3)} : Set V3) := by
          rw [← h7q]
          exact ⟨sliceW4_coneOneOfSmul hq0 ht.le hxq, hxB⟩
        rw [Set.mem_singleton_iff] at hx0
        rw [hx0]
        exact sliceW4_zeroMemConeOne hp0
    · rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
      · simp at hxst
        exact sliceW4_coneOneOfSmul hp0 hs.le hxst
      · -- 开锥点：与旧边闭锥至多交于原点
        have hxgt : x ∈ affGt ({0} : Set V3) ({p, q} : Set V3) :=
          sliceW4_affGtPairOfSums hp0 hq0 (Ne.symm hpq) hs ht x hxst
        rw [sliceW4_openConeMissEdge h hp hq hpq hsub he2 hxgt hxB]
        exact sliceW4_zeroMemConeOne hp0
  · intro hx
    have h7p : affGe ({0} : Set V3) ({p} : Set V3) ∩ affGe ({0} : Set V3) e2
        = affGe ({0} : Set V3) (({p} : Set V3) ∩ e2) :=
      h7 ({p} : Set V3) (Set.mem_union_right _
        (show ({p} : Set V3) ∈ {s : Set V3 | ∃ u ∈ V, s = ({u} : Set V3)} from
          ⟨p, hp, rfl⟩)) e2 (Set.mem_union_left _ he2)
    rw [Set.singleton_inter_of_mem hpE] at h7p
    have hxAB : x ∈ affGe ({0} : Set V3) ({p} : Set V3) ∩ affGe ({0} : Set V3) e2 := by
      rw [h7p]
      exact hx
    exact ⟨sliceW4_coneOneSubsetConePair hp0 hq0 (Ne.symm hpq) hx, hxAB.2⟩

/-- **fan7 对角支（不交支）**：旧边 `e2` 与对角无公共元素时 RHS 塌缩为 `{0}`。 -/
private theorem sliceW4_fan7NewEdgeDisj {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {p q : V3} (h : localFan_p2 V E FF)
    (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {p, q} ⊆ wedgeInFanGt_p2 x E)
    {e2 : Set V3} (he2 : e2 ∈ E) (hpE : p ∉ e2) (hqE : q ∉ e2) :
    affGe ({0} : Set V3) ({p, q} : Set V3) ∩ affGe ({0} : Set V3) e2
      = affGe ({0} : Set V3) (({p, q} : Set V3) ∩ e2) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  have hp0 : (0:V3) ≠ p := fun hc => h0V (hc ▸ hp)
  have hq0 : (0:V3) ≠ q := fun hc => h0V (hc ▸ hq)
  have h7 : Kepler.Text.Fan.fan7 0 V E := hF.2.2.2.2.2
  have hint : ({p, q} : Set V3) ∩ e2 = (∅ : Set V3) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.notMem_empty]
    constructor
    · rintro ⟨(h1 | h1), h2⟩
      · exact hpE (h1 ▸ h2)
      · exact hqE (h1 ▸ h2)
    · exact fun h => h.elim
  rw [hint, sliceW4_affGeEmptySet]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxA, hxB⟩
    obtain ⟨s, t, hs0, ht0, hxst⟩ := sliceW4_affGePairRender hp0 hq0 (Ne.symm hpq) hxA
    rcases le_iff_eq_or_lt.mp hs0 with rfl | hs
    · rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
      · simp at hxst
        exact hxst
      · have h7q : affGe ({0} : Set V3) ({q} : Set V3) ∩ affGe ({0} : Set V3) e2
            = affGe ({0} : Set V3) (({q} : Set V3) ∩ e2) :=
          h7 ({q} : Set V3) (Set.mem_union_right _
            (show ({q} : Set V3) ∈ {s : Set V3 | ∃ u ∈ V, s = ({u} : Set V3)} from
              ⟨q, hq, rfl⟩)) e2 (Set.mem_union_left _ he2)
        rw [Set.singleton_inter_of_notMem hqE, sliceW4_affGeEmptySet] at h7q
        have hxq : x = t • q := by rw [hxst]; simp
        have hx0 : x ∈ ({(0:V3)} : Set V3) := by
          rw [← h7q]
          exact ⟨sliceW4_coneOneOfSmul hq0 ht.le hxq, hxB⟩
        rw [Set.mem_singleton_iff] at hx0
        exact hx0
    · rcases le_iff_eq_or_lt.mp ht0 with rfl | ht
      · have h7p : affGe ({0} : Set V3) ({p} : Set V3) ∩ affGe ({0} : Set V3) e2
            = affGe ({0} : Set V3) (({p} : Set V3) ∩ e2) :=
          h7 ({p} : Set V3) (Set.mem_union_right _
            (show ({p} : Set V3) ∈ {s : Set V3 | ∃ u ∈ V, s = ({u} : Set V3)} from
              ⟨p, hp, rfl⟩)) e2 (Set.mem_union_left _ he2)
        rw [Set.singleton_inter_of_notMem hpE, sliceW4_affGeEmptySet] at h7p
        have hxp : x = s • p := by rw [hxst]; simp
        have hx0 : x ∈ ({(0:V3)} : Set V3) := by
          rw [← h7p]
          exact ⟨sliceW4_coneOneOfSmul hp0 hs.le hxp, hxB⟩
        rw [Set.mem_singleton_iff] at hx0
        exact hx0
      · have hxgt : x ∈ affGt ({0} : Set V3) ({p, q} : Set V3) :=
          sliceW4_affGtPairOfSums hp0 hq0 (Ne.symm hpq) hs ht x hxst
        exact sliceW4_openConeMissEdge h hp hq hpq hsub he2 hxgt hxB
  · intro hx
    subst hx
    exact ⟨sliceW4_zeroMemConePair hp0 hq0 (Ne.symm hpq), sliceW4_zeroConeEdge h he2⟩

/-- **fan7 对角支（`e2 ∈ E` 全形）**：`e2` 含 `v`、`w` 皆含（⟹ `e2 = {v,w}`，
两锥自交）、含一（Hit）、皆不含（Disj）三分。 -/
private theorem sliceW4_fan7NewEdge {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} (h : localFan_p2 V E FF)
    (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    {e2 : Set V3} (he2 : e2 ∈ E) :
    affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affGe ({0} : Set V3) e2
      = affGe ({0} : Set V3) (({v, w} : Set V3) ∩ e2) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  by_cases hvE : v ∈ e2
  · by_cases hwE : w ∈ e2
    · -- e2 ⊇ {v,w} ⟹ e2 = {v,w}（两元素），两锥自交
      have he2eq : e2 = ({v, w} : Set V3) := by
        have hsubvw : ({v, w} : Set V3) ⊆ e2 := by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact hvE
          · rw [Set.mem_singleton_iff] at hz
            exact hz ▸ hwE
        have hn2e : e2.ncard = 2 := by
          obtain ⟨hfin, hcard⟩ := hF.2.1 e2 he2
          rw [Set.ncard_eq_toFinset_card e2 hfin]
          exact hcard
        have hn2v : ({v, w} : Set V3).ncard = 2 := (SET2_HAS_SIZE2 v w).mpr hwv
        have hfin2 : e2.Finite := by
          obtain ⟨hfin, -⟩ := hF.2.1 e2 he2
          exact hfin
        exact (Set.eq_of_subset_of_ncard_le hsubvw (by rw [hn2e, hn2v]) hfin2).symm
      rw [he2eq]
      simp only [Set.inter_self]
    · exact sliceW4_fan7NewEdgeHit h hv hw hwv hsub he2 hvE hwE
  · by_cases hwE : w ∈ e2
    · -- w ∈ e2、v ∉ e2：换序套用 Hit
      have hsub' : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
        intro x hx z hz
        rw [Set.pair_comm w v] at hz
        exact hsub x hx hz
      rw [Set.pair_comm v w]
      exact sliceW4_fan7NewEdgeHit h hw hv hwv.symm hsub' he2 hwE hvE
    · exact sliceW4_fan7NewEdgeDisj h hv hw hwv hsub he2 hvE hwE

/-- **fan7 单点支（`{u}`，`u ∉ {v,w}`）**：`u` 射线与对角锥至多交于原点；
`u = c•v` / `u = c•w` 支由 `hcol` 非共线排除，双正系数支由面尾射线排除。 -/
private theorem sliceW4_fan7AugSingleton {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w u : V3} (h : localFan_p2 V E FF)
    (hv : v ∈ V) (hw : w ∈ V) (hu : u ∈ V) (hwv : v ≠ w) (huv : u ≠ v) (huw : u ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affGe ({0} : Set V3) ({u} : Set V3)
      = affGe ({0} : Set V3) (({v, w} : Set V3) ∩ ({u} : Set V3)) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  have hv0 : (0:V3) ≠ v := fun hc => h0V (hc ▸ hv)
  have hw0 : (0:V3) ≠ w := fun hc => h0V (hc ▸ hw)
  have hu0 : (0:V3) ≠ u := fun hc => h0V (hc ▸ hu)
  have hv0' : v ≠ (0:V3) := fun hc => hv0 hc.symm
  have hw0' : w ≠ (0:V3) := fun hc => hw0 hc.symm
  have hdFF : (u, rhoNode1_p2 FF u) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 u hu
  have hnoray := sliceW4_noRayOfFaceTail h hu hsub hdFF
  have huv' : v ≠ u := fun hc => huv hc.symm
  have huw' : w ≠ u := fun hc => huw hc.symm
  ext x
  by_cases huab : u ∈ ({v, w} : Set V3)
  · -- u ∈ {v, w}：纯锥代数
    rcases Set.mem_insert_iff.mp huab with hue | hue
    · have hue' : u = v := hue
      have hint2 : ({v, w} : Set V3) ∩ ({u} : Set V3) = ({u} : Set V3) := by
        rw [hue']
        ext q
        simp
      rw [hint2]
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hxu⟩
        exact hxu
      · intro hxu
        rw [hue'] at hxu ⊢
        exact ⟨sliceW4_coneOneSubsetConePair hv0 hw0 (Ne.symm hwv) hxu, hxu⟩
    · have hue' : u = w := Set.mem_singleton_iff.mp hue
      have hint2 : ({v, w} : Set V3) ∩ ({u} : Set V3) = ({u} : Set V3) := by
        rw [hue']
        ext q
        simp
      rw [hint2]
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hxu⟩
        exact hxu
      · intro hxu
        rw [hue'] at hxu ⊢
        rw [Set.pair_comm v w]
        exact ⟨sliceW4_coneOneSubsetConePair hw0 hv0 hwv hxu, hxu⟩
  · -- u ∉ {v, w}：RHS 塌缩为 {0}，LHS 射线归位排除
    have hint : ({v, w} : Set V3) ∩ ({u} : Set V3) = (∅ : Set V3) := by
      ext q
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.notMem_empty]
      constructor
      · rintro ⟨hIn, h2⟩
        rcases hIn with h1 | h1
        · subst h2
          exact huab (by rw [h1]; simp)
        · subst h2
          exact huab (by rw [h1]; simp)
      · exact fun h2 => h2.elim
    rw [hint, sliceW4_affGeEmptySet]
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxu⟩
      obtain ⟨s, t, hs0, ht0, hx⟩ := sliceW4_affGePairRender hv0 hw0 (Ne.symm hwv) hx
      obtain ⟨r, hr0, hxu⟩ := sliceW4_affGeOneRender hu0 hxu
      rcases eq_or_lt_of_le hr0 with hr | hr
      · rw [hxu, ← hr, zero_smul]
      · have huinv : u = r⁻¹ • x := by
          rw [hxu, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
        have huval : u = (r⁻¹ * s) • v + (r⁻¹ * t) • w := by
          rw [huinv, hx, smul_add, smul_smul, smul_smul]
        rcases Classical.em (s = 0) with hs | hs
        · rcases Classical.em (t = 0) with ht | ht
          · -- u = 0 ⟹ x = 0
            rw [hxu, huval, hs, ht, mul_zero, zero_smul, zero_smul, add_zero,
              smul_zero]
          · -- u = (r⁻¹ * t) • w：hcol 非共线排除
            rw [hs, mul_zero, zero_smul, zero_add] at huval
            have hcoluw := hcol w u (by simp) ⟨hu, by simp [huw]⟩
            exact absurd ((collinear3_iff_smul (v := (0:V3)) (w := w) (w1 := u)
              hw0').mpr ⟨r⁻¹ * t, by rw [huval]; simp⟩) hcoluw
        · rcases Classical.em (t = 0) with ht | ht
          · -- u = (r⁻¹ * s) • v：hcol 非共线排除
            rw [ht, mul_zero, zero_smul, add_zero] at huval
            have hcoluv := hcol v u (by simp) ⟨hu, by simp [huv]⟩
            exact absurd ((collinear3_iff_smul (v := (0:V3)) (w := v) (w1 := u)
              hv0').mpr ⟨r⁻¹ * s, by rw [huval]; simp⟩) hcoluv
          · -- 两系数皆正：u ∈ 开锥，面尾射线排除
            exact absurd (sliceW4_affGtPairOfSums hv0 hw0 (Ne.symm hwv)
              (mul_pos (inv_pos.mpr hr) (lt_of_le_of_ne hs0 (Ne.symm hs)))
              (mul_pos (inv_pos.mpr hr) (lt_of_le_of_ne ht0 (Ne.symm ht))) u huval)
              hnoray
    · intro hx
      subst hx
      exact ⟨sliceW4_zeroMemConePair hv0 hw0 (Ne.symm hwv), sliceW4_zeroMemConeOne hu0⟩

/-- **fan7 增广归约**：`E' = E ∪ {{v,w}}` 的 fan7 归约为旧 fan7 + 新边锥支。 -/
private theorem sliceW4_fan7Augment {V : Set V3} {E E' : Set (Set V3)}
    (h7 : Kepler.Text.Fan.fan7 0 V E)
    (hnew : ∀ e1 ∈ E' ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)},
      ∀ e2 ∈ E' ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)},
        e1 ∉ E ∨ e2 ∉ E →
        affGe ({0} : Set V3) e1 ∩ affGe ({0} : Set V3) e2
          = affGe ({0} : Set V3) (e1 ∩ e2)) :
    Kepler.Text.Fan.fan7 0 V E' := by
  intro e1 he1 e2 he2
  have h1mem : e1 ∈ E' ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)} := he1
  have h2mem : e2 ∈ E' ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)} := he2
  by_cases h1 : e1 ∈ E
  · rcases he2 with h2E | h2S
    · by_cases h2 : e2 ∈ E
      · exact h7 e1 (Set.mem_union_left _ h1) e2 (Set.mem_union_left _ h2)
      · exact hnew e1 h1mem e2 h2mem (Or.inr h2)
    · exact h7 e1 (Set.mem_union_left _ h1) e2 (Set.mem_union_right _ h2S)
  · rcases he1 with h1E | h1S
    · exact hnew e1 h1mem e2 h2mem (Or.inl h1)
    · rcases he2 with h2E | h2S
      · by_cases h2 : e2 ∈ E
        · exact h7 e1 (Set.mem_union_right _ h1S) e2 (Set.mem_union_left _ h2)
        · exact hnew e1 h1mem e2 h2mem (Or.inr h2)
      · exact h7 e1 (Set.mem_union_right _ h1S) e2 (Set.mem_union_right _ h2S)

/-- **hfan7new 全形**：增广 fan7 的新边支（对角自交 / 旧边 / 单点）。 -/
private theorem sliceW4_fan7New {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} (h : localFan_p2 V E FF)
    (hv : v ∈ V) (hw : w ∈ V) (hwv : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    ∀ e2 ∈ (E ∪ {{v, w}}) ∪ {s : Set V3 | ∃ u ∈ V, s = ({u} : Set V3)},
      affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affGe ({0} : Set V3) e2
        = affGe ({0} : Set V3) (({v, w} : Set V3) ∩ e2) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  have h0V : (0:V3) ∉ V := hF.2.2.2.1
  have hv0 : (0:V3) ≠ v := fun hc => h0V (hc ▸ hv)
  have hw0 : (0:V3) ≠ w := fun hc => h0V (hc ▸ hw)
  intro e2 he2
  rcases he2 with hE2 | hS2
  · rcases hE2 with hE | hD
    · exact sliceW4_fan7NewEdge h hv hw hwv hsub hE
    · rw [hD]
      simp only [Set.inter_self]
  · obtain ⟨u, huV, huD⟩ := hS2
    rw [huD]
    by_cases huab : u ∈ ({v, w} : Set V3)
    · rcases Set.mem_insert_iff.mp huab with hue | hue
      · -- u = v
        rw [hue, Set.inter_singleton_of_mem (by simp : v ∈ ({v, w} : Set V3))]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, hxv⟩
          exact hxv
        · intro hxv
          exact ⟨sliceW4_coneOneSubsetConePair hv0 hw0 (Ne.symm hwv) hxv, hxv⟩
      · -- u = w
        have hue' : u = w := Set.mem_singleton_iff.mp hue
        rw [hue', Set.inter_singleton_of_mem (by simp : w ∈ ({v, w} : Set V3))]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, hxw⟩
          exact hxw
        · intro hxw
          rw [Set.pair_comm v w]
          exact ⟨sliceW4_coneOneSubsetConePair hw0 hv0 hwv hxw, hxw⟩
    · exact sliceW4_fan7AugSingleton h hv hw huV hwv
        (fun hc => huab (by rw [hc]; simp))
        (fun hc => huab (by rw [hc]; simp)) hcol hsub

/-- HOL `PROVE_SLICING_FAN` (local_lemmas1.hl:1378) — giant. -/
theorem PROVE_SLICING_FAN (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E) :
    FAN 0 V (E ∪ {{v, w}}) := by
  have hkeep := h
  obtain ⟨-, -, -, -, -, hF, -, -⟩ := hkeep
  obtain ⟨hVE, hG, hf1, hf2, hf6, h7⟩ := hF
  refine ⟨?_, ?_, hf1, hf2, ?_, ?_⟩
  · -- ⋃₀ (E ∪ {{v,w}}) ⊆ V
    intro z hz
    obtain ⟨e, he, hze⟩ := hz
    rcases he with hEe | hDe
    · exact hVE (Set.mem_sUnion_of_mem hze hEe)
    · rw [show e = ({v, w} : Set V3) from hDe, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hze
      rcases hze with hh | hh
      · exact hh ▸ hv
      · exact hh ▸ hw
  · -- Graph (E ∪ {{v,w}})
    intro e he
    rcases he with hEe | hDe
    · exact hG e hEe
    · rw [show e = ({v, w} : Set V3) from hDe]
      have h2 : ({v, w} : Set V3).ncard = 2 := (SET2_HAS_SIZE2 v w).mpr hvw
      refine ⟨Set.Finite.insert v (Set.finite_singleton w), ?_⟩
      rw [← Set.ncard_eq_toFinset_card ({v, w} : Set V3)
        (Set.Finite.insert v (Set.finite_singleton w))]
      exact h2
  · -- fan6：新边非共线由 hcol
    intro e he
    rcases he with hEe | hDe
    · exact hf6 e hEe
    · rw [show e = ({v, w} : Set V3) from hDe]
      exact hcol v w (by simp)
        ⟨hw, fun hc => hvw (Set.mem_singleton_iff.mp hc).symm⟩
  · -- fan7：旧 fan7 + 新边锥支
    refine sliceW4_fan7Augment h7 ?_
    intro e1 he1 e2 he2 hd
    by_cases h1 : e1 = ({v, w} : Set V3)
    · rw [h1]
      exact sliceW4_fan7New h hv hw hvw hcol hsub e2 he2
    · by_cases h2 : e2 = ({v, w} : Set V3)
      · rw [h2]
        have H := sliceW4_fan7New h hv hw hvw hcol hsub e1 he1
        rw [Set.inter_comm (affGe ({0} : Set V3) ({v, w} : Set V3))
          (affGe ({0} : Set V3) e1), Set.inter_comm ({v, w} : Set V3) e1] at H
        exact H
      · have h1' : e1 ∈ E ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)} := by
          rcases he1 with hE1 | hS1
          · rcases hE1 with hh | hh
            · exact Set.mem_union_left _ hh
            · exact absurd hh h1
          · exact Set.mem_union_right _ hS1
        have h2' : e2 ∈ E ∪ {s : Set V3 | ∃ v ∈ V, s = ({v} : Set V3)} := by
          rcases he2 with hE2 | hS2
          · rcases hE2 with hh | hh
            · exact Set.mem_union_left _ hh
            · exact absurd hh h2
          · exact Set.mem_union_right _ hS2
        exact h7 e1 h1' e2 h2'


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
    2 < fv.ncard := by
  -- (0) 旧扇 FAN / 增广 FAN / 旧 hypermap
  have hkeep := h
  obtain ⟨HS2, hd2, he2, hn2, hf2, hFAN, hfacegen, hdih⟩ := hkeep
  have hHS2 : IsHyp_p2 0 V E HS2 := ⟨hd2, he2, hn2, hf2⟩
  have hFANaug : FAN 0 V (E ∪ {{v, w}}) := PROVE_SLICING_FAN h hv hw hvw hcol hsub
  -- (1) rho v ≠ w（CROSS_PAIR_NOT_IN_FF）
  have hdFF : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  have hrv_ne_w : rhoNode1_p2 FF v ≠ w := by
    intro hrvw
    exact CROSS_PAIR_NOT_IN_FF h hv hw hvw hsub (hrvw ▸ hdFF)
  have hrv_ne_v : rhoNode1_p2 FF v ≠ v := (LOCAL_FAN_CHARACTER_OF_RHO_NODE h hv).1
  -- (2) 增广 faceMap 在 (v, rho v) 上的值
  have hd1darts : (v, rhoNode1_p2 FF v) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V := by
    have ho := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdFF
    refine Set.mem_union_left _ ?_
    simp only [ordPairs_p2, Set.mem_setOf_eq] at ho ⊢
    exact Set.mem_union_left _ ho
  have hface1 : HS.faceMap (v, rhoNode1_p2 FF v) =
      (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) := by
    have heq := FACE_MAP_ADD_SET2_EQ HS HS2 v w v (rhoNode1_p2 FF v) hd1darts
      hrv_ne_v hrv_ne_w hFAN hFANaug hHS hHS2
    rw [heq]
    exact LOCAL_FACE_MAP_RHO_NODE1 h HS2 hHS2 hdFF
  -- (3) 三个 dart 在 fv 中
  have hd1mem : (v, rhoNode1_p2 FF v) ∈ fv := by
    rw [hfv]
    exact ⟨0, rfl⟩
  have hd2mem : (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ∈ fv := by
    have h1 : (HS.faceMap ^ 1) (v, rhoNode1_p2 FF v) ∈ HS.face (v, rhoNode1_p2 FF v) :=
      pow_apply_mem_orbitMap HS.faceMap 1 _
    rw [pow_one] at h1
    rw [← hfv, hface1] at h1
    exact h1
  have hd3mem : HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ∈ fv := by
    have h1 : (HS.faceMap ^ 2) (v, rhoNode1_p2 FF v) ∈ HS.face (v, rhoNode1_p2 FF v) :=
      pow_apply_mem_orbitMap HS.faceMap 2 _
    have h2 : (HS.faceMap ^ 2) (v, rhoNode1_p2 FF v) =
        HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) := by
      rw [pow_two, Equiv.Perm.mul_apply, hface1]
    rw [← hfv, h2] at h1
    exact h1
  -- (4) 两两相异
  have hne12 : (v, rhoNode1_p2 FF v) ≠
      (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) := by
    intro hc
    exact hrv_ne_v (congrArg Prod.fst hc).symm
  have hrhoV : rhoNode1_p2 FF v ∈ V := LOFA_IN_V_SO_DO_RHO_NODE_V h hv
  have hd2darts : (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ∈
      dartsOfHyp_p2 (E ∪ {{v, w}}) V := by
    have hd2FF : (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ∈ FF :=
      (LOCAL_FAN_RHO_NODE_PROS2 h).2 (rhoNode1_p2 FF v) hrhoV
    have ho := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hd2FF
    refine Set.mem_union_left _ ?_
    simp only [ordPairs_p2, Set.mem_setOf_eq] at ho ⊢
    exact Set.mem_union_left _ ho
  have hface2first :
      (HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v))).1
        = rhoNode1_p2 FF (rhoNode1_p2 FF v) := by
    rw [hHS.2.2.2]
    simp only [ffOfHyp_p2, if_pos hd2darts]
  have hne23 : (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ≠
      HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) := by
    intro hc
    have hc1 := congrArg Prod.fst hc
    rw [hface2first] at hc1
    exact (LOCAL_FAN_CHARACTER_OF_RHO_NODE h hrhoV).1 hc1.symm
  have hvv_ne : v ≠ rhoNode1_p2 FF (rhoNode1_p2 FF v) := by
    intro hcontra
    have hper : ∀ n : ℕ, (rhoNode1_p2 FF)^[n] v = v ∨
        (rhoNode1_p2 FF)^[n] v = rhoNode1_p2 FF v := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with hk | hk
        · rw [hk]; exact Or.inr rfl
        · rw [hk, ← hcontra]; exact Or.inl rfl
    have hVsub : V ⊆ ({v, rhoNode1_p2 FF v} : Set V3) := by
      intro z hz
      have hz' : z ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
        rw [LOCAL_FAN_ORBIT_MAP_V h hv]
        exact hz
      obtain ⟨n, hn⟩ := hz'
      rw [← hn]
      rcases hper n with hk | hk
      · rw [hk]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · rw [hk]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    rcases Set.mem_insert_iff.mp (hVsub hw) with hk | hk
    · exact hvw hk.symm
    · exact hrv_ne_w (Set.mem_singleton_iff.mp hk).symm
  have hne13 : (v, rhoNode1_p2 FF v) ≠
      HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) := by
    intro hc
    have hc1 := congrArg Prod.fst hc
    rw [hface2first] at hc1
    exact hvv_ne hc1
  -- (5) 三元子集 ⟹ 3 ≤ ncard
  have h1n : (v, rhoNode1_p2 FF v) ∉
      ({(rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)),
        HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v))} :
        Set (V3 × V3)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne12, hne13⟩
  have h2n : (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)) ∉
      ({HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v))} :
        Set (V3 × V3)) := by
    simpa using hne23
  have h3 : ({(v, rhoNode1_p2 FF v),
      (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)),
      HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v))} :
        Set (V3 × V3)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem h1n, Set.ncard_insert_of_notMem h2n,
      Set.ncard_singleton]
  have hsub3 : ({(v, rhoNode1_p2 FF v),
      (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v)),
      HS.faceMap (rhoNode1_p2 FF v, rhoNode1_p2 FF (rhoNode1_p2 FF v))} :
        Set (V3 × V3)) ⊆ fv := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hd1mem
    · exact hd2mem
    · exact hd3mem
  have hfin : fv.Finite := by
    have hx : (v, rhoNode1_p2 FF v) ∈ HS.darts :=
      Finset.mem_coe.mp (by rw [hHS.1]; exact hd1darts)
    have hsubD := Hypermap.face_subset_darts HS hx
    rw [← hfv] at hsubD
    exact (Finset.finite_toSet HS.darts).subset hsubD
  have hle := Set.ncard_le_ncard hsub3 hfin
  rw [h3] at hle
  omega


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
    HS.faceMap (x, v) = (v, w) := by
  -- Slice fan and the carrier face map.
  have hkeep := h
  have hFAN0 : FAN 0 V E := by
    obtain ⟨-, -, -, -, -, hf, -, -⟩ := hkeep
    exact hf
  have hFAN' : FAN 0 V (E ∪ {{v, w}}) :=
    PROVE_SLICING_FAN h hv hw hvw hcol hsub
  have hface : (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p2 0 V (E ∪ {{v, w}}) :=
    hHS.2.2.2
  rw [hface]
  -- The dart `(x,v)` is a carrier dart of the slice fan.
  have hxvE : ({x, v} : Set V3) ∈ E := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hxv
  have hd : (x, v) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V :=
    IN_DARTS_EXTENSION (x := x) (y := v)
      (E := E) (S := ({{v, w}} : Set (Set V3))) hxvE
  unfold ffOfHyp_p2
  rw [if_pos hd]
  simp only [Prod.mk.injEq, true_and]
  rw [show ivsAzimCycle_p2 (EE_p2 v (E ∪ {{v, w}})) 0 v x
      = ivsAzimCycle_p3 (EE_p3 v (E ∪ {{v, w}})) 0 v x from rfl]
  -- The rho-predecessor of `v` is `x`; the augmented neighbours of `v`.
  obtain ⟨hxV, -, -, -⟩ := LOCAL_FAN_IMP_IN_V h hxv hxv
  have hxr : rhoNode1_p2 FF x = v := DETER_RHO_NODE h hxv
  have hEEold : EE_p2 v E = ({rhoNode1_p2 FF v, x} : Set V3) :=
    LOFA_IMP_EE_TWO_ELMS (vv := x) (v := v) h hxV hxr
  have hsingle : EE_p2 v ({{v, w}} : Set (Set V3)) = ({w} : Set V3) :=
    EE_SING_SING v w
  have hEEnew : EE_p2 v (E ∪ {{v, w}}) = ({x, rhoNode1_p2 FF v, w} : Set V3) := by
    rw [EE_UNION v E ({{v, w}} : Set (Set V3)), hEEold, hsingle]
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  -- The slice wedge at the dart `(v, rho v)` is `wedge 0 v (rho v) x`.
  have hcardv : 1 < (EE_p2 v E).ncard := by
    rw [LOFA_CARD_EE_V_1 h hv]
    norm_num
  have hwedge_det : wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E
      = wedge 0 v (rhoNode1_p2 FF v) x := by
    rw [wedgeInFanGt_p2, if_pos hcardv, hEEold, AZIM_CYCLE_TWO_POINT_SET]
  -- The midpoint of the slice segment is a strict point of that wedge.
  have hv0 : (0 : V3) ≠ v := (FAN_IMP_V_DIFF hFAN0 v hv).symm
  have hw0 : (0 : V3) ≠ w := (FAN_IMP_V_DIFF hFAN0 w hw).symm
  have hmid1 : (1/2 : ℝ) • v + (1/2 : ℝ) • w ∈ affGt ({0} : Set V3) {v, w} :=
    sliceW4_affGtPairOfSums hv0 hw0 (Ne.symm hvw)
      (s := (1/2 : ℝ)) (t := (1/2 : ℝ)) (by norm_num) (by norm_num) _ rfl
  have hrv_dart : (v, rhoNode1_p2 FF v) ∈ FF :=
    (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  have hwedge_mem : (1/2 : ℝ) • v + (1/2 : ℝ) • w
      ∈ wedge 0 v (rhoNode1_p2 FF v) x := by
    have hh := hsub (v, rhoNode1_p2 FF v) hrv_dart
    rw [hwedge_det] at hh
    exact hh hmid1
  -- The angle at the midpoint equals the angle at `w`.
  have hnc_rho : ¬ Collinear3 0 v (rhoNode1_p2 FF v) := by
    simpa only [Collinear3] using LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hv
  have hnc_w : ¬ Collinear3 0 v w := by
    have hraw : ¬ Collinear ℝ ({0, v, w} : Set V3) :=
      hcol v w (by simp) (by simp [hw, Ne.symm hvw])
    simpa only [Collinear3] using hraw
  have hmid2 : (1/2 : ℝ) • v + (1/2 : ℝ) • w ∈ affGt ({0, v} : Set V3) {w} := by
    rw [COLL_AFF_GT_2_1 0 v w hnc_w]
    exact ⟨0, 1/2, 1/2, by norm_num, by norm_num, by module⟩
  have hnc_vw : ¬ Collinear3 0 v ((1/2 : ℝ) • v + (1/2 : ℝ) • w) := hwedge_mem.1
  have hazEq : azim 0 v (rhoNode1_p2 FF v) ((1/2 : ℝ) • v + (1/2 : ℝ) • w)
      = azim 0 v (rhoNode1_p2 FF v) w :=
    (azim_eq_azim_iff_alt (v0 := 0) (v1 := v) (w := rhoNode1_p2 FF v)
      (x := (1/2 : ℝ) • v + (1/2 : ℝ) • w) (y := w)
      hnc_rho hnc_vw hnc_w).mpr hmid2
  -- The analytic core: `x` follows `w` no later than `rho v` does.
  have haz_lt : azim 0 v (rhoNode1_p2 FF v) ((1/2 : ℝ) • v + (1/2 : ℝ) • w)
      < azim 0 v (rhoNode1_p2 FF v) x := hwedge_mem.2.2
  have hazw_lt_hazx : azim 0 v (rhoNode1_p2 FF v) w
      < azim 0 v (rhoNode1_p2 FF v) x := by
    rw [← hazEq]
    exact haz_lt
  have hnc_x : ¬ Collinear3 0 v x := by
    have hEx : ({v, x} : Set V3) ∈ E := by
      rw [Set.pair_comm v x]
      exact hxvE
    exact fan_not_collinear hFAN0 hEx
  have hsum4 : azim 0 v (rhoNode1_p2 FF v) x
      = azim 0 v (rhoNode1_p2 FF v) w + azim 0 v w x :=
    sum4_azim_fan (x := 0) (v := v) (u := rhoNode1_p2 FF v) (w1 := w) (w2 := x)
      (FAN_IMP_V_DIFF hFAN0 v hv) hnc_rho hnc_w hnc_x (le_of_lt hazw_lt_hazx)
  have hazw_pos : 0 < azim 0 v (rhoNode1_p2 FF v) w := by
    rw [← hazEq]
    exact hwedge_mem.2.1
  have h2pi : azim 0 v (rhoNode1_p2 FF v) w + azim 0 v w (rhoNode1_p2 FF v)
      = 2 * Real.pi := AZIM_POS_IMP_SUM_2PI hazw_pos
  have haz_ineq : azim 0 v w x ≤ azim 0 v w (rhoNode1_p2 FF v) := by
    have hb := (AZIM_RANGE 0 v (rhoNode1_p2 FF v) x).2
    linarith
  -- Neighbourhood facts in the slice fan.
  have hx_mem : x ∈ setOfEdge v V (E ∪ {{v, w}}) := by
    rw [← FAN_IMP_EE_EQ_SET_OF_EDGE hFAN' v]
    change x ∈ EE_p2 v (E ∪ {{v, w}})
    rw [hEEnew]
    simp
  have hw_mem : w ∈ setOfEdge v V (E ∪ {{v, w}}) := by
    rw [← FAN_IMP_EE_EQ_SET_OF_EDGE hFAN' v]
    change w ∈ EE_p2 v (E ∪ {{v, w}})
    rw [hEEnew]
    simp
  have hx_ne_w : x ≠ w := by
    intro hxw
    have hsub' : ∀ d ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 d E := by
      intro d hd
      rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v]
      exact hsub d hd
    exact CROSS_PAIR_NOT_IN_FF (v := w) (w := v) h hw hv (Ne.symm hvw) hsub'
      (hxw ▸ hxv)
  have hne : setOfEdge v V (E ∪ {{v, w}}) ≠ {w} := by
    intro hsingle'
    have hxw : x = w := Set.mem_singleton_iff.mp (hsingle' ▸ hx_mem)
    exact hx_ne_w hxw
  have hmin : ∀ w1 : V3, w1 ∈ setOfEdge v V (E ∪ {{v, w}}) → w1 ≠ w →
      azim 0 v w x ≤ azim 0 v w w1 := by
    intro w1 hw1 hw1w
    have hw1EE : w1 ∈ ({x, rhoNode1_p2 FF v, w} : Set V3) := by
      rw [← FAN_IMP_EE_EQ_SET_OF_EDGE hFAN' v] at hw1
      change w1 ∈ EE_p2 v (E ∪ {{v, w}}) at hw1
      simpa only [hEEnew] using hw1
    rcases Set.mem_insert_iff.mp hw1EE with hwx | h2
    · rw [hwx]
    · rcases Set.mem_insert_iff.mp h2 with hwr | hww
      · rw [hwr]
        exact haz_ineq
      · exact absurd (Set.mem_singleton_iff.mp hww) hw1w
  -- `sigma_fan` of `w` at `v` in the slice fan is the predecessor `x`.
  have hsig : sigmaFan 0 V (E ∪ {{v, w}}) v w = x :=
    UNIQUE_SIGMA_FAN hne hFAN' hw_mem hx_mem hx_ne_w hmin
  -- Turn the `sigma_fan` back into the face map via `ivs_azim_cycle`.
  rw [IVS_AZIM_EQ_INVERSE_SIGMA_FAN (x := 0) (V := V) (E := E ∪ {{v, w}}) hFAN'
    (v := v) (u := x) (Or.inl (by rwa [Set.pair_comm v x]))]
  exact SIG_AND_INVERSE1_SIG (x := 0) (V := V) (E := E ∪ {{v, w}}) hFAN'
    (u := v) (w := w) (v := x) (Or.inr (by simp)) hsig

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
    HS.faceMap (v, w) = (w, rhoNode1_p2 FF w) := by
  -- Slice fan and the carrier face map.
  have hkeep := h
  have hFAN0 : FAN 0 V E := by
    obtain ⟨-, -, -, -, -, hf, -, -⟩ := hkeep
    exact hf
  have hFAN' : FAN 0 V (E ∪ {{v, w}}) :=
    PROVE_SLICING_FAN h hv hw hvw hcol hsub
  have hface : (HS.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p2 0 V (E ∪ {{v, w}}) :=
    hHS.2.2.2
  rw [hface]
  -- The diagonal dart `(v, w)` is a carrier dart; read `ff_of_hyp`.
  have hd : (v, w) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V := by
    rw [Set.union_comm]
    exact IN_DARTS_EXTENSION (x := v) (y := w)
      (E := ({{v, w}} : Set (Set V3))) (S := E) (by simp)
  unfold ffOfHyp_p2
  rw [if_pos hd]
  simp only [Prod.mk.injEq, true_and]
  -- Work in the `_p3` rendering of `ivs_azim_cycle`.
  rw [show ivsAzimCycle_p2 (EE_p2 w (E ∪ {{v, w}})) 0 w v
      = ivsAzimCycle_p3 (EE_p3 w (E ∪ {{v, w}})) 0 w v from rfl]
  have hwv_mem : ({w, v} : Set V3) ∈ E ∪ {{v, w}} := by
    refine Or.inr ?_
    rw [Set.mem_singleton_iff]
    exact (Set.pair_comm v w).symm
  -- The fan predecessor `x` of `w` along `rho`.
  obtain ⟨x, hxV, hxw⟩ : ∃ x : V3, x ∈ V ∧ rhoNode1_p2 FF x = w := by
    have hwimg : w ∈ Set.image (rhoNode1_p2 FF) V := by
      rw [LOFA_IMAGE_RHO_NODE_IDE h]
      exact hw
    simpa only [Set.mem_image] using hwimg
  have hrho_ne_x : rhoNode1_p2 FF w ≠ x := by
    have hh := LOCAL_FAN_IMP_NOT_SEMI_IDE h hxV
    rwa [hxw] at hh
  -- The augmented neighbour set at `w` is `{v, x, rho w}`.
  have hEEold : EE_p2 w E = ({rhoNode1_p2 FF w, x} : Set V3) :=
    LOFA_IMP_EE_TWO_ELMS (vv := x) (v := w) h hxV hxw
  have hsingle : EE_p2 w ({{v, w}} : Set (Set V3)) = ({v} : Set V3) := by
    have hh := EE_SING_SING (v := w) (w := v)
    simpa only [Set.pair_comm v w] using hh
  have hEEnew : EE_p2 w (E ∪ {{v, w}}) = ({v, x, rhoNode1_p2 FF w} : Set V3) := by
    rw [EE_UNION w E ({{v, w}} : Set (Set V3)), hEEold, hsingle]
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hEEp3eq : EE_p3 w (E ∪ {{v, w}}) = ({v, x, rhoNode1_p2 FF w} : Set V3) := by
    change EE_p2 w (E ∪ {{v, w}}) = _
    exact hEEnew
  -- The face dart at `w` and the strict point of the slice.
  have hrho_dart : (w, rhoNode1_p2 FF w) ∈ FF :=
    (LOCAL_FAN_RHO_NODE_PROS2 h).2 w hw
  have hrho_mem : rhoNode1_p2 FF w ∈ EE_p2 w (E ∪ {{v, w}}) := by
    rw [hEEnew]
    simp
  have hv0 : (0 : V3) ≠ v := (FAN_IMP_V_DIFF hFAN0 v hv).symm
  have hw0 : (0 : V3) ≠ w := (FAN_IMP_V_DIFF hFAN0 w hw).symm
  have hmid1 : (1/2 : ℝ) • v + (1/2 : ℝ) • w ∈ affGt ({0} : Set V3) {v, w} :=
    sliceW4_affGtPairOfSums hv0 hw0 (Ne.symm hvw)
      (s := (1/2 : ℝ)) (t := (1/2 : ℝ)) (by norm_num) (by norm_num) _ rfl
  have hnc_v : ¬ Collinear3 0 w v := by
    have hraw : ¬ Collinear ℝ ({0, v, w} : Set V3) :=
      hcol v w (by simp) (by simp [hw, Ne.symm hvw])
    simpa only [Collinear3, Set.insert_comm, Set.pair_comm] using hraw
  have hmid2 : (1/2 : ℝ) • v + (1/2 : ℝ) • w ∈ affGt ({0, w} : Set V3) {v} := by
    rw [COLL_AFF_GT_2_1 0 w v hnc_v]
    exact ⟨0, 1/2, 1/2, by norm_num, by norm_num, by module⟩
  have hwedge_eq : wedgeInFanGt_p2 (w, rhoNode1_p2 FF w) E
      = wedge 0 w (rhoNode1_p2 FF w) x :=
    WEDGE_IN_FAN_LOFA_DETER (v := x) (w := w) h hxV hxw
  have hwedge_mem : (1/2 : ℝ) • v + (1/2 : ℝ) • w
      ∈ wedge 0 w (rhoNode1_p2 FF w) x := by
    have hh := hsub (w, rhoNode1_p2 FF w) hrho_dart
    rw [hwedge_eq] at hh
    exact hh hmid1
  have hnc_wedge : ¬ Collinear3 0 w ((1/2 : ℝ) • v + (1/2 : ℝ) • w) :=
    hwedge_mem.1
  have hazlt : azim 0 w (rhoNode1_p2 FF w) ((1/2 : ℝ) • v + (1/2 : ℝ) • w)
      < azim 0 w (rhoNode1_p2 FF w) x := hwedge_mem.2.2
  have hnc_rho : ¬ Collinear3 0 w (rhoNode1_p2 FF w) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hw
  have hazEq : azim 0 w (rhoNode1_p2 FF w) ((1/2 : ℝ) • v + (1/2 : ℝ) • w)
      = azim 0 w (rhoNode1_p2 FF w) v :=
    (azim_eq_azim_iff_alt (v0 := 0) (v1 := w) (w := rhoNode1_p2 FF w)
      (x := (1/2 : ℝ) • v + (1/2 : ℝ) • w) (y := v)
      hnc_rho hnc_wedge hnc_v).mpr hmid2
  -- `rho w` is a neighbour of `w` in the slice fan, hence a `sigma_fan` point.
  have hrho_set : rhoNode1_p2 FF w ∈ setOfEdge w V (E ∪ {{v, w}}) := by
    rw [← FAN_IMP_EE_EQ_SET_OF_EDGE hFAN' w]
    change rhoNode1_p2 FF w ∈ EE_p2 w (E ∪ {{v, w}})
    exact hrho_mem
  have hWnotSub : ¬ (EE_p3 w (E ∪ {{v, w}}) ⊆ ({rhoNode1_p2 FF w} : Set V3)) := by
    intro hsubW
    have hxmem : x ∈ EE_p3 w (E ∪ {{v, w}}) := by
      change x ∈ EE_p2 w (E ∪ {{v, w}})
      rw [hEEnew]
      simp
    have hxr : x = rhoNode1_p2 FF w := by simpa using hsubW hxmem
    exact hrho_ne_x hxr.symm
  have hWfin : (EE_p3 w (E ∪ {{v, w}})).Finite := FAN_IMP_FINITE_EE hFAN' w
  obtain ⟨hazne, hazmem, hazmin⟩ :=
    AZIM_CYCLE_PROPERTIES (W := EE_p3 w (E ∪ {{v, w}}))
      (p := rhoNode1_p2 FF w) hWnotSub hWfin 0 w
  rw [hEEp3eq] at hazne hazmem hazmin
  have hv_mem_W : v ∈ ({v, x, rhoNode1_p2 FF w} : Set V3) := by
    rw [← hEEnew]
    change ({w, v} : Set V3) ∈ E ∪ {{v, w}}
    exact Or.inr (by rw [Set.mem_singleton_iff]; exact (Set.pair_comm v w).symm)
  have hsub' : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
    intro x hx
    rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v]
    exact hsub x hx
  have hv_ne_rho : v ≠ rhoNode1_p2 FF w := by
    intro hveq
    have hmem : (w, v) ∈ FF := by rw [hveq]; exact hrho_dart
    exact CROSS_PAIR_NOT_IN_FF (v := w) (w := v) h hw hv (Ne.symm hvw) hsub' hmem
  have hmin := hazmin v hv_mem_W hv_ne_rho
  -- The cyclic successor of `rho w` is `v` (it cannot be `x`, by the wedge).
  have haz_eq_v_lit : azimCycle_p3 ({v, x, rhoNode1_p2 FF w} : Set V3) 0 w
      (rhoNode1_p2 FF w) = v := by
    rcases Set.mem_insert_iff.mp hazmem with hzv | h2
    · exact hzv
    rcases Set.mem_insert_iff.mp h2 with hzx | hzr
    · exfalso
      rcases hmin with hlt' | ⟨heq, _⟩
      · rw [hzx] at hlt'
        rw [← hazEq] at hlt'
        linarith
      · rw [hzx] at heq
        rw [← hazEq] at heq
        linarith
    · exact absurd hzr hazne
  have haz_eq_v : azimCycle_p3 (EE_p3 w (E ∪ {{v, w}})) 0 w (rhoNode1_p2 FF w) = v := by
    rw [hEEp3eq]
    exact haz_eq_v_lit
  have hsig_cyc : sigmaFan 0 V (E ∪ {{v, w}}) w (rhoNode1_p2 FF w)
      = azimCycle_p3 (EE_p3 w (E ∪ {{v, w}})) 0 w (rhoNode1_p2 FF w) :=
    (AZIM_CYCLE_EQ_SIGMA_FAN (x := 0) (V := V) (E := E ∪ {{v, w}}) hFAN'
      (v := w) (u := rhoNode1_p2 FF w) hrho_set).symm
  have hsig : sigmaFan 0 V (E ∪ {{v, w}}) w (rhoNode1_p2 FF w) = v := by
    rw [hsig_cyc, haz_eq_v]
  rw [IVS_AZIM_EQ_INVERSE_SIGMA_FAN (x := 0) (V := V) (E := E ∪ {{v, w}}) hFAN'
    (v := w) (u := v) hwv_mem]
  exact SIG_AND_INVERSE1_SIG (x := 0) (V := V) (E := E ∪ {{v, w}}) hFAN'
    (u := w) (w := rhoNode1_p2 FF w) (v := v)
    (Or.inl (LOCAL_RHO_NODE_PAIR_E h hw)) hsig

/-- HOL `FACE_MAP_AT_TURNING_DART1` (local_lemmas1.hl:2641) — giant. -/
theorem FACE_MAP_AT_TURNING_DART1 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hxw : (x, w) ∈ FF) :
    HS.faceMap (x, w) = (w, v) := by
  have hcol' : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz ht
    exact hcol z t (by rwa [Set.pair_comm w v] at hz) ht
  have hsub' : ∀ d ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 d E := by
    intro d hd
    rw [show ({w, v} : Set V3) = {v, w} from Set.pair_comm w v]
    exact hsub d hd
  have hpair : (E ∪ {{v, w}} : Set (Set V3)) = E ∪ {{w, v}} := by
    rw [Set.pair_comm v w]
  exact FACE_MAP_AT_TURNING_DART (v := w) (w := v) h hw hv (Ne.symm hvw)
    hcol' hsub' HS (hpair ▸ hHS) hxw

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
        p = ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v)} := by
  have hkeep := h
  -- the `E`-hypermap of the local fan
  obtain ⟨H, hHdarts, hHedge, hHnode, hHface, hFAN0, hHmem, hHdih⟩ := h
  have hH : IsHyp_p2 0 V E H := ⟨hHdarts, hHedge, hHnode, hHface⟩
  have hFANsl : FAN 0 V (E ∪ {{v, w}}) :=
    PROVE_SLICING_FAN hkeep hv hw hvw hcol hsub
  -- `w` occurs in the rho-orbit of `v`; take the least such index `n₀`
  have hwOrb : w ∈ orbitF_p2 (rhoNode1_p2 FF) v := by
    rw [LOCAL_FAN_ORBIT_MAP_V hkeep hv]
    exact hw
  obtain ⟨m₀, hm₀⟩ := hwOrb
  have hex : ∃ n : ℕ, (rhoNode1_p2 FF)^[n] v = w := ⟨m₀, hm₀⟩
  set n₀ := Nat.find hex with hn₀def
  have hn₀ : (rhoNode1_p2 FF)^[n₀] v = w := by
    rw [hn₀def]
    exact Nat.find_spec hex
  have hn₀min : ∀ m, (rhoNode1_p2 FF)^[m] v = w → n₀ ≤ m := by
    intro m hm
    rw [hn₀def]
    exact Nat.find_min' hex hm
  have hmin : ∀ m < n₀, (rhoNode1_p2 FF)^[m] v ≠ w := by
    intro m hm heq
    have hle := hn₀min m heq
    omega
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · exfalso
      rw [h0] at hn₀
      simp only [Function.iterate_zero_apply] at hn₀
      exact hvw hn₀
    · exact hpos
  have hn₀card : n₀ < V.ncard := by
    have henum := LOOP_SET_DETER_FIRTS_ELMS (f := rhoNode1_p2 FF) (V := V)
      (fun u hu => LOCAL_FAN_ORBIT_MAP_V hkeep hu) v hv
    have hwmem : w ∈ ({x : V3 | ∃ n < V.ncard, (rhoNode1_p2 FF)^[n] v = x} : Set V3) := by
      rw [henum]
      exact hw
    obtain ⟨m, hmcard, hmw⟩ := hwmem
    have hle := hn₀min m hmw
    omega
  -- one rho-step is one face-map step, as long as the target is not `v` or `w`
  have hstep : ∀ j : ℕ, j + 1 < n₀ →
      HS.faceMap ((rhoNode1_p2 FF)^[j] v, (rhoNode1_p2 FF)^[j + 1] v)
        = ((rhoNode1_p2 FF)^[j + 1] v, (rhoNode1_p2 FF)^[j + 2] v) := by
    intro j hj
    set x := (rhoNode1_p2 FF)^[j] v with hxdef
    set y := (rhoNode1_p2 FF)^[j + 1] v with hydef
    have hxV : x ∈ V := by
      rw [hxdef]
      exact LOCAL_FAN_ITER_RHO_NODE_IN_V hkeep hv j
    have hdFF : (x, y) ∈ FF := by
      have hd := LOCAL_FAN_ORBIT_MAP_VITERFF hkeep hv j
      simpa only [hxdef, hydef] using hd
    have hxyE : ({x, y} : Set V3) ∈ E := by
      have hpair := LOCAL_RHO_NODE_PAIR_E hkeep hxV
      have hrho : rhoNode1_p2 FF x = y := by
        rw [hxdef, hydef]
        exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) j v).symm
      rwa [hrho] at hpair
    have hd : (x, y) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V :=
      IN_DARTS_EXTENSION (x := x) (y := y) (E := E) (S := ({{v, w}} : Set (Set V3))) hxyE
    have hyv : y ≠ v := by
      rw [hydef]
      have hdis := LOFA_IMP_DIS_ELMS23 hkeep hv 0 (j + 1) (by omega) (by omega)
      simpa using hdis
    have hyw : y ≠ w := by
      rw [hydef]
      exact hmin (j + 1) (by omega)
    have hP1 : HS.faceMap (x, y) = H.faceMap (x, y) :=
      FACE_MAP_ADD_SET2_EQ HS H v w x y hd hyv hyw hFAN0 hFANsl hHS hH
    have hP2 : H.faceMap (x, y) = (rhoNode1_p2 FF x, rhoNode1_p2 FF y) :=
      LOCAL_FACE_MAP_RHO_NODE1 hkeep H hH hdFF
    rw [hP1, hP2]
    have hxy : rhoNode1_p2 FF x = y := DETER_RHO_NODE hkeep hdFF
    have hyz : rhoNode1_p2 FF y = (rhoNode1_p2 FF)^[j + 2] v := by
      rw [hydef]
      exact (Function.iterate_succ_apply' (rhoNode1_p2 FF) (j + 1) v).symm
    rw [hxy, hyz]
  -- face-map iterates follow the rho iterates up to `n₀`
  have hiter : ∀ j : ℕ, j < n₀ →
      (HS.faceMap ^ j) (v, rhoNode1_p2 FF v)
        = ((rhoNode1_p2 FF)^[j] v, (rhoNode1_p2 FF)^[j + 1] v) := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ j ih =>
        intro hj
        have hj' : j < n₀ := by omega
        rw [pow_succ', Equiv.Perm.mul_apply, ih hj']
        exact hstep j (by omega)
  -- the `n₀`-th face-map iterate is the turning dart `(w, v)`
  have hn1 : n₀ - 1 + 1 = n₀ := Nat.sub_add_cancel (by omega : 1 ≤ n₀)
  have hclosing : (HS.faceMap ^ n₀) (v, rhoNode1_p2 FF v) = (w, v) := by
    have hprev := hiter (n₀ - 1) (by omega)
    have hdFF : ((rhoNode1_p2 FF)^[n₀ - 1] v, w) ∈ FF := by
      have hd := LOCAL_FAN_ORBIT_MAP_VITERFF hkeep hv (n₀ - 1)
      rwa [hn1, hn₀] at hd
    have hsucc : HS.faceMap ^ n₀ = HS.faceMap * HS.faceMap ^ (n₀ - 1) := by
      conv_lhs => rw [← hn1]
      rw [pow_succ']
    rw [hsucc, Equiv.Perm.mul_apply, hprev, hn1, hn₀]
    exact FACE_MAP_AT_TURNING_DART1 hkeep hv hw hvw hcol hsub HS hHS hdFF
  -- and the next step returns to the start
  have hclose2 : (HS.faceMap ^ (n₀ + 1)) (v, rhoNode1_p2 FF v)
      = (v, rhoNode1_p2 FF v) := by
    have hswap := FACE_MAP_SLICING_HYP_TRANS_POINT (v := w) (w := v) hkeep hw hv
      (Ne.symm hvw)
      (by
        intro z t hz ht
        exact hcol z t (by rwa [Set.pair_comm w v] at hz) ht)
      (by
        intro d hd
        rw [Set.pair_comm w v]
        exact hsub d hd)
      HS (by simpa only [Set.pair_comm w v] using hHS)
    rw [pow_succ', Equiv.Perm.mul_apply, hclosing]
    exact hswap
  -- the face orbit is cyclic with period `n₀ + 1`
  have hcyc := orbit_cyclic HS.faceMap (x := (v, rhoNode1_p2 FF v)) (m := n₀ + 1)
    (by omega) hclose2
  have hrange : (↑(Finset.range (n₀ + 1)) : Set ℕ) = {k : ℕ | k < n₀ + 1} := by
    ext k
    exact Finset.mem_range
  rw [hrange] at hcyc
  rw [hfv]
  change orbitMap HS.faceMap (v, rhoNode1_p2 FF v)
      = insert (w, v) {p | ∃ n : ℕ,
        (∀ m : ℕ, m < n + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
          p = ((rhoNode1_p2 FF)^[n] v, (rhoNode1_p2 FF)^[n + 1] v)}
  rw [hcyc]
  ext p
  constructor
  · rintro ⟨k, hk, hkp⟩
    have hk' : k < n₀ + 1 := hk
    rcases Nat.lt_or_eq_of_le (by omega : k ≤ n₀) with hklt | hkeq
    · right
      refine ⟨k, ?_, ?_⟩
      · intro m hm
        exact hmin m (by omega)
      · rw [← hkp]
        exact hiter k hklt
    · left
      rw [← hkp, hkeq]
      exact hclosing
  · intro hp
    rcases hp with hpw | ⟨n, hcond, hpn⟩
    · refine ⟨n₀, ?_, ?_⟩
      · simp
      · rw [hpw]
        exact hclosing
    · have hnlt : n < n₀ := by
        by_contra hcon
        have hlt : n₀ < n + 1 := by omega
        exact hcond n₀ hlt hn₀
      refine ⟨n, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        omega
      · rw [hpn]
        exact hiter n hnlt

/-- HOL `CARD_IS_LEAST_CYCLE` (local_lemmas1.hl:3056) — giant. -/
theorem CARD_IS_LEAST_CYCLE (h : localFan_p2 V E FF) (hv : v ∈ V) (n : ℕ)
    (hn : (rhoNode1_p2 FF)^[n] v = v) (hnz : n ≠ 0) : V.ncard ≤ n := by
  by_contra hc
  have hlt : n < V.ncard := by omega
  have hp : 0 < n := by omega
  have hne := LOFA_IMP_DIS_ELMS23 h hv 0 n hp hlt
  exact hne (by rw [hn]; rfl)

/-- **HAFL assembly with the `dih2k` residual explicit.**

Hypotheses are the frozen LA6 statement's, plus
`hdihFor`: the localized-carrier `dih2k` transfer (`DIH_K_HYP_E_PRIME`
specialized to the slice carriers, uniform in the carrier `HS'`).

Proof route (HOL local_lemmas1.hl:3077):
1. `PROVE_SLICING_FAN` → `FAN 0 V (E ∪ {{v,w}})` (LA6, closed);
2. the base dart `d = (v, rhoNode1 FF v)` is a carrier dart;
3. `IMP_FAN_V_PRIME_E_PRIME` (LA3, closed) → `FAN 0 (vPrime V fv) (ePrime E' fv)`;
4. `HYP_LEMMA` (LA3, closed) → the slice carrier hypermap `HS'`;
5. `LOCALIZE_PRESERVE_FACE` (LA10, closed) → `fv = HS'.face d`;
6. the slice base-dart membership;
7. `localFan_p2` fields. -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN_of_dih {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v w : V3} {fv : Set (V3 × V3)}
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hdihFor : ∀ HS' : Hypermap (V3 × V3),
      IsHyp_p2 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) HS' →
      dih2k_p2 HS' fv.ncard) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv := by
  -- (1) the augmented carrier still carries a fan
  have hfanAug : FAN 0 V (E ∪ {{v, w}}) :=
    PROVE_SLICING_FAN h hv hw hvw hcol hsub
  -- (2) the base dart `(v, rho v)` is a carrier dart
  have hdFF : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  have hdOrd : (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E :=
    LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdFF
  have hdOrd' : (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 (E ∪ {{v, w}}) :=
    Or.inl hdOrd
  have hd : (v, rhoNode1_p2 FF v) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V :=
    Or.inl hdOrd'
  have hdD : (v, rhoNode1_p2 FF v) ∈ (↑HS.darts : Set (V3 × V3)) := by
    rw [hHS.1]; exact hd
  -- (3) + (4): the slice fan and its HYP carrier
  have hH : ∃ H : Hypermap (V3 × V3),
      (↑H.darts : Set (V3 × V3)) = dartsOfHyp_p3 (E ∪ {{v, w}}) V ∧
      (H.edgeMap : V3 × V3 → V3 × V3) = eeOfHyp_p3 0 V (E ∪ {{v, w}}) ∧
      (H.nodeMap : V3 × V3 → V3 × V3) = nnOfHyp_p3 0 V (E ∪ {{v, w}}) ∧
      (H.faceMap : V3 × V3 → V3 × V3) = ffOfHyp_p3 0 V (E ∪ {{v, w}}) ∧
      ∃ x ∈ H.darts, fv = H.face x :=
    ⟨HS, hHS.1, hHS.2.1, hHS.2.2.1, hHS.2.2.2,
      (v, rhoNode1_p2 FF v), Finset.mem_coe.mp hdD, hfv⟩
  have hfanSl : FAN 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) :=
    IMP_FAN_V_PRIME_E_PRIME hfanAug hH
  obtain ⟨HS', hHS'⟩ := HYP_LEMMA hfanSl
  -- (5) localization preserves the face
  have hface : fv = HS'.face (v, rhoNode1_p2 FF v) :=
    LOCALIZE_PRESERVE_FACE (v := 0) hfanAug hHS hHS' hd hfv
  -- (6) the slice base-dart membership
  have hdfv : (v, rhoNode1_p2 FF v) ∈ fv := by
    rw [hfv]; exact HS.mem_face_self _
  have hpair : ({v, rhoNode1_p2 FF v} : Set V3) ∈ ePrime_p2 (E ∪ {{v, w}}) fv :=
    ⟨v, rhoNode1_p2 FF v, rfl, Or.inl hdOrd, hdfv⟩
  have hd' : (v, rhoNode1_p2 FF v) ∈
      dartsOfHyp_p2 (ePrime_p2 (E ∪ {{v, w}}) fv) (vPrime_p2 V fv) :=
    Or.inl hpair
  have hdD' : (v, rhoNode1_p2 FF v) ∈ (↑HS'.darts : Set (V3 × V3)) := by
    rw [hHS'.1]; exact hd'
  -- (7) assemble `localFan_p2`
  exact ⟨HS', hHS'.1, hHS'.2.1, hHS'.2.2.1, hHS'.2.2.2, hfanSl,
    ⟨(v, rhoNode1_p2 FF v), Finset.mem_coe.mp hdD', hface⟩,
    hdihFor HS' hHS'⟩


/-! ## Private helpers for the slice-`Simple` residual (R1) -/

/-- `nn_of_hyp` preserves the first coordinate. -/
private theorem w2_nn_fst {x : V3} {V : Set V3} {E : Set (Set V3)} (d : V3 × V3) :
    (nnOfHyp_p2 x V E d).1 = d.1 := by
  simp only [nnOfHyp_p2]
  split <;> rfl

/-- `azim_cycle` on a singleton is the identity. -/
private theorem w2_azim_single (p v0 u : V3) : azimCycle_p2 ({p} : Set V3) v0 u p = p := by
  rw [azimCycle_p2, if_pos (c := (({p} : Set V3) ⊆ {p})) (Set.Subset.refl _)]

/-- `ivs_azim_cycle` on a two-point set returns the other point. -/
private theorem w2_ivs_pair (a b v0 u : V3) :
    ivsAzimCycle_p2 ({a, b} : Set V3) v0 u a = b := by
  by_cases hab : a = b
  · subst hab
    rw [ivsAzimCycle_p2, if_neg (c := (({a, a} : Set V3) = ∅)) (by
      intro h
      have h2 : (a : V3) ∈ ({a, a} : Set V3) := by simp
      rw [h] at h2
      exact absurd h2 (by simp))]
    have hspec := Classical.epsilon_spec
      (p := fun z : V3 => z ∈ ({a, a} : Set V3) ∧ azimCycle_p2 ({a, a} : Set V3) v0 u z = a)
      ⟨a, by simp, by simpa using w2_azim_single a v0 u⟩
    simpa using hspec.1
  · rw [ivsAzimCycle_p2, if_neg (c := (({a, b} : Set V3) = ∅)) (by
      intro h
      have h2 : (a : V3) ∈ ({a, b} : Set V3) := by simp
      rw [h] at h2
      exact absurd h2 (by simp))]
    have haz_b : azimCycle_p2 ({a, b} : Set V3) v0 u b = a := by
      rw [Set.pair_comm]
      exact AZIM_CYCLE_TWO_POINT_SET b a v0 u
    obtain ⟨h1, h2⟩ := Classical.epsilon_spec
      (p := fun z : V3 => z ∈ ({a, b} : Set V3) ∧ azimCycle_p2 ({a, b} : Set V3) v0 u z = a)
      ⟨b, by simp, haz_b⟩
    rcases (Set.mem_insert_iff.mp h1) with h | h
    · exfalso
      rw [h, AZIM_CYCLE_TWO_POINT_SET a b v0 u] at h2
      exact hab h2.symm
    · exact Set.mem_singleton_iff.mp h

/-- successor / predecessor index on the cyclic window `0..n`. -/
private def w2nx (n m : ℕ) : ℕ := if m = n then 0 else m + 1

private def w2pv (n m : ℕ) : ℕ := if m = 0 then n else m - 1

private theorem w2nx_lt {n m : ℕ} (h : m < n) : w2nx n m = m + 1 := by
  simp only [w2nx]
  rw [if_neg (ne_of_lt h)]

private theorem w2nx_self (n : ℕ) : w2nx n n = 0 := by
  simp [w2nx]

private theorem w2pv_pos {n m : ℕ} (h : 0 < m) : w2pv n m = m - 1 := by
  simp only [w2pv]
  rw [if_neg (ne_of_gt h)]

private theorem w2pv_idx0 (n : ℕ) : w2pv n 0 = n := by
  simp [w2pv]

private theorem w2pv_succ (n k : ℕ) : w2pv n (k + 1) = k := by
  simp only [w2pv]
  rw [if_neg (by omega)]
  omega

private theorem w2nx_le {n m : ℕ} (hm : m ≤ n) : w2nx n m ≤ n := by
  by_cases h : m = n
  · rw [h, w2nx_self]; omega
  · rw [w2nx_lt (by omega)]; omega

private theorem w2pv_le {n m : ℕ} (hm : m ≤ n) : w2pv n m ≤ n := by
  by_cases h : m = 0
  · rw [h, w2pv_idx0]
  · rw [w2pv_pos (by omega)]; omega

private theorem w2pv_nx {n m : ℕ} (hm : m ≤ n) : w2pv n (w2nx n m) = m := by
  by_cases h : m = n
  · rw [h, w2nx_self, w2pv_idx0]
  · rw [w2nx_lt (by omega), w2pv_succ]

private theorem w2nx_pv {n m : ℕ} (hm : m ≤ n) : w2nx n (w2pv n m) = m := by
  by_cases h : m = 0
  · subst h
    rw [w2pv_idx0, w2nx_self]
  · rw [w2pv_pos (by omega)]
    by_cases h2 : m - 1 = n
    · omega
    · rw [w2nx_lt (by omega)]; omega

private theorem w2nx_zero {n k : ℕ} (hk : k ≤ n) : (w2nx n)^[k] 0 = k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have hj : j ≤ n := by omega
    rw [Function.iterate_succ_apply', ih hj]
    by_cases h : j = n
    · rw [h, w2nx_self]; omega
    · rw [w2nx_lt (by omega)]

private theorem w2nx_iter_le (n k : ℕ) : (w2nx n)^[k] 0 ≤ n := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact w2nx_le ih

/-! ## R1: the sliced HYP hypermap is `Simple` -/

theorem w2_slice_hyp_simple
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (HS' : Hypermap (V3 × V3))
    (hHS' : IsHyp_p2 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) HS') :
    HS'.Simple := by
  -- ## 0. the `rho`-orbit enumeration of `fv`
  obtain ⟨n, hn_card, hn_w⟩ : ∃ n, n < V.ncard ∧ (rhoNode1_p2 FF)^[n] v = w := by
    have henum := LOOP_SET_DETER_FIRTS_ELMS (f := rhoNode1_p2 FF) (V := V)
      (fun u hu => LOCAL_FAN_ORBIT_MAP_V h hu) v hv
    have hwmem : w ∈ ({x : V3 | ∃ n < V.ncard, (rhoNode1_p2 FF)^[n] v = x} : Set V3) := by
      rw [henum]; exact hw
    obtain ⟨m, hmc, hmw⟩ := hwmem
    exact ⟨m, hmc, hmw⟩
  -- the `m < n` enumeration (inlined `DETERMINE_FV2`, which is stated later in
  -- the file; only `DETERMINE_FV` is needed)
  have hfv_min := DETERMINE_FV h hv hw hvw hcol hsub HS hHS hfv
  have hset_eq : {p : V3 × V3 | ∃ n₀ : ℕ,
      (∀ m : ℕ, m < n₀ + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
        p = ((rhoNode1_p2 FF)^[n₀] v, (rhoNode1_p2 FF)^[n₀ + 1] v)}
      = {p : V3 × V3 | ∃ m : ℕ, m < n ∧
        p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
    ext p
    constructor
    · rintro ⟨n₀, hn₀c, hn₀p⟩
      have hn₀lt : n₀ < n := by
        by_contra hle
        exact hn₀c n (by omega) hn_w
      exact ⟨n₀, hn₀lt, hn₀p⟩
    · rintro ⟨m, hm, hmp⟩
      refine ⟨m, ?_, hmp⟩
      intro m' hm' hmeq
      exact LOFA_IMP_DIS_ELMS23 h hv m' n (by omega) hn_card (hn_w.trans hmeq.symm)
  have hfv2 : fv = insert (w, v)
      {p : V3 × V3 | ∃ m : ℕ, m < n ∧
        p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
    rw [hfv_min, hset_eq]
  set a : ℕ → V3 := fun m => (rhoNode1_p2 FF)^[m] v with ha
  have han : a n = w := hn_w
  have ha0 : a 0 = v := rfl
  have hfv2' : fv = insert (a n, a 0) {p : V3 × V3 | ∃ m, m < n ∧ p = (a m, a (m + 1))} := by
    rw [hfv2, ← han]
    rfl
  have hainj : ∀ m m', m ≤ n → m' ≤ n → a m = a m' → m = m' := by
    intro m m' hm hm' heq
    rcases lt_trichotomy m m' with hlt | heq' | hgt
    · exact absurd heq.symm (LOFA_IMP_DIS_ELMS23 h hv m m' hlt (by omega))
    · exact heq'
    · exact absurd heq (LOFA_IMP_DIS_ELMS23 h hv m' m hgt (by omega))
  have ha0n : a n ≠ a 0 := by
    intro heq
    exact hvw (by rw [han, ha0] at heq; exact heq.symm)
  have hasucc : ∀ m, a (m + 1) = rhoNode1_p2 FF (a m) := fun m =>
    Function.iterate_succ_apply' (rhoNode1_p2 FF) m v
  -- membership description of `fv`
  have hfvm : ∀ p : V3 × V3, p ∈ fv ↔
      p = (a n, a 0) ∨ ∃ m, m < n ∧ p = (a m, a (m + 1)) := by
    intro p
    rw [hfv2']
    constructor
    · intro hp
      rcases Set.mem_insert_iff.mp hp with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hp
      rcases hp with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr h)
  -- `a m ∈ V` on the window
  have haV : ∀ m, m ≤ n → a m ∈ V := fun m hm =>
    LOCAL_FAN_ITER_RHO_NODE_IN_V h hv m
  -- the polygon dart `(a m, a (next m))`
  have hgdarts : ∀ m, m ≤ n → (a m, a (w2nx n m)) ∈ fv := by
    intro m hm
    rw [hfvm]
    by_cases hmn : m = n
    · left
      subst hmn
      rw [w2nx_self]
    · right
      refine ⟨m, by omega, ?_⟩
      rw [w2nx_lt (by omega)]
  -- ## 1. lookups and injectivity
  have hfst_lookup : ∀ p, p ∈ fv → ∀ m, m ≤ n → p.1 = a m → p = (a m, a (w2nx n m)) := by
    intro p hp m hm hpm
    rcases (hfvm p).mp hp with h | ⟨k, hk, hkp⟩
    · have hnk : a n = a m := by rw [← hpm]; rw [h]
      have hmn : m = n := (hainj n m (le_refl n) hm hnk).symm
      subst hmn
      rw [w2nx_self]
      exact h
    · have hkm : a k = a m := by rw [← hpm]; rw [hkp]
      have hke : k = m := hainj k m (by omega) hm hkm
      subst hke
      rw [hkp, w2nx_lt (by omega)]
  have hsnd_lookup : ∀ p, p ∈ fv → ∀ m, m ≤ n → p.2 = a (w2nx n m) → p = (a m, a (w2nx n m)) := by
    intro p hp m hm hpm
    rcases (hfvm p).mp hp with h | ⟨k, hk, hkp⟩
    · have hz : a 0 = a (w2nx n m) := by rw [← hpm]; rw [h]
      have hzm : w2nx n m = 0 := hainj (w2nx n m) 0 (w2nx_le hm) (by omega) hz.symm
      have hmn : m = n := by
        have h2 := w2pv_nx hm
        rw [hzm, w2pv_idx0] at h2
        omega
      subst hmn
      rw [w2nx_self]
      exact h
    · have hz : a (k + 1) = a (w2nx n m) := by rw [← hpm]; rw [hkp]
      have hzm : w2nx n m = k + 1 := hainj (w2nx n m) (k + 1) (w2nx_le hm) (by omega) hz.symm
      have hkm : k = m := by
        have h2 := w2pv_nx hm
        rw [hzm, w2pv_succ] at h2
        omega
      subst hkm
      rw [hkp, w2nx_lt (by omega)]
  have hfst_inj : Set.InjOn Prod.fst fv := by
    intro p hp q hq hpq
    obtain ⟨m, hm, hpm⟩ : ∃ m, m ≤ n ∧ p = (a m, a (w2nx n m)) := by
      rcases (hfvm p).mp hp with h | ⟨k, hk, hkp⟩
      · exact ⟨n, le_refl n, by rw [h, w2nx_self]⟩
      · exact ⟨k, by omega, by rw [hkp, w2nx_lt (by omega)]⟩
    have hqm : q.1 = a m := by rw [← hpq]; rw [hpm]
    rw [hfst_lookup q hq m hm hqm, hpm]
  have hsnd_inj : Set.InjOn Prod.snd fv := by
    intro p hp q hq hpq
    obtain ⟨m, hm, hpm⟩ : ∃ m, m ≤ n ∧ p = (a m, a (w2nx n m)) := by
      rcases (hfvm p).mp hp with h | ⟨k, hk, hkp⟩
      · exact ⟨n, le_refl n, by rw [h, w2nx_self]⟩
      · exact ⟨k, by omega, by rw [hkp, w2nx_lt (by omega)]⟩
    have hqm : q.2 = a (w2nx n m) := by rw [← hpq]; rw [hpm]
    rw [hsnd_lookup q hq m hm hqm, hpm]
  -- ## 2. `ePrime` membership and the dart set
  have hmemE : ∀ (u z : V3), ({u, z} : Set V3) ∈ ePrime_p2 (E ∪ {{v, w}}) fv →
      (u, z) ∈ fv ∨ (z, u) ∈ fv := by
    intro u z hmem
    simp only [ePrime_p2, Set.mem_setOf_eq] at hmem
    obtain ⟨p, q, hpq, -, hpqfv⟩ := hmem
    have hp : p = u ∨ p = z := by
      have h1 : p ∈ ({p, q} : Set V3) := by simp
      rw [← hpq] at h1
      simpa using h1
    have hq : q = u ∨ q = z := by
      have h1 : q ∈ ({p, q} : Set V3) := by simp
      rw [← hpq] at h1
      simpa using h1
    rcases hp with hpu | hpz
    · rw [hpu] at hpqfv
      rcases hq with hqu | hqz
      · rw [hqu] at hpqfv
        have hzu : z = u := by
          have h1 : z ∈ ({u, z} : Set V3) := by simp
          rw [hpq] at h1
          simpa [hpu, hqu] using h1
        rw [hzu]; left; exact hpqfv
      · rw [hqz] at hpqfv
        left; exact hpqfv
    · rw [hpz] at hpqfv
      rcases hq with hqu | hqz
      · rw [hqu] at hpqfv
        right; exact hpqfv
      · rw [hqz] at hpqfv
        have huz : u = z := by
          have h1 : u ∈ ({u, z} : Set V3) := by simp
          rw [hpq] at h1
          simpa [hpz, hqz] using h1
        rw [huz]; right; exact hpqfv
  -- `fv ⊆ darts` needs the carrier pair memberships
  have hpairE : ∀ p ∈ fv, ({p.1, p.2} : Set V3) ∈ (E ∪ {{v, w}} : Set (Set V3)) := by
    intro p hp
    have hdf : (v, rhoNode1_p2 FF v) ∈ (↑HS.darts : Set (V3 × V3)) := by
      rw [hHS.1]
      exact Or.inl (Or.inl (LOCAL_FAN_IN_FF_IN_ORD_PAIRS h
        ((LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv)))
    have hface : p ∈ HS.face (v, rhoNode1_p2 FF v) := by rw [← hfv]; exact hp
    have hdfv : p ∈ (↑HS.darts : Set (V3 × V3)) := HS.face_subset_darts hdf hface
    rw [hHS.1] at hdfv
    simp only [dartsOfHyp_p2, Set.mem_union, ordPairs_p2, selfPairs_p2, Set.mem_setOf_eq] at hdfv
    rcases hdfv with hord | hself
    · exact hord
    · exfalso
      obtain ⟨hpeq, -, -⟩ := hself
      rcases (hfvm p).mp hp with hh | ⟨k, hk, hkp⟩
      · exact ha0n (by rw [hh] at hpeq; exact hpeq)
      · have h1 : a k = a (k + 1) := by rw [hkp] at hpeq; exact hpeq
        exact absurd (hainj k (k + 1) (by omega) (by omega) h1) (by omega)
  have hfv_darts : ∀ p ∈ fv, p ∈ (↑HS'.darts : Set (V3 × V3)) := by
    intro p hp
    rw [hHS'.1]
    simp only [dartsOfHyp_p2, Set.mem_union, ordPairs_p2, Set.mem_setOf_eq, ePrime_p2]
    exact Or.inl ⟨p.1, p.2, rfl, hpairE p hp, hp⟩
  -- every slice dart is `fv` or the reverse of an `fv` dart
  have hdarts_sub : ∀ x, x ∈ (↑HS'.darts : Set (V3 × V3)) → x ∈ fv ∨ (x.2, x.1) ∈ fv := by
    intro x hx
    rw [hHS'.1] at hx
    simp only [dartsOfHyp_p2, Set.mem_union, ordPairs_p2, selfPairs_p2,
      Set.mem_setOf_eq] at hx
    rcases hx with hord | hself
    · exact hmemE x.1 x.2 hord
    · exfalso
      obtain ⟨-, hxv, hEE0⟩ := hself
      simp only [vPrime_p2, Set.mem_setOf_eq] at hxv
      obtain ⟨-, b, hbfv⟩ := hxv
      have hbEE : b ∈ EE_p2 x.1 (ePrime_p2 (E ∪ {{v, w}}) fv) := by
        simp only [EE_p2, Set.mem_setOf_eq, ePrime_p2]
        exact ⟨x.1, b, rfl, hpairE (x.1, b) hbfv, hbfv⟩
      rw [hEE0] at hbEE
      exact absurd hbEE (by simp)
  -- ## 3. the neighbour sets `EE (a m)`
  have hEE : ∀ m, m ≤ n → EE_p2 (a m) (ePrime_p2 (E ∪ {{v, w}}) fv)
      = ({a (w2pv n m), a (w2nx n m)} : Set V3) := by
    intro m hm
    ext y
    constructor
    · intro hy
      simp only [EE_p2, Set.mem_setOf_eq] at hy
      rcases hmemE (a m) y hy with h | h
      · have hyv : y = a (w2nx n m) := by
          have h2 := hfst_lookup (a m, y) h m hm rfl
          simpa using congrArg Prod.snd h2
        rw [hyv]; simp
      · have h0 : w2pv n m ≤ n := w2pv_le hm
        have hyv : y = a (w2pv n m) := by
          have h2 := hsnd_lookup (y, a m) h (w2pv n m) h0 (by rw [w2nx_pv hm])
          simpa using congrArg Prod.fst h2
        rw [hyv]; simp
    · intro hy
      have h0 : w2pv n m ≤ n := w2pv_le hm
      have h1 : w2nx n m ≤ n := w2nx_le hm
      rcases (by simpa using hy : y = a (w2pv n m) ∨ y = a (w2nx n m)) with rfl | rfl
      · -- predecessor direction: `{a (pv m), a m} ∈ ePrime`
        simp only [EE_p2, Set.mem_setOf_eq, ePrime_p2, Set.mem_setOf_eq]
        refine ⟨a (w2pv n m), a m, Set.pair_comm _ _, ?_, ?_⟩
        · by_cases hpz : m = 0
          · subst hpz
            rw [w2pv_idx0, han, ha0]
            exact Or.inr (Set.mem_singleton_iff.mpr (Set.pair_comm v w).symm)
          · have hpos : 0 < m := by omega
            rw [w2pv_pos hpos]
            have hstep : a m = rhoNode1_p2 FF (a (m - 1)) := by
              have h1' := hasucc (m - 1)
              have h2' : (m - 1) + 1 = m := by omega
              rw [h2'] at h1'
              exact h1'
            rw [hstep]
            exact Or.inl (LOCAL_RHO_NODE_PAIR_E h (haV (m - 1) (by omega)))
        · rw [hfvm]
          by_cases hpz : m = 0
          · subst hpz
            rw [w2pv_idx0]
            exact Or.inl rfl
          · right
            refine ⟨m - 1, by omega, ?_⟩
            rw [w2pv_pos (by omega)]
            rw [show m - 1 + 1 = m from by omega]
      · -- successor direction: `{a m, a (nx m)} ∈ ePrime`
        simp only [EE_p2, Set.mem_setOf_eq, ePrime_p2, Set.mem_setOf_eq]
        refine ⟨a m, a (w2nx n m), rfl, ?_, hgdarts m hm⟩
        by_cases hmn : m = n
        · subst hmn
          rw [w2nx_self, han, ha0]
          exact Or.inr (Set.mem_singleton_iff.mpr (Set.pair_comm v w).symm)
        · rw [w2nx_lt (by omega), hasucc m]
          exact Or.inl (LOCAL_RHO_NODE_PAIR_E h (haV m hm))
  -- ## 4. the face walk on `fv`
  have hff : ∀ d ∈ (↑HS'.darts : Set (V3 × V3)),
      HS'.faceMap d =
        (d.2, ivsAzimCycle_p2 (EE_p2 d.2 (ePrime_p2 (E ∪ {{v, w}}) fv)) 0 d.2 d.1) := by
    intro d hd
    have hd' : d ∈ dartsOfHyp_p2 (ePrime_p2 (E ∪ {{v, w}}) fv) (vPrime_p2 V fv) := by
      rw [← hHS'.1]; exact hd
    show (HS'.faceMap : V3 × V3 → V3 × V3) d = _
    rw [hHS'.2.2.2]
    show (if d ∈ dartsOfHyp_p2 (ePrime_p2 (E ∪ {{v, w}}) fv) (vPrime_p2 V fv) then
      (d.2, ivsAzimCycle_p2 (EE_p2 d.2 (ePrime_p2 (E ∪ {{v, w}}) fv)) 0 d.2 d.1) else d) = _
    rw [if_pos hd']
  have hg_ff : ∀ m, m ≤ n →
      HS'.faceMap (a m, a (w2nx n m)) = (a (w2nx n m), a (w2nx n (w2nx n m))) := by
    intro m hm
    have hgd : (a m, a (w2nx n m)) ∈ (↑HS'.darts : Set (V3 × V3)) := hfv_darts _ (hgdarts m hm)
    have hstep := hff (a m, a (w2nx n m)) hgd
    rw [hstep]
    have h1 : w2nx n m ≤ n := w2nx_le hm
    have h2 : w2pv n (w2nx n m) = m := w2pv_nx hm
    rw [hEE (w2nx n m) h1, h2, w2_ivs_pair (a m) (a (w2nx n (w2nx n m))) 0 (a (w2nx n m))]
  -- the full `faceMap` orbit of the base dart `g 0`
  have hiter : ∀ k, (HS'.faceMap^[k]) (a 0, a (w2nx n 0))
      = (a ((w2nx n)^[k] 0), a (w2nx n ((w2nx n)^[k] 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih =>
      have h1 : (HS'.faceMap^[j+1]) (a 0, a (w2nx n 0))
          = HS'.faceMap ((HS'.faceMap^[j]) (a 0, a (w2nx n 0))) :=
        Function.iterate_succ_apply' _ _ _
      rw [h1, ih]
      rw [show (w2nx n)^[j+1] 0 = w2nx n ((w2nx n)^[j] 0) from
        Function.iterate_succ_apply' _ _ _]
      exact hg_ff ((w2nx n)^[j] 0) (w2nx_iter_le n j)
  have hface_g0 : HS'.face (a 0, a (w2nx n 0)) = fv := by
    ext z
    constructor
    · intro hz
      rw [Hypermap.face, orbitMap] at hz
      simp only [Set.mem_setOf_eq] at hz
      obtain ⟨k, hk⟩ := hz
      rw [Equiv.Perm.coe_pow] at hk
      rw [← hk, hiter]
      exact hgdarts _ (w2nx_iter_le n k)
    · intro hz
      rw [Hypermap.face, orbitMap]
      simp only [Set.mem_setOf_eq]
      rcases (hfvm z).mp hz with hh | ⟨m, hm, hhm⟩
      · refine ⟨n, ?_⟩
        rw [Equiv.Perm.coe_pow, hiter, w2nx_zero (le_refl n), w2nx_self]
        exact hh.symm
      · refine ⟨m, ?_⟩
        rw [Equiv.Perm.coe_pow, hiter, w2nx_zero (by omega), w2nx_lt (by omega)]
        exact hhm.symm
  have hface_fv : ∀ z ∈ fv, HS'.face z = fv := by
    intro z hz
    have hzface : z ∈ HS'.face (a 0, a (w2nx n 0)) := by rw [hface_g0]; exact hz
    have h := Hypermap.face_eq_of_mem HS' hzface
    rw [hface_g0] at h
    exact h.symm
  -- faces of non-`fv` darts avoid `fv`
  have hface_notfv : ∀ x ∈ (↑HS'.darts : Set (V3 × V3)), x ∉ fv →
      HS'.face x ⊆ {y : V3 × V3 | (y.2, y.1) ∈ fv} := by
    intro x hx hxn z hz
    have hznot : z ∉ fv := by
      intro hzf
      have h1 : HS'.face z = fv := hface_fv z hzf
      have h2 : HS'.face x = HS'.face z := Hypermap.face_eq_of_mem HS' hz
      rw [h1] at h2
      exact hxn (h2 ▸ HS'.mem_face_self x)
    have hzd : z ∈ (↑HS'.darts : Set (V3 × V3)) := HS'.face_subset_darts hx hz
    exact (hdarts_sub z hzd).resolve_left hznot
  -- ## 5. node orbits keep the first coordinate
  have hstep_fst : ∀ d : V3 × V3, (HS'.nodeMap d).1 = d.1 := by
    intro d
    rw [show (HS'.nodeMap : V3 × V3 → V3 × V3) d
      = nnOfHyp_p2 0 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) d from
      congrFun hHS'.2.2.1 d]
    exact w2_nn_fst d
  have hniter : ∀ (k : ℕ) (x : V3 × V3), (((HS'.nodeMap)^[k]) x).1 = x.1 := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hstep_fst]
      exact ih x
  have hnode_fst : ∀ {x z : V3 × V3}, z ∈ HS'.node x → z.1 = x.1 := by
    intro x z hz
    rw [Hypermap.node, orbitMap] at hz
    simp only [Set.mem_setOf_eq] at hz
    obtain ⟨k, hk⟩ := hz
    rw [Equiv.Perm.coe_pow] at hk
    rw [← hk]
    exact hniter k x
  -- ## 6. `Simple`
  intro x hx
  ext z
  constructor
  · intro hz
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzn, hzf⟩ := hz
    have hz1 : z.1 = x.1 := hnode_fst hzn
    by_cases hxfv : x ∈ fv
    · have hzfv : z ∈ fv := by
        have h1 := hface_fv x hxfv
        rw [h1] at hzf
        exact hzf
      rw [Set.mem_singleton_iff]
      exact hfst_inj hzfv hxfv hz1
    · have hxsw : (x.2, x.1) ∈ fv := (hdarts_sub x hx).resolve_left hxfv
      have hzsw : (z.2, z.1) ∈ fv := hface_notfv x hx hxfv hzf
      have hpair : (z.2, z.1) = (x.2, x.1) := hsnd_inj hzsw hxsw hz1
      rw [Set.mem_singleton_iff]
      rw [Prod.mk.injEq] at hpair
      exact Prod.ext hpair.2 hpair.1
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨HS'.mem_node_self x, HS'.mem_face_self x⟩

/-- HOL `HAFL_CIRCLE_FORM_LOCAL_FAN` (local_lemmas1.hl:3077) — giant. -/
theorem HAFL_CIRCLE_FORM_LOCAL_FAN (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv := by
  have hdFF : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  have hdOrd : (v, rhoNode1_p2 FF v) ∈ ordPairs_p2 E := LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdFF
  have hd : (v, rhoNode1_p2 FF v) ∈ dartsOfHyp_p2 (E ∪ {{v, w}}) V :=
    Or.inl (Or.inl hdOrd)
  exact HAFL_CIRCLE_FORM_LOCAL_FAN_of_dih h hv hw hvw hcol hsub HS hHS hfv
    (fun HS' hHS' =>
      DIH_K_HYP_E_PRIME (v := 0) (FF := fv)
        (PROVE_SLICING_FAN h hv hw hvw hcol hsub) hHS hHS' hd hfv
        (w2_slice_hyp_simple h hv hw hvw hcol hsub HS hHS hfv HS' hHS')
        (LOFA_HYP_UNION_CARD_GT2 h hv hw hvw hcol hsub HS hHS hfv))


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
      localFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw := by
  constructor
  · exact HAFL_CIRCLE_FORM_LOCAL_FAN h hv hw hvw hcol hsub HS hHS hfv
  · -- the `fw` side is the same theorem with `v` and `w` exchanged
    have hHSw : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
      have hEq : (E ∪ {{w, v}} : Set (Set V3)) = E ∪ {{v, w}} := by
        rw [Set.pair_comm w v]
      rw [hEq]
      exact hHS
    have hcolw : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
        ¬ Collinear ℝ ({0, z, t} : Set V3) := by
      intro z t hz ht
      exact hcol z t (by rwa [Set.pair_comm w v] at hz) ht
    have hsubw : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
      intro d hd
      rw [Set.pair_comm w v]
      exact hsub d hd
    have hdFF : (w, rhoNode1_p2 FF w) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 w hw
    have hdOrd : (w, rhoNode1_p2 FF w) ∈ ordPairs_p2 E :=
      LOCAL_FAN_IN_FF_IN_ORD_PAIRS h hdFF
    have hd : (w, rhoNode1_p2 FF w) ∈ dartsOfHyp_p2 (E ∪ {{w, v}}) V :=
      Or.inl (Or.inl hdOrd)
    exact HAFL_CIRCLE_FORM_LOCAL_FAN_of_dih (v := w) (w := v) (fv := fw)
      h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw
      (fun HS' hHS' =>
        DIH_K_HYP_E_PRIME (v := 0) (FF := fw)
          (PROVE_SLICING_FAN h hw hv (Ne.symm hvw) hcolw hsubw) hHSw hHS' hd hfw
          (w2_slice_hyp_simple (v := w) (w := v) (fv := fw)
            h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw HS' hHS')
          (LOFA_HYP_UNION_CARD_GT2 h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw))

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
        z = (rhoNode1_p2 FF)^[n] v} := by
  have hfvD := DETERMINE_FV h hv hw hvw hcol hsub HS hHS hfv
  ext z
  constructor
  · intro hz
    rw [vPrime_p2, Set.mem_setOf_eq] at hz
    obtain ⟨_, y, hzy⟩ := hz
    rw [hfvD] at hzy
    rcases Set.mem_insert_iff.mp hzy with hzy' | hzy'
    · have hzw : z = w := congrArg Prod.fst hzy'
      obtain ⟨n, _, hnw, hnmin⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
      exact ⟨n, hnmin, hzw.trans hnw.symm⟩
    · rw [Set.mem_setOf_eq] at hzy'
      obtain ⟨n, hncond, hpair⟩ := hzy'
      refine ⟨n, ?_, ?_⟩
      · intro m hm
        exact hncond m (by omega)
      · simpa using congrArg Prod.fst hpair
  · intro hz
    rw [Set.mem_setOf_eq] at hz
    obtain ⟨n, hncond, rfl⟩ := hz
    rw [vPrime_p2, Set.mem_setOf_eq]
    refine ⟨LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n, ?_⟩
    by_cases hwn : (rhoNode1_p2 FF)^[n] v = w
    · exact ⟨v, by rw [hfvD, hwn]; exact Set.mem_insert _ _⟩
    · refine ⟨(rhoNode1_p2 FF)^[n + 1] v, ?_⟩
      rw [hfvD, Set.mem_insert_iff]
      right
      rw [Set.mem_setOf_eq]
      refine ⟨n, ?_, rfl⟩
      intro m hm
      by_cases hmn : m < n
      · exact hncond m hmn
      · have hmn' : m = n := by omega
        rw [hmn']
        exact hwn

/-! ## w3: `_p2` MONO kit — pure affine / trig helpers (lane `la6-covex-w3`)

`COVEX_OF_LOFA_HALF_CIRCLE` consumes `MONO_AZIM_AS_BTA_I` (HOL
local_lemmas.hl:6448).  That theorem lives in LocalAuto14, which imports
LocalAuto6, so it cannot be imported here.  This section restates and proves
the unconditional MONO at the `_p2` encoding *inside* LocalAuto6 (option (b):
self-contained, zero import change, acyclic — LocalAuto14/LocalAuto35 stay
untouched).

Provenance of the copied pieces (all pure, carrier-free):
- `w16_*`/`AZIM_EQ_PI_ALT`/`CONV02_SU_CONV2`/`OPPOSITE_SIDES_IMP_INTER`:
  LocalAuto14 §0–§4 (verbatim proof bodies, `LocalFan`→`localFan_p2`
  transport dropped — the `_p2` statements below take the `_p2` hypothesis
  directly).
- `IN_V_IMP_AZIM_LESS_PI`: LocalAuto9:1378 at `_p2` (verbatim, the LA9
  version already lives at `convexLocalFan_p2`).
- trig core (`monoStepCore`/`monoStepOrbit`/`monoWindowNowrap` and helpers):
  LocalAuto35 GATE-B section (private there; copied verbatim with the
  `_p35`→ no suffix rename).
NEEDS: dedup at merge — these are statement-identical twins of the LA14/LA35
private kit, single-home move once the wave closes.
-/

/-- `V3` cross product (copy of `Kepler.Text.cross3`, PackingAuto18:210; that
module is not on LocalAuto6's import face).  Private: no namespace surface. -/
private noncomputable def cross3 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))

/-! ### §0 small self-contained helpers (LocalAuto14 §0 verbatim) -/

private theorem w16_dot3_eq (x y : V3) :
    x ⬝ᵥ y = ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ) := rfl

private theorem w16_coe_cross3 (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) =
      crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ) := rfl

private theorem w16_cross3_dotL (u v : V3) : cross3 u v ⬝ᵥ u = 0 := by
  rw [w16_dot3_eq, w16_coe_cross3, dotProduct_comm]
  exact dot_self_cross _ _

private theorem w16_cross3_dotR (u v : V3) : cross3 u v ⬝ᵥ v = 0 := by
  rw [w16_dot3_eq, w16_coe_cross3, dotProduct_comm]
  exact dot_cross_self _ _

private theorem w16_dot3_comm (x y : V3) : x ⬝ᵥ y = y ⬝ᵥ x := dotProduct_comm _ _

private theorem w16_dot3_smul_left (t : ℝ) (x z : V3) :
    (t • x) ⬝ᵥ z = t * (x ⬝ᵥ z) := by
  rw [w16_dot3_eq, w16_dot3_eq]
  simp only [WithLp.ofLp_smul]
  exact smul_dotProduct _ _ _

private theorem w16_dot3_add_right (x y z : V3) : z ⬝ᵥ (x + y) = z ⬝ᵥ x + z ⬝ᵥ y := by
  rw [w16_dot3_eq, w16_dot3_eq, w16_dot3_eq]
  simp only [WithLp.ofLp_add]
  exact dotProduct_add _ _ _

private theorem w16_dot3_smul_right (t : ℝ) (x z : V3) :
    z ⬝ᵥ (t • x) = t * (z ⬝ᵥ x) := by
  rw [w16_dot3_eq, w16_dot3_eq]
  simp only [WithLp.ofLp_smul]
  rw [dotProduct_smul, smul_eq_mul]

private theorem w16_dot3_self_pos {x : V3} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have hn : ‖x‖ ≠ 0 := fun hzero => hx (norm_eq_zero.mp hzero)
  have h1 : (0:ℝ) < ‖x‖ ^ 2 := sq_pos_iff.mpr hn
  rwa [norm_sq_eq_dot] at h1

private theorem w16_cross3_ne {u v : V3} (h : ¬ Collinear ℝ ({0, u, v} : Set V3)) :
    cross3 u v ≠ 0 := by
  intro hz
  exact h ((COLLINEAR_CROSS_0 (x := (0:V3)) (y := u) (z := v)).mpr
    (by simpa [cross3] using hz))

/-- Extraction on an origin-line (copy of LA14's private `smul_of_collinear0_p14`). -/
private theorem w16_smul_of_collinear0 {c v : V3} (hc : c ≠ 0)
    (h : Collinear ℝ ({0, c, v} : Set V3)) : ∃ t : ℝ, v = t • c := by
  obtain ⟨p₀, u, hub⟩ := collinear_iff_exists_forall_eq_smul_vadd _ |>.1 h
  obtain ⟨r0, h0⟩ := hub 0 (by simp)
  obtain ⟨r1, h1⟩ := hub c (by simp)
  obtain ⟨r2, h2⟩ := hub v (by simp)
  rw [vadd_eq_add] at h0 h1 h2
  have hpc : p₀ = -(r0 • u) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
  have hu : u ≠ 0 := by
    intro hzero
    rw [hzero, smul_zero, zero_add, hpc, hzero, smul_zero, neg_zero] at h1
    exact hc h1
  have hvc : c = (r1 - r0) • u := by rw [h1, hpc, sub_smul]; module
  have hvd : v = (r2 - r0) • u := by rw [h2, hpc, sub_smul]; module
  by_cases hr : r1 - r0 = 0
  · rw [hr, zero_smul] at hvc; exact absurd hvc hc
  refine ⟨(r2 - r0) / (r1 - r0), ?_⟩
  rw [hvd, hvc, smul_smul]
  field_simp

/-! ### §1 CONV02_SU_CONV2 (LocalAuto14 §1 verbatim) -/

/-- HOL `CONV02_SU_CONV2`: `conv0 {a,b} ⊆ conv {a,b}`. -/
private theorem CONV02_SU_CONV2 (a b : V3) :
    conv0_p2 ({a, b} : Set V3) ⊆ convexHull ℝ ({a, b} : Set V3) := by
  intro x hx
  obtain ⟨f, hfin, hvec, hpos, hone⟩ := hx
  have hT : hfin.toFinset = ({a, b} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_empty_iff_false,
      false_or, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  by_cases hab : a = b
  · subst b
    have hT' : hfin.toFinset = ({a} : Finset V3) := by
      rw [hT]; ext w; simp
    have h1 : f a = 1 := by
      rw [hT', Finset.sum_singleton] at hone; exact hone
    have hx2 : x = a := by
      rw [hvec, hT', Finset.sum_singleton, h1, one_smul]
    rw [hx2]
    exact subset_convexHull ℝ _ (by simp)
  · have hsum : f a + f b = 1 := by
      rw [hT, Finset.sum_insert (by simp [hab]), Finset.sum_singleton] at hone
      exact hone
    have hx2 : x = f a • a + f b • b := by
      rw [hvec, hT, Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
    rw [hx2]
    exact (convex_convexHull ℝ ({a, b} : Set V3))
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      (hpos a (by simp)).le (hpos b (by simp)).le hsum

/-! ### §2 AZIM_EQ_PI_ALT (LocalAuto14 §2 verbatim) -/

/-- `affLt {0,u} {v}` 的三系数提取。 -/
private theorem w16_affLt_coeffs {u v w : V3} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hw : w ∈ affLt ({0, u} : Set V3) ({v} : Set V3)) :
    ∃ t1 t2 t3 : ℝ, t3 < 0 ∧ t1 + t2 + t3 = 1 ∧ w = t1 • (0 : V3) + t2 • u + t3 • v := by
  obtain ⟨f, hfin, hsum, hneg, hone⟩ := hw
  have htf : hfin.toFinset = ({0, u, v} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨f 0, f u, f v, hneg v (by simp), ?_, ?_⟩
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton] at hone
    linarith
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton] at hsum
    rw [hsum]
    abel

/-- 三系数形构造回 `affLt {0,u} {v}`。 -/
private theorem w16_affLt_of_coeffs {u v w : V3} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    {t1 t2 t3 : ℝ} (ht3 : t3 < 0) (hsum : t1 + t2 + t3 = 1)
    (hrep : w = t1 • (0 : V3) + t2 • u + t3 • v) :
    w ∈ affLt ({0, u} : Set V3) ({v} : Set V3) := by
  have hfin : (({0, u} : Set V3) ∪ {v} : Set V3).Finite :=
    ((Set.finite_singleton u).insert 0).union (Set.finite_singleton v)
  have htf : hfin.toFinset = ({0, u, v} : Finset V3) := by
    apply Finset.ext
    intro q
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨fun q => if q = v then t3 else if q = u then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
    simp [hu0.symm, hv0.symm, huv]
    simpa using hrep
  · intro q hq
    simp only [Set.mem_singleton_iff] at hq
    subst hq
    simp [hu0.symm, hv0.symm, huv]
    exact ht3
  · rw [htf, Finset.sum_insert (by simp [hu0.symm, hv0.symm]),
      Finset.sum_insert (by simp [huv]), Finset.sum_singleton]
    simp [hu0.symm, hv0.symm, huv]
    linarith

/-- HOL `AZIM_EQ_PI_ALT`: `azim 0 u v w = π ↔ w ∈ affLt {0,u} {v}`. -/
private theorem AZIM_EQ_PI_ALT {u v w : V3}
    (huv : ¬ Collinear3 0 u v) (huw : ¬ Collinear3 0 u w) :
    azim 0 u v w = Real.pi ↔ w ∈ affLt ({0, u} : Set V3) ({v} : Set V3) := by
  have hu0 : u ≠ 0 := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) v)
  have hv0 : v ≠ 0 := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) u)
  have huvne : u ≠ v := fun he => huv (by
    rw [he]; simpa [Collinear3, Set.pair_comm] using collinear_pair ℝ (0:V3) v)
  obtain ⟨e1, e2, e3, hon, halign⟩ := exists_on3_eq_smul (u - 0) (sub_ne_zero.mpr hu0)
  have hax : (u - 0 : V3) = dist u 0 • e3 := by rw [dist_eq_norm]; exact halign
  constructor
  · intro hpi
    have hvw : v ≠ w := by
      intro he
      rw [he, azim_self] at hpi
      exact Real.pi_pos.ne' hpi.symm
    obtain ⟨h1, h2, hframes⟩ := (azim_master (0 : V3) u v w).2.2
    obtain ⟨ψ, r1, r2, repv, repw, hr1, hr2⟩ := hframes e1 e2 e3 hon hax hu0
    have hr1' : 0 < r1 := hr1 huv
    have hr2' : 0 < r2 := hr2 huw
    rw [hpi, Real.cos_add_pi, Real.sin_add_pi] at repw
    have hkey : w - 0 = (-(r2 / r1)) • (v - 0) + (h2 + (r2 / r1) * h1) • (u - 0) := by
      rw [repv, repw]
      simp only [smul_add, smul_smul]
      have hc1 : (-(r2 / r1)) * (r1 * Real.cos ψ) = -(r2 * Real.cos ψ) := by
        field_simp
      have hc2 : (-(r2 / r1)) * (r1 * Real.sin ψ) = -(r2 * Real.sin ψ) := by
        field_simp
      have hc3 : (-(r2 / r1)) * h1 + (h2 + (r2 / r1) * h1) = h2 := by ring
      rw [hc1, hc2, ← hc3]
      module
    have hwrep : w = (-(r2 / r1)) • v + (h2 + (r2 / r1) * h1) • u := by
      simpa using hkey
    refine w16_affLt_of_coeffs (u := u) (v := v) (w := w) hu0 hv0 huvne
      (t1 := 1 - (h2 + (r2 / r1) * h1) - (-(r2 / r1)))
      (t2 := h2 + (r2 / r1) * h1) (t3 := -(r2 / r1)) ?_ ?_ ?_
    · have : 0 < r2 / r1 := div_pos hr2' hr1'
      linarith
    · ring
    · rw [hwrep]; simp only [smul_zero, zero_add]; exact add_comm _ _
  · intro hmem
    obtain ⟨t1, t2, t3, ht3, hsum, hrep⟩ := w16_affLt_coeffs hu0 hv0 huvne hmem
    obtain ⟨ψ, r1, r2, hr1', hr2', hzv, hzw⟩ :=
      azim_frame_spec (v := (0 : V3)) (w := u) (w1 := v) (w2 := w) huv huw hon hax hu0
    have hzu : zOf e1 e2 u = 0 := by
      simpa using zOf_axis (v := (0 : V3)) (w := u) hax hon
    have hz0 : zOf e1 e2 (0 : V3) = 0 := by simp [zOf]
    have hzlin : zOf e1 e2 (w - 0) = ((t3 : ℝ) : ℂ) * zOf e1 e2 (v - 0) := by
      have hw0 : w - 0 = t1 • (0 : V3) + t2 • u + t3 • v := by rw [sub_zero, hrep]
      rw [hw0]
      simp only [zOf_add, zOf_smul, hzu, hz0, mul_zero, add_zero, sub_zero]
      ring
    rw [hzv, hzw] at hzlin
    have hexp : Complex.exp (((ψ + azim 0 u v w : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((azim 0 u v w : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp] at hzlin
    have h2 : (((r2 : ℝ) : ℂ) * Complex.exp (((azim 0 u v w : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        = (((t3 * r1 : ℝ) : ℂ)) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
      push_cast
      linear_combination hzlin
    have hkey := mul_right_cancel₀ (Complex.exp_ne_zero _) h2
    have hsin : Real.sin (azim 0 u v w) = 0 := by
      have hi := congrArg Complex.im hkey
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_mul_I,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        add_zero, zero_add, mul_one, mul_add, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re] at hi
      have h0 : r2 * Real.sin (azim 0 u v w) = 0 := by linarith [hi]
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hr2')
      · exact h
    have hcos : Real.cos (azim 0 u v w) < 0 := by
      have hr := congrArg Complex.re hkey
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_mul_I,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        add_zero, zero_add, mul_one, mul_add, Complex.cos_ofReal_re,
        Complex.sin_ofReal_im] at hr
      have h1 : r2 * Real.cos (azim 0 u v w) = t3 * r1 := by linarith [hr]
      have : t3 * r1 < 0 := mul_neg_of_neg_of_pos ht3 hr1'
      nlinarith [hr1', hr2', h1]
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
    have hθ0 := azim_nonneg 0 u v w
    have hθπ := azim_lt_two_pi 0 u v w
    have hn0 : 0 ≤ n := by
      by_contra hcon
      push_neg at hcon
      have hnle : ((n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega)
      nlinarith
    have hn1 : n ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have hnge : (2 : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega)
      nlinarith
    interval_cases n
    · rw [← hn] at hcos
      norm_num at hcos
    · rw [← hn]
      push_cast
      ring

/-! ### §3 ray / aff_ge / aff_lt kit (LocalAuto14 §3 verbatim) -/

/-- `affGe {x} ∅ = {x}`. -/
private theorem w16_affGe_empty_singleton (x : V3) : affGe ({x} : Set V3) (∅ : Set V3) = {x} := by
  ext y
  constructor
  · rintro ⟨f, hfin, hsum, -, hone⟩
    have h2 : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, Finset.mem_singleton]
    rw [h2, Finset.sum_singleton] at hsum hone
    rw [Set.mem_singleton_iff, hsum, hone, one_smul]
  · intro heq
    rw [heq]
    have hfin : (({x} : Set V3) ∪ (∅ : Set V3)).Finite := by simp
    have hT : hfin.toFinset = ({x} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, or_false, Finset.mem_singleton]
    refine ⟨fun _ => 1, hfin, ?_, ?_, ?_⟩
    · rw [hT, Finset.sum_singleton, one_smul]
    · intro z hz
      exact zero_le_one
    · rw [hT, Finset.sum_singleton]

/-- Affsign membership from a two-term representation. -/
private theorem w16_affsign_single {x u y : V3} (hxu : x ≠ u) {t1 t2 : ℝ}
    (hy : y = t1 • x + t2 • u) (hsum : t1 + t2 = 1) {sgn : ℝ → Prop} (h2 : sgn t2) :
    Affsign sgn ({x} : Set V3) ({u} : Set V3) y := by
  have hfin : (({x} : Set V3) ∪ {u}).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton u)
  have hT : hfin.toFinset = ({x, u} : Finset V3) := by
    ext w
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun w => if w = u then t2 else t1, hfin, ?_, ?_, ?_⟩
  · rw [hT, Finset.sum_insert (by simp [hxu]), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxu, smul_zero, zero_add]
    exact hy
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simpa using h2
  · rw [hT, Finset.sum_insert (by simp [hxu]), Finset.sum_singleton]
    simp only [if_pos rfl, if_neg hxu]
    exact hsum

/-- `t • u ∈ affGe {0} {u}` for `t ≥ 0`. -/
private theorem w16_smul_mem_affGe {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    t • u ∈ affGe ({0} : Set V3) ({u} : Set V3) :=
  w16_affsign_single (x := 0) (u := u) (y := t • u) (sgn := fun x => 0 ≤ x)
    (by simpa using hu.symm) (t1 := 1 - t) (t2 := t) (by simp) (by ring)
    (by simpa using ht)

/-- `t • u ∈ affLt {0} {u}` for `t < 0`. -/
private theorem w16_smul_mem_affLt {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : t < 0) :
    t • u ∈ affLt ({0} : Set V3) ({u} : Set V3) :=
  w16_affsign_single (x := 0) (u := u) (y := t • u) (sgn := fun x => x < 0)
    (by simpa using hu.symm) (t1 := 1 - t) (t2 := t) (by simp) (by ring)
    (by simpa using ht)

/-- `affGt ∅ S ⊆ affGt {0} S` when `0 ∉ S`. -/
private theorem w16_affGt_empty_subset {S : Set V3} (h0S : (0:V3) ∉ S) :
    affGt (∅ : Set V3) S ⊆ affGt ({0} : Set V3) S := by
  rintro v ⟨f, hfin, hvec, hpos, hone⟩
  have hSfin : S.Finite := by simpa using hfin
  have hfin' : (({0} : Set V3) ∪ S).Finite := hSfin.insert 0
  have hT : hfin.toFinset = hSfin.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_empty_iff_false,
      false_or]
  have hT' : hfin'.toFinset = insert (0:V3) hSfin.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert]
  set g : V3 → ℝ := fun w => if w = 0 then 0 else f w with hg
  have hg_eq : ∀ w ∈ hSfin.toFinset, g w = f w := by
    intro w hw
    have hwS : w ∈ S := by simpa using hw
    have hw0 : w ≠ 0 := fun h => h0S (h ▸ hwS)
    simp only [hg, if_neg hw0]
  have hg0 : g (0:V3) = 0 := by simp [hg]
  refine ⟨g, hfin', ?_, ?_, ?_⟩
  · rw [hT', Finset.sum_insert (by simp [h0S]), hg0, zero_smul, zero_add]
    rw [show (∑ w ∈ hSfin.toFinset, g w • w) = ∑ w ∈ hSfin.toFinset, f w • w from by
      refine Finset.sum_congr rfl ?_
      intro w hw
      rw [hg_eq w hw]]
    rw [← hT]
    exact hvec
  · intro w hw
    have hwS : w ∈ S := hw
    have hw0 : w ≠ 0 := fun h => h0S (h ▸ hwS)
    simp only [hg, if_neg hw0]
    exact hpos w hwS
  · rw [hT', Finset.sum_insert (by simp [h0S]), hg0, zero_add]
    rw [show (∑ w ∈ hSfin.toFinset, g w) = ∑ w ∈ hSfin.toFinset, f w from by
      refine Finset.sum_congr rfl ?_
      intro w hw
      rw [hg_eq w hw]]
    rw [← hT]
    exact hone

/-! ### §4 cross / triple product kit (LocalAuto14 §4 verbatim) -/

/-- V3 dot of `cross3` equals the `Fin 3 → ℝ` dot of `crossProduct`. -/
private theorem w16_cross3_dot_eq (u v w : V3) :
    (cross3 u v) ⬝ᵥ w =
      (crossProduct ((u:V3) : Fin 3 → ℝ) ((v:V3) : Fin 3 → ℝ)) ⬝ᵥ ((w:V3) : Fin 3 → ℝ) := by
  rw [w16_dot3_eq, w16_coe_cross3]

/-- Scalar triple product identity: `((u × v) × u) · v = (u × v) · (u × v)`. -/
private theorem w16_triple_identity (u v : V3) :
    (cross3 (cross3 u v) u) ⬝ᵥ v = (cross3 u v) ⬝ᵥ (cross3 u v) := by
  rw [w16_dot3_eq, w16_coe_cross3, w16_coe_cross3, dotProduct_comm]
  exact triple_product_permutation ((v:V3) : Fin 3 → ℝ)
    (crossProduct ((u:V3) : Fin 3 → ℝ) ((v:V3) : Fin 3 → ℝ)) ((u:V3) : Fin 3 → ℝ)

/-! ### §5 affine combination helpers + OPPOSITE_SIDES_IMP_INTER
(LocalAuto14 w15 block verbatim) -/

private theorem w15_div_combo {t1 t2 t3 : ℝ} (ht3 : t3 ≠ 0) (hsum : t1 + t2 + t3 = 1) :
    -(t1 / t3) + -(t2 / t3) + 1 / t3 = 1 := by
  have h : -(t1 / t3) + -(t2 / t3) + 1 / t3 = (-t1 - t2 + 1) / t3 := by
    field_simp
    ring
  rw [h, div_eq_one_iff_eq ht3]
  linarith

private theorem w15_div_combo_vec {a b x y : V3} {t1 t2 t3 : ℝ} (ht3 : t3 ≠ 0)
    (hy : y = t1 • a + t2 • b + t3 • x) :
    x = (-(t1 / t3)) • a + (-(t2 / t3)) • b + (1 / t3) • y := by
  subst hy
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have h1 : (1 / t3) * t3 = 1 := by field_simp
  have h2 : (1 / t3) * t1 = t1 / t3 := by ring
  have h3 : (1 / t3) * t2 = t2 / t3 := by ring
  rw [h1, h2, h3]
  match_scalars <;> ring

private theorem w15_affine_cancel {X Y : V3} {mu lam h c t2 t3 : ℝ}
    (h1 : mu * c + lam * t3 = 0) :
    mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X := by
  have hh : mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X + (mu * c + lam * t3) • Y := by module
  rw [hh, h1, zero_smul, add_zero]

/-- w15: `OPPOSITE_SIDES_IMP_INTER` (local_lemmas.hl:6324): a point of the open
`vc`-cone and one of the opposite open half-plane force the segment `conv0 {a,b}`
to cross `aff {va, vb}`.  (LocalAuto14 verbatim.) -/
private theorem OPPOSITE_SIDES_IMP_INTER {va vb vc a b : V3}
    (hvab : va ≠ vb)
    (hd : Disjoint ({va, vb} : Set V3) ({vc} : Set V3))
    (ha : a ∈ affGt ({va, vb} : Set V3) ({vc} : Set V3))
    (hb : b ∈ affLt ({va, vb} : Set V3) ({vc} : Set V3)) :
    conv0_p2 ({a, b} : Set V3) ∩
      (affineSpan ℝ ({va, vb} : Set V3) : Set V3) ≠ ∅ := by
  have hvcbs : vc ∉ ({va, vb} : Set V3) := Set.disjoint_right.mp hd (Set.mem_singleton vc)
  have hvca : vc ≠ va := by
    intro h
    apply hvcbs
    rw [h]
    exact Set.mem_insert va {vb}
  have hvcb : vc ≠ vb := by
    intro h
    apply hvcbs
    rw [h]
    exact Set.mem_insert_of_mem va (Set.mem_singleton vb)
  obtain ⟨c, hc, h, hha⟩ :=
    (affGt_pair_iff (v0 := va) (v1 := vb) (x := vc) (y := a) hvab hvca hvcb).mp ha
  obtain ⟨t1, t2, t3, ht3, hsum, hbeq⟩ :
      ∃ t1 t2 t3 : ℝ, t3 < 0 ∧ t1 + t2 + t3 = 1 ∧
        b = t1 • va + t2 • vb + t3 • vc := by
    have h2 := hb
    rw [AFF_LT_2_1 hd, Set.mem_setOf_eq] at h2
    exact h2
  have haeq : a = (1 - c - h) • va + h • vb + c • vc := by
    have h2 : a = (a - va) + va := by abel
    rw [h2, hha]
    module
  have haeq' : a - va = h • (vb - va) + c • (vc - va) := by
    rw [hha, add_comm]
  have hbeq' : b - va = t2 • (vb - va) + t3 • (vc - va) := by
    have ht1 : t1 = 1 - t2 - t3 := by linarith
    rw [hbeq, ht1]
    module
  have hden : 0 < c - t3 := by linarith
  set lam : ℝ := c / (c - t3) with hlam
  set mu : ℝ := -t3 / (c - t3) with hmu
  have hmu_pos : 0 < mu := by rw [hmu]; exact div_pos (by linarith) hden
  have hlam_pos : 0 < lam := by rw [hlam]; exact div_pos hc hden
  have hsum' : mu + lam = 1 := by
    rw [hmu, hlam]; field_simp; ring
  have hkey : mu * c + lam * t3 = 0 := by
    rw [hmu, hlam]; field_simp; ring
  set p : V3 := mu • a + lam • b with hp
  have hconv : p ∈ conv0_p2 ({a, b} : Set V3) := by
    have h1 := IN_CONV0 (x := a) (y := b) (a := mu) (b := lam) hmu_pos hlam_pos
    rw [hsum', div_one, one_smul, ← hp] at h1
    exact h1
  have hpsub : p - va = (mu * h + lam * t2) • (vb - va) := by
    have h2 : mu • (a - va) + lam • (b - va) = mu • a + lam • b - (mu + lam) • va := by
      rw [smul_sub, smul_sub, add_smul]; abel
    have e1 : mu • a + lam • b - va = mu • (a - va) + lam • (b - va) := by
      rw [h2, hsum', one_smul]
    rw [hp, e1, haeq', hbeq', w15_affine_cancel hkey]
  have haff : p ∈ (affineSpan ℝ ({va, vb} : Set V3) : Set V3) := by
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨mu * h + lam * t2, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hpsub]
    abel
  exact Set.nonempty_iff_ne_empty.mp ⟨p, hconv, haff⟩

/-! ### §6 IN_V_IMP_AZIM_LESS_PI (LocalAuto9:1378 `_p2` verbatim) -/

/-- HOL `IN_V_IMP_AZIM_LESS_PI` (Local_lemmas.hl:6247): on a convex local
fan the azimuth from `v` to its rho-successor bounds by `pi` every azimuth
from `v`'s rho-successor to a fan vertex. -/
private theorem IN_V_IMP_AZIM_LESS_PI {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : convexLocalFan_p2 V E FF) (v : V3) (hv : v ∈ V) :
    ∀ w ∈ V, azim 0 v (rhoNode1_p2 FF v) w ≤ Real.pi := by
  obtain ⟨hlf, hconv⟩ := h
  have hpro := LOCAL_FAN_RHO_NODE_PROS2 hlf
  have hdart : (v, rhoNode1_p2 FF v) ∈ FF := hpro.2 v hv
  have hwedge := hconv (v, rhoNode1_p2 FF v) hdart
  have hcycPi : azim 0 v (rhoNode1_p2 FF v)
      (azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v)) ≤ Real.pi := by
    have h1 := hwedge.1
    rwa [LOFA_DETERMINE_AZIM_IN_FA hlf hdart] at h1
  intro w hwv
  have hmem : w ∈ wedgeGe_p2 0 v (rhoNode1_p2 FF v)
      (azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v)) := by
    have h2 : w ∈ wedgeInFanGe_p2 (v, rhoNode1_p2 FF v) E := hwedge.2 hwv
    rwa [DETERMINE_WEDGE_IN_FAN hlf hdart] at h2
  have hle : azim 0 v (rhoNode1_p2 FF v) w ≤ azim 0 v (rhoNode1_p2 FF v)
      (azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v)) := hmem.2
  exact hle.trans hcycPi

/-! ### §7 GATE-B MONO single-step trig core (LocalAuto35 GATE-B section verbatim;
private there, renamed `_p35` -> `_p2`).  `monoStepCore` isolates the wrap corner
`(azim = π, azim = 0)` as an explicit disjunct; `monoWindowNowrap` resolves it under
`hnowrap`, which the fan-side `w16_noWrap_p2` supplies below. -/


/-- Azimuth-of-axis-point vanishes (the collinear disjunct of `azim`). -/
private theorem azimAxis_p2 {a b x : V3} (h : Collinear3 0 a x) :
    azim 0 a b x = 0 := by
  rw [azim, if_pos (Or.inr h)]

/-- dot with a right smul factor (local bridge for the cross-pairing). -/
private theorem pmDotSmul_p2 (c : ℝ) (f g : Fin 3 → ℝ) :
    g ⬝ᵥ (c • f) = c * (g ⬝ᵥ f) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    ring

/-- Half-space bound at a dart (open-sector case; sin bridge). -/
private theorem pmCrossGe_p2 {y z x : V3} (hcolx : ¬ Collinear3 0 y x)
    (hnc : ¬ Collinear3 0 y z)
    (h0 : 0 ≤ azim 0 y z x) (hπ : azim 0 y z x ≤ Real.pi) :
    0 ≤ (crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  have h := cross_dot_fully_surrounded_ge_fan (x := 0) (v1 := y) (v := z) (u1 := x)
    hcolx hnc h0 hπ
  simpa [sub_zero] using h

/-- Half-space bound at a dart (combined, collinear fallback included):
every point whose azimuth from the dart lies in `[0, π]` sits in the closed
`{y × z ≥ 0}` half-space. -/
private theorem pmCrossGeAll_p2 {y z x : V3} (hvi0 : y ≠ 0)
    (hnc : ¬ Collinear3 0 y z)
    (h0 : 0 ≤ azim 0 y z x) (hπ : azim 0 y z x ≤ Real.pi) :
    0 ≤ (crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
  by_cases hcol : Collinear3 0 y x
  · obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := y) (w1 := x) hvi0).mp hcol
    have h2 : x - 0 = c • (y - 0) := hc
    simp only [sub_zero] at h2
    rw [show ((x : V3) : Fin 3 → ℝ) = c • ((y : V3) : Fin 3 → ℝ) from
      congrArg (fun w : V3 => (w : Fin 3 → ℝ)) h2, pmDotSmul_p2, dotProduct_comm,
      show crossProduct (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)
          = -(crossProduct (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)) from
        (cross_anticomm (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)).symm,
      dotProduct_neg, dot_cross_self (z : Fin 3 → ℝ) (y : Fin 3 → ℝ)]
    simp
  · exact pmCrossGe_p2 hcol hnc h0 hπ

/-- Triple product cyclic permutation (Mathlib
`triple_product_permutation` + `dotProduct_comm`). -/
private theorem pmTripleCyc_p2 (f g h : Fin 3 → ℝ) :
    (crossProduct f g) ⬝ᵥ h = (crossProduct g h) ⬝ᵥ f := by
  rw [dotProduct_comm (crossProduct f g) h, triple_product_permutation h f g,
    dotProduct_comm (crossProduct g h) f]

/-- FAN-free azimuth addition (`Kepler.Text.Fan.sum2_azim_fan` clone with the
`FAN x V E` hypothesis replaced by the three fan6-type non-collinearity
facts, which is all its proof consumes). -/
private theorem azimAddTriple_p2 {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hu : ¬ Collinear3 x v u) (h1 : ¬ Collinear3 x v w1) (h2 : ¬ Collinear3 x v w2)
    (hle : azim x v u w1 ≤ azim x v u w2) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr hxv)
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hu h1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hu h2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec h1 h2 hon hax hxv
  have hψu : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ2 : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hru hru2 (hzu.symm.trans hzu2)
  have hE2 : Complex.exp ((((ψ + azim x v u w1 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (((ψ' : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hr1 hr1' (hzw1.symm.trans hzw1')
  have hE1' : Complex.exp ((((ψ2 + azim x v u w2 : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ψ' + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) :=
    exp_pos_mul_eq hr2 hr2' (hzw2.symm.trans hzw2')
  rw [exp_add_I, exp_add_I] at hE1'
  rw [exp_add_I] at hE2
  rw [hψu.symm] at hE1'
  rw [← hE2] at hE1'
  have hE3 : Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
    have hkey : Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim x v u w2 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((azim x v u w1 + azim x v w1 w2 : ℝ) : ℂ)) * Complex.I) := by
      rw [hE1', mul_assoc, ← exp_add_I]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE3
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hc3 : azim x v u w2
      = azim x v u w1 + azim x v w1 w2 + (n:ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hr1'0 : (0:ℝ) ≤ azim x v u w1 := azim_nonneg x v u w1
  have hr2'0 : (0:ℝ) ≤ azim x v w1 w2 := azim_nonneg x v w1 w2
  have hr3'0 : (0:ℝ) ≤ azim x v u w2 := azim_nonneg x v u w2
  have hr3'1 : azim x v u w2 < 2 * Real.pi := azim_lt_two_pi x v u w2
  have hφ1 : azim x v w1 w2 < 2 * Real.pi := azim_lt_two_pi x v w1 w2
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hnpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (n : ℤ) ≤ -1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by
      have := (by omega : (n : ℤ) ≥ 1)
      exact_mod_cast this
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith

/-- **GATE-B 三角核心（MONO_AZIM 单步，回卷隔离）** — 参考射线 `b`、扇轴
`(0, u)`：若 `x` 的方位不超过 `y` 的方位则左支；否则 `azimAddTriple_p2`
在假定窗口内加出步差 `δ = azim 0 u y x ∈ (0, π]`，`JBDNJJB` 给
`sin δ = t * ((u × y) ⬝ x)`（`t > 0`），对角楔 `x → y` 对 `u` 的 `≤ π`
半支经 `pmCrossGeAll_p2` 与循环置换反号夹出 `(u × y) ⬝ x = 0`，故
`sin δ = 0`、`δ = π`，即 `(va, vb) = (π, 0)`。HOL 原路在这一点进入
KCHMAMG 平面化（ll:6790-6927）导出矛盾；此处如实保留为析取支。 -/
theorem monoStepCore_p2 {u b x y : V3} (hu0 : u ≠ 0)
    (hb : ¬ Collinear3 0 u b) (hx : ¬ Collinear3 0 u x)
    (hy : ¬ Collinear3 0 u y) (hx0 : x ≠ 0) (hncxy : ¬ Collinear3 0 x y)
    (hvapi : azim 0 u b x ≤ Real.pi)
    (hdart0 : 0 ≤ azim 0 x y u) (hdartpi : azim 0 x y u ≤ Real.pi)
    (hvb0 : 0 ≤ azim 0 u b y) :
    azim 0 u b x ≤ azim 0 u b y ∨
      (azim 0 u b x = Real.pi ∧ azim 0 u b y = 0) := by
  rcases lt_or_ge (azim 0 u b y) (azim 0 u b x) with hlt | hle
  · right
    have hadd : azim 0 u b x = azim 0 u b y + azim 0 u y x :=
      azimAddTriple_p2 (x := (0 : V3)) (v := u) (u := b) (w1 := y) (w2 := x)
        hu0 hb hy hx hlt.le
    have hδpos : 0 < azim 0 u y x := by linarith
    have hδpi : azim 0 u y x ≤ Real.pi := by linarith
    -- JBDNJJB 桥：sin δ = t * ((u × y) ⬝ x)，t > 0
    obtain ⟨t, ht, hsin⟩ := JBDNJJB (u := u) (v := y) (w := x) hy hx
    -- 对角楔半空间（pmCrossGeAll 于 dart (x, y) 对 u）
    have hd := pmCrossGeAll_p2 (y := x) (z := y) (x := u) hx0 hncxy hdart0 hdartpi
    -- 循环置换 + 反交换：(u × y) ⬝ x = -((x × y) ⬝ u)
    have hcyc : (crossProduct (u : Fin 3 → ℝ) (y : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ)
        = -((crossProduct (x : Fin 3 → ℝ) (y : Fin 3 → ℝ)) ⬝ᵥ (u : Fin 3 → ℝ)) := by
      rw [pmTripleCyc_p2, ← cross_anticomm (x : Fin 3 → ℝ) (y : Fin 3 → ℝ),
        dotProduct_comm, dotProduct_neg, dotProduct_comm]
    have hTge : (0:ℝ) ≤ (crossProduct (u : Fin 3 → ℝ) (y : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) := by
      by_contra hneg
      push_neg at hneg
      have hsp : (0:ℝ) ≤ Real.sin (azim 0 u y x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδpos.le hδpi
      rw [hsin] at hsp
      have hprod : t * ((crossProduct (u : Fin 3 → ℝ) (y : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ)) < 0 :=
        mul_neg_of_pos_of_neg ht hneg
      linarith
    have hT0 : (crossProduct (u : Fin 3 → ℝ) (y : Fin 3 → ℝ)) ⬝ᵥ (x : Fin 3 → ℝ) = 0 :=
      le_antisymm (by rw [hcyc]; linarith) hTge
    have hsin0 : Real.sin (azim 0 u y x) = 0 := by
      rw [hsin, hT0]; ring
    have hδeq : azim 0 u y x = Real.pi := by
      rcases eq_or_lt_of_le hδpi with h | hlt2
      · exact h
      · exact absurd (Real.sin_pos_of_pos_of_lt_pi hδpos hlt2)
          (by rw [hsin0]; simp)
    have hvaeq : azim 0 u b x = Real.pi := by
      rw [hadd, hδeq]; linarith
    have hsub : azim 0 u b y = azim 0 u b x - azim 0 u y x := by linarith
    rw [hsub, hvaeq, hδeq]
    simp
  · exact Or.inl hle

theorem monoStepOrbit_p2 (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
    (hr0 : ρ 0 = v0) (hv0 : v0 ≠ 0) (hb : ¬ Collinear3 0 v0 b)
    (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 v0 (ρ i))
    (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
    (hbnds : ∀ i, 0 < i → i < k → 0 ≤ azim 0 v0 b (ρ i) ∧
      azim 0 v0 b (ρ i) ≤ Real.pi)
    (hdart : ∀ i, i + 1 < k → ¬ Collinear3 0 (ρ i) (ρ (i + 1)) ∧
      0 ≤ azim 0 (ρ i) (ρ (i + 1)) v0 ∧
      azim 0 (ρ i) (ρ (i + 1)) v0 ≤ Real.pi) (i : ℕ) (hik : i + 1 < k) :
    azim 0 v0 b (ρ i) ≤ azim 0 v0 b (ρ (i + 1)) ∨
      (azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0) := by
  rcases Nat.lt_or_ge i 1 with hi0 | hi1
  · have hi : i = 0 := Nat.lt_one_iff.mp hi0
    left
    rw [hi, hr0, azimAxis_p2 (collinear3_pair_right (v0 := (0 : V3))
      (v1 := v0) (x := v0) rfl)]
    exact azim_nonneg 0 v0 b _
  · exact monoStepCore_p2 (u := v0) (b := b) (x := ρ i) (y := ρ (i + 1))
      hv0 hb (hvx i hi1 (lt_of_le_of_lt (Nat.le_succ i) hik))
      (hvx (i + 1) (Nat.succ_pos i) hik) (hvx0 i hi1 (lt_of_le_of_lt (Nat.le_succ i) hik))
      (hdart i hik).1 (hbnds i hi1 (lt_of_le_of_lt (Nat.le_succ i) hik)).2
      (hdart i hik).2.1 (hdart i hik).2.2 (hbnds (i + 1) (Nat.succ_pos i) hik).1

theorem monoWindowNowrap_p2 (k : ℕ) {v0 b : V3} (ρ : ℕ → V3)
    (hr0 : ρ 0 = v0) (hv0 : v0 ≠ 0) (hb : ¬ Collinear3 0 v0 b)
    (hvx : ∀ i, 0 < i → i < k → ¬ Collinear3 0 v0 (ρ i))
    (hvx0 : ∀ i, 0 < i → i < k → ρ i ≠ 0)
    (hbnds : ∀ i, 0 < i → i < k → 0 ≤ azim 0 v0 b (ρ i) ∧
      azim 0 v0 b (ρ i) ≤ Real.pi)
    (hdart : ∀ i, i + 1 < k → ¬ Collinear3 0 (ρ i) (ρ (i + 1)) ∧
      0 ≤ azim 0 (ρ i) (ρ (i + 1)) v0 ∧
      azim 0 (ρ i) (ρ (i + 1)) v0 ≤ Real.pi)
    (hnowrap : ∀ i, i + 1 < k →
      ¬(azim 0 v0 b (ρ i) = Real.pi ∧ azim 0 v0 b (ρ (i + 1)) = 0))
    {i j : ℕ} (hij : i < j) (hjk : j < k) :
    azim 0 v0 b (ρ i) ≤ azim 0 v0 b (ρ j) := by
  have hstep : ∀ m, m + 1 < k → azim 0 v0 b (ρ m) ≤ azim 0 v0 b (ρ (m + 1)) := by
    intro m hm
    rcases monoStepOrbit_p2 k ρ hr0 hv0 hb hvx hvx0 hbnds hdart m hm with h | h
    · exact h
    · exact absurd h (hnowrap m hm)
  -- 窗口归纳（NEXT_PRO_IMP_ALLS_STRICT 骨架的泛射线内联；b 与 ρ 1 的
  -- 高阶合一在 term-mode 会卡 whnf，故不走 MONO_AZIM_AS_BTA_I_p35 装配）
  have key : ∀ d m, m + d < k → azim 0 v0 b (ρ m) ≤ azim 0 v0 b (ρ (m + d)) := by
    intro d
    induction d with
    | zero => exact fun _ _ => le_refl _
    | succ n ihn =>
        intro m hmk
        have h1 := hstep m (by omega)
        have h2 := ihn (m + 1) (by omega)
        rw [show m + (n + 1) = m + 1 + n from by omega]
        exact h1.trans h2
  have hji : i ≤ j := le_of_lt hij
  have hd : i + (j - i) = j := Nat.add_sub_cancel' hji
  rw [← hd]
  exact key (j - i) i (by rw [hd]; exact hjk)
/-! ### §8 wrap-corner exclusion (LocalAuto14 §5 verbatim, `_p2` hypothesis;
`LocalFan`→`localFan_p2`/`ConvexLocalFan`→`convexLocalFan_p2` transport calls dropped). -/

/-- HOL `MONO_AZIM_AS_BTA_I` wrap corner is impossible: no consecutive orbit
pair has azimuths `(π, 0)` around the axis `(0, v0)` from the reference `vv 1`.
KCHMAMG / `SEQUENCE_OF_RHO_NODE_IS_SUC` branch of local_lemmas.hl:6740-6927. -/
theorem w16_noWrap_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v0 : V3} {vv : ℕ → V3} {k i : ℕ}
    (hcl : convexLocalFan_p2 V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
    (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v0 = vv n)
    (hi : i + 1 < k) :
    ¬(azim 0 v0 (vv 1) (vv i) = Real.pi ∧ azim 0 v0 (vv 1) (vv (i + 1)) = 0) := by
  intro ⟨hva, hvb⟩
  have hlf2 : localFan_p2 V E FF := hcl.1
  have hclf2 : convexLocalFan_p2 V E FF := hcl
  have hmemV : ∀ n, (rhoNode1_p2 FF)^[n] v0 ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv0
  have hmemvv : ∀ n, vv n ∈ V := fun n => by rw [← hiter n]; exact hmemV n
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := hlf2
  have hv0ne : v0 ≠ 0 := FAN_IMP_V_DIFF hfan v0 hv0
  have hv0ne' : (0:V3) ≠ v0 := Ne.symm hv0ne
  have hvv0 : vv 0 = v0 := (hiter 0).symm
  -- i ≥ 1
  have hi0 : 0 < i := by
    by_contra hcon
    push_neg at hcon
    have hi_eq : i = 0 := Nat.le_zero.mp hcon
    rw [hi_eq] at hva
    have hz : azim 0 v0 (vv 1) (vv 0) = 0 := by
      rw [hvv0, azim, if_pos]
      exact Or.inr (collinear3_pair_right (v0 := (0:V3)) (v1 := v0) (x := v0) rfl)
    rw [hz] at hva
    exact absurd hva.symm Real.pi_pos.ne'
  -- non-collinearity
  have hne1 : vv 1 ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 1 (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1_p2 FF)^[1] v0 ≠ (rhoNode1_p2 FF)^[0] v0 := h2
    rw [hiter 1, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnei : vv i ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 i (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1_p2 FF)^[i] v0 ≠ (rhoNode1_p2 FF)^[0] v0 := h2
    rw [hiter i, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnei1 : vv (i + 1) ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 (i + 1) (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1_p2 FF)^[i + 1] v0 ≠ (rhoNode1_p2 FF)^[0] v0 := h2
    rw [hiter (i + 1), hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnc1 : ¬ Collinear3 0 v0 (vv 1) := hcol (vv 1) (hmemvv 1) hne1
  have hnci : ¬ Collinear3 0 v0 (vv i) := hcol (vv i) (hmemvv i) hnei
  have hnci1 : ¬ Collinear3 0 v0 (vv (i + 1)) := hcol (vv (i + 1)) (hmemvv (i + 1)) hnei1
  have h1ne0 : vv 1 ≠ 0 := FAN_IMP_V_DIFF hfan (vv 1) (hmemvv 1)
  -- AZIM_EQ_0_ALT / AZIM_EQ_PI_ALT
  have hgt : vv (i + 1) ∈ affGt ({0, v0} : Set V3) ({vv 1} : Set V3) :=
    (azim_eq_zero_iff_alt (v0 := 0) (v1 := v0) (w := vv 1) (x := vv (i + 1))
      hnc1 hnci1).mp hvb
  have hlt : vv i ∈ affLt ({0, v0} : Set V3) ({vv 1} : Set V3) :=
    (AZIM_EQ_PI_ALT (u := v0) (v := vv 1) (w := vv i) hnc1 hnci).mp hva
  -- disjointness
  have hdis : Disjoint ({0, v0} : Set V3) ({vv 1} : Set V3) := by
    rw [Set.disjoint_singleton_right]
    intro hmem
    rcases Set.mem_insert_iff.mp hmem with hh | hh
    · refine hnc1 ?_
      rw [hh]
      exact collinear3_pair_left (v0 := (0:V3)) (v1 := v0) (x := 0) rfl
    · refine hnc1 ?_
      rw [hh]
      exact collinear3_pair_right (v0 := (0:V3)) (v1 := v0) (x := v0) rfl
  -- opposite sides
  have hop := OPPOSITE_SIDES_IMP_INTER (va := 0) (vb := v0) (vc := vv 1)
    (a := vv (i + 1)) (b := vv i) hv0ne' hdis hgt hlt
  obtain ⟨p, hpconv, hpspan⟩ := Set.nonempty_iff_ne_empty.mpr hop
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hpspan
  have hpt : p = t • v0 := by rw [← ht]; simp [AffineMap.lineMap_apply]
  -- the dart (vv i, vv (i+1)) and its edge
  have hrn : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
    rw [← hiter (i + 1), show i + 1 = Nat.succ i from rfl,
      Function.iterate_succ_apply', hiter i]
  have hFFi : (vv i, vv (i + 1)) ∈ FF := by
    have h1 : (vv i, rhoNode1_p2 FF (vv i)) ∈ FF :=
      (LOCAL_FAN_RHO_NODE_PROS2 hclf2.1).2 (vv i) (hmemvv i)
    have h2 : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
      show rhoNode1_p2 FF (vv i) = vv (i + 1)
      exact hrn
    rwa [h2] at h1
  have hedge : ({vv i, vv (i + 1)} : Set V3) ∈ E :=
    (LOCAL_FAN_IN_FF_IN_ORD_PAIRS2 hclf2.1 hFFi hFFi).1
  -- split on the crossing point side
  by_cases ht0 : 0 ≤ t
  · -- Branch A: p on the v0 ray -> p = 0 -> collinear
    have hpge : p ∈ affGe ({0} : Set V3) ({v0} : Set V3) := by
      rw [hpt]; exact w16_smul_mem_affGe hv0ne ht0
    have hpge2 : p ∈ affGe ({0} : Set V3) ({vv (i + 1), vv i} : Set V3) :=
      CONV_SUBSET_AFF_GE (S := ({0} : Set V3)) (SS := ({vv (i + 1), vv i} : Set V3))
        (by simp) (by simp) (CONV02_SU_CONV2 (vv (i + 1)) (vv i) hpconv)
    have h77 := hfan.2.2.2.2.2 ({v0} : Set V3) (Or.inr ⟨v0, hv0, rfl⟩)
      ({vv i, vv (i + 1)} : Set V3) (Or.inl hedge)
    have hinter : ({v0} : Set V3) ∩ ({vv i, vv (i + 1)} : Set V3) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_singleton_iff] at hz1
      subst hz1
      rcases Set.mem_insert_iff.mp hz2 with hh | hh
      · exact hnei hh.symm
      · exact hnei1 hh.symm
    have hp0 : p ∈ ({0} : Set V3) := by
      have hmem : p ∈ affGe ({0} : Set V3)
          (({v0} : Set V3) ∩ ({vv i, vv (i + 1)} : Set V3)) := by
        rw [← h77]
        refine ⟨hpge, ?_⟩
        rw [show ({vv i, vv (i + 1)} : Set V3) = ({vv (i + 1), vv i} : Set V3) by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
        exact hpge2
      rwa [hinter, w16_affGe_empty_singleton] at hmem
    have hpzero : p = 0 := by simpa using hp0
    have h0conv : (0:V3) ∈ convexHull ℝ ({vv (i + 1), vv i} : Set V3) := by
      rw [← hpzero]
      exact CONV02_SU_CONV2 (vv (i + 1)) (vv i) hpconv
    have h0aff : (0:V3) ∈ (affineSpan ℝ ({vv (i + 1), vv i} : Set V3) : Set V3) :=
      convexHull_subset_affineSpan _ h0conv
    have hcol0 : Collinear ℝ ({0, vv i, vv (i + 1)} : Set V3) := by
      have hc : Collinear ℝ ({vv (i + 1), vv i, 0} : Set V3) :=
        (collinear_triple_iff (x := vv (i + 1)) (v := vv i) (u := 0)).mpr (Or.inl h0aff)
      have hset : ({0, vv i, vv (i + 1)} : Set V3) = ({vv (i + 1), vv i, 0} : Set V3) := by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset]
    have hnc2 := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hclf2.1 (v := vv i) (hmemvv i)
    have hnc2' : ¬ Collinear ℝ ({0, vv i, rhoNode1_p2 FF (vv i)} : Set V3) := hnc2
    rw [hrn] at hnc2'
    exact hnc2' hcol0
  · -- Branch B: p on the opposite ray -> circular -> KCHMAMG -> SEQUENCE
    push_neg at ht0
    have hplt : p ∈ affLt ({0} : Set V3) ({v0} : Set V3) := by
      rw [hpt]; exact w16_smul_mem_affLt hv0ne ht0
    have h0S : (0:V3) ∉ ({vv (i + 1), vv i} : Set V3) := by
      intro hmem
      rcases Set.mem_insert_iff.mp hmem with hh | hh
      · have hz : vv (i + 1) = 0 := hh.symm
        exact FAN_IMP_V_DIFF hfan (vv (i + 1)) (hmemvv (i + 1)) hz
      · have hz : vv i = 0 := (Set.mem_singleton_iff.mp hh).symm
        exact FAN_IMP_V_DIFF hfan (vv i) (hmemvv i) hz
    have hpgt : p ∈ affGt ({0} : Set V3) ({vv (i + 1), vv i} : Set V3) :=
      w16_affGt_empty_subset h0S hpconv
    have hcirc : circular_p2 V E := by
      refine ⟨vv (i + 1), vv i, v0, ?_, hv0, ?_⟩
      · have hEq : ({vv (i + 1), vv i} : Set V3) = ({vv i, vv (i + 1)} : Set V3) := by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hEq]; exact hedge
      · intro hempty
        have hmem : p ∈ affGt ({0} : Set V3) ({vv (i + 1), vv i} : Set V3) ∩
            affLt ({0} : Set V3) ({v0} : Set V3) := Set.mem_inter hpgt hplt
        rw [hempty] at hmem
        exact hmem
    obtain ⟨-, A, hAplane, hA0, hAsub, -⟩ := KCHMAMG hclf2 hcirc
    -- SEQUENCE_OF_RHO_NODE_IS_SUC at v0, window i+1
    have hUsub : ({(rhoNode1_p2 FF)^[n] v0 | n ≤ i + 1} : Set V3) ⊆ A := by
      rintro z ⟨n, hn, rfl⟩
      exact hAsub (hmemV n)
    have hseq := SEQUENCE_OF_RHO_NODE_IS_SUC (h := hclf2.1) (v := v0) (hv := hv0)
      (l := i + 1) (U := {(rhoNode1_p2 FF)^[n] v0 | n ≤ i + 1}) (P := A)
      rfl hAplane hA0 hUsub (e := cross3 v0 (rhoNode1_p2 FF v0)) rfl
    have hyU : v0 ∈ ({(rhoNode1_p2 FF)^[n] v0 | n ≤ i + 1} : Set V3) :=
      ⟨0, by omega, by simp⟩
    have hstrict := hseq (vv i) i (hiter i).symm (by omega) v0 hyU hnei.symm
      (by
        show v0 ≠ rhoNode1_p2 FF (vv i)
        rw [hrn]
        exact hnei1.symm)
    -- rewrite the reference e = v0 × vv 1
    have he1 : rhoNode1_p2 FF v0 = vv 1 := by
      rw [← hiter 1, show (1:ℕ) = Nat.succ 0 from rfl,
        Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [he1] at hstrict
    have hrn2 : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
      show rhoNode1_p2 FF (vv i) = vv (i + 1)
      exact hrn
    rw [hrn2] at hstrict
    -- coefficient representations
    obtain ⟨c, hcpos, hcoef, hrepr⟩ :=
      (affGt_pair_iff (v0 := (0:V3)) (v1 := v0) (x := vv 1) (y := vv (i + 1))
        hv0ne' h1ne0 hne1).mp hgt
    obtain ⟨t1, t2, t3, ht3, hsum3, hrepr3⟩ := by
      have h2 := hlt
      rw [AFF_LT_2_1 (x := (0:V3)) (v := v0) (w := vv 1) hdis, Set.mem_setOf_eq] at h2
      exact h2
    have hrepr' : vv (i + 1) = c • vv 1 + hcoef • v0 := by
      simpa only [sub_zero] using hrepr
    have hrepr3' : vv i = t2 • v0 + t3 • vv 1 := by
      simpa only [smul_zero, zero_add] using hrepr3
    -- triple products
    have hene : cross3 v0 (vv 1) ≠ 0 := w16_cross3_ne hnc1
    have hposident : 0 < (cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv 1 := by
      rw [w16_triple_identity]
      exact w16_dot3_self_pos hene
    have hsign1 : 0 < (cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv (i + 1) := by
      have hsplit : (cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv (i + 1)
          = c * ((cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv 1) := by
        rw [hrepr']
        simp only [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul,
          smul_eq_mul, w16_cross3_dotR]
        ring
      rw [hsplit]
      exact mul_pos hcpos hposident
    have hsign2 : (cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv i < 0 := by
      have hsplit : (cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv i
          = t3 * ((cross3 (cross3 v0 (vv 1)) v0) ⬝ᵥ vv 1) := by
        rw [hrepr3']
        simp only [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul,
          smul_eq_mul, w16_cross3_dotR]
        ring
      rw [hsplit]
      exact mul_neg_of_neg_of_pos ht3 hposident
    -- non-collinearity for JBDNJJB
    have hncev0 : ¬ Collinear3 0 (cross3 v0 (vv 1)) v0 := by
      intro hc
      obtain ⟨s, hs⟩ := w16_smul_of_collinear0 hene hc
      have hdot0 : v0 ⬝ᵥ (cross3 v0 (vv 1)) = 0 := by
        rw [w16_dot3_comm]; exact w16_cross3_dotL v0 (vv 1)
      have hdot : s * ((cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1))) = 0 := by
        rw [← w16_dot3_smul_left, ← hs]
        exact hdot0
      have hdd : (0:ℝ) < (cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1)) := w16_dot3_self_pos hene
      have hs0 : s = 0 := (mul_eq_zero.mp hdot).resolve_right hdd.ne'
      rw [hs0, zero_smul] at hs
      exact hv0ne hs
    have hperp : (cross3 v0 (vv 1)) ⬝ᵥ vv i = 0 := by
      rw [hrepr3']
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul,
        smul_eq_mul, w16_cross3_dotR, w16_cross3_dotL]
      ring
    have hperp1 : (cross3 v0 (vv 1)) ⬝ᵥ vv (i + 1) = 0 := by
      rw [hrepr']
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul,
        smul_eq_mul, w16_cross3_dotR, w16_cross3_dotL]
      ring
    have hncei : ¬ Collinear3 0 (cross3 v0 (vv 1)) (vv i) := by
      intro hc
      obtain ⟨s, hs⟩ := w16_smul_of_collinear0 hene hc
      have hdd : (0:ℝ) < (cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1)) := w16_dot3_self_pos hene
      have hzero : s * ((cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1))) = 0 := by
        rw [← w16_dot3_smul_left, ← hs, w16_dot3_comm]
        exact hperp
      have hs0 : s = 0 := (mul_eq_zero.mp hzero).resolve_right hdd.ne'
      rw [hs0, zero_smul] at hs
      exact FAN_IMP_V_DIFF hfan (vv i) (hmemvv i) hs
    have hncei1 : ¬ Collinear3 0 (cross3 v0 (vv 1)) (vv (i + 1)) := by
      intro hc
      obtain ⟨s, hs⟩ := w16_smul_of_collinear0 hene hc
      have hdd : (0:ℝ) < (cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1)) := w16_dot3_self_pos hene
      have hzero : s * ((cross3 v0 (vv 1)) ⬝ᵥ (cross3 v0 (vv 1))) = 0 := by
        rw [← w16_dot3_smul_left, ← hs, w16_dot3_comm]
        exact hperp1
      have hs0 : s = 0 := (mul_eq_zero.mp hzero).resolve_right hdd.ne'
      rw [hs0, zero_smul] at hs
      exact FAN_IMP_V_DIFF hfan (vv (i + 1)) (hmemvv (i + 1)) hs
    -- sine signs
    obtain ⟨s1, hs1pos, hs1⟩ := JBDNJJB (u := cross3 v0 (vv 1)) (v := v0) (w := vv i)
      hncev0 hncei
    obtain ⟨s2, hs2pos, hs2⟩ := JBDNJJB (u := cross3 v0 (vv 1)) (v := v0)
      (w := vv (i + 1)) hncev0 hncei1
    have hsin1 : Real.sin (azim 0 (cross3 v0 (vv 1)) v0 (vv i)) < 0 := by
      rw [hs1, ← w16_cross3_dot_eq]
      exact mul_neg_of_pos_of_neg hs1pos hsign2
    have hsin2 : 0 < Real.sin (azim 0 (cross3 v0 (vv 1)) v0 (vv (i + 1))) := by
      rw [hs2, ← w16_cross3_dot_eq]
      exact mul_pos hs2pos hsign1
    have hpi1 : Real.pi < azim 0 (cross3 v0 (vv 1)) v0 (vv i) :=
      (SIN_AZIM_NEG_PI_LT 0 (cross3 v0 (vv 1)) v0 (vv i)).mp hsin1
    have hpi2 : Real.pi < azim 0 (cross3 v0 (vv 1)) v0 (vv (i + 1)) :=
      lt_trans hpi1 hstrict
    have hsin2' : Real.sin (azim 0 (cross3 v0 (vv 1)) v0 (vv (i + 1))) < 0 :=
      (SIN_AZIM_NEG_PI_LT 0 (cross3 v0 (vv 1)) v0 (vv (i + 1))).mpr hpi2
    linarith [hsin2]
/-! ### §9 unconditional MONO_AZIM_AS_BTA_I at `_p2` (LocalAuto14 §6 verbatim;
per-step trig = `monoWindowNowrap_p2`, wrap corner = `w16_noWrap_p2`). -/

/-- HOL `MONO_AZIM_AS_BTA_I` (local_lemmas.hl:6448), **unconditional form**:
the orbit-window azimuth sequence is monotone.  The per-step trig is the
LA35 `monoStepOrbit_p2` disjunction; its wrap corner `(π, 0)` is killed by
`w16_noWrap_p2`. -/
theorem MONO_AZIM_AS_BTA_I_p2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hcl : convexLocalFan_p2 V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
    (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ i, (rhoNode1_p2 FF)^[i] v0 = vv i)
    (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i) :
    ∀ i j, i < j → j < k → bta i ≤ bta j := by
  intro i j hij hjk
  have hlf2 : localFan_p2 V E FF := hcl.1
  have hclf2 : convexLocalFan_p2 V E FF := hcl
  have hmemvv : ∀ n, vv n ∈ V := fun n => by
    rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv0 n
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := hlf2
  have hv0ne : v0 ≠ 0 := FAN_IMP_V_DIFF hfan v0 hv0
  have hvv0 : vv 0 = v0 := (hiter 0).symm
  have hr0 : rhoNode1_p2 FF v0 = vv 1 := by
    show rhoNode1_p2 FF v0 = vv 1
    rw [← hiter 1, show (1:ℕ) = Nat.succ 0 from rfl,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
  have hne1 : vv 1 ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 1 (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1_p2 FF)^[1] v0 ≠ (rhoNode1_p2 FF)^[0] v0 := h2
    rw [hiter 1, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hb : ¬ Collinear3 0 v0 (vv 1) := hcol (vv 1) (hmemvv 1) hne1
  have hvx : ∀ m, 0 < m → m < k → ¬ Collinear3 0 v0 (vv m) := by
    intro m hm0 hmk
    refine hcol (vv m) (hmemvv m) ?_
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 m hm0 (by rw [hk]; exact hmk)
    have h2' : (rhoNode1_p2 FF)^[m] v0 ≠ (rhoNode1_p2 FF)^[0] v0 := h2
    rw [hiter m, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hvx0 : ∀ m, 0 < m → m < k → vv m ≠ 0 :=
    fun m _ _ => FAN_IMP_V_DIFF hfan (vv m) (hmemvv m)
  have hbnds : ∀ m, 0 < m → m < k → 0 ≤ azim 0 v0 (vv 1) (vv m) ∧
      azim 0 v0 (vv 1) (vv m) ≤ Real.pi := by
    intro m _ _
    refine ⟨azim_nonneg _ _ _ _, ?_⟩
    have h1 := IN_V_IMP_AZIM_LESS_PI hclf2 v0 hv0 (vv m) (hmemvv m)
    rwa [hr0] at h1
  have hdart : ∀ m, m + 1 < k → ¬ Collinear3 0 (vv m) (vv (m + 1)) ∧
      0 ≤ azim 0 (vv m) (vv (m + 1)) v0 ∧
      azim 0 (vv m) (vv (m + 1)) v0 ≤ Real.pi := by
    intro m hmk
    have hrn : rhoNode1_p2 FF (vv m) = vv (m + 1) := by
      rw [← hiter (m + 1), show m + 1 = Nat.succ m from rfl,
        Function.iterate_succ_apply', hiter m]
    have hnc := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hclf2.1 (v := vv m) (hmemvv m)
    have hnc' : ¬ Collinear ℝ ({0, vv m, rhoNode1_p2 FF (vv m)} : Set V3) := hnc
    rw [hrn] at hnc'
    refine ⟨hnc', azim_nonneg _ _ _ _, ?_⟩
    have h1 := IN_V_IMP_AZIM_LESS_PI hclf2 (vv m) (hmemvv m) v0 hv0
    have h1' : azim 0 (vv m) (rhoNode1_p2 FF (vv m)) v0 ≤ Real.pi := h1
    rwa [hrn] at h1'
  have hnowrap : ∀ m, m + 1 < k →
      ¬(azim 0 v0 (vv 1) (vv m) = Real.pi ∧ azim 0 v0 (vv 1) (vv (m + 1)) = 0) :=
    fun m hmk => w16_noWrap_p2 hcl hv0 hk hcol hiter hmk
  have hmono := monoWindowNowrap_p2 (k := k) (v0 := v0) (b := vv 1) (ρ := vv)
    hvv0 hv0ne hb hvx hvx0 hbnds hdart hnowrap hij hjk
  rw [← hbta i, ← hbta j]
  exact hmono
/-- Orbit-length bookkeeping for the half circle (local copy of
`CARD_V_TWO_HAFL_CIRCLE`, declared later in this file). -/
private theorem w4c_card_two_hafl (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w) (n n' : ℕ) (hn : (rhoNode1_p2 FF)^[n] v = w)
    (hn' : (rhoNode1_p2 FF)^[n'] w = v) (hnc : n < V.ncard) (hn'c : n' < V.ncard) :
    n + n' = V.ncard := by
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

/-- Clean `fv` enumeration (local copy of `DETERMINE_FV2`, declared later in
this file). -/
private theorem w4c_determine_fv2 (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V)
    (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hn : n < V.ncard) (hw : (rhoNode1_p2 FF)^[n] v = w) :
    fv = insert (w, v) {p | ∃ m : ℕ, m < n ∧
      p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
  have hwV : w ∈ V := hw ▸ LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  have hFV := DETERMINE_FV h hv hwV hvw hcol hsub HS hHS hfv
  have hset : {p : V3 × V3 | ∃ n₀ : ℕ,
      (∀ m : ℕ, m < n₀ + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
        p = ((rhoNode1_p2 FF)^[n₀] v, (rhoNode1_p2 FF)^[n₀ + 1] v)}
      = {p : V3 × V3 | ∃ m : ℕ, m < n ∧
        p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n₀, hn₀c, hn₀p⟩ := hp
      have hn₀lt : n₀ < n := by
        by_contra hle
        exact hn₀c n (by omega) hw
      exact ⟨n₀, hn₀lt, hn₀p⟩
    · intro hp
      obtain ⟨m, hm, hmp⟩ := hp
      refine ⟨m, ?_, hmp⟩
      intro m' hm' hmeq
      exact LOFA_IMP_DIS_ELMS23 h hv m' n (by omega) hn (hw.trans hmeq.symm)
  rw [hFV, hset]

/-- `azim` vanishes when the last point is the axis vertex. -/
private theorem w4c_azim_vertex_last (x v u : V3) : azim x v u v = 0 := by
  rw [azim]
  exact if_pos (Or.inr (by
    have h : ({x, v, v} : Set V3) = {x, v} := by ext z; simp [or_assoc]
    rw [Collinear3, h]
    exact collinear_pair ℝ x v))

/-- Slice-dart convexity interface: once the two slice neighbours of a dart
`(a,b)` are identified as `b = rho_fv a`, `c = ivs_fv a` and the azimuth
bounds are available, both `convex_local_fan` conjuncts at that dart follow. -/
private theorem w4c_slice_dart_convex {v w : V3} {fv : Set (V3 × V3)} {a b c : V3}
    (hLF : localFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv)
    (hd : (a, b) ∈ fv) (hd' : (c, a) ∈ fv)
    (hpi : azim 0 a b c ≤ Real.pi)
    (hle : ∀ z ∈ vPrime_p2 V fv, azim 0 a b z ≤ azim 0 a b c) :
    azimInFan_p2 (a, b) (ePrime_p2 (E ∪ {{v, w}}) fv) ≤ Real.pi ∧
      vPrime_p2 V fv ⊆ wedgeInFanGe_p2 (a, b) (ePrime_p2 (E ∪ {{v, w}}) fv) := by
  have ha : a ∈ vPrime_p2 V fv := (LOCAL_FAN_IMP_IN_V hLF hd hd).1
  have hrho : rhoNode1_p2 fv a = b := DETER_RHO_NODE hLF hd
  have hivs : ivsRhoNode1_p2 fv a = c := IVS_RHO_NODE1_DETE hLF hd'
  have hazim : azimInFan_p2 (a, b) (ePrime_p2 (E ∪ {{v, w}}) fv) = azim 0 a b c := by
    rw [← hrho, AZIM_IN_FAN_RHOND_IVS_RHOND hLF ha, hivs]
  have hwedge : wedgeInFanGe_p2 (a, b) (ePrime_p2 (E ∪ {{v, w}}) fv) = wedgeGe_p2 0 a b c := by
    rw [← hrho, WEDGE_IN_FAN_RHOND_IVS_RHOND hLF ha, hivs]
  constructor
  · rw [hazim]
    exact hpi
  · rw [hwedge]
    intro z hz
    simp only [wedgeGe_p2, Set.mem_setOf_eq]
    exact ⟨azim_nonneg 0 a b z, hle z hz⟩

/-- HOL `COVEX_OF_LOFA_HALF_CIRCLE` (local_lemmas1.hl:3973) — giant. -/
theorem COVEX_OF_LOFA_HALF_CIRCLE (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v)) :
    convexLocalFan_p2 (vPrime_p2 V fv) (ePrime_p2 (E ∪ {{v, w}}) fv) fv := by
  obtain ⟨n, hnlt, hnv, -⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0, Function.iterate_zero] at hnv
      exact absurd hnv hvw
    · exact hp
  obtain ⟨n', hn'lt, hn'w, -⟩ := POINT_PRESENTED_IN_RHOND1 (v := w) (w := v) h hw hv
  have hcard : n + n' = V.ncard :=
    w4c_card_two_hafl h hv hw hvw n n' hnv hn'w hnlt hn'lt
  have hFV := w4c_determine_fv2 h hv hw hvw hcol hsub HS hHS hfv hnlt hnv
  have hLF := HAFL_CIRCLE_FORM_LOCAL_FAN h hv hw hvw hcol hsub HS hHS hfv
  have hmemfv : ∀ m : ℕ, m < n →
      ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v) ∈ fv := by
    intro m hm
    rw [hFV, Set.mem_insert_iff]
    right
    exact ⟨m, hm, rfl⟩
  have hmemwv : (w, v) ∈ fv := by
    rw [hFV]
    exact Set.mem_insert _ _
  -- orbit parametrizations and their monotone azimuth windows
  let bv : ℕ → ℝ := fun i => azim 0 v (rhoNode1_p2 FF v) ((rhoNode1_p2 FF)^[i] v)
  have hmonov : ∀ i j, i < j → j < V.ncard → bv i ≤ bv j :=
    MONO_AZIM_AS_BTA_I_p2 (v0 := v) (vv := fun i => (rhoNode1_p2 FF)^[i] v)
      (bta := bv) (k := V.ncard) hcl hv rfl
      (fun z hz hzv => hcol v z (by simp) ⟨hz, hzv⟩) (fun i => rfl) (fun i => rfl)
  have hbvle : ∀ i j, i ≤ j → j < V.ncard → bv i ≤ bv j := by
    intro i j hij hj
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · exact hmonov i j hlt hj
    · subst heq
      exact le_rfl
  have hbvn : bv n = azim 0 v (rhoNode1_p2 FF v) w := by
    dsimp only [bv]
    rw [hnv]
  have hbvn_pi : bv n ≤ Real.pi := by
    have h1 := hbvle n (V.ncard - 1) (by omega) (by omega)
    have h2 : bv (V.ncard - 1) = azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
      dsimp only [bv]
      rw [ITER_CARD_MINUS1_EQ_IVS_RN1 h hv]
    have h3 := IN_V_IMP_AZIM_LESS_PI hcl v hv (ivsRhoNode1_p2 FF v) (LOCAL_FAN_IVS_IN_V h hv)
    rw [h2] at h1
    exact h1.trans h3
  let bw : ℕ → ℝ := fun j => azim 0 w (rhoNode1_p2 FF w) ((rhoNode1_p2 FF)^[j] w)
  have hmonow : ∀ i j, i < j → j < V.ncard → bw i ≤ bw j :=
    MONO_AZIM_AS_BTA_I_p2 (v0 := w) (vv := fun j => (rhoNode1_p2 FF)^[j] w)
      (bta := bw) (k := V.ncard) hcl hw rfl
      (fun z hz hzw => hcol w z (by simp) ⟨hz, hzw⟩) (fun j => rfl) (fun j => rfl)
  have hbwle : ∀ i j, i ≤ j → j < V.ncard → bw i ≤ bw j := by
    intro i j hij hj
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · exact hmonow i j hlt hj
    · subst heq
      exact le_rfl
  -- every slice vertex is an orbit point with index at most `n`
  have hzrep : ∀ z ∈ vPrime_p2 V fv, ∃ i : ℕ, i < n + 1 ∧
      z = (rhoNode1_p2 FF)^[i] v := by
    intro z hz
    rw [POINTS_IN_HAFL_CIRCLE h hv hw hvw hcol hsub HS hHS hfv] at hz
    obtain ⟨k, hkmin, hzk⟩ := hz
    have hk_le : k ≤ n := by
      by_contra hle
      exact hkmin n (by omega) hnv
    exact ⟨k, by omega, hzk⟩
  refine ⟨hLF, ?_⟩
  intro p hp
  have hpcases : p = (w, v) ∨ ∃ m : ℕ, m < n ∧
      p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v) := by
    rw [hFV] at hp
    rcases Set.mem_insert_iff.mp hp with h | h
    · exact Or.inl h
    · rw [Set.mem_setOf_eq] at h
      obtain ⟨m, hm, hmp⟩ := h
      exact Or.inr ⟨m, hm, hmp⟩
  rcases hpcases with hpw | ⟨m, hmn, hmp⟩
  · -- diagonal dart `(w, v)`
    rw [hpw]
    have hw0 : w ≠ 0 := by
      obtain ⟨_, _, _, _, _, hFAN, _, _⟩ := h
      exact FAN_IMP_V_DIFF hFAN w hw
    have hncu : ¬ Collinear3 0 w (rhoNode1_p2 FF w) := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hw
    have hncv : ¬ Collinear3 0 w v :=
      hcol w v (by simp) ⟨hv, by simpa using hvw⟩
    have hcK : (rhoNode1_p2 FF)^[n - 1] v = (rhoNode1_p2 FF)^[V.ncard - 1] w := by
      conv_lhs => rw [← hn'w]
      rw [← Function.iterate_add_apply, show n - 1 + n' = V.ncard - 1 by omega]
    have hbwK : bw (V.ncard - 1) =
        azim 0 w (rhoNode1_p2 FF w) ((rhoNode1_p2 FF)^[n - 1] v) := by
      dsimp only [bw]
      rw [hcK]
    have hbwn' : bw n' = azim 0 w (rhoNode1_p2 FF w) v := by
      dsimp only [bw]
      rw [hn'w]
    have hbKpi : bw (V.ncard - 1) ≤ Real.pi := by
      have hπw := IN_V_IMP_AZIM_LESS_PI hcl w hw (ivsRhoNode1_p2 FF w) (LOCAL_FAN_IVS_IN_V h hw)
      have heq : bw (V.ncard - 1) =
          azim 0 w (rhoNode1_p2 FF w) (ivsRhoNode1_p2 FF w) := by
        dsimp only [bw]
        rw [ITER_CARD_MINUS1_EQ_IVS_RN1 h hw]
      rwa [heq]
    have hncc : ¬ Collinear3 0 w ((rhoNode1_p2 FF)^[n - 1] v) := by
      have hne : (rhoNode1_p2 FF)^[n - 1] v ≠ w := by
        intro he
        have hd := LOFA_IMP_DIS_ELMS23 h hv (n - 1) n (by omega) hnlt
        exact hd (he.trans hnv.symm).symm
      exact hcol w _ (by simp)
        ⟨LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (n - 1), by simpa using hne⟩
    have hle_c : bw n' ≤ bw (V.ncard - 1) :=
      hbwle n' (V.ncard - 1) (by omega) (by omega)
    have hsumc := sum4_azim_fan (x := 0) (v := w) (u := rhoNode1_p2 FF w)
      (w1 := v) (w2 := (rhoNode1_p2 FF)^[n - 1] v)
      hw0 hncu hncv hncc (by simpa only [hbwn', hbwK] using hle_c)
    have hazc : azim 0 w v ((rhoNode1_p2 FF)^[n - 1] v) =
        bw (V.ncard - 1) - bw n' := by
      rw [← hbwn', ← hbwK] at hsumc
      linarith
    refine w4c_slice_dart_convex (v := v) (w := w) (a := w) (b := v)
      (c := (rhoNode1_p2 FF)^[n - 1] v) hLF hmemwv ?_ ?_ ?_
    · rw [← hnv]
      have h := hmemfv (n - 1) (by omega)
      simpa [show n - 1 + 1 = n by omega] using h
    · rw [hazc]
      have h1 : 0 ≤ bw n' := by
        dsimp only [bw]
        exact azim_nonneg _ _ _ _
      linarith
    · intro z hz
      obtain ⟨i, hi_le, hiz⟩ := hzrep z hz
      by_cases hin : i = n
      · rw [hiz, hin, hnv, w4c_azim_vertex_last]
        exact azim_nonneg 0 w v ((rhoNode1_p2 FF)^[n - 1] v)
      · have hilt : i < n := by omega
        rw [hiz]
        have hai : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[i + n'] w := by
          conv_lhs => rw [← hn'w]
          rw [← Function.iterate_add_apply]
        have hbwi : bw (i + n') =
            azim 0 w (rhoNode1_p2 FF w) ((rhoNode1_p2 FF)^[i] v) := by
          dsimp only [bw]
          rw [hai]
        have hnei : (rhoNode1_p2 FF)^[i] v ≠ w := by
          intro he
          have hd := LOFA_IMP_DIS_ELMS23 h hv i n hilt hnlt
          exact hd (he.trans hnv.symm).symm
        have hnci : ¬ Collinear3 0 w ((rhoNode1_p2 FF)^[i] v) :=
          hcol w _ (by simp)
            ⟨LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i, by simpa using hnei⟩
        have hle_i : azim 0 w (rhoNode1_p2 FF w) v ≤
            azim 0 w (rhoNode1_p2 FF w) ((rhoNode1_p2 FF)^[i] v) := by
          have h := hbwle n' (i + n') (by omega) (by omega)
          simpa only [hbwn', hbwi] using h
        have hsum_i := sum4_azim_fan (x := 0) (v := w) (u := rhoNode1_p2 FF w)
          (w1 := v) (w2 := (rhoNode1_p2 FF)^[i] v)
          hw0 hncu hncv hnci hle_i
        have haz_i : azim 0 w v ((rhoNode1_p2 FF)^[i] v) = bw (i + n') - bw n' := by
          rw [← hbwn', ← hbwi] at hsum_i
          linarith
        calc azim 0 w v ((rhoNode1_p2 FF)^[i] v) = bw (i + n') - bw n' := haz_i
          _ ≤ bw (V.ncard - 1) - bw n' := by
              have h := hbwle (i + n') (V.ncard - 1) (by omega) (by omega)
              linarith
          _ = azim 0 w v ((rhoNode1_p2 FF)^[n - 1] v) := hazc.symm
  · -- darts `(rho^[m] v, rho^[m+1] v)` of the orbit
    rw [hmp]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- leading dart `(v, rho v)`, closing neighbour `w`
      subst hm0
      have hd0 : (v, rhoNode1_p2 FF v) ∈ fv := by
        simpa using hmemfv 0 hnpos
      refine w4c_slice_dart_convex (v := v) (w := w) (a := v)
        (b := rhoNode1_p2 FF v) (c := w) hLF hd0 hmemwv ?_ ?_
      · rw [← hbvn]
        exact hbvn_pi
      · intro z hz
        obtain ⟨i, hi_le, hiz⟩ := hzrep z hz
        rw [hiz, ← hbvn]
        change bv i ≤ bv n
        exact hbvle i n (by omega) hnlt
    · -- interior dart, predecessor `rho^[m-1] v`
      have hd' : ((rhoNode1_p2 FF)^[m - 1] v, (rhoNode1_p2 FF)^[m] v) ∈ fv := by
        have h := hmemfv (m - 1) (by omega)
        simpa [show m - 1 + 1 = m by omega] using h
      have hρm : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[m] v) =
          (rhoNode1_p2 FF)^[m + 1] v :=
        (Function.iterate_succ_apply' (rhoNode1_p2 FF) m v).symm
      have hivsm : ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[m] v) =
          (rhoNode1_p2 FF)^[m - 1] v := by
        have hstep : (rhoNode1_p2 FF)^[m] v =
            rhoNode1_p2 FF ((rhoNode1_p2 FF)^[m - 1] v) := by
          have h1 := Function.iterate_succ_apply' (rhoNode1_p2 FF) (m - 1) v
          simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ m)] using h1
        rw [hstep]
        exact IVS_RHO_IDD h (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (m - 1))
      refine w4c_slice_dart_convex (v := v) (w := w)
        (a := (rhoNode1_p2 FF)^[m] v) (b := (rhoNode1_p2 FF)^[m + 1] v)
        (c := (rhoNode1_p2 FF)^[m - 1] v) hLF (hmemfv m hmn) hd' ?_ ?_
      · have hπ := IN_V_IMP_AZIM_LESS_PI hcl ((rhoNode1_p2 FF)^[m] v)
          (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv m)
          ((rhoNode1_p2 FF)^[m - 1] v) (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (m - 1))
        rwa [hρm] at hπ
      · intro z hz
        have hzV : z ∈ V := by
          have hz' : z ∈ V ∧ ∃ y : V3, (z, y) ∈ fv := by
            simpa only [vPrime_p2, Set.mem_setOf_eq] using hz
          exact hz'.1
        have hdFF : ((rhoNode1_p2 FF)^[m] v, rhoNode1_p2 FF ((rhoNode1_p2 FF)^[m] v)) ∈ FF :=
          (LOCAL_FAN_RHO_NODE_PROS2 h).2 _ (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv m)
        have hwz := (hcl.2 _ hdFF).2 hzV
        rw [WEDGE_IN_FAN_RHOND_IVS_RHOND h (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv m)] at hwz
        simp only [wedgeGe_p2, Set.mem_setOf_eq] at hwz
        rw [hρm, hivsm] at hwz
        exact hwz.2

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
      convexLocalFan_p2 (vPrime_p2 V fw) (ePrime_p2 (E ∪ {{w, v}}) fw) fw := by
  constructor
  · exact COVEX_OF_LOFA_HALF_CIRCLE hcl h hv hw hvw hcol hsub HS hHS hfv
  · have hpair : ({w, v} : Set V3) = {v, w} := Set.pair_comm w v
    have hcolw : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
        ¬ Collinear ℝ ({0, z, t} : Set V3) := by
      intro z t hz ht
      rw [hpair] at hz
      exact hcol z t hz ht
    have hsubw : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
      intro x hx
      have h := hsub x hx
      rwa [← hpair] at h
    have hHSw : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
      rw [hpair]
      exact hHS
    exact COVEX_OF_LOFA_HALF_CIRCLE (v := w) (w := v) (fv := fw)
      hcl h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw

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
    ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv ↔ i < n + 1 := by
  intro i
  have hwV : w ∈ V := hw ▸ LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  have hFV := DETERMINE_FV h hv hwV hvw hcol hsub HS hHS hfv
  constructor
  · intro ⟨hi, hmem⟩
    rw [vPrime_p2, Set.mem_setOf_eq] at hmem
    obtain ⟨_, y, hiy⟩ := hmem
    rw [hFV] at hiy
    rcases Set.mem_insert_iff.mp hiy with hins | hT
    · have hip : (rhoNode1_p2 FF)^[i] v = w := congrArg Prod.fst hins
      have hpin : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[n] v := hip.trans hw.symm
      have hin : i = n := LT_CARD_MONO_LOFA h hv i n ⟨hi, hn, hpin⟩
      omega
    · rw [Set.mem_setOf_eq] at hT
      obtain ⟨n₀, hn₀c, hpair⟩ := hT
      have hip : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[n₀] v := congrArg Prod.fst hpair
      have hn₀lt : n₀ < n := by
        by_contra hle
        exact hn₀c n (by omega) hw
      have hn₀V : n₀ < V.ncard := by omega
      have hin : i = n₀ := LT_CARD_MONO_LOFA h hv i n₀ ⟨hi, hn₀V, hip⟩
      omega
  · intro hi
    have hiV : i < V.ncard := by omega
    refine ⟨hiV, ?_⟩
    rw [vPrime_p2, Set.mem_setOf_eq]
    refine ⟨LOCAL_FAN_ITER_RHO_NODE_IN_V h hv i, ?_⟩
    rw [hFV]
    by_cases hin : i < n
    · refine ⟨(rhoNode1_p2 FF)^[i + 1] v, ?_⟩
      rw [Set.mem_insert_iff]
      right
      rw [Set.mem_setOf_eq]
      refine ⟨i, ?_, rfl⟩
      intro m hm hmeq
      have hmV : m < V.ncard := by omega
      have hmn : m = n := LT_CARD_MONO_LOFA h hv m n ⟨hmV, hn, hmeq.trans hw.symm⟩
      omega
    · have hni : i = n := by omega
      refine ⟨v, ?_⟩
      rw [Set.mem_insert_iff]
      left
      have hip : (rhoNode1_p2 FF)^[i] v = w := by rw [hni]; exact hw
      rw [hip]

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
      i = 0 ∨ n ≤ i ∧ i < V.ncard := by
  -- `hw : w ∈ V` is shadowed by the orbit equation above.
  have hwV : w ∈ V := hw ▸ LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  -- Orbit length from `w` back to `v`.
  obtain ⟨n', hn'lt, hn'w, _⟩ := POINT_PRESENTED_IN_RHOND1 h hwV hv
  have hpair : ({w, v} : Set V3) = {v, w} := Set.pair_comm w v
  have hcolS : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz ht
    rw [hpair] at hz
    exact hcol z t hz ht
  have hsubS : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
    intro x hx
    rw [hpair]
    exact hsub x hx
  have hHS' : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
    rw [hpair]
    exact hHS
  have hconds := CONDS_IN_V_PRIME_NUM h hwV hv (Ne.symm hvw) hcolS hsubS HS hHS'
    hfw hn'lt hn'w
  have hcard : n + n' = V.ncard :=
    CARD_V_TWO_HAFL_CIRCLE h hv hwV hvw n n' hw hn'w hn hn'lt
  have hper : ∀ j : ℕ,
      (rhoNode1_p2 FF)^[j + n'] w = (rhoNode1_p2 FF)^[j] v :=
    fun j => by rw [Function.iterate_add_apply, hn'w]
  have hpern : ∀ k : ℕ,
      (rhoNode1_p2 FF)^[k + n] v = (rhoNode1_p2 FF)^[k] w :=
    fun k => by rw [Function.iterate_add_apply, hw]
  intro i
  constructor
  · rintro ⟨hiV, hmem⟩
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · refine Or.inr ⟨?_, hiV⟩
      by_contra hnot
      have hin : i < n := by omega
      have hklt : i + n' < V.ncard := by omega
      have hmem' : (rhoNode1_p2 FF)^[i + n'] w ∈ vPrime_p2 V fw := by
        rw [hper i]
        exact hmem
      have hlt := (hconds (i + n')).mp ⟨hklt, hmem'⟩
      omega
  · rintro (hi0 | ⟨hni, hiV⟩)
    · subst hi0
      refine ⟨by omega, ?_⟩
      have hm := (hconds n').mpr (by omega : n' < n' + 1)
      simpa [hn'w] using hm.2
    · refine ⟨hiV, ?_⟩
      have hkle : i - n < n' + 1 := by omega
      have hm := (hconds (i - n)).mpr hkle
      have heq : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[i - n] w := by
        simpa [Nat.sub_add_cancel hni] using hpern (i - n)
      rw [heq]
      exact hm.2

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
      p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
  have hwV : w ∈ V := hw ▸ LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  have hFV := DETERMINE_FV h hv hwV hvw hcol hsub HS hHS hfv
  have hset : {p : V3 × V3 | ∃ n₀ : ℕ,
      (∀ m : ℕ, m < n₀ + 1 → ¬((rhoNode1_p2 FF)^[m] v = w)) ∧
        p = ((rhoNode1_p2 FF)^[n₀] v, (rhoNode1_p2 FF)^[n₀ + 1] v)}
      = {p : V3 × V3 | ∃ m : ℕ, m < n ∧
        p = ((rhoNode1_p2 FF)^[m] v, (rhoNode1_p2 FF)^[m + 1] v)} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n₀, hn₀c, hn₀p⟩ := hp
      have hn₀lt : n₀ < n := by
        by_contra hle
        exact hn₀c n (by omega) hw
      exact ⟨n₀, hn₀lt, hn₀p⟩
    · intro hp
      obtain ⟨m, hm, hmp⟩ := hp
      refine ⟨m, ?_, hmp⟩
      intro m' hm' hmeq
      exact LOFA_IMP_DIS_ELMS23 h hv m' n (by omega) hn (hw.trans hmeq.symm)
  rw [hFV, hset]

/-- HOL `INTERIOR_ANGLE_LEM_SLICING_FAN` (local_lemmas1.hl:4988) — giant. -/
theorem INTERIOR_ANGLE_LEM_SLICING_FAN (hcl : convexLocalFan_p2 V E FF)
    (h : localFan_p2 V E FF) (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w)
    (hcol : ∀ z t : V3, z ∈ ({v, w} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3))
    (hsub : ∀ x ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 x E)
    (HS : Hypermap (V3 × V3)) (hHS : IsHyp_p2 0 V (E ∪ {{v, w}}) HS)
    (hfv : fv = HS.face (v, rhoNode1_p2 FF v))
    (hfw : fw = HS.face (w, rhoNode1_p2 FF w)) :
    interiorAngle1_p2 0 fv v + interiorAngle1_p2 0 fw v = interiorAngle1_p2 0 FF v := by
  obtain ⟨n, hnlt, hnv, -⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0, Function.iterate_zero] at hnv
      exact absurd hnv hvw
    · exact hp
  have hFVn := DETERMINE_FV2 h hv hw hvw hcol hsub HS hHS hfv hnlt hnv
  obtain ⟨n', hn'lt, hn'v, -⟩ := POINT_PRESENTED_IN_RHOND1 (v := w) (w := v) h hw hv
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | hp
    · rw [h0, Function.iterate_zero] at hn'v
      exact absurd hn'v hvw.symm
    · exact hp
  have hHSw : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
    have he : E ∪ {{w, v}} = E ∪ {{v, w}} := by rw [Set.pair_comm]
    rwa [he]
  have hcolw : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz ht
    exact hcol z t (by rwa [Set.pair_comm] at hz) ht
  have hsubw : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
    intro x hx
    have h := hsub x hx
    rwa [Set.pair_comm v w] at h
  have hFVw := DETERMINE_FV2 (v := w) (w := v) (fv := fw) (n := n')
    h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw hn'lt hn'v
  have hLF := HAFL_CIRCLE_FORM_LOCAL_FAN h hv hw hvw hcol hsub HS hHS hfv
  have hLF2 := HAFL_CIRCLE_FORM_LOCAL_FAN2 h hv hw hvw hcol hsub HS hHS hfv hfw
  -- fv: rho = rho_FF v, ivs = w (closing dart)
  have hd1 : (v, rhoNode1_p2 FF v) ∈ fv := by
    rw [hFVn, Set.mem_insert_iff]
    right
    refine ⟨0, hnpos, ?_⟩
    simp
  have hd2 : (w, v) ∈ fv := by
    rw [hFVn]
    exact Set.mem_insert _ _
  have hrho_fv : rhoNode1_p2 fv v = rhoNode1_p2 FF v := DETER_RHO_NODE hLF hd1
  have hivs_fv : ivsRhoNode1_p2 fv v = w := IVS_RHO_NODE1_DETE hLF hd2
  -- fw: rho = w (closing dart), ivs = ivs_FF v
  have hd3 : (v, w) ∈ fw := by
    rw [hFVw]
    exact Set.mem_insert _ _
  have hrho_fw : rhoNode1_p2 fw v = w := DETER_RHO_NODE hLF2.2 hd3
  have hcard := CARD_V_TWO_HAFL_CIRCLE h hv hw hvw n n' hnv hn'v hnlt hn'lt
  have hd4 : (ivsRhoNode1_p2 FF v, v) ∈ fw := by
    rw [hFVw, Set.mem_insert_iff]
    right
    refine ⟨n' - 1, by omega, ?_⟩
    have hleft : (rhoNode1_p2 FF)^[n' - 1] w = ivsRhoNode1_p2 FF v := by
      rw [← hnv, ← Function.iterate_add_apply]
      rw [show n' - 1 + n = V.ncard - 1 by omega]
      exact ITER_CARD_MINUS1_EQ_IVS_RN1 h hv
    have hstep : (rhoNode1_p2 FF)^[n' - 1 + 1] w = v := by
      rw [show n' - 1 + 1 = n' by omega]
      exact hn'v
    rw [hleft, hstep]
  have hivs_fw : ivsRhoNode1_p2 fw v = ivsRhoNode1_p2 FF v := IVS_RHO_NODE1_DETE hLF2.2 hd4
  simp only [interiorAngle1_p2]
  rw [hrho_fv, hivs_fv, hrho_fw, hivs_fw]
  -- the two half-angles sum to the full angle by `sum4_azim_fan`
  have hdFF : (v, rhoNode1_p2 FF v) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 h).2 v hv
  have hwmem : w ∈ wedgeGe_p2 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
    have hVsub := (hcl.2 (v, rhoNode1_p2 FF v) hdFF).2
    have hmem := hVsub hw
    rwa [WEDGE_IN_FAN_RHOND_IVS_RHOND h hv] at hmem
  have hxv : v ≠ 0 := by
    obtain ⟨_, _, _, _, _, hFAN, _, _⟩ := h
    exact FAN_IMP_V_DIFF hFAN v hv
  have hncu : ¬ Collinear3 0 v (rhoNode1_p2 FF v) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h hv
  have hnc1 : ¬ Collinear3 0 v w := hcol v w (by simp) ⟨hw, by simpa using hvw.symm⟩
  have hnc2 : ¬ Collinear3 0 v (ivsRhoNode1_p2 FF v) := LOFA_IMP_NOT_COLL_IVS h hv
  exact (sum4_azim_fan (x := 0) (v := v) (u := rhoNode1_p2 FF v)
    (w1 := w) (w2 := ivsRhoNode1_p2 FF v) hxv hncu hnc1 hnc2 hwmem.2).symm

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
      interiorAngle1_p2 0 fw w + interiorAngle1_p2 0 fv w = interiorAngle1_p2 0 FF w := by
  constructor
  · exact INTERIOR_ANGLE_LEM_SLICING_FAN hcl h hv hw hvw hcol hsub HS hHS hfv hfw
  · have hHSw : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
      have he : E ∪ {{w, v}} = E ∪ {{v, w}} := by rw [Set.pair_comm]
      rwa [he]
    have hcolw : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
        ¬ Collinear ℝ ({0, z, t} : Set V3) := by
      intro z t hz ht
      exact hcol z t (by rwa [Set.pair_comm] at hz) ht
    have hsubw : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
      intro x hx
      have h := hsub x hx
      rwa [Set.pair_comm v w] at h
    exact INTERIOR_ANGLE_LEM_SLICING_FAN (v := w) (w := v) (fv := fw) (fw := fv)
      hcl h hw hv (Ne.symm hvw) hcolw hsubw HS hHSw hfw hfv

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
        interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v) := by
  intro i hi
  have hwV : w ∈ V := hw ▸ LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  have hFV2 := DETERMINE_FV2 h hv hwV hvw hcol hsub HS hHS hfv hn hw
  have hLF := HAFL_CIRCLE_FORM_LOCAL_FAN h hv hwV hvw hcol hsub HS hHS hfv
  have hdart : ((rhoNode1_p2 FF)^[i] v, (rhoNode1_p2 FF)^[i + 1] v) ∈ fv := by
    rw [hFV2, Set.mem_insert_iff]
    right
    exact ⟨i, hi.2, rfl⟩
  have hdart' : ((rhoNode1_p2 FF)^[i - 1] v, (rhoNode1_p2 FF)^[i] v) ∈ fv := by
    rw [hFV2, Set.mem_insert_iff]
    right
    refine ⟨i - 1, by omega, ?_⟩
    rw [show i - 1 + 1 = i by omega]
  have hrho : rhoNode1_p2 fv ((rhoNode1_p2 FF)^[i] v) = (rhoNode1_p2 FF)^[i + 1] v :=
    DETER_RHO_NODE hLF hdart
  have hivs : ivsRhoNode1_p2 fv ((rhoNode1_p2 FF)^[i] v) = (rhoNode1_p2 FF)^[i - 1] v :=
    IVS_RHO_NODE1_DETE hLF hdart'
  have hrhoFF : rhoNode1_p2 FF ((rhoNode1_p2 FF)^[i] v) = (rhoNode1_p2 FF)^[i + 1] v :=
    (Function.iterate_succ_apply' (rhoNode1_p2 FF) i v).symm
  have hivsFF : ivsRhoNode1_p2 FF ((rhoNode1_p2 FF)^[i] v) = (rhoNode1_p2 FF)^[i - 1] v := by
    have hstep : (rhoNode1_p2 FF)^[i] v = rhoNode1_p2 FF ((rhoNode1_p2 FF)^[i - 1] v) := by
      have h1 := Function.iterate_succ_apply' (rhoNode1_p2 FF) (i - 1) v
      simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hi.1] using h1
    rw [hstep]
    exact IVS_RHO_IDD h (LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (i - 1))
  simp only [interiorAngle1_p2]
  rw [hrho, hivs, hrhoFF, hivsFF]

/-- Local `SUM_UNION` for `setSum` on `ℕ` (the importable copy lives in
`TameLp`, outside this file's import cone). -/
private theorem w4c_setSum_union_disjoint {s t : Set ℕ} {f : ℕ → ℝ}
    (hd : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    setSum (s ∪ t) f = setSum s f + setSum t f := by
  rw [setSum, setSum, setSum, dif_pos (hs.union ht), dif_pos hs, dif_pos ht,
    Set.Finite.toFinset_union hs ht]
  have hd' : Disjoint hs.toFinset ht.toFinset := by
    rw [Finset.disjoint_left]
    intro a ha hta
    exact (Set.disjoint_left.mp hd) ((Set.Finite.mem_toFinset hs).mp ha)
      ((Set.Finite.mem_toFinset ht).mp hta)
  exact Finset.sum_union hd'

/-- Local `SUM_CLAUSES` insert for `setSum`. -/
private theorem w4c_setSum_insert {s : Set ℕ} {a : ℕ} (ha : a ∉ s) (hs : s.Finite)
    (f : ℕ → ℝ) : setSum (insert a s) f = f a + setSum s f := by
  rw [setSum, setSum, dif_pos (hs.insert a), dif_pos hs,
    Set.Finite.toFinset_insert (hs.insert a)]
  exact Finset.sum_insert (by simpa using ha)

/-- `setSum` on the empty set. -/
private theorem w4c_setSum_empty (f : ℕ → ℝ) : setSum (∅ : Set ℕ) f = 0 := by
  rw [setSum, dif_pos Set.finite_empty]
  simp

/-- `setSum` on a singleton. -/
private theorem w4c_setSum_singleton (a : ℕ) (f : ℕ → ℝ) :
    setSum ({a} : Set ℕ) f = f a := by
  simp [setSum]

/-- `setSum` on a two-element set. -/
private theorem w4c_setSum_pair {a b : ℕ} (hab : a ≠ b) (f : ℕ → ℝ) :
    setSum ({a, b} : Set ℕ) f = f a + f b := by
  have h1 : ({a, b} : Set ℕ) = insert a ({b} : Set ℕ) := rfl
  rw [h1, w4c_setSum_insert (by simpa using hab) (Set.finite_singleton b) f,
    w4c_setSum_singleton]

/-- `setSum` congruence on a fixed finite set. -/
private theorem w4c_setSum_congr {s : Set ℕ} {f g : ℕ → ℝ}
    (h : ∀ i ∈ s, f i = g i) : setSum s f = setSum s g := by
  unfold setSum
  by_cases hs : s.Finite
  · simp only [dif_pos hs]
    exact Finset.sum_congr rfl (fun i hi => h i ((Set.Finite.mem_toFinset hs).mp hi))
  · simp only [dif_neg hs]

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
            (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) := by
  intro g
  obtain ⟨n, hnlt, hnv, -⟩ := POINT_PRESENTED_IN_RHOND1 h hv hw
  obtain ⟨n', hn'lt, hn'w, -⟩ := POINT_PRESENTED_IN_RHOND1 (v := w) (w := v) h hw hv
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0, Function.iterate_zero] at hnv
      exact absurd hnv hvw
    · exact hp
  have hpair : ({w, v} : Set V3) = {v, w} := Set.pair_comm w v
  have hcolS : ∀ z t : V3, z ∈ ({w, v} : Set V3) → t ∈ V \ {z} →
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
    intro z t hz ht
    rw [hpair] at hz
    exact hcol z t hz ht
  have hsubS : ∀ x ∈ FF, affGt ({0} : Set V3) {w, v} ⊆ wedgeInFanGt_p2 x E := by
    intro x hx
    rw [hpair]
    exact hsub x hx
  have hHS' : IsHyp_p2 0 V (E ∪ {{w, v}}) HS := by
    rw [hpair]
    exact hHS
  have hcard : n + n' = V.ncard :=
    CARD_V_TWO_HAFL_CIRCLE h hv hw hvw n n' hnv hn'w hnlt hn'lt
  have hmemfv : ∀ i : ℕ,
      i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv ↔ i < n + 1 :=
    fun i => CONDS_IN_V_PRIME_NUM h hv hw hvw hcol hsub HS hHS hfv hnlt hnv i
  have hmemfw : ∀ i : ℕ, i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw ↔
      i = 0 ∨ n ≤ i ∧ i < V.ncard :=
    fun i => CONDS_IN_V_PRIME_NUM2 h hv hw hvw hcol hsub HS hHS hfw hnlt hnv i
  have hfvset : {i : ℕ | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fv} =
      {i : ℕ | i < n + 1} := by
    ext i
    simpa only [Set.mem_setOf_eq] using hmemfv i
  have hfwset : {i : ℕ | i < V.ncard ∧ (rhoNode1_p2 FF)^[i] v ∈ vPrime_p2 V fw} =
      {i : ℕ | i = 0 ∨ n ≤ i ∧ i < V.ncard} := by
    ext i
    simpa only [Set.mem_setOf_eq] using hmemfw i
  have hU1 : ({i : ℕ | i < n + 1} : Set ℕ) =
      {i : ℕ | 0 < i ∧ i < n} ∪ {0, n} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hU2 : ({i : ℕ | i = 0 ∨ n ≤ i ∧ i < V.ncard} : Set ℕ) =
      {i : ℕ | n < i ∧ i < V.ncard} ∪ {0, n} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hU3 : ({i : ℕ | i < V.ncard} : Set ℕ) =
      {i : ℕ | 0 < i ∧ i < n} ∪ ({i : ℕ | n < i ∧ i < V.ncard} ∪ {0, n}) := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hd1 : Disjoint ({i : ℕ | 0 < i ∧ i < n} : Set ℕ) ({0, n} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hj
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    omega
  have hd2 : Disjoint ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ) ({0, n} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hj
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    omega
  have hd3 : Disjoint ({i : ℕ | 0 < i ∧ i < n} : Set ℕ)
      ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hj
    simp only [Set.mem_setOf_eq] at hi hj
    omega
  have hd3' : Disjoint ({i : ℕ | 0 < i ∧ i < n} : Set ℕ)
      ({i : ℕ | n < i ∧ i < V.ncard} ∪ {0, n}) := by
    rw [Set.disjoint_left]
    intro i hi hj
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hi hj
    omega
  have hf1 : ({i : ℕ | 0 < i ∧ i < n} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio n) (fun i hi => by
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hi ⊢
      omega)
  have hf2 : ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio V.ncard) (fun i hi => by
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hi ⊢
      omega)
  have hfE : ({0, n} : Set ℕ).Finite := (Set.finite_singleton n).insert 0
  have hpairFF : setSum ({0, n} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
      g 0 * interiorAngle1_p2 0 FF v + g n * interiorAngle1_p2 0 FF w := by
    rw [w4c_setSum_pair (by omega : (0 : ℕ) ≠ n)]
    simp [Function.iterate_zero, hnv]
  have hpairA : setSum ({0, n} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) =
      g 0 * interiorAngle1_p2 0 fv v + g n * interiorAngle1_p2 0 fv w := by
    rw [w4c_setSum_pair (by omega : (0 : ℕ) ≠ n)]
    simp [Function.iterate_zero, hnv]
  have hpairB : setSum ({0, n} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) =
      g 0 * interiorAngle1_p2 0 fw v + g n * interiorAngle1_p2 0 fw w := by
    rw [w4c_setSum_pair (by omega : (0 : ℕ) ≠ n)]
    simp [Function.iterate_zero, hnv]
  have hS1eq : setSum ({i : ℕ | 0 < i ∧ i < n} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 fv ((rhoNode1_p2 FF)^[i] v)) =
      setSum ({i : ℕ | 0 < i ∧ i < n} : Set ℕ)
        (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) := by
    apply w4c_setSum_congr
    intro i hi
    obtain ⟨hi0, hin⟩ := hi
    rw [INTERIOR_AGL_EQ h hv hw hvw hcol hsub HS hHS hfv hnlt hnv i ⟨hi0, hin⟩]
  have hS2eq : setSum ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v)) =
      setSum ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ)
        (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) := by
    apply w4c_setSum_congr
    intro i hi
    obtain ⟨hni, hiK⟩ := hi
    have hper : (rhoNode1_p2 FF)^[i] v = (rhoNode1_p2 FF)^[i - n] w := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : n ≤ i)]
      rw [Function.iterate_add_apply, hnv]
    have hj := INTERIOR_AGL_EQ (v := w) (w := v) (fv := fw) (n := n')
      h hw hv (Ne.symm hvw) hcolS hsubS HS hHS' hfw hn'lt hn'w (i - n)
      ⟨by omega, by omega⟩
    rw [hper, hj]
  have hL : setSum ({i : ℕ | i < V.ncard} : Set ℕ)
      (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) =
      setSum ({i : ℕ | 0 < i ∧ i < n} : Set ℕ)
          (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) +
        setSum ({i : ℕ | n < i ∧ i < V.ncard} : Set ℕ)
          (fun i => g i * interiorAngle1_p2 0 FF ((rhoNode1_p2 FF)^[i] v)) +
        (g 0 * interiorAngle1_p2 0 FF v + g n * interiorAngle1_p2 0 FF w) := by
    rw [hU3]
    rw [w4c_setSum_union_disjoint hd3' hf1 (hf2.union hfE)]
    rw [w4c_setSum_union_disjoint hd2 hf2 hfE]
    rw [hpairFF]
    ring
  rw [hfvset, hfwset, hU1, hU2]
  rw [w4c_setSum_union_disjoint hd1 hf1 hfE]
  rw [w4c_setSum_union_disjoint hd2 hf2 hfE]
  rw [hS1eq, hS2eq, hpairA, hpairB]
  rw [hL]
  have h0 := (INTERIOR_ANGLE_LEM_SLICING_FAN2 hcl h hv hw hvw hcol hsub HS hHS hfv hfw).1
  have hn2 := (INTERIOR_ANGLE_LEM_SLICING_FAN2 hcl h hv hw hvw hcol hsub HS hHS hfv hfw).2
  linear_combination - (g 0) * h0 - (g n) * hn2

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
              (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v))) := by
  have hcvx := COVEX_OF_LOFA_HALF_CIRCLE2 hcl h hv hw hvw hcol hsub HS hHS hfv hfw
  exact ⟨hcvx.1, hcvx.2, SUM_INTERIOR_AGL_LEMMA hcl h hv hw hvw hcol hsub HS hHS hfv hfw⟩

/-- HOL `WEDGE_IN_FAN_LOFA_DETER2` (local_lemmas1.hl:5609) — giant. -/
theorem WEDGE_IN_FAN_LOFA_DETER2 (h : localFan_p2 V E FF) (hv : v ∈ V) :
    wedgeInFanGt_p2 (v, rhoNode1_p2 FF v) E =
      wedge 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v) := by
  have hivsV : ivsRhoNode1_p2 FF v ∈ V := LOCAL_FAN_IVS_IN_V h hv
  have hr : rhoNode1_p2 FF (ivsRhoNode1_p2 FF v) = v := LOCAL_FAN_RHO_NODE_IVS h hv
  exact WEDGE_IN_FAN_LOFA_DETER (v := ivsRhoNode1_p2 FF v) (w := v) h hivsV hr

/-- 三点仿射包 membership 的双系数刻画（差落在 `span {b-a, c-a}`）。 -/
private theorem w11_exists_combo_of_mem_affineSpan3 {a b c z : V3}
    (hz : z ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3)) :
    ∃ d1 d2 : ℝ, z = a + d1 • (b - a) + d2 • (c - a) := by
  have h1 : z -ᵥ a ∈ vectorSpan ℝ ({a, b, c} : Set V3) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan (SetLike.mem_coe.mp hz)
      (mem_affineSpan ℝ (by simp))
  rw [vectorSpan_eq_span_vsub_set_right ℝ
    (by simp : a ∈ ({a, b, c} : Set V3))] at h1
  have hle : Submodule.span ℝ ((· -ᵥ a) '' ({a, b, c} : Set V3)) ≤
      Submodule.span ℝ ({b - a, c - a} : Set V3) := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨z', hz'set, hp⟩
    dsimp only at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'set
    rcases hz'set with hz' | hz' | hz'
    · rw [← hp, hz', vsub_self]
      exact Submodule.zero_mem _
    · rw [← hp, hz', vsub_eq_sub]
      exact Submodule.subset_span (by simp)
    · rw [← hp, hz', vsub_eq_sub]
      exact Submodule.subset_span (by simp)
  obtain ⟨d1, d2, hd⟩ := Submodule.mem_span_pair.mp (hle h1)
  have hd' : d1 • (b - a) + d2 • (c - a) = z - a := by
    rw [hd, vsub_eq_sub]
  refine ⟨d1, d2, ?_⟩
  calc z = a + (z - a) := by abel
    _ = a + (d1 • (b - a) + d2 • (c - a)) := by rw [hd']
    _ = a + d1 • (b - a) + d2 • (c - a) := by abel

/-- 共面提取的抽象 ℂ 核心：两组实系数组合共用一对复数 P、Q，且轴向组合
为零、w 侧组合非零时，v 侧组合是 w 侧组合的实倍数。 -/
private theorem w11_complex_mul_of_span_two {P Q zv zw : ℂ}
    {β1 β2 α1 α2 γ1 γ2 : ℝ}
    (hzu : ((β1 : ℝ) : ℂ) * P + ((β2 : ℝ) : ℂ) * Q = 0)
    (hzv : zv = ((α1 : ℝ) : ℂ) * P + ((α2 : ℝ) : ℂ) * Q)
    (hzw : zw = ((γ1 : ℝ) : ℂ) * P + ((γ2 : ℝ) : ℂ) * Q)
    (hβ : β1 ≠ 0 ∨ β2 ≠ 0) (hzw0 : zw ≠ 0) :
    ∃ μ : ℝ, zv = ((μ : ℝ) : ℂ) * zw := by
  by_cases hβ1 : β1 = 0
  · have hβ2 : β2 ≠ 0 := by
      rcases hβ with h | h
      · exact absurd hβ1 h
      · exact h
    have hβ2' : ((β2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ2
    have h1 : ((β2 : ℝ) : ℂ) * Q = 0 := by
      have h1' := hzu
      rw [hβ1, Complex.ofReal_zero, zero_mul, zero_add] at h1'
      exact h1'
    have hQ : Q = 0 := by
      have h2 : Q = (((β2 : ℝ) : ℂ)⁻¹ * ((β2 : ℝ) : ℂ)) * Q := by
        rw [inv_mul_cancel₀ hβ2', one_mul]
      calc Q = (((β2 : ℝ) : ℂ)⁻¹ * ((β2 : ℝ) : ℂ)) * Q := h2
        _ = ((β2 : ℝ) : ℂ)⁻¹ * (((β2 : ℝ) : ℂ) * Q) := by ring
        _ = ((β2 : ℝ) : ℂ)⁻¹ * 0 := by rw [h1]
        _ = 0 := by rw [mul_zero]
    have hγ1 : γ1 ≠ 0 := by
      intro h0
      rw [hzw, h0, hQ] at hzw0
      simp at hzw0
    have hd1 : ((α1 / γ1 : ℝ) : ℂ) * ((γ1 : ℝ) : ℂ) = ((α1 : ℝ) : ℂ) := by
      exact_mod_cast div_mul_cancel₀ α1 hγ1
    refine ⟨α1 / γ1, ?_⟩
    rw [hzv, hzw, hQ, mul_add, ← mul_assoc, hd1]
    simp [mul_zero]
  · have hβ1' : ((β1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ1
    have hP : P = ((-(β2 / β1) : ℝ) : ℂ) * Q := by
      have h1 : ((β1 : ℝ) : ℂ) * P = -((β2 : ℝ) : ℂ) * Q := by
        linear_combination hzu
      have h2 : P = (((β1 : ℝ) : ℂ)⁻¹ * ((β1 : ℝ) : ℂ)) * P := by
        rw [inv_mul_cancel₀ hβ1', one_mul]
      calc P = (((β1 : ℝ) : ℂ)⁻¹ * ((β1 : ℝ) : ℂ)) * P := h2
        _ = ((β1 : ℝ) : ℂ)⁻¹ * (((β1 : ℝ) : ℂ) * P) := by ring
        _ = ((β1 : ℝ) : ℂ)⁻¹ * (-((β2 : ℝ) : ℂ) * Q) := by rw [h1]
        _ = ((-(β2 / β1) : ℝ) : ℂ) * Q := by
            push_cast
            field_simp [hβ1']
    have hzvQ : zv = ((α2 - α1 * β2 / β1 : ℝ) : ℂ) * Q := by
      rw [hzv, hP]; push_cast; ring
    have hzwQ : zw = ((γ2 - γ1 * β2 / β1 : ℝ) : ℂ) * Q := by
      rw [hzw, hP]; push_cast; ring
    have hκ : γ2 - γ1 * β2 / β1 ≠ 0 := by
      intro h0
      rw [hzwQ, h0] at hzw0
      simp at hzw0
    have hd2 : (((α2 - α1 * β2 / β1 : ℝ) / (γ2 - γ1 * β2 / β1 : ℝ) : ℝ) : ℂ)
        * ((γ2 - γ1 * β2 / β1 : ℝ) : ℂ) = ((α2 - α1 * β2 / β1 : ℝ) : ℂ) := by
      exact_mod_cast div_mul_cancel₀ _ hκ
    refine ⟨(α2 - α1 * β2 / β1) / (γ2 - γ1 * β2 / β1), ?_⟩
    rw [hzvQ, hzwQ, ← mul_assoc, hd2]

/-- HOL `AZIM_EQ_0_PI_EQ_COPLANAR`（Multivariate-flyspeck.ml:3161）的解析
替代：四点 {x,u,v,w} 共面且 v、w 都不在轴 xu 上时，v-x 与 w-x 在轴向
正交标架下的 ℂ 平面坐标成实倍数，故 θ = azim x u w v 的相位 e^{iθ} 为
实数，即 sin θ = 0，结合 0 ≤ θ < 2π 得 θ ∈ {0, π}。 -/
private theorem w11_azim_eq_0_or_pi_of_coplanar {x u v w : V3}
    (hncv : ¬ Collinear3 x u v) (hncw : ¬ Collinear3 x u w)
    (hcop : Coplanar ({x, u, v, w} : Set V3)) :
    azim x u w v = 0 ∨ azim x u w v = Real.pi := by
  have hux : u ≠ x := fun he => hncw (collinear3_of_eq he)
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (u - x) (sub_ne_zero.mpr hux)
  have hax : (u - x : V3) = dist u x • f3 := by rw [dist_eq_norm]; exact halign
  have hzwne : zOf f1 f2 (w - x) ≠ 0 := (zOf_ne_zero_iff hon hax hux w).mpr hncw
  obtain ⟨ψ, rb, ra, hrb, hra, hzwrep, hzvrep⟩ := azim_frame_spec hncw hncv hon hax hux
  -- 共面性 → 公共平面表示 → ℂ 坐标实相关
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, zOf f1 f2 (v - x) = ((μ : ℝ) : ℂ) * zOf f1 f2 (w - x) := by
    obtain ⟨a, b, c, hsub⟩ := hcop
    have hxS : x ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have huS : u ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have hvS : v ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    have hwS : w ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
    obtain ⟨ξ1, ξ2, hξ⟩ := w11_exists_combo_of_mem_affineSpan3 hxS
    obtain ⟨β1, β2, hβ⟩ := w11_exists_combo_of_mem_affineSpan3 huS
    obtain ⟨α1, α2, hα⟩ := w11_exists_combo_of_mem_affineSpan3 hvS
    obtain ⟨γ1, γ2, hγ⟩ := w11_exists_combo_of_mem_affineSpan3 hwS
    have hvx : v - x = (α1 - ξ1) • (b - a) + (α2 - ξ2) • (c - a) := by
      rw [hα, hξ]; module
    have hwx : w - x = (γ1 - ξ1) • (b - a) + (γ2 - ξ2) • (c - a) := by
      rw [hγ, hξ]; module
    have huxc : u - x = (β1 - ξ1) • (b - a) + (β2 - ξ2) • (c - a) := by
      rw [hβ, hξ]; module
    have hzlin : ∀ p q : V3, ∀ d1 d2 : ℝ, p - q = d1 • (b - a) + d2 • (c - a) →
        zOf f1 f2 (p - q) = ((d1 : ℝ) : ℂ) * zOf f1 f2 (b - a)
          + ((d2 : ℝ) : ℂ) * zOf f1 f2 (c - a) := by
      intro p q d1 d2 hd
      rw [hd, zOf_add, zOf_smul, zOf_smul]
    have hzc := hzlin v x (α1 - ξ1) (α2 - ξ2) hvx
    have hzd := hzlin w x (γ1 - ξ1) (γ2 - ξ2) hwx
    have hzu0 := hzlin u x (β1 - ξ1) (β2 - ξ2) huxc
    have hf3z : zOf f1 f2 f3 = 0 := by
      obtain ⟨-, -, -, -, h13, h23, -⟩ := hon
      unfold zOf
      rw [dotProduct_comm f3 f1, dotProduct_comm f3 f2, h13, h23]
      norm_num
    rw [hax, zOf_smul, hf3z, mul_zero] at hzu0
    have hne2 : β1 - ξ1 ≠ 0 ∨ β2 - ξ2 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hux
      have hzero : u - x = 0 := by
        rw [huxc, hcon.1, hcon.2]
        module
      exact sub_eq_zero.mp hzero
    exact w11_complex_mul_of_span_two hzu0.symm hzc hzd hne2 hzwne
  -- 相位：ra • e^{i(ψ+θ)} = μ • rb • e^{iψ} ⟹ ra • e^{iθ} = μ • rb ∈ ℝ
  have hkey : ((ra : ℝ) : ℂ) * Complex.exp (((azim x u w v : ℝ) : ℂ) * Complex.I)
      = ((μ * rb : ℝ) : ℂ) := by
    have h1 : ((ra : ℝ) : ℂ)
          * Complex.exp ((((ψ + azim x u w v : ℝ) : ℂ)) * Complex.I)
        = ((μ : ℝ) : ℂ) * (((rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)) := by
      rw [← hzvrep, ← hzwrep]
      exact hμ
    have hexp : Complex.exp ((((ψ + azim x u w v : ℝ) : ℂ)) * Complex.I)
        = Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((azim x u w v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp] at h1
    have h2 : ((ra : ℝ) : ℂ) * Complex.exp (((azim x u w v : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)
        = ((μ * rb : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
      push_cast
      linear_combination h1
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) h2
  have hsin : Real.sin (azim x u w v) = 0 := by
    have h := congrArg Complex.im hkey
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_mul_I,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, mul_zero, add_zero, zero_mul, zero_add, mul_one, mul_add] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by exact_mod_cast (ne_of_gt hra))
    · exact h'
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hn0 : (0:ℤ) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hnle : ((n:ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega)
    have hθn : azim x u w v < 0 := by rw [← hn]; nlinarith [hnle, hpi]
    exact absurd (azim_nonneg x u w v) (not_le.mpr hθn)
  have hn2 : n < 2 := by
    by_contra hcon
    push_neg at hcon
    have hnge : (2:ℝ) ≤ ((n:ℤ) : ℝ) := by exact_mod_cast (by omega)
    have hθbig : 2 * Real.pi ≤ azim x u w v := by rw [← hn]; nlinarith [hnge, hpi]
    exact absurd hθbig (not_le.mpr (azim_lt_two_pi x u w v))
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · exact Or.inl (by rw [← hn]; push_cast; norm_num)
  · exact Or.inr (by rw [← hn]; push_cast; norm_num)

/-- HOL `AZIM_COND_FOR_COPLANAR` (local_lemmas1.hl:5620): the azimuth is `0`
or `π` iff the four points are coplanar. -/
theorem AZIM_COND_FOR_COPLANAR (v0 v1 w1 w2 : V3) :
    azim v0 v1 w1 w2 = 0 ∨ azim v0 v1 w1 w2 = Real.pi ↔ Coplanar {v0, v1, w1, w2} := by

  constructor
  · intro h
    exact AZIM_EQ_0_PI_IMP_COPLANAR v0 v1 w1 w2 h
  · intro hcop
    by_cases hc1 : Collinear3 v0 v1 w1
    · exact Or.inl (by rw [azim, if_pos (Or.inl hc1)])
    by_cases hc2 : Collinear3 v0 v1 w2
    · exact Or.inl (by rw [azim, if_pos (Or.inr hc2)])
    · have hset : ({v0, v1, w2, w1} : Set V3) = {v0, v1, w1, w2} := by
        ext q
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      have hcop' : Coplanar ({v0, v1, w2, w1} : Set V3) := by rw [hset]; exact hcop
      exact w11_azim_eq_0_or_pi_of_coplanar (x := v0) (u := v1) (v := w2) (w := w1)
        hc2 hc1 hcop'

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
      ¬ Collinear ℝ ({0, z, t} : Set V3) := by
  -- It suffices to treat the `z = v` side: the `z = w` side is the same
  -- statement for the swapped pair (`{w,v} = {v,w}`).
  have key : ∀ (a b : V3), a ∈ V → b ∈ V → a ≠ b →
      (∀ x ∈ FF, affGt ({0} : Set V3) {a, b} ⊆ wedgeInFanGt_p2 x E) →
      ∀ t : V3, t ∈ V \ {a} → ¬ Collinear ℝ ({0, a, t} : Set V3) := by
    intro a b ha hb hab hsub' t ht
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at ht
    obtain ⟨htV, hta⟩ := ht
    intro hcol
    have hlf : localFan_p2 V E FF := CVX_LO_IMP_LO hcl
    have hFAN : FAN 0 V E := by
      obtain ⟨HS0, _, _, _, _, hFAN, _, _⟩ := hlf
      exact hFAN
    have h0a : (0:V3) ≠ a := Ne.symm (FAN_IMP_V_DIFF hFAN a ha)
    have h0b : (0:V3) ≠ b := Ne.symm (FAN_IMP_V_DIFF hFAN b hb)
    have hdis_ab : Disjoint ({0} : Set V3) {a, b} := by
      rw [Set.disjoint_singleton_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h0a, h0b⟩
    have hdis_ba : Disjoint ({0} : Set V3) {b, a} := by
      rw [Set.disjoint_singleton_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h0b, h0a⟩
    have hcollρ : ¬ Collinear ℝ ({0, a, rhoNode1_p2 FF a} : Set V3) :=
      LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf ha
    have hdart : (a, rhoNode1_p2 FF a) ∈ FF := (LOCAL_FAN_RHO_NODE_PROS2 hlf).2 a ha
    have hlfρV : rhoNode1_p2 FF a ∈ V := by
      simpa using LOCAL_FAN_ITER_RHO_NODE_IN_V hlf ha 1
    have hunion : (({0} : Set V3) ∪ {a, b}) = ({0, a, b} : Set V3) := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hsub_at : ({a, t} : Set V3) ⊆ V := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact htV
    rcases CVLF_COLLINEAR_CIRCULAR_LUNAR (v := a) (w := t) hcl hsub_at hcol
        (Ne.symm hta) with hcirc | hlun
    · -- circular branch: `KCHMAMG` puts everything in one plane `A`;
      -- the open cone point `y` is in `A`, so its azimuth is `0` or `π`,
      -- while the wedge membership forces it into `(0, π)`.
      obtain ⟨hpi, A, hAplane, h0A, hVA, _⟩ := KCHMAMG hcl hcirc
      have hangle_pi : azim 0 a (rhoNode1_p2 FF a) (ivsRhoNode1_p2 FF a) = Real.pi := by
        simpa [interiorAngle1_p2] using hpi a ha
      have hsubAB : ({0, a, b} : Set V3) ⊆ A := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact h0A
        · exact hVA ha
        · exact hVA hb
      have hAGt : affGt ({0} : Set V3) {a, b} ⊆ A := by
        have h1 : affGt ({0} : Set V3) {a, b} ⊆
            (affineSpan ℝ (({0} : Set V3) ∪ {a, b}) : Set V3) :=
          AFF_GT_SUB_AFF_UNION _ _
        have h3 : (affineSpan ℝ ({0, a, b} : Set V3) : Set V3) ⊆ A :=
          AFF_SUB_PLANE A hAplane hsubAB
        rw [hunion] at h1
        exact h1.trans h3
      obtain ⟨y, hyGt⟩ := exists_in_aff_gt_disjoint 0 a b hdis_ab
      have hyA : y ∈ A := hAGt hyGt
      have hsub4 : ({0, a, rhoNode1_p2 FF a, y} : Set V3) ⊆ A := by
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact h0A
        · exact hVA ha
        · exact hVA hlfρV
        · exact hyA
      have hcop : Coplanar ({0, a, rhoNode1_p2 FF a, y} : Set V3) := by
        obtain ⟨u, v0, w0, -, hEq⟩ := hAplane
        rw [hEq] at hsub4
        exact ⟨u, v0, w0, hsub4⟩
      have haz := (AZIM_COND_FOR_COPLANAR 0 a (rhoNode1_p2 FF a) y).mpr hcop
      have hyW : y ∈ wedgeInFanGt_p2 (a, rhoNode1_p2 FF a) E := hsub' _ hdart hyGt
      rw [WEDGE_IN_FAN_LOFA_DETER2 hlf ha] at hyW
      simp only [wedge, Set.mem_setOf_eq] at hyW
      rw [hangle_pi] at hyW
      rcases haz with h0 | hpi'
      · linarith [hyW.2.1]
      · linarith [hyW.2.2]
    · -- lunar branch: `HKIRPEP` gives the orbit positions of `t` and `b`
      -- (`i` and `n`); compare `n` with `i`.
      obtain ⟨-, hanglepos, -, -, hi_ex, hj_ex⟩ := HKIRPEP hcl hlun
      obtain ⟨i, hi_lt, hi0, hi1, hti, himg⟩ := hi_ex
      obtain ⟨j, hj_lt, hj0, hj1, htj, hjimg⟩ := hj_ex
      have hcardij : i + j = V.ncard :=
        CARD_V_TWO_HAFL_CIRCLE hlf ha htV (Ne.symm hta) i j hti.symm htj.symm hi_lt hj_lt
      obtain ⟨n, hnlt, hnb, hnmin⟩ := POINT_PRESENTED_IN_RHOND1 hlf ha hb
      by_cases hn0 : n = 0
      · rw [hn0] at hnb
        exact hab (by simpa using hnb)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        by_cases hni : n < i
        · -- `n < i`: `b` lies in the open cone at `rho a`, so the
          -- azimuth at `rho a` is `0`, contradicting the wedge.
          have hbimg : b ∈ (fun l => (rhoNode1_p2 FF)^[l] a) ''
              {l : ℕ | 0 < l ∧ l < i} :=
            ⟨n, ⟨hnpos, hni⟩, hnb⟩
          rw [himg] at hbimg
          have hbGt : b ∈ affGt ({0, a} : Set V3) ({rhoNode1_p2 FF a} : Set V3) :=
            hbimg.1
          have heqGt : affGt ({0, a} : Set V3) ({rhoNode1_p2 FF a} : Set V3) =
              affGt ({0, a} : Set V3) ({b} : Set V3) :=
            COLL_IN_AFF_GT_AFF_GT_EQ hcollρ hbGt
          have hmono : affGt ({0} : Set V3) {b, a} ⊆
              affGt ({0, a} : Set V3) ({b} : Set V3) := by
            have hh := AFF_GT_MONO_TRANS (S := ({a} : Set V3))
              (X := ({0, a} : Set V3)) (Y := ({b} : Set V3)) (by simp)
            have h1 : (({0, a} : Set V3) \ {a}) = {0} := by
              ext x
              simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
              constructor
              · rintro ⟨hx | hx, hxa⟩
                · exact hx
                · exact absurd hx hxa
              · rintro rfl
                exact ⟨Or.inl rfl, h0a⟩
            have h2 : (({b} : Set V3) ∪ {a}) = {b, a} := by
              ext x
              simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
            rw [h1, h2] at hh
            exact hh
          obtain ⟨y, hyGt_ba⟩ := exists_in_aff_gt_disjoint 0 b a hdis_ba
          have hba : ({b, a} : Set V3) = {a, b} := Set.pair_comm b a
          have hyGt_ab : y ∈ affGt ({0} : Set V3) {a, b} := by
            rwa [hba] at hyGt_ba
          have hyGt' : y ∈ affGt ({0, a} : Set V3) ({rhoNode1_p2 FF a} : Set V3) := by
            rw [heqGt]
            exact hmono hyGt_ba
          have hcollY : ¬ Collinear ℝ ({0, a, y} : Set V3) :=
            COLL_IN_AFF_GT_TOO hcollρ hyGt'
          have haz0 : azim 0 a (rhoNode1_p2 FF a) y = 0 :=
            (azim_eq_zero_iff_alt hcollρ hcollY).mpr hyGt'
          have hyW : y ∈ wedgeInFanGt_p2 (a, rhoNode1_p2 FF a) E :=
            hsub' _ hdart hyGt_ab
          rw [WEDGE_IN_FAN_LOFA_DETER2 hlf ha] at hyW
          simp only [wedge, Set.mem_setOf_eq] at hyW
          rw [haz0] at hyW
          linarith [hyW.2.1]
        · have hile : i ≤ n := Nat.le_of_not_lt hni
          by_cases hnieq : n = i
          · -- `n = i`: then `b = t`, so `{0,a,b}` is collinear, hence the
            -- cone point `y` is collinear with `0,a` and its azimuth is `0`.
            rw [hnieq] at hnb
            have hbt : b = t := hnb.symm.trans hti.symm
            have hcol' : Collinear ℝ ({0, a, b} : Set V3) := by
              rw [hbt]
              exact hcol
            obtain ⟨y, hyGt_ab⟩ := exists_in_aff_gt_disjoint 0 a b hdis_ab
            have hySpan : y ∈ (affineSpan ℝ ({0, a, b} : Set V3) : Set V3) := by
              have h1 : affGt ({0} : Set V3) {a, b} ⊆
                  (affineSpan ℝ (({0} : Set V3) ∪ {a, b}) : Set V3) :=
                AFF_GT_SUB_AFF_UNION _ _
              rw [hunion] at h1
              exact h1 hyGt_ab
            have hyLine : y ∈ (affineSpan ℝ ({0, a} : Set V3) : Set V3) := by
              have hspan : (affineSpan ℝ ({0, a} : Set V3)) =
                  (affineSpan ℝ ({0, a, b} : Set V3)) :=
                hcol'.affineSpan_eq_of_ne (p₁ := (0:V3)) (p₂ := a)
                  (by simp) (by simp) h0a
              rw [hspan]
              exact hySpan
            have hcollY : Collinear ℝ ({0, a, y} : Set V3) := by
              have hc := collinear_insert_of_mem_affineSpan_pair (k := ℝ)
                (p₁ := y) (p₂ := (0:V3)) (p₃ := a) hyLine
              have hset : ({y, 0, a} : Set V3) = {0, a, y} := by
                ext x
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
                tauto
              rwa [hset] at hc
            have haz0 : azim 0 a (rhoNode1_p2 FF a) y = 0 := by
              rw [azim]
              exact if_pos (Or.inr hcollY)
            have hyW : y ∈ wedgeInFanGt_p2 (a, rhoNode1_p2 FF a) E :=
              hsub' _ hdart hyGt_ab
            rw [WEDGE_IN_FAN_LOFA_DETER2 hlf ha] at hyW
            simp only [wedge, Set.mem_setOf_eq] at hyW
            rw [haz0] at hyW
            linarith [hyW.2.1]
          · -- `i < n`: `b` lies in the open cone at `ivs a`, so the two
            -- azimuths coincide and the wedge's strict inequality collapses.
            have hin : i < n := lt_of_le_of_ne hile (Ne.symm hnieq)
            have hnt : 0 < n - i := Nat.sub_pos_of_lt hin
            have hltj : n - i < j := by omega
            have hbimg : b ∈ (fun l => (rhoNode1_p2 FF)^[l] t) ''
                {l : ℕ | 0 < l ∧ l < j} := by
              refine ⟨n - i, ⟨hnt, hltj⟩, ?_⟩
              have h1 : (rhoNode1_p2 FF)^[n - i] t =
                  (rhoNode1_p2 FF)^[n - i] ((rhoNode1_p2 FF)^[i] a) := by
                rw [hti]
              have h2 : (rhoNode1_p2 FF)^[n - i] ((rhoNode1_p2 FF)^[i] a) =
                  (rhoNode1_p2 FF)^[(n - i) + i] a := by
                rw [← Function.iterate_add_apply]
              have h3 : (rhoNode1_p2 FF)^[(n - i) + i] a =
                  (rhoNode1_p2 FF)^[n] a := by
                rw [Nat.sub_add_cancel hile]
              exact h1.trans (h2.trans (h3.trans hnb))
            rw [hjimg] at hbimg
            have hbGt : b ∈ affGt ({0, a} : Set V3)
                ({ivsRhoNode1_p2 FF a} : Set V3) := hbimg.1
            have hcollIvs : ¬ Collinear ℝ ({0, a, ivsRhoNode1_p2 FF a} : Set V3) :=
              LOFA_IMP_NOT_COLL_IVS hlf ha
            have heqGt2 : affGt ({0, a} : Set V3) ({ivsRhoNode1_p2 FF a} : Set V3) =
                affGt ({0, a} : Set V3) ({b} : Set V3) :=
              COLL_IN_AFF_GT_AFF_GT_EQ hcollIvs hbGt
            have hmono2 : affGt ({0} : Set V3) {a, b} ⊆
                affGt ({0, a} : Set V3) ({b} : Set V3) := by
              have hh := AFF_GT_MONO (X := ({0} : Set V3)) (Y := ({a, b} : Set V3))
                (S := ({a} : Set V3)) (by simp)
              have h1 : (({0} : Set V3) ∪ {a}) = {0, a} := by
                ext x
                simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
              have h2 : (({a, b} : Set V3) \ {a}) = {b} := by
                ext x
                simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
                constructor
                · rintro ⟨hx | hx, hxa⟩
                  · exact absurd hx hxa
                  · exact hx
                · rintro rfl
                  exact ⟨Or.inr rfl, Ne.symm hab⟩
              rw [h1, h2] at hh
              exact hh
            obtain ⟨y, hyGt_ab⟩ := exists_in_aff_gt_disjoint 0 a b hdis_ab
            have hyGt_ivs : y ∈ affGt ({0, a} : Set V3)
                ({ivsRhoNode1_p2 FF a} : Set V3) := by
              rw [heqGt2]
              exact hmono2 hyGt_ab
            have hcollY : ¬ Collinear ℝ ({0, a, y} : Set V3) :=
              COLL_IN_AFF_GT_TOO hcollIvs hyGt_ivs
            have hazEq : azim 0 a (rhoNode1_p2 FF a) y =
                azim 0 a (rhoNode1_p2 FF a) (ivsRhoNode1_p2 FF a) :=
              (azim_eq_azim_iff_alt hcollρ hcollY hcollIvs).mpr hyGt_ivs
            have hyW : y ∈ wedgeInFanGt_p2 (a, rhoNode1_p2 FF a) E :=
              hsub' _ hdart hyGt_ab
            rw [WEDGE_IN_FAN_LOFA_DETER2 hlf ha] at hyW
            simp only [wedge, Set.mem_setOf_eq] at hyW
            rw [hazEq] at hyW
            linarith [hyW.2.2]
  intro z t hz ht
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact key _ _ hv hw hvw hsub t ht
  · refine key _ _ hw hv (Ne.symm hvw) ?_ t ht
    intro x hx
    simpa [Set.pair_comm] using hsub x hx

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
              (fun i => g i * interiorAngle1_p2 0 fw ((rhoNode1_p2 FF)^[i] v))) := by
  have hcol := PROVE_THE_SLICE_ASSUMPTION hcl hv hw hvw hsub
  have h : localFan_p2 V E FF := CVX_LO_IMP_LO hcl
  exact THE_SLICING_INTO_2_LEMMA hcl h hv hw hvw hcol hsub HS hHS hfv hfw

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
