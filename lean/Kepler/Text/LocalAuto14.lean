/-
LocalAuto14: port of `scripts/local/ZLZTHIC.hl` (Flyspeck "Local Fan /
Conclusions" chapter, Lemma ZLZTHIC and its sub-library; T. Hales,
2013; 3781 lines, 0 defs + 54 theorems).

FILE MAP
  Section 0 (`_p14` encoding kit): coercion bridges for the `V3` /
  `Fin 3 → ℝ` type synonym, a collinearity characterization kit and the
  cross-product nonvanishing/orthogonality facts used by the mechanical
  theorems.
  Section 1: the 54 theorems in source order.  Small linear-algebra /
  continuity / logic lemmas are PROVED (`azim_cross_0`, `vuy1`, `vuy3`,
  `cross_independent`, `ybt_inj_0`, `ECAU_aff_ge`, `collinear_cross`,
  `REAL_CONTINUOUS_AT_DOT2`, `azim_pos_iff_nz`, `deformation_subset`,
  `real_interval_contains_0_ball`, `wedge_ge_refl`, `SKOLEM_EPSILON`,
  `projection_scale`, `IDENTIFY_AZIM_CYCLE_SIMPLE`, ...); the azim-cycle
  combinatorics, the deformation-continuity suite (`NHCXLRV`..,
  `zlz_*`, `XIV_*`) and the terminal `ZLZTHIC` keep `sorry` bodies with
  NEEDS markers.

ENCODING NOTES
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `(0 : V3)`; `x dot y` ↔
    `x ⬝ᵥ y`; `x cross y` ↔ `cross3 x y` (PackingAuto18, Mathlib
    `crossProduct` underneath); `--e` ↔ `-e`; `&0` ↔ `(0:ℝ)`; NO
    `native_decide` anywhere.
  - `collinear {a,b,c}` ↔ `Collinear ℝ ({a,b,c} : Set V3)`;
    `real_interval (a,b)` ↔ `Set.Icc a b`; `v continuous atreal t` ↔
    `ContinuousAt v t`; `real_continuous_on` ↔ `ContinuousOn`;
    `v1 continuous (atreal x)` on an interval ↔ pointwise `ContinuousAt`.
  - `wedge_ge` ↔ `wedgeGe` (PackingAuto2), `wedge` ↔ `Kepler.Geom.wedge`,
    `aff_ge/aff_gt/aff_lt` ↔ `affGe/affGt/affLt` (Geom.Aff),
    `cyclic_set` ↔ `cyclicSet` (PolyAuto1), `projection` ↔
    `PackingAuto5.projection` (note the argument order:
    HOL `projection e u` ↔ `projection u e`).
  - `azim_cycle` has NO unsuffixed importable port: `azimCycle_p14` is a
    verbatim `_p14` copy of `azimCycle_p3` (LocalAuto3, sphere.hl:414).
    NEEDS: upstream home in the sphere/fan_defs layer.
  - Fan-side vocabulary comes from LocalAuto1 (`azimInFan`, `rhoNode1`,
    `ivsRhoNode1`, `interiorAngle1`, `wedgeInFanGe`, `Generic`,
    `Deformation`, `LocalFan` (skeleton `True`), `ConvexLocalFan`);
    `LocalFan`-consuming statements are therefore carried at the
    registry strength of LocalAuto1.
  - `{u i | i <= r}` ↔ `u '' Set.Icc 0 r`; `i IN 1..r+1` ↔
    `i ∈ Set.Icc 1 (r+1)`; HOL `pairwise P (m..n)` ↔
    `Set.Pairwise (Set.Icc m n) P`; HOL `(\(i,j,k). g i j k) = dh` is
    rendered pointwise `∀ i j k, g i j k = dh (i, j, k)`.
  - Source duplicate: `azim_cycle_neg` is proved twice (hl:2828, hl:2897,
    the second re-binds the name); the rebind is kept as
    `azim_cycle_neg2_p14`.  hl:2964 has a commented-out hypothesis
    (`// &0 < ...`), kept out of `XIV_ECAU_BACK_p14`.
  - DISCHARGES convention: the terminal theorem `ZLZTHIC_p14`
    shape-matches `ZLZTHIC_concl` (LocalAuto1, appendix.hl:45); a later
    wave proving `ZLZTHIC_p14` discharges that registry `sorry`.
-/

import Kepler.Geom.AzimLemmas
import Kepler.Text.LocalAuto1
import Kepler.Text.PackingAuto5
import Kepler.Text.PolyAuto1
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p14` encoding kit -/

/-- Coercion bridge: the `V3` dot is the `Fin 3 → ℝ` dot product. -/
private theorem dot3_eq_p14 (x y : V3) :
    x ⬝ᵥ y = ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ) := rfl

/-- Coercion bridge: `cross3` is Mathlib `crossProduct` under coercion. -/
private theorem coe_cross3_p14 (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) =
      crossProduct ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ) := rfl

private theorem coe_add_p14 (x y : V3) :
    ((x + y : V3) : Fin 3 → ℝ) = ((x : V3) : Fin 3 → ℝ) + ((y : V3) : Fin 3 → ℝ) := rfl

private theorem coe_smul_p14 (t : ℝ) (x : V3) :
    ((t • x : V3) : Fin 3 → ℝ) = t • ((x : V3) : Fin 3 → ℝ) := rfl

private theorem coe_zero_p14 : (((0 : V3) : V3) : Fin 3 → ℝ) = 0 := rfl

private theorem dot3_comm_p14 (x y : V3) : x ⬝ᵥ y = y ⬝ᵥ x :=
  dotProduct_comm _ _

private theorem dot3_add_left_p14 (x y z : V3) :
    (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z := by
  rw [dot3_eq_p14, coe_add_p14]; exact add_dotProduct _ _ _

private theorem dot3_smul_left_p14 (t : ℝ) (x z : V3) :
    (t • x) ⬝ᵥ z = t * (x ⬝ᵥ z) := by
  rw [dot3_eq_p14, coe_smul_p14]; exact smul_dotProduct _ _ _

private theorem dot3_add_right_p14 (x y z : V3) :
    z ⬝ᵥ (x + y) = z ⬝ᵥ x + z ⬝ᵥ y := by
  have h1 : z ⬝ᵥ (x + y) = (x + y) ⬝ᵥ z := dot3_comm_p14 z (x + y)
  have h2 : (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z := dot3_add_left_p14 x y z
  have h3 : x ⬝ᵥ z = z ⬝ᵥ x := dot3_comm_p14 x z
  have h4 : y ⬝ᵥ z = z ⬝ᵥ y := dot3_comm_p14 y z
  rw [h1, h2, h3, h4]

private theorem dot3_smul_right_p14 (t : ℝ) (x z : V3) :
    z ⬝ᵥ (t • x) = t * (z ⬝ᵥ x) := by
  have h1 : z ⬝ᵥ (t • x) = (t • x) ⬝ᵥ z := dot3_comm_p14 z (t • x)
  have h2 : (t • x) ⬝ᵥ z = t * (x ⬝ᵥ z) := dot3_smul_left_p14 t x z
  have h3 : x ⬝ᵥ z = z ⬝ᵥ x := dot3_comm_p14 x z
  rw [h1, h2, h3]

private theorem dot3_self_zero_p14 {x : V3} (h : x ⬝ᵥ x = 0) : x = 0 := by
  have h2 : ‖x‖ ^ 2 = 0 := by rw [norm_sq_eq_dot]; exact h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

private theorem dot3_self_pos_p14 {x : V3} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have hn : ‖x‖ ≠ 0 := fun hzero => hx (norm_eq_zero.mp hzero)
  have h1 : (0:ℝ) < ‖x‖ ^ 2 := sq_pos_iff.mpr hn
  rwa [norm_sq_eq_dot] at h1

/-- Any two points are collinear. -/
private theorem collinear2_p14 (x y : V3) : Collinear ℝ ({x, y} : Set V3) := by
  refine collinear_iff_exists_forall_eq_smul_vadd _ |>.2 ⟨x, y - x, ?_⟩
  rintro z (rfl | rfl)
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private theorem collinear0_smulL_p14 (u : V3) (t : ℝ) :
    Collinear ℝ ({0, u, t • u} : Set V3) := by
  refine collinear_iff_exists_forall_eq_smul_vadd _ |>.2 ⟨0, u, ?_⟩
  rintro z (rfl | rfl | rfl)
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨t, by simp⟩

private theorem collinear0_smulR_p14 (u : V3) (t : ℝ) :
    Collinear ℝ ({0, t • u, u} : Set V3) := by
  refine collinear_iff_exists_forall_eq_smul_vadd _ |>.2 ⟨0, u, ?_⟩
  rintro z (rfl | rfl | rfl)
  · exact ⟨0, by simp⟩
  · exact ⟨t, by simp⟩
  · exact ⟨1, by simp⟩

/-- Noncollinear (with the origin) vectors are linearly independent. -/
private theorem not_collinear_dep_p14 {u0 u1 : V3}
    (h : ¬ Collinear ℝ ({0, u0, u1} : Set V3)) :
    ∀ a b : ℝ, a • u0 + b • u1 = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  by_contra hne
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb0; rw [ha, hb0] at hne; exact hne ⟨rfl, rfl⟩
    have hu1 : u1 = 0 := by
      rw [ha, zero_smul, zero_add] at hab
      rcases smul_eq_zero.mp hab with h | h
      · exact absurd h hb
      · exact h
    exact h (by rw [show u1 = 0 from hu1]; simpa using collinear2_p14 u0 0)
  · rcases eq_or_ne b 0 with hb | hb
    · have hu0 : u0 = 0 := by
        rw [hb, zero_smul, add_zero] at hab
        rcases smul_eq_zero.mp hab with h | h
        · exact absurd h ha
        · exact h
      exact h (by rw [show u0 = 0 from hu0]; simpa using collinear2_p14 0 u1)
    · have hu0 : u0 = (a⁻¹ * -b) • u1 := by
        have h5 : a • u0 = -(b • u1) := by
          rw [eq_neg_iff_add_eq_zero]; exact hab
        have h7 : a • u0 = a • ((a⁻¹ * -b) • u1) := by
          rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
          exact h5.trans (neg_smul b u1).symm
        exact smul_right_injective V3 ha h7
      apply h
      rw [hu0]
      exact collinear0_smulR_p14 u1 (a⁻¹ * -b)

/-- HOL `cross`: the cross product of noncollinear (with the origin)
vectors is nonzero. -/
private theorem cross3_ne_p14 {u0 u1 : V3} (h : ¬ Collinear ℝ ({0, u0, u1} : Set V3)) :
    cross3 u0 u1 ≠ 0 := by
  have key := not_collinear_dep_p14 h
  have hli : LinearIndependent ℝ ![((u0 : V3) : Fin 3 → ℝ), ((u1 : V3) : Fin 3 → ℝ)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hv3 : g 0 • u0 + g 1 • u1 = (0 : V3) := by
      have hvp : ((g 0 • u0 + g 1 • u1 : V3) : Fin 3 → ℝ) = ((0 : V3) : Fin 3 → ℝ) := by
        rw [coe_add_p14, coe_smul_p14, coe_smul_p14, coe_zero_p14]
        exact hg
      exact congrArg (fun w : Fin 3 → ℝ => WithLp.toLp 2 w) hvp
    obtain ⟨h0, h1⟩ := key (g 0) (g 1) hv3
    intro i
    fin_cases i
    · exact h0
    · exact h1
  intro hzero
  have hco := coe_cross3_p14 u0 u1
  have hz : crossProduct u0.ofLp u1.ofLp = 0 := by
    have t := congrArg WithLp.ofLp hzero
    rwa [coe_zero_p14, hco] at t
  have hnez : crossProduct u0.ofLp u1.ofLp ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hli
  exact hnez hz

/-- The cross product annihilates its factors. -/
private theorem cross3_dotL_p14 (u v : V3) : cross3 u v ⬝ᵥ u = 0 := by
  rw [dot3_eq_p14, coe_cross3_p14, dotProduct_comm]
  exact dot_self_cross _ _

private theorem cross3_dotR_p14 (u v : V3) : cross3 u v ⬝ᵥ v = 0 := by
  rw [dot3_eq_p14, coe_cross3_p14, dotProduct_comm]
  exact dot_cross_self _ _

private theorem inner_cross3_dotL_p14 (u v : V3) : inner ℝ (cross3 u v) u = 0 := by
  rw [inner_eq_dot]; exact cross3_dotL_p14 u v

private theorem inner_cross3_dotR_p14 (u v : V3) : inner ℝ (cross3 u v) v = 0 := by
  rw [inner_eq_dot]; exact cross3_dotR_p14 u v

private theorem inner_cross3_self_pos_p14 (u v : V3)
    (h : ¬ Collinear ℝ ({0, u, v} : Set V3)) :
    0 < inner ℝ (cross3 u v) (cross3 u v) := by
  rw [inner_eq_dot]; exact dot3_self_pos_p14 (cross3_ne_p14 h)

private theorem dot3_zero_right_p14 (x : V3) : x ⬝ᵥ (0 : V3) = 0 := by
  rw [dot3_eq_p14, coe_zero_p14]; exact dotProduct_zero _

/-- NEEDS: flyspeck `azim_cycle` (sphere.hl:414; minimal azimuth,
distance tiebreak, `W SUBSET {p}` degenerate case) — `_p14` copy of
`Kepler.Text.azimCycle_p3` (LocalAuto3); no unsuffixed importable port.
Note the repo `projection` argument order: HOL `projection (w-v) (u-v)`
↔ `projection (u - v) (w - v)`. -/
noncomputable def azimCycle_p14 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-- Extraction on an origin-line: points collinear with a nonzero `c`
and the origin lie on the span of `c`. -/
private theorem smul_of_collinear0_p14 {c v : V3} (hc : c ≠ 0)
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

/-! ## Section 1: the theorems of ZLZTHIC.hl, in source order -/

/-- HOL `NONPLANAR_OPEN` (hl:33): coplanarity is an open condition along
continuous curves.  NEEDS: continuity of the coplanarity predicate. -/
theorem NONPLANAR_OPEN_p14 (v1 v2 v3 v4 : ℝ → V3) (t : ℝ)
    (h : ¬ Coplanar ({v1 t, v2 t, v3 t, v4 t} : Set V3))
    (hc1 : ContinuousAt v1 t) (hc2 : ContinuousAt v2 t) (hc3 : ContinuousAt v3 t)
    (hc4 : ContinuousAt v4 t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t', |t - t'| < e →
      ¬ Coplanar ({v1 t', v2 t', v3 t', v4 t'} : Set V3) := by
  sorry

/-! ## w5cA helpers (W5c-A lane; inserted before consumption points) -/

/-- w5cA: collinear-with-origin vectors have vanishing cross product. -/
private theorem w5cA_collinear_cross3_eq {v w : V3}
    (h : Collinear ℝ ({0, v, w} : Set V3)) : cross3 v w = 0 := by
  by_cases hv : v = 0
  · have hpi : crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ) = 0 := by
      rw [hv, coe_zero_p14, map_zero, LinearMap.zero_apply]
    have hd : cross3 v w ⬝ᵥ (cross3 v w) = 0 := by
      rw [dot3_eq_p14, coe_cross3_p14, hpi, dotProduct_zero]
    exact dot3_self_zero_p14 hd
  obtain ⟨t, ht⟩ := smul_of_collinear0_p14 hv h
  have hpi : crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ) = 0 := by
    rw [ht, coe_smul_p14, map_smul, cross_self, smul_zero]
  have hd : cross3 v w ⬝ᵥ (cross3 v w) = 0 := by
    rw [dot3_eq_p14, coe_cross3_p14, hpi, dotProduct_zero]
  exact dot3_self_zero_p14 hd

/-- HOL `COLL_IFF_COLL_CROSS2` (hl:59).  NEEDS: cross-product collinearity
algebra. -/
theorem COLL_IFF_COLL_CROSS2_p14 (v w : V3) :
    Collinear ℝ ({0, v, w} : Set V3) ↔
      Collinear ℝ ({0, w, cross3 v w} : Set V3) := by
  constructor
  · intro h
    rw [w5cA_collinear_cross3_eq h]
    simpa using collinear2_p14 w 0
  · intro h
    by_cases hnc : Collinear ℝ ({0, v, w} : Set V3)
    · exact hnc
    · exfalso
      have hc : cross3 v w ≠ 0 := cross3_ne_p14 hnc
      have hset : Collinear ℝ ({0, cross3 v w, w} : Set V3) := by
        rw [show ({0, cross3 v w, w} : Set V3) = ({0, w, cross3 v w} : Set V3) from
          by ext z; simp; tauto]
        exact h
      obtain ⟨t, ht⟩ := smul_of_collinear0_p14 hc hset
      have hd : cross3 v w ⬝ᵥ w = 0 := cross3_dotR_p14 v w
      nth_rewrite 2 [ht] at hd
      rw [coe_smul_p14, dot3_smul_right_p14] at hd
      rcases mul_eq_zero.mp hd with h0 | hcz
      · exact hnc (by rw [ht, h0]; simpa using collinear2_p14 v 0)
      · exact absurd hcz (ne_of_gt (dot3_self_pos_p14 hc))

/-- HOL `azim_cross_0` (hl:76). -/
theorem azim_cross_0_p14 (v w : V3) (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    ¬ (azim 0 (cross3 v w) v w = 0) := by
  have hc : cross3 v w ≠ 0 := cross3_ne_p14 h
  have hv0 : v ≠ 0 := by
    intro hzero
    exact h (by rw [hzero]; simpa using collinear2_p14 0 w)
  have hw0 : w ≠ 0 := by
    intro hzero
    exact h (by rw [hzero]; simpa using collinear2_p14 v 0)
  have hncv : ¬ Collinear ℝ ({0, cross3 v w, v} : Set V3) := by
    intro hcol
    obtain ⟨t, htv⟩ := smul_of_collinear0_p14 hc hcol
    have hu0c := inner_cross3_dotL_p14 v w
    nth_rewrite 2 [htv] at hu0c
    rw [inner_smul_right] at hu0c
    rcases mul_eq_zero.mp hu0c with hzero | hczero
    · rw [hzero, zero_smul] at htv
      exact hv0 (by rw [htv])
    · linarith [hczero, inner_cross3_self_pos_p14 v w h]
  have hncw : ¬ Collinear ℝ ({0, cross3 v w, w} : Set V3) := by
    intro hcol
    obtain ⟨t, htw⟩ := smul_of_collinear0_p14 hc hcol
    have hu0c := inner_cross3_dotR_p14 v w
    nth_rewrite 2 [htw] at hu0c
    rw [inner_smul_right] at hu0c
    rcases mul_eq_zero.mp hu0c with hzero | hczero
    · rw [hzero, zero_smul] at htw
      exact hw0 (by rw [htw])
    · linarith [hczero, inner_cross3_self_pos_p14 v w h]
  intro haz
  rw [azim_eq_zero_iff hncv hncw] at haz
  have hwc : w ≠ cross3 v w := by
    intro heq
    exact hncw (by rw [← heq]; simpa using collinear0_smulR_p14 w 1)
  obtain ⟨a, ha, k, hvk⟩ :=
    (affGt_pair_iff (v0 := 0) (v1 := cross3 v w) (x := w) (y := v)
      (Ne.symm hc) hw0 hwc).mp haz
  have hvk' : v = a • w + k • cross3 v w := by simpa only [sub_zero] using hvk
  have hperp := inner_cross3_dotL_p14 v w
  nth_rewrite 2 [hvk'] at hperp
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_cross3_dotR_p14,
    mul_zero, zero_add] at hperp
  rcases mul_eq_zero.mp hperp with hzero | hczero
  · rw [hzero, zero_smul, add_zero] at hvk'
    exact h (by rw [hvk']; exact collinear0_smulR_p14 w a)
  · linarith [hczero, inner_cross3_self_pos_p14 v w h]

/-- HOL `wedge_ge_cross` (hl:85).  NEEDS: wedge characterization. -/
theorem wedge_ge_cross_p14 (v w : V3) (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    wedgeGe 0 (cross3 v w) v w = affGe ({0, cross3 v w} : Set V3) ({v, w} : Set V3) := by
  sorry

/-- HOL `azim_lt_pi_cross` (hl:107).  NEEDS: azim sign theory. -/
theorem azim_lt_pi_cross_p14 (u1 u2 u3 : V3) :
    (0 < azim 0 u1 u2 u3 ∧ azim 0 u1 u2 u3 < Real.pi) ↔
      0 < (cross3 u1 u2) ⬝ᵥ u3 := by
  sorry

/-- HOL `generic_alt` (hl:142).  NEEDS: generic wedge theory. -/
theorem generic_alt_p14 (u v w : V3) (h1 : ¬ Collinear ℝ ({0, v, w} : Set V3))
    (h2 : u ≠ 0) :
    affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affLt ({0} : Set V3) ({u} : Set V3) = ∅ ↔
      ¬ Coplanar ({0, u, v, w} : Set V3) ∨ (-u) ∈ Kepler.Geom.wedge 0 (cross3 v w) w v := by
  sorry

/-- HOL `vuy1` (hl:264). -/
theorem vuy1_p14 (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    ∃ t0 t1 : ℝ, 0 < t1 ∧ v = t0 • u0 + t1 • u1 := by
  obtain ⟨f, hfin, hsum, hge, hone⟩ := h3
  have h00 : u0 ≠ 0 := by
    intro heq; rw [heq] at h2; exact h2 (by simpa using collinear2_p14 0 u1)
  have h01 : u1 ≠ 0 := by
    intro heq; rw [heq] at h2; exact h2 (by simpa using collinear2_p14 u0 0)
  have h10 : u1 ≠ u0 := by
    intro heq; rw [heq] at h2; exact h2 (by simpa using collinear2_p14 0 u0)
  have h3f : hfin.toFinset = ({u1, 0, u0} : Finset V3) := by
    apply Finset.ext
    intro z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h3f] at hsum hone
  have hu1nin : u1 ∉ ({0, u0} : Finset V3) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact h01 h
    · exact h10 (Finset.mem_singleton.mp h)
  have hu0nin : 0 ∉ ({u0} : Finset V3) := fun h => h00 (Finset.mem_singleton.mp h).symm
  rw [Finset.sum_insert hu1nin, Finset.sum_insert hu0nin, Finset.sum_singleton] at hsum hone
  simp only [smul_zero, zero_add] at hsum
  have hf1 : 0 < f u1 := by
    by_contra hcon
    push_neg at hcon
    have hfu1 : f u1 = 0 := le_antisymm hcon (hge u1 rfl)
    rw [hfu1, zero_smul, zero_add] at hsum
    exact h1 (by rw [hsum]; exact collinear0_smulL_p14 u0 (f u0))
  refine ⟨f u0, f u1, hf1, ?_⟩
  rw [hsum]
  exact add_comm _ _

/-- HOL `vuy3` (hl:292). -/
theorem vuy3_p14 (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    ¬ Collinear ℝ ({0, cross3 u0 u1, v} : Set V3) := by
  obtain ⟨t0, t1, ht1, hv⟩ := vuy1_p14 v u0 u1 h1 h2 h3
  have hcne : cross3 u0 u1 ≠ 0 := cross3_ne_p14 h2
  intro hcol
  obtain ⟨s, hs⟩ := smul_of_collinear0_p14 hcne hcol
  have hperp : inner ℝ (cross3 u0 u1) v = 0 := by
    rw [hv, inner_add_right, inner_smul_right, inner_smul_right, inner_cross3_dotL_p14,
      inner_cross3_dotR_p14]
    ring
  rw [hs] at hperp
  rw [inner_smul_right] at hperp
  rcases mul_eq_zero.mp hperp with hzero | hczero
  · rw [hzero, zero_smul] at hs
    exact h1 (by rw [hs]; simpa using collinear2_p14 u0 0)
  · exact (dot3_self_pos_p14 hcne).ne' hczero

/-- HOL `vuy4` (hl:319).  NEEDS: azim range theory. -/
theorem vuy4_p14 (v u0 u1 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h3 : v ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    azim 0 (cross3 u0 u1) u0 v < Real.pi := by
  sorry

/-- HOL `cross_independent` (hl:340). -/
theorem cross_independent_p14 (u0 u1 : V3) (h : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (a b c : ℝ) (heq : a • cross3 u0 u1 + b • u0 + c • u1 = 0) : a = 0 := by
  by_contra hac
  have hcne : cross3 u0 u1 ≠ 0 := cross3_ne_p14 h
  have hdot : inner ℝ (cross3 u0 u1) (a • cross3 u0 u1 + b • u0 + c • u1) = 0 := by
    rw [heq]; exact inner_zero_right _
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_cross3_dotL_p14, inner_cross3_dotR_p14, mul_zero, mul_zero,
    add_zero, add_zero] at hdot
  rcases mul_eq_zero.mp hdot with h0 | hczero
  · exact hac h0
  · linarith [hczero, inner_cross3_self_pos_p14 u0 u1 h]

/-- HOL `ybt_inj` (hl:358).  NEEDS: azimuth injectivity on the cone. -/
theorem ybt_inj_p14 (u0 u1 v1 v2 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v1} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, v2} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h4 : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (h5 : v1 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3))
    (h6 : v2 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    ¬ (azim 0 (cross3 u0 u1) u0 v1 = azim 0 (cross3 u0 u1) u0 v2) := by
  sorry

/-- HOL `ybt_inj_0` (hl:428). -/
theorem ybt_inj_0_p14 (u0 u1 v2 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v2} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h3 : v2 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    ¬ (azim 0 (cross3 u0 u1) u0 v2 = 0) := by
  obtain ⟨t0, t1, ht1, hv2⟩ := vuy1_p14 v2 u0 u1 h1 h2 h3
  have hcne : cross3 u0 u1 ≠ 0 := cross3_ne_p14 h2
  have hv20 : v2 ≠ 0 := by
    intro hzero
    exact h1 (by rw [hzero]; simpa using collinear2_p14 u0 0)
  have hcv2 : inner ℝ (cross3 u0 u1) v2 = 0 := by
    rw [hv2, inner_add_right, inner_smul_right, inner_smul_right, inner_cross3_dotL_p14,
      inner_cross3_dotR_p14]
    ring
  have hncu0 : ¬ Collinear ℝ ({0, cross3 u0 u1, u0} : Set V3) := by
    intro hcol
    obtain ⟨t, htu0⟩ := smul_of_collinear0_p14 hcne hcol
    have hu0c := inner_cross3_dotL_p14 u0 u1
    nth_rewrite 2 [htu0] at hu0c
    rw [inner_smul_right] at hu0c
    rcases mul_eq_zero.mp hu0c with hzero | hczero
    · rw [hzero, zero_smul] at htu0
      exact h2 (by rw [htu0]; simpa using collinear2_p14 0 u1)
    · linarith [hczero, inner_cross3_self_pos_p14 u0 u1 h2]
  have hncv2 : ¬ Collinear ℝ ({0, cross3 u0 u1, v2} : Set V3) := by
    intro hcol
    obtain ⟨t, htv2⟩ := smul_of_collinear0_p14 hcne hcol
    rw [htv2] at hcv2
    rw [inner_smul_right] at hcv2
    rcases mul_eq_zero.mp hcv2 with hzero | hczero
    · rw [hzero, zero_smul] at htv2
      exact h1 (by rw [htv2]; simpa using collinear2_p14 u0 0)
    · linarith [hczero, inner_cross3_self_pos_p14 u0 u1 h2]
  intro haz
  rw [azim_eq_zero_iff hncu0 hncv2] at haz
  have hv2c : v2 ≠ cross3 u0 u1 := by
    intro heq
    rw [heq] at hcv2
    exact (dot3_self_pos_p14 hcne).ne' hcv2
  obtain ⟨a, ha, k, hu0k⟩ :=
    (affGt_pair_iff (v0 := 0) (v1 := cross3 u0 u1) (x := v2) (y := u0)
      (Ne.symm hcne) hv20 hv2c).mp haz
  have hu0k' : u0 = a • v2 + k • cross3 u0 u1 := by simpa only [sub_zero] using hu0k
  have hperp := inner_cross3_dotL_p14 u0 u1
  nth_rewrite 2 [hu0k'] at hperp
  rw [inner_add_right, inner_smul_right, inner_smul_right, hcv2, mul_zero, zero_add] at hperp
  rcases mul_eq_zero.mp hperp with hzero | hczero
  · rw [hzero, zero_smul, add_zero] at hu0k'
    exact h1 (by rw [hu0k']; exact collinear0_smulR_p14 v2 a)
  · linarith [hczero, inner_cross3_self_pos_p14 u0 u1 h2]

/-- HOL `ECAU_aff_ge` (hl:478). -/
theorem ECAU_aff_ge_p14 (u : ℝ → V3) (r : ℕ)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3)) :
    ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGe ({0, u 0} : Set V3) ({u 1} : Set V3) := by
  intro i hi hir
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := h2 i hi hir
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- HOL `collinear_cross` (hl:493). -/
theorem collinear_cross_p14 (u : ℕ → V3) (i r : ℕ) (hi : i ≤ r) (hr : 1 ≤ r)
    (h : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (hu : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3)) :
    ¬ Collinear ℝ ({0, cross3 (u 0) (u 1), u i} : Set V3) := by
  have h00 : u 0 ≠ 0 := by
    intro heq
    exact h 0 1 (by omega) (by omega) (by omega) (by rw [heq]; simpa using collinear2_p14 0 (u 1))
  have h01 : u 1 ≠ 0 := by
    intro heq
    exact h 0 1 (by omega) (by omega) (by omega) (by rw [heq]; simpa using collinear2_p14 (u 0) 0)
  have h10 : u 1 ≠ u 0 := by
    intro heq
    exact h 1 0 (by omega) (by omega) (by omega) (by rw [heq]; simpa using collinear2_p14 0 (u 0))
  by_cases hiz : i = 0
  · subst hiz
    intro hcol
    have hcne : cross3 (u 0) (u 1) ≠ 0 :=
      cross3_ne_p14 (h 0 1 (by omega) (by omega) (by omega))
    obtain ⟨t, ht⟩ := smul_of_collinear0_p14 hcne hcol
    have hperp := inner_cross3_dotL_p14 (u 0) (u 1)
    nth_rewrite 2 [ht] at hperp
    rw [inner_smul_right] at hperp
    rcases mul_eq_zero.mp hperp with hzero | hczero
    · rw [hzero, zero_smul] at ht
      exact h 0 1 (by omega) (by omega) (by omega) (by rw [ht]; simpa using collinear2_p14 0 (u 1))
    · linarith [hczero, inner_cross3_self_pos_p14 (u 0) (u 1) (h 0 1 (by omega) (by omega) (by omega))]
  · have hi1 : 1 ≤ i := by omega
    intro hcol
    obtain ⟨a, ha, k, huik⟩ :=
      (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := u i)
        (Ne.symm h00) h01 h10).mp (hu i hi1 hi)
    simp only [sub_zero] at huik
    have hperp : inner ℝ (cross3 (u 0) (u 1)) (u i) = 0 := by
      nth_rewrite 1 [huik]
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        inner_cross3_dotR_p14, inner_cross3_dotL_p14]
      ring
    obtain ⟨t, ht⟩ := smul_of_collinear0_p14
      (cross3_ne_p14 (h 0 1 (by omega) (by omega) (by omega))) hcol
    nth_rewrite 1 [ht] at hperp
    rw [inner_smul_right] at hperp
    rcases mul_eq_zero.mp hperp with hzero | hczero
    · rw [hzero, zero_smul] at ht
      exact h i 0 hi (by omega) (by omega) (by rw [ht]; simpa using collinear2_p14 0 (u 0))
    · linarith [hczero, inner_cross3_self_pos_p14 (u 0) (u 1)
        (h 0 1 (by omega) (by omega) (by omega))]

/-- HOL `YBTASCZ1` (hl:516).  NEEDS: azimuth-cycle ordering kit. -/
theorem YBTASCZ1_p14 (u : ℕ → V3) (r j : ℕ) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    ∀ i, i < j →
      azim 0 (cross3 (u 0) (u 1)) (u 0) (u i) < azim 0 (cross3 (u 0) (u 1)) (u 0) (u j) := by
  sorry

/-- HOL `YBTASCZ2` (hl:624).  NEEDS: azimuth-cycle ordering kit. -/
theorem YBTASCZ2_p14 (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (cross3 (u 0) (u 1)) (u i) (u j) < Real.pi := by
  sorry

/-- HOL `YBTASCZ3` (hl:656).  NEEDS: azimuth-cycle ordering kit. -/
theorem YBTASCZ3_p14 (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    0 < azim 0 (cross3 (u 0) (u 1)) (u i) (u j) := by
  sorry

/-- HOL `KCZXLLE` (hl:681).  NEEDS: azimuth-cycle ordering kit. -/
theorem KCZXLLE_p14 (u : ℕ → V3) (r i j k : ℕ) (hjk : j < k) (hk : k ≤ r) (hr : 1 ≤ r)
    (hii : i ≤ r) (hijk : i < j ∨ k < i)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  sorry

/-- HOL `KCZXLLE_SYM` (hl:931).  NEEDS: azimuth-cycle ordering kit. -/
theorem KCZXLLE_SYM_p14 (u : ℕ → V3) (r i j k : ℕ) (hk : k ≤ r) (hj : j ≤ r) (hr : 1 ≤ r)
    (hi : i ≤ r) (hord : (j < k ∧ (i < j ∨ k < i)) ∨ (k < j ∧ (i < k ∨ j < i)))
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  sorry

/-- w5cA: a 2-vector family spans something of finrank 2 when linearly
independent. -/
private theorem w5cA_finrank_span_range_two {a b : V3}
    (hind : LinearIndependent ℝ ![a, b]) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range ![a, b])) = 2 := by
  rw [finrank_span_eq_card hind]
  norm_num

/-- HOL `coplanar_in_affine_hull` (hl:960; HOL real^A rendered at V3).
NEEDS: affine-dimension theory. -/
theorem coplanar_in_affine_hull_p14 (u v w x : V3)
    (h1 : ¬ Collinear ℝ ({u, v, w} : Set V3)) (h2 : Coplanar ({x, u, v, w} : Set V3)) :
    x ∈ affineSpan ℝ ({u, v, w} : Set V3) := by
  obtain ⟨p, q, r, hsub⟩ := h2
  set A : AffineSubspace ℝ V3 := affineSpan ℝ ({p, q, r} : Set V3) with hAdef
  set B : AffineSubspace ℝ V3 := affineSpan ℝ ({u, v, w} : Set V3) with hBdef
  have huA : u ∈ A := hsub (by simp)
  have hBA : B ≤ A := affineSpan_le.mpr (fun z hz => hsub (by rcases hz with rfl | rfl | rfl <;> simp))
  have hind : LinearIndependent ℝ ![v - u, w - u] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
    simp only [Fin.forall_fin_two, Fin.forall_fin_one]
    refine ⟨?_, ?_⟩
    · by_contra h0
      apply h1
      have hkey := eq_neg_of_add_eq_zero_left hg
      have hkey2 : v - u = ((g 0)⁻¹ * -(g 1)) • (w - u) := by
        apply smul_right_injective V3 h0
        show (g 0) • (v - u) = (g 0) • (((g 0)⁻¹ * -(g 1)) • (w - u))
        rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
        exact hkey.trans (neg_smul (g 1) (w - u)).symm
      refine collinear_iff_exists_forall_eq_smul_vadd _ |>.2 ⟨u, w - u, ?_⟩
      rintro z (hz1 | hz1 | hz1)
      · exact ⟨0, by rw [hz1]; simp⟩
      · refine ⟨(g 0)⁻¹ * -(g 1), ?_⟩
        have hzz : v = (v - u) + u := by abel
        rw [hz1, hzz, hkey2, vadd_eq_add]
      · exact ⟨1, by rw [hz1]; simp⟩
    · by_contra h1'
      apply h1
      have hkey := eq_neg_of_add_eq_zero_right hg
      have hkey2 : w - u = ((g 1)⁻¹ * -(g 0)) • (v - u) := by
        apply smul_right_injective V3 h1'
        show (g 1) • (w - u) = (g 1) • (((g 1)⁻¹ * -(g 0)) • (v - u))
        rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ h1', one_mul]
        exact hkey.trans (neg_smul (g 0) (v - u)).symm
      refine collinear_iff_exists_forall_eq_smul_vadd _ |>.2 ⟨u, v - u, ?_⟩
      rintro z (hz1 | hz1 | hz1)
      · exact ⟨0, by rw [hz1]; simp⟩
      · exact ⟨1, by rw [hz1]; simp⟩
      · refine ⟨(g 1)⁻¹ * -(g 0), ?_⟩
        have hzz : w = (w - u) + u := by abel
        rw [hz1, hzz, hkey2, vadd_eq_add]
  have hfr2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![v - u, w - u])) = 2 :=
    w5cA_finrank_span_range_two hind
  have hspanB : Submodule.span ℝ (Set.range ![v - u, w - u]) ≤ B.direction := by
    rw [Submodule.span_le]
    rintro d ⟨i, hi, rfl⟩
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      exact AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ (by simp)) (mem_affineSpan ℝ (by simp))
  have hdBA : B.direction ≤ A.direction := by
    rw [hBdef, direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro d ⟨z, hz, y, hy, rfl⟩
    exact AffineSubspace.vsub_mem_direction (hsub (by rcases hz with rfl | rfl | rfl <;> simp))
      (hsub (by rcases hy with rfl | rfl | rfl <;> simp))
  have hdA : A.direction ≤ Submodule.span ℝ ({q - p, r - p} : Set V3) := by
    rw [hAdef, direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro d ⟨a, ha, b, hb, rfl⟩
    rcases ha with hp | hq | hr
    · rcases hb with hp' | hq' | hr'
      · rw [hp, hp']
        simp only [vsub_eq_sub, sub_self]
        exact Submodule.zero_mem _
      · rw [hp, hq']
        simp only [vsub_eq_sub]
        rw [show (p : V3) - q = (-1 : ℝ) • (q - p) from by module]
        exact Submodule.smul_mem _ (-1) (Submodule.subset_span (by simp))
      · rw [hp, hr']
        simp only [vsub_eq_sub]
        rw [show (p : V3) - r = (-1 : ℝ) • (r - p) from by module]
        exact Submodule.smul_mem _ (-1) (Submodule.subset_span (by simp))
    · rcases hb with hp' | hq' | hr'
      · rw [hq, hp']
        simp only [vsub_eq_sub]
        exact Submodule.subset_span (by simp)
      · rw [hq, hq']
        simp only [vsub_eq_sub, sub_self]
        exact Submodule.zero_mem _
      · rw [hq, hr']
        simp only [vsub_eq_sub]
        have hqeq : (q : V3) - r = (q - p) - (r - p) := by abel
        rw [hqeq]
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
    · rcases hb with hp' | hq' | hr'
      · rw [hr, hp']
        simp only [vsub_eq_sub]
        exact Submodule.subset_span (by simp)
      · rw [hr, hq']
        simp only [vsub_eq_sub]
        have hrq : (r : V3) - q = (r - p) - (q - p) := by abel
        rw [hrq]
        exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
      · rw [hr, hr']
        simp only [vsub_eq_sub, sub_self]
        exact Submodule.zero_mem _
  have hfrA : Module.finrank ℝ A.direction
      ≤ Module.finrank ℝ (Submodule.span ℝ ({q - p, r - p} : Set V3)) :=
    Submodule.finrank_mono hdA
  have hfrA2 : Module.finrank ℝ (Submodule.span ℝ ({q - p, r - p} : Set V3)) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) ({q - p, r - p} : Finset V3)
    unfold Set.finrank at h
    rw [show (({q - p, r - p} : Finset V3) : Set V3) = ({q - p, r - p} : Set V3) from
      by ext z; simp] at h
    have hcard : (({q - p, r - p} : Finset V3)).card ≤ 2 := by
      have h2c := Finset.card_insert_le (q - p) ({r - p} : Finset V3)
      rw [Finset.card_singleton] at h2c
      simpa using h2c
    exact le_trans h hcard
  have hfrB : Module.finrank ℝ (Submodule.span ℝ (Set.range ![v - u, w - u]))
      ≤ Module.finrank ℝ B.direction := Submodule.finrank_mono hspanB
  have h2 : Module.finrank ℝ B.direction ≤ Module.finrank ℝ A.direction :=
    Submodule.finrank_mono hdBA
  have h3 : Module.finrank ℝ A.direction ≤ 2 := le_trans hfrA hfrA2
  have hfdB : Module.finrank ℝ B.direction = 2 :=
    le_antisymm (h2.trans h3) (hfr2.symm.le.trans hfrB)
  have hfdA : Module.finrank ℝ A.direction = 2 :=
    le_antisymm h3 (hfdB.symm.le.trans h2)
  have hdir : B.direction = A.direction :=
    Submodule.eq_of_le_of_finrank_eq hdBA (by rw [hfdB]; exact hfdA.symm)
  have hABeq : A = B := by
    ext z
    constructor
    · intro hz
      have hd : z -ᵥ u ∈ B.direction := by
        rw [hdir]
        exact AffineSubspace.vsub_mem_direction hz huA
      have hzv : z = (z -ᵥ u) +ᵥ u := by rw [vsub_vadd]
      rw [hzv]
      exact AffineSubspace.vadd_mem_of_mem_direction hd
        (mem_affineSpan ℝ (by simp))
    · intro hz
      exact hBA hz
  rw [← hABeq]
  exact hsub (by simp)

/-- HOL `azim_0_as_closed` (hl:972).  NEEDS: azim-zero coplanarity theory. -/
theorem azim_0_as_closed_p14 (v2 v3 v4 : V3)
    (h1 : ¬ Collinear ℝ ({0, v2, v3} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, v2, v4} : Set V3)) :
    azim 0 v2 v3 v4 = 0 ↔
      Coplanar ({0, v2, v3, v4} : Set V3) ∧
        0 ≤ (cross3 (cross3 v2 v3) v2) ⬝ᵥ v4 := by
  sorry

/-- HOL `REAL_CONTINUOUS_AT_DOT2` (hl:1057; HOL `real^A` rendered as a real
inner product space; HOL `dot` ↔ `inner ℝ`). -/
theorem REAL_CONTINUOUS_AT_DOT2_p14 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f g : ℝ → E) (x : ℝ)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => inner ℝ (f x) (g x)) x :=
  hf.inner hg

/-- HOL `azim_pos_open` (hl:1071).  NEEDS: azim continuity. -/
theorem azim_pos_open_p14 (v2 v3 v4 : ℝ → V3) (t a b : ℝ)
    (h1 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v2 x)
    (h2 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v3 x)
    (h3 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v4 x)
    (h4 : t ∈ Set.Icc a b)
    (h5 : ¬ Collinear ℝ ({0, v2 t, v3 t} : Set V3))
    (h6 : ¬ Collinear ℝ ({0, v2 t, v4 t} : Set V3))
    (h7 : ¬ (azim 0 (v2 t) (v3 t) (v4 t) = 0)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t', |t' - t| < e →
      ¬ (azim 0 (v2 t') (v3 t') (v4 t') = 0) := by
  sorry

/-- HOL `azim_real_continuous_on` (hl:1141).  NEEDS: azim continuity. -/
theorem azim_real_continuous_on_p14 (v2 v3 v4 : ℝ → V3) (t a b : ℝ)
    (h1 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v2 x)
    (h2 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v3 x)
    (h3 : ∀ x, x ∈ Set.Icc a b → ContinuousAt v4 x)
    (h4 : t ∈ Set.Icc a b)
    (h5 : ¬ Collinear ℝ ({0, v2 t, v3 t} : Set V3))
    (h6 : ¬ Collinear ℝ ({0, v2 t, v4 t} : Set V3))
    (h7 : ¬ (azim 0 (v2 t) (v3 t) (v4 t) = 0)) :
    ∃ e : ℝ, 0 < e ∧
      ContinuousOn (fun q => azim 0 (v2 q) (v3 q) (v4 q)) (Set.Icc (t - e) (t + e)) := by
  sorry

/-- HOL `azim_pos_iff_nz` (hl:1198). -/
theorem azim_pos_iff_nz_p14 (v1 v2 v3 v4 : V3) :
    0 < azim v1 v2 v3 v4 ↔ azim v1 v2 v3 v4 ≠ 0 := by
  constructor
  · intro h h0
    exact lt_irrefl _ (h0 ▸ h)
  · intro h
    rcases lt_or_eq_of_le (azim_nonneg v1 v2 v3 v4) with h' | h'
    · exact h'
    · exact absurd h'.symm h

/-- HOL `NHCXLRV` (hl:1209).  NEEDS: deformation wedge-persistence. -/
theorem NHCXLRV_p14 (v w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
    (h1 : Deformation f ({w0, w1, w2, v} : Set V3) a b)
    (h2 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3))
    (h4 : ¬ Collinear ℝ ({0, f w1 0, f v 0} : Set V3))
    (h5 : v ∈ Kepler.Geom.wedge 0 w1 w2 w0) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      f v t ∈ Kepler.Geom.wedge 0 (f w1 t) (f w2 t) (f w0 t) := by
  sorry

/-- HOL `NHCXLRV_ALT` (hl:1268; the `f w (§0) = w`-rewritten variant).
NEEDS: deformation wedge-persistence. -/
theorem NHCXLRV_ALT_p14 (v w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
    (h1 : Deformation f ({w0, w1, w2, v} : Set V3) a b)
    (h2 : ¬ Collinear ℝ ({0, w1, w2} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, w1, w0} : Set V3))
    (h4 : ¬ Collinear ℝ ({0, w1, v} : Set V3))
    (h5 : v ∈ Kepler.Geom.wedge 0 w1 w2 w0) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      f v t ∈ Kepler.Geom.wedge 0 (f w1 t) (f w2 t) (f w0 t) := by
  sorry

/-- HOL `WNWSHJT` (hl:1295).  NEEDS: azim continuity + deformation kit. -/
theorem WNWSHJT_p14 (w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
    (h1 : Deformation f ({w0, w1, w2} : Set V3) a b)
    (h2 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3))
    (h4 : 0 < azim 0 w1 w2 w0) (h5 : azim 0 w1 w2 w0 < Real.pi) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      azim 0 (f w1 t) (f w2 t) (f w0 t) < Real.pi := by
  sorry

/-- HOL `LOFA_IMP_INANGLE_EQ_AZIM` (hl:1325).  NEEDS: fan structure
(`LocalFan` is the LocalAuto1 skeleton). -/
theorem LOFA_IMP_INANGLE_EQ_AZIM_p14 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (h1 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (h2 : v ∈ V) :
    interiorAngle1 0 FF v = azimInFan (v, rhoNode1 FF v) E := by
  sorry

/-- HOL `deformation_rho_node1_equivariant1` (hl:1353).  NEEDS: fan
structure + deformation theory. -/
theorem deformation_rho_node1_equivariant1_p14 (f : V3 → ℝ → V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
    (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V) :
    f (rhoNode1 FF v) t =
      rhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) := by
  sorry

/-- HOL `deformation_ivs_rho_node1_equivariant1` (hl:1381).  NEEDS: fan
structure + deformation theory. -/
theorem deformation_ivs_rho_node1_equivariant1_p14 (f : V3 → ℝ → V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
    (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V) :
    f (ivsRhoNode1 FF v) t =
      ivsRhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) := by
  sorry

/-- HOL `deformation_subset` (hl:1409). -/
theorem deformation_subset_p14 (f : V3 → ℝ → V3) (U V : Set V3) (a b : ℝ)
    (hsub : U ⊆ V) (h : Deformation f V a b) : Deformation f U a b := by
  obtain ⟨h0, hc, hf⟩ := h
  exact ⟨h0, fun v hv => hc v (hsub hv), fun v hv => hf v (hsub hv)⟩

/-- HOL `zlz_reduction` (hl:1418).  NEEDS: the terminal deformation
theorem (giants `zlz_azim`/`zlz_generic`/`zlz_wedge_*` below). -/
theorem zlz_reduction_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi)
    (h5 : ∀ u v w : V3, ∃ e4 : ℝ, ((v, w) ∈ FF ∧ u ∈ V) →
      0 < e4 ∧ ∀ t, -e4 < t ∧ t < e4 →
        affGe ({0} : Set V3) ({f v t, f w t} : Set V3) ∩
          affLt ({0} : Set V3) ({f u t} : Set V3) = ∅)
    (h6 : ∀ x : V3 × V3, ∃ e3 : ℝ, x ∈ FF →
      0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
        ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
          ((fun s => (fun v => f v t) '' s) '' E))
    (h7 : ∀ x : V3 × V3, ∃ e2 : ℝ, x ∈ FF →
      0 < e2 ∧ ∀ t, -e2 < t ∧ t < e2 →
        azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Generic ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

/-- HOL `real_interval_contains_0_ball` (hl:1647). -/
theorem real_interval_contains_0_ball_p14 (a b e1 : ℝ) (ha : a < 0) (hb : 0 < b)
    (he1 : 0 < e1) :
    ∃ e : ℝ, 0 < e ∧ e ≤ e1 ∧ ∀ t, |t| < e → t ∈ Icc a b := by
  have hb2 : (0:ℝ) < min (-a) b := lt_min (by linarith) hb
  have hM0 : (0:ℝ) ≤ min e1 (min (-a) b) := le_min (le_of_lt he1) (le_of_lt hb2)
  refine ⟨min e1 (min (-a) b) / 2, by positivity, ?_, ?_⟩
  · exact le_trans (div_le_self hM0 (by norm_num : (1:ℝ) ≤ 2)) (min_le_left _ _)
  · intro t ht
    have hmin : min e1 (min (-a) b) / 2 ≤ min (-a) b :=
      le_trans (div_le_self hM0 (by norm_num : (1:ℝ) ≤ 2)) (min_le_right _ _)
    have hlt : |t| < min (-a) b := lt_of_lt_of_le ht hmin
    rw [mem_Icc]
    have habs := abs_lt.mp hlt
    exact ⟨le_of_lt (by linarith [habs.left, min_le_left (-a) b]),
      le_of_lt (lt_of_lt_of_le habs.right (min_le_right _ _))⟩

/-- HOL `zlz_azim` (hl:1664).  NEEDS: terminal deformation theory. -/
theorem zlz_azim_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ x : V3 × V3, ∃ e2 : ℝ, x ∈ FF →
      0 < e2 ∧ ∀ t, -e2 < t ∧ t < e2 →
        azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi := by
  sorry

/-- HOL `zlz_generic` (hl:1852).  NEEDS: terminal deformation theory. -/
theorem zlz_generic_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b) :
    ∀ u v w : V3, ∃ e4 : ℝ, ((v, w) ∈ FF ∧ u ∈ V) →
      0 < e4 ∧ ∀ t, -e4 < t ∧ t < e4 →
        affGe ({0} : Set V3) ({f v t, f w t} : Set V3) ∩
          affLt ({0} : Set V3) ({f u t} : Set V3) = ∅ := by
  sorry

/-- HOL `zlz_wedge_skolem` (hl:2007).  NEEDS: terminal deformation
theory. -/
theorem zlz_wedge_skolem_p14 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3) (h1 : ConvexLocalFan V E FF)
    (h2 : ∀ x : V3 × V3, ∀ v : V3, ∃ e3 : ℝ, (x ∈ FF ∧ v ∈ V) →
      0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
        f v t ∈ wedgeInFanGe (f x.1 t, f x.2 t)
          ((fun s => (fun v => f v t) '' s) '' E)) :
    ∀ x : V3 × V3, ∃ e3 : ℝ, x ∈ FF →
      0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
        ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
          ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

/-- HOL `wedge_ge_refl` (hl:2076). -/
theorem wedge_ge_refl_p14 (v1 v2 v3 v4 : V3) : v2 ∈ wedgeGe v1 v2 v3 v4 := by
  have hcol : Collinear ℝ ({v1, v2, v2} : Set V3) := by
    simpa using collinear2_p14 v1 v2
  show 0 ≤ azim v1 v2 v3 v2 ∧ azim v1 v2 v3 v2 ≤ azim v1 v2 v3 v4
  have h0 : azim v1 v2 v3 v2 = 0 := by
    unfold azim
    split
    · rfl
    · rename_i hc
      exact absurd (Or.inr hcol) hc
  rw [h0]
  exact ⟨le_refl 0, azim_nonneg v1 v2 v3 v4⟩

/-- HOL `zlz_wedge_refl` (hl:2085).  NEEDS: terminal deformation theory. -/
theorem zlz_wedge_refl_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ v w : V3, w ∈ V → v ∈ ({w, rhoNode1 FF w, ivsRhoNode1 FF w} : Set V3) →
      ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t ∧ t < e →
        f v t ∈ wedgeInFanGe (f w t, f (rhoNode1 FF w) t)
          ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

/-- HOL `zlz_wedge_open` (hl:2133).  NEEDS: terminal deformation theory. -/
theorem zlz_wedge_open_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ v w : V3, v ∈ V → w ∈ V →
      v ∈ Kepler.Geom.wedge 0 w (rhoNode1 FF w) (ivsRhoNode1 FF w) →
      ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t ∧ t < e →
        f v t ∈ wedgeInFanGe (f w t, f (rhoNode1 FF w) t)
          ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

/-- HOL `PROPERTIES_GENERIC_LOCAL_FAN_ALT` (hl:2217).  NEEDS: fan
structure (`LocalFan` skeleton) + generic theory. -/
theorem PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (u v : V3) (h1 : LocalFan V E FF) (h2 : u ∈ V)
    (h3 : v ∈ V) (h4 : u ≠ v) (h5 : Generic V E) :
    ¬ Collinear ℝ ({0, u, v} : Set V3) := by
  sorry

/-- HOL `SKOLEM_EPSILON` (hl:2226). -/
theorem SKOLEM_EPSILON_p14 {A : Type*} (Q : ℝ → A → Prop) (s : Set A)
    (hmono : ∀ e e' : ℝ, ∀ i : A, 0 < e → e ≤ e' → i ∈ s → (Q e' i → Q e i))
    (hs : s.Finite) :
    (∀ i : A, ∃ e : ℝ, 0 < e ∧ (i ∈ s → Q e i)) ↔
      ∃ e : ℝ, ∀ i : A, 0 < e ∧ (i ∈ s → Q e i) := by
  constructor
  · intro hf
    by_cases hse : s = ∅
    · subst hse
      exact ⟨1, fun i => ⟨one_pos, fun hi => absurd hi (by simp)⟩⟩
    · push_neg at hse
      obtain ⟨i₀, hi₀⟩ := hse
      choose g hg using hf
      have hTne : (hs.toFinset.image g).Nonempty := by
        refine Finset.nonempty_iff_ne_empty.mpr fun hempty => ?_
        have hi₀img : g i₀ ∈ hs.toFinset.image g :=
          Finset.mem_image.mpr ⟨i₀, Set.Finite.mem_toFinset hs |>.mpr hi₀, rfl⟩
        rw [hempty] at hi₀img
        simp at hi₀img
      obtain ⟨j, hj, hgif⟩ := Finset.mem_image.mp (Finset.min'_mem _ hTne)
      have hmin_eq : (hs.toFinset.image g).min' hTne = g j := hgif.symm
      have hpos : 0 < (hs.toFinset.image g).min' hTne := hmin_eq ▸ (hg j).1
      refine ⟨(hs.toFinset.image g).min' hTne, fun i => ⟨hpos, fun hi => ?_⟩⟩
      have hgi : g i ∈ hs.toFinset.image g :=
        Finset.mem_image.mpr ⟨i, Set.Finite.mem_toFinset hs |>.mpr hi, rfl⟩
      exact hmono _ _ _ (hmin_eq ▸ (hg j).1) (Finset.min'_le _ _ hgi) hi ((hg i).2 hi)
  · rintro ⟨e, hall⟩
    exact fun i => ⟨e, (hall i).1, (hall i).2⟩

/-- HOL `XIV_DEFORMATION` (hl:2259; the `dihV = dh` hypothesis is rendered
pointwise).  NEEDS: the XIV wedge-closure argument. -/
theorem XIV_DEFORMATION_p14 (f : V3 → ℝ → V3) (dh : ℕ × ℕ × ℕ → ℝ) (r : ℕ)
    (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h3 : Set.Pairwise (Set.Icc 1 (r + 2)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h4 : ∀ i j k, dihV 0 (w i) (w j) (w k) = dh (i, j, k))
    (h5 : ∀ i, i ∈ Set.Icc 1 (r + 1) → ∃ e2 : ℝ, 0 < e2 ∧ ∀ t, |t| < e2 →
      azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi)
    (h6 : ∀ i, i ∈ Set.Icc 1 (r + 1) →
      0 < azim 0 (w i) (w (i + 1)) (w (i - 1)))
    (h7 : ∀ p q, ({p, q, q + 1} : Set ℕ) ⊆ Set.Icc 1 (r + 1) → p ≠ q → p ≠ q + 1 →
      dh (p, q, q + 1) = 0)
    (h8 : ∀ p q, ({p, p + 1, q} : Set ℕ) ⊆ Set.Icc 1 (r + 1) → p + 1 < q →
      dh (p, p + 1, q) = 0)
    (h9 : ∀ p q, ({p + 1, p, q} : Set ℕ) ⊆ Set.Icc 1 (r + 1) → q < p →
      dh (p + 1, p, q) = 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      f (w 1) t ∈ wedgeGe 0 (f (w (r + 1)) t) (f (w (r + 2)) t) (f (w r) t) ∧
      f (w (r + 1)) t ∈ wedgeGe 0 (f (w 1) t) (f (w 2) t) (f (w 0) t) := by
  sorry

/-- HOL `XIV_ECAU` (hl:2562).  NEEDS: the XIV wedge-closure argument. -/
theorem XIV_ECAU_p14 (f : V3 → ℝ → V3) (r : ℕ) (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : ∀ i, i ∈ Set.Icc 2 (r + 1) → w i ∈ affGt ({0, w 1} : Set V3) ({w 2} : Set V3))
    (h3 : cyclicSet (w '' Set.Icc 1 (r + 1)) 0 (cross3 (w 1) (w 2)))
    (h4 : ∀ i, i ∈ Set.Icc 1 r →
      azimCycle_p14 (w '' Set.Icc 1 (r + 1)) 0 (cross3 (w 1) (w 2)) (w i) = w (i + 1))
    (h5 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h6 : Set.Pairwise (Set.Icc 1 (r + 2)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h7 : ∀ i, i ∈ Set.Icc 1 (r + 1) → ∃ e2 : ℝ, 0 < e2 ∧ ∀ t, |t| < e2 →
      azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi)
    (h8 : ∀ i, i ∈ Set.Icc 1 (r + 1) →
      0 < azim 0 (w i) (w (i + 1)) (w (i - 1))) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      f (w 1) t ∈ wedgeGe 0 (f (w (r + 1)) t) (f (w (r + 2)) t) (f (w r) t) ∧
      f (w (r + 1)) t ∈ wedgeGe 0 (f (w 1) t) (f (w 2) t) (f (w 0) t) := by
  sorry

/-- w5cA: the affine span of `{0, t • e}` equals that of `{0, e}` for `t ≠ 0`. -/
private theorem w5cA_affineSpan_pair_smul (e : V3) (t : ℝ) (ht : t ≠ 0) :
    affineSpan ℝ ({0, t • e} : Set V3) = affineSpan ℝ ({0, e} : Set V3) := by
  ext z
  constructor
  · intro hz
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hz ⊢
    obtain ⟨s, hs⟩ := hz
    refine ⟨s * t, ?_⟩
    rw [AffineMap.lineMap_apply_module'] at hs ⊢
    simp only [sub_zero, add_zero] at hs ⊢
    rw [← hs, smul_smul]
  · intro hz
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hz ⊢
    obtain ⟨s, hs⟩ := hz
    refine ⟨s / t, ?_⟩
    rw [AffineMap.lineMap_apply_module'] at hs ⊢
    simp only [sub_zero, add_zero] at hs ⊢
    rw [← hs, smul_smul, div_mul_cancel₀ s ht]

/-- HOL `cyclic_set_scale` (hl:2651).  NEEDS: affine-span scaling invariance
(this file's Section 0 has the collinearity kit). -/
theorem cyclic_set_scale_p14 (U : Set V3) (e : V3) (t : ℝ) (ht : t ≠ 0) :
    cyclicSet U 0 (t • e) ↔ cyclicSet U 0 e := by
  have hspan : affineSpan ℝ ({0, t • e} : Set V3) = affineSpan ℝ ({0, e} : Set V3) :=
    w5cA_affineSpan_pair_smul e t ht
  have hne : (0 : V3) ≠ t • e ↔ (0 : V3) ≠ e := by
    constructor
    · intro h hze
      exact h (by rw [← hze, smul_zero])
    · intro h hze
      rcases smul_eq_zero.mp hze.symm with h3 | h3
      · exact absurd h3 ht
      · exact h h3.symm
  constructor
  · rintro ⟨h0, hfin, hdiff, hspanE⟩
    refine ⟨hne.mp h0, hfin, ?_, ?_⟩
    · intro p hp q hq h heq
      have hcoef : (h * t⁻¹) • (0 - t • e) = h • (0 - e) := by
        rw [zero_sub, zero_sub, smul_neg, smul_neg, smul_smul, mul_assoc,
          inv_mul_cancel₀ ht, mul_one]
      refine hdiff p hp q hq (h * t⁻¹) ?_
      rw [heq, hcoef]
    · rw [hspan] at hspanE
      exact hspanE
  · rintro ⟨h0, hfin, hdiff, hspanE⟩
    refine ⟨hne.mpr h0, hfin, ?_, ?_⟩
    · intro p hp q hq h heq
      have hcoef : (h * t) • (0 - e) = h • (0 - t • e) := by
        rw [zero_sub, zero_sub, smul_neg, smul_neg, smul_smul]
      refine hdiff p hp q hq (h * t) ?_
      rw [heq, hcoef]
    · rw [← hspan] at hspanE
      exact hspanE


/-- HOL `projection_scale` (hl:2681; argument order: HOL `projection e u`
↔ repo `projection u e`). -/
theorem projection_scale_p14 (e u : V3) (t : ℝ) (ht : t ≠ 0) :
    projection u (t • e) = projection u e := by
  by_cases he : e ⬝ᵥ e = 0
  · have he0 : e = 0 := dot3_self_zero_p14 he
    subst he0
    simp only [projection, smul_zero, dot3_zero_right_p14, zero_div, zero_smul, sub_zero]
  · have h1 : (u : Fin 3 → ℝ) ⬝ᵥ ((t • e : V3) : Fin 3 → ℝ)
        = t * (u ⬝ᵥ e) := by
      refine (inner_eq_dot u (t • e)).symm.trans ?_
      rw [real_inner_smul_right, inner_eq_dot]
    have h2 : ((t • e : V3) : Fin 3 → ℝ) ⬝ᵥ ((t • e : V3) : Fin 3 → ℝ)
        = t * t * (e ⬝ᵥ e) := by
      refine (inner_eq_dot (t • e) (t • e)).symm.trans ?_
      rw [real_inner_smul_left, real_inner_smul_right, inner_eq_dot]
      ring
    unfold projection
    rw [h1, h2, smul_smul]
    field_simp

/-- w5cA: azim is invariant under positively scaling the axis point. -/
private theorem w5cA_azim_axis_scale (e x u : V3) (t : ℝ) (ht : 0 < t) :
    azim 0 (t • e) x u = azim 0 e x u := by
  have hcoliff : ∀ z : V3, Collinear3 0 (t • e) z ↔ Collinear3 0 e z := by
    intro z
    by_cases he : e = 0
    · subst he
      rw [smul_zero]
    · have hne : t • e ≠ 0 := by
        intro hze
        exact ht.ne' ((smul_eq_zero.mp hze).resolve_right he)
      rw [collinear3_iff_smul (hw := hne) (v := 0) (w := t • e) (w1 := z),
        collinear3_iff_smul (hw := he) (v := 0) (w := e) (w1 := z)]
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨c * t, ?_⟩
        simpa only [sub_zero, smul_smul] using hc
      · rintro ⟨c, hc⟩
        refine ⟨c / t, ?_⟩
        simpa only [sub_zero, smul_smul, div_mul_cancel₀ c (ne_of_gt ht)] using hc
  by_cases hc1 : Collinear3 0 e x
  · have hc1' : Collinear3 0 (t • e) x := (hcoliff x).mpr hc1
    rw [azim, azim, if_pos (Or.inl hc1'), if_pos (Or.inl hc1)]
  · by_cases hc2 : Collinear3 0 e u
    · rw [azim, azim, if_pos (Or.inr ((hcoliff u).mpr hc2)), if_pos (Or.inr hc2)]
    · obtain ⟨hge0, hlt2pi, h1c, h2c, hframe⟩ := azim_master 0 (t • e) x u
      have hdist : dist (t • e) 0 = t * dist e 0 := by
        rw [dist_eq_norm, dist_eq_norm, sub_zero, sub_zero, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht]
      have hspec : AzimSpec 0 e x u (azim 0 (t • e) x u) :=
        ⟨hge0, hlt2pi, h1c * t, h2c * t, ?_⟩
      exact (azim_eq_of_spec hc1 hc2 hspec).symm
      intro E1 E2 E3 hon haxis he0
      rw [sub_zero] at haxis
      obtain ⟨ψ, r1, r2, hrepx, hrepu, hpos1, hpos2⟩ :=
        hframe E1 E2 E3 hon
          (show (t • e - 0) = dist (t • e) 0 • E3 from by
            rw [sub_zero, hdist]
            conv_lhs => rw [haxis]
            rw [smul_smul])
          (by
            intro hze
            exact ht.ne' ((smul_eq_zero.mp hze).resolve_right
              (fun he0 => hc1 (by rw [he0]; simpa [Collinear3] using collinear2_p14 0 x))))
      refine ⟨ψ, r1, r2, ?_, ?_, ?_, ?_⟩
      · simpa only [sub_zero, smul_smul] using hrepx
      · simpa only [sub_zero, smul_smul] using hrepu
      · exact hpos1 (fun hh => hc1 ((hcoliff x).mp hh))
      · exact hpos2 (fun hh => hc2 ((hcoliff u).mp hh))

/-- w5cA: on a finite set not contained in `{p}` there exists an
azim-minimal element with the projection-norm tiebreak. -/
private theorem w5cA_exis_smallest {W : Set V3} {v w p : V3}
    (h1 : ¬(W ⊆ {p})) (hfin : W.Finite) :
    ∃ u : V3, u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ := by
  have hne : {u : V3 | u ∈ W ∧ u ≠ p}.Nonempty := by
    by_contra hc
    apply h1
    intro x hx
    by_contra hxp
    exact hc ⟨x, hx, hxp⟩
  have hf : {u : V3 | u ∈ W ∧ u ≠ p}.Finite := hfin.subset fun x hx => hx.1
  obtain ⟨q, hqin, hqmin⟩ := Set.exists_min_image
    {u : V3 | u ∈ W ∧ u ≠ p}
    (fun x => toLex (azim v w p x, ‖projection (x - v) (w - v)‖)) hf hne
  refine ⟨q, hqin.2, hqin.1, fun r hr hpr => ?_⟩
  have h := hqmin r ⟨hr, hpr⟩
  rw [Prod.Lex.toLex_le_toLex] at h
  exact h

/-- w5cA: characterization of `azimCycle_p14` (the `_p14` copy of the proved
`AZIM_CYCLE_PROPERTIES`). -/
private theorem w5cA_azimCycle_properties {W : Set V3} {p : V3} (hsub : ¬(W ⊆ {p}))
    (hfin : W.Finite) (v w : V3) :
    azimCycle_p14 W v w p ≠ p ∧ azimCycle_p14 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p →
        azim v w p (azimCycle_p14 W v w p) < azim v w p q ∨
          azim v w p (azimCycle_p14 W v w p) = azim v w p q ∧
            ‖projection (azimCycle_p14 W v w p - v) (w - v)‖ ≤
              ‖projection (q - v) (w - v)‖ := by
  obtain ⟨u, hu1, hu2, hu3⟩ := w5cA_exis_smallest hsub hfin
  rw [azimCycle_p14, if_neg hsub]
  exact Classical.epsilon_spec
    (p := fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖)
    ⟨u, hu1, hu2, hu3⟩

/-- HOL `azim_cycle_scale` (hl:2699).  NEEDS: azim scaling theory. -/
theorem azim_cycle_scale_p14 (U : Set V3) (e : V3) (t : ℝ) (ht : 0 < t) :
    azimCycle_p14 U 0 (t • e) = azimCycle_p14 U 0 e := by
  funext p
  by_cases hsub : U ⊆ {p}
  · rw [azimCycle_p14, if_pos hsub, azimCycle_p14, if_pos hsub]
  · rw [azimCycle_p14, if_neg hsub, azimCycle_p14, if_neg hsub]
    refine congrArg Classical.epsilon ?_
    funext q
    have hax : ∀ z : V3, azim 0 (t • e) p z = azim 0 e p z :=
      fun z => w5cA_azim_axis_scale e p z t ht
    have hproj : ∀ z : V3, projection z (t • e) = projection z e :=
      fun z => projection_scale_p14 e z t (ne_of_gt ht)
    simp only [sub_zero, hax, hproj]

/-- HOL `IDENTIFY_AZIM_CYCLE_SIMPLE` (hl:2720). -/
theorem IDENTIFY_AZIM_CYCLE_SIMPLE_p14 (W : Set V3) (v w p u : V3)
    (h1 : ¬ (W ⊆ {p})) (h2 : p ∈ W) (hc : cyclicSet W v w) (h3 : u ≠ p) (h4 : u ∈ W)
    (h5 : ∀ q : V3, q ≠ p → q ∈ W → q ≠ u → azim v w p u < azim v w p q) :
    azimCycle_p14 W v w p = u := by
  unfold azimCycle_p14
  rw [if_neg h1]
  by_contra hne
  set P : V3 → Prop := fun x => x ≠ p ∧ x ∈ W ∧ ∀ q ∈ W, q ≠ p →
    azim v w p x < azim v w p q ∨ azim v w p x = azim v w p q ∧
      ‖projection (x - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖ with hPdef
  obtain ⟨hne', hmu', hall⟩ :=
    Classical.epsilon_spec (p := P) ⟨u, h3, h4, fun q hq hpq => by
      by_cases hqu : q = u
      · rw [hqu]
        exact Or.inr ⟨rfl, le_refl _⟩
      · exact Or.inl (h5 q hpq hq hqu)⟩
  have hlt := h5 (Classical.epsilon P) hne' hmu' (fun heq => hne heq)
  rcases hall u h4 h3 with hlt2 | ⟨heq, _⟩
  · linarith
  · linarith

/-- HOL `coplanar_cross_scale` (hl:2745).  NEEDS: plane/span dimension
theory. -/
theorem coplanar_cross_scale_p14 (u1 u2 v1 v2 : V3)
    (h1 : Coplanar ({0, u1, u2, v1, v2} : Set V3))
    (h2 : 0 < (cross3 v1 v2) ⬝ᵥ (cross3 u1 u2)) :
    ∃ t : ℝ, 0 < t ∧ cross3 v1 v2 = t • (cross3 u1 u2) := by
  sorry

/-- HOL `azim_cycle_distinct` (hl:2782).  NEEDS: azimuth-cycle minimality
theory. -/
theorem azim_cycle_distinct_p14 (U : Set V3) (e v w : V3) (h1 : U.Finite)
    (h2 : v ∈ U) (h3 : w ∈ U) (h4 : v ≠ w)
    (h5 : ∀ x ∈ U, e ⬝ᵥ (cross3 x (azimCycle_p14 U 0 e x)) ≠ 0) :
    0 < azim 0 e v w := by
  have he0 : e ≠ 0 := by
    intro he
    exact h5 v h2 (by rw [he, dot3_eq_p14, coe_zero_p14, dotProduct_comm,
      dotProduct_zero])
  have hnc : ∀ x ∈ U, ¬ Collinear ℝ ({0, e, x} : Set V3) := by
    intro x hx hcol
    by_cases hx0 : x = 0
    · refine h5 x hx ?_
      have h3z : cross3 x (azimCycle_p14 U 0 e x) = 0 :=
        w5cA_collinear_cross3_eq (v := x) (w := azimCycle_p14 U 0 e x)
          (by simpa [hx0] using collinear2_p14 0 (azimCycle_p14 U 0 e 0))
      rw [h3z]
      simp
    · obtain ⟨c, hc⟩ := (collinear3_iff_smul (hw := he0) (v := 0) (w := e)
        (w1 := x)).mp (by simpa [Collinear3] using hcol)
      have hc' : x = c • e := by simpa only [sub_zero] using hc
      apply h5 x hx
      rw [hc', dot3_eq_p14, coe_cross3_p14, coe_smul_p14, map_smul,
        LinearMap.smul_apply]
      simp [dot_self_cross]
  have hcy := w5cA_azimCycle_properties (p := v)
    (hsub := by intro hsub; exact h4 ((Set.mem_singleton_iff.mp (hsub h3)).symm)) h1 0 e
  obtain ⟨hcy1, hcy2, hcy3⟩ := hcy
  have hncv : ¬ Collinear ℝ ({0, e, v} : Set V3) := hnc v h2
  have hncu : ¬ Collinear ℝ ({0, e, azimCycle_p14 U 0 e v} : Set V3) := hnc _ hcy2
  have hcyc0 : azimCycle_p14 U 0 e v ≠ 0 := by
    intro hzero
    exact hncu (by rw [hzero]; simpa using collinear2_p14 e 0)
  have hcycE : azimCycle_p14 U 0 e v ≠ e := by
    intro heq
    exact hncu (by rw [heq]; simpa using collinear2_p14 0 e)
  have hpos : 0 < azim 0 e v (azimCycle_p14 U 0 e v) := by
    rw [azim_pos_iff_nz_p14]
    intro hz
    apply h5 v h2
    obtain ⟨a, ha, k, hvk⟩ := (affGt_pair_iff (v0 := 0) (v1 := e)
      (x := azimCycle_p14 U 0 e v) (y := v) (Ne.symm he0)
      (by intro hzero; exact hncu (by rw [hzero]; simpa using collinear2_p14 e 0))
      (by intro heq; exact hncu (by rw [heq]; simpa using collinear2_p14 0 e))).mp
      ((azim_eq_zero_iff hncv hncu).mp hz)
    have hvk' : v = a • (azimCycle_p14 U 0 e v) + k • e := by
      simpa only [sub_zero] using hvk
    nth_rewrite 1 [hvk']
    rw [dot3_eq_p14, coe_cross3_p14, coe_add_p14, coe_smul_p14, coe_smul_p14,
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, cross_self, smul_zero, zero_add, dotProduct_comm,
      smul_dotProduct, dotProduct_comm, dot_self_cross, smul_zero]
  rcases hcy3 w h3 (Ne.symm h4) with hlt | heqq
  · exact lt_trans hpos hlt
  · obtain ⟨heqq, -⟩ := heqq
    rw [← heqq]
    exact hpos

/-- HOL `azim_cycle_neg` (hl:2828).  NEEDS: azimuth-cycle negation theory. -/
theorem azim_cycle_neg_p14 (U : Set V3) (e v w : V3) (h1 : U.Finite) (h2 : v ∈ U)
    (h3 : azimCycle_p14 U 0 e v = w)
    (h4 : ∀ x ∈ U, e ⬝ᵥ (cross3 x (azimCycle_p14 U 0 e x)) ≠ 0) :
    azimCycle_p14 U 0 (-e) w = v := by
  sorry

/-- HOL `azim_cycle_neg` re-proved (hl:2897; the source re-binds the name
with stronger hypotheses).  NEEDS: azimuth-cycle negation theory. -/
theorem azim_cycle_neg2_p14 (U : Set V3) (e v w : V3) (h1 : ¬ (U ⊆ {w}))
    (h2 : U.Finite) (h3 : cyclicSet U 0 e) (h4 : v ∈ U)
    (h5 : e ⬝ᵥ (cross3 v w) ≠ 0) (h6 : azimCycle_p14 U 0 e v = w) :
    azimCycle_p14 U 0 (-e) w = v := by
  sorry

/-- HOL `XIV_ECAU_BACK` (hl:2938; the hl:2964 hypothesis `// &0 < ...` is
commented out in the source and not carried).  NEEDS: the XIV
wedge-closure argument. -/
theorem XIV_ECAU_BACK_p14 (f : V3 → ℝ → V3) (r : ℕ) (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : 1 ≤ r)
    (h3 : ∀ i, i ∈ Set.Icc 1 r → w i ∈ affGt ({0, w (r + 1)} : Set V3) ({w r} : Set V3))
    (h4 : cyclicSet (w '' Set.Icc 1 (r + 1)) 0 (cross3 (w 1) (w 2)))
    (h5 : ∀ i, i ∈ Set.Icc 1 r →
      0 < (cross3 (w i) (w (i + 1))) ⬝ᵥ (cross3 (w 1) (w 2)))
    (h6 : ({w 1, w 2} : Set V3) ⊆ affGt ({0, w (r + 1)} : Set V3) ({w r} : Set V3))
    (h7 : ∀ i, i ∈ Set.Icc 1 r →
      azimCycle_p14 (w '' Set.Icc 1 (r + 1)) 0 (cross3 (w 1) (w 2)) (w i) = w (i + 1))
    (h8 : azimCycle_p14 (w '' Set.Icc 1 (r + 1)) 0 (cross3 (w 1) (w 2)) (w (r + 1)) = w 1)
    (h9 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h10 : Set.Pairwise (Set.Icc 1 (r + 2)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h11 : ∀ i, i ∈ Set.Icc 1 (r + 1) → ∃ e2 : ℝ, 0 < e2 ∧ ∀ t, |t| < e2 →
      azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi)
    (h12 : ∀ i, i ∈ Set.Icc 1 (r + 1) →
      0 < azim 0 (w i) (w (i + 1)) (w (i - 1))) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      f (w 1) t ∈ wedgeGe 0 (f (w (r + 1)) t) (f (w (r + 2)) t) (f (w r) t) ∧
      f (w (r + 1)) t ∈ wedgeGe 0 (f (w 1) t) (f (w 2) t) (f (w 0) t) := by
  sorry

/-- HOL `zlz_wedge_boundary` (hl:3130).  NEEDS: terminal deformation
theory. -/
theorem zlz_wedge_boundary_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ x : V3 × V3, ∀ v : V3, ∃ e3 : ℝ, (x ∈ FF ∧ v ∈ V) →
      0 < e3 ∧ ∀ t, -e3 < t ∧ t < e3 →
        f v t ∈ wedgeInFanGe (f x.1 t, f x.2 t)
          ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

/-- HOL `ZLZTHIC` (hl:3742) — the chapter terminal lemma; shape-matches
`ZLZTHIC_concl` (LocalAuto1, appendix.hl:45).  NEEDS: the assembled
zlz chain (`zlz_reduction`, `zlz_generic`, `zlz_wedge_skolem`,
`zlz_wedge_boundary`, `zlz_azim`). -/
theorem ZLZTHIC_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, -ε < t ∧ t < ε →
      ConvexLocalFan ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) ∧
      Generic ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E) := by
  sorry

end Kepler.Text
