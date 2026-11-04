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
  - Source duplicate: `azim_cycle_neg` appears twice (hl:2828 live; hl:2897
    is an abandoned attempt inside an OCaml comment block, never proved and
    false — its port was removed by SF-96).  hl:2964 has a commented-out hypothesis
    (`// &0 < ...`), kept out of `XIV_ECAU_BACK_p14`.
  - DISCHARGES convention: the terminal theorem `ZLZTHIC_p14`
    shape-matches `ZLZTHIC_concl` (LocalAuto1, appendix.hl:45); a later
    wave proving `ZLZTHIC_p14` discharges that registry `sorry`.
-/

import Kepler.Geom.AzimLemmas
import Kepler.Text.LocalAuto1
import Kepler.Text.AzimBridge
import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto6
import Kepler.Text.LocalAuto9
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto5
import Kepler.Text.PolyAuto1
import Mathlib
import Kepler.Text.V3Coe
import Kepler.Text.LocalAuto37
import Kepler.Text.LocalAuto35
import Kepler.Text.XivphksKit

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical
open Kepler.Text.V3Coe

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

/-! ## w5cA2 kit A (W5c-A wave 2): continuity of cross/dot along curves and
the coplanarity/triple-product characterization.  Inserted before the first
consumption point `NONPLANAR_OPEN_p14`; self-contained w.r.t. the wave-1
`w5cA_` block (which sits later in the file). -/

/-- w5cA2: collinear-with-origin vectors have vanishing cross product
(re-derivation; this kit precedes the wave-1 helper block). -/
private theorem w5cA2_collinear0_cross {v w : V3}
    (h : Collinear ℝ ({0, v, w} : Set V3)) : cross3 v w = 0 := by
  by_cases hv : v = 0
  · have hpi : crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ) = 0 := by
      rw [hv, coe_zero_p14, map_zero, LinearMap.zero_apply]
    have hd : cross3 v w ⬝ᵥ (cross3 v w) = 0 := by
      rw [dot3_eq_p14, coe_cross3_p14, hpi, dotProduct_zero]
    exact dot3_self_zero_p14 hd
  obtain ⟨s, hs⟩ := smul_of_collinear0_p14 hv h
  have hpi : crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ) = 0 := by
    rw [hs, coe_smul_p14, map_smul, cross_self, smul_zero]
  have hd : cross3 v w ⬝ᵥ (cross3 v w) = 0 := by
    rw [dot3_eq_p14, coe_cross3_p14, hpi, dotProduct_zero]
  exact dot3_self_zero_p14 hd

/-- w5cA2: origin-collinearity is exactly the vanishing of the cross product. -/
private theorem w5cA2_collinear0_iff_cross {v w : V3} :
    Collinear ℝ ({0, v, w} : Set V3) ↔ cross3 v w = 0 :=
  ⟨w5cA2_collinear0_cross, fun hc => by
    by_contra hnc
    exact absurd hc (cross3_ne_p14 hnc)⟩

/-- w5cA2: norm bound for the cross product. -/
private theorem w5cA2_cross_norm_le (u v : V3) : ‖cross3 u v‖ ≤ ‖u‖ * ‖v‖ := by
  have key : cross3 u v ⬝ᵥ cross3 u v = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (u ⬝ᵥ v) ^ 2 := by
    rw [dot3_eq_p14, coe_cross3_p14 u v, cross_dot_cross, ← dot3_eq_p14 u u,
      ← dot3_eq_p14 v v, ← dot3_eq_p14 u v, ← dot3_eq_p14 v u, norm_sq_eq_dot,
      norm_sq_eq_dot, dot3_comm_p14 v u, sq]

  have h1 : ‖cross3 u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have hs : ‖cross3 u v‖ ^ 2 = cross3 u v ⬝ᵥ cross3 u v := norm_sq_eq_dot _
    have hpow : (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [pow_two, pow_two, pow_two]; ring
    rw [hs, key]
    linarith [sq_nonneg (u ⬝ᵥ v), hpow]
  have h2 := sq_le_sq.mp h1
  rw [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h2
  exact h2

private theorem w5cA2_coe_sub_p14 (x y : V3) :
    ((x - y : V3) : Fin 3 → ℝ) = ((x : V3) : Fin 3 → ℝ) - ((y : V3) : Fin 3 → ℝ) := rfl

private theorem w5cA2_coe_neg_p14 (x : V3) :
    ((-x : V3) : Fin 3 → ℝ) = -((x : V3) : Fin 3 → ℝ) := rfl

/-- w5cA2: difference form of cross bilinearity. -/
private theorem w5cA2_cross3_sub (a a' b b' : V3) :
    cross3 a b - cross3 a' b' = cross3 (a - a') b + cross3 a' (b - b') := by
  have h : ((cross3 a b - cross3 a' b' : V3) : Fin 3 → ℝ)
      = ((cross3 (a - a') b + cross3 a' (b - b') : V3) : Fin 3 → ℝ) := by
    rw [w5cA2_coe_sub_p14, coe_add_p14, coe_cross3_p14 a b, coe_cross3_p14 a' b',
      coe_cross3_p14 (a - a') b, coe_cross3_p14 a' (b - b')]
    simp only [w5cA2_coe_sub_p14, map_sub, LinearMap.sub_apply]
    ring
  exact congrArg (fun w : Fin 3 → ℝ => WithLp.toLp 2 w) h

/-- w5cA2: antisymmetry of `cross3`. -/
private theorem w5cA2_cross3_neg (x y : V3) : cross3 x y = -cross3 y x := by
  have h : ((cross3 x y : V3) : Fin 3 → ℝ) = ((-cross3 y x : V3) : Fin 3 → ℝ) := by
    rw [coe_cross3_p14 x y, w5cA2_coe_neg_p14, coe_cross3_p14 y x, cross_anticomm]
  exact congrArg (fun w : Fin 3 → ℝ => WithLp.toLp 2 w) h

/-- w5cA2: continuity of the cross product along curves. -/
private theorem w5cA2_continuousAt_cross3 {f g : ℝ → V3} {t : ℝ}
    (hf : ContinuousAt f t) (hg : ContinuousAt g t) :
    ContinuousAt (fun x => cross3 (f x) (g x)) t := by
  have hb : ∀ x : ℝ, dist (cross3 (f x) (g x)) (cross3 (f t) (g t))
      ≤ ‖f x - f t‖ * ‖g x‖ + ‖f t‖ * ‖g x - g t‖ := by
    intro x
    rw [dist_eq_norm, w5cA2_cross3_sub (f x) (f t) (g x) (g t)]
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add (w5cA2_cross_norm_le _ _) (w5cA2_cross_norm_le _ _)
  have ha : Filter.Tendsto (fun x => ‖f x - f t‖) (nhds t) (nhds 0) := by
    have h : Filter.Tendsto (fun x => ‖f x - f t‖) (nhds t)
        (nhds (‖f t - f t‖)) :=
      (hf.sub continuousAt_const).norm.tendsto
    rw [sub_self, norm_zero] at h
    exact h
  have hb2 : Filter.Tendsto (fun x => ‖f t‖ * ‖g x - g t‖) (nhds t) (nhds 0) := by
    have h : Filter.Tendsto (fun x => ‖g x - g t‖) (nhds t)
        (nhds (‖g t - g t‖)) :=
      (hg.sub continuousAt_const).norm.tendsto
    rw [sub_self, norm_zero] at h
    have h2 := h.const_mul ‖f t‖
    rwa [mul_zero] at h2
  have h1 : Filter.Tendsto (fun x => ‖f x - f t‖ * ‖g x‖) (nhds t) (nhds 0) := by
    have h : Filter.Tendsto (fun x => ‖f x - f t‖ * ‖g x‖) (nhds t)
        (nhds (0 * ‖g t‖)) :=
      ha.mul hg.norm.tendsto
    rwa [zero_mul] at h
  have hsum : Filter.Tendsto
      (fun x => ‖f x - f t‖ * ‖g x‖ + ‖f t‖ * ‖g x - g t‖) (nhds t) (nhds 0) := by
    have h := Filter.Tendsto.add h1 hb2
    rwa [zero_add] at h
  have h2 : Filter.Tendsto (fun x => dist (cross3 (f x) (g x)) (cross3 (f t) (g t)))
      (nhds t) (nhds 0) :=
    squeeze_zero (fun x => dist_nonneg) hb hsum
  show Filter.Tendsto (fun x => cross3 (f x) (g x)) (nhds t)
    (nhds (cross3 (f t) (g t)))
  exact tendsto_iff_dist_tendsto_zero.mpr h2

/-- w5cA2: continuity of the dot product along curves. -/
private theorem w5cA2_continuousAt_dot {f g : ℝ → V3} {t : ℝ}
    (hf : ContinuousAt f t) (hg : ContinuousAt g t) :
    ContinuousAt (fun x => f x ⬝ᵥ g x) t := by
  have hEq : (fun x => f x ⬝ᵥ g x) = fun x => inner ℝ (f x) (g x) :=
    funext fun x => (inner_eq_dot _ _).symm
  rw [hEq]
  exact hf.inner hg

/-- w5cA2: a scalar function continuous at a point of nonzero value stays
nonzero in a ball around the point. -/
private theorem w5cA2_eventually_ne {G : ℝ → ℝ} {t : ℝ} (hG : ContinuousAt G t)
    (h0 : G t ≠ 0) : ∃ e : ℝ, 0 < e ∧ ∀ t', |t - t'| < e → G t' ≠ 0 := by
  have hd : (0:ℝ) < dist (G t) 0 := by
    rw [dist_eq_norm, sub_zero]
    exact norm_pos_iff.mpr h0
  have hmem : Metric.ball (G t) (dist (G t) 0 / 2) ∈ nhds (G t) :=
    Metric.ball_mem_nhds (G t) (by linarith)
  have hsub : Metric.ball (G t) (dist (G t) 0 / 2) ⊆ {y : ℝ | y ≠ 0} := by
    intro y hy hy0
    rw [Metric.mem_ball] at hy
    rw [hy0, dist_comm] at hy
    linarith
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hG.eventually hmem)
  refine ⟨e, he, fun t' ht => hsub (hball t' ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact ht

/-- w5cA2: a scalar function continuous at a point of positive value stays
positive in a ball around the point. -/
private theorem w5cA2_eventually_pos {G : ℝ → ℝ} {t : ℝ} (hG : ContinuousAt G t)
    (h0 : 0 < G t) : ∃ e : ℝ, 0 < e ∧ ∀ t', |t - t'| < e → 0 < G t' := by
  have hmem : {y : ℝ | 0 < y} ∈ nhds (G t) := isOpen_Ioi.mem_nhds h0
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hG.eventually hmem)
  refine ⟨e, he, fun t' ht => hball t' ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact ht

/-- w5cA2: a vector in the span of two others has zero triple product. -/
private theorem w5cA2_span2_triple {v w x : V3}
    (h : x ∈ Submodule.span ℝ ({v, w} : Set V3)) : x ⬝ᵥ cross3 v w = 0 := by
  obtain ⟨α, β, hx⟩ := Submodule.mem_span_pair.mp h
  have h1 : v ⬝ᵥ cross3 v w = 0 := by rw [dot3_comm_p14]; exact cross3_dotL_p14 v w
  have h2 : w ⬝ᵥ cross3 v w = 0 := by rw [dot3_comm_p14]; exact cross3_dotR_p14 v w
  rw [← hx, dot3_add_left_p14, dot3_smul_left_p14, dot3_smul_left_p14, h1, h2]
  ring

/-- w5cA2: negation in the second slot of the dot product. -/
private theorem w5cA2_dot_neg_right (x w : V3) : x ⬝ᵥ (-w) = -(x ⬝ᵥ w) := by
  exact dotProduct_neg _ _

/-- w5cA2: cyclic permutation of the triple product. -/
private theorem w5cA2_triple_perm (x y z : V3) :
    x ⬝ᵥ cross3 y z = y ⬝ᵥ cross3 z x := by
  rw [dot3_eq_p14, dot3_eq_p14, coe_cross3_p14 y z, coe_cross3_p14 z x]
  exact triple_product_permutation _ _ _

/-- w5cA2: swapping the cross factors negates the triple product. -/
private theorem w5cA2_triple_anti (x y z : V3) :
    x ⬝ᵥ cross3 y z = -(y ⬝ᵥ cross3 x z) := by
  have h2 : x ⬝ᵥ cross3 y z + y ⬝ᵥ cross3 x z = 0 := by
    rw [dot3_eq_p14, dot3_eq_p14, coe_cross3_p14 y z, coe_cross3_p14 x z,
      triple_product_permutation ((y : V3) : Fin 3 → ℝ) ((x : V3) : Fin 3 → ℝ)
        ((z : V3) : Fin 3 → ℝ), ← dotProduct_add, cross_anticomm',
      dotProduct_zero]
  exact eq_neg_iff_add_eq_zero.mpr h2

/-- w5cA2: case analysis over `Fin 3` by the literal value. -/
private theorem w5cA2_fin3_eq_cases {f g : Fin 3 → ℝ} (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (h2 : f 2 = g 2) (i : Fin 3) : f i = g i := by
  have hv := i.isLt
  have hval : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  rcases hval with h | h | h
  · have hi0 : i = (0 : Fin 3) := Fin.ext (b := 0) (by simpa using h)
    rw [hi0]; exact h0
  · have hi1 : i = (1 : Fin 3) := Fin.ext (b := 1) (by simpa using h)
    rw [hi1]; exact h1
  · have hi2 : i = (2 : Fin 3) := Fin.ext (b := 2) (by simpa using h)
    rw [hi2]; exact h2

/-- w5cA2: a dependent triple of vectors has one member in the span of the
other two. -/
private theorem w5cA2_dependent3 {u v w : V3} (hdep : ¬ LinearIndependent ℝ ![u, v, w]) :
    u ∈ Submodule.span ℝ ({v, w} : Set V3) ∨ v ∈ Submodule.span ℝ ({u, w} : Set V3) ∨
      w ∈ Submodule.span ℝ ({u, v} : Set V3) := by
  obtain ⟨f, g, hsum, hne⟩ :=
    (Fintype.not_linearIndependent_iffₛ (v := ![u, v, w])).mp hdep
  have hkey : ∑ i, (f i - g i) • (![u, v, w] i) = 0 := by
    have hterm : ∀ i : Fin 3, (f i - g i) • (![u, v, w] i)
        = f i • (![u, v, w] i) - g i • (![u, v, w] i) := fun i => sub_smul _ _ _
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, hsum,
      sub_self]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, show (![u, v, w] : Fin 3 → V3) 2 = w from rfl] at hkey
  by_cases hz1 : f 0 = g 0
  · by_cases hz2 : f 1 = g 1
    · have hz3 : f 2 - g 2 ≠ 0 := by
        intro h3
        obtain ⟨i, hi⟩ := hne
        have hi' := w5cA2_fin3_eq_cases (f := f) (g := g) hz1 hz2
          (sub_eq_zero.mp h3) i
        rw [hi'] at hi
        exact hi rfl
      rw [hz1, hz2, sub_self, sub_self, zero_smul, zero_smul, zero_add, zero_add]
        at hkey
      have hwz : w = 0 := by
        rcases smul_eq_zero.mp hkey with h | h
        · exact absurd h hz3
        · exact h
      exact Or.inr (Or.inr (by rw [hwz]; exact Submodule.zero_mem _))
    · have h2ne : f 1 - g 1 ≠ 0 := sub_ne_zero.mpr hz2
      have hkv : (f 1 - g 1) • v = -((f 2 - g 2) • w) := by
        rw [hz1, sub_self, zero_smul, zero_add] at hkey
        exact eq_neg_iff_add_eq_zero.mpr hkey
      have hvw2 : v = ((f 1 - g 1)⁻¹ * -(f 2 - g 2)) • w := by
        have h := congrArg (fun z : V3 => (f 1 - g 1)⁻¹ • z) hkv
        rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul, smul_neg] at h
        rw [h]
        module
      refine Or.inr (Or.inl (Submodule.mem_span_pair.mpr
        ⟨0, (f 1 - g 1)⁻¹ * -(f 2 - g 2), by rw [zero_smul, zero_add, hvw2]⟩))
  · have h1ne : f 0 - g 0 ≠ 0 := sub_ne_zero.mpr hz1
    have hu : u = -((f 0 - g 0)⁻¹ • ((f 1 - g 1) • v + (f 2 - g 2) • w)) := by
      have h : (f 0 - g 0) • u + ((f 1 - g 1) • v + (f 2 - g 2) • w) = 0 :=
        (add_assoc ((f 0 - g 0) • u) ((f 1 - g 1) • v)
          ((f 2 - g 2) • w)).symm.trans hkey
      have h2 := congrArg (fun z : V3 => (f 0 - g 0)⁻¹ • z)
        (eq_neg_iff_add_eq_zero.mpr h)
      rw [smul_smul, inv_mul_cancel₀ h1ne, one_smul, smul_neg] at h2
      exact h2
    refine Or.inl (Submodule.mem_span_pair.mpr
      ⟨-(f 0 - g 0)⁻¹ * (f 1 - g 1), -(f 0 - g 0)⁻¹ * (f 2 - g 2), ?_⟩)
    rw [hu]
    module

/-- w5cA2: a linearly independent triple has nonzero triple product. -/
private theorem w5cA2_li3_triple_ne {u v w : V3} (hli : LinearIndependent ℝ ![u, v, w]) :
    u ⬝ᵥ cross3 v w ≠ 0 := by
  have hco : crossProduct ((v : V3) : Fin 3 → ℝ) ((w : V3) : Fin 3 → ℝ) ≠ 0 := by
    rw [crossProduct_ne_zero_iff_linearIndependent]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hv3 : ((g 0 • v + g 1 • w : V3) : Fin 3 → ℝ) = ((0 : V3) : Fin 3 → ℝ) := by
      rw [coe_add_p14, coe_smul_p14, coe_smul_p14, coe_zero_p14]
      exact hg
    have hv3' : g 0 • v + g 1 • w = (0 : V3) :=
      congrArg (fun q : Fin 3 → ℝ => WithLp.toLp 2 q) hv3
    have h1 := Fintype.linearIndependent_iff.mp hli ![0, g 0, g 1] (by
      show (∑ i : Fin 3, (![0, g 0, g 1] i) • (![u, v, w] i)) = 0
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, show (![0, g 0, g 1] : Fin 3 → ℝ) 2 = g 1 from rfl,
        show (![u, v, w] : Fin 3 → V3) 2 = w from rfl, zero_smul, zero_add]
      simp [hv3'])
    have hg0 : g 0 = 0 := h1 1
    have hg1 : g 1 = 0 := h1 2
    intro i
    fin_cases i <;> simp [hg0, hg1]
  have hcw : cross3 v w ≠ 0 := by
    intro h0
    have h := coe_cross3_p14 v w
    rw [h0, coe_zero_p14] at h
    exact hco h.symm
  -- {u, v, w} is a basis of V3; write the cross product in it and dot with itself
  have hfin3 : Module.finrank ℝ V3 = 3 := by
    have h := (finrank_euclideanSpace_fin (𝕜 := ℝ) : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    exact h
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ V3 := by simp [hfin3]
  have hbcoe : ∀ i : Fin 3,
      (basisOfLinearIndependentOfCardEqFinrank hli hcard) i = (![u, v, w] i) :=
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcsum : (basisOfLinearIndependentOfCardEqFinrank hli hcard).repr
        (cross3 v w) 0 • (basisOfLinearIndependentOfCardEqFinrank hli hcard) 0
      + (basisOfLinearIndependentOfCardEqFinrank hli hcard).repr (cross3 v w) 1 •
        (basisOfLinearIndependentOfCardEqFinrank hli hcard) 1
      + (basisOfLinearIndependentOfCardEqFinrank hli hcard).repr (cross3 v w) 2 •
        (basisOfLinearIndependentOfCardEqFinrank hli hcard) 2 = cross3 v w := by
    have h := (basisOfLinearIndependentOfCardEqFinrank hli hcard).sum_repr
      (cross3 v w)
    simpa [hbcoe, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, show (![u, v, w] : Fin 3 → V3) 2 = w from rfl] using h
  intro hz
  have hv0 : v ⬝ᵥ cross3 v w = 0 := by rw [dot3_comm_p14]; exact cross3_dotL_p14 v w
  have hv0' : w ⬝ᵥ cross3 v w = 0 := by rw [dot3_comm_p14]; exact cross3_dotR_p14 v w
  rw [← hcsum] at hz hv0 hv0'
  simp only [hbcoe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    show (![u, v, w] : Fin 3 → V3) 2 = w from rfl] at hz hv0 hv0'
  have hc0 : cross3 v w ⬝ᵥ cross3 v w = 0 := by
    rw [← hcsum, dot3_add_left_p14, dot3_add_left_p14, dot3_smul_left_p14,
      dot3_smul_left_p14, dot3_smul_left_p14]
    simp only [hbcoe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      show (![u, v, w] : Fin 3 → V3) 2 = w from rfl]
    rw [hz, hv0, hv0']
    ring
  exact hcw (dot3_self_zero_p14 hc0)

/-- w5cA2: membership in the affine span of three points, explicit form. -/
private theorem w5cA2_mem_affineSpan_of_span2 {a b c x : V3}
    (h : x - a ∈ Submodule.span ℝ ({b - a, c - a} : Set V3)) :
    x ∈ affineSpan ℝ ({a, b, c} : Set V3) := by
  have hsub : ({b - a, c - a} : Set V3) ⊆ ({a, b, c} : Set V3) -ᵥ ({a, b, c} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzb | hzc
    · exact ⟨b, by simp, a, by simp, hzb ▸ rfl⟩
    · exact ⟨c, by simp, a, by simp, hzc ▸ rfl⟩
  have hd : x -ᵥ a ∈ (affineSpan ℝ ({a, b, c} : Set V3)).direction := by
    rw [direction_affineSpan, vectorSpan_def]
    exact Submodule.span_mono hsub h
  have hx : x = (x -ᵥ a) +ᵥ a := (vsub_vadd x a).symm
  rw [hx]
  exact AffineSubspace.vadd_mem_of_mem_direction hd (mem_affineSpan ℝ (by simp))

/-- w5cA2: master coplanarity characterization: four points are coplanar iff
the triple product of the difference vectors vanishes. -/
private theorem w5cA2_coplanar_triple {a b c d : V3} :
    Coplanar ({a, b, c, d} : Set V3) ↔ (b - a) ⬝ᵥ cross3 (c - a) (d - a) = 0 := by
  constructor
  · rintro ⟨p, q, r, hsub⟩
    have hdirle : (affineSpan ℝ ({p, q, r} : Set V3)).direction ≤
        Submodule.span ℝ ({q - p, r - p} : Set V3) := by
      rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro d ⟨z, hz, y, hy, rfl⟩
      simp only [vsub_eq_sub] at hy ⊢
      rcases hz with hp | hq | hr
      · rcases hy with hp' | hq' | hr'
        · rw [hp, hp']
          simp only [sub_self]
          exact Submodule.zero_mem _
        · rw [hp, hq']
          rw [show (p : V3) - q = (-1 : ℝ) • (q - p) from by module]
          exact Submodule.smul_mem _ (-1) (Submodule.subset_span (by simp))
        · rw [hp, hr']
          rw [show (p : V3) - r = (-1 : ℝ) • (r - p) from by module]
          exact Submodule.smul_mem _ (-1) (Submodule.subset_span (by simp))
      · rcases hy with hp' | hq' | hr'
        · rw [hq, hp']
          exact Submodule.subset_span (by simp)
        · rw [hq, hq']
          simp only [sub_self]
          exact Submodule.zero_mem _
        · rw [hq, hr']
          have hqeq : (q : V3) - r = (q - p) - (r - p) := by abel
          rw [hqeq]
          exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
      · rcases hy with hp' | hq' | hr'
        · rw [hr, hp']
          exact Submodule.subset_span (by simp)
        · rw [hr, hq']
          have hrq : (r : V3) - q = (r - p) - (q - p) := by abel
          rw [hrq]
          exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
        · rw [hr, hr']
          simp only [sub_self]
          exact Submodule.zero_mem _
    have hfr : Module.finrank ℝ (Submodule.span ℝ ({q - p, r - p} : Set V3)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := ℝ) ({q - p, r - p} : Finset V3)
      unfold Set.finrank at h
      rw [show (({q - p, r - p} : Finset V3) : Set V3) = ({q - p, r - p} : Set V3) from
        by ext z; simp] at h
      have h2c : (({q - p, r - p} : Finset V3)).card ≤ 2 := by
        have h2c := Finset.card_insert_le (q - p) ({r - p} : Finset V3)
        rw [Finset.card_singleton] at h2c
        simpa using h2c
      exact le_trans h h2c
    have hndep : ¬ LinearIndependent ℝ ![b - a, c - a, d - a] := by
      intro hli
      have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![b - a, c - a, d - a])) = 3 := by
        rw [finrank_span_eq_card hli]; norm_num
      have hmem : ∀ z ∈ ({b - a, c - a, d - a} : Set V3),
          z ∈ Submodule.span ℝ ({q - p, r - p} : Set V3) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with h | h | h
        · rw [h]
          exact hdirle (AffineSubspace.vsub_mem_direction (hsub (by simp))
            (hsub (by simp)))
        · rw [h]
          exact hdirle (AffineSubspace.vsub_mem_direction (hsub (by simp))
            (hsub (by simp)))
        · rw [h]
          exact hdirle (AffineSubspace.vsub_mem_direction (hsub (by simp))
            (hsub (by simp)))
      have hle : Submodule.span ℝ (Set.range ![b - a, c - a, d - a]) ≤
          Submodule.span ℝ ({q - p, r - p} : Set V3) := by
        rw [Submodule.span_le]
        rintro y ⟨i, hi, rfl⟩
        fin_cases i <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
          exact hmem _ (by simp)
      exact absurd (le_trans (Submodule.finrank_mono hle) hfr) (by rw [h3]; norm_num)
    rcases w5cA2_dependent3 hndep with h | h | h
    · exact w5cA2_span2_triple h
    · rw [w5cA2_triple_anti (b - a) (c - a) (d - a), w5cA2_span2_triple h, neg_zero]
    · rw [w5cA2_triple_perm (b - a) (c - a) (d - a),
        w5cA2_triple_perm (c - a) (d - a) (b - a), w5cA2_span2_triple h]
  · intro hz
    by_cases hind : LinearIndependent ℝ ![c - a, d - a]
    · have hmem : b - a ∈ Submodule.span ℝ ({c - a, d - a} : Set V3) := by
        by_contra hout
        have hli : LinearIndependent ℝ ![b - a, c - a, d - a] := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, show (![b - a, c - a, d - a] : Fin 3 → V3) 2 = d - a
              from rfl] at hg
          by_cases h0 : g 0 = 0
          · have h12 : g 1 • (c - a) + g 2 • (d - a) = 0 := by
              rw [h0, zero_smul, zero_add] at hg; exact hg
            have h12' := Fintype.linearIndependent_iff.mp hind ![g 1, g 2] (by
              simpa [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
                using h12)
            have hg1 : g 1 = 0 := h12' 0
            have hg2 : g 2 = 0 := h12' 1
            intro i
            fin_cases i <;> simp [h0, hg1, hg2]
          · exfalso
            have hu : b - a = ((-g 1 / g 0) • (c - a) + (-g 2 / g 0) • (d - a)) := by
              have hinj := smul_right_injective V3 h0
              refine hinj ?_
              show g 0 • (b - a)
                = g 0 • ((-g 1 / g 0) • (c - a) + (-g 2 / g 0) • (d - a))
              rw [smul_add, smul_smul, smul_smul]
              rw [show g 0 * (-g 1 / g 0) = -g 1 from by field_simp,
                show g 0 * (-g 2 / g 0) = -g 2 from by field_simp]
              have hxe := eq_neg_iff_add_eq_zero.mpr
                ((add_assoc (g 0 • (b - a)) (g 1 • (c - a))
                    (g 2 • (d - a))).symm.trans hg)
              rw [hxe, neg_add, neg_smul, neg_smul]
              -- 目标两侧已一致
            exact hout (Submodule.mem_span_pair.mpr ⟨-g 1 / g 0, -g 2 / g 0,
              hu.symm⟩)
        exact absurd hz (w5cA2_li3_triple_ne hli)
      refine ⟨a, c, d, ?_⟩
      intro z hzz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzz
      rcases hzz with rfl | rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · exact w5cA2_mem_affineSpan_of_span2 hmem
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
    · by_cases hca : c - a = 0
      · refine ⟨a, b, d, ?_⟩
        intro z hzz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzz
        rcases hzz with rfl | rfl | rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
        · rw [show z = a from sub_eq_zero.mp hca]; exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
      · obtain ⟨f, g, hsum, hne⟩ :=
          (Fintype.not_linearIndependent_iffₛ (v := ![c - a, d - a])).mp hind
        have hkey : ∑ i, (f i - g i) • (![c - a, d - a] i) = 0 := by
          have hterm : ∀ i : Fin 2, (f i - g i) • (![c - a, d - a] i)
              = f i • (![c - a, d - a] i) - g i • (![c - a, d - a] i) :=
            fun i => sub_smul _ _ _
          rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
            hsum, sub_self]
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          at hkey
        by_cases hk0 : f 0 - g 0 = 0
        · by_cases hk1 : f 1 - g 1 = 0
          · exfalso
            rcases hne with ⟨i, hi⟩
            fin_cases i
            · rw [show f (⟨0, _⟩ : Fin 2) = g (⟨0, _⟩ : Fin 2) from
                sub_eq_zero.mp hk0] at hi
              exact hi rfl
            · rw [show f (⟨1, _⟩ : Fin 2) = g (⟨1, _⟩ : Fin 2) from
                sub_eq_zero.mp hk1] at hi
              exact hi rfl
          · rw [hk0, zero_smul, zero_add, smul_eq_zero] at hkey
            have hd0 : d - a = 0 := hkey.resolve_left hk1
            refine ⟨a, b, c, ?_⟩
            intro z hzz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzz
            rcases hzz with rfl | rfl | rfl | rfl
            · exact mem_affineSpan ℝ (by simp)
            · exact mem_affineSpan ℝ (by simp)
            · exact mem_affineSpan ℝ (by simp)
            · exact w5cA2_mem_affineSpan_of_span2
                (by rw [hd0]; exact Submodule.zero_mem _)
        · by_cases hk1 : f 1 - g 1 = 0
          · rw [hk1, zero_smul, add_zero, smul_eq_zero] at hkey
            exact (hca (hkey.resolve_left hk0)).elim
          · have hdv : d - a = (-(f 0 - g 0) / (f 1 - g 1)) • (c - a) := by
              have hinj := smul_right_injective V3 hk1
              refine hinj ?_
              show (f 1 - g 1) • (d - a)
                = (f 1 - g 1) • ((-(f 0 - g 0) / (f 1 - g 1)) • (c - a))
              rw [smul_smul, show (f 1 - g 1) * (-(f 0 - g 0) / (f 1 - g 1))
                = -(f 0 - g 0) from by field_simp, neg_smul]
              exact eq_neg_of_add_eq_zero_right hkey
            refine ⟨a, b, c, ?_⟩
            intro z hzz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzz
            rcases hzz with rfl | rfl | rfl | rfl
            · exact mem_affineSpan ℝ (by simp)
            · exact mem_affineSpan ℝ (by simp)
            · exact mem_affineSpan ℝ (by simp)
            · exact w5cA2_mem_affineSpan_of_span2
                (Submodule.mem_span_pair.mpr ⟨0, -(f 0 - g 0) / (f 1 - g 1),
                  by rw [hdv]; simp⟩)

/-! ## Section 0.5: fan vocabulary bridge (W7)

LA14 is written over the LocalAuto1 `LocalFan` encoding (`hypermapOfFan`);
the external fan lemmas shipped by LocalAuto5/6/7/9 are stated over the
LocalAuto2 `localFan_p2` encoding.  Every lemma below is either a
definitional equality (`rfl`) or a direct consumer of an already proved
repo lemma (`localFan_p2.of_LocalFan_noIso` (AzimBridge), `EE_elim`,
`AZIM_CYCLE_EQ_SIGMA_FAN_ALT` (LocalAuto2), `LOCAL_FAN_RHO_NODE_PROS`,
`DETER_RHO_NODE`, `EXISTS_INVERSE_OF_V`, `IVS_RHO_NODE1_DETE`,
`FAN_IMP_V_DIFF` (LocalAuto5)); no edge is postulated. -/

/-- W7 bridge (a): every vertex of a `LocalFan` has a neighbour (the
2-regular conjunct), i.e. the no-isolated hypothesis of
`localFan_p2.of_LocalFan_noIso` (HOL `LOFA_IMP_EE_TWO_ELMS` FAN-side). -/
private theorem w5cA7_hedge_of_LocalFan {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) :
    ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  obtain ⟨hfan, x, hx, -, -, hreg⟩ := h
  intro v hv
  have h2 : (ee v E).ncard = 2 := hreg v hv
  have hne : (ee v E).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty.mp hc, Set.ncard_empty] at h2
    norm_num at h2
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw⟩

/-- W7 bridge (b): `LocalFan` (LA1 hypermap encoding) implies LA2's
`localFan_p2`.  Proof = the proved AzimBridge transport
`localFan_p2.of_LocalFan_noIso` fed with bridge (a). -/
private theorem w5cA7_localFan_p2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) : localFan_p2 V E FF :=
  localFan_p2.of_LocalFan_noIso h (w5cA7_hedge_of_LocalFan h)

/-- W7 bridge (c): the two `rho_node1` spellings are definitionally equal. -/
private theorem w5cA7_rhoNode1_eq (FF : Set (V3 × V3)) (v : V3) :
    rhoNode1 FF v = rhoNode1_p2 FF v := rfl

/-- W7 bridge (d): the two `ivs_rho_node1` spellings are definitionally equal. -/
private theorem w5cA7_ivsRhoNode1_eq (FF : Set (V3 × V3)) (v : V3) :
    ivsRhoNode1 FF v = ivsRhoNode1_p2 FF v := rfl

/-- W7 bridge (e): the two `interior_angle1` spellings are definitionally
equal (both bodies are the same `azim x v (rho v) (ivs v)`). -/
private theorem w5cA7_interiorAngle1_eq (x : V3) (FF : Set (V3 × V3)) (v : V3) :
    interiorAngle1 x FF v = interiorAngle1_p2 x FF v := rfl

/-- W7 bridge (f): `azim_in_fan` (LA1, `sigmaFan` body) = `azim_in_fan_p2`
(LA2, `EE`+`azim_cycle` body) on fan darts.  Route: `EE_elim` identifies the
two guard sets, `AZIM_CYCLE_EQ_SIGMA_FAN_ALT` identifies the successor. -/
private theorem w5cA7_azimInFan_p2_eq {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) {d : V3 × V3} (hd : d ∈ Fan.dart1OfFan V E) :
    azimInFan d E = azimInFan_p2 d E := by
  have hw : d.2 ∈ Fan.setOfEdge d.1 V E := by
    rw [← Fan.properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan]
    exact hd
  have hso : Fan.setOfEdge d.1 Set.univ E = Fan.setOfEdge d.1 V E := by
    rw [← EE_elim hfan d.1]
    simp [Fan.setOfEdge, EE_p2]
  have hsf : Fan.sigmaFan 0 Set.univ E d.1 d.2 = Fan.sigmaFan 0 V E d.1 d.2 := by
    unfold Fan.sigmaFan
    rw [hso]
  unfold azimInFan azimInFan_p2
  by_cases hnc : 1 < (ee d.1 E).ncard
  · rw [if_pos hnc, if_pos (show 1 < (EE_p2 d.1 E).ncard from hnc), hsf,
      EE_elim hfan d.1]
    exact congrArg (azim 0 d.1 d.2) (AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hw).symm
  · rw [if_neg hnc, if_neg (show ¬(1 < (EE_p2 d.1 E).ncard) from hnc)]

/-- W7 bridge (g): `wedge_in_fan_ge` (LA1) = `wedge_in_fan_ge_p2` (LA2) on
fan darts (same route as bridge (f)). -/
private theorem w5cA7_wedgeInFanGe_p2_eq {V : Set V3} {E : Set (Set V3)}
    (hfan : Fan.FAN 0 V E) {d : V3 × V3} (hd : d ∈ Fan.dart1OfFan V E) :
    wedgeInFanGe d E = wedgeInFanGe_p2 d E := by
  have hw : d.2 ∈ Fan.setOfEdge d.1 V E := by
    rw [← Fan.properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan]
    exact hd
  have hso : Fan.setOfEdge d.1 Set.univ E = Fan.setOfEdge d.1 V E := by
    rw [← EE_elim hfan d.1]
    simp [Fan.setOfEdge, EE_p2]
  have hsf : Fan.sigmaFan 0 Set.univ E d.1 d.2 = Fan.sigmaFan 0 V E d.1 d.2 := by
    unfold Fan.sigmaFan
    rw [hso]
  have hee : ee d.1 E = Fan.setOfEdge d.1 V E := by
    rw [← EE_elim hfan d.1]
    rfl
  unfold wedgeInFanGe wedgeInFanGe_p2
  rw [hee, EE_elim hfan d.1, hsf, AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hw]
  rfl

/-- W7 bridge (h): a face dart of a `LocalFan` is a fan dart
(`AzimBridge.localFan_data` supplies `FF ⊆ dart1OfFan`). -/
private theorem w5cA7_mem_dart_of_face {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {x : V3 × V3} (hx : x ∈ FF) :
    x ∈ Fan.dart1OfFan V E := by
  obtain ⟨-, d, hd, -, -, hsub, -⟩ := localFan_data h
  exact hsub hx

/-- W7 bridge (i): the `rho_node1` dart `(v, rho v)` is in `FF`
(HOL `LOCAL_FAN_RHO_NODE_PROS` Fst, LA5). -/
private theorem w5cA7_rho_mem_FF {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {v : V3} (hv : v ∈ V) :
    (v, rhoNode1 FF v) ∈ FF := by
  have h2 := w5cA7_localFan_p2 h
  have hmem := (LOCAL_FAN_RHO_NODE_PROS h2).1 v hv
  rwa [← w5cA7_rhoNode1_eq] at hmem

/-- W7 bridge (j): the `ivs_rho_node1` dart `(ivs v, v)` is in `FF`
(via `EXISTS_INVERSE_OF_V` + `IVS_RHO_NODE1_DETE`, both LA5). -/
private theorem w5cA7_ivs_mem_FF {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {v : V3} (hv : v ∈ V) :
    (ivsRhoNode1 FF v, v) ∈ FF := by
  have h2 := w5cA7_localFan_p2 h
  obtain ⟨vv, hvv, hrv⟩ := EXISTS_INVERSE_OF_V h2 hv
  have hd : (vv, v) ∈ FF := by
    rw [← hrv]
    exact w5cA7_rho_mem_FF h hvv
  have hivs : ivsRhoNode1_p2 FF v = vv := IVS_RHO_NODE1_DETE h2 hd
  rw [w5cA7_ivsRhoNode1_eq, hivs]
  exact hd

/-- W7 bridge (k): a dart in `FF` determines `rho_node1`
(HOL `DETER_RHO_NODE`, LA5). -/
private theorem w5cA7_deter_rho {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {v w : V3} (hw : (v, w) ∈ FF) :
    rhoNode1 FF v = w := by
  rw [w5cA7_rhoNode1_eq]
  exact DETER_RHO_NODE (w5cA7_localFan_p2 h) hw

/-- W7 bridge (l): a dart in `FF` determines `ivs_rho_node1`
(HOL `IVS_RHO_NODE1_DETE`, LA5). -/
private theorem w5cA7_deter_ivs {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {vv v : V3} (hv : (vv, v) ∈ FF) :
    ivsRhoNode1 FF v = vv := by
  rw [w5cA7_ivsRhoNode1_eq]
  exact IVS_RHO_NODE1_DETE (w5cA7_localFan_p2 h) hv

/-- W7 bridge (n): the p2-vocabulary pointwise inangle identity (same proof
as LA9's private `p9_inangle_eq_azimInFan`, restated locally so that no
private name / extra lane import leaks in). -/
private theorem w5cA7_inangle_eq_azimInFan_p2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (hlf : localFan_p2 V E FF) {v : V3} (hv : v ∈ V) :
    interiorAngle1_p2 0 FF v = azimInFan_p2 (v, rhoNode1_p2 FF v) E := by
  have hpro := LOCAL_FAN_RHO_NODE_PROS2 hlf
  have hdart : (v, rhoNode1_p2 FF v) ∈ FF := hpro.2 v hv
  obtain ⟨vv, hvv, hrv⟩ := EXISTS_INVERSE_OF_V hlf hv
  have hEE : EE_p2 v E = {rhoNode1_p2 FF v, vv} := LOFA_IMP_EE_TWO_ELMS hlf hvv hrv
  have hcyc : azimCycle_p2 (EE_p2 v E) 0 v (rhoNode1_p2 FF v) = vv := by
    rw [hEE]
    exact AZIM_CYCLE_TWO_POINT_SET (rhoNode1_p2 FF v) vv 0 v
  have hinj : Set.InjOn (rhoNode1_p2 FF) V :=
    (SELF_CYCLIC_IMP_BIJ (rhoNode1_p2 FF) V
      (fun x hx => (LOCAL_FAN_ORBIT_MAP_V hlf hx).symm)).2.1
  have hpre : (vv, v) ∈ FF := by rw [← hrv]; exact hpro.2 vv hvv
  have hivs : ivsRhoNode1_p2 FF v = vv := by
    refine RHO_NODE_INVERSE_POINT hpre fun ww hw => ?_
    have hv' : v = rhoNode1_p2 FF ww :=
      congrArg Prod.snd (hpro.1 (ww, v) hw)
    exact hinj (LOCAL_FAN_IMP_IN_V2 hlf hw).1 hvv (hv'.symm.trans hrv.symm)
  show azim 0 v (rhoNode1_p2 FF v) (ivsRhoNode1_p2 FF v)
      = azimInFan_p2 (v, rhoNode1_p2 FF v) E
  rw [hivs]
  have h2 : azimInFan_p2 (v, rhoNode1_p2 FF v) E
      = azim 0 v (rhoNode1_p2 FF v) vv := by
    rw [LOFA_DETERMINE_AZIM_IN_FA hlf hdart]
    exact congrArg (azim 0 (v, rhoNode1_p2 FF v).1 (v, rhoNode1_p2 FF v).2) hcyc
  rw [h2]

/-- W7 bridge (m): vertices of a `LocalFan` are off the apex
(HOL `LOFA_IMP_V_DIFF`, from `FAN_IMP_V_DIFF`, LA5). -/
private theorem w5cA7_v_ne_zero {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) {u : V3} (hu : u ∈ V) :
    u ≠ 0 :=
  FAN_IMP_V_DIFF h.1 u hu

/-! ## Section 1: the theorems of ZLZTHIC.hl, in source order -/

/-- HOL `NONPLANAR_OPEN` (hl:33): coplanarity is an open condition along
continuous curves. -/
theorem NONPLANAR_OPEN_p14 (v1 v2 v3 v4 : ℝ → V3) (t : ℝ)
    (h : ¬ Coplanar ({v1 t, v2 t, v3 t, v4 t} : Set V3))
    (hc1 : ContinuousAt v1 t) (hc2 : ContinuousAt v2 t) (hc3 : ContinuousAt v3 t)
    (hc4 : ContinuousAt v4 t) :
    ∃ e : ℝ, 0 < e ∧ ∀ t', |t - t'| < e →
      ¬ Coplanar ({v1 t', v2 t', v3 t', v4 t'} : Set V3) := by
  have hG : ContinuousAt
      (fun x => (v2 x - v1 x) ⬝ᵥ cross3 (v3 x - v1 x) (v4 x - v1 x)) t :=
    w5cA2_continuousAt_dot (hc2.sub hc1)
      (w5cA2_continuousAt_cross3 (hc3.sub hc1) (hc4.sub hc1))
  have hne : (fun x => (v2 x - v1 x) ⬝ᵥ cross3 (v3 x - v1 x) (v4 x - v1 x)) t ≠ 0 :=
    fun hz => h (w5cA2_coplanar_triple.mpr hz)
  obtain ⟨e, he, hne'⟩ := w5cA2_eventually_ne hG hne
  exact ⟨e, he, fun t' ht hc => hne' t' ht (w5cA2_coplanar_triple.mp hc)⟩

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
  have htriple : (cross3 (cross3 v w) v) ⬝ᵥ w = (cross3 v w) ⬝ᵥ (cross3 v w) := by
    rw [dot3_eq_p14, dot3_eq_p14, coe_cross3_p14, coe_cross3_p14]
    conv_lhs => rw [dotProduct_comm]
    rw [triple_product_permutation]
  have hdot : 0 < (cross3 (cross3 v w) v) ⬝ᵥ w := by
    rw [htriple]
    exact dot3_self_pos_p14 hc
  obtain ⟨t, ht, hsin⟩ := JBDNJJB (u := cross3 v w) (v := v) (w := w) hncv hncw
  have hdotcoe : (cross3 (cross3 v w) v) ⬝ᵥ w =
      (crossProduct (cross3 v w).ofLp v.ofLp) ⬝ᵥ w.ofLp := by
    rw [dot3_eq_p14, coe_cross3_p14]
  have hspos : 0 < Real.sin (azim 0 (cross3 v w) v w) := by
    rw [hsin, ← hdotcoe]
    exact mul_pos ht hdot
  have haz : azim 0 (cross3 v w) v w < Real.pi := by
    rcases lt_or_ge (azim 0 (cross3 v w) v w) Real.pi with hlt | hge
    · exact hlt
    · exfalso
      have hpos : 0 ≤ azim 0 (cross3 v w) v w - Real.pi := by linarith
      have hle : azim 0 (cross3 v w) v w - Real.pi ≤ Real.pi := by
        have := azim_lt_two_pi 0 (cross3 v w) v w; linarith
      have hsn : 0 ≤ Real.sin (azim 0 (cross3 v w) v w - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hpos hle
      have hsub : Real.sin (azim 0 (cross3 v w) v w - Real.pi) =
          -Real.sin (azim 0 (cross3 v w) v w) := by
        rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]; ring
      rw [hsub] at hsn
      linarith
  exact WEDGE_GE_EQ_AFF_GE haz hncv hncw

/-- w5cA6: `sin (azim …) > 0` characterizes the `(0, π)` range (private
twin of the LocalAuto21 `sin_azim_pos_p21`, kept local to avoid an import). -/
private theorem w5cA6_sin_azim_pos (v1 v2 v3 v4 : V3) :
    0 < Real.sin (azim v1 v2 v3 v4) ↔
      (0 < azim v1 v2 v3 v4 ∧ azim v1 v2 v3 v4 < Real.pi) := by
  have hnn : 0 ≤ azim v1 v2 v3 v4 := azim_nonneg v1 v2 v3 v4
  have h2π : azim v1 v2 v3 v4 < 2 * Real.pi := azim_lt_two_pi v1 v2 v3 v4
  constructor
  · intro h
    rcases lt_or_ge (azim v1 v2 v3 v4) Real.pi with hlt | hge
    · refine ⟨?_, hlt⟩
      by_contra hnonpos
      have h0 : azim v1 v2 v3 v4 = 0 := le_antisymm (not_lt.mp hnonpos) hnn
      rw [h0] at h
      simp at h
    · exfalso
      have hpos : 0 ≤ azim v1 v2 v3 v4 - Real.pi := by linarith
      have hle : azim v1 v2 v3 v4 - Real.pi ≤ Real.pi := by linarith
      have hsn : 0 ≤ Real.sin (azim v1 v2 v3 v4 - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hpos hle
      have hsub : Real.sin (azim v1 v2 v3 v4 - Real.pi) = -Real.sin (azim v1 v2 v3 v4) := by
        rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]
        ring
      rw [hsub] at hsn
      linarith
  · rintro ⟨h1, h2⟩
    exact Real.sin_pos_of_mem_Ioo ⟨h1, h2⟩

/-- W7 helper: `{0, v×w, v}` is non-collinear when `{0,v,w}` is. -/
private theorem w5cA7_not_coll_cross_left {v w : V3}
    (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    ¬ Collinear ℝ ({0, cross3 v w, v} : Set V3) := by
  intro hcol
  obtain ⟨t, htv⟩ := smul_of_collinear0_p14 (cross3_ne_p14 h) hcol
  have hu0c := inner_cross3_dotL_p14 v w
  nth_rewrite 2 [htv] at hu0c
  rw [inner_smul_right] at hu0c
  rcases mul_eq_zero.mp hu0c with hzero | hczero
  · rw [hzero, zero_smul] at htv
    have hv0 : v ≠ 0 := by
      intro hh; exact h (by rw [hh]; simpa using collinear2_p14 0 w)
    exact hv0 (by rw [htv])
  · linarith [hczero, inner_cross3_self_pos_p14 v w h]

/-- W7 helper: `{0, v×w, w}` is non-collinear when `{0,v,w}` is. -/
private theorem w5cA7_not_coll_cross_right {v w : V3}
    (h : ¬ Collinear ℝ ({0, v, w} : Set V3)) :
    ¬ Collinear ℝ ({0, cross3 v w, w} : Set V3) := by
  intro hcol
  obtain ⟨t, htw⟩ := smul_of_collinear0_p14 (cross3_ne_p14 h) hcol
  have hu0c := inner_cross3_dotR_p14 v w
  nth_rewrite 2 [htw] at hu0c
  rw [inner_smul_right] at hu0c
  rcases mul_eq_zero.mp hu0c with hzero | hczero
  · rw [hzero, zero_smul] at htw
    have hw0 : w ≠ 0 := by
      intro hh; exact h (by rw [hh]; simpa using collinear2_p14 v 0)
    exact hw0 (by rw [htw])
  · linarith [hczero, inner_cross3_self_pos_p14 v w h]

/-- HOL `azim_lt_pi_cross` (hl:107).  NEEDS: azim sign theory. -/
theorem azim_lt_pi_cross_p14 (u1 u2 u3 : V3) :
    (0 < azim 0 u1 u2 u3 ∧ azim 0 u1 u2 u3 < Real.pi) ↔
      0 < (cross3 u1 u2) ⬝ᵥ u3 := by
  have hdotcoe : (cross3 u1 u2) ⬝ᵥ u3 =
      (crossProduct u1.ofLp u2.ofLp) ⬝ᵥ u3.ofLp := by
    rw [dot3_eq_p14, coe_cross3_p14]
  have hdeg : Collinear ℝ ({0, u1, u2} : Set V3) ∨
      Collinear ℝ ({0, u1, u3} : Set V3) → (cross3 u1 u2) ⬝ᵥ u3 = 0 := by
    rintro (hc | hc)
    · have hz : cross3 u1 u2 = 0 := w5cA_collinear_cross3_eq hc
      rw [hz, dot3_comm_p14, dot3_zero_right_p14]
    · rcases eq_or_ne u1 0 with h0 | h0
      · subst h0
        have hz0 : cross3 (0 : V3) u2 = 0 := by
          apply w5cA_collinear_cross3_eq
          simpa using collinear2_p14 (0 : V3) u2
        rw [hz0, dot3_comm_p14, dot3_zero_right_p14]
      · obtain ⟨t, ht⟩ := smul_of_collinear0_p14 h0 hc
        rw [ht]
        simp only [coe_smul_p14]
        rw [dot3_smul_right_p14, cross3_dotL_p14, mul_zero]
  constructor
  · rintro ⟨hpos, hlt⟩
    have hnc12 : ¬ Collinear ℝ ({0, u1, u2} : Set V3) := by
      intro hc
      have hz : azim 0 u1 u2 u3 = 0 := by
        unfold azim
        exact if_pos (Or.inl (show Collinear3 0 u1 u2 from hc))
      rw [hz] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hnc13 : ¬ Collinear ℝ ({0, u1, u3} : Set V3) := by
      intro hc
      have hz : azim 0 u1 u2 u3 = 0 := by
        unfold azim
        exact if_pos (Or.inr (show Collinear3 0 u1 u3 from hc))
      rw [hz] at hpos
      exact absurd hpos (lt_irrefl 0)
    obtain ⟨t, ht, hsin⟩ := JBDNJJB (u := u1) (v := u2) (w := u3) hnc12 hnc13
    have hspos : 0 < Real.sin (azim 0 u1 u2 u3) :=
      Real.sin_pos_of_pos_of_lt_pi hpos hlt
    rw [hsin] at hspos
    rw [hdotcoe]
    exact pos_of_mul_pos_right hspos (le_of_lt ht)
  · intro hd
    have hnc12 : ¬ Collinear ℝ ({0, u1, u2} : Set V3) := by
      intro hc
      rw [hdeg (Or.inl hc)] at hd
      exact absurd hd (lt_irrefl 0)
    have hnc13 : ¬ Collinear ℝ ({0, u1, u3} : Set V3) := by
      intro hc
      rw [hdeg (Or.inr hc)] at hd
      exact absurd hd (lt_irrefl 0)
    obtain ⟨t, ht, hsin⟩ := JBDNJJB (u := u1) (v := u2) (w := u3) hnc12 hnc13
    have hprod : 0 < t * ((crossProduct u1.ofLp u2.ofLp) ⬝ᵥ u3.ofLp) := by
      rw [← hdotcoe]
      exact mul_pos ht hd
    have hspos : 0 < Real.sin (azim 0 u1 u2 u3) := by
      rw [hsin]
      exact hprod
    exact (w5cA6_sin_azim_pos 0 u1 u2 u3).mp hspos

/-- W7 helper: `aff_lt {0} {u}` is the open opposite ray (u ≠ 0). -/
private theorem w5cA7_mem_affLt_ray0 {u y : V3} (hu : u ≠ 0) :
    y ∈ affLt ({0} : Set V3) ({u} : Set V3) ↔ ∃ t : ℝ, t < 0 ∧ y = t • u := by
  rw [AFF_LT_1_1_p9 (0:V3) u (Ne.symm hu)]
  constructor
  · rintro ⟨t1, t2, ht2, -, hy⟩
    exact ⟨t2, ht2, by rw [hy]; simp⟩
  · rintro ⟨t, ht, hy⟩
    exact ⟨1 - t, t, ht, by ring, by rw [hy]; simp⟩

/-- W7 helper: non-negative coefficients in `span{v,w}` put a point in
`aff_ge {0} {v,w}`. -/
private theorem w5cA7_mem_affGe_pair_of_coeff {v w z : V3}
    (hdisj : Disjoint ({0} : Set V3) ({v, w} : Set V3)) (hvw : v ≠ w)
    (h : ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ z = c • v + d • w) :
    z ∈ affGe ({0} : Set V3) ({v, w} : Set V3) := by
  obtain ⟨c, d, hc, hd, hz⟩ := h
  rw [mem_affGe_singleton_pair hdisj hvw]
  exact ⟨1 - c - d, c, d, hc, hd, by ring, by rw [hz]; simp⟩

/-- W7 helper: coordinate form of `aff_ge {0, n} {v, w}` (the axial
coefficient is free, the `v,w` coefficients are non-negative). -/
private theorem w5cA7_affGe_axis_decomp {v w n y : V3}
    (hdis : Disjoint ({0, n} : Set V3) ({v, w} : Set V3)) :
    y ∈ affGe ({0, n} : Set V3) ({v, w} : Set V3) ↔
      ∃ b c d : ℝ, y = b • n + c • v + d • w ∧ 0 ≤ c ∧ 0 ≤ d := by
  rw [AFF_GE_2_2 (0:V3) n v w hdis]
  constructor
  · rintro ⟨t1, t2, t3, t4, ht3, ht4, -, hy⟩
    exact ⟨t2, t3, t4, by rw [hy]; simp, ht3, ht4⟩
  · rintro ⟨b, c, d, hy, hc, hd⟩
    exact ⟨1 - b - c - d, b, c, d, hc, hd, by ring, by rw [hy]; simp⟩

/-- W7 helper: `wedge 0 (v×w) w v` is the complement of the axial slab
`affGe {0, v×w} {v,w}` (via `WEDGE_GE_COMPLEMENT` + `wedge_ge_cross`). -/
private theorem w5cA7_wedge_compl {v w : V3}
    (h1 : ¬ Collinear ℝ ({0, v, w} : Set V3)) (z : V3) :
    z ∈ Kepler.Geom.wedge 0 (cross3 v w) w v ↔
      z ∉ affGe ({0, cross3 v w} : Set V3) ({v, w} : Set V3) := by
  have haz0 : azim 0 (cross3 v w) v w ≠ 0 := azim_cross_0_p14 v w h1
  have hcomp := WEDGE_GE_COMPLEMENT (0:V3) (cross3 v w) v w haz0
  have hwg := wedge_ge_cross_p14 v w h1
  have hstep : z ∈ Kepler.Geom.wedge 0 (cross3 v w) w v ↔
      z ∈ (Set.univ \ wedgeGe 0 (cross3 v w) v w) := by
    rw [hcomp]
    exact Iff.rfl
  rw [hstep, hwg]
  simp

/-- HOL `generic_alt` (hl:142).  NEEDS: generic wedge theory. -/
theorem generic_alt_p14 (u v w : V3) (h1 : ¬ Collinear ℝ ({0, v, w} : Set V3))
    (h2 : u ≠ 0) :
    affGe ({0} : Set V3) ({v, w} : Set V3) ∩ affLt ({0} : Set V3) ({u} : Set V3) = ∅ ↔
      ¬ Coplanar ({0, u, v, w} : Set V3) ∨ (-u) ∈ Kepler.Geom.wedge 0 (cross3 v w) w v := by
  have hv0 : v ≠ 0 := by
    intro h; exact h1 (by rw [h]; simpa using collinear2_p14 0 w)
  have hw0 : w ≠ 0 := by
    intro h; exact h1 (by rw [h]; simpa using collinear2_p14 v 0)
  have hvw : v ≠ w := by
    intro h; exact h1 (by simpa [h] using collinear2_p14 0 v)
  have hn : cross3 v w ≠ 0 := cross3_ne_p14 h1
  have hnv : cross3 v w ≠ v := by
    intro he
    have hdot := cross3_dotL_p14 v w
    rw [he] at hdot
    exact hv0 (dot3_self_zero_p14 hdot)
  have hnw : cross3 v w ≠ w := by
    intro he
    have hdot := cross3_dotR_p14 v w
    rw [he] at hdot
    exact hw0 (dot3_self_zero_p14 hdot)
  have hdisj0 : Disjoint ({0} : Set V3) ({v, w} : Set V3) := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hz2
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rcases Set.mem_insert_iff.mp hz2 with h | h
    · exact hv0 h.symm
    · exact hw0 (Set.mem_singleton_iff.mp h).symm
  have hdisjn : Disjoint ({0, cross3 v w} : Set V3) ({v, w} : Set V3) := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hz2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hz2
    rcases hz with rfl | rfl <;> rcases hz2 with h | h
    · exact hv0 h.symm
    · exact hw0 h.symm
    · exact hnv h
    · exact hnw h
  have hdotcop : (cross3 v w) ⬝ᵥ u = 0 ↔ Coplanar ({0, u, v, w} : Set V3) := by
    have h := CROSS_DOT_COPLANAR (x := v) (y := w) (z := u)
    have hset : ({0, v, w, u} : Set V3) = ({0, u, v, w} : Set V3) := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset] at h
    exact h
  constructor
  · intro hemp
    by_cases hcop : Coplanar ({0, u, v, w} : Set V3)
    · right
      rw [w5cA7_wedge_compl h1]
      intro hmem
      obtain ⟨b, c, d, hbd, hc, hd⟩ := (w5cA7_affGe_axis_decomp hdisjn).mp hmem
      have hnu : (cross3 v w) ⬝ᵥ u = 0 := hdotcop.mpr hcop
      have hdot : (cross3 v w) ⬝ᵥ (-u) =
          b * ((cross3 v w) ⬝ᵥ (cross3 v w)) := by
        have h1 : (cross3 v w) ⬝ᵥ (-u) =
            (cross3 v w) ⬝ᵥ (b • cross3 v w + c • v + d • w) :=
          congrArg (fun z : V3 => (cross3 v w) ⬝ᵥ z) hbd
        rw [h1, dot3_add_right_p14, dot3_add_right_p14, dot3_smul_right_p14,
          dot3_smul_right_p14, dot3_smul_right_p14, cross3_dotL_p14,
          cross3_dotR_p14, mul_zero, mul_zero, add_zero, add_zero]
      have hb0 : b = 0 := by
        rw [w5cA2_dot_neg_right, hnu, neg_zero] at hdot
        rcases mul_eq_zero.mp hdot.symm with hb | hn2
        · exact hb
        · exact absurd hn2 (ne_of_gt (dot3_self_pos_p14 hn))
      have hbdeq : (-u) = c • v + d • w := by
        rw [hbd, hb0, zero_smul, zero_add]
      have hlt : (-u) ∈ affLt ({0} : Set V3) ({u} : Set V3) := by
        rw [w5cA7_mem_affLt_ray0 h2]
        exact ⟨-1, by norm_num, by simp⟩
      have hge : (-u) ∈ affGe ({0} : Set V3) ({v, w} : Set V3) :=
        w5cA7_mem_affGe_pair_of_coeff hdisj0 hvw ⟨c, d, hc, hd, hbdeq⟩
      have hmem : (-u) ∈ affGe ({0} : Set V3) ({v, w} : Set V3) ∩
          affLt ({0} : Set V3) ({u} : Set V3) := ⟨hge, hlt⟩
      rw [hemp] at hmem
      exact hmem
    · exact Or.inl hcop
  · rintro (hnc | hw)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hge, hlt⟩
      obtain ⟨_, c, d, hrest⟩ := (mem_affGe_singleton_pair (x := (0:V3)) (v := v) (w := w) hdisj0 hvw).mp hge
      obtain ⟨hc, hd, -, hycd⟩ := hrest
      have hycd' : y = c • v + d • w := by simpa using hycd
      obtain ⟨t, ht, hyt⟩ := (w5cA7_mem_affLt_ray0 h2).mp hlt
      have htne : t ≠ 0 := ne_of_lt ht
      have hu : u = t⁻¹ • y := by
        rw [hyt, smul_smul, inv_mul_cancel₀ htne, one_smul]
      have hu2 : u = t⁻¹ • (c • v + d • w) := by rw [hu, hycd']
      have hnu : (cross3 v w) ⬝ᵥ u = 0 := by
        have h1 : (cross3 v w) ⬝ᵥ u =
            (cross3 v w) ⬝ᵥ (t⁻¹ • (c • v + d • w)) :=
          congrArg (fun z : V3 => (cross3 v w) ⬝ᵥ z) hu2
        rw [h1, dot3_smul_right_p14, dot3_add_right_p14,
          dot3_smul_right_p14, dot3_smul_right_p14, cross3_dotL_p14,
          cross3_dotR_p14, mul_zero, mul_zero, add_zero, mul_zero]
      exact hnc (hdotcop.mp hnu)
    · rw [w5cA7_wedge_compl h1] at hw
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hge, hlt⟩
      obtain ⟨_, c, d, hrest⟩ := (mem_affGe_singleton_pair (x := (0:V3)) (v := v) (w := w) hdisj0 hvw).mp hge
      obtain ⟨hc, hd, -, hycd⟩ := hrest
      have hycd' : y = c • v + d • w := by simpa using hycd
      obtain ⟨t, ht, hyt⟩ := (w5cA7_mem_affLt_ray0 h2).mp hlt
      have htne : t ≠ 0 := ne_of_lt ht
      have hcoef : (-u) = (0:ℝ) • (cross3 v w) + ((-1/t) * c) • v + ((-1/t) * d) • w := by
        have hy1 : y = t • u := hyt
        have h1 : (-u) = (-1/t) • y := by
          rw [hy1, smul_smul, div_mul_cancel₀ (-1) htne, neg_one_smul]
        rw [h1, hycd', smul_add, smul_smul, smul_smul]
        simp
      have hpos : 0 < -1/t := div_pos_of_neg_of_neg (by norm_num) ht
      exact hw ((w5cA7_affGe_axis_decomp hdisjn).mpr
        ⟨0, (-1/t) * c, (-1/t) * d, hcoef, mul_nonneg (le_of_lt hpos) hc,
          mul_nonneg (le_of_lt hpos) hd⟩)

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
  obtain ⟨t0, t1, ht1, hv⟩ := vuy1_p14 v u0 u1 h1 h2 h3
  have hApos : 0 < (cross3 u0 u1) ⬝ᵥ (cross3 u0 u1) := by
    have h := inner_cross3_self_pos_p14 u0 u1 h2
    rwa [inner_eq_dot] at h
  have htriple : (cross3 (cross3 u0 u1) u0) ⬝ᵥ u1 =
      (cross3 u0 u1) ⬝ᵥ (cross3 u0 u1) := by
    rw [dot3_eq_p14, dot3_eq_p14, coe_cross3_p14, coe_cross3_p14]
    conv_lhs => rw [dotProduct_comm]
    rw [triple_product_permutation]
  have hzero : (cross3 (cross3 u0 u1) u0) ⬝ᵥ u0 = 0 := cross3_dotR_p14 _ _
  have hexp : (cross3 (cross3 u0 u1) u0) ⬝ᵥ v = t1 * ((cross3 u0 u1) ⬝ᵥ (cross3 u0 u1)) := by
    rw [hv]
    simp only [coe_add_p14, coe_smul_p14]
    rw [dot3_add_right_p14, dot3_smul_right_p14, dot3_smul_right_p14, hzero, htriple]
    ring
  have hpos : 0 < (cross3 (cross3 u0 u1) u0) ⬝ᵥ v := by
    rw [hexp]
    exact mul_pos ht1 hApos
  exact ((azim_lt_pi_cross_p14 (cross3 u0 u1) u0 v).mpr hpos).2

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

/-- HOL `ybt_inj` (hl:358): azimuth is injective on a cone `aff_ge {0,u0} {u1}`
above the base ray `u0`, seen from the axis `u0 × u1`. -/
theorem ybt_inj_p14 (u0 u1 v1 v2 : V3) (h1 : ¬ Collinear ℝ ({0, u0, v1} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, u0, v2} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, u0, u1} : Set V3))
    (h4 : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (h5 : v1 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3))
    (h6 : v2 ∈ affGe ({0, u0} : Set V3) ({u1} : Set V3)) :
    ¬ (azim 0 (cross3 u0 u1) u0 v1 = azim 0 (cross3 u0 u1) u0 v2) := by
  obtain ⟨a0, a1, ha1, hv1⟩ := vuy1_p14 v1 u0 u1 h1 h3 h5
  obtain ⟨b0, b1, hb1, hv2⟩ := vuy1_p14 v2 u0 u1 h2 h3 h6
  have hcne : cross3 u0 u1 ≠ 0 := cross3_ne_p14 h3
  have hv20 : v2 ≠ 0 := by
    intro hzero
    exact h2 (by rw [hzero]; simpa using collinear2_p14 u0 0)
  have hncu0 : ¬ Collinear ℝ ({0, cross3 u0 u1, u0} : Set V3) := by
    intro hcol
    obtain ⟨t, htu0⟩ := smul_of_collinear0_p14 hcne hcol
    have hu0c := inner_cross3_dotL_p14 u0 u1
    nth_rewrite 2 [htu0] at hu0c
    rw [inner_smul_right] at hu0c
    rcases mul_eq_zero.mp hu0c with hzero | hczero
    · rw [hzero, zero_smul] at htu0
      exact h3 (by rw [htu0]; simpa using collinear2_p14 0 u1)
    · linarith [hczero, inner_cross3_self_pos_p14 u0 u1 h3]
  have hncv1 : ¬ Collinear ℝ ({0, cross3 u0 u1, v1} : Set V3) :=
    vuy3_p14 v1 u0 u1 h1 h3 h5
  have hncv2 : ¬ Collinear ℝ ({0, cross3 u0 u1, v2} : Set V3) :=
    vuy3_p14 v2 u0 u1 h2 h3 h6
  have hnc : v2 ≠ cross3 u0 u1 := by
    intro heq
    have hp : inner ℝ (cross3 u0 u1) v2 = 0 := by
      rw [hv2, inner_add_right, inner_smul_right, inner_smul_right,
        inner_cross3_dotL_p14, inner_cross3_dotR_p14]
      ring
    rw [heq] at hp
    exact (inner_cross3_self_pos_p14 u0 u1 h3).ne' hp
  intro haz
  have hmem : v1 ∈ affGt ({0, cross3 u0 u1} : Set V3) ({v2} : Set V3) :=
    (azim_eq_azim_iff hncu0 hncv2 hncv1).mp haz.symm
  obtain ⟨c, hc, k, hvk⟩ :=
    (affGt_pair_iff (v0 := 0) (v1 := cross3 u0 u1) (x := v2) (y := v1)
      (Ne.symm hcne) hv20 hnc).mp hmem
  have hvk' : v1 = c • v2 + k • cross3 u0 u1 := by simpa only [sub_zero] using hvk
  have hkey : k • cross3 u0 u1 + (c * b0 - a0) • u0 + (c * b1 - a1) • u1 = 0 := by
    have h0 : c • v2 + k • cross3 u0 u1 = a0 • u0 + a1 • u1 := by rw [← hvk', ← hv1]
    rw [hv2] at h0
    have h1' : k • cross3 u0 u1 + (c * b0 - a0) • u0 + (c * b1 - a1) • u1
        = c • (b0 • u0 + b1 • u1) + k • cross3 u0 u1 - (a0 • u0 + a1 • u1) := by
      module
    rw [h1', h0, sub_self]
  have hk0 : k = 0 := cross_independent_p14 u0 u1 h3 _ _ _ hkey
  rw [hk0, zero_smul, add_zero] at hvk'
  exact h4 (by rw [hvk']; exact collinear0_smulR_p14 v2 c)

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

/-! ## w10 kit: half-plane azimuth lexicographic order

`YBTASCZ1/2/3` (hl:516/624/656) are the "azimuth increases with the index
along the cyclic order" block.  The missing ingredient over the wave-8
material is the dictionary order on `azim` inside the half-plane
`aff_ge {0,u0}{u1}`.  The kit has four parts:
* `w10_exis_smallest` / `w10_azimCycle_properties`: minimum existence and
  the `AZIM_CYCLE_PROPERTIES`-style characterization of `azimCycle_p14`
  (the wave-5 copy `w5cA_azimCycle_properties` is declared later in the
  file, so the epsilon specification is reproduced here);
* `w10_affGe_of_affGt`: `aff_gt ⊆ aff_ge` (the `vuy1` cone);
* `w10_u_inj`: distinct indices give distinct cone points;
* the proofs of `YBTASCZ1/2/3` use `AZIM_BASE_SHIFT_LE` (PackingAuto18) as
  the base-point shift telescope and `sum4_azim_fan` (TopologyFan) as the
  three-point azimuth addition. -/

/-- w10: on a finite set not contained in `{p}` there is an
`azim`-minimal element with the projection-norm tiebreak (the selection
predicate of `azimCycle_p14` is inhabited). -/
private theorem w10_exis_smallest {W : Set V3} {v w p : V3}
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

/-- w10: characterization of `azimCycle_p14` (the `_p14` copy of the
proved `AZIM_CYCLE_PROPERTIES`), available before the wave-5 block. -/
private theorem w10_azimCycle_properties {W : Set V3} {p : V3} (hsub : ¬(W ⊆ {p}))
    (hfin : W.Finite) (v w : V3) :
    azimCycle_p14 W v w p ≠ p ∧ azimCycle_p14 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p →
        azim v w p (azimCycle_p14 W v w p) < azim v w p q ∨
          azim v w p (azimCycle_p14 W v w p) = azim v w p q ∧
            ‖projection (azimCycle_p14 W v w p - v) (w - v)‖ ≤
              ‖projection (q - v) (w - v)‖ := by
  obtain ⟨u, hu1, hu2, hu3⟩ := w10_exis_smallest hsub hfin
  rw [azimCycle_p14, if_neg hsub]
  exact Classical.epsilon_spec
    (p := fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖)
    ⟨u, hu1, hu2, hu3⟩

/-- w10: `affGt s t ⊆ affGe s t`. -/
private theorem w10_affGe_of_affGt {s t : Set V3} {x : V3} (h : x ∈ affGt s t) :
    x ∈ affGe s t := by
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := h
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- w10: distinct indices in `Icc 0 r` give distinct cone points. -/
private theorem w10_u_inj (u : ℕ → V3) (r : ℕ)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3)) :
    ∀ i j, i ≤ r → j ≤ r → i ≠ j → u i ≠ u j := by
  intro i j hi hj hij heq
  exact h1 i j hi hj hij (by rw [heq]; simpa using collinear2_p14 (0 : V3) (u j))

/-- HOL `YBTASCZ1` (hl:516): azimuth from `u 0` is strictly increasing in
the cyclic index `i < j`.  Induction on `i`: the base case is `ybt_inj_0_p14`
plus `azim_nonneg`; the step rules out `azim(u 0,u j) < azim(u 0,u (i+1))`
by the `AZIM_CYCLE_PROPERTIES` minimality at `u i` and the base shift
`AZIM_BASE_SHIFT_LE` (`u 0` → `u i`), and closes with `ybt_inj_p14`. -/
theorem YBTASCZ1_p14 (u : ℕ → V3) (r j : ℕ) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    ∀ i, i < j →
      azim 0 (cross3 (u 0) (u 1)) (u 0) (u i) < azim 0 (cross3 (u 0) (u 1)) (u 0) (u j) := by
  set c : V3 := cross3 (u 0) (u 1) with hcdef
  have hcross : ∀ i, i ≤ r → ¬ Collinear ℝ ({0, c, u i} : Set V3) := by
    intro i hi
    rw [hcdef]
    exact collinear_cross_p14 u i r hi hr h1 h2
  have hfin : (u '' Set.Icc 0 r).Finite := h3.2.1
  have hmem : ∀ i, i ≤ r → u i ∈ u '' Set.Icc 0 r := by
    intro i hi
    exact ⟨i, ⟨by omega, hi⟩, rfl⟩
  have hune : ∀ i j, i ≤ r → j ≤ r → i ≠ j → u i ≠ u j :=
    w10_u_inj u r h1
  have main : ∀ i, i < j →
      azim 0 c (u 0) (u i) < azim 0 c (u 0) (u j) := by
    intro i
    induction i with
    | zero =>
      intro _hj
      have hj1 : 1 ≤ j := by omega
      rw [azim_self]
      have hjne : azim 0 c (u 0) (u j) ≠ 0 := by
        rw [hcdef]
        exact ybt_inj_0_p14 (u 0) (u 1) (u j)
          (h1 0 j (by omega) hj (by omega))
          (h1 0 1 (by omega) (by omega) (by omega))
          (w10_affGe_of_affGt (h2 j hj1 hj))
      have hnn : 0 ≤ azim 0 c (u 0) (u j) := azim_nonneg _ _ _ _
      exact lt_of_le_of_ne' hnn hjne
    | succ i ih =>
      intro hsucc
      have hij : i < j := by omega
      have hir : i < r := by omega
      have hih : azim 0 c (u 0) (u i) < azim 0 c (u 0) (u j) := ih hij
      have hne : azim 0 c (u 0) (u (i + 1)) ≠ azim 0 c (u 0) (u j) := by
        rw [hcdef]
        exact ybt_inj_p14 (u 0) (u 1) (u (i + 1)) (u j)
          (h1 0 (i + 1) (by omega) (by omega) (by omega))
          (h1 0 j (by omega) hj (by omega))
          (h1 0 1 (by omega) (by omega) (by omega))
          (h1 (i + 1) j (by omega) hj (by omega))
          (w10_affGe_of_affGt (h2 (i + 1) (by omega) (by omega)))
          (w10_affGe_of_affGt (h2 j (by omega) hj))
      refine lt_of_le_of_ne ?_ hne
      by_contra hcon
      push_neg at hcon
      have hsub : ¬ ((u '' Set.Icc 0 r) ⊆ {u i}) := by
        intro hsubmem
        have hmj : u j ∈ (u '' Set.Icc 0 r) := hmem j hj
        have heqj : u j = u i := by simpa using hsubmem hmj
        exact hune i j (by omega) hj (by omega) heqj.symm
      have hcyc := w10_azimCycle_properties (W := u '' Set.Icc 0 r) (p := u i) hsub hfin 0 c
      obtain ⟨-, -, hmin⟩ := hcyc
      have h4i : azimCycle_p14 (u '' Set.Icc 0 r) 0 c (u i) = u (i + 1) := h4 i hir
      have hcyc_le : azim 0 c (u i) (u (i + 1)) ≤ azim 0 c (u i) (u j) := by
        have hqmem : u j ∈ (u '' Set.Icc 0 r) := hmem j hj
        have hqp : u j ≠ u i := fun heq => hune i j (by omega) hj (by omega) heq.symm
        have h := hmin (u j) hqmem hqp
        rw [h4i] at h
        rcases h with h | ⟨h, -⟩
        · exact le_of_lt h
        · exact le_of_eq h
      have hshift := AZIM_BASE_SHIFT_LE (0 : V3) c (u 0) (u i) (u (i + 1)) (u j)
        (hcross 0 (by omega))
        (hcross i (by omega))
        (hcross (i + 1) (by omega))
        (hcross j hj)
        (le_of_lt (hih.trans hcon))
        (le_of_lt hih)
      linarith
  exact main

/-- HOL `YBTASCZ2` (hl:624): the cone-wide angle from `u i` to `u j` is
below `π`.  `YBTASCZ1_p14` gives `azim(u 0,u i) < azim(u 0,u j)`; the
three-point addition `sum4_azim_fan` at the base `u 0` and `vuy4_p14`
(`azim(u 0,u j) < π`) then bound the difference. -/
theorem YBTASCZ2_p14 (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (cross3 (u 0) (u 1)) (u i) (u j) < Real.pi := by
  have hlt := YBTASCZ1_p14 u r j hj hr h1 h2 h3 h4 i hij
  have hsum := sum4_azim_fan (x := (0 : V3)) (v := cross3 (u 0) (u 1))
    (u := u 0) (w1 := u i) (w2 := u j)
    (cross3_ne_p14 (h1 0 1 (by omega) (by omega) (by omega)))
    (collinear_cross_p14 u 0 r (by omega) hr h1 h2)
    (collinear_cross_p14 u i r (by omega) hr h1 h2)
    (collinear_cross_p14 u j r hj hr h1 h2)
    (le_of_lt hlt)
  have h4j := vuy4_p14 (u j) (u 0) (u 1)
    (h1 0 j (by omega) hj (by omega))
    (h1 0 1 (by omega) (by omega) (by omega))
    (w10_affGe_of_affGt (h2 j (by omega) hj))
  have hnn := azim_nonneg (0 : V3) (cross3 (u 0) (u 1)) (u 0) (u i)
  linarith

/-- HOL `YBTASCZ3` (hl:656): the cone-wide angle from `u i` to `u j` is
positive.  Immediate from `YBTASCZ1_p14` plus the three-point addition
`sum4_azim_fan` at the base `u 0`. -/
theorem YBTASCZ3_p14 (u : ℕ → V3) (r i j : ℕ) (hij : i < j) (hj : j ≤ r) (hr : 1 ≤ r)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    0 < azim 0 (cross3 (u 0) (u 1)) (u i) (u j) := by
  have hlt := YBTASCZ1_p14 u r j hj hr h1 h2 h3 h4 i hij
  have hsum := sum4_azim_fan (x := (0 : V3)) (v := cross3 (u 0) (u 1))
    (u := u 0) (w1 := u i) (w2 := u j)
    (cross3_ne_p14 (h1 0 1 (by omega) (by omega) (by omega)))
    (collinear_cross_p14 u 0 r (by omega) hr h1 h2)
    (collinear_cross_p14 u i r (by omega) hr h1 h2)
    (collinear_cross_p14 u j r hj hr h1 h2)
    (le_of_lt hlt)
  linarith

/-! ## w12 port kit: the four unported HOL pieces

`AZIM_SCALE_ALL` (flyspeck_multivariate.ml:2373) — public analogue
`w5cC_azim_scale` exists in LocalAuto31 but is not in the LA14 import
closure; ported privately here with its collinearity helpers.
`AFF_GT_MONO_LEFT` (flyspeck_multivariate.ml:1215) — near-relative
`affGt_mono_base` in ConformingAuto17 (not imported); private port with the
finiteness hypothesis the Lean `Affsign` encoding forces.
`UIVNNRR2 = AFF_GT_EQ_AFFINE_HULL` (trig3.hl:192): `aff_gt X {} = aff X`.
`AFF2_VEC0` (trig2.hl:2648): `aff {0, w} = {x | ∃ k, x = k % w}`.
-/

/-! ### AZIM_SCALE_ALL -/

/-- Collinearity through the origin: `x` on the line `0 v` is a multiple of `v`. -/
private theorem w12_lineMem_smul {v x : V3} (h : x ∈ affineSpan ℝ ({0, v} : Set V3)) :
    ∃ r : ℝ, x = r • v := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  refine ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply] at hr
  simpa using hr.symm

private theorem w12_smul_lineMem (r : ℝ) (v : V3) :
    (r • v) ∈ affineSpan ℝ ({0, v} : Set V3) := by
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r, ?_⟩
  rw [AffineMap.lineMap_apply]
  simp

private theorem w12_collinear3_smul2_fwd {v x : V3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcol : Collinear3 0 v x) : Collinear3 0 (a • v) (b • x) := by
  classical
  rcases (collinear_triple_iff (x := (0:V3)) (v := v) (u := x)).mp hcol with hu | h0
  · obtain ⟨r, hr⟩ := w12_lineMem_smul hu
    have hbv : b • x = (b * r / a) • (a • v) := by
      rw [hr, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show b * r = (b * r / a) * a from by field_simp)
    refine (collinear_triple_iff (x := (0:V3)) (v := a • v) (u := b • x)).mpr
      (Or.inl ?_)
    rw [hbv]
    exact w12_smul_lineMem _ _
  · refine (collinear_triple_iff (x := (0:V3)) (v := a • v) (u := b • x)).mpr
      (Or.inr ?_)
    rw [← h0, smul_zero]

private theorem w12_collinear3_smul2 {v x : V3} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Collinear3 0 v x ↔ Collinear3 0 (a • v) (b • x) := by
  constructor
  · exact w12_collinear3_smul2_fwd ha hb
  · intro hcol
    have h := w12_collinear3_smul2_fwd (a := a⁻¹) (b := b⁻¹)
      (inv_ne_zero ha) (inv_ne_zero hb) hcol
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, smul_smul, inv_mul_cancel₀ hb, one_smul] at h
    exact h

/-- HOL `AZIM_SCALE_ALL` (flyspeck_multivariate.ml:2373): with every scale
positive, the azimuth at the origin is unchanged by independently scaling the
axis and the two ray points. -/
private theorem w12_azim_scale_all {v w1 w2 : V3} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    azim 0 (a • v) (b • w1) (c • w2) = azim 0 v w1 w2 := by
  classical
  have hiff1 := w12_collinear3_smul2 (v := v) (x := w1) (a := a) (b := b)
    (ne_of_gt ha) (ne_of_gt hb)
  have hiff2 := w12_collinear3_smul2 (v := v) (x := w2) (a := a) (b := c)
    (ne_of_gt ha) (ne_of_gt hc)
  show (if Collinear3 0 (a • v) (b • w1) ∨ Collinear3 0 (a • v) (c • w2) then (0:ℝ)
      else Classical.epsilon (AzimSpec 0 (a • v) (b • w1) (c • w2)))
    = (if Collinear3 0 v w1 ∨ Collinear3 0 v w2 then (0:ℝ)
      else Classical.epsilon (AzimSpec 0 v w1 w2))
  by_cases hcol : Collinear3 0 v w1 ∨ Collinear3 0 v w2
  · rcases hcol with h | h
    · rw [if_pos (Or.inl (hiff1.mp h)), if_pos (Or.inl h)]
    · rw [if_pos (Or.inr (hiff2.mp h)), if_pos (Or.inr h)]
  · push_neg at hcol
    have hn1 : ¬ Collinear3 0 (a • v) (b • w1) := fun hh => hcol.1 (hiff1.mpr hh)
    have hn2 : ¬ Collinear3 0 (a • v) (c • w2) := fun hh => hcol.2 (hiff2.mpr hh)
    obtain ⟨h0θ, h2piθ, hh1, hh2, hframes⟩ := azim_master 0 v w1 w2
    have hvne : v ≠ 0 := by
      intro hzz
      apply hcol.1
      rw [hzz]
      exact (collinear_triple_iff (x := (0:V3)) (v := (0:V3)) (u := w1)).mpr (Or.inr rfl)
    refine azim_eq_of_spec (θ := azim 0 v w1 w2) hn1 hn2
      ⟨h0θ, h2piθ, b * hh1 / a, c * hh2 / a, ?_⟩
    intro e1 e2 e3 horth hax _
    have hax' : v = dist v 0 • e3 := by
      have hna : dist (a • v) 0 = a * dist v 0 := by
        rw [dist_zero_right, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ha]
      rw [hna, sub_zero] at hax
      exact smul_right_injective V3 (ne_of_gt ha)
        (show a • (dist v 0 • e3) = a • v by rw [smul_smul]; exact hax.symm) |>.symm
    obtain ⟨psi, r1, r2, hs1, hs2, hr1, hr2⟩ :=
      hframes e1 e2 e3 horth (by rw [sub_zero]; exact hax') hvne
    rw [sub_zero, sub_zero] at hs1 hs2
    have hb1 : (b * hh1 / a) • ((a • v : V3) - 0) = b • (hh1 • v) := by
      rw [sub_zero, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show (b * hh1 / a) * a = b * hh1 from by field_simp)
    have hb2 : (c * hh2 / a) • ((a • v : V3) - 0) = c • (hh2 • v) := by
      rw [sub_zero, smul_smul, smul_smul]
      exact congrArg (fun (s : ℝ) => s • v)
        (show (c * hh2 / a) * a = c * hh2 from by field_simp)
    have hdisp1 : b • w1 = (b * (r1 * Real.cos psi)) • e1
        + (b * (r1 * Real.sin psi)) • e2 + b • (hh1 • v) := by
      rw [hs1, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    have hdisp2 : c • w2 = (c * (r2 * Real.cos (psi + azim 0 v w1 w2))) • e1
        + (c * (r2 * Real.sin (psi + azim 0 v w1 w2))) • e2 + c • (hh2 • v) := by
      conv_lhs => rw [hs2]
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    refine ⟨psi, b * r1, c * r2, ?_, ?_, ?_, ?_⟩
    · rw [show ((b • w1 : V3) - 0) = b • w1 from by rw [sub_zero], hdisp1, hb1,
        mul_assoc b r1 (Real.cos psi), mul_assoc b r1 (Real.sin psi)]
    · rw [show ((c • w2 : V3) - 0) = c • w2 from by rw [sub_zero], hdisp2, hb2,
        mul_assoc c r2 (Real.cos (psi + azim 0 v w1 w2)),
        mul_assoc c r2 (Real.sin (psi + azim 0 v w1 w2))]
    · exact mul_pos hb (hr1 hcol.1)
    · exact mul_pos hc (hr2 hcol.2)

/-! ### AFF_GT_MONO_LEFT -/

/-- HOL `AFF_GT_MONO_LEFT` (flyspeck_multivariate.ml:1215): `affGt` is
monotone in its left (base) argument.  The Lean `Affsign` encoding carries an
explicit finiteness witness, so `(s' ∪ t).Finite` is required. -/
private theorem w12_affGt_mono_left {s s' t : Set V3} (hss : s ⊆ s')
    (hfin : (s' ∪ t).Finite) : affGt s t ⊆ affGt s' t := by
  intro y hy
  simp only [affGt, Set.mem_setOf_eq, Affsign] at hy ⊢
  obtain ⟨f, hS, hyv, hpos, hsum⟩ := hy
  have hsub : (s ∪ t : Set V3) ⊆ s' ∪ t := by
    intro z hz
    simp only [Set.mem_union] at hz ⊢
    rcases hz with h | h
    · exact Or.inl (hss h)
    · exact Or.inr h
  have hsubfin : hS.toFinset ⊆ hfin.toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact hsub hz
  have hgv0 : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ (s ∪ t : Set V3) then f z else 0) = 0 := by
    intro z hz hzs
    exact if_neg (fun hcon => hzs (by
      simp only [Set.Finite.mem_toFinset]
      exact hcon))
  have hgvv : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ (s ∪ t : Set V3) then f z else 0) • z = 0 := by
    intro z hz hzs
    rw [hgv0 z hz hzs, zero_smul]
  refine ⟨fun z => if z ∈ (s ∪ t : Set V3) then f z else 0, hfin, ?_, ?_, ?_⟩
  · show y = ∑ z ∈ hfin.toFinset, (if z ∈ (s ∪ t : Set V3) then f z else 0) • z
    rw [hyv, ← Finset.sum_subset hsubfin hgvv]
    exact Finset.sum_congr rfl (fun z hz => by
      simp only [Set.Finite.mem_toFinset] at hz
      rw [if_pos hz])
  · intro z hzt
    show 0 < (if z ∈ (s ∪ t : Set V3) then f z else 0)
    have hzt' : z ∈ (s ∪ t : Set V3) := Or.inr hzt
    rw [if_pos hzt']
    exact hpos z hzt
  · show ∑ z ∈ hfin.toFinset, (if z ∈ (s ∪ t : Set V3) then f z else 0) = 1
    rw [← hsum, ← Finset.sum_subset hsubfin hgv0]
    exact Finset.sum_congr rfl (fun z hz => by
      simp only [Set.Finite.mem_toFinset] at hz
      rw [if_pos hz])

/-! ### UIVNNRR2 = AFF_GT_EQ_AFFINE_HULL -/

/-- The easy half of `AFF_GT_EQ_AFFINE_HULL`: an `affGt`-combination is an
affine combination. -/
private theorem w12_affGt_empty_subset_affineSpan {s : Set V3} :
    affGt s ∅ ⊆ (affineSpan ℝ s : Set V3) := by
  intro y hy
  simp only [affGt, Set.mem_setOf_eq, Affsign] at hy
  obtain ⟨f, hfin, hyv, -, hone⟩ := hy
  classical
  have hto : ∀ z ∈ hfin.toFinset, z ∈ s := by
    intro z hz
    have hz' : z ∈ s ∪ (∅ : Set V3) := (Set.Finite.mem_toFinset hfin).mp hz
    simpa using hz'
  rcases hfin.toFinset.eq_empty_or_nonempty with hem | hne
  · exfalso
    have h0 : ∑ z ∈ hfin.toFinset, f z = 0 := by rw [hem]; simp
    rw [h0] at hone
    exact zero_ne_one hone
  · obtain ⟨p, hp⟩ := hne
    have hps : p ∈ s := hto p hp
    have hpspan : p ∈ (affineSpan ℝ s : Set V3) := mem_affineSpan ℝ hps
    have hmem : ∀ z ∈ hfin.toFinset, z - p ∈ (affineSpan ℝ s).direction := by
      intro z hz
      exact AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ (hto z hz)) hpspan
    have hd : (∑ z ∈ hfin.toFinset, f z • (z - p) : V3) ∈
        (affineSpan ℝ s).direction :=
      Submodule.sum_mem (p := (affineSpan ℝ s).direction)
        (fun z hz => Submodule.smul_mem _ _ (hmem z hz))
    have hsumd : ∑ z ∈ hfin.toFinset, f z • (z - p) = y - p := by
      have h1 : ∑ z ∈ hfin.toFinset, f z • (z - p)
          = ∑ z ∈ hfin.toFinset, (f z • z - f z • p) := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [smul_sub]
      have this : ∑ z ∈ hfin.toFinset, f z • (z - p)
          = ∑ z ∈ hfin.toFinset, f z • z - (∑ z ∈ hfin.toFinset, f z) • p := by
        rw [h1, Finset.sum_sub_distrib, Finset.sum_smul]
      rw [this, hyv, hone, one_smul]
    have hy' : y = (∑ z ∈ hfin.toFinset, f z • (z - p)) + p := by
      rw [hsumd]; abel
    rw [hy']
    exact AffineSubspace.vadd_mem_of_mem_direction hd hpspan

/-- HOL `UIVNNRR2 = AFF_GT_EQ_AFFINE_HULL` (trig3.hl:192): the strict
`aff_gt`-cone over a finite set with empty apex is its affine hull. -/
private theorem w12_affGt_empty_eq_affineSpan {s : Set V3} (hs : s.Finite) :
    affGt s ∅ = (affineSpan ℝ s : Set V3) := by
  classical
  refine Set.Subset.antisymm w12_affGt_empty_subset_affineSpan ?_
  intro y hy
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  rw [Set.union_empty]
  -- affine combination representation from Mathlib
  have hrange : Set.range (Subtype.val : s → V3) = s := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩; exact i.2
    · intro hz; exact ⟨⟨z, hz⟩, rfl⟩
  have hy' : y ∈ affineSpan ℝ (Set.range (Subtype.val : s → V3)) := by
    rw [hrange]; exact hy
  obtain ⟨s', w', hsum', hyrep⟩ :=
    (mem_affineSpan_iff_eq_affineCombination (k := ℝ) (V := V3) (P := V3)
      (p1 := y) (p := (Subtype.val : s → V3))).mp hy'
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum'] at hyrep
  -- the candidate coefficient function on V3
  set f : V3 → ℝ := fun z =>
    if h : z ∈ s then (if (⟨z, h⟩ : s) ∈ s' then w' ⟨z, h⟩ else 0) else 0 with hf
  refine ⟨f, hs, ?_, ?_, ?_⟩
  · -- vector sum: y = ∑ z ∈ hs.toFinset, f z • z
    have himg : ∀ i ∈ s', f (i : V3) • (i : V3) = w' i • (i : V3) := by
      intro i hi
      have hfval : f (i : V3) = w' i := by
        simp only [hf]
        rw [dif_pos i.2]
        have hsub : (⟨(i : V3), i.2⟩ : s) = i := Subtype.ext rfl
        rw [if_pos hi, hsub]
      rw [hfval]
    have h1 : ∑ z ∈ s'.image (Subtype.val : s → V3), f z • z
        = ∑ i ∈ s', w' i • (i : V3) := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl himg
      · intro i _ j _ hij
        exact Subtype.ext hij
    have h2 : ∑ z ∈ hs.toFinset, f z • z
        = ∑ z ∈ s'.image (Subtype.val : s → V3), f z • z := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro z hz
        simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hz ⊢
        obtain ⟨i, hi, rfl⟩ := hz
        exact i.2
      · intro z hz hzt
        have hzs : z ∈ s := by simpa using (Set.Finite.mem_toFinset hs).mp hz
        have hfz : f z = 0 := by
          simp only [hf, dif_pos hzs]
          by_cases hin : (⟨z, hzs⟩ : s) ∈ s'
          · exfalso
            apply hzt
            refine Finset.mem_image.mpr ⟨⟨z, hzs⟩, hin, ?_⟩
            rfl
          · rw [if_neg hin]
        rw [hfz, zero_smul]
    rw [h2, h1]
    exact hyrep
  · -- positivity on the (empty) apex
    intro z hz
    simp at hz
  · -- scalar sum
    have himg : ∀ i ∈ s', f (i : V3) = w' i := by
      intro i hi
      simp only [hf]
      rw [dif_pos i.2]
      have hsub : (⟨(i : V3), i.2⟩ : s) = i := Subtype.ext rfl
      rw [if_pos hi, hsub]
    have h1 : ∑ z ∈ s'.image (Subtype.val : s → V3), f z = ∑ i ∈ s', w' i := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl himg
      · intro i _ j _ hij
        exact Subtype.ext hij
    have h2 : ∑ z ∈ hs.toFinset, f z = ∑ z ∈ s'.image (Subtype.val : s → V3), f z := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro z hz
        simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hz ⊢
        obtain ⟨i, hi, rfl⟩ := hz
        exact i.2
      · intro z hz hzt
        have hzs : z ∈ s := by simpa using (Set.Finite.mem_toFinset hs).mp hz
        simp only [hf, dif_pos hzs]
        by_cases hin : (⟨z, hzs⟩ : s) ∈ s'
        · exfalso
          apply hzt
          exact Finset.mem_image.mpr ⟨⟨z, hzs⟩, hin, rfl⟩
        · rw [if_neg hin]
    rw [h2, h1, hsum']

/-! ### AFF2_VEC0 -/

/-- HOL `AFF2_VEC0` (trig2.hl:2648): the affine hull of the origin and a
point `w` is the ray (linear span) of `w`. -/
private theorem w12_aff2_vec0 (w : V3) :
    affineSpan ℝ ({0, w} : Set V3) = {x : V3 | ∃ k : ℝ, x = k • w} := by
  ext x
  constructor
  · intro hx
    have h1 : x ∈ (Submodule.span ℝ ({0, w} : Set V3)).toAffineSubspace :=
      affineSpan_le_toAffineSubspace_span hx
    have h2 : x ∈ Submodule.span ℝ ({w} : Set V3) := by
      rwa [Submodule.mem_toAffineSubspace,
        show ({0, w} : Set V3) = insert 0 {w} from rfl,
        Submodule.span_insert_zero] at h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
    exact ⟨a, ha.symm⟩
  · rintro ⟨k, rfl⟩
    have h := smul_vsub_rev_vadd_mem_affineSpan_pair (k := ℝ) k w (0 : V3)
    rw [show affineSpan ℝ ({w, (0 : V3)} : Set V3) = affineSpan ℝ ({0, w} : Set V3) by
      rw [Set.pair_comm]] at h
    simpa using h

/-! ### Local conv0 extraction (HOL `CONV0_SET2` consumer) -/

/-- Extraction of the strict two-point convex combination. -/
private theorem w12_conv02_extract {a b x : V3} (hx : x ∈ conv0_p2 ({a, b} : Set V3)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β = 1 ∧ x = α • a + β • b := by
  obtain ⟨f, hfin, hvec, hpos, hsum⟩ := hx
  by_cases hab : a = b
  · subst hab
    have hEq : hfin.toFinset = ({a} : Finset V3) := by ext w; simp
    rw [hEq] at hvec hsum
    simp only [Finset.sum_singleton] at hvec hsum
    have hfa : f a = 1 := hsum
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hvec, hfa]
    module
  · have hEq : hfin.toFinset = ({a, b} : Finset V3) := by ext w; simp [hab]
    rw [hEq] at hvec hsum
    simp only [Finset.sum_insert (by simp [hab] : ¬(a ∈ ({b} : Finset V3))),
      Finset.sum_singleton] at hvec hsum
    exact ⟨f a, f b, hpos a (by simp [hab]), hpos b (by simp [hab]), by linarith, hvec⟩

/-! ### KCZXLLE (HOL hl:681) -/

/-- HOL `KCZXLLE` (hl:681): with the base fan data on `u 0..u r`, the
azimuth `azim 0 (u i) (u j) (u k)` vanishes whenever `i` lies outside the
arc `[j,k]`. -/
private theorem w12_kczxlle (u : ℕ → V3) (r i j k : ℕ) (hjk : j < k) (hk : k ≤ r) (hr : 1 ≤ r)
    (hii : i ≤ r) (hijk : i < j ∨ k < i)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  classical
  have hj : j ≤ r := le_trans (le_of_lt hjk) hk
  have hij : i ≠ j := by
    rintro rfl
    rcases hijk with h | h
    · exact lt_irrefl _ h
    · omega
  have hik : i ≠ k := by
    rintro rfl
    rcases hijk with h | h
    · omega
    · exact lt_irrefl _ h
  have hk1 : 1 ≤ k := by omega
  have h01 : ¬ Collinear ℝ ({0, u 0, u 1} : Set V3) := h1 0 1 (by omega) (by omega) (by omega)
  have hu0ne : u 0 ≠ 0 := by
    intro h
    exact h01 (by rw [h]; simpa using collinear2_p14 (0 : V3) (u 1))
  have hu1ne : u 1 ≠ 0 := by
    intro h
    exact h01 (by rw [h]; simpa [Set.pair_comm] using collinear2_p14 (u 0) 0)
  have hu10 : u 1 ≠ u 0 := by
    intro h
    exact h01 (by rw [h]; simpa [Set.pair_comm] using collinear2_p14 (u 0) 0)
  -- every `u m` (m ≤ r) lies in the plane `affineSpan {0, u0, u1}`
  have hplan : ∀ m, m ≤ r → u m ∈ affineSpan ℝ ({0, u 0, u 1} : Set V3) := by
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0
      exact mem_affineSpan ℝ (by simp)
    · have hm1 : 1 ≤ m := by omega
      have hmem := AFF_GT_MONO (X := ({0, u 0} : Set V3)) (Y := ({u 1} : Set V3))
        (S := ({u 1} : Set V3)) (by simp) (h2 m hm1 hm)
      rw [show (({0, u 0} : Set V3) ∪ {u 1}) = ({0, u 0, u 1} : Set V3) by
            ext z
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
            tauto,
          show (({u 1} : Set V3) \ {u 1}) = (∅ : Set V3) by simp] at hmem
      exact w12_affGt_empty_subset_affineSpan hmem
  have hcop : Coplanar ({0, u i, u j, u k} : Set V3) := by
    refine ⟨0, u 0, u 1, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact hplan i hii
    · exact hplan j hj
    · exact hplan k hk
  rcases (AZIM_COND_FOR_COPLANAR 0 (u i) (u j) (u k)).mpr hcop with h0 | hpi
  · exact h0
  · exfalso
    have hnij : ¬ Collinear ℝ ({0, u i, u j} : Set V3) := h1 i j hii hj hij
    have hnik : ¬ Collinear ℝ ({0, u i, u k} : Set V3) := h1 i k hii hk hik
    have hinter := ((LDURDPN (u := u i) (v := u j) (w := u k) hnij hnik).mp hpi).2
    have hne : (affineSpan ℝ ({0, u i} : Set V3) ∩ conv0_p2 ({u j, u k} : Set V3)
        : Set V3).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact hinter
    obtain ⟨x, hx⟩ := hne
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxaff, hxconv⟩ := hx
    -- x = c • u i
    obtain ⟨c, hc⟩ : ∃ c : ℝ, x = c • u i := by
      have h := hxaff
      rwa [w12_aff2_vec0 (u i)] at h
    -- conv0 {u j, u k} ⊆ affGt {0, u0} {u1}
    have hconv_aff : ∀ y ∈ conv0_p2 ({u j, u k} : Set V3),
        y ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3) := by
      intro y hy
      obtain ⟨α, β, hα, hβ, hsum, hyab⟩ := w12_conv02_extract hy
      obtain ⟨cj, hj', hcj, huj⟩ : ∃ cj hj' : ℝ, 0 ≤ cj ∧ u j = cj • u 1 + hj' • u 0 := by
        by_cases hj0 : j = 0
        · subst hj0
          exact ⟨0, 1, le_refl 0, by rw [zero_smul, zero_add, one_smul]⟩
        · have hj1 : 1 ≤ j := by omega
          obtain ⟨cj, hcj, hj', hrep⟩ :=
            (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := u j)
              (Ne.symm hu0ne) hu1ne hu10).mp (h2 j hj1 hj)
          exact ⟨cj, hj', le_of_lt hcj, by simpa only [sub_zero] using hrep⟩
      obtain ⟨ck, hck, hk', huk⟩ :=
        (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := u k)
          (Ne.symm hu0ne) hu1ne hu10).mp (h2 k hk1 hk)
      simp only [sub_zero] at huk
      have hcomb : y = (α * cj + β * ck) • u 1 + (α * hj' + β * hk') • u 0 := by
        rw [hyab, huj, huk]
        module
      refine (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := y)
        (Ne.symm hu0ne) hu1ne hu10).mpr
        ⟨α * cj + β * ck, ?_, α * hj' + β * hk', by simpa only [sub_zero] using hcomb⟩
      have hβck : 0 < β * ck := mul_pos hβ hck
      nlinarith [mul_nonneg hα.le hcj]
    have hxaffGt : x ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3) := hconv_aff x hxconv
    obtain ⟨t3, ht3, t2, hxrep⟩ :=
      (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := x)
        (Ne.symm hu0ne) hu1ne hu10).mp hxaffGt
    simp only [sub_zero] at hxrep
    -- i ≠ 0 (otherwise `u 1` would be collinear with `u 0`)
    have hi0 : i ≠ 0 := by
      rintro rfl
      have hz : t3 • u 1 + (t2 - c) • u 0 = 0 := by
        have h := hxrep
        rw [hc] at h
        calc t3 • u 1 + (t2 - c) • u 0
            = (t3 • u 1 + t2 • u 0) - c • u 0 := by module
          _ = 0 := by rw [← h]; abel
      have hres := not_collinear_dep_p14 h01 (t2 - c) t3 (by simpa [add_comm] using hz)
      linarith [hres.2]
    have hi1 : 1 ≤ i := by omega
    obtain ⟨a, ha, b, huirep⟩ :=
      (affGt_pair_iff (v0 := 0) (v1 := u 0) (x := u 1) (y := u i)
        (Ne.symm hu0ne) hu1ne hu10).mp (h2 i hi1 hii)
    simp only [sub_zero] at huirep
    -- coefficient comparison: c * a = t3 > 0, hence c > 0
    have hcpos : 0 < c := by
      have hz : (c * a - t3) • u 1 + (c * b - t2) • u 0 = 0 := by
        have h := hxrep
        rw [hc, huirep, smul_add, smul_smul, smul_smul] at h
        calc (c * a - t3) • u 1 + (c * b - t2) • u 0
            = ((c * a) • u 1 + (c * b) • u 0) - (t3 • u 1 + t2 • u 0) := by module
          _ = 0 := by rw [← h]; abel
      have hres := not_collinear_dep_p14 h01 (c * b - t2) (c * a - t3)
        (by simpa [add_comm] using hz)
      have hca : 0 < c * a := by linarith [hres.2]
      by_contra hcnon
      have hcnon' : c ≤ 0 := le_of_not_gt hcnon
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hcnon' ha.le]
    -- x lies in the open wedge over (u j, u k)
    have hncj : ¬ Collinear3 0 (cross3 (u 0) (u 1)) (u j) := collinear_cross_p14 u j r hj hr h1 h2
    have hnck : ¬ Collinear3 0 (cross3 (u 0) (u 1)) (u k) := collinear_cross_p14 u k r hk hr h1 h2
    have hposjk : 0 < azim 0 (cross3 (u 0) (u 1)) (u j) (u k) :=
      YBTASCZ3_p14 u r j k hjk hk hr h1 h2 h3 h4
    have hltpijk : azim 0 (cross3 (u 0) (u 1)) (u j) (u k) < Real.pi :=
      YBTASCZ2_p14 u r j k hjk hk hr h1 h2 h3 h4
    have hxwedge : x ∈ Kepler.Geom.wedge 0 (cross3 (u 0) (u 1)) (u j) (u k) := by
      rw [Kepler.Geom.wedge_eq_affGt hncj hnck hposjk hltpijk]
      exact CONV0_SUBSET_AFF_GT (S := ({0, cross3 (u 0) (u 1)} : Set V3)) (by simp) hxconv
    rw [Kepler.Geom.wedge, Set.mem_setOf_eq] at hxwedge
    obtain ⟨-, hxpos, hxlt⟩ := hxwedge
    -- replace `x` by `c • u i` in the azimuth
    have hxaz : azim 0 (cross3 (u 0) (u 1)) (u j) x
        = azim 0 (cross3 (u 0) (u 1)) (u j) (u i) := by
      rw [hc]
      simpa using w12_azim_scale_all (v := cross3 (u 0) (u 1)) (w1 := u j) (w2 := u i)
        (a := 1) (b := 1) (c := c) one_pos one_pos hcpos
    rw [hxaz] at hxpos hxlt
    rcases hijk with hij' | hki
    · -- i < j: `azim uj ui ≥ π` while `azim uj uk < π`
      have hlt2 : azim 0 (cross3 (u 0) (u 1)) (u i) (u j) < Real.pi :=
        YBTASCZ2_p14 u r i j hij' hj hr h1 h2 h3 h4
      have hpos2 : 0 < azim 0 (cross3 (u 0) (u 1)) (u i) (u j) :=
        YBTASCZ3_p14 u r i j hij' hj hr h1 h2 h3 h4
      have hcompl := AZIM_COMPL_EXT 0 (cross3 (u 0) (u 1)) (u i) (u j)
      rw [if_neg (ne_of_gt hpos2)] at hcompl
      have hle : azim 0 (cross3 (u 0) (u 1)) (u j) (u k) ≤ Real.pi := le_of_lt hltpijk
      linarith
    · -- k < i: `azim uj ui = azim uj uk + azim uk ui ≥ azim uj uk`
      have hncu : ¬ Collinear3 0 (cross3 (u 0) (u 1)) (u j) := hncj
      have hnc1 : ¬ Collinear3 0 (cross3 (u 0) (u 1)) (u k) := hnck
      have hnc2 : ¬ Collinear3 0 (cross3 (u 0) (u 1)) (u i) :=
        collinear_cross_p14 u i r hii hr h1 h2
      have hxv : cross3 (u 0) (u 1) ≠ 0 := cross3_ne_p14 h01
      have hlt2 : azim 0 (cross3 (u 0) (u 1)) (u k) (u i) < Real.pi :=
        YBTASCZ2_p14 u r k i hki hii hr h1 h2 h3 h4
      have hsum3 := sum3_azim_fan (x := (0 : V3)) (v := cross3 (u 0) (u 1))
        (u := u j) (w1 := u k) (w2 := u i) hxv hncu hnc1 hnc2
        (by linarith)
      have hnn : 0 ≤ azim 0 (cross3 (u 0) (u 1)) (u k) (u i) := azim_nonneg _ _ _ _
      linarith


/-- HOL `KCZXLLE_SYM` (hl:931). -/
private theorem w12_kczxlle_sym (u : ℕ → V3) (r i j k : ℕ) (hk : k ≤ r) (hj : j ≤ r)
    (hr : 1 ≤ r) (hi : i ≤ r)
    (hord : (j < k ∧ (i < j ∨ k < i)) ∨ (k < j ∧ (i < k ∨ j < i)))
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  rcases hord with ⟨hjk, hijk⟩ | ⟨hkj, hijk⟩
  · exact w12_kczxlle u r i j k hjk hk hr hi hijk h1 h2 h3 h4
  · refine (AZIM_EQ_0_SYM2 0 (u i) (u j) (u k)).mpr ?_
    exact w12_kczxlle u r i k j hkj hj hr hi hijk h1 h2 h3 h4

/-- HOL `KCZXLLE` (hl:681). -/
theorem KCZXLLE_p14 (u : ℕ → V3) (r i j k : ℕ) (hjk : j < k) (hk : k ≤ r) (hr : 1 ≤ r)
    (hii : i ≤ r) (hijk : i < j ∨ k < i)
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  exact w12_kczxlle u r i j k hjk hk hr hii hijk h1 h2 h3 h4

/-- HOL `KCZXLLE_SYM` (hl:931). -/
theorem KCZXLLE_SYM_p14 (u : ℕ → V3) (r i j k : ℕ) (hk : k ≤ r) (hj : j ≤ r) (hr : 1 ≤ r)
    (hi : i ≤ r) (hord : (j < k ∧ (i < j ∨ k < i)) ∨ (k < j ∧ (i < k ∨ j < i)))
    (h1 : ∀ i j, i ≤ r → j ≤ r → i ≠ j → ¬ Collinear ℝ ({0, u i, u j} : Set V3))
    (h2 : ∀ i, 1 ≤ i → i ≤ r → u i ∈ affGt ({0, u 0} : Set V3) ({u 1} : Set V3))
    (h3 : cyclicSet (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)))
    (h4 : ∀ i, i < r →
      azimCycle_p14 (u '' Set.Icc 0 r) 0 (cross3 (u 0) (u 1)) (u i) = u (i + 1)) :
    azim 0 (u i) (u j) (u k) = 0 := by
  exact w12_kczxlle_sym u r i j k hk hj hr hi hord h1 h2 h3 h4

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

/-! ## w5cA3 kit B（波 2 连续性 kit，全 private 零 sorry）：圆→角度提升连续性、
azim 的 cos/sin 点式刻画、azim 沿曲线逐点连续性。-/

/-- w5cA3: triple product is additive in the first cross factor. -/
private theorem w5cA3_triple_addL (x y z w : V3) :
    (cross3 (x + y) z) ⬝ᵥ w = (cross3 x z) ⬝ᵥ w + (cross3 y z) ⬝ᵥ w := by
  simp only [dot3_eq_p14]
  rw [coe_cross3_p14, coe_add_p14, map_add, LinearMap.add_apply, add_dotProduct]
  rfl

/-- w5cA3: triple product is homogeneous in the first cross factor. -/
private theorem w5cA3_triple_smulL (t : ℝ) (x z w : V3) :
    (cross3 (t • x) z) ⬝ᵥ w = t * ((cross3 x z) ⬝ᵥ w) := by
  simp only [dot3_eq_p14]
  rw [coe_cross3_p14, coe_smul_p14, map_smul, LinearMap.smul_apply, smul_dotProduct,
    smul_eq_mul]
  rfl

/-- w5cA3: triple product is additive in the second cross factor. -/
private theorem w5cA3_triple_addR (x y z w : V3) :
    (cross3 x (y + z)) ⬝ᵥ w = (cross3 x y) ⬝ᵥ w + (cross3 x z) ⬝ᵥ w := by
  simp only [dot3_eq_p14]
  rw [coe_cross3_p14, coe_add_p14, map_add, add_dotProduct]
  rfl

/-- w5cA3: triple product is homogeneous in the second cross factor. -/
private theorem w5cA3_triple_smulR (t : ℝ) (x z w : V3) :
    (cross3 x (t • z)) ⬝ᵥ w = t * ((cross3 x z) ⬝ᵥ w) := by
  simp only [dot3_eq_p14]
  rw [coe_cross3_p14, coe_smul_p14, map_smul, smul_dotProduct, smul_eq_mul]
  rfl

/-- w5cA3: triple product vanishes when the dot slot repeats a cross factor. -/
private theorem w5cA3_triple_crossR (x y : V3) : (cross3 x y) ⬝ᵥ y = 0 := by
  rw [dot3_comm_p14, dot3_eq_p14, coe_cross3_p14, dot_cross_self]

/-- w5cA3: triple product vanishes when the dot slot repeats the other cross
factor. -/
private theorem w5cA3_triple_crossL (x y : V3) : (cross3 x y) ⬝ᵥ x = 0 := by
  rw [dot3_eq_p14, coe_cross3_p14, dotProduct_comm, dot_self_cross]

/-- w5cA3: triple product vanishes for a repeated cross factor. -/
private theorem w5cA3_triple_same (x z : V3) : (cross3 x x) ⬝ᵥ z = 0 := by
  rw [dot3_eq_p14, coe_cross3_p14, cross_self, zero_dotProduct]

/-- w5cA3: dot of a sum in the right slot (via comm to the left slot). -/
private theorem w5cA3_dot_sumR (x y z : V3) : x ⬝ᵥ (y + z) = y ⬝ᵥ x + z ⬝ᵥ x := by
  calc x ⬝ᵥ (y + z) = (y + z) ⬝ᵥ x := dot3_comm_p14 x (y + z)
    _ = y ⬝ᵥ x + z ⬝ᵥ x := dot3_add_left_p14 y z x

/-- w5cA3: the perpendicular component of `v3` against `v2` is nonzero. -/
private theorem w5cA3_perp_ne_zero (v2 v3 : V3) (hv2 : v2 ≠ 0)
    (h : ¬ Collinear3 0 v2 v3) :
    v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2 ≠ 0 := by
  intro hz
  apply h
  have hv : v3 = ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2 := eq_of_sub_eq_zero hz
  rw [hv]
  exact collinear0_smulL_p14 v2 _

/-- w5cA3: the perpendicular component against the axis has positive norm. -/
private theorem w5cA3_perp_norm_pos (v2 v3 : V3) (hv2 : v2 ≠ 0)
    (h : ¬ Collinear3 0 v2 v3) : 0 < ‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ :=
  norm_pos_iff.mpr (w5cA3_perp_ne_zero v2 v3 hv2 h)

/-- w5cA3: angle-lift continuity on `[0, 2π)`: if `θ t ∈ [0, 2π)` everywhere and
`cos ∘ θ`, `sin ∘ θ` are continuous at `t₀` with `θ t₀ ∈ (0, 2π)`, then `θ` is
continuous at `t₀`.  Route: the chord distance `‖e^{iφ} − e^{iθ₀}‖` has a
positive minimum `c` on the compact set of angles `≥ ε` away from `θ t₀`; small
`Δcos`/`Δsin` force that distance below `c`. -/
private theorem w5cA3_continuousAt_of_cos_sin {θ : ℝ → ℝ} {t₀ : ℝ}
    (hnn : ∀ t, 0 ≤ θ t) (hlt : ∀ t, θ t < 2 * Real.pi)
    (hC : ContinuousAt (fun t => Real.cos (θ t)) t₀)
    (hS : ContinuousAt (fun t => Real.sin (θ t)) t₀)
    (hpos : 0 < θ t₀) : ContinuousAt θ t₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hmin1 : 0 < min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2) :=
    lt_min (by linarith [hpos]) (by linarith [hlt t₀])
  have hmin2 : min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2) < θ t₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hpos])
  have hε'0 : 0 < min ε (min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2)) :=
    lt_min hε hmin1
  have hw1 : min ε (min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2)) < θ t₀ :=
    lt_of_le_of_lt (min_le_right ε _) hmin2
  have hw2 : min ε (min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2))
      < 2 * Real.pi - θ t₀ :=
    lt_of_le_of_lt (min_le_right ε _)
      (lt_of_le_of_lt (min_le_right _ _) (by linarith [hlt t₀]))
  set ε' := min ε (min (θ t₀ / 2) ((2 * Real.pi - θ t₀) / 2)) with hε'def
  have hε'le : ε' ≤ ε := min_le_left _ _
  -- K := 远离 θ₀ 的角度带的紧覆盖
  set K : Set ℝ := Set.Icc 0 (θ t₀ - ε') ∪ Set.Icc (θ t₀ + ε') (2 * Real.pi)
    with hKdef
  have hKc : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨0, Or.inl (Set.mem_Icc.mpr ⟨le_refl 0, show 0 ≤ θ t₀ - ε' from by linarith [hw1]⟩)⟩
  have hcc : Continuous (fun φ : ℝ =>
      ‖Complex.exp ((φ : ℂ) * Complex.I)
        - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖) := by fun_prop
  obtain ⟨xt, hxK, hxmin⟩ := hKc.exists_isMinOn hKne hcc.continuousOn
  have hmin : ∀ φ ∈ K,
      ‖Complex.exp ((xt : ℂ) * Complex.I)
          - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ ≤
        ‖Complex.exp ((φ : ℂ) * Complex.I)
          - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ :=
    isMinOn_iff.mp hxmin
  have hxtle : xt ≤ 2 * Real.pi := by
    rcases hxK with h | h
    · exact le_trans h.2 (by linarith)
    · exact h.2
  have hxtge : 0 ≤ xt := by
    rcases hxK with h | h
    · exact h.1
    · exact le_trans (by linarith) h.1
  -- c := f xt > 0
  have hcx : 0 < ‖Complex.exp ((xt : ℂ) * Complex.I)
      - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ := by
    by_contra hc0
    push_neg at hc0
    have hzero := norm_eq_zero.mp (le_antisymm hc0 (norm_nonneg _))
    have heq : Complex.exp ((xt : ℂ) * Complex.I)
        = Complex.exp ((θ t₀ : ℂ) * Complex.I) := eq_of_sub_eq_zero hzero
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    have hxr : xt = θ t₀ + (n : ℝ) * (2 * Real.pi) := by
      have h5 := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
        mul_zero, zero_add, mul_one, add_zero] at h5
      norm_num at h5
      linarith
    rcases Int.lt_trichotomy n 0 with hneg | hzero2 | hpos2
    · have hle : (n : ℝ) ≤ -1 := by
        have := (by omega : (n : ℤ) ≤ -1)
        exact_mod_cast this
      have hnp : (n : ℝ) * (2 * Real.pi) ≤ (-1 : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    · rw [show (n : ℝ) = 0 from by exact_mod_cast hzero2, zero_mul, add_zero] at hxr
      rcases hxK with h | h
      · linarith [h.2, hε'0]
      · linarith [h.1, hε'0]
    · have hge : (n : ℝ) ≥ 1 := by
        have := (by omega : (n : ℤ) ≥ 1)
        exact_mod_cast this
      have hnp : (1 : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hge (by positivity)
      linarith
  -- 由 hC hS 取窗口
  obtain ⟨δ₁, hδ₁, hCδ⟩ := Metric.continuousAt_iff.mp hC (‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3) (by linarith)
  obtain ⟨δ₂, hδ₂, hSδ⟩ := Metric.continuousAt_iff.mp hS (‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3) (by linarith)
  have h2η : ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3 + ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3 < ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ := by linarith
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
  have hxδ₁ : dist x t₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxδ₂ : dist x t₀ < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hΔ1 : |Real.cos (θ x) - Real.cos (θ t₀)| < ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3 := by
    have h1 := hCδ (show dist x t₀ < δ₁ from hxδ₁)
    rwa [Real.dist_eq] at h1
  have hΔ2 : |Real.sin (θ x) - Real.sin (θ t₀)| < ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ / 3 := by
    have h1 := hSδ (show dist x t₀ < δ₂ from hxδ₂)
    rwa [Real.dist_eq] at h1
  by_contra hcon
  rw [Real.dist_eq] at hcon
  -- θ x ∈ K
  have hKx : θ x ∈ K := by
    by_cases h : θ x ≤ θ t₀ - ε'
    · exact Or.inl (Set.mem_Icc.mpr ⟨hnn x, h⟩)
    · by_cases h2 : θ t₀ + ε' ≤ θ x
      · exact Or.inr (Set.mem_Icc.mpr ⟨h2, le_of_lt (hlt x)⟩)
      · exact absurd (show dist (θ x) (θ t₀) < ε from by
          rw [Real.dist_eq]
          exact lt_of_lt_of_le (abs_lt.mpr ⟨ by linarith [not_le.mp h],
            by linarith [not_le.mp h2]⟩) hε'le) hcon
  have hge := hmin (θ x) hKx
  have hfin : ‖Complex.exp ((θ x : ℂ) * Complex.I)
      - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ < ‖Complex.exp ((xt : ℂ) * Complex.I) - Complex.exp ((θ t₀ : ℂ) * Complex.I)‖ := by
    refine lt_of_le_of_lt (le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_) h2η
    have hre : (Complex.exp ((θ x : ℂ) * Complex.I)
        - Complex.exp ((θ t₀ : ℂ) * Complex.I)).re
        = Real.cos (θ x) - Real.cos (θ t₀) := by
      rw [Complex.sub_re, Complex.exp_re, Complex.exp_re]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have him : (Complex.exp ((θ x : ℂ) * Complex.I)
        - Complex.exp ((θ t₀ : ℂ) * Complex.I)).im
        = Real.sin (θ x) - Real.sin (θ t₀) := by
      rw [Complex.sub_im, Complex.exp_im, Complex.exp_im]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hre, him]
    exact add_le_add hΔ1.le hΔ2.le
  linarith


/-! ## w5cA3 kit (waves 3-5): azimuth cos/sin, pointwise continuity,
and the coplanar 0-or-π dichotomy consumed by `azim_0_as_closed_p14`. -/

/-- w5cA3 波3: 非退化 `azim 0 v2 v3 v4` 的 cos/sin 点式刻画（帧极表示展开）：
垂直分量 `p = v3 − proj`, `q = v4 − proj` 满足
`cos θ · ‖p‖‖q‖ = p ⬝ q` 与 `sin θ · ‖v2‖‖p‖‖q‖ = (v3 × v4) ⬝ v2`。 -/
private theorem w5cA3_azim_cos_sin (v2 v3 v4 : V3) (hv2 : v2 ≠ 0)
    (h1 : ¬ Collinear3 0 v2 v3) (h2 : ¬ Collinear3 0 v2 v4) :
    Real.cos (azim 0 v2 v3 v4) *
        (‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ *
          ‖v4 - ((v4 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖)
      = inner ℝ (v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2)
          (v4 - ((v4 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2)
      ∧ Real.sin (azim 0 v2 v3 v4) *
          (‖v2‖ * (‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ *
            ‖v4 - ((v4 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖))
        = (cross3 v3 v4) ⬝ᵥ v2 := by
  obtain ⟨E1, E2, E3, hon, halign⟩ := exists_on3_eq_smul v2 hv2
  have hax : (v2 - 0 : V3) = dist v2 0 • E3 := by
    rw [dist_eq_norm, sub_zero]; exact halign
  have hcopy := hon
  obtain ⟨o11, o22, o33, o12, o13, o23, -⟩ := hcopy
  have hv2E1 : v2 ⬝ᵥ E1 = 0 := by
    rw [halign, dot3_smul_left_p14, dot3_comm_p14, o13, mul_zero]
  have hv2E2 : v2 ⬝ᵥ E2 = 0 := by
    rw [halign, dot3_smul_left_p14, dot3_comm_p14, o23, mul_zero]
  have hEv21 : E1 ⬝ᵥ v2 = 0 := by rw [dot3_comm_p14, hv2E1]
  have hEv22 : E2 ⬝ᵥ v2 = 0 := by rw [dot3_comm_p14, hv2E2]
  have hv22ne : v2 ⬝ᵥ v2 ≠ 0 := ne_of_gt (dot3_self_pos_p14 hv2)
  obtain ⟨-, -, hframe⟩ := azim_master 0 v2 v3 v4
  obtain ⟨hA, hB, hframe⟩ := hframe
  obtain ⟨psi, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframe E1 E2 E3 hon hax hv2
  have hr1' : 0 < r1 := hr1 h1
  have hr2' : 0 < r2 := hr2 h2
  set theta := azim 0 v2 v3 v4 with hthetadef
  have hv3 : v3 = (r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2 + hA • v2 := by
    simpa only [sub_zero] using hrep1
  have hv4 : v4 = (r2 * Real.cos (psi + theta)) • E1
      + (r2 * Real.sin (psi + theta)) • E2 + hB • v2 := by
    simpa only [sub_zero] using hrep2
  have hv3d : v3 ⬝ᵥ v2 = hA * (v2 ⬝ᵥ v2) := by
    rw [hv3, dot3_add_left_p14, dot3_add_left_p14, dot3_smul_left_p14,
      dot3_smul_left_p14, dot3_smul_left_p14, hEv21, hEv22, mul_zero, mul_zero,
      zero_add, zero_add]
  have hv4d : v4 ⬝ᵥ v2 = hB * (v2 ⬝ᵥ v2) := by
    rw [hv4, dot3_add_left_p14, dot3_add_left_p14, dot3_smul_left_p14,
      dot3_smul_left_p14, dot3_smul_left_p14, hEv21, hEv22, mul_zero, mul_zero,
      zero_add, zero_add]
  have hdivA : (hA * (v2 ⬝ᵥ v2)) / (v2 ⬝ᵥ v2) = hA := by
    rw [mul_div_assoc, div_self hv22ne, mul_one]
  have hdivB : (hB * (v2 ⬝ᵥ v2)) / (v2 ⬝ᵥ v2) = hB := by
    rw [mul_div_assoc, div_self hv22ne, mul_one]
  have hp : v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2
      = (r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2 := by
    rw [hv3d, hdivA, hv3]
    module
  have hq : v4 - ((v4 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2
      = (r2 * Real.cos (psi + theta)) • E1 + (r2 * Real.sin (psi + theta)) • E2 := by
    rw [hv4d, hdivB, hv4]
    module
  have hE1u : ‖E1‖ = 1 := by
    have h2 : ‖E1‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [norm_sq_eq_dot, o11, one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hh | hh
    · exact hh
    · linarith [norm_nonneg E1]
  have hE2u : ‖E2‖ = 1 := by
    have h2 : ‖E2‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [norm_sq_eq_dot, o22, one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hh | hh
    · exact hh
    · linarith [norm_nonneg E2]
  have o21 : E2 ⬝ᵥ E1 = 0 := by rw [dot3_comm_p14, o12]
  have hpn : ‖(r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2‖ = r1 := by
    have hi : inner ℝ ((r1 * Real.cos psi) • E1) ((r1 * Real.sin psi) • E2) = 0 := by
      rw [inner_eq_dot, dot3_smul_left_p14, dot3_comm_p14, dot3_smul_left_p14, o21,
        mul_zero, mul_zero]
    have hsq2 : ‖(r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2‖ ^ 2
        = r1 ^ 2 := by
      rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real hi, norm_smul, norm_smul,
        hE1u, hE2u, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, ← sq, ← sq,
        sq_abs, sq_abs, mul_pow, mul_pow, ← mul_add,
        add_comm (Real.cos psi ^ 2) (Real.sin psi ^ 2),
        Real.sin_sq_add_cos_sq psi, mul_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with hh | hh
    · exact hh
    · linarith [hh, norm_nonneg ((r1 * Real.cos psi) • E1
        + (r1 * Real.sin psi) • E2)]
  have hqn : ‖(r2 * Real.cos (psi + theta)) • E1
      + (r2 * Real.sin (psi + theta)) • E2‖ = r2 := by
    have hi : inner ℝ ((r2 * Real.cos (psi + theta)) • E1)
        ((r2 * Real.sin (psi + theta)) • E2) = 0 := by
      rw [inner_eq_dot, dot3_smul_left_p14, dot3_comm_p14, dot3_smul_left_p14, o21,
        mul_zero, mul_zero]
    have hsq2 : ‖(r2 * Real.cos (psi + theta)) • E1
        + (r2 * Real.sin (psi + theta)) • E2‖ ^ 2 = r2 ^ 2 := by
      rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real hi, norm_smul, norm_smul,
        hE1u, hE2u, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, ← sq, ← sq,
        sq_abs, sq_abs, mul_pow, mul_pow, ← mul_add,
        add_comm (Real.cos (psi + theta) ^ 2) (Real.sin (psi + theta) ^ 2),
        Real.sin_sq_add_cos_sq (psi + theta), mul_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with hh | hh
    · exact hh
    · linarith [hh, norm_nonneg ((r2 * Real.cos (psi + theta)) • E1
        + (r2 * Real.sin (psi + theta)) • E2)]
  -- 余弦主式（norm_add_sq_real 路线 + B6-unify）
  have hcos : Real.cos theta * (r1 * r2)
      = inner ℝ ((r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2)
          ((r2 * Real.cos (psi + theta)) • E1
            + (r2 * Real.sin (psi + theta)) • E2) := by
    have hcs := Real.cos_sub (psi + theta) psi
    rw [show psi + theta - psi = theta from by ring] at hcs
    have hXYnorm : ((r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2)
        + ((r2 * Real.cos (psi + theta)) • E1
          + (r2 * Real.sin (psi + theta)) • E2)
        = ((r1 * Real.cos psi + r2 * Real.cos (psi + theta)) • E1
          + ((r1 * Real.sin psi + r2 * Real.sin (psi + theta)) • E2)) := by
      module
    have hicomb : inner ℝ ((r1 * Real.cos psi + r2 * Real.cos (psi + theta)) • E1)
        ((r1 * Real.sin psi + r2 * Real.sin (psi + theta)) • E2) = 0 := by
      rw [inner_eq_dot, dot3_smul_left_p14, dot3_comm_p14, dot3_smul_left_p14, o21,
        mul_zero, mul_zero]
    have hcomb : ‖((r1 * Real.cos psi + r2 * Real.cos (psi + theta)) • E1
        + ((r1 * Real.sin psi + r2 * Real.sin (psi + theta)) • E2))‖ ^ 2
        = (r1 * Real.cos psi + r2 * Real.cos (psi + theta)) ^ 2
          + (r1 * Real.sin psi + r2 * Real.sin (psi + theta)) ^ 2 := by
      rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real hicomb, norm_smul, norm_smul,
        hE1u, hE2u, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, ← sq, ← sq,
        sq_abs, sq_abs]
    have h1 := norm_add_sq_real ((r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2)
      ((r2 * Real.cos (psi + theta)) • E1 + (r2 * Real.sin (psi + theta)) • E2)
    rw [hXYnorm, hcomb, hpn, hqn] at h1
    have hA' : ((r1 * Real.cos psi + r2 * Real.cos (psi + theta)) ^ 2
          + (r1 * Real.sin psi + r2 * Real.sin (psi + theta)) ^ 2)
        = r1 ^ 2 + r2 ^ 2 + 2 * ((Real.cos (psi + theta) * Real.cos psi
            + Real.sin (psi + theta) * Real.sin psi) * (r1 * r2)) := by
      nlinarith [Real.sin_sq_add_cos_sq psi, Real.sin_sq_add_cos_sq (psi + theta)]
    have hAB : inner ℝ ((r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2)
        ((r2 * Real.cos (psi + theta)) • E1 + (r2 * Real.sin (psi + theta)) • E2)
        = (r1 * r2) * (Real.cos (psi + theta) * Real.cos psi
          + Real.sin (psi + theta) * Real.sin psi) := by
      rw [inner_eq_dot]
      simp only [v3coe, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
        smul_eq_mul, o11, o12, o21, o22, mul_one, mul_zero, zero_mul, zero_add]
      ring
    rw [hA'] at h1
    rw [hAB] at h1
    rw [hcs]
    linarith [h1]
  -- 正弦主式：先算标架基元的 triple product
  have hcoev2 : ((v2 : V3) : Fin 3 → ℝ) = ‖v2‖ • ((E3 : V3) : Fin 3 → ℝ) := by
    have hE3u : ‖E3‖ = 1 := by
      have h2 : ‖E3‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [norm_sq_eq_dot, o33, one_pow]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hh | hh
      · exact hh
      · linarith [norm_nonneg E3]
    rw [congrArg (fun w : V3 => ((w : V3) : Fin 3 → ℝ)) halign, coe_smul_p14]
  have hE12 : (cross3 E1 E2) ⬝ᵥ v2 = ‖v2‖ := by
    rw [dot3_eq_p14, coe_cross3_p14, on3_cross hon, hcoev2]
    simp only [dotProduct_smul, smul_eq_mul, ← dot3_eq_p14, o33, mul_one]
  have hE21 : (cross3 E2 E1) ⬝ᵥ v2 = -‖v2‖ := by
    rw [dot3_eq_p14, coe_cross3_p14, ← cross_anticomm, neg_dotProduct, on3_cross hon,
      hcoev2]
    simp only [dotProduct_smul, smul_eq_mul, ← dot3_eq_p14, o33, mul_one]
  have hsin : (cross3 v3 v4) ⬝ᵥ v2
      = ‖v2‖ * (r1 * r2 * (Real.cos psi * Real.sin (psi + theta)
          - Real.sin psi * Real.cos (psi + theta))) := by
    rw [hv3, hv4]
    simp only [w5cA3_triple_addL, w5cA3_triple_smulL, w5cA3_triple_addR,
      w5cA3_triple_smulR, w5cA3_triple_crossL, w5cA3_triple_crossR,
      w5cA3_triple_same, mul_zero, zero_mul, add_zero, zero_add]
    rw [hE12, hE21]
    ring
  have hss := Real.sin_sub (psi + theta) psi
  rw [show psi + theta - psi = theta from by ring] at hss
  refine ⟨?_, ?_⟩
  · rw [hp, hq, hpn, hqn, hcos]
    canonicalize
  · canonicalGoal
    rw [hp, hq, hpn, hqn, hsin, hss]
    canonicalize
    ring

/-- w5cA3: azim 沿连续曲线的逐点连续性（轴点非退化 + 该点 azim ≠ 0）。 -/
private theorem w5cA3_continuousAt_azim {v2 v3 v4 : ℝ → V3} {t₀ : ℝ}
    (hv2c : ContinuousAt v2 t₀) (hv3c : ContinuousAt v3 t₀)
    (hv4c : ContinuousAt v4 t₀)
    (h5 : ¬ Collinear ℝ ({0, v2 t₀, v3 t₀} : Set V3))
    (h6 : ¬ Collinear ℝ ({0, v2 t₀, v4 t₀} : Set V3))
    (h7 : azim 0 (v2 t₀) (v3 t₀) (v4 t₀) ≠ 0) :
    ContinuousAt (fun t => azim 0 (v2 t) (v3 t) (v4 t)) t₀ := by
  have hv20 : v2 t₀ ≠ 0 := by
    intro hz
    apply h5
    rw [hz]
    simpa using collinear2_p14 0 (v3 t₀)
  set p : ℝ → V3 := fun t => v3 t - ((v3 t ⬝ᵥ v2 t) / (v2 t ⬝ᵥ v2 t)) • v2 t
    with hpdef
  set q : ℝ → V3 := fun t => v4 t - ((v4 t ⬝ᵥ v2 t) / (v2 t ⬝ᵥ v2 t)) • v2 t
    with hqdef
  have hdotc2 : ContinuousAt (fun t => v2 t ⬝ᵥ v2 t) t₀ :=
    w5cA2_continuousAt_dot hv2c hv2c
  have hd2ne : v2 t₀ ⬝ᵥ v2 t₀ ≠ 0 := ne_of_gt (dot3_self_pos_p14 hv20)
  have hpc : ContinuousAt p t₀ := by
    have hd1 : ContinuousAt (fun t => v3 t ⬝ᵥ v2 t) t₀ :=
      w5cA2_continuousAt_dot hv3c hv2c
    exact hv3c.sub ((hd1.div hdotc2 hd2ne).smul hv2c)
  have hqc : ContinuousAt q t₀ := by
    have hd1 : ContinuousAt (fun t => v4 t ⬝ᵥ v2 t) t₀ :=
      w5cA2_continuousAt_dot hv4c hv2c
    exact hv4c.sub ((hd1.div hdotc2 hd2ne).smul hv2c)
  have hpne : p t₀ ≠ 0 := by
    intro hz
    exact absurd hz (w5cA3_perp_ne_zero (v2 t₀) (v3 t₀) hv20 h5)
  have hqne : q t₀ ≠ 0 := by
    intro hz
    exact absurd hz (w5cA3_perp_ne_zero (v2 t₀) (v4 t₀) hv20 h6)
  have hG1 : ContinuousAt (fun t => p t ⬝ᵥ q t) t₀ :=
    w5cA2_continuousAt_dot hpc hqc
  have hG2 : ContinuousAt (fun t => ‖p t‖) t₀ := hpc.norm
  have hG3 : ContinuousAt (fun t => ‖q t‖) t₀ := hqc.norm
  have hG4 : ContinuousAt (fun t => (cross3 (v3 t) (v4 t)) ⬝ᵥ v2 t) t₀ :=
    w5cA2_continuousAt_dot (w5cA2_continuousAt_cross3 hv3c hv4c) hv2c
  have hG5 : ContinuousAt (fun t => ‖v2 t‖) t₀ := hv2c.norm
  have hdene : ‖p t₀‖ * ‖q t₀‖ ≠ 0 :=
    mul_ne_zero (fun hz => hpne (norm_eq_zero.mp hz))
      (fun hz => hqne (norm_eq_zero.mp hz))
  have hdene2 : ‖v2 t₀‖ * (‖p t₀‖ * ‖q t₀‖) ≠ 0 :=
    mul_ne_zero (fun hz => hv20 (norm_eq_zero.mp hz)) hdene
  have hident : ∀ t, v2 t ≠ 0 → ¬ Collinear3 0 (v2 t) (v3 t) →
      ¬ Collinear3 0 (v2 t) (v4 t) →
      Real.cos (azim 0 (v2 t) (v3 t) (v4 t))
          = (p t ⬝ᵥ q t) / (‖p t‖ * ‖q t‖)
        ∧ Real.sin (azim 0 (v2 t) (v3 t) (v4 t))
          = (cross3 (v3 t) (v4 t) ⬝ᵥ v2 t)
            / (‖v2 t‖ * (‖p t‖ * ‖q t‖)) := by
    intro t hv2t hn1 hn2
    obtain ⟨hc, hs⟩ := w5cA3_azim_cos_sin (v2 t) (v3 t) (v4 t) hv2t hn1 hn2
    have hden : ‖p t‖ * ‖q t‖ ≠ 0 :=
      mul_ne_zero (fun hz => (w5cA3_perp_ne_zero (v2 t) (v3 t) hv2t hn1)
          (norm_eq_zero.mp hz))
        (fun hz => (w5cA3_perp_ne_zero (v2 t) (v4 t) hv2t hn2)
          (norm_eq_zero.mp hz))
    refine ⟨?_, ?_⟩
    · refine mul_right_cancel₀ hden ?_
      rw [div_mul_cancel₀ _ hden]
      rw [← inner_eq_dot]
      exact hc
    · refine mul_right_cancel₀ (mul_ne_zero (fun hz => hv2t (norm_eq_zero.mp hz)) hden) ?_
      rw [div_mul_cancel₀ _ (mul_ne_zero (fun hz => hv2t (norm_eq_zero.mp hz)) hden)]
      exact hs
  have hnc1 : ContinuousAt (fun t => ‖cross3 (v2 t) (v3 t)‖) t₀ :=
    (w5cA2_continuousAt_cross3 hv2c hv3c).norm
  have hnc2 : ContinuousAt (fun t => ‖cross3 (v2 t) (v4 t)‖) t₀ :=
    (w5cA2_continuousAt_cross3 hv2c hv4c).norm
  have hne1 : ‖cross3 (v2 t₀) (v3 t₀)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (cross3_ne_p14 h5))
  have hne2 : ‖cross3 (v2 t₀) (v4 t₀)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (cross3_ne_p14 h6))
  have hne3 : ‖v2 t₀‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv20)
  obtain ⟨eA, heA, hbA⟩ := w5cA2_eventually_ne hnc1 hne1
  obtain ⟨eB, heB, hbB⟩ := w5cA2_eventually_ne hnc2 hne2
  obtain ⟨eC, heC, hbC⟩ := w5cA2_eventually_ne hG5 hne3
  have htri : ∀ t, dist t t₀ < min eA (min eB eC) →
      v2 t ≠ 0 ∧ ¬ Collinear3 0 (v2 t) (v3 t) ∧ ¬ Collinear3 0 (v2 t) (v4 t) := by
    intro t ht
    have s1 : |t₀ - t| < eA := by
      rw [← Real.dist_eq, dist_comm]
      exact lt_of_lt_of_le ht (min_le_left _ _)
    have s2 : |t₀ - t| < eB := by
      rw [← Real.dist_eq, dist_comm]
      exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
    have s3 : |t₀ - t| < eC := by
      rw [← Real.dist_eq, dist_comm]
      exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨fun hz => hbC t s3 (by rw [hz, norm_zero]), fun hcol =>
      hbA t s1 (by rw [w5cA2_collinear0_iff_cross.mp hcol, norm_zero]),
      fun hcol => hbB t s2 (by rw [w5cA2_collinear0_iff_cross.mp hcol, norm_zero])⟩
  have hcos2 : ContinuousAt (fun t => Real.cos (azim 0 (v2 t) (v3 t) (v4 t))) t₀ := by
    refine (hG1.div (hG2.mul hG3) hdene).congr (Filter.eventually_of_mem
      (Metric.ball_mem_nhds t₀ (lt_min heA (lt_min heB heC))) (fun t ht => ?_))
    obtain ⟨hv2t, hn1, hn2⟩ := htri t ht
    exact (hident t hv2t hn1 hn2).1.symm
  have hsin2 : ContinuousAt (fun t => Real.sin (azim 0 (v2 t) (v3 t) (v4 t))) t₀ := by
    refine (hG4.div (hG5.mul (hG2.mul hG3)) hdene2).congr (Filter.eventually_of_mem
      (Metric.ball_mem_nhds t₀ (lt_min heA (lt_min heB heC))) (fun t ht => ?_))
    obtain ⟨hv2t, hn1, hn2⟩ := htri t ht
    exact (hident t hv2t hn1 hn2).2.symm
  exact w5cA3_continuousAt_of_cos_sin
    (fun t => azim_nonneg 0 (v2 t) (v3 t) (v4 t))
    (fun t => azim_lt_two_pi 0 (v2 t) (v3 t) (v4 t)) hcos2 hsin2
    (lt_of_le_of_ne (azim_nonneg 0 (v2 t₀) (v3 t₀) (v4 t₀)) (Ne.symm h7))

/-- w5cA3: 共面四点组（含原点）的 azim 只能是 0 或 π。 -/
private theorem w5cA3_azim_0_or_pi (v2 v3 v4 : V3) (hv2 : v2 ≠ 0)
    (h1 : ¬ Collinear3 0 v2 v3) (h2 : ¬ Collinear3 0 v2 v4)
    (hcop : Coplanar ({0, v2, v3, v4} : Set V3)) :
    azim 0 v2 v3 v4 = 0 ∨ azim 0 v2 v3 v4 = Real.pi := by
  by_cases hc1 : Collinear3 0 v2 v3
  · exact Or.inl (by unfold azim; rw [if_pos (Or.inl hc1)])
  by_cases hc2 : Collinear3 0 v2 v4
  · exact Or.inl (by unfold azim; rw [if_pos (Or.inr hc2)])
  obtain ⟨h1s, h2s⟩ : ¬ Collinear ℝ ({0, v2, v3} : Set V3) ∧
      ¬ Collinear ℝ ({0, v2, v4} : Set V3) := ⟨h1, h2⟩
  have hv20 : v2 ≠ 0 := fun hz => h1s (by rw [hz]; simpa using collinear2_p14 0 v3)
  have hpne := w5cA3_perp_ne_zero v2 v3 hv20 h1
  have hqne := w5cA3_perp_ne_zero v2 v4 hv20 h2
  have hv2E1 : v2 ⬝ᵥ cross3 v3 v4 = 0 := by
    simpa only [v3coe] using (w5cA2_coplanar_triple).mp hcop
  rw [dot3_comm_p14] at hv2E1
  obtain ⟨hc, hs⟩ := w5cA3_azim_cos_sin v2 v3 v4 hv20 h1 h2
  rw [hv2E1] at hs
  have hs0 : Real.sin (azim 0 v2 v3 v4) = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · exact h
    · have hnz := mul_ne_zero (mul_ne_zero (fun hz => hv20 (norm_eq_zero.mp hz))
          (fun hz => hpne (norm_eq_zero.mp hz)))
        (fun hz => hqne (norm_eq_zero.mp hz))
      rw [mul_assoc] at hnz
      exact absurd h hnz
  have hθlt : azim 0 v2 v3 v4 < 2 * Real.pi := azim_lt_two_pi 0 v2 v3 v4
  have hθnn : 0 ≤ azim 0 v2 v3 v4 := azim_nonneg 0 v2 v3 v4
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs0
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · have hle : (n : ℝ) ≤ -1 := by
      exact_mod_cast (show (n : ℤ) ≤ -1 from by omega)
    have hnp : (n : ℝ) * Real.pi ≤ (-1 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    rw [hn] at hnp
    linarith [Real.pi_pos]
  · exact Or.inl (by rw [show (n : ℝ) = 0 from by exact_mod_cast hzero, zero_mul] at hn; linarith)
  · have hge : (n : ℝ) ≥ 1 := by
      exact_mod_cast (show (n : ℤ) ≥ 1 from by omega)
    have hle : (n : ℝ) ≤ 1 := by
      have h1x : (n : ℝ) * Real.pi < 2 * Real.pi := by rwa [hn]
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have hn2 : (n : ℝ) < 2 := lt_of_mul_lt_mul_right h1x (le_of_lt hpi)
      exact_mod_cast (show (n : ℤ) ≤ 1 from by
        have hn2' : n < 2 := by exact_mod_cast hn2
        omega)
    have hn1 : (n : ℝ) = 1 := by linarith
    refine Or.inr (by rw [show azim 0 v2 v3 v4 = Real.pi from by
      rw [hn1] at hn; linarith])
/-- HOL `azim_0_as_closed` (hl:972).  NEEDS: azim-zero coplanarity theory. -/
theorem azim_0_as_closed_p14 (v2 v3 v4 : V3)
    (h1 : ¬ Collinear ℝ ({0, v2, v3} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, v2, v4} : Set V3)) :
    azim 0 v2 v3 v4 = 0 ↔
      Coplanar ({0, v2, v3, v4} : Set V3) ∧
        0 ≤ (cross3 (cross3 v2 v3) v2) ⬝ᵥ v4 := by
  have hv2n : v2 ≠ 0 := by
    intro hz; apply h1; rw [hz]; simpa using collinear2_p14 0 v3
  have hv3n : v3 ≠ 0 := by
    intro hz; apply h1; rw [hz]; simpa using collinear2_p14 v2 0
  have hv4n : v4 ≠ 0 := by
    intro hz; apply h2; rw [hz]; simpa using collinear2_p14 v2 0
  constructor
  · intro h0
    have hmem := (azim_eq_zero_iff (v0 := 0) (v1 := v2) (w := v3) (x := v4) h1 h2).mp h0
    obtain ⟨c, hc, k, hvk⟩ := (affGt_pair_iff (v0 := 0) (v1 := v2) (x := v4) (y := v3)
      (Ne.symm hv2n) hv4n (fun heq => h2 (by rw [heq]; simpa using collinear2_p14 0 v2))) |>.mp hmem
    have hv3s : v3 = c • v4 + k • v2 := by simpa only [sub_zero] using hvk
    refine ⟨?_, ?_⟩
    · rw [w5cA2_coplanar_triple]
      simp only [sub_zero]
      rw [hv3s, dot3_comm_p14, w5cA3_triple_addL, w5cA3_triple_smulL,
        w5cA3_triple_smulL, w5cA3_triple_same, w5cA3_triple_crossL]
      simp
    · have hBAC : (cross3 (cross3 v2 v3) v2) ⬝ᵥ v4
          = (v2 ⬝ᵥ v2) * (v3 ⬝ᵥ v4) - (v3 ⬝ᵥ v2) * (v2 ⬝ᵥ v4) := by
        rw [dot3_eq_p14, coe_cross3_p14 (cross3 v2 v3) v2, coe_cross3_p14 v2 v3,
          cross_cross_eq_smul_sub_smul]
        simp only [v3coe, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      have hv3d4 : v3 ⬝ᵥ v4 = c * (v4 ⬝ᵥ v4) + k * (v2 ⬝ᵥ v4) := by
        rw [hv3s]
        simp only [v3coe, add_dotProduct, smul_dotProduct, smul_eq_mul]
      have hv2d3 : v2 ⬝ᵥ v3 = c * (v2 ⬝ᵥ v4) + k * (v2 ⬝ᵥ v2) := by
        rw [hv3s]
        simp only [v3coe, dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [dot3_comm_p14 v2 v3] at hv2d3
      have hCS : (v2 ⬝ᵥ v4) ^ 2 ≤ (v2 ⬝ᵥ v2) * (v4 ⬝ᵥ v4) := by
        have h := abs_real_inner_le_norm (x := v2) (y := v4)
        rw [inner_eq_dot] at h
        have h2 : (v2 ⬝ᵥ v4) ^ 2 ≤ (‖v2‖ * ‖v4‖) ^ 2 := by
          rcases abs_le.mp h with ⟨hneg, hpos⟩
          exact sq_le_sq' (by linarith) hpos
        rwa [mul_pow, norm_sq_eq_dot, norm_sq_eq_dot] at h2
      have hge0 : 0 ≤ (v2 ⬝ᵥ v2) * (v4 ⬝ᵥ v4) - (v2 ⬝ᵥ v4) ^ 2 := by
        linarith [hCS]
      rw [hBAC, hv3d4, hv2d3]
      have hbig : (v2 ⬝ᵥ v2) * (c * (v4 ⬝ᵥ v4) + k * (v2 ⬝ᵥ v4))
          - (c * (v2 ⬝ᵥ v4) + k * (v2 ⬝ᵥ v2)) * (v2 ⬝ᵥ v4)
          = c * ((v2 ⬝ᵥ v2) * (v4 ⬝ᵥ v4) - (v2 ⬝ᵥ v4) ^ 2) := by ring
      rw [hbig]
      exact mul_nonneg hc.le hge0
  · rintro ⟨hcop, hT⟩
    by_contra h0
    have hv2E1 : v2 ⬝ᵥ cross3 v3 v4 = 0 := by
      simpa only [v3coe] using (w5cA2_coplanar_triple).mp hcop
    have hv2n : v2 ≠ 0 := by
      intro hz; apply h1; rw [hz]; simpa using collinear2_p14 0 v3
    have hθlt : azim 0 v2 v3 v4 < 2 * Real.pi := azim_lt_two_pi 0 v2 v3 v4
    have hθnn : 0 ≤ azim 0 v2 v3 v4 := azim_nonneg 0 v2 v3 v4
    obtain ⟨hc, hs⟩ := w5cA3_azim_cos_sin v2 v3 v4 hv2n h1 h2
    have hpne := w5cA3_perp_ne_zero v2 v3 hv2n h1
    have hqne := w5cA3_perp_ne_zero v2 v4 hv2n h2
    have hv2E1 : v2 ⬝ᵥ cross3 v3 v4 = 0 := by
      simpa only [v3coe] using (w5cA2_coplanar_triple).mp hcop
    rw [dot3_comm_p14] at hv2E1
    rw [hv2E1] at hs
    have hs0 : Real.sin (azim 0 v2 v3 v4) = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact h
      · have hnz := mul_ne_zero (mul_ne_zero (fun hz => hv2n (norm_eq_zero.mp hz))
            (fun hz => hpne (norm_eq_zero.mp hz)))
          (fun hz => hqne (norm_eq_zero.mp hz))
        rw [mul_assoc] at hnz
        exact absurd h hnz
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs0
    obtain hn0 : (n : ℝ) = 0 ∨ (n : ℝ) = 1 := by
      rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
      · exfalso
        have hle : (n : ℝ) ≤ -1 := by
          exact_mod_cast (show (n : ℤ) ≤ -1 from by omega)
        have hnp : (n : ℝ) * Real.pi ≤ (-1 : ℝ) * Real.pi :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        rw [hn] at hnp
        linarith [Real.pi_pos]
      · exact Or.inl (by exact_mod_cast hzero)
      · -- n ≥ 1, and n ≤ 1 since θ = n·π < 2π
        have hge : (n : ℝ) ≥ 1 := by
          exact_mod_cast (show (n : ℤ) ≥ 1 from by omega)
        have hle : (n : ℝ) ≤ 1 := by
          have h1x : (n : ℝ) * Real.pi < 2 * Real.pi := by rwa [hn]
          have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
          have hn2 : (n : ℝ) < 2 := lt_of_mul_lt_mul_right h1x (le_of_lt hpi)
          exact_mod_cast (show (n : ℤ) ≤ 1 from by
            have hn2' : n < 2 := by exact_mod_cast hn2
            omega)
        exact Or.inr (by linarith)
    rcases hn0 with h0n | h1n
    · rw [h0n, zero_mul] at hn
      exact h0 hn.symm
    · rw [h1n, one_mul] at hn
      -- θ = π: 帧表示给出 v4 = −λ•v3 + μ•v2, 从而 T < 0 与 hT ≥ 0 矛盾
      have hπ : azim 0 v2 v3 v4 = Real.pi := hn.symm
      obtain ⟨E1, E2, E3, hon, halign⟩ := exists_on3_eq_smul v2 hv2n
      have hax : (v2 - 0 : V3) = dist v2 0 • E3 := by
        rw [dist_eq_norm, sub_zero]; exact halign
      have hcopy := hon
      obtain ⟨o11, o22, o33, o12, o13, o23, -⟩ := hcopy
      have hv22 : v2 ⬝ᵥ v2 = ‖v2‖ ^ 2 := (norm_sq_eq_dot v2).symm
      have hv33 : v3 ⬝ᵥ v3 = ‖v3‖ ^ 2 := (norm_sq_eq_dot v3).symm
      obtain ⟨-, -, hframe⟩ := azim_master 0 v2 v3 v4
      obtain ⟨hA, hB, hframe⟩ := hframe
      obtain ⟨psi, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframe E1 E2 E3 hon hax hv2n
      have hr1' : 0 < r1 := hr1 h1
      have hr2' : 0 < r2 := hr2 h2
      have hv3 : v3 = (r1 * Real.cos psi) • E1 + (r1 * Real.sin psi) • E2 + hA • v2 := by
        simpa only [sub_zero] using hrep1
      have hv4 : v4 = (r2 * Real.cos (psi + Real.pi)) • E1
          + (r2 * Real.sin (psi + Real.pi)) • E2 + hB • v2 := by
        have hrep2' := hrep2
        rw [hπ] at hrep2'
        simpa only [sub_zero] using hrep2'
      have hcospi : Real.cos (psi + Real.pi) = -Real.cos psi := by
        rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
      have hsinpi : Real.sin (psi + Real.pi) = -Real.sin psi := by
        rw [Real.sin_add, Real.cos_pi, Real.sin_pi]; ring
      rw [hcospi, hsinpi] at hv4
      have hlr : r2 = r1 * (r2 / r1) := by field_simp
      rw [hlr] at hv4
      have hv4s : v4 = -(r2 / r1) • v3 + ((r2 / r1) * hA + hB) • v2 := by
        rw [hv4, hv3]; module
      have hBAC : (cross3 (cross3 v2 v3) v2) ⬝ᵥ v4
          = (v2 ⬝ᵥ v2) * (v3 ⬝ᵥ v4) - (v3 ⬝ᵥ v2) * (v2 ⬝ᵥ v4) := by
        rw [dot3_eq_p14, coe_cross3_p14 (cross3 v2 v3) v2, coe_cross3_p14 v2 v3,
          cross_cross_eq_smul_sub_smul]
        simp only [v3coe, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      have hv3d4 : v3 ⬝ᵥ v4 = -(r2 / r1) * (v3 ⬝ᵥ v3)
          + ((r2 / r1) * hA + hB) * (v3 ⬝ᵥ v2) := by
        rw [hv4s]
        simp only [v3coe, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hv2d4 : v2 ⬝ᵥ v4 = -(r2 / r1) * (v2 ⬝ᵥ v3)
          + ((r2 / r1) * hA + hB) * (v2 ⬝ᵥ v2) := by
        rw [hv4s]
        simp only [v3coe, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hTneg : (v2 ⬝ᵥ v2) * (v3 ⬝ᵥ v4) - (v3 ⬝ᵥ v2) * (v2 ⬝ᵥ v4)
          = -(r2 / r1) * ((v2 ⬝ᵥ v2) * (v3 ⬝ᵥ v3) - (v2 ⬝ᵥ v3) ^ 2) := by
        rw [hv3d4, hv2d4, dot3_comm_p14 v3 v2]; ring
      have hv3perp := w5cA3_perp_ne_zero v2 v3 hv2n h1
      have hp0 : (v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2) ⬝ᵥ v2 = 0 := by
        have hv22ne' : v2 ⬝ᵥ v2 ≠ 0 := ne_of_gt (dot3_self_pos_p14 hv2n)
        simp only [v3coe, sub_dotProduct, smul_dotProduct, smul_eq_mul, div_eq_mul_inv]
        rw [mul_assoc, inv_mul_cancel₀ hv22ne', mul_one, sub_self]
      have hid : (v2 ⬝ᵥ v2) * (v3 ⬝ᵥ v3) - (v2 ⬝ᵥ v3) ^ 2
          = (v2 ⬝ᵥ v2) * ‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ ^ 2 := by
        have hp2 : ‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ ^ 2
            = (v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2)
              ⬝ᵥ (v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2) := norm_sq_eq_dot _
        rw [hp2]
        simp only [v3coe, sub_dotProduct, dotProduct_sub, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]
        have hv22ne' : v2 ⬝ᵥ v2 ≠ 0 := ne_of_gt (dot3_self_pos_p14 hv2n)
        field_simp [hv22ne']
        rw [dotProduct_comm (v3.ofLp) (v2.ofLp)]
        ring
      rw [hBAC] at hT
      rw [hTneg, hid] at hT
      have hlam : 0 < r2 / r1 := div_pos hr2' hr1'
      have hP : 0 < (v2 ⬝ᵥ v2) * ‖v3 - ((v3 ⬝ᵥ v2) / (v2 ⬝ᵥ v2)) • v2‖ ^ 2 := by
        rw [norm_sq_eq_dot]
        exact mul_pos (dot3_self_pos_p14 hv2n) (dot3_self_pos_p14 hv3perp)
      linarith [hlam, hP, hT, mul_pos hlam hP]

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
  have hv2n : v2 ≠ 0 := by
    intro hz; apply h5; rw [hz]; simpa using collinear2_p14 0 (v3 t)
  have hApos : 0 < azim 0 (v2 t) (v3 t) (v4 t) :=
    lt_of_le_of_ne (azim_nonneg 0 (v2 t) (v3 t) (v4 t)) (Ne.symm h7)
  have hcont := w5cA3_continuousAt_azim (h1 t h4) (h2 t h4) (h3 t h4) h5 h6 h7
  obtain ⟨e, he, hball⟩ := Metric.continuousAt_iff.mp hcont
    (azim 0 (v2 t) (v3 t) (v4 t) / 2) (by linarith [hApos])
  refine ⟨e, he, fun t' ht' => ?_⟩
  have hd : dist (azim 0 (v2 t') (v3 t') (v4 t')) (azim 0 (v2 t) (v3 t) (v4 t))
      < azim 0 (v2 t) (v3 t) (v4 t) / 2 :=
    hball (by rw [Real.dist_eq]; exact ht')
  rw [Real.dist_eq] at hd
  obtain ⟨h2a, h2b⟩ := abs_lt.mp hd
  intro hzero
  have hnpos : 0 ≤ azim 0 (v2 t) (v3 t) (v4 t) := azim_nonneg 0 (v2 t) (v3 t) (v4 t)
  linarith

/-- HOL `azim_real_continuous_on` (hl:1141).  SF-95 (2026-11-03): the four
`real_interval (a,b)` hypotheses are OPEN intervals in HOL; the first
rendering used `Set.Icc a b` and was FALSE at `t = a` / `t = b` (the window
`Icc (t-e) (t+e)` leaves `[a, b]`, where h1-h3 say nothing — W5c-A2
countermodel: curves constant-nice on `[a, b]`, redefined at one point
`q0 < a`).  Re-frozen verbatim to HOL with `Set.Ioo a b`; the closed window
in the conclusion is kept (stronger than HOL's open one, true for small
`e`).  The azim-continuity kit (cos/sin representation + arccos assembly)
is designed in the W5c-A2 handoff note. -/
theorem azim_real_continuous_on_p14 (v2 v3 v4 : ℝ → V3) (t a b : ℝ)
    (h1 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v2 x)
    (h2 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v3 x)
    (h3 : ∀ x, x ∈ Set.Ioo a b → ContinuousAt v4 x)
    (h4 : t ∈ Set.Ioo a b)
    (h5 : ¬ Collinear ℝ ({0, v2 t, v3 t} : Set V3))
    (h6 : ¬ Collinear ℝ ({0, v2 t, v4 t} : Set V3))
    (h7 : ¬ (azim 0 (v2 t) (v3 t) (v4 t) = 0)) :
    ∃ e : ℝ, 0 < e ∧
      ContinuousOn (fun q => azim 0 (v2 q) (v3 q) (v4 q)) (Set.Icc (t - e) (t + e)) := by
  have hv2t0 : v2 t ≠ 0 := by
    intro hz
    apply h5
    rw [hz]
    simpa using collinear2_p14 0 (v3 t)
  have hcont : ContinuousAt (fun q => azim 0 (v2 q) (v3 q) (v4 q)) t :=
    w5cA3_continuousAt_azim (h1 t h4) (h2 t h4) (h3 t h4) h5 h6 h7
  have hApos : 0 < azim 0 (v2 t) (v3 t) (v4 t) :=
    lt_of_le_of_ne (azim_nonneg 0 (v2 t) (v3 t) (v4 t)) (Ne.symm h7)
  obtain ⟨e4, he4, hb4⟩ := Metric.continuousAt_iff.mp hcont
    (azim 0 (v2 t) (v3 t) (v4 t) / 2) (by linarith [hApos])
  have hposat : ∀ q, dist q t < e4 → ¬ (azim 0 (v2 q) (v3 q) (v4 q) = 0) := by
    intro q hq
    have hd := hb4 hq
    rw [Real.dist_eq] at hd
    obtain ⟨h2qa, h2qb⟩ := abs_lt.mp hd
    intro hzero
    have hnpos : 0 ≤ azim 0 (v2 t) (v3 t) (v4 t) := azim_nonneg 0 (v2 t) (v3 t) (v4 t)
    linarith
  have hc1 : ContinuousAt (fun x => ‖cross3 (v2 x) (v3 x)‖) t :=
    (w5cA2_continuousAt_cross3 (h1 t h4) (h2 t h4)).norm
  have hc2 : ContinuousAt (fun x => ‖cross3 (v2 x) (v4 x)‖) t :=
    (w5cA2_continuousAt_cross3 (h1 t h4) (h3 t h4)).norm
  have hc3 : ContinuousAt (fun x => ‖v2 x‖) t := (h1 t h4).norm
  obtain ⟨e1, he1, hb1⟩ := w5cA2_eventually_ne hc1
    (ne_of_gt (norm_pos_iff.mpr (cross3_ne_p14 h5)))
  obtain ⟨e2, he2, hb2⟩ := w5cA2_eventually_ne hc2
    (ne_of_gt (norm_pos_iff.mpr (cross3_ne_p14 h6)))
  obtain ⟨e3, he3, hb3⟩ := w5cA2_eventually_ne hc3
    (ne_of_gt (norm_pos_iff.mpr hv2t0))
  set m : ℝ := min (min e1 (min e2 e3)) (min e4 (min ((t - a) / 2) ((b - t) / 2)))
    with hmd
  set e : ℝ := m / 2 with hed
  have h4a : a < t := h4.1
  have h4b : t < b := h4.2
  have hmpos : 0 < m := lt_min (lt_min he1 (lt_min he2 he3)) (lt_min he4
    (lt_min (by linarith) (by linarith)))
  have hmle1 : m ≤ e1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmle2 : m ≤ e2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmle3 : m ≤ e3 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hmle4 : m ≤ e4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmha : m ≤ (t - a) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmhb : m ≤ (b - t) / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨e, by linarith, ?_⟩
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := hx
  have habsle : |x - t| ≤ e := abs_le.mpr ⟨by linarith, by linarith⟩
  have hxab : x ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hm1 : e ≤ e1 := by linarith [hmle1, hed]
  have hm2 : e ≤ e2 := by linarith [hmle2, hed]
  have hm3 : e ≤ e3 := by linarith [hmle3, hed]
  have hm4 : e ≤ e4 := by linarith [hmle4, hed]
  have hst1 : |t - x| < e1 := by
    rw [abs_sub_comm]
    have h11 : e < e1 := by linarith [hmle1, he1, hed]
    linarith [habsle, h11]
  have hst2 : |t - x| < e2 := by
    rw [abs_sub_comm]
    have h12 : e < e2 := by linarith [hmle2, he2, hed]
    linarith [habsle, h12]
  have hst3 : |t - x| < e3 := by
    rw [abs_sub_comm]
    have h13 : e < e3 := by linarith [hmle3, he3, hed]
    linarith [habsle, h13]
  have hxd : dist x t < e4 := by
    rw [Real.dist_eq]
    have h14 : e < e4 := by linarith [hmle4, he4, hed]
    linarith [habsle, h14]
  have hcol1 : ¬ Collinear ℝ ({0, v2 x, v3 x} : Set V3) := by
    intro hcol
    have hz : cross3 (v2 x) (v3 x) = 0 := w5cA2_collinear0_iff_cross.mp hcol
    have hzn : ‖cross3 (v2 x) (v3 x)‖ = 0 := by rw [hz, norm_zero]
    exact hb1 x hst1 hzn
  have hcol2 : ¬ Collinear ℝ ({0, v2 x, v4 x} : Set V3) := by
    intro hcol
    have hz : cross3 (v2 x) (v4 x) = 0 := w5cA2_collinear0_iff_cross.mp hcol
    have hzn : ‖cross3 (v2 x) (v4 x)‖ = 0 := by rw [hz, norm_zero]
    exact hb2 x hst2 hzn
  have hv2xn : ‖v2 x‖ ≠ 0 := by
    by_contra hzn
    exact hb3 x hst3 hzn
  have hv2x : v2 x ≠ 0 := fun hz => hv2xn (by rw [hz, norm_zero])
  have hposx : ¬ (azim 0 (v2 x) (v3 x) (v4 x) = 0) := hposat x hxd
  exact (w5cA3_continuousAt_azim (h1 x hxab) (h2 x hxab) (h3 x hxab) hcol1 hcol2
    hposx).continuousWithinAt

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
  obtain ⟨h0mem, hcont, hzero⟩ := h1
  have hw1 : f w1 0 = w1 := hzero w1 (by simp)
  have hw2 : f w2 0 = w2 := hzero w2 (by simp)
  have hw0 : f w0 0 = w0 := hzero w0 (by simp)
  have hv0 : f v 0 = v := hzero v (by simp)
  obtain ⟨-, hpos, hlt⟩ := h5
  obtain ⟨c, hAc, hcB⟩ : ∃ c : ℝ, azim 0 w1 w2 v < c ∧ c < azim 0 w1 w2 w0 :=
    ⟨(azim 0 w1 w2 v + azim 0 w1 w2 w0) / 2, by linarith, by linarith⟩
  have hAcCont : ContinuousAt (fun t => azim 0 (f w1 t) (f w2 t) (f v t)) 0 := by
    refine w5cA3_continuousAt_azim (hcont w1 (by simp) 0 h0mem)
      (hcont w2 (by simp) 0 h0mem) (hcont v (by simp) 0 h0mem) ?_ ?_ ?_
    · simpa [hw1, hw2] using h2
    · simpa [hw1, hv0] using h4
    · rw [hw1, hw2, hv0]
      exact ne_of_gt hpos
  have hBcCont : ContinuousAt (fun t => azim 0 (f w1 t) (f w2 t) (f w0 t)) 0 := by
    refine w5cA3_continuousAt_azim (hcont w1 (by simp) 0 h0mem)
      (hcont w2 (by simp) 0 h0mem) (hcont w0 (by simp) 0 h0mem) ?_ ?_ ?_
    · simpa [hw1, hw2] using h2
    · simpa [hw1, hw0] using h3
    · rw [hw1, hw2, hw0]
      exact ne_of_gt (lt_trans hpos hlt)
  have hA0 : azim 0 (f w1 0) (f w2 0) (f v 0) = azim 0 w1 w2 v := by
    rw [hw1, hw2, hv0]
  have hB0 : azim 0 (f w1 0) (f w2 0) (f w0 0) = azim 0 w1 w2 w0 := by
    rw [hw1, hw2, hw0]
  obtain ⟨e1, he1, hb1⟩ := Metric.continuousAt_iff.mp hAcCont
    (azim 0 w1 w2 v / 2) (by linarith)
  obtain ⟨e2, he2, hb2⟩ := Metric.continuousAt_iff.mp hAcCont
    (c - azim 0 w1 w2 v) (by linarith)
  obtain ⟨e3, he3, hb3⟩ := Metric.continuousAt_iff.mp hBcCont
    (azim 0 w1 w2 w0 - c) (by linarith)
  refine ⟨min e1 (min e2 e3), lt_min he1 (lt_min he2 he3), ?_⟩
  intro t ht
  have ht1 : dist t 0 < e1 := by
    rw [Real.dist_eq]; simpa using lt_of_lt_of_le ht (min_le_left _ _)
  have ht23 : dist t 0 < min e2 e3 := by
    rw [Real.dist_eq]; simpa using lt_of_lt_of_le ht (min_le_right _ _)
  have ht2 : dist t 0 < e2 := lt_of_lt_of_le ht23 (min_le_left _ _)
  have ht3 : dist t 0 < e3 := lt_of_lt_of_le ht23 (min_le_right _ _)
  have h1' := hb1 (x := t) ht1
  rw [hA0, Real.dist_eq] at h1'
  have hApos : 0 < azim 0 (f w1 t) (f w2 t) (f v t) := by
    have := (abs_lt.mp h1').1
    linarith
  have h2' := hb2 (x := t) ht2
  rw [hA0, Real.dist_eq] at h2'
  have hAlt : azim 0 (f w1 t) (f w2 t) (f v t) < c := by
    have := (abs_lt.mp h2').2
    linarith
  have h3' := hb3 (x := t) ht3
  rw [hB0, Real.dist_eq] at h3'
  have hcLt : c < azim 0 (f w1 t) (f w2 t) (f w0 t) := by
    have := (abs_lt.mp h3').1
    linarith
  refine ⟨?_, hApos, lt_trans hAlt hcLt⟩
  intro hcol
  have hz : azim 0 (f w1 t) (f w2 t) (f v t) = 0 := by
    unfold azim
    rw [if_pos (Or.inr hcol)]
  linarith

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
  have hz : ∀ u ∈ ({w0, w1, w2, v} : Set V3), f u 0 = u := fun u hu =>
    h1.2.2 u hu
  refine NHCXLRV_p14 v w0 w1 w2 f a b h1 ?_ ?_ ?_ h5
  · simpa [hz w1 (by simp), hz w2 (by simp)] using h2
  · simpa [hz w1 (by simp), hz w0 (by simp)] using h3
  · simpa [hz w1 (by simp), hz v (by simp)] using h4

/-- HOL `WNWSHJT` (hl:1295).  NEEDS: azim continuity + deformation kit. -/
theorem WNWSHJT_p14 (w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b : ℝ)
    (h1 : Deformation f ({w0, w1, w2} : Set V3) a b)
    (h2 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3))
    (h4 : 0 < azim 0 w1 w2 w0) (h5 : azim 0 w1 w2 w0 < Real.pi) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      azim 0 (f w1 t) (f w2 t) (f w0 t) < Real.pi := by
  obtain ⟨h0mem, hcont, hzero⟩ := h1
  have hw1 : f w1 0 = w1 := hzero w1 (by simp)
  have hw2 : f w2 0 = w2 := hzero w2 (by simp)
  have hw0 : f w0 0 = w0 := hzero w0 (by simp)
  have hBcCont : ContinuousAt (fun t => azim 0 (f w1 t) (f w2 t) (f w0 t)) 0 := by
    refine w5cA3_continuousAt_azim (hcont w1 (by simp) 0 h0mem)
      (hcont w2 (by simp) 0 h0mem) (hcont w0 (by simp) 0 h0mem) ?_ ?_ ?_
    · simpa [hw1, hw2] using h2
    · simpa [hw1, hw0] using h3
    · rw [hw1, hw2, hw0]
      exact ne_of_gt h4
  have hB0 : azim 0 (f w1 0) (f w2 0) (f w0 0) = azim 0 w1 w2 w0 := by
    rw [hw1, hw2, hw0]
  obtain ⟨e, he, hb⟩ := Metric.continuousAt_iff.mp hBcCont
    (Real.pi - azim 0 w1 w2 w0) (by linarith)
  refine ⟨e, he, ?_⟩
  intro t ht
  have ht' : dist t 0 < e := by
    rw [Real.dist_eq]; simpa using ht
  have h := hb (x := t) ht'
  rw [hB0, Real.dist_eq] at h
  have := (abs_lt.mp h).2
  linarith

/-- HOL `LOFA_IMP_INANGLE_EQ_AZIM` (hl:1325).  NEEDS: fan structure
(`LocalFan` is the LocalAuto1 skeleton). -/
theorem LOFA_IMP_INANGLE_EQ_AZIM_p14 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (h1 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (h2 : v ∈ V) :
    interiorAngle1 0 FF v = azimInFan (v, rhoNode1 FF v) E := by
  have h2' := w5cA7_localFan_p2 h1
  have hd : (v, rhoNode1 FF v) ∈ FF := w5cA7_rho_mem_FF h1 h2
  have hdart : (v, rhoNode1 FF v) ∈ Fan.dart1OfFan V E :=
    w5cA7_mem_dart_of_face h1 hd
  have e1 : interiorAngle1 0 FF v = interiorAngle1_p2 0 FF v :=
    w5cA7_interiorAngle1_eq 0 FF v
  have e2 : azimInFan (v, rhoNode1 FF v) E =
      azimInFan_p2 (v, rhoNode1_p2 FF v) E := by
    rw [w5cA7_rhoNode1_eq]
    exact w5cA7_azimInFan_p2_eq h1.1 hdart
  rw [e1, e2]
  exact w5cA7_inangle_eq_azimInFan_p2 h2' h2

/-- HOL `deformation_rho_node1_equivariant1` (hl:1353).  NEEDS: fan
structure + deformation theory. -/
theorem deformation_rho_node1_equivariant1_p14 (f : V3 → ℝ → V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
    (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V) :
    f (rhoNode1 FF v) t =
      rhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) := by
  have hd : (v, rhoNode1 FF v) ∈ FF := w5cA7_rho_mem_FF h2 h4
  have himg : (f v t, f (rhoNode1 FF v) t) ∈
      (fun d => (f d.1 t, f d.2 t)) '' FF := Set.mem_image_of_mem _ hd
  exact (w5cA7_deter_rho h3 himg).symm

/-- HOL `deformation_ivs_rho_node1_equivariant1` (hl:1381).  NEEDS: fan
structure + deformation theory. -/
theorem deformation_ivs_rho_node1_equivariant1_p14 (f : V3 → ℝ → V3) (V : Set V3)
    (E : Set (Set V3)) (FF : Set (V3 × V3)) (a b : ℝ) (v : V3) (t : ℝ)
    (h1 : Deformation f V a b) (h2 : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    (h3 : LocalFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF)) (h4 : v ∈ V) :
    f (ivsRhoNode1 FF v) t =
      ivsRhoNode1 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) := by
  have hd : (ivsRhoNode1 FF v, v) ∈ FF := w5cA7_ivs_mem_FF h2 h4
  have himg : (f (ivsRhoNode1 FF v) t, f v t) ∈
      (fun d => (f d.1 t, f d.2 t)) '' FF := Set.mem_image_of_mem _ hd
  exact (w5cA7_deter_ivs h3 himg).symm

/-- HOL `deformation_subset` (hl:1409). -/
theorem deformation_subset_p14 (f : V3 → ℝ → V3) (U V : Set V3) (a b : ℝ)
    (hsub : U ⊆ V) (h : Deformation f V a b) : Deformation f U a b := by
  obtain ⟨h0, hc, hf⟩ := h
  exact ⟨h0, fun v hv => hc v (hsub hv), fun v hv => hf v (hsub hv)⟩

/-- w8: finite-min Skolemization for positive-radius windows (private copy of
the later `SKOLEM_EPSILON_p14`, usable at this point of the file). -/
private theorem w8_skolem_min {A : Type*} (Q : ℝ → A → Prop) (s : Set A)
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
  obtain ⟨hLF, -⟩ := h1
  have hLF2 : localFan_p2 V E FF := w5cA7_localFan_p2 hLF
  have hVfin : V.Finite := LOCAL_FAN_FINITE_V hLF2
  have hFFfin : FF.Finite := by
    obtain ⟨HS, -, -, -, -, -, ⟨x0, hx0, hFx0⟩, -⟩ := hLF2
    refine (HS.darts.finite_toSet).subset ?_
    rw [hFx0]
    exact Hypermap.face_subset_darts HS hx0
  -- (1) LocalFan transfer along the deformation
  obtain ⟨e1, he1, hLFt⟩ := XRECQNS_UPDATE_p37 (f := f) h3 hLF
  -- (2) uniform window for `azimInFan <= pi` (from h7)
  have h7' : ∀ x : V3 × V3, ∃ e2 : ℝ, 0 < e2 ∧ (x ∈ FF →
      ∀ t, -e2 < t ∧ t < e2 →
        azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi) := by
    intro x
    obtain ⟨e2, he2⟩ := h7 x
    by_cases hx : x ∈ FF
    · obtain ⟨hpos, hprop⟩ := he2 hx
      exact ⟨e2, hpos, fun _ => hprop⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  obtain ⟨e2, he2⟩ := (w8_skolem_min (A := V3 × V3) (s := FF)
    (Q := fun e x => ∀ t, -e < t ∧ t < e →
      azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi)
    (fun e e' i _ hle _ hQ t ht => hQ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    hFFfin).mp h7'
  have he2pos : 0 < e2 := (he2 (0, 0)).1
  -- (3) uniform window for `V ⊆ wedgeInFanGe` (from h6, already V-uniform)
  have h6'' : ∀ x : V3 × V3, ∃ e3 : ℝ, 0 < e3 ∧ (x ∈ FF →
      ∀ t, -e3 < t ∧ t < e3 →
        ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
          ((fun s => (fun v => f v t) '' s) '' E)) := by
    intro x
    obtain ⟨e3, he3⟩ := h6 x
    by_cases hx : x ∈ FF
    · obtain ⟨hpos, hprop⟩ := he3 hx
      exact ⟨e3, hpos, fun _ => hprop⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  obtain ⟨e3, he3⟩ := (w8_skolem_min (A := V3 × V3) (s := FF)
    (Q := fun e x => ∀ t, -e < t ∧ t < e →
      ((fun v => f v t) '' V) ⊆ wedgeInFanGe (f x.1 t, f x.2 t)
        ((fun s => (fun v => f v t) '' s) '' E))
    (fun e e' i _ hle _ hQ t ht => hQ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    hFFfin).mp h6''
  have he3pos : 0 < e3 := (he3 (0, 0)).1
  -- (4) uniform window for the generic (non-planarity) condition (from h5)
  have h5' : ∀ p : V3 × (V3 × V3), ∃ e4 : ℝ, 0 < e4 ∧ (p ∈ (V ×ˢ FF) →
      ∀ t, -e4 < t ∧ t < e4 →
        affGe ({0} : Set V3) ({f p.2.1 t, f p.2.2 t} : Set V3) ∩
          affLt ({0} : Set V3) ({f p.1 t} : Set V3) = ∅) := by
    intro p
    obtain ⟨e4, he4⟩ := h5 p.1 p.2.1 p.2.2
    by_cases hp : (p.2.1, p.2.2) ∈ FF ∧ p.1 ∈ V
    · obtain ⟨hpos, hprop⟩ := he4 hp
      exact ⟨e4, hpos, fun _ => hprop⟩
    · refine ⟨1, one_pos, fun hmem => absurd ?_ hp⟩
      rw [Set.mem_prod] at hmem
      exact ⟨hmem.2, hmem.1⟩
  obtain ⟨e4, he4⟩ := (w8_skolem_min (A := V3 × (V3 × V3)) (s := V ×ˢ FF)
    (Q := fun e p => ∀ t, -e < t ∧ t < e →
      affGe ({0} : Set V3) ({f p.2.1 t, f p.2.2 t} : Set V3) ∩
        affLt ({0} : Set V3) ({f p.1 t} : Set V3) = ∅)
    (fun e e' i _ hle _ hQ t ht => hQ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (hVfin.prod hFFfin)).mp h5'
  have he4pos : 0 < e4 := (he4 (0, (0, 0))).1
  refine ⟨min (min e1 e2) (min e3 e4), lt_min (lt_min he1 he2pos) (lt_min he3pos he4pos), ?_⟩
  intro t ht
  have ht' := abs_lt.mpr ht
  have ht1 : |t| < e1 := lt_of_lt_of_le ht' (le_trans (min_le_left _ _) (min_le_left _ _))
  have hte2 : -e2 < t ∧ t < e2 := abs_lt.mp
    (lt_of_lt_of_le ht' (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hte3 : -e3 < t ∧ t < e3 := abs_lt.mp
    (lt_of_lt_of_le ht' (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hte4 : -e4 < t ∧ t < e4 := abs_lt.mp
    (lt_of_lt_of_le ht' (le_trans (min_le_right _ _) (min_le_right _ _)))
  constructor
  · refine ⟨hLFt t ht1, ?_⟩
    rintro ⟨d1, d2⟩ hx
    obtain ⟨d, hdFF, hdeq⟩ := hx
    have h1eq : f d.1 t = d1 := congrArg Prod.fst hdeq
    have h2eq : f d.2 t = d2 := congrArg Prod.snd hdeq
    rw [← h1eq, ← h2eq]
    exact ⟨(he2 d).2 hdFF t hte2, (he3 d).2 hdFF t hte3⟩
  · rintro v' w' u' hE' hV'
    obtain ⟨u, huV, rfl⟩ := hV'
    have hLF2t : localFan_p2 ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) := w5cA7_localFan_p2 (hLFt t ht1)
    rcases LOFA_IN_E_IMP_IN_FF hLF2t hE' with hd | hd
    · obtain ⟨d, hdFF, hdeq⟩ := hd
      have h := (he4 (u, (d.1, d.2))).2 (by
        rw [Set.mem_prod]; exact ⟨huV, hdFF⟩) t hte4
      have h1eq : f d.1 t = v' := congrArg Prod.fst hdeq
      have h2eq : f d.2 t = w' := congrArg Prod.snd hdeq
      rw [← h1eq, ← h2eq]
      exact h
    · obtain ⟨d, hdFF, hdeq⟩ := hd
      have h := (he4 (u, (d.1, d.2))).2 (by
        rw [Set.mem_prod]; exact ⟨huV, hdFF⟩) t hte4
      have h1eq : f d.1 t = w' := congrArg Prod.fst hdeq
      have h2eq : f d.2 t = v' := congrArg Prod.snd hdeq
      rw [← h1eq, ← h2eq, Set.pair_comm]
      exact h

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

/-- w9 recon: `zlz_azim` under the interval strictness that HOL's *open*
`real_interval (a,b)` supplies (`a < 0 < b`) but the LocalAuto1 `Deformation`
encoding (`0 ∈ Set.Icc a b`) did not.  Everything else is proved; this
lemma is the exact statement of `zlz_azim_p14` with `ha`/`hb` added; SF-99
(2026-11-05) upgraded `Deformation` to `Set.Ioo`, so `zlz_azim_p14` is now a
one-line consumer of this lemma. -/
private theorem w9_zlz_azim_strict (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (ha : a < 0) (hb : 0 < b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ x : V3 × V3, ∃ e2 : ℝ, x ∈ FF →
      0 < e2 ∧ ∀ t, -e2 < t ∧ t < e2 →
        azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi := by
  rintro ⟨p1, p2⟩
  by_cases hxFF : (p1, p2) ∈ FF
  · have hLF : LocalFan V E FF := h1.1
    have hlf2 : localFan_p2 V E FF := w5cA7_localFan_p2 hLF
    have hedge : ∀ u ∈ V, ∃ z, {u, z} ∈ E := w5cA7_hedge_of_LocalFan hLF
    have hp1V : p1 ∈ V := (LOCAL_FAN_IMP_IN_V2 hlf2 hxFF).1
    have hp2V : p2 ∈ V := (LOCAL_FAN_IMP_IN_V2 hlf2 hxFF).2
    have hp2 : p2 = rhoNode1 FF p1 := (w5cA7_deter_rho hLF hxFF).symm
    have hin : interiorAngle1 0 FF p1 = azimInFan (p1, p2) E := by
      rw [hp2]
      exact LOFA_IMP_INANGLE_EQ_AZIM_p14 V E FF p1 hLF hedge hp1V
    obtain ⟨e0, he0, hfan_t⟩ := XRECQNS_UPDATE_p37 (f := f) h3 hLF
    obtain ⟨e1, he1, he1le, hint⟩ := real_interval_contains_0_ball_p14 a b e0 ha hb he0
    by_cases hpi : interiorAngle1 0 FF p1 = Real.pi
    · refine ⟨e1, fun _ => ⟨he1, fun t ht => ?_⟩⟩
      have htab : |t| < e1 := abs_lt.mpr ht
      have htI : t ∈ Set.Icc a b := hint t htab
      have ht0 : |t| < e0 := lt_of_lt_of_le htab he1le
      have hLFt : LocalFan ((fun v => f v t) '' V)
          ((fun s => (fun v => f v t) '' s) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) := hfan_t t ht0
      have hptV : f p1 t ∈ (fun v => f v t) '' V := Set.mem_image_of_mem _ hp1V
      have heq := LOFA_IMP_INANGLE_EQ_AZIM_p14 _ _ _ _
        hLFt (w5cA7_hedge_of_LocalFan hLFt) hptV
      have h4' := h4 p1 hp1V t htI hpi
      rw [heq] at h4'
      have hrhot := deformation_rho_node1_equivariant1_p14 f V E FF a b p1 t h3
        hLF hedge hLFt hp1V
      rw [hp2, hrhot]
      exact h4'
    · have hle : interiorAngle1 0 FF p1 ≤ Real.pi := by
        have hx := h1.2 (p1, p2) hxFF
        rw [hin]
        exact hx.1
      have hlt : interiorAngle1 0 FF p1 < Real.pi := lt_of_le_of_ne hle hpi
      have hivsV : ivsRhoNode1 FF p1 ∈ V := by
        rw [w5cA7_ivsRhoNode1_eq]
        exact LOCAL_FAN_IVS_IN_V hlf2 hp1V
      have hsub3 : ({ivsRhoNode1 FF p1, p1, p2} : Set V3) ⊆ V := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact hivsV
        · exact hp1V
        · exact hp2V
      have hdef3 : Deformation f ({ivsRhoNode1 FF p1, p1, p2} : Set V3) a b :=
        deformation_subset_p14 f _ V a b hsub3 h3
      have hnc2 : ¬ Collinear ℝ ({0, f p1 0, f p2 0} : Set V3) := by
        rw [hdef3.2.2 p1 (by simp), hdef3.2.2 p2 (by simp), hp2]
        simpa [w5cA7_rhoNode1_eq] using LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf2 hp1V
      have hnc3 : ¬ Collinear ℝ ({0, f p1 0, f (ivsRhoNode1 FF p1) 0} : Set V3) := by
        rw [hdef3.2.2 p1 (by simp), hdef3.2.2 (ivsRhoNode1 FF p1) (by simp)]
        simpa [w5cA7_ivsRhoNode1_eq] using LOFA_IMP_NOT_COLL_IVS hlf2 hp1V
      have hpos0 : 0 < azim 0 p1 p2 (ivsRhoNode1 FF p1) := by
        rw [hp2]
        simpa [interiorAngle1, interiorAngle1_p2, w5cA7_rhoNode1_eq, w5cA7_ivsRhoNode1_eq]
          using INTERIOR_ANGLE1_POS hlf2 hp1V
      have hlt0 : azim 0 p1 p2 (ivsRhoNode1 FF p1) < Real.pi := by
        rw [hp2]
        simpa [interiorAngle1] using hlt
      obtain ⟨e2, he2, hltpi⟩ :=
        WNWSHJT_p14 (ivsRhoNode1 FF p1) p1 p2 f a b hdef3 hnc2 hnc3 hpos0 hlt0
      refine ⟨min e1 e2, fun _ => ⟨lt_min he1 he2, fun t ht => ?_⟩⟩
      have htab : |t| < min e1 e2 := abs_lt.mpr ht
      have ht1 : |t| < e1 := lt_of_lt_of_le htab (min_le_left _ _)
      have ht2 : |t| < e2 := lt_of_lt_of_le htab (min_le_right _ _)
      have ht0 : |t| < e0 := lt_of_lt_of_le ht1 he1le
      have hLFt : LocalFan ((fun v => f v t) '' V)
          ((fun s => (fun v => f v t) '' s) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) := hfan_t t ht0
      have hLF2t : localFan_p2 ((fun v => f v t) '' V)
          ((fun s => (fun v => f v t) '' s) '' E)
          ((fun d => (f d.1 t, f d.2 t)) '' FF) := w5cA7_localFan_p2 hLFt
      have hptV : f p1 t ∈ (fun v => f v t) '' V := Set.mem_image_of_mem _ hp1V
      have hrhot := deformation_rho_node1_equivariant1_p14 f V E FF a b p1 t h3
        hLF hedge hLFt hp1V
      have hivst := deformation_ivs_rho_node1_equivariant1_p14 f V E FF a b p1 t h3
        hLF hedge hLFt hp1V
      have himg : (f p1 t, f p2 t) ∈ (fun d => (f d.1 t, f d.2 t)) '' FF :=
        Set.mem_image_of_mem _ hxFF
      have hdart : (f p1 t, f p2 t) ∈
          Fan.dart1OfFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E) :=
        w5cA7_mem_dart_of_face hLFt himg
      have key : azimInFan (f p1 t, f p2 t)
            ((fun s => (fun v => f v t) '' s) '' E)
          = azim 0 (f p1 t) (f p2 t) (f (ivsRhoNode1 FF p1) t) := by
        rw [w5cA7_azimInFan_p2_eq hLFt.1 hdart, hp2, hrhot, hivst]
        simpa [w5cA7_rhoNode1_eq, w5cA7_ivsRhoNode1_eq] using
          AZIM_IN_FAN_RHOND_IVS_RHOND hLF2t hptV
      rw [key]
      exact le_of_lt (hltpi t ht2)
  · exact ⟨1, fun h => absurd h hxFF⟩

/-- HOL `zlz_azim` (hl:1664).  NEEDS: terminal deformation theory. -/
theorem zlz_azim_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ x : V3 × V3, ∃ e2 : ℝ, x ∈ FF →
      0 < e2 ∧ ∀ t, -e2 < t ∧ t < e2 →
        azimInFan (f x.1 t, f x.2 t) ((fun s => (fun v => f v t) '' s) '' E) ≤ Real.pi := by
  exact w9_zlz_azim_strict a b V E FF f h1 h2 h3 h3.1.1 h3.1.2 h4

/-- W7 helper: wedge persistence along four continuous curves (the
curve-level form of `NHCXLRV`, used by `zlz_generic` with the cross-product
curve `t ↦ f v t × f w t`). -/
private theorem w5cA7_wedge_persist {w1 w2 w0 vz : ℝ → V3}
    (hc1 : ContinuousAt w1 0) (hc2 : ContinuousAt w2 0)
    (hc3 : ContinuousAt w0 0) (hcz : ContinuousAt vz 0)
    (hnc12 : ¬ Collinear ℝ ({0, w1 0, w2 0} : Set V3))
    (hnc10 : ¬ Collinear ℝ ({0, w1 0, w0 0} : Set V3))
    (hnc1z : ¬ Collinear ℝ ({0, w1 0, vz 0} : Set V3))
    (hpos : 0 < azim 0 (w1 0) (w2 0) (vz 0))
    (hlt : azim 0 (w1 0) (w2 0) (vz 0) < azim 0 (w1 0) (w2 0) (w0 0)) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
      vz t ∈ Kepler.Geom.wedge 0 (w1 t) (w2 t) (w0 t) := by
  obtain ⟨c, hAc, hcB⟩ : ∃ c : ℝ,
      azim 0 (w1 0) (w2 0) (vz 0) < c ∧ c < azim 0 (w1 0) (w2 0) (w0 0) :=
    ⟨(azim 0 (w1 0) (w2 0) (vz 0) + azim 0 (w1 0) (w2 0) (w0 0)) / 2,
      by linarith, by linarith⟩
  have hAcCont : ContinuousAt (fun t => azim 0 (w1 t) (w2 t) (vz t)) 0 :=
    w5cA3_continuousAt_azim hc1 hc2 hcz hnc12 hnc1z (ne_of_gt hpos)
  have hBcCont : ContinuousAt (fun t => azim 0 (w1 t) (w2 t) (w0 t)) 0 :=
    w5cA3_continuousAt_azim hc1 hc2 hc3 hnc12 hnc10
      (ne_of_gt (lt_trans hpos hlt))
  have hA0 : azim 0 (w1 0) (w2 0) (vz 0) = azim 0 (w1 0) (w2 0) (vz 0) := rfl
  have hB0 : azim 0 (w1 0) (w2 0) (w0 0) = azim 0 (w1 0) (w2 0) (w0 0) := rfl
  obtain ⟨e1, he1, hb1⟩ := Metric.continuousAt_iff.mp hAcCont
    (azim 0 (w1 0) (w2 0) (vz 0) / 2) (by linarith)
  obtain ⟨e2, he2, hb2⟩ := Metric.continuousAt_iff.mp hAcCont
    (c - azim 0 (w1 0) (w2 0) (vz 0)) (by linarith)
  obtain ⟨e3, he3, hb3⟩ := Metric.continuousAt_iff.mp hBcCont
    (azim 0 (w1 0) (w2 0) (w0 0) - c) (by linarith)
  refine ⟨min e1 (min e2 e3), lt_min he1 (lt_min he2 he3), ?_⟩
  intro t ht
  have htd : dist t 0 < min e1 (min e2 e3) := by
    rw [Real.dist_eq]; simpa using ht
  have ht1 : dist t 0 < e1 := lt_of_lt_of_le htd (min_le_left _ _)
  have ht23 : dist t 0 < min e2 e3 := lt_of_lt_of_le htd (min_le_right _ _)
  have ht2 : dist t 0 < e2 := lt_of_lt_of_le ht23 (min_le_left _ _)
  have ht3 : dist t 0 < e3 := lt_of_lt_of_le ht23 (min_le_right _ _)
  have h1' := hb1 (x := t) ht1
  rw [hA0, Real.dist_eq] at h1'
  have hApos : 0 < azim 0 (w1 t) (w2 t) (vz t) := by
    have := (abs_lt.mp h1').1
    linarith
  have h2' := hb2 (x := t) ht2
  rw [hA0, Real.dist_eq] at h2'
  have hAlt : azim 0 (w1 t) (w2 t) (vz t) < c := by
    have := (abs_lt.mp h2').2
    linarith
  have h3' := hb3 (x := t) ht3
  rw [hB0, Real.dist_eq] at h3'
  have hcLt : c < azim 0 (w1 t) (w2 t) (w0 t) := by
    have := (abs_lt.mp h3').1
    linarith
  refine ⟨?_, hApos, lt_trans hAlt hcLt⟩
  intro hcol
  have hz : azim 0 (w1 t) (w2 t) (vz t) = 0 := by
    unfold azim
    rw [if_pos (Or.inr hcol)]
  linarith

/-- HOL `zlz_generic` (hl:1852).  NEEDS: terminal deformation theory. -/
theorem zlz_generic_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b) :
    ∀ u v w : V3, ∃ e4 : ℝ, ((v, w) ∈ FF ∧ u ∈ V) →
      0 < e4 ∧ ∀ t, -e4 < t ∧ t < e4 →
        affGe ({0} : Set V3) ({f v t, f w t} : Set V3) ∩
          affLt ({0} : Set V3) ({f u t} : Set V3) = ∅ := by
  intro u v w
  by_cases hprem : (v, w) ∈ FF ∧ u ∈ V
  · obtain ⟨hd, huV⟩ := hprem
    have hlo : LocalFan V E FF := h1.1
    have hlf2 : localFan_p2 V E FF := w5cA7_localFan_p2 hlo
    have hvV : v ∈ V := (LOCAL_FAN_IMP_IN_V2 hlf2 hd).1
    have hwV : w ∈ V := (LOCAL_FAN_IMP_IN_V2 hlf2 hd).2
    have hu0 : u ≠ 0 := w5cA7_v_ne_zero hlo huV
    have hrv : rhoNode1 FF v = w := w5cA7_deter_rho hlo hd
    have hnczero : ¬ Collinear ℝ ({0, v, w} : Set V3) := by
      have h := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf2 hvV
      rwa [show rhoNode1_p2 FF v = w from
        (w5cA7_rhoNode1_eq FF v).symm.trans hrv] at h
    have hE : ({v, w} : Set V3) ∈ E := (LOCAL_FAN_IN_FF_IN_ORD_PAIRS2 hlf2 hd hd).1
    have hgen := h2 v w u hE huV
    have hga : ¬ Coplanar ({0, u, v, w} : Set V3) ∨
        (-u) ∈ Kepler.Geom.wedge 0 (cross3 v w) w v :=
      (generic_alt_p14 u v w hnczero hu0).mp hgen
    obtain ⟨h0mem, hcont, hzero⟩ := h3
    have hucont : ContinuousAt (fun t => f u t) 0 := hcont u huV 0 h0mem
    have hvcont : ContinuousAt (fun t => f v t) 0 := hcont v hvV 0 h0mem
    have hwcont : ContinuousAt (fun t => f w t) 0 := hcont w hwV 0 h0mem
    have hGdot_cont : ContinuousAt (fun t => f u t ⬝ᵥ f u t) 0 :=
      w5cA2_continuousAt_dot hucont hucont
    have hGdot0 : (fun t => f u t ⬝ᵥ f u t) 0 ≠ 0 := by
      simp only [hzero u huV]
      exact ne_of_gt (dot3_self_pos_p14 hu0)
    obtain ⟨e1, he1, hb1⟩ := w5cA2_eventually_ne hGdot_cont hGdot0
    have hcross_cont : ContinuousAt (fun t => cross3 (f v t) (f w t)) 0 :=
      w5cA2_continuousAt_cross3 hvcont hwcont
    have hGcross_cont : ContinuousAt
        (fun t => cross3 (f v t) (f w t) ⬝ᵥ cross3 (f v t) (f w t)) 0 :=
      w5cA2_continuousAt_dot hcross_cont hcross_cont
    have hGcross0 : (fun t =>
        cross3 (f v t) (f w t) ⬝ᵥ cross3 (f v t) (f w t)) 0 ≠ 0 := by
      simp only [hzero v hvV, hzero w hwV]
      exact ne_of_gt (dot3_self_pos_p14 (cross3_ne_p14 hnczero))
    obtain ⟨e2, he2, hb2⟩ := w5cA2_eventually_ne hGcross_cont hGcross0
    rcases hga with hncop | hwedge
    · have hnp : ¬ Coplanar ({0, f u 0, f v 0, f w 0} : Set V3) := by
        simpa [hzero u huV, hzero v hvV, hzero w hwV] using hncop
      obtain ⟨e3, he3, hb3⟩ := NONPLANAR_OPEN_p14 (fun _ => (0:V3))
        (fun t => f u t) (fun t => f v t) (fun t => f w t) 0 hnp
        continuousAt_const hucont hvcont hwcont
      refine ⟨min e1 (min e2 e3), ?_⟩
      intro _
      refine ⟨lt_min he1 (lt_min he2 he3), ?_⟩
      intro t ht
      have htabs : |t| < min e1 (min e2 e3) := by rw [abs_lt]; exact ht
      have ht1 : dist t 0 < e1 := by
        rw [Real.dist_eq]
        simpa using lt_of_lt_of_le htabs (min_le_left _ _)
      have htd : dist t 0 < min e1 (min e2 e3) := by
        rw [Real.dist_eq]; simpa using htabs
      have ht23 : dist t 0 < min e2 e3 :=
        lt_of_lt_of_le htd (min_le_right _ _)
      have ht2 : dist t 0 < e2 := lt_of_lt_of_le ht23 (min_le_left _ _)
      have ht3 : dist t 0 < e3 := lt_of_lt_of_le ht23 (min_le_right _ _)
      have hfu_ne : f u t ≠ 0 := by
        intro hz
        exact hb1 t (by simpa using ht1) (by rw [hz]; simp)
      have hncv_t : ¬ Collinear ℝ ({0, f v t, f w t} : Set V3) := by
        have h2t : (fun t => cross3 (f v t) (f w t) ⬝ᵥ
            cross3 (f v t) (f w t)) t ≠ 0 := hb2 t (by simpa using ht2)
        have hcne : cross3 (f v t) (f w t) ≠ 0 := by
          intro hc
          exact h2t (by simp [hc])
        intro hcol
        exact hcne (w5cA2_collinear0_iff_cross.mp hcol)
      have hnp_t : ¬ Coplanar ({0, f u t, f v t, f w t} : Set V3) :=
        hb3 t (by simpa using ht3)
      exact (generic_alt_p14 (f u t) (f v t) (f w t) hncv_t hfu_ne).mpr
        (Or.inl hnp_t)
    · obtain ⟨hnc1z, hpos0, hlt0⟩ := hwedge
      obtain ⟨e3, he3, hb3⟩ := w5cA7_wedge_persist
        (w1 := fun t => cross3 (f v t) (f w t)) (w2 := fun t => f w t)
        (w0 := fun t => f v t) (vz := fun t => -f u t)
        hcross_cont hwcont hvcont hucont.neg
        (by simpa [hzero v hvV, hzero w hwV] using
          w5cA7_not_coll_cross_right hnczero)
        (by simpa [hzero v hvV, hzero w hwV] using
          w5cA7_not_coll_cross_left hnczero)
        (by
          rw [hzero v hvV, hzero w hwV, hzero u huV]
          simpa [Collinear3] using hnc1z)
        (by
          rw [hzero v hvV, hzero w hwV, hzero u huV]
          exact hpos0)
        (by
          rw [hzero v hvV, hzero w hwV, hzero u huV]
          exact hlt0)
      refine ⟨min e1 (min e2 e3), ?_⟩
      intro _
      refine ⟨lt_min he1 (lt_min he2 he3), ?_⟩
      intro t ht
      have htabs : |t| < min e1 (min e2 e3) := by rw [abs_lt]; exact ht
      have ht1 : dist t 0 < e1 := by
        rw [Real.dist_eq]
        simpa using lt_of_lt_of_le htabs (min_le_left _ _)
      have htd : dist t 0 < min e1 (min e2 e3) := by
        rw [Real.dist_eq]; simpa using htabs
      have ht23 : dist t 0 < min e2 e3 :=
        lt_of_lt_of_le htd (min_le_right _ _)
      have ht2 : dist t 0 < e2 := lt_of_lt_of_le ht23 (min_le_left _ _)
      have ht3 : dist t 0 < e3 := lt_of_lt_of_le ht23 (min_le_right _ _)
      have hfu_ne : f u t ≠ 0 := by
        intro hz
        exact hb1 t (by simpa using ht1) (by rw [hz]; simp)
      have hncv_t : ¬ Collinear ℝ ({0, f v t, f w t} : Set V3) := by
        have h2t : (fun t => cross3 (f v t) (f w t) ⬝ᵥ
            cross3 (f v t) (f w t)) t ≠ 0 := hb2 t (by simpa using ht2)
        have hcne : cross3 (f v t) (f w t) ≠ 0 := by
          intro hc
          exact h2t (by simp [hc])
        intro hcol
        exact hcne (w5cA2_collinear0_iff_cross.mp hcol)
      have hwedge_t : (-f u t) ∈ Kepler.Geom.wedge 0
          (cross3 (f v t) (f w t)) (f w t) (f v t) :=
        hb3 t (by simpa using ht3)
      exact (generic_alt_p14 (f u t) (f v t) (f w t) hncv_t hfu_ne).mpr
        (Or.inr hwedge_t)
  · exact ⟨1, fun h => absurd h hprem⟩

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
  -- the fan axioms give `V` finite and nonempty
  obtain ⟨hfan, -⟩ := h1.1
  obtain ⟨hVfin, hVne⟩ := hfan.2.2.1
  intro x
  by_cases hxFF : x ∈ FF
  · -- skolemize the pointwise `e3` and take its minimum over the finite `V`
    choose e3 he3 using fun v => h2 x v
    obtain ⟨v₁, hv₁⟩ : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hVne
    obtain ⟨v₀, hv₀, hmin⟩ := Set.exists_min_image V e3 hVfin ⟨v₁, hv₁⟩
    have hpos : 0 < e3 v₀ := (he3 v₀ ⟨hxFF, hv₀⟩).1
    refine ⟨e3 v₀, fun _ => ⟨hpos, ?_⟩⟩
    intro t ht y hy
    obtain ⟨v, hv, rfl⟩ := hy
    have hle : e3 v₀ ≤ e3 v := hmin v hv
    exact (he3 v ⟨hxFF, hv⟩).2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact ⟨1, fun h => absurd h hxFF⟩

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

/-- HOL `zlz_wedge_refl` (hl:2085): the three boundary vertices of the fan
wedge at `w` (`w` itself, its `rho_node1` and `ivs_rho_node1` neighbours)
stay in the deformed fan wedge for a whole deformation window.  Route: the
fan transfers (`XRECQNS_UPDATE_p37`), its two neighbour maps are
equivariant, `WEDGE_IN_FAN_RHOND_IVS_RHOND` names the `p2` wedge as
`wedgeGe 0 (f w t) (rho) (ivs)`, and the p1/p2 bridge
`w5cA7_wedgeInFanGe_p2_eq` lands back in the `LocalAuto1` vocabulary. -/
theorem zlz_wedge_refl_p14 (a b : ℝ) (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (f : V3 → ℝ → V3)
    (h1 : ConvexLocalFan V E FF) (h2 : Generic V E) (h3 : Deformation f V a b)
    (h4 : ∀ v ∈ V, ∀ t ∈ Icc a b, interiorAngle1 0 FF v = Real.pi →
      interiorAngle1 0 ((fun d => (f d.1 t, f d.2 t)) '' FF) (f v t) ≤ Real.pi) :
    ∀ v w : V3, w ∈ V → v ∈ ({w, rhoNode1 FF w, ivsRhoNode1 FF w} : Set V3) →
      ∃ e : ℝ, 0 < e ∧ ∀ t, -e < t ∧ t < e →
        f v t ∈ wedgeInFanGe (f w t, f (rhoNode1 FF w) t)
          ((fun s => (fun v => f v t) '' s) '' E) := by
  intro v w hw hv
  have hLF : LocalFan V E FF := h1.1
  have hedge : ∀ u ∈ V, ∃ z, {u, z} ∈ E := w5cA7_hedge_of_LocalFan hLF
  obtain ⟨e0, he0, hfan_t⟩ := XRECQNS_UPDATE_p37 (f := f) h3 hLF
  refine ⟨e0, he0, fun t ht => ?_⟩
  have htab : |t| < e0 := by rw [abs_lt]; exact ht
  have hLFt : LocalFan ((fun v => f v t) '' V)
      ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF) := hfan_t t htab
  have hLF2t : localFan_p2 ((fun v => f v t) '' V)
      ((fun s => (fun v => f v t) '' s) '' E)
      ((fun d => (f d.1 t, f d.2 t)) '' FF) := w5cA7_localFan_p2 hLFt
  have hrho := deformation_rho_node1_equivariant1_p14 f V E FF a b w t h3 hLF hedge hLFt hw
  have hivs := deformation_ivs_rho_node1_equivariant1_p14 f V E FF a b w t h3 hLF hedge hLFt hw
  have hdFF : (w, rhoNode1 FF w) ∈ FF := w5cA7_rho_mem_FF hLF hw
  have himg : (f w t, f (rhoNode1 FF w) t) ∈
      (fun d => (f d.1 t, f d.2 t)) '' FF := Set.mem_image_of_mem _ hdFF
  have hdart : (f w t, f (rhoNode1 FF w) t) ∈
      Fan.dart1OfFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E) :=
    w5cA7_mem_dart_of_face hLFt himg
  rw [w5cA7_wedgeInFanGe_p2_eq hLFt.1 hdart]
  have hW := WEDGE_IN_FAN_RHOND_IVS_RHOND hLF2t
    (v := f w t) (Set.mem_image_of_mem _ hw)
  rw [hrho, w5cA7_rhoNode1_eq, hW]
  rcases hv with hvw | hvr | hvi
  · rw [hvw]
    exact wedge_ge_refl_p14 0 (f w t) _ _
  · rw [hvr, hrho]
    exact (FST_LST_IN_WEDGE_GE 0 (f w t) _ _).1
  · rw [hvi, hivs]
    exact (FST_LST_IN_WEDGE_GE 0 (f w t) _ _).2

/-- HOL `zlz_wedge_open` (hl:2133): a vertex `v ∈ V` on the open wedge at `w`
(not just the three boundary vertices of `zlz_wedge_refl`) stays in the
deformed fan wedge; the bound is the minimum of the fan window and the
`NHCXLRV_ALT` wedge-persistence window (`v = w` is `zlz_wedge_refl`). -/
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
  intro v w hv hw hwedge
  by_cases hvw : v = w
  · rw [hvw]
    exact zlz_wedge_refl_p14 a b V E FF f h1 h2 h3 h4 w w hw (by simp)
  · have hLF : LocalFan V E FF := h1.1
    have hedge : ∀ u ∈ V, ∃ z, {u, z} ∈ E := w5cA7_hedge_of_LocalFan hLF
    have hlf2 : localFan_p2 V E FF := w5cA7_localFan_p2 hLF
    have hrhoV : rhoNode1 FF w ∈ V := by
      rw [w5cA7_rhoNode1_eq]
      exact LOFA_IN_V_SO_DO_RHO_NODE_V hlf2 hw
    have hivsV : ivsRhoNode1 FF w ∈ V := by
      rw [w5cA7_ivsRhoNode1_eq]
      exact LOCAL_FAN_IVS_IN_V hlf2 hw
    have hsub : ({ivsRhoNode1 FF w, w, rhoNode1 FF w, v} : Set V3) ⊆ V := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hivsV
      · exact hw
      · exact hrhoV
      · exact hv
    have hdef4 : Deformation f ({ivsRhoNode1 FF w, w, rhoNode1 FF w, v} : Set V3) a b :=
      deformation_subset_p14 f _ V a b hsub h3
    have hnc1 : ¬ Collinear ℝ ({0, w, rhoNode1 FF w} : Set V3) := by
      simpa [w5cA7_rhoNode1_eq] using LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hlf2 (v := w) hw
    have hnc2 : ¬ Collinear ℝ ({0, w, ivsRhoNode1 FF w} : Set V3) := by
      simpa [w5cA7_ivsRhoNode1_eq] using LOFA_IMP_NOT_COLL_IVS hlf2 (v := w) hw
    have hnc3 : ¬ Collinear ℝ ({0, w, v} : Set V3) :=
      PROPERTIES_GENERIC_LOCAL_FAN_p9 hlf2 (fun _ _ => True.intro) h2 w hw v hv hvw
    obtain ⟨e1, he1, hnh⟩ := NHCXLRV_ALT_p14 v (ivsRhoNode1 FF w) w
      (rhoNode1 FF w) f a b hdef4 hnc1 hnc2 hnc3 hwedge
    obtain ⟨e0, he0, hfan_t⟩ := XRECQNS_UPDATE_p37 (f := f) h3 hLF
    refine ⟨min e0 e1, lt_min he0 he1, fun t ht => ?_⟩
    have htab : |t| < min e0 e1 := abs_lt.mpr ht
    have ht0 : |t| < e0 := lt_of_lt_of_le htab (min_le_left _ _)
    have ht1 : |t| < e1 := lt_of_lt_of_le htab (min_le_right _ _)
    have hLFt : LocalFan ((fun v => f v t) '' V)
        ((fun s => (fun v => f v t) '' s) '' E)
        ((fun d => (f d.1 t, f d.2 t)) '' FF) := hfan_t t ht0
    have hrho := deformation_rho_node1_equivariant1_p14 f V E FF a b w t h3 hLF hedge hLFt hw
    have hivs := deformation_ivs_rho_node1_equivariant1_p14 f V E FF a b w t h3 hLF hedge hLFt hw
    have hdFF : (w, rhoNode1 FF w) ∈ FF := w5cA7_rho_mem_FF hLF hw
    have himg : (f w t, f (rhoNode1 FF w) t) ∈
        (fun d => (f d.1 t, f d.2 t)) '' FF := Set.mem_image_of_mem _ hdFF
    have hdart : (f w t, f (rhoNode1 FF w) t) ∈
        Fan.dart1OfFan ((fun v => f v t) '' V) ((fun s => (fun v => f v t) '' s) '' E) :=
      w5cA7_mem_dart_of_face hLFt himg
    rw [w5cA7_wedgeInFanGe_p2_eq hLFt.1 hdart]
    have hW := WEDGE_IN_FAN_RHOND_IVS_RHOND (w5cA7_localFan_p2 hLFt)
      (v := f w t) (Set.mem_image_of_mem _ hw)
    rw [hrho, w5cA7_rhoNode1_eq, hW]
    have hnh' := hnh t ht1
    rw [hrho, w5cA7_rhoNode1_eq, hivs, w5cA7_ivsRhoNode1_eq] at hnh'
    exact WEDGE_SUBSET_WEDGE_GE 0 (f w t) _ _ hnh'

/-- HOL `PROPERTIES_GENERIC_LOCAL_FAN_ALT` (hl:2217).  NEEDS: fan
structure (`LocalFan` skeleton) + generic theory. -/
theorem PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (u v : V3) (h1 : LocalFan V E FF) (h2 : u ∈ V)
    (h3 : v ∈ V) (h4 : u ≠ v) (h5 : Generic V E) :
    ¬ Collinear ℝ ({0, u, v} : Set V3) := by
  exact PROPERTIES_GENERIC_LOCAL_FAN_p9 (w5cA7_localFan_p2 h1) (fun _ _ => True.intro) h5
    u h2 v h3 (Ne.symm h4)

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

/-- HOL `IN_AFFINE_KY_LEMMA1` (marchal2.hl:3055, Lemma 53): a point of `s`
lies in the affine hull of `s`.  `affine hull` ↔ `affineSpan ℝ`. -/
private theorem w13_in_affine_ky_lemma1 {x : V3} {s : Set V3} (hx : x ∈ s) :
    x ∈ affineSpan ℝ s :=
  subset_affineSpan ℝ s hx

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

/-- w17 kit: the pair window `(Icc 0 (r+1))² ∪ (Icc 1 (r+2))²` minus the
diagonal — the index family over which `XIV_DEFORMATION` (HOL
ZLZTHIC.hl:2259) needs a uniform non-collinearity radius. -/
private def w17_pairs (r : ℕ) : Set (ℕ × ℕ) :=
  {p | (p.1 ∈ Set.Icc 0 (r + 1) ∧ p.2 ∈ Set.Icc 0 (r + 1) ∧ p.1 ≠ p.2) ∨
       (p.1 ∈ Set.Icc 1 (r + 2) ∧ p.2 ∈ Set.Icc 1 (r + 2) ∧ p.1 ≠ p.2)}

/-- w17 kit: the triple window over which the `dihV`-consistency radius is
taken (`dh = 0` triples with all indices in `1..r+1`). -/
private def w17_triples (r : ℕ) : Set (ℕ × ℕ × ℕ) :=
  Set.Icc 1 (r + 1) ×ˢ (Set.Icc 1 (r + 1) ×ˢ Set.Icc 1 (r + 1))

private theorem w17_pairs_finite (r : ℕ) : (w17_pairs r).Finite := by
  refine Set.Finite.subset ((Set.finite_Icc (0:ℕ) (r + 2)).prod
    (Set.finite_Icc (0:ℕ) (r + 2))) ?_
  rintro ⟨i, j⟩ (⟨hi, hj, -⟩ | ⟨hi, hj, -⟩)
  · exact ⟨⟨Nat.zero_le i, by have := hi.2; omega⟩,
      ⟨Nat.zero_le j, by have := hj.2; omega⟩⟩
  · exact ⟨⟨Nat.zero_le i, by have := hi.2; omega⟩,
      ⟨Nat.zero_le j, by have := hj.2; omega⟩⟩

private theorem w17_triples_finite (r : ℕ) : (w17_triples r).Finite :=
  (Set.finite_Icc 1 (r + 1)).prod
    ((Set.finite_Icc 1 (r + 1)).prod (Set.finite_Icc 1 (r + 1)))

/-- w17 kit: uniform non-collinearity radius over `w17_pairs`
(HOL `NONCOLLINEAR_OPEN` = `CONTINUOUS_PRESERVE_COLLINEAR` + `SKOLEM_EPSILON`). -/
private theorem w17_nc_window (f : V3 → ℝ → V3) (r : ℕ) (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h3 : Set.Pairwise (Set.Icc 1 (r + 2)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3)) :
    ∃ dc : ℝ, 0 < dc ∧ ∀ p ∈ w17_pairs r, ∀ t, |t| < dc →
      ¬ Collinear ℝ ({0, f (w p.1) t, f (w p.2) t} : Set V3) := by
  have hz : ∀ i, i ≤ r + 2 → f (w i) 0 = w i := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.2 (w i) hwin
  have hcont0 : ∀ i, i ≤ r + 2 → ContinuousAt (fun t => f (w i) t) 0 := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.1 (w i) hwin 0 h1.1
  have hncopen : ∀ (m n : ℕ)
      (hpair : Set.Pairwise (Set.Icc m n) fun i j =>
        ¬ Collinear ℝ ({0, w i, w j} : Set V3))
      (i j : ℕ), i ∈ Set.Icc m n → j ∈ Set.Icc m n → i ≠ j → n ≤ r + 2 →
      ∃ e : ℝ, 0 < e ∧ ∀ t, |t| < e →
        ¬ Collinear ℝ ({0, f (w i) t, f (w j) t} : Set V3) := by
    intro m n hpair i j hi hj hij hn
    have hi2 : i ≤ r + 2 := le_trans hi.2 hn
    have hj2 : j ≤ r + 2 := le_trans hj.2 hn
    have hnc : ¬ Collinear3 0 (w i) (w j) := hpair hi hj hij
    obtain ⟨e, he, hb⟩ := CONTINUOUS_PRESERVE_COLLINEAR (0 : V3)
      (fun t => f (w i) t) (fun t => f (w j) t) 0 (hcont0 i hi2) (hcont0 j hj2)
      (by simpa only [hz i hi2, hz j hj2] using hnc)
    exact ⟨e, he, fun t ht => hb t (by simpa using ht)⟩
  let Q : ℝ → ℕ × ℕ → Prop := fun e p => ∀ t, |t| < e →
    ¬ Collinear ℝ ({0, f (w p.1) t, f (w p.2) t} : Set V3)
  have hm : ∀ p : ℕ × ℕ, ∃ e : ℝ, 0 < e ∧ (p ∈ w17_pairs r → Q e p) := by
    intro p
    by_cases hp : p ∈ w17_pairs r
    · rcases hp with ⟨hi, hj, hij⟩ | ⟨hi, hj, hij⟩
      · exact (hncopen 0 (r + 1) h2 p.1 p.2 hi hj hij (by omega)).imp
          (fun e he => ⟨he.1, fun _ => he.2⟩)
      · exact (hncopen 1 (r + 2) h3 p.1 p.2 hi hj hij (by omega)).imp
          (fun e he => ⟨he.1, fun _ => he.2⟩)
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  have hmono : ∀ e e' : ℝ, ∀ i : ℕ × ℕ, 0 < e → e ≤ e' → i ∈ w17_pairs r →
      (Q e' i → Q e i) := by
    intro e e' i _ heei _ hq t ht
    exact hq t (lt_of_lt_of_le ht heei)
  obtain ⟨dc, hall⟩ := (SKOLEM_EPSILON_p14 Q (w17_pairs r) hmono
    (w17_pairs_finite r)).mp hm
  exact ⟨dc, (hall (0, 0)).1, fun p hp t ht => (hall p).2 hp t ht⟩

/-- w17 kit: `dihV` along a continuous triple of deformation curves is
`ContinuousAt` (HOL `REAL_CONTINUOUS_ATREAL_DIHV_COMPOSE`), via the LA9
forwarding lemma `fw5_continuousAt_dihV_p9`. -/
private theorem w17_continuousAt_dihV_comp {v2 v3 v4 : ℝ → V3} {t₀ : ℝ}
    (hc2 : ContinuousAt v2 t₀) (hc3 : ContinuousAt v3 t₀)
    (hc4 : ContinuousAt v4 t₀)
    (hn23 : ¬ Collinear ℝ ({0, v2 t₀, v3 t₀} : Set V3))
    (hn24 : ¬ Collinear ℝ ({0, v2 t₀, v4 t₀} : Set V3)) :
    ContinuousAt (fun t => dihV 0 (v2 t) (v3 t) (v4 t)) t₀ :=
  ContinuousAt.comp (x := t₀) (f := fun t => (v2 t, v3 t, v4 t))
    (g := fun q : V3 × V3 × V3 => dihV 0 q.1 q.2.1 q.2.2)
    (fw5_continuousAt_dihV_p9 (v2 t₀) (v3 t₀) (v4 t₀) hn23 hn24)
    (hc2.prodMk (hc3.prodMk hc4))

/-- w17 kit: uniform `dihV` consistency radius — every `dh = 0` triple in
`w17_triples` has `dihV < cc` along the deformation. -/
private theorem w17_dih_window (f : V3 → ℝ → V3) (dh : ℕ × ℕ × ℕ → ℝ) (r : ℕ)
    (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h4 : ∀ i j k, dihV 0 (w i) (w j) (w k) = dh (i, j, k))
    (cc : ℝ) (hcc : 0 < cc) :
    ∃ dd : ℝ, 0 < dd ∧ ∀ p ∈ w17_triples r,
      p.1 ≠ p.2.1 → p.1 ≠ p.2.2 → dh p = 0 → ∀ t, |t| < dd →
        dihV 0 (f (w p.1) t) (f (w p.2.1) t) (f (w p.2.2) t) < cc := by
  have hz : ∀ i, i ≤ r + 2 → f (w i) 0 = w i := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.2 (w i) hwin
  have hcont0 : ∀ i, i ≤ r + 2 → ContinuousAt (fun t => f (w i) t) 0 := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.1 (w i) hwin 0 h1.1
  let Q : ℝ → ℕ × ℕ × ℕ → Prop := fun e p =>
    p.1 ≠ p.2.1 → p.1 ≠ p.2.2 → dh p = 0 → ∀ t, |t| < e →
      dihV 0 (f (w p.1) t) (f (w p.2.1) t) (f (w p.2.2) t) < cc
  have hm : ∀ p : ℕ × ℕ × ℕ, ∃ e : ℝ, 0 < e ∧ (p ∈ w17_triples r → Q e p) := by
    intro p
    by_cases hp : p ∈ w17_triples r
    · by_cases hA : p.1 = p.2.1
      · exact ⟨1, one_pos, fun _ hne => absurd hA hne⟩
      · by_cases hB : p.1 = p.2.2
        · exact ⟨1, one_pos, fun _ _ hne => absurd hB hne⟩
        · by_cases hdh0 : dh p = 0
          · have hz1 : p.1 ≤ r + 2 := by have := hp.1.2; omega
            have hz21 : p.2.1 ≤ r + 2 := by have := hp.2.1.2; omega
            have hz22 : p.2.2 ≤ r + 2 := by have := hp.2.2.2; omega
            have hnc1 : ¬ Collinear ℝ
                ({0, f (w p.1) 0, f (w p.2.1) 0} : Set V3) := by
              have h := h2 ⟨Nat.zero_le p.1, hp.1.2⟩
                ⟨Nat.zero_le p.2.1, hp.2.1.2⟩ hA
              simpa only [hz p.1 hz1, hz p.2.1 hz21] using h
            have hnc2 : ¬ Collinear ℝ
                ({0, f (w p.1) 0, f (w p.2.2) 0} : Set V3) := by
              have h := h2 ⟨Nat.zero_le p.1, hp.1.2⟩
                ⟨Nat.zero_le p.2.2, hp.2.2.2⟩ hB
              simpa only [hz p.1 hz1, hz p.2.2 hz22] using h
            have hcon : ContinuousAt (fun t =>
                dihV 0 (f (w p.1) t) (f (w p.2.1) t) (f (w p.2.2) t)) 0 :=
              w17_continuousAt_dihV_comp (hcont0 p.1 hz1) (hcont0 p.2.1 hz21)
                (hcont0 p.2.2 hz22) hnc1 hnc2
            obtain ⟨e, he, hb⟩ := Metric.continuousAt_iff.mp hcon cc hcc
            refine ⟨e, he, fun _ _ _ hdh t ht => ?_⟩
            have hdist : dist (dihV 0 (f (w p.1) t) (f (w p.2.1) t) (f (w p.2.2) t))
                (dihV 0 (f (w p.1) 0) (f (w p.2.1) 0) (f (w p.2.2) 0)) < cc :=
              hb (by simpa [Real.dist_eq] using ht)
            have hv0 : dihV 0 (f (w p.1) 0) (f (w p.2.1) 0) (f (w p.2.2) 0) = 0 := by
              rw [hz p.1 hz1, hz p.2.1 hz21, hz p.2.2 hz22,
                h4 p.1 p.2.1 p.2.2]
              simpa using hdh0
            rw [hv0, Real.dist_eq] at hdist
            simpa using (abs_lt.mp hdist).2
          · exact ⟨1, one_pos, fun _ _ _ h => absurd h hdh0⟩
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  have hmono : ∀ e e' : ℝ, ∀ i : ℕ × ℕ × ℕ, 0 < e → e ≤ e' → i ∈ w17_triples r →
      (Q e' i → Q e i) := by
    intro e e' i _ heei _ hq hne1 hne2 hdh t ht
    exact hq hne1 hne2 hdh t (lt_of_lt_of_le ht heei)
  obtain ⟨dd, hall⟩ := (SKOLEM_EPSILON_p14 Q (w17_triples r) hmono
    (w17_triples_finite r)).mp hm
  exact ⟨dd, (hall (0, 0, 0)).1, fun p hp hne1 hne2 hdh t ht =>
    (hall p).2 hp hne1 hne2 hdh t ht⟩

/-- w17 kit: the global azimuth floor `c` from the pointwise floors `h6`
(HOL: finite min of the pointwise floors). -/
private theorem w17_azim_floor (r : ℕ) (w : ℕ → V3)
    (h6 : ∀ i, i ∈ Set.Icc 1 (r + 1) →
      0 < azim 0 (w i) (w (i + 1)) (w (i - 1))) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, i ∈ Set.Icc 1 (r + 1) →
      c < azim 0 (w i) (w (i + 1)) (w (i - 1)) := by
  let Q : ℝ → ℕ → Prop := fun e i => e < azim 0 (w i) (w (i + 1)) (w (i - 1))
  have hm : ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ (i ∈ Set.Icc 1 (r + 1) → Q e i) := by
    intro i
    by_cases hi : i ∈ Set.Icc 1 (r + 1)
    · exact ⟨azim 0 (w i) (w (i + 1)) (w (i - 1)) / 2, half_pos (h6 i hi),
        fun _ => half_lt_self (h6 i hi)⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  have hmono : ∀ e e' : ℝ, ∀ i : ℕ, 0 < e → e ≤ e' → i ∈ Set.Icc 1 (r + 1) →
      (Q e' i → Q e i) := by
    intro e e' i _ hee _ hq
    exact lt_of_le_of_lt hee hq
  obtain ⟨c, hall⟩ := (SKOLEM_EPSILON_p14 Q (Set.Icc 1 (r + 1)) hmono
    (Set.finite_Icc 1 (r + 1))).mp hm
  exact ⟨c, (hall 0).1, fun i hi => (hall i).2 hi⟩

/-- w17 kit: the azimuth floor persists along the deformation (HOL
`REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE` = `w5cA3_continuousAt_azim`). -/
private theorem w17_azim_floor_window (f : V3 → ℝ → V3) (r : ℕ) (w : ℕ → V3)
    (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (h2 : Set.Pairwise (Set.Icc 0 (r + 1)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (h3 : Set.Pairwise (Set.Icc 1 (r + 2)) fun i j =>
      ¬ Collinear ℝ ({0, w i, w j} : Set V3))
    (cc : ℝ) (hcc0 : 0 ≤ cc)
    (hcc : ∀ i, i ∈ Set.Icc 1 (r + 1) →
      cc < azim 0 (w i) (w (i + 1)) (w (i - 1))) :
    ∃ daz : ℝ, 0 < daz ∧ ∀ i, i ∈ Set.Icc 1 (r + 1) → ∀ t, |t| < daz →
      cc < azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) := by
  have hz : ∀ i, i ≤ r + 2 → f (w i) 0 = w i := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.2 (w i) hwin
  have hcont0 : ∀ i, i ≤ r + 2 → ContinuousAt (fun t => f (w i) t) 0 := fun i hi => by
    have hwin : w i ∈ w '' Set.Icc 0 (r + 2) :=
      Set.mem_image_of_mem w (by simp only [Set.mem_Icc]; omega)
    exact h1.2.1 (w i) hwin 0 h1.1
  let Q : ℝ → ℕ → Prop := fun e i => ∀ t, |t| < e →
    cc < azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t)
  have hm : ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ (i ∈ Set.Icc 1 (r + 1) → Q e i) := by
    intro i
    by_cases hi : i ∈ Set.Icc 1 (r + 1)
    · have hi1 : 1 ≤ i := hi.1
      have hi2 : i ≤ r + 1 := hi.2
      have hm1 : i ≤ r + 2 := by omega
      have hm2 : i + 1 ≤ r + 2 := by omega
      have hm0 : i - 1 ≤ r + 2 := by omega
      have hci : ContinuousAt
          (fun t => azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t)) 0 := by
        refine w5cA3_continuousAt_azim (hcont0 i hm1) (hcont0 (i + 1) hm2)
          (hcont0 (i - 1) hm0) ?_ ?_ ?_
        · have h := h3 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
            (by omega : i ≠ i + 1)
          simpa only [hz i hm1, hz (i + 1) hm2] using h
        · have h := h2 ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩
            (by omega : i ≠ i - 1)
          simpa only [hz i hm1, hz (i - 1) hm0] using h
        · rw [hz i hm1, hz (i + 1) hm2, hz (i - 1) hm0]
          exact ne_of_gt (lt_of_le_of_lt hcc0 (hcc i hi))
      obtain ⟨d, hd, hbb⟩ := Metric.continuousAt_iff.mp hci
        (azim 0 (w i) (w (i + 1)) (w (i - 1)) - cc) (by linarith [hcc i hi])
      refine ⟨d, hd, fun _ t ht => ?_⟩
      have hdist : dist (azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t))
          (azim 0 (f (w i) 0) (f (w (i + 1)) 0) (f (w (i - 1)) 0)) <
          azim 0 (w i) (w (i + 1)) (w (i - 1)) - cc :=
        hbb (by simpa [Real.dist_eq] using ht)
      rw [hz i hm1, hz (i + 1) hm2, hz (i - 1) hm0, Real.dist_eq] at hdist
      have hlt := (abs_lt.mp hdist).1
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  have hmono : ∀ e e' : ℝ, ∀ i : ℕ, 0 < e → e ≤ e' → i ∈ Set.Icc 1 (r + 1) →
      (Q e' i → Q e i) := by
    intro e e' i _ heei _ hq t ht
    exact hq t (lt_of_lt_of_le ht heei)
  obtain ⟨daz, hall⟩ := (SKOLEM_EPSILON_p14 Q (Set.Icc 1 (r + 1)) hmono
    (Set.finite_Icc 1 (r + 1))).mp hm
  exact ⟨daz, (hall 0).1, fun i hi t ht => (hall i).2 hi t ht⟩

/-- w17 kit: uniform radius for `h5`'s `azim ≤ π` (HOL: skolemize the
pointwise `azim ≤ pi`). -/
private theorem w17_azim_pi_window (f : V3 → ℝ → V3) (r : ℕ) (w : ℕ → V3)
    (h5 : ∀ i, i ∈ Set.Icc 1 (r + 1) → ∃ e2 : ℝ, 0 < e2 ∧ ∀ t, |t| < e2 →
      azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi) :
    ∃ d2 : ℝ, 0 < d2 ∧ ∀ i, i ∈ Set.Icc 1 (r + 1) → ∀ t, |t| < d2 →
      azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi := by
  let Q : ℝ → ℕ → Prop := fun e i => ∀ t, |t| < e →
    azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi
  have hm : ∀ i : ℕ, ∃ e : ℝ, 0 < e ∧ (i ∈ Set.Icc 1 (r + 1) → Q e i) := by
    intro i
    by_cases hi : i ∈ Set.Icc 1 (r + 1)
    · obtain ⟨e, he, hb⟩ := h5 i hi
      exact ⟨e, he, fun _ => hb⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  have hmono : ∀ e e' : ℝ, ∀ i : ℕ, 0 < e → e ≤ e' → i ∈ Set.Icc 1 (r + 1) →
      (Q e' i → Q e i) := by
    intro e e' i _ heei _ hq t ht
    exact hq t (lt_of_lt_of_le ht heei)
  obtain ⟨d2, hall⟩ := (SKOLEM_EPSILON_p14 Q (Set.Icc 1 (r + 1)) hmono
    (Set.finite_Icc 1 (r + 1))).mp hm
  exact ⟨d2, (hall 0).1, fun i hi t ht => (hall i).2 hi t ht⟩

/-- w17: `XIV_DEFORMATION` (HOL ZLZTHIC.hl:2259) in the *strict* interval
form: the frozen `_p14` statement plus `a < 0 < b`.  HOL's `deformation`
runs over the open `real_interval (a,b)`, whereas the LocalAuto1
`Deformation` encoding (`0 ∈ Set.Icc a b`) does not record the sign
conditions; this private form is therefore the SF-99 bridge: once the public
statement / `Deformation` carries `ha`/`hb`, `XIV_DEFORMATION_p14` is a
one-line consumer of this lemma.  All hypotheses and the conclusion are the
frozen statement verbatim, with `ha`/`hb` inserted after `h1`.

Proof = HOL ZLZTHIC.hl:2259–2518 compressed: uniform non-collinearity radius
(`w17_nc_window`), dih-consistency radius at `c/2` (`w17_dih_window`), azim
floor `c` (`w17_azim_floor`) and its persistence radius
(`w17_azim_floor_window`), `h5`'s `azim ≤ π` radius
(`w17_azim_pi_window`); then a 4-ary `min` and `XIVPHKS_SHIFT_p16` at
`j = 1`, `k = r`. -/
private theorem w17_xiv_deformation_strict (f : V3 → ℝ → V3) (dh : ℕ × ℕ × ℕ → ℝ) (r : ℕ)
    (w : ℕ → V3) (a b : ℝ)
    (h1 : Deformation f (w '' Set.Icc 0 (r + 2)) a b)
    (ha : a < 0) (hb : 0 < b)
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
  have _ha := ha
  have _hb := hb
  obtain ⟨dc, hdcpos, hdc⟩ := w17_nc_window f r w a b h1 h2 h3
  obtain ⟨c, hcpos, hc⟩ := w17_azim_floor r w h6
  obtain ⟨dd, hddpos, hdd⟩ := w17_dih_window f dh r w a b h1 h2 h4 (c / 2) (by linarith)
  obtain ⟨daz, hdazpos, hdaz⟩ :=
    w17_azim_floor_window f r w a b h1 h2 h3 c (le_of_lt hcpos) hc
  obtain ⟨d2, hd2pos, hd2⟩ := w17_azim_pi_window f r w h5
  set eS : ℝ := c / 2 with heSdef
  have heSpos : 0 < eS := by rw [heSdef]; linarith
  have h2eS : 2 * eS = c := by rw [heSdef]; ring
  refine ⟨min eS (min dc (min dd (min daz d2))), ?_, ?_⟩
  · exact lt_min heSpos (lt_min hdcpos (lt_min hddpos (lt_min hdazpos hd2pos)))
  · intro t ht
    have htE : |t| < eS := lt_of_lt_of_le ht (min_le_left _ _)
    have htR : |t| < min dc (min dd (min daz d2)) :=
      lt_of_lt_of_le ht (min_le_right _ _)
    have htC : |t| < dc := lt_of_lt_of_le htR (min_le_left _ _)
    have htR2 : |t| < min dd (min daz d2) := lt_of_lt_of_le htR (min_le_right _ _)
    have htD : |t| < dd := lt_of_lt_of_le htR2 (min_le_left _ _)
    have htR3 : |t| < min daz d2 := lt_of_lt_of_le htR2 (min_le_right _ _)
    have htA : |t| < daz := lt_of_lt_of_le htR3 (min_le_left _ _)
    have htP : |t| < d2 := lt_of_lt_of_le htR3 (min_le_right _ _)
    have hpair1 : (Set.Icc 0 (r + 1)).Pairwise fun i j =>
        ¬ Collinear3 0 (f (w i) t) (f (w j) t) := by
      intro i hi j hj hij
      exact hdc (i, j) (Or.inl ⟨hi, hj, hij⟩) t htC
    have hpair2 : (Set.Icc 1 (r + 2)).Pairwise fun i j =>
        ¬ Collinear3 0 (f (w i) t) (f (w j) t) := by
      intro i hi j hj hij
      exact hdc (i, j) (Or.inr ⟨hi, hj, hij⟩) t htC
    have h1shift : ∀ i ∈ Finset.Icc 1 (r + 1),
        2 * eS < azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) := by
      intro i hi
      rw [h2eS]
      exact hdaz i (by simpa using hi) t htA
    have h2shift : ∀ i ∈ Finset.Icc 1 (r + 1),
        azim 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t) ≤ Real.pi := by
      intro i hi
      exact hd2 i (by simpa using hi) t htP
    have h3shift : ∀ p q, ({p, q, q + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) →
        p ≠ q → p ≠ q + 1 →
        dihV 0 (f (w p) t) (f (w q) t) (f (w (q + 1)) t) < eS := by
      intro p q hsub hpq hpq1
      have hmem : ∀ x ∈ ({p, q, q + 1} : Finset ℕ), x ∈ Set.Icc 1 (r + 1) :=
        fun x hx => by simpa using hsub hx
      have hp : p ∈ Set.Icc 1 (r + 1) := hmem p (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hq : q ∈ Set.Icc 1 (r + 1) := hmem q (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hq1 : q + 1 ∈ Set.Icc 1 (r + 1) := hmem (q + 1) (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hdh : dh (p, q, q + 1) = 0 := h7 p q (by
        intro x hx
        have hx' : x ∈ ({p, q, q + 1} : Finset ℕ) := by simpa using hx
        exact hmem x hx') hpq hpq1
      exact hdd (p, q, q + 1) ⟨hp, hq, hq1⟩ hpq hpq1 hdh t htD
    have h4shift : ∀ p q, ({p, p + 1, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) →
        q > p + 1 → dihV 0 (f (w p) t) (f (w (p + 1)) t) (f (w q) t) < eS := by
      intro p q hsub hq
      have hmem : ∀ x ∈ ({p, p + 1, q} : Finset ℕ), x ∈ Set.Icc 1 (r + 1) :=
        fun x hx => by simpa using hsub hx
      have hp : p ∈ Set.Icc 1 (r + 1) := hmem p (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hp1 : p + 1 ∈ Set.Icc 1 (r + 1) := hmem (p + 1) (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hqI : q ∈ Set.Icc 1 (r + 1) := hmem q (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hpq : p ≠ p + 1 := by omega
      have hpq' : p ≠ q := by omega
      have hpq1 : p + 1 < q := by omega
      have hdh : dh (p, p + 1, q) = 0 := h8 p q (by
        intro x hx
        have hx' : x ∈ ({p, p + 1, q} : Finset ℕ) := by simpa using hx
        exact hmem x hx') hpq1
      exact hdd (p, p + 1, q) ⟨hp, hp1, hqI⟩ hpq hpq' hdh t htD
    have h5shift : ∀ p q, ({p + 1, p, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) →
        q < p → dihV 0 (f (w (p + 1)) t) (f (w p) t) (f (w q) t) < eS := by
      intro p q hsub hq
      have hmem : ∀ x ∈ ({p + 1, p, q} : Finset ℕ), x ∈ Set.Icc 1 (r + 1) :=
        fun x hx => by simpa using hsub hx
      have hp1 : p + 1 ∈ Set.Icc 1 (r + 1) := hmem (p + 1) (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hp : p ∈ Set.Icc 1 (r + 1) := hmem p (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hqI : q ∈ Set.Icc 1 (r + 1) := hmem q (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have hne1 : p + 1 ≠ p := by omega
      have hne2 : p + 1 ≠ q := by omega
      have hdh : dh (p + 1, p, q) = 0 := h9 p q (by
        intro x hx
        have hx' : x ∈ ({p + 1, p, q} : Finset ℕ) := by simpa using hx
        exact hmem x hx') hq
      exact hdd (p + 1, p, q) ⟨hp1, hp, hqI⟩ hne1 hne2 hdh t htD
    have hshift := XIVPHKS_SHIFT_p16
      (fun i => wedgeGe 0 (f (w i) t) (f (w (i + 1)) t) (f (w (i - 1)) t))
      (fun i j k => azim 0 (f (w i) t) (f (w j) t) (f (w k) t))
      (fun i j k => dihV 0 (f (w i) t) (f (w j) t) (f (w k) t))
      eS r (fun i => f (w i) t) hpair1 hpair2 rfl rfl rfl
      (by rw [h2eS]; exact hcpos) h1shift h2shift h3shift h4shift h5shift
    refine ⟨?_, ?_⟩
    · simpa only [Nat.add_comm 1 r, Nat.add_sub_cancel] using
        hshift.1 r 1 (by norm_num) (by omega)
    · simpa only [Nat.add_comm 1 r] using hshift.2 r 1 (by norm_num) (by omega)

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

/-- w8: coercion injectivity helper for `V3 = EuclideanSpace ℝ (Fin 3)`. -/
private theorem w8_coe_inj {x y : V3} (h : ((x : V3) : Fin 3 → ℝ) = ((y : V3) : Fin 3 → ℝ)) :
    x = y := by
  simpa using congrArg (fun w : Fin 3 → ℝ => WithLp.toLp 2 w) h

/-- w8: `cross3 a a = 0`. -/
private theorem w8_cross3_self (a : V3) : cross3 a a = 0 := by
  refine w8_coe_inj ?_
  rw [coe_cross3_p14, coe_zero_p14]
  exact cross_self _

/-- w8: additivity of `cross3` in the left slot. -/
private theorem w8_cross3_add_left (a b c : V3) :
    cross3 (a + b) c = cross3 a c + cross3 b c := by
  refine w8_coe_inj ?_
  rw [coe_cross3_p14, coe_add_p14, coe_add_p14, coe_cross3_p14, coe_cross3_p14]
  ext i
  fin_cases i <;> simp [cross_apply, Pi.add_apply] <;> ring

/-- w8: additivity of `cross3` in the right slot. -/
private theorem w8_cross3_add_right (a b c : V3) :
    cross3 a (b + c) = cross3 a b + cross3 a c := by
  rw [w5cA2_cross3_neg a (b + c), w8_cross3_add_left, w5cA2_cross3_neg b a,
    w5cA2_cross3_neg c a, neg_add]
  simp only [neg_neg]

/-- w8: homogeneity of `cross3` in the left slot. -/
private theorem w8_cross3_smul_left (t : ℝ) (a c : V3) :
    cross3 (t • a) c = t • cross3 a c := by
  refine w8_coe_inj ?_
  rw [coe_cross3_p14, coe_smul_p14, coe_smul_p14, coe_cross3_p14]
  ext i
  fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring

/-- w8: homogeneity of `cross3` in the right slot. -/
private theorem w8_cross3_smul_right (t : ℝ) (a c : V3) :
    cross3 a (t • c) = t • cross3 a c := by
  rw [w5cA2_cross3_neg a (t • c), w8_cross3_smul_left, w5cA2_cross3_neg c a]
  simp only [smul_neg, neg_neg]

/-- w8: `affineSpan {0,u1,u2} ⊆ span {u1,u2}`. -/
private theorem w8_affineSpan_zero_pair_subset_span (u1 u2 : V3) :
    (affineSpan ℝ ({0, u1, u2} : Set V3) : Set V3) ⊆
      Submodule.span ℝ ({u1, u2} : Set V3) := by
  intro x hx
  refine affineSpan_induction hx ?_ ?_
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · intro c u v w hu hv hw
    have h1 : u -ᵥ v ∈ Submodule.span ℝ ({u1, u2} : Set V3) :=
      Submodule.sub_mem _ hu hv
    have h2 : c • (u -ᵥ v) ∈ Submodule.span ℝ ({u1, u2} : Set V3) :=
      Submodule.smul_mem _ c h1
    exact Submodule.add_mem _ h2 hw

/-- HOL `coplanar_cross_scale` (hl:2745): coplanar `v1, v2` whose cross product
has positive dot with `u1 × u2` give a positive multiple of `u1 × u2`. -/
theorem coplanar_cross_scale_p14 (u1 u2 v1 v2 : V3)
    (h1 : Coplanar ({0, u1, u2, v1, v2} : Set V3))
    (h2 : 0 < (cross3 v1 v2) ⬝ᵥ (cross3 u1 u2)) :
    ∃ t : ℝ, 0 < t ∧ cross3 v1 v2 = t • (cross3 u1 u2) := by
  have hnc : ¬ Collinear ℝ ({0, u1, u2} : Set V3) := by
    intro hcol
    have hz : cross3 u1 u2 = 0 := w5cA2_collinear0_iff_cross.mp hcol
    rw [hz, dot3_zero_right_p14] at h2
    linarith
  have hsub1 : ({v1, 0, u1, u2} : Set V3) ⊆ ({0, u1, u2, v1, v2} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  have hsub2 : ({v2, 0, u1, u2} : Set V3) ⊆ ({0, u1, u2, v1, v2} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  have hm1 : v1 ∈ affineSpan ℝ ({0, u1, u2} : Set V3) :=
    coplanar_in_affine_hull_p14 0 u1 u2 v1 (by simpa using hnc)
      (h1.subset hsub1)
  have hm2 : v2 ∈ affineSpan ℝ ({0, u1, u2} : Set V3) :=
    coplanar_in_affine_hull_p14 0 u1 u2 v2 (by simpa using hnc)
      (h1.subset hsub2)
  obtain ⟨a1, b1, hab1⟩ := Submodule.mem_span_pair.mp
    (w8_affineSpan_zero_pair_subset_span u1 u2 hm1)
  obtain ⟨a2, b2, hab2⟩ := Submodule.mem_span_pair.mp
    (w8_affineSpan_zero_pair_subset_span u1 u2 hm2)
  have hv1 : v1 = a1 • u1 + b1 • u2 := hab1.symm
  have hv2 : v2 = a2 • u1 + b2 • u2 := hab2.symm
  have hcross : cross3 v1 v2 = (a1 * b2 - b1 * a2) • cross3 u1 u2 := by
    rw [hv1, hv2, w8_cross3_add_left, w8_cross3_add_right, w8_cross3_add_right]
    rw [w8_cross3_smul_left, w8_cross3_smul_right, w8_cross3_smul_left,
      w8_cross3_smul_right, w8_cross3_smul_left, w8_cross3_smul_right,
      w8_cross3_smul_left, w8_cross3_smul_right]
    rw [w8_cross3_self, w8_cross3_self, w5cA2_cross3_neg u1 u2]
    simp only [smul_zero, zero_add, add_zero, smul_neg, smul_smul]
    module
  have hsq : 0 < (cross3 u1 u2) ⬝ᵥ (cross3 u1 u2) := by
    have h := inner_cross3_self_pos_p14 u1 u2 hnc
    rwa [inner_eq_dot] at h
  refine ⟨a1 * b2 - b1 * a2, ?_, hcross⟩
  have hpos : 0 < (cross3 v1 v2) ⬝ᵥ (cross3 u1 u2) := h2
  rw [hcross, dot3_smul_left_p14] at hpos
  by_contra hcon
  push_neg at hcon
  nlinarith

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

/-! ## w5cA5 kit（wave 5）：azim 轴反向与三点角加法

供 `azim_cycle_neg_p14` 收尾的私助件：`w5cA5_azim_axis_neg`（轴反向
`azim 0 (-e) x u = azim 0 e u x`，AzimSpec 标架传输）与
`w5cA5_sum3_azim`（三点角加法；`TopologyFan.azim_sum_core`/`sum3_azim_fan`
的私孪生，避免为底章模块引入下游 import）。全部只消费 `Kepler.Geom`。 -/

/-- 三点角加法的标架核心（`TopologyFan.azim_sum_core` 的私孪生）。 -/
private theorem w5cA5_azim_sum_core {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hncu : ¬ Collinear3 x v u) (hnc1 : ¬ Collinear3 x v w1)
    (hnc2 : ¬ Collinear3 x v w2) :
    ∃ n : ℤ, azim x v u w2 =
      azim x v u w1 + azim x v w1 w2 + (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v - x)
    (sub_ne_zero.mpr (fun he => hxv he))
  have hax : (v - x : V3) = dist v x • f3 := by
    rw [dist_eq_norm]
    exact halign
  obtain ⟨ψ, ru, r1, hru, hr1, hzu, hzw1⟩ := azim_frame_spec hncu hnc1 hon hax hxv
  obtain ⟨ψ2, ru2, r2, hru2, hr2, hzu2, hzw2⟩ := azim_frame_spec hncu hnc2 hon hax hxv
  obtain ⟨ψ', r1', r2', hr1', hr2', hzw1', hzw2'⟩ :=
    azim_frame_spec hnc1 hnc2 hon hax hxv
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
  refine ⟨n, ?_⟩
  have hc2 : ((azim x v u w2 : ℝ) : ℂ) * Complex.I
      = ((((azim x v u w1 + azim x v w1 w2 : ℝ)
          + (n:ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
    rw [hn]
    push_cast
    ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hc2

/-- 三点角加法（`TopologyFan.sum3_azim_fan` 的私孪生：三段和 < 2π 版）。 -/
private theorem w5cA5_sum3_azim {x v u w1 w2 : V3} (hxv : v ≠ x)
    (hncu : ¬ Collinear3 x v u) (hnc1 : ¬ Collinear3 x v w1)
    (hnc2 : ¬ Collinear3 x v w2)
    (hlt : azim x v u w1 + azim x v w1 w2 < 2 * Real.pi) :
    azim x v u w2 = azim x v u w1 + azim x v w1 w2 := by
  obtain ⟨n, hc3⟩ := w5cA5_azim_sum_core hxv hncu hnc1 hnc2
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  rcases Int.lt_trichotomy n 0 with hneg | hzero | hpos
  · exfalso
    have hle2 : ((n:ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : (n : ℤ) ≤ -1)
    have hmul : (n:ℝ) * (2 * Real.pi) ≤ (-1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hle2 h2pi.le
    linarith [hlt, hc3, hmul, azim_nonneg x v u w2]
  · rw [hzero] at hc3
    simp only [Int.cast_zero, zero_mul, add_zero] at hc3
    exact hc3
  · exfalso
    have hge : ((n:ℤ) : ℝ) ≥ 1 := by exact_mod_cast (by omega : (n : ℤ) ≥ 1)
    have hmul : (n:ℝ) * (2 * Real.pi) ≥ (1:ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge h2pi.le
    linarith [hlt, hc3, hmul, azim_nonneg x v u w1,
      azim_nonneg x v w1 w2, azim_lt_two_pi x v u w2]

/-- 反映恒等式：`cos((π-ψ)+(2π-θ)) = -cos(ψ+θ)`。 -/
private theorem w5cA5_cos_reflect (ψ θ : ℝ) :
    Real.cos ((Real.pi - ψ) + (2 * Real.pi - θ)) = -Real.cos (ψ + θ) := by
  rw [show (Real.pi - ψ) + (2 * Real.pi - θ)
      = (Real.pi - (ψ + θ)) + 2 * Real.pi from by ring,
    Real.cos_add_two_pi, Real.cos_pi_sub]

/-- 反映恒等式：`sin((π-ψ)+(2π-θ)) = sin(ψ+θ)`。 -/
private theorem w5cA5_sin_reflect (ψ θ : ℝ) :
    Real.sin ((Real.pi - ψ) + (2 * Real.pi - θ)) = Real.sin (ψ + θ) := by
  rw [show (Real.pi - ψ) + (2 * Real.pi - θ)
      = (Real.pi - (ψ + θ)) + 2 * Real.pi from by ring,
    Real.sin_add_two_pi, Real.sin_pi_sub]

/-- 轴反向的 AzimSpec 传输：轴 `-e` 的方位角候选为
`θ ↦ if θ = 0 then 0 else 2π - θ`（θ = `azim 0 e x u`）。标架取
`(f1,f2,f3) ↦ (-f1, f2, -f3)`（保持右手系，轴由 `-e` 转为 `e`）。 -/
private theorem w5cA5_azimSpec_neg {e x u : V3}
    (hx : ¬ Collinear3 0 e x) (hu : ¬ Collinear3 0 e u) :
    AzimSpec 0 (-e) x u (if azim 0 e x u = 0 then 0 else 2 * Real.pi - azim 0 e x u) := by
  obtain ⟨-, -, h1f, h2f, hframes⟩ := azim_master 0 e x u
  refine ⟨?_, ?_, -h1f, -h2f, ?_⟩
  · split_ifs with h0
    · exact le_refl 0
    · linarith [azim_lt_two_pi 0 e x u]
  · split_ifs with h0
    · have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
      linarith
    · have hpos : 0 < azim 0 e x u := lt_of_le_of_ne (azim_nonneg 0 e x u) (Ne.symm h0)
      linarith
  · intro f1 f2 f3 hf hax hw
    obtain ⟨h11, h22, h33, h12, h13, h23, hhand⟩ := hf
    have hon : Orthonormal3 (-f1) f2 (-f3) := by
      refine ⟨?_, h22, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using h11
      · simpa using h33
      · simpa using h12
      · simpa using h13
      · simpa using h23
      · have hcross (a b : Fin 3 → ℝ) : crossProduct (-a) b = -(crossProduct a b) := by
          rw [map_neg, LinearMap.neg_apply]
        have hval : crossProduct ((-f1 : V3) : Fin 3 → ℝ) ((f2 : V3) : Fin 3 → ℝ)
              ⬝ᵥ ((-f3 : V3) : Fin 3 → ℝ)
            = crossProduct ((f1 : V3) : Fin 3 → ℝ) ((f2 : V3) : Fin 3 → ℝ)
              ⬝ᵥ ((f3 : V3) : Fin 3 → ℝ) := by
          simp only [WithLp.ofLp_neg, hcross, neg_dotProduct, dotProduct_neg, neg_neg]
        rwa [hval]
    have he : e ≠ 0 := by
      intro h
      exact hx (collinear3_of_eq (v := (0:V3)) (w := e) (w1 := x) h)
    have haxe : (e - 0 : V3) = dist e 0 • (-f3) := by
      have hax' : -e = dist e 0 • f3 := by
        have h := hax
        rw [sub_zero, show dist (-e) 0 = dist e 0 from by simp [dist_eq_norm]] at h
        exact h
      rw [sub_zero]
      calc e = -(-e) := by simp
        _ = -(dist e 0 • f3) := by rw [hax']
        _ = dist e 0 • (-f3) := by rw [smul_neg]
    obtain ⟨ψ, r1, r2, rep1, rep2, hr1, hr2⟩ := hframes (-f1) f2 (-f3) hon haxe he
    refine ⟨Real.pi - ψ, r1, r2, ?_, ?_, hr1 hx, hr2 hu⟩
    · have htail : (-h1f) • ((-e) - 0) = h1f • (e - 0) := by
        rw [sub_zero, sub_zero, neg_smul, smul_neg, neg_neg]
      have hcos1 : r1 * Real.cos (Real.pi - ψ) = -(r1 * Real.cos ψ) := by
        rw [Real.cos_pi_sub]; ring
      rw [rep1, htail, hcos1, Real.sin_pi_sub, neg_smul, smul_neg]
    · have htail : (-h2f) • ((-e) - 0) = h2f • (e - 0) := by
        rw [sub_zero, sub_zero, neg_smul, smul_neg, neg_neg]
      rw [rep2, htail]
      split_ifs with h0
      · have hcos1 : r2 * Real.cos ((Real.pi - ψ) + 0)
            = -(r2 * Real.cos (ψ + azim 0 e x u)) := by
          rw [add_zero, Real.cos_pi_sub, h0, add_zero]; ring
        have hsin1 : r2 * Real.sin ((Real.pi - ψ) + 0)
            = r2 * Real.sin (ψ + azim 0 e x u) := by
          rw [add_zero, Real.sin_pi_sub, h0, add_zero]
        rw [hcos1, hsin1, neg_smul, smul_neg]
      · have hcos1 : r2 * Real.cos ((Real.pi - ψ) + (2 * Real.pi - azim 0 e x u))
            = -(r2 * Real.cos (ψ + azim 0 e x u)) := by
          rw [w5cA5_cos_reflect]; ring
        have hsin1 : r2 * Real.sin ((Real.pi - ψ) + (2 * Real.pi - azim 0 e x u))
            = r2 * Real.sin (ψ + azim 0 e x u) := by
          rw [w5cA5_sin_reflect]
        rw [hcos1, hsin1, neg_smul, smul_neg]

/-- 轴反向：`azim 0 (-e) x u = azim 0 e u x`（HOL `AZIM_COMPL_NEG` 的私孪生）。 -/
private theorem w5cA5_azim_axis_neg {e x u : V3}
    (hx : ¬ Collinear3 0 e x) (hu : ¬ Collinear3 0 e u) :
    azim 0 (-e) x u = azim 0 e u x := by
  have he : e ≠ 0 := by
    intro h
    exact hx (collinear3_of_eq (v := (0:V3)) (w := e) (w1 := x) h)
  have hneg_col : ∀ z : V3, Collinear3 0 (-e) z → Collinear3 0 e z := by
    intro z hc
    have hne : -e ≠ 0 := neg_ne_zero.mpr he
    obtain ⟨c, hc'⟩ := (collinear3_iff_smul (hw := hne) (v := 0) (w := -e) (w1 := z)).mp hc
    refine (collinear3_iff_smul (hw := he) (v := 0) (w := e) (w1 := z)).mpr ⟨-c, ?_⟩
    have hz : z - 0 = c • (-e - 0) := hc'
    simpa only [sub_zero, smul_neg, neg_smul] using hz
  have hxn : ¬ Collinear3 0 (-e) x := fun hc => hx (hneg_col x hc)
  have hun : ¬ Collinear3 0 (-e) u := fun hc => hu (hneg_col u hc)
  rw [azim_eq_of_spec hxn hun (w5cA5_azimSpec_neg hx hu), azim_compl hx hu]

/-- `IDENTIFY_AZIM_CYCLE_SIMPLE_p14` 的无 `cyclicSet` 版（原证明体不使用该
假设；此处内联以免为底章构造下游 `cyclicSet` 证据）。 -/
private theorem w5cA5_identify (W : Set V3) (v w p u : V3)
    (h1 : ¬ (W ⊆ {p})) (h2 : p ∈ W) (h3 : u ≠ p) (h4 : u ∈ W)
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

/-- HOL `azim_cycle_neg` (hl:2828).  NEEDS: azimuth-cycle negation theory
(wave-3: helpers `w5cA2_azim_axis_neg` (`azim 0 (-e) x u = azim 0 e u x`,
frame flip E1 := -E1, E2, E3 := -E3 of the AzimSpec transport) and
`w5cA2_sum2_azim` (the `Fan.sum2_azim_fan` skeleton with FAN replaced by
three `¬ Collinear3`); route = minimality `A ≤ azim 0 e v q`,
`C := azim 0 e w' w ≤ A`, one `sum2` application per trichotomy branch of
`A = azim 0 e v w'`, `azim_compl` for `C` from `D := azim 0 e w w'`, and
`azim_cycle_distinct_p14` at `(w, w')` for the `D = 0` branch). -/
theorem azim_cycle_neg_p14 (U : Set V3) (e v w : V3) (h1 : U.Finite) (h2 : v ∈ U)
    (h3 : azimCycle_p14 U 0 e v = w)
    (h4 : ∀ x ∈ U, e ⬝ᵥ (cross3 x (azimCycle_p14 U 0 e x)) ≠ 0) :
    azimCycle_p14 U 0 (-e) w = v := by
  have he0 : e ≠ 0 := by
    intro he
    exact h4 v h2 (by rw [he, dot3_eq_p14, coe_zero_p14, dotProduct_comm,
      dotProduct_zero])
  have hnc : ∀ x ∈ U, ¬ Collinear ℝ ({0, e, x} : Set V3) := by
    intro x hx hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul (hw := he0) (v := 0) (w := e)
      (w1 := x)).mp (by simpa [Collinear3] using hcol)
    have hc' : x = c • e := by simpa only [sub_zero] using hc
    apply h4 x hx
    rw [hc', dot3_eq_p14, coe_cross3_p14, coe_smul_p14, map_smul, LinearMap.smul_apply]
    simp [dot_self_cross]
  have hsubv : ¬ (U ⊆ {v}) := by
    intro hsub
    have hcv : azimCycle_p14 U 0 e v = v := by rw [azimCycle_p14, if_pos hsub]
    have hzz : cross3 v v ⬝ᵥ cross3 v v = 0 := by
      rw [dot3_eq_p14, coe_cross3_p14, cross_self, dotProduct_zero]
    exact h4 v h2 (by rw [hcv, dot3_self_zero_p14 hzz, dot3_zero_right_p14])
  obtain ⟨hcy1, hcy2, hcy3⟩ := w5cA_azimCycle_properties (W := U) (p := v) hsubv h1 0 e
  have hwv : w ≠ v := fun heq => hcy1 (by rw [h3]; exact heq)
  have hwU : w ∈ U := by rw [← h3]; exact hcy2
  have hmin : ∀ q ∈ U, q ≠ v →
      azim 0 e v w < azim 0 e v q ∨ azim 0 e v w = azim 0 e v q := by
    intro q hq hqv
    rcases hcy3 q hq hqv with hlt | ⟨heq, -⟩
    · exact Or.inl (by rwa [h3] at hlt)
    · exact Or.inr (by rwa [h3] at heq)
  have hsubw : ¬ (U ⊆ {w}) := by
    intro hsub
    exact hwv (hsub h2).symm
  have hkey : ∀ q ∈ U, q ≠ w → q ≠ v →
      azim 0 (-e) w v < azim 0 (-e) w q := by
    intro q hq hqw hqv
    have hw' : ¬ Collinear3 0 e w := hnc w hwU
    have hv' : ¬ Collinear3 0 e v := hnc v h2
    have hq' : ¬ Collinear3 0 e q := hnc q hq
    rw [w5cA5_azim_axis_neg (x := w) (u := v) hw' hv',
        w5cA5_azim_axis_neg (x := w) (u := q) hw' hq']
    rcases hmin q hq hqv with hlt | heq
    · have hBne : azim 0 e v q ≠ 0 :=
        ne_of_gt (lt_of_le_of_lt (azim_nonneg 0 e v w) hlt)
      have hqv' : azim 0 e q v = 2 * Real.pi - azim 0 e v q := by
        rw [azim_compl hv' hq', if_neg hBne]
      have hlt2 : azim 0 e q v + azim 0 e v w < 2 * Real.pi := by
        rw [hqv']; linarith [azim_lt_two_pi 0 e v q]
      have hadd := w5cA5_sum3_azim (x := 0) (v := e) (u := q) (w1 := v) (w2 := w)
        he0 hq' hv' hw' hlt2
      rw [hadd, hqv']
      linarith [azim_lt_two_pi 0 e v q]
    · exfalso
      have hmem : q ∈ affGt ({0, e} : Set V3) {w} :=
        (azim_eq_azim_iff hv' hw' hq').mp heq
      have hD0 : azim 0 e q w = 0 :=
        (azim_eq_zero_iff hq' hw').mpr hmem
      have hD0' : azim 0 e w q = 0 := by
        have hc := azim_compl hw' hq'
        rw [hD0] at hc
        by_contra hne
        rw [if_neg hne] at hc
        linarith [azim_lt_two_pi 0 e w q]
      obtain ⟨-, hcyw2, hminw⟩ :=
        w5cA_azimCycle_properties (W := U) (p := w) hsubw h1 0 e
      have hz0 : azim 0 e w (azimCycle_p14 U 0 e w) = 0 := by
        rcases hminw q hq hqw with hlt' | ⟨heq', -⟩
        · rw [hD0'] at hlt'
          linarith [azim_nonneg 0 e w (azimCycle_p14 U 0 e w)]
        · exact heq'.trans hD0'
      have hmem2 : w ∈ affGt ({0, e} : Set V3) {azimCycle_p14 U 0 e w} :=
        (azim_eq_zero_iff hw' (hnc _ hcyw2)).mp hz0
      have hcyc0 : azimCycle_p14 U 0 e w ≠ 0 := fun hz =>
        hnc _ hcyw2 (hz.symm ▸ collinear3_pair_left (v0 := (0:V3)) (v1 := e)
          (x := 0) rfl)
      have hcycE : azimCycle_p14 U 0 e w ≠ e := fun hz =>
        hnc _ hcyw2 (hz.symm ▸ collinear3_pair_right (v0 := (0:V3)) (v1 := e)
          (x := e) rfl)
      obtain ⟨c, hc, k, hwk⟩ := (affGt_pair_iff (v0 := 0) (v1 := e)
        (x := azimCycle_p14 U 0 e w) (y := w) (Ne.symm he0) hcyc0 hcycE).mp hmem2
      have hwrep : w = c • azimCycle_p14 U 0 e w + k • e := by
        simpa only [sub_zero] using hwk
      have hdot0 : e ⬝ᵥ (cross3 w (azimCycle_p14 U 0 e w)) = 0 := by
        nth_rewrite 1 [hwrep]
        rw [dot3_eq_p14, coe_cross3_p14, coe_add_p14, coe_smul_p14, coe_smul_p14,
          map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smul,
          LinearMap.smul_apply, cross_self, smul_zero, zero_add, dotProduct_comm,
          smul_dotProduct, dotProduct_comm, dot_self_cross, smul_zero]
      exact h4 w hwU hdot0
  exact w5cA5_identify U 0 (-e) w v hsubw hwU (Ne.symm hwv) h2
    (fun q hqw hq hqv => hkey q hq hqw hqv)


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

/-! ## w13 axiom audit (closed items only) -/

#print axioms w13_in_affine_ky_lemma1

/-! ## w15: GATE-B three-piece port (HOL local_lemmas.hl:6448/7036/7080) -/

/-- w15: 2-regularity gives no isolated vertices. -/
private theorem w15_hedge {V : Set V3} {E : Set (Set V3)}
    (h2reg : ∀ u ∈ V, (ee u E).ncard = 2) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : ee v E ≠ ∅ := by
    intro hE
    rw [hE, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨w, hw⟩

/-- w15: `LocalFan` → `localFan_p2` (the 2-regularity conjunct supplies the
no-isolated-vertex side condition). -/
private theorem w15_lf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : localFan_p2 V E FF := by
  obtain ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ := h
  exact localFan_p2.of_LocalFan_noIso ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ (w15_hedge h2reg)

/-- w15: consecutive orbit points at a local-fan vertex are non-collinear with
`0` (HOL `LOCAL_FAN_CHARACTER_OF_RHO_NODE3`, local_lemmas.hl:7065). -/
theorem w15_char3 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) {v : V3} (hv : v ∈ V) (i : ℕ) :
    ¬ Collinear ℝ ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) := by
  have h2 := w15_lf2 h
  have hbase : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i] v, rhoNode1 FF ((rhoNode1 FF)^[i] v)} : Set V3) :=
    LOCAL_FAN_CHARACTER_OF_RHO_NODE2 h2 (LOCAL_FAN_ITER_RHO_NODE_IN_V h2 hv i)
  have hgoal : (rhoNode1 FF)^[i + 1] v = rhoNode1 FF ((rhoNode1 FF)^[i] v) := by
    rw [show i + 1 = Nat.succ i from rfl, Function.iterate_succ_apply']
  rw [hgoal]
  exact hbase

/-- w15: the third point of a non-collinear triple is off the pair. -/
private theorem w15_ncol_third_notMem {a c d : V3}
    (h : ¬ Collinear ℝ ({a, c, d} : Set V3)) : d ∉ ({a, c} : Set V3) := by
  intro hd
  apply h
  have hsub : ({a, c, d} : Set V3) ⊆ ({a, c} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hd with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  exact (Collinear.subset hsub (collinear_pair (k := ℝ) (p₁ := a) (p₂ := c) : Collinear ℝ ({a, c} : Set V3)))

/-- w15: the middle point of a non-collinear triple is off the pair. -/
private theorem w15_ncol_mid_notMem {a c d : V3}
    (h : ¬ Collinear ℝ ({a, c, d} : Set V3)) : c ∉ ({a, d} : Set V3) := by
  intro hc
  apply h
  have hsub : ({a, c, d} : Set V3) ⊆ ({a, d} : Set V3) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  exact (Collinear.subset hsub (collinear_pair (k := ℝ) (p₁ := a) (p₂ := d) : Collinear ℝ ({a, d} : Set V3)))

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

/-- w15: `affLt {a,b} {x}` is symmetric in `x` and the member `y`, both off the
pair `{a,b}`. -/
theorem w15_affLt_swap {a b x y : V3}
    (hx : x ∉ ({a, b} : Set V3)) (hy : y ∉ ({a, b} : Set V3)) :
    y ∈ affLt ({a, b} : Set V3) ({x} : Set V3) ↔
      x ∈ affLt ({a, b} : Set V3) ({y} : Set V3) := by
  have hdx : Disjoint ({a, b} : Set V3) ({x} : Set V3) := by
    rwa [Set.disjoint_singleton_right]
  have hdy : Disjoint ({a, b} : Set V3) ({y} : Set V3) := by
    rwa [Set.disjoint_singleton_right]
  rw [AFF_LT_2_1 hdx, AFF_LT_2_1 hdy]
  constructor
  · rintro ⟨t1, t2, t3, ht3, hsum, hy'⟩
    refine ⟨-(t1 / t3), -(t2 / t3), 1 / t3,
      div_neg_of_pos_of_neg one_pos ht3, ?_, ?_⟩
    · exact w15_div_combo ht3.ne hsum
    · exact w15_div_combo_vec ht3.ne hy'
  · rintro ⟨s1, s2, s3, hs3, hsum, hx'⟩
    refine ⟨-(s1 / s3), -(s2 / s3), 1 / s3,
      div_neg_of_pos_of_neg one_pos hs3, ?_, ?_⟩
    · exact w15_div_combo hs3.ne hsum
    · exact w15_div_combo_vec hs3.ne hx'

private theorem w15_affine_cancel {X Y : V3} {mu lam h c t2 t3 : ℝ}
    (h1 : mu * c + lam * t3 = 0) :
    mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X := by
  have hh : mu • (h • X + c • Y) + lam • (t2 • X + t3 • Y)
      = (mu * h + lam * t2) • X + (mu * c + lam * t3) • Y := by module
  rw [hh, h1, zero_smul, add_zero]

/-- w15: `OPPOSITE_SIDES_IMP_INTER` (local_lemmas.hl:6324): a point of the open
`vc`-cone and one of the opposite open half-plane force the segment `conv0 {a,b}`
to cross `aff {va, vb}`.  (The extra `hvab` is not needed by HOL's `DISJOINT`
alone in the degenerate `va = vb` case; the caller always has it.  `vc` off
`aff {va,vb}` turns out not to be needed by this proof.) -/
theorem OPPOSITE_SIDES_IMP_INTER {va vb vc a b : V3}
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

/-- w15: `SUCCESSIVE_RHO_NODE1_AFF_LT` (local_lemmas.hl:6928): three consecutive
orbit points put the previous one in the open half-plane opposite the next one
across the axis `{0, ρ^i v}`.  Reduces to LA37's `ITER_IN_AFF_GT_2_1_P37` (the
`i`-shifted statement) plus the side-swap `w15_affLt_swap`. -/
theorem SUCCESSIVE_RHO_NODE1_AFF_LT {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (h : LocalFan V E FF) (hv : v ∈ V)
    (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
    (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P) :
    ∀ i, 0 < i → i < l →
      (rhoNode1 FF)^[i - 1] v ∈
        affLt ({0, (rhoNode1 FF)^[i] v} : Set V3) ({(rhoNode1 FF)^[i + 1] v} : Set V3) := by
  intro i hi hil
  have hU' : {z | ∃ n ≤ l, z = (rhoNode1 FF)^[n] v} = U := by
    rw [← hU]
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  have hP' : PlaneP_p37 P := hP
  have hj : i - 1 < l - 1 := by omega
  have hstep := ITER_IN_AFF_GT_2_1_p37 (V := V) (E := E) (FF := FF) (v := v) (l := l)
    (U := U) (P := P) h hv hU' hP' h0 hUsub (i - 1) hj
  have e2 : i - 1 + 2 = i + 1 := by omega
  have e1 : i - 1 + 1 = i := by omega
  rw [e2, e1] at hstep
  have hnc1 : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i] v} : Set V3) := by
    have hh := w15_char3 h hv (i - 1)
    rwa [show i - 1 + 1 = i from by omega] at hh
  have hnc2 : ¬ Collinear ℝ
      ({0, (rhoNode1 FF)^[i] v, (rhoNode1 FF)^[i + 1] v} : Set V3) :=
    w15_char3 h hv i
  have hx : (rhoNode1 FF)^[i - 1] v ∉ ({0, (rhoNode1 FF)^[i] v} : Set V3) :=
    w15_ncol_mid_notMem hnc1
  have hy : (rhoNode1 FF)^[i + 1] v ∉ ({0, (rhoNode1 FF)^[i] v} : Set V3) :=
    w15_ncol_third_notMem hnc2
  exact (w15_affLt_swap (x := (rhoNode1 FF)^[i - 1] v)
    (y := (rhoNode1 FF)^[i + 1] v) hx hy).mp hstep

/-- w15: `TWO_SIDES_SUCESSIVE` (local_lemmas.hl:7036): for `0 < i < l` the
segment joining the two orbit neighbours of `ρ^i v` crosses the axis
`aff {0, ρ^i v}`. -/
theorem TWO_SIDES_SUCESSIVE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v : V3} {l : ℕ} {U P : Set V3}
    (h : LocalFan V E FF) (hv : v ∈ V)
    (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
    (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P) :
    ∀ i, 0 < i → i < l →
      conv0_p2 ({(rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i + 1] v} : Set V3) ∩
        (affineSpan ℝ ({0, (rhoNode1 FF)^[i] v} : Set V3) : Set V3) ≠ ∅ := by
  intro i hi hil
  have hlt := SUCCESSIVE_RHO_NODE1_AFF_LT h hv hU hP h0 hUsub i hi hil
  have hnc := w15_char3 h hv i
  have hdis : Disjoint ({0, (rhoNode1 FF)^[i] v} : Set V3)
      ({(rhoNode1 FF)^[i + 1] v} : Set V3) := by
    rw [Set.disjoint_singleton_right]
    exact w15_ncol_third_notMem hnc
  have hgt : (rhoNode1 FF)^[i + 1] v ∈
      affGt ({0, (rhoNode1 FF)^[i] v} : Set V3)
        ({(rhoNode1 FF)^[i + 1] v} : Set V3) :=
    DISJOINT_IMP_Z_IN_AFF_GT hdis
  have hmemV : (rhoNode1 FF)^[i] v ∈ V :=
    LOCAL_FAN_ITER_RHO_NODE_IN_V (w15_lf2 h) hv i
  have hvab : (0 : V3) ≠ (rhoNode1 FF)^[i] v :=
    (FAN_IMP_V_DIFF h.1 ((rhoNode1 FF)^[i] v) hmemV).symm
  have hint := OPPOSITE_SIDES_IMP_INTER (va := 0) (vb := (rhoNode1 FF)^[i] v)
    (vc := (rhoNode1 FF)^[i + 1] v) (a := (rhoNode1 FF)^[i + 1] v)
    (b := (rhoNode1 FF)^[i - 1] v) hvab hdis hgt hlt
  rw [show ({(rhoNode1 FF)^[i - 1] v, (rhoNode1 FF)^[i + 1] v} : Set V3)
        = ({(rhoNode1 FF)^[i + 1] v, (rhoNode1 FF)^[i - 1] v} : Set V3) by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  exact hint

/-- w15: `ConvexLocalFan` (LA1) → `convexLocalFan_p2` (LA2) transport, the
public twin of LA37's private `la37g5_clf2` / CircularSolKit's `kcs_clf2`. -/
theorem w15_clf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) : convexLocalFan_p2 V E FF := by
  obtain ⟨hlf, hcvx⟩ := h
  have hcopy := hlf
  obtain ⟨hfan, -, -, -, -, h2reg⟩ := hcopy
  obtain ⟨-, -, -, -, -, hsub, -⟩ := localFan_data hlf
  have hlf2 := localFan_p2.of_LocalFan_noIso hlf (w15_hedge h2reg)
  refine ⟨hlf2, ?_⟩
  intro d hd
  refine ⟨?_, ?_⟩
  · have hb : azimInFan d E = azimInFan_p3 d E := azimInFan_eq_azimInFan_p3 hfan (hsub hd)
    show azimInFan_p2 d E ≤ Real.pi
    rw [show azimInFan_p2 d E = azimInFan_p3 d E from rfl, ← hb]
    exact (hcvx d hd).1
  · show V ⊆ wedgeInFanGe_p2 d E
    rw [show wedgeInFanGe_p2 d E = wedgeInFanGe_p3 d E from rfl,
      ← wedgeInFanGe_eq_wedgeInFanGe_p3 hfan (hsub hd)]
    exact (hcvx d hd).2

/-- w15: `CNVX_IMP_INTERIOR_ANGLE_PI` (local_lemmas.hl:7080): in a convex local
fan, every interior orbit vertex of a plane-carried orbit window has interior
angle `π`.  Port of the HOL chain `CVX_LO_IMP_LO` → `TWO_SIDES_SUCESSIVE` →
`OZQVSFF`. -/
theorem CNVX_IMP_INTERIOR_ANGLE_PI {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} {v : V3} {l : ℕ} {U P : Set V3}
    (h : ConvexLocalFan V E FF) (hv : v ∈ V)
    (hU : {(rhoNode1 FF)^[n] v | n ≤ l} = U)
    (hP : plane_p2 P) (h0 : (0 : V3) ∈ P) (hUsub : U ⊆ P) :
    ∀ i, 0 < i → i < l →
      interiorAngle1 0 FF ((rhoNode1 FF)^[i] v) = Real.pi := by
  intro i hi hil
  have hclf2 := w15_clf2 h
  have hlf2 : localFan_p2 V E FF := CVX_LO_IMP_LO hclf2
  have hmemV : ∀ n, (rhoNode1 FF)^[n] v ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv
  have hUmem : ∀ n, n ≤ l → (rhoNode1 FF)^[n] v ∈ U := by
    intro n hn
    rw [← hU]
    exact ⟨n, hn, rfl⟩
  have hts := TWO_SIDES_SUCESSIVE h.1 hv hU hP h0 hUsub i hi hil
  set a1 : V3 := (rhoNode1 FF)^[i - 1] v with ha1
  set a2 : V3 := (rhoNode1 FF)^[i] v with ha2
  set a3 : V3 := (rhoNode1 FF)^[i + 1] v with ha3
  have hnc1 : ¬ Collinear ℝ ({0, a2, a3} : Set V3) := w15_char3 h.1 hv i
  have hnc2 : ¬ Collinear ℝ ({0, a2, a1} : Set V3) := by
    have hh := w15_char3 h.1 hv (i - 1)
    rw [show i - 1 + 1 = i from by omega] at hh
    rwa [show ({0, a2, a1} : Set V3) = ({0, a1, a2} : Set V3) by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hdis1 : a3 ∉ (affineSpan ℝ ({0, a2} : Set V3) : Set V3) := by
    intro hm
    exact hnc1 (collinear_triple_iff.mpr (Or.inl hm))
  have hdis2 : a1 ∉ (affineSpan ℝ ({0, a2} : Set V3) : Set V3) := by
    intro hm
    exact hnc2 (collinear_triple_iff.mpr (Or.inl hm))
  have hempty : ({a3, a1} : Set V3) ∩
      (affineSpan ℝ ({0, a2} : Set V3) : Set V3) = ∅ := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1
      rcases hz1 with rfl | rfl
      · exact absurd hz2 hdis1
      · exact absurd hz2 hdis2
    · intro hz
      exact hz.elim
  have hspan : (affineSpan ℝ ({a2, 0} : Set V3) : Set V3) =
      (affineSpan ℝ ({0, a2} : Set V3) : Set V3) := by
    rw [show ({a2, 0} : Set V3) = ({0, a2} : Set V3) by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have hne : ¬ (((affineSpan ℝ ({a2, 0} : Set V3) : Set V3) ∩
      conv0_p2 ({a1, a3} : Set V3)) = ∅) := by
    intro hE
    apply hts
    rw [hspan, Set.inter_comm] at hE
    exact hE
  have hsub : ({a3, a2, a1} : Set V3) ⊆ V := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hmemV (i + 1)
    · exact hmemV i
    · exact hmemV (i - 1)
  have hsub2 : ({0, a3, a2, a1} : Set V3) ⊆ P := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact h0
    · exact hUsub (hUmem (i + 1) (by omega))
    · exact hUsub (hUmem i (by omega))
    · exact hUsub (hUmem (i - 1) (by omega))
  exact (OZQVSFF hclf2 (u := a3) (v := a2) (w := a1) (P := P)
    hsub hP hsub2 hempty hne).1

/-! ## w15 axiom audit (GATE-B three-piece port) -/

#print axioms w15_char3
#print axioms w15_affLt_swap
#print axioms OPPOSITE_SIDES_IMP_INTER
#print axioms SUCCESSIVE_RHO_NODE1_AFF_LT
#print axioms TWO_SIDES_SUCESSIVE
#print axioms w15_clf2
#print axioms CNVX_IMP_INTERIOR_ANGLE_PI

/-! ## §0 small self-contained helpers -/

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

/-- `LocalFan` → `localFan_p2` (copy of LA14's private `w15_lf2`). -/
private theorem w16_lf2 {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : localFan_p2 V E FF := by
  obtain ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ := h
  have hne : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
    intro v hv
    have h2 : (ee v E).ncard = 2 := h2reg v hv
    have hne' : ee v E ≠ ∅ := by
      intro hE
      rw [hE, Set.ncard_empty] at h2
      omega
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    exact ⟨w, hw⟩
  exact localFan_p2.of_LocalFan_noIso ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ hne

/-! ## §1 CONV02_SU_CONV2 (HOL Geomdetail.CONV02_SU_CONV2) -/

/-- HOL `CONV02_SU_CONV2`: `conv0 {a,b} ⊆ conv {a,b}`. -/
theorem CONV02_SU_CONV2 (a b : V3) :
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

/-! ## §2 AZIM_EQ_PI_ALT (public copy of LA2's private `w11_azim_pi_iff_affLt`) -/

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
theorem AZIM_EQ_PI_ALT {u v w : V3}
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

/-! ## §3 ray / aff_ge / aff_lt kit -/

/-- `affGe {x} ∅ = {x}`. -/
theorem w16_affGe_empty_singleton (x : V3) : affGe ({x} : Set V3) (∅ : Set V3) = {x} := by
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
theorem w16_smul_mem_affGe {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    t • u ∈ affGe ({0} : Set V3) ({u} : Set V3) :=
  w16_affsign_single (x := 0) (u := u) (y := t • u) (sgn := fun x => 0 ≤ x)
    (by simpa using hu.symm) (t1 := 1 - t) (t2 := t) (by simp) (by ring)
    (by simpa using ht)

/-- `t • u ∈ affLt {0} {u}` for `t < 0`. -/
theorem w16_smul_mem_affLt {u : V3} (hu : u ≠ 0) {t : ℝ} (ht : t < 0) :
    t • u ∈ affLt ({0} : Set V3) ({u} : Set V3) :=
  w16_affsign_single (x := 0) (u := u) (y := t • u) (sgn := fun x => x < 0)
    (by simpa using hu.symm) (t1 := 1 - t) (t2 := t) (by simp) (by ring)
    (by simpa using ht)

/-- `affGt ∅ S ⊆ affGt {0} S` when `0 ∉ S`. -/
theorem w16_affGt_empty_subset {S : Set V3} (h0S : (0:V3) ∉ S) :
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

/-! ## §4 cross / triple product kit -/

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


/-! ## §5 wrap-corner exclusion (HOL MONO_AZIM_AS_BTA_I, `vb - va = -π` branch) -/

/-- HOL `MONO_AZIM_AS_BTA_I` wrap corner is impossible: no consecutive orbit
pair has azimuths `(π, 0)` around the axis `(0, v0)` from the reference `vv 1`.
KCHMAMG / `SEQUENCE_OF_RHO_NODE_IS_SUC` branch of local_lemmas.hl:6740-6927. -/
theorem w16_noWrap {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v0 : V3} {vv : ℕ → V3} {k i : ℕ}
    (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
    (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ n, (rhoNode1 FF)^[n] v0 = vv n)
    (hi : i + 1 < k) :
    ¬(azim 0 v0 (vv 1) (vv i) = Real.pi ∧ azim 0 v0 (vv 1) (vv (i + 1)) = 0) := by
  intro ⟨hva, hvb⟩
  have hlf2 : localFan_p2 V E FF := w16_lf2 h.1
  have hclf2 : convexLocalFan_p2 V E FF := w15_clf2 h
  have hmemV : ∀ n, (rhoNode1 FF)^[n] v0 ∈ V := LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv0
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
    have h2' : (rhoNode1 FF)^[1] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
    rw [hiter 1, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnei : vv i ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 i (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1 FF)^[i] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
    rw [hiter i, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnei1 : vv (i + 1) ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 (i + 1) (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1 FF)^[i + 1] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
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
  have hrn : rhoNode1 FF (vv i) = vv (i + 1) := by
    rw [← hiter (i + 1), show i + 1 = Nat.succ i from rfl,
      Function.iterate_succ_apply', hiter i]
  have hFFi : (vv i, vv (i + 1)) ∈ FF := by
    have h1 : (vv i, rhoNode1_p2 FF (vv i)) ∈ FF :=
      (LOCAL_FAN_RHO_NODE_PROS2 hclf2.1).2 (vv i) (hmemvv i)
    have h2 : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
      show rhoNode1 FF (vv i) = vv (i + 1)
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
    have hnc2' : ¬ Collinear ℝ ({0, vv i, rhoNode1 FF (vv i)} : Set V3) := hnc2
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
    have hUsub : ({(rhoNode1 FF)^[n] v0 | n ≤ i + 1} : Set V3) ⊆ A := by
      rintro z ⟨n, hn, rfl⟩
      exact hAsub (hmemV n)
    have hseq := SEQUENCE_OF_RHO_NODE_IS_SUC (h := hclf2.1) (v := v0) (hv := hv0)
      (l := i + 1) (U := {(rhoNode1 FF)^[n] v0 | n ≤ i + 1}) (P := A)
      rfl hAplane hA0 hUsub (e := cross3 v0 (rhoNode1 FF v0)) rfl
    have hyU : v0 ∈ ({(rhoNode1 FF)^[n] v0 | n ≤ i + 1} : Set V3) :=
      ⟨0, by omega, by simp⟩
    have hstrict := hseq (vv i) i (hiter i).symm (by omega) v0 hyU hnei.symm
      (by
        show v0 ≠ rhoNode1 FF (vv i)
        rw [hrn]
        exact hnei1.symm)
    -- rewrite the reference e = v0 × vv 1
    have he1 : rhoNode1 FF v0 = vv 1 := by
      rw [← hiter 1, show (1:ℕ) = Nat.succ 0 from rfl,
        Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [he1] at hstrict
    have hrn2 : rhoNode1_p2 FF (vv i) = vv (i + 1) := by
      show rhoNode1 FF (vv i) = vv (i + 1)
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


/-! ## §6 unconditional MONO_AZIM_AS_BTA_I -/

/-- HOL `MONO_AZIM_AS_BTA_I` (local_lemmas.hl:6448), **unconditional form**:
the orbit-window azimuth sequence is monotone.  The per-step trig is the
LA35 `monoStepOrbit_p35` disjunction; its wrap corner `(π, 0)` is killed by
`w16_noWrap`. -/
theorem MONO_AZIM_AS_BTA_I {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
    (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ i, (rhoNode1 FF)^[i] v0 = vv i)
    (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i) :
    ∀ i j, i < j → j < k → bta i ≤ bta j := by
  intro i j hij hjk
  have hlf2 : localFan_p2 V E FF := w16_lf2 h.1
  have hclf2 : convexLocalFan_p2 V E FF := w15_clf2 h
  have hmemvv : ∀ n, vv n ∈ V := fun n => by
    rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv0 n
  obtain ⟨-, -, -, -, -, hfan, -, -⟩ := hlf2
  have hv0ne : v0 ≠ 0 := FAN_IMP_V_DIFF hfan v0 hv0
  have hvv0 : vv 0 = v0 := (hiter 0).symm
  have hr0 : rhoNode1_p2 FF v0 = vv 1 := by
    show rhoNode1 FF v0 = vv 1
    rw [← hiter 1, show (1:ℕ) = Nat.succ 0 from rfl,
      Function.iterate_succ_apply', Function.iterate_zero_apply]
  have hne1 : vv 1 ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 1 (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1 FF)^[1] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
    rw [hiter 1, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hb : ¬ Collinear3 0 v0 (vv 1) := hcol (vv 1) (hmemvv 1) hne1
  have hvx : ∀ m, 0 < m → m < k → ¬ Collinear3 0 v0 (vv m) := by
    intro m hm0 hmk
    refine hcol (vv m) (hmemvv m) ?_
    have h2 := LOFA_IMP_DIS_ELMS23 hclf2.1 hv0 0 m hm0 (by rw [hk]; exact hmk)
    have h2' : (rhoNode1 FF)^[m] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
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
    have hrn : rhoNode1 FF (vv m) = vv (m + 1) := by
      rw [← hiter (m + 1), show m + 1 = Nat.succ m from rfl,
        Function.iterate_succ_apply', hiter m]
    have hnc := LOCAL_FAN_CHARACTER_OF_RHO_NODE2 hclf2.1 (v := vv m) (hmemvv m)
    have hnc' : ¬ Collinear ℝ ({0, vv m, rhoNode1 FF (vv m)} : Set V3) := hnc
    rw [hrn] at hnc'
    refine ⟨hnc', azim_nonneg _ _ _ _, ?_⟩
    have h1 := IN_V_IMP_AZIM_LESS_PI hclf2 (vv m) (hmemvv m) v0 hv0
    have h1' : azim 0 (vv m) (rhoNode1 FF (vv m)) v0 ≤ Real.pi := h1
    rwa [hrn] at h1'
  have hnowrap : ∀ m, m + 1 < k →
      ¬(azim 0 v0 (vv 1) (vv m) = Real.pi ∧ azim 0 v0 (vv 1) (vv (m + 1)) = 0) :=
    fun m hmk => w16_noWrap h hv0 hk hcol hiter hmk
  have hmono := monoWindowNowrap_p35 (k := k) (v0 := v0) (b := vv 1) (ρ := vv)
    hvv0 hv0ne hb hvx hvx0 hbnds hdart hnowrap hij hjk
  rw [← hbta i, ← hbta j]
  exact hmono

/-! ## §7 EGHNAVX (local_lemmas.hl:7170) -/

/-- HOL `EGHNAVX` (local_lemmas.hl:7170): the five-conjunct orbit-ordering
package. -/
theorem EGHNAVX {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (h : ConvexLocalFan V E FF) (hv0 : v0 ∈ V) (hk : V.ncard = k)
    (hcol : ∀ v ∈ V, v ≠ v0 → ¬ Collinear ℝ ({0, v0, v} : Set V3))
    (hiter : ∀ i, (rhoNode1 FF)^[i] v0 = vv i)
    (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i) :
    bta 1 = 0 ∧ bta (k - 1) ≤ Real.pi ∧
    (∀ i j, i < j → j < k → bta i ≤ bta j) ∧
    (∀ i, (bta i = 0 ∧ i < k →
        (∀ j, 0 < j ∧ j < i → interiorAngle1 0 FF (vv j) = Real.pi) ∧
        ({z : V3 | ∃ n, 0 < n ∧ n ≤ i ∧ vv n = z} ⊆
          affGt ({0, v0} : Set V3) ({vv 1} : Set V3))) ∧
      (bta i = bta (k - 1) ∧ 0 < i ∧ i < k - 1 →
        (∀ j, i < j ∧ j < k → interiorAngle1 0 FF (vv j) = Real.pi) ∧
        ({z : V3 | ∃ n, i ≤ n ∧ n < k ∧ vv n = z} ⊆
          affGt ({0, v0} : Set V3) ({vv (k - 1)})))) := by
  have hlf2 : localFan_p2 V E FF := w16_lf2 h.1
  have hclf2 : convexLocalFan_p2 V E FF := w15_clf2 h
  have hmemvv : ∀ n, vv n ∈ V := fun n => by
    rw [← hiter n]; exact LOCAL_FAN_ITER_RHO_NODE_IN_V hlf2 hv0 n
  have hvv0 : vv 0 = v0 := (hiter 0).symm
  obtain ⟨hfirst, hlast⟩ := FIRST_EQ0_LAST_LT_PI hclf2 hv0 hk hiter hbta
  have hmono := MONO_AZIM_AS_BTA_I h hv0 hk hcol hiter hbta
  obtain ⟨hfan, x0, hx0, hFF0, hD0, h2reg⟩ := h.1
  -- the fan has at least two vertices, hence `1 < k`
  have hk2 : 1 < k := by
    rw [← hk]
    have hVfin : V.Finite := hfan.2.2.1.1
    have hVne : V ≠ ∅ := hfan.2.2.1.2
    rcases Nat.lt_or_ge V.ncard 2 with hlt | hge
    · exfalso
      rcases Nat.eq_zero_or_pos V.ncard with h0 | h0
      · rw [Set.ncard_eq_zero hVfin] at h0
        exact hVne h0
      · have h1 : V.ncard = 1 := by omega
        obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
        exact LOCAL_FAN_NOT_V_SING hlf2 ⟨v, hv⟩
    · omega
  have hne1 : vv 1 ≠ v0 := by
    have h2 := LOFA_IMP_DIS_ELMS23 hlf2 hv0 0 1 (by omega) (by rw [hk]; omega)
    have h2' : (rhoNode1 FF)^[1] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
    rw [hiter 1, hiter 0] at h2'
    exact fun hc => h2' (hc.trans hvv0.symm)
  have hnc1 : ¬ Collinear3 0 v0 (vv 1) := hcol (vv 1) (hmemvv 1) hne1
  refine ⟨hfirst, hlast, hmono, ?_⟩
  intro i
  constructor
  · -- conjunct 4
    intro ⟨hbi, hik⟩
    have hsub4 : ({z : V3 | ∃ n, 0 < n ∧ n ≤ i ∧ vv n = z} : Set V3) ⊆
        affGt ({0, v0} : Set V3) ({vv 1} : Set V3) := by
      rintro z ⟨n, hn0, hni, rfl⟩
      have hbn : bta n = 0 := by
        rcases lt_or_eq_of_le hni with hlt | heq
        · have h1 := hmono n i hlt hik
          have h2 : 0 ≤ bta n := by rw [← hbta n]; exact azim_nonneg _ _ _ _
          linarith
        · rw [heq]; exact hbi
      have haz : azim 0 v0 (vv 1) (vv n) = 0 := by rw [hbta n]; exact hbn
      have hncn : ¬ Collinear3 0 v0 (vv n) := by
        refine hcol (vv n) (hmemvv n) ?_
        have h2 := LOFA_IMP_DIS_ELMS23 hlf2 hv0 0 n hn0 (by rw [hk]; omega)
        have h2' : (rhoNode1 FF)^[n] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
        rw [hiter n, hiter 0] at h2'
        exact fun hc => h2' (hc.trans hvv0.symm)
      exact (azim_eq_zero_iff_alt (v0 := 0) (v1 := v0) (w := vv 1) (x := vv n)
        hnc1 hncn).mp haz
    constructor
    · intro j ⟨hj0, hji⟩
      have hplane : plane_p2 (affineSpan ℝ ({0, v0, vv 1} : Set V3)) :=
        ⟨0, v0, vv 1, hnc1, rfl⟩
      have h0mem : (0:V3) ∈ (affineSpan ℝ ({0, v0, vv 1} : Set V3) : Set V3) :=
        mem_affineSpan ℝ (by simp)
      have hUsub : ({z : V3 | ∃ n, n ≤ i ∧ vv n = z} : Set V3) ⊆
          (affineSpan ℝ ({0, v0, vv 1} : Set V3) : Set V3) := by
        rintro z ⟨n, hni, rfl⟩
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0, hvv0]; exact mem_affineSpan ℝ (by simp)
        · have hmem := hsub4 ⟨n, hpos, hni, rfl⟩
          have h1 := AFF_GT_SUBSET_AFFINE_HULL ({0, v0} : Set V3) ({vv 1} : Set V3) hmem
          have hset : (({0, v0} : Set V3) ∪ {vv 1}) = ({0, v0, vv 1} : Set V3) := by
            ext w
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
            tauto
          rwa [hset] at h1
      have hUeq : ({(rhoNode1 FF)^[n] v0 | n ≤ i} : Set V3) =
          {z : V3 | ∃ n, n ≤ i ∧ vv n = z} := by
        ext z
        constructor
        · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, (hiter n).symm⟩
        · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, hiter n⟩
      have hang := CNVX_IMP_INTERIOR_ANGLE_PI h hv0 hUeq hplane h0mem hUsub
      have hj := hang j hj0 hji
      rwa [hiter j] at hj
    · exact hsub4
  · -- conjunct 5
    intro ⟨hbi, hi0, hik⟩
    have hk1pos : 0 < k - 1 := by omega
    have hk1lt : k - 1 < k := by omega
    have hne_k1 : vv (k - 1) ≠ v0 := by
      have h2 := LOFA_IMP_DIS_ELMS23 hlf2 hv0 0 (k - 1) hk1pos (by rw [hk]; exact hk1lt)
      have h2' : (rhoNode1 FF)^[k - 1] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
      rw [hiter (k - 1), hiter 0] at h2'
      exact fun hc => h2' (hc.trans hvv0.symm)
    have hnc_k1 : ¬ Collinear3 0 v0 (vv (k - 1)) := hcol _ (hmemvv _) hne_k1
    have hsub5 : ({z : V3 | ∃ n, i ≤ n ∧ n < k ∧ vv n = z} : Set V3) ⊆
        affGt ({0, v0} : Set V3) ({vv (k - 1)} : Set V3) := by
      rintro z ⟨n, hni, hnk, rfl⟩
      have haz : azim 0 v0 (vv 1) (vv n) = azim 0 v0 (vv 1) (vv (k - 1)) := by
        rcases lt_or_eq_of_le hni with hlt | heq
        · rcases lt_or_eq_of_le (show n ≤ k - 1 from by omega) with hnk' | hnk'
          · have h2 := hmono i n hlt (by omega)
            have h3 := hmono n (k - 1) hnk' hk1lt
            have h4 : bta n = bta (k - 1) := by linarith
            rw [hbta n, hbta (k - 1)]
            exact h4
          · rw [hnk']
        · rw [← heq, hbta i, hbta (k - 1)]
          exact hbi
      have hncn : ¬ Collinear3 0 v0 (vv n) := by
        refine hcol (vv n) (hmemvv n) ?_
        have h2 := LOFA_IMP_DIS_ELMS23 hlf2 hv0 0 n (by omega) (by rw [hk]; omega)
        have h2' : (rhoNode1 FF)^[n] v0 ≠ (rhoNode1 FF)^[0] v0 := h2
        rw [hiter n, hiter 0] at h2'
        exact fun hc => h2' (hc.trans hvv0.symm)
      exact (azim_eq_azim_iff (v0 := 0) (v1 := v0) (w := vv 1) (x := vv (k - 1))
        (y := vv n) hnc1 hnc_k1 hncn).mp haz.symm
    constructor
    · intro j ⟨hij, hjk⟩
      have hplane : plane_p2 (affineSpan ℝ ({0, v0, vv (k - 1)} : Set V3)) :=
        ⟨0, v0, vv (k - 1), hnc_k1, rfl⟩
      have h0mem : (0:V3) ∈ (affineSpan ℝ ({0, v0, vv (k - 1)} : Set V3) : Set V3) :=
        mem_affineSpan ℝ (by simp)
      have hUsub : ({(rhoNode1 FF)^[n] ((rhoNode1 FF)^[i] v0) | n ≤ k - i} : Set V3) ⊆
          (affineSpan ℝ ({0, v0, vv (k - 1)} : Set V3) : Set V3) := by
        rintro z ⟨n, hn, rfl⟩
        have hiter_add : (rhoNode1 FF)^[n] ((rhoNode1 FF)^[i] v0) = vv (i + n) := by
          rw [← Function.iterate_add_apply, show n + i = i + n from by omega,
            hiter (i + n)]
        rw [hiter_add]
        rcases lt_or_eq_of_le (show i + n ≤ k from by omega) with hlt | heq
        · have hmem := hsub5 ⟨i + n, by omega, hlt, rfl⟩
          have h1 := AFF_GT_SUBSET_AFFINE_HULL ({0, v0} : Set V3)
            ({vv (k - 1)} : Set V3) hmem
          have hset : (({0, v0} : Set V3) ∪ {vv (k - 1)}) = ({0, v0, vv (k - 1)} : Set V3) := by
            ext w
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
            tauto
          rwa [hset] at h1
        · have hk_eq : vv (i + n) = v0 := by
            rw [← hiter (i + n), heq, ← hk]
            exact LOFA_IMP_ITER_RHO_NODE_ID hlf2 hv0
          rw [hk_eq]
          exact mem_affineSpan ℝ (by simp)
      have hang := CNVX_IMP_INTERIOR_ANGLE_PI (v := (rhoNode1 FF)^[i] v0) (l := k - i)
        (U := {(rhoNode1 FF)^[n] ((rhoNode1 FF)^[i] v0) | n ≤ k - i})
        h (by rw [hiter i]; exact hmemvv i) rfl hplane h0mem hUsub
      have hj0 : 0 < j - i := by omega
      have hjk' : j - i < k - i := by omega
      have hj := hang (j - i) hj0 hjk'
      rwa [show (rhoNode1 FF)^[j - i] ((rhoNode1 FF)^[i] v0) = vv j from by
        rw [← Function.iterate_add_apply, show j - i + i = j from by omega,
          hiter j]] at hj
    · exact hsub5

/-! ## axiom audit -/
#print axioms CONV02_SU_CONV2
#print axioms AZIM_EQ_PI_ALT
#print axioms w16_affGe_empty_singleton
#print axioms w16_smul_mem_affGe
#print axioms w16_smul_mem_affLt
#print axioms w16_affGt_empty_subset
#print axioms w16_noWrap
#print axioms MONO_AZIM_AS_BTA_I
#print axioms EGHNAVX

/-! ## w17 axiom audit (XIV_DEFORMATION strict form kit) -/
#print axioms w17_pairs_finite
#print axioms w17_triples_finite
#print axioms w17_nc_window
#print axioms w17_continuousAt_dihV_comp
#print axioms w17_dih_window
#print axioms w17_azim_floor
#print axioms w17_azim_floor_window
#print axioms w17_azim_pi_window
#print axioms w17_xiv_deformation_strict

end Kepler.Text
