/-
XivphksKit: the shared XIVPHKS.hl kit (Lemma 7.143 wedge-membership
induction), extracted verbatim from `Kepler.Text.LocalAuto16` Section B
on 2026-11-05 (lane la14-shared-w16) so that modules on the
LocalAuto14 side (which cannot import LocalAuto16: LocalAuto16 →
LocalAuto27 → LocalAuto14) can consume it without an import cycle.

Contents (all names unchanged, `_p16` suffix kept for downstream
compatibility):
  - sine-of-azimuth algebra kit: `w13_cross3_*`, `w13_dot3_*`,
    `w13_exists_smul_of_collinear3_zero`,
    `w13_cross3_eq_zero_of_collinear3_zero`,
    `w13_triple_eq_zero_of_collinear3_zero_{left,right}`,
    `w13_triple_cyclic`, `w13_cexp_{cos_re,sin_im}`,
    `w13_sin_azim_eq_pos_mul_triple`, `w13_sin_pos_iff_triple_pos`,
    `w13_sin_neg_iff_triple_neg`, `w13_fsqkwkk_origin`;
  - `FSQKWKK_p16` (HOL `FSQKWKK`, Lemma 7.141);
  - `XIVPHKS_p16` (HOL `XIVPHKS`, Lemma 7.143);
  - `XIVPHKS_SHIFT_p16` (HOL `XIVPHKS_SHIFT`).

Import face (acyclic): LocalAuto5 (`AZIM_SPEC_DEGENERATE`),
LocalAuto7 (`AZIM_DIHV_SAME_STRONG`), TopologyFan
(`sum3/4/5_azim_fan`), Geom.Aff/Geom.Azim (`wedgeGe`, `azim_*`,
`collinear3_of_eq`), Mathlib.  None of these imports
LocalAuto14/16/27 (verified by transitive-import scan), so both
LocalAuto14 and LocalAuto16 may import this module.
-/

import Kepler.Text.LocalAuto5
import Kepler.Text.LocalAuto7
import Kepler.Text.TopologyFan
import Kepler.Geom.Aff
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

/-! ## Section B: XIVPHKS.hl (wedge-membership induction, Lemma 7.143) -/




open Kepler.Geom Set Classical

/-! ## w13 provisional kit: cross3 algebra -/

private theorem w13_cross3_add_left (a b c : V3) :
    cross3 (a + b) c = cross3 a c + cross3 b c := by
  apply WithLp.ofLp_injective
  simp [cross3, map_add]

private theorem w13_cross3_add_right (a b c : V3) :
    cross3 a (b + c) = cross3 a b + cross3 a c := by
  apply WithLp.ofLp_injective
  simp [cross3, map_add]

private theorem w13_cross3_smul_left (t : ℝ) (a b : V3) :
    cross3 (t • a) b = t • cross3 a b := by
  apply WithLp.ofLp_injective
  simp [cross3, map_smul]

private theorem w13_cross3_smul_right (t : ℝ) (a b : V3) :
    cross3 a (t • b) = t • cross3 a b := by
  apply WithLp.ofLp_injective
  simp [cross3, map_smul]

private theorem w13_cross3_self (a : V3) : cross3 a a = 0 := by
  apply WithLp.ofLp_injective
  simp [cross3, cross_self]

private theorem w13_cross3_neg_left (a b : V3) : cross3 (-a) b = -cross3 a b := by
  simpa using w13_cross3_smul_left (-1) a b

private theorem w13_cross3_anticomm (a b : V3) : cross3 b a = -cross3 a b := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_neg]
  exact (cross_anticomm ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ)).symm

private theorem w13_cross3_cross3 (u v w : V3) :
    cross3 (cross3 u v) w = (u ⬝ᵥ w) • v - (v ⬝ᵥ w) • u := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [cross_cross_eq_smul_sub_smul]

private theorem w13_dot3_add_left (x y z : V3) :
    (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z :=
  add_dotProduct _ _ _

private theorem w13_dot3_add_right (x y z : V3) :
    z ⬝ᵥ (x + y) = z ⬝ᵥ x + z ⬝ᵥ y :=
  dotProduct_add _ _ _

private theorem w13_dot3_smul_left (t : ℝ) (x z : V3) :
    (t • x) ⬝ᵥ z = t * (x ⬝ᵥ z) :=
  smul_dotProduct _ _ _

private theorem w13_dot3_smul_right (t : ℝ) (x z : V3) :
    z ⬝ᵥ (t • x) = t * (z ⬝ᵥ x) :=
  dotProduct_smul _ _ _

private theorem w13_dot3_comm (x y : V3) : x ⬝ᵥ y = y ⬝ᵥ x :=
  dotProduct_comm _ _

private theorem w13_dot3_sub_left (x y z : V3) :
    (x - y) ⬝ᵥ z = x ⬝ᵥ z - y ⬝ᵥ z :=
  sub_dotProduct _ _ _

private theorem w13_cross3_dot_self_left (a b : V3) : cross3 a b ⬝ᵥ a = 0 := by
  rw [w13_dot3_comm]
  exact dot_self_cross ((a : V3) : Fin 3 → ℝ) ((b : V3) : Fin 3 → ℝ)

private theorem w13_exists_smul_of_collinear3_zero {a b : V3}
    (h : Collinear3 0 a b) : ∃ (z : V3) (sa sb : ℝ),
      a = sa • z ∧ b = sb • z := by
  have h0 : (0:V3) ∈ ({0, a, b} : Set V3) := by simp
  obtain ⟨z, hz⟩ := (collinear_iff_of_mem (k := ℝ) h0).mp h
  obtain ⟨sa, ha⟩ := hz a (by simp)
  obtain ⟨sb, hb⟩ := hz b (by simp)
  exact ⟨z, sa, sb, by simpa using ha, by simpa using hb⟩

private theorem w13_cross3_eq_zero_of_collinear3_zero {a b : V3}
    (h : Collinear3 0 a b) : cross3 a b = 0 := by
  obtain ⟨z, sa, sb, ha, hb⟩ := w13_exists_smul_of_collinear3_zero h
  rw [ha, hb, w13_cross3_smul_left, w13_cross3_smul_right, w13_cross3_self]
  simp

private theorem w13_triple_eq_zero_of_collinear3_zero_left {u v w : V3}
    (h : Collinear3 0 u v) : (cross3 u v) ⬝ᵥ w = 0 := by
  rw [w13_cross3_eq_zero_of_collinear3_zero h]
  simp

private theorem w13_triple_cyclic (a b c : V3) :
    (cross3 a b) ⬝ᵥ c = (cross3 c a) ⬝ᵥ b := by
  rw [show (cross3 a b) ⬝ᵥ c
        = ((cross3 a b : V3) : Fin 3 → ℝ) ⬝ᵥ ((c:V3) : Fin 3 → ℝ) from rfl,
      show (cross3 c a) ⬝ᵥ b
        = ((cross3 c a : V3) : Fin 3 → ℝ) ⬝ᵥ ((b:V3) : Fin 3 → ℝ) from rfl]
  simp only [cross3, WithLp.ofLp_toLp]
  rw [dotProduct_comm (crossProduct ((a:V3):Fin 3 → ℝ) ((b:V3):Fin 3 → ℝ)) ((c:V3):Fin 3 → ℝ),
    triple_product_permutation ((c:V3):Fin 3 → ℝ) ((a:V3):Fin 3 → ℝ) ((b:V3):Fin 3 → ℝ),
    triple_product_permutation ((a:V3):Fin 3 → ℝ) ((b:V3):Fin 3 → ℝ) ((c:V3):Fin 3 → ℝ),
    dotProduct_comm ((b:V3):Fin 3 → ℝ) (crossProduct ((c:V3):Fin 3 → ℝ) ((a:V3):Fin 3 → ℝ))]

private theorem w13_triple_eq_zero_of_collinear3_zero_right {u v w : V3}
    (h : Collinear3 0 u w) : (cross3 u v) ⬝ᵥ w = 0 := by
  rw [w13_triple_cyclic u v w]
  exact w13_triple_eq_zero_of_collinear3_zero_left (u := w) (v := u) (w := v)
    (by
      have hset : ({0, w, u} : Set V3) = {0, u, w} := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [Collinear3, hset]
      exact h)

/-! ## sine-of-azim sign -/

private theorem w13_cexp_cos_re (r : ℝ) :
    (Complex.exp ((r : ℂ) * Complex.I)).re = Real.cos r := by
  have h := congrArg Complex.re (Complex.exp_mul_I (r : ℂ))
  simpa using h

private theorem w13_cexp_sin_im (r : ℝ) :
    (Complex.exp ((r : ℂ) * Complex.I)).im = Real.sin r := by
  have h := congrArg Complex.im (Complex.exp_mul_I (r : ℂ))
  simpa using h

private theorem w13_sin_azim_eq_pos_mul_triple (u v w : V3) :
    ∃ c : ℝ, 0 < c ∧ Real.sin (azim 0 u v w) = c * ((cross3 u v) ⬝ᵥ w) := by
  by_cases hdeg : Collinear3 0 u v ∨ Collinear3 0 u w
  · refine ⟨1, one_pos, ?_⟩
    rw [azim, if_pos hdeg, Real.sin_zero, one_mul]
    symm
    rcases hdeg with h | h
    · exact w13_triple_eq_zero_of_collinear3_zero_left h
    · exact w13_triple_eq_zero_of_collinear3_zero_right h
  · push_neg at hdeg
    obtain ⟨h1, h2⟩ := hdeg
    set θ : ℝ := azim 0 u v w with hθdef
    have hu : u ≠ 0 := by
      intro h0
      exact h1 (by rw [h0]; exact collinear3_of_eq (by simp))
    -- frame
    obtain ⟨e1, e2, e3, hon, hualign⟩ := exists_on3_eq_smul u hu
    have hax : (u - 0 : V3) = dist u 0 • e3 := by
      simpa only [sub_zero, dist_eq_norm] using hualign
    have honk := hon
    obtain ⟨hon1, hon2, hon3, hon12, hon13, hon23, -⟩ := honk
    have hon21 : e2 ⬝ᵥ e1 = 0 := by rw [w13_dot3_comm, hon12]
    have hon31 : e3 ⬝ᵥ e1 = 0 := by rw [w13_dot3_comm, hon13]
    have hon32 : e3 ⬝ᵥ e2 = 0 := by rw [w13_dot3_comm, hon23]
    obtain ⟨psi, r1, r2, hr1, hr2, hz1, hz2⟩ :=
      azim_frame_spec (v := (0:V3)) (w := u) (w1 := v) (w2 := w) h1 h2 hon hax hu
    rw [← hθdef] at hz2
    -- component readings
    have hv1 : v ⬝ᵥ e1 = r1 * Real.cos psi := by
      have h := congrArg Complex.re hz1
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one] at h
      rw [w13_cexp_cos_re] at h
      exact h
    have hv2 : v ⬝ᵥ e2 = r1 * Real.sin psi := by
      have h := congrArg Complex.im hz1
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
        zero_add, mul_one] at h
      rw [w13_cexp_sin_im] at h
      simpa only [sub_zero] using h
    have hw1 : w ⬝ᵥ e1 = r2 * Real.cos (psi + θ) := by
      have h := congrArg Complex.re hz2
      simp only [zOf, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one] at h
      rw [w13_cexp_cos_re] at h
      exact h
    have hw2 : w ⬝ᵥ e2 = r2 * Real.sin (psi + θ) := by
      have h := congrArg Complex.im hz2
      simp only [zOf, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero,
        zero_add, mul_one] at h
      rw [w13_cexp_sin_im] at h
      simpa only [sub_zero] using h
    -- cross table
    have he1e2 : cross3 e1 e2 = e3 := by
      simp only [cross3, WithLp.ofLp_toLp]
      rw [on3_cross hon, WithLp.toLp_ofLp]
    have he3e1 : cross3 e3 e1 = e2 := by
      have h := w13_cross3_cross3 e1 e2 e1
      rw [he1e2] at h
      simpa [hon1, hon21] using h
    have he3e2 : cross3 e3 e2 = -e1 := by
      have h21 : cross3 e2 e1 = -e3 := by
        rw [w13_cross3_anticomm, he1e2]
      have h := w13_cross3_cross3 e2 e1 e2
      rw [h21] at h
      rw [w13_cross3_neg_left] at h
      have h' : -cross3 e3 e2 = e1 := by simpa [hon2, hon12] using h
      simpa using congrArg Neg.neg h'
    have hcross : cross3 u v = ‖u‖ • ((r1 * Real.cos psi) • e2 - (r1 * Real.sin psi) • e1) := by
      conv_lhs => rw [hualign]
      rw [on3_expand hon v, hv1, hv2]
      rw [w13_cross3_smul_left]
      congr 1
      rw [w13_cross3_add_right, w13_cross3_add_right]
      rw [w13_cross3_smul_right, w13_cross3_smul_right, w13_cross3_smul_right]
      rw [he3e1, he3e2, w13_cross3_self]
      module
    have hdot : (cross3 u v) ⬝ᵥ w =
        ‖u‖ * (r1 * Real.cos psi * (r2 * Real.sin (psi + θ)) -
          r1 * Real.sin psi * (r2 * Real.cos (psi + θ))) := by
      rw [hcross, on3_expand hon w, hw1, hw2]
      simp only [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_add,
        smul_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_smul,
        hon1, hon2, hon3, hon12, hon21, hon13, hon31, hon23, hon32,
        mul_zero, mul_one, add_zero, zero_add]
      ring
    have htrig : r1 * Real.cos psi * (r2 * Real.sin (psi + θ)) -
        r1 * Real.sin psi * (r2 * Real.cos (psi + θ)) =
        r1 * r2 * Real.sin θ := by
      have hs := Real.sin_sub (psi + θ) psi
      rw [show psi + θ - psi = θ by ring] at hs
      rw [hs]
      ring
    refine ⟨1 / (‖u‖ * r1 * r2), ?_, ?_⟩
    · have : 0 < ‖u‖ * r1 * r2 := by positivity
      exact one_div_pos.mpr this
    · rw [hdot, htrig]
      have hp : ‖u‖ * r1 * r2 ≠ 0 := by positivity
      field_simp



private theorem w13_sin_pos_iff_triple_pos (u v w : V3) :
    0 < Real.sin (azim 0 u v w) ↔ 0 < (cross3 u v) ⬝ᵥ w := by
  obtain ⟨c, hc, he⟩ := w13_sin_azim_eq_pos_mul_triple u v w
  rw [he]
  exact mul_pos_iff_of_pos_left hc

private theorem w13_sin_neg_iff_triple_neg (u v w : V3) :
    Real.sin (azim 0 u v w) < 0 ↔ (cross3 u v) ⬝ᵥ w < 0 := by
  obtain ⟨c, hc, he⟩ := w13_sin_azim_eq_pos_mul_triple u v w
  rw [he]
  have h := mul_lt_mul_iff_of_pos_left (a := c) (b := (cross3 u v) ⬝ᵥ w) (c := 0) hc
  simpa using h

private theorem w13_fsqkwkk_origin (v1 v2 v3 : V3) (h : azim 0 v1 v2 v3 ≤ Real.pi) :
    azim 0 v2 v3 v1 ≤ Real.pi := by
  by_cases h1 : v1 = 0
  · have hz : azim 0 v2 v3 v1 = 0 := by
      rw [azim, if_pos]
      right
      have hc : Collinear3 0 v2 0 :=
        collinear3_pair_left (v0 := (0:V3)) (v1 := v2) (x := 0) rfl
      simpa [h1] using hc
    rw [hz]
    exact Real.pi_pos.le
  by_cases h2 : v2 = 0
  · have hz : azim 0 v2 v3 v1 = 0 := by
      rw [azim, if_pos]
      left
      have hc : Collinear3 0 v3 0 :=
        collinear3_pair_left (v0 := (0:V3)) (v1 := v3) (x := 0) rfl
      simpa [h2, Collinear3, Set.insert_comm, Set.pair_comm] using hc
    rw [hz]
    exact Real.pi_pos.le
  by_cases h3 : v3 = 0
  · have hz : azim 0 v2 v3 v1 = 0 := by
      rw [azim, if_pos]
      left
      have hc : Collinear3 0 v2 0 :=
        collinear3_pair_left (v0 := (0:V3)) (v1 := v2) (x := 0) rfl
      simpa [h3] using hc
    rw [hz]
    exact Real.pi_pos.le
  have hsin1 : 0 ≤ Real.sin (azim 0 v1 v2 v3) := by
    by_contra hc
    have hlt : Real.sin (azim 0 v1 v2 v3) < 0 := lt_of_not_ge hc
    have hpi := (SIN_AZIM_NEG_PI_LT 0 v1 v2 v3).mp hlt
    linarith
  have htriple1 : 0 ≤ (cross3 v1 v2) ⬝ᵥ v3 := by
    by_contra hc
    have hlt : (cross3 v1 v2) ⬝ᵥ v3 < 0 := lt_of_not_ge hc
    have hs := (w13_sin_neg_iff_triple_neg v1 v2 v3).mpr hlt
    linarith
  have hcyc : (cross3 v2 v3) ⬝ᵥ v1 = (cross3 v1 v2) ⬝ᵥ v3 :=
    w13_triple_cyclic v2 v3 v1
  have hsin2 : 0 ≤ Real.sin (azim 0 v2 v3 v1) := by
    by_contra hc
    have hlt : Real.sin (azim 0 v2 v3 v1) < 0 := lt_of_not_ge hc
    have hs := (w13_sin_neg_iff_triple_neg v2 v3 v1).mp hlt
    rw [hcyc] at hs
    linarith
  by_contra hc
  push Not at hc
  have hs := (SIN_AZIM_NEG_PI_LT 0 v2 v3 v1).mpr hc
  linarith



/-- HOL `FSQKWKK` (XIVPHKS.hl:17, Lemma 7.141): azimuth-permutation for
the cyclic triple.  Proved from the sine-of-azim sign kit above; the
origin form `w13_fsqkwkk_origin` is translated with `azim_sub_self`. -/
theorem FSQKWKK_p16 (v0 v1 v2 v3 : V3) (h : azim v0 v1 v2 v3 ≤ Real.pi) :
    azim v0 v2 v3 v1 ≤ Real.pi := by
  rw [azim_sub_self v0 v1 v2 v3] at h
  rw [azim_sub_self v0 v2 v3 v1]
  exact w13_fsqkwkk_origin (v1 - v0) (v2 - v0) (v3 - v0) h

/-- HOL `XIVPHKS` (XIVPHKS.hl:29, Lemma 7.143): under the local
non-collinearity, small-diagonal (`< e`) and ear-angle (`2e < a ≤ π`)
hypotheses, consecutive wedges absorb the whole chain in both
directions.  HOL `n - 1 = r` kept verbatim (ℕ truncated subtraction).
Proved by the source induction: `wedgeGe` unfolding with
`AZIM_SPEC_DEGENERATE` / `azim_self` at the degenerate indices,
`AZIM_DIHV_SAME_STRONG`, `FSQKWKK_p16`, and Fan `sum3/4/5_azim_fan`
(all non-collinearity from `hpair`). -/
theorem XIVPHKS_p16 (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ) (n r : ℕ)
    (w : ℕ → V3) (hn : 1 ≤ n) (hr : n - 1 = r)
    (hpair : (Set.Icc (0:ℕ) n).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hd : (fun i j k => dihV 0 (w i) (w j) (w k)) = d)
    (ha : (fun i j k => azim 0 (w i) (w j) (w k)) = a)
    (hW : (fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))) = W)
    (he : 0 < 2 * e)
    (h1 : ∀ i ∈ Finset.Icc 1 r, 2 * e < a i (i + 1) (i - 1))
    (h2 : ∀ i ∈ Finset.Icc 1 r, a i (i + 1) (i - 1) ≤ Real.pi)
    (h3 : ∀ p q, ({p, q, q + 1} : Finset ℕ) ⊆ Finset.Icc 0 r → p ≠ q →
      p ≠ q + 1 → d p q (q + 1) < e)
    (h4 : ∀ p q, ({p, p + 1, q} : Finset ℕ) ⊆ Finset.Icc 0 r → q > p + 1 →
      d p (p + 1) q < e)
    (h5 : ∀ p q, ({p + 1, p, q} : Finset ℕ) ⊆ Finset.Icc 0 r → q < p →
      d (p + 1) p q < e) :
    (∀ k j, j + k ≤ r → w j ∈ W (j + k)) ∧
    (∀ k j, 1 ≤ j → j + k ≤ r → w (j + k) ∈ W j) := by
  subst W
  subst a
  subst d
  dsimp only at h1 h2 h3 h4 h5
  let F : ℕ → Set V3 := fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))
  have hrn : r + 1 = n := by omega
  have hnc : ∀ p q, p ≤ r + 1 → q ≤ r + 1 → p ≠ q → ¬ Collinear3 0 (w p) (w q) := by
    intro p q hp hq hpne
    exact hpair (by simp only [Set.mem_Icc]; omega)
      (by simp only [Set.mem_Icc]; omega) hpne
  have hne0 : ∀ p, p ≤ r → w p ≠ 0 := by
    intro p hp h0
    exact hnc p (p + 1) (by omega) (by omega) (by omega)
      (by simpa [h0] using
        collinear3_of_eq (v := (0:V3)) (w := (0:V3)) (w1 := w (p + 1)) rfl)
  have main : ∀ k, ∀ j, j + k ≤ r →
      w j ∈ F (j + k) ∧ (1 ≤ j → w (j + k) ∈ F j) := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hdeg := AZIM_SPEC_DEGENERATE (0:V3) (w j) (w (j + 1))
        have hmem : w j ∈ F j := by
          refine ⟨?_, ?_⟩
          · rw [hdeg.2]
          · rw [hdeg.2]; exact azim_nonneg _ _ _ _
        exact ⟨hmem, fun _ => hmem⟩
    | succ k ih =>
        by_cases hk : k = 0
        · subst k
          intro j hj
          have hm1 : w j ∈ F (j + 1) := by
            refine ⟨azim_nonneg _ _ _ _, ?_⟩
            simp
          have hm2 : w (j + 1) ∈ F j := by
            refine ⟨?_, ?_⟩
            · rw [azim_self]
            · rw [azim_self]; exact azim_nonneg _ _ _ _
          exact ⟨hm1, fun _ => hm2⟩
        · have hk1 : 1 ≤ k := by omega
          intro j hj
          change w j ∈ F (j + k + 1) ∧ (1 ≤ j → w (j + k + 1) ∈ F j)
          have hjk : j + k ≤ r := by omega
          have hjr : j ≤ r := by omega
          obtain ⟨hA, hB⟩ := ih j hjk
          have hA' : w j ∈ wedgeGe 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) := by
            simpa [F] using hA
          have he' : 0 < e := by linarith
          have h2eπ : 2 * e < 2 * Real.pi := by
            have hlt := h1 1 (by simp only [Finset.mem_Icc]; omega)
            have hle := h2 1 (by simp only [Finset.mem_Icc]; omega)
            have hlt2 := azim_lt_two_pi 0 (w 1) (w (1 + 1)) (w (1 - 1))
            linarith
          constructor
          · -- direction 1: w j ∈ F (j + k + 1)
            obtain ⟨hA2, hB2⟩ := ih (j + 1) (by omega)
            have hshift : (j + 1) + k = j + k + 1 := by omega
            rw [hshift] at hA2
            have hA2' : w (j + 1) ∈
                wedgeGe 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              simpa [F] using hA2
            have hB2' : w (j + k + 1) ∈
                wedgeGe 0 (w (j + 1)) (w (j + 2)) (w j) := by
              have h := hB2 (by omega)
              rw [hshift] at h
              simpa [F] using h
            have hA2j : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := hA2'.2
            have hB2j : azim 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1)) ≤
                azim 0 (w (j + 1)) (w (j + 2)) (w j) := hB2'.2
            have hsum4a : azim 0 (w (j + 1)) (w (j + 2)) (w j) =
                azim 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1)) +
                azim 0 (w (j + 1)) (w (j + k + 1)) (w j) := by
              refine sum4_azim_fan (x := 0) (v := w (j + 1)) (u := w (j + 2))
                (w1 := w (j + k + 1)) (w2 := w j)
                (hne0 (j + 1) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + 1) (j + 2) (by omega) (by omega) (by omega)
              · exact hnc (j + 1) (j + k + 1) (by omega) (by omega) (by omega)
              · exact hnc (j + 1) j (by omega) (by omega) (by omega)
              · exact hB2j
            have hle1 : azim 0 (w (j + 1)) (w (j + k + 1)) (w j) ≤
                azim 0 (w (j + 1)) (w (j + 2)) (w j) := by
              rw [hsum4a]
              have hnn := azim_nonneg 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1))
              linarith
            have hpi1 : azim 0 (w (j + 1)) (w (j + 2)) (w j) ≤ Real.pi :=
              h2 (j + 1) (by simp only [Finset.mem_Icc]; omega)
            have hpi2 : azim 0 (w (j + 1)) (w (j + k + 1)) (w j) ≤ Real.pi :=
              le_trans hle1 hpi1
            have hfsq : azim 0 (w (j + k + 1)) (w j) (w (j + 1)) ≤ Real.pi :=
              FSQKWKK_p16 0 (w (j + 1)) (w (j + k + 1)) (w j) hpi2
            have hd5 : azim 0 (w (j + k + 1)) (w j) (w (j + 1)) < e := by
              rw [AZIM_DIHV_SAME_STRONG
                (hnc (j + k + 1) j (by omega) (by omega) (by omega))
                (hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega)) hfsq]
              have hsub : ({j + k + 1, j, j + 1} : Finset ℕ) ⊆ Finset.Icc 0 r := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp only [Finset.mem_Icc]
                omega
              exact h3 (j + k + 1) j hsub (by omega) (by omega)
            have hsum4b : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1)) +
                azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) := by
              refine sum4_azim_fan (x := 0) (v := w (j + k + 1)) (u := w (j + k + 2))
                (w1 := w (j + 1)) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) (j + k + 2) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega)
              · exact hA2j
            have hle2 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              rw [hsum4b]
              have hnn := azim_nonneg 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1))
              linarith
            have hpi3 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) ≤ Real.pi :=
              h2 (j + k + 1) (by simp only [Finset.mem_Icc]; omega)
            have hpi4 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) ≤ Real.pi :=
              le_trans hle2 hpi3
            have hd6 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) < e := by
              by_cases hk1' : k = 1
              · subst k
                rw [azim_self]
                linarith
              · have hk2' : 2 ≤ k := by omega
                rw [AZIM_DIHV_SAME_STRONG
                  (hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega))
                  (hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega)) hpi4]
                have hsub : ({j + k + 1, j + k, j + 1} : Finset ℕ) ⊆ Finset.Icc 0 r := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp only [Finset.mem_Icc]
                  omega
                have h5' := h5 (j + k) (j + 1) hsub (by omega)
                rw [DIHV_SYM_2] at h5'
                exact h5'
            have hsum3b : azim 0 (w (j + k + 1)) (w j) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w j) (w (j + 1)) +
                azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) := by
              refine sum3_azim_fan (x := 0) (v := w (j + k + 1)) (u := w j)
                (w1 := w (j + 1)) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) j (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega)
              · linarith
            have hle3 : azim 0 (w (j + k + 1)) (w j) (w (j + k)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              have h1i : 2 * e < azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) :=
                h1 (j + k + 1) (by simp only [Finset.mem_Icc]; omega)
              rw [hsum3b]
              linarith
            have hsum5 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w j) +
                azim 0 (w (j + k + 1)) (w j) (w (j + k)) := by
              refine sum5_azim_fan (x := 0) (v := w (j + k + 1)) (u := w (j + k + 2))
                (w1 := w j) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) (j + k + 2) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) j (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega)
              · exact hle3
            have hfin2 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w j) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              rw [hsum5]
              have hnn := azim_nonneg 0 (w (j + k + 1)) (w j) (w (j + k))
              linarith
            exact ⟨azim_nonneg _ _ _ _, hfin2⟩
          · -- direction 2: 1 ≤ j → w (j + k + 1) ∈ F j
            intro hj1
            have hB' : w (j + k) ∈ wedgeGe 0 (w j) (w (j + 1)) (w (j - 1)) := by
              simpa [F] using hB hj1
            have hBj : azim 0 (w j) (w (j + 1)) (w (j + k)) ≤
                azim 0 (w j) (w (j + 1)) (w (j - 1)) := hB'.2
            have hAj : azim 0 (w (j + k)) (w (j + k + 1)) (w j) ≤
                azim 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) := hA'.2
            have hpi_k : azim 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) ≤ Real.pi :=
              h2 (j + k) (by simp only [Finset.mem_Icc]; omega)
            have hstep1 : azim 0 (w (j + k)) (w (j + k + 1)) (w j) ≤ Real.pi :=
              le_trans hAj hpi_k
            have hstep2 : azim 0 (w j) (w (j + k)) (w (j + k + 1)) ≤ Real.pi := by
              have hs : azim 0 (w (j + k + 1)) (w j) (w (j + k)) ≤ Real.pi :=
                FSQKWKK_p16 0 (w (j + k)) (w (j + k + 1)) (w j) hstep1
              exact FSQKWKK_p16 0 (w (j + k + 1)) (w j) (w (j + k)) hs
            have hd3 : azim 0 (w j) (w (j + k)) (w (j + k + 1)) < e := by
              rw [AZIM_DIHV_SAME_STRONG
                (hnc j (j + k) (by omega) (by omega) (by omega))
                (hnc j (j + k + 1) (by omega) (by omega) (by omega)) hstep2]
              have hsub : ({j, j + k, j + k + 1} : Finset ℕ) ⊆ Finset.Icc 0 r := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp only [Finset.mem_Icc]
                omega
              exact h3 j (j + k) hsub (by omega) (by omega)
            have hpi_j : azim 0 (w j) (w (j + 1)) (w (j - 1)) ≤ Real.pi :=
              h2 j (by simp only [Finset.mem_Icc]; omega)
            have hstep3 : azim 0 (w j) (w (j + 1)) (w (j + k)) ≤ Real.pi :=
              le_trans hBj hpi_j
            have hd4 : azim 0 (w j) (w (j + 1)) (w (j + k)) < e := by
              by_cases hk1' : k = 1
              · subst k
                rw [azim_self]
                linarith
              · have hk2' : 2 ≤ k := by omega
                rw [AZIM_DIHV_SAME_STRONG
                  (hnc j (j + 1) (by omega) (by omega) (by omega))
                  (hnc j (j + k) (by omega) (by omega) (by omega)) hstep3]
                have hsub : ({j, j + 1, j + k} : Finset ℕ) ⊆ Finset.Icc 0 r := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp only [Finset.mem_Icc]
                  omega
                exact h4 j (j + k) hsub (by omega)
            have hsum3 : azim 0 (w j) (w (j + 1)) (w (j + k + 1)) =
                azim 0 (w j) (w (j + 1)) (w (j + k)) +
                azim 0 (w j) (w (j + k)) (w (j + k + 1)) := by
              refine sum3_azim_fan (x := 0) (v := w j) (u := w (j + 1))
                (w1 := w (j + k)) (w2 := w (j + k + 1))
                (hne0 j hjr) ?_ ?_ ?_ ?_
              · exact hnc j (j + 1) (by omega) (by omega) (by omega)
              · exact hnc j (j + k) (by omega) (by omega) (by omega)
              · exact hnc j (j + k + 1) (by omega) (by omega) (by omega)
              · linarith
            have hfin : azim 0 (w j) (w (j + 1)) (w (j + k + 1)) ≤
                azim 0 (w j) (w (j + 1)) (w (j - 1)) := by
              rw [hsum3]
              have h1j : 2 * e < azim 0 (w j) (w (j + 1)) (w (j - 1)) :=
                h1 j (by simp only [Finset.mem_Icc]; omega)
              linarith
            exact ⟨azim_nonneg _ _ _ _, hfin⟩
  constructor
  · intro k j hjk
    exact (main k j hjk).1
  · intro k j hj1 hjk
    exact (main k j hjk).2 hj1


/-- HOL `XIVPHKS_SHIFT` (XIVPHKS.hl:278): the same induction with the
straight angles in `1..(r+1)` (indices shifted by one).
Proved by the shifted copy of the `XIVPHKS_p16` induction; the `k = 0`
step is the `FST_LST_IN_WEDGE_GE` membership inline in `wedgeGe` form
(both wedges), and all non-collinearity comes from `hpair2`. -/
theorem XIVPHKS_SHIFT_p16 (W : ℕ → Set V3) (a d : ℕ → ℕ → ℕ → ℝ) (e : ℝ)
    (r : ℕ) (w : ℕ → V3)
    (hpair1 : (Set.Icc (0:ℕ) (r + 1)).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hpair2 : (Set.Icc (1:ℕ) (r + 2)).Pairwise fun i j => ¬ Collinear3 0 (w i) (w j))
    (hd : (fun i j k => dihV 0 (w i) (w j) (w k)) = d)
    (ha : (fun i j k => azim 0 (w i) (w j) (w k)) = a)
    (hW : (fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))) = W)
    (he : 0 < 2 * e)
    (h1 : ∀ i ∈ Finset.Icc 1 (r + 1), 2 * e < a i (i + 1) (i - 1))
    (h2 : ∀ i ∈ Finset.Icc 1 (r + 1), a i (i + 1) (i - 1) ≤ Real.pi)
    (h3 : ∀ p q, ({p, q, q + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) → p ≠ q →
      p ≠ q + 1 → d p q (q + 1) < e)
    (h4 : ∀ p q, ({p, p + 1, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) →
      q > p + 1 → d p (p + 1) q < e)
    (h5 : ∀ p q, ({p + 1, p, q} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) → q < p →
      d (p + 1) p q < e) :
    (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w j ∈ W (j + k)) ∧
    (∀ k j, 1 ≤ j → j + k ≤ r + 1 → w (j + k) ∈ W j) := by
  subst W
  subst a
  subst d
  dsimp only at h1 h2 h3 h4 h5
  let F : ℕ → Set V3 := fun i => wedgeGe 0 (w i) (w (i + 1)) (w (i - 1))
  have hnc : ∀ p q, 1 ≤ p → p ≤ r + 2 → 1 ≤ q → q ≤ r + 2 → p ≠ q →
      ¬ Collinear3 0 (w p) (w q) := by
    intro p q hp1 hp2 hq1 hq2 hpne
    exact hpair2 (by simp only [Set.mem_Icc]; omega)
      (by simp only [Set.mem_Icc]; omega) hpne
  have hne0 : ∀ p, 1 ≤ p → p ≤ r + 1 → w p ≠ 0 := by
    intro p hp1 hp2 h0
    exact hnc p (p + 1) hp1 (by omega) (by omega) (by omega) (by omega)
      (by simpa [h0] using
        collinear3_of_eq (v := (0:V3)) (w := (0:V3)) (w1 := w (p + 1)) rfl)
  have main : ∀ k, ∀ j, 1 ≤ j → j + k ≤ r + 1 →
      w j ∈ F (j + k) ∧ w (j + k) ∈ F j := by
    intro k
    induction k with
    | zero =>
        intro j hj1 hj
        have hdeg := AZIM_SPEC_DEGENERATE (0:V3) (w j) (w (j + 1))
        have hmem : w j ∈ F j := by
          refine ⟨?_, ?_⟩
          · rw [hdeg.2]
          · rw [hdeg.2]; exact azim_nonneg _ _ _ _
        exact ⟨hmem, hmem⟩
    | succ k ih =>
        by_cases hk : k = 0
        · subst k
          intro j hj1 hj
          have hm1 : w j ∈ F (j + 1) := by
            refine ⟨azim_nonneg _ _ _ _, ?_⟩
            simp
          have hm2 : w (j + 1) ∈ F j := by
            refine ⟨?_, ?_⟩
            · rw [azim_self]
            · rw [azim_self]; exact azim_nonneg _ _ _ _
          exact ⟨hm1, hm2⟩
        · have hk1 : 1 ≤ k := by omega
          intro j hj1 hj
          change w j ∈ F (j + k + 1) ∧ w (j + k + 1) ∈ F j
          have hjk : j + k ≤ r + 1 := by omega
          obtain ⟨hA, hB⟩ := ih j hj1 hjk
          have hA' : w j ∈ wedgeGe 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) := by
            simpa [F] using hA
          have he' : 0 < e := by linarith
          have h2eπ : 2 * e < 2 * Real.pi := by
            have hlt := h1 1 (by simp only [Finset.mem_Icc]; omega)
            have hle := h2 1 (by simp only [Finset.mem_Icc]; omega)
            have hlt2 := azim_lt_two_pi 0 (w 1) (w (1 + 1)) (w (1 - 1))
            linarith
          constructor
          · -- direction 1: w j ∈ F (j + k + 1)
            obtain ⟨hA2, hB2⟩ := ih (j + 1) (by omega) (by omega)
            have hshift : (j + 1) + k = j + k + 1 := by omega
            rw [hshift] at hA2
            have hA2' : w (j + 1) ∈
                wedgeGe 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              simpa [F] using hA2
            have hB2' : w (j + k + 1) ∈
                wedgeGe 0 (w (j + 1)) (w (j + 2)) (w j) := by
              have h := hB2
              rw [hshift] at h
              simpa [F] using h
            have hA2j : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := hA2'.2
            have hB2j : azim 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1)) ≤
                azim 0 (w (j + 1)) (w (j + 2)) (w j) := hB2'.2
            have hsum4a : azim 0 (w (j + 1)) (w (j + 2)) (w j) =
                azim 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1)) +
                azim 0 (w (j + 1)) (w (j + k + 1)) (w j) := by
              refine sum4_azim_fan (x := 0) (v := w (j + 1)) (u := w (j + 2))
                (w1 := w (j + k + 1)) (w2 := w j)
                (hne0 (j + 1) (by omega) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + 1) (j + 2) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + 1) (j + k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hB2j
            have hle1 : azim 0 (w (j + 1)) (w (j + k + 1)) (w j) ≤
                azim 0 (w (j + 1)) (w (j + 2)) (w j) := by
              rw [hsum4a]
              have hnn := azim_nonneg 0 (w (j + 1)) (w (j + 2)) (w (j + k + 1))
              linarith
            have hpi1 : azim 0 (w (j + 1)) (w (j + 2)) (w j) ≤ Real.pi :=
              h2 (j + 1) (by simp only [Finset.mem_Icc]; omega)
            have hpi2 : azim 0 (w (j + 1)) (w (j + k + 1)) (w j) ≤ Real.pi :=
              le_trans hle1 hpi1
            have hfsq : azim 0 (w (j + k + 1)) (w j) (w (j + 1)) ≤ Real.pi :=
              FSQKWKK_p16 0 (w (j + 1)) (w (j + k + 1)) (w j) hpi2
            have hd5 : azim 0 (w (j + k + 1)) (w j) (w (j + 1)) < e := by
              rw [AZIM_DIHV_SAME_STRONG
                (hnc (j + k + 1) j (by omega) (by omega) (by omega) (by omega) (by omega))
                (hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)) hfsq]
              have hsub : ({j + k + 1, j, j + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp only [Finset.mem_Icc]
                omega
              exact h3 (j + k + 1) j hsub (by omega) (by omega)
            have hsum4b : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1)) +
                azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) := by
              refine sum4_azim_fan (x := 0) (v := w (j + k + 1)) (u := w (j + k + 2))
                (w1 := w (j + 1)) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) (j + k + 2) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hA2j
            have hle2 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              rw [hsum4b]
              have hnn := azim_nonneg 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + 1))
              linarith
            have hpi3 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) ≤ Real.pi :=
              h2 (j + k + 1) (by simp only [Finset.mem_Icc]; omega)
            have hpi4 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) ≤ Real.pi :=
              le_trans hle2 hpi3
            have hd6 : azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) < e := by
              by_cases hk1' : k = 1
              · subst k
                rw [azim_self]
                linarith
              · have hk2' : 2 ≤ k := by omega
                rw [AZIM_DIHV_SAME_STRONG
                  (hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)) hpi4]
                have hsub : ({j + k + 1, j + k, j + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp only [Finset.mem_Icc]
                  omega
                have h5' := h5 (j + k) (j + 1) hsub (by omega)
                rw [DIHV_SYM_2] at h5'
                exact h5'
            have hsum3b : azim 0 (w (j + k + 1)) (w j) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w j) (w (j + 1)) +
                azim 0 (w (j + k + 1)) (w (j + 1)) (w (j + k)) := by
              refine sum3_azim_fan (x := 0) (v := w (j + k + 1)) (u := w j)
                (w1 := w (j + 1)) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)
              · linarith
            have hle3 : azim 0 (w (j + k + 1)) (w j) (w (j + k)) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              have h1i : 2 * e < azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) :=
                h1 (j + k + 1) (by simp only [Finset.mem_Icc]; omega)
              rw [hsum3b]
              linarith
            have hsum5 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) =
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w j) +
                azim 0 (w (j + k + 1)) (w j) (w (j + k)) := by
              refine sum5_azim_fan (x := 0) (v := w (j + k + 1)) (u := w (j + k + 2))
                (w1 := w j) (w2 := w (j + k))
                (hne0 (j + k + 1) (by omega) (by omega)) ?_ ?_ ?_ ?_
              · exact hnc (j + k + 1) (j + k + 2) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc (j + k + 1) (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hle3
            have hfin2 : azim 0 (w (j + k + 1)) (w (j + k + 2)) (w j) ≤
                azim 0 (w (j + k + 1)) (w (j + k + 2)) (w (j + k)) := by
              rw [hsum5]
              have hnn := azim_nonneg 0 (w (j + k + 1)) (w j) (w (j + k))
              linarith
            exact ⟨azim_nonneg _ _ _ _, hfin2⟩
          · -- direction 2: w (j + k + 1) ∈ F j
            have hB' : w (j + k) ∈ wedgeGe 0 (w j) (w (j + 1)) (w (j - 1)) := by
              simpa [F] using hB
            have hBj : azim 0 (w j) (w (j + 1)) (w (j + k)) ≤
                azim 0 (w j) (w (j + 1)) (w (j - 1)) := hB'.2
            have hAj : azim 0 (w (j + k)) (w (j + k + 1)) (w j) ≤
                azim 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) := hA'.2
            have hpi_k : azim 0 (w (j + k)) (w (j + k + 1)) (w (j + k - 1)) ≤ Real.pi :=
              h2 (j + k) (by simp only [Finset.mem_Icc]; omega)
            have hstep1 : azim 0 (w (j + k)) (w (j + k + 1)) (w j) ≤ Real.pi :=
              le_trans hAj hpi_k
            have hstep2 : azim 0 (w j) (w (j + k)) (w (j + k + 1)) ≤ Real.pi := by
              have hs : azim 0 (w (j + k + 1)) (w j) (w (j + k)) ≤ Real.pi :=
                FSQKWKK_p16 0 (w (j + k)) (w (j + k + 1)) (w j) hstep1
              exact FSQKWKK_p16 0 (w (j + k + 1)) (w j) (w (j + k)) hs
            have hd3 : azim 0 (w j) (w (j + k)) (w (j + k + 1)) < e := by
              rw [AZIM_DIHV_SAME_STRONG
                (hnc j (j + k) (by omega) (by omega) (by omega) (by omega) (by omega))
                (hnc j (j + k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)) hstep2]
              have hsub : ({j, j + k, j + k + 1} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp only [Finset.mem_Icc]
                omega
              exact h3 j (j + k) hsub (by omega) (by omega)
            have hpi_j : azim 0 (w j) (w (j + 1)) (w (j - 1)) ≤ Real.pi :=
              h2 j (by simp only [Finset.mem_Icc]; omega)
            have hstep3 : azim 0 (w j) (w (j + 1)) (w (j + k)) ≤ Real.pi :=
              le_trans hBj hpi_j
            have hd4 : azim 0 (w j) (w (j + 1)) (w (j + k)) < e := by
              by_cases hk1' : k = 1
              · subst k
                rw [azim_self]
                linarith
              · have hk2' : 2 ≤ k := by omega
                rw [AZIM_DIHV_SAME_STRONG
                  (hnc j (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (hnc j (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)) hstep3]
                have hsub : ({j, j + 1, j + k} : Finset ℕ) ⊆ Finset.Icc 1 (r + 1) := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp only [Finset.mem_Icc]
                  omega
                exact h4 j (j + k) hsub (by omega)
            have hsum3 : azim 0 (w j) (w (j + 1)) (w (j + k + 1)) =
                azim 0 (w j) (w (j + 1)) (w (j + k)) +
                azim 0 (w j) (w (j + k)) (w (j + k + 1)) := by
              refine sum3_azim_fan (x := 0) (v := w j) (u := w (j + 1))
                (w1 := w (j + k)) (w2 := w (j + k + 1))
                (hne0 j hj1 (by omega)) ?_ ?_ ?_ ?_
              · exact hnc j (j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc j (j + k) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact hnc j (j + k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              · linarith
            have hfin : azim 0 (w j) (w (j + 1)) (w (j + k + 1)) ≤
                azim 0 (w j) (w (j + 1)) (w (j - 1)) := by
              rw [hsum3]
              have h1j : 2 * e < azim 0 (w j) (w (j + 1)) (w (j - 1)) :=
                h1 j (by simp only [Finset.mem_Icc]; omega)
              linarith
            exact ⟨azim_nonneg _ _ _ _, hfin⟩
  constructor
  · intro k j hj1 hjk
    exact (main k j hj1 hjk).1
  · intro k j hj1 hjk
    exact (main k j hj1 hjk).2

end Kepler.Text
