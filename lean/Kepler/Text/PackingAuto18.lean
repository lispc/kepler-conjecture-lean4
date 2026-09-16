/-
Kepler Text lane, stage 18: the leaf-cell calculus (`leaf_cell.hl`), the
`sum_gamma` cluster-inequality scaffold (`sum_gamma.hl` /
`SUM_GAMMAX_LMFUN_ESTIMATE`, a supported lemma behind book lemma UPFZBZM), and
the counting-spheres bank of `YSSKQOY.hl`.

HOL sources (flyspeck text_formalization / packing):
- `leaf_cell.hl` (4306 ln): the "leaf" Voronoi faces (`leaf`, `stem`,
  `cc_pe1/2`, `cc_uh`, `cc_ke`, `cc_A0`, `cc_cell`) and 116 lemmas around
  Marchal cells attached to a leaf stem `{EL 0 ul, EL 1 ul}` (coplanarity,
  azimuth/wedge splitting, cell-compatibility `BDXKHTW`/`EWYBJUA`, `CFFONNL`).
- `sum_gamma.hl` (1465 ln): `TSKAJXY_statement` (already encoded in
  PackingAuto2) and the giant estimate `SUM_GAMMAX_LMFUN_ESTIMATE`
  (ported `sorry`; its HL proof is a 1400-line lemma chain over
  `mcell_set`, `gammaX`, `beta_bump_v1` bounds and the cluster sum).
- `YSSKQOY.hl` (551 ln): `selectd`, `normalize`, complex-argument helpers and
  the arclength monotonicity chain ending in `YSSKQOY`.

Encoding notes:
- HOL `real^3` ↔ `V3`; `set_of_list` ↔ `setOfList`, `barV`/`hl`/`mxi`/
  `omega_list`/`voronoi_list`/`radV`/`circumcenter` come from PackingAuto2.
- `chi_msb ul p = ((EL 1 ul - EL 0 ul) cross (EL 2 ul - EL 0 ul)) dot
  (p - EL 0 ul)` is rendered with Mathlib `CrossProduct` on `Fin 3 → ℝ`
  (the `V3 → Fin 3 → ℝ` coercion is the identity type-synonym lift; addition,
  subtraction and scalar multiplication commute with it by `rfl`, as used in
  TopologyFan).
- `cc_pe1`/`cc_pe2`/`cc_uh` are HOL `new_specification` (Skolem) constants;
  they are rendered by `Classical.choose` over the (sorry'd) existence
  theorems `cc_pe_exists` / `cc_uh_exists`, mirroring `SKOLEM_THM`.
- `re_eqvl` (trig2.hl:4238), `conv0` (sphere.hl:294), `delta`
  (collect_geom.hl:94), `delta_x` (sphere.hl:86), `ups_x` (sphere.hl:122),
  `arclength` (sphere.hl:258) are ported here because the ported lemmas
  quantify over them; `arclength` uses flyspeck `atn2(x, y) =
  Real.atan2 y x` (the flyspeck branch structure coincides with Mathlib's
  `Real.atan2` off the degenerate origin pair).
- YSSKQOY's `dot`/`vector_angle` on `:complex` are the real^2 structures
  under the standard complex identification; `complexDot` is that dot
  product. `COS_ARG_VECTOR_ANGLE` is stated in the ℂ identification (the
  HOL `vector_angle` of the pair); `SEC_DOT` is stated over `V3` with
  Kepler.Text's `vectorAngle`.
- `pack_ineq_def_a` (YSSKQOY.hl:24-31) is HOL reflection machinery: it builds
  the conjunction of the `UKBRPFE`/`WAZLDCD`/`BIEFJHU` flypaper inequalities
  out of `Ineq.ineqs` at load time. It is not a mathematical constant of the
  development and has no Lean counterpart; the three lemmas that reference
  such hypotheses are out of scope here.
- DISCHARGE check vs PackingAuto2 concl theorems: `TSKAJXY_statement` is
  byte-identical to PackingAuto2's encoding (reused, not redefined).
  `SUM_GAMMAX_LMFUN_ESTIMATE` is only a *support* lemma for UPFZBZM; it does
  not match `UPFZBZM_concl`, `RDWKARC_concl`, `GOTCJAH_concl` or
  `TIWWFYQ_concl`, which remain `sorry` in PackingAuto2.
- `AJRIPQN_0` (leaf_cell.hl:2132) discharges against PackingAuto17.AJRIPQN
  (its HOL twin), losing only the redundant `i = j` conjunct.

STATUS: skeleton port; statements faithful, mechanical lemmas proved,
the giant leaf-cell/sum-gamma chains carry `sorry`.
-/

import Kepler.Text.PackingAuto13
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical ComplexConjugate

noncomputable section

/-! ## Definitions (leaf_cell.hl:17-1142, sphere/collect-geom helpers) -/

/-- HOL `leaf` (leaf_cell.hl:17): a leaf Voronoi face over the bar pair. -/
def leaf (V : Set V3) (ul : List V3) : Prop := barV V 2 ul ∧ hl ul < Real.sqrt 2

/-- HOL `stem` (leaf_cell.hl:19): the pair of vertices carried by the leaf. -/
def stem (ul : List V3) : Set V3 := setOfList (truncateSimplex 1 ul)

/-- HOL `re_eqvl` (trig2.hl:4238): equality up to a positive real factor. -/
def reEqvl (a b : ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ a = t * b

/-- HOL `conv0` (sphere.hl:294): `affsign sgn_gt {} S`, the open cone on `S`. -/
def conv0 (S : Set V3) : Set V3 := affGt ∅ S

/-- The `V3` cross product (TopologyFan.cross3, non-private copy): Mathlib
`crossProduct` on the `Fin 3 → ℝ` identification. -/
noncomputable def cross3 (a b : V3) : V3 :=
  WithLp.toLp 2 (crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ))

/-- HOL `chi_msb` (leaf_cell.hl:781-782): the signed volume functional of the
ordered triple `ul` at `p`. -/
noncomputable def chiMsb (ul : List V3) (p : V3) : ℝ :=
  (crossProduct ((ul[1]! - ul[0]! : V3) : Fin 3 → ℝ)
      ((ul[2]! - ul[0]! : V3) : Fin 3 → ℝ)) ⬝ᵥ ((p - ul[0]! : V3) : Fin 3 → ℝ)

/-- HOL `cc_pe_exists` (leaf_cell.hl:1052-1084), from `YBZFUPO`. -/
theorem cc_pe_exists (V : Set V3) (ul : List V3) :
    ∃ p1 p2 : V3, Packing V → saturated V → leaf V ul →
      voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
        0 < chiMsb ul p1 := by
  sorry

/-- HOL `cc_pe1` (leaf_cell.hl:1082, `new_specification` via `SKOLEM_THM`). -/
noncomputable def ccPe1 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (cc_pe_exists V ul)

/-- HOL `cc_pe2` (leaf_cell.hl:1082, `new_specification` via `SKOLEM_THM`). -/
noncomputable def ccPe2 (V : Set V3) (ul : List V3) : V3 :=
  Classical.choose (Classical.choose_spec (cc_pe_exists V ul))

/-- HOL `cc_uh_exists` (leaf_cell.hl:1120-1132), from `NWVRFMF`. -/
theorem cc_uh_exists (V : Set V3) (ul : List V3) :
    ∃ vl : List V3, Packing V → saturated V → leaf V ul →
      barV V 3 vl ∧ truncateSimplex 2 vl = ul ∧ omegaList V vl = ccPe1 V ul := by
  sorry

/-- HOL `cc_uh` (leaf_cell.hl:1133, `new_specification` via `SKOLEM_THM`):
the four-point list whose Marchal cell is `cc_cell`. -/
noncomputable def ccUh (V : Set V3) (ul : List V3) : List V3 :=
  Classical.choose (cc_uh_exists V ul)

/-- HOL `cc_ke` (leaf_cell.hl:1136-1137): 4 when the cc_uh list is itself a
leaf (tetrahedron cell), else 3 (prism-with-apex cell). -/
def ccKe (V : Set V3) (ul : List V3) : ℕ :=
  if hl (ccUh V ul) < Real.sqrt 2 then 4 else 3

/-- HOL `cc_A0` (leaf_cell.hl:1139-1141). -/
def ccA0 (ul : List V3) : Set V3 :=
  affGt {ul[0]!, ul[1]!} {ul[2]!}

/-- HOL `cc_cell` (leaf_cell.hl:1142): the Marchal cell over `cc_uh`. -/
def ccCell (V : Set V3) (ul : List V3) : Set V3 := mcell (ccKe V ul) V (ccUh V ul)

/-- HOL `delta_x` (sphere.hl:86-90). -/
def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- HOL `delta` (collect_geom.hl:94-100): the Cayley–Menger style
determinant on edge-squared entries. -/
def deltaP (x12 x13 x14 x23 x24 x34 : ℝ) : ℝ :=
  -(x12 * x13 * x23) - x12 * x14 * x24 - x13 * x14 * x34 - x23 * x24 * x34 +
    x12 * x34 * (-x12 + x13 + x14 + x23 + x24 - x34) +
    x13 * x24 * (x12 - x13 + x14 + x23 - x24 + x34) +
    x14 * x23 * (x12 + x13 - x14 - x23 + x24 + x34)

/-- HOL `ups_x` (sphere.hl:122-124). -/
def upsX (x1 x2 x6 : ℝ) : ℝ :=
  -(x1 * x1) - x2 * x2 - x6 * x6 + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

/-- Flyspeck `atn2` (sphere.hl:48-52); `atn2 x y = Real.atan2 y x` off the
degenerate pair `(0, 0)`-with-`x ≤ 0` corner. -/
noncomputable def atn2 (x y : ℝ) : ℝ :=
  if |y| < x then Real.arctan (y / x)
  else if 0 < y then Real.pi / 2 - Real.arctan (x / y)
  else if y < 0 then -(Real.pi / 2) - Real.arctan (x / y)
  else Real.pi

/-- HOL `arclength` (sphere.hl:258-260). -/
noncomputable def arcLength (a b c : ℝ) : ℝ :=
  Real.pi / 2 +
    atn2 (Real.sqrt (upsX (a * a) (b * b) (c * c))) (c * c - a * a - b * b)

/-- HOL `selectd` (YSSKQOY.hl:39-40): a default-carrying choice operator
(the `Nonempty` constraint is a rendering artifact of `Classical.epsilon`,
which HOL's `@` does not need since HOL types are inhabited). -/
def selectd {α : Type*} [Nonempty α] (P : α → Prop) (d : α) : α :=
  if ∃ r, P r then Classical.epsilon P else d

/-- The real^2 dot product under the complex identification (YSSKQOY.hl:66
`DOT_COMPLEX`'s `dot` on `complex`). -/
def complexDot (z1 z2 : ℂ) : ℝ := z1.re * z2.re + z1.im * z2.im

/-- HOL `normalize` (YSSKQOY.hl:187). -/
noncomputable def normalize (v : V3) : V3 := (‖v‖ : ℝ)⁻¹ • v

/-- HOL `SUM_GAMMAX_LMFUN_ESTIMATE_concl` (sum_gamma.hl:53-60): there is a
constant bounding the cluster `gammaX` sum of an annulus-restricted cluster;
the supporting estimate for book lemma UPFZBZM. -/
def SUM_GAMMAX_LMFUN_ESTIMATE_concl : Prop :=
  ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V → 1 ≤ r →
    cellClusterInequality V → TSKAJXY_statement →
    c * r ^ 2 ≤ setSum {X | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
      (fun X => gammaX V X lmfun)

/-! ## YSSKQOY.hl: general lemmas -/

/-- HOL `selectd_cases` (YSSKQOY.hl:42-53). -/
theorem selectd_cases {α : Type*} [Nonempty α] (P : α → Prop) (d : α) :
    P (selectd P d) ∨ selectd P d = d := by
  by_cases h : ∃ r, P r
  · left
    simp only [selectd, if_pos h]
    exact Classical.epsilon_spec h
  · right; simp [selectd, h]

/-- HOL `selectd_exists` (YSSKQOY.hl:55-63). -/
theorem selectd_exists {α : Type*} [Nonempty α] {P : α → Prop} {d : α}
    (h : ∃ r, P r) : P (selectd P d) := by
  simp only [selectd, if_pos h]
  exact Classical.epsilon_spec h

/-- HOL `DOT_COMPLEX` (YSSKQOY.hl:66-72). -/
theorem DOT_COMPLEX (x y x' y' : ℝ) :
    complexDot (x + y * Complex.I) (x' + y' * Complex.I) = x * x' + y * y' := by
  simp [complexDot, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]

/-- HOL `DOT_RE` (YSSKQOY.hl:74-81). -/
theorem DOT_RE (z1 z2 : ℂ) : complexDot z1 z2 = (z1 * conj z2).re := by
  simp only [complexDot, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- HOL `ARG_0_DIV` (YSSKQOY.hl:99-105). -/
theorem ARG_0_DIV (u v : ℂ) : u / v = 0 ↔ u = 0 ∨ v = 0 := by
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · exact div_eq_zero_iff

/-- HOL `RE_CEXP_CX` (YSSKQOY.hl:198-204). -/
theorem RE_CEXP_CX (x : ℝ) : (Complex.exp (Complex.I * x)).re = Real.cos x := by
  rw [show Complex.I * x = x * Complex.I from mul_comm _ _]
  exact Complex.exp_ofReal_mul_I_re x

/-- HOL `ARG_CNJ` (YSSKQOY.hl:83-97). -/
theorem ARG_CNJ (z w : ℂ) (hw : w ≠ 0) :
    Complex.arg (z / w) = Complex.arg (z * conj w) := by
  sorry

/-- HOL `RE_NORM_1` (YSSKQOY.hl:216-224). -/
theorem RE_NORM_1 (z : ℂ) (h : ‖z‖ = 1) : z.re = Real.cos (Complex.arg z) := by
  have hz : z ≠ 0 := by
    intro hc; rw [hc] at h; simpa using h.symm
  have := Complex.cos_arg hz
  rw [h] at this
  simp at this
  linarith

/-- HOL `COS_ARG_VECTOR_ANGLE` (YSSKQOY.hl:226-261), stated with the real^2
`vector_angle` under the complex identification. -/
theorem COS_ARG_VECTOR_ANGLE (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.cos (Complex.arg (u / v)) =
      Real.cos (Real.arccos (complexDot u v / (‖u‖ * ‖v‖))) := by
  have huv : u / v ≠ 0 := by
    rw [ne_eq, div_eq_zero_iff]
    simp [hv, hu]
  have h1 : Real.cos (Complex.arg (u / v)) = (u / v).re / ‖u / v‖ :=
    Complex.cos_arg huv
  have hnorm : ‖u / v‖ = ‖u‖ / ‖v‖ := by
    rw [show u / v = u * v⁻¹ from by ring, norm_mul, norm_inv]; ring
  have hre : (u / v).re = complexDot u v / ‖v‖ ^ 2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [complexDot]
    ring
  have hcs : |complexDot u v| ≤ ‖u‖ * ‖v‖ := by
    rw [DOT_RE]
    refine le_trans (Complex.abs_re_le_norm (u * conj v)) ?_
    refine le_trans (norm_mul_le u (conj v)) ?_
    rw [Complex.norm_conj]
  have hdiv : |complexDot u v / (‖u‖ * ‖v‖)| ≤ 1 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity),
      div_le_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
    linarith
  have hbound := abs_le.1 hdiv
  rw [h1, hnorm, hre]
  have h2 : complexDot u v / ‖v‖ ^ 2 / (‖u‖ / ‖v‖) = complexDot u v / (‖u‖ * ‖v‖) := by
    have hu' : ‖u‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hu)
    have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv)
    field_simp
  rw [h2, Real.cos_arccos hbound.1 hbound.2]

/-- HOL `norm_normalize` (YSSKQOY.hl:189-196; the HL file carries it twice). -/
theorem norm_normalize (v : V3) (h : v ≠ 0) : ‖normalize v‖ = 1 := by
  simp only [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (fun hc => h (by rw [← norm_eq_zero]; exact hc))

/-- HOL `CARD_UNION_EQ` (YSSKQOY.hl:107-110). -/
theorem CARD_UNION_EQ {α : Type*} {s t u : Set α} (hu : u.Finite)
    (hst : s ∩ t = ∅) (huni : s ∪ t = u) :
    Nat.card s + Nat.card t = Nat.card u := by
  have hs : s.Finite := hu.subset (by rw [← huni]; exact subset_union_left)
  have ht : t.Finite := hu.subset (by rw [← huni]; exact subset_union_right)
  have key : (s ∪ t).ncard = s.ncard + t.ncard :=
    Set.ncard_union_eq (by rw [Set.disjoint_iff_inter_eq_empty]; exact hst) hs ht
  rw [_root_.Nat.card_coe_set_eq, _root_.Nat.card_coe_set_eq,
    _root_.Nat.card_coe_set_eq, ← huni]
  exact key.symm

/-- HOL `INJ_SURJ` (YSSKQOY.hl:112-155). The HOL `INJ f a b` splits into
`Set.InjOn f a` plus the codomain membership of `f` on `a`, which is stated
explicitly here. -/
theorem INJ_SURJ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
    (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
    (hi : Set.InjOn f a) (hmem : ∀ x ∈ a, f x ∈ b) :
    ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y := by
  have him : (f '' a).Finite := ha.image f
  have hcardimg : (f '' a).ncard = a.ncard := by
    have he := hi.encard_image
    rw [← him.cast_ncard_eq, ← ha.cast_ncard_eq] at he
    simpa using he
  have himsub : f '' a ⊆ b := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmem x hx
  have hsub2 : b ∩ f '' a = f '' a := Set.inter_eq_right.2 himsub
  have hun : b ∩ f '' a ∪ (b \ f '' a) = b := Set.inter_union_sdiff b (f '' a)
  rw [hsub2, Set.union_comm] at hun
  have hdiff : (b \ f '' a).Finite := hb.subset Set.sdiff_subset
  have hdisj : Disjoint (b \ f '' a) (f '' a) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact h1.2 h2
  have key := Set.ncard_union_eq hdisj hdiff him
  rw [hun] at key
  rw [_root_.Nat.card_coe_set_eq] at hcard
  have hcard' : a.ncard = b.ncard := hcard
  have hzero : (b \ f '' a).ncard = 0 := by
    have h1 := key
    have h2 := hcardimg
    omega
  have hempty : b \ f '' a = ∅ := (Set.ncard_eq_zero hdiff).1 hzero
  intro y hy
  have hmem2 : y ∈ f '' a := by
    by_contra hc
    exact absurd (Set.mem_sdiff y |>.2 ⟨hy, hc⟩) (by rw [hempty]; simp)
  obtain ⟨x, hx, hfx⟩ := (Set.mem_image f a y).1 hmem2
  exact ⟨x, hx, hfx⟩


/-- HOL `INJ_IFF_SURJ` (YSSKQOY.hl:157-185); same explicit codomain-membership
splitting of `INJ` as `INJ_SURJ`. -/
theorem INJ_IFF_SURJ {α β : Type*} {a : Set α} {b : Set β} {f : α → β}
    (ha : a.Finite) (hb : b.Finite) (hcard : Nat.card a = Nat.card b)
    (hmem : ∀ x ∈ a, f x ∈ b) :
    Set.InjOn f a ↔ ∀ y ∈ b, ∃ x, x ∈ a ∧ f x = y := by
  constructor
  · intro hi
    exact INJ_SURJ ha hb hcard hi hmem
  · intro hsurj
    have himg : f '' a = b := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨x, hx, rfl⟩
        exact hmem x hx
      · intro y hy
        obtain ⟨x, hx, hfx⟩ := hsurj y hy
        exact ⟨x, hx, hfx⟩
    have hcardimg : (f '' a).ncard = a.ncard := by
      rw [himg]
      exact hcard.symm
    exact Set.injOn_of_ncard_image_eq hcardimg ha

private theorem upsX_sq_factor (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c)
      = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  simp only [upsX]
  ring

/-- HOL `TRI_UPS_X_STRICT_POS` (YSSKQOY.hl:340-346). -/
theorem TRI_UPS_X_STRICT_POS (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (h1 : c < a + b) (h2 : a < b + c) (h3 : b < c + a) :
    0 < upsX (a * a) (b * b) (c * c) := by
  rw [upsX_sq_factor]
  refine mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    (by linarith)

/-- HOL `ups_x_pos` (YSSKQOY.hl:348-357). -/
theorem ups_x_pos (a b : ℝ) (h1 : 2 ≤ a) (h2 : a ≤ 2.52) (h3 : 2 ≤ b)
    (h4 : b ≤ 2.52) : 0 < upsX (a ^ 2) (b ^ 2) 4 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [sq a, sq b, show (4:ℝ) = 2 * 2 from by norm_num]
  exact TRI_UPS_X_STRICT_POS a b 2 ha hb (by norm_num) (by linarith) (by linarith)
    (by linarith)

/-- HOL `SEC_DOT` (YSSKQOY.hl:263-285), over `V3` with Kepler.Text's
`vector_angle`. -/
theorem SEC_DOT (u v : V3) (r ψ : ℝ) (hr : 0 < r) (hψ1 : 0 ≤ ψ)
    (hψ2 : ψ < Real.pi / 2) (hv : ‖v‖ = r / Real.cos ψ) (hu : ‖u‖ = r)
    (hcos : Real.cos (vectorAngle u v) = Real.cos ψ) :
    u ⬝ᵥ (v - u) = 0 := by
  have hcosψ : 0 < Real.cos ψ :=
    Real.cos_pos_of_mem_Ioo (by constructor <;> linarith)
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero, eq_comm, div_eq_zero_iff] at hv
    exact hcosψ.ne' (hv.resolve_left hr.ne')
  have hu0 : u ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hu
    exact hr.ne' hu.symm
  have hsplit : vectorAngle u v =
      Real.arccos ((u ⬝ᵥ v) / (‖u‖ * ‖v‖)) := by
    rw [vectorAngle, if_neg (by simp [hu0, hv0])]
  have hcs : |(u ⬝ᵥ v : ℝ)| ≤ ‖u‖ * ‖v‖ := by
    have := abs_real_inner_le_norm (x := u) (y := v)
    rwa [Kepler.Geom.inner_eq_dot] at this
  have hcs1 : -1 ≤ (u ⬝ᵥ v) / (‖u‖ * ‖v‖) ∧ (u ⬝ᵥ v) / (‖u‖ * ‖v‖) ≤ 1 := by
    obtain ⟨hn1, hn2⟩ := abs_le.1 hcs
    constructor
    · rw [le_div_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
      linarith
    · rw [div_le_iff₀ (show (0:ℝ) < ‖u‖ * ‖v‖ by positivity)]
      linarith
  have hval : Real.cos (Real.arccos ((u ⬝ᵥ v) / (‖u‖ * ‖v‖))) =
      (u ⬝ᵥ v) / (‖u‖ * ‖v‖) := Real.cos_arccos hcs1.1 hcs1.2
  have hkey : (u ⬝ᵥ v : ℝ) = r ^ 2 := by
    have h1 : Real.cos ψ = (u ⬝ᵥ v) / (‖u‖ * ‖v‖) := by
      rw [← Real.cos_arccos hcs1.1 hcs1.2, ← hsplit, eq_comm]
      exact hcos
    rw [hu, hv] at h1
    have ht0 : (u ⬝ᵥ v : ℝ) ≠ 0 := by
      intro hc
      rw [hc, zero_div] at h1
      exact hcosψ.ne' h1
    have hden : r * (r / Real.cos ψ) ≠ 0 :=
      mul_ne_zero hr.ne' (div_ne_zero hr.ne' hcosψ.ne')
    have h3 : Real.cos ψ * (r * (r / Real.cos ψ))
        = (u ⬝ᵥ v) / (r * (r / Real.cos ψ)) * (r * (r / Real.cos ψ)) :=
      congrArg (fun x : ℝ => x * (r * (r / Real.cos ψ))) h1
    have h2 : Real.cos ψ * (r * (r / Real.cos ψ)) = u ⬝ᵥ v := by
      rw [h3]
      exact div_mul_cancel₀ _ hden
    rw [← h2]
    field_simp
  rw [dotProduct_sub, hkey]
  rw [← Kepler.Geom.norm_sq_eq_dot, hu]
  ring

/-- HOL `Arc_properties.arc_sym` (the `arclength` symmetry in its first two
arguments; used by `yssk_reduction`). -/
theorem arc_sym (a b c : ℝ) : arcLength a b c = arcLength b a c := by
  have hu : upsX (a * a) (b * b) (c * c) = upsX (b * b) (a * a) (c * c) := by
    simp only [upsX]; ring
  have hy : c * c - a * a - b * b = c * c - b * b - a * a := by ring
  rw [arcLength, arcLength, hu, hy]

/-- HOL `arclength2` (YSSKQOY.hl:297-313): `arclength 2 (2 h) 2 = acs (h/2)`
on the flyspeck range `1 ≤ h ≤ h0`. -/
theorem arclength2 {h : ℝ} (h1 : 1 ≤ h) (h2 : h ≤ h0) :
    arcLength 2 (2 * h) 2 = Real.arccos (h / 2) := by
  have hv : h0 = 1.26 := rfl
  have hh : (0:ℝ) < h := by linarith
  have h126 : h ≤ 1.26 := by linarith
  have hp : (0:ℝ) < 4 - h * h := by nlinarith
  have hx : Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2))
      = 4 * h * Real.sqrt (4 - h * h) := by
    have hup : upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2) = (4 * h) ^ 2 * (4 - h * h) := by
      simp only [upsX]; ring
    have h4 : (0:ℝ) ≤ 4 * h := by nlinarith
    rw [hup, Real.sqrt_mul (sq_nonneg (4 * h)), Real.sqrt_sq h4]
  have hneg : (2 * 2 - 2 * 2 - (2 * h) * (2 * h) : ℝ) < 0 := by nlinarith
  have hyx : |2 * 2 - 2 * 2 - (2 * h) * (2 * h)| < 4 * h * Real.sqrt (4 - h * h) := by
    rw [abs_of_neg hneg]
    have hsqrt : h < Real.sqrt (4 - h * h) :=
      Real.lt_sqrt_of_sq_lt (by nlinarith)
    have hstep : h * h < h * Real.sqrt (4 - h * h) :=
      mul_lt_mul_of_pos_left hsqrt hh
    nlinarith
  have hatn : atn2 (Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2)))
      (2 * 2 - 2 * 2 - (2 * h) * (2 * h))
      = Real.arctan (-(h / Real.sqrt (4 - h * h))) := by
    rw [atn2, hx, if_pos hyx, show (2 * 2 - 2 * 2 - (2 * h) * (2 * h) : ℝ) = -(4 * h * h) from
      by ring]
    congr 1
    field_simp
  have hten : (1:ℝ) + (h / Real.sqrt (4 - h * h)) ^ 2 = 4 / (4 - h * h) := by
    rw [div_pow, Real.sq_sqrt hp.le, one_add_div hp.ne']
    congr 1
    ring
  have htsqrt : Real.sqrt (1 + (h / Real.sqrt (4 - h * h)) ^ 2)
      = 2 / Real.sqrt (4 - h * h) := by
    rw [hten, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  calc arcLength 2 (2 * h) 2
      = Real.pi / 2 + atn2 (Real.sqrt (upsX (2 * 2) ((2 * h) * (2 * h)) (2 * 2)))
          (2 * 2 - 2 * 2 - (2 * h) * (2 * h)) := rfl
    _ = Real.pi / 2 + Real.arctan (-(h / Real.sqrt (4 - h * h))) := by rw [hatn]
    _ = Real.pi / 2 - Real.arcsin (h / 2) := by
        rw [show Real.pi / 2 + Real.arctan (-(h / Real.sqrt (4 - h * h)))
            = Real.pi / 2 - Real.arctan (h / Real.sqrt (4 - h * h)) from by
              rw [Real.arctan_neg]; ring,
          Real.arctan_eq_arcsin, htsqrt, div_div_div_comm]
        have hd0 : Real.sqrt (4 - h * h) ≠ 0 := (Real.sqrt_ne_zero hp.le).2 hp.ne'
        rw [div_self hd0, div_one]
    _ = Real.arccos (h / 2) := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]

/-- HOL `yssk_reduction` (YSSKQOY.hl:316-338): `YSSKQOY` reduces to the
four-point monotonicity of `arclength`. -/
theorem yssk_reduction
    (hmono : ∀ a1 a2 b1 b2 : ℝ, 2 ≤ a1 → a1 ≤ a2 → a2 ≤ 2 * h0 →
      2 ≤ b1 → b1 ≤ b2 → b2 ≤ 2 * h0 →
      0 ≤ arcLength a2 b2 2 - arcLength a1 b2 2 - arcLength a2 b1 2 +
        arcLength a1 b1 2)
    {h h' : ℝ} (hh1 : 1 ≤ h) (hh2 : h ≤ h0) (hh1' : 1 ≤ h') (hh2' : h' ≤ h0) :
    Real.arccos (h / 2) + Real.arccos (h' / 2) - Real.pi / 3 ≤
      arcLength (2 * h) (2 * h') 2 := by
  have h2h : 2 ≤ 2 * h := by linarith
  have h2h0 : 2 * h ≤ 2 * h0 := by linarith
  have h2h' : 2 ≤ 2 * h' := by linarith
  have h2h0' : 2 * h' ≤ 2 * h0 := by linarith
  have hstep := hmono 2 (2 * h) 2 (2 * h') le_rfl h2h h2h0 le_rfl h2h' h2h0'
  have e1 : arcLength 2 (2 * h') 2 = Real.arccos (h' / 2) := arclength2 hh1' hh2'
  have e2 : arcLength (2 * h) 2 2 = arcLength 2 (2 * h) 2 := arc_sym _ _ _
  have e3 : arcLength 2 (2 * h) 2 = Real.arccos (h / 2) := arclength2 hh1 hh2
  have e4 : arcLength 2 2 2 = Real.pi / 3 := by
    have h1' : arcLength 2 (2 * 1) 2 = Real.arccos (1 / 2) :=
      arclength2 (by norm_num)
        (by have hv : h0 = 1.26 := rfl; linarith)
    rw [show 2 * 1 = (2:ℝ) from by ring] at h1'
    rw [h1', Real.arccos_eq_pi_div_two_sub_arcsin, ← Real.sin_pi_div_six,
      Real.arcsin_sin] <;> linarith [Real.pi_pos]
  rw [e1, e2, e3, e4] at hstep
  linarith

/-- HOL `arc_derivative` (YSSKQOY.hl:365-398); the `Arc_properties`
derivative theory is out of scope here. -/
theorem arc_derivative (a b : ℝ) (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b ∧ b ≤ 2.52) :
    HasDerivWithinAt (fun x => arcLength x b 2)
      (-(4 + a ^ 2 - b ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (b ^ 2) 4)))
      (Icc 2 2.52) a := by
  sorry

/-- HOL `arc_derivative2` (YSSKQOY.hl:400-443); requires the automated
`Calc_derivative` machinery (out of scope here). -/
theorem arc_derivative2 (a b : ℝ) (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b ∧ b ≤ 2.52) :
    HasDerivWithinAt
      (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4)))
      (32 * a * b / (Real.sqrt (upsX (a ^ 2) (b ^ 2) 4)) ^ 3) (Icc 2 2.52) b := by
  sorry

/-- HOL `arc_length2_increasing` (YSSKQOY.hl:447-489). -/
theorem arc_length2_increasing (a b1 b2 : ℝ)
    (h : 2 ≤ a ∧ a ≤ 2.52 ∧ 2 ≤ b1 ∧ b1 ≤ 2.52 ∧ 2 ≤ b2 ∧ b2 ≤ 2.52 ∧ b1 ≤ b2) :
    (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4))) b1 ≤
      (fun x => -(4 + a ^ 2 - x ^ 2) / (a * Real.sqrt (upsX (a ^ 2) (x ^ 2) 4))) b2 := by
  sorry

/-- HOL `arc_length1_increasing` (YSSKQOY.hl:491-529). -/
theorem arc_length1_increasing (a1 a2 b1 b2 : ℝ)
    (h : 2 ≤ a1 ∧ a1 ≤ a2 ∧ a2 ≤ 2.52 ∧ 2 ≤ b1 ∧ b1 ≤ b2 ∧ b2 ≤ 2.52) :
    arcLength a1 b2 2 - arcLength a1 b1 2 ≤ arcLength a2 b2 2 - arcLength a2 b1 2 := by
  sorry

/-- HOL `YSSKQOY` (YSSKQOY.hl:531-549): the counting-spheres arclength
inequality. -/
theorem YSSKQOY {h h' : ℝ} (hh1 : 1 ≤ h) (hh2 : h ≤ h0) (hh1' : 1 ≤ h')
    (hh2' : h' ≤ h0) :
    Real.arccos (h / 2) + Real.arccos (h' / 2) - Real.pi / 3 ≤
      arcLength (2 * h) (2 * h') 2 := by
  sorry

/-! ## leaf_cell.hl: generic lemmas -/

/-- HOL `plane` (collect_geom.hl:217-218). -/
def Plane (x : Set V3) : Prop :=
  ∃ u v w : V3, ¬Collinear3 u v w ∧ x = affineSpan ℝ {u, v, w}

/-- HOL `coplanar_alt` (collect_geom.hl:222). -/
def CoplanarAlt (S : Set V3) : Prop := ∃ x : Set V3, Plane x ∧ S ⊆ x

/-- HOL `coplanar_eq_coplanar_alt` (leaf_cell.hl:23-27); the ← direction
needs a non-collinear triple spanning the hull of a collinear one. -/
theorem coplanar_eq_coplanar_alt {s : Set V3} : Coplanar s ↔ CoplanarAlt s := by
  sorry

/-- HOL `RE_EQVL_IMP_SYM` (leaf_cell.hl:28-41). -/
theorem RE_EQVL_IMP_SYM {a b : ℝ} (h : reEqvl a b) : reEqvl b a := by
  obtain ⟨t, ht, hab⟩ := h
  exact ⟨t⁻¹, inv_pos.2 ht, by rw [hab]; field_simp⟩

/-- HOL `RE_EQVL_SYM` (leaf_cell.hl:42-49). -/
theorem RE_EQVL_SYM (a b : ℝ) : reEqvl a b ↔ reEqvl b a :=
  ⟨RE_EQVL_IMP_SYM, RE_EQVL_IMP_SYM⟩

/-- HOL `RE_EQVL_SCALE1` (leaf_cell.hl:50-71). -/
theorem RE_EQVL_SCALE1 (a b t : ℝ) (ht : 0 < t) :
    reEqvl (t * a) b ↔ reEqvl a b := by
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨s / t, div_pos hs ht, by
      rw [show s / t * b = s * b / t from by field_simp, eq_div_iff ht.ne', mul_comm]
      exact hsa⟩
  · rintro ⟨u, hu, hua⟩
    exact ⟨t * u, mul_pos ht hu, by rw [hua]; ring⟩

/-- HOL `RE_EQVL_SCALE2` (leaf_cell.hl:72-79). -/
theorem RE_EQVL_SCALE2 (a b t : ℝ) (ht : 0 < t) :
    reEqvl a (t * b) ↔ reEqvl a b := by
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨s * t, mul_pos hs ht, by rw [hsa]; ring⟩
  · rintro ⟨u, hu, hua⟩
    exact ⟨u / t, div_pos hu ht, by
      rw [show u / t * (t * b) = u * b from by field_simp]
      exact hua⟩

/-- HOL `RE_EQVL_REFL` (leaf_cell.hl:80-90). -/
theorem RE_EQVL_REFL (a : ℝ) : reEqvl a a := ⟨1, one_pos, by ring⟩

/-- HOL `AFF_DIM_3` (leaf_cell.hl:209-226 intermediate). -/
theorem AFF_DIM_3 (a b c : V3) : affDim {a, b, c} ≤ 2 := by
  rw [affDim]
  split
  · norm_num
  · have hsub : vectorSpan ℝ {a, b, c} ≤ Submodule.span ℝ ({a - b, a - c} : Set V3) := by
      rw [vectorSpan_eq_span_vsub_set_left (k := ℝ) (Set.mem_insert a ({b, c} : Set V3)),
        Submodule.span_le]
      rintro d ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · show x -ᵥ x ∈ Submodule.span ℝ ({x - b, x - c} : Set V3)
        rw [vsub_self]
        exact Submodule.zero_mem _
      · show a - x ∈ Submodule.span ℝ ({a - x, a - c} : Set V3)
        exact Submodule.subset_span (Set.mem_insert (a - x) {a - c})
      · show a - x ∈ Submodule.span ℝ ({a - b, a - x} : Set V3)
        exact Submodule.subset_span (by
          rw [Set.mem_insert_iff]
          exact Or.inr (Set.mem_singleton _))
    have hcard : (Module.finrank ℝ
        (Submodule.span ℝ ({a - b, a - c} : Set V3))) ≤ 2 := by
      sorry
    have h1 : Module.finrank ℝ (vectorSpan ℝ {a, b, c})
        ≤ Module.finrank ℝ (Submodule.span ℝ ({a - b, a - c} : Set V3)) :=
      Submodule.finrank_mono hsub
    linarith

/-- HOL `COPLANAR_IMP_AFF_DIM` (leaf_cell.hl:209-226). -/
theorem COPLANAR_IMP_AFF_DIM {s : Set V3} (h : Coplanar s) : affDim s ≤ 2 := by
  sorry

/-- HOL `NOT_COLLINEAR_AFF_DIM2` (leaf_cell.hl:3913-3926). -/
theorem NOT_COLLINEAR_AFF_DIM2 (a b c : V3) (h : ¬Collinear3 a b c) :
    affDim {a, b, c} = 2 := by
  have hne : ({a, b, c} : Set V3) ≠ ∅ := by
    intro hc
    have hm : a ∈ ({a, b, c} : Set V3) := Set.mem_insert a ({b, c} : Set V3)
    rw [hc] at hm
    exact hm
  have hle := AFF_DIM_3 a b c
  have hge : ¬(Module.finrank ℝ (vectorSpan ℝ {a, b, c}) ≤ 1) := by
    intro h1
    exact h (show Collinear ℝ ({a, b, c} : Set V3) from
      (collinear_iff_finrank_le_one (s := ({a, b, c} : Set V3))).2 h1)
  rw [affDim, if_neg hne] at hle ⊢
  have h2 := hge
  push_neg at h2
  have hcast : (1:ℤ) < (Module.finrank ℝ (vectorSpan ℝ {a, b, c}) : ℤ) :=
    by exact_mod_cast h2
  omega

/-- HOL `COPLANAR_INSERT` (leaf_cell.hl:227-240). -/
theorem COPLANAR_INSERT {s : Set V3} (p : V3) (h : affDim s = 2)
    (hc : Coplanar (insert p s)) : p ∈ affineSpan ℝ s := by
  sorry

/-- HOL `COPLANAR_UNION` (leaf_cell.hl:241-303). -/
theorem COPLANAR_UNION {P Q : Set V3} {a b : V3} (hP : P ≠ ∅) (hQ : Q ≠ ∅)
    (h1 : ∀ p ∈ P, ¬Collinear3 p a b) (h2 : ∀ q ∈ Q, ¬Collinear3 q a b)
    (h3 : ∀ p ∈ P, ∀ q ∈ Q, Coplanar ({p, q, a, b} : Set V3)) :
    Coplanar (P ∪ Q ∪ {a, b} : Set V3) := by
  sorry

/-- HOL `CONNECTED_SEGMENT_NOT_COVERED` (leaf_cell.hl:304-327). -/
theorem CONNECTED_SEGMENT_NOT_COVERED {A B : Set V3} {a b : V3}
    (hA : IsOpen A) (hB : IsOpen B) (ha : a ∈ A) (hb : b ∈ B) (hd : A ∩ B = ∅) :
    ∃ x, x ∈ segment ℝ a b ∧ x ∉ A ∧ x ∉ B := by
  sorry

/-- HOL `WEDGE_GE_NULL` (leaf_cell.hl:91-106). -/
theorem WEDGE_GE_NULL (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) (haz : azim u0 u1 v1 v2 = 0) :
    wedgeGe u0 u1 v1 v2 = affGe {u0, u1} {v1} := by
  sorry

/-- HOL `WEDGE_WEDGE_GE` (leaf_cell.hl:107-153). -/
theorem WEDGE_WEDGE_GE (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    wedgeGe u0 u1 v1 v2 ⊆ wedge u0 u1 v1 v2 ∪ affGe {u0, u1} {v1} ∪
      affGe {u0, u1} {v2} := by
  sorry

/-- HOL `WEDGE_GE_ALMOST_DISJOINT` (leaf_cell.hl:154-208). -/
theorem WEDGE_GE_ALMOST_DISJOINT (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} := by
  sorry

/-- HOL `GBEWYFX` (leaf_cell.hl:328-341). -/
theorem GBEWYFX {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) : ¬Collinear3 ul[0]! ul[1]! ul[2]! := by
  sorry

/-- HOL `NWVRFMF` (leaf_cell.hl:342-359). -/
theorem NWVRFMF {V : Set V3} {ul : List V3} {p : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul)
    (hf : FacetOf {p} (voronoiList V ul)) :
    ∃ vl, barV V 3 vl ∧ truncateSimplex 2 vl = ul ∧ omegaList V vl = p := by
  sorry

/-- HOL `YBZFUPO` (leaf_cell.hl:360-423). -/
theorem YBZFUPO {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) :
    ∃ p1 p2 : V3, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧ p1 ≠ p2 ∧
      ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2} := by
  sorry

/-- HOL `permutes` (HOL Light sets.ml): `p` maps the set into itself, fixes
every point outside it, and is globally injective. -/
def Permutes (p : ℕ → ℕ) (s : Set ℕ) : Prop :=
  (∀ x ∈ s, p x ∈ s) ∧ (∀ x ∉ s, p x = x) ∧ ∀ x y : ℕ, p x = p y → x = y

/-- HOL `PERMUTES_a_PERMUTES_b` (leaf_cell.hl:424-462); HOL `0..a` is
`Finset.range (a+1)` as a set. -/
theorem PERMUTES_a_PERMUTES_b {p : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : Permutes p ((Finset.range (a + 1) : Finset ℕ))) :
    Permutes p ((Finset.range (b + 1) : Finset ℕ)) := by
  have hmid : ∀ x ∉ ((Finset.range (b + 1) : Finset ℕ) : Set ℕ), p x = x := by
    intro x hx
    refine h.2.1 x ?_
    intro hmem
    rw [Finset.mem_coe, Finset.mem_range] at hmem
    have hx1 : x < b + 1 := by omega
    exact hx (by rw [Finset.mem_coe, Finset.mem_range]; exact hx1)
  refine ⟨?_, hmid, h.2.2⟩
  intro x hx
  rw [Finset.mem_coe, Finset.mem_range] at hx ⊢
  rcases le_or_gt x a with hle | hgt
  · have hx' : p x ∈ ((Finset.range (a + 1) : Finset ℕ) : Set ℕ) :=
      h.1 x (by rw [Finset.mem_coe]; exact Finset.mem_range.2 (by omega))
    rw [Finset.mem_coe, Finset.mem_range] at hx'
    omega
  · have hfx := h.2.1 x (by
      intro hmem
      rw [Finset.mem_coe, Finset.mem_range] at hmem
      omega)
    omega

/-- HOL `PERMUTE_BARV3` (leaf_cell.hl:463-529). -/
theorem PERMUTE_BARV3 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (hhl : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    {p : Equiv.Perm ℕ} (hp' : permutes p (Finset.range 2)) :
    barV V 3 (leftActionList p ul) := by
  sorry

/-- HOL `ZASUVOR` (leaf_cell.hl:530-?). -/
theorem ZASUVOR {V : Set V3} {u0 u1 u2 : V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V [u0, u1, u2]) :
    leaf V [u1, u0, u2] ∧ stem [u0, u1, u2] = stem [u1, u0, u2] := by
  sorry

/-- HOL `truncate_set_of_list` (leaf_cell.hl:530-554). -/
theorem truncate_set_of_list {vl : List V3} {k : ℕ}
    (hk : 0 < k) (hlen : vl.length = k + 1) :
    setOfList vl ⊆ setOfList (truncateSimplex (k - 1) vl) ∪ {vl.getD k 0} := by
  sorry

private theorem sub_dot18 (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c :=
  sub_dotProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_sub18 (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c :=
  dotProduct_sub (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → ℝ)

private theorem dot_smul18 (t : ℝ) (a b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) :=
  dotProduct_smul t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem dot_comm18 (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

private theorem coe_smul18 (t : ℝ) (a : V3) :
    ((t • a : V3) : Fin 3 → ℝ) = t • (a : Fin 3 → ℝ) := rfl

private theorem coe_add18 (a b : V3) :
    ((a + b : V3) : Fin 3 → ℝ) = (a : Fin 3 → ℝ) + (b : Fin 3 → ℝ) := rfl

/-- norm-squares equal implies norms equal (helper for DIST_EQ_HALF_PLANE). -/
private theorem norm_eq_of_sq_eq {u v : V3} (h : ‖u‖ ^ 2 = ‖v‖ ^ 2) : ‖u‖ = ‖v‖ := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg (R := ℝ)).1 h with h1 | h1
  · exact h1
  · have hnu : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
    have hnv : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
    have hu : ‖u‖ = 0 := by linarith
    have hv : ‖v‖ = 0 := by linarith
    rw [norm_eq_zero.1 hu, norm_eq_zero.1 hv]

/-- HOL `DIST_LE_HALF_PLANE` (leaf_cell.hl:555-573). The proof is pure
inner-product algebra (`‖x−a‖² ≤ ‖x−b‖² ↔ 0 ≤ (a−b)·(2x−a−b)`); the `V3`
dot/WithLp coercion bridging is left to a follow-up lane. -/
theorem DIST_LE_HALF_PLANE (x a b : V3) :
    dist x a ≤ dist x b ↔ 0 ≤ (a - b) ⬝ᵥ (2 • x - (a + b)) := by
  sorry

/-- HOL `DIST_EQ_HALF_PLANE` (leaf_cell.hl:574-780). -/
theorem DIST_EQ_HALF_PLANE (x a b : V3) :
    dist x a = dist x b ↔ (a - b) ⬝ᵥ (2 • x - (a + b)) = 0 := by
  sorry

/-- HOL `FUZBZGI_0` (leaf_cell.hl:781-835). -/
theorem FUZBZGI_0 {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hfac : ∀ f, FacetOf f (voronoiList V ul) → f = {p1} ∨ f = {p2}) :
    0 < t2 := by
  sorry

/-- HOL `FUZBZGI_1` (leaf_cell.hl:781-835). -/
theorem FUZBZGI_1 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    ∃ p1 p2 : V3, ∃ t1 t2 : ℝ, voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3) ∧
      p1 ≠ p2 ∧ circumcenter (setOfList ul) = t1 • p1 + t2 • p2 ∧ t1 + t2 = 1 ∧
      0 < t1 ∧ 0 < t2 := by
  sorry

/-- HOL `chi_msb_swap_01` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_01 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [b, a, c] d := by
  sorry

/-- HOL `chi_msb_swap_23` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_23 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [a, b, d] c := by
  sorry

/-- HOL `chi_msb_swap_12` (leaf_cell.hl:803-835). -/
theorem chi_msb_swap_12 (a b c d : V3) :
    chiMsb [a, b, c] d = -chiMsb [a, c, b] d := by
  sorry

/-- HOL `chi_msb_additive_a` (leaf_cell.hl:836-861). -/
theorem chi_msb_additive_a (a b c d : V3) (t1 t2 t3 t4 : ℝ) (ht : t1 + t2 + t3 + t4 = 1) :
    chiMsb [t1 • a + t2 • b + t3 • c + t4 • d, b, c] d
      = t1 * chiMsb [a, b, c] d := by
  sorry

/-- HOL `chi_msb_additive_d` (leaf_cell.hl:862-878). -/
theorem chi_msb_additive_d (a b c d : V3) (t1 t2 t3 t4 : ℝ) (ht : t1 + t2 + t3 + t4 = 1) :
    chiMsb [a, b, c] (t1 • a + t2 • b + t3 • c + t4 • d)
      = t4 * chiMsb [a, b, c] d := by
  sorry

/-- HOL `CHI_MSB_ADDITIVE` (leaf_cell.hl:879-890). -/
theorem CHI_MSB_ADDITIVE (ul : List V3) (p1 p2 : V3) (t1 t2 : ℝ) (ht : t1 + t2 = 1) :
    chiMsb ul (t1 • p1 + t2 • p2)
      = t1 * chiMsb ul p1 + t2 * chiMsb ul p2 := by
  sorry

/-- HOL `CHI_MSB_CONVEX` (leaf_cell.hl:891-934). -/
theorem CHI_MSB_CONVEX (ul : List V3) :
    Convex ℝ {p | 0 ≤ chiMsb ul p} := by
  sorry

/-- HOL `AFFINE_IMP_CHI_MSB_0` (leaf_cell.hl:935-942). -/
theorem AFFINE_IMP_CHI_MSB_0 (ul : List V3) (p : V3) (hlen : ul.length = 3)
    (hp : p ∈ affineSpan ℝ (setOfList ul)) : chiMsb ul p = 0 := by
  sorry

/-- HOL `CHI_MSB_IMP_COPLANAR` (leaf_cell.hl:935-942). -/
theorem CHI_MSB_IMP_COPLANAR (ul : List V3) (p : V3) (h : chiMsb ul p = 0) :
    Coplanar ({ul.getD 0 0, ul.getD 1 0, ul.getD 2 0, p} : Set V3) := by
  sorry

/-- HOL `CHI_MSB_COPLANAR` (leaf_cell.hl:943-1011). -/
theorem CHI_MSB_COPLANAR (a b c d : V3) :
    Coplanar ({a, b, c, d} : Set V3) ↔ chiMsb [a, b, c] d = 0 := by
  sorry

/-- HOL `JDHAWAY_0` (leaf_cell.hl:1012-1051). -/
theorem JDHAWAY_0 {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hpos : 0 < t1 ∧ 0 < t2) : chiMsb ul p1 ≠ 0 := by
  sorry

/-- HOL `JDHAWAY_1` (leaf_cell.hl:1012-1051). -/
theorem JDHAWAY_1 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    chiMsb ul (circumcenter (setOfList ul)) = 0 := by
  sorry

/-- HOL `JDWAWAY` (leaf_cell.hl:1012-1051). -/
theorem JDWAWAY {V : Set V3} {ul : List V3} {p1 p2 : V3} {t1 t2 : ℝ}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hv : voronoiList V ul = convexHull ℝ ({p1, p2} : Set V3)) (hne : p1 ≠ p2)
    (hc : circumcenter (setOfList ul) = t1 • p1 + t2 • p2) (hts : t1 + t2 = 1)
    (hpos : 0 < t1 ∧ 0 < t2) :
    chiMsb ul p1 ≠ 0 ∧ chiMsb ul p2 ≠ 0 ∧ (chiMsb ul p1 < 0 ↔ 0 < chiMsb ul p2) := by
  sorry

/-- HOL `FACET_OF_SEGMENT` (leaf_cell.hl:1085-1104): the endpoints are the
1-dimensional faces of the closed segment `segment[a,b]`. -/
theorem FACET_OF_SEGMENT (a b : V3) (h : a ≠ b) :
    FacetOf {a} (segment ℝ a b) := by
  sorry

/-- HOL `CC_PE_FACET_OF` (leaf_cell.hl:1105-1119). -/
theorem CC_PE_FACET_OF {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    FacetOf {ccPe1 V ul} (voronoiList V ul) := by
  sorry

/-- HOL `CC_CELL4` (leaf_cell.hl:1143-?): the 4-case Marchal cell is the
Delaunay tetrahedron over `cc_uh`. -/
theorem CC_CELL4 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    ccCell V ul = convexHull ℝ (setOfList (ccUh V ul)) := by
  unfold ccCell ccKe at *
  rw [h4]
  have hif : hl (ccUh V ul) < Real.sqrt 2 := by
    by_contra hc
    rw [if_neg hc] at h4
    exact absurd h4 (by norm_num)
  have hd : mcell 4 V (ccUh V ul) = mcell4 V (ccUh V ul) := by
    rw [mcell]; simp
  rw [hd, mcell4, if_pos hif]

/-- HOL `CC_KE_34` (leaf_cell.hl:1245-?): the dispatch value is 3 or 4. -/
theorem CC_KE_34 (V : Set V3) (ul : List V3) : ccKe V ul = 3 ∨ ccKe V ul = 4 := by
  unfold ccKe
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- HOL `CC_CELL3` (leaf_cell.hl:1180-1210). -/
theorem CC_CELL3 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    ccCell V ul = convexHull ℝ (setOfList (truncateSimplex 2 (ccUh V ul)) ∪
      {mxi V (ccUh V ul)}) := by
  sorry

/-- HOL `CC_CELL34` (leaf_cell.hl:1210-1244). -/
theorem CC_CELL34 {V : Set V3} {ul : List V3} {pp : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    ccCell V ul = convexHull ℝ ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pp} : Set V3) := by
  sorry

/-- HOL `U2_IN_CC_CELL` (leaf_cell.hl:1245-?). -/
theorem U2_IN_CC_CELL {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 2 0 ∈ ccCell V ul := by
  sorry

/-- HOL `U2_IN_AFF_GT` (leaf_cell.hl:1250-1276). -/
theorem U2_IN_AFF_GT {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 2 0 ∈ affGt {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0}
      {(ccUh V ul).getD 2 0} := by
  sorry

/-- HOL `EL_CC_UH` (leaf_cell.hl:1277-1313): the first three entries of
`cc_uh` agree with `ul`. -/
theorem EL_CC_UH {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    (ccUh V ul).getD 0 0 = ul.getD 0 0 ∧ (ccUh V ul).getD 1 0 = ul.getD 1 0 ∧
      (ccUh V ul).getD 2 0 = ul.getD 2 0 := by
  sorry

/-- HOL `NUNRRDS_0` (leaf_cell.hl:1314-?). -/
theorem NUNRRDS_0 {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) :
    ccA0 ul ∩ ccCell V ul ≠ ∅ := by
  sorry

/-- HOL `AFF_GE_MONO_TRANS` (leaf_cell.hl:1314-1390). -/
theorem AFF_GE_MONO_TRANS {X Y S : Set V3} (h : S ⊆ X) :
    affGe (X \ S) (Y ∪ S) ⊆ affGe X Y := by
  sorry

/-- HOL `K4_CHI_MSB_EQVL` (leaf_cell.hl:1391-?). -/
theorem K4_CHI_MSB_EQVL {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    reEqvl (chiMsb ul ((ccUh V ul).getD 3 0)) (chiMsb ul (ccPe1 V ul)) := by
  sorry

/-- HOL `K4_CHI_MSB_POS` (leaf_cell.hl:1391-?). -/
theorem K4_CHI_MSB_POS {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h4 : ccKe V ul = 4) :
    0 < chiMsb ul ((ccUh V ul).getD 3 0) := by
  sorry

/-- HOL `MXI_BETWEEN` (leaf_cell.hl:1391-1421). -/
theorem MXI_BETWEEN {V : Set V3} {ul vl : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3)
    (hv : ccUh V ul = vl) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      mxi V vl = (1 - t) • omegaListN V vl 2 + t • omegaListN V vl 3) ∧
      dist (vl.getD 0 0) (mxi V vl) = Real.sqrt 2 := by
  sorry

/-- HOL `affine_invert` (leaf_cell.hl:1422-1528). -/
theorem affine_invert {u : ℝ} {p q : V3} {s : Set V3} (hu : u ≠ 0)
    (haff : affineSpan ℝ s = s)
    (hm : (1 - u) • p + u • q ∈ s) (hp : p ∈ s) : q ∈ s := by
  sorry

/-! ## leaf_cell.hl: the cc_cell block -/

/-- HOL `CELL3_NONDEG` (leaf_cell.hl:1529-1575). -/
theorem CELL3_NONDEG {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    (mxi V (ccUh V ul)) ∉ affineSpan ℝ (setOfList ul) ∧
      0 < chiMsb ul (mxi V (ccUh V ul)) := by
  sorry

/-- HOL `CELL_NN` (leaf_cell.hl:1529-1575). -/
theorem CELL_NN {V : Set V3} {ul : List V3} {p : V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (hp' : p ∈ ccCell V ul) :
    0 ≤ chiMsb ul p := by
  sorry

/-- HOL `delta_delta_x` (leaf_cell.hl:1576-1584): the two Cayley–Menger
encodings agree. -/
theorem delta_delta_x (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaP x1 x2 x3 x6 x5 x4 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaP, deltaX]
  ring

/-- HOL `ZWVCBMN` (leaf_cell.hl:1585-1629). -/
theorem ZWVCBMN (a b c d : V3) (h : ¬Coplanar ({a, b, c, d} : Set V3)) :
    0 < MeasureTheory.volume (convexHull ℝ ({a, b, c, d} : Set V3)) := by
  sorry

/-- HOL `MXI_IN_VORONOI_LIST` (leaf_cell.hl:1630-1665). -/
theorem MXI_IN_VORONOI_LIST {V : Set V3} {vl : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 vl) (h1 : Real.sqrt 2 ≤ hl vl)
    (h2 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    mxi V vl ∈ voronoiList V (truncateSimplex 2 vl) ∧
      dist (vl.getD 0 0) (mxi V vl) = Real.sqrt 2 := by
  sorry

/-- HOL `VORONOI_LIST_EQ` (leaf_cell.hl:1666-1687). -/
theorem VORONOI_LIST_EQ {V : Set V3} {ul : List V3} {p : V3} {k : ℕ}
    (hp : p ∈ voronoiList V ul) (hb : barV V k ul) :
    ∃ r : ℝ, ∀ q ∈ setOfList ul, dist p q = r := by
  sorry

/-- HOL `NOT_COL_IMP_RADV` (leaf_cell.hl:1688-1869). -/
theorem NOT_COL_IMP_RADV (va vb vc : V3) (h : ¬Collinear3 va vb vc) :
    ∀ w ∈ ({va, vb, vc} : Set V3),
      radV ({va, vb, vc} : Set V3) = dist (circumcenter ({va, vb, vc} : Set V3)) w := by
  sorry

/-- HOL `MCELL3_NONPLANAR` (leaf_cell.hl:1870-?). -/
theorem MCELL3_NONPLANAR {V : Set V3} {vl : List V3} (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 vl) (h1 : Real.sqrt 2 ≤ hl vl)
    (h2 : hl (truncateSimplex 2 vl) < Real.sqrt 2) :
    ¬Coplanar (mcell3 V vl) := by
  sorry

/-- HOL `MCELL2_SUBSET_AFF_GE` (leaf_cell.hl:1870-?). -/
theorem MCELL2_SUBSET_AFF_GE (V : Set V3) (ul : List V3) :
    mcell2 V ul ⊆ affGe {hdV ul, hdV ul.tail} {mxi V ul, omegaListN V ul 3} := by
  sorry

/-- HOL `CONDS_IN_CONV2` (leaf_cell.hl:1870-?). -/
theorem CONDS_IN_CONV2 {v w : V3} {t2 t3 : ℝ} (h2 : 0 ≤ t2) (h3 : 0 ≤ t3)
    (hne : ¬(t2 = 0 ∧ t3 = 0)) :
    (t2 / (t2 + t3)) • v + (t3 / (t2 + t3)) • w ∈ convexHull ℝ ({v, w} : Set V3) := by
  sorry

/-- HOL `AFFINE_DEPENDENT_EXPLICIT_4` (leaf_cell.hl:1870-?). -/
theorem AFFINE_DEPENDENT_EXPLICIT_4 (a b c d : V3) (ta tb tc td : ℝ)
    (hind : AffineIndependent ℝ (fun x : ({a, b, c, d} : Set V3) => (x : V3)))
    (hcard : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hsum : ta + tb + tc + td = 0)
    (hlin : ta • a + tb • b + tc • c + td • d = 0) :
    ta = 0 ∧ tb = 0 ∧ tc = 0 ∧ td = 0 := by
  sorry

/-- HOL `CONVEX_PLANE_INTER` (leaf_cell.hl:1870-2053). -/
theorem CONVEX_PLANE_INTER (a b p q : V3) (hab : a ≠ b) (hd : a ≠ p ∧ b ≠ p)
    (hq : q ∈ affGt {a, b} {p}) :
    ∃ c, c ∈ affGt {a, b} {p} ∧
      c ∈ convexHull ℝ ({a, b, p} : Set V3) ∩ convexHull ℝ ({a, b, q} : Set V3) := by
  sorry

/-- HOL `CONVEX_R3_INTER` (leaf_cell.hl:1870-2053). -/
theorem CONVEX_R3_INTER (a b c p q : V3) (hnc : ¬Coplanar ({a, b, c, p} : Set V3))
    (hq : q ∈ affGt {a, b, c} {p}) :
    ∃ d : V3, ¬Coplanar ({a, b, c, d} : Set V3) ∧
      d ∈ convexHull ℝ ({a, b, c, p} : Set V3) ∩ convexHull ℝ ({a, b, c, q} : Set V3) := by
  sorry

/-- HOL `MCELL2_CONVEX` (leaf_cell.hl:2054-2131). -/
theorem MCELL2_CONVEX {V : Set V3} {vl : List V3} (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 vl) : Convex ℝ (mcell2 V vl) := by
  sorry

/-- HOL `MCELL_CONVEX` (leaf_cell.hl:2054-2131). -/
theorem MCELL_CONVEX {V : Set V3} {vl : List V3} {k : ℕ} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 vl) (hk : 2 ≤ k) : Convex ℝ (mcell k V vl) := by
  sorry

/-- HOL `CHI_MSB_AFF_GT_0` (leaf_cell.hl:2132-2177). -/
theorem CHI_MSB_AFF_GT_0 (a b c q q' : V3)
    (hnc : ¬Coplanar ({a, b, c, q} : Set V3))
    (hq : 0 < chiMsb [a, b, c] q) (hq' : 0 < chiMsb [a, b, c] q') :
    q' ∈ affGt {a, b, c} {q} := by
  sorry

/-- HOL `CHI_MSB_POS2` (leaf_cell.hl:2132-2177). -/
theorem CHI_MSB_POS2 (a b c d p : V3) (hd : a ≠ b ∧ b ≠ c)
    (hd' : d ∈ affGt {a, b} {c}) :
    reEqvl (chiMsb [a, b, d] p) (chiMsb [a, b, c] p) := by
  sorry

/-- HOL `MCELL_ARG_REDUCE` (leaf_cell.hl:2132-2177): every Marchal cell is
one of `mcell j`, `j ≤ 4`. -/
theorem MCELL_ARG_REDUCE (V : Set V3) (ul : List V3) (i : ℕ) :
    ∃ j, j ≤ 4 ∧ mcell i V ul = mcell j V ul := by
  match i with
  | 0 => exact ⟨0, by omega, rfl⟩
  | 1 => exact ⟨1, by omega, rfl⟩
  | 2 => exact ⟨2, by omega, rfl⟩
  | 3 => exact ⟨3, by omega, rfl⟩
  | n + 4 => exact ⟨4, by omega, by simp [mcell]⟩

/-- HOL `AJRIPQN_0` (leaf_cell.hl:2132-2177); a corollary of the Auto17
`AJRIPQN` (which additionally concludes `i = j`). -/
theorem AJRIPQN_0 {V : Set V3} {ul vl : List V3} {i j : ℕ} (hp : Packing V)
    (hs : saturated V) (hb1 : barV V 3 ul) (hb2 : barV V 3 vl)
    (hvol : ¬nullSet (mcell i V ul ∩ mcell j V vl)) :
    mcell j V vl = mcell i V ul := by
  sorry

/-- HOL `CFFONNL` (leaf_cell.hl:2178-2514). -/
theorem CFFONNL {V : Set V3} {ul : List V3} {X : Set V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) (hX : X ∈ mcellSet V)
    (he : {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} ∈ edgeX V X)
    (hA : X ∩ ccA0 ul ≠ ∅) (hne : X ≠ ccCell V ul) :
    X = ccCell V [(ccUh V ul).getD 1 0, (ccUh V ul).getD 0 0, (ccUh V ul).getD 2 0] := by
  sorry

/-- HOL `CC_CELL_IN_MCELL_SET` (leaf_cell.hl:2515-2584). -/
theorem CC_CELL_IN_MCELL_SET {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) : ccCell V ul ∈ mcellSet V := by
  sorry

/-- HOL `CARD4_ALL_DISTINCT` (leaf_cell.hl:2585-?). -/
theorem CARD4_ALL_DISTINCT {a b c d : V3} (h4 : Nat.card ({a, b, c, d} : Set V3) = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  sorry

/-- HOL `LENGTH4_SET2` (leaf_cell.hl:2585-?). -/
theorem LENGTH4_SET2 {a b c d e f : V3} (h4 : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hset : setOfList [a, b, c, d] = setOfList [a, b, e, f]) :
    (e = c ∧ f = d) ∨ (e = d ∧ f = c) := by
  sorry

/-- HOL `LENGTH4_SET2_SWAP01` (leaf_cell.hl:2585-?). -/
theorem LENGTH4_SET2_SWAP01 {a b c d e f : V3}
    (h4 : Nat.card ({a, b, c, d} : Set V3) = 4)
    (hset : setOfList [a, b, c, d] = setOfList [b, a, e, f]) :
    (e = c ∧ f = d) ∨ (e = d ∧ f = c) := by
  sorry

/-- HOL `CC_CELL_NOT_COPLANAR` (leaf_cell.hl:2622-2640). -/
theorem CC_CELL_NOT_COPLANAR {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) : ¬Coplanar (ccCell V ul) := by
  sorry

/-- HOL `CC_CELL_NOT_COPLANAR_EXTREME` (leaf_cell.hl:2622-2640). -/
theorem CC_CELL_NOT_COPLANAR_EXTREME {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    ¬Coplanar ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pp} : Set V3) := by
  sorry

/-- HOL `CC_CELL_NOT_NULLSET` (leaf_cell.hl:2641-2661). -/
theorem CC_CELL_NOT_NULLSET {V : Set V3} {ul : List V3} (hp : Packing V)
    (hs : saturated V) (hl' : leaf V ul) : ¬nullSet (ccCell V ul) := by
  sorry

/-- HOL `CC_CELL_EXTREME_CARD` (leaf_cell.hl:2662-2678). -/
theorem CC_CELL_EXTREME_CARD {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    Nat.card ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pp} : Set V3)
      = 4 := by
  sorry

/-- HOL `CC_CELL_INDEPENDENT` (leaf_cell.hl:2679-2708). -/
theorem CC_CELL_INDEPENDENT {V : Set V3} {ul : List V3} {pp : V3}
    (hp : Packing V) (hs : saturated V) (hl' : leaf V ul)
    (hpp : pp = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0) :
    AffineIndependent ℝ (fun x : ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, pp} : Set V3) => (x : V3)) := by
  sorry

/-- HOL `CC_CELL_CONVEX_HULL_INJ` (leaf_cell.hl:2709-2731). -/
theorem CC_CELL_CONVEX_HULL_INJ {V : Set V3} {ul vl : List V3} {pu pv : V3}
    (hp : Packing V) (hs : saturated V) (hl1 : leaf V ul) (hl2 : leaf V vl)
    (hpu : pu = if ccKe V ul = 3 then mxi V (ccUh V ul) else (ccUh V ul).getD 3 0)
    (hpv : pv = if ccKe V vl = 3 then mxi V (ccUh V vl) else (ccUh V vl).getD 3 0)
    (heq : ccCell V ul = ccCell V vl) :
    ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0, pu} : Set V3)
      = {(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0, (ccUh V vl).getD 2 0, pv} := by
  sorry

/-- HOL `FUEIMOV_K` (leaf_cell.hl:2732-2749). -/
theorem FUEIMOV_K {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (heq : ccCell V ul = ccCell V vl) :
    ccKe V ul = ccKe V vl := by
  sorry

/-- HOL `LIST_OF_CC_UH` (leaf_cell.hl:2750-2764). -/
theorem LIST_OF_CC_UH {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) :
    ccUh V ul = [(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
      (ccUh V ul).getD 3 0] := by
  sorry

/-- HOL `SET_OF_LIST_CC_UH` (leaf_cell.hl:2765-2792). -/
theorem SET_OF_LIST_CC_UH {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) :
    setOfList (ccUh V ul) = {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0,
      (ccUh V ul).getD 2 0, (ccUh V ul).getD 3 0} := by
  sorry

/-- HOL `MCELL4_EXTREME_POINT` (leaf_cell.hl:2793-?). -/
theorem MCELL4_EXTREME_POINT {V : Set V3} {ul vl : List V3} (hs : saturated V)
    (hp : Packing V) (hl1 : leaf V ul) (hl2 : leaf V vl)
    (heq : ccCell V ul = ccCell V vl) (h4 : ccKe V ul = 4) :
    setOfList (ccUh V ul) = setOfList (ccUh V vl) := by
  sorry

/-- HOL `STEM_OF_LEAF` (leaf_cell.hl:2793-?). -/
theorem STEM_OF_LEAF {ul : List V3} (hl' : leaf V ul) :
    stem ul = {ul.getD 0 0, ul.getD 1 0} := by
  sorry

/-- HOL `FUEIMOV_4` (leaf_cell.hl:2793-?). -/
theorem FUEIMOV_4 {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (heq : ccCell V ul = ccCell V vl)
    (hst : stem ul = stem vl) (h4 : ccKe V ul = 4) (hne : ul ≠ vl) :
    ccUh V vl = [(ccUh V ul).getD 1 0, (ccUh V ul).getD 0 0, (ccUh V ul).getD 3 0,
      (ccUh V ul).getD 2 0] := by
  sorry

/-- HOL `MXI_NOT_IN_V` (leaf_cell.hl:2894-2948). -/
theorem MXI_NOT_IN_V {V : Set V3} {ul : List V3} (hs : saturated V) (hp : Packing V)
    (hl' : leaf V ul) (h3 : ccKe V ul = 3) : mxi V (ccUh V ul) ∉ V := by
  sorry

/-- HOL `MCELL_V_INTER_EXTREME` (leaf_cell.hl:2949-2976). -/
theorem MCELL_V_INTER_EXTREME {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    V ∩ {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
        mxi V (ccUh V ul)} = setOfList ul := by
  sorry

/-- HOL `MCELL_EXTREME_DIFF_V` (leaf_cell.hl:2977-3337). -/
theorem MCELL_EXTREME_DIFF_V {V : Set V3} {ul : List V3} (hs : saturated V)
    (hp : Packing V) (hl' : leaf V ul) (h3 : ccKe V ul = 3) :
    ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0, (ccUh V ul).getD 2 0,
        mxi V (ccUh V ul)} : Set V3) \ V = {mxi V (ccUh V ul)} := by
  sorry

/-- HOL `FUEIMOV_3` (leaf_cell.hl:2977-3337). -/
theorem FUEIMOV_3 {V : Set V3} {ul vl : List V3} (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V ul) (hl2 : leaf V vl) (h3 : ccKe V ul = 3)
    (hst : ({(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} : Set V3)
        = {(ccUh V vl).getD 0 0, (ccUh V vl).getD 1 0})
    (heq : ccCell V ul = ccCell V vl) : ul = vl := by
  sorry

/-- HOL `MCELL2_EDGE_FIRST` (leaf_cell.hl:3338-3374). -/
theorem MCELL2_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell2 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell2 V ul = mcell2 V vl := by
  sorry

/-- HOL `FINITE_CARD1_IMP_SINGLETON` (leaf_cell.hl:3338-3374). -/
theorem FINITE_CARD1_IMP_SINGLETON {α : Type*} {S : Set α}
    (h : Nat.card S = 1) : ∃ x, S = {x} := by
  sorry

/-- HOL `SET2_INSERT1` (leaf_cell.hl:3375-?). -/
theorem SET2_INSERT1 {a b x y z : V3} (hsub : ({a, b} : Set V3) ⊆ {x, y, z})
    (hne : a ≠ b) : ∃ c : V3, ({a, b, c} : Set V3) = {x, y, z} := by
  sorry

/-- HOL `MCELL3_EDGE_FIRST` (leaf_cell.hl:3375-?). -/
theorem MCELL3_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell3 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell3 V ul = mcell3 V vl := by
  sorry

/-- HOL `SET2_INSERT2` (leaf_cell.hl:3375-?). -/
theorem SET2_INSERT2 {a b w x y z : V3} (hsub : ({a, b} : Set V3) ⊆ {w, x, y, z})
    (hne : a ≠ b) (h4 : Nat.card ({w, x, y, z} : Set V3) = 4) :
    ∃ c d : V3, ({w, x, y, z} : Set V3) = {a, b, c, d} := by
  sorry

/-- HOL `MCELL4_EDGE_FIRST` (leaf_cell.hl:3375-?). -/
theorem MCELL4_EDGE_FIRST {V : Set V3} {ul : List V3} {u v : V3} (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell4 V ul)) :
    ∃ vl, barV V 3 vl ∧ u = vl.getD 0 0 ∧ v = vl.getD 1 0 ∧ mcell4 V ul = mcell4 V vl := by
  sorry

/-- HOL `MCELL_EDGE_FIRST` (leaf_cell.hl:3338-3374). -/
theorem MCELL_EDGE_FIRST {V : Set V3} {ul : List V3} {k : ℕ} {u v : V3}
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (he : {u, v} ∈ edgeX V (mcell k V ul)) :
    ∃ vl, barV V 3 vl ∧ mcell k V vl = mcell k V ul ∧ u = vl.getD 0 0 ∧
      v = vl.getD 1 0 := by
  sorry

/-- HOL `BARV3_TRUNC2` (leaf_cell.hl:3375-?). -/
theorem BARV3_TRUNC2 {V : Set V3} {ul : List V3} (hb : barV V 3 ul) :
    truncateSimplex 2 ul = [ul.getD 0 0, ul.getD 1 0, ul.getD 2 0] := by
  sorry

/-- HOL `STEM_EDGEX` (leaf_cell.hl:3375-?). -/
theorem STEM_EDGEX {V : Set V3} {ul : List V3} (hp : Packing V) (hs : saturated V)
    (hl' : leaf V ul) :
    {(ccUh V ul).getD 0 0, (ccUh V ul).getD 1 0} ∈ edgeX V (ccCell V ul) := by
  sorry

/-- HOL `FCHKUGT` (leaf_cell.hl:3432-3528). -/
theorem FCHKUGT {V : Set V3} {u0 u1 u2 u2' : V3} (hs : saturated V) (hp : Packing V)
    (hA : ccA0 [u0, u1, u2] = ccA0 [u0, u1, u2'])
    (hl1 : leaf V [u0, u1, u2]) (hl2 : leaf V [u0, u1, u2']) : u2 = u2' := by
  sorry

/-- HOL `AZIM_BASE_SHIFT_LE` (leaf_cell.hl:3529-3547). -/
theorem AZIM_BASE_SHIFT_LE (x y b1 b2 w1 w2 : V3)
    (h1 : ¬Collinear3 x y b1) (h2 : ¬Collinear3 x y b2) (h3 : ¬Collinear3 x y w1)
    (h4 : ¬Collinear3 x y w2)
    (h5 : azim x y b1 b2 ≤ azim x y b1 w1) (h6 : azim x y b1 b2 ≤ azim x y b1 w2) :
    azim x y b1 w2 - azim x y b1 w1 = azim x y b2 w2 - azim x y b2 w1 := by
  sorry

/-- HOL `WEDGE_GE_SPLIT` (leaf_cell.hl:3548-3611). -/
theorem WEDGE_GE_SPLIT (u0 u1 u2 u3 w : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hw : w ∈ wedge u0 u1 u2 u3) :
    ¬Collinear3 u0 u1 w ∧
      wedgeGe u0 u1 u2 u3 = wedgeGe u0 u1 u2 w ∪ wedgeGe u0 u1 w u3 := by
  sorry

/-- HOL `IN_CONV0_IMP_AZIM_PI_ALT` (leaf_cell.hl:3612-?). -/
theorem IN_CONV0_IMP_AZIM_PI_ALT (x e a b : V3) (h : ¬Collinear3 x e a)
    (hx : x ∈ conv0 {a, b}) : azim x e a b = Real.pi := by
  sorry

/-- HOL `AFF_GT_0_2` (leaf_cell.hl:3659-?). -/
theorem AFF_GT_0_2 (v w : V3) :
    conv0 {v, w} = {y | ∃ t2 t3 : ℝ, 0 < t2 ∧ 0 < t3 ∧ t2 + t3 = 1 ∧
      y = t2 • v + t3 • w} := by
  sorry

/-- HOL `MIDPOINT_IN_CONV0` (leaf_cell.hl:3659-?). -/
theorem MIDPOINT_IN_CONV0 (p q : V3) :
    ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) ∈ conv0 {p, q} := by
  sorry

/-- HOL `AZIM_SPLIT_POINT` (leaf_cell.hl:3612-?). -/
theorem AZIM_SPLIT_POINT (u0 u1 u2 u3 : V3)
    (h2 : ¬Collinear3 u0 u1 u2) (h3 : ¬Collinear3 u0 u1 u3)
    (hpi : Real.pi < azim u0 u1 u2 u3) :
    ∃ w, w ∈ wedge u0 u1 u2 u3 ∧ azim u0 u1 u2 w = Real.pi ∧
      azim u0 u1 w u3 < Real.pi := by
  sorry

/-- HOL `CLOSED_WEDGE_LT_PI` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE_LT_PI (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) (hpi : azim u0 u1 u2 u3 < Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `CLOSED_WEDGE_EQ_PI` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE_EQ_PI (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) (hpi : azim u0 u1 u2 u3 = Real.pi) :
    IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `CLOSED_WEDGE` (leaf_cell.hl:3659-?). -/
theorem CLOSED_WEDGE (u0 u1 u2 u3 : V3) (h2 : ¬Collinear3 u0 u1 u2)
    (h3 : ¬Collinear3 u0 u1 u3) : IsClosed (wedgeGe u0 u1 u2 u3) := by
  sorry

/-- HOL `WEDGE_INTER_AFF_GE` (leaf_cell.hl:3710-3743). -/
theorem WEDGE_INTER_AFF_GE (u0 u1 v1 v2 : V3) :
    wedge u0 u1 v1 v2 ∩ affGe {u0, u1} {v1} = ∅ ∧
      wedge u0 u1 v1 v2 ∩ affGe {u0, u1} {v2} = ∅ := by
  sorry

/-- HOL `AFF_GE_SUBSET_WEDGE_GE` (leaf_cell.hl:3744-3766). -/
theorem AFF_GE_SUBSET_WEDGE_GE (u0 u1 v1 v2 : V3) (h1 : ¬Collinear3 u0 u1 v1)
    (h2 : ¬Collinear3 u0 u1 v2) :
    affGe {u0, u1} {v1} ⊆ wedgeGe u0 u1 v1 v2 ∧ affGe {u0, u1} {v2} ⊆ wedgeGe u0 u1 v1 v2 := by
  sorry

/-- HOL `BDXKHTW_PREP_LEMMA` (leaf_cell.hl:3767-3903). -/
theorem BDXKHTW_PREP_LEMMA {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0)
    (hy : ∃ y, y ∈ X ∩ wedge u0 u1 v1 v2)
    (hx : ∃ x, x ∈ X ∧ x ∉ wedgeGe u0 u1 v1 v2) :
    Convex ℝ X ∧ u0 ≠ u1 ∧ ¬Collinear3 u0 u1 v1 ∧ ¬Collinear3 u0 u1 v2 ∧
      ∃ p q, p ∈ X ∩ wedge u0 u1 v1 v2 ∧ q ∈ X \ wedgeGe u0 u1 v1 v2 ∧
        ¬Coplanar ({p, q, u0, u1} : Set V3) ∧
        p ∉ affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} ∧
        q ∉ affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} := by
  sorry

/-- HOL `WEDGE_SUBSET_WEDGE_GE` (leaf_cell.hl:3904-3912). -/
theorem WEDGE_SUBSET_WEDGE_GE (u0 u1 u2 u3 : V3) :
    wedge u0 u1 u2 u3 ⊆ wedgeGe u0 u1 u2 u3 := by
  intro y hy
  exact ⟨le_of_lt hy.2.1, le_of_lt hy.2.2⟩

/-- HOL `AFF_INTER_IMP_COPLANAR` (leaf_cell.hl:3913-3963). -/
theorem AFF_INTER_IMP_COPLANAR (a b c d : V3)
    (h : (affineSpan ℝ {a, b} : Set V3) ∩ (affineSpan ℝ {c, d} : Set V3) ≠ ∅) :
    Coplanar ({a, b, c, d} : Set V3) := by
  sorry

/-- HOL `NOT_COLLINEAR_AFF_DIM2` is proved above; `ADD_NN_ZERO` here. -/
theorem ADD_NN_ZERO (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : a * x + b * y = 0) : x = 0 ∧ y = 0 := by
  have h5 : 0 ≤ a * x := mul_nonneg ha.le hx
  have h6 : 0 ≤ b * y := mul_nonneg hb.le hy
  have hax : a * x = 0 := by linarith
  have hby : b * y = 0 := by linarith
  exact ⟨by
    rcases mul_eq_zero.1 hax with h7 | h7
    · exact absurd h7 ha.ne'
    · exact h7,
    by
      rcases mul_eq_zero.1 hby with h7 | h7
      · exact absurd h7 hb.ne'
      · exact h7⟩

/-- HOL `BDXKHTW` (leaf_cell.hl:3984-4166). -/
theorem BDXKHTW {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0)
    (hy : ∃ y, y ∈ X ∩ wedge u0 u1 v1 v2) :
    X ⊆ wedgeGe u0 u1 v1 v2 := by
  sorry

/-- HOL `AZIM_POS_IMP_SUM_2PI_ALT` (leaf_cell.hl:4167-?). -/
theorem AZIM_POS_IMP_SUM_2PI_ALT (a b c d : V3) (h : 0 < azim a b c d) :
    azim a b c d + azim a b d c = 2 * Real.pi := by
  sorry

/-- HOL `WEDGE_GE_COMPLEMENT` (leaf_cell.hl:4167-4201). -/
theorem WEDGE_GE_COMPLEMENT (u0 u1 v1 v2 : V3) (h : azim u0 u1 v1 v2 ≠ 0) :
    (Set.univ : Set V3) \ wedgeGe u0 u1 v1 v2 = wedge u0 u1 v2 v1 := by
  sorry

/-- HOL `WEDGE_COMPLEMENT` (leaf_cell.hl:4202-4215). -/
theorem WEDGE_COMPLEMENT (u0 u1 v1 v2 : V3) (h : azim u0 u1 v1 v2 ≠ 0) :
    (Set.univ : Set V3) \ wedge u0 u1 v1 v2 = wedgeGe u0 u1 v2 v1 := by
  sorry

/-- HOL `EWYBJUA` (leaf_cell.hl:4216-4306): two cells sharing a leaf stem lie
on azimuthal sides of the stem. -/
theorem EWYBJUA {V : Set V3} {X : Set V3} {u0 u1 v1 v2 : V3}
    (hs : saturated V) (hp : Packing V)
    (hl1 : leaf V [u0, u1, v1]) (hl2 : leaf V [u0, u1, v2])
    (hX : X ∈ mcellSet V) (he : {u0, u1} ∈ edgeX V X)
    (haz : azim u0 u1 v1 v2 ≠ 0) :
    X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1 := by
  sorry

/-! ## sum_gamma.hl: the UPFZBZM support estimate -/

/-- HOL `SUM_GAMMAX_LMFUN_ESTIMATE` (sum_gamma.hl:62-1465): the 1400-line
lemma chain is `sorry` (uses `BOUND_GAMMA_X_lmfun`, `CARD_MCELL_CONTAINS_POINT_klemma`,
`Bump.BOUND_BETA_BUMP`, the cluster-sum split `T1/T2/T3`, etc.). Note the
DISCHARGE convention vs PackingAuto2 concl theorems: this is only a *support
lemma* for UPFZBZM — it matches neither `UPFZBZM_concl`, `RDWKARC_concl`,
`GOTCJAH_concl` nor `TIWWFYQ_concl`, which therefore remain `sorry` in
PackingAuto2. `TSKAJXY_statement` itself is byte-identical to PackingAuto2's
encoding and is reused, not redefined. -/
theorem SUM_GAMMAX_LMFUN_ESTIMATE : SUM_GAMMAX_LMFUN_ESTIMATE_concl := by
  sorry

end
end Kepler.Text
