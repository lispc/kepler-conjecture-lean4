/-
LocalAuto7: port of `scripts/local/polar_fan.hl` (Flyspeck "polar fan"
formalization, module `Polar_fan`; 3362 lines, 2 defs + 49 theorems).

FILE MAP
  The file is the POLAR-FAN DUALITY chapter of the local-fan development.
  (a) Geometric groundwork: azimuth/arc/dihedral kit (`DIHV_ARCV`,
      `AZIM_DIHV_SAME_STRONG`, `AZIM_ARCV`), plane/hull kit
      (`PLANE_AFFINE_HULL_3`, `AFFINE_HULL_3_GENERATED`), azimuth
      degeneracy (`COLLINEAR_AZIM_0_OR_PI`), angle additivity on cones
      (`ANGLES_ADD_AFF_GE`).
  (b) The aff_ge cone lemmas driving the polar construction:
      `AFF_GE_SCALE_LEMMA`, `AZIM_SAME_WITHIN_AFF_GE(_ALT)`,
      `COLLINEAR_WITHIN_AFF_GE_COLLINEAR`,
      `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE`, `UNION_AFF_GE_1_2`.
  (c) Cycle/iteration kit on the rho orbit (`AZIM_CYCLE_*`,
      `IVS_AZIM_CYCLE_*`, `RHO_NODE1_INJECTIVE`, the orbit-map lemmas,
      `ITER_(IVS_)RHO_IDD`, `LOFA_IMP_ITER_IVS_RHO_NODE_ID`), the
      hyp-function characterizations (`nnOfHyp3`/`ffOfHyp3`/`eeOfHyp3`),
      cyclicity sums (`ORDER_AZIM_SUM2Pi_0`), local-fan cardinal facts,
      sin/cross sign kit (`SIN_AZIM_MUTUAL_CROSS`,
      `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS(_ALT)`).
  (d) fan7/FAN economizations (`GMLWKPK`, `GMLWKPK_ALT`,
      `FAN_ECONOMIZED`, `FAN7_AFF_GT_CONDITION`, `FAN_AFF_GT_CONDITION`,
      `GMLWKPK_SIMPLE`, `FAN_ECONOMIZED_SIMPLE`).
  (e) The polar fan itself: `polarFan` (HOL `JNVXCRC`), its fundamental
      duality property `BGMIFTE` (the polar fan of a convex local fan is
      again a convex local fan; arc ↔ interior-angle duality), and the
      perimeter lane: `fanPerimeter` (HOL `IQCPCGW`), invariance
      (`FAN_PERIMETER_INVARIANT`, `FAN_PERIMETER_INVARIANT_CARD_V`,
      `FAN_PERIMETER`) and the 2*pi bound `WSEWPCH`.

ENCODING NOTES (polar fan ↔ local fan duality)
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `ITER n f x` ↔
    `f^[n] x` (`Function.iterate`); `@v. v IN V` ↔ `Classical.epsilon`;
    `CARD s` ↔ `Set.ncard` (junk 0 on infinite sets, as in HOL);
    `sum (0..n) g` ↔ `∑ i ∈ Finset.Ico 0 (n+1)`; the `CARD FF - 1`
    truncation in `fan_perimeter` is kept verbatim via natural
    subtraction: `Finset.range ((FF.ncard : ℕ) - 1 + 1)`.
  - HOL `cross` ↔ `cross3` (Mathlib `crossProduct` lifted over the
    `WithLp` type synonym; the TopologyFan copy is private there, so a
    module-local copy is made here).  HOL `orthogonal a b` is rendered
    pointwise as `a ⬝ᵥ b = 0`.
  - The Wrgcvdr_cizmrrh/Sphere vocabulary is ported here as the module's
    own `_p7` copies (bodies copied verbatim from the `_p2` lane in
    LocalAuto2): `azim_cycle` ↦ `azimCycle_p7`, `ivs_azim_cycle` ↦
    `ivsAzimCycle_p7`, `nn_of_hyp`/`ff_of_hyp`/`ee_of_hyp` ↦
    `nnOfHyp_p7`/`ffOfHyp_p7`/`eeOfHyp_p7`, `darts_of_hyp` ↦
    `dartsOfHyp_p7`,     `EE` ↦ LocalAuto1's `ee`, `plane` ↦ `plane_p7`.
    DEDUP (atn2-merge pass): the old blocker ("LocalAuto2 is NOT importable
    next to LocalAuto1 — both lanes own `Kepler.Text.atn2`") is RESOLVED:
    `atn2` is single-sourced in `Kepler.Text.SphereKit` (imported via
    LocalAuto1), and LocalAuto1/LocalAuto2 are co-importable.  However the
    shared localization kit (`EE`/`azim_cycle`/`azim_in_fan`) is DEFERRED in
    SphereKit (no rendering bridge yet), so the `_p7` copies — and the
    `ee` references, which still resolve to LocalAuto1's `ee` — remain
    until the fan-kit bridge lands (plan §6).  No hosted twin here; pass
    is otherwise a no-op.
  - `local_fan`/`convex_local_fan` ↦ LocalAuto1's `LocalFan` /
    `ConvexLocalFan` (whose hypermap kit is still a registry stub), so
    every theorem whose HOL proof consumes local-fan content carries a
    faithful STATEMENT with `sorry` body — DISCHARGES convention: the
    Local-Fan chapter discharges them when the hypermap kit lands, with
    the statements unchanged.  `interior_angle1` ↦ `interiorAngle1`;
    `rho_node1`/`ivs_rho_node1` ↦ `rhoNode1`/`ivsRhoNode1`;
    `generic`/`circular`/`lunar` ↦ `Generic`/`Circular`/`Lunar`;
    `graph`/`fan1`/`fan2`/`fan6`/`fan7`/`FAN` ↦ `Kepler.Text.Fan`'s
    `Graph`/`fan1`/`fan2`/`fan6`/`fan7`/`FAN`; `aff_ge`/`aff_gt`/
    `aff_lt` ↦ `affGe`/`affGt`/`affLt` (Kepler.Geom.Aff); HOL
    `angle(v,u,x)` ↦ `EuclideanGeometry.angle v u x`; `sum V f` over a
    set ↦ `setSum` (PackingAuto2, junk 0 on infinite sets).
  - The 15 mechanical theorems are PROVED here: `DIHV_ARCV`,
    `AZIM_DIHV_SAME_STRONG`, `AZIM_ARCV`, `PLANE_AFFINE_HULL_3`,
    `AZIM_CYCLE_BASIC_PROPERTIES`, `AZIM_CYCLE_TWO_POINT_SET_ALT`,
    `IVS_AZIM_CYCLE_TWO_POINT_SET`, `IVS_AZIM_CYCLE_TWO_POINT_SET_ALT`,
    `AZIM_CYCLE_SING`, `IVS_AZIM_CYCLE_SING`, `nnOfHyp3`, `ffOfHyp3`,
    `eeOfHyp3`, `FAN_ECONOMIZED`, `FAN_ECONOMIZED_SIMPLE` (the latter
    two by propositional transport through `GMLWKPK`/`GMLWKPK_SIMPLE`).
    NO `native_decide` anywhere.

DISCHARGES: the sorry'd theorems are the polar-fan chapter contract
(`BGMIFTE`, `WSEWPCH`, the orbit/perimeter lemmas and the fan7/FAN
economizations); they are discharged from the Local-Fan foundation with
the statements below unchanged.
-/

import Kepler.Geom.Aff
import Kepler.Geom.LuneVolume
import Kepler.Text.Fan
import Kepler.Text.LocalAuto1
import Kepler.Text.PackingAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## Cross product (HOL `cross`) -/

/-- HOL `cross` (`real^3` cross product) on `V3` — this is PackingAuto18's
`cross3` (imported; a module-local copy would clash).  Coercion kit for
the `WithLp` type synonym, mirroring `Kepler.Geom`: -/
private theorem coe_cross3P (a b : V3) :
    ((cross3 a b : V3) : Fin 3 → ℝ) = crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ) :=
  rfl

/-- Canonical dot on `V3` (both arguments coerced whole to the
`Fin 3 → ℝ` identification); module-internal carrier keeping coercion
forms stable under `rw` (HOL `x dot y`). -/
@[reducible] private def dotV (x y : V3) : ℝ := ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ)

private theorem coe_smulP (t : ℝ) (a : V3) : ((t • a : V3) : Fin 3 → ℝ) = t • ((a : V3) : Fin 3 → ℝ) := rfl
private theorem coe_subP (a b : V3) : ((a - b : V3) : Fin 3 → ℝ) = ((a : V3) : Fin 3 → ℝ) - ((b : V3) : Fin 3 → ℝ) := rfl
private theorem coe_zeroV : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl
private theorem smul_dotP (t : ℝ) (a b : Fin 3 → ℝ) :
    (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := smul_dotProduct t a b
private theorem dot_smulP (a : Fin 3 → ℝ) (t : ℝ) (b : Fin 3 → ℝ) :
    a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) := dotProduct_smul t a b

/-! ## Wrgcvdr vocabulary, `_p7` copies (localization.hl:38-63) -/

/-- HOL `azim_cycle` (sphere.hl:414; minimal azimuth, distance tiebreak,
`W SUBSET {p}` degenerate case).  `_p7` module-local copy, see the
encoding notes; HOL `projection (w-v) (u-v)` ↔ repo
`projection (u - v) (w - v)`. -/
noncomputable def azimCycle_p7 (W : Set V3) (v w p : V3) : V3 :=
  if W ⊆ {p} then p
  else
    Classical.epsilon fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
      azim v w p u < azim v w p q ∨
        azim v w p u = azim v w p q ∧
          ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖

/-- HOL `ivs_azim_cycle W v0 v w` (localization.hl:55). -/
noncomputable def ivsAzimCycle_p7 (W : Set V3) (v0 v w : V3) : V3 :=
  if W = ∅ then w else Classical.epsilon fun x => x ∈ W ∧ azimCycle_p7 W v0 v x = w

/-- HOL `darts_of_hyp E V` (localization.hl:45) =
`ord_pairs E ∪ self_pairs E V`. -/
def dartsOfHyp_p7 {α : Type*} (E : Set (Set α)) (V : Set α) : Set (α × α) :=
  {p | {p.1, p.2} ∈ E} ∪ {p | p.1 = p.2 ∧ p.1 ∈ V}

/-- HOL `ee_of_hyp (x,V,E)` (localization.hl:48). -/
noncomputable def eeOfHyp_p7 (_x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.2, d.1) else d

/-- HOL `nn_of_hyp (x,V,E)` (localization.hl:51). -/
noncomputable def nnOfHyp_p7 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.1, azimCycle_p7 (ee d.1 E) x d.1 d.2) else d

/-- HOL `ff_of_hyp (x,V,E)` (localization.hl:59). -/
noncomputable def ffOfHyp_p7 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : V3 × V3) :
    V3 × V3 :=
  if d ∈ dartsOfHyp_p7 E V then (d.2, ivsAzimCycle_p7 (ee d.2 E) x d.2 d.1) else d

/-- HOL `plane` (sphere.hl:345): spanned by three non-collinear points. -/
def plane_p7 (A : Set V3) : Prop :=
  ∃ u v w : V3, ¬ Collinear ℝ ({u, v, w} : Set V3) ∧ A = affineSpan ℝ ({u, v, w} : Set V3)

/-! ## W1 discharge kit (`p7w_*` private helpers; WSEWPCH wave W1) -/

section W1Kit

/-- V3 点积经 `Fin 3 → ℝ` 强制转换不变（PolyAuto7 `p7_dot_pi` 同款）。 -/
private theorem p7w_dot_coe {x y : V3} :
    x ⬝ᵥ y = ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y : V3) : Fin 3 → ℝ) := by
  have h1 : x = WithLp.toLp 2 ((x : V3) : Fin 3 → ℝ) := (WithLp.toLp_ofLp 2 x).symm
  rw [h1, dot_toLp]

/-- V3 向量等式的强制转换传输（coe 单射）。 -/
private theorem p7w_v3_eq {x y : V3}
    (h : ((x : V3) : Fin 3 → ℝ) = ((y : V3) : Fin 3 → ℝ)) : x = y := by
  calc x = WithLp.toLp 2 ((x : V3) : Fin 3 → ℝ) := (WithLp.toLp_ofLp 2 x).symm
    _ = WithLp.toLp 2 ((y : V3) : Fin 3 → ℝ) := by rw [h]
    _ = y := WithLp.toLp_ofLp 2 y

/-- 退化共线三元组（第 1、2 点重合）。 -/
private theorem p7w_col_112 (x y : V3) : Collinear3 x x y := collinear3_of_eq rfl

/-- 退化共线三元组（第 2、3 点重合）。 -/
private theorem p7w_col_122 (x y : V3) : Collinear3 x y y := by
  by_cases h : y = x
  · exact collinear3_of_eq h
  · exact (collinear3_iff_smul h).mpr ⟨1, by simp⟩

/-- 退化共线三元组（第 1、3 点重合）。 -/
private theorem p7w_col_131 (x y : V3) : Collinear3 x y x := by
  by_cases h : y = x
  · exact collinear3_of_eq h
  · exact (collinear3_iff_smul h).mpr ⟨0, by simp⟩

/-- 共线三元组的后两点交换。 -/
private theorem p7w_col_swap (x y z : V3) (h : Collinear3 x z y) : Collinear3 x y z := by
  unfold Collinear3 at h ⊢
  have hset : ({x, z, y} : Set V3) = ({x, y, z} : Set V3) := by
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [hset] at h

/-- 非共线前提给出的第 1、2 点互异。 -/
private theorem p7w_ncol_ne12 {a b c : V3} (h : ¬ Collinear3 a b c) : a ≠ b :=
  fun he => h (by rw [he]; exact collinear3_of_eq rfl)

/-- 非共线前提给出的第 1、3 点互异。 -/
private theorem p7w_ncol_ne13 {a b c : V3} (h : ¬ Collinear3 a b c) : a ≠ c :=
  fun he => h (by rw [he]; exact p7w_col_131 c b)

/-- 非共线前提给出的第 2、3 点互异。 -/
private theorem p7w_ncol_ne23 {a b c : V3} (h : ¬ Collinear3 a b c) : b ≠ c :=
  fun he => h (by rw [he]; exact p7w_col_122 a c)

/-- `+ᵥ` 在 V3 上即向量加法（PolyAuto2 同款）。 -/
private theorem p7w_vadd_eq_add (v p : V3) : v +ᵥ p = v + p := rfl

/-- 共线的平移不变性。 -/
private theorem p7w_collinear_translate (t : V3) (s : Set V3) :
    Collinear ℝ ((fun z : V3 => z + t) '' s) ↔ Collinear ℝ s := by
  constructor
  · intro hcol
    obtain ⟨p₀, vec, hall⟩ :=
      (collinear_iff_exists_forall_eq_smul_vadd ((fun z : V3 => z + t) '' s)).mp hcol
    refine (collinear_iff_exists_forall_eq_smul_vadd s).mpr ⟨p₀ - t, vec, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := hall (p + t) (Set.mem_image_of_mem _ hp)
    rw [p7w_vadd_eq_add] at hr
    refine ⟨r, ?_⟩
    show p = r • vec + (p₀ - t)
    have hp2 : p = (p + t) - t := by abel
    rw [hp2, hr]
    abel
  · intro hcol
    obtain ⟨p₀, vec, hall⟩ := (collinear_iff_exists_forall_eq_smul_vadd s).mp hcol
    refine (collinear_iff_exists_forall_eq_smul_vadd _).mpr ⟨p₀ + t, vec, fun p' hp' => ?_⟩
    obtain ⟨p, hp, hp'eq⟩ := hp'
    obtain ⟨r, hr⟩ := hall p hp
    rw [p7w_vadd_eq_add] at hr
    have hp't : p' = p + t := hp'eq.symm
    refine ⟨r, ?_⟩
    show p' = r • vec + (p₀ + t)
    rw [hp't, hr]
    abel

/-- `Collinear3` 的平移不变性。 -/
private theorem p7w_collinear3_translate (t : V3) (v w w1 : V3) :
    Collinear3 (v + t) (w + t) (w1 + t) ↔ Collinear3 v w w1 := by
  unfold Collinear3
  have himg : ({v + t, w + t, w1 + t} : Set V3)
      = (fun z : V3 => z + t) '' ({v, w, w1} : Set V3) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro h
      obtain h | h | h := h
      · exact ⟨v, Or.inl rfl, h.symm⟩
      · exact ⟨w, Or.inr (Or.inl rfl), h.symm⟩
      · exact ⟨w1, Or.inr (Or.inr rfl), h.symm⟩
    · rintro ⟨x, hx, hx'⟩
      have hzx : z = x + t := by rw [← hx']
      rcases hx with rfl | rfl | rfl
      · exact Or.inl hzx
      · exact Or.inr (Or.inl hzx)
      · exact Or.inr (Or.inr hzx)
  rw [himg]
  exact p7w_collinear_translate t _

/-- `AzimSpec` 的平移不变性（体由逐项差向量重排给出）。 -/
private theorem p7w_azimSpec_translate (t : V3) (v w w1 w2 : V3) (θ : ℝ) :
    AzimSpec (v + t) (w + t) (w1 + t) (w2 + t) θ ↔ AzimSpec v w w1 w2 θ := by
  have hab : ((w + t) - (v + t) : V3) = w - v := by abel
  have he1 : ((w1 + t) - (v + t) : V3) = w1 - v := by abel
  have he2 : ((w2 + t) - (v + t) : V3) = w2 - v := by abel
  have hdist : dist (w + t) (v + t) = dist w v := by
    rw [dist_eq_norm, dist_eq_norm, hab]
  constructor
  · rintro ⟨h0, h2π, hk1, hk2, hframe⟩
    refine ⟨h0, h2π, hk1, hk2, fun e1 e2 e3 he hax hwv => ?_⟩
    obtain ⟨psi, r1, r2, hre1, hre2, hr1, hr2⟩ :=
      hframe e1 e2 e3 he (by rw [hab, hdist]; exact hax)
        (fun hne => hwv (add_right_cancel hne))
    rw [he1, hab] at hre1
    rw [he2, hab] at hre2
    exact ⟨psi, r1, r2, hre1, hre2, hr1, hr2⟩
  · rintro ⟨h0, h2π, hk1, hk2, hframe⟩
    refine ⟨h0, h2π, hk1, hk2, fun e1 e2 e3 he hax hwv => ?_⟩
    have hax' : (w - v : V3) = dist w v • e3 := by rw [← hab, ← hdist]; exact hax
    have hwv' : w ≠ v := fun he => hwv (by rw [he])
    obtain ⟨psi, r1, r2, hre1, hre2, hr1, hr2⟩ := hframe e1 e2 e3 he hax' hwv'
    rw [← he1, ← hab] at hre1
    rw [← he2, ← hab] at hre2
    exact ⟨psi, r1, r2, hre1, hre2, hr1, hr2⟩

/-- `azim` 的平移不变性。 -/
private theorem p7w_azim_translate (t : V3) (v w w1 w2 : V3) :
    azim (v + t) (w + t) (w1 + t) (w2 + t) = azim v w w1 w2 := by
  unfold azim
  by_cases hcol : Collinear3 (v + t) (w + t) (w1 + t) ∨ Collinear3 (v + t) (w + t) (w2 + t)
  · have h1 : Collinear3 v w w1 ∨ Collinear3 v w w2 := by
      rcases hcol with h | h
      · exact Or.inl ((p7w_collinear3_translate t v w w1).mp h)
      · exact Or.inr ((p7w_collinear3_translate t v w w2).mp h)
    rw [if_pos h1, if_pos hcol]
  · have h1 : ¬ (Collinear3 v w w1 ∨ Collinear3 v w w2) := by
      intro hc
      apply hcol
      rcases hc with h | h
      · exact Or.inl ((p7w_collinear3_translate t v w w1).mpr h)
      · exact Or.inr ((p7w_collinear3_translate t v w w2).mpr h)
    rw [if_neg h1, if_neg hcol]
    have hpredeq : AzimSpec (v + t) (w + t) (w1 + t) (w2 + t) = AzimSpec v w w1 w2 :=
      funext fun θ => propext (p7w_azimSpec_translate t v w w1 w2 θ)
    rw [hpredeq]

/-- 方位角正弦为零 ⟹ 值为 0 或 π（值域夹逼）。 -/
private theorem p7w_azim_sin_zero {v w w1 w2 : V3}
    (h : Real.sin (azim v w w1 w2) = 0) : azim v w w1 w2 = 0 ∨ azim v w w1 w2 = Real.pi := by
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hm0 : (0:ℤ) ≤ m := by
    by_contra hcon
    push_neg at hcon
    have hmle : ((m:ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : (m : ℤ) ≤ -1)
    have hθ : azim v w w1 w2 < 0 := by rw [← hm]; nlinarith [hmle, hpi]
    exact absurd (azim_nonneg v w w1 w2) (not_le.mpr hθ)
  have hm2 : m < 2 := by
    by_contra hcon
    push_neg at hcon
    have hmge : (2:ℝ) ≤ ((m:ℤ) : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ m)
    have hθ : 2 * Real.pi ≤ azim v w w1 w2 := by rw [← hm]; nlinarith [hmge, hpi]
    exact absurd hθ (not_le.mpr (azim_lt_two_pi v w w1 w2))
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · exact Or.inl (by rw [← hm]; push_cast; norm_num)
  · exact Or.inr (by rw [← hm]; push_cast; norm_num)

/-- `cross3` 与零向量的叉积为零（第一变元）。 -/
private theorem p7w_cross3_zero_left (v : V3) : cross3 (0:V3) v = 0 := by
  refine p7w_v3_eq ?_
  rw [coe_cross3P, coe_zeroV]
  ext i
  fin_cases i <;> simp [cross_apply]

/-- `cross3 u (c • u) = 0`（平行向量叉积消灭）。 -/
private theorem p7w_cross3_smul_right_self (u : V3) (c : ℝ) : cross3 u (c • u) = 0 := by
  refine p7w_v3_eq ?_
  rw [coe_cross3P, coe_smulP, coe_zeroV]
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

/-- `affGe {a} {p,q}` 锥成员的非负系数分解（提取方向；p、q 均异于顶点 a）。 -/
private theorem p7w_affGe_pair_extract {a p q y : V3} (hpa : p ≠ a) (hqa : q ≠ a)
    (hmem : y ∈ affGe ({a} : Set V3) ({p, q})) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ y - a = r • (p - a) + s • (q - a) := by
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hmem
  obtain ⟨f, hfin, hvec, hsgn, hone⟩ := hmem
  by_cases hpq : p = q
  · subst hpq
    have hTeq : hfin.toFinset = ({a, p} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa]), Finset.sum_singleton] at hvec hone
    have hfp : 0 ≤ f p := hsgn p (by simp)
    have hfa : f a = 1 - f p := by linarith
    refine ⟨f p, 0, hfp, by positivity, ?_⟩
    rw [hvec, hfa, sub_smul, one_smul, zero_smul, smul_sub]
    abel
  · have hTeq : hfin.toFinset = ({a, p, q} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      first | tauto | skip
    rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa, Ne.symm hqa]),
      Finset.sum_insert (by simp [hpq]), Finset.sum_singleton] at hvec hone
    have hfp : 0 ≤ f p := hsgn p (by simp)
    have hfq : 0 ≤ f q := hsgn q (by simp)
    have hfa : f a = 1 - f p - f q := by linarith
    refine ⟨f p, f q, hfp, hfq, ?_⟩
    rw [hvec, hfa, sub_smul, sub_smul, one_smul, smul_sub, smul_sub]
    abel

/-- `affGe {a} {p,q}` 锥成员的非负系数分解（构造方向；p、q 均异于顶点 a）。 -/
private theorem p7w_affGe_pair_intro {a p q y : V3} (hpa : p ≠ a) (hqa : q ≠ a)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hy : y - a = r • (p - a) + s • (q - a)) :
    y ∈ affGe ({a} : Set V3) ({p, q}) := by
  by_cases hpq : p = q
  · subst hpq
    have hfin : (({a} ∪ {p, p} : Set V3)).Finite :=
      (Set.finite_singleton a).union ((Set.finite_singleton p).insert p)
    have hTeq : hfin.toFinset = ({a, p} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      first | tauto | skip
    set f : V3 → ℝ := fun z => if z = p then r + s else 1 - r - s with hfdef
    have hfp : f p = r + s := by rw [hfdef]; simp
    have hfa : f a = 1 - r - s := by rw [hfdef]; simp [Ne.symm hpa]
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa]), Finset.sum_singleton, hfa, hfp]
      have hy2 : y = a + (y - a) := by abel
      rw [hy2, hy]
      module
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> rw [hfp] <;> exact add_nonneg hr hs
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa]), Finset.sum_singleton, hfa, hfp]
      ring
  · have hfin : (({a} ∪ {p, q} : Set V3)).Finite :=
      (Set.finite_singleton a).union ((Set.finite_singleton q).insert p)
    have hTeq : hfin.toFinset = ({a, p, q} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      first | tauto | skip
    set f : V3 → ℝ := fun z => if z = p then r else if z = q then s else 1 - r - s with hfdef
    have hfp : f p = r := by rw [hfdef]; simp
    have hfq : f q = s := by rw [hfdef]; simp [Ne.symm hpq]
    have hfa : f a = 1 - r - s := by rw [hfdef]; simp [Ne.symm hpa, Ne.symm hqa]
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa, Ne.symm hqa]),
        Finset.sum_insert (by simp [hpq]), Finset.sum_singleton, hfa, hfp, hfq]
      have hy2 : y = a + (y - a) := by abel
      rw [hy2, hy]
      module
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hfp]; exact hr
      · rw [hfq]; exact hs
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa, Ne.symm hqa]),
        Finset.sum_insert (by simp [hpq]), Finset.sum_singleton, hfa, hfp, hfq]
      ring

/-- `affLt {a} {p}` 负射线成员的构造方向（p 异于顶点 a）。 -/
private theorem p7w_affLt_singleton_intro {a p y : V3} (hpa : p ≠ a) {t : ℝ} (ht : t < 0)
    (hy : y - a = t • (p - a)) : y ∈ affLt ({a} : Set V3) ({p} : Set V3) := by
  have hfin : (({a} ∪ {p} : Set V3)).Finite :=
    (Set.finite_singleton a).union (Set.finite_singleton p)
  have hTeq : hfin.toFinset = ({a, p} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    first | tauto | skip
  set f : V3 → ℝ := fun z => if z = p then t else 1 - t with hfdef
  have hfp : f p = t := by rw [hfdef]; simp
  have hfa : f a = 1 - t := by rw [hfdef]; simp [Ne.symm hpa]
  refine ⟨f, hfin, ?_, ?_, ?_⟩
  · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa]), Finset.sum_singleton, hfa, hfp]
    have hy2 : y = a + (y - a) := by abel
    rw [hy2, hy]
    module
  · intro z hz
    simp only [Set.mem_singleton_iff] at hz
    rcases hz with rfl
    rw [hfp]
    exact ht
  · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hpa]), Finset.sum_singleton, hfa, hfp]
    ring

/-- `affGe {0} {p,q}` 锥成员的非负系数分解（提取方向；p、q 均非零）。 -/
private theorem p7w_affGe_pair_extract0 {p q y : V3} (hp : p ≠ 0) (hq : q ≠ 0)
    (hmem : y ∈ affGe ({0} : Set V3) ({p, q})) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ y = r • p + s • q := by
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hmem
  obtain ⟨f, hfin, hvec, hsgn, hone⟩ := hmem
  by_cases hpq : p = q
  · subst hpq
    have hTeq : hfin.toFinset = ({0, p} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      first | tauto | skip
    rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp]), Finset.sum_singleton] at hvec
    have hfp : 0 ≤ f p := hsgn p (by simp)
    refine ⟨f p, 0, hfp, by positivity, ?_⟩
    rw [hvec, smul_zero, zero_add, zero_smul, add_zero]
  · have hTeq : hfin.toFinset = ({0, p, q} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      first | tauto | skip
    rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp, Ne.symm hq]),
      Finset.sum_insert (by simp [hpq]), Finset.sum_singleton] at hvec
    have hfp : 0 ≤ f p := hsgn p (by simp)
    have hfq : 0 ≤ f q := hsgn q (by simp)
    refine ⟨f p, f q, hfp, hfq, ?_⟩
    rw [hvec, smul_zero, zero_add]

/-- `affGe {0} {p,q}` 锥成员的非负系数分解（构造方向；p、q 均非零）。 -/
private theorem p7w_affGe_pair_intro0 {p q y : V3} (hp : p ≠ 0) (hq : q ≠ 0)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hy : y = r • p + s • q) :
    y ∈ affGe ({0} : Set V3) ({p, q}) := by
  have hfin : (({0} ∪ {p, q} : Set V3)).Finite :=
    (Set.finite_singleton 0).union ((Set.finite_singleton q).insert p)
  have hTeq : hfin.toFinset = ({0, p, q} : Finset V3) := by
    ext z
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    first | tauto | skip
  by_cases hpq : p = q
  · subst hpq
    set f : V3 → ℝ := fun z => if z = p then r + s else 1 - r - s with hfdef
    have hfp : f p = r + s := by rw [hfdef]; simp
    have hf0 : f 0 = 1 - r - s := by rw [hfdef]; simp [Ne.symm hp]
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp])]
      rw [show ({p, p} : Finset V3) = ({p} : Finset V3) from by simp, Finset.sum_singleton,
        hf0, hfp, smul_zero, zero_add]
      rw [← add_smul] at hy
      exact hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> rw [hfp] <;> exact add_nonneg hr hs
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp])]
      rw [show ({p, p} : Finset V3) = ({p} : Finset V3) from by simp, Finset.sum_singleton,
        hf0, hfp]
      ring
  · set f : V3 → ℝ := fun z => if z = p then r else if z = q then s else 1 - r - s
      with hfdef
    have hfp : f p = r := by rw [hfdef]; simp
    have hfq : f q = s := by rw [hfdef]; simp [Ne.symm hpq]
    have hf0 : f 0 = 1 - r - s := by rw [hfdef]; simp [Ne.symm hp, Ne.symm hq]
    refine ⟨f, hfin, ?_, ?_, ?_⟩
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp, Ne.symm hq]),
        Finset.sum_insert (by simp [hpq]), Finset.sum_singleton, hf0, hfp, hfq,
        smul_zero, zero_add]
      exact hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hfp]; exact hr
      · rw [hfq]; exact hs
    · rw [hTeq, Finset.sum_insert (by simp [Ne.symm hp, Ne.symm hq]),
        Finset.sum_insert (by simp [hpq]), Finset.sum_singleton, hf0, hfp, hfq]
      ring

end W1Kit

/-! ## Some natural lemmas (polar_fan.hl:11-100) -/

/-- HOL `DIHV_ARCV` (polar_fan.hl:11). -/
theorem DIHV_ARCV {e u v w : V3} (h1 : (e - u) ⬝ᵥ (v - u) = 0)
    (h2 : (e - u) ⬝ᵥ (w - u) = 0) (he : e ≠ u) : dihV u e v w = arcV u v w := by
  have hcn : 0 < ‖(e - u : V3)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hc : 0 < dotV (e - u) (e - u) := by
    rw [show dotV (e - u) (e - u)
          = ‖(e - u : V3)‖ ^ 2 from (norm_sq_eq_dot (e - u : V3)).symm]
    exact pow_pos hcn 2
  have h1' : dotV (v - u) (e - u) = 0 := by
    show ((v - u : V3) : Fin 3 → ℝ) ⬝ᵥ ((e - u : V3) : Fin 3 → ℝ) = 0
    rw [dotProduct_comm]
    exact h1
  have h2' : dotV (w - u) (e - u) = 0 := by
    show ((w - u : V3) : Fin 3 → ℝ) ⬝ᵥ ((e - u : V3) : Fin 3 → ℝ) = 0
    rw [dotProduct_comm]
    exact h2
  unfold dihV
  dsimp only
  show arcV 0 (dotV (e - u) (e - u) • (v - u) - dotV (v - u) (e - u) • (e - u))
           (dotV (e - u) (e - u) • (w - u) - dotV (w - u) (e - u) • (e - u))
      = arcV u v w
  rw [h1', h2', zero_smul, sub_zero]
  simp only [arcV, coe_zeroV, coe_smulP, coe_subP, sub_zero, dist_eq_norm, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, smul_dotP, dot_smulP]
  by_cases ha : v - u = 0
  · rw [ha]; simp
  by_cases hb : w - u = 0
  · rw [hb]; simp
  · have hna : ‖(v - u : V3)‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hnb : ‖(w - u : V3)‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    have hcne : dotV (e - u) (e - u) ≠ 0 := ne_of_gt hc
    refine congrArg Real.arccos ?_
    field_simp

/-- HOL `AZIM_DIHV_SAME_STRONG` (polar_fan.hl:23). -/
theorem AZIM_DIHV_SAME_STRONG {v w v1 v2 : V3} (h1 : ¬ Collinear3 v w v1)
    (h2 : ¬ Collinear3 v w v2) (hπ : azim v w v1 v2 ≤ Real.pi) :
    azim v w v1 v2 = dihV v w v1 v2 := by
  rcases lt_or_eq_of_le hπ with hlt | heq
  · exact azim_dihv_same h1 h2 hlt
  · have hcompl := azim_dihv_compl h1 h2 (le_of_eq heq.symm)
    rw [heq]; linarith

/-- HOL `AZIM_ARCV` (polar_fan.hl:31). -/
theorem AZIM_ARCV {e u v w : V3} (h1 : (e - u) ⬝ᵥ (v - u) = 0)
    (h2 : (e - u) ⬝ᵥ (w - u) = 0) (h3 : ¬ Collinear3 u e v) (h4 : ¬ Collinear3 u e w)
    (hπ : azim u e v w ≤ Real.pi) : azim u e v w = arcV u v w := by
  have hne : e ≠ u := fun h => h3 (collinear3_of_eq h)
  rw [← DIHV_ARCV h1 h2 hne]
  exact AZIM_DIHV_SAME_STRONG h3 h4 hπ

/-- HOL `PLANE_AFFINE_HULL_3` (polar_fan.hl:42). -/
theorem PLANE_AFFINE_HULL_3 (a b c : V3) :
    plane_p7 (affineSpan ℝ ({a, b, c} : Set V3)) ↔ ¬ Collinear ℝ ({a, b, c} : Set V3) := by
  constructor
  · rintro ⟨u, v, w, hnc, hA⟩ hC
    apply hnc
    have hdir : vectorSpan ℝ ({u, v, w} : Set V3) = vectorSpan ℝ ({a, b, c} : Set V3) := by
      rw [← direction_affineSpan ℝ ({u, v, w} : Set V3),
          ← direction_affineSpan ℝ ({a, b, c} : Set V3)]
      have hA' : affineSpan ℝ ({a, b, c} : Set V3) = affineSpan ℝ ({u, v, w} : Set V3) :=
        SetLike.coe_injective hA
      rw [hA']
    rw [collinear_iff_finrank_le_one, hdir]
    exact collinear_iff_finrank_le_one.mp hC
  · intro hnc
    exact ⟨a, b, c, hnc, rfl⟩

/-- HOL `AFFINE_HULL_3_GENERATED` (polar_fan.hl:46). -/
theorem AFFINE_HULL_3_GENERATED {s : Set V3} {u v w : V3}
    (hsub : s ⊆ affineSpan ℝ ({u, v, w} : Set V3)) (hnc : ¬ Collinear ℝ s) :
    affineSpan ℝ ({u, v, w} : Set V3) = affineSpan ℝ s := by
  have hle : affineSpan ℝ s ≤ affineSpan ℝ ({u, v, w} : Set V3) := by
    rw [← AffineSubspace.affineSpan_coe (affineSpan ℝ ({u, v, w} : Set V3))]
    exact affineSpan_mono ℝ hsub
  have h2 : (affineSpan ℝ ({u, v, w} : Set V3)).direction
      ≤ Submodule.span ℝ (Set.range ![v - u, w - u]) := by
    rw [direction_affineSpan]
    rw [vectorSpan_eq_span_vsub_set_right ℝ (by simp : (u:V3) ∈ ({u, v, w} : Set V3))]
    refine Submodule.span_le.mpr ?_
    rintro p ⟨z, hz, hp⟩
    dsimp only at hp
    rcases hz with hzu | hzv | hzw
    · rw [hzu] at hp
      rw [← hp, show (u -ᵥ u : V3) = 0 from vsub_self u]
      exact Submodule.zero_mem _
    · rw [hzv] at hp
      rw [← hp, show (v -ᵥ u : V3) = v - u from rfl]
      exact Submodule.subset_span ⟨0, rfl⟩
    · rw [hzw] at hp
      rw [← hp, show (w -ᵥ u : V3) = w - u from rfl]
      exact Submodule.subset_span ⟨1, rfl⟩
  have hmono : vectorSpan ℝ s
      ≤ (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    refine (vectorSpan_mono ℝ hsub).trans ?_
    exact le_rfl
  have hfin1 : Module.finrank ℝ (vectorSpan ℝ s)
      ≤ Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    exact Submodule.finrank_mono hmono
  have hfin2 : Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction ≤ 2 := by
    have h := finrank_range_le_card (R := ℝ) (M := V3) ![v - u, w - u]
    rw [Fintype.card_fin] at h
    exact (Submodule.finrank_mono h2).trans h
  have hnc2 : ¬ (Module.finrank ℝ (vectorSpan ℝ s) ≤ 1) := by
    haveI : FiniteDimensional ℝ (vectorSpan ℝ s) := inferInstance
    have h := collinear_iff_finrank_le_one (k := ℝ) (s := s)
    rw [h] at hnc
    exact hnc
  have heq1 : Module.finrank ℝ (vectorSpan ℝ s) = 2 := by omega
  have hvs : vectorSpan ℝ s = (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    refine Submodule.eq_of_le_of_finrank_eq hmono ?_
    have hge := Submodule.finrank_mono hmono
    omega
  have hdir : (affineSpan ℝ s).direction
      = (affineSpan ℝ ({u, v, w} : Set V3)).direction := by
    rw [direction_affineSpan, hvs]
  have hsne : (affineSpan ℝ s : Set V3).Nonempty := by
    rcases Set.eq_empty_or_nonempty s with h0 | hx
    · exact absurd (by rw [h0]; exact collinear_empty (k := ℝ) (P := V3) : Collinear ℝ s)
        hnc
    · obtain ⟨x, hx⟩ := hx
      exact ⟨x, mem_affineSpan ℝ hx⟩
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (s₁ := affineSpan ℝ s) (s₂ := affineSpan ℝ ({u, v, w} : Set V3)) hdir hsne hle).symm

/-- HOL `COLLINEAR_AZIM_0_OR_PI` (polar_fan.hl:63). -/
theorem COLLINEAR_AZIM_0_OR_PI (u e v w : V3) (hcol : Collinear ℝ ({u, v, w} : Set V3)) :
    azim u e v w = 0 ∨ azim u e v w = Real.pi := by
  by_cases h1 : Collinear3 u e v
  · left; unfold azim; rw [if_pos (Or.inl h1)]
  by_cases h2 : Collinear3 u e w
  · left; unfold azim; rw [if_pos (Or.inr h2)]
  have hae : u ≠ e := p7w_ncol_ne12 h1
  have huv : u ≠ v := p7w_ncol_ne13 h1
  have hwu : w ≠ u := Ne.symm (p7w_ncol_ne13 h2)
  have hwe : w ≠ e := Ne.symm (p7w_ncol_ne23 h2)
  obtain ⟨c, hwc⟩ := (collinear3_iff_smul (Ne.symm huv)).mp hcol
  have hne0 : c ≠ 0 := by
    intro h0
    apply h2
    rw [h0, zero_smul] at hwc
    rw [sub_eq_zero.mp hwc]
    exact p7w_col_131 u e
  rcases lt_trichotomy c 0 with hcn | hcz | hcp
  · -- c < 0：azim = π
    right
    have htr : azim (0:V3) (e - u) (v - u) (w - u) = azim u e v w := by
      have h := p7w_azim_translate (-u) u e v w
      rw [show u + -u = (0:V3) from by abel, show e + -u = e - u from by abel,
        show v + -u = v - u from by abel, show w + -u = w - u from by abel] at h
      exact h
    have hnc1 : ¬ Collinear3 (0:V3) (e - u) (v - u) := by
      intro hcc
      obtain ⟨κ, hκ⟩ :=
        (collinear3_iff_smul (sub_ne_zero.mpr (Ne.symm hae))).mp hcc
      rw [sub_zero, sub_zero] at hκ
      exact h1 ((collinear3_iff_smul (Ne.symm hae)).mpr ⟨κ, hκ⟩)
    have hnc2 : ¬ Collinear3 (0:V3) (e - u) (w - u) := by
      intro hcc
      obtain ⟨κ, hκ⟩ :=
        (collinear3_iff_smul (sub_ne_zero.mpr (Ne.symm hae))).mp hcc
      rw [sub_zero, sub_zero] at hκ
      exact h2 ((collinear3_iff_smul (Ne.symm hae)).mpr ⟨κ, hκ⟩)
    have hzsin : Real.sin (azim (0:V3) (e - u) (v - u) (w - u)) = 0 := by
      obtain ⟨t, ht, hJ⟩ := JBDNJJB hnc1 hnc2
      have hdot : (crossProduct ((e - u : V3) : Fin 3 → ℝ) ((v - u : V3) : Fin 3 → ℝ))
          ⬝ᵥ ((w - u : V3) : Fin 3 → ℝ) = 0 := by
        rw [hwc, coe_smulP, dotProduct_smul, smul_eq_mul, dotProduct_comm, dot_cross_self,
          mul_zero]
      rw [hJ, hdot, mul_zero]
    rcases p7w_azim_sin_zero hzsin with h0 | hpi
    · exfalso
      have hvg : v ∈ affGt {u, e} {w} :=
        (azim_eq_zero_iff h1 h2).mp (by rw [← htr]; exact h0)
      obtain ⟨c', hc'pos, h, heq⟩ := (affGt_pair_iff hae hwu hwe).mp hvg
      rw [hwc, smul_smul] at heq
      have hcomb : (1 - c' * c) • (v - u) = h • (e - u) := by
        rw [sub_smul, one_smul]
        nth_rewrite 1 [heq]
        abel
      rcases eq_or_ne h 0 with hh0 | hhne
      · rw [hh0, zero_smul] at hcomb
        rcases smul_eq_zero.mp hcomb with h2' | h2'
        · have hc'c : c' * c = 1 := by linarith
          nlinarith [hc'pos, hcn]
        · exact huv (sub_eq_zero.mp h2').symm
      · rcases eq_or_ne (1 - c' * c) 0 with hk0 | hkne
        · rw [hk0, zero_smul] at hcomb
          rcases smul_eq_zero.mp hcomb.symm with h2' | h2'
          · exact hhne h2'
          · exact hae (sub_eq_zero.mp h2').symm
        · have hpar : v - u = ((1 - c' * c)⁻¹ * h) • (e - u) := by
            refine (smul_right_injective V3 hkne) ?_
            show (1 - c' * c) • (v - u)
                = (1 - c' * c) • (((1 - c' * c)⁻¹ * h) • (e - u))
            rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hkne, one_mul, hcomb]
          exact h1 ((collinear3_iff_smul (Ne.symm hae)).mpr ⟨_, hpar⟩)
    · -- hpi : azim 0 (e-u) (v-u) (w-u) = π
      rw [← htr]
      exact hpi
  · exact absurd hcz hne0
  · -- 0 < c：azim = 0
    left
    have hvg : v ∈ affGt {u, e} {w} :=
      (affGt_pair_iff hae hwu hwe).mpr ⟨1 / c, by positivity, 0, by
        rw [hwc, smul_smul, div_eq_mul_inv, one_mul, inv_mul_cancel₀ hne0,
          one_smul, zero_smul, add_zero]⟩
    exact (azim_eq_zero_iff h1 h2).mpr hvg

-- W1 注记：HOL 经 ANGLES_ADD_BETWEEN（x ∈ segment [v,w] 的角加法）。
-- Lean 路线：x = u + r•(v-u) + s•(w-u)（r,s > 0，affGt），x' := u + (r+s)⁻¹•(x-u) 严格
-- 位于 segment [v,w] 内（Sbtw ℝ v x' w），由 angle_smul_right_of_pos /
-- angle_smul_left_of_pos 把 ∠vux、∠xuw 归到 x' 处，再用
-- Mathlib angle_add_angle_eq_of_sbtw 收口；v = w 退化情形两角皆 0。
/-- HOL `ANGLES_ADD_AFF_GE` (polar_fan.hl:74). -/
theorem ANGLES_ADD_AFF_GE {u v w x : V3} (hv : v ≠ u) (hw : w ≠ u) (hx : x ≠ u)
    (hmem : x ∈ affGt {u} {v, w}) :
    EuclideanGeometry.angle v u x + EuclideanGeometry.angle x u w
      = EuclideanGeometry.angle v u w := by
  sorry

-- W1 注记：HOL 经 ANGLES_ADD_BETWEEN（x ∈ segment [v,w] 的角加法）。
-- Lean 路线：x = u + r•(v-u) + s•(w-u)（r,s > 0，affGt），x' := u + (r+s)⁻¹•(x-u) 严格
-- 位于 segment [v,w] 内（Sbtw ℝ v x' w），由 angle_smul_right_of_pos /
-- angle_smul_left_of_pos 把 ∠vux、∠xuw 归到 x' 处，再用
-- Mathlib angle_add_angle_eq_of_sbtw 收口；v = w 退化情形两角皆 0。
/-! ## Borderline case and aff_ge cones (polar_fan.hl:102-273) -/

/-- HOL `AFF_GE_SCALE_LEMMA` (polar_fan.hl:102). -/
theorem AFF_GE_SCALE_LEMMA (a : ℝ) (u v : V3) (ha : 0 < a) (hv : v ≠ 0) :
    affGe ({0} : Set V3) {a • u, v} = affGe ({0} : Set V3) {u, v} := by
  by_cases hu : u = 0
  · subst hu
    rw [smul_zero]
  · have hau : a • u ≠ 0 := smul_ne_zero ha.ne' hu
    ext y
    constructor
    · intro hmem
      obtain ⟨r, s, hr, hs, hy⟩ := p7w_affGe_pair_extract0 hau hv hmem
      rw [smul_smul] at hy
      refine p7w_affGe_pair_intro0 hu hv (mul_nonneg hr ha.le) hs hy
    · intro hmem
      obtain ⟨r, s, hr, hs, hy⟩ := p7w_affGe_pair_extract0 hu hv hmem
      have hr' : 0 ≤ r / a := by positivity
      refine p7w_affGe_pair_intro0 hau hv hr' hs ?_
      rw [hy, smul_smul, div_mul_cancel₀ r (ne_of_gt ha)]

/-- HOL `AZIM_SAME_WITHIN_AFF_GE` (polar_fan.hl:120). -/
theorem AZIM_SAME_WITHIN_AFF_GE (a u v w z : V3) (hmem : v ∈ affGe {a} {u, w})
    (h1 : ¬ Collinear3 a u v) (h2 : ¬ Collinear3 a u w) :
    azim a u v z = azim a u w z := by
  by_cases hz : Collinear3 a u z
  · have h1z : azim a u v z = 0 := by unfold azim; rw [if_pos (Or.inr hz)]
    have h2z : azim a u w z = 0 := by unfold azim; rw [if_pos (Or.inr hz)]
    rw [h1z, h2z]
  · have hau : a ≠ u := p7w_ncol_ne12 h1
    obtain ⟨m, n, hm, hn, hv⟩ := p7w_affGe_pair_extract (Ne.symm hau)
      (Ne.symm (p7w_ncol_ne13 h2)) hmem
    have hn0 : 0 < n := by
      rcases lt_or_eq_of_le hn with h | h
      · exact h
      · exfalso
        apply h1
        rw [← h, zero_smul, add_zero] at hv
        exact (collinear3_iff_smul (Ne.symm hau)).mpr ⟨m, hv⟩
    have hv' : v - a = n • (w - a) + m • (u - a) := by rw [hv]; abel
    have hvgt : v ∈ affGt {a, u} {w} :=
      (affGt_pair_iff hau (Ne.symm (p7w_ncol_ne13 h2))
        (Ne.symm (p7w_ncol_ne23 h2))).mpr ⟨n, hn0, m, hv'⟩
    rw [azim_compl hz h1, azim_compl hz h2]
    rw [(azim_eq_azim_iff_alt hz h1 h2).mpr hvgt]

/-- HOL `AZIM_SAME_WITHIN_AFF_GE_ALT` (polar_fan.hl:148). -/
theorem AZIM_SAME_WITHIN_AFF_GE_ALT (a u v w z : V3) (hmem : v ∈ affGe {a} {u, w})
    (h1 : ¬ Collinear3 a u v) (h2 : ¬ Collinear3 a u w) :
    azim a u z v = azim a u z w := by
  by_cases hz : Collinear3 a u z
  · have h1z : azim a u z v = 0 := by unfold azim; rw [if_pos (Or.inl hz)]
    have h2z : azim a u z w = 0 := by unfold azim; rw [if_pos (Or.inl hz)]
    rw [h1z, h2z]
  · have hau : a ≠ u := p7w_ncol_ne12 h1
    obtain ⟨m, n, hm, hn, hv⟩ := p7w_affGe_pair_extract (Ne.symm hau)
      (Ne.symm (p7w_ncol_ne13 h2)) hmem
    have hn0 : 0 < n := by
      rcases lt_or_eq_of_le hn with h | h
      · exact h
      · exfalso
        apply h1
        rw [← h, zero_smul, add_zero] at hv
        exact (collinear3_iff_smul (Ne.symm hau)).mpr ⟨m, hv⟩
    have hkey : w - a = (1 / n) • (v - a) + (-(m / n)) • (u - a) := by
      apply smul_right_injective V3 (ne_of_gt hn0)
      show n • (w - a)
          = n • ((1 / n) • (v - a) + (-(m / n)) • (u - a))
      rw [smul_add, smul_smul, smul_smul, div_eq_mul_inv, one_mul,
        mul_inv_cancel₀ (ne_of_gt hn0), one_smul, mul_neg, div_eq_mul_inv, ← mul_assoc,
        mul_comm n m, mul_assoc m n n⁻¹, mul_inv_cancel₀ (ne_of_gt hn0), mul_one,
        hv]
      module
    have hwgt : w ∈ affGt {a, u} {v} :=
      (affGt_pair_iff hau (Ne.symm (p7w_ncol_ne13 h1))
        (Ne.symm (p7w_ncol_ne23 h1))).mpr ⟨1 / n, by positivity, -(m / n), hkey⟩
    exact (azim_eq_azim_iff hz h1 h2).mpr hwgt

/-- HOL `COLLINEAR_WITHIN_AFF_GE_COLLINEAR` (polar_fan.hl:161). -/
theorem COLLINEAR_WITHIN_AFF_GE_COLLINEAR (a u v w : V3) (hmem : v ∈ affGe {a} {u, w})
    (hcol : Collinear3 a u w) : Collinear3 a v w := by
  by_cases hwa : w = a
  · rw [hwa]
    exact p7w_col_131 a v
  by_cases hva : v = a
  · rw [hva]
    exact p7w_col_112 a w
  by_cases hua : u = a
  · rw [hua] at hmem
    simp only [affGe, Set.mem_setOf_eq, Affsign] at hmem
    obtain ⟨f, hfin, hvec, hsgn, hone⟩ := hmem
    have hTeq : hfin.toFinset = ({a, w} : Finset V3) := by
      ext z
      simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hTeq, Finset.sum_insert (by simp [Ne.symm hwa]), Finset.sum_singleton] at hvec hone
    have hfw : 0 ≤ f w := hsgn w (by simp)
    have hfa : f a = 1 - f w := by linarith
    have hfv : v - a = f w • (w - a) := by
      rw [hvec, hfa, sub_smul, one_smul, smul_sub]
      abel
    exact p7w_col_swap a v w ((collinear3_iff_smul hwa).mpr ⟨f w, hfv⟩)
  · obtain ⟨m, n, hm, hn, hv⟩ := p7w_affGe_pair_extract hua hwa hmem
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hua).mp hcol
    -- hc : w - a = c • (u - a); c ≠ 0 since w ≠ a
    have hc0 : c ≠ 0 := by
      intro h0
      apply hwa
      rw [h0, zero_smul] at hc
      exact sub_eq_zero.mp hc
    have hkey : v - a = ((m + n * c) / c) • (w - a) := by
      rw [hv, hc, smul_smul, smul_smul, div_mul_cancel₀ (m + n * c) hc0]
      module
    exact p7w_col_swap a v w ((collinear3_iff_smul hwa).mpr ⟨(m + n * c) / c, hkey⟩)

/-- HOL `GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE` (polar_fan.hl:188). -/
theorem GENERIC_LOCAL_FAN_STRAIGHT_AFF_GE (u v w : V3)
    (h1 : ¬ Collinear3 (0 : V3) v u) (h2 : ¬ Collinear3 (0 : V3) v w)
    (hπ : azim (0 : V3) v w u = Real.pi)
    (hdis : affGe ({0} : Set V3) {v, w} ∩ affLt ({0} : Set V3) {u} = ∅) :
    v ∈ affGe ({0} : Set V3) {u, w} := by
  sorry

/-- HOL `UNION_AFF_GE_1_2` (polar_fan.hl:226). -/
-- W1 注记（UNION_AFF_GE_1_2，未闭合，路线已验）：HOL 体 53 行（polar_fan.hl:226）。
-- 路线：p7w_affGe_pair_extract hu hw hmem 给 v - a = m•(u-a) + n•(w-a)（m,n ≥ 0）。
-- ⊆ 方向两组系数合并（module 收口，已验）。⊇ 方向按 (m,n) 零性分派：
-- (i) m = 0：v - a = n•(w-a)（n > 0，否则 v = a 矛盾），y - a = r•(u-a) + (s/n)•(v-a)
--     由 hvn 重写 + smul_smul + div_mul_cancel₀ s (hne0) + hy 闭合（无 injectivity）；
-- (ii) n = 0：对称地落 affGe {a} {v,w}；
-- (iii) m,n > 0：r·n ≤ s·m 时 y - a = ((r·n - m·s)/n)•(u-a) + (s/n)•(v-a)
--     （系数 ≥ 0 由 div_nonneg + linarith），n•(y-a) 双边展开后 module 收口；
--     r·n > s·m 时对称地落 affGe {a} {v,w}。除法消除走
--     div_eq_mul_inv + mul_inv_cancel₀ / mul_div_cancel_left₀ 路（本波已验的套路）。
-- 消费者：W6 generic 支极扇 E' 子集引理一半。
theorem UNION_AFF_GE_1_2 (a u v w : V3) (hmem : v ∈ affGe {a} {u, w})
    (hu : u ≠ a) (hv : v ≠ a) (hw : w ≠ a) :
    affGe {a} {u, v} ∪ affGe {a} {v, w} = affGe {a} {u, w} := by
  sorry

/-! ## Cycle and iteration kit (polar_fan.hl:279-406) -/

/-- HOL `AZIM_CYCLE_BASIC_PROPERTIES` (polar_fan.hl:279). -/
theorem AZIM_CYCLE_BASIC_PROPERTIES {W : Set V3} {v w p : V3} (hfin : W.Finite)
    (hp : p ∈ W) :
    azimCycle_p7 W v w p ∈ W ∧
      ∀ q ∈ W, q ≠ p → azim v w p (azimCycle_p7 W v w p) ≤ azim v w p q := by
  by_cases hsub : W ⊆ {p}
  · rw [azimCycle_p7, if_pos hsub]
    refine ⟨hp, fun q hq _ => ?_⟩
    rw [azim_self]
    exact azim_nonneg v w p q
  · have hne : ∃ u ∈ W, u ≠ p := by
      by_contra hc
      push_neg at hc
      exact hsub (fun x hx => by rw [hc x hx]; simp)
    -- lexicographic minimizer of (azim, ‖projection‖) on {u ∈ W | u ≠ p}
    have hf : {u : V3 | u ∈ W ∧ u ≠ p}.Finite := hfin.subset fun x hx => hx.1
    have hne2 : {u : V3 | u ∈ W ∧ u ≠ p}.Nonempty := by
      obtain ⟨u, hu1, hu2⟩ := hne
      exact ⟨u, hu1, hu2⟩
    obtain ⟨q, hqin, hqmin⟩ := Set.exists_min_image
      {u : V3 | u ∈ W ∧ u ≠ p}
      (fun x => toLex (azim v w p x, ‖projection (x - v) (w - v)‖)) hf hne2
    have hqP : q ≠ p ∧ q ∈ W ∧ ∀ r ∈ W, r ≠ p →
        azim v w p q < azim v w p r ∨
          azim v w p q = azim v w p r ∧
            ‖projection (q - v) (w - v)‖ ≤ ‖projection (r - v) (w - v)‖ := by
      refine ⟨hqin.2, hqin.1, fun r hr hpr => ?_⟩
      have h := hqmin r ⟨hr, hpr⟩
      rw [Prod.Lex.toLex_le_toLex] at h
      exact h
    rw [azimCycle_p7, if_neg hsub]
    obtain ⟨hεne, hεW, hεmin⟩ := Classical.epsilon_spec
      (p := fun u : V3 => u ≠ p ∧ u ∈ W ∧ ∀ q ∈ W, q ≠ p →
        azim v w p u < azim v w p q ∨
          azim v w p u = azim v w p q ∧
            ‖projection (u - v) (w - v)‖ ≤ ‖projection (q - v) (w - v)‖)
      ⟨q, hqP⟩
    exact ⟨hεW, fun r hr hpr => by
      rcases hεmin r hr hpr with h | h
      · exact le_of_lt h
      · exact le_of_eq h.1⟩

/-- HOL `AZIM_CYCLE_TWO_POINT_SET_ALT` (polar_fan.hl:292). -/
theorem AZIM_CYCLE_TWO_POINT_SET_ALT {W : Set V3} {x u v w : V3} (hW : W = {v, w}) :
    azimCycle_p7 W x u v = w := by
  subst hW
  by_cases hvw : v = w
  · subst hvw
    rw [azimCycle_p7, if_pos (c := (({v, v} : Set V3) ⊆ {v})) (by simp)]
  · rw [azimCycle_p7, if_neg (c := (({v, w} : Set V3) ⊆ {v}))
      (fun h => hvw (mem_singleton_iff.mp (h (by simp))).symm)]
    have hwP : w ≠ v ∧ w ∈ ({v, w} : Set V3) ∧ ∀ q ∈ ({v, w} : Set V3), q ≠ v →
        azim x u v w < azim x u v q ∨
          azim x u v w = azim x u v q ∧
            ‖projection (w - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖ := by
      refine ⟨fun h => hvw h.symm, by simp, ?_⟩
      intro q hq hqv
      have hq2 : q ∈ ({v} ∪ {w} : Set V3) := hq
      rcases hq2 with h | h
      · exact absurd (Set.mem_singleton_iff.mp h) hqv
      · exact Or.inr ⟨by rw [Set.mem_singleton_iff.mp h], by rw [Set.mem_singleton_iff.mp h]⟩
    obtain ⟨h1, h2, h3⟩ := Classical.epsilon_spec
      (p := fun z : V3 => z ≠ v ∧ z ∈ ({v, w} : Set V3) ∧
        ∀ q ∈ ({v, w} : Set V3), q ≠ v → azim x u v z < azim x u v q ∨
          azim x u v z = azim x u v q ∧
            ‖projection (z - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖)
      ⟨w, hwP⟩
    have h2' : ((Classical.epsilon (fun z : V3 => z ≠ v ∧ z ∈ ({v, w} : Set V3) ∧ ∀ q ∈ ({v, w} : Set V3), q ≠ v → azim x u v z < azim x u v q ∨ azim x u v z = azim x u v q ∧ ‖projection (z - x) (u - x)‖ ≤ ‖projection (q - x) (u - x)‖)) ∈ ({v} ∪ {w} : Set V3)) := h2
    rcases h2' with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) h1
    · exact Set.mem_singleton_iff.mp h

/-- The epsilon characterisation of `ivs_azim_cycle` on a singleton. -/
private theorem ivsAzimCycle_singleton {W : Set V3} {x u v : V3} (hW : W = {v})
    (hself : azimCycle_p7 W x u v = v) :
    ivsAzimCycle_p7 W x u v = v := by
  subst hW
  rw [ivsAzimCycle_p7, if_neg (c := (({v} : Set V3) = ∅)) (by
    intro h
    have h2 : (v : V3) ∈ ({v} : Set V3) := by simp
    rw [h] at h2
    exact absurd h2 (by simp))]
  have hspec := Classical.epsilon_spec
    (p := fun z : V3 => z ∈ ({v} : Set V3) ∧ azimCycle_p7 ({v} : Set V3) x u z = v)
    ⟨v, by simp, hself⟩
  have h1 : (Classical.epsilon (fun z : V3 => z ∈ ({v} : Set V3) ∧
      azimCycle_p7 ({v} : Set V3) x u z = v)) ∈ ({v} : Set V3) := hspec.1
  have h3 : (Classical.epsilon (fun z : V3 => z ∈ ({v} : Set V3) ∧
      azimCycle_p7 ({v} : Set V3) x u z = v)) = v := Set.mem_singleton_iff.mp h1
  rw [h3]

/-- HOL `AZIM_CYCLE_SING` (polar_fan.hl:309). -/
theorem AZIM_CYCLE_SING (x u v : V3) : azimCycle_p7 ({v} : Set V3) x u v = v := by
  rw [azimCycle_p7, if_pos (c := (({v} : Set V3) ⊆ {v})) (Set.Subset.refl _)]

/-- HOL `IVS_AZIM_CYCLE_SING` (polar_fan.hl:313). -/
theorem IVS_AZIM_CYCLE_SING (x u v : V3) : ivsAzimCycle_p7 ({v} : Set V3) x u v = v :=
  ivsAzimCycle_singleton rfl (AZIM_CYCLE_SING x u v)

/-- HOL `IVS_AZIM_CYCLE_TWO_POINT_SET` (polar_fan.hl:296). -/
theorem IVS_AZIM_CYCLE_TWO_POINT_SET (a b v w : V3) :
    ivsAzimCycle_p7 ({a, b} : Set V3) v w a = b := by
  by_cases hab : a = b
  · subst hab
    exact ivsAzimCycle_singleton (by simp)
      (AZIM_CYCLE_TWO_POINT_SET_ALT (x := v) (u := w) (v := a) (w := a) rfl)
  · rw [ivsAzimCycle_p7, if_neg (c := (({a, b} : Set V3) = ∅)) (by
      intro h
      have h2 : (a : V3) ∈ ({a, b} : Set V3) := by simp
      rw [h] at h2
      exact absurd h2 (by simp))]
    have hPb : b ∈ ({a, b} : Set V3) ∧ azimCycle_p7 ({a, b} : Set V3) v w b = a :=
      ⟨by simp, AZIM_CYCLE_TWO_POINT_SET_ALT (Set.pair_comm a b)⟩
    obtain ⟨h1, h2⟩ := Classical.epsilon_spec
      (p := fun z : V3 => z ∈ ({a, b} : Set V3) ∧
        azimCycle_p7 ({a, b} : Set V3) v w z = a) ⟨b, hPb⟩
    have h1' : ((Classical.epsilon (fun z : V3 => z ∈ ({a, b} : Set V3) ∧ azimCycle_p7 ({a, b} : Set V3) v w z = a)) ∈ ({a} ∪ {b} : Set V3)) := h1
    rcases h1' with h | h
    · exfalso
      rw [Set.mem_singleton_iff.mp h, AZIM_CYCLE_TWO_POINT_SET_ALT (W := ({a, b} : Set V3)) (x := v) (u := w) (v := a) (w := b) rfl] at h2
      exact hab h2.symm
    · exact Set.mem_singleton_iff.mp h

/-- HOL `IVS_AZIM_CYCLE_TWO_POINT_SET_ALT` (polar_fan.hl:305). -/
theorem IVS_AZIM_CYCLE_TWO_POINT_SET_ALT {W : Set V3} {x u v w : V3} (hW : W = {v, w}) :
    ivsAzimCycle_p7 W x u v = w := by
  subst hW
  exact IVS_AZIM_CYCLE_TWO_POINT_SET v w x u

/-! ## W5b face kit (polar_fan.hl face-consumers; W6a partial prepayment) -/

section W5bFace

/-- `hypermapOfFan` 的 dart 集合即 `dart1OfFan`（coe 传输）。 -/
private theorem p7w2_coe_darts {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E) :
    ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E := by
  show ((finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
  exact (finite_dart1_fan hfan).coe_toFinset

/-- `hypermapOfFan` 的 faceMap 在 dart 上即 `fFanPair`（AzimBridge 同款技术）。 -/
private theorem p7w2_apply_faceMap {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (d : V3 × V3) :
    (hypermapOfFan x V E hfan).faceMap d =
      if d ∈ dart1OfFan V E then fFanPair x V E d else d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [(finite_dart1_fan hfan).coe_toFinset]

private theorem p7w2_mem_dart1 {x : V3} {V : Set V3} {E : Set (Set V3)} (hfan : FAN x V E)
    {d : V3 × V3} (hd : d ∈ (hypermapOfFan x V E hfan).darts) : d ∈ dart1OfFan V E := by
  have h : d ∈ ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) := Finset.mem_coe.mpr hd
  rwa [p7w2_coe_darts hfan] at h

end W5bFace

/-! ## rho_node1 orbit (polar_fan.hl:318-469) -/

/-- HOL `RHO_NODE1_INJECTIVE` (polar_fan.hl:318). -/
theorem RHO_NODE1_INJECTIVE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    ∀ v ∈ V, ∀ w ∈ V, (rhoNode1 FF v = rhoNode1 FF w ↔ v = w) := by
  sorry

/-- HOL `IVS_RHO_NODE1_IN_V` (polar_fan.hl:325). -/
theorem IVS_RHO_NODE1_IN_V {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : ∀ v ∈ V, ivsRhoNode1 FF v ∈ V := by
  sorry

/-- HOL `LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V` (polar_fan.hl:330). -/
theorem LOCAL_FAN_ITER_IVS_RHO_NODE_IN_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) {v : V3} (hv : v ∈ V) (i : ℕ) :
    (ivsRhoNode1 FF)^[i] v ∈ V := by
  sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT` (polar_fan.hl:336). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT_LA7 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (rhoNode1 FF)^[i] v := by
  sorry

/-- HOL `LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS` (polar_fan.hl:360). -/
theorem LOCAL_FAN_ORBIT_MAP_EXPLICIT_IVS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v w : V3) (hv : v ∈ V) (hw : w ∈ V) :
    ∃ i, i < V.ncard ∧ w = (ivsRhoNode1 FF)^[i] v := by
  sorry

/-- HOL `ITER_IVS_RHO_IDD` (polar_fan.hl:381). -/
theorem ITER_IVS_RHO_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (ivsRhoNode1 FF)^[n] ((rhoNode1 FF)^[n] v) = v := by
  sorry

/-- HOL `ITER_RHO_IVS_IDD` (polar_fan.hl:392). -/
theorem ITER_RHO_IVS_IDD {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) (n : ℕ) :
    (rhoNode1 FF)^[n] ((ivsRhoNode1 FF)^[n] v) = v := by
  sorry

/-- HOL `LOFA_IMP_ITER_IVS_RHO_NODE_ID` (polar_fan.hl:402). -/
theorem LOFA_IMP_ITER_IVS_RHO_NODE_ID {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    (ivsRhoNode1 FF)^[V.ncard] v = v := by
  sorry

/-- HOL `GENERIC_LOCAL_FAN_AZIM_POS` (polar_fan.hl:408). -/
theorem GENERIC_LOCAL_FAN_AZIM_POS {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (v w : V3) (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) (hwr : w ≠ rhoNode1 FF v) :
    0 < Real.sin (azim (0 : V3) v (rhoNode1 FF v) w) := by
  sorry

/-! ## Hyp-function characterizations and order sums (polar_fan.hl:471-530) -/

/-- HOL `nn_of_hyp3` (polar_fan.hl:471). -/
theorem nnOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    nnOfHyp_p7 x V E = fun d =>
      if d ∈ dartsOfHyp_p7 E V then (d.1, azimCycle_p7 (ee d.1 E) x d.1 d.2) else d :=
  rfl

/-- HOL `ff_of_hyp3` (polar_fan.hl:477). -/
theorem ffOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    ffOfHyp_p7 x V E = fun d =>
      if d ∈ dartsOfHyp_p7 E V then (d.2, ivsAzimCycle_p7 (ee d.2 E) x d.2 d.1) else d :=
  rfl

/-- HOL `ee_of_hyp3` (polar_fan.hl:483). -/
theorem eeOfHyp3 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    eeOfHyp_p7 x V E = fun d => if d ∈ dartsOfHyp_p7 E V then (d.2, d.1) else d :=
  rfl

/-- HOL `ORDER_AZIM_SUM2Pi_0` (polar_fan.hl:488). -/
theorem ORDER_AZIM_SUM2Pi_0 {x y z : V3} {n : ℕ} {g : ℕ → V3}
    (h1 : ¬ Collinear ℝ ({x, y, z} : Set V3))
    (h2 : ∀ i ∈ Finset.Ico 0 (n + 1), ¬ Collinear ℝ ({x, y, g i} : Set V3))
    (h3 : g (n + 1) = g 0) (h4 : 0 < n)
    (h5 : ∀ j ∈ Finset.Ico 0 (n + 1), ∀ k ∈ Finset.Ico 0 (n + 1), j < k →
      azim x y z (g j) < azim x y z (g k)) :
    (∑ i ∈ Finset.Ico 0 (n + 1), azim x y (g i) (g (i + 1))) = 2 * Real.pi := by
  have h1' : ¬ Collinear3 x y z := h1
  have hcol : ∀ i, i < n + 1 → ¬ Collinear3 x y (g i) := by
    intro i hi
    exact h2 i (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
  have key : ∀ p q, p < q → q < n + 1 →
      azim x y (g p) (g q) = azim x y z (g q) - azim x y z (g p) := by
    intro p q hpq hqn
    have hchain : azim x y z (g p) < azim x y z (g q) :=
      h5 p (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) q (Finset.mem_Ico.mpr ⟨by omega, hqn⟩) hpq
    have h := AZIM_BASE_SHIFT_LE x y z (g p) (g p) (g q)
      h1' (hcol p (by omega)) (hcol p (by omega)) (hcol q (by omega)) (le_refl _) hchain.le
    rw [azim_self] at h
    linarith
  have comp : ∀ p q, p < q → q < n + 1 →
      azim x y (g q) (g p) = 2 * Real.pi - (azim x y z (g q) - azim x y z (g p)) := by
    intro p q hpq hqn
    have hchain : azim x y z (g p) < azim x y z (g q) :=
      h5 p (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) q (Finset.mem_Ico.mpr ⟨by omega, hqn⟩) hpq
    have hpos : (0:ℝ) < azim x y (g p) (g q) := by rw [key p q hpq hqn]; linarith
    have hc := azim_compl (hcol p (by omega)) (hcol q (by omega))
    rw [key p q hpq hqn,
      if_neg (by rw [← key p q hpq hqn]; exact ne_of_gt hpos)] at hc
    exact hc
  have tel : ∀ m, 1 ≤ m → m ≤ n →
      ∑ i ∈ Finset.range m, azim x y (g i) (g (i + 1))
        = azim x y z (g m) - azim x y z (g 0) := by
    intro m hm1 hm2
    induction m with
    | zero => omega
    | succ k ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0
        simp only [Finset.sum_range_zero, Finset.sum_empty, zero_add]
        have hstep := key 0 1 (by omega) (by omega)
        linarith
      · have hkm : k ≤ n := by omega
        have hstep := key k (k + 1) (by omega) (by omega)
        linarith [ih hk1 hkm]
  have hIco : Finset.Ico 0 (n + 1) = Finset.range (n + 1) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_range]
    omega
  rw [hIco]
  have hsplit : ∑ i ∈ Finset.range (n + 1), azim x y (g i) (g (i + 1))
      = (∑ i ∈ Finset.range n, azim x y (g i) (g (i + 1)))
        + azim x y (g n) (g (n + 1)) :=
    Finset.sum_range_succ (fun i => azim x y (g i) (g (i + 1))) n
  rw [hsplit]
  have hwrap : azim x y (g n) (g (n + 1)) = 2 * Real.pi
      - (azim x y z (g n) - azim x y z (g 0)) := by
    rw [h3]
    exact comp 0 n (by omega) (by omega)
  linarith [tel n h4 (Nat.le_refl _)]

/-- HOL `LOCAL_FAN_NOT_EMPTY_FF` (polar_fan.hl:511). -/
theorem LOCAL_FAN_NOT_EMPTY_FF {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : FF ≠ ∅ := by
  obtain ⟨hfan, x, hx, hFF, -⟩ := h
  intro h0
  have hx' : x ∈ FF := by rw [hFF]; exact mem_orbitMap_self _ x
  rw [h0] at hx'
  exact absurd hx' (by simp)

/-- HOL `LOCAL_FAN_NOT_CARD_FF_GE_2` (polar_fan.hl:521). -/
theorem LOCAL_FAN_NOT_CARD_FF_GE_2 {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) : 2 ≤ FF.ncard := by
  obtain ⟨hfan, x, hx, hFF, hD⟩ := h
  have hxFF : x ∈ FF := by rw [hFF]; exact mem_orbitMap_self _ x
  have hsub : FF ⊆ dart1OfFan V E := by
    rw [hFF]
    exact (orbitMap_subset_of_permutesOn (hypermapOfFan 0 V E hfan).faceMap_permutes hx).trans
      (p7w2_coe_darts hfan).subset
  have hfin : FF.Finite := (finite_dart1_fan hfan).subset hsub
  have hcard : (dart1OfFan V E).ncard = 2 * FF.ncard := by
    rw [← p7w2_coe_darts hfan, Set.ncard_coe_finset]
    exact hD.1
  have h1le : 0 < FF.ncard := (Set.ncard_pos hfin).mpr ⟨x, hxFF⟩
  by_contra hlt
  push_neg at hlt
  have h1 : FF.ncard = 1 := by omega
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
  have hxy : x = y := by
    rw [hy] at hxFF
    exact Set.mem_singleton_iff.mp hxFF
  have hfix : (hypermapOfFan 0 V E hfan).faceMap x = x := by
    have hmem := pow_apply_mem_orbitMap (hypermapOfFan 0 V E hfan).faceMap 1 x
    rw [← hFF, hy, ← hxy] at hmem
    simpa using hmem
  rw [p7w2_apply_faceMap hfan x, if_pos (p7w2_mem_dart1 hfan hx)] at hfix
  exact f_fan_no_fix hfan x (p7w2_mem_dart1 hfan hx) hfix

/-! ## Sin/cross sign kit (polar_fan.hl:532-566) -/

/-- HOL `SIN_AZIM_MUTUAL_CROSS` (polar_fan.hl:532). -/
theorem SIN_AZIM_MUTUAL_CROSS (u v w : V3) :
    (Real.sin (azim (0 : V3) u v w) < 0 ↔ (cross3 u v) ⬝ᵥ w < 0) ∧
    (0 < Real.sin (azim (0 : V3) u v w) ↔ 0 < (cross3 u v) ⬝ᵥ w) ∧
    (Real.sin (azim (0 : V3) u v w) ≤ 0 ↔ (cross3 u v) ⬝ᵥ w ≤ 0) ∧
    (0 ≤ Real.sin (azim (0 : V3) u v w) ↔ 0 ≤ (cross3 u v) ⬝ᵥ w) ∧
    (Real.sin (azim (0 : V3) u v w) = 0 ↔ (cross3 u v) ⬝ᵥ w = 0) := by
  set C := ((cross3 u v) ⬝ᵥ w : ℝ) with hCdef
  have hsin : ∃ t : ℝ, 0 < t ∧ Real.sin (azim (0 : V3) u v w) = t * C := by
    rcases Classical.em (Collinear3 (0:V3) u v ∨ Collinear3 (0:V3) u w) with hcol | hnd
    · have haz : azim (0:V3) u v w = 0 := by
        unfold azim
        rw [if_pos hcol]
      have hc : C = 0 := by
        rcases hcol with h | h
        · by_cases hu : (u:V3) = 0
          · rw [hCdef, hu, p7w_cross3_zero_left, dotProduct_comm, coe_zeroV, dotProduct_zero]
          · obtain ⟨c, hc⟩ := (collinear3_iff_smul hu).mp h
            rw [sub_zero, sub_zero] at hc
            have hv' : v = c • u := hc
            rw [hCdef, hv', p7w_cross3_smul_right_self, dotProduct_comm, coe_zeroV, dotProduct_zero]
        · by_cases hu : (u:V3) = 0
          · rw [hCdef, hu, p7w_cross3_zero_left, dotProduct_comm, coe_zeroV, dotProduct_zero]
          · obtain ⟨c, hc⟩ := (collinear3_iff_smul hu).mp h
            rw [sub_zero, sub_zero] at hc
            have hw' : w = c • u := hc
            have hcu : ((cross3 u v : V3) : Fin 3 → ℝ) ⬝ᵥ ((u : V3) : Fin 3 → ℝ) = 0 := by
              rw [coe_cross3P, dotProduct_comm]
              exact dot_self_cross _ _
            rw [hCdef, hw', coe_smulP, dotProduct_smul, hcu, smul_eq_mul, mul_zero]
      exact ⟨1, one_pos, by rw [haz, hc]; norm_num⟩
    · obtain ⟨hn1, hn2⟩ := not_or.mp hnd
      obtain ⟨t, ht, hJ⟩ := JBDNJJB hn1 hn2
      refine ⟨t, ht, ?_⟩
      have hC' : C = (crossProduct ((u : V3) : Fin 3 → ℝ) ((v : V3) : Fin 3 → ℝ))
          ⬝ᵥ ((w : V3) : Fin 3 → ℝ) := by
        rw [hCdef, p7w_dot_coe, coe_cross3P]
      rw [hJ, hC']
  obtain ⟨t, ht, hs⟩ := hsin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      rw [hs, mul_neg_iff] at h
      rcases h with ⟨-, hC⟩ | ⟨hlt, -⟩
      · exact hC
      · linarith
    · intro h
      rw [hs, mul_neg_iff]
      exact Or.inl ⟨ht, h⟩
  · constructor
    · intro h
      rw [hs] at h
      rcases mul_pos_iff.mp h with ⟨-, hC⟩ | ⟨hlt, -⟩
      · exact hC
      · linarith
    · intro h
      rw [hs, mul_pos_iff]
      exact Or.inl ⟨ht, h⟩
  · constructor
    · intro h
      rw [hs] at h
      by_contra hcon
      push_neg at hcon
      exact absurd (mul_pos ht hcon) (not_lt.mpr h)
    · intro h
      rw [hs]
      have hle : t * C ≤ t * 0 := mul_le_mul_of_nonneg_left h ht.le
      simpa using hle
  · constructor
    · intro h
      rw [hs] at h
      by_contra hcon
      push_neg at hcon
      exact absurd (mul_neg_iff.mpr (Or.inl ⟨ht, hcon⟩)) (not_lt.mpr h)
    · intro h
      rw [hs]
      exact mul_nonneg ht.le h
  · constructor
    · intro h
      rw [hs, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h ht.ne'
      · exact h
    · intro h
      rw [hs, h, mul_zero]

/-- HOL `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS` (polar_fan.hl:541). -/
theorem CROSS_POSITIVE_MULTIPLE_AZIM_AXIS {x y z : V3} (hx : x ≠ 0)
    (h1 : x ⬝ᵥ y = 0) (h2 : x ⬝ᵥ z = 0)
    (h3 : 0 < azim (0 : V3) x y z) (h4 : azim (0 : V3) x y z < Real.pi) :
    ∃ a : ℝ, 0 < a ∧ cross3 y z = a • x := by
  have hBAC : cross3 x (cross3 y z) = 0 := by
    refine p7w_v3_eq ?_
    rw [coe_cross3P, coe_cross3P, coe_zeroV, cross_cross_eq_smul_sub_smul']
    have h1' : ((y : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm, ← p7w_dot_coe]
      exact h1
    have h2' : ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((z : V3) : Fin 3 → ℝ) = 0 := by
      rw [← p7w_dot_coe]
      exact h2
    rw [h2', h1', zero_smul, zero_smul, sub_zero]
  have hx' : ((x : V3) : Fin 3 → ℝ) ≠ ((0 : V3) : Fin 3 → ℝ) := fun h0 => hx (p7w_v3_eq h0)
  have hdep : ¬ LinearIndependent ℝ ![((x : V3) : Fin 3 → ℝ),
      ((cross3 y z : V3) : Fin 3 → ℝ)] := by
    intro hli
    have hne : crossProduct ((x : V3) : Fin 3 → ℝ) ((cross3 y z : V3) : Fin 3 → ℝ) ≠ 0 :=
      (crossProduct_ne_zero_iff_linearIndependent (v := ((x : V3) : Fin 3 → ℝ))
        (w := ((cross3 y z : V3) : Fin 3 → ℝ))).mpr hli
    apply hne
    exact congrArg (fun v : V3 => ((v : V3) : Fin 3 → ℝ)) hBAC
  rw [LinearIndependent.pair_iff' hx'] at hdep
  push_neg at hdep
  obtain ⟨c, hc⟩ := hdep
  have hcz : cross3 y z = c • x := p7w_v3_eq (by rw [coe_smulP]; exact hc.symm)
  have hnc1 : ¬ Collinear3 (0:V3) x y := fun hcc =>
    h3.ne' (by unfold azim; rw [if_pos (Or.inl hcc)])
  have hnc2 : ¬ Collinear3 (0:V3) x z := fun hcc =>
    h3.ne' (by unfold azim; rw [if_pos (Or.inr hcc)])
  obtain ⟨tJ, htJ, hJ⟩ := JBDNJJB hnc1 hnc2
  have hpos1 : (0:ℝ) < (crossProduct ((x:V3):Fin 3 → ℝ) ((y:V3):Fin 3 → ℝ))
      ⬝ᵥ ((z:V3):Fin 3 → ℝ) := by
    have hsp : (0:ℝ) < Real.sin (azim (0:V3) x y z) :=
      Real.sin_pos_of_pos_of_lt_pi h3 h4
    rw [hJ] at hsp
    rcases mul_pos_iff.mp hsp with ⟨-, hP⟩ | ⟨hlt, -⟩
    · exact hP
    · linarith
  have hcyc : (crossProduct ((x:V3):Fin 3 → ℝ) ((y:V3):Fin 3 → ℝ)) ⬝ᵥ ((z:V3):Fin 3 → ℝ)
      = (crossProduct ((y:V3):Fin 3 → ℝ) ((z:V3):Fin 3 → ℝ)) ⬝ᵥ ((x:V3):Fin 3 → ℝ) := by
    rw [dotProduct_comm, triple_product_permutation, dotProduct_comm]
  have hxx : (0:ℝ) < ((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ) := by
    rw [← p7w_dot_coe]
    have hn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hq := norm_sq_eq_dot x
    linarith [pow_pos hn 2]
  have hcpos : (0:ℝ) < c := by
    have hd1 : (crossProduct ((y:V3):Fin 3 → ℝ) ((z:V3):Fin 3 → ℝ)) ⬝ᵥ ((x:V3):Fin 3 → ℝ)
        = c * (((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ)) := by
      have hcPi : crossProduct ((y:V3):Fin 3 → ℝ) ((z:V3):Fin 3 → ℝ)
          = c • ((x : V3) : Fin 3 → ℝ) := by
        rw [← coe_cross3P, ← coe_smulP]
        exact congrArg (fun v : V3 => ((v : V3) : Fin 3 → ℝ)) hcz
      rw [hcPi, smul_dotProduct, smul_eq_mul]
    have hkey : (0:ℝ) < c * (((x : V3) : Fin 3 → ℝ) ⬝ᵥ ((x : V3) : Fin 3 → ℝ)) := by
      rw [← hd1, ← hcyc]
      exact hpos1
    rcases mul_pos_iff.mp hkey with ⟨hcpos', -⟩ | ⟨hlt, hxxneg⟩
    · exact hcpos'
    · linarith
  refine ⟨c, hcpos, hcz⟩

/-- HOL `CROSS_POSITIVE_MULTIPLE_AZIM_AXIS_ALT` (polar_fan.hl:557). -/
theorem CROSS_POSITIVE_MULTIPLE_AZIM_AXIS_ALT {x y z : V3} (hx : x ≠ 0)
    (h1 : x ⬝ᵥ y = 0) (h2 : x ⬝ᵥ z = 0)
    (h3 : 0 < azim (0 : V3) x y z) (h4 : azim (0 : V3) x y z < Real.pi) :
    ∃ a : ℝ, 0 < a ∧ x = a • cross3 y z := by
  obtain ⟨a, ha, hxy⟩ := CROSS_POSITIVE_MULTIPLE_AZIM_AXIS hx h1 h2 h3 h4
  refine ⟨a⁻¹, by positivity, ?_⟩
  rw [hxy, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

/-! ## fan7 / FAN equivalences (polar_fan.hl:572-1047) -/

/-- HOL `GMLWKPK` (polar_fan.hl:572). -/
theorem GMLWKPK (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E) :
    fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
          (∀ v : V3, e1 ∩ e2 = {v} → affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v}) := by
  sorry

/-- HOL `GMLWKPK_ALT` (polar_fan.hl:608). -/
theorem GMLWKPK_ALT (x : V3) (V : Set V3) (E : Set (Set V3)) (hg : Graph E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
      (∀ e1 ∈ E, ∀ e2 ∈ E, ∀ v : V3, e1 ∩ e2 = {v} →
        affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v})) := by
  sorry

/-- HOL `FAN_ECONOMIZED` (polar_fan.hl:641). -/
theorem FAN_ECONOMIZED (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ↔
      (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧
        (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
          ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
            (e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) ∧
            (∀ v : V3, e1 ∩ e2 = {v} →
              affGe {x} e1 ∩ affGe {x} e2 = affGe {x} {v})) := by
  constructor
  · rintro ⟨hun, hg, hf1, hf2, hf6, hf7⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK x V E hg).mp hf7⟩
  · rintro ⟨hun, hg, hf1, hf2, hf6, he⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK x V E hg).mpr he⟩

/-- HOL `FAN7_AFF_GT_CONDITION` (polar_fan.hl:661). -/
theorem FAN7_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hg : Graph E) (hx : x ∉ V)
    (hsub : ∀ e ∈ E, e ⊆ V ∧ x ∉ e)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    fan7 x V E := by
  sorry

/-- HOL `FAN_AFF_GT_CONDITION` (polar_fan.hl:812). -/
theorem FAN_AFF_GT_CONDITION (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf1 : fan1 x V E) (hf2 : fan2 x V E)
    (hf6 : fan6 x V E)
    (hvs : ∀ v ∈ V, ∀ w ∈ V, affGe {x} {v} ∩ affGe {x} {w} = affGe {x} ({v} ∩ {w}))
    (hve : ∀ v ∈ V, ∀ e ∈ E, affGt {x} {v} ∩ affGt {x} e = ∅)
    (hee : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → affGt {x} e1 ∩ affGt {x} e2 = ∅) :
    FAN x V E := by
  sorry

/-- HOL `GMLWKPK_SIMPLE` (polar_fan.hl:832). -/
theorem GMLWKPK_SIMPLE (x : V3) (V : Set V3) (E : Set (Set V3))
    (hun : (⋃₀ E) ⊆ V) (hg : Graph E) (hf6 : fan6 x V E)
    (hx : ∀ e ∈ E, x ∉ e) :
    (fan7 x V E ↔
      ∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
        ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
          e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) := by
  sorry

/-- HOL `FAN_ECONOMIZED_SIMPLE` (polar_fan.hl:1023). -/
theorem FAN_ECONOMIZED_SIMPLE (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN x V E ↔
      (⋃₀ E) ⊆ V ∧ Graph E ∧ fan1 x V E ∧ fan2 x V E ∧ fan6 x V E ∧
        (∀ e1 ∈ E ∪ (image (fun v : V3 => {v}) V),
          ∀ e2 ∈ E ∪ (image (fun v : V3 => {v}) V),
            e1 ∩ e2 = ∅ → affGe {x} e1 ∩ affGe {x} e2 = ({x} : Set V3)) := by
  constructor
  · rintro ⟨hun, hg, hf1, hf2, hf6, hf7⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK_SIMPLE x V E hun hg hf6
      (fun e he hxe => hf2 (hun (Set.mem_sUnion_of_mem hxe he)))).mp hf7⟩
  · rintro ⟨hun, hg, hf1, hf2, hf6, he⟩
    exact ⟨hun, hg, hf1, hf2, hf6, (GMLWKPK_SIMPLE x V E hun hg hf6
      (fun e he hxe => hf2 (hun (Set.mem_sUnion_of_mem hxe he)))).mpr he⟩

/-! ## W5b: BGMIFTE arc-half kit (Hvihvec duality + polar arc half) -/

section W5bKit

private theorem p7w2_coe_neg (a : V3) : ((-a : V3) : Fin 3 → ℝ) = -((a : V3) : Fin 3 → ℝ) := rfl

/-- 复合 V3 项的 coe 展开（折叠形匹配）。 -/
private theorem p7w2_coe_lin (k c : ℝ) (v u : V3) :
    ((k • v - c • u : V3) : Fin 3 → ℝ)
      = k • ((v : V3) : Fin 3 → ℝ) - c • ((u : V3) : Fin 3 → ℝ) := by
  rw [coe_subP, coe_smulP, coe_smulP]

/-- Fin3 层左减法点积。 -/
private theorem p7w2_sub_dotF (a b c : Fin 3 → ℝ) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  rw [dotProduct, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.sub_apply, sub_mul]

/-- Fin3 层右减法点积。 -/
private theorem p7w2_dot_subF (a b c : Fin 3 → ℝ) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c := by
  rw [dotProduct, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.sub_apply, mul_sub]

/-- `cross3` 反交换。 -/
private theorem p7w2_cross3_anticomm (a b : V3) : cross3 a b = -(cross3 b a) := by
  refine p7w_v3_eq ?_
  simp only [coe_cross3P, p7w2_coe_neg, cross_anticomm]

/-- `cross3` 零积 ⇒ 与 0 共线（第一变元非零情形）。 -/
private theorem p7w2_cross3_zero_collinear {a b : V3} (ha : a ≠ 0)
    (h : cross3 a b = 0) : Collinear3 (0:V3) a b := by
  have haF : ((a:V3):Fin 3 → ℝ) ≠ 0 := fun he => ha (p7w_v3_eq he)
  have hdep : ¬ LinearIndependent ℝ ![((a:V3):Fin 3 → ℝ), ((b:V3):Fin 3 → ℝ)] := by
    intro hli
    have hne : crossProduct ((a:V3):Fin 3 → ℝ) ((b:V3):Fin 3 → ℝ) ≠ 0 :=
      (crossProduct_ne_zero_iff_linearIndependent (v := ((a:V3):Fin 3 → ℝ))
        (w := ((b:V3):Fin 3 → ℝ))).mpr hli
    exact hne (by rw [← coe_cross3P]; exact congrArg (fun v : V3 => ((v:V3):Fin 3 → ℝ)) h)
  rw [LinearIndependent.pair_iff' haF] at hdep
  push_neg at hdep
  obtain ⟨c, hc⟩ := hdep
  have hbeq : b = c • a := p7w_v3_eq hc.symm
  exact (collinear3_iff_smul ha).mpr ⟨c, by simp [hbeq]⟩

/-- Lagrange 恒等式（V3 级，经 coe）。 -/
private theorem p7w2_dot_cross_cross (u v w : V3) :
    (cross3 u v) ⬝ᵥ (cross3 u w) = (u ⬝ᵥ u) * (v ⬝ᵥ w) - (u ⬝ᵥ w) * (v ⬝ᵥ u) := by
  rw [p7w_dot_coe, coe_cross3P, coe_cross3P]
  have h := cross_dot_cross ((u:V3):Fin 3 → ℝ) ((v:V3):Fin 3 → ℝ) ((u:V3):Fin 3 → ℝ)
    ((w:V3):Fin 3 → ℝ)
  rw [p7w_dot_coe, p7w_dot_coe, p7w_dot_coe, p7w_dot_coe]
  linarith [h]

/-- Fin3 层数值核：投影点积 = k × 叉点积（标量为 coe 点积形）。 -/
private theorem p7w2_num_id (U V W : Fin 3 → ℝ) (k c d : ℝ) (hk : k = U ⬝ᵥ U)
    (hc : c = V ⬝ᵥ U) (hd : d = W ⬝ᵥ U) :
    (k • V - c • U) ⬝ᵥ (k • W - d • U) = k * (crossProduct U V ⬝ᵥ crossProduct U W) := by
  subst hk; subst hc; subst hd
  rw [p7w2_sub_dotF, p7w2_dot_subF, p7w2_dot_subF]
  simp only [dot_smulP, smul_dotP, cross_dot_cross U V U W]
  ring

/-- V3 层范数核：投影向量范数 = ‖u‖·‖u×v‖（标量为 coe 点积形）。 -/
private theorem p7w2_norm_id (u v : V3) :
    ‖(((((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • v
        - (((v:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • u : V3))‖
      = ‖u‖ * ‖cross3 u v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ?_
  have h1 : ‖(((((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • v
        - (((v:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • u : V3))‖ ^ 2
      = ((((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • v
        - (((v:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • u : V3) ⬝ᵥ
        ((((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • v
        - (((v:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) • u : V3) :=
    norm_sq_eq_dot _
  have h2 : ‖cross3 u v‖ ^ 2 = (cross3 u v) ⬝ᵥ (cross3 u v) := norm_sq_eq_dot (cross3 u v)
  have h3 : ‖u‖ ^ 2 = u ⬝ᵥ u := norm_sq_eq_dot u
  have hpair : (‖u‖ * ‖cross3 u v‖) ^ 2 = ‖u‖ ^ 2 * ‖cross3 u v‖ ^ 2 := by
    rw [pow_two, pow_two, pow_two]; ring
  rw [h1, hpair, h3, h2, p7w_dot_coe, p7w2_coe_lin]
  simp only [p7w2_sub_dotF, p7w2_dot_subF, dot_smulP, smul_dotP, p7w2_dot_cross_cross]
  ring

/-- **HVIHVEC**（Hvihvec.hl:34 的 0 心形式）：`dihV 0 u v w` 即 `u×v` 与
`u×w` 在原点处的夹角。退化支两侧同为 `arccos 0`，故对一切 `v w` 成立。
BGMIFTE 的 arc↔角对偶两 half 的共同引擎。 -/
private theorem p7w2_hvihvec {u : V3} (hu : u ≠ 0) (v w : V3) :
    dihV 0 u v w = arcV 0 (cross3 u v) (cross3 u w) := by
  have hknorm : (0:ℝ) < dotV u u := by
    rw [show dotV u u = ‖(u:V3)‖ ^ 2 from (norm_sq_eq_dot (u:V3)).symm]
    exact pow_pos (norm_pos_iff.mpr hu) 2
  unfold dihV
  dsimp only
  simp only [sub_zero]
  unfold arcV
  simp only [coe_zeroV, sub_zero, dist_eq_norm, p7w2_coe_lin]
  refine congrArg Real.arccos ?_
  rw [p7w2_num_id ((u:V3):Fin 3 → ℝ) ((v:V3):Fin 3 → ℝ) ((w:V3):Fin 3 → ℝ)
      (((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ))
      (((v:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ))
      (((w:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ)) rfl rfl rfl,
    p7w2_norm_id u v, p7w2_norm_id u w]
  simp only [coe_cross3P]
  rw [mul_mul_mul_comm ‖u‖ ‖cross3 u v‖ ‖u‖ ‖cross3 u w‖,
    show ‖u‖ * ‖u‖ = ‖u‖ ^ 2 from (pow_two ‖u‖).symm, norm_sq_eq_dot (u:V3), p7w_dot_coe]
  have hkF : ((u:V3):Fin 3 → ℝ) ⬝ᵥ ((u:V3):Fin 3 → ℝ) ≠ 0 := ne_of_gt hknorm
  field_simp [hkF]

/-- `arcV 0` 对称。 -/
private theorem p7w2_arcV_comm (a b : V3) : arcV 0 a b = arcV 0 b a := by
  unfold arcV
  simp only [coe_zeroV, sub_zero, dist_eq_norm]
  refine congrArg Real.arccos ?_
  rw [p7w_dot_coe, p7w_dot_coe, dotProduct_comm, mul_comm]

/-- `arcV 0` 第二变元取负 = π 减角。 -/
private theorem p7w2_arcV_neg (a b : V3) :
    arcV 0 a (-b) = Real.pi - arcV 0 a b := by
  unfold arcV
  simp only [coe_zeroV, sub_zero, dist_eq_norm]
  rw [show (-b : V3) = (-1 : ℝ) • b by module]
  rw [p7w_dot_coe, p7w_dot_coe, coe_smulP, dot_smulP, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_one, one_mul]
  have hneg2 : (-1 : ℝ) * (((a : V3) : Fin 3 → ℝ) ⬝ᵥ ((b : V3) : Fin 3 → ℝ))
      / (‖a‖ * ‖b‖) = -(((a : V3) : Fin 3 → ℝ) ⬝ᵥ ((b : V3) : Fin 3 → ℝ)
      / (‖a‖ * ‖b‖)) := by ring
  rw [hneg2, Real.arccos_neg]

/-- 0 心三点集交换的共线传输。 -/
private theorem p7w2_collinear_swap01 {a v : V3} (h : ¬ Collinear ℝ (({0, v, a} : Set V3))) :
    ¬ Collinear ℝ (({0, a, v} : Set V3)) := by
  intro hc
  apply h
  have hset : ({0, a, v} : Set V3) = ({0, v, a} : Set V3) := by
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [hset] at hc

/-- **W5b 主件（BGMIFTE 极扇弧 half，逐点前提形式）**：极点 `a = ρ v`、
`b = ρ a` 处，极扇弧 `arcV 0 (v×a) (a×b)` 等于 `π` 减原扇内角
`interiorAngle1 0 FF a = azim 0 a b (ivs a)`。
- `h3` = IVS_RHO_IDD 逐点形（`ivs (ρ v) = v`）；
- `h4/h5` = 非共线，即 LOCAL_FAN_CHARACTER_OF_RHO_NODE 第三合取（fan6 型）
  在 `a`、`v` 处的逐点形；
- `hia/hpos` = 内角界：`hia` 即 BGMIFTE 前提在 `ρ v` 处的实例，`hpos` 即
  INTERIOR_ANGLE1_POS（LA5:5442）逐点形。
W6c 装配时以 ρ 轨道 foundation 逐点供件即可；退化侧由逐点前提挡住。 -/
private theorem p7w2_half_polar_arc {V : Set V3} {FF : Set (V3 × V3)}
    {v a b : V3} (ha : a = rhoNode1 FF v) (hb : b = rhoNode1 FF a)
    (h3 : ivsRhoNode1 FF a = v)
    (h4 : ¬ Collinear ℝ (({0, a, b} : Set V3)))
    (h5 : ¬ Collinear ℝ (({0, v, a} : Set V3)))
    (hia : interiorAngle1 (0:V3) FF a < Real.pi)
    (hpos : 0 < interiorAngle1 (0:V3) FF a) :
    arcV (0:V3) (cross3 v a) (cross3 a b)
        = Real.pi - interiorAngle1 (0:V3) FF a
      ∧ 0 < arcV (0:V3) (cross3 v a) (cross3 a b)
      ∧ arcV (0:V3) (cross3 v a) (cross3 a b) < Real.pi := by
  have ncol4 : ¬ Collinear3 (0:V3) a b := h4
  have ncol5 : ¬ Collinear3 (0:V3) a v := p7w2_collinear_swap01 h5
  have ha0 : a ≠ 0 := fun he => ncol4 (by rw [he]; exact collinear3_of_eq rfl)
  have hv0 : v ≠ 0 := fun he => ncol5 (by rw [he]; exact p7w_col_131 0 a)
  have hp0 : cross3 v a ≠ 0 := fun he => h5 (p7w2_cross3_zero_collinear hv0 he)
  have hq0 : cross3 a b ≠ 0 := fun he => h4 (p7w2_cross3_zero_collinear ha0 he)
  have hint : interiorAngle1 (0:V3) FF a = azim (0:V3) a b v := by
    show azim (0:V3) a (rhoNode1 FF a) (ivsRhoNode1 FF a) = _
    rw [← hb, h3]
  have hlt : azim (0:V3) a b v < Real.pi := by rw [← hint]; exact hia
  have had : azim (0:V3) a b v = dihV 0 a b v := azim_dihv_same ncol4 ncol5 hlt
  have hdual : dihV 0 a b v = arcV 0 (cross3 a b) (cross3 a v) := p7w2_hvihvec ha0 b v
  have hskew : cross3 a v = -(cross3 v a) := p7w2_cross3_anticomm a v
  have hcomm : arcV 0 (cross3 v a) (cross3 a b) = arcV 0 (cross3 a b) (cross3 v a) :=
    p7w2_arcV_comm _ _
  have hneg : arcV 0 (cross3 a b) (-(cross3 a v))
      = Real.pi - arcV 0 (cross3 a b) (cross3 a v) :=
    p7w2_arcV_neg _ _
  have hmain : arcV 0 (cross3 v a) (cross3 a b)
      = Real.pi - interiorAngle1 (0:V3) FF a := by
    rw [hcomm, hint, had, hdual, ← hneg, hskew, neg_neg]
  exact ⟨hmain, by rw [hmain]; linarith, by rw [hmain]; linarith⟩

end W5bKit

/-! ## Definition of the polar fan (polar_fan.hl:1053) -/

/-- HOL `JNVXCRC` (polar_fan.hl:1053): the polar fan of `(V,E,FF)` —
vertices are the cross products `v × rho_node1 FF v`, edges join
consecutive images, darts likewise.  `E` is not used by the body (kept
for the HOL signature). -/
noncomputable def polarFan (V : Set V3) (_E : Set (Set V3)) (FF : Set (V3 × V3)) :
    Set V3 × Set (Set V3) × Set (V3 × V3) :=
  let r := rhoNode1 FF
  let p := fun v : V3 => cross3 v (r v)
  (image p V, image (fun v : V3 => {p v, p (r v)}) V,
    image (fun v : V3 => (p v, p (r v))) V)

/-! ## Properties of the polar fan (polar_fan.hl:1065) -/

/-- HOL `BGMIFTE` (polar_fan.hl:1065): the polar fan of a convex local
fan is a convex local fan; the interior angles pass to the polar
vertices via `arcV = π - interior_angle1` in both directions. -/
theorem BGMIFTE {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)} {V' : Set V3}
    {E' : Set (Set V3)}
    {FF' : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (hg : Generic V E)
    (hia : ∀ v ∈ V, interiorAngle1 (0 : V3) FF v < Real.pi)
    (hp : polarFan V E FF = (V', E', FF')) :
    ConvexLocalFan V' E' FF' ∧ Generic V' E' ∧ V'.ncard = V.ncard ∧
      (∀ v ∈ V,
          arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v)))
            = Real.pi - interiorAngle1 (0 : V3) FF (rhoNode1 FF v) ∧
          0 < arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) ∧
          arcV (0 : V3) (cross3 v (rhoNode1 FF v))
                (cross3 (rhoNode1 FF v) (rhoNode1 FF (rhoNode1 FF v))) < Real.pi) ∧
      (∀ v ∈ V,
          arcV (0 : V3) v (rhoNode1 FF v)
            = Real.pi - interiorAngle1 (0 : V3) FF' (cross3 v (rhoNode1 FF v)) ∧
          0 < arcV (0 : V3) v (rhoNode1 FF v) ∧
          arcV (0 : V3) v (rhoNode1 FF v) < Real.pi) := by
  -- NEEDS（wsewpch-w5b 侦察+部分填证 2026-10-23；三缺口，剩余为 W6c 装配件）：
  -- (1) 结论 4（第一 arc half）已闭合：私件 `p7w2_half_polar_arc`（本文件，
  --     逐点前提形式；引擎 = `p7w2_hvihvec`，即 Hvihvec.hl:34 的 0 心移植）。
  --     W6c 装配：foundation 供 (v, ρv) 轨道点、IVS_RHO_IDD、非共线（fan6 型，
  --     LOCAL_FAN_CHARACTER_OF_RHO_NODE 第三合取逐点形）、INTERIOR_ANGLE1_POS
  --     逐点形 + 本文件前提 hia 即可逐 v 实例化。
  -- (2) 结论 1（ConvexLocalFan V' E' FF'）+ 结论 3（CARD V' = CARD V）：
  --     HOL polar_fan.hl:1217-2050 的 FAN_AFF_GT_CONDITION 路线 + local_fan/dih2k
  --     装配，~600 行，未移植。
  -- (3) 结论 2（Generic V' E'）：**外部锚阻塞** —— HOL 经 CIZMRRH
  --     （LA3:1881，未证，W3b）三分 + KCHMAMG（LA5:5018，未证）排除
  --     circular/lunar 支；CIZMRRH/KCHMAMG 落地后机械装配。
  -- 另两枚 SF 立案（见交付 DELIVERY.md）：LA1 `Generic`（affGt）与 HOL generic
  -- （aff_ge，LA2 generic_p2 忠实）不一致；LA1 `LocalFan` 世界允许孤立顶点
  -- （HOL local_fan 不允许），foundation 桩 RHO_NODE1_INJECTIVE 等在此弱编码下
  -- 疑似假（junk ε），本 lane 的 :1093-1121 桩维持待证状态并等待 SF 裁决。
  sorry

/-! ## Perimeter and its bound of 2 pi (polar_fan.hl:2115-3362) -/

/-- HOL `IQCPCGW` (polar_fan.hl:2115): `fan_perimeter`.  The
`@v. v IN V` choice is `Classical.epsilon`; the `CARD FF - 1`
truncation is kept verbatim. -/
noncomputable def fanPerimeter (V : Set V3) (_E : Set (Set V3)) (FF : Set (V3 × V3)) : ℝ :=
  let v := Classical.epsilon (fun v : V3 => v ∈ V)
  ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
    arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v)

/-- HOL `FAN_PERIMETER_INVARIANT` (polar_fan.hl:2122). -/
theorem FAN_PERIMETER_INVARIANT {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((FF.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  sorry

/-- HOL `FAN_PERIMETER_INVARIANT_CARD_V` (polar_fan.hl:2171). -/
theorem FAN_PERIMETER_INVARIANT_CARD_V {V : Set V3} {E : Set (Set V3)}
    {FF : Set (V3 × V3)} (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) (v : V3) (hv : v ∈ V) :
    fanPerimeter V E FF =
      ∑ i ∈ Finset.range ((V.ncard - 1 : ℕ) + 1),
        arcV (0 : V3) ((rhoNode1 FF)^[i] v) ((rhoNode1 FF)^[i + 1] v) := by
  sorry

/-- HOL `FAN_PERIMETER` (polar_fan.hl:2184). -/
theorem FAN_PERIMETER {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) :
    fanPerimeter V E FF = setSum V (fun v : V3 => arcV (0 : V3) v (rhoNode1 FF v)) := by
  sorry

/-- HOL `WSEWPCH` (polar_fan.hl:2213): the fan perimeter of a convex
local fan is at most `2 * pi`. -/
theorem WSEWPCH {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E) : fanPerimeter V E FF ≤ 2 * Real.pi := by
  sorry

end Kepler.Text
